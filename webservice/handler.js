"use strict";

const {
  binaryPath,
  defaultArguments,
  OCAMLRUNPARAM
} = require("makam/lib/constants");
const makamVersion = require("makam/package.json").version;

const hash = require("object-hash");
const { execSync } = require("child_process");
const fs = require("fs");
const AWS = require("aws-sdk");
const s3 = new AWS.S3();
const zlib = require("zlib");

const _saveToS3 = (filename, content) => {
  return s3
    .putObject({
      Bucket: process.env.MAKAM_CACHE_BUCKET,
      Key: `v${makamVersion}/${filename}.gz`,
      Body: zlib.gzipSync(content)
    })
    .promise();
};

const _loadFromS3 = (filename, filepath) => {
  return s3
    .getObject({
      Bucket: process.env.MAKAM_CACHE_BUCKET,
      Key: `v${makamVersion}/${filename}.gz`
    })
    .promise()
    .then(result =>
      result
        .createReadStream()
        .pipe(zlib.createGunzip())
        .pipe(filepath)
    );
};

const _parseLocation = message => {
  const sameLineRegexp = /line ([0-9]+), characters ([0-9]+)-([0-9]+)/m;
  const spansLineRegexp = /line ([0-9]+), character ([0-9]+) to line ([0-9]+), character ([0-9]+)/m;
  if (message.match(sameLineRegexp)) {
    const [_, line, startChar, endChar] = message.match(sameLineRegexp);
    return {
      start: { line: parseInt(line) - 1, char: parseInt(startChar) - 1 },
      end: { line: parseInt(line) - 1, char: parseInt(endChar) - 1 }
    };
  } else if (message.match(spansLineRegexp)) {
    const [_, startLine, startChar, endLine, endChar] = message.match(
      spansLineRegexp
    );
    return {
      start: { line: parseInt(startLine) - 1, char: parseInt(startChar) - 1 },
      end: { line: parseInt(endLine) - 1, char: parseInt(endChar) - 1 }
    };
  } else {
    return null;
  }
};

const _parseError = error => {
  const errorRegexp = /^!! Error in block block[0-9]+, .*:$/m;
  return {
    message: error.replace(errorRegexp, "").trim(),
    location: _parseLocation(error)
  };
};

const _parseQueryResult = queryResult => {
  const headerRegexp = /^line .+:$/m;
  return {
    message: queryResult.replace(headerRegexp, "").trim(),
    location: _parseLocation(queryResult)
  };
};

const _parseOutput = output => {
  let processed = output;

  const errorRegexp = /^!! Error in block block[0-9]+, .*$\n(.+\n)*\n/gm;
  let errors = [];
  if (processed.match(errorRegexp)) {
    errors = processed.match(errorRegexp).map(_parseError);
  }

  processed = processed.replace(errorRegexp, "");
  const queryResultRegexp = /^-- Query result in block block[0-9]+, /m;
  let queryResults = processed.split(queryResultRegexp);
  if (queryResults.length >= 1 && queryResults[0].trim() == "") {
    queryResults = queryResults.slice(1);
  }
  queryResults = queryResults.map(_parseQueryResult);

  return {
    fullOutput: output,
    errors,
    queryResults
  };
};

const _run = (args, inputBlocks) => {
  const allArguments = [].concat(defaultArguments, args);

  let input = "";
  inputBlocks.forEach((block, i) => {
    input += `\n%block-begin block${i}.\n${block}\n%block-end.\n`;
  });

  let makamOutput;
  let makamExitCode;

  try {
    makamOutput = execSync(`${binaryPath} ${allArguments.join(" ")}`, {
      env: Object.assign({}, process.env, { OCAMLRUNPARAM }),
      input
    });
    makamExitCode = 0;
  } catch (e) {
    makamOutput = e.stdout;
    makamExitCode = e.status;
  }

  return {
    exitCode: makamExitCode,
    output: makamOutput
      .toString("utf8")
      .split("## Ready for input.\n")
      .map(_parseOutput)
      .slice(1)
  };
};

const _suffixForInput = input => `${makamVersion}-${hash(input)}`;

const _runAndPersist = input => {
  const stateFilename = `makam-state-${_suffixForInput(input)}`;
  const statePath = `/tmp/${stateFilename}`;
  const outputFilename = `makam-output-${_suffixForInput(input)}`;
  const outputPath = `/tmp/${outputFilename}`;

  const output = _run(["--persist-state", statePath], input);

  fs.writeFileSync(outputPath, JSON.stringify(output));

  const readStateFile = new Promise((resolve, reject) => {
    fs.readFile(statePath, (error, content) => {
      if (error === null) {
        resolve(content);
      } else {
        reject(error);
      }
    });
  });

  return Promise.all([
    readStateFile.then(content => _saveToS3(stateFilename, content)),
    _saveToS3(outputFilename, JSON.stringify(output))
  ])
    .then(_ => output)
    .catch(_ => {
      console.error(`could not persist state to s3`);
      return output;
    });
};

const _cachedRun = input => {
  const stateFilename = `makam-state-${_suffixForInput(input)}`;
  const statePath = `/tmp/${stateFilename}`;
  const outputFilename = `makam-output-${_suffixForInput(input)}`;
  const outputPath = `/tmp/${outputFilename}`;

  if (fs.existsSync(statePath) && fs.existsSync(outputPath)) {
    return Promise.resolve(JSON.parse(fs.readFileSync(outputPath, "utf8")));
  } else {
    return Promise.all([
      _loadFromS3(stateFilename, statePath),
      _loadFromS3(outputFilename, outputPath)
    ])
      .then(() => JSON.parse(fs.readFileSync(outputPath, "utf8")))
      .catch(e => _runAndPersist(input));
  }
};

const _runOnState = (stateInput, input) => {
  const stateFilename = `/tmp/makam-state-${_suffixForInput(stateInput)}`;

  return _run(["--init-state", stateFilename], input);
};

const _executeQuery = (stateBlocks, query, callback) => {
  _cachedRun(stateBlocks).then(stateBlocksOutput => {
    let defaultOutput = {
      exitCode: 0,
      output: [
        {
          fullOutput: "",
          errors: [],
          queryResults: []
        }
      ]
    };

    let queryOutput = query ? _runOnState(stateBlocks, [query]) : defaultOutput;

    const response = {
      statusCode: 200,
      body: JSON.stringify({
        stateBlocksOutput,
        queryOutput
      })
    };

    callback(null, response);
  });
};

module.exports.makamQuery = (event, context, callback) => {
  const body = JSON.parse(event.body);
  _executeQuery(body.stateBlocks, body.query, callback);
};
