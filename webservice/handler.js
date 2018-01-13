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

const _run = (args, inputBlocks) => {
  const allArguments = [].concat(defaultArguments, args);

  let input = "";
  inputBlocks.forEach((block, i) => {
    input += `\n%block-begin block${i}.\n${block}\n%block-end.\n`;
  });

  const results = execSync(`${binaryPath} ${allArguments.join(" ")}`, {
    env: Object.assign({}, process.env, { OCAMLRUNPARAM }),
    input
  })
    .toString("utf8")
    .split("# ");

  return results;
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
    .catch(_ => console.error(`could not persist state to s3`));
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
    let queryOutput = query ? _runOnState(stateBlocks, [query])[1] : "";

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
