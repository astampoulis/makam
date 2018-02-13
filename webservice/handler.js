"use strict";

const makam = require("makam");
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

const _promisify = f => {
  return new Promise((resolve, reject) => {
    f((error, result) => {
      if (error === null) {
        resolve(result);
      } else {
        reject(error);
      }
    });
  });
};

const _loadFromS3 = (filename, filepath) => {
  return s3
    .getObject({
      Bucket: process.env.MAKAM_CACHE_BUCKET,
      Key: `v${makamVersion}/${filename}.gz`
    })
    .promise()
    .then(gzData => _promisify(cb => zlib.gunzip(gzData.Body, cb)))
    .then(data => _promisify(cb => fs.writeFile(filepath, data, cb)));
};

const _saveDependencies = dependencies => {
  try {
    fs.mkdirSync("/tmp/dependencies");
  } catch (e) {}
  return Promise.all(
    dependencies.map(dependency => {
      if (!dependency.filename.match(/^[a-zA-Z_\-\.0-9]+\.(md|makam)$/))
        throw new Error("dependency " + dependency.filename + " not supported");
      return _promisify(cb =>
        fs.writeFile(
          `/tmp/dependencies/${dependency.filename}`,
          dependency.content,
          cb
        )
      );
    })
  );
};

const _suffixForInput = input => `${makamVersion}-${hash(input)}`;

const _runAndPersist = input => {
  const stateFilename = `makam-state-${_suffixForInput(input)}`;
  const statePath = `/tmp/${stateFilename}`;
  const outputFilename = `makam-output-${_suffixForInput(input)}`;
  const outputPath = `/tmp/${outputFilename}`;

  const output = makam.runSync(input.actualInput, [
    "--persist-state",
    statePath,
    "-I",
    "/tmp/dependencies"
  ]);

  fs.writeFileSync(outputPath, JSON.stringify(output));

  const readStateFile = _promisify(cb => fs.readFile(statePath, cb));

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

  return makam.runSync(input, [
    "--init-state",
    stateFilename,
    "-I",
    "/tmp/dependencies"
  ]);
};

const _createResponse = obj => {
  return {
    statusCode: 200,
    headers: {
      "Access-Control-Allow-Origin": "*",
      "Access-Control-Allow-Credentials": true
    },
    body: JSON.stringify(obj)
  };
};

const _executeQuery = (dependencies, stateBlocks, query, callback) => {
  const stateInput = { dependencies, actualInput: stateBlocks };
  _saveDependencies(dependencies)
    .then(() => _cachedRun(stateInput))
    .then(stateBlocksOutput => {
      if (stateBlocksOutput.exitCode != 0) {
        return callback(null, _createResponse({ stateBlocksOutput }));
      }
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

      let queryOutput = query
        ? _runOnState(stateInput, [query])
        : defaultOutput;

      callback(null, _createResponse({ stateBlocksOutput, queryOutput }));
    });
};

module.exports.makamQuery = (event, context, callback) => {
  const body = JSON.parse(event.body);
  _executeQuery(
    body.dependencies ? body.dependencies : [],
    body.stateBlocks,
    body.query,
    callback
  );
};
