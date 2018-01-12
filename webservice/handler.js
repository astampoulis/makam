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

const _run = (args, inputBlocks) => {
  const allArguments = [].concat(defaultArguments, args);

  let input = "";
  inputBlocks.forEach((block, i) => {
    input += `\n%batch-begin block${i}.\n${block}\n%batch-end.\n`;
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
  const stateFilename = `/tmp/makam-state-${_suffixForInput(input)}`;
  const outputFilename = `/tmp/makam-output-${_suffixForInput(input)}`;

  const output = _run(["--persist-state", stateFilename], input);

  fs.writeFileSync(outputFilename, JSON.stringify(output));

  return output;
};

const _cachedRun = input => {
  const stateFilename = `/tmp/makam-state-${_suffixForInput(input)}`;
  const outputFilename = `/tmp/makam-output-${_suffixForInput(input)}`;

  if (fs.existsSync(stateFilename) && fs.existsSync(outputFilename)) {
    return JSON.parse(fs.readFileSync(outputFilename, "utf8"));
  } else {
    return _runAndPersist(input);
  }
};

const _runOnState = (stateInput, input) => {
  const stateFilename = `/tmp/makam-state-${_suffixForInput(stateInput)}`;

  return _run(["--init-state", stateFilename], input);
};

module.exports.makamQuery = (event, context, callback) => {
  const body = JSON.parse(event.body);

  let stateBlocksOutput = _cachedRun(body.stateBlocks);
  let queryOutput = body.query
    ? _runOnState(body.stateBlocks, [body.query])[1]
    : "";

  const response = {
    statusCode: 200,
    body: JSON.stringify({
      stateBlocksOutput,
      queryOutput
    })
  };

  callback(null, response);
};
