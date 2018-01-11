"use strict";

const {
  binaryPath,
  defaultArguments,
  OCAMLRUNPARAM
} = require("./package/lib/constants");

const { execSync } = require("child_process");

const _run = input => {
  return execSync(`${binaryPath} ${defaultArguments.join(" ")}`, {
    env: Object.assign({}, process.env, { OCAMLRUNPARAM }),
    input
  });
};

module.exports.makamQuery = (event, context, callback) => {
  const body = JSON.parse(event.body);

  const inputBlocks = JSON.parse(event.body).input;
  let input = "";
  inputBlocks.forEach((block, i) => {
    input += `%batch-begin block${i}.\n${block}\n%batch-end.\n`;
  });

  const result = _run(input)
    .toString("utf8")
    .split("# ");
  const response = {
    statusCode: 200,
    body: JSON.stringify({
      result
    })
  };

  callback(null, response);
};
