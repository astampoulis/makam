#!/usr/bin/env node

const { spawn } = require("child_process");
const path = require("path");

const OCAMLRUNPARAM = "l=100M,s=16M,i=2M,o=200";

const arguments = ["-I", __dirname, ...process.argv.slice(2)];

spawn(path.join(__dirname, "makam-bin-linux64"), arguments, {
  stdio: "inherit",
  env: Object.assign({}, process.env, { OCAMLRUNPARAM })
}).on("exit", process.exit);
