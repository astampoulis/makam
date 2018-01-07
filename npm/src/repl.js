#!/usr/bin/env node

const { repl } = require("./");

repl(process.argv.slice(2)).on("exit", process.exit);
