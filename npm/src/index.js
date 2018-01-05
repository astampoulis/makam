#!/usr/bin/env flow-node -a

const { spawn } = require("child_process");
const path = require("path");
const EventEmitter = require("events");
const { Readable } = require("stream");

const OCAMLRUNPARAM = "l=100M,s=16M,i=2M,o=200";

const defaultArguments = ["-I", path.join(__dirname, "..")];
const binaryPath = path.join(__dirname, "..", "makam-bin-linux64");

const _run = (args = [], extraOptions = {}) => {
  return spawn(binaryPath, [...defaultArguments, ...args], {
    env: Object.assign({}, process.env, { OCAMLRUNPARAM }),
    ...extraOptions
  });
};

class GotResponseEmitter extends EventEmitter {}

class MakamProcess {
  makamProcess: any;
  gotResponse: GotResponseEmitter;
  stdout: Readable;

  _currentResponse: string;
  _lastPromise: Promise<string>;

  constructor() {
    this.makamProcess = _run();
    if (!this.makamProcess) throw new Error("could not start makam");

    this._currentResponse = "";
    this.gotResponse = new GotResponseEmitter();
    this.stdout = this.makamProcess.stdout;

    this.stdout.setEncoding("utf8");
    this.stdout.on("data", s => {
      const lastOne = s.endsWith("# ");
      this._currentResponse += lastOne ? s.replace(/# $/, "") : s;
      if (lastOne) {
        this.gotResponse.emit("got_response", this._currentResponse);
        this._currentResponse = "";
      }
    });

    this._lastPromise = this.getResponsePromise();
  }

  async write(input: string) {
    this._lastPromise = this.getResponsePromise();
    this.makamProcess.stdin.write(
      `%batch-begin.\n${input}\n%batch-end.\n`,
      "utf8"
    );
    return await this._lastPromise;
  }

  async close() {
    this._lastPromise = this.getResponsePromise();
    this.makamProcess.stdin.end();
    return await this._lastPromise;
  }

  async lastResponse() {
    return this._lastPromise;
  }

  getResponsePromise(): Promise<string> {
    return new Promise((resolve, reject) => {
      this.gotResponse.once("got_response", resolve);
    });
  }
}

const repl = (args: Array<string> = []) => {
  return _run(args, { stdio: "inherit" });
};

if (require.main === module) {
  repl(process.argv.slice(2)).on("exit", process.exit);
}

module.exports = { MakamProcess, repl, binaryPath };
