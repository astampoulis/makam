// @flow

const { execSync, spawn } = require("child_process");
const EventEmitter = require("events");
const { Readable } = require("stream");

const { defaultArguments, binaryPath } = require("./constants");
const { parseOutput } = require("./helpers");
import type { MakamResult } from "./helpers";

let OCAMLRUNPARAM = "l=100M,s=16M,i=2M,o=200";

const runSync = (inputBlocks: Array<string>, args: Array<string> = []) => {
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

  const results = makamOutput
    .toString("utf8")
    .split("## Ready for input.\n")
    .map(parseOutput);

  return {
    exitCode: makamExitCode,
    output: results.slice(1),
    initialMessage: results[0]
  };
};

const _run = (args = [], extraOptions = {}) => {
  return spawn(
    binaryPath,
    [].concat(defaultArguments, args),
    Object.assign(
      {},
      { env: Object.assign({}, process.env, { OCAMLRUNPARAM }) },
      extraOptions
    )
  );
};

class GotResponseEmitter extends EventEmitter {}

class MakamProcess {
  makamProcess: any;
  gotResponse: GotResponseEmitter;
  stdout: Readable;

  _currentResponse: string;
  _lastPromise: ?Promise<MakamResult>;

  constructor() {
    this.makamProcess = _run();
    if (!this.makamProcess) throw new Error("could not start makam");

    this._currentResponse = "";

    this.gotResponse = new GotResponseEmitter();
    this.stdout = this.makamProcess.stdout;

    this.stdout.setEncoding("utf8");
    this.stdout.on("end", () => this.gotResponse.emit("end"));
    this.stdout.on("data", s => {
      const lastOne = s.endsWith("## Ready for input.\n");
      this._currentResponse += lastOne
        ? s.replace("## Ready for input.\n", "")
        : s;
      if (lastOne) {
        this.gotResponse.emit("got_response", this._currentResponse);
        this._currentResponse = "";
      }
    });

    this._lastPromise = this._getResponsePromise();
  }

  write(input: string): Promise<MakamResult> {
    if (!this._lastPromise) {
      return Promise.reject(new Error("process has ended"));
    }
    return this._lastPromise.then(() => {
      const newPromise = this._getClosePromise();
      this._lastPromise = newPromise;
      this.makamProcess.stdin.write(
        `%block-begin block.\n${input}\n%block-end.\n`,
        "utf8"
      );
      return newPromise;
    });
  }

  close(): Promise<MakamResult> {
    if (!this._lastPromise) {
      return Promise.resolve(parseOutput(this._currentResponse));
    }
    return this._lastPromise.then(() => {
      const newPromise = this._getClosePromise();
      this._lastPromise = newPromise;
      this.makamProcess.stdin.end();
      return newPromise;
    });
  }

  lastResponse(): ?Promise<MakamResult> {
    return this._lastPromise;
  }

  _getClosePromise(): Promise<MakamResult> {
    return new Promise((resolve, reject) => {
      this.gotResponse.once("end", () => {
        this._lastPromise = null;
        return resolve(parseOutput(this._currentResponse));
      });
    });
  }

  _getResponsePromise(): Promise<MakamResult> {
    return new Promise((resolve, reject) => {
      this.gotResponse.once("got_response", output => {
        return resolve(parseOutput(output));
      });
      this.gotResponse.once("end", () => {
        this._lastPromise = null;
        return reject(new Error("Makam process ended"));
      });
    });
  }
}

const repl = (args: Array<string> = []) => {
  return _run(args, { stdio: "inherit" });
};

module.exports = { MakamProcess, repl, binaryPath, runSync, OCAMLRUNPARAM };
