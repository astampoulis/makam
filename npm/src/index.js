const { spawn } = require("child_process");
const EventEmitter = require("events");
const { Readable } = require("stream");

const { OCAMLRUNPARAM, defaultArguments, binaryPath } = require("./constants");

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

  _processEnded: boolean;
  _currentResponse: string;
  _lastPromise: Promise<string>;

  constructor() {
    this.makamProcess = _run();
    if (!this.makamProcess) throw new Error("could not start makam");

    this._currentResponse = "";
    this._processEnded = false;

    this.gotResponse = new GotResponseEmitter();
    this.stdout = this.makamProcess.stdout;

    this.stdout.setEncoding("utf8");
    this.stdout.on("end", () => this.gotResponse.emit("end"));
    this.stdout.on("data", s => {
      const lastOne = s.endsWith("## Ready for input.\n");
      this._currentResponse += lastOne ? s.replace("## Ready for input.\n", "") : s;
      if (lastOne) {
        this.gotResponse.emit("got_response", this._currentResponse);
        this._currentResponse = "";
      }
    });

    this._lastPromise = this._getResponsePromise();
  }

  async write(input: string) {
    this._lastPromise = this._getResponsePromise();
    if (!this._processEnded) {
      this.makamProcess.stdin.write(
        `%block-begin.\n${input}\n%block-end.\n`,
        "utf8"
      );
    }
    return this._lastPromise;
  }

  async close() {
    if (this._processEnded) {
      this._lastPromise = Promise.resolve(this._currentResponse);
    } else {
      this._lastPromise = this._getClosePromise();
      this.makamProcess.stdin.end();
    }
    return this._lastPromise;
  }

  async lastResponse() {
    return this._lastPromise;
  }

  _getClosePromise(): Promise<string> {
    return new Promise((resolve, reject) => {
      this.gotResponse.once("end", () => resolve(this._currentResponse));
    });
  }

  _getResponsePromise(): Promise<string> {
    return new Promise((resolve, reject) => {
      this.gotResponse.once("got_response", resolve);
      this.gotResponse.once("end", () => {
        this._processEnded = true;
        reject(new Error("Makam process ended"));
      });
    });
  }
}

const repl = (args: Array<string> = []) => {
  return _run(args, { stdio: "inherit" });
};

module.exports = { MakamProcess, repl, binaryPath };
