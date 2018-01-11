const path = require("path");

const OCAMLRUNPARAM = "l=100M,s=16M,i=2M,o=200";

const binaryName =
  process.platform === "linux" && process.arch === "x64"
    ? "makam-bin-linux64"
    : process.platform === "darwin" ? "makam-bin-darwin64" : null;
if (!binaryName)
  throw new Error("Platform " + process.platform + " not supported");
const binaryPath = path.join(__dirname, "..", binaryName);

const stdlibPath = path.join(__dirname, "..");
const stdlibCachePath = path.join(__dirname, "..", "stdlib-cache");

const defaultArguments = ["-I", stdlibPath, "-I", stdlibCachePath];

module.exports = {
  OCAMLRUNPARAM,
  defaultArguments,
  binaryPath,
  stdlibPath,
  stdlibCachePath
};
