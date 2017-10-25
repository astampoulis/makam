const makam = require("./makam");

function repl() {
  console.log(`\n\tMakam, version ${makam.version} (Javascript REPL)\n\n`);
  const nodeRepl = require("repl");
  nodeRepl.start({ eval: function (cmd, context, filename, cb) { makam.eval(cmd); cb(null); } });
}

if (require.main === module) repl();

module.exports = { ...makam, repl: repl };
