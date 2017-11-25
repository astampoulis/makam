const makam = require("./makam");

function repl() {
  console.log(`\n\tMakam, version ${makam.version} (Javascript REPL)\n\n`);
  const nodeRepl = require("repl");
  nodeRepl.start({
    eval: function (cmd, context, filename, cb) {
      var cmdTrimmed = cmd.trim();
      if (![".", "?"].includes(cmdTrimmed[cmdTrimmed.length - 1])) {
        return cb(new nodeRepl.Recoverable());
      } else {
        makam.eval(cmd); cb(null);
      }
    }});
}

if (require.main === module) repl();

module.exports = Object.assign({}, makam, { repl: repl });
