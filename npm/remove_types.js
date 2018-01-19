require("flow-remove-types/register");
var flowRemoveTypes = require("flow-remove-types");
module.exports = {
  process(src, filename) {
    return `${flowRemoveTypes(src).toString()}`;
  }
};
