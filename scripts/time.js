const { promisify } = require("util");
const exec = promisify(require("child_process").exec);
let count = 0;
let sum = 0.0;

const [a, b, iterations, command] = process.argv;

if (!iterations || !parseInt(iterations) || !command) {
  console.error(`usage: ${a} ${b} <iterations> <command>\n`);
  return;
}

let iter = parseInt(iterations);

(async () => {
  while (iter > 0) {
    iter--;
    try {
      const start = Date.now();
      const result = await exec(command);
      console.log(result.stdout);
      const end = Date.now();
      const current = (end - start) / 1000.0;
      count++;
      sum += current;
      console.log("This run:", current, "Moving average:", sum / count);
    } catch (err) {
      console.error(err.message);
      process.exit(1);
    }
  }

  console.log(sum / count);
})();
