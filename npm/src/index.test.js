const { runSync, MakamProcess } = require("./");

describe("runSync", () => {
  it("parses and returns the results", () => {
    const { exitCode, output } = runSync([
      "foo : prop.",
      'foo :- print_string "hello".',
      "foo ?",
      "test ?"
    ]);
    expect({ exitCode, output }).toMatchSnapshot();
  });
});

describe("MakamProcess", () => {
  it("parses and returns the results", async () => {
    const makam = new MakamProcess();
    const result = await makam.write(`
      foo : prop.
      foo :- print_string "hello".
      foo ?
      test ?
    `);
    await makam.close();
    expect(result).toMatchSnapshot();
  });
});
