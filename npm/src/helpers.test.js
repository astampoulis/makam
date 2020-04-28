const { parseLocation } = require("./helpers");

describe("parseLocation", () => {
  it("parses location with a single character", () => {
    expect(parseLocation("5:5")).toEqual({
      start: { line: 3, char: 4 },
      end: { line: 3, char: 4 }
    });
  });

  it("parses location in the same line", () => {
    expect(parseLocation("5:5-10")).toEqual({
      start: { line: 3, char: 4 },
      end: { line: 3, char: 9 }
    });
  });

  it("parses locations spanning different lines", () => {
    expect(
      parseLocation("5.5-6.10")
    ).toEqual({
      start: { line: 3, char: 4 },
      end: { line: 4, char: 9 }
    });
  });
});
