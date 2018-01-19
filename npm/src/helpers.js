// @flow

type Location = {
  start: { line: number, char: number },
  end: { line: number, char: number }
};

type LocatedMessage = {
  message: string,
  location: ?Location
};

export type MakamResult = {
  fullOutput: string,
  errors: Array<LocatedMessage>,
  queryResults: Array<LocatedMessage>
};

const parseLocation = (message: string): ?Location => {
  const sameLineRegexp = /line ([0-9]+), characters ([0-9]+)-([0-9]+)/m;
  const spansLineRegexp = /line ([0-9]+), character ([0-9]+) to line ([0-9]+), character ([0-9]+)/m;

  const sameMatch = message.match(sameLineRegexp);
  const spansMatch = message.match(spansLineRegexp);

  if (sameMatch) {
    const [_, line, startChar, endChar] = sameMatch;
    return {
      start: { line: parseInt(line) - 1, char: parseInt(startChar) - 1 },
      end: { line: parseInt(line) - 1, char: parseInt(endChar) - 1 }
    };
  } else if (spansMatch) {
    const [_, startLine, startChar, endLine, endChar] = spansMatch;
    return {
      start: { line: parseInt(startLine) - 1, char: parseInt(startChar) - 1 },
      end: { line: parseInt(endLine) - 1, char: parseInt(endChar) - 1 }
    };
  } else {
    return null;
  }
};

const parseError = (error: string): LocatedMessage => {
  const errorRegexp = /^!! Error in block block[0-9]*, .*:$/m;
  return {
    message: error.replace(errorRegexp, "").trim(),
    location: parseLocation(error)
  };
};

const parseQueryResult = (queryResult: string): LocatedMessage => {
  const headerRegexp = /^line .+:$/m;
  return {
    message: queryResult.replace(headerRegexp, "").trim(),
    location: parseLocation(queryResult)
  };
};

const parseOutput = (output: string): MakamResult => {
  let processed = output;

  const errorRegexp = /^!! Error in block block[0-9]*, .*$\n(.+\n)*\n/gm;
  let errors = [];
  const errorMatch = processed.match(errorRegexp);
  if (errorMatch) {
    errors = errorMatch.map(parseError);
  }

  processed = processed.replace(errorRegexp, "");
  const queryResultRegexp = /^-- Query result in block block[0-9]*, /m;
  let queryResults = processed.split(queryResultRegexp);
  if (queryResults.length >= 1 && queryResults[0].trim() == "") {
    queryResults = queryResults.slice(1);
  }
  queryResults = queryResults.map(parseQueryResult);

  return {
    fullOutput: output,
    errors,
    queryResults
  };
};

module.exports = { parseOutput, parseQueryResult, parseError, parseLocation };
