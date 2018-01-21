import { h, render } from "preact";
import * as ES6Promise from "es6-promise";
ES6Promise.polyfill();
import "isomorphic-fetch";

var highlight = (text, output) => {
  var element = (
    <pre style="width: 50% !important; overflow: wrap;">
      <code
        language="makam"
        class="cm-s-default"
        ref={c => CodeMirror.runMode(text, "makam", c)}
      />
    </pre>
  );
  return render(element, output);
};

var annotationNode = text => {
  var element = document.createElement("div");
  highlight(text, element);
  return element;
};

var run = input => {
  fetch(
    "https://0l0h0ccxff.execute-api.us-east-1.amazonaws.com/dev/makam/query",
    {
      method: "POST",
      headers: {
        "Content-Type": "application/json"
      },
      body: JSON.stringify({ stateBlocks: [input] })
    }
  )
    .then(response => {
      return response.json();
    })
    .then(json => {
      const output = json.stateBlocksOutput.output[0];
      output.errors.forEach(err => {
        console.log(err);
        cm.markText(
          {
            line: err.location.start.line,
            ch: err.location.start.char
          },
          { line: err.location.end.line, ch: err.location.end.char },
          { css: "background-color: #f13" }
        );
        cm.addLineWidget(err.location.start.line, annotationNode(err.message));
      });
    })
    .catch(console.error);
};

// highlight(document.getElementById("makam").textContent, document.body);
run(document.getElementById("makam").textContent);

// highlight(document.getElementById("makam").textContent, node);

var element = <span>hello</span>;
var q = render(element, document.body);
