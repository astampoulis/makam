import { h, render, Component } from "preact";
import * as ES6Promise from "es6-promise";
ES6Promise.polyfill();
import jump from "jump.js";
import "isomorphic-fetch";

const makamWebServiceURLs = {
  dev: "https://0l0h0ccxff.execute-api.us-east-1.amazonaws.com/dev/makam/query",
  prod:
    "https://hwtoumy97e.execute-api.us-east-1.amazonaws.com/prod/makam/query"
};

var highlightText = (text, mode, theme) => {
  return (
    <pre style="white-space: pre-wrap;">
      <code
        language="makam"
        class={`cm-s-${theme}`}
        ref={c => CodeMirror.runMode(text, mode, c)}
      />
    </pre>
  );
};

var replaceCodeElement = (element, mode, options = {}) => {
  const allOptions = Object.assign(
    {},
    {
      value: element.textContent,
      readOnly: options.editable ? false : "nocursor",
      theme: "default",
      mode
    },
    options
  );
  return CodeMirror(cmElement => {
    element.parentNode.replaceChild(cmElement, element);
  }, allOptions);
};

class MakamCodeblock {
  constructor(element, options = {}) {
    this.codeMirror = replaceCodeElement(element, "makam", options);
    this.theme = this.codeMirror.getOption("theme");
    this.annotations = [];
  }

  value() {
    return this.codeMirror.getValue();
  }

  addAnnotation(text, location, className) {
    const element = document.createElement("div");
    element.classList.add("cm-makam-annotation");
    element.classList.add(className);
    render(highlightText(text, "makam-query-results", this.theme), element);
    element.style.transform = "scale(0.0)";
    window.setTimeout(() => (element.style.transform = "scale(1.0)"), 0);
    const widget = this.codeMirror.addLineWidget(location.end.line, element);
    const marker = this.codeMirror.markText(
      {
        line: location.start.line,
        ch: location.start.char
      },
      { line: location.end.line, ch: location.end.char },
      { className }
    );
    this.annotations.push({ element, widget, marker });
  }

  clearAnnotations(options = { animation: true }) {
    this.annotations.forEach(({ element, widget, marker }) => {
      marker.clear();
      if (options.animation) {
        element.style.transform = "scale(0.0)";
        element.addEventListener("transitionend", () => widget.clear(), {
          capture: true,
          once: true
        });
      } else {
        widget.clear();
      }
    });
    this.annotations = [];
  }

  setEditable(value) {
    this.codeMirror.setOption("readOnly", value ? false : "nocursor");
  }

  addAnnotationsForResult(result) {
    result.errors.forEach(err =>
      this.addAnnotation(err.message, err.location, "makam-error")
    );
    result.queryResults.forEach(qry =>
      this.addAnnotation(qry.message, qry.location, "makam-query-result")
    );
  }
}

var evalMakam = (url, stateBlocks, queryBlock) => {
  return fetch(url, {
    method: "POST",
    headers: {
      "Content-Type": "application/json"
    },
    body: JSON.stringify({
      stateBlocks: stateBlocks.map(x => x.value()),
      query: queryBlock.value()
    })
  })
    .then(response => {
      return response.json();
    })
    .then(json => {
      json.stateBlocksOutput.output.forEach((output, i) => {
        if (stateBlocks[i]) stateBlocks[i].addAnnotationsForResult(output);
      });
      queryBlock.addAnnotationsForResult(json.queryOutput.output[0]);
    })
    .catch(console.error);
};

class LiterateWebUI {
  constructor(options = { stateBlocksEditable: false, env: "prod" }) {
    this.stateBlocks = [];
    this.queryBlock = null;
    this.otherBlocks = [];
    this.options = options;
    this.makamURL = makamWebServiceURLs[options.env];
  }

  initialize() {
    const stateBlocksOptions = Object.assign({}, this.options, {
      editable: this.options.stateBlocksEditable
    });
    const queryBlockOptions = Object.assign({}, this.options, {
      editable: true
    });
    document
      .querySelectorAll("pre > code[language='makam']")
      .forEach(codeElement => {
        this.stateBlocks.push(
          new MakamCodeblock(codeElement.parentNode, stateBlocksOptions)
        );
      });
    this.queryBlock = new MakamCodeblock(
      document.querySelector("pre > code[language='makam:input']"),
      queryBlockOptions
    );
    document
      .querySelectorAll("pre > code:not([language^='makam'])")
      .forEach(codeElement => {
        this.otherBlocks.push(
          replaceCodeElement(
            codeElement.parentNode,
            codeElement.attributes.language,
            this.options
          )
        );
      });
    render(<WebUIControls />, document.body);
  }

  eval() {
    this.reset({ animation: false });
    evalMakam(this.makamURL, this.stateBlocks, this.queryBlock);
    let f = () => null;
    f = () => {
      this.reset();
      this.queryBlock.codeMirror.off("change", f);
    };
    this.queryBlock.codeMirror.on("change", f);
  }

  reset(options = { animation: true }) {
    this.stateBlocks.forEach(x => x.clearAnnotations(options));
    this.queryBlock.clearAnnotations(options);
  }

  focusOnQuery() {
    this.queryBlock.codeMirror.focus();
    jump(this.queryBlock.codeMirror.getWrapperElement(), { duration: 400 });
  }
}

class WebUIControls extends Component {
  render() {
    return (
      <ButtonContainer>
        <Button label="Evaluate code" onClick={() => webUI.eval()}>
          <PlayIcon />
        </Button>
        <Button
          label="Edit query"
          onClick={() => {
            webUI.reset();
            webUI.focusOnQuery();
          }}
        >
          <EditIcon />
        </Button>
      </ButtonContainer>
    );
  }
}

class ButtonContainer extends Component {
  render(props) {
    return <div class="makam-button-container">{props.children}</div>;
  }
}

class Button extends Component {
  render(props, state) {
    return (
      <div class="makam-button" onClick={props.onClick}>
        <div class="makam-button-label">{props.label}</div>
        <div class="makam-button-icon">{props.children}</div>
      </div>
    );
  }
}

class PlayIcon extends Component {
  render() {
    return (
      <svg
        xmlns="http://www.w3.org/2000/svg"
        width="100%"
        height="100%"
        viewBox="0 0 24 24"
      >
        <path d="M3 22v-20l18 10-18 10z" />
      </svg>
    );
  }
}

class EditIcon extends Component {
  render() {
    return (
      <svg
        xmlns="http://www.w3.org/2000/svg"
        width="100%"
        height="100%"
        viewBox="0 0 24 24"
      >
        <path d="M14.078 4.232l-12.64 12.639-1.438 7.129 7.127-1.438 12.641-12.64-5.69-5.69zm-10.369 14.893l-.85-.85 11.141-11.125.849.849-11.14 11.126zm2.008 2.008l-.85-.85 11.141-11.125.85.85-11.141 11.125zm18.283-15.444l-2.816 2.818-5.691-5.691 2.816-2.816 5.691 5.689z" />
      </svg>
    );
  }
}

const webUI = new LiterateWebUI({
  viewportMargin: 100000000,
  lineNumbers: true,
  env: "dev"
});
webUI.initialize();
