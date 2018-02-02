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
        class="language-makam"
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
      value: element.textContent.trim(),
      readOnly: options.editable ? false : "nocursor",
      theme: "default",
      mode,
      viewportMargin: Infinity,
      gutters: ["cm-makam-gutter-default"]
    },
    options
  );
  return CodeMirror(cmElement => {
    if (options.className) cmElement.classList.add(options.className);
    element.parentNode.replaceChild(cmElement, element);
  }, allOptions);
};

class HiddenCodeblock {
  constructor(element) {
    this.element = element;
  }

  value() {
    return this.element.textContent.trim();
  }

  addAnnotationsForResult() {
    return;
  }

  setGutter() {
    return;
  }

  clearAnnotations() {
    return Promise.resolve();
  }

  setEditable() {
    return;
  }
}

class MakamCodeblock {
  constructor(element, options = {}) {
    this.codeMirror = replaceCodeElement(element, "makam", options);
    this.theme = this.codeMirror.getOption("theme");
    this.annotations = [];
  }

  value() {
    return this.codeMirror.getValue();
  }

  setGutter(gutterType) {
    this.codeMirror.setOption("gutters", [`cm-makam-gutter-${gutterType}`]);
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
    this.setGutter("default");
    const promise = Promise.all(
      this.annotations.map(({ element, widget, marker }) => {
        marker.clear();
        if (options.animation) {
          return new Promise(resolve => {
            element.style.transform = "scale(0.0)";
            element.addEventListener(
              "transitionend",
              () => {
                widget.clear();
                resolve();
              },
              {
                capture: true,
                once: true
              }
            );
          });
        } else {
          widget.clear();
          return Promise.resolve();
        }
      })
    );
    this.annotations = [];
    return promise;
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
      let lastResponseFrom = -1;
      json.stateBlocksOutput.output.forEach((output, i) => {
        lastResponseFrom = i;
        if (stateBlocks[i]) stateBlocks[i].addAnnotationsForResult(output);
      });
      stateBlocks.forEach((stateBlock, i) => {
        if (i < lastResponseFrom) stateBlock.setGutter("success");
        else if (i == lastResponseFrom)
          stateBlock.setGutter(
            json.stateBlocksOutput.exitCode === 0 ? "success" : "failure"
          );
      });
      if (
        json.queryOutput &&
        json.queryOutput.output &&
        json.queryOutput.output[0]
      ) {
        queryBlock.setGutter(
          json.queryOutput.exitCode === 0 ? "success" : "failure"
        );
        queryBlock.addAnnotationsForResult(json.queryOutput.output[0]);
      }
    })
    .catch(console.error);
};

export default class LiterateWebUI {
  constructor(options = { stateBlocksEditable: false, env: "prod" }) {
    this.stateBlocks = [];
    this.queryBlock = null;
    this.otherBlocks = [];
    this.options = options;
    this.makamURL = makamWebServiceURLs[options.env];
  }

  initialize() {
    const stateBlocksOptions = Object.assign({}, this.options, {
      editable: this.options.stateBlocksEditable,
      className: "language-makam"
    });
    const queryBlockOptions = Object.assign({}, this.options, {
      editable: true,
      className: "language-makam-input"
    });
    document
      .querySelectorAll(
        "pre > code.language-makam, pre > code.language-makam-hidden"
      )
      .forEach(codeElement => {
        if (codeElement.classList.contains("language-makam-hidden")) {
          this.stateBlocks.push(new HiddenCodeblock(codeElement.parentNode));
        } else {
          this.stateBlocks.push(
            new MakamCodeblock(codeElement.parentNode, stateBlocksOptions)
          );
        }
      });
    const queryBlockElement = document.querySelector(
      "pre > code.language-makam-input"
    );
    if (queryBlockElement) {
      this.queryBlock = new MakamCodeblock(
        queryBlockElement,
        queryBlockOptions
      );
    }
    document
      .querySelectorAll(
        "pre > code:not(.language-makam):not(.language-makam-input):not(.language-makam-hidden)"
      )
      .forEach(codeElement => {
        let mode, gutterObject;
        if (codeElement.className == "language-makam-noeval") {
          mode = "makam";
          gutterObject = { gutters: ["cm-makam-gutter-noeval"] };
        } else {
          mode = codeElement.className.replace(/^language-/, "");
          gutterObject = {};
        }
        this.otherBlocks.push(
          replaceCodeElement(
            codeElement.parentNode,
            mode,
            Object.assign(
              {},
              this.options,
              {
                className: codeElement.className
              },
              gutterObject
            )
          )
        );
      });
    render(
      <WebUIControls onEval={() => this.eval()} onEdit={() => this.edit()} />,
      document.body
    );
    document.addEventListener("keyup", e => {
      const event = e || window.event;
      if (e.ctrlKey && e.key == "/") {
        document.querySelector("#makam-edit").click();
      } else if (e.ctrlKey && e.key == "Enter") {
        document.querySelector("#makam-eval").click();
      }
    });
  }

  keepQueryScroll(promise) {
    if (!this.queryBlock) return promise();

    const currentRect = this.queryBlock.codeMirror
      .getWrapperElement()
      .getBoundingClientRect();
    const topVisible = currentRect.top >= 0;
    const bottomVisible =
      currentRect.bottom <=
      (window.innerHeight || document.documentElement.clientHeight);
    if (!topVisible && !bottomVisible) return promise();

    const currentCursor = this.queryBlock.codeMirror.getCursor();
    const currentPos = this.queryBlock.codeMirror.cursorCoords(
      currentCursor,
      "page"
    ).top;
    return promise().then(() => {
      const newPos = this.queryBlock.codeMirror.cursorCoords(
        currentCursor,
        "page"
      ).top;
      let scrollAmount = newPos - currentPos;
      if (topVisible && bottomVisible) {
        const newRect = this.queryBlock.codeMirror
          .getWrapperElement()
          .getBoundingClientRect();
        scrollAmount += newRect.bottom - currentRect.bottom;
      }
      jump(scrollAmount, { duration: 100 });
    });
  }

  eval() {
    return this.keepQueryScroll(() => {
      this.reset({ animation: false });
      return evalMakam(this.makamURL, this.stateBlocks, this.queryBlock).then(
        () => {
          let f = () => null;
          f = () =>
            this.queryBlock.codeMirror.operation(() => {
              this.reset({ animation: false });
              this.queryBlock.codeMirror.off("change", f);
            });
          this.queryBlock.codeMirror.on("change", f);
        }
      );
    });
  }

  edit() {
    return this.keepQueryScroll(() =>
      this.reset().then(() => this.focusOnQuery())
    );
  }

  reset(options = { animation: true }) {
    return Promise.all(
      [].concat(this.stateBlocks.map(x => x.clearAnnotations(options)), [
        this.queryBlock.clearAnnotations(options)
      ])
    );
  }

  focusOnQuery() {
    if (!this.queryBlock) return;

    this.queryBlock.codeMirror.focus();

    const currentRect = this.queryBlock.codeMirror
      .getWrapperElement()
      .getBoundingClientRect();
    const topVisible = currentRect.top >= 0;
    const bottomVisible =
      currentRect.bottom <=
      (window.innerHeight || document.documentElement.clientHeight);
    if (!topVisible && !bottomVisible)
      jump(this.queryBlock.codeMirror.getWrapperElement(), { duration: 400 });
  }
}

class WebUIControls extends Component {
  render(props, state) {
    let evalIcon = state.evaluating ? <LoadingIcon /> : <PlayIcon />;
    return (
      <ButtonContainer>
        <Button
          id="makam-eval"
          label="Evaluate code (Ctrl-Enter)"
          onClick={() => {
            this.setState({ evaluating: true });
            props.onEval().then(() => this.setState({ evaluating: false }));
          }}
        >
          {evalIcon}
        </Button>
        <Button
          id="makam-edit"
          label="Edit query (Ctrl-/)"
          onClick={props.onEdit}
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
      <div id={props.id} class="makam-button" onClick={props.onClick}>
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

class LoadingIcon extends Component {
  render() {
    return (
      <svg
        xmlns="http://www.w3.org/2000/svg"
        width="100%"
        height="100%"
        viewBox="0 0 24 24"
        class="rotating"
      >
        <path d="M12.979 3.055c4.508.489 8.021 4.306 8.021 8.945.001 2.698-1.194 5.113-3.075 6.763l-1.633-1.245c1.645-1.282 2.709-3.276 2.708-5.518 0-3.527-2.624-6.445-6.021-6.923v2.923l-5.25-4 5.25-4v3.055zm-1.979 15.865c-3.387-.486-6-3.401-6.001-6.92 0-2.237 1.061-4.228 2.697-5.509l-1.631-1.245c-1.876 1.65-3.066 4.061-3.065 6.754-.001 4.632 3.502 8.444 8 8.942v3.058l5.25-4-5.25-4v2.92z" />
      </svg>
    );
  }
}

export const makamWebUIOnLoad = (options = {}) => {
  document.addEventListener("DOMContentLoaded", function() {
    const webUI = new LiterateWebUI(options);
    webUI.initialize();
  });
};

if (window) {
  window.LiterateWebUI = LiterateWebUI;
  window.makamWebUIOnLoad = makamWebUIOnLoad;
}
