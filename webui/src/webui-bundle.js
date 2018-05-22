import CodeMirror from "codemirror";
window.CodeMirror = CodeMirror;

import SimpleMode from "codemirror/addon/mode/simple";
import RunMode from "codemirror/addon/runmode/runmode";
import MakamMode from "../makam-codemirror";

import * as WebUI from "./webui";
import css1 from "codemirror/lib/codemirror.css";
import css2 from "./makam-webui.css";

WebUI.makamWebUIOnLoad(window.makamWebUIOptions);
