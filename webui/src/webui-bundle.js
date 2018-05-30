import CodeMirror from "codemirror";
window.CodeMirror = CodeMirror;

import SimpleMode from "codemirror/addon/mode/simple";
import RunMode from "codemirror/addon/runmode/runmode";
import MakamMode from "../makam-codemirror";

import * as WebUI from "./webui";
import "./style-bundle.scss";

WebUI.makamWebUIOnLoad(window.makamWebUIOptions);
