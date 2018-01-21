const path = require("path");

module.exports = {
  entry: "./index.js",
  output: {
    path: path.resolve(__dirname, "dist"),
    filename: "bundle.js",
    library: "makam-codeblock",
    libraryTarget: "umd"
  },
  module: {
    rules: [
      {
        test: /\.js$/,
        loader: "babel-loader",
        options: {
          presets: ["env"]
        }
      }
    ]
  },
  resolve: {
    modules: ["node_modules", path.resolve(__dirname)]
  }
};
