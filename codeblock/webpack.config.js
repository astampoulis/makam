const path = require("path");

module.exports = {
  entry: "./index.js",
  output: {
    path: path.resolve(__dirname, "dist"),
    filename: "bundle.js"
  },
  module: {
    rules: [
      {
        test: /\.js$/,
        loader: "babel-loader",
        options: {
          presets: ["env", "preact"]
        }
      }
    ]
  },
  resolve: {
    modules: ["node_modules", path.resolve(__dirname)]
  }
};
