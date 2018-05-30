const path = require("path");

module.exports = {
  mode: "development",
  entry: {
    webui: "./src/webui.js",
    "webui-bundle": "./src/webui-bundle.js"
  },
  output: {
    path: __dirname,
    filename: "makam-[name].js"
  },
  module: {
    rules: [
      {
        test: /\.js$/,
        loader: "babel-loader",
        options: {
          presets: ["env", "preact"]
        }
      },
      {
        test: /\.s?css$/,
        use: ["style-loader", "css-loader", "sass-loader"]
      }
    ]
  },
  resolve: {
    modules: ["node_modules", path.resolve(__dirname)]
  }
};
