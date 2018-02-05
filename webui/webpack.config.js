const path = require("path");

module.exports = {
  entry: "./src/index.js",
  output: {
    path: __dirname,
    filename: "makam-webui.js"
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
        test: /\.css$/,
        use: ["style-loader", "css-loader"]
      }
    ]
  },
  resolve: {
    modules: ["node_modules", path.resolve(__dirname)]
  }
};
