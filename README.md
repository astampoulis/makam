# The Makam metalanguage -- a tool for rapid language prototyping

[![CircleCI](https://circleci.com/gh/astampoulis/makam.svg?style=svg)](https://circleci.com/gh/astampoulis/makam)

Copyright (C) 2012- Antonis Stampoulis

This program is free software, licensed under the GPLv3 (see LICENSE).

## Introduction

Makam is a metalanguage that eases implementation of languages with rich type systems, supporting
concise and modular language definitions, aimed at allowing rapid prototyping and experimentation
with new programming language research ideas. The design of Makam is based on higher-order logic
programming and is a refinement of the λProlog language. Makam is implemented from scratch in OCaml.

The name comes from the makam/maqam of traditional Turkish and Arabic music: a set of
techniques of improvisation, defining the pitches, patterns and development of a piece of music.

The design and development of Makam started in 2012 at MIT, under the supervision of Prof. Adam
Chlipala, and continues as a personal project at [Originate NYC](http://www.originate.com/).

To read more about Makam, visit my homepage:

<http://astampoulis.github.io/>


## Installation

There are multiple ways to install Makam: The easiest way is by using the `makam` Node.js package
that includes a pre-compiled Makam binary.

- [Install through Node](#install-through-node). This is the easiest way, as it requires
  only a Node.js installation; the package includes a pre-compiled Makam binary.
- [Install through OPAM](#install-through-opam). This requires both an OCaml and a Node.js
  installation, and compiles Makam from source.

### Install through Node

#### TL;DR

- Install [Node.js 12.x](https://nodejs.org/en/download/)
- `npm install -g makam`
- `makam`

#### Instructions

- Install [Node.js 12.x](https://nodejs.org/en/download/)

  In Ubuntu/Debian Linux:

        curl -sL https://deb.nodesource.com/setup_12.x | sudo -E bash -
        sudo apt-get install -y nodejs

  In MacOS X:

        brew install node

  Windows are not supported through this method at this time, as there
  is no pre-compiled binary for this platform in the Node.js package.
  [Compiling from source](#install-through-opam) should work though.

- Install the `makam` npm package globally (you might need `sudo`):

        npm install -g makam

- Clone the Makam repository to have examples locally:

        git clone https://github.com/astampoulis/makam.git
        cd makam

- Use `makam` to run the REPL:

        makam

- If you `git pull` a newer version of the repository, make
  sure to also update your Makam installation with:

        npm install -g makam

(Alternatively, instead of installing Makam globally, you can install
Makam under `./node_modules` with `npm install makam`, in which case
you'll have to use `./node_modules/.bin/makam` to run `makam`, or
add `$(pwd)/node_modules/.bin` to your path.)

### Install through OPAM

#### TL;DR

- [OPAM](http://opam.ocaml.org/doc/Quick_Install.html)
- `opam switch create ./`
- `eval $(opam config env)`
- [Node.js 8.x](https://nodejs.org/en/download/)
- `make`
- `./makam`

#### Instructions

Clone the repository to get the Makam source code.

    git clone https://github.com/astampoulis/makam.git

You then need to install OPAM, the OCaml Package Manager. Instructions are
available at:

<http://opam.ocaml.org/doc/Install.html>

We have been testing using the OCaml 4.07.1 configuration. Creating a
local switch is the recommended way to keep the OCaml compiler
configuration and dependencies separate from other OCaml projects you
might have. To create a local switch, install all dependencies, and set
up the environment variables you need, do:

- `opam switch create ./`
- `eval $(opam config env)`

Makam also depends on Node.js, which is used for optimized parser
generation. Instructions are available at:

<https://nodejs.org/en/download/>

Most recent versions of Node.js should work. If you are on an old version
(before `7.x`), you can use `nave` to install a newer Node.js version:

    npm install -g nave && nave use 12

(Other Node version managers like `n` and `nvm` should also work.)

Finally, compile Makam:

    make

Now, when you want to run Makam, just issue:

    ./makam

Examples written in Makam are available in the same repository that you cloned
above. Having a local copy is useful as a reference point, since there's no
tutorial yet; look in the `examples` directory.

To update your version of Makam, you can do:

    git pull
    opam install . --deps-only
    make

## Using Makam

Unfortunately we do not have a Makam tutorial yet. I am in the process of
writing introductory posts which will be available in my homepage:

    http://astampoulis.github.io/makam/

Look into the files in the `examples/` directory for sample developments in Makam.
