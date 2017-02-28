# The Makam metalanguage -- a tool for rapid language prototyping
## Version 0.5

Copyright (C) 2012- Antonis Stampoulis

This program is free software, licensed under the GPLv3 (see LICENSE).

### Introduction

test
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


### Build instructions

You first need to install OPAM, the OCaml Package Manager. Instructions are available at:

<http://opam.ocaml.org/doc/Quick_Install.html>

We have been testing using the OCaml 4.02.0 configuration.

After you have OPAM installed, you can install Makam:

    opam pin add makam https://github.com/astampoulis/makam.git

(Makam is still under development and does not have a stable release yet, thus having its
installation track the git repository is the recommended option for the time being.)

This compiles and installs Makam after installing all needed dependencies.
Now, when you want to run Makam, just issue:

    makam

Examples written in Makam are available in the same repository. Having a local copy
is useful as a reference point, since there's no tutorial yet:

    git clone https://github.com/astampoulis/makam.git

Look in the `examples` directory.

### Upgrading Makam

It is recommended that you upgrade Makam frequently. OPAM can be used for that:

    opam upgrade makam

### How to use Makam

Unfortunately we do not have a Makam tutorial yet -- one will be out soon though.
The closest thing to a proper tutorial is a technical overview paper which you can
find on my website. However, note that some identifiers are different in the
actual implementation compared to the paper. Also, to switch to specialized syntax
for propositions the form `{prop| ... |}` needs to be used.

Look into the files in the examples/ directory for sample developments in Makam.

Recommendations:

`small/systemf.makam`  -- a simple implementation of System F

`big/ocaml.makam`      -- a fragment of the OCaml type system

`big/hol.makam`        -- the HOL formal logic

`big/veriml.makam`     -- the VeriML type system

`big/urweb.makam`      -- type inference for Featherweight Ur

`big/testocaml.makam`,
`big/testveriml.makam`,
`big/testurweb.makam`  -- files containing sample queries

`lib/builtins.makam`   -- the builtin types and constants of Makam


Some commands:

`%use "examples/big/testocaml.makam".`       -- load a file

`%use testocaml.`                            -- when testocaml.makam is in the search path

`%reset.`                                    -- to reset the state of Makam

`expr : type.`                               -- declare a new type (or type constructor)

`ifthenelse : expr -> expr -> expr.`         -- declare a new constant

`eval : expr -> expr -> prop.`               -- declare a new predicate

`eval (ifthenelse E1 E2 E3) V2 <- eval E1 etrue, eval E2 V2.` -- declare a new rule

`eval (ifthenelse etrue efalse etrue) E ?` -- perform a query


That's basically it. For the rest, look at the examples!
