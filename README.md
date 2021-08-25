<!---
This file was generated from `meta.yml`, please do not edit manually.
Follow the instructions on https://github.com/coq-community/templates to regenerate.
--->
# Paramcoq

[![Docker CI][docker-action-shield]][docker-action-link]
[![Contributing][contributing-shield]][contributing-link]
[![Code of Conduct][conduct-shield]][conduct-link]
[![Zulip][zulip-shield]][zulip-link]
[![DOI][doi-shield]][doi-link]

[docker-action-shield]: https://github.com/coq-community/paramcoq/workflows/Docker%20CI/badge.svg?branch=v8.10
[docker-action-link]: https://github.com/coq-community/paramcoq/actions?query=workflow:"Docker%20CI"

[contributing-shield]: https://img.shields.io/badge/contributions-welcome-%23f7931e.svg
[contributing-link]: https://github.com/coq-community/manifesto/blob/master/CONTRIBUTING.md

[conduct-shield]: https://img.shields.io/badge/%E2%9D%A4-code%20of%20conduct-%23f15a24.svg
[conduct-link]: https://github.com/coq-community/manifesto/blob/master/CODE_OF_CONDUCT.md

[zulip-shield]: https://img.shields.io/badge/chat-on%20zulip-%23c1272d.svg
[zulip-link]: https://coq.zulipchat.com/#narrow/stream/237663-coq-community-devs.20.26.20users


[doi-shield]: https://zenodo.org/badge/DOI/10.4230/LIPIcs.CSL.2012.399.svg
[doi-link]: https://doi.org/10.4230/LIPIcs.CSL.2012.399

A Coq plugin providing commands for generating parametricity statements.
Typical applications of such statements are in data refinement proofs.
Note that the plugin is still in an experimental state - it is not very user
friendly (lack of good error messages) and still contains bugs. But it
is usable enough to "translate" a large chunk of the standard library.

## Meta

- Author(s):
  - Chantal Keller (initial)
  - Marc Lasson (initial)
  - Abhishek Anand
  - Pierre Roux
  - Emilio Jesús Gallego Arias
  - Cyril Cohen
  - Matthieu Sozeau
- Coq-community maintainer(s):
  - Pierre Roux ([**@proux01**](https://github.com/proux01))
- License: [MIT License](LICENSE)
- Compatible Coq versions: The v8.10 branch tracks version 8.13 of Coq, see releases for compatibility with released versions of Coq.
- Additional dependencies: none
- Coq namespace: `Param`
- Related publication(s):
  - [Parametricity in an Impredicative Sort](https://hal.archives-ouvertes.fr/hal-00730913/) doi:[10.4230/LIPIcs.CSL.2012.399](https://doi.org/10.4230/LIPIcs.CSL.2012.399)

## Building and installation instructions

The easiest way to install the latest released version of Paramcoq
is via [OPAM](https://opam.ocaml.org/doc/Install.html):

```shell
opam repo add coq-released https://coq.inria.fr/opam/released
opam install coq-paramcoq
```

To instead build and install manually, do:

``` shell
git clone https://github.com/coq-community/paramcoq.git
cd paramcoq
make   # or make -j <number-of-cores-on-your-machine> 
make install
```


## Usage and Commands

To load the plugin and make its commands available:
```coq
From Param Require Import Param.
```

The command scheme for named translations is:
```
Parametricity <ident> as <name> [arity <n>].
```
For example, the following command generates a translation named `my_param`
of the constant or inductive `my_id` with arity 2 (the default):
```coq
Parametricity my_id as my_param.
```

The command scheme for automatically named translations is:
```coq
Parametricity [Recursive] <ident> [arity <n>] [qualified].
```
Such commands generate and name translations based on the given identifier.
The `Recursive` option can be used to recursively translate all the constants
and inductives which are used by the constant or inductive with the given
identifier. The `qualified` option allows you to use a qualified default name
for the translated constants and inductives. The default name then has the form
`Module_o_Submodule_o_my_id` if the identifier `my_id` is declared in the
`Module.Submodule` namespace.

Instead of using identifiers, you can provide explicit terms to translate,
according to the following command scheme:
```coq
Parametricity Translation <term> [as <name>] [arity <n>].
```
This defines a new constant containing the parametricity translation of
the given term.

To recursively translate everything in a module:
```coq
Parametricity Module <module_path>.
```

When translating terms containing section variables or axioms,
it may be useful to declare a term to be the translation of a constant:
```coq
Realizer <constant_or_variable> [as <name>] [arity <n>] := <term>.
```

Note that translating a term or module may lead to proof obligations (for some
fixpoints and opaque terms if you did not import `ProofIrrelevence`). You need to
declare a tactic to solve such proof obligations:
```coq
[Global|Local] Parametricity Tactic := <tactic>.
```
