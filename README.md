# Deprecation Notice

Paramcoq is no longer actually maintained and released. It is only
kept as a test case for Rocq's OCaml API. The release for Rocq 9.0
will be the last one and is known to suffer some universe issues
(for instance iit no longer enable to compile CoqEAL). Users are
invited to switch to [coq-elpi](https://github.com/LPCIC/coq-elpi)
derive.param2. One can look at
[CoqEAL](https://github.com/coq-community/coqeal) for an example of
porting. Main current caveat: support for mutual inductives isn't
implemented yet.

See [old README](README_old.md) for previous documentation.
