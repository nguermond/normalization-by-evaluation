# Normalization by Evaluation

Compile with `ocamlbuild *.native`.
Run with `./*.native`.

## File descriptions
Domain semantics [1] with 'name generation' syntax [2].
* `STLC_NG_D.ml` : simply typed lambda calculus
* `SystemT_NG_D.ml` : System T
* `MLTT_NG_D.ml` : Martin-Löf's type theory

Presheaf semantics [3,4] with de Bruijn syntax.
* `STLC_dB_PS.ml` : simply typed lambda calculus

Domain semantics [1] with de Bruijn syntax.
* `STLC_dB_D.ml` : simply typed lambda calculus

### References
[1] Andreas Abel, Klaus Aehlig, Peter Dybjer. *Normalization by evaluation for Martin-Löf type theory with one universe.* 2007.

[2] Andrzej Filinski. *Normalization by evaluation for the computational lambda-calculus.* 2001.

[3] Thorsten Altenkirch, Martin Hofmann, Thomas Streicher. *Categorical reconstruction of a reduction free normalization proof.* 1995(?).

[4] Thorsten Altenkirch, Ambrus Kaposi. *Normalization by evaluation for type theory, in type theory.* 2017.
