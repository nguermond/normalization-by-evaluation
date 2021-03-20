# Normalization by Evaluation

Compile with `ocamlbuild *.native`.
Run with `./*.native`.

## File descriptions
Domain semantics [1] with 'name generation' syntax [2].
* [`STLC_NG_D.ml`](./STLC_NG_D.ml) : simply typed lambda calculus
* [`SystemT_NG_D.ml`](./SystemT_NG_D.ml) : System T
* [`MLTT_NG_D.ml`](./MLTT_NG_D.ml) : Martin-Löf's type theory

Presheaf semantics [3,4] with de Bruijn syntax.
* [`STLC_dB_PS.ml`](./STLC_dB_PS.ml) : simply typed lambda calculus
* [`STLC_dB_PS.agda`](./STLC_dB_PS.agda) : simply typed lambda calculus
* [`Signatures_dB_PS.ml`](./Signatures_dB_PS.ml) : theory of signatures
* [`Signatures_dB_PS2.ml`](./Signatures_dB_PS2.ml) : theory of signatures, but much closer to the intended presheaf semantics
* [`MLTT_dB_PS.ml`](./MLTT_dB_PS.ml) : Martin-Löf's type theory (W-types NYI)

Domain semantics [1] with de Bruijn syntax.
* [`STLC_dB_D.ml`](./STLC_dB_D.ml) : simply typed lambda calculus
* [`SystemT_dB_D.ml`](./SystemT_dB_D.ml) : System T

The theory of signatures refers to λP_ω in the lambda cube, or the "higher-order" logical framework.

### References
[1] Andreas Abel, Klaus Aehlig, Peter Dybjer. *Normalization by evaluation for Martin-Löf type theory with one universe.* 2007.

[2] Andrzej Filinski. *Normalization by evaluation for the computational lambda-calculus.* 2001.

[3] Thorsten Altenkirch, Martin Hofmann, Thomas Streicher. *Categorical reconstruction of a reduction free normalization proof.* 1995(?).

[4] Thorsten Altenkirch, Ambrus Kaposi. *Normalization by evaluation for type theory, in type theory.* 2017.
