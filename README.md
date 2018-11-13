Examples for Use in EasyCrypt Teaching
====================================================================

This repository contains several, graduated examples for use in the
teaching of the [EasyCrypt](https://www.easycrypt.info/trac/) proof
assistant.

Instructions for installing EasyCrypt can be found at the [EasyCrypt
GitHub Repository](https://github.com/EasyCrypt/easycrypt).  See the
[EasyCrypt reference
manual](https://www.easycrypt.info/documentation/refman.pdf) for how
to use EasyCrypt.

First Example: Simple Logic
--------------------------------------------------------------------

[`SimpLogic.ec`](../master/SimpLogic.ec) contains the proof of a lemma
showing how universal quantification can be expressed in terms
of existential quantification and negation. (The file 
[`SimpLogic-initial.ec`](../master/SimpLogic-initial.ec) contains
a less sophisticated precursor to the final, terser proof. And the file
[`SimpLogic-fill.ec`](../master/SimpLogic-fill.ec) omits the
proofs, allowing them to be filled-in.)

Second Example: Random Assignment
--------------------------------------------------------------------

[`RndEx.ec`](../master/RndEx.ec) contains several lemmas concerning
two procedures involving random assignments. The first procedure
returns a randomly chosen boolean, whereas the second returns the
exclusive or of two randomly chosen booleans. Among other facts,
it is proved that both procedures are equally likely to return
true, and equally likely to return false. The file
[`RndEx-fill.ec`](../master/RndEx-fill.ec) omits the proofs,
allowing them to be filled-in.

Third Example: Secure Message Communication Via One-time Pad in
Real/Ideal Paradigm Style
--------------------------------------------------------------------

[`SMC.ec`](../master/SMC.ec) contains the formalization and security
proof of two-party secure message communication via a one-time
pad. This is done using the Real/Ideal Paradigm (but in a non-UC
(Universally Composable Security) style). 
The file [`SMC-fill.ec`](../master/SMC-fill.ec) omits the proof,
allowing them to be filled-in.

Fourth Example: Symmetric Encryption from Pseudorandom Functions
--------------------------------------------------------------------

The subdirectory [`encryption`](../master/encryption) contains the proof
of IND-CPA (indistinguishability under chosen plaintext attack)
security for symmetric encryption built out of a pseudorandom
function.
