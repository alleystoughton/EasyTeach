(* PseudoRandFun.ec *)

(* Pseudorandom Functions (PRFs) *)

prover [""].  (* no SMT solvers *)

require import AllCore Distr DBool FSet SmtMap.

(* theory parameters *)

type key.  (* PRF keys *)

op dkey : key distr.  (* full, uniform and lossless distribution on keys *)

(* full means every element of type has non-zero value in
   distribution; uniform means every element of type with non-zero
   value in distribution has the same value in distribution; lossless
   means the sum of the type's values in distribution is 1 *)

axiom dkey_fu : is_full dkey.
axiom dkey_uni : is_uniform dkey.
axiom dkey_ll : is_lossless dkey.

type text.  (* texts *)

op dtext : text distr.  (* full, uniform and lossless distribution on texts *)

axiom dtext_fu : is_full dtext.
axiom dtext_uni : is_uniform dtext.
axiom dtext_ll : is_lossless dtext.

op F : key -> text -> text.  (* PRF *)

(* end of theory parameters *)

(* module type of random functions *)

module type RF = {
  (* initialization *)
  proc * init() : unit

  (* application to a text *)
  proc f(x : text) : text
}.

(* random function implementation using PRF *)

module PRF : RF = {
  var key : key

  proc init() : unit = {
    key <$ dkey;
  }

  proc f(x : text) : text = {
    var y : text;
    y <- F key x;
    return y;
  }
}.

(* random function implemention using true randomness *)

module TRF : RF = {
  (* mp is a finite map associating texts with texts *)
  var mp : (text, text) fmap

  proc init() : unit = {
    mp <- empty;  (* empty map *)
  }

  proc f(x : text) : text = {
    if (! x \in mp) {   (* give x a random value in *)
      mp.[x] <$ dtext;  (* mp if not already in mp's domain *)
    }
    return oget mp.[x];
  }
}.

(* module type of random function adversaries, parameterized
   by random function RF

   adversary may only call RF.f (it can't initialize the random
   function) *)

module type RFA (RF : RF) = {
  proc * main() : bool {RF.f}
}.

(* random function game:

   `|Pr[GRF(PRF, RFA).main() @ &m : res] -
     Pr[GRF(TRF, RFA).main() @ &m : res]|

   may be negligible, if F is "good", RFA is limited and RFA can't
   read/write the global variables of PRF/TRF *)

module GRF (RF : RF, RFA : RFA) = {
  module A = RFA(RF)

  proc main() : bool = {
    var b : bool;
    RF.init();
    b <@ A.main();
    return b;
  }
}.
