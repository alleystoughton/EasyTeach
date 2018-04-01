(* PseudoRandFun.ec *)

(* Pseudorandom Functions (PRFs) *)

prover ["!"].  (* no SMT solvers *)

require import AllCore Distr DBool FSet NewFMap.

(* theory parameters *)

type key.  (* PRF keys *)

op dkey : key distr.  (* full, uniform and lossless distribution on keys *)

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
  var mp : (text, text) fmap

  proc init() : unit = {
    mp <- map0;
  }

  proc f(x : text) : text = {
    if (! mem (dom mp) x) {
      mp.[x] <$ dtext;
    }
    return oget mp.[x];
  }
}.

(*
lemma TRF_f (x' : text) (mp : (text, text)fmap) :
  equiv[TRF.f ~ TRF.f :
        ={x, TRF.mp} /\ x{1} = x' /\ mp = TRF.mp{1} ==>
        ={res, TRF.mp} /\ mem (dom TRF.mp{1}) x' /\
        oget TRF.mp{1}.[x'] = res{1}].
proof.
proc.
if => //; auto => /> &2 _ mp _.
by rewrite domP_eq.
qed.
*)

lemma TRF_f_ll : islossless TRF.f.
proof.
proc; if; [auto => /> _ _; apply dtext_ll | auto].
qed.

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

   may be negligible, if F is "good" and RFA is limited *)

module GRF (RF : RF, RFA : RFA) = {
  module A = RFA(RF)

  proc main() : bool = {
    var b : bool;
    RF.init();
    b <@ A.main();
    return b;
  }
}.
