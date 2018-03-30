(* SymEnc.ec *)

(* Symmetric Encryption *)

prover ["!"].  (* no SMT solvers *)

require import AllCore Distr DBool.

(* theory parameters *)

type key.  (* encryption keys *)

type text.  (* plaintexts *)

type cipher.  (* ciphertexts *)

op ciph_def : cipher.  (* default ciphertext *)

op limit : {int | 0 <= limit} as ge0_limit.  (* encryption oracle limit *)

(* end theory parameters *)

(* module type of encryption schemes

   an encryption scheme Enc should be stateless, meaning that

     forall (g1 g2 : glob Enc), g1 = g2 *)

module type ENC = {
  (* key generation *)

  proc key_gen() : key

  (* encryption *)

  proc enc(k : key, x : text) : cipher

  (* decryption *)

  proc dec(k : key, c : cipher) : text
}.

(* module for checking correctness of encryption, parameterized
   by encryption scheme

   correctness means main returns true with probability 1, without any
   assumptions about value of x *)

module Cor (Enc : ENC) = {
  proc main(x : text) : bool = {
    var k : key; var c : cipher; var y : text;
    k <@ Enc.key_gen();
    c <@ Enc.enc(k, x);
    y <@ Enc.dec(k, c);
    return x = y;
  }
}.

(* module type of encryption oracles *)

module type EO = {
  (* initialization *)

  proc * init() : unit

  (* encryption of text *)

  proc enc(x : text) : cipher
}.

(* standard encryption oracle, constructed from an encryption
   scheme *)

module EncO (Enc : ENC) : EO = {
  var key : key
  var ctr : int

  proc init() : unit = {
    key <@ Enc.key_gen();
    ctr <- 0;
  }

  proc enc(x : text) : cipher = {
    var c : cipher;
    if (ctr < limit) {
      ctr <- ctr + 1;
      c <@ Enc.enc(key, x);
    }
    else {
      c <- ciph_def;  (* default result *)
    }  
    return c;
  }
}.

(* encryption adversary, parameterized by encryption oracle, EO

   both procedures may call EO.enc (but neither may call EO.init) *)

module type ADV (EO : EO) = {
  (* choose a pair of texts *)

  proc * choose() : text * text {EO.enc}

  (* given cipher of one of texts previously chosen, try to
     guess which text it came from (true means first text,
     false means second text) *)

  proc guess(c : cipher) : bool {EO.enc}
}.

(* IND-CPA security game, parameterized by an encryption scheme Enc
   and adversary Adv

   an encryption scheme is secure iff the probability of main
   returning true (Adv winning the game) is close to 1/2, i.e., Adv
   isn't doing much better than always guessing the ciphertext comes
   from the first plaintext

   if the limit on calls to EO.enc has already been exceeded at the
   point when one of x1/x2 is encrypted, then c (ciph_def) will be
   independent of x1/x2, giving Adv no chance of winning game

   note: Adv may directly use Enc (which is stateless) as much as
   it wants (and in any case could simulate it) *)

module INDCPA (Enc : ENC, Adv : ADV) = {
  module EO = EncO(Enc)       (* make EO from Enc *)
  module A = Adv(EO)          (* connect Adv to EO *)

  proc main() : bool = {
    var b, b' : bool; var x1, x2 : text; var c : cipher; var k : key;
    EO.init();                (* initialize EO *)
    (x1, x2) <@ A.choose();   (* let A choose plaintexts x1/x2 *)
    b <$ {0,1};               (* choose boolean b *)
    c <@ EO.enc(b ? x1 : x2); (* encrypt x1 if b = true, x2 if b = false *)
    b' <@ A.guess(c);         (* give ciphertext to A, which returns guess b' *)
    return b = b';            (* see if A guessed correctly, winning game *)
  }
}.
