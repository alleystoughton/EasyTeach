(* Secure Message Communication via a One-time Pad, Formalized
   in Ordinary (Non-UC) Real/Ideal Paradigm Style *)

require import AllCore Distr.

(* minimal axiomatization of bitstrings *)

op n : int.  (* length of bitstrings *)

axiom ge0_n : 0 <= n.

type bits.  (* type of bitstrings *)

op zero : bits.  (* the all zero bitstring *)

op (^^) : bits -> bits -> bits.  (* pointwise exclusive or *)

axiom xorC (x y : bits) :
  x ^^ y = y ^^ x.

axiom xorA (x y z : bits) :
  x ^^ y ^^ z = x ^^ (y ^^ z).

axiom xor0_ (x : bits) :
  zero ^^ x = x.

lemma xor_0 (x : bits) :
  x ^^ zero = x.
proof.
by rewrite xorC xor0_.
qed.

axiom xorK (x : bits) :
  x ^^ x = zero.

lemma xor_double_same_right (x y : bits) :
  x ^^ y ^^ y = x.
proof.
by rewrite xorA xorK xor_0.
qed.

lemma xor_double_same_left (x y : bits) :
  y ^^ y ^^ x = x.
proof.
by rewrite xorK xor0_.
qed.

(* uniform, full and lossless distribution on bitstrings *)

op dbits : bits distr.

axiom dbits_ll : is_lossless dbits.

axiom dbits1E (x : bits) :
  mu1 dbits x = 1%r / (2 ^ n)%r.

lemma dbits_fu : is_full dbits.
proof.
move => x.
rewrite /support dbits1E.
by rewrite StdRing.RField.div1r StdOrder.RealOrder.invr_gt0
           lt_fromint powPos.
qed.

(* module type of Adversaries *)

module type ADV = {
  (* ask Adversary for message to securely communicate; the
     asterisk means get initializes Adversary's state *)

  proc * get() : bits

  (* let Adversary observe encrypted message being communicated *)

  proc obs(x : bits) : unit

  (* give Adversary decryption of received message *)

  proc put(x : bits) : bool
}.

(* Real Game, Parameterized by Adversary *)

module GReal (Adv : ADV) = {
  var pad : bits  (* one-time pad *)

  (* generate the one-time pad, sharing with both parties; we're
     assuming Adversary observes nothing when this happens *)

  proc gen() : unit = {
    pad <$ dbits;
  }

  (* the receiving and sending parties are the same, as encrypting
     and decrypting are the same *)

  proc party(x : bits) : bits = {
    return x ^^ pad;
  }

  proc main() : bool = {
    var b : bool;
    var x, y, z : bits;

    x <@ Adv.get();    (* get message from Adversary, give to Party 1 *)
    gen();             (* generate and share to parties one-time pad *)
    y <@ party(x);     (* Party 1 encrypts x, yielding y *)
    Adv.obs(y);        (* y is observed in transit between parties
                          by Adversary *)
    z <@ party(y);     (* y is decrypted by Party 2, yielding z *)
    b <@ Adv.put(z);   (* z is given to Adversary by Party 2, which chooses
                          boolean judgment *)
    return b;          (* return boolean judgment as game's result *)
  }    
}.

(* module type of Simulators *)

module type SIM = {
  (* choose gets no help to simulate encrypted message *)

  proc choose() : bits
}.

(* Ideal Game, parameterized by both Simulator and Adversary *)

module GIdeal(Sim : SIM, Adv : ADV) = {
  proc main() : bool = {
    var b : bool;
    var x, y : bits;

    x <@ Adv.get();     (* get message from Adversary *)
    y <@ Sim.choose();  (* simulate message encryption *)
    Adv.obs(y);         (* encryption simulation is observed by Adversary *)
    b <@ Adv.put(x);    (* x is given back to Adversary *)
    return b;           (* return Adversary's boolean judgment *)
  }    
}.

(* Simulator - part of proof, not security specification *)

module Sim : SIM = {
  proc choose() : bits = {
    var x : bits;
    x <$ dbits;
    return x;
  }
}.

(* enter section, so Adversary is in scope *)

section.

(* say Adv and GReal don't read/write each other's globals *)

declare module Adv : ADV{GReal}.

local lemma GReal_GIdeal :
  equiv[GReal(Adv).main ~ GIdeal(Sim, Adv).main :
        true ==> ={res}].
proof.
proc.
inline*.
seq 1 1 : (={x, glob Adv}).
call (_ : true).
auto.
seq 1 1 : (={x, glob Adv} /\ x{1} ^^ GReal.pad{1} = x0{2}).
rnd (fun z => x{1} ^^ z).
auto => /> &2.
split => [z _ | _].
by rewrite -xorA xor_double_same_left.
split => [z _ | _ z _].
by rewrite 2!dbits1E.
split => [| _].
apply dbits_fu.
by rewrite -xorA xor_double_same_left.
call (_ : true).
wp.
call (_ : true).
auto => />.
by rewrite xor_double_same_right.
qed.

lemma Sec &m :
  Pr[GReal(Adv).main() @ &m : res] =
  Pr[GIdeal(Sim, Adv).main() @ &m : res].
proof.
by byequiv GReal_GIdeal.
qed.

end section.

(* security theorem *)

lemma Security (Adv <: ADV{GReal}) &m :
  Pr[GReal(Adv).main() @ &m : res] =
  Pr[GIdeal(Sim, Adv).main() @ &m : res].
proof.
apply (Sec Adv &m).
qed.
