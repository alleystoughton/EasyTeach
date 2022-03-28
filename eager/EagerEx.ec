(* eager sampling example *)

prover [""].

require import AllCore Distr SmtMap DBool.
require RedundantHashing.  (* abstract theory - can't import *)

module type OR = {
  proc * init(b_o : bool option) : unit

  proc get() : bool
}.

module Or : OR = {
  var b_opt : bool option

  proc init(b_o : bool option) : unit = {
    b_opt <- b_o;
  }

  proc get() : bool = {
    var b : bool;
    if (b_opt = None) {
      b <$ {0,1};
      b_opt <- Some b;
    }
    return oget b_opt;
  }
}.

module type ADV (O : OR) = {
  proc * main() : bool {O.get}
}.

module GEager (Adv : ADV) = {
  proc main() : bool = {
    var b : bool;
    b <$ {0,1};
    Or.init(Some b);
    b <@ Adv(Or).main();
    return b;
  }
}.

module GLazy (Adv : ADV) = {
  proc main() : bool = {
    var b : bool;
    Or.init(None);
    b <@ Adv(Or).main();
    return b;
  }
}.

(* see end of section for main lemma *)

section.

declare module Adv <: ADV{-Or}.

type input = [TheBool].  (* TheBool is only element of input *)

local clone RedundantHashing as RH with
  type input <- input,
  type output <- bool,
  op doutput <- {0,1}
proof *.
realize doutput_ll. rewrite dbool_ll. qed.

module OrFromHashing(H : RH.HASHING) : OR = {
  (* init must exist, but not used *)
  proc init(b_opt : bool option) : unit = {}

  proc get() : bool = {
    var b : bool;
    b <@ H.hash(TheBool);  (* ordinary hashing *)
    return b;
  }
}.  

local module (HashAdv : RH.HASHING_ADV) (H : RH.HASHING) = {
  proc main() : bool = {
    var b : bool;
    H.rhash(TheBool);  (* redundant hashing *)
    b <@ Adv(OrFromHashing(H)).main();
    return b;
  }
}.

local lemma GEager_NonOptHashing &m :
  Pr[GEager(Adv).main() @ &m : res] =
  Pr[RH.GNonOptHashing(HashAdv).main() @ &m : res].
proof.    
byequiv => //.
proc.
inline*; wp.
seq 3 4 :
  (Or.b_opt{1} <> None /\
   RH.NonOptHashing.mp{2}.[TheBool] = Some (oget Or.b_opt{1})).
wp; sp.
rcondt{2} 1; first auto; progress; by rewrite mem_empty.
wp; rnd; auto; progress; by rewrite get_set_sameE.
call
  (_ : 
   Or.b_opt{1} <> None /\
   RH.NonOptHashing.mp{2}.[TheBool] = Some (oget Or.b_opt{1})).
proc.
inline*.
rcondf{1} 1; first auto.
rcondf{2} 2; first auto.
progress; by rewrite domE H0.
auto; progress; by rewrite H0.
auto.
qed.

local lemma GLazy_OptHashing &m :
  Pr[GLazy(Adv).main() @ &m : res] =
  Pr[RH.GOptHashing(HashAdv).main() @ &m : res].
proof.    
byequiv => //.
proc.
inline*; wp.
seq 2 2 : (Or.b_opt{1} = None /\ RH.OptHashing.mp{2} = empty).
auto.
call
  (_ :
   Or.b_opt{1} = None /\ RH.OptHashing.mp{2} = empty \/
   Or.b_opt{1} <> None /\
   RH.OptHashing.mp{2}.[TheBool] = Some (oget Or.b_opt{1})).
proc; inline*; sp.
if.
move => &1 &2 [#] -> _ [[#] -> -> | [#] -> /=].
by rewrite mem_empty.
by rewrite domE => ->.
auto => /> &2 -> bL _.
by rewrite get_set_sameE.
auto => /> &1 &2 [] // [#] -> -> //.
auto.
qed.

lemma eag_laz &m :
  Pr[GEager(Adv).main() @ &m : res] =
  Pr[GLazy(Adv).main() @ &m : res].
proof.
by rewrite (GEager_NonOptHashing &m) (GLazy_OptHashing &m)
           (RH.GNonOptHashing_GOptHashing HashAdv &m).
qed.

end section.

lemma eager_lazy (Adv <: ADV{-Or}) &m :
  Pr[GEager(Adv).main() @ &m : res] = Pr[GLazy(Adv).main() @ &m : res].
proof.
apply (eag_laz Adv &m).
qed.
