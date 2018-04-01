(* Aux.ec *)

(* Auxiliary Lemmas *)

(* Lemmas that probably should be in EasyCrypt Library *)

prover ["!"].  (* no SMT solvers *)

require import AllCore FSet NewFMap.

lemma eq_except_dom (x y : 'a, mp1 mp2 : ('a, 'b) fmap) :
  eq_except mp1 mp2 (pred1 x) => y <> x =>
  y \in dom mp1 => y \in dom mp2.
proof.
move => /eq_exceptP @/pred1 eq_exc ne_y_x y_in_dom_mp1.
have mp2_y_eq : mp2.[y] = Some (oget mp1.[y])
  by rewrite -get_oget // eq_exc.
by rewrite in_dom mp2_y_eq.
qed.
