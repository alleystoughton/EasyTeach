(* Aux.ec *)

(* Auxiliary Lemmas *)

(* Lemmas that probably should be in EasyCrypt Library *)

prover [""].  (* no SMT solvers *)

require import AllCore SmtMap.

lemma eq_except_ne_in (x y : 'a, mp1 mp2 : ('a, 'b) fmap) :
  eq_except (pred1 x) mp1 mp2 => y <> x =>
  y \in mp1 => y \in mp2.
proof.
move => /eq_exceptP @/pred1 eq_exc ne_y_x.
by rewrite 2!domE eq_exc.
qed.
