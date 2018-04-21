(* SimpLogic-initial.ec *)

(* less sophisticated version of SimpLogic.ec *)

prover [""].  (* no SMT solvers *)

lemma fa_imp_not_ex_not (P : 'a -> bool) :
  (forall (x : 'a), P x) => ! exists (x : 'a), ! P x.
proof.
move => fa_x_P_x.
case (exists x, ! P x).
move => ex_x_not_P_x.
elim ex_x_not_P_x.
move => x not_P_x.
have P_x : P x.
  apply (fa_x_P_x x).
trivial.
trivial.
qed.

lemma not_ex_not_imp_fa (P : 'a -> bool) :
  ! (exists (x : 'a), ! P x) => forall (x : 'a), P x.
proof.
move => not_ex_x_not_P_x x.
case (P x).
trivial.
move => not_P_x.
have ex_x_not_P_x : exists (x : 'a), ! P x.
  exists x.
  apply not_P_x.
trivial.
qed.

lemma fa_iff_not_ex_not (P : 'a -> bool) :
  (forall (x : 'a), P x) <=> ! exists (x : 'a), ! P x.
proof.
split.
apply fa_imp_not_ex_not.
apply not_ex_not_imp_fa.
qed.
