(* SimpLogic.ec *)

prover [""].  (* no SMT solvers *)

lemma fa_imp_not_ex_not (P : 'a -> bool) :
  (forall (x : 'a), P x) => ! exists (x : 'a), ! P x.
proof.
move => fa_x_P_x.
case (exists x, ! P x) => [[] x not_P_x | //].
have // : P x by apply fa_x_P_x.
qed.

lemma not_ex_not_imp_fa (P : 'a -> bool) :
  ! (exists (x : 'a), ! P x) => forall (x : 'a), P x.
proof.
move => not_ex_x_not_P_x x.
case (P x) => [// | not_P_x].
have // : exists x, ! P x by exists x.
qed.

lemma fa_iff_not_ex_not (P : 'a -> bool) :
  (forall (x : 'a), P x) <=> ! exists (x : 'a), ! P x.
proof.
split; [apply fa_imp_not_ex_not | apply not_ex_not_imp_fa].
qed.
