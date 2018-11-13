(* SimpLogic.ec *)

prover [""].  (* no SMT solvers *)

lemma fa_imp_not_ex_not (P : 'a -> bool) :
  (forall (x : 'a), P x) => ! exists (x : 'a), ! P x.
proof.

qed.

lemma not_ex_not_imp_fa (P : 'a -> bool) :
  ! (exists (x : 'a), ! P x) => forall (x : 'a), P x.
proof.

qed.

lemma fa_iff_not_ex_not (P : 'a -> bool) :
  (forall (x : 'a), P x) <=> ! exists (x : 'a), ! P x.
proof.

qed.

(* we can do the above using a lemma in the EasyCrypt Library: *)

lemma fa_iff_not_ex_not' (P : 'a -> bool) :
  (forall (x : 'a), P x) <=> ! exists (x : 'a), ! P x.
proof.
(* to see the lemma's statement, use
print negb_exists.
*)
qed.
