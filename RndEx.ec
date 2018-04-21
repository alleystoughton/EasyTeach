(* RndEx.ec *)

prover [""].  (* no SMT solvers *)

require import AllCore Bool Distr DBool.

module M = {
  proc f() : bool = {
    var b : bool;
    b <$ {0,1};
    return b;
  }
}.

module N = {
  proc f() : bool = {
    var b1, b2 : bool;
    b1 <$ {0,1};
    b2 <$ {0,1};
    return b1 ^^ b2;  (* exclusive or *)
  }
}.

lemma M_N_equiv :
  equiv[M.f ~ N.f : true ==> ={res}].
proof.
proc.
seq 0 1 : (true).
rnd{2}; skip; apply dbool_ll.
rnd (fun x => x ^^ b1{2}).
skip; progress.
by rewrite xorA xorK xor_false.
by rewrite !dbool1E.
rewrite dbool_fu.
by rewrite xorA xorK xor_false.
by rewrite xorC xorA xorK xor_false. 
qed.

lemma M_N_true &m :
  Pr[M.f() @ &m : res] = Pr[N.f() @ &m : res].
proof.
by byequiv M_N_equiv.
qed.

lemma M_N_false &m :
  Pr[M.f() @ &m : ! res] = Pr[N.f() @ &m : ! res].
proof.
by byequiv M_N_equiv.
qed.

lemma M &m :
  Pr[M.f() @ &m : res] = 1%r / 2%r.
proof.
byphoare => //.
proc; rnd; skip => />.
by rewrite dboolE.
qed.

lemma N &m :
  Pr[N.f() @ &m : res] = 1%r / 2%r.
proof.
by rewrite -(M_N_true &m) (M &m).
qed.
