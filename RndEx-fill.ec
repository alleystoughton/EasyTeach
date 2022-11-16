(* RndEx.ec *)

prover [""].  (* no SMT solvers *)

require import AllCore.
require import Bool.   (* defines ^^ as exclusive or *)
require import Distr.  (* (sub-)distributions *)
(* lossless, full, uniform distribution {0,1} on bool

   lossless means sum of the weights of type is 1%r
   full means every element of type is in support (has non-0 probability)
   uniform means all elements in support have same weight *)
require import DBool.

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

qed.

lemma M_N_true &m :
  Pr[M.f() @ &m : res] = Pr[N.f() @ &m : res].
proof.

qed.

lemma M_N_false &m :
  Pr[M.f() @ &m : ! res] = Pr[N.f() @ &m : ! res].
proof.

qed.

lemma M &m :
  Pr[M.f() @ &m : res] = 1%r / 2%r.
proof.

qed.

lemma N &m :
  Pr[N.f() @ &m : res] = 1%r / 2%r.
proof.

qed.
