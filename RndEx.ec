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
proc.
seq 0 1 : (true).
rnd{2}.  (* rnd is figuring out the {0,1} is lossless *)
auto.
rnd (fun x => x ^^ b1{2}).
skip; progress.
by rewrite xorA xorK xor_false.
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
byphoare => //; proc.
(* rnd without an argument predicate tries to guess the predicate,
   and is often wrong

   one approach is to start with `rnd pred0`, where pred0
   is the predicate that satisfies nothing - this helps you
   figure out what the predicate should actually be

   predT is the predicate that satisfies everything

   `pred1 x` is the predicate that only satisfies x

   `mu d P` means the probability that choosing a value
   from distribution d satisfies P (i.e., the sum of the
   weights of all the elements of the type that P likes)

   `mu1 d x` appreviates `mu d (pred1 x)`, and so means the
   probability that choosing a value from d results in x,
   i.e., the weight of x in d *)
rnd (pred1 true).
skip => />.
split => [| _ v _].
(* do `search {0,1}` *)
by rewrite dbool1E.
by rewrite /pred1.
qed.

lemma N &m :
  Pr[N.f() @ &m : res] = 1%r / 2%r.
proof.
by rewrite -(M_N_true &m) (M &m).
qed.
