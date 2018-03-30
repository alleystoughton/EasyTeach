(* IND-CPA (indistinguishability under chosen plaintext attack)
   security for symmetric encryption built out of pseudorandom
   function *)

prover ["!"].  (* no SMT solvers *)

require export AllCore Distr DBool NewFMap FSet Mu_mem.
require import StdBigop. import Bigreal BRA.
require import StdOrder. import RealOrder.
require import StdRing. import RField.
require BitWord FelTactic.

(* require but don't import theories for symmetric encryption and
   pseudorandom functions *)

require SymEnc PseudoRandFun.

(* PRF and encryption keys: bitstrings of length key_len *)

op key_len : {int | 0 < key_len} as gt0_key_len.

clone BitWord as Key with
  op n <- key_len
proof gt0_n by apply gt0_key_len.

type key = Key.word.

op key0 : key = Key.zerow.  (* all 0 key *)

(* full/uniform/lossless distribution *)

op dkey : key distr = Key.DWord.dunifin.

lemma dkey_fu : is_full dkey.
proof. apply Key.DWord.dunifin_fu. qed.

lemma dkey_uni : is_uniform dkey.
proof. apply Key.DWord.dunifin_uni. qed.

lemma dkey_ll : is_lossless dkey.
proof. apply Key.DWord.dunifin_ll. qed.

(* texts: bitstrings of length text_len *)

op text_len : {int | 0 < text_len} as gt0_text_len.

clone BitWord as Text with
  op n <- text_len
proof gt0_n by apply gt0_text_len.

type text = Text.word.

op text0 : text = Text.zerow.  (* all 0 text *)

op (+^) : text -> text -> text = Text.(+^).  (* bitwise exclusive or *)

lemma text_xorK (x : text) : x +^ x = text0.
proof. apply Text.xorwK. qed.

lemma text_xorA (x y z : text) :
  x +^ (y +^ z) = x +^ y +^ z.
proof. apply Text.xorwA. qed.

lemma text_xor_rid (x : text) :
  x +^ text0 = x.
proof. apply Text.xorw0. qed.

lemma text_xor_lid (x : text) :
  text0 +^ x = x.
proof. by rewrite Text.xorwC text_xor_rid. qed.

(* full/uniform/lossless distribution *)

op dtext : text distr = Text.DWord.dunifin.

lemma dtext_fu : is_full dtext.
proof. apply Text.DWord.dunifin_fu. qed.

lemma dtext_uni : is_uniform dtext.
proof. apply Text.DWord.dunifin_uni. qed.

lemma dtext_ll : is_lossless dtext.
proof. apply Text.DWord.dunifin_ll. qed.

lemma mu1_dtext (x : text) :
  mu1 dtext x = 1%r / (2 ^ text_len)%r.
proof. by rewrite Text.DWord.dunifin1E Text.word_card. qed.

lemma mu_dtext_mem (xs : text fset) :
  mu dtext (mem xs) = (card xs)%r / (2 ^ text_len)%r.
proof.
apply (mu_mem _ _ (1%r / (2 ^ text_len)%r)) => x mem_xs_x.
apply mu1_dtext.
qed.

(* pseudorandom function (PRF)

   the definition of F could be spelled out, and is considered public
   -- i.e., any adversary is entitled to use F and know its
   definition *)

op F : key -> text -> text.  (* PRF *)

(* clone and import pseudorandom function and symmetric encryption
   theories, substituting for parameters, and proving the needed
   axioms *)

clone import PseudoRandFun as PRF with
  type key  <- key,
  op dkey   <- dkey,
  type text <- text,
  op dtext  <- dtext,
  op F      <- F
proof *.
realize dkey_fu. apply dkey_fu. qed.
realize dkey_uni. apply dkey_uni. qed.
realize dkey_ll. apply dkey_ll. qed.
realize dtext_fu. apply dtext_fu. qed.
realize dtext_uni. apply dtext_uni. qed.
realize dtext_ll. apply dtext_ll. qed.

type cipher = text * text.  (* ciphertexts *)

op limit : {int | 0 <= limit} as ge0_limit.  (* encryption oracle limit *)

clone import SymEnc as SE with
  type key    <- key,
  type text   <- text,
  type cipher <- cipher,
  op ciph_def <- (text0, text0),
  op limit    <- limit
proof *.
realize ge0_limit. apply ge0_limit. qed.

(* definition of encryption

   key_gen and enc are probabilistic, but dec is deterministic

   the module has no state *)

module Enc : ENC = {
  proc key_gen() : key = {
    var k : key;
    k <$ dkey;
    return k;
  }

  proc enc(k : key, x : text) : cipher = {
    var u : text;
    u <$ dtext;
    return (u, x +^ F k u);
  }

  proc dec(k : key, c : cipher) : text = {
    var u, v : text;
    (u, v) <- c;
    return v +^ F k u;
  }
}.

(* prove encryption scheme is stateless *)

lemma enc_stateless (g1 g2 : glob Enc) :
  g1 = g2.
proof. trivial. qed.

(* lemma proving correctness of encryption *)

lemma correctness :
  phoare[Cor(Enc).main : true ==> res] = 1%r.
proof.
proc; inline *; auto; progress.
apply dkey_ll.
apply dtext_ll.
by rewrite -text_xorA text_xorK text_xor_rid.
qed.

(* module turning an encryption adversary Adv into a random function
   adversary

   used in upper bound of IND-CPA security theorem, but to understand
   why it's defined the way it is, need to read proof

   note that it doesn't interact with any other module (except though
   its Adv and RF parameters) *)

module Adv2RFA(Adv : ADV, RF : RF) = {
  module EO : EO = {  (* uses RF.f *)
    var ctr : int

    proc init() = {
      ctr <- 0;  (* RF.init will be called by GRF *)
    }

    proc enc(x : text) : cipher = {
      var u, v : text; var c : cipher;
      if (ctr < limit) {
        ctr <- ctr + 1;
        u <$ dtext;
        v <@ RF.f(u);
        c <- (u, x +^ v);
      }
      else {
        c <- (text0, text0);
      }
      return c;
    }
  }

  module A = Adv(EO)

  proc main() : bool = {
    var b, b' : bool; var x1, x2 : text; var c : cipher;
    EO.init();
    (x1, x2) <@ A.choose();
    b <$ {0,1};
    c <@ EO.enc(b ? x1 : x2);
    b' <@ A.guess(c);
    return b = b';
  }
}.

(* see after section for security theorem *)

section.

(* declare adversary with module restrictions: Adv can't
   interact with EncO, PRF, TRF or Adv2RFA *)

declare module Adv : ADV{EncO, PRF, TRF, Adv2RFA}.

(* axiomatize losslessness of Adv's procedures *)

axiom Adv_choose_ll :
  forall (EO <: EO{Adv}),
  islossless EO.enc => islossless Adv(EO).choose.

axiom Adv_guess_ll :
  forall (EO <: EO{Adv}),
  islossless EO.enc => islossless Adv(EO).guess.

module EO : EO = EncO(Enc).  (* standard encryption oracle *)

(* version of encryption oracle that takes implementation of
   RF as argument

   annotated to keep track in global variable inps of random inputs to
   RF.f; if the same input is used twice, global variable dup is set
   to true *)

local module EO_RF (RF : RF) : EO = {
  var ctr : int
  var inps : text fset
  var dup : bool

  proc init() = {
    RF.init();
    ctr <- 0; inps <- fset0; dup <- false;
  }

  proc enc(x : text) : cipher = {
    var u, v : text; var c : cipher;
    if (ctr < limit) {
      ctr <- ctr + 1;
      u <$ dtext;
      if (mem inps u) {
        dup <- true;
      }
      inps <- inps `|` fset1 u;
      v <@ RF.f(u);
      c <- (u, x +^ v);
    }
    else {
      c <- (text0, text0);
    }  
    return c;
  }
}.

local lemma EO_RF_TRF_enc_dup_pres :
  phoare[EO_RF(TRF).enc : EO_RF.dup ==> EO_RF.dup] = 1%r.
proof.
proc; if; [wp; call TRF_f_ll; auto => /> _ _ _; apply dtext_ll | auto].
qed.

(* game parameterized by implementation of RF, and using EO_RF *)

local module G1 (RF : RF) = {
  module E = EO_RF(RF)
  module A = Adv(E)

  proc main() : bool = {
    var b, b' : bool; var x1, x2 : text; var c : cipher;
    E.init();
    (x1, x2) <@ A.choose();
    b <$ {0,1};
    c <@ E.enc(b ? x1 : x2);
    b' <@ A.guess(c);
    return b = b';
  }
}.    

local lemma EO_EO_RF_PRF_enc :
  equiv[EO.enc ~ EO_RF(PRF).enc :
        ={x} /\ ={key}(EncO, PRF) /\ ={ctr}(EncO, EO_RF) ==>
        ={res} /\ ={key}(EncO, PRF) /\ ={ctr}(EncO, EO_RF)].
proof.       
proc; inline*.
if => //; [wp; rnd; auto | auto].
qed.

local lemma INDCPA_G1_PRF &m :
  Pr[INDCPA(Enc, Adv).main() @ &m : res] = Pr[G1(PRF).main() @ &m : res].
proof.
byequiv => //; proc.
call (_ : ={key}(EO, PRF) /\ ={ctr}(EO, EO_RF)).
apply EO_EO_RF_PRF_enc.
call EO_EO_RF_PRF_enc.
rnd.
call (_ : ={key}(EO, PRF) /\ ={ctr}(EO, EO_RF)).
apply EO_EO_RF_PRF_enc.
inline*; auto.
qed.

local lemma G1_GRF (RF <: RF{EO_RF, Adv, Adv2RFA}) &m :
  Pr[G1(RF).main() @ &m : res] =
  Pr[GRF(RF, Adv2RFA(Adv)).main() @ &m : res].
proof.
byequiv => //; proc.
inline GRF(RF, Adv2RFA(Adv)).A.main G1(RF).E.init
       Adv2RFA(Adv, RF).EO.init.
wp; sim.
qed.

local lemma INDCPA_G1_TRF &m :
  `|Pr[INDCPA(Enc, Adv).main() @ &m : res] -
    Pr[G1(TRF).main() @ &m : res]| =
  `|Pr[GRF(PRF, Adv2RFA(Adv)).main() @ &m : res] -
    Pr[GRF(TRF, Adv2RFA(Adv)).main() @ &m : res]|.
proof.
by rewrite (INDCPA_G1_PRF &m) (G1_GRF PRF &m) (G1_GRF TRF &m).
qed.

(* version of encryption oracle where a random text is xor'ed with
   plaintext to form second component of ciphertext

   the "I" in name stands for "independent", as in independent of
   first component of ciphertext *)

local module EO_I : EO = {
  var ctr : int
  var inps : text fset
  var dup : bool

  proc init() : unit = {
    ctr <- 0; inps <- fset0; dup <- false;
  }

  proc enc(x : text) : cipher = {
    var c : cipher; var u, v : text;
    if (ctr < limit) {
      ctr <- ctr + 1;
      u <$ dtext;
      if (mem inps u) {
        dup <- true;
      }
      inps <- inps `|` fset1 u;
      v <$ dtext;  (* note *)
      c <- (u, x +^ v);
    }
    else {
      c <- (text0, text0);
    }  
    return c;
  }
}.

local lemma EO_I_enc_dup_pres :
  phoare [EO_I.enc : EO_I.dup ==> EO_I.dup] = 1%r.
proof.
proc; if; [auto => /> _ _ _; apply dtext_ll | auto].
qed.

(* game using EO_I *)

local module G2 = {
  module A = Adv(EO_I)

  proc main() : bool = {
    var b, b' : bool; var x1, x2 : text; var c : cipher;
    EO_I.init();
    (x1, x2) <@ A.choose();
    b <$ {0,1};
    c <@ EO_I.enc(b ? x1 : x2);
    b' <@ A.guess(c);
    return b = b';
  }
}.    

(* in the following lemmas, we using reasoning up to failure (up to
   bad reasoning), with dup being the failure event *)

local lemma EO_RF_TRF_EO_I_enc dup' :
  equiv
  [EO_RF(TRF).enc ~ EO_I.enc :
   ={dup}(EO_RF, EO_I) /\ dup' = EO_RF.dup{1} /\
   (! EO_RF.dup{1} =>
    ={x} /\ ={ctr, inps}(EO_RF, EO_I) /\
    dom TRF.mp{1} = EO_RF.inps{1}) ==>
   ={dup}(EO_RF, EO_I) /\
   (! EO_RF.dup{1} => ! dup' /\
    ={res} /\ ={ctr, inps}(EO_RF,EO_I) /\
    dom TRF.mp{1} = EO_RF.inps{1})].
proof.
proc.
case (EO_RF.dup{1}).
if{1}.
wp; call{1} TRF_f_ll.
auto; if{2}; auto => /> &1 &2 _ _ _ _; apply dtext_ll.
wp; if{2}; auto => /> &1 &2  _ _ _ _; apply dtext_ll.
(* ! EO_RF.dup{1} *)
if; first move => /> &1 &2 not_dup_imp /not_dup_imp //.
seq 2 2 :
  (={x, u} /\ ={ctr, inps, dup}(EO_RF, EO_I) /\ ! EO_RF.dup{1} /\
   dup' = EO_RF.dup{1} /\ dom TRF.mp{1} = EO_RF.inps{1}).
auto => /> &1 &2 not_dup_imp /not_dup_imp //.
if => //.
auto; call{1} TRF_f_ll.
auto => /> &1 &2 _ _; apply dtext_ll.
inline TRF.f; rcondt{1} 3.
move => &m; auto.
auto; progress.
by rewrite getP_eq oget_some.
by rewrite dom_set.
auto => /> &1 &2 not_dup_eq /not_dup_eq //.
qed.

local lemma G1_TRF_G2_main :
  equiv
  [G1(TRF).main ~ G2.main :
   true ==>
   ={dup}(EO_RF, EO_I) /\ (! EO_RF.dup{1} => ={res})].
proof.
proc; inline TRF.init EO_I.init EO_RF(TRF).init.
seq 4 3 :
  (={ctr, inps, dup}(EO_RF,EO_I) /\ dom TRF.mp{1} = EO_RF.inps{1}).
auto => />; apply dom0.
seq 1 1 :
 (={dup}(EO_RF,EO_I) /\
  (! EO_RF.dup{1} => 
   ={glob Adv, x1, x2} /\ ={ctr, inps}(EO_RF,EO_I) /\
   dom TRF.mp{1} = EO_RF.inps{1})).
call
  (_ :
   ={ctr, inps, dup}(EO_RF,EO_I) /\ dom TRF.mp{1} = EO_RF.inps{1} ==>
   ={dup}(EO_RF,EO_I) /\
   (! EO_RF.dup{1} => 
    ={res, glob Adv} /\ ={ctr, inps}(EO_RF,EO_I) /\
    dom TRF.mp{1} = EO_RF.inps{1})).
proc
  (EO_I.dup)
  (={ctr, inps, dup}(EO_RF,EO_I) /\ dom TRF.mp{1} = EO_RF.inps{1})
  (EO_RF.dup{1}) => //.
by move => &1 &2; case (EO_I.dup{2}) => // _ ->.
apply Adv_choose_ll.
exists* EO_RF.dup{1}; elim* => dup'.
conseq (EO_RF_TRF_EO_I_enc dup') => //.
by move => /> &2 ->.
move => &2 _; apply EO_RF_TRF_enc_dup_pres.
move => &1; by conseq EO_I_enc_dup_pres.
auto => /> res_L res_R Adv_L inps_L n_L mp_L Adv_R dup_R inps_R n_R
        not_dup_R_eq /not_dup_R_eq //.
seq 1 1 :
  (={b} /\ ={dup}(EO_RF, EO_I) /\
   (! EO_RF.dup{1} =>
    ={glob Adv, x1, x2} /\ ={ctr, inps}(EO_RF, EO_I) /\
    dom TRF.mp{1} = EO_RF.inps{1})); first auto.
seq 1 1 :
  (={b} /\ ={dup}(EO_RF, EO_I) /\
   (! EO_RF.dup{1} =>
    ={glob Adv, c} /\ ={ctr, inps}(EO_RF, EO_I) /\
    dom TRF.mp{1} = EO_RF.inps{1})).
exists* EO_RF.dup{1}; elim* => dup'.
call (EO_RF_TRF_EO_I_enc dup'); auto.
move => /> &1 &2 not_dup_eq1.
split => [/not_dup_eq1 // |].
move => _ res_L res_R ctr_L inps_L mp_L ctr_R dup_R inps_R
        not_dup_R_eq /not_dup_R_eq /> /not_dup_eq1 //.
exists* EO_RF.dup{1}; elim* => dup'.
call
  (_ :
   ={dup}(EO_RF, EO_I) /\ dup' = EO_RF.dup{1} /\
   (! EO_RF.dup{1} =>
    ={glob Adv, c} /\ ={ctr, inps}(EO_RF, EO_I) /\
    dom TRF.mp{1} = EO_RF.inps{1}) ==>
   ={dup}(EO_RF, EO_I) /\
   (! EO_RF.dup{1} => ! dup' /\
    ={res} /\ ={ctr, inps}(EO_RF, EO_I) /\ dom TRF.mp{1} = EO_RF.inps{1})).
proc
  (EO_I.dup)
  (={ctr, inps, dup}(EO_RF, EO_I) /\ dom TRF.mp{1} = EO_RF.inps{1} /\ ! dup')
  (EO_RF.dup{1}).
move => /> &1 &2 not_dup_eq /not_dup_eq //.
move => &1 &2; case (EO_I.dup{2}) => />.
apply Adv_guess_ll.
conseq (EO_RF_TRF_EO_I_enc dup').
by move => /> &2 -> ->.
by move => />.
move => &2 _; apply EO_RF_TRF_enc_dup_pres.
move => &1; by conseq EO_I_enc_dup_pres.
auto.
move => /> &1 &2 not_dup_eq res_L res_R inps_L n_L mp_L dup_R inps_R n_R
        not_dup_R_eq /not_dup_R_eq //.
qed.

(* use failure event lemma tactic (fel) to upper bound probability
   that G2.main results in failure event being set *)

local lemma G2_main_dup_ub &m :
  Pr[G2.main() @ &m : EO_I.dup] <=
  (limit * (limit - 1))%r / (2 ^ (text_len + 1))%r.
proof.
fel
  (* number of lines of G2.main needed to initialize counter, failure
     event and invariant *)
  1
  EO_I.ctr  (* counter *)
  (* upper bound in terms of current counter of probability that failure
     event is set during one run of oracle *)
  (fun n, (n%r) * (1%r / (2 ^ text_len)%r))
  limit  (* counter limit *)
  EO_I.dup  (* failure event *)
  (* precondition on enc: if it holds, then counter goes up and
     failure might happen; if it doesn't hold, then counter doesn't go
     down, and failure status preserved *)
  [EO_I.enc : (EO_I.ctr < limit)]
  (* invariant *)
  (EO_I.ctr <= limit /\ card EO_I.inps <= EO_I.ctr) => //.
(* 1 *)
by rewrite -mulr_suml sumidE 1:ge0_limit
           powS 1:ltzW 1:gt0_text_len (fromintM 2) mul1r -mulrA -invfM.
(* 2 *)
inline*; auto.
move => />; split; [rewrite ge0_limit | by rewrite fcards0].
(* 3 *)
proc; rcondt 1; first auto.
wp; rnd; wp; rnd (mem EO_I.inps).
move => bd; auto => /> &hr _ _ not_dup _ _.
split => [| _ x _ not_x_in_inps_imp_dup].
by rewrite mu_dtext_mem ler_wpmul2r 1:invr_ge0 le_fromint
           1:ltzW 1:powPos.
case (x \in EO_I.inps{hr}) => // not_x_in_inps.
by have := not_x_in_inps_imp_dup not_x_in_inps.
(* 4 *)
move => c; proc; if.
auto => /> &hr ctr_lt_limit _ card_inps_le_ctr x _ y _.
split; first by rewrite ltz_addl.
split; first by rewrite -ltzE.
rewrite fcardU fcard1.
pose m := card (EO_I.inps{hr} `&` fset1 x).
have ge0_m : 0 <= m by rewrite /m fcard_ge0.
apply (lez_trans (card EO_I.inps{hr} + 1)).
rewrite IntOrder.ler_subl_addr.
pose l := card EO_I.inps{hr} + 1.
by rewrite -{1}addz0 lez_add2l.
by rewrite lez_add2r.
auto.
(* 5 *)
move => b c; proc; if; auto.
qed.

local lemma G1_TRF_G2 &m :
  `|Pr[G1(TRF).main() @ &m : res] - Pr[G2.main() @ &m : res]| <=
   (limit * (limit - 1))%r / (2 ^ (text_len + 1))%r.
proof.
rewrite (RealOrder.ler_trans Pr[G2.main() @ &m : EO_I.dup]);
  last 1 apply (G2_main_dup_ub &m).
byequiv
  (_ :
   true ==>
   (={dup}(EO_RF, EO_I)) /\ (! EO_I.dup{2} => ={res})) :
  (EO_RF.dup) => //; last first.
move => &1 &2 [#] -> not_dup_eq /=.
by rewrite -eq_iff.
by conseq G1_TRF_G2_main.
qed.

(* now we use triangular inequality to summarize: *)

local lemma INDCPA_G2 &m :
  `|Pr[INDCPA(Enc, Adv).main() @ &m : res] - Pr[G2.main() @ &m : res]| <=
  `|Pr[GRF(PRF, Adv2RFA(Adv)).main() @ &m : res] -
    Pr[GRF(TRF, Adv2RFA(Adv)).main() @ &m : res]| +
  (limit * (limit - 1))%r / (2 ^ (text_len + 1))%r.
proof.
rewrite
  (ler_trans
   (`|Pr[INDCPA(Enc, Adv).main() @ &m : res] - Pr[G1(TRF).main() @ &m : res]| +
    `|Pr[G1(TRF).main() @ &m : res] - Pr[G2.main() @ &m : res]|))
  1:ler_dist_add (INDCPA_G1_TRF &m) ler_add2l (G1_TRF_G2 &m).
qed.

(* version of encryption oracle where second part of ciphertext is
   randomly chosen (without being xor'ed with plaintext) *)

local module EO_R : EO = {
  var ctr : int

  proc init() : unit = {
    ctr <- 0;
  }

  proc enc(x : text) : cipher = {
    var c : cipher; var u, z : text;
    if (ctr < limit) {
      ctr <- ctr + 1;
      u <$ dtext; z <$ dtext;
      c <- (u, z);
    }
    else {
      c <- (text0, text0);
    }  
    return c;
  }
}.

local lemma EO_R_enc_ll : islossless EO_R.enc.
proof.
proc; if; [auto => /> _ _; apply dtext_ll | auto].
qed.

(* game based on EO_R *)

local module G3 = {
  module A = Adv(EO_R)

  proc main() : bool = {
    var b, b' : bool; var x1, x2 : text; var c : cipher;
    EO_R.init();
    (x1, x2) <@ A.choose();
    b <$ {0,1};
    c <@ EO_R.enc(text0);
    b' <@ A.guess(c);
    return b = b';
  }
}.    

local lemma EO_I_EO_R :
  equiv
  [EO_I.enc ~ EO_R.enc :
   ={ctr}(EO_I, EO_R) ==>
   ={res} /\ ={ctr}(EO_I, EO_R)].
proof.
proc.
if => //.
wp; rnd (fun u => x{1} +^ u); auto.
progress.
by rewrite text_xorA text_xorK text_xor_lid.
by rewrite 2!mu1_dtext.
rewrite dtext_fu.
by rewrite text_xorA text_xorK text_xor_lid.
auto.
qed.

local lemma G2_G3 &m :
  Pr[G2.main() @ &m : res] = Pr[G3.main() @ &m : res].
proof.
byequiv => //; proc.
call (_ : ={ctr}(EO_I, EO_R));
  first by conseq EO_I_EO_R.
call EO_I_EO_R.
rnd.
call (_ : ={ctr}(EO_I, EO_R));
  first by conseq EO_I_EO_R.
inline*; auto.
qed.

local lemma INDCPA_G3 &m :
  `|Pr[INDCPA(Enc,Adv).main() @ &m : res] - Pr[G3.main() @ &m : res]| <=
  `|Pr[GRF(PRF, Adv2RFA(Adv)).main() @ &m : res] -
    Pr[GRF(TRF, Adv2RFA(Adv)).main() @ &m : res]| +
  (limit * (limit - 1))%r / (2 ^ (text_len + 1))%r.
proof. rewrite -(G2_G3 &m) (INDCPA_G2 &m). qed.

(* probability that G3.main returns true *)

local lemma G3_prob &m :
  Pr[G3.main() @ &m : res] = 1%r / 2%r.
proof.
byphoare => //; proc.
swap 3 2; rnd.
call (_ : true);
  [apply Adv_guess_ll | apply EO_R_enc_ll | idtac].
call EO_R_enc_ll.
call (_ : true);
  [apply Adv_choose_ll | apply EO_R_enc_ll | idtac].
inline*; auto => /= x; by rewrite dbool1E.
qed.

lemma INDCPA' &m :
  `|Pr[INDCPA(Enc, Adv).main() @ &m : res] - 1%r / 2%r| <=
  `|Pr[GRF(PRF, Adv2RFA(Adv)).main() @ &m : res] -
    Pr[GRF(TRF, Adv2RFA(Adv)).main() @ &m : res]| +
  (limit * (limit - 1))%r / (2 ^ (text_len + 1))%r.
proof. rewrite -(G3_prob &m) (INDCPA_G3 &m). qed.

end section.

(* IND-CPA security theorem

   we need to assume Adv is lossless and that it doesn't interact with
   EO or PRF/TRF/Adv2RFA (which appear in the upper bound)

   because Enc is stateless, Adv may use it (and in any event could
   simulate it) *)

lemma INDCPA (Adv <: ADV{EO, PRF, TRF, Adv2RFA}) &m :
  (forall (EO <: EO{Adv}),
   islossless EO.enc => islossless Adv(EO).choose) =>
  (forall (EO <: EO{Adv}),
   islossless EO.enc => islossless Adv(EO).guess) =>
  `|Pr[INDCPA(Enc, Adv).main() @ &m : res] - 1%r / 2%r| <=
  `|Pr[GRF(PRF, Adv2RFA(Adv)).main() @ &m : res] -
    Pr[GRF(TRF, Adv2RFA(Adv)).main() @ &m : res]| +
  (limit * (limit - 1))%r / (2 ^ (text_len + 1))%r.
proof.
move => Adv_choose_ll Adv_guess_ll.
apply (INDCPA' Adv Adv_choose_ll Adv_guess_ll &m).
qed.
