(* SymEnc-PRF.ec *)

(* IND-CPA (indistinguishability under chosen plaintext attack)
   security for symmetric encryption built out of pseudorandom
   function *)

prover [""].  (* no SMT solvers *)

require export AllCore Distr DBool List SmtMap FSet Mu_mem.
require import StdBigop. import Bigreal BRA.
require import StdOrder. import RealOrder.
require import StdRing. import RField.
require import SmtMapAux.
require BitWord FelTactic.

(* require but don't import theories for symmetric encryption and
   pseudorandom functions - then will be cloned below *)

require SymEnc PseudoRandFun.

(* PRF and encryption keys: bitstrings of length key_len *)

(* this says key_len has type int, and the axiom gt0_key_len says
   that key_len is positive *)
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

lemma text_xorA (x y z : text) : x +^ (y +^ z) = x +^ y +^ z.
proof. apply Text.xorwA. qed.

lemma text_xorC (x y : text) : x +^ y = y +^ x.
proof. apply Text.xorwC. qed.

lemma text_xor_rid (x : text) : x +^ text0 = x.
proof. apply Text.xorw0. qed.

lemma text_xor_lid (x : text) : text0 +^ x = x.
proof. by rewrite Text.xorwC text_xor_rid. qed.

(* full/uniform/lossless distribution *)

op dtext : text distr = Text.DWord.dunifin.

lemma dtext_fu : is_full dtext.
proof. apply Text.DWord.dunifin_fu. qed.

lemma dtext_uni : is_uniform dtext.
proof. apply Text.DWord.dunifin_uni. qed.

lemma dtext_ll : is_lossless dtext.
proof. apply Text.DWord.dunifin_ll. qed.

lemma mu1_dtext (x : text) : mu1 dtext x = 1%r / (2 ^ text_len)%r.
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

(* encryption oracle limit before game's encryption *)
op limit_pre : {int | 0 <= limit_pre} as ge0_limit_pre.

(* encryption oracle limit after game's encryption *)
op limit_post : {int | 0 <= limit_post} as ge0_limit_post.

clone import SymEnc as SE with
  type key      <- key,
  type text     <- text,
  type cipher   <- cipher,
  op ciph_def   <- (text0, text0),
  op limit_pre  <- limit_pre,
  op limit_post <- limit_post
proof *.
realize ge0_limit_pre. apply ge0_limit_pre. qed.
realize ge0_limit_post. apply ge0_limit_post. qed.

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

lemma enc_stateless (g1 g2 : glob Enc) : g1 = g2.
proof. trivial. qed.

(* lemma proving correctness of encryption *)

lemma correctness : phoare[Cor(Enc).main : true ==> res] = 1%r.
proof.
proc; inline*; auto; progress.
apply dkey_ll.
apply dtext_ll.
by rewrite -text_xorA text_xorK text_xor_rid.
qed.

(* standard encryption oracle *)

module EO : EO = EncO(Enc).

(* module turning an encryption adversary Adv into a random function
   adversary

   used in upper bound of IND-CPA security theorem, but to understand
   why it's defined the way it is, need to read proof

   note that it doesn't interact with any other module (except though
   its Adv and RF parameters) *)

module Adv2RFA(Adv : ADV, RF : RF) = {
  module EO : EO = {  (* uses RF.f *)
    var ctr_pre : int
    var ctr_post : int

    proc init() : unit = {
      (* RF.init will be called by GRF *)
      ctr_pre <- 0; ctr_post <- 0;
    }

    proc enc_pre(x : text) : cipher = {
      var u, v : text; var c : cipher;
      if (ctr_pre < limit_pre) {
        ctr_pre <- ctr_pre + 1;
        u <$ dtext;
        v <@ RF.f(u);
        c <- (u, x +^ v);
      }
      else {
        c <- (text0, text0);
      }
      return c;
    }

    proc genc(x : text) : cipher = {
      var u, v : text; var c : cipher;
      u <$ dtext;
      v <@ RF.f(u);
      c <- (u, x +^ v);
      return c;
    }

    proc enc_post(x : text) : cipher = {
      var u, v : text; var c : cipher;
      if (ctr_post < limit_post) {
        ctr_post <- ctr_post + 1;
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
    c <@ EO.genc(b ? x1 : x2);
    b' <@ A.guess(c);
    return b = b';
  }
}.

(* see after section for security theorem

   in the proof, we connect the INDCPA game to a game that returns
   true with probability 1/2, via a sequence of 3 intermediate
   games *)

section.

(* declare adversary with module restrictions: Adv can't
   interact with EncO, PRF, TRF or Adv2RFA

   the scope of Adv is the rest of the section *)

declare module Adv : ADV{EncO, PRF, TRF, Adv2RFA}.

(* axiomatize losslessness (termination for all arguments) of Adv's
   procedures, for all encryption oracles whose accessible procedures
   are themselves lossless

   this is required for us to use upto bad reasoning *)

axiom Adv_choose_ll :
  forall (EO <: EO{Adv}),
  islossless EO.enc_pre => islossless Adv(EO).choose.

axiom Adv_guess_ll :
  forall (EO <: EO{Adv}),
  islossless EO.enc_post => islossless Adv(EO).guess.

(* version of encryption oracle that takes implementation of
   RF as argument - instrumented to detect two distinct
   kind of clashes *)

local module EO_RF (RF : RF) : EO = {
  var ctr_pre : int
  var ctr_post : int
  var inps_pre : text fset
  var clash_pre : bool
  var clash_post : bool
  var genc_inp : text

  proc init() = {
    RF.init();
    ctr_pre <- 0; ctr_post <- 0; inps_pre <- fset0;
    clash_pre <- false; clash_post <- false;
    genc_inp <- text0;
  }

  proc enc_pre(x : text) : cipher = {
    var u, v : text; var c : cipher;
    if (ctr_pre < limit_pre) {
      ctr_pre <- ctr_pre + 1;
      u <$ dtext;
      (* collect all of enc_pre's u's in set *)
      inps_pre <- inps_pre `|` fset1 u;
      v <@ RF.f(u);
      c <- (u, x +^ v);
    }
    else {
      c <- (text0, text0);
    }  
    return c;
  }

  proc genc(x : text) : cipher = {
    var u, v : text; var c : cipher;
    u <$ dtext;
    if (mem inps_pre u) {  (* did u also arise in enc_pre? *)
      clash_pre <- true;
    }
    genc_inp <- u;  (* save for reference in enc_post *)
    v <@ RF.f(u);
    c <- (u, x +^ v);
    return c;
  }

  proc enc_post(x : text) : cipher = {
    var u, v : text; var c : cipher;
    if (ctr_post < limit_post) {
      ctr_post <- ctr_post + 1;
      u <$ dtext;
      if (u = genc_inp) {  (* did u also arise in genc *)
        clash_post <- true;
      }
      v <@ RF.f(u);
      c <- (u, x +^ v);
    }
    else {
      c <- (text0, text0);
    }  
    return c;
  }
}.

(* game parameterized by implementation of RF, and using EO_RF *)

local module G1 (RF : RF) = {
  module E = EO_RF(RF)
  module A = Adv(E)

  proc main() : bool = {
    var b, b' : bool; var x1, x2 : text; var c : cipher;
    E.init();
    (x1, x2) <@ A.choose();
    b <$ {0,1};
    c <@ E.genc(b ? x1 : x2);
    b' <@ A.guess(c);
    return b = b';
  }
}.    

local lemma EO_EO_RF_PRF_enc_pre :
  equiv[EO.enc_pre ~ EO_RF(PRF).enc_pre :
        ={x} /\ ={key}(EncO, PRF) /\ ={ctr_pre}(EncO, EO_RF) ==>
        ={res} /\ ={ctr_pre}(EncO, EO_RF)].
proof.
proc; inline*; if => //; [wp; rnd; auto | auto].
qed.

local lemma EO_EO_RF_PRF_genc :
  equiv[EO.genc ~ EO_RF(PRF).genc :
        ={x} /\ ={key}(EncO, PRF) ==> ={res}].
proof.
proc; inline*; wp; rnd; auto.
qed.

local lemma EO_EO_RF_PRF_enc_post :
  equiv[EO.enc_post ~ EO_RF(PRF).enc_post :
        ={x} /\ ={key}(EncO, PRF) /\ ={ctr_post}(EncO, EO_RF) ==>
        ={res} /\ ={ctr_post}(EncO, EO_RF)].
proof.
proc; inline*; if => //; [wp; rnd; auto | auto].
qed.

local lemma INDCPA_G1_PRF &m :
  Pr[INDCPA(Enc, Adv).main() @ &m : res] = Pr[G1(PRF).main() @ &m : res].
proof.
byequiv => //; proc.
call (_ : ={key}(EO, PRF) /\ ={ctr_post}(EO, EO_RF)).
by conseq EO_EO_RF_PRF_enc_post.
call EO_EO_RF_PRF_genc.
rnd.
call (_ : ={key}(EO, PRF) /\ ={ctr_pre}(EO, EO_RF)).
by conseq EO_EO_RF_PRF_enc_pre.
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

(* version of encryption oracle using TRF, and where genc
   (Obliviously) updates TRF.mp with randomly chosen u even if
   clash_pre has happened *)

local module EO_O : EO = {
  var ctr_pre : int
  var ctr_post : int
  var clash_pre : bool
  var clash_post : bool
  var genc_inp : text

  proc init() = {
    TRF.init();
    ctr_pre <- 0; ctr_post <- 0; clash_pre <- false;
    clash_post <- false; genc_inp <- text0;
  }

  proc enc_pre(x : text) : cipher = {
    var u, v : text; var c : cipher;
    if (ctr_pre < limit_pre) {
      ctr_pre <- ctr_pre + 1;
      u <$ dtext;
      v <@ TRF.f(u);
      c <- (u, x +^ v);
    }
    else {
      c <- (text0, text0);
    }  
    return c;
  }

  proc genc(x : text) : cipher = {
    var u, v : text; var c : cipher;
    u <$ dtext;
    if (u \in TRF.mp) {
      clash_pre <- true;
    }
    genc_inp <- u;
    v <$ dtext;
    TRF.mp.[u] <- v;  (* note *)
    c <- (u, x +^ v);
    return c;
  }

  proc enc_post(x : text) : cipher = {
    var u, v : text; var c : cipher;
    if (ctr_post < limit_post) {
      ctr_post <- ctr_post + 1;
      u <$ dtext;
      if (u = genc_inp) {
        clash_post <- true;
      }
      v <@ TRF.f(u);
      c <- (u, x +^ v);
    }
    else {
      c <- (text0, text0);
    }  
    return c;
  }
}.

(* game using EO_O *)

local module G2 = {
  module A = Adv(EO_O)

  proc main() : bool = {
    var b, b' : bool; var x1, x2 : text; var c : cipher;
    EO_O.init();
    (x1, x2) <@ A.choose();
    b <$ {0,1};
    c <@ EO_O.genc(b ? x1 : x2);
    b' <@ A.guess(c);
    return b = b';
  }
}.    

(* we use upto bad reasoning to connect G1(TRF) and G2 *)

local lemma EO_O_enc_pre_ll : islossless EO_O.enc_pre.
proof.
proc; islossless; by rewrite dtext_ll.
qed.

local lemma EO_O_enc_post_ll : islossless EO_O.enc_post.
proof.
proc; islossless; by rewrite dtext_ll.
qed.

local lemma EO_RF_TRF_enc_post_ll : islossless EO_RF(TRF).enc_post.
proof.
proc; islossless; by rewrite dtext_ll.
qed.

local lemma EO_RF_TRF_EO_O_enc_pre :
  equiv
  [EO_RF(TRF).enc_pre ~ EO_O.enc_pre :
   ={x, TRF.mp} /\ ={ctr_pre}(EO_RF, EO_O) /\
   EO_RF.inps_pre{1} = fdom TRF.mp{1} ==>
   ={res, TRF.mp} /\ ={ctr_pre}(EO_RF, EO_O) /\
   EO_RF.inps_pre{1} = fdom TRF.mp{1}].
proof.
proc.
if => //.
seq 2 2 :
  (={u, x, TRF.mp} /\ ={ctr_pre}(EO_RF, EO_O) /\
   EO_RF.inps_pre{1} = fdom TRF.mp{1}).
auto.
wp; sp; inline*; wp; sp.
if => //.
auto; progress; by rewrite fdom_set.
auto => /> &2 mem_u_mp.
rewrite fsetP => x.
rewrite in_fsetU in_fset1.
split => [[] // -> | -> //]; by rewrite mem_fdom.
auto.
qed.

local lemma EO_RF_TRF_EO_O_genc :
  equiv
  [EO_RF(TRF).genc ~ EO_O.genc :
   ={x, TRF.mp} /\ ={clash_pre}(EO_RF, EO_O) /\
   EO_RF.inps_pre{1} = fdom TRF.mp{1} /\
   !EO_RF.clash_pre{1} ==>
   ={clash_pre, genc_inp}(EO_RF, EO_O) /\
   (! EO_RF.clash_pre{1} => ={res, TRF.mp})].
proof.
proc.
seq 1 1 :
  (={x, u, TRF.mp} /\ ={clash_pre}(EO_RF, EO_O) /\
   EO_RF.inps_pre{1} = fdom TRF.mp{1} /\ !EO_RF.clash_pre{1}).
auto.
if.
progress; [by rewrite -mem_fdom | by rewrite mem_fdom].
wp; sp; inline*; wp; sp.
rcondf{1} 1.
auto => />; by rewrite mem_fdom.
auto; progress; apply dtext_ll.
wp; sp; inline*; wp; sp.
rcondt{1} 1.
auto => />; by rewrite mem_fdom.
auto; progress; by rewrite get_set_eqE.
qed.

local lemma EO_RF_TRF_EO_O_enc_post :
  equiv
  [EO_RF(TRF).enc_post ~ EO_O.enc_post :
   ={x} /\ ={TRF.mp} /\ ={ctr_post, genc_inp}(EO_RF, EO_O) ==>
   ={res} /\ ={TRF.mp} /\ ={ctr_post}(EO_RF, EO_O)].
proof.
proc.
if => //.
wp.
call (_ : ={TRF.mp}).
sim.
auto.
auto.
qed.

local lemma G1_TRF_G2_main :
  equiv
  [G1(TRF).main ~ G2.main :
   true ==>
   ={clash_pre}(EO_RF, EO_O) /\
   (! EO_RF.clash_pre{1} => ={res})].
proof.
proc.
seq 3 3 :
  (={TRF.mp} /\
   ={x1, x2, b, glob Adv} /\
   ={ctr_pre, ctr_post, clash_pre, clash_post, genc_inp}(EO_RF, EO_O) /\
   EO_RF.inps_pre{1} = fdom TRF.mp{1} /\
   !EO_RF.clash_pre{1}).
rnd.
call
  (_ :
   ={TRF.mp} /\
   ={ctr_pre, clash_pre}(EO_RF, EO_O) /\
   EO_RF.inps_pre{1} = fdom TRF.mp{1}).
by conseq EO_RF_TRF_EO_O_enc_pre.
inline*; auto; progress; by rewrite fdom0.
seq 1 1 :
  (={b} /\
   ={ctr_post, clash_pre, clash_post, genc_inp,
     glob Adv}(EO_RF, EO_O) /\
   (! EO_RF.clash_pre{1} => ={c, TRF.mp})).
call EO_RF_TRF_EO_O_genc.
auto.
call
  (_ :
   ={ctr_post, clash_pre, clash_post, genc_inp}(EO_RF, EO_O) /\
   ={glob Adv} /\
   (! EO_RF.clash_pre{1} => ={c, TRF.mp}) ==>
   (! EO_RF.clash_pre{1} => ={res})).
proc
  (EO_O.clash_pre)  (* bad event in second game *)
  (={TRF.mp} /\  (* when bad event is false *)
   ={ctr_post, genc_inp, clash_pre}(EO_RF, EO_O))
  (EO_RF.clash_pre{1}).  (* when bad event is true *)
by move => />.
move => &1 &2.
by case (EO_O.clash_pre{2}).
apply Adv_guess_ll.
by conseq EO_RF_TRF_EO_O_enc_post.
progress; conseq EO_RF_TRF_enc_post_ll.
progress; conseq EO_O_enc_post_ll.
skip => /> &1 &2 _ result_L result_R not_clash_imp /not_clash_imp //.
qed.

local lemma EO_O_enc_pre_pres_invar :
  phoare
  [EO_O.enc_pre :
   card (fdom TRF.mp) <= EO_O.ctr_pre <= limit_pre  ==>
   card (fdom TRF.mp) <= EO_O.ctr_pre <= limit_pre] =
  (1%r).
proof.
proc.
if.
seq 2 :
  (* intermediate condition (IC) *)
  (card (fdom TRF.mp) < EO_O.ctr_pre <= limit_pre)
  1%r   (* probability of termination of 1st part with IC from
           precondition  *)
  1%r   (* probability of termination of 2nd part with post
           condition from IC *)
  0%r   (* probability of termination of 1st part with !IC from
           precondition *)
  1%r.  (* probability of termination of 2nd part with post
           condition from !IC *)
(* the above can be abbreviated:
seq 2 : (card (fdom TRF.mp) < EO_O.ctr_pre <= limit_pre)
*)
auto.
rnd; auto; progress;
  [by rewrite ltzS |
   by rewrite addzC lez_add1r |
   apply dtext_ll].
inline*; wp; sp; if.
rnd predT. (* rnd without an argument doesn't work! *)
auto => /> &hr lt_card_dom_mp_ctr _ not_mem_u_dom_mp.
split => [| _ y _ _]; first apply dtext_ll.
by rewrite fdom_set fcardUI_indep 1:fsetI1 1:mem_fdom
           1:not_mem_u_dom_mp // fcard1 addzC lez_add1r.
auto; progress; by rewrite ltzW.
hoare; simplify.
rnd; auto => /> &hr le_card_dom_mp_ctr _ _ _ _.
split => [| _]; [by rewrite ltzS | by rewrite addzC lez_add1r].
trivial.
auto.
qed.

local lemma EO_O_genc_clash_up :
  phoare
  [EO_O.genc :
   card (fdom TRF.mp) <= EO_O.ctr_pre <= limit_pre /\ !EO_O.clash_pre ==>
   EO_O.clash_pre] <=
  (limit_pre%r / (2 ^ text_len)%r).
proof.
proc.
seq 2 :
  (EO_O.clash_pre)
  (limit_pre%r / (2 ^ text_len)%r)
  (1%r)
  ((2 ^ text_len - limit_pre)%r / (2 ^ text_len)%r)
  (0%r).
auto.
conseq
  (_ :
   card (fdom TRF.mp) <= limit_pre /\ !EO_O.clash_pre ==>
   _ : <=
  (limit_pre%r / (2 ^ text_len)%r)).
move => /> &hr le_card_dom_mp_ctr le_ctr_limit _.
by apply (lez_trans EO_O.ctr_pre{hr}).
wp; simplify.
conseq (_ : _ ==> u \in fdom TRF.mp).
move => /> &hr le_card_dom_mp_limit _ u0.
by rewrite mem_fdom.
rnd; simplify; skip; progress.
by rewrite mu_dtext_mem ler_wpmul2r 1:invr_ge0
           1:le_fromint 1:ltzW 1:powPos // le_fromint.
auto; progress; by rewrite dtext_ll.
hoare; inline*; auto; progress.
trivial.
qed.

local lemma G2_main_clash_ub &m :
  Pr[G2.main() @ &m : EO_O.clash_pre] <=
  limit_pre%r / (2 ^ text_len)%r.
proof.
byphoare => //.
proc.
seq 3 :
  (card (fdom TRF.mp) <= EO_O.ctr_pre <= limit_pre /\ !EO_O.clash_pre)
  (1%r)
  (limit_pre%r / (2 ^ text_len)%r)
  (0%r)
  (1%r);
last 2 first.
hoare.
inline*; auto.
call (_ : card (fdom TRF.mp) <= EO_O.ctr_pre <= limit_pre).
conseq (_ : _ ==> _ : = (1%r)) => //.
apply EO_O_enc_pre_pres_invar.
auto => />.
rewrite fdom0 fcards0 /= ge0_limit_pre.
trivial.
inline*; auto.
inline*; auto.
seq 1 :
  (EO_O.clash_pre)
  (limit_pre%r / (2 ^ text_len)%r)
  (1%r)
  ((2 ^ text_len - 1)%r / (2 ^ text_len)%r)
  (0%r);
last 2 first.
hoare.
conseq (_ : true ==> true).
call (_ : true).
conseq (_ : _ ==> true : = (1%r)) => //.
apply EO_O_enc_post_ll.
auto.
trivial.
call (_ : true); auto.
call EO_O_genc_clash_up.
auto.
conseq (_ : true ==> true : = (1%r)).
call (_ : true).
apply Adv_guess_ll.
apply EO_O_enc_post_ll.
auto.
qed.

local lemma G1_TRF_G2 &m :
  `|Pr[G1(TRF).main() @ &m : res] - Pr[G2.main() @ &m : res]| <=
  limit_pre%r / (2 ^ text_len)%r.
proof.
rewrite (RealOrder.ler_trans Pr[G2.main() @ &m : EO_O.clash_pre]);
  last 1 apply (G2_main_clash_ub &m).
byequiv
  (_ :
   true ==>
   (={clash_pre}(EO_RF, EO_O)) /\ (! EO_O.clash_pre{2} => ={res})) :
  (EO_RF.clash_pre) => //.
by conseq G1_TRF_G2_main.
move => &1 &2 [#] -> not_class_imp /=.
by rewrite -eq_iff.
qed.

(* now we use triangular inequality

    |x - z| <= |x - y| + |y - z]

   to summarize: *)

local lemma INDCPA_G2 &m :
  `|Pr[INDCPA(Enc, Adv).main() @ &m : res] - Pr[G2.main() @ &m : res]| <=
  `|Pr[GRF(PRF, Adv2RFA(Adv)).main() @ &m : res] -
    Pr[GRF(TRF, Adv2RFA(Adv)).main() @ &m : res]| +
  limit_pre%r / (2 ^ text_len)%r.
proof.
rewrite
  (ler_trans
   (`|Pr[INDCPA(Enc, Adv).main() @ &m : res] - Pr[G1(TRF).main() @ &m : res]| +
    `|Pr[G1(TRF).main() @ &m : res] - Pr[G2.main() @ &m : res]|))
  1:ler_dist_add (INDCPA_G1_TRF &m) ler_add2l (G1_TRF_G2 &m).
qed.

(* version of encryption oracle in which genc doesn't update TRF.mp at
   all (I for Independent of map) *)

local module EO_I : EO = {
  var ctr_pre : int
  var ctr_post : int
  var clash_pre : bool
  var clash_post : bool
  var genc_inp : text

  proc init() = {
    TRF.init();
    ctr_pre <- 0; ctr_post <- 0; clash_pre <- false;
    clash_post <- false; genc_inp <- text0;
  }

  proc enc_pre(x : text) : cipher = {
    var u, v : text; var c : cipher;
    if (ctr_pre < limit_pre) {
      ctr_pre <- ctr_pre + 1;
      u <$ dtext;
      v <@ TRF.f(u);
      c <- (u, x +^ v);
    }
    else {
      c <- (text0, text0);
    }  
    return c;
  }

  proc genc(x : text) : cipher = {
    var u, v : text; var c : cipher;
    u <$ dtext;
    if (u \in TRF.mp) {
      clash_pre <- true;
    }
    genc_inp <- u;
    v <$ dtext;
    (* note: map no longer updated *)
    c <- (u, x +^ v);
    return c;
  }

  proc enc_post(x : text) : cipher = {
    var u, v : text; var c : cipher;
    if (ctr_post < limit_post) {
      ctr_post <- ctr_post + 1;
      u <$ dtext;
      if (u = genc_inp) {
        clash_post <- true;
      }
      v <@ TRF.f(u);
      c <- (u, x +^ v);
    }
    else {
      c <- (text0, text0);
    }  
    return c;
  }
}.

(* game using EO_I *)

local module G3 = {
  module A = Adv(EO_I)

  proc main() : bool = {
    var b, b' : bool; var x1, x2 : text; var c : cipher;
    EO_I.init();
    (x1, x2) <@ A.choose();
    b <$ {0,1};
    c <@ EO_I.genc(b ? x1 : x2);
    b' <@ A.guess(c);
    return b = b';
  }
}.    

(* we use upto bad reasoning to connect G2 and G3 *)

local lemma EO_O_enc_post_pres_clash_post :
  phoare[EO_O.enc_post :
         EO_O.clash_post ==> EO_O.clash_post] = 1%r.
proof.
proc.
if.
seq 2 : (EO_O.clash_post).
auto.
auto; progress; by rewrite dtext_ll.
if.
wp; sp; inline*; sp; wp.
if; [auto; progress; by rewrite dtext_ll | auto].
inline*; wp; sp.
if; [auto; progress; by rewrite dtext_ll | auto].
hoare; auto.
trivial.
auto.
qed.

local lemma EO_I_enc_post_pres_clash_post :
  phoare[EO_I.enc_post :
         EO_I.clash_post ==> EO_I.clash_post] = 1%r.
proof.
proc.
if.
seq 2 : (EO_I.clash_post).
auto.
auto; progress; by rewrite dtext_ll.
if.
wp; sp; inline*; sp; wp.
if; [auto; progress; by rewrite dtext_ll | auto].
inline*; wp; sp.
if; [auto; progress; by rewrite dtext_ll | auto].
hoare; auto.
trivial.
auto.
qed.

(* the following postcondition says that TRF.mp{1} and TRF.mp{2}
   are equal except on EO_I.genc_inp{2} (= EO_O.genc_inp{1}) *)

local lemma EO_O_EO_I_genc :
  equiv[EO_O.genc ~ EO_I.genc :
        ={x, TRF.mp} ==>
        ={res} /\ ={genc_inp}(EO_O, EO_I) /\
        eq_except (pred1 EO_I.genc_inp{2}) TRF.mp{1} TRF.mp{2}].
proof.        
proc.
seq 1 1 : (={u, x, TRF.mp}); first auto.
if => //; auto; progress; rewrite eq_except_setl.
qed.

local lemma EO_O_EO_I_enc_post :
  equiv[EO_O.enc_post ~ EO_I.enc_post :
        ={x} /\
        ={ctr_post, clash_post, genc_inp}(EO_O, EO_I) /\
        !EO_O.clash_post{1} /\
        eq_except (pred1 EO_I.genc_inp{2}) TRF.mp{1} TRF.mp{2} ==>
        ={ctr_post, clash_post, genc_inp}(EO_O, EO_I) /\
        eq_except (pred1 EO_I.genc_inp{2}) TRF.mp{1} TRF.mp{2} /\
        (!EO_O.clash_post{1} => ={res})].
proof.
proc.
if => //.
seq 2 2 :
  (={x, u} /\ !EO_O.clash_post{1} /\
   ={ctr_post, clash_post, genc_inp}(EO_O, EO_I) /\
   EO_O.ctr_post{1} <= limit_post /\
   eq_except (pred1 EO_I.genc_inp{2}) TRF.mp{1} TRF.mp{2}).
auto; progress; by rewrite -ltzE.
if => //.
wp; sp.
inline*; wp; sp.
if{1}; auto.
if{2}; auto.
move => /> &1 &2 ? _ _ eq_exc _ _ mp _ mp0 _.
by rewrite eq_except_pred_set.
move => /> &1 &2 ? _ _ eq_exc _ _ mp _.
by rewrite eq_except_pred_set_l.
if{2}; auto.
move => /> &1 &2 ? _ _ eq_exc _ _.
move => mp _.
by rewrite eq_except_pred_set_r.
inline*; wp; sp.
if => //.
move => /> &1 &2 _ _ eq_exc ne_u_genc_inp.
split => [u_in_dom_mp1 | u_in_dom_mp2].
by apply (eq_except_notp_in (pred1 EO_I.genc_inp{2}) u{2} TRF.mp{1} TRF.mp{2}).
rewrite (eq_except_notp_in (pred1 EO_I.genc_inp{2}) u{2} TRF.mp{2} TRF.mp{1})
        1:eq_except_sym //.
auto => /> &1 &2 _ _ eq_exc ne_u_genc_inp not_mem_u_dom_mp1 z _.
split; first by rewrite eq_except_set_eq.
congr; by rewrite 2!get_set_sameE.
auto => /> &1 &2 _ _ eq_exc ne_u_genc_inp _.
congr.
by rewrite (eq_except_not_pred_get (pred1 EO_I.genc_inp{2})
            _ TRF.mp{1} TRF.mp{2}).
auto.
qed.

local lemma G2_G3_main :
  equiv
  [G2.main ~ G3.main :
   true ==>
   ={clash_post}(EO_O, EO_I) /\ (! EO_O.clash_post{1} => ={res})].
proof.
proc.
seq 4 4 :
  (={c, b, x1, x2, glob Adv} /\
   ={ctr_post, clash_post, genc_inp}(EO_O, EO_I) /\
   !EO_O.clash_post{1} /\
   eq_except (pred1 EO_I.genc_inp{2}) TRF.mp{1} TRF.mp{2}).
call EO_O_EO_I_genc.
rnd.
call (_ : (={TRF.mp} /\ ={ctr_pre}(EO_O, EO_I))).
sim.
inline*; auto.
call
  (_ :
   ={c, glob Adv} /\
   ={ctr_post, clash_post, genc_inp}(EO_O, EO_I) /\
   !EO_O.clash_post{1} /\
   eq_except (pred1 EO_I.genc_inp{2}) TRF.mp{1} TRF.mp{2} ==>
   ={clash_post}(EO_O, EO_I) /\
   (!EO_O.clash_post{1} => ={res})).
proc
  (EO_I.clash_post)
  (={ctr_post, clash_post, genc_inp}(EO_O, EO_I) /\
   eq_except (pred1 EO_I.genc_inp{2}) TRF.mp{1} TRF.mp{2})
  (EO_O.clash_post{1}) => //.
move => &1 &2.
case (EO_I.clash_post{2}) => [_ -> // | //].
apply Adv_guess_ll.
conseq EO_O_EO_I_enc_post => //.
by move => />.
progress; apply EO_O_enc_post_pres_clash_post.
progress; conseq (EO_I_enc_post_pres_clash_post) => //.
auto => /> &1 &2.
move => _ _ res_L res_R clash_R not_clash_R_imp
        /not_clash_R_imp -> //.
qed.

(* use failure event lemma tactic (fel) to upper bound probability
   that G2.main results in failure event being set

   fel is applicable because, after initialization of the counter
   (EO_I.ctr_post), failure event (EO_I.clash_post) and invariant
   (EO_I.ctr_post < limit_post) by line 1 of G3.main, it's only
   EO_I.clash_post that's capable of setting the failure event *)

local lemma G3_main_clash_ub &m :
  Pr[G3.main() @ &m : EO_I.clash_post] <= limit_post%r / (2 ^ text_len)%r.
proof.
fel
  (* number of lines of G3.main needed to initialize counter, failure
     event and invariant *)
  1
  EO_I.ctr_post  (* counter *)
  (* upper bound in terms of current counter of probability that failure
     event is set during one run of oracle *)
  (fun n, 1%r / (2 ^ text_len)%r)
  limit_post  (* counter limit *)
  EO_I.clash_post  (* failure event *)
  (* precondition on enc_post: if it holds, then counter goes up and
     failure might happen; if it doesn't hold, then counter doesn't go
     down, and failure status preserved *)
  [EO_I.enc_post : (EO_I.ctr_post < limit_post)]
  (* invariant *)
  (EO_I.ctr_post <= limit_post) => //.
(* 1 *)
by rewrite sumr_const intmulr /= count_predT size_range
           max_ler /= 1:ge0_limit_post.
(* 2 *)
inline*; auto; progress; rewrite ge0_limit_post.
(* 3 *)
proc; rcondt 1; first auto.
wp; sp.
seq 2 :
  (EO_I.clash_post)
  (1%r / (2 ^ text_len)%r)
  (1%r)
  ((2 ^ text_len - 1)%r / (2 ^ text_len)%r)
  (0%r).
auto.
wp.
rnd (pred1 EO_I.genc_inp).
auto => /> &hr _.
by rewrite mu1_dtext.
auto.
hoare; inline*; wp; sp; if; auto.
trivial.
(* 4 *)
progress; proc.
rcondt 1; first auto.
seq 2 : (c < EO_I.ctr_post <= limit_post).
auto => /> &hr lt_lim le_lim x _.
split => [| _].
rewrite ltzS lezz.
rewrite addzC lez_add1r lt_lim.
if; inline*; wp; sp; if; auto.
(* 5 *)
progress; proc.
rcondf 1; first auto.
auto.
qed.

local lemma G2_G3 &m :
  `|Pr[G2.main() @ &m : res] - Pr[G3.main() @ &m : res]| <=
  limit_post%r / (2 ^ text_len)%r.
proof.
rewrite (RealOrder.ler_trans Pr[G3.main() @ &m : EO_I.clash_post]);
  last 1 apply (G3_main_clash_ub &m).
byequiv
  (_ :
   true ==>
   (={clash_post}(EO_O, EO_I)) /\ (! EO_I.clash_post{2} => ={res})) :
  (EO_O.clash_post) => //.
by conseq G2_G3_main.
move => &1 &2 [#] -> not_class_imp /=.
by rewrite -eq_iff.
qed.

(* now we use triangular inequality to summarize: *)

local lemma INDCPA_G3 &m :
  `|Pr[INDCPA(Enc, Adv).main() @ &m : res] - Pr[G3.main() @ &m : res]| <=
  `|Pr[GRF(PRF, Adv2RFA(Adv)).main() @ &m : res] -
    Pr[GRF(TRF, Adv2RFA(Adv)).main() @ &m : res]| +
  (limit_pre%r + limit_post%r) / (2 ^ text_len)%r.
proof.
rewrite
  (ler_trans
   (`|Pr[INDCPA(Enc, Adv).main() @ &m : res] - Pr[G2.main() @ &m : res]| +
    `|Pr[G2.main() @ &m : res] - Pr[G3.main() @ &m : res]|))
  1:ler_dist_add mulrDl addrA ler_add 1:(INDCPA_G2 &m) (G2_G3 &m).
qed.

(* version of encryption oracle in which right side of ciphertext
   produced by genc doesn't reference plaintext at all (N stands for
   No reference to plaintext); we no longer need any
   instrumentation *)

local module EO_N : EO = {
  var ctr_pre : int
  var ctr_post : int

  proc init() = {
    TRF.init();
    ctr_pre <- 0; ctr_post <- 0;
  }

  proc enc_pre(x : text) : cipher = {
    var u, v : text; var c : cipher;
    if (ctr_pre < limit_pre) {
      ctr_pre <- ctr_pre + 1;
      u <$ dtext;
      v <@ TRF.f(u);
      c <- (u, x +^ v);
    }
    else {
      c <- (text0, text0);
    }  
    return c;
  }

  proc genc(x : text) : cipher = {
    var u, v : text; var c : cipher;
    u <$ dtext;
    v <$ dtext;
    c <- (u, v);  (* note: no exclusive or *)
    return c;
  }

  proc enc_post(x : text) : cipher = {
    var u, v : text; var c : cipher;
    if (ctr_post < limit_post) {
      ctr_post <- ctr_post + 1;
      u <$ dtext;
      v <@ TRF.f(u);
      c <- (u, x +^ v);
    }
    else {
      c <- (text0, text0);
    }  
    return c;
  }
}.

(* game using EO_N, and where argument to EO_N.genc is independent
   from x1/x2/b *)

local module G4 = {
  module A = Adv(EO_N)

  proc main() : bool = {
    var b, b' : bool; var x1, x2 : text; var c : cipher;
    EO_N.init();
    (x1, x2) <@ A.choose();
    b <$ {0,1};
    c <@ EO_N.genc(text0);
    b' <@ A.guess(c);
    return b = b';
  }
}.    

local lemma EO_N_enc_pre_ll : islossless EO_N.enc_pre.
proof.
proc; islossless; by rewrite dtext_ll.
qed.

local lemma EO_N_enc_post_ll : islossless EO_N.enc_post.
proof.
proc; islossless; by rewrite dtext_ll.
qed.

local lemma EO_N_genc_ll : islossless EO_N.genc.
proof.
proc; islossless; by rewrite dtext_ll.
qed.

(* note no assumption about genc's argument, x *)

local lemma EO_I_EO_N_genc :
  equiv[EO_I.genc ~ EO_N.genc : true ==> ={res}].
proof.
proc.
wp.
rnd (fun z => x{1} +^ z).
auto; progress.
by rewrite text_xorA text_xorK text_xor_lid.
qed.

local lemma G3_G4 &m :
  Pr[G3.main() @ &m : res] = Pr[G4.main() @ &m : res].
proof.
byequiv => //.
proc.
call (_ : ={TRF.mp} /\ ={ctr_post}(EO_I, EO_N)).
sim.
call EO_I_EO_N_genc.
rnd.
call (_ : ={TRF.mp} /\ ={ctr_pre}(EO_I, EO_N)).
sim.
inline*; auto.
qed.

local lemma INDCPA_G4 &m :
  `|Pr[INDCPA(Enc, Adv).main() @ &m : res] - Pr[G4.main() @ &m : res]| <=
  `|Pr[GRF(PRF, Adv2RFA(Adv)).main() @ &m : res] -
    Pr[GRF(TRF, Adv2RFA(Adv)).main() @ &m : res]| +
  (limit_pre%r + limit_post%r) / (2 ^ text_len)%r.
proof.
rewrite -(G3_G4 &m) (INDCPA_G3 &m).
qed.

(* probability that G4.main returns true *)

local lemma G4_prob &m :
  Pr[G4.main() @ &m : res] = 1%r / 2%r.
proof.
byphoare => //; proc.
swap 3 2; rnd.
call (_ : true);
  [apply Adv_guess_ll | apply EO_N_enc_post_ll | idtac].
call EO_N_genc_ll.
call (_ : true);
  [apply Adv_choose_ll | apply EO_N_enc_pre_ll | idtac].
inline*; auto => /= x; by rewrite dbool1E.
qed.

lemma INDCPA' &m :
  `|Pr[INDCPA(Enc, Adv).main() @ &m : res] - 1%r / 2%r| <=
  `|Pr[GRF(PRF, Adv2RFA(Adv)).main() @ &m : res] -
    Pr[GRF(TRF, Adv2RFA(Adv)).main() @ &m : res]| +
  (limit_pre%r + limit_post%r) / (2 ^ text_len)%r.
proof. rewrite -(G4_prob &m) (INDCPA_G4 &m). qed.

end section.

(* IND-CPA security theorem

   we need to assume Adv is lossless and that it doesn't interact with
   EncO (which INDCPA uses) or PRF/TRF/Adv2RFA (which appear in the
   upper bound)

   because Enc is stateless, Adv may use it (and in any event could
   simulate it) *)

lemma INDCPA (Adv <: ADV{EncO, PRF, TRF, Adv2RFA}) &m :
  (forall (EO <: EO{Adv}),
   islossless EO.enc_pre => islossless Adv(EO).choose) =>
  (forall (EO <: EO{Adv}),
   islossless EO.enc_post => islossless Adv(EO).guess) =>
  `|Pr[INDCPA(Enc, Adv).main() @ &m : res] - 1%r / 2%r| <=
  `|Pr[GRF(PRF, Adv2RFA(Adv)).main() @ &m : res] -
    Pr[GRF(TRF, Adv2RFA(Adv)).main() @ &m : res]| +
  (limit_pre%r + limit_post%r) / (2 ^ text_len)%r.
proof.
move => Adv_choose_ll Adv_guess_ll.
apply (INDCPA' Adv Adv_choose_ll Adv_guess_ll &m).
qed.
