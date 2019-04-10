(* SmtMapAux.ec *)

require import AllCore SmtMap.

lemma eq_except_pred_set
      (X : 'a -> bool) (x : 'a) (y y' : 'b) (m1 m2 : ('a, 'b) fmap) :
  eq_except X m1 m2 => X x => eq_except X m1.[x <- y] m2.[x <- y'].
proof.
move => /eq_exceptP eq_exc X_x.
rewrite eq_exceptP => z not_X_z.
case (z = x) => [->> // |] ne_z_x.
do 2! rewrite get_set_neqE //.
by rewrite eq_exc.
qed.

lemma eq_except_pred_set_l
      (X : 'a -> bool) (x : 'a) (y : 'b) (m1 m2 : ('a, 'b) fmap) :
  eq_except X m1 m2 => X x => eq_except X m1.[x <- y] m2.
proof.
move => /eq_exceptP eq_exc X_x.
rewrite eq_exceptP => z not_X_z.
case (z = x) => [->> // |] ne_z_x.
rewrite get_set_neqE //.
by rewrite eq_exc.
qed.

lemma eq_except_pred_set_r
      (X : 'a -> bool) (x : 'a) (y : 'b) (m1 m2 : ('a, 'b) fmap) :
  eq_except X m1 m2 => X x => eq_except X m1 m2.[x <- y].
proof.
move => eq_exc X_x.
by rewrite eq_except_sym eq_except_pred_set_l 1:eq_except_sym.
qed.

lemma eq_except_not_pred_get
      (X : 'a -> bool) (x : 'a) (m1 m2 : ('a, 'b) fmap) :
  eq_except X m1 m2 => ! X x => m1.[x] = m2.[x].
proof.
move => /eq_exceptP eq_exc not_X_x.
by rewrite eq_exc.
qed.
