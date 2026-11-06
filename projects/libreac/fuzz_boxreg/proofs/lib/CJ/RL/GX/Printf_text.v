(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/cjson/cjson_read_fuzzer/lib/P/F_vsnprintf.v, with its module paths and module names changed; 710 of its 816 lines of code are new or changed and 1295 lines of the source are left out. *)
From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.CJ.Lib Require Import ITree.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.CJ.Spec Require Import Prelim Monad FmtFp.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.CJ.RL.GX Require Import Printf_model.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.CJ.RL.GX Require G_printf_core_common.
Import G_printf_core_common.G_printf_iface.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope mspec_scope.

Inductive pf_piece : Type := PLit (b : Z) | Pd | Pc | Px04 | Px02 | Pllu | Ps | Pps.
Inductive pf_arg : Type := AInt (v : Z) | AU64 (u : Z) | APtr (s : list Z).

Fixpoint pf_parse (f : list Z) : option (list pf_piece) :=
  match f with
  | [] => Some []
  | b :: r =>
    if b =? 37 then
      match r with
      | c :: r1 =>
        if c =? 100 then option_map (cons Pd) (pf_parse r1)
        else if c =? 99 then option_map (cons Pc) (pf_parse r1)
        else if c =? 115 then option_map (cons Ps) (pf_parse r1)
        else if c =? 48 then
          match r1 with
          | c2 :: c3 :: r3 =>
              if (c2 =? 52) && (c3 =? 120) then option_map (cons Px04) (pf_parse r3)
              else if (c2 =? 50) && (c3 =? 120) then option_map (cons Px02) (pf_parse r3)
              else None
          | _ => None
          end
        else if c =? 108 then
          match r1 with
          | c2 :: c3 :: r3 => if (c2 =? 108) && (c3 =? 117) then option_map (cons Pllu) (pf_parse r3) else None
          | _ => None
          end
        else if c =? 46 then
          match r1 with
          | c2 :: c3 :: r3 => if (c2 =? 42) && (c3 =? 115) then option_map (cons Pps) (pf_parse r3) else None
          | _ => None
          end
        else None
      | [] => None
      end
    else if (0 <? b) && (b <? 256) then option_map (cons (PLit b)) (pf_parse r)
    else None
  end.

Fixpoint pf_digits (fuel : nat) (x : Z) (acc : list Z) : list Z :=
  match fuel with
  | O => acc
  | S f => if x <? 10 then (48 + x) :: acc else pf_digits f (x / 10) ((48 + x mod 10) :: acc)
  end.

Definition pf_dec (v : Z) : list Z := if v <? 0 then 45 :: pf_digits 11 (- v) [] else pf_digits 11 v [].

Definition pf_hexd (d : Z) : Z := if d <? 10 then 48 + d else 87 + d.

Fixpoint pf_hexs (fuel : nat) (x : Z) (acc : list Z) : list Z :=
  match fuel with
  | O => acc
  | S f => if x <? 16 then pf_hexd x :: acc else pf_hexs f (x / 16) (pf_hexd (x mod 16) :: acc)
  end.

Definition pf_hex4 (v : Z) : list Z :=
  let h := pf_hexs 8 (v mod 2^32) [] in repeat 48 (4 - length h) ++ h.

Definition pf_hex2 (v : Z) : list Z :=
  let h := pf_hexs 8 (v mod 2^32) [] in repeat 48 (2 - length h) ++ h.

Definition pf_udec (u : Z) : list Z := pf_digits 20 u [].

Fixpoint pf_text (ps : list pf_piece) (args : list pf_arg) : option (list Z) :=
  match ps with
  | [] => match args with [] => Some [] | _ :: _ => None end
  | PLit b :: ps' => option_map (cons b) (pf_text ps' args)
  | Pd :: ps' => match args with AInt v :: a' => option_map (app (pf_dec v)) (pf_text ps' a') | _ => None end
  | Pc :: ps' => match args with AInt v :: a' => option_map (cons (v mod 256)) (pf_text ps' a') | _ => None end
  | Px04 :: ps' => match args with AInt v :: a' => option_map (app (pf_hex4 v)) (pf_text ps' a') | _ => None end
  | Px02 :: ps' => match args with AInt v :: a' => option_map (app (pf_hex2 v)) (pf_text ps' a') | _ => None end
  | Pllu :: ps' => match args with AU64 u :: a' => option_map (app (pf_udec u)) (pf_text ps' a') | _ => None end
  | Ps :: ps' => match args with APtr s :: a' => option_map (app s) (pf_text ps' a') | _ => None end
  | Pps :: ps' =>
      match args with
      | AInt k :: APtr s :: a' =>
          if (0 <=? k) && (k <=? Z.of_nat (length s)) then option_map (app (firstn (Z.to_nat k) s)) (pf_text ps' a')
          else None
      | _ => None
      end
  end.

Fixpoint pf_pargs (ps : list pf_piece) (args : list pf_arg) : list parg :=
  match ps with
  | [] => []
  | PLit _ :: ps' => pf_pargs ps' args
  | Pd :: ps' => match args with AInt v :: a' => PA_i v :: pf_pargs ps' a' | _ => [] end
  | Pc :: ps' => match args with AInt v :: a' => PA_i v :: pf_pargs ps' a' | _ => [] end
  | Px04 :: ps' => match args with AInt v :: a' => PA_u (v mod 2^32) :: pf_pargs ps' a' | _ => [] end
  | Px02 :: ps' => match args with AInt v :: a' => PA_u (v mod 2^32) :: pf_pargs ps' a' | _ => [] end
  | Pllu :: ps' => match args with AU64 u :: a' => PA_ull u :: pf_pargs ps' a' | _ => [] end
  | Ps :: ps' => match args with APtr s :: a' => PA_s s :: pf_pargs ps' a' | _ => [] end
  | Pps :: ps' => match args with AInt k :: APtr s :: a' => PA_i k :: PA_s s :: pf_pargs ps' a' | _ => [] end
  end.

Definition pt_fit (a : pf_arg) : Prop := match a with AInt v => -2^31 <= v < 2^31 | AU64 u => 0 <= u | _ => True end.

Definition pt_nog (a : parg) : Prop := match a with PA_g _ => False | _ => True end.

Definition pt_hexw (w : nat) (v : Z) : list Z :=
  let h := pf_hexs 8 (v mod 2^32) [] in repeat 48 (w - length h) ++ h.

Lemma pt_zlength_app : forall {A} (a b : list A), zlength (a ++ b) = zlength a + zlength b.
Proof. intros. unfold zlength. rewrite length_app. lia. Qed.
Lemma pt_zlength_nil : zlength (@nil Z) = 0.
Proof. reflexivity. Qed.
Lemma pt_zlength_concat_cons : forall {A} (p : list A) ps, zlength (concat (p :: ps)) = zlength p + zlength (concat ps).
Proof. intros. cbn [concat]. apply pt_zlength_app. Qed.
Lemma pt_zlength_concat_app : forall {A} (ps qs : list (list A)), zlength (concat (ps ++ qs)) = zlength (concat ps) + zlength (concat qs).
Proof. intros. rewrite concat_app. apply pt_zlength_app. Qed.
Lemma pt_zlength_nonneg : forall {A} (l : list A), 0 <= zlength l.
Proof. intros. unfold zlength. lia. Qed.

Ltac zl := unfold zlength in *; cbn [length] in *; lia.

Lemma pt_mbind_eq : forall {St A B} (m : M St A) (f : A -> M St B) s a s',
  m s = ITree.Ret (Ok (a, s')) -> mbind m f s = f a s'.
Proof. intros St A B m f s a s' H. unfold mbind, ebind. rewrite H. reflexivity. Qed.

Lemma pt_mbind_mbind_eq : forall {St A B C} (m : M St A) (f : A -> M St B) (g : B -> M St C) s a s',
  m s = ITree.Ret (Ok (a, s')) -> mbind (mbind m f) g s = mbind (f a) g s'.
Proof. intros St A B C m f g s a s' H. unfold mbind, ebind. rewrite H. reflexivity. Qed.

Ltac pt_m E := first [ rewrite (pt_mbind_mbind_eq _ _ _ _ _ _ E) | rewrite (pt_mbind_eq _ _ _ _ _ E) ]; cbv beta.

Lemma pt_out_eq : forall OM bs o, zlength o + zlength bs <= OM -> OUT_snf OM bs o = ITree.Ret (Ok (tt, o ++ bs)).
Proof.
  intros OM bs o H. unfold OUT_snf. rewrite (pt_mbind_eq mget _ o o o) by reflexivity.
  replace (zlength o + zlength bs <=? OM) with true by (symmetry; apply Z.leb_le; exact H). reflexivity.
Qed.

Lemma pt_mpad_eq : forall OM c w l fl o ps,
  pad_pieces c w l fl = Some ps -> zlength o + zlength (concat ps) <= OM ->
  mpad (OUT_snf OM) c w l fl o = ITree.Ret (Ok (tt, o ++ concat ps)).
Proof.
  intros OM c w l fl o ps P H. unfold mpad, pad_pieces in *.
  destruct (negb (Z.land fl (Z.lor LEFT_ADJ ZERO_PAD) =? 0) || (w <=? l))%bool.
  - inversion P; subst. cbn [concat]. rewrite app_nil_r. reflexivity.
  - destruct (256 <=? w - l); [discriminate|]. inversion P; subst. cbn [concat] in *. rewrite app_nil_r in *.
    apply pt_out_eq. exact H.
Qed.

Lemma pt_conv_tail : forall OM cnt fl w p prefix body (k : Z -> M (list Z) Z) o ps r,
  tail_pieces cnt fl w p prefix body = Some (ps, r) -> zlength o + zlength (concat ps) <= OM ->
  mbind (conv_tail (OUT_snf OM) cnt fl w p prefix body) k o = k r (o ++ concat ps).
Proof.
  intros OM cnt fl w p prefix body k o ps r T H. unfold conv_tail, tail_pieces in *. cbv zeta in T. cbv zeta.
  destruct (INT_MAX - zlength prefix <? Z.max p (zlength body)); [discriminate|].
  destruct (INT_MAX - cnt <? Z.max w (zlength prefix + Z.max p (zlength body))); [discriminate|].
  destruct (pad_pieces 32 _ _ fl) as [p1|] eqn:P1; [|discriminate].
  destruct (pad_pieces 48 _ _ (Z.lxor fl ZERO_PAD)) as [p2|] eqn:P2; [|discriminate].
  destruct (pad_pieces 48 _ _ 0) as [p3|] eqn:P3; [|discriminate].
  destruct (pad_pieces 32 _ _ (Z.lxor fl LEFT_ADJ)) as [p4|] eqn:P4; [|discriminate].
  inversion T; subst. clear T.
  repeat first [rewrite pt_zlength_concat_app in H | rewrite pt_zlength_concat_cons in H]. rewrite ?pt_zlength_nil in H. cbn [concat] in H. rewrite ?app_nil_r, ?pt_zlength_nil in H.
  pose proof (pt_zlength_nonneg (concat p1)). pose proof (pt_zlength_nonneg (concat p2)). pose proof (pt_zlength_nonneg (concat p3)).
  pose proof (pt_zlength_nonneg (concat p4)). pose proof (pt_zlength_nonneg prefix). pose proof (pt_zlength_nonneg body). pose proof (pt_zlength_nonneg o).
  pose proof (pt_mpad_eq OM _ _ _ _ o _ P1 ltac:(lia)) as E1. pt_m E1.
  pose proof (pt_out_eq OM prefix (o ++ concat p1) ltac:(rewrite pt_zlength_app; lia)) as E2. pt_m E2.
  pose proof (pt_mpad_eq OM _ _ _ _ ((o ++ concat p1) ++ prefix) _ P2 ltac:(rewrite !pt_zlength_app; lia)) as E3. pt_m E3.
  pose proof (pt_mpad_eq OM _ _ _ _ (((o ++ concat p1) ++ prefix) ++ concat p2) _ P3 ltac:(rewrite !pt_zlength_app; lia)) as E4. pt_m E4.
  pose proof (pt_out_eq OM body ((((o ++ concat p1) ++ prefix) ++ concat p2) ++ concat p3) ltac:(rewrite !pt_zlength_app; lia)) as E5. pt_m E5.
  pose proof (pt_mpad_eq OM _ _ _ _ (((((o ++ concat p1) ++ prefix) ++ concat p2) ++ concat p3) ++ body) _ P4 ltac:(rewrite !pt_zlength_app; lia)) as E6. pt_m E6.
  rewrite mbind_mret. rewrite ?concat_app. cbn [concat]. rewrite ?concat_app. cbn [concat]. rewrite ?app_nil_r, <- ?app_assoc. reflexivity.
Qed.

Lemma pt_conv_int : forall OM cnt fl w p xp argi prefix body (k : Z -> M (list Z) Z) o ps r,
  int_pieces cnt fl w p xp argi prefix body = Some (ps, r) -> zlength o + zlength (concat ps) <= OM ->
  mbind (conv_int (OUT_snf OM) cnt fl w p xp argi prefix body) k o = k r (o ++ concat ps).
Proof.
  intros OM cnt fl w p xp argi prefix body k o ps r T H. unfold conv_int, int_pieces in *.
  destruct (xp && (p <? 0))%bool; [discriminate|]. cbv zeta in T. cbv zeta.
  destruct ((argi =? 0) && (p =? 0))%bool; eapply pt_conv_tail; eassumption.
Qed.

Lemma pt_conv : forall OM cnt d a (k : Z -> M (list Z) Z) o ps r,
  conv_pieces cnt d a = Some (ps, r) -> zlength o + zlength (concat ps) <= OM ->
  mbind (conv (OUT_snf OM) OUTFP_snf cnt d a) k o = k r (o ++ concat ps).
Proof.
  intros OM cnt d a k o ps r T H. unfold conv, conv_pieces in *. cbv zeta in T. cbv zeta.
  destruct a as [s|i|u|dd|l].
  - destruct (negb (d_ty d =? T_PTR)); [discriminate|].
    destruct ((d_p d <? 0) && (INT_MAX <=? zlength s))%bool; [discriminate|].
    eapply pt_conv_tail; eassumption.
  - destruct (negb (d_ty d =? T_INT)); [discriminate|].
    destruct (d_t d =? 99); [eapply pt_conv_tail; eassumption|].
    destruct (INTMAX_MAX <? i mod 2 ^ 64);
      [|destruct (negb (Z.land _ MARK_POS =? 0)); [|destruct (negb (Z.land _ PAD_POS =? 0))]];
      eapply pt_conv_int; eassumption.
  - destruct (negb (d_ty d =? T_UINT)); [discriminate|].
    destruct (d_t d =? 117); eapply pt_conv_int; eassumption.
  - discriminate.
  - destruct (negb ((d_ty d =? T_ULLONG) || (d_ty d =? T_SIZET))); [discriminate|].
    destruct (d_t d =? 117); [eapply pt_conv_int; eassumption | discriminate].
Qed.

Lemma pt_loop : forall OM fuel s args cnt o ps r,
  printf_pieces_loop fuel s args cnt = Some (ps, r) -> zlength o + zlength (concat ps) <= OM ->
  printf_loop (OUT_snf OM) OUTFP_snf fuel s args cnt o = ITree.Ret (Ok (r, o ++ concat ps)).
Proof.
  intros OM. induction fuel as [|fuel IH]; intros s args cnt o ps r P H; [discriminate|].
  cbn [printf_pieces_loop] in P. cbn [printf_loop].
  destruct s as [|c s1]; [discriminate|].
  destruct (c =? 0). { inversion P; subst. cbn [concat]. rewrite app_nil_r. reflexivity. }
  cbv zeta in P. cbv zeta. remember (lit_run (c :: s1)) as lit eqn:Hlit. clear Hlit.
  destruct (skipn (Datatypes.length lit) (c :: s1)) as [|c1 s2]; [discriminate|].
  destruct ((c1 =? 37) && match s2 with [] => true | c2 :: _ => c2 =? 37 end)%bool; [discriminate|].
  pose proof (pt_zlength_nonneg o) as Ho.
  destruct (0 <? zlength lit).
  - destruct (INT_MAX - cnt <? zlength lit); [discriminate|].
    destruct (printf_pieces_loop fuel (c1 :: s2) args (cnt + zlength lit)) as [[ps' r']|] eqn:R; [|discriminate].
    inversion P; subst. clear P. rewrite pt_zlength_concat_cons in H. pose proof (pt_zlength_nonneg (concat ps')).
    pose proof (pt_out_eq OM lit o ltac:(lia)) as E1. pt_m E1.
    rewrite (IH _ _ _ _ _ _ R) by (rewrite pt_zlength_app; lia). cbn [concat]. rewrite <- ?app_assoc. rewrite ?app_nil_l, ?app_nil_r. reflexivity.
  - destruct (parse_dir s2) as [[d s3]|].
    + destruct args as [|a args']; [discriminate|].
      destruct (conv_pieces cnt d a) as [[ps1 cnt']|] eqn:C; [|discriminate].
      destruct (printf_pieces_loop fuel s3 args' cnt') as [[ps2 r2]|] eqn:R; [|discriminate].
      inversion P; subst. clear P. rewrite pt_zlength_concat_cons, pt_zlength_concat_app, pt_zlength_nil in H.
      pose proof (pt_zlength_nonneg (concat ps1)). pose proof (pt_zlength_nonneg (concat ps2)).
      pose proof (pt_out_eq OM [] o ltac:(rewrite pt_zlength_nil; lia)) as E1. pt_m E1. rewrite app_nil_r.
      rewrite (pt_conv _ _ _ _ _ _ _ _ C) by lia.
      rewrite (IH _ _ _ _ _ _ R) by (rewrite ?pt_zlength_app; lia). cbn [concat]. rewrite ?concat_app. rewrite <- ?app_assoc. rewrite ?app_nil_l, ?app_nil_r. reflexivity.
    + destruct args as [|[ss|k|u|dd|ll] args']; try discriminate.
      destruct args' as [|a args']; [discriminate|].
      destruct (parse_star s2) as [[d s3]|]; [|discriminate].
      destruct (conv_pieces cnt (set_prec d k) a) as [[ps1 cnt']|] eqn:C; [|discriminate].
      destruct (printf_pieces_loop fuel s3 args' cnt') as [[ps2 r2]|] eqn:R; [|discriminate].
      inversion P; subst. clear P. rewrite pt_zlength_concat_cons, pt_zlength_concat_app, pt_zlength_nil in H.
      pose proof (pt_zlength_nonneg (concat ps1)). pose proof (pt_zlength_nonneg (concat ps2)).
      pose proof (pt_out_eq OM [] o ltac:(rewrite pt_zlength_nil; lia)) as E1. pt_m E1. rewrite app_nil_r.
      rewrite (pt_conv _ _ _ _ _ _ _ _ C) by lia.
      rewrite (IH _ _ _ _ _ _ R) by (rewrite ?pt_zlength_app; lia). cbn [concat]. rewrite ?concat_app. rewrite <- ?app_assoc. rewrite ?app_nil_l, ?app_nil_r. reflexivity.
Qed.

Theorem printf_model_snf_pieces : forall OM fmt args ps r,
  printf_pieces fmt args = Some (ps, r) -> zlength (concat ps) <= OM ->
  printf_model (OUT_snf OM) OUTFP_snf fmt args [] = ITree.Ret (Ok (r, concat ps)).
Proof.
  intros OM fmt args ps r P H. unfold printf_model, printf_pieces in *.
  exact (pt_loop OM _ _ _ _ [] _ _ P ltac:(rewrite pt_zlength_nil; lia)).
Qed.

Lemma pt_omap_some : forall {A B} (f : A -> B) x y, option_map f x = Some y -> exists x', x = Some x' /\ y = f x'.
Proof. intros A B f [x'|] y H; cbn in H; [injection H as <-; exists x'; split; reflexivity | discriminate H]. Qed.

Lemma pt_parse_pct : forall r ps, pf_parse (37 :: r) = Some ps ->
  (exists r1 ps', r = 100 :: r1 /\ pf_parse r1 = Some ps' /\ ps = Pd :: ps')
  \/ (exists r1 ps', r = 99 :: r1 /\ pf_parse r1 = Some ps' /\ ps = Pc :: ps')
  \/ (exists r1 ps', r = 115 :: r1 /\ pf_parse r1 = Some ps' /\ ps = Ps :: ps')
  \/ (exists r1 ps', r = 48 :: 52 :: 120 :: r1 /\ pf_parse r1 = Some ps' /\ ps = Px04 :: ps')
  \/ (exists r1 ps', r = 48 :: 50 :: 120 :: r1 /\ pf_parse r1 = Some ps' /\ ps = Px02 :: ps')
  \/ (exists r1 ps', r = 108 :: 108 :: 117 :: r1 /\ pf_parse r1 = Some ps' /\ ps = Pllu :: ps')
  \/ (exists r1 ps', r = 46 :: 42 :: 115 :: r1 /\ pf_parse r1 = Some ps' /\ ps = Pps :: ps').
Proof.
  intros r ps H. destruct r as [|c r1]; [discriminate H|].
  cbn [pf_parse] in H. rewrite Z.eqb_refl in H.
  destruct (c =? 100) eqn:N1.
  { apply Z.eqb_eq in N1. subst c. cbv beta iota in H. apply pt_omap_some in H as (ps' & H & ->).
    left. exists r1, ps'. split; [reflexivity|split; [exact H|reflexivity]]. }
  destruct (c =? 99) eqn:N2.
  { apply Z.eqb_eq in N2. subst c. cbv beta iota in H. apply pt_omap_some in H as (ps' & H & ->).
    right; left. exists r1, ps'. split; [reflexivity|split; [exact H|reflexivity]]. }
  destruct (c =? 115) eqn:N3.
  { apply Z.eqb_eq in N3. subst c. cbv beta iota in H. apply pt_omap_some in H as (ps' & H & ->).
    right; right; left. exists r1, ps'. split; [reflexivity|split; [exact H|reflexivity]]. }
  destruct (c =? 48) eqn:N4.
  { apply Z.eqb_eq in N4. subst c. cbv beta iota in H.
    destruct r1 as [|c2 [|c3 r3]]; try discriminate H.
    destruct (c2 =? 52) eqn:N5.
    - apply Z.eqb_eq in N5. subst c2. destruct (c3 =? 120) eqn:N6; cbn [andb] in H; [|discriminate H].
      apply Z.eqb_eq in N6. subst c3. apply pt_omap_some in H as (ps' & H & ->).
      right; right; right; left. exists r3, ps'. split; [reflexivity|split; [exact H|reflexivity]].
    - destruct (c2 =? 50) eqn:N7; cbn [andb] in H; [|discriminate H].
      apply Z.eqb_eq in N7. subst c2. destruct (c3 =? 120) eqn:N6; cbn [andb] in H; [|discriminate H].
      apply Z.eqb_eq in N6. subst c3. apply pt_omap_some in H as (ps' & H & ->).
      right; right; right; right; left. exists r3, ps'. split; [reflexivity|split; [exact H|reflexivity]]. }
  destruct (c =? 108) eqn:N8.
  { apply Z.eqb_eq in N8. subst c. cbv beta iota in H.
    destruct r1 as [|c2 [|c3 r3]]; try discriminate H.
    destruct (c2 =? 108) eqn:N5; cbn [andb] in H; [|discriminate H].
    destruct (c3 =? 117) eqn:N6; cbn [andb] in H; [|discriminate H].
    apply Z.eqb_eq in N5. apply Z.eqb_eq in N6. subst c2 c3. apply pt_omap_some in H as (ps' & H & ->).
    right; right; right; right; right; left. exists r3, ps'. split; [reflexivity|split; [exact H|reflexivity]]. }
  destruct (c =? 46) eqn:N9.
  { apply Z.eqb_eq in N9. subst c. cbv beta iota in H.
    destruct r1 as [|c2 [|c3 r3]]; try discriminate H.
    destruct (c2 =? 42) eqn:N5; cbn [andb] in H; [|discriminate H].
    destruct (c3 =? 115) eqn:N6; cbn [andb] in H; [|discriminate H].
    apply Z.eqb_eq in N5. apply Z.eqb_eq in N6. subst c2 c3. apply pt_omap_some in H as (ps' & H & ->).
    right; right; right; right; right; right. exists r3, ps'. split; [reflexivity|split; [exact H|reflexivity]]. }
  discriminate H.
Qed.

Lemma pt_parse_lit : forall b r ps, b <> 37 -> pf_parse (b :: r) = Some ps ->
  0 < b < 256 /\ exists ps', pf_parse r = Some ps' /\ ps = PLit b :: ps'.
Proof.
  intros b r ps Hb H. cbn [pf_parse] in H.
  replace (b =? 37) with false in H by (symmetry; apply Z.eqb_neq; exact Hb).
  destruct (0 <? b) eqn:E1; cbn [andb] in H; [|discriminate H].
  destruct (b <? 256) eqn:E2; cbn [andb] in H; [|discriminate H].
  apply Z.ltb_lt in E1. apply Z.ltb_lt in E2.
  apply pt_omap_some in H as (ps' & H & ->). split; [lia|]. exists ps'. split; [exact H|reflexivity].
Qed.

Lemma pt_parse_bytes : forall n fmt ps, (length fmt < n)%nat -> pf_parse fmt = Some ps -> Forall (fun c => 0 <= c < 256) fmt.
Proof.
  induction n as [|n IH]; intros fmt ps Hn H; [lia|].
  destruct fmt as [|b r]; [constructor|].
  destruct (Z.eqb_spec b 37) as [->|Hb].
  - apply pt_parse_pct in H.
    destruct H as [(r1 & ps' & -> & H & _)|[(r1 & ps' & -> & H & _)|[(r1 & ps' & -> & H & _)|[(r1 & ps' & -> & H & _)|[(r1 & ps' & -> & H & _)|[(r1 & ps' & -> & H & _)|(r1 & ps' & -> & H & _)]]]]]];
      cbn [length] in Hn; repeat (constructor; [cbv beta; lia|]); (eapply IH; [lia|exact H]).
  - destruct (pt_parse_lit b r ps Hb H) as [Hr (ps' & H' & _)]. constructor; [cbv beta; lia|].
    eapply IH; [|exact H']. cbn [length] in Hn. lia.
Qed.

Lemma pt_skipn_app : forall (L X : list Z), skipn (length L) (L ++ X) = X.
Proof. induction L as [|x L IH]; intros X; [reflexivity|]. cbn [length app skipn]. apply IH. Qed.

Lemma pt_lit_split : forall fmt ps, pf_parse fmt = Some ps ->
  exists L R psR, fmt = L ++ R /\ lit_run (fmt ++ [0]) = L /\ pf_parse R = Some psR /\ ps = map PLit L ++ psR
    /\ (R = [] \/ exists R', R = 37 :: R').
Proof.
  induction fmt as [|b r IH]; intros ps H.
  - exists [], [], []. cbn [pf_parse] in H. injection H as <-.
    split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. left. reflexivity.
  - destruct (Z.eqb_spec b 37) as [->|Hb].
    + exists [], (37 :: r), ps. split; [reflexivity|]. split; [reflexivity|]. split; [exact H|]. split; [reflexivity|].
      right. exists r. reflexivity.
    + destruct (pt_parse_lit b r ps Hb H) as [Hb2 (ps' & H' & ->)].
      destruct (IH ps' H') as (L & R & psR & E1 & E2 & E3 & E4 & E5).
      exists (b :: L), R, psR. split; [rewrite E1; reflexivity|]. split.
      { cbn [app lit_run]. replace (b =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
        replace (b =? 37) with false by (symmetry; apply Z.eqb_neq; exact Hb). cbn [orb]. rewrite E2. reflexivity. }
      split; [exact E3|]. split; [rewrite E4; reflexivity|]. exact E5.
Qed.

Lemma pt_text_lits : forall L ps args, pf_text (map PLit L ++ ps) args = option_map (app L) (pf_text ps args).
Proof.
  induction L as [|x L IH]; intros ps args; cbn [map app pf_text]; [|rewrite IH]; destruct (pf_text ps args); reflexivity.
Qed.

Lemma pt_pargs_lits : forall L ps args, pf_pargs (map PLit L ++ ps) args = pf_pargs ps args.
Proof. induction L as [|x L IH]; intros ps args; cbn [map app pf_pargs]; auto. Qed.

Lemma pt_pargs_nog : forall ps args, Forall pt_nog (pf_pargs ps args).
Proof.
  induction ps as [|p ps IH]; intros args; [constructor|].
  destruct p; cbn [pf_pargs]; try apply IH;
    destruct args as [|[v|u|s] [|[v2|u2|s2] a']]; repeat constructor; apply IH.
Qed.

Lemma pt_fp_nog : forall fuel s args, Forall pt_nog args -> fp_calls fuel s args = [].
Proof.
  induction fuel as [|fuel IH]; intros s args H; [reflexivity|].
  cbn [fp_calls]. destruct s as [|c s1]; [reflexivity|].
  destruct (c =? 0); [reflexivity|].
  cbv zeta. destruct (0 <? zlength (lit_run (c :: s1))); [apply IH; exact H|].
  destruct (skipn (Datatypes.length (lit_run (c :: s1))) (c :: s1)) as [|c1 s2]; [reflexivity|].
  destruct (parse_dir s2) as [[d s3]|].
  - destruct args as [|a args']; [reflexivity|]. inversion H as [|? ? Ha Hr]; subst.
    destruct a; cbn [pt_nog] in Ha; try contradiction; apply IH; exact Hr.
  - destruct args as [|[ss|k|u|dd|ll] args']; try reflexivity.
    destruct args' as [|a args']; [reflexivity|]. inversion H as [|? ? _ Hr]; subst. inversion Hr as [|? ? Ha Hr']; subst.
    destruct (parse_star s2) as [[d s3]|]; [|reflexivity].
    destruct a; cbn [pt_nog] in Ha; try contradiction; apply IH; exact Hr'.
Qed.

Lemma pt_pd_d : forall t, parse_dir (100 :: t) = Some (mkDir 0 0 (-1) false 100 T_INT, t).
Proof. intros [|c t]; reflexivity. Qed.
Lemma pt_pd_c : forall t, parse_dir (99 :: t) = Some (mkDir 0 0 (-1) false 99 T_INT, t).
Proof. intros [|c t]; reflexivity. Qed.
Lemma pt_pd_s : forall t, parse_dir (115 :: t) = Some (mkDir 0 0 (-1) false 115 T_PTR, t).
Proof. intros [|c t]; reflexivity. Qed.
Lemma pt_pd_x4 : forall t, parse_dir (48 :: 52 :: 120 :: t) = Some (mkDir 65536 4 (-1) false 120 T_UINT, t).
Proof. intros t; reflexivity. Qed.
Lemma pt_pd_x2 : forall t, parse_dir (48 :: 50 :: 120 :: t) = Some (mkDir 65536 2 (-1) false 120 T_UINT, t).
Proof. intros t; reflexivity. Qed.
Lemma pt_pd_ps : forall t, parse_dir (46 :: 42 :: 115 :: t) = None.
Proof. intros t; reflexivity. Qed.
Lemma pt_ps_ps : forall t, parse_star (46 :: 42 :: 115 :: t) = Some (mkDir 0 0 0 true 115 T_PTR, t).
Proof. intros [|c t]; reflexivity. Qed.

Lemma pt_digits : forall n f x acc, 1 <= x < 10 ^ Z.of_nat n -> (n <= f)%nat ->
  digits_aux f 10 (fun v => 48 + v) x acc = pf_digits n x acc.
Proof.
  induction n as [|n IH]; intros f x acc Hx Hf.
  - cbn in Hx. lia.
  - destruct f as [|f]; [lia|]. cbn [digits_aux pf_digits].
    replace (x =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
    rewrite Nat2Z.inj_succ, Z.pow_succ_r in Hx by lia.
    destruct (Z.ltb_spec x 10) as [Hl|Hl].
    + rewrite Z.div_small, Z.mod_small by lia. destruct f; reflexivity.
    + apply IH; [|lia]. split; [apply Z.div_le_lower_bound; lia|apply Z.div_lt_upper_bound; lia].
Qed.

Lemma pt_dec_eq : forall x, 1 <= x <= 2^31 -> pf_digits 11 x [] = dec_digits x.
Proof.
  intros x Hx. unfold dec_digits. symmetry. apply pt_digits; [|lia].
  split; [lia|]. change (10 ^ Z.of_nat 11) with 100000000000. lia.
Qed.

Lemma pt_hexd : forall v, 0 <= v < 16 -> Z.lor (znth XDIGITS v) 32 = pf_hexd v.
Proof.
  intros v Hv. assert (Hn : exists n : nat, v = Z.of_nat n /\ (n < 16)%nat) by (exists (Z.to_nat v); lia).
  destruct Hn as [n [-> Hn]]. do 16 (destruct n as [|n]; [reflexivity|]). lia.
Qed.

Lemma pt_hexs : forall n f x acc, 1 <= x < 16 ^ Z.of_nat n -> (n <= f)%nat ->
  digits_aux f 16 (fun v => Z.lor (znth XDIGITS v) 32) x acc = pf_hexs n x acc.
Proof.
  induction n as [|n IH]; intros f x acc Hx Hf.
  - cbn in Hx. lia.
  - destruct f as [|f]; [lia|]. cbn [digits_aux pf_hexs].
    replace (x =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
    rewrite Nat2Z.inj_succ, Z.pow_succ_r in Hx by lia.
    destruct (Z.ltb_spec x 16) as [Hl|Hl].
    + rewrite Z.div_small, Z.mod_small, pt_hexd by lia. destruct f; reflexivity.
    + rewrite pt_hexd by (apply Z.mod_pos_bound; lia). apply IH; [|lia].
      split; [apply Z.div_le_lower_bound; lia|apply Z.div_lt_upper_bound; lia].
Qed.

Lemma pt_hex_eq : forall x, 1 <= x < 2^32 -> hex_digits 32 x = pf_hexs 8 x [].
Proof.
  intros x Hx. unfold hex_digits. apply pt_hexs; [|lia].
  split; [lia|]. change (16 ^ Z.of_nat 8) with 4294967296. lia.
Qed.

Lemma pt_tail_exact : forall cnt fl w p prefix body r out,
  w <= zlength prefix + zlength body -> p <= zlength body -> 0 <= cnt ->
  cnt + (zlength prefix + zlength body) <= INT_MAX ->
  r = cnt + (zlength prefix + zlength body) -> out = prefix ++ body ->
  exists ps, tail_pieces cnt fl w p prefix body = Some (ps, r) /\ concat ps = out.
Proof.
  intros cnt fl w p prefix body r out Hw Hp Hc Hm -> ->.
  pose proof (pt_zlength_nonneg prefix). pose proof (pt_zlength_nonneg body).
  unfold tail_pieces. cbv zeta.
  rewrite (Z.max_r p (zlength body)) by lia.
  rewrite (Z.max_r w (zlength prefix + zlength body)) by lia.
  replace (INT_MAX - zlength prefix <? zlength body) with false by (symmetry; apply Z.ltb_ge; lia).
  replace (INT_MAX - cnt <? zlength prefix + zlength body) with false by (symmetry; apply Z.ltb_ge; lia).
  unfold pad_pieces. rewrite !Z.leb_refl, !orb_true_r.
  eexists. split; [reflexivity|]. cbn [concat app]. rewrite app_nil_r. reflexivity.
Qed.

Lemma pt_tail_zpad : forall cnt W body, 0 <= W < 256 -> 0 <= cnt -> cnt + Z.max W (zlength body) <= INT_MAX ->
  exists ps, tail_pieces cnt 65536 W (zlength body) [] body = Some (ps, cnt + Z.max W (zlength body))
    /\ concat ps = zrepeat 48 (W - zlength body) ++ body.
Proof.
  intros cnt W body HW Hc Hm. pose proof (pt_zlength_nonneg body) as Hb.
  unfold tail_pieces. cbv zeta. change (zlength (@nil Z)) with 0.
  rewrite Z.max_id, Z.add_0_l.
  replace (INT_MAX - 0 <? zlength body) with false by (symmetry; apply Z.ltb_ge; lia).
  replace (INT_MAX - cnt <? Z.max W (zlength body)) with false by (symmetry; apply Z.ltb_ge; lia).
  unfold pad_pieces.
  destruct (Z_lt_le_dec (zlength body) W) as [Hl|Hl].
  - rewrite (Z.max_l W (zlength body)) by lia.
    replace (W <=? zlength body) with false by (symmetry; apply Z.leb_gt; lia).
    replace (256 <=? W - zlength body) with false by (symmetry; apply Z.leb_gt; lia).
    rewrite Z.leb_refl. eexists. split; [reflexivity|]. cbn [concat app]. rewrite app_nil_r. reflexivity.
  - rewrite (Z.max_r W (zlength body)) by lia. rewrite Z.leb_refl.
    eexists. split; [reflexivity|]. cbn [concat app]. rewrite app_nil_r.
    unfold zrepeat. replace (Z.to_nat (W - zlength body)) with 0%nat by lia. reflexivity.
Qed.

Lemma pt_conv_d : forall cnt v, -2^31 <= v < 2^31 -> 0 <= cnt -> cnt + zlength (pf_dec v) <= INT_MAX ->
  exists ps, conv_pieces cnt (mkDir 0 0 (-1) false 100 T_INT) (PA_i v) = Some (ps, cnt + zlength (pf_dec v))
    /\ concat ps = pf_dec v.
Proof.
  intros cnt v Hv Hc Hm.
  destruct (Z_lt_le_dec v 0) as [Hn|Hn].
  - assert (D : pf_dec v = [45] ++ dec_digits (- v)).
    { unfold pf_dec. replace (v <? 0) with true by (symmetry; apply Z.ltb_lt; lia). rewrite pt_dec_eq by lia. reflexivity. }
    assert (C1 : conv_pieces cnt (mkDir 0 0 (-1) false 100 T_INT) (PA_i v) = int_pieces cnt 0 0 (-1) false (- v) [45] (dec_digits (- v))).
    { unfold conv_pieces. cbv zeta.
      replace (v mod 2 ^ 64) with (v + 2 ^ 64) by (apply Z.mod_unique with (q := -1); lia).
      replace (INTMAX_MAX <? v + 2 ^ 64) with true by (symmetry; apply Z.ltb_lt; unfold INTMAX_MAX; lia).
      replace ((- (v + 2 ^ 64)) mod 2 ^ 64) with (- v) by (apply Z.mod_unique with (q := -1); lia).
      reflexivity. }
    assert (C2 : int_pieces cnt 0 0 (-1) false (- v) [45] (dec_digits (- v))
                 = tail_pieces cnt 0 0 (Z.max (-1) (zlength (dec_digits (- v)) + 0)) [45] (dec_digits (- v))).
    { unfold int_pieces. replace (- v =? 0) with false by (symmetry; apply Z.eqb_neq; lia). reflexivity. }
    rewrite C1, C2. pose proof (pt_zlength_nonneg (dec_digits (- v))).
    rewrite D, pt_zlength_app in Hm.
    apply pt_tail_exact; [zl|zl|zl|zl| |exact D]. rewrite D, pt_zlength_app. reflexivity.
  - destruct (Z.eq_dec v 0) as [->|Hz].
    + exists [[]; [48]; []]. split; [|reflexivity].
      change (conv_pieces cnt (mkDir 0 0 (-1) false 100 T_INT) (PA_i 0))
        with (if INT_MAX - cnt <? 1 then None else Some ([[]; [48]; []], cnt + 1)).
      change (zlength (pf_dec 0)) with 1 in *.
      replace (INT_MAX - cnt <? 1) with false by (symmetry; apply Z.ltb_ge; lia). reflexivity.
    + assert (D : pf_dec v = dec_digits v).
      { unfold pf_dec. replace (v <? 0) with false by (symmetry; apply Z.ltb_ge; lia). apply pt_dec_eq. lia. }
      assert (C1 : conv_pieces cnt (mkDir 0 0 (-1) false 100 T_INT) (PA_i v) = int_pieces cnt 0 0 (-1) false v [] (dec_digits v)).
      { unfold conv_pieces. cbv zeta. rewrite (Z.mod_small v (2 ^ 64)) by lia.
        replace (INTMAX_MAX <? v) with false by (symmetry; apply Z.ltb_ge; unfold INTMAX_MAX; lia). reflexivity. }
      assert (C2 : int_pieces cnt 0 0 (-1) false v [] (dec_digits v)
                   = tail_pieces cnt 0 0 (Z.max (-1) (zlength (dec_digits v) + 0)) [] (dec_digits v)).
      { unfold int_pieces. replace (v =? 0) with false by (symmetry; apply Z.eqb_neq; lia). reflexivity. }
      rewrite C1, C2. rewrite D in *. pose proof (pt_zlength_nonneg (dec_digits v)).
      apply pt_tail_exact; [zl|zl|zl|zl|reflexivity|reflexivity].
Qed.

Lemma pt_conv_c : forall cnt v, 0 <= cnt -> cnt + zlength [v mod 256] <= INT_MAX ->
  exists ps, conv_pieces cnt (mkDir 0 0 (-1) false 99 T_INT) (PA_i v) = Some (ps, cnt + zlength [v mod 256])
    /\ concat ps = [v mod 256].
Proof.
  intros cnt v Hc Hm.
  change (conv_pieces cnt (mkDir 0 0 (-1) false 99 T_INT) (PA_i v)) with (tail_pieces cnt 0 0 1 [] [v mod 256]).
  apply pt_tail_exact; [zl|zl|zl|zl|reflexivity|reflexivity].
Qed.

Lemma pt_conv_s : forall cnt s, zlength s < INT_MAX -> 0 <= cnt -> cnt + zlength s <= INT_MAX ->
  exists ps, conv_pieces cnt (mkDir 0 0 (-1) false 115 T_PTR) (PA_s s) = Some (ps, cnt + zlength s) /\ concat ps = s.
Proof.
  intros cnt s Hs Hc Hm.
  assert (C : conv_pieces cnt (mkDir 0 0 (-1) false 115 T_PTR) (PA_s s) = tail_pieces cnt 0 0 (zlength s) [] (firstn (Z.to_nat (zlength s)) s)).
  { unfold conv_pieces. replace (INT_MAX <=? zlength s) with false by (symmetry; apply Z.leb_gt; lia). reflexivity. }
  rewrite C. replace (firstn (Z.to_nat (zlength s)) s) with s by (unfold zlength; rewrite Nat2Z.id, firstn_all; reflexivity).
  pose proof (pt_zlength_nonneg s).
  apply pt_tail_exact; [zl|zl|zl|zl|reflexivity|reflexivity].
Qed.

Lemma pt_conv_ps : forall cnt k s, 0 <= k <= zlength s -> 0 <= cnt -> cnt + zlength (firstn (Z.to_nat k) s) <= INT_MAX ->
  exists ps, conv_pieces cnt (set_prec (mkDir 0 0 0 true 115 T_PTR) k) (PA_s s) = Some (ps, cnt + zlength (firstn (Z.to_nat k) s))
    /\ concat ps = firstn (Z.to_nat k) s.
Proof.
  intros cnt k s Hk Hc Hm.
  assert (HF : zlength (firstn (Z.to_nat k) s) = k) by (unfold zlength in *; rewrite length_firstn; lia).
  assert (C : conv_pieces cnt (set_prec (mkDir 0 0 0 true 115 T_PTR) k) (PA_s s)
              = tail_pieces cnt 0 0 (Z.min (zlength s) k) [] (firstn (Z.to_nat (Z.min (zlength s) k)) s)).
  { unfold conv_pieces, set_prec. cbv zeta. cbn [d_fl d_w d_p d_xp d_t d_ty].
    replace (k <? 0) with false by (symmetry; apply Z.ltb_ge; lia). reflexivity. }
  rewrite C, (Z.min_r (zlength s) k) by lia.
  apply pt_tail_exact; [zl|zl|zl|zl|reflexivity|reflexivity].
Qed.

Lemma pt_conv_x : forall (W : nat) cnt v, (W = 2 \/ W = 4)%nat -> 0 <= cnt -> cnt + zlength (pt_hexw W v) <= INT_MAX ->
  exists ps, conv_pieces cnt (mkDir 65536 (Z.of_nat W) (-1) false 120 T_UINT) (PA_u (v mod 2^32))
               = Some (ps, cnt + zlength (pt_hexw W v)) /\ concat ps = pt_hexw W v.
Proof.
  intros W cnt v HW Hc Hm. pose proof (Z.mod_pos_bound v (2^32) ltac:(lia)) as Hu.
  destruct (Z.eq_dec (v mod 2^32) 0) as [Hz|Hz].
  - assert (H0 : pt_hexw W v = repeat 48 (W - 1) ++ [48]) by (unfold pt_hexw; rewrite Hz; reflexivity).
    rewrite H0 in *. rewrite Hz. destruct HW as [-> | ->].
    + exists [[]; [48]; [48]; []]. split; [|reflexivity].
      change (conv_pieces cnt (mkDir 65536 (Z.of_nat 2) (-1) false 120 T_UINT) (PA_u 0))
        with (if INT_MAX - cnt <? 2 then None else Some ([[]; [48]; [48]; []], cnt + 2)).
      change (zlength (repeat 48 (2 - 1) ++ [48])) with 2 in *.
      replace (INT_MAX - cnt <? 2) with false by (symmetry; apply Z.ltb_ge; lia). reflexivity.
    + exists [[]; [48; 48; 48]; [48]; []]. split; [|reflexivity].
      change (conv_pieces cnt (mkDir 65536 (Z.of_nat 4) (-1) false 120 T_UINT) (PA_u 0))
        with (if INT_MAX - cnt <? 4 then None else Some ([[]; [48; 48; 48]; [48]; []], cnt + 4)).
      change (zlength (repeat 48 (4 - 1) ++ [48])) with 4 in *.
      replace (INT_MAX - cnt <? 4) with false by (symmetry; apply Z.ltb_ge; lia). reflexivity.
  - set (h := hex_digits 32 (v mod 2^32)).
    assert (Hh : pf_hexs 8 (v mod 2^32) [] = h) by (symmetry; apply pt_hex_eq; lia).
    assert (H4 : pt_hexw W v = zrepeat 48 (Z.of_nat W - zlength h) ++ h).
    { unfold pt_hexw. cbv zeta. rewrite Hh. unfold zrepeat, zlength. f_equal. f_equal. lia. }
    assert (L4 : zlength (pt_hexw W v) = Z.max (Z.of_nat W) (zlength h)).
    { rewrite H4, pt_zlength_app. unfold zrepeat, zlength. rewrite repeat_length. lia. }
    assert (C : conv_pieces cnt (mkDir 65536 (Z.of_nat W) (-1) false 120 T_UINT) (PA_u (v mod 2^32))
                = tail_pieces cnt 65536 (Z.of_nat W) (Z.max (-1) (zlength h + 0)) [] h).
    { unfold conv_pieces, int_pieces. cbv zeta.
      replace (v mod 2 ^ 32 =? 0) with false by (symmetry; apply Z.eqb_neq; exact Hz). reflexivity. }
    pose proof (pt_zlength_nonneg h).
    rewrite C, Z.add_0_r, (Z.max_r (-1) (zlength h)) by lia. rewrite L4 in *. rewrite H4.
    apply pt_tail_zpad; lia.
Qed.

Lemma pt_digits_any : forall n x acc, 1 <= x -> digits_aux n 10 (fun v => 48 + v) x acc = pf_digits n x acc.
Proof.
  induction n as [|n IH]; intros x acc Hx; [reflexivity|]. cbn [digits_aux pf_digits].
  replace (x =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
  destruct (Z.ltb_spec x 10) as [Hl|Hl].
  - rewrite Z.div_small, Z.mod_small by lia. destruct n; reflexivity.
  - apply IH. apply Z.div_le_lower_bound; lia.
Qed.

Lemma pt_udec_eq : forall u, 1 <= u -> pf_udec u = dec_digits u.
Proof. intros u Hu. unfold pf_udec, dec_digits. symmetry. apply pt_digits_any. exact Hu. Qed.

Lemma pt_int_udec : forall cnt u, 0 <= u -> 0 <= cnt -> cnt + zlength (pf_udec u) <= INT_MAX ->
  exists ps, int_pieces cnt 0 0 (-1) false u [] (dec_digits u) = Some (ps, cnt + zlength (pf_udec u)) /\ concat ps = pf_udec u.
Proof.
  intros cnt u Hu Hc Hm. destruct (Z.eq_dec u 0) as [->|Hz].
  - exists [[]; [48]; []]. split; [|reflexivity].
    change (int_pieces cnt 0 0 (-1) false 0 [] (dec_digits 0))
      with (if INT_MAX - cnt <? 1 then None else Some ([[]; [48]; []], cnt + 1)).
    change (zlength (pf_udec 0)) with 1 in *.
    replace (INT_MAX - cnt <? 1) with false by (symmetry; apply Z.ltb_ge; lia). reflexivity.
  - rewrite (pt_udec_eq u) in * by lia.
    assert (C2 : int_pieces cnt 0 0 (-1) false u [] (dec_digits u)
                 = tail_pieces cnt 0 0 (Z.max (-1) (zlength (dec_digits u) + 0)) [] (dec_digits u)).
    { unfold int_pieces. replace (u =? 0) with false by (symmetry; apply Z.eqb_neq; lia). reflexivity. }
    rewrite C2. pose proof (pt_zlength_nonneg (dec_digits u)).
    apply pt_tail_exact; [zl|zl|zl|zl|reflexivity|reflexivity].
Qed.

Lemma pt_pd_llu : forall t, parse_dir (108 :: 108 :: 117 :: t) = Some (mkDir 0 0 (-1) false 117 T_ULLONG, t).
Proof. intros t; reflexivity. Qed.
Lemma pt_pd_u : forall t, parse_dir (117 :: t) = Some (mkDir 0 0 (-1) false 117 T_UINT, t).
Proof. intros [|c t]; reflexivity. Qed.
Lemma pt_pd_zu : forall t, parse_dir (122 :: 117 :: t) = Some (mkDir 0 0 (-1) false 117 T_SIZET, t).
Proof. intros t; reflexivity. Qed.

Lemma pt_conv_ull : forall cnt ty u, (ty = T_ULLONG \/ ty = T_SIZET) -> 0 <= u -> 0 <= cnt -> cnt + zlength (pf_udec u) <= INT_MAX ->
  exists ps, conv_pieces cnt (mkDir 0 0 (-1) false 117 ty) (PA_ull u) = Some (ps, cnt + zlength (pf_udec u))
    /\ concat ps = pf_udec u.
Proof.
  intros cnt ty u Hty Hu Hc Hm.
  replace (conv_pieces cnt (mkDir 0 0 (-1) false 117 ty) (PA_ull u)) with (int_pieces cnt 0 0 (-1) false u [] (dec_digits u))
    by (destruct Hty as [-> | ->]; reflexivity).
  apply pt_int_udec; assumption.
Qed.

Lemma pt_conv_u : forall cnt u, 0 <= u -> 0 <= cnt -> cnt + zlength (pf_udec u) <= INT_MAX ->
  exists ps, conv_pieces cnt (mkDir 0 0 (-1) false 117 T_UINT) (PA_u u) = Some (ps, cnt + zlength (pf_udec u))
    /\ concat ps = pf_udec u.
Proof.
  intros cnt u Hu Hc Hm.
  change (conv_pieces cnt (mkDir 0 0 (-1) false 117 T_UINT) (PA_u u)) with (int_pieces cnt 0 0 (-1) false u [] (dec_digits u)).
  apply pt_int_udec; assumption.
Qed.

Lemma pt_dir_step : forall fuel c t d t' a pa cnt ps1 cnt' ps r,
  c <> 37 -> parse_dir (c :: t) = Some (d, t') -> conv_pieces cnt d a = Some (ps1, cnt') ->
  printf_pieces_loop fuel t' pa cnt' = Some (ps, r) ->
  printf_pieces_loop (S fuel) (37 :: c :: t) (a :: pa) cnt = Some ([] :: ps1 ++ ps, r).
Proof.
  intros fuel c t d t' a pa cnt ps1 cnt' ps r Hc Hd C P.
  cbn [printf_pieces_loop]. cbv zeta.
  change (lit_run (37 :: c :: t)) with (@nil Z).
  cbv beta iota zeta delta [skipn Datatypes.length].
  replace (c =? 37) with false by (symmetry; apply Z.eqb_neq; exact Hc).
  rewrite Hd. cbv beta iota zeta. rewrite C. cbv beta iota zeta. rewrite P. reflexivity.
Qed.

Lemma pt_star_step : forall fuel c t d t' k a pa cnt ps1 cnt' ps r,
  c <> 37 -> parse_dir (c :: t) = None -> parse_star (c :: t) = Some (d, t') ->
  conv_pieces cnt (set_prec d k) a = Some (ps1, cnt') ->
  printf_pieces_loop fuel t' pa cnt' = Some (ps, r) ->
  printf_pieces_loop (S fuel) (37 :: c :: t) (PA_i k :: a :: pa) cnt = Some ([] :: ps1 ++ ps, r).
Proof.
  intros fuel c t d t' k a pa cnt ps1 cnt' ps r Hc Hd Hs C P.
  cbn [printf_pieces_loop]. cbv zeta.
  change (lit_run (37 :: c :: t)) with (@nil Z).
  cbv beta iota zeta delta [skipn Datatypes.length].
  replace (c =? 37) with false by (symmetry; apply Z.eqb_neq; exact Hc).
  rewrite Hd. cbv beta iota zeta. rewrite Hs. cbv beta iota zeta. rewrite C. cbv beta iota zeta. rewrite P. reflexivity.
Qed.

Lemma pt_lit_step : forall fuel b s args cnt L s1 ps r,
  b <> 0 -> lit_run (b :: s) = L -> skipn (length L) (b :: s) = s1 -> 0 < zlength L ->
  match s1 with [] => False | c1 :: s2 => c1 = 0 \/ (c1 = 37 /\ exists c2 s3, s2 = c2 :: s3 /\ c2 <> 37) end ->
  cnt + zlength L <= INT_MAX ->
  printf_pieces_loop fuel s1 args (cnt + zlength L) = Some (ps, r) ->
  printf_pieces_loop (S fuel) (b :: s) args cnt = Some (L :: ps, r).
Proof.
  intros fuel b s args cnt L s1 ps r Hb HL Hs HL0 Hs1 Hc P.
  cbn [printf_pieces_loop].
  replace (b =? 0) with false by (symmetry; apply Z.eqb_neq; exact Hb).
  cbv zeta. rewrite HL, Hs.
  replace (0 <? zlength L) with true by (symmetry; apply Z.ltb_lt; exact HL0).
  replace (INT_MAX - cnt <? zlength L) with false by (symmetry; apply Z.ltb_ge; lia).
  rewrite P.
  destruct s1 as [|c1 s2]; [contradiction|].
  destruct Hs1 as [->|(-> & c2 & s3 & -> & Hc2)].
  - reflexivity.
  - cbv beta iota. replace (c2 =? 37) with false by (symmetry; apply Z.eqb_neq; exact Hc2). reflexivity.
Qed.

Lemma pt_dir_glue : forall fuel c t d t' a pa cnt ps1 X pcs T',
  c <> 37 -> parse_dir (c :: t) = Some (d, t') ->
  conv_pieces cnt d a = Some (ps1, cnt + zlength X) -> concat ps1 = X ->
  printf_pieces_loop fuel t' pa (cnt + zlength X) = Some (pcs, cnt + zlength X + zlength T') -> concat pcs = T' ->
  exists pcs', printf_pieces_loop (S fuel) (37 :: c :: t) (a :: pa) cnt = Some (pcs', cnt + zlength (X ++ T'))
    /\ concat pcs' = X ++ T'.
Proof.
  intros fuel c t d t' a pa cnt ps1 X pcs T' Hc Hd C E1 P E.
  exists ([] :: ps1 ++ pcs). split.
  - rewrite pt_zlength_app, Z.add_assoc. eapply pt_dir_step; eassumption.
  - cbn [concat app]. rewrite concat_app, E1, E. reflexivity.
Qed.

Lemma pt_star_glue : forall fuel c t d t' k a pa cnt ps1 X pcs T',
  c <> 37 -> parse_dir (c :: t) = None -> parse_star (c :: t) = Some (d, t') ->
  conv_pieces cnt (set_prec d k) a = Some (ps1, cnt + zlength X) -> concat ps1 = X ->
  printf_pieces_loop fuel t' pa (cnt + zlength X) = Some (pcs, cnt + zlength X + zlength T') -> concat pcs = T' ->
  exists pcs', printf_pieces_loop (S fuel) (37 :: c :: t) (PA_i k :: a :: pa) cnt = Some (pcs', cnt + zlength (X ++ T'))
    /\ concat pcs' = X ++ T'.
Proof.
  intros fuel c t d t' k a pa cnt ps1 X pcs T' Hc Hd Hs C E1 P E.
  exists ([] :: ps1 ++ pcs). split.
  - rewrite pt_zlength_app, Z.add_assoc. eapply pt_star_step; eassumption.
  - cbn [concat app]. rewrite concat_app, E1, E. reflexivity.
Qed.

Ltac pt_hs HS := destruct HS as [HS|HS];
  [left; rewrite ?pt_zlength_app in HS; lia | right; intros ? Hin; apply HS; cbn [In]; tauto].

Lemma pt_pieces : forall fuel fmt ps args T cnt,
  (length fmt < fuel)%nat -> pf_parse fmt = Some ps -> pf_text ps args = Some T -> Forall pt_fit args ->
  0 <= cnt -> cnt + zlength T <= INT_MAX ->
  (cnt + zlength T < INT_MAX \/ (forall s, In (APtr s) args -> zlength s < INT_MAX)) ->
  exists pcs, printf_pieces_loop fuel (fmt ++ [0]) (pf_pargs ps args) cnt = Some (pcs, cnt + zlength T) /\ concat pcs = T.
Proof.
  induction fuel as [|fuel IH]; intros fmt ps args T cnt Hlen Hp Ht Ha Hc HT HS; [lia|].
  destruct fmt as [|b r].
  { cbn [pf_parse] in Hp. injection Hp as <-. destruct args as [|a args]; cbn [pf_text] in Ht; [|discriminate Ht].
    injection Ht as <-. exists []. split; [|reflexivity]. change (zlength (@nil Z)) with 0. rewrite Z.add_0_r. reflexivity. }
  destruct (Z.eqb_spec b 37) as [->|Hb].
  - apply pt_parse_pct in Hp.
    destruct Hp as [(r1 & ps' & -> & Hp' & ->)|[(r1 & ps' & -> & Hp' & ->)|[(r1 & ps' & -> & Hp' & ->)|[(r1 & ps' & -> & Hp' & ->)|[(r1 & ps' & -> & Hp' & ->)|[(r1 & ps' & -> & Hp' & ->)|(r1 & ps' & -> & Hp' & ->)]]]]]];
      cbn [length] in Hlen.
    + destruct args as [|[v|u|s] a']; cbn [pf_text] in Ht; try discriminate Ht.
      apply pt_omap_some in Ht as (T' & Ht' & ->). inversion_clear Ha as [|? ? Hv Ha']. cbn [pt_fit] in Hv.
      rewrite pt_zlength_app in HT. pose proof (pt_zlength_nonneg (pf_dec v)). pose proof (pt_zlength_nonneg T').
      destruct (pt_conv_d cnt v Hv Hc ltac:(lia)) as (ps1 & C & E1).
      destruct (IH r1 ps' a' T' (cnt + zlength (pf_dec v)) ltac:(lia) Hp' Ht' Ha' ltac:(lia) ltac:(lia) ltac:(pt_hs HS))
        as (pcs & P & E).
      cbn [app pf_pargs]. exact (pt_dir_glue fuel 100 _ _ _ _ _ cnt ps1 (pf_dec v) pcs T' ltac:(lia) (pt_pd_d _) C E1 P E).
    + destruct args as [|[v|u|s] a']; cbn [pf_text] in Ht; try discriminate Ht.
      apply pt_omap_some in Ht as (T' & Ht' & ->). inversion_clear Ha as [|? ? Hv Ha'].
      change (v mod 256 :: T') with ([v mod 256] ++ T') in *.
      rewrite pt_zlength_app in HT. pose proof (pt_zlength_nonneg [v mod 256]). pose proof (pt_zlength_nonneg T').
      destruct (pt_conv_c cnt v Hc ltac:(lia)) as (ps1 & C & E1).
      destruct (IH r1 ps' a' T' (cnt + zlength [v mod 256]) ltac:(lia) Hp' Ht' Ha' ltac:(lia) ltac:(lia) ltac:(pt_hs HS))
        as (pcs & P & E).
      cbn [app pf_pargs]. exact (pt_dir_glue fuel 99 _ _ _ _ _ cnt ps1 [v mod 256] pcs T' ltac:(lia) (pt_pd_c _) C E1 P E).
    + destruct args as [|[v|u|s] a']; cbn [pf_text] in Ht; try discriminate Ht.
      apply pt_omap_some in Ht as (T' & Ht' & ->). inversion_clear Ha as [|? ? Hv Ha'].
      rewrite pt_zlength_app in HT. pose proof (pt_zlength_nonneg s). pose proof (pt_zlength_nonneg T').
      assert (Hs : zlength s < INT_MAX)
        by (destruct HS as [HS|HS]; [rewrite pt_zlength_app in HS; lia | apply HS; left; reflexivity]).
      destruct (pt_conv_s cnt s Hs Hc ltac:(lia)) as (ps1 & C & E1).
      destruct (IH r1 ps' a' T' (cnt + zlength s) ltac:(lia) Hp' Ht' Ha' ltac:(lia) ltac:(lia) ltac:(pt_hs HS))
        as (pcs & P & E).
      cbn [app pf_pargs]. exact (pt_dir_glue fuel 115 _ _ _ _ _ cnt ps1 s pcs T' ltac:(lia) (pt_pd_s _) C E1 P E).
    + destruct args as [|[v|u|s] a']; cbn [pf_text] in Ht; try discriminate Ht.
      apply pt_omap_some in Ht as (T' & Ht' & ->). inversion_clear Ha as [|? ? Hv Ha'].
      rewrite pt_zlength_app in HT. pose proof (pt_zlength_nonneg (pf_hex4 v)). pose proof (pt_zlength_nonneg T').
      destruct (pt_conv_x 4 cnt v (or_intror eq_refl) Hc ltac:(change (pt_hexw 4 v) with (pf_hex4 v); lia)) as (ps1 & C & E1).
      destruct (IH r1 ps' a' T' (cnt + zlength (pf_hex4 v)) ltac:(lia) Hp' Ht' Ha' ltac:(lia) ltac:(lia) ltac:(pt_hs HS))
        as (pcs & P & E).
      cbn [app pf_pargs]. exact (pt_dir_glue fuel 48 _ _ _ _ _ cnt ps1 (pf_hex4 v) pcs T' ltac:(lia) (pt_pd_x4 _) C E1 P E).
    + destruct args as [|[v|u|s] a']; cbn [pf_text] in Ht; try discriminate Ht.
      apply pt_omap_some in Ht as (T' & Ht' & ->). inversion_clear Ha as [|? ? Hv Ha'].
      rewrite pt_zlength_app in HT. pose proof (pt_zlength_nonneg (pf_hex2 v)). pose proof (pt_zlength_nonneg T').
      destruct (pt_conv_x 2 cnt v (or_introl eq_refl) Hc ltac:(change (pt_hexw 2 v) with (pf_hex2 v); lia)) as (ps1 & C & E1).
      destruct (IH r1 ps' a' T' (cnt + zlength (pf_hex2 v)) ltac:(lia) Hp' Ht' Ha' ltac:(lia) ltac:(lia) ltac:(pt_hs HS))
        as (pcs & P & E).
      cbn [app pf_pargs]. exact (pt_dir_glue fuel 48 _ _ _ _ _ cnt ps1 (pf_hex2 v) pcs T' ltac:(lia) (pt_pd_x2 _) C E1 P E).
    + destruct args as [|[v|u|s] a']; cbn [pf_text] in Ht; try discriminate Ht.
      apply pt_omap_some in Ht as (T' & Ht' & ->). inversion_clear Ha as [|? ? Hu Ha']. cbn [pt_fit] in Hu.
      rewrite pt_zlength_app in HT. pose proof (pt_zlength_nonneg (pf_udec u)). pose proof (pt_zlength_nonneg T').
      destruct (pt_conv_ull cnt T_ULLONG u (or_introl eq_refl) Hu Hc ltac:(lia)) as (ps1 & C & E1).
      destruct (IH r1 ps' a' T' (cnt + zlength (pf_udec u)) ltac:(lia) Hp' Ht' Ha' ltac:(lia) ltac:(lia) ltac:(pt_hs HS))
        as (pcs & P & E).
      cbn [app pf_pargs]. exact (pt_dir_glue fuel 108 _ _ _ _ _ cnt ps1 (pf_udec u) pcs T' ltac:(lia) (pt_pd_llu _) C E1 P E).
    + destruct args as [|[k|u|s] [|[v|u2|s2] a']]; cbn [pf_text] in Ht; try discriminate Ht.
      revert Ht. destruct ((0 <=? k) && (k <=? Z.of_nat (length s2))) eqn:Ek; intros Ht; [|discriminate Ht].
      apply andb_prop in Ek as [Ek1 Ek2]. apply Z.leb_le in Ek1. apply Z.leb_le in Ek2.
      apply pt_omap_some in Ht as (T' & Ht' & ->). inversion_clear Ha as [|? ? Hv Ha0]. inversion_clear Ha0 as [|? ? _ Ha'].
      rewrite pt_zlength_app in HT. pose proof (pt_zlength_nonneg (firstn (Z.to_nat k) s2)). pose proof (pt_zlength_nonneg T').
      destruct (pt_conv_ps cnt k s2 ltac:(unfold zlength; lia) Hc ltac:(lia)) as (ps1 & C & E1).
      destruct (IH r1 ps' a' T' (cnt + zlength (firstn (Z.to_nat k) s2)) ltac:(lia) Hp' Ht' Ha' ltac:(lia) ltac:(lia) ltac:(pt_hs HS))
        as (pcs & P & E).
      cbn [app pf_pargs].
      exact (pt_star_glue fuel 46 _ _ _ k _ _ cnt ps1 (firstn (Z.to_nat k) s2) pcs T' ltac:(lia) (pt_pd_ps _) (pt_ps_ps _) C E1 P E).
  - destruct (pt_parse_lit b r ps Hb Hp) as [Hb2 _].
    destruct (pt_lit_split (b :: r) ps Hp) as (L & R & psR & E1 & E2 & E3 & -> & E5).
    rewrite pt_text_lits in Ht. apply pt_omap_some in Ht as (TR & Ht' & ->).
    assert (HL : 0 < zlength L).
    { destruct L as [|x L]; [|unfold zlength; cbn [length]; lia].
      cbn [app] in E1. destruct E5 as [->|(R' & ->)]; [discriminate E1|]. injection E1 as E1 _. contradiction. }
    assert (Hlen' : (length R < fuel)%nat).
    { rewrite E1, length_app in Hlen. unfold zlength in HL. lia. }
    rewrite pt_zlength_app in HT. pose proof (pt_zlength_nonneg TR).
    destruct (IH R psR args TR (cnt + zlength L) Hlen' E3 Ht' Ha ltac:(lia) ltac:(lia) ltac:(pt_hs HS)) as (pcs & P & E).
    exists (L :: pcs). split.
    + rewrite pt_pargs_lits, pt_zlength_app, Z.add_assoc. change ((b :: r) ++ [0]) with (b :: (r ++ [0])).
      eapply pt_lit_step with (s1 := R ++ [0]); [lia | exact E2 | | exact HL | | lia | exact P].
      * change (b :: r ++ [0]) with ((b :: r) ++ [0]). rewrite E1, <- app_assoc. apply pt_skipn_app.
      * destruct E5 as [->|(R' & ->)]; [cbn [app]; left; reflexivity|].
        destruct (pt_parse_pct R' psR E3) as [(r1 & ps' & -> & _)|[(r1 & ps' & -> & _)|[(r1 & ps' & -> & _)|[(r1 & ps' & -> & _)|[(r1 & ps' & -> & _)|[(r1 & ps' & -> & _)|(r1 & ps' & -> & _)]]]]]];
          cbn [app]; right; (split; [reflexivity|]); eexists; eexists; (split; [reflexivity|lia]).
    + cbn [concat]. rewrite E. reflexivity.
Qed.

Lemma pt_fit_of : forall args, (forall v, In (AInt v) args -> -2^31 <= v < 2^31) -> (forall u, In (AU64 u) args -> 0 <= u) ->
  Forall pt_fit args.
Proof. intros args HA HU. apply Forall_forall. intros [v|u|s] Hin; [exact (HA v Hin)|exact (HU u Hin)|exact I]. Qed.

Theorem printf_text_pieces : forall fmt ps args T,
  pf_parse fmt = Some ps -> pf_text ps args = Some T ->
  (forall v, In (AInt v) args -> -2^31 <= v < 2^31) ->
  (forall u, In (AU64 u) args -> 0 <= u) ->
  zlength T <= 2147483647 ->
  (zlength T < 2147483647 \/ (forall s, In (APtr s) args -> zlength s < 2147483647)) ->
  exists pcs, printf_pieces (fmt ++ [0]) (pf_pargs ps args) = Some (pcs, zlength T) /\ concat pcs = T.
Proof.
  intros fmt ps args T Hp Ht HA HU HT HS.
  destruct (pt_pieces (length (fmt ++ [0])) fmt ps args T 0 ltac:(rewrite length_app; cbn [length]; lia) Hp Ht (pt_fit_of args HA HU)
              ltac:(lia) HT HS) as (pcs & P & E).
  exists pcs. split; [exact P|exact E].
Qed.

Theorem printf_text_model : forall fmt ps args T,
  pf_parse fmt = Some ps -> pf_text ps args = Some T ->
  (forall v, In (AInt v) args -> -2^31 <= v < 2^31) ->
  (forall u, In (AU64 u) args -> 0 <= u) ->
  zlength T <= 2147483647 ->
  (zlength T < 2147483647 \/ (forall s, In (APtr s) args -> zlength s < 2147483647)) ->
  printf_model (St:=list Z) (OUT_snf (zlength T)) OUTFP_snf (fmt ++ [0]) (pf_pargs ps args) [] = ITree.Ret (Ok (zlength T, T)).
Proof.
  intros fmt ps args T Hp Ht HA HU HT HS.
  destruct (printf_text_pieces fmt ps args T Hp Ht HA HU HT HS) as (pcs & P & E).
  pose proof (printf_model_snf_pieces (zlength T) _ _ pcs (zlength T) P ltac:(rewrite E; lia)) as M.
  rewrite E in M. exact M.
Qed.

Theorem printf_text_pass1 : forall fmt ps args T,
  pf_parse fmt = Some ps -> pf_text ps args = Some T -> zlength T <= 2147483647 ->
  pass1_ok (fmt ++ [0]) = true.
Proof.
  intros fmt ps args T Hp Ht HT.
  destruct (pt_lit_split fmt ps Hp) as (L & R & psR & E1 & E2 & E3 & -> & E5).
  rewrite pt_text_lits in Ht. apply pt_omap_some in Ht as (TR & _ & ->).
  rewrite pt_zlength_app in HT. pose proof (pt_zlength_nonneg TR).
  unfold pass1_ok. cbv zeta. rewrite E2.
  replace (zlength L <=? INT_MAX) with true by (symmetry; apply Z.leb_le; unfold INT_MAX; lia).
  rewrite E1, <- app_assoc, pt_skipn_app.
  destruct E5 as [->|(R' & ->)]; [reflexivity|].
  destruct (pt_parse_pct R' psR E3) as [(r1 & ps' & -> & _)|[(r1 & ps' & -> & _)|[(r1 & ps' & -> & _)|[(r1 & ps' & -> & _)|[(r1 & ps' & -> & _)|[(r1 & ps' & -> & _)|(r1 & ps' & -> & _)]]]]]];
    cbn [app].
  - rewrite pt_pd_d. reflexivity.
  - rewrite pt_pd_c. reflexivity.
  - rewrite pt_pd_s. reflexivity.
  - rewrite pt_pd_x4. reflexivity.
  - rewrite pt_pd_x2. reflexivity.
  - rewrite pt_pd_llu. reflexivity.
  - rewrite pt_pd_ps, pt_ps_ps. reflexivity.
Qed.

Theorem printf_text_fp : forall fmt ps args,
  fp_calls (length (fmt ++ [0])) (fmt ++ [0]) (pf_pargs ps args) = [].
Proof. intros fmt ps args. apply pt_fp_nog. apply pt_pargs_nog. Qed.

Theorem printf_text_bytes : forall fmt ps, pf_parse fmt = Some ps -> Forall (fun c => 0 <= c < 256) (fmt ++ [0]).
Proof.
  intros fmt ps Hp. apply Forall_app. split.
  - apply (pt_parse_bytes (S (length fmt)) fmt ps); [lia|exact Hp].
  - constructor; [cbv beta; lia|constructor].
Qed.

Theorem printf_text_ok : forall fmt ps args T,
  pf_parse fmt = Some ps -> pf_text ps args = Some T ->
  (forall v, In (AInt v) args -> -2^31 <= v < 2^31) ->
  (forall u, In (AU64 u) args -> 0 <= u) ->
  zlength T <= 2147483647 ->
  (zlength T < 2147483647 \/ (forall s, In (APtr s) args -> zlength s < 2147483647)) ->
  printf_model (St:=list Z) (OUT_snf (zlength T)) OUTFP_snf (fmt ++ [0]) (pf_pargs ps args) [] = ITree.Ret (Ok (zlength T, T))
  /\ pass1_ok (fmt ++ [0]) = true
  /\ fp_calls (length (fmt ++ [0])) (fmt ++ [0]) (pf_pargs ps args) = []
  /\ Forall (fun c => 0 <= c < 256) (fmt ++ [0]).
Proof.
  intros fmt ps args T Hp Ht HA HU HT HS. split; [|split; [|split]].
  - exact (printf_text_model fmt ps args T Hp Ht HA HU HT HS).
  - exact (printf_text_pass1 fmt ps args T Hp Ht HT).
  - apply printf_text_fp.
  - exact (printf_text_bytes fmt ps Hp).
Qed.
