(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/cjson/cjson_read_fuzzer/lib/A/F_vsnprintf.v, with its module paths and module names changed; 120 of its 167 lines of code are new or changed and 2093 lines of the source are left out. *)
From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.CJ.Lib Require Import ITree.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.CJ.Spec Require Import Prelim Monad FmtFp.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.CJ.RL.GX Require Import Printf_model Printf_text.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.CJ.RL.GX Require G_printf_core_common.
Import G_printf_core_common.G_printf_iface.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope mspec_scope.

Lemma cap_mbind_unr : forall {St A B} (m : M St A) (f : A -> M St B) s,
  m s = ITree.Ret Unr -> mbind m f s = ITree.Ret Unr.
Proof. intros St A B m f s H. unfold mbind, ebind. rewrite H. reflexivity. Qed.

Lemma cap_mbind_mbind_unr : forall {St A B C} (m : M St A) (f : A -> M St B) (g : B -> M St C) s,
  m s = ITree.Ret Unr -> mbind (mbind m f) g s = ITree.Ret Unr.
Proof. intros St A B C m f g s H. unfold mbind, ebind. rewrite H. reflexivity. Qed.

Lemma cap_out : forall OM bs o, OM < zlength o + zlength bs -> OUT_snf OM bs o = ITree.Ret Unr.
Proof.
  intros OM bs o H. unfold OUT_snf. rewrite (pt_mbind_eq mget _ o o o) by reflexivity.
  replace (zlength o + zlength bs <=? OM) with false by (symmetry; apply Z.leb_gt; exact H). reflexivity.
Qed.

Lemma cap_mpad : forall OM c w l fl o ps,
  pad_pieces c w l fl = Some ps -> zlength o <= OM -> OM < zlength o + zlength (concat ps) ->
  mpad (OUT_snf OM) c w l fl o = ITree.Ret Unr.
Proof.
  intros OM c w l fl o ps P H0 H. unfold mpad, pad_pieces in *.
  destruct (negb (Z.land fl (Z.lor LEFT_ADJ ZERO_PAD) =? 0) || (w <=? l))%bool.
  - inversion P; subst. cbn [concat] in H. rewrite pt_zlength_nil in H. lia.
  - destruct (256 <=? w - l); [discriminate|]. inversion P; subst. cbn [concat] in *. rewrite app_nil_r in *.
    apply cap_out. exact H.
Qed.

Ltac cap_unr E := first [ rewrite (cap_mbind_mbind_unr _ _ _ _ E) | rewrite (cap_mbind_unr _ _ _ E) ]; reflexivity.
Ltac cap_lia := rewrite ?pt_zlength_app in *; lia.

Lemma cap_conv_tail : forall OM cnt fl w p prefix body (k : Z -> M (list Z) Z) o ps r,
  tail_pieces cnt fl w p prefix body = Some (ps, r) -> zlength o <= OM -> OM < zlength o + zlength (concat ps) ->
  mbind (conv_tail (OUT_snf OM) cnt fl w p prefix body) k o = ITree.Ret Unr.
Proof.
  intros OM cnt fl w p prefix body k o ps r T H0 H. unfold conv_tail, tail_pieces in *. cbv zeta in T. cbv zeta.
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
  set (o1 := o ++ concat p1). set (o2 := o1 ++ prefix). set (o3 := o2 ++ concat p2). set (o4 := o3 ++ concat p3). set (o5 := o4 ++ body).
  assert (L1 : zlength o1 = zlength o + zlength (concat p1)) by (apply pt_zlength_app).
  assert (L2 : zlength o2 = zlength o1 + zlength prefix) by (apply pt_zlength_app).
  assert (L3 : zlength o3 = zlength o2 + zlength (concat p2)) by (apply pt_zlength_app).
  assert (L4 : zlength o4 = zlength o3 + zlength (concat p3)) by (apply pt_zlength_app).
  assert (L5 : zlength o5 = zlength o4 + zlength body) by (apply pt_zlength_app).
  destruct (Z_le_gt_dec (zlength o1) OM) as [F1|F1];
    [|cap_unr (cap_mpad OM _ _ _ _ o _ P1 H0 ltac:(lia))].
  pose proof (pt_mpad_eq OM _ _ _ _ o _ P1 ltac:(lia)) as E1. pt_m E1. fold o1.
  destruct (Z_le_gt_dec (zlength o2) OM) as [F2|F2];
    [|cap_unr (cap_out OM prefix o1 ltac:(lia))].
  pose proof (pt_out_eq OM prefix o1 ltac:(lia)) as E2. pt_m E2. fold o2.
  destruct (Z_le_gt_dec (zlength o3) OM) as [F3|F3];
    [|cap_unr (cap_mpad OM _ _ _ _ o2 _ P2 ltac:(lia) ltac:(lia))].
  pose proof (pt_mpad_eq OM _ _ _ _ o2 _ P2 ltac:(lia)) as E3. pt_m E3. fold o3.
  destruct (Z_le_gt_dec (zlength o4) OM) as [F4|F4];
    [|cap_unr (cap_mpad OM _ _ _ _ o3 _ P3 ltac:(lia) ltac:(lia))].
  pose proof (pt_mpad_eq OM _ _ _ _ o3 _ P3 ltac:(lia)) as E4. pt_m E4. fold o4.
  destruct (Z_le_gt_dec (zlength o5) OM) as [F5|F5];
    [|cap_unr (cap_out OM body o4 ltac:(lia))].
  pose proof (pt_out_eq OM body o4 ltac:(lia)) as E5. pt_m E5. fold o5.
  cap_unr (cap_mpad OM _ _ _ _ o5 _ P4 ltac:(lia) ltac:(lia)).
Qed.

Lemma cap_conv_int : forall OM cnt fl w p xp argi prefix body (k : Z -> M (list Z) Z) o ps r,
  int_pieces cnt fl w p xp argi prefix body = Some (ps, r) -> zlength o <= OM -> OM < zlength o + zlength (concat ps) ->
  mbind (conv_int (OUT_snf OM) cnt fl w p xp argi prefix body) k o = ITree.Ret Unr.
Proof.
  intros OM cnt fl w p xp argi prefix body k o ps r T H0 H. unfold conv_int, int_pieces in *.
  destruct (xp && (p <? 0))%bool; [discriminate|]. cbv zeta in T. cbv zeta.
  destruct ((argi =? 0) && (p =? 0))%bool; eapply cap_conv_tail; eassumption.
Qed.

Lemma cap_conv : forall OM cnt d a (k : Z -> M (list Z) Z) o ps r,
  conv_pieces cnt d a = Some (ps, r) -> zlength o <= OM -> OM < zlength o + zlength (concat ps) ->
  mbind (conv (OUT_snf OM) OUTFP_snf cnt d a) k o = ITree.Ret Unr.
Proof.
  intros OM cnt d a k o ps r T H0 H. unfold conv, conv_pieces in *. cbv zeta in T. cbv zeta.
  destruct a as [s|i|u|dd|l].
  - destruct (negb (d_ty d =? T_PTR)); [discriminate|].
    destruct ((d_p d <? 0) && (INT_MAX <=? zlength s))%bool; [discriminate|].
    eapply cap_conv_tail; eassumption.
  - destruct (negb (d_ty d =? T_INT)); [discriminate|].
    destruct (d_t d =? 99); [eapply cap_conv_tail; eassumption|].
    destruct (INTMAX_MAX <? i mod 2 ^ 64);
      [|destruct (negb (Z.land _ MARK_POS =? 0)); [|destruct (negb (Z.land _ PAD_POS =? 0))]];
      eapply cap_conv_int; eassumption.
  - destruct (negb (d_ty d =? T_UINT)); [discriminate|].
    destruct (d_t d =? 117); eapply cap_conv_int; eassumption.
  - discriminate.
  - destruct (negb ((d_ty d =? T_ULLONG) || (d_ty d =? T_SIZET))); [discriminate|].
    destruct (d_t d =? 117); [eapply cap_conv_int; eassumption | discriminate].
Qed.

Lemma cap_loop : forall OM fuel s args cnt o ps r,
  printf_pieces_loop fuel s args cnt = Some (ps, r) -> zlength o <= OM -> OM < zlength o + zlength (concat ps) ->
  printf_loop (OUT_snf OM) OUTFP_snf fuel s args cnt o = ITree.Ret Unr.
Proof.
  intros OM. induction fuel as [|fuel IH]; intros s args cnt o ps r P H0 H; [discriminate|].
  cbn [printf_pieces_loop] in P. cbn [printf_loop].
  destruct s as [|c s1]; [discriminate|].
  destruct (c =? 0). { inversion P; subst. cbn [concat] in H. rewrite pt_zlength_nil in H. lia. }
  cbv zeta in P. cbv zeta. remember (lit_run (c :: s1)) as lit eqn:Hlit. clear Hlit.
  destruct (skipn (Datatypes.length lit) (c :: s1)) as [|c1 s2]; [discriminate|].
  destruct ((c1 =? 37) && match s2 with [] => true | c2 :: _ => c2 =? 37 end)%bool; [discriminate|].
  pose proof (pt_zlength_nonneg o) as Ho.
  destruct (0 <? zlength lit).
  - destruct (INT_MAX - cnt <? zlength lit); [discriminate|].
    destruct (printf_pieces_loop fuel (c1 :: s2) args (cnt + zlength lit)) as [[ps' r']|] eqn:R; [|discriminate].
    inversion P; subst. clear P. rewrite pt_zlength_concat_cons in H. pose proof (pt_zlength_nonneg (concat ps')).
    destruct (Z_le_gt_dec (zlength o + zlength lit) OM) as [F1|F1];
      [|cap_unr (cap_out OM lit o ltac:(lia))].
    pose proof (pt_out_eq OM lit o F1) as E1. pt_m E1.
    apply (IH _ _ _ _ _ _ R); cap_lia.
  - destruct (parse_dir s2) as [[d s3]|].
    + destruct args as [|a args']; [discriminate|].
      destruct (conv_pieces cnt d a) as [[ps1 cnt']|] eqn:C; [|discriminate].
      destruct (printf_pieces_loop fuel s3 args' cnt') as [[ps2 r2]|] eqn:R; [|discriminate].
      inversion P; subst. clear P. rewrite pt_zlength_concat_cons, pt_zlength_concat_app, pt_zlength_nil in H.
      pose proof (pt_zlength_nonneg (concat ps1)). pose proof (pt_zlength_nonneg (concat ps2)).
      pose proof (pt_out_eq OM [] o ltac:(rewrite pt_zlength_nil; lia)) as E1. pt_m E1. rewrite app_nil_r.
      destruct (Z_le_gt_dec (zlength o + zlength (concat ps1)) OM) as [F1|F1].
      * rewrite (pt_conv _ _ _ _ _ _ _ _ C F1). apply (IH _ _ _ _ _ _ R); cap_lia.
      * exact (cap_conv _ _ _ _ _ _ _ _ C H0 ltac:(lia)).
    + destruct args as [|[ss|k|u|dd|ll] args']; try discriminate.
      destruct args' as [|a args']; [discriminate|].
      destruct (parse_star s2) as [[d s3]|]; [|discriminate].
      destruct (conv_pieces cnt (set_prec d k) a) as [[ps1 cnt']|] eqn:C; [|discriminate].
      destruct (printf_pieces_loop fuel s3 args' cnt') as [[ps2 r2]|] eqn:R; [|discriminate].
      inversion P; subst. clear P. rewrite pt_zlength_concat_cons, pt_zlength_concat_app, pt_zlength_nil in H.
      pose proof (pt_zlength_nonneg (concat ps1)). pose proof (pt_zlength_nonneg (concat ps2)).
      pose proof (pt_out_eq OM [] o ltac:(rewrite pt_zlength_nil; lia)) as E1. pt_m E1. rewrite app_nil_r.
      destruct (Z_le_gt_dec (zlength o + zlength (concat ps1)) OM) as [F1|F1].
      * rewrite (pt_conv _ _ _ _ _ _ _ _ C F1). apply (IH _ _ _ _ _ _ R); cap_lia.
      * exact (cap_conv _ _ _ _ _ _ _ _ C H0 ltac:(lia)).
Qed.

Theorem printf_model_snf_inv : forall OM fmt args ps r r' o',
  printf_pieces fmt args = Some (ps, r) -> 0 <= OM ->
  printf_model (OUT_snf OM) OUTFP_snf fmt args [] = ITree.Ret (Ok (r', o')) ->
  r' = r /\ o' = concat ps.
Proof.
  intros OM fmt args ps r r' o' P H0 E.
  destruct (Z_le_gt_dec (zlength (concat ps)) OM) as [F|F].
  - rewrite (printf_model_snf_pieces OM fmt args ps r P F) in E. injection E as E1 E2. split; congruence.
  - unfold printf_model, printf_pieces in *.
    rewrite (cap_loop OM _ _ _ _ [] _ _ P ltac:(rewrite pt_zlength_nil; lia) ltac:(rewrite pt_zlength_nil; lia)) in E.
    discriminate E.
Qed.

Theorem printf_text_inv : forall OM fmt ps args T r o,
  pf_parse fmt = Some ps -> pf_text ps args = Some T ->
  (forall v, In (AInt v) args -> -2^31 <= v < 2^31) ->
  (forall u, In (AU64 u) args -> 0 <= u) ->
  zlength T < 2147483647 -> 0 <= OM ->
  printf_model (St:=list Z) (OUT_snf OM) OUTFP_snf (fmt ++ [0]) (pf_pargs ps args) [] = ITree.Ret (Ok (r, o)) ->
  r = zlength T /\ o = T.
Proof.
  intros OM fmt ps args T r o Hp Ht HA HU HT HOM E.
  destruct (printf_text_pieces fmt ps args T Hp Ht HA HU ltac:(lia) ltac:(left; exact HT)) as (pcs & P & C).
  destruct (printf_model_snf_inv OM _ _ pcs (zlength T) r o P HOM E) as [E1 E2].
  split; [exact E1 | rewrite E2; exact C].
Qed.
