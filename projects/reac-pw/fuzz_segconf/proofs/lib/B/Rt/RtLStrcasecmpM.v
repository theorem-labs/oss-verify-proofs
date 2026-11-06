(* Modified by Theorem Labs, 2026-10: the image-B copy (fuzz_segconf.asan-ubsan, pin c3796c0b38f3, twin 80e82127e8ca) of lib/A/Rt/RtLStrcasecmpM.v, derived mechanically (derive_y.py b7b132fb12a7; every changed numeral checked against alreloc.py a5c53bb2bed4 and against image B), with its module paths changed (lib/A to lib/B) and its addresses moved to reac-pw/fuzz_segconf's ASan+UBSan build. The comments are the A file's. *)
(* reac-pw/fuzz_segconf image B, interface row 10 (strcasecmp): the list facts that connect the wrapper walk's answer
   (lib/A/Bz/A/I_strcasecmpm.v scc_res, the difference of the lowered bytes where the comparison stopped) with
   - the post of RtSeg.astrcasecmp_realizes: a0 = 0 exactly when the two strings with their NULs agree under
     RtSeg.lc, and
   - the program model's strcasecmp (lib/Spec/SegModel.v:114), which the callers in reac_segconf_parse_file compare
     with 0.
   Pure lemmas on byte lists and Z lists; no program and no runtime module. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Bz.A Require I_strcasecmpm.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Rt Require RtSeg.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require SegModel.
Import ListNotations.
Local Unset Lia Cache. Local Unset Nia Cache.
Open Scope Z_scope.

Module CM := OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Bz.A.I_strcasecmpm.
Module SM := OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec.SegModel.

(* the byte values of a byte list *)
#[local] Abbreviation ZS s := (map (fun b : byte => bv_unsigned b) s).

(* ---- the three lowerings are one function ---- *)

Lemma zlc_lc : forall c, CM.zlc c = RtSeg.lc c.
Proof. reflexivity. Qed.

Lemma lc_lower : forall c, RtSeg.lc c = SM.lower c.
Proof. intros c. unfold RtSeg.lc, SM.lower. destruct ((65 <=? c) && (c <=? 90)); lia. Qed.

Lemma lc_zero : forall c, RtSeg.lc c = 0 <-> c = 0.
Proof.
  intros c. unfold RtSeg.lc. destruct ((65 <=? c) && (c <=? 90)) eqn:E; [apply andb_prop in E as [E1 E2]|]; lia.
Qed.

Lemma u8_range : forall b : byte, 0 <= bv_unsigned b < 256.
Proof.
  intros b. pose proof (bv_unsigned_in_range 8 b) as R. unfold bv_modulus in R. change (2 ^ Z.of_N 8) with 256 in R. lia.
Qed.

Lemma u8_zero : forall b : byte, bv_unsigned b = 0 <-> b = Z_to_bv 8 0.
Proof.
  intros b. split; intros H; [apply bv_eq; rewrite H; reflexivity | subst b; reflexivity].
Qed.

(* ---- the walk stops inside both strings ---- *)

Lemma scc_idx_cstr : forall sx sy : list byte, ~ In (Z_to_bv 8 0) sx ->
  (CM.scc_idx (sx ++ [Z_to_bv 8 0]) (sy ++ [Z_to_bv 8 0]) <= length sx)%nat /\
  (CM.scc_idx (sx ++ [Z_to_bv 8 0]) (sy ++ [Z_to_bv 8 0]) <= length sy)%nat.
Proof.
  induction sx as [|x sx IH]; intros sy Nx.
  - destruct sy as [|y sy]; cbn [app CM.scc_idx]; change (bv_unsigned (Z_to_bv 8 0)) with 0;
      rewrite Z.eqb_refl, orb_true_r; cbn [length]; lia.
  - assert (Hx : bv_unsigned x <> 0) by (intros E; apply Nx; left; exact (proj1 (u8_zero _) E)).
    assert (Nx' : ~ In (Z_to_bv 8 0) sx) by (intros H; apply Nx; right; exact H).
    destruct sy as [|y sy].
    + cbn [app CM.scc_idx]. change (bv_unsigned (Z_to_bv 8 0)) with 0.
      assert (L : CM.zlc (bv_unsigned x) <> CM.zlc 0)
        by (change (CM.zlc 0) with 0; intros E; apply Hx; exact (proj1 (CM.zlc_zero _ (proj1 (u8_range x))) E)).
      rewrite (proj2 (Z.eqb_neq _ _) L). cbn [negb orb length]. lia.
    + cbn [app CM.scc_idx]. cbn [length].
      destruct (negb (CM.zlc (bv_unsigned x) =? CM.zlc (bv_unsigned y)) || (bv_unsigned x =? 0))%bool; [lia|].
      destruct (IH sy Nx'). lia.
Qed.

Lemma scc_ok_cstr : forall sx sy : list byte, ~ In (Z_to_bv 8 0) sx ->
  CM.scc_ok (sx ++ [Z_to_bv 8 0]) (sy ++ [Z_to_bv 8 0]) /\
  1 <= CM.scc_sz (sx ++ [Z_to_bv 8 0]) (sy ++ [Z_to_bv 8 0]) <= Z.of_nat (length sx) + 1 /\
  CM.scc_sz (sx ++ [Z_to_bv 8 0]) (sy ++ [Z_to_bv 8 0]) <= Z.of_nat (length sy) + 1.
Proof.
  intros sx sy Nx. destruct (scc_idx_cstr sx sy Nx) as (L1 & L2).
  unfold CM.scc_ok, CM.scc_sz. rewrite !length_app. cbn [length]. lia.
Qed.

(* ---- the answer ---- *)

Lemma scc_res_range : forall b1 b2, -256 < CM.scc_res b1 b2 < 256.
Proof.
  intros b1 b2. unfold CM.scc_res.
  destruct (nth_error b1 (CM.scc_idx b1 b2)) as [u|]; [| lia].
  destruct (nth_error b2 (CM.scc_idx b1 b2)) as [w|]; [| lia].
  pose proof (CM.zlc_range _ (u8_range u)). pose proof (CM.zlc_range _ (u8_range w)). lia.
Qed.

Lemma scc_res_step : forall x y b1 b2, CM.zlc (bv_unsigned x) = CM.zlc (bv_unsigned y) -> bv_unsigned x <> 0 ->
  CM.scc_res (x :: b1) (y :: b2) = CM.scc_res b1 b2.
Proof.
  intros x y b1 b2 HL NZ. unfold CM.scc_res. rewrite (CM.scc_idx_step x y b1 b2 HL NZ). reflexivity.
Qed.

Lemma scc_res_stop : forall x y b1 b2,
  (negb (CM.zlc (bv_unsigned x) =? CM.zlc (bv_unsigned y)) || (bv_unsigned x =? 0))%bool = true ->
  CM.scc_res (x :: b1) (y :: b2) = CM.zlc (bv_unsigned x) - CM.zlc (bv_unsigned y).
Proof. intros x y b1 b2 E. unfold CM.scc_res. cbn [CM.scc_idx]. rewrite E. reflexivity. Qed.

(* the walk answers 0 exactly when the strings with their NULs agree under lc (RtSeg.v:168's post) *)
Theorem scc_res_zero_iff : forall sx sy : list byte, ~ In (Z_to_bv 8 0) sx -> ~ In (Z_to_bv 8 0) sy ->
  (CM.scc_res (sx ++ [Z_to_bv 8 0]) (sy ++ [Z_to_bv 8 0]) = 0 <->
   map RtSeg.lc (ZS sx ++ [0]) = map RtSeg.lc (ZS sy ++ [0])).
Proof.
  change RtSeg.lc with CM.zlc.
  induction sx as [|x sx IH]; intros sy Nx Ny.
  - destruct sy as [|y sy].
    + cbn. split; intros _; reflexivity.
    + assert (Hy : bv_unsigned y <> 0) by (intros E; apply Ny; left; exact (proj1 (u8_zero _) E)).
      assert (Ly : CM.zlc (bv_unsigned y) <> 0)
        by (intros E; apply Hy; exact (proj1 (CM.zlc_zero _ (proj1 (u8_range y))) E)).
      cbn [app map].
      rewrite scc_res_stop by (change (bv_unsigned (Z_to_bv 8 0)) with 0; rewrite Z.eqb_refl, orb_true_r; reflexivity).
      change (bv_unsigned (Z_to_bv 8 0)) with 0. change (CM.zlc 0) with 0.
      split; intros H; [lia| injection H as H _; lia].
  - assert (Hx : bv_unsigned x <> 0) by (intros E; apply Nx; left; exact (proj1 (u8_zero _) E)).
    assert (Nx' : ~ In (Z_to_bv 8 0) sx) by (intros H; apply Nx; right; exact H).
    assert (Lx : CM.zlc (bv_unsigned x) <> 0)
      by (intros E; apply Hx; exact (proj1 (CM.zlc_zero _ (proj1 (u8_range x))) E)).
    destruct sy as [|y sy].
    + cbn [app map].
      rewrite scc_res_stop
        by (apply orb_true_iff; left; apply negb_true_iff, Z.eqb_neq; change (bv_unsigned (Z_to_bv 8 0)) with 0;
            change (CM.zlc 0) with 0; exact Lx).
      change (bv_unsigned (Z_to_bv 8 0)) with 0. change (CM.zlc 0) with 0.
      split; intros H; [lia| injection H as H _; lia].
    + assert (Ny' : ~ In (Z_to_bv 8 0) sy) by (intros H; apply Ny; right; exact H).
      cbn [app map].
      destruct (Z.eq_dec (CM.zlc (bv_unsigned x)) (CM.zlc (bv_unsigned y))) as [E|E].
      * rewrite (scc_res_step x y _ _ E Hx). rewrite (IH sy Nx' Ny'). rewrite E.
        split; [intros H; rewrite H; reflexivity | intros H; injection H as H; exact H].
      * rewrite scc_res_stop by (apply orb_true_iff; left; apply negb_true_iff, Z.eqb_neq; exact E).
        split; intros H; [lia| injection H as H _; contradiction].
Qed.

(* ---- the program model (lib/Spec/SegModel.v:114) ---- *)

Lemma tolower_lc : forall c, SM.tolower c = RtSeg.lc c.
Proof. intros c. rewrite SM.tolower_lower, lc_lower. reflexivity. Qed.

(* SegModel's strcasecmp of two NUL-free texts is 0 exactly when the texts with their NULs agree under lc *)
Theorem segmodel_strcasecmp_iff : forall l r : list Z, SM.nulfree l -> SM.nulfree r ->
  (SM.strcasecmp l r = 0 <-> map RtSeg.lc (l ++ [0]) = map RtSeg.lc (r ++ [0])).
Proof.
  induction l as [|a l IH]; intros r Hl Hr.
  - destruct r as [|b r].
    + cbn. split; intros _; reflexivity.
    + apply SM.nulfree_cons in Hr as [Hb _].
      pose proof (proj2 (not_iff_compat (lc_zero b)) Hb) as Lb.
      cbn [SM.strcasecmp SM.hd0 app map]. rewrite !tolower_lc. change (RtSeg.lc 0) with 0.
      split; intros H; [lia| injection H as H _; lia].
  - apply SM.nulfree_cons in Hl as [Ha Hl].
    pose proof (proj2 (not_iff_compat (lc_zero a)) Ha) as La.
    destruct r as [|b r].
    + cbn [SM.strcasecmp SM.hd0 app map]. rewrite !tolower_lc. change (RtSeg.lc 0) with 0.
      split; intros H; [lia| injection H as H _; lia].
    + apply SM.nulfree_cons in Hr as [Hb Hr].
      cbn [SM.strcasecmp app map]. rewrite !tolower_lc.
      rewrite (proj2 (Z.eqb_neq a 0) Ha), (proj2 (Z.eqb_neq b 0) Hb). cbn [negb andb].
      destruct (Z.eq_dec (RtSeg.lc a) (RtSeg.lc b)) as [E|E].
      * replace ((a =? b) || (RtSeg.lc a =? RtSeg.lc b))%bool with true
          by (rewrite E, Z.eqb_refl, orb_true_r; reflexivity).
        rewrite (IH r Hl Hr), E.
        split; [intros H; rewrite H; reflexivity | intros H; injection H as H; exact H].
      * replace ((a =? b) || (RtSeg.lc a =? RtSeg.lc b))%bool with false
          by (symmetry; apply orb_false_iff; split; apply Z.eqb_neq; [intros ->; contradiction| exact E]).
        split; intros H; [lia| injection H as H _; contradiction].
Qed.

(* the post of RtSeg.astrcasecmp_realizes read as the program model's answer *)
Corollary casecmp_post_model : forall sx sy : list byte, ~ In (Z_to_bv 8 0) sx -> ~ In (Z_to_bv 8 0) sy ->
  (map RtSeg.lc (ZS sx ++ [0]) = map RtSeg.lc (ZS sy ++ [0]) <-> SM.strcasecmp (ZS sx) (ZS sy) = 0).
Proof.
  intros sx sy Nx Ny.
  assert (NF : forall s : list byte, ~ In (Z_to_bv 8 0) s -> SM.nulfree (ZS s)).
  { intros s Ns Hin. apply in_map_iff in Hin as (b & Hb & Hin). apply Ns. rewrite <- (proj1 (u8_zero b) Hb). exact Hin. }
  symmetry. apply segmodel_strcasecmp_iff; apply NF; assumption.
Qed.
