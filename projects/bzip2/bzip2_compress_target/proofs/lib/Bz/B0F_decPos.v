(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require Import PropExec.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import Tac WalkLib SegsA0 SegsB0.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzDefs BzModel BzTac BzInv BzTables BzContracts AsanKit DecCutB B0F_decV.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzArr DecTac2.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzArr.
From Stdlib Require Lia. Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Open Scope Z_scope.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeil.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import CpsOpen.

(* [comment removed for export] *)
Definition pos_agA (pb : list byte) (pos : zarr) (n : Z) : Prop :=
  length pb = 6%nat /\ forall k, (0 <= k < n)%Z -> nth_error pb (Z.to_nat k) = Some (Z_to_bv 8 (zget pos k)).
(* [comment removed for export] *)
Definition pos_okz (pos : zarr) (ng : Z) : Prop := forall k, (0 <= k < ng)%Z -> (0 <= zget pos k < ng)%Z.

Lemma pos_agA_set : forall pb pos n k x n', pos_agA pb pos n -> (0 <= k < 6)%Z -> (n' <= 6)%Z ->
  (forall j, 0 <= j < n' -> j <> k -> j < n)%Z ->
  pos_agA (upd pb (Z.to_nat k) (Z_to_bv 8 x)) (zset pos k x) n'.
Proof.
  intros pb pos n k x n' [L P] Hk Hn' Hj. split; [rewrite upd_length; exact L|].
  intros j Hjr. rewrite zget_zset. destruct (Z.eqb_spec j k) as [->|NE].
  - apply nth_error_upd_same. rewrite L. lia.
  - rewrite nth_error_upd_other by lia. apply P. specialize (Hj j Hjr NE). lia.
Qed.
Lemma pos_okz_init : forall pos v, (forall k, 0 <= k < v -> zget pos k = k)%Z -> pos_okz pos v.
Proof. intros pos v H k Hk. rewrite H by lia. lia. Qed.
Lemma pos_okz_set : forall pos ng k x, pos_okz pos ng -> (0 <= x < ng)%Z -> pos_okz (zset pos k x) ng.
Proof. intros pos ng k x P Hx j Hj. rewrite zget_zset. destruct (Z.eqb_spec j k); [lia| apply P; lia]. Qed.
Lemma pos_agA_nil : forall pb pos, length pb = 6%nat -> pos_agA pb pos 0.
Proof. intros pb pos L. split; [exact L|]. intros k Hk. exfalso. lia. Qed.

(* [comment removed for export] *)
Lemma pos_sh_addr : forall X SHX v, sanchor X SHX -> 0 <= v < 8 -> (X + 32 + v) / 8 + 2147450880 = SHX + 4.
Proof. intros X SHX v [M E] Hv. subst SHX. Z.div_mod_to_equations. lia. Qed.
Lemma pos_land7 : forall X SHX v, sanchor X SHX -> 0 <= v < 8 -> Z.land (X + 32 + v) 7 = v.
Proof.
  intros X SHX v [M _] Hv. change 7 with (Z.ones 3). rewrite Z.land_ones by lia. change (2 ^ 3) with 8.
  Z.div_mod_to_equations. lia.
Qed.

(* [comment removed for export] *)
Lemma sxb_6 : sxb (Z_to_bv 8 6) = Z_to_bv 64 6. Proof. reflexivity. Qed.

(* [comment removed for export] *)
Lemma land255_small : forall v, (0 <= v < 256)%Z -> Z.land v 255 = v.
Proof. intros v Hv. change 255%Z with (Z.ones 8). rewrite Z.land_ones by lia. apply Z.mod_small. lia. Qed.
(* [comment removed for export] *)
Lemma land_w32 : forall w, (1 <= w < 4294967296)%Z -> Z.land (w + 4294967295) 4294967295 = (w - 1)%Z.
Proof.
  intros w Hw. change 4294967295%Z with (Z.ones 32) at 2. rewrite Z.land_ones by lia.
  replace (w + 4294967295)%Z with (w - 1 + 1 * 2 ^ 32)%Z by (cbn; lia).
  rewrite Z_mod_plus_full. apply Z.mod_small. lia.
Qed.

Section ACeilS1. Context {ACEIL__ : ACeil}.

(* [comment removed for export] *)
Definition FSH (b : byte) : list cell := [C1 df1b; C1 df1b; C1 df1b; C1 df1b; C1 b; C1 df3b; C1 df3b; C1 df3b].

(* [comment removed for export] *)
Definition aframe_pos (A : act14) (m : word -> option byte) : Prop :=
  exists (zt : word) (ng : nat) (jg j24 j38 : list byte) (fl : Z),
    a_P A + 760 + Z.of_nat ng + 104 = a_usp A /\ (ng = 0 \/ ng = 16)%nat /\
    ro_cells b0segs m (a_fb A + 56) [C8 (Z_to_bv 64 fl)] /\
    rw_cells b0segs m (a_P A + 128) (FM_CELLS A zt) /\
    rw_cells b0segs m (a_P A + 760) (CB ng jg :: FT_REGS A) /\
    rw_cells b0segs m (a_fb A) [C8 (Z_to_bv 64 1102416563); C8 (Z_to_bv 64 132751); C8 (Z_to_bv 64 693392); CB 8 j24] /\
    rw_cells b0segs m (a_fb A + 38) [CB 18 j38].

Lemma aframe_pos_open : forall A m, aframe A m ->
  exists pb, length pb = 6%nat /\ aframe_pos A m /\ u8arr b0segs m (a_fb A + 32) pb /\ rw_cells b0segs m (a_shf A) (FSH df8b).
Proof.
  intros A m (zt & ng & jg & j24 & pos & j38 & fl & GEO & NG & FLP & FRM & FRT & FF & FS).
  DecTac2.rw_split3 FF 4%nat FFm FFc.
  exists pos. split; [exact (DecTac2.rw_cells_CB_length b0segs m _ [] 6%nat pos [] FFm)|].
  split.
  - exists zt, ng, jg, j24, j38, fl. split; [exact GEO|]. split; [exact NG|]. split; [exact FLP|]. split; [exact FRM|]. split; [exact FRT|]. split; [exact FF|].
    lazymatch type of FFc with rw_cells _ _ ?a _ => replace (a_fb A + 38) with a by lia end. exact FFc.
  - split; [| exact FS]. apply (u8arr_of_rw_cells b0segs m _ 6 pos).
    lazymatch type of FFm with rw_cells _ _ ?a _ => replace (a_fb A + 32) with a by lia end. exact FFm.
Qed.

Lemma aframe_pos_close : forall A m pb, aframe_pos A m -> u8arr b0segs m (a_fb A + 32) pb -> length pb = 6%nat ->
  rw_cells b0segs m (a_shf A) (FSH df8b) -> aframe A m.
Proof.
  intros A m pb (zt & ng & jg & j24 & j38 & fl & GEO & NG & FLP & FRM & FRT & FF & FFc) POS LPB FS.
  apply rw_cells_of_u8arr in POS. rewrite LPB in POS. rename POS into FFm.
  DecTac2.rw_join3 FF FFm FFc.
  exists zt, ng, jg, j24, pb, j38, fl. split; [exact GEO|]. split; [exact NG|]. split; [exact FLP|]. split; [exact FRM|]. split; [exact FRT|]. split; [exact FF| exact FS].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma aframe_pos_tr : forall A W m m', aframe_pos A m -> munch W m m' -> wmono b0segs m m' ->
  disjoint_from W (a_P A + 128) 216 -> disjoint_from W (a_P A + 760) 120 -> disjoint_from W (a_fb A) 32 -> disjoint_from W (a_fb A + 38) 26 ->
  aframe_pos A m'.
Proof.
  intros A W m m' (zt & ng & jg & j24 & j38 & fl & GEO & NG & FLP & FRM & FRT & FF & FFc) MU WM D1 D2 D3 D4.
  assert (D4a : disjoint_from W (a_fb A + 38) 18) by (apply (disjoint_from_le W _ 26); [exact D4| lia]).
  assert (D4b : disjoint_from W (a_fb A + 56) 8).
  { clear - D4. induction W as [|[lo hi] W IH]; cbn in *; [exact I|]. destruct D4 as [H1 H2]. split; [lia| exact (IH H2)]. }
  exists zt, ng, jg, j24, j38, fl. split; [exact GEO|]. split; [exact NG|].
  split; [exact (ro_cells_transport b0segs W m m' _ _ FLP MU D4b)|].
  split; [exact (rw_cells_transport b0segs W m m' _ _ FRM MU WM D1)|].
  split. { apply (rw_cells_transport b0segs W m m' _ _ FRT MU WM). apply (disjoint_from_le W _ 120); [exact D2|].
           cbn [cells_size csize FT_REGS Nat.add]. destruct NG as [-> | ->]; cbn; lia. }
  split; [exact (rw_cells_transport b0segs W m m' _ _ FF MU WM D3)|].
  exact (rw_cells_transport b0segs W m m' _ _ FFc MU WM D4a).
Qed.
End ACeilS1.
