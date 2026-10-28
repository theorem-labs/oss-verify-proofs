(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require Import PropExec.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import Tac WalkLib.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import BzDefs. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzModel. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import BzTac BzInv. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzTables. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import BzContracts DecCut.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import CmpMem.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzArr BzCStream BzDState.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzDBlock.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzDBlock BzDK. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require DecCutF. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzDU10M.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzArr OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCStream OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDState OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDBlock.BzDHuff OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDBlock OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDK OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.DecCutF OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDU10M.
From Stdlib Require Lia. Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Open Scope bv_scope.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeil.
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import CpsOpen.
Section ACeilS1. Context {ACEIL__ : ACeil}.
Local Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition zl (l : list Z) : zarr := zarr_of_list l.
(* [comment removed for export] *)
Definition bvals (bs : list byte) : list Z := map (fun b : byte => bv_unsigned b) bs.
Definition wvals (ws : list word) : list Z := map (fun w : word => bv_unsigned w mod 2 ^ 32) ws.
Fixpoint hvals (bs : list byte) : list Z :=
  match bs with
  | lo :: hi :: bs' => (bv_unsigned lo + 256 * bv_unsigned hi) :: hvals bs'
  | _ => []
  end.
Definition barr (bs : list byte) : zarr := zl (bvals bs).
Definition warr (ws : list word) : zarr := zl (wvals ws).
Definition harr (bs : list byte) : zarr := zl (hvals bs).
(* [comment removed for export] *)
Definition blk_tt (k : blk) : zarr := match k with BlkF ws => warr ws | BlkS _ _ => znew end.
Definition blk_l16 (k : blk) : zarr := match k with BlkF _ => znew | BlkS l16 _ => harr l16 end.
Definition blk_l4 (k : blk) : zarr := match k with BlkF _ => znew | BlkS _ l4 => barr l4 end.

(* [comment removed for export] *)
Definition jd_of (h : dsh) (nbu : Z) (cf : list word) (dm : dsm) (r : drest) (k : blk) : dst :=
  DST (sh_state h) (bv_unsigned (sh_soch h)) (sh_solen h) (bv_unsigned (sh_brand h)) (sh_rNToGo h) (sh_rTPos h)
      (sh_bsBuff h) (sh_bsLive h) (sh_n h) (bv_unsigned (sh_small h)) (sh_cbn h) (sh_verb h) (sh_origPtr h)
      (bv_unsigned (sh_tPos h)) (bv_unsigned (sh_k0 h))
      (warr (r_unz r)) nbu (warr cf) (warr (r_cfc r)) (blk_tt k) (blk_l16 k) (blk_l4 k) false false
      (bv_unsigned (sm_sbcrc dm)) (bv_unsigned (sm_sccrc dm) mod 2 ^ 32) (bv_unsigned (sm_cbcrc dm)) (bv_unsigned (sm_cccrc dm) mod 2 ^ 32)
      (sm_nInUse dm) (barr (r_inUse r)) (barr (r_in16 r)) (barr (r_s2u r)) (barr (r_mtfa r)) (warr (r_mtfb r))
      (barr (r_sel r)) (barr (r_selm r)) (barr (r_len r)) (warr (r_lim r)) (warr (r_base r)) (warr (r_perm r)) (warr (r_minl r))
      dsv_zero.

(* [comment removed for export] *)
Definition jk_of (h : dsh) (j1 j2 : list byte) (b0 : bzs) (til tih : word) : jk :=
  JK (sh_p1 h) (sh_p2 h) (sh_p3 h) j1 j2 til tih (bs_q1 b0) (bs_tol b0) (bs_toh b0) (bs_q2 b0) (bs_bzalloc b0) (bs_bzfree b0) (bs_opaque b0).

(* [comment removed for export] *)
Definition junk_kept (P : dst -> dst) : Prop := forall jd,
  d_out_ch (P jd) = d_out_ch jd /\ d_out_len (P jd) = d_out_len jd /\ d_rand (P jd) = d_rand jd /\
  d_rNToGo (P jd) = d_rNToGo jd /\ d_rTPos (P jd) = d_rTPos jd /\ d_origPtr (P jd) = d_origPtr jd /\
  d_tPos (P jd) = d_tPos jd /\ d_k0 (P jd) = d_k0 jd /\
  d_unzftab (P jd) = d_unzftab jd /\ d_nused (P jd) = d_nused jd /\ d_cftab (P jd) = d_cftab jd /\ d_cftabCopy (P jd) = d_cftabCopy jd /\
  d_tt (P jd) = d_tt jd /\ d_ll16 (P jd) = d_ll16 jd /\ d_ll4 (P jd) = d_ll4 jd /\
  d_sbcrc (P jd) = d_sbcrc jd /\ d_sccrc (P jd) = d_sccrc jd /\ d_cbcrc (P jd) = d_cbcrc jd /\
  d_nInUse (P jd) = d_nInUse jd /\ d_inUse (P jd) = d_inUse jd /\ d_inUse16 (P jd) = d_inUse16 jd /\ d_s2u (P jd) = d_s2u jd /\
  d_mtfa (P jd) = d_mtfa jd /\ d_mtfbase (P jd) = d_mtfbase jd /\ d_sel (P jd) = d_sel jd /\ d_selMtf (P jd) = d_selMtf jd /\
  d_len (P jd) = d_len jd /\ d_limit (P jd) = d_limit jd /\ d_base (P jd) = d_base jd /\ d_perm (P jd) = d_perm jd /\
  d_minLens (P jd) = d_minLens jd.

(* [comment removed for export] *)
Lemma junk_kept_d14 : forall small v, 0 <= v < 256 -> junk_kept (fun jd => d14 jd small v).
Proof. intros small v Hv jd. pose proof (d14_fields jd small v Hv) as H. decompose [and] H. repeat split; assumption. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma zget_of_list_at_above : forall l a lo j, lo + Z.of_nat (length l) <= j -> zget (zarr_of_list_at a lo l) j = zget a j.
Proof.
  induction l as [|x l IH]; intros a lo j Hj; cbn in Hj |- *; [reflexivity|].
  rewrite IH by lia. apply zget_zset_other. lia.
Qed.

Lemma zget_zl_in : forall l k, (k < length l)%nat -> zget (zl l) (Z.of_nat k) = nth k l 0.
Proof. intros. unfold zl. apply zget_of_list. assumption. Qed.

Lemma zget_zl_out : forall l i, i < 0 \/ Z.of_nat (length l) <= i -> zget (zl l) i = 0.
Proof.
  intros l i [H|H]; unfold zl, zarr_of_list.
  - rewrite zget_of_list_at_below by lia. apply zget_znew.
  - rewrite zget_of_list_at_above by lia. apply zget_znew.
Qed.

(* [comment removed for export] *)
Lemma zl_range : forall l lo hi, lo <= 0 < hi -> (forall x, In x l -> lo <= x < hi) -> forall i, lo <= zget (zl l) i < hi.
Proof.
  intros l lo hi H0 Hl i.
  destruct (Z_lt_le_dec i 0) as [Hi|Hi]; [rewrite zget_zl_out by lia; lia|].
  destruct (Z_lt_le_dec i (Z.of_nat (length l))) as [Hi2|Hi2]; [| rewrite zget_zl_out by lia; lia].
  replace i with (Z.of_nat (Z.to_nat i)) by lia. rewrite zget_zl_in by lia.
  apply Hl. apply nth_In. lia.
Qed.

Lemma byte_rangeF : forall b : byte, 0 <= bv_unsigned b < 256.
Proof. intros b. pose proof (bv_unsigned_in_range 8 b) as H. unfold bv_modulus in H. cbn in H. lia. Qed.

Lemma bvals_range : forall bs x, In x (bvals bs) -> 0 <= x < 256.
Proof. intros bs x H. unfold bvals in H. apply in_map_iff in H. cps_destruct H as (b & <- & _). apply byte_rangeF. Qed.
Lemma wvals_range : forall ws x, In x (wvals ws) -> 0 <= x < 2 ^ 32.
Proof. intros ws x H. unfold wvals in H. apply in_map_iff in H. cps_destruct H as (w & <- & _). apply Z.mod_pos_bound. lia. Qed.
Lemma hvals_range : forall bs x, In x (hvals bs) -> 0 <= x < 2 ^ 16.
Proof.
  fix IH 1. intros [|lo [|hi bs]] x H; cbn in H; try contradiction.
  destruct H as [<-|H]; [| exact (IH bs x H)].
  pose proof (byte_rangeF lo). pose proof (byte_rangeF hi). lia.
Qed.

Lemma barr_range : forall bs i, 0 <= zget (barr bs) i < 256.
Proof. intros. unfold barr. apply zl_range; [lia| apply bvals_range]. Qed.
Lemma warr_range : forall ws i, 0 <= zget (warr ws) i < 2 ^ 32.
Proof. intros. unfold warr. apply zl_range; [lia| apply wvals_range]. Qed.
Lemma harr_range : forall bs i, 0 <= zget (harr bs) i < 2 ^ 16.
Proof. intros. unfold harr. apply zl_range; [lia| apply hvals_range]. Qed.
Lemma blk_tt_range : forall k i, 0 <= zget (blk_tt k) i < 2 ^ 32.
Proof. intros [ws|l16 l4] i; cbn [blk_tt]; [apply warr_range| rewrite zget_znew; lia]. Qed.
Lemma blk_l16_range : forall k i, 0 <= zget (blk_l16 k) i < 2 ^ 16.
Proof. intros [ws|l16 l4] i; cbn [blk_l16]; [rewrite zget_znew; lia| apply harr_range]. Qed.
Lemma blk_l4_range : forall k i, 0 <= zget (blk_l4 k) i < 256.
Proof. intros [ws|l16 l4] i; cbn [blk_l4]; [rewrite zget_znew; lia| apply barr_range]. Qed.

(* [comment removed for export] *)
Lemma bvals_length : forall bs, length (bvals bs) = length bs. Proof. intros. apply length_map. Qed.
Lemma wvals_length : forall ws, length (wvals ws) = length ws. Proof. intros. apply length_map. Qed.
Lemma hvals_length : forall bs n, length bs = (2 * n)%nat -> length (hvals bs) = n.
Proof.
  fix IH 1. intros [|lo [|hi bs]] n H; cbn in H |- *; try lia.
  rewrite (IH bs (n - 1)%nat) by lia. lia.
Qed.

(* [comment removed for export] *)
Lemma map_nth' : forall {A B} (f : A -> B) (l : list A) k da db, (k < length l)%nat -> nth k (map f l) db = f (nth k l da).
Proof. intros A B f l k da db Hk. rewrite (nth_indep _ db (f da)) by (rewrite length_map; exact Hk). apply map_nth. Qed.
Lemma bvals_nth : forall bs k, (k < length bs)%nat -> nth k (bvals bs) 0 = bv_unsigned (nth k bs (Z_to_bv 8 0)).
Proof. intros bs k Hk. unfold bvals. apply (map_nth' (fun b : byte => bv_unsigned b)). exact Hk. Qed.
Lemma wvals_nth : forall ws k, (k < length ws)%nat -> nth k (wvals ws) 0 = bv_unsigned (nth k ws (Z_to_bv 64 0)) mod 2 ^ 32.
Proof. intros ws k Hk. unfold wvals. apply (map_nth' (fun w : word => bv_unsigned w mod 2 ^ 32)). exact Hk. Qed.
Lemma hvals_nth : forall i bs, (2 * i + 1 < length bs)%nat ->
  nth i (hvals bs) 0 = bv_unsigned (nth (2 * i) bs (Z_to_bv 8 0)) + 256 * bv_unsigned (nth (2 * i + 1) bs (Z_to_bv 8 0)).
Proof.
  induction i as [|i IH]; intros [|lo [|hi bs]] H; cbn [length] in H; try lia.
  - reflexivity.
  - cbn [hvals nth]. rewrite IH by lia.
    replace (2 * S i)%nat with (S (S (2 * i))) by lia. replace (2 * S i + 1)%nat with (S (S (2 * i + 1))) by lia. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma zb8_barr : forall bs, zb8 (barr bs) (Z.of_nat (length bs)) = bs.
Proof.
  intros bs. apply nth_error_ext. intros k.
  destruct (Nat.lt_ge_cases k (length bs)) as [Hk|Hk].
  - replace k with (Z.to_nat (Z.of_nat k)) by lia. rewrite zb8_nth by lia.
    replace (Z.to_nat (Z.of_nat k)) with k by lia.
    unfold barr. rewrite zget_zl_in by (rewrite bvals_length; exact Hk). rewrite bvals_nth by exact Hk.
    rewrite Z_to_bv8_unsigned. symmetry. apply nth_error_nth'. exact Hk.
  - rewrite (proj2 (nth_error_None _ _)) by (rewrite zb8_length_nat; lia).
    rewrite (proj2 (nth_error_None _ _)) by lia. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma zh16_harr : forall bs n, length bs = (2 * n)%nat -> zh16 (harr bs) (Z.of_nat (length bs)) = bs.
Proof.
  intros bs n Hn. apply nth_error_ext. intros k.
  destruct (Nat.lt_ge_cases k (length bs)) as [Hk|Hk].
  - unfold zh16. replace k with (Z.to_nat (Z.of_nat k)) at 1 by lia. rewrite tab_nth by lia.
    rewrite (nth_error_nth' bs (Z_to_bv 8 0) Hk). f_equal.
    set (i := (k / 2)%nat).
    assert (Hi : (2 * i + 1 < length bs)%nat) by (subst i; pose proof (Nat.div_mod_eq k 2); pose proof (Nat.mod_upper_bound k 2); lia).
    replace (Z.of_nat k / 2) with (Z.of_nat i) by (subst i; rewrite Nat2Z.inj_div; reflexivity).
    unfold harr. rewrite zget_zl_in by (rewrite (hvals_length bs n Hn); lia). rewrite hvals_nth by exact Hi.
    pose proof (byte_rangeF (nth (2 * i) bs (Z_to_bv 8 0))) as R0.
    destruct (Nat.eq_dec (k mod 2) 0) as [E|E].
    + assert (E2 : Z.of_nat k mod 2 = 0) by (transitivity (Z.of_nat (k mod 2)); [rewrite Nat2Z.inj_mod; reflexivity| rewrite E; reflexivity]).
      rewrite E2, Z.mul_0_r, Z.pow_0_r, Z.div_1_r.
      rewrite Z_to_bv8_plus256. rewrite Z_to_bv8_unsigned. f_equal. subst i. pose proof (Nat.div_mod_eq k 2). lia.
    + assert (E2 : Z.of_nat k mod 2 = 1) by (transitivity (Z.of_nat (k mod 2)); [rewrite Nat2Z.inj_mod; reflexivity| pose proof (Nat.mod_upper_bound k 2); lia]).
      rewrite E2.
      rewrite Z.mul_1_r. change (2 ^ 8) with 256. rewrite div256_plus by exact R0.
      rewrite Z_to_bv8_unsigned. f_equal. subst i. pose proof (Nat.div_mod_eq k 2). pose proof (Nat.mod_upper_bound k 2). lia.
  - rewrite (proj2 (nth_error_None _ _)) by (unfold zh16; rewrite tab_length_nat; lia).
    rewrite (proj2 (nth_error_None _ _)) by lia. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma Forall2_by_nth : forall {A B} (R : A -> B -> Prop) (l1 : list A) (l2 : list B) da db,
  length l1 = length l2 -> (forall k, (k < length l1)%nat -> R (nth k l1 da) (nth k l2 db)) -> Forall2 R l1 l2.
Proof.
  intros A B R l1. induction l1 as [|x l1 IH]; intros [|y l2] da db HL H; cbn in HL; try discriminate; [constructor|].
  constructor; [exact (H 0%nat ltac:(cbn; lia))|].
  apply (IH l2 da db); [lia|]. intros k Hk. exact (H (S k) ltac:(cbn; lia)).
Qed.

Lemma warr_ext4 : forall ws, Forall2 (fun x y : word => le4 x = le4 y) ws (zw32 (warr ws) (Z.of_nat (length ws))).
Proof.
  intros ws. apply (Forall2_by_nth _ _ _ (Z_to_bv 64 0) (Z_to_bv 64 0)); [rewrite zw32_length_nat; lia|].
  intros k Hk.
  assert (E : nth_error (zw32 (warr ws) (Z.of_nat (length ws))) k = Some (Z_to_bv 64 (zget (warr ws) (Z.of_nat k)))).
  { rewrite <- (Nat2Z.id k) at 1. apply zw32_nth. lia. }
  rewrite (nth_error_nth _ _ _ E). clear E.
  unfold warr. rewrite zget_zl_in by (rewrite wvals_length; exact Hk). rewrite wvals_nth by exact Hk.
  apply le4_lit_mod32. rewrite Z.mod_mod by lia. reflexivity.
Qed.

Section WithSegsR.
  Variable segs : list Segment.
  Lemma u32arr_warr : forall m A ws n, u32arr segs m A ws -> Z.of_nat (length ws) = n -> u32arr segs m A (zw32 (warr ws) n).
  Proof. intros m A ws n U <-. eapply u32arr_ext4; [exact U| apply warr_ext4]. Qed.
  Lemma u8arr_barr : forall m A bs n, u8arr segs m A bs -> Z.of_nat (length bs) = n -> u8arr segs m A (zb8 (barr bs) n).
  Proof. intros m A bs n U <-. rewrite zb8_barr. exact U. Qed.
  Lemma u8arr_harr : forall m A bs n, u8arr segs m A bs -> Z.of_nat (length bs) = 2 * n -> u8arr segs m A (zh16 (harr bs) (2 * n)).
  Proof. intros m A bs n U E. rewrite <- E. rewrite (zh16_harr bs (Z.to_nat n)) by lia. exact U. Qed.
  Lemma rw_cells_eqv : forall m A cs cs', rw_cells segs m A cs -> cs = cs' -> rw_cells segs m A cs'.
  Proof. intros m A cs cs' H <-. exact H. Qed.
End WithSegsR.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section WithImg.
  Variable I : dimg.
  Let segs := di_segs I.

  (* [comment removed for export] *)
  Lemma raw_dvF_d : forall (d : dst) (cx : bctx) (g1 sv : word) (payload : list byte) (m : word -> option byte)
                           (h : dsh) (nbu : Z) (cf : list word) (dm : dsm) (j1 : list byte) (snb : Z) (j2 : list byte)
                           (r : drest) (b0 : bzs) (ai : Z) (til tih : word) (k : blk) (s : dstrm),
    let J := jk_of h j1 j2 b0 til tih in
    (* [comment removed for export] *)
    rw_cells segs m (b_s cx) (HEAD_CELLS h) ->
    rw_cells segs m (b_s cx + 1092) [C4 (Z_to_bv 64 nbu)] ->
    u32arr segs m (b_s cx + 1096) cf -> length cf = 257%nat ->
    rw_cells segs m (b_s cx + 3152) (MID_CELLS dm) ->
    rw_cells segs m (b_s cx + 64036) (SAVE_CELLS j1 snb j2) ->
    drest_at segs m (b_s cx) r ->
    rw_cells segs m (b_strm cx) (STRM_CELLS (bupd b0 ai til tih)) ->
    blk_at segs m cx k ->
    bytes_at segs m (b_src cx) payload ->
    rw_cells segs m (di_got I) [C8 (Z_to_bv 64 (di_stderrp I)); C8 g1; C8 (Z_to_bv 64 (di_stderrp I + 8)); C8 (Z_to_bv 64 (di_crc I)); C8 (Z_to_bv 64 (di_rnums I))] ->
    rw_cells segs m (di_stderrp I) [C8 sv] ->
    u32arr segs m (di_rnums I) rnums_words ->
    (* [comment removed for export] *)
    d_out_ch d = bv_unsigned (sh_soch h) -> d_out_len d = sh_solen h -> d_rand d = bv_unsigned (sh_brand h) ->
    d_rNToGo d = sh_rNToGo h -> d_rTPos d = sh_rTPos h -> d_origPtr d = sh_origPtr h ->
    d_tPos d = bv_unsigned (sh_tPos h) -> d_k0 d = bv_unsigned (sh_k0 h) ->
    d_unzftab d = warr (r_unz r) -> d_nused d = nbu -> d_cftab d = warr cf -> d_cftabCopy d = warr (r_cfc r) ->
    d_tt d = blk_tt k -> d_ll16 d = blk_l16 k -> d_ll4 d = blk_l4 k ->
    d_sbcrc d = bv_unsigned (sm_sbcrc dm) -> d_sccrc d = bv_unsigned (sm_sccrc dm) mod 2 ^ 32 -> d_cbcrc d = bv_unsigned (sm_cbcrc dm) ->
    d_nInUse d = sm_nInUse dm -> d_inUse d = barr (r_inUse r) -> d_inUse16 d = barr (r_in16 r) -> d_s2u d = barr (r_s2u r) ->
    d_mtfa d = barr (r_mtfa r) -> d_mtfbase d = warr (r_mtfb r) -> d_sel d = barr (r_sel r) -> d_selMtf d = barr (r_selm r) ->
    d_len d = barr (r_len r) -> d_limit d = warr (r_lim r) -> d_base d = warr (r_base r) -> d_perm d = warr (r_perm r) ->
    d_minLens d = warr (r_minl r) ->
    (* [comment removed for export] *)
    sh_strm h = b_strm cx ->
    d_state d = sh_state h -> d_bsBuff d = sh_bsBuff h -> d_bsLive d = sh_bsLive h -> d_bs100k d = sh_n h ->
    d_small d = bv_unsigned (sh_small h) -> d_blockNo d = sh_cbn h -> d_verb d = sh_verb h ->
    Z_to_bv 64 (d_cccrc d) = sm_cccrc dm -> sv_nblock (d_sv d) = snb ->
    sm_tt dm = b_tt cx -> sm_ll16 dm = b_ll16 cx -> sm_ll4 dm = b_ll4 cx ->
    (* [comment removed for export] *)
    bs_S b0 = b_s cx -> bs_src b0 = b_src cx -> bs_len b0 = b_len cx -> bs_dst b0 = b_dst cx -> bs_dlen b0 = b_dlen cx ->
    bs_av b0 = s_avail_out s -> ai = Z.of_nat (length (s_in s)) ->
    dmem I cx g1 sv payload m (dvF cx J d s) /\ jk_wf J /\ jk_static b0 J /\ drep d.
  Proof.
    intros until s. cbv zeta.
    intros HD NBU CF Lcf MID SAV DR STRM BLK PAY GOT SEV RN.
    intros Joch Jolen Jrand Jrn Jrt Jorig Jtpos Jk0 Junz Jnbu Jcf Jcfc Jtt Jl16 Jl4 Jsb Jsc Jcb Jniu Jiu Ji16 Js2u Jmtfa Jmtfb Jsel Jselm
           Jlen Jlim Jbase Jperm Jminl.
    intros Hstrm Dst Dbb Dbl Dn Dsm Dcbn Dverb Dcc Dsnb Ett El16 El4 HbS Hsrc Hlen Hdst Hdlen Hav Hai.
    (* [comment removed for export] *)
    pose proof HD as HD'. destruct HD' as [[WFh _] _]. cbn [cells_wf cell_wf] in WFh.
    cps_destruct WFh as (_ & _ & _ & Lp1 & _ & _ & Lp2 & _ & _ & _ & _ & _ & _ & Lp3 & _).
    pose proof SAV as SAV'. destruct SAV' as [[WFs _] _]. cbn [cells_wf cell_wf] in WFs. cps_destruct WFs as (Lj1 & _ & Lj2 & _).
    pose proof STRM as STRM'. destruct STRM' as [[WFb _] _]. cbn [cells_wf cell_wf bupd bs_q1 bs_q2] in WFb.
    cps_destruct WFb as (_ & _ & _ & _ & Lq1 & _ & _ & _ & _ & Lq2 & _).
    split; [| split; [| split]].
    - (* [comment removed for export] *)
      unfold dvF. apply dmem_intro; fold segs.
      + (* [comment removed for export] *)
        eapply rw_cells_eqv; [exact HD|]. unfold hd_of. cbn [j_p1 j_p2 j_p3 jk_of].
        rewrite Joch, Jolen, Jrand, Jrn, Jrt, Jorig, Jtpos, Jk0, Dst, Dbb, Dbl, Dn, Dsm, Dcbn, Dverb, <- Hstrm.
        rewrite !Z_to_bv8_unsigned, !Z_to_bv_bv_unsigned. destruct h; reflexivity.
      + (* [comment removed for export] *) rewrite Jnbu. exact NBU.
      + (* [comment removed for export] *) rewrite Jcf. apply u32arr_warr; [exact CF| rewrite Lcf; reflexivity].
      + (* [comment removed for export] *)
        eapply rw_cells_same_bytes; [| | | exact MID].
        * unfold mid_of. rewrite Jsb, Jsc, Jcb, Jniu, Dcc, Ett, El16, El4.
          cbn [cells_bytes cbytes sm_tt sm_ll16 sm_ll4 sm_sbcrc sm_sccrc sm_cbcrc sm_cccrc sm_nInUse].
          rewrite !Z_to_bv_bv_unsigned.
          rewrite <- (le4_lit_mod32 (sm_sccrc dm) (bv_unsigned (sm_sccrc dm) mod 2 ^ 32)) by (rewrite Z.mod_mod by lia; reflexivity).
          reflexivity.
        * reflexivity.
        * cbn. repeat split.
      + (* [comment removed for export] *) cbn [j_s1 j_s2 jk_of]. rewrite Dsnb. exact SAV.
      + (* [comment removed for export] *)
        unfold r_of. rewrite Junz, Jcfc, Jiu, Ji16, Js2u, Jmtfa, Jmtfb, Jsel, Jselm, Jlen, Jlim, Jbase, Jperm, Jminl.
        cps_destruct DR as ((A1&L1)&(A2&L2)&(A3&L3)&(A4&L4)&(A5&L5)&(A6&L6)&(A7&L7)&(A8&L8)&(A9&L9)&(A10&L10)&(A11&L11)&(A12&L12)&(A13&L13)&(A14&L14)).
        unfold drest_at. cbn [r_unz r_cfc r_inUse r_in16 r_s2u r_mtfa r_mtfb r_sel r_selm r_len r_lim r_base r_perm r_minl].
        rewrite !zw32_length, !zb8_length by lia.
        repeat match goal with |- _ /\ _ => split end; try reflexivity;
          first [ eapply u32arr_warr; eassumption | eapply u8arr_barr; eassumption ].
      + (* [comment removed for export] *)
        eapply rw_cells_eqv; [exact STRM|]. unfold bs_of, bupd.
        cbn [j_til j_tih j_q1 j_tol j_toh j_q2 j_bzalloc j_bzfree j_opaque jk_of
             bs_src bs_len bs_ai bs_til bs_tih bs_q1 bs_dst bs_dlen bs_av bs_tol bs_toh bs_q2 bs_S bs_bzalloc bs_bzfree bs_opaque].
        rewrite <- HbS, <- Hsrc, <- Hlen, <- Hdst, <- Hdlen, Hav, Hai. destruct b0; reflexivity.
      + (* [comment removed for export] *)
        unfold blk_of. rewrite Jtt, Jl16, Jl4. destruct k as [ws|l16 l4]; cbn [blk_at] in BLK.
        * cps_destruct BLK as (SM & U & LU). rewrite SM. cbn [Z.eqb blk_tt]. cbn [blk_at].
          split; [exact SM|]. split; [apply u32arr_warr; [exact U| exact LU] | apply zw32_length; lia].
        * cps_destruct BLK as (SM & U16 & L16 & U4 & L4). rewrite SM. cbn [Z.eqb blk_l16 blk_l4]. cbn [blk_at].
          split; [exact SM|]. split; [| split; [| split]].
          -- replace (200000 * b_n cx) with (2 * (100000 * b_n cx)) by lia. apply u8arr_harr; [exact U16| lia].
          -- unfold zh16. apply tab_length. lia.
          -- apply u8arr_barr; [exact U4| exact L4].
          -- apply zb8_length. lia.
      + exact PAY.
      + exact GOT.
      + exact SEV.
      + exact RN.
    - (* [comment removed for export] *) unfold jk_wf. cbn [j_p1 j_p2 j_p3 j_s1 j_s2 j_q1 j_q2 jk_of]. repeat split; assumption.
    - (* [comment removed for export] *) unfold jk_static. cbn [j_q1 j_q2 j_tol j_toh j_bzalloc j_bzfree j_opaque jk_of]. repeat split; reflexivity.
    - (* [comment removed for export] *) unfold drep. rewrite Jtt, Jl16, Jl4, Js2u, Jsc, Jmtfa.
      split; [apply blk_tt_range|]. split; [apply blk_l16_range|]. split; [apply blk_l4_range|].
      split; [apply barr_range|]. split; [apply Z.mod_pos_bound; lia| apply barr_range].
  Qed.

  (* [comment removed for export] *)
  Lemma raw_dvF : forall (P : dst -> dst) (cx : bctx) (g1 sv : word) (payload : list byte) (m : word -> option byte)
                         (h : dsh) (nbu : Z) (cf : list word) (dm : dsm) (j1 : list byte) (snb : Z) (j2 : list byte)
                         (r : drest) (b0 : bzs) (ai : Z) (til tih : word) (k : blk) (s : dstrm),
    let jd := jd_of h nbu cf dm r k in
    let J := jk_of h j1 j2 b0 til tih in
    junk_kept P ->
    (* [comment removed for export] *)
    rw_cells segs m (b_s cx) (HEAD_CELLS h) ->
    rw_cells segs m (b_s cx + 1092) [C4 (Z_to_bv 64 nbu)] ->
    u32arr segs m (b_s cx + 1096) cf -> length cf = 257%nat ->
    rw_cells segs m (b_s cx + 3152) (MID_CELLS dm) ->
    rw_cells segs m (b_s cx + 64036) (SAVE_CELLS j1 snb j2) ->
    drest_at segs m (b_s cx) r ->
    rw_cells segs m (b_strm cx) (STRM_CELLS (bupd b0 ai til tih)) ->
    blk_at segs m cx k ->
    bytes_at segs m (b_src cx) payload ->
    rw_cells segs m (di_got I) [C8 (Z_to_bv 64 (di_stderrp I)); C8 g1; C8 (Z_to_bv 64 (di_stderrp I + 8)); C8 (Z_to_bv 64 (di_crc I)); C8 (Z_to_bv 64 (di_rnums I))] ->
    rw_cells segs m (di_stderrp I) [C8 sv] ->
    u32arr segs m (di_rnums I) rnums_words ->
    (* [comment removed for export] *)
    sh_strm h = b_strm cx ->
    d_state (P jd) = sh_state h -> d_bsBuff (P jd) = sh_bsBuff h -> d_bsLive (P jd) = sh_bsLive h -> d_bs100k (P jd) = sh_n h ->
    d_small (P jd) = bv_unsigned (sh_small h) -> d_blockNo (P jd) = sh_cbn h -> d_verb (P jd) = sh_verb h ->
    Z_to_bv 64 (d_cccrc (P jd)) = sm_cccrc dm -> sv_nblock (d_sv (P jd)) = snb ->
    sm_tt dm = b_tt cx -> sm_ll16 dm = b_ll16 cx -> sm_ll4 dm = b_ll4 cx ->
    (* [comment removed for export] *)
    bs_S b0 = b_s cx -> bs_src b0 = b_src cx -> bs_len b0 = b_len cx -> bs_dst b0 = b_dst cx -> bs_dlen b0 = b_dlen cx ->
    bs_av b0 = s_avail_out s -> ai = Z.of_nat (length (s_in s)) ->
    dmem I cx g1 sv payload m (dvF cx J (P jd) s) /\ jk_wf J /\ jk_static b0 J /\ drep (P jd).
  Proof.
    intros until s. cbv zeta. intros JKP. intros.
    pose proof (JKP (jd_of h nbu cf dm r k)) as X.
    cbn [jd_of d_out_ch d_out_len d_rand d_rNToGo d_rTPos d_origPtr d_tPos d_k0 d_unzftab d_nused d_cftab d_cftabCopy d_tt d_ll16 d_ll4
         d_sbcrc d_sccrc d_cbcrc d_nInUse d_inUse d_inUse16 d_s2u d_mtfa d_mtfbase d_sel d_selMtf d_len d_limit d_base d_perm d_minLens] in X.
    decompose [and] X.
    eapply raw_dvF_d; eassumption.
  Qed.
End WithImg.
End ACeilS1.
