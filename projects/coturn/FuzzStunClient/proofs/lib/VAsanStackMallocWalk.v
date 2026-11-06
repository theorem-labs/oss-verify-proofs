(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.coturn.FuzzStunClient.images Require Import Asan.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import PropExec CatExec CatSim SeqExec MmapSim StepTac Hoare RefEnframeArith.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Asan Require Import AsanRegionPoisoned.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib Require Import VAsanTls_code VAsanStackMalloc_code VAsanTlsWalk.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import LiaKeep.  (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import WalkFastV.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import WalkFastVK.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import WalkFastVS.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Ltac OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common.WalkTac.gres ::= gres_fast.
#[local] Ltac OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common.WalkTac.vnorm ::= vnorm_fast.
#[local] Ltac OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common.StepTac.step_simpl ::= step_simpl_fast.
#[local] Ltac OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common.RefMemcpyLib.not_kept ::= not_kept_fast.
#[local] Ltac OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common.StartupTac.in_list ::= in_list_fast.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Asan Require Import AsanWalkFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Ltac OSSVerify.Proofs.coturn.FuzzStunClient.lib.Asan.AsanRegionPoisoned.gr ::= gr_fast.
(* [comment removed for export] *)
#[local] Existing Instance PropExec.fx0.  (* [comment removed for export] *)
Import ListNotations.
Open Scope bv_scope.

Abbreviation SEGS := Asan.M.loaded_segments.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma zbv_mod : forall z, Z_to_bv 64 (z mod 2 ^ 64) = Z_to_bv 64 z.
Proof. intros z. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64)%Z. apply Z.mod_mod. lia. Qed.
Lemma v_addi_any : forall z i, v_addi (Z_to_bv 64 z) i = Z_to_bv 64 (z + i).
Proof.
  intros z i. unfold v_addi. rewrite Z_to_bv_unsigned. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap.
  change (bv_modulus 64) with (2 ^ 64)%Z. rewrite Zplus_mod_idemp_l. reflexivity.
Qed.
Lemma v_add_any : forall a b, v_add (Z_to_bv 64 a) (Z_to_bv 64 b) = Z_to_bv 64 (a + b).
Proof.
  intros a b. unfold v_add. rewrite !Z_to_bv_unsigned. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap.
  change (bv_modulus 64) with (2 ^ 64)%Z. rewrite <- Z.add_mod by lia. reflexivity.
Qed.
Lemma land_ones_mod : forall z k, (0 <= k)%Z -> Z.land z (2 ^ k - 1) = (z mod 2 ^ k)%Z.
Proof. intros z k Hk. rewrite <- Z.land_ones by exact Hk. unfold Z.ones. rewrite Z.shiftl_1_l. reflexivity. Qed.
Lemma v_and_mask : forall z k, (0 <= k <= 64)%Z -> v_and (Z_to_bv 64 z) (Z_to_bv 64 (2 ^ k - 1)) = Z_to_bv 64 (z mod 2 ^ k).
Proof.
  intros z k Hk. unfold v_and. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64)%Z.
  assert (Hp : (0 < 2 ^ k)%Z) by (apply Z.pow_pos_nonneg; lia).
  assert (Hle : (2 ^ k <= 2 ^ 64)%Z) by (apply Z.pow_le_mono_r; lia).
  rewrite (Z.mod_small (2 ^ k - 1)) by lia. rewrite land_ones_mod by lia.
  apply (f_equal (Z_to_bv 64)).
  destruct (Z.le_exists_sub k 64 ltac:(lia)) as (e & E & He). rewrite E, Z.pow_add_r by lia.
  apply Z.mod_mod_divide. exists (2 ^ e)%Z. reflexivity.
Qed.
Lemma v_addiw_small : forall z i, (- 2 ^ 31 <= z + i < 2 ^ 31)%Z -> (0 <= z < 2 ^ 64)%Z ->
  v_addiw (Z_to_bv 64 z) i = Z_to_bv 64 (z + i).
Proof.
  intros z i Hr Hz. unfold v_addiw. rewrite zbv_u by exact Hz. apply (f_equal (Z_to_bv 64)).
  apply bv_swrap_small. change (bv_half_modulus 32) with (2 ^ 31)%Z. lia.
Qed.
Lemma c_eq_zbv0 : forall z, (0 <= z < 2 ^ 64)%Z -> c_eq (Z_to_bv 64 z) (Z_to_bv 64 0) = (z =? 0)%Z.
Proof. intros z Hz. apply c_eq_zbv; lia. Qed.
Lemma c_lts_pos_ft : forall z, (0 < z < 2 ^ 63)%Z -> c_lts (Z_to_bv 64 0) (Z_to_bv 64 z) = true.
Proof. intros z Hz. rewrite c_lts_zbv by lia. apply Z.ltb_lt. lia. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma mem_to_shadow_5e918 : forall rom regs m (p : Z) (ra : word),
  cells m -> (0 <= p)%Z -> in_mem p ->
  getr regs 10 = Z_to_bv 64 p -> getr regs 1 = ra -> ret_ok ra ->
  exists regs',
    msteps SEGS (mkst regs (0x3f510 : word) m rom) (mkst regs' ra m rom)
    /\ getr regs' 10 = Z_to_bv 64 (SB + p / 8)
    /\ (forall r, m2s_clob r = false -> getr regs' r = getr regs r).
Proof.
  intros rom regs m p ra (C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8) Hp Hin H10 H1 Hret.
  unfold in_mem, kLowEnd, kHighBeg, kHighEnd in Hin.
  assert (Hp64 : (p < 2 ^ 64)%Z) by lia. pose proof SB_val as HSB.
  pose proof (Z.div_mod p 8 ltac:(lia)) as Hdm. pose proof (Z.mod_pos_bound p 8 ltac:(lia)) as Hmb.
  destruct (Z.le_gt_cases p 0x7fff7fff) as [Hlow | Hhigh].
  - eexists. split; [|split].
    + mstep ltac:(eapply (step_auipc_at _ _ _ _ _ _ _ _ (Z_to_bv 64 0xab510) F_3f510 eq_refl D_3f510);
                   [reflexivity | apply bv_eq; vm_compute; reflexivity]).
      mld F_3f514 D_3f514 0xb35f8%Z C1 H10.
      mld F_3f518 D_3f518 SB C2 H10.
      mstep ltac:(exact (step_addi _ _ _ _ _ _ _ _ _ F_3f51c eq_refl D_3f51c)). gr. zn.
      mstep ltac:(exact (step_sltu _ _ _ _ _ _ _ _ _ F_3f520 eq_refl D_3f520)). gr.
      mstep ltac:(exact (step_addi _ _ _ _ _ _ _ _ _ F_3f524 eq_refl D_3f524)). gr.
      mstep ltac:(exact (step_and _ _ _ _ _ _ _ _ _ F_3f528 eq_refl D_3f528)). gr.
      rewrite k_low_val. unfold kLowEnd.
      mstep ltac:(eapply (step_bgeu_tk _ _ _ _ _ _ _ _ _ F_3f52c eq_refl D_3f52c); gr; rewrite ?H10; br_lt).
      mstep ltac:(exact (PropExec.step_srli _ _ _ _ _ _ _ _ _ F_3f570 eq_refl D_3f570)). gr. rewrite H10, (v_srli_3 p) by lia.
      mstep ltac:(exact (step_add _ _ _ _ _ _ _ _ _ F_3f574 eq_refl D_3f574)). gr. rewrite v_add_zbv by lia.
      eapply mst_step; [reflexivity | eapply (step_jalr_x0 _ _ _ _ _ _ _ _ ra F_3f578 eq_refl D_3f578); gr; exact H1 |].
      imm_norm. rewrite Hret. apply mst_refl.
    + gr. apply (f_equal (Z_to_bv 64)). lia.
    + intros r Hr. unfold m2s_clob in Hr.
      repeat (rewrite getr_other by (intros ->; cbn in Hr; discriminate)). reflexivity.
  - eexists. split; [|split].
    + mstep ltac:(eapply (step_auipc_at _ _ _ _ _ _ _ _ (Z_to_bv 64 0xab510) F_3f510 eq_refl D_3f510);
                   [reflexivity | apply bv_eq; vm_compute; reflexivity]).
      mld F_3f514 D_3f514 0xb35f8%Z C1 H10.
      mld F_3f518 D_3f518 SB C2 H10.
      mstep ltac:(exact (step_addi _ _ _ _ _ _ _ _ _ F_3f51c eq_refl D_3f51c)). gr. zn.
      mstep ltac:(exact (step_sltu _ _ _ _ _ _ _ _ _ F_3f520 eq_refl D_3f520)). gr.
      mstep ltac:(exact (step_addi _ _ _ _ _ _ _ _ _ F_3f524 eq_refl D_3f524)). gr.
      mstep ltac:(exact (step_and _ _ _ _ _ _ _ _ _ F_3f528 eq_refl D_3f528)). gr.
      rewrite k_low_val. unfold kLowEnd.
      mstep ltac:(eapply (step_bgeu_ft _ _ _ _ _ _ _ _ _ F_3f52c eq_refl D_3f52c); gr; rewrite ?H10; br_lt).
      mstep ltac:(eapply (step_auipc_at _ _ _ _ _ _ _ _ (Z_to_bv 64 0xab530) F_3f530 eq_refl D_3f530);
                   [reflexivity | apply bv_eq; vm_compute; reflexivity]).
      mld F_3f534 D_3f534 0xb42e8%Z C3 H10.
      mstep ltac:(eapply (step_auipc_at _ _ _ _ _ _ _ _ (Z_to_bv 64 0xab538) F_3f538 eq_refl D_3f538);
                   [reflexivity | apply bv_eq; vm_compute; reflexivity]).
      mld F_3f53c D_3f53c 0xb42f0%Z C5 H10.
      mld F_3f540 D_3f540 0%Z C4 H10.
      mld F_3f544 D_3f544 0%Z C6 H10.
      mstep ltac:(exact (step_addi _ _ _ _ _ _ _ _ _ F_3f548 eq_refl D_3f548)). gr. rewrite k_m1_val.
      mstep ltac:(eapply (step_bgeu_tk _ _ _ _ _ _ _ _ _ F_3f54c eq_refl D_3f54c); gr; rewrite ?H10; br_lt).
      mstep ltac:(eapply (step_auipc_at _ _ _ _ _ _ _ _ (Z_to_bv 64 0xab554) F_3f554 eq_refl D_3f554);
                   [reflexivity | apply bv_eq; vm_compute; reflexivity]).
      mld F_3f558 D_3f558 0xb42e0%Z C7 H10.
      mld F_3f55c D_3f55c kHighEnd C8 H10.
      mstep ltac:(exact (PropExec.step_srli _ _ _ _ _ _ _ _ _ F_3f560 eq_refl D_3f560)). gr.
      mstep ltac:(exact (step_add _ _ _ _ _ _ _ _ _ F_3f564 eq_refl D_3f564)). gr. rewrite k_hse_val. unfold kHighBeg.
      replace (17594333495296 - 1)%Z with 17594333495295%Z by reflexivity.
      mstep ltac:(eapply (step_bltu_ft _ _ _ _ _ _ _ _ _ F_3f568 eq_refl D_3f568); gr; rewrite ?H10; unfold kHighEnd; br_lt).
      mstep ltac:(eapply (step_bgeu_ft _ _ _ _ _ _ _ _ _ F_3f56c eq_refl D_3f56c); gr; rewrite ?H10; br_lt).
      mstep ltac:(exact (PropExec.step_srli _ _ _ _ _ _ _ _ _ F_3f570 eq_refl D_3f570)). gr. rewrite H10, (v_srli_3 p) by lia.
      mstep ltac:(exact (step_add _ _ _ _ _ _ _ _ _ F_3f574 eq_refl D_3f574)). gr. rewrite v_add_zbv by lia.
      eapply mst_step; [reflexivity | eapply (step_jalr_x0 _ _ _ _ _ _ _ _ ra F_3f578 eq_refl D_3f578); gr; exact H1 |].
      imm_norm. rewrite Hret. apply mst_refl.
    + gr. apply (f_equal (Z_to_bv 64)). lia.
    + intros r Hr. unfold m2s_clob in Hr.
      repeat (rewrite getr_other by (intros ->; cbn in Hr; discriminate)). reflexivity.
Qed.

Lemma v_slli_zbv : forall z k, (0 <= z)%Z -> (0 <= k)%Z -> (z * 2 ^ k < 2 ^ 64)%Z -> v_slli (Z_to_bv 64 z) k = Z_to_bv 64 (z * 2 ^ k).
Proof.
  intros z k Hz Hk Hzk. unfold v_slli. assert (0 < 2 ^ k)%Z by (apply Z.pow_pos_nonneg; lia).
  rewrite zbv_u by nia. rewrite Z.shiftl_mul_pow2 by lia. reflexivity.
Qed.
Lemma zbv_self' : forall (x : word), x = Z_to_bv 64 (bv_unsigned x). Proof. intros x. symmetry. apply zbv_self. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition SM_FRAME : Z := 208.           (* [comment removed for export] *)
Definition FS_AREA : Z := 36864 + 5 * 2 ^ 20. (* [comment removed for export] *)

(* [comment removed for export] *)
Definition fs_band (fs : Z) : Prop := (fs + FS_AREA <= 0x7fff7000 \/ 0x10007fff8000 <= fs)%Z.

Lemma in_mem_frame (fs a sz : Z) : fs_band fs -> (0 <= fs)%Z -> (fs <= a)%Z -> (a + sz <= fs + FS_AREA)%Z -> (fs + FS_AREA <= 2 ^ 47)%Z ->
  (0 < sz)%Z -> in_mem a.
Proof. unfold fs_band, in_mem, kLowEnd, kHighBeg, kHighEnd, FS_AREA. lia. Qed.

(* [comment removed for export] *)
Record smH (mem : word -> option byte) (usp fs ctx thr db beg : Z) (a2v a3v : word) : Prop := {
  s_usp   : (0x10007fff8000 + SM_FRAME <= usp)%Z /\ (usp + 16 <= 2 ^ 64)%Z;
  s_stk   : forall a, (usp - SM_FRAME <= a < usp)%Z -> store_ok SEGS mem (Z_to_bv 64 a) 1 = true;
  (* [comment removed for export] *)
  s_tcells: tcells mem;
  s_ctx   : cell mem 0x607998 ctx;
  s_ctxb  : (0 < ctx)%Z /\ (ctx + 160 <= 2 ^ 64)%Z;
  s_thr   : cell mem (ctx + 152) thr;
  s_thrb  : (0 < thr)%Z /\ (thr + 64 <= 2 ^ 64)%Z;
  s_a2    : rdn SEGS mem (Z_to_bv 64 (thr + 48)) 8 = Some (word_to_le_bytes 8 a2v);
  s_a3    : rdn SEGS mem (Z_to_bv 64 (thr + 56)) 8 = Some (word_to_le_bytes 8 a3v);
  s_db    : cell mem (TP + 8) db;
  s_dbb   : (0 < db)%Z /\ (db + 32 <= 2 ^ 64)%Z;
  s_beg   : cell mem (db + 24) beg;
  s_begb  : (0 < beg < 2 ^ 64)%Z;
  s_ap1   : (ctx + 160 <= usp - SM_FRAME \/ usp <= ctx + 152)%Z;
  s_ap2   : (thr + 64 <= usp - SM_FRAME \/ usp <= thr + 48)%Z;
  s_ap3   : (db + 32 <= usp - SM_FRAME \/ usp <= db + 24)%Z;
  (* [comment removed for export] *)
  s_cells : cells mem;
  (* [comment removed for export] *)
  s_fs    : cell mem TP fs;
  (* [comment removed for export] *)
  s_fsb   : (0x608000 <= fs)%Z /\ fs_band fs /\ (fs + FS_AREA <= 2 ^ 47)%Z /\ (fs mod 4096 = 0)%Z;
  s_fsap  : (fs + FS_AREA <= usp - SM_FRAME \/ usp <= fs)%Z;
  s_gc    : rdn SEGS mem (Z_to_bv 64 (fs + 96)) 1 = Some [Z_to_bv 8 0];
  s_ssl   : cell mem (fs + 88) 20
}.

(* [comment removed for export] *)
Definition sm_clob (r : reg) : bool :=
  (bv_eqb r 5 || bv_eqb r 10 || bv_eqb r 11 || bv_eqb r 12 || bv_eqb r 13 || bv_eqb r 14
   || bv_eqb r 15 || bv_eqb r 16 || bv_eqb r 17)%bool.

Section SM.
  Variables (mem rom : word -> option byte) (usp fs ctx thr db beg : Z) (a2v a3v : word).
  Hypothesis H : smH mem usp fs ctx thr db beg a2v a3v.
  Variable regs0 : bvmap 5 word.
  Variable ra : word.
  Hypothesis Hret : ret_ok ra.
  Hypothesis H01 : getr regs0 1 = ra.
  Hypothesis H02 : getr regs0 2 = Z_to_bv 64 usp.
  Hypothesis H04 : getr regs0 4 = Z_to_bv 64 TP.

  #[using="mem fs ctx thr db beg a2v a3v H"] Lemma HU : (0x10007fff8000 + 208 <= usp)%Z /\ (usp + 16 <= 2 ^ 64)%Z.
  Proof. pose proof (s_usp _ _ _ _ _ _ _ _ _ H). unfold SM_FRAME in *. lia. Qed.
  #[using="mem rom ctx thr db beg a2v a3v H"] Lemma HF : (0x608000 <= fs)%Z /\ (fs + FS_AREA <= 2 ^ 47)%Z /\ (fs mod 4096 = 0)%Z /\ (fs + FS_AREA <= usp - 208 \/ usp <= fs)%Z.
  Proof. pose proof (s_fsb _ _ _ _ _ _ _ _ _ H). pose proof (s_fsap _ _ _ _ _ _ _ _ _ H). unfold SM_FRAME in *. tauto. Qed.
  #[using="mem usp ctx thr db beg a2v a3v H"] Lemma HFB : fs_band fs.
  Proof. exact (proj1 (proj2 (s_fsb _ _ _ _ _ _ _ _ _ H))). Qed.

  Ltac len8 := rewrite ?length_N_to_le_bytes; change (Z.of_nat 8) with 8%Z; change (Z.of_nat 1) with 1%Z.

  (* [comment removed for export] *)
  Definition sfr (m : word -> option byte) : Prop :=
       (forall x : word, (bv_unsigned x < usp - SM_FRAME \/ usp <= bv_unsigned x)%Z -> m x = mem x)
    /\ (forall x, mem x <> None -> m x <> None)
    /\ (forall x, store_ok SEGS mem x 1 = true -> store_ok SEGS m x 1 = true).

  #[using="fs ctx thr db beg a2v a3v H"] Lemma rdn_sfr : forall m (a : Z) k, sfr m -> (0 <= a < 2 ^ 64)%Z -> (a + Z.of_nat k <= 2 ^ 64)%Z ->
    (a + Z.of_nat k <= usp - SM_FRAME \/ usp <= a)%Z ->
    rdn SEGS m (Z_to_bv 64 a) k = rdn SEGS mem (Z_to_bv 64 a) k.
  Proof.
    intros m a k (F1 & _) Ha Hk Hap. pose proof HU. apply rdn_ext; [rewrite zbv_u by lia; lia|].
    intros x Hx. rewrite zbv_u in Hx by lia. apply F1. unfold SM_FRAME in *. lia.
  Qed.

  (* [comment removed for export] *)
  Definition m1 : word -> option byte :=
    let w (o : Z) (v : word) (m : word -> option byte) := wbytes m (Z_to_bv 64 (usp - o)) (word_to_le_bytes 8 v) in
    w 32%Z (getr regs0 18) (w 24%Z (getr regs0 9) (w 16%Z (getr regs0 8) (w 8%Z ra mem))).

  #[using="fs ctx thr db beg a2v a3v H"] Lemma m1_out : forall x : word, (bv_unsigned x < usp - 32 \/ usp <= bv_unsigned x)%Z -> m1 x = mem x.
  Proof.
    intros x Hx. pose proof HU. unfold m1. destruct Hx as [Hx|Hx].
    - rewrite !wbytes_below; try reflexivity; len8; rewrite ?zbv_u by lia; lia.
    - rewrite !wbytes_above; try reflexivity; len8; rewrite ?zbv_u by lia; lia.
  Qed.
  #[using="fs ctx thr db beg a2v a3v H"] Lemma m1_sfr : sfr m1.
  Proof.
    split; [|split].
    - intros x Hx. apply m1_out. unfold SM_FRAME in Hx. lia.
    - intros x Hx. unfold m1. repeat apply wbytes_keep. exact Hx.
    - intros x Hx. unfold m1. repeat apply store_ok1_wbytes. exact Hx.
  Qed.
  Ltac rd_side := len8; rewrite !zbv_u by lia; lia.
  Ltac rd_slot := pose proof HU; unfold m1;
    repeat (first [ apply rdn_wbytes_hit8; rewrite zbv_u by lia; lia
                  | rewrite rdn_wbytes_out; [| rd_side | rd_side | rd_side] ]).
  #[using="fs ctx thr db beg a2v a3v H"] Lemma rd1_8 : rdn SEGS m1 (Z_to_bv 64 (usp - 8)) 8 = Some (word_to_le_bytes 8 ra). Proof. rd_slot. Qed.
  #[using="fs ctx thr db beg a2v a3v H"] Lemma rd1_16 : rdn SEGS m1 (Z_to_bv 64 (usp - 16)) 8 = Some (word_to_le_bytes 8 (getr regs0 8)). Proof. rd_slot. Qed.
  #[using="fs ctx thr db beg a2v a3v H"] Lemma rd1_24 : rdn SEGS m1 (Z_to_bv 64 (usp - 24)) 8 = Some (word_to_le_bytes 8 (getr regs0 9)). Proof. rd_slot. Qed.
  #[using="fs ctx thr db beg a2v a3v H"] Lemma rd1_32 : rdn SEGS m1 (Z_to_bv 64 (usp - 32)) 8 = Some (word_to_le_bytes 8 (getr regs0 18)). Proof. rd_slot. Qed.

  (* [comment removed for export] *)
  #[using="fs H"] Lemma tls_m1 : tlsH m1 (usp - 32) ctx thr db beg a2v a3v.
  Proof.
    pose proof HU as U. pose proof (s_ctxb _ _ _ _ _ _ _ _ _ H). pose proof (s_thrb _ _ _ _ _ _ _ _ _ H). pose proof (s_dbb _ _ _ _ _ _ _ _ _ H).
    pose proof (s_ap1 _ _ _ _ _ _ _ _ _ H). pose proof (s_ap2 _ _ _ _ _ _ _ _ _ H). pose proof (s_ap3 _ _ _ _ _ _ _ _ _ H).
    unfold SM_FRAME in *.
    assert (RD : forall a k, (0 <= a < 2 ^ 64)%Z -> (a + Z.of_nat k <= 2 ^ 64)%Z -> (a + Z.of_nat k <= usp - 208 \/ usp <= a)%Z ->
                 rdn SEGS m1 (Z_to_bv 64 a) k = rdn SEGS mem (Z_to_bv 64 a) k).
    { intros a k Ha Hk Hap. apply rdn_ext; [rewrite zbv_u by lia; lia|]. intros x Hx. rewrite zbv_u in Hx by lia. apply m1_out. lia. }
    constructor; unfold TLS_FRAME, cell, TP in *; rewrite ?RD by (cbn; lia); try (cbn; lia).
    - intros a Ha. unfold m1. repeat apply store_ok1_wbytes. apply (s_stk _ _ _ _ _ _ _ _ _ H). unfold SM_FRAME. lia.
    - pose proof (s_tcells _ _ _ _ _ _ _ _ _ H) as C. unfold tcells, cell in *. rewrite !RD by (cbn; lia). exact C.
    - exact (s_ctx _ _ _ _ _ _ _ _ _ H).
    - exact (s_thr _ _ _ _ _ _ _ _ _ H).
    - exact (s_a2 _ _ _ _ _ _ _ _ _ H).
    - exact (s_a3 _ _ _ _ _ _ _ _ _ H).
    - exact (s_db _ _ _ _ _ _ _ _ _ H).
    - exact (s_beg _ _ _ _ _ _ _ _ _ H).
    - exact (s_begb _ _ _ _ _ _ _ _ _ H).
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Section C0.
    Definition N0 : Z := 16384.
    Definition FL0 : Z := 4096.          (* [comment removed for export] *)
    Definition FR0 : Z := 36864.         (* [comment removed for export] *)
    Variable hint : word.                (* [comment removed for export] *)
    Variable FL : Z -> byte.             (* [comment removed for export] *)
    Variable p0 : Z.                     (* [comment removed for export] *)
    Hypothesis Hhint : rdn SEGS mem (Z_to_bv 64 fs) 8 = Some (word_to_le_bytes 8 hint).
    Hypothesis Hflags : forall p, (0 <= p < N0)%Z -> rdn SEGS mem (Z_to_bv 64 (fs + FL0 + p)) 1 = Some [FL p].
    Hypothesis Hp0 : (0 <= p0 < N0)%Z /\ bv_unsigned (FL p0) = 0%Z.
    Hypothesis Whint : forall j, (0 <= j < 8)%Z -> store_ok SEGS mem (Z_to_bv 64 (fs + j)) 1 = true.
    Hypothesis Wflag : forall p, (0 <= p < N0)%Z -> store_ok SEGS mem (Z_to_bv 64 (fs + FL0 + p)) 1 = true.
    Hypothesis Wframe : forall p j, (0 <= p < N0)%Z -> (0 <= j < 64)%Z -> store_ok SEGS mem (Z_to_bv 64 (fs + FR0 + 64 * p + j)) 1 = true.
    Hypothesis Wshad : forall p j, (0 <= p < N0)%Z -> (0 <= j < 8)%Z -> store_ok SEGS mem (Z_to_bv 64 (SB + (fs + FR0 + 64 * p) / 8 + j)) 1 = true.

    Let h : Z := bv_unsigned hint.
    Definition pos (i : Z) : Z := ((h + i) mod N0)%Z.
    Definition ff (p : Z) : Z := (fs + FR0 + 64 * p)%Z.

    #[using="Type"] Lemma lit_5bfc8 : v_addi (0x3ed18 : word) 4 = Z_to_bv 64 0x3ed1c. Proof. apply bv_eq; vm_compute; reflexivity. Qed.
    #[using="Type"] Lemma ret_ok_5bfcc : ret_ok (Z_to_bv 64 0x3ed1c). Proof. apply ret_ok_even. vm_compute. reflexivity. Qed.
    #[using="Type"] Lemma lit_5c0d4 : v_addi (0x3ee24 : word) 4 = Z_to_bv 64 0x3ee28. Proof. apply bv_eq; vm_compute; reflexivity. Qed.
    #[using="Type"] Lemma ret_ok_5c0d8 : ret_ok (Z_to_bv 64 0x3ee28). Proof. apply ret_ok_even. vm_compute. reflexivity. Qed.

    Ltac wz T V := progress (replace T with (Z_to_bv 64 V) by (apply bv_eq; vm_compute; reflexivity)).
    Ltac msd1 F D a v Hbase SOK :=
      mstep ltac:(eapply (step_sd_at _ _ _ _ _ _ _ _ _ (Z_to_bv 64 a) v F eq_refl D);
                   [ gr; rewrite ?Hbase; imm_norm; rewrite ?v_addi_any; apply (f_equal (Z_to_bv 64)); lia
                   | gr; first [reflexivity | assumption | symmetry; assumption]
                   | SOK ]).
    Ltac stk8 := pose proof HU; apply store_ok8_bytes; [lia|lia|];
                 intros j Hj; repeat apply store_ok1_wbytes; apply (s_stk _ _ _ _ _ _ _ _ _ H); unfold SM_FRAME; lia.

    (* [comment removed for export] *)
    Definition t_keep (r : reg) : bool := negb (tls_clob r || bv_eqb r 1 || bv_eqb r 2 || bv_eqb r 8 || bv_eqb r 10)%bool.

    #[using="fs ctx thr db beg a2v a3v H H01 H02 H04 hint h"] Lemma blk_PT :
      exists regs m,
        msteps SEGS (mkst regs0 (0x3ecf8 : word) mem rom) (mkst regs (0x3ed1c : word) m rom)
        /\ getr regs 2 = Z_to_bv 64 (usp - 32) /\ getr regs 8 = Z_to_bv 64 usp /\ getr regs 10 = Z_to_bv 64 TP
        /\ getr regs 4 = Z_to_bv 64 TP
        /\ (forall r, t_keep r = true -> getr regs r = getr regs0 r)
        /\ sfr m
        /\ (forall x : word, (usp - 32 <= bv_unsigned x)%Z -> m x = m1 x).
    Proof.
      pose proof HU as U.
      (* [comment removed for export] *)
      assert (P : exists q, msteps SEGS (mkst regs0 (0x3ecf8 : word) mem rom) (mkst q (0x4428c : word) m1 rom)
                /\ getr q 2 = Z_to_bv 64 (usp - 32) /\ getr q 8 = Z_to_bv 64 usp /\ getr q 10 = Z_to_bv 64 A_DESC
                /\ getr q 1 = Z_to_bv 64 0x3ed1c /\ getr q 4 = Z_to_bv 64 TP
                /\ (forall r : reg, r <> 1 -> r <> 2 -> r <> 8 -> r <> 10 -> getr q r = getr regs0 r)).
      { eexists. split.
        - mstep ltac:(exact (step_addi _ _ _ _ _ _ _ _ _ F_3ecf8 eq_refl D_3ecf8)). rewrite H02. zn.
          msd1 F_3ecfc D_3ecfc (usp - 8)%Z ra H02 ltac:(stk8).
          msd1 F_3ed00 D_3ed00 (usp - 16)%Z (getr regs0 8) H02 ltac:(stk8).
          msd1 F_3ed04 D_3ed04 (usp - 24)%Z (getr regs0 9) H02 ltac:(stk8).
          msd1 F_3ed08 D_3ed08 (usp - 32)%Z (getr regs0 18) H02 ltac:(stk8).
          change (wbytes _ _ _) with m1.
          mstep ltac:(exact (step_addi _ _ _ _ _ _ _ _ _ F_3ed0c eq_refl D_3ed0c)). gr. zn.
          mstep ltac:(eapply (step_auipc_at _ _ _ _ _ _ _ _ (Z_to_bv 64 0xabd10) F_3ed10 eq_refl D_3ed10);
                       [reflexivity | apply bv_eq; vm_compute; reflexivity]).
          mstep ltac:(exact (step_addi _ _ _ _ _ _ _ _ _ F_3ed14 eq_refl D_3ed14)). gr. zn.
          mstep ltac:(eapply (step_jal_link _ _ _ _ _ _ _ _ F_3ed18 eq_refl D_3ed18)). rewrite lit_5bfc8.
          apply mst_refl.
        - gr. repeat split; try (apply (f_equal (Z_to_bv 64)); lia); try reflexivity; try assumption.
          intros r N1 N2 N8 N10. repeat (rewrite getr_other by congruence). reflexivity. }
      destruct P as (q & MP & Q2 & Q8 & Q10 & Q1 & Q4 & QK).
      destruct (tls_run m1 rom (usp - 32) ctx thr db beg a2v a3v tls_m1 q (Z_to_bv 64 0x3ed1c) ret_ok_5bfcc Q1 Q2 Q4 Q10)
        as (q2 & m2 & MT & T10 & T2 & T1 & TK & TM1 & TM2 & TM3).
      exists q2, m2. split.
      { eapply msteps_trans; [exact MP|]. replace (Z_to_bv 64 0x3ed1c) with (0x3ed1c : word) in MT by (apply bv_eq; reflexivity). exact MT. }
      split; [exact T2|]. split; [rewrite TK by reflexivity; exact Q8|]. split; [exact T10|].
      split; [rewrite TK by reflexivity; exact Q4|]. split.
      { intros r Hr. unfold t_keep in Hr. apply negb_true_iff in Hr.
        apply orb_false_iff in Hr as [Hr K10]. apply orb_false_iff in Hr as [Hr K8].
        apply orb_false_iff in Hr as [Hr K2]. apply orb_false_iff in Hr as [Hr K1].
        rewrite TK by exact Hr. apply QK; intros ->; discriminate. }
      split.
      { destruct m1_sfr as (F1 & F2 & F3). unfold TLS_FRAME in TM1. split; [|split].
        - intros x Hx. rewrite TM1 by (unfold SM_FRAME in Hx; lia). apply F1. exact Hx.
        - intros x Hx. apply TM2. apply F2. exact Hx.
        - intros x Hx. apply TM3. apply F3. exact Hx. }
      intros x Hx. apply TM1. lia.
    Qed.

    (* [comment removed for export] *)
    Definition a_clob (r : reg) : bool :=
      (bv_eqb r 9 || bv_eqb r 10 || bv_eqb r 11 || bv_eqb r 12 || bv_eqb r 13 || bv_eqb r 14 || bv_eqb r 15 || bv_eqb r 18)%bool.

    #[using="ctx thr db beg a2v a3v H Hhint"] Lemma blk_A : forall regs m,
      sfr m -> getr regs 10 = Z_to_bv 64 TP ->
      exists regs',
        msteps SEGS (mkst regs (0x3ed1c : word) m rom) (mkst regs' (0x3ed7c : word) m rom)
        /\ getr regs' 9 = Z_to_bv 64 fs /\ getr regs' 18 = Z_to_bv 64 20
        /\ getr regs' 10 = Z_to_bv 64 (N0 - 0) /\ getr regs' 12 = Z_to_bv 64 (h + 0)
        /\ getr regs' 11 = Z_to_bv 64 (fs + FL0) /\ getr regs' 13 = Z_to_bv 64 (N0 - 1)
        /\ (forall r, a_clob r = false -> getr regs' r = getr regs r).
    Proof.
      intros regs m FR H10. pose proof HU as U. pose proof HF as (F1 & F2 & F3 & F4). unfold FS_AREA, TP in *.
      pose proof (s_fs _ _ _ _ _ _ _ _ _ H) as Cfs. pose proof (s_gc _ _ _ _ _ _ _ _ _ H) as Cgc. pose proof (s_ssl _ _ _ _ _ _ _ _ _ H) as Cssl.
      pose proof Hhint as Ch. unfold cell, TP in Cfs, Cgc, Cssl, Ch.
      rewrite <- (rdn_sfr m) in Cfs by (first [exact FR | cbn; unfold SM_FRAME; lia]).
      rewrite <- (rdn_sfr m) in Cgc by (first [exact FR | cbn; unfold SM_FRAME; lia]).
      rewrite <- (rdn_sfr m) in Cssl by (first [exact FR | cbn; unfold SM_FRAME; lia]).
      rewrite <- (rdn_sfr m) in Ch by (first [exact FR | cbn; unfold SM_FRAME; lia]).
      eexists. split.
      - mld F_3ed1c D_3ed1c fs Cfs H10.
        mstep ltac:(eapply (step_beq_ft _ _ _ _ _ _ _ _ _ F_3ed20 eq_refl D_3ed20); gr; rewrite getr_zero; br_eq).
        mstep ltac:(eapply (@step_lbu _ _ _ _ _ _ _ _ _ _ (Z_to_bv 8 0) F_3ed24 eq_refl D_3ed24); gr; imm_norm; zn; exact Cgc).
        change (bv_unsigned (Z_to_bv 8 0)) with 0%Z.
        mld F_3ed28 D_3ed28 20%Z Cssl H10.
        mstep ltac:(eapply (step_beq_tk _ _ _ _ _ _ _ _ _ F_3ed2c eq_refl D_3ed2c); gr; rewrite getr_zero; br_eq).
        mstep ltac:(exact (step_addi _ _ _ _ _ _ _ _ _ F_3ed3c eq_refl D_3ed3c)). gr. zn.
        mstep ltac:(exact (step_addi _ _ _ _ _ _ _ _ _ F_3ed40 eq_refl D_3ed40)). rewrite getr_zero. zn.
        mstep ltac:(exact (step_sll _ _ _ _ _ _ _ _ _ F_3ed44 eq_refl D_3ed44)). gr.
        wz (v_sll (Z_to_bv 64 1) (Z_to_bv 64 (20 + -6))) 16384%Z.
        mstep ltac:(exact (step_addiw _ _ _ _ _ _ _ _ _ F_3ed48 eq_refl D_3ed48)). gr. imm_norm.
        wz (v_addiw (Z_to_bv 64 16384) 0) 16384%Z.
        mstep ltac:(eapply (step_bge_ft _ _ _ _ _ _ _ _ _ F_3ed4c eq_refl D_3ed4c); gr; rewrite getr_zero; apply c_lts_pos_ft; lia).
        mstep ltac:(eapply (step_lui_at _ _ _ _ _ _ _ _ (Z_to_bv 64 4096) F_3ed50 eq_refl D_3ed50); reflexivity).
        mstep ltac:(exact (step_addi _ _ _ _ _ _ _ _ _ F_3ed54 eq_refl D_3ed54)). rewrite getr_zero, k_m1_val.
        mstep ltac:(eapply (@step_ld _ _ _ _ _ _ _ _ _ _ _ hint F_3ed58 eq_refl D_3ed58);
                     [ gr; imm_norm; zn; rewrite ?Z.add_0_r; exact Ch | apply bytes_le_to_Z_8 ]).
        rewrite (zbv_self' hint). fold h.
        mstep ltac:(exact (step_sll _ _ _ _ _ _ _ _ _ F_3ed5c eq_refl D_3ed5c)). gr.
        wz (v_sll (Z_to_bv 64 (2 ^ 64 - 1)) (Z_to_bv 64 (20 + -6))) (2 ^ 64 - 16384)%Z.
        mstep ltac:(exact (step_addi _ _ _ _ _ _ _ _ _ F_3ed60 eq_refl D_3ed60)). gr. zn.
        mstep ltac:(exact (step_add _ _ _ _ _ _ _ _ _ F_3ed64 eq_refl D_3ed64)). gr. rewrite v_add_zbv by lia.
        mstep ltac:(exact (step_xori _ _ _ _ _ _ _ _ _ F_3ed68 eq_refl D_3ed68)). gr. imm_norm.
        wz (v_xori (Z_to_bv 64 (2 ^ 64 - 16384)) (-1)) 16383%Z.
        mstep ltac:(exact (step_slli _ _ _ _ _ _ _ _ _ F_3ed6c eq_refl D_3ed6c)). gr. imm_norm.
        wz (v_slli (Z_to_bv 64 (16384 + -1)) 32) (16383 * 2 ^ 32)%Z.
        mstep ltac:(exact (PropExec.step_srli _ _ _ _ _ _ _ _ _ F_3ed70 eq_refl D_3ed70)). gr. imm_norm.
        wz (v_srli (Z_to_bv 64 (16383 * 2 ^ 32)) 32) 16383%Z.
        mstep ltac:(exact (step_add _ _ _ _ _ _ _ _ _ F_3ed74 eq_refl D_3ed74)). gr. rewrite v_add_any.
        mstep ltac:(exact (step_addi _ _ _ _ _ _ _ _ _ F_3ed78 eq_refl D_3ed78)). gr. rewrite v_addi_any.
        apply mst_refl.
      - gr. unfold N0, FL0. repeat split; try (apply (f_equal (Z_to_bv 64)); lia); try reflexivity.
        intros r Hr. unfold a_clob in Hr.
        repeat (rewrite getr_other by (intros ->; cbn in Hr; discriminate)). reflexivity.
    Qed.

    (* [comment removed for export] *)
    Let i0 : Z := ((p0 - h) mod N0)%Z.
    #[using="Type"] Lemma i0_rng : (0 <= i0 < N0)%Z. Proof. unfold i0, N0. apply Z.mod_pos_bound. lia. Qed.
    #[using="FL Hp0"] Lemma pos_i0 : pos i0 = p0.
    Proof.
      unfold pos, i0, N0. rewrite Zplus_mod_idemp_r. replace (h + (p0 - h))%Z with p0 by lia.
      apply Z.mod_small. unfold N0 in Hp0. lia.
    Qed.
    #[using="p0 i0"] Lemma pos_rng : forall i, (0 <= pos i < N0)%Z. Proof. intros i. unfold pos, N0. apply Z.mod_pos_bound. lia. Qed.

    Definition l_clob (r : reg) : bool := (bv_eqb r 10 || bv_eqb r 12 || bv_eqb r 15 || bv_eqb r 16 || bv_eqb r 17)%bool.

    #[using="ctx thr db beg a2v a3v H Hflags Hp0"] Lemma blk_L : forall (k : nat) i regs m,
      (i + Z.of_nat k = i0)%Z -> (0 <= i)%Z -> sfr m ->
      getr regs 10 = Z_to_bv 64 (N0 - i) -> getr regs 12 = Z_to_bv 64 (h + i) ->
      getr regs 11 = Z_to_bv 64 (fs + FL0) -> getr regs 13 = Z_to_bv 64 (N0 - 1) ->
      exists i' regs',
        (i <= i' <= i0)%Z /\ bv_unsigned (FL (pos i')) = 0%Z
        /\ msteps SEGS (mkst regs (0x3ed7c : word) m rom) (mkst regs' (0x3edf4 : word) m rom)
        /\ getr regs' 12 = Z_to_bv 64 (h + i') /\ getr regs' 16 = Z_to_bv 64 (pos i')
        /\ getr regs' 15 = Z_to_bv 64 (fs + FL0 + pos i')
        /\ (forall r, l_clob r = false -> getr regs' r = getr regs r).
    Proof.
      pose proof HU as U. pose proof HF as (F1 & F2 & F3 & F4). unfold FS_AREA in *. pose proof i0_rng as I0. pose proof Hp0 as [P0 P1].
      unfold N0 in *.
      unfold FL0 in *.
      induction k as [|k IH]; intros i regs m Hk Hi FR H10 H12 H11 H13.
      - (* [comment removed for export] *)
        cbn [Z.of_nat] in Hk. rewrite Z.add_0_r in Hk. subst i.
        pose proof (pos_rng i0) as PR. unfold N0 in PR.
        pose proof (Hflags (pos i0) PR) as CF. rewrite <- (rdn_sfr m) in CF by (first [exact FR | cbn; unfold SM_FRAME, FL0; lia]).
        exists i0. eexists. split; [lia|]. split; [rewrite pos_i0; exact P1|]. split.
        + mstep ltac:(exact (step_and _ _ _ _ _ _ _ _ _ F_3ed7c eq_refl D_3ed7c)). gr. rewrite H12, H13.
          change (16384 - 1)%Z with (2 ^ 14 - 1)%Z. rewrite v_and_mask by lia. change (2 ^ 14)%Z with 16384%Z. fold N0. fold (pos i0).
          mstep ltac:(exact (step_add _ _ _ _ _ _ _ _ _ F_3ed80 eq_refl D_3ed80)). gr. rewrite H11. unfold FL0. rewrite v_add_zbv by lia.
          mstep ltac:(eapply (@step_lbu _ _ _ _ _ _ _ _ _ _ (FL (pos i0)) F_3ed84 eq_refl D_3ed84); gr; imm_norm; zn; rewrite ?Z.add_0_r; unfold FL0 in CF; exact CF).
          replace (bv_unsigned (FL (pos i0))) with 0%Z by (rewrite pos_i0, P1; reflexivity).
          mstep ltac:(eapply (step_beq_tk _ _ _ _ _ _ _ _ _ F_3ed88 eq_refl D_3ed88); gr; rewrite getr_zero; br_eq).
          apply mst_refl.
        + gr. unfold FL0. repeat split; try (apply (f_equal (Z_to_bv 64)); lia); try reflexivity; try assumption.
          intros r Hr. unfold l_clob in Hr.
          repeat (rewrite getr_other by (intros ->; cbn in Hr; discriminate)). reflexivity.
      - (* [comment removed for export] *)
        pose proof (pos_rng i) as PR. unfold N0 in PR.
        pose proof (Hflags (pos i) PR) as CF. rewrite <- (rdn_sfr m) in CF by (first [exact FR | cbn; unfold SM_FRAME, FL0; lia]).
        pose proof (bv_unsigned_in_range 8 (FL (pos i))) as BR. change (bv_modulus 8) with 256%Z in BR.
        destruct (Z.eq_dec (bv_unsigned (FL (pos i))) 0) as [Z0|NZ].
        + exists i. eexists. split; [lia|]. split; [exact Z0|]. split.
          * mstep ltac:(exact (step_and _ _ _ _ _ _ _ _ _ F_3ed7c eq_refl D_3ed7c)). gr. rewrite H12, H13.
            change (16384 - 1)%Z with (2 ^ 14 - 1)%Z. rewrite v_and_mask by lia. change (2 ^ 14)%Z with 16384%Z. fold N0. fold (pos i).
            mstep ltac:(exact (step_add _ _ _ _ _ _ _ _ _ F_3ed80 eq_refl D_3ed80)). gr. rewrite H11. unfold FL0. rewrite v_add_zbv by lia.
            mstep ltac:(eapply (@step_lbu _ _ _ _ _ _ _ _ _ _ (FL (pos i)) F_3ed84 eq_refl D_3ed84); gr; imm_norm; zn; rewrite ?Z.add_0_r; unfold FL0 in CF; exact CF).
            rewrite Z0.
            mstep ltac:(eapply (step_beq_tk _ _ _ _ _ _ _ _ _ F_3ed88 eq_refl D_3ed88); gr; rewrite getr_zero; br_eq).
            apply mst_refl.
          * gr. unfold FL0. repeat split; try (apply (f_equal (Z_to_bv 64)); lia); try reflexivity; try assumption.
            intros r Hr. unfold l_clob in Hr.
            repeat (rewrite getr_other by (intros ->; cbn in Hr; discriminate)). reflexivity.
        + assert (NI : i <> i0) by (intros ->; rewrite pos_i0 in NZ; exact (NZ P1)).
          edestruct (IH (i + 1)%Z
            (regupd (regupd (regupd (regupd (regupd regs 16 (Z_to_bv 64 (pos i))) 15 (Z_to_bv 64 (fs + FL0 + pos i)))
               17 (Z_to_bv 64 (bv_unsigned (FL (pos i))))) 10 (Z_to_bv 64 (16384 - i - 1))) 12 (Z_to_bv 64 (h + i + 1))) m)
            as (i' & regs' & R1 & R2 & M & Q12 & Q16 & Q15 & QK); try lia; try exact FR.
          1-4: gr; first [assumption | apply (f_equal (Z_to_bv 64)); lia].
          exists i', regs'. split; [lia|]. split; [exact R2|]. split.
          * mstep ltac:(exact (step_and _ _ _ _ _ _ _ _ _ F_3ed7c eq_refl D_3ed7c)). gr. rewrite H12, H13.
            change (16384 - 1)%Z with (2 ^ 14 - 1)%Z. rewrite v_and_mask by lia. change (2 ^ 14)%Z with 16384%Z. fold N0. fold (pos i).
            mstep ltac:(exact (step_add _ _ _ _ _ _ _ _ _ F_3ed80 eq_refl D_3ed80)). gr. rewrite H11. rewrite v_add_zbv by (unfold FL0; lia).
            mstep ltac:(eapply (@step_lbu _ _ _ _ _ _ _ _ _ _ (FL (pos i)) F_3ed84 eq_refl D_3ed84); gr; imm_norm; zn; rewrite ?Z.add_0_r; exact CF).
            mstep ltac:(eapply (step_beq_ft _ _ _ _ _ _ _ _ _ F_3ed88 eq_refl D_3ed88); gr; rewrite getr_zero; br_eq).
            mstep ltac:(exact (step_addiw _ _ _ _ _ _ _ _ _ F_3ed8c eq_refl D_3ed8c)). gr. rewrite H10. imm_norm.
            rewrite v_addiw_small by lia.
            mstep ltac:(exact (step_addi _ _ _ _ _ _ _ _ _ F_3ed90 eq_refl D_3ed90)). gr. rewrite H12, v_addi_any.
            mstep ltac:(eapply (step_bne_tk _ _ _ _ _ _ _ _ _ F_3ed94 eq_refl D_3ed94); gr; rewrite getr_zero; br_eq).
            replace (16384 - i + -1)%Z with (16384 - i - 1)%Z by lia. exact M.
          * split; [exact Q12|]. split; [exact Q16|]. split; [exact Q15|].
            intros r Hr. rewrite (QK r Hr). unfold l_clob in Hr.
            repeat (rewrite getr_other by (intros ->; cbn in Hr; discriminate)). reflexivity.
    Qed.

    (* [comment removed for export] *)
    (* [comment removed for export] *)
    Definition WR (m : word -> option byte) (i p : Z) : word -> option byte :=
      wbytes (wbytes (wbytes (wbytes (wbytes m
        (Z_to_bv 64 fs) (word_to_le_bytes 8 (Z_to_bv 64 (h + i + 1))))
        (Z_to_bv 64 (fs + FL0 + p)) (word_to_le_bytes 1 (Z_to_bv 64 1)))
        (Z_to_bv 64 (ff p + 24)) (word_to_le_bytes 8 (Z_to_bv 64 usp)))
        (Z_to_bv 64 (ff p + 56)) (word_to_le_bytes 8 (Z_to_bv 64 (fs + FL0 + p))))
        (Z_to_bv 64 (SB + ff p / 8)) (word_to_le_bytes 8 (Z_to_bv 64 0)).

    #[using="Type"] Lemma WR_agree : forall ma mb i p (x : word), ma x = mb x -> WR ma i p x = WR mb i p x.
    Proof. intros. unfold WR. repeat apply wbytes_agree. assumption. Qed.
    #[using="Type"] Lemma WR_keep : forall m i p (x : word), m x <> None -> WR m i p x <> None.
    Proof. intros. unfold WR. repeat apply wbytes_keep. assumption. Qed.
    #[using="Type"] Lemma WR_sok : forall m i p (x : word), store_ok SEGS m x 1 = true -> store_ok SEGS (WR m i p) x 1 = true.
    Proof. intros. unfold WR. repeat apply store_ok1_wbytes. assumption. Qed.

    (* [comment removed for export] *)
    #[using="mem rom ctx thr db beg a2v a3v H p0 i0"] Lemma WR_stack : forall m i p a, (0 <= p < N0)%Z -> (usp - 32 <= a)%Z -> (a + 8 <= usp)%Z ->
      rdn SEGS (WR m i p) (Z_to_bv 64 a) 8 = rdn SEGS m (Z_to_bv 64 a) 8.
    Proof.
      intros m i p a Hp Ha Hb. pose proof HU as U. pose proof HF as (F1 & F2 & F3 & F4). unfold FS_AREA, N0, ff, FR0, FL0 in *.
      pose proof SB_val.
      assert (ff_hi : (fs + 36864 + 64 * p + 64 <= 2 ^ 47)%Z) by lia.
      pose proof (Z.div_pos (fs + 36864 + 64 * p) 8 ltac:(lia) ltac:(lia)).
      pose proof (Z.div_lt_upper_bound (fs + 36864 + 64 * p) 8 (2 ^ 44) ltac:(lia) ltac:(lia)).
      unfold WR, ff, FL0, FR0. rewrite !rdn_wbytes_out; try reflexivity; len8; rewrite ?zbv_u by lia; lia.
    Qed.
    #[using="mem rom ctx thr db beg a2v a3v H p0 i0"] Lemma WR_low : forall m i p a k, (0 <= p < N0)%Z -> (0 <= a)%Z -> (a + Z.of_nat k <= 0x608000)%Z ->
      rdn SEGS (WR m i p) (Z_to_bv 64 a) k = rdn SEGS m (Z_to_bv 64 a) k.
    Proof.
      intros m i p a k Hp Ha Hb. pose proof HU as U. pose proof HF as (F1 & F2 & F3 & F4). unfold FS_AREA, N0, ff, FR0, FL0 in *.
      pose proof SB_val.
      assert (ff_hi : (fs + 36864 + 64 * p + 64 <= 2 ^ 47)%Z) by lia.
      pose proof (Z.div_pos (fs + 36864 + 64 * p) 8 ltac:(lia) ltac:(lia)).
      pose proof (Z.div_lt_upper_bound (fs + 36864 + 64 * p) 8 (2 ^ 44) ltac:(lia) ltac:(lia)).
      unfold WR, ff, FL0, FR0. rewrite !rdn_wbytes_out; try reflexivity; len8; rewrite ?zbv_u by lia; lia.
    Qed.

    Definition f_clob (r : reg) : bool :=
      (bv_eqb r 1 || bv_eqb r 2 || bv_eqb r 5 || bv_eqb r 8 || bv_eqb r 9 || bv_eqb r 10 || bv_eqb r 11 || bv_eqb r 12
       || bv_eqb r 13 || bv_eqb r 14 || bv_eqb r 15 || bv_eqb r 16 || bv_eqb r 17 || bv_eqb r 18)%bool.

    #[using="ctx thr db beg a2v a3v H Hret p0 Whint Wflag Wframe Wshad i0"] Lemma blk_F : forall regs m i p,
      sfr m -> (forall x : word, (usp - 32 <= bv_unsigned x)%Z -> m x = m1 x) ->
      (0 <= p < N0)%Z -> (0 <= i < N0)%Z ->
      getr regs 2 = Z_to_bv 64 (usp - 32) -> getr regs 8 = Z_to_bv 64 usp -> getr regs 9 = Z_to_bv 64 fs ->
      getr regs 18 = Z_to_bv 64 20 -> getr regs 11 = Z_to_bv 64 (fs + FL0) ->
      getr regs 12 = Z_to_bv 64 (h + i) -> getr regs 16 = Z_to_bv 64 p -> getr regs 15 = Z_to_bv 64 (fs + FL0 + p) ->
      exists regs',
        msteps SEGS (mkst regs (0x3edf4 : word) m rom) (mkst regs' ra (WR m i p) rom)
        /\ getr regs' 10 = Z_to_bv 64 (ff p) /\ getr regs' 2 = Z_to_bv 64 usp /\ getr regs' 1 = ra
        /\ getr regs' 8 = getr regs0 8 /\ getr regs' 9 = getr regs0 9 /\ getr regs' 18 = getr regs0 18
        /\ (forall r, f_clob r = false -> getr regs' r = getr regs r).
    Proof.
      intros regs m i p FR AG Hp Hi H2 H8 H9 H18 H11 H12 H16 H15.
      pose proof HU as U. pose proof HF as (F1 & F2 & F3 & F4). pose proof SB_val as HSB. unfold FS_AREA, N0, FL0 in *.
      destruct FR as (FR1 & FR2 & FR3).
      assert (ff_lo : (0x608000 <= ff p)%Z) by (unfold ff, FR0; lia).
      assert (ff_hi : (ff p + 64 <= 2 ^ 47)%Z) by (unfold ff, FR0; lia).
      pose proof (Z.div_pos (ff p) 8 ltac:(lia) ltac:(lia)) as D1.
      pose proof (Z.div_lt_upper_bound (ff p) 8 (2 ^ 44) ltac:(lia) ltac:(lia)) as D2.
      (* [comment removed for export] *)
      assert (RD : forall a v, (usp - 32 <= a)%Z -> (a + 8 <= usp)%Z ->
                rdn SEGS m1 (Z_to_bv 64 a) 8 = Some (word_to_le_bytes 8 v) ->
                rdn SEGS (WR m i p) (Z_to_bv 64 a) 8 = Some (word_to_le_bytes 8 v)).
      { intros a v Ha Hb R. rewrite WR_stack by (unfold N0; lia). rewrite <- R. apply rdn_ext; [rewrite zbv_u by lia; cbn; lia|].
        intros x Hx. rewrite zbv_u in Hx by lia. apply AG. lia. }
      pose proof (RD (usp - 8)%Z _ ltac:(lia) ltac:(lia) rd1_8) as R8. pose proof (RD (usp - 16)%Z _ ltac:(lia) ltac:(lia) rd1_16) as R16.
      pose proof (RD (usp - 24)%Z _ ltac:(lia) ltac:(lia) rd1_24) as R24. pose proof (RD (usp - 32)%Z _ ltac:(lia) ltac:(lia) rd1_32) as R32.
      (* [comment removed for export] *)
      set (m4 := wbytes (wbytes (wbytes (wbytes m
        (Z_to_bv 64 fs) (word_to_le_bytes 8 (Z_to_bv 64 (h + i + 1))))
        (Z_to_bv 64 (fs + 4096 + p)) (word_to_le_bytes 1 (Z_to_bv 64 1)))
        (Z_to_bv 64 (ff p + 24)) (word_to_le_bytes 8 (Z_to_bv 64 usp)))
        (Z_to_bv 64 (ff p + 56)) (word_to_le_bytes 8 (Z_to_bv 64 (fs + 4096 + p)))).
      assert (C4 : cells m4).
      { pose proof (s_cells _ _ _ _ _ _ _ _ _ H) as C. unfold cells, cell in *. unfold m4.
        rewrite !rdn_wbytes_out; len8; rewrite ?zbv_u by (ltac2:(LK.k [@F1; @F2; @Hp; @U; @ff_lo; @ff_hi]); lia); try (cbn; unfold ff, FR0 in *; (ltac2:(LK.k [@F1; @F2; @Hp; @U; @ff_lo; @ff_hi]); lia)).
        rewrite !(rdn_sfr m) by (first [split; [exact FR1|split; [exact FR2|exact FR3]] | cbn; unfold SM_FRAME; lia]). exact C. }
      (* [comment removed for export] *)
      assert (P1 : exists r1,
        msteps SEGS (mkst regs (0x3edf4 : word) m rom) (mkst r1 (0x3f510 : word) m4 rom)
        /\ getr r1 10 = Z_to_bv 64 (ff p) /\ getr r1 1 = Z_to_bv 64 0x3ee28 /\ getr r1 2 = Z_to_bv 64 (usp - 32)
        /\ getr r1 9 = Z_to_bv 64 (ff p)
        /\ (forall r : reg, r <> 1 -> r <> 9 -> r <> 10 -> r <> 12 -> r <> 16 -> r <> 18 -> getr r1 r = getr regs r)).
      { eexists. split.
        - mstep ltac:(exact (step_addi _ _ _ _ _ _ _ _ _ F_3edf4 eq_refl D_3edf4)). gr. rewrite H12, v_addi_any.
          mstep ltac:(exact (step_addi _ _ _ _ _ _ _ _ _ F_3edf8 eq_refl D_3edf8)). rewrite getr_zero. zn.
          mstep ltac:(exact (step_addi _ _ _ _ _ _ _ _ _ F_3edfc eq_refl D_3edfc)). gr. rewrite H18. zn.
          mstep ltac:(exact (step_slli _ _ _ _ _ _ _ _ _ F_3ee00 eq_refl D_3ee00)). gr. rewrite H16. imm_norm.
          rewrite (v_slli_zbv p 6) by lia.
          msd1 F_3ee04 D_3ee04 fs (Z_to_bv 64 (h + i + 1)) H9
               ltac:(apply store_ok8_bytes; [lia|lia|]; intros j Hj; apply FR3; apply Whint; lia).
          mstep ltac:(eapply (step_sb _ _ _ _ _ _ _ _ _ F_3ee08 eq_refl D_3ee08);
                       gr; rewrite H15; imm_norm; zn; rewrite ?Z.add_0_r; apply store_ok1_wbytes; apply FR3; apply Wflag; lia).
          gr. rewrite H15. zn. rewrite ?Z.add_0_r.
          mstep ltac:(exact (step_sll _ _ _ _ _ _ _ _ _ F_3ee0c eq_refl D_3ee0c)). gr.
          wz (v_sll (Z_to_bv 64 1) (Z_to_bv 64 (20 + -5))) 32768%Z.
          mstep ltac:(exact (step_add _ _ _ _ _ _ _ _ _ F_3ee10 eq_refl D_3ee10)). gr. rewrite H11, v_add_zbv by lia.
          mstep ltac:(exact (step_add _ _ _ _ _ _ _ _ _ F_3ee14 eq_refl D_3ee14)). gr. rewrite v_add_zbv by lia.
          change (2 ^ 6)%Z with 64%Z. replace (fs + 4096 + 32768 + p * 64)%Z with (ff p) by (unfold ff, FR0; lia).
          msd1 F_3ee18 D_3ee18 (ff p + 24)%Z (Z_to_bv 64 usp) H8
               ltac:(apply store_ok8_bytes; [lia|lia|]; intros j Hj; repeat apply store_ok1_wbytes; apply FR3;
                     unfold ff, FR0; replace (fs + 36864 + 64 * p + 24 + j)%Z with (fs + 36864 + 64 * p + (24 + j))%Z by lia; apply Wframe; lia).
          msd1 F_3ee1c D_3ee1c (ff p + 56)%Z (Z_to_bv 64 (fs + 4096 + p)) H8
               ltac:(apply store_ok8_bytes; [lia|lia|]; intros j Hj; repeat apply store_ok1_wbytes; apply FR3;
                     unfold ff, FR0; replace (fs + 36864 + 64 * p + 56 + j)%Z with (fs + 36864 + 64 * p + (56 + j))%Z by lia; apply Wframe; lia).
          change (wbytes _ _ _) with m4.
          mstep ltac:(exact (step_addi _ _ _ _ _ _ _ _ _ F_3ee20 eq_refl D_3ee20)). gr. zn. rewrite ?Z.add_0_r.
          mstep ltac:(eapply (step_jal_link _ _ _ _ _ _ _ _ F_3ee24 eq_refl D_3ee24)). rewrite lit_5c0d4.
          apply mst_refl.
        - gr. repeat split; try reflexivity; try assumption; try (apply (f_equal (Z_to_bv 64)); lia).
          intros r N1 N9 N10 N12 N16 N18. repeat (rewrite getr_other by congruence). reflexivity. }
      destruct P1 as (r1 & M1 & P10 & P1ra & P2 & P9 & PK).
      destruct (mem_to_shadow_5e918 rom r1 m4 (ff p) (Z_to_bv 64 0x3ee28) C4 ltac:(lia)
                  ltac:(apply (in_mem_frame fs (ff p) 64 HFB); [lia|unfold ff, FR0; lia|unfold ff, FR0 in *; unfold FS_AREA in *; lia|unfold FS_AREA in *; lia|lia])
                  P10 P1ra ret_ok_5c0d8)
        as (q & MQ & Q10 & QK).
      assert (Q2 : getr q 2 = Z_to_bv 64 (usp - 32)) by (rewrite QK by reflexivity; exact P2).
      assert (Q9 : getr q 9 = Z_to_bv 64 (ff p)) by (rewrite QK by reflexivity; exact P9).
      eexists. split.
      - eapply msteps_trans; [exact M1|]. eapply msteps_trans; [exact MQ|].
        replace (Z_to_bv 64 0x3ee28) with (0x3ee28 : word) by (apply bv_eq; reflexivity).
        mstep ltac:(exact (step_addi _ _ _ _ _ _ _ _ _ F_3ee28 eq_refl D_3ee28)). gr. rewrite Q10. zn. rewrite ?Z.add_0_r.
        mstep ltac:(exact (step_addi _ _ _ _ _ _ _ _ _ F_3ee2c eq_refl D_3ee2c)). gr. rewrite Q9. zn. rewrite ?Z.add_0_r.
        mstep ltac:(exact (step_addi _ _ _ _ _ _ _ _ _ F_3ee30 eq_refl D_3ee30)). rewrite getr_zero. zn.
        msd1 F_3ee34 D_3ee34 (SB + ff p / 8)%Z (Z_to_bv 64 0) Q2
             ltac:(apply store_ok8_bytes; [lia|lia|]; intros j Hj; unfold m4; repeat apply store_ok1_wbytes; apply FR3;
                   unfold ff, FR0; apply Wshad; lia).
        change (wbytes _ _ _) with (WR m i p).
        mstep ltac:(eapply (@step_ld _ _ _ _ _ _ _ _ _ _ _ ra F_3ee38 eq_refl D_3ee38);
                     [ gr; rewrite Q2; imm_norm; zn; replace (usp - 32 + 24)%Z with (usp - 8)%Z by lia; exact R8 | apply bytes_le_to_Z_8 ]).
        mstep ltac:(eapply (@step_ld _ _ _ _ _ _ _ _ _ _ _ (getr regs0 8) F_3ee3c eq_refl D_3ee3c);
                     [ gr; rewrite Q2; imm_norm; zn; replace (usp - 32 + 16)%Z with (usp - 16)%Z by lia; exact R16 | apply bytes_le_to_Z_8 ]).
        mstep ltac:(eapply (@step_ld _ _ _ _ _ _ _ _ _ _ _ (getr regs0 9) F_3ee40 eq_refl D_3ee40);
                     [ gr; rewrite Q2; imm_norm; zn; replace (usp - 32 + 8)%Z with (usp - 24)%Z by lia; exact R24 | apply bytes_le_to_Z_8 ]).
        mstep ltac:(eapply (@step_ld _ _ _ _ _ _ _ _ _ _ _ (getr regs0 18) F_3ee44 eq_refl D_3ee44);
                     [ gr; rewrite Q2; imm_norm; zn; rewrite ?Z.add_0_r; exact R32 | apply bytes_le_to_Z_8 ]).
        mstep ltac:(exact (step_addi _ _ _ _ _ _ _ _ _ F_3ee48 eq_refl D_3ee48)). gr. rewrite Q2. zn.
        replace (usp - 32 + 32)%Z with usp by lia.
        eapply mst_step; [reflexivity | eapply (step_jalr_x0 _ _ _ _ _ _ _ _ ra F_3ee4c eq_refl D_3ee4c); gr; reflexivity |].
        imm_norm. rewrite Hret. apply mst_refl.
      - gr. repeat split; try reflexivity.
        intros r Hr. unfold f_clob in Hr.
        repeat (rewrite getr_other by (intros ->; cbn in Hr; discriminate)).
        rewrite QK by (unfold m2s_clob; repeat match type of Hr with (?a || ?b)%bool = false => apply orb_false_iff in Hr; destruct Hr as [Hr ?] end;
                       repeat match goal with Hb : bv_eqb r _ = false |- _ => rewrite Hb; clear Hb end; reflexivity).
        apply PK; intros ->; cbn in Hr; discriminate.
    Qed.

    (* [comment removed for export] *)
    #[using="ctx thr db beg a2v a3v H Hret H01 H02 H04 p0 Hhint Hflags Hp0 Whint Wflag Wframe Wshad i0"] Theorem sm0_AM :
      exists i p regs' m',
        (0 <= i < N0)%Z /\ p = pos i /\ bv_unsigned (FL p) = 0%Z
        /\ msteps SEGS (mkst regs0 (0x3ecf8 : word) mem rom) (mkst regs' ra m' rom)
        /\ getr regs' 10 = Z_to_bv 64 (ff p) /\ getr regs' 2 = Z_to_bv 64 usp /\ getr regs' 1 = ra
        /\ (forall r, sm_clob r = false -> getr regs' r = getr regs0 r)
        /\ (forall x : word, (bv_unsigned x < usp - SM_FRAME \/ usp <= bv_unsigned x)%Z -> m' x = WR mem i p x)
        /\ (forall x, mem x <> None -> m' x <> None)
        /\ (forall x, store_ok SEGS mem x 1 = true -> store_ok SEGS m' x 1 = true).
    Proof.
      pose proof HU as U. pose proof i0_rng as I0.
      destruct blk_PT as (q1 & m2 & M1 & A2 & A8 & A10 & A4 & AK & FR & AG).
      destruct (blk_A q1 m2 FR A10) as (q2 & M2 & B9 & B18 & B10 & B12 & B11 & B13 & BK).
      destruct (blk_L (Z.to_nat i0) 0 q2 m2 ltac:(lia) ltac:(lia) FR B10 B12 B11 B13)
        as (i & q3 & Hi & HZ & M3 & C12 & C16 & C15 & CK).
      assert (C2 : getr q3 2 = Z_to_bv 64 (usp - 32)) by (rewrite CK, BK by reflexivity; exact A2).
      assert (C8 : getr q3 8 = Z_to_bv 64 usp) by (rewrite CK, BK by reflexivity; exact A8).
      assert (C9 : getr q3 9 = Z_to_bv 64 fs) by (rewrite CK by reflexivity; exact B9).
      assert (C18 : getr q3 18 = Z_to_bv 64 20) by (rewrite CK by reflexivity; exact B18).
      assert (C11 : getr q3 11 = Z_to_bv 64 (fs + FL0)) by (rewrite CK by reflexivity; exact B11).
      pose proof (pos_rng i) as PR.
      destruct (blk_F q3 m2 i (pos i) FR AG PR ltac:(lia) C2 C8 C9 C18 C11 C12 C16 C15)
        as (q4 & M4 & D10 & D2 & D1 & D8 & D9 & D18 & DK).
      exists i, (pos i), q4, (WR m2 i (pos i)).
      split; [lia|]. split; [reflexivity|]. split; [exact HZ|]. split.
      { eapply msteps_trans; [exact M1|]. eapply msteps_trans; [exact M2|]. eapply msteps_trans; [exact M3|]. exact M4. }
      split; [exact D10|]. split; [exact D2|]. split; [exact D1|]. split.
      { intros r Hr.
        destruct (bv_eq_dec _ r 1) as [-> | N1]; [rewrite D1; symmetry; exact H01|].
        destruct (bv_eq_dec _ r 2) as [-> | N2]; [rewrite D2; symmetry; exact H02|].
        destruct (bv_eq_dec _ r 8) as [-> | N8]; [exact D8|].
        destruct (bv_eq_dec _ r 9) as [-> | N9]; [exact D9|].
        destruct (bv_eq_dec _ r 18) as [-> | N18]; [exact D18|].
        assert (NE : forall k : reg, r <> k -> bv_eqb r k = false) by (intros k Hk; apply bv_eqb_neq; exact Hk).
        pose proof (NE _ N1) as T1. pose proof (NE _ N2) as T2. pose proof (NE _ N8) as T8. pose proof (NE _ N9) as T9. pose proof (NE _ N18) as T18.
        unfold sm_clob in Hr.
        apply orb_false_iff in Hr as [Hr T17]. apply orb_false_iff in Hr as [Hr T16]. apply orb_false_iff in Hr as [Hr T15].
        apply orb_false_iff in Hr as [Hr T14]. apply orb_false_iff in Hr as [Hr T13]. apply orb_false_iff in Hr as [Hr T12].
        apply orb_false_iff in Hr as [Hr T11]. apply orb_false_iff in Hr as [T5 T10].
        rewrite DK by (unfold f_clob; rewrite ?T1, ?T2, ?T5, ?T8, ?T9, ?T10, ?T11, ?T12, ?T13, ?T14, ?T15, ?T16, ?T17, ?T18; reflexivity).
        rewrite CK by (unfold l_clob; rewrite ?T10, ?T12, ?T15, ?T16, ?T17; reflexivity).
        rewrite BK by (unfold a_clob; rewrite ?T9, ?T10, ?T11, ?T12, ?T13, ?T14, ?T15, ?T18; reflexivity).
        apply AK. unfold t_keep, tls_clob. rewrite T10, T11, T12, T13, T1, T2, T8. reflexivity. }
      destruct FR as (FR1 & FR2 & FR3). split; [|split].
      - intros x Hx. apply WR_agree. apply FR1. exact Hx.
      - intros x Hx. apply WR_keep. apply FR2. exact Hx.
      - intros x Hx. apply WR_sok. apply FR3. exact Hx.
    Qed.
  End C0.
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Section C1.
    Definition N1 : Z := 8192.
    Definition FL1 : Z := 20480.         (* [comment removed for export] *)
    Definition FR1 : Z := 1085440.       (* [comment removed for export] *)
    Variable hint : word.                (* [comment removed for export] *)
    Variable FL : Z -> byte.             (* [comment removed for export] *)
    Variable p0 : Z.                     (* [comment removed for export] *)
    Hypothesis Hhint : rdn SEGS mem (Z_to_bv 64 (fs + 8)) 8 = Some (word_to_le_bytes 8 hint).
    Hypothesis Hflags : forall p, (0 <= p < N1)%Z -> rdn SEGS mem (Z_to_bv 64 (fs + FL1 + p)) 1 = Some [FL p].
    Hypothesis Hp0 : (0 <= p0 < N1)%Z /\ bv_unsigned (FL p0) = 0%Z.
    Hypothesis Whint : forall j, (8 <= j < 16)%Z -> store_ok SEGS mem (Z_to_bv 64 (fs + j)) 1 = true.
    Hypothesis Wflag : forall p, (0 <= p < N1)%Z -> store_ok SEGS mem (Z_to_bv 64 (fs + FL1 + p)) 1 = true.
    Hypothesis Wframe : forall p j, (0 <= p < N1)%Z -> (0 <= j < 128)%Z -> store_ok SEGS mem (Z_to_bv 64 (fs + FR1 + 128 * p + j)) 1 = true.
    Hypothesis Wshad : forall p j, (0 <= p < N1)%Z -> (0 <= j < 16)%Z -> store_ok SEGS mem (Z_to_bv 64 (SB + (fs + FR1 + 128 * p) / 8 + j)) 1 = true.

    Let h : Z := bv_unsigned hint.
    Definition pos1 (i : Z) : Z := ((h + i) mod N1)%Z.
    Definition ff1 (p : Z) : Z := (fs + FR1 + 128 * p)%Z.

    #[using="Type"] Lemma lit_5bfcc1 : v_addi (0x3ee8c : word) 4 = Z_to_bv 64 0x3ee90. Proof. apply bv_eq; vm_compute; reflexivity. Qed.
    #[using="Type"] Lemma ret_ok_5bfcc1 : ret_ok (Z_to_bv 64 0x3ee90). Proof. apply ret_ok_even. vm_compute. reflexivity. Qed.
    #[using="Type"] Lemma lit_5c0d81 : v_addi (0x3efb0 : word) 4 = Z_to_bv 64 0x3efb4. Proof. apply bv_eq; vm_compute; reflexivity. Qed.
    #[using="Type"] Lemma ret_ok_5c0d81 : ret_ok (Z_to_bv 64 0x3efb4). Proof. apply ret_ok_even. vm_compute. reflexivity. Qed.

    Ltac wz1 T V := progress (replace T with (Z_to_bv 64 V) by (apply bv_eq; vm_compute; reflexivity)).
    Ltac msd11 F D a v Hbase SOK :=
      mstep ltac:(eapply (step_sd_at _ _ _ _ _ _ _ _ _ (Z_to_bv 64 a) v F eq_refl D);
                   [ gr; rewrite ?Hbase; imm_norm; rewrite ?v_addi_any; apply (f_equal (Z_to_bv 64)); lia
                   | gr; first [reflexivity | assumption | symmetry; assumption]
                   | SOK ]).
    Ltac stk81 := pose proof HU; apply store_ok8_bytes; [lia|lia|];
                 intros j Hj; repeat apply store_ok1_wbytes; apply (s_stk _ _ _ _ _ _ _ _ _ H); unfold SM_FRAME; lia.

    (* [comment removed for export] *)
    Definition t_keep1 (r : reg) : bool := negb (tls_clob r || bv_eqb r 1 || bv_eqb r 2 || bv_eqb r 8 || bv_eqb r 10)%bool.

    #[using="fs ctx thr db beg a2v a3v H H01 H02 H04 hint h"] Lemma blk_PT1 :
      exists regs m,
        msteps SEGS (mkst regs0 (0x3ee6c : word) mem rom) (mkst regs (0x3ee90 : word) m rom)
        /\ getr regs 2 = Z_to_bv 64 (usp - 32) /\ getr regs 8 = Z_to_bv 64 usp /\ getr regs 10 = Z_to_bv 64 TP
        /\ getr regs 4 = Z_to_bv 64 TP
        /\ (forall r, t_keep1 r = true -> getr regs r = getr regs0 r)
        /\ sfr m
        /\ (forall x : word, (usp - 32 <= bv_unsigned x)%Z -> m x = m1 x).
    Proof.
      pose proof HU as U.
      (* [comment removed for export] *)
      assert (P : exists q, msteps SEGS (mkst regs0 (0x3ee6c : word) mem rom) (mkst q (0x4428c : word) m1 rom)
                /\ getr q 2 = Z_to_bv 64 (usp - 32) /\ getr q 8 = Z_to_bv 64 usp /\ getr q 10 = Z_to_bv 64 A_DESC
                /\ getr q 1 = Z_to_bv 64 0x3ee90 /\ getr q 4 = Z_to_bv 64 TP
                /\ (forall r : reg, r <> 1 -> r <> 2 -> r <> 8 -> r <> 10 -> getr q r = getr regs0 r)).
      { eexists. split.
        - mstep ltac:(exact (step_addi _ _ _ _ _ _ _ _ _ F_3ee6c eq_refl D_3ee6c)). rewrite H02. zn.
          msd11 F_3ee70 D_3ee70 (usp - 8)%Z ra H02 ltac:(stk81).
          msd11 F_3ee74 D_3ee74 (usp - 16)%Z (getr regs0 8) H02 ltac:(stk81).
          msd11 F_3ee78 D_3ee78 (usp - 24)%Z (getr regs0 9) H02 ltac:(stk81).
          msd11 F_3ee7c D_3ee7c (usp - 32)%Z (getr regs0 18) H02 ltac:(stk81).
          change (wbytes _ _ _) with m1.
          mstep ltac:(exact (step_addi _ _ _ _ _ _ _ _ _ F_3ee80 eq_refl D_3ee80)). gr. zn.
          mstep ltac:(eapply (step_auipc_at _ _ _ _ _ _ _ _ (Z_to_bv 64 0xabe84) F_3ee84 eq_refl D_3ee84);
                       [reflexivity | apply bv_eq; vm_compute; reflexivity]).
          mstep ltac:(exact (step_addi _ _ _ _ _ _ _ _ _ F_3ee88 eq_refl D_3ee88)). gr. zn.
          mstep ltac:(eapply (step_jal_link _ _ _ _ _ _ _ _ F_3ee8c eq_refl D_3ee8c)). rewrite lit_5bfcc1.
          apply mst_refl.
        - gr. repeat split; try (apply (f_equal (Z_to_bv 64)); lia); try reflexivity; try assumption.
          intros r N1 N2 N8 N10. repeat (rewrite getr_other by congruence). reflexivity. }
      destruct P as (q & MP & Q2 & Q8 & Q10 & Q1 & Q4 & QK).
      destruct (tls_run m1 rom (usp - 32) ctx thr db beg a2v a3v tls_m1 q (Z_to_bv 64 0x3ee90) ret_ok_5bfcc1 Q1 Q2 Q4 Q10)
        as (q2 & m2 & MT & T10 & T2 & T1 & TK & TM1 & TM2 & TM3).
      exists q2, m2. split.
      { eapply msteps_trans; [exact MP|]. replace (Z_to_bv 64 0x3ee90) with (0x3ee90 : word) in MT by (apply bv_eq; reflexivity). exact MT. }
      split; [exact T2|]. split; [rewrite TK by reflexivity; exact Q8|]. split; [exact T10|].
      split; [rewrite TK by reflexivity; exact Q4|]. split.
      { intros r Hr. unfold t_keep1 in Hr. apply negb_true_iff in Hr.
        apply orb_false_iff in Hr as [Hr K10]. apply orb_false_iff in Hr as [Hr K8].
        apply orb_false_iff in Hr as [Hr K2]. apply orb_false_iff in Hr as [Hr K1].
        rewrite TK by exact Hr. apply QK; intros ->; discriminate. }
      split.
      { destruct m1_sfr as (F1 & F2 & F3). unfold TLS_FRAME in TM1. split; [|split].
        - intros x Hx. rewrite TM1 by (unfold SM_FRAME in Hx; lia). apply F1. exact Hx.
        - intros x Hx. apply TM2. apply F2. exact Hx.
        - intros x Hx. apply TM3. apply F3. exact Hx. }
      intros x Hx. apply TM1. lia.
    Qed.

    (* [comment removed for export] *)
    Definition a_clob1 (r : reg) : bool :=
      (bv_eqb r 9 || bv_eqb r 10 || bv_eqb r 11 || bv_eqb r 12 || bv_eqb r 13 || bv_eqb r 14 || bv_eqb r 15 || bv_eqb r 16 || bv_eqb r 18)%bool.

    #[using="ctx thr db beg a2v a3v H Hhint"] Lemma blk_A1 : forall regs m,
      sfr m -> getr regs 10 = Z_to_bv 64 TP ->
      exists regs',
        msteps SEGS (mkst regs (0x3ee90 : word) m rom) (mkst regs' (0x3ef00 : word) m rom)
        /\ getr regs' 9 = Z_to_bv 64 fs /\ getr regs' 18 = Z_to_bv 64 20
        /\ getr regs' 10 = Z_to_bv 64 (N1 - 0) /\ getr regs' 12 = Z_to_bv 64 (h + 0)
        /\ getr regs' 13 = Z_to_bv 64 (fs + FL1) /\ getr regs' 14 = Z_to_bv 64 (N1 - 1)
        /\ getr regs' 11 = Z_to_bv 64 (fs + 4096)
        /\ (forall r, a_clob1 r = false -> getr regs' r = getr regs r).
    Proof.
      intros regs m FR H10. pose proof HU as U. pose proof HF as (F1 & F2 & F3 & F4). unfold FS_AREA, TP in *.
      pose proof (s_fs _ _ _ _ _ _ _ _ _ H) as Cfs. pose proof (s_gc _ _ _ _ _ _ _ _ _ H) as Cgc. pose proof (s_ssl _ _ _ _ _ _ _ _ _ H) as Cssl.
      pose proof Hhint as Ch. unfold cell, TP in Cfs, Cgc, Cssl, Ch.
      rewrite <- (rdn_sfr m) in Cfs by (first [exact FR | cbn; unfold SM_FRAME; lia]).
      rewrite <- (rdn_sfr m) in Cgc by (first [exact FR | cbn; unfold SM_FRAME; lia]).
      rewrite <- (rdn_sfr m) in Cssl by (first [exact FR | cbn; unfold SM_FRAME; lia]).
      rewrite <- (rdn_sfr m) in Ch by (first [exact FR | cbn; unfold SM_FRAME; lia]).
      eexists. split.
      - mld F_3ee90 D_3ee90 fs Cfs H10.
        mstep ltac:(eapply (step_beq_ft _ _ _ _ _ _ _ _ _ F_3ee94 eq_refl D_3ee94); gr; rewrite getr_zero; br_eq).
        mstep ltac:(eapply (@step_lbu _ _ _ _ _ _ _ _ _ _ (Z_to_bv 8 0) F_3ee98 eq_refl D_3ee98); gr; imm_norm; zn; exact Cgc).
        change (bv_unsigned (Z_to_bv 8 0)) with 0%Z.
        mld F_3ee9c D_3ee9c 20%Z Cssl H10.
        mstep ltac:(eapply (step_beq_tk _ _ _ _ _ _ _ _ _ F_3eea0 eq_refl D_3eea0); gr; rewrite getr_zero; br_eq).
        mstep ltac:(exact (step_addi _ _ _ _ _ _ _ _ _ F_3eeb0 eq_refl D_3eeb0)). gr. zn.
        mstep ltac:(exact (step_addi _ _ _ _ _ _ _ _ _ F_3eeb4 eq_refl D_3eeb4)). rewrite getr_zero. zn.
        mstep ltac:(exact (step_sll _ _ _ _ _ _ _ _ _ F_3eeb8 eq_refl D_3eeb8)). gr.
        wz1 (v_sll (Z_to_bv 64 1) (Z_to_bv 64 (20 + -7))) 8192%Z.
        mstep ltac:(exact (step_addiw _ _ _ _ _ _ _ _ _ F_3eebc eq_refl D_3eebc)). gr. imm_norm.
        wz1 (v_addiw (Z_to_bv 64 8192) 0) 8192%Z.
        mstep ltac:(eapply (step_bge_ft _ _ _ _ _ _ _ _ _ F_3eec0 eq_refl D_3eec0); gr; rewrite getr_zero; apply c_lts_pos_ft; lia).
        mstep ltac:(eapply (step_lui_at _ _ _ _ _ _ _ _ (Z_to_bv 64 4096) F_3eec4 eq_refl D_3eec4); reflexivity).
        mstep ltac:(exact (step_addi _ _ _ _ _ _ _ _ _ F_3eec8 eq_refl D_3eec8)). gr. zn.
        mstep ltac:(exact (step_addi _ _ _ _ _ _ _ _ _ F_3eecc eq_refl D_3eecc)). rewrite getr_zero. zn.
        mstep ltac:(exact (step_addi _ _ _ _ _ _ _ _ _ F_3eed0 eq_refl D_3eed0)). rewrite getr_zero, k_m1_val.
        mstep ltac:(exact (step_sll _ _ _ _ _ _ _ _ _ F_3eed4 eq_refl D_3eed4)). gr.
        wz1 (v_sll (Z_to_bv 64 512) (Z_to_bv 64 (20 + -15))) 16384%Z.
        mstep ltac:(eapply (@step_ld _ _ _ _ _ _ _ _ _ _ _ hint F_3eed8 eq_refl D_3eed8);
                     [ gr; imm_norm; zn; exact Ch | apply bytes_le_to_Z_8 ]).
        rewrite (zbv_self' hint). fold h.
        mstep ltac:(exact (step_sll _ _ _ _ _ _ _ _ _ F_3eedc eq_refl D_3eedc)). gr.
        wz1 (v_sll (Z_to_bv 64 (2 ^ 64 - 1)) (Z_to_bv 64 (20 + -7))) (2 ^ 64 - 8192)%Z.
        mstep ltac:(exact (step_addi _ _ _ _ _ _ _ _ _ F_3eee0 eq_refl D_3eee0)). gr. zn.
        mstep ltac:(exact (step_add _ _ _ _ _ _ _ _ _ F_3eee4 eq_refl D_3eee4)). gr. rewrite v_add_zbv by lia.
        mstep ltac:(exact (step_add _ _ _ _ _ _ _ _ _ F_3eee8 eq_refl D_3eee8)). gr. rewrite v_add_zbv by lia.
        mstep ltac:(exact (step_xori _ _ _ _ _ _ _ _ _ F_3eeec eq_refl D_3eeec)). gr. imm_norm.
        wz1 (v_xori (Z_to_bv 64 (2 ^ 64 - 8192)) (-1)) 8191%Z.
        mstep ltac:(exact (step_slli _ _ _ _ _ _ _ _ _ F_3eef0 eq_refl D_3eef0)). gr. imm_norm.
        wz1 (v_slli (Z_to_bv 64 (8192 + -1)) 32) (8191 * 2 ^ 32)%Z.
        mstep ltac:(exact (PropExec.step_srli _ _ _ _ _ _ _ _ _ F_3eef4 eq_refl D_3eef4)). gr. imm_norm.
        wz1 (v_srli (Z_to_bv 64 (8191 * 2 ^ 32)) 32) 8191%Z.
        mstep ltac:(exact (step_add _ _ _ _ _ _ _ _ _ F_3eef8 eq_refl D_3eef8)). gr. rewrite v_add_any.
        mstep ltac:(exact (step_addi _ _ _ _ _ _ _ _ _ F_3eefc eq_refl D_3eefc)). gr. rewrite v_addi_any.
        apply mst_refl.
      - gr. unfold N1, FL1. repeat split; try (apply (f_equal (Z_to_bv 64)); lia); try reflexivity.
        intros r Hr. unfold a_clob1 in Hr.
        repeat (rewrite getr_other by (intros ->; cbn in Hr; discriminate)). reflexivity.
    Qed.

    (* [comment removed for export] *)
    Let i0 : Z := ((p0 - h) mod N1)%Z.
    #[using="Type"] Lemma i0_rng1 : (0 <= i0 < N1)%Z. Proof. unfold i0, N1. apply Z.mod_pos_bound. lia. Qed.
    #[using="FL Hp0"] Lemma pos_i01 : pos1 i0 = p0.
    Proof.
      unfold pos1, i0, N1. rewrite Zplus_mod_idemp_r. replace (h + (p0 - h))%Z with p0 by lia.
      apply Z.mod_small. unfold N1 in Hp0. lia.
    Qed.
    #[using="p0 i0"] Lemma pos_rng1 : forall i, (0 <= pos1 i < N1)%Z. Proof. intros i. unfold pos1, N1. apply Z.mod_pos_bound. lia. Qed.

    Definition l_clob1 (r : reg) : bool := (bv_eqb r 5 || bv_eqb r 10 || bv_eqb r 12 || bv_eqb r 15 || bv_eqb r 17)%bool.

    #[using="ctx thr db beg a2v a3v H Hflags Hp0"] Lemma blk_L1 : forall (k : nat) i regs m,
      (i + Z.of_nat k = i0)%Z -> (0 <= i)%Z -> sfr m ->
      getr regs 10 = Z_to_bv 64 (N1 - i) -> getr regs 12 = Z_to_bv 64 (h + i) ->
      getr regs 13 = Z_to_bv 64 (fs + FL1) -> getr regs 14 = Z_to_bv 64 (N1 - 1) ->
      exists i' regs',
        (i <= i' <= i0)%Z /\ bv_unsigned (FL (pos1 i')) = 0%Z
        /\ msteps SEGS (mkst regs (0x3ef00 : word) m rom) (mkst regs' (0x3ef78 : word) m rom)
        /\ getr regs' 12 = Z_to_bv 64 (h + i') /\ getr regs' 17 = Z_to_bv 64 (pos1 i')
        /\ getr regs' 15 = Z_to_bv 64 (fs + FL1 + pos1 i')
        /\ (forall r, l_clob1 r = false -> getr regs' r = getr regs r).
    Proof.
      pose proof HU as U. pose proof HF as (F1 & F2 & F3 & F4). unfold FS_AREA in *. pose proof i0_rng1 as I0. pose proof Hp0 as [P0 P1].
      unfold N1 in *.
      unfold FL1 in *.
      induction k as [|k IH]; intros i regs m Hk Hi FR H10 H12 H13 H14.
      - (* [comment removed for export] *)
        cbn [Z.of_nat] in Hk. rewrite Z.add_0_r in Hk. subst i.
        pose proof (pos_rng1 i0) as PR. unfold N1 in PR.
        pose proof (Hflags (pos1 i0) PR) as CF. rewrite <- (rdn_sfr m) in CF by (first [exact FR | cbn; unfold SM_FRAME, FL1; lia]).
        exists i0. eexists. split; [lia|]. split; [rewrite pos_i01; exact P1|]. split.
        + mstep ltac:(exact (step_and _ _ _ _ _ _ _ _ _ F_3ef00 eq_refl D_3ef00)). gr. rewrite H12, H14.
          change (8192 - 1)%Z with (2 ^ 13 - 1)%Z. rewrite v_and_mask by lia. change (2 ^ 13)%Z with 8192%Z. fold N1. fold (pos1 i0).
          mstep ltac:(exact (step_add _ _ _ _ _ _ _ _ _ F_3ef04 eq_refl D_3ef04)). gr. rewrite H13. unfold FL1. rewrite v_add_zbv by lia.
          mstep ltac:(eapply (@step_lbu _ _ _ _ _ _ _ _ _ _ (FL (pos1 i0)) F_3ef08 eq_refl D_3ef08); gr; imm_norm; zn; rewrite ?Z.add_0_r; unfold FL1 in CF; exact CF).
          replace (bv_unsigned (FL (pos1 i0))) with 0%Z by (rewrite pos_i01, P1; reflexivity).
          mstep ltac:(eapply (step_beq_tk _ _ _ _ _ _ _ _ _ F_3ef0c eq_refl D_3ef0c); gr; rewrite getr_zero; br_eq).
          apply mst_refl.
        + gr. unfold FL1. repeat split; try (apply (f_equal (Z_to_bv 64)); lia); try reflexivity; try assumption.
          intros r Hr. unfold l_clob1 in Hr.
          repeat (rewrite getr_other by (intros ->; cbn in Hr; discriminate)). reflexivity.
      - (* [comment removed for export] *)
        pose proof (pos_rng1 i) as PR. unfold N1 in PR.
        pose proof (Hflags (pos1 i) PR) as CF. rewrite <- (rdn_sfr m) in CF by (first [exact FR | cbn; unfold SM_FRAME, FL1; lia]).
        pose proof (bv_unsigned_in_range 8 (FL (pos1 i))) as BR. change (bv_modulus 8) with 256%Z in BR.
        destruct (Z.eq_dec (bv_unsigned (FL (pos1 i))) 0) as [Z0|NZ].
        + exists i. eexists. split; [lia|]. split; [exact Z0|]. split.
          * mstep ltac:(exact (step_and _ _ _ _ _ _ _ _ _ F_3ef00 eq_refl D_3ef00)). gr. rewrite H12, H14.
            change (8192 - 1)%Z with (2 ^ 13 - 1)%Z. rewrite v_and_mask by lia. change (2 ^ 13)%Z with 8192%Z. fold N1. fold (pos1 i).
            mstep ltac:(exact (step_add _ _ _ _ _ _ _ _ _ F_3ef04 eq_refl D_3ef04)). gr. rewrite H13. unfold FL1. rewrite v_add_zbv by lia.
            mstep ltac:(eapply (@step_lbu _ _ _ _ _ _ _ _ _ _ (FL (pos1 i)) F_3ef08 eq_refl D_3ef08); gr; imm_norm; zn; rewrite ?Z.add_0_r; unfold FL1 in CF; exact CF).
            rewrite Z0.
            mstep ltac:(eapply (step_beq_tk _ _ _ _ _ _ _ _ _ F_3ef0c eq_refl D_3ef0c); gr; rewrite getr_zero; br_eq).
            apply mst_refl.
          * gr. unfold FL1. repeat split; try (apply (f_equal (Z_to_bv 64)); lia); try reflexivity; try assumption.
            intros r Hr. unfold l_clob1 in Hr.
            repeat (rewrite getr_other by (intros ->; cbn in Hr; discriminate)). reflexivity.
        + assert (NI : i <> i0) by (intros ->; rewrite pos_i01 in NZ; exact (NZ P1)).
          edestruct (IH (i + 1)%Z
            (regupd (regupd (regupd (regupd (regupd regs 17 (Z_to_bv 64 (pos1 i))) 15 (Z_to_bv 64 (fs + FL1 + pos1 i)))
               5 (Z_to_bv 64 (bv_unsigned (FL (pos1 i))))) 10 (Z_to_bv 64 (8192 - i - 1))) 12 (Z_to_bv 64 (h + i + 1))) m)
            as (i' & regs' & R1 & R2 & M & Q12 & Q17 & Q15 & QK); try lia; try exact FR.
          1-4: gr; first [assumption | apply (f_equal (Z_to_bv 64)); lia].
          exists i', regs'. split; [lia|]. split; [exact R2|]. split.
          * mstep ltac:(exact (step_and _ _ _ _ _ _ _ _ _ F_3ef00 eq_refl D_3ef00)). gr. rewrite H12, H14.
            change (8192 - 1)%Z with (2 ^ 13 - 1)%Z. rewrite v_and_mask by lia. change (2 ^ 13)%Z with 8192%Z. fold N1. fold (pos1 i).
            mstep ltac:(exact (step_add _ _ _ _ _ _ _ _ _ F_3ef04 eq_refl D_3ef04)). gr. rewrite H13. rewrite v_add_zbv by (unfold FL1; lia).
            mstep ltac:(eapply (@step_lbu _ _ _ _ _ _ _ _ _ _ (FL (pos1 i)) F_3ef08 eq_refl D_3ef08); gr; imm_norm; zn; rewrite ?Z.add_0_r; exact CF).
            mstep ltac:(eapply (step_beq_ft _ _ _ _ _ _ _ _ _ F_3ef0c eq_refl D_3ef0c); gr; rewrite getr_zero; br_eq).
            mstep ltac:(exact (step_addiw _ _ _ _ _ _ _ _ _ F_3ef10 eq_refl D_3ef10)). gr. rewrite H10. imm_norm.
            rewrite v_addiw_small by lia.
            mstep ltac:(exact (step_addi _ _ _ _ _ _ _ _ _ F_3ef14 eq_refl D_3ef14)). gr. rewrite H12, v_addi_any.
            mstep ltac:(eapply (step_bne_tk _ _ _ _ _ _ _ _ _ F_3ef18 eq_refl D_3ef18); gr; rewrite getr_zero; br_eq).
            replace (8192 - i + -1)%Z with (8192 - i - 1)%Z by lia. exact M.
          * split; [exact Q12|]. split; [exact Q17|]. split; [exact Q15|].
            intros r Hr. rewrite (QK r Hr). unfold l_clob1 in Hr.
            repeat (rewrite getr_other by (intros ->; cbn in Hr; discriminate)). reflexivity.
    Qed.

    (* [comment removed for export] *)
    (* [comment removed for export] *)
    Definition WR1 (m : word -> option byte) (i p : Z) : word -> option byte :=
      wbytes (wbytes (wbytes (wbytes (wbytes (wbytes m
        (Z_to_bv 64 (fs + 8)) (word_to_le_bytes 8 (Z_to_bv 64 (h + i + 1))))
        (Z_to_bv 64 (fs + FL1 + p)) (word_to_le_bytes 1 (Z_to_bv 64 1)))
        (Z_to_bv 64 (ff1 p + 24)) (word_to_le_bytes 8 (Z_to_bv 64 usp)))
        (Z_to_bv 64 (ff1 p + 120)) (word_to_le_bytes 8 (Z_to_bv 64 (fs + FL1 + p))))
        (Z_to_bv 64 (SB + ff1 p / 8)) (word_to_le_bytes 8 (Z_to_bv 64 0)))
        (Z_to_bv 64 (SB + ff1 p / 8 + 8)) (word_to_le_bytes 8 (Z_to_bv 64 0)).

    #[using="Type"] Lemma WR_agree1 : forall ma mb i p (x : word), ma x = mb x -> WR1 ma i p x = WR1 mb i p x.
    Proof. intros. unfold WR1. repeat apply wbytes_agree. assumption. Qed.
    #[using="Type"] Lemma WR_keep1 : forall m i p (x : word), m x <> None -> WR1 m i p x <> None.
    Proof. intros. unfold WR1. repeat apply wbytes_keep. assumption. Qed.
    #[using="Type"] Lemma WR_sok1 : forall m i p (x : word), store_ok SEGS m x 1 = true -> store_ok SEGS (WR1 m i p) x 1 = true.
    Proof. intros. unfold WR1. repeat apply store_ok1_wbytes. assumption. Qed.

    #[using="mem rom ctx thr db beg a2v a3v H p0 i0"] Lemma WR_stack1 : forall m i p a, (0 <= p < N1)%Z -> (usp - 32 <= a)%Z -> (a + 8 <= usp)%Z ->
      rdn SEGS (WR1 m i p) (Z_to_bv 64 a) 8 = rdn SEGS m (Z_to_bv 64 a) 8.
    Proof.
      intros m i p a Hp Ha Hb. pose proof HU as U. pose proof HF as (F1 & F2 & F3 & F4). unfold FS_AREA, N1, ff1, FR1, FL1 in *.
      pose proof SB_val.
      assert (ff_hi : (fs + 1085440 + 128 * p + 128 <= 2 ^ 47)%Z) by lia.
      pose proof (Z.div_pos (fs + 1085440 + 128 * p) 8 ltac:(lia) ltac:(lia)).
      pose proof (Z.div_lt_upper_bound (fs + 1085440 + 128 * p) 8 (2 ^ 44) ltac:(lia) ltac:(lia)).
      unfold WR1, ff1, FL1, FR1. rewrite !rdn_wbytes_out; try reflexivity; len8; rewrite ?zbv_u by (ltac2:(LK.k [@Hp; @Ha; @Hb; @U; @F1; @F2; @ff_hi; @H0; @H1; @H2; @F4]); lia); (ltac2:(LK.k [@Hp; @Ha; @Hb; @U; @F1; @F2; @ff_hi; @H0; @H1; @H2; @F4]); lia).
    Qed.

    Definition f_clob1 (r : reg) : bool :=
      (bv_eqb r 1 || bv_eqb r 2 || bv_eqb r 5 || bv_eqb r 8 || bv_eqb r 9 || bv_eqb r 10 || bv_eqb r 11 || bv_eqb r 12
       || bv_eqb r 13 || bv_eqb r 14 || bv_eqb r 15 || bv_eqb r 16 || bv_eqb r 17 || bv_eqb r 18)%bool.

    #[using="ctx thr db beg a2v a3v H Hret p0 Whint Wflag Wframe Wshad i0"] Lemma blk_F1 : forall regs m i p,
      sfr m -> (forall x : word, (usp - 32 <= bv_unsigned x)%Z -> m x = m1 x) ->
      (0 <= p < N1)%Z -> (0 <= i < N1)%Z ->
      getr regs 2 = Z_to_bv 64 (usp - 32) -> getr regs 8 = Z_to_bv 64 usp -> getr regs 9 = Z_to_bv 64 fs ->
      getr regs 18 = Z_to_bv 64 20 -> getr regs 11 = Z_to_bv 64 (fs + 4096) ->
      getr regs 12 = Z_to_bv 64 (h + i) -> getr regs 17 = Z_to_bv 64 p -> getr regs 15 = Z_to_bv 64 (fs + FL1 + p) ->
      exists regs',
        msteps SEGS (mkst regs (0x3ef78 : word) m rom) (mkst regs' ra (WR1 m i p) rom)
        /\ getr regs' 10 = Z_to_bv 64 (ff1 p) /\ getr regs' 2 = Z_to_bv 64 usp /\ getr regs' 1 = ra
        /\ getr regs' 8 = getr regs0 8 /\ getr regs' 9 = getr regs0 9 /\ getr regs' 18 = getr regs0 18
        /\ (forall r, f_clob1 r = false -> getr regs' r = getr regs r).
    Proof.
      intros regs m i p FR AG Hp Hi H2 H8 H9 H18 H11 H12 H17 H15.
      pose proof HU as U. pose proof HF as (F1 & F2 & F3 & F4). pose proof SB_val as HSB. unfold FS_AREA, N1, FL1 in *.
      destruct FR as (FRa & FRb & FRc).
      assert (ff_lo : (0x608000 <= ff1 p)%Z) by (unfold ff1, FR1; lia).
      assert (ff_hi : (ff1 p + 128 <= 2 ^ 47)%Z) by (unfold ff1, FR1; lia).
      pose proof (Z.div_pos (ff1 p) 8 ltac:(lia) ltac:(lia)) as D1.
      pose proof (Z.div_lt_upper_bound (ff1 p) 8 (2 ^ 44) ltac:(lia) ltac:(lia)) as D2.
      (* [comment removed for export] *)
      assert (RD : forall a v, (usp - 32 <= a)%Z -> (a + 8 <= usp)%Z ->
                rdn SEGS m1 (Z_to_bv 64 a) 8 = Some (word_to_le_bytes 8 v) ->
                rdn SEGS (WR1 m i p) (Z_to_bv 64 a) 8 = Some (word_to_le_bytes 8 v)).
      { intros a v Ha Hb R. rewrite WR_stack1 by (unfold N1; lia). rewrite <- R. apply rdn_ext; [rewrite zbv_u by lia; cbn; lia|].
        intros x Hx. rewrite zbv_u in Hx by lia. apply AG. lia. }
      pose proof (RD (usp - 8)%Z _ ltac:(lia) ltac:(lia) rd1_8) as R8. pose proof (RD (usp - 16)%Z _ ltac:(lia) ltac:(lia) rd1_16) as R16.
      pose proof (RD (usp - 24)%Z _ ltac:(lia) ltac:(lia) rd1_24) as R24. pose proof (RD (usp - 32)%Z _ ltac:(lia) ltac:(lia) rd1_32) as R32.
      (* [comment removed for export] *)
      set (m4 := wbytes (wbytes (wbytes (wbytes m
        (Z_to_bv 64 (fs + 8)) (word_to_le_bytes 8 (Z_to_bv 64 (h + i + 1))))
        (Z_to_bv 64 (fs + 20480 + p)) (word_to_le_bytes 1 (Z_to_bv 64 1)))
        (Z_to_bv 64 (ff1 p + 24)) (word_to_le_bytes 8 (Z_to_bv 64 usp)))
        (Z_to_bv 64 (ff1 p + 120)) (word_to_le_bytes 8 (Z_to_bv 64 (fs + 20480 + p)))).
      assert (C4 : cells m4).
      { pose proof (s_cells _ _ _ _ _ _ _ _ _ H) as C. unfold cells, cell in *. unfold m4.
        rewrite !rdn_wbytes_out; len8; rewrite ?zbv_u by (ltac2:(LK.k [@F1; @F2; @Hp; @U; @ff_lo; @ff_hi]); lia); try (cbn; unfold ff1, FR1 in *; (ltac2:(LK.k [@F1; @F2; @Hp; @U; @ff_lo; @ff_hi]); lia)).
        rewrite !(rdn_sfr m) by (first [split; [exact FRa|split; [exact FRb|exact FRc]] | cbn; unfold SM_FRAME; lia]). exact C. }
      (* [comment removed for export] *)
      assert (P1 : exists r1,
        msteps SEGS (mkst regs (0x3ef78 : word) m rom) (mkst r1 (0x3f510 : word) m4 rom)
        /\ getr r1 10 = Z_to_bv 64 (ff1 p) /\ getr r1 1 = Z_to_bv 64 0x3efb4 /\ getr r1 2 = Z_to_bv 64 (usp - 32)
        /\ getr r1 9 = Z_to_bv 64 (ff1 p)
        /\ (forall r : reg, r <> 1 -> r <> 9 -> r <> 10 -> r <> 11 -> r <> 12 -> r <> 13 -> r <> 17 -> getr r1 r = getr regs r)).
      { eexists. split.
        - mstep ltac:(exact (step_addi _ _ _ _ _ _ _ _ _ F_3ef78 eq_refl D_3ef78)). gr. rewrite H12, v_addi_any.
          mstep ltac:(exact (step_addi _ _ _ _ _ _ _ _ _ F_3ef7c eq_refl D_3ef7c)). rewrite getr_zero. zn.
          mstep ltac:(exact (step_addi _ _ _ _ _ _ _ _ _ F_3ef80 eq_refl D_3ef80)). gr. rewrite H18. zn.
          mstep ltac:(exact (step_slli _ _ _ _ _ _ _ _ _ F_3ef84 eq_refl D_3ef84)). gr. rewrite H17. imm_norm.
          rewrite (v_slli_zbv p 7) by lia.
          msd11 F_3ef88 D_3ef88 (fs + 8)%Z (Z_to_bv 64 (h + i + 1)) H9
               ltac:(apply store_ok8_bytes; [lia|lia|]; intros j Hj; apply FRc; replace (fs + 8 + j)%Z with (fs + (8 + j))%Z by lia; apply Whint; lia).
          mstep ltac:(eapply (step_sb _ _ _ _ _ _ _ _ _ F_3ef8c eq_refl D_3ef8c);
                       gr; rewrite H15; imm_norm; zn; rewrite ?Z.add_0_r; apply store_ok1_wbytes; apply FRc; apply Wflag; lia).
          gr. rewrite H15. zn. rewrite ?Z.add_0_r.
          mstep ltac:(exact (step_sll _ _ _ _ _ _ _ _ _ F_3ef90 eq_refl D_3ef90)). gr.
          wz1 (v_sll (Z_to_bv 64 1) (Z_to_bv 64 (20 + -5))) 32768%Z.
          mstep ltac:(exact (step_sll _ _ _ _ _ _ _ _ _ F_3ef94 eq_refl D_3ef94)). gr. rewrite H18.
          wz1 (v_sll (Z_to_bv 64 1) (Z_to_bv 64 20)) (2 ^ 20)%Z.
          mstep ltac:(exact (step_add _ _ _ _ _ _ _ _ _ F_3ef98 eq_refl D_3ef98)). gr. rewrite H11, v_add_zbv by lia.
          mstep ltac:(exact (step_add _ _ _ _ _ _ _ _ _ F_3ef9c eq_refl D_3ef9c)). gr. rewrite v_add_zbv by lia.
          mstep ltac:(exact (step_add _ _ _ _ _ _ _ _ _ F_3efa0 eq_refl D_3efa0)). gr. rewrite v_add_zbv by lia.
          change (2 ^ 7)%Z with 128%Z. replace (fs + 4096 + 32768 + (2 ^ 20 + p * 128))%Z with (ff1 p) by (unfold ff1, FR1; lia).
          msd11 F_3efa4 D_3efa4 (ff1 p + 24)%Z (Z_to_bv 64 usp) H8
               ltac:(apply store_ok8_bytes; [lia|lia|]; intros j Hj; repeat apply store_ok1_wbytes; apply FRc;
                     unfold ff1, FR1; replace (fs + 1085440 + 128 * p + 24 + j)%Z with (fs + 1085440 + 128 * p + (24 + j))%Z by lia; apply Wframe; lia).
          msd11 F_3efa8 D_3efa8 (ff1 p + 120)%Z (Z_to_bv 64 (fs + 20480 + p)) H8
               ltac:(apply store_ok8_bytes; [lia|lia|]; intros j Hj; repeat apply store_ok1_wbytes; apply FRc;
                     unfold ff1, FR1; replace (fs + 1085440 + 128 * p + 120 + j)%Z with (fs + 1085440 + 128 * p + (120 + j))%Z by lia; apply Wframe; lia).
          change (wbytes _ _ _) with m4.
          mstep ltac:(exact (step_addi _ _ _ _ _ _ _ _ _ F_3efac eq_refl D_3efac)). gr. zn. rewrite ?Z.add_0_r.
          mstep ltac:(eapply (step_jal_link _ _ _ _ _ _ _ _ F_3efb0 eq_refl D_3efb0)). rewrite lit_5c0d81.
          apply mst_refl.
        - gr. repeat split; try reflexivity; try assumption; try (apply (f_equal (Z_to_bv 64)); lia).
          intros r N1 N9 N10 N11 N12 N13 N17. repeat (rewrite getr_other by congruence). reflexivity. }
      destruct P1 as (r1 & M1 & P10 & P1ra & P2 & P9 & PK).
      destruct (mem_to_shadow_5e918 rom r1 m4 (ff1 p) (Z_to_bv 64 0x3efb4) C4 ltac:(lia)
                  ltac:(apply (in_mem_frame fs (ff1 p) 128 HFB); [lia|unfold ff1, FR1; lia|unfold ff1, FR1 in *; unfold FS_AREA in *; lia|unfold FS_AREA in *; lia|lia])
                  P10 P1ra ret_ok_5c0d81)
        as (q & MQ & Q10 & QK).
      assert (Q2 : getr q 2 = Z_to_bv 64 (usp - 32)) by (rewrite QK by reflexivity; exact P2).
      assert (Q9 : getr q 9 = Z_to_bv 64 (ff1 p)) by (rewrite QK by reflexivity; exact P9).
      eexists. split.
      - eapply msteps_trans; [exact M1|]. eapply msteps_trans; [exact MQ|].
        replace (Z_to_bv 64 0x3efb4) with (0x3efb4 : word) by (apply bv_eq; reflexivity).
        mstep ltac:(exact (step_addi _ _ _ _ _ _ _ _ _ F_3efb4 eq_refl D_3efb4)). gr. rewrite Q10. zn. rewrite ?Z.add_0_r.
        mstep ltac:(exact (step_addi _ _ _ _ _ _ _ _ _ F_3efb8 eq_refl D_3efb8)). gr. rewrite Q9. zn. rewrite ?Z.add_0_r.
        mstep ltac:(exact (step_addi _ _ _ _ _ _ _ _ _ F_3efbc eq_refl D_3efbc)). rewrite getr_zero. zn.
        msd11 F_3efc0 D_3efc0 (SB + ff1 p / 8)%Z (Z_to_bv 64 0) Q2
             ltac:(apply store_ok8_bytes; [lia|lia|]; intros j Hj; unfold m4; repeat apply store_ok1_wbytes; apply FRc;
                   unfold ff1, FR1; apply Wshad; lia).
        msd11 F_3efc4 D_3efc4 (SB + ff1 p / 8 + 8)%Z (Z_to_bv 64 0) Q2
             ltac:(apply store_ok8_bytes; [lia|lia|]; intros j Hj; unfold m4; repeat apply store_ok1_wbytes; apply FRc;
                   unfold ff1, FR1; replace (SB + (fs + 1085440 + 128 * p) / 8 + 8 + j)%Z with (SB + (fs + 1085440 + 128 * p) / 8 + (8 + j))%Z by lia;
                   apply Wshad; lia).
        change (wbytes _ _ _) with (WR1 m i p).
        mstep ltac:(eapply (@step_ld _ _ _ _ _ _ _ _ _ _ _ ra F_3efc8 eq_refl D_3efc8);
                     [ gr; rewrite Q2; imm_norm; zn; replace (usp - 32 + 24)%Z with (usp - 8)%Z by lia; exact R8 | apply bytes_le_to_Z_8 ]).
        mstep ltac:(eapply (@step_ld _ _ _ _ _ _ _ _ _ _ _ (getr regs0 8) F_3efcc eq_refl D_3efcc);
                     [ gr; rewrite Q2; imm_norm; zn; replace (usp - 32 + 16)%Z with (usp - 16)%Z by lia; exact R16 | apply bytes_le_to_Z_8 ]).
        mstep ltac:(eapply (@step_ld _ _ _ _ _ _ _ _ _ _ _ (getr regs0 9) F_3efd0 eq_refl D_3efd0);
                     [ gr; rewrite Q2; imm_norm; zn; replace (usp - 32 + 8)%Z with (usp - 24)%Z by lia; exact R24 | apply bytes_le_to_Z_8 ]).
        mstep ltac:(eapply (@step_ld _ _ _ _ _ _ _ _ _ _ _ (getr regs0 18) F_3efd4 eq_refl D_3efd4);
                     [ gr; rewrite Q2; imm_norm; zn; rewrite ?Z.add_0_r; exact R32 | apply bytes_le_to_Z_8 ]).
        mstep ltac:(exact (step_addi _ _ _ _ _ _ _ _ _ F_3efd8 eq_refl D_3efd8)). gr. rewrite Q2. zn.
        replace (usp - 32 + 32)%Z with usp by lia.
        eapply mst_step; [reflexivity | eapply (step_jalr_x0 _ _ _ _ _ _ _ _ ra F_3efdc eq_refl D_3efdc); gr; reflexivity |].
        imm_norm. rewrite Hret. apply mst_refl.
      - gr. repeat split; try reflexivity.
        intros r Hr. unfold f_clob1 in Hr.
        repeat (rewrite getr_other by (intros ->; cbn in Hr; discriminate)).
        rewrite QK by (unfold m2s_clob; repeat match type of Hr with (?a || ?b)%bool = false => apply orb_false_iff in Hr; destruct Hr as [Hr ?] end;
                       repeat match goal with Hb : bv_eqb r _ = false |- _ => rewrite Hb; clear Hb end; reflexivity).
        apply PK; intros ->; cbn in Hr; discriminate.
    Qed.

    (* [comment removed for export] *)
    #[using="ctx thr db beg a2v a3v H Hret H01 H02 H04 p0 Hhint Hflags Hp0 Whint Wflag Wframe Wshad i0"] Theorem sm1_AM :
      exists i p regs' m',
        (0 <= i < N1)%Z /\ p = pos1 i /\ bv_unsigned (FL p) = 0%Z
        /\ msteps SEGS (mkst regs0 (0x3ee6c : word) mem rom) (mkst regs' ra m' rom)
        /\ getr regs' 10 = Z_to_bv 64 (ff1 p) /\ getr regs' 2 = Z_to_bv 64 usp /\ getr regs' 1 = ra
        /\ (forall r, sm_clob r = false -> getr regs' r = getr regs0 r)
        /\ (forall x : word, (bv_unsigned x < usp - SM_FRAME \/ usp <= bv_unsigned x)%Z -> m' x = WR1 mem i p x)
        /\ (forall x, mem x <> None -> m' x <> None)
        /\ (forall x, store_ok SEGS mem x 1 = true -> store_ok SEGS m' x 1 = true).
    Proof.
      pose proof HU as U. pose proof i0_rng1 as I0.
      destruct blk_PT1 as (q1 & m2 & M1 & A2 & A8 & A10 & A4 & AK & FR & AG).
      destruct (blk_A1 q1 m2 FR A10) as (q2 & M2 & B9 & B18 & B10 & B12 & B13 & B14 & B11 & BK).
      destruct (blk_L1 (Z.to_nat i0) 0 q2 m2 ltac:(lia) ltac:(lia) FR B10 B12 B13 B14)
        as (i & q3 & Hi & HZ & M3 & C12 & C17 & C15 & CK).
      assert (C2 : getr q3 2 = Z_to_bv 64 (usp - 32)) by (rewrite CK, BK by reflexivity; exact A2).
      assert (C8 : getr q3 8 = Z_to_bv 64 usp) by (rewrite CK, BK by reflexivity; exact A8).
      assert (C9 : getr q3 9 = Z_to_bv 64 fs) by (rewrite CK by reflexivity; exact B9).
      assert (C18 : getr q3 18 = Z_to_bv 64 20) by (rewrite CK by reflexivity; exact B18).
      assert (C11 : getr q3 11 = Z_to_bv 64 (fs + 4096)) by (rewrite CK by reflexivity; exact B11).
      pose proof (pos_rng1 i) as PR.
      destruct (blk_F1 q3 m2 i (pos1 i) FR AG PR ltac:(lia) C2 C8 C9 C18 C11 C12 C17 C15)
        as (q4 & M4 & D10 & D2 & D1 & D8 & D9 & D18 & DK).
      exists i, (pos1 i), q4, (WR1 m2 i (pos1 i)).
      split; [lia|]. split; [reflexivity|]. split; [exact HZ|]. split.
      { eapply msteps_trans; [exact M1|]. eapply msteps_trans; [exact M2|]. eapply msteps_trans; [exact M3|]. exact M4. }
      split; [exact D10|]. split; [exact D2|]. split; [exact D1|]. split.
      { intros r Hr.
        destruct (bv_eq_dec _ r 1) as [-> | N1]; [rewrite D1; symmetry; exact H01|].
        destruct (bv_eq_dec _ r 2) as [-> | N2]; [rewrite D2; symmetry; exact H02|].
        destruct (bv_eq_dec _ r 8) as [-> | N8]; [exact D8|].
        destruct (bv_eq_dec _ r 9) as [-> | N9]; [exact D9|].
        destruct (bv_eq_dec _ r 18) as [-> | N18]; [exact D18|].
        assert (NE : forall k : reg, r <> k -> bv_eqb r k = false) by (intros k Hk; apply bv_eqb_neq; exact Hk).
        pose proof (NE _ N1) as T1. pose proof (NE _ N2) as T2. pose proof (NE _ N8) as T8. pose proof (NE _ N9) as T9. pose proof (NE _ N18) as T18.
        unfold sm_clob in Hr.
        apply orb_false_iff in Hr as [Hr T17]. apply orb_false_iff in Hr as [Hr T16]. apply orb_false_iff in Hr as [Hr T15].
        apply orb_false_iff in Hr as [Hr T14]. apply orb_false_iff in Hr as [Hr T13]. apply orb_false_iff in Hr as [Hr T12].
        apply orb_false_iff in Hr as [Hr T11]. apply orb_false_iff in Hr as [T5 T10].
        rewrite DK by (unfold f_clob1; rewrite ?T1, ?T2, ?T5, ?T8, ?T9, ?T10, ?T11, ?T12, ?T13, ?T14, ?T15, ?T16, ?T17, ?T18; reflexivity).
        rewrite CK by (unfold l_clob1; rewrite ?T5, ?T10, ?T12, ?T15, ?T17; reflexivity).
        rewrite BK by (unfold a_clob1; rewrite ?T9, ?T10, ?T11, ?T12, ?T13, ?T14, ?T15, ?T16, ?T18; reflexivity).
        apply AK. unfold t_keep1, tls_clob. rewrite T10, T11, T12, T13, T1, T2, T8. reflexivity. }
      destruct FR as (FRa & FRb & FRc). split; [|split].
      - intros x Hx. apply WR_agree1. apply FRa. exact Hx.
      - intros x Hx. apply WR_keep1. apply FRb. exact Hx.
      - intros x Hx. apply WR_sok1. apply FRc. exact Hx.
    Qed.
  End C1.
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Section C2.
    Definition N2 : Z := 4096.
    Definition FL2 : Z := 28672.
    Definition FR2 : Z := 2134016.
    Variable hint : word.                (* [comment removed for export] *)
    Variable FL : Z -> byte.             (* [comment removed for export] *)
    Variable p0 : Z.                     (* [comment removed for export] *)
    Hypothesis Hhint : rdn SEGS mem (Z_to_bv 64 (fs + 16)) 8 = Some (word_to_le_bytes 8 hint).
    Hypothesis Hflags : forall p, (0 <= p < N2)%Z -> rdn SEGS mem (Z_to_bv 64 (fs + FL2 + p)) 1 = Some [FL p].
    Hypothesis Hp0 : (0 <= p0 < N2)%Z /\ bv_unsigned (FL p0) = 0%Z.
    Hypothesis Whint : forall j, (16 <= j < 24)%Z -> store_ok SEGS mem (Z_to_bv 64 (fs + j)) 1 = true.
    Hypothesis Wflag : forall p, (0 <= p < N2)%Z -> store_ok SEGS mem (Z_to_bv 64 (fs + FL2 + p)) 1 = true.
    Hypothesis Wframe : forall p j, (0 <= p < N2)%Z -> (0 <= j < 256)%Z -> store_ok SEGS mem (Z_to_bv 64 (fs + FR2 + 256 * p + j)) 1 = true.
    Hypothesis Wshad : forall p j, (0 <= p < N2)%Z -> (0 <= j < 32)%Z -> store_ok SEGS mem (Z_to_bv 64 (SB + (fs + FR2 + 256 * p) / 8 + j)) 1 = true.

    Let h : Z := bv_unsigned hint.
    Definition pos2 (i : Z) : Z := ((h + i) mod N2)%Z.
    Definition ff2 (p : Z) : Z := (fs + FR2 + 256 * p)%Z.

    #[using="Type"] Lemma lit_5bfcc2 : v_addi (0x3f01c : word) 4 = Z_to_bv 64 0x3f020. Proof. apply bv_eq; vm_compute; reflexivity. Qed.
    #[using="Type"] Lemma ret_ok_5bfcc2 : ret_ok (Z_to_bv 64 0x3f020). Proof. apply ret_ok_even. vm_compute. reflexivity. Qed.
    #[using="Type"] Lemma lit_5c0d82 : v_addi (0x3f144 : word) 4 = Z_to_bv 64 0x3f148. Proof. apply bv_eq; vm_compute; reflexivity. Qed.
    #[using="Type"] Lemma ret_ok_5c0d82 : ret_ok (Z_to_bv 64 0x3f148). Proof. apply ret_ok_even. vm_compute. reflexivity. Qed.

    Ltac wz2 T V := progress (replace T with (Z_to_bv 64 V) by (apply bv_eq; vm_compute; reflexivity)).
    Ltac msd12 F D a v Hbase SOK :=
      mstep ltac:(eapply (step_sd_at _ _ _ _ _ _ _ _ _ (Z_to_bv 64 a) v F eq_refl D);
                   [ gr; rewrite ?Hbase; imm_norm; rewrite ?v_addi_any; apply (f_equal (Z_to_bv 64)); lia
                   | gr; first [reflexivity | assumption | symmetry; assumption]
                   | SOK ]).
    Ltac stk82 := pose proof HU; apply store_ok8_bytes; [lia|lia|];
                 intros j Hj; repeat apply store_ok1_wbytes; apply (s_stk _ _ _ _ _ _ _ _ _ H); unfold SM_FRAME; lia.

    (* [comment removed for export] *)
    Definition t_keep2 (r : reg) : bool := negb (tls_clob r || bv_eqb r 1 || bv_eqb r 2 || bv_eqb r 8 || bv_eqb r 10)%bool.

    #[using="fs ctx thr db beg a2v a3v H H01 H02 H04 hint h"] Lemma blk_PT2 :
      exists regs m,
        msteps SEGS (mkst regs0 (0x3effc : word) mem rom) (mkst regs (0x3f020 : word) m rom)
        /\ getr regs 2 = Z_to_bv 64 (usp - 32) /\ getr regs 8 = Z_to_bv 64 usp /\ getr regs 10 = Z_to_bv 64 TP
        /\ getr regs 4 = Z_to_bv 64 TP
        /\ (forall r, t_keep2 r = true -> getr regs r = getr regs0 r)
        /\ sfr m
        /\ (forall x : word, (usp - 32 <= bv_unsigned x)%Z -> m x = m1 x).
    Proof.
      pose proof HU as U.
      (* [comment removed for export] *)
      assert (P : exists q, msteps SEGS (mkst regs0 (0x3effc : word) mem rom) (mkst q (0x4428c : word) m1 rom)
                /\ getr q 2 = Z_to_bv 64 (usp - 32) /\ getr q 8 = Z_to_bv 64 usp /\ getr q 10 = Z_to_bv 64 A_DESC
                /\ getr q 1 = Z_to_bv 64 0x3f020 /\ getr q 4 = Z_to_bv 64 TP
                /\ (forall r : reg, r <> 1 -> r <> 2 -> r <> 8 -> r <> 10 -> getr q r = getr regs0 r)).
      { eexists. split.
        - mstep ltac:(exact (step_addi _ _ _ _ _ _ _ _ _ F_3effc eq_refl D_3effc)). rewrite H02. zn.
          msd12 F_3f000 D_3f000 (usp - 8)%Z ra H02 ltac:(stk82).
          msd12 F_3f004 D_3f004 (usp - 16)%Z (getr regs0 8) H02 ltac:(stk82).
          msd12 F_3f008 D_3f008 (usp - 24)%Z (getr regs0 9) H02 ltac:(stk82).
          msd12 F_3f00c D_3f00c (usp - 32)%Z (getr regs0 18) H02 ltac:(stk82).
          change (wbytes _ _ _) with m1.
          mstep ltac:(exact (step_addi _ _ _ _ _ _ _ _ _ F_3f010 eq_refl D_3f010)). gr. zn.
          mstep ltac:(eapply (step_auipc_at _ _ _ _ _ _ _ _ (Z_to_bv 64 0xac014) F_3f014 eq_refl D_3f014);
                       [reflexivity | apply bv_eq; vm_compute; reflexivity]).
          mstep ltac:(exact (step_addi _ _ _ _ _ _ _ _ _ F_3f018 eq_refl D_3f018)). gr. zn.
          mstep ltac:(eapply (step_jal_link _ _ _ _ _ _ _ _ F_3f01c eq_refl D_3f01c)). rewrite lit_5bfcc2.
          apply mst_refl.
        - gr. repeat split; try (apply (f_equal (Z_to_bv 64)); lia); try reflexivity; try assumption.
          intros r X1 X2 X8 X10. repeat (rewrite getr_other by congruence). reflexivity. }
      destruct P as (q & MP & Q2 & Q8 & Q10 & Q1 & Q4 & QK).
      destruct (tls_run m1 rom (usp - 32) ctx thr db beg a2v a3v tls_m1 q (Z_to_bv 64 0x3f020) ret_ok_5bfcc2 Q1 Q2 Q4 Q10)
        as (q2 & m2 & MT & T10 & T2 & T1 & TK & TM1 & TM2 & TM3).
      exists q2, m2. split.
      { eapply msteps_trans; [exact MP|]. replace (Z_to_bv 64 0x3f020) with (0x3f020 : word) in MT by (apply bv_eq; reflexivity). exact MT. }
      split; [exact T2|]. split; [rewrite TK by reflexivity; exact Q8|]. split; [exact T10|].
      split; [rewrite TK by reflexivity; exact Q4|]. split.
      { intros r Hr. unfold t_keep2 in Hr. apply negb_true_iff in Hr.
        apply orb_false_iff in Hr as [Hr K10]. apply orb_false_iff in Hr as [Hr K8].
        apply orb_false_iff in Hr as [Hr K2]. apply orb_false_iff in Hr as [Hr K1].
        rewrite TK by exact Hr. apply QK; intros ->; discriminate. }
      split.
      { destruct m1_sfr as (F1 & F2 & F3). unfold TLS_FRAME in TM1. split; [|split].
        - intros x Hx. rewrite TM1 by (unfold SM_FRAME in Hx; lia). apply F1. exact Hx.
        - intros x Hx. apply TM2. apply F2. exact Hx.
        - intros x Hx. apply TM3. apply F3. exact Hx. }
      intros x Hx. apply TM1. lia.
    Qed.

    (* [comment removed for export] *)
    Definition a_clob2 (r : reg) : bool :=
      (bv_eqb r 9 || bv_eqb r 10 || bv_eqb r 11 || bv_eqb r 12 || bv_eqb r 13 || bv_eqb r 14 || bv_eqb r 15 || bv_eqb r 16 || bv_eqb r 18)%bool.

    #[using="ctx thr db beg a2v a3v H Hhint"] Lemma blk_A2 : forall regs m,
      sfr m -> getr regs 10 = Z_to_bv 64 TP ->
      exists regs',
        msteps SEGS (mkst regs (0x3f020 : word) m rom) (mkst regs' (0x3f090 : word) m rom)
        /\ getr regs' 9 = Z_to_bv 64 fs /\ getr regs' 18 = Z_to_bv 64 20
        /\ getr regs' 10 = Z_to_bv 64 (N2 - 0) /\ getr regs' 12 = Z_to_bv 64 (h + 0)
        /\ getr regs' 13 = Z_to_bv 64 (fs + FL2) /\ getr regs' 14 = Z_to_bv 64 (N2 - 1)
        /\ getr regs' 11 = Z_to_bv 64 (fs + 4096)
        /\ (forall r, a_clob2 r = false -> getr regs' r = getr regs r).
    Proof.
      intros regs m FR H10. pose proof HU as U. pose proof HF as (F1 & F2 & F3 & F4). unfold FS_AREA, TP in *.
      pose proof (s_fs _ _ _ _ _ _ _ _ _ H) as Cfs. pose proof (s_gc _ _ _ _ _ _ _ _ _ H) as Cgc. pose proof (s_ssl _ _ _ _ _ _ _ _ _ H) as Cssl.
      pose proof Hhint as Ch. unfold cell, TP in Cfs, Cgc, Cssl, Ch.
      rewrite <- (rdn_sfr m) in Cfs by (first [exact FR | cbn; unfold SM_FRAME; lia]).
      rewrite <- (rdn_sfr m) in Cgc by (first [exact FR | cbn; unfold SM_FRAME; lia]).
      rewrite <- (rdn_sfr m) in Cssl by (first [exact FR | cbn; unfold SM_FRAME; lia]).
      rewrite <- (rdn_sfr m) in Ch by (first [exact FR | cbn; unfold SM_FRAME; lia]).
      eexists. split.
      - mld F_3f020 D_3f020 fs Cfs H10.
        mstep ltac:(eapply (step_beq_ft _ _ _ _ _ _ _ _ _ F_3f024 eq_refl D_3f024); gr; rewrite getr_zero; br_eq).
        mstep ltac:(eapply (@step_lbu _ _ _ _ _ _ _ _ _ _ (Z_to_bv 8 0) F_3f028 eq_refl D_3f028); gr; imm_norm; zn; exact Cgc).
        change (bv_unsigned (Z_to_bv 8 0)) with 0%Z.
        mld F_3f02c D_3f02c 20%Z Cssl H10.
        mstep ltac:(eapply (step_beq_tk _ _ _ _ _ _ _ _ _ F_3f030 eq_refl D_3f030); gr; rewrite getr_zero; br_eq).
        mstep ltac:(exact (step_addi _ _ _ _ _ _ _ _ _ F_3f040 eq_refl D_3f040)). gr. zn.
        mstep ltac:(exact (step_addi _ _ _ _ _ _ _ _ _ F_3f044 eq_refl D_3f044)). rewrite getr_zero. zn.
        mstep ltac:(exact (step_sll _ _ _ _ _ _ _ _ _ F_3f048 eq_refl D_3f048)). gr.
        wz2 (v_sll (Z_to_bv 64 1) (Z_to_bv 64 (20 + -8))) 4096%Z.
        mstep ltac:(exact (step_addiw _ _ _ _ _ _ _ _ _ F_3f04c eq_refl D_3f04c)). gr. imm_norm.
        wz2 (v_addiw (Z_to_bv 64 4096) 0) 4096%Z.
        mstep ltac:(eapply (step_bge_ft _ _ _ _ _ _ _ _ _ F_3f050 eq_refl D_3f050); gr; rewrite getr_zero; apply c_lts_pos_ft; lia).
        mstep ltac:(eapply (step_lui_at _ _ _ _ _ _ _ _ (Z_to_bv 64 4096) F_3f054 eq_refl D_3f054); reflexivity).
        mstep ltac:(exact (step_addi _ _ _ _ _ _ _ _ _ F_3f058 eq_refl D_3f058)). gr. zn.
        mstep ltac:(exact (step_addi _ _ _ _ _ _ _ _ _ F_3f05c eq_refl D_3f05c)). rewrite getr_zero. zn.
        mstep ltac:(exact (step_addi _ _ _ _ _ _ _ _ _ F_3f060 eq_refl D_3f060)). rewrite getr_zero, k_m1_val.
        mstep ltac:(exact (step_sll _ _ _ _ _ _ _ _ _ F_3f064 eq_refl D_3f064)). gr.
        wz2 (v_sll (Z_to_bv 64 768) (Z_to_bv 64 (20 + -15))) 24576%Z.
        mstep ltac:(eapply (@step_ld _ _ _ _ _ _ _ _ _ _ _ hint F_3f068 eq_refl D_3f068);
                     [ gr; imm_norm; zn; exact Ch | apply bytes_le_to_Z_8 ]).
        rewrite (zbv_self' hint). fold h.
        mstep ltac:(exact (step_sll _ _ _ _ _ _ _ _ _ F_3f06c eq_refl D_3f06c)). gr.
        wz2 (v_sll (Z_to_bv 64 (2 ^ 64 - 1)) (Z_to_bv 64 (20 + -8))) (2 ^ 64 - 4096)%Z.
        mstep ltac:(exact (step_addi _ _ _ _ _ _ _ _ _ F_3f070 eq_refl D_3f070)). gr. zn.
        mstep ltac:(exact (step_add _ _ _ _ _ _ _ _ _ F_3f074 eq_refl D_3f074)). gr. rewrite v_add_zbv by lia.
        mstep ltac:(exact (step_add _ _ _ _ _ _ _ _ _ F_3f078 eq_refl D_3f078)). gr. rewrite v_add_zbv by lia.
        mstep ltac:(exact (step_xori _ _ _ _ _ _ _ _ _ F_3f07c eq_refl D_3f07c)). gr. imm_norm.
        wz2 (v_xori (Z_to_bv 64 (2 ^ 64 - 4096)) (-1)) 4095%Z.
        mstep ltac:(exact (step_slli _ _ _ _ _ _ _ _ _ F_3f080 eq_refl D_3f080)). gr. imm_norm.
        wz2 (v_slli (Z_to_bv 64 (4096 + -1)) 32) (4095 * 2 ^ 32)%Z.
        mstep ltac:(exact (PropExec.step_srli _ _ _ _ _ _ _ _ _ F_3f084 eq_refl D_3f084)). gr. imm_norm.
        wz2 (v_srli (Z_to_bv 64 (4095 * 2 ^ 32)) 32) 4095%Z.
        mstep ltac:(exact (step_add _ _ _ _ _ _ _ _ _ F_3f088 eq_refl D_3f088)). gr. rewrite v_add_any.
        mstep ltac:(exact (step_addi _ _ _ _ _ _ _ _ _ F_3f08c eq_refl D_3f08c)). gr. rewrite v_addi_any.
        apply mst_refl.
      - gr. unfold N2, FL2. repeat split; try (apply (f_equal (Z_to_bv 64)); lia); try reflexivity.
        intros r Hr. unfold a_clob2 in Hr.
        repeat (rewrite getr_other by (intros ->; cbn in Hr; discriminate)). reflexivity.
    Qed.

    (* [comment removed for export] *)
    Let i0 : Z := ((p0 - h) mod N2)%Z.
    #[using="Type"] Lemma i0_rng2 : (0 <= i0 < N2)%Z. Proof. unfold i0, N2. apply Z.mod_pos_bound. lia. Qed.
    #[using="FL Hp0"] Lemma pos_i02 : pos2 i0 = p0.
    Proof.
      unfold pos2, i0, N2. rewrite Zplus_mod_idemp_r. replace (h + (p0 - h))%Z with p0 by lia.
      apply Z.mod_small. unfold N2 in Hp0. lia.
    Qed.
    #[using="p0 i0"] Lemma pos_rng2 : forall i, (0 <= pos2 i < N2)%Z. Proof. intros i. unfold pos2, N2. apply Z.mod_pos_bound. lia. Qed.

    Definition l_clob2 (r : reg) : bool := (bv_eqb r 5 || bv_eqb r 10 || bv_eqb r 12 || bv_eqb r 15 || bv_eqb r 17)%bool.

    #[using="ctx thr db beg a2v a3v H Hflags Hp0"] Lemma blk_L2 : forall (k : nat) i regs m,
      (i + Z.of_nat k = i0)%Z -> (0 <= i)%Z -> sfr m ->
      getr regs 10 = Z_to_bv 64 (N2 - i) -> getr regs 12 = Z_to_bv 64 (h + i) ->
      getr regs 13 = Z_to_bv 64 (fs + FL2) -> getr regs 14 = Z_to_bv 64 (N2 - 1) ->
      exists i' regs',
        (i <= i' <= i0)%Z /\ bv_unsigned (FL (pos2 i')) = 0%Z
        /\ msteps SEGS (mkst regs (0x3f090 : word) m rom) (mkst regs' (0x3f108 : word) m rom)
        /\ getr regs' 12 = Z_to_bv 64 (h + i') /\ getr regs' 17 = Z_to_bv 64 (pos2 i')
        /\ getr regs' 15 = Z_to_bv 64 (fs + FL2 + pos2 i')
        /\ (forall r, l_clob2 r = false -> getr regs' r = getr regs r).
    Proof.
      pose proof HU as U. pose proof HF as (F1 & F2 & F3 & F4). unfold FS_AREA in *. pose proof i0_rng2 as I0. pose proof Hp0 as [P0 P1].
      unfold N2 in *.
      unfold FL2 in *.
      induction k as [|k IH]; intros i regs m Hk Hi FR H10 H12 H13 H14.
      - (* [comment removed for export] *)
        cbn [Z.of_nat] in Hk. rewrite Z.add_0_r in Hk. subst i.
        pose proof (pos_rng2 i0) as PR. unfold N2 in PR.
        pose proof (Hflags (pos2 i0) PR) as CF. rewrite <- (rdn_sfr m) in CF by (first [exact FR | cbn; unfold SM_FRAME, FL2; lia]).
        exists i0. eexists. split; [lia|]. split; [rewrite pos_i02; exact P1|]. split.
        + mstep ltac:(exact (step_and _ _ _ _ _ _ _ _ _ F_3f090 eq_refl D_3f090)). gr. rewrite H12, H14.
          change (4096 - 1)%Z with (2 ^ 12 - 1)%Z. rewrite v_and_mask by lia. change (2 ^ 12)%Z with 4096%Z. fold N2. fold (pos2 i0).
          mstep ltac:(exact (step_add _ _ _ _ _ _ _ _ _ F_3f094 eq_refl D_3f094)). gr. rewrite H13. unfold FL2. rewrite v_add_zbv by lia.
          mstep ltac:(eapply (@step_lbu _ _ _ _ _ _ _ _ _ _ (FL (pos2 i0)) F_3f098 eq_refl D_3f098); gr; imm_norm; zn; rewrite ?Z.add_0_r; unfold FL2 in CF; exact CF).
          replace (bv_unsigned (FL (pos2 i0))) with 0%Z by (rewrite pos_i02, P1; reflexivity).
          mstep ltac:(eapply (step_beq_tk _ _ _ _ _ _ _ _ _ F_3f09c eq_refl D_3f09c); gr; rewrite getr_zero; br_eq).
          apply mst_refl.
        + gr. unfold FL2. repeat split; try (apply (f_equal (Z_to_bv 64)); lia); try reflexivity; try assumption.
          intros r Hr. unfold l_clob2 in Hr.
          repeat (rewrite getr_other by (intros ->; cbn in Hr; discriminate)). reflexivity.
      - (* [comment removed for export] *)
        pose proof (pos_rng2 i) as PR. unfold N2 in PR.
        pose proof (Hflags (pos2 i) PR) as CF. rewrite <- (rdn_sfr m) in CF by (first [exact FR | cbn; unfold SM_FRAME, FL2; lia]).
        pose proof (bv_unsigned_in_range 8 (FL (pos2 i))) as BR. change (bv_modulus 8) with 256%Z in BR.
        destruct (Z.eq_dec (bv_unsigned (FL (pos2 i))) 0) as [Z0|NZ].
        + exists i. eexists. split; [lia|]. split; [exact Z0|]. split.
          * mstep ltac:(exact (step_and _ _ _ _ _ _ _ _ _ F_3f090 eq_refl D_3f090)). gr. rewrite H12, H14.
            change (4096 - 1)%Z with (2 ^ 12 - 1)%Z. rewrite v_and_mask by lia. change (2 ^ 12)%Z with 4096%Z. fold N2. fold (pos2 i).
            mstep ltac:(exact (step_add _ _ _ _ _ _ _ _ _ F_3f094 eq_refl D_3f094)). gr. rewrite H13. unfold FL2. rewrite v_add_zbv by lia.
            mstep ltac:(eapply (@step_lbu _ _ _ _ _ _ _ _ _ _ (FL (pos2 i)) F_3f098 eq_refl D_3f098); gr; imm_norm; zn; rewrite ?Z.add_0_r; unfold FL2 in CF; exact CF).
            rewrite Z0.
            mstep ltac:(eapply (step_beq_tk _ _ _ _ _ _ _ _ _ F_3f09c eq_refl D_3f09c); gr; rewrite getr_zero; br_eq).
            apply mst_refl.
          * gr. unfold FL2. repeat split; try (apply (f_equal (Z_to_bv 64)); lia); try reflexivity; try assumption.
            intros r Hr. unfold l_clob2 in Hr.
            repeat (rewrite getr_other by (intros ->; cbn in Hr; discriminate)). reflexivity.
        + assert (NI : i <> i0) by (intros ->; rewrite pos_i02 in NZ; exact (NZ P1)).
          edestruct (IH (i + 1)%Z
            (regupd (regupd (regupd (regupd (regupd regs 17 (Z_to_bv 64 (pos2 i))) 15 (Z_to_bv 64 (fs + FL2 + pos2 i)))
               5 (Z_to_bv 64 (bv_unsigned (FL (pos2 i))))) 10 (Z_to_bv 64 (4096 - i - 1))) 12 (Z_to_bv 64 (h + i + 1))) m)
            as (i' & regs' & R1 & R2 & M & Q12 & Q17 & Q15 & QK); try lia; try exact FR.
          1-4: gr; first [assumption | apply (f_equal (Z_to_bv 64)); lia].
          exists i', regs'. split; [lia|]. split; [exact R2|]. split.
          * mstep ltac:(exact (step_and _ _ _ _ _ _ _ _ _ F_3f090 eq_refl D_3f090)). gr. rewrite H12, H14.
            change (4096 - 1)%Z with (2 ^ 12 - 1)%Z. rewrite v_and_mask by lia. change (2 ^ 12)%Z with 4096%Z. fold N2. fold (pos2 i).
            mstep ltac:(exact (step_add _ _ _ _ _ _ _ _ _ F_3f094 eq_refl D_3f094)). gr. rewrite H13. rewrite v_add_zbv by (unfold FL2; lia).
            mstep ltac:(eapply (@step_lbu _ _ _ _ _ _ _ _ _ _ (FL (pos2 i)) F_3f098 eq_refl D_3f098); gr; imm_norm; zn; rewrite ?Z.add_0_r; exact CF).
            mstep ltac:(eapply (step_beq_ft _ _ _ _ _ _ _ _ _ F_3f09c eq_refl D_3f09c); gr; rewrite getr_zero; br_eq).
            mstep ltac:(exact (step_addiw _ _ _ _ _ _ _ _ _ F_3f0a0 eq_refl D_3f0a0)). gr. rewrite H10. imm_norm.
            rewrite v_addiw_small by lia.
            mstep ltac:(exact (step_addi _ _ _ _ _ _ _ _ _ F_3f0a4 eq_refl D_3f0a4)). gr. rewrite H12, v_addi_any.
            mstep ltac:(eapply (step_bne_tk _ _ _ _ _ _ _ _ _ F_3f0a8 eq_refl D_3f0a8); gr; rewrite getr_zero; br_eq).
            replace (4096 - i + -1)%Z with (4096 - i - 1)%Z by lia. exact M.
          * split; [exact Q12|]. split; [exact Q17|]. split; [exact Q15|].
            intros r Hr. rewrite (QK r Hr). unfold l_clob2 in Hr.
            repeat (rewrite getr_other by (intros ->; cbn in Hr; discriminate)). reflexivity.
    Qed.

    (* [comment removed for export] *)
    (* [comment removed for export] *)
    Definition WR2 (m : word -> option byte) (i p : Z) : word -> option byte :=
      wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes m
        (Z_to_bv 64 (fs + 16)) (word_to_le_bytes 8 (Z_to_bv 64 (h + i + 1))))
        (Z_to_bv 64 (fs + FL2 + p)) (word_to_le_bytes 1 (Z_to_bv 64 1)))
        (Z_to_bv 64 (ff2 p + 24)) (word_to_le_bytes 8 (Z_to_bv 64 usp)))
        (Z_to_bv 64 (ff2 p + 248)) (word_to_le_bytes 8 (Z_to_bv 64 (fs + FL2 + p))))
        (Z_to_bv 64 (SB + ff2 p / 8)) (word_to_le_bytes 8 (Z_to_bv 64 0)))
        (Z_to_bv 64 (SB + ff2 p / 8 + 8)) (word_to_le_bytes 8 (Z_to_bv 64 0)))
        (Z_to_bv 64 (SB + ff2 p / 8 + 16)) (word_to_le_bytes 8 (Z_to_bv 64 0)))
        (Z_to_bv 64 (SB + ff2 p / 8 + 24)) (word_to_le_bytes 8 (Z_to_bv 64 0)).

    #[using="Type"] Lemma WR_agree2 : forall ma mb i p (x : word), ma x = mb x -> WR2 ma i p x = WR2 mb i p x.
    Proof. intros. unfold WR2. repeat apply wbytes_agree. assumption. Qed.
    #[using="Type"] Lemma WR_keep2 : forall m i p (x : word), m x <> None -> WR2 m i p x <> None.
    Proof. intros. unfold WR2. repeat apply wbytes_keep. assumption. Qed.
    #[using="Type"] Lemma WR_sok2 : forall m i p (x : word), store_ok SEGS m x 1 = true -> store_ok SEGS (WR2 m i p) x 1 = true.
    Proof. intros. unfold WR2. repeat apply store_ok1_wbytes. assumption. Qed.

    #[using="mem rom ctx thr db beg a2v a3v H p0 i0"] Lemma WR_stack2 : forall m i p a, (0 <= p < N2)%Z -> (usp - 32 <= a)%Z -> (a + 8 <= usp)%Z ->
      rdn SEGS (WR2 m i p) (Z_to_bv 64 a) 8 = rdn SEGS m (Z_to_bv 64 a) 8.
    Proof.
      intros m i p a Hp Ha Hb. pose proof HU as U. pose proof HF as (F1 & F2 & F3 & F4). unfold FS_AREA, N2, ff2, FR2, FL2 in *.
      pose proof SB_val.
      assert (ff_hi : (fs + 2134016 + 256 * p + 256 <= 2 ^ 47)%Z) by lia.
      pose proof (Z.div_pos (fs + 2134016 + 256 * p) 8 ltac:(lia) ltac:(lia)).
      pose proof (Z.div_lt_upper_bound (fs + 2134016 + 256 * p) 8 (2 ^ 44) ltac:(lia) ltac:(lia)).
      unfold WR2, ff2, FL2, FR2. rewrite !rdn_wbytes_out; try reflexivity; len8; rewrite ?zbv_u by (ltac2:(LK.k [@Hp; @Ha; @Hb; @U; @F1; @F2; @ff_hi; @H0; @H1; @H2; @F4]); lia); (ltac2:(LK.k [@Hp; @Ha; @Hb; @U; @F1; @F2; @ff_hi; @H0; @H1; @H2; @F4]); lia).
    Qed.

    Definition f_clob2 (r : reg) : bool :=
      (bv_eqb r 1 || bv_eqb r 2 || bv_eqb r 5 || bv_eqb r 8 || bv_eqb r 9 || bv_eqb r 10 || bv_eqb r 11 || bv_eqb r 12
       || bv_eqb r 13 || bv_eqb r 14 || bv_eqb r 15 || bv_eqb r 16 || bv_eqb r 17 || bv_eqb r 18)%bool.

    #[using="ctx thr db beg a2v a3v H Hret p0 Whint Wflag Wframe Wshad i0"] Lemma blk_F2 : forall regs m i p,
      sfr m -> (forall x : word, (usp - 32 <= bv_unsigned x)%Z -> m x = m1 x) ->
      (0 <= p < N2)%Z -> (0 <= i < N2)%Z ->
      getr regs 2 = Z_to_bv 64 (usp - 32) -> getr regs 8 = Z_to_bv 64 usp -> getr regs 9 = Z_to_bv 64 fs ->
      getr regs 18 = Z_to_bv 64 20 -> getr regs 11 = Z_to_bv 64 (fs + 4096) ->
      getr regs 12 = Z_to_bv 64 (h + i) -> getr regs 17 = Z_to_bv 64 p -> getr regs 15 = Z_to_bv 64 (fs + FL2 + p) ->
      exists regs',
        msteps SEGS (mkst regs (0x3f108 : word) m rom) (mkst regs' ra (WR2 m i p) rom)
        /\ getr regs' 10 = Z_to_bv 64 (ff2 p) /\ getr regs' 2 = Z_to_bv 64 usp /\ getr regs' 1 = ra
        /\ getr regs' 8 = getr regs0 8 /\ getr regs' 9 = getr regs0 9 /\ getr regs' 18 = getr regs0 18
        /\ (forall r, f_clob2 r = false -> getr regs' r = getr regs r).
    Proof.
      intros regs m i p FR AG Hp Hi H2 H8 H9 H18 H11 H12 H17 H15.
      pose proof HU as U. pose proof HF as (F1 & F2 & F3 & F4). pose proof SB_val as HSB. unfold FS_AREA, N2, FL2 in *.
      destruct FR as (FRa & FRb & FRc).
      assert (ff_lo : (0x608000 <= ff2 p)%Z) by (unfold ff2, FR2; lia).
      assert (ff_hi : (ff2 p + 256 <= 2 ^ 47)%Z) by (unfold ff2, FR2; lia).
      pose proof (Z.div_pos (ff2 p) 8 ltac:(lia) ltac:(lia)) as D1.
      pose proof (Z.div_lt_upper_bound (ff2 p) 8 (2 ^ 44) ltac:(lia) ltac:(lia)) as D2.
      (* [comment removed for export] *)
      assert (RD : forall a v, (usp - 32 <= a)%Z -> (a + 8 <= usp)%Z ->
                rdn SEGS m1 (Z_to_bv 64 a) 8 = Some (word_to_le_bytes 8 v) ->
                rdn SEGS (WR2 m i p) (Z_to_bv 64 a) 8 = Some (word_to_le_bytes 8 v)).
      { intros a v Ha Hb R. rewrite WR_stack2 by (unfold N2; lia). rewrite <- R. apply rdn_ext; [rewrite zbv_u by lia; cbn; lia|].
        intros x Hx. rewrite zbv_u in Hx by lia. apply AG. lia. }
      pose proof (RD (usp - 8)%Z _ ltac:(lia) ltac:(lia) rd1_8) as R8. pose proof (RD (usp - 16)%Z _ ltac:(lia) ltac:(lia) rd1_16) as R16.
      pose proof (RD (usp - 24)%Z _ ltac:(lia) ltac:(lia) rd1_24) as R24. pose proof (RD (usp - 32)%Z _ ltac:(lia) ltac:(lia) rd1_32) as R32.
      (* [comment removed for export] *)
      set (m4 := wbytes (wbytes (wbytes (wbytes m
        (Z_to_bv 64 (fs + 16)) (word_to_le_bytes 8 (Z_to_bv 64 (h + i + 1))))
        (Z_to_bv 64 (fs + 28672 + p)) (word_to_le_bytes 1 (Z_to_bv 64 1)))
        (Z_to_bv 64 (ff2 p + 24)) (word_to_le_bytes 8 (Z_to_bv 64 usp)))
        (Z_to_bv 64 (ff2 p + 248)) (word_to_le_bytes 8 (Z_to_bv 64 (fs + 28672 + p)))).
      assert (C4 : cells m4).
      { pose proof (s_cells _ _ _ _ _ _ _ _ _ H) as C. unfold cells, cell in *. unfold m4.
        rewrite !rdn_wbytes_out; len8; rewrite ?zbv_u by (ltac2:(LK.k [@F1; @F2; @Hp; @U; @ff_lo; @ff_hi]); lia); try (cbn; unfold ff2, FR2 in *; (ltac2:(LK.k [@F1; @F2; @Hp; @U; @ff_lo; @ff_hi]); lia)).
        rewrite !(rdn_sfr m) by (first [split; [exact FRa|split; [exact FRb|exact FRc]] | cbn; unfold SM_FRAME; lia]). exact C. }
      (* [comment removed for export] *)
      assert (P1 : exists r1,
        msteps SEGS (mkst regs (0x3f108 : word) m rom) (mkst r1 (0x3f510 : word) m4 rom)
        /\ getr r1 10 = Z_to_bv 64 (ff2 p) /\ getr r1 1 = Z_to_bv 64 0x3f148 /\ getr r1 2 = Z_to_bv 64 (usp - 32)
        /\ getr r1 9 = Z_to_bv 64 (ff2 p)
        /\ (forall r : reg, r <> 1 -> r <> 9 -> r <> 10 -> r <> 12 -> r <> 13 -> r <> 17 -> getr r1 r = getr regs r)).
      { eexists. split.
        - mstep ltac:(exact (step_addi _ _ _ _ _ _ _ _ _ F_3f108 eq_refl D_3f108)). gr. rewrite H12, v_addi_any.
          mstep ltac:(exact (step_addi _ _ _ _ _ _ _ _ _ F_3f10c eq_refl D_3f10c)). rewrite getr_zero. zn.
          mstep ltac:(exact (step_addi _ _ _ _ _ _ _ _ _ F_3f110 eq_refl D_3f110)). gr. rewrite H18. zn.
          msd12 F_3f114 D_3f114 (fs + 16)%Z (Z_to_bv 64 (h + i + 1)) H9
               ltac:(apply store_ok8_bytes; [lia|lia|]; intros j Hj; apply FRc; replace (fs + 16 + j)%Z with (fs + (16 + j))%Z by lia; apply Whint; lia).
          mstep ltac:(eapply (step_sb _ _ _ _ _ _ _ _ _ F_3f118 eq_refl D_3f118);
                       gr; rewrite H15; imm_norm; zn; rewrite ?Z.add_0_r; apply store_ok1_wbytes; apply FRc; apply Wflag; lia).
          gr. rewrite H15. zn. rewrite ?Z.add_0_r.
          mstep ltac:(exact (step_sll _ _ _ _ _ _ _ _ _ F_3f11c eq_refl D_3f11c)). gr.
          wz2 (v_sll (Z_to_bv 64 1) (Z_to_bv 64 (20 + -5))) 32768%Z.
          mstep ltac:(exact (step_addi _ _ _ _ _ _ _ _ _ F_3f120 eq_refl D_3f120)). rewrite getr_zero. zn.
          mstep ltac:(exact (step_slli _ _ _ _ _ _ _ _ _ F_3f124 eq_refl D_3f124)). gr. rewrite H17. imm_norm.
          rewrite (v_slli_zbv p 8) by lia.
          mstep ltac:(exact (step_sll _ _ _ _ _ _ _ _ _ F_3f128 eq_refl D_3f128)). gr. rewrite H18.
          wz2 (v_sll (Z_to_bv 64 2) (Z_to_bv 64 20)) (2 * 2 ^ 20)%Z.
          mstep ltac:(exact (step_add _ _ _ _ _ _ _ _ _ F_3f12c eq_refl D_3f12c)). gr. rewrite H11, v_add_zbv by lia.
          mstep ltac:(exact (step_add _ _ _ _ _ _ _ _ _ F_3f130 eq_refl D_3f130)). gr. rewrite v_add_zbv by lia.
          mstep ltac:(exact (step_add _ _ _ _ _ _ _ _ _ F_3f134 eq_refl D_3f134)). gr. rewrite v_add_zbv by lia.
          change (2 ^ 8)%Z with 256%Z. replace (fs + 4096 + 32768 + (2 * 2 ^ 20 + p * 256))%Z with (ff2 p) by (unfold ff2, FR2; lia).
          msd12 F_3f138 D_3f138 (ff2 p + 24)%Z (Z_to_bv 64 usp) H8
               ltac:(apply store_ok8_bytes; [lia|lia|]; intros j Hj; repeat apply store_ok1_wbytes; apply FRc;
                     unfold ff2, FR2; replace (fs + 2134016 + 256 * p + 24 + j)%Z with (fs + 2134016 + 256 * p + (24 + j))%Z by lia; apply Wframe; lia).
          msd12 F_3f13c D_3f13c (ff2 p + 248)%Z (Z_to_bv 64 (fs + 28672 + p)) H8
               ltac:(apply store_ok8_bytes; [lia|lia|]; intros j Hj; repeat apply store_ok1_wbytes; apply FRc;
                     unfold ff2, FR2; replace (fs + 2134016 + 256 * p + 248 + j)%Z with (fs + 2134016 + 256 * p + (248 + j))%Z by lia; apply Wframe; lia).
          change (wbytes _ _ _) with m4.
          mstep ltac:(exact (step_addi _ _ _ _ _ _ _ _ _ F_3f140 eq_refl D_3f140)). gr. zn. rewrite ?Z.add_0_r.
          mstep ltac:(eapply (step_jal_link _ _ _ _ _ _ _ _ F_3f144 eq_refl D_3f144)). rewrite lit_5c0d82.
          apply mst_refl.
        - gr. repeat split; try reflexivity; try assumption; try (apply (f_equal (Z_to_bv 64)); lia).
          intros r N1 N9 N10 N12 N13 N17. repeat (rewrite getr_other by congruence). reflexivity. }
      destruct P1 as (r1 & M1 & P10 & P1ra & P2 & P9 & PK).
      destruct (mem_to_shadow_5e918 rom r1 m4 (ff2 p) (Z_to_bv 64 0x3f148) C4 ltac:(lia)
                  ltac:(apply (in_mem_frame fs (ff2 p) 256 HFB); [lia|unfold ff2, FR2; lia|unfold ff2, FR2 in *; unfold FS_AREA in *; lia|unfold FS_AREA in *; lia|lia])
                  P10 P1ra ret_ok_5c0d82)
        as (q & MQ & Q10 & QK).
      assert (Q2 : getr q 2 = Z_to_bv 64 (usp - 32)) by (rewrite QK by reflexivity; exact P2).
      assert (Q9 : getr q 9 = Z_to_bv 64 (ff2 p)) by (rewrite QK by reflexivity; exact P9).
      eexists. split.
      - eapply msteps_trans; [exact M1|]. eapply msteps_trans; [exact MQ|].
        replace (Z_to_bv 64 0x3f148) with (0x3f148 : word) by (apply bv_eq; reflexivity).
        mstep ltac:(exact (step_addi _ _ _ _ _ _ _ _ _ F_3f148 eq_refl D_3f148)). gr. rewrite Q10. zn. rewrite ?Z.add_0_r.
        mstep ltac:(exact (step_addi _ _ _ _ _ _ _ _ _ F_3f14c eq_refl D_3f14c)). gr. rewrite Q9. zn. rewrite ?Z.add_0_r.
        mstep ltac:(exact (step_addi _ _ _ _ _ _ _ _ _ F_3f150 eq_refl D_3f150)). rewrite getr_zero. zn.
        msd12 F_3f154 D_3f154 (SB + ff2 p / 8)%Z (Z_to_bv 64 0) Q2
             ltac:(apply store_ok8_bytes; [lia|lia|]; intros j Hj; unfold m4; repeat apply store_ok1_wbytes; apply FRc;
                   unfold ff2, FR2; apply Wshad; lia).
        msd12 F_3f158 D_3f158 (SB + ff2 p / 8 + 8)%Z (Z_to_bv 64 0) Q2
             ltac:(apply store_ok8_bytes; [lia|lia|]; intros j Hj; unfold m4; repeat apply store_ok1_wbytes; apply FRc;
                   unfold ff2, FR2; replace (SB + (fs + 2134016 + 256 * p) / 8 + 8 + j)%Z with (SB + (fs + 2134016 + 256 * p) / 8 + (8 + j))%Z by lia;
                   apply Wshad; lia).
        msd12 F_3f15c D_3f15c (SB + ff2 p / 8 + 16)%Z (Z_to_bv 64 0) Q2
             ltac:(apply store_ok8_bytes; [lia|lia|]; intros j Hj; unfold m4; repeat apply store_ok1_wbytes; apply FRc;
                   unfold ff2, FR2; replace (SB + (fs + 2134016 + 256 * p) / 8 + 16 + j)%Z with (SB + (fs + 2134016 + 256 * p) / 8 + (16 + j))%Z by lia;
                   apply Wshad; lia).
        msd12 F_3f160 D_3f160 (SB + ff2 p / 8 + 24)%Z (Z_to_bv 64 0) Q2
             ltac:(apply store_ok8_bytes; [lia|lia|]; intros j Hj; unfold m4; repeat apply store_ok1_wbytes; apply FRc;
                   unfold ff2, FR2; replace (SB + (fs + 2134016 + 256 * p) / 8 + 24 + j)%Z with (SB + (fs + 2134016 + 256 * p) / 8 + (24 + j))%Z by lia;
                   apply Wshad; lia).
        change (wbytes _ _ _) with (WR2 m i p).
        mstep ltac:(eapply (@step_ld _ _ _ _ _ _ _ _ _ _ _ ra F_3f164 eq_refl D_3f164);
                     [ gr; rewrite Q2; imm_norm; zn; replace (usp - 32 + 24)%Z with (usp - 8)%Z by lia; exact R8 | apply bytes_le_to_Z_8 ]).
        mstep ltac:(eapply (@step_ld _ _ _ _ _ _ _ _ _ _ _ (getr regs0 8) F_3f168 eq_refl D_3f168);
                     [ gr; rewrite Q2; imm_norm; zn; replace (usp - 32 + 16)%Z with (usp - 16)%Z by lia; exact R16 | apply bytes_le_to_Z_8 ]).
        mstep ltac:(eapply (@step_ld _ _ _ _ _ _ _ _ _ _ _ (getr regs0 9) F_3f16c eq_refl D_3f16c);
                     [ gr; rewrite Q2; imm_norm; zn; replace (usp - 32 + 8)%Z with (usp - 24)%Z by lia; exact R24 | apply bytes_le_to_Z_8 ]).
        mstep ltac:(eapply (@step_ld _ _ _ _ _ _ _ _ _ _ _ (getr regs0 18) F_3f170 eq_refl D_3f170);
                     [ gr; rewrite Q2; imm_norm; zn; rewrite ?Z.add_0_r; exact R32 | apply bytes_le_to_Z_8 ]).
        mstep ltac:(exact (step_addi _ _ _ _ _ _ _ _ _ F_3f174 eq_refl D_3f174)). gr. rewrite Q2. zn.
        replace (usp - 32 + 32)%Z with usp by lia.
        eapply mst_step; [reflexivity | eapply (step_jalr_x0 _ _ _ _ _ _ _ _ ra F_3f178 eq_refl D_3f178); gr; reflexivity |].
        imm_norm. rewrite Hret. apply mst_refl.
      - gr. repeat split; try reflexivity.
        intros r Hr. unfold f_clob2 in Hr.
        repeat (rewrite getr_other by (intros ->; cbn in Hr; discriminate)).
        rewrite QK by (unfold m2s_clob; repeat match type of Hr with (?a || ?b)%bool = false => apply orb_false_iff in Hr; destruct Hr as [Hr ?] end;
                       repeat match goal with Hb : bv_eqb r _ = false |- _ => rewrite Hb; clear Hb end; reflexivity).
        apply PK; intros ->; cbn in Hr; discriminate.
    Qed.

    (* [comment removed for export] *)
    #[using="ctx thr db beg a2v a3v H Hret H01 H02 H04 p0 Hhint Hflags Hp0 Whint Wflag Wframe Wshad i0"] Theorem sm2_AM :
      exists i p regs' m',
        (0 <= i < N2)%Z /\ p = pos2 i /\ bv_unsigned (FL p) = 0%Z
        /\ msteps SEGS (mkst regs0 (0x3effc : word) mem rom) (mkst regs' ra m' rom)
        /\ getr regs' 10 = Z_to_bv 64 (ff2 p) /\ getr regs' 2 = Z_to_bv 64 usp /\ getr regs' 1 = ra
        /\ (forall r, sm_clob r = false -> getr regs' r = getr regs0 r)
        /\ (forall x : word, (bv_unsigned x < usp - SM_FRAME \/ usp <= bv_unsigned x)%Z -> m' x = WR2 mem i p x)
        /\ (forall x, mem x <> None -> m' x <> None)
        /\ (forall x, store_ok SEGS mem x 1 = true -> store_ok SEGS m' x 1 = true).
    Proof.
      pose proof HU as U. pose proof i0_rng2 as I0.
      destruct blk_PT2 as (q1 & m2 & M1 & A2 & A8 & A10 & A4 & AK & FR & AG).
      destruct (blk_A2 q1 m2 FR A10) as (q2 & M2 & B9 & B18 & B10 & B12 & B13 & B14 & B11 & BK).
      destruct (blk_L2 (Z.to_nat i0) 0 q2 m2 ltac:(lia) ltac:(lia) FR B10 B12 B13 B14)
        as (i & q3 & Hi & HZ & M3 & C12 & C17 & C15 & CK).
      assert (C2 : getr q3 2 = Z_to_bv 64 (usp - 32)) by (rewrite CK, BK by reflexivity; exact A2).
      assert (C8 : getr q3 8 = Z_to_bv 64 usp) by (rewrite CK, BK by reflexivity; exact A8).
      assert (C9 : getr q3 9 = Z_to_bv 64 fs) by (rewrite CK by reflexivity; exact B9).
      assert (C18 : getr q3 18 = Z_to_bv 64 20) by (rewrite CK by reflexivity; exact B18).
      assert (C11 : getr q3 11 = Z_to_bv 64 (fs + 4096)) by (rewrite CK by reflexivity; exact B11).
      pose proof (pos_rng2 i) as PR.
      destruct (blk_F2 q3 m2 i (pos2 i) FR AG PR ltac:(lia) C2 C8 C9 C18 C11 C12 C17 C15)
        as (q4 & M4 & D10 & D2 & D1 & D8 & D9 & D18 & DK).
      exists i, (pos2 i), q4, (WR2 m2 i (pos2 i)).
      split; [lia|]. split; [reflexivity|]. split; [exact HZ|]. split.
      { eapply msteps_trans; [exact M1|]. eapply msteps_trans; [exact M2|]. eapply msteps_trans; [exact M3|]. exact M4. }
      split; [exact D10|]. split; [exact D2|]. split; [exact D1|]. split.
      { intros r Hr.
        destruct (bv_eq_dec _ r 1) as [-> | X1]; [rewrite D1; symmetry; exact H01|].
        destruct (bv_eq_dec _ r 2) as [-> | N2]; [rewrite D2; symmetry; exact H02|].
        destruct (bv_eq_dec _ r 8) as [-> | N8]; [exact D8|].
        destruct (bv_eq_dec _ r 9) as [-> | N9]; [exact D9|].
        destruct (bv_eq_dec _ r 18) as [-> | N18]; [exact D18|].
        assert (NE : forall k : reg, r <> k -> bv_eqb r k = false) by (intros k Hk; apply bv_eqb_neq; exact Hk).
        pose proof (NE _ X1) as T1. pose proof (NE _ N2) as T2. pose proof (NE _ N8) as T8. pose proof (NE _ N9) as T9. pose proof (NE _ N18) as T18.
        unfold sm_clob in Hr.
        apply orb_false_iff in Hr as [Hr T17]. apply orb_false_iff in Hr as [Hr T16]. apply orb_false_iff in Hr as [Hr T15].
        apply orb_false_iff in Hr as [Hr T14]. apply orb_false_iff in Hr as [Hr T13]. apply orb_false_iff in Hr as [Hr T12].
        apply orb_false_iff in Hr as [Hr T11]. apply orb_false_iff in Hr as [T5 T10].
        rewrite DK by (unfold f_clob2; rewrite ?T1, ?T2, ?T5, ?T8, ?T9, ?T10, ?T11, ?T12, ?T13, ?T14, ?T15, ?T16, ?T17, ?T18; reflexivity).
        rewrite CK by (unfold l_clob2; rewrite ?T5, ?T10, ?T12, ?T15, ?T17; reflexivity).
        rewrite BK by (unfold a_clob2; rewrite ?T9, ?T10, ?T11, ?T12, ?T13, ?T14, ?T15, ?T16, ?T18; reflexivity).
        apply AK. unfold t_keep2, tls_clob. rewrite T10, T11, T12, T13, T1, T2, T8. reflexivity. }
      destruct FR as (FRa & FRb & FRc). split; [|split].
      - intros x Hx. apply WR_agree2. apply FRa. exact Hx.
      - intros x Hx. apply WR_keep2. apply FRb. exact Hx.
      - intros x Hx. apply WR_sok2. apply FRc. exact Hx.
    Qed.
  End C2.
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Section C3.
    Definition N3 : Z := 2048.
    Definition FL3 : Z := 32768.
    Definition FR3 : Z := 3182592.
    Variable hint : word.                (* [comment removed for export] *)
    Variable FL : Z -> byte.             (* [comment removed for export] *)
    Variable p0 : Z.                     (* [comment removed for export] *)
    Hypothesis Hhint : rdn SEGS mem (Z_to_bv 64 (fs + 24)) 8 = Some (word_to_le_bytes 8 hint).
    Hypothesis Hflags : forall p, (0 <= p < N3)%Z -> rdn SEGS mem (Z_to_bv 64 (fs + FL3 + p)) 1 = Some [FL p].
    Hypothesis Hp0 : (0 <= p0 < N3)%Z /\ bv_unsigned (FL p0) = 0%Z.
    Hypothesis Whint : forall j, (24 <= j < 32)%Z -> store_ok SEGS mem (Z_to_bv 64 (fs + j)) 1 = true.
    Hypothesis Wflag : forall p, (0 <= p < N3)%Z -> store_ok SEGS mem (Z_to_bv 64 (fs + FL3 + p)) 1 = true.
    Hypothesis Wframe : forall p j, (0 <= p < N3)%Z -> (0 <= j < 512)%Z -> store_ok SEGS mem (Z_to_bv 64 (fs + FR3 + 512 * p + j)) 1 = true.
    Hypothesis Wshad : forall p j, (0 <= p < N3)%Z -> (0 <= j < 64)%Z -> store_ok SEGS mem (Z_to_bv 64 (SB + (fs + FR3 + 512 * p) / 8 + j)) 1 = true.

    Let h : Z := bv_unsigned hint.
    Definition pos3 (i : Z) : Z := ((h + i) mod N3)%Z.
    Definition ff3 (p : Z) : Z := (fs + FR3 + 512 * p)%Z.

    #[using="Type"] Lemma lit_5bfcc3 : v_addi (0x3f1b8 : word) 4 = Z_to_bv 64 0x3f1bc. Proof. apply bv_eq; vm_compute; reflexivity. Qed.
    #[using="Type"] Lemma ret_ok_5bfcc3 : ret_ok (Z_to_bv 64 0x3f1bc). Proof. apply ret_ok_even. vm_compute. reflexivity. Qed.
    #[using="Type"] Lemma lit_5c0d83 : v_addi (0x3f2e0 : word) 4 = Z_to_bv 64 0x3f2e4. Proof. apply bv_eq; vm_compute; reflexivity. Qed.
    #[using="Type"] Lemma ret_ok_5c0d83 : ret_ok (Z_to_bv 64 0x3f2e4). Proof. apply ret_ok_even. vm_compute. reflexivity. Qed.

    Ltac wz3 T V := progress (replace T with (Z_to_bv 64 V) by (apply bv_eq; vm_compute; reflexivity)).
    Ltac msd13 F D a v Hbase SOK :=
      mstep ltac:(eapply (step_sd_at _ _ _ _ _ _ _ _ _ (Z_to_bv 64 a) v F eq_refl D);
                   [ gr; rewrite ?Hbase; imm_norm; rewrite ?v_addi_any; apply (f_equal (Z_to_bv 64)); lia
                   | gr; first [reflexivity | assumption | symmetry; assumption]
                   | SOK ]).
    Ltac stk83 := pose proof HU; apply store_ok8_bytes; [lia|lia|];
                 intros j Hj; repeat apply store_ok1_wbytes; apply (s_stk _ _ _ _ _ _ _ _ _ H); unfold SM_FRAME; lia.

    (* [comment removed for export] *)
    Definition t_keep3 (r : reg) : bool := negb (tls_clob r || bv_eqb r 1 || bv_eqb r 2 || bv_eqb r 8 || bv_eqb r 10)%bool.

    #[using="fs ctx thr db beg a2v a3v H H01 H02 H04 hint h"] Lemma blk_PT3 :
      exists regs m,
        msteps SEGS (mkst regs0 (0x3f198 : word) mem rom) (mkst regs (0x3f1bc : word) m rom)
        /\ getr regs 2 = Z_to_bv 64 (usp - 32) /\ getr regs 8 = Z_to_bv 64 usp /\ getr regs 10 = Z_to_bv 64 TP
        /\ getr regs 4 = Z_to_bv 64 TP
        /\ (forall r, t_keep3 r = true -> getr regs r = getr regs0 r)
        /\ sfr m
        /\ (forall x : word, (usp - 32 <= bv_unsigned x)%Z -> m x = m1 x).
    Proof.
      pose proof HU as U.
      (* [comment removed for export] *)
      assert (P : exists q, msteps SEGS (mkst regs0 (0x3f198 : word) mem rom) (mkst q (0x4428c : word) m1 rom)
                /\ getr q 2 = Z_to_bv 64 (usp - 32) /\ getr q 8 = Z_to_bv 64 usp /\ getr q 10 = Z_to_bv 64 A_DESC
                /\ getr q 1 = Z_to_bv 64 0x3f1bc /\ getr q 4 = Z_to_bv 64 TP
                /\ (forall r : reg, r <> 1 -> r <> 2 -> r <> 8 -> r <> 10 -> getr q r = getr regs0 r)).
      { eexists. split.
        - mstep ltac:(exact (step_addi _ _ _ _ _ _ _ _ _ F_3f198 eq_refl D_3f198)). rewrite H02. zn.
          msd13 F_3f19c D_3f19c (usp - 8)%Z ra H02 ltac:(stk83).
          msd13 F_3f1a0 D_3f1a0 (usp - 16)%Z (getr regs0 8) H02 ltac:(stk83).
          msd13 F_3f1a4 D_3f1a4 (usp - 24)%Z (getr regs0 9) H02 ltac:(stk83).
          msd13 F_3f1a8 D_3f1a8 (usp - 32)%Z (getr regs0 18) H02 ltac:(stk83).
          change (wbytes _ _ _) with m1.
          mstep ltac:(exact (step_addi _ _ _ _ _ _ _ _ _ F_3f1ac eq_refl D_3f1ac)). gr. zn.
          mstep ltac:(eapply (step_auipc_at _ _ _ _ _ _ _ _ (Z_to_bv 64 0xac1b0) F_3f1b0 eq_refl D_3f1b0);
                       [reflexivity | apply bv_eq; vm_compute; reflexivity]).
          mstep ltac:(exact (step_addi _ _ _ _ _ _ _ _ _ F_3f1b4 eq_refl D_3f1b4)). gr. zn.
          mstep ltac:(eapply (step_jal_link _ _ _ _ _ _ _ _ F_3f1b8 eq_refl D_3f1b8)). rewrite lit_5bfcc3.
          apply mst_refl.
        - gr. repeat split; try (apply (f_equal (Z_to_bv 64)); lia); try reflexivity; try assumption.
          intros r X1 X2 X8 X10. repeat (rewrite getr_other by congruence). reflexivity. }
      destruct P as (q & MP & Q2 & Q8 & Q10 & Q1 & Q4 & QK).
      destruct (tls_run m1 rom (usp - 32) ctx thr db beg a2v a3v tls_m1 q (Z_to_bv 64 0x3f1bc) ret_ok_5bfcc3 Q1 Q2 Q4 Q10)
        as (q2 & m2 & MT & T10 & T2 & T1 & TK & TM1 & TM2 & TM3).
      exists q2, m2. split.
      { eapply msteps_trans; [exact MP|]. replace (Z_to_bv 64 0x3f1bc) with (0x3f1bc : word) in MT by (apply bv_eq; reflexivity). exact MT. }
      split; [exact T2|]. split; [rewrite TK by reflexivity; exact Q8|]. split; [exact T10|].
      split; [rewrite TK by reflexivity; exact Q4|]. split.
      { intros r Hr. unfold t_keep3 in Hr. apply negb_true_iff in Hr.
        apply orb_false_iff in Hr as [Hr K10]. apply orb_false_iff in Hr as [Hr K8].
        apply orb_false_iff in Hr as [Hr K2]. apply orb_false_iff in Hr as [Hr K1].
        rewrite TK by exact Hr. apply QK; intros ->; discriminate. }
      split.
      { destruct m1_sfr as (F1 & F2 & F3). unfold TLS_FRAME in TM1. split; [|split].
        - intros x Hx. rewrite TM1 by (unfold SM_FRAME in Hx; lia). apply F1. exact Hx.
        - intros x Hx. apply TM2. apply F2. exact Hx.
        - intros x Hx. apply TM3. apply F3. exact Hx. }
      intros x Hx. apply TM1. lia.
    Qed.

    (* [comment removed for export] *)
    Definition a_clob3 (r : reg) : bool :=
      (bv_eqb r 9 || bv_eqb r 10 || bv_eqb r 11 || bv_eqb r 12 || bv_eqb r 13 || bv_eqb r 14 || bv_eqb r 15 || bv_eqb r 16 || bv_eqb r 18)%bool.

    #[using="ctx thr db beg a2v a3v H Hhint"] Lemma blk_A3 : forall regs m,
      sfr m -> getr regs 10 = Z_to_bv 64 TP ->
      exists regs',
        msteps SEGS (mkst regs (0x3f1bc : word) m rom) (mkst regs' (0x3f22c : word) m rom)
        /\ getr regs' 9 = Z_to_bv 64 fs /\ getr regs' 18 = Z_to_bv 64 20
        /\ getr regs' 10 = Z_to_bv 64 (N3 - 0) /\ getr regs' 12 = Z_to_bv 64 (h + 0)
        /\ getr regs' 13 = Z_to_bv 64 (fs + FL3) /\ getr regs' 14 = Z_to_bv 64 (N3 - 1)
        /\ getr regs' 11 = Z_to_bv 64 (fs + 4096)
        /\ (forall r, a_clob3 r = false -> getr regs' r = getr regs r).
    Proof.
      intros regs m FR H10. pose proof HU as U. pose proof HF as (F1 & F2 & F3 & F4). unfold FS_AREA, TP in *.
      pose proof (s_fs _ _ _ _ _ _ _ _ _ H) as Cfs. pose proof (s_gc _ _ _ _ _ _ _ _ _ H) as Cgc. pose proof (s_ssl _ _ _ _ _ _ _ _ _ H) as Cssl.
      pose proof Hhint as Ch. unfold cell, TP in Cfs, Cgc, Cssl, Ch.
      rewrite <- (rdn_sfr m) in Cfs by (first [exact FR | cbn; unfold SM_FRAME; lia]).
      rewrite <- (rdn_sfr m) in Cgc by (first [exact FR | cbn; unfold SM_FRAME; lia]).
      rewrite <- (rdn_sfr m) in Cssl by (first [exact FR | cbn; unfold SM_FRAME; lia]).
      rewrite <- (rdn_sfr m) in Ch by (first [exact FR | cbn; unfold SM_FRAME; lia]).
      eexists. split.
      - mld F_3f1bc D_3f1bc fs Cfs H10.
        mstep ltac:(eapply (step_beq_ft _ _ _ _ _ _ _ _ _ F_3f1c0 eq_refl D_3f1c0); gr; rewrite getr_zero; br_eq).
        mstep ltac:(eapply (@step_lbu _ _ _ _ _ _ _ _ _ _ (Z_to_bv 8 0) F_3f1c4 eq_refl D_3f1c4); gr; imm_norm; zn; exact Cgc).
        change (bv_unsigned (Z_to_bv 8 0)) with 0%Z.
        mld F_3f1c8 D_3f1c8 20%Z Cssl H10.
        mstep ltac:(eapply (step_beq_tk _ _ _ _ _ _ _ _ _ F_3f1cc eq_refl D_3f1cc); gr; rewrite getr_zero; br_eq).
        mstep ltac:(exact (step_addi _ _ _ _ _ _ _ _ _ F_3f1dc eq_refl D_3f1dc)). gr. zn.
        mstep ltac:(exact (step_addi _ _ _ _ _ _ _ _ _ F_3f1e0 eq_refl D_3f1e0)). rewrite getr_zero. zn.
        mstep ltac:(exact (step_sll _ _ _ _ _ _ _ _ _ F_3f1e4 eq_refl D_3f1e4)). gr.
        wz3 (v_sll (Z_to_bv 64 1) (Z_to_bv 64 (20 + -9))) 2048%Z.
        mstep ltac:(exact (step_addiw _ _ _ _ _ _ _ _ _ F_3f1e8 eq_refl D_3f1e8)). gr. imm_norm.
        wz3 (v_addiw (Z_to_bv 64 2048) 0) 2048%Z.
        mstep ltac:(eapply (step_bge_ft _ _ _ _ _ _ _ _ _ F_3f1ec eq_refl D_3f1ec); gr; rewrite getr_zero; apply c_lts_pos_ft; lia).
        mstep ltac:(eapply (step_lui_at _ _ _ _ _ _ _ _ (Z_to_bv 64 4096) F_3f1f0 eq_refl D_3f1f0); reflexivity).
        mstep ltac:(exact (step_addi _ _ _ _ _ _ _ _ _ F_3f1f4 eq_refl D_3f1f4)). gr. zn.
        mstep ltac:(exact (step_addi _ _ _ _ _ _ _ _ _ F_3f1f8 eq_refl D_3f1f8)). rewrite getr_zero. zn.
        mstep ltac:(exact (step_addi _ _ _ _ _ _ _ _ _ F_3f1fc eq_refl D_3f1fc)). rewrite getr_zero, k_m1_val.
        mstep ltac:(exact (step_sll _ _ _ _ _ _ _ _ _ F_3f200 eq_refl D_3f200)). gr.
        wz3 (v_sll (Z_to_bv 64 896) (Z_to_bv 64 (20 + -15))) 28672%Z.
        mstep ltac:(eapply (@step_ld _ _ _ _ _ _ _ _ _ _ _ hint F_3f204 eq_refl D_3f204);
                     [ gr; imm_norm; zn; exact Ch | apply bytes_le_to_Z_8 ]).
        rewrite (zbv_self' hint). fold h.
        mstep ltac:(exact (step_sll _ _ _ _ _ _ _ _ _ F_3f208 eq_refl D_3f208)). gr.
        wz3 (v_sll (Z_to_bv 64 (2 ^ 64 - 1)) (Z_to_bv 64 (20 + -9))) (2 ^ 64 - 2048)%Z.
        mstep ltac:(exact (step_addi _ _ _ _ _ _ _ _ _ F_3f20c eq_refl D_3f20c)). gr. zn.
        mstep ltac:(exact (step_add _ _ _ _ _ _ _ _ _ F_3f210 eq_refl D_3f210)). gr. rewrite v_add_zbv by lia.
        mstep ltac:(exact (step_add _ _ _ _ _ _ _ _ _ F_3f214 eq_refl D_3f214)). gr. rewrite v_add_zbv by lia.
        mstep ltac:(exact (step_xori _ _ _ _ _ _ _ _ _ F_3f218 eq_refl D_3f218)). gr. imm_norm.
        wz3 (v_xori (Z_to_bv 64 (2 ^ 64 - 2048)) (-1)) 2047%Z.
        mstep ltac:(exact (step_slli _ _ _ _ _ _ _ _ _ F_3f21c eq_refl D_3f21c)). gr. imm_norm.
        wz3 (v_slli (Z_to_bv 64 (2048 + -1)) 32) (2047 * 2 ^ 32)%Z.
        mstep ltac:(exact (PropExec.step_srli _ _ _ _ _ _ _ _ _ F_3f220 eq_refl D_3f220)). gr. imm_norm.
        wz3 (v_srli (Z_to_bv 64 (2047 * 2 ^ 32)) 32) 2047%Z.
        mstep ltac:(exact (step_add _ _ _ _ _ _ _ _ _ F_3f224 eq_refl D_3f224)). gr. rewrite v_add_any.
        mstep ltac:(exact (step_addi _ _ _ _ _ _ _ _ _ F_3f228 eq_refl D_3f228)). gr. rewrite v_addi_any.
        apply mst_refl.
      - gr. unfold N3, FL3. repeat split; try (apply (f_equal (Z_to_bv 64)); lia); try reflexivity.
        intros r Hr. unfold a_clob3 in Hr.
        repeat (rewrite getr_other by (intros ->; cbn in Hr; discriminate)). reflexivity.
    Qed.

    (* [comment removed for export] *)
    Let i0 : Z := ((p0 - h) mod N3)%Z.
    #[using="Type"] Lemma i0_rng3 : (0 <= i0 < N3)%Z. Proof. unfold i0, N3. apply Z.mod_pos_bound. lia. Qed.
    #[using="FL Hp0"] Lemma pos_i03 : pos3 i0 = p0.
    Proof.
      unfold pos3, i0, N3. rewrite Zplus_mod_idemp_r. replace (h + (p0 - h))%Z with p0 by lia.
      apply Z.mod_small. unfold N3 in Hp0. lia.
    Qed.
    #[using="p0 i0"] Lemma pos_rng3 : forall i, (0 <= pos3 i < N3)%Z. Proof. intros i. unfold pos3, N3. apply Z.mod_pos_bound. lia. Qed.

    Definition l_clob3 (r : reg) : bool := (bv_eqb r 5 || bv_eqb r 10 || bv_eqb r 12 || bv_eqb r 15 || bv_eqb r 17)%bool.

    #[using="ctx thr db beg a2v a3v H Hflags Hp0"] Lemma blk_L3 : forall (k : nat) i regs m,
      (i + Z.of_nat k = i0)%Z -> (0 <= i)%Z -> sfr m ->
      getr regs 10 = Z_to_bv 64 (N3 - i) -> getr regs 12 = Z_to_bv 64 (h + i) ->
      getr regs 13 = Z_to_bv 64 (fs + FL3) -> getr regs 14 = Z_to_bv 64 (N3 - 1) ->
      exists i' regs',
        (i <= i' <= i0)%Z /\ bv_unsigned (FL (pos3 i')) = 0%Z
        /\ msteps SEGS (mkst regs (0x3f22c : word) m rom) (mkst regs' (0x3f2a4 : word) m rom)
        /\ getr regs' 12 = Z_to_bv 64 (h + i') /\ getr regs' 17 = Z_to_bv 64 (pos3 i')
        /\ getr regs' 15 = Z_to_bv 64 (fs + FL3 + pos3 i')
        /\ (forall r, l_clob3 r = false -> getr regs' r = getr regs r).
    Proof.
      pose proof HU as U. pose proof HF as (F1 & F2 & F3 & F4). unfold FS_AREA in *. pose proof i0_rng3 as I0. pose proof Hp0 as [P0 P1].
      unfold N3 in *.
      unfold FL3 in *.
      induction k as [|k IH]; intros i regs m Hk Hi FR H10 H12 H13 H14.
      - (* [comment removed for export] *)
        cbn [Z.of_nat] in Hk. rewrite Z.add_0_r in Hk. subst i.
        pose proof (pos_rng3 i0) as PR. unfold N3 in PR.
        pose proof (Hflags (pos3 i0) PR) as CF. rewrite <- (rdn_sfr m) in CF by (first [exact FR | cbn; unfold SM_FRAME, FL3; lia]).
        exists i0. eexists. split; [lia|]. split; [rewrite pos_i03; exact P1|]. split.
        + mstep ltac:(exact (step_and _ _ _ _ _ _ _ _ _ F_3f22c eq_refl D_3f22c)). gr. rewrite H12, H14.
          change (2048 - 1)%Z with (2 ^ 11 - 1)%Z. rewrite v_and_mask by lia. change (2 ^ 11)%Z with 2048%Z. fold N3. fold (pos3 i0).
          mstep ltac:(exact (step_add _ _ _ _ _ _ _ _ _ F_3f230 eq_refl D_3f230)). gr. rewrite H13. unfold FL3. rewrite v_add_zbv by lia.
          mstep ltac:(eapply (@step_lbu _ _ _ _ _ _ _ _ _ _ (FL (pos3 i0)) F_3f234 eq_refl D_3f234); gr; imm_norm; zn; rewrite ?Z.add_0_r; unfold FL3 in CF; exact CF).
          replace (bv_unsigned (FL (pos3 i0))) with 0%Z by (rewrite pos_i03, P1; reflexivity).
          mstep ltac:(eapply (step_beq_tk _ _ _ _ _ _ _ _ _ F_3f238 eq_refl D_3f238); gr; rewrite getr_zero; br_eq).
          apply mst_refl.
        + gr. unfold FL3. repeat split; try (apply (f_equal (Z_to_bv 64)); lia); try reflexivity; try assumption.
          intros r Hr. unfold l_clob3 in Hr.
          repeat (rewrite getr_other by (intros ->; cbn in Hr; discriminate)). reflexivity.
      - (* [comment removed for export] *)
        pose proof (pos_rng3 i) as PR. unfold N3 in PR.
        pose proof (Hflags (pos3 i) PR) as CF. rewrite <- (rdn_sfr m) in CF by (first [exact FR | cbn; unfold SM_FRAME, FL3; lia]).
        pose proof (bv_unsigned_in_range 8 (FL (pos3 i))) as BR. change (bv_modulus 8) with 256%Z in BR.
        destruct (Z.eq_dec (bv_unsigned (FL (pos3 i))) 0) as [Z0|NZ].
        + exists i. eexists. split; [lia|]. split; [exact Z0|]. split.
          * mstep ltac:(exact (step_and _ _ _ _ _ _ _ _ _ F_3f22c eq_refl D_3f22c)). gr. rewrite H12, H14.
            change (2048 - 1)%Z with (2 ^ 11 - 1)%Z. rewrite v_and_mask by lia. change (2 ^ 11)%Z with 2048%Z. fold N3. fold (pos3 i).
            mstep ltac:(exact (step_add _ _ _ _ _ _ _ _ _ F_3f230 eq_refl D_3f230)). gr. rewrite H13. unfold FL3. rewrite v_add_zbv by lia.
            mstep ltac:(eapply (@step_lbu _ _ _ _ _ _ _ _ _ _ (FL (pos3 i)) F_3f234 eq_refl D_3f234); gr; imm_norm; zn; rewrite ?Z.add_0_r; unfold FL3 in CF; exact CF).
            rewrite Z0.
            mstep ltac:(eapply (step_beq_tk _ _ _ _ _ _ _ _ _ F_3f238 eq_refl D_3f238); gr; rewrite getr_zero; br_eq).
            apply mst_refl.
          * gr. unfold FL3. repeat split; try (apply (f_equal (Z_to_bv 64)); lia); try reflexivity; try assumption.
            intros r Hr. unfold l_clob3 in Hr.
            repeat (rewrite getr_other by (intros ->; cbn in Hr; discriminate)). reflexivity.
        + assert (NI : i <> i0) by (intros ->; rewrite pos_i03 in NZ; exact (NZ P1)).
          edestruct (IH (i + 1)%Z
            (regupd (regupd (regupd (regupd (regupd regs 17 (Z_to_bv 64 (pos3 i))) 15 (Z_to_bv 64 (fs + FL3 + pos3 i)))
               5 (Z_to_bv 64 (bv_unsigned (FL (pos3 i))))) 10 (Z_to_bv 64 (2048 - i - 1))) 12 (Z_to_bv 64 (h + i + 1))) m)
            as (i' & regs' & R1 & R2 & M & Q12 & Q17 & Q15 & QK); try lia; try exact FR.
          1-4: gr; first [assumption | apply (f_equal (Z_to_bv 64)); lia].
          exists i', regs'. split; [lia|]. split; [exact R2|]. split.
          * mstep ltac:(exact (step_and _ _ _ _ _ _ _ _ _ F_3f22c eq_refl D_3f22c)). gr. rewrite H12, H14.
            change (2048 - 1)%Z with (2 ^ 11 - 1)%Z. rewrite v_and_mask by lia. change (2 ^ 11)%Z with 2048%Z. fold N3. fold (pos3 i).
            mstep ltac:(exact (step_add _ _ _ _ _ _ _ _ _ F_3f230 eq_refl D_3f230)). gr. rewrite H13. rewrite v_add_zbv by (unfold FL3; lia).
            mstep ltac:(eapply (@step_lbu _ _ _ _ _ _ _ _ _ _ (FL (pos3 i)) F_3f234 eq_refl D_3f234); gr; imm_norm; zn; rewrite ?Z.add_0_r; exact CF).
            mstep ltac:(eapply (step_beq_ft _ _ _ _ _ _ _ _ _ F_3f238 eq_refl D_3f238); gr; rewrite getr_zero; br_eq).
            mstep ltac:(exact (step_addiw _ _ _ _ _ _ _ _ _ F_3f23c eq_refl D_3f23c)). gr. rewrite H10. imm_norm.
            rewrite v_addiw_small by lia.
            mstep ltac:(exact (step_addi _ _ _ _ _ _ _ _ _ F_3f240 eq_refl D_3f240)). gr. rewrite H12, v_addi_any.
            mstep ltac:(eapply (step_bne_tk _ _ _ _ _ _ _ _ _ F_3f244 eq_refl D_3f244); gr; rewrite getr_zero; br_eq).
            replace (2048 - i + -1)%Z with (2048 - i - 1)%Z by lia. exact M.
          * split; [exact Q12|]. split; [exact Q17|]. split; [exact Q15|].
            intros r Hr. rewrite (QK r Hr). unfold l_clob3 in Hr.
            repeat (rewrite getr_other by (intros ->; cbn in Hr; discriminate)). reflexivity.
    Qed.

    (* [comment removed for export] *)
    (* [comment removed for export] *)
    Definition WR3 (m : word -> option byte) (i p : Z) : word -> option byte :=
      wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes m
        (Z_to_bv 64 (fs + 24)) (word_to_le_bytes 8 (Z_to_bv 64 (h + i + 1))))
        (Z_to_bv 64 (fs + FL3 + p)) (word_to_le_bytes 1 (Z_to_bv 64 1)))
        (Z_to_bv 64 (ff3 p + 24)) (word_to_le_bytes 8 (Z_to_bv 64 usp)))
        (Z_to_bv 64 (ff3 p + 504)) (word_to_le_bytes 8 (Z_to_bv 64 (fs + FL3 + p))))
        (Z_to_bv 64 (SB + ff3 p / 8)) (word_to_le_bytes 8 (Z_to_bv 64 0)))
        (Z_to_bv 64 (SB + ff3 p / 8 + 8)) (word_to_le_bytes 8 (Z_to_bv 64 0)))
        (Z_to_bv 64 (SB + ff3 p / 8 + 16)) (word_to_le_bytes 8 (Z_to_bv 64 0)))
        (Z_to_bv 64 (SB + ff3 p / 8 + 24)) (word_to_le_bytes 8 (Z_to_bv 64 0)))
        (Z_to_bv 64 (SB + ff3 p / 8 + 32)) (word_to_le_bytes 8 (Z_to_bv 64 0)))
        (Z_to_bv 64 (SB + ff3 p / 8 + 40)) (word_to_le_bytes 8 (Z_to_bv 64 0)))
        (Z_to_bv 64 (SB + ff3 p / 8 + 48)) (word_to_le_bytes 8 (Z_to_bv 64 0)))
        (Z_to_bv 64 (SB + ff3 p / 8 + 56)) (word_to_le_bytes 8 (Z_to_bv 64 0)).

    #[using="Type"] Lemma WR_agree3 : forall ma mb i p (x : word), ma x = mb x -> WR3 ma i p x = WR3 mb i p x.
    Proof. intros. unfold WR3. repeat apply wbytes_agree. assumption. Qed.
    #[using="Type"] Lemma WR_keep3 : forall m i p (x : word), m x <> None -> WR3 m i p x <> None.
    Proof. intros. unfold WR3. repeat apply wbytes_keep. assumption. Qed.
    #[using="Type"] Lemma WR_sok3 : forall m i p (x : word), store_ok SEGS m x 1 = true -> store_ok SEGS (WR3 m i p) x 1 = true.
    Proof. intros. unfold WR3. repeat apply store_ok1_wbytes. assumption. Qed.

    #[using="mem rom ctx thr db beg a2v a3v H p0 i0"] Lemma WR_stack3 : forall m i p a, (0 <= p < N3)%Z -> (usp - 32 <= a)%Z -> (a + 8 <= usp)%Z ->
      rdn SEGS (WR3 m i p) (Z_to_bv 64 a) 8 = rdn SEGS m (Z_to_bv 64 a) 8.
    Proof.
      intros m i p a Hp Ha Hb. pose proof HU as U. pose proof HF as (F1 & F2 & F3 & F4). unfold FS_AREA, N3, ff3, FR3, FL3 in *.
      pose proof SB_val.
      assert (ff_hi : (fs + 3182592 + 512 * p + 512 <= 2 ^ 47)%Z) by lia.
      pose proof (Z.div_pos (fs + 3182592 + 512 * p) 8 ltac:(lia) ltac:(lia)).
      pose proof (Z.div_lt_upper_bound (fs + 3182592 + 512 * p) 8 (2 ^ 44) ltac:(lia) ltac:(lia)).
      unfold WR3, ff3, FL3, FR3. rewrite !rdn_wbytes_out; try reflexivity; len8; rewrite ?zbv_u by (ltac2:(LK.k [@Hp; @Ha; @Hb; @U; @F1; @F2; @ff_hi; @H0; @H1; @H2; @F4]); lia); (ltac2:(LK.k [@Hp; @Ha; @Hb; @U; @F1; @F2; @ff_hi; @H0; @H1; @H2; @F4]); lia).
    Qed.

    Definition f_clob3 (r : reg) : bool :=
      (bv_eqb r 1 || bv_eqb r 2 || bv_eqb r 5 || bv_eqb r 8 || bv_eqb r 9 || bv_eqb r 10 || bv_eqb r 11 || bv_eqb r 12
       || bv_eqb r 13 || bv_eqb r 14 || bv_eqb r 15 || bv_eqb r 16 || bv_eqb r 17 || bv_eqb r 18)%bool.

    #[using="ctx thr db beg a2v a3v H Hret p0 Whint Wflag Wframe Wshad i0"] Lemma blk_F3 : forall regs m i p,
      sfr m -> (forall x : word, (usp - 32 <= bv_unsigned x)%Z -> m x = m1 x) ->
      (0 <= p < N3)%Z -> (0 <= i < N3)%Z ->
      getr regs 2 = Z_to_bv 64 (usp - 32) -> getr regs 8 = Z_to_bv 64 usp -> getr regs 9 = Z_to_bv 64 fs ->
      getr regs 18 = Z_to_bv 64 20 -> getr regs 11 = Z_to_bv 64 (fs + 4096) ->
      getr regs 12 = Z_to_bv 64 (h + i) -> getr regs 17 = Z_to_bv 64 p -> getr regs 15 = Z_to_bv 64 (fs + FL3 + p) ->
      exists regs',
        msteps SEGS (mkst regs (0x3f2a4 : word) m rom) (mkst regs' ra (WR3 m i p) rom)
        /\ getr regs' 10 = Z_to_bv 64 (ff3 p) /\ getr regs' 2 = Z_to_bv 64 usp /\ getr regs' 1 = ra
        /\ getr regs' 8 = getr regs0 8 /\ getr regs' 9 = getr regs0 9 /\ getr regs' 18 = getr regs0 18
        /\ (forall r, f_clob3 r = false -> getr regs' r = getr regs r).
    Proof.
      intros regs m i p FR AG Hp Hi H2 H8 H9 H18 H11 H12 H17 H15.
      pose proof HU as U. pose proof HF as (F1 & F2 & F3 & F4). pose proof SB_val as HSB. unfold FS_AREA, N3, FL3 in *.
      destruct FR as (FRa & FRb & FRc).
      assert (ff_lo : (0x608000 <= ff3 p)%Z) by (unfold ff3, FR3; lia).
      assert (ff_hi : (ff3 p + 512 <= 2 ^ 47)%Z) by (unfold ff3, FR3; lia).
      pose proof (Z.div_pos (ff3 p) 8 ltac:(lia) ltac:(lia)) as D1.
      pose proof (Z.div_lt_upper_bound (ff3 p) 8 (2 ^ 44) ltac:(lia) ltac:(lia)) as D2.
      (* [comment removed for export] *)
      assert (RD : forall a v, (usp - 32 <= a)%Z -> (a + 8 <= usp)%Z ->
                rdn SEGS m1 (Z_to_bv 64 a) 8 = Some (word_to_le_bytes 8 v) ->
                rdn SEGS (WR3 m i p) (Z_to_bv 64 a) 8 = Some (word_to_le_bytes 8 v)).
      { intros a v Ha Hb R. rewrite WR_stack3 by (unfold N3; lia). rewrite <- R. apply rdn_ext; [rewrite zbv_u by lia; cbn; lia|].
        intros x Hx. rewrite zbv_u in Hx by lia. apply AG. lia. }
      pose proof (RD (usp - 8)%Z _ ltac:(lia) ltac:(lia) rd1_8) as R8. pose proof (RD (usp - 16)%Z _ ltac:(lia) ltac:(lia) rd1_16) as R16.
      pose proof (RD (usp - 24)%Z _ ltac:(lia) ltac:(lia) rd1_24) as R24. pose proof (RD (usp - 32)%Z _ ltac:(lia) ltac:(lia) rd1_32) as R32.
      (* [comment removed for export] *)
      set (m4 := wbytes (wbytes (wbytes (wbytes m
        (Z_to_bv 64 (fs + 24)) (word_to_le_bytes 8 (Z_to_bv 64 (h + i + 1))))
        (Z_to_bv 64 (fs + 32768 + p)) (word_to_le_bytes 1 (Z_to_bv 64 1)))
        (Z_to_bv 64 (ff3 p + 24)) (word_to_le_bytes 8 (Z_to_bv 64 usp)))
        (Z_to_bv 64 (ff3 p + 504)) (word_to_le_bytes 8 (Z_to_bv 64 (fs + 32768 + p)))).
      assert (C4 : cells m4).
      { pose proof (s_cells _ _ _ _ _ _ _ _ _ H) as C. unfold cells, cell in *. unfold m4.
        rewrite !rdn_wbytes_out; len8; rewrite ?zbv_u by (ltac2:(LK.k [@F1; @F2; @Hp; @U; @ff_lo; @ff_hi]); lia); try (cbn; unfold ff3, FR3 in *; (ltac2:(LK.k [@F1; @F2; @Hp; @U; @ff_lo; @ff_hi]); lia)).
        rewrite !(rdn_sfr m) by (first [split; [exact FRa|split; [exact FRb|exact FRc]] | cbn; unfold SM_FRAME; lia]). exact C. }
      (* [comment removed for export] *)
      assert (P1 : exists r1,
        msteps SEGS (mkst regs (0x3f2a4 : word) m rom) (mkst r1 (0x3f510 : word) m4 rom)
        /\ getr r1 10 = Z_to_bv 64 (ff3 p) /\ getr r1 1 = Z_to_bv 64 0x3f2e4 /\ getr r1 2 = Z_to_bv 64 (usp - 32)
        /\ getr r1 9 = Z_to_bv 64 (ff3 p)
        /\ (forall r : reg, r <> 1 -> r <> 9 -> r <> 10 -> r <> 12 -> r <> 13 -> r <> 17 -> getr r1 r = getr regs r)).
      { eexists. split.
        - mstep ltac:(exact (step_addi _ _ _ _ _ _ _ _ _ F_3f2a4 eq_refl D_3f2a4)). gr. rewrite H12, v_addi_any.
          mstep ltac:(exact (step_addi _ _ _ _ _ _ _ _ _ F_3f2a8 eq_refl D_3f2a8)). rewrite getr_zero. zn.
          mstep ltac:(exact (step_addi _ _ _ _ _ _ _ _ _ F_3f2ac eq_refl D_3f2ac)). gr. rewrite H18. zn.
          msd13 F_3f2b0 D_3f2b0 (fs + 24)%Z (Z_to_bv 64 (h + i + 1)) H9
               ltac:(apply store_ok8_bytes; [lia|lia|]; intros j Hj; apply FRc; replace (fs + 24 + j)%Z with (fs + (24 + j))%Z by lia; apply Whint; lia).
          mstep ltac:(eapply (step_sb _ _ _ _ _ _ _ _ _ F_3f2b4 eq_refl D_3f2b4);
                       gr; rewrite H15; imm_norm; zn; rewrite ?Z.add_0_r; apply store_ok1_wbytes; apply FRc; apply Wflag; lia).
          gr. rewrite H15. zn. rewrite ?Z.add_0_r.
          mstep ltac:(exact (step_sll _ _ _ _ _ _ _ _ _ F_3f2b8 eq_refl D_3f2b8)). gr.
          wz3 (v_sll (Z_to_bv 64 1) (Z_to_bv 64 (20 + -5))) 32768%Z.
          mstep ltac:(exact (step_addi _ _ _ _ _ _ _ _ _ F_3f2bc eq_refl D_3f2bc)). rewrite getr_zero. zn.
          mstep ltac:(exact (step_slli _ _ _ _ _ _ _ _ _ F_3f2c0 eq_refl D_3f2c0)). gr. rewrite H17. imm_norm.
          rewrite (v_slli_zbv p 9) by lia.
          mstep ltac:(exact (step_sll _ _ _ _ _ _ _ _ _ F_3f2c4 eq_refl D_3f2c4)). gr. rewrite H18.
          wz3 (v_sll (Z_to_bv 64 3) (Z_to_bv 64 20)) (3 * 2 ^ 20)%Z.
          mstep ltac:(exact (step_add _ _ _ _ _ _ _ _ _ F_3f2c8 eq_refl D_3f2c8)). gr. rewrite H11, v_add_zbv by lia.
          mstep ltac:(exact (step_add _ _ _ _ _ _ _ _ _ F_3f2cc eq_refl D_3f2cc)). gr. rewrite v_add_zbv by lia.
          mstep ltac:(exact (step_add _ _ _ _ _ _ _ _ _ F_3f2d0 eq_refl D_3f2d0)). gr. rewrite v_add_zbv by lia.
          change (2 ^ 9)%Z with 512%Z. replace (fs + 4096 + 32768 + (3 * 2 ^ 20 + p * 512))%Z with (ff3 p) by (unfold ff3, FR3; lia).
          msd13 F_3f2d4 D_3f2d4 (ff3 p + 24)%Z (Z_to_bv 64 usp) H8
               ltac:(apply store_ok8_bytes; [lia|lia|]; intros j Hj; repeat apply store_ok1_wbytes; apply FRc;
                     unfold ff3, FR3; replace (fs + 3182592 + 512 * p + 24 + j)%Z with (fs + 3182592 + 512 * p + (24 + j))%Z by lia; apply Wframe; lia).
          msd13 F_3f2d8 D_3f2d8 (ff3 p + 504)%Z (Z_to_bv 64 (fs + 32768 + p)) H8
               ltac:(apply store_ok8_bytes; [lia|lia|]; intros j Hj; repeat apply store_ok1_wbytes; apply FRc;
                     unfold ff3, FR3; replace (fs + 3182592 + 512 * p + 504 + j)%Z with (fs + 3182592 + 512 * p + (504 + j))%Z by lia; apply Wframe; lia).
          change (wbytes _ _ _) with m4.
          mstep ltac:(exact (step_addi _ _ _ _ _ _ _ _ _ F_3f2dc eq_refl D_3f2dc)). gr. zn. rewrite ?Z.add_0_r.
          mstep ltac:(eapply (step_jal_link _ _ _ _ _ _ _ _ F_3f2e0 eq_refl D_3f2e0)). rewrite lit_5c0d83.
          apply mst_refl.
        - gr. repeat split; try reflexivity; try assumption; try (apply (f_equal (Z_to_bv 64)); lia).
          intros r N1 N9 N10 N12 N13 N17. repeat (rewrite getr_other by congruence). reflexivity. }
      destruct P1 as (r1 & M1 & P10 & P1ra & P2 & P9 & PK).
      destruct (mem_to_shadow_5e918 rom r1 m4 (ff3 p) (Z_to_bv 64 0x3f2e4) C4 ltac:(lia)
                  ltac:(apply (in_mem_frame fs (ff3 p) 512 HFB); [lia|unfold ff3, FR3; lia|unfold ff3, FR3 in *; unfold FS_AREA in *; lia|unfold FS_AREA in *; lia|lia])
                  P10 P1ra ret_ok_5c0d83)
        as (q & MQ & Q10 & QK).
      assert (Q2 : getr q 2 = Z_to_bv 64 (usp - 32)) by (rewrite QK by reflexivity; exact P2).
      assert (Q9 : getr q 9 = Z_to_bv 64 (ff3 p)) by (rewrite QK by reflexivity; exact P9).
      eexists. split.
      - eapply msteps_trans; [exact M1|]. eapply msteps_trans; [exact MQ|].
        replace (Z_to_bv 64 0x3f2e4) with (0x3f2e4 : word) by (apply bv_eq; reflexivity).
        mstep ltac:(exact (step_addi _ _ _ _ _ _ _ _ _ F_3f2e4 eq_refl D_3f2e4)). gr. rewrite Q10. zn. rewrite ?Z.add_0_r.
        mstep ltac:(exact (step_addi _ _ _ _ _ _ _ _ _ F_3f2e8 eq_refl D_3f2e8)). gr. rewrite Q9. zn. rewrite ?Z.add_0_r.
        mstep ltac:(exact (step_addi _ _ _ _ _ _ _ _ _ F_3f2ec eq_refl D_3f2ec)). rewrite getr_zero. zn.
        msd13 F_3f2f0 D_3f2f0 (SB + ff3 p / 8)%Z (Z_to_bv 64 0) Q2
             ltac:(apply store_ok8_bytes; [lia|lia|]; intros j Hj; unfold m4; repeat apply store_ok1_wbytes; apply FRc;
                   unfold ff3, FR3; apply Wshad; lia).
        msd13 F_3f2f4 D_3f2f4 (SB + ff3 p / 8 + 8)%Z (Z_to_bv 64 0) Q2
             ltac:(apply store_ok8_bytes; [lia|lia|]; intros j Hj; unfold m4; repeat apply store_ok1_wbytes; apply FRc;
                   unfold ff3, FR3; replace (SB + (fs + 3182592 + 512 * p) / 8 + 8 + j)%Z with (SB + (fs + 3182592 + 512 * p) / 8 + (8 + j))%Z by lia;
                   apply Wshad; lia).
        msd13 F_3f2f8 D_3f2f8 (SB + ff3 p / 8 + 16)%Z (Z_to_bv 64 0) Q2
             ltac:(apply store_ok8_bytes; [lia|lia|]; intros j Hj; unfold m4; repeat apply store_ok1_wbytes; apply FRc;
                   unfold ff3, FR3; replace (SB + (fs + 3182592 + 512 * p) / 8 + 16 + j)%Z with (SB + (fs + 3182592 + 512 * p) / 8 + (16 + j))%Z by lia;
                   apply Wshad; lia).
        msd13 F_3f2fc D_3f2fc (SB + ff3 p / 8 + 24)%Z (Z_to_bv 64 0) Q2
             ltac:(apply store_ok8_bytes; [lia|lia|]; intros j Hj; unfold m4; repeat apply store_ok1_wbytes; apply FRc;
                   unfold ff3, FR3; replace (SB + (fs + 3182592 + 512 * p) / 8 + 24 + j)%Z with (SB + (fs + 3182592 + 512 * p) / 8 + (24 + j))%Z by lia;
                   apply Wshad; lia).
        msd13 F_3f300 D_3f300 (SB + ff3 p / 8 + 32)%Z (Z_to_bv 64 0) Q2
             ltac:(apply store_ok8_bytes; [lia|lia|]; intros j Hj; unfold m4; repeat apply store_ok1_wbytes; apply FRc;
                   unfold ff3, FR3; replace (SB + (fs + 3182592 + 512 * p) / 8 + 32 + j)%Z with (SB + (fs + 3182592 + 512 * p) / 8 + (32 + j))%Z by lia;
                   apply Wshad; lia).
        msd13 F_3f304 D_3f304 (SB + ff3 p / 8 + 40)%Z (Z_to_bv 64 0) Q2
             ltac:(apply store_ok8_bytes; [lia|lia|]; intros j Hj; unfold m4; repeat apply store_ok1_wbytes; apply FRc;
                   unfold ff3, FR3; replace (SB + (fs + 3182592 + 512 * p) / 8 + 40 + j)%Z with (SB + (fs + 3182592 + 512 * p) / 8 + (40 + j))%Z by lia;
                   apply Wshad; lia).
        msd13 F_3f308 D_3f308 (SB + ff3 p / 8 + 48)%Z (Z_to_bv 64 0) Q2
             ltac:(apply store_ok8_bytes; [lia|lia|]; intros j Hj; unfold m4; repeat apply store_ok1_wbytes; apply FRc;
                   unfold ff3, FR3; replace (SB + (fs + 3182592 + 512 * p) / 8 + 48 + j)%Z with (SB + (fs + 3182592 + 512 * p) / 8 + (48 + j))%Z by lia;
                   apply Wshad; lia).
        msd13 F_3f30c D_3f30c (SB + ff3 p / 8 + 56)%Z (Z_to_bv 64 0) Q2
             ltac:(apply store_ok8_bytes; [lia|lia|]; intros j Hj; unfold m4; repeat apply store_ok1_wbytes; apply FRc;
                   unfold ff3, FR3; replace (SB + (fs + 3182592 + 512 * p) / 8 + 56 + j)%Z with (SB + (fs + 3182592 + 512 * p) / 8 + (56 + j))%Z by lia;
                   apply Wshad; lia).
        change (wbytes _ _ _) with (WR3 m i p).
        mstep ltac:(eapply (@step_ld _ _ _ _ _ _ _ _ _ _ _ ra F_3f310 eq_refl D_3f310);
                     [ gr; rewrite Q2; imm_norm; zn; replace (usp - 32 + 24)%Z with (usp - 8)%Z by lia; exact R8 | apply bytes_le_to_Z_8 ]).
        mstep ltac:(eapply (@step_ld _ _ _ _ _ _ _ _ _ _ _ (getr regs0 8) F_3f314 eq_refl D_3f314);
                     [ gr; rewrite Q2; imm_norm; zn; replace (usp - 32 + 16)%Z with (usp - 16)%Z by lia; exact R16 | apply bytes_le_to_Z_8 ]).
        mstep ltac:(eapply (@step_ld _ _ _ _ _ _ _ _ _ _ _ (getr regs0 9) F_3f318 eq_refl D_3f318);
                     [ gr; rewrite Q2; imm_norm; zn; replace (usp - 32 + 8)%Z with (usp - 24)%Z by lia; exact R24 | apply bytes_le_to_Z_8 ]).
        mstep ltac:(eapply (@step_ld _ _ _ _ _ _ _ _ _ _ _ (getr regs0 18) F_3f31c eq_refl D_3f31c);
                     [ gr; rewrite Q2; imm_norm; zn; rewrite ?Z.add_0_r; exact R32 | apply bytes_le_to_Z_8 ]).
        mstep ltac:(exact (step_addi _ _ _ _ _ _ _ _ _ F_3f320 eq_refl D_3f320)). gr. rewrite Q2. zn.
        replace (usp - 32 + 32)%Z with usp by lia.
        eapply mst_step; [reflexivity | eapply (step_jalr_x0 _ _ _ _ _ _ _ _ ra F_3f324 eq_refl D_3f324); gr; reflexivity |].
        imm_norm. rewrite Hret. apply mst_refl.
      - gr. repeat split; try reflexivity.
        intros r Hr. unfold f_clob3 in Hr.
        repeat (rewrite getr_other by (intros ->; cbn in Hr; discriminate)).
        rewrite QK by (unfold m2s_clob; repeat match type of Hr with (?a || ?b)%bool = false => apply orb_false_iff in Hr; destruct Hr as [Hr ?] end;
                       repeat match goal with Hb : bv_eqb r _ = false |- _ => rewrite Hb; clear Hb end; reflexivity).
        apply PK; intros ->; cbn in Hr; discriminate.
    Qed.

    (* [comment removed for export] *)
    #[using="ctx thr db beg a2v a3v H Hret H01 H02 H04 p0 Hhint Hflags Hp0 Whint Wflag Wframe Wshad i0"] Theorem sm3_AM :
      exists i p regs' m',
        (0 <= i < N3)%Z /\ p = pos3 i /\ bv_unsigned (FL p) = 0%Z
        /\ msteps SEGS (mkst regs0 (0x3f198 : word) mem rom) (mkst regs' ra m' rom)
        /\ getr regs' 10 = Z_to_bv 64 (ff3 p) /\ getr regs' 2 = Z_to_bv 64 usp /\ getr regs' 1 = ra
        /\ (forall r, sm_clob r = false -> getr regs' r = getr regs0 r)
        /\ (forall x : word, (bv_unsigned x < usp - SM_FRAME \/ usp <= bv_unsigned x)%Z -> m' x = WR3 mem i p x)
        /\ (forall x, mem x <> None -> m' x <> None)
        /\ (forall x, store_ok SEGS mem x 1 = true -> store_ok SEGS m' x 1 = true).
    Proof.
      pose proof HU as U. pose proof i0_rng3 as I0.
      destruct blk_PT3 as (q1 & m2 & M1 & A2 & A8 & A10 & A4 & AK & FR & AG).
      destruct (blk_A3 q1 m2 FR A10) as (q2 & M2 & B9 & B18 & B10 & B12 & B13 & B14 & B11 & BK).
      destruct (blk_L3 (Z.to_nat i0) 0 q2 m2 ltac:(lia) ltac:(lia) FR B10 B12 B13 B14)
        as (i & q3 & Hi & HZ & M3 & C12 & C17 & C15 & CK).
      assert (C2 : getr q3 2 = Z_to_bv 64 (usp - 32)) by (rewrite CK, BK by reflexivity; exact A2).
      assert (C8 : getr q3 8 = Z_to_bv 64 usp) by (rewrite CK, BK by reflexivity; exact A8).
      assert (C9 : getr q3 9 = Z_to_bv 64 fs) by (rewrite CK by reflexivity; exact B9).
      assert (C18 : getr q3 18 = Z_to_bv 64 20) by (rewrite CK by reflexivity; exact B18).
      assert (C11 : getr q3 11 = Z_to_bv 64 (fs + 4096)) by (rewrite CK by reflexivity; exact B11).
      pose proof (pos_rng3 i) as PR.
      destruct (blk_F3 q3 m2 i (pos3 i) FR AG PR ltac:(lia) C2 C8 C9 C18 C11 C12 C17 C15)
        as (q4 & M4 & D10 & D2 & D1 & D8 & D9 & D18 & DK).
      exists i, (pos3 i), q4, (WR3 m2 i (pos3 i)).
      split; [lia|]. split; [reflexivity|]. split; [exact HZ|]. split.
      { eapply msteps_trans; [exact M1|]. eapply msteps_trans; [exact M2|]. eapply msteps_trans; [exact M3|]. exact M4. }
      split; [exact D10|]. split; [exact D2|]. split; [exact D1|]. split.
      { intros r Hr.
        destruct (bv_eq_dec _ r 1) as [-> | X1]; [rewrite D1; symmetry; exact H01|].
        destruct (bv_eq_dec _ r 2) as [-> | N2]; [rewrite D2; symmetry; exact H02|].
        destruct (bv_eq_dec _ r 8) as [-> | N8]; [exact D8|].
        destruct (bv_eq_dec _ r 9) as [-> | N9]; [exact D9|].
        destruct (bv_eq_dec _ r 18) as [-> | N18]; [exact D18|].
        assert (NE : forall k : reg, r <> k -> bv_eqb r k = false) by (intros k Hk; apply bv_eqb_neq; exact Hk).
        pose proof (NE _ X1) as T1. pose proof (NE _ N2) as T2. pose proof (NE _ N8) as T8. pose proof (NE _ N9) as T9. pose proof (NE _ N18) as T18.
        unfold sm_clob in Hr.
        apply orb_false_iff in Hr as [Hr T17]. apply orb_false_iff in Hr as [Hr T16]. apply orb_false_iff in Hr as [Hr T15].
        apply orb_false_iff in Hr as [Hr T14]. apply orb_false_iff in Hr as [Hr T13]. apply orb_false_iff in Hr as [Hr T12].
        apply orb_false_iff in Hr as [Hr T11]. apply orb_false_iff in Hr as [T5 T10].
        rewrite DK by (unfold f_clob3; rewrite ?T1, ?T2, ?T5, ?T8, ?T9, ?T10, ?T11, ?T12, ?T13, ?T14, ?T15, ?T16, ?T17, ?T18; reflexivity).
        rewrite CK by (unfold l_clob3; rewrite ?T5, ?T10, ?T12, ?T15, ?T17; reflexivity).
        rewrite BK by (unfold a_clob3; rewrite ?T9, ?T10, ?T11, ?T12, ?T13, ?T14, ?T15, ?T16, ?T18; reflexivity).
        apply AK. unfold t_keep3, tls_clob. rewrite T10, T11, T12, T13, T1, T2, T8. reflexivity. }
      destruct FR as (FRa & FRb & FRc). split; [|split].
      - intros x Hx. apply WR_agree3. apply FRa. exact Hx.
      - intros x Hx. apply WR_keep3. apply FRb. exact Hx.
      - intros x Hx. apply WR_sok3. apply FRc. exact Hx.
    Qed.
  End C3.
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Section C4.
    Definition N4 : Z := 1024.
    Definition FL4 : Z := 34816.
    Definition FR4 : Z := 4231168.
    Variable hint : word.                (* [comment removed for export] *)
    Variable FL : Z -> byte.             (* [comment removed for export] *)
    Variable p0 : Z.                     (* [comment removed for export] *)
    Hypothesis Hhint : rdn SEGS mem (Z_to_bv 64 (fs + 32)) 8 = Some (word_to_le_bytes 8 hint).
    Hypothesis Hflags : forall p, (0 <= p < N4)%Z -> rdn SEGS mem (Z_to_bv 64 (fs + FL4 + p)) 1 = Some [FL p].
    Hypothesis Hp0 : (0 <= p0 < N4)%Z /\ bv_unsigned (FL p0) = 0%Z.
    Hypothesis Whint : forall j, (32 <= j < 40)%Z -> store_ok SEGS mem (Z_to_bv 64 (fs + j)) 1 = true.
    Hypothesis Wflag : forall p, (0 <= p < N4)%Z -> store_ok SEGS mem (Z_to_bv 64 (fs + FL4 + p)) 1 = true.
    Hypothesis Wframe : forall p j, (0 <= p < N4)%Z -> (0 <= j < 1024)%Z -> store_ok SEGS mem (Z_to_bv 64 (fs + FR4 + 1024 * p + j)) 1 = true.
    Hypothesis Wshad : forall p j, (0 <= p < N4)%Z -> (0 <= j < 128)%Z -> store_ok SEGS mem (Z_to_bv 64 (SB + (fs + FR4 + 1024 * p) / 8 + j)) 1 = true.

    Let h : Z := bv_unsigned hint.
    Definition pos4 (i : Z) : Z := ((h + i) mod N4)%Z.
    Definition ff4 (p : Z) : Z := (fs + FR4 + 1024 * p)%Z.

    #[using="Type"] Lemma lit_5bfcc4 : v_addi (0x3f364 : word) 4 = Z_to_bv 64 0x3f368. Proof. apply bv_eq; vm_compute; reflexivity. Qed.
    #[using="Type"] Lemma ret_ok_5bfcc4 : ret_ok (Z_to_bv 64 0x3f368). Proof. apply ret_ok_even. vm_compute. reflexivity. Qed.
    #[using="Type"] Lemma lit_5c0d84 : v_addi (0x3f48c : word) 4 = Z_to_bv 64 0x3f490. Proof. apply bv_eq; vm_compute; reflexivity. Qed.
    #[using="Type"] Lemma ret_ok_5c0d84 : ret_ok (Z_to_bv 64 0x3f490). Proof. apply ret_ok_even. vm_compute. reflexivity. Qed.

    Ltac wz4 T V := progress (replace T with (Z_to_bv 64 V) by (apply bv_eq; vm_compute; reflexivity)).
    Ltac msd14 F D a v Hbase SOK :=
      mstep ltac:(eapply (step_sd_at _ _ _ _ _ _ _ _ _ (Z_to_bv 64 a) v F eq_refl D);
                   [ gr; rewrite ?Hbase; imm_norm; rewrite ?v_addi_any; apply (f_equal (Z_to_bv 64)); lia
                   | gr; first [reflexivity | assumption | symmetry; assumption]
                   | SOK ]).
    Ltac stk84 := pose proof HU; apply store_ok8_bytes; [lia|lia|];
                 intros j Hj; repeat apply store_ok1_wbytes; apply (s_stk _ _ _ _ _ _ _ _ _ H); unfold SM_FRAME; lia.

    (* [comment removed for export] *)
    Definition t_keep4 (r : reg) : bool := negb (tls_clob r || bv_eqb r 1 || bv_eqb r 2 || bv_eqb r 8 || bv_eqb r 10)%bool.

    #[using="fs ctx thr db beg a2v a3v H H01 H02 H04 hint h"] Lemma blk_PT4 :
      exists regs m,
        msteps SEGS (mkst regs0 (0x3f344 : word) mem rom) (mkst regs (0x3f368 : word) m rom)
        /\ getr regs 2 = Z_to_bv 64 (usp - 32) /\ getr regs 8 = Z_to_bv 64 usp /\ getr regs 10 = Z_to_bv 64 TP
        /\ getr regs 4 = Z_to_bv 64 TP
        /\ (forall r, t_keep4 r = true -> getr regs r = getr regs0 r)
        /\ sfr m
        /\ (forall x : word, (usp - 32 <= bv_unsigned x)%Z -> m x = m1 x).
    Proof.
      pose proof HU as U.
      (* [comment removed for export] *)
      assert (P : exists q, msteps SEGS (mkst regs0 (0x3f344 : word) mem rom) (mkst q (0x4428c : word) m1 rom)
                /\ getr q 2 = Z_to_bv 64 (usp - 32) /\ getr q 8 = Z_to_bv 64 usp /\ getr q 10 = Z_to_bv 64 A_DESC
                /\ getr q 1 = Z_to_bv 64 0x3f368 /\ getr q 4 = Z_to_bv 64 TP
                /\ (forall r : reg, r <> 1 -> r <> 2 -> r <> 8 -> r <> 10 -> getr q r = getr regs0 r)).
      { eexists. split.
        - mstep ltac:(exact (step_addi _ _ _ _ _ _ _ _ _ F_3f344 eq_refl D_3f344)). rewrite H02. zn.
          msd14 F_3f348 D_3f348 (usp - 8)%Z ra H02 ltac:(stk84).
          msd14 F_3f34c D_3f34c (usp - 16)%Z (getr regs0 8) H02 ltac:(stk84).
          msd14 F_3f350 D_3f350 (usp - 24)%Z (getr regs0 9) H02 ltac:(stk84).
          msd14 F_3f354 D_3f354 (usp - 32)%Z (getr regs0 18) H02 ltac:(stk84).
          change (wbytes _ _ _) with m1.
          mstep ltac:(exact (step_addi _ _ _ _ _ _ _ _ _ F_3f358 eq_refl D_3f358)). gr. zn.
          mstep ltac:(eapply (step_auipc_at _ _ _ _ _ _ _ _ (Z_to_bv 64 0xac35c) F_3f35c eq_refl D_3f35c);
                       [reflexivity | apply bv_eq; vm_compute; reflexivity]).
          mstep ltac:(exact (step_addi _ _ _ _ _ _ _ _ _ F_3f360 eq_refl D_3f360)). gr. zn.
          mstep ltac:(eapply (step_jal_link _ _ _ _ _ _ _ _ F_3f364 eq_refl D_3f364)). rewrite lit_5bfcc4.
          apply mst_refl.
        - gr. repeat split; try (apply (f_equal (Z_to_bv 64)); lia); try reflexivity; try assumption.
          intros r X1 X2 X8 X10. repeat (rewrite getr_other by congruence). reflexivity. }
      destruct P as (q & MP & Q2 & Q8 & Q10 & Q1 & Q4 & QK).
      destruct (tls_run m1 rom (usp - 32) ctx thr db beg a2v a3v tls_m1 q (Z_to_bv 64 0x3f368) ret_ok_5bfcc4 Q1 Q2 Q4 Q10)
        as (q2 & m2 & MT & T10 & T2 & T1 & TK & TM1 & TM2 & TM3).
      exists q2, m2. split.
      { eapply msteps_trans; [exact MP|]. replace (Z_to_bv 64 0x3f368) with (0x3f368 : word) in MT by (apply bv_eq; reflexivity). exact MT. }
      split; [exact T2|]. split; [rewrite TK by reflexivity; exact Q8|]. split; [exact T10|].
      split; [rewrite TK by reflexivity; exact Q4|]. split.
      { intros r Hr. unfold t_keep4 in Hr. apply negb_true_iff in Hr.
        apply orb_false_iff in Hr as [Hr K10]. apply orb_false_iff in Hr as [Hr K8].
        apply orb_false_iff in Hr as [Hr K2]. apply orb_false_iff in Hr as [Hr K1].
        rewrite TK by exact Hr. apply QK; intros ->; discriminate. }
      split.
      { destruct m1_sfr as (F1 & F2 & F3). unfold TLS_FRAME in TM1. split; [|split].
        - intros x Hx. rewrite TM1 by (unfold SM_FRAME in Hx; lia). apply F1. exact Hx.
        - intros x Hx. apply TM2. apply F2. exact Hx.
        - intros x Hx. apply TM3. apply F3. exact Hx. }
      intros x Hx. apply TM1. lia.
    Qed.

    (* [comment removed for export] *)
    Definition a_clob4 (r : reg) : bool :=
      (bv_eqb r 9 || bv_eqb r 10 || bv_eqb r 11 || bv_eqb r 12 || bv_eqb r 13 || bv_eqb r 14 || bv_eqb r 15 || bv_eqb r 16 || bv_eqb r 18)%bool.

    #[using="ctx thr db beg a2v a3v H Hhint"] Lemma blk_A4 : forall regs m,
      sfr m -> getr regs 10 = Z_to_bv 64 TP ->
      exists regs',
        msteps SEGS (mkst regs (0x3f368 : word) m rom) (mkst regs' (0x3f3d8 : word) m rom)
        /\ getr regs' 9 = Z_to_bv 64 fs /\ getr regs' 18 = Z_to_bv 64 20
        /\ getr regs' 10 = Z_to_bv 64 (N4 - 0) /\ getr regs' 12 = Z_to_bv 64 (h + 0)
        /\ getr regs' 13 = Z_to_bv 64 (fs + FL4) /\ getr regs' 14 = Z_to_bv 64 (N4 - 1)
        /\ getr regs' 11 = Z_to_bv 64 (fs + 4096)
        /\ (forall r, a_clob4 r = false -> getr regs' r = getr regs r).
    Proof.
      intros regs m FR H10. pose proof HU as U. pose proof HF as (F1 & F2 & F3 & F4). unfold FS_AREA, TP in *.
      pose proof (s_fs _ _ _ _ _ _ _ _ _ H) as Cfs. pose proof (s_gc _ _ _ _ _ _ _ _ _ H) as Cgc. pose proof (s_ssl _ _ _ _ _ _ _ _ _ H) as Cssl.
      pose proof Hhint as Ch. unfold cell, TP in Cfs, Cgc, Cssl, Ch.
      rewrite <- (rdn_sfr m) in Cfs by (first [exact FR | cbn; unfold SM_FRAME; lia]).
      rewrite <- (rdn_sfr m) in Cgc by (first [exact FR | cbn; unfold SM_FRAME; lia]).
      rewrite <- (rdn_sfr m) in Cssl by (first [exact FR | cbn; unfold SM_FRAME; lia]).
      rewrite <- (rdn_sfr m) in Ch by (first [exact FR | cbn; unfold SM_FRAME; lia]).
      eexists. split.
      - mld F_3f368 D_3f368 fs Cfs H10.
        mstep ltac:(eapply (step_beq_ft _ _ _ _ _ _ _ _ _ F_3f36c eq_refl D_3f36c); gr; rewrite getr_zero; br_eq).
        mstep ltac:(eapply (@step_lbu _ _ _ _ _ _ _ _ _ _ (Z_to_bv 8 0) F_3f370 eq_refl D_3f370); gr; imm_norm; zn; exact Cgc).
        change (bv_unsigned (Z_to_bv 8 0)) with 0%Z.
        mld F_3f374 D_3f374 20%Z Cssl H10.
        mstep ltac:(eapply (step_beq_tk _ _ _ _ _ _ _ _ _ F_3f378 eq_refl D_3f378); gr; rewrite getr_zero; br_eq).
        mstep ltac:(exact (step_addi _ _ _ _ _ _ _ _ _ F_3f388 eq_refl D_3f388)). gr. zn.
        mstep ltac:(exact (step_addi _ _ _ _ _ _ _ _ _ F_3f38c eq_refl D_3f38c)). rewrite getr_zero. zn.
        mstep ltac:(exact (step_sll _ _ _ _ _ _ _ _ _ F_3f390 eq_refl D_3f390)). gr.
        wz4 (v_sll (Z_to_bv 64 1) (Z_to_bv 64 (20 + -10))) 1024%Z.
        mstep ltac:(exact (step_addiw _ _ _ _ _ _ _ _ _ F_3f394 eq_refl D_3f394)). gr. imm_norm.
        wz4 (v_addiw (Z_to_bv 64 1024) 0) 1024%Z.
        mstep ltac:(eapply (step_bge_ft _ _ _ _ _ _ _ _ _ F_3f398 eq_refl D_3f398); gr; rewrite getr_zero; apply c_lts_pos_ft; lia).
        mstep ltac:(eapply (step_lui_at _ _ _ _ _ _ _ _ (Z_to_bv 64 4096) F_3f39c eq_refl D_3f39c); reflexivity).
        mstep ltac:(exact (step_addi _ _ _ _ _ _ _ _ _ F_3f3a0 eq_refl D_3f3a0)). gr. zn.
        mstep ltac:(exact (step_addi _ _ _ _ _ _ _ _ _ F_3f3a4 eq_refl D_3f3a4)). rewrite getr_zero. zn.
        mstep ltac:(exact (step_addi _ _ _ _ _ _ _ _ _ F_3f3a8 eq_refl D_3f3a8)). rewrite getr_zero, k_m1_val.
        mstep ltac:(exact (step_sll _ _ _ _ _ _ _ _ _ F_3f3ac eq_refl D_3f3ac)). gr.
        wz4 (v_sll (Z_to_bv 64 960) (Z_to_bv 64 (20 + -15))) 30720%Z.
        mstep ltac:(eapply (@step_ld _ _ _ _ _ _ _ _ _ _ _ hint F_3f3b0 eq_refl D_3f3b0);
                     [ gr; imm_norm; zn; exact Ch | apply bytes_le_to_Z_8 ]).
        rewrite (zbv_self' hint). fold h.
        mstep ltac:(exact (step_sll _ _ _ _ _ _ _ _ _ F_3f3b4 eq_refl D_3f3b4)). gr.
        wz4 (v_sll (Z_to_bv 64 (2 ^ 64 - 1)) (Z_to_bv 64 (20 + -10))) (2 ^ 64 - 1024)%Z.
        mstep ltac:(exact (step_addi _ _ _ _ _ _ _ _ _ F_3f3b8 eq_refl D_3f3b8)). gr. zn.
        mstep ltac:(exact (step_add _ _ _ _ _ _ _ _ _ F_3f3bc eq_refl D_3f3bc)). gr. rewrite v_add_zbv by lia.
        mstep ltac:(exact (step_add _ _ _ _ _ _ _ _ _ F_3f3c0 eq_refl D_3f3c0)). gr. rewrite v_add_zbv by lia.
        mstep ltac:(exact (step_xori _ _ _ _ _ _ _ _ _ F_3f3c4 eq_refl D_3f3c4)). gr. imm_norm.
        wz4 (v_xori (Z_to_bv 64 (2 ^ 64 - 1024)) (-1)) 1023%Z.
        mstep ltac:(exact (step_slli _ _ _ _ _ _ _ _ _ F_3f3c8 eq_refl D_3f3c8)). gr. imm_norm.
        wz4 (v_slli (Z_to_bv 64 (1024 + -1)) 32) (1023 * 2 ^ 32)%Z.
        mstep ltac:(exact (PropExec.step_srli _ _ _ _ _ _ _ _ _ F_3f3cc eq_refl D_3f3cc)). gr. imm_norm.
        wz4 (v_srli (Z_to_bv 64 (1023 * 2 ^ 32)) 32) 1023%Z.
        mstep ltac:(exact (step_add _ _ _ _ _ _ _ _ _ F_3f3d0 eq_refl D_3f3d0)). gr. rewrite v_add_any.
        mstep ltac:(exact (step_addi _ _ _ _ _ _ _ _ _ F_3f3d4 eq_refl D_3f3d4)). gr. rewrite v_addi_any.
        apply mst_refl.
      - gr. unfold N4, FL4. repeat split; try (apply (f_equal (Z_to_bv 64)); lia); try reflexivity.
        intros r Hr. unfold a_clob4 in Hr.
        repeat (rewrite getr_other by (intros ->; cbn in Hr; discriminate)). reflexivity.
    Qed.

    (* [comment removed for export] *)
    Let i0 : Z := ((p0 - h) mod N4)%Z.
    #[using="Type"] Lemma i0_rng4 : (0 <= i0 < N4)%Z. Proof. unfold i0, N4. apply Z.mod_pos_bound. lia. Qed.
    #[using="FL Hp0"] Lemma pos_i04 : pos4 i0 = p0.
    Proof.
      unfold pos4, i0, N4. rewrite Zplus_mod_idemp_r. replace (h + (p0 - h))%Z with p0 by lia.
      apply Z.mod_small. unfold N4 in Hp0. lia.
    Qed.
    #[using="p0 i0"] Lemma pos_rng4 : forall i, (0 <= pos4 i < N4)%Z. Proof. intros i. unfold pos4, N4. apply Z.mod_pos_bound. lia. Qed.

    Definition l_clob4 (r : reg) : bool := (bv_eqb r 5 || bv_eqb r 10 || bv_eqb r 12 || bv_eqb r 15 || bv_eqb r 17)%bool.

    #[using="ctx thr db beg a2v a3v H Hflags Hp0"] Lemma blk_L4 : forall (k : nat) i regs m,
      (i + Z.of_nat k = i0)%Z -> (0 <= i)%Z -> sfr m ->
      getr regs 10 = Z_to_bv 64 (N4 - i) -> getr regs 12 = Z_to_bv 64 (h + i) ->
      getr regs 13 = Z_to_bv 64 (fs + FL4) -> getr regs 14 = Z_to_bv 64 (N4 - 1) ->
      exists i' regs',
        (i <= i' <= i0)%Z /\ bv_unsigned (FL (pos4 i')) = 0%Z
        /\ msteps SEGS (mkst regs (0x3f3d8 : word) m rom) (mkst regs' (0x3f450 : word) m rom)
        /\ getr regs' 12 = Z_to_bv 64 (h + i') /\ getr regs' 17 = Z_to_bv 64 (pos4 i')
        /\ getr regs' 15 = Z_to_bv 64 (fs + FL4 + pos4 i')
        /\ (forall r, l_clob4 r = false -> getr regs' r = getr regs r).
    Proof.
      pose proof HU as U. pose proof HF as (F1 & F2 & F3 & F4). unfold FS_AREA in *. pose proof i0_rng4 as I0. pose proof Hp0 as [P0 P1].
      unfold N4 in *.
      unfold FL4 in *.
      induction k as [|k IH]; intros i regs m Hk Hi FR H10 H12 H13 H14.
      - (* [comment removed for export] *)
        cbn [Z.of_nat] in Hk. rewrite Z.add_0_r in Hk. subst i.
        pose proof (pos_rng4 i0) as PR. unfold N4 in PR.
        pose proof (Hflags (pos4 i0) PR) as CF. rewrite <- (rdn_sfr m) in CF by (first [exact FR | cbn; unfold SM_FRAME, FL4; lia]).
        exists i0. eexists. split; [lia|]. split; [rewrite pos_i04; exact P1|]. split.
        + mstep ltac:(exact (step_and _ _ _ _ _ _ _ _ _ F_3f3d8 eq_refl D_3f3d8)). gr. rewrite H12, H14.
          change (1024 - 1)%Z with (2 ^ 10 - 1)%Z. rewrite v_and_mask by lia. change (2 ^ 10)%Z with 1024%Z. fold N4. fold (pos4 i0).
          mstep ltac:(exact (step_add _ _ _ _ _ _ _ _ _ F_3f3dc eq_refl D_3f3dc)). gr. rewrite H13. unfold FL4. rewrite v_add_zbv by lia.
          mstep ltac:(eapply (@step_lbu _ _ _ _ _ _ _ _ _ _ (FL (pos4 i0)) F_3f3e0 eq_refl D_3f3e0); gr; imm_norm; zn; rewrite ?Z.add_0_r; unfold FL4 in CF; exact CF).
          replace (bv_unsigned (FL (pos4 i0))) with 0%Z by (rewrite pos_i04, P1; reflexivity).
          mstep ltac:(eapply (step_beq_tk _ _ _ _ _ _ _ _ _ F_3f3e4 eq_refl D_3f3e4); gr; rewrite getr_zero; br_eq).
          apply mst_refl.
        + gr. unfold FL4. repeat split; try (apply (f_equal (Z_to_bv 64)); lia); try reflexivity; try assumption.
          intros r Hr. unfold l_clob4 in Hr.
          repeat (rewrite getr_other by (intros ->; cbn in Hr; discriminate)). reflexivity.
      - (* [comment removed for export] *)
        pose proof (pos_rng4 i) as PR. unfold N4 in PR.
        pose proof (Hflags (pos4 i) PR) as CF. rewrite <- (rdn_sfr m) in CF by (first [exact FR | cbn; unfold SM_FRAME, FL4; lia]).
        pose proof (bv_unsigned_in_range 8 (FL (pos4 i))) as BR. change (bv_modulus 8) with 256%Z in BR.
        destruct (Z.eq_dec (bv_unsigned (FL (pos4 i))) 0) as [Z0|NZ].
        + exists i. eexists. split; [lia|]. split; [exact Z0|]. split.
          * mstep ltac:(exact (step_and _ _ _ _ _ _ _ _ _ F_3f3d8 eq_refl D_3f3d8)). gr. rewrite H12, H14.
            change (1024 - 1)%Z with (2 ^ 10 - 1)%Z. rewrite v_and_mask by lia. change (2 ^ 10)%Z with 1024%Z. fold N4. fold (pos4 i).
            mstep ltac:(exact (step_add _ _ _ _ _ _ _ _ _ F_3f3dc eq_refl D_3f3dc)). gr. rewrite H13. unfold FL4. rewrite v_add_zbv by lia.
            mstep ltac:(eapply (@step_lbu _ _ _ _ _ _ _ _ _ _ (FL (pos4 i)) F_3f3e0 eq_refl D_3f3e0); gr; imm_norm; zn; rewrite ?Z.add_0_r; unfold FL4 in CF; exact CF).
            rewrite Z0.
            mstep ltac:(eapply (step_beq_tk _ _ _ _ _ _ _ _ _ F_3f3e4 eq_refl D_3f3e4); gr; rewrite getr_zero; br_eq).
            apply mst_refl.
          * gr. unfold FL4. repeat split; try (apply (f_equal (Z_to_bv 64)); lia); try reflexivity; try assumption.
            intros r Hr. unfold l_clob4 in Hr.
            repeat (rewrite getr_other by (intros ->; cbn in Hr; discriminate)). reflexivity.
        + assert (NI : i <> i0) by (intros ->; rewrite pos_i04 in NZ; exact (NZ P1)).
          edestruct (IH (i + 1)%Z
            (regupd (regupd (regupd (regupd (regupd regs 17 (Z_to_bv 64 (pos4 i))) 15 (Z_to_bv 64 (fs + FL4 + pos4 i)))
               5 (Z_to_bv 64 (bv_unsigned (FL (pos4 i))))) 10 (Z_to_bv 64 (1024 - i - 1))) 12 (Z_to_bv 64 (h + i + 1))) m)
            as (i' & regs' & R1 & R2 & M & Q12 & Q17 & Q15 & QK); try lia; try exact FR.
          1-4: gr; first [assumption | apply (f_equal (Z_to_bv 64)); lia].
          exists i', regs'. split; [lia|]. split; [exact R2|]. split.
          * mstep ltac:(exact (step_and _ _ _ _ _ _ _ _ _ F_3f3d8 eq_refl D_3f3d8)). gr. rewrite H12, H14.
            change (1024 - 1)%Z with (2 ^ 10 - 1)%Z. rewrite v_and_mask by lia. change (2 ^ 10)%Z with 1024%Z. fold N4. fold (pos4 i).
            mstep ltac:(exact (step_add _ _ _ _ _ _ _ _ _ F_3f3dc eq_refl D_3f3dc)). gr. rewrite H13. rewrite v_add_zbv by (unfold FL4; lia).
            mstep ltac:(eapply (@step_lbu _ _ _ _ _ _ _ _ _ _ (FL (pos4 i)) F_3f3e0 eq_refl D_3f3e0); gr; imm_norm; zn; rewrite ?Z.add_0_r; exact CF).
            mstep ltac:(eapply (step_beq_ft _ _ _ _ _ _ _ _ _ F_3f3e4 eq_refl D_3f3e4); gr; rewrite getr_zero; br_eq).
            mstep ltac:(exact (step_addiw _ _ _ _ _ _ _ _ _ F_3f3e8 eq_refl D_3f3e8)). gr. rewrite H10. imm_norm.
            rewrite v_addiw_small by lia.
            mstep ltac:(exact (step_addi _ _ _ _ _ _ _ _ _ F_3f3ec eq_refl D_3f3ec)). gr. rewrite H12, v_addi_any.
            mstep ltac:(eapply (step_bne_tk _ _ _ _ _ _ _ _ _ F_3f3f0 eq_refl D_3f3f0); gr; rewrite getr_zero; br_eq).
            replace (1024 - i + -1)%Z with (1024 - i - 1)%Z by lia. exact M.
          * split; [exact Q12|]. split; [exact Q17|]. split; [exact Q15|].
            intros r Hr. rewrite (QK r Hr). unfold l_clob4 in Hr.
            repeat (rewrite getr_other by (intros ->; cbn in Hr; discriminate)). reflexivity.
    Qed.

    (* [comment removed for export] *)
    (* [comment removed for export] *)
    Definition WR4 (m : word -> option byte) (i p : Z) : word -> option byte :=
      wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes m
        (Z_to_bv 64 (fs + 32)) (word_to_le_bytes 8 (Z_to_bv 64 (h + i + 1))))
        (Z_to_bv 64 (fs + FL4 + p)) (word_to_le_bytes 1 (Z_to_bv 64 1)))
        (Z_to_bv 64 (ff4 p + 24)) (word_to_le_bytes 8 (Z_to_bv 64 usp)))
        (Z_to_bv 64 (ff4 p + 1016)) (word_to_le_bytes 8 (Z_to_bv 64 (fs + FL4 + p))))
        (Z_to_bv 64 (SB + ff4 p / 8)) (word_to_le_bytes 8 (Z_to_bv 64 0)))
        (Z_to_bv 64 (SB + ff4 p / 8 + 8)) (word_to_le_bytes 8 (Z_to_bv 64 0)))
        (Z_to_bv 64 (SB + ff4 p / 8 + 16)) (word_to_le_bytes 8 (Z_to_bv 64 0)))
        (Z_to_bv 64 (SB + ff4 p / 8 + 24)) (word_to_le_bytes 8 (Z_to_bv 64 0)))
        (Z_to_bv 64 (SB + ff4 p / 8 + 32)) (word_to_le_bytes 8 (Z_to_bv 64 0)))
        (Z_to_bv 64 (SB + ff4 p / 8 + 40)) (word_to_le_bytes 8 (Z_to_bv 64 0)))
        (Z_to_bv 64 (SB + ff4 p / 8 + 48)) (word_to_le_bytes 8 (Z_to_bv 64 0)))
        (Z_to_bv 64 (SB + ff4 p / 8 + 56)) (word_to_le_bytes 8 (Z_to_bv 64 0)))
        (Z_to_bv 64 (SB + ff4 p / 8 + 64)) (word_to_le_bytes 8 (Z_to_bv 64 0)))
        (Z_to_bv 64 (SB + ff4 p / 8 + 72)) (word_to_le_bytes 8 (Z_to_bv 64 0)))
        (Z_to_bv 64 (SB + ff4 p / 8 + 80)) (word_to_le_bytes 8 (Z_to_bv 64 0)))
        (Z_to_bv 64 (SB + ff4 p / 8 + 88)) (word_to_le_bytes 8 (Z_to_bv 64 0)))
        (Z_to_bv 64 (SB + ff4 p / 8 + 96)) (word_to_le_bytes 8 (Z_to_bv 64 0)))
        (Z_to_bv 64 (SB + ff4 p / 8 + 104)) (word_to_le_bytes 8 (Z_to_bv 64 0)))
        (Z_to_bv 64 (SB + ff4 p / 8 + 112)) (word_to_le_bytes 8 (Z_to_bv 64 0)))
        (Z_to_bv 64 (SB + ff4 p / 8 + 120)) (word_to_le_bytes 8 (Z_to_bv 64 0)).

    #[using="Type"] Lemma WR_agree4 : forall ma mb i p (x : word), ma x = mb x -> WR4 ma i p x = WR4 mb i p x.
    Proof. intros. unfold WR4. repeat apply wbytes_agree. assumption. Qed.
    #[using="Type"] Lemma WR_keep4 : forall m i p (x : word), m x <> None -> WR4 m i p x <> None.
    Proof. intros. unfold WR4. repeat apply wbytes_keep. assumption. Qed.
    #[using="Type"] Lemma WR_sok4 : forall m i p (x : word), store_ok SEGS m x 1 = true -> store_ok SEGS (WR4 m i p) x 1 = true.
    Proof. intros. unfold WR4. repeat apply store_ok1_wbytes. assumption. Qed.

    #[using="mem rom ctx thr db beg a2v a3v H p0 i0"] Lemma WR_stack4 : forall m i p a, (0 <= p < N4)%Z -> (usp - 32 <= a)%Z -> (a + 8 <= usp)%Z ->
      rdn SEGS (WR4 m i p) (Z_to_bv 64 a) 8 = rdn SEGS m (Z_to_bv 64 a) 8.
    Proof.
      intros m i p a Hp Ha Hb. pose proof HU as U. pose proof HF as (F1 & F2 & F3 & F4). unfold FS_AREA, N4, ff4, FR4, FL4 in *.
      pose proof SB_val.
      assert (ff_hi : (fs + 4231168 + 1024 * p + 1024 <= 2 ^ 47)%Z) by lia.
      pose proof (Z.div_pos (fs + 4231168 + 1024 * p) 8 ltac:(lia) ltac:(lia)).
      pose proof (Z.div_lt_upper_bound (fs + 4231168 + 1024 * p) 8 (2 ^ 44) ltac:(lia) ltac:(lia)).
      unfold WR4, ff4, FL4, FR4. rewrite !rdn_wbytes_out; try reflexivity; len8; rewrite ?zbv_u by (ltac2:(LK.k [@Hp; @Ha; @Hb; @U; @F1; @F2; @ff_hi; @H0; @H1; @H2; @F4]); lia); (ltac2:(LK.k [@Hp; @Ha; @Hb; @U; @F1; @F2; @ff_hi; @H0; @H1; @H2; @F4]); lia).
    Qed.

    Definition f_clob4 (r : reg) : bool :=
      (bv_eqb r 1 || bv_eqb r 2 || bv_eqb r 5 || bv_eqb r 8 || bv_eqb r 9 || bv_eqb r 10 || bv_eqb r 11 || bv_eqb r 12
       || bv_eqb r 13 || bv_eqb r 14 || bv_eqb r 15 || bv_eqb r 16 || bv_eqb r 17 || bv_eqb r 18)%bool.

    #[using="ctx thr db beg a2v a3v H Hret p0 Whint Wflag Wframe Wshad i0"] Lemma blk_F4 : forall regs m i p,
      sfr m -> (forall x : word, (usp - 32 <= bv_unsigned x)%Z -> m x = m1 x) ->
      (0 <= p < N4)%Z -> (0 <= i < N4)%Z ->
      getr regs 2 = Z_to_bv 64 (usp - 32) -> getr regs 8 = Z_to_bv 64 usp -> getr regs 9 = Z_to_bv 64 fs ->
      getr regs 18 = Z_to_bv 64 20 -> getr regs 11 = Z_to_bv 64 (fs + 4096) ->
      getr regs 12 = Z_to_bv 64 (h + i) -> getr regs 17 = Z_to_bv 64 p -> getr regs 15 = Z_to_bv 64 (fs + FL4 + p) ->
      exists regs',
        msteps SEGS (mkst regs (0x3f450 : word) m rom) (mkst regs' ra (WR4 m i p) rom)
        /\ getr regs' 10 = Z_to_bv 64 (ff4 p) /\ getr regs' 2 = Z_to_bv 64 usp /\ getr regs' 1 = ra
        /\ getr regs' 8 = getr regs0 8 /\ getr regs' 9 = getr regs0 9 /\ getr regs' 18 = getr regs0 18
        /\ (forall r, f_clob4 r = false -> getr regs' r = getr regs r).
    Proof.
      intros regs m i p FR AG Hp Hi H2 H8 H9 H18 H11 H12 H17 H15.
      pose proof HU as U. pose proof HF as (F1 & F2 & F3 & F4). pose proof SB_val as HSB. unfold FS_AREA, N4, FL4 in *.
      destruct FR as (FRa & FRb & FRc).
      assert (ff_lo : (0x608000 <= ff4 p)%Z) by (unfold ff4, FR4; lia).
      assert (ff_hi : (ff4 p + 1024 <= 2 ^ 47)%Z) by (unfold ff4, FR4; lia).
      pose proof (Z.div_pos (ff4 p) 8 ltac:(lia) ltac:(lia)) as D1.
      pose proof (Z.div_lt_upper_bound (ff4 p) 8 (2 ^ 44) ltac:(lia) ltac:(lia)) as D2.
      (* [comment removed for export] *)
      assert (RD : forall a v, (usp - 32 <= a)%Z -> (a + 8 <= usp)%Z ->
                rdn SEGS m1 (Z_to_bv 64 a) 8 = Some (word_to_le_bytes 8 v) ->
                rdn SEGS (WR4 m i p) (Z_to_bv 64 a) 8 = Some (word_to_le_bytes 8 v)).
      { intros a v Ha Hb R. rewrite WR_stack4 by (unfold N4; lia). rewrite <- R. apply rdn_ext; [rewrite zbv_u by lia; cbn; lia|].
        intros x Hx. rewrite zbv_u in Hx by lia. apply AG. lia. }
      pose proof (RD (usp - 8)%Z _ ltac:(lia) ltac:(lia) rd1_8) as R8. pose proof (RD (usp - 16)%Z _ ltac:(lia) ltac:(lia) rd1_16) as R16.
      pose proof (RD (usp - 24)%Z _ ltac:(lia) ltac:(lia) rd1_24) as R24. pose proof (RD (usp - 32)%Z _ ltac:(lia) ltac:(lia) rd1_32) as R32.
      (* [comment removed for export] *)
      set (m4 := wbytes (wbytes (wbytes (wbytes m
        (Z_to_bv 64 (fs + 32)) (word_to_le_bytes 8 (Z_to_bv 64 (h + i + 1))))
        (Z_to_bv 64 (fs + 34816 + p)) (word_to_le_bytes 1 (Z_to_bv 64 1)))
        (Z_to_bv 64 (ff4 p + 24)) (word_to_le_bytes 8 (Z_to_bv 64 usp)))
        (Z_to_bv 64 (ff4 p + 1016)) (word_to_le_bytes 8 (Z_to_bv 64 (fs + 34816 + p)))).
      assert (C4 : cells m4).
      { pose proof (s_cells _ _ _ _ _ _ _ _ _ H) as C. unfold cells, cell in *. unfold m4.
        rewrite !rdn_wbytes_out; len8; rewrite ?zbv_u by (ltac2:(LK.k [@F1; @F2; @Hp; @U; @ff_lo; @ff_hi]); lia); try (cbn; unfold ff4, FR4 in *; (ltac2:(LK.k [@F1; @F2; @Hp; @U; @ff_lo; @ff_hi]); lia)).
        rewrite !(rdn_sfr m) by (first [split; [exact FRa|split; [exact FRb|exact FRc]] | cbn; unfold SM_FRAME; lia]). exact C. }
      (* [comment removed for export] *)
      assert (P1 : exists r1,
        msteps SEGS (mkst regs (0x3f450 : word) m rom) (mkst r1 (0x3f510 : word) m4 rom)
        /\ getr r1 10 = Z_to_bv 64 (ff4 p) /\ getr r1 1 = Z_to_bv 64 0x3f490 /\ getr r1 2 = Z_to_bv 64 (usp - 32)
        /\ getr r1 9 = Z_to_bv 64 (ff4 p)
        /\ (forall r : reg, r <> 1 -> r <> 9 -> r <> 10 -> r <> 12 -> r <> 13 -> r <> 17 -> getr r1 r = getr regs r)).
      { eexists. split.
        - mstep ltac:(exact (step_addi _ _ _ _ _ _ _ _ _ F_3f450 eq_refl D_3f450)). gr. rewrite H12, v_addi_any.
          mstep ltac:(exact (step_addi _ _ _ _ _ _ _ _ _ F_3f454 eq_refl D_3f454)). rewrite getr_zero. zn.
          mstep ltac:(exact (step_addi _ _ _ _ _ _ _ _ _ F_3f458 eq_refl D_3f458)). gr. rewrite H18. zn.
          msd14 F_3f45c D_3f45c (fs + 32)%Z (Z_to_bv 64 (h + i + 1)) H9
               ltac:(apply store_ok8_bytes; [lia|lia|]; intros j Hj; apply FRc; replace (fs + 32 + j)%Z with (fs + (32 + j))%Z by lia; apply Whint; lia).
          mstep ltac:(eapply (step_sb _ _ _ _ _ _ _ _ _ F_3f460 eq_refl D_3f460);
                       gr; rewrite H15; imm_norm; zn; rewrite ?Z.add_0_r; apply store_ok1_wbytes; apply FRc; apply Wflag; lia).
          gr. rewrite H15. zn. rewrite ?Z.add_0_r.
          mstep ltac:(exact (step_sll _ _ _ _ _ _ _ _ _ F_3f464 eq_refl D_3f464)). gr.
          wz4 (v_sll (Z_to_bv 64 1) (Z_to_bv 64 (20 + -5))) 32768%Z.
          mstep ltac:(exact (step_addi _ _ _ _ _ _ _ _ _ F_3f468 eq_refl D_3f468)). rewrite getr_zero. zn.
          mstep ltac:(exact (step_slli _ _ _ _ _ _ _ _ _ F_3f46c eq_refl D_3f46c)). gr. rewrite H17. imm_norm.
          rewrite (v_slli_zbv p 10) by lia.
          mstep ltac:(exact (step_sll _ _ _ _ _ _ _ _ _ F_3f470 eq_refl D_3f470)). gr. rewrite H18.
          wz4 (v_sll (Z_to_bv 64 4) (Z_to_bv 64 20)) (4 * 2 ^ 20)%Z.
          mstep ltac:(exact (step_add _ _ _ _ _ _ _ _ _ F_3f474 eq_refl D_3f474)). gr. rewrite H11, v_add_zbv by lia.
          mstep ltac:(exact (step_add _ _ _ _ _ _ _ _ _ F_3f478 eq_refl D_3f478)). gr. rewrite v_add_zbv by lia.
          mstep ltac:(exact (step_add _ _ _ _ _ _ _ _ _ F_3f47c eq_refl D_3f47c)). gr. rewrite v_add_zbv by lia.
          change (2 ^ 10)%Z with 1024%Z. replace (fs + 4096 + 32768 + (4 * 2 ^ 20 + p * 1024))%Z with (ff4 p) by (unfold ff4, FR4; lia).
          msd14 F_3f480 D_3f480 (ff4 p + 24)%Z (Z_to_bv 64 usp) H8
               ltac:(apply store_ok8_bytes; [lia|lia|]; intros j Hj; repeat apply store_ok1_wbytes; apply FRc;
                     unfold ff4, FR4; replace (fs + 4231168 + 1024 * p + 24 + j)%Z with (fs + 4231168 + 1024 * p + (24 + j))%Z by lia; apply Wframe; lia).
          msd14 F_3f484 D_3f484 (ff4 p + 1016)%Z (Z_to_bv 64 (fs + 34816 + p)) H8
               ltac:(apply store_ok8_bytes; [lia|lia|]; intros j Hj; repeat apply store_ok1_wbytes; apply FRc;
                     unfold ff4, FR4; replace (fs + 4231168 + 1024 * p + 1016 + j)%Z with (fs + 4231168 + 1024 * p + (1016 + j))%Z by lia; apply Wframe; lia).
          change (wbytes _ _ _) with m4.
          mstep ltac:(exact (step_addi _ _ _ _ _ _ _ _ _ F_3f488 eq_refl D_3f488)). gr. zn. rewrite ?Z.add_0_r.
          mstep ltac:(eapply (step_jal_link _ _ _ _ _ _ _ _ F_3f48c eq_refl D_3f48c)). rewrite lit_5c0d84.
          apply mst_refl.
        - gr. repeat split; try reflexivity; try assumption; try (apply (f_equal (Z_to_bv 64)); lia).
          intros r N1 N9 N10 N12 N13 N17. repeat (rewrite getr_other by congruence). reflexivity. }
      destruct P1 as (r1 & M1 & P10 & P1ra & P2 & P9 & PK).
      destruct (mem_to_shadow_5e918 rom r1 m4 (ff4 p) (Z_to_bv 64 0x3f490) C4 ltac:(lia)
                  ltac:(apply (in_mem_frame fs (ff4 p) 1024 HFB); [lia|unfold ff4, FR4; lia|unfold ff4, FR4 in *; unfold FS_AREA in *; lia|unfold FS_AREA in *; lia|lia])
                  P10 P1ra ret_ok_5c0d84)
        as (q & MQ & Q10 & QK).
      assert (Q2 : getr q 2 = Z_to_bv 64 (usp - 32)) by (rewrite QK by reflexivity; exact P2).
      assert (Q9 : getr q 9 = Z_to_bv 64 (ff4 p)) by (rewrite QK by reflexivity; exact P9).
      eexists. split.
      - eapply msteps_trans; [exact M1|]. eapply msteps_trans; [exact MQ|].
        replace (Z_to_bv 64 0x3f490) with (0x3f490 : word) by (apply bv_eq; reflexivity).
        mstep ltac:(exact (step_addi _ _ _ _ _ _ _ _ _ F_3f490 eq_refl D_3f490)). gr. rewrite Q10. zn. rewrite ?Z.add_0_r.
        mstep ltac:(exact (step_addi _ _ _ _ _ _ _ _ _ F_3f494 eq_refl D_3f494)). gr. rewrite Q9. zn. rewrite ?Z.add_0_r.
        mstep ltac:(exact (step_addi _ _ _ _ _ _ _ _ _ F_3f498 eq_refl D_3f498)). rewrite getr_zero. zn.
        msd14 F_3f49c D_3f49c (SB + ff4 p / 8)%Z (Z_to_bv 64 0) Q2
             ltac:(apply store_ok8_bytes; [lia|lia|]; intros j Hj; unfold m4; repeat apply store_ok1_wbytes; apply FRc;
                   unfold ff4, FR4; apply Wshad; lia).
        msd14 F_3f4a0 D_3f4a0 (SB + ff4 p / 8 + 8)%Z (Z_to_bv 64 0) Q2
             ltac:(apply store_ok8_bytes; [lia|lia|]; intros j Hj; unfold m4; repeat apply store_ok1_wbytes; apply FRc;
                   unfold ff4, FR4; replace (SB + (fs + 4231168 + 1024 * p) / 8 + 8 + j)%Z with (SB + (fs + 4231168 + 1024 * p) / 8 + (8 + j))%Z by lia;
                   apply Wshad; lia).
        msd14 F_3f4a4 D_3f4a4 (SB + ff4 p / 8 + 16)%Z (Z_to_bv 64 0) Q2
             ltac:(apply store_ok8_bytes; [lia|lia|]; intros j Hj; unfold m4; repeat apply store_ok1_wbytes; apply FRc;
                   unfold ff4, FR4; replace (SB + (fs + 4231168 + 1024 * p) / 8 + 16 + j)%Z with (SB + (fs + 4231168 + 1024 * p) / 8 + (16 + j))%Z by lia;
                   apply Wshad; lia).
        msd14 F_3f4a8 D_3f4a8 (SB + ff4 p / 8 + 24)%Z (Z_to_bv 64 0) Q2
             ltac:(apply store_ok8_bytes; [lia|lia|]; intros j Hj; unfold m4; repeat apply store_ok1_wbytes; apply FRc;
                   unfold ff4, FR4; replace (SB + (fs + 4231168 + 1024 * p) / 8 + 24 + j)%Z with (SB + (fs + 4231168 + 1024 * p) / 8 + (24 + j))%Z by lia;
                   apply Wshad; lia).
        msd14 F_3f4ac D_3f4ac (SB + ff4 p / 8 + 32)%Z (Z_to_bv 64 0) Q2
             ltac:(apply store_ok8_bytes; [lia|lia|]; intros j Hj; unfold m4; repeat apply store_ok1_wbytes; apply FRc;
                   unfold ff4, FR4; replace (SB + (fs + 4231168 + 1024 * p) / 8 + 32 + j)%Z with (SB + (fs + 4231168 + 1024 * p) / 8 + (32 + j))%Z by lia;
                   apply Wshad; lia).
        msd14 F_3f4b0 D_3f4b0 (SB + ff4 p / 8 + 40)%Z (Z_to_bv 64 0) Q2
             ltac:(apply store_ok8_bytes; [lia|lia|]; intros j Hj; unfold m4; repeat apply store_ok1_wbytes; apply FRc;
                   unfold ff4, FR4; replace (SB + (fs + 4231168 + 1024 * p) / 8 + 40 + j)%Z with (SB + (fs + 4231168 + 1024 * p) / 8 + (40 + j))%Z by lia;
                   apply Wshad; lia).
        msd14 F_3f4b4 D_3f4b4 (SB + ff4 p / 8 + 48)%Z (Z_to_bv 64 0) Q2
             ltac:(apply store_ok8_bytes; [lia|lia|]; intros j Hj; unfold m4; repeat apply store_ok1_wbytes; apply FRc;
                   unfold ff4, FR4; replace (SB + (fs + 4231168 + 1024 * p) / 8 + 48 + j)%Z with (SB + (fs + 4231168 + 1024 * p) / 8 + (48 + j))%Z by lia;
                   apply Wshad; lia).
        msd14 F_3f4b8 D_3f4b8 (SB + ff4 p / 8 + 56)%Z (Z_to_bv 64 0) Q2
             ltac:(apply store_ok8_bytes; [lia|lia|]; intros j Hj; unfold m4; repeat apply store_ok1_wbytes; apply FRc;
                   unfold ff4, FR4; replace (SB + (fs + 4231168 + 1024 * p) / 8 + 56 + j)%Z with (SB + (fs + 4231168 + 1024 * p) / 8 + (56 + j))%Z by lia;
                   apply Wshad; lia).
        msd14 F_3f4bc D_3f4bc (SB + ff4 p / 8 + 64)%Z (Z_to_bv 64 0) Q2
             ltac:(apply store_ok8_bytes; [lia|lia|]; intros j Hj; unfold m4; repeat apply store_ok1_wbytes; apply FRc;
                   unfold ff4, FR4; replace (SB + (fs + 4231168 + 1024 * p) / 8 + 64 + j)%Z with (SB + (fs + 4231168 + 1024 * p) / 8 + (64 + j))%Z by lia;
                   apply Wshad; lia).
        msd14 F_3f4c0 D_3f4c0 (SB + ff4 p / 8 + 72)%Z (Z_to_bv 64 0) Q2
             ltac:(apply store_ok8_bytes; [lia|lia|]; intros j Hj; unfold m4; repeat apply store_ok1_wbytes; apply FRc;
                   unfold ff4, FR4; replace (SB + (fs + 4231168 + 1024 * p) / 8 + 72 + j)%Z with (SB + (fs + 4231168 + 1024 * p) / 8 + (72 + j))%Z by lia;
                   apply Wshad; lia).
        msd14 F_3f4c4 D_3f4c4 (SB + ff4 p / 8 + 80)%Z (Z_to_bv 64 0) Q2
             ltac:(apply store_ok8_bytes; [lia|lia|]; intros j Hj; unfold m4; repeat apply store_ok1_wbytes; apply FRc;
                   unfold ff4, FR4; replace (SB + (fs + 4231168 + 1024 * p) / 8 + 80 + j)%Z with (SB + (fs + 4231168 + 1024 * p) / 8 + (80 + j))%Z by lia;
                   apply Wshad; lia).
        msd14 F_3f4c8 D_3f4c8 (SB + ff4 p / 8 + 88)%Z (Z_to_bv 64 0) Q2
             ltac:(apply store_ok8_bytes; [lia|lia|]; intros j Hj; unfold m4; repeat apply store_ok1_wbytes; apply FRc;
                   unfold ff4, FR4; replace (SB + (fs + 4231168 + 1024 * p) / 8 + 88 + j)%Z with (SB + (fs + 4231168 + 1024 * p) / 8 + (88 + j))%Z by lia;
                   apply Wshad; lia).
        msd14 F_3f4cc D_3f4cc (SB + ff4 p / 8 + 96)%Z (Z_to_bv 64 0) Q2
             ltac:(apply store_ok8_bytes; [lia|lia|]; intros j Hj; unfold m4; repeat apply store_ok1_wbytes; apply FRc;
                   unfold ff4, FR4; replace (SB + (fs + 4231168 + 1024 * p) / 8 + 96 + j)%Z with (SB + (fs + 4231168 + 1024 * p) / 8 + (96 + j))%Z by lia;
                   apply Wshad; lia).
        msd14 F_3f4d0 D_3f4d0 (SB + ff4 p / 8 + 104)%Z (Z_to_bv 64 0) Q2
             ltac:(apply store_ok8_bytes; [lia|lia|]; intros j Hj; unfold m4; repeat apply store_ok1_wbytes; apply FRc;
                   unfold ff4, FR4; replace (SB + (fs + 4231168 + 1024 * p) / 8 + 104 + j)%Z with (SB + (fs + 4231168 + 1024 * p) / 8 + (104 + j))%Z by lia;
                   apply Wshad; lia).
        msd14 F_3f4d4 D_3f4d4 (SB + ff4 p / 8 + 112)%Z (Z_to_bv 64 0) Q2
             ltac:(apply store_ok8_bytes; [lia|lia|]; intros j Hj; unfold m4; repeat apply store_ok1_wbytes; apply FRc;
                   unfold ff4, FR4; replace (SB + (fs + 4231168 + 1024 * p) / 8 + 112 + j)%Z with (SB + (fs + 4231168 + 1024 * p) / 8 + (112 + j))%Z by lia;
                   apply Wshad; lia).
        msd14 F_3f4d8 D_3f4d8 (SB + ff4 p / 8 + 120)%Z (Z_to_bv 64 0) Q2
             ltac:(apply store_ok8_bytes; [lia|lia|]; intros j Hj; unfold m4; repeat apply store_ok1_wbytes; apply FRc;
                   unfold ff4, FR4; replace (SB + (fs + 4231168 + 1024 * p) / 8 + 120 + j)%Z with (SB + (fs + 4231168 + 1024 * p) / 8 + (120 + j))%Z by lia;
                   apply Wshad; lia).
        change (wbytes _ _ _) with (WR4 m i p).
        mstep ltac:(eapply (@step_ld _ _ _ _ _ _ _ _ _ _ _ ra F_3f4dc eq_refl D_3f4dc);
                     [ gr; rewrite Q2; imm_norm; zn; replace (usp - 32 + 24)%Z with (usp - 8)%Z by lia; exact R8 | apply bytes_le_to_Z_8 ]).
        mstep ltac:(eapply (@step_ld _ _ _ _ _ _ _ _ _ _ _ (getr regs0 8) F_3f4e0 eq_refl D_3f4e0);
                     [ gr; rewrite Q2; imm_norm; zn; replace (usp - 32 + 16)%Z with (usp - 16)%Z by lia; exact R16 | apply bytes_le_to_Z_8 ]).
        mstep ltac:(eapply (@step_ld _ _ _ _ _ _ _ _ _ _ _ (getr regs0 9) F_3f4e4 eq_refl D_3f4e4);
                     [ gr; rewrite Q2; imm_norm; zn; replace (usp - 32 + 8)%Z with (usp - 24)%Z by lia; exact R24 | apply bytes_le_to_Z_8 ]).
        mstep ltac:(eapply (@step_ld _ _ _ _ _ _ _ _ _ _ _ (getr regs0 18) F_3f4e8 eq_refl D_3f4e8);
                     [ gr; rewrite Q2; imm_norm; zn; rewrite ?Z.add_0_r; exact R32 | apply bytes_le_to_Z_8 ]).
        mstep ltac:(exact (step_addi _ _ _ _ _ _ _ _ _ F_3f4ec eq_refl D_3f4ec)). gr. rewrite Q2. zn.
        replace (usp - 32 + 32)%Z with usp by lia.
        eapply mst_step; [reflexivity | eapply (step_jalr_x0 _ _ _ _ _ _ _ _ ra F_3f4f0 eq_refl D_3f4f0); gr; reflexivity |].
        imm_norm. rewrite Hret. apply mst_refl.
      - gr. repeat split; try reflexivity.
        intros r Hr. unfold f_clob4 in Hr.
        repeat (rewrite getr_other by (intros ->; cbn in Hr; discriminate)).
        rewrite QK by (unfold m2s_clob; repeat match type of Hr with (?a || ?b)%bool = false => apply orb_false_iff in Hr; destruct Hr as [Hr ?] end;
                       repeat match goal with Hb : bv_eqb r _ = false |- _ => rewrite Hb; clear Hb end; reflexivity).
        apply PK; intros ->; cbn in Hr; discriminate.
    Qed.

    (* [comment removed for export] *)
    #[using="ctx thr db beg a2v a3v H Hret H01 H02 H04 p0 Hhint Hflags Hp0 Whint Wflag Wframe Wshad i0"] Theorem sm4_AM :
      exists i p regs' m',
        (0 <= i < N4)%Z /\ p = pos4 i /\ bv_unsigned (FL p) = 0%Z
        /\ msteps SEGS (mkst regs0 (0x3f344 : word) mem rom) (mkst regs' ra m' rom)
        /\ getr regs' 10 = Z_to_bv 64 (ff4 p) /\ getr regs' 2 = Z_to_bv 64 usp /\ getr regs' 1 = ra
        /\ (forall r, sm_clob r = false -> getr regs' r = getr regs0 r)
        /\ (forall x : word, (bv_unsigned x < usp - SM_FRAME \/ usp <= bv_unsigned x)%Z -> m' x = WR4 mem i p x)
        /\ (forall x, mem x <> None -> m' x <> None)
        /\ (forall x, store_ok SEGS mem x 1 = true -> store_ok SEGS m' x 1 = true).
    Proof.
      pose proof HU as U. pose proof i0_rng4 as I0.
      destruct blk_PT4 as (q1 & m2 & M1 & A2 & A8 & A10 & A4 & AK & FR & AG).
      destruct (blk_A4 q1 m2 FR A10) as (q2 & M2 & B9 & B18 & B10 & B12 & B13 & B14 & B11 & BK).
      destruct (blk_L4 (Z.to_nat i0) 0 q2 m2 ltac:(lia) ltac:(lia) FR B10 B12 B13 B14)
        as (i & q3 & Hi & HZ & M3 & C12 & C17 & C15 & CK).
      assert (C2 : getr q3 2 = Z_to_bv 64 (usp - 32)) by (rewrite CK, BK by reflexivity; exact A2).
      assert (C8 : getr q3 8 = Z_to_bv 64 usp) by (rewrite CK, BK by reflexivity; exact A8).
      assert (C9 : getr q3 9 = Z_to_bv 64 fs) by (rewrite CK by reflexivity; exact B9).
      assert (C18 : getr q3 18 = Z_to_bv 64 20) by (rewrite CK by reflexivity; exact B18).
      assert (C11 : getr q3 11 = Z_to_bv 64 (fs + 4096)) by (rewrite CK by reflexivity; exact B11).
      pose proof (pos_rng4 i) as PR.
      destruct (blk_F4 q3 m2 i (pos4 i) FR AG PR ltac:(lia) C2 C8 C9 C18 C11 C12 C17 C15)
        as (q4 & M4 & D10 & D2 & D1 & D8 & D9 & D18 & DK).
      exists i, (pos4 i), q4, (WR4 m2 i (pos4 i)).
      split; [lia|]. split; [reflexivity|]. split; [exact HZ|]. split.
      { eapply msteps_trans; [exact M1|]. eapply msteps_trans; [exact M2|]. eapply msteps_trans; [exact M3|]. exact M4. }
      split; [exact D10|]. split; [exact D2|]. split; [exact D1|]. split.
      { intros r Hr.
        destruct (bv_eq_dec _ r 1) as [-> | X1]; [rewrite D1; symmetry; exact H01|].
        destruct (bv_eq_dec _ r 2) as [-> | N2]; [rewrite D2; symmetry; exact H02|].
        destruct (bv_eq_dec _ r 8) as [-> | N8]; [exact D8|].
        destruct (bv_eq_dec _ r 9) as [-> | N9]; [exact D9|].
        destruct (bv_eq_dec _ r 18) as [-> | N18]; [exact D18|].
        assert (NE : forall k : reg, r <> k -> bv_eqb r k = false) by (intros k Hk; apply bv_eqb_neq; exact Hk).
        pose proof (NE _ X1) as T1. pose proof (NE _ N2) as T2. pose proof (NE _ N8) as T8. pose proof (NE _ N9) as T9. pose proof (NE _ N18) as T18.
        unfold sm_clob in Hr.
        apply orb_false_iff in Hr as [Hr T17]. apply orb_false_iff in Hr as [Hr T16]. apply orb_false_iff in Hr as [Hr T15].
        apply orb_false_iff in Hr as [Hr T14]. apply orb_false_iff in Hr as [Hr T13]. apply orb_false_iff in Hr as [Hr T12].
        apply orb_false_iff in Hr as [Hr T11]. apply orb_false_iff in Hr as [T5 T10].
        rewrite DK by (unfold f_clob4; rewrite ?T1, ?T2, ?T5, ?T8, ?T9, ?T10, ?T11, ?T12, ?T13, ?T14, ?T15, ?T16, ?T17, ?T18; reflexivity).
        rewrite CK by (unfold l_clob4; rewrite ?T5, ?T10, ?T12, ?T15, ?T17; reflexivity).
        rewrite BK by (unfold a_clob4; rewrite ?T9, ?T10, ?T11, ?T12, ?T13, ?T14, ?T15, ?T16, ?T18; reflexivity).
        apply AK. unfold t_keep4, tls_clob. rewrite T10, T11, T12, T13, T1, T2, T8. reflexivity. }
      destruct FR as (FRa & FRb & FRc). split; [|split].
      - intros x Hx. apply WR_agree4. apply FRa. exact Hx.
      - intros x Hx. apply WR_keep4. apply FRb. exact Hx.
      - intros x Hx. apply WR_sok4. apply FRc. exact Hx.
    Qed.
  End C4.
End SM.
