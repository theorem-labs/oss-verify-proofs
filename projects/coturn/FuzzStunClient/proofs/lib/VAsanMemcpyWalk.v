(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From Stdlib Require Import FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.coturn.FuzzStunClient.images Require Import Asan.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import PropExec CatExec CatSim SeqExec MmapSim StepTac Hoare RefEnframeArith.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Asan Require Import AsanRegionPoisoned.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require RefMemcpyLib.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Asan Require AsanMemcpyBase AsanMemcpy.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib Require Import VAsanMemcpy_code VAsanMemsetWalk.
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
Lemma lit_cc2fc : v_addi (0x53f28 : word) 4 = (0x53f2c : word). Proof. apply bv_eq; vm_compute; reflexivity. Qed.
Lemma lit_cc5a4 : v_addi (0x541d0 : word) 4 = (0x541d4 : word). Proof. apply bv_eq; vm_compute; reflexivity. Qed.
Lemma lit_cc644 : v_addi (0x54270 : word) 4 = (0x54274 : word). Proof. apply bv_eq; vm_compute; reflexivity. Qed.
Lemma ret_ok_cc2fc : ret_ok (0x53f2c : word). Proof. apply ret_ok_even. vm_compute. reflexivity. Qed.
Lemma ret_ok_cc5a4 : ret_ok (0x541d4 : word). Proof. apply ret_ok_even. vm_compute. reflexivity. Qed.
Lemma ret_ok_cc644 : ret_ok (0x54274 : word). Proof. apply ret_ok_even. vm_compute. reflexivity. Qed.

Definition CP_ENTRY : Z := 0x53e30.
Definition CP_FRAME : Z := 2216.     (* [comment removed for export] *)

(* [comment removed for export] *)
Definition cp_cells (m : word -> option byte) : Prop :=
  cells m
  /\ cell m 0xab9e8 0xb42d9 /\ rdn SEGS m (Z_to_bv 64 0xb42d9) 1 = Some [Z_to_bv 8 1]
  /\ cell m 0xacce8 0xa41ac.

Record cpH (mem : word -> option byte) (d s n usp : Z) (bs : list byte) : Prop := {
  cp_n    : (0 <= n <= 2 ^ 40)%Z;
  cp_d    : (0 <= d)%Z;
  cp_s    : (0 <= s)%Z;
  cp_dn   : (d + n < 2 ^ 64)%Z;
  cp_sn   : (s + n < 2 ^ 64)%Z;
  (* [comment removed for export] *)
  cp_disj : (n = 0 \/ s + n <= d \/ d + n <= s)%Z;
  (* [comment removed for export] *)
  cp_len  : length bs = Z.to_nat n;
  cp_src  : rdn SEGS mem (Z_to_bv 64 s) (length bs) = Some bs;
  cp_rngd : (0 < n)%Z -> (d + n <= kLowEnd)%Z \/ (kHighBeg <= d /\ d + n <= kHighEnd)%Z;
  cp_rngs : (0 < n)%Z -> (s + n <= kLowEnd)%Z \/ (kHighBeg <= s /\ s + n <= kHighEnd)%Z;
  cp_sp   : (SB + CP_FRAME + 8 <= usp < 2 ^ 64)%Z;
  (* [comment removed for export] *)
  cp_dst  : (n = 0 \/ usp <= d \/ d + n <= usp - CP_FRAME)%Z;
  cp_sst  : (n = 0 \/ usp <= s \/ s + n <= usp - CP_FRAME)%Z;
  cp_shd  : (0 < n)%Z -> (SB + (d + n - 1) / 8 + 8 < usp - CP_FRAME)%Z;
  cp_shs  : (0 < n)%Z -> (SB + (s + n - 1) / 8 + 8 < usp - CP_FRAME)%Z;
  (* [comment removed for export] *)
  cp_zerod : forall g, (0 < n)%Z -> (d / 8 <= g < (d + n - 1) / 8)%Z -> mem (Z_to_bv 64 (SB + g)) = Some (Z_to_bv 8 0);
  cp_lastd : (0 < n)%Z -> exists b1 : byte, mem (Z_to_bv 64 (SB + (d + n - 1) / 8)) = Some b1
                                      /\ (bv_unsigned b1 = 0%Z \/ ((d + n - 1) mod 8 < bv_unsigned b1 < 8)%Z);
  cp_zeros : forall g, (0 < n)%Z -> (s / 8 <= g < (s + n - 1) / 8)%Z -> mem (Z_to_bv 64 (SB + g)) = Some (Z_to_bv 8 0);
  cp_lasts : (0 < n)%Z -> exists b1 : byte, mem (Z_to_bv 64 (SB + (s + n - 1) / 8)) = Some b1
                                      /\ (bv_unsigned b1 = 0%Z \/ ((s + n - 1) mod 8 < bv_unsigned b1 < 8)%Z);
  (* [comment removed for export] *)
  cp_w1d  : (0 < n)%Z -> exists w : word, rdn SEGS mem (Z_to_bv 64 ((SB + d / 8) / 8 * 8)) 8 = Some (word_to_le_bytes 8 w);
  cp_w2d  : (0 < n)%Z -> exists w : word, rdn SEGS mem (Z_to_bv 64 ((SB + (d + n - 1) / 8) / 8 * 8)) 8 = Some (word_to_le_bytes 8 w);
  cp_w1s  : (0 < n)%Z -> exists w : word, rdn SEGS mem (Z_to_bv 64 ((SB + s / 8) / 8 * 8)) 8 = Some (word_to_le_bytes 8 w);
  cp_w2s  : (0 < n)%Z -> exists w : word, rdn SEGS mem (Z_to_bv 64 ((SB + (s + n - 1) / 8) / 8 * 8)) 8 = Some (word_to_le_bytes 8 w);
  (* [comment removed for export] *)
  cp_dok  : forall j, (0 <= j < n)%Z -> store_ok SEGS mem (Z_to_bv 64 (d + j)) 1 = true;
  cp_stk  : forall a, (usp - CP_FRAME <= a < usp)%Z -> store_ok SEGS mem (Z_to_bv 64 a) 1 = true;
  cp_cel  : cp_cells mem
}.

(* [comment removed for export] *)
Definition cp_clob (r : reg) : bool :=
  (bv_eqb r 5 || bv_eqb r 6 || bv_eqb r 7 || bv_eqb r 10 || bv_eqb r 11 || bv_eqb r 12 || bv_eqb r 13 || bv_eqb r 14
   || bv_eqb r 15 || bv_eqb r 16 || bv_eqb r 17 || bv_eqb r 28 || bv_eqb r 29 || bv_eqb r 30 || bv_eqb r 31)%bool.

(* [comment removed for export] *)
Lemma kept_of_clob (r : reg) : cp_clob r = false -> r <> 0 -> r <> 1 -> In r RefMemcpyLib.callee_kept.
Proof.
  intros C N0 N1.
  assert (B : existsb (bv_eqb r) RefMemcpyLib.callee_kept = true).
  { pose proof (bv_unsigned_in_range 5 r) as R. change (bv_modulus 5) with 32%Z in R.
    assert (U0 : bv_unsigned r <> 0%Z) by (intros X; apply N0; apply bv_eq; exact X).
    assert (U1 : bv_unsigned r <> 1%Z) by (intros X; apply N1; apply bv_eq; exact X).
    assert (E : r = Z_to_bv 5 (bv_unsigned r)) by (apply bv_eq; rewrite Z_to_bv_unsigned; symmetry; apply bv_wrap_small; exact (bv_unsigned_in_range 5 r)).
    revert C. rewrite E. generalize R U0 U1. generalize (bv_unsigned r) as u. clear. intros u R U0 U1.
    destruct (Z_of_nat_complete u ltac:(lia)) as [k ->].
    do 32 (destruct k as [|k]; [vm_compute; intros X; first [discriminate X | reflexivity | exfalso; lia] |]). lia. }
  apply existsb_exists in B as (k & Hk & E). unfold bv_eqb in E. apply Z.eqb_eq in E. apply bv_eq in E. subst. exact Hk.
Qed.

Lemma keeps_unclobbered regs regs' (r : reg) :
  RefMemcpyLib.keeps regs regs' -> cp_clob r = false -> r <> 1 -> getr regs' r = getr regs r.
Proof.
  intros K C N1. destruct (bv_eq_dec _ r 0) as [->|N0]; [rewrite !getr_zero; reflexivity|].
  exact (K r (kept_of_clob r C N0 N1)).
Qed.

Section CP.
  Variables (mem rom : word -> option byte) (d s n usp : Z) (bs : list byte).
  Hypothesis H : cpH mem d s n usp bs.
  Variable regs0 : bvmap 5 word.
  Variable ra : word.
  Hypothesis Hret : ret_ok ra.
  Hypothesis H01 : getr regs0 1 = ra.
  Hypothesis H02 : getr regs0 2 = Z_to_bv 64 usp.
  Hypothesis H010 : getr regs0 10 = Z_to_bv 64 d.
  Hypothesis H011 : getr regs0 11 = Z_to_bv 64 s.
  Hypothesis H012 : getr regs0 12 = Z_to_bv 64 n.

  Let Hn := cp_n _ _ _ _ _ _ H.
  Let Hd := cp_d _ _ _ _ _ _ H.
  Let Hs := cp_s _ _ _ _ _ _ H.
  #[using="mem d s n bs H"] Lemma Hsp : (0x7fff8000 + 2224 <= usp < 2 ^ 64)%Z.
  Proof. pose proof (cp_sp _ _ _ _ _ _ H). unfold CP_FRAME, SB in *. lia. Qed.

  (* [comment removed for export] *)
  Definition p9 : word -> option byte :=
    let w (o : Z) (v : word) (m : word -> option byte) := wbytes m (Z_to_bv 64 (usp - o)) (word_to_le_bytes 8 v) in
    w 72%Z (getr regs0 23) (w 64%Z (getr regs0 22) (w 56%Z (getr regs0 21) (w 48%Z (getr regs0 20) (w 40%Z (getr regs0 19)
      (w 32%Z (getr regs0 18) (w 24%Z (getr regs0 9) (w 16%Z (getr regs0 8) (w 8%Z ra mem)))))))).

  Ltac len8 := rewrite ?length_N_to_le_bytes; change (Z.of_nat 8) with 8%Z.

  #[using="d s n bs H"] Lemma p9_below : forall x : word, (bv_unsigned x < usp - 72)%Z -> p9 x = mem x.
  Proof.
    intros x Hx. unfold p9. pose proof Hsp. rewrite !wbytes_below; try reflexivity; len8; rewrite ?zbv_u by lia; lia.
  Qed.

  #[using="d s n bs H"] Lemma p9_out : forall x : word, (bv_unsigned x < usp - 72 \/ usp <= bv_unsigned x)%Z -> p9 x = mem x.
  Proof.
    intros x [Hx|Hx]; [apply p9_below; exact Hx|]. unfold p9. pose proof Hsp.
    rewrite !wbytes_above; try reflexivity; len8; rewrite ?zbv_u by lia; lia.
  Qed.

  #[using="d s n bs H"] Lemma rdn_p9_below : forall (a : Z) k, (0 <= a)%Z -> (a + Z.of_nat k <= usp - 72)%Z ->
    rdn SEGS p9 (Z_to_bv 64 a) k = rdn SEGS mem (Z_to_bv 64 a) k.
  Proof.
    intros a k Ha Hk. pose proof Hsp. apply rdn_ext; [rewrite zbv_u by lia; lia|].
    intros x Hx. rewrite zbv_u in Hx by lia. apply p9_below. lia.
  Qed.

  #[using="d s n bs H"] Lemma rdn_p9_out : forall (a : Z) k, (0 <= a < 2 ^ 64)%Z -> (a + Z.of_nat k <= 2 ^ 64)%Z ->
    (a + Z.of_nat k <= usp - 72 \/ usp <= a)%Z ->
    rdn SEGS p9 (Z_to_bv 64 a) k = rdn SEGS mem (Z_to_bv 64 a) k.
  Proof.
    intros a k Ha Hk Hap. pose proof Hsp. apply rdn_ext; [rewrite zbv_u by lia; lia|].
    intros x Hx. rewrite zbv_u in Hx by lia. apply p9_out. lia.
  Qed.

  #[using="d s n bs H"] Lemma stk8p : forall m a, (usp - CP_FRAME <= a)%Z -> (a + 8 <= usp)%Z ->
    (forall x, store_ok SEGS mem x 1 = true -> store_ok SEGS m x 1 = true) ->
    store_ok SEGS m (Z_to_bv 64 a) 8 = true.
  Proof.
    intros m a H1 H2 Hm. unfold CP_FRAME in *. pose proof Hsp. apply store_ok8_bytes; [lia|lia|].
    intros j Hj. apply Hm. apply (cp_stk _ _ _ _ _ _ H). unfold CP_FRAME. lia.
  Qed.

  Definition keep (regs : bvmap 5 word) : Prop :=
    forall r : reg, cp_clob r = false -> r <> 1 -> r <> 2 -> r <> 8 -> r <> 9 -> r <> 18 -> r <> 19 -> r <> 20 -> r <> 21 ->
      r <> 22 -> r <> 23 -> getr regs r = getr regs0 r.

  Ltac msd F D o v Hbase :=
    mstep ltac:(eapply (step_sd_at _ _ _ _ _ _ _ _ _ (Z_to_bv 64 (usp - o)) v F eq_refl D);
                 [ gr; rewrite ?Hbase; imm_norm; zn; apply (f_equal (Z_to_bv 64)); lia
                 | gr; first [reflexivity | assumption | symmetry; assumption]
                 | apply stk8p; [unfold CP_FRAME; lia | lia | intros x Hx; repeat apply store_ok1_wbytes; exact Hx] ]).

  (* [comment removed for export] *)
  #[using="bs H H01 H02 H010 H011 H012"] Lemma blk_P :
    exists regs,
      msteps SEGS (mkst regs0 (0x53e30 : word) mem rom) (mkst regs (0x53e60 : word) p9 rom)
      /\ getr regs 2 = Z_to_bv 64 (usp - 2144) /\ getr regs 8 = Z_to_bv 64 usp
      /\ getr regs 10 = Z_to_bv 64 d /\ getr regs 11 = Z_to_bv 64 s /\ getr regs 12 = Z_to_bv 64 n
      /\ getr regs 1 = ra /\ keep regs.
  Proof.
    pose proof Hsp.
    eexists. split.
    - mstep ltac:(exact (step_addi _ _ _ _ _ _ _ _ _ F_53e30 eq_refl D_53e30)). rewrite H02. zn.
      msd F_53e34 D_53e34 8%Z ra H02.
      msd F_53e38 D_53e38 16%Z (getr regs0 8) H02.
      msd F_53e3c D_53e3c 24%Z (getr regs0 9) H02.
      msd F_53e40 D_53e40 32%Z (getr regs0 18) H02.
      msd F_53e44 D_53e44 40%Z (getr regs0 19) H02.
      msd F_53e48 D_53e48 48%Z (getr regs0 20) H02.
      msd F_53e4c D_53e4c 56%Z (getr regs0 21) H02.
      msd F_53e50 D_53e50 64%Z (getr regs0 22) H02.
      msd F_53e54 D_53e54 72%Z (getr regs0 23) H02.
      mstep ltac:(exact (step_addi _ _ _ _ _ _ _ _ _ F_53e58 eq_refl D_53e58)). gr. zn.
      mstep ltac:(exact (step_addi _ _ _ _ _ _ _ _ _ F_53e5c eq_refl D_53e5c)). gr. zn.
      apply mst_refl.
    - gr. repeat split; try (apply (f_equal (Z_to_bv 64)); lia); try assumption.
      intros r Hr N1 N2 N8 N9 N18 N19 N20 N21 N22 N23. unfold cp_clob in Hr.
      repeat (rewrite getr_other by (intros ->; cbn in Hr; try discriminate; congruence)). reflexivity.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  #[using="d s n bs H"] Lemma cells_p9 : cp_cells p9.
  Proof.
    pose proof (cp_cel _ _ _ _ _ _ H) as C. pose proof Hsp. pose proof SB_val.
    unfold cp_cells, cells, cell in *. rewrite !rdn_p9_below by (cbn; lia). exact C.
  Qed.

  Definition b_clob (r : reg) : bool := (bv_eqb r 13 || bv_eqb r 19 || bv_eqb r 20 || bv_eqb r 21 || bv_eqb r 22)%bool.

  #[using="bs H Hn Hd Hs"] Lemma blk_B : forall regs,
    getr regs 8 = Z_to_bv 64 usp -> getr regs 10 = Z_to_bv 64 d -> getr regs 11 = Z_to_bv 64 s -> getr regs 12 = Z_to_bv 64 n ->
    exists regs',
      msteps SEGS (mkst regs (0x53e60 : word) p9 rom) (mkst regs' (0x53e9c : word) p9 rom)
      /\ getr regs' 22 = Z_to_bv 64 (n - 65) /\ getr regs' 13 = Z_to_bv 64 (2 ^ 64 - 65)
      /\ getr regs' 20 = Z_to_bv 64 (usp - 2144) /\ getr regs' 21 = Z_to_bv 64 (s + n) /\ getr regs' 19 = Z_to_bv 64 (d + n)
      /\ (forall r, b_clob r = false -> getr regs' r = getr regs r).
  Proof.
    intros regs H8 H10 H11 H12. pose proof Hsp. pose proof SB_val as HSB.
    pose proof (cp_dn _ _ _ _ _ _ H) as Hdn. pose proof (cp_sn _ _ _ _ _ _ H) as Hsn. pose proof (cp_disj _ _ _ _ _ _ H) as Hdisj.
    pose proof cells_p9 as (CC & G1 & B1 & G2).
    eexists. split.
    - mstep ltac:(eapply (step_auipc_at _ _ _ _ _ _ _ _ (Z_to_bv 64 0xabe60) F_53e60 eq_refl D_53e60);
                   [reflexivity | apply bv_eq; vm_compute; reflexivity]).
      mld F_53e64 D_53e64 0xb42d9%Z G1 H8.
      mstep ltac:(eapply (@step_lbu _ _ _ _ _ _ _ _ _ _ (Z_to_bv 8 1) F_53e68 eq_refl D_53e68);
                   gr; imm_norm; zn; rewrite Z.add_0_r; exact B1).
      change (bv_unsigned (Z_to_bv 8 1)) with 1%Z.
      mstep ltac:(eapply (step_beq_ft _ _ _ _ _ _ _ _ _ F_53e6c eq_refl D_53e6c); gr; rewrite ?getr_zero; br_eq).
      mstep ltac:(exact (step_addi _ _ _ _ _ _ _ _ _ F_53e70 eq_refl D_53e70)). gr. rewrite H8. zn.
      mstep ltac:(exact (step_addi _ _ _ _ _ _ _ _ _ F_53e74 eq_refl D_53e74)). gr. zn.
      mstep ltac:(exact (step_add _ _ _ _ _ _ _ _ _ F_53e78 eq_refl D_53e78)). gr. rewrite H11, H12, v_add_zbv by lia.
      mstep ltac:(exact (step_add _ _ _ _ _ _ _ _ _ F_53e7c eq_refl D_53e7c)). gr. rewrite H10, H12, v_add_zbv by lia.
      destruct (Z.eq_dec d s) as [Eds|Nds].
      + mstep ltac:(eapply (step_beq_tk _ _ _ _ _ _ _ _ _ F_53e80 eq_refl D_53e80); gr; rewrite ?H10, ?H11; br_eq).
        mstep ltac:(exact (step_xori _ _ _ _ _ _ _ _ _ F_53e8c eq_refl D_53e8c)). gr. rewrite H11. rewrite v_not_zbv by lia.
        mstep ltac:(eapply (step_bltu_ft _ _ _ _ _ _ _ _ _ F_53e90 eq_refl D_53e90); gr; rewrite ?H12; br_lt).
        mstep ltac:(exact (step_addi _ _ _ _ _ _ _ _ _ F_53e94 eq_refl D_53e94)). gr. rewrite H12. zn.
        mstep ltac:(exact (step_addi _ _ _ _ _ _ _ _ _ F_53e98 eq_refl D_53e98)). rewrite getr_zero. zn.
        apply mst_refl.
      + mstep ltac:(eapply (step_beq_ft _ _ _ _ _ _ _ _ _ F_53e80 eq_refl D_53e80); gr; rewrite ?H10, ?H11; br_eq).
        destruct (Z_le_gt_dec (d + n) s) as [Hfar|Hnear].
        * mstep ltac:(eapply (step_bgeu_tk _ _ _ _ _ _ _ _ _ F_53e84 eq_refl D_53e84); gr; rewrite ?H11; br_lt).
          mstep ltac:(exact (step_xori _ _ _ _ _ _ _ _ _ F_53e8c eq_refl D_53e8c)). gr. rewrite H11. rewrite v_not_zbv by lia.
          mstep ltac:(eapply (step_bltu_ft _ _ _ _ _ _ _ _ _ F_53e90 eq_refl D_53e90); gr; rewrite ?H12; br_lt).
          mstep ltac:(exact (step_addi _ _ _ _ _ _ _ _ _ F_53e94 eq_refl D_53e94)). gr. rewrite H12. zn.
          mstep ltac:(exact (step_addi _ _ _ _ _ _ _ _ _ F_53e98 eq_refl D_53e98)). rewrite getr_zero. zn.
          apply mst_refl.
        * mstep ltac:(eapply (step_bgeu_ft _ _ _ _ _ _ _ _ _ F_53e84 eq_refl D_53e84); gr; rewrite ?H11; br_lt).
          mstep ltac:(eapply (step_bltu_ft _ _ _ _ _ _ _ _ _ F_53e88 eq_refl D_53e88); gr; rewrite ?H10; br_lt).
          mstep ltac:(exact (step_xori _ _ _ _ _ _ _ _ _ F_53e8c eq_refl D_53e8c)). gr. rewrite H11. rewrite v_not_zbv by lia.
          mstep ltac:(eapply (step_bltu_ft _ _ _ _ _ _ _ _ _ F_53e90 eq_refl D_53e90); gr; rewrite ?H12; br_lt).
          mstep ltac:(exact (step_addi _ _ _ _ _ _ _ _ _ F_53e94 eq_refl D_53e94)). gr. rewrite H12. zn.
          mstep ltac:(exact (step_addi _ _ _ _ _ _ _ _ _ F_53e98 eq_refl D_53e98)). rewrite getr_zero. zn.
          apply mst_refl.
    - gr. repeat split.
      + rewrite <- (zbv_wrap_add (-65)). apply (f_equal (Z_to_bv 64)). lia.
      + apply (f_equal (Z_to_bv 64)). lia.
      + intros r Hr. unfold b_clob in Hr.
        repeat (rewrite getr_other by (intros ->; cbn in Hr; discriminate)). reflexivity.
  Qed.
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Ltac rd_side := len8; rewrite !zbv_u by lia; lia.
  Ltac rd_slot := pose proof Hsp; unfold p9;
    repeat (first [ apply rdn_wbytes_hit8; rewrite zbv_u by lia; lia
                  | rewrite rdn_wbytes_out; [| rd_side | rd_side | rd_side] ]).

  #[using="d s n bs H"] Lemma rd_ra : rdn SEGS p9 (Z_to_bv 64 (usp - 8)) 8 = Some (word_to_le_bytes 8 ra).              Proof. rd_slot. Qed.
  #[using="d s n bs H"] Lemma rd_s0 : rdn SEGS p9 (Z_to_bv 64 (usp - 16)) 8 = Some (word_to_le_bytes 8 (getr regs0 8)).  Proof. rd_slot. Qed.
  #[using="d s n bs H"] Lemma rd_s1 : rdn SEGS p9 (Z_to_bv 64 (usp - 24)) 8 = Some (word_to_le_bytes 8 (getr regs0 9)).  Proof. rd_slot. Qed.
  #[using="d s n bs H"] Lemma rd_s2 : rdn SEGS p9 (Z_to_bv 64 (usp - 32)) 8 = Some (word_to_le_bytes 8 (getr regs0 18)). Proof. rd_slot. Qed.
  #[using="d s n bs H"] Lemma rd_s3 : rdn SEGS p9 (Z_to_bv 64 (usp - 40)) 8 = Some (word_to_le_bytes 8 (getr regs0 19)). Proof. rd_slot. Qed.
  #[using="d s n bs H"] Lemma rd_s4 : rdn SEGS p9 (Z_to_bv 64 (usp - 48)) 8 = Some (word_to_le_bytes 8 (getr regs0 20)). Proof. rd_slot. Qed.
  #[using="d s n bs H"] Lemma rd_s5 : rdn SEGS p9 (Z_to_bv 64 (usp - 56)) 8 = Some (word_to_le_bytes 8 (getr regs0 21)). Proof. rd_slot. Qed.
  #[using="d s n bs H"] Lemma rd_s6 : rdn SEGS p9 (Z_to_bv 64 (usp - 64)) 8 = Some (word_to_le_bytes 8 (getr regs0 22)). Proof. rd_slot. Qed.
  #[using="d s n bs H"] Lemma rd_s7 : rdn SEGS p9 (Z_to_bv 64 (usp - 72)) 8 = Some (word_to_le_bytes 8 (getr regs0 23)). Proof. rd_slot. Qed.

  (* [comment removed for export] *)
  Definition sfr (m : word -> option byte) : Prop :=
       (forall x : word, (bv_unsigned x < usp - CP_FRAME \/ usp - 2144 <= bv_unsigned x)%Z -> m x = p9 x)
    /\ (forall x, store_ok SEGS mem x 1 = true -> store_ok SEGS m x 1 = true)
    /\ (forall x, mem x <> None -> m x <> None).

  #[using="Type"] Lemma p9_sok : forall x, store_ok SEGS mem x 1 = true -> store_ok SEGS p9 x 1 = true.
  Proof. intros x Hx. unfold p9. repeat apply store_ok1_wbytes. exact Hx. Qed.
  #[using="Type"] Lemma p9_keep : forall x, mem x <> None -> p9 x <> None.
  Proof. intros x Hx. unfold p9. repeat apply wbytes_keep. exact Hx. Qed.
  #[using="Type"] Lemma sfr_p9 : sfr p9.
  Proof. split; [intros; reflexivity|]. split; [exact p9_sok|exact p9_keep]. Qed.

  #[using="d s n bs H"] Lemma sfr_rp : forall m (rra s0 s1 s2 s3 s4 s5 : word), sfr m -> sfr (rp_frame m (usp - 2144) rra s0 s1 s2 s3 s4 s5).
  Proof.
    intros m rra s0 s1 s2 s3 s4 s5 (F1 & F2 & F3). pose proof Hsp. unfold sfr, CP_FRAME in *. split; [|split].
    - intros x Hx. unfold rp_frame. rewrite <- (F1 x Hx). destruct Hx as [Hx|Hx].
      + rewrite !wbytes_below; try reflexivity; len8; rewrite ?zbv_u by lia; lia.
      + rewrite !wbytes_above; try reflexivity; len8; rewrite ?zbv_u by lia; lia.
    - intros x Hx. unfold rp_frame. repeat apply store_ok1_wbytes. apply F2. exact Hx.
    - intros x Hx. unfold rp_frame. repeat apply wbytes_keep. apply F3. exact Hx.
  Qed.

  #[using="d s n bs H"] Lemma sfr_below : forall m (x : word), sfr m -> (bv_unsigned x < usp - CP_FRAME)%Z -> m x = mem x.
  Proof. intros m x (F1 & _) Hx. rewrite (F1 x (or_introl Hx)). apply p9_below. unfold CP_FRAME in Hx. lia. Qed.

  #[using="d s n bs H"] Lemma rdn_sfr_below : forall m (a : Z) k, sfr m -> (0 <= a)%Z -> (a + Z.of_nat k <= usp - CP_FRAME)%Z ->
    rdn SEGS m (Z_to_bv 64 a) k = rdn SEGS mem (Z_to_bv 64 a) k.
  Proof.
    intros m a k F Ha Hk. pose proof Hsp. unfold CP_FRAME in *. apply rdn_ext; [rewrite zbv_u by lia; lia|].
    intros x Hx. rewrite zbv_u in Hx by lia. apply (sfr_below m x F). unfold CP_FRAME. lia.
  Qed.

  #[using="d s n bs H"] Lemma rdn_sfr_out : forall m (a : Z) k, sfr m -> (0 <= a < 2 ^ 64)%Z -> (a + Z.of_nat k <= 2 ^ 64)%Z ->
    (a + Z.of_nat k <= usp - CP_FRAME \/ usp <= a)%Z ->
    rdn SEGS m (Z_to_bv 64 a) k = rdn SEGS mem (Z_to_bv 64 a) k.
  Proof.
    intros m a k (F1 & _) Ha Hk Hap. pose proof Hsp. unfold CP_FRAME in *. apply rdn_ext; [rewrite zbv_u by lia; lia|].
    intros x Hx. rewrite zbv_u in Hx by lia. rewrite F1 by lia. apply p9_out. lia.
  Qed.

  #[using="d s n bs H"] Lemma cells_sfr : forall m, sfr m -> cp_cells m.
  Proof.
    intros m F. pose proof (cp_cel _ _ _ _ _ _ H) as C. pose proof Hsp. pose proof SB_val. unfold CP_FRAME in *.
    unfold cp_cells, cells, cell in *. rewrite !(rdn_sfr_below m) by (first [exact F | cbn; unfold CP_FRAME; lia]). exact C.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  #[using="mem d s usp bs H Hn"] Lemma blk_RZ : forall regs m,
    n = 0%Z -> getr regs 13 = Z_to_bv 64 (2 ^ 64 - 65) -> getr regs 22 = Z_to_bv 64 (n - 65) -> getr regs 12 = Z_to_bv 64 n ->
    msteps SEGS (mkst regs (0x53e9c : word) m rom) (mkst regs (0x53ed8 : word) m rom).
  Proof.
    intros regs m Hn0 H13 H22 H12.
    replace (Z_to_bv 64 (n - 65)) with (Z_to_bv 64 (2 ^ 64 - 65 + n)) in H22
      by (rewrite <- (zbv_wrap_add (n - 65)); apply (f_equal (Z_to_bv 64)); lia).
    mstep ltac:(eapply (step_bgeu_tk _ _ _ _ _ _ _ _ _ F_53e9c eq_refl D_53e9c); gr; rewrite ?H13, ?H22; br_lt).
    mstep ltac:(eapply (step_bne_ft _ _ _ _ _ _ _ _ _ F_54180 eq_refl D_54180); gr; rewrite ?H12, ?getr_zero; br_eq).
    mstep ltac:(exact (step_jal_x0 _ _ _ _ _ _ _ F_54184 eq_refl D_54184)).
    apply mst_refl.
  Qed.

  #[using="mem d s usp bs H Hn"] Lemma blk_WZ : forall regs m,
    n = 0%Z -> getr regs 13 = Z_to_bv 64 (2 ^ 64 - 65) -> getr regs 22 = Z_to_bv 64 (n - 65) -> getr regs 12 = Z_to_bv 64 n ->
    msteps SEGS (mkst regs (0x53ee4 : word) m rom) (mkst regs (0x53f20 : word) m rom).
  Proof.
    intros regs m Hn0 H13 H22 H12.
    replace (Z_to_bv 64 (n - 65)) with (Z_to_bv 64 (2 ^ 64 - 65 + n)) in H22
      by (rewrite <- (zbv_wrap_add (n - 65)); apply (f_equal (Z_to_bv 64)); lia).
    mstep ltac:(eapply (step_bgeu_tk _ _ _ _ _ _ _ _ _ F_53ee4 eq_refl D_53ee4); gr; rewrite ?H13, ?H22; br_lt).
    mstep ltac:(eapply (step_bne_ft _ _ _ _ _ _ _ _ _ F_54034 eq_refl D_54034); gr; rewrite ?H12, ?getr_zero; br_eq).
    mstep ltac:(exact (step_jal_x0 _ _ _ _ _ _ _ F_54038 eq_refl D_54038)).
    apply mst_refl.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  #[using="mem s usp bs H Hn Hd"] Lemma blk_W0 : forall regs m,
    getr regs 10 = Z_to_bv 64 d -> getr regs 12 = Z_to_bv 64 n ->
    exists regs',
      msteps SEGS (mkst regs (0x53ed8 : word) m rom) (mkst regs' (0x53ee4 : word) m rom)
      /\ getr regs' 13 = Z_to_bv 64 (2 ^ 64 - 65)
      /\ (forall r : reg, r <> 13 -> getr regs' r = getr regs r).
  Proof.
    intros regs m H10 H12. pose proof (cp_dn _ _ _ _ _ _ H) as Hdn.
    eexists. split.
    - mstep ltac:(exact (step_xori _ _ _ _ _ _ _ _ _ F_53ed8 eq_refl D_53ed8)). gr. rewrite H10. rewrite v_not_zbv by lia.
      mstep ltac:(eapply (step_bltu_ft _ _ _ _ _ _ _ _ _ F_53edc eq_refl D_53edc); gr; rewrite ?H12; br_lt).
      mstep ltac:(exact (step_addi _ _ _ _ _ _ _ _ _ F_53ee0 eq_refl D_53ee0)). rewrite getr_zero. zn.
      apply mst_refl.
    - gr. split; [rewrite <- (zbv_wrap_add (-65)); apply (f_equal (Z_to_bv 64)); lia|]. intros r Hr. repeat (rewrite getr_other by congruence). reflexivity.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  #[using="d bs H Hn Hs"] Lemma rp_pre_s : forall m b1, sfr m ->
    (65 <= n)%Z -> mem (Z_to_bv 64 (SB + (s + n - 1) / 8)) = Some b1 ->
    (bv_unsigned b1 = 0%Z \/ ((s + n - 1) mod 8 < bv_unsigned b1 < 8)%Z) ->
    rpH m s n (usp - 2144) b1.
  Proof.
    intros m b1 F Hn65 L1 Hb1. pose proof Hsp. pose proof SB_val. pose proof (cp_sn _ _ _ _ _ _ H).
    pose proof (cp_shs _ _ _ _ _ _ H ltac:(lia)) as Hshd. unfold CP_FRAME in Hshd.
    pose proof (Z.div_mod (s + n - 1) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (s + n - 1) 8 ltac:(lia)).
    pose proof F as (F1 & F2 & F3).
    constructor.
    - lia.
    - exact Hs.
    - apply (cp_rngs _ _ _ _ _ _ H). lia.
    - lia.
    - lia.
    - intros g Hg. rewrite (sfr_below m) by (first [exact F | rewrite zbv_u by lia; unfold CP_FRAME; lia]). apply (cp_zeros _ _ _ _ _ _ H); lia.
    - rewrite (sfr_below m) by (first [exact F | rewrite zbv_u by lia; unfold CP_FRAME; lia]). exact L1.
    - exact Hb1.
    - intros a Ha. apply F2. apply (cp_stk _ _ _ _ _ _ H). unfold CP_FRAME. lia.
    - exact (proj1 (cells_sfr m F)).
  Qed.

  #[using="s bs H Hn Hd"] Lemma rp_pre_d : forall m b1, sfr m ->
    (65 <= n)%Z -> mem (Z_to_bv 64 (SB + (d + n - 1) / 8)) = Some b1 ->
    (bv_unsigned b1 = 0%Z \/ ((d + n - 1) mod 8 < bv_unsigned b1 < 8)%Z) ->
    rpH m d n (usp - 2144) b1.
  Proof.
    intros m b1 F Hn65 L1 Hb1. pose proof Hsp. pose proof SB_val. pose proof (cp_dn _ _ _ _ _ _ H).
    pose proof (cp_shd _ _ _ _ _ _ H ltac:(lia)) as Hshd. unfold CP_FRAME in Hshd.
    pose proof (Z.div_mod (d + n - 1) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (d + n - 1) 8 ltac:(lia)).
    pose proof F as (F1 & F2 & F3).
    constructor.
    - lia.
    - exact Hd.
    - apply (cp_rngd _ _ _ _ _ _ H). lia.
    - lia.
    - lia.
    - intros g Hg. rewrite (sfr_below m) by (first [exact F | rewrite zbv_u by lia; unfold CP_FRAME; lia]). apply (cp_zerod _ _ _ _ _ _ H); lia.
    - rewrite (sfr_below m) by (first [exact F | rewrite zbv_u by lia; unfold CP_FRAME; lia]). exact L1.
    - exact Hb1.
    - intros a Ha. apply F2. apply (cp_stk _ _ _ _ _ _ H). unfold CP_FRAME. lia.
    - exact (proj1 (cells_sfr m F)).
  Qed.

  Definition l_clob (r : reg) : bool :=
    (cp_clob r || bv_eqb r 1 || bv_eqb r 9 || bv_eqb r 18 || bv_eqb r 19 || bv_eqb r 21 || bv_eqb r 23)%bool.

  #[using="bs H Hn Hd Hs"] Lemma blk_RL : forall regs m,
    sfr m -> (65 <= n)%Z ->
    getr regs 13 = Z_to_bv 64 (2 ^ 64 - 65) -> getr regs 22 = Z_to_bv 64 (n - 65) ->
    getr regs 10 = Z_to_bv 64 d -> getr regs 11 = Z_to_bv 64 s -> getr regs 12 = Z_to_bv 64 n ->
    getr regs 2 = Z_to_bv 64 (usp - 2144) ->
    exists regs' m',
      msteps SEGS (mkst regs (0x53e9c : word) m rom) (mkst regs' (0x53ed8 : word) m' rom)
      /\ sfr m'
      /\ getr regs' 10 = Z_to_bv 64 d /\ getr regs' 11 = Z_to_bv 64 s /\ getr regs' 12 = Z_to_bv 64 n
      /\ getr regs' 2 = Z_to_bv 64 (usp - 2144) /\ getr regs' 22 = getr regs 22 /\ getr regs' 19 = getr regs 19
      /\ (forall r, l_clob r = false -> getr regs' r = getr regs r).
  Proof.
    intros regs m F Hn65 H13 H22 H10 H11 H12 H2. pose proof Hsp. pose proof (cp_sn _ _ _ _ _ _ H). pose proof (cp_dn _ _ _ _ _ _ H). pose proof Hd. pose proof Hs. pose proof Hn.
    destruct (cp_lasts _ _ _ _ _ _ H ltac:(lia)) as (b1 & L1 & Hb1).
    evar (rr : bvmap 5 word).
    edestruct (as_region_is_poisoned m rom s n (usp - 2144) b1 (rp_pre_s m b1 F Hn65 L1 Hb1) rr (0x541d4 : word) ret_ok_cc5a4)
      as (r1 & M1 & R10 & R2 & R1 & K1); cycle -1.
    { eexists. eexists. split; [|split; [|split; [|split; [|split; [|split; [|split; [|split]]]]]]].
      - mstep ltac:(eapply (step_bgeu_tk _ _ _ _ _ _ _ _ _ F_53e9c eq_refl D_53e9c); gr; rewrite ?H13, ?H22; br_lt).
        mstep ltac:(eapply (step_bne_tk _ _ _ _ _ _ _ _ _ F_54180 eq_refl D_54180); gr; rewrite ?H12, ?getr_zero; br_eq).
        mstep ltac:(exact (step_addi _ _ _ _ _ _ _ _ _ F_541bc eq_refl D_541bc)). gr. rewrite H10. zn. rewrite ?Z.add_0_r.
        mstep ltac:(exact (step_addi _ _ _ _ _ _ _ _ _ F_541c0 eq_refl D_541c0)). gr. rewrite H11. zn. rewrite ?Z.add_0_r.
        mstep ltac:(exact (step_addi _ _ _ _ _ _ _ _ _ F_541c4 eq_refl D_541c4)). gr. rewrite H11. zn. rewrite ?Z.add_0_r.
        mstep ltac:(exact (step_addi _ _ _ _ _ _ _ _ _ F_541c8 eq_refl D_541c8)). gr. rewrite H12. zn. rewrite ?Z.add_0_r.
        mstep ltac:(exact (step_addi _ _ _ _ _ _ _ _ _ F_541cc eq_refl D_541cc)). gr. rewrite H12. zn. rewrite ?Z.add_0_r.
        mstep ltac:(exact (step_jal_link _ _ _ _ _ _ _ _ F_541d0 eq_refl D_541d0)). rewrite lit_cc5a4.
        eapply msteps_trans; [subst rr; exact M1|].
        mstep ltac:(exact (step_addi _ _ _ _ _ _ _ _ _ F_541d4 eq_refl D_541d4)).
        rewrite (K1 23) by reflexivity. subst rr. gr. zn. rewrite ?Z.add_0_r.
        mstep ltac:(exact (step_addi _ _ _ _ _ _ _ _ _ F_541d8 eq_refl D_541d8)). gr.
        rewrite (K1 9) by reflexivity. gr. zn. rewrite ?Z.add_0_r.
        mstep ltac:(exact (step_addi _ _ _ _ _ _ _ _ _ F_541dc eq_refl D_541dc)). gr. rewrite R10. zn.
        mstep ltac:(exact (step_addi _ _ _ _ _ _ _ _ _ F_541e0 eq_refl D_541e0)). gr.
        rewrite (K1 21) by reflexivity. gr. zn. rewrite ?Z.add_0_r.
        mstep ltac:(eapply (step_beq_tk _ _ _ _ _ _ _ _ _ F_541e4 eq_refl D_541e4); gr; rewrite ?getr_zero; br_eq).
        apply mst_refl.
      - apply sfr_rp. exact F.
      - subst rr. gr. reflexivity.
      - subst rr. gr. reflexivity.
      - subst rr. gr. reflexivity.
      - subst rr. gr. exact R2.
      - subst rr. gr. rewrite (K1 22) by reflexivity. gr. reflexivity.
      - subst rr. gr. rewrite (K1 19) by reflexivity. gr. reflexivity.
      - subst rr. intros r Hr. unfold l_clob, cp_clob in Hr.
        repeat (rewrite getr_other by (intros ->; cbn in Hr; discriminate)).
        rewrite K1 by (unfold rp_clob; repeat match type of Hr with (?a || ?b)%bool = false =>
                         apply orb_false_iff in Hr; destruct Hr as [Hr ?] end;
                       repeat match goal with Hb : bv_eqb r ?k = false |- _ => rewrite Hb end; reflexivity).
        repeat (rewrite getr_other by (intros ->; cbn in Hr; discriminate)). reflexivity. }
    all: subst rr; gr; try reflexivity; try assumption.
  Qed.

  #[using="bs H Hn Hd Hs"] Lemma blk_WL : forall regs m,
    sfr m -> (65 <= n)%Z ->
    getr regs 13 = Z_to_bv 64 (2 ^ 64 - 65) -> getr regs 22 = Z_to_bv 64 (n - 65) ->
    getr regs 10 = Z_to_bv 64 d -> getr regs 11 = Z_to_bv 64 s -> getr regs 12 = Z_to_bv 64 n ->
    getr regs 2 = Z_to_bv 64 (usp - 2144) ->
    exists regs' m',
      msteps SEGS (mkst regs (0x53ee4 : word) m rom) (mkst regs' (0x53f20 : word) m' rom)
      /\ sfr m'
      /\ getr regs' 10 = Z_to_bv 64 d /\ getr regs' 11 = Z_to_bv 64 s /\ getr regs' 12 = Z_to_bv 64 n
      /\ getr regs' 2 = Z_to_bv 64 (usp - 2144)
      /\ (forall r, l_clob r = false -> getr regs' r = getr regs r).
  Proof.
    intros regs m F Hn65 H13 H22 H10 H11 H12 H2. pose proof Hsp. pose proof (cp_sn _ _ _ _ _ _ H). pose proof (cp_dn _ _ _ _ _ _ H). pose proof Hd. pose proof Hs. pose proof Hn.
    destruct (cp_lastd _ _ _ _ _ _ H ltac:(lia)) as (b1 & L1 & Hb1).
    evar (rr : bvmap 5 word).
    edestruct (as_region_is_poisoned m rom d n (usp - 2144) b1 (rp_pre_d m b1 F Hn65 L1 Hb1) rr (0x54274 : word) ret_ok_cc644)
      as (r1 & M1 & R10 & R2 & R1 & K1); cycle -1.
    { eexists. eexists. split; [|split; [|split; [|split; [|split; [|split]]]]].
      - mstep ltac:(eapply (step_bgeu_tk _ _ _ _ _ _ _ _ _ F_53ee4 eq_refl D_53ee4); gr; rewrite ?H13, ?H22; br_lt).
        mstep ltac:(eapply (step_bne_tk _ _ _ _ _ _ _ _ _ F_54034 eq_refl D_54034); gr; rewrite ?H12, ?getr_zero; br_eq).
        mstep ltac:(exact (step_addi _ _ _ _ _ _ _ _ _ F_54260 eq_refl D_54260)). gr. rewrite H10. zn. rewrite ?Z.add_0_r.
        mstep ltac:(exact (step_addi _ _ _ _ _ _ _ _ _ F_54264 eq_refl D_54264)). gr. rewrite H11. zn. rewrite ?Z.add_0_r.
        mstep ltac:(exact (step_addi _ _ _ _ _ _ _ _ _ F_54268 eq_refl D_54268)). gr. rewrite H12. zn. rewrite ?Z.add_0_r.
        mstep ltac:(exact (step_addi _ _ _ _ _ _ _ _ _ F_5426c eq_refl D_5426c)). gr. rewrite H12. zn. rewrite ?Z.add_0_r.
        mstep ltac:(exact (step_jal_link _ _ _ _ _ _ _ _ F_54270 eq_refl D_54270)). rewrite lit_cc644.
        eapply msteps_trans; [subst rr; exact M1|].
        mstep ltac:(exact (step_addi _ _ _ _ _ _ _ _ _ F_54274 eq_refl D_54274)).
        rewrite (K1 21) by reflexivity. subst rr. gr. zn. rewrite ?Z.add_0_r.
        mstep ltac:(exact (step_addi _ _ _ _ _ _ _ _ _ F_54278 eq_refl D_54278)). gr.
        rewrite (K1 18) by reflexivity. gr. zn. rewrite ?Z.add_0_r.
        mstep ltac:(exact (step_addi _ _ _ _ _ _ _ _ _ F_5427c eq_refl D_5427c)). gr. rewrite R10. zn.
        mstep ltac:(exact (step_addi _ _ _ _ _ _ _ _ _ F_54280 eq_refl D_54280)). gr.
        rewrite (K1 9) by reflexivity. gr. zn. rewrite ?Z.add_0_r.
        mstep ltac:(eapply (step_beq_tk _ _ _ _ _ _ _ _ _ F_54284 eq_refl D_54284); gr; rewrite ?getr_zero; br_eq).
        apply mst_refl.
      - apply sfr_rp. exact F.
      - subst rr. gr. reflexivity.
      - subst rr. gr. reflexivity.
      - subst rr. gr. reflexivity.
      - subst rr. gr. exact R2.
      - subst rr. intros r Hr. unfold l_clob, cp_clob in Hr.
        repeat (rewrite getr_other by (intros ->; cbn in Hr; discriminate)).
        rewrite K1 by (unfold rp_clob; repeat match type of Hr with (?a || ?b)%bool = false =>
                         apply orb_false_iff in Hr; destruct Hr as [Hr ?] end;
                       repeat match goal with Hb : bv_eqb r ?k = false |- _ => rewrite Hb end; reflexivity).
        repeat (rewrite getr_other by (intros ->; cbn in Hr; discriminate)). reflexivity. }
    all: subst rr; gr; try reflexivity; try assumption.
  Qed.

  Let g0s : Z := (s / 8)%Z.
  Let g1s : Z := ((s + n - 1) / 8)%Z.
  Let g0d : Z := (d / 8)%Z.
  Let g1d : Z := ((d + n - 1) / 8)%Z.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition rq_clob (r : reg) : bool :=
    (bv_eqb r 13 || bv_eqb r 14 || bv_eqb r 15 || bv_eqb r 16 || bv_eqb r 17 || bv_eqb r 21)%bool.

  #[using="mem d bs H Hd Hs g0d g1d"] Lemma rqfacts : (0 < n)%Z ->
    (8 * g0s <= s < 8 * g0s + 8)%Z /\ (8 * g1s <= s + n - 1 < 8 * g1s + 8)%Z
    /\ ((s + n - 1) mod 8 = s + n - 1 - 8 * g1s)%Z
    /\ (SB + g1s + 8 < usp - 2216)%Z /\ (g0s <= g1s)%Z /\ SB = 0x7fff8000%Z.
  Proof.
    intros Hn0. pose proof (cp_shs _ _ _ _ _ _ H Hn0) as Hshd. unfold CP_FRAME in Hshd. pose proof SB_val.
    pose proof Hd. pose proof Hs. unfold g0s, g1s in *.
    pose proof (Z.div_mod s 8 ltac:(lia)). pose proof (Z.mod_pos_bound s 8 ltac:(lia)).
    pose proof (Z.div_mod (s + n - 1) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (s + n - 1) 8 ltac:(lia)).
    assert (s / 8 <= (s + n - 1) / 8)%Z by (apply Z.div_le_mono; lia).
    lia.
  Qed.

  (* [comment removed for export] *)
  #[using="d bs H Hn Hd Hs g0d g1d"] Lemma blk_RQ1 : forall regs m, sfr m ->
    (1 <= n <= 64)%Z ->
    getr regs 13 = Z_to_bv 64 (2 ^ 64 - 65) -> getr regs 22 = Z_to_bv 64 (n - 65) ->
    getr regs 11 = Z_to_bv 64 s -> getr regs 21 = Z_to_bv 64 (s + n) ->
    exists regs' (w : word),
      msteps SEGS (mkst regs (0x53e9c : word) m rom) (mkst regs' (0x53ed4 : word) m rom)
      /\ getr regs' 13 = Z_to_bv 64 (SB + g0s) /\ getr regs' 14 = Z_to_bv 64 (SB + g1s)
      /\ getr regs' 21 = Z_to_bv 64 (s + n - 1) /\ getr regs' 15 = w
      /\ (forall r, rq_clob r = false -> getr regs' r = getr regs r).
  Proof.
    intros regs m F Hn64 H13 H22 HX HE. pose proof Hsp as HU. pose proof (cp_dn _ _ _ _ _ _ H) as Hdn. pose proof (cp_sn _ _ _ _ _ _ H) as Hsn.
    pose proof Hd. pose proof Hs.
    destruct (rqfacts ltac:(lia)) as (D0 & D1 & DM & Dshd & D01 & HSB).
    pose proof (cells_sfr m F) as ((C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8) & G1 & B1 & G2).
    destruct (cp_w1s _ _ _ _ _ _ H ltac:(lia)) as [w1 W1]. destruct (cp_w2s _ _ _ _ _ _ H ltac:(lia)) as [w2 W2].
    pose proof (Z.div_mod (SB + g0s) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (SB + g0s) 8 ltac:(lia)).
    pose proof (Z.div_mod (SB + g1s) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (SB + g1s) 8 ltac:(lia)).
    assert (W1c : cell m ((SB + g0s) / 8 * 8) (bv_unsigned w1)).
    { unfold cell. rewrite zbv_self. rewrite (rdn_sfr_below m) by (first [exact F | cbn; unfold CP_FRAME; (ltac2:(LK.k [@Hn64; @H0; @H1; @D0; @D1; @HSB; @H2; @H3; @Dshd]); lia)]). exact W1. }
    assert (W2c : cell m ((SB + g1s) / 8 * 8) (bv_unsigned w2)).
    { unfold cell. rewrite zbv_self. rewrite (rdn_sfr_below m) by (first [exact F | cbn; unfold CP_FRAME; (ltac2:(LK.k [@Hn64; @H0; @H1; @D0; @D1; @HSB; @H4; @H5; @Dshd]); lia)]). exact W2. }
    replace (Z_to_bv 64 (n - 65)) with (Z_to_bv 64 (2 ^ 64 - 65 + n)) in H22
      by (rewrite <- (zbv_wrap_add (n - 65)); apply (f_equal (Z_to_bv 64)); lia).
    eexists. eexists. split.
    - mstep ltac:(eapply (step_bgeu_ft _ _ _ _ _ _ _ _ _ F_53e9c eq_refl D_53e9c); gr; rewrite ?H13, ?H22; br_lt).
      mstep ltac:(eapply (step_auipc_at _ _ _ _ _ _ _ _ (Z_to_bv 64 0xaaea0) F_53ea0 eq_refl D_53ea0);
                   [reflexivity | apply bv_eq; vm_compute; reflexivity]).
      mld F_53ea4 D_53ea4 0xb35f8%Z C1 HX.
      mld F_53ea8 D_53ea8 SB C2 HX.
      mstep ltac:(exact (step_addi _ _ _ _ _ _ _ _ _ F_53eac eq_refl D_53eac)). gr. rewrite HE. zn.
      replace (s + n + -1)%Z with (s + n - 1)%Z by lia.
      mstep ltac:(exact (PropExec.step_srli _ _ _ _ _ _ _ _ _ F_53eb0 eq_refl D_53eb0)). gr. rewrite HX, (v_srli_3 s) by (ltac2:(LK.k [@Hs; @Hn64; @Hsn; @H0; @H1; @D0; @D1; @HSB]); lia).
      mstep ltac:(exact (PropExec.step_srli _ _ _ _ _ _ _ _ _ F_53eb4 eq_refl D_53eb4)). gr. rewrite (v_srli_3 (s + n - 1)) by (ltac2:(LK.k [@Hn64; @Hsn; @H0; @H1; @D0; @D1; @DM; @D01; @HSB]); lia).
      mstep ltac:(exact (step_add _ _ _ _ _ _ _ _ _ F_53eb8 eq_refl D_53eb8)). gr. rewrite v_add_zbv by (ltac2:(LK.k [@H0; @H1; @HSB; @Hn64; @Hsn; @D0]); lia).
      mstep ltac:(exact (step_add _ _ _ _ _ _ _ _ _ F_53ebc eq_refl D_53ebc)). gr. rewrite v_add_zbv by (ltac2:(LK.k [@H0; @H1; @HSB; @Hn64; @Hsn; @D0; @D1; @DM]); lia).
      mstep ltac:(exact (step_andi _ _ _ _ _ _ _ _ _ F_53ec0 eq_refl D_53ec0)). gr. rewrite v_andi_m8 by (ltac2:(LK.k [@Hn64; @Hsn; @H0; @H1; @D0; @D1; @HSB]); lia).
      mstep ltac:(exact (step_andi _ _ _ _ _ _ _ _ _ F_53ec4 eq_refl D_53ec4)). gr. rewrite v_andi_m8 by (ltac2:(LK.k [@Hn64; @Hsn; @H0; @H1; @D0; @D1; @DM; @HSB]); lia).
      fold g0s. fold g1s.
      mld F_53ec8 D_53ec8 (bv_unsigned w1) W1c HX.
      mld F_53ecc D_53ecc (bv_unsigned w2) W2c HX.
      mstep ltac:(exact (step_or _ _ _ _ _ _ _ _ _ F_53ed0 eq_refl D_53ed0)). gr.
      apply mst_refl.
    - gr. repeat split; try reflexivity.
      intros r Hr. unfold rq_clob in Hr.
      repeat (rewrite getr_other by (intros ->; cbn in Hr; discriminate)). reflexivity.
  Qed.

  (* [comment removed for export] *)
  #[using="d bs H Hd Hs g0s g0d g1d"] Lemma blk_RQ2a : forall regs m, sfr m ->
    (1 <= n <= 64)%Z ->
    getr regs 14 = Z_to_bv 64 (SB + g1s) -> getr regs 21 = Z_to_bv 64 (s + n - 1) ->
    exists regs',
      msteps SEGS (mkst regs (0x54188 : word) m rom) (mkst regs' (0x541a0 : word) m rom)
      /\ getr regs' 15 = Z_to_bv 64 0
      /\ (forall r, rq_clob r = false -> getr regs' r = getr regs r)
      /\ getr regs' 13 = getr regs 13 /\ getr regs' 14 = getr regs 14.
  Proof.
    intros regs m F Hn64 H14 HE. pose proof Hsp as HU. pose proof (cp_dn _ _ _ _ _ _ H) as Hdn. pose proof (cp_sn _ _ _ _ _ _ H) as Hsn.
    pose proof Hd. pose proof Hs.
    destruct (rqfacts ltac:(lia)) as (D0 & D1 & DM & Dshd & D01 & HSB).
    destruct (cp_lasts _ _ _ _ _ _ H ltac:(lia)) as (b1 & L1 & Hb1). pose proof (bv_unsigned_in_range 8 b1) as Hb1r.
    assert (L1' : rdn SEGS m (Z_to_bv 64 (SB + g1s)) 1 = Some [b1]).
    { apply rdn1. rewrite (sfr_below m) by (first [exact F | rewrite zbv_u by lia; unfold CP_FRAME; lia]). exact L1. }
    assert (Hsg : bv_signed b1 = bv_unsigned b1) by (apply bv_signed_small8; lia).
    assert (AND0 : v_and (Z_to_bv 64 0) (v_xori (Z_to_bv 64 0) 1) = Z_to_bv 64 0) by (apply bv_eq; vm_compute; reflexivity).
    assert (AND1 : v_and (Z_to_bv 64 1) (v_xori (Z_to_bv 64 1) 1) = Z_to_bv 64 0) by (apply bv_eq; vm_compute; reflexivity).
    destruct Hb1 as [Hz | Hpart].
    - eexists. split; [|split; [|split; [|split]]].
      + mstep ltac:(eapply (@step_lb _ _ _ _ _ _ _ _ _ _ b1 F_54188 eq_refl D_54188);
                     gr; rewrite ?H14; imm_norm; zn; rewrite ?Z.add_0_r; exact L1').
        unfold v_lb. rewrite Hsg, Hz.
        mstep ltac:(exact (step_andi _ _ _ _ _ _ _ _ _ F_5418c eq_refl D_5418c)). gr. rewrite HE, v_andi_7 by lia.
        mstep ltac:(exact (step_sltu _ _ _ _ _ _ _ _ _ F_54190 eq_refl D_54190)). gr. rewrite getr_zero.
        unfold v_sltu. rewrite c_ltu_zbv by lia. rewrite (proj2 (Z.ltb_ge 0 0)) by lia.
        mstep ltac:(exact (step_slt _ _ _ _ _ _ _ _ _ F_54194 eq_refl D_54194)). gr.
        unfold v_slt. rewrite c_lts_zbv by lia. rewrite (proj2 (Z.ltb_ge _ 0)) by lia.
        mstep ltac:(exact (step_xori _ _ _ _ _ _ _ _ _ F_54198 eq_refl D_54198)). gr.
        mstep ltac:(exact (step_and _ _ _ _ _ _ _ _ _ F_5419c eq_refl D_5419c)). gr. rewrite AND0.
        apply mst_refl.
      + gr. reflexivity.
      + intros r Hr. unfold rq_clob in Hr. repeat (rewrite getr_other by (intros ->; cbn in Hr; discriminate)). reflexivity.
      + gr. reflexivity.
      + gr. reflexivity.
    - eexists. split; [|split; [|split; [|split]]].
      + mstep ltac:(eapply (@step_lb _ _ _ _ _ _ _ _ _ _ b1 F_54188 eq_refl D_54188);
                     gr; rewrite ?H14; imm_norm; zn; rewrite ?Z.add_0_r; exact L1').
        unfold v_lb. rewrite Hsg. rewrite <- (zbv_self (Z_to_bv 64 (bv_unsigned b1))). rewrite (zbv_u (bv_unsigned b1)) by lia.
        mstep ltac:(exact (step_andi _ _ _ _ _ _ _ _ _ F_5418c eq_refl D_5418c)). gr. rewrite HE, v_andi_7 by lia.
        mstep ltac:(exact (step_sltu _ _ _ _ _ _ _ _ _ F_54190 eq_refl D_54190)). gr. rewrite getr_zero.
        unfold v_sltu. rewrite c_ltu_zbv by lia. rewrite (proj2 (Z.ltb_lt 0 _)) by lia.
        mstep ltac:(exact (step_slt _ _ _ _ _ _ _ _ _ F_54194 eq_refl D_54194)). gr.
        unfold v_slt. rewrite c_lts_zbv by lia. rewrite (proj2 (Z.ltb_lt _ _)) by lia.
        mstep ltac:(exact (step_xori _ _ _ _ _ _ _ _ _ F_54198 eq_refl D_54198)). gr.
        mstep ltac:(exact (step_and _ _ _ _ _ _ _ _ _ F_5419c eq_refl D_5419c)). gr. rewrite AND1.
        apply mst_refl.
      + gr. reflexivity.
      + intros r Hr. unfold rq_clob in Hr. repeat (rewrite getr_other by (intros ->; cbn in Hr; discriminate)). reflexivity.
      + gr. reflexivity.
      + gr. reflexivity.
  Qed.

  (* [comment removed for export] *)
  #[using="d bs H Hd Hs g0d g1d"] Lemma rq_loop : forall (i : nat) regs m g, sfr m ->
    (1 <= n <= 64)%Z ->
    getr regs 13 = Z_to_bv 64 (SB + g) -> getr regs 14 = Z_to_bv 64 (SB + g1s) -> getr regs 15 = Z_to_bv 64 0 ->
    (g0s <= g < g1s)%Z -> Z.of_nat i = (g1s - g)%Z ->
    exists regs',
      msteps SEGS (mkst regs (0x541a4 : word) m rom) (mkst regs' (0x541b4 : word) m rom)
      /\ getr regs' 15 = Z_to_bv 64 0
      /\ (forall r, rq_clob r = false -> getr regs' r = getr regs r).
  Proof.
    pose proof Hsp as HU. pose proof (cp_dn _ _ _ _ _ _ H) as Hdn. pose proof (cp_sn _ _ _ _ _ _ H) as Hsn. pose proof Hd. pose proof Hs.
    induction i as [|i IH]; intros regs m g F Hn64 H13 H14 H15 Hg Hi; [lia|].
    destruct (rqfacts ltac:(lia)) as (D0 & D1 & DM & Dshd & D01 & HSB).
    assert (Z0 : rdn SEGS m (Z_to_bv 64 (SB + g)) 1 = Some [Z_to_bv 8 0]).
    { apply rdn1. rewrite (sfr_below m) by (first [exact F | rewrite zbv_u by lia; unfold CP_FRAME; lia]).
      apply (cp_zeros _ _ _ _ _ _ H); unfold g0s, g1s in *; lia. }
    destruct (Z.eq_dec (g + 1) g1s) as [Heq | Hne].
    - eexists. split; [|split].
      + mstep ltac:(eapply (@step_lbu _ _ _ _ _ _ _ _ _ _ (Z_to_bv 8 0) F_541a4 eq_refl D_541a4);
                     gr; rewrite ?H13; imm_norm; zn; rewrite ?Z.add_0_r; exact Z0).
        change (bv_unsigned (Z_to_bv 8 0)) with 0%Z.
        mstep ltac:(exact (step_addi _ _ _ _ _ _ _ _ _ F_541a8 eq_refl D_541a8)). gr. rewrite H13. zn.
        mstep ltac:(exact (step_or _ _ _ _ _ _ _ _ _ F_541ac eq_refl D_541ac)). gr. rewrite H15, v_or_zero.
        mstep ltac:(eapply (step_bne_ft _ _ _ _ _ _ _ _ _ F_541b0 eq_refl D_541b0); gr; rewrite ?H14; br_eq).
        apply mst_refl.
      + gr. reflexivity.
      + intros r Hr. unfold rq_clob in Hr. repeat (rewrite getr_other by (intros ->; cbn in Hr; discriminate)). reflexivity.
    - evar (rr : bvmap 5 word).
      edestruct (IH rr m (g + 1)%Z F Hn64) as (r2 & M2 & R15 & K2); cycle -1.
      { exists r2. split; [|split].
        + mstep ltac:(eapply (@step_lbu _ _ _ _ _ _ _ _ _ _ (Z_to_bv 8 0) F_541a4 eq_refl D_541a4);
                       gr; rewrite ?H13; imm_norm; zn; rewrite ?Z.add_0_r; exact Z0).
          change (bv_unsigned (Z_to_bv 8 0)) with 0%Z.
          mstep ltac:(exact (step_addi _ _ _ _ _ _ _ _ _ F_541a8 eq_refl D_541a8)). gr. rewrite H13. zn.
          mstep ltac:(exact (step_or _ _ _ _ _ _ _ _ _ F_541ac eq_refl D_541ac)). gr. rewrite H15, v_or_zero.
          mstep ltac:(eapply (step_bne_tk _ _ _ _ _ _ _ _ _ F_541b0 eq_refl D_541b0); gr; rewrite ?H14; br_eq).
          subst rr. exact M2.
        + exact R15.
        + intros r Hr. rewrite (K2 r Hr). subst rr. unfold rq_clob in Hr.
          repeat (rewrite getr_other by (intros ->; cbn in Hr; discriminate)). reflexivity. }
      all: subst rr; gr; try reflexivity; try assumption; try lia.
      apply (f_equal (Z_to_bv 64)). lia.
  Qed.

  (* [comment removed for export] *)
  #[using="d bs H Hd Hs g0d g1d"] Lemma blk_RQ2b : forall regs m, sfr m ->
    (1 <= n <= 64)%Z ->
    getr regs 13 = Z_to_bv 64 (SB + g0s) -> getr regs 14 = Z_to_bv 64 (SB + g1s) -> getr regs 15 = Z_to_bv 64 0 ->
    exists regs',
      msteps SEGS (mkst regs (0x541a0 : word) m rom) (mkst regs' (0x53ed8 : word) m rom)
      /\ (forall r, rq_clob r = false -> getr regs' r = getr regs r).
  Proof.
    intros regs m F Hn64 H13 H14 H15. pose proof Hsp as HU. pose proof (cp_dn _ _ _ _ _ _ H) as Hdn. pose proof (cp_sn _ _ _ _ _ _ H) as Hsn.
    pose proof Hd. pose proof Hs.
    destruct (rqfacts ltac:(lia)) as (D0 & D1 & DM & Dshd & D01 & HSB).
    assert (ANDI0 : v_andi (Z_to_bv 64 0) 255 = Z_to_bv 64 0) by (apply bv_eq; vm_compute; reflexivity).
    destruct (Z.eq_dec g0s g1s) as [Heq | Hne].
    - eexists. split.
      + mstep ltac:(eapply (step_bgeu_tk _ _ _ _ _ _ _ _ _ F_541a0 eq_refl D_541a0); gr; rewrite ?H13, ?H14; br_lt).
        mstep ltac:(exact (step_andi _ _ _ _ _ _ _ _ _ F_541b4 eq_refl D_541b4)). gr. rewrite H15, ANDI0.
        mstep ltac:(eapply (step_beq_tk _ _ _ _ _ _ _ _ _ F_541b8 eq_refl D_541b8); gr; rewrite ?getr_zero; br_eq).
        apply mst_refl.
      + intros r Hr. unfold rq_clob in Hr. repeat (rewrite getr_other by (intros ->; cbn in Hr; discriminate)). reflexivity.
    - evar (rr : bvmap 5 word).
      edestruct (rq_loop (Z.to_nat (g1s - g0s)) rr m g0s F Hn64) as (r2 & M2 & R15 & K2); cycle -1.
      { eexists. split.
        + mstep ltac:(eapply (step_bgeu_ft _ _ _ _ _ _ _ _ _ F_541a0 eq_refl D_541a0); gr; rewrite ?H13, ?H14; br_lt).
          eapply msteps_trans; [subst rr; exact M2|].
          mstep ltac:(exact (step_andi _ _ _ _ _ _ _ _ _ F_541b4 eq_refl D_541b4)). rewrite R15, ANDI0.
          mstep ltac:(eapply (step_beq_tk _ _ _ _ _ _ _ _ _ F_541b8 eq_refl D_541b8); gr; rewrite ?getr_zero; br_eq).
          apply mst_refl.
        + intros r Hr. unfold rq_clob in Hr. repeat (rewrite getr_other by (intros ->; cbn in Hr; discriminate)).
          rewrite (K2 r) by exact Hr. subst rr. reflexivity. }
      all: subst rr; try assumption; try lia.
  Qed.

  (* [comment removed for export] *)
  #[using="d bs H Hn Hd Hs g0s g1s g0d g1d"] Lemma blk_RQ : forall regs m, sfr m ->
    (1 <= n <= 64)%Z ->
    getr regs 13 = Z_to_bv 64 (2 ^ 64 - 65) -> getr regs 22 = Z_to_bv 64 (n - 65) ->
    getr regs 11 = Z_to_bv 64 s -> getr regs 21 = Z_to_bv 64 (s + n) ->
    exists regs',
      msteps SEGS (mkst regs (0x53e9c : word) m rom) (mkst regs' (0x53ed8 : word) m rom)
      /\ (forall r, rq_clob r = false -> getr regs' r = getr regs r).
  Proof.
    intros regs m F Hn64 H13 H22 HX HE.
    destruct (blk_RQ1 regs m F Hn64 H13 H22 HX HE) as (q1 & w & M1 & A13 & A14 & AE & A15 & K1).
    pose proof (bv_unsigned_in_range 64 w) as Hw. change (bv_modulus 64) with (2 ^ 64)%Z in Hw.
    destruct (bv_eq_dec _ w (Z_to_bv 64 0)) as [-> | NZ].
    - exists q1. split.
      + eapply msteps_trans; [exact M1|].
        mstep ltac:(eapply (step_bne_ft _ _ _ _ _ _ _ _ _ F_53ed4 eq_refl D_53ed4); gr; rewrite ?A15, ?getr_zero; br_eq).
        apply mst_refl.
      + exact K1.
    - assert (NZu : bv_unsigned w <> 0%Z).
      { intros E0. apply NZ. rewrite <- (zbv_self w), E0. reflexivity. }
      destruct (blk_RQ2a q1 m F Hn64 A14 AE) as (q2 & M2 & B15 & K2 & B13 & B14).
      destruct (blk_RQ2b q2 m F Hn64) as (q3 & M3 & K3); [rewrite B13; exact A13 | rewrite B14; exact A14 | exact B15 |].
      exists q3. split.
      + eapply msteps_trans; [exact M1|].
        mstep ltac:(eapply (step_bne_tk _ _ _ _ _ _ _ _ _ F_53ed4 eq_refl D_53ed4); gr; rewrite ?A15, ?getr_zero;
                     rewrite <- (zbv_self w); br_eq).
        eapply msteps_trans; [exact M2|]. exact M3.
      + intros r Hr. rewrite (K3 r Hr), (K2 r Hr). apply K1. exact Hr.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition wq_clob (r : reg) : bool :=
    (bv_eqb r 13 || bv_eqb r 14 || bv_eqb r 15 || bv_eqb r 16 || bv_eqb r 17 || bv_eqb r 19)%bool.

  #[using="mem s bs H Hd Hs g0s g1s"] Lemma wqfacts : (0 < n)%Z ->
    (8 * g0d <= d < 8 * g0d + 8)%Z /\ (8 * g1d <= d + n - 1 < 8 * g1d + 8)%Z
    /\ ((d + n - 1) mod 8 = d + n - 1 - 8 * g1d)%Z
    /\ (SB + g1d + 8 < usp - 2216)%Z /\ (g0d <= g1d)%Z /\ SB = 0x7fff8000%Z.
  Proof.
    intros Hn0. pose proof (cp_shd _ _ _ _ _ _ H Hn0) as Hshd. unfold CP_FRAME in Hshd. pose proof SB_val.
    pose proof Hd. pose proof Hs. unfold g0d, g1d in *.
    pose proof (Z.div_mod d 8 ltac:(lia)). pose proof (Z.mod_pos_bound d 8 ltac:(lia)).
    pose proof (Z.div_mod (d + n - 1) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (d + n - 1) 8 ltac:(lia)).
    assert (d / 8 <= (d + n - 1) / 8)%Z by (apply Z.div_le_mono; lia).
    lia.
  Qed.

  (* [comment removed for export] *)
  #[using="s bs H Hn Hd Hs g0s g1s"] Lemma blk_WQ1 : forall regs m, sfr m ->
    (1 <= n <= 64)%Z ->
    getr regs 13 = Z_to_bv 64 (2 ^ 64 - 65) -> getr regs 22 = Z_to_bv 64 (n - 65) ->
    getr regs 10 = Z_to_bv 64 d -> getr regs 19 = Z_to_bv 64 (d + n) ->
    exists regs' (w : word),
      msteps SEGS (mkst regs (0x53ee4 : word) m rom) (mkst regs' (0x53f1c : word) m rom)
      /\ getr regs' 13 = Z_to_bv 64 (SB + g0d) /\ getr regs' 14 = Z_to_bv 64 (SB + g1d)
      /\ getr regs' 19 = Z_to_bv 64 (d + n - 1) /\ getr regs' 15 = w
      /\ (forall r, wq_clob r = false -> getr regs' r = getr regs r).
  Proof.
    intros regs m F Hn64 H13 H22 HX HE. pose proof Hsp as HU. pose proof (cp_dn _ _ _ _ _ _ H) as Hdn. pose proof (cp_sn _ _ _ _ _ _ H) as Hsn.
    pose proof Hd. pose proof Hs.
    destruct (wqfacts ltac:(lia)) as (D0 & D1 & DM & Dshd & D01 & HSB).
    pose proof (cells_sfr m F) as ((C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8) & G1 & B1 & G2).
    destruct (cp_w1d _ _ _ _ _ _ H ltac:(lia)) as [w1 W1]. destruct (cp_w2d _ _ _ _ _ _ H ltac:(lia)) as [w2 W2].
    pose proof (Z.div_mod (SB + g0d) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (SB + g0d) 8 ltac:(lia)).
    pose proof (Z.div_mod (SB + g1d) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (SB + g1d) 8 ltac:(lia)).
    assert (W1c : cell m ((SB + g0d) / 8 * 8) (bv_unsigned w1)).
    { unfold cell. rewrite zbv_self. rewrite (rdn_sfr_below m) by (first [exact F | cbn; unfold CP_FRAME; (ltac2:(LK.k [@Hn64; @H0; @H1; @D0; @D1; @HSB; @H2; @H3; @Dshd]); lia)]). exact W1. }
    assert (W2c : cell m ((SB + g1d) / 8 * 8) (bv_unsigned w2)).
    { unfold cell. rewrite zbv_self. rewrite (rdn_sfr_below m) by (first [exact F | cbn; unfold CP_FRAME; (ltac2:(LK.k [@Hn64; @H0; @H1; @D0; @D1; @HSB; @H4; @H5; @Dshd]); lia)]). exact W2. }
    replace (Z_to_bv 64 (n - 65)) with (Z_to_bv 64 (2 ^ 64 - 65 + n)) in H22
      by (rewrite <- (zbv_wrap_add (n - 65)); apply (f_equal (Z_to_bv 64)); lia).
    eexists. eexists. split.
    - mstep ltac:(eapply (step_bgeu_ft _ _ _ _ _ _ _ _ _ F_53ee4 eq_refl D_53ee4); gr; rewrite ?H13, ?H22; br_lt).
      mstep ltac:(eapply (step_auipc_at _ _ _ _ _ _ _ _ (Z_to_bv 64 0xaaee8) F_53ee8 eq_refl D_53ee8);
                   [reflexivity | apply bv_eq; vm_compute; reflexivity]).
      mld F_53eec D_53eec 0xb35f8%Z C1 HX.
      mld F_53ef0 D_53ef0 SB C2 HX.
      mstep ltac:(exact (step_addi _ _ _ _ _ _ _ _ _ F_53ef4 eq_refl D_53ef4)). gr. rewrite HE. zn.
      replace (d + n + -1)%Z with (d + n - 1)%Z by lia.
      mstep ltac:(exact (PropExec.step_srli _ _ _ _ _ _ _ _ _ F_53ef8 eq_refl D_53ef8)). gr. rewrite HX, (v_srli_3 d) by (ltac2:(LK.k [@Hd; @Hn64; @Hdn; @H0; @H1; @D0; @D1; @HSB]); lia).
      mstep ltac:(exact (PropExec.step_srli _ _ _ _ _ _ _ _ _ F_53efc eq_refl D_53efc)). gr. rewrite (v_srli_3 (d + n - 1)) by (ltac2:(LK.k [@Hn64; @Hdn; @H0; @H1; @D0; @D1; @DM; @D01; @HSB]); lia).
      mstep ltac:(exact (step_add _ _ _ _ _ _ _ _ _ F_53f00 eq_refl D_53f00)). gr. rewrite v_add_zbv by (ltac2:(LK.k [@H0; @H1; @HSB; @Hn64; @Hdn; @D0]); lia).
      mstep ltac:(exact (step_add _ _ _ _ _ _ _ _ _ F_53f04 eq_refl D_53f04)). gr. rewrite v_add_zbv by (ltac2:(LK.k [@H0; @H1; @HSB; @Hn64; @Hdn; @D0; @D1; @DM]); lia).
      mstep ltac:(exact (step_andi _ _ _ _ _ _ _ _ _ F_53f08 eq_refl D_53f08)). gr. rewrite v_andi_m8 by (ltac2:(LK.k [@Hn64; @Hdn; @H0; @H1; @D0; @D1; @HSB]); lia).
      mstep ltac:(exact (step_andi _ _ _ _ _ _ _ _ _ F_53f0c eq_refl D_53f0c)). gr. rewrite v_andi_m8 by (ltac2:(LK.k [@Hn64; @Hdn; @H0; @H1; @D0; @D1; @DM; @HSB]); lia).
      fold g0d. fold g1d.
      mld F_53f10 D_53f10 (bv_unsigned w1) W1c HX.
      mld F_53f14 D_53f14 (bv_unsigned w2) W2c HX.
      mstep ltac:(exact (step_or _ _ _ _ _ _ _ _ _ F_53f18 eq_refl D_53f18)). gr.
      apply mst_refl.
    - gr. repeat split; try reflexivity.
      intros r Hr. unfold wq_clob in Hr.
      repeat (rewrite getr_other by (intros ->; cbn in Hr; discriminate)). reflexivity.
  Qed.

  (* [comment removed for export] *)
  #[using="s bs H Hd Hs g0s g1s g0d"] Lemma blk_WQ2a : forall regs m, sfr m ->
    (1 <= n <= 64)%Z ->
    getr regs 14 = Z_to_bv 64 (SB + g1d) -> getr regs 19 = Z_to_bv 64 (d + n - 1) ->
    exists regs',
      msteps SEGS (mkst regs (0x5422c : word) m rom) (mkst regs' (0x54244 : word) m rom)
      /\ getr regs' 15 = Z_to_bv 64 0
      /\ (forall r, wq_clob r = false -> getr regs' r = getr regs r)
      /\ getr regs' 13 = getr regs 13 /\ getr regs' 14 = getr regs 14.
  Proof.
    intros regs m F Hn64 H14 HE. pose proof Hsp as HU. pose proof (cp_dn _ _ _ _ _ _ H) as Hdn. pose proof (cp_sn _ _ _ _ _ _ H) as Hsn.
    pose proof Hd. pose proof Hs.
    destruct (wqfacts ltac:(lia)) as (D0 & D1 & DM & Dshd & D01 & HSB).
    destruct (cp_lastd _ _ _ _ _ _ H ltac:(lia)) as (b1 & L1 & Hb1). pose proof (bv_unsigned_in_range 8 b1) as Hb1r.
    assert (L1' : rdn SEGS m (Z_to_bv 64 (SB + g1d)) 1 = Some [b1]).
    { apply rdn1. rewrite (sfr_below m) by (first [exact F | rewrite zbv_u by lia; unfold CP_FRAME; lia]). exact L1. }
    assert (Hsg : bv_signed b1 = bv_unsigned b1) by (apply bv_signed_small8; lia).
    assert (AND0 : v_and (Z_to_bv 64 0) (v_xori (Z_to_bv 64 0) 1) = Z_to_bv 64 0) by (apply bv_eq; vm_compute; reflexivity).
    assert (AND1 : v_and (Z_to_bv 64 1) (v_xori (Z_to_bv 64 1) 1) = Z_to_bv 64 0) by (apply bv_eq; vm_compute; reflexivity).
    destruct Hb1 as [Hz | Hpart].
    - eexists. split; [|split; [|split; [|split]]].
      + mstep ltac:(eapply (@step_lb _ _ _ _ _ _ _ _ _ _ b1 F_5422c eq_refl D_5422c);
                     gr; rewrite ?H14; imm_norm; zn; rewrite ?Z.add_0_r; exact L1').
        unfold v_lb. rewrite Hsg, Hz.
        mstep ltac:(exact (step_andi _ _ _ _ _ _ _ _ _ F_54230 eq_refl D_54230)). gr. rewrite HE, v_andi_7 by lia.
        mstep ltac:(exact (step_sltu _ _ _ _ _ _ _ _ _ F_54234 eq_refl D_54234)). gr. rewrite getr_zero.
        unfold v_sltu. rewrite c_ltu_zbv by lia. rewrite (proj2 (Z.ltb_ge 0 0)) by lia.
        mstep ltac:(exact (step_slt _ _ _ _ _ _ _ _ _ F_54238 eq_refl D_54238)). gr.
        unfold v_slt. rewrite c_lts_zbv by lia. rewrite (proj2 (Z.ltb_ge _ 0)) by lia.
        mstep ltac:(exact (step_xori _ _ _ _ _ _ _ _ _ F_5423c eq_refl D_5423c)). gr.
        mstep ltac:(exact (step_and _ _ _ _ _ _ _ _ _ F_54240 eq_refl D_54240)). gr. rewrite AND0.
        apply mst_refl.
      + gr. reflexivity.
      + intros r Hr. unfold wq_clob in Hr. repeat (rewrite getr_other by (intros ->; cbn in Hr; discriminate)). reflexivity.
      + gr. reflexivity.
      + gr. reflexivity.
    - eexists. split; [|split; [|split; [|split]]].
      + mstep ltac:(eapply (@step_lb _ _ _ _ _ _ _ _ _ _ b1 F_5422c eq_refl D_5422c);
                     gr; rewrite ?H14; imm_norm; zn; rewrite ?Z.add_0_r; exact L1').
        unfold v_lb. rewrite Hsg. rewrite <- (zbv_self (Z_to_bv 64 (bv_unsigned b1))). rewrite (zbv_u (bv_unsigned b1)) by lia.
        mstep ltac:(exact (step_andi _ _ _ _ _ _ _ _ _ F_54230 eq_refl D_54230)). gr. rewrite HE, v_andi_7 by lia.
        mstep ltac:(exact (step_sltu _ _ _ _ _ _ _ _ _ F_54234 eq_refl D_54234)). gr. rewrite getr_zero.
        unfold v_sltu. rewrite c_ltu_zbv by lia. rewrite (proj2 (Z.ltb_lt 0 _)) by lia.
        mstep ltac:(exact (step_slt _ _ _ _ _ _ _ _ _ F_54238 eq_refl D_54238)). gr.
        unfold v_slt. rewrite c_lts_zbv by lia. rewrite (proj2 (Z.ltb_lt _ _)) by lia.
        mstep ltac:(exact (step_xori _ _ _ _ _ _ _ _ _ F_5423c eq_refl D_5423c)). gr.
        mstep ltac:(exact (step_and _ _ _ _ _ _ _ _ _ F_54240 eq_refl D_54240)). gr. rewrite AND1.
        apply mst_refl.
      + gr. reflexivity.
      + intros r Hr. unfold wq_clob in Hr. repeat (rewrite getr_other by (intros ->; cbn in Hr; discriminate)). reflexivity.
      + gr. reflexivity.
      + gr. reflexivity.
  Qed.

  (* [comment removed for export] *)
  #[using="s bs H Hd Hs g0s g1s"] Lemma wq_loop : forall (i : nat) regs m g, sfr m ->
    (1 <= n <= 64)%Z ->
    getr regs 13 = Z_to_bv 64 (SB + g) -> getr regs 14 = Z_to_bv 64 (SB + g1d) -> getr regs 15 = Z_to_bv 64 0 ->
    (g0d <= g < g1d)%Z -> Z.of_nat i = (g1d - g)%Z ->
    exists regs',
      msteps SEGS (mkst regs (0x54248 : word) m rom) (mkst regs' (0x54258 : word) m rom)
      /\ getr regs' 15 = Z_to_bv 64 0
      /\ (forall r, wq_clob r = false -> getr regs' r = getr regs r).
  Proof.
    pose proof Hsp as HU. pose proof (cp_dn _ _ _ _ _ _ H) as Hdn. pose proof (cp_sn _ _ _ _ _ _ H) as Hsn. pose proof Hd. pose proof Hs.
    induction i as [|i IH]; intros regs m g F Hn64 H13 H14 H15 Hg Hi; [lia|].
    destruct (wqfacts ltac:(lia)) as (D0 & D1 & DM & Dshd & D01 & HSB).
    assert (Z0 : rdn SEGS m (Z_to_bv 64 (SB + g)) 1 = Some [Z_to_bv 8 0]).
    { apply rdn1. rewrite (sfr_below m) by (first [exact F | rewrite zbv_u by lia; unfold CP_FRAME; lia]).
      apply (cp_zerod _ _ _ _ _ _ H); unfold g0d, g1d in *; lia. }
    destruct (Z.eq_dec (g + 1) g1d) as [Heq | Hne].
    - eexists. split; [|split].
      + mstep ltac:(eapply (@step_lbu _ _ _ _ _ _ _ _ _ _ (Z_to_bv 8 0) F_54248 eq_refl D_54248);
                     gr; rewrite ?H13; imm_norm; zn; rewrite ?Z.add_0_r; exact Z0).
        change (bv_unsigned (Z_to_bv 8 0)) with 0%Z.
        mstep ltac:(exact (step_addi _ _ _ _ _ _ _ _ _ F_5424c eq_refl D_5424c)). gr. rewrite H13. zn.
        mstep ltac:(exact (step_or _ _ _ _ _ _ _ _ _ F_54250 eq_refl D_54250)). gr. rewrite H15, v_or_zero.
        mstep ltac:(eapply (step_bne_ft _ _ _ _ _ _ _ _ _ F_54254 eq_refl D_54254); gr; rewrite ?H14; br_eq).
        apply mst_refl.
      + gr. reflexivity.
      + intros r Hr. unfold wq_clob in Hr. repeat (rewrite getr_other by (intros ->; cbn in Hr; discriminate)). reflexivity.
    - evar (rr : bvmap 5 word).
      edestruct (IH rr m (g + 1)%Z F Hn64) as (r2 & M2 & R15 & K2); cycle -1.
      { exists r2. split; [|split].
        + mstep ltac:(eapply (@step_lbu _ _ _ _ _ _ _ _ _ _ (Z_to_bv 8 0) F_54248 eq_refl D_54248);
                       gr; rewrite ?H13; imm_norm; zn; rewrite ?Z.add_0_r; exact Z0).
          change (bv_unsigned (Z_to_bv 8 0)) with 0%Z.
          mstep ltac:(exact (step_addi _ _ _ _ _ _ _ _ _ F_5424c eq_refl D_5424c)). gr. rewrite H13. zn.
          mstep ltac:(exact (step_or _ _ _ _ _ _ _ _ _ F_54250 eq_refl D_54250)). gr. rewrite H15, v_or_zero.
          mstep ltac:(eapply (step_bne_tk _ _ _ _ _ _ _ _ _ F_54254 eq_refl D_54254); gr; rewrite ?H14; br_eq).
          subst rr. exact M2.
        + exact R15.
        + intros r Hr. rewrite (K2 r Hr). subst rr. unfold wq_clob in Hr.
          repeat (rewrite getr_other by (intros ->; cbn in Hr; discriminate)). reflexivity. }
      all: subst rr; gr; try reflexivity; try assumption; try lia.
      apply (f_equal (Z_to_bv 64)). lia.
  Qed.

  (* [comment removed for export] *)
  #[using="s bs H Hd Hs g0s g1s"] Lemma blk_WQ2b : forall regs m, sfr m ->
    (1 <= n <= 64)%Z ->
    getr regs 13 = Z_to_bv 64 (SB + g0d) -> getr regs 14 = Z_to_bv 64 (SB + g1d) -> getr regs 15 = Z_to_bv 64 0 ->
    exists regs',
      msteps SEGS (mkst regs (0x54244 : word) m rom) (mkst regs' (0x53f20 : word) m rom)
      /\ (forall r, wq_clob r = false -> getr regs' r = getr regs r).
  Proof.
    intros regs m F Hn64 H13 H14 H15. pose proof Hsp as HU. pose proof (cp_dn _ _ _ _ _ _ H) as Hdn. pose proof (cp_sn _ _ _ _ _ _ H) as Hsn.
    pose proof Hd. pose proof Hs.
    destruct (wqfacts ltac:(lia)) as (D0 & D1 & DM & Dshd & D01 & HSB).
    assert (ANDI0 : v_andi (Z_to_bv 64 0) 255 = Z_to_bv 64 0) by (apply bv_eq; vm_compute; reflexivity).
    destruct (Z.eq_dec g0d g1d) as [Heq | Hne].
    - eexists. split.
      + mstep ltac:(eapply (step_bgeu_tk _ _ _ _ _ _ _ _ _ F_54244 eq_refl D_54244); gr; rewrite ?H13, ?H14; br_lt).
        mstep ltac:(exact (step_andi _ _ _ _ _ _ _ _ _ F_54258 eq_refl D_54258)). gr. rewrite H15, ANDI0.
        mstep ltac:(eapply (step_beq_tk _ _ _ _ _ _ _ _ _ F_5425c eq_refl D_5425c); gr; rewrite ?getr_zero; br_eq).
        apply mst_refl.
      + intros r Hr. unfold wq_clob in Hr. repeat (rewrite getr_other by (intros ->; cbn in Hr; discriminate)). reflexivity.
    - evar (rr : bvmap 5 word).
      edestruct (wq_loop (Z.to_nat (g1d - g0d)) rr m g0d F Hn64) as (r2 & M2 & R15 & K2); cycle -1.
      { eexists. split.
        + mstep ltac:(eapply (step_bgeu_ft _ _ _ _ _ _ _ _ _ F_54244 eq_refl D_54244); gr; rewrite ?H13, ?H14; br_lt).
          eapply msteps_trans; [subst rr; exact M2|].
          mstep ltac:(exact (step_andi _ _ _ _ _ _ _ _ _ F_54258 eq_refl D_54258)). rewrite R15, ANDI0.
          mstep ltac:(eapply (step_beq_tk _ _ _ _ _ _ _ _ _ F_5425c eq_refl D_5425c); gr; rewrite ?getr_zero; br_eq).
          apply mst_refl.
        + intros r Hr. unfold wq_clob in Hr. repeat (rewrite getr_other by (intros ->; cbn in Hr; discriminate)).
          rewrite (K2 r) by exact Hr. subst rr. reflexivity. }
      all: subst rr; try assumption; try lia.
  Qed.

  (* [comment removed for export] *)
  #[using="s bs H Hn Hd Hs g0s g1s g0d g1d"] Lemma blk_WQ : forall regs m, sfr m ->
    (1 <= n <= 64)%Z ->
    getr regs 13 = Z_to_bv 64 (2 ^ 64 - 65) -> getr regs 22 = Z_to_bv 64 (n - 65) ->
    getr regs 10 = Z_to_bv 64 d -> getr regs 19 = Z_to_bv 64 (d + n) ->
    exists regs',
      msteps SEGS (mkst regs (0x53ee4 : word) m rom) (mkst regs' (0x53f20 : word) m rom)
      /\ (forall r, wq_clob r = false -> getr regs' r = getr regs r).
  Proof.
    intros regs m F Hn64 H13 H22 HX HE.
    destruct (blk_WQ1 regs m F Hn64 H13 H22 HX HE) as (q1 & w & M1 & A13 & A14 & AE & A15 & K1).
    pose proof (bv_unsigned_in_range 64 w) as Hw. change (bv_modulus 64) with (2 ^ 64)%Z in Hw.
    destruct (bv_eq_dec _ w (Z_to_bv 64 0)) as [-> | NZ].
    - exists q1. split.
      + eapply msteps_trans; [exact M1|].
        mstep ltac:(eapply (step_bne_ft _ _ _ _ _ _ _ _ _ F_53f1c eq_refl D_53f1c); gr; rewrite ?A15, ?getr_zero; br_eq).
        apply mst_refl.
      + exact K1.
    - assert (NZu : bv_unsigned w <> 0%Z).
      { intros E0. apply NZ. rewrite <- (zbv_self w), E0. reflexivity. }
      destruct (blk_WQ2a q1 m F Hn64 A14 AE) as (q2 & M2 & B15 & K2 & B13 & B14).
      destruct (blk_WQ2b q2 m F Hn64) as (q3 & M3 & K3); [rewrite B13; exact A13 | rewrite B14; exact A14 | exact B15 |].
      exists q3. split.
      + eapply msteps_trans; [exact M1|].
        mstep ltac:(eapply (step_bne_tk _ _ _ _ _ _ _ _ _ F_53f1c eq_refl D_53f1c); gr; rewrite ?A15, ?getr_zero;
                     rewrite <- (zbv_self w); br_eq).
        eapply msteps_trans; [exact M2|]. exact M3.
      + intros r Hr. rewrite (K3 r Hr), (K2 r Hr). apply K1. exact Hr.
  Qed.
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  #[using="d n H Hn Hd Hs g0s g1s g0d g1d"] Lemma src_m : forall m, sfr m -> rdn SEGS m (Z_to_bv 64 s) (length bs) = Some bs.
  Proof.
    intros m F. pose proof (cp_src _ _ _ _ _ _ H) as SRC. pose proof (cp_len _ _ _ _ _ _ H) as L.
    pose proof (cp_sst _ _ _ _ _ _ H) as AP. pose proof (cp_sn _ _ _ _ _ _ H). pose proof Hs. pose proof Hn. pose proof Hsp.
    destruct (Z.eq_dec n 0) as [N0|N0].
    - rewrite N0 in L. destruct bs; [reflexivity|discriminate L].
    - rewrite (rdn_sfr_out m); [exact SRC|exact F|lia|rewrite L; lia|rewrite L; unfold CP_FRAME in *; lia].
  Qed.

  #[using="H Hn Hd Hs g0s g1s g0d g1d"] Lemma mcH_m : forall m, sfr m -> AsanMemcpyBase.mcH m (Z_to_bv 64 d) (Z_to_bv 64 s) n bs.
  Proof.
    intros m F. pose proof (cp_len _ _ _ _ _ _ H) as L. pose proof (cp_sn _ _ _ _ _ _ H). pose proof (cp_dn _ _ _ _ _ _ H).
    pose proof Hs. pose proof Hd. pose proof Hn. pose proof (cp_disj _ _ _ _ _ _ H) as DJ. pose proof F as (F1 & F2 & F3).
    constructor; rewrite ?zbv_u by lia; try lia.
    - exact (src_m m F).
    - rewrite L. apply store_ok_bytes; [lia|rewrite Z2Nat.id by lia; lia|]. intros j Hj. rewrite Z2Nat.id in Hj by lia.
      apply F2. apply (cp_dok _ _ _ _ _ _ H). lia.
  Qed.

  #[using="H Hn Hd Hs g0s g1s g0d g1d"] Lemma blk_M : forall regs m, sfr m ->
    getr regs 10 = Z_to_bv 64 d -> getr regs 11 = Z_to_bv 64 s -> getr regs 12 = Z_to_bv 64 n ->
    exists regs',
      msteps SEGS (mkst regs (0x53f20 : word) m rom) (mkst regs' (0x53f2c : word) (wbytes m (Z_to_bv 64 d) bs) rom)
      /\ getr regs' 10 = Z_to_bv 64 d
      /\ (forall r, cp_clob r = false -> r <> 1 -> getr regs' r = getr regs r).
  Proof.
    intros regs m F H10 H11 H12. pose proof Hn. pose proof Hd. pose proof (cp_dn _ _ _ _ _ _ H).
    pose proof (cells_sfr m F) as (_ & _ & _ & G2).
    evar (rr : bvmap 5 word).
    edestruct (AsanMemcpy.ref_memcpy m (Z_to_bv 64 d) (Z_to_bv 64 s) n bs rom (mcH_m m F) rr (0x53f2c : word))
      as (r1 & M1 & K1); cycle -1.
    { exists r1. split; [|split].
      - mstep ltac:(eapply (step_auipc_at _ _ _ _ _ _ _ _ (Z_to_bv 64 0xacf20) F_53f20 eq_refl D_53f20);
                     [reflexivity | apply bv_eq; vm_compute; reflexivity]).
        mld F_53f24 D_53f24 0xa41ac%Z G2 H10.
        mstep ltac:(eapply (step_jalr_link _ _ _ _ _ _ _ _ _ (Z_to_bv 64 0xa41ac) F_53f28 eq_refl D_53f28);
                     [reflexivity | gr; reflexivity]).
        rewrite ?lit_cc2fc.
        match goal with |- msteps _ (mkst ?r ?pc ?mm ?ro) _ =>
          replace pc with (0xa41ac : word) by (apply bv_eq; vm_compute; reflexivity) end.
        subst rr. exact M1.
      - rewrite (K1 10) by (cbv; tauto). subst rr. gr. exact H10.
      - intros r Hr Hr1. rewrite (keeps_unclobbered _ _ r K1 Hr Hr1). subst rr. gr.
        rewrite !getr_other by (intros ->; cbn in Hr; first [discriminate | congruence]). reflexivity. }
    all: subst rr; gr; try reflexivity; try assumption; try apply ret_ok_cc2fc.
  Qed.
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Ltac mld2 F D v Hrd Hbase :=
    mstep ltac:(eapply (@step_ld _ _ _ _ _ _ _ _ _ _ _ v F eq_refl D);
                 [ gr; rewrite ?Hbase; imm_norm; zn;
                   match goal with |- rdn _ _ (Z_to_bv 64 ?a) 8 = _ =>
                     match type of Hrd with rdn _ _ (Z_to_bv 64 ?c) 8 = _ =>
                       replace a with c by lia end end; exact Hrd
                 | apply bytes_le_to_Z_8 ]).

  Definition f_clob (r : reg) : bool :=
    (bv_eqb r 1 || bv_eqb r 2 || bv_eqb r 8 || bv_eqb r 9 || bv_eqb r 18 || bv_eqb r 19
     || bv_eqb r 20 || bv_eqb r 21 || bv_eqb r 22 || bv_eqb r 23)%bool.

  #[using="d s n bs H Hret Hd Hs g0s g1s g0d g1d"] Lemma blk_E : forall regs mF,
    getr regs 2 = Z_to_bv 64 (usp - 2144) ->
    (forall a, (usp - 72 <= a)%Z -> (a + 8 <= usp)%Z -> rdn SEGS mF (Z_to_bv 64 a) 8 = rdn SEGS p9 (Z_to_bv 64 a) 8) ->
    exists regs',
      msteps SEGS (mkst regs (0x53f2c : word) mF rom) (mkst regs' ra mF rom)
      /\ getr regs' 2 = Z_to_bv 64 usp /\ getr regs' 1 = ra
      /\ getr regs' 8 = getr regs0 8 /\ getr regs' 9 = getr regs0 9 /\ getr regs' 18 = getr regs0 18
      /\ getr regs' 19 = getr regs0 19 /\ getr regs' 20 = getr regs0 20 /\ getr regs' 21 = getr regs0 21
      /\ getr regs' 22 = getr regs0 22 /\ getr regs' 23 = getr regs0 23
      /\ (forall r, f_clob r = false -> getr regs' r = getr regs r).
  Proof.
    intros regs mF H2 HF. pose proof Hsp.
    pose proof rd_ra as RD1. pose proof rd_s0 as RD8. pose proof rd_s1 as RD9. pose proof rd_s2 as RD18.
    pose proof rd_s3 as RD19. pose proof rd_s4 as RD20. pose proof rd_s5 as RD21. pose proof rd_s6 as RD22. pose proof rd_s7 as RD23.
    rewrite <- HF in RD1 by lia. rewrite <- HF in RD8 by lia. rewrite <- HF in RD9 by lia. rewrite <- HF in RD18 by lia.
    rewrite <- HF in RD19 by lia. rewrite <- HF in RD20 by lia. rewrite <- HF in RD21 by lia. rewrite <- HF in RD22 by lia.
    rewrite <- HF in RD23 by lia.
    eexists. split.
    - mstep ltac:(exact (step_addi _ _ _ _ _ _ _ _ _ F_53f2c eq_refl D_53f2c)). rewrite H2. zn.
      mld2 F_53f30 D_53f30 ra RD1 H2.
      mld2 F_53f34 D_53f34 (getr regs0 8) RD8 H2.
      mld2 F_53f38 D_53f38 (getr regs0 9) RD9 H2.
      mld2 F_53f3c D_53f3c (getr regs0 18) RD18 H2.
      mld2 F_53f40 D_53f40 (getr regs0 19) RD19 H2.
      mld2 F_53f44 D_53f44 (getr regs0 20) RD20 H2.
      mld2 F_53f48 D_53f48 (getr regs0 21) RD21 H2.
      mld2 F_53f4c D_53f4c (getr regs0 22) RD22 H2.
      mld2 F_53f50 D_53f50 (getr regs0 23) RD23 H2.
      mstep ltac:(exact (step_addi _ _ _ _ _ _ _ _ _ F_53f54 eq_refl D_53f54)). gr. zn.
      replace (usp - 2144 + 112 + 2032)%Z with usp by lia.
      eapply mst_step; [reflexivity | eapply (step_jalr_x0 _ _ _ _ _ _ _ _ ra F_53f58 eq_refl D_53f58); gr; reflexivity |].
      imm_norm. rewrite Hret. apply mst_refl.
    - gr. repeat split; try reflexivity.
      intros r Hr. unfold f_clob in Hr.
      repeat (rewrite getr_other by (intros ->; cbn in Hr; discriminate)). reflexivity.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  #[using="H Hret Hn Hd Hs g0s g1s g0d g1d"] Lemma finish : forall q mX, sfr mX ->
    getr q 10 = Z_to_bv 64 d -> getr q 11 = Z_to_bv 64 s -> getr q 12 = Z_to_bv 64 n ->
    getr q 2 = Z_to_bv 64 (usp - 2144) ->
    exists regs' m',
      msteps SEGS (mkst q (0x53f20 : word) mX rom) (mkst regs' ra m' rom)
      /\ getr regs' 10 = Z_to_bv 64 d /\ getr regs' 2 = Z_to_bv 64 usp /\ getr regs' 1 = ra
      /\ getr regs' 8 = getr regs0 8 /\ getr regs' 9 = getr regs0 9 /\ getr regs' 18 = getr regs0 18
      /\ getr regs' 19 = getr regs0 19 /\ getr regs' 20 = getr regs0 20 /\ getr regs' 21 = getr regs0 21
      /\ getr regs' 22 = getr regs0 22 /\ getr regs' 23 = getr regs0 23
      /\ (forall r, cp_clob r = false -> f_clob r = false -> getr regs' r = getr q r)
      /\ (forall x : word, (bv_unsigned x < usp - CP_FRAME \/ usp <= bv_unsigned x)%Z ->
            m' x = wbytes mem (Z_to_bv 64 d) bs x)
      /\ (forall x, mem x <> None -> m' x <> None).
  Proof.
    intros q mX F Q10 Q11 Q12 Q2. pose proof Hsp as HU. pose proof (cp_dn _ _ _ _ _ _ H) as Hdn. pose proof Hn. pose proof Hd.
    pose proof (cp_dst _ _ _ _ _ _ H) as Hdst. unfold CP_FRAME in Hdst. pose proof (cp_len _ _ _ _ _ _ H) as L.
    assert (LBS : Z.of_nat (length bs) = n) by (rewrite L; lia).
    pose proof F as (F1 & F2 & F3).
    destruct (blk_M q mX F Q10 Q11 Q12) as (q5 & M5 & R10 & K5).
    destruct (blk_E q5 (wbytes mX (Z_to_bv 64 d) bs)) as (q6 & M6 & E2 & E1 & E8 & E9 & E18 & E19 & E20 & E21 & E22 & E23 & EK).
    { rewrite (K5 2) by (reflexivity || (intros X; discriminate X)). exact Q2. }
    { intros a Ha1 Ha2.
      assert (RX : rdn SEGS mX (Z_to_bv 64 a) 8 = rdn SEGS p9 (Z_to_bv 64 a) 8).
      { apply rdn_ext; [rewrite zbv_u by lia; cbn; lia|]. intros x Hx. rewrite zbv_u in Hx by lia. cbn in Hx. apply F1. lia. }
      destruct (Z.eq_dec n 0) as [N0|N0].
      { rewrite N0 in L. destruct bs; [|discriminate L]. cbn [wbytes]. exact RX. }
      rewrite rdn_wbytes_out; [exact RX | rewrite !zbv_u by lia; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia
                             | rewrite zbv_u by lia; cbn; lia | rewrite zbv_u by lia; lia ]. }
    exists q6, (wbytes mX (Z_to_bv 64 d) bs).
    split; [eapply msteps_trans; [exact M5 | exact M6] |].
    split; [rewrite (EK 10) by reflexivity; exact R10 |].
    split; [exact E2|]. split; [exact E1|]. split; [exact E8|]. split; [exact E9|]. split; [exact E18|].
    split; [exact E19|]. split; [exact E20|]. split; [exact E21|]. split; [exact E22|]. split; [exact E23|].
    split; [|split].
    - intros r Hr Hf. rewrite (EK r Hf). apply K5; [exact Hr|]. intros ->. cbn in Hf. discriminate.
    - intros x Hx. unfold CP_FRAME in Hx. apply wbytes_agree. rewrite F1 by (unfold CP_FRAME; lia). apply p9_out. lia.
    - intros x Hx. apply wbytes_keep. apply F3. exact Hx.
  Qed.

  #[using="s n H Hret H01 H02 H010 H011 H012 Hn Hd Hs g0s g1s g0d g1d"] Theorem asan_memcpy_CP :
    exists regs' m',
      msteps SEGS (mkst regs0 (0x53e30 : word) mem rom) (mkst regs' ra m' rom)
      /\ getr regs' 10 = Z_to_bv 64 d /\ getr regs' 2 = Z_to_bv 64 usp /\ getr regs' 1 = ra
      /\ (forall r, cp_clob r = false -> getr regs' r = getr regs0 r)
      /\ (forall x : word, (bv_unsigned x < usp - CP_FRAME \/ usp <= bv_unsigned x)%Z ->
            m' x = wbytes mem (Z_to_bv 64 d) bs x)
      /\ (forall x, mem x <> None -> m' x <> None).
  Proof.
    pose proof Hsp as HU.
    destruct blk_P as (q1 & MP & P2 & P8 & P10 & P11 & P12 & P1 & PK).
    destruct (blk_B q1 P8 P10 P11 P12) as (q2 & MB & B22 & B13 & B20 & B21 & B19 & BK).
    assert (B10 : getr q2 10 = Z_to_bv 64 d) by (rewrite BK by reflexivity; exact P10).
    assert (B11 : getr q2 11 = Z_to_bv 64 s) by (rewrite BK by reflexivity; exact P11).
    assert (B12 : getr q2 12 = Z_to_bv 64 n) by (rewrite BK by reflexivity; exact P12).
    assert (B2 : getr q2 2 = Z_to_bv 64 (usp - 2144)) by (rewrite BK by reflexivity; exact P2).
    (* [comment removed for export] *)
    assert (ASM : forall q3 m3 (kr kw : reg -> bool),
      msteps SEGS (mkst q2 (0x53e9c : word) p9 rom) (mkst q3 (0x53ed8 : word) m3 rom) ->
      (forall r, kr r = false -> getr q3 r = getr q2 r) ->
      getr q3 10 = Z_to_bv 64 d -> getr q3 11 = Z_to_bv 64 s -> getr q3 12 = Z_to_bv 64 n -> getr q3 2 = Z_to_bv 64 (usp - 2144) ->
      (forall q4, getr q4 13 = Z_to_bv 64 (2 ^ 64 - 65) -> (forall r : reg, r <> 13 -> getr q4 r = getr q3 r) ->
         exists q5 m5, msteps SEGS (mkst q4 (0x53ee4 : word) m3 rom) (mkst q5 (0x53f20 : word) m5 rom)
           /\ sfr m5 /\ (forall r, kw r = false -> getr q5 r = getr q4 r)
           /\ getr q5 10 = Z_to_bv 64 d /\ getr q5 11 = Z_to_bv 64 s /\ getr q5 12 = Z_to_bv 64 n /\ getr q5 2 = Z_to_bv 64 (usp - 2144)) ->
      (forall r : reg, cp_clob r = false -> r <> 1 -> r <> 2 -> r <> 8 -> r <> 9 -> r <> 18 -> r <> 19 -> r <> 20 -> r <> 21 ->
         r <> 22 -> r <> 23 -> kr r = false /\ kw r = false) ->
      exists regs' m',
        msteps SEGS (mkst regs0 (0x53e30 : word) mem rom) (mkst regs' ra m' rom)
        /\ getr regs' 10 = Z_to_bv 64 d /\ getr regs' 2 = Z_to_bv 64 usp /\ getr regs' 1 = ra
        /\ (forall r, cp_clob r = false -> getr regs' r = getr regs0 r)
        /\ (forall x : word, (bv_unsigned x < usp - CP_FRAME \/ usp <= bv_unsigned x)%Z ->
              m' x = wbytes mem (Z_to_bv 64 d) bs x)
        /\ (forall x, mem x <> None -> m' x <> None)).
    { intros q3 m3 kr kw M3 K3 Q10 Q11 Q12 Q2 W KC.
      destruct (blk_W0 q3 m3 Q10 Q12) as (q4 & M4 & A13 & K4).
      destruct (W q4 A13 K4) as (q5 & m5 & M5 & F5 & K5 & R10 & R11 & R12 & R2).
      destruct (finish q5 m5 F5 R10 R11 R12 R2) as (q6 & m' & MF & F10 & F2 & F1 & F8 & F9 & F18 & F19 & F20 & F21 & F22 & F23 & FK & ME & MGr).
      exists q6, m'. split; [|split; [exact F10|split; [exact F2|split; [exact F1|split; [|split; [exact ME|exact MGr]]]]]].
      - eapply msteps_trans; [exact MP|]. eapply msteps_trans; [exact MB|]. eapply msteps_trans; [exact M3|].
        eapply msteps_trans; [exact M4|]. eapply msteps_trans; [exact M5|]. exact MF.
      - intros r Hr.
        destruct (bv_eq_dec _ r 1) as [-> | N1]; [rewrite F1; symmetry; exact H01|].
        destruct (bv_eq_dec _ r 2) as [-> | N2]; [rewrite F2; symmetry; exact H02|].
        destruct (bv_eq_dec _ r 8) as [-> | N8]; [exact F8|].
        destruct (bv_eq_dec _ r 9) as [-> | N9]; [exact F9|].
        destruct (bv_eq_dec _ r 18) as [-> | N18]; [exact F18|].
        destruct (bv_eq_dec _ r 19) as [-> | N19]; [exact F19|].
        destruct (bv_eq_dec _ r 20) as [-> | N20]; [exact F20|].
        destruct (bv_eq_dec _ r 21) as [-> | N21]; [exact F21|].
        destruct (bv_eq_dec _ r 22) as [-> | N22]; [exact F22|].
        destruct (bv_eq_dec _ r 23) as [-> | N23]; [exact F23|].
        rewrite (FK r Hr) by (unfold f_clob; rewrite (bv_eqb_neq _ _ N1), (bv_eqb_neq _ _ N2), (bv_eqb_neq _ _ N8),
                                (bv_eqb_neq _ _ N9), (bv_eqb_neq _ _ N18), (bv_eqb_neq _ _ N19), (bv_eqb_neq _ _ N20),
                                (bv_eqb_neq _ _ N21), (bv_eqb_neq _ _ N22), (bv_eqb_neq _ _ N23); reflexivity).
        destruct (KC r Hr N1 N2 N8 N9 N18 N19 N20 N21 N22 N23) as [Kr Kw].
        rewrite (K5 r Kw). rewrite (K4 r) by (intros ->; cbn in Hr; discriminate). rewrite (K3 r Kr).
        assert (Hr' := Hr). unfold cp_clob in Hr'.
        repeat match type of Hr' with (?a || ?b)%bool = false => apply orb_false_iff in Hr'; destruct Hr' as [Hr' ?] end.
        rewrite (BK r) by (unfold b_clob; rewrite (bv_eqb_neq _ _ N19), (bv_eqb_neq _ _ N20), (bv_eqb_neq _ _ N21), (bv_eqb_neq _ _ N22);
                           repeat match goal with Hb : bv_eqb r _ = false |- _ => rewrite Hb end; reflexivity).
        apply PK; assumption. }
    destruct (Z.eq_dec n 0) as [Hn0 | Hn0].
    - (* [comment removed for export] *)
      apply (ASM q2 p9 (fun _ => false) (fun _ => false)).
      + apply blk_RZ; assumption.
      + intros; reflexivity.
      + exact B10. + exact B11. + exact B12. + exact B2.
      + intros q4 A13 K4. exists q4, p9. split; [apply blk_WZ; try assumption|].
        * rewrite (K4 22) by (intros X; discriminate X). exact B22.
        * rewrite (K4 12) by (intros X; discriminate X). exact B12.
        * split; [exact sfr_p9|]. split; [intros; reflexivity|].
          rewrite !K4 by (intros X; discriminate X). auto.
      + intros. split; reflexivity.
    - destruct (Z.lt_ge_cases n 65) as [Hsmall | Hbig].
      + (* [comment removed for export] *)
        destruct (blk_RQ q2 p9 sfr_p9 ltac:(lia) B13 B22 B11 B21) as (q3 & M3 & K3).
        apply (ASM q3 p9 rq_clob wq_clob M3 K3).
        * rewrite (K3 10) by reflexivity. exact B10.
        * rewrite (K3 11) by reflexivity. exact B11.
        * rewrite (K3 12) by reflexivity. exact B12.
        * rewrite (K3 2) by reflexivity. exact B2.
        * intros q4 A13 K4.
          destruct (blk_WQ q4 p9 sfr_p9 ltac:(lia) A13) as (q5 & M5 & K5).
          { rewrite (K4 22) by (intros X; discriminate X). rewrite (K3 22) by reflexivity. exact B22. }
          { rewrite (K4 10) by (intros X; discriminate X). rewrite (K3 10) by reflexivity. exact B10. }
          { rewrite (K4 19) by (intros X; discriminate X). rewrite (K3 19) by reflexivity. exact B19. }
          exists q5, p9. split; [exact M5|]. split; [exact sfr_p9|]. split; [exact K5|].
          rewrite !K5 by reflexivity. rewrite !K4 by (intros X; discriminate X). rewrite !K3 by reflexivity. auto.
        * intros r Hr N1 N2 N8 N9 N18 N19 N20 N21 N22 N23. assert (Hr' := Hr). unfold cp_clob in Hr'.
          repeat match type of Hr' with (?a || ?b)%bool = false => apply orb_false_iff in Hr'; destruct Hr' as [Hr' ?] end.
          unfold rq_clob, wq_clob. rewrite (bv_eqb_neq _ _ N19), (bv_eqb_neq _ _ N21).
          repeat match goal with Hb : bv_eqb r _ = false |- _ => rewrite Hb end. split; reflexivity.
      + (* [comment removed for export] *)
        destruct (blk_RL q2 p9 sfr_p9 Hbig B13 B22 B10 B11 B12 B2) as (q3 & m3 & M3 & F3 & L10 & L11 & L12 & L2 & L22 & L19 & K3).
        apply (ASM q3 m3 l_clob l_clob M3 K3 L10 L11 L12 L2).
        * intros q4 A13 K4.
          destruct (blk_WL q4 m3 F3 Hbig A13) as (q5 & m5 & M5 & F5 & M10 & M11 & M12 & M2 & K5).
          { rewrite (K4 22) by (intros X; discriminate X). rewrite L22. exact B22. }
          { rewrite (K4 10) by (intros X; discriminate X). exact L10. }
          { rewrite (K4 11) by (intros X; discriminate X). exact L11. }
          { rewrite (K4 12) by (intros X; discriminate X). exact L12. }
          { rewrite (K4 2) by (intros X; discriminate X). exact L2. }
          exists q5, m5. split; [exact M5|]. split; [exact F5|]. split; [exact K5|]. auto.
        * intros r Hr N1 N2 N8 N9 N18 N19 N20 N21 N22 N23. assert (Hr' := Hr). unfold cp_clob in Hr'.
          repeat match type of Hr' with (?a || ?b)%bool = false => apply orb_false_iff in Hr'; destruct Hr' as [Hr' ?] end.
          unfold l_clob, cp_clob. rewrite (bv_eqb_neq _ _ N1), (bv_eqb_neq _ _ N9), (bv_eqb_neq _ _ N18),
                                        (bv_eqb_neq _ _ N19), (bv_eqb_neq _ _ N21), (bv_eqb_neq _ _ N23).
          repeat match goal with Hb : bv_eqb r _ = false |- _ => rewrite Hb end. split; reflexivity.
  Qed.
End CP.

(* [comment removed for export] *)
Theorem asan_memcpy_run :
  forall (mem rom : word -> option byte) (d s n usp : Z) (bs : list byte),
  cpH mem d s n usp bs ->
  forall regs (ra : word),
  ret_ok ra -> getr regs 1 = ra -> getr regs 2 = Z_to_bv 64 usp ->
  getr regs 10 = Z_to_bv 64 d -> getr regs 11 = Z_to_bv 64 s -> getr regs 12 = Z_to_bv 64 n ->
  exists regs' m',
    msteps SEGS (mkst regs (0x53e30 : word) mem rom) (mkst regs' ra m' rom)
    /\ getr regs' 10 = Z_to_bv 64 d /\ getr regs' 2 = Z_to_bv 64 usp /\ getr regs' 1 = ra
    /\ (forall r, cp_clob r = false -> getr regs' r = getr regs r)
    /\ (forall x : word, (bv_unsigned x < usp - CP_FRAME \/ usp <= bv_unsigned x)%Z ->
          m' x = wbytes mem (Z_to_bv 64 d) bs x)
    /\ (forall x, mem x <> None -> m' x <> None).
Proof.
  intros mem rom d s n usp bs H regs ra Hret H1 H2 H10 H11 H12.
  exact (asan_memcpy_CP mem rom d s n usp bs H regs ra Hret H1 H2 H10 H11 H12).
Qed.
