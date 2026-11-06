(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.coturn.FuzzStunClient.images Require Import AsanUbsan.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import PropExec CatExec CatSim SeqExec MmapSim StepTac Hoare RefEnframeArith.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Asan Require Import Both_code_icpt Both_code_icpt2 BothRegionPoisoned BothReadCheck.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib Require Import RefReadLib.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require PropExec.
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
#[local] Ltac OSSVerify.Proofs.coturn.FuzzStunClient.lib.Asan.BothRegionPoisoned.gr ::= gr_fast.
(* [comment removed for export] *)
#[local] Existing Instance PropExec.fx0.   (* [comment removed for export] *)
Import ListNotations.
Open Scope bv_scope.

Abbreviation SEGS := AsanUbsan.M.loaded_segments.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Definition ISRC_ENTRY : Z := 0x54860.
Definition ISRC_EXIT : Z := 0x54898.

Section ISRC.
  Variables (mem rom : word -> option byte) (src s3v : Z).
  Hypothesis Hsrc : (0 <= src < 2 ^ 64)%Z.
  Hypothesis Hs3 : (1 <= s3v < 2 ^ 64)%Z.
  Hypothesis C1 : cell mem 0xa94b8 0xb1bb8.
  Hypothesis C2 : cell mem 0xb1bb8 SB.
  (* [comment removed for export] *)
  Definition h1 : Z := ((SB + src / 8) / 8 * 8)%Z.
  Definition h2 : Z := ((SB + (s3v - 1) / 8) / 8 * 8)%Z.
  Hypothesis Hz1 : forall j, (0 <= j < 8)%Z -> mem (Z_to_bv 64 (h1 + j)) = Some (Z_to_bv 8 0).
  Hypothesis Hz2 : forall j, (0 <= j < 8)%Z -> mem (Z_to_bv 64 (h2 + j)) = Some (Z_to_bv 8 0).

  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
  #[using="Hsrc Hs3"] Lemma isrc_arith :
    (0 <= SB + src / 8 < 2 ^ 64)%Z /\ (0 <= SB + (s3v - 1) / 8 < 2 ^ 64)%Z
    /\ (0 <= h1)%Z /\ (h1 + 8 <= 2 ^ 64)%Z /\ (0 <= h2)%Z /\ (h2 + 8 <= 2 ^ 64)%Z
    /\ (0 <= src / 8 < 2 ^ 64)%Z /\ (0 <= (s3v - 1) / 8 < 2 ^ 64)%Z /\ (0 <= s3v - 1 < 2 ^ 64)%Z.
  Proof. pose proof SB_val. unfold h1, h2. unfold SB. lia. Qed.
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

  #[using="Hz1"] Lemma rd_h1 : rdn SEGS mem (Z_to_bv 64 h1) 8 = Some (repeat (Z_to_bv 8 0) 8).
  Proof. apply rdn_zeros. intros j Hj. apply Hz1. cbn in Hj. lia. Qed.
  #[using="Hz2"] Lemma rd_h2 : rdn SEGS mem (Z_to_bv 64 h2) 8 = Some (repeat (Z_to_bv 8 0) 8).
  Proof. apply rdn_zeros. intros j Hj. apply Hz2. cbn in Hj. lia. Qed.

  #[using="Hsrc Hs3 C1 C2 Hz1 Hz2"] Theorem icpt_src_check_S : forall regs,
    getr regs 11 = Z_to_bv 64 src -> getr regs 19 = Z_to_bv 64 s3v ->
    exists regs',
      msteps SEGS (mkst regs (0x54860 : word) mem rom) (mkst regs' (0x54898 : word) mem rom)
      /\ (forall r, r <> 13 -> r <> 14 -> r <> 15 -> r <> 16 -> r <> 19 -> getr regs' r = getr regs r).
  Proof.
    intros regs H11 H19. pose proof SB_val as HSB.
    pose proof isrc_arith as RA. destruct RA as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9).
    pose proof rd_h1 as RD1. pose proof rd_h2 as RD2. unfold h1 in RD1, A3, A4. unfold h2 in RD2, A5, A6.
    eexists. split.
    - (* [comment removed for export] *)
      mstep ltac:(eapply (step_auipc_at _ _ _ _ _ _ _ _ (Z_to_bv 64 0xa9860) F_54860 eq_refl D_54860);
                   [reflexivity | apply bv_eq; vm_compute; reflexivity]).
      mld F_54864 D_54864 0xb1bb8%Z C1 H11.
      (* [comment removed for export] *)
      mld F_54868 D_54868 SB C2 H11.
      (* [comment removed for export] *)
      mstep ltac:(exact (step_addi _ _ _ _ _ _ _ _ _ F_5486c eq_refl D_5486c)). gr. rewrite H19. zn.
      replace (s3v + -1)%Z with (s3v - 1)%Z by lia.
      (* [comment removed for export] *)
      mstep ltac:(exact (PropExec.step_srli _ _ _ _ _ _ _ _ _ F_54870 eq_refl D_54870)). gr. rewrite H11, (v_srli_3 src) by lia.
      mstep ltac:(exact (PropExec.step_srli _ _ _ _ _ _ _ _ _ F_54874 eq_refl D_54874)). gr. rewrite (v_srli_3 (s3v - 1)) by lia.
      (* [comment removed for export] *)
      mstep ltac:(exact (step_add _ _ _ _ _ _ _ _ _ F_54878 eq_refl D_54878)). gr. rewrite v_add_zbv by lia.
      mstep ltac:(exact (step_add _ _ _ _ _ _ _ _ _ F_5487c eq_refl D_5487c)). gr. rewrite v_add_zbv by lia.
      (* [comment removed for export] *)
      mstep ltac:(exact (step_andi _ _ _ _ _ _ _ _ _ F_54880 eq_refl D_54880)). gr. rewrite v_andi_m8 by lia.
      mstep ltac:(exact (step_andi _ _ _ _ _ _ _ _ _ F_54884 eq_refl D_54884)). gr. rewrite v_andi_m8 by lia.
      (* [comment removed for export] *)
      mstep ltac:(eapply (@step_ld _ _ _ _ _ _ _ _ _ _ _ (Z_to_bv 64 0) F_54888 eq_refl D_54888);
                   [ gr; zn; rewrite Z.add_0_r; exact RD1 | rewrite bytes_le_to_Z_zeros; reflexivity ]).
      mstep ltac:(eapply (@step_ld _ _ _ _ _ _ _ _ _ _ _ (Z_to_bv 64 0) F_5488c eq_refl D_5488c);
                   [ gr; zn; rewrite Z.add_0_r; exact RD2 | rewrite bytes_le_to_Z_zeros; reflexivity ]).
      (* [comment removed for export] *)
      mstep ltac:(exact (step_or _ _ _ _ _ _ _ _ _ F_54890 eq_refl D_54890)). gr. rewrite v_or_zero.
      eapply mst_step; [reflexivity | eapply (step_bne_ft _ _ _ _ _ _ _ _ _ F_54894 eq_refl D_54894); gr; rewrite getr_zero; reflexivity |].
      step_simpl. imm_norm. apply mst_refl.
    - gr. intros r N13 N14 N15 N16 N19.
      repeat (rewrite getr_other by (intros ->; first [contradiction | congruence])). reflexivity.
  Qed.
End ISRC.

(* [comment removed for export] *)
Theorem icpt_src_check :
  forall (mem rom : word -> option byte) (src s3v : Z),
  (0 <= src < 2 ^ 64)%Z -> (1 <= s3v < 2 ^ 64)%Z ->
  cell mem 0xa94b8 0xb1bb8 -> cell mem 0xb1bb8 SB ->
  (forall j, (0 <= j < 8)%Z -> mem (Z_to_bv 64 ((SB + src / 8) / 8 * 8 + j)) = Some (Z_to_bv 8 0)) ->
  (forall j, (0 <= j < 8)%Z -> mem (Z_to_bv 64 ((SB + (s3v - 1) / 8) / 8 * 8 + j)) = Some (Z_to_bv 8 0)) ->
  forall regs, getr regs 11 = Z_to_bv 64 src -> getr regs 19 = Z_to_bv 64 s3v ->
  exists regs',
    msteps SEGS (mkst regs (0x54860 : word) mem rom) (mkst regs' (0x54898 : word) mem rom)
    /\ (forall r, r <> 13 -> r <> 14 -> r <> 15 -> r <> 16 -> r <> 19 -> getr regs' r = getr regs r).
Proof.
  intros mem rom src s3v Hsrc Hs3 C1 C2 Hz1 Hz2 regs H11 H19.
  exact (icpt_src_check_S mem rom src s3v Hsrc Hs3 C1 C2 Hz1 Hz2 regs H11 H19).
Qed.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition IDST_ENTRY : Z := 0x548a8.
Definition IDST_EXIT : Z := 0x548e0.

Lemma lit_54ae8 : btgt (0x548dc : word) 884 = (0x54c50 : word).
Proof. apply bv_eq. vm_compute. reflexivity. Qed.
Lemma lit_54b04 : btgt (0x54c78 : word) (-12) = (0x54c6c : word).
Proof. apply bv_eq. vm_compute. reflexivity. Qed.
Lemma lit_54b14 : btgt (0x54c68 : word) 20 = (0x54c7c : word).
Proof. apply bv_eq. vm_compute. reflexivity. Qed.
Lemma lit_54778 : btgt (0x54c80 : word) (-928) = (0x548e0 : word).
Proof. apply bv_eq. vm_compute. reflexivity. Qed.

Section LOOP.
  Variables (mem rom : word -> option byte).

  (* [comment removed for export] *)
  #[using="Type"] Lemma or_loop_body : forall (k : nat) regs (a3 : Z),
    (1 <= Z.of_nat k)%Z -> (0 <= a3)%Z -> (a3 + Z.of_nat k < 2 ^ 64)%Z ->
    (forall i, (0 <= i < Z.of_nat k)%Z -> mem (Z_to_bv 64 (a3 + i)) = Some (Z_to_bv 8 0)) ->
    getr regs 13 = Z_to_bv 64 a3 -> getr regs 14 = Z_to_bv 64 (a3 + Z.of_nat k) -> getr regs 15 = Z_to_bv 64 0 ->
    exists regs',
      msteps SEGS (mkst regs (0x54c6c : word) mem rom) (mkst regs' (0x54c7c : word) mem rom)
      /\ getr regs' 15 = Z_to_bv 64 0
      /\ (forall r, r <> 13 -> r <> 15 -> r <> 16 -> getr regs' r = getr regs r).
  Proof.
    induction k as [|k IH]; intros regs a3 Hk Ha3 Hhi Hz H13 H14 H15; [cbn in Hk; lia|].
    assert (Hrd : rdn SEGS mem (Z_to_bv 64 a3) 1 = Some [Z_to_bv 8 0]).
    { apply rdn1. rewrite <- (Z.add_0_r a3). apply Hz. lia. }
    destruct (Nat.eq_dec k 0) as [K0|Kpos].
    - (* [comment removed for export] *)
      subst k. cbn [Z.of_nat Pos.of_succ_nat] in *.
      eexists. split; [|split].
      + mstep ltac:(eapply (@step_lbu _ _ _ _ _ _ _ _ _ _ (Z_to_bv 8 0) F_54c6c eq_refl D_54c6c); gr; rewrite ?H13; imm_norm; zn; rewrite ?Z.add_0_r; exact Hrd).
        mstep ltac:(exact (step_addi _ _ _ _ _ _ _ _ _ F_54c70 eq_refl D_54c70)). gr. rewrite H13. zn.
        mstep ltac:(exact (step_or _ _ _ _ _ _ _ _ _ F_54c74 eq_refl D_54c74)). gr. rewrite H15.
        change (bv_unsigned (Z_to_bv 8 0)) with 0%Z. rewrite v_or_zero.
        mstep ltac:(eapply (step_bne_ft _ _ _ _ _ _ _ _ _ F_54c78 eq_refl D_54c78); gr; rewrite ?H14; br_eq).
        apply mst_refl.
      + gr. reflexivity.
      + intros r N13 N15 N16. repeat (rewrite getr_other by (intros ->; first [contradiction | congruence])). reflexivity.
    - (* [comment removed for export] *)
      assert (Hk1 : (1 <= Z.of_nat k)%Z) by lia.
      edestruct (IH (regupd (regupd (regupd regs 16 (Z_to_bv 64 0)) 13 (Z_to_bv 64 (a3 + 1))) 15 (Z_to_bv 64 0)) (a3 + 1)%Z Hk1)
        as (regs' & Hms & H15' & Hoth); [lia | lia | | gr; reflexivity | gr; rewrite H14; apply (f_equal (Z_to_bv 64)); lia | gr; reflexivity |].
      { intros i Hi. replace (a3 + 1 + i)%Z with (a3 + (1 + i))%Z by lia. apply Hz. lia. }
      eexists. split; [|split].
      + mstep ltac:(eapply (@step_lbu _ _ _ _ _ _ _ _ _ _ (Z_to_bv 8 0) F_54c6c eq_refl D_54c6c); gr; rewrite ?H13; imm_norm; zn; rewrite ?Z.add_0_r; exact Hrd).
        mstep ltac:(exact (step_addi _ _ _ _ _ _ _ _ _ F_54c70 eq_refl D_54c70)). gr. rewrite H13. zn.
        mstep ltac:(exact (step_or _ _ _ _ _ _ _ _ _ F_54c74 eq_refl D_54c74)). gr. rewrite H15.
        change (bv_unsigned (Z_to_bv 8 0)) with 0%Z. rewrite v_or_zero.
        mstep ltac:(eapply (step_bne_tk _ _ _ _ _ _ _ _ _ F_54c78 eq_refl D_54c78); gr; rewrite ?H14; br_eq).
        exact Hms.
      + exact H15'.
      + intros r N13 N15 N16. rewrite (Hoth r N13 N15 N16).
        repeat (rewrite getr_other by (intros ->; first [contradiction | congruence])). reflexivity.
  Qed.

  (* [comment removed for export] *)
  #[using="Type"] Lemma or_loop : forall (k : nat) regs (a3 : Z),
    (0 <= a3)%Z -> (a3 + Z.of_nat k < 2 ^ 64)%Z ->
    (forall i, (0 <= i < Z.of_nat k)%Z -> mem (Z_to_bv 64 (a3 + i)) = Some (Z_to_bv 8 0)) ->
    getr regs 13 = Z_to_bv 64 a3 -> getr regs 14 = Z_to_bv 64 (a3 + Z.of_nat k) -> getr regs 15 = Z_to_bv 64 0 ->
    exists regs',
      msteps SEGS (mkst regs (0x54c68 : word) mem rom) (mkst regs' (0x54c7c : word) mem rom)
      /\ getr regs' 15 = Z_to_bv 64 0
      /\ (forall r, r <> 13 -> r <> 15 -> r <> 16 -> getr regs' r = getr regs r).
  Proof.
    intros k regs a3 Ha3 Hhi Hz H13 H14 H15.
    destruct (Nat.eq_dec k 0) as [K0|Kpos].
    - subst k. eexists. split; [|split; [exact H15 | intros; reflexivity]].
      mstep ltac:(eapply (step_bgeu_tk _ _ _ _ _ _ _ _ _ F_54c68 eq_refl D_54c68); gr; rewrite ?H13, ?H14; br_lt).
      apply mst_refl.
    - edestruct (or_loop_body k regs a3) as (regs' & Hms & H15' & Hoth); [lia | lia | lia | exact Hz | exact H13 | exact H14 | exact H15 |].
      exists regs'. split; [|split; [exact H15' | exact Hoth]].
      mstep ltac:(eapply (step_bgeu_ft _ _ _ _ _ _ _ _ _ F_54c68 eq_refl D_54c68); gr; rewrite ?H13, ?H14; br_lt).
      exact Hms.
  Qed.
End LOOP.

Section IDST.
  Variables (mem rom : word -> option byte) (p n : Z) (b1 : byte) (bs1 bs2 : list byte).
  Hypothesis Hp : (0 <= p)%Z.
  Hypothesis Hp8 : (p mod 8 = 0)%Z.
  Hypothesis Hn : (1 <= n <= 64)%Z.
  Hypothesis Hpn : (p + n < 2 ^ 47)%Z.
  Hypothesis C1 : cell mem 0xa94b8 0xb1bb8.
  Hypothesis C2 : cell mem 0xb1bb8 SB.
  Definition q : Z := (n / 8)%Z.
  Definition r : Z := (n mod 8)%Z.
  Definition sp0 : Z := (SB + p / 8)%Z.                 (* [comment removed for export] *)
  Definition sl : Z := (SB + (p + n - 1) / 8)%Z.        (* [comment removed for export] *)
  Hypothesis Hzero : forall i, (0 <= i < q)%Z -> mem (Z_to_bv 64 (sp0 + i)) = Some (Z_to_bv 8 0).
  Hypothesis Hlast : r <> 0%Z -> rdn SEGS mem (Z_to_bv 64 (sp0 + q)) 1 = Some [b1] /\ (r <= bv_unsigned b1 <= 127)%Z.
  Hypothesis Hw1 : rdn SEGS mem (Z_to_bv 64 (sp0 / 8 * 8)) 8 = Some bs1.
  Hypothesis Hw2 : rdn SEGS mem (Z_to_bv 64 (sl / 8 * 8)) 8 = Some bs2.

  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
  #[using="Hp Hp8 Hn Hpn"] Lemma idst_arith :
    (0 <= sp0)%Z /\ (sl < 2 ^ 62)%Z /\ (sp0 <= sl)%Z /\ (0 <= sp0 / 8 * 8)%Z /\ (sp0 / 8 * 8 < 2 ^ 64)%Z
    /\ (0 <= sl / 8 * 8)%Z /\ (sl / 8 * 8 < 2 ^ 64)%Z /\ (0 <= p / 8 < 2 ^ 64)%Z /\ (0 <= (p + n - 1) / 8 < 2 ^ 64)%Z
    /\ (0 <= p + n - 1 < 2 ^ 64)%Z /\ (0 <= q <= 8)%Z /\ (0 <= r < 8)%Z
    /\ (r = 0 -> sl = sp0 + q - 1 /\ 1 <= q)%Z /\ (r <> 0 -> sl = sp0 + q)%Z
    /\ ((p + n - 1) mod 8 = (if r =? 0 then 7 else r - 1))%Z.
  Proof.
    pose proof SB_val. unfold sp0, sl, q, r. unfold SB.
    destruct (Z.eqb_spec (n mod 8) 0); (ltac2:(LK.k [@Hp; @Hp8; @Hn; @Hpn; @e; @n0]); lia).
  Qed.
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

  #[using="Type"] Lemma w_of_bytes : forall a bs, rdn SEGS mem a 8 = Some bs -> (0 <= bytes_le_to_Z bs < 2 ^ 64)%Z.
  Proof.
    intros a bs Hrd. pose proof (rdn_length _ _ _ _ _ Hrd) as Hlen. split; [apply bytes_le_to_Z_nonneg|].
    pose proof (bytes_le_to_Z_bound bs) as Hb. rewrite Hlen in Hb. exact Hb.
  Qed.

  (* [comment removed for export] *)
  Definition pre_clob (x : reg) : bool := (bv_eqb x 13 || bv_eqb x 14 || bv_eqb x 15 || bv_eqb x 16 || bv_eqb x 20)%bool.
  #[using="Hp Hp8 Hn Hpn C1 C2 Hw1 Hw2"] Lemma idst_prefix : forall regs,
    getr regs 10 = Z_to_bv 64 p -> getr regs 20 = Z_to_bv 64 (p + n) ->
    exists regs',
      msteps SEGS (mkst regs (0x548a8 : word) mem rom) (mkst regs' (0x548dc : word) mem rom)
      /\ getr regs' 13 = Z_to_bv 64 sp0 /\ getr regs' 14 = Z_to_bv 64 sl /\ getr regs' 20 = Z_to_bv 64 (p + n - 1)
      /\ getr regs' 15 = v_or (Z_to_bv 64 (bytes_le_to_Z bs2)) (Z_to_bv 64 (bytes_le_to_Z bs1))
      /\ (forall x, pre_clob x = false -> getr regs' x = getr regs x).
  Proof.
    intros regs H10 H20. pose proof SB_val as HSB.
    pose proof idst_arith as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & A10 & _).
    pose proof (w_of_bytes _ _ Hw1) as B1. pose proof (w_of_bytes _ _ Hw2) as B2.
    eexists. split.
    - mstep ltac:(eapply (step_auipc_at _ _ _ _ _ _ _ _ (Z_to_bv 64 0xa98a8) F_548a8 eq_refl D_548a8);
                   [reflexivity | apply bv_eq; vm_compute; reflexivity]).
      mld F_548ac D_548ac 0xb1bb8%Z C1 H10.
      mld F_548b0 D_548b0 SB C2 H10.
      mstep ltac:(exact (step_addi _ _ _ _ _ _ _ _ _ F_548b4 eq_refl D_548b4)). gr. rewrite H20. zn.
      replace (p + n + -1)%Z with (p + n - 1)%Z by lia.
      mstep ltac:(exact (PropExec.step_srli _ _ _ _ _ _ _ _ _ F_548b8 eq_refl D_548b8)). gr. rewrite H10, (v_srli_3 p) by lia.
      mstep ltac:(exact (PropExec.step_srli _ _ _ _ _ _ _ _ _ F_548bc eq_refl D_548bc)). gr. rewrite (v_srli_3 (p + n - 1)) by lia.
      mstep ltac:(exact (step_add _ _ _ _ _ _ _ _ _ F_548c0 eq_refl D_548c0)). gr. rewrite v_add_zbv by lia.
      mstep ltac:(exact (step_add _ _ _ _ _ _ _ _ _ F_548c4 eq_refl D_548c4)). gr. rewrite v_add_zbv by lia.
      fold sp0. fold sl.
      mstep ltac:(exact (step_andi _ _ _ _ _ _ _ _ _ F_548c8 eq_refl D_548c8)). gr. rewrite v_andi_m8 by lia.
      mstep ltac:(exact (step_andi _ _ _ _ _ _ _ _ _ F_548cc eq_refl D_548cc)). gr. rewrite v_andi_m8 by lia.
      mstep ltac:(eapply (@step_ld _ _ _ _ _ _ _ _ _ _ _ (Z_to_bv 64 (bytes_le_to_Z bs1)) F_548d0 eq_refl D_548d0);
                   [ gr; zn; rewrite Z.add_0_r; exact Hw1 | rewrite zbv_u by exact B1; reflexivity ]).
      mstep ltac:(eapply (@step_ld _ _ _ _ _ _ _ _ _ _ _ (Z_to_bv 64 (bytes_le_to_Z bs2)) F_548d4 eq_refl D_548d4);
                   [ gr; zn; rewrite Z.add_0_r; exact Hw2 | rewrite zbv_u by exact B2; reflexivity ]).
      eapply mst_step; [reflexivity | exact (step_or _ _ _ _ _ _ _ _ _ F_548d8 eq_refl D_548d8) |].
      step_simpl. imm_norm. apply mst_refl.
    - gr. repeat split; try reflexivity.
      intros x Hx. unfold pre_clob in Hx.
      repeat (rewrite getr_other by (intros ->; cbn in Hx; discriminate)). reflexivity.
  Qed.

  Definition idst_clob (x : reg) : bool :=
    (bv_eqb x 13 || bv_eqb x 14 || bv_eqb x 15 || bv_eqb x 16 || bv_eqb x 17 || bv_eqb x 20)%bool.

  #[using="p n Hp"] Lemma v_lb_small : forall b : byte, (bv_unsigned b <= 127)%Z -> v_lb b = Z_to_bv 64 (bv_unsigned b).
  Proof. intros b Hb. unfold v_lb. rewrite bv_signed_small8 by lia. reflexivity. Qed.
  #[using="p n Hp"] Lemma v_xori_1 : forall z, (0 <= z <= 1)%Z -> v_xori (Z_to_bv 64 z) 1 = Z_to_bv 64 (1 - z).
  Proof.
    intros z Hz. unfold v_xori. rewrite zbv_u by lia. change (bv_wrap 64 1) with 1%Z.
    assert (z = 0 \/ z = 1)%Z as [->| ->] by lia; reflexivity.
  Qed.

  #[using="b1 bs1 bs2 Hp Hp8 Hn Hpn C1 C2 Hzero Hlast Hw1 Hw2"] Theorem icpt_dst_check_S : forall regs,
    getr regs 10 = Z_to_bv 64 p -> getr regs 20 = Z_to_bv 64 (p + n) ->
    exists regs',
      msteps SEGS (mkst regs (0x548a8 : word) mem rom) (mkst regs' (0x548e0 : word) mem rom)
      /\ (forall x, idst_clob x = false -> getr regs' x = getr regs x).
  Proof.
    intros regs H10 H20. pose proof SB_val as HSB.
    pose proof idst_arith as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & A10 & A11 & A12 & A13 & A14 & A15).
    pose proof (w_of_bytes _ _ Hw1) as B1. pose proof (w_of_bytes _ _ Hw2) as B2.
    destruct (idst_prefix regs H10 H20) as (regs1 & Hms1 & R13 & R14 & R20 & R15 & Roth).
    set (wv := v_or (Z_to_bv 64 (bytes_le_to_Z bs2)) (Z_to_bv 64 (bytes_le_to_Z bs1))) in R15.
    destruct (bv_eq_dec 64 wv (Z_to_bv 64 0)) as [W0|W1].
    - (* [comment removed for export] *)
      exists regs1. split.
      + eapply msteps_trans; [exact Hms1|].
        mstep ltac:(eapply (step_bne_ft _ _ _ _ _ _ _ _ _ F_548dc eq_refl D_548dc); gr; rewrite ?R15, ?getr_zero, W0; unfold c_eq; apply bv_eqb_refl).
        apply mst_refl.
      + intros x Hx. apply Roth. unfold idst_clob in Hx. unfold pre_clob.
        destruct (bv_eqb x 13), (bv_eqb x 14), (bv_eqb x 15), (bv_eqb x 16), (bv_eqb x 17), (bv_eqb x 20); cbn in Hx |- *; congruence.
    - (* [comment removed for export] *)
      (* [comment removed for export] *)
      assert (exists b, rdn SEGS mem (Z_to_bv 64 sl) 1 = Some [b] /\ (bv_unsigned b <= 127)%Z
                        /\ (bv_unsigned b = 0 \/ (p + n - 1) mod 8 < bv_unsigned b)%Z) as (b & Hrd & Hb127 & Hbok).
      { destruct (Z.eq_dec r 0) as [R0|R1].
        - destruct (A13 R0) as [E1 Q1]. exists (Z_to_bv 8 0). rewrite E1.
          replace (sp0 + q - 1)%Z with (sp0 + (q - 1))%Z by lia. split; [apply rdn1; apply Hzero; lia|].
          change (bv_unsigned (Z_to_bv 8 0)) with 0%Z. split; [lia | left; reflexivity].
        - destruct (Hlast R1) as [E1 Q1]. exists b1. rewrite (A14 R1). split; [exact E1|]. split; [lia|].
          right. rewrite A15. destruct (Z.eqb_spec r 0); lia. }
      pose proof (bv_unsigned_in_range 8 b) as Hbr.
      set (a6v := ((p + n - 1) mod 8)%Z).
      assert (Ha6 : (0 <= a6v < 8)%Z) by (unfold a6v; apply Z.mod_pos_bound; lia).
      (* [comment removed for export] *)
      assert (exists regs2,
        msteps SEGS (mkst regs1 (0x548dc : word) mem rom) (mkst regs2 (0x54c68 : word) mem rom)
        /\ getr regs2 13 = Z_to_bv 64 sp0 /\ getr regs2 14 = Z_to_bv 64 sl /\ getr regs2 15 = Z_to_bv 64 0
        /\ (forall x, x <> 15 -> x <> 16 -> x <> 17 -> getr regs2 x = getr regs1 x)) as (regs2 & Hms2 & S13 & S14 & S15 & Soth).
      { eexists. split.
        - mstep ltac:(eapply (step_bne_tk _ _ _ _ _ _ _ _ _ F_548dc eq_refl D_548dc); gr; rewrite ?R15, ?getr_zero;
                       unfold c_eq, bv_eqb; apply Z.eqb_neq; intros X; apply W1; apply bv_eq; exact X).
          mstep ltac:(eapply (@step_lb _ _ _ _ _ _ _ _ _ _ b F_54c50 eq_refl D_54c50); gr; rewrite ?R14; imm_norm; zn; rewrite ?Z.add_0_r; exact Hrd).
          rewrite (v_lb_small b) by exact Hb127.
          mstep ltac:(exact (step_andi _ _ _ _ _ _ _ _ _ F_54c54 eq_refl D_54c54)). gr. rewrite R20, v_andi_7 by lia. fold a6v.
          mstep ltac:(exact (step_sltu _ _ _ _ _ _ _ _ _ F_54c58 eq_refl D_54c58)). gr. rewrite getr_zero, v_sltu_lit by lia.
          mstep ltac:(exact (step_slt _ _ _ _ _ _ _ _ _ F_54c5c eq_refl D_54c5c)). gr.
          unfold v_slt. rewrite c_lts_zbv by lia.
          mstep ltac:(exact (step_xori _ _ _ _ _ _ _ _ _ F_54c60 eq_refl D_54c60)). gr.
          mstep ltac:(exact (step_and _ _ _ _ _ _ _ _ _ F_54c64 eq_refl D_54c64)). gr.
          apply mst_refl.
        - gr. split; [exact R13|]. split; [exact R14|]. split.
          + (* [comment removed for export] *)
            destruct Hbok as [Z0 | LT].
            * rewrite Z0. match goal with |- ?g => idtac g end.
              replace (0 <? 0)%Z with false by reflexivity.
              replace (a6v <? 0)%Z with false by (symmetry; apply Z.ltb_ge; lia).
              rewrite v_xori_1 by lia. rewrite v_and_lit by lia. reflexivity.
            * replace (0 <? bv_unsigned b)%Z with true by (symmetry; apply Z.ltb_lt; lia).
              replace (a6v <? bv_unsigned b)%Z with true by (symmetry; apply Z.ltb_lt; unfold a6v; lia).
              rewrite v_xori_1 by lia. rewrite v_and_lit by lia. reflexivity.
          + intros x N15 N16 N17. repeat (rewrite getr_other by (intros ->; first [contradiction | congruence])). reflexivity. }
      (* [comment removed for export] *)
      edestruct (or_loop mem rom (Z.to_nat (sl - sp0)) regs2 sp0) as (regs3 & Hms3 & T15 & Toth);
        [lia | rewrite Z2Nat.id by lia; lia | | exact S13 | rewrite Z2Nat.id by lia; replace (sp0 + (sl - sp0))%Z with sl by lia; exact S14 | exact S15 |].
      { intros i Hi. rewrite Z2Nat.id in Hi by lia. apply Hzero. destruct (Z.eq_dec r 0) as [R0|R1]; [destruct (A13 R0); lia | rewrite (A14 R1) in Hi; lia]. }
      exists (regupd regs3 13 (Z_to_bv 64 0)). split.
      + eapply msteps_trans; [exact Hms1|]. eapply msteps_trans; [exact Hms2|]. eapply msteps_trans; [exact Hms3|].
        mstep ltac:(exact (step_andi _ _ _ _ _ _ _ _ _ F_54c7c eq_refl D_54c7c)). gr. rewrite T15.
        rewrite v_andi_lit by lia. change (Z.land 0 255) with 0%Z.
        mstep ltac:(eapply (step_beq_tk _ _ _ _ _ _ _ _ _ F_54c80 eq_refl D_54c80); gr; rewrite ?getr_zero; br_eq).
        apply mst_refl.
      + intros x Hx. unfold idst_clob in Hx.
        assert (N13 : x <> 13) by (intros ->; cbn in Hx; discriminate).
        assert (N14 : x <> 14) by (intros ->; cbn in Hx; discriminate).
        assert (N15 : x <> 15) by (intros ->; cbn in Hx; discriminate).
        assert (N16 : x <> 16) by (intros ->; cbn in Hx; discriminate).
        assert (N17 : x <> 17) by (intros ->; cbn in Hx; discriminate).
        assert (N20 : x <> 20) by (intros ->; cbn in Hx; discriminate).
        rewrite getr_other by exact N13. rewrite (Toth x N13 N15 N16). rewrite (Soth x N15 N16 N17). apply Roth.
        unfold pre_clob. destruct (bv_eqb x 13) eqn:E13; [exfalso; apply N13; apply bv_eq; unfold bv_eqb in E13; apply Z.eqb_eq in E13; exact E13|].
        destruct (bv_eqb x 14) eqn:E14; [exfalso; apply N14; apply bv_eq; unfold bv_eqb in E14; apply Z.eqb_eq in E14; exact E14|].
        destruct (bv_eqb x 15) eqn:E15; [exfalso; apply N15; apply bv_eq; unfold bv_eqb in E15; apply Z.eqb_eq in E15; exact E15|].
        destruct (bv_eqb x 16) eqn:E16; [exfalso; apply N16; apply bv_eq; unfold bv_eqb in E16; apply Z.eqb_eq in E16; exact E16|].
        destruct (bv_eqb x 20) eqn:E20; [exfalso; apply N20; apply bv_eq; unfold bv_eqb in E20; apply Z.eqb_eq in E20; exact E20|].
        reflexivity.
  Qed.
End IDST.

(* [comment removed for export] *)
Theorem icpt_dst_check :
  forall (mem rom : word -> option byte) (p n : Z) (b1 : byte) (bs1 bs2 : list byte),
  (0 <= p)%Z -> (p mod 8 = 0)%Z -> (1 <= n <= 64)%Z -> (p + n < 2 ^ 47)%Z ->
  cell mem 0xa94b8 0xb1bb8 -> cell mem 0xb1bb8 SB ->
  (forall i, (0 <= i < n / 8)%Z -> mem (Z_to_bv 64 (SB + p / 8 + i)) = Some (Z_to_bv 8 0)) ->
  ((n mod 8 <> 0)%Z -> rdn SEGS mem (Z_to_bv 64 (SB + p / 8 + n / 8)) 1 = Some [b1] /\ (n mod 8 <= bv_unsigned b1 <= 127)%Z) ->
  rdn SEGS mem (Z_to_bv 64 ((SB + p / 8) / 8 * 8)) 8 = Some bs1 ->
  rdn SEGS mem (Z_to_bv 64 ((SB + (p + n - 1) / 8) / 8 * 8)) 8 = Some bs2 ->
  forall regs, getr regs 10 = Z_to_bv 64 p -> getr regs 20 = Z_to_bv 64 (p + n) ->
  exists regs',
    msteps SEGS (mkst regs (0x548a8 : word) mem rom) (mkst regs' (0x548e0 : word) mem rom)
    /\ (forall x, x <> 13 -> x <> 14 -> x <> 15 -> x <> 16 -> x <> 17 -> x <> 20 -> getr regs' x = getr regs x).
Proof.
  intros mem rom p n b1 bs1 bs2 Hp Hp8 Hn Hpn C1 C2 Hzero Hlast Hw1 Hw2 regs H10 H20.
  destruct (icpt_dst_check_S mem rom p n b1 bs1 bs2 Hp Hp8 Hn Hpn C1 C2 Hzero Hlast Hw1 Hw2 regs H10 H20) as (regs' & Hms & Hoth).
  exists regs'. split; [exact Hms|]. intros x N13 N14 N15 N16 N17 N20. apply Hoth. unfold idst_clob.
  destruct (bv_eqb x 13) eqn:E13; [exfalso; apply N13; apply bv_eq; unfold bv_eqb in E13; apply Z.eqb_eq in E13; exact E13|].
  destruct (bv_eqb x 14) eqn:E14; [exfalso; apply N14; apply bv_eq; unfold bv_eqb in E14; apply Z.eqb_eq in E14; exact E14|].
  destruct (bv_eqb x 15) eqn:E15; [exfalso; apply N15; apply bv_eq; unfold bv_eqb in E15; apply Z.eqb_eq in E15; exact E15|].
  destruct (bv_eqb x 16) eqn:E16; [exfalso; apply N16; apply bv_eq; unfold bv_eqb in E16; apply Z.eqb_eq in E16; exact E16|].
  destruct (bv_eqb x 17) eqn:E17; [exfalso; apply N17; apply bv_eq; unfold bv_eqb in E17; apply Z.eqb_eq in E17; exact E17|].
  destruct (bv_eqb x 20) eqn:E20; [exfalso; apply N20; apply bv_eq; unfold bv_eqb in E20; apply Z.eqb_eq in E20; exact E20|].
  reflexivity.
Qed.
