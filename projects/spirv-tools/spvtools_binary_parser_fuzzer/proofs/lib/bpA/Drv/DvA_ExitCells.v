(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.spirv_tools.spvtools_binary_parser_fuzzer.images Require Import Asan.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import HPropExec HStoreOk HAgentLib HSymRun HeapCeil HSumWalkTac MainMem.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import HMem HCells HStep HLFrame HMState HSysStep HExec CellsX TacX.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import ASegs AsShadow AsConst AsIface AsPrintfFirst AsDrvMem AsDrvDefs AsDrvCells.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import AsExitDefs DvA_ExitPre DvA_ExitIface AsTailExit.
Import ListNotations.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Open Scope Z_scope.

#[local] Abbreviation RSEGS := Asan.M.loaded_segments.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Definition xk_ac : list (Z * nat * Z) :=
  [(0x1855d8, 8%nat, 0x16c1ec); (0x185648, 8%nat, 0x16a760); (0x185680, 8%nat, 0x16b77c); (0x185780, 8%nat, 0x1750fc);
   (0x185788, 8%nat, 0x175500); (0x1877fc, 4%nat, 0x8); (0x18c040, 8%nat, 0x1); (0x18cf10, 4%nat, 0x1); (0x18cf14, 1%nat, 0x0);
   (0x18cfb0, 8%nat, 0x0); (0x18ef40, 8%nat, 0x18ef48); (0x18ef5c, 1%nat, 0x1); (0x18f6f8, 8%nat, 0x7fff8000);
   (0x1903d8, 1%nat, 0x1); (0x1903d9, 1%nat, 0x1); (0x2212a0, 8%nat, 0xffffffffffffffff); (0x2215a0, 1%nat, 0x0)].
Definition xk_img : list (Z * nat * Z) :=
  [(0x188048, 8%nat, 0x187f60); (0x188058, 8%nat, 0x0); (0x188060, 8%nat, 0x0); (0x188078, 8%nat, 0x0); (0x188088, 8%nat, 0x0);
   (0x1880dc, 4%nat, 0xffffffff); (0x188138, 8%nat, 0x188050); (0x188228, 8%nat, 0x188140)].

Definition xdrv2 : list (Z * nat * Z) :=
  Eval vm_compute in List.filter (fun c => match c with (a, _, _) => negb ((0x187f60 <=? a) && (a <? 0x188048)) end) adrv_cells_base.
Definition xk_atxU : list (Z * nat * Z) := [(0x6e3f70, 4%nat, 0x3)].
Definition xk_atxT : list (Z * nat * Z) :=
  [(0x6c1d54, 1%nat, 0x0); (0x6e3f70, 4%nat, 0x4); (0x6e3fa0, 8%nat, 0x163a80); (0x6e40a0, 8%nat, 0xe8bd4)].

Definition xk_err6 : list (Z * nat * Z) :=
  [(0x187f60, 4%nat, 0x5); (0x187fb8, 8%nat, 0x6e4730); (0x187fc0, 8%nat, 0x0);
   (0x187fec, 4%nat, 0xffffffff); (0x187ff0, 4%nat, 0xffffffff)].

Definition xk_err0 : list (Z * nat * Z) := (0x187fe8, 4%nat, 0x0) :: (0x187f80, 8%nat, 0x0) :: xk_err6.

Definition xk_stderr2 : list (Z * nat * Z) :=
  [(0x187f60, 4%nat, 0x5); (0x187f68, 8%nat, 0x0); (0x187f70, 8%nat, 0x0); (0x187f80, 8%nat, 0x6e4730);
   (0x187f88, 8%nat, 0x6e4730); (0x187f98, 8%nat, 0x6e4730); (0x187fb8, 8%nat, 0x6e4730); (0x187fc0, 8%nat, 0x0);
   (0x187fe8, 4%nat, 0xffffffff); (0x187fec, 4%nat, 0xffffffff); (0x187ff0, 4%nat, 0xffffffff)].
Definition xk_out4 : list (Z * nat * Z) :=
  [(0x188140, 4%nat, 0x5); (0x188198, 8%nat, 0x6e4b40); (0x1881a0, 8%nat, 0x400); (0x1881cc, 4%nat, 0xffffffff)].

Lemma cells_ok_app2 : forall m c1 c2, cells_ok m c1 -> cells_ok m c2 -> cells_ok m (c1 ++ c2).
Proof. intros m c1 c2 H1 H2. unfold cells_ok in *. apply Forall_app. split; assumption. Qed.

Lemma xk_ac_of : forall m, ACONST m -> cells_ok m xk_ac.
Proof.
  intros m AC. acells AC. pose proof (ACONST_exit_v5 m AC) as V. decompose [and] V. clear V.
  lazymatch goal with F6 : rw_cells asegs m AINITED_CELL _ |- _ =>
    pose proof (cells_of_C1C1 m AINITED_CELL 1 1 F6 ltac:(unfold AINITED_CELL; lia) ltac:(unfold AINITED_CELL; lia)) as [I1 I2] end.
  lazymatch goal with X : rw_cells asegs m ACOVFLAG_CELL _ |- _ => pose proof (cell_of_C1 m _ _ X) as I3 end.
  lazymatch goal with X : rw_cells asegs m ACANPOISON_CELL _ |- _ => pose proof (cell_of_C1 m _ _ X) as I4 end.
  lazymatch goal with X : rw_cells asegs m AF_F28_CELL _ |- _ => pose proof (cell_of_C1 m _ _ X) as I5 end.
  unfold xk_ac, cells_ok.
  repeat apply Forall_cons; try apply Forall_nil;
    first [ apply cell_of_C8; assumption
          | apply cell_of_C4; assumption
          | unfold cell_ok; first [exact I1 | exact I2 | exact I3 | exact I4 | exact I5] ].
Qed.

Lemma xk_img_of : forall m, aglb_none m -> cells_ok m xk_img.
Proof.
  intros m [G1 G2]. unfold xk_img, cells_ok.
  repeat apply Forall_cons; try apply Forall_nil; unfold cell_ok;
    first [ rewrite (rdn_img RSEGS m _ _ 0x188048 0x188140 G1) by (cbn; lia)
          | rewrite (rdn_img RSEGS m _ _ 0x188228 0x18c040 G2) by (cbn; lia) ];
    vm_compute; f_equal; repeat first [ reflexivity | apply (f_equal2 cons); [apply bv_eq; reflexivity | ] ].
Qed.

Lemma xdrv2_of : forall m, cells_ok m adrv_cells -> cells_ok m xdrv2.
Proof. intros m CE. apply (cells_ok_incl_b m xdrv2 adrv_cells); [vm_compute; reflexivity | exact CE]. Qed.

Lemma xdrv2_ofT : forall m, cells_ok m adrv_cells_T -> cells_ok m xdrv2.
Proof. intros m CE. apply (cells_ok_incl_b m xdrv2 adrv_cells_T); [vm_compute; reflexivity | exact CE]. Qed.
Lemma xk_err0_ofT : forall m, cells_ok m adrv_cells_T -> cells_ok m xk_err0.
Proof. intros m CE. apply (cells_ok_incl_b m xk_err0 adrv_cells_T); [vm_compute; reflexivity | exact CE]. Qed.
Lemma xk_atxU_wf : forallb cell_wf_b xk_atxU = true. Proof. vm_compute. reflexivity. Qed.

Lemma xk_atxU_range : Forall (fun c : Z * nat * Z => match c with (a, w, _) => 0x6c1d54 <= a /\ a + Z.of_nat w <= 0x6e40a8 end) xk_atxU.
Proof. unfold xk_atxU. repeat (apply Forall_cons; [cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia|]). apply Forall_nil. Qed.

Lemma xk_atxU_of : forall m, cells_ok m adrv_cells -> cells_ok m xk_atxU.
Proof. intros m CE. apply (cells_ok_incl_b m xk_atxU adrv_cells); [vm_compute; reflexivity | exact CE]. Qed.
Lemma xk_atxT_of : forall m, cells_ok m adrv_cells_T -> cells_ok m xk_atxT.
Proof. intros m CE. apply (cells_ok_incl_b m xk_atxT adrv_cells_T); [vm_compute; reflexivity | exact CE]. Qed.

Lemma xk_common_of : forall m, ACONST m -> aglb_none m -> cells_ok m xdrv2 -> cells_ok m xk_err6 -> cells_ok m xk_out4 ->
  cells_ok m xk_common.
Proof.
  intros m AC GL CD CE CO.
  apply (cells_ok_incl_b m xk_common (xk_err6 ++ xk_out4 ++ xdrv2 ++ xk_img ++ xk_ac)); [vm_compute; reflexivity|].
  repeat apply cells_ok_app2; try assumption; [apply xk_img_of; exact GL | apply xk_ac_of; exact AC].
Qed.

Lemma xk_rest_of : forall m, ACONST m -> aglb_none m -> cells_ok m xdrv2 -> cells_ok m xk_out4 -> cells_ok m xk_rest.
Proof.
  intros m AC GL CD CO.
  apply (cells_ok_incl_b m xk_rest (xk_out4 ++ xdrv2 ++ xk_img ++ xk_ac)); [vm_compute; reflexivity|].
  repeat apply cells_ok_app2; try assumption; [apply xk_img_of; exact GL | apply xk_ac_of; exact AC].
Qed.

Lemma cfg_U2_cells : forall m, cells_ok m xk_stderr2 -> cells_ok m astdout0 -> cells_ok m xk_atxU ->
  cells_ok m xk_err6 /\ cells_ok m xk_out4 /\ cells_ok m xk_U2.
Proof.
  intros m CE CO CA. repeat split.
  - apply (cells_ok_incl_b m xk_err6 xk_stderr2); [vm_compute; reflexivity | exact CE].
  - apply (cells_ok_incl_b m xk_out4 astdout0); [vm_compute; reflexivity | exact CO].
  - apply (cells_ok_incl_b m xk_U2 (xk_atxU ++ xk_stderr2 ++ astdout0)); [vm_compute; reflexivity | repeat apply cells_ok_app2; assumption].
Qed.

Lemma cfg_T_cells : forall m k, astdout_after m k -> cells_ok m xk_err0 -> cells_ok m xk_atxT ->
  cells_ok m xk_err6 /\ cells_ok m xk_out4 /\ (k = 0%nat -> cells_ok m xk_T0) /\ cells_ok m (xk_T (Z.of_nat k)).
Proof.
  intros m k ST CE CA. pose proof CE as CE'. unfold xk_err0, cells_ok in CE'. inversion CE' as [|c cs EM CE7]; subst.
  inversion CE7 as [|c cs EW CE6]; subst.
  pose proof CA as CA'. unfold xk_atxT, cells_ok in CA'.
  inversion CA' as [|c1 cs1 A1 CA1]; subst. inversion CA1 as [|c2 cs2 A2 CA2]; subst.
  inversion CA2 as [|c3 cs3 A3 CA3]; subst. inversion CA3 as [|c4 cs4 A4 CA4]; subst. unfold cell_ok in A1, A2, A3, A4.
  destruct ST as [F1 F2 F3 F4 F5 F6 F7 F8 F9 F10 F11 F12 F13 F14].
  repeat split.
  - exact CE6.
  - unfold xk_out4, cells_ok. repeat apply Forall_cons; try apply Forall_nil; unfold cell_ok; assumption.
  - intros ->. unfold xk_T0, cells_ok. repeat apply Forall_cons; try apply Forall_nil; unfold cell_ok; assumption.
  - unfold xk_T, cells_ok. repeat apply Forall_cons; try apply Forall_nil; unfold cell_ok; assumption.
Qed.

Lemma stk_store_okX : forall m lo hi (a : word) n,
  stk asegs m lo hi -> lo <= bv_unsigned a -> bv_unsigned a + Z.of_nat n <= hi -> hi < 2 ^ 64 ->
  store_ok RSEGS m a n = true.
Proof.
  intros m lo hi a n (S1 & S2 & S3) Hlo Hhi H64. apply astore_ok_of_wview; [lia|].
  intros i Hi. rewrite <- wa_eq. exact (proj1 (S3 (bv_unsigned a + i) ltac:(lia))).
Qed.

Section Intro.
  Context {HCEIL : HeapCeil}.

  Definition ahm_ok (m : word -> option byte) (TB : Z) : Prop :=
       rw_cells asegs m 0x18ef48 [C8 (Z_to_bv 64 TB)] /\ 4096 <= TB /\ TB mod 4096 = 0 /\ TB + 0x38e000 <= aceil
    /\ aapp TB 0x38e000
    /\ rw_cells asegs m (TB + 0x14dc00) [CB 96 (repeat (b8 0) 96)] /\ rw_cells asegs m (TB + 0x224ac0) [CB 96 (repeat (b8 0) 96)].

  Lemma ahm_bytes : forall m TB, ahm_ok m TB ->
    (forall i, 0 <= i < 96 -> m (Z_to_bv 64 (TB + 0x14dc00 + i)) = Some (Z_to_bv 8 0)
                             /\ m (Z_to_bv 64 (TB + 0x224ac0 + i)) = Some (Z_to_bv 8 0))
    /\ (forall d n, 0 <= d -> d + Z.of_nat n <= 8 ->
          store_ok RSEGS m (Z_to_bv 64 (TB + 0x14dc00 + d)) n = true /\ store_ok RSEGS m (Z_to_bv 64 (TB + 0x224ac0 + d)) n = true)
    /\ rdn RSEGS m (Z_to_bv 64 0x18ef48) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 TB))
    /\ ATB_LO <= TB <= ATB_HI
    /\ (TB + 0x38e000 <= AIMGR_LO \/ AIMGR_LO + AIMGR_N <= TB)
    /\ (TB + 0x38e000 <= ASHR_LO \/ ASHR_LO + ASHR_N <= TB).
  Proof.
    intros m TB (C & L & AL & CE & KO & B1 & B2). acb.
    assert (KO' : (AIMG_TOP <= TB /\ TB + 0x38e000 <= ALOWSH_LO) \/ (AHI_LO <= TB /\ TB + 0x38e000 <= aceil))
      by (destruct KO as [K|K]; [left | right]; exact K).
    unfold AIMG_TOP, ALOWSH_LO, AHI_LO in KO'.
    destruct B1 as [[_ BA1] WA1]. destruct B2 as [[_ BA2] WA2].
    repeat split.
    - destruct BA1 as (_ & _ & X). specialize (X (Z.to_nat i) ltac:(cbn [cells_bytes cbytes]; rewrite app_nil_r, repeat_length; lia)).
      cbn [cells_bytes cbytes] in X. rewrite app_nil_r, nth_error_repeat in X by lia.
      unfold mrd in X. rewrite Z2Nat.id in X by lia. unfold wa in X.
      destruct (m _) eqn:EM; [exact X|]. change asegs with RSEGS in X.
      rewrite (aseg_rom_high _) in X; [discriminate | rewrite u64_lit by lia; lia].
    - destruct BA2 as (_ & _ & X). specialize (X (Z.to_nat i) ltac:(cbn [cells_bytes cbytes]; rewrite app_nil_r, repeat_length; lia)).
      cbn [cells_bytes cbytes] in X. rewrite app_nil_r, nth_error_repeat in X by lia.
      unfold mrd in X. rewrite Z2Nat.id in X by lia. unfold wa in X.
      destruct (m _) eqn:EM; [exact X|]. change asegs with RSEGS in X.
      rewrite (aseg_rom_high _) in X; [discriminate | rewrite u64_lit by lia; lia].
    - apply astore_ok_of_wview; [rewrite u64_lit by lia; lia|]. intros j Hj. rewrite <- wa_eq. rewrite u64_lit in * by lia.
      cbn [cells_size csize] in WA1. destruct WA1 as (_ & _ & W). replace (TB + 0x14dc00 + d + j) with (TB + 0x14dc00 + (d + j)) by lia.
      apply W. lia.
    - apply astore_ok_of_wview; [rewrite u64_lit by lia; lia|]. intros j Hj. rewrite <- wa_eq. rewrite u64_lit in * by lia.
      cbn [cells_size csize] in WA2. destruct WA2 as (_ & _ & W). replace (TB + 0x224ac0 + d + j) with (TB + 0x224ac0 + (d + j)) by lia.
      apply W. lia.
    - exact (cell_of_C8 m 0x18ef48 TB C).
    - unfold ATB_LO. lia.
    - unfold ATB_HI. lia.
    - unfold AIMGR_LO, AIMGR_N. lia.
    - unfold ASHR_LO, ASHR_N. lia.
  Qed.

  Theorem exitA_intro : forall m (sp : word) tid can TB,
    mem_inv asegs m -> arelro_none m -> aglb_none m -> ACONST m ->
    cells_ok m xdrv2 -> cells_ok m xk_atxU -> cells_ok m astdout0 ->
    atid_cell m tid -> acanary m can ->
    ahm_ok m TB -> TB + 0x38e000 + 4194304 <= bv_unsigned sp ->
    (forall a, 2147450880 + (bv_unsigned sp - 4096) / 8 <= a < 2147450880 + bv_unsigned sp / 8 -> m (Z_to_bv 64 a) = Some (Z_to_bv 8 0)) ->
    exitA m sp tid can TB.
  Proof.
    intros m sp tid can TB INV RELRO [G1 G2] AC CD CA CO [TID Ht] [CAN Hc] AH HSP SHS.
    pose proof (ahm_bytes m TB AH) as (Z1 & W1 & TBC & TBR & TBI & TBS).
    pose proof AH as (_ & _ & TBAL & _).
    split; try assumption.
    - lia.
    - exact (amem_inv_ro_none m INV).
    - exact (cell_of_C8 m ASHW_LCXXMB 0 (proj2 (proj2 (proj2 (proj2 (proj2 (ACONST_exit_v5 m AC))))))).
    - intros a n Ha Hn. pose proof (ACONST_imgvis m AC) as SV.
      change (sh AIMG_LO) with 0x7fffa000 in SV. change (sh AIMG_TOP) with 0x800d4c00 in SV.
      eapply stk_store_okX; [exact SV | lia | lia | lia].
    - apply xk_rest_of; try assumption; [split; assumption|].
      apply (cells_ok_incl_b m xk_out4 astdout0); [vm_compute; reflexivity | exact CO].
    - apply (cells_ok_incl_b m xk_Uout (xk_atxU ++ astdout0)); [vm_compute; reflexivity | apply cells_ok_app2; assumption].
  Qed.

  Theorem axA_intro : forall m (sp : word) tid can TB,
    bv_unsigned sp mod 16 = 0 -> ASP_LO <= bv_unsigned sp -> bv_unsigned sp <= ASP_HI -> stk_ok RSEGS m sp 2560 ->
    mem_inv asegs m -> arelro_none m -> aglb_none m -> ACONST m ->
    cells_ok m xdrv2 -> cells_ok m xk_err6 -> cells_ok m xk_out4 ->
    atid_cell m tid -> acanary m can ->
    ahm_ok m TB -> TB + 0x38e000 + 2560 <= bv_unsigned sp ->
    (forall a, 2147450880 + (bv_unsigned sp - 4096) / 8 <= a < 2147450880 + bv_unsigned sp / 8 -> m (Z_to_bv 64 a) = Some (Z_to_bv 8 0)) ->
    axA m sp tid can TB.
  Proof.
    intros m sp tid can TB H16 HLO HHI STK INV RELRO [G1 G2] AC CD CE CO [TID Ht] [CAN Hc] AH HSP SHS.
    pose proof (ahm_bytes m TB AH) as (Z1 & W1 & TBC & TBR & TBI & TBS).
    pose proof AH as (_ & _ & TBAL & _).
    split; try assumption.
    - lia.
    - exact (amem_inv_ro_none m INV).
    - exact (cell_of_C8 m ASHW_LCXXMB 0 (proj2 (proj2 (proj2 (proj2 (proj2 (ACONST_exit_v5 m AC))))))).
    - intros a n Ha Hn. pose proof (ACONST_imgvis m AC) as SV.
      change (sh AIMG_LO) with 0x7fffa000 in SV. change (sh AIMG_TOP) with 0x800d4c00 in SV.
      eapply stk_store_okX; [exact SV | lia | lia | lia].
    - apply xk_common_of; try assumption. split; assumption.
  Qed.
End Intro.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
