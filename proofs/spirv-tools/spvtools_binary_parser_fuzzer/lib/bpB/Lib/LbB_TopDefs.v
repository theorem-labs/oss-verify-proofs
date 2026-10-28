(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BeapCeil.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BTac BArr BSysStep BExec BellsX BacX BMem BMState BLFrame.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BPrelim.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BSegs BsShadow BsConst BsIface BsCXXHeap BXXRep BsStack0 RtB_Iface.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require FPSteps.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require RtB_Td.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import DvB_FuzzStmt LbB_PrsStmt LbB_DStat.
Import ListNotations.
Open Scope Z_scope.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.

Definition TOP_PO_RA : Z := 0xe8c10.
Definition TOP_CD_RA : Z := 0xe8c18.
Definition TOP_VD_RA : Z := 0xe8c28.

Definition TOP_PF : list (Z * list Z) :=
  [(APC0_FREE, [TOP_CD_RA]); (APC0_FREE, [TOP_VD_RA])] ++ pf_shift TOP_PO_RA PO_PF.

Definition top_cost (N : Z) : Z := ICM 64 + ICM (4 * (N / 4)) + po_cost (N / 4).

Definition TOP_SMALL : Z := 64 + 64512 + po_small (2 ^ 24).
Definition TOP_CNT : Z := 2 + po_cnt (2 ^ 24).
Definition TOP_LARGE : Z := 1 + po_large (2 ^ 24).

Definition FZP_A : fuzz_params :=
  {| fz_cost := top_cost; fz_tr_ok := po_tr_ok; fz_pf := TOP_PF; fz_inv := LINV_P5;
     fz_small := TOP_SMALL; fz_cnt := TOP_CNT; fz_large := TOP_LARGE |}.

Lemma ICM_nonneg : forall n, 0 <= n -> 0 <= ICM n.
Proof. intros n Hn. unfold ICM. destruct (Z.leb_spec n 64512); lia. Qed.
Lemma ICM_mono : forall n n', 0 <= n <= n' -> ICM n <= ICM n'.
Proof. intros n n' Hn. unfold ICM. destruct (Z.leb_spec n 64512), (Z.leb_spec n' 64512); lia. Qed.

Lemma top_cost_nonneg : forall n, 0 <= n -> 0 <= top_cost n.
Proof.
  intros n Hn. unfold top_cost. pose proof (ICM_nonneg 64 ltac:(lia)).
  pose proof (ICM_nonneg (4 * (n / 4)) ltac:(Z.div_mod_to_equations; lia)). unfold po_cost. lia.
Qed.
Lemma top_cost_mono : forall n n', 0 <= n <= n' -> top_cost n <= top_cost n'.
Proof.
  intros n n' Hn. unfold top_cost.
  assert (n / 4 <= n' / 4) by (apply Z.div_le_mono; lia).
  pose proof (ICM_mono (4 * (n / 4)) (4 * (n' / 4)) ltac:(Z.div_mod_to_equations; lia)). unfold po_cost. lia.
Qed.

Lemma FZP_A_ok : fz_params_ok FZP_A.
Proof.
  unfold fz_params_ok, fz_cost_nonneg, fz_cost_mono. cbn [fz_cost fz_small fz_cnt fz_large FZP_A].
  split; [exact top_cost_nonneg|]. split; [exact top_cost_mono|].
  unfold TOP_SMALL, TOP_CNT, TOP_LARGE, po_small, po_cnt, po_large, RT_SMALL_MAX, RT_CNT_MAX, RT_LARGE_MAX.
  vm_compute. repeat split; discriminate.
Qed.

Lemma FZP_A_pcost : 4 * fz_cost FZP_A (2 ^ 26) <= 2 ^ 38.
Proof. cbn [fz_cost FZP_A]. unfold top_cost, ICM, po_cost. vm_compute. discriminate. Qed.

Definition TOP_FCLASS : Z := 6.
Definition TOP_FSIZE : Z := 2752.
Definition TOP_OBJ_OFF : Z := 32.
Definition TOP_VEC_OFF : Z := 2672.

Section Inv.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.

  Definition XH (ff fp : Z) : list (Z * Z) :=
    [(as_FSB H, as_FSB H + AFS_FLAGS); (fp, fp + 1); (ff, ff + fsz 6); (sh ff, sh ff + fshn 6)].

  Record hent : Type := HEnt {
    e_ra : word; e_sp : word; e_gp : word; e_tp : word;
    e_s0 : word; e_s1 : word; e_s2 : word; e_s3 : word; e_s4 : word; e_s5 : word;
    e_s6 : word; e_s7 : word; e_s8 : word; e_s9 : word; e_s10 : word; e_s11 : word;
    e_F : bvmap 5 word; e_fc : bv 32; e_m : mem; e_mo : Model;
    e_s : as_St H; e_LB : list block; e_LF : list fframe; e_CH : list (Z * Z);
    e_D : Z; e_N : Z; e_lo : Z; e_B : Z; e_shi : Z; e_ds : list byte }.

  Definition eSP (e : hent) : Z := bv_unsigned (e_sp e).

  Definition eS1 (e : hent) : Z := eSP e - 224 - eSP e mod 32.

  Definition esaved (e : hent) : list cell :=
    [C8 (e_s11 e); C8 (e_s10 e); C8 (e_s9 e); C8 (e_s8 e); C8 (e_s7 e); C8 (e_s6 e); C8 (e_s5 e); C8 (e_s4 e); C8 (e_s3 e);
     C8 (e_s2 e); C8 (e_s1 e); C8 (e_s0 e); C8 (e_ra e)].

  Definition top_fr (A ff : Z) : list cell :=
    [C8 (wz A); C8 (wz (sh ff + 4)); C8 (wz ff); C8 (wz (sh ff)); C8 (wz ff)].

  Definition top_vd (ff D : Z) : list cell := [C8 (wz (ff + 2672)); C8 (wz D)].

  Definition hpre (e : hent) : Prop :=
    let m := e_m e in let D := e_D e in let N := e_N e in let LB := e_LB e in let SP := eSP e in
       FPSteps.frm_zero (e_fc e)
    /\ bytes_at asegs m D (e_ds e) /\ Z.of_nat (length (e_ds e)) = N /\ 0 <= N < 2 ^ 26 /\ D mod 16 = 0
    /\ (1 <= N -> exists pD, In (pD, D, N) LB) /\ (N = 0 -> D = AFUZZ_EMPTY)
    /\ as_RHEAP H (e_s e) LB m
    /\ lb_small LB + TOP_SMALL <= RT_SMALL_MAX /\ Z.of_nat (length LB) + TOP_CNT <= RT_CNT_MAX
    /\ nlarge LB + TOP_LARGE <= RT_LARGE_MAX
    /\ as_rauxv_ok H m (e_B e) /\ SP <= e_B e /\ e_B e < 2 ^ 64
    /\ SP mod 16 = 0 /\ stk asegs m (e_lo e) SP /\ aceil <= e_lo e /\ e_lo e <= SP - AFUZZ_STACK
    /\ (exists errv, rw_cells asegs m (errno_addr (e_tp e)) [C4 errv]) /\ mem_inv asegs m /\ e_tp e = Z_to_bv 64 ATP
    /\ LINV_P5 m /\ bv_unsigned (e_ra e) mod 2 = 0 /\ ACONST m
    /\ (1 <= N -> addressable m D N)
    /\ as_RFS H (e_LF e) m /\ (length (e_LF e) + 16 <= AFS_MAXLIVE_BP)%nat
    /\ stack0 m (e_lo e) (e_shi e) /\ SP <= e_shi e
    /\ as_chain H m (bv_unsigned (e_s0 e)) (e_CH e) /\ pf_ok (as_TR H) TOP_PF (bv_unsigned (e_ra e)) (e_CH e)
    /\ (forall fp' ra', In (fp', ra') (e_CH e) -> SP + 16 <= fp')
    /\ top_cost N <= as_AL H (e_s e).

  Definition hinv (e : hent) (ff fp : Z) (XSc : list (Z * Z)) (sk : as_St H) (LBk : list block) (m' : mem) : Prop :=
       as_RFS H ((6, ff, fp) :: e_LF e) m' /\ fresh_frame H (e_LF e) 6 ff fp
    /\ as_RHEAP H sk LBk m' /\ ACONST m' /\ mem_inv asegs m'
    /\ stack0 m' (e_lo e) (e_shi e) /\ as_rauxv_ok H m' (e_B e)
    /\ (exists errv', rw_cells asegs m' (errno_addr (e_tp e)) [C4 errv'])
    /\ stk asegs m' (e_lo e) (eSP e)
    /\ rw_cells asegs m' (eSP e - 104) (esaved e)
    /\ rw_cells asegs m' (ff + 4088) [C8 (Z_to_bv 64 fp)]
    /\ wr_at asegs m' ff 8
    /\ xpres H (e_LB e) (eSP e) ((RtB_Td.ATDLOC, RtB_Td.ATDLOC + 8) :: XH ff fp ++ XSc) (e_m e) m'
    /\ Forall (fs_scratch H (e_LF e)) XSc
    /\ LINV_P5 m'.
End Inv.
Arguments e_ra {H} _.
Arguments e_sp {H} _.
Arguments e_gp {H} _.
Arguments e_tp {H} _.
Arguments e_s0 {H} _.
Arguments e_s1 {H} _.
Arguments e_s2 {H} _.
Arguments e_s3 {H} _.
Arguments e_s4 {H} _.
Arguments e_s5 {H} _.
Arguments e_s6 {H} _.
Arguments e_s7 {H} _.
Arguments e_s8 {H} _.
Arguments e_s9 {H} _.
Arguments e_s10 {H} _.
Arguments e_s11 {H} _.
Arguments e_F {H} _.
Arguments e_fc {H} _.
Arguments e_m {H} _.
Arguments e_mo {H} _.
Arguments e_s {H} _.
Arguments e_LB {H} _.
Arguments e_LF {H} _.
Arguments e_CH {H} _.
Arguments e_D {H} _.
Arguments e_N {H} _.
Arguments e_lo {H} _.
Arguments e_B {H} _.
Arguments e_shi {H} _.
Arguments e_ds {H} _.
Arguments eSP {H} e.
Arguments eS1 {H} e.
Arguments esaved {H} e.
