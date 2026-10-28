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
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import LbB_PrsStmt LbB_DStat LbB_DiagStmt.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require RtB_Td.
Import ListNotations.
Open Scope Z_scope.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.

Definition EX_FRAME : Z := 128.
Definition EX_SAVED : Z := 104.
Definition EX_FLAGP : Z := 504.
Definition EX_DS_OFF : Z := 32.

Definition AEX_STACK : Z := ADS_STACK + 1024.

Definition EX_FRAMES : nat := S DS_FRAMES.

Definition EX_COST : Z := 2 ^ 20.

Section Inv.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.

  Definition XE (ff fp : Z) : list (Z * Z) :=
    [(as_FSB H, as_FSB H + AFS_FLAGS); (fp, fp + 1); (ff, ff + fsz 3); (sh ff, sh ff + fshn 3)].

  Record xent : Type := XEnt {
    x_ra : word; x_sp : word; x_gp : word; x_tp : word;
    x_s0 : word; x_s1 : word; x_s2 : word; x_s3 : word; x_s4 : word; x_s5 : word;
    x_s6 : word; x_s7 : word; x_s8 : word; x_s9 : word; x_s10 : word; x_s11 : word;
    x_F : bvmap 5 word; x_fc : bv 32; x_m : mem; x_mo : Model;
    x_s : as_St H; x_LB : list block; x_LF : list fframe; x_CH : list (Z * Z);
    x_this : Z; x_pcons : Z; x_nwords : Z; x_widx : Z; x_icount : Z; x_ioff : Z; x_opc : Z; x_ty : Z;
    x_lo : Z; x_B : Z; x_shi : Z }.

  Definition xSP (e : xent) : Z := bv_unsigned (x_sp e).

  Definition xS1 (e : xent) : Z := xSP e - EX_FRAME - xSP e mod 32.

  Definition xsaved (e : xent) : list cell :=
    [C8 (x_s11 e); C8 (x_s10 e); C8 (x_s9 e); C8 (x_s8 e); C8 (x_s7 e); C8 (x_s6 e); C8 (x_s5 e); C8 (x_s4 e); C8 (x_s3 e);
     C8 (x_s2 e); C8 (x_s1 e); C8 (x_s0 e); C8 (x_ra e)].

  Definition xpre (e : xent) : Prop :=
    let m := x_m e in let LB := x_LB e in let SP := xSP e in
       FPSteps.frm_zero (x_fc e)
    /\ as_RHEAP H (x_s e) LB m
    /\ lb_small LB + 3 * 64512 <= RT_SMALL_MAX /\ Z.of_nat (length LB) + 3 <= RT_CNT_MAX /\ nlarge LB + 3 <= RT_LARGE_MAX
    /\ as_rauxv_ok H m (x_B e) /\ SP <= x_B e /\ x_B e < 2 ^ 64
    /\ SP mod 16 = 0 /\ stk asegs m (x_lo e) SP /\ aceil <= x_lo e /\ x_lo e <= SP - AEX_STACK
    /\ (exists errv, rw_cells asegs m (errno_addr (x_tp e)) [C4 errv]) /\ mem_inv asegs m /\ x_tp e = Z_to_bv 64 ATP
    /\ bv_unsigned (x_ra e) mod 2 = 0
    /\ LINV_P5 m /\ ACONST m
    /\ as_RFS H (x_LF e) m /\ (length (x_LF e) + EX_FRAMES <= AFS_MAXLIVE_BP)%nat
    /\ stack0 m (x_lo e) (x_shi e) /\ SP <= x_shi e
    /\ as_chain H m (bv_unsigned (x_s0 e)) (x_CH e) /\ pf_ok (as_TR H) DS_EXH_PF (bv_unsigned (x_ra e)) (x_CH e)
    /\ (forall fp' ra', In (fp', ra') (x_CH e) -> SP + 16 <= fp')
    /\ ds_tr_ok H
    /\ EX_COST <= as_AL H (x_s e)

    /\ 0 <= x_ioff e < 2 ^ 63 /\ 0 <= x_opc e < 2 ^ 16 /\ 0 <= x_ty e < 2 ^ 32
    /\ ds_obj H (x_LF e) m SP (x_this e) 288
    /\ rw_cells asegs m (x_this e + 8) [C8 (Z_to_bv 64 (x_pcons e))] /\ rw_cells asegs m (x_this e + 56) [C8 (Z_to_bv 64 (x_nwords e))]
    /\ rw_cells asegs m (x_this e + 72) [C8 (Z_to_bv 64 (x_widx e))] /\ rw_cells asegs m (x_this e + 80) [C8 (Z_to_bv 64 (x_icount e))]
    /\ 0 <= x_nwords e < 2 ^ 63 /\ 0 <= x_widx e < 2 ^ 63 /\ 0 <= x_icount e < 2 ^ 63
    /\ ds_obj H (x_LF e) m SP (x_pcons e) 48 /\ rw_cells asegs m (x_pcons e + 32) [C8 (Z_to_bv 64 0)]
    /\ x_pcons e mod 16 = 0.

  Definition xinv (e : xent) (ff fp : Z) (XSc : list (Z * Z)) (sk : as_St H) (LBk : list block) (m' : mem) : Prop :=
       as_RFS H ((3, ff, fp) :: x_LF e) m' /\ fresh_frame H (x_LF e) 3 ff fp
    /\ as_RHEAP H sk LBk m' /\ ACONST m' /\ mem_inv asegs m'
    /\ stack0 m' (x_lo e) (x_shi e) /\ as_rauxv_ok H m' (x_B e)
    /\ (exists errv', rw_cells asegs m' (errno_addr (x_tp e)) [C4 errv'])
    /\ stk asegs m' (x_lo e) (xSP e)
    /\ rw_cells asegs m' (xSP e - EX_SAVED) (xsaved e)
    /\ rw_cells asegs m' (ff + EX_FLAGP) [C8 (Z_to_bv 64 fp)]
    /\ wr_at asegs m' ff EX_FLAGP /\ wr_at asegs m' fp 1
    /\ xpres H (x_LB e) (xSP e) ((RtB_Td.ATDLOC, RtB_Td.ATDLOC + 8) :: XE ff fp ++ XSc) (x_m e) m'
    /\ Forall (fs_scratch H (x_LF e)) XSc
    /\ LINV_P5 m'.
End Inv.
Arguments x_ra {H} _.
Arguments x_sp {H} _.
Arguments x_gp {H} _.
Arguments x_tp {H} _.
Arguments x_s0 {H} _.
Arguments x_s1 {H} _.
Arguments x_s2 {H} _.
Arguments x_s3 {H} _.
Arguments x_s4 {H} _.
Arguments x_s5 {H} _.
Arguments x_s6 {H} _.
Arguments x_s7 {H} _.
Arguments x_s8 {H} _.
Arguments x_s9 {H} _.
Arguments x_s10 {H} _.
Arguments x_s11 {H} _.
Arguments x_F {H} _.
Arguments x_fc {H} _.
Arguments x_m {H} _.
Arguments x_mo {H} _.
Arguments x_s {H} _.
Arguments x_LB {H} _.
Arguments x_LF {H} _.
Arguments x_CH {H} _.
Arguments x_this {H} _.
Arguments x_pcons {H} _.
Arguments x_nwords {H} _.
Arguments x_widx {H} _.
Arguments x_icount {H} _.
Arguments x_ioff {H} _.
Arguments x_opc {H} _.
Arguments x_ty {H} _.
Arguments x_lo {H} _.
Arguments x_B {H} _.
Arguments x_shi {H} _.
Arguments xSP {H} e.
Arguments xS1 {H} e.
Arguments xsaved {H} e.
