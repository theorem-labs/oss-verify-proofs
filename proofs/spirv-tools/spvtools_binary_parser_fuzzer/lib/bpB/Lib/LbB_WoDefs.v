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
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import LbB_PrsStmt LbB_DStat.
Import ListNotations.
Open Scope Z_scope.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.

Definition WO_FRAME : Z := 192.
Definition WO_SAVED : Z := 104.
Definition WO_FLAGP : Z := 4088.
Definition WO_T_OFF : Z := 72.
Definition WO_ST_OFF : Z := 176.
Definition WO_CONS_OFF : Z := 48.

Section Inv.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.

  Definition XW (ff fp : Z) : list (Z * Z) :=
    [(as_FSB H, as_FSB H + AFS_FLAGS); (fp, fp + 1); (ff, ff + fsz 6); (sh ff, sh ff + fshn 6)].

  Record went : Type := WEnt {
    w_ra : word; w_sp : word; w_gp : word; w_tp : word;
    w_s0 : word; w_s1 : word; w_s2 : word; w_s3 : word; w_s4 : word; w_s5 : word;
    w_s6 : word; w_s7 : word; w_s8 : word; w_s9 : word; w_s10 : word; w_s11 : word;
    w_F : bvmap 5 word; w_fc : bv 32; w_m : mem; w_mo : Model;
    w_s : as_St H; w_LB : list block; w_LF : list fframe; w_CH : list (Z * Z);
    w_ctx : Z; w_env : Z; w_words : Z; w_n : Z; w_lo : Z; w_B : Z; w_shi : Z }.

  Definition wSP (e : went) : Z := bv_unsigned (w_sp e).

  Definition wS1 (e : went) : Z := wSP e - WO_FRAME - wSP e mod 32.

  Definition wsaved (e : went) : list cell :=
    [C8 (w_s11 e); C8 (w_s10 e); C8 (w_s9 e); C8 (w_s8 e); C8 (w_s7 e); C8 (w_s6 e); C8 (w_s5 e); C8 (w_s4 e); C8 (w_s3 e);
     C8 (w_s2 e); C8 (w_s1 e); C8 (w_s0 e); C8 (w_ra e)].

  Definition wpre (e : went) : Prop :=
    let m := w_m e in let n := w_n e in let LB := w_LB e in let SP := wSP e in
       FPSteps.frm_zero (w_fc e)
    /\ ctx_okA LB m (w_ctx e) (w_env e)
    /\ 0 <= n < 2 ^ 24 /\ ((w_words e = 0 /\ n = 0) \/ words_okA LB m (w_words e) n)
    /\ as_RHEAP H (w_s e) LB m
    /\ lb_small LB + po_small n <= RT_SMALL_MAX /\ Z.of_nat (length LB) + po_cnt n <= RT_CNT_MAX
    /\ nlarge LB + po_large n <= RT_LARGE_MAX
    /\ as_rauxv_ok H m (w_B e) /\ SP <= w_B e /\ w_B e < 2 ^ 64
    /\ SP mod 16 = 0 /\ stk asegs m (w_lo e) SP /\ aceil <= w_lo e /\ w_lo e <= SP - APO_STACK
    /\ (exists errv, rw_cells asegs m (errno_addr (w_tp e)) [C4 errv]) /\ mem_inv asegs m /\ w_tp e = Z_to_bv 64 ATP
    /\ bv_unsigned (w_ra e) mod 2 = 0
    /\ LINV_P5 m /\ ACONST m
    /\ as_RFS H (w_LF e) m /\ (length (w_LF e) + PO_FRAMES <= AFS_MAXLIVE_BP)%nat
    /\ stack0 m (w_lo e) (w_shi e) /\ SP <= w_shi e
    /\ as_chain H m (bv_unsigned (w_s0 e)) (w_CH e) /\ pf_ok (as_TR H) PO_PF (bv_unsigned (w_ra e)) (w_CH e)
    /\ (forall fp' ra', In (fp', ra') (w_CH e) -> SP + 16 <= fp')
    /\ po_cost n <= as_AL H (w_s e).

  Definition winv (e : went) (ff fp : Z) (XSc : list (Z * Z)) (sk : as_St H) (LBk : list block) (m' : mem) : Prop :=
       as_RFS H ((6, ff, fp) :: w_LF e) m' /\ fresh_frame H (w_LF e) 6 ff fp
    /\ as_RHEAP H sk LBk m' /\ ACONST m' /\ mem_inv asegs m'
    /\ stack0 m' (w_lo e) (w_shi e) /\ as_rauxv_ok H m' (w_B e)
    /\ (exists errv', rw_cells asegs m' (errno_addr (w_tp e)) [C4 errv'])
    /\ stk asegs m' (w_lo e) (wSP e)
    /\ rw_cells asegs m' (wSP e - WO_SAVED) (wsaved e)
    /\ rw_cells asegs m' (ff + WO_FLAGP) [C8 (Z_to_bv 64 fp)]
    /\ wr_at asegs m' ff WO_FLAGP /\ wr_at asegs m' fp 1
    /\ xpres H (w_LB e) (wSP e) ((RtB_Td.ATDLOC, RtB_Td.ATDLOC + 8) :: XW ff fp ++ XSc) (w_m e) m'
    /\ Forall (fs_scratch H (w_LF e)) XSc
    /\ LINV_P5 m'.
End Inv.
Arguments w_ra {H} _.
Arguments w_sp {H} _.
Arguments w_gp {H} _.
Arguments w_tp {H} _.
Arguments w_s0 {H} _.
Arguments w_s1 {H} _.
Arguments w_s2 {H} _.
Arguments w_s3 {H} _.
Arguments w_s4 {H} _.
Arguments w_s5 {H} _.
Arguments w_s6 {H} _.
Arguments w_s7 {H} _.
Arguments w_s8 {H} _.
Arguments w_s9 {H} _.
Arguments w_s10 {H} _.
Arguments w_s11 {H} _.
Arguments w_F {H} _.
Arguments w_fc {H} _.
Arguments w_m {H} _.
Arguments w_mo {H} _.
Arguments w_s {H} _.
Arguments w_LB {H} _.
Arguments w_LF {H} _.
Arguments w_CH {H} _.
Arguments w_ctx {H} _.
Arguments w_env {H} _.
Arguments w_words {H} _.
Arguments w_n {H} _.
Arguments w_lo {H} _.
Arguments w_B {H} _.
Arguments w_shi {H} _.
Arguments wSP {H} e.
Arguments wS1 {H} e.
Arguments wsaved {H} e.
