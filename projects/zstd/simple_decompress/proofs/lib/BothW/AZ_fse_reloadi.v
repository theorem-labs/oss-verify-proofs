(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Spec Require Import FseNCount FseLemmas ZdFrame ZdFrameThm ZdDCtx ZdSeqTable.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Lib Require Import Tac Arr Bytes ZBridge.
From OSSVerify.Proofs.zstd.simple_decompress.lib.LibA Require Import ExecF StepF Shadow.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Common Require Import FseWalkKit MemRange ZdSeqW ZdTbl KXExec KXSound KXFull KXBridge KXTac KXGo KXTree KXAuto KXMem KXMem2 KXPost KXGoF KXLean KXAsan KXAutoA KXUb KXUb2.
From OSSVerify.Proofs.zstd.simple_decompress.lib.BothW Require Import BImg RtCells ABase AZ_kit AZ_kx AZ_globals AZ_globalsR AZ_huf_iface.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Common Require Import RunDraw.
Import ListNotations. Import KXS.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Ltac kx_lia ::= kx_bv_ranges; first [ solve [lia] | solve [kx_lia_pruned] ].
Ltac kxa_norm ::= unfold shspan in *.
Notation FSE_RELOADI_STACK_A := 16 (only parsing).

Section CANSEC1. Context {rc : runConstT}.
Definition APFSE_RELOADI : Z := 0xb24fc.     (* [comment removed for export] *)

(* [comment removed for export] *)
Definition fse_reload_int_postA (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (SPV BD SRC bc ptr lo : Z) (pad : list byte) (m : amem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' cont',
    ms' = MS (mkR ra (Z_to_bv 64 SPV) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom bsegs)
    /\ munch [(BD, BD + 40); (SPV - FSE_RELOADI_STACK_A, SPV)] m m' /\ wmono bsegs m m' /\ mem_inv bsegs m' /\ stk bsegs m' lo SPV
    /\ rw_cells bsegs m' BD (bitd_cells cont' (Z_to_bv 64 (bc mod 8)) pad (ptr - bc / 8) SRC).

Definition fse_reload_int_stmtA : Prop :=
  forall (RNG : footprint) (ra gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : amem) (SPV lo BD SRC n bc ptr : Z) (cont : word) (pad src : list byte),
  rw_cells bsegs m BD (bitd_cells cont (Z_to_bv 64 bc) pad ptr SRC) -> bytes_at bsegs m SRC src -> zlen src = n ->
  4096 <= BD -> BD + 40 < 2^47 -> 4096 <= SRC -> SRC + n < 2^47 -> BD mod 8 = 0 ->
  (BD + 40 <= SRC \/ SRC + n <= BD) ->
  0 <= bc <= 64 -> SRC + 8 <= ptr -> ptr <= SRC + n - 8 ->
  stk bsegs m lo SPV -> lo <= SPV - FSE_RELOADI_STACK_A -> SPV < 2^47 ->
  (BD + 40 <= lo \/ SPV <= BD) -> (SRC + n <= lo \/ SPV <= SRC) ->
  (* [comment removed for export] *)
  app_blk BD (BD + 40) -> aro RNG m BD 40 -> aro RNG m SRC n -> art m -> astk RNG lo SPV ->
  mem_inv bsegs m ->
  evtF bsegs RNG (fse_reload_int_postA ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc SPV BD SRC bc ptr lo pad m)
      (MS (mkR ra (Z_to_bv 64 SPV) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 BD) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 APFSE_RELOADI) fc None m (seg_rom bsegs)).

Theorem fse_reload_int_proofA : fse_reload_int_stmtA.
Proof.
  unfold fse_reload_int_stmtA, APFSE_RELOADI. intros until src.
  intros HBD SQB En R1 R2 R3 R4 A1 DJ RB RPT RPT2 STK LOS SPB OS1 OS2 APB AROB AROQ ART AST MI.
  symmetry in En.
  unfold bitd_cells in HBD.
  destruct ART as (GOT & RIC & SHB & INI & LAY & REAL).
  destruct AST as (KLO & RSTK & RI). unfold KHIGH in KLO.
  destruct AROB as (UB & RGB & RGBS). destruct AROQ as (UQ & RGQ & RGQS).
  assert (BDB : BD + 40 <= 0x7fff8000 \/ 0x10007fff8000 <= BD) by (unfold app_blk, KLOW, KHIGH, KEND in APB; clear - APB; lia).
  assert (MU : munch [(BD, BD + 40); (SPV - 16, SPV)] m m) by apply munch_refl.
  assert (WM : wmono bsegs m m) by apply wmono_refl.
  assert (QR : exists q r d, bc = 8 * q + r /\ ptr = SRC + d /\ 0 <= q <= 8 /\ 0 <= r <= 7 /\ 8 <= d /\ d + 8 <= n)
    by (exists (bc / 8), (bc mod 8), (ptr - SRC); clear - RB RPT RPT2; lia).
  destruct QR as (q & r & d & -> & -> & Q1 & Q2 & Q3 & Q4).
  assert (EDIV : (8 * q + r) / 8 = q /\ (8 * q + r) mod 8 = r) by (clear - Q1 Q2; split; [symmetry; apply (Z.div_unique (8 * q + r) 8 q r); lia | symmetry; apply (Z.mod_unique (8 * q + r) 8 q r); lia]).
  destruct EDIV as (ED & EM).
  assert (RG : 4096 <= BD < 2^47 /\ 4096 <= SRC < 2^47 /\ 4096 <= SRC + n < 2^47 /\ 16 <= n < 2^47) by lia.
  carve_frame 16%nat STK.
  clear APB.
  kx_autoFA [KAUnp BD 40; KAUnp SRC n; KAApp BD 40; KAApp (SPV - 16) 16] (@nil Z) 150%nat
    [KZRange BD 4096 (2^47 - 40); KZRange SRC 4096 (2^47); KZRange (SRC + n) 4096 (2^47); KZRange n 16 (2^47); KZRange q 0 8; KZRange r 0 7; KZRange (8 * q + r) 0 64;
     KZRange d 8 (2^47); KZRange (d - q) 0 (2^47); KZRange (n - d) 8 (2^47); KZRange (n - d + q) 8 (2^47);
     KZRange SPV 4112 (2^47); KZAlign BD 8; KZWr BD 40; KZWr (SPV - 16) 16;
     KZDisj BD 40 SRC n; KZDisj (SPV - 16) 16 BD 40; KZDisj (SPV - 16) 16 SRC n]
    [(SRC, n); (SPV - 16, 16); (BD, 40)] [(BD, 40); (SPV - 16, 16)].
  all: try kx_cell_lit; try kx_z; try kx_acc RI; try kx_acc RGQ; try kx_acc RGB.
  all: lazymatch goal with |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0xb2624) _ _ _ _) => kx_trap_fast | _ => idtac end.
  all: kx_mem.
  all: zstep.
  all: kx_abs.
  all: release_frame FR STK SPV.
  all: kx_mkR_fold.
  all: (apply evtF_done; unfold fse_reload_int_postA, bitd_cells; repeat (lazymatch goal with |- ex _ => eexists end);
        split; [reflexivity|]; split; [eassumption|]; split; [eassumption|]; split; [eassumption|]; split; [eassumption|];
        rewrite ED, EM; replace (SRC + d - q) with (SRC + (-1 * q + d)) by lia;
        match goal with H : rw_cells _ _ ?B (C8 _ :: C4 _ :: _) |- rw_cells _ _ ?B2 _ => constr_eq B B2; exact H end).
Qed.
End CANSEC1.
