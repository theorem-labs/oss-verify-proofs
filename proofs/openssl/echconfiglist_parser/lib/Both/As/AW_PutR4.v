(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib Require Import HeapCeil.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import Tac Image ZBridge SysStep SFModel CellsX Arr TacX.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib Require Import AsanAllocModel.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.As Require Import ASegs AsShadow AllocKit AllocRep AllocWalkKit AsDepotInv AW_MallocBase AW_PutR1 AW_EnqueueR1 AW_PutR2 AW_Drain AllocTacX.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Unset Keyed Unification.

Section HCW.
  Context {HCEIL : HeapCeil}.
  Variables (sp cs0 cs2 cs3 cs4 cs5 : word).
  Variables (gp tp s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
  Variables (lo : Z).
  Hypothesis LO : aceil <= lo.  Hypothesis HI : lo + 2576 <= bv_unsigned sp.
  Hypothesis SPT : bv_unsigned sp + 16 <= 2^47.

  Theorem put_after_recycleR : forall (rax t0 t1 t2 x0 x1 a0 a1 a2 a3 a4 a5 a6 a7 x2 x3 x4 x5 x6 t3 t4 t5 t6 : word) (m : mem) (U TH : Z),
    mem_inv asegs m -> stk asegs m lo (bv_unsigned sp + -2288) ->
    rw_cells asegs m (bv_unsigned sp + -2288) (put_frameR sp cs0 cs2 cs3 cs4 cs5 s6 U TH) ->
    evt asegs (put_retR_post sp cs0 cs2 cs3 cs4 cs5 gp tp s6 s7 s8 s9 s10 s11 F fc lo U m)
      (MS (mkR rax (Z_to_bv 64 (bv_unsigned sp + -2288)) gp tp t0 t1 t2 x0 x1 a0 a1 a2 a3 a4 a5 a6 a7 x2 x3 x4 x5 x6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x19b3a4) fc None m (seg_rom asegs)).
  Proof.
    intros until m. intros U TH MI ST PFR.
    pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64)%Z in SPR. acb.
    unfold put_frameR, OT_TQ, OT_CACHE, wz in *.
    (* [comment removed for export] *)
    do 8 step. step. step.
    release_frame PFR ST (bv_unsigned sp + -2208).
    replace (ret_pc (Z_to_bv 64 1669648)) with (Z_to_bv 64 1669648) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    apply evt_done. unfold put_retR_post. do 15 eexists. split; [reflexivity| exact ST].
  Qed.
End HCW.
