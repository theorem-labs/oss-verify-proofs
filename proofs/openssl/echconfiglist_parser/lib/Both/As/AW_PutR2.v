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
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.As Require Import ASegs AsShadow AllocKit AllocRep AllocWalkKit AsDepotInv AW_MallocBase AW_PutR1 AW_EnqueueR1 AllocTacX.
Import ListNotations.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.As Require Import AllocStoreDj.   (* [comment removed for export] *)
Local Ltac transport_chunks segs m a bs ::= transport_chunks_rx8 segs m a bs.   (* [comment removed for export] *)
Open Scope bv_scope.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Unset Keyed Unification.

Section HCW.
  Context {HCEIL : HeapCeil}.
  (* [comment removed for export] *)
  Variables (sp cs0 cs2 cs3 cs4 cs5 : word).
  Variables (gp tp s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
  Variables (lo : Z).
  Hypothesis LO : aceil <= lo.  Hypothesis HI : lo + 2576 <= bv_unsigned sp.
  Hypothesis SPT : bv_unsigned sp + 16 <= 2^47.

  (* [comment removed for export] *)
  Definition put_retR_post (U : Z) (m : mem) : machine_state -> Prop := fun ms' =>
    exists (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
    ms' = MS (mkR (wz 0x197a10) (Z_to_bv 64 (bv_unsigned sp + -2208)) gp tp t0 t1 t2 cs0 (wz U) a0 a1 a2 a3 a4 a5 a6 a7 cs2 cs3 cs4 cs5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 0x197a10) fc None m (seg_rom asegs)
    /\ stk asegs m lo (bv_unsigned sp + -2208).

  Section PutTailR.
    Variables (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m : mem).
    Variables (U size TH qcache : Z) (k f la qbytes : Z).
    Hypothesis MI : mem_inv asegs m.
    Hypothesis THR : hidden (akobj TH 4096 /\ TH + 4096 <= aceil).
    Hypothesis QCR : 0 <= qcache < 2^64. Hypothesis QB : 0 <= qbytes <= qcache.
    Hypothesis ST  : stk asegs m lo (bv_unsigned sp + -2288).
    Hypothesis PFR : rw_cells asegs m (bv_unsigned sp + -2288) (put_frameR sp cs0 cs2 cs3 cs4 cs5 s6 U TH).
    Hypothesis TQ  : rw_cells asegs m (TH + OT_TQ) [C8 (wz k); C8 (wz f); C8 (wz la); C8 (wz qbytes)].

    Theorem put_tailR :
      evt asegs (put_retR_post U m)
        (MS (enq_regsR sp gp tp s7 s8 s9 s10 s11 U size TH qcache t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6)
            F (Z_to_bv 64 0x19b46c) fc None m (seg_rom asegs)).
    Proof.
      pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64)%Z in SPR.
      assert (BND : aceil <= lo /\ 4096 <= TH /\ TH + 4096 <= aceil) by (clear - LO THR; destruct THR as [THR']; unfold AHI_LO in *; aunf; lia).
    region_sides. name_bands.
      unfold enq_regsR, put_frameR, AINST, OI_Q, OT_TQ, OT_CACHE, wz in *.
      (* [comment removed for export] *)
      step. step. if_cases K; zify_cond K. { exfalso. rewrite ?unsigned_lit in K by lia. lia. } clear K.
      step.
      (* [comment removed for export] *)
      do 8 step. step. step.
      release_frame PFR ST (bv_unsigned sp + -2208).
      replace (ret_pc (Z_to_bv 64 1669648)) with (Z_to_bv 64 1669648) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
      apply evt_done. unfold put_retR_post. do 15 eexists. split; [reflexivity| exact ST].
    Qed.
  End PutTailR.
End HCW.
