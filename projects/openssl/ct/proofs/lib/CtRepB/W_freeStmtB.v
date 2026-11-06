(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.openssl.ct.lib.CtLib Require Import ImageCtA.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.openssl.ct.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP Frame Cells Step Mem RzCPS. 
From OSSVerify.Proofs.openssl.ct.lib.Malloc Require Import MallocRep MallocBlocks Malloc_iface.
From OSSVerify.Proofs.openssl.ct.lib.Spec Require Import Prelim Malloc Prog BnBase BnModel BnTree ApBase ApLogic ApErr.
From OSSVerify.Proofs.openssl.ct.lib.A Require Import Shadow.
From OSSVerify.Proofs.openssl.ct.lib.CtB Require Import Layout RT_iface RT_client_kit D_defs D_cs I_lkit.
From OSSVerify.Proofs.openssl.ct.lib.BnBoth Require Import AsKit AsLoop.
From OSSVerify.Proofs.openssl.ct.lib.CtKitB Require Import RT_iface2 LibKitA ARun BnHeapA ImplA BnIfaceA AsStruct.
From OSSVerify.Proofs.openssl.ct.lib.CtRepP Require Import ApCells.
From OSSVerify.Proofs.openssl.ct.lib.CtRepB Require Import ApBImg ApWalkTac ApRepDefs ApRep ApIface W_item_d2i_imgA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Definition ITEM_EX_FREE_A : Z := 0x246d80.
(* [comment removed for export] *)
Definition ITEM_EX_FREE_STACK_A : Z := 176.
Definition ASN1_TYPE_FREE_A : Z := 0x24a2c0.
(* [comment removed for export] *)
Definition TFN_STACK_A : Z := 16 + 128 + 128 + 32 + RT_STACK.

(* [comment removed for export] *)
Definition item_ex_free_null_specA : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (lo PVAL IT w PB PBn : Z) (shb : shb_cells ctbsegs A_GOT_SHB A_SHB_CELL m -> Prop) (POST : machine_state -> Prop),
    stk ctbsegs m lo (bv_unsigned sp) -> SHHI <= lo -> lo <= bv_unsigned sp - ITEM_EX_FREE_STACK_A -> bv_unsigned sp + 16 <= USTACK_TOP -> mem_inv ctbsegs m ->
    shb_cells ctbsegs A_GOT_SHB A_SHB_CELL m ->
    acc ctbsegs m PB PBn -> PB <= PVAL -> PVAL + 8 <= PB + PBn -> 0 < PB -> PB + PBn <= lo -> (PB + PBn <= SHLO \/ SHHI <= PB) -> PVAL mod 8 = 0 ->
    rw_cells ctbsegs m PVAL [C8 (Z_to_bv 64 0)] ->
    item_cellsA m IT w -> 0 < IT -> IT + 56 <= SHLO -> IT mod 8 = 0 -> bv_unsigned (sx32 (Z_to_bv 64 w)) <> 1 ->
    a0 = wz PVAL -> a1 = wz IT ->
    (forall (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : mem),
       munch [(bv_unsigned sp - ITEM_EX_FREE_STACK_A, bv_unsigned sp)]%Z m m' -> wmono ctbsegs m m' -> mem_inv ctbsegs m' -> stk ctbsegs m' lo (bv_unsigned sp) ->
       evt ctbsegs POST
         (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
             F (ret_pc ra) fc None m' (seg_rom ctbsegs))) ->
    evt ctbsegs POST
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz ITEM_EX_FREE_A) fc None m (seg_rom ctbsegs)).

Section WithRT0.
Context {AR : ARun}.
Local Notation RT := (@ar_RT AR).
Local Notation PMc := (@ar_PMc AR).
Local Notation FR := (@ar_FR AR).
Local Notation ACEIL := (@BnHeapA.ACEIL AR).
Local Notation AHEAP := (@BnHeapA.AHEAP AR).

(* [comment removed for export] *)
Definition tfree_null_postA (ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (Σ : rts RT) (OW LB : list block) (lo : Z) (m : mem)
    (Σ1 : rts RT) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 (F' : bvmap 5 word) (fc' : bv 32) m',
    ms' = MS (mkR ra sp gp (wz TP_A) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F' (ret_pc ra) fc' None m' (seg_rom ctbsegs)
    /\ AHEAP Σ1 OW LB m' /\ rt_credit RT Σ - 1 <= rt_credit RT Σ1 /\ stk ctbsegs m' lo (bv_unsigned sp) /\ mem_inv ctbsegs m'
    /\ agree_on (aclient_addr (OW ++ LB) (bv_unsigned sp)) m m'.

Definition type_free_null_specA : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (Σ : rts RT) (OW LB : list block) (lo : Z),
    AHEAP Σ OW LB m -> stk ctbsegs m lo (bv_unsigned sp) -> ACEIL <= lo -> lo + TFN_STACK_A <= bv_unsigned sp ->
    bv_unsigned sp + 16 <= USTACK_TOP -> bv_unsigned sp mod 16 = 0 -> mem_inv ctbsegs m -> tp = wz TP_A ->
    (length FR < FRAMES_MAX)%nat -> 1 <= rt_credit RT Σ -> a0 = wz 0 ->
    cps ctbsegs (ASTA RT Σ PMc (eq (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                     F (wz ASN1_TYPE_FREE_A) fc None m (seg_rom ctbsegs))))
        (fun c => exists Σ1, ASTA RT Σ1 PMc (tfree_null_postA ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 Σ OW LB lo m Σ1) c
                             /\ rt_live RT Σ1 = rt_live RT Σ).
End WithRT0.
