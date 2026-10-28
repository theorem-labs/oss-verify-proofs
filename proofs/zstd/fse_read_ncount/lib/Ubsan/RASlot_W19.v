(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.fse_read_ncount.lib.Lib Require Import Tac Image ZBridge SysStep Walk ITree Nodes Decode Arr.
From OssFuzzTheorems.Proofs.zstd.fse_read_ncount.lib.Common Require Import SFModel.
From OssFuzzTheorems.Proofs.zstd.fse_read_ncount.lib.Ubsan Require Import UImgX.
From OssFuzzTheorems.Proofs.zstd.fse_read_ncount.lib.Malloc Require Import F_malloc_free F_malloc_fast F_malloc_enframe MallocTree MallocFacts_A MallocKit_A MallocKit_AB MallocKit_A2 MallocKit_A3 MallocKit_B MallocKit_B3 MallocModel_B.
From OssFuzzTheorems.Proofs.zstd.fse_read_ncount.lib.Spec Require Import STree Malloc MallocCtrl Monad.
From OssFuzzTheorems.Proofs.zstd.fse_read_ncount.lib.Malloc Require Import ProgDeps.
From OssFuzzTheorems.Proofs.zstd.fse_read_ncount.lib.Malloc Require Import Malloc_fp MallocNat MallocFacts_AS ASlot_W0 ASlot_W1 ASlot_I.
From OssFuzzTheorems.Proofs.zstd.fse_read_ncount.lib.Ubsan Require Import RMallocRep RMallocTree RMallocKit_B RMallocKit_B2 RMallocKit_B3 RMallocKit_A RMallocKit_A2 RMalloc_fp RAllocSlot_iface RASlot_I RASlot_W2.
From OssFuzzTheorems.Proofs.zstd.fse_read_ncount.lib.Ubsan Require Import RunDraw.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Section CANSEC1. Context {rc : runConstT}.
#[using="Type"] Lemma ras_ret0 : forall (sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 : word)
(s9v s8v s7v s6v s5v s4v s3v s2v s1v s0v rav : word) F fc (m : word -> option byte) (junk : list byte) (st' : mstate) (lo : Z),
rmrep st' m -> mem_inv usegs m ->
rw_cells usegs m (bv_unsigned sp + -144) (rta_frame junk s9v s8v s7v s6v s5v s4v s3v s2v s1v s0v rav) ->
stk usegs m lo (bv_unsigned sp + -144) -> ATOP <= lo -> lo <= bv_unsigned sp - 144 ->
evt usegs (fun ms' => exists (a1' a2' : word),
ms' = MS (mkR rav sp gp tp t0 t1 t2 s0v s1v a0 a1' a2' a3 a4 a5 a6 a7 s2v s3v s4v s5v s6v s7v s8v s9v s10 s11 t3 t4 t5 t6)
F (ret_pc rav) fc None m (seg_rom usegs)
/\ stk usegs m lo (bv_unsigned sp))
(MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -144)) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 (Z_to_bv 64 RSSP_GUARD) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x16854) fc None m (seg_rom usegs)).
Proof.
intros until lo. intros MR' MI FR ST LO LOLE.
pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
pose proof MR' as (_ & _ & (_ & _ & _ & _ & GUARD) & _).
unfold RSSP_GUARD, rta_frame in *. atop_facts.
step. Local Ltac2 Set LiaHints.tbl := fun () => "00>0>10224819587.641089863043.64 13327157379.6416198329987.6521747491971.6525941134723.6429399778947.65414905987.66  43930219544.5744954929309.5857760626819.6559739554179.6467629104515.657339497859.64 00000100200300400500600700800900?00@00A00B00CSSSSSSSSSS4LOLESSSS".
step. step. if_cases K; zify_cond K. { exfalso. apply K. reflexivity. }
step. step. step. step. step. step. step. step. step. step. step. step. step.
release_frame FR ST (bv_unsigned sp).
apply evt_done. do 2 eexists. split; [reflexivity| exact ST].
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
End CANSEC1.
