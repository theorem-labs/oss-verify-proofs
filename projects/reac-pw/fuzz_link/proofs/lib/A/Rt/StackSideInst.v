(* The side-stack contracts of reac-pw/fuzz_link's asan build for every certificate B of link's image
   (`PcapSyms B`, lib/A/AF0m.v; link's own one is AD2l.PcapB with AD2l.PcapB_syms), with every other premise
   discharged: the frame_alloc_3 / frame_alloc_4 contracts (astack_malloc_realizes, lib/Reusable/YG0d.v), the
   frame_alloc_8 / frame_alloc_9 contracts (astack_malloc_sz_realizes, lib/Reusable/AsStackSz.v) and the frame_release_8 /
   frame_release_9 contracts (astack_free_realizes, lib/Reusable/StackFreeDef.v; the class-9 names are those of
   lib/A/Rt/StackSide9.v). AR_laws holds for every certificate (YG0q.AR_laws_ok); the thread pointer and TSD fields are
   PcapSyms's ts_tp / ts_tsd; each start-up cell the frame_alloc_8 / frame_alloc_9 walks read (the same TLS chain) is
   found in the constant table PcapSyms fixes (ts_const: Tfib_const of lib/A/AF0m.v) by the kernel (AF0x.cell_lookup_In).
   The own-function walks cite these as the discharge of their side-stack Section hypotheses. *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YK11 YK0s YK0i YK15 YK0j YK18 YP09.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d YG0q.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YM05 AsStackSz StackFreeDef.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require Import AB1v AF0m AF0x.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Rt Require StackMalloc3 StackMalloc4.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Rt Require Import StackMalloc8Tbl StackFree8Tbl.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Rt Require StackMalloc8Closed StackFree8Closed.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Rt Require Import StackSide9.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Rt Require StackMalloc9Closed StackFree9Closed.
Import ListNotations.
Open Scope Z_scope.

Section i. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : asyms.
Hypothesis TB : PcapSyms B.

(* `forall ly, In c (as_const B ly)` for a cell c of link's constant table: the first cell at c's address is c. *)
Local Ltac cell :=
  intros ?ly; rewrite (ts_const B TB ly);
  match goal with |- In ?c ?l => apply (cell_lookup_In l (c_at c)); vm_compute; reflexivity end.

Theorem link_stack_malloc_3 : astack_malloc_realizes tfibsegs B 3.
Proof. exact (StackMalloc3.stack_malloc3_contract B (AR_laws_ok tfibsegs B) TB). Qed.

Theorem link_stack_malloc_4 : astack_malloc_realizes tfibsegs B 4.
Proof. exact (StackMalloc4.stack_malloc4_contract B (AR_laws_ok tfibsegs B) TB). Qed.

Theorem link_stack_malloc_8 : astack_malloc_sz_realizes tfibsegs B PC_STACK_MALLOC_8 CID8.
Proof.
apply (StackMalloc8Closed.stack_malloc_8_sz_discharged B (AR_laws_ok tfibsegs B) TB);
[exact (ts_tp B TB) | exact (ts_tsd B TB) | ..]; cell.
Qed.

Theorem link_stack_free_8 : astack_free_realizes tfibsegs B PC_STACK_FREE_8 CID8.
Proof. exact (StackFree8Closed.stack_free_8_discharged B (AR_laws_ok tfibsegs B) TB). Qed.

Theorem link_stack_malloc_9 : stack_malloc_9_contract B.
Proof.
unfold stack_malloc_9_contract.
apply (StackMalloc9Closed.stack_malloc_9_sz_discharged B (AR_laws_ok tfibsegs B) TB);
[exact (ts_tp B TB) | exact (ts_tsd B TB) | ..]; cell.
Qed.

Theorem link_stack_free_9 : stack_free_9_contract B.
Proof. exact (StackFree9Closed.stack_free_9_discharged B (AR_laws_ok tfibsegs B) TB). Qed.

End i.
