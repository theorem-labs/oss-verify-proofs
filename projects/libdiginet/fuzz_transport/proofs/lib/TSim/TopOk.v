(* The harness model never fails: LLVMFuzzerTestOneInput_m (TOps.v, the patched harness; fuzz_transport.c,
   FT:1124-1218) returns Some (_, 0) for every input D, every heap-address stream A the allocator contract allows
   (heap_ok) and every world B of W_LEN bytes over an image I with nonzero callback and table addresses (timg_ok,
   Agree.v). The statement is Prog/T/SlotBridge.v's (and U/Prog/T/SlotBridge.v's) harness_model_ok_stmt, with
   LoopOk.heap_ok for the slot's llvm_heap_ok (the same text).
   The prologue (InitOk.prologue_ok, prologue_big) gives agree I 0 at the head of the loop; LoopOk.loop_ok runs
   the loop; links_holds (LinksProof.v) discharges the hypothesis L1-L7 (HL : links) that the
   simulation proofs take. *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require Import TWorld TImg TCb TOps.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TSim Require Import Agree LoopOk.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TSim Require LinksProof InitOk.
Open Scope Z_scope.

(* the fuel of the loop (FT:1168, ops from 0 to OPS_MAX) *)
Lemma ops_fuel : 0 + Z.of_nat (Z.to_nat OPS_MAX) = OPS_MAX.
Proof. vm_compute. reflexivity. Qed.

Theorem harness_model_ok : forall (I : timg) (Bw : list byte) (A : nat -> Z) (D : list byte),
  timg_ok I -> length Bw = Z.to_nat W_LEN -> heap_ok A ->
  exists Bw', LLVMFuzzerTestOneInput_m I Bw A D = Some (Bw', 0).
Proof.
  intros I Bw A D HI HB HA.
  destruct (Z_lt_le_dec (Z.of_nat (length D)) FUZZ_INPUT_MAX) as [Hs|Hs].
  - destruct (InitOk.prologue_ok I Bw A D HI HB Hs) as (B0 & E & Hag & Hc).
    destruct (loop_ok LinksProof.links_holds I A D HA (Z.to_nat OPS_MAX) B0 (InitOk.prologue_cursor D) O 0 Hag
                (Z.le_refl 0) ops_fuel (Z.le_refl 0) Hc) as (B1 & E1).
    exists B1. rewrite E, E1. reflexivity.
  - exists Bw. exact (InitOk.prologue_big I Bw A D Hs).
Qed.

Print Assumptions harness_model_ok.
