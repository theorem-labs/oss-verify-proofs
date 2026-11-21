(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (3 recorded proofs replaced by written proofs (HINV_from_init, HINV_init, brk_link_ps_iff)). *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Spec Require Import STree Malloc MallocCtrl.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Malloc Require Import ProgDeps.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Malloc Require Import MallocRep MallocTree.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Malloc Require Export MallocBlocks.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Common Require Import RunDraw.
From OSSVerify.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_MallocHINV () := "I47Corelib4Init9Datatypes4prod00I47Corelib4Init9Datatypes4list00C59OSSVerify5KrLib3Lib8RunConst4ATOPC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc5minitC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc<MallocBlocks8brk_linkC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4list01I59OSSVerify5KrLib6Malloc<MallocBlocks;AREACH_from00C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib6Malloc<MallocBlocks;AREACH_from01C1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic3and01I47Corelib7Numbers7BinNums1Z00K47Corelib7Numbers7BinNums1Z01C59OSSVerify5KrLib6Malloc<MallocBlocks5blockC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic4True01c59OSSVerify5KrLib6Malloc:MallocHINV>HINV_from_initC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc9MallocRep>agent_reservedC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc3ctxC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc5c_brkC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6PState6ps_brkC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4prod01C59OSSVerify5KrLib4Spec6Malloc4concC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2eq00C47Corelib4Init5Logic3iffC59OSSVerify5KrLib6Malloc:MallocTree;brk_link_psC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Malloc6mstate00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6PState6PState00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Malloc8brkstate00C1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic4True00I47Corelib7Numbers7BinNums1N00".
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Section CANSEC1. Context {rc : runConstT}.
Definition HINV_from (resv : list (Z * Z)) (st : mstate) (pbrk : Z) (LB : list block) : Prop :=
  brk_link st pbrk /\ AREACH_from resv st LB.
End CANSEC1.
Notation HINV := (HINV_from agent_reserved).

Section CANSEC2. Context {rc : runConstT}.
Lemma HINV_from_init : forall resv pbrk, HINV_from resv (minit 0 resv ATOP) pbrk [].
Proof. intros. split; [exact I | apply areach_init]. Qed.

Lemma HINV_init : forall pbrk, HINV (minit 0 agent_reserved ATOP) pbrk [].
Proof. intros. apply HINV_from_init. Qed.

Lemma brk_link_ps_iff : forall st s, brk_link_ps st s <-> brk_link st (ps_brk s).
Proof. intros st s. unfold brk_link_ps, brk_link. destruct (c_brk (ctx st)); tauto. Qed.


End CANSEC2.
