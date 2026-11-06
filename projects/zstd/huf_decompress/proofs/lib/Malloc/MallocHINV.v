(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
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
Proof.
ltac2:(KReplay.run1 (kr_t_MallocHINV ()) ["CANSEC2"] "h04pbrkh14resvp;2p;1p;3p;4g0000j28Tg000Pj17Tg0010j10Tg001fj31Tg002\j26Tg003]j12Tg004=j43Tg005Cj24Tg006Ij45Tg006dR0/80#7g007Bf1R1p,2rcR2#031R3f0'6P2P1P3g007`#2C3g008^1421C5X00W1o"). Qed.

Lemma HINV_init : forall pbrk, HINV (minit 0 agent_reserved ATOP) pbrk [].
Proof.
ltac2:(KReplay.run1 (kr_t_MallocHINV ()) ["CANSEC2"] "h04pbrkp;2g009:j20Tg006dg00:?f0'0W0o"). Qed.

Lemma brk_link_ps_iff : forall st s, brk_link_ps st s <-> brk_link st (ps_brk s).
Proof.
ltac2:(KReplay.run1 (kr_t_MallocHINV ()) ["CANSEC2"] "p'0h01Hh11bi001bh23offi013offh33ridi023ridh41sh52sti031xp;1p;4p;2p;3g00;Cj19Tg00<7j18Tg00<mj10Tg00=dj43Tg00>Dj22Tg00?9j31Tg00?Sj25Tg006Ij44Tg00?lj26Tg002\j27Tg00@ng00Agf1R0#9#8g00B`R1P1P1p-0f0R1g00C[R2P2g006dR3f4#0f5R4g00D7R5P3P0P1C3R6'231n011030003000020102101R7/57P1P2\2R7P7g008^X02R2P2C4R2P2%04f6R4/26513R6%04f7P5P3f2P0C3'2513[R4P4P1X06R6P6C4X23X35P0P1O2n011000003000020102101b11601%01,70'5eW4W5o"). Qed.


End CANSEC2.
