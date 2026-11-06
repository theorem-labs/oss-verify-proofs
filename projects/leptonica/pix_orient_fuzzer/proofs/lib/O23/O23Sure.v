(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.Common Require Import
  PropExec CatExec CatSim Hoare ShapeAlg PureModel VmLedger AllocIface.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.Common.Mallocng Require Import
  MallocLayout MallocTree MallocOps MallocIface MallocInv_defs MallocIfaceX
  AllocBase AllocCalloc AllocSure MallocAllocLayout MallocGlue MallocSure.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.O23 Require Import O23MallocLayout O23Ref_malloc O23Ref_free O23Ref_calloc O23Alloc.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib Require KReplay.
Ltac2 kr_t_O23Sure () := "C47Corelib7Classes?RelationClasses9ReflexiveC69OSSVerify5KrLib6Common8MallocngAMallocAllocLayoutEmallocng_alloc_layoutC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common8MallocngAMallocAllocLayoutFmallocng_calloc_layoutC1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib6Common8Mallocng;AllocCalloc;AllocCalloc00C1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2eq01C59OSSVerify5KrLib3O23?O23MallocLayout4LS16C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3O238O23Alloc:s16_callocC1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib6Common8Mallocng9AllocBase9AllocBase00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3O238O23Alloc8s16_baseC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common8Mallocng9AllocSure:asr_callocC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common8Mallocng;AllocCalloc8aic_baseC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common8Mallocng9AllocBase2ASC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common8Mallocng:MallocSure6g_roomC1?~~~~~~~~~~~~~~~C47Corelib7Classes?RelationClasses;reflexivityc59OSSVerify5KrLib3O237O23Sure8s16_sureC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem5State6VmMaps00I47Corelib7Numbers7BinNums1Z00C47Corelib4Init5Logic3iffC47Corelib7Classes?RelationClasses=iff_Reflexive".
Import ListNotations.
Local Open Scope Z_scope.

Definition s16_sure : AllocSure (AL:=mallocng_alloc_layout (ML:=LS16)) (CL:=mallocng_calloc_layout (ML:=LS16)) :=
  mallocng_sure (ML:=LS16) s16_malloc_okX s16_free_okX s16_calloc_okX
    (fun fx => malloc_refines (fx:=fx)) (fun fx => free_refines (fx:=fx)) (fun fx => calloc_refines (fx:=fx)).

Lemma s16_sure_calloc : asr_calloc (AllocSure:=s16_sure) = s16_calloc.
Proof.
ltac2:(KReplay.run1 (kr_t_O23Sure ()) [] "p;1p;2p-1p10000p4p710p9g000\j13Tg0028j12Tg003Uj20Tg004cj21Tg005=R0#3%20'0g006:'1o"). Qed.

Lemma s16_sure_base : aic_base (AllocCalloc:=asr_calloc (AllocSure:=s16_sure)) = s16_base.
Proof.
ltac2:(KReplay.run1 (kr_t_O23Sure ()) [] "p;1p;2g000\j12Tg0076j11Tg004cj20Tg005=#2#1g008@'0o"). Qed.

(* [comment removed for export] *)
Lemma s16_sure_room : forall A h k b,
  aroom (AllocSure:=s16_sure) A h k b <-> g_room A h k b.
Proof.
ltac2:(KReplay.run1 (kr_t_O23Sure ()) [] "h01Ah11bh21hh31kp;1p;3p;2p;4g000\j16Tg0028j15Tg009:j30Tg00:Cj31Tg00;Lj24Tg00<Mj42Tg00=Sj43Tg005=R0#6R1%50R0g00>A9010511'4g00?:g00@1R1p-0g00@Og00@hf3f2f1f0C2C3X11W3W2W0o"). Qed.
