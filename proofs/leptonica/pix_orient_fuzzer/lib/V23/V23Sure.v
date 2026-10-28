(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common Require Import
  PropExec CatExec CatSim Hoare ShapeAlg PureModel VmLedger AllocIface.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common.Mallocng Require Import
  MallocLayout MallocTree MallocOps MallocIface MallocInv_defs MallocIfaceX
  AllocBase AllocCalloc AllocSure MallocAllocLayout MallocGlue MallocSure.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.V23 Require Import V23MallocLayout V23Ref_malloc V23Ref_free V23Ref_calloc V23Alloc.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib Require KReplay.
Ltac2 kr_t_V23Sure () := "C47Corelib7Classes?RelationClasses9ReflexiveC6ARocqVerifyHarness?AgentSubmission6Common8MallocngAMallocAllocLayoutEmallocng_alloc_layoutC6ARocqVerifyHarness?AgentSubmission6Common8MallocngAMallocAllocLayoutFmallocng_calloc_layoutI6ARocqVerifyHarness?AgentSubmission6Common8Mallocng;AllocCalloc;AllocCalloc00K47Corelib4Init5Logic2eq01C5ARocqVerifyHarness?AgentSubmission3V23?V23MallocLayout4LU16C5ARocqVerifyHarness?AgentSubmission3V238V23Alloc:u16_callocI6ARocqVerifyHarness?AgentSubmission6Common8Mallocng9AllocBase9AllocBase00C5ARocqVerifyHarness?AgentSubmission3V238V23Alloc8u16_baseC6ARocqVerifyHarness?AgentSubmission6Common8Mallocng9AllocSure:asr_callocC6ARocqVerifyHarness?AgentSubmission6Common8Mallocng;AllocCalloc8aic_baseC6ARocqVerifyHarness?AgentSubmission6Common8Mallocng9AllocBase2ASC6ARocqVerifyHarness?AgentSubmission6Common8Mallocng:MallocSure6g_roomC47Corelib7Classes?RelationClasses;reflexivityc5ARocqVerifyHarness?AgentSubmission3V237V23Sure8u16_sureI4ELinuxProcessSemantics?LinuxProcessSem5State6VmMaps00I47Corelib7Numbers7BinNums1Z00C47Corelib4Init5Logic3iffC47Corelib7Classes?RelationClasses=iff_Reflexive".
Import ListNotations.
Local Open Scope Z_scope.

Definition u16_sure : AllocSure (AL:=mallocng_alloc_layout (ML:=LU16)) (CL:=mallocng_calloc_layout (ML:=LU16)) :=
  mallocng_sure (ML:=LU16) u16_malloc_okX u16_free_okX u16_calloc_okX
    (fun fx => malloc_refines (fx:=fx)) (fun fx => free_refines (fx:=fx)) (fun fx => calloc_refines (fx:=fx)).

Lemma u16_sure_calloc : asr_calloc (AllocSure:=u16_sure) = u16_calloc.
Proof.
ltac2:(KReplay.run1 (kr_t_V23Sure ()) [] "p;1p;2p-1p10000p4p710p9g000\j13Tg0028j12Tg003Uj20Tg004cj21Tg005=R0#3%20'0g006:'1o"). Qed.

Lemma u16_sure_base : aic_base (AllocCalloc:=asr_calloc (AllocSure:=u16_sure)) = u16_base.
Proof.
ltac2:(KReplay.run1 (kr_t_V23Sure ()) [] "p;1p;2g000\j12Tg0076j11Tg004cj20Tg005=#2#1g008@'0o"). Qed.

(* [comment removed for export] *)
Lemma u16_sure_room : forall A h k b,
  aroom (AllocSure:=u16_sure) A h k b <-> g_room A h k b.
Proof.
ltac2:(KReplay.run1 (kr_t_V23Sure ()) [] "h01Ah11bh21hh31kp;1p;3p;2p;4g000\j16Tg0028j15Tg009:j30Tg00:Cj31Tg00;Lj24Tg00<Mj42Tg00=Sj43Tg005=R0#6R1%50R0g00>A9010511'4g00?:g00@1R1p-0g00@Og00@hf3f2f1f0C2C3X11W3W2W0o"). Qed.
