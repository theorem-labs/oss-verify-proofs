(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common Require Import
  PropExec CatExec CatSim Hoare ShapeAlg PureModel VmLedger AllocIface.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common.Mallocng Require Import
  MallocLayout MallocTree MallocOps MallocIface MallocInv_defs MallocIfaceX
  AllocBase AllocCalloc AllocSure AllocCredit MallocAllocLayout MallocGlue MallocSure MallocCredit.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.V23 Require Import V23MallocLayout V23Ref_malloc V23Ref_free V23Ref_calloc V23Alloc V23Sure.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib Require KReplay.
Ltac2 kr_t_V23Credit () := "C47Corelib7Classes?RelationClasses9ReflexiveC6ARocqVerifyHarness?AgentSubmission6Common8MallocngAMallocAllocLayoutEmallocng_alloc_layoutC6ARocqVerifyHarness?AgentSubmission6Common8MallocngAMallocAllocLayoutFmallocng_calloc_layoutI6ARocqVerifyHarness?AgentSubmission6Common8Mallocng9AllocSure9AllocSure00K47Corelib4Init5Logic2eq01C5ARocqVerifyHarness?AgentSubmission3V23?V23MallocLayout4LU16C5ARocqVerifyHarness?AgentSubmission3V237V23Sure8u16_sureC6ARocqVerifyHarness?AgentSubmission6Common8Mallocng;AllocCredit8acr_sureC6ARocqVerifyHarness?AgentSubmission6Common8Mallocng9AllocSure:asr_callocC6ARocqVerifyHarness?AgentSubmission6Common8Mallocng;AllocCalloc8aic_baseC6ARocqVerifyHarness?AgentSubmission6Common8Mallocng9AllocBase2ASC6ARocqVerifyHarness?AgentSubmission6Common8Mallocng<MallocCredit7g_roomPC47Corelib7Classes?RelationClasses;reflexivityc5ARocqVerifyHarness?AgentSubmission3V239V23Credit:u16_creditI4ELinuxProcessSemantics?LinuxProcessSem5State6VmMaps00I47Corelib7Numbers7BinNums1Z00C47Corelib4Init5Logic3iffC47Corelib7Classes?RelationClasses=iff_Reflexive".
Import ListNotations.
Local Open Scope Z_scope.

Definition u16_credit : AllocCredit (AL:=mallocng_alloc_layout (ML:=LU16)) (CL:=mallocng_calloc_layout (ML:=LU16)) :=
  mallocng_credit (ML:=LU16) u16_malloc_okX u16_free_okX u16_calloc_okX
    (fun fx => malloc_refines (fx:=fx)) (fun fx => free_refines (fx:=fx)) (fun fx => calloc_refines (fx:=fx)).

Lemma u16_credit_sure : acr_sure (AllocCredit:=u16_credit) = u16_sure.
Proof.
ltac2:(KReplay.run1 (kr_t_V23Credit ()) [] "p;1p;2p-1p10000p4p710p9g000\j13Tg0028j12Tg003Uj20Tg004_j21Tg0059R0#3%20'0g0066'1o"). Qed.

(* [comment removed for export] *)
Lemma u16_credit_room : forall A h k p,
  aroomP (AllocCredit:=u16_credit) A h k p <-> g_roomP A h k p.
Proof.
ltac2:(KReplay.run1 (kr_t_V23Credit ()) [] "h01Ah11hh21kh31pp;1p;3p;2p;4g000\j17Tg0028j16Tg006oj30Tg0088j31Tg009Aj35Tg00:Jj22Tg00;Kj43Tg00<Tj44Tg0059R0#7R1%60R0g00=B90109110551'2g00>?g00?6R1p-0g00?Tg00?mf3f2f1f0C3C4X31W2W1W0o"). Qed.
