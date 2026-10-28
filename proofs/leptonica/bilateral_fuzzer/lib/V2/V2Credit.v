(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.Common Require Import
  PropExec CatExec CatSim Hoare ShapeAlg PureModel VmLedger AllocIface.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.Common.Mallocng Require Import
  MallocLayout MallocTree MallocOps MallocIface MallocInv_defs MallocIfaceX
  AllocBase AllocCalloc AllocSure AllocCredit MallocAllocLayout MallocGlue MallocSure MallocCredit.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.V2 Require Import V2MallocLayout V2Ref_malloc V2Ref_free V2Ref_calloc V2Alloc V2Sure.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib Require KReplay.
Ltac2 kr_t_V2Credit () := "C47Corelib7Classes?RelationClasses9ReflexiveC6ARocqVerifyHarness?AgentSubmission6Common8MallocngAMallocAllocLayoutEmallocng_alloc_layoutC6ARocqVerifyHarness?AgentSubmission6Common8MallocngAMallocAllocLayoutFmallocng_calloc_layoutI6ARocqVerifyHarness?AgentSubmission6Common8Mallocng9AllocSure9AllocSure00K47Corelib4Init5Logic2eq01C5ARocqVerifyHarness?AgentSubmission2V2>V2MallocLayout4LU16C5ARocqVerifyHarness?AgentSubmission2V26V2Sure8u16_sureC6ARocqVerifyHarness?AgentSubmission6Common8Mallocng;AllocCredit8acr_sureC6ARocqVerifyHarness?AgentSubmission6Common8Mallocng9AllocSure:asr_callocC6ARocqVerifyHarness?AgentSubmission6Common8Mallocng;AllocCalloc8aic_baseC6ARocqVerifyHarness?AgentSubmission6Common8Mallocng9AllocBase2ASC6ARocqVerifyHarness?AgentSubmission6Common8Mallocng<MallocCredit7g_roomPC47Corelib7Classes?RelationClasses;reflexivityc5ARocqVerifyHarness?AgentSubmission2V28V2Credit:u16_creditI4ELinuxProcessSemantics?LinuxProcessSem5State6VmMaps00I47Corelib7Numbers7BinNums1Z00C47Corelib4Init5Logic3iffC47Corelib7Classes?RelationClasses=iff_Reflexive".
Import ListNotations.
Local Open Scope Z_scope.

Definition u16_credit : AllocCredit (AL:=mallocng_alloc_layout (ML:=LU16)) (CL:=mallocng_calloc_layout (ML:=LU16)) :=
  mallocng_credit (ML:=LU16) u16_malloc_okX u16_free_okX u16_calloc_okX
    (fun fx => malloc_refines (fx:=fx)) (fun fx => free_refines (fx:=fx)) (fun fx => calloc_refines (fx:=fx)).

Lemma u16_credit_sure : acr_sure (AllocCredit:=u16_credit) = u16_sure.
Proof.
ltac2:(KReplay.run1 (kr_t_V2Credit ()) [] "p;1p;2p-1p10000p4p710p9g000\j13Tg0028j12Tg003Uj20Tg004_j21Tg0059R0#3%20'0g0064'1o"). Qed.

(* [comment removed for export] *)
Lemma u16_credit_room : forall A h k p,
  aroomP (AllocCredit:=u16_credit) A h k p <-> g_roomP A h k p.
Proof.
ltac2:(KReplay.run1 (kr_t_V2Credit ()) [] "h01Ah11hh21kh31pp;1p;3p;2p;4g000\j17Tg0028j16Tg006kj30Tg0084j31Tg009=j35Tg00:Fj22Tg00;Gj43Tg00<Pj44Tg0059R0#7R1%60R0g00=>90109110551'2g00>9g00?0R1p-0g00?Ng00?gf3f2f1f0C3C4X31W2W1W0o"). Qed.
