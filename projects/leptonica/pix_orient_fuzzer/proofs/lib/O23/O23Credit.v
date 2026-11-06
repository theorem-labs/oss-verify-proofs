(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.Common Require Import
  PropExec CatExec CatSim Hoare ShapeAlg PureModel VmLedger AllocIface.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.Common.Mallocng Require Import
  MallocLayout MallocTree MallocOps MallocIface MallocInv_defs MallocIfaceX
  AllocBase AllocCalloc AllocSure AllocCredit MallocAllocLayout MallocGlue MallocSure MallocCredit.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.O23 Require Import O23MallocLayout O23Ref_malloc O23Ref_free O23Ref_calloc O23Alloc O23Sure.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib Require KReplay.
Ltac2 kr_t_O23Credit () := "C47Corelib7Classes?RelationClasses9ReflexiveC69OSSVerify5KrLib6Common8MallocngAMallocAllocLayoutEmallocng_alloc_layoutC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common8MallocngAMallocAllocLayoutFmallocng_calloc_layoutC1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib6Common8Mallocng9AllocSure9AllocSure00C1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2eq01C59OSSVerify5KrLib3O23?O23MallocLayout4LS16C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3O237O23Sure8s16_sureC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common8Mallocng;AllocCredit8acr_sureC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common8Mallocng9AllocSure:asr_callocC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common8Mallocng;AllocCalloc8aic_baseC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common8Mallocng9AllocBase2ASC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common8Mallocng<MallocCredit7g_roomPC1?~~~~~~~~~~~~~~~C47Corelib7Classes?RelationClasses;reflexivityc59OSSVerify5KrLib3O239O23Credit:s16_creditC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem5State6VmMaps00I47Corelib7Numbers7BinNums1Z00C47Corelib4Init5Logic3iffC47Corelib7Classes?RelationClasses=iff_Reflexive".
Import ListNotations.
Local Open Scope Z_scope.

Definition s16_credit : AllocCredit (AL:=mallocng_alloc_layout (ML:=LS16)) (CL:=mallocng_calloc_layout (ML:=LS16)) :=
  mallocng_credit (ML:=LS16) s16_malloc_okX s16_free_okX s16_calloc_okX
    (fun fx => malloc_refines (fx:=fx)) (fun fx => free_refines (fx:=fx)) (fun fx => calloc_refines (fx:=fx)).

Lemma s16_credit_sure : acr_sure (AllocCredit:=s16_credit) = s16_sure.
Proof.
ltac2:(KReplay.run1 (kr_t_O23Credit ()) [] "p;1p;2p-1p10000p4p710p9g000\j13Tg0028j12Tg003Uj20Tg004_j21Tg0059R0#3%20'0g0066'1o"). Qed.

(* [comment removed for export] *)
Lemma s16_credit_room : forall A h k p,
  aroomP (AllocCredit:=s16_credit) A h k p <-> g_roomP A h k p.
Proof.
ltac2:(KReplay.run1 (kr_t_O23Credit ()) [] "h01Ah11hh21kh31pp;1p;3p;2p;4g000\j17Tg0028j16Tg006oj30Tg0088j31Tg009Aj35Tg00:Jj22Tg00;Kj43Tg00<Tj44Tg0059R0#7R1%60R0g00=B90109110551'2g00>?g00?6R1p-0g00?Tg00?mf3f2f1f0C3C4X31W2W1W0o"). Qed.
