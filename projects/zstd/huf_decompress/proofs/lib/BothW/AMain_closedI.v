(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import MemImageType.
From OSSVerify.Proofs.zstd.huf_decompress.lib Require Import BothMain.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Plain Require Import PImg.
From OSSVerify.Proofs.zstd.huf_decompress.lib.BothW Require Import BImg AMalloc_iface AFake_iface AHarness_iface ADriver_iface AInstance AInstanceM AInstanceF ATsafeMain AMain_asm AMain_closed.
From OSSVerify.Proofs.zstd.huf_decompress.lib.BothW Require Import AHarness_bm.   (* [comment removed for export] *)
From OSSVerify.Proofs.zstd.huf_decompress.lib.Common Require Import RunDraw.
From OSSVerify.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_AMain_closedI () := "C59OSSVerify5KrLib5BothW:AInstanceF5AI_ofC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW:AInstanceF7AI_of_EC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW:AInstanceF;AI_of_CI_OKC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW:AInstanceF<AI_of_DRV_CIC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW:AInstanceF<AI_of_CLI_CIC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW<AMain_closed4adrvC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW9AInstance3AHIC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW6AHeapP7AHEAP_PC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW=AMalloc_iface:afree_stmtC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW;AHarness_bm?fuzz_oneA_stmtBC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5BothW=AMain_closedI<adrv_of_freeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW<AMain_closed8model_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW9AMain_asm9asan_implC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib3Lib8RunConst9runConstT00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW:AInstanceM5aci_IC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW;AFake_iface9afake_rngC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW:ATsafeMain4NMAXC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW:ATsafeMain2A0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW:ATsafeMain7A0_initC1?~~~~~~~~~~~~~~~".

Section CANSEC1. Context {rc : runConstT}.
Section WithFree.
  Hypothesis FREE : afree_stmt aci_I AHEAP_I.
  (* [comment removed for export] *)
  Hypothesis FUZZ : fuzz_oneA_stmtB (AI_of FREE) AFake_iface.afake_rng.

  Theorem adrv_of_free : adrv_stmt ATsafeMain.A0.
Proof.
ltac2:(KReplay.run1 (kr_t_AMain_closedI ()) ["CANSEC1"; "WithFree"] "p;2p;7g0000j25Tg000kj24Tg001hj20Tg002ij21Tg003kj23Tg004mj72Tp,2rcR0p,4FREER1,501401100111011301p,4FUZZF2o"). Qed.
End WithFree.
End CANSEC1.

(* [comment removed for export] *)
Theorem asan_impl_of_free :
  forall FREE : (forall rc : runConstT, afree_stmt aci_I AHEAP_I),
  (forall rc : runConstT, fuzz_oneA_stmtB (AI_of (FREE rc)) AFake_iface.afake_rng) -> asan_impl_stmt ASTAGE.
Proof.
ltac2:(KReplay.run1 (kr_t_AMain_closedI ()) [] "h02rch14FREEh24FUZZp;1p;2p;3p;5g005ij17Tg006aj26Tg007Zj30Tg0000j21Tg008]j35Tg009cj32Tg00:hj13Tg00;hj54Tg00<fR0f0R1g00=c%71,6130]0f1P1O1R2,11g00>^551^00g00?^g00@Xf2P1O1=212X00%31X00g00APD4W2W1o"). Qed.
