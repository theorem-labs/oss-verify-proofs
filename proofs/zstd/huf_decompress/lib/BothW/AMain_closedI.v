(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import MemImageType.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib Require Import BothMain.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Plain Require Import PImg.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.BothW Require Import BImg AMalloc_iface AFake_iface AHarness_iface ADriver_iface AInstance AInstanceM AInstanceF ATsafeMain AMain_asm AMain_closed.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.BothW Require Import AHarness_bm.   (* [comment removed for export] *)
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import RunDraw.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_AMain_closedI () := "C5ARocqVerifyHarness?AgentSubmission5BothW:AInstanceF5AI_ofC5ARocqVerifyHarness?AgentSubmission5BothW:AInstanceF7AI_of_EC5ARocqVerifyHarness?AgentSubmission5BothW:AInstanceF;AI_of_CI_OKC5ARocqVerifyHarness?AgentSubmission5BothW:AInstanceF<AI_of_DRV_CIC5ARocqVerifyHarness?AgentSubmission5BothW:AInstanceF<AI_of_CLI_CIC5ARocqVerifyHarness?AgentSubmission5BothW<AMain_closed4adrvC5ARocqVerifyHarness?AgentSubmission5BothW9AInstance3AHIC5ARocqVerifyHarness?AgentSubmission5BothW6AHeapP7AHEAP_PC5ARocqVerifyHarness?AgentSubmission5BothW=AMalloc_iface:afree_stmtC5ARocqVerifyHarness?AgentSubmission5BothW;AHarness_bm?fuzz_oneA_stmtBc5ARocqVerifyHarness?AgentSubmission5BothW=AMain_closedI<adrv_of_freeC5ARocqVerifyHarness?AgentSubmission5BothW<AMain_closed8model_okC5ARocqVerifyHarness?AgentSubmission5BothW9AMain_asm9asan_implI5ARocqVerifyHarness?AgentSubmission3Lib8RunConst9runConstT00C5ARocqVerifyHarness?AgentSubmission5BothW:AInstanceM5aci_IC5ARocqVerifyHarness?AgentSubmission5BothW;AFake_iface9afake_rngC5ARocqVerifyHarness?AgentSubmission5BothW:ATsafeMain4NMAXC5ARocqVerifyHarness?AgentSubmission5BothW:ATsafeMain2A0C5ARocqVerifyHarness?AgentSubmission5BothW:ATsafeMain7A0_init".

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
