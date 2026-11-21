(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import MemImageType.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_agrees_alloc_forced_only.UnpW Require Import ZTopC AsanMain.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_agrees_alloc_forced_only.UnpW.Plain Require Import PImg.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_agrees_alloc_forced_only.UnpW.AsanW Require Import AImg AMalloc_iface AFake_iface AHarness_iface ADriver_iface AInstance AInstanceM AInstanceF AMain_closed AMain_closedI AFreeAll.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_agrees_alloc_forced_only.Common Require Import RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Definition harness_closed_stmt : Prop := forall rc : runConstT, fuzz_oneA_stmt (AI_of (@AHI_free rc)) afake_rng.

Theorem asan_implC_final : harness_closed_stmt -> asan_implC_stmt ASTAGE.
Proof. intros HARNESS. exact (asan_implC_of_free (fun rc : runConstT => @AHI_free rc) HARNESS). Qed.
