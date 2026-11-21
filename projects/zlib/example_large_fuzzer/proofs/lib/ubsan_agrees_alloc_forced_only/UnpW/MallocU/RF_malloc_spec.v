(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Malloc Require Import MallocTree ASlot_I MallocFacts_AM. (* [comment removed for export] *)
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.MallocU Require Import RMallocTree RMalloc_iface RAllocSlot_iface RF_malloc_core RF_malloc_top RASlot_I RF_alloc_slot RF_malloc_big RF_am_P RF_alloc_meta RMallocz_iface.

From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import Ceiling.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.P Require Import Rnd.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Malloc Require Import CeilWin.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac std_lia__ := lia.
Local Ltac lia := first [std_lia__ | try (pose proof ceil_window_holds as CEIL_RANGE__); unfold ceil_window in *; std_lia__].
Local Ltac std_nia__ := nia.
Local Ltac nia := first [std_nia__ | try (pose proof ceil_window_holds as CEIL_RANGE__); unfold ceil_window in *; std_nia__].
Local Ltac OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib.ZBridge.flia ::= first [ assumption | OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib.ZBridge.slim; lia | lia ].
Local Ltac OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib.ZBridge.mlia ::= Z.div_mod_to_equations; lia.
Local Ltac OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib.Step.slia ::= first [ exact I | lia | split; [lia|exact I] ].
Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.
Theorem rmalloc_spec : rmalloc_stmt.
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__).
  exact (rmalloc_spec_proof ras_pre2 as_inv2 ralloc_slot_spec ras_pre2_intro (rbig_spec ram_pre ralloc_meta_spec ramp_big)).
Qed.

(* [comment removed for export] *)
Theorem rmallocz_spec : rmallocz_stmt.
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__).
  exact (rmallocz_spec_proof ras_pre2 as_inv2 ralloc_slot_spec ras_pre2_intro (rbig_spec ram_pre ralloc_meta_spec ramp_big)).
Qed.
End WithCeiling0.
