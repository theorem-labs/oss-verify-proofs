(* The 8-byte statics of fuzz_state's fuzz/alloc.c in fuzz_state.asan-ubsan: g_fail_at, g_live, g_peak, g_count
   (journal footprint ranges [lo, hi)); the build-B twin of lib/A/FSPstat.v, same shape at B's addresses.
   MEASURED from the unstripped twin of the pinned fuzz_state.asan-ubsan (sha256 5ac5ce09...) by
   (internal path) and a capstone scan of fuzz/alloc.c's functions. The four symbols are 32 bytes each
   (asan global with redzone); the code writes only the first 8 bytes of each, with `sd`, at offset 0. B puts own()
   out of line, so the g_live / g_peak stores of malloc and realloc are in own:
     g_fail_at 0xa41c0:  stores at fuzz_malloc 0x82a88, fuzz_realloc 0x82c0c, fuzz_alloc_fail 0x82f34
     g_live    0x5daac0: stores at own 0x82b70, fuzz_realloc 0x82ce0, fuzz_free 0x82e8c
     g_peak    0x5daae0: stores at own 0x82b78, fuzz_alloc_peak_reset 0x82f10
     g_count   0x5dab00: stores at fuzz_malloc 0x82a7c, fuzz_realloc 0x82c00
   No store is wider than 8 bytes and none is at a non-zero offset, so the ranges cover exactly the written bytes and
   not the redzone padding. *)
From Stdlib Require Import ZArith List Lia.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YI04.
Import ListNotations.
Local Open Scope Z_scope.
Definition FS_PSTAT_FP : list (Z * Z) := [(0xa41c0, 0xa41c8); (0x5daac0, 0x5daac8); (0x5daae0, 0x5daae8); (0x5dab00, 0x5dab08)].
Lemma inFP_FS_PSTAT_FP : forall g, In (g, g + 8) FS_PSTAT_FP -> forall a, g <= a < g + 8 -> inFP FS_PSTAT_FP a.
Proof. intros g Hg a Ha. exists (g, g + 8). split; [exact Hg | cbn [fst snd]; lia]. Qed.
