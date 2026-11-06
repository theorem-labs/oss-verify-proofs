(* The 8-byte statics of fuzz_state's fuzz/alloc.c in fuzz_state.asan: g_fail_at, g_live, g_peak, g_count (journal
   footprint ranges [lo, hi)). A walk that writes a static declares it in the journal's FP; the image clause of
   ajournal (lib/Reusable/YCbq.v) spares the footprint (RELOC's FP-keyed journal, a working branch 5658cc32098).
   Ported from: a Theorem Labs lane's proofs/omx-clap-core/fuzz_manifest/lib/A/FMPstat.v (5658cc32098), same shape at fs's addresses.
   MEASURED from the unstripped twin of the pinned fuzz_state.asan (sha256 64b53ff8...) by
   (internal path) and a capstone scan of fuzz/alloc.c's functions: the four symbols are 32 bytes each
   (asan global with redzone), but the code writes only the first 8 bytes of each, with `sd`, at offset 0:
     g_fail_at 0xa3ca0:  stores at fuzz_malloc 0x828f4, fuzz_realloc 0x82a48, fuzz_alloc_fail 0x82ea4
     g_live    0x5da5c0: stores at fuzz_malloc 0x82994, fuzz_realloc 0x82b24 / 0x82bb8 / 0x82c40, fuzz_free 0x82e00
     g_peak    0x5da5e0: stores at fuzz_malloc 0x8299c, fuzz_realloc 0x82bc0 / 0x82c4c, fuzz_alloc_peak_reset 0x82e80
     g_count   0x5da600: stores at fuzz_malloc 0x828e4, fuzz_realloc 0x82a38
   (fuzz_strdup writes none of its own; it writes through fuzz_malloc. No store is wider than 8 bytes and none is at a
   non-zero offset, so the ranges cover exactly the written bytes and not the redzone padding.) *)
From Stdlib Require Import ZArith List Lia.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YI04.
Import ListNotations.
Local Open Scope Z_scope.
Definition FS_PSTAT_FP : list (Z * Z) := [(0xa3ca0, 0xa3ca8); (0x5da5c0, 0x5da5c8); (0x5da5e0, 0x5da5e8); (0x5da600, 0x5da608)].
Lemma inFP_FS_PSTAT_FP : forall g, In (g, g + 8) FS_PSTAT_FP -> forall a, g <= a < g + 8 -> inFP FS_PSTAT_FP a.
Proof. intros g Hg a Ha. exists (g, g + 8). split; [exact Hg | cbn [fst snd]; lia]. Qed.
