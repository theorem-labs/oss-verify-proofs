(* The 8-byte statics of fuzz_manifest's fuzz/alloc.c in fuzz_manifest.asan: g_fail_at, g_live, g_peak, g_count (journal footprint ranges [lo, hi)). *)
From Stdlib Require Import ZArith List Lia.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YI04.
Import ListNotations.
Local Open Scope Z_scope.
Definition FM_PSTAT_FP : list (Z * Z) := [(0x9df80, 0x9df88); (0x5d4400, 0x5d4408); (0x5d4420, 0x5d4428); (0x5d4440, 0x5d4448)].
Lemma inFP_FM_PSTAT_FP : forall g, In (g, g + 8) FM_PSTAT_FP -> forall a, g <= a < g + 8 -> inFP FM_PSTAT_FP a.
Proof. intros g Hg a Ha. exists (g, g + 8). split; [exact Hg | cbn [fst snd]; lia]. Qed.
