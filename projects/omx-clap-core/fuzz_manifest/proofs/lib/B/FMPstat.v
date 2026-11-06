(* B twin (fm.asan-ubsan, pin ca61e5c9eabc0050) of lib/A/FMPstat.v at a working branch 5d8d8a15571, relocated A->B by Theorem Labs tools over the unstripped twins; every image numeral re-derived by symbol / section (a Theorem Labs lane reloc report). *)
(* The 8-byte statics of fuzz_manifest's fuzz/alloc.c in fuzz_manifest.asan: g_fail_at, g_live, g_peak, g_count (journal footprint ranges [lo, hi)). *)
From Stdlib Require Import ZArith List Lia.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YI04.
Import ListNotations.
Local Open Scope Z_scope.
Definition FM_PSTAT_FP : list (Z * Z) := [(0x9e260, 0x9e268); (0x5d4700, 0x5d4708); (0x5d4720, 0x5d4728); (0x5d4740, 0x5d4748)].
Lemma inFP_FM_PSTAT_FP : forall g, In (g, g + 8) FM_PSTAT_FP -> forall a, g <= a < g + 8 -> inFP FM_PSTAT_FP a.
Proof. intros g Hg a Ha. exists (g, g + 8). split; [exact Hg | cbn [fst snd]; lia]. Qed.
