(** * HaltsUFO — example_large_fuzzer UBSan halts over the filtered run (twin of [Halts.halts_ubsan])

    Submission 4's [Halts.halts_ubsan] proved the may-fail statement over the lps patch-04 spec, from the UBSan
    build's program tree ([U.Impl_closed.impl_U_of_zlib]) exactly as [Halts.halts_plain] did from the plain
    build's.  Since the tier-0 port the node relation is the filtered one, and [HaltsFO.halts_core_of_impl]
    turns any build's program tree into the forced-only core; this file applies it to the UBSan build. *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence MustExit HaltsAllowed.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType State Run.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Lib Require Import Image Stage.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Spec Require Import ModelInv.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.World Require Import Tgt_example_large_fuzzer_ubsan.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit Require Import HaltsFO.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.U Require Zlib_iface Zlib_closed Impl_closed.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.FO Require Import FOCore.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(** The UBSan build: halting under memory forced-only, no budget premise. *)
Theorem halts_ubsan_core :
  halts_core alloc_forced_cfg source_alloc_limit AnyExit.codes
    (mkImage Tgt_example_large_fuzzer_ubsan.M.loaded_segments Tgt_example_large_fuzzer_ubsan.M.init_pc
             Tgt_example_large_fuzzer_ubsan.M.phdrs).
Proof.
  exact (halts_core_of_impl usegs ustage _ _ segs_ok_usegs
           (U.Impl_closed.impl_U_of_zlib (fun CE => @U.Zlib_closed.zR CE) U.Zlib_closed.zlib_closed_all)).
Qed.
