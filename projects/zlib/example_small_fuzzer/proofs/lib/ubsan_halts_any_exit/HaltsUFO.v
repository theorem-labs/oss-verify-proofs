(** * HaltsUFO — example_small_fuzzer UBSan halts over the filtered run (twin of [Halts.halts_ubsan])

    Submission 3's [Halts.halts_ubsan] proved the may-fail statement over the lps patch-04 spec, from the UBSan
    build's program tree ([U.Impl_closed.impl_U_of_zlib]) exactly as [Halts.halts_plain] did from the plain
    build's.  Since the tier-0 port the node relation is the filtered one; [HaltsFO.halts_plain_core]'s
    argument, run on the UBSan build ([usegs], [ustage], [segs_ok_usegs]), gives its forced-only core. *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence MustExit HaltsAllowed.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Sem.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Lib Require MState.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Lib Require MState Frame Exec ITree Nodes RegsEquiv Image Ceiling ITreeFO RegsEquivFO.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Lib.MState.PropExec OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Lib.MState OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Lib.Frame OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Lib.Exec OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Lib.ITree OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Lib.Nodes OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Lib.RegsEquiv OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Lib.Image OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Lib.Ceiling OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Lib.ITreeFO OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Lib.RegsEquivFO.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit Require Import TopLevel HaltsFO.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Spec Require Import Prog ModelInv.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.World Require Import Tgt_example_small_fuzzer_ubsan.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U Require Zlib_iface Zlib_closed Impl_closed.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.FO Require Import FOCore.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.

(** The UBSan build: halting under memory forced-only, no budget premise. *)
Theorem halts_ubsan_core :
  halts_core alloc_forced_cfg source_alloc_limit AnyExit.codes
    (mkImage Tgt_example_small_fuzzer_ubsan.M.loaded_segments
             Tgt_example_small_fuzzer_ubsan.M.init_pc
             Tgt_example_small_fuzzer_ubsan.M.phdrs).
Proof.
  intros en inp He Hi.
  pose proof (valid_input_va_size _ Hi) as Hsv48.
  pose proof (U.Impl_closed.impl_U_of_zlib (fun CE => @U.Zlib_closed.zR CE) U.Zlib_closed.zlib_closed_all
                en inp He Hi) as Himpl.
  assert (Htop : (bv_unsigned (en_sp en) - stack_max_size)%Z
                 = @alloc_ceiling (ceiling_of_sp (bv_unsigned (en_sp en)))).
  { rewrite <- (mo0_alloc_top usegs source_alloc_limit en inp).
    exact (mo0_alloc_top_ceiling usegs _ _ source_alloc_limit en inp Hsv48 He). }
  destruct (prog_model_ok (CE__ := ceiling_of_sp (bv_unsigned (en_sp en))) usegs ustage _ _
              source_alloc_limit en inp segs_ok_usegs He (valid_input_either_of_valid_input _ Hi) Htop)
    as [Hl Hs].
  exact (must_exit_in_scfg_of_tree usegs _ _ source_alloc_limit _ _ en inp (valid_input_channel_reader _ Hi)
           Himpl Hl Hs).
Qed.
