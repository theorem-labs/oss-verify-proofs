(** * HaltsFO — example_small_fuzzer plain halts over the filtered run (twin of [Halts.halts_plain])

    [Halts.halts_plain] proved the may-fail statement over the patch-04 spec, through
    [Lib.MustExitTree.tree_at_must_exit_in] and the unfiltered [Nodes.nodes_sound].  Since the port the
    node relation is sound for [Run.sstep_cfg alloc_forced_cfg] ([Nodes.nodes_sound_fo]), and the same
    three tree facts ([P.Impl_closed.impl_P_of_zlib] and [Spec.ModelInv.prog_model_ok], unchanged text)
    give [MustExit.must_exit_in_scfg alloc_forced_cfg] through [ITreeFO.impl_run_must_exit2_cfg], with no
    budget premise ([FOCore.halts_core]).  The UBSan build is not part of tier 0, so this file reads only
    the plain build's proof. *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence MustExit HaltsAllowed.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Sem.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Lib Require MState.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Lib Require MState Frame Exec ITree Nodes RegsEquiv Image Ceiling ITreeFO RegsEquivFO.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Lib.MState.PropExec OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Lib.MState OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Lib.Frame OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Lib.Exec OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Lib.ITree OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Lib.Nodes OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Lib.RegsEquiv OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Lib.Image OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Lib.Ceiling OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Lib.ITreeFO OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Lib.RegsEquivFO.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit Require Import TopLevel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Spec Require Import Prog ModelInv.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.World Require Import Src_zlib_example_small_fuzzer_repro.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Zlib_iface Zlib_closed Impl_closed.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.FO Require Import FOCore.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.

(** Every exit node's status is in [AnyExit.codes] (the bundle's [Halts.nodes_exits_ok], first half). *)
Lemma nexit_any_exit_fo : forall n mo1 code mo2,
  nexit n mo1 code mo2 -> In code AnyExit.codes.
Proof.
  intros n mo1 code mo2 H. destruct n; cbn [nexit] in H; try contradiction.
  destruct H as [-> _]. apply any_exit_covers_masked_status.
Qed.

(** [Halts.halts_of_tree] over the filtered run: a tree's three facts give halting under
    [alloc_forced_cfg]. *)
Theorem must_exit_in_scfg_of_tree : forall {R : Type} segs pc ph lim (t : itree node R)
    (Q : R -> machine_state -> Prop) en inp,
  in_channel_reader inp = true ->
  impl segs (at_node segs) t Q (ms0 segs pc ph en inp) ->
  leaves_unreachable_m nstep t (mo0 segs lim en inp) ->
  tsafe nstep nsafe t (mo0 segs lim en inp) ->
  must_exit_in_scfg alloc_forced_cfg AnyExit.codes (mkImage segs pc ph) lim en inp.
Proof.
  (* at 727298f3 [must_exit_in_scfg] reads the run's list [run_segments segs inp sp mbase] =
     [segs ++ vdso_segments ..].  The tree stays over [segs] and is carried to the run's list by TopLevel's
     [impl_lift] (the vDSO pair is never executable: [vdso_nonexec]); the model is still [mo0]
     ([init_config_run_eq]).  NEW PREMISE: the launch's channel reader, which [mo0_minv] needs; the two callers
     discharge it from [valid_input] by Run's [valid_input_channel_reader]. *)
  intros R segs pc ph lim t Q en inp Hrdr Himpl Hleaves Hsafe.
  destruct en as [sp brk mb rnd]. cbn [must_exit_in_scfg]. cbv zeta.
  pose proof (init_config_run_eq segs pc ph lim (mkEntry sp brk mb rnd) inp) as EC.
  cbn [en_sp en_brk en_mmap_base en_draw] in EC. rewrite EC. clear EC.
  unfold run_segments.
  apply must_exit_in_at_cfg_init_ms.
  pose proof (impl_lift segs (vdso_segments (in_kernel inp) sp mb) t Q (ms0 segs pc ph (mkEntry sp brk mb rnd) inp)
                (vdso_nonexec _ _ _) Himpl) as Himpl'.
  rewrite set_rom_ms0 in Himpl'. cbn [en_sp en_mmap_base en_draw] in Himpl'.
  exact (impl_run_must_exit2_cfg alloc_forced_cfg node (segs ++ vdso_segments (in_kernel inp) sp mb)
           (at_node (segs ++ vdso_segments (in_kernel inp) sp mb)) nstep nexit minv nsafe
           (nodes_sound_fo (segs ++ vdso_segments (in_kernel inp) sp mb)) AnyExit.codes t _ _ _ Himpl' Hleaves
           (mo0_not_halted _ _ _ _) (mo0_minv _ _ _ _ Hrdr) Hsafe nexit_any_exit_fo).
Qed.

(** The core claim for the plain build: halting under the forced-only configuration at the shipped
    budget, no budget premise. *)
Theorem halts_plain_core :
  halts_core alloc_forced_cfg source_alloc_limit AnyExit.codes
    (mkImage Src_zlib_example_small_fuzzer_repro.M.loaded_segments
             Src_zlib_example_small_fuzzer_repro.M.init_pc
             Src_zlib_example_small_fuzzer_repro.M.phdrs).
Proof.
  intros en inp He Hi.
  pose proof (valid_input_va_size _ Hi) as Hsv48.
  pose proof (P.Impl_closed.impl_P_of_zlib (fun CE => @P.Zlib_closed.zR CE) P.Zlib_closed.zlib_closed_all
                en inp He Hi) as Himpl.
  assert (Htop : (bv_unsigned (en_sp en) - stack_max_size)%Z
                 = @alloc_ceiling (ceiling_of_sp (bv_unsigned (en_sp en)))).
  { rewrite <- (mo0_alloc_top psegs source_alloc_limit en inp).
    exact (mo0_alloc_top_ceiling psegs _ _ source_alloc_limit en inp Hsv48 He). }
  destruct (prog_model_ok (CE__ := ceiling_of_sp (bv_unsigned (en_sp en))) psegs pstage _ _
              source_alloc_limit en inp segs_ok_psegs He (valid_input_either_of_valid_input _ Hi) Htop)
    as [Hl Hs].
  exact (must_exit_in_scfg_of_tree psegs _ _ source_alloc_limit _ _ en inp (valid_input_channel_reader _ Hi)
           Himpl Hl Hs).
Qed.
