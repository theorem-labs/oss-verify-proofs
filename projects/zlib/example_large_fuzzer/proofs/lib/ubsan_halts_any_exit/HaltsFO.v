(** * HaltsFO — example_large_fuzzer plain halts over the filtered run (twin of the plain half of [Halts])

    Submission 4's [Halts.halts_plain] proved the may-fail statement over the lps patch-04 spec.  On the
    unpatched spec that statement is out of reach: a MAP_FIXED PROT_NONE mmap over live memory may then
    answer -ENOMEM (range kept, or range destroyed), which the tree never handles
    ([KStep.nstep_mmap_fixed_inv]).  Since the port the node relation is the FILTERED one ([Nodes.nstep]
    drops a refusal beside a grant, [Nodes.nodes_sound_fo]), where those refusals are spurious, and the same
    tree facts ([ModelInv.prog_model_ok], unchanged text) give the forced-only core directly through
    [MustExitTreeFO.tree_at_must_exit_in_cfg], with no budget premise ([FOCore.halts_core]).  The UBSan
    build is not part of tier 0, so its cone stays out of the build. *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence MustExit HaltsAllowed.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Sem.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Lib Require Import PropExec MState Frame Exec ITree Nodes RegsEquiv Image Ceiling MustExitTree.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Lib Require Import ITreeFO RegsEquivFO MustExitTreeFO.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit Require Import TopLevel Obligations.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Spec Require Import Prog ModelInv ProgDet.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.World Require Import Src_zlib_example_large_fuzzer_repro.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.P Require Rnd Zlib_iface Zlib_closed Impl_closed.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.FO Require Import FOCore.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.

(** Every exit node exits with an allowed status and is not killed. *)
Lemma nodes_exits_ok : forall segs, @exits_ok node (at_node segs) nexit minv nsafe AnyExit.codes.
Proof.
  intros segs n ms mo code mo' _ Hh _ _ Hex.
  destruct n; cbn [nexit] in Hex; try contradiction.
  destruct Hex as [-> ->]. split; [apply any_exit_covers_masked_status| apply m_killed_with_halted].
Qed.

(** A node tree's three facts give [must_exit_in_scfg] at the forced-only configuration. *)
(* at 727298f3
   [must_exit_in_scfg] reads the run's list [run_segments segs inp sp mbase] = [segs ++ vdso_segments ..]
   (MustExit.v l.1306).  The tree stays over [segs] and is carried to the run's list by TopLevel's [impl_lift]
   (the vDSO pair is never executable: [vdso_nonexec]); the model is still [mo0] ([init_config_run_eq]).
   NEW PREMISE: the launch's channel reader, which [mo0_minv] needs; [halts_core_of_impl] discharges it from
   [valid_input] by Run's [valid_input_channel_reader]. *)
Theorem must_exit_in_scfg_of_tree : forall {R : Type} segs pc ph lim (t : itree node R)
    (Q : R -> machine_state -> Prop) en inp,
  in_channel_reader inp = true ->
  impl segs (at_node segs) t Q (ms0 segs pc ph en inp) ->
  leaves_unreachable_m nstep t (mo0 segs lim en inp) ->
  tsafe nstep nsafe t (mo0 segs lim en inp) ->
  must_exit_in_scfg alloc_forced_cfg AnyExit.codes (mkImage segs pc ph) lim en inp.
Proof.
  intros R segs pc ph lim t Q en inp Hrdr Himpl Hleaves Hsafe.
  destruct en as [sp brk mb rnd]. cbn [must_exit_in_scfg]. cbv zeta.
  pose proof (init_config_run_eq segs pc ph lim (mkEntry sp brk mb rnd) inp) as EC.
  cbn [en_sp en_brk en_mmap_base en_draw] in EC. rewrite EC. clear EC.
  unfold run_segments.
  apply must_exit_in_at_cfg_init_ms.
  pose proof (impl_lift segs (vdso_segments (in_kernel inp) sp mb) t Q (ms0 segs pc ph (mkEntry sp brk mb rnd) inp)
                (vdso_nonexec _ _ _) Himpl) as Himpl'.
  rewrite set_rom_ms0 in Himpl'. cbn [en_sp en_mmap_base en_draw] in Himpl'.
  exact (tree_at_must_exit_in_cfg alloc_forced_cfg node (segs ++ vdso_segments (in_kernel inp) sp mb)
           (at_node (segs ++ vdso_segments (in_kernel inp) sp mb)) nstep nexit minv nsafe
           (nodes_sound_fo (segs ++ vdso_segments (in_kernel inp) sp mb)) AnyExit.codes
           (nodes_exits_ok (segs ++ vdso_segments (in_kernel inp) sp mb)) _ t _ _ _
           (conj Himpl' (conj Hleaves (conj (mo0_not_halted _ _ _ _) (conj (mo0_minv _ _ _ _ Hrdr) Hsafe))))).
Qed.

(** The forced-only core of a build (halting at every valid entry and input, no budget premise) from its
    program-tree refinement. *)
Theorem halts_core_of_impl : forall segs rstage pc ph,
  segs_ok segs ->
  (forall en inp, valid_entry (mkImage segs pc ph) en inp -> valid_input inp ->
     impl segs (at_node segs) (the_prog segs rstage inp en) (epost the_post) (ms0 segs pc ph en inp)) ->
  halts_core alloc_forced_cfg source_alloc_limit AnyExit.codes (mkImage segs pc ph).
Proof.
  intros segs rstage pc ph Hsegs Himpl en inp He Hi.
  destruct (prog_model_ok (CE__:=run_ceiling en) segs rstage pc ph source_alloc_limit en inp Hsegs He
              (valid_input_either_of_valid_input _ Hi) (run_ceiling_eq _ _ _ _ _ (valid_input_va_size _ Hi) He)) as [Hl Hs].
  exact (must_exit_in_scfg_of_tree segs pc ph source_alloc_limit (the_prog segs rstage inp en) (epost the_post) en inp
           (valid_input_channel_reader _ Hi) (Himpl en inp He Hi) Hl Hs).
Qed.

(** The plain build: halting under memory forced-only, no budget premise. *)
Theorem halts_plain_core :
  halts_core alloc_forced_cfg source_alloc_limit AnyExit.codes
    (mkImage Src_zlib_example_large_fuzzer_repro.M.loaded_segments Src_zlib_example_large_fuzzer_repro.M.init_pc
             Src_zlib_example_large_fuzzer_repro.M.phdrs).
Proof.
  exact (halts_core_of_impl psegs pstage _ _ segs_ok_psegs
           (P.Impl_closed.impl_P_of_zlib (fun CE => @P.Zlib_closed.zR CE) P.Zlib_closed.zlib_closed_all)).
Qed.
