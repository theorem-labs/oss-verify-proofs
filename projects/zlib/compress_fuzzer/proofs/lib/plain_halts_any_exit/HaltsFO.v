(** * HaltsFO — compress_fuzzer plain halts over the filtered run, for the ISSUED (unpatched) binary

    Submission 5's [HaltsP.halts_plain] proved the may-fail statement about a rebuild of the plain binary with
    harness patch 02 (a failed assert exits 1).  The issued binary is not patched: a failed assert calls
    __assert_fail, which aborts, and death by signal is exactly what the halting statement forbids.  So:

    - every address the walks name was moved to the issued link (port/reloc/compress_fuzzer, applied to the
      bundle files before anything else), and the harness walk stops at each failed check
      ([P.Zc_fuzz.fz_check]), where the model now has an unreachable leaf ([Spec.ZTargetC.check_failM]);
    - the model is shown never to reach that leaf on the runs where no allocation fails
      ([Spec.TargetSafeR.fuzz_one_R], over [Spec.MSafeR]), from ONE hypothesis,
      [Spec.TargetSafeR.NoCkFail] : forall d k, harness_outC ZApiInstC.zinstC d <> HC_exit k, the conclusion
      of part C's [harness_no_ckfail_all];
    - those runs are all the runs: the node relation is the filtered one ([Nodes.nodes_sound_fo]) and the
      no-refusal fact [Spec.ProgNoEnomem] holds on it (as for example_dict_fuzzer).

    The result is the forced-only core with no budget premise, under [NoCkFail]. *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence MustExit HaltsAllowed.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Sem.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Lib Require Import PropExec MState Frame Exec ITree Nodes RegsEquiv Image Ceiling MustExitTree.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Lib Require Import ITreeFO RegsEquivFO MustExitTreeFO.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit Require Import TopLevel Obligations.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec Require Import Prog ModelInv MSafeR TargetSafeR.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec Require ProgDetIface Unforced ProgNoEnomem.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.World Require Import Src_zlib_compress_fuzzer_repro.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.P Require Rnd Zlib_iface Zlib_closed Impl_closed.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.FO Require Import FOCore.
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
(* port727: at 
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

(** The stack top the kernel places is the ceiling the model is run with ([ProgDet.run_ceiling_eq]). *)
Lemma run_ceiling_eq : forall segs pc ph en inp,
  in_va_size inp = Sv48 ->
  valid_entry (mkImage segs pc ph) en inp ->
  bv_unsigned (en_sp en) - stack_max_size = @alloc_ceiling (run_ceiling en).
Proof.
  intros segs pc ph en inp Hsv48 Hve. rewrite (valid_entry_sv48 _ _ _ Hsv48) in Hve.
  destruct en as [sp brk mb rnd]. destruct Hve as (Hsp & _ & _ & _). destruct Hsp as (H1 & H2 & H3).
  cbn [en_sp]. unfold run_ceiling, sp_window_lo, sp_window_hi, stack_max_size in *. cbn [en_sp].
  rewrite ceiling_of_sp_eq; [reflexivity| lia| exact H3].
Qed.

Lemma tsafe_no_enomem_R : forall {R} (t : itree node R) mo,
  tsafe nstep ProgDetIface.no_enomem t mo -> tsafe nstep no_enomemR t mo.
Proof.
  intros R t. induction t as [r|n k IH]; intros mo H; cbn in *; [exact I|].
  destruct H as [Hn Hk]. split; [destruct n; exact Hn|]. intros rsp mo' evs Hst. apply IH. exact (Hk rsp mo' evs Hst).
Qed.

(** The program tree's two model facts, on the filtered run, from [NoCkFail] and the no-refusal fact. *)
Theorem prog_model_ok_run : NoCkFail -> forall segs rstage pc ph lim en inp,
  segs_ok segs ->
  ProgDetIface.prog_no_enomem_stmt segs rstage pc ph lim ->
  valid_entry (mkImage segs pc ph) en inp -> valid_input_either inp ->
  leaves_unreachable_m nstep (the_prog segs rstage inp en) (mo0 segs lim en inp)
  /\ tsafe nstep nsafe (the_prog segs rstage inp en) (mo0 segs lim en inp).
Proof.
  intros NoCk segs rstage pc ph lim en inp Hsegs Hne Hve Hvi. unfold the_prog.
  apply (prog_model_ok (CE__ := run_ceiling en) NoCk segs rstage pc ph lim en inp Hsegs Hve Hvi
           (run_ceiling_eq segs pc ph en inp (vie_va_size _ Hvi) Hve)).
  apply tsafe_no_enomem_R. exact (Hne en inp Hve Hvi).
Qed.

(** The forced-only core of a build from its program-tree refinement, the no-refusal fact and [NoCkFail]. *)
Theorem halts_core_of_impl : NoCkFail -> forall segs rstage pc ph,
  segs_ok segs ->
  (forall en inp, valid_entry (mkImage segs pc ph) en inp -> valid_input inp ->
     impl segs (at_node segs) (the_prog segs rstage inp en) (epost the_post) (ms0 segs pc ph en inp)) ->
  ProgDetIface.prog_no_enomem_stmt segs rstage pc ph source_alloc_limit ->
  halts_core alloc_forced_cfg source_alloc_limit AnyExit.codes (mkImage segs pc ph).
Proof.
  intros NoCk segs rstage pc ph Hsegs Himpl Hne en inp He Hi.
  destruct (prog_model_ok_run NoCk segs rstage pc ph source_alloc_limit en inp Hsegs Hne He
              (valid_input_either_of_valid_input _ Hi)) as [Hl Hs].
  exact (must_exit_in_scfg_of_tree segs pc ph source_alloc_limit (the_prog segs rstage inp en) (epost the_post)
           en inp (valid_input_channel_reader _ Hi) (Himpl en inp He Hi) Hl Hs).
Qed.

Lemma prog_no_enomem_P :
  ProgDetIface.prog_no_enomem_stmt psegs pstage Src_zlib_compress_fuzzer_repro.M.init_pc
    Src_zlib_compress_fuzzer_repro.M.phdrs source_alloc_limit.
Proof. apply ProgNoEnomem.prog_no_enomem_P_lim. unfold Unforced.KLIM, Unforced.SMALLREQ, source_alloc_limit. lia. Qed.

(** The issued plain build: halting under memory forced-only, no budget premise, given [NoCkFail]. *)
Theorem halts_plain_core : NoCkFail ->
  halts_core alloc_forced_cfg source_alloc_limit AnyExit.codes
    (mkImage Src_zlib_compress_fuzzer_repro.M.loaded_segments Src_zlib_compress_fuzzer_repro.M.init_pc
             Src_zlib_compress_fuzzer_repro.M.phdrs).
Proof.
  intros NoCk.
  exact (halts_core_of_impl NoCk psegs pstage _ _ segs_ok_psegs
           (P.Impl_closed.impl_P_of_zlib (fun CE => @P.Zlib_closed.zR CE) P.Zlib_closed.zlib_closed_all)
           prog_no_enomem_P).
Qed.
