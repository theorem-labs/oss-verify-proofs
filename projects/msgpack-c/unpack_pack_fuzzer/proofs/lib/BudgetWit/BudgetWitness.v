(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from Glue/TopHypsSrc.v and Theorems.v: the budget-premise witness for the plain build and the lemmas that apply the three agreement proofs there. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (usage_rzb takes the launch and channel-reader facts of the input, read with the input's other conjuncts at their LPS c0dd863a positions; the usage walk over the image's own segments is lifted to the run's segment list by RzbRom.rzb_run_init before rzb_never_refused(_cfg)). *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType StackLayout Fs State Run.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From OSSVerify.Core Require Import Shapes.
From OSSVerify.Core Require Premises.
From OSSVerify.msgpack_c.unpack_pack_fuzzer Require Images Statements.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Img Require Import ImgSrc.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib Require Theorems.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.BudgetWit Require Import Rzb RzbRom TopB.
Import ListNotations.
Open Scope Z_scope.

(** * msgpack-c / unpack_pack_fuzzer: the plain build meets the agreement statements' premises together

    [Statements.asan_agrees], [Statements.ubsan_agrees] and
    [Statements.asan_ubsan_agrees] are [agrees_in_abort_modelled
    Env.alloc_forced_only lim_plain lim_san Images.plain san].  Each
    quantifies over entries [en_plain], [en_san] and an input [inp] and has
    four premises: [valid_entry Images.plain en_plain inp], [valid_entry san
    en_san inp], [valid_input_abort inp] and the budget premise [~
    run_scfg_budget_refused Env.alloc_forced_only Images.plain lim_plain
    en_plain inp], with lim_plain [Budgets.Asan.lim_source] (2 GiB) for the
    two ASan pairs and [Budgets.Standard.lim_source] (16 GiB) for the UBSan
    pair.  [OSSVerify.Core.Premises] gives the first three for every
    well-formed image and leaves the fourth, which reads the run; this file
    gives the fourth.

    The input is [Premises.witness_input true]: one empty argument (so argc =
    1), no environment, an empty file system, abort declared as death by
    SIGABRT.  With argc <> 2 the driver writes its usage line to fd 2 and
    exits with status 2.  On that path the program makes three kinds of system
    call: set_tid_address (96) in musl's start-up, writev (66) for the line,
    exit or exit_group (93, 94).  None is an allocation call (brk 214, mremap
    216, mmap 222, mprotect 226), so no configuration the run reaches is
    refused by the budget.

    The proof is the released proof of that path ([Glue.RunSrc.rz_usage] and
    the certificate nodes [Glue.Run.SrcNU_1] to [SrcNU_6] it rests on),
    restated over [BudgetWit.Rzb.rzb], the released [ShapeAlg.realizes] with
    a budget check at each node ([BudgetWit.Rzb] says why [realizes] itself
    cannot carry the fact).  [BudgetWit.TopB.rzb_usage_top] is that walk, over
    the image's own segments; [BudgetWit.RzbRom.rzb_run_init] lifts it to the
    run's segment list [run_segments SEGS inp sp mb], which the budget premise
    reads, and [Rzb.rzb_never_refused] turns it into the budget premise, for
    every spurious-failure configuration ([usage_never_refused]) and for the
    unconfigured run ([usage_never_refused_run]).  The released walk builds the
    heap invariant of the start-up code for a budget of at least 2 GiB
    ([Glue.TopHypsSrc.aw_init]), so both lemmas take [2 ^ 31 <= lim]; both
    budgets the statements use meet it.

    [plain_budget_witness] is the four premises at one pair of entries and one
    input; [asan_agrees_not_vacuous], [ubsan_agrees_not_vacuous] and
    [asan_ubsan_agrees_not_vacuous] give them to the released proofs (the
    terms that each statement's [Proof.v] is), so each statement's conclusion
    holds at entries and an input that meet all its premises, with no
    hypothesis left.  Non-vacuous; shown on the usage path, not yet on a fuzz
    input. *)

Lemma lim_asan : 2 ^ 31 <= Budgets.Asan.lim_source.
Proof. apply Z.leb_le. reflexivity. Qed.

Lemma lim_standard : 2 ^ 31 <= Budgets.Standard.lim_source.
Proof. apply Z.leb_le. reflexivity. Qed.

(** The plain image has no vDSO segment of its own: the run appends the pair
    ([run_segments]). *)
Lemma vdso_image_SEGS : RiscvSemantics.vdso_image SEGS = None.
Proof. reflexivity. Qed.

(** The usage walk at an entry of the plain build. *)
Lemma usage_rzb : forall sp brk0 mb rnd lim inp,
  valid_entry OSSVerify.msgpack_c.unpack_pack_fuzzer.Images.plain (mkEntry sp brk0 mb rnd) inp ->
  valid_argv (in_argv inp) -> valid_envp (in_envp inp) -> valid_hwcap (in_hwcap inp) ->
  in_va_size inp = Sv48 -> valid_launch inp -> in_channel_reader inp = true -> 2 ^ 31 <= lim -> (length (in_argv inp) <> 2)%nat ->
  rzb SEGS (init_config SEGS PC PH sp brk0 mb rnd lim inp) (OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Glue.DrvShape.DrvShape.K inp).
Proof.
  intros sp brk0 mb rnd lim inp Hen Hva Hve Hhw Hsz Hvl Hrdr Hlim Hlen.
  exact (TopB.rzb_usage_top inp sp brk0 mb rnd lim Hva Hve Hhw Hsz Hvl Hrdr Hen Hlim Hlen).
Qed.

(** On every valid entry of the plain build and every input whose argv has
    not two entries, no configuration of the run is refused by the budget,
    whatever the spurious-failure configuration, for every limit of at least
    2 GiB.  Stated for the abort-modelled inputs these statements quantify
    over, and below for [valid_input]. *)
Theorem usage_never_refused : forall en inp,
  valid_entry OSSVerify.msgpack_c.unpack_pack_fuzzer.Images.plain en inp -> valid_input_abort inp ->
  (length (in_argv inp) <> 2)%nat ->
  forall (cfg : SpuriousCfg) (lim : Z), 2 ^ 31 <= lim ->
  ~ run_scfg_budget_refused cfg OSSVerify.msgpack_c.unpack_pack_fuzzer.Images.plain lim en inp.
Proof.
  intros [sp brk0 mb rnd] inp Hen Hinp Hlen cfg lim Hlim.
  (* the input's conjuncts at LPS c0dd863a: argv, envp, fs, the image's keys and realness, creds, nofile,
     sigmask, hwcap, the abort stance, the VA size, urandom, the launch, the far-end reader, ... *)
  destruct Hinp as (Hva & Hve & _ & _ & _ & _ & _ & _ & Hhw & _ & Hsz & _ & Hvl & Hrdr & _).
  exact (rzb_never_refused_cfg (run_segments SEGS inp sp mb) cfg _ _
           (rzb_run_init SEGS inp sp mb PC PH brk0 rnd lim _ vdso_image_SEGS
              (usage_rzb sp brk0 mb rnd lim inp Hen Hva Hve Hhw Hsz Hvl Hrdr Hlim Hlen))).
Qed.

Theorem usage_never_refused_valid_input : forall en inp,
  valid_entry OSSVerify.msgpack_c.unpack_pack_fuzzer.Images.plain en inp -> valid_input inp ->
  (length (in_argv inp) <> 2)%nat ->
  forall (cfg : SpuriousCfg) (lim : Z), 2 ^ 31 <= lim ->
  ~ run_scfg_budget_refused cfg OSSVerify.msgpack_c.unpack_pack_fuzzer.Images.plain lim en inp.
Proof.
  intros [sp brk0 mb rnd] inp Hen Hinp Hlen cfg lim Hlim.
  destruct Hinp as (Hva & Hve & _ & _ & _ & _ & _ & _ & Hhw & _ & Hsz & _ & Hvl & Hrdr & _).
  exact (rzb_never_refused_cfg (run_segments SEGS inp sp mb) cfg _ _
           (rzb_run_init SEGS inp sp mb PC PH brk0 rnd lim _ vdso_image_SEGS
              (usage_rzb sp brk0 mb rnd lim inp Hen Hva Hve Hhw Hsz Hvl Hrdr Hlim Hlen))).
Qed.

(** The same for the unconfigured run ([Run.run_budget_refused]). *)
Theorem usage_never_refused_run : forall en inp,
  valid_entry OSSVerify.msgpack_c.unpack_pack_fuzzer.Images.plain en inp -> valid_input_abort inp ->
  (length (in_argv inp) <> 2)%nat ->
  forall (lim : Z), 2 ^ 31 <= lim ->
  ~ run_budget_refused OSSVerify.msgpack_c.unpack_pack_fuzzer.Images.plain lim en inp.
Proof.
  intros [sp brk0 mb rnd] inp Hen Hinp Hlen lim Hlim.
  destruct Hinp as (Hva & Hve & _ & _ & _ & _ & _ & _ & Hhw & _ & Hsz & _ & Hvl & Hrdr & _).
  exact (rzb_never_refused (run_segments SEGS inp sp mb) _ _
           (rzb_run_init SEGS inp sp mb PC PH brk0 rnd lim _ vdso_image_SEGS
              (usage_rzb sp brk0 mb rnd lim inp Hen Hva Hve Hhw Hsz Hvl Hrdr Hlim Hlen))).
Qed.

(** The four premises of each agreement statement hold together, at
    [Premises.witness_input true] and the entries [Premises.valid_input_abort_entry]
    gives for it: the plain build's budget premise at both limits, and valid
    entries of all four builds on the same input. *)
Theorem plain_budget_witness :
  exists en inp,
    valid_entry OSSVerify.msgpack_c.unpack_pack_fuzzer.Images.plain en inp /\ valid_input_abort inp /\
    ~ run_scfg_budget_refused Env.alloc_forced_only OSSVerify.msgpack_c.unpack_pack_fuzzer.Images.plain
        Budgets.Asan.lim_source en inp /\
    ~ run_scfg_budget_refused Env.alloc_forced_only OSSVerify.msgpack_c.unpack_pack_fuzzer.Images.plain
        Budgets.Standard.lim_source en inp /\
    (exists e, valid_entry OSSVerify.msgpack_c.unpack_pack_fuzzer.Images.asan e inp) /\
    (exists e, valid_entry OSSVerify.msgpack_c.unpack_pack_fuzzer.Images.ubsan e inp) /\
    (exists e, valid_entry OSSVerify.msgpack_c.unpack_pack_fuzzer.Images.asan_ubsan e inp).
Proof.
  destruct (Premises.valid_input_abort_entry OSSVerify.msgpack_c.unpack_pack_fuzzer.Images.plain
              (Premises.witness_input true) OSSVerify.msgpack_c.unpack_pack_fuzzer.Images.plain_wf
              Premises.witness_valid_input_abort) as [en Hen].
  exists en, (Premises.witness_input true).
  split; [exact Hen | split; [exact Premises.witness_valid_input_abort |]].
  split; [apply (usage_never_refused en _ Hen Premises.witness_valid_input_abort);
          [cbn; discriminate | exact lim_asan] |].
  split; [apply (usage_never_refused en _ Hen Premises.witness_valid_input_abort);
          [cbn; discriminate | exact lim_standard] |].
  split; [exact (Premises.valid_input_abort_entry _ _ OSSVerify.msgpack_c.unpack_pack_fuzzer.Images.asan_wf
                   Premises.witness_valid_input_abort) |].
  split; [exact (Premises.valid_input_abort_entry _ _ OSSVerify.msgpack_c.unpack_pack_fuzzer.Images.ubsan_wf
                   Premises.witness_valid_input_abort) |].
  exact (Premises.valid_input_abort_entry _ _ OSSVerify.msgpack_c.unpack_pack_fuzzer.Images.asan_ubsan_wf
           Premises.witness_valid_input_abort).
Qed.

(** [Statements.asan_agrees], which the released
    [Theorems.strong_universal_error_free_unpack_pack_fuzzer_asan] proves, at
    entries and an input that meet all four of its premises: its conclusion
    holds there with no hypothesis left. *)
Theorem asan_agrees_not_vacuous :
  exists (en_plain en_san : ExecEntry) (inp : ProcInput),
    valid_entry OSSVerify.msgpack_c.unpack_pack_fuzzer.Images.plain en_plain inp /\
    valid_entry OSSVerify.msgpack_c.unpack_pack_fuzzer.Images.asan en_san inp /\
    valid_input_abort inp /\
    ~ run_scfg_budget_refused Env.alloc_forced_only OSSVerify.msgpack_c.unpack_pack_fuzzer.Images.plain
        Budgets.Asan.lim_source en_plain inp /\
    (error_free_unkilled (run_scfg Env.alloc_forced_only OSSVerify.msgpack_c.unpack_pack_fuzzer.Images.plain
                            Budgets.Asan.lim_source en_plain inp)
     /\ error_free_unkilled (run_scfg Env.alloc_forced_only OSSVerify.msgpack_c.unpack_pack_fuzzer.Images.asan
                               Budgets.Asan.lim_target en_san inp)
     /\ trace_equiv (bh_traces (run_scfg Env.alloc_forced_only OSSVerify.msgpack_c.unpack_pack_fuzzer.Images.plain
                                  Budgets.Asan.lim_source en_plain inp))
                    (bh_traces (run_scfg Env.alloc_forced_only OSSVerify.msgpack_c.unpack_pack_fuzzer.Images.asan
                                  Budgets.Asan.lim_target en_san inp))).
Proof.
  destruct plain_budget_witness as (en & inp & Hen & Hinp & Hnr & _ & (es & Hes) & _ & _).
  exists en, es, inp.
  split; [exact Hen | split; [exact Hes | split; [exact Hinp | split; [exact Hnr |]]]].
  exact ((OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Theorems.strong_universal_error_free_unpack_pack_fuzzer_asan
          : OSSVerify.msgpack_c.unpack_pack_fuzzer.Statements.asan_agrees) en es inp Hen Hes Hinp Hnr).
Qed.

(** [Statements.ubsan_agrees], which the released
    [Theorems.strong_universal_error_free_unpack_pack_fuzzer_ubsan] proves, at
    entries and an input that meet all four of its premises. *)
Theorem ubsan_agrees_not_vacuous :
  exists (en_plain en_san : ExecEntry) (inp : ProcInput),
    valid_entry OSSVerify.msgpack_c.unpack_pack_fuzzer.Images.plain en_plain inp /\
    valid_entry OSSVerify.msgpack_c.unpack_pack_fuzzer.Images.ubsan en_san inp /\
    valid_input_abort inp /\
    ~ run_scfg_budget_refused Env.alloc_forced_only OSSVerify.msgpack_c.unpack_pack_fuzzer.Images.plain
        Budgets.Standard.lim_source en_plain inp /\
    (error_free_unkilled (run_scfg Env.alloc_forced_only OSSVerify.msgpack_c.unpack_pack_fuzzer.Images.plain
                            Budgets.Standard.lim_source en_plain inp)
     /\ error_free_unkilled (run_scfg Env.alloc_forced_only OSSVerify.msgpack_c.unpack_pack_fuzzer.Images.ubsan
                               Budgets.Standard.lim_target en_san inp)
     /\ trace_equiv (bh_traces (run_scfg Env.alloc_forced_only OSSVerify.msgpack_c.unpack_pack_fuzzer.Images.plain
                                  Budgets.Standard.lim_source en_plain inp))
                    (bh_traces (run_scfg Env.alloc_forced_only OSSVerify.msgpack_c.unpack_pack_fuzzer.Images.ubsan
                                  Budgets.Standard.lim_target en_san inp))).
Proof.
  destruct plain_budget_witness as (en & inp & Hen & Hinp & _ & Hnr & _ & (es & Hes) & _).
  exists en, es, inp.
  split; [exact Hen | split; [exact Hes | split; [exact Hinp | split; [exact Hnr |]]]].
  exact ((OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Theorems.strong_universal_error_free_unpack_pack_fuzzer_ubsan
          : OSSVerify.msgpack_c.unpack_pack_fuzzer.Statements.ubsan_agrees) en es inp Hen Hes Hinp Hnr).
Qed.

(** [Statements.asan_ubsan_agrees], which the released
    [Theorems.strong_universal_error_free_unpack_pack_fuzzer_both] proves, at
    entries and an input that meet all four of its premises. *)
Theorem asan_ubsan_agrees_not_vacuous :
  exists (en_plain en_san : ExecEntry) (inp : ProcInput),
    valid_entry OSSVerify.msgpack_c.unpack_pack_fuzzer.Images.plain en_plain inp /\
    valid_entry OSSVerify.msgpack_c.unpack_pack_fuzzer.Images.asan_ubsan en_san inp /\
    valid_input_abort inp /\
    ~ run_scfg_budget_refused Env.alloc_forced_only OSSVerify.msgpack_c.unpack_pack_fuzzer.Images.plain
        Budgets.Asan.lim_source en_plain inp /\
    (error_free_unkilled (run_scfg Env.alloc_forced_only OSSVerify.msgpack_c.unpack_pack_fuzzer.Images.plain
                            Budgets.Asan.lim_source en_plain inp)
     /\ error_free_unkilled (run_scfg Env.alloc_forced_only OSSVerify.msgpack_c.unpack_pack_fuzzer.Images.asan_ubsan
                               Budgets.Asan.lim_target en_san inp)
     /\ trace_equiv (bh_traces (run_scfg Env.alloc_forced_only OSSVerify.msgpack_c.unpack_pack_fuzzer.Images.plain
                                  Budgets.Asan.lim_source en_plain inp))
                    (bh_traces (run_scfg Env.alloc_forced_only OSSVerify.msgpack_c.unpack_pack_fuzzer.Images.asan_ubsan
                                  Budgets.Asan.lim_target en_san inp))).
Proof.
  destruct plain_budget_witness as (en & inp & Hen & Hinp & Hnr & _ & _ & _ & (es & Hes)).
  exists en, es, inp.
  split; [exact Hen | split; [exact Hes | split; [exact Hinp | split; [exact Hnr |]]]].
  exact ((OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Theorems.strong_universal_error_free_unpack_pack_fuzzer_both
          : OSSVerify.msgpack_c.unpack_pack_fuzzer.Statements.asan_ubsan_agrees) en es inp Hen Hes Hinp Hnr).
Qed.
