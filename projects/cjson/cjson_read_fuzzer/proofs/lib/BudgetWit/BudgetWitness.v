(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from the argc <> 2 arms of P/DrvTop.v's p_main_body and from Glue/Top04.v's plain_realizes04_lim, over BudgetWit.Rzb.rzb; adds the budget-premise witness for the plain build and the lemmas that apply the released proofs of the three statements whose budget premise is on the plain build there. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3: p_main_usage_b and usage_rzb take the launch premise entry_launch_ok_va, the vDSO run state and the heap ceiling and secret, and read the entry facts as P/DrvTop.v's p_main_body does there; p_main_usage_b reads the stack pointer's window bounds off valid_sp and argc's register value (argcN) through the argv split, as P/DrvTop does; usage_never_refused lifts the usage walk over the binary's own segments to the run's run_segments by RzbRom.rzb_run_init. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Run.
From LinuxProcessSemantics.LinuxProcessSem Require Vdso.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib Require PropExec.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib Require WallSim.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib Require PStartup PStartupDefs PStartupFacts Amb RealizesEqv TopUbsan.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Fs Require Import Namei.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import Tac Bytes SCPS.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require Import Prelim Stdio.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require Import PImg CJ_iface CJ_tree F_pad Exit F_printf_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require SO_fprintf.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.SO_fprintf.Stdio_iface.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.SO_fprintf.SO_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require Import RRealloc_iface CJ_heap_inst0.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require Drv_heap.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Drv_heap.KB_drv.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require Import SO_diag SO_emit.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.SO_emit.SO_exit.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require Import Drv_base Drv_entry Drv_heap.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require Drv_hdr.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Drv_hdr.Drv_stmt.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require Drv_usage.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Drv_usage.Drv_exit.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require Import Drv_usage Drv_open Drv_loop Drv_hdr Drv_trun.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require Import CJ_heap_instR.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.CJ_heap_instR.RF_realloc_null.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require Import DrvTop.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib Require Import ShapeAlg ShapeSpec.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib Require Import SspGuard.
From OSSVerify.Core Require Import Shapes.
From OSSVerify.Core Require Premises.
From OSSVerify.cjson.cjson_read_fuzzer Require Images Statements.
From OSSVerify.cjson.cjson_read_fuzzer.images Require Import Plain.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib Require Theorems.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.BudgetWit Require Import Rzb RzbRom PStartupRTB P_SO_fprintfB P_SO_diagB P_SO_emitB P_Drv_usageB.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope Z_scope.
Module PS := OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.PStartup.
Module CE := OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.WallSim.CatExec.
Module AM := OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Amb.
Module RE := OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RealizesEqv.
Module SSP := OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.PStartupDefs.StartupSsp.

Local Notation ppc := Plain.M.init_pc (only parsing).
Local Notation pph := Plain.M.phdrs (only parsing).

(** * cjson / cjson_read_fuzzer: the budget premise on the plain build holds together with the other premises

    Three statements of [Statements] carry a budget premise on the plain build,
    [~ run_scfg_budget_refused cfg Images.plain lim en inp], and are proved on
    main: [ubsan_agrees], at [Env.alloc_forced_only] and
    [Budgets.Standard.lim_source]; [asan_agrees] and [asan_ubsan_agrees], at
    [Env.alloc_forced_only] and [Budgets.Asan.lim_source].  A theorem whose
    premises never hold together proves nothing.  [OSSVerify.Core.Premises]
    gives the entry and input premises for every well-formed image and leaves
    the budget premise, which reads the run; this file gives it for this
    build, for every configuration and every limit.

    The input is [Premises.witness_input false]: one empty argument (so
    argc = 1), no environment, an empty file system.  With argc <> 2 the
    driver's [main] writes its usage line to fd 2 and exits with status 2.
    On that path the program makes three kinds of system call: set_tid_address
    (96) in musl's start-up, writev (66) for the usage line, exit or
    exit_group (93, 94); the exit-time stdout flush finds stdout empty and
    makes none (the flush's ioctl 29 and writev nodes are covered all the
    same).  None is an allocation call (brk 214, mremap 216, mmap 222, mprotect
    226), and no mapping is lazy ([m_vm_lazy = []] throughout), so no
    configuration the run reaches is refused by the budget.  This shows the
    budget premise satisfiable on the usage path, not yet on an input that
    reaches [LLVMFuzzerTestOneInput].

    The released proof of that path is [PStartupRT.p_startup_rt] (start-up)
    and the argc <> 2 arms of [P.DrvTop.p_main_body], whose usage walk is
    [P.Drv_usage.main_usage] with the stderr diagnostic
    ([P.SO_diag.so_diag_usage_proof]) and the exit
    ([P.SO_emit.SO_exit.so_exit_proof]).  All of it is stated in
    [ShapeAlg.realizes]; the files of this directory restate it over
    [BudgetWit.Rzb.rzb], [realizes] with a no-allocation-call check at each
    node ([BudgetWit.Rzb] says why [realizes] itself cannot carry the fact).
    The deep proofs below that layer (the printf model, the stdio exit flush,
    the startup code) are stated over [ITree.impl], [Monad.implM] or a
    caller-chosen predicate, not over [realizes], and are used unchanged.
    [usage_rzb] is the walk; [Rzb.rzb_never_refused_cfg] turns it into the
    budget premise, for every spurious-failure configuration and every limit
    ([usage_never_refused]).  Each [<statement>_not_vacuous] gives the
    premises of one of the three statements at one input to the released
    proof of that statement (the term its [proofs/<statement>/Proof.v] is),
    so the statement's conclusion holds at a point that meets all its
    premises, with no hypothesis left. *)

Section CeilWrap.
Context {ACEIL : Ceil} {AGRD : Guard}.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(** The argc <> 2 arms of [P.DrvTop.p_main_body] (one argument; three or
    more), over [rzb]: [main]'s usage path from its entry. *)
Theorem p_main_usage_b : forall (lim : Z) (sp0 brk mbase : word) (rnd : EntryDraw) (inp : ProcInput) (tid : word) (regs : bvmap 5 word) (mem : word -> option byte),
  valid_sp sp0 -> valid_input inp ->
  entry_stack_fits sp0 (in_argv inp) (in_envp inp) ->
  (0 < bv_unsigned tid < 2^22)%Z ->
  entry_launch_ok_va Sv48 (mkEntry sp0 brk mbase rnd) inp ->
  PS.p_main_entry sp0 inp mbase rnd tid regs mem ->
  alloc_ceiling = bv_unsigned sp0 - stack_max_size ->
  ssp_guard_val = SSP.canary_w (ed_random rnd) ->
  malloc_secret_val = rnd_secret (ed_random rnd) ->
  (length (in_argv inp) <> 2)%nat ->
  rzb psegs
    (mkCfg (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.MState.MS (RE.mkR_of regs) bvmap_empty (Z_to_bv 64 0x1214c)
              (Z_to_bv 32 0) None mem (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.PropExec.seg_rom psegs))
           (with_tid tid (with_vdso (Vdso.vdso_run_init (ed_vdso rnd)) (init_model (segments_reserved psegs) brk mbase sp0 lim inp))))
    (t_die (msg_usage (nth 0 (in_argv inp) [])) (in_fs inp)).
Proof.
  intros lim sp0 brk mbase rnd inp tid regs mem VSP VINP FITS TID LAU ME CEQ GEQ SEQ HLEN.
  pose proof (valid_input_launch _ VINP) as VL.
  pose proof VINP as (VA & VE & VFS & _).
  pose proof VSP as (LO & HI & AL). unfold sp_window_lo in LO. unfold sp_window_hi in HI.
  assert (HCEIL : alloc_ceiling <= bv_unsigned sp0 - 8388608) by (rewrite CEQ; unfold stack_max_size; lia).
  unfold RE.mkR_of.
  rewrite (PS.me_ra _ _ _ _ _ _ _ ME), (PS.me_tp _ _ _ _ _ _ _ ME), (PS.me_a0 _ _ _ _ _ _ _ ME), (PS.me_a1 _ _ _ _ _ _ _ ME).
  lazymatch goal with |- context [mkR _ ?x2 _ _ _ _ _ _ _ _ _ _] => set (sp := x2) end.
  assert (USP : bv_unsigned sp = bv_unsigned sp0 - 48).
  { subst sp. rewrite (PS.me_sp _ _ _ _ _ _ _ ME). apply unsigned_lit. lia. }
  replace (Z_to_bv 64 (bv_unsigned sp0 + 8)) with (wz (bv_unsigned sp + 56)) by (unfold wz; f_equal; lia).
  pose proof (entry_stk sp0 inp mbase brk tid rnd regs mem ME VA VE VSP VL LAU HCEIL SEQ) as ST.
  replace (bv_unsigned sp0 - 48) with (bv_unsigned sp) in ST by lia.
  pose proof (entry_mem_inv sp0 inp mbase brk tid rnd regs mem ME VA VE VSP VL LAU HCEIL SEQ) as MI.
  pose proof (entry_dstat sp0 inp mbase brk tid rnd regs mem ME VA VE VSP VL LAU HCEIL SEQ) as DS.
  pose proof (entry_libc sp0 inp mbase brk tid rnd regs mem ME VA VE VSP VL LAU HCEIL SEQ) as LC.
  pose proof (entry_ssp sp0 inp mbase brk tid rnd regs mem ME VA VE VSP VL LAU HCEIL SEQ) as SSP0. rewrite <- GEQ in SSP0.
  pose proof (entry_stdout sp0 inp mbase brk tid rnd regs mem ME VA VE VSP VL LAU HCEIL SEQ) as SOF.
  pose proof (entry_stderr sp0 inp mbase brk tid rnd regs mem ME VA VE VSP VL LAU HCEIL SEQ) as SEF.
  pose proof (entry_argv_str sp0 inp mbase brk tid rnd regs mem ME VA VE VSP VL LAU HCEIL SEQ) as EAS.
  pose proof (entry_argv_ptr sp0 inp mbase brk tid rnd regs mem ME VA VE VSP VL LAU HCEIL SEQ) as EAP.
  pose proof (mo0_dmod inp tid brk mbase sp0 lim rnd (valid_input_channel_reader _ VINP)) as DM.
  destruct (in_argv inp) as [|argv0 [|path [|x rest]]] eqn:EAV.
  - exfalso. destruct VA as [[H _] _]. cbn in H. lia.
  - destruct (EAS 0%nat ltac:(cbn; lia)) as (slack & BY & SLK & AB & _ & NONUL & LEN).
    pose proof (EAP 0%nat ltac:(cbn; lia)) as AV.
    cbn [nth] in BY, SLK, NONUL, LEN |- *. cbn [hd].
    set (P0w := CE.cat_argv_ptr (ed_top rnd) [argv0] (in_envp inp) (in_execfn inp) 0) in *.
    replace (bv_unsigned sp0 + 8 + 8 * Z.of_nat 0) with (bv_unsigned sp + 56) in AV by lia.
    rewrite <- (Z_to_bv_bv_unsigned P0w) in AV. change (Z_to_bv 64 (bv_unsigned P0w)) with (wz (bv_unsigned P0w)) in AV.
    eapply (main_usage_b so_exit_proof_b so_diag_usage_proof_b) with (lo := bv_unsigned sp0 - 6144512) (argc := 1) (P0 := bv_unsigned P0w) (argv0 := argv0) (slack := slack);
      first [exact DM| exact ST| exact MI| exact DS| exact TID| exact LC| exact SSP0| exact SOF| exact SEF| exact NONUL| exact AV| exact BY| exact SLK| apply frm0_zero
            | reflexivity | unfold PStartupDefs.ArgvEnv.argcN; rewrite EAV; reflexivity | unfold GLOBALS_TOP, zlength in *; lia].
  - exfalso. apply HLEN. reflexivity.
  - destruct (EAS 0%nat ltac:(cbn; lia)) as (slack & BY & SLK & AB & _ & NONUL & LEN).
    pose proof (EAP 0%nat ltac:(cbn; lia)) as AV.
    cbn [nth] in BY, SLK, NONUL, LEN |- *. cbn [hd].
    set (P0w := CE.cat_argv_ptr (ed_top rnd) (argv0 :: path :: x :: rest) (in_envp inp) (in_execfn inp) 0) in *.
    replace (bv_unsigned sp0 + 8 + 8 * Z.of_nat 0) with (bv_unsigned sp + 56) in AV by lia.
    rewrite <- (Z_to_bv_bv_unsigned P0w) in AV. change (Z_to_bv 64 (bv_unsigned P0w)) with (wz (bv_unsigned P0w)) in AV.
    destruct VA as [[_ AC] _].
    eapply (main_usage_b so_exit_proof_b so_diag_usage_proof_b) with (lo := bv_unsigned sp0 - 6144512) (argc := Z.of_nat (length (argv0 :: path :: x :: rest))) (P0 := bv_unsigned P0w) (argv0 := argv0) (slack := slack);
      first [exact DM| exact ST| exact MI| exact DS| exact TID| exact LC| exact SSP0| exact SOF| exact SEF| exact NONUL| exact AV| exact BY| exact SLK| apply frm0_zero
            | reflexivity | unfold PStartupDefs.ArgvEnv.argcN; rewrite EAV; reflexivity | unfold GLOBALS_TOP, zlength in *; cbn [length] in *; lia ].
Qed.

End CeilWrap.

(** Start-up ([PStartupRTB.p_startup_rt_b]), then [main]'s usage path
    ([p_main_usage_b]), at the [Ceil] and [Guard] instances
    [P.DrvTop.p_main_proof_lim] builds; at every limit. *)
Lemma usage_rzb : forall sp brk mbase rnd lim inp,
  valid_sp sp -> valid_brk psegs brk -> valid_input inp ->
  entry_stack_fits sp (in_argv inp) (in_envp inp) ->
  entry_launch_ok_va Sv48 (mkEntry sp brk mbase rnd) inp ->
  (length (in_argv inp) <> 2)%nat ->
  rzb psegs (init_config psegs ppc pph sp brk mbase rnd lim inp)
      (t_die (msg_usage (nth 0 (in_argv inp) [])) (in_fs inp)).
Proof.
  intros sp0 brk mbase rnd lim inp VSP Hbrk VINP FITS LAU HLEN.
  pose proof VINP as (Hargv & Henvp & _).
  apply (p_startup_rt_b sp0 brk mbase rnd lim inp _ VSP Hbrk Hargv Henvp (valid_input_launch _ VINP) LAU).
  intros tid regs mem TID ME.
  assert (E : (0x1214c%bv : word) = Z_to_bv 64 0x1214c) by (apply bv_eq; reflexivity).
  rewrite E.
  pose proof VSP as (V1 & V2 & V3). unfold sp_window_lo, sp_window_hi in V1, V2.
  assert (H1 : 0x7fff7f800000 <= bv_unsigned sp0 - stack_max_size) by (unfold stack_max_size; lia).
  assert (H2 : bv_unsigned sp0 - stack_max_size <= 0x7fffff800000) by (unfold stack_max_size; lia).
  assert (H3 : (bv_unsigned sp0 - stack_max_size) mod 16 = 0).
  { unfold stack_max_size. rewrite Zminus_mod, V3. reflexivity. }
  exact (@p_main_usage_b (ceil_of_val _ H1 H2 H3) (guard_of (SSP.canary_w (ed_random rnd)) (rnd_secret (ed_random rnd)))
           lim sp0 brk mbase rnd inp tid regs mem VSP VINP FITS TID LAU ME eq_refl eq_refl eq_refl HLEN).
Qed.

(** On every valid entry of the plain build and every valid input whose argv
    has not two entries, no configuration of the run is refused by the
    budget, whatever the spurious-failure configuration and whatever the
    limit. *)
Theorem usage_never_refused : forall en inp,
  valid_entry OSSVerify.cjson.cjson_read_fuzzer.Images.plain en inp -> valid_input inp ->
  (length (in_argv inp) <> 2)%nat ->
  forall (cfg : SpuriousCfg) (lim : Z),
  ~ run_scfg_budget_refused cfg OSSVerify.cjson.cjson_read_fuzzer.Images.plain lim en inp.
Proof.
  intros [sp brk mbase rnd] inp Hen Hinp Hlen cfg lim.
  pose proof (valid_input_va_size _ Hinp) as Hv.
  rewrite (valid_entry_sv48 _ _ _ Hv) in Hen.
  destruct Hen as (Hsp & Hbrk & _ & Hfit & Hlau).
  (* the run reads the binary against run_segments; the walk over the binary's own segments lifts to it *)
  exact (rzb_never_refused_cfg (run_segments psegs inp sp mbase) cfg _ _
           (rzb_run_init psegs inp sp mbase ppc pph brk rnd lim _ eq_refl
              (usage_rzb sp brk mbase rnd lim inp Hsp Hbrk Hinp Hfit Hlau Hlen))).
Qed.

(** An entry of the plain build at [Premises.witness_input false], the entry
    [Premises.valid_input_entry] gives for it, at which the budget refuses
    nothing, whatever the configuration and the limit. *)
Lemma plain_witness_entry : exists en,
  valid_entry OSSVerify.cjson.cjson_read_fuzzer.Images.plain en (Premises.witness_input false) /\
  forall (cfg : SpuriousCfg) (lim : Z),
  ~ run_scfg_budget_refused cfg OSSVerify.cjson.cjson_read_fuzzer.Images.plain lim en (Premises.witness_input false).
Proof.
  destruct (Premises.valid_input_entry OSSVerify.cjson.cjson_read_fuzzer.Images.plain (Premises.witness_input false)
    OSSVerify.cjson.cjson_read_fuzzer.Images.plain_wf Premises.witness_valid_input) as [en Hen].
  exists en. split; [exact Hen |].
  apply (usage_never_refused en _ Hen Premises.witness_valid_input).
  cbn. discriminate.
Qed.

(** The budget premise of the plain build, with the other premises of the
    agreement statements at the same input: an entry of the plain build and
    one of the sanitizer build on [Premises.witness_input false] (the pair
    [Premises.agrees_in_premises] builds, constructed here so that the input
    stays the witness input). *)
Lemma agree_witness : forall san, OSSVerify.Core.Images.image_wf san ->
  exists en_plain en_san,
  valid_entry OSSVerify.cjson.cjson_read_fuzzer.Images.plain en_plain (Premises.witness_input false) /\
  valid_entry san en_san (Premises.witness_input false) /\
  forall (cfg : SpuriousCfg) (lim : Z),
  ~ run_scfg_budget_refused cfg OSSVerify.cjson.cjson_read_fuzzer.Images.plain lim en_plain (Premises.witness_input false).
Proof.
  intros san Hwf.
  destruct plain_witness_entry as (en_plain & Hep & Hnr).
  destruct (Premises.valid_input_entry san (Premises.witness_input false) Hwf Premises.witness_valid_input)
    as [en_san Hes].
  exists en_plain, en_san. exact (conj Hep (conj Hes Hnr)).
Qed.

(** [plain_budget_witness]: the budget premise of the plain build at the
    configuration and limit of [Statements.asan_agrees] and
    [Statements.asan_ubsan_agrees], with the entry and input premises. *)
Theorem plain_budget_witness :
  exists en inp, valid_entry OSSVerify.cjson.cjson_read_fuzzer.Images.plain en inp /\ valid_input inp /\
  ~ run_scfg_budget_refused Env.alloc_forced_only OSSVerify.cjson.cjson_read_fuzzer.Images.plain
      Budgets.Asan.lim_source en inp.
Proof.
  destruct plain_witness_entry as (en & Hen & Hnr).
  exists en, (Premises.witness_input false).
  split; [exact Hen | split; [exact Premises.witness_valid_input | apply Hnr]].
Qed.

(** [Statements.asan_agrees], which the released
    [Theorems.strong_universal_error_free_cjson_read_fuzzer_asan] proves, at
    entries and an input that meet all four of its premises: its conclusion
    holds there with no hypothesis left. *)
Theorem asan_agrees_not_vacuous :
  exists en_plain en_san inp,
  valid_entry OSSVerify.cjson.cjson_read_fuzzer.Images.plain en_plain inp /\
  valid_entry OSSVerify.cjson.cjson_read_fuzzer.Images.asan en_san inp /\
  valid_input inp /\
  ~ run_scfg_budget_refused Env.alloc_forced_only OSSVerify.cjson.cjson_read_fuzzer.Images.plain
      Budgets.Asan.lim_source en_plain inp /\
  error_free (run_scfg Env.alloc_forced_only OSSVerify.cjson.cjson_read_fuzzer.Images.plain
      Budgets.Asan.lim_source en_plain inp)
  /\ error_free (run_scfg Env.alloc_forced_only OSSVerify.cjson.cjson_read_fuzzer.Images.asan
      Budgets.Asan.lim_target en_san inp)
  /\ trace_equiv (bh_traces (run_scfg Env.alloc_forced_only OSSVerify.cjson.cjson_read_fuzzer.Images.plain
                     Budgets.Asan.lim_source en_plain inp))
                 (bh_traces (run_scfg Env.alloc_forced_only OSSVerify.cjson.cjson_read_fuzzer.Images.asan
                     Budgets.Asan.lim_target en_san inp)).
Proof.
  destruct (agree_witness OSSVerify.cjson.cjson_read_fuzzer.Images.asan OSSVerify.cjson.cjson_read_fuzzer.Images.asan_wf)
    as (ep & es & Hep & Hes & Hnr).
  exists ep, es, (Premises.witness_input false).
  split; [exact Hep | split; [exact Hes | split; [exact Premises.witness_valid_input | split; [apply Hnr |]]]].
  exact (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Theorems.strong_universal_error_free_cjson_read_fuzzer_asan
    ep es (Premises.witness_input false) Hep Hes Premises.witness_valid_input (Hnr _ _)).
Qed.

(** [Statements.ubsan_agrees], which the released
    [Theorems.strong_universal_error_free_cjson_read_fuzzer_ubsan] proves, at
    entries and an input that meet all four of its premises: its conclusion
    holds there with no hypothesis left. *)
Theorem ubsan_agrees_not_vacuous :
  exists en_plain en_san inp,
  valid_entry OSSVerify.cjson.cjson_read_fuzzer.Images.plain en_plain inp /\
  valid_entry OSSVerify.cjson.cjson_read_fuzzer.Images.ubsan en_san inp /\
  valid_input inp /\
  ~ run_scfg_budget_refused Env.alloc_forced_only OSSVerify.cjson.cjson_read_fuzzer.Images.plain
      Budgets.Standard.lim_source en_plain inp /\
  error_free (run_scfg Env.alloc_forced_only OSSVerify.cjson.cjson_read_fuzzer.Images.plain
      Budgets.Standard.lim_source en_plain inp)
  /\ error_free (run_scfg Env.alloc_forced_only OSSVerify.cjson.cjson_read_fuzzer.Images.ubsan
      Budgets.Standard.lim_target en_san inp)
  /\ trace_equiv (bh_traces (run_scfg Env.alloc_forced_only OSSVerify.cjson.cjson_read_fuzzer.Images.plain
                     Budgets.Standard.lim_source en_plain inp))
                 (bh_traces (run_scfg Env.alloc_forced_only OSSVerify.cjson.cjson_read_fuzzer.Images.ubsan
                     Budgets.Standard.lim_target en_san inp)).
Proof.
  destruct (agree_witness OSSVerify.cjson.cjson_read_fuzzer.Images.ubsan OSSVerify.cjson.cjson_read_fuzzer.Images.ubsan_wf)
    as (ep & es & Hep & Hes & Hnr).
  exists ep, es, (Premises.witness_input false).
  split; [exact Hep | split; [exact Hes | split; [exact Premises.witness_valid_input | split; [apply Hnr |]]]].
  exact (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Theorems.strong_universal_error_free_cjson_read_fuzzer_ubsan
    ep es (Premises.witness_input false) Hep Hes Premises.witness_valid_input (Hnr _ _)).
Qed.

(** [Statements.asan_ubsan_agrees], which the released
    [Theorems.strong_universal_error_free_cjson_read_fuzzer_both] proves, at
    entries and an input that meet all four of its premises: its conclusion
    holds there with no hypothesis left. *)
Theorem asan_ubsan_agrees_not_vacuous :
  exists en_plain en_san inp,
  valid_entry OSSVerify.cjson.cjson_read_fuzzer.Images.plain en_plain inp /\
  valid_entry OSSVerify.cjson.cjson_read_fuzzer.Images.asan_ubsan en_san inp /\
  valid_input inp /\
  ~ run_scfg_budget_refused Env.alloc_forced_only OSSVerify.cjson.cjson_read_fuzzer.Images.plain
      Budgets.Asan.lim_source en_plain inp /\
  error_free (run_scfg Env.alloc_forced_only OSSVerify.cjson.cjson_read_fuzzer.Images.plain
      Budgets.Asan.lim_source en_plain inp)
  /\ error_free (run_scfg Env.alloc_forced_only OSSVerify.cjson.cjson_read_fuzzer.Images.asan_ubsan
      Budgets.Asan.lim_target en_san inp)
  /\ trace_equiv (bh_traces (run_scfg Env.alloc_forced_only OSSVerify.cjson.cjson_read_fuzzer.Images.plain
                     Budgets.Asan.lim_source en_plain inp))
                 (bh_traces (run_scfg Env.alloc_forced_only OSSVerify.cjson.cjson_read_fuzzer.Images.asan_ubsan
                     Budgets.Asan.lim_target en_san inp)).
Proof.
  destruct (agree_witness OSSVerify.cjson.cjson_read_fuzzer.Images.asan_ubsan
    OSSVerify.cjson.cjson_read_fuzzer.Images.asan_ubsan_wf) as (ep & es & Hep & Hes & Hnr).
  exists ep, es, (Premises.witness_input false).
  split; [exact Hep | split; [exact Hes | split; [exact Premises.witness_valid_input | split; [apply Hnr |]]]].
  exact (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Theorems.strong_universal_error_free_cjson_read_fuzzer_both
    ep es (Premises.witness_input false) Hep Hes Premises.witness_valid_input (Hnr _ _)).
Qed.
