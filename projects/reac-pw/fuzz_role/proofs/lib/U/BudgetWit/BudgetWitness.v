(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Rares Buhai, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YL0j.v, with its module paths changed. *)
(* Modified by Theorem Labs, 2026-11: made from the argc <> 2 branch of Reusable/YL0j.v's src0_realizes_specX, over BudgetWit.Rzb.rzb; adds the budget-premise witness for the plain build and the lemma that applies the plain_halts proof there. *)
(* Modified by Theorem Labs, 2026-11: the UBSan build's copy of lib/BudgetWit/BudgetWitness.v, over lib/U/Reusable: the witness for the UBSan build and the lemma that applies the ubsan_halts proof there. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (the launch's ProcInput and its entry-launch facts, given to the start-up and usage walks; the channel-reader conjunct of fdchan; the walk lifted to the run over run_segments), in reac-pw/fuzz_qdisc's form. *)
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.U.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence MustExit.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Core Require Import Shapes.
From OSSVerify.Core Require Premises.
From OSSVerify.reac_pw.fuzz_role Require Images Statements.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.U.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK0n YP0n.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.U.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP08 YP03 YP0f YP04 YN3v.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.U.Reusable Require Import YO05 YH00 YH01 YH03 YN3e YL0y.
From OSSVerify.reac_pw.fuzz_role.images Require Import Ubsan.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.U.Reusable.R Require Import Cfg.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib Require Theorems.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.U.BudgetWit Require Import Rzb StartB UsageB.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require RomStableK.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
#[local] Existing Instance YK11.fx0.
Open Scope bv_scope.
Open Scope Z_scope.

(** * reac-pw / fuzz_role: the UBSan build meets [ubsan_halts]'s three premises together

    [Statements.ubsan_halts] quantifies over every entry [en] and input [inp] and
    has three premises: [valid_entry Images.ubsan en inp], [valid_input inp] and the
    budget premise [~ run_scfg_budget_refused forced_only_cfg Images.ubsan
    Budgets.Standard.lim_source en inp].  A theorem whose premises never hold
    together proves nothing.  [OSSVerify.Core.Premises] gives the first two for every
    well-formed image and leaves the third, which reads the run; this file gives the
    third for this build.

    This file is lib/BudgetWit/BudgetWitness.v (the plain build's witness) with the
    UBSan build's modules under lib/U/Reusable in place of the plain build's, and
    the UBSan image and statement in place of the plain ones.  The argument is the
    same.  The input is [Premises.witness_input false]: one empty argument (so
    argc = 1), no environment, an empty file system.  With argc <> 2 the driver's
    [main] writes its usage line to fd 2 and exits with status 2.  On that path the
    program makes three kinds of system call: set_tid_address (96) in musl's
    start-up, writev (66) for the line, exit or exit_group (93, 94).  None is an
    allocation call (brk 214, mremap 216, mmap 222, mprotect 226), and no mapping is
    lazy ([m_vm_lazy = []] throughout), so no configuration the run reaches is
    refused by the budget.

    The proof is the released proof of that path in the UBSan build
    ([U.Reusable.YN3e.src0_start], the argc <> 2 branch of
    [U.Reusable.YL0j.src0_realizes_specX], [U.Reusable.YL0y.src0_usage]) restated
    over [BudgetWit.Rzb.rzb], the released [YK15.realizes] with no cut and a grant
    check at each node ([BudgetWit.Rzb] says why [realizes] itself cannot carry the
    fact; [rzb] reads no address of the image, so this build uses the plain build's
    [Rzb] module).  [usage_rzb] is that walk at [MayFail];
    [Rzb.rzb_never_refused_cfg] turns it into the budget premise, for every
    spurious-failure configuration and every limit ([ubsan_never_refused]).
    [ubsan_budget_witness] is the three premises at one entry and one input;
    [ubsan_halts_not_vacuous] gives them to the released proof
    [Theorems.reac_pw_fuzz_role_ubsan_halts] (the term that
    [ubsan_halts/Proof.v]'s [ubsan_halts_holds] is), so the statement's conclusion
    holds at a pair that meets all its premises, with no hypothesis left. *)

(** The argc <> 2 branch of [YL0j.src0_realizes_specX], over [rzb] at [MayFail]:
    start-up ([StartB.src0_start_b]), then [main]'s usage path
    ([UsageB.src0_usage_b]). *)
Lemma usage_rzb : forall sp brk mbase rnd lim inp,
valid_sp sp -> valid_argv (in_argv inp) -> valid_envp (in_envp inp) ->
entry_stack_fits sp (in_argv inp) (in_envp inp) ->
valid_launch inp -> entry_launch_ok_va Sv48 (mkEntry sp brk mbase rnd) inp ->
in_channel_reader inp = true ->
(length (in_argv inp) <> 2)%nat ->
@rzb src0segs MayFail (init_config src0segs Ubsan_init_pc Ubsan_phdrs sp brk mbase rnd lim inp)
(diag (msg_usage (nth 0 (in_argv inp) [])) (in_fs inp)).
Proof.
intros sp brk mbase rnd lim inp Hsp Hva Hve Hfits Hvl Hlau Hcr Hlen.
apply (@src0_start_b MayFail false sp brk mbase rnd lim inp _ Hsp Hva Hve Hfits Hvl Hlau I).
intros ms tid Htid HS HR.
lazymatch goal with |- rzb _ (mkCfg _ ?m) _ => set (md0 := m) end.
assert (Hh : m_halted md0 = None) by reflexivity.
assert (Hlz : m_vm_lazy md0 = []) by reflexivity.
change (in_fs inp) with (m_fs md0).
(* 727298f3: [src0_usage_b] is stated over the launch's ProcInput and holds at every run
   ceiling; take the run's own (as libdiginet/fuzz_decode's BudgetWitness.v). *)
apply (src0_usage_b (fx:=YK11.fx0)
  (rc:=YM05.RunCeilOf (bv_unsigned sp) ltac:(destruct Hsp as [Hlo [Hhi _]]; split; assumption) lim)
  (AM:=MayFail) sp inp mbase brk tid rnd Hsp Hva Hve Hvl Hlau Hfits Hlen ms _).
- apply st_ok_add_cond; [exact HS |].
assert (H3 : bv_unsigned (ew (E_main sp inp tid rnd) 3) = Z.of_nat (length (in_argv inp)))
by (unfold E_main; exact (YP08.ew3 src0segs Ubsan_phdrs inp mbase Ubsan_init_pc sp brk rnd Hsp Hva Hve Hvl Hlau 1 ltac:(lia) (xw_main inp rnd tid) (xd_main rnd))).
unfold branch_taken. cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned.
apply Bool.negb_true_iff. apply bv_eqb_neq. intros Heq.
apply (f_equal bv_unsigned) in Heq. rewrite H3 in Heq. change (bv_unsigned (Z_to_bv 64 2)) with 2 in Heq. lia.
- exact HR.
- exact Hh.
- exact Hlz.
- (* 727298f3: [fdchan]'s third conjunct is the launch's reader fact. *)
  split; [reflexivity | split; [reflexivity |]].
  first [ (unfold md0, init_model; autorewrite with model; exact Hcr) | (unfold md0; cbn; exact Hcr) ].
Qed.

(** On every valid entry of the UBSan build and every valid input whose argv has
    not two entries, no configuration of the run is refused by the budget, whatever
    the spurious-failure configuration and whatever the limit. *)
Theorem ubsan_never_refused : forall en inp,
valid_entry OSSVerify.reac_pw.fuzz_role.Images.ubsan en inp -> valid_input inp ->
(length (in_argv inp) <> 2)%nat ->
forall (cfg : SpuriousCfg) (lim : Z),
~ run_scfg_budget_refused cfg OSSVerify.reac_pw.fuzz_role.Images.ubsan lim en inp.
Proof.
intros [sp brk mbase rnd] inp Hen Hinp Hlen cfg lim.
pose proof (valid_input_va_size _ Hinp) as Hv.
apply (valid_entry_sv48 _ _ _ Hv) in Hen.
destruct Hen as (Hsp & _ & _ & Hfits & Hlau).
pose proof (valid_input_argv inp Hinp) as Hva. pose proof (valid_input_envp inp Hinp) as Hve.
pose proof (valid_input_launch inp Hinp) as Hvl. pose proof (valid_input_channel_reader inp Hinp) as Hcr.
(* 727298f3: [Run.run_scfg_budget_refused] reads the run against [run_segments] (the binary's
   segments with the run's vDSO appended); [Rzb.rzb_run_init] lifts the walk over the binary's own
   segments, which carry no vDSO text. *)
exact (rzb_never_refused_cfg _ cfg _ _
  (@rzb_run_init MayFail src0segs inp sp mbase Ubsan_init_pc Ubsan_phdrs brk rnd lim _ ltac:(RomStableK.vdso_none)
     (usage_rzb sp brk mbase rnd lim inp Hsp Hva Hve Hfits Hvl Hlau Hcr Hlen))).
Qed.

(** [ubsan_halts]'s three premises hold together: at [Premises.witness_input false]
    and the entry [Premises.valid_input_entry] gives for it. *)
Theorem ubsan_budget_witness :
exists en inp, valid_entry OSSVerify.reac_pw.fuzz_role.Images.ubsan en inp /\ valid_input inp /\
~ run_scfg_budget_refused forced_only_cfg OSSVerify.reac_pw.fuzz_role.Images.ubsan
    Budgets.Standard.lim_source en inp.
Proof.
destruct (Premises.valid_input_entry OSSVerify.reac_pw.fuzz_role.Images.ubsan (Premises.witness_input false)
  OSSVerify.reac_pw.fuzz_role.Images.ubsan_wf Premises.witness_valid_input) as [en Hen].
exists en, (Premises.witness_input false).
split; [exact Hen | split; [exact Premises.witness_valid_input |]].
apply (ubsan_never_refused en _ Hen Premises.witness_valid_input).
cbn. discriminate.
Qed.

(** [Statements.ubsan_halts], which the released [Theorems.reac_pw_fuzz_role_ubsan_halts]
    proves, at an entry and an input that meet all three of its premises: its
    conclusion holds there with no hypothesis left. *)
Theorem ubsan_halts_not_vacuous :
exists en inp, valid_entry OSSVerify.reac_pw.fuzz_role.Images.ubsan en inp /\ valid_input inp /\
~ run_scfg_budget_refused forced_only_cfg OSSVerify.reac_pw.fuzz_role.Images.ubsan
    Budgets.Standard.lim_source en inp /\
must_exit_in_scfg forced_only_cfg Exits.ok_or_refused OSSVerify.reac_pw.fuzz_role.Images.ubsan
    Budgets.Standard.lim_source en inp.
Proof.
destruct ubsan_budget_witness as (en & inp & Hen & Hinp & Hnr).
exists en, inp. split; [exact Hen | split; [exact Hinp | split; [exact Hnr |]]].
exact (OSSVerify.Proofs.reac_pw.fuzz_role.lib.Theorems.reac_pw_fuzz_role_ubsan_halts en inp Hen Hinp Hnr).
Qed.
