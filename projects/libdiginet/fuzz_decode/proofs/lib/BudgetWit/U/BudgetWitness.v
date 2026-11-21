(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Rares Buhai, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YL0j.v, with its module paths changed. *)
(* Modified by Theorem Labs, 2026-10: ported from libreac/fuzz_decode proofs/libreac/fuzz_decode/lib/U/Reusable/YL0j.v for libdiginet/fuzz_decode; no image value changed; module path OSSVerify.Proofs.libdiginet.fuzz_decode.lib. *)
(* Modified by Theorem Labs, 2026-11: made from the argc <> 2 branch of U/Reusable/YL0j.v's src0_realizes_specX, over BudgetWit.Rzb.rzb; adds the budget-premise witness for the UBSan build and the lemma that applies the released proof of ubsan_halts there. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (usage_rzb over the ProcInput launch (the launch premises proved at usage_never_refused from valid_entry and valid_input) and the vDSO-wrapped start model; the walk lifted to the run's segments by Rzb.rzb_run_init); internal commit ids in comments replaced by public commits or removed. *)
From OSSVerify.Proofs.libdiginet.fuzz_decode.lib.U.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence MustExit.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Core Require Import Shapes.
From OSSVerify.Core Require Premises.
From OSSVerify.libdiginet.fuzz_decode Require Images Statements.
From OSSVerify.Proofs.libdiginet.fuzz_decode.lib.U.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK0n YP0n.
From OSSVerify.Proofs.libdiginet.fuzz_decode.lib.U.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP08 YP03 YP0f YP04 YN3v.
From OSSVerify.Proofs.libdiginet.fuzz_decode.lib.U.Reusable Require Import YO05 YH00 YH01 YH03 YN3e YL0y.
From OSSVerify.libdiginet.fuzz_decode.images Require Import Ubsan.
From OSSVerify.Proofs.libdiginet.fuzz_decode.lib.U.Reusable.R Require Import Cfg.
From OSSVerify.Proofs.libdiginet.fuzz_decode.lib Require Theorems.
From OSSVerify.Proofs.libdiginet.fuzz_decode.lib.BudgetWit Require Import Rzb.
From OSSVerify.Proofs.libdiginet.fuzz_decode.lib.Reusable Require RomStableK.
From OSSVerify.Proofs.libdiginet.fuzz_decode.lib.BudgetWit.U Require Import StartB UsageB.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
#[local] Existing Instance YK11.fx0.
Open Scope bv_scope.
Open Scope Z_scope.

(** * libdiginet / fuzz_decode: the budget premise on the UBSan build holds together with the other premises

    One statement of [Statements] carries a budget premise on the UBSan build:
    [ubsan_halts] ([halts_within_budget]), at [forced_only_cfg] and
    [Budgets.Standard.lim_source].  (The agreement statements carry theirs on the
    plain build; [BudgetWit.BudgetWitness] ties those off.)  This file gives that
    premise for this build, for every configuration and every limit, and applies
    the released proof of [ubsan_halts] at a point that meets all its premises.

    The input is [Premises.witness_input false]: one empty argument (so argc = 1),
    no environment, an empty file system.  With argc <> 2 the driver's [main] writes
    its usage line to fd 2 and exits with status 2.  The UBSan build's start-up and
    usage path are the plain build's at other addresses ([U/Reusable] is the plain
    [Reusable] with its addresses changed, and the image-independent modules are the
    plain ones): set_tid_address (96), writev (66), exit or exit_group (93, 94), no
    allocation call and no lazy mapping, so no configuration the run reaches is
    refused by the budget.  This shows the budget premise satisfiable on the usage
    path, not yet on an input that reaches [LLVMFuzzerTestOneInput].

    The proof is [BudgetWit.BudgetWitness]'s at the UBSan build's walk:
    [BudgetWit.U.StartB], [BudgetWit.U.UsageB] and the files they import are the
    plain build's BudgetWit walk files made from [U/Reusable] instead of [Reusable];
    [BudgetWit.Rzb] is shared, since [rzb] and its soundness are stated for every
    segment list. *)

(** The argc <> 2 branch of [U/Reusable/YL0j.src0_realizes_specX], over [rzb]. *)
Lemma usage_rzb : forall sp brk mbase rnd lim inp,
valid_sp sp -> valid_argv (in_argv inp) -> valid_envp (in_envp inp) ->
entry_stack_fits sp (in_argv inp) (in_envp inp) ->
valid_launch inp -> entry_launch_ok_va Sv48 (mkEntry sp brk mbase rnd) inp ->
in_channel_reader inp = true ->
(length (in_argv inp) <> 2)%nat ->
rzb src0segs (init_config src0segs Ubsan_init_pc Ubsan_phdrs sp brk mbase rnd lim inp)
(diag (msg_usage (nth 0 (in_argv inp) [])) (in_fs inp)).
Proof.
intros sp brk mbase rnd lim inp Hsp Hva Hve Hfits Hvl Hlau Hcr Hlen.
apply (src0_start_b false sp brk mbase rnd lim inp _ Hsp Hva Hve Hfits Hvl Hlau I).
intros ms tid Htid HS HR.
lazymatch goal with |- rzb _ (mkCfg _ ?m) _ => set (md0 := m) end.
assert (Hh : m_halted md0 = None) by reflexivity.
assert (Hlz : m_vm_lazy md0 = []) by reflexivity.
change (in_fs inp) with (m_fs md0).
(* [src0_usage_b] holds at every run ceiling; take the run's own. *)
apply (src0_usage_b (rc:=YM05.RunCeilOf (bv_unsigned sp) ltac:(destruct Hsp as [Hlo [Hhi _]]; split; assumption) lim)
  sp inp mbase brk tid rnd Hsp Hva Hve Hvl Hlau Hfits Hlen ms _).
+ apply st_ok_add_cond; [exact HS |].
pose proof (ew3 src0segs Ubsan_phdrs inp mbase Ubsan_init_pc sp brk rnd Hsp Hva Hve Hvl Hlau 1 ltac:(lia) (xw_main inp rnd tid) (xd_main rnd)) as H3.
change (E0 _ _ _ _ _ _ _ _) with (E_main sp inp tid rnd) in H3.
unfold branch_taken. cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned.
apply Bool.negb_true_iff. apply bv_eqb_neq. intros Heq.
apply (f_equal bv_unsigned) in Heq. rewrite H3 in Heq. change (bv_unsigned (Z_to_bv 64 2)) with 2 in Heq. lia.
+ exact HR.
+ exact Hh.
+ exact Hlz.
+ (* 727298f3: [fdchan]'s third conjunct is the launch's reader fact. *)
  split; [reflexivity | split; [reflexivity |]].
  first [ (unfold md0, init_model; autorewrite with model; exact Hcr) | (unfold md0; cbn; exact Hcr) ].
Qed.

(** On every valid entry of the UBSan build and every valid input whose argv has
    not two entries, no configuration of the run is refused by the budget, whatever
    the spurious-failure configuration and whatever the limit. *)
Theorem usage_never_refused : forall en inp,
valid_entry OSSVerify.libdiginet.fuzz_decode.Images.ubsan en inp -> valid_input inp ->
(length (in_argv inp) <> 2)%nat ->
forall (cfg : SpuriousCfg) (lim : Z),
~ run_scfg_budget_refused cfg OSSVerify.libdiginet.fuzz_decode.Images.ubsan lim en inp.
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
  (rzb_run_init src0segs inp sp mbase Ubsan_init_pc Ubsan_phdrs brk rnd lim _ ltac:(RomStableK.vdso_none)
     (usage_rzb sp brk mbase rnd lim inp Hsp Hva Hve Hfits Hvl Hlau Hcr Hlen))).
Qed.

(** [ubsan_halts]'s three premises hold together: at [Premises.witness_input false]
    and the entry [Premises.valid_input_entry] gives for it. *)
Theorem ubsan_budget_witness :
exists en inp, valid_entry OSSVerify.libdiginet.fuzz_decode.Images.ubsan en inp /\ valid_input inp /\
~ run_scfg_budget_refused forced_only_cfg OSSVerify.libdiginet.fuzz_decode.Images.ubsan
    Budgets.Standard.lim_source en inp.
Proof.
destruct (Premises.valid_input_entry OSSVerify.libdiginet.fuzz_decode.Images.ubsan (Premises.witness_input false)
  OSSVerify.libdiginet.fuzz_decode.Images.ubsan_wf Premises.witness_valid_input) as [en Hen].
exists en, (Premises.witness_input false).
split; [exact Hen | split; [exact Premises.witness_valid_input |]].
apply (usage_never_refused en _ Hen Premises.witness_valid_input).
cbn. discriminate.
Qed.

(** [Statements.ubsan_halts], which the released [Theorems.libdiginet_fuzz_decode_ubsan_halts]
    proves, at an entry and an input that meet all three of its premises: its
    conclusion holds there with no hypothesis left. *)
Theorem ubsan_halts_not_vacuous :
exists en inp, valid_entry OSSVerify.libdiginet.fuzz_decode.Images.ubsan en inp /\ valid_input inp /\
~ run_scfg_budget_refused forced_only_cfg OSSVerify.libdiginet.fuzz_decode.Images.ubsan
    Budgets.Standard.lim_source en inp /\
must_exit_in_scfg forced_only_cfg Exits.ok_or_refused OSSVerify.libdiginet.fuzz_decode.Images.ubsan
    Budgets.Standard.lim_source en inp.
Proof.
destruct ubsan_budget_witness as (en & inp & Hen & Hinp & Hnr).
exists en, inp. split; [exact Hen | split; [exact Hinp | split; [exact Hnr |]]].
exact (OSSVerify.Proofs.libdiginet.fuzz_decode.lib.Theorems.libdiginet_fuzz_decode_ubsan_halts en inp Hen Hinp Hnr).
Qed.
