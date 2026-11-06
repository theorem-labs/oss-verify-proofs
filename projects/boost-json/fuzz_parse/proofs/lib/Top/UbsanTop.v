(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence MustExit HaltsAllowed.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.boost_json.fuzz_parse.images Require Import Ubsan.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import Scfg ShapeAlg ShapeEFA HeapCeil HeapSecret Spec.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.U Require Import MainDefs RefStartupDefs TargetRun RefTop.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require PropExec.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.RefU Require Import HeapMF_iface.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.BJU Require Import BJIface BJIfaceLL.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.EHU Require Import EhX_ubsan EhGlue.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require PropExec.   (* [comment removed for export] *)
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.RefU Require Import RSegs MallocSR MallocMF.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.U Require Import HeapGlue.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Bridge Require Import MustExitIn.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Definition UBSAN : Image :=
  mkImage Ubsan.M.loaded_segments Ubsan.M.init_pc Ubsan.M.phdrs.

Definition exit_codes_02 : list word := [Z_to_bv 64 0; Z_to_bv 64 2].

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma W_no_exit : forall ch s, Forall no_exit_ev (W ch s).
Proof. intros ch s. unfold W. induction s as [|b s IH]; cbn; constructor; [exact I | exact IH]. Qed.

Lemma t_die_exits : forall msg fs, exits_in exit_codes_02 (t_die msg fs).
Proof.
  intros msg fs. unfold t_die. apply exits_in_emit; [apply W_no_exit|].
  apply exits_in_exit. right. left. reflexivity.
Qed.

Lemma t_body_exits : forall data fs, exits_in exit_codes_02 (t_body data fs).
Proof.
  intros data fs. unfold t_body.
  destruct (MAX_INPUT <=? Z.of_nat (length data))%Z; [apply t_die_exits|].
  destruct (length data <? 6)%nat; [apply t_die_exits|].
  cbv zeta.
  destruct (length data <? _)%nat; [apply t_die_exits|].
  apply exits_in_emit; [apply W_no_exit | apply exits_in_exit]. left. reflexivity.
Qed.

Lemma spec_exits : forall argv fs, exits_in exit_codes_02 (spec argv fs).
Proof.
  intros argv fs. unfold spec.
  destruct argv as [|a0 [|path [|x l]]]; try apply t_die_exits.
  destruct (4096 <=? length path)%nat; [apply t_die_exits|].
  destruct (list_byte_eqb path []); [apply t_die_exits|].
  destruct (list_byte_eqb path dot_path).
  - apply exits_in_alt2; [apply t_die_exits|]. unfold t_opened_dir. apply t_die_exits.
  - destruct (fs_lookup fs path) as [data|]; [|apply t_die_exits].
    apply exits_in_alt2; [apply t_die_exits|]. unfold t_opened. apply t_body_exits.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma hceil_of_sp_range : forall sp, valid_sp sp ->
  0x7fff7f800000 <= bv_unsigned sp - stack_max_size <= 0x7fffff800000.
Proof.
  intros sp (Hlo & Hhi & _). unfold sp_window_lo, sp_window_hi in *.
  change stack_max_size with 8388608. lia.
Qed.

Definition heap_ceil_of_sp (sp : word) (Hsp : valid_sp sp) : HeapCeil :=
  mkHeapCeil (bv_unsigned sp - stack_max_size) (hceil_of_sp_range sp Hsp).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section WithTR.
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Hypothesis FZ : forall (HCEIL : HeapCeil) (HSEC : HeapSecret),
      @BJIfaceLL.llvm_fuzz_stmt2 HCEIL (@MallocMF.HMF HCEIL HSEC) (@EhGlue.EHG.E HCEIL HSEC).

  (* [comment removed for export] *)
  Lemma TR : forall (HCEIL : HeapCeil) (HSEC : HeapSecret),
      @target_run_stmt OSSVerify.Proofs.boost_json.fuzz_parse.lib.PropExec.fx0 HCEIL (@MallocSR.HS HCEIL HSEC) (@MallocMF.HMF HCEIL HSEC).
  Proof.
    intros HCEIL HSEC.
    exact (@TargetRun.target_run_sound OSSVerify.Proofs.boost_json.fuzz_parse.lib.PropExec.fx0 HCEIL
             (@MallocSR.HS HCEIL HSEC) (@HeapGlue.heap_sr_hyps_closed HCEIL HSEC) (@HeapGlue.heap_extra_HS HCEIL HSEC)
             (@MallocMF.HMF HCEIL HSEC) (@HeapGlue.heap_extraM_HMF HCEIL HSEC) (@HeapGlue.handover_HS_HMF HCEIL HSEC)
             (@EhGlue.EHG.E HCEIL HSEC) (FZ HCEIL HSEC)
             (@EhGlue.EHG.EHB HCEIL HSEC) (@EhGlue.EHG.EHI HCEIL HSEC) (@EhGlue.EHG.EHF HCEIL HSEC)
             (@EhGlue.EHG.EHS HCEIL HSEC) (@EhGlue.EHG.EHSTK HCEIL HSEC)).
  Qed.

  Theorem ubsan_realizes_spec_lim :
    forall (sp brk mbase : word) (rnd : EntryDraw) (lim : Z) (inp : ProcInput),
      valid_sp sp -> valid_brk RSEGS brk -> 2 ^ 34 <= lim ->
      entry_stack_fits sp (in_argv inp) (in_envp inp) ->
      valid_argv (in_argv inp) -> valid_envp (in_envp inp) -> valid_fs (in_fs inp) ->
      realizes RSEGS (init_config RSEGS Ubsan.M.init_pc RPH sp brk mbase rnd lim inp)
               (spec (in_argv inp) (in_fs inp)).
  Proof.
    intros sp brk mbase rnd lim inp Hsp Hbrk Hlim Hfit Hva Hve Hfs.
    pose (HCEIL := heap_ceil_of_sp sp Hsp).
    pose (HSEC := heap_secret_of_draw rnd (canary_w rnd)).
    exact (@ref_realizes_spec_at HCEIL HSEC (@MallocSR.HS HCEIL HSEC) (@MallocMF.HMF HCEIL HSEC)
             (@HeapGlue.heap_sr_hyps_closed HCEIL HSEC) (@HeapGlue.heap_extra_HS HCEIL HSEC)
             (@HeapGlue.heap_extraM_HMF HCEIL HSEC)
             (@HeapGlue.RINIT_HS HCEIL HSEC) (@HeapGlue.AUXINIT_HS HCEIL HSEC) (@HeapGlue.KINIT_HS HCEIL HSEC)
             (TR HCEIL HSEC)
             sp brk mbase rnd lim inp eq_refl (conj eq_refl eq_refl) Hsp Hbrk Hlim Hfit Hva Hve Hfs).
  Qed.

  (* [comment removed for export] *)
  Lemma ubsan_realizes_spec_entry :
    forall en inp lim,
      valid_entry UBSAN en inp ->
      valid_argv (in_argv inp) -> valid_envp (in_envp inp) -> valid_fs (in_fs inp) -> in_va_size inp = Sv48 ->
      2 ^ 34 <= lim ->
      match en with mkEntry sp brk mbase rnd =>
        realizes RSEGS (init_config RSEGS Ubsan.M.init_pc RPH sp brk mbase rnd lim inp)
                 (spec (in_argv inp) (in_fs inp)) end.
  Proof.
    intros [sp brk mbase rnd] inp lim Hen Hva Hve Hfs Hsv Hlim.
    rewrite (valid_entry_sv48 _ _ _ Hsv) in Hen. destruct Hen as (Hsp & Hbrk & Hmb & Hfit).
    exact (ubsan_realizes_spec_lim sp brk mbase rnd lim inp Hsp Hbrk Hlim Hfit Hva Hve Hfs).
  Qed.

  (* [comment removed for export] *)
  Theorem ubsan_halts_lim : forall lim, 2 ^ 34 <= lim ->
    halts_allowed_T_scfg_budgets forced_only_cfg lim exit_codes_02 UBSAN.
  Proof.
    intros lim Hlim.
    apply (halts_allowed_T_scfg_budgets_down forced_only_cfg (@the_scfg hunspell_scfg));
      [apply forced_only_cfg_least|].
    intros [sp brk mbase rnd] inp Hen Hvalid.
    pose proof Hvalid as (Hva & Hve & Hfs & _ & _ & _ & _ & _ & _ & Hsv & _).
    pose proof (ubsan_realizes_spec_entry (mkEntry sp brk mbase rnd) inp lim Hen Hva Hve Hfs Hsv Hlim) as RZ.
    cbn [must_exit_in_scfg UBSAN].
    eapply realizes_must_exit_in; [exact RZ | left; reflexivity | apply spec_exits].
  Qed.

  Theorem ubsan_halts :
    halts_allowed_T_scfg_budgets forced_only_cfg ShippedBudgets.lim_source exit_codes_02 UBSAN.
  Proof. apply ubsan_halts_lim. unfold ShippedBudgets.lim_source, source_alloc_limit. cbn. lia. Qed.
End WithTR.
(* [comment removed for export] *)
