(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Rares Buhai, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YK15.v, with its module paths changed. *)
(* Modified by Theorem Labs, 2026-11: made from this unit's Reusable/YK15.v as libreac/fuzz_identity's lib/BudgetWit/Rzb.v is made from that unit's Reusable/YK15.v: the code is identity's Rzb.v cut to grant_ok, grant_ok_instr, grant_ok_nonalloc, grant_ok_no, grant_ok_exit, grant_ok_budget and sstep_acfg_of_grant, with this unit's module paths, over this unit's Reusable/YK15.v and Reusable/R/Cfg.v (this unit's YK15.v is libreac/fuzz_knock's byte for byte after module-path normalisation, not identity's); the module here is BudgetWit.AW.Rzb_w.  This unit's own lib/BudgetWit/Rzb.v is not used: it defines four of the six names YK18_w needs (grant_ok, grant_ok_instr, grant_ok_no, grant_ok_exit), its grant_ok asks only for the budget mark's answer, and it has neither grant_ok_budget nor sstep_acfg_of_grant, which YK18_w's bnode_of_grant needs; the second cannot be derived from it, since it needs Cfg.acfg_nonspurious, whose premise is that the pending call is none of the four allocation numbers, which that grant_ok does not give. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (the vvar/vDSO pages; the model's step and syscall-input changes). *)
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence OmniEquivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run OmniRun.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YK16 YK0n YK0i YK0v YK02 YK1i YK15.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable.R Require Import Cfg.
Unset Lia Cache. Unset Nia Cache.
Import ListNotations.
Open Scope bv_scope.

(** * [grant_ok]: no allocation call is pending

    [YK18_w.bnode_of_grant] discharges [YK18_w]'s node obligation where no
    allocation call is pending, through the names in this file.  [grant_ok c]:
    if a syscall is pending at [c], its number is none of the four allocation
    numbers 214, 216, 222 and 226 (brk, mremap, mmap, mprotect;
    [Run.alloc_mark_sysnos]).

    Where that holds, every unfiltered [sstep] from [c] is an
    [sstep_cfg segs ACFG] step ([sstep_acfg_of_grant]): an instruction step and
    an exit step have no refusal premise, and a syscall step off the allocation
    numbers is never a spurious refusal under [ACFG] ([Cfg.acfg_nonspurious]).
    It gives the budget mark's answer as well ([grant_ok_budget],
    [Run.alloc_budget_refused_b_outside]).

    These are libreac/fuzz_identity's lib/BudgetWit/Rzb.v lemmas of the same
    names, with their proofs.  The rest of that file, the relation [rzb] and its
    soundness, is not used on the usage path and is not kept here. *)


(** If a syscall is pending at [c], it is not an allocation call. *)
Definition grant_ok (c : config) : Prop :=
  forall x8, ms_svc_pending (cfg_ms c) = Some x8 -> ~ In (bv_unsigned x8) alloc_mark_sysnos.

Lemma grant_ok_instr : forall ms model,
  ms_svc_pending ms = None -> grant_ok (mkCfg ms model).
Proof.
  intros ms model Hsvc x8 Hx. cbn [cfg_ms] in Hx. rewrite Hsvc in Hx. discriminate Hx.
Qed.

Lemma grant_ok_nonalloc : forall ms model x8,
  ms_svc_pending ms = Some x8 -> ~ In (bv_unsigned x8) alloc_mark_sysnos ->
  grant_ok (mkCfg ms model).
Proof.
  intros ms model x8 Hsvc Hnin y Hy. cbn [cfg_ms] in Hy.
  rewrite Hsvc in Hy. injection Hy as <-. exact Hnin.
Qed.

(** The form [Cfg.transparent_nonalloc_no] has: the number as a literal, checked by
    [alloc_no_b]. *)
Lemma grant_ok_no : forall ms (model : Model) (x8 : word) (n : Z),
  ms_svc_pending ms = Some x8 -> bv_unsigned x8 = n -> alloc_no_b n = false ->
  grant_ok (mkCfg ms model).
Proof.
  intros ms model x8 n Hsvc Hx Hb. subst n.
  exact (grant_ok_nonalloc ms model x8 Hsvc (alloc_no_b_false _ Hb)).
Qed.

(** The exit (93 or 94) is off the four allocation numbers. *)
Lemma grant_ok_exit : forall ms model x8,
  ms_svc_pending ms = Some x8 -> is_exit_no x8 -> grant_ok (mkCfg ms model).
Proof.
  intros ms model x8 Hsvc [E|E]; (eapply grant_ok_no; [exact Hsvc | exact E | reflexivity]).
Qed.

Section g.
Variable segs : list Segment.

(** ... so the budget does not refuse it as a grant. *)
Lemma grant_ok_budget : forall c x8,
  grant_ok c -> ms_svc_pending (cfg_ms c) = Some x8 ->
  alloc_budget_refused_b (sys_input segs (cfg_ms c) x8) (cfg_model c) = false.
Proof.
  intros c x8 Hg Hx.
  exact (alloc_budget_refused_b_outside (sys_input segs (cfg_ms c) x8) (cfg_model c) (Hg x8 Hx)).
Qed.

(** Where no allocation call is pending, every step is an [ACFG] step. *)
Lemma sstep_acfg_of_grant : forall c e st,
  grant_ok c -> sstep segs c e st -> sstep_cfg segs ACFG c e st.
Proof.
  intros c e st Hg H. destruct H as
    [ms model ms' model' Hh Hs Hst
    | ms model Hh Hs Hst
    | ms model Hh Hs Hst Hv
    | ms model fn n eff model' model'' evs Hh Hs Hst Hv Hn Hspec Hret Hh' Hmat
    | ms model fn n eff model' evs Hh Hs Hst Hv Hn Hspec Hret Hh' Hmat
    | ms model fn Hh Hs Hst Hv Hu
    | ms model x8 eff model' model'' evs Hh Hs Hspec Hh' Hmat
    | ms model x8 eff model' evs Hh Hs Hspec Hh' Hmat
    | ms model x8 eff model' evs code Hh Hs Hspec Hh' Hk
    | ms model x8 eff model' evs sig Hh Hs Hspec Hk
    | ms model x8 Hh Hs Hspec ].
  - exact (sstep_cfg_instr segs ACFG ms model ms' model' Hh Hs Hst).
  - exact (sstep_cfg_instr_fault segs ACFG ms model Hh Hs Hst).
  - exact (sstep_cfg_instr_unmodeled segs ACFG ms model Hh Hs Hst Hv).
  (* 727298f3: the three vDSO arms, which [sstep_cfg] mirrors with no filter premise *)
  - exact (sstep_cfg_vdso_call segs ACFG ms model fn n eff model' model'' evs Hh Hs Hst Hv Hn Hspec Hret Hh' Hmat).
  - exact (sstep_cfg_vdso_materialization_fault segs ACFG ms model fn n eff model' evs Hh Hs Hst Hv Hn Hspec Hret Hh' Hmat).
  - exact (sstep_cfg_vdso_unmodeled segs ACFG ms model fn Hh Hs Hst Hv Hu).
  - exact (sstep_cfg_syscall segs ACFG ms model x8 eff model' model'' evs Hh Hs Hspec
      (acfg_nonspurious (sys_input segs ms x8) model eff (Hg x8 Hs)) Hh' Hmat).
  - exact (sstep_cfg_syscall_materialization_fault segs ACFG ms model x8 eff model' evs Hh Hs Hspec
      (acfg_nonspurious (sys_input segs ms x8) model eff (Hg x8 Hs)) Hh' Hmat).
  - exact (sstep_cfg_exit segs ACFG ms model x8 eff model' evs code Hh Hs Hspec Hh' Hk).
  - exact (sstep_cfg_killed segs ACFG ms model x8 eff model' evs sig Hh Hs Hspec Hk).
  - exact (sstep_cfg_syscall_unmodeled segs ACFG ms model x8 Hh Hs Hspec).
Qed.
End g.
