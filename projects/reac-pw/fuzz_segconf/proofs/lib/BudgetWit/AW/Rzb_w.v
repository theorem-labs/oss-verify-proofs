(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Rares Buhai, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YK15.v, with its module paths changed. *)
(* Modified by Theorem Labs, 2026-11: made from this unit's Reusable/YK15.v by a three-way merge that carries libreac/fuzz_identity's edit of its own Reusable/YK15.v into lib/BudgetWit/Rzb.v (base: identity's YK15.v, ours: identity's Rzb.v, both at this unit's module paths; theirs: this unit's YK15.v); apart from the provenance header, where this file keeps this unit's YK15.v line, its conflicts are all in the relation rzb, its soundness and the node lemmas over it, where this unit's YK15.v has fuzz_knock's AllocMode text, and none of that survives: the file is cut to what YK18_w uses, the no-allocation-call check grant_ok and its lemmas, whose text the merge gives with no conflict; the opening comment is rewritten to describe what survived; the module here is BudgetWit.AW.Rzb_w. This unit's own lib/BudgetWit/Rzb.v (PR #2404) is not used because it has fuzz_knock's interface: its grant_ok takes segs and states alloc_budget_refused_b ... = false, and it has no grant_ok_budget and no sstep_acfg_of_grant, which YK18_w.bnode_of_grant needs (sstep_acfg_of_grant needs Cfg.acfg_nonspurious, whose premise ~ In (bv_unsigned x8) alloc_mark_sysnos that grant_ok does not give). *)
(* Theorem Labs, 2026-11: cut to the declarations the usage path at 16 GiB uses. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (the vDSO pair and vDSO steps; the vDSO arms of the budget premise). *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence OmniEquivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run OmniRun.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK16 YK0n YK0i YK0v YK02 YK1i YK15.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable.R Require Import Cfg.
Unset Lia Cache. Unset Nia Cache.
Import ListNotations.
Open Scope bv_scope.

(** * [grant_ok]: no allocation call is pending

    [grant_ok c]: if a syscall is pending at [c], its number is none of the
    four allocation numbers 214, 216, 222 and 226 (brk, mremap, mmap, mprotect;
    [Run.alloc_mark_sysnos]).  [YK18_w.bnode_of_grant] reads it through the two
    lemmas of Section [g]: the budget mark answers [false] there
    ([grant_ok_budget], from [Run.alloc_budget_refused_b_outside]), and every
    unfiltered step from such a configuration is an [sstep_cfg segs ACFG] step
    ([sstep_acfg_of_grant]): an instruction step and an exit step have no
    refusal premise, and a syscall step off the allocation numbers is never a
    spurious refusal under [ACFG] ([Cfg.acfg_nonspurious]).  [grant_ok_instr],
    [grant_ok_no] and [grant_ok_exit] discharge it at an instruction, at a
    literal non-allocation number, and at an exit. *)

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
