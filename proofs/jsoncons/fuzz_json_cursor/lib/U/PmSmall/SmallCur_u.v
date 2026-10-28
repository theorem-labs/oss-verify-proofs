(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib Require Import L5Defs L5Core. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U Require Import PmLibDefs_u PmCurDefs_u.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module SCU.
Lemma set_more_more : forall ps m, PML.ps_more (PMCUR.ps_set_more ps m) = m.
Proof. reflexivity. Qed.
Lemma set_more_id : forall ps, PMCUR.ps_set_more ps (PML.ps_more ps) = ps.
Proof. intros [] ; reflexivity. Qed.

Lemma wf_ps_stop : forall ps, PML.ps_more ps = false -> PML.wf_ps (PMCUR.ps_set_more ps true) -> PML.wf_ps ps.
Proof.
  intros ps Hm (W1 & W2 & W3 & W4 & (C & T & W5 & W6 & _)). destruct ps; cbn in *.
  split; [exact W1|]. split; [exact W2|]. split; [exact W3|]. split; [exact W4|]. exists C, T. split; [exact W5|]. split; [exact W6|]. intros Q; rewrite Hm in Q; discriminate Q.
Qed.
Lemma lvl_ok_stop : forall ps, PML.ps_more ps = false -> PMCUR.lvl_ok ps.
Proof. intros ps Hm Q. rewrite Hm in Q. discriminate Q. Qed.
Lemma wf_c_stop : forall ps, PML.ps_more ps = false -> PML.wf_ps (PMCUR.ps_set_more ps true) -> PMCUR.wf_c ps.
Proof. intros ps Hm H. split; [exact (wf_ps_stop ps Hm H) | exact (lvl_ok_stop ps Hm)]. Qed.

Lemma wf_ps_stale_stop : forall ps, PML.ps_more ps = false -> PML.wf_ps_stale (PMCUR.ps_set_more ps true) -> PML.wf_ps_stale ps.
Proof.
  intros ps Hm (Hn & n' & H). split; [destruct ps; exact Hn|]. exists n'.
  assert (E : PML.ps_set_nst (PMCUR.ps_set_more ps true) n' = PMCUR.ps_set_more (PML.ps_set_nst ps n') true) by (destruct ps; reflexivity).
  rewrite E in H. apply (wf_ps_stop (PML.ps_set_nst ps n')); [destruct ps; exact Hm | exact H].
Qed.

Lemma not_ics_container : forall x, x = PML.ST_ROOT \/ PML.is_container x -> ~ In x PMCUR.ICS.
Proof. intros x Hx Hin. unfold PML.is_container, PML.ST_ROOT, PML.ST_OBJECT, PML.ST_ARRAY in Hx. unfold PMCUR.ICS in Hin. cbn in Hin. unfold PML.ST_EXPECT_COMMA_OR_END, PML.ST_EXPECT_MEMBER_NAME_OR_END, PML.ST_EXPECT_MEMBER_NAME, PML.ST_EXPECT_COLON, PML.ST_EXPECT_VALUE_OR_END, PML.ST_EXPECT_VALUE, PML.ST_MEMBER_NAME in Hin. lia. Qed.

Lemma lvl_ok_rootc : forall ps C, PML.ps_stack ps = PML.ST_ROOT :: C -> Forall PML.is_container C ->
  (In (PML.ps_st ps) PMCUR.ICS -> PML.ps_more ps = true -> 1 <= PML.ps_level ps) -> PMCUR.lvl_ok ps.
Proof.
  intros ps C HS HC H Hm [Hin|(x & Hx & Hin)]; [exact (H Hin Hm)|]. exfalso. rewrite HS in Hx. destruct Hx as [<-|Hx].
  - exact (not_ics_container _ (or_introl eq_refl) Hin).
  - exact (not_ics_container x (or_intror (proj1 (Forall_forall _ _) HC x Hx)) Hin).
Qed.

Section Ev.
Variable segs : list Segment.
Lemma cur_post_event : forall ps ps' (M' : PMCUR.mem) V e,
  PML.ps_more ps' = false -> PMCUR.wf_c (PMCUR.ps_set_more ps' true) -> PMCUR.ev_at segs M' V e -> PMCUR.ev_rel (PML.ps_level ps) (PML.ps_win ps) ps' e ->
  PMCUR.cur_post segs ps ps' 0 M' V.
Proof.
  intros ps ps' M' V e Hm HW HE HR. split; [intros _ Q; rewrite Hm in Q; discriminate Q|]. intros _ _. right. split; [exact HW|]. exists e. split; [exact HE | exact HR].
Qed.

Lemma cur_post_err : forall ps ps' code (M' : PMCUR.mem) V, code <> 0 -> PMCUR.cur_post segs ps ps' code M' V.
Proof. intros ps ps' code M' V Hc. split; intros Q; contradiction. Qed.

Lemma cur_post_more : forall ps ps' code (M' : PMCUR.mem) V, PML.ps_more ps' = true -> PML.ps_level ps' = PML.ps_level ps -> PMCUR.cur_post segs ps ps' code M' V.
Proof. intros ps ps' code M' V Hm Hl. split; [intros _ _; exact Hl|]. intros _ Q. rewrite Hm in Q. discriminate Q. Qed.
End Ev.
End SCU.
