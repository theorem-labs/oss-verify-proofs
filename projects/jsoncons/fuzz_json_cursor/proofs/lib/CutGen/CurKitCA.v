(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Import HeapIface HeapIfaceA L5Defs L5Core PmLibDefs PmCurDefs PmLibDefsA.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module CKA.
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

Lemma stksh_deeper : forall (ar : asan_run) (M M' : PMCUR.mem) sp scr sp' scr',
  PMLA.stksh ar M sp scr -> (sp - scr) mod 8 = 0 -> (sp' - scr' - (sp - scr)) mod 8 = 0 -> sp - scr <= sp' - scr' ->
  (forall a, S (sp - scr) <= a < S (sp - scr) + (Z.max (ar_sptop ar) (ar_stack_top ar) - (sp - scr)) / 8 -> M' (Z_to_bv 64 a) = M (Z_to_bv 64 a)) ->
  PMLA.stksh ar M' sp' scr'.
Proof.
  intros ar M M' sp scr sp' scr' HS A1 A2 Hle AG jj Hjj. unfold PMLA.stksh in *. unfold byte_at.
  set (b := sp - scr) in *. set (b' := sp' - scr') in *. set (mx := Z.max (ar_sptop ar) (ar_stack_top ar)) in *.
  assert (Hk : exists k, b' = b + 8 * k /\ 0 <= k).
  { apply Z.mod_divide in A2; [|lia]. destruct A2 as [k Hk]. exists k. split; [lia | lia]. }
  destruct Hk as (k & Hb' & Hk0). rewrite Hb' in Hjj |- *.
  assert (ES : S (b + 8 * k) + jj = S b + (k + jj)).
  { unfold S. replace (b + 8 * k) with (b + k * 8) by lia. rewrite Z.div_add by lia. lia. }
  assert (EG : (mx - (b + 8 * k)) / 8 = (mx - b) / 8 - k).
  { replace (mx - b) with ((mx - (b + 8 * k)) + k * 8) by lia. rewrite Z.div_add by lia. lia. }
  rewrite EG in Hjj. rewrite ES. rewrite AG; [apply HS; lia | lia].
Qed.
End CKA.
