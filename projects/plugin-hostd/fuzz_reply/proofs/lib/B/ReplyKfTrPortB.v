(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: segment TOP of the ASan walk of fuzz_reply's relay_instance_gone
   (fuzz_reply.asan 0x82d98 .. 0x82e50 / 0x82f44), against the frozen segment interface
   lib/A/W_relay_instance_gone_cx.v (rig_top_stmt).  The Section-hypothesis block is that file's (commit
   92dac370558), verbatim.
   Layout: the tracks' pure trace lemmas, then the generic Section: its hypotheses, the statements of the lemma
   tracks, and their proofs (drain's
   model and budget, drain's live bytes, the relay representation across drain, GLIVE, GIN / GOUT at the key loop's
   start, the snprintf / strlen calls), then the walk itself: top_p1 (0x82d98 -> drain -> 0x82dd0), top_p2
   (0x82dd0 -> snprintf, strlen, the nheld test -> RGI / RGE) and rig_top_proof.
   C3 (475b8a2b569, the peak form): drain's room is the peak of its trace, a prefix of the remaining trace (top_room);
   drain's live bytes are bounded in the NET form, blocks_bytes S' <= blocks_bytes S + tr_net (dr_tr ..) (dr_bytes:
   the potential td_pot now weighs the pending texts too, which drain frees as it reads them), and tb_core carries
   gbud's peak room across the drain step with tr_peak_app.
   ROUTE (b), STEP 3 (CONVERSION.md (sha256 1015972e02a9; internal record); the RIG_x round): over any allocator relation
   ARx with its laws and the room record RP, at W_relay_instance_gone_cx.v's generic Section c (its list copied
   verbatim).  The statements of the lemma tracks now sit inside that Section, after its hypotheses.  Every journal is
   ajournal_gx_x with its head sets; the laws are AR_laws_x's.  THE ROOM at the drain call: gbud's room over the
   remaining trace grest i splits at the drain (tr_cost MT_rk is additive and nonnegative), so drain gets
   rp_RM RP S (Z.to_nat (dr_cost MT_rk ..) + dr_kr ..) with dr_kr the rest's MT_rk count plus gxkr, and its post's
   rp_RM RP S' dr_kr is gbud's room after the drain (top_room / top_budget).  THE COUNTS: drain's count premise dr_pk is
   within gbud's (tr_peakP of a prefix), and after the drain the live counts move by exactly tr_netP of drain's trace
   (stmt_dr_cnt, RR's lib/A/W_rr_m_dcnt.v rmc_dr_cnt), which tr_peakP_app turns into gbud's count bound over the rest
   (tb_core).  The fake frame is only 32-aligned in a generic state (alx_frames): ts_ra, ts_hull and the shadow seat
   tp_seat2 read that alignment (F's shadow address is 4-aligned). *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_reply/lib/A/W_rig_top.v, with its module paths and module names changed; 516 of its 657 lines of code are new or changed and 5398 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_reply/lib/A/ReplyCntAcc.v; 3 of its 62 lines of code are new or changed and 598 lines of the source are left out. *)
(* The drain helpers of lib/A/ReplyCntAcc.v that ReplyKfTrRigB.v uses and lib/B lacks: a drain's final state, with
   g_nout and g_capout forgotten, does not depend on its sends (acc_canon, acc_fin_canon).  Image B's twin of
   lib/A/ReplyCntAcc.v:573-628: the same names, statements and proofs, over the shared lib/Prog models.  The
   trace-count helpers of lib/A/W_tr_cnt.v (ge_cap_tr, ge_cap_of_keys, tc_gse and the rest) are the kit twin
   lib/B/W_tr_cnt.v's.
   proves no function (kind: segment lemma).
   The A source, with only the definitions and lemmas it needs (transitively):
   - lib/A/ReplyCntAcc.v:573-577 acc_kaf; :580-589 acc_lines_hk; :591-594 acc_canon; :595-624 acc_drain_canon;
     :625-630 acc_fin_canon. *)
From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require RelayRunF drain_b_c RelayCap.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import RelayKeys RelayModel.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

(* ================================================================== lib/A/ReplyCntAcc.v: the drain's model fields
   do not depend on its sends *)
(* the held array's size after the relayed lines: lines_run's, with no send and no names *)
Fixpoint acc_kaf (H : list (list Z)) (ka : Z) (ls : list (list Z)) : Z :=
  match ls with
  | [] => ka
  | l :: r => acc_kaf (seen_arr H l) (snd (fst (drain_b_c.seen_tr H ka l 0 RelayRunF.adr0 []))) r
  end.
Lemma acc_lines_hk : forall ls live mx no cap H ka j o ha ks,
  snd (fst (snd (fst (drain_b_c.lines_run live mx no cap H ka ls j o ha ks)))) = fold_left seen_arr ls H /\
  snd (snd (fst (drain_b_c.lines_run live mx no cap H ka ls j o ha ks))) = acc_kaf H ka ls.
Proof.
  induction ls as [|l ls IH]; intros live mx no cap H ka j o ha ks; cbn [drain_b_c.lines_run fst snd]; [split; reflexivity|].
  cbn [fold_left acc_kaf].
  match goal with |- context [drain_b_c.lines_run live mx ?n ?c ?H1 ?k1 ls ?jj ?oo ?hh ?kk] =>
    destruct (IH live mx n c H1 k1 jj oo hh kk) as (E1 & E2) end.
  rewrite E1, E2. split; [reflexivity|]. f_equal. apply RelayCap.rc_seen_ka.
Qed.
(* a drain state with g_nout and g_capout forgotten *)
Definition acc_canon (s : drain_b_c.dstate) : drain_b_c.dstate :=
  drain_b_c.DS (drain_b_c.ds_cap s) (drain_b_c.ds_u s) (drain_b_c.ds_skip s) (drain_b_c.ds_H s) (drain_b_c.ds_ka s)
    (drain_b_c.ds_eintr s) (drain_b_c.ds_pend s) (drain_b_c.ds_off s) (drain_b_c.ds_ref s) (drain_b_c.ds_en s)
    (drain_b_c.ds_ecap s) 0 0.
Lemma acc_drain_canon : forall f live mx s j a,
  acc_canon (fst (snd (drain_b_c.drain_run f live mx s j a))) =
  acc_canon (fst (snd (drain_b_c.drain_run f false 0 (acc_canon s) 0 drain_b_c.dadr0))).
Proof.
  induction f as [|f IH]; intros live mx [c u sk H ka ei pd off rf en ec no oc] j a; [reflexivity|].
  unfold acc_canon at 3. cbn [drain_b_c.ds_cap drain_b_c.ds_u drain_b_c.ds_skip drain_b_c.ds_H drain_b_c.ds_ka
    drain_b_c.ds_eintr drain_b_c.ds_pend drain_b_c.ds_off drain_b_c.ds_ref drain_b_c.ds_en drain_b_c.ds_ecap].
  cbn [drain_b_c.drain_run drain_b_c.ds_cap drain_b_c.ds_u drain_b_c.ds_skip drain_b_c.ds_H drain_b_c.ds_ka
       drain_b_c.ds_eintr drain_b_c.ds_pend drain_b_c.ds_off drain_b_c.ds_ref drain_b_c.ds_en drain_b_c.ds_ecap
       drain_b_c.ds_no drain_b_c.ds_ocap].
  rewrite (RelayCap.rc_grow_cap c (Z.of_nat (length u)) j (drain_b_c.da_buf a) 0 (drain_b_c.da_buf drain_b_c.dadr0)).
  set (cp := fst (snd (drain_b_c.grow_tr c (Z.of_nat (length u)) 0 (drain_b_c.da_buf drain_b_c.dadr0)))).
  destruct ei.
  - cbn [fst snd]. rewrite IH. symmetry. rewrite IH. reflexivity.
  - destruct pd as [|r0 rs]; [reflexivity|].
    match goal with |- context [Z.min ?x ?y <=? 0] => destruct (Z.min x y <=? 0) end; [reflexivity|].
    match goal with |- context [chunk u sk ?d] => destruct (chunk u sk d) as [[u' sk'] rl] end.
    match goal with |- context [drain_b_c.lines_run live mx no oc H ka rl ?j3 ?o3 ?h3 ?k3] =>
      destruct (acc_lines_hk rl live mx no oc H ka j3 o3 h3 k3) as (L1 & L2);
      destruct (drain_b_c.lines_run live mx no oc H ka rl j3 o3 h3 k3) as [[t1 [[oc1 H1] ka1]] [[o1 ha1] ks1]] end.
    match goal with |- context [drain_b_c.lines_run false 0 0 0 H ka rl ?j3 ?o3 ?h3 ?k3] =>
      destruct (acc_lines_hk rl false 0 0 0 H ka j3 o3 h3 k3) as (L3 & L4);
      destruct (drain_b_c.lines_run false 0 0 0 H ka rl j3 o3 h3 k3) as [[t2 [[oc2 H2] ka2]] [[o2 ha2] ks2]] end.
    cbn [fst snd] in L1, L2, L3, L4 |- *. subst H1 H2 ka1 ka2.
    match goal with |- context [drain_b_c.pushes_run en ec ?ls ?j1 ?v1 ?r1] =>
      match goal with |- context [drain_b_c.pushes_run en ec ls ?j2 ?v2 ?r2] =>
        tryif constr_eq j1 j2 then fail else
        rewrite (RelayCap.rc_pushes_cap ls en ec j1 v1 r1 j2 v2 r2) end end.
    rewrite IH. symmetry. rewrite IH. reflexivity.
Qed.
Lemma acc_fin_canon : forall live live' mx mx' NO NO' CAP CAP' e h,
  acc_canon (drain_b_c.drain_fin live mx NO CAP e h) = acc_canon (drain_b_c.drain_fin live' mx' NO' CAP' e h).
Proof.
  intros. unfold drain_b_c.drain_fin, drain_b_c.drain_go. rewrite acc_drain_canon. symmetry. rewrite acc_drain_canon.
  reflexivity.
Qed.
