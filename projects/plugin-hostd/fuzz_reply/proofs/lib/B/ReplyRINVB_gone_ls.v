(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: group RI-gone of the image-A top (W_LLVMFuzzerTestOneInput_top_x.v, the rows
   RI_gone_pairs / RI_gone_read / RI_gone_step / RI_gone_end) at RINV := fr_RINV (ReplyRINV.v).  Proves no function
   walk (model-rule obligations only).
   Part 1 (over ReplyRINV.v's copies of the gone model, verbatim the same text as gone_base.v's):
   - RI_gone_pairs_holds: fr_RINV's pairing hj of the table with the open sources is a gn_pairs witness.  The size
     bounds gn_pair_ok asks come from fr_RINV's cost bound (fr_cost <= c_n < 2 ^ 26: a pending stream and a key count
     are parts of one entry's cost) and from fr_pair_ok's ecap_ok.
   - RI_gone_read_holds: a slot k that reads (gn_reads m k = 1) holds the source of an open entry j; that entry's
     gn_pair_ok source is at slot k (fr_RINV's distinct fds, RI_fds_holds), so after relay_instance_gone slot k holds
     rig_post's source for entry j, which rig_rel's dr_rel leaves drained (pending list empty, offset 0).
   - RI_gone_read_sat: one state meets all of RI_gone_read's premises (and RI_gone_pairs's).
   - Section collapse / collapse2: the records of rounds 1 and 2 of the gone rules' texts (bb9dae5d905, a1a3591c77c),
     which were false at the instance; machine-checked counter-instances, not proofs of the rows.
   Part 2 (over W_LLVMFuzzerTestOneInput_gone_base.v's own model): RI_gone_pairs_plug / RI_gone_read_plug restate
   part 1 at gone_base's GN_RI_pairs / GN_RI_read; then the step and end rows.
   - The table-order loop (gn_run) as an invariant (rg_inv): every entry's slot, once processed, holds what
     check_no_loss and check_shape_ends left of what relay_instance_gone left there; when gone = 0, `at` is the
     entry's position in the stream relay_instance_gone sent (rg_acc_pos), which is the entries' drained lines and
     then their ended keys' end lines (rg_rel_dec, rg_strm).
   - RI_gone_step_holds(_c): GN_RI_step of a working branch a39b599f92e (copied verbatim as
     GN_RI_step_d) at MT := ameter_triv, RINV := fr_RINV, MMAX := WR_MMAX, LS := fr_LS3 B / fr_LS3c B.  The LS-side
     conjunct cnl_room is a Theorem Labs lane's gx6_step_room(_c) (ReplyLS3cTopxGoneF.v at b25d82fcf04); mo_ok is True at
     ameter_triv; the rest is RINV-side (rg_step_rinv_side).
   - RI_gone_end_holds_q5(_c): GN_RI_end of a39b599f92e (copied as GN_RI_end_q5) with REQ5 (no held list's capacity
     shrinks from m to mc) as one more, last, premise: s5-r1d's gx6_end_LS3(_c) needs it, and a39b599f92e's gn_cnl_ok
     does not carry `hl_cap (hs_held h) <= hl_cap H'` from which ReplyLS3cTopxGoneH.v's gxh_req5 derives it.
   - GN_RI_step_r3 (Section rg3): the record of round 3 (aa34c06e82c): without re_U NUL-free the step row is false.
   Local helpers rg_lines_nz / rg_upds_in / rg_W_read_lines_nz state what a Theorem Labs lane's ReplyRINV_a12.v
   (lines_nul_free / upds_nul_free) states; they stay local. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_reply/lib/A/ReplyRINV_gone.v, with its module paths and module names changed; 496 of its 612 lines of code are new or changed and 2807 lines of the source are left out. *)
(* proves no function (rule 24; kind: segment lemma): the LS halves of image B's GN_RI_step_x / GN_RI_end_x (B
   top_x Section hypotheses, lib/B/W_LLVMFuzzerTestOneInput_top_x.v :892-893; B-TOPX-OWNERS rows 96-97, row G-BRI-gone)
   at B's v3 LS instance, and the two rows from them with the RINV halves of lib/B/ReplyRINVB_gone.v.
   THE TEXTS are the F3 gone_base's (a Theorem Labs lane's KF-COUNT text: binder q, premises gn_runc .. q and gn_cst cx m m1 q
   cst); RG.GN_RI_step_room / RG.GN_RI_end_ls copy their premise lists verbatim.  The B v3 gone lemmas cited here
   (lib/B/ReplyB3LS3cTopxGoneF.v gx6_step_room_c / gx6_end_LS3c, ReplyB3LS3oGn.v fr_OUT_gone_end, ReplyB3LS3e.v
   fr_ENT_gone_end, ReplyB3LScap.v fr_CAP_gone_end) are stated at the pre-F3 premise lists with REQ1-REQ3 (and REQ5):
   the F3 extras q, gn_runc and gn_cst are premises they do not read and are dropped; since KF-COUNT B (09be0e8b51b)
   they are generic in the meter and take the row's own `mo_le MT S Sx cst`, so the halves hold at EVERY meter MT;
   REQ5 is gxh_req5 below.
   THE INSTANCE (lib/B/ReplyLS3B_inst.v :224-227): LSI B OM fr_CAP := fr_LS3cp B YCfn_cf.CALL_ROOM_B /\ fr_OUT OM /\
   fr_ENT B /\ fr_CAP, fr_LS3cp := fr_LS3c /\ fr_POT (lib/B/ReplyB3LS3p.v :326-327).
   - the room half GN_RI_step_room_lsi: gx6_step_room_c at fr_LS3c (lsi_parts), its premise
     YCfn_cf.CALL_ROOM_B <= CALL_ROOM_B by Z.le_refl;
   - the end LS half GN_RI_end_ls_lsi, conjunct by conjunct: fr_LS3c gx6_end_LS3c, fr_POT fr_POT_gone_end (below),
     fr_OUT fr_OUT_gone_end, fr_ENT fr_ENT_gone_end, fr_CAP the slot rule GN_CAP_end (fr_CAP_gone_end's statement at
     any fr_CAP; at ReplyB3LScap.fr_CAP it is fr_CAP_gone_end, GN_CAP_end_cap);
   - the rows GN_RI_step_lsi / GN_RI_end_lsi: RG.GN_RI_step_of_parts / RG.GN_RI_end_of_parts with
     RG.GN_RI_step_ri_holds / RG.GN_RI_end_ri_holds; the step's two meter conjuncts (RG.GN_RI_step_cnl_meter /
     RG.GN_RI_step_cshe_meter) are premises at a generic meter, as in RG.GN_RI_step_ls_of_room_mt, proved at
     ameter_triv (GN_RI_step_lsi_triv) and at the counting meter ReplyKfMeterB.MT_sec nsec KMAX from the instance's
     count clause fr_SEC (lib/B/ReplyLSBSec.v), in its last slot (GN_RI_step_lsi_sec, GN_RI_end_lsi_sec).
   At the end, what B's top needs (TfibB, RINV := fr_RINV, MMAX := CfParamsReply.fr_MMAX): GN_RI_step_x_sec /
   GN_RI_end_x_sec, top_x's two rows verbatim at MT_sec with LSx := LSI TfibB OUT_MAX4 (ReplyB3LScap.fr_CAP /\
   fr_SEC ..), the forms k3 plugs; and, as Checks, the two rows at ameter_triv with LSx := LSI TfibB OUT_MAX4
   ReplyB3LScap.fr_CAP.
   Two pieces have no lib/B twin and are ported here under their A names, over lib/B's records, their proofs A's word
   for word over the lib/B twins of the names they cite (lib/B/ReplyB3LS3p.v, ReplyB3LS3Arms.v,
   ReplyB3LS3cTopxGone.v, ReplyB3LS3cTopxGoneF.v): the gone end's fr_POT half (lib/A/ReplyLS3pGn.v :86-392, the pg
   lemmas and fr_POT_gone_end) and REQ5 from GN_RI_end's own premises (lib/A/ReplyLS3cTopxGoneH.v :62-145, the gxh
   lemmas). *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn YP0b YP0a.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YN3v YI04 YI00.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YP0d YP0c YC80 YC81 YO0a YN1e.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YO09.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YB1v.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YI16 YE00.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YE01 YE2k.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YC5d YCbp.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require YCfn.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib Require Import ZTraceSpec.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import
W_syms W_listing W_place W_tbl W_kit W_pl W_img W_journal.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import HarnessRep RelayRep.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_rep W_contract W_sites W_frame W_op_add.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require ReplyGuardB.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_LLVMFuzzerTestOneInput_cut.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_LLVMFuzzerTestOneInput_cut_x.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_LLVMFuzzerTestOneInput_drain_defs.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_LLVMFuzzerTestOneInput_write.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_LLVMFuzzerTestOneInput_arm_event.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import
  W_LLVMFuzzerTestOneInput_head W_LLVMFuzzerTestOneInput_small W_LLVMFuzzerTestOneInput_add.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import CheckRep.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import RelayKeys RelayModel ListRep.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require
  RelayRunT RelayRunF drain_b_c gestures_end_b_c gesture_end_c relay_remove_b_c relay_instance_gone_b_c RelayCap
  SlotReads SlotInv SlotDrain3Aux SlotPass2Aux relay_remove_b_aux send_line_b_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import CfParamsReply.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require YCfn_cf.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import ReplyLSB ReplyRINVB ReplyLSBArms.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import ReplyLSBDrainPre ReplyLSBTrPeak.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import
ReplyB3Base ReplyB3LS3 ReplyB3LS3Arms ReplyB3LSCntL ReplyB3LS3c.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import ReplyB3LS3cTopxDefs ReplyB3LS3cTopxGone.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import ReplyLSBo ReplyLSBoRf ReplyB3LS3o.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import ReplyB3LS3cTopxGoneF.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import ReplyB3LS3oGn ReplyB3LS3e ReplyB3LS3p.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import ReplyB3LS3eCap.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require W_LLVMFuzzerTestOneInput_gone_base.
Local Notation gn_pairs := W_LLVMFuzzerTestOneInput_gone_base.gn_pairs.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require YD2l ReplyB3LScap ReplyLS3B_inst ReplyRINVB_gone.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require ReplyKfMeterB ReplyLSBSec.
(* the zify flag as the unit leaves it (a Theorem Labs lane's ZIFY-FLAG-NOTE), whatever a Required file leaves *)
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Import ListNotations.
Local Unset Lia Cache. Local Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Local Notation zsum l := (fold_right Z.add 0 l).
Local Notation LSI := ReplyLS3B_inst.LSI.
Local Notation RG_step_room := ReplyRINVB_gone.RG.GN_RI_step_room.
Local Notation RG_end_ls := ReplyRINVB_gone.RG.GN_RI_end_ls.

(* ================================================================== REQ5 from GN_RI_end's own premises
   (lib/A/ReplyLS3cTopxGoneH.v :59-145, word for word): no held list's capacity shrinks from m to mc.  B's gn_cnl_ok
   (gone_base :466-473) carries `hl_cap (hs_held h) <= hl_cap H'` as its eighth conjunct, as A's does. *)
Section gh.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
(* ================================================================== the slot lists *)
Lemma gxh_setn_same : forall k x (l : list (option hsrc)) y, nth k l None = Some y -> nth k (gn_setn k x l) None = x.
Proof.
  induction k as [|k IH]; intros x [|z l] y H; cbn in *; try discriminate; [reflexivity | exact (IH x l y H)].
Qed.
Lemma gxh_setn_other : forall k j x (l : list (option hsrc)), j <> k -> nth j (gn_setn k x l) None = nth j l None.
Proof.
  induction k as [|k IH]; intros j x [|z l] Hne; cbn; try reflexivity.
  - destruct j as [|j]; [congruence | reflexivity].
  - destruct j as [|j]; [reflexivity | apply IH; lia].
Qed.

(* ================================================================== m -> m1: relay_instance_gone keeps held lists *)
(* a slot that holds a source in m holds one in m1 with the same held list: kept slots by gn_after_rig's clause
   (6a2e02357a4 gone_base.v:434-435), drained slots by gn_pair_ok's slot (:418) and dr_rel's hs_held clause
   (W_contract.v:1232) through gn_rig_ok's rig_rel (:450-451) *)
Lemma gxh_rig_held : forall cx t m hs qs c2 O2 cap2 out2 m1,
  fr_RINV cx t m -> gn_pairs m hs -> gn_after_rig cx m hs qs c2 O2 cap2 out2 m1 ->
  gn_rig_ok cx m hs qs c2 O2 cap2 ->
  forall j hj, nth j (lm_hs m) None = Some hj ->
  exists hj1, nth j (lm_hs m1) None = Some hj1 /\ hs_held hj1 = hs_held hj.
Proof.
  intros cx t m hs qs c2 O2 cap2 out2 m1 HRI Hpairs Hafter Hrok j hj Hj.
  pose proof Hafter as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & A10 & A11 & A12 & A13).
  pose proof Hpairs as (Hlh & _ & _).
  pose proof Hrok as (Hrr & Hlq & _ & _).
  pose proof (gx_pq_facts cx m hs qs c2 O2 cap2 out2 m1 Hpairs Hafter Hrok) as HPQ.
  pose proof (gx_rig_pairs _ _ _ _ _ _ _ _ _ _ Hrr) as HRP.
  rewrite Forall_forall in HPQ, HRP.
  assert (Hj4 : (j < 4)%nat).
  { pose proof HRI as (_ & (Hl4 & _) & _).
    destruct (Nat.lt_ge_cases j (length (lm_hs m))) as [L|L]; [lia|].
    rewrite nth_overflow in Hj by exact L. discriminate Hj. }
  set (ps := combine (lm_es m) hs) in *.
  destruct (in_dec Nat.eq_dec j (rig_slots ps)) as [Hin|Hnin].
  2: { exists hj. split; [rewrite (A12 j Hj4 Hnin); exact Hj | reflexivity]. }
  destruct (gx_rs_in j ps Hin) as (p & Hp & Heof & Hpk).
  destruct (In_nth ps p (gn_e0, gn_hj0) Hp) as (i & Hi & Hpi).
  assert (Hlps : length ps = length qs) by (unfold ps; rewrite length_combine; lia).
  set (q := nth i qs gn_q0).
  assert (Hpq : In (p, q) (combine ps qs)).
  { rewrite <- Hpi. unfold q. rewrite <- combine_nth by exact Hlps. apply nth_In. rewrite length_combine. lia. }
  destruct (HRP _ Hpq) as (_ & Hdr). cbn [fst snd] in Hdr.
  destruct (Hdr Heof) as (c & mx & no & cap & e1 & LB & Hd).
  destruct (HPQ _ Hpq Heof) as (_ & Hm & Hm1). cbn [fst snd] in Hm, Hm1.
  destruct p as [e [h0 j']]. cbn [fst snd] in *. subst j'.
  rewrite Hj in Hm. injection Hm as Eh0. subst h0.
  destruct (gx_dr_rel _ _ _ _ _ _ _ _ _ Hd) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Dheld & _).
  exists (snd q). split; [exact Hm1 | exact Dheld].
Qed.

(* ================================================================== m1 -> mc: the loop never lowers a held capacity *)
Lemma gxh_run_held : forall P m1 mc A i k, gn_run P m1 mc A i k ->
  forall j hj hj', nth j (lm_hs m1) None = Some hj -> nth j (lm_hs mc) None = Some hj' ->
  hl_cap (hs_held hj) <= hl_cap (hs_held hj').
Proof.
  intros P m1 mc A i k HR.
  induction HR as [|mc A i k HR IH Hk Hs|mc A i k h h' h'' E' H' ds c HR IH Hk Hi Hh Hfd Hc Hcs|mc A i HR IH];
    intros j hj hj' H1 H2.
  - rewrite H1 in H2. injection H2 as E2. subst hj'. lia.
  - exact (IH j hj hj' H1 H2).
  - cbn [gn_set lm_hs] in H2.
    destruct (Nat.eq_dec j k) as [->|Hne].
    + rewrite (gxh_setn_same k (Some h'') (lm_hs mc) h Hh) in H2. injection H2 as E2. subst hj'.
      pose proof (IH k hj h H1 Hh) as Hle.
      destruct Hc as (Eh' & _ & _ & _ & _ & _ & _ & Hb & _).
      destruct Hcs as (H2' & Eh'' & _ & Hc2 & _).
      subst h'' h'. cbn [set_held set_exp_held hs_held] in Hc2, Hb |- *. lia.
    + rewrite (gxh_setn_other k j (Some h'') (lm_hs mc) Hne) in H2. exact (IH j hj hj' H1 H2).
  - exact (IH j hj hj' H1 H2).
Qed.

(* ================================================================== REQ5 from the rule's own premises *)
Lemma gxh_req5 : forall cx t m hs qs c2 O2 cap2 out2 m1 mc A i k,
  fr_RINV cx t m -> gn_pairs m hs -> gn_after_rig cx m hs qs c2 O2 cap2 out2 m1 ->
  gn_rig_ok cx m hs qs c2 O2 cap2 -> gn_run (gn_pre cx m) m1 mc A i k ->
  forall j hj hj', nth j (lm_hs m) None = Some hj -> nth j (lm_hs mc) None = Some hj' ->
  hl_cap (hs_held hj) <= hl_cap (hs_held hj').
Proof.
  intros cx t m hs qs c2 O2 cap2 out2 m1 mc A i k HRI Hpairs Hafter Hrok Hrun j hj hj' Hj Hj'.
  destruct (gxh_rig_held cx t m hs qs c2 O2 cap2 out2 m1 HRI Hpairs Hafter Hrok j hj Hj) as (hj1 & Hj1 & Eh).
  pose proof (gxh_run_held _ m1 mc A i k Hrun j hj1 hj' Hj1 Hj') as Hle.
  rewrite Eh in Hle. exact Hle.
Qed.
End gh.

(* ================================================================== fr_POT kept by the gone arm (lib/A/ReplyLS3pGn.v
   :86-394, word for word): for every class c the potential pt_s c * pt_kc c m + pt_v c * pt_mass m does not grow from
   m to mc (pg_core), so fr_POT_step closes with the operation's write budget unused.  A's header (:3-35) says why;
   fr_POT_gone_end's premises are fr_OUT_gone_end's with fr_OUT OM cx t m ly S -> fr_POT cx t m and fr_LS3 and the
   block relation dropped. *)
(* ================================================================== the potential by component *)
(* an entry: its keys of class c and its unfinished line *)
Definition pg_EP (c : Z) (e : rentry) : Z := pt_s c * pt_ekc c e + pt_v c * pt_eu e.
(* a slot as fr_POT counts it: its expected and held texts of class c, its pending bytes past the read offset *)
Definition pg_SP (c : Z) (o : option hsrc) : Z := pt_s c * pt_skc c o + pt_v c * slot_pend o.
(* a slot between relay_instance_gone and check_no_loss: its held texts and the begin keys of its expected texts *)
Definition pg_SQ (c : Z) (o : option hsrc) : Z :=
  match o with
  | Some h => pt_s c * (pt_tc c (texts (hs_held h)) + pt_tc c (dr3_nk (texts (hs_expected h)))) +
              pt_v c * slot_pend (Some h)
  | None => 0
  end.

Lemma pg_zsum_lin : forall {X : Type} (a b : Z) (f g : X -> Z) l,
  zsum (map (fun x => a * f x + b * g x) l) = a * zsum (map f l) + b * zsum (map g l).
Proof. intros X a b f g l. induction l as [|x l IH]; cbn [map fold_right]; [ring|]. rewrite IH. ring. Qed.
Lemma pg_split : forall c m, pt_s c * pt_kc c m + pt_v c * pt_mass m =
  zsum (map (pg_EP c) (lm_es m)) + zsum (map (pg_SP c) (lm_hs m)).
Proof.
  intros c m. unfold pt_kc, pt_mass, pend_bytes, pg_EP, pg_SP.
  rewrite (pg_zsum_lin (pt_s c) (pt_v c) (pt_ekc c) pt_eu (lm_es m)).
  rewrite (pg_zsum_lin (pt_s c) (pt_v c) (pt_skc c) slot_pend (lm_hs m)).
  generalize (zsum (map (pt_ekc c) (lm_es m))) (zsum (map (pt_skc c) (lm_hs m))) (zsum (map slot_pend (lm_hs m)))
    (zsum (map pt_eu (lm_es m))) (pt_s c) (pt_v c).
  intros a b d f s v. ring.
Qed.
Lemma pg_SQ_SP : forall c h, hl_recs (hs_expected h) = [] -> pg_SQ c (Some h) = pg_SP c (Some h).
Proof.
  intros c h H. unfold pg_SP. cbn [pg_SQ pt_skc].
  assert (E : texts (hs_expected h) = []) by (unfold texts; rewrite H; reflexivity).
  rewrite E. assert (Z1 : dr3_nk [] = []) by reflexivity. assert (Z0 : pt_tc c [] = 0) by reflexivity.
  rewrite Z1, Z0, Z.add_0_r, Z.add_0_l. reflexivity.
Qed.
Lemma pg_SQ_SP_none : forall c, pg_SQ c None = pg_SP c None.
Proof. intros c. unfold pg_SP. cbn [pg_SQ pt_skc slot_pend]. rewrite !Z.mul_0_r. reflexivity. Qed.

(* ================================================================== relay_instance_gone, entry by entry *)
(* gestures_end_instance keeps a sub-permutation of the keys *)
Lemma pg_geik : forall c pre ks,
  pt_tc c (drain_b_c.keys_texts (snd (geik pre ks))) <= pt_tc c (drain_b_c.keys_texts ks).
Proof.
  intros c pre ks. unfold geik.
  destruct (gx_geik_loop (length ks) pre 0 ks) as (HP & _).
  set (E := fst (geik_loop (length ks) pre 0 ks)) in *.
  set (K := snd (geik_loop (length ks) pre 0 ks)) in *.
  assert (EQ : pt_tc c (drain_b_c.keys_texts ks) =
               pt_tc c (drain_b_c.keys_texts E) + pt_tc c (drain_b_c.keys_texts K)).
  { unfold pt_tc, drain_b_c.keys_texts. rewrite <- zsum_app, <- !map_app.
    apply fr_sum_perm. apply Permutation_map. exact HP. }
  pose proof (pt_tc_nonneg c (drain_b_c.keys_texts E)). lia.
Qed.
(* an eof entry: its keys with the prefix ended, its re_U kept *)
Lemma pg_closed : forall c pre e, pg_EP c (entry_keys e (snd (geik pre (re_keys e)))) <= pg_EP c e.
Proof.
  intros c pre e. unfold pg_EP.
  assert (E1 : pt_ekc c (entry_keys e (snd (geik pre (re_keys e)))) =
               pt_tc c (drain_b_c.keys_texts (snd (geik pre (re_keys e))))) by reflexivity.
  assert (E2 : pt_eu (entry_keys e (snd (geik pre (re_keys e)))) = pt_eu e) by reflexivity.
  rewrite E1, E2. pose proof (pg_geik c pre (re_keys e)) as G. pose proof (pt_s_ge c).
  assert (M : pt_s c * pt_tc c (drain_b_c.keys_texts (snd (geik pre (re_keys e)))) <= pt_s c * pt_ekc c e)
    by (apply Z.mul_le_mono_nonneg_l; [lia | exact G]).
  lia.
Qed.
(* an open entry and its slot: the drain (fr_LS3cp_drain_step_p's arithmetic, check_no_loss's keys in pg_SQ), then
   gestures_end_instance *)
Lemma pg_open : forall c pre cc mx no cap e h j e1 h1 LB,
  gx_pf (e, (h, j)) -> dr_rel cc mx no cap e h e1 h1 LB ->
  pg_EP c (entry_keys e1 (snd (geik pre (re_keys e1)))) + pg_SQ c (Some h1) <= pg_EP c e + pg_SQ c (Some h).
Proof.
  intros c pre cc mx no cap e h j e1 h1 LB Hpf Hdr.
  destruct Hpf as (Hexp & Hec0 & Hoff & Hsk & HskU & Hsk01 & Hepre & Hkh & Hhpre & _).
  cbn [fst snd] in *.
  pose proof Hepre as (Hce & HU & HUz & _).
  destruct (gx_exp_lines cc mx no cap e h e1 h1 LB Hdr Hexp) as (HT & _ & _ & _).
  destruct (gx_dr_rel cc mx no cap e h e1 h1 LB Hdr)
    as (_ & _ & HU' & _ & Hnd & Hss & _ & _ & _ & Dpend & Doff & _ & _ & Dheld & _).
  set (Ls := dr_lines h) in *.
  set (TOT := Z.of_nat (length (with_nul Ls))).
  (* ---- the relay's mass: TOT + U' <= U + P ---- *)
  assert (HJ : J1 (bzs (re_U e)) (re_skip e =? 1) (hs_state h)) by exact (dr3_J1 e h Hsk HskU Hsk01 HU HUz).
  assert (Hce0 : re_cap e = 0 \/ 8192 <= re_cap e) by lia.
  assert (Hkh168 : 168 * Z.of_nat (length (re_keys e)) <= 21 * drain_b_c.ent_ka e).
  { unfold drain_b_c.ent_ka. destruct Hkh as [(E1 & E2) | (E1 & E2)].
    - rewrite E1, E2. cbn [length Z.of_nat Z.eqb]. lia.
    - rewrite (proj2 (Z.eqb_neq _ _) E1). unfold re_nheld in E2. lia. }
  pose proof (relay_remove_b_aux.rma_fin_no (dr_live cc h) mx no cap e h HJ (dr3_pok no cap e h Hoff Hhpre) Hce0)
    as Hno.
  change (lines (hs_state h) (bzs (pending_stream h))) with Ls in Hno. fold TOT in Hno.
  assert (HU6 : Z.of_nat (length (re_U e)) <= 6000) by (unfold APARTIAL in HU; lia).
  destruct (gx_drain_fin (dr_live cc h) mx no cap e h (proj1 Hhpre) Hkh168 Hce HU6 Hec0) as (RM & _).
  unfold dr_fin in HU'. rewrite <- HU' in RM. rewrite SlotReads.bzs_length in RM.
  assert (HMASS : TOT + Z.of_nat (length (re_U e1)) <=
                  Z.of_nat (length (re_U e)) + Z.of_nat (length (pending_stream h))) by lia.
  clear RM Hno.
  (* ---- the keys: the drain's are within the old ones and the lines' begin keys; gestures_end_instance removes ---- *)
  assert (KI : pt_ekc c e1 <= pt_ekc c e + pt_tc c (dr3_nk Ls)).
  { unfold pt_ekc, pt_tc. pose proof Hnd as Hnd2. apply NoDup_ListNoDup in Hnd2.
    pose proof (pt_sum_incl (pt_w c) (drain_b_c.keys_texts (re_keys e1))
                  (drain_b_c.keys_texts (re_keys e) ++ dr3_nk Ls) (fun x => proj1 (pt_w_range c x)) Hnd2) as X.
    rewrite map_app, zsum_app in X. apply X. intros y Hy. apply in_or_app.
    destruct (dr3_upds_in Ls _ y (proj1 (Hss y) Hy)) as [Hy'|Hy']; [left | right]; exact Hy'. }
  pose proof (pg_geik c pre (re_keys e1)) as HG.
  change (pt_tc c (drain_b_c.keys_texts (re_keys e1))) with (pt_ekc c e1) in HG.
  pose proof (pt_nk c Ls) as NK. fold TOT in NK.
  pose proof (pt_s_ge c) as Hs. pose proof (pt_v_range c) as Hv.
  assert (HTOT0 : 0 <= TOT) by (unfold TOT; lia).
  (* ---- the slot: pending bytes released, the lines expected, the held texts kept ---- *)
  assert (ES1 : slot_pend (Some h1) = 0) by (cbn [slot_pend]; unfold hl_bytes; rewrite Dpend, Doff; reflexivity).
  assert (ES0 : slot_pend (Some h) = Z.of_nat (length (pending_stream h)))
    by (symmetry; exact (ls3_ps_sp h (proj1 Hhpre))).
  assert (EX0 : texts (hs_expected h) = []) by (unfold texts; rewrite Hexp; reflexivity).
  unfold pg_EP. cbn [pg_SQ]. rewrite ES1, ES0, HT, EX0, Dheld.
  assert (Z0 : pt_tc c (dr3_nk []) = 0) by reflexivity. rewrite Z0.
  assert (Ek : pt_ekc c (entry_keys e1 (snd (geik pre (re_keys e1)))) =
               pt_tc c (drain_b_c.keys_texts (snd (geik pre (re_keys e1))))) by reflexivity.
  assert (Eu : pt_eu (entry_keys e1 (snd (geik pre (re_keys e1)))) = Z.of_nat (length (re_U e1))) by reflexivity.
  assert (Eu0 : pt_eu e = Z.of_nat (length (re_U e))) by reflexivity.
  rewrite Ek, Eu, Eu0.
  pose proof (pt_arith (pt_s c) (pt_v c) (pt_ekc c e + pt_tc c (texts (hs_held h)))
                (pt_tc c (drain_b_c.keys_texts (snd (geik pre (re_keys e1)))) + pt_tc c (texts (hs_held h)) +
                 pt_tc c (dr3_nk Ls))
                (Z.of_nat (length (re_U e)) + Z.of_nat (length (pending_stream h))) (Z.of_nat (length (re_U e1)))
                (pt_tc c (dr3_nk Ls)) TOT ltac:(lia) ltac:(lia) HTOT0 ltac:(lia) NK ltac:(lia)) as AR.
  rewrite !Z.mul_add_distr_l in AR |- *. lia.
Qed.

(* the table run: entries and drained slots after it, against before it (pg_SQ = pg_SP on m's open slots) *)
Lemma pg_rig : forall c pre mx ps qs cc O cap c2 O2 cap2,
  rig_rel pre mx cc O cap ps qs c2 O2 cap2 ->
  Forall (fun p => re_eof (fst p) = 0 -> gx_pf p) ps ->
  zsum (map (fun pq => pg_EP c (fst (snd pq))) (combine ps qs)) +
  zsum (map (fun pq => if re_eof (fst (fst pq)) =? 0 then pg_SQ c (Some (snd (snd pq))) else 0) (combine ps qs)) <=
  zsum (map (fun pq => pg_EP c (fst (fst pq))) (combine ps qs)) +
  zsum (map (fun pq => if re_eof (fst (fst pq)) =? 0 then pg_SQ c (Some (fst (snd (fst pq)))) else 0)
          (combine ps qs)).
Proof.
  intros c pre mx ps. induction ps as [|[e [h j]] r IH]; intros qs cc O cap c2 O2 cap2 HR HF.
  - destruct qs as [|q qs]; cbn [rig_rel] in HR; [|contradiction].
    cbn [combine map fold_right]. lia.
  - destruct qs as [|[e' h1] q]; cbn [rig_rel] in HR; [contradiction|].
    destruct HR as (e1 & ev & LB & HR). cbv zeta in HR. destruct HR as (Hd & He' & Hrest).
    apply Forall_cons_iff in HF as [Hp HF]. cbn [fst snd] in Hp.
    match type of Hrest with context [sl_sends ?a ?b ?d ?f ?g] =>
      destruct (sl_sends a b d f g) as [[c3 O3] cap3] eqn:ES end.
    pose proof (IH q c3 O3 cap3 c2 O2 cap2 Hrest HF) as I.
    clear ES Hrest IH.
    cbn [combine map fold_right fst snd].
    subst e'.
    revert Hd. destruct (re_eof e =? 0) eqn:Eo; cbn [andb]; intros Hd.
    + apply Z.eqb_eq in Eo. specialize (Hp Eo).
      pose proof (pg_open c pre cc mx _ cap e h j e1 h1 LB Hp Hd) as P1. lia.
    + destruct Hd as [-> ->]. pose proof (pg_closed c pre e) as P1. lia.
Qed.

(* ================================================================== the loop: one check_no_loss + check_shape_ends *)
Lemma pg_touch : forall c h h'', gx_touch h h'' ->
  pg_SQ c (Some h'') <= pg_SQ c (Some h) /\ hl_recs (hs_expected h'') = [].
Proof.
  intros c h h'' Ht.
  destruct (gx_touch_cost h h'' Ht) as (T1 & T0 & T3 & _).
  destruct Ht as (h' & E' & H' & P & g & A0 & ob & ds & cc & Hcnl & Hcshe).
  destruct (gx_cshe_perm P g A0 ob h' h'' ds cc Hcshe) as (H'' & E2 & _ & Hperm).
  destruct Hcnl as (E1 & _ & _ & _ & HndH' & HtH' & _).
  split; [|exact T3].
  cbn [pg_SQ].
  assert (Q3 : hs_held h'' = H'') by (rewrite E2; reflexivity).
  assert (Q5 : hs_held h' = H') by (rewrite E1; reflexivity).
  rewrite Q5 in Hperm.
  assert (Qs : slot_pend (Some h'') = slot_pend (Some h)) by (cbn [slot_pend]; rewrite T1, T0; reflexivity).
  assert (QE : texts (hs_expected h'') = []) by (unfold texts; rewrite T3; reflexivity).
  set (Ls := texts (hs_expected h)) in *.
  assert (W1 : pt_tc c (texts H'') <= pt_tc c (texts H')).
  { assert (P1 : Permutation (texts H') (texts H'' ++ map (fun r => bzs (snd r)) ds))
      by (unfold texts; rewrite <- map_app; apply Permutation_map; exact Hperm).
    unfold pt_tc. rewrite (fr_sum_perm _ (pt_w c) _ _ P1), map_app, zsum_app.
    pose proof (pt_tc_nonneg c (map (fun r => bzs (snd r)) ds)) as N. unfold pt_tc in N. lia. }
  assert (W2 : pt_tc c (texts H') <= pt_tc c (texts (hs_held h)) + pt_tc c (dr3_nk Ls)).
  { unfold pt_tc. pose proof HndH' as Hnd2. apply NoDup_ListNoDup in Hnd2.
    pose proof (pt_sum_incl (pt_w c) (texts H') (texts (hs_held h) ++ dr3_nk Ls)
                  (fun x => proj1 (pt_w_range c x)) Hnd2) as X.
    rewrite map_app, zsum_app in X. apply X. intros y Hy. apply in_or_app. rewrite HtH' in Hy.
    destruct (dr3_upds_in Ls _ y Hy) as [Hy'|Hy']; [left | right]; exact Hy'. }
  rewrite Qs, QE, Q3.
  assert (Z0 : pt_tc c (dr3_nk []) = 0) by reflexivity. rewrite Z0.
  pose proof (pt_s_ge c) as Hs.
  assert (M : pt_s c * (pt_tc c (texts H'') + 0) <=
              pt_s c * (pt_tc c (texts (hs_held h)) + pt_tc c (dr3_nk Ls)))
    by (apply Z.mul_le_mono_nonneg_l; lia).
  lia.
Qed.

Section pgn.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.

(* ================================================================== the potential, m against mc *)
Lemma pg_core : forall c cx t m hs qs c2 O2 cap2 out2 m1 mc A,
  fr_RINV cx t m -> gn_pairs m hs -> gn_after_rig cx m hs qs c2 O2 cap2 out2 m1 ->
  gn_rig_ok cx m hs qs c2 O2 cap2 -> gn_run (gn_pre cx m) m1 mc A (length (lm_es m1)) 0%nat ->
  gx_xpre m hs ->
  pt_s c * pt_kc c mc + pt_v c * pt_mass mc <= pt_s c * pt_kc c m + pt_v c * pt_mass m.
Proof.
  intros c cx t m hs qs c2 O2 cap2 out2 m1 mc A HRI Hpairs Hafter Hrok Hrun HX.
  pose proof (gx_pf_all cx t m hs HRI Hpairs HX) as HPF.
  pose proof (gx_pq_facts cx m hs qs c2 O2 cap2 out2 m1 Hpairs Hafter Hrok) as HPQ.
  pose proof Hpairs as (Hlh & HPok & HRS).
  pose proof Hafter as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & A10 & A11 & A12 & A13).
  pose proof Hrok as (Hrr & Hlq & _ & Hfds).
  pose proof HRI as (_ & (Hl4 & _) & _).
  set (ps := combine (lm_es m) hs) in *.
  assert (Hlps : length ps = length qs) by (unfold ps; rewrite length_combine; lia).
  (* ---- relay_instance_gone: the entries and the drained slots ---- *)
  pose proof (pg_rig c _ (lm_mx m) ps qs (lm_c m) (lm_O m) (lm_cap m) c2 O2 cap2 Hrr HPF) as R.
  assert (EA : zsum (map (pg_EP c) (lm_es m1)) = zsum (map (fun pq => pg_EP c (fst (snd pq))) (combine ps qs))).
  { rewrite A3, map_map, (gx_sum_csnd (fun q => pg_EP c (fst q)) ps qs Hlps). reflexivity. }
  assert (EB : zsum (map (pg_EP c) (lm_es m)) = zsum (map (fun pq => pg_EP c (fst (fst pq))) (combine ps qs))).
  { rewrite (gx_sum_cfst (pg_EP c) (lm_es m) hs ltac:(lia)). fold ps.
    rewrite (gx_sum_cfst (fun p => pg_EP c (fst p)) ps qs Hlps). reflexivity. }
  (* ---- the slots: only the drained ones change ---- *)
  set (F := fun j => pg_SQ c (nth j (lm_hs m1) None) - pg_SQ c (nth j (lm_hs m) None)).
  assert (S1 : zsum (map (pg_SQ c) (lm_hs m1)) - zsum (map (pg_SP c) (lm_hs m)) =
               F 0%nat + F 1%nat + F 2%nat + F 3%nat).
  { rewrite (gx_sum4 (pg_SQ c) (lm_hs m1) A11), (gx_sum4 (pg_SP c) (lm_hs m) Hl4).
    assert (R0 : forall j, (j < 4)%nat -> pg_SQ c (nth j (lm_hs m) None) = pg_SP c (nth j (lm_hs m) None)).
    { intros j Hj. destruct (nth j (lm_hs m) None) as [h|] eqn:Eh; [|exact (pg_SQ_SP_none c)].
      destruct (gx_rinv_slot cx t m j h HRI Hj Eh) as (Hexp & _). exact (pg_SQ_SP c h Hexp). }
    unfold F. rewrite (R0 0%nat), (R0 1%nat), (R0 2%nat), (R0 3%nat) by lia. lia. }
  assert (S2 : F 0%nat + F 1%nat + F 2%nat + F 3%nat = zsum (map F (rig_slots ps))).
  { apply gx_sum_RS.
    - apply NoDup_ListNoDup. exact HRS.
    - intros j Hj. destruct (gx_rs_in j ps Hj) as (p & Hp & Heof & <-).
      rewrite Forall_forall in HPok. destruct (HPok p Hp Heof) as (Hj4 & _). exact Hj4.
    - intros j Hj Hn. unfold F. rewrite (A12 j Hj Hn). lia. }
  rewrite gx_rs_sum in S2.
  rewrite (gx_sum_cfst (fun p => if re_eof (fst p) =? 0 then F (snd (snd p)) else 0) ps qs Hlps) in S2.
  cbv beta in S2.
  assert (S3 : zsum (map (fun pq => if re_eof (fst (fst pq)) =? 0 then F (snd (snd (fst pq))) else 0)
                     (combine ps qs)) =
     zsum (map (fun pq => if re_eof (fst (fst pq)) =? 0 then pg_SQ c (Some (snd (snd pq))) else 0) (combine ps qs)) -
     zsum (map (fun pq => if re_eof (fst (fst pq)) =? 0 then pg_SQ c (Some (fst (snd (fst pq)))) else 0)
             (combine ps qs))).
  { rewrite <- gx_zsum_sub. apply (gx_sum_ext _ _ _ _ HPQ). intros [p q] Hpq. cbn [fst snd] in Hpq |- *.
    destruct (re_eof (fst p) =? 0) eqn:Eo; [|lia].
    apply Z.eqb_eq in Eo. destruct (Hpq Eo) as (_ & Hm & Hm1).
    unfold F. rewrite Hm, Hm1. lia. }
  assert (HRIG : zsum (map (pg_EP c) (lm_es m1)) + zsum (map (pg_SQ c) (lm_hs m1)) <=
                 zsum (map (pg_EP c) (lm_es m)) + zsum (map (pg_SP c) (lm_hs m))).
  { clearbody F. lia. }
  (* ---- the loop: each slot of mc against m1's ---- *)
  assert (Hnd : List.NoDup (map re_fd (lm_es m1))) by (rewrite A3; apply NoDup_ListNoDup; exact Hfds).
  destruct (gx_run _ m1 mc A _ _ Hrun Hnd) as (R1 & _ & _ & _ & _ & R6 & Hhist & Hcov).
  assert (Hlc : length (lm_hs mc) = 4%nat) by lia.
  assert (Hslot : forall k', (k' < 4)%nat ->
            pg_SP c (nth k' (lm_hs mc) None) <= pg_SQ c (nth k' (lm_hs m1) None)).
  { intros k' Hk'.
    destruct (Hhist k') as [L | (h & h'' & i0 & X1 & X2 & X3 & _)].
    - rewrite L.
      destruct (gx_rig_slot cx t m hs qs c2 O2 cap2 out2 m1 HRI Hpairs Hafter Hrok HX k' Hk')
        as [L2 | (e & h0 & h1 & cc & mx & no & cap & e1 & LB & i1 & Y1 & Y2 & Y3 & Y4 & Y5 & Y6)].
      + rewrite L2. destruct (nth k' (lm_hs m) None) as [h0|] eqn:Eh.
        * destruct (gx_rinv_slot cx t m k' h0 HRI Hk' Eh) as (Hexp & _). rewrite (pg_SQ_SP c h0 Hexp). lia.
        * rewrite pg_SQ_SP_none. lia.
      + rewrite Y2.
        assert (Hexp1 : hl_recs (hs_expected h1) = []).
        { apply (Hcov i1 k' h1); [lia | exact Y5 | exact Hk' | rewrite L; exact Y2 | symmetry; exact Y6]. }
        rewrite (pg_SQ_SP c h1 Hexp1). lia.
    - rewrite X2, X1. destruct (pg_touch c h h'' X3) as (T1 & T2). rewrite <- (pg_SQ_SP c h'' T2). exact T1. }
  assert (HLOOP : zsum (map (pg_SP c) (lm_hs mc)) <= zsum (map (pg_SQ c) (lm_hs m1))).
  { rewrite (gx_sum4 (pg_SP c) (lm_hs mc) Hlc), (gx_sum4 (pg_SQ c) (lm_hs m1) A11).
    pose proof (Hslot 0%nat ltac:(lia)). pose proof (Hslot 1%nat ltac:(lia)).
    pose proof (Hslot 2%nat ltac:(lia)). pose proof (Hslot 3%nat ltac:(lia)). lia. }
  rewrite (pg_split c mc), (pg_split c m), R1. lia.
Qed.

(* ================================================================== GN_RI_end's fr_POT *)
(* fr_POT kept over the gone operation: ReplyLS3oGn.v fr_OUT_gone_end's premises in its order, with
   fr_OUT OM cx t m ly S replaced by fr_POT cx t m; fr_LS3 B cx t m ly S and the block-permutation premise dropped
   (not used).  No extra hypothesis, no REQ5. *)
Lemma fr_POT_gone_end : forall cx t m (ly : alayout) (S : astate) hs qs c2 O2 cap2 out2 m1 mc A (lyx : alayout)
    (Sx : astate),
  fr_RINV cx t m -> gn_op cx t m ->
  Forall (fun e => ~ In (Z_to_bv 8 0) (re_U e) /\
    Forall (fun k => ~ In (Z_to_bv 8 0) (gestures_end_b_c.key_text k) /\
      14 <= Z.of_nat (length (gestures_end_b_c.key_text k)) <= APARTIAL) (re_keys e)) (lm_es m) ->
  (* REQ1 *) 0 <= lm_cap m ->
  (* REQ2 *)
  Forall (fun e => Z.of_nat (length (re_U e)) <= APARTIAL /\ (re_cap e = 0 \/ re_cap e = 8192 \/ re_cap e = 16384) /\
    ((re_hp e = 0 /\ re_keys e = []) \/ (re_hp e <> 0 /\ 8 * re_nheld e <= re_kh e /\ 8 <= re_kh e))) (lm_es m) ->
  (* REQ3 *)
  Forall (fun o => match o with
    | Some h0 => ((hl_recs (hs_pending h0) = [] /\ hs_off h0 = 0) \/
                  (exists r rs, hl_recs (hs_pending h0) = r :: rs /\ 0 <= hs_off h0 < Z.of_nat (length (snd r)))) /\
                 Forall (fun r => (1 <= length (snd r))%nat) (hl_recs (hs_pending h0))
    | None => True end) (lm_hs m) ->
  fr_POT cx t m ->
  gn_pairs m hs -> gn_after_rig cx m hs qs c2 O2 cap2 out2 m1 ->
  gn_rig_ok cx m hs qs c2 O2 cap2 ->
  gn_run (gn_pre cx m) m1 mc A (length (lm_es m1)) 0%nat ->
  fr_POT cx (t + 1) mc.
Proof.
  intros cx t m ly S hs qs c2 O2 cap2 out2 m1 mc A lyx Sx HRI Hop HE Hcap HE6 HS6 HPOT Hpairs Hafter Hrok Hrun.
  pose proof (gx_xpre_of6 cx t m hs Hop HE Hcap HE6 HS6 Hpairs) as HX.
  apply (fr_POT_step cx t (t + 1) m mc); [intros c | exact HPOT].
  pose proof (pg_core c cx t m hs qs c2 O2 cap2 out2 m1 mc A HRI Hpairs Hafter Hrok Hrun HX) as H.
  pose proof (pt_wm_nonneg c (t + 1 - t) ltac:(lia)) as W.
  lia.
Qed.
End pgn.

(* ================================================================== the LS halves at B's v3 instance *)
Section lsi.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.

(* fr_CAP's gone rule: lib/B/ReplyB3LScap.v fr_CAP_gone_end's statement (:599-618) at any fr_CAP, at the instance's
   call room *)
Definition GN_CAP_end (B : asyms) (OM : Z) (fr_CAP : lfcx -> Z -> lmod -> alayout -> astate -> Prop) : Prop :=
  forall cx t m ly S hs qs c2 O2 cap2 out2 m1 mc A (lyx : alayout) (Sx : astate),
  fr_RINV cx t m -> gn_op cx t m ->
  Forall (fun e => ~ In (Z_to_bv 8 0) (re_U e) /\
    Forall (fun k => ~ In (Z_to_bv 8 0) (gestures_end_b_c.key_text k) /\
      14 <= Z.of_nat (length (gestures_end_b_c.key_text k)) <= APARTIAL) (re_keys e)) (lm_es m) ->
  0 <= lm_cap m ->
  Forall (fun e => Z.of_nat (length (re_U e)) <= APARTIAL /\ (re_cap e = 0 \/ re_cap e = 8192 \/ re_cap e = 16384) /\
    ((re_hp e = 0 /\ re_keys e = []) \/ (re_hp e <> 0 /\ 8 * re_nheld e <= re_kh e /\ 8 <= re_kh e))) (lm_es m) ->
  Forall (fun o => match o with
    | Some h0 => ((hl_recs (hs_pending h0) = [] /\ hs_off h0 = 0) \/
                  (exists r rs, hl_recs (hs_pending h0) = r :: rs /\ 0 <= hs_off h0 < Z.of_nat (length (snd r)))) /\
                 Forall (fun r => (1 <= length (snd r))%nat) (hl_recs (hs_pending h0))
    | None => True end) (lm_hs m) ->
  fr_LS3 B YCfn_cf.CALL_ROOM_B cx t m ly S -> fr_OUT OM cx t m ly S -> fr_CAP cx t m ly S ->
  gn_pairs m hs -> gn_after_rig cx m hs qs c2 O2 cap2 out2 m1 ->
  gn_rig_ok cx m hs qs c2 O2 cap2 ->
  gn_run (gn_pre cx m) m1 mc A (length (lm_es m1)) 0%nat ->
  (forall rest, Permutation (ablocks B ly S) (input_blks cx ++ model_blks m ++ rest) ->
     Permutation (ablocks B lyx Sx) (input_blks cx ++ model_blks mc ++ rest)) ->
  fr_CAP cx (t + 1) mc lyx Sx.

(* at the instance's fr_CAP (lib/B/ReplyB3LScap.v :113) the slot rule is fr_CAP_gone_end *)
Lemma GN_CAP_end_cap : forall (B : asyms) (OM : Z), OUT_MAX4 <= OM -> GN_CAP_end B OM ReplyB3LScap.fr_CAP.
Proof.
  intros B OM HOM. unfold GN_CAP_end. intros.
  eapply ReplyB3LScap.fr_CAP_gone_end; eassumption.
Qed.

(* the step's room conjunct: gx6_step_room_c at the instance's fr_LS3c, every meter (the row's own mo_le premise P13
   is gx6_step_room_c's, which is generic in the meter since KF-COUNT B) *)
Lemma GN_RI_step_room_lsi : forall (B : asyms) (MT : ameter_ops) (OM : Z)
    (fr_CAP : lfcx -> Z -> lmod -> alayout -> astate -> Prop),
  RG_step_room B MT (LSI B OM fr_CAP) fr_RINV fr_MMAX.
Proof.
  intros B MT OM fr_CAP. unfold ReplyRINVB_gone.RG.GN_RI_step_room.
  intros cx t m ly S hs qs c2 O2 cap2 out2 m1 mc A i k h lyx Sx cst q
    P1 P2 P3 P4 P5 P6 P7 P8 P9 P10 P11 _ P13 _ P15 P16 P17 P18 P19 P20.
  destruct (ReplyLS3B_inst.lsi_parts B OM fr_CAP cx t m ly S P7) as (_ & H3c & _).
  exact (gx6_step_room_c B YCfn_cf.CALL_ROOM_B (Z.le_refl _) cx t m ly S hs qs c2 O2 cap2 out2 m1 mc A i k h lyx Sx
    cst P1 P2 P3 P4 P5 P6 H3c P8 P9 P10 P11 P13 P15 P16 P17 P18 P19 P20).
Qed.

(* the end's LS conjunct at the instance, conjunct by conjunct, every meter (the row's mo_le premise P14 goes to
   gx6_end_LS3c and fr_ENT_gone_end, generic in the meter); fr_CAP by its slot rule *)
Lemma GN_RI_end_ls_lsi : forall (B : asyms) (MT : ameter_ops) (OM : Z)
    (fr_CAP : lfcx -> Z -> lmod -> alayout -> astate -> Prop),
  OUT_MAX4 <= OM -> GN_CAP_end B OM fr_CAP ->
  RG_end_ls B MT (LSI B OM fr_CAP) fr_RINV.
Proof.
  intros B MT OM fr_CAP HOM HCAP. unfold ReplyRINVB_gone.RG.GN_RI_end_ls.
  intros cx t m ly S hs qs c2 O2 cap2 out2 m1 mc A lyx Sx cst q
    P1 P2 P3 _ P5 P6 P7 P8 P9 P10 P11 P12 _ P14 _ P16.
  destruct (ReplyLS3B_inst.lsi_parts B OM fr_CAP cx t m ly S P8) as (HP & H3c & H3 & HO & HE & HC).
  pose proof (gxh_req5 cx t m hs qs c2 O2 cap2 out2 m1 mc A _ _ P1 P9 P10 P11 P12) as HR5.
  unfold ReplyLS3B_inst.LSI, ReplyB3LS3p.fr_LS3cp.
  refine (conj (conj _ _) (conj _ (conj _ _))).
  - exact (gx6_end_LS3c B YCfn_cf.CALL_ROOM_B cx t m ly S hs qs c2 O2 cap2 out2 m1 mc A lyx Sx cst P1 P2 P3 P5 P6 P7
      H3c P9 P10 P11 P12 P14 P16 HR5).
  - exact (fr_POT_gone_end cx t m ly S hs qs c2 O2 cap2 out2 m1 mc A lyx Sx P1 P2 P3 P5 P6 P7 (proj2 HP) P9 P10 P11
      P12).
  - eapply ReplyB3LS3oGn.fr_OUT_gone_end; eassumption.
  - exact (ReplyB3LS3e.fr_ENT_gone_end B YCfn_cf.CALL_ROOM_B cx t m ly S hs qs c2 O2 cap2 out2 m1 mc A lyx Sx cst
      P1 P2 P3 P5 P6 P7 H3 HE P9 P10 P11 P12 P14 P16 HR5).
  - exact (HCAP cx t m ly S hs qs c2 O2 cap2 out2 m1 mc A lyx Sx P1 P2 P3 P5 P6 P7 H3 HO HC P9 P10 P11 P12 P16).
Qed.

(* ================================================================== the two rows at the instance *)
(* GN_RI_step at every meter MT: its RINV half (RG.GN_RI_step_ri_holds), its room conjunct (above) and its two meter
   conjuncts (premises: the instance has no count clause yet) *)
Lemma GN_RI_step_lsi : forall (B : asyms) (MT : ameter_ops) (OM : Z)
    (fr_CAP : lfcx -> Z -> lmod -> alayout -> astate -> Prop),
  ReplyRINVB_gone.RG.GN_RI_step_cnl_meter B MT (LSI B OM fr_CAP) fr_RINV ->
  ReplyRINVB_gone.RG.GN_RI_step_cshe_meter B MT (LSI B OM fr_CAP) fr_RINV ->
  W_LLVMFuzzerTestOneInput_gone_base.GN_RI_step B MT (LSI B OM fr_CAP) fr_RINV fr_MMAX.
Proof.
  intros B MT OM fr_CAP HCM HSM.
  apply ReplyRINVB_gone.RG.GN_RI_step_of_parts.
  - apply ReplyRINVB_gone.RG.GN_RI_step_ri_holds.
  - exact (ReplyRINVB_gone.RG.GN_RI_step_ls_of_room_mt B MT (LSI B OM fr_CAP) fr_RINV fr_MMAX
      (GN_RI_step_room_lsi B MT OM fr_CAP) HCM HSM).
Qed.
(* at ameter_triv both meter conjuncts are True (RG.GN_RI_step_cnl_meter_triv / RG.GN_RI_step_cshe_meter_triv) *)
Lemma GN_RI_step_lsi_triv : forall (B : asyms) (OM : Z) (fr_CAP : lfcx -> Z -> lmod -> alayout -> astate -> Prop),
  W_LLVMFuzzerTestOneInput_gone_base.GN_RI_step B ameter_triv (LSI B OM fr_CAP) fr_RINV fr_MMAX.
Proof.
  intros B OM fr_CAP. apply GN_RI_step_lsi.
  - apply ReplyRINVB_gone.RG.GN_RI_step_cnl_meter_triv.
  - apply ReplyRINVB_gone.RG.GN_RI_step_cshe_meter_triv.
Qed.
(* GN_RI_end at every meter MT: its RINV half (RG.GN_RI_end_ri_holds) and its LS half (above) *)
Lemma GN_RI_end_lsi : forall (B : asyms) (MT : ameter_ops) (OM : Z)
    (fr_CAP : lfcx -> Z -> lmod -> alayout -> astate -> Prop),
  OUT_MAX4 <= OM -> GN_CAP_end B OM fr_CAP ->
  W_LLVMFuzzerTestOneInput_gone_base.GN_RI_end B MT (LSI B OM fr_CAP) fr_RINV.
Proof.
  intros B MT OM fr_CAP HOM HCAP.
  apply ReplyRINVB_gone.RG.GN_RI_end_of_parts.
  - apply ReplyRINVB_gone.RG.GN_RI_end_ri_holds.
  - exact (GN_RI_end_ls_lsi B MT OM fr_CAP HOM HCAP).
Qed.
(* at the instance's fr_CAP (lib/B/ReplyB3LScap.v) the slot rule is proved, so the end row needs only OUT_MAX4 <= OM *)
Lemma GN_RI_end_lsi_cap : forall (B : asyms) (MT : ameter_ops) (OM : Z), OUT_MAX4 <= OM ->
  W_LLVMFuzzerTestOneInput_gone_base.GN_RI_end B MT (LSI B OM ReplyB3LScap.fr_CAP) fr_RINV.
Proof.
  intros B MT OM HOM. exact (GN_RI_end_lsi B MT OM ReplyB3LScap.fr_CAP HOM (GN_CAP_end_cap B OM HOM)).
Qed.
End lsi.

(* ================================================================== the two rows at the counting meter MT_sec *)
(* The instance with its count clause (lib/B/ReplyLSBSec.v :1586-1600): ReplyLS3B_inst.LSI with its last slot
   CAP /\ fr_SEC nsec KMAX KC, at the meter ReplyKfMeterB.MT_sec nsec KMAX.  ReplyLSBSec.v fr_SEC_GN_RI_step_cnl_meter /
   fr_SEC_GN_RI_step_cshe_meter give the step's two meter conjuncts from fr_LS3c and fr_SEC (sec_lsi_parts), so the
   step has no meter premise; the end keeps fr_SEC by fr_SEC_gone_end_a and the other four slots by GN_RI_end_ls_lsi
   at CAP. *)
Section lsi_sec.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.

(* sec_lsi_parts at an LSI hypothesis *)
Lemma sec_lsi_of : forall (B : asyms) (OM : Z) (CAP : lfcx -> Z -> lmod -> alayout -> astate -> Prop)
    (nsec : astate -> Z) (KMAX KC : Z) cx t m ly S,
  LSI B OM (fun cx t m ly S => CAP cx t m ly S /\ ReplyLSBSec.fr_SEC nsec KMAX KC cx t m ly S) cx t m ly S ->
  fr_LS3c B YCfn_cf.CALL_ROOM_B cx t m ly S /\ ReplyLSBSec.fr_SEC nsec KMAX KC cx t m ly S.
Proof.
  intros B OM CAP nsec KMAX KC cx t m ly S H.
  exact (ReplyLSBSec.sec_lsi_parts B OM CAP nsec KMAX KC cx t m ly S H).
Qed.

(* GN_RI_step at MT_sec, no meter premise.  Arguments in the order of GN_RI_step_lsi (B MT OM fr_CAP): B, the
   meter's nsec KMAX with fr_SEC's KC, OM, the slot CAP *)
Lemma GN_RI_step_lsi_sec : forall (B : asyms) (nsec : astate -> Z) (KMAX KC : Z) (OM : Z)
    (CAP : lfcx -> Z -> lmod -> alayout -> astate -> Prop), 240 <= KC ->
  W_LLVMFuzzerTestOneInput_gone_base.GN_RI_step B (ReplyKfMeterB.MT_sec nsec KMAX)
    (LSI B OM (fun cx t m ly S => CAP cx t m ly S /\ ReplyLSBSec.fr_SEC nsec KMAX KC cx t m ly S)) fr_RINV fr_MMAX.
Proof.
  intros B nsec KMAX KC OM CAP HKC.
  apply GN_RI_step_lsi.
  - exact (ReplyLSBSec.fr_SEC_GN_RI_step_cnl_meter nsec KMAX KC HKC B _ (sec_lsi_of B OM CAP nsec KMAX KC)).
  - exact (ReplyLSBSec.fr_SEC_GN_RI_step_cshe_meter nsec KMAX KC HKC B _ (sec_lsi_of B OM CAP nsec KMAX KC)).
Qed.

(* GN_RI_end's LS half at MT_sec: LSI's four slots at CAP (GN_RI_end_ls_lsi) and fr_SEC (fr_SEC_gone_end_a) *)
Lemma GN_RI_end_ls_lsi_sec : forall (B : asyms) (nsec : astate -> Z) (KMAX KC : Z) (OM : Z)
    (CAP : lfcx -> Z -> lmod -> alayout -> astate -> Prop), 240 <= KC -> OUT_MAX4 <= OM -> GN_CAP_end B OM CAP ->
  RG_end_ls B (ReplyKfMeterB.MT_sec nsec KMAX) (LSI B OM (fun cx t m ly S => CAP cx t m ly S /\ ReplyLSBSec.fr_SEC nsec KMAX KC cx t m ly S)) fr_RINV.
Proof.
  intros B nsec KMAX KC OM CAP HKC HOM HCAP. unfold ReplyRINVB_gone.RG.GN_RI_end_ls.
  intros cx t m ly S hs qs c2 O2 cap2 out2 m1 mc A lyx Sx cst q
    P1 P2 P3 P4 P5 P6 P7 P8 P9 P10 P11 P12 P13 P14 P15 P16.
  destruct (sec_lsi_of B OM CAP nsec KMAX KC cx t m ly S P8) as (H3c & HS).
  destruct P8 as (HP & HO & HE & HC & _).
  destruct (GN_RI_end_ls_lsi B (ReplyKfMeterB.MT_sec nsec KMAX) OM CAP HOM HCAP cx t m ly S hs qs c2 O2 cap2 out2 m1
              mc A lyx Sx cst q P1 P2 P3 P4 P5 P6 P7 (conj HP (conj HO (conj HE HC))) P9 P10 P11 P12 P13 P14 P15 P16)
    as (HP' & HO' & HE' & HC').
  unfold ReplyLS3B_inst.LSI. cbv beta.
  refine (conj HP' (conj HO' (conj HE' (conj HC' _)))).
  exact (ReplyLSBSec.fr_SEC_gone_end_a nsec KMAX KC HKC B cx t m ly S hs qs c2 O2 cap2 out2 m1 mc A lyx Sx cst q
    H3c P1 P2 P3 P5 P6 P7 P9 P10 P11 P12 P13 P14 P15 HS).
Qed.

(* GN_RI_end at MT_sec: its RINV half and its LS half (above) *)
Lemma GN_RI_end_lsi_sec : forall (B : asyms) (nsec : astate -> Z) (KMAX KC : Z) (OM : Z)
    (CAP : lfcx -> Z -> lmod -> alayout -> astate -> Prop), 240 <= KC -> OUT_MAX4 <= OM -> GN_CAP_end B OM CAP ->
  W_LLVMFuzzerTestOneInput_gone_base.GN_RI_end B (ReplyKfMeterB.MT_sec nsec KMAX) (LSI B OM (fun cx t m ly S => CAP cx t m ly S /\ ReplyLSBSec.fr_SEC nsec KMAX KC cx t m ly S)) fr_RINV.
Proof.
  intros B nsec KMAX KC OM CAP HKC HOM HCAP.
  apply ReplyRINVB_gone.RG.GN_RI_end_of_parts.
  - apply ReplyRINVB_gone.RG.GN_RI_end_ri_holds.
  - exact (GN_RI_end_ls_lsi_sec B nsec KMAX KC OM CAP HKC HOM HCAP).
Qed.
(* at CAP := ReplyB3LScap.fr_CAP the slot rule is proved (GN_CAP_end_cap) *)
Lemma GN_RI_end_lsi_sec_cap : forall (B : asyms) (nsec : astate -> Z) (KMAX KC : Z) (OM : Z),
  240 <= KC -> OUT_MAX4 <= OM ->
  W_LLVMFuzzerTestOneInput_gone_base.GN_RI_end B (ReplyKfMeterB.MT_sec nsec KMAX)
    (LSI B OM (fun cx t m ly S => ReplyB3LScap.fr_CAP cx t m ly S /\ ReplyLSBSec.fr_SEC nsec KMAX KC cx t m ly S))
    fr_RINV.
Proof.
  intros B nsec KMAX KC OM HKC HOM.
  exact (GN_RI_end_lsi_sec B nsec KMAX KC OM ReplyB3LScap.fr_CAP HKC HOM (GN_CAP_end_cap B OM HOM)).
Qed.
End lsi_sec.

(* ================================================================== what B's top needs (top_x :864-865) *)
(* k3's two rows, the hypotheses GN_RI_step_x / GN_RI_end_x of lib/B/W_LLVMFuzzerTestOneInput_top_x.v :892-893
   verbatim, at top_x's TfibB, RINV := ReplyRINVB.fr_RINV and MMAX := CfParamsReply.fr_MMAX, the counting meter
   MT := ReplyKfMeterB.MT_sec nsec KMAX and the instance with its count clause
   LSx := ReplyLS3B_inst.LSI TfibB ReplyLSBo.OUT_MAX4 (fun .. => ReplyB3LScap.fr_CAP .. /\ ReplyLSBSec.fr_SEC nsec KMAX KC ..)
   (lib/B/ReplyLSBSec.v :1586-1590), for every rc fx and 240 <= KC: the forms k3 plugs. *)
Lemma GN_RI_step_x_sec : forall (rc : YM05.RunCeil) (fx : YK11.FPState) (nsec : astate -> Z) (KMAX KC : Z),
  240 <= KC ->
  W_LLVMFuzzerTestOneInput_gone_base.GN_RI_step YD2l.TfibB (ReplyKfMeterB.MT_sec nsec KMAX)
    (ReplyLS3B_inst.LSI YD2l.TfibB ReplyLSBo.OUT_MAX4
       (fun cx t m ly S => ReplyB3LScap.fr_CAP cx t m ly S /\ ReplyLSBSec.fr_SEC nsec KMAX KC cx t m ly S))
    ReplyRINVB.fr_RINV CfParamsReply.fr_MMAX.
Proof.
  intros rc fx nsec KMAX KC HKC.
  exact (GN_RI_step_lsi_sec YD2l.TfibB nsec KMAX KC ReplyLSBo.OUT_MAX4 ReplyB3LScap.fr_CAP HKC).
Qed.
Lemma GN_RI_end_x_sec : forall (rc : YM05.RunCeil) (fx : YK11.FPState) (nsec : astate -> Z) (KMAX KC : Z),
  240 <= KC ->
  W_LLVMFuzzerTestOneInput_gone_base.GN_RI_end YD2l.TfibB (ReplyKfMeterB.MT_sec nsec KMAX)
    (ReplyLS3B_inst.LSI YD2l.TfibB ReplyLSBo.OUT_MAX4
       (fun cx t m ly S => ReplyB3LScap.fr_CAP cx t m ly S /\ ReplyLSBSec.fr_SEC nsec KMAX KC cx t m ly S))
    ReplyRINVB.fr_RINV.
Proof.
  intros rc fx nsec KMAX KC HKC.
  exact (GN_RI_end_lsi_sec_cap YD2l.TfibB nsec KMAX KC ReplyLSBo.OUT_MAX4 HKC (Z.le_refl _)).
Qed.

(* the same two rows at MT := ameter_triv with LSx := LSI TfibB OUT_MAX4 ReplyB3LScap.fr_CAP, from nothing *)
Section k3.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Check (GN_RI_step_lsi_triv YD2l.TfibB OUT_MAX4 ReplyB3LScap.fr_CAP :
  W_LLVMFuzzerTestOneInput_gone_base.GN_RI_step YD2l.TfibB ameter_triv
    (ReplyLS3B_inst.LSI YD2l.TfibB OUT_MAX4 ReplyB3LScap.fr_CAP) ReplyRINVB.fr_RINV CfParamsReply.fr_MMAX).
Check (GN_RI_end_lsi_cap YD2l.TfibB ameter_triv OUT_MAX4 (Z.le_refl _) :
  W_LLVMFuzzerTestOneInput_gone_base.GN_RI_end YD2l.TfibB ameter_triv
    (ReplyLS3B_inst.LSI YD2l.TfibB OUT_MAX4 ReplyB3LScap.fr_CAP) ReplyRINVB.fr_RINV).
End k3.

Print Assumptions gxh_req5.
Print Assumptions fr_POT_gone_end.
Print Assumptions GN_CAP_end_cap.
Print Assumptions GN_RI_step_room_lsi.
Print Assumptions GN_RI_end_ls_lsi.
Print Assumptions GN_RI_step_lsi.
Print Assumptions GN_RI_step_lsi_triv.
Print Assumptions GN_RI_end_lsi.
Print Assumptions GN_RI_end_lsi_cap.
Print Assumptions GN_RI_step_lsi_sec.
Print Assumptions GN_RI_end_ls_lsi_sec.
Print Assumptions GN_RI_end_lsi_sec.
Print Assumptions GN_RI_end_lsi_sec_cap.
Print Assumptions GN_RI_step_x_sec.
Print Assumptions GN_RI_end_x_sec.
