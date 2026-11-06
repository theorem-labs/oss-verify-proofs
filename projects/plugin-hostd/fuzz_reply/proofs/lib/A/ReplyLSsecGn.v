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
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_reply/lib/A/ReplyRINV_gone.v, with its module paths and module names changed; 392 of its 510 lines of code are new or changed and 2805 lines of the source are left out. *)
(* fr_SEC over the gone operation (ReplyLSsec.v's clause): top_x's LS_gone_rig meter conjunct (gone_base GN_LS_rig),
   GN_RI_step's two meter conjuncts and GN_RI_end's fr_SEC, at gone_base's KF-COUNT text (the binder q, gn_runc,
   gn_cst).  proves no function (kind: invariant lemma).
   - relay_instance_gone's requests: lane B's ReplyKfTrRig.kf_rig (KC_rig = 180) at gn_rigc's own pairs, its premises
     from gone's REQ2 / REQ3 (gx_pf_all), paid by the open pairs' bytes (sec_osum_in); LS_gone_rig has no re_cap, so
     there ReplyLSsec.sec_rig45 (240).  gn_rigc's pairs and the rule's give the same open sources (sec_osum_same: the
     slots' fds are distinct, RI_fds_holds).
   - the loop's requests q: one check_no_loss per call, at most 15 at a drained slot and 0 at an untouched one (its
     expected list is empty), so q plus every slot's remaining charge is the slots' charge after the rig
     (sec_runc), at most 4 * 15 (sec_F_m1).
   - the bytes: the rig consumes every open pair's pending stream and partial line and leaves dr_fin's partial line
     (sec_ub_gone, ReplyLS3oGn.v fr_OUT_gone_end's accounting with sec_str in place of slot_pend). *)
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
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import AB1v.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YI16 YE00 YE01.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import AE2k.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YC5d.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import ACfn.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib Require Import ZTraceSpec.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import
W_syms W_listing W_place W_tbl W_kit W_pl W_img W_journal.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import HarnessRep RelayRep.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import W_rep W_contract W_sites W_frame W_op_add.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import W_LLVMFuzzerTestOneInput_cut.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import ReplyLS.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import ReplyRINV.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YCbp.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import CheckRep.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import RelayKeys RelayModel ListRep.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require
  drain_b_c gestures_end_b_c relay_remove_b_c SlotReads SlotInv relay_instance_gone_b_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require ACfn_cf CfParamsReply.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import ReplyLS3 ReplyLSDrain3 ReplyLSRemove3.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import ReplyLS3Arms ReplyLS3c.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import ReplyLS3o ReplyLS3p ReplyLS3oGn.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import W_LLVMFuzzerTestOneInput_gone_base.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import
  ReplyLS3cTopxGone ReplyLS3cTopxGoneF ReplyLS3cTopxRig.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import ReplyLS3Peak ReplyRINV_a12.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import ReplyKfMeter ReplyKfNsec.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require ReplyKfTrRig.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import ReplyLSsec.
Import ListNotations.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Local Notation zsum l := (fold_right Z.add 0 l).
Local Notation osum := ReplyKfTrRig.osum.
Local Notation kf_in := ReplyKfTrRig.kf_in.
Local Notation kf_tail := ReplyKfTrRig.kf_tail.

(* ================================================================== the open pairs' bytes *)
Lemma sec_osum_nonneg : forall (f : rentry -> hsrc -> Z) ps, (forall e h, 0 <= f e h) -> 0 <= osum f ps.
Proof.
  intros f ps Hf. induction ps as [|[e hj] ps IH].
  - unfold ReplyKfTrRig.osum. cbn [map fold_right]. lia.
  - rewrite ReplyKfTrRig.osum_cons. pose proof (Hf e (fst hj)). destruct (re_eof e =? 0); lia.
Qed.
Lemma sec_osum_split : forall ps, osum kf_in ps = osum (fun e _ => pt_eu e) ps + zsum (map pk_gp ps).
Proof.
  induction ps as [|[e hj] ps IH]; [reflexivity|].
  rewrite !ReplyKfTrRig.osum_cons. cbn [map fold_right]. rewrite IH.
  change (pk_gp (e, hj)) with (if re_eof e =? 0 then Z.of_nat (length (pending_stream (fst hj))) else 0).
  unfold ReplyKfTrRig.kf_in, pt_eu. destruct (re_eof e =? 0); lia.
Qed.
Lemma sec_osum_U : forall es (hs : list (hsrc * nat)), osum (fun e _ => pt_eu e) (combine es hs) <= zsum (map pt_eu es).
Proof.
  induction es as [|e es IH]; intros [|hj hs]; cbn [combine map fold_right].
  - unfold ReplyKfTrRig.osum. cbn [map fold_right]. lia.
  - unfold ReplyKfTrRig.osum. cbn [map fold_right]. lia.
  - unfold ReplyKfTrRig.osum. cbn [map fold_right]. pose proof (pt_eu_nonneg e).
    pose proof (zsum_map_nonneg pt_eu es pt_eu_nonneg). lia.
  - rewrite ReplyKfTrRig.osum_cons. pose proof (pt_eu_nonneg e). specialize (IH hs). destruct (re_eof e =? 0); lia.
Qed.
Lemma sec_gp_slots : forall m ps,
  Forall (fun p => re_eof (fst p) = 0 -> gn_pair_ok m (fst p) (snd p)) ps ->
  zsum (map pk_gp ps) = zsum (map (fun i => sec_str (nth i (lm_hs m) None)) (rig_slots ps)).
Proof.
  intros m. induction ps as [|[e hj] ps IH]; intros HF; [reflexivity|].
  apply Forall_cons_iff in HF as [H1 HF].
  rewrite pk_slots_cons, map_app, zsum_app. cbn [map fold_right]. cbn [fst snd] in H1.
  change (pk_gp (e, hj)) with (if re_eof e =? 0 then Z.of_nat (length (pending_stream (fst hj))) else 0).
  rewrite <- (IH HF).
  destruct (Z.eqb_spec (re_eof e) 0) as [Eo|Eo]; cbn [map fold_right].
  - destruct (H1 Eo) as (_ & Hn & _). rewrite Hn.
    change (sec_str (Some (fst hj))) with (Z.of_nat (length (pending_stream (fst hj)))). lia.
  - lia.
Qed.
Lemma sec_gp_le : forall m ps, length (lm_hs m) = 4%nat ->
  Forall (fun p => re_eof (fst p) = 0 -> gn_pair_ok m (fst p) (snd p)) ps -> List.NoDup (rig_slots ps) ->
  zsum (map pk_gp ps) <= zsum (map sec_str (lm_hs m)).
Proof.
  intros m ps Hl HF HND. rewrite (sec_gp_slots m ps HF).
  rewrite <- (pk_zsum_seq sec_str (lm_hs m)).
  apply pk_zsum_nodup_le; [intros i; apply sec_str_nonneg | exact HND |].
  intros i Hi. unfold rig_slots in Hi. apply in_concat in Hi as (l & Hl' & Hil).
  apply in_map_iff in Hl' as (p & <- & Hp).
  destruct (Z.eqb_spec (re_eof (fst p)) 0) as [Eo|Eo]; [|destruct Hil].
  destruct Hil as [<- | []].
  destruct (proj1 (Forall_forall _ _) HF p Hp Eo) as (H4 & _).
  apply in_seq. rewrite Hl. lia.
Qed.
(* the open pairs' bytes are within sec_ub *)
Lemma sec_osum_in : forall m hs, length (lm_hs m) = 4%nat -> gn_pairs m hs ->
  osum kf_in (combine (lm_es m) hs) <= sec_ub m.
Proof.
  intros m hs Hl (_ & HF & HND). rewrite sec_osum_split.
  pose proof (sec_osum_U (lm_es m) hs). pose proof (sec_gp_le m _ Hl HF (proj1 (NoDup_ListNoDup _) HND)).
  unfold sec_ub. lia.
Qed.
Section same.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
(* the open entries' sources are the same at any two pairings (the open slots' fds are distinct) *)
Lemma sec_osum_same : forall cx t m (f : rentry -> hsrc -> Z) hs hs',
  fr_RINV cx t m -> gn_pairs m hs -> gn_pairs m hs' ->
  osum f (combine (lm_es m) hs) = osum f (combine (lm_es m) hs').
Proof.
  intros cx t m f hs hs' HRI (Hl & HF & _) (Hl' & HF' & _).
  assert (G : forall es (hs1 hs1' : list (hsrc * nat)), length hs1 = length es -> length hs1' = length es ->
    Forall (fun p => re_eof (fst p) = 0 -> gn_pair_ok m (fst p) (snd p)) (combine es hs1) ->
    Forall (fun p => re_eof (fst p) = 0 -> gn_pair_ok m (fst p) (snd p)) (combine es hs1') ->
    osum f (combine es hs1) = osum f (combine es hs1')).
  { induction es as [|e es IH]; intros [|hj hs1] [|hj' hs1'] L L' F F'; cbn [length] in L, L'; try lia.
    cbn [combine] in F, F' |- *. apply Forall_cons_iff in F as [F0 F]. apply Forall_cons_iff in F' as [F0' F'].
    rewrite !ReplyKfTrRig.osum_cons. rewrite (IH hs1 hs1' ltac:(lia) ltac:(lia) F F').
    destruct (Z.eqb_spec (re_eof e) 0) as [Eo|Eo]; [|reflexivity].
    cbn [fst snd] in F0, F0'. destruct (F0 Eo) as (Hj & Hn & Hfd & _). destruct (F0' Eo) as (Hj' & Hn' & Hfd' & _).
    assert (Ej : snd hj = snd hj').
    { destruct (Nat.eq_dec (snd hj) (snd hj')) as [E|E]; [exact E|].
      exfalso. exact (RI_fds_holds cx t m (snd hj) (snd hj') (fst hj) (fst hj') HRI Hj Hj' E Hn Hn'
                        ltac:(congruence)). }
    rewrite Ej in Hn. rewrite Hn in Hn'. injection Hn' as E. rewrite E. reflexivity. }
  exact (G (lm_es m) hs hs' Hl Hl' HF HF').
Qed.
End same.

(* the open pairs' facts give lane B's drain premises *)
Lemma sec_pf_pre : forall p, gx_pf p -> ReplyKfTrRig.kf_dr_pre (fst p) (fst (snd p)).
Proof.
  intros [e [h j]] (_ & _ & Hoff & Hsk & HskU & Hsk01 & (Hce & HU & _) & _). cbn [fst snd] in *.
  refine (conj Hoff (conj (sec_hsW e h Hsk HskU Hsk01 HU) (conj Hce _))). unfold APARTIAL in HU. lia.
Qed.

(* ================================================================== the loop's check_no_loss charges *)
Section gn.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable nsec : astate -> Z.
Variable KMAX : Z.
Variable KC : Z.
Local Notation MT := (MT_sec nsec KMAX).

Definition sec_c (o : option hsrc) : Z :=
  match o with Some h => cnl_cost MT (hs_expected h) (hs_held h) | None => 0 end.
Definition sec_F (hs : list (option hsrc)) : Z :=
  sec_c (nth 0 hs None) + sec_c (nth 1 hs None) + sec_c (nth 2 hs None) + sec_c (nth 3 hs None).

Lemma sec_c_nonneg : forall o, 0 <= sec_c o.
Proof. intros [h|]; cbn [sec_c]; [apply sec_cnl_nonneg | lia]. Qed.
Lemma sec_F_nonneg : forall hs, 0 <= sec_F hs.
Proof.
  intros hs. unfold sec_F. pose proof (sec_c_nonneg (nth 0 hs None)). pose proof (sec_c_nonneg (nth 1 hs None)).
  pose proof (sec_c_nonneg (nth 2 hs None)). pose proof (sec_c_nonneg (nth 3 hs None)). lia.
Qed.
Lemma sec_c_empty : forall h, hl_recs (hs_expected h) = [] -> sec_c (Some h) = 0.
Proof. intros h E. cbn [sec_c]. unfold cnl_cost. rewrite E. reflexivity. Qed.
Lemma sec_F_ge : forall hs k h, (k < 4)%nat -> nth k hs None = Some h -> sec_c (Some h) <= sec_F hs.
Proof.
  intros hs k h Hk Hh. unfold sec_F. pose proof (sec_c_nonneg (nth 0 hs None)).
  pose proof (sec_c_nonneg (nth 1 hs None)). pose proof (sec_c_nonneg (nth 2 hs None)).
  pose proof (sec_c_nonneg (nth 3 hs None)).
  destruct k as [|[|[|[|k]]]]; [| | | | lia]; rewrite <- Hh; lia.
Qed.
Lemma sec_nth_lt : forall (l : list (option hsrc)) k h, nth k l None = Some h -> (k < length l)%nat.
Proof.
  intros l k h E. destruct (Nat.lt_ge_cases k (length l)) as [L|L]; [exact L|].
  rewrite nth_overflow in E by exact L. discriminate.
Qed.
Lemma sec_F_set : forall hs k x, (k < 4)%nat -> (k < length hs)%nat ->
  sec_F (gn_setn k x hs) = sec_F hs - sec_c (nth k hs None) + sec_c x.
Proof.
  intros hs k x Hk Hl. unfold sec_F.
  destruct k as [|[|[|[|k]]]]; [| | | | lia];
    rewrite ?(gx_setn_same _ x hs Hl); rewrite ?gx_setn_other by discriminate; lia.
Qed.

(* q plus the slots' remaining charges is their charge after the rig *)
Lemma sec_runc : forall P m1 mc A i k q, gn_runc MT P m1 mc A i k q -> q + sec_F (lm_hs mc) = sec_F (lm_hs m1).
Proof.
  intros P m1 mc A i k q H.
  induction H as [|mc A i k q Hr IH Hk Hs|mc A i k q h h' h'' E' H' ds c Hr IH Hk Hi Hh Hfd Hcnl Hcshe
                  |mc A i q Hr IH].
  - lia.
  - exact IH.
  - cbn [gn_set lm_hs].
    rewrite (sec_F_set (lm_hs mc) k (Some h'') Hk (sec_nth_lt _ _ _ Hh)), Hh.
    destruct Hcnl as (Eh' & HrE & _). destruct Hcshe as (H'' & Eh'' & _).
    assert (Z0 : sec_c (Some h'') = 0).
    { apply sec_c_empty. rewrite Eh'', Eh'. cbn [set_held set_exp_held hs_expected]. exact HrE. }
    assert (Z1 : sec_c (Some h) = cnl_cost MT (hs_expected h) (hs_held h)) by reflexivity.
    rewrite (sec_cshe nsec KMAX). lia.
  - exact IH.
Qed.

(* a slot the rig drained: its check_no_loss charge is at most 15 (ReplyLSsec.sec_cnl_le) *)
Lemma sec_c_drained : forall cx t m k (e : rentry) h0 h1 c mx no cap e1 LB,
  fr_RINV cx t m -> (k < 4)%nat -> nth k (lm_hs m) None = Some h0 -> gx_pf (e, (h0, k)) ->
  dr_rel c mx no cap e h0 e1 h1 LB -> sec_c (Some h1) <= 15.
Proof.
  intros cx t m k e h0 h1 c mx no cap e1 LB HRI Hk Hh Hpf Hdr.
  destruct Hpf as (Hexp & _ & _ & Hsk & HskU & Hsk01 & Hepre & _ & _ & Hps). cbn [fst snd] in *.
  destruct Hepre as (_ & HU & _).
  destruct (gx_rinv_slot cx t m k h0 HRI Hk Hh) as (_ & _ & _ & _ & Hnd & e2 & Hss & Hkt).
  destruct (gx_dr_rel _ _ _ _ _ _ _ _ _ Hdr) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hmap & Hheld & _).
  destruct (gx_exp_lines _ _ _ _ _ _ _ _ _ Hdr Hexp) as (HT & _).
  pose proof (sec_hsW e h0 Hsk HskU Hsk01 HU) as HW.
  pose proof (dr3_lines h0) as (_ & HLw & _ & _).
  pose proof (dr3_wcost e h0 Hsk HskU Hsk01) as Hwc.
  cbn [sec_c]. apply (sec_cnl_le nsec KMAX).
  - rewrite HT, Hheld.
    pose proof (fr_a12_held_keys (re_keys e2) (hs_held h0) Hnd Hss) as A.
    pose proof (rm3_kt_len (re_keys e2)) as K.
    pose proof (SlotReads.count_begin_bytes (dr_lines h0)) as C.
    rewrite Hwc in HLw. unfold APARTIAL in HU. destruct (re_skip e =? 0); lia.
  - rewrite Hexp in Hmap. cbn [map app] in Hmap.
    exact (sec_recs_short (hs_expected h1) (dr_lines h0) Hmap (sec_lines6 h0 HW)).
Qed.

(* the slots' charges after the rig: at most 4 * 15 *)
Lemma sec_F_m1 : forall cx t m hs qs c2 O2 cap2 out2 m1,
  fr_RINV cx t m -> gn_pairs m hs -> gn_after_rig cx m hs qs c2 O2 cap2 out2 m1 ->
  gn_rig_ok cx m hs qs c2 O2 cap2 -> gx_xpre m hs -> sec_F (lm_hs m1) <= 60.
Proof.
  intros cx t m hs qs c2 O2 cap2 out2 m1 HRI Hp Ha Hr HX.
  assert (Hk : forall k, (k < 4)%nat -> sec_c (nth k (lm_hs m1) None) <= 15).
  { intros k Hk. destruct (gx_rig_slot cx t m hs qs c2 O2 cap2 out2 m1 HRI Hp Ha Hr HX k Hk) as
      [E | (e & h0 & h1 & c & mx & no & cap & e1 & LB & i & H0 & H1 & Hpf & Hdr & _)].
    - rewrite E. destruct (nth k (lm_hs m) None) as [h|] eqn:Eh; [|cbn [sec_c]; lia].
      destruct (gx_rinv_slot cx t m k h HRI Hk Eh) as (Hexp & _). rewrite (sec_c_empty h Hexp). lia.
    - rewrite H1. exact (sec_c_drained cx t m k e h0 h1 c mx no cap e1 LB HRI Hk H0 Hpf Hdr). }
  unfold sec_F. pose proof (Hk 0%nat ltac:(lia)). pose proof (Hk 1%nat ltac:(lia)).
  pose proof (Hk 2%nat ltac:(lia)). pose proof (Hk 3%nat ltac:(lia)). lia.
Qed.

(* ================================================================== the bytes over the gone operation *)
Lemma sec_rig_U : forall pre mx ps qs c O cap c2 O2 cap2 c0 mx0 no0 cap0,
  rig_rel pre mx c O cap ps qs c2 O2 cap2 ->
  zsum (map (fun q => pt_eu (fst q)) qs) =
  zsum (map (fun p => if re_eof (fst p) =? 0 then kf_tail c0 mx0 no0 cap0 (fst p) (fst (snd p))
                      else pt_eu (fst p)) ps).
Proof.
  intros pre mx ps. induction ps as [|[e [h j]] r IH]; intros qs c O cap c2 O2 cap2 c0 mx0 no0 cap0 HR.
  - destruct qs as [|q qs]; cbn [rig_rel] in HR; [reflexivity | contradiction].
  - destruct qs as [|[e' h1] q]; cbn [rig_rel] in HR; [contradiction|].
    destruct HR as (e1 & ev & LB & HR). cbv zeta in HR. destruct HR as (Hd & He' & Hrest).
    match type of Hrest with context [sl_sends ?a ?b ?d ?f ?g] =>
      destruct (sl_sends a b d f g) as [[c3 O3] cap3] eqn:ES end.
    cbn [map fold_right fst snd]. rewrite (IH q c3 O3 cap3 c2 O2 cap2 c0 mx0 no0 cap0 Hrest).
    subst e'. assert (EU : pt_eu (entry_keys e1 (snd (geik pre (re_keys e1)))) = pt_eu e1) by reflexivity.
    rewrite EU. revert Hd. destruct (re_eof e =? 0) eqn:Eo; intros Hd.
    + destruct (gx_dr_rel _ _ _ _ _ _ _ _ _ Hd) as (_ & _ & HU' & _).
      assert (ET : pt_eu e1 = kf_tail c0 mx0 no0 cap0 e h).
      { unfold pt_eu. rewrite <- (SlotReads.bzs_length (re_U e1)), HU'. unfold dr_fin.
        exact (ReplyKfTrRig.kf_tail_fin c0 mx0 no0 cap0 _ _ _ _ e h). }
      lia.
    + destruct Hd as [-> ->]. lia.
Qed.
Lemma sec_tail_split : forall (g : rentry -> hsrc -> Z) ps,
  zsum (map (fun p => if re_eof (fst p) =? 0 then g (fst p) (fst (snd p)) else pt_eu (fst p)) ps) =
  zsum (map (fun p => pt_eu (fst p)) ps) - osum (fun e _ => pt_eu e) ps + osum g ps.
Proof.
  intros g. induction ps as [|[e hj] ps IH]; [reflexivity|].
  cbn [map fold_right fst snd]. rewrite !ReplyKfTrRig.osum_cons, IH. destruct (re_eof e =? 0); lia.
Qed.

(* the rig consumes the open pairs' bytes and leaves the drains' partial lines; the loop keeps every pending stream *)
Lemma sec_ub_gone : forall cx t m hs qs c2 O2 cap2 out2 m1 mc A,
  fr_RINV cx t m -> gx_xpre m hs -> gn_pairs m hs -> gn_after_rig cx m hs qs c2 O2 cap2 out2 m1 ->
  gn_rig_ok cx m hs qs c2 O2 cap2 -> gn_run (gn_pre cx m) m1 mc A (length (lm_es m1)) 0%nat ->
  sec_ub mc + osum kf_in (combine (lm_es m) hs) =
  sec_ub m + osum (kf_tail (lm_c m) (lm_mx m) (Z.of_nat (length (lm_O m))) (lm_cap m)) (combine (lm_es m) hs).
Proof.
  intros cx t m hs qs c2 O2 cap2 out2 m1 mc A HRI HX Hpairs Hafter Hrok Hrun.
  pose proof (gx_pq_facts cx m hs qs c2 O2 cap2 out2 m1 Hpairs Hafter Hrok) as HPQ.
  pose proof Hpairs as (Hlh & HPok & HRS).
  pose proof Hafter as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & A10 & A11 & A12 & A13).
  pose proof Hrok as (Hrr & Hlq & _ & Hfds).
  pose proof HRI as (_ & (Hl4 & _) & _).
  pose proof (gx_rig_pairs _ _ _ _ _ _ _ _ _ _ Hrr) as HRP.
  pose proof (sec_rig_U _ _ _ _ _ _ _ _ _ _ (lm_c m) (lm_mx m) (Z.of_nat (length (lm_O m))) (lm_cap m) Hrr) as HU.
  set (ps := combine (lm_es m) hs) in *.
  assert (Hlps : length ps = length qs) by (unfold ps; rewrite length_combine; lia).
  assert (Hnd : List.NoDup (map re_fd (lm_es m1))) by (rewrite A3; apply NoDup_ListNoDup; exact Hfds).
  destruct (gx_run _ m1 mc A _ _ Hrun Hnd) as (R5 & R6 & _ & _ & _ & R7 & Hhist & _).
  (* the loop keeps every slot's pending stream *)
  assert (Hs1 : zsum (map sec_str (lm_hs mc)) = zsum (map sec_str (lm_hs m1))).
  { rewrite (gx_sum4 sec_str (lm_hs mc) ltac:(lia)), (gx_sum4 sec_str (lm_hs m1) A11).
    assert (Hk : forall k', sec_str (nth k' (lm_hs mc) None) = sec_str (nth k' (lm_hs m1) None)).
    { intros k'. destruct (Hhist k') as [L | (h0 & h2 & i0 & X1 & X2 & X3 & _)]; [rewrite L; reflexivity|].
      rewrite X1, X2.
      destruct X3 as (h' & E' & H' & P & g & A0 & ob & ds & c & (E1 & _) & (H'' & E2 & _)).
      subst. reflexivity. }
    rewrite !Hk. reflexivity. }
  (* relay_instance_gone empties the drained slots' pending lists and keeps the others *)
  assert (HALL : Forall (fun pq => re_eof (fst (fst pq)) = 0 ->
            nth (snd (snd (fst pq))) (lm_hs m) None = Some (fst (snd (fst pq))) /\
            nth (snd (snd (fst pq))) (lm_hs m1) None = Some (snd (snd pq)) /\
            sec_str (Some (snd (snd pq))) = 0) (combine ps qs)).
  { rewrite Forall_forall in HPQ, HRP |- *. intros [p q] Hin Heof. cbn [fst snd] in Heof |- *.
    destruct (HPQ (p, q) Hin Heof) as (_ & Q2 & Q3). cbn [fst snd] in Q2, Q3.
    destruct (HRP (p, q) Hin) as (_ & Hdr). cbn [fst snd] in Hdr.
    destruct (Hdr Heof) as (c' & mx' & no & cap' & e1 & LB & D).
    destruct (gx_dr_rel _ _ _ _ _ _ _ _ _ D) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Dp & _).
    split; [exact Q2|]. split; [exact Q3|].
    change (sec_str (Some (snd q))) with (Z.of_nat (length (pending_stream (snd q)))).
    unfold pending_stream. rewrite Dp. reflexivity. }
  set (F := fun j => sec_str (nth j (lm_hs m1) None) - sec_str (nth j (lm_hs m) None)).
  assert (S1 : zsum (map sec_str (lm_hs m1)) - zsum (map sec_str (lm_hs m)) = F 0%nat + F 1%nat + F 2%nat + F 3%nat).
  { unfold F. rewrite (gx_sum4 sec_str (lm_hs m1) A11), (gx_sum4 sec_str (lm_hs m) Hl4). lia. }
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
               zsum (map (fun pq => - pk_gp (fst pq)) (combine ps qs))).
  { apply (gx_sum_ext _ _ _ _ HALL). intros [p q] Hpq. cbn [fst snd] in Hpq |- *. unfold pk_gp.
    destruct (re_eof (fst p) =? 0) eqn:Eo; [|lia].
    apply Z.eqb_eq in Eo. destruct (Hpq Eo) as (Hm & Hm1 & P2).
    unfold F. rewrite Hm, Hm1, P2.
    change (sec_str (Some (fst (snd p)))) with (Z.of_nat (length (pending_stream (fst (snd p))))). lia. }
  rewrite ou_zsum_opp, <- (gx_sum_cfst pk_gp ps qs Hlps) in S3.
  (* the entries: the drained ones' partial lines are dr_fin's *)
  assert (EU : zsum (map pt_eu (lm_es mc)) = zsum (map (fun q => pt_eu (fst q)) qs))
    by (rewrite R5, A3, map_map; reflexivity).
  assert (EE : zsum (map pt_eu (lm_es m)) = zsum (map (fun p => pt_eu (fst p)) ps))
    by (exact (gx_sum_cfst pt_eu (lm_es m) hs ltac:(lia))).
  rewrite sec_tail_split in HU.
  pose proof (sec_osum_split ps) as SP.
  unfold sec_ub. lia.
Qed.

(* ================================================================== the rows and the rules *)
Section rules.
Hypothesis HKC : 240 <= KC.
Variable B : asyms.
Local Notation fr_SEC := (fr_SEC nsec KMAX KC).

(* lane B's rig count at gn_rigc's (or any) pairing, with gone's premises *)
Lemma sec_rig_at : forall cx t m ly S hs',
  fr_LS3c B cx t m ly S -> fr_RINV cx t m -> gn_op cx t m -> gx_xpre m hs' -> gn_pairs m hs' ->
  Forall (fun e => Z.of_nat (length (re_U e)) <= APARTIAL) (lm_es m) ->
  21 * nsec_tr (rig_tr (lm_c m) (lm_mx m) (Z.of_nat (length (lm_O m))) (lm_cap m) (gn_id cx m) (lm_es m) hs') +
    osum (kf_tail (lm_c m) (lm_mx m) (Z.of_nat (length (lm_O m))) (lm_cap m)) (combine (lm_es m) hs') <=
  21 * 180 + osum kf_in (combine (lm_es m) hs').
Proof.
  intros cx t m ly S hs' HLS HRI Hop HX Hp HU.
  pose proof Hop as (_ & HO & Ht & _).
  destruct (grg_pairs cx t m hs' HRI Hp Ht HU) as (_ & _ & _ & Hlen).
  pose proof (fr_LS3c_gone_rig_c1 B cx t m ly S hs' HLS HRI Hp HO Ht HU) as HM. rewrite pk_WR_MMAX in HM.
  pose proof (gx_pf_all cx t m hs' HRI Hp HX) as HPF.
  assert (HF : Forall (fun p => re_eof (fst p) = 0 -> ReplyKfTrRig.kf_dr_pre (fst p) (fst (snd p)))
                 (combine (lm_es m) hs')).
  { eapply Forall_impl; [|exact HPF]. intros p Hp' Heof. exact (sec_pf_pre p (Hp' Heof)). }
  pose proof (ReplyKfTrRig.kf_rig (lm_c m) (lm_mx m) (Z.of_nat (length (lm_O m))) (lm_cap m) (gn_id cx m) (lm_es m)
                hs' Hlen HF ltac:(lia)) as K.
  assert (KK : ReplyKfTrRig.KC_rig = 180) by reflexivity. lia.
Qed.

(* top_x LS_gone_rig's meter conjunct (GN_LS_rig at LS := LSI, MMAX := fr_MMAX): no re_cap there, so sec_rig45 *)
Lemma fr_SEC_gone_rig : forall cx t m ly S hs,
  fr_LS3c B cx t m ly S -> fr_RINV cx t m -> gn_pairs m hs -> gn_op cx t m ->
  Forall (fun e => Z.of_nat (length (re_U e)) <= APARTIAL) (lm_es m) ->
  (forall j h, nth j (lm_hs m) None = Some h ->
     (hl_recs (hs_pending h) = [] /\ hs_off h = 0) \/
     (exists r rs, hl_recs (hs_pending h) = r :: rs /\ 0 <= hs_off h < Z.of_nat (length (snd r)))) ->
  fr_SEC cx t m ly S ->
  mo_ok MT S (tr_cost MT (rig_tr (lm_c m) (lm_mx m) (Z.of_nat (length (lm_O m))) (lm_cap m) (gn_id cx m) (lm_es m) hs)).
Proof.
  intros cx t m ly S hs HLS HRI Hp Hop HU HS H.
  pose proof Hop as (_ & HO & Ht & _). pose proof HRI as (_ & (Hl4 & _ & _ & Hent & _) & _).
  destruct (grg_pairs cx t m hs HRI Hp Ht HU) as (_ & _ & _ & Hlen).
  pose proof (fr_LS3c_gone_rig_c1 B cx t m ly S hs HLS HRI Hp HO Ht HU) as HM. rewrite pk_WR_MMAX in HM.
  assert (HF : Forall (fun p => re_eof (fst p) = 0 -> sec_dr_pre (fst p) (fst (snd p))) (combine (lm_es m) hs)).
  { pose proof Hp as (_ & HPok & _). rewrite Forall_forall in HPok |- *. intros [e hj] Hin Heof. cbn [fst snd] in *.
    destruct (HPok (e, hj) Hin Heof) as (Hj & Hn & _ & Hsk & HskU & _). cbn [fst snd] in *.
    assert (He : In e (lm_es m)) by exact (in_combine_l _ _ _ _ Hin).
    rewrite Forall_forall in Hent, HU. destruct (Hent e He) as (_ & _ & _ & _ & Hsk01).
    split.
    - destruct (HS _ _ Hn) as [(_ & E) | (r & rs & _ & E & _)]; lia.
    - exact (sec_hsW e (fst hj) Hsk HskU Hsk01 (HU e He)). }
  pose proof (sec_rig45 (lm_c m) (lm_mx m) (Z.of_nat (length (lm_O m))) (lm_cap m) (gn_id cx m) (lm_es m) hs Hlen HF
                ltac:(lia)) as K.
  pose proof (sec_osum_in m hs Hl4 Hp) as Hin.
  pose proof (sec_osum_nonneg (kf_tail (lm_c m) (lm_mx m) (Z.of_nat (length (lm_O m))) (lm_cap m))
                (combine (lm_es m) hs) ltac:(intros; unfold ReplyKfTrRig.kf_tail; lia)) as T0.
  rewrite (sec_tr nsec KMAX).
  apply (fr_SEC_ok nsec KMAX KC HKC cx t m ly S S 0); [exact H | lia | lia].
Qed.

(* the gone operation's count so far at a call of the loop: the rig's (at gn_rigc's pairing) and the earlier calls' *)
Lemma sec_gone_so_far : forall cx t m ly S hs qs c2 O2 cap2 out2 m1 mc A i k (Sx : astate) cst q,
  fr_LS3c B cx t m ly S -> fr_RINV cx t m -> gn_op cx t m ->
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
  gn_pairs m hs -> gn_after_rig cx m hs qs c2 O2 cap2 out2 m1 -> gn_rig_ok cx m hs qs c2 O2 cap2 ->
  gn_runc MT (gn_pre cx m) m1 mc A i k q -> mo_le MT S Sx cst -> gn_cst MT cx m m1 q cst ->
  exists r, nsec Sx <= nsec S + r + q /\ 21 * r <= 21 * 180 + sec_ub m /\ q + sec_F (lm_hs mc) <= 60.
Proof.
  intros cx t m ly S hs qs c2 O2 cap2 out2 m1 mc A i k Sx cst q HLS HRI Hop HE Hcap HE6 HS6 Hp Ha Hrok Hrunc Hmo
    Hcst.
  pose proof (gx_xpre_of6 cx t m hs Hop HE Hcap HE6 HS6 Hp) as HX.
  pose proof HRI as (_ & (Hl4 & _) & _).
  assert (HU : Forall (fun e => Z.of_nat (length (re_U e)) <= APARTIAL) (lm_es m))
    by (eapply Forall_impl; [|exact HE6]; intros e He; exact (proj1 He)).
  destruct Hcst as (r & (hs' & qs' & c2' & O2' & cap2' & out2' & Hp' & _ & Er) & Hc).
  pose proof (gx_xpre_of6 cx t m hs' Hop HE Hcap HE6 HS6 Hp') as HX'.
  pose proof (sec_rig_at cx t m ly S hs' HLS HRI Hop HX' Hp' HU) as Kr.
  pose proof (sec_osum_in m hs' Hl4 Hp') as Hin.
  pose proof (sec_osum_nonneg (kf_tail (lm_c m) (lm_mx m) (Z.of_nat (length (lm_O m))) (lm_cap m))
                (combine (lm_es m) hs') ltac:(intros; unfold ReplyKfTrRig.kf_tail; lia)) as T0.
  pose proof (sec_F_m1 cx t m hs qs c2 O2 cap2 out2 m1 HRI Hp Ha Hrok HX) as HF1.
  pose proof (sec_runc _ m1 mc A _ _ q Hrunc) as HR.
  change (nsec Sx <= nsec S + cst) in Hmo. rewrite (sec_tr nsec KMAX) in Er.
  exists r. subst r. split; [lia|]. split; lia.
Qed.

(* GN_RI_step's cnl meter conjunct *)
Lemma fr_SEC_gone_cnl : forall cx t m ly S hs qs c2 O2 cap2 out2 m1 mc A i k h (Sx : astate) cst q,
  fr_LS3c B cx t m ly S -> fr_RINV cx t m -> gn_op cx t m ->
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
  gn_pairs m hs -> gn_after_rig cx m hs qs c2 O2 cap2 out2 m1 -> gn_rig_ok cx m hs qs c2 O2 cap2 ->
  gn_runc MT (gn_pre cx m) m1 mc A i k q -> mo_le MT S Sx cst -> gn_cst MT cx m m1 q cst ->
  (k < 4)%nat -> nth k (lm_hs mc) None = Some h ->
  fr_SEC cx t m ly S -> mo_ok MT Sx (cnl_cost MT (hs_expected h) (hs_held h)).
Proof.
  intros cx t m ly S hs qs c2 O2 cap2 out2 m1 mc A i k h Sx cst q HLS HRI Hop HE Hcap HE6 HS6 Hp Ha Hrok Hrunc Hmo
    Hcst Hk Hh H.
  destruct (sec_gone_so_far cx t m ly S hs qs c2 O2 cap2 out2 m1 mc A i k Sx cst q HLS HRI Hop HE Hcap HE6 HS6 Hp
              Ha Hrok Hrunc Hmo Hcst) as (r & R1 & R2 & R3).
  pose proof (sec_F_ge (lm_hs mc) k h Hk Hh) as Hge.
  assert (Ec : sec_c (Some h) = cnl_cost MT (hs_expected h) (hs_held h)) by reflexivity.
  apply (fr_SEC_ok nsec KMAX KC HKC cx t m ly S Sx (r + q)); [exact H | lia | lia].
Qed.
(* GN_RI_step's cshe meter conjunct (check_shape_ends frees only) *)
Lemma fr_SEC_gone_cshe : forall cx t m ly S hs qs c2 O2 cap2 out2 m1 mc A i k h (Sx Sy : astate) cst q (h' : hsrc),
  fr_LS3c B cx t m ly S -> fr_RINV cx t m -> gn_op cx t m ->
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
  gn_pairs m hs -> gn_after_rig cx m hs qs c2 O2 cap2 out2 m1 -> gn_rig_ok cx m hs qs c2 O2 cap2 ->
  gn_runc MT (gn_pre cx m) m1 mc A i k q -> mo_le MT S Sx cst -> gn_cst MT cx m m1 q cst ->
  (k < 4)%nat -> nth k (lm_hs mc) None = Some h ->
  mo_le MT Sx Sy (cnl_cost MT (hs_expected h) (hs_held h)) ->
  fr_SEC cx t m ly S -> mo_ok MT Sy (hl_n (hs_held h') * mo_free MT).
Proof.
  intros cx t m ly S hs qs c2 O2 cap2 out2 m1 mc A i k h Sx Sy cst q h' HLS HRI Hop HE Hcap HE6 HS6 Hp Ha Hrok
    Hrunc Hmo Hcst Hk Hh Hmo2 H.
  destruct (sec_gone_so_far cx t m ly S hs qs c2 O2 cap2 out2 m1 mc A i k Sx cst q HLS HRI Hop HE Hcap HE6 HS6 Hp
              Ha Hrok Hrunc Hmo Hcst) as (r & R1 & R2 & R3).
  pose proof (sec_F_ge (lm_hs mc) k h Hk Hh) as Hge.
  assert (Ec : sec_c (Some h) = cnl_cost MT (hs_expected h) (hs_held h)) by reflexivity.
  change (nsec Sy <= nsec Sx + cnl_cost MT (hs_expected h) (hs_held h)) in Hmo2.
  rewrite (sec_HFs nsec KMAX), Z.mul_0_r.
  apply (fr_SEC_ok nsec KMAX KC HKC cx t m ly S Sy (r + q + cnl_cost MT (hs_expected h) (hs_held h))); [exact H | lia |].
  lia.
Qed.

(* GN_RI_end's fr_SEC *)
Lemma fr_SEC_gone_end : forall cx t m ly S hs qs c2 O2 cap2 out2 m1 mc A (lyx : alayout) (Sx : astate) cst q,
  fr_LS3c B cx t m ly S -> fr_RINV cx t m -> gn_op cx t m ->
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
  gn_pairs m hs -> gn_after_rig cx m hs qs c2 O2 cap2 out2 m1 -> gn_rig_ok cx m hs qs c2 O2 cap2 ->
  gn_run (gn_pre cx m) m1 mc A (length (lm_es m1)) 0%nat ->
  gn_runc MT (gn_pre cx m) m1 mc A (length (lm_es m1)) 0%nat q ->
  mo_le MT S Sx cst -> gn_cst MT cx m m1 q cst ->
  fr_SEC cx t m ly S -> fr_SEC cx (t + 1) mc lyx Sx.
Proof.
  intros cx t m ly S hs qs c2 O2 cap2 out2 m1 mc A lyx Sx cst q HLS HRI Hop HE Hcap HE6 HS6 Hp Ha Hrok Hrun Hrunc
    Hmo Hcst H.
  pose proof (gx_xpre_of6 cx t m hs Hop HE Hcap HE6 HS6 Hp) as HX.
  pose proof Hop as (_ & _ & Ht & _).
  pose proof HRI as (_ & (Hl4 & _) & _).
  assert (HU : Forall (fun e => Z.of_nat (length (re_U e)) <= APARTIAL) (lm_es m))
    by (eapply Forall_impl; [|exact HE6]; intros e He; exact (proj1 He)).
  destruct Hcst as (r & (hs' & qs' & c2' & O2' & cap2' & out2' & Hp' & _ & Er) & Hc).
  pose proof (gx_xpre_of6 cx t m hs' Hop HE Hcap HE6 HS6 Hp') as HX'.
  pose proof (sec_rig_at cx t m ly S hs' HLS HRI Hop HX' Hp' HU) as Kr.
  rewrite (sec_osum_same cx t m kf_in hs' hs HRI Hp' Hp),
    (sec_osum_same cx t m (kf_tail (lm_c m) (lm_mx m) (Z.of_nat (length (lm_O m))) (lm_cap m)) hs' hs HRI Hp' Hp)
    in Kr.
  pose proof (sec_ub_gone cx t m hs qs c2 O2 cap2 out2 m1 mc A HRI HX Hp Ha Hrok Hrun) as Hub.
  pose proof (sec_F_m1 cx t m hs qs c2 O2 cap2 out2 m1 HRI Hp Ha Hrok HX) as HF1.
  pose proof (sec_runc _ m1 mc A _ _ q Hrunc) as HR. pose proof (sec_F_nonneg (lm_hs mc)) as HF0.
  change (nsec Sx <= nsec S + cst) in Hmo. rewrite (sec_tr nsec KMAX) in Er. subst r.
  apply (fr_SEC_step nsec KMAX KC cx t m mc ly S lyx Sx
           (nsec_tr (rig_tr (lm_c m) (lm_mx m) (Z.of_nat (length (lm_O m))) (lm_cap m) (gn_id cx m) (lm_es m) hs') + q)
           Ht ltac:(lia)); [|exact H].
  destruct (SEC_RATE_ge KC HKC) as (R1 & _). lia.
Qed.
End rules.
End gn.
