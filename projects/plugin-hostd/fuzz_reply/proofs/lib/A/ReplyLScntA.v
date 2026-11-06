(* The LS_cnt rows of SEG_PRO, ARM_add, ARM_write and ARM_remove at W8's re-fit arm texts (the TOP-step head
   14fbe276057: lib/A/W_LLVMFuzzerTestOneInput_pro_x.v:241 (and its check Section's twin :2009), _add_x.v:760,
   _write_x.v:162 (twin :2092), _remove_x.v:230; the first three as at armsrest bcd04daf1a1), at LSx := fr_LS3cp B and
   RINV := fr_RINV, with HRP_CNT (ReplyLScntRP.v: RP's count fields are ReplyCnt.v's; the top discharges it at RP_cf by
   rp_cnt_cf).  proves no function (kind: invariant lemma).

   THE BRIDGE.  The arms give amodel_at (lib/A/W_LLVMFuzzerTestOneInput_cut.v, the same text at bcd04daf1a1) where
   ReplyLScnt.v's rows take ReplyCnt.msz_ok (lm_es m) (lm_hs m) (each entry's buffer at most 16,384 bytes and its keys
   at most APARTIAL; each open source's expected and held texts at most APARTIAL).  msz_ok_of_amodel_at reads them off
   amodel_at: the entries' from arelay_at's aentry_ok (lib/A/W_rep.v:124 the buffer's three sizes, :139 the keys'
   lengths), the sources' from aslot's asrc_at, whose expected and held lists are alist_at's `lines = true` (:90).  It is
   the two halves msz_es_of_amodel_at / msz_hs_of_amodel_at joined by `split`.

   THE TEXTS.  rp_cnt_pro_A, rp_cnt_add_A, rp_cnt_write_A and rp_cnt_rm_A are the arms' LS_cnt texts, the binders, the
   guards in their order and the conclusion, with LSx / RINV the local notations below.  Every name resolves to the
   definition the arms name: roomp / cnt_ok_pk (lib/A/W_journal_x.v), oa_peak (lib/A/W_op_add.v), lp_peak
   (lib/A/W_contract_x.v), rm_at (lib/A/W_LLVMFuzzerTestOneInput_remove.v), rm_pk (_remove_x.v).

   THE REMOVE ROW.  _remove_x.v's LS_cnt guards with rm_at and amodel_at only; ReplyLScntRP.v rp_cnt_rm (at
   ReplyLScnt.v fr_LS3cp_cnt_rm's premises) also takes |re_U| of the removed entry <= APARTIAL, the model blocks' sizes
   not negative and the source's read offset.  amodel_at gives all three: aentry_ok's re_used clause (W_rep.v:125) and
   _remove.v rm_mfacts_of.  remove_x's rm_pk is ReplyLScnt.pk_rm's text (its rm_cnl_pk restates
   ReplyTrPeakCnl.cnl_pk), so the rows meet by conversion; ReplyRINV.v's rm_at / rm_ent are notations for _remove.v's. *)
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
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YC5d YCbp.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import ACfn.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib Require Import ZTraceSpec.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import
W_syms W_listing W_place W_tbl W_kit W_pl W_img W_journal.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import HarnessRep RelayRep ListRep.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import W_rep W_contract W_sites W_frame W_op_add.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import W_LLVMFuzzerTestOneInput_cut.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import
W_LLVMFuzzerTestOneInput_head W_LLVMFuzzerTestOneInput_small W_LLVMFuzzerTestOneInput_write
W_LLVMFuzzerTestOneInput_add.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require ACfn_cf.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import ReplyLS.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import W_LLVMFuzzerTestOneInput_drain.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import W_LLVMFuzzerTestOneInput_event.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import ReplyRINV.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import CheckRep.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import ReplyLSArms.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import RelayKeys RelayModel.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require
  RelayRunT RelayRunF ListTr drain_b_c send_line_b_c gesture_end_b_c gestures_end_b_c relay_remove_b_c RelayCap SlotInv
  SlotReads relay_instance_gone_b_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Spec Require PresetRoom.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import
  ReplyLS3 ReplyLSDrainPre ReplyLSRemove3 ReplyLSRrPre ReplyLSDrain3 ReplyLSEvent3.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import ReplyTrPeak.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import
  ReplyLS3Arms ReplyLSCntL ReplyLS3c ReplyLS3cArms ReplyTrPeakW.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import ReplyLSCntM ReplyLS3p ReplyTrPeakCnt.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import ReplyLScnt ReplyLScntRP.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import ReplyCnt.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import W_journal_x W_contract_x.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require W_LLVMFuzzerTestOneInput_remove
  W_LLVMFuzzerTestOneInput_remove_x.
Import ListNotations.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

Section sz.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
#[local] Notation segs := (@pa_segs _ fr_prog_listing PB_fr).
Variable B : asyms.

(* ================================================================== msz_ok from amodel_at *)
(* an expected or held list (alist_at's lines = true, W_rep.v:90): its texts are at most APARTIAL *)
Lemma lsc_alist_texts : forall ly S (W : world segs) mem LA l,
  alist_at B ly S W mem LA l true -> ReplyCnt.texts_ok l.
Proof.
  intros ly S W mem LA l (_ & _ & _ & _ & _ & _ & _ & _ & HF). unfold ReplyCnt.texts_ok.
  eapply Forall_impl; [|exact HF]. intros r (_ & _ & Ht & _). exact (proj2 (Ht eq_refl)).
Qed.
(* an open source (asrc_at, W_rep.v:111-112): its expected and held lists *)
Lemma lsc_asrc_texts : forall ly S (W : world segs) mem HA h,
  asrc_at B ly S W mem HA h -> ReplyCnt.texts_ok (hs_expected h) /\ ReplyCnt.texts_ok (hs_held h).
Proof.
  intros ly S W mem HA h
    (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & He & Hh & _).
  exact (conj (lsc_alist_texts _ _ _ _ _ _ He) (lsc_alist_texts _ _ _ _ _ _ Hh)).
Qed.
(* a relay entry (aentry_ok, W_rep.v:124, :139): its buffer's size and its keys' lengths *)
Lemma lsc_entry_sz : forall ly S (W : world segs) mem e, aentry_ok B ly S W mem e ->
  0 <= re_cap e <= 16384 /\
  Forall (fun k => Z.of_nat (length (gestures_end_b_c.key_text k)) <= APARTIAL) (re_keys e).
Proof.
  intros ly S W mem e (_ & _ & _ & _ & _ & Hcap & _ & _ & _ & _ & _ & _ & _ & _ & HK). split; [lia|].
  eapply Forall_impl; [|exact HK]. intros k (_ & _ & _ & Hk). lia.
Qed.
(* msz_ok's first half: the relay's entries (arelay_at's Forall aentry_ok, W_rep.v:162) *)
Lemma msz_es_of_amodel_at : forall ly S (W : world segs) mem m, amodel_at B ly S W mem m ->
  Forall (fun e => 0 <= re_cap e <= 16384 /\
    Forall (fun k => Z.of_nat (length (gestures_end_b_c.key_text k)) <= APARTIAL) (re_keys e)) (lm_es m).
Proof.
  intros ly S W mem m (_ & _ & Hrel & _). destruct Hrel as (_ & _ & _ & _ & _ & _ & _ & _ & _ & HF & _).
  eapply Forall_impl; [|exact HF]. intros e He. exact (lsc_entry_sz _ _ _ _ e He).
Qed.
(* msz_ok's second half: the four slots (aslot: an open one is asrc_at) *)
Lemma msz_hs_of_amodel_at : forall ly S (W : world segs) mem m, amodel_at B ly S W mem m ->
  Forall (fun o => match o with Some h => ReplyCnt.texts_ok (hs_expected h) /\ ReplyCnt.texts_ok (hs_held h)
                   | None => True end) (lm_hs m).
Proof.
  intros ly S W mem m (Hlen & Hsl & _). apply Forall_forall. intros o Ho.
  destruct (In_nth (lm_hs m) o None Ho) as (i & Hi & Ei). rewrite Hlen in Hi.
  specialize (Hsl i Hi). rewrite Ei in Hsl. destruct o as [h|]; [|exact I].
  exact (lsc_asrc_texts _ _ _ _ _ h Hsl).
Qed.
(* the bridge: amodel_at gives msz_ok *)
Lemma msz_ok_of_amodel_at : forall ly S (W : world segs) mem m, amodel_at B ly S W mem m ->
  ReplyCnt.msz_ok (lm_es m) (lm_hs m).
Proof.
  intros ly S W mem m H.
  split; [exact (msz_es_of_amodel_at ly S W mem m H) | exact (msz_hs_of_amodel_at ly S W mem m H)].
Qed.
End sz.

Section arms.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
#[local] Notation segs := (@pa_segs _ fr_prog_listing PB_fr).
Variable B : asyms.
Variable RP : roomp.
Hypothesis HRP_CNT : RP_CNT RP.
#[local] Notation LSx := (fr_LS3cp B).
#[local] Notation RINV := fr_RINV.

(* ================================================================== the arms' LS_cnt texts *)
(* _pro_x.v:241 (and :2009) at bcd04daf1a1 *)
Lemma rp_cnt_pro_A : forall cx T0 cap out (S2 : astate),
  ReplyCnt.xcnt_ok B (c_S cx) (c_ly cx) (input_blks cx) T0 cap out ->
  ablocks B (c_ly cx) S2 = ablocks B (c_ly cx) (c_S cx) ->
  cnt_ok_pk RP W_op_add.oa_peak (ablocks B (c_ly cx) S2).
Proof.
  intros cx T0 cap out S2 HX E.
  exact (rp_cnt_pro B RP HRP_CNT (c_S cx) S2 (c_ly cx) (c_p cx) (c_n cx) T0 cap out HX E).
Qed.
(* _add_x.v:760 at bcd04daf1a1 *)
Lemma rp_cnt_add_A : forall cx t m ly S (W : world segs) mem,
  LSx cx t m ly S -> RINV cx t m -> ad_at_op cx m -> amodel_at B ly S W mem m -> 0 <= t < OPS_MAX ->
  cnt_ok_pk RP oa_peak (ablocks B ly S).
Proof.
  intros cx t m ly S W mem HLS HRI Hop HM Ht.
  exact (rp_cnt_add B RP HRP_CNT cx t m ly S HLS HRI Hop (msz_ok_of_amodel_at B ly S W mem m HM) Ht).
Qed.
(* _write_x.v:162 (and :2092) at bcd04daf1a1 *)
Lemma rp_cnt_write_A : forall cx t m si h ly S (W : world segs) mem,
  LSx cx t m ly S -> RINV cx t m -> wr_pick cx m si h -> 0 < wr_n cx m -> amodel_at B ly S W mem m -> 0 <= t < OPS_MAX ->
  cnt_ok_pk RP (lp_peak (hs_pending h) (wr_n cx m)) (ablocks B ly S).
Proof.
  intros cx t m si h ly S W mem HLS HRI Hpk Hn HM Ht.
  exact (rp_cnt_write B RP HRP_CNT cx t m si h (wr_n cx m) ly S HLS HRI Hpk Hn
           (msz_ok_of_amodel_at B ly S W mem m HM) Ht).
Qed.
(* _remove_x.v:230 at the TOP-step head 14fbe276057 (top_x LS_cnt_remove) *)
Lemma rp_cnt_rm_A : forall cx t m ly S (W : world segs) mem si h j0,
  LSx cx t m ly S -> RINV cx t m -> W_LLVMFuzzerTestOneInput_remove.rm_at cx m si h j0 ->
  amodel_at B ly S W mem m -> 0 <= t < OPS_MAX ->
  cnt_ok_pk RP (W_LLVMFuzzerTestOneInput_remove_x.rm_pk m h j0) (ablocks B ly S).
Proof.
  intros cx t m ly S W mem si h j0 HLS HRI Hat HM Ht.
  pose proof Hat as (_ & _ & _ & _ & _ & Hh & Hj0 & _).
  destruct (W_LLVMFuzzerTestOneInput_remove.rm_mfacts_of B ly S W mem m HM) as (Hpos & _ & Hoffs).
  assert (HU : Z.of_nat (length (re_U (nth j0 (lm_es m) relay_remove_b_c.no_entry))) <= APARTIAL).
  { pose proof HM as (_ & _ & HREL & _).
    destruct HREL as (_ & _ & _ & _ & _ & _ & _ & _ & _ & HAE & _). rewrite Forall_forall in HAE.
    destruct (HAE _ (nth_In (lm_es m) relay_remove_b_c.no_entry Hj0)) as (_ & _ & _ & _ & _ & _ & U1 & U2 & _).
    lia. }
  exact (rp_cnt_rm B RP HRP_CNT cx t m ly S si h j0 HLS HRI Hat (msz_ok_of_amodel_at B ly S W mem m HM) Ht HU Hpos
           (Hoffs si h Hh)).
Qed.
End arms.
