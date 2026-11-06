(* WIP (a Theorem Labs lane's FREE-PIECES row B1c, a Theorem Labs lane, claimed 2026-10-29T20:07:33Z): the LS rules of the drain /
   remove / gone / event arms of fuzz_reply's entry walk, proved from fr_LS (lib/A/ReplyLS.v, v2 text: a Theorem Labs lane's B1a
   keeps it, with `kk` moved into Section ls).  The arms' texts are those of a working branch
   11dbbff1cc0 (drain / remove / gone are the same blobs on this base 87ac96a746d; event's LS rules are in integ's
   event.v (sha256 8897210ba524; internal record) only).

   CLASSIFICATION at the instance MT := ameter_triv (Reusable/YCbp.v:17: mo_ok := fun _ _ => True,
   mo_le := fun _ _ _ => True):
   (1) about the state LS holds in only - provable from fr_LS (as fr_LS_add_room / the keep rules are):
       drain.v  LS_drain_pre :658, LS_drain_skip :692 (same S, model dr_skip);
       remove.v LS_rm_rr_pre :1957;
       event.v  LS_event_malloc (integ :1032).
   (2) conclusion only mo_ok of some state - True at ameter_triv:
       remove.v LS_rm_cshe_pre :3767, LS_rm_sr_pre :5186; event.v LS_event_free (integ :1041).
   (3) about a POST-state tied to S only by mo_le (True at ameter_triv), so the post-state's blocks are free - not
       provable for any LS that bounds live bytes (ls_rules_collapse_at_triv, LS-FINDING.v (sha256 e350965e21c5; internal record)); these
       need the arm's text to carry the callee post's ablocks Permutation premises, as LS_add_open does:
       drain.v  LS_cnl_pre (blocks_bytes S'), LS_drain_step :701;
       remove.v LS_rm_cnl_pre :2601 (blocks_bytes S), LS_rm_step :5404;
       event.v  LS_event_relay (integ :1035, blocks_bytes S1), LS_event_step (integ :1046).
   gone.v states no LS rule.  Group (3) is what the row's "FREE once each arm's statement lands" waits for.
   Each lemma below is the arm's hypothesis text with LS := fr_LS B; RINV is left a parameter where the proof does
   not read it (so the lemma holds at RINV := fr_RINV, the instance's). *)
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
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import W_LLVMFuzzerTestOneInput_drain.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import W_LLVMFuzzerTestOneInput_write.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import W_LLVMFuzzerTestOneInput_event.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import ReplyRINV.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YCbp.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import CheckRep.
(* rm_rr_tr / rm_rr_cost / rm_cnl_cost / rm_cshe_cost: the remove arm's (Section rmw); Require without Import, so the
   remove model names below stay ReplyRINV.v's *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require W_LLVMFuzzerTestOneInput_remove.
Import ListNotations.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

(* The instance the arms are used at (ReplyATop.v:93 MT := ameter_triv; the request bound of the write arm,
   W_LLVMFuzzerTestOneInput_write.v:132 WR_MMAX, which ATop equates with fr_MMAX).  Each rule below is the arm's
   hypothesis with LS := fr_LS B, RINV := fr_RINV, MT := ameter_triv, MMAX := WR_MMAX. *)
Local Notation MT := ameter_triv.
Local Notation MMAX := WR_MMAX.

Lemma mo_ok_triv : forall (S : astate) (c : Z), mo_ok MT S c.
Proof. intros S c. exact I. Qed.

Section arms.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : asyms.

(* ================================================================== drain *)
(* a working branch 129f255c729 _drain.v:760 LS_drain_skip (integ 6fb612fb746 :692 has four more
   premises; this text implies it) *)
Lemma fr_LS_drain_skip : forall cx t m ly S,
  fr_LS B cx t m ly S -> fr_LS B cx (t + 1) (dr_skip m (dr_k' cx m)) ly S.
Proof.
  intros cx t m ly S H.
  apply (fr_LS_k_only B cx t (t + 1) m (dr_skip m (dr_k' cx m)) ly S); try reflexivity; [|exact H].
  left. unfold dr_skip, dr_k'. cbn [lm_k]. destruct (lm_k m + 1 <? c_n cx); lia.
Qed.

(* ================================================================== remove *)
(* 30d91cacb63 _remove.v:3801 LS_rm_cshe_pre (= integ :3767) *)
Lemma fr_LS_rm_cshe_pre : forall cx t m ly0 S0 (S : astate) si h j0 e1 h1 ev LB c2 O2 cap2 E' H',
  fr_LS B cx t m ly0 S0 -> fr_RINV cx t m -> rm_at cx m si h j0 -> rm_rr_ok m h j0 e1 h1 ev LB c2 O2 cap2 ->
  rm_cnl_ok h1 E' H' ->
  mo_le MT S0 S (W_LLVMFuzzerTestOneInput_remove.rm_rr_cost MT m h +
    W_LLVMFuzzerTestOneInput_remove.rm_cnl_cost MT (hs_expected h1) (hs_held h1)) ->
  mo_ok MT S (W_LLVMFuzzerTestOneInput_remove.rm_cshe_cost MT H').
Proof. intros. apply mo_ok_triv. Qed.

(* 30d91cacb63 _remove.v:5232 LS_rm_sr_pre (= integ :5186) *)
Lemma fr_LS_rm_sr_pre : forall cx t m ly0 S0 (S : astate) si h j0 e1 h1 ev LB c2 O2 cap2 E' H' H'' ds cc,
  fr_LS B cx t m ly0 S0 -> fr_RINV cx t m -> rm_at cx m si h j0 -> rm_rr_ok m h j0 e1 h1 ev LB c2 O2 cap2 ->
  rm_cnl_ok h1 E' H' -> rm_cshe_ok m (set_exp_held h1 E' H') O2 (rm_A1 m h1) H'' ds cc ->
  mo_le MT S0 S (W_LLVMFuzzerTestOneInput_remove.rm_rr_cost MT m h +
    W_LLVMFuzzerTestOneInput_remove.rm_cnl_cost MT (hs_expected h1) (hs_held h1) +
    W_LLVMFuzzerTestOneInput_remove.rm_cshe_cost MT H') ->
  mo_ok MT S (sr_cost MT (Some (set_held (set_exp_held h1 E' H') H''))).
Proof. intros. apply mo_ok_triv. Qed.

(* ================================================================== event *)
(* the event's bytes are input bytes: at most c_n of them *)
Lemma ev_len_le : forall cx m, 0 <= lm_k m -> 0 <= c_n cx -> ev_len cx m <= c_n cx.
Proof.
  intros cx m Hk Hn. unfold ev_len. destruct (Z.leb_spec 2 (c_n cx - lm_k m - 1)); lia.
Qed.

(* a working branch 1172d6d9065 _event.v:1031 LS_event_malloc (= integ :1032) *)
Lemma fr_LS_event_malloc : forall cx t m ly S e,
  fr_LS B cx t m ly S -> fr_RINV cx t m -> ev_evt cx m e ->
  re_len e < MMAX /\ blocks_bytes S + re_len e <= LIVE_MAX /\ mo_ok MT S (mo_malloc MT (re_len e)).
Proof.
  intros cx t m ly S e H _ (He & _).
  pose proof (fr_LS_room B cx t m ly S H) as Hroom. pose proof (fr_LS_k B cx t m ly S H) as Hk.
  destruct H as (rest & e0 & _ & _ & _ & Hc & _).
  assert (Hk0 : 0 <= lm_k m) by (unfold kk in Hk; lia).
  pose proof (ev_len_le cx m Hk0 ltac:(lia)) as Hl.
  assert (HW : WR_MMAX = 1072693248) by reflexivity.
  unfold re_len, ROOM_SPARE in *. refine (conj _ (conj _ (mo_ok_triv _ _))); lia.
Qed.

(* 1172d6d9065 _event.v:1040 LS_event_free (= integ :1041) *)
Lemma fr_LS_event_free : forall cx t m ly S (S1 S2 : astate) e,
  fr_LS B cx t m ly S -> fr_RINV cx t m -> ev_evt cx m e ->
  mo_le MT S S1 (mo_malloc MT (re_len e)) ->
  mo_le MT S1 S2 (sl_cost MT (lm_c m) (lm_mx m) (Z.of_nat (length (lm_O m))) (lm_cap m) (re_len e)) ->
  mo_ok MT S2 (mo_free MT).
Proof. intros. apply mo_ok_triv. Qed.

End arms.
