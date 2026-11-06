(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/jsoncons/fuzz_msgpack_encoder/lib/CJ/Ref/Mh_0118.v, with its module paths, module names and addresses changed; 1147 of its 1229 lines of code are new or changed and 2359 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_reply/lib/Prog/drain_b_seg.v, with its module paths, module names, addresses and numbers changed; 655 of its 764 lines of code are new or changed and 1120 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_reply/lib/U/Prog/relay_instance_gone_b_seg.v, with its module paths and module names changed; 188 of its 239 lines of code are new or changed and 713 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_reply/lib/U/Prog/SlotPass5A.v, with its module paths and module names changed; 957 of its 1013 lines of code are new or changed and 183 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_reply/lib/Prog/CF/SlotPass5Check.v; 192 of its 256 lines of code are new or changed and 949 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_reply/lib/Prog/CF/SlotPass5M.v, with its module paths and module names changed; 190 of its 243 lines of code are new or changed and 203 lines of the source are left out. *)
(* a Theorem Labs lane's FREE-PIECES row B1c (a Theorem Labs lane): conjunct 2 of the remove arm's LS_rm_rr_pre,
   `tr_max (rm_rr_tr m h) < MMAX`, at the instance LS := fr_LS B, RINV := fr_RINV, MT := ameter_triv,
   MMAX := WR_MMAX.  The text is a working branch 30d91cacb63
   lib/A/W_LLVMFuzzerTestOneInput_remove.v:1971-1978; rm_rr_tr is that file's :334-335, and
   W_contract.v's rr_tr / dr_tr / dr_fin / dr_live / tr_max and Prog/drain_b_c.v, gestures_end_b_c.v,
   gesture_end_b_c.v, send_line_b_c.v, RelayKeys.v, RelayModel.v, HarnessRep.v, SlotInv.v have the arm head's text
   in this tree.

   PROVED at a PROPOSED text (fr_LS_rm_rr_pre_c2): the arm's premises (fr_LS, fr_RINV, rm_at) and two more, both of
   which the arm holds where it applies LS_rm_rr_pre (rm_rr, _remove.v:2342; the application at :2398):
     `0 <= t < OPS_MAX` - rm_regs_base's last clause (_remove.v:358), the first conjunct of lregs_rr (:371), named
       Rt where rm_rr destructs the cut's registers (:2353);
     `Z.of_nat (length (re_U (rm_ent m j0))) <= APARTIAL` - aentry_ok of entry j0 (W_rep.v:125, `Z.of_nat (length
       (re_U e)) = re_used e /\ re_used e <= APARTIAL`): rm_rr has HREL : arelay_at B fr_RG ly3 S3 W mem (lm_G m)
       (lm_es m) (:2356, amodel_at's clause _cut.v:302), whose clause W_rep.v:156 is Forall (aentry_ok ..) (lm_es m),
       and j0 < length (lm_es m) is Hj0 (:2351); rm_rr already destructs HREL at :2359 (for its NoDup clause).
   Neither follows from fr_LS + fr_RINV, for the reasons ReplyLSDrainPre.v's header gives for the same drain
   (rr_tr's first part is dr_tr of the entry when it is open): without t < OPS_MAX the pending stream may be
   2 ^ 25 + 2 NUL bytes and reference_feed's push asks 2 ^ 30 > WR_MMAX; fr_RINV bounds re_U only at re_skip = 0
   and fr_LS bounds re_cap only through PHI, so drain's first growth may ask 2 re_cap >= 2 ^ 30.
   The rest of rr_tr needs no extra fact: the gesture ends of the keys drain leaves (gestures_end_b_c.keys_end_run
   from g_nout = ds_no) ask at most 2 * (ds_no + sum (|key| + 5)) per send_line round (dpre_send_line), drain's
   g_nout is at most the pair's input cost (ReplyLSRemove3.rm3_no_fin, with no = |lm_O m| = 0 from rm_at), drain
   adds at most |line| + 1 key bytes per relayed line (rrp_drain_kw), so every such request is at most
   4 * c_n < 2 ^ 28; relay_remove's last two requests are frees.
   fr_LS_rm_rr_pre_124 states conjuncts 1, 2 and 4 together at the same premises (1 and 4 are
   ReplyLSRemove3.fr_LS_rm_rr_pre_sizes, which needs neither extra premise). *)
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
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import ReplyLSArms.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import RelayKeys RelayModel ListRep.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require
  RelayRunT drain_b_c send_line_b_c gesture_end_b_c gestures_end_b_c relay_remove_b_c RelayCap SlotInv.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import ReplyLSDrainPre ReplyLSRemove3.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require W_LLVMFuzzerTestOneInput_remove.
Import ListNotations.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

(* the instance (ReplyATop.v:93 MT := ameter_triv; W_LLVMFuzzerTestOneInput_write.v:132 WR_MMAX) *)
Local Notation MT := ameter_triv.
Local Notation MMAX := WR_MMAX.

(* ================================================================== the largest request of a trace *)
Lemma rrp_tr_max_nonneg : forall {P : Type} (tr : list (RelayRunT.rev P)), 0 <= tr_max tr.
Proof.
  intros P tr. induction tr as [|ev tr IH]; unfold tr_max in *; cbn [fold_right] in *; [lia|].
  destruct ev; cbv beta iota; lia.
Qed.

Lemma rrp_tr_max_app : forall {P : Type} (a b : list (RelayRunT.rev P)),
  tr_max (a ++ b) = Z.max (tr_max a) (tr_max b).
Proof.
  intros P a b. pose proof (rrp_tr_max_nonneg b) as Hb.
  induction a as [|ev a IH]; unfold tr_max in *; cbn [fold_right app] in *; [lia|].
  rewrite IH. destruct ev; cbv beta iota; lia.
Qed.

(* ================================================================== relay_remove's find *)
(* the entry of fd that find returns is the first one with that fd (the arm's rr_find_first, _remove.v:2162) *)
Lemma rrp_find : forall (es : list rentry) (j0 : nat) (fd : Z),
  (j0 < length es)%nat -> re_fd (nth j0 es relay_remove_b_c.no_entry) = fd ->
  (forall q, (q < j0)%nat -> re_fd (nth q es relay_remove_b_c.no_entry) <> fd) ->
  find (fun e => re_fd e =? fd) es = Some (nth j0 es relay_remove_b_c.no_entry).
Proof.
  induction es as [|e es IH]; intros j0 fd Hj Hf Hq; [cbn [length] in Hj; lia|].
  destruct j0 as [|j0].
  - cbn [nth] in Hf |- *. cbn [find]. rewrite Hf, Z.eqb_refl. reflexivity.
  - pose proof (Hq 0%nat ltac:(lia)) as E. cbn [nth] in E. cbn [find nth].
    rewrite (proj2 (Z.eqb_neq _ _) E).
    apply IH; [cbn [length] in Hj; lia | exact Hf |].
    intros q Hq'. exact (Hq (S q) ltac:(lia)).
Qed.

(* ================================================================== the held keys drain leaves *)
(* a begin line's key and its 5 end bytes are at most the line and its NUL (copied from lib/Prog/SlotPass5M.v:20
   g5m_gesture_begin, which this tree does not build here) *)
Lemma rrp_gesture_begin : forall l x, gesture l = Some (GBegin, x) ->
  Z.of_nat (length x) + 5 <= Z.of_nat (length l) + 1.
Proof.
  intros l x G. unfold gesture in G.
  destruct (list_eqb (firstn 13 l) K_GESTURE && Z.eqb (nth 13 l 0) SPACE && Nat.ltb 13 (length l)); [|discriminate].
  destruct (last_space_from 0 l) as [j|]; [|discriminate].
  destruct (Nat.ltb 13 j); [|discriminate].
  destruct (list_eqb (skipn (S j) l) W_BEGIN) eqn:EB.
  - injection G as EX. subst x. unfold list_eqb in EB.
    destruct (list_eq_dec Z.eq_dec (skipn (S j) l) W_BEGIN) as [Es|]; [|discriminate].
    pose proof (f_equal (@length Z) Es) as LE. rewrite length_skipn in LE. cbn [W_BEGIN length] in LE.
    rewrite length_firstn. lia.
  - destruct (list_eqb (skipn (S j) l) W_END); discriminate.
Qed.

(* gesture_seen's held array (RelayKeys.seen_arr): its keys' bytes with 5 each (ReplyLSRemove3.rm3_kw) grow by at
   most the line and its NUL *)
Lemma rrp_seen_kw : forall H l, rm3_kw (seen_arr H l) <= rm3_kw H + Z.of_nat (length l) + 1.
Proof.
  intros H l. unfold seen_arr. destruct (gesture l) as [[k x]|] eqn:EG; [destruct k|].
  - destruct (index_of x H); [lia|]. unfold rm3_kw. rewrite map_app, zsum_app. cbn [map fold_right].
    pose proof (rrp_gesture_begin l x EG). lia.
  - destruct (index_of x H) as [n|] eqn:EI; [|lia].
    destruct (index_of_some x H n EI) as (a & b & -> & <-).
    pose proof (fr_sum_perm _ (fun y => Z.of_nat (length y) + 5) _ _ (swap_remove_perm [] a x b)) as E.
    unfold rm3_kw. rewrite E. cbn [map fold_right]. lia.
  - lia.
Qed.

Lemma rrp_lines_kw : forall live mx ls no cap H ka j o ha ks,
  rm3_kw (snd (fst (snd (fst (drain_b_c.lines_run live mx no cap H ka ls j o ha ks))))) <=
  rm3_kw H + Z.of_nat (length (with_nul ls)).
Proof.
  intros live mx ls. induction ls as [|l ls IH]; intros no cap H ka j o ha ks.
  - cbn [drain_b_c.lines_run snd fst]. rewrite RelayCap.with_nul_nil_len. lia.
  - cbn [drain_b_c.lines_run]. cbv zeta. cbn [snd fst]. rewrite RelayCap.with_nul_cons_len.
    match goal with |- context [drain_b_c.lines_run live mx ?n ?c (seen_arr H l) ?k ls ?j1 ?o1 ?h1 ?s1] =>
      pose proof (IH n c (seen_arr H l) k j1 o1 h1 s1) as IHr end.
    pose proof (rrp_seen_kw H l). lia.
Qed.

(* over drain's rounds the held keys' bytes grow by at most what g_nout grows by (the relayed lines' bytes) *)
Lemma rrp_drain_kw : forall f live mx s j a,
  rm3_kw (drain_b_c.ds_H (fst (snd (drain_b_c.drain_run f live mx s j a)))) -
    drain_b_c.ds_no (fst (snd (drain_b_c.drain_run f live mx s j a))) <=
  rm3_kw (drain_b_c.ds_H s) - drain_b_c.ds_no s.
Proof.
  intros f live mx. induction f as [|f IH]; intros s j a.
  - cbn [drain_b_c.drain_run snd fst]. lia.
  - cbn [drain_b_c.drain_run]. cbv zeta. destruct (drain_b_c.ds_eintr s).
    + cbn [snd fst].
      match goal with |- context [drain_b_c.drain_run f live mx ?s1 ?j1 ?a1] => pose proof (IH s1 j1 a1) as I1 end.
      cbn [drain_b_c.ds_H drain_b_c.ds_no] in I1. lia.
    + destruct (drain_b_c.ds_pend s) as [|r0 rs].
      { cbn [snd fst drain_b_c.ds_H drain_b_c.ds_no]. lia. }
      match goal with |- context [Z.min ?a ?b <=? 0] => destruct (Z.min a b <=? 0) end.
      { cbn [snd fst drain_b_c.ds_H drain_b_c.ds_no]. lia. }
      match goal with |- context [RelayModel.chunk ?u ?k ?d] =>
        destruct (RelayModel.chunk u k d) as [[u' sk'] rl] end.
      match goal with |- context [drain_b_c.lines_run live mx (drain_b_c.ds_no s) (drain_b_c.ds_ocap s)
                                    (drain_b_c.ds_H s) (drain_b_c.ds_ka s) rl ?j3 ?o ?ha ?ks] =>
        pose proof (rrp_lines_kw live mx rl (drain_b_c.ds_no s) (drain_b_c.ds_ocap s) (drain_b_c.ds_H s)
                      (drain_b_c.ds_ka s) j3 o ha ks) as LW;
        destruct (drain_b_c.lines_run live mx (drain_b_c.ds_no s) (drain_b_c.ds_ocap s) (drain_b_c.ds_H s)
                    (drain_b_c.ds_ka s) rl j3 o ha ks) as [[tl [[oc' H'] ka']] [[o' ha'] ks']] end.
      cbn [snd fst] in LW |- *.
      match goal with |- context [drain_b_c.drain_run f live mx ?s2 ?j4 ?a2] => pose proof (IH s2 j4 a2) as I1 end.
      cbn [drain_b_c.ds_H drain_b_c.ds_no] in I1. lia.
Qed.

(* from g_nout = 0: the keys drain leaves are at most the entry's keys_total and drain's final g_nout *)
Lemma rrp_fin_kw : forall lv mx CAP e h,
  rm3_kw (drain_b_c.ds_H (drain_b_c.drain_fin lv mx 0 CAP e h)) <=
  gestures_end_b_c.keys_total (re_keys e) + drain_b_c.ds_no (drain_b_c.drain_fin lv mx 0 CAP e h).
Proof.
  intros lv mx CAP e h. unfold drain_b_c.drain_fin, drain_b_c.drain_go.
  pose proof (rrp_drain_kw (S (S (length (pending_stream h)))) lv mx (drain_b_c.drain_init 0 CAP e h) 0%nat
                drain_b_c.dadr0) as W.
  change (drain_b_c.ds_H (drain_b_c.drain_init 0 CAP e h)) with (drain_b_c.keys_texts (re_keys e)) in W.
  change (drain_b_c.ds_no (drain_b_c.drain_init 0 CAP e h)) with 0 in W.
  rewrite <- rm3_kt_kw in W. lia.
Qed.

(* ================================================================== the gesture ends' requests *)
(* gestures_end_b_c.keys_end_run: each key's two send_lines (|key| bytes, then the 5 end bytes) from g_nout no, which
   then grows by |key| + 5; each send_line round asks at most 2 * (no + len) (dpre_send_line); the key's free asks
   nothing *)
Lemma rrp_ker : forall live mx (xks : list (Z * RelayRunT.addr YO0i.sptr)) no cap j o M,
  Forall (fun x => 0 <= fst x) xks ->
  2 * (no + fold_right (fun x acc => fst x + 5 + acc) 0 xks) <= M ->
  Forall (dpre_rq M) (fst (gestures_end_b_c.keys_end_run live mx no cap xks j o)).
Proof.
  intros live mx xks. induction xks as [|[xl ka] r IH]; intros no cap j o M HF HM;
    cbn [gestures_end_b_c.keys_end_run fst]; [constructor|].
  apply Forall_cons_iff in HF as [Hx HF]. cbn [fst] in Hx. cbn [fold_right fst] in HM.
  assert (Hr : 0 <= fold_right (fun x acc => fst x + 5 + acc) 0 r).
  { clear -HF. revert HF. induction r as [|[x k] r IHr]; intros HF; cbn [fold_right fst]; [lia|].
    apply Forall_cons_iff in HF as [H1 H2]. cbn [fst] in H1. specialize (IHr H2). lia. }
  apply Forall_app. split.
  - unfold gesture_end_b_c.gesture_end_tr. apply Forall_app. split; apply dpre_send_line; lia.
  - apply Forall_cons; [exact I|]. apply IH; [exact HF | lia].
Qed.

Lemma rrp_ker_w : forall (A : Type) (a0 : A) (H : list (list Z)),
  fold_right (fun x acc => fst x + 5 + acc) 0 (map (fun x => (Z.of_nat (length x), a0)) H) = rm3_kw H.
Proof. intros A a0 H. unfold rm3_kw. induction H as [|x H IH]; cbn [map fold_right fst]; lia. Qed.

(* rr_tr's key run: the held texts' lengths, from g_nout no *)
Lemma rrp_ker_lens : forall live mx (H : list (list Z)) (a0 : RelayRunT.addr YO0i.sptr) no cap j o M,
  2 * (no + rm3_kw H) <= M ->
  Forall (dpre_rq M)
    (fst (gestures_end_b_c.keys_end_run live mx no cap (map (fun x => (Z.of_nat (length x), a0)) H) j o)).
Proof.
  intros live mx H a0 no cap j o M HM. apply rrp_ker.
  - apply Forall_forall. intros y Hy. apply in_map_iff in Hy as (x & <- & _). cbn [fst]. lia.
  - rewrite rrp_ker_w. exact HM.
Qed.

(* ================================================================== the rule *)
Section rrp.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : asyms.

(* conjunct 2 of _remove.v:1971 LS_rm_rr_pre, at the PROPOSED text: the arm's premises and the two rm_rr holds where
   it applies the rule (_remove.v:2398) - rm_regs_base's `0 <= t < OPS_MAX` (:358, Rt at :2353) and entry j0's
   aentry_ok (W_rep.v:125, from HREL at :2356 through W_rep.v:156) *)
Lemma fr_LS_rm_rr_pre_c2 : forall cx t m ly S si h j0,
  fr_LS B cx t m ly S -> fr_RINV cx t m -> rm_at cx m si h j0 ->
  0 <= t < OPS_MAX ->
  Z.of_nat (length (re_U (rm_ent m j0))) <= APARTIAL ->
  tr_max (W_LLVMFuzzerTestOneInput_remove.rm_rr_tr m h) < MMAX.
Proof.
  intros cx t m ly S si h j0 _ HRI Hat Ht HU.
  destruct (rm3_pair cx t m si h j0 HRI Hat) as (HP & HE & Hc & Hn).
  pose proof Hat as (_ & HO & _ & _ & _ & _ & Hj0 & Hfd & Hfirst).
  destruct HP as (_ & _ & _ & Hre & _ & _ & Hexp & _ & _ & Hpe & Hoff). cbn [fst snd] in Hre, Hexp, Hpe, Hoff.
  destruct HE as (_ & _ & _ & _ & Hsk).
  unfold fr_pair_cost in Hc. cbn [fst] in Hc.
  pose proof (fr_keys_total_nonneg (re_keys (rm_ent m j0))) as HKT0.
  pose proof (dpre_keys_le (re_keys (rm_ent m j0))) as Hkl.
  assert (HX0 : 0 <= (if re_skip (rm_ent m j0) =? 0 then Z.of_nat (length (re_U (rm_ent m j0))) else 0))
    by (destruct (re_skip (rm_ent m j0) =? 0); lia).
  assert (EM : WR_MMAX = 1072693248) by reflexivity.
  assert (E26 : 2 ^ 26 = 67108864) by reflexivity.
  assert (Hfind : find (fun e => re_fd e =? hs_fd h) (lm_es m) = Some (rm_ent m j0))
    by (unfold rm_ent; apply rrp_find; [exact Hj0 | exact Hfd | exact Hfirst]).
  unfold W_LLVMFuzzerTestOneInput_remove.rm_rr_tr, rr_tr. cbv beta zeta.
  replace (Z.of_nat (length (lm_O m))) with 0 by (rewrite HO; reflexivity).
  destruct (hs_fd h <? 0); cbv iota; [unfold tr_max; cbn [fold_right]; lia|].
  rewrite Hfind. cbv beta iota zeta.
  destruct (re_eof (rm_ent m j0) =? 0) eqn:Eo; cbv iota.
  - (* open: drain's own trace, then the gesture ends of the keys it leaves, then two frees *)
    apply Z.eqb_eq in Eo.
    assert (HA : tr_max (dr_tr (lm_c m) (lm_mx m) 0 (lm_cap m) (rm_ent m j0) h) < WR_MMAX).
    { destruct (Hre Eo) as (S1 & W1). apply dpre_dr_tr_max.
      - exact HU.
      - destruct (Z.eq_dec (hs_overlong h) 1) as [E|E]; [left; exact E | right]. apply W1. lia.
      - exact Hoff.
      - exact Hexp.
      - lia.
      - unfold SlotInv.WRITE_MAX, OPS_MAX in *. lia. }
    rewrite rrp_tr_max_app.
    match goal with |- Z.max _ (tr_max ?KF) < _ => assert (HB : tr_max KF <= WR_MMAX - 1) end.
    { apply dpre_tr_max; [lia|]. apply Forall_app. split.
      - apply rrp_ker_lens. unfold dr_fin.
        pose proof (rm3_no_fin (dr_live (lm_c m) h) (lm_mx m) (lm_cap m) (rm_ent m j0) h Hoff) as NF.
        pose proof (rrp_fin_kw (dr_live (lm_c m) h) (lm_mx m) (lm_cap m) (rm_ent m j0) h) as KW.
        rewrite (rm3_skip_if (re_skip (rm_ent m j0)) (Z.of_nat (length (re_U (rm_ent m j0)))) Hsk) in NF.
        lia.
      - apply Forall_cons; [exact I|]. apply Forall_cons; [exact I|]. apply Forall_nil. }
    lia.
  - (* at eof: no drain; the gesture ends of the entry's own keys from g_nout = 0, then two frees *)
    rewrite app_nil_l.
    apply (Z.le_lt_trans _ (WR_MMAX - 1)); [|lia].
    apply dpre_tr_max; [lia|]. apply Forall_app. split.
    + apply rrp_ker_lens. cbn [drain_b_c.drain_init drain_b_c.ds_no drain_b_c.ds_H].
      rewrite <- rm3_kt_kw. lia.
    + apply Forall_cons; [exact I|]. apply Forall_cons; [exact I|]. apply Forall_nil.
Qed.

(* conjuncts 1, 2 and 4 of _remove.v:1971 LS_rm_rr_pre at the premises of fr_LS_rm_rr_pre_c2 (1 and 4 are
   ReplyLSRemove3.fr_LS_rm_rr_pre_sizes) *)
Lemma fr_LS_rm_rr_pre_124 : forall cx t m ly S si h j0,
  fr_LS B cx t m ly S -> fr_RINV cx t m -> rm_at cx m si h j0 ->
  0 <= t < OPS_MAX ->
  Z.of_nat (length (re_U (rm_ent m j0))) <= APARTIAL ->
  (re_eof (rm_ent m j0) = 0 ->
     Z.of_nat (length (pending_stream h)) < 2 ^ 26 /\ hl_cap (hs_expected h) < 2 ^ 26 /\
     re_nheld (rm_ent m j0) + Z.of_nat (length (pending_stream h)) < 2 ^ 26) /\
  tr_max (W_LLVMFuzzerTestOneInput_remove.rm_rr_tr m h) < MMAX /\
  mo_ok MT S (W_LLVMFuzzerTestOneInput_remove.rm_rr_cost MT m h).
Proof.
  intros cx t m ly S si h j0 HLS HRI Hat Ht HU.
  destruct (fr_LS_rm_rr_pre_sizes B cx t m ly S si h j0 HLS HRI Hat) as (C1 & C4).
  exact (conj C1 (conj (fr_LS_rm_rr_pre_c2 cx t m ly S si h j0 HLS HRI Hat Ht HU) C4)).
Qed.
End rrp.
