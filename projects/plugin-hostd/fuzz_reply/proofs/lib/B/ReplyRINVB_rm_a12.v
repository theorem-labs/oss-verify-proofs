(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: new file, row G-BRI-rm of a Theorem Labs lane's B owner table (B-TOPX-OWNERS rows 78, 81,
   83, 85, 87).  proves no function (rule 24; kind: model rules): the five remove-arm RINV rules of image B's
   lib/B/W_LLVMFuzzerTestOneInput_top_x.v (B top e43cf0c7bef, the Hypothesis lines 485 RI_rm_found, 500 RI_rm_cnl_pre,
   511 RI_rm_cshe_pre, 521 RI_rm_csd, 530 RI_rm_step) at RINV := ReplyRINVB.fr_RINV, each stated word for word at the
   top_x text with RINV replaced (a Theorem Labs lane's lib/B/ReplyBTop.v Section hypotheses of the same names).
   RELOCATED, not re-proved: every proof is the image-A twin's, moved to lib/B's names, except the two new `_sat`
   lemmas RI_rm_found_sat and RI_rm_step_sat (image A has none for those two rows; they reuse the relocated states).
     - from lib/A/ReplyRINV.v (a working branch 8da615a239d; the same text at 419c9d7c02f):
       RI_rm_found_holds, RI_rm_step_holds and the helpers they read (fr_Forall2_r, fr_Forall2_comb, fr_comb_inj,
       fr_pair_of_open, RI_fds_holds, fr_rm_set_nth_*, fr_nopen_clear, fr_split_nth, fr_remove_perm, fr_combine_*,
       fr_F2_*, fr_sum_perm, fr_keys_total_nonneg, fr_pair_cost_nonneg, fr_ctl_*, fr_bzs_line(s), fr_ru);
     - from lib/A/ReplyRINV_a12.v (a working branch 419c9d7c02f): the state constructions a12_*, the
       `_false` lemmas, the remove-arm helpers (fr_rm_pair, fr_rm_facts, lines_nul_free, upds_nul_free, fr_rm_keys_nz,
       fr_rm_cnl_pre_core, fr_rm_ends, fr_rm_cshe_pre_core, fr_rm_csd_core, ...), the three restated `_holds` and the
       `_sat` lemmas.
   A -> B: the A twins read fr_RINV of lib/A/ReplyRINV.v and that file's copies of _remove.v's model functions; here
   fr_RINV is lib/B/ReplyRINVB.v's and rm_at / rm_ent / rm_kb / rm_rr_ok / rm_cnl_ok / rm_cshe_ok / rm_A1 / rm_mk /
   rm_cev / rm_set_nth are lib/B/W_LLVMFuzzerTestOneInput_remove.v's own, and A's rm_capb (lib/A/ReplyRINV.v's copy
   of lib/A/W_check_no_loss.v capb) is lib/B/W_contract.v capb.
   Each pair has the same text word for word (checked at e43cf0c7bef against lib/A at 419c9d7c02f: fr_pair_cost ..
   fr_RINV; rm_k' .. rm_cshe_ok; W_contract.v sl_live sl_ctl sl_O dr_lines dr_tot dr_live dr_fin dr_ctl sl_sends ge_bytes
   dr_rel capb; _cut.v OPS_MAX in_byte picks nopen pick; LFCX has the same ten fields), so no proof step changes.
   Imports are A's with lib/A -> lib/B as lib/B/ReplyRINVB.v swaps them.
   No image address is read: every numeral is a model constant of fr_RINV's text (FIRST_FD 100, 4 slots, CLIENT_FD 3,
   op modulus 10, 2 ^ 22 / 2 ^ 24 / 2 ^ 26 bounds, ReplyRINVB.v's CONSTANT-SWAP TABLE gives each B value) or a byte /
   length of a constructed state.
   RESULT at the B top text:
     RI_rm_found, RI_rm_step: PROVED (RI_rm_found_holds, RI_rm_step_holds).
     RI_rm_cnl_pre, RI_rm_cshe_pre, RI_rm_csd: FALSE for fr_RINV as it is defined (STOP; never weakened).  These are
     the texts image A had before its restatement (A integ bb9dae5d905; restated on A at a working branch
     3f40808c334).  RI_rm_cnl_pre_top / RI_rm_cshe_pre_top / RI_rm_csd_top copy the B top texts, and each `_top_false`
     proves the negation from a state that meets fr_RINV and the rule's premises and not its conclusion:
     - RI_rm_cnl_pre: fr_RINV does not bound the held count below 2 ^ 22.  lm_gn m = 0, one open slot 0 holding h, its
       entry at eof (h1 = h), 2 ^ 22 held records with distinct 3-byte texts and one key each; keys_total = 2 ^ 25 <=
       lm_k m < c_n cx < 2 ^ 26.  hl_n (hs_held h1) + count_begin (texts (hs_expected h1)) = 2 ^ 22, not < 2 ^ 22.
     - RI_rm_cshe_pre: fr_RINV does not say the held texts have no NUL byte.  lm_gn m = 0, held list [(0, [NUL])], one
       key of text [NUL]; O2 = [NUL] ++ " end\0", rm_A1 m h1 = 0, CheckRep.ends_run's first line is empty: None.
     - RI_rm_csd: fr_RINV does not say lm_gn m is 0 or 1.  lm_gn m = 2, held list [(0, "a")]; O2 = "a end\0" (6 bytes),
       rm_cshe_ok's gone branch with cc = 0, rm_A1 m h1 = 0: 0 + 0 <> 6.
     With the arm's premise added (A's restatement, fr_RINV unchanged) they hold: RI_rm_cnl_pre_K14_holds (every key
     text of the table >= 14 bytes; _remove.v rm_mfacts conjunct 2), RI_rm_cshe_pre_nz_holds (H' NUL-free),
     RI_rm_csd_gn_holds (0 <= lm_gn m <= 1).
   Every row has a `_sat` lemma (VERIFY rule 10): from any call context, a state meeting every premise. *)
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
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YC5d.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require YCfn.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib Require Import ZTraceSpec.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import
W_syms W_listing W_place W_tbl W_kit W_pl W_img W_journal.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import
HarnessRep RelayRep CheckRep RelayKeys RelayModel ListRep.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require
RelayRunT drain_b_c gestures_end_b_c relay_remove_b_c relay_instance_gone_b_c SlotInv SlotReads SlotPass2Aux send_line_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_rep W_contract W_sites W_frame.
(* RelocB's sink-instance guard (after the Import of YE2k), as lib/B/ReplyRINVB.v Requires it *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require ReplyGuardB.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_LLVMFuzzerTestOneInput_cut.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_LLVMFuzzerTestOneInput_remove.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import ReplyRINVB.
Import ListNotations.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

Section rinvb_rm_a12.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.

(* ================================================================== helpers of lib/A/ReplyRINV.v (A twins), relocated *)
Lemma fr_Forall2_r : forall (X Y : Type) (R : X -> Y -> Prop) l1 l2,
  Forall2 R l1 l2 -> forall y, In y l2 -> exists x, In x l1 /\ R x y.
Proof.
  intros X Y R l1 l2 H. induction H as [|x y l1 l2 Hxy _ IH]; intros z Hz; [destruct Hz|].
  destruct Hz as [<- | Hz]; [exists x; split; [left; reflexivity | exact Hxy]|].
  destruct (IH z Hz) as (x' & Hx' & HR). exists x'. split; [right; exact Hx' | exact HR].
Qed.
Lemma fr_Forall2_comb : forall (X Y : Type) (R : X -> Y -> Prop) l1 l2,
  Forall2 R l1 l2 -> forall y, In y l2 -> exists x, In (x, y) (combine l1 l2) /\ R x y.
Proof.
  intros X Y R l1 l2 H. induction H as [|x y l1 l2 Hxy _ IH]; intros z Hz; [destruct Hz|].
  destruct Hz as [<- | Hz]; [exists x; split; [left; reflexivity | exact Hxy]|].
  destruct (IH z Hz) as (x' & Hx' & HR). exists x'. split; [right; exact Hx' | exact HR].
Qed.
(* two entries of the table with the same fd are one row, so their sources are one *)
Lemma fr_comb_inj : forall (Y : Type) (es : list rentry) (hj : list Y), List.NoDup (map re_fd es) ->
  forall e1 p1 e2 p2, In (e1, p1) (combine es hj) -> In (e2, p2) (combine es hj) -> re_fd e1 = re_fd e2 ->
  p1 = p2.
Proof.
  intros Y es. induction es as [|x es IH]; intros hj Hnd e1 p1 e2 p2 H1 H2 Hf; [destruct H1|].
  destruct hj as [|y hj]; [destruct H1|]. cbn [map] in Hnd. apply NoDup_cons_iff in Hnd as [Hx Hnd].
  cbn [combine In] in H1, H2.
  destruct H1 as [E1 | H1]; destruct H2 as [E2 | H2].
  - injection E1 as <- <-. injection E2 as <- <-. reflexivity.
  - injection E1 as <- <-. exfalso. apply Hx. rewrite Hf. apply in_map. eapply in_combine_l. exact H2.
  - injection E2 as <- <-. exfalso. apply Hx. rewrite <- Hf. apply in_map. eapply in_combine_l. exact H1.
  - exact (IH hj Hnd e1 p1 e2 p2 H1 H2 Hf).
Qed.
(* an open slot is some entry's source *)
Lemma fr_pair_of_open : forall m t hj i h, Forall2 (fr_pair_ok m t) (lm_es m) hj ->
  (forall i, (i < 4)%nat -> SlotInv.slot_open hj i = false -> nth i (lm_hs m) None = None) ->
  (i < 4)%nat -> nth i (lm_hs m) None = Some h ->
  exists e p, In (e, p) (combine (lm_es m) hj) /\ fr_pair_ok m t e p /\ snd p = i /\ fst p = h.
Proof.
  intros m t hj i h HF Hcl Hi Hh.
  destruct (SlotInv.slot_open hj i) eqn:Ho; [|rewrite (Hcl i Hi Ho) in Hh; discriminate Hh].
  unfold SlotInv.slot_open in Ho. apply existsb_exists in Ho as (x & Hx & Hxi).
  apply Nat.eqb_eq in Hxi. subst x. apply in_map_iff in Hx as (p & Hpi & Hp).
  destruct (fr_Forall2_comb _ _ _ _ _ HF p Hp) as (e & Hin & HR).
  exists e, p. split; [exact Hin|]. split; [exact HR|]. split; [exact Hpi|].
  destruct HR as (_ & Hn & _). rewrite Hpi, Hh in Hn. injection Hn as Ef. exact (eq_sym Ef).
Qed.
(* _drain.v RI_fds (lib/A/ReplyRINV.v RI_fds_obl, the same text): two open slots have distinct fds *)
Lemma RI_fds_holds : forall cx t m i1 i2 h1 h2,
  fr_RINV cx t m -> (i1 < 4)%nat -> (i2 < 4)%nat -> i1 <> i2 ->
  nth i1 (lm_hs m) None = Some h1 -> nth i2 (lm_hs m) None = Some h2 -> hs_fd h1 <> hs_fd h2.
Proof.
  intros cx t m i1 i2 h1 h2 (_ & HR & _) Hi1 Hi2 Hne Hh1 Hh2 Hf.
  destruct HR as (_ & Hnd & _ & _ & hj & HF & _ & Hcl & _). apply NoDup_ListNoDup in Hnd.
  destruct (fr_pair_of_open m t hj i1 h1 HF Hcl Hi1 Hh1) as (e1 & p1 & Hin1 & HR1 & Hs1 & Hf1).
  destruct (fr_pair_of_open m t hj i2 h2 HF Hcl Hi2 Hh2) as (e2 & p2 & Hin2 & HR2 & Hs2 & Hf2).
  apply Hne. rewrite <- Hs1, <- Hs2. f_equal.
  apply (fr_comb_inj _ (lm_es m) hj Hnd e1 p1 e2 p2 Hin1 Hin2).
  destruct HR1 as (_ & _ & E1 & _). destruct HR2 as (_ & _ & E2 & _).
  rewrite <- E1, <- E2, Hf1, Hf2. exact Hf.
Qed.
(* ---- ARM_remove's step (fuzz_reply.c:619-631): relay_remove drops the entry j0 of slot si's fd, moving the
   table's last entry into its place (relay_remove_b_c.remove_at), and source_reset closes slot si *)
Lemma fr_rm_set_nth_length : forall (T : Type) n (x : T) l, length (rm_set_nth n x l) = length l.
Proof.
  intros T n x l. revert n. induction l as [|y l IH]; intros [|n]; cbn [rm_set_nth length]; try reflexivity.
  rewrite IH. reflexivity.
Qed.
Lemma fr_rm_set_nth_same : forall (T : Type) n (x : T) l d, (n < length l)%nat -> nth n (rm_set_nth n x l) d = x.
Proof.
  intros T n x l. revert n. induction l as [|y l IH]; intros [|n] d Hn; cbn [length] in Hn; try lia;
    cbn [rm_set_nth nth]; [reflexivity | apply IH; lia].
Qed.
Lemma fr_rm_set_nth_other : forall (T : Type) n p (x : T) l d, n <> p -> nth p (rm_set_nth n x l) d = nth p l d.
Proof.
  intros T n. induction n as [|n IH]; intros [|p] x l d Hnp; destruct l as [|y l];
    cbn [rm_set_nth nth]; try reflexivity; try lia.
  apply IH. lia.
Qed.
Lemma fr_nopen_clear : forall hs i x, nth i hs None = Some x -> (i < length hs)%nat ->
  nopen (rm_set_nth i None hs) + 1 = nopen hs.
Proof.
  intros hs i x. unfold nopen. revert i. induction hs as [|o hs IH]; intros [|i] Hn Hi;
    cbn [length] in Hi; try lia.
  - cbn [nth] in Hn. subst o. cbn [rm_set_nth List.filter length]. lia.
  - cbn [nth] in Hn. pose proof (IH i Hn ltac:(lia)) as Hih.
    destruct o; cbn [rm_set_nth List.filter length]; lia.
Qed.
(* remove_at i l is l without its i-th element, up to order *)
Lemma fr_split_nth : forall (T : Type) (l : list T) i d, (i < length l)%nat ->
  l = firstn i l ++ nth i l d :: skipn (S i) l.
Proof.
  intros T l. induction l as [|x l IH]; intros [|i] d Hi; cbn [length] in Hi; try lia.
  - reflexivity.
  - cbn [firstn nth skipn app]. f_equal. apply IH. lia.
Qed.
Lemma fr_remove_perm : forall (T : Type) (l : list T) i d, (i < length l)%nat ->
  Permutation l (nth i l d :: relay_remove_b_c.remove_at i l).
Proof.
  intros T l i d Hi. unfold relay_remove_b_c.remove_at.
  destruct (List.rev l) as [|a r] eqn:Er.
  - apply (f_equal (@length T)) in Er. rewrite length_rev in Er. cbn [length] in Er. lia.
  - assert (El : l = List.rev r ++ [a]) by (rewrite <- (rev_involutive l), Er; reflexivity).
    subst l. rewrite length_app in Hi. cbn [length] in Hi.
    cbv beta iota zeta.
    destruct (Nat.eqb i (length (List.rev r))) eqn:Ei; cbv iota.
    + apply Nat.eqb_eq in Ei. rewrite app_nth2 by lia. rewrite Ei, Nat.sub_diag. cbn [nth].
      apply Permutation_sym, Permutation_cons_append.
    + apply Nat.eqb_neq in Ei. rewrite app_nth1 by lia.
      rewrite (fr_split_nth _ (List.rev r) i d ltac:(lia)) at 1.
      rewrite <- app_assoc, <- app_comm_cons.
      eapply Permutation_trans; [apply Permutation_sym, Permutation_middle|].
      apply perm_skip, Permutation_app_head, Permutation_sym, Permutation_cons_append.
Qed.
Lemma fr_combine_app : forall (X Y : Type) (a : list X) (b : list Y) c d, length a = length b ->
  combine (a ++ c) (b ++ d) = combine a b ++ combine c d.
Proof.
  intros X Y a. induction a as [|x a IH]; intros [|y b] c d Hl; cbn [length] in Hl; try discriminate Hl.
  - reflexivity.
  - cbn [app combine]. f_equal. apply IH. lia.
Qed.
Lemma fr_combine_rev : forall (X Y : Type) (l1 : list X) (l2 : list Y), length l1 = length l2 ->
  List.rev (combine l1 l2) = combine (List.rev l1) (List.rev l2).
Proof.
  intros X Y l1. induction l1 as [|x l1 IH]; intros [|y l2] Hl; cbn [length] in Hl; try discriminate Hl.
  - reflexivity.
  - cbn [combine List.rev]. rewrite IH by lia. rewrite fr_combine_app by (rewrite !length_rev; lia).
    reflexivity.
Qed.
Lemma fr_combine_firstn : forall (X Y : Type) n (l1 : list X) (l2 : list Y),
  combine (firstn n l1) (firstn n l2) = firstn n (combine l1 l2).
Proof.
  intros X Y n. induction n as [|n IH]; intros l1 l2; [reflexivity|].
  destruct l1 as [|x l1], l2 as [|y l2]; cbn [firstn combine]; try reflexivity.
  f_equal. apply IH.
Qed.
Lemma fr_combine_skipn : forall (X Y : Type) n (l1 : list X) (l2 : list Y),
  combine (skipn n l1) (skipn n l2) = skipn n (combine l1 l2).
Proof.
  intros X Y n. induction n as [|n IH]; intros l1 l2; [reflexivity|].
  destruct l1 as [|x l1], l2 as [|y l2]; cbn [skipn combine].
  - reflexivity.
  - reflexivity.
  - destruct (skipn n l1); reflexivity.
  - apply IH.
Qed.
(* the table and its sources lose the same row *)
Lemma fr_combine_remove : forall (X Y : Type) i (l1 : list X) (l2 : list Y), length l1 = length l2 ->
  combine (relay_remove_b_c.remove_at i l1) (relay_remove_b_c.remove_at i l2) =
  relay_remove_b_c.remove_at i (combine l1 l2).
Proof.
  intros X Y i l1 l2 Hl. unfold relay_remove_b_c.remove_at.
  rewrite (fr_combine_rev _ _ l1 l2 Hl).
  assert (Hr : length (List.rev l1) = length (List.rev l2)) by (rewrite !length_rev; exact Hl).
  destruct (List.rev l1) as [|a1 r1], (List.rev l2) as [|a2 r2]; cbn [length] in Hr; try discriminate Hr.
  - reflexivity.
  - cbn [combine]. assert (Hr' : length r1 = length r2) by lia.
    rewrite (fr_combine_rev _ _ r1 r2 Hr').
    assert (E1 : length (combine (List.rev r1) (List.rev r2)) = length (List.rev r1))
      by (rewrite length_combine, !length_rev; lia).
    assert (E2 : length (List.rev r2) = length (List.rev r1)) by (rewrite !length_rev; lia).
    rewrite E1, E2.
    destruct (Nat.eqb i (length (List.rev r1))); [reflexivity|].
    rewrite fr_combine_app by (rewrite !length_firstn, !length_rev; lia). cbn [combine].
    rewrite fr_combine_firstn, fr_combine_skipn. reflexivity.
Qed.
Lemma fr_F2_nth : forall (T1 T2 : Type) (R : T1 -> T2 -> Prop) l1 l2, Forall2 R l1 l2 ->
  forall i d1 d2, (i < length l1)%nat -> R (nth i l1 d1) (nth i l2 d2).
Proof.
  intros T1 T2 R l1 l2 H. induction H as [|x y l1 l2 Hxy _ IH]; intros [|i] d1 d2 Hi; cbn [length] in Hi;
    try lia; cbn [nth]; [exact Hxy | apply IH; lia].
Qed.
Lemma fr_combine_of_F2 : forall (T1 T2 : Type) (R : T1 -> T2 -> Prop) l1 l2, Forall2 R l1 l2 ->
  forall q, In q (combine l1 l2) -> R (fst q) (snd q).
Proof.
  intros T1 T2 R l1 l2 H. induction H as [|x y l1 l2 Hxy _ IH]; intros q Hq; cbn [combine In] in Hq;
    [destruct Hq|].
  destruct Hq as [<- | Hq]; [exact Hxy | exact (IH q Hq)].
Qed.
Lemma fr_F2_of_combine : forall (T1 T2 : Type) (R : T1 -> T2 -> Prop) l1 l2, length l1 = length l2 ->
  (forall q, In q (combine l1 l2) -> R (fst q) (snd q)) -> Forall2 R l1 l2.
Proof.
  intros T1 T2 R l1. induction l1 as [|x l1 IH]; intros [|y l2] Hl Hq; cbn [length] in Hl; try discriminate Hl.
  - constructor.
  - constructor.
    + exact (Hq (x, y) (or_introl eq_refl)).
    + apply IH; [lia | intros q Hin; apply Hq; right; exact Hin].
Qed.
Lemma fr_sum_perm : forall (T : Type) (f : T -> Z) l l', Permutation l l' ->
  fold_right Z.add 0 (map f l) = fold_right Z.add 0 (map f l').
Proof. intros T f l l' H. induction H; cbn [map fold_right]; lia. Qed.
Lemma fr_keys_total_nonneg : forall ks, 0 <= gestures_end_b_c.keys_total ks.
Proof. unfold gestures_end_b_c.keys_total. induction ks as [|k ks IH]; cbn [fold_right]; lia. Qed.
Lemma fr_pair_cost_nonneg : forall e p, 0 <= fr_pair_cost e p.
Proof.
  intros e p. unfold fr_pair_cost. pose proof (fr_keys_total_nonneg (re_keys e)).
  destruct (re_skip e =? 0); lia.
Qed.
(* the controller's flags against g_gone (fr_gone's text) through the sends: send_line keeps g_client and
   g_send_dead, and sets g_client_broken only from g_send_dead when the send is not off (send_off: closed, broken or
   empty; W_contract.v sl_ctl, dr_ctl; send_line_c.v:21) *)
Definition fr_ctl_ok (gn : Z) (c : ctl) : Prop :=
  (gn = 0 -> ct_cl c = 3 /\ ct_br c = 0 /\ ct_dd c = 0) /\ (gn = 1 -> ct_cl c = -1 \/ ct_br c = 1 \/ ct_dd c = 1).
Lemma fr_ctl_step : forall gn c c', ct_cl c' = ct_cl c -> ct_dd c' = ct_dd c ->
  (ct_br c' = ct_br c \/ (ct_br c' = ct_dd c /\ ct_br c <> 1)) -> fr_ctl_ok gn c -> fr_ctl_ok gn c'.
Proof.
  intros gn c c' E1 E2 E3 (G0 & G1). unfold fr_ctl_ok. rewrite E1, E2. split.
  - intros Hg. destruct (G0 Hg) as (A1 & A2 & A3).
    destruct E3 as [E3 | (E3 & _)]; rewrite E3; [exact (conj A1 (conj A2 A3)) | exact (conj A1 (conj A3 A3))].
  - intros Hg. destruct (G1 Hg) as [A1 | [A2 | A3]]; [left; exact A1 | | right; right; exact A3].
    destruct E3 as [E3 | (_ & N)]; [right; left; rewrite E3; exact A2 | contradiction].
Qed.
Lemma fr_ctl_sl : forall gn c len, fr_ctl_ok gn c -> fr_ctl_ok gn (sl_ctl c len).
Proof.
  intros gn c len Hc. apply (fr_ctl_step gn c); [reflexivity | reflexivity | | exact Hc].
  unfold sl_ctl. cbn [ct_br].
  destruct (send_line_c.send_off (ct_cl c) (ct_br c) len) eqn:E; [left; reflexivity|].
  right. split; [reflexivity|]. unfold send_line_c.send_off in E.
  apply orb_false_iff in E as [E _]. apply orb_false_iff in E as [_ E]. apply Z.eqb_neq in E. exact E.
Qed.
Lemma fr_ctl_dr : forall gn c h ev, fr_ctl_ok gn c -> fr_ctl_ok gn (dr_ctl c h ev).
Proof.
  intros gn c h ev Hc. apply (fr_ctl_step gn c); [reflexivity | reflexivity | | exact Hc].
  unfold dr_ctl. cbn [ct_br].
  destruct (send_line_c.send_off (ct_cl c) (ct_br c) (dr_tot h)) eqn:E; [left; reflexivity|].
  right. split; [reflexivity|]. unfold send_line_c.send_off in E.
  apply orb_false_iff in E as [E _]. apply orb_false_iff in E as [_ E]. apply Z.eqb_neq in E. exact E.
Qed.
Lemma fr_ctl_sends : forall gn mx Bs c O cap c' O' cap', fr_ctl_ok gn c ->
  sl_sends mx c O cap Bs = (c', O', cap') -> fr_ctl_ok gn c'.
Proof.
  intros gn mx Bs. induction Bs as [|Bl r IH]; intros c O cap c' O' cap' Hc Hs; cbn [sl_sends] in Hs.
  - assert (E : c = c') by exact (f_equal (fun q => fst (fst q)) Hs). subst c'. exact Hc.
  - exact (IH _ _ _ c' O' cap' (fr_ctl_sl gn c _ Hc) Hs).
Qed.
Lemma fr_bzs_line : forall l, SlotReads.zrange l -> bzs (map (Z_to_bv 8) l) = l.
Proof.
  induction l as [|z l IH]; intros Hl; [reflexivity|]. apply Forall_cons_iff in Hl as [Hz Hl].
  unfold bzs in *. cbn [map]. rewrite SlotReads.bz_lit by exact Hz. f_equal. apply IH. exact Hl.
Qed.
Lemma fr_bzs_lines : forall Ls, Forall SlotReads.zrange Ls -> map bzs (map (map (Z_to_bv 8)) Ls) = Ls.
Proof.
  induction Ls as [|l Ls IH]; intros H; [reflexivity|]. apply Forall_cons_iff in H as [H1 H2]. cbn [map].
  rewrite fr_bzs_line by exact H1. f_equal. apply IH. exact H2.
Qed.
(* the entry with re_used replaced by its line's length: SlotInv.pair_cost of it is fr_pair_cost *)
Definition fr_ru (e : rentry) : rentry :=
  RE (re_fd e) (re_eof e) (re_skip e) (re_pad1 e) (re_buf e) (Z.of_nat (length (re_U e))) (re_cap e) (re_hp e)
     (re_kh e) (re_pad2 e) (re_keys e) (re_U e) (re_junk e).

(* B top_x :485 RI_rm_found at RINV := ReplyRINVB.fr_RINV (A twin: lib/A/ReplyRINV.v RI_rm_found_holds).  An open
   slot is some entry's source (fr_pair_of_open); that entry has the slot's fd. *)
Lemma RI_rm_found_holds : forall cx t m si h,
  ReplyRINVB.fr_RINV cx t m -> 0 <= lm_k m < c_n cx -> lm_O m = [] -> in_byte cx (lm_k m) mod 10 = 4 ->
  pick (lm_hs m) (W_LLVMFuzzerTestOneInput_remove.rm_kb cx m) = Some si -> nth si (lm_hs m) None = Some h ->
  exists j, (j < length (lm_es m))%nat /\ re_fd (W_LLVMFuzzerTestOneInput_remove.rm_ent m j) = hs_fd h.
Proof.
  intros cx t m si h (_ & HR & _ & _) _ _ _ _ Hh.
  destruct HR as (Hlen & _ & _ & _ & hj & HF & _ & Hcl & _).
  assert (Hsi : (si < 4)%nat).
  { destruct (Nat.lt_ge_cases si 4) as [H | H]; [exact H|].
    rewrite nth_overflow in Hh by lia. discriminate Hh. }
  destruct (fr_pair_of_open m t hj si h HF Hcl Hsi Hh) as (e & p & Hin & HRp & _ & Hfst).
  assert (He : In e (lm_es m)) by (eapply in_combine_l; exact Hin).
  apply (In_nth (lm_es m) e relay_remove_b_c.no_entry) in He as (j & Hj & Hnj).
  exists j. split; [exact Hj|]. unfold rm_ent. rewrite Hnj.
  destruct HRp as (_ & _ & Hfd & _). rewrite <- Hfd, Hfst. reflexivity.
Qed.

(* remove-s2 _remove.v:5393: the counting invariant loses one open slot and gains one operation; the pairing
   loses slot si's row (the row at j0: slot si holds entry j0's fd, open slots' fds are distinct); the cost drops
   by that row's; the flags pass through drain's and the gesture ends' sends.  out2, ev5, O2 and cap2 are not
   read. *)
Lemma RI_rm_step_holds : forall cx t m si h j0 e1 h1 ev LB c2 O2 cap2 out2 E' H' H'' ds cc ev5,
  ReplyRINVB.fr_RINV cx t m -> W_LLVMFuzzerTestOneInput_remove.rm_at cx m si h j0 ->
  W_LLVMFuzzerTestOneInput_remove.rm_rr_ok m h j0 e1 h1 ev LB c2 O2 cap2 -> W_LLVMFuzzerTestOneInput_remove.rm_cnl_ok h1 E' H' ->
  W_LLVMFuzzerTestOneInput_remove.rm_cshe_ok m (set_exp_held h1 E' H') O2 (W_LLVMFuzzerTestOneInput_remove.rm_A1 m h1) H'' ds cc ->
  ReplyRINVB.fr_RINV cx (t + 1) (W_LLVMFuzzerTestOneInput_remove.rm_mk cx m si None j0 (W_LLVMFuzzerTestOneInput_remove.rm_cev c2 ev5) O2 cap2 out2).
Proof.
  intros cx t m si h j0 e1 h1 ev LB c2 O2 cap2 out2 E' H' H'' ds cc ev5 HRI Hat Hrr _ _.
  pose proof HRI as ((HC & Hnfd) & HR & Hn & HG).
  destruct HR as (Hlen & Hnd & Hrng & Hent & hj & HF & HNDs & Hcl & Hc & Hcn).
  destruct Hat as (_ & _ & _ & _ & Hsi & Hh & Hj0 & Hfd0 & _).
  pose proof (Forall2_length HF) as Hlh.
  assert (Hj0h : (j0 < length hj)%nat) by lia.
  assert (Hk : lm_k m <= rm_k' cx m) by (unfold rm_k'; destruct (lm_k m + 1 <? c_n cx); lia).
  (* the row at j0 is slot si's *)
  assert (Hs0 : snd (nth j0 hj (h, si)) = si).
  { pose proof (fr_F2_nth _ _ _ _ _ HF j0 relay_remove_b_c.no_entry (h, si) Hj0) as (H4 & Hn0 & Hf0 & _).
    destruct (Nat.eq_dec (snd (nth j0 hj (h, si))) si) as [E | Ne]; [exact E | exfalso].
    apply (RI_fds_holds cx t m _ si _ h HRI H4 Hsi Ne Hn0 Hh). rewrite Hf0. exact Hfd0. }
  pose proof (fr_remove_perm _ hj j0 (h, si) Hj0h) as Hperm.
  pose proof (fr_remove_perm _ (lm_es m) j0 relay_remove_b_c.no_entry Hj0) as Hperm_es.
  (* no other row follows slot si *)
  assert (HNDs2 : List.NoDup (map snd (nth j0 hj (h, si) :: relay_remove_b_c.remove_at j0 hj))).
  { assert (Hpm : Permutation (map snd hj) (map snd (nth j0 hj (h, si) :: relay_remove_b_c.remove_at j0 hj)))
      by (apply Permutation_map; exact Hperm).
    eapply Permutation_NoDup; [exact Hpm | exact (proj1 (NoDup_ListNoDup _) HNDs)]. }
  cbn [map] in HNDs2. apply NoDup_cons_iff in HNDs2 as [Hni HNDs2].
  assert (Hother : forall y, In y (relay_remove_b_c.remove_at j0 hj) -> snd y <> si).
  { intros y Hy E. apply Hni. rewrite Hs0, <- E. apply in_map. exact Hy. }
  (* the new table and its sources, row by row *)
  assert (Hcomb : combine (relay_remove_b_c.remove_at j0 (lm_es m)) (relay_remove_b_c.remove_at j0 hj) =
                  relay_remove_b_c.remove_at j0 (combine (lm_es m) hj)) by exact (fr_combine_remove _ _ j0 _ _ Hlh).
  assert (HjC : (j0 < length (combine (lm_es m) hj))%nat) by (rewrite length_combine; lia).
  pose proof (fr_remove_perm _ (combine (lm_es m) hj) j0 (relay_remove_b_c.no_entry, (h, si)) HjC) as HpermC.
  assert (HlenR : length (relay_remove_b_c.remove_at j0 (lm_es m)) = length (relay_remove_b_c.remove_at j0 hj)).
  { pose proof Hperm as L1. pose proof Hperm_es as L2.
    apply Permutation_length in L1. apply Permutation_length in L2. cbn [length] in L1, L2. lia. }
  assert (HF' : Forall2 (fr_pair_ok (rm_mk cx m si None j0 (rm_cev c2 ev5) O2 cap2 out2) (t + 1))
                  (relay_remove_b_c.remove_at j0 (lm_es m)) (relay_remove_b_c.remove_at j0 hj)).
  { apply fr_F2_of_combine; [exact HlenR|]. intros [qe qp] Hq.
    assert (Hq0 : In (qe, qp) (combine (lm_es m) hj)).
    { rewrite Hcomb in Hq. eapply Permutation_in; [apply Permutation_sym; exact HpermC | right; exact Hq]. }
    pose proof (fr_combine_of_F2 _ _ _ _ _ HF (qe, qp) Hq0) as Hpq. cbn [fst snd] in Hpq |- *.
    assert (Hqp : In qp (relay_remove_b_c.remove_at j0 hj)) by (eapply in_combine_r; exact Hq).
    assert (Hsq : si <> snd qp) by (intros E; exact (Hother qp Hqp (eq_sym E))).
    destruct Hpq as (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11).
    unfold fr_pair_ok. cbn [rm_mk lm_hs]. rewrite (fr_rm_set_nth_other _ si (snd qp) _ _ _ Hsq).
    unfold SlotInv.WRITE_MAX in *.
    refine (conj H1 (conj H2 (conj H3 (conj H4 (conj H5 (conj H6 (conj H7 (conj H8 (conj H9
      (conj _ H11)))))))))). lia. }
  assert (Hnd' : NoDup (map re_fd (relay_remove_b_c.remove_at j0 (lm_es m)))).
  { apply NoDup_ListNoDup.
    assert (Hpm : Permutation (map re_fd (lm_es m))
                    (map re_fd (nth j0 (lm_es m) relay_remove_b_c.no_entry :: relay_remove_b_c.remove_at j0 (lm_es m))))
      by (apply Permutation_map; exact Hperm_es).
    assert (X : List.NoDup (map re_fd (nth j0 (lm_es m) relay_remove_b_c.no_entry ::
                                        relay_remove_b_c.remove_at j0 (lm_es m))))
      by (eapply Permutation_NoDup; [exact Hpm | exact (proj1 (NoDup_ListNoDup _) Hnd)]).
    cbn [map] in X. apply NoDup_cons_iff in X as [_ X]. exact X. }
  assert (HFa : forall P : rentry -> Prop, Forall P (lm_es m) -> Forall P (relay_remove_b_c.remove_at j0 (lm_es m))).
  { intros P HP. rewrite Forall_forall in HP |- *. intros x Hx. apply HP.
    eapply Permutation_in; [apply Permutation_sym; exact Hperm_es | right; exact Hx]. }
  (* the cost drops by the removed row's *)
  assert (Hcr : fr_cost (relay_remove_b_c.remove_at j0 (lm_es m)) (relay_remove_b_c.remove_at j0 hj)
                <= fr_cost (lm_es m) hj).
  { unfold fr_cost. rewrite Hcomb.
    rewrite (fr_sum_perm _ (fun q => fr_pair_cost (fst q) (snd q)) _ _ HpermC). cbn [map fold_right].
    pose proof (fr_pair_cost_nonneg (fst (nth j0 (combine (lm_es m) hj) (relay_remove_b_c.no_entry, (h, si))))
      (snd (nth j0 (combine (lm_es m) hj) (relay_remove_b_c.no_entry, (h, si))))). lia. }
  split; [|split; [|split; [exact Hn|]]].
  - unfold fr_count, rm_mk. cbn [lm_nfd lm_hs].
    pose proof (fr_nopen_clear _ _ _ Hh ltac:(lia)) as Hop. lia.
  - unfold fr_relay. cbn [rm_mk lm_hs lm_es lm_nfd lm_k].
    split; [rewrite fr_rm_set_nth_length; exact Hlen|].
    split; [exact Hnd'|]. split; [exact (HFa _ Hrng)|]. split; [exact (HFa _ Hent)|].
    exists (relay_remove_b_c.remove_at j0 hj).
    split; [exact HF'|]. split; [exact (proj2 (NoDup_ListNoDup _) HNDs2)|].
    split.
    { intros j Hj Ho. destruct (Nat.eq_dec j si) as [-> | Ne].
      - apply fr_rm_set_nth_same. lia.
      - rewrite (fr_rm_set_nth_other _ si j _ _ _ (not_eq_sym Ne)). apply (Hcl j Hj).
        destruct (SlotInv.slot_open hj j) eqn:Eo; [exfalso | reflexivity].
        unfold SlotInv.slot_open in Eo, Ho. apply existsb_exists in Eo as (x & Hx & Hxj).
        apply Nat.eqb_eq in Hxj. subst x. apply in_map_iff in Hx as (y & Hyj & Hy).
        assert (Hy' : In y (nth j0 hj (h, si) :: relay_remove_b_c.remove_at j0 hj))
          by (eapply Permutation_in; [exact Hperm | exact Hy]).
        destruct Hy' as [Ey | Hy'].
        + apply Ne. rewrite <- Hyj, <- Ey. exact Hs0.
        + assert (Ht : existsb (Nat.eqb j) (map snd (relay_remove_b_c.remove_at j0 hj)) = true).
          { apply existsb_exists. exists j. split; [|apply Nat.eqb_refl].
            apply in_map_iff. exists y. split; [exact Hyj | exact Hy']. }
          rewrite Ho in Ht. discriminate Ht. }
    split; lia.
  - change (fr_ctl_ok (lm_gn m) c2).
    destruct Hrr as [_ Hs]. eapply fr_ctl_sends; [|exact Hs].
    destruct (re_eof (rm_ent m j0) =? 0); [apply fr_ctl_dr; exact HG | exact HG].
Qed.

(* ---- the cost bound reaches every row: a row's cost is at most the table's (the rows' costs are >= 0) *)
Lemma fr_a12_sum_nonneg : forall (l : list (rentry * (hsrc * nat))),
  0 <= fold_right Z.add 0 (map (fun q => fr_pair_cost (fst q) (snd q)) l).
Proof.
  induction l as [|q l IH]; cbn [map fold_right]; [lia|].
  pose proof (fr_pair_cost_nonneg (fst q) (snd q)). lia.
Qed.
Lemma fr_a12_sum_ge : forall (l : list (rentry * (hsrc * nat))) q, In q l ->
  fr_pair_cost (fst q) (snd q) <= fold_right Z.add 0 (map (fun q => fr_pair_cost (fst q) (snd q)) l).
Proof.
  induction l as [|q0 l IH]; intros q Hq; [destruct Hq|]. cbn [map fold_right].
  pose proof (fr_a12_sum_nonneg l) as Hl. pose proof (fr_pair_cost_nonneg (fst q0) (snd q0)) as H0.
  destruct Hq as [<- | Hq]; [lia|]. specialize (IH q Hq). lia.
Qed.
Lemma fr_a12_cost_ge : forall es hj e p, In (e, p) (combine es hj) -> fr_pair_cost e p <= fr_cost es hj.
Proof. intros es hj e p Hin. unfold fr_cost. exact (fr_a12_sum_ge (combine es hj) (e, p) Hin). Qed.
(* a held key costs at least 5 (gesture_end's " end\0") *)
Lemma fr_a12_keys_len : forall ks, 5 * Z.of_nat (length ks) <= gestures_end_b_c.keys_total ks.
Proof.
  unfold gestures_end_b_c.keys_total. induction ks as [|k ks IH]; cbn [fold_right length]; lia.
Qed.
(* the held list is no longer than the keys: its texts are distinct and each is a key's *)
Lemma fr_a12_held_keys : forall ks (H : hlist), NoDup (texts H) -> same_set (drain_b_c.keys_texts ks) (texts H) ->
  hl_n H <= Z.of_nat (length ks).
Proof.
  intros ks H Hnd Hss. first [apply NoDup_ListNoDup in Hnd | idtac].
  assert (Hinc : incl (texts H) (drain_b_c.keys_texts ks)) by (intros y Hy; exact (proj2 (Hss y) Hy)).
  pose proof (NoDup_incl_length Hnd Hinc) as Hle.
  unfold texts, drain_b_c.keys_texts in Hle. rewrite !length_map in Hle. unfold hl_n. lia.
Qed.

(* ================================================================== the states (lib/A/ReplyRINV_a12.v)
   One open slot 0 with source a12_src H (fd 100, held list H), one relay entry a12_ent ks (fd 100, at eof, keys ks),
   the controller CTL 3 0 0 0 0; from any call context cx0 (its layout, state, world, registers, memory and model are
   kept; the input is replaced). *)
Definition a12_cx (cx0 : lfcx) (n : Z) (pl : list byte) : lfcx :=
  LFCX (c_ly cx0) (c_S cx0) (c_W cx0) (c_regs cx0) (c_mem cx0) (c_md cx0) 0 n pl 0.
Definition a12_pad : list byte := [Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0].
Definition a12_E0 : hlist := HL 0 0 [] [].
Definition a12_src (H : hlist) : hsrc := HS 100 1 0 0 a12_E0 0 0 [] 0 0 [] a12_E0 H.
Definition a12_ent (ks : list (Z * list byte * list byte)) : rentry :=
  RE 100 1 1 a12_pad 0 0 0 0 0 a12_pad ks [] [].
Definition a12_m (k : Z) (H : hlist) (ks : list (Z * list byte * list byte)) (gn : Z) : lmod :=
  LM k [Some (a12_src H); None; None; None] 0 [a12_ent ks] (CTL 3 0 0 0 0) [] 0 0 0 gn 1.

(* fr_RINV holds at the state when the keys and the held texts agree and the keys' cost is in the input *)
Lemma a12_RINV : forall cx0 n pl k H ks gn,
  NoDup (drain_b_c.keys_texts ks) -> same_set (drain_b_c.keys_texts ks) (texts H) -> NoDup (texts H) ->
  hl_cap H < 2 ^ 24 -> gestures_end_b_c.keys_total ks <= k -> k <= n -> n < 2 ^ 26 -> gn <> 1 ->
  fr_RINV (a12_cx cx0 n pl) 0 (a12_m k H ks gn).
Proof.
  intros cx0 n pl k H ks gn Hnk Hss Hnd Hcap Hk Hkn Hn Hgn.
  split; [|split; [|split]].
  - unfold fr_count, nopen, OPS_MAX, a12_m. cbn [lm_nfd lm_hs List.filter length Z.of_nat]. lia.
  - unfold fr_relay, a12_m. cbn [lm_hs lm_es lm_nfd lm_k length].
    split; [reflexivity|].
    split; [apply NoDup_ListNoDup; repeat constructor; intros []|].
    split; [constructor; [cbn; lia | constructor]|].
    split.
    { constructor; [|constructor]. unfold fr_entry_ok, a12_ent, a12_pad.
      cbn [re_eof re_pad1 re_pad2 re_keys re_skip length].
      split; [right; reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
      split; [exact Hnk | right; reflexivity]. }
    exists [(a12_src H, 0%nat)].
    split.
    { constructor; [|constructor]. unfold fr_pair_ok, a12_src, a12_ent.
      cbn [fst snd nth lm_hs re_eof re_fd hs_fd re_keys hs_held hs_expected hs_off hl_recs hl_cap].
      split; [lia|]. split; [reflexivity|]. split; [reflexivity|].
      split; [intros E; discriminate E|].
      split; [exact Hss|]. split; [exact Hnd|]. split; [reflexivity|].
      split; [left; reflexivity|]. split; [exact Hcap|].
      split; [unfold pending_stream, a12_E0; cbn [hs_pending hl_recs length Z.of_nat]; unfold SlotInv.WRITE_MAX; lia
             | lia]. }
    split; [apply NoDup_ListNoDup; repeat constructor; intros []|].
    split.
    { intros i Hi Ho. destruct i as [|[|[|[|i]]]]; cbn in Ho |- *; first [discriminate Ho | reflexivity | lia]. }
    unfold fr_cost, fr_pair_cost, a12_ent, a12_src, pending_stream, a12_E0.
    cbn -[gestures_end_b_c.keys_total]. lia.
  - exact Hn.
  - unfold fr_gone, a12_m. cbn [lm_gn lm_c ct_cl ct_br ct_dd].
    split; intros E; [repeat split | exfalso; exact (Hgn E)].
Qed.
Lemma a12_pick : forall h kb, pick [Some h; None; None; None] kb = Some 0%nat.
Proof. intros h kb. unfold pick. cbn -[Z.modulo]. rewrite Z.mod_1_r. reflexivity. Qed.
(* the remove arm's operation at the state: op 4 at the cursor k, slot 0, entry 0 *)
Lemma a12_rm_at : forall cx0 n pl k H ks gn, 0 <= k -> k + 1 < n -> in_byte (a12_cx cx0 n pl) k mod 10 = 4 ->
  rm_at (a12_cx cx0 n pl) (a12_m k H ks gn) 0 (a12_src H) 0.
Proof.
  intros cx0 n pl k H ks gn Hk Hkn Hb. unfold rm_at, a12_m. cbn [lm_k lm_O lm_hs lm_es length].
  split; [unfold a12_cx; cbn [c_n]; lia|].
  split; [reflexivity|]. split; [exact Hb|]. split; [apply a12_pick|].
  split; [lia|]. split; [reflexivity|]. split; [lia|]. split; [reflexivity|].
  intros q Hq. lia.
Qed.
(* relay_remove at an entry at eof: the entry and the source are kept, the keys' ends are sent *)
Lemma a12_rr_ok : forall k H ks gn c2 O2 cap2,
  sl_sends 0 (CTL 3 0 0 0 0) [] 0 (ge_bytes ks) = (c2, O2, cap2) ->
  rm_rr_ok (a12_m k H ks gn) (a12_src H) 0 (a12_ent ks) (a12_src H) 0 [] c2 O2 cap2.
Proof. intros k H ks gn c2 O2 cap2 Er. unfold rm_rr_ok. split; [split; reflexivity | exact Er]. Qed.
(* check_no_loss with nothing expected keeps the held list *)
Lemma a12_cnl_ok : forall H, NoDup (texts H) -> rm_cnl_ok (a12_src H) a12_E0 H.
Proof.
  intros H Hnd. unfold rm_cnl_ok, a12_src, a12_E0. cbn [hl_recs hl_v hl_cap hs_expected hs_held].
  split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [exact Hnd|].
  split; [reflexivity | lia].
Qed.

(* the small states: one held text x, one key of text x, cost 6 = |x| + 5; the input 10 bytes of 4 *)
Definition a12_pl : list byte := repeat (Z_to_bv 8 4) 10.
Definition a12_H1 (x : list byte) : hlist := HL 0 8 [(0, x)] [].
Definition a12_ks1 (x : list byte) : list (Z * list byte * list byte) := [(0, x, [])].
Definition a12_a : list byte := [Z_to_bv 8 97].   (* "a" *)
Definition a12_nul : list byte := [Z_to_bv 8 0].  (* one NUL byte *)
Lemma a12_RINV1 : forall cx0 x gn, length x = 1%nat -> gn <> 1 ->
  fr_RINV (a12_cx cx0 10 a12_pl) 0 (a12_m 6 (a12_H1 x) (a12_ks1 x) gn).
Proof.
  intros cx0 x gn Hx Hgn. apply a12_RINV; try lia.
  - apply NoDup_ListNoDup. repeat constructor. intros [].
  - intros y. split; intros Hy; exact Hy.
  - apply NoDup_ListNoDup. repeat constructor. intros [].
  - cbn. lia.
  - unfold gestures_end_b_c.keys_total, a12_ks1, gestures_end_b_c.key_text. cbn [fold_right fst snd].
    rewrite Hx. cbn. lia.
Qed.
Lemma a12_rm_at1 : forall cx0 x gn, rm_at (a12_cx cx0 10 a12_pl) (a12_m 6 (a12_H1 x) (a12_ks1 x) gn) 0 (a12_src (a12_H1 x)) 0.
Proof. intros cx0 x gn. apply a12_rm_at; [lia | lia | reflexivity]. Qed.
Lemma a12_nd1 : forall x, NoDup (texts (a12_H1 x)).
Proof. intros x. apply NoDup_ListNoDup. repeat constructor. intros []. Qed.

(* ================================================================== the three B top texts fr_RINV does not meet
   B top_x :500 RI_rm_cnl_pre, :511 RI_rm_cshe_pre, :521 RI_rm_csd, word for word at RINV := ReplyRINVB.fr_RINV *)
Definition RI_rm_cnl_pre_top : Prop := forall cx t m si h j0 e1 h1 ev LB c2 O2 cap2,
  ReplyRINVB.fr_RINV cx t m -> W_LLVMFuzzerTestOneInput_remove.rm_at cx m si h j0 -> W_LLVMFuzzerTestOneInput_remove.rm_rr_ok m h j0 e1 h1 ev LB c2 O2 cap2 ->
  NoDup (texts (hs_held h1)) /\ hl_n (hs_expected h1) < 2 ^ 26 /\
  hl_n (hs_held h1) + Z.of_nat (count_begin (texts (hs_expected h1))) < 2 ^ 22 /\
  AREC * capb (hs_held h1) (hs_expected h1) < 2 ^ 32 /\ Z.of_nat (length O2) < 2 ^ 32 /\
  (lm_gn m = 0 -> exists rest, O2 = bstream (hs_expected h1) ++ rest).
Definition RI_rm_cshe_pre_top : Prop := forall cx t m si h j0 e1 h1 ev LB c2 O2 cap2 E' H',
  ReplyRINVB.fr_RINV cx t m -> W_LLVMFuzzerTestOneInput_remove.rm_at cx m si h j0 -> W_LLVMFuzzerTestOneInput_remove.rm_rr_ok m h j0 e1 h1 ev LB c2 O2 cap2 -> W_LLVMFuzzerTestOneInput_remove.rm_cnl_ok h1 E' H' ->
  lm_gn m = 0 ->
  W_LLVMFuzzerTestOneInput_remove.rm_A1 m h1 <= Z.of_nat (length O2) /\
  ends_run [] (hl_recs H') (skipn (Z.to_nat (W_LLVMFuzzerTestOneInput_remove.rm_A1 m h1)) O2) (want_of [] (hl_recs H')) <> None.
Definition RI_rm_csd_top : Prop := forall cx t m si h j0 e1 h1 ev LB c2 O2 cap2 E' H' H'' ds cc,
  ReplyRINVB.fr_RINV cx t m -> W_LLVMFuzzerTestOneInput_remove.rm_at cx m si h j0 -> W_LLVMFuzzerTestOneInput_remove.rm_rr_ok m h j0 e1 h1 ev LB c2 O2 cap2 -> W_LLVMFuzzerTestOneInput_remove.rm_cnl_ok h1 E' H' ->
  W_LLVMFuzzerTestOneInput_remove.rm_cshe_ok m (set_exp_held h1 E' H') O2 (W_LLVMFuzzerTestOneInput_remove.rm_A1 m h1) H'' ds cc ->
  W_LLVMFuzzerTestOneInput_remove.rm_A1 m h1 + cc = Z.of_nat (length O2).

(* the stream relay_remove leaves: the ends of the keys ks1 x, sent to the live controller *)
Definition a12_r (x : list byte) : ctl * list byte * Z := sl_sends 0 (CTL 3 0 0 0 0) [] 0 (ge_bytes (a12_ks1 x)).
(* RI_rm_cshe_pre at lm_gn m = 0 with a held text of one NUL byte *)
Lemma RI_rm_cshe_pre_top_false : lfcx -> ~ RI_rm_cshe_pre_top.
Proof.
  intros cx0 Hobl.
  pose proof (Hobl _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    (a12_RINV1 cx0 a12_nul 0 eq_refl ltac:(lia)) (a12_rm_at1 cx0 a12_nul 0)
    (a12_rr_ok 6 (a12_H1 a12_nul) (a12_ks1 a12_nul) 0 (fst (fst (a12_r a12_nul))) (snd (fst (a12_r a12_nul)))
       (snd (a12_r a12_nul)) eq_refl)
    (a12_cnl_ok (a12_H1 a12_nul) (a12_nd1 a12_nul)) eq_refl) as (_ & Hne).
  apply Hne. vm_compute. reflexivity.
Qed.
(* RI_rm_csd at lm_gn m = 2: rm_cshe_ok's gone branch with cc = 0, rm_A1 = 0, and 6 bytes sent *)
Lemma RI_rm_csd_top_false : lfcx -> ~ RI_rm_csd_top.
Proof.
  intros cx0 Hobl.
  assert (Hcs : rm_cshe_ok (a12_m 6 (a12_H1 a12_a) (a12_ks1 a12_a) 2)
    (set_exp_held (a12_src (a12_H1 a12_a)) a12_E0 (a12_H1 a12_a)) (snd (fst (a12_r a12_a)))
    (rm_A1 (a12_m 6 (a12_H1 a12_a) (a12_ks1 a12_a) 2) (a12_src (a12_H1 a12_a)))
    (HL 0 8 [] []) [(0, a12_a)] 0).
  { unfold rm_cshe_ok. cbn [hl_v hl_cap hs_held set_exp_held a12_src a12_H1 a12_m lm_gn hl_recs].
    split; [reflexivity|]. split; [reflexivity|].
    split; [apply NoDup_ListNoDup; constructor|]. split; [lia|].
    left. split; [lia|]. split; [reflexivity|]. split; reflexivity. }
  pose proof (Hobl _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    (a12_RINV1 cx0 a12_a 2 eq_refl ltac:(lia)) (a12_rm_at1 cx0 a12_a 2)
    (a12_rr_ok 6 (a12_H1 a12_a) (a12_ks1 a12_a) 2 (fst (fst (a12_r a12_a))) (snd (fst (a12_r a12_a)))
       (snd (a12_r a12_a)) eq_refl)
    (a12_cnl_ok (a12_H1 a12_a) (a12_nd1 a12_a)) Hcs) as Hc.
  vm_compute in Hc. discriminate Hc.
Qed.

(* RI_rm_cnl_pre: 2 ^ 22 held records with distinct 3-byte texts, one key for each; the cost 8 * 2 ^ 22 = 2 ^ 25 is
   below the cursor 2 ^ 25 and the input length 2 ^ 25 + 2 < 2 ^ 26.  The lists are never computed: every fact about
   them is a lemma over map / seq. *)
Definition a12_NB : nat := Z.to_nat (2 ^ 22).
Definition a12_t (n : nat) : list byte :=
  [Z_to_bv 8 (Z.of_nat n mod 256); Z_to_bv 8 (Z.of_nat n / 256 mod 256); Z_to_bv 8 (Z.of_nat n / 65536)].
Definition a12_ks : list (Z * list byte * list byte) := map (fun n => (0, a12_t n, [])) (seq 0 a12_NB).
Definition a12_bH : hlist := HL 0 (2 ^ 22) (map (fun n => (0, a12_t n)) (seq 0 a12_NB)) [].
Definition a12_bpl : list byte := repeat (Z_to_bv 8 0) (Z.to_nat (2 ^ 25)) ++ [Z_to_bv 8 4; Z_to_bv 8 4].
Lemma a12_nodup_map_in : forall (A B : Type) (f : A -> B) (l : list A),
  (forall x y, In x l -> In y l -> f x = f y -> x = y) -> List.NoDup l -> List.NoDup (map f l).
Proof.
  intros A B f l Hinj Hnd. revert Hinj. induction Hnd as [|a l Ha Hnd IH]; intros Hinj; cbn [map]; constructor.
  - intros Hin. apply in_map_iff in Hin as (b & Hb & Hbl). apply Ha.
    rewrite (Hinj b a (or_intror Hbl) (or_introl eq_refl) Hb) in Hbl. exact Hbl.
  - apply IH. intros x y Hx Hy Exy. apply Hinj; [right; exact Hx | right; exact Hy | exact Exy].
Qed.
Lemma a12_texts : drain_b_c.keys_texts a12_ks = texts a12_bH.
Proof.
  unfold drain_b_c.keys_texts, texts, a12_ks, a12_bH. cbn [hl_recs]. rewrite !map_map.
  apply map_ext. intros n. reflexivity.
Qed.
Lemma a12_ks_nodup : NoDup (drain_b_c.keys_texts a12_ks).
Proof.
  apply NoDup_ListNoDup. unfold drain_b_c.keys_texts, a12_ks. rewrite map_map.
  apply a12_nodup_map_in; [|apply seq_NoDup].
  intros x y Hx Hy E. apply in_seq in Hx as [_ Hx]. apply in_seq in Hy as [_ Hy].
  change (x < a12_NB)%nat in Hx. change (y < a12_NB)%nat in Hy. unfold a12_NB in Hx, Hy.
  apply Nat2Z.inj_lt in Hx, Hy. rewrite Z2Nat.id in Hx, Hy by lia.
  unfold gestures_end_b_c.key_text, a12_t, bzs in E. cbn [fst snd map] in E.
  injection E as E1 E2 E3.
  rewrite !SlotReads.bz_lit in E1, E2, E3 by first [apply Z.mod_pos_bound; lia | split; [apply Z.div_pos | apply Z.div_lt_upper_bound]; lia].
  apply Nat2Z.inj. lia.
Qed.
Lemma a12_ks_total : gestures_end_b_c.keys_total a12_ks = 2 ^ 25.
Proof.
  assert (Hm : forall l, gestures_end_b_c.keys_total (map (fun n => (0, a12_t n, @nil byte)) l) = 8 * Z.of_nat (length l)).
  { unfold gestures_end_b_c.keys_total. induction l as [|a l IH]; [reflexivity|].
    cbn [map fold_right length]. rewrite IH. unfold gestures_end_b_c.key_text. cbn [fst snd a12_t length]. lia. }
  unfold a12_ks. rewrite Hm, length_seq. unfold a12_NB. rewrite Z2Nat.id by lia. reflexivity.
Qed.
Lemma a12_bH_n : hl_n a12_bH = 2 ^ 22.
Proof.
  unfold hl_n, a12_bH. cbn [hl_recs]. rewrite length_map, length_seq. unfold a12_NB. rewrite Z2Nat.id by lia.
  reflexivity.
Qed.
Lemma a12_bpl_at : forall cx0, in_byte (a12_cx cx0 (2 ^ 25 + 2) a12_bpl) (2 ^ 25) mod 10 = 4.
Proof.
  intros cx0. unfold in_byte, a12_cx. cbn [c_pl]. unfold a12_bpl.
  rewrite app_nth2 by (rewrite repeat_length; apply Nat.le_refl).
  rewrite repeat_length, Nat.sub_diag. reflexivity.
Qed.
Lemma RI_rm_cnl_pre_top_false : lfcx -> ~ RI_rm_cnl_pre_top.
Proof.
  intros cx0 Hobl.
  assert (HRI : fr_RINV (a12_cx cx0 (2 ^ 25 + 2) a12_bpl) 0 (a12_m (2 ^ 25) a12_bH a12_ks 0)).
  { apply a12_RINV.
    - exact a12_ks_nodup.
    - rewrite a12_texts. intros y. split; intros Hy; exact Hy.
    - rewrite <- a12_texts. exact a12_ks_nodup.
    - change (hl_cap a12_bH) with (2 ^ 22). lia.
    - rewrite a12_ks_total. lia.
    - lia.
    - lia.
    - lia. }
  destruct (sl_sends 0 (CTL 3 0 0 0 0) [] 0 (ge_bytes a12_ks)) as [[c2 O2] cap2] eqn:Er.
  destruct (Hobl _ _ _ _ _ _ _ _ _ _ _ _ _ HRI
    (a12_rm_at cx0 (2 ^ 25 + 2) a12_bpl (2 ^ 25) a12_bH a12_ks 0 ltac:(lia) ltac:(lia) (a12_bpl_at cx0))
    (a12_rr_ok (2 ^ 25) a12_bH a12_ks 0 c2 O2 cap2 Er)) as (_ & _ & Hb & _).
  change (hl_n a12_bH + Z.of_nat (count_begin (texts a12_E0)) < 2 ^ 22) in Hb.
  rewrite a12_bH_n in Hb. change (count_begin (texts a12_E0)) with 0%nat in Hb. lia.
Qed.

(* ================================================================== the remove arm with the arm's premises *)
Definition fr_live3 (c : ctl) : Prop := ct_cl c = 3 /\ ct_br c = 0 /\ ct_dd c = 0.
Definition fr_dead (c : ctl) : Prop := ct_cl c = -1 \/ ct_br c = 1 \/ ct_dd c = 1.
Lemma fr_sl_live3 : forall c len, fr_live3 c -> sl_live c len = negb (len =? 0).
Proof.
  intros [cl br dd ei ev] len (E1 & E2 & E3). cbn [ct_cl ct_br ct_dd] in *. subst cl br dd.
  unfold sl_live, send_line_c.send_live, send_line_c.send_off. cbn [ct_cl ct_br ct_dd].
  destruct (len =? 0); reflexivity.
Qed.
Lemma fr_sl_ctl3 : forall c len, fr_live3 c -> fr_live3 (sl_ctl c len).
Proof.
  intros [cl br dd ei ev] len (E1 & E2 & E3). cbn [ct_cl ct_br ct_dd] in *. subst cl br dd.
  unfold sl_ctl, fr_live3. cbn [ct_cl ct_br ct_dd].
  destruct (send_line_c.send_off 3 0 len); (repeat split); reflexivity.
Qed.
Lemma fr_sl_O3 : forall c O x, fr_live3 c -> sl_O c O x = O ++ x.
Proof.
  intros c O x H. unfold sl_O. rewrite (fr_sl_live3 c _ H).
  destruct x as [|b x]; [cbn; rewrite app_nil_r; reflexivity | reflexivity].
Qed.
Lemma fr_sl_dead : forall c len, fr_dead c -> sl_live c len = false /\ fr_dead (sl_ctl c len).
Proof.
  intros [cl br dd ei ev] len Hd. unfold fr_dead in *. cbn [ct_cl ct_br ct_dd] in Hd.
  unfold sl_live, sl_ctl, send_line_c.send_live, send_line_c.send_off. cbn [ct_cl ct_br ct_dd].
  destruct Hd as [-> | [-> | ->]].
  - split; [reflexivity | left; reflexivity].
  - destruct (cl <? 0); (split; [reflexivity | right; left; reflexivity]).
  - destruct ((cl <? 0) || (br =? 1) || (len =? 0)); (split; [reflexivity | right; right; reflexivity]).
Qed.
(* ================================================================== the remove arm with the arm's premises
   What relay_remove leaves (rm_rr_ok): the held list is h's, the new keys are the held texts updated by the drained
   lines Ls (none when the entry was at eof), the expected list is Ls, and the stream is the expected stream then
   the new keys' ends when the controller is live, nothing when it is gone. *)
Lemma fr_skipn_len : forall (T : Type) (x y : list T), skipn (length x) (x ++ y) = y.
Proof. intros T x y. induction x as [|a x IH]; [reflexivity|]. cbn [length skipn app]. exact IH. Qed.
Lemma fr_ge_out : forall ks, concat (ge_bytes ks) = gestures_end_b_c.keys_out ks.
Proof.
  unfold ge_bytes, gestures_end_b_c.keys_out. induction ks as [|k ks IH]; [reflexivity|].
  cbn [map concat]. rewrite concat_app, IH. cbn [concat]. rewrite app_nil_r. reflexivity.
Qed.
Lemma fr_sends3 : forall Bs mx c O cap, fr_live3 c -> snd (fst (sl_sends mx c O cap Bs)) = O ++ concat Bs.
Proof.
  induction Bs as [|Bl r IH]; intros mx c O cap H; cbn [sl_sends].
  - cbn. rewrite app_nil_r. reflexivity.
  - rewrite IH by (apply fr_sl_ctl3; exact H). rewrite (fr_sl_O3 c O Bl H). cbn [concat]. rewrite app_assoc.
    reflexivity.
Qed.
Lemma fr_sends_dead : forall Bs mx c O cap, fr_dead c -> snd (fst (sl_sends mx c O cap Bs)) = O.
Proof.
  induction Bs as [|Bl r IH]; intros mx c O cap H; cbn [sl_sends]; [reflexivity|].
  destruct (fr_sl_dead c (Z.of_nat (length Bl)) H) as (L & D). rewrite IH by exact D. unfold sl_O. rewrite L.
  reflexivity.
Qed.
Lemma fr_sends_len : forall Bs mx c O cap,
  (length (snd (fst (sl_sends mx c O cap Bs))) <= length O + length (concat Bs))%nat.
Proof.
  induction Bs as [|Bl r IH]; intros mx c O cap; cbn [sl_sends].
  - cbn. lia.
  - etransitivity; [apply IH|]. unfold sl_O. cbn [concat]. rewrite length_app.
    destruct (sl_live c (Z.of_nat (length Bl))); [rewrite length_app|]; lia.
Qed.
Lemma fr_dr_ctl3 : forall c h ev, fr_live3 c -> fr_live3 (dr_ctl c h ev).
Proof.
  intros [cl br dd ei ev0] h ev (E1 & E2 & E3). cbn [ct_cl ct_br ct_dd] in *. subst cl br dd.
  unfold dr_ctl, fr_live3. cbn [ct_cl ct_br ct_dd].
  destruct (send_line_c.send_off 3 0 (dr_tot h)); (repeat split); reflexivity.
Qed.
Lemma fr_dr_ctl_dead : forall c h ev, fr_dead c -> fr_dead (dr_ctl c h ev).
Proof.
  intros [cl br dd ei ev0] h ev Hd. unfold fr_dead in *. cbn [ct_cl ct_br ct_dd] in Hd.
  unfold dr_ctl, send_line_c.send_off. cbn [ct_cl ct_br ct_dd].
  destruct Hd as [-> | [-> | ->]].
  - left; reflexivity.
  - destruct (cl <? 0); right; left; reflexivity.
  - right; right; reflexivity.
Qed.
(* keys_total is SlotPass2Aux's sum over the key texts *)
Lemma fr_kt_ksum : forall ks, gestures_end_b_c.keys_total ks = SlotPass2Aux.p2_ksum (drain_b_c.keys_texts ks).
Proof.
  unfold gestures_end_b_c.keys_total, SlotPass2Aux.p2_ksum, drain_b_c.keys_texts.
  induction ks as [|k ks IH]; [reflexivity|]. cbn [map fold_right]. rewrite IH. unfold bzs. rewrite length_map.
  reflexivity.
Qed.
Lemma fr_lines_zr : forall h, Forall SlotReads.zrange (dr_lines h).
Proof.
  intros h. unfold dr_lines. apply (SlotReads.lines_range (bzs (pending_stream h)) (hs_state h));
    [unfold hs_state; cbn [ls_w] | ]; apply SlotReads.zrange_bzs.
Qed.
(* the entry j0 and the operation's source h are one row of the table *)
Lemma fr_rm_pair : forall cx t m si h j0, fr_RINV cx t m -> rm_at cx m si h j0 ->
  fr_pair_ok m t (rm_ent m j0) (h, si) /\ fr_pair_cost (rm_ent m j0) (h, si) < 2 ^ 26 /\
  fr_entry_ok (rm_ent m j0).
Proof.
  intros cx t m si h j0 HRI Hat. pose proof HRI as (_ & HR & Hn & _).
  destruct HR as (_ & _ & _ & Hent & hj & HF & _ & _ & _ & Hcn).
  pose proof Hat as (_ & _ & _ & _ & Hsi & Hh & Hj & Hfd & _).
  pose proof (fr_F2_nth _ _ _ _ _ HF j0 relay_remove_b_c.no_entry relay_instance_gone_b_c.no_hj Hj) as HRp.
  change (nth j0 (lm_es m) relay_remove_b_c.no_entry) with (rm_ent m j0) in HRp.
  assert (Hin : In (rm_ent m j0, nth j0 hj relay_instance_gone_b_c.no_hj) (combine (lm_es m) hj)).
  { unfold rm_ent. rewrite <- combine_nth by exact (Forall2_length HF). apply nth_In.
    rewrite length_combine, <- (Forall2_length HF). lia. }
  revert HRp Hin. destruct (nth j0 hj relay_instance_gone_b_c.no_hj) as [h' s'] eqn:Ep. intros HRp Hin.
  pose proof HRp as (Hs4 & Hsn & Hpfd & _). cbn [fst snd] in Hs4, Hsn, Hpfd.
  assert (Es : s' = si).
  { destruct (Nat.eq_dec s' si) as [E | Ne]; [exact E|]. exfalso.
    apply (RI_fds_holds cx t m s' si h' h HRI Hs4 Hsi Ne Hsn Hh). rewrite Hpfd, Hfd. reflexivity. }
  subst s'. rewrite Hh in Hsn. injection Hsn as <-.
  split; [exact HRp|]. split.
  - pose proof (fr_a12_cost_ge (lm_es m) hj _ _ Hin). lia.
  - rewrite Forall_forall in Hent. apply Hent. eapply in_combine_l. exact Hin.
Qed.
Lemma fr_rm_facts : forall cx t m si h j0 e1 h1 ev LB c2 O2 cap2,
  fr_RINV cx t m -> rm_at cx m si h j0 -> rm_rr_ok m h j0 e1 h1 ev LB c2 O2 cap2 ->
  exists Ls,
    hs_held h1 = hs_held h /\
    NoDup (drain_b_c.keys_texts (re_keys e1)) /\
    same_set (drain_b_c.keys_texts (re_keys e1)) (upds (texts (hs_held h)) Ls) /\
    texts (hs_expected h1) = Ls /\
    map snd (hl_recs (hs_expected h1)) = map (map (Z_to_bv 8)) Ls /\ Forall SlotReads.zrange Ls /\
    Z.of_nat (length (with_nul Ls)) <=
      (if re_skip (rm_ent m j0) =? 0 then Z.of_nat (length (re_U (rm_ent m j0))) else 0) +
      Z.of_nat (length (pending_stream h)) /\
    gestures_end_b_c.keys_total (re_keys e1) <=
      gestures_end_b_c.keys_total (re_keys (rm_ent m j0)) + Z.of_nat (length (with_nul Ls)) /\
    (fr_live3 (lm_c m) -> O2 = bstream (hs_expected h1) ++ gestures_end_b_c.keys_out (re_keys e1)) /\
    (fr_dead (lm_c m) -> O2 = []) /\
    (length O2 <= length (with_nul Ls) + length (gestures_end_b_c.keys_out (re_keys e1)))%nat /\
    (Ls = [] \/ (re_eof (rm_ent m j0) = 0 /\ Ls = dr_lines h)).
Proof.
  intros cx t m si h j0 e1 h1 ev LB c2 O2 cap2 HRI Hat Hrr.
  destruct (fr_rm_pair cx t m si h j0 HRI Hat) as (HP & _ & HE).
  pose proof HP as (_ & _ & _ & Heof & Hss & Hndh & Hexp & _). cbn [fst snd] in Heof, Hss, Hndh, Hexp.
  pose proof HE as (Hef & _ & _ & Hndk & Hsk).
  pose proof Hat as (_ & HO & _).
  unfold rm_rr_ok in Hrr. cbv beta zeta in Hrr. rewrite HO in Hrr.
  destruct (Z.eqb_spec (re_eof (rm_ent m j0)) 0) as [E0 | E1].
  - (* the entry was open: drain ran *)
    try rewrite (proj2 (Z.eqb_eq _ _) E0) in Hrr. cbn [andb] in Hrr. destruct Hrr as (Hdr & Hsd).
    destruct Hdr as (_ & _ & _ & _ & _ & _ & _ & _ & Dnd & Dss & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
      Dexp & _ & Dheld & _ & _ & DLB).
    rewrite Hexp in Dexp. cbn [map app] in Dexp.
    pose proof (fr_lines_zr h) as Hzr.
    assert (HT : texts (hs_expected h1) = dr_lines h).
    { unfold texts. rewrite <- (map_map snd bzs), Dexp. apply fr_bzs_lines. exact Hzr. }
    assert (HB : bstream (hs_expected h1) = LB).
    { apply SlotReads.bzs_inj. rewrite (SlotReads.bstream_bzs _ _ Dexp Hzr). symmetry. exact DLB. }
    assert (HLB : length LB = length (with_nul (dr_lines h))).
    { rewrite <- (length_map bz LB). change (map bz LB) with (bzs LB). rewrite DLB. reflexivity. }
    pose proof (f_equal (fun r => snd (fst r)) Hsd) as HO2. cbn [fst snd] in HO2.
    exists (dr_lines h). split; [exact Dheld|]. split; [exact Dnd|]. split.
    { eapply SlotReads.same_set_trans; [exact Dss|]. apply SlotReads.upds_same_set. exact Hss. }
    split; [exact HT|]. split; [exact Dexp|]. split; [exact Hzr|].
    split.
    { pose proof (Heof E0) as (S1 & S2).
      assert (Ho : hs_overlong h = 0 \/ hs_overlong h = 1) by (rewrite <- S1; exact Hsk).
      exact (SlotReads.reads_bound (fr_ru (rm_ent m j0)) h S1 S2 Ho eq_refl). }
    split.
    { rewrite !fr_kt_ksum. etransitivity.
      - apply SlotPass2Aux.p2_ksum_incl; [first [exact Dnd | apply NoDup_ListNoDup; exact Dnd]|].
        intros y Hy. exact (proj1 (Dss y) Hy).
      - apply SlotPass2Aux.p2_ksum_upds. }
    split.
    { intros Hl. rewrite <- HO2. rewrite (fr_sends3 _ _ _ _ _ (fr_dr_ctl3 _ h ev Hl)), fr_ge_out.
      f_equal. rewrite HB. unfold dr_live. rewrite (fr_sl_live3 _ _ Hl). unfold dr_tot.
      destruct (Z.of_nat (length (with_nul (dr_lines h))) =? 0) eqn:Et; cbn [negb]; [|reflexivity].
      apply Z.eqb_eq in Et. destruct LB as [|b LB]; [reflexivity|]. cbn [length] in HLB. lia. }
    split.
    { intros Hd. rewrite <- HO2. rewrite (fr_sends_dead _ _ _ _ _ (fr_dr_ctl_dead _ h ev Hd)).
      unfold dr_live. rewrite (proj1 (fr_sl_dead _ (dr_tot h) Hd)). reflexivity. }
    split; [|right; split; [exact E0 | reflexivity]].
    rewrite <- HO2. etransitivity; [apply fr_sends_len|]. rewrite fr_ge_out.
    destruct (dr_live (lm_c m) h); cbn [app length]; lia.
  - (* the entry was at eof: nothing drained *)
    try rewrite (proj2 (Z.eqb_neq _ _) E1) in Hrr. cbn [andb] in Hrr. destruct Hrr as ((-> & ->) & Hsd).
    pose proof (f_equal (fun r => snd (fst r)) Hsd) as HO2. cbn [fst snd] in HO2.
    assert (HT : texts (hs_expected h) = []) by (unfold texts; rewrite Hexp; reflexivity).
    assert (HW0 : Z.of_nat (length (with_nul [])) = 0) by reflexivity.
    exists []. split; [reflexivity|]. split; [exact Hndk|]. split; [exact Hss|].
    split; [exact HT|]. split; [rewrite Hexp; reflexivity|]. split; [constructor|].
    split; [rewrite HW0; pose proof (Zle_0_nat (length (pending_stream h)));
            pose proof (Zle_0_nat (length (re_U (rm_ent m j0)))); destruct (re_skip (rm_ent m j0) =? 0); lia|].
    split; [rewrite HW0; lia|].
    split.
    { intros Hl. rewrite <- HO2. rewrite (fr_sends3 _ _ _ _ _ Hl), fr_ge_out. unfold bstream. rewrite Hexp.
      reflexivity. }
    split; [intros Hd; rewrite <- HO2; exact (fr_sends_dead _ _ _ _ _ Hd)|].
    split; [|left; reflexivity].
    rewrite <- HO2. etransitivity; [apply fr_sends_len|]. rewrite fr_ge_out. cbn [length with_nul map concat]. lia.
Qed.

(* the relay's lines have no NUL byte when the partial line it carries has none (or is dropped: ls_k = true), and
   the held-key texts the lines add (gesture's key, a prefix of a line) have none either; stated over RelayModel's
   plain terms *)
Lemma lines_nul_free : forall (d : list Z) (st : lstate), (ls_k st = false -> ~ In 0 (ls_w st)) ->
  Forall (fun l => ~ In 0 l) (lines st d).
Proof.
  induction d as [|b d IH]; intros st Hst; [rewrite lines_nil; constructor|].
  rewrite lines_cons.
  destruct (Z.eq_dec b 0) as [-> | Hb].
  - rewrite step_zero. cbn [fst snd].
    assert (H0 : Forall (fun l => ~ In 0 l) (lines (LS [] false) d)) by (apply IH; intros _ []).
    destruct (ls_k st) eqn:Hk; [exact H0|]. constructor; [exact (Hst eq_refl) | exact H0].
  - destruct (ls_k st) eqn:Hk.
    + rewrite (step_nz_k st b Hb Hk). cbn [fst snd]. apply IH. rewrite Hk. intros Hf; discriminate Hf.
    + destruct (Nat.eq_dec (length (ls_w st)) LINE_LIMIT) as [He | He].
      * rewrite (step_nz_full st b Hb Hk He). cbn [fst snd]. apply IH. cbn [ls_k]. intros Hf; discriminate Hf.
      * rewrite (step_nz_add st b Hb Hk He). cbn [fst snd]. apply IH. cbn [ls_k ls_w]. intros _ Hin.
        apply in_app_or in Hin as [Hin | [E | []]]; [exact (Hst eq_refl Hin) | exact (Hb E)].
Qed.
Lemma fr_gesture_sub : forall l k x, gesture l = Some (k, x) -> forall z, In z x -> In z l.
Proof.
  intros l k x Hg z Hz. unfold gesture in Hg. cbv zeta in Hg.
  destruct (list_eqb (firstn 13 l) K_GESTURE && Z.eqb (nth 13 l 0) SPACE && Nat.ltb 13 (length l));
    [|discriminate Hg].
  destruct (last_space_from 0 l) as [j|]; [|discriminate Hg].
  destruct (Nat.ltb 13 j); [|discriminate Hg].
  rewrite <- (firstn_skipn j l). apply in_or_app. left.
  destruct (list_eqb (skipn (S j) l) W_BEGIN); [injection Hg as _ <-; exact Hz|].
  destruct (list_eqb (skipn (S j) l) W_END); [injection Hg as _ <-; exact Hz | discriminate Hg].
Qed.
Lemma upds_nul_free : forall (Ls G : list (list Z)), Forall (fun x => ~ In 0 x) G ->
  Forall (fun l => ~ In 0 l) Ls -> Forall (fun x => ~ In 0 x) (upds G Ls).
Proof.
  unfold upds. induction Ls as [|l Ls IH]; intros G HG HL; cbn [fold_left]; [exact HG|].
  apply Forall_cons_iff in HL as [Hl HL']. apply IH; [|exact HL'].
  unfold upd. destruct (gesture l) as [[[|] x]|] eqn:Eg.
  - destruct (existsb (list_eqb x) G); cbv beta iota; [exact HG|].
    apply Forall_app. split; [exact HG|]. constructor; [|constructor].
    intros Hx. exact (Hl (fr_gesture_sub l _ x Eg 0 Hx)).
  - apply Forall_forall. intros y Hy. apply filter_In in Hy as [Hy _]. rewrite Forall_forall in HG. exact (HG y Hy).
  - exact HG.
Qed.
Lemma fr_nz_bzs : forall x, ~ In (Z_to_bv 8 0) x -> ~ In 0 (bzs x).
Proof.
  intros x Hx Hin. unfold bzs in Hin. apply in_map_iff in Hin as (b & Eb & Hb). apply Hx.
  replace (Z_to_bv 8 0) with b; [exact Hb|]. apply SlotReads.bz_inj. rewrite Eb. reflexivity.
Qed.
Lemma fr_nz_bzs' : forall x, ~ In 0 (bzs x) -> ~ In (Z_to_bv 8 0) x.
Proof.
  intros x Hx Hin. apply Hx. unfold bzs. replace 0 with (bz (Z_to_bv 8 0)) by reflexivity. apply in_map. exact Hin.
Qed.
(* the keys relay_remove leaves on the removed entry have no NUL byte when its unfinished line and its keys have
   none: the drained lines are NUL-free (the unfinished line is the source's partial line while it is read,
   fr_pair_ok), so every key they add is *)
Lemma fr_rm_keys_nz : forall cx t m si h j0 e1 h1 ev LB c2 O2 cap2,
  fr_RINV cx t m -> rm_at cx m si h j0 -> rm_rr_ok m h j0 e1 h1 ev LB c2 O2 cap2 ->
  ~ In (Z_to_bv 8 0) (re_U (rm_ent m j0)) ->
  Forall (fun k => ~ In (Z_to_bv 8 0) (gestures_end_b_c.key_text k)) (re_keys (rm_ent m j0)) ->
  Forall (fun k => ~ In (Z_to_bv 8 0) (gestures_end_b_c.key_text k)) (re_keys e1).
Proof.
  intros cx t m si h j0 e1 h1 ev LB c2 O2 cap2 HRI Hat Hrr HU HK.
  destruct (fr_rm_pair cx t m si h j0 HRI Hat) as (HP & _ & HE).
  pose proof HP as (_ & _ & _ & Heof & Hss & _). cbn [fst snd] in Heof, Hss.
  pose proof HE as (_ & _ & _ & _ & Hsk).
  destruct (fr_rm_facts cx t m si h j0 e1 h1 ev LB c2 O2 cap2 HRI Hat Hrr)
    as (Ls & _ & _ & Hss1 & _ & _ & _ & _ & _ & _ & _ & _ & HLs).
  assert (HG : Forall (fun x => ~ In 0 x) (texts (hs_held h))).
  { apply Forall_forall. intros y Hy. apply (proj2 (Hss y)) in Hy.
    unfold drain_b_c.keys_texts in Hy. apply in_map_iff in Hy as (k & <- & Hk).
    rewrite Forall_forall in HK. apply fr_nz_bzs. exact (HK k Hk). }
  assert (HL : Forall (fun l => ~ In 0 l) Ls).
  { destruct HLs as [-> | (E0 & ->)]; [constructor|].
    unfold dr_lines. apply lines_nul_free. unfold hs_state. cbn [ls_k ls_w]. intros Hk.
    destruct (Heof E0) as (S1 & S2).
    assert (Hs0 : re_skip (rm_ent m j0) = 0).
    { destruct Hsk as [E | E]; [exact E|]. exfalso. rewrite S1 in E. rewrite E in Hk. discriminate Hk. }
    rewrite <- (S2 Hs0). apply fr_nz_bzs. exact HU. }
  pose proof (upds_nul_free Ls (texts (hs_held h)) HG HL) as HU2. rewrite Forall_forall in HU2.
  apply Forall_forall. intros k Hk. apply fr_nz_bzs'. apply HU2. apply (proj1 (Hss1 _)).
  unfold drain_b_c.keys_texts. apply (in_map (fun k => bzs (gestures_end_b_c.key_text k))). exact Hk.
Qed.

(* RI_rm_cnl_pre with K14 (every key text >= 14 bytes, rm_mfacts conjunct 2): the plain proof's p4_cnl_bound route
   (19 * keys <= keys_total, 21 * count_begin <= the drained bytes, both within the row's cost < 2 ^ 26) *)
Lemma fr_rm_cnl_pre_core : forall cx t m si h j0 e1 h1 ev LB c2 O2 cap2,
  fr_RINV cx t m -> rm_at cx m si h j0 -> rm_rr_ok m h j0 e1 h1 ev LB c2 O2 cap2 ->
  Forall (fun k => 14 <= Z.of_nat (length (gestures_end_b_c.key_text k))) (re_keys (rm_ent m j0)) ->
  NoDup (texts (hs_held h1)) /\ hl_n (hs_expected h1) < 2 ^ 26 /\
  hl_n (hs_held h1) + Z.of_nat (count_begin (texts (hs_expected h1))) < 2 ^ 22 /\
  AREC * capb (hs_held h1) (hs_expected h1) < 2 ^ 32 /\ Z.of_nat (length O2) < 2 ^ 32 /\
  (lm_gn m = 0 -> exists rest, O2 = bstream (hs_expected h1) ++ rest).
Proof.
  intros cx t m si h j0 e1 h1 ev LB c2 O2 cap2 HRI Hat Hrr K14.
  destruct (fr_rm_pair cx t m si h j0 HRI Hat) as (HP & HC & _).
  pose proof HP as (_ & _ & _ & _ & Hss & Hndh & _ & _ & Hcap & _). cbn [fst snd] in Hss, Hndh, Hcap.
  destruct (fr_rm_facts cx t m si h j0 e1 h1 ev LB c2 O2 cap2 HRI Hat Hrr)
    as (Ls & Hheld & _ & _ & HT & Hexp & _ & Hwn & Hkt & Hlive & _ & Hlen & _).
  pose proof (fr_a12_held_keys _ _ Hndh Hss) as HHK.
  pose proof (SlotReads.keys_total_count _ K14) as K19.
  pose proof (SlotReads.count_begin_bytes Ls) as CB.
  pose proof (SlotReads.lines_count Ls) as LC.
  pose proof (SlotReads.keys_out_length (re_keys e1)) as KO.
  unfold fr_pair_cost in HC. cbn [fst] in HC.
  assert (Hnexp : hl_n (hs_expected h1) = Z.of_nat (length Ls)).
  { unfold hl_n. rewrite <- (length_map snd), Hexp, length_map. reflexivity. }
  assert (Hb : hl_n (hs_held h) + Z.of_nat (count_begin Ls) < 2 ^ 22).
  { pose proof (Zle_0_nat (length (pending_stream h))). pose proof (Zle_0_nat (length (re_U (rm_ent m j0)))).
    destruct (re_skip (rm_ent m j0) =? 0); lia. }
  rewrite Hheld, HT. split; [exact Hndh|]. split.
  { rewrite Hnexp. pose proof (Zle_0_nat (length (pending_stream h))).
    pose proof (Zle_0_nat (length (re_U (rm_ent m j0)))). destruct (re_skip (rm_ent m j0) =? 0); lia. }
  split; [exact Hb|]. split.
  { unfold capb, AREC. rewrite HT. lia. }
  split.
  { pose proof (Zle_0_nat (length (pending_stream h))). pose proof (Zle_0_nat (length (re_U (rm_ent m j0)))).
    pose proof (fr_keys_total_nonneg (re_keys (rm_ent m j0))).
    assert (Z.of_nat (length O2) <= Z.of_nat (length (with_nul Ls)) + gestures_end_b_c.keys_total (re_keys e1)) by lia.
    destruct (re_skip (rm_ent m j0) =? 0); lia. }
  intros Hg. pose proof HRI as (_ & _ & _ & (G0 & _)).
  exists (gestures_end_b_c.keys_out (re_keys e1)). exact (Hlive (G0 Hg)).
Qed.

(* the shutdown check's run never reads a NUL byte: every record it matched (all of them, at want = length) has a
   NUL-free text *)
Lemma fr_split_nul_nz : forall d l d', split_nul d = Some (l, d') -> ~ In (Z_to_bv 8 0) l.
Proof.
  induction d as [|b d IH]; intros l d' Hs; cbn [split_nul] in Hs; [discriminate Hs|].
  revert Hs. destruct (Z.eqb_spec (bv_unsigned b) 0) as [_ | Hb]; intros Hs.
  - injection Hs as <- _. intros [].
  - revert Hs. destruct (split_nul d) as [[l0 r]|] eqn:E; intros Hs; [|discriminate Hs]. injection Hs as <- <-.
    intros [Eb | Hin].
    + apply Hb. rewrite Eb. reflexivity.
    + exact (IH l0 r eq_refl Hin).
Qed.
Lemma fr_find_text_some : forall y rs i, find_text y rs = Some i ->
  (i < length rs)%nat /\ bzs (snd (nth i rs (0, []))) = bzs y.
Proof.
  intros y rs. induction rs as [|r rs IH]; intros i Hf; cbn [find_text] in Hf; [discriminate Hf|].
  revert Hf. destruct (list_eqb (bzs (snd r)) (bzs y)) eqn:E; intros Hf.
  - injection Hf as <-.
    assert (X : bzs (snd r) = bzs y).
    { revert E. unfold list_eqb. destruct (list_eq_dec Z.eq_dec (bzs (snd r)) (bzs y)) as [X|_]; intros E;
        [exact X | discriminate E]. }
    cbn [nth length]. split; [lia | exact X].
  - revert Hf. destruct (find_text y rs) as [i0|] eqn:Ef; cbn [option_map]; intros Hf; [|discriminate Hf].
    injection Hf as <-. destruct (IH i0 eq_refl) as (Hi & Ht). cbn [length nth]. split; [lia | exact Ht].
Qed.
Lemma fr_ends_nz : forall w rs d x, ends_run [] rs d w = Some x -> w = length rs ->
  Forall (fun r => ~ In (Z_to_bv 8 0) (snd r)) rs.
Proof.
  induction w as [|w IH]; intros rs d x Hr Hw.
  - destruct rs; [constructor | discriminate Hw].
  - cbn [ends_run] in Hr. revert Hr.
    destruct (split_nul d) as [[l d']|] eqn:Es; [|intros Hr; discriminate Hr]. cbv beta iota zeta.
    destruct (Nat.leb 4 (length l) && list_eqb (bzs (skipn (length l - 4)%nat l)) (bzs END4) && prefixb [] l);
      [|intros Hr; discriminate Hr]. cbv beta iota zeta.
    destruct (find_text (firstn (length l - 4)%nat l) rs) as [i|] eqn:Ef; [|intros Hr; discriminate Hr].
    cbv beta iota zeta.
    destruct (ends_run [] (drop_nth i rs) d' w) as [y|] eqn:Er; [|intros Hr; discriminate Hr]. intros _.
    destruct (fr_find_text_some _ _ _ Ef) as (Hi & Ht).
    assert (Hd : Forall (fun r => ~ In (Z_to_bv 8 0) (snd r)) (drop_nth i rs)).
    { apply (IH _ _ _ Er). unfold drop_nth. rewrite length_app, length_firstn, length_skipn. lia. }
    assert (Hn : ~ In (Z_to_bv 8 0) (snd (nth i rs (0, [])))).
    { apply SlotReads.bzs_inj in Ht. rewrite Ht. intros Hin. apply (fr_split_nul_nz _ _ _ Es).
      rewrite <- (firstn_skipn (length l - 4)%nat l). apply in_or_app. left. exact Hin. }
    rewrite (fr_split_nth _ rs i (0, []) Hi). unfold drop_nth in Hd. apply Forall_app in Hd as [H1 H2].
    apply Forall_app. split; [exact H1|]. constructor; [exact Hn | exact H2].
Qed.
(* the key texts are NUL-free when the held list they match is *)
Lemma fr_keys_nz : forall ks (rs : list (Z * list byte)), Forall (fun r => ~ In (Z_to_bv 8 0) (snd r)) rs ->
  (forall y, In y (drain_b_c.keys_texts ks) -> In y (map (fun r => bzs (snd r)) rs)) ->
  Forall (fun k => ~ In (Z_to_bv 8 0) (gestures_end_b_c.key_text k)) ks.
Proof.
  intros ks rs HR HS. apply Forall_forall. intros k Hk HZ.
  assert (Hy : In (bzs (gestures_end_b_c.key_text k)) (drain_b_c.keys_texts ks))
    by (unfold drain_b_c.keys_texts; apply (in_map (fun k => bzs (gestures_end_b_c.key_text k))); exact Hk).
  apply HS in Hy. apply in_map_iff in Hy as (r & Er & Hr).
  apply SlotReads.bzs_inj in Er. rewrite Forall_forall in HR. apply (HR r Hr). rewrite Er. exact HZ.
Qed.
(* the check over the remove arm's stream at gone = 0: skipn rm_A1 O2 is the new keys' ends *)
Lemma fr_rm_ends : forall cx t m si h j0 e1 h1 ev LB c2 O2 cap2 E' H',
  fr_RINV cx t m -> rm_at cx m si h j0 -> rm_rr_ok m h j0 e1 h1 ev LB c2 O2 cap2 -> rm_cnl_ok h1 E' H' ->
  lm_gn m = 0 ->
  rm_A1 m h1 <= Z.of_nat (length O2) /\
  skipn (Z.to_nat (rm_A1 m h1)) O2 = gestures_end_b_c.keys_out (re_keys e1) /\
  NoDup (drain_b_c.keys_texts (re_keys e1)) /\ same_set (drain_b_c.keys_texts (re_keys e1)) (texts H') /\
  Z.of_nat (length O2) = rm_A1 m h1 + Z.of_nat (length (gestures_end_b_c.keys_out (re_keys e1))).
Proof.
  intros cx t m si h j0 e1 h1 ev LB c2 O2 cap2 E' H' HRI Hat Hrr Hcnl Hg.
  destruct (fr_rm_facts cx t m si h j0 e1 h1 ev LB c2 O2 cap2 HRI Hat Hrr)
    as (Ls & Hheld & Hndk & Hss & HT & _ & _ & _ & _ & Hlive & _ & _).
  pose proof HRI as (_ & _ & _ & (G0 & _)). specialize (Hlive (G0 Hg)).
  destruct Hcnl as (_ & _ & _ & _ & HTH & _).
  assert (HA : rm_A1 m h1 = Z.of_nat (length (bstream (hs_expected h1)))) by (unfold rm_A1; rewrite Hg; reflexivity).
  rewrite HA, Hlive, Nat2Z.id, fr_skipn_len, length_app, Nat2Z.inj_add.
  split; [lia|]. split; [reflexivity|]. split; [exact Hndk|]. split; [|reflexivity].
  rewrite HTH, Hheld, HT. exact Hss.
Qed.
Lemma fr_rm_cshe_pre_core : forall cx t m si h j0 e1 h1 ev LB c2 O2 cap2 E' H',
  fr_RINV cx t m -> rm_at cx m si h j0 -> rm_rr_ok m h j0 e1 h1 ev LB c2 O2 cap2 -> rm_cnl_ok h1 E' H' ->
  lm_gn m = 0 -> Forall (fun k => ~ In (Z_to_bv 8 0) (gestures_end_b_c.key_text k)) (re_keys e1) ->
  rm_A1 m h1 <= Z.of_nat (length O2) /\
  ends_run [] (hl_recs H') (skipn (Z.to_nat (rm_A1 m h1)) O2) (want_of [] (hl_recs H')) <> None.
Proof.
  intros cx t m si h j0 e1 h1 ev LB c2 O2 cap2 E' H' HRI Hat Hrr Hcnl Hg Hnz.
  pose proof Hcnl as (_ & _ & _ & HndH & _).
  destruct (fr_rm_ends cx t m si h j0 e1 h1 ev LB c2 O2 cap2 E' H' HRI Hat Hrr Hcnl Hg) as (Hle & Hsk & Hndk & Hss & _).
  split; [exact Hle|]. rewrite Hsk, SlotReads.want_of_nil, <- (app_nil_r (gestures_end_b_c.keys_out (re_keys e1))).
  destruct (SlotReads.ends_run_keys (re_keys e1) (hl_recs H') [])
    as (rs' & ds & E).
  all: try first [exact Hndk | exact (proj1 (NoDup_ListNoDup _) Hndk) | exact (proj2 (NoDup_ListNoDup _) Hndk)
                 | exact HndH | exact (proj1 (NoDup_ListNoDup _) HndH) | exact (proj2 (NoDup_ListNoDup _) HndH)
                 | exact Hss | exact Hnz].
  rewrite E. discriminate.
Qed.
Lemma fr_rm_csd_core : forall cx t m si h j0 e1 h1 ev LB c2 O2 cap2 E' H' H'' ds cc,
  fr_RINV cx t m -> rm_at cx m si h j0 -> rm_rr_ok m h j0 e1 h1 ev LB c2 O2 cap2 -> rm_cnl_ok h1 E' H' ->
  rm_cshe_ok m (set_exp_held h1 E' H') O2 (rm_A1 m h1) H'' ds cc ->
  (lm_gn m = 0 \/ lm_gn m = 1) ->
  rm_A1 m h1 + cc = Z.of_nat (length O2).
Proof.
  intros cx t m si h j0 e1 h1 ev LB c2 O2 cap2 E' H' H'' ds cc HRI Hat Hrr Hcnl Hcs Hg.
  pose proof HRI as (_ & _ & _ & (G0 & G1)).
  destruct Hcs as (_ & _ & _ & _ & [(Hg1 & _ & _ & Hcc) | (Hg0 & Hrun)]).
  - (* gone: nothing was sent *)
    assert (E1 : lm_gn m = 1) by lia.
    destruct (fr_rm_facts cx t m si h j0 e1 h1 ev LB c2 O2 cap2 HRI Hat Hrr)
      as (Ls & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hdead & _).
    rewrite (Hdead (G1 E1)), Hcc. unfold rm_A1. rewrite E1. reflexivity.
  - (* live: the check consumed the new keys' ends *)
    cbn [hs_held set_exp_held] in Hrun.
    pose proof Hcnl as (_ & _ & _ & HndH & _).
    destruct (fr_rm_ends cx t m si h j0 e1 h1 ev LB c2 O2 cap2 E' H' HRI Hat Hrr Hcnl Hg0)
      as (_ & Hsk & Hndk & Hss & Hlen).
    rewrite Hsk, SlotReads.want_of_nil in Hrun.
    assert (Hnz : Forall (fun r => ~ In (Z_to_bv 8 0) (snd r)) (hl_recs H')) by exact (fr_ends_nz _ _ _ _ Hrun eq_refl).
    rewrite <- (app_nil_r (gestures_end_b_c.keys_out (re_keys e1))) in Hrun.
    destruct (SlotReads.ends_run_keys (re_keys e1) (hl_recs H') [])
      as (rs' & ds' & E).
    all: try first [exact Hndk | exact (proj1 (NoDup_ListNoDup _) Hndk) | exact (proj2 (NoDup_ListNoDup _) Hndk)
                   | exact HndH | exact (proj1 (NoDup_ListNoDup _) HndH) | exact (proj2 (NoDup_ListNoDup _) HndH)
                   | exact Hss | exact (fr_keys_nz _ _ Hnz (fun y Hy => proj1 (Hss y) Hy))].
    rewrite E in Hrun. injection Hrun as _ _ <-. lia.
Qed.

(* ================================================================== the three rows with the arm's premise
   (A's restated texts, a working branch 3f40808c334), at RINV := fr_RINV *)
Lemma RI_rm_cnl_pre_K14_holds : forall cx t m si h j0 e1 h1 ev LB c2 O2 cap2,
  fr_RINV cx t m -> rm_at cx m si h j0 -> rm_rr_ok m h j0 e1 h1 ev LB c2 O2 cap2 ->
  Forall (fun e => Forall (fun k => 14 <= Z.of_nat (length (gestures_end_b_c.key_text k))) (re_keys e)) (lm_es m) ->
  NoDup (texts (hs_held h1)) /\ hl_n (hs_expected h1) < 2 ^ 26 /\
  hl_n (hs_held h1) + Z.of_nat (count_begin (texts (hs_expected h1))) < 2 ^ 22 /\
  AREC * capb (hs_held h1) (hs_expected h1) < 2 ^ 32 /\ Z.of_nat (length O2) < 2 ^ 32 /\
  (lm_gn m = 0 -> exists rest, O2 = bstream (hs_expected h1) ++ rest).
Proof.
  intros cx t m si h j0 e1 h1 ev LB c2 O2 cap2 HRI Hat Hrr HK.
  apply (fr_rm_cnl_pre_core cx t m si h j0 e1 h1 ev LB c2 O2 cap2 HRI Hat Hrr).
  rewrite Forall_forall in HK. apply HK. pose proof Hat as (_ & _ & _ & _ & _ & _ & Hj & _).
  unfold rm_ent. apply nth_In. exact Hj.
Qed.
Lemma RI_rm_cshe_pre_nz_holds : forall cx t m si h j0 e1 h1 ev LB c2 O2 cap2 E' H',
  fr_RINV cx t m -> rm_at cx m si h j0 -> rm_rr_ok m h j0 e1 h1 ev LB c2 O2 cap2 -> rm_cnl_ok h1 E' H' ->
  lm_gn m = 0 ->
  Forall (fun r => ~ In (Z_to_bv 8 0) (snd r)) (hl_recs H') ->
  rm_A1 m h1 <= Z.of_nat (length O2) /\
  ends_run [] (hl_recs H') (skipn (Z.to_nat (rm_A1 m h1)) O2) (want_of [] (hl_recs H')) <> None.
Proof.
  intros cx t m si h j0 e1 h1 ev LB c2 O2 cap2 E' H' HRI Hat Hrr Hcnl Hg Hnz.
  apply (fr_rm_cshe_pre_core cx t m si h j0 e1 h1 ev LB c2 O2 cap2 E' H' HRI Hat Hrr Hcnl Hg).
  destruct (fr_rm_ends cx t m si h j0 e1 h1 ev LB c2 O2 cap2 E' H' HRI Hat Hrr Hcnl Hg) as (_ & _ & _ & Hss & _).
  exact (fr_keys_nz _ _ Hnz (fun y Hy => proj1 (Hss y) Hy)).
Qed.
Lemma RI_rm_csd_gn_holds : forall cx t m si h j0 e1 h1 ev LB c2 O2 cap2 E' H' H'' ds cc,
  fr_RINV cx t m -> rm_at cx m si h j0 -> rm_rr_ok m h j0 e1 h1 ev LB c2 O2 cap2 -> rm_cnl_ok h1 E' H' ->
  rm_cshe_ok m (set_exp_held h1 E' H') O2 (rm_A1 m h1) H'' ds cc ->
  0 <= lm_gn m <= 1 ->
  rm_A1 m h1 + cc = Z.of_nat (length O2).
Proof.
  intros cx t m si h j0 e1 h1 ev LB c2 O2 cap2 E' H' H'' ds cc HRI Hat Hrr Hcnl Hcs Hg.
  exact (fr_rm_csd_core cx t m si h j0 e1 h1 ev LB c2 O2 cap2 E' H' H'' ds cc HRI Hat Hrr Hcnl Hcs ltac:(lia)).
Qed.

(* ================================================================== every row's premises are satisfiable
   (VERIFY rule 10): from any call context, a state that meets every premise of the row *)
Definition a12_ent0 : rentry := RE 100 0 0 a12_pad 0 0 0 0 0 a12_pad (a12_ks1 a12_a) [] [].
Definition a12_m0 : lmod :=
  LM 6 [Some (a12_src (a12_H1 a12_a)); None; None; None] 0 [a12_ent0] (CTL 3 0 0 0 0) [] 0 0 0 0 1.
(* the open entry's state: fr_pair_ok's eof clause is met (skip 0 = overlong 0, the unfinished line [] = hs_W []) *)
Lemma a12_RINV0 : forall cx0, fr_RINV (a12_cx cx0 10 a12_pl) 0 a12_m0.
Proof.
  intros cx0. split; [|split; [|split]].
  - unfold fr_count, nopen, OPS_MAX, a12_m0. cbn [lm_nfd lm_hs List.filter length Z.of_nat]. lia.
  - unfold fr_relay, a12_m0. cbn [lm_hs lm_es lm_nfd lm_k length].
    split; [reflexivity|].
    split; [apply NoDup_ListNoDup; repeat constructor; intros []|].
    split; [constructor; [cbn; lia | constructor]|].
    split.
    { constructor; [|constructor]. unfold fr_entry_ok, a12_ent0, a12_pad.
      cbn [re_eof re_pad1 re_pad2 re_keys re_skip length].
      split; [left; reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
      split; [apply NoDup_ListNoDup; repeat constructor; intros [] | left; reflexivity]. }
    exists [(a12_src (a12_H1 a12_a), 0%nat)].
    split.
    { constructor; [|constructor]. unfold fr_pair_ok, a12_src, a12_ent0.
      cbn [fst snd nth lm_hs re_eof re_fd hs_fd re_keys hs_held hs_expected hs_off hl_recs hl_cap].
      split; [lia|]. split; [reflexivity|]. split; [reflexivity|].
      split; [intros _; split; [reflexivity | intros _; reflexivity]|].
      split; [intros y; split; intros Hy; exact Hy|].
      split; [apply NoDup_ListNoDup; repeat constructor; intros []|].
      split; [reflexivity|]. split; [left; reflexivity|]. split; [cbn; lia|].
      split; [unfold pending_stream, a12_E0; cbn [hs_pending hl_recs length Z.of_nat]; unfold SlotInv.WRITE_MAX; lia
             | lia]. }
    split; [apply NoDup_ListNoDup; repeat constructor; intros []|].
    split.
    { intros i Hi Ho. destruct i as [|[|[|[|i]]]]; cbn in Ho |- *; first [discriminate Ho | reflexivity | lia]. }
    unfold fr_cost, fr_pair_cost, a12_ent0, a12_src, pending_stream, a12_E0, a12_ks1, a12_a,
      gestures_end_b_c.keys_total, gestures_end_b_c.key_text.
    cbn. lia.
  - unfold a12_cx. cbn [c_n]. lia.
  - unfold fr_gone, a12_m0. cbn [lm_gn lm_c ct_cl ct_br ct_dd]. split; intros E; [repeat split | discriminate E].
Qed.
Lemma a12_rm_at0 : forall cx0, rm_at (a12_cx cx0 10 a12_pl) a12_m0 0 (a12_src (a12_H1 a12_a)) 0.
Proof.
  intros cx0. unfold rm_at, a12_m0. cbn [lm_k lm_O lm_hs lm_es length].
  split; [unfold a12_cx; cbn [c_n]; lia|]. split; [reflexivity|]. split; [reflexivity|]. split; [apply a12_pick|].
  split; [lia|]. split; [reflexivity|]. split; [lia|]. split; [reflexivity|]. intros q Hq. lia.
Qed.
Lemma a12_a_nz : ~ In (Z_to_bv 8 0) a12_a.
Proof. intros [X | []]. apply (f_equal bv_unsigned) in X. vm_compute in X. discriminate X. Qed.
Definition a12_k14 : list byte := repeat (Z_to_bv 8 97) 14.
Definition a12_pl30 : list byte := repeat (Z_to_bv 8 4) 30.
Definition a12_r14 : ctl * list byte * Z := sl_sends 0 (CTL 3 0 0 0 0) [] 0 (ge_bytes (a12_ks1 a12_k14)).
Lemma RI_rm_cnl_pre_K14_sat : lfcx -> exists cx t m si h j0 e1 h1 ev LB c2 O2 cap2,
  fr_RINV cx t m /\ rm_at cx m si h j0 /\ rm_rr_ok m h j0 e1 h1 ev LB c2 O2 cap2 /\
  Forall (fun e => Forall (fun k => 14 <= Z.of_nat (length (gestures_end_b_c.key_text k))) (re_keys e)) (lm_es m).
Proof.
  intros cx0. exists (a12_cx cx0 30 a12_pl30), 0, (a12_m 19 (a12_H1 a12_k14) (a12_ks1 a12_k14) 0), 0%nat,
    (a12_src (a12_H1 a12_k14)), 0%nat, (a12_ent (a12_ks1 a12_k14)), (a12_src (a12_H1 a12_k14)), 0, [],
    (fst (fst a12_r14)), (snd (fst a12_r14)), (snd a12_r14).
  split.
  { apply a12_RINV; try lia.
    - apply NoDup_ListNoDup. repeat constructor. intros [].
    - intros y. split; intros Hy; exact Hy.
    - apply NoDup_ListNoDup. repeat constructor. intros [].
    - cbn. lia.
    - unfold gestures_end_b_c.keys_total, a12_ks1, a12_k14, gestures_end_b_c.key_text. cbn. lia. }
  split; [apply a12_rm_at; [lia | lia | reflexivity]|].
  split; [apply a12_rr_ok; reflexivity|].
  constructor; [|constructor]. constructor; [|constructor]. cbn. lia.
Qed.
Lemma RI_rm_cshe_pre_nz_sat : lfcx -> exists cx t m si h j0 e1 h1 ev LB c2 O2 cap2 E' H',
  fr_RINV cx t m /\ rm_at cx m si h j0 /\ rm_rr_ok m h j0 e1 h1 ev LB c2 O2 cap2 /\ rm_cnl_ok h1 E' H' /\
  lm_gn m = 0 /\ Forall (fun r => ~ In (Z_to_bv 8 0) (snd r)) (hl_recs H').
Proof.
  intros cx0. exists (a12_cx cx0 10 a12_pl), 0, (a12_m 6 (a12_H1 a12_a) (a12_ks1 a12_a) 0), 0%nat,
    (a12_src (a12_H1 a12_a)), 0%nat, (a12_ent (a12_ks1 a12_a)), (a12_src (a12_H1 a12_a)), 0, [],
    (fst (fst (a12_r a12_a))), (snd (fst (a12_r a12_a))), (snd (a12_r a12_a)), a12_E0, (a12_H1 a12_a).
  split; [apply a12_RINV1; [reflexivity | lia]|]. split; [apply a12_rm_at1|].
  split; [apply a12_rr_ok; reflexivity|]. split; [apply a12_cnl_ok, a12_nd1|]. split; [reflexivity|].
  constructor; [exact a12_a_nz | constructor].
Qed.
Lemma RI_rm_csd_gn_sat : lfcx -> exists cx t m si h j0 e1 h1 ev LB c2 O2 cap2 E' H' H'' ds cc,
  fr_RINV cx t m /\ rm_at cx m si h j0 /\ rm_rr_ok m h j0 e1 h1 ev LB c2 O2 cap2 /\ rm_cnl_ok h1 E' H' /\
  rm_cshe_ok m (set_exp_held h1 E' H') O2 (rm_A1 m h1) H'' ds cc /\ 0 <= lm_gn m <= 1.
Proof.
  intros cx0. exists (a12_cx cx0 10 a12_pl), 0, (a12_m 6 (a12_H1 a12_a) (a12_ks1 a12_a) 0), 0%nat,
    (a12_src (a12_H1 a12_a)), 0%nat, (a12_ent (a12_ks1 a12_a)), (a12_src (a12_H1 a12_a)), 0, [],
    (fst (fst (a12_r a12_a))), (snd (fst (a12_r a12_a))), (snd (a12_r a12_a)), a12_E0, (a12_H1 a12_a),
    (HL 0 8 [] []), [(0, a12_a)], 6.
  split; [apply a12_RINV1; [reflexivity | lia]|]. split; [apply a12_rm_at1|].
  split; [apply a12_rr_ok; reflexivity|]. split; [apply a12_cnl_ok, a12_nd1|].
  split; [|cbn; lia].
  unfold rm_cshe_ok. split; [reflexivity|]. split; [reflexivity|]. split; [apply NoDup_ListNoDup; constructor|].
  split; [lia|]. right. split; [reflexivity|]. vm_compute. reflexivity.
Qed.

(* RI_rm_found's premises: the open-entry state a12_m0, op 4 at the cursor 6, slot 0 *)
Lemma RI_rm_found_sat : lfcx -> exists cx t m si h,
  ReplyRINVB.fr_RINV cx t m /\ 0 <= lm_k m < c_n cx /\ lm_O m = [] /\ in_byte cx (lm_k m) mod 10 = 4 /\
  pick (lm_hs m) (W_LLVMFuzzerTestOneInput_remove.rm_kb cx m) = Some si /\ nth si (lm_hs m) None = Some h.
Proof.
  intros cx0. exists (a12_cx cx0 10 a12_pl), 0, a12_m0, 0%nat, (a12_src (a12_H1 a12_a)).
  pose proof (a12_rm_at0 cx0) as (Hk & HO & Hb & Hp & _ & Hh & _).
  split; [apply a12_RINV0|]. split; [exact Hk|]. split; [exact HO|]. split; [exact Hb|].
  split; [exact Hp | exact Hh].
Qed.
(* RI_rm_step's premises: RI_rm_csd_gn_sat's state meets them (its last conjunct, the gone range, is extra) *)
Lemma RI_rm_step_sat : lfcx -> exists cx t m si h j0 e1 h1 ev LB c2 O2 cap2 E' H' H'' ds cc,
  ReplyRINVB.fr_RINV cx t m /\ W_LLVMFuzzerTestOneInput_remove.rm_at cx m si h j0 /\
  W_LLVMFuzzerTestOneInput_remove.rm_rr_ok m h j0 e1 h1 ev LB c2 O2 cap2 /\
  W_LLVMFuzzerTestOneInput_remove.rm_cnl_ok h1 E' H' /\
  W_LLVMFuzzerTestOneInput_remove.rm_cshe_ok m (set_exp_held h1 E' H') O2 (W_LLVMFuzzerTestOneInput_remove.rm_A1 m h1) H'' ds cc.
Proof.
  intros cx0.
  destruct (RI_rm_csd_gn_sat cx0) as (cx & t & m & si & h & j0 & e1 & h1 & ev & LB & c2 & O2 & cap2 & E' & H' & H'' & ds & cc &
    HRI & Hat & Hrr & Hcnl & Hcs & _).
  exists cx, t, m, si, h, j0, e1, h1, ev, LB, c2, O2, cap2, E', H', H'', ds, cc.
  exact (conj HRI (conj Hat (conj Hrr (conj Hcnl Hcs)))).
Qed.
End rinvb_rm_a12.
