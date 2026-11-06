(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: fr_RINV, a concrete definition of the loop's relational invariant RINV of the
   entry walk of fuzz_reply's LLVMFuzzerTestOneInput (lib/A/W_LLVMFuzzerTestOneInput_cut.v:332, the Section variable
   `RINV : lfcx -> Z -> lmod -> Prop` that lcut carries at every cut point), and, below it, each model rule over RINV
   that a W8 segment takes as a Section hypothesis, restated with RINV := fr_RINV (the `_obl` definitions).  The last
   section proves the obligations that read fr_RINV alone or step only the cursor and the flags; the rest are open.
   The shape is the plain proof's (lib/Prog/SlotInv.v:253-314): relay_at's pairing of the relay's entries with the
   open harness sources (Forall2 pair_ok es hj, NoDup (map snd hj), every slot outside hj closed, the entries' fds
   distinct and in [FIRST_FD, FIRST_FD + nfd)), pair_ok's model clauses, LI's input-cost bound
   (slot_cost es hj <= k, k <= n < INPUT_MAX) and globals_at's link between g_gone and the controller's flags.
   What differs from the plain LI, and why:
   - The COUNTING invariant `2 * nfd <= t + 1 + nopen` replaces the plain `0 <= nfd <= t + 1` (SlotInv.v:309).  The
     plain bound allows nfd = 512 at t = 511, so it does not give op_add's `nfd < OPS_MAX` (a Theorem Labs lane's ruling on
     a Theorem Labs lane's finding).  Every operation keeps the counting invariant (fuzz_reply.c:577-593: op_add raises g_nfd
     only when it opens a slot; :619-631: op_remove closes the slot it removes; no other operation opens or closes a
     slot), and with t < OPS_MAX and a free slot it gives nfd <= 257.  The plain bound follows from it and the
     fd clauses (nopen <= nfd, since the open slots' fds are distinct and in [100, 100 + nfd)).
   - No upper bound on t and no `k <= n`.  Most RI_* rules step `RINV cx t m -> RINV cx (t + 1) m'` with no
     `t < OPS_MAX` premise and, for the small arms, no `lm_k m < c_n cx` premise, so a t- or k-bound in RINV would
     make those rules false.  The input-cost bound is therefore split into `cost <= k` (k only grows) and
     `cost <= n` (the rules that raise the cost all carry `lm_k m < c_n cx`).
   - pair_ok's src_at (memory) is amodel_at's slot here; pair_ok keeps the model slot `nth (snd p) (lm_hs m) None =
     Some (fst p)`.  pair_ok's t-bounds on the pending list (SlotInv.v:261-262) are allocator room, which the
     A-proof keeps in LS (LS_write_room, LS_drain_pre); they are not here.
   - The cost counts the relay's unfinished line by its bytes, `length (re_U e)`, where SlotInv.v:56 counts
     `re_used e`: the two are equal under aentry_ok (W_rep.v:127), but the arms' rules see only the model, and W7's
     drain fixes re_U, not re_used (dr_step_ok, W_LLVMFuzzerTestOneInput_drain.v:601).
   - The entries' model facts that aentry_ok (W_rep.v:122-137) states in memory and that RINV-only rules read
     (RI_pads, RI_pair, RI_rm_cnlr_eof, the exit's end matching) are fr_entry_ok.
   The `_obl` definitions are grouped by segment file, each with the rule's file:line.  Rules on atop's head (head,
   drain, small, write, exit, add) are read off the segment files (Required below); rules that exist only on a hand
   branch are stated over verbatim copies of that branch's model notions (each block names the branch, file and line
   it copies; replace the block by a Require when the branch merges).  A rule that is false against fr_RINV has an
   `_obl` (verbatim) and a `_fix_obl` (the amended text, with the premise the arm already holds).  The last section
   proves every rule of W_LLVMFuzzerTestOneInput_top.v (SEG_HEAD's, ARM_add's, the small arms') in the form that
   holds. *)
(* Modified by Theorem Labs, 2026-10: lib/B/ReplyRINVBHead.v, new, holds part of lib/A/ReplyRINV.v: its helpers
   fr_Forall2_r, fr_Forall2_comb, fr_comb_inj, fr_pair_of_open, RI_fds_holds, fr_F2_nth, fr_Forall2_map, fr_upd_hs_*,
   fr_hkeep, fr_upd_pair, fr_pair_upd, fr_cost_map and fr_step_upd, copied as hb_* (renamed, image B's small-file
   names qualified), and the six rules RI_src_b, RI_pair_b, RI_close_b, RI_eintr_b, RI_sendmax_b, RI_default_b,
   proved as A's RI_*_holds over lib/B/ReplyRINVB.v's fr_RINV. *)
(* proves no function (rule 24; kind: model rules): six of image B top_x's RINV obligations at RINV := ReplyRINVB.fr_RINV
   (row G-BRI-head; B-TOPX-OWNERS.md (sha256 705727227472; internal record) rows 51, 53, 59, 60, 61, 62).
   Each `_b` lemma states, token for token, the Section hypothesis of the same name in lib/B/ReplyBTop.v
   (a working branch f908a004fd1, :100, :101, :105-108), each for every rc and fx:
     RI_src_b     : ReplyBTop.v :100 (B top_x RI_src,     Btop:321)
     RI_pair_b    : ReplyBTop.v :101 (B top_x RI_pair,    Btop:327)
     RI_close_b   : ReplyBTop.v :105 (B top_x RI_close,   Btop:378)
     RI_eintr_b   : ReplyBTop.v :106 (B top_x RI_eintr,   Btop:381)
     RI_sendmax_b : ReplyBTop.v :107 (B top_x RI_sendmax, Btop:384)
     RI_default_b : ReplyBTop.v :108 (B top_x RI_default, Btop:387)
   The image-A twins (a working branch 8da615a239d): lib/A/ReplyRINV.v RI_src_holds (:727),
   RI_close_holds (:941), RI_eintr_holds (:953), RI_sendmax_holds (:837), RI_default_holds (:843), and
   lib/A/ReplyRINV_a3.v RI_pair_holds (:149).  Each proof below is A's, relocated: fr_RINV, fr_pair_ok, fr_relay,
   fr_gone, fr_cost, fr_pair_cost and fr_step_k are lib/B/ReplyRINVB.v's (the same text as A's ReplyRINV.v :97-183,
   :805-818, by that file's header); sm_close / sm_eintr / sm_sendmax / sm_default / sm_dg / sm_kn / upd_hs /
   upd_closed / upd_eintr are lib/B/W_LLVMFuzzerTestOneInput_small.v :386-454 (the same text as A's _small.v); pick,
   nopen, in_byte, c_n are lib/B/W_LLVMFuzzerTestOneInput_cut.v :644-656; dr_pick, dr_e0 are
   lib/B/W_LLVMFuzzerTestOneInput_drain_defs.v :121, :173.  A's helpers that ReplyRINVB.v does not carry are copied
   here as hb_* (A's ReplyRINV.v line in each comment), unchanged but for the name.  RI_pair uses RI_fds (A
   ReplyRINV.v :739), copied as hb_fds.
   No image constant is read: these rules are over the model records only (lmod, hsrc, rentry), so no address or
   numeral of image A or image B enters any statement or proof here. *)
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
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require drain_b_c gestures_end_b_c SlotInv.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_rep W_contract W_sites W_frame.
(* RelocB's sink-instance guard (after the Import of YE2k), as lib/B's segment files Require it *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require ReplyGuardB.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_LLVMFuzzerTestOneInput_cut.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_LLVMFuzzerTestOneInput_head.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require W_LLVMFuzzerTestOneInput_small
  W_LLVMFuzzerTestOneInput_drain_defs.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import ReplyRINVB.
Import ListNotations.
Local Unset Lia Cache. Local Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

Section hb.
Context {rc : YM05.RunCeil}.

(* ---- the relay table and its sources (A ReplyRINV.v :605-692) *)
(* A :605 fr_Forall2_r *)
Lemma hb_Forall2_r : forall (X Y : Type) (R : X -> Y -> Prop) l1 l2,
  Forall2 R l1 l2 -> forall y, In y l2 -> exists x, In x l1 /\ R x y.
Proof.
  intros X Y R l1 l2 H. induction H as [|x y l1 l2 Hxy _ IH]; intros z Hz; [destruct Hz|].
  destruct Hz as [<- | Hz]; [exists x; split; [left; reflexivity | exact Hxy]|].
  destruct (IH z Hz) as (x' & Hx' & HR). exists x'. split; [right; exact Hx' | exact HR].
Qed.
(* A :612 fr_Forall2_comb *)
Lemma hb_Forall2_comb : forall (X Y : Type) (R : X -> Y -> Prop) l1 l2,
  Forall2 R l1 l2 -> forall y, In y l2 -> exists x, In (x, y) (combine l1 l2) /\ R x y.
Proof.
  intros X Y R l1 l2 H. induction H as [|x y l1 l2 Hxy _ IH]; intros z Hz; [destruct Hz|].
  destruct Hz as [<- | Hz]; [exists x; split; [left; reflexivity | exact Hxy]|].
  destruct (IH z Hz) as (x' & Hx' & HR). exists x'. split; [right; exact Hx' | exact HR].
Qed.
(* A :620 fr_comb_inj: two entries of the table with the same fd are one row, so their sources are one *)
Lemma hb_comb_inj : forall (Y : Type) (es : list rentry) (hj : list Y), List.NoDup (map re_fd es) ->
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
(* A :634 fr_pair_of_open: an open slot is some entry's source *)
Lemma hb_pair_of_open : forall m t hj i h, Forall2 (fr_pair_ok m t) (lm_es m) hj ->
  (forall i, (i < 4)%nat -> SlotInv.slot_open hj i = false -> nth i (lm_hs m) None = None) ->
  (i < 4)%nat -> nth i (lm_hs m) None = Some h ->
  exists e p, In (e, p) (combine (lm_es m) hj) /\ fr_pair_ok m t e p /\ snd p = i /\ fst p = h.
Proof.
  intros m t hj i h HF Hcl Hi Hh.
  destruct (SlotInv.slot_open hj i) eqn:Ho; [|rewrite (Hcl i Hi Ho) in Hh; discriminate Hh].
  unfold SlotInv.slot_open in Ho. apply existsb_exists in Ho as (x & Hx & Hxi).
  apply Nat.eqb_eq in Hxi. subst x. apply in_map_iff in Hx as (p & Hpi & Hp).
  destruct (hb_Forall2_comb _ _ _ _ _ HF p Hp) as (e & Hin & HR).
  exists e, p. split; [exact Hin|]. split; [exact HR|]. split; [exact Hpi|].
  destruct HR as (_ & Hn & _). rewrite Hpi, Hh in Hn. injection Hn as Ef. exact (eq_sym Ef).
Qed.
(* A :739 RI_fds_holds: open slots have distinct fds *)
Lemma hb_fds : forall cx t m i1 i2 h1 h2,
  fr_RINV cx t m -> (i1 < 4)%nat -> (i2 < 4)%nat -> i1 <> i2 ->
  nth i1 (lm_hs m) None = Some h1 -> nth i2 (lm_hs m) None = Some h2 -> hs_fd h1 <> hs_fd h2.
Proof.
  intros cx t m i1 i2 h1 h2 (_ & HR & _) Hi1 Hi2 Hne Hh1 Hh2 Hf.
  destruct HR as (_ & Hnd & _ & _ & hj & HF & _ & Hcl & _). apply NoDup_ListNoDup in Hnd.
  destruct (hb_pair_of_open m t hj i1 h1 HF Hcl Hi1 Hh1) as (e1 & p1 & Hin1 & HR1 & Hs1 & Hf1).
  destruct (hb_pair_of_open m t hj i2 h2 HF Hcl Hi2 Hh2) as (e2 & p2 & Hin2 & HR2 & Hs2 & Hf2).
  apply Hne. rewrite <- Hs1, <- Hs2. f_equal.
  apply (hb_comb_inj _ (lm_es m) hj Hnd e1 p1 e2 p2 Hin1 Hin2).
  destruct HR1 as (_ & _ & E1 & _). destruct HR2 as (_ & _ & E2 & _).
  rewrite <- E1, <- E2, Hf1, Hf2. exact Hf.
Qed.
(* A :1168 fr_F2_nth *)
Lemma hb_F2_nth : forall (T1 T2 : Type) (R : T1 -> T2 -> Prop) l1 l2, Forall2 R l1 l2 ->
  forall i d1 d2, (i < length l1)%nat -> R (nth i l1 d1) (nth i l2 d2).
Proof.
  intros T1 T2 R l1 l2 H. induction H as [|x y l1 l2 Hxy _ IH]; intros [|i] d1 d2 Hi; cbn [length] in Hi;
    try lia; cbn [nth]; [exact Hxy | apply IH; lia].
Qed.

(* ---- the small arms' slot updates (A ReplyRINV.v :801-803, :852-938; fuzz_reply.c:712-713 `s->closed = 1`,
   :721-722 `s->eintr = 1`) *)
(* A :801 fr_Forall2_map *)
Lemma hb_Forall2_map : forall (T1 T2 T3 : Type) (R : T1 -> T2 -> Prop) (R' : T1 -> T3 -> Prop) (g : T2 -> T3) l1 l2,
  (forall x y, R x y -> R' x (g y)) -> Forall2 R l1 l2 -> Forall2 R' l1 (map g l2).
Proof. intros T1 T2 T3 R R' g l1 l2 H HF. induction HF; cbn [map]; constructor; auto. Qed.
(* A :852 fr_upd_hs_length *)
Lemma hb_upd_hs_length : forall i f l, length (W_LLVMFuzzerTestOneInput_small.upd_hs i f l) = length l.
Proof.
  intros i f l. revert i. induction l as [|o l IH]; intros [|i]; cbn [W_LLVMFuzzerTestOneInput_small.upd_hs length].
  - reflexivity.
  - reflexivity.
  - destruct o; reflexivity.
  - rewrite IH. reflexivity.
Qed.
(* A :860 fr_upd_hs_nth *)
Lemma hb_upd_hs_nth : forall i f l j,
  nth j (W_LLVMFuzzerTestOneInput_small.upd_hs i f l) None =
  if Nat.eqb j i then option_map f (nth j l None) else nth j l None.
Proof.
  intros i f l. revert i. induction l as [|o l IH]; intros i j.
  - destruct i as [|i], j as [|j]; cbn; try reflexivity. destruct (Nat.eqb j i); reflexivity.
  - destruct i as [|i], j as [|j]; cbn.
    + destruct o; reflexivity.
    + destruct o; reflexivity.
    + reflexivity.
    + apply IH.
Qed.
(* A :871 fr_upd_hs_nopen *)
Lemma hb_upd_hs_nopen : forall i f l, nopen (W_LLVMFuzzerTestOneInput_small.upd_hs i f l) = nopen l.
Proof.
  intros i f l. unfold nopen. f_equal. revert i. induction l as [|o l IH]; intros [|i].
  - reflexivity.
  - reflexivity.
  - destruct o; reflexivity.
  - cbn [W_LLVMFuzzerTestOneInput_small.upd_hs]. destruct o; cbn [List.filter length]; rewrite IH; reflexivity.
Qed.
(* A :880 fr_hkeep: the fields of a source that fr_pair_ok and fr_cost read *)
Definition hb_hkeep (h' h : hsrc) : Prop :=
  hs_fd h' = hs_fd h /\ hs_overlong h' = hs_overlong h /\ hs_W h' = hs_W h /\ hs_held h' = hs_held h /\
  hs_expected h' = hs_expected h /\ pending_stream h' = pending_stream h /\ hs_off h' = hs_off h.
(* A :883 fr_upd_pair *)
Definition hb_upd_pair (f : hsrc -> hsrc) (i : nat) (p : hsrc * nat) : hsrc * nat :=
  if Nat.eqb (snd p) i then (f (fst p), snd p) else p.
(* A :885 fr_pair_upd *)
Lemma hb_pair_upd : forall f i m m' t e p, (forall h, hb_hkeep (f h) h) ->
  lm_hs m' = W_LLVMFuzzerTestOneInput_small.upd_hs i f (lm_hs m) -> fr_pair_ok m t e p ->
  fr_pair_ok m' (t + 1) e (hb_upd_pair f i p).
Proof.
  intros f i m m' t e [h j] Hf Ehs Hp.
  destruct Hp as (Hj & Hn & Hfd & Hre & Hss & Hnd & Hexp & Hec & Hhc & Hpe & Hoff). cbn [fst snd] in *.
  unfold SlotInv.WRITE_MAX in Hpe.
  unfold hb_upd_pair. cbn [fst snd].
  destruct (Nat.eqb j i) eqn:Eji.
  - apply Nat.eqb_eq in Eji. subst i. destruct (Hf h) as (F1 & F2 & F3 & F4 & F5 & F6 & F7).
    unfold fr_pair_ok. cbn [fst snd]. rewrite Ehs, hb_upd_hs_nth, Nat.eqb_refl, Hn. cbn [option_map].
    rewrite F1, F2, F3, F4, F5, F6, F7.
    refine (conj Hj (conj eq_refl (conj Hfd (conj Hre (conj Hss (conj Hnd (conj Hexp (conj Hec
      (conj Hhc (conj _ Hoff)))))))))).
    unfold SlotInv.WRITE_MAX. lia.
  - unfold fr_pair_ok. cbn [fst snd]. rewrite Ehs, hb_upd_hs_nth, Eji.
    refine (conj Hj (conj Hn (conj Hfd (conj Hre (conj Hss (conj Hnd (conj Hexp (conj Hec
      (conj Hhc (conj _ Hoff)))))))))).
    unfold SlotInv.WRITE_MAX. lia.
Qed.
(* A :904 fr_cost_map *)
Lemma hb_cost_map : forall (g : hsrc * nat -> hsrc * nat),
  (forall p, pending_stream (fst (g p)) = pending_stream (fst p)) ->
  forall es hj, fr_cost es (map g hj) = fr_cost es hj.
Proof.
  intros g Hg es. unfold fr_cost. induction es as [|e es IH]; intros [|p hj];
    cbn [map combine fold_right fst snd]; try reflexivity.
  rewrite IH. unfold fr_pair_cost. rewrite Hg. reflexivity.
Qed.
(* A :913 fr_step_upd: an operation that updates one slot's flags in place *)
Lemma hb_step_upd : forall f i cx t m m', (forall h, hb_hkeep (f h) h) -> fr_RINV cx t m ->
  lm_hs m' = W_LLVMFuzzerTestOneInput_small.upd_hs i f (lm_hs m) -> lm_es m' = lm_es m ->
  lm_nfd m' = lm_nfd m -> lm_k m <= lm_k m' -> fr_gone m' -> fr_RINV cx (t + 1) m'.
Proof.
  intros f i cx t m m' Hf ((HC & Hnfd) & HR & Hn & _) Ehs Ees Enfd Hk HG.
  destruct HR as (Hlen & Hnd & Hrng & Hent & hj & HF & HNDs & Hcl & Hc & Hcn).
  assert (Esnd : map snd (map (hb_upd_pair f i) hj) = map snd hj).
  { rewrite List.map_map. apply List.map_ext. intros [h j]. unfold hb_upd_pair. cbn [fst snd].
    destruct (Nat.eqb j i); reflexivity. }
  split; [|split; [|split; [exact Hn | exact HG]]].
  - unfold fr_count. rewrite Ehs, Enfd, hb_upd_hs_nopen. lia.
  - unfold fr_relay. rewrite Ees, Enfd.
    split; [rewrite Ehs, hb_upd_hs_length; exact Hlen|].
    split; [exact Hnd|]. split; [exact Hrng|]. split; [exact Hent|].
    exists (map (hb_upd_pair f i) hj).
    split; [exact (hb_Forall2_map _ _ _ _ _ _ _ _ (fun e p => hb_pair_upd f i m m' t e p Hf Ehs) HF)|].
    split; [rewrite Esnd; exact HNDs|].
    split.
    { intros j Hj Ho. unfold SlotInv.slot_open in Ho. rewrite Esnd in Ho.
      rewrite Ehs, hb_upd_hs_nth, (Hcl j Hj Ho). destruct (Nat.eqb j i); reflexivity. }
    rewrite hb_cost_map.
    + split; [lia | exact Hcn].
    + intros [h j]. unfold hb_upd_pair. cbn [fst snd]. destruct (Nat.eqb j i).
      * exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (Hf h))))))).
      * reflexivity.
Qed.
End hb.

(* ================================================================== the six obligations, as ReplyBTop.v states them *)
(* ReplyBTop.v :100 RI_src (A ReplyRINV.v :727 RI_src_holds) *)
Lemma RI_src_b : forall (rc : YM05.RunCeil) (fx : YK11.FPState) (cx : @lfcx rc) (t : Z) (m : lmod) (si : nat)
  (h : hsrc), @ReplyRINVB.fr_RINV rc cx t m -> @W_LLVMFuzzerTestOneInput_drain_defs.dr_pick rc cx m si h ->
  hl_recs (hs_expected h) = [] /\ @NoDup (list Z) (CheckRep.texts (hs_held h)) /\ 0 <= hs_fd h < 2 ^ 31.
Proof.
  intros rc fx cx t m si h ((_ & Hnfd) & HR & _ & _) (_ & Hsi & Hh).
  destruct HR as (_ & _ & Hrng & _ & hj & HF & _ & Hcl & _).
  destruct (hb_pair_of_open m t hj si h HF Hcl Hsi Hh) as (e & p & Hin & HRp & _ & <-).
  destruct HRp as (_ & _ & Hfd & _ & _ & Hnd & Hexp & _).
  split; [exact Hexp|]. split; [exact Hnd|].
  assert (He : In e (lm_es m)) by (eapply in_combine_l; exact Hin).
  rewrite Forall_forall in Hrng. specialize (Hrng e He).
  unfold OPS_MAX in Hnfd. rewrite Hfd. lia.
Qed.

(* ReplyBTop.v :101 RI_pair (A ReplyRINV_a3.v :149 RI_pair_holds): the relay row with the picked source's fd is
   that source's row *)
Lemma RI_pair_b : forall (rc : YM05.RunCeil) (fx : YK11.FPState) (cx : @lfcx rc) (t : Z) (m : lmod) (si : nat)
  (h : hsrc) (j : nat), @ReplyRINVB.fr_RINV rc cx t m -> @W_LLVMFuzzerTestOneInput_drain_defs.dr_pick rc cx m si h ->
  (j < @length rentry (lm_es m))%nat ->
  re_fd (@nth rentry j (lm_es m) W_LLVMFuzzerTestOneInput_drain_defs.dr_e0) = hs_fd h ->
  re_eof (@nth rentry j (lm_es m) W_LLVMFuzzerTestOneInput_drain_defs.dr_e0) = 0 ->
  re_skip (@nth rentry j (lm_es m) W_LLVMFuzzerTestOneInput_drain_defs.dr_e0) = hs_overlong h /\
  (re_skip (@nth rentry j (lm_es m) W_LLVMFuzzerTestOneInput_drain_defs.dr_e0) = 0 ->
   bzs (re_U (@nth rentry j (lm_es m) W_LLVMFuzzerTestOneInput_drain_defs.dr_e0)) = bzs (hs_W h)) /\
  @length byte (re_pad1 (@nth rentry j (lm_es m) W_LLVMFuzzerTestOneInput_drain_defs.dr_e0)) = 4%nat /\
  @length byte (re_pad2 (@nth rentry j (lm_es m) W_LLVMFuzzerTestOneInput_drain_defs.dr_e0)) = 4%nat.
Proof.
  intros rc fx cx t m si h j HRI (_ & Hsi & Hh) Hj Hfdj Heof.
  pose proof HRI as (_ & HR & _).
  destruct HR as (_ & _ & _ & Hent & hj & HF & _ & _ & _).
  pose proof (hb_F2_nth _ _ _ _ _ HF j W_LLVMFuzzerTestOneInput_drain_defs.dr_e0 (h, si) Hj) as Hp0.
  assert (Hs0 : snd (nth j hj (h, si)) = si).
  { destruct Hp0 as (H4 & Hn0 & Hf0 & _).
    destruct (Nat.eq_dec (snd (nth j hj (h, si))) si) as [E | Ne]; [exact E | exfalso].
    apply (hb_fds cx t m _ si _ h HRI H4 Hsi Ne Hn0 Hh). rewrite Hf0. exact Hfdj. }
  assert (Ep0 : nth j hj (h, si) = (h, si)).
  { destruct Hp0 as (_ & Hn0 & _). rewrite Hs0, Hh in Hn0. injection Hn0 as Ef.
    apply injective_projections; [exact (eq_sym Ef) | exact Hs0]. }
  rewrite Ep0 in Hp0.
  destruct Hp0 as (_ & _ & _ & Hre & _). cbn [fst snd] in Hre.
  destruct (Hre Heof) as (S1 & W1).
  rewrite Forall_forall in Hent.
  assert (He : In (nth j (lm_es m) W_LLVMFuzzerTestOneInput_drain_defs.dr_e0) (lm_es m))
    by (apply nth_In; exact Hj).
  destruct (Hent _ He) as (_ & P1 & P2 & _).
  split; [exact S1|]. split; [exact W1|]. split; [exact P1 | exact P2].
Qed.

(* ReplyBTop.v :105 RI_close (A ReplyRINV.v :941 RI_close_holds): close sets the picked slot's flag *)
Lemma RI_close_b : forall (rc : YM05.RunCeil) (fx : YK11.FPState) (cx : @lfcx rc) (t : Z) (m : lmod) (i : nat),
  @ReplyRINVB.fr_RINV rc cx t m ->
  pick (lm_hs m) (if lm_k m + 1 <? @c_n rc cx then @in_byte rc cx (lm_k m + 1) else 0) = @Some nat i ->
  @ReplyRINVB.fr_RINV rc cx (t + 1) (@W_LLVMFuzzerTestOneInput_small.sm_close rc cx m i).
Proof.
  intros rc fx cx t m i H _. apply (hb_step_upd W_LLVMFuzzerTestOneInput_small.upd_closed i cx t m _).
  - intros h. unfold hb_hkeep. repeat split; reflexivity.
  - exact H.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - unfold W_LLVMFuzzerTestOneInput_small.sm_close, W_LLVMFuzzerTestOneInput_small.sm_kn. cbn [lm_k].
    destruct (lm_k m + 1 <? c_n cx); lia.
  - destruct H as (_ & _ & _ & HG). exact HG.
Qed.

(* ReplyBTop.v :106 RI_eintr (A ReplyRINV.v :953 RI_eintr_holds): eintr sets the picked slot's flag *)
Lemma RI_eintr_b : forall (rc : YM05.RunCeil) (fx : YK11.FPState) (cx : @lfcx rc) (t : Z) (m : lmod) (i : nat),
  @ReplyRINVB.fr_RINV rc cx t m ->
  pick (lm_hs m) (if lm_k m + 1 <? @c_n rc cx then @in_byte rc cx (lm_k m + 1) else 0) = @Some nat i ->
  @ReplyRINVB.fr_RINV rc cx (t + 1) (@W_LLVMFuzzerTestOneInput_small.sm_eintr rc cx m i).
Proof.
  intros rc fx cx t m i H _. apply (hb_step_upd W_LLVMFuzzerTestOneInput_small.upd_eintr i cx t m _).
  - intros h. unfold hb_hkeep. repeat split; reflexivity.
  - exact H.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - unfold W_LLVMFuzzerTestOneInput_small.sm_eintr, W_LLVMFuzzerTestOneInput_small.sm_kn. cbn [lm_k].
    destruct (lm_k m + 1 <? c_n cx); lia.
  - destruct H as (_ & _ & _ & HG). exact HG.
Qed.

(* ReplyBTop.v :107 RI_sendmax (A ReplyRINV.v :837 RI_sendmax_holds): only the cursor and the send flag change *)
Lemma RI_sendmax_b : forall (rc : YM05.RunCeil) (fx : YK11.FPState) (cx : @lfcx rc) (t : Z) (m : lmod),
  @ReplyRINVB.fr_RINV rc cx t m ->
  @ReplyRINVB.fr_RINV rc cx (t + 1)
    (@W_LLVMFuzzerTestOneInput_small.sm_sendmax rc cx m
       (if lm_k m + 1 <? @c_n rc cx then @in_byte rc cx (lm_k m + 1) else 0)).
Proof.
  intros rc fx cx t m H. apply (fr_step_k cx t m _ H); try reflexivity.
  - unfold W_LLVMFuzzerTestOneInput_small.sm_sendmax, W_LLVMFuzzerTestOneInput_small.sm_kn. cbn [lm_k].
    destruct (lm_k m + 1 <? c_n cx); lia.
  - destruct H as (_ & _ & _ & HG). exact HG.
Qed.

(* ReplyBTop.v :108 RI_default (A ReplyRINV.v :843 RI_default_holds): the cursor and the controller's flags change;
   the flags keep their link to g_gone (lm_gn becomes 1, and the default arm sets one of the three) *)
Lemma RI_default_b : forall (rc : YM05.RunCeil) (fx : YK11.FPState) (cx : @lfcx rc) (t : Z) (m : lmod),
  @ReplyRINVB.fr_RINV rc cx t m ->
  @ReplyRINVB.fr_RINV rc cx (t + 1)
    (@W_LLVMFuzzerTestOneInput_small.sm_default rc cx m (@W_LLVMFuzzerTestOneInput_small.sm_dg rc cx m)).
Proof.
  intros rc fx cx t m H. apply (fr_step_k cx t m _ H); try reflexivity.
  - unfold W_LLVMFuzzerTestOneInput_small.sm_default, W_LLVMFuzzerTestOneInput_small.sm_kn. cbn [lm_k].
    destruct (lm_k m + 1 <? c_n cx); lia.
  - unfold fr_gone, W_LLVMFuzzerTestOneInput_small.sm_default; cbn [lm_gn lm_c ct_cl ct_br ct_dd].
    split; [intros Hg; discriminate Hg|]. intros _.
    destruct (W_LLVMFuzzerTestOneInput_small.sm_dg cx m); [left | right; right]; reflexivity.
Qed.
