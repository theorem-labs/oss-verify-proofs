(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ARM_drain (op 2) of the ASan walk of fuzz_reply's LLVMFuzzerTestOneInput over the
   GENERIC allocator relation ARx: the ARx conversion of lib/A/W_LLVMFuzzerTestOneInput_drain.v's lf_arm_drain.
   The AR proof is a Theorem Labs lane's: a working branch 129f255c729 (dr_found_join / lf_arm_drain Qed on W8
   base ec4dd616ed1: fresh rc=0 wall 604, Print Assumptions 13 Prim* + funext), adapted to the current cut on
   a working branch cdc87da7be0 (b5 w8c rc=0).  lf_arm_drain_x's statement is the text of the
   Section hypothesis ARM_drain of lib/A/W_LLVMFuzzerTestOneInput_cut_x.v Section w (:349), checked at the end
   (lf_arm_drain_x_check).
   THE ROOM ROUND (a working branch, on meet 393c0b2cb2a): the cut's invariants take NP
   (lcut_x's NP S after LSx; DLK carries it); DRAIN / CNL take the room record RP (RP_NP ties its rp_RM to NP) and
   their count premises cnt_ok_pk RP (dr_pk ..) / (cnl_pk ..), the first from LS_cnt at the cut, the second at the
   state the drain leaves through the two pure model rules DR_CNT_grow / DR_CNT_cnl; LS_drain_pre's conjunct 5 is
   the peak form (with the three premises s5-r1d's rows take); LS_cnl_pre / LS_drain_step are a Theorem Labs lane's
   TX_LS_cnl_pre / TX_LS_drain_step (d0d75bf92db), whose premises dc_stB (dcB_out) and dc_stE export.
   The method (W8Entry-2's add_x method): this file Requires _drain.v and CITES every item of it that reads no AR
   and no Section variable (the model notions, the symbolic states, the pure list / byte lemmas); every item that
   reads a Section variable but no AR is restated VERBATIM (same name, same proof, up to cut_x's LS -> LSx and the
   local names Hp / Hp1 / Hp2 / HP0 -> Hpo / Hp1o / Hp2o / HPm0, which the ghost lists and HP0 take); every
   AR-reading item is CONVERTED, keeping its name: AR -> ARx with the ghost head list (Hpe at the entry, Hp / Hp2 /
   Hp3 / Hpc after the state they belong to), al_* -> alx_*, the journal lemmas -> W_journal_x / YCbqG / W_frame_x's
   _x twins (the journal's image clause takes `~ Exists (in_zr a) PST`, from HPST), paj_run(_to)_tok ->
   paj_run(_to)_tok_x, the callee specs -> their kit _x forms (W_contract_x / W_sites_x), aj_gx_entry_at ->
   aj_gx_entry_at_x.  The arm's states DST / DLK / dc_at / dcB_post take the entry's Hpe beside cx and the state's
   Hp beside S; dr_callZ's post predicate K takes the callee's Hp2 beside S2.
   Section hypotheses beyond cut_x's Section w header (B .. RINV, verbatim):
     MMAX / TL / the G-coverage and image facts (HGs, HG_DR, HGlock, HG_GK, HERR_HI, DR_ROM_OUT, GWR, HZS, HAP) /
       RI_* / LS_* (LS is cut_x's LSx) - _drain.v's, verbatim;
     DRAIN / CSD / CNLR / CNL - dr_spec_x / csd_spec_x / cnlr_spec_x / cnl_spec_x at the walk's PST / ARx;
     ALOCK / AUNLOCK - alock_realizes_x / aunlock_realizes_x;  ERR - cut_x's errno_law_x;
     HPST - the image is off PST (W_op_add.v Section x's text; trivial at the instance's PST := []);
     BLKR - a live block's request is in [0, 2 ^ 30) (AR's al_blocks carries 0 <= n < MALLOC_MAX = 2 ^ 28, which
       AR_laws_x's alx_blocks does not; the cf instance has 0 <= n < cf_malloc_max as AR_blocks_law_cf's last
       conjunct and cf_malloc_max + 15 <= 2 ^ 30 as YG08cf.v cf_malloc_max_bound).
   ARM_drain takes no allocator rule directly, so it takes no caller-context table.
   ROUTE R (Section drxR at the end; a Theorem Labs lane's segment-twin round, 2026-10-31): lf_arm_drain_xR is the R twin of
   lf_arm_drain_x, stated as cut_x's Section wR hypothesis ARM_drain_R (checked: lf_arm_drain_xR_check).  It takes the
   strict lemma's Section hypotheses without DRAIN and CNL and, after them, R R_refl R_trans WLE_R, then DRAIN_R
   (W_contract_xR.v's dr_spec_xR: drain reallocs and frees, so it may re-hide) and CNL_R (W_contract_xR_g6.v's
   cnl_spec_xR: check_no_loss frees).  The leaves lock / unlock / check_no_loss_read / check_shape_done free nothing and
   keep their strict specs, lifted inside the walk (W_sites_x.v aj_gx_entry_at_xR; SRr_SRrG with WLE_R and YCbqG.v
   ajournal_xR_mono).  Each item of the strict walk that reads the cut's or a callee's journal has an R twin, its name
   suffixed R, whose proof is the strict one over the R twins of the journal lemmas (W_journal_x / YCbqG / W_frame_x /
   W_sites_x / W_kit's paj_branch_xR); the call-free segments (dr_entryR, dr_scanR, dr_nf_joinR, dr_join_latchR) conclude
   strict SRr over the R journal (paj_run_x_xR) and are lifted by SRr_SRrG; the stages with a call conclude SRrG segs R
   (paj_run_x_xG runs, SRrG_bind / SRrG_mono).  The strict lemmas and their proofs are unchanged. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_reply/lib/A/W_LLVMFuzzerTestOneInput_drain_x.v, with its module paths and module names changed; 475 of its 588 lines of code are new or changed and 6933 lines of the source are left out. *)
(* Row B1c (a Theorem Labs lane's FREE-PIECES, a Theorem Labs lane): the drain arm's two post-state LS rules, LS_cnl_pre and
   LS_drain_step (a working branch 129f255c729 lib/A/W_LLVMFuzzerTestOneInput_drain.v:743, :765),
   at the instance LS := fr_LS B (lib/A/ReplyLS.v), RINV := fr_RINV (lib/A/ReplyRINV.v), MT := ameter_triv,
   MMAX := WR_MMAX.

   Both published texts tie the post-state (S' after drain, S' after check_no_loss) to S only by `mo_le MT ...`,
   which is True at ameter_triv (Reusable/YCbp.v), so the post-state's blocks are free and neither text is provable
   for an LS that bounds live bytes.  The lemmas below are the PROPOSED texts: every published premise and the
   published conclusion, plus premises the arm holds at its Qed head, each named with the clause that gives it:
   - dr_post (W_contract.v at 129f255c729, :938-976): the blocks' change :949-950, the cap' it names :943, the entry
     it leaves (:952 aentry_ok e' - W_rep.v aentry_ok's re_cap clause -, :957, :958, :959) and the source (:964,
     :966, :967);
   - dr_spec's premises at the call (W_contract.v :1013 aentry_ok e, :984 asrc_at h, :986 aout_at), whose model
     clauses (W_rep.v aentry_ok, asrc_at with alist_at (HA + 16) _ false, aout_at) the arm holds at the drain call
     (drain.v dc_stB: HEOK, HSRC0, HOUT);
   - check_no_loss's blocks' change (cnl_post, drain.v:238-239);
   - the arm's own facts: `0 <= t < OPS_MAX` (lregs_base, DLK's Ht at drain.v:5414) and `lm_O m = []`
     (dr_at_op, Hatop at drain.v:5413).
   check_no_loss's vocabulary (capstep, capb, tbytes, hbytes, cnl_cap, cnl_room, gmc, cnl_go, cnl_cost) is the
   worktree's lib/A/W_contract.v :1947-2008, the same text as the arm head's stub (drain.v:171-219).

   fr_LS_cnl_pre_p: PROVED at the proposed text.
   fr_LS_drain_step_p: fr_LS v2's potential does NOT pay the drain (a fresh entry's first drain allocates the
   relay's 8192-byte buffer, drain_b_c.v grow_tr :28-31, with no input consumed but the operation's 1-2 bytes, whose
   MB_K credit is 65-130 bytes; see the report), so the published conclusion's PHI conjunct is not provable at
   fr_LS v2.  The lemma carries that one missing fact as the named hypothesis Hpay (dr3_pays) and proves the rest:
   the split of the post-state from the two callees' blocks' changes, the counts and the cursor. *)
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
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import
HarnessRep RelayRep CheckRep RelayKeys RelayModel ListRep.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require
drain_b_c gestures_end_b_c SlotInv SlotReads SlotDrain3Aux SlotPass2Aux RelayCap relay_remove_b_aux.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import W_rep W_contract W_sites W_frame W_op_add.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import W_LLVMFuzzerTestOneInput_cut.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import ReplyLS.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import W_LLVMFuzzerTestOneInput_write.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import W_LLVMFuzzerTestOneInput_drain.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import ReplyRINV.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YCbp.
Import ListNotations.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

(* the instance (ReplyATop.v:93 MT := ameter_triv; W_LLVMFuzzerTestOneInput_write.v:132 WR_MMAX) *)
Local Notation MT := ameter_triv.
Local Notation MMAX := WR_MMAX.
Local Notation zsum l := (fold_right Z.add 0 l).
Local Notation dset := W_LLVMFuzzerTestOneInput_drain.set_nth.

(* ------------------------------------------------------------------ the proposed premises' bundles *)
(* (W_contract.v and W_rep.v at 129f255c729.)  dr_spec's premises at the drain call, model clauses: W_contract.v:983
   aentry_ok B ly S W mem e (W_rep.v aentry_ok: the re_cap clause :124, |re_U| = re_used <= APARTIAL and no NUL in
   re_U :125, the held array's 8 <= re_kh :131-132, the keys' 14 <= |text| :139) *)
Definition dr3_epre (e : rentry) : Prop :=
  (re_cap e = 0 \/ re_cap e = 8192 \/ re_cap e = 16384) /\
  Z.of_nat (length (re_U e)) <= APARTIAL /\ ~ In (Z_to_bv 8 0) (re_U e) /\
  (re_hp e <> 0 -> 8 <= re_kh e) /\
  Forall (fun k => 14 <= Z.of_nat (length (gestures_end_b_c.key_text k))) (re_keys e).
(* W_contract.v:1014 asrc_at B ly S W mem HA h: the pending list's offset clause (W_rep.v:104-105) and its texts'
   non-emptiness (alist_at (HA + 16) (hs_pending h) false, W_rep.v:91) *)
Definition dr3_hpre (h : hsrc) : Prop :=
  ((hl_recs (hs_pending h) = [] /\ hs_off h = 0) \/
   (exists r rs, hl_recs (hs_pending h) = r :: rs /\ 0 <= hs_off h < Z.of_nat (length (snd r)))) /\
  Forall (fun r => (1 <= length (snd r))%nat) (hl_recs (hs_pending h)).
(* dr_post's clauses on the entry it leaves: :952 aentry_ok e' (W_rep.v:124), :957, :958, :959 *)
Definition dr3_epost (e e' : rentry) (h : hsrc) : Prop :=
  (re_cap e' = 0 \/ re_cap e' = 8192 \/ re_cap e' = 16384) /\
  ((re_hp e' = re_hp e /\ re_kh e' = re_kh e) \/ re_kh e' <= 2 ^ 30) /\
  NoDup (drain_b_c.keys_texts (re_keys e')) /\
  same_set (drain_b_c.keys_texts (re_keys e')) (upds (drain_b_c.keys_texts (re_keys e)) (dr_lines h)).
(* dr_post's clauses on the source it leaves: :966, :967, :964 *)
Definition dr3_hpost (h h' : hsrc) : Prop :=
  hl_recs (hs_pending h') = [] /\ hl_cap (hs_pending h') = hl_cap (hs_pending h) /\
  hl_cap (hs_expected h') <= Z.max 8 (Z.max (hl_cap (hs_expected h)) (2 * hl_n (hs_expected h'))).

(* ------------------------------------------------------------------ list helpers *)
Lemma dr3_zsum_nonneg : forall {X} (g : X -> Z) l, (forall x, 0 <= g x) -> 0 <= zsum (map g l).
Proof. intros X g l H. induction l as [|a l IH]; cbn [map fold_right]; [lia | specialize (H a); lia]. Qed.
Lemma dr3_sum_in : forall {X} (g : X -> Z) l q, (forall x, 0 <= g x) -> In q l -> g q <= zsum (map g l).
Proof.
  intros X g l q Hg Hq. induction l as [|x l IH]; [destruct Hq|]. cbn [map fold_right].
  pose proof (dr3_zsum_nonneg g l Hg). destruct Hq as [<-|Hq]; [lia|]. specialize (IH Hq). specialize (Hg x). lia.
Qed.
Lemma dr3_nodup_map_in : forall {X Y} (f : X -> Y) l a b, List.NoDup (map f l) -> In a l -> In b l -> f a = f b ->
  a = b.
Proof.
  intros X Y f l. induction l as [|x t IH]; intros a b ND Ha Hb E; [destruct Ha|]. cbn [map] in ND.
  apply NoDup_cons_iff in ND as [N1 N2].
  destruct Ha as [<-|Ha], Hb as [<-|Hb]; [reflexivity | | | exact (IH a b N2 Ha Hb E)].
  - exfalso. apply N1. rewrite E. apply in_map. exact Hb.
  - exfalso. apply N1. rewrite <- E. apply in_map. exact Ha.
Qed.
Lemma dr3_filter_len : forall {X} (f : X -> bool) l, (length (List.filter f l) <= length l)%nat.
Proof. intros X f l. induction l as [|x l IH]; cbn [List.filter length]; [lia|]. destruct (f x); cbn [length]; lia. Qed.

(* counts of a block at a point: every Permutation hypothesis and the goal, then linear arithmetic *)
Ltac dr3_cnt := repeat progress (rewrite ?count_occ_app, ?cnt_cons, ?cnt_nil in *).
Ltac dr3_perm :=
  repeat match goal with H : Permutation _ _ |- _ =>
    let H' := fresh "Hc" in pose proof (proj1 (Permutation_count_occ zzdec _ _) H) as H'; clear H end;
  apply (proj2 (Permutation_count_occ zzdec _ _)); let x := fresh "x" in intros x;
  repeat match goal with H : forall _ : Z * Z, count_occ _ _ _ = count_occ _ _ _ |- _ => specialize (H x) end;
  dr3_cnt; lia.

(* the drain arm's set_nth (dr_step's) *)
Lemma dr3_dset_len : forall {A} i (x : A) l, length (dset i x l) = length l.
Proof. intros A i. induction i as [|i IH]; intros x [|y l]; cbn; try reflexivity; rewrite IH; reflexivity. Qed.
Lemma dr3_dset_perm : forall {A} (f : A -> list (Z * Z)) i x y l, nth_error l i = Some y ->
  Permutation (concat (map f (dset i x l)) ++ f y) (concat (map f l) ++ f x).
Proof.
  intros A f i. induction i as [|i IH]; intros x y [|z l] H; cbn in H; try discriminate.
  - injection H as ->. cbn [W_LLVMFuzzerTestOneInput_drain.set_nth map concat]. dr3_perm.
  - cbn [W_LLVMFuzzerTestOneInput_drain.set_nth map concat]. rewrite <- !app_assoc. apply Permutation_app_head.
    exact (IH x y l H).
Qed.
Lemma dr3_dset_zsum : forall {A} (g : A -> Z) i x y l, nth_error l i = Some y ->
  zsum (map g (dset i x l)) + g y = zsum (map g l) + g x.
Proof.
  intros A g i. induction i as [|i IH]; intros x y [|z l] H; cbn in H; try discriminate.
  - injection H as ->. cbn. lia.
  - cbn. specialize (IH x y l H). lia.
Qed.

(* ------------------------------------------------------------------ the blocks' sizes *)
Definition dr3_vec (cap : Z) : Z := if cap =? 0 then 0 else AREC * cap.
Definition dr3_tsz (rs : list (Z * list byte)) : Z := zsum (map (fun r => Z.of_nat (length (snd r)) + 1) rs).
Definition dr3_ksz (ks : list (Z * list byte * list byte)) : Z :=
  zsum (map (fun k => Z.of_nat (length (gestures_end_b_c.key_text k)) + 1) ks).
Definition dr3_ce (e : rentry) : Z := if re_cap e =? 0 then 0 else re_cap e.
Definition dr3_ke (e : rentry) : Z := if re_hp e =? 0 then 0 else re_kh e.
Definition dr3_bo (cap : Z) : Z := if cap =? 0 then 0 else cap.

Lemma dr3_bsum_map : forall {X} (f : X -> Z * Z) l, bsum (map f l) = zsum (map (fun x => snd (f x)) l).
Proof. intros X f l. unfold bsum. induction l as [|x l IH]; cbn [map fold_right]; [reflexivity | rewrite IH; reflexivity]. Qed.
Lemma dr3_bsum_alist : forall l, bsum (alist_blks l) = dr3_vec (hl_cap l) + dr3_tsz (hl_recs l).
Proof.
  intros l. unfold alist_blks, dr3_vec, dr3_tsz. rewrite bsum_app, dr3_bsum_map.
  destruct (hl_cap l =? 0); cbn [bsum fold_right snd]; unfold bsum; cbn [fold_right snd]; lia.
Qed.
Lemma dr3_bsum_asrc : forall h, bsum (asrc_blks h) =
  APARTIAL + bsum (alist_blks (hs_pending h)) + bsum (alist_blks (hs_expected h)) + bsum (alist_blks (hs_held h)).
Proof. intros h. unfold asrc_blks. rewrite bsum_cons, !bsum_app. cbn [snd]. lia. Qed.
Lemma dr3_bsum_aentry : forall e, bsum (aentry_blks e) = dr3_ce e + dr3_ke e + dr3_ksz (re_keys e).
Proof.
  intros e. unfold aentry_blks, dr3_ce, dr3_ke, dr3_ksz. rewrite !bsum_app, dr3_bsum_map.
  destruct (re_cap e =? 0), (re_hp e =? 0); unfold bsum; cbn [fold_right snd]; lia.
Qed.
Lemma dr3_bsum_aout : forall cap out, bsum (aout_blks cap out) = dr3_bo cap.
Proof. intros cap out. unfold aout_blks, dr3_bo. destruct (cap =? 0); unfold bsum; cbn [fold_right snd]; lia. Qed.
Lemma dr3_tsz_nonneg : forall rs, 0 <= dr3_tsz rs.
Proof. intros rs. unfold dr3_tsz. apply dr3_zsum_nonneg. intros r. lia. Qed.
Lemma dr3_ksz_nonneg : forall ks, 0 <= dr3_ksz ks.
Proof. intros ks. unfold dr3_ksz. apply dr3_zsum_nonneg. intros k. lia. Qed.
Lemma dr3_ksz_le : forall ks, dr3_ksz ks <= SlotPass2Aux.p2_ksum (drain_b_c.keys_texts ks).
Proof.
  intros ks. unfold dr3_ksz, SlotPass2Aux.p2_ksum, drain_b_c.keys_texts.
  induction ks as [|k ks IH]; cbn [map fold_right]; [lia|]. rewrite SlotReads.bzs_length. lia.
Qed.

(* ------------------------------------------------------------------ the lines a drain relays *)
Lemma dr3_wn_in : forall Ls l, In l Ls -> Z.of_nat (length l) + 1 <= Z.of_nat (length (with_nul Ls)).
Proof.
  induction Ls as [|x Ls IH]; intros l H; [destruct H|]. rewrite RelayCap.with_nul_cons_len.
  destruct H as [<-|H]; [lia | specialize (IH l H); lia].
Qed.
Lemma dr3_wn_sum : forall Ls, Z.of_nat (length (with_nul Ls)) = zsum (map (fun l => Z.of_nat (length l) + 1) Ls).
Proof. induction Ls as [|l Ls IH]; [reflexivity|]. rewrite RelayCap.with_nul_cons_len, IH. cbn [map fold_right]. lia. Qed.
Lemma dr3_lines : forall h,
  (length (dr_lines h) <= length (pending_stream h))%nat /\
  Z.of_nat (length (with_nul (dr_lines h))) <=
    SlotReads.wcost (hs_state h) + Z.of_nat (length (pending_stream h)) /\
  Forall SlotReads.zrange (dr_lines h) /\ (21 * count_begin (dr_lines h) <= length (with_nul (dr_lines h)))%nat.
Proof.
  intros h. unfold dr_lines. split; [|split; [|split]].
  - pose proof (SlotDrain3Aux.lines_count (bzs (pending_stream h)) (hs_state h)) as L.
    rewrite SlotReads.bzs_length in L. exact L.
  - pose proof (SlotReads.lines_bytes (bzs (pending_stream h)) (hs_state h)) as L.
    pose proof (SlotReads.wcost_nonneg (feed (hs_state h) (bzs (pending_stream h)))).
    rewrite SlotReads.bzs_length in L. lia.
  - exact (proj1 (SlotReads.lines_range (bzs (pending_stream h)) (hs_state h)
                    (SlotReads.zrange_bzs (hs_W h)) (SlotReads.zrange_bzs (pending_stream h)))).
  - apply SlotReads.count_begin_bytes.
Qed.
(* the splitter's carried line is the relay's (fr_pair_ok's clause), so its cost is fr_pair_cost's third term *)
Lemma dr3_wcost : forall (e : rentry) h, re_skip e = hs_overlong h -> (re_skip e = 0 -> bzs (re_U e) = bzs (hs_W h)) ->
  (re_skip e = 0 \/ re_skip e = 1) ->
  SlotReads.wcost (hs_state h) = (if re_skip e =? 0 then Z.of_nat (length (re_U e)) else 0).
Proof.
  intros e h H1 H2 H3. unfold SlotReads.wcost, hs_state. cbn [ls_k ls_w]. rewrite <- H1.
  destruct H3 as [E|E].
  - rewrite <- (H2 E), E. cbn [Z.eqb]. rewrite SlotReads.bzs_length. reflexivity.
  - rewrite E. reflexivity.
Qed.

(* ------------------------------------------------------------------ the keys a drain can add *)
Definition dr3_bk (l : list Z) : list (list Z) := match gesture l with Some (GBegin, x) => [x] | _ => [] end.
Definition dr3_nk (Ls : list (list Z)) : list (list Z) := concat (map dr3_bk Ls).
Lemma dr3_gesture_sub : forall l k x, gesture l = Some (k, x) -> (length x <= length l)%nat.
Proof.
  intros l k x H. unfold gesture in H.
  destruct (list_eqb (firstn 13 l) K_GESTURE && Z.eqb (nth 13 l 0) SPACE && Nat.ltb 13 (length l)); [|discriminate].
  destruct (last_space_from 0 l) as [j|]; [|discriminate].
  destruct (Nat.ltb 13 j); [|discriminate].
  destruct (list_eqb (skipn (S j) l) W_BEGIN); [injection H as _ <-; rewrite length_firstn; lia|].
  destruct (list_eqb (skipn (S j) l) W_END); [injection H as _ <-; rewrite length_firstn; lia | discriminate].
Qed.
Lemma dr3_upd_in : forall G l y, In y (RelayModel.upd G l) -> In y G \/ In y (dr3_bk l).
Proof.
  intros G l y H. unfold RelayModel.upd, dr3_bk in *. destruct (gesture l) as [[[|] x]|].
  - apply upd_in_begin in H as [H|H]; [left; exact H | right; left; symmetry; exact H].
  - apply upd_in_end in H as [H _]. left. exact H.
  - left. exact H.
Qed.
Lemma dr3_upds_in : forall Ls G y, In y (RelayModel.upds G Ls) -> In y G \/ In y (dr3_nk Ls).
Proof.
  induction Ls as [|l Ls IH]; intros G y H; [left; exact H|].
  unfold RelayModel.upds in H. cbn [fold_left] in H.
  change (fold_left RelayModel.upd Ls (RelayModel.upd G l)) with (RelayModel.upds (RelayModel.upd G l) Ls) in H.
  unfold dr3_nk. cbn [map concat].
  destruct (IH _ _ H) as [H1|H1].
  - destruct (dr3_upd_in G l y H1) as [H2|H2]; [left; exact H2 | right; apply in_or_app; left; exact H2].
  - right. apply in_or_app. right. exact H1.
Qed.
Lemma dr3_p2_nk : forall Ls, SlotPass2Aux.p2_ksum (dr3_nk Ls) <= 5 * Z.of_nat (length (with_nul Ls)).
Proof.
  induction Ls as [|l Ls IH]; [unfold dr3_nk, SlotPass2Aux.p2_ksum; cbn; lia|].
  unfold dr3_nk in *. cbn [map concat]. rewrite SlotPass2Aux.p2_ksum_app, RelayCap.with_nul_cons_len.
  assert (Hb : dr3_bk l = match gesture l with Some (GBegin, x) => [x] | _ => [] end) by reflexivity.
  rewrite Hb. destruct (gesture l) as [[[|] x]|] eqn:G; cbv beta iota.
  - pose proof (dr3_gesture_sub l GBegin x G).
    assert (E : SlotPass2Aux.p2_ksum [x] = Z.of_nat (length x) + 5) by (unfold SlotPass2Aux.p2_ksum; cbn; lia).
    lia.
  - assert (E : SlotPass2Aux.p2_ksum [] = 0) by reflexivity. lia.
  - assert (E : SlotPass2Aux.p2_ksum [] = 0) by reflexivity. lia.
Qed.

(* ------------------------------------------------------------------ check_no_loss's room, replayed *)
Lemma dr3_tbytes_app : forall T x, tbytes (T ++ [x]) = tbytes T + Z.of_nat (length x) + 1.
Proof. intros T x. unfold tbytes. induction T as [|t T IH]; cbn [app fold_right]; lia. Qed.
Lemma dr3_tbytes_filter : forall f T, tbytes (List.filter f T) <= tbytes T.
Proof.
  intros f T. unfold tbytes. induction T as [|t T IH]; cbn [List.filter fold_right]; [lia|].
  destruct (f t); cbn [fold_right]; lia.
Qed.
Lemma dr3_upd_tbytes : forall T l, tbytes (RelayModel.upd T l) <= tbytes T + Z.of_nat (length l) + 1.
Proof.
  intros T l. unfold RelayModel.upd. destruct (gesture l) as [[[|] x]|] eqn:G.
  - destruct (existsb (list_eqb x) T); [lia|]. rewrite dr3_tbytes_app. pose proof (dr3_gesture_sub l GBegin x G). lia.
  - pose proof (dr3_tbytes_filter (fun y => negb (list_eqb x y)) T). lia.
  - lia.
Qed.
Lemma dr3_upd_len : forall T l,
  Z.of_nat (length (RelayModel.upd T l)) <= Z.of_nat (length T) + (if is_begin l then 1 else 0).
Proof.
  intros T l. unfold RelayModel.upd, is_begin. destruct (gesture l) as [[[|] x]|]; cbv beta iota.
  - destruct (existsb (list_eqb x) T); [lia|]. rewrite length_app. cbn [length]. lia.
  - pose proof (dr3_filter_len (fun y => negb (list_eqb x y)) T). lia.
  - lia.
Qed.
Lemma dr3_capstep_neg : forall T l cap, cap < 0 -> capstep T l cap = cap.
Proof.
  intros T l cap Hc. unfold capstep, ListRep.grow_cap.
  destruct (Nat.ltb _ _); [|reflexivity].
  destruct (Z.eqb_spec (Z.of_nat (length T)) cap); [lia | reflexivity].
Qed.
Lemma dr3_capstep_ge : forall T l cap, 0 <= cap -> cap <= capstep T l cap.
Proof.
  intros T l cap Hc. unfold capstep, ListRep.grow_cap.
  destruct (Nat.ltb _ _); [|lia].
  destruct (Z.eqb_spec (Z.of_nat (length T)) cap); [destruct (Z.eqb_spec cap 0); lia | lia].
Qed.
Lemma dr3_vec_min : forall T l cap,
  dr3_vec (capstep T l cap) - Z.max 0 (dr3_vec (capstep T l cap)) <= dr3_vec cap - Z.max 0 (dr3_vec cap).
Proof.
  intros T l cap. destruct (Z_lt_le_dec cap 0) as [Hc|Hc].
  - rewrite (dr3_capstep_neg T l cap Hc). lia.
  - pose proof (dr3_capstep_ge T l cap Hc) as Hg. unfold dr3_vec.
    destruct (capstep T l cap =? 0), (cap =? 0); unfold AREC; lia.
Qed.
Definition dr3_M (T : list (list Z)) (cap : Z) (rs : list (Z * list byte)) : Z :=
  Z.max 8 (Z.max cap (2 * (Z.of_nat (length T) + Z.of_nat (count_begin (map (fun r => bzs (snd r)) rs))))).
Lemma dr3_room : forall MX rs T cap bb Mx L,
  dr3_M T cap rs <= Mx -> 32 * Mx < MX ->
  (forall r, In r rs -> Z.of_nat (length (snd r)) + 1 <= L) ->
  bb - Z.max 0 (dr3_vec cap) + 48 * Mx + L <= LIVE_MAX ->
  cnl_room MX bb T cap rs.
Proof.
  intros MX rs. induction rs as [|r rs IH]; intros T cap bb Mx L HM HX HL HB; [exact I|].
  cbn [cnl_room].
  pose proof (HL r (or_introl eq_refl)) as Hr.
  set (l := bzs (snd r)) in *.
  assert (Hl : Z.of_nat (length l) = Z.of_nat (length (snd r))) by (unfold l; rewrite SlotReads.bzs_length; reflexivity).
  set (cb := Z.of_nat (count_begin (map (fun r => bzs (snd r)) rs))) in *.
  assert (Ecb : cb = Z.of_nat (count_begin (map (fun r => bzs (snd r)) rs))) by reflexivity.
  assert (Hbeg : Z.of_nat (count_begin (map (fun r => bzs (snd r)) (r :: rs))) = (if is_begin l then 1 else 0) + cb).
  { cbn [map]. fold l. rewrite SlotReads.count_begin_cons. rewrite Ecb. destruct (is_begin l); lia. }
  assert (Hb01 : 0 <= (if is_begin l then 1 else 0) <= 1) by (destruct (is_begin l); lia).
  unfold dr3_M in HM. rewrite Hbeg in HM.
  set (n := Z.of_nat (length T)) in *.
  assert (En : n = Z.of_nat (length T)) by reflexivity.
  assert (Hn0 : 0 <= n) by (rewrite En; lia).
  assert (Hv : Z.max 0 (dr3_vec cap) <= 16 * Mx) by (unfold dr3_vec, AREC; destruct (cap =? 0); lia).
  assert (Hgr : n = cap -> AREC * ListRep.grow_cap n cap <= 32 * Mx).
  { intros E. unfold ListRep.grow_cap. rewrite E, Z.eqb_refl. unfold AREC. destruct (cap =? 0); lia. }
  split; [|split].
  - intros E. specialize (Hgr E). lia.
  - destruct (Z.eqb_spec n cap) as [E|E]; [specialize (Hgr E)|]; lia.
  - pose proof (dr3_upd_len T l) as Hul. pose proof (dr3_upd_tbytes T l) as Hut.
    pose proof (dr3_vec_min T l cap) as Hvm.
    apply (IH _ _ _ Mx L).
    + unfold dr3_M. rewrite <- Ecb.
      assert (Hc' : capstep T l cap <= Mx).
      { unfold capstep, ListRep.grow_cap.
        destruct (Nat.ltb_spec (length T) (length (RelayModel.upd T l))) as [Lt|Ge]; [|lia].
        destruct (Z.eqb_spec (Z.of_nat (length T)) cap) as [E|E]; [|lia].
        destruct (Z.eqb_spec cap 0); lia. }
      lia.
    + exact HX.
    + intros r' Hr'. exact (HL r' (or_intror Hr')).
    + assert (E1 : hbytes T cap = dr3_vec cap + tbytes T) by reflexivity.
      assert (E2 : hbytes (RelayModel.upd T l) (capstep T l cap) =
                   dr3_vec (capstep T l cap) + tbytes (RelayModel.upd T l)) by reflexivity.
      rewrite E1, E2. lia.
Qed.

Section drain3.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : asyms.
(* ------------------------------------------------------------------ the drained pair, read off fr_RINV *)
Lemma dr3_rinv : forall cx t m si h j, fr_RINV cx t m -> dr_pick cx m si h -> (j < length (lm_es m))%nat ->
  re_fd (nth j (lm_es m) dr_e0) = hs_fd h -> re_eof (nth j (lm_es m) dr_e0) = 0 ->
  (re_skip (nth j (lm_es m) dr_e0) = hs_overlong h /\
   (re_skip (nth j (lm_es m) dr_e0) = 0 -> bzs (re_U (nth j (lm_es m) dr_e0)) = bzs (hs_W h))) /\
  (re_skip (nth j (lm_es m) dr_e0) = 0 \/ re_skip (nth j (lm_es m) dr_e0) = 1) /\
  same_set (drain_b_c.keys_texts (re_keys (nth j (lm_es m) dr_e0))) (texts (hs_held h)) /\
  NoDup (texts (hs_held h)) /\ hl_recs (hs_expected h) = [] /\
  SlotInv.ecap_ok (hl_cap (hs_expected h)) /\ hl_cap (hs_held h) < 2 ^ 24 /\
  Z.of_nat (length (pending_stream h)) <= SlotInv.WRITE_MAX * t /\ 0 <= hs_off h /\
  fr_pair_cost (nth j (lm_es m) dr_e0) (h, si) < 2 ^ 26.
Proof.
  intros cx t m si h j HRI (_ & Hsi & Hh) Hj Hfd Heof.
  destruct HRI as (_ & HR & Hn & _).
  destruct HR as (_ & Hnd & _ & Hent & hj & HF & _ & Hcl & _ & Hcn).
  destruct (fr_pair_of_open m t hj si h HF Hcl Hsi Hh) as (e1 & p & Hin & Hok & Hp2 & Hp1).
  destruct p as [h0 s0]. cbn [fst snd] in Hp1, Hp2. subst h0 s0.
  unfold fr_pair_ok in Hok. cbv zeta in Hok. cbn [fst snd] in Hok.
  destruct Hok as (_ & _ & Hfd1 & Hrs & Hss & Hnd2 & Hexp & Hec & Hhc & Hpw & Hoff).
  assert (He1 : e1 = nth j (lm_es m) dr_e0).
  { apply NoDup_ListNoDup in Hnd. apply (dr3_nodup_map_in re_fd (lm_es m) e1 _ Hnd).
    - exact (in_combine_l _ _ _ _ Hin).
    - apply nth_In. exact Hj.
    - lia. }
  subst e1.
  assert (Hsk : re_skip (nth j (lm_es m) dr_e0) = 0 \/ re_skip (nth j (lm_es m) dr_e0) = 1).
  { rewrite Forall_forall in Hent. destruct (Hent _ (nth_In _ dr_e0 Hj)) as (_ & _ & _ & _ & Hs). exact Hs. }
  assert (Hc : fr_pair_cost (nth j (lm_es m) dr_e0) (h, si) <= fr_cost (lm_es m) hj).
  { unfold fr_cost. apply (dr3_sum_in (fun q => fr_pair_cost (fst q) (snd q)) _ (nth j (lm_es m) dr_e0, (h, si))).
    - intros q. apply fr_pair_cost_nonneg.
    - exact Hin. }
  refine (conj (Hrs Heof) (conj Hsk (conj Hss (conj Hnd2 (conj Hexp (conj Hec (conj Hhc (conj Hpw (conj Hoff _))))))))).
  lia.
Qed.

(* the held texts are the entry's keys, each once *)
Lemma dr3_held_len : forall ks (H : hlist), NoDup (texts H) -> same_set (drain_b_c.keys_texts ks) (texts H) ->
  (length (texts H) <= length ks)%nat.
Proof.
  intros ks H ND S. apply NoDup_ListNoDup in ND.
  replace (length ks) with (length (drain_b_c.keys_texts ks)) by (unfold drain_b_c.keys_texts; apply length_map).
  apply NoDup_incl_length; [exact ND|]. intros y Hy. apply S. exact Hy.
Qed.

(* ------------------------------------------------------------------ the output buffer after the drain *)
Lemma dr3_J1 : forall (e : rentry) h, re_skip e = hs_overlong h -> (re_skip e = 0 -> bzs (re_U e) = bzs (hs_W h)) ->
  (re_skip e = 0 \/ re_skip e = 1) -> Z.of_nat (length (re_U e)) <= APARTIAL -> ~ In (Z_to_bv 8 0) (re_U e) ->
  J1 (bzs (re_U e)) (re_skip e =? 1) (hs_state h).
Proof.
  intros e h H1 H2 H3 H4 H5. unfold J1, hs_state. cbn [ls_k ls_w]. rewrite <- H1.
  split; [reflexivity|]. split; [|split].
  - intros Hf. destruct H3 as [E|E]; [exact (H2 E) | rewrite E in Hf; cbn in Hf; discriminate].
  - rewrite SlotReads.bzs_length. apply Nat2Z.inj_le.
    assert (E6 : Z.of_nat LINE_LIMIT = 6000) by reflexivity. rewrite E6. unfold APARTIAL in H4. exact H4.
  - unfold nozero, bzs. apply Forall_map. apply Forall_forall. intros b Hb Hz. apply H5.
    assert (E : bzs [b] = bzs [Z_to_bv 8 0]) by (rewrite SlotReads.bzs_zero; unfold bzs; cbn [map]; rewrite Hz; reflexivity).
    apply SlotReads.bzs_inj in E. injection E as <-. exact Hb.
Qed.
Lemma dr3_pok : forall NO CAP e h, 0 <= hs_off h -> dr3_hpre h ->
  relay_remove_b_aux.rma_pok (drain_b_c.drain_init NO CAP e h).
Proof.
  intros NO CAP e h Ho (Hs & Hne). unfold relay_remove_b_aux.rma_pok, drain_b_c.drain_init.
  cbn [drain_b_c.ds_off drain_b_c.ds_pend]. split; [exact Ho|].
  destruct Hs as [(E & _) | (r & rs & E & Hr)]; rewrite E; cbn [map]; [exact I|].
  rewrite E in Hne. inversion Hne as [|? ? _ Hne']; subst. split.
  - rewrite SlotReads.bzs_length. lia.
  - apply Forall_map. eapply Forall_impl; [|exact Hne']. intros x Hx. cbv beta. rewrite SlotReads.bzs_length. exact Hx.
Qed.
Lemma dr3_ocap : forall c mx cap (e : rentry) h,
  J1 (bzs (re_U e)) (re_skip e =? 1) (hs_state h) -> relay_remove_b_aux.rma_pok (drain_b_c.drain_init 0 cap e h) ->
  (re_cap e = 0 \/ 8192 <= re_cap e) ->
  drain_b_c.ds_ocap (dr_fin c mx 0 cap e h) <= Z.max cap (2 * Z.of_nat (length (with_nul (dr_lines h)))).
Proof.
  intros c mx cap e h HJ HP HC. unfold dr_fin, dr_lines.
  pose proof (RelayCap.drain_ocap_le (dr_live c h) mx 0 cap e h) as (_ & H).
  rewrite (relay_remove_b_aux.rma_fin_no (dr_live c h) mx 0 cap e h HJ HP HC) in H. lia.
Qed.


(* what fr_LS leaves of LIVE_MAX at any cut point, with the potential's credits counted (fr_LS_room's 2 ^ 31 is the
   round figure) *)
Lemma dr3_room_S : forall cx t m ly S, fr_LS B cx t m ly S -> blocks_bytes S + 4160725633 <= LIVE_MAX.
Proof.
  intros cx t m ly S (rest & e0 & HP & HR & HE & Hc & Hl & Hnp & HM).
  rewrite (blocks_bytes_bsum B ly S), (bsum_perm _ _ HP), !bsum_app.
  pose proof (PHI_ge m). pose proof (nopen_le4 _ Hl).
  assert (Hk : kk cx m <= c_n cx) by (unfold kk; lia).
  assert (HC : ACfn_cf.CALL_ROOM = 8589934592) by reflexivity.
  unfold MB_K, MB_C, APARTIAL in *. lia.
Qed.

(* ================================================================== LS_cnl_pre *)
(* 129f255c729 _drain.v:743 LS_cnl_pre, AT THE PROPOSED TEXT: the published premises, then (1) the arm's operation
   bound and empty stream, (2) dr_spec's model clauses at the call, (3) dr_post's blocks' change and the cap' it names,
   (4) dr_post's clauses on the entry and source it leaves.  The published conclusion. *)
Lemma fr_LS_cnl_pre_p : forall cx t m ly S (ly' : alayout) (S' : astate) si h j h'' e' cap' out',
  fr_LS B cx t m ly S -> fr_RINV cx t m -> dr_pick cx m si h ->
  (j < length (lm_es m))%nat -> re_fd (nth j (lm_es m) dr_e0) = hs_fd h ->
  re_eof (nth j (lm_es m) dr_e0) = 0 ->
  mo_le MT S S' (dr_cost MT (lm_c m) (lm_mx m) (Z.of_nat (length (lm_O m))) (lm_cap m)
                   (nth j (lm_es m) dr_e0) h) ->
  hl_cap (hs_expected h'') = drain_b_c.ds_ecap
    (dr_fin (lm_c m) (lm_mx m) (Z.of_nat (length (lm_O m))) (lm_cap m) (nth j (lm_es m) dr_e0) h) ->
  map snd (hl_recs (hs_expected h'')) =
    map snd (hl_recs (hs_expected h)) ++ map (map (Z_to_bv 8)) (dr_lines h) ->
  hs_held h'' = hs_held h ->
  (* (1) lregs_base (DLK's Ht, drain.v:5414); dr_at_op (Hatop, drain.v:5413) *)
  0 <= t < OPS_MAX -> lm_O m = [] ->
  (* (2) W_contract.v:1013 aentry_ok e, :984 asrc_at h, :986 aout_at (W_rep.v:177-178, the cap clause) *)
  dr3_epre (nth j (lm_es m) dr_e0) -> dr3_hpre h -> 0 <= lm_cap m ->
  (* (3) dr_post :949-950, :943 *)
  (exists rest,
     Permutation (ablocks B ly S)
       (aentry_blks (nth j (lm_es m) dr_e0) ++ asrc_blks h ++ aout_blks (lm_cap m) (lm_out m) ++ rest) /\
     Permutation (ablocks B ly' S') (aentry_blks e' ++ asrc_blks h'' ++ aout_blks cap' out' ++ rest)) ->
  cap' = (if dr_live (lm_c m) h
          then drain_b_c.ds_ocap (dr_fin (lm_c m) (lm_mx m) (Z.of_nat (length (lm_O m))) (lm_cap m)
                                   (nth j (lm_es m) dr_e0) h)
          else lm_cap m) ->
  (* (4) dr_post :952 (aentry_ok e'), :957, :958, :959; :966, :967, :964 *)
  dr3_epost (nth j (lm_es m) dr_e0) e' h -> dr3_hpost h h'' ->
  NoDup (texts (hs_held h'')) /\ hl_n (hs_expected h'') < 2 ^ 26 /\
  hl_n (hs_held h'') + Z.of_nat (count_begin (texts (hs_expected h''))) < 2 ^ 22 /\
  cnl_room MMAX (blocks_bytes S') (texts (hs_held h'')) (hl_cap (hs_held h'')) (hl_recs (hs_expected h'')) /\
  mo_ok MT S' (cnl_cost MT (hs_expected h'') (hs_held h'')) /\
  AREC * capb (hs_held h'') (hs_expected h'') < 2 ^ 32.
Proof.
  intros cx t m ly S ly' S' si h j h'' e' cap' out' HLS HRI Hpick Hj Hfd Heof _ _ Hmap Hheld Ht HO
    Hepre Hhpre Hcap0 (rest & HP1 & HP2) Hcap' Hepost Hhpost.
  pose proof (dr3_room_S cx t m ly S HLS) as Hroom.
  destruct (dr3_rinv cx t m si h j HRI Hpick Hj Hfd Heof)
    as ((Hsk & HskU) & Hsk01 & Hss & Hnd & Hexp & Hec & Hhc & Hpw & Hoff & Hcost).
  set (e := nth j (lm_es m) dr_e0) in *.
  set (Ls := dr_lines h) in *.
  destruct Hepre as (Hce & HU & HUz & Hkh & H14).
  destruct Hepost as (Hce' & Hkh' & Hnd' & Hss').
  destruct Hhpost as (Hpd'' & Hpc'' & Hec'').
  pose proof (dr3_lines h) as (HLn & HTOT & HZr & HCB). fold Ls in HLn, HTOT, HZr, HCB.
  pose proof (dr3_wcost e h Hsk HskU Hsk01) as HW.
  unfold SlotInv.WRITE_MAX in Hpw.
  set (P := Z.of_nat (length (pending_stream h))) in *.
  assert (EP : P = Z.of_nat (length (pending_stream h))) by reflexivity.
  set (TOT := Z.of_nat (length (with_nul Ls))) in *.
  assert (ETOT : TOT = Z.of_nat (length (with_nul Ls))) by reflexivity.
  set (K := gestures_end_b_c.keys_total (re_keys e)) in *.
  assert (HUW : Z.of_nat (length (re_U e)) <= 6000) by (unfold APARTIAL in HU; exact HU).
  assert (Hpc : fr_pair_cost e (h, si) = K + P + (if re_skip e =? 0 then Z.of_nat (length (re_U e)) else 0))
    by reflexivity.
  assert (HK0 : 0 <= K) by (unfold K; apply SlotReads.keys_total_nonneg).
  assert (HWr : 0 <= (if re_skip e =? 0 then Z.of_nat (length (re_U e)) else 0) <= 6000)
    by (destruct (re_skip e =? 0); lia).
  assert (HOM : OPS_MAX = 512) by reflexivity.
  (* the expected list after the drain holds exactly the lines *)
  assert (HT : texts (hs_expected h'') = Ls).
  { unfold texts. rewrite <- (map_map snd bzs). rewrite Hmap, Hexp. cbn [map app]. exact (fr_bzs_lines _ HZr). }
  assert (HnE : hl_n (hs_expected h'') = Z.of_nat (length Ls)).
  { unfold hl_n. rewrite <- (length_map snd (hl_recs (hs_expected h''))), Hmap, Hexp. cbn [map app].
    rewrite length_map. reflexivity. }
  (* the held count and the begins *)
  pose proof (dr3_held_len (re_keys e) (hs_held h) Hnd Hss) as HHL.
  pose proof (SlotReads.keys_total_count (re_keys e) H14) as HKC. fold K in HKC.
  assert (HnH : hl_n (hs_held h) = Z.of_nat (length (texts (hs_held h))))
    by (unfold hl_n, texts; rewrite length_map; reflexivity).
  assert (N3 : hl_n (hs_held h'') + Z.of_nat (count_begin (texts (hs_expected h''))) < 2 ^ 22).
  { rewrite Hheld, HT, HnH. lia. }
  assert (N2 : hl_n (hs_expected h'') < 2 ^ 26) by (rewrite HnE; lia).
  set (Mx := capb (hs_held h) (hs_expected h'')).
  assert (HMx : Mx < 2 ^ 24) by (unfold Mx, capb; pose proof N3 as N3'; rewrite Hheld in N3'; lia).
  refine (conj _ (conj N2 (conj N3 (conj _ (conj I _))))).
  - rewrite Hheld. exact Hnd.
  - (* the room: blocks_bytes S' against blocks_bytes S *)
    rewrite Hheld.
    assert (HB1 : blocks_bytes S = bsum (aentry_blks e) + bsum (asrc_blks h) + bsum (aout_blks (lm_cap m) (lm_out m)) +
                                   bsum rest)
      by (rewrite (blocks_bytes_bsum B ly S), (bsum_perm _ _ HP1), !bsum_app; lia).
    assert (HB2 : blocks_bytes S' = bsum (aentry_blks e') + bsum (asrc_blks h'') + bsum (aout_blks cap' out') +
                                    bsum rest)
      by (rewrite (blocks_bytes_bsum B ly' S'), (bsum_perm _ _ HP2), !bsum_app; lia).
    rewrite !dr3_bsum_aentry, !dr3_bsum_asrc, !dr3_bsum_aout, !dr3_bsum_alist in HB1, HB2.
    rewrite Hheld in HB2.
    (* the relay's buffer and held array *)
    assert (Da : dr3_ce e' <= 16384 /\ 0 <= dr3_ce e) by (unfold dr3_ce; destruct (re_cap e' =? 0), (re_cap e =? 0); lia).
    assert (Db : dr3_ke e' - dr3_ke e <= 2 ^ 30).
    { unfold dr3_ke. destruct Hkh' as [(E1 & E2) | Hk]; [rewrite E1, E2; lia|].
      destruct (Z.eqb_spec (re_hp e') 0), (Z.eqb_spec (re_hp e) 0); try lia;
        specialize (Hkh ltac:(assumption)); lia. }
    (* the relay's keys *)
    assert (Dc : dr3_ksz (re_keys e') <= K + 5 * TOT).
    { pose proof (dr3_ksz_le (re_keys e')) as X1.
      pose proof (SlotPass2Aux.p2_ksum_incl (drain_b_c.keys_texts (re_keys e'))
                    (drain_b_c.keys_texts (re_keys e) ++ dr3_nk Ls)) as X2.
      rewrite SlotPass2Aux.p2_ksum_app in X2.
      assert (X3 : K = SlotPass2Aux.p2_ksum (drain_b_c.keys_texts (re_keys e)))
        by (unfold K, SlotPass2Aux.p2_ksum; apply RelayCap.keys_total_texts).
      pose proof (dr3_p2_nk Ls) as X4. fold TOT in X4.
      assert (X5 : SlotPass2Aux.p2_ksum (drain_b_c.keys_texts (re_keys e')) <=
                   SlotPass2Aux.p2_ksum (drain_b_c.keys_texts (re_keys e)) + SlotPass2Aux.p2_ksum (dr3_nk Ls)).
      { apply X2; [apply NoDup_ListNoDup; exact Hnd'|]. intros y Hy. apply in_or_app.
        destruct (dr3_upds_in Ls _ y (proj1 (Hss' y) Hy)) as [Hy'|Hy']; [left | right]; exact Hy'. }
      lia. }
    pose proof (dr3_ksz_nonneg (re_keys e)) as Dc0.
    (* the pending list: its texts are freed, its vector kept *)
    assert (Dd : dr3_vec (hl_cap (hs_pending h'')) + dr3_tsz (hl_recs (hs_pending h'')) <=
                 dr3_vec (hl_cap (hs_pending h)) + dr3_tsz (hl_recs (hs_pending h))).
    { rewrite Hpc'', Hpd''. pose proof (dr3_tsz_nonneg (hl_recs (hs_pending h))).
      assert (E0 : dr3_tsz [] = 0) by reflexivity. rewrite E0. lia. }
    (* the expected list: the lines' texts, the vector's growth *)
    assert (De1 : dr3_tsz (hl_recs (hs_expected h'')) = TOT).
    { assert (X : map (fun r : Z * list byte => Z.of_nat (length (snd r)) + 1) (hl_recs (hs_expected h'')) =
                  map (fun x => Z.of_nat (length x) + 1) (map snd (hl_recs (hs_expected h''))))
        by (rewrite map_map; reflexivity).
      unfold dr3_tsz. rewrite X, Hmap, Hexp. cbn [map app]. rewrite map_map, ETOT, dr3_wn_sum. f_equal.
      apply map_ext. intros x. rewrite length_map. reflexivity. }
    assert (De2 : dr3_tsz (hl_recs (hs_expected h)) = 0) by (rewrite Hexp; reflexivity).
    pose proof (SlotInv.ecap_ok_lt _ Hec) as Hec0.
    assert (De3 : dr3_vec (hl_cap (hs_expected h'')) - dr3_vec (hl_cap (hs_expected h)) <=
                  AREC * Z.max 8 (2 * Z.of_nat (length Ls))).
    { rewrite HnE in Hec''. unfold dr3_vec, AREC.
      destruct (Z.eqb_spec (hl_cap (hs_expected h'')) 0), (Z.eqb_spec (hl_cap (hs_expected h)) 0); lia. }
    (* the output buffer *)
    assert (Dg : dr3_bo cap' - dr3_bo (lm_cap m) <= 2 * TOT).
    { replace (Z.of_nat (length (lm_O m))) with 0 in Hcap' by (rewrite HO; reflexivity).
      assert (HJ : J1 (bzs (re_U e)) (re_skip e =? 1) (hs_state h)) by exact (dr3_J1 e h Hsk HskU Hsk01 HU HUz).
      pose proof (dr3_ocap (lm_c m) (lm_mx m) (lm_cap m) e h HJ (dr3_pok 0 (lm_cap m) e h Hoff Hhpre)
                    ltac:(lia)) as Ho. fold Ls TOT in Ho.
      unfold dr3_bo. rewrite Hcap'. destruct (dr_live (lm_c m) h); cbv beta iota.
      - destruct (Z.eqb_spec (drain_b_c.ds_ocap (dr_fin (lm_c m) (lm_mx m) 0 (lm_cap m) e h)) 0),
          (Z.eqb_spec (lm_cap m) 0); lia.
      - lia. }
    (* the room check_no_loss needs *)
    apply (dr3_room MMAX _ _ _ _ Mx TOT).
    + unfold dr3_M. change (map (fun r => bzs (snd r)) (hl_recs (hs_expected h''))) with (texts (hs_expected h'')).
      unfold Mx, capb. rewrite HnH. lia.
    + assert (HW' : WR_MMAX = 1072693248) by reflexivity. lia.
    + intros r Hr. assert (Hs : In (snd r) (map (map (Z_to_bv 8)) Ls)).
      { replace (map (map (Z_to_bv 8)) Ls) with (map snd (hl_recs (hs_expected h'')))
          by (rewrite Hmap, Hexp; reflexivity).
        apply in_map. exact Hr. }
      apply in_map_iff in Hs as (l & El & Hl). rewrite <- El, length_map. exact (dr3_wn_in Ls l Hl).
    + assert (Hv0 : 0 <= Z.max 0 (dr3_vec (hl_cap (hs_held h)))) by lia.
      assert (HnL : Z.of_nat (length Ls) <= P) by (rewrite EP; lia).
      assert (HTOT' : TOT <= 6000 + P) by (rewrite HW in HTOT; lia).
      assert (HK26 : K < 2 ^ 26) by lia.
      assert (HP25 : P <= 65535 * 511) by lia.
      assert (Hd : blocks_bytes S' <= blocks_bytes S + 16384 + 2 ^ 30 + K + 8 * TOT +
                                     AREC * Z.max 8 (2 * Z.of_nat (length Ls))) by lia.
      clear - Hd Hroom HMx Hv0 HnL HTOT' HK26 HP25 HK0.
      unfold AREC in *. lia.
  - unfold capb. rewrite Hheld. rewrite Hheld in N3. unfold AREC. lia.
Qed.

(* ================================================================== LS_drain_step *)
(* the potential's step: what fr_LS v2 needs of a drain and does not get (the report's quantity) *)
Definition dr3_pays (cx : lfcx) (m m' : lmod) : Prop := PHI m' <= PHI m + MB_K * (kk cx m' - kk cx m).

(* 129f255c729 _drain.v:765 LS_drain_step, AT THE PROPOSED TEXT: the published premises, then dr_post's blocks' change
   (:949-950) and pending list (:966), check_no_loss's blocks' change (drain.v cnl_post :238-239) at the lists it was
   called with, the arm's h'' = set_exp_held h1 E' H' (drain.v:5471), and the ONE named extra hypothesis Hpay. *)
Lemma fr_LS_drain_step_p : forall cx t m ly S (S1 : astate) (ly' : alayout) (S' : astate)
    si h j h'' e' c' O' cap' out' (E H : hlist) (ly1 : alayout) (h1 : hsrc) (E' H' : hlist),
  fr_LS B cx t m ly S -> dr_pick cx m si h -> (j < length (lm_es m))%nat ->
  mo_le MT S S1
    (dr_cost MT (lm_c m) (lm_mx m) (Z.of_nat (length (lm_O m))) (lm_cap m) (nth j (lm_es m) dr_e0) h) ->
  mo_le MT S1 S' (cnl_cost MT E H) ->
  (* dr_post :949-950, :966 *)
  (exists rest,
     Permutation (ablocks B ly S)
       (aentry_blks (nth j (lm_es m) dr_e0) ++ asrc_blks h ++ aout_blks (lm_cap m) (lm_out m) ++ rest) /\
     Permutation (ablocks B ly1 S1) (aentry_blks e' ++ asrc_blks h1 ++ aout_blks cap' out' ++ rest)) ->
  hl_recs (hs_pending h1) = [] ->
  (* the arm calls check_no_loss on the drained source's lists (drain.v:5472) and cnl_post :238-239 *)
  E = hs_expected h1 -> H = hs_held h1 ->
  (forall rest, Permutation (ablocks B ly1 S1) (list_blks E ++ list_blks H ++ rest) ->
     Permutation (ablocks B ly' S') (list_blks E' ++ list_blks H' ++ rest)) ->
  h'' = set_exp_held h1 E' H' ->
  (* the named extra hypothesis: the drain's potential step is paid by the input it consumes *)
  forall Hpay : dr3_pays cx m (dr_step m (dr_k' cx m) si h'' j e' c' O' cap' out'),
  fr_LS B cx (t + 1) (dr_step m (dr_k' cx m) si h'' j e' c' O' cap' out') ly' S'.
Proof.
  intros cx t m ly S S1 ly' S' si h j h'' e' c' O' cap' out' E H ly1 h1 E' H' HLS (_ & Hsi & Hh) Hj _ _
    (rest_d & HPd1 & HPd2) Hpend HEq HHq Hcnl Hh'' Hpay.
  subst E H h''.
  destruct HLS as (rest & e0 & HP & HR & HE & Hc & Hl & Hnp & HM).
  set (e := nth j (lm_es m) dr_e0) in *.
  set (h'' := set_exp_held h1 E' H') in *.
  set (m' := dr_step m (dr_k' cx m) si h'' j e' c' O' cap' out') in *.
  assert (Hej : nth_error (lm_es m) j = Some e) by (unfold e; apply nth_error_nth'; exact Hj).
  pose proof (nth_some_error _ _ _ Hh) as Hhi.
  assert (LB : forall l, list_blks l = alist_blks l) by reflexivity.
  assert (Ha1 : asrc_blks h1 = (hs_partial h1, APARTIAL) :: alist_blks (hs_pending h1) ++
                               alist_blks (hs_expected h1) ++ alist_blks (hs_held h1)) by reflexivity.
  assert (Ha'' : asrc_blks h'' = (hs_partial h1, APARTIAL) :: alist_blks (hs_pending h1) ++
                                 alist_blks E' ++ alist_blks H') by reflexivity.
  (* check_no_loss's frame at the drain's post-state *)
  pose proof (Hcnl ((hs_partial h1, APARTIAL) :: alist_blks (hs_pending h1) ++ aentry_blks e' ++
                    aout_blks cap' out' ++ rest_d)) as HP3.
  rewrite !LB in HP3.
  assert (HP2' : Permutation (ablocks B ly1 S1) (alist_blks (hs_expected h1) ++ alist_blks (hs_held h1) ++
                   (hs_partial h1, APARTIAL) :: alist_blks (hs_pending h1) ++ aentry_blks e' ++ aout_blks cap' out' ++
                   rest_d)).
  { rewrite Ha1 in HPd2. clear - HPd2. dr3_perm. }
  specialize (HP3 HP2'). clear HP2' Hcnl.
  (* the model's blocks: the drained entry and slot against the rest *)
  pose proof (dr3_dset_perm aentry_blks j e' e (lm_es m) Hej) as PA.
  pose proof (dr3_dset_perm slot_blks si (Some h'') (Some h) (lm_hs m) Hhi) as PS.
  change (slot_blks (Some h'')) with (asrc_blks h'') in PS. change (slot_blks (Some h)) with (asrc_blks h) in PS.
  rewrite Ha'' in PS.
  assert (Hlen' : length (lm_hs m') = 4%nat) by (unfold m'; cbn [dr_step lm_hs]; rewrite dr3_dset_len; exact Hl).
  assert (Hk' : kk cx m <= kk cx m').
  { unfold kk, m'. cbn [dr_step lm_k]. unfold dr_k'. destruct (lm_k m + 1 <? c_n cx); lia. }
  assert (Hnp' : npend m' <= npend m).
  { unfold npend, m'. cbn [dr_step lm_hs].
    pose proof (dr3_dset_zsum slot_npend si (Some h'') (Some h) (lm_hs m) Hhi) as Z1.
    cbn [slot_npend] in Z1.
    assert (E0 : hl_n (hs_pending h'') = 0)
      by (unfold h''; cbn [set_exp_held hs_pending]; unfold hl_n; rewrite Hpend; reflexivity).
    assert (E1 : 0 <= hl_n (hs_pending h)) by (unfold hl_n; lia).
    lia. }
  assert (Hno' : nopen (lm_hs m') = nopen (lm_hs m)).
  { unfold m'. cbn [dr_step lm_hs]. apply (fr_nopen_dset (lm_hs m) si h'' h Hh). lia. }
  exists rest, e0.
  split; [| split; [exact HR | split; [exact HE | split; [exact Hc | split; [exact Hlen' | split]]]]].
  - unfold model_blks in HP |- *. unfold m'. cbn [dr_step lm_G lm_es lm_hs lm_cap lm_out].
    change (list_blks E') with (alist_blks E') in HP3. change (list_blks H') with (alist_blks H') in HP3.
    clear - HP HPd1 HP3 PA PS. dr3_perm.
  - lia.
  - unfold dr3_pays in Hpay. rewrite Hno'. unfold MB_K in *. lia.
Qed.
End drain3.
