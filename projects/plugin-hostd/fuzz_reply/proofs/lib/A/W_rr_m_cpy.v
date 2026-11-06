(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: hop 4 (CPY) of the MATCH segment of the ASan walk of fuzz_reply's relay_remove
   (lib/A/W_rr_match_cx.v hop_cpy_stmt): RRC i 0x83f98 -> RRU (Some i) 0x83fc4.
   rule 24: proves function relay_remove MATCH hop 4 (kind: segment lemma of the W6 walk, PORTED from 2ad36763b22
   relay_remove_p_c_tail.v rrA_tail_proved / rrt_block_cpy, relay_remove_seg.v rrA_cpy; lookup + CONFIRM in context).

   Where each part comes from (the retired lane form, commit 2ad36763b22, lib/A/Prog/... and lib/Prog/...):
   - rmc_firstn_app, rmc_skipn_app_S, rmc_remove_at_last, rmc_remove_at_mid, rmc_split_nth: P/relay_remove_b_aux.v
     rma_firstn_app / rma_skipn_app_S / rma_remove_at_last / rma_remove_at_mid / rma_split_nth, verbatim;
     rmc_skipn_app_exact: Lib/Cells.v skipn_app_exact, verbatim.
   - rmc_upd, rmc_nth_last, rmc_cmap_*, rmc_concat_cpy, rmc_concat_len, rmc_forall_firstn / _skipn, rmc_nth_skipn,
     rmc_slot_k, rmc_block_cpy: relay_remove_p_c_tail.v rrt_upd / rrt_nth_last / cmap_* / rrt_concat_cpy /
     rrt_concat_len / rrt_forall_firstn / _skipn / rrt_nth_skipn / rrt_slot_k / rrt_block_cpy (Part 1 and Part 3),
     ported over W6's remove_at and no_entry (the table's Tpre / Tpost as rmc_Tpre / rmc_Tpost).
   - the live blocks' NoDup: W_gestures_end.v gse_nodup (Section ark), cited.  rmc_bzs_len, rmc_text_rec_len, rmc_recs_len,
     rmc_key_ptrs_len, rmc_kept_trans, rmc_aout_fp_cases, rmc_cell_img: W_rr_tail.v rr_bzs_len / rr_text_rec_len /
     rr_concat_len / rr_key_ptrs_len / abyte_kept_trans / rr_aout_fp_cases / rrt_cell_img, verbatim.
   - rck / rcz and rcz_alist / rcz_asrc / rcz_aentry / rcz_aout: W_rr_tail.v rkz / rfz / rfz_* with the kept set
     changed (image bytes off g_nsrc, the bytes of the live blocks other than the table) and the blocks a footprint
     names taken from a list OB (the Permutation's other blocks).
   - the seat at 0x83f98 and the walk to the memcpy (rr_m_cpy): the lane's rrA_cpy (relay_remove_seg.v:716, the
     g_nsrc decrement and a0 / a1 / a2 at the jal) and rrA_tail_proved (relay_remove_p_c_tail.v:999, the memcpy and
     the post): ported, the register and count content; new, the W6 symbolic seat (W_rr_scan.v rr_scan form), the
     store through the hi atom A_HI 59 (W_rebase.v prebase, as W7's W_send_line_loop.v), the call by
     aj_gx_entry_at with AMEMCPY (i < N - 1) or AMEMCPYS (i = N - 1, the lane's one-case run split as PREP (c) S2 9).
   - rmc_post (RDONE from RRC and the memory after the hop): new (W6's cut predicates); arelay_at's twelfth conjunct
     (no entry block is the table, W8 42f5184c7ab) for remove_at i es is W_rr_match_cx.v's rm_base_notab. *)
(* Modified by Theorem Labs, 2026-10: ROUTE (b), STEP 3 in the room form (a Theorem Labs lane, lane RR_x): hop 4 (CPY) over ANY
   allocator relation ARx (Section c is W_relay_remove_cx.v's generic block, verbatim): laws al_X -> alx_X (BLKN for a
   live block's 0 <= n), the journal, frame and block lemmas their _x twins (the heap-block shadow facts under HP0), the
   call by aj_gx_entry_at_x with AMEMCPY / AMEMCPYS in their _x forms (the site keeps ly S Hp).  The room round: the hop
   allocates nothing, so RRC's rp_RM RP S1 kr is RDONE's last conjunct at the same state (rmc_post's new premise). *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn YP0b YP0a.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YP0d YP0c YC80 YC81 YO0a YN1e.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import W_syms W_listing W_pl W_kit W_contract.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YI00 YC5d.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import HarnessRep RelayRep gestures_end_b_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require relay_remove_b_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import W_frame W_journal W_sites W_rep W_rebase.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YCbqG YGcallx YC80x.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import
W_kit_x W_journal_x W_sites_x W_contract_x W_frame_x.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require ReplyCnt.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YCe5x.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import W_relay_remove_cx W_rr_match_cx W_rr_scan.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require W_gestures_end.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YA0nH.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

(* ------------------------------------------------------------------ the table after the copy *)
Lemma rmc_firstn_app : forall {X : Type} (l1 l2 : list X), firstn (length l1) (l1 ++ l2) = l1.
Proof. intros X l1 l2. induction l1 as [|a l1 IH]; cbn; [reflexivity|]. rewrite IH. reflexivity. Qed.
Lemma rmc_skipn_app_exact : forall {X : Type} (l1 l2 : list X), skipn (length l1) (l1 ++ l2) = l2.
Proof. intros X l1 l2. induction l1 as [|a l1 IH]; cbn; [reflexivity|]. exact IH. Qed.
Lemma rmc_skipn_app_S : forall {X : Type} (l1 l2 : list X) (x : X), skipn (S (length l1)) (l1 ++ x :: l2) = l2.
Proof. intros X l1 l2 x. induction l1 as [|a l1 IH]; cbn; [reflexivity|]. exact IH. Qed.
Lemma rmc_remove_at_last : forall {X : Type} (l : list X) (x : X),
  relay_remove_b_c.remove_at (length l) (l ++ [x]) = l.
Proof.
  intros X l x. unfold relay_remove_b_c.remove_at. rewrite rev_unit. cbv beta iota zeta.
  rewrite rev_involutive, Nat.eqb_refl. reflexivity.
Qed.
Lemma rmc_remove_at_mid : forall {X : Type} (l1 l2 : list X) (x z : X),
  relay_remove_b_c.remove_at (length l1) (l1 ++ x :: l2 ++ [z]) = l1 ++ z :: l2.
Proof.
  intros X l1 l2 x z. unfold relay_remove_b_c.remove_at.
  replace (l1 ++ x :: l2 ++ [z]) with ((l1 ++ x :: l2) ++ [z]) by (rewrite <- app_assoc; reflexivity).
  rewrite rev_unit. cbv beta iota zeta. rewrite rev_involutive.
  replace (Nat.eqb (length l1) (length (l1 ++ x :: l2))) with false
    by (symmetry; apply Nat.eqb_neq; rewrite length_app; cbn [length]; lia).
  rewrite rmc_firstn_app, rmc_skipn_app_S. reflexivity.
Qed.
Lemma rmc_split_nth : forall {X : Type} (l : list X) (d : X) (i : nat), (i < length l)%nat ->
  l = firstn i l ++ nth i l d :: skipn (S i) l.
Proof.
  intros X l d. induction l as [|a l IH]; intros i Hi; cbn [length] in Hi; [lia|].
  destruct i as [|i]; [reflexivity|]. cbn [firstn nth skipn app]. f_equal. apply IH. lia.
Qed.
Definition rmc_upd (i : nat) (e : rentry) (es : list rentry) : list rentry := firstn i es ++ e :: skipn (S i) es.
Lemma rmc_nth_last : forall (l : list rentry) d, (0 < length l)%nat -> nth (length l - 1) l d = last l d.
Proof.
  intros l d Hl.
  destruct (exists_last (l := l) ltac:(destruct l; [cbn in Hl; lia | discriminate])) as (l' & a & ->).
  rewrite length_app. cbn [length]. rewrite Nat.add_sub.
  rewrite app_nth2 by lia. rewrite Nat.sub_diag. cbn [nth]. rewrite last_last. reflexivity.
Qed.
Lemma rmc_cmap_app : forall (f : rentry -> list byte) a b,
  concat (map f (a ++ b)) = concat (map f a) ++ concat (map f b).
Proof. intros f a b. rewrite map_app, concat_app. reflexivity. Qed.
Lemma rmc_cmap_cons : forall (f : rentry -> list byte) a l, concat (map f (a :: l)) = f a ++ concat (map f l).
Proof. intros. reflexivity. Qed.
Lemma rmc_cmap_single : forall (f : rentry -> list byte) a, concat (map f [a]) = f a.
Proof. intros f a. cbn [map concat]. rewrite app_nil_r. reflexivity. Qed.
Lemma rmc_concat_cpy : forall i (es2 : list rentry), (i < length es2)%nat ->
  concat (map entry_bytes (rmc_upd i (last es2 relay_remove_b_c.no_entry) es2))
    = concat (map entry_bytes (relay_remove_b_c.remove_at i es2)) ++ entry_bytes (last es2 relay_remove_b_c.no_entry).
Proof.
  intros i es2 Hi.
  pose proof (rmc_split_nth es2 relay_remove_b_c.no_entry i Hi) as Ees.
  assert (Hlpre : length (firstn i es2) = i) by (rewrite length_firstn, Nat.min_l by lia; reflexivity).
  remember (firstn i es2) as pre eqn:Hpre.
  remember (skipn (S i) es2) as suf eqn:Hsuf.
  remember (nth i es2 relay_remove_b_c.no_entry) as x eqn:Hx.
  assert (Hru : rmc_upd i (last es2 relay_remove_b_c.no_entry) es2 = pre ++ last es2 relay_remove_b_c.no_entry :: suf)
    by (unfold rmc_upd; rewrite <- Hpre, <- Hsuf; reflexivity).
  rewrite Hru.
  destruct suf as [|y suf'] eqn:Esuf.
  - assert (Hlast : last es2 relay_remove_b_c.no_entry = x) by (rewrite Ees; cbn [app]; rewrite last_last; reflexivity).
    assert (Hrem : relay_remove_b_c.remove_at i es2 = pre)
      by (rewrite Ees, <- Hlpre; cbn [app]; apply rmc_remove_at_last).
    rewrite Hlast, Hrem.
    repeat (rewrite rmc_cmap_app || rewrite rmc_cmap_single || rewrite rmc_cmap_cons). reflexivity.
  - destruct (exists_last (l := y :: suf') ltac:(discriminate)) as (mid & zl & Hmz).
    assert (Hlast : last es2 relay_remove_b_c.no_entry = zl)
      by (rewrite Ees, Hmz, app_comm_cons, app_assoc, last_last; reflexivity).
    assert (Hrem : relay_remove_b_c.remove_at i es2 = pre ++ zl :: mid).
    { rewrite Ees, Hmz, <- Hlpre. rewrite rmc_remove_at_mid. reflexivity. }
    rewrite Hlast, Hrem, Hmz.
    repeat (rewrite rmc_cmap_app || rewrite rmc_cmap_single || rewrite rmc_cmap_cons).
    rewrite <- ?app_assoc. reflexivity.
Qed.
Lemma rmc_concat_len : forall (l : list rentry),
  Forall (fun e => length (entry_bytes e) = 56%nat) l -> length (concat (map entry_bytes l)) = (56 * length l)%nat.
Proof.
  induction l as [|e l IH]; intros HF; [reflexivity|].
  cbn [map concat length]. inversion HF as [|a b He HF' Hab]; subst.
  rewrite length_app, He, (IH HF'). lia.
Qed.
Lemma rmc_entry_len56 : forall (es : list rentry),
  Forall (fun e => length (re_pad1 e) = 4%nat /\ length (re_pad2 e) = 4%nat) es ->
  Forall (fun e => length (entry_bytes e) = 56%nat) es.
Proof. intros es HF. eapply Forall_impl; [|exact HF]. intros e [P1 P2]. exact (rrs_eb_len e P1 P2). Qed.
Lemma rmc_forall_firstn : forall {A} (P : A -> Prop) n l, Forall P l -> Forall P (firstn n l).
Proof.
  intros A P n l HF. rewrite Forall_forall in *. intros x Hx. apply HF.
  rewrite <- (firstn_skipn n l). apply in_or_app. left. exact Hx.
Qed.
Lemma rmc_forall_skipn : forall {A} (P : A -> Prop) n l, Forall P l -> Forall P (skipn n l).
Proof.
  intros A P n l HF. rewrite Forall_forall in *. intros x Hx. apply HF.
  rewrite <- (firstn_skipn n l). apply in_or_app. right. exact Hx.
Qed.
Lemma rmc_nth_skipn : forall {A} (l : list A) m k d, nth k (skipn m l) d = nth (m + k) l d.
Proof.
  intros A l m. revert l. induction m as [|m IH]; intros l k d; [reflexivity|].
  destruct l as [|a l]; cbn [skipn nth]; [destruct k; reflexivity|]. apply IH.
Qed.
Lemma rmc_slot_k : forall (l : list rentry) (tl : list byte) k d, (k < length l)%nat ->
  Forall (fun e => length (entry_bytes e) = 56%nat) l ->
  firstn 56 (skipn (56 * k) (concat (map entry_bytes l) ++ tl)) = entry_bytes (nth k l d).
Proof.
  induction l as [|e l IH]; intros tl k d Hk HF; cbn [length] in Hk; [lia|].
  inversion HF as [|a b He HF' Hab]; subst. cbn [map concat].
  rewrite <- app_assoc.
  destruct k as [|k].
  - cbn [nth]. rewrite Nat.mul_0_r, skipn_O, <- He. apply rmc_firstn_app.
  - cbn [nth]. replace (56 * S k)%nat with (56 + 56 * k)%nat by lia.
    rewrite skipn_app, He. rewrite skipn_all2 by (rewrite He; lia).
    replace (56 + 56 * k - 56)%nat with (56 * k)%nat by lia. cbn [app].
    apply IH; [lia | exact HF'].
Qed.
Definition rmc_Tpre (es : list rentry) (i : nat) : list byte := concat (map entry_bytes (firstn i es)).
Definition rmc_Tpost (es : list rentry) (i : nat) (tail : list byte) : list byte :=
  concat (map entry_bytes (skipn (S i) es)) ++ tail.
(* the 896 bytes after slot N - 1 is copied over slot i: the removal's entries, then the copied slot and the old tail *)
Lemma rmc_block_cpy : forall (es : list rentry) (tail X src Bl : list byte) (i : nat),
  (i < length es)%nat -> length X = 56%nat ->
  Forall (fun e => length (re_pad1 e) = 4%nat /\ length (re_pad2 e) = 4%nat) es ->
  Bl = rmc_Tpre es i ++ X ++ rmc_Tpost es i tail ->
  src = firstn 56 (skipn (56 * (length es - 1)) Bl) ->
  firstn (56 * i) Bl ++ src ++ skipn (56 * i + 56) Bl
    = concat (map entry_bytes (relay_remove_b_c.remove_at i es)) ++ src ++ tail.
Proof.
  intros es tail X src Bl i Hi HX HF HB Hsrc.
  pose proof (rmc_entry_len56 es HF) as HE56.
  assert (HLpre : length (rmc_Tpre es i) = (56 * i)%nat).
  { unfold rmc_Tpre. rewrite rmc_concat_len by (apply rmc_forall_firstn; exact HE56).
    rewrite length_firstn, Nat.min_l by lia. reflexivity. }
  assert (Hf1 : firstn (56 * i) Bl = rmc_Tpre es i)
    by (rewrite HB, <- HLpre; apply rmc_firstn_app).
  assert (Hf3 : skipn (56 * i + 56) Bl = rmc_Tpost es i tail).
  { rewrite HB. rewrite (app_assoc (rmc_Tpre es i) X). rewrite <- HLpre.
    replace (length (rmc_Tpre es i) + 56)%nat with (length (rmc_Tpre es i ++ X))
      by (rewrite length_app, HX; reflexivity).
    apply rmc_skipn_app_exact. }
  rewrite Hf1, Hf3. unfold rmc_Tpost.
  rewrite (app_assoc src), (app_assoc (rmc_Tpre es i)).
  rewrite (app_assoc (concat (map entry_bytes (relay_remove_b_c.remove_at i es)))).
  f_equal.
  destruct (Nat.eq_dec i (length es - 1)) as [Hlast | Hne].
  - (* i = N - 1: src = X, remove_at i es = firstn i es, no entry after slot i *)
    assert (Hsk : skipn (S i) es = []) by (apply skipn_all2; lia).
    assert (HsrcX : src = X).
    { rewrite Hsrc, HB, <- Hlast, <- HLpre, rmc_skipn_app_exact, <- HX. apply rmc_firstn_app. }
    assert (Hrem : relay_remove_b_c.remove_at i es = firstn i es).
    { pose proof (rmc_split_nth es relay_remove_b_c.no_entry i Hi) as E.
      rewrite Hsk in E. rewrite E at 1.
      assert (Hl : length (firstn i es) = i) by (rewrite length_firstn, Nat.min_l by lia; reflexivity).
      rewrite <- Hl at 1. apply rmc_remove_at_last. }
    replace (concat (map entry_bytes (skipn (S i) es))) with (@nil byte) by (rewrite Hsk; reflexivity).
    rewrite HsrcX, Hrem, app_nil_r. unfold rmc_Tpre. reflexivity.
  - (* i < N - 1: src = entry_bytes (last es), rmc_concat_cpy closes it *)
    assert (Hilt : (i < length es - 1)%nat) by lia.
    pose proof (rmc_nth_last es relay_remove_b_c.no_entry ltac:(lia)) as Hnl.
    assert (HsrcL : src = entry_bytes (last es relay_remove_b_c.no_entry)).
    { rewrite Hsrc, HB, (app_assoc (rmc_Tpre es i) X).
      replace (56 * (length es - 1))%nat
        with (length (rmc_Tpre es i ++ X) + 56 * (length es - 1 - (i + 1)))%nat
        by (rewrite length_app, HLpre, HX; lia).
      rewrite skipn_app, skipn_all2 by lia.
      replace (length (rmc_Tpre es i ++ X) + 56 * (length es - 1 - (i + 1)) - length (rmc_Tpre es i ++ X))%nat
        with (56 * (length es - 1 - (i + 1)))%nat by lia.
      rewrite app_nil_l. unfold rmc_Tpost.
      rewrite (rmc_slot_k (skipn (S i) es) tail (length es - 1 - (i + 1)) relay_remove_b_c.no_entry).
      - rewrite rmc_nth_skipn, <- Hnl. f_equal. f_equal. lia.
      - rewrite length_skipn. lia.
      - apply rmc_forall_skipn; exact HE56. }
    rewrite HsrcL.
    pose proof (rmc_concat_cpy i es Hi) as Hcc.
    assert (Hup : concat (map entry_bytes (rmc_upd i (last es relay_remove_b_c.no_entry) es))
                  = rmc_Tpre es i ++ entry_bytes (last es relay_remove_b_c.no_entry) ++
                    concat (map entry_bytes (skipn (S i) es))).
    { unfold rmc_upd, rmc_Tpre. rewrite rmc_cmap_app, rmc_cmap_cons. reflexivity. }
    rewrite Hup in Hcc. exact Hcc.
Qed.
(* the fds of the removal are distinct (new) *)
Lemma rmc_nodup_remove : forall (es : list rentry) i, (i < length es)%nat ->
  List.NoDup (map re_fd es) -> List.NoDup (map re_fd (relay_remove_b_c.remove_at i es)).
Proof.
  intros es i Hi HND.
  pose proof (Permutation_map re_fd (rm_remove_perm es i relay_remove_b_c.no_entry Hi)) as HPm.
  apply (Permutation_NoDup HPm) in HND. cbn [map] in HND. apply List.NoDup_cons_iff in HND as [_ HND]. exact HND.
Qed.
Lemma rmc_in_remove : forall (es : list rentry) i x, (i < length es)%nat ->
  In x (relay_remove_b_c.remove_at i es) -> In x es.
Proof.
  intros es i x Hi Hx. apply (Permutation_in _ (Permutation_sym (rm_remove_perm es i relay_remove_b_c.no_entry Hi))).
  right. exact Hx.
Qed.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section b.
Context {PI : PAImg fr_prog_listing}.
#[local] Notation SEGS := (@pa_segs _ fr_prog_listing PI).
#[local] Notation VAL := (@pa_val _ fr_prog_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ fr_prog_listing PI).
#[local] Notation BASE := (@pa_val _ fr_prog_listing PI A_TEXT).

(* ------------------------------------------------------------------ the seat at 0x83f98 (new) *)
(* s7 / s9 hold the listing's hi atoms (a PLdHi slot runs only on its own base atom); g_src (A_OBJ 8, read-only) holds
   G0 (atom 32), g_nsrc (A_OBJ 7, writable) holds N (atom 33); s8 = 56 i is atom 24. *)
Definition rmc_sr : list sv := sr_set (sr_set sr_atoms 23%bv (SOff (A_HI 59) 0)) 25%bv (SOff (A_HI 60) 0).
Definition rmc_src : YP09.region := YP09.mkRegion (Some (A_OBJ 8)) 0 8 0 0 [YP09.mkChunk 0 (CVal 8 (SOff 32 0))].
Definition rmc_nsrc : YP09.region := YP09.mkRegion (Some (A_OBJ 7)) 0 4 0 4 [YP09.mkChunk 0 (CVal 4 (SOff 33 0))].
Definition rmc_OBJF : afact := mkAF 0x10000 0x5fb000 0.
Definition rmc_HIF : afact := mkAF 0x10000 0x5fb800 0.
Definition rmc_facts : facts :=
mkFacts [ (22%nat, mkAF SB SB 0); (24%nat, mkAF 0 840 0); (32%nat, mkAF 4096 140737479966720 4); (33%nat, mkAF 1 16 0);
  (A_OBJ 7, rmc_OBJF); (A_OBJ 8, rmc_OBJF); (A_HI 59, rmc_HIF) ] [] [].
Definition ss_rmc : sstate := mkSS A_rr_cpy rmc_sr [rmc_src; rmc_nsrc] None rmc_facts.
Definition rmc_Bx : sv := SOff 22 0.
(* the registers the run keeps (RRU's rregs_base: sp gp tp s0 s1 s2 s4 s5 s6 s10 s11) *)
Definition RMC_KEPT : list (bv 5) := [2; 3; 4; 8; 9; 18; 20; 21; 22; 26; 27]%bv.
Definition rmc_Bspan : Z * Z := (SB, SB + 2 ^ 44 - 1).
Definition rmc_extra (G0 N : Z) : list word := map (Z_to_bv 64) [G0; N].

Section c.
Variable B : asyms.
Variable PST : list (Z * Z).
Variable ARx : alayout -> astate -> list Z -> world SEGS -> (word -> option byte) -> Model -> Prop.
Variable MT : ameter_ops.
(* the room round (W_journal_x.v Record roomp): the allocator's room invariant and the live counts, after MT *)
Variable RP : roomp.
Variable MMAX : Z.
Variable RG : rep_globals.
(* the free interceptor's caller-context table (one table for free and free(NULL): K0_SITES' CTX_AFREE) *)
Variable CTX_AFREE : list (list Z).
Context {hl : Z}.
(* ---- The Section hypotheses every segment file copies (the names are the contracts'). ---- *)
(* the generic relation's laws and its empty head set (CONVERSION.md (sha256 1015972e02a9; internal record) 1.) *)
Hypothesis LAWS : AR_laws_x SEGS B ARx hl.
Hypothesis HP0 : forall ly S Hp W mem md, ARx ly S Hp W mem md -> Hp = [].
Hypothesis TL : PALib B.
Hypothesis TLF : PALibF B.
(* the frame twins' hypotheses (W_frame_x.v): the image cover IMGC (frm_off_imgP_x, blk_off_imgP_x), a live block's
   size non-negative (BLKN, W_kit_x.v), the owned-low law OWNLOW, the model invariant WFx with its law WFL and the two
   facts the twins read off model_laws / stack_malloc_progressP (SFREE, SMALLOC) *)
Hypothesis IMGC : forall ly S Hp W mem md, ARx ly S Hp W mem md ->
fst (ly_img ly) <= 0x10000 /\ 0x5fb000 <= fst (ly_img ly) + snd (ly_img ly).
Hypothesis BLKN : forall ly S Hp W mem md p n, ARx ly S Hp W mem md -> In (p, n) (ablocks B ly S) -> 0 <= n.
Hypothesis OWNLOW : ARx_owned_low_law SEGS B ARx.
Variable WFx : astate -> Prop.
Hypothesis WFL : ARx_wf_law SEGS ARx WFx.
Hypothesis SFREE : forall s cid pos, WFx s -> In (cid, pos) (frames s) ->
exists l1 l2, frames s = l1 ++ (cid, pos) :: l2 /\ frames (stack_free_state cid pos s) = l1 ++ l2.
Hypothesis SMALLOC : forall s cid, WFx s -> 0 <= cid <= 10 -> count_cid cid (frames s) < fs_frames cid ->
exists pos s', apath (stack_malloc cid s) [] (PFake cid pos, s') /\ (exists f, s' = set_fs f s) /\
frames s' = (cid, pos) :: frames s /\ ~ In (cid, pos) (frames s).
Hypothesis ASMP : astack_malloc_pres_x SEGS B ARx 0.
Hypothesis ASF : astack_free_law_x SEGS B ARx.
Hypothesis FFL : frame_flag_lawP_x SEGS B ARx.
Hypothesis HG : gx_ok SEGS B (G_RR B RG).
(* the register images of g_nsrc / g_src: the auipc's of 0x83ee8 (s7, listing A_HI 59) and 0x83ef8 (s9, A_HI 60).
   The abstract placement does not fix them against the objects (W_rebase.v:7-15); PB_fr discharges both by
   vm_compute, as W_send_line_cx.v's HH17 .. HH24. *)
Hypothesis HH59 : VAL (A_HI 59) = rg_nsrc RG + RR_HI_NSRC.
Hypothesis HH60 : VAL (A_HI 60) = rg_src RG + RR_HI_SRC.
(* g_wake[1], read at 0x83fe0 by PLdHi (A_OBJ 4) (W5's HV4, verbatim) *)
Hypothesis HV4 : VAL (A_OBJ 4) = rg_wake RG + 4.
(* the relay's and the output's global cells are pairwise apart, and errno with them; the four that neither rg_place
   nor gx_ok places are image bytes (so apart from the frames, the fake frame's shadow and the stack).  The pinned
   placement decides both by vm_compute at fr_globals, as W7's W_drain_cx.v HRGD / HGSB. *)
Hypothesis HRGP : zpairwise_disjoint
[(rg_lock RG, rg_lock RG + 12); (rg_s RG, rg_s RG + 4 * ASRC); (rg_src RG, rg_src RG + 8);
 (rg_nsrc RG, rg_nsrc RG + 4); (rg_capsrc RG, rg_capsrc RG + 4); (rg_send_max RG, rg_send_max RG + 8);
 (rg_nout RG, rg_nout RG + 8); (rg_capout RG, rg_capout RG + 8); (rg_out RG, rg_out RG + 8);
 (rg_client RG, rg_client RG + 4); (rg_client_broken RG, rg_client_broken RG + 1);
 (rg_send_dead RG, rg_send_dead RG + 1); (rg_send_eintr RG, rg_send_eintr RG + 1); (rg_wake RG + 4, rg_wake RG + 8);
 (as_errno B, as_errno B + 4)].
Hypothesis HRGI : forall a,
(rg_capsrc RG <= a < rg_capsrc RG + 4 \/ rg_send_max RG <= a < rg_send_max RG + 8 \/
 rg_client RG <= a < rg_client RG + 4 \/ rg_send_dead RG <= a < rg_send_dead RG + 1) ->
in_img SEGS a /\ ~ Exists (in_zr a) (as_owned_static B).
(* no read-only image byte is owned by the runtime (W_gesture_end.v's HROMO form): rom_view survives the stack
   allocator's calls (W_journal.v ajournal_gx_rom_view) *)
Hypothesis HROMO : rom_out SEGS B (G_RR B RG).
Hypothesis MLAW : ameter_laws MT.
(* the live-state meter does not see the fake frame: its seat and its release are set_fs steps (W8's ruling, the
   lead's KF-COUNT #4: the ablocks form is false at the count meter) *)
Hypothesis MO_FR : forall s f, mo_le MT s (set_fs f s) 0.
(* the runtime entries relay_remove calls, at their SIGMA pcs (W_sites.v / the donor's YG0d.v / W_journal.v) *)
Hypothesis ALOCK : alock_realizes_x B ARx (SIGMA WS_pthread_mutex_lock).
Hypothesis AUNLOCK : aunlock_realizes_x B ARx (SIGMA WS_pthread_mutex_unlock).
Hypothesis AFREE : afree_cf_rule_c_x SEGS B PST ARx MT RP CTX_AFREE.
Hypothesis AMEMCPY : aintrin_realizes_x SEGS B ARx OCpy (SIGMA WS_asan_memcpy).
Hypothesis AMEMCPYS : amemcpy_same_realizes_x B ARx (SIGMA WS_asan_memcpy).
(* the program functions relay_remove calls (W7's drain, W4's gestures_end), by their published _x specs *)
Hypothesis DRAIN : dr_spec_x B PST ARx MT RP MMAX RG (BASE + AF_fr_drain).
Hypothesis GSE : gse_spec_x B PST ARx MT RP MMAX RG (BASE + AF_fr_gestures_end).
(* free (s->buf) at 0x83f94 with s->buf = NULL (an entry with cap 0) *)
Hypothesis AFREEN : afree_null_cf_rule_c_x SEGS B PST ARx MT RP CTX_AFREE.
(* the bytes of " end\0" (.str.4, read-only .rodata), which gse_spec's / ge_spec's premise garr8 (VAL A_lit_end5)
   (bzs END5) needs with rom_view (no zero-shadow fact: the literal's last shadow granule is partial): k3's HEND5L, verbatim (W_drain_cx.v dlit_at form; PB_fr
   by vm_compute) *)
Hypothesis HEND5L : forall k, (k < 5)%nat -> YG0d.in_rom SEGS (VAL A_lit_end5 + Z.of_nat k) /\
  seg_rom SEGS (Z_to_bv 64 (VAL A_lit_end5 + Z.of_nat k)) = nth_error END5 k.
(* The program statics PST hold no byte the walk carries through a journal's image clause, which exempts PST
   (YCbqG.v ajournal_x): no read-only byte (ajournal_gx_rom_view_x) and no byte of the relay's / output's cells or
   errno (rr_gcells, HRGP's list).  At PST := [] both hold trivially (W_relay_finish_h.v's PSTR / PSTC form). *)
Hypothesis PSTR : forall a, in_rom SEGS a -> ~ Exists (in_zr a) PST.
Hypothesis PSTG : forall a, Exists (fun r => fst r <= a < snd r) (rr_gcells B RG) -> ~ Exists (in_zr a) PST.

Let RUN := paj_run_x_x B PST ARx LAWS (G_RR B RG) HG 0 [].
Let RUNTO := paj_run_to_x_x B PST ARx LAWS (G_RR B RG) HG 0 [].

(* ---- The kept bytes of this hop: image bytes off g_nsrc, and the bytes of the live blocks OB other than the table
   (W_rr_tail.v rkz / rfz with this hop's writes: g_nsrc, slot i of the table, the memcpy's scratch). ---- *)
Definition rck (OB : list (Z * Z)) (a : Z) : Prop :=
  (in_img SEGS a /\ ~ (rg_nsrc RG <= a < rg_nsrc RG + 4)) \/
  (exists p n, In (p, n) OB /\ p <= a < p + req_size n).
Definition rcz (OB : list (Z * Z)) (fp : list (Z * Z)) : Prop :=
  forall r, In r fp -> forall a, fst r <= a < snd r -> rck OB a.
Lemma rcz_nil : forall OB, rcz OB [].
Proof. intros OB r []. Qed.
Lemma rcz_cons : forall OB r fp, (forall a, fst r <= a < snd r -> rck OB a) -> rcz OB fp -> rcz OB (r :: fp).
Proof. intros OB r fp H1 H2 r' [<- | Hr]; [exact H1 | exact (H2 r' Hr)]. Qed.
Lemma rcz_app : forall OB f1 f2, rcz OB f1 -> rcz OB f2 -> rcz OB (f1 ++ f2).
Proof. intros OB f1 f2 H1 H2 r Hr. apply in_app_or in Hr as [Hr | Hr]; [exact (H1 r Hr) | exact (H2 r Hr)]. Qed.
Lemma rck_blk : forall OB p n len a, In (p, n) OB -> 0 <= n -> len <= n -> p <= a < p + len -> rck OB a.
Proof.
intros OB p n len a Hin Hn Hl Ha. right. exists p, n. split; [exact Hin|].
pose proof (req_size_pos n Hn) as [_ Hr]. lia.
Qed.
Lemma rmc_bzs_len : forall l, Z.of_nat (length (bzs l)) = Z.of_nat (length l).
Proof. intros l. unfold bzs. rewrite length_map. reflexivity. Qed.
Lemma rmc_text_rec_len : forall r, length (text_rec r) = 16%nat.
Proof. intros r. unfold text_rec. rewrite length_app. reflexivity. Qed.
Lemma rmc_recs_len : forall rs, length (concat (map text_rec rs)) = (16 * length rs)%nat.
Proof.
induction rs as [|r rs IH]; [reflexivity|].
cbn [map concat]. rewrite length_app, rmc_text_rec_len, IH. cbn [length]. lia.
Qed.
Lemma rmc_key_ptrs_len : forall ks, length (key_ptrs ks) = (8 * length ks)%nat.
Proof.
induction ks as [|k ks IH]; [reflexivity|].
unfold key_ptrs in *. cbn [map concat].
rewrite length_app, IH, OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Lib.Mem.length_le8. cbn [length]. lia.
Qed.
Lemma rcz_alist : forall OB ly S W mem LA l lines,
  alist_at B ly S W mem LA l lines -> (forall a, LA <= a < LA + 16 -> rck OB a) ->
  (forall b, In b (alist_blks l) -> In b OB) -> rcz OB (alist_fp LA l).
Proof.
intros OB ly S W mem LA l lines (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9) HLA HOB.
rewrite Forall_forall in H9.
unfold alist_fp. apply rcz_cons; [exact HLA|]. apply rcz_app.
- destruct (Z.eqb_spec (hl_cap l) 0) as [Hc|Hc]; [apply rcz_nil|].
  destruct H6 as [[Hc0 _] | (Hcp & Hin & Hj & Hg)]; [lia|].
  assert (HB : In (hl_v l, AREC * hl_cap l) OB).
  { apply HOB. unfold alist_blks. apply in_or_app. left. rewrite (proj2 (Z.eqb_neq _ _) Hc). left. reflexivity. }
  apply rcz_cons; [|apply rcz_nil]. cbn [gfp fst snd]. intros a Ha.
  rewrite rmc_bzs_len, length_app, Nat2Z.inj_add, rmc_recs_len, Hj in Ha. unfold hl_n, AREC in *.
  apply (rck_blk OB (hl_v l) (16 * hl_cap l) (16 * hl_cap l) a HB); lia.
- intros r Hr. apply in_map_iff in Hr as (x & <- & Hx). cbn [gfp fst snd]. intros a Ha.
  assert (HB : In (fst x, Z.of_nat (length (snd x)) + 1) OB).
  { apply HOB. unfold alist_blks. apply in_or_app. right.
    apply (in_map (fun r => (fst r, Z.of_nat (length (snd r)) + 1))). exact Hx. }
  rewrite rmc_bzs_len, length_app in Ha. cbn [length] in Ha.
  apply (rck_blk OB (fst x) (Z.of_nat (length (snd x)) + 1) (Z.of_nat (length (snd x)) + 1) a HB); lia.
Qed.
Lemma rcz_asrc : forall OB ly S W mem HA h,
  asrc_at B ly S W mem HA h -> (forall a, HA <= a < HA + ASRC -> rck OB a) ->
  (forall b, In b (asrc_blks h) -> In b OB) -> rcz OB (asrc_fp HA h).
Proof.
intros OB ly S W mem HA h HS HHA HOB.
pose proof HS as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Hpend & _ & _ & _ & _ & _ & _ & _ & Hpb & Hpj & _ &
                  _ & Hexp & Hheld & _).
assert (K16 : forall a, HA + 16 <= a < HA + 16 + 16 -> rck OB a) by (intros a Ha; apply HHA; unfold ASRC; lia).
assert (K64 : forall a, HA + 64 <= a < HA + 64 + 16 -> rck OB a) by (intros a Ha; apply HHA; unfold ASRC; lia).
assert (K80 : forall a, HA + 80 <= a < HA + 80 + 16 -> rck OB a) by (intros a Ha; apply HHA; unfold ASRC; lia).
pose proof (rcz_alist OB ly S W mem (HA + 16) (hs_pending h) false Hpend K16
  ltac:(intros b Hb; apply HOB; right; apply in_or_app; left; exact Hb)) as A1.
pose proof (rcz_alist OB ly S W mem (HA + 64) (hs_expected h) true Hexp K64
  ltac:(intros b Hb; apply HOB; right; apply in_or_app; right; apply in_or_app; left; exact Hb)) as E1.
pose proof (rcz_alist OB ly S W mem (HA + 80) (hs_held h) true Hheld K80
  ltac:(intros b Hb; apply HOB; right; apply in_or_app; right; apply in_or_app; right; exact Hb)) as L1.
unfold asrc_fp. apply rcz_cons; [exact HHA|]. apply rcz_cons.
- cbn [gfp fst snd]. intros a Ha. rewrite rmc_bzs_len, Hpj in Ha.
  apply (rck_blk OB (hs_partial h) APARTIAL APARTIAL a (HOB _ (or_introl eq_refl))); unfold APARTIAL in *; lia.
- apply rcz_app; [exact A1|]. apply rcz_app; [exact E1 | exact L1].
Qed.
Lemma rcz_aentry : forall OB ly S W mem e,
  aentry_ok B ly S W mem e -> (forall b, In b (aentry_blks e) -> In b OB) -> rcz OB (aentry_fp e).
Proof.
intros OB ly S W mem e (K1 & K2 & K3 & K4 & K5 & K6 & K7 & K8 & K9 & K10 & K11 & K12 & K13 & K14 & K15) HOB.
rewrite Forall_forall in K15.
unfold aentry_fp. apply rcz_app.
- destruct (Z.eqb_spec (re_cap e) 0) as [Hc|Hc]; [apply rcz_nil|].
  destruct K10 as [(Hc0 & _) | (Hcp & Hin & Hj & Hg)]; [lia|].
  assert (HB : In (re_buf e, re_cap e) OB).
  { apply HOB. unfold aentry_blks. apply in_or_app. left. rewrite (proj2 (Z.eqb_neq _ _) Hc). left. reflexivity. }
  apply rcz_cons; [|apply rcz_nil]. cbn [gfp fst snd]. intros a Ha.
  rewrite rmc_bzs_len, length_app, Nat2Z.inj_add, Hj, K7 in Ha.
  apply (rck_blk OB (re_buf e) (re_cap e) (re_cap e) a HB); lia.
- apply rcz_cons.
  + cbn [gfp fst snd]. intros a Ha. rewrite rmc_bzs_len, rmc_key_ptrs_len in Ha.
    destruct K12 as [(Hz & Hks) | (Hz & Hin & Hk1 & Hk2 & Hg)].
    { rewrite Hks in Ha. cbn [length] in Ha. lia. }
    assert (HB : In (re_hp e, re_kh e) OB).
    { apply HOB. unfold aentry_blks. apply in_or_app. right. apply in_or_app. left.
      rewrite (proj2 (Z.eqb_neq _ _) Hz). left. reflexivity. }
    unfold re_nheld in Hk1.
    apply (rck_blk OB (re_hp e) (re_kh e) (Z.of_nat (8 * length (re_keys e))) a HB); lia.
  + intros r Hr. apply in_map_iff in Hr as (k & <- & Hk). cbn [gfp fst snd]. intros a Ha.
    assert (HB : In (key_addr k, Z.of_nat (length (key_text k)) + 1) OB).
    { apply HOB. unfold aentry_blks. apply in_or_app. right. apply in_or_app. right.
      apply (in_map (fun k => (key_addr k, Z.of_nat (length (key_text k)) + 1))). exact Hk. }
    rewrite rmc_bzs_len, length_app in Ha. cbn [length] in Ha.
    apply (rck_blk OB (key_addr k) (Z.of_nat (length (key_text k)) + 1) (Z.of_nat (length (key_text k)) + 1) a HB);
      lia.
Qed.
Lemma rmc_aout_fp_cases : forall cap out r, In r (aout_fp B RG cap out) ->
  In r (aout_fp B RG 0 0) \/ (cap <> 0 /\ r = (out, out + cap)).
Proof.
intros cap out r Hr. unfold aout_fp in Hr |- *. cbn [Z.eqb] in *.
do 9 (destruct Hr as [Hr | Hr]; [left; subst r; cbn; tauto|]).
destruct (Z.eqb_spec cap 0); [destruct Hr | destruct Hr as [<- | []]; right; split; [exact n | reflexivity]].
Qed.
Lemma rcz_aout : forall OB ly S W mem c O mx no cap out,
  aout_at B RG ly S W mem c O mx no cap out -> rcz OB (aout_fp B RG 0 0) ->
  (forall b, In b (aout_blks cap out) -> In b OB) -> rcz OB (aout_fp B RG cap out).
Proof.
intros OB ly S W mem c O mx no cap out HO HC HOB.
pose proof HO as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
                  Hblk).
intros r Hr a Ha. destruct (rmc_aout_fp_cases cap out r Hr) as [Hr0 | (Hc & ->)]; [exact (HC r Hr0 a Ha)|].
destruct Hblk as [(Hc0 & _) | (Hcp & _ & Hin & _)]; [lia|].
assert (HB : In (out, cap) OB) by (apply HOB; unfold aout_blks; rewrite (proj2 (Z.eqb_neq _ _) Hc); left; reflexivity).
cbn [fst snd] in Ha. apply (rck_blk OB out cap cap a HB); lia.
Qed.

(* ---- the global cells the post reads, other than g_nsrc: image bytes apart from g_nsrc (W_rr_tail.v rr_cells /
   rrt_cell_img; HRGP for the separation) ---- *)
Definition rmc_cells (a : Z) : Prop :=
  rg_lock RG <= a < rg_lock RG + 12 \/ rg_s RG <= a < rg_s RG + 4 * ASRC \/ rg_src RG <= a < rg_src RG + 8 \/
  rg_capsrc RG <= a < rg_capsrc RG + 4 \/ rg_send_max RG <= a < rg_send_max RG + 8 \/
  rg_nout RG <= a < rg_nout RG + 8 \/ rg_capout RG <= a < rg_capout RG + 8 \/ rg_out RG <= a < rg_out RG + 8 \/
  rg_client RG <= a < rg_client RG + 4 \/ rg_client_broken RG <= a < rg_client_broken RG + 1 \/
  rg_send_dead RG <= a < rg_send_dead RG + 1 \/ rg_send_eintr RG <= a < rg_send_eintr RG + 1 \/
  rg_wake RG + 4 <= a < rg_wake RG + 8 \/ as_errno B <= a < as_errno B + 4.
Ltac rmc_exists := repeat (first [apply Exists_cons_hd; unfold in_zr; cbn [fst snd]; lia | apply Exists_cons_tl]).
Lemma rmc_cell_img : rg_place B RG -> forall a, rmc_cells a -> in_img SEGS a.
Proof.
intros RGP a Ha. destruct RGP as (_ & _ & _ & _ & _ & _ & RGIMG & _). unfold rmc_cells in Ha.
destruct Ha as [Ha|[Ha|[Ha|[Ha|[Ha|[Ha|[Ha|[Ha|[Ha|[Ha|[Ha|[Ha|[Ha|Ha]]]]]]]]]]]]];
first [ exact (proj1 (RGIMG a ltac:(unfold rg_rng; tauto)))
      | exact (proj1 (HRGI a ltac:(tauto)))
      | exact (proj1 (HG a ltac:(unfold inG, G_RR, G_DR, G_SL; rmc_exists))) ].
Qed.
Lemma rmc_cell_nnsrc : forall a, rmc_cells a -> ~ (rg_nsrc RG <= a < rg_nsrc RG + 4).
Proof.
intros a Ha. pose proof HRGP as H. cbn [zpairwise_disjoint zall_disjoint] in H. unfold zdisj in H. cbn [fst snd] in H.
destruct H as ((_ & _ & D0 & _) & (_ & D1 & _) & (D2 & _) &
  (D4 & D5 & D6 & D7 & D8 & D9 & D10 & D11 & D12 & D13 & D14 & _) & _).
unfold rmc_cells in Ha.
destruct Ha as [Ha|[Ha|[Ha|[Ha|[Ha|[Ha|[Ha|[Ha|[Ha|[Ha|[Ha|[Ha|[Ha|Ha]]]]]]]]]]]]];
[revert D0 Ha | revert D1 Ha | revert D2 Ha | revert D4 Ha | revert D5 Ha | revert D6 Ha | revert D7 Ha |
 revert D8 Ha | revert D9 Ha | revert D10 Ha | revert D11 Ha | revert D12 Ha | revert D13 Ha | revert D14 Ha];
clear; intros; lia.
Qed.
Lemma rmc_kept_trans : forall (W W1 W2 : world SEGS) m m1 m2 a,
  abyte_kept W m W1 m1 a -> abyte_kept W1 m1 W2 m2 a -> abyte_kept W m W2 m2 a.
Proof.
intros W W1 W2 m m1 m2 a (A1 & B1) (A2 & B2). split; [rewrite A2; exact A1 | intros Hw; exact (B2 (B1 Hw))].
Qed.
(* byte arrays moved, cut (new) *)
Lemma rmc_garr8_moved : forall (W W' : world SEGS) m m' a b l,
  garr8 SEGS (arm W m) a l ->
  (forall j, 0 <= j < Z.of_nat (length l) -> aview SEGS (w_H W') m' (b + j) = aview SEGS (w_H W) m (a + j)) ->
  garr8 SEGS (arm W' m') b l.
Proof.
intros W W' m m' a b l Hg Hk j Hj. destruct (Hg j Hj) as [Hv Hr]. split; [|exact Hr].
unfold arm in *. apply (val_mem_moved SEGS (w_H W) (w_H W') m m' (a + Z.of_nat j) (b + Z.of_nat j) 1); [|exact Hv].
intros k Hk'. cbn in Hk'. replace k with 0 by lia. rewrite !Z.add_0_r. apply Hk. lia.
Qed.
Lemma rmc_garr8_skipn : forall m a (l : list Z) k, (k <= length l)%nat -> garr8 SEGS m a l ->
  garr8 SEGS m (a + Z.of_nat k) (skipn k l).
Proof.
intros m a l k Hk Hg. rewrite <- (firstn_skipn k l) in Hg. apply garr8_app in Hg as [_ Hg].
rewrite length_firstn, Nat.min_l in Hg by lia. exact Hg.
Qed.
Lemma rmc_garr8_firstn : forall m a (l : list Z) k, garr8 SEGS m a l -> garr8 SEGS m a (firstn k l).
Proof.
intros m a l k Hg. rewrite <- (firstn_skipn k l) in Hg. apply garr8_app in Hg as [Hg _]. exact Hg.
Qed.

(* ---- RDONE from RRC and what the hop did to the memory (new): only g_nsrc (N -> N - 1), slot i (the copy of slot
   N - 1) and the memcpy's scratch below sp changed, every present byte stays present, the journal holds. ---- *)
Lemma rmc_post : forall cx i ly1 S1 Hp1 W1 m1 md1 k1 F FL e1 h1 ev LB c2 O2 cap2 out2 X fpos m3 md3,
RBASE B ARx MT RP MMAX RG cx ->
0 <= rxFD cx -> (i < length (rxes cx))%nat -> re_fd (rnth cx i) = rxFD cx ->
ARx ly1 S1 Hp1 W1 m1 md1 ->
apres_kept B (rxW cx) (rxmem cx) W1 m1 -> rr_frame cx fpos F FL ly1 W1 m1 ->
alock_at RG W1 m1 true -> awake_at RG W1 m1 ->
rmdrel B RG cx i ly1 S1 W1 m1 e1 h1 LB ->
rmtbl B RG cx i ly1 S1 W1 m1 X ->
sl_sends (rxmx cx) (rmc1 cx i ev) (rmO1 cx i LB) (rmcap1 cx i) (ge_bytes (re_keys e1)) = (c2, O2, cap2) ->
aout_at B RG ly1 S1 W1 m1 c2 O2 (rxmx cx) (Z.of_nat (length O2)) cap2 out2 ->
Permutation (ablocks B ly1 S1)
  ((rxG0 cx, ATABLE) :: rmOB cx i ++ rmsrc cx i h1 ++ aout_blks cap2 out2 ++ rxrest cx) ->
rmgs RG cx W1 m1 ->
mo_le MT (rxS cx) S1 (tr_cost MT (rtr cx)) ->
rp_RM RP S1 (rxkr cx) ->
(forall a, 0 <= a < 2 ^ 64 -> ~ (rg_nsrc RG <= a < rg_nsrc RG + 4) -> ~ (rmSA cx i <= a < rmSA cx i + AENT) ->
   ~ (rsp0 cx - RR_FRAME - ESTACK <= a < rsp0 cx - RR_FRAME) ->
   aview SEGS (w_H W1) m3 a = aview SEGS (w_H W1) m1 a) ->
(forall a, apresent (w_H W1) m1 a -> apresent (w_H W1) m3 a) ->
val_mem SEGS (arm W1 m3) (rg_nsrc RG) 4 (rN cx - 1) ->
(forall t, 0 <= t < AENT ->
   aview SEGS (w_H W1) m3 (rmSA cx i + t) = aview SEGS (w_H W1) m1 (rxG0 cx + AENT * (rN cx - 1) + t)) ->
ajournal_gx_x (SK := SK) SEGS B PST ARx (G_RR B RG) 0 [] RR_STK_x (rsp0 cx) (rFP cx)
  (rxly cx) (rxS cx) (rxHp cx) (rxW cx) (rxmem cx) (rxmd cx) [(0, fpos)] ly1 S1 Hp1 W1 m3 md3 k1 ->
RDONE B PST ARx MT RP RG cx i F FL ly1 S1 Hp1 W1 m3 md3 k1.
Proof.
intros cx i ly1 S1 Hp1 W1 m1 md1 k1 F FL e1 h1 ev LB c2 O2 cap2 out2 X fpos m3 md3
  HB HFD0 Hi Hfd HAR HPK1 HFR1 HLK1 HWK1 HDR HTB HSL HOUT HPERM HGS HMO HRM KM PM NSM SLM HJ3.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof pa_segs_low as Hsegs.
pose proof HB as (HPRE & _ & _ & RGP & _ & _ & _ & _ & HREL0 & _ & HROM0 & HSRC0 & HPERM0 & _).
pose proof RGP as (_ & _ & _ & _ & _ & _ & RGIMG & _ & _).
pose proof HPRE as (_ & _ & _ & _ & _ & Hstk & _).
pose proof Hstk as (_ & _ & Hceil & Hslo & Hshi & H47 & _).
assert (WS : RR_STK_x = 17072) by reflexivity. assert (WF : RR_FRAME = 96) by reflexivity.
assert (Hes : ESTACK = 4096) by reflexivity.
fold (rsp0 cx) in Hslo, Hshi.
assert (HSC : alloc_ceiling <= rsp0 cx - RR_FRAME - ESTACK) by lia.
assert (HSP : rsp0 cx <= 2 ^ 47) by lia.
clear Hceil Hslo Hshi H47 Hstk HPRE.
pose proof HTB as (Tsrc & Tsrcw & Tnsrc & Tnsrcw & Tcap & Tcapw & TIn & TX & (tail & Ttl & Ttab) & Tslw & Tok).
pose proof HREL0 as (_ & _ & _ & _ & _ & _ & Rlen16 & _ & _ & ROK & RND & _).
destruct (alx_blocks _ _ _ LAWS ly1 S1 Hp1 W1 m1 md1 (rxG0 cx) ATABLE HAR TIn) as (HG16 & HG4096 & HGceil & _ & _ & _).
change (req_size ATABLE) with 896 in HGceil.
assert (HN : 1 <= rN cx <= 16) by (unfold rN; lia).
assert (HIN : In (0, fpos) (frames S1)).
{ pose proof HJ3 as (_ & _ & (memS & HJd & _) & _). pose proof HJd as (_ & _ & _ & _ & _ & Hfrs & _).
  rewrite Hfrs. left. reflexivity. }
(* the other blocks: live, apart from the table *)
set (OB := rmOB cx i ++ rmsrc cx i h1 ++ aout_blks cap2 out2 ++ rxrest cx).
assert (OBIN : forall b, In b OB -> In b (ablocks B ly1 S1))
  by (intros b Hb; apply (Permutation_in _ (Permutation_sym HPERM)); right; exact Hb).
assert (OBNE : forall b, In b OB -> b <> (rxG0 cx, ATABLE)).
{ intros b Hb Eb. pose proof (W_gestures_end.gse_nodup_x B ARx LAWS BLKN ly1 S1 Hp1 W1 m1 md1 HAR) as ND.
  apply (Permutation_NoDup HPERM) in ND. apply List.NoDup_cons_iff in ND as [Hni _]. apply Hni. rewrite <- Eb. exact Hb. }
assert (NSIMG : forall a, rg_nsrc RG <= a < rg_nsrc RG + 4 -> in_img SEGS a)
  by (intros a Ha; apply RGIMG; unfold rg_rng; tauto).
assert (TBIMG : forall a, rxG0 cx <= a < rxG0 cx + 896 -> ~ in_img SEGS a)
  by (intros a Ha; exact (blk_img_x SEGS B ARx LAWS ly1 S1 Hp1 W1 m1 md1 (rxG0 cx) ATABLE a HAR TIn
        ltac:(change (req_size ATABLE) with 896; lia))).
(* THE KEEP: a kept byte keeps its view (none of g_nsrc, slot i, the scratch) and its writability *)
assert (KEEP : forall a, rck OB a -> abyte_kept W1 m1 W1 m3 a).
{ intros a Ha. split; [|intros Hw; unfold arm in *; exact (writable_kept (w_H W1) m1 m3 a (PM a) Hw)].
  destruct Ha as [(Himg & Hn) | (p & n & Hin & Hpa)].
  - pose proof (Hsegs a Himg) as Hl. apply KM; [lia | exact Hn | | lia].
    intros Hs. apply (TBIMG a); [unfold rmSA, AENT in *; lia | exact Himg].
  - pose proof (OBIN _ Hin) as Hin'.
    destruct (alx_blocks _ _ _ LAWS ly1 S1 Hp1 W1 m1 md1 p n HAR Hin') as (_ & Hp4096 & Hpceil & _ & _ & _).
    pose proof (BLKN ly1 S1 Hp1 W1 m1 md1 p n HAR Hin') as Hn.
    pose proof (sep_blocks_x SEGS B ARx LAWS ly1 S1 Hp1 W1 m1 md1 p n (rxG0 cx) ATABLE HAR Hin' TIn (OBNE _ Hin)) as Hd.
    unfold zdisjoint in Hd. cbn [fst snd] in Hd. change (req_size ATABLE) with 896 in Hd.
    apply KM; [lia | | | lia].
    + intros Hs. exact (blk_img_x SEGS B ARx LAWS ly1 S1 Hp1 W1 m1 md1 p n a HAR Hin' Hpa (NSIMG a Hs)).
    + unfold rmSA, AENT in *. lia. }
assert (CKZ : forall a, rmc_cells a -> rck OB a)
  by (intros a Ha; left; split; [exact (rmc_cell_img RGP a Ha) | exact (rmc_cell_nnsrc a Ha)]).
assert (AK : forall fp, rcz OB fp -> akept W1 m1 W1 m3 fp)
  by (intros fp Hfp r Hr a Ha; exact (KEEP a (Hfp r Hr a Ha))).
assert (OUTC : rcz OB (aout_fp B RG 0 0)).
{ intros r Hr a Ha. apply CKZ. unfold aout_fp in Hr.
  destruct Hr as [<- | [<- | [<- | [<- | [<- | [<- | [<- | [<- | [<- | Hr]]]]]]]]];
  [cbn [fst snd] in Ha; unfold rmc_cells; tauto .. | simpl in Hr; destruct Hr]. }
(* the table outside slot i *)
assert (TB : forall a, rxG0 cx <= a < rxG0 cx + 896 -> ~ (rmSA cx i <= a < rmSA cx i + AENT) ->
  aview SEGS (w_H W1) m3 a = aview SEGS (w_H W1) m1 a).
{ intros a Ha Hs. apply KM; [lia | intros Hn; exact (TBIMG a Ha (NSIMG a Hn)) | exact Hs | lia]. }
unfold RDONE. split; [|split; [exact Hi|split; [exact Hfd|split; [exact HMO|split; [|split; [|exact HRM]]]]]].
- (* RLIVE *)
  exists fpos. split; [exact HJ3|].
  split; [eapply (ajournal_gx_rom_view_x SEGS B PST ARx LAWS pa_segs_low); [exact HJ3 | exact HROMO | exact PSTR | exact HROM0]|].
  split; [intros a H1 H2 H3 Hp; apply PM; exact (HPK1 a H1 H2 H3 Hp)|].
  split; [|split].
  + (* the frame: the saved registers above sp, the flag cell in F *)
    destruct HFR1 as (EF & EFL & HFL56 & HSV).
    destruct (frames_bounds_x SEGS B ARx LAWS _ _ _ _ _ _ 0 fpos HAR HIN) as (HF4096 & HFceil & _).
    change (fs_frame_bytes 0) with 64 in HFceil. rewrite EF in HF4096, HFceil.
    pose proof (sep_block_frame_x SEGS B ARx LAWS ly1 S1 Hp1 W1 m1 md1 (rxG0 cx) ATABLE 0 fpos HAR TIn HIN) as HdF.
    unfold zdisjoint in HdF. cbn [fst snd] in HdF. change (req_size ATABLE) with 896 in HdF.
    change (fs_frame_bytes 0) with 64 in HdF. rewrite EF in HdF.
    split; [exact EF|]. split; [exact EFL|].
    split.
    * apply (val_mem_kept SEGS (w_H W1) (w_H W1) m1 m3 (F + 56) 8 FL); [|exact HFL56].
      intros k Hk. cbn in Hk. apply KM; [lia | | | lia].
      -- intros Hn. refine (frm_img_x SEGS B ARx LAWS ly1 S1 Hp1 W1 m1 md1 0 fpos _ HAR HIN _ (NSIMG _ Hn)).
         change (fs_frame_bytes 0) with 64. rewrite EF. lia.
      -- unfold rmSA, AENT in *. lia.
    * intros k Hk. apply (val_mem_kept SEGS (w_H W1) (w_H W1) m1 m3 _ 8 _); [|exact (HSV k Hk)].
      intros t Ht. cbn in Ht. apply KM; [lia | | | lia].
      -- intros Hn. pose proof (Hsegs _ (NSIMG _ Hn)). lia.
      -- unfold rmSA, AENT in *. lia.
  + (* g_lock held *)
    eapply alock_at_kept; [exact HLK1|]. apply AK. apply rcz_cons; [|apply rcz_nil]. cbn [fst snd].
    intros a Ha. apply CKZ. unfold rmc_cells. left. exact Ha.
  + eapply awake_at_kept; [exact HWK1|]. apply AK. apply rcz_cons; [|apply rcz_nil]. cbn [fst snd].
    intros a Ha. apply CKZ. unfold rmc_cells. tauto.
- (* g_s as at the entry outside drain's slot j *)
  intros a Ha Hj. apply (rmc_kept_trans _ _ _ _ _ _ a (HGS a Ha Hj)). apply KEEP. apply CKZ. unfold rmc_cells. tauto.
- (* rr_found *)
  unfold rr_found. cbv zeta.
  exists e1, h1, ev, LB, c2, O2, cap2, out2, (rxrest cx).
  split.
  { destruct (re_eof (nth i (rxes cx) relay_remove_b_c.no_entry) =? 0) eqn:Eo.
    - unfold rmdrel, rmopen, rnth in HDR. rewrite Eo in HDR. destruct HDR as (HDR1 & HAS).
      split; [exact HDR1|].
      pose proof (proj1 (HSRC0 i Hi Hfd (proj1 (Z.eqb_eq _ _) Eo))) as Hj4.
      assert (HOBs : forall b, In b (asrc_blks h1) -> In b OB).
      { intros b Hb. unfold OB, rmsrc, rmopen, rnth. rewrite Eo. apply in_or_app. right. apply in_or_app. left. exact Hb. }
      apply (asrc_at_kept B ly1 S1 W1 m1 ly1 S1 W1 m3 _ h1 HAS).
      + apply AK. apply (rcz_asrc OB ly1 S1 W1 m1 _ h1 HAS); [|exact HOBs].
        intros a Ha. apply CKZ. unfold rmc_cells. right. left. unfold rmHA, ASRC in *. lia.
      + intros b Hb. exact (OBIN b (HOBs b Hb)).
    - unfold rmdrel, rmopen, rnth in HDR. rewrite Eo in HDR. exact HDR. }
  split; [exact HSL|].
  split.
  { (* the relay's table after the copy: remove_at i es *)
    assert (HPADS : Forall (fun e => length (re_pad1 e) = 4%nat /\ length (re_pad2 e) = 4%nat) (rxes cx)).
    { eapply Forall_impl; [|exact ROK]. intros e (_ & _ & P1 & P2 & _). split; assumption. }
    pose proof (rm_remove_length (rxes cx) i Hi) as HRL.
    assert (LTpre : length (rmTpre cx i) = (56 * i)%nat).
    { unfold rmTpre. rewrite rrs_concat_len by (apply rmc_forall_firstn; exact HPADS). rewrite length_firstn. lia. }
    assert (LTpost : length (rmTpost cx i) = (56 * (length (rxes cx) - S i))%nat).
    { unfold rmTpost. rewrite rrs_concat_len by (apply rmc_forall_skipn; exact HPADS). rewrite length_skipn. lia. }
    assert (LX : length X = 56%nat) by (unfold AENT in TX; lia).
    set (Bl := rmTpre cx i ++ X ++ rmTpost cx i ++ tail) in Ttab.
    assert (LBl : length Bl = 896%nat).
    { unfold Bl. rewrite !length_app, LTpre, LX, LTpost. unfold rN, ATABLE, AENT in Ttl. lia. }
    set (src := firstn 56 (skipn (56 * (length (rxes cx) - 1)) Bl)).
    assert (Lsrc : length src = 56%nat) by (unfold src; rewrite length_firstn, length_skipn, LBl; lia).
    assert (EQB : firstn (56 * i) Bl ++ src ++ skipn (56 * i + 56) Bl =
                  concat (map entry_bytes (relay_remove_b_c.remove_at i (rxes cx))) ++ src ++ tail)
      by (apply (rmc_block_cpy (rxes cx) tail X src Bl i Hi LX HPADS); reflexivity).
    assert (GNL : garr8 SEGS (arm W1 m3) (rxG0 cx) (bzs (firstn (56 * i) Bl ++ src ++ skipn (56 * i + 56) Bl))).
    { unfold bzs in Ttab |- *. rewrite !map_app. apply garr8_app. split.
      - apply (rmc_garr8_moved W1 W1 m1 m3 (rxG0 cx) (rxG0 cx)).
        + rewrite <- firstn_map. apply rmc_garr8_firstn. exact Ttab.
        + intros j Hj. rewrite length_map, length_firstn in Hj. apply TB; [lia | unfold rmSA, AENT; lia].
      - rewrite length_map, length_firstn, Nat.min_l by lia. apply garr8_app. split.
        + apply (rmc_garr8_moved W1 W1 m1 m3 (rxG0 cx + Z.of_nat (56 * (length (rxes cx) - 1))) _).
          * unfold src. rewrite <- firstn_map, <- skipn_map. apply rmc_garr8_firstn. apply rmc_garr8_skipn;
            [rewrite length_map; lia | exact Ttab].
          * intros j Hj. rewrite length_map, Lsrc in Hj.
            replace (rxG0 cx + Z.of_nat (56 * i) + j) with (rmSA cx i + j) by (unfold rmSA, AENT; lia).
            rewrite (SLM j ltac:(unfold AENT; lia)). f_equal. unfold rN, AENT. lia.
        + rewrite length_map, Lsrc.
          apply (rmc_garr8_moved W1 W1 m1 m3 (rxG0 cx + Z.of_nat (56 * i + 56)) _).
          * rewrite <- skipn_map. apply rmc_garr8_skipn; [rewrite length_map; lia | exact Ttab].
          * intros j Hj. rewrite length_map, length_skipn, LBl in Hj.
            replace (rxG0 cx + Z.of_nat (56 * i) + Z.of_nat 56 + j) with (rxG0 cx + Z.of_nat (56 * i + 56) + j) by lia.
            apply TB; [lia | unfold rmSA, AENT; lia]. }
    split; [apply (akept_vm W1 m1); [intros x Hx; apply KEEP; apply CKZ; unfold rmc_cells; cbn in Hx; tauto | exact Tsrc]|].
    split; [apply (akept_awr W1 m1); [intros x Hx; apply KEEP; apply CKZ; unfold rmc_cells; tauto | exact Tsrcw]|].
    split.
    { rewrite HRL. replace (Z.of_nat (length (rxes cx) - 1)) with (rN cx - 1) by (unfold rN; lia). exact NSM. }
    split; [intros k Hk; unfold arm; exact (writable_kept (w_H W1) m1 m3 _ (PM _) (Tnsrcw k Hk))|].
    split; [apply (akept_vm W1 m1); [intros x Hx; apply KEEP; apply CKZ; unfold rmc_cells; cbn in Hx; tauto | exact Tcap]|].
    split; [apply (akept_awr W1 m1); [intros x Hx; apply KEEP; apply CKZ; unfold rmc_cells; tauto | exact Tcapw]|].
    split; [rewrite HRL; lia|].
    split; [exact TIn|].
    split.
    { exists (src ++ tail). split; [|split].
      - rewrite length_app, Nat2Z.inj_add, Lsrc, Ttl, HRL. unfold rN, ATABLE, AENT. lia.
      - rewrite <- EQB, !length_app, length_firstn, Lsrc, length_skipn, LBl. unfold ATABLE. lia.
      - rewrite <- EQB. exact GNL. }
    split.
    { rewrite Forall_forall in Tok |- *. intros e He.
      assert (HOBe : forall b, In b (aentry_blks e) -> In b OB).
      { intros b Hb. unfold OB, rmOB. apply in_or_app. left. apply in_concat. exists (aentry_blks e).
        split; [apply in_map; exact He | exact Hb]. }
      apply (aentry_ok_kept B ly1 S1 W1 m1 ly1 S1 W1 m3 e (Tok e He)).
      - apply AK. exact (rcz_aentry OB ly1 S1 W1 m1 e (Tok e He) HOBe).
      - intros b Hb. exact (OBIN b (HOBe b Hb)). }
    split.
    { apply (proj2 (stdpp.base.NoDup_ListNoDup _)). apply rmc_nodup_remove; [exact Hi|].
      exact (proj1 (stdpp.base.NoDup_ListNoDup _) RND). }
    (* no entry's block is the table (arelay_at's twelfth conjunct, W8 42f5184c7ab): MatchCx's rm_base_notab *)
    exact (rm_base_notab B ARx MT RP MMAX RG cx i HB Hi). }
  split.
  { apply (aout_at_kept B RG ly1 S1 W1 m1 ly1 S1 W1 m3 _ _ _ _ _ _ HOUT).
    - apply AK. apply (rcz_aout OB ly1 S1 W1 m1 _ _ _ _ _ _ HOUT OUTC).
      intros b Hb. unfold OB. apply in_or_app. right. apply in_or_app. right. apply in_or_app. left. exact Hb.
    - intros b Hb. apply OBIN. unfold OB. apply in_or_app. right. apply in_or_app. right. apply in_or_app. left. exact Hb. }
  split.
  { rewrite (rm_drains cx i (proj1 (stdpp.base.NoDup_ListNoDup _) RND) HFD0 Hi Hfd) in HPERM0. exact HPERM0. }
  exact HPERM.
Qed.

Theorem rr_m_cpy : hop_cpy_stmt B PST ARx MT RP MMAX RG.
Proof.
unfold hop_cpy_stmt. intros cx i W1 c1 HB HC KU.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof pa_segs_low as Hsegs.
destruct HC as (regs1 & ly1 & S1 & Hp1 & m1 & md1 & k1 & F & FL & e1 & h1 & ev & LB & c2 & O2 & cap2 & out2 & X &
  -> & HMH & HLV & HDR & HTB & HSL & HOUT & HPERM & HGS & HMO & HRM).
pose proof HB as (HPRE & _ & _ & RGP & _ & _ & _ & _ & HREL0 & _ & HROM0 & _).
pose proof RGP as (_ & RGNSRC & RGSRC & _ & _ & _ & RGIMG & _ & _).
destruct HMH as (HRH & H25 & H24 & HFD0 & Hi & Hfd).
pose proof HRH as ((Hsp1 & H3 & H4 & _ & _ & _ & _ & _ & H22 & _ & _) & _ & H23).
pose proof HLV as (fpos & HJ & _ & HPK1 & HFR1 & HLK1 & HWK1).
pose proof HTB as (Tsrc & _ & Tnsrc & Tnsrcw & _ & _ & TIn & _ & _ & _ & _).
pose proof HREL0 as (_ & _ & _ & _ & _ & _ & Rlen16 & _).
assert (HAR : ARx ly1 S1 Hp1 W1 m1 md1) by (eapply ajournal_gx_AR_x; exact HJ).
destruct (alx_blocks _ _ _ LAWS ly1 S1 Hp1 W1 m1 md1 (rxG0 cx) ATABLE HAR TIn) as (HG16 & HG4096 & HGceil & HGapp & HGpres & _).
change (req_size ATABLE) with 896 in HGceil, HGapp, HGpres.
assert (HN : 1 <= rN cx <= 16) by (unfold rN; lia).
remember (Eimg (Ereg regs1 (rmc_extra (rxG0 cx) (rN cx)))) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (HAE : env_agree 32 (Ereg regs1 (rmc_extra (rxG0 cx) (rN cx))) E)
by (rewrite HE; split; [intros m Hm; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
assert (EEo : forall m (rr : bv 5), Z.of_nat m = bv_unsigned rr -> ew E m = getr regs1 rr)
by (intros m rr Hm; subst E; pose proof (bv_unsigned_in_range 5 rr) as Hr5; change (bv_modulus 5) with 32 in Hr5;
rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_nat; exact Hm).
assert (E32 : ew E 32 = Z_to_bv 64 (rxG0 cx))
by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 (rN cx))
by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 _ 1)).
assert (E22 : ew E 22 = Z_to_bv 64 SHADOW_OFF) by (rewrite (EEo 22%nat 22%bv eq_refl); exact H22).
assert (E24 : ew E 24 = Z_to_bv 64 (AENT * Z.of_nat i)) by (rewrite (EEo 24%nat 24%bv eq_refl); exact H24).
assert (UV : forall n, (A_TEXT <= n < A_LIM)%nat -> bv_unsigned (ew E n) = VAL n).
{ intros n Hn. subst E. rewrite Eimg_img by exact Hn. apply unsigned_lit_small. apply pa_val_range. }
pose proof (pa_obj_img 7 ltac:(lia)) as Q7. pose proof (pa_obj_img 8 ltac:(lia)) as Q8.
assert (HS : st_ok_pi SEGS VAL E ss_rmc (restrict (w_H W1) (mkst regs1 (Z_to_bv 64 (BASE + A_rr_cpy)) m1 (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. unfold ss_rmc. apply pa_entry_st_ok_full.
- unfold rmc_sr.
  apply regs_ok_pin; [| intros X0; discriminate X0 |].
  2:{ cbn [sv_denot]. rewrite (UV (A_HI 60)) by (unfold A_HI, A_TEXT, A_LIM; lia). rewrite Z.add_0_r, HH60. exact H25. }
  apply regs_ok_pin; [| intros X0; discriminate X0 |].
  2:{ cbn [sv_denot]. rewrite (UV (A_HI 59)) by (unfold A_HI, A_TEXT, A_LIM; lia). rewrite Z.add_0_r, HH59. exact H23. }
  rewrite HE. apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- repeat apply Forall_cons; try apply Forall_nil; unfold region_ok, rmc_src, rmc_nsrc;
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
  + rewrite (UV (A_OBJ 8)) by (unfold A_OBJ, A_TEXT, A_LIM; lia). rewrite <- RGSRC.
    split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    repeat apply Forall_cons; try apply Forall_nil.
    apply (chunk_ok_val SEGS E _ (rg_src RG) 0 8 (SOff 32 0) (rxG0 cx));
    [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
    rewrite Z.add_0_r. exact Tsrc.
  + rewrite (UV (A_OBJ 7)) by (unfold A_OBJ, A_TEXT, A_LIM; lia). rewrite <- RGNSRC.
    split; [lia|]. split; [lia|]. split; [intros o Ho; apply Tnsrcw; lia|].
    repeat apply Forall_cons; try apply Forall_nil.
    apply (chunk_ok_val SEGS E _ (rg_nsrc RG) 0 4 (SOff 33 0) (rN cx));
    [cbn [sv_denot]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
    rewrite Z.add_0_r. exact Tnsrc.
- apply pairwise_disjoint_of_extents. unfold rmc_src, rmc_nsrc, extent_of_region.
  cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val].
  rewrite (UV (A_OBJ 8)), (UV (A_OBJ 7)) by (unfold A_OBJ, A_TEXT, A_LIM; lia). rewrite <- RGSRC, <- RGNSRC.
  pose proof HRGP as HP. cbn [zpairwise_disjoint zall_disjoint] in HP. unfold zdisj in HP. cbn [fst snd] in HP.
  destruct HP as (_ & _ & (D23 & _) & _).
  cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. repeat split; try exact I; lia.
- split; [|split; [exact I | exact I]].
  cbn [rmc_facts f_atoms atoms_ok]. unfold afact_ok, rmc_OBJF, rmc_HIF. cbn [af_lo af_hi af_al2].
  rewrite E22, E24, E32, E33.
  rewrite (UV (A_OBJ 7)), (UV (A_OBJ 8)), (UV (A_HI 59)) by (unfold A_OBJ, A_HI, A_TEXT, A_LIM; lia).
  rewrite HH59. rewrite <- RGNSRC in Q7. unfold RR_HI_NSRC.
  rewrite !unsigned_lit_small by (unfold SHADOW_OFF, AENT, rN in *; lia).
  change (2 ^ 4) with 16. rewrite !Z.pow_0_r, !Z.mod_1_r.
  unfold SB, SHADOW_OFF, AENT in *. repeat match goal with |- _ /\ _ => split end; try lia; try exact I. }
clear HE.
assert (SHOK : sh_ok SEGS rmc_Bx [] E (mrestrict (w_H W1) m1)) by constructor.
unfold cfg_at. change (w64 (BASE + A_rr_cpy)) with (Z_to_bv 64 (BASE + A_rr_cpy)).
(* 0x83f98 .. 0x83fa4: the loads of g_src and g_nsrc, a0 = &g_src[i], a2 = N - 1; stop at the store 0x83fa8 *)
paj_run_to_tok_x RUNTO HS HJ SHOK rmc_Bspan (AF_fr_relay_remove + 0x1c4).
{ apply awr_ok_x_cons; [intros a Ha; cbn in Ha; lia|].
  apply awr_ok_x_cons_g; [|apply awr_ok_x_nil].
  intros a Ha. cbn [rmc_nsrc YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha.
  rewrite (UV (A_OBJ 7)) in Ha by (unfold A_OBJ, A_TEXT, A_LIM; lia). rewrite <- RGNSRC in Ha.
  unfold inG, G_RR. apply Exists_cons_tl. apply Exists_cons_hd. unfold in_zr. cbn [fst snd]. lia. }
rename HFr into HFr1, HG0 into HGr1. clear HF.
lazymatch goal with |- SRr _ _ (mkCfg ?mm _) _ => rename mm into ms1 end.
clear HEI0.
assert (HREL : VAL (A_OBJ 7) = VAL (A_HI 59) + -1864) by (rewrite HH59, <- RGNSRC; unfold RR_HI_NSRC; lia).
prebase HS 1%nat (A_HI 59) (-1864) HREL.
(* 0x83fa8 .. 0x83fc0: g_nsrc = N - 1 (through s7 = A_HI 59), a1 = &g_src[N - 1], a2 = 56; the call *)
paj_run_tok_x RUN HS HJ SHOK rmc_Bspan.
{ apply awr_ok_x_cons; [intros a Ha; cbn in Ha; lia|].
  apply awr_ok_x_cons_g; [|apply awr_ok_x_nil].
  intros a Ha. cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha.
  match goal with HE : img_env _ _ ?Ex |- _ => rewrite (HE 339%nat ltac:(unfold A_TEXT, A_LIM; lia)) in Ha end.
  change 339%nat with (A_HI 59) in Ha. rewrite HH59 in Ha. unfold RR_HI_NSRC in Ha.
  unfold inG, G_RR. apply Exists_cons_tl. apply Exists_cons_hd. unfold in_zr. cbn [fst snd]. lia. }
rename HFr into HFr2, HG0 into HGr2. clear HF.
lazymatch goal with |- SRr _ _ (mkCfg ?mm _) _ => rename mm into ms2 end.
pose proof (st_ok_region_nth _ _ _ 1 _ HS eq_refl) as HRN. cbn [ms_mem restrict] in HRN.
pose proof (regs_kept_of_st_ok SEGS _ _ _ regs1 _ RMC_KEPT HS HAE ltac:(vm_compute; reflexivity)) as K2.
cbn [ms_regs restrict] in K2.
pmkst HS.
prreg HS (1%bv : bv 5) P1. prreg HS (10%bv : bv 5) P10. prreg HS (11%bv : bv 5) P11. prreg HS (12%bv : bv 5) P12.
(* ---- the state at the call: what the two runs changed (g_nsrc), the registers ---- *)
pose proof HPRE as (_ & _ & _ & Hgp & Htp & Hstk & _).
pose proof Hstk as (_ & _ & Hceil & Hslo & Hshi & H47 & _).
assert (WS : RR_STK_x = 17072) by reflexivity. assert (WF : RR_FRAME = 96) by reflexivity.
assert (Hes : ESTACK = 4096) by reflexivity.
fold (rsp0 cx) in Hslo, Hshi.
assert (HSC : alloc_ceiling <= rsp0 cx - RR_FRAME - ESTACK) by lia.
pose proof HJ as HAR2. eapply ajournal_gx_AR_x in HAR2.
assert (KR : forall a, 0 <= a < 2 ^ 64 -> ~ (rg_nsrc RG <= a < rg_nsrc RG + 4) ->
  aview SEGS (w_H W1) (ms_mem ms2) a = aview SEGS (w_H W1) m1 a).
{ intros a Ha Hn.
  rewrite (aview_kept_out _ _ (w_H W1) (ms_mem ms1) (ms_mem ms2) HFr2 a Ha).
  2:{ intros (r & Hin & Hr).
      lazymatch type of Hin with In _ ?rs => let rs' := eval vm_compute in rs in change (In r rs') in Hin end.
      cbn [In] in Hin. destruct Hin as [<- | [<- | []]]; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr; [lia|].
      rewrite (HEI 339%nat ltac:(unfold A_TEXT, A_LIM; lia)) in Hr. change 339%nat with (A_HI 59) in Hr.
      rewrite HH59 in Hr. unfold RR_HI_NSRC in Hr. lia. }
  apply (aview_kept_out _ _ (w_H W1) m1 (ms_mem ms1) HFr1 a Ha).
  intros (r & Hin & Hr).
  lazymatch type of Hin with In _ ?rs => let rs' := eval vm_compute in rs in change (In r rs') in Hin end.
  cbn [In] in Hin. destruct Hin as [<- | [<- | []]]; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr; [lia|].
  rewrite (HEI 248%nat ltac:(unfold A_TEXT, A_LIM; lia)) in Hr. change 248%nat with (A_OBJ 7) in Hr.
  rewrite <- RGNSRC in Hr. lia. }
assert (PR : forall a, apresent (w_H W1) m1 a -> apresent (w_H W1) (ms_mem ms2) a)
  by (intros a Ha; exact (apresent_grows _ _ _ a HGr2 (apresent_grows _ _ _ a HGr1 Ha))).
assert (NS2 : val_mem SEGS (mrestrict (w_H W1) (ms_mem ms2)) (rg_nsrc RG) 4 (rN cx - 1)).
{ replace (rg_nsrc RG) with (VAL (A_HI 59) + -1864) by (rewrite HH59; unfold RR_HI_NSRC; lia).
  change 4%nat with (N.to_nat 4).
  apply (field_of_region E _ 339%nat _ _ _ _ _ _ (-1864) 4 (SOff 33 (-1)) (rN cx - 1) HRN).
  - exact (HEI 339%nat ltac:(unfold A_TEXT, A_LIM; lia)).
  - left. reflexivity.
  - cbn [sv_denot]. rewrite E33, unsigned_lit_small by lia. reflexivity.
  - cbn. lia.
  - cbn. lia. }
assert (SP2 : spZ (ms_regs ms2) = rsp0 cx - RR_FRAME).
{ unfold spZ. rewrite (K2 2%bv ltac:(cbn; tauto)). exact Hsp1. }
assert (A10 : getr (ms_regs ms2) 10 = w64 (rmSA cx i)).
{ rewrite P10, E24, E32, YI08.alu64_add_lit. unfold w64, rmSA. f_equal. lia. }
assert (A11 : getr (ms_regs ms2) 11 = w64 (rxG0 cx + AENT * (rN cx - 1))).
{ rewrite P11, E32, E33, unsigned_lit_small by lia.
  assert (M : mul_div M_MUL (Z_to_bv 64 (rN cx)) (Z_to_bv 64 56) = Z_to_bv 64 (rN cx * 56)).
  { apply bv_eq. rewrite mul_div_unsigned, !unsigned_lit_small by lia. cbn [zmd_raw].
    unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64). apply Z.mod_small. lia. }
  rewrite M, YI08.alu64_add_lit. unfold w64, AENT. f_equal. lia. }
assert (HSLOT : forall a, rmSA cx i <= a < rmSA cx i + AENT -> rxG0 cx <= a < rxG0 cx + 896)
  by (intros a Ha; unfold rmSA, AENT in *; lia).
assert (HLAST : forall a, rxG0 cx + AENT * (rN cx - 1) <= a < rxG0 cx + AENT * (rN cx - 1) + AENT ->
  rxG0 cx <= a < rxG0 cx + 896) by (intros a Ha; unfold AENT in *; lia).
(* ---- __asan_memcpy (&g_src[i], &g_src[N - 1], 56) ---- *)
eapply SRr_bind.
{ eapply (aj_gx_entry_at_x B PST ARx LAWS (G_RR B RG) 0 [] ESTACK (SIGMA WS_asan_memcpy)
    (fun a => rmSA cx i <= a < rmSA cx i + AENT)
    (fun (regs' : bvmap 5 word) (mem' : word -> option byte) => forall t, 0 <= t < AENT ->
       aview SEGS (w_H W1) mem' (rmSA cx i + t) = aview SEGS (w_H W1) (ms_mem ms2) (rxG0 cx + AENT * (rN cx - 1) + t))
    W1 _ _ RR_STK_x (rsp0 cx) (rFP cx) (rxly cx) (rxS cx) (rxHp cx) (rxW cx) (rxmem cx) (rxmd cx) _ _ _ _ _ _ (-96) _ HG eq_refl
    HJ).
  - rewrite SP2, WF. lia.
  - reflexivity.
  - lia.
  - lia.
  - rewrite WS, Hes. lia.
  - rewrite (K2 3%bv ltac:(cbn; tauto)), H3. exact Hgp.
  - rewrite (K2 4%bv ltac:(cbn; tauto)), H4. exact Htp.
  - exact P1.
  - apply ret_ok_codeptr_v; [lia | reflexivity].
  - intros a. destruct (Z_lt_ge_dec a (rmSA cx i)); [right; lia|].
    destruct (Z_lt_ge_dec a (rmSA cx i + AENT)); [left; lia | right; lia].
  - intros a Ha HGa. exfalso. destruct (HG a HGa) as [Himg _].
    refine (blk_img_x SEGS B ARx LAWS ly1 S1 Hp1 W1 (ms_mem ms2) _ (rxG0 cx) ATABLE a HAR2 TIn _ Himg).
    change (req_size ATABLE) with 896. exact (HSLOT a Ha).
  - intros a Ha _. split; [|lia].
    right. left. split.
    + unfold rFP, rr_fp. replace a with (rxG0 cx + (a - rxG0 cx)) by lia.
      apply (inFP_ablocks_fp _ (rxG0 cx) ATABLE); [left; reflexivity | change (req_size ATABLE) with 896; pose proof (HSLOT a Ha); lia].
    + exists (rxG0 cx), ATABLE. split; [exact TIn|]. change (req_size ATABLE) with 896. exact (HSLOT a Ha).
  - intros HPRE2 _.
    assert (DEST : dest_ok SEGS B ly1 S1 W1 (ms_regs ms2) (ms_mem ms2) (rmSA cx i) AENT).
    { intros a Ha. destruct (HGpres a (HSLOT a Ha)) as [Hp Hno].
      split; [apply (apresent_writable SEGS); exact (PR a Hp)|]. split; [exact Hno|].
      rewrite SP2. pose proof (HSLOT a Ha). lia. }
    assert (CHK : forall x, rxG0 cx <= x -> x + AENT <= rxG0 cx + 896 -> achecked W1 (ms_mem ms2) x AENT).
    { intros x Hx1 Hx2. split; [|split].
      - eapply (YCe5x.amem_range_of_block_x SEGS B ARx LAWS ly1 S1 Hp1 W1 (ms_mem ms2) _ (rxG0 cx) ATABLE);
        [exact HAR2 | exact TIn | lia |].
        change (req_size ATABLE) with 896. lia.
      - eapply (range_addressable_of_block_hp0_x SEGS B ARx LAWS HP0 ly1 S1 Hp1 W1 (ms_mem ms2) _ (rxG0 cx) ATABLE);
        [exact HAR2 | exact TIn | lia |].
        change (req_size ATABLE) with 896. lia.
      - intros Hpos. eapply (shadow_hull_vis_of_block_hp0_x SEGS B ARx LAWS HP0 ly1 S1 Hp1 W1 (ms_mem ms2) _ (rxG0 cx) ATABLE);
        [exact HAR2 | exact TIn | lia | change (req_size ATABLE) with 896; lia | exact Hpos]. }
    assert (SRC : src_ok SEGS W1 (ms_regs ms2) (ms_mem ms2) (rxG0 cx + AENT * (rN cx - 1)) AENT).
    { intros a Ha. split; [apply aview_some_of_apresent; exact (PR a (proj1 (HGpres a (HLAST a Ha))))|].
      rewrite SP2. pose proof (HLAST a Ha). lia. }
    destruct (Nat.lt_ge_cases (S i) (length (rxes cx))) as [Hlt | Hge].
    + (* i < N - 1: the copy of slot N - 1 (disjoint) *)
      destruct (CHK (rmSA cx i) ltac:(unfold rmSA, AENT; lia) ltac:(unfold rmSA, AENT; lia)) as (Cd1 & Cd2 & Cd3).
      destruct (CHK (rxG0 cx + AENT * (rN cx - 1)) ltac:(unfold AENT; lia) ltac:(unfold AENT; lia)) as (Cs1 & Cs2 & Cs3).
      eapply SRr_mono.
      { apply (AMEMCPY ly1 S1 Hp1 W1 (ms_regs ms2) (ms_mem ms2) _ (rmSA cx i) (rxG0 cx + AENT * (rN cx - 1)) AENT HPRE2
          A10 A11 P12); try (unfold rmSA, AENT; lia); [exact DEST | exact Cd1 | | exact Cd2 | exact Cd3 |].
        1: { intros a Ha. apply kept_x_off_img. exact (blk_img_x SEGS B ARx LAWS ly1 S1 Hp1 W1 (ms_mem ms2) _ (rxG0 cx) ATABLE a
               HAR2 TIn ltac:(change (req_size ATABLE) with 896; exact (HSLOT a Ha))). }
        split; [unfold AENT; lia|]. split; [unfold AENT; lia|]. split; [exact SRC|].
        split; [unfold rmSA, rN, AENT in *; lia|]. split; [exact Cs1|]. split; [exact Cs2 | exact Cs3]. }
      cbv beta. intros W4 c4 _ (-> & regs4 & mem4 & md4 & -> & HAR4 & HP4 & Hsm4 & _ & Hcp4 & Hfr4 & Hpr4).
      split; [reflexivity|]. exists regs4, mem4, md4.
      split; [reflexivity|]. split; [exact HAR4|]. split; [exact HP4|]. split; [exact Hsm4|].
      split; [exact Hcp4|]. split; [exact Hfr4 | exact Hpr4].
    + (* i = N - 1: onto itself *)
      assert (EL : rxG0 cx + AENT * (rN cx - 1) = rmSA cx i) by (unfold rmSA, rN, AENT; lia).
      rewrite EL in A11.
      eapply SRr_mono.
      { apply (AMEMCPYS ly1 S1 Hp1 W1 (ms_regs ms2) (ms_mem ms2) _ (rmSA cx i) AENT HPRE2 A10 A11 P12);
          try (unfold rmSA, AENT; lia); [exact DEST | rewrite <- EL; exact SRC | apply CHK; unfold rmSA, AENT; lia | | | ].
        - eapply (ajournal_gx_rom_view_x SEGS B PST ARx LAWS pa_segs_low); [exact HJ | exact HROMO | exact PSTR | exact HROM0].
        - intros _. eapply (YCe5x.amem_range_of_block_x SEGS B ARx LAWS ly1 S1 Hp1 W1 (ms_mem ms2) _ (rxG0 cx) ATABLE);
          [exact HAR2 | exact TIn | unfold rmSA, AENT; lia | change (req_size ATABLE) with 896; unfold rmSA, AENT; lia].
        - intros a Ha. exact (blk_img_x SEGS B ARx LAWS ly1 S1 Hp1 W1 (ms_mem ms2) _ (rxG0 cx) ATABLE a HAR2 TIn
            ltac:(change (req_size ATABLE) with 896; exact (HSLOT a Ha))). }
      cbv beta. intros W4 c4 _ (-> & regs4 & mem4 & md4 & -> & HAR4 & HP4 & Hsm4 & _ & Hfr4 & Hpr4).
      split; [reflexivity|]. exists regs4, mem4, md4.
      split; [reflexivity|]. split; [exact HAR4|]. split; [exact HP4|]. split; [exact Hsm4|].
      split; [|split; [intros a Ha _ Hsc; exact (Hfr4 a Ha (fun x => x) Hsc) | exact Hpr4]].
      intros t Ht. rewrite EL. apply Hfr4; [unfold rmSA, AENT in *; lia | intros x; exact x |].
      rewrite SP2. unfold rmSA, AENT in *. lia. }
cbv beta. intros W3 c3 _ (-> & regs3 & mem3 & md3 & -> & HJ3 & HP3 & HPr3 & Hfr3 & Hpres3).
(* ---- back at 0x83fc4: RRU (Some i) ---- *)
assert (K3 : forall r : bv 5, In r RMC_KEPT -> getr regs3 r = getr regs1 r).
{ intros r Hr. rewrite <- (K2 r Hr). rewrite <- (Z_to_bv_bv_unsigned 5 r). apply HP3.
  unfold RMC_KEPT in Hr.
  repeat (destruct Hr as [<- | Hr]; [unfold acallee_saved;
    lazymatch goal with |- context [bv_unsigned ?b] => let v := eval vm_compute in (bv_unsigned b) in
      change (bv_unsigned b) with v end; lia|]).
  destruct Hr. }
apply KU. exists regs3, ly1, S1, Hp1, mem3, md3, k1, F, FL.
split; [reflexivity|].
split; [unfold rregs_base, spZ; rewrite !K3 by (cbn; tauto); exact (proj1 HRH)|].
split; [exact HFD0|].
apply (rmc_post cx i ly1 S1 Hp1 W1 m1 md1 k1 F FL e1 h1 ev LB c2 O2 cap2 out2 X fpos mem3 md3 HB HFD0 Hi Hfd HAR HPK1
  HFR1 HLK1 HWK1 HDR HTB HSL HOUT HPERM HGS HMO HRM).
- intros a Ha Hn Hs Hsc. rewrite (Hfr3 a Ha Hs ltac:(rewrite WF in Hsc; lia)). exact (KR a Ha Hn).
- intros a Hp. exact (Hpres3 a (PR a Hp)).
- apply (val_mem_kept SEGS (w_H W1) (w_H W1) (ms_mem ms2) mem3 (rg_nsrc RG) 4 (rN cx - 1)); [|exact NS2].
  intros k Hk. apply Hfr3.
  + pose proof (Hsegs (rg_nsrc RG + k) ltac:(apply RGIMG; unfold rg_rng; cbn in Hk; lia)). lia.
  + intros Hs. refine (blk_img_x SEGS B ARx LAWS ly1 S1 Hp1 W1 m1 md1 (rxG0 cx) ATABLE _ HAR TIn _
      (proj1 (RGIMG (rg_nsrc RG + k) ltac:(unfold rg_rng; cbn in Hk; lia)))).
    change (req_size ATABLE) with 896. exact (HSLOT _ Hs).
  + pose proof (Hsegs (rg_nsrc RG + k) ltac:(apply RGIMG; unfold rg_rng; cbn in Hk; lia)). lia.
- intros t Ht. rewrite (HPr3 t Ht). apply KR; [unfold AENT in *; lia|].
  intros Hn. refine (blk_img_x SEGS B ARx LAWS ly1 S1 Hp1 W1 m1 md1 (rxG0 cx) ATABLE _ HAR TIn _
    (proj1 (RGIMG (rxG0 cx + AENT * (rN cx - 1) + t) ltac:(unfold rg_rng; lia)))).
  change (req_size ATABLE) with 896. unfold AENT in *. lia.
- exact HJ3.
Qed.


(* ---- route R: the R twin of each piece of Section c whose statement names the journal, SRr, a
   carrier or a statement: the strict text with the journal and SRr at R and each carrier / statement / callee
   spec / engine lemma at its R twin. The strict text above is unchanged. ---- *)
Section wR.
Variable R : world SEGS -> world SEGS -> Prop.
Hypothesis R_refl : forall W, R W W.
Hypothesis R_trans : forall W1 W2 W3, R W1 W2 -> R W2 W3 -> R W1 W3.
Hypothesis WLE_R : forall W W', @wle SEGS W W' -> R W W'.
Let RUNR := paj_run_x_xG B PST ARx LAWS R (G_RR B RG) HG 0 [].
Let RUNTOR := paj_run_to_x_xG B PST ARx LAWS R (G_RR B RG) HG 0 [].

Lemma rmc_post_xR : forall cx i ly1 S1 Hp1 W1 m1 md1 k1 F FL e1 h1 ev LB c2 O2 cap2 out2 X fpos m3 md3,
RBASE B ARx MT RP MMAX RG cx ->
0 <= rxFD cx -> (i < length (rxes cx))%nat -> re_fd (rnth cx i) = rxFD cx ->
ARx ly1 S1 Hp1 W1 m1 md1 ->
apres_kept B (rxW cx) (rxmem cx) W1 m1 -> rr_frame cx fpos F FL ly1 W1 m1 ->
alock_at RG W1 m1 true -> awake_at RG W1 m1 ->
rmdrel B RG cx i ly1 S1 W1 m1 e1 h1 LB ->
rmtbl B RG cx i ly1 S1 W1 m1 X ->
sl_sends (rxmx cx) (rmc1 cx i ev) (rmO1 cx i LB) (rmcap1 cx i) (ge_bytes (re_keys e1)) = (c2, O2, cap2) ->
aout_at B RG ly1 S1 W1 m1 c2 O2 (rxmx cx) (Z.of_nat (length O2)) cap2 out2 ->
Permutation (ablocks B ly1 S1)
  ((rxG0 cx, ATABLE) :: rmOB cx i ++ rmsrc cx i h1 ++ aout_blks cap2 out2 ++ rxrest cx) ->
rmgs RG cx W1 m1 ->
mo_le MT (rxS cx) S1 (tr_cost MT (rtr cx)) ->
rp_RM RP S1 (rxkr cx) ->
(forall a, 0 <= a < 2 ^ 64 -> ~ (rg_nsrc RG <= a < rg_nsrc RG + 4) -> ~ (rmSA cx i <= a < rmSA cx i + AENT) ->
   ~ (rsp0 cx - RR_FRAME - ESTACK <= a < rsp0 cx - RR_FRAME) ->
   aview SEGS (w_H W1) m3 a = aview SEGS (w_H W1) m1 a) ->
(forall a, apresent (w_H W1) m1 a -> apresent (w_H W1) m3 a) ->
val_mem SEGS (arm W1 m3) (rg_nsrc RG) 4 (rN cx - 1) ->
(forall t, 0 <= t < AENT ->
   aview SEGS (w_H W1) m3 (rmSA cx i + t) = aview SEGS (w_H W1) m1 (rxG0 cx + AENT * (rN cx - 1) + t)) ->
ajournal_gx_xR (SK := SK) SEGS B PST ARx R (G_RR B RG) 0 [] RR_STK_x (rsp0 cx) (rFP cx)
  (rxly cx) (rxS cx) (rxHp cx) (rxW cx) (rxmem cx) (rxmd cx) [(0, fpos)] ly1 S1 Hp1 W1 m3 md3 k1 ->
RDONE_xR B PST ARx MT RP RG R cx i F FL ly1 S1 Hp1 W1 m3 md3 k1.
Proof.
intros cx i ly1 S1 Hp1 W1 m1 md1 k1 F FL e1 h1 ev LB c2 O2 cap2 out2 X fpos m3 md3
  HB HFD0 Hi Hfd HAR HPK1 HFR1 HLK1 HWK1 HDR HTB HSL HOUT HPERM HGS HMO HRM KM PM NSM SLM HJ3.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof pa_segs_low as Hsegs.
pose proof HB as (HPRE & _ & _ & RGP & _ & _ & _ & _ & HREL0 & _ & HROM0 & HSRC0 & HPERM0 & _).
pose proof RGP as (_ & _ & _ & _ & _ & _ & RGIMG & _ & _).
pose proof HPRE as (_ & _ & _ & _ & _ & Hstk & _).
pose proof Hstk as (_ & _ & Hceil & Hslo & Hshi & H47 & _).
assert (WS : RR_STK_x = 17072) by reflexivity. assert (WF : RR_FRAME = 96) by reflexivity.
assert (Hes : ESTACK = 4096) by reflexivity.
fold (rsp0 cx) in Hslo, Hshi.
assert (HSC : alloc_ceiling <= rsp0 cx - RR_FRAME - ESTACK) by lia.
assert (HSP : rsp0 cx <= 2 ^ 47) by lia.
clear Hceil Hslo Hshi H47 Hstk HPRE.
pose proof HTB as (Tsrc & Tsrcw & Tnsrc & Tnsrcw & Tcap & Tcapw & TIn & TX & (tail & Ttl & Ttab) & Tslw & Tok).
pose proof HREL0 as (_ & _ & _ & _ & _ & _ & Rlen16 & _ & _ & ROK & RND & _).
destruct (alx_blocks _ _ _ LAWS ly1 S1 Hp1 W1 m1 md1 (rxG0 cx) ATABLE HAR TIn) as (HG16 & HG4096 & HGceil & _ & _ & _).
change (req_size ATABLE) with 896 in HGceil.
assert (HN : 1 <= rN cx <= 16) by (unfold rN; lia).
assert (HIN : In (0, fpos) (frames S1)).
{ pose proof HJ3 as (_ & _ & (memS & HJd & _) & _). pose proof HJd as (_ & _ & _ & _ & _ & Hfrs & _).
  rewrite Hfrs. left. reflexivity. }
(* the other blocks: live, apart from the table *)
set (OB := rmOB cx i ++ rmsrc cx i h1 ++ aout_blks cap2 out2 ++ rxrest cx).
assert (OBIN : forall b, In b OB -> In b (ablocks B ly1 S1))
  by (intros b Hb; apply (Permutation_in _ (Permutation_sym HPERM)); right; exact Hb).
assert (OBNE : forall b, In b OB -> b <> (rxG0 cx, ATABLE)).
{ intros b Hb Eb. pose proof (W_gestures_end.gse_nodup_x B ARx LAWS BLKN ly1 S1 Hp1 W1 m1 md1 HAR) as ND.
  apply (Permutation_NoDup HPERM) in ND. apply List.NoDup_cons_iff in ND as [Hni _]. apply Hni. rewrite <- Eb. exact Hb. }
assert (NSIMG : forall a, rg_nsrc RG <= a < rg_nsrc RG + 4 -> in_img SEGS a)
  by (intros a Ha; apply RGIMG; unfold rg_rng; tauto).
assert (TBIMG : forall a, rxG0 cx <= a < rxG0 cx + 896 -> ~ in_img SEGS a)
  by (intros a Ha; exact (blk_img_x SEGS B ARx LAWS ly1 S1 Hp1 W1 m1 md1 (rxG0 cx) ATABLE a HAR TIn
        ltac:(change (req_size ATABLE) with 896; lia))).
(* THE KEEP: a kept byte keeps its view (none of g_nsrc, slot i, the scratch) and its writability *)
assert (KEEP : forall a, rck OB a -> abyte_kept W1 m1 W1 m3 a).
{ intros a Ha. split; [|intros Hw; unfold arm in *; exact (writable_kept (w_H W1) m1 m3 a (PM a) Hw)].
  destruct Ha as [(Himg & Hn) | (p & n & Hin & Hpa)].
  - pose proof (Hsegs a Himg) as Hl. apply KM; [lia | exact Hn | | lia].
    intros Hs. apply (TBIMG a); [unfold rmSA, AENT in *; lia | exact Himg].
  - pose proof (OBIN _ Hin) as Hin'.
    destruct (alx_blocks _ _ _ LAWS ly1 S1 Hp1 W1 m1 md1 p n HAR Hin') as (_ & Hp4096 & Hpceil & _ & _ & _).
    pose proof (BLKN ly1 S1 Hp1 W1 m1 md1 p n HAR Hin') as Hn.
    pose proof (sep_blocks_x SEGS B ARx LAWS ly1 S1 Hp1 W1 m1 md1 p n (rxG0 cx) ATABLE HAR Hin' TIn (OBNE _ Hin)) as Hd.
    unfold zdisjoint in Hd. cbn [fst snd] in Hd. change (req_size ATABLE) with 896 in Hd.
    apply KM; [lia | | | lia].
    + intros Hs. exact (blk_img_x SEGS B ARx LAWS ly1 S1 Hp1 W1 m1 md1 p n a HAR Hin' Hpa (NSIMG a Hs)).
    + unfold rmSA, AENT in *. lia. }
assert (CKZ : forall a, rmc_cells a -> rck OB a)
  by (intros a Ha; left; split; [exact (rmc_cell_img RGP a Ha) | exact (rmc_cell_nnsrc a Ha)]).
assert (AK : forall fp, rcz OB fp -> akept W1 m1 W1 m3 fp)
  by (intros fp Hfp r Hr a Ha; exact (KEEP a (Hfp r Hr a Ha))).
assert (OUTC : rcz OB (aout_fp B RG 0 0)).
{ intros r Hr a Ha. apply CKZ. unfold aout_fp in Hr.
  destruct Hr as [<- | [<- | [<- | [<- | [<- | [<- | [<- | [<- | [<- | Hr]]]]]]]]];
  [cbn [fst snd] in Ha; unfold rmc_cells; tauto .. | simpl in Hr; destruct Hr]. }
(* the table outside slot i *)
assert (TB : forall a, rxG0 cx <= a < rxG0 cx + 896 -> ~ (rmSA cx i <= a < rmSA cx i + AENT) ->
  aview SEGS (w_H W1) m3 a = aview SEGS (w_H W1) m1 a).
{ intros a Ha Hs. apply KM; [lia | intros Hn; exact (TBIMG a Ha (NSIMG a Hn)) | exact Hs | lia]. }
unfold RDONE_xR. split; [|split; [exact Hi|split; [exact Hfd|split; [exact HMO|split; [|split; [|exact HRM]]]]]].
- (* RLIVE_xR *)
  exists fpos. split; [exact HJ3|].
  split; [eapply (ajournal_gx_rom_view_xR SEGS B PST ARx LAWS pa_segs_low); [exact HJ3 | exact HROMO | exact PSTR | exact HROM0]|].
  split; [intros a H1 H2 H3 Hp; apply PM; exact (HPK1 a H1 H2 H3 Hp)|].
  split; [|split].
  + (* the frame: the saved registers above sp, the flag cell in F *)
    destruct HFR1 as (EF & EFL & HFL56 & HSV).
    destruct (frames_bounds_x SEGS B ARx LAWS _ _ _ _ _ _ 0 fpos HAR HIN) as (HF4096 & HFceil & _).
    change (fs_frame_bytes 0) with 64 in HFceil. rewrite EF in HF4096, HFceil.
    pose proof (sep_block_frame_x SEGS B ARx LAWS ly1 S1 Hp1 W1 m1 md1 (rxG0 cx) ATABLE 0 fpos HAR TIn HIN) as HdF.
    unfold zdisjoint in HdF. cbn [fst snd] in HdF. change (req_size ATABLE) with 896 in HdF.
    change (fs_frame_bytes 0) with 64 in HdF. rewrite EF in HdF.
    split; [exact EF|]. split; [exact EFL|].
    split.
    * apply (val_mem_kept SEGS (w_H W1) (w_H W1) m1 m3 (F + 56) 8 FL); [|exact HFL56].
      intros k Hk. cbn in Hk. apply KM; [lia | | | lia].
      -- intros Hn. refine (frm_img_x SEGS B ARx LAWS ly1 S1 Hp1 W1 m1 md1 0 fpos _ HAR HIN _ (NSIMG _ Hn)).
         change (fs_frame_bytes 0) with 64. rewrite EF. lia.
      -- unfold rmSA, AENT in *. lia.
    * intros k Hk. apply (val_mem_kept SEGS (w_H W1) (w_H W1) m1 m3 _ 8 _); [|exact (HSV k Hk)].
      intros t Ht. cbn in Ht. apply KM; [lia | | | lia].
      -- intros Hn. pose proof (Hsegs _ (NSIMG _ Hn)). lia.
      -- unfold rmSA, AENT in *. lia.
  + (* g_lock held *)
    eapply alock_at_kept; [exact HLK1|]. apply AK. apply rcz_cons; [|apply rcz_nil]. cbn [fst snd].
    intros a Ha. apply CKZ. unfold rmc_cells. left. exact Ha.
  + eapply awake_at_kept; [exact HWK1|]. apply AK. apply rcz_cons; [|apply rcz_nil]. cbn [fst snd].
    intros a Ha. apply CKZ. unfold rmc_cells. tauto.
- (* g_s as at the entry outside drain's slot j *)
  intros a Ha Hj. apply (rmc_kept_trans _ _ _ _ _ _ a (HGS a Ha Hj)). apply KEEP. apply CKZ. unfold rmc_cells. tauto.
- (* rr_found *)
  unfold rr_found. cbv zeta.
  exists e1, h1, ev, LB, c2, O2, cap2, out2, (rxrest cx).
  split.
  { destruct (re_eof (nth i (rxes cx) relay_remove_b_c.no_entry) =? 0) eqn:Eo.
    - unfold rmdrel, rmopen, rnth in HDR. rewrite Eo in HDR. destruct HDR as (HDR1 & HAS).
      split; [exact HDR1|].
      pose proof (proj1 (HSRC0 i Hi Hfd (proj1 (Z.eqb_eq _ _) Eo))) as Hj4.
      assert (HOBs : forall b, In b (asrc_blks h1) -> In b OB).
      { intros b Hb. unfold OB, rmsrc, rmopen, rnth. rewrite Eo. apply in_or_app. right. apply in_or_app. left. exact Hb. }
      apply (asrc_at_kept B ly1 S1 W1 m1 ly1 S1 W1 m3 _ h1 HAS).
      + apply AK. apply (rcz_asrc OB ly1 S1 W1 m1 _ h1 HAS); [|exact HOBs].
        intros a Ha. apply CKZ. unfold rmc_cells. right. left. unfold rmHA, ASRC in *. lia.
      + intros b Hb. exact (OBIN b (HOBs b Hb)).
    - unfold rmdrel, rmopen, rnth in HDR. rewrite Eo in HDR. exact HDR. }
  split; [exact HSL|].
  split.
  { (* the relay's table after the copy: remove_at i es *)
    assert (HPADS : Forall (fun e => length (re_pad1 e) = 4%nat /\ length (re_pad2 e) = 4%nat) (rxes cx)).
    { eapply Forall_impl; [|exact ROK]. intros e (_ & _ & P1 & P2 & _). split; assumption. }
    pose proof (rm_remove_length (rxes cx) i Hi) as HRL.
    assert (LTpre : length (rmTpre cx i) = (56 * i)%nat).
    { unfold rmTpre. rewrite rrs_concat_len by (apply rmc_forall_firstn; exact HPADS). rewrite length_firstn. lia. }
    assert (LTpost : length (rmTpost cx i) = (56 * (length (rxes cx) - S i))%nat).
    { unfold rmTpost. rewrite rrs_concat_len by (apply rmc_forall_skipn; exact HPADS). rewrite length_skipn. lia. }
    assert (LX : length X = 56%nat) by (unfold AENT in TX; lia).
    set (Bl := rmTpre cx i ++ X ++ rmTpost cx i ++ tail) in Ttab.
    assert (LBl : length Bl = 896%nat).
    { unfold Bl. rewrite !length_app, LTpre, LX, LTpost. unfold rN, ATABLE, AENT in Ttl. lia. }
    set (src := firstn 56 (skipn (56 * (length (rxes cx) - 1)) Bl)).
    assert (Lsrc : length src = 56%nat) by (unfold src; rewrite length_firstn, length_skipn, LBl; lia).
    assert (EQB : firstn (56 * i) Bl ++ src ++ skipn (56 * i + 56) Bl =
                  concat (map entry_bytes (relay_remove_b_c.remove_at i (rxes cx))) ++ src ++ tail)
      by (apply (rmc_block_cpy (rxes cx) tail X src Bl i Hi LX HPADS); reflexivity).
    assert (GNL : garr8 SEGS (arm W1 m3) (rxG0 cx) (bzs (firstn (56 * i) Bl ++ src ++ skipn (56 * i + 56) Bl))).
    { unfold bzs in Ttab |- *. rewrite !map_app. apply garr8_app. split.
      - apply (rmc_garr8_moved W1 W1 m1 m3 (rxG0 cx) (rxG0 cx)).
        + rewrite <- firstn_map. apply rmc_garr8_firstn. exact Ttab.
        + intros j Hj. rewrite length_map, length_firstn in Hj. apply TB; [lia | unfold rmSA, AENT; lia].
      - rewrite length_map, length_firstn, Nat.min_l by lia. apply garr8_app. split.
        + apply (rmc_garr8_moved W1 W1 m1 m3 (rxG0 cx + Z.of_nat (56 * (length (rxes cx) - 1))) _).
          * unfold src. rewrite <- firstn_map, <- skipn_map. apply rmc_garr8_firstn. apply rmc_garr8_skipn;
            [rewrite length_map; lia | exact Ttab].
          * intros j Hj. rewrite length_map, Lsrc in Hj.
            replace (rxG0 cx + Z.of_nat (56 * i) + j) with (rmSA cx i + j) by (unfold rmSA, AENT; lia).
            rewrite (SLM j ltac:(unfold AENT; lia)). f_equal. unfold rN, AENT. lia.
        + rewrite length_map, Lsrc.
          apply (rmc_garr8_moved W1 W1 m1 m3 (rxG0 cx + Z.of_nat (56 * i + 56)) _).
          * rewrite <- skipn_map. apply rmc_garr8_skipn; [rewrite length_map; lia | exact Ttab].
          * intros j Hj. rewrite length_map, length_skipn, LBl in Hj.
            replace (rxG0 cx + Z.of_nat (56 * i) + Z.of_nat 56 + j) with (rxG0 cx + Z.of_nat (56 * i + 56) + j) by lia.
            apply TB; [lia | unfold rmSA, AENT; lia]. }
    split; [apply (akept_vm W1 m1); [intros x Hx; apply KEEP; apply CKZ; unfold rmc_cells; cbn in Hx; tauto | exact Tsrc]|].
    split; [apply (akept_awr W1 m1); [intros x Hx; apply KEEP; apply CKZ; unfold rmc_cells; tauto | exact Tsrcw]|].
    split.
    { rewrite HRL. replace (Z.of_nat (length (rxes cx) - 1)) with (rN cx - 1) by (unfold rN; lia). exact NSM. }
    split; [intros k Hk; unfold arm; exact (writable_kept (w_H W1) m1 m3 _ (PM _) (Tnsrcw k Hk))|].
    split; [apply (akept_vm W1 m1); [intros x Hx; apply KEEP; apply CKZ; unfold rmc_cells; cbn in Hx; tauto | exact Tcap]|].
    split; [apply (akept_awr W1 m1); [intros x Hx; apply KEEP; apply CKZ; unfold rmc_cells; tauto | exact Tcapw]|].
    split; [rewrite HRL; lia|].
    split; [exact TIn|].
    split.
    { exists (src ++ tail). split; [|split].
      - rewrite length_app, Nat2Z.inj_add, Lsrc, Ttl, HRL. unfold rN, ATABLE, AENT. lia.
      - rewrite <- EQB, !length_app, length_firstn, Lsrc, length_skipn, LBl. unfold ATABLE. lia.
      - rewrite <- EQB. exact GNL. }
    split.
    { rewrite Forall_forall in Tok |- *. intros e He.
      assert (HOBe : forall b, In b (aentry_blks e) -> In b OB).
      { intros b Hb. unfold OB, rmOB. apply in_or_app. left. apply in_concat. exists (aentry_blks e).
        split; [apply in_map; exact He | exact Hb]. }
      apply (aentry_ok_kept B ly1 S1 W1 m1 ly1 S1 W1 m3 e (Tok e He)).
      - apply AK. exact (rcz_aentry OB ly1 S1 W1 m1 e (Tok e He) HOBe).
      - intros b Hb. exact (OBIN b (HOBe b Hb)). }
    split.
    { apply (proj2 (stdpp.base.NoDup_ListNoDup _)). apply rmc_nodup_remove; [exact Hi|].
      exact (proj1 (stdpp.base.NoDup_ListNoDup _) RND). }
    (* no entry's block is the table (arelay_at's twelfth conjunct, W8 42f5184c7ab): MatchCx's rm_base_notab *)
    exact (rm_base_notab B ARx MT RP MMAX RG cx i HB Hi). }
  split.
  { apply (aout_at_kept B RG ly1 S1 W1 m1 ly1 S1 W1 m3 _ _ _ _ _ _ HOUT).
    - apply AK. apply (rcz_aout OB ly1 S1 W1 m1 _ _ _ _ _ _ HOUT OUTC).
      intros b Hb. unfold OB. apply in_or_app. right. apply in_or_app. right. apply in_or_app. left. exact Hb.
    - intros b Hb. apply OBIN. unfold OB. apply in_or_app. right. apply in_or_app. right. apply in_or_app. left. exact Hb. }
  split.
  { rewrite (rm_drains cx i (proj1 (stdpp.base.NoDup_ListNoDup _) RND) HFD0 Hi Hfd) in HPERM0. exact HPERM0. }
  exact HPERM.
Qed.

Theorem rr_m_cpy_xR : hop_cpy_stmt_xR B PST ARx MT RP MMAX RG R.
Proof.
unfold hop_cpy_stmt_xR. intros cx i W1 c1 HB HC KU.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof pa_segs_low as Hsegs.
destruct HC as (regs1 & ly1 & S1 & Hp1 & m1 & md1 & k1 & F & FL & e1 & h1 & ev & LB & c2 & O2 & cap2 & out2 & X &
  -> & HMH & HLV & HDR & HTB & HSL & HOUT & HPERM & HGS & HMO & HRM).
pose proof HB as (HPRE & _ & _ & RGP & _ & _ & _ & _ & HREL0 & _ & HROM0 & _).
pose proof RGP as (_ & RGNSRC & RGSRC & _ & _ & _ & RGIMG & _ & _).
destruct HMH as (HRH & H25 & H24 & HFD0 & Hi & Hfd).
pose proof HRH as ((Hsp1 & H3 & H4 & _ & _ & _ & _ & _ & H22 & _ & _) & _ & H23).
pose proof HLV as (fpos & HJ & _ & HPK1 & HFR1 & HLK1 & HWK1).
pose proof HTB as (Tsrc & _ & Tnsrc & Tnsrcw & _ & _ & TIn & _ & _ & _ & _).
pose proof HREL0 as (_ & _ & _ & _ & _ & _ & Rlen16 & _).
assert (HAR : ARx ly1 S1 Hp1 W1 m1 md1) by (eapply ajournal_gx_AR_xR; exact HJ).
destruct (alx_blocks _ _ _ LAWS ly1 S1 Hp1 W1 m1 md1 (rxG0 cx) ATABLE HAR TIn) as (HG16 & HG4096 & HGceil & HGapp & HGpres & _).
change (req_size ATABLE) with 896 in HGceil, HGapp, HGpres.
assert (HN : 1 <= rN cx <= 16) by (unfold rN; lia).
remember (Eimg (Ereg regs1 (rmc_extra (rxG0 cx) (rN cx)))) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (HAE : env_agree 32 (Ereg regs1 (rmc_extra (rxG0 cx) (rN cx))) E)
by (rewrite HE; split; [intros m Hm; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
assert (EEo : forall m (rr : bv 5), Z.of_nat m = bv_unsigned rr -> ew E m = getr regs1 rr)
by (intros m rr Hm; subst E; pose proof (bv_unsigned_in_range 5 rr) as Hr5; change (bv_modulus 5) with 32 in Hr5;
rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_nat; exact Hm).
assert (E32 : ew E 32 = Z_to_bv 64 (rxG0 cx))
by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 (rN cx))
by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 _ 1)).
assert (E22 : ew E 22 = Z_to_bv 64 SHADOW_OFF) by (rewrite (EEo 22%nat 22%bv eq_refl); exact H22).
assert (E24 : ew E 24 = Z_to_bv 64 (AENT * Z.of_nat i)) by (rewrite (EEo 24%nat 24%bv eq_refl); exact H24).
assert (UV : forall n, (A_TEXT <= n < A_LIM)%nat -> bv_unsigned (ew E n) = VAL n).
{ intros n Hn. subst E. rewrite Eimg_img by exact Hn. apply unsigned_lit_small. apply pa_val_range. }
pose proof (pa_obj_img 7 ltac:(lia)) as Q7. pose proof (pa_obj_img 8 ltac:(lia)) as Q8.
assert (HS : st_ok_pi SEGS VAL E ss_rmc (restrict (w_H W1) (mkst regs1 (Z_to_bv 64 (BASE + A_rr_cpy)) m1 (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. unfold ss_rmc. apply pa_entry_st_ok_full.
- unfold rmc_sr.
  apply regs_ok_pin; [| intros X0; discriminate X0 |].
  2:{ cbn [sv_denot]. rewrite (UV (A_HI 60)) by (unfold A_HI, A_TEXT, A_LIM; lia). rewrite Z.add_0_r, HH60. exact H25. }
  apply regs_ok_pin; [| intros X0; discriminate X0 |].
  2:{ cbn [sv_denot]. rewrite (UV (A_HI 59)) by (unfold A_HI, A_TEXT, A_LIM; lia). rewrite Z.add_0_r, HH59. exact H23. }
  rewrite HE. apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- repeat apply Forall_cons; try apply Forall_nil; unfold region_ok, rmc_src, rmc_nsrc;
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
  + rewrite (UV (A_OBJ 8)) by (unfold A_OBJ, A_TEXT, A_LIM; lia). rewrite <- RGSRC.
    split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    repeat apply Forall_cons; try apply Forall_nil.
    apply (chunk_ok_val SEGS E _ (rg_src RG) 0 8 (SOff 32 0) (rxG0 cx));
    [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
    rewrite Z.add_0_r. exact Tsrc.
  + rewrite (UV (A_OBJ 7)) by (unfold A_OBJ, A_TEXT, A_LIM; lia). rewrite <- RGNSRC.
    split; [lia|]. split; [lia|]. split; [intros o Ho; apply Tnsrcw; lia|].
    repeat apply Forall_cons; try apply Forall_nil.
    apply (chunk_ok_val SEGS E _ (rg_nsrc RG) 0 4 (SOff 33 0) (rN cx));
    [cbn [sv_denot]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
    rewrite Z.add_0_r. exact Tnsrc.
- apply pairwise_disjoint_of_extents. unfold rmc_src, rmc_nsrc, extent_of_region.
  cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val].
  rewrite (UV (A_OBJ 8)), (UV (A_OBJ 7)) by (unfold A_OBJ, A_TEXT, A_LIM; lia). rewrite <- RGSRC, <- RGNSRC.
  pose proof HRGP as HP. cbn [zpairwise_disjoint zall_disjoint] in HP. unfold zdisj in HP. cbn [fst snd] in HP.
  destruct HP as (_ & _ & (D23 & _) & _).
  cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. repeat split; try exact I; lia.
- split; [|split; [exact I | exact I]].
  cbn [rmc_facts f_atoms atoms_ok]. unfold afact_ok, rmc_OBJF, rmc_HIF. cbn [af_lo af_hi af_al2].
  rewrite E22, E24, E32, E33.
  rewrite (UV (A_OBJ 7)), (UV (A_OBJ 8)), (UV (A_HI 59)) by (unfold A_OBJ, A_HI, A_TEXT, A_LIM; lia).
  rewrite HH59. rewrite <- RGNSRC in Q7. unfold RR_HI_NSRC.
  rewrite !unsigned_lit_small by (unfold SHADOW_OFF, AENT, rN in *; lia).
  change (2 ^ 4) with 16. rewrite !Z.pow_0_r, !Z.mod_1_r.
  unfold SB, SHADOW_OFF, AENT in *. repeat match goal with |- _ /\ _ => split end; try lia; try exact I. }
clear HE.
assert (SHOK : sh_ok SEGS rmc_Bx [] E (mrestrict (w_H W1) m1)) by constructor.
unfold cfg_at. change (w64 (BASE + A_rr_cpy)) with (Z_to_bv 64 (BASE + A_rr_cpy)).
(* 0x83f98 .. 0x83fa4: the loads of g_src and g_nsrc, a0 = &g_src[i], a2 = N - 1; stop at the store 0x83fa8 *)
paj_run_to_tok_xR RUNTOR HS HJ SHOK rmc_Bspan (AF_fr_relay_remove + 0x1c4).
{ apply awr_ok_x_cons; [intros a Ha; cbn in Ha; lia|].
  apply awr_ok_x_cons_g; [|apply awr_ok_x_nil].
  intros a Ha. cbn [rmc_nsrc YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha.
  rewrite (UV (A_OBJ 7)) in Ha by (unfold A_OBJ, A_TEXT, A_LIM; lia). rewrite <- RGNSRC in Ha.
  unfold inG, G_RR. apply Exists_cons_tl. apply Exists_cons_hd. unfold in_zr. cbn [fst snd]. lia. }
rename HFr into HFr1, HG0 into HGr1. clear HF.
lazymatch goal with |- SRrG _ _ _ (mkCfg ?mm _) _ => rename mm into ms1 end.
clear HEI0.
assert (HREL : VAL (A_OBJ 7) = VAL (A_HI 59) + -1864) by (rewrite HH59, <- RGNSRC; unfold RR_HI_NSRC; lia).
prebase HS 1%nat (A_HI 59) (-1864) HREL.
(* 0x83fa8 .. 0x83fc0: g_nsrc = N - 1 (through s7 = A_HI 59), a1 = &g_src[N - 1], a2 = 56; the call *)
paj_run_tok_xR RUNR HS HJ SHOK rmc_Bspan.
{ apply awr_ok_x_cons; [intros a Ha; cbn in Ha; lia|].
  apply awr_ok_x_cons_g; [|apply awr_ok_x_nil].
  intros a Ha. cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha.
  match goal with HE : img_env _ _ ?Ex |- _ => rewrite (HE 339%nat ltac:(unfold A_TEXT, A_LIM; lia)) in Ha end.
  change 339%nat with (A_HI 59) in Ha. rewrite HH59 in Ha. unfold RR_HI_NSRC in Ha.
  unfold inG, G_RR. apply Exists_cons_tl. apply Exists_cons_hd. unfold in_zr. cbn [fst snd]. lia. }
rename HFr into HFr2, HG0 into HGr2. clear HF.
lazymatch goal with |- SRrG _ _ _ (mkCfg ?mm _) _ => rename mm into ms2 end.
pose proof (st_ok_region_nth _ _ _ 1 _ HS eq_refl) as HRN. cbn [ms_mem restrict] in HRN.
pose proof (regs_kept_of_st_ok SEGS _ _ _ regs1 _ RMC_KEPT HS HAE ltac:(vm_compute; reflexivity)) as K2.
cbn [ms_regs restrict] in K2.
pmkst HS.
prreg HS (1%bv : bv 5) P1. prreg HS (10%bv : bv 5) P10. prreg HS (11%bv : bv 5) P11. prreg HS (12%bv : bv 5) P12.
(* ---- the state at the call: what the two runs changed (g_nsrc), the registers ---- *)
pose proof HPRE as (_ & _ & _ & Hgp & Htp & Hstk & _).
pose proof Hstk as (_ & _ & Hceil & Hslo & Hshi & H47 & _).
assert (WS : RR_STK_x = 17072) by reflexivity. assert (WF : RR_FRAME = 96) by reflexivity.
assert (Hes : ESTACK = 4096) by reflexivity.
fold (rsp0 cx) in Hslo, Hshi.
assert (HSC : alloc_ceiling <= rsp0 cx - RR_FRAME - ESTACK) by lia.
pose proof HJ as HAR2. eapply ajournal_gx_AR_xR in HAR2.
assert (KR : forall a, 0 <= a < 2 ^ 64 -> ~ (rg_nsrc RG <= a < rg_nsrc RG + 4) ->
  aview SEGS (w_H W1) (ms_mem ms2) a = aview SEGS (w_H W1) m1 a).
{ intros a Ha Hn.
  rewrite (aview_kept_out _ _ (w_H W1) (ms_mem ms1) (ms_mem ms2) HFr2 a Ha).
  2:{ intros (r & Hin & Hr).
      lazymatch type of Hin with In _ ?rs => let rs' := eval vm_compute in rs in change (In r rs') in Hin end.
      cbn [In] in Hin. destruct Hin as [<- | [<- | []]]; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr; [lia|].
      rewrite (HEI 339%nat ltac:(unfold A_TEXT, A_LIM; lia)) in Hr. change 339%nat with (A_HI 59) in Hr.
      rewrite HH59 in Hr. unfold RR_HI_NSRC in Hr. lia. }
  apply (aview_kept_out _ _ (w_H W1) m1 (ms_mem ms1) HFr1 a Ha).
  intros (r & Hin & Hr).
  lazymatch type of Hin with In _ ?rs => let rs' := eval vm_compute in rs in change (In r rs') in Hin end.
  cbn [In] in Hin. destruct Hin as [<- | [<- | []]]; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr; [lia|].
  rewrite (HEI 248%nat ltac:(unfold A_TEXT, A_LIM; lia)) in Hr. change 248%nat with (A_OBJ 7) in Hr.
  rewrite <- RGNSRC in Hr. lia. }
assert (PR : forall a, apresent (w_H W1) m1 a -> apresent (w_H W1) (ms_mem ms2) a)
  by (intros a Ha; exact (apresent_grows _ _ _ a HGr2 (apresent_grows _ _ _ a HGr1 Ha))).
assert (NS2 : val_mem SEGS (mrestrict (w_H W1) (ms_mem ms2)) (rg_nsrc RG) 4 (rN cx - 1)).
{ replace (rg_nsrc RG) with (VAL (A_HI 59) + -1864) by (rewrite HH59; unfold RR_HI_NSRC; lia).
  change 4%nat with (N.to_nat 4).
  apply (field_of_region E _ 339%nat _ _ _ _ _ _ (-1864) 4 (SOff 33 (-1)) (rN cx - 1) HRN).
  - exact (HEI 339%nat ltac:(unfold A_TEXT, A_LIM; lia)).
  - left. reflexivity.
  - cbn [sv_denot]. rewrite E33, unsigned_lit_small by lia. reflexivity.
  - cbn. lia.
  - cbn. lia. }
assert (SP2 : spZ (ms_regs ms2) = rsp0 cx - RR_FRAME).
{ unfold spZ. rewrite (K2 2%bv ltac:(cbn; tauto)). exact Hsp1. }
assert (A10 : getr (ms_regs ms2) 10 = w64 (rmSA cx i)).
{ rewrite P10, E24, E32, YI08.alu64_add_lit. unfold w64, rmSA. f_equal. lia. }
assert (A11 : getr (ms_regs ms2) 11 = w64 (rxG0 cx + AENT * (rN cx - 1))).
{ rewrite P11, E32, E33, unsigned_lit_small by lia.
  assert (M : mul_div M_MUL (Z_to_bv 64 (rN cx)) (Z_to_bv 64 56) = Z_to_bv 64 (rN cx * 56)).
  { apply bv_eq. rewrite mul_div_unsigned, !unsigned_lit_small by lia. cbn [zmd_raw].
    unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64). apply Z.mod_small. lia. }
  rewrite M, YI08.alu64_add_lit. unfold w64, AENT. f_equal. lia. }
assert (HSLOT : forall a, rmSA cx i <= a < rmSA cx i + AENT -> rxG0 cx <= a < rxG0 cx + 896)
  by (intros a Ha; unfold rmSA, AENT in *; lia).
assert (HLAST : forall a, rxG0 cx + AENT * (rN cx - 1) <= a < rxG0 cx + AENT * (rN cx - 1) + AENT ->
  rxG0 cx <= a < rxG0 cx + 896) by (intros a Ha; unfold AENT in *; lia).
(* ---- __asan_memcpy (&g_src[i], &g_src[N - 1], 56) ---- *)
eapply (SRrG_bind SEGS R R_trans).
{ eapply (aj_gx_entry_at_xR B PST ARx LAWS R_trans WLE_R (G_RR B RG) 0 [] ESTACK (SIGMA WS_asan_memcpy)
    (fun a => rmSA cx i <= a < rmSA cx i + AENT)
    (fun (regs' : bvmap 5 word) (mem' : word -> option byte) => forall t, 0 <= t < AENT ->
       aview SEGS (w_H W1) mem' (rmSA cx i + t) = aview SEGS (w_H W1) (ms_mem ms2) (rxG0 cx + AENT * (rN cx - 1) + t))
    W1 _ _ RR_STK_x (rsp0 cx) (rFP cx) (rxly cx) (rxS cx) (rxHp cx) (rxW cx) (rxmem cx) (rxmd cx) _ _ _ _ _ _ (-96) _ HG eq_refl
    HJ).
  - rewrite SP2, WF. lia.
  - reflexivity.
  - lia.
  - lia.
  - rewrite WS, Hes. lia.
  - rewrite (K2 3%bv ltac:(cbn; tauto)), H3. exact Hgp.
  - rewrite (K2 4%bv ltac:(cbn; tauto)), H4. exact Htp.
  - exact P1.
  - apply ret_ok_codeptr_v; [lia | reflexivity].
  - intros a. destruct (Z_lt_ge_dec a (rmSA cx i)); [right; lia|].
    destruct (Z_lt_ge_dec a (rmSA cx i + AENT)); [left; lia | right; lia].
  - intros a Ha HGa. exfalso. destruct (HG a HGa) as [Himg _].
    refine (blk_img_x SEGS B ARx LAWS ly1 S1 Hp1 W1 (ms_mem ms2) _ (rxG0 cx) ATABLE a HAR2 TIn _ Himg).
    change (req_size ATABLE) with 896. exact (HSLOT a Ha).
  - intros a Ha _. split; [|lia].
    right. left. split.
    + unfold rFP, rr_fp. replace a with (rxG0 cx + (a - rxG0 cx)) by lia.
      apply (inFP_ablocks_fp _ (rxG0 cx) ATABLE); [left; reflexivity | change (req_size ATABLE) with 896; pose proof (HSLOT a Ha); lia].
    + exists (rxG0 cx), ATABLE. split; [exact TIn|]. change (req_size ATABLE) with 896. exact (HSLOT a Ha).
  - intros HPRE2 _.
    assert (DEST : dest_ok SEGS B ly1 S1 W1 (ms_regs ms2) (ms_mem ms2) (rmSA cx i) AENT).
    { intros a Ha. destruct (HGpres a (HSLOT a Ha)) as [Hp Hno].
      split; [apply (apresent_writable SEGS); exact (PR a Hp)|]. split; [exact Hno|].
      rewrite SP2. pose proof (HSLOT a Ha). lia. }
    assert (CHK : forall x, rxG0 cx <= x -> x + AENT <= rxG0 cx + 896 -> achecked W1 (ms_mem ms2) x AENT).
    { intros x Hx1 Hx2. split; [|split].
      - eapply (YCe5x.amem_range_of_block_x SEGS B ARx LAWS ly1 S1 Hp1 W1 (ms_mem ms2) _ (rxG0 cx) ATABLE);
        [exact HAR2 | exact TIn | lia |].
        change (req_size ATABLE) with 896. lia.
      - eapply (range_addressable_of_block_hp0_x SEGS B ARx LAWS HP0 ly1 S1 Hp1 W1 (ms_mem ms2) _ (rxG0 cx) ATABLE);
        [exact HAR2 | exact TIn | lia |].
        change (req_size ATABLE) with 896. lia.
      - intros Hpos. eapply (shadow_hull_vis_of_block_hp0_x SEGS B ARx LAWS HP0 ly1 S1 Hp1 W1 (ms_mem ms2) _ (rxG0 cx) ATABLE);
        [exact HAR2 | exact TIn | lia | change (req_size ATABLE) with 896; lia | exact Hpos]. }
    assert (SRC : src_ok SEGS W1 (ms_regs ms2) (ms_mem ms2) (rxG0 cx + AENT * (rN cx - 1)) AENT).
    { intros a Ha. split; [apply aview_some_of_apresent; exact (PR a (proj1 (HGpres a (HLAST a Ha))))|].
      rewrite SP2. pose proof (HLAST a Ha). lia. }
    destruct (Nat.lt_ge_cases (S i) (length (rxes cx))) as [Hlt | Hge].
    + (* i < N - 1: the copy of slot N - 1 (disjoint) *)
      destruct (CHK (rmSA cx i) ltac:(unfold rmSA, AENT; lia) ltac:(unfold rmSA, AENT; lia)) as (Cd1 & Cd2 & Cd3).
      destruct (CHK (rxG0 cx + AENT * (rN cx - 1)) ltac:(unfold AENT; lia) ltac:(unfold AENT; lia)) as (Cs1 & Cs2 & Cs3).
      eapply SRr_mono.
      { apply (AMEMCPY ly1 S1 Hp1 W1 (ms_regs ms2) (ms_mem ms2) _ (rmSA cx i) (rxG0 cx + AENT * (rN cx - 1)) AENT HPRE2
          A10 A11 P12); try (unfold rmSA, AENT; lia); [exact DEST | exact Cd1 | | exact Cd2 | exact Cd3 |].
        1: { intros a Ha. apply kept_x_off_img. exact (blk_img_x SEGS B ARx LAWS ly1 S1 Hp1 W1 (ms_mem ms2) _ (rxG0 cx) ATABLE a
               HAR2 TIn ltac:(change (req_size ATABLE) with 896; exact (HSLOT a Ha))). }
        split; [unfold AENT; lia|]. split; [unfold AENT; lia|]. split; [exact SRC|].
        split; [unfold rmSA, rN, AENT in *; lia|]. split; [exact Cs1|]. split; [exact Cs2 | exact Cs3]. }
      cbv beta. intros W4 c4 _ (-> & regs4 & mem4 & md4 & -> & HAR4 & HP4 & Hsm4 & _ & Hcp4 & Hfr4 & Hpr4).
      split; [reflexivity|]. exists regs4, mem4, md4.
      split; [reflexivity|]. split; [exact HAR4|]. split; [exact HP4|]. split; [exact Hsm4|].
      split; [exact Hcp4|]. split; [exact Hfr4 | exact Hpr4].
    + (* i = N - 1: onto itself *)
      assert (EL : rxG0 cx + AENT * (rN cx - 1) = rmSA cx i) by (unfold rmSA, rN, AENT; lia).
      rewrite EL in A11.
      eapply SRr_mono.
      { apply (AMEMCPYS ly1 S1 Hp1 W1 (ms_regs ms2) (ms_mem ms2) _ (rmSA cx i) AENT HPRE2 A10 A11 P12);
          try (unfold rmSA, AENT; lia); [exact DEST | rewrite <- EL; exact SRC | apply CHK; unfold rmSA, AENT; lia | | | ].
        - eapply (ajournal_gx_rom_view_xR SEGS B PST ARx LAWS pa_segs_low); [exact HJ | exact HROMO | exact PSTR | exact HROM0].
        - intros _. eapply (YCe5x.amem_range_of_block_x SEGS B ARx LAWS ly1 S1 Hp1 W1 (ms_mem ms2) _ (rxG0 cx) ATABLE);
          [exact HAR2 | exact TIn | unfold rmSA, AENT; lia | change (req_size ATABLE) with 896; unfold rmSA, AENT; lia].
        - intros a Ha. exact (blk_img_x SEGS B ARx LAWS ly1 S1 Hp1 W1 (ms_mem ms2) _ (rxG0 cx) ATABLE a HAR2 TIn
            ltac:(change (req_size ATABLE) with 896; exact (HSLOT a Ha))). }
      cbv beta. intros W4 c4 _ (-> & regs4 & mem4 & md4 & -> & HAR4 & HP4 & Hsm4 & _ & Hfr4 & Hpr4).
      split; [reflexivity|]. exists regs4, mem4, md4.
      split; [reflexivity|]. split; [exact HAR4|]. split; [exact HP4|]. split; [exact Hsm4|].
      split; [|split; [intros a Ha _ Hsc; exact (Hfr4 a Ha (fun x => x) Hsc) | exact Hpr4]].
      intros t Ht. rewrite EL. apply Hfr4; [unfold rmSA, AENT in *; lia | intros x; exact x |].
      rewrite SP2. unfold rmSA, AENT in *. lia. }
cbv beta. intros W3 c3 _ (-> & regs3 & mem3 & md3 & -> & HJ3 & HP3 & HPr3 & Hfr3 & Hpres3).
(* ---- back at 0x83fc4: RRU_xR (Some i) ---- *)
assert (K3 : forall r : bv 5, In r RMC_KEPT -> getr regs3 r = getr regs1 r).
{ intros r Hr. rewrite <- (K2 r Hr). rewrite <- (Z_to_bv_bv_unsigned 5 r). apply HP3.
  unfold RMC_KEPT in Hr.
  repeat (destruct Hr as [<- | Hr]; [unfold acallee_saved;
    lazymatch goal with |- context [bv_unsigned ?b] => let v := eval vm_compute in (bv_unsigned b) in
      change (bv_unsigned b) with v end; lia|]).
  destruct Hr. }
apply KU. exists regs3, ly1, S1, Hp1, mem3, md3, k1, F, FL.
split; [reflexivity|].
split; [unfold rregs_base, spZ; rewrite !K3 by (cbn; tauto); exact (proj1 HRH)|].
split; [exact HFD0|].
apply (rmc_post_xR cx i ly1 S1 Hp1 W1 m1 md1 k1 F FL e1 h1 ev LB c2 O2 cap2 out2 X fpos mem3 md3 HB HFD0 Hi Hfd HAR HPK1
  HFR1 HLK1 HWK1 HDR HTB HSL HOUT HPERM HGS HMO HRM).
- intros a Ha Hn Hs Hsc. rewrite (Hfr3 a Ha Hs ltac:(rewrite WF in Hsc; lia)). exact (KR a Ha Hn).
- intros a Hp. exact (Hpres3 a (PR a Hp)).
- apply (val_mem_kept SEGS (w_H W1) (w_H W1) (ms_mem ms2) mem3 (rg_nsrc RG) 4 (rN cx - 1)); [|exact NS2].
  intros k Hk. apply Hfr3.
  + pose proof (Hsegs (rg_nsrc RG + k) ltac:(apply RGIMG; unfold rg_rng; cbn in Hk; lia)). lia.
  + intros Hs. refine (blk_img_x SEGS B ARx LAWS ly1 S1 Hp1 W1 m1 md1 (rxG0 cx) ATABLE _ HAR TIn _
      (proj1 (RGIMG (rg_nsrc RG + k) ltac:(unfold rg_rng; cbn in Hk; lia)))).
    change (req_size ATABLE) with 896. exact (HSLOT _ Hs).
  + pose proof (Hsegs (rg_nsrc RG + k) ltac:(apply RGIMG; unfold rg_rng; cbn in Hk; lia)). lia.
- intros t Ht. rewrite (HPr3 t Ht). apply KR; [unfold AENT in *; lia|].
  intros Hn. refine (blk_img_x SEGS B ARx LAWS ly1 S1 Hp1 W1 m1 md1 (rxG0 cx) ATABLE _ HAR TIn _
    (proj1 (RGIMG (rxG0 cx + AENT * (rN cx - 1) + t) ltac:(unfold rg_rng; lia)))).
  change (req_size ATABLE) with 896. unfold AENT in *. lia.
- exact HJ3.
Qed.

End wR.
End c.
End b.
End a.
