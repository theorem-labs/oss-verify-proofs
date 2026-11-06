(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: hop DRAIN of the MATCH segment of the ASan walk of fuzz_reply's relay_remove
   (lib/A/W_rr_match_cx.v hop_drain_stmt): RRM i 0x83f48 -> RRG i 0x83f68.
   rule 24: proves function relay_remove MATCH hop 1 (kind: segment lemma of the W6 walk, PORTED from 2ad36763b22
   relay_remove_p_bc.v rrA_drain_hop / relay_remove_seg.v rrA_found; lookup + CONFIRM in context).

   The hop: the shadow check of entry i's eof field (0x83f4c-0x83f58: the engine's fast path over the slot's 56
   bytes, so the report arm 0x84098-0x840a8 is never reached), the eof load 0x83f5c and the test 0x83f60.  eof <> 0:
   to 0x83f68 with nothing changed.  eof = 0: jal drain 0x83f64, through DRAIN (dr_spec) at BASE + AF_fr_drain, back
   at 0x83f68; drain's journal (at G_DR) is lifted to G_RR (rr_lift_DR) for the caller's.

   Where each part comes from:
   - rr_m_drain (the hop): the lane's rrA_drain_hop (relay_remove_p_bc.v:1956) with rrA_found / rrA_found_tail /
     rrA_fdisp (relay_remove_seg.v:594-674).  Ported: the instruction run and its two arms (eof <> 0: e1 = e and
     nothing changed, the lane's rrA_at_ge_noeof, relay_remove_p_c_noeof.v:36; eof = 0: drain's call, the lane's
     rrA_at_ge_of_drain, relay_remove_p_c_atge.v:593), dr_spec's premises from the matched entry (the lane's D39 /
     rrA_nodup_pick, relay_remove_p_bc.v:130), the trace split (rrA_tr_split, p_bc.v:179, here rm_tr_split).  New: the
     symbolic state at 0x83f48 (W_rr_scan.v's form, the slot atom with mkSHE 10 0 56 so the check takes the fast
     path), the call through W_gestures_end.v gse_callS (Section ark), and RRG's bookkeeping
     (W_rr_match_cx.v): rrd_closed_rrg (eof <> 0), rrd_open_rrg / rmd_tbl_drain / rmd_bud_open (eof = 0), rrd_drp /
     rrd_drp_of (dr_post at the return state).  RLIVE across drain's call is W_rr_m_kit.v rr_live_call (written here,
     moved to the kit).  dr_spec's
     `SA mod 8 = 0` is W_drain_sa.v dr_sa_align_slot (W7's, cited).
   - rmd_eof_cell, rmd_eb_len, rmd_concat_split, rmd_concat_len, rmd_nth_le_bytes, rmd_garr8_le: W_rr_scan.v
     rrs_fd_cell (the lane's rrA_fd_cell, relay_remove_stg.v:221) at the eof field, rrs_eb_len, rrs_concat_split,
     rrs_concat_len, rrs_nth_le_bytes, rrs_garr8_le, copied.  rmd_bzs_len, rmd_key_ptrs_len: W_rr_tail.v
     rr_bzs_len / rr_key_ptrs_len, copied.
   - rmd_nn .. rmd_dtr_nn (drain's and the key run's request sizes are nonnegative) and rmd_dr_inv_of: copied from
     the relay_instance_gone TOP lane, commit d634148958a, lib/A/W_rig_top_bud.v tb_nn ..
     tb_dtr_nn, dr_inv_of (written new there); rmd_nn_meas keeps tb_nn_meas's tr_cost half only.
   - rmd_lw .. rmd_bsum_out and rmd_dr_bytes (drain changes the live bytes by at most its trace's net change tr_net;
     from dr_post's two Permutations by blocks_bytes_bsum, no dr_spec gap): the same commit's lib/A/W_rig_top_bytes.v
     td_lw .. dr_bytes, re-proved in C3's net form: rmd_grow, rmd_seen, rmd_lines_run, rmd_push_tra, rmd_pushes,
     rmd_run and rmd_drain are equalities over tr_net (each growth replaces its block, each free removes its block's
     size; send_line's share is W_tr_peak.v send_line_tr_net), rmd_pot counts the pending texts' blocks too, and
     rmd_drop_net / rmd_pend_lw are new.
   - rmd_tl_nn, rmd_bud_open (RRG's meter after drain: RBASE's peak premise, W_tr_peak.v tr_peak_app and
     rmd_dr_bytes; dr_spec's peak premise at the call is W_tr_peak.v tr_peak_prefix): new.
   - rmd_blk_kept, rmd_notin_fp, rmd_aentry_fp (adapted from W_rr_tail.v rfz_aentry), rmd_abk_trans, rmd_X_in_rr,
     rmd_perm_cmap, rmd_blks_split, rmd_perm_pre / post / rest, rmd_nodup_app_disj, rmd_nodup_mid: new. *)
(* Modified by Theorem Labs, 2026-10: ROUTE (b), STEP 3 in the room form (a Theorem Labs lane, lane RR_x): hop DRAIN over ANY
   allocator relation ARx (Section c is W_relay_remove_cx.v's generic block, verbatim); rr_m_drain : hop_drain_stmt
   B PST ARx MT RP MMAX RG.  The laws, the journal and its lemmas are their _x twins (head set Hp after each state),
   drain is called at dr_spec_x through W_gestures_end.v gse_callS_x, and the slot's 8-alignment is rmd_sa_align
   (commit 3d17f490d56, lib/A/W_drain_sa.v dr_sa_align_slot over alx_blocks).  The room round, RRG's two new conjuncts:
   - eof <> 0 (rrd_closed_rrg): rtr = key run ++ frees (rm_tr_split, no drain), so rmbud's rp_RM is RHELD's; the count
     cnt_ok_pk RP gse_pk by cnt_ok_pk_mono from RHELD's rr_pk count (gse_pk = 4 <= tr_peakP + 4).
   - eof = 0 (rr_m_drain, rrd_open_rrg): drain at kr' = Z.to_nat (tr_cost MT_rk (key run ++ frees)) + kr.  Its rp_RM
     premise is RHELD's split exactly (rm_tr_cost_app_m, Z2Nat.inj_add over the nonnegative MT_rk costs: rmd_nn_meas,
     rmd_rk_laws); its count premise (dr_pk = drain's peak + 2) by cnt_ok_pk_mono from RHELD's (W_tr_cnt.v
     tr_peakP_app).  After the call rmbud's rp_RM is dr_post_x's, and RRG's count is RHELD's moved by drain's count
     growth (W_rr_m_dcnt.v rmc_dr_cnt_peak over dr_post_x's two Permutations), within the trace's peak.
   - rmd_drain_dr, rmd_ocap, rmd_bytes_close (new): rmd_dr_bytes's closing arithmetic is over a final state, a
     trace net and lines that are variables, so no proof term asks the kernel to compare dr_fin with an unfolded
     drain run (rmd_dr_bytes's one-proof form took 753 s at Qed; W_rr_m_dcnt.v rmc_close, the same cut). *)
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
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YI08.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YP0d YP0c YC80 YC81 YO0a YN1e.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import W_syms W_listing W_pl W_kit W_contract.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YI00 YC5d.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import HarnessRep RelayRep gestures_end_b_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require relay_remove_b_c drain_b_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require relay_instance_gone_b_lem RelayCap.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require RelayModel RelayKeys send_line_b_c ListTr RelayRunT.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import W_frame W_journal W_sites W_rep.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YCbqG YGcallx YC80x.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import
W_kit_x W_journal_x W_sites_x W_contract_x W_frame_x.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require ReplyCnt.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import W_relay_remove_cx W_rr_match_cx W_rr_m_kit.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import W_tr_peak.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require W_gesture_end W_gestures_end W_tr_cnt.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require W_rr_m_dcnt.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import W_contract_xR.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YA0nH.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

(* ------------------------------------------------------------------ I. request sizes are nonnegative *)
(* (copied from commit d634148958a, lib/A/W_rig_top_bud.v tb_nn .. tb_dtr_nn) *)
Definition rmd_nn (t : list (RelayRunT.rev YO0i.sptr)) : Prop :=
  Forall (fun ev => match ev with
                    | RelayRunT.RMalloc n => 0 <= n
                    | RelayRunT.RFree _ _ => True
                    | RelayRunT.RRealloc _ n _ => 0 <= n
                    end) t.

Lemma rmd_nn_meas : forall MT t, ameter_laws MT -> rmd_nn t -> 0 <= tr_cost MT t.
Proof.
  intros MT t ML. induction t as [|x t IH]; intros H; [cbn; lia|].
  apply Forall_cons_iff in H as [Hx H]. pose proof (IH H) as C.
  unfold tr_cost in *. cbn [fold_right]. pose proof (mo_free_nonneg MT ML) as F.
  destruct x as [n|n a|k n a]; cbn in Hx; [pose proof (mo_malloc_nonneg MT ML n Hx) | | pose proof (mo_malloc_nonneg MT ML n Hx)];
    lia.
Qed.

Lemma rmd_nn_app : forall a b, rmd_nn a -> rmd_nn b -> rmd_nn (a ++ b).
Proof. intros a b Ha Hb. apply Forall_app. split; assumption. Qed.

Lemma rmd_sl_nn : forall f mx no cap rem j o, 0 <= mx -> 0 <= no ->
  rmd_nn (fst (send_line_b_c.sl_run f mx no cap rem j o)).
Proof.
  induction f as [|f IH]; intros mx no cap rem j o Hmx Hno; cbn [send_line_b_c.sl_run]; [constructor|].
  destruct (Z.leb_spec rem 0) as [Hr|Hr]; [constructor|].
  set (n := if negb (mx =? 0) && (mx <? rem) then mx else rem).
  assert (Hn : 0 < n) by (unfold n; destruct (Z.eqb_spec mx 0); destruct (Z.ltb_spec mx rem); cbn; lia).
  destruct (cap <? no + n); cbn [fst]; [|apply IH; lia].
  apply Forall_cons; [destruct (cap =? 0); cbn; lia | apply IH; lia].
Qed.

Lemma rmd_send_nn : forall live mx NO CAP LEN j o, 0 <= mx -> 0 <= NO ->
  rmd_nn (send_line_b_c.send_line_tr live mx NO CAP LEN j o).
Proof. intros. unfold send_line_b_c.send_line_tr. destruct live; [apply rmd_sl_nn; assumption | constructor]. Qed.

Lemma rmd_ge_nn : forall live mx NO CAP XL j o, 0 <= mx -> 0 <= NO -> 0 <= XL ->
  rmd_nn (gesture_end_b_c.gesture_end_tr live mx NO CAP XL j o).
Proof. intros. unfold gesture_end_b_c.gesture_end_tr. apply rmd_nn_app; apply rmd_send_nn; lia. Qed.

Lemma rmd_ker_nn : forall live mx xks no cap j o, 0 <= mx -> 0 <= no -> Forall (fun x => 0 <= fst x) xks ->
  rmd_nn (fst (keys_end_run live mx no cap xks j o)).
Proof.
  intros live mx xks. induction xks as [|[xl ka] r IH]; intros no cap j o Hmx Hno HF; [constructor|].
  apply Forall_cons_iff in HF as [Hx HF]. cbn [fst] in Hx. cbn [keys_end_run fst].
  apply rmd_nn_app; [apply rmd_ge_nn; lia|]. apply Forall_cons; [exact I|]. apply IH; [lia | lia | exact HF].
Qed.

Lemma rmd_grow_nn : forall c u j b, 0 <= c ->
  rmd_nn (fst (drain_b_c.grow_tr c u j b)) /\ 0 <= fst (snd (drain_b_c.grow_tr c u j b)).
Proof.
  intros c u j b Hc. unfold drain_b_c.grow_tr.
  destruct (c - u <? 4096); [destruct (Z.eqb_spec c 0)|]; cbn [fst snd];
    (split; [unfold rmd_nn; repeat constructor; cbn; lia | lia]).
Qed.

Lemma rmd_seen_nn : forall H ka l j ha ks, rmd_nn (fst (fst (drain_b_c.seen_tr H ka l j ha ks))).
Proof.
  intros. unfold drain_b_c.seen_tr, rmd_nn.
  destruct (RelayModel.gesture l) as [[g x]|]; [|constructor].
  destruct g; (match goal with |- context [match ?m with Some _ => _ | None => _ end] => destruct m end); cbn [fst].
  - constructor.
  - constructor; [destruct (ka =? 0); cbn; lia|]. constructor; [cbn; lia | constructor].
  - constructor; [exact I | constructor].
  - constructor.
Qed.

Lemma rmd_lines_nn : forall ls live mx no cap H ka j o ha ks, 0 <= mx -> 0 <= no ->
  rmd_nn (fst (fst (drain_b_c.lines_run live mx no cap H ka ls j o ha ks))).
Proof.
  induction ls as [|l r IH]; intros live mx no cap H ka j o ha ks Hmx Hno; cbn [drain_b_c.lines_run fst];
    [constructor|].
  apply rmd_nn_app; [apply rmd_send_nn; lia|]. apply rmd_nn_app; [apply rmd_seen_nn|]. apply IH; lia.
Qed.

Lemma rmd_push_nn : forall ls n cap j v rs, 0 <= n -> rmd_nn (fst (fst (drain_b_c.pushes_run n cap ls j v rs))).
Proof.
  induction ls as [|l r IH]; intros n cap j v rs Hn; cbn [drain_b_c.pushes_run fst]; [constructor|].
  apply rmd_nn_app; [|apply IH; lia].
  unfold ListTr.list_push_tra. apply rmd_nn_app; [|unfold rmd_nn; repeat constructor; cbn; lia].
  unfold rmd_nn. destruct (Z.eqb_spec n cap); [destruct (Z.eqb_spec cap 0)|]; repeat constructor; cbn; lia.
Qed.

Lemma rmd_drain_nn : forall f live mx s j a, 0 <= mx -> 0 <= drain_b_c.ds_cap s -> 0 <= drain_b_c.ds_no s ->
  0 <= drain_b_c.ds_en s -> rmd_nn (fst (drain_b_c.drain_run f live mx s j a)).
Proof.
  induction f as [|f IH]; intros live mx s j a Hmx Hc Hno Hen; cbn [drain_b_c.drain_run]; [constructor|].
  destruct (rmd_grow_nn (drain_b_c.ds_cap s) (Z.of_nat (length (drain_b_c.ds_u s))) j (drain_b_c.da_buf a) Hc)
    as [G1 G2].
  destruct (drain_b_c.ds_eintr s).
  - cbn [fst]. apply rmd_nn_app; [exact G1|]. apply IH; cbn [drain_b_c.ds_cap drain_b_c.ds_no drain_b_c.ds_en]; lia.
  - destruct (drain_b_c.ds_pend s) as [|r0 rs]; [exact G1|].
    match goal with |- context [if (?x <=? 0) then _ else _] => destruct (x <=? 0) end; [exact G1|].
    match goal with |- context [RelayModel.chunk ?u ?sk ?d] => destruct (RelayModel.chunk u sk d) as [[u' sk'] rl] end.
    match goal with |- context [drain_b_c.pushes_run ?n ?c ?ls ?j1 ?v1 ?r1] =>
      pose proof (rmd_push_nn ls n c j1 v1 r1 Hen) as TP end.
    match goal with |- context [drain_b_c.lines_run live mx ?n0 ?c0 ?H0 ?k0 rl ?J1 ?o1 ?h1 ?ks1] =>
      pose proof (rmd_lines_nn rl live mx n0 c0 H0 k0 J1 o1 h1 ks1 Hmx Hno) as TL; revert TL;
      destruct (drain_b_c.lines_run live mx n0 c0 H0 k0 rl J1 o1 h1 ks1) as [[t1 [[oc' H'] ka']] [[o' ha'] ks']] end.
    cbn [fst snd]. intros TL.
    apply rmd_nn_app; [exact G1|]. apply rmd_nn_app; [exact TP|].
    apply rmd_nn_app; [match goal with |- rmd_nn (if ?b then _ else _) => destruct b end; unfold rmd_nn; repeat constructor|].
    apply rmd_nn_app; [exact TL|]. apply IH; cbn [drain_b_c.ds_cap drain_b_c.ds_no drain_b_c.ds_en]; lia.
Qed.

Lemma rmd_dtr_nn : forall live mx NO CAP e h j a, 0 <= mx -> 0 <= re_cap e -> 0 <= NO ->
  rmd_nn (drain_b_c.drain_tr live mx NO CAP e h j a).
Proof.
  intros. unfold drain_b_c.drain_tr, drain_b_c.drain_go.
  apply rmd_drain_nn; cbn [drain_b_c.drain_init drain_b_c.ds_cap drain_b_c.ds_no drain_b_c.ds_en]; unfold hl_n; lia.
Qed.

(* ------------------------------------------------------------------ II. drain's live bytes, exactly *)
(* (commit d634148958a, lib/A/W_rig_top_bytes.v td_lw .. td_bsum_out, in C3's net form: every request
   moves the live bytes by exactly its share of tr_net, so drain's potential, with the reference lines still to push,
   moves by exactly its trace's tr_net) *)
Definition rmd_lw {A : Type} (ls : list (list A)) : Z := fold_right (fun l acc => Z.of_nat (length l) + 1 + acc) 0 ls.

Lemma rmd_lw_one : forall {A} (x : list A), rmd_lw [x] = Z.of_nat (length x) + 1.
Proof. intros A x. unfold rmd_lw. cbn [fold_right]. lia. Qed.

Lemma rmd_lw_cons : forall {A} (x : list A) ls, rmd_lw (x :: ls) = Z.of_nat (length x) + 1 + rmd_lw ls.
Proof. reflexivity. Qed.

Lemma rmd_lw_app : forall {A} (l1 l2 : list (list A)), rmd_lw (l1 ++ l2) = rmd_lw l1 + rmd_lw l2.
Proof.
  intros A l1 l2. induction l1 as [|x l1 IH]; cbn [app]; [reflexivity|]. rewrite !rmd_lw_cons, IH. lia.
Qed.

Lemma rmd_lw_perm : forall {A} (l1 l2 : list (list A)), Permutation l1 l2 -> rmd_lw l1 = rmd_lw l2.
Proof. intros A l1 l2 HP. induction HP; rewrite ?rmd_lw_cons in *; lia. Qed.

Lemma rmd_lw_nonneg : forall {A} (ls : list (list A)), 0 <= rmd_lw ls.
Proof. intros A ls. induction ls as [|x ls IH]; [unfold rmd_lw; cbn [fold_right]; lia | rewrite rmd_lw_cons; lia]. Qed.

Lemma rmd_lw_map : forall {A A'} (f : A -> A') ls, rmd_lw (map (map f) ls) = rmd_lw ls.
Proof.
  intros A A' f ls. induction ls as [|x ls IH]; [reflexivity|]. cbn [map]. rewrite !rmd_lw_cons, IH, length_map.
  reflexivity.
Qed.

(* the pending texts of drain_init, as the harness list's records *)
Lemma rmd_pend_lw : forall (rs : list (Z * list byte)),
  rmd_lw (map (fun r => bzs (snd r)) rs) = rmd_lw (map snd rs).
Proof.
  intros rs. induction rs as [|r rs IH]; [reflexivity|]. cbn [map]. rewrite !rmd_lw_cons, IH.
  unfold bzs. rewrite length_map. reflexivity.
Qed.

(* the buffer's growth replaces s->buf: malloc (8192) of nothing, or realloc cap -> 2 cap *)
Lemma rmd_grow : forall c used j b,
  fst (snd (drain_b_c.grow_tr c used j b)) = c + tr_net (fst (drain_b_c.grow_tr c used j b)).
Proof.
  intros c used j b. unfold drain_b_c.grow_tr.
  destruct (c - used <? 4096); cbn [fst snd]; [|unfold tr_net; cbn [fold_right]; lia].
  destruct (Z.eqb_spec c 0); unfold tr_net; cbn [fold_right]; lia.
Qed.

(* gesture_seen: a begin grows the held array to c and adds the key's |x| + 1; an end frees the key's block *)
Lemma rmd_seen : forall H ka l j ha ks,
  snd (fst (drain_b_c.seen_tr H ka l j ha ks)) + rmd_lw (RelayKeys.seen_arr H l) =
    ka + rmd_lw H + tr_net (fst (fst (drain_b_c.seen_tr H ka l j ha ks))).
Proof.
  intros H ka l j ha ks. unfold drain_b_c.seen_tr, RelayKeys.seen_arr.
  destruct (RelayModel.gesture l) as [[[|] x]|]; [| |cbn; unfold tr_net; cbn; lia].
  - destruct (RelayKeys.index_of x H) as [n|] eqn:E; [cbn; unfold tr_net; cbn; lia|].
    cbn [fst snd]. pose proof (rmd_lw_app H [x]) as A1. pose proof (rmd_lw_one x) as A2.
    destruct (Z.eqb_spec ka 0); unfold tr_net; cbn [fold_right]; lia.
  - destruct (RelayKeys.index_of x H) as [n|] eqn:E; [|cbn; unfold tr_net; cbn; lia].
    destruct (RelayKeys.index_of_some x H n E) as (a & b & HH & Ha). subst H n.
    rewrite (rmd_lw_perm _ _ (RelayKeys.swap_remove_perm [] a x b)). cbn [fst snd].
    rewrite rmd_lw_cons. unfold tr_net; cbn [fold_right]. lia.
Qed.

(* the relayed lines: g_out's growth (send_line_tr_net), then gesture_seen, line by line *)
Lemma rmd_lines_run : forall rl live mx no cap H ka j o ha ks,
  let p := drain_b_c.lines_run live mx no cap H ka rl j o ha ks in
  fst (fst (snd (fst p))) + snd (snd (fst p)) + rmd_lw (snd (fst (snd (fst p)))) =
    cap + ka + rmd_lw H + tr_net (fst (fst p)).
Proof.
  induction rl as [|l r IH]; intros live mx no cap H ka j o ha ks; cbv zeta;
    cbn [drain_b_c.lines_run fst snd]; [unfold tr_net; cbn; lia|].
  pose proof (send_line_tr_net live mx no cap (Z.of_nat (length l) + 1) j o) as S2.
  match goal with |- context [drain_b_c.seen_tr H ka l ?jj ha ks] =>
    pose proof (rmd_seen H ka l jj ha ks) as K2 end.
  match goal with |- context [drain_b_c.lines_run live mx ?no' ?cap' ?H' ?ka' r ?j' ?o' ?ha' ?ks'] =>
    pose proof (IH live mx no' cap' H' ka' j' o' ha' ks') as I3 end.
  cbv zeta in I3. rewrite !tr_net_app. lia.
Qed.

Lemma rmd_push_tra : forall v N CAP m, tr_net (ListTr.list_push_tra v N CAP m) =
  (if N =? CAP then (if CAP =? 0 then 128 else 16 * CAP) else 0) + (m + 1).
Proof.
  intros v N CAP m. unfold ListTr.list_push_tra. rewrite tr_net_app.
  destruct (N =? CAP); [destruct (CAP =? 0)|]; unfold tr_net; cbn [fold_right]; lia.
Qed.

(* reference_feed's pushes: the expected list's array grows to push_cap, each text adds |l| + 1 *)
Lemma rmd_pushes : forall ls n cap j v rs,
  AREC * snd (fst (drain_b_c.pushes_run n cap ls j v rs)) + rmd_lw ls =
    AREC * cap + tr_net (fst (fst (drain_b_c.pushes_run n cap ls j v rs))).
Proof.
  induction ls as [|l r IH]; intros n cap j v rs; cbn [drain_b_c.pushes_run fst snd];
    [unfold rmd_lw, tr_net; cbn; lia|].
  match goal with |- context [drain_b_c.pushes_run (n + 1) ?pc r ?jj ?vv ?rr] =>
    assert (PC : AREC * pc = AREC * cap + (if n =? cap then (if cap =? 0 then 128 else 16 * cap) else 0))
      by (unfold drain_b_c.push_cap, AREC; destruct (Z.eqb_spec n cap); [destruct (Z.eqb_spec cap 0)|]; lia);
    pose proof (IH (n + 1) pc jj vv rr) as I2 end.
  rewrite tr_net_app, rmd_push_tra, rmd_lw_cons. lia.
Qed.

(* the head pending text, dropped once it is all read: its block of |r0| + 1 bytes is freed *)
Lemma rmd_drop_net : forall (b : bool) (r0 : list Z) (rs : list (list Z)) x,
  rmd_lw (if b then rs else r0 :: rs) =
  rmd_lw (r0 :: rs) + tr_net (if b then ListTr.list_drop_tra x (Z.of_nat (length r0)) else []).
Proof.
  intros [|] r0 rs x; unfold ListTr.list_drop_tra, tr_net; cbn [fold_right]; rewrite ?rmd_lw_cons; lia.
Qed.

(* the weight of drain's state: s->buf, s->held and the held keys, the expected list's vector, g_out, and the
   pending texts' blocks *)
Definition rmd_pot (s : drain_b_c.dstate) : Z :=
  drain_b_c.ds_cap s + drain_b_c.ds_ka s + rmd_lw (drain_b_c.ds_H s) + AREC * drain_b_c.ds_ecap s +
  drain_b_c.ds_ocap s + rmd_lw (drain_b_c.ds_pend s).

Lemma rmd_run : forall f live mx s j a,
  relay_instance_gone_b_lem.dr_inv s ->
  (length (relay_instance_gone_b_lem.dr_rest s) + (if drain_b_c.ds_eintr s then 2 else 1) <= f)%nat ->
  rmd_pot (fst (snd (drain_b_c.drain_run f live mx s j a))) +
    rmd_lw (RelayModel.lines (drain_b_c.ds_ref s) (relay_instance_gone_b_lem.dr_rest s)) =
  rmd_pot s + tr_net (fst (drain_b_c.drain_run f live mx s j a)).
Proof.
  induction f as [|f IH]; intros live mx [c u sk H ka ei pd off rf en ec no oc] j a INV FU;
    [destruct ei; cbn [drain_b_c.ds_eintr] in FU; lia|].
  unfold relay_instance_gone_b_lem.dr_inv in INV. unfold relay_instance_gone_b_lem.dr_rest in FU |- *.
  cbn [drain_b_c.ds_cap drain_b_c.ds_u drain_b_c.ds_skip drain_b_c.ds_H drain_b_c.ds_ka drain_b_c.ds_eintr
       drain_b_c.ds_pend drain_b_c.ds_off drain_b_c.ds_ref drain_b_c.ds_en drain_b_c.ds_ecap drain_b_c.ds_no
       drain_b_c.ds_ocap] in INV, FU |- *.
  destruct INV as (J & HC & HP).
  pose proof J as (Jk & Jw & Jl & Jz).
  pose proof (relay_instance_gone_b_lem.rig_ll_z _ Jl) as UL'.
  assert (UL'' : 0 <= Z.of_nat (length u) <= 6000) by (clear - UL'; lia).
  pose proof (relay_instance_gone_b_lem.rig_grow c (Z.of_nat (length u)) j (drain_b_c.da_buf a) HC UL'') as [G1 G2].
  pose proof (rmd_grow c (Z.of_nat (length u)) j (drain_b_c.da_buf a)) as G4.
  cbn [drain_b_c.drain_run drain_b_c.ds_cap drain_b_c.ds_u drain_b_c.ds_skip drain_b_c.ds_H drain_b_c.ds_ka
       drain_b_c.ds_eintr drain_b_c.ds_pend drain_b_c.ds_off drain_b_c.ds_ref drain_b_c.ds_en drain_b_c.ds_ecap
       drain_b_c.ds_no drain_b_c.ds_ocap].
  set (cp := fst (snd (drain_b_c.grow_tr c (Z.of_nat (length u)) j (drain_b_c.da_buf a)))) in *.
  set (tg := fst (drain_b_c.grow_tr c (Z.of_nat (length u)) j (drain_b_c.da_buf a))) in *.
  destruct ei; cbv beta iota in FU.
  - (* EINTR: the growth only *)
    match goal with |- context [drain_b_c.drain_run f live mx (drain_b_c.DS cp u sk H ka false pd off rf en ec no oc) ?jj ?aa] =>
      assert (IV : relay_instance_gone_b_lem.dr_inv (drain_b_c.DS cp u sk H ka false pd off rf en ec no oc))
        by (unfold relay_instance_gone_b_lem.dr_inv;
            cbn [drain_b_c.ds_u drain_b_c.ds_skip drain_b_c.ds_ref drain_b_c.ds_cap drain_b_c.ds_pend drain_b_c.ds_off];
            split; [exact J|]; split; [lia|exact HP]);
      pose proof (IH live mx (drain_b_c.DS cp u sk H ka false pd off rf en ec no oc) jj aa IV
                    ltac:(unfold relay_instance_gone_b_lem.dr_rest;
                          cbn [drain_b_c.ds_pend drain_b_c.ds_off drain_b_c.ds_eintr]; lia)) as E end.
    unfold relay_instance_gone_b_lem.dr_rest in E.
    cbn [drain_b_c.ds_pend drain_b_c.ds_off drain_b_c.ds_ref] in E. cbn [fst snd]. rewrite tr_net_app.
    unfold rmd_pot in E |- *.
    cbn [drain_b_c.ds_cap drain_b_c.ds_H drain_b_c.ds_ka drain_b_c.ds_ecap drain_b_c.ds_ocap drain_b_c.ds_pend] in E |- *.
    lia.
  - destruct pd as [|r0 rs].
    + (* nothing pending: the growth only, no line left *)
      cbn [relay_instance_gone_b_lem.dr_rest_of fst snd].
      assert (Z0 : rmd_lw (RelayModel.lines rf []) = 0) by reflexivity.
      unfold rmd_pot.
      cbn [drain_b_c.ds_cap drain_b_c.ds_H drain_b_c.ds_ka drain_b_c.ds_ecap drain_b_c.ds_ocap drain_b_c.ds_pend]. lia.
    + (* a data round: d read, its reference lines pushed, its relayed lines sent and seen *)
      destruct HP as [HO HF].
      match goal with |- context [Z.min ?x ?y <=? 0] => remember (Z.min x y) as nn eqn:Enn end.
      assert (NP : 0 < nn) by (rewrite Enn; lia).
      assert (NL : nn <= Z.of_nat (length r0) - off) by (rewrite Enn; lia).
      destruct (Z.leb_spec nn 0) as [X|X]; [lia|]. clear X.
      set (d := firstn (Z.to_nat nn) (skipn (Z.to_nat off) r0)) in *.
      pose proof (RelayModel.chunk_ok u sk rf d J) as CK.
      destruct (RelayModel.chunk u sk d) as [[u' sk'] rl] eqn:ECH.
      destruct CK as [Erl J'].
      set (PEND := if off + nn =? Z.of_nat (length r0) then rs else r0 :: rs) in *.
      set (OFF := if off + nn =? Z.of_nat (length r0) then 0 else off + nn) in *.
      assert (RS : relay_instance_gone_b_lem.dr_rest_of (r0 :: rs) off =
                   d ++ relay_instance_gone_b_lem.dr_rest_of PEND OFF /\
                   relay_instance_gone_b_lem.dr_pend_ok PEND OFF).
      { unfold PEND, OFF, d. cbn [relay_instance_gone_b_lem.dr_rest_of].
        destruct (Z.eqb_spec (off + nn) (Z.of_nat (length r0))) as [W|W].
        - split.
          + rewrite firstn_all2 by (rewrite length_skipn; lia). f_equal.
            destruct rs as [|r1 rs1]; reflexivity.
          + destruct rs as [|r1 rs1]; [exact I|]. inversion HF as [|? ? HF1 HF2]; subst.
            cbn [relay_instance_gone_b_lem.dr_pend_ok]. split; [lia | exact HF2].
        - split.
          + cbn [relay_instance_gone_b_lem.dr_rest_of].
            replace (Z.to_nat (off + nn)) with (Z.to_nat nn + Z.to_nat off)%nat by lia.
            rewrite <- skipn_skipn, app_assoc, firstn_skipn. reflexivity.
          + cbn [relay_instance_gone_b_lem.dr_pend_ok]. split; [lia | exact HF]. }
      destruct RS as [RS1 RS2].
      assert (IVG : forall H' ka' en' ec' no' oc',
                 relay_instance_gone_b_lem.dr_inv
                   (drain_b_c.DS cp u' sk' H' ka' false PEND OFF (RelayModel.feed rf d) en' ec' no' oc')).
      { intros. unfold relay_instance_gone_b_lem.dr_inv.
        cbn [drain_b_c.ds_u drain_b_c.ds_skip drain_b_c.ds_ref drain_b_c.ds_cap drain_b_c.ds_pend drain_b_c.ds_off].
        split; [exact J'|]. split; [lia | exact RS2]. }
      assert (FUG : forall H' ka' en' ec' no' oc',
                 (length (relay_instance_gone_b_lem.dr_rest
                            (drain_b_c.DS cp u' sk' H' ka' false PEND OFF (RelayModel.feed rf d) en' ec' no' oc')) +
                  (if drain_b_c.ds_eintr
                        (drain_b_c.DS cp u' sk' H' ka' false PEND OFF (RelayModel.feed rf d) en' ec' no' oc')
                   then 2 else 1) <= f)%nat).
      { assert (DL : length d = Z.to_nat nn)
          by (unfold d; rewrite firstn_length_le by (rewrite length_skipn; lia); reflexivity).
        intros. unfold relay_instance_gone_b_lem.dr_rest. cbn [drain_b_c.ds_pend drain_b_c.ds_off drain_b_c.ds_eintr].
        rewrite RS1, length_app in FU. lia. }
      match goal with |- context [drain_b_c.pushes_run en ec (RelayModel.lines rf d) ?jj ?vv ?rr] =>
        pose proof (rmd_pushes (RelayModel.lines rf d) en ec jj vv rr) as P2 end.
      match goal with |- context [drain_b_c.lines_run live mx no oc H ka rl ?j3 ?o3 ?h3 ?k3] =>
        pose proof (rmd_lines_run rl live mx no oc H ka j3 o3 h3 k3) as LR;
        destruct (drain_b_c.lines_run live mx no oc H ka rl j3 o3 h3 k3) as [[t1 [[oc1 H1] ka1]] [[o1 ha1] ks1]] end.
      cbn [fst snd] in LR |- *.
      match goal with |- context [drain_b_c.drain_run f live mx (drain_b_c.DS _ _ _ _ _ _ _ _ _ ?en' ?ec' ?no' _) ?jj ?aa] =>
        pose proof (IH live mx _ jj aa (IVG H1 ka1 en' ec' no' oc1) (FUG H1 ka1 en' ec' no' oc1)) as E end.
      unfold relay_instance_gone_b_lem.dr_rest in E.
      cbn [drain_b_c.ds_pend drain_b_c.ds_off drain_b_c.ds_ref] in E.
      rewrite RS1, RelayModel.lines_app, rmd_lw_app, !tr_net_app.
      match goal with |- context [tr_net (if ?b then ListTr.list_drop_tra ?x _ else [])] =>
        pose proof (rmd_drop_net b r0 rs x) as TD end.
      unfold rmd_pot in E |- *.
      cbn [drain_b_c.ds_cap drain_b_c.ds_H drain_b_c.ds_ka drain_b_c.ds_ecap drain_b_c.ds_ocap drain_b_c.ds_pend] in E |- *.
      unfold PEND in *.
      lia.
Qed.

(* drain_go from drain_init: the reference lines of the pending stream are all pushed *)
Lemma rmd_drain : forall live mx no cap e h,
  relay_instance_gone_b_lem.dr_inv (drain_b_c.drain_init no cap e h) ->
  relay_instance_gone_b_lem.dr_rest (drain_b_c.drain_init no cap e h) = bzs (pending_stream h) ->
  rmd_pot (drain_b_c.drain_fin live mx no cap e h) + rmd_lw (RelayModel.lines (hs_state h) (bzs (pending_stream h))) =
    rmd_pot (drain_b_c.drain_init no cap e h) + tr_net (drain_b_c.drain_tr live mx no cap e h 0 drain_b_c.dadr0).
Proof.
  intros live mx no cap e h IV ER.
  assert (FU : (length (relay_instance_gone_b_lem.dr_rest (drain_b_c.drain_init no cap e h)) +
                (if drain_b_c.ds_eintr (drain_b_c.drain_init no cap e h) then 2 else 1)
                <= S (S (length (pending_stream h))))%nat).
  { rewrite ER. unfold bzs. rewrite length_map. destruct (drain_b_c.ds_eintr _); lia. }
  pose proof (rmd_run (S (S (length (pending_stream h)))) live mx (drain_b_c.drain_init no cap e h) 0 drain_b_c.dadr0
                IV FU) as E.
  rewrite ER in E. change (drain_b_c.ds_ref (drain_b_c.drain_init no cap e h)) with (hs_state h) in E.
  unfold drain_b_c.drain_fin, drain_b_c.drain_tr, drain_b_c.drain_go. exact E.
Qed.

(* rmd_drain at drain's names in W_contract.v *)
Lemma rmd_drain_dr : forall c mx no cap e h,
  relay_instance_gone_b_lem.dr_inv (drain_b_c.drain_init no cap e h) ->
  relay_instance_gone_b_lem.dr_rest (drain_b_c.drain_init no cap e h) = bzs (pending_stream h) ->
  rmd_pot (dr_fin c mx no cap e h) + rmd_lw (dr_lines h) =
    rmd_pot (drain_b_c.drain_init no cap e h) + tr_net (dr_tr c mx no cap e h).
Proof. intros c mx no cap e h IV ER. exact (rmd_drain (dr_live c h) mx no cap e h IV ER). Qed.

(* a dead drain keeps g_capout *)
Lemma rmd_ocap : forall c mx no cap e h,
  (if dr_live c h then drain_b_c.ds_ocap (dr_fin c mx no cap e h) else cap) = drain_b_c.ds_ocap (dr_fin c mx no cap e h).
Proof.
  intros c mx no cap e h. unfold dr_fin. destruct (dr_live c h); [reflexivity|].
  destruct (relay_instance_gone_b_lem.rig_drain_false mx no no cap e h 0 drain_b_c.dadr0) as (_ & _ & _ & X).
  symmetry. exact X.
Qed.

(* the bytes of the blocks W_rep.v represents an entry, a source and g_out over *)
Lemma rmd_bsum_keys : forall ks,
  bsum (map (fun k => (key_addr k, Z.of_nat (length (key_text k)) + 1)) ks) = rmd_lw (drain_b_c.keys_texts ks).
Proof.
  intros ks. unfold drain_b_c.keys_texts. induction ks as [|k ks IH]; [reflexivity|].
  cbn [map]. rewrite bsum_cons, rmd_lw_cons, IH. cbn [snd]. unfold bzs. rewrite length_map. reflexivity.
Qed.

Lemma rmd_bsum_recs : forall (rs : list (Z * list byte)),
  bsum (map (fun r => (fst r, Z.of_nat (length (snd r)) + 1)) rs) = rmd_lw (map snd rs).
Proof.
  intros rs. induction rs as [|r rs IH]; [reflexivity|]. cbn [map]. rewrite bsum_cons, rmd_lw_cons, IH. reflexivity.
Qed.

Lemma rmd_bsum_entry : forall e,
  bsum (aentry_blks e) = re_cap e + drain_b_c.ent_ka e + rmd_lw (drain_b_c.keys_texts (re_keys e)).
Proof.
  intros e. unfold aentry_blks, drain_b_c.ent_ka. rewrite !bsum_app, rmd_bsum_keys.
  destruct (Z.eqb_spec (re_cap e) 0); destruct (Z.eqb_spec (re_hp e) 0); cbn [bsum fold_right snd]; lia.
Qed.

Lemma rmd_bsum_list : forall l, bsum (alist_blks l) = AREC * hl_cap l + rmd_lw (map snd (hl_recs l)).
Proof.
  intros l. unfold alist_blks. rewrite bsum_app, rmd_bsum_recs. unfold AREC.
  destruct (Z.eqb_spec (hl_cap l) 0); cbn [bsum fold_right snd]; lia.
Qed.

Lemma rmd_bsum_src : forall h, bsum (asrc_blks h) =
  APARTIAL + bsum (alist_blks (hs_pending h)) + bsum (alist_blks (hs_expected h)) + bsum (alist_blks (hs_held h)).
Proof. intros h. unfold asrc_blks. rewrite bsum_cons, !bsum_app. cbn [snd]. lia. Qed.

Lemma rmd_bsum_out : forall cap out, bsum (aout_blks cap out) = cap.
Proof. intros cap out. unfold aout_blks. destruct (Z.eqb_spec cap 0); cbn [bsum fold_right snd]; lia. Qed.

(* ------------------------------------------------------------------ III. lists *)
Lemma rmd_concat_split : forall {X : Type} (f : X -> list byte) (l : list X) (d : X) (i : nat),
  (i < length l)%nat ->
  concat (map f l) = concat (map f (firstn i l)) ++ f (nth i l d) ++ concat (map f (skipn (S i) l)).
Proof.
  intros X f l d. induction l as [|x l IH]; intros i Hi; cbn [length] in Hi; [lia|].
  destruct i as [|i]; cbn [firstn skipn nth map concat].
  - reflexivity.
  - rewrite (IH i ltac:(cbn [length] in Hi; lia)) at 1. cbn [map concat]. rewrite app_assoc. reflexivity.
Qed.
Lemma rmd_eb_len : forall e, length (re_pad1 e) = 4%nat -> length (re_pad2 e) = 4%nat ->
  length (entry_bytes e) = 56%nat.
Proof.
intros e P1 P2. unfold entry_bytes.
rewrite !length_app, !OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Lib.Mem.length_le4,
  !OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Lib.Mem.length_le8, P1, P2. reflexivity.
Qed.
Lemma rmd_concat_len : forall l, Forall (fun e => length (re_pad1 e) = 4%nat /\ length (re_pad2 e) = 4%nat) l ->
  length (concat (map entry_bytes l)) = (56 * length l)%nat.
Proof.
induction l as [|e l IH]; intros HF; [reflexivity|].
apply Forall_cons_iff in HF as [[P1 P2] HF]. cbn [map concat length]. rewrite length_app, (rmd_eb_len e P1 P2), (IH HF). lia.
Qed.
(* the blocks of a list, permuted *)
Lemma rmd_perm_cmap : forall {X Y : Type} (f : X -> list Y) l l', Permutation l l' ->
  Permutation (concat (map f l)) (concat (map f l')).
Proof.
intros X Y f l l' H. induction H; cbn [map concat].
- constructor.
- apply Permutation_app_head. exact IHPermutation.
- rewrite !app_assoc. apply Permutation_app_tail, Permutation_app_comm.
- eapply perm_trans; eassumption.
Qed.
(* the blocks of the table's entries: entry i's, then the others' *)
Lemma rmd_blks_split : forall es i, (i < length es)%nat ->
  Permutation (concat (map aentry_blks es))
    (aentry_blks (nth i es relay_remove_b_c.no_entry) ++ concat (map aentry_blks (relay_remove_b_c.remove_at i es))).
Proof.
intros es i Hi. pose proof (rm_remove_perm es i relay_remove_b_c.no_entry Hi) as HP.
apply (rmd_perm_cmap aentry_blks) in HP. cbn [map concat] in HP. exact HP.
Qed.

Lemma rmd_nodup_app_disj : forall {X : Type} (A B : list X) x, List.NoDup (A ++ B) -> In x B -> ~ In x A.
Proof.
intros X A. induction A as [|a A IH]; intros B x H Hx Ha; [destruct Ha|]. cbn [app] in H.
inversion H as [|? ? Hn Hd]; subst. destruct Ha as [<-|Ha]; [apply Hn; apply in_or_app; right; exact Hx|].
exact (IH B x Hd Hx Ha).
Qed.
Lemma rmd_nodup_mid : forall {X : Type} (A OB R : list X) T, List.NoDup (A ++ T :: OB ++ R) ->
  ~ In T A /\ ~ In T OB /\ (forall b, In b OB -> ~ In b A).
Proof.
intros X A OB R T H. pose proof (NoDup_remove_2 A (OB ++ R) T H) as N1. pose proof (NoDup_remove_1 A (OB ++ R) T H) as N2.
split; [intros Ha; apply N1; apply in_or_app; left; exact Ha|].
split; [intros Ho; apply N1; apply in_or_app; right; apply in_or_app; left; exact Ho|].
intros b Hb Ha. exact (rmd_nodup_app_disj A (OB ++ R) b N2 (in_or_app _ _ _ (or_introl Hb)) Ha).
Qed.
(* W_rr_tail.v rr_bzs_len / rr_key_ptrs_len, copied *)
Lemma rmd_bzs_len : forall l, Z.of_nat (length (bzs l)) = Z.of_nat (length l).
Proof. intros l. unfold bzs. rewrite length_map. reflexivity. Qed.
Lemma rmd_key_ptrs_len : forall ks, length (key_ptrs ks) = (8 * length ks)%nat.
Proof.
induction ks as [|k ks IH]; [reflexivity|].
unfold key_ptrs in *. cbn [map concat].
rewrite length_app, IH, OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Lib.Mem.length_le8. cbn [length]. lia.
Qed.
(* the block lists of the matched entry: the entry's form (RHELD) against drain's (dr_spec / dr_post) *)
Lemma rmd_perm_pre : forall {X : Type} (T : X) Ae OB SB O0 R,
  Permutation (T :: (Ae ++ OB) ++ SB ++ O0 ++ R) (Ae ++ SB ++ O0 ++ T :: OB ++ R).
Proof.
intros X T Ae OB SB O0 R.
pose proof (Permutation_middle (Ae ++ SB ++ O0) (OB ++ R) T) as M. rewrite <- !app_assoc in M.
eapply perm_trans; [|exact M]. apply perm_skip. rewrite <- !app_assoc. apply Permutation_app_head.
rewrite (app_assoc SB O0 (OB ++ R)), (app_assoc SB O0 R). apply Permutation_app_swap_app.
Qed.
Lemma rmd_perm_post : forall {X : Type} (L : list X) T Ae OB Sh Oc R rest,
  Permutation L (Ae ++ Sh ++ Oc ++ rest) -> Permutation rest (T :: OB ++ R) ->
  Permutation L (T :: Ae ++ OB ++ Sh ++ Oc ++ R).
Proof.
intros X L T Ae OB Sh Oc R rest H1 H2. eapply perm_trans; [exact H1|].
eapply perm_trans; [do 3 apply Permutation_app_head; exact H2|].
pose proof (Permutation_middle (Ae ++ Sh ++ Oc) (OB ++ R) T) as M. rewrite <- !app_assoc in M.
eapply perm_trans; [apply Permutation_sym; exact M|]. apply perm_skip. apply Permutation_app_head.
rewrite (app_assoc Sh Oc (OB ++ R)), (app_assoc Sh Oc R). apply Permutation_app_swap_app.
Qed.
Lemma rmd_perm_rest : forall {X : Type} (L : list X) T Ae OB Sh Oc R rest,
  Permutation L (Ae ++ Sh ++ Oc ++ rest) -> Permutation L (Ae ++ Sh ++ Oc ++ T :: OB ++ R) ->
  Permutation rest (T :: OB ++ R).
Proof.
intros X L T Ae OB Sh Oc R rest H1 H2.
apply (Permutation_app_inv_l Oc), (Permutation_app_inv_l Sh), (Permutation_app_inv_l Ae).
eapply perm_trans; [apply Permutation_sym; exact H1 | exact H2].
Qed.
(* the count of a drain-form block list: drain's three parts, then the rest *)
Lemma rmd_acnt3 : forall (P : Z -> bool) (A B C R : list (Z * Z)),
  ReplyCnt.acnt P (A ++ B ++ C ++ R) = (ReplyCnt.acnt P (A ++ B ++ C) + ReplyCnt.acnt P R)%nat.
Proof. intros P A B C R. rewrite !app_assoc. apply ReplyCnt.acnt_app. Qed.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section b.
Context {PI : PAImg fr_prog_listing}.
#[local] Notation SEGS := (@pa_segs _ fr_prog_listing PI).
#[local] Notation VAL := (@pa_val _ fr_prog_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ fr_prog_listing PI).
#[local] Notation BASE := (@pa_val _ fr_prog_listing PI A_TEXT).

(* W_rr_scan.v rrs_nth_le_bytes / rrs_garr8_le, copied *)
Lemma rmd_nth_le_bytes : forall n z k, (k < n)%nat ->
  nth k (Z_to_le_bytes n z) (Z_to_bv 8 0) = Z_to_bv 8 (Z.shiftr z (8 * Z.of_nat k)).
Proof.
induction n as [|n IH]; intros z k Hk; [lia|].
destruct k as [|k]; cbn [Z_to_le_bytes nth].
- change (8 * Z.of_nat 0) with 0. rewrite Z.shiftr_0_r. reflexivity.
- rewrite IH by lia. rewrite Z.shiftr_shiftr by lia. f_equal. f_equal. lia.
Qed.
Lemma rmd_garr8_le : forall m a n z, garr8 SEGS m a (bzs (Z_to_le_bytes n z)) -> 0 <= z < 2 ^ (8 * Z.of_nat n) ->
  val_mem SEGS m a n z.
Proof.
intros m a n z Hg Hz k Hk.
assert (Hl : (k < length (bzs (Z_to_le_bytes n z)))%nat) by (unfold bzs; rewrite length_map, length_Z_to_le_bytes; exact Hk).
destruct (Hg k Hl) as [Hv _]. specialize (Hv 0%nat ltac:(lia)). change (Z.of_nat 0) with 0 in Hv. rewrite Z.add_0_r in Hv.
rewrite Hv. apply f_equal.
unfold bzs. rewrite (nth_indep _ 0 (bz (Z_to_bv 8 0))) by (rewrite length_map, length_Z_to_le_bytes; exact Hk).
rewrite map_nth, rmd_nth_le_bytes by exact Hk. unfold bz.
apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256.
unfold YO0f.le_byte. replace (8 * Z.of_nat 1) with 8 by lia. replace (8 * Z.of_nat 0) with 0 by lia. rewrite Z.shiftr_0_r.
lazymatch goal with |- context [z mod 2 ^ ?w] => rewrite (Z.mod_small z (2 ^ w)) by lia end.
change (2 ^ 8) with 256. rewrite !Z.mod_mod by lia. reflexivity.
Qed.

(* entry k's eof field: bytes 4 .. 8 of its 56 at G + 56 k (W_rr_scan.v rrs_fd_cell at the next field) *)
Lemma rmd_eof_cell : forall M G es tail k,
  garr8 SEGS M G (bzs (concat (map entry_bytes es) ++ tail)) ->
  Forall (fun e => length (re_pad1 e) = 4%nat /\ length (re_pad2 e) = 4%nat) es ->
  (k < length es)%nat -> 0 <= re_eof (nth k es relay_remove_b_c.no_entry) < 2 ^ 31 ->
  val_mem SEGS M (G + AENT * Z.of_nat k + 4) 4 (re_eof (nth k es relay_remove_b_c.no_entry)).
Proof.
intros M G es tail k Hg HF Hk Hev.
rewrite (rmd_concat_split entry_bytes es relay_remove_b_c.no_entry k Hk) in Hg.
unfold bzs in Hg. rewrite !map_app in Hg.
apply garr8_app in Hg as [Hg _]. apply garr8_app in Hg as [_ Hg]. apply garr8_app in Hg as [Hg _].
assert (HF1 : Forall (fun e => length (re_pad1 e) = 4%nat /\ length (re_pad2 e) = 4%nat) (firstn k es)).
{ rewrite <- (firstn_skipn k es) in HF. apply Forall_app in HF as [HF1 _]. exact HF1. }
rewrite length_map, (rmd_concat_len _ HF1), length_firstn in Hg.
replace (Nat.min k (length es)) with k in Hg by lia.
unfold entry_bytes in Hg. rewrite map_app in Hg. apply garr8_app in Hg as [_ Hg].
rewrite map_app in Hg. apply garr8_app in Hg as [Hg _].
rewrite length_map, OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Lib.Mem.length_le4 in Hg.
replace (G + AENT * Z.of_nat k + 4) with (G + Z.of_nat (56 * k) + Z.of_nat 4) by (unfold AENT; lia).
apply rmd_garr8_le; [|lia].
unfold OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Lib.Mem.le4 in Hg.
rewrite unsigned_lit_small in Hg by lia. exact Hg.
Qed.

(* ------------------------------------------------------------------ the symbolic state at 0x83f48 *)
(* a0 = SA = G0 + 56 i (atom 10), s6 = SB (22); atom 32 = entry i's eof.  The region on the slot atom holds the
   eof field at offset 4; the shadow entry over the slot's 56 bytes takes the check's fast path. *)
Definition RRD_PHI : Z := 140737479966720.
Definition rrd_Bx : sv := SOff 22 0.
Definition rrd_regions : smem := [ YP09.mkRegion (Some 10%nat) 0 8 0 0 [YP09.mkChunk 4 (CVal 4 (SOff 32 0))] ].
Definition rrd_facts : facts :=
mkFacts [ (10%nat, mkAF 4096 RRD_PHI 3); (22%nat, mkAF SB SB 0); (32%nat, mkAF 0 (2 ^ 31 - 1) 0) ] [] [].
Definition ss_rrd : sstate := mkSS A_rr_match sr_atoms rrd_regions None rrd_facts.
Definition rrd_SH : list shent := [ mkSHE 10 0 56 ].
Definition rrd_Bspan : Z * Z := (SB, SB + 2 ^ 44 - 1).
Definition rrd_extra (ev : Z) : list word := map (Z_to_bv 64) [ev].
Definition RRD_KEPT : list (bv 5) := [2; 3; 4; 8; 9; 10; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv.

(* a register of RRD_KEPT that the callee saves (YG0d.v acallee_saved: sp, gp, tp, s0 .. s11) *)
Ltac rrd_cs := first [cbv; tauto | unfold acallee_saved; vm_compute;
  first [lia | right; right; right; right; right; split; discriminate]].

Ltac rrd_mem Em :=
lazymatch goal with HF : frame_of ?E ?rs ?m (ms_mem ?x) |- _ =>
  pose proof (frame_of_read_only E rs m (ms_mem x) ltac:(vm_compute; reflexivity) HF) as Em end;
repeat match goal with Hx : frame_of _ _ _ _ |- _ => clear Hx | Hx : mem_grows _ _ |- _ => clear Hx end.

(* the key run and the two frees after the matched entry's drain ask nonnegative sizes *)
Lemma rmd_tl_nn : forall cx i, 0 <= rxmx cx -> rmd_nn (rmtrK cx i ++ rmtrF cx i).
Proof.
intros cx i Hmx. apply rmd_nn_app.
- unfold rmtrK. apply rmd_ker_nn; [exact Hmx | |].
  + unfold rms. destruct (rmopen cx i).
    * pose proof (proj1 (RelayCap.drain_ocap_le (dr_live (rxc cx) (rxh cx)) (rxmx cx) (rmno cx) (rxcap cx) (rnth cx i)
                          (rxh cx))) as N.
      unfold dr_fin. unfold rmno in *. lia.
    * cbn [drain_b_c.drain_init drain_b_c.ds_no]. unfold rmno. lia.
  + apply Forall_map. apply Forall_forall. intros x _. cbn [fst]. lia.
- unfold rmtrF, rmd_nn. repeat constructor.
Qed.

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

(* ------------------------------------------------------------------ the meter's laws, the held array, the slot *)
(* the counting meter's laws (commit 3d17f490d56, lib/A/W_relay_finish_h.v rfl_rk_laws, verbatim) *)
Lemma rmd_rk_laws : ameter_laws MT_rk.
Proof. constructor; cbn [mo_ok mo_le mo_malloc mo_free MT_rk]; intros; solve [exact I | lia]. Qed.
(* an entry's held array: no pointer, or a block of nonzero size (aentry_ok's held-array clause, 8 <= re_kh) *)
Lemma rmd_held_ok : forall ly S W mem e, aentry_ok B ly S W mem e -> re_hp e = 0 \/ re_kh e <> 0.
Proof.
intros ly S W mem e (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HK & _).
destruct HK as [(Hz & _) | (_ & _ & _ & H8 & _)]; [left; exact Hz | right; lia].
Qed.
(* a slot of the table block is 8-aligned: every live block is 16-aligned (commit 3d17f490d56, lib/A/W_drain_sa.v
   dr_sa_align_slot, over alx_blocks) *)
Lemma rmd_sa_align : forall ly S Hp W mem md (G : Z) (i : nat),
  ARx ly S Hp W mem md -> In (G, ATABLE) (ablocks B ly S) -> (G + AENT * Z.of_nat i) mod 8 = 0.
Proof.
intros ly S Hp W mem md G i HAR Hin.
destruct (alx_blocks _ _ _ LAWS ly S Hp W mem md G ATABLE HAR Hin) as (H16 & _).
apply Z.mod_divide in H16; [|lia]. destruct H16 as (k & ->).
unfold AENT. apply Z.mod_divide; [lia|]. exists (2 * k + 7 * Z.of_nat i). lia.
Qed.

(* ------------------------------------------------------------------ what a callee's journal keeps *)
(* a byte of a block live before and after, outside the callee's footprint *)
Lemma rmd_blk_kept : forall Gc XO OUT STK sp0 FP ly S Hp W mem md own ly' S' Hp' W' mem' md' k p n a,
  gx_ok SEGS B Gc ->
  ajournal_gx_x (SK := SK) SEGS B PST ARx Gc XO OUT STK sp0 FP ly S Hp W mem md own ly' S' Hp' W' mem' md' k ->
  ARx ly S Hp W mem md -> In (p, n) (ablocks B ly S) -> In (p, n) (ablocks B ly' S') ->
  p <= a < p + req_size n -> ~ inFP FP a -> aview SEGS (w_H W') mem' a = aview SEGS (w_H W) mem a.
Proof.
intros Gc XO OUT STK sp0 FP ly S Hp W mem md own ly' S' Hp' W' mem' md' k p n a HGc HJ HAR H1 H2 Ha HnF.
pose proof asan_consts as (C1 & _).
destruct (alx_blocks _ _ _ LAWS ly S Hp W mem md p n HAR H1) as (_ & H4096 & Hceil & _).
pose proof HJ as HJin. apply ajournal_gx_inner_x in HJin. destruct HJin as (memS & HJi & HAG).
pose proof HJi as (_ & _ & _ & _ & _ & _ & _ & _ & _ & HBLK & _).
replace a with (p + (a - p)) by lia.
rewrite (HBLK p n (a - p) H1 H2 ltac:(lia) ltac:(replace (p + (a - p)) with a by lia; exact HnF)).
apply HAG. rewrite unsigned_lit_small by lia. intros Hg.
apply (blk_img_x SEGS B ARx LAWS ly S Hp W mem md p n (p + (a - p)) HAR H1 ltac:(lia)). exact (proj1 (HGc _ Hg)).
Qed.
(* a byte of a block not named by a footprint of other blocks is outside it (the blocks are apart) *)
Lemma rmd_notin_fp : forall ly S Hp W mem md X p n a,
  ARx ly S Hp W mem md -> In (p, n) (ablocks B ly S) -> ~ In (p, n) X ->
  (forall b, In b X -> In b (ablocks B ly S)) -> p <= a < p + req_size n -> ~ inFP (ablocks_fp X) a.
Proof.
intros ly S Hp W mem md X p n a HAR Hin HnX HX Ha Hf.
apply inFP_ablocks_fp_inv in Hf as (q & m & Hq & Hr).
assert (Hne : (p, n) <> (q, m)) by (intros E; rewrite E in HnX; exact (HnX Hq)).
pose proof (sep_blocks_x SEGS B ARx LAWS ly S Hp W mem md p n q m HAR Hin (HX _ Hq) Hne) as D.
unfold zdisjoint in D. cbn [fst snd] in D. lia.
Qed.
(* the bytes an entry's representation reads lie in its own blocks (W_rr_tail.v rfz_aentry, adapted) *)
Lemma rmd_aentry_fp : forall ly S W mem e, aentry_ok B ly S W mem e ->
  forall r, In r (aentry_fp e) -> forall a, fst r <= a < snd r ->
  exists p n, In (p, n) (aentry_blks e) /\ p <= a < p + req_size n.
Proof.
intros ly S W mem e (K1 & K2 & K3 & K4 & K5 & K6 & K7 & K8 & K9 & K10 & K11 & K12 & K13 & K14 & K15).
rewrite Forall_forall in K15.
assert (BL : forall p n len a, In (p, n) (aentry_blks e) -> 0 <= n -> len <= n -> p <= a < p + len ->
  exists p' n', In (p', n') (aentry_blks e) /\ p' <= a < p' + req_size n').
{ intros p n len a Hin Hn Hl Ha. exists p, n. split; [exact Hin|]. pose proof (req_size_pos n Hn) as [_ Hr]. lia. }
unfold aentry_fp. intros r Hr a Ha. apply in_app_or in Hr as [Hr | Hr].
- destruct (Z.eqb_spec (re_cap e) 0) as [Hc|Hc]; [destruct Hr|].
  destruct K10 as [(Hc0 & _) | (Hcp & Hin & Hj & Hg)]; [lia|].
  destruct Hr as [<- | []]. cbn [gfp fst snd] in Ha.
  rewrite rmd_bzs_len, length_app, Nat2Z.inj_add, Hj, K7 in Ha.
  apply (BL (re_buf e) (re_cap e) (re_cap e) a); [|lia|lia|lia].
  unfold aentry_blks. apply in_or_app. left. rewrite (proj2 (Z.eqb_neq _ _) Hc). left. reflexivity.
- destruct Hr as [<- | Hr].
  + cbn [gfp fst snd] in Ha. rewrite rmd_bzs_len, rmd_key_ptrs_len in Ha.
    destruct K12 as [(Hz & Hks) | (Hz & Hin & Hk1 & Hk2 & Hg)].
    { rewrite Hks in Ha. cbn [length] in Ha. lia. }
    unfold re_nheld in Hk1.
    apply (BL (re_hp e) (re_kh e) (Z.of_nat (8 * length (re_keys e))) a); [|lia|lia|lia].
    unfold aentry_blks. apply in_or_app. right. apply in_or_app. left.
    rewrite (proj2 (Z.eqb_neq _ _) Hz). left. reflexivity.
  + apply in_map_iff in Hr as (k & <- & Hk). cbn [gfp fst snd] in Ha.
    rewrite rmd_bzs_len, length_app in Ha. cbn [length] in Ha.
    apply (BL (key_addr k) (Z.of_nat (length (key_text k)) + 1) (Z.of_nat (length (key_text k)) + 1) a);
      [|lia|lia|lia].
    unfold aentry_blks. apply in_or_app. right. apply in_or_app. right.
    apply in_map_iff. exists k. split; [reflexivity | exact Hk].
Qed.
Lemma rmd_abk_trans : forall (W W1 W2 : world SEGS) m m1 m2 a,
  abyte_kept W m W1 m1 a -> abyte_kept W1 m1 W2 m2 a -> abyte_kept W m W2 m2 a.
Proof. intros W W1 W2 m m1 m2 a (A1 & B1) (A2 & B2). split; [rewrite A2; exact A1 | intros Hw; exact (B2 (B1 Hw))]. Qed.

(* ------------------------------------------------------------------ drain's post at the return state *)
(* dr_post_x's body (W_contract_x.v dr_post_x, verbatim) at the return state's layout, astate, head set, world,
   registers, memory and model, so that gse_callS_x's continuation can carry it *)
Definition rrd_drp (regs : bvmap 5 word) ly S (Hp : list Z) (W : world SEGS) (mem : word -> option byte) (md : Model)
(SA HA : Z) (e : rentry) (h : hsrc) (c : ctl) (O : list byte) (mx no cap out : Z) (kr : nat)
(ly' : alayout) (S' : astate) (Hp' : list Z) (W' : world SEGS) (regs' : bvmap 5 word) (mem' : word -> option byte)
(md' : Model) : Prop :=
exists k (e' : rentry) (h' : hsrc) (out' ev' : Z) (LB : list byte) rest,
let fin := dr_fin c mx no cap e h in
let live := dr_live c h in
let cap' := if live then drain_b_c.ds_ocap fin else cap in
ajournal_gx_x (SK := SK) SEGS B PST ARx (G_DR B RG) 0 [] DRAIN_STK_x (spZ regs) (dr_fp SA e h cap out)
  ly S Hp W mem md [] ly' S' Hp' W' mem' md' k /\
aregs_preserved regs regs' /\
apres_kept B W mem W' mem' /\
mo_le MT S S' (dr_cost MT c mx no cap e h) /\
rp_RM RP S' kr /\
Permutation (ablocks B ly S) (aentry_blks e ++ asrc_blks h ++ aout_blks cap out ++ rest) /\
Permutation (ablocks B ly' S') (aentry_blks e' ++ asrc_blks h' ++ aout_blks cap' out' ++ rest) /\
garr8 SEGS (arm W' mem') SA (bzs (entry_bytes e')) /\ awr W' mem' SA AENT /\ aentry_ok B ly' S' W' mem' e' /\
re_fd e' = re_fd e /\ re_eof e' = (if hs_closed h =? 1 then 1 else re_eof e) /\ 0 < re_cap e' /\
re_cap e' = drain_b_c.ds_cap fin /\ bzs (re_U e') = drain_b_c.ds_u fin /\
re_skip e' = (if drain_b_c.ds_skip fin then 1 else 0) /\
drain_b_c.keys_texts (re_keys e') = drain_b_c.ds_H fin /\ drain_b_c.ent_ka e' = drain_b_c.ds_ka fin /\
((re_hp e' = re_hp e /\ re_kh e' = re_kh e) \/ re_kh e' <= 2 ^ 30) /\
NoDup (drain_b_c.keys_texts (re_keys e')) /\
RelayKeys.same_set (drain_b_c.keys_texts (re_keys e')) (RelayModel.upds (drain_b_c.keys_texts (re_keys e)) (dr_lines h)) /\
asrc_at B ly' S' W' mem' HA h' /\
(forall a, rg_s RG <= a < rg_s RG + 4 * ASRC -> ~ (HA <= a < HA + ASRC) -> abyte_kept W mem W' mem' a) /\
hl_cap (hs_expected h') = drain_b_c.ds_ecap fin /\
hl_cap (hs_expected h') <= Z.max 8 (Z.max (hl_cap (hs_expected h)) (2 * hl_n (hs_expected h'))) /\
hs_fd h' = hs_fd h /\ hs_closed h' = hs_closed h /\ hs_eintr h' = 0 /\
hl_recs (hs_pending h') = [] /\ hs_off h' = 0 /\
hl_v (hs_pending h') = hl_v (hs_pending h) /\ hl_cap (hs_pending h') = hl_cap (hs_pending h) /\
hs_partial h' = hs_partial h /\
hs_state h' = RelayModel.feed (hs_state h) (bzs (pending_stream h)) /\
map snd (hl_recs (hs_expected h')) = map snd (hl_recs (hs_expected h)) ++ map (map (Z_to_bv 8)) (dr_lines h) /\
firstn (length (hl_recs (hs_expected h))) (hl_recs (hs_expected h')) = hl_recs (hs_expected h) /\
hs_held h' = hs_held h /\
re_skip e' = hs_overlong h' /\ (re_skip e' = 0 -> bzs (re_U e') = bzs (hs_W h')) /\
bzs LB = RelayModel.with_nul (dr_lines h) /\
aout_at B RG ly' S' W' mem' (dr_ctl c h ev') (if live then O ++ LB else O) mx (if live then no + dr_tot h else no) cap' out'.
Lemma rrd_drp_of : forall regs ly S Hp W mem md SA HA e h c O mx no cap out kr W' c',
  dr_post_x B PST ARx MT RP RG regs ly S Hp W mem md SA HA e h c O mx no cap out kr W' c' ->
  exists ly' S' Hp' regs' mem' md', c' = mkCfg (mkst regs' (getr regs 1) mem' (seg_rom SEGS)) md' /\
  rrd_drp regs ly S Hp W mem md SA HA e h c O mx no cap out kr ly' S' Hp' W' regs' mem' md'.
Proof.
intros regs ly S Hp W mem md SA HA e h c O mx no cap out kr W' c' H.
destruct H as (ly' & S' & Hp' & regs' & mem' & md' & k & e' & h' & out' & ev' & LB & rest & H). cbv zeta in H.
destruct H as (Hc & REST).
exists ly', S', Hp', regs', mem', md'. split; [exact Hc|]. exists k, e', h', out', ev', LB, rest. exact REST.
Qed.

(* rmd_dr_bytes's arithmetic, at any final state F, trace net T and drained lines L: what dr_rel says of the entry
   and the source drain leaves, and the potential equation of rmd_drain_dr *)
Lemma rmd_bytes_close : forall (F : drain_b_c.dstate) (T : Z) (L : list (list Z)) (g : Z -> byte) ly S ly' S'
    no cap out cap' out' e h e' h' rest,
  rmd_pot F + rmd_lw L = rmd_pot (drain_b_c.drain_init no cap e h) + T ->
  Permutation (ablocks B ly S) (aentry_blks e ++ asrc_blks h ++ aout_blks cap out ++ rest) ->
  Permutation (ablocks B ly' S') (aentry_blks e' ++ asrc_blks h' ++ aout_blks cap' out' ++ rest) ->
  cap' = drain_b_c.ds_ocap F ->
  re_cap e' = drain_b_c.ds_cap F ->
  drain_b_c.keys_texts (re_keys e') = drain_b_c.ds_H F ->
  drain_b_c.ent_ka e' = drain_b_c.ds_ka F ->
  hl_cap (hs_expected h') = drain_b_c.ds_ecap F ->
  hl_recs (hs_pending h') = [] ->
  hl_cap (hs_pending h') = hl_cap (hs_pending h) ->
  map snd (hl_recs (hs_expected h')) = map snd (hl_recs (hs_expected h)) ++ map (map g) L ->
  hs_held h' = hs_held h ->
  blocks_bytes S' <= blocks_bytes S + T.
Proof using Type.
  intros F T L g ly S ly' S' no cap out cap' out' e h e' h' rest D P1 P2 OC R4 R7 R8 R11 R16 R19 R22 R24.
  subst cap'.
  rewrite (blocks_bytes_bsum B ly' S'), (blocks_bytes_bsum B ly S), (bsum_perm _ _ P1), (bsum_perm _ _ P2), !bsum_app.
  rewrite !rmd_bsum_entry, !rmd_bsum_src, !rmd_bsum_list, !rmd_bsum_out.
  assert (Z0 : rmd_lw (map snd (hl_recs (hs_pending h'))) = 0) by (rewrite R16; reflexivity).
  rewrite R4, R7, R8, R11, R19, R22, R24, rmd_lw_app, rmd_lw_map.
  unfold rmd_pot, drain_b_c.drain_init in D.
  cbn [drain_b_c.ds_cap drain_b_c.ds_H drain_b_c.ds_ka drain_b_c.ds_ecap drain_b_c.ds_ocap drain_b_c.ds_pend] in D.
  rewrite rmd_pend_lw in D.
  pose proof (rmd_lw_nonneg (drain_b_c.ds_pend F)) as NF.
  unfold AREC in *. clear - D NF Z0. lia.
Qed.

(* ------------------------------------------------------------------ drain's live bytes and model invariant *)
(* (copied from commit d634148958a, lib/A/W_rig_top_bytes.v dr_bytes and lib/A/W_rig_top_bud.v dr_inv_of;
   rmd_dr_bytes in C3's net form) *)
Lemma rmd_dr_bytes : forall ly S ly' S' c mx no cap out out' e h e' h' LB rest,
  let fin := dr_fin c mx no cap e h in
  let cap' := if dr_live c h then drain_b_c.ds_ocap fin else cap in
  relay_instance_gone_b_lem.dr_inv (drain_b_c.drain_init no cap e h) ->
  relay_instance_gone_b_lem.dr_rest (drain_b_c.drain_init no cap e h) = bzs (pending_stream h) ->
  Permutation (ablocks B ly S) (aentry_blks e ++ asrc_blks h ++ aout_blks cap out ++ rest) ->
  Permutation (ablocks B ly' S') (aentry_blks e' ++ asrc_blks h' ++ aout_blks cap' out' ++ rest) ->
  dr_rel c mx no cap e h e' h' LB ->
  blocks_bytes S' <= blocks_bytes S + tr_net (dr_tr c mx no cap e h).
Proof using Type.
  intros ly S ly' S' c mx no cap out out' e h e' h' LB rest. cbv zeta.
  intros IV ER P1 P2 REL.
  destruct REL as (_ & _ & _ & R4 & _ & _ & R7 & R8 & _ & _ & R11 & _ & _ & _ & _ & R16 & _ & _ & R19 & _ & _ & R22 &
                   _ & R24 & _).
  exact (rmd_bytes_close _ _ _ _ ly S ly' S' no cap out _ out' e h e' h' rest (rmd_drain_dr c mx no cap e h IV ER)
           P1 P2 (rmd_ocap c mx no cap e h) R4 R7 R8 R11 R16 R19 R22 R24).
Qed.

Lemma rmd_dr_inv_of : forall ly S W mem e h j no cap,
  aentry_ok B ly S W mem e -> dr_src_ok B RG ly S W mem e h j ->
  relay_instance_gone_b_lem.dr_inv (drain_b_c.drain_init no cap e h) /\
  relay_instance_gone_b_lem.dr_rest (drain_b_c.drain_init no cap e h) = bzs (pending_stream h).
Proof.
  intros ly S W mem e h j no cap HE HS.
  destruct HE as (_ & HSK & _ & _ & _ & HCAP & HUL & HUM & HUZ & _).
  destruct HS as (_ & HA & _ & _ & HOV & HUW & _).
  destruct HA as (_ & _ & _ & _ & _ & _ & _ & _ & _ & HPL & _ & _ & _ & _ & HPD & _).
  destruct HPL as (_ & _ & _ & _ & _ & _ & _ & _ & HPF).
  apply relay_instance_gone_b_lem.rig_dinit; [exact HSK | exact HOV | exact HUW | unfold APARTIAL in HUM; lia |
    exact HUZ | lia | exact HPD |].
  eapply Forall_impl; [|exact HPF]. intros r (_ & _ & _ & Hr). exact (Hr eq_refl).
Qed.

(* ------------------------------------------------------------------ RRG when entry i is closed (eof <> 0) *)
Lemma rrd_closed_rrg : forall cx i regs F FL ly1 S1 Hp1 W1 m1 md k1,
  RBASE B ARx MT RP MMAX RG cx -> rmopen cx i = false -> RMHD RG cx i regs F ->
  RHELD B PST ARx MT RP RG cx F FL ly1 S1 Hp1 W1 m1 md k1 ->
  RRG B PST ARx MT RP MMAX RG cx i W1 (cfg_at SEGS (BASE + A_rr_ge) regs m1 md).
Proof.
intros cx i regs F FL ly1 S1 Hp1 W1 m1 md k1 HB Hop HMH HH.
pose proof HB as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HPERM0 & HTM & HPK & _).
pose proof HMH as (_ & _ & _ & HFD0 & Hi & Hfd).
pose proof HH as (HLV & HREL & HOUT & HPERM & HGS & _ & HMO0 & _ & HRM0 & HCNT0).
assert (HND : List.NoDup (map re_fd (rxes cx))) by (eapply rm_base_nodup; exact HB).
pose proof HREL as (R1 & R2 & R3 & R4 & R5 & R6 & R7 & R8 & (tail & T1 & T2 & T3) & R10 & R11).
assert (HAR : ARx ly1 S1 Hp1 W1 m1 md) by (destruct HLV as (fpos & HJ & _); eapply ajournal_gx_AR_x; exact HJ).
destruct (alx_blocks _ _ _ LAWS ly1 S1 Hp1 W1 m1 md (rxG0 cx) ATABLE HAR R8) as (_ & _ & _ & _ & HPpres & _).
change (req_size ATABLE) with 896 in HPpres.
assert (He : aentry_ok B ly1 S1 W1 m1 (rnth cx i)).
{ rewrite Forall_forall in R10. exact (R10 _ (nth_In (rxes cx) relay_remove_b_c.no_entry Hi)). }
pose proof He as (_ & _ & P1 & P2 & _).
assert (HDR : rr_drains (rxFD cx) (rxes cx) = false) by (rewrite (rm_drains _ _ HND HFD0 Hi Hfd); exact Hop).
exists regs, ly1, S1, Hp1, m1, md, k1, F, FL, (rnth cx i), (rxh cx), 0, [], (rxout cx), 0.
split; [reflexivity|].
split; [exact HMH|].
split; [exact HLV|].
split; [unfold rmdrel; rewrite Hop; reflexivity|].
split; [exact He|].
split.
{ unfold rmtbl. split; [exact R1|]. split; [exact R2|]. split; [unfold rN; exact R3|]. split; [exact R4|].
  split; [exact R5|]. split; [exact R6|]. split; [exact R8|].
  split; [rewrite (rmd_eb_len _ P1 P2); reflexivity|].
  split.
  { exists tail. split; [unfold rN; exact T1|]. unfold rmTpre, rmTpost.
    rewrite (rmd_concat_split entry_bytes (rxes cx) relay_remove_b_c.no_entry i Hi) in T3.
    rewrite <- !app_assoc in T3. exact T3. }
  split.
  { intros o Ho. apply (apresent_writable SEGS). apply (proj1 (HPpres (rmSA cx i + o) ltac:(unfold rmSA, AENT in *; lia))). }
  rewrite Forall_forall in R10 |- *. intros e'' He''. apply R10.
  apply (Permutation_in _ (Permutation_sym (rm_remove_perm (rxes cx) i relay_remove_b_c.no_entry Hi))).
  right. exact He''. }
split.
{ unfold rmc1, rmO1, rmcap1, rmlive. rewrite Hop. cbn [andb]. exact HOUT. }
split.
{ unfold rmsrc, rmcap1, rmlive. rewrite Hop. cbn [andb].
  eapply perm_trans; [exact HPERM|]. rewrite HDR. apply perm_skip. cbn [app].
  rewrite (app_assoc (aentry_blks (rnth cx i)) (rmOB cx i)). apply Permutation_app_tail.
  unfold rmOB. apply rmd_blks_split. exact Hi. }
split.
{ unfold rmgs. intros a Ha _. exact (HGS a Ha). }
pose proof (rm_tr_split _ _ HND HFD0 Hi Hfd) as TS. unfold rmtrD in TS. rewrite Hop in TS. cbn [app] in TS.
assert (BB : blocks_bytes S1 = blocks_bytes (rxS cx)).
{ rewrite (blocks_bytes_bsum B ly1 S1), (blocks_bytes_bsum B (rxly cx) (rxS cx)), (bsum_perm _ _ HPERM),
    (bsum_perm _ _ HPERM0). reflexivity. }
split.
{ (* the room round: no drain, so the rest of the trace is the whole trace and rmbud's rp_RM is RHELD's *)
  unfold rmbud. rewrite TS in HTM, HPK, HRM0.
  split; [exact HMO0|]. split; [lia|]. split; [rewrite TS; lia|]. split; [exact HTM|].
  split; [rewrite BB; exact HPK | exact HRM0]. }
(* gestures_end's count premise: its constant peak 4 is under RHELD's rr_pk = tr_peakP + 4 *)
apply (cnt_ok_pk_mono RP (rr_pk (rtr cx)) gse_pk (ablocks B ly1 S1) (ablocks B ly1 S1)); [|exact HCNT0].
intros P. unfold gse_pk, rr_pk. cbv beta. lia.
Qed.

(* ------------------------------------------------------------------ RRG's meter after drain (eof = 0) *)
Lemma rmd_bud_open : forall cx i S1 S2,
  RBASE B ARx MT RP MMAX RG cx -> rmopen cx i = true -> List.NoDup (map re_fd (rxes cx)) -> 0 <= rxFD cx ->
  (i < length (rxes cx))%nat -> re_fd (rnth cx i) = rxFD cx ->
  mo_le MT (rxS cx) S1 0 -> blocks_bytes S1 = blocks_bytes (rxS cx) ->
  mo_le MT S1 S2 (dr_cost MT (rxc cx) (rxmx cx) (rmno cx) (rxcap cx) (rnth cx i) (rxh cx)) ->
  blocks_bytes S2 <= blocks_bytes S1 + tr_net (dr_tr (rxc cx) (rxmx cx) (rmno cx) (rxcap cx) (rnth cx i) (rxh cx)) ->
  0 <= rxmx cx -> 0 <= re_cap (rnth cx i) ->
  rp_RM RP S2 (Z.to_nat (tr_cost MT_rk (rmtrK cx i ++ rmtrF cx i)) + rxkr cx) ->
  rmbud MT RP MMAX cx S2 (dr_cost MT (rxc cx) (rxmx cx) (rmno cx) (rxcap cx) (rnth cx i) (rxh cx))
    (rmtrK cx i ++ rmtrF cx i).
Proof.
intros cx i S1 S2 HB Hop HND HFD0 Hi Hfd HMO0 HBB HMd HBd Hmx Hcap HRM2.
pose proof HB as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HTM & HPK & _).
pose proof (rm_tr_split _ _ HND HFD0 Hi Hfd) as TS. unfold rmtrD in TS. rewrite Hop in TS. cbv beta iota in TS.
rewrite TS, rm_tr_max_app in HTM. rewrite TS, tr_peak_app in HPK.
assert (NN : rmd_nn (dr_tr (rxc cx) (rxmx cx) (rmno cx) (rxcap cx) (rnth cx i) (rxh cx))).
{ unfold dr_tr. apply rmd_dtr_nn; [exact Hmx | exact Hcap | unfold rmno; lia]. }
pose proof (rmd_nn_meas MT _ MLAW NN) as CN.
unfold rmbud. split.
{ pose proof (mo_le_trans MT MLAW _ _ _ _ _ HMO0 HMd) as M. rewrite Z.add_0_l in M. exact M. }
split; [unfold dr_cost; exact CN|].
split; [rewrite TS, !rm_tr_cost_app; unfold dr_cost; lia|].
split; [lia|].
split; [lia | exact HRM2].
Qed.

(* ------------------------------------------------------------------ the relay's table after drain *)
Lemma rmd_tbl_drain : forall cx i ly1 S1 Hp1 W1 m1 md1 ly2 S2 Hp2 W2 m2 md2 STK sp0 kc e' X,
  (i < length (rxes cx))%nat -> rg_place B RG ->
  arelay_at B RG ly1 S1 W1 m1 (rxG0 cx) (rxes cx) -> ARx ly1 S1 Hp1 W1 m1 md1 ->
  ajournal_gx_x (SK := SK) SEGS B PST ARx (G_DR B RG) 0 [] STK sp0 ((rmSA cx i, rmSA cx i + AENT) :: ablocks_fp X)
    ly1 S1 Hp1 W1 m1 md1 [] ly2 S2 Hp2 W2 m2 md2 kc ->
  apres_kept B W1 m1 W2 m2 -> ARx ly2 S2 Hp2 W2 m2 md2 ->
  ~ In (rxG0 cx, ATABLE) X -> (forall b, In b (rmOB cx i) -> ~ In b X) -> ~ In (rxG0 cx, ATABLE) (rmOB cx i) ->
  (forall b, In b X -> In b (ablocks B ly1 S1)) -> (forall b, In b (rmOB cx i) -> In b (ablocks B ly1 S1)) ->
  In (rxG0 cx, ATABLE) (ablocks B ly2 S2) -> (forall b, In b (rmOB cx i) -> In b (ablocks B ly2 S2)) ->
  Forall (fun r => 0 < fst r) ((rmSA cx i, rmSA cx i + AENT) :: ablocks_fp X) ->
  garr8 SEGS (arm W2 m2) (rmSA cx i) (bzs (entry_bytes e')) -> awr W2 m2 (rmSA cx i) AENT ->
  length (re_pad1 e') = 4%nat -> length (re_pad2 e') = 4%nat ->
  rmtbl B RG cx i ly2 S2 W2 m2 (entry_bytes e').
Proof.
intros cx i ly1 S1 Hp1 W1 m1 md1 ly2 S2 Hp2 W2 m2 md2 STK sp0 kc e' X Hi RGP HREL HAR1 HJd HPK HAR2 NT NOX NTO XS OS1 T2 OS2
  HFP0 HG8 HAW P1' P2'.
pose proof asan_consts as (C1 & _).
pose proof RGP as (_ & _ & _ & _ & _ & _ & RGIMG & _).
pose proof HREL as (R1 & R2 & R3 & R4 & R5 & R6 & R7 & R8 & (tail & T1 & T2t & T3) & R10 & R11).
assert (Hok : Forall (fun e => length (re_pad1 e) = 4%nat /\ length (re_pad2 e) = 4%nat) (rxes cx)).
{ eapply Forall_impl; [|exact R10]. intros e (_ & _ & Q1 & Q2 & _). split; assumption. }
assert (He : aentry_ok B ly1 S1 W1 m1 (rnth cx i)).
{ rewrite Forall_forall in R10. exact (R10 _ (nth_In (rxes cx) relay_remove_b_c.no_entry Hi)). }
pose proof He as (_ & _ & P1 & P2 & _).
destruct (alx_blocks _ _ _ LAWS ly1 S1 Hp1 W1 m1 md1 (rxG0 cx) ATABLE HAR1 R8) as (HP16 & HP4096 & HPceil & _).
change (req_size ATABLE) with 896 in HPceil.
assert (HGDR : gx_ok SEGS B (G_DR B RG)) by (eapply gx_ok_sub; [intros a Ha; apply rr_G_DR_RR; exact Ha | exact HG]).
(* g_src, g_nsrc, g_capsrc: image bytes outside G_DR *)
assert (GK : forall a, rg_src RG <= a < rg_src RG + 8 \/ rg_nsrc RG <= a < rg_nsrc RG + 4 \/
  rg_capsrc RG <= a < rg_capsrc RG + 4 -> abyte_kept W1 m1 W2 m2 a).
{ intros a Ha.
  assert (HIO : in_img SEGS a /\ ~ Exists (in_zr a) (as_owned_static B) /\ ~ (as_errno B <= a < as_errno B + 4)).
  { destruct Ha as [Ha|[Ha|Ha]].
    - apply RGIMG. unfold rg_rng. right; right; left. exact Ha.
    - apply RGIMG. unfold rg_rng. right; left. exact Ha.
    - destruct (HRGI a (or_introl Ha)) as [Hi1 Ho1]. split; [exact Hi1|]. split; [exact Ho1|].
      exact (rr_capsrc_nerr B RG HRGP a Ha). }
  destruct HIO as (Hi1 & Ho1 & He1).
  assert (Hq1 : ~ Exists (in_zr a) PST).
  { apply PSTG. unfold rr_gcells. do 2 apply Exists_cons_tl.
    destruct Ha as [Ha|[Ha|Ha]]; [apply Exists_cons_hd | apply Exists_cons_tl, Exists_cons_hd |
      do 2 apply Exists_cons_tl; apply Exists_cons_hd]; cbn [fst snd]; lia. }
  eapply rr_img_kept;
    [intros x Hx; exact Hx | exact HJd | exact HFP0 | exact HPK | exact Hi1 | exact Ho1 | exact He1 | exact Hq1 |].
  apply (rr_nG_DR B RG HRGP). destruct Ha as [Ha|[Ha|Ha]]; [right; left | right; right; left | right; right; right; left];
    exact Ha. }
(* the table's bytes outside slot i *)
assert (TK : forall a, rxG0 cx <= a < rxG0 cx + 896 -> ~ (rmSA cx i <= a < rmSA cx i + AENT) ->
  aview SEGS (w_H W2) m2 a = aview SEGS (w_H W1) m1 a).
{ intros a Ha Hns. eapply rmd_blk_kept; [exact HGDR | exact HJd | exact HAR1 | exact R8 | exact T2 |
    change (req_size ATABLE) with 896; exact Ha |].
  intros Hf. apply inFP_cons in Hf as [Hf|Hf]; [exact (Hns Hf)|].
  apply (rmd_notin_fp ly1 S1 Hp1 W1 m1 md1 X (rxG0 cx) ATABLE a HAR1 R8 NT XS); [change (req_size ATABLE) with 896; exact Ha | exact Hf]. }
unfold rmtbl.
split; [apply (akept_vm W1 m1 W2 m2 (rg_src RG) 8 (rxG0 cx)); [intros x Hx; apply GK; left; cbn in Hx; lia | exact R1]|].
split; [apply (akept_awr W1 m1 W2 m2 (rg_src RG) 8); [intros x Hx; apply GK; left; lia | exact R2]|].
split; [apply (akept_vm W1 m1 W2 m2 (rg_nsrc RG) 4 (rN cx)); [intros x Hx; apply GK; right; left; cbn in Hx; lia | exact R3]|].
split; [apply (akept_awr W1 m1 W2 m2 (rg_nsrc RG) 4); [intros x Hx; apply GK; right; left; lia | exact R4]|].
split; [apply (akept_vm W1 m1 W2 m2 (rg_capsrc RG) 4 16); [intros x Hx; apply GK; right; right; cbn in Hx; lia | exact R5]|].
split; [apply (akept_awr W1 m1 W2 m2 (rg_capsrc RG) 4); [intros x Hx; apply GK; right; right; lia | exact R6]|].
split; [exact T2|].
split; [rewrite (rmd_eb_len _ P1' P2'); reflexivity|].
split.
{ exists tail. split; [exact T1|]. unfold rmTpre, rmTpost.
  pose proof (f_equal (@length _) (rmd_concat_split entry_bytes (rxes cx) relay_remove_b_c.no_entry i Hi)) as LEN.
  rewrite !length_app in LEN. rewrite length_app in T2t. unfold ATABLE in T2t.
  assert (HF1 : Forall (fun e => length (re_pad1 e) = 4%nat /\ length (re_pad2 e) = 4%nat) (firstn i (rxes cx))).
  { rewrite <- (firstn_skipn i (rxes cx)) in Hok. apply Forall_app in Hok as [HF1 _]. exact HF1. }
  pose proof (rmd_concat_len _ HF1) as LPRE. rewrite length_firstn in LPRE.
  replace (Nat.min i (length (rxes cx))) with i in LPRE by lia.
  pose proof (rmd_eb_len (nth i (rxes cx) relay_remove_b_c.no_entry) P1 P2) as LE. pose proof (rmd_eb_len _ P1' P2') as LE'.
  rewrite (rmd_concat_split entry_bytes (rxes cx) relay_remove_b_c.no_entry i Hi) in T3.
  rewrite <- !app_assoc in T3.
  unfold bzs in *. rewrite !map_app in T3 |- *.
  apply garr8_app in T3 as [Ta Tb]. apply garr8_app in Tb as [_ Tc].
  rewrite !length_map in Tc. rewrite LE in Tc.
  apply garr8_app. split.
  - apply (W_gesture_end.ge_garr8_kept (w_H W1) (w_H W2) m1 m2 _ _ Ta). intros b Hb.
    rewrite !length_map, LPRE in Hb. apply TK; unfold rmSA, AENT; lia.
  - rewrite !length_map, LPRE. apply garr8_app. split.
    + unfold rmSA, AENT in HG8. replace (rxG0 cx + Z.of_nat (56 * i)) with (rxG0 cx + 56 * Z.of_nat i) by lia.
      exact HG8.
    + rewrite length_map, LE'. rewrite LPRE in Tc.
      apply (W_gesture_end.ge_garr8_kept (w_H W1) (w_H W2) m1 m2 _ _ Tc). intros b Hb.
      rewrite length_app, !length_map in Hb. apply TK; unfold rmSA, AENT; lia. }
split; [exact HAW|].
rewrite Forall_forall in R10 |- *. intros e'' He''.
assert (Hin'' : In e'' (rxes cx)).
{ apply (Permutation_in _ (Permutation_sym (rm_remove_perm (rxes cx) i relay_remove_b_c.no_entry Hi))).
  right. exact He''. }
assert (OBe : forall b, In b (aentry_blks e'') -> In b (rmOB cx i)).
{ intros b Hb. unfold rmOB. apply in_concat. exists (aentry_blks e''). split; [apply in_map; exact He'' | exact Hb]. }
apply (aentry_ok_kept B ly1 S1 W1 m1 ly2 S2 W2 m2 e'' (R10 _ Hin'')).
- intros r Hr a Ha. destruct (rmd_aentry_fp ly1 S1 W1 m1 e'' (R10 _ Hin'') r Hr a Ha) as (p & n & Hpn & Hpa).
  pose proof (OBe _ Hpn) as Hob.
  split.
  + eapply rmd_blk_kept; [exact HGDR | exact HJd | exact HAR1 | exact (OS1 _ Hob) | exact (OS2 _ Hob) | exact Hpa |].
    intros Hf. apply inFP_cons in Hf as [Hf|Hf].
    * assert (Hne : (rxG0 cx, ATABLE) <> (p, n)) by (intros E; rewrite E in NTO; exact (NTO Hob)).
      pose proof (sep_blocks_x SEGS B ARx LAWS ly1 S1 Hp1 W1 m1 md1 _ _ _ _ HAR1 R8 (OS1 _ Hob) Hne) as D.
      unfold zdisjoint in D. cbn [fst snd] in D. change (req_size ATABLE) with 896 in D.
      unfold rmSA, AENT in Hf. clear - D Hf Hpa Hi R7. lia.
    * exact (rmd_notin_fp ly1 S1 Hp1 W1 m1 md1 X p n a HAR1 (OS1 _ Hob) (NOX _ Hob) XS Hpa Hf).
  + intros _. apply (apresent_writable SEGS).
    destruct (alx_blocks _ _ _ LAWS ly2 S2 Hp2 W2 m2 md2 p n HAR2 (OS2 _ Hob)) as (_ & _ & _ & _ & Hpres & _).
    exact (proj1 (Hpres a Hpa)).
- intros b Hb. exact (OS2 _ (OBe _ Hb)).
Qed.

(* ------------------------------------------------------------------ RRG after drain (eof = 0) *)
Lemma rrd_open_rrg : forall cx i regsc regs2 F FL fpos ly1 S1 Hp1 W1 m1 md1 k1 ly2 S2 Hp2 W2 m2 md2 k2,
  RBASE B ARx MT RP MMAX RG cx -> rmopen cx i = true -> RMHD RG cx i regs2 F ->
  RHELD B PST ARx MT RP RG cx F FL ly1 S1 Hp1 W1 m1 md1 k1 ->
  ajournal_gx_x (SK := SK) SEGS B PST ARx (G_RR B RG) 0 [] RR_STK_x (rsp0 cx) (rFP cx)
    (rxly cx) (rxS cx) (rxHp cx) (rxW cx) (rxmem cx) (rxmd cx) [(0, fpos)] ly1 S1 Hp1 W1 m1 md1 k1 ->
  rr_frame cx fpos F FL ly1 W1 m1 ->
  ajournal_gx_x (SK := SK) SEGS B PST ARx (G_RR B RG) 0 [] RR_STK_x (rsp0 cx) (rFP cx)
    (rxly cx) (rxS cx) (rxHp cx) (rxW cx) (rxmem cx) (rxmd cx) [(0, fpos)] ly2 S2 Hp2 W2 m2 md2 k2 ->
  spZ regsc = rsp0 cx - RR_FRAME ->
  rrd_drp regsc ly1 S1 Hp1 W1 m1 md1 (rmSA cx i) (rmHA RG cx) (rnth cx i) (rxh cx) (rxc cx) (rxO cx) (rxmx cx) (rmno cx)
    (rxcap cx) (rxout cx) (Z.to_nat (tr_cost MT_rk (rmtrK cx i ++ rmtrF cx i)) + rxkr cx) ly2 S2 Hp2 W2 regs2 m2 md2 ->
  RRG B PST ARx MT RP MMAX RG cx i W2 (cfg_at SEGS (BASE + A_rr_ge) regs2 m2 md2).
Proof.
intros cx i regsc regs2 F FL fpos ly1 S1 Hp1 W1 m1 md1 k1 ly2 S2 Hp2 W2 m2 md2 k2 HB Hop HMH HH HJ1 HFR1 HJ2 Hspc HD.
pose proof asan_consts as (C1 & _).
pose proof HB as (_ & _ & _ & RGP & _ & _ & _ & _ & _ & _ & _ & _ & HPERM0 & _).
pose proof HMH as (_ & _ & _ & HFD0 & Hi & Hfd).
pose proof HH as ((fpos' & _ & HROM1 & HPK1 & _ & HLK1 & HWK1) & HREL & HOUT & HPERM & HGS & HSRC & HMO0 & _ & _ & HCNT0).
pose proof HREL as (_ & _ & _ & _ & _ & _ & R7 & R8 & _ & R10 & _).
assert (HND : List.NoDup (map re_fd (rxes cx))) by (eapply rm_base_nodup; exact HB).
assert (Heof : re_eof (rnth cx i) = 0) by (unfold rmopen in Hop; apply Z.eqb_eq; exact Hop).
assert (HDR : rr_drains (rxFD cx) (rxes cx) = true) by (rewrite (rm_drains _ _ HND HFD0 Hi Hfd); exact Hop).
pose proof (HSRC i Hi Hfd Heof) as HSO.
assert (HAR1 : ARx ly1 S1 Hp1 W1 m1 md1) by (eapply ajournal_gx_AR_x; exact HJ1).
destruct (alx_blocks _ _ _ LAWS ly1 S1 Hp1 W1 m1 md1 (rxG0 cx) ATABLE HAR1 R8) as (_ & HP4096 & HPceil & _).
change (req_size ATABLE) with 896 in HPceil.
assert (He : aentry_ok B ly1 S1 W1 m1 (rnth cx i)).
{ rewrite Forall_forall in R10. exact (R10 _ (nth_In (rxes cx) relay_remove_b_c.no_entry Hi)). }
assert (Hcap0 : 0 <= re_cap (rnth cx i)) by (clear - He; destruct He as (_ & _ & _ & _ & _ & HC & _); lia).
destruct (W_gesture_end.aout_facts B RG _ _ _ _ _ _ _ _ _ _ HOUT) as (Hmx & _ & Hcp).
assert (Hcapo : 0 <= rxcap cx) by (destruct Hcp as [(Hc & _) | (Hc & _)]; lia).
destruct HD as (kc & e' & h' & out' & ev' & LB & rest & HD). cbv zeta in HD.
destruct HD as (HJd & _ & HPKd & HMd & HRMd & HP1 & HP2 & HG8 & HAW & HEOK & D10 & D11 & D12 & D13 & D14 & D15 & D16 &
  D17 & D18 & D19 & D20 & HSRC' & HGSd & D23 & D24 & D25 & D26 & D27 & D28 & D29 & D30 & D31 & D32 & D33 & D34 & D35 &
  D36 & D37 & D38 & D39 & HOUTd).
rewrite Hspc in HJd.
assert (HAR2 : ARx ly2 S2 Hp2 W2 m2 md2) by (eapply ajournal_gx_AR_x; exact HJd).
assert (HGDR : gx_ok SEGS B (G_DR B RG)) by (eapply gx_ok_sub; [intros a Ha; apply rr_G_DR_RR; exact Ha | exact HG]).
(* the blocks: the entry's, in entry i's drain form; drain's rest; the return's *)
assert (P0 : Permutation (ablocks B ly1 S1) (aentry_blks (rnth cx i) ++ asrc_blks (rxh cx) ++
  aout_blks (rxcap cx) (rxout cx) ++ (rxG0 cx, ATABLE) :: rmOB cx i ++ rxrest cx)).
{ eapply perm_trans; [exact HPERM|]. rewrite HDR.
  eapply perm_trans; [|apply rmd_perm_pre]. apply perm_skip. apply Permutation_app_tail. apply rmd_blks_split. exact Hi. }
pose proof (rmd_perm_rest _ _ _ _ _ _ _ _ HP1 P0) as HR.
pose proof (rmd_perm_post _ _ _ _ _ _ _ _ HP2 HR) as P2X.
assert (ND1 : List.NoDup ((aentry_blks (rnth cx i) ++ asrc_blks (rxh cx) ++ aout_blks (rxcap cx) (rxout cx)) ++
  (rxG0 cx, ATABLE) :: rmOB cx i ++ rxrest cx)).
{ rewrite <- !app_assoc. apply (Permutation_NoDup P0). exact (W_gestures_end.gse_nodup_x B ARx LAWS BLKN _ _ _ _ _ _ HAR1). }
destruct (rmd_nodup_mid _ _ _ _ ND1) as (NT & NTO & NOX).
assert (XS : forall b, In b (aentry_blks (rnth cx i) ++ asrc_blks (rxh cx) ++ aout_blks (rxcap cx) (rxout cx)) ->
  In b (ablocks B ly1 S1)).
{ intros b Hb. apply (Permutation_in _ (Permutation_sym HP1)).
  apply in_app_or in Hb as [Hb|Hb]; [apply in_or_app; left; exact Hb|]. apply in_or_app; right.
  apply in_app_or in Hb as [Hb|Hb]; [apply in_or_app; left; exact Hb|]. apply in_or_app; right.
  apply in_or_app; left; exact Hb. }
assert (OS1 : forall b, In b (rmOB cx i) -> In b (ablocks B ly1 S1)).
{ intros b Hb. apply (Permutation_in _ (Permutation_sym P0)). apply in_or_app; right. apply in_or_app; right.
  apply in_or_app; right. right. apply in_or_app; left; exact Hb. }
assert (T2 : In (rxG0 cx, ATABLE) (ablocks B ly2 S2)) by (apply (Permutation_in _ (Permutation_sym P2X)); left; reflexivity).
assert (OS2 : forall b, In b (rmOB cx i) -> In b (ablocks B ly2 S2)).
{ intros b Hb. apply (Permutation_in _ (Permutation_sym P2X)). right. apply in_or_app; right.
  apply in_or_app; left; exact Hb. }
(* drain's footprint: the slot and drain's blocks *)
assert (FP0 : Forall (fun r => 0 < fst r) ((rmSA cx i, rmSA cx i + AENT) ::
  ablocks_fp (aentry_blks (rnth cx i) ++ asrc_blks (rxh cx) ++ aout_blks (rxcap cx) (rxout cx)))).
{ constructor; [cbn [fst]; unfold rmSA, AENT; lia|].
  unfold ablocks_fp. apply Forall_map. apply Forall_forall. intros [p n] Hb. cbn [fst].
  destruct (alx_blocks _ _ _ LAWS ly1 S1 Hp1 W1 m1 md1 p n HAR1 (XS _ Hb)) as (_ & H4 & _). lia. }
assert (FPB : forall a, inFP (dr_fp (rmSA cx i) (rnth cx i) (rxh cx) (rxcap cx) (rxout cx)) a ->
  exists b n, In (b, n) (ablocks B ly1 S1) /\ b <= a < b + req_size n).
{ intros a Ha. unfold dr_fp in Ha. apply inFP_cons in Ha as [Ha|Ha].
  - exists (rxG0 cx), ATABLE. split; [exact R8|]. change (req_size ATABLE) with 896. unfold rmSA, AENT in Ha. lia.
  - apply inFP_ablocks_fp_inv in Ha as (p & n & Hpn & Hpa). exists p, n. split; [exact (XS _ Hpn) | exact Hpa]. }
(* the pieces of RRG *)
assert (HLV2 : RLIVE B PST ARx RG cx F FL ly2 S2 Hp2 W2 m2 md2 k2).
{ eapply (rr_live_call B PST ARx MT RP MMAX RG LAWS HRGP HROMO PSTR PSTG cx F FL fpos ly1 S1 Hp1 W1 m1 md1 k1
    (G_DR B RG) DRAIN_STK_x);
    [exact HB | exact HJ1 | exact HROM1 | exact HPK1 | exact HFR1 | exact HLK1 | exact HWK1 | exact HGDR |
     intros a Ha; exact Ha | unfold DRAIN_STK_x, DRAIN_STK, DRAIN_FRAME, SL_STK, SL_FRAME, ASTACK; lia | exact HJd | exact FP0 |
     exact FPB | exact HPKd | exact HJ2]. }
assert (HREL1 : dr_rel (rxc cx) (rxmx cx) (rmno cx) (rxcap cx) (rnth cx i) (rxh cx) e' h' LB).
{ unfold dr_rel. cbv zeta. repeat match goal with |- _ /\ _ => split end; assumption. }
destruct (rmd_dr_inv_of ly1 S1 W1 m1 (rnth cx i) (rxh cx) (rxj cx) (rmno cx) (rxcap cx) He HSO) as [IV ER].
pose proof (rmd_dr_bytes ly1 S1 ly2 S2 (rxc cx) (rxmx cx) (rmno cx) (rxcap cx) (rxout cx) out' (rnth cx i) (rxh cx)
  e' h' LB rest IV ER HP1 HP2 HREL1) as HBD.
assert (HO2 : aout_at B RG ly2 S2 W2 m2 (rmc1 cx i ev') (rmO1 cx i LB) (rxmx cx) (Z.of_nat (length (rmO1 cx i LB)))
  (rmcap1 cx i) out').
{ unfold rmc1, rmO1, rmcap1, rmlive. rewrite Hop. cbn [andb].
  destruct (dr_live (rxc cx) (rxh cx)) eqn:DL; try rewrite DL in HOUTd.
  - replace (Z.of_nat (length (rxO cx ++ LB))) with (rmno cx + dr_tot (rxh cx)); [exact HOUTd|].
    rewrite length_app, Nat2Z.inj_add. unfold rmno. f_equal.
    unfold dr_tot. rewrite <- D39. unfold bzs. rewrite length_map. reflexivity.
  - unfold rmno in HOUTd. exact HOUTd. }
assert (HP3 : Permutation (ablocks B ly2 S2) ((rxG0 cx, ATABLE) :: aentry_blks e' ++ rmOB cx i ++ rmsrc cx i h' ++
  aout_blks (rmcap1 cx i) out' ++ rxrest cx)).
{ unfold rmsrc, rmcap1, rmlive. rewrite Hop. cbn [andb]. exact P2X. }
assert (HGS2 : rmgs RG cx W2 m2).
{ unfold rmgs. intros a Ha Hj. pose proof (Hj HDR) as Hn.
  exact (rmd_abk_trans _ _ _ _ _ _ a (HGS a Ha) (HGSd a Ha Hn)). }
assert (BB : blocks_bytes S1 = blocks_bytes (rxS cx)).
{ rewrite (blocks_bytes_bsum B ly1 S1), (blocks_bytes_bsum B (rxly cx) (rxS cx)), (bsum_perm _ _ HPERM),
    (bsum_perm _ _ HPERM0). reflexivity. }
pose proof HEOK as (_ & _ & EP1 & EP2 & _).
exists regs2, ly2, S2, Hp2, m2, md2, k2, F, FL, e', h', ev', LB, out',
  (dr_cost MT (rxc cx) (rxmx cx) (rmno cx) (rxcap cx) (rnth cx i) (rxh cx)).
split; [reflexivity|]. split; [exact HMH|]. split; [exact HLV2|].
split; [unfold rmdrel; rewrite Hop; split; [exact HREL1 | exact HSRC']|].
split; [exact HEOK|].
split.
{ eapply (rmd_tbl_drain cx i ly1 S1 Hp1 W1 m1 md1 ly2 S2 Hp2 W2 m2 md2); [exact Hi | exact RGP | exact HREL | exact HAR1 |
    exact HJd | exact HPKd | exact HAR2 | exact NT | exact NOX | exact NTO | exact XS | exact OS1 | exact T2 | exact OS2 |
    exact FP0 | exact HG8 | exact HAW | exact EP1 | exact EP2]. }
split; [exact HO2|]. split; [exact HP3|]. split; [exact HGS2|].
split.
{ apply (rmd_bud_open cx i S1 S2); [exact HB | exact Hop | exact HND | exact HFD0 | exact Hi | exact Hfd | exact HMO0 |
    exact BB | exact HMd | exact HBD | exact (proj1 Hmx) | exact Hcap0 | exact HRMd]. }
(* the room round: gestures_end's count premise at the return state.  Drain moves the count of its own blocks (the
   entry's, the source's, g_out's) by at most its trace's count peak (W_rr_m_dcnt.v), and that peak is within the
   request trace's (W_tr_cnt.v tr_peakP_app), whose rr_pk = peak + 4 RHELD's count fact carries; gse_pk is 4. *)
pose proof (rm_tr_split _ _ HND HFD0 Hi Hfd) as TS. unfold rmtrD in TS. rewrite Hop in TS. cbv beta iota in TS.
apply (cnt_ok_pk_mono RP (rr_pk (rtr cx)) gse_pk (ablocks B ly1 S1) (ablocks B ly2 S2)); [|exact HCNT0].
intros P. unfold gse_pk, rr_pk. cbv beta.
pose proof (W_rr_m_dcnt.rmc_dr_cnt_peak (rxc cx) (rxmx cx) (rmno cx) (rxcap cx) (rxout cx) out' (rnth cx i) (rxh cx)
  e' h' LB P IV ER (rmd_held_ok _ _ _ _ _ He) (rmd_held_ok _ _ _ _ _ HEOK) Hcapo HREL1) as DC. cbv zeta in DC.
rewrite (ReplyCnt.acnt_perm P _ _ HP2), (ReplyCnt.acnt_perm P _ _ HP1),
  (rmd_acnt3 P (aentry_blks e')), (rmd_acnt3 P (aentry_blks (rnth cx i))).
rewrite TS, W_tr_cnt.tr_peakP_app.
lia.
Qed.

(* the blocks drain names are the entry's (rr_fp's) *)
Lemma rmd_X_in_rr : forall cx i b, (i < length (rxes cx))%nat ->
  In b (aentry_blks (rnth cx i) ++ asrc_blks (rxh cx) ++ aout_blks (rxcap cx) (rxout cx)) ->
  In b (concat (map aentry_blks (rxes cx)) ++ asrc_blks (rxh cx) ++ aout_blks (rxcap cx) (rxout cx)).
Proof.
intros cx i b Hi Hb. apply in_app_or in Hb as [Hb|Hb]; [|apply in_or_app; right; exact Hb].
apply in_or_app; left. apply in_concat. exists (aentry_blks (rnth cx i)). split; [|exact Hb].
apply in_map. apply nth_In. exact Hi.
Qed.

Let RUN := paj_run_x_x B PST ARx LAWS (G_RR B RG) HG 0 [].
Let RUNTO := paj_run_to_x_x B PST ARx LAWS (G_RR B RG) HG 0 [].
Let BR := paj_branch (PI := PI).

Theorem rr_m_drain : hop_drain_stmt B PST ARx MT RP MMAX RG.
Proof.
unfold hop_drain_stmt. intros cx i W1 c1 HB HM KG.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
pose proof HB as (HPRE & _ & _ & RGP & _ & HFDr & _).
destruct HM as (regs1 & ly1 & S1 & Hp1 & m1 & md1 & k1 & F & FL & -> & HRH & H25 & H10 & H24 & HFD0 & Hi & Hfd & HH).
pose proof HH as (HLV & HREL & HOUT & HPERM & HGS & HSRC & HMO0 & HBB0 & HRM0 & HCNT0).
pose proof HLV as (fpos & HJ & HLVr).
pose proof HREL as (_ & _ & _ & _ & _ & _ & Rlen & RIn & (tail & _ & _ & Rtab) & Rok & _).
pose proof HRH as ((Hsp & H3 & H4 & H8 & H9 & H18 & H20 & H21 & H22 & H26 & H27) & H19 & H23).
assert (HAR : ARx ly1 S1 Hp1 W1 m1 md1) by (eapply ajournal_gx_AR_x; exact HJ).
destruct (alx_blocks _ _ _ LAWS ly1 S1 Hp1 W1 m1 md1 (rxG0 cx) ATABLE HAR RIn) as (HP16 & HP4096 & HPceil & HPh_ia & HPpres & _).
pose proof (proj1 HPh_ia) as HPh.
change (req_size ATABLE) with 896 in HPceil, HPh_ia, HPh, HPpres.
assert (Hok : Forall (fun e => length (re_pad1 e) = 4%nat /\ length (re_pad2 e) = 4%nat) (rxes cx)).
{ eapply Forall_impl; [|exact Rok]. intros e (_ & _ & P1 & P2 & _). split; assumption. }
assert (He : aentry_ok B ly1 S1 W1 m1 (rnth cx i)).
{ rewrite Forall_forall in Rok. exact (Rok _ (nth_In (rxes cx) relay_remove_b_c.no_entry Hi)). }
assert (Hev : 0 <= re_eof (rnth cx i) < 2 ^ 31) by (clear - He; destruct He as ([E0|E1] & _); lia).
pose proof (rmd_eof_cell (arm W1 m1) (rxG0 cx) (rxes cx) tail i Rtab Hok Hi Hev) as Mev.
assert (G8 : rxG0 cx = 8 * (rxG0 cx / 8)).
{ pose proof (Z.div_mod (rxG0 cx) 16 ltac:(lia)) as D. rewrite HP16, Z.add_0_r in D.
  rewrite D at 2. replace (16 * (rxG0 cx / 16)) with ((2 * (rxG0 cx / 16)) * 8) by ring. rewrite Z.div_mul by lia. lia. }
assert (GB : 4096 <= rxG0 cx /\ rxG0 cx + 896 <= 0x7fffff800000) by (unfold ASAN_CEIL in *; lia).
assert (Hi16 : (i < 16)%nat) by lia.
remember (Eimg (Ereg regs1 (rrd_extra (re_eof (rnth cx i))))) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (HAE : env_agree 32 (Ereg regs1 (rrd_extra (re_eof (rnth cx i)))) E)
by (rewrite HE; split; [intros m Hm; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
assert (EEo : forall m (rr : bv 5), Z.of_nat m = bv_unsigned rr -> ew E m = getr regs1 rr)
by (intros m rr Hm; subst E; pose proof (bv_unsigned_in_range 5 rr) as Hr5; change (bv_modulus 5) with 32 in Hr5;
rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_nat; exact Hm).
assert (E10 : ew E 10 = Z_to_bv 64 (rxG0 cx + AENT * Z.of_nat i)) by (rewrite (EEo 10%nat 10%bv eq_refl); exact H10).
assert (E22 : ew E 22 = Z_to_bv 64 SHADOW_OFF) by (rewrite (EEo 22%nat 22%bv eq_refl); exact H22).
assert (E32 : ew E 32 = Z_to_bv 64 (re_eof (rnth cx i)))
by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 _ 0)).
assert (HS : st_ok_pi SEGS VAL E ss_rrd (restrict (w_H W1) (mkst regs1 (Z_to_bv 64 (BASE + A_rr_match)) m1 (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. unfold ss_rrd. apply pa_entry_st_ok_full.
- rewrite HE. apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- unfold rrd_regions. repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
  cbn [base_val]. rewrite E10, unsigned_lit_small by (unfold AENT; lia).
  split; [unfold AENT; lia|]. split; [unfold AENT; lia|]. split; [intros o Ho; lia|].
  constructor; [|constructor].
  apply (chunk_ok_val SEGS E _ (rxG0 cx + AENT * Z.of_nat i) 4 4 (SOff 32 0) (re_eof (rnth cx i)));
  [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
  exact Mev.
- cbn [pairwise_disjoint all_disjoint]. repeat split.
- split; [|split; [exact I | exact I]].
  cbn [rrd_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
  rewrite E10, E22, E32, !unsigned_lit_small by (unfold SHADOW_OFF, AENT in *; lia).
  change (2 ^ 3) with 8. rewrite !Z.pow_0_r, !Z.mod_1_r.
  assert ((rxG0 cx + AENT * Z.of_nat i) mod 8 = 0).
  { unfold AENT. rewrite G8. replace (8 * (rxG0 cx / 8) + 56 * Z.of_nat i) with ((rxG0 cx / 8 + 7 * Z.of_nat i) * 8) by ring.
    apply Z_mod_mult. }
  unfold RRD_PHI, SB, SHADOW_OFF, AENT in *. repeat match goal with |- _ /\ _ => split end; try lia; try exact I. }
clear HE.
assert (HBx : U E rrd_Bx = SHADOW_OFF) by (unfold rrd_Bx; rewrite (U_atom E 22 SHADOW_OFF E22) by (unfold SHADOW_OFF; lia); reflexivity).
assert (SHOK : sh_ok SEGS rrd_Bx rrd_SH E (mrestrict (w_H W1) m1)).
{ constructor; [|constructor].
  eapply shent_ok_of_range.
  + apply (range_addressable_of_block_hp0_x SEGS B ARx LAWS HP0 ly1 S1 Hp1 W1 m1 md1 (rxG0 cx) ATABLE
      (rxG0 cx + AENT * Z.of_nat i) 56 HAR RIn);
    [unfold AENT; lia | change (req_size ATABLE) with 896; unfold AENT; lia].
  + exact HBx.
  + rewrite (U_atom E 10 _ E10) by (unfold AENT; lia). reflexivity.
  + lia.
  + lia.
  + intros x Hx. unfold in_app, SHADOW_OFF, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, AENT in *. lia. }
unfold cfg_at. change (w64 (BASE + A_rr_match)) with (Z_to_bv 64 (BASE + A_rr_match)).
(* the eof field's shadow check (fast path), the eof load, to the test 0x83f60 *)
paj_run_tok_x RUN HS HJ SHOK rrd_Bspan.
{ apply awr_ok_x_cons; [intros a Ha; cbn in Ha; lia | apply awr_ok_x_nil]. }
rrd_mem Em1.
psrr_branch_tok RUN BR HS SHOK rrd_Bspan.
- (* eof <> 0: the bnez to 0x83f68, nothing changed (the lane's rrA_at_ge_noeof) *)
  rewrite branch_ne_U, (U_atom E 32 _ E32), U_lit in Hc by lia.
  apply negb_true_iff, Z.eqb_neq in Hc.
  assert (Hop : rmopen cx i = false) by (unfold rmopen; apply Z.eqb_neq; exact Hc).
  paj_run_to_tok_x RUNTO HS HJ SHOK rrd_Bspan (AF_fr_relay_remove + 0x184).
  { apply awr_ok_x_cons; [intros a Ha; cbn in Ha; lia | apply awr_ok_x_nil]. }
  rrd_mem Em2.
  lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?ms') =>
    pose proof (regs_kept_of_st_ok_pi _ _ _ regs1 _ RRD_KEPT HS HAE ltac:(vm_compute; reflexivity)) as HK;
    cbn [ms_regs restrict] in HK;
    pmkst HS; rewrite Em2, Em1 in HJ |- *; apply KG;
    apply (rrd_closed_rrg cx i (ms_regs ms') F FL ly1 S1 Hp1 W1 m1 _ k1 HB Hop) end.
  + unfold RMHD. split; [unfold rregs_held, rregs_base, spZ; rewrite !HK by (cbv; tauto); exact HRH|].
    split; [rewrite (HK 25%bv) by (cbv; tauto); exact H25|].
    split; [rewrite (HK 24%bv) by (cbv; tauto); exact H24|].
    exact (conj HFD0 (conj Hi Hfd)).
  + split; [exists fpos; split; [exact HJ | exact HLVr] | exact (proj2 HH)].
- (* eof = 0: jal drain 0x83f64 (the lane's rrA_drain_hop, eof = 0 arm) *)
  rewrite branch_ne_U, (U_atom E 32 _ E32), U_lit in Hc by lia.
  apply negb_false_iff, Z.eqb_eq in Hc.
  assert (Hop : rmopen cx i = true) by (unfold rmopen; apply Z.eqb_eq; exact Hc).
  pose proof HLVr as (HROM1 & HPK1 & HFR1 & HLK1 & HWK1).
  pose proof HPRE as (_ & _ & _ & Hgp & Htp & HstkE & _).
  pose proof HstkE as (_ & _ & Hceil0 & Hslo0 & Hshi0 & H470 & _).
  assert (HND : List.NoDup (map re_fd (rxes cx))) by (eapply rm_base_nodup; exact HB).
  assert (HDR : rr_drains (rxFD cx) (rxes cx) = true) by (rewrite (rm_drains _ _ HND HFD0 Hi Hfd); exact Hop).
  pose proof (HSRC i Hi Hfd Hc) as HSO.
  pose proof HSO as (Hj4 & HSA & HOTH & Hhfd & Hsk & HU & Hb1 & Hb2 & Hb3).
  destruct (W_gesture_end.aout_facts B RG _ _ _ _ _ _ _ _ _ _ HOUT) as (Hmx & _ & _).
  assert (Hcap0 : 0 <= re_cap (rnth cx i)) by (clear - He; destruct He as (_ & _ & _ & _ & _ & HC & _); lia).
  assert (Hno0 : 0 <= rmno cx) by (unfold rmno; lia).
  (* dr_spec's premises from RRM *)
  assert (GE : garr8 SEGS (arm W1 m1) (rmSA cx i) (bzs (entry_bytes (rnth cx i)))).
  { pose proof Rtab as T3. rewrite (rmd_concat_split entry_bytes (rxes cx) relay_remove_b_c.no_entry i Hi) in T3.
    rewrite <- !app_assoc in T3. unfold bzs in T3 |- *. rewrite !map_app in T3.
    apply garr8_app in T3 as [_ T3]. apply garr8_app in T3 as [T3 _].
    assert (HF1 : Forall (fun e => length (re_pad1 e) = 4%nat /\ length (re_pad2 e) = 4%nat) (firstn i (rxes cx))).
    { rewrite <- (firstn_skipn i (rxes cx)) in Hok. apply Forall_app in Hok as [HF1 _]. exact HF1. }
    rewrite length_map, (rmd_concat_len _ HF1), length_firstn in T3.
    replace (Nat.min i (length (rxes cx))) with i in T3 by lia.
    unfold rmSA, AENT. replace (rxG0 cx + 56 * Z.of_nat i) with (rxG0 cx + Z.of_nat (56 * i)) by lia. exact T3. }
  assert (AW : awr W1 m1 (rmSA cx i) AENT).
  { intros o Ho. apply (apresent_writable SEGS). apply (proj1 (HPpres (rmSA cx i + o) ltac:(unfold rmSA, AENT in *; lia))). }
  assert (P0 : Permutation (ablocks B ly1 S1) (aentry_blks (rnth cx i) ++ asrc_blks (rxh cx) ++
    aout_blks (rxcap cx) (rxout cx) ++ (rxG0 cx, ATABLE) :: rmOB cx i ++ rxrest cx)).
  { eapply perm_trans; [exact HPERM|]. rewrite HDR.
    eapply perm_trans; [|apply rmd_perm_pre]. apply perm_skip. apply Permutation_app_tail. apply rmd_blks_split. exact Hi. }
  assert (PRE : Permutation (ablocks B ly1 S1) ((rxG0 cx, ATABLE) :: aentry_blks (rnth cx i) ++ asrc_blks (rxh cx) ++
    aout_blks (rxcap cx) (rxout cx) ++ (rmOB cx i ++ rxrest cx))).
  { eapply perm_trans; [exact P0|].
    pose proof (Permutation_middle (aentry_blks (rnth cx i) ++ asrc_blks (rxh cx) ++ aout_blks (rxcap cx) (rxout cx))
      (rmOB cx i ++ rxrest cx) (rxG0 cx, ATABLE)) as M. rewrite <- !app_assoc in M. apply Permutation_sym. exact M. }
  assert (XS : forall b, In b (aentry_blks (rnth cx i) ++ asrc_blks (rxh cx) ++ aout_blks (rxcap cx) (rxout cx)) ->
    In b (ablocks B ly1 S1)).
  { intros b Hb. apply (Permutation_in _ (Permutation_sym P0)).
    apply in_app_or in Hb as [Hb|Hb]; [apply in_or_app; left; exact Hb|]. apply in_or_app; right.
    apply in_app_or in Hb as [Hb|Hb]; [apply in_or_app; left; exact Hb|]. apply in_or_app; right.
    apply in_or_app; left; exact Hb. }
  pose proof (rm_tr_split _ _ HND HFD0 Hi Hfd) as TS. unfold rmtrD in TS. rewrite Hop in TS. cbv beta iota in TS.
  pose proof HB as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HTM & _ & HMOK & _).
  pose proof (rmd_nn_meas MT _ MLAW (rmd_tl_nn cx i (proj1 Hmx))) as TC.
  assert (NN : rmd_nn (dr_tr (rxc cx) (rxmx cx) (rmno cx) (rxcap cx) (rnth cx i) (rxh cx))).
  { unfold dr_tr. apply rmd_dtr_nn; [exact (proj1 Hmx) | exact Hcap0 | exact Hno0]. }
  pose proof (rmd_nn_meas MT _ MLAW NN) as CN.
  assert (RM1 : tr_max (dr_tr (rxc cx) (rxmx cx) (rmno cx) (rxcap cx) (rnth cx i) (rxh cx)) < MMAX).
  { rewrite TS, rm_tr_max_app in HTM. lia. }
  assert (RM2 : blocks_bytes S1 + tr_peak (dr_tr (rxc cx) (rxmx cx) (rmno cx) (rxcap cx) (rnth cx i) (rxh cx)) <= LIVE_MAX).
  { rewrite TS in HBB0.
    pose proof (tr_peak_prefix (dr_tr (rxc cx) (rxmx cx) (rmno cx) (rxcap cx) (rnth cx i) (rxh cx))
      (rmtrK cx i ++ rmtrF cx i)) as PP. lia. }
  assert (RM3 : mo_ok MT S1 (dr_cost MT (rxc cx) (rxmx cx) (rmno cx) (rxcap cx) (rnth cx i) (rxh cx))).
  { apply (mok_station MT (rxS cx) S1 (tr_cost MT (rtr cx)) 0 _ MLAW HMOK HMO0 CN).
    rewrite TS, rm_tr_cost_app. unfold dr_cost. lia. }
  (* the room round at drain's call: drain gets kr' = what the key run and the two frees charge, plus kr; its room
     premise is RHELD's split exactly (the counting meter's costs are nonnegative), its count premise (drain's peak
     plus 2) is under RHELD's (the request trace's peak plus 4) *)
  pose proof (rmd_nn_meas MT_rk _ rmd_rk_laws (rmd_tl_nn cx i (proj1 Hmx))) as TCk.
  pose proof (rmd_nn_meas MT_rk _ rmd_rk_laws NN) as CNk.
  assert (HRMdr : rp_RM RP S1 (Z.to_nat (dr_cost MT_rk (rxc cx) (rxmx cx) (rmno cx) (rxcap cx) (rnth cx i) (rxh cx)) +
    (Z.to_nat (tr_cost MT_rk (rmtrK cx i ++ rmtrF cx i)) + rxkr cx))).
  { apply (RMM_of RP S1 _ (Z.to_nat (tr_cost MT_rk (rtr cx)) + rxkr cx)); [|exact HRM0].
    rewrite TS, (rm_tr_cost_app_m MT_rk (dr_tr (rxc cx) (rxmx cx) (rmno cx) (rxcap cx) (rnth cx i) (rxh cx))
      (rmtrK cx i ++ rmtrF cx i)).
    unfold dr_cost. lia. }
  assert (HCNTd : cnt_ok_pk RP (dr_pk (rxc cx) (rxmx cx) (rmno cx) (rxcap cx) (rnth cx i) (rxh cx)) (ablocks B ly1 S1)).
  { apply (cnt_ok_pk_mono RP (rr_pk (rtr cx)) _ (ablocks B ly1 S1) (ablocks B ly1 S1)); [|exact HCNT0].
    intros P. unfold dr_pk, rr_pk. cbv beta. rewrite TS, W_tr_cnt.tr_peakP_app. lia. }
  destruct (rr_call_chain B PST ARx MT RP MMAX RG HG cx F FL ly1 S1 Hp1 W1 m1 md1 k1 HB HLV) as (ch1 & Hch).
  (* the run to drain's entry: jal 0x83f64, ra = 0x83f68 *)
  paj_run_to_tok_x RUNTO HS HJ SHOK rrd_Bspan AF_fr_drain.
  { apply awr_ok_x_cons; [intros a Ha; cbn in Ha; lia | apply awr_ok_x_nil]. }
  rrd_mem Em2.
  lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?ms') =>
    pose proof (regs_kept_of_st_ok_pi _ _ _ regs1 _ RRD_KEPT HS HAE ltac:(vm_compute; reflexivity)) as HK;
    cbn [ms_regs restrict] in HK; prreg HS (1%bv : bv 5) Q1;
    pmkst HS; rewrite Em2, Em1 in HJ |- *; set (regsc := ms_regs ms') in * end.
  lazymatch goal with |- SRr _ _ {| cfg_ms := _; cfg_model := ?md |} _ => set (mdx := md) in * end.
  assert (Hspc : spZ regsc = rsp0 cx - RR_FRAME) by (unfold spZ; rewrite (HK 2%bv) by (cbv; tauto); exact Hsp).
  eapply SRr_bind.
  { eapply (W_gestures_end.gse_callS_x B PST ARx LAWS (G_RR B RG) W1 regsc m1 _ RR_STK_x (rsp0 cx) (rFP cx)
      (rxly cx) (rxS cx) (rxHp cx) (rxW cx) (rxmem cx) (rxmd cx) [(0, fpos)] ly1 S1 Hp1 mdx k1 DRAIN_STK_x
      (dr_fp (rmSA cx i) (rnth cx i) (rxh cx) (rxcap cx) (rxout cx)) (-96) (getr regsc 1) ch1
      (fun ly2 S2 W2 regs2 mem2 md2 => exists Hp2, rrd_drp regsc ly1 S1 Hp1 W1 m1 mdx (rmSA cx i) (rmHA RG cx)
         (rnth cx i) (rxh cx) (rxc cx) (rxO cx) (rxmx cx) (rmno cx) (rxcap cx) (rxout cx)
         (Z.to_nat (tr_cost MT_rk (rmtrK cx i ++ rmtrF cx i)) + rxkr cx) ly2 S2 Hp2 W2 regs2 mem2 md2) HG HJ).
    - rewrite Hspc. unfold RR_FRAME. lia.
    - reflexivity.
    - lia.
    - unfold DRAIN_STK_x, DRAIN_STK, DRAIN_FRAME, SL_STK, SL_FRAME, ASTACK. lia.
    - unfold RR_STK_x, RR_STK, RR_FRAME, DRAIN_STK_x. lia.
    - rewrite (HK 3%bv) by (cbv; tauto). rewrite H3. exact Hgp.
    - rewrite (HK 4%bv) by (cbv; tauto). rewrite H4. exact Htp.
    - reflexivity.
    - rewrite Q1. apply ret_ok_codeptr_v; [lia | reflexivity].
    - rewrite Q1. rewrite unsigned_lit_small by lia. lia.
    - replace (rsp0 cx + -96) with (rsp0 cx - RR_FRAME) by (unfold RR_FRAME; lia).
      replace (s0Z regsc) with (rsp0 cx); [exact Hch|].
      unfold s0Z. rewrite (HK 8%bv) by (cbv; tauto). rewrite H8. unfold w64.
      rewrite unsigned_lit_small by (unfold rsp0, RR_STK_x, RR_STK, RR_FRAME, DRAIN_STK_x, DRAIN_STK, DRAIN_FRAME, SL_STK, SL_FRAME, ASTACK in *; lia).
      reflexivity.
    - intros HPRE1.
      assert (H10c : getr regsc 10 = w64 (rmSA cx i)) by (rewrite (HK 10%bv) by (cbv; tauto); exact H10).
      eapply SRr_mono.
      { exact (DRAIN W1 ly1 S1 Hp1 regsc m1 mdx ch1 (rxG0 cx) (rmSA cx i) (rnth cx i) (rxj cx) (rxh cx) (rxc cx)
          (rxO cx) (rxmx cx) (rmno cx) (rxcap cx) (rxout cx) HPRE1 H10c RIn ltac:(unfold rmSA, AENT; lia)
          ltac:(unfold rmSA, AENT, ATABLE; lia) (rmd_sa_align ly1 S1 Hp1 W1 m1 md1 (rxG0 cx) i HAR RIn)
          GE AW He Hj4 HSA HOTH Hhfd Hsk HU HOUT HROM1 (ex_intro _ (rmOB cx i ++ rxrest cx) PRE) Hb1 Hb2 Hb3
          RM1 RM2 RM3 _ HRMdr HCNTd). }
      cbv beta. intros W2 c2 _ HDP. apply rrd_drp_of in HDP.
      destruct HDP as (ly2 & S2 & Hp2 & regs2 & m2 & md2 & -> & HD).
      pose proof HD as (kc & e' & h' & out' & ev' & LB & rest & HDb). cbv zeta in HDb. destruct HDb as (HJd & HPd & _).
      exists ly2, S2, Hp2, regs2, m2, md2, kc. split; [reflexivity|].
      split; [apply rr_lift_DR; exact HJd|]. split; [exact HPd | exists Hp2; exact HD].
    - intros a Ha. left.
      assert (HB1 : exists b n, In (b, n) (ablocks B ly1 S1) /\ b <= a < b + req_size n).
      { unfold dr_fp in Ha. apply inFP_cons in Ha as [Ha|Ha].
        - exists (rxG0 cx), ATABLE. split; [exact RIn|]. change (req_size ATABLE) with 896. unfold rmSA, AENT in Ha. lia.
        - apply inFP_ablocks_fp_inv in Ha as (p & n & Hpn & Hpa). exists p, n. split; [exact (XS _ Hpn) | exact Hpa]. }
      split; [|exact HB1].
      unfold dr_fp in Ha. apply inFP_cons in Ha as [Ha|Ha].
      + unfold rFP, rr_fp. replace a with (rxG0 cx + (a - rxG0 cx)) by lia.
        apply (inFP_ablocks_fp _ (rxG0 cx) ATABLE); [left; reflexivity | change (req_size ATABLE) with 896; unfold rmSA, AENT in Ha; lia].
      + apply inFP_ablocks_fp_inv in Ha as (p & n & Hpn & Hpa). unfold rFP, rr_fp.
        replace a with (p + (a - p)) by lia. apply (inFP_ablocks_fp _ p n); [|lia]. right. rewrite HDR.
        exact (rmd_X_in_rr cx i (p, n) Hi Hpn). }
  cbv beta. intros W2 c2 Hwle2 (ly2 & S2 & Hp2 & regs2 & m2 & md2 & kc & -> & HJ2 & HJc & HP2 & (Hp2' & HD)).
  (* drain's journal and the caller's end at the same state, whose head set is empty (HP0) *)
  assert (EHp : Hp2' = Hp2).
  { destruct HD as (kd & e2 & h2 & o2 & v2 & L2 & r2 & HD). cbv zeta in HD. destruct HD as (HJd & _).
    apply ajournal_gx_AR_x in HJd. apply ajournal_gx_AR_x in HJ2.
    rewrite (HP0 _ _ _ _ _ _ HJd), (HP0 _ _ _ _ _ _ HJ2). reflexivity. }
  subst Hp2'.
  apply KG.
  assert (EC : {| cfg_ms := mkst regs2 (getr regsc 1) m2 (seg_rom SEGS); cfg_model := md2 |} =
               cfg_at SEGS (BASE + A_rr_ge) regs2 m2 md2) by (unfold cfg_at; rewrite Q1; reflexivity).
  rewrite EC.
  assert (KP : forall r : bv 5, In r RRD_KEPT -> acallee_saved (bv_unsigned r) -> getr regs2 r = getr regs1 r).
  { intros r Hr Hc0. pose proof (HP2 _ Hc0) as X. rewrite !Z_to_bv_bv_unsigned in X. rewrite X. apply HK. exact Hr. }
  eapply (rrd_open_rrg cx i regsc regs2 F FL fpos ly1 S1 Hp1 W1 m1 mdx k1 ly2 S2 Hp2 W2 m2 md2 (k1 + kc));
    [exact HB | exact Hop | | split; [exists fpos; split; [exact HJ | exact HLVr] | exact (proj2 HH)] | exact HJ |
     exact HFR1 | exact HJ2 | exact Hspc | exact HD].
  unfold RMHD. split.
  { unfold rregs_held, rregs_base, spZ.
    rewrite !KP by rrd_cs. exact HRH. }
  split; [rewrite KP by rrd_cs; exact H25|].
  split; [rewrite KP by rrd_cs; exact H24|].
  exact (conj HFD0 (conj Hi Hfd)).
Qed.

(* ---- route R (RULE-SHAPES.md (sha256 2e856ce788dd; internal record) sec 0): the DRAIN hop at a world relation R, stated as W_rr_match_cx.v hop_drain_stmt_xR
   (RRM_xR / RRG_xR over RLIVE_xR's journal ajournal_gx_xR .. R; the step relation YA0nH.SRrG SEGS R).  Drain is called
   at its contract at R (DRAIN_R, W_contract_xR.v dr_spec_xR) through W_gestures_end.v gse_callS_xR; its journal (at
   G_DR in dr_post_xR) is lifted to G_RR by W_relay_remove_cx.v rr_lift_DR_xR and composed into the caller's by
   gse_callS_xR (ajournal_gx_sub_xR, R_trans).  The runs are the G runs (paj_run_x_xG / paj_run_to_x_xG with
   paj_run_tok_xR / paj_run_to_tok_xR), the branch paj_branch_xR, the chain and RLIVE across the call W_rr_m_kit.v
   rr_call_chain_xR / rr_live_call_xR, the kept image bytes rr_img_kept_xR.  Each X_xR below is X above with the journal,
   RHELD / RLIVE / RRG and these pieces at R; no step reads the world relation, so the journal-free helpers (rmd_bud_open,
   rmd_X_in_rr, rmd_notin_fp, rmd_aentry_fp, rmd_dr_bytes, ..) serve both forms. ---- *)
Section wR.
Variable R : world SEGS -> world SEGS -> Prop.
Hypothesis R_refl : forall W, R W W.
Hypothesis R_trans : forall W1 W2 W3, R W1 W2 -> R W2 W3 -> R W1 W3.
Hypothesis WLE_R : forall W W', @wle SEGS W W' -> R W W'.
(* drain's contract at R (W_contract_xR.v dr_spec_xR): hop_drain_stmt_xR names no callee spec, so the hop takes it here *)
Hypothesis DRAIN_R : dr_spec_xR B PST ARx R MT RP MMAX RG (BASE + AF_fr_drain).
(* :798 rmd_blk_kept at R *)
Lemma rmd_blk_kept_xR : forall Gc XO OUT STK sp0 FP ly S Hp W mem md own ly' S' Hp' W' mem' md' k p n a,
  gx_ok SEGS B Gc ->
  ajournal_gx_xR (SK := SK) SEGS B PST ARx R Gc XO OUT STK sp0 FP ly S Hp W mem md own ly' S' Hp' W' mem' md' k ->
  ARx ly S Hp W mem md -> In (p, n) (ablocks B ly S) -> In (p, n) (ablocks B ly' S') ->
  p <= a < p + req_size n -> ~ inFP FP a -> aview SEGS (w_H W') mem' a = aview SEGS (w_H W) mem a.
Proof.
intros Gc XO OUT STK sp0 FP ly S Hp W mem md own ly' S' Hp' W' mem' md' k p n a HGc HJ HAR H1 H2 Ha HnF.
pose proof asan_consts as (C1 & _).
destruct (alx_blocks _ _ _ LAWS ly S Hp W mem md p n HAR H1) as (_ & H4096 & Hceil & _).
pose proof HJ as HJin. apply ajournal_gx_inner_xR in HJin. destruct HJin as (memS & HJi & HAG).
pose proof HJi as (_ & _ & _ & _ & _ & _ & _ & _ & _ & HBLK & _).
replace a with (p + (a - p)) by lia.
rewrite (HBLK p n (a - p) H1 H2 ltac:(lia) ltac:(replace (p + (a - p)) with a by lia; exact HnF)).
apply HAG. rewrite unsigned_lit_small by lia. intros Hg.
apply (blk_img_x SEGS B ARx LAWS ly S Hp W mem md p n (p + (a - p)) HAR H1 ltac:(lia)). exact (proj1 (HGc _ Hg)).
Qed.
(* :864 rrd_drp at R: dr_post_xR's body (W_contract_xR.v) at the return state *)
Definition rrd_drp_xR (regs : bvmap 5 word) ly S (Hp : list Z) (W : world SEGS) (mem : word -> option byte) (md : Model)
(SA HA : Z) (e : rentry) (h : hsrc) (c : ctl) (O : list byte) (mx no cap out : Z) (kr : nat)
(ly' : alayout) (S' : astate) (Hp' : list Z) (W' : world SEGS) (regs' : bvmap 5 word) (mem' : word -> option byte)
(md' : Model) : Prop :=
exists k (e' : rentry) (h' : hsrc) (out' ev' : Z) (LB : list byte) rest,
let fin := dr_fin c mx no cap e h in
let live := dr_live c h in
let cap' := if live then drain_b_c.ds_ocap fin else cap in
ajournal_gx_xR (SK := SK) SEGS B PST ARx R (G_DR B RG) 0 [] DRAIN_STK_x (spZ regs) (dr_fp SA e h cap out)
  ly S Hp W mem md [] ly' S' Hp' W' mem' md' k /\
aregs_preserved regs regs' /\
apres_kept B W mem W' mem' /\
mo_le MT S S' (dr_cost MT c mx no cap e h) /\
rp_RM RP S' kr /\
Permutation (ablocks B ly S) (aentry_blks e ++ asrc_blks h ++ aout_blks cap out ++ rest) /\
Permutation (ablocks B ly' S') (aentry_blks e' ++ asrc_blks h' ++ aout_blks cap' out' ++ rest) /\
garr8 SEGS (arm W' mem') SA (bzs (entry_bytes e')) /\ awr W' mem' SA AENT /\ aentry_ok B ly' S' W' mem' e' /\
re_fd e' = re_fd e /\ re_eof e' = (if hs_closed h =? 1 then 1 else re_eof e) /\ 0 < re_cap e' /\
re_cap e' = drain_b_c.ds_cap fin /\ bzs (re_U e') = drain_b_c.ds_u fin /\
re_skip e' = (if drain_b_c.ds_skip fin then 1 else 0) /\
drain_b_c.keys_texts (re_keys e') = drain_b_c.ds_H fin /\ drain_b_c.ent_ka e' = drain_b_c.ds_ka fin /\
((re_hp e' = re_hp e /\ re_kh e' = re_kh e) \/ re_kh e' <= 2 ^ 30) /\
NoDup (drain_b_c.keys_texts (re_keys e')) /\
RelayKeys.same_set (drain_b_c.keys_texts (re_keys e')) (RelayModel.upds (drain_b_c.keys_texts (re_keys e)) (dr_lines h)) /\
asrc_at B ly' S' W' mem' HA h' /\
(forall a, rg_s RG <= a < rg_s RG + 4 * ASRC -> ~ (HA <= a < HA + ASRC) -> abyte_kept W mem W' mem' a) /\
hl_cap (hs_expected h') = drain_b_c.ds_ecap fin /\
hl_cap (hs_expected h') <= Z.max 8 (Z.max (hl_cap (hs_expected h)) (2 * hl_n (hs_expected h'))) /\
hs_fd h' = hs_fd h /\ hs_closed h' = hs_closed h /\ hs_eintr h' = 0 /\
hl_recs (hs_pending h') = [] /\ hs_off h' = 0 /\
hl_v (hs_pending h') = hl_v (hs_pending h) /\ hl_cap (hs_pending h') = hl_cap (hs_pending h) /\
hs_partial h' = hs_partial h /\
hs_state h' = RelayModel.feed (hs_state h) (bzs (pending_stream h)) /\
map snd (hl_recs (hs_expected h')) = map snd (hl_recs (hs_expected h)) ++ map (map (Z_to_bv 8)) (dr_lines h) /\
firstn (length (hl_recs (hs_expected h))) (hl_recs (hs_expected h')) = hl_recs (hs_expected h) /\
hs_held h' = hs_held h /\
re_skip e' = hs_overlong h' /\ (re_skip e' = 0 -> bzs (re_U e') = bzs (hs_W h')) /\
bzs LB = RelayModel.with_nul (dr_lines h) /\
aout_at B RG ly' S' W' mem' (dr_ctl c h ev') (if live then O ++ LB else O) mx (if live then no + dr_tot h else no) cap' out'.
(* :903 rrd_drp_of at R *)
Lemma rrd_drp_of_xR : forall regs ly S Hp W mem md SA HA e h c O mx no cap out kr W' c',
  dr_post_xR B PST ARx R MT RP RG regs ly S Hp W mem md SA HA e h c O mx no cap out kr W' c' ->
  exists ly' S' Hp' regs' mem' md', c' = mkCfg (mkst regs' (getr regs 1) mem' (seg_rom SEGS)) md' /\
  rrd_drp_xR regs ly S Hp W mem md SA HA e h c O mx no cap out kr ly' S' Hp' W' regs' mem' md'.
Proof.
intros regs ly S Hp W mem md SA HA e h c O mx no cap out kr W' c' H.
destruct H as (ly' & S' & Hp' & regs' & mem' & md' & k & e' & h' & out' & ev' & LB & rest & H). cbv zeta in H.
destruct H as (Hc & REST).
exists ly', S', Hp', regs', mem', md'. split; [exact Hc|]. exists k, e', h', out', ev', LB, rest. exact REST.
Qed.
(* :982 rrd_closed_rrg at R *)
Lemma rrd_closed_rrg_xR : forall cx i regs F FL ly1 S1 Hp1 W1 m1 md k1,
  RBASE B ARx MT RP MMAX RG cx -> rmopen cx i = false -> RMHD RG cx i regs F ->
  RHELD_xR B PST ARx MT RP RG R cx F FL ly1 S1 Hp1 W1 m1 md k1 ->
  RRG_xR B PST ARx MT RP MMAX RG R cx i W1 (cfg_at SEGS (BASE + A_rr_ge) regs m1 md).
Proof.
intros cx i regs F FL ly1 S1 Hp1 W1 m1 md k1 HB Hop HMH HH.
pose proof HB as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HPERM0 & HTM & HPK & _).
pose proof HMH as (_ & _ & _ & HFD0 & Hi & Hfd).
pose proof HH as (HLV & HREL & HOUT & HPERM & HGS & _ & HMO0 & _ & HRM0 & HCNT0).
assert (HND : List.NoDup (map re_fd (rxes cx))) by (eapply rm_base_nodup; exact HB).
pose proof HREL as (R1 & R2 & R3 & R4 & R5 & R6 & R7 & R8 & (tail & T1 & T2 & T3) & R10 & R11).
assert (HAR : ARx ly1 S1 Hp1 W1 m1 md) by (destruct HLV as (fpos & HJ & _); eapply ajournal_gx_AR_xR; exact HJ).
destruct (alx_blocks _ _ _ LAWS ly1 S1 Hp1 W1 m1 md (rxG0 cx) ATABLE HAR R8) as (_ & _ & _ & _ & HPpres & _).
change (req_size ATABLE) with 896 in HPpres.
assert (He : aentry_ok B ly1 S1 W1 m1 (rnth cx i)).
{ rewrite Forall_forall in R10. exact (R10 _ (nth_In (rxes cx) relay_remove_b_c.no_entry Hi)). }
pose proof He as (_ & _ & P1 & P2 & _).
assert (HDR : rr_drains (rxFD cx) (rxes cx) = false) by (rewrite (rm_drains _ _ HND HFD0 Hi Hfd); exact Hop).
exists regs, ly1, S1, Hp1, m1, md, k1, F, FL, (rnth cx i), (rxh cx), 0, [], (rxout cx), 0.
split; [reflexivity|].
split; [exact HMH|].
split; [exact HLV|].
split; [unfold rmdrel; rewrite Hop; reflexivity|].
split; [exact He|].
split.
{ unfold rmtbl. split; [exact R1|]. split; [exact R2|]. split; [unfold rN; exact R3|]. split; [exact R4|].
  split; [exact R5|]. split; [exact R6|]. split; [exact R8|].
  split; [rewrite (rmd_eb_len _ P1 P2); reflexivity|].
  split.
  { exists tail. split; [unfold rN; exact T1|]. unfold rmTpre, rmTpost.
    rewrite (rmd_concat_split entry_bytes (rxes cx) relay_remove_b_c.no_entry i Hi) in T3.
    rewrite <- !app_assoc in T3. exact T3. }
  split.
  { intros o Ho. apply (apresent_writable SEGS). apply (proj1 (HPpres (rmSA cx i + o) ltac:(unfold rmSA, AENT in *; lia))). }
  rewrite Forall_forall in R10 |- *. intros e'' He''. apply R10.
  apply (Permutation_in _ (Permutation_sym (rm_remove_perm (rxes cx) i relay_remove_b_c.no_entry Hi))).
  right. exact He''. }
split.
{ unfold rmc1, rmO1, rmcap1, rmlive. rewrite Hop. cbn [andb]. exact HOUT. }
split.
{ unfold rmsrc, rmcap1, rmlive. rewrite Hop. cbn [andb].
  eapply perm_trans; [exact HPERM|]. rewrite HDR. apply perm_skip. cbn [app].
  rewrite (app_assoc (aentry_blks (rnth cx i)) (rmOB cx i)). apply Permutation_app_tail.
  unfold rmOB. apply rmd_blks_split. exact Hi. }
split.
{ unfold rmgs. intros a Ha _. exact (HGS a Ha). }
pose proof (rm_tr_split _ _ HND HFD0 Hi Hfd) as TS. unfold rmtrD in TS. rewrite Hop in TS. cbn [app] in TS.
assert (BB : blocks_bytes S1 = blocks_bytes (rxS cx)).
{ rewrite (blocks_bytes_bsum B ly1 S1), (blocks_bytes_bsum B (rxly cx) (rxS cx)), (bsum_perm _ _ HPERM),
    (bsum_perm _ _ HPERM0). reflexivity. }
split.
{ (* the room round: no drain, so the rest of the trace is the whole trace and rmbud's rp_RM is RHELD's *)
  unfold rmbud. rewrite TS in HTM, HPK, HRM0.
  split; [exact HMO0|]. split; [lia|]. split; [rewrite TS; lia|]. split; [exact HTM|].
  split; [rewrite BB; exact HPK | exact HRM0]. }
(* gestures_end's count premise: its constant peak 4 is under RHELD's rr_pk = tr_peakP + 4 *)
apply (cnt_ok_pk_mono RP (rr_pk (rtr cx)) gse_pk (ablocks B ly1 S1) (ablocks B ly1 S1)); [|exact HCNT0].
intros P. unfold gse_pk, rr_pk. cbv beta. lia.
Qed.
(* :1070 rmd_tbl_drain at R *)
Lemma rmd_tbl_drain_xR : forall cx i ly1 S1 Hp1 W1 m1 md1 ly2 S2 Hp2 W2 m2 md2 STK sp0 kc e' X,
  (i < length (rxes cx))%nat -> rg_place B RG ->
  arelay_at B RG ly1 S1 W1 m1 (rxG0 cx) (rxes cx) -> ARx ly1 S1 Hp1 W1 m1 md1 ->
  ajournal_gx_xR (SK := SK) SEGS B PST ARx R (G_DR B RG) 0 [] STK sp0 ((rmSA cx i, rmSA cx i + AENT) :: ablocks_fp X)
    ly1 S1 Hp1 W1 m1 md1 [] ly2 S2 Hp2 W2 m2 md2 kc ->
  apres_kept B W1 m1 W2 m2 -> ARx ly2 S2 Hp2 W2 m2 md2 ->
  ~ In (rxG0 cx, ATABLE) X -> (forall b, In b (rmOB cx i) -> ~ In b X) -> ~ In (rxG0 cx, ATABLE) (rmOB cx i) ->
  (forall b, In b X -> In b (ablocks B ly1 S1)) -> (forall b, In b (rmOB cx i) -> In b (ablocks B ly1 S1)) ->
  In (rxG0 cx, ATABLE) (ablocks B ly2 S2) -> (forall b, In b (rmOB cx i) -> In b (ablocks B ly2 S2)) ->
  Forall (fun r => 0 < fst r) ((rmSA cx i, rmSA cx i + AENT) :: ablocks_fp X) ->
  garr8 SEGS (arm W2 m2) (rmSA cx i) (bzs (entry_bytes e')) -> awr W2 m2 (rmSA cx i) AENT ->
  length (re_pad1 e') = 4%nat -> length (re_pad2 e') = 4%nat ->
  rmtbl B RG cx i ly2 S2 W2 m2 (entry_bytes e').
Proof.
intros cx i ly1 S1 Hp1 W1 m1 md1 ly2 S2 Hp2 W2 m2 md2 STK sp0 kc e' X Hi RGP HREL HAR1 HJd HPK HAR2 NT NOX NTO XS OS1 T2 OS2
  HFP0 HG8 HAW P1' P2'.
pose proof asan_consts as (C1 & _).
pose proof RGP as (_ & _ & _ & _ & _ & _ & RGIMG & _).
pose proof HREL as (R1 & R2 & R3 & R4 & R5 & R6 & R7 & R8 & (tail & T1 & T2t & T3) & R10 & R11).
assert (Hok : Forall (fun e => length (re_pad1 e) = 4%nat /\ length (re_pad2 e) = 4%nat) (rxes cx)).
{ eapply Forall_impl; [|exact R10]. intros e (_ & _ & Q1 & Q2 & _). split; assumption. }
assert (He : aentry_ok B ly1 S1 W1 m1 (rnth cx i)).
{ rewrite Forall_forall in R10. exact (R10 _ (nth_In (rxes cx) relay_remove_b_c.no_entry Hi)). }
pose proof He as (_ & _ & P1 & P2 & _).
destruct (alx_blocks _ _ _ LAWS ly1 S1 Hp1 W1 m1 md1 (rxG0 cx) ATABLE HAR1 R8) as (HP16 & HP4096 & HPceil & _).
change (req_size ATABLE) with 896 in HPceil.
assert (HGDR : gx_ok SEGS B (G_DR B RG)) by (eapply gx_ok_sub; [intros a Ha; apply rr_G_DR_RR; exact Ha | exact HG]).
(* g_src, g_nsrc, g_capsrc: image bytes outside G_DR *)
assert (GK : forall a, rg_src RG <= a < rg_src RG + 8 \/ rg_nsrc RG <= a < rg_nsrc RG + 4 \/
  rg_capsrc RG <= a < rg_capsrc RG + 4 -> abyte_kept W1 m1 W2 m2 a).
{ intros a Ha.
  assert (HIO : in_img SEGS a /\ ~ Exists (in_zr a) (as_owned_static B) /\ ~ (as_errno B <= a < as_errno B + 4)).
  { destruct Ha as [Ha|[Ha|Ha]].
    - apply RGIMG. unfold rg_rng. right; right; left. exact Ha.
    - apply RGIMG. unfold rg_rng. right; left. exact Ha.
    - destruct (HRGI a (or_introl Ha)) as [Hi1 Ho1]. split; [exact Hi1|]. split; [exact Ho1|].
      exact (rr_capsrc_nerr B RG HRGP a Ha). }
  destruct HIO as (Hi1 & Ho1 & He1).
  assert (Hq1 : ~ Exists (in_zr a) PST).
  { apply PSTG. unfold rr_gcells. do 2 apply Exists_cons_tl.
    destruct Ha as [Ha|[Ha|Ha]]; [apply Exists_cons_hd | apply Exists_cons_tl, Exists_cons_hd |
      do 2 apply Exists_cons_tl; apply Exists_cons_hd]; cbn [fst snd]; lia. }
  eapply rr_img_kept_xR;
    [intros x Hx; exact Hx | exact HJd | exact HFP0 | exact HPK | exact Hi1 | exact Ho1 | exact He1 | exact Hq1 |].
  apply (rr_nG_DR B RG HRGP). destruct Ha as [Ha|[Ha|Ha]]; [right; left | right; right; left | right; right; right; left];
    exact Ha. }
(* the table's bytes outside slot i *)
assert (TK : forall a, rxG0 cx <= a < rxG0 cx + 896 -> ~ (rmSA cx i <= a < rmSA cx i + AENT) ->
  aview SEGS (w_H W2) m2 a = aview SEGS (w_H W1) m1 a).
{ intros a Ha Hns. eapply rmd_blk_kept_xR; [exact HGDR | exact HJd | exact HAR1 | exact R8 | exact T2 |
    change (req_size ATABLE) with 896; exact Ha |].
  intros Hf. apply inFP_cons in Hf as [Hf|Hf]; [exact (Hns Hf)|].
  apply (rmd_notin_fp ly1 S1 Hp1 W1 m1 md1 X (rxG0 cx) ATABLE a HAR1 R8 NT XS); [change (req_size ATABLE) with 896; exact Ha | exact Hf]. }
unfold rmtbl.
split; [apply (akept_vm W1 m1 W2 m2 (rg_src RG) 8 (rxG0 cx)); [intros x Hx; apply GK; left; cbn in Hx; lia | exact R1]|].
split; [apply (akept_awr W1 m1 W2 m2 (rg_src RG) 8); [intros x Hx; apply GK; left; lia | exact R2]|].
split; [apply (akept_vm W1 m1 W2 m2 (rg_nsrc RG) 4 (rN cx)); [intros x Hx; apply GK; right; left; cbn in Hx; lia | exact R3]|].
split; [apply (akept_awr W1 m1 W2 m2 (rg_nsrc RG) 4); [intros x Hx; apply GK; right; left; lia | exact R4]|].
split; [apply (akept_vm W1 m1 W2 m2 (rg_capsrc RG) 4 16); [intros x Hx; apply GK; right; right; cbn in Hx; lia | exact R5]|].
split; [apply (akept_awr W1 m1 W2 m2 (rg_capsrc RG) 4); [intros x Hx; apply GK; right; right; lia | exact R6]|].
split; [exact T2|].
split; [rewrite (rmd_eb_len _ P1' P2'); reflexivity|].
split.
{ exists tail. split; [exact T1|]. unfold rmTpre, rmTpost.
  pose proof (f_equal (@length _) (rmd_concat_split entry_bytes (rxes cx) relay_remove_b_c.no_entry i Hi)) as LEN.
  rewrite !length_app in LEN. rewrite length_app in T2t. unfold ATABLE in T2t.
  assert (HF1 : Forall (fun e => length (re_pad1 e) = 4%nat /\ length (re_pad2 e) = 4%nat) (firstn i (rxes cx))).
  { rewrite <- (firstn_skipn i (rxes cx)) in Hok. apply Forall_app in Hok as [HF1 _]. exact HF1. }
  pose proof (rmd_concat_len _ HF1) as LPRE. rewrite length_firstn in LPRE.
  replace (Nat.min i (length (rxes cx))) with i in LPRE by lia.
  pose proof (rmd_eb_len (nth i (rxes cx) relay_remove_b_c.no_entry) P1 P2) as LE. pose proof (rmd_eb_len _ P1' P2') as LE'.
  rewrite (rmd_concat_split entry_bytes (rxes cx) relay_remove_b_c.no_entry i Hi) in T3.
  rewrite <- !app_assoc in T3.
  unfold bzs in *. rewrite !map_app in T3 |- *.
  apply garr8_app in T3 as [Ta Tb]. apply garr8_app in Tb as [_ Tc].
  rewrite !length_map in Tc. rewrite LE in Tc.
  apply garr8_app. split.
  - apply (W_gesture_end.ge_garr8_kept (w_H W1) (w_H W2) m1 m2 _ _ Ta). intros b Hb.
    rewrite !length_map, LPRE in Hb. apply TK; unfold rmSA, AENT; lia.
  - rewrite !length_map, LPRE. apply garr8_app. split.
    + unfold rmSA, AENT in HG8. replace (rxG0 cx + Z.of_nat (56 * i)) with (rxG0 cx + 56 * Z.of_nat i) by lia.
      exact HG8.
    + rewrite length_map, LE'. rewrite LPRE in Tc.
      apply (W_gesture_end.ge_garr8_kept (w_H W1) (w_H W2) m1 m2 _ _ Tc). intros b Hb.
      rewrite length_app, !length_map in Hb. apply TK; unfold rmSA, AENT; lia. }
split; [exact HAW|].
rewrite Forall_forall in R10 |- *. intros e'' He''.
assert (Hin'' : In e'' (rxes cx)).
{ apply (Permutation_in _ (Permutation_sym (rm_remove_perm (rxes cx) i relay_remove_b_c.no_entry Hi))).
  right. exact He''. }
assert (OBe : forall b, In b (aentry_blks e'') -> In b (rmOB cx i)).
{ intros b Hb. unfold rmOB. apply in_concat. exists (aentry_blks e''). split; [apply in_map; exact He'' | exact Hb]. }
apply (aentry_ok_kept B ly1 S1 W1 m1 ly2 S2 W2 m2 e'' (R10 _ Hin'')).
- intros r Hr a Ha. destruct (rmd_aentry_fp ly1 S1 W1 m1 e'' (R10 _ Hin'') r Hr a Ha) as (p & n & Hpn & Hpa).
  pose proof (OBe _ Hpn) as Hob.
  split.
  + eapply rmd_blk_kept_xR; [exact HGDR | exact HJd | exact HAR1 | exact (OS1 _ Hob) | exact (OS2 _ Hob) | exact Hpa |].
    intros Hf. apply inFP_cons in Hf as [Hf|Hf].
    * assert (Hne : (rxG0 cx, ATABLE) <> (p, n)) by (intros E; rewrite E in NTO; exact (NTO Hob)).
      pose proof (sep_blocks_x SEGS B ARx LAWS ly1 S1 Hp1 W1 m1 md1 _ _ _ _ HAR1 R8 (OS1 _ Hob) Hne) as D.
      unfold zdisjoint in D. cbn [fst snd] in D. change (req_size ATABLE) with 896 in D.
      unfold rmSA, AENT in Hf. clear - D Hf Hpa Hi R7. lia.
    * exact (rmd_notin_fp ly1 S1 Hp1 W1 m1 md1 X p n a HAR1 (OS1 _ Hob) (NOX _ Hob) XS Hpa Hf).
  + intros _. apply (apresent_writable SEGS).
    destruct (alx_blocks _ _ _ LAWS ly2 S2 Hp2 W2 m2 md2 p n HAR2 (OS2 _ Hob)) as (_ & _ & _ & _ & Hpres & _).
    exact (proj1 (Hpres a Hpa)).
- intros b Hb. exact (OS2 _ (OBe _ Hb)).
Qed.
(* :1180 rrd_open_rrg at R *)
Lemma rrd_open_rrg_xR : forall cx i regsc regs2 F FL fpos ly1 S1 Hp1 W1 m1 md1 k1 ly2 S2 Hp2 W2 m2 md2 k2,
  RBASE B ARx MT RP MMAX RG cx -> rmopen cx i = true -> RMHD RG cx i regs2 F ->
  RHELD_xR B PST ARx MT RP RG R cx F FL ly1 S1 Hp1 W1 m1 md1 k1 ->
  ajournal_gx_xR (SK := SK) SEGS B PST ARx R (G_RR B RG) 0 [] RR_STK_x (rsp0 cx) (rFP cx)
    (rxly cx) (rxS cx) (rxHp cx) (rxW cx) (rxmem cx) (rxmd cx) [(0, fpos)] ly1 S1 Hp1 W1 m1 md1 k1 ->
  rr_frame cx fpos F FL ly1 W1 m1 ->
  ajournal_gx_xR (SK := SK) SEGS B PST ARx R (G_RR B RG) 0 [] RR_STK_x (rsp0 cx) (rFP cx)
    (rxly cx) (rxS cx) (rxHp cx) (rxW cx) (rxmem cx) (rxmd cx) [(0, fpos)] ly2 S2 Hp2 W2 m2 md2 k2 ->
  spZ regsc = rsp0 cx - RR_FRAME ->
  rrd_drp_xR regsc ly1 S1 Hp1 W1 m1 md1 (rmSA cx i) (rmHA RG cx) (rnth cx i) (rxh cx) (rxc cx) (rxO cx) (rxmx cx) (rmno cx)
    (rxcap cx) (rxout cx) (Z.to_nat (tr_cost MT_rk (rmtrK cx i ++ rmtrF cx i)) + rxkr cx) ly2 S2 Hp2 W2 regs2 m2 md2 ->
  RRG_xR B PST ARx MT RP MMAX RG R cx i W2 (cfg_at SEGS (BASE + A_rr_ge) regs2 m2 md2).
Proof.
intros cx i regsc regs2 F FL fpos ly1 S1 Hp1 W1 m1 md1 k1 ly2 S2 Hp2 W2 m2 md2 k2 HB Hop HMH HH HJ1 HFR1 HJ2 Hspc HD.
pose proof asan_consts as (C1 & _).
pose proof HB as (_ & _ & _ & RGP & _ & _ & _ & _ & _ & _ & _ & _ & HPERM0 & _).
pose proof HMH as (_ & _ & _ & HFD0 & Hi & Hfd).
pose proof HH as ((fpos' & _ & HROM1 & HPK1 & _ & HLK1 & HWK1) & HREL & HOUT & HPERM & HGS & HSRC & HMO0 & _ & _ & HCNT0).
pose proof HREL as (_ & _ & _ & _ & _ & _ & R7 & R8 & _ & R10 & _).
assert (HND : List.NoDup (map re_fd (rxes cx))) by (eapply rm_base_nodup; exact HB).
assert (Heof : re_eof (rnth cx i) = 0) by (unfold rmopen in Hop; apply Z.eqb_eq; exact Hop).
assert (HDR : rr_drains (rxFD cx) (rxes cx) = true) by (rewrite (rm_drains _ _ HND HFD0 Hi Hfd); exact Hop).
pose proof (HSRC i Hi Hfd Heof) as HSO.
assert (HAR1 : ARx ly1 S1 Hp1 W1 m1 md1) by (eapply ajournal_gx_AR_xR; exact HJ1).
destruct (alx_blocks _ _ _ LAWS ly1 S1 Hp1 W1 m1 md1 (rxG0 cx) ATABLE HAR1 R8) as (_ & HP4096 & HPceil & _).
change (req_size ATABLE) with 896 in HPceil.
assert (He : aentry_ok B ly1 S1 W1 m1 (rnth cx i)).
{ rewrite Forall_forall in R10. exact (R10 _ (nth_In (rxes cx) relay_remove_b_c.no_entry Hi)). }
assert (Hcap0 : 0 <= re_cap (rnth cx i)) by (clear - He; destruct He as (_ & _ & _ & _ & _ & HC & _); lia).
destruct (W_gesture_end.aout_facts B RG _ _ _ _ _ _ _ _ _ _ HOUT) as (Hmx & _ & Hcp).
assert (Hcapo : 0 <= rxcap cx) by (destruct Hcp as [(Hc & _) | (Hc & _)]; lia).
destruct HD as (kc & e' & h' & out' & ev' & LB & rest & HD). cbv zeta in HD.
destruct HD as (HJd & _ & HPKd & HMd & HRMd & HP1 & HP2 & HG8 & HAW & HEOK & D10 & D11 & D12 & D13 & D14 & D15 & D16 &
  D17 & D18 & D19 & D20 & HSRC' & HGSd & D23 & D24 & D25 & D26 & D27 & D28 & D29 & D30 & D31 & D32 & D33 & D34 & D35 &
  D36 & D37 & D38 & D39 & HOUTd).
rewrite Hspc in HJd.
assert (HAR2 : ARx ly2 S2 Hp2 W2 m2 md2) by (eapply ajournal_gx_AR_xR; exact HJd).
assert (HGDR : gx_ok SEGS B (G_DR B RG)) by (eapply gx_ok_sub; [intros a Ha; apply rr_G_DR_RR; exact Ha | exact HG]).
(* the blocks: the entry's, in entry i's drain form; drain's rest; the return's *)
assert (P0 : Permutation (ablocks B ly1 S1) (aentry_blks (rnth cx i) ++ asrc_blks (rxh cx) ++
  aout_blks (rxcap cx) (rxout cx) ++ (rxG0 cx, ATABLE) :: rmOB cx i ++ rxrest cx)).
{ eapply perm_trans; [exact HPERM|]. rewrite HDR.
  eapply perm_trans; [|apply rmd_perm_pre]. apply perm_skip. apply Permutation_app_tail. apply rmd_blks_split. exact Hi. }
pose proof (rmd_perm_rest _ _ _ _ _ _ _ _ HP1 P0) as HR.
pose proof (rmd_perm_post _ _ _ _ _ _ _ _ HP2 HR) as P2X.
assert (ND1 : List.NoDup ((aentry_blks (rnth cx i) ++ asrc_blks (rxh cx) ++ aout_blks (rxcap cx) (rxout cx)) ++
  (rxG0 cx, ATABLE) :: rmOB cx i ++ rxrest cx)).
{ rewrite <- !app_assoc. apply (Permutation_NoDup P0). exact (W_gestures_end.gse_nodup_x B ARx LAWS BLKN _ _ _ _ _ _ HAR1). }
destruct (rmd_nodup_mid _ _ _ _ ND1) as (NT & NTO & NOX).
assert (XS : forall b, In b (aentry_blks (rnth cx i) ++ asrc_blks (rxh cx) ++ aout_blks (rxcap cx) (rxout cx)) ->
  In b (ablocks B ly1 S1)).
{ intros b Hb. apply (Permutation_in _ (Permutation_sym HP1)).
  apply in_app_or in Hb as [Hb|Hb]; [apply in_or_app; left; exact Hb|]. apply in_or_app; right.
  apply in_app_or in Hb as [Hb|Hb]; [apply in_or_app; left; exact Hb|]. apply in_or_app; right.
  apply in_or_app; left; exact Hb. }
assert (OS1 : forall b, In b (rmOB cx i) -> In b (ablocks B ly1 S1)).
{ intros b Hb. apply (Permutation_in _ (Permutation_sym P0)). apply in_or_app; right. apply in_or_app; right.
  apply in_or_app; right. right. apply in_or_app; left; exact Hb. }
assert (T2 : In (rxG0 cx, ATABLE) (ablocks B ly2 S2)) by (apply (Permutation_in _ (Permutation_sym P2X)); left; reflexivity).
assert (OS2 : forall b, In b (rmOB cx i) -> In b (ablocks B ly2 S2)).
{ intros b Hb. apply (Permutation_in _ (Permutation_sym P2X)). right. apply in_or_app; right.
  apply in_or_app; left; exact Hb. }
(* drain's footprint: the slot and drain's blocks *)
assert (FP0 : Forall (fun r => 0 < fst r) ((rmSA cx i, rmSA cx i + AENT) ::
  ablocks_fp (aentry_blks (rnth cx i) ++ asrc_blks (rxh cx) ++ aout_blks (rxcap cx) (rxout cx)))).
{ constructor; [cbn [fst]; unfold rmSA, AENT; lia|].
  unfold ablocks_fp. apply Forall_map. apply Forall_forall. intros [p n] Hb. cbn [fst].
  destruct (alx_blocks _ _ _ LAWS ly1 S1 Hp1 W1 m1 md1 p n HAR1 (XS _ Hb)) as (_ & H4 & _). lia. }
assert (FPB : forall a, inFP (dr_fp (rmSA cx i) (rnth cx i) (rxh cx) (rxcap cx) (rxout cx)) a ->
  exists b n, In (b, n) (ablocks B ly1 S1) /\ b <= a < b + req_size n).
{ intros a Ha. unfold dr_fp in Ha. apply inFP_cons in Ha as [Ha|Ha].
  - exists (rxG0 cx), ATABLE. split; [exact R8|]. change (req_size ATABLE) with 896. unfold rmSA, AENT in Ha. lia.
  - apply inFP_ablocks_fp_inv in Ha as (p & n & Hpn & Hpa). exists p, n. split; [exact (XS _ Hpn) | exact Hpa]. }
(* the pieces of RRG *)
assert (HLV2 : RLIVE_xR B PST ARx RG R cx F FL ly2 S2 Hp2 W2 m2 md2 k2).
{ eapply (rr_live_call_xR B PST ARx MT RP MMAX RG LAWS HRGP HROMO PSTR PSTG R cx F FL fpos ly1 S1 Hp1 W1 m1 md1 k1
    (G_DR B RG) DRAIN_STK_x);
    [exact HB | exact HJ1 | exact HROM1 | exact HPK1 | exact HFR1 | exact HLK1 | exact HWK1 | exact HGDR |
     intros a Ha; exact Ha | unfold DRAIN_STK_x, DRAIN_STK, DRAIN_FRAME, SL_STK, SL_FRAME, ASTACK; lia | exact HJd | exact FP0 |
     exact FPB | exact HPKd | exact HJ2]. }
assert (HREL1 : dr_rel (rxc cx) (rxmx cx) (rmno cx) (rxcap cx) (rnth cx i) (rxh cx) e' h' LB).
{ unfold dr_rel. cbv zeta. repeat match goal with |- _ /\ _ => split end; assumption. }
destruct (rmd_dr_inv_of ly1 S1 W1 m1 (rnth cx i) (rxh cx) (rxj cx) (rmno cx) (rxcap cx) He HSO) as [IV ER].
pose proof (rmd_dr_bytes ly1 S1 ly2 S2 (rxc cx) (rxmx cx) (rmno cx) (rxcap cx) (rxout cx) out' (rnth cx i) (rxh cx)
  e' h' LB rest IV ER HP1 HP2 HREL1) as HBD.
assert (HO2 : aout_at B RG ly2 S2 W2 m2 (rmc1 cx i ev') (rmO1 cx i LB) (rxmx cx) (Z.of_nat (length (rmO1 cx i LB)))
  (rmcap1 cx i) out').
{ unfold rmc1, rmO1, rmcap1, rmlive. rewrite Hop. cbn [andb].
  destruct (dr_live (rxc cx) (rxh cx)) eqn:DL; try rewrite DL in HOUTd.
  - replace (Z.of_nat (length (rxO cx ++ LB))) with (rmno cx + dr_tot (rxh cx)); [exact HOUTd|].
    rewrite length_app, Nat2Z.inj_add. unfold rmno. f_equal.
    unfold dr_tot. rewrite <- D39. unfold bzs. rewrite length_map. reflexivity.
  - unfold rmno in HOUTd. exact HOUTd. }
assert (HP3 : Permutation (ablocks B ly2 S2) ((rxG0 cx, ATABLE) :: aentry_blks e' ++ rmOB cx i ++ rmsrc cx i h' ++
  aout_blks (rmcap1 cx i) out' ++ rxrest cx)).
{ unfold rmsrc, rmcap1, rmlive. rewrite Hop. cbn [andb]. exact P2X. }
assert (HGS2 : rmgs RG cx W2 m2).
{ unfold rmgs. intros a Ha Hj. pose proof (Hj HDR) as Hn.
  exact (rmd_abk_trans _ _ _ _ _ _ a (HGS a Ha) (HGSd a Ha Hn)). }
assert (BB : blocks_bytes S1 = blocks_bytes (rxS cx)).
{ rewrite (blocks_bytes_bsum B ly1 S1), (blocks_bytes_bsum B (rxly cx) (rxS cx)), (bsum_perm _ _ HPERM),
    (bsum_perm _ _ HPERM0). reflexivity. }
pose proof HEOK as (_ & _ & EP1 & EP2 & _).
exists regs2, ly2, S2, Hp2, m2, md2, k2, F, FL, e', h', ev', LB, out',
  (dr_cost MT (rxc cx) (rxmx cx) (rmno cx) (rxcap cx) (rnth cx i) (rxh cx)).
split; [reflexivity|]. split; [exact HMH|]. split; [exact HLV2|].
split; [unfold rmdrel; rewrite Hop; split; [exact HREL1 | exact HSRC']|].
split; [exact HEOK|].
split.
{ eapply (rmd_tbl_drain_xR cx i ly1 S1 Hp1 W1 m1 md1 ly2 S2 Hp2 W2 m2 md2); [exact Hi | exact RGP | exact HREL | exact HAR1 |
    exact HJd | exact HPKd | exact HAR2 | exact NT | exact NOX | exact NTO | exact XS | exact OS1 | exact T2 | exact OS2 |
    exact FP0 | exact HG8 | exact HAW | exact EP1 | exact EP2]. }
split; [exact HO2|]. split; [exact HP3|]. split; [exact HGS2|].
split.
{ apply (rmd_bud_open cx i S1 S2); [exact HB | exact Hop | exact HND | exact HFD0 | exact Hi | exact Hfd | exact HMO0 |
    exact BB | exact HMd | exact HBD | exact (proj1 Hmx) | exact Hcap0 | exact HRMd]. }
(* the room round: gestures_end's count premise at the return state.  Drain moves the count of its own blocks (the
   entry's, the source's, g_out's) by at most its trace's count peak (W_rr_m_dcnt.v), and that peak is within the
   request trace's (W_tr_cnt.v tr_peakP_app), whose rr_pk = peak + 4 RHELD's count fact carries; gse_pk is 4. *)
pose proof (rm_tr_split _ _ HND HFD0 Hi Hfd) as TS. unfold rmtrD in TS. rewrite Hop in TS. cbv beta iota in TS.
apply (cnt_ok_pk_mono RP (rr_pk (rtr cx)) gse_pk (ablocks B ly1 S1) (ablocks B ly2 S2)); [|exact HCNT0].
intros P. unfold gse_pk, rr_pk. cbv beta.
pose proof (W_rr_m_dcnt.rmc_dr_cnt_peak (rxc cx) (rxmx cx) (rmno cx) (rxcap cx) (rxout cx) out' (rnth cx i) (rxh cx)
  e' h' LB P IV ER (rmd_held_ok _ _ _ _ _ He) (rmd_held_ok _ _ _ _ _ HEOK) Hcapo HREL1) as DC. cbv zeta in DC.
rewrite (ReplyCnt.acnt_perm P _ _ HP2), (ReplyCnt.acnt_perm P _ _ HP1),
  (rmd_acnt3 P (aentry_blks e')), (rmd_acnt3 P (aentry_blks (rnth cx i))).
rewrite TS, W_tr_cnt.tr_peakP_app.
lia.
Qed.
Let RUN_R := paj_run_x_xG B PST ARx LAWS R (G_RR B RG) HG 0 [].
Let RUNTO_R := paj_run_to_x_xG B PST ARx LAWS R (G_RR B RG) HG 0 [].
Let BR_R := paj_branch_xR (PI := PI) (R := R).
(* :1324 rr_m_drain at R *)
Theorem rr_m_drain_xR : hop_drain_stmt_xR B PST ARx MT RP MMAX RG R.
Proof.
unfold hop_drain_stmt_xR. intros cx i W1 c1 HB HM KG.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
pose proof HB as (HPRE & _ & _ & RGP & _ & HFDr & _).
destruct HM as (regs1 & ly1 & S1 & Hp1 & m1 & md1 & k1 & F & FL & -> & HRH & H25 & H10 & H24 & HFD0 & Hi & Hfd & HH).
pose proof HH as (HLV & HREL & HOUT & HPERM & HGS & HSRC & HMO0 & HBB0 & HRM0 & HCNT0).
pose proof HLV as (fpos & HJ & HLVr).
pose proof HREL as (_ & _ & _ & _ & _ & _ & Rlen & RIn & (tail & _ & _ & Rtab) & Rok & _).
pose proof HRH as ((Hsp & H3 & H4 & H8 & H9 & H18 & H20 & H21 & H22 & H26 & H27) & H19 & H23).
assert (HAR : ARx ly1 S1 Hp1 W1 m1 md1) by (eapply ajournal_gx_AR_xR; exact HJ).
destruct (alx_blocks _ _ _ LAWS ly1 S1 Hp1 W1 m1 md1 (rxG0 cx) ATABLE HAR RIn) as (HP16 & HP4096 & HPceil & HPh_ia & HPpres & _).
pose proof (proj1 HPh_ia) as HPh.
change (req_size ATABLE) with 896 in HPceil, HPh_ia, HPh, HPpres.
assert (Hok : Forall (fun e => length (re_pad1 e) = 4%nat /\ length (re_pad2 e) = 4%nat) (rxes cx)).
{ eapply Forall_impl; [|exact Rok]. intros e (_ & _ & P1 & P2 & _). split; assumption. }
assert (He : aentry_ok B ly1 S1 W1 m1 (rnth cx i)).
{ rewrite Forall_forall in Rok. exact (Rok _ (nth_In (rxes cx) relay_remove_b_c.no_entry Hi)). }
assert (Hev : 0 <= re_eof (rnth cx i) < 2 ^ 31) by (clear - He; destruct He as ([E0|E1] & _); lia).
pose proof (rmd_eof_cell (arm W1 m1) (rxG0 cx) (rxes cx) tail i Rtab Hok Hi Hev) as Mev.
assert (G8 : rxG0 cx = 8 * (rxG0 cx / 8)).
{ pose proof (Z.div_mod (rxG0 cx) 16 ltac:(lia)) as D. rewrite HP16, Z.add_0_r in D.
  rewrite D at 2. replace (16 * (rxG0 cx / 16)) with ((2 * (rxG0 cx / 16)) * 8) by ring. rewrite Z.div_mul by lia. lia. }
assert (GB : 4096 <= rxG0 cx /\ rxG0 cx + 896 <= 0x7fffff800000) by (unfold ASAN_CEIL in *; lia).
assert (Hi16 : (i < 16)%nat) by lia.
remember (Eimg (Ereg regs1 (rrd_extra (re_eof (rnth cx i))))) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (HAE : env_agree 32 (Ereg regs1 (rrd_extra (re_eof (rnth cx i)))) E)
by (rewrite HE; split; [intros m Hm; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
assert (EEo : forall m (rr : bv 5), Z.of_nat m = bv_unsigned rr -> ew E m = getr regs1 rr)
by (intros m rr Hm; subst E; pose proof (bv_unsigned_in_range 5 rr) as Hr5; change (bv_modulus 5) with 32 in Hr5;
rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_nat; exact Hm).
assert (E10 : ew E 10 = Z_to_bv 64 (rxG0 cx + AENT * Z.of_nat i)) by (rewrite (EEo 10%nat 10%bv eq_refl); exact H10).
assert (E22 : ew E 22 = Z_to_bv 64 SHADOW_OFF) by (rewrite (EEo 22%nat 22%bv eq_refl); exact H22).
assert (E32 : ew E 32 = Z_to_bv 64 (re_eof (rnth cx i)))
by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 _ 0)).
assert (HS : st_ok_pi SEGS VAL E ss_rrd (restrict (w_H W1) (mkst regs1 (Z_to_bv 64 (BASE + A_rr_match)) m1 (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. unfold ss_rrd. apply pa_entry_st_ok_full.
- rewrite HE. apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- unfold rrd_regions. repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
  cbn [base_val]. rewrite E10, unsigned_lit_small by (unfold AENT; lia).
  split; [unfold AENT; lia|]. split; [unfold AENT; lia|]. split; [intros o Ho; lia|].
  constructor; [|constructor].
  apply (chunk_ok_val SEGS E _ (rxG0 cx + AENT * Z.of_nat i) 4 4 (SOff 32 0) (re_eof (rnth cx i)));
  [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
  exact Mev.
- cbn [pairwise_disjoint all_disjoint]. repeat split.
- split; [|split; [exact I | exact I]].
  cbn [rrd_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
  rewrite E10, E22, E32, !unsigned_lit_small by (unfold SHADOW_OFF, AENT in *; lia).
  change (2 ^ 3) with 8. rewrite !Z.pow_0_r, !Z.mod_1_r.
  assert ((rxG0 cx + AENT * Z.of_nat i) mod 8 = 0).
  { unfold AENT. rewrite G8. replace (8 * (rxG0 cx / 8) + 56 * Z.of_nat i) with ((rxG0 cx / 8 + 7 * Z.of_nat i) * 8) by ring.
    apply Z_mod_mult. }
  unfold RRD_PHI, SB, SHADOW_OFF, AENT in *. repeat match goal with |- _ /\ _ => split end; try lia; try exact I. }
clear HE.
assert (HBx : U E rrd_Bx = SHADOW_OFF) by (unfold rrd_Bx; rewrite (U_atom E 22 SHADOW_OFF E22) by (unfold SHADOW_OFF; lia); reflexivity).
assert (SHOK : sh_ok SEGS rrd_Bx rrd_SH E (mrestrict (w_H W1) m1)).
{ constructor; [|constructor].
  eapply shent_ok_of_range.
  + apply (range_addressable_of_block_hp0_x SEGS B ARx LAWS HP0 ly1 S1 Hp1 W1 m1 md1 (rxG0 cx) ATABLE
      (rxG0 cx + AENT * Z.of_nat i) 56 HAR RIn);
    [unfold AENT; lia | change (req_size ATABLE) with 896; unfold AENT; lia].
  + exact HBx.
  + rewrite (U_atom E 10 _ E10) by (unfold AENT; lia). reflexivity.
  + lia.
  + lia.
  + intros x Hx. unfold in_app, SHADOW_OFF, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, AENT in *. lia. }
unfold cfg_at. change (w64 (BASE + A_rr_match)) with (Z_to_bv 64 (BASE + A_rr_match)).
(* the eof field's shadow check (fast path), the eof load, to the test 0x83f60 *)
paj_run_tok_xR RUN_R HS HJ SHOK rrd_Bspan.
{ apply awr_ok_x_cons; [intros a Ha; cbn in Ha; lia | apply awr_ok_x_nil]. }
rrd_mem Em1.
psrr_branch_tok RUN_R BR_R HS SHOK rrd_Bspan.
- (* eof <> 0: the bnez to 0x83f68, nothing changed (the lane's rrA_at_ge_noeof) *)
  rewrite branch_ne_U, (U_atom E 32 _ E32), U_lit in Hc by lia.
  apply negb_true_iff, Z.eqb_neq in Hc.
  assert (Hop : rmopen cx i = false) by (unfold rmopen; apply Z.eqb_neq; exact Hc).
  paj_run_to_tok_xR RUNTO_R HS HJ SHOK rrd_Bspan (AF_fr_relay_remove + 0x184).
  { apply awr_ok_x_cons; [intros a Ha; cbn in Ha; lia | apply awr_ok_x_nil]. }
  rrd_mem Em2.
  lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?ms') =>
    pose proof (regs_kept_of_st_ok_pi _ _ _ regs1 _ RRD_KEPT HS HAE ltac:(vm_compute; reflexivity)) as HK;
    cbn [ms_regs restrict] in HK;
    pmkst HS; rewrite Em2, Em1 in HJ |- *; apply KG;
    apply (rrd_closed_rrg_xR cx i (ms_regs ms') F FL ly1 S1 Hp1 W1 m1 _ k1 HB Hop) end.
  + unfold RMHD. split; [unfold rregs_held, rregs_base, spZ; rewrite !HK by (cbv; tauto); exact HRH|].
    split; [rewrite (HK 25%bv) by (cbv; tauto); exact H25|].
    split; [rewrite (HK 24%bv) by (cbv; tauto); exact H24|].
    exact (conj HFD0 (conj Hi Hfd)).
  + split; [exists fpos; split; [exact HJ | exact HLVr] | exact (proj2 HH)].
- (* eof = 0: jal drain 0x83f64 (the lane's rrA_drain_hop, eof = 0 arm) *)
  rewrite branch_ne_U, (U_atom E 32 _ E32), U_lit in Hc by lia.
  apply negb_false_iff, Z.eqb_eq in Hc.
  assert (Hop : rmopen cx i = true) by (unfold rmopen; apply Z.eqb_eq; exact Hc).
  pose proof HLVr as (HROM1 & HPK1 & HFR1 & HLK1 & HWK1).
  pose proof HPRE as (_ & _ & _ & Hgp & Htp & HstkE & _).
  pose proof HstkE as (_ & _ & Hceil0 & Hslo0 & Hshi0 & H470 & _).
  assert (HND : List.NoDup (map re_fd (rxes cx))) by (eapply rm_base_nodup; exact HB).
  assert (HDR : rr_drains (rxFD cx) (rxes cx) = true) by (rewrite (rm_drains _ _ HND HFD0 Hi Hfd); exact Hop).
  pose proof (HSRC i Hi Hfd Hc) as HSO.
  pose proof HSO as (Hj4 & HSA & HOTH & Hhfd & Hsk & HU & Hb1 & Hb2 & Hb3).
  destruct (W_gesture_end.aout_facts B RG _ _ _ _ _ _ _ _ _ _ HOUT) as (Hmx & _ & _).
  assert (Hcap0 : 0 <= re_cap (rnth cx i)) by (clear - He; destruct He as (_ & _ & _ & _ & _ & HC & _); lia).
  assert (Hno0 : 0 <= rmno cx) by (unfold rmno; lia).
  (* dr_spec's premises from RRM *)
  assert (GE : garr8 SEGS (arm W1 m1) (rmSA cx i) (bzs (entry_bytes (rnth cx i)))).
  { pose proof Rtab as T3. rewrite (rmd_concat_split entry_bytes (rxes cx) relay_remove_b_c.no_entry i Hi) in T3.
    rewrite <- !app_assoc in T3. unfold bzs in T3 |- *. rewrite !map_app in T3.
    apply garr8_app in T3 as [_ T3]. apply garr8_app in T3 as [T3 _].
    assert (HF1 : Forall (fun e => length (re_pad1 e) = 4%nat /\ length (re_pad2 e) = 4%nat) (firstn i (rxes cx))).
    { rewrite <- (firstn_skipn i (rxes cx)) in Hok. apply Forall_app in Hok as [HF1 _]. exact HF1. }
    rewrite length_map, (rmd_concat_len _ HF1), length_firstn in T3.
    replace (Nat.min i (length (rxes cx))) with i in T3 by lia.
    unfold rmSA, AENT. replace (rxG0 cx + 56 * Z.of_nat i) with (rxG0 cx + Z.of_nat (56 * i)) by lia. exact T3. }
  assert (AW : awr W1 m1 (rmSA cx i) AENT).
  { intros o Ho. apply (apresent_writable SEGS). apply (proj1 (HPpres (rmSA cx i + o) ltac:(unfold rmSA, AENT in *; lia))). }
  assert (P0 : Permutation (ablocks B ly1 S1) (aentry_blks (rnth cx i) ++ asrc_blks (rxh cx) ++
    aout_blks (rxcap cx) (rxout cx) ++ (rxG0 cx, ATABLE) :: rmOB cx i ++ rxrest cx)).
  { eapply perm_trans; [exact HPERM|]. rewrite HDR.
    eapply perm_trans; [|apply rmd_perm_pre]. apply perm_skip. apply Permutation_app_tail. apply rmd_blks_split. exact Hi. }
  assert (PRE : Permutation (ablocks B ly1 S1) ((rxG0 cx, ATABLE) :: aentry_blks (rnth cx i) ++ asrc_blks (rxh cx) ++
    aout_blks (rxcap cx) (rxout cx) ++ (rmOB cx i ++ rxrest cx))).
  { eapply perm_trans; [exact P0|].
    pose proof (Permutation_middle (aentry_blks (rnth cx i) ++ asrc_blks (rxh cx) ++ aout_blks (rxcap cx) (rxout cx))
      (rmOB cx i ++ rxrest cx) (rxG0 cx, ATABLE)) as M. rewrite <- !app_assoc in M. apply Permutation_sym. exact M. }
  assert (XS : forall b, In b (aentry_blks (rnth cx i) ++ asrc_blks (rxh cx) ++ aout_blks (rxcap cx) (rxout cx)) ->
    In b (ablocks B ly1 S1)).
  { intros b Hb. apply (Permutation_in _ (Permutation_sym P0)).
    apply in_app_or in Hb as [Hb|Hb]; [apply in_or_app; left; exact Hb|]. apply in_or_app; right.
    apply in_app_or in Hb as [Hb|Hb]; [apply in_or_app; left; exact Hb|]. apply in_or_app; right.
    apply in_or_app; left; exact Hb. }
  pose proof (rm_tr_split _ _ HND HFD0 Hi Hfd) as TS. unfold rmtrD in TS. rewrite Hop in TS. cbv beta iota in TS.
  pose proof HB as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HTM & _ & HMOK & _).
  pose proof (rmd_nn_meas MT _ MLAW (rmd_tl_nn cx i (proj1 Hmx))) as TC.
  assert (NN : rmd_nn (dr_tr (rxc cx) (rxmx cx) (rmno cx) (rxcap cx) (rnth cx i) (rxh cx))).
  { unfold dr_tr. apply rmd_dtr_nn; [exact (proj1 Hmx) | exact Hcap0 | exact Hno0]. }
  pose proof (rmd_nn_meas MT _ MLAW NN) as CN.
  assert (RM1 : tr_max (dr_tr (rxc cx) (rxmx cx) (rmno cx) (rxcap cx) (rnth cx i) (rxh cx)) < MMAX).
  { rewrite TS, rm_tr_max_app in HTM. lia. }
  assert (RM2 : blocks_bytes S1 + tr_peak (dr_tr (rxc cx) (rxmx cx) (rmno cx) (rxcap cx) (rnth cx i) (rxh cx)) <= LIVE_MAX).
  { rewrite TS in HBB0.
    pose proof (tr_peak_prefix (dr_tr (rxc cx) (rxmx cx) (rmno cx) (rxcap cx) (rnth cx i) (rxh cx))
      (rmtrK cx i ++ rmtrF cx i)) as PP. lia. }
  assert (RM3 : mo_ok MT S1 (dr_cost MT (rxc cx) (rxmx cx) (rmno cx) (rxcap cx) (rnth cx i) (rxh cx))).
  { apply (mok_station MT (rxS cx) S1 (tr_cost MT (rtr cx)) 0 _ MLAW HMOK HMO0 CN).
    rewrite TS, rm_tr_cost_app. unfold dr_cost. lia. }
  (* the room round at drain's call: drain gets kr' = what the key run and the two frees charge, plus kr; its room
     premise is RHELD's split exactly (the counting meter's costs are nonnegative), its count premise (drain's peak
     plus 2) is under RHELD's (the request trace's peak plus 4) *)
  pose proof (rmd_nn_meas MT_rk _ rmd_rk_laws (rmd_tl_nn cx i (proj1 Hmx))) as TCk.
  pose proof (rmd_nn_meas MT_rk _ rmd_rk_laws NN) as CNk.
  assert (HRMdr : rp_RM RP S1 (Z.to_nat (dr_cost MT_rk (rxc cx) (rxmx cx) (rmno cx) (rxcap cx) (rnth cx i) (rxh cx)) +
    (Z.to_nat (tr_cost MT_rk (rmtrK cx i ++ rmtrF cx i)) + rxkr cx))).
  { apply (RMM_of RP S1 _ (Z.to_nat (tr_cost MT_rk (rtr cx)) + rxkr cx)); [|exact HRM0].
    rewrite TS, (rm_tr_cost_app_m MT_rk (dr_tr (rxc cx) (rxmx cx) (rmno cx) (rxcap cx) (rnth cx i) (rxh cx))
      (rmtrK cx i ++ rmtrF cx i)).
    unfold dr_cost. lia. }
  assert (HCNTd : cnt_ok_pk RP (dr_pk (rxc cx) (rxmx cx) (rmno cx) (rxcap cx) (rnth cx i) (rxh cx)) (ablocks B ly1 S1)).
  { apply (cnt_ok_pk_mono RP (rr_pk (rtr cx)) _ (ablocks B ly1 S1) (ablocks B ly1 S1)); [|exact HCNT0].
    intros P. unfold dr_pk, rr_pk. cbv beta. rewrite TS, W_tr_cnt.tr_peakP_app. lia. }
  destruct (rr_call_chain_xR B PST ARx MT RP MMAX RG HG R cx F FL ly1 S1 Hp1 W1 m1 md1 k1 HB HLV) as (ch1 & Hch).
  (* the run to drain's entry: jal 0x83f64, ra = 0x83f68 *)
  paj_run_to_tok_xR RUNTO_R HS HJ SHOK rrd_Bspan AF_fr_drain.
  { apply awr_ok_x_cons; [intros a Ha; cbn in Ha; lia | apply awr_ok_x_nil]. }
  rrd_mem Em2.
  lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?ms') =>
    pose proof (regs_kept_of_st_ok_pi _ _ _ regs1 _ RRD_KEPT HS HAE ltac:(vm_compute; reflexivity)) as HK;
    cbn [ms_regs restrict] in HK; prreg HS (1%bv : bv 5) Q1;
    pmkst HS; rewrite Em2, Em1 in HJ |- *; set (regsc := ms_regs ms') in * end.
  lazymatch goal with |- SRrG _ _ _ {| cfg_ms := _; cfg_model := ?md |} _ => set (mdx := md) in * end.
  assert (Hspc : spZ regsc = rsp0 cx - RR_FRAME) by (unfold spZ; rewrite (HK 2%bv) by (cbv; tauto); exact Hsp).
  eapply (SRrG_bind SEGS R R_trans).
  { eapply (W_gestures_end.gse_callS_xR B PST ARx LAWS R R_trans (G_RR B RG) W1 regsc m1 _ RR_STK_x (rsp0 cx) (rFP cx)
      (rxly cx) (rxS cx) (rxHp cx) (rxW cx) (rxmem cx) (rxmd cx) [(0, fpos)] ly1 S1 Hp1 mdx k1 DRAIN_STK_x
      (dr_fp (rmSA cx i) (rnth cx i) (rxh cx) (rxcap cx) (rxout cx)) (-96) (getr regsc 1) ch1
      (fun ly2 S2 W2 regs2 mem2 md2 => exists Hp2, rrd_drp_xR regsc ly1 S1 Hp1 W1 m1 mdx (rmSA cx i) (rmHA RG cx)
         (rnth cx i) (rxh cx) (rxc cx) (rxO cx) (rxmx cx) (rmno cx) (rxcap cx) (rxout cx)
         (Z.to_nat (tr_cost MT_rk (rmtrK cx i ++ rmtrF cx i)) + rxkr cx) ly2 S2 Hp2 W2 regs2 mem2 md2) HG HJ).
    - rewrite Hspc. unfold RR_FRAME. lia.
    - reflexivity.
    - lia.
    - unfold DRAIN_STK_x, DRAIN_STK, DRAIN_FRAME, SL_STK, SL_FRAME, ASTACK. lia.
    - unfold RR_STK_x, RR_STK, RR_FRAME, DRAIN_STK_x. lia.
    - rewrite (HK 3%bv) by (cbv; tauto). rewrite H3. exact Hgp.
    - rewrite (HK 4%bv) by (cbv; tauto). rewrite H4. exact Htp.
    - reflexivity.
    - rewrite Q1. apply ret_ok_codeptr_v; [lia | reflexivity].
    - rewrite Q1. rewrite unsigned_lit_small by lia. lia.
    - replace (rsp0 cx + -96) with (rsp0 cx - RR_FRAME) by (unfold RR_FRAME; lia).
      replace (s0Z regsc) with (rsp0 cx); [exact Hch|].
      unfold s0Z. rewrite (HK 8%bv) by (cbv; tauto). rewrite H8. unfold w64.
      rewrite unsigned_lit_small by (unfold rsp0, RR_STK_x, RR_STK, RR_FRAME, DRAIN_STK_x, DRAIN_STK, DRAIN_FRAME, SL_STK, SL_FRAME, ASTACK in *; lia).
      reflexivity.
    - intros HPRE1.
      assert (H10c : getr regsc 10 = w64 (rmSA cx i)) by (rewrite (HK 10%bv) by (cbv; tauto); exact H10).
      eapply (SRrG_mono SEGS R).
      { exact (DRAIN_R W1 ly1 S1 Hp1 regsc m1 mdx ch1 (rxG0 cx) (rmSA cx i) (rnth cx i) (rxj cx) (rxh cx) (rxc cx)
          (rxO cx) (rxmx cx) (rmno cx) (rxcap cx) (rxout cx) HPRE1 H10c RIn ltac:(unfold rmSA, AENT; lia)
          ltac:(unfold rmSA, AENT, ATABLE; lia) (rmd_sa_align ly1 S1 Hp1 W1 m1 md1 (rxG0 cx) i HAR RIn)
          GE AW He Hj4 HSA HOTH Hhfd Hsk HU HOUT HROM1 (ex_intro _ (rmOB cx i ++ rxrest cx) PRE) Hb1 Hb2 Hb3
          RM1 RM2 RM3 _ HRMdr HCNTd). }
      cbv beta. intros W2 c2 _ HDP. apply rrd_drp_of_xR in HDP.
      destruct HDP as (ly2 & S2 & Hp2 & regs2 & m2 & md2 & -> & HD).
      pose proof HD as (kc & e' & h' & out' & ev' & LB & rest & HDb). cbv zeta in HDb. destruct HDb as (HJd & HPd & _).
      exists ly2, S2, Hp2, regs2, m2, md2, kc. split; [reflexivity|].
      split; [apply rr_lift_DR_xR; exact HJd|]. split; [exact HPd | exists Hp2; exact HD].
    - intros a Ha. left.
      assert (HB1 : exists b n, In (b, n) (ablocks B ly1 S1) /\ b <= a < b + req_size n).
      { unfold dr_fp in Ha. apply inFP_cons in Ha as [Ha|Ha].
        - exists (rxG0 cx), ATABLE. split; [exact RIn|]. change (req_size ATABLE) with 896. unfold rmSA, AENT in Ha. lia.
        - apply inFP_ablocks_fp_inv in Ha as (p & n & Hpn & Hpa). exists p, n. split; [exact (XS _ Hpn) | exact Hpa]. }
      split; [|exact HB1].
      unfold dr_fp in Ha. apply inFP_cons in Ha as [Ha|Ha].
      + unfold rFP, rr_fp. replace a with (rxG0 cx + (a - rxG0 cx)) by lia.
        apply (inFP_ablocks_fp _ (rxG0 cx) ATABLE); [left; reflexivity | change (req_size ATABLE) with 896; unfold rmSA, AENT in Ha; lia].
      + apply inFP_ablocks_fp_inv in Ha as (p & n & Hpn & Hpa). unfold rFP, rr_fp.
        replace a with (p + (a - p)) by lia. apply (inFP_ablocks_fp _ p n); [|lia]. right. rewrite HDR.
        exact (rmd_X_in_rr cx i (p, n) Hi Hpn). }
  cbv beta. intros W2 c2 Hwle2 (ly2 & S2 & Hp2 & regs2 & m2 & md2 & kc & -> & HJ2 & HJc & HP2 & (Hp2' & HD)).
  (* drain's journal and the caller's end at the same state, whose head set is empty (HP0) *)
  assert (EHp : Hp2' = Hp2).
  { destruct HD as (kd & e2 & h2 & o2 & v2 & L2 & r2 & HD). cbv zeta in HD. destruct HD as (HJd & _).
    apply ajournal_gx_AR_xR in HJd. apply ajournal_gx_AR_xR in HJ2.
    rewrite (HP0 _ _ _ _ _ _ HJd), (HP0 _ _ _ _ _ _ HJ2). reflexivity. }
  subst Hp2'.
  apply KG.
  assert (EC : {| cfg_ms := mkst regs2 (getr regsc 1) m2 (seg_rom SEGS); cfg_model := md2 |} =
               cfg_at SEGS (BASE + A_rr_ge) regs2 m2 md2) by (unfold cfg_at; rewrite Q1; reflexivity).
  rewrite EC.
  assert (KP : forall r : bv 5, In r RRD_KEPT -> acallee_saved (bv_unsigned r) -> getr regs2 r = getr regs1 r).
  { intros r Hr Hc0. pose proof (HP2 _ Hc0) as X. rewrite !Z_to_bv_bv_unsigned in X. rewrite X. apply HK. exact Hr. }
  eapply (rrd_open_rrg_xR cx i regsc regs2 F FL fpos ly1 S1 Hp1 W1 m1 mdx k1 ly2 S2 Hp2 W2 m2 md2 (k1 + kc));
    [exact HB | exact Hop | | split; [exists fpos; split; [exact HJ | exact HLVr] | exact (proj2 HH)] | exact HJ |
     exact HFR1 | exact HJ2 | exact Hspc | exact HD].
  unfold RMHD. split.
  { unfold rregs_held, rregs_base, spZ.
    rewrite !KP by rrd_cs. exact HRH. }
  split; [rewrite KP by rrd_cs; exact H25|].
  split; [rewrite KP by rrd_cs; exact H24|].
  exact (conj HFD0 (conj Hi Hfd)).
Qed.
End wR.

End c.
End b.
End a.

