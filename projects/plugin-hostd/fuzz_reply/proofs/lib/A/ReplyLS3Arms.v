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
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_reply/lib/A/W_LLVMFuzzerTestOneInput_drain_x.v, with its module paths and module names changed; 1050 of its 1174 lines of code are new or changed and 6922 lines of the source are left out. *)
(* a Theorem Labs lane's FREE-PIECES row B1c (a Theorem Labs lane): B1c's LS rules at fr_LS3 (lib/A/ReplyLS3.v, LS v3, PROPOSED beside
   fr_LS v2), at the instance LS := fr_LS3 B, RINV := fr_RINV, MT := ameter_triv, MMAX := WR_MMAX.
   proves no function (kind: invariant lemma).

   The two rules v2 could not close (ReplyLSDrain3.v fr_LS_drain_step_p with Hpay, ReplyLSRemove3.v fr_LS_rm_step_p
   with Hout) are proved here at their proposed texts WITHOUT Hpay / Hout:
   - fr_LS3_drain_step_p: the drain's potential step is paid by the 64 per pending byte it releases and the 65 of the
     operation's first input byte.  It adds to ReplyLSDrain3.v's proposed text only premises the drain arm holds
     where it applies LS_drain_step (a working branch 129f255c729 _drain.v dc_calls :5471):
     Hatop, HRI, Hfdj, Hef0 (:5413-5414, the DLK state's), the entry's and the source's model clauses at the drain call
     (DLK's HMOD :5413, amodel_ne :2633-2635: aentry_ok W_rep.v:124-139, asrc_at :91/:101-105/:111-112 through
   alist_at :81, aout_at W_rep.v:177-178), and dr_post's / cnl_post's clauses on what they leave (W_contract.v at
   129f255c729 :943, :952 (aentry_ok e'), :954, :956, :957-959, :961 (asrc_at h'), :964, :966, :967, :970, :972;
   cnl_post: the drain arm's stub _drain.v:223-241 at 129f255c729).  dc_stB / dc_stE hand dc_calls most of these as
   dr_dfun / dr_cfun (:2661-2683) and the
     dc_at models (:5422, :5444); dr_post's :949-950, :957, :964 and :967 are not in dr_dfun at 129f255c729
     (ReplyLSDrain3.v's proposed texts already need them), so dc_stB must add them to what it exports.
   - fr_LS3_rm_step_p: the remove releases the entry's and the source's credit; it adds to ReplyLSRemove3.v's proposed
     text three facts the remove arm holds at rm_rr's state (_remove.v:2398, a working branch
     30d91cacb63), carried with the LS in rm_Q as ReplyLSRemove3.v's (P1) is: the model's blocks are nonnegative
     (rr_blks_pos :2155), the removed entry's keys are >= 14 bytes (HREL :2411, aentry_ok W_rep.v:139) and the source's
     read offset is inside its first pending text (HSRC :2418, asrc_at W_rep.v:104-105).
   Then B1c's other rules at v3 (drain_skip, event_malloc / relay / free / step, cnl_pre, rm_cnl_pre, rm_cshe_pre,
   rm_sr_pre, and the drain_pre / rm_rr_pre parts), each the text of its v2 lemma with fr_LS -> fr_LS3. *)
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
  drain_b_c gestures_end_b_c gesture_end_c relay_remove_b_c RelayCap SlotReads SlotInv SlotDrain3Aux SlotPass2Aux
  relay_remove_b_aux.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require ACfn_cf.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import
  ReplyLS3 ReplyLSDrainPre ReplyLSDrain3 ReplyLSRemove3 ReplyLSEvent3.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require W_LLVMFuzzerTestOneInput_remove.
Import ListNotations.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

Local Notation MT := ameter_triv.
Local Notation MMAX := WR_MMAX.
Local Notation zsum l := (fold_right Z.add 0 l).
Local Notation dset := W_LLVMFuzzerTestOneInput_drain.set_nth.

(* counts of a block at a point: every Permutation hypothesis and the goal, then linear arithmetic *)
Ltac ls3_perm :=
  repeat match goal with H : Permutation _ _ |- _ =>
    let H' := fresh "Hc" in pose proof (proj1 (Permutation_count_occ zzdec _ _) H) as H'; clear H end;
  apply (proj2 (Permutation_count_occ zzdec _ _)); let x := fresh "x" in intros x;
  repeat match goal with H : forall _ : Z * Z, count_occ _ _ _ = count_occ _ _ _ |- _ => specialize (H x) end;
  repeat progress (rewrite ?count_occ_app, ?cnt_cons, ?cnt_nil in *); lia.

(* ================================================================== the weights of a text *)
(* a key or held text x costs |x| + 1 bytes (its block) and W_H * |x| of the potential: 5 |x| + 1 *)
Definition ls3_wk (x : list Z) : Z := 5 * Z.of_nat (length x) + 1.
Lemma ls3_wk_nonneg : forall x, 0 <= ls3_wk x.
Proof. intros x. unfold ls3_wk. lia. Qed.
Lemma ls3_sum_perm : forall l l', Permutation l l' -> zsum (map ls3_wk l) = zsum (map ls3_wk l').
Proof. intros l l' HP. induction HP; cbn [map fold_right]; lia. Qed.
Lemma ls3_sum_incl : forall A Bl, List.NoDup A -> incl A Bl -> zsum (map ls3_wk A) <= zsum (map ls3_wk Bl).
Proof.
  induction A as [|a A IH]; intros Bl Hnd Hinc.
  - cbn [map fold_right]. apply zsum_map_nonneg. exact ls3_wk_nonneg.
  - apply NoDup_cons_iff in Hnd as [Ha Hnd].
    assert (Hin : In a Bl) by (apply Hinc; left; reflexivity).
    destruct (in_split _ _ Hin) as (l1 & l2 & ->).
    assert (Hi : incl A (l1 ++ l2)).
    { intros x Hx. assert (Hx' : In x (l1 ++ a :: l2)) by (apply Hinc; right; exact Hx).
      apply in_app_iff in Hx' as [H1 | [H2 | H3]]; apply in_app_iff;
        [left; exact H1 | subst x; contradiction | right; exact H3]. }
    specialize (IH (l1 ++ l2) Hnd Hi).
    rewrite (ls3_sum_perm (l1 ++ a :: l2) (a :: l1 ++ l2) (Permutation_sym (Permutation_middle l1 l2 a))).
    cbn [map fold_right]. lia.
Qed.
(* the keys a drain's lines can add: at most 5 per byte of the lines with their NULs *)
Lemma ls3_nk_wk : forall Ls, zsum (map ls3_wk (dr3_nk Ls)) <= 5 * Z.of_nat (length (with_nul Ls)).
Proof.
  induction Ls as [|l Ls IH]; [unfold dr3_nk; cbn; lia|].
  unfold dr3_nk in *. cbn [map concat]. rewrite map_app, zsum_app, RelayCap.with_nul_cons_len.
  assert (Hb : dr3_bk l = match gesture l with Some (GBegin, x) => [x] | _ => [] end) by reflexivity.
  rewrite Hb. destruct (gesture l) as [[[|] x]|] eqn:G; cbv beta iota; cbn [map fold_right].
  - pose proof (dr3_gesture_sub l GBegin x G).
    assert (Ew : ls3_wk x = 5 * Z.of_nat (length x) + 1) by reflexivity. lia.
  - lia.
  - lia.
Qed.
(* the held keys after check_no_loss: at most one more per begin line *)
Lemma ls3_upds_len : forall Ls T,
  Z.of_nat (length (RelayModel.upds T Ls)) <= Z.of_nat (length T) + Z.of_nat (count_begin Ls).
Proof.
  induction Ls as [|l Ls IH]; intros T.
  - unfold RelayModel.upds. cbn [fold_left]. replace (count_begin []) with 0%nat by reflexivity. lia.
  - unfold RelayModel.upds in *. cbn [fold_left]. rewrite SlotReads.count_begin_cons.
    pose proof (IH (RelayModel.upd T l)) as I. pose proof (dr3_upd_len T l) as U.
    destruct (is_begin l); lia.
Qed.
(* the relay entry's keys and a held list, as sums of weights *)
Lemma ls3_keys_wk : forall ks,
  dr3_ksz ks + W_H * zsum (map (fun k => Z.of_nat (length (gestures_end_b_c.key_text k))) ks) =
  zsum (map ls3_wk (drain_b_c.keys_texts ks)).
Proof.
  induction ks as [|k ks IH]; [reflexivity|]. unfold dr3_ksz, drain_b_c.keys_texts in *. cbn [map fold_right].
  assert (Ew : ls3_wk (bzs (gestures_end_b_c.key_text k)) = 5 * Z.of_nat (length (gestures_end_b_c.key_text k)) + 1)
    by (unfold ls3_wk; rewrite SlotReads.bzs_length; reflexivity).
  unfold W_H in *. lia.
Qed.
Lemma ls3_held_wk : forall l, dr3_tsz (hl_recs l) + W_H * hl_bytes l = zsum (map ls3_wk (texts l)).
Proof.
  intros l. unfold dr3_tsz, hl_bytes, texts. induction (hl_recs l) as [|r rs IH]; [reflexivity|].
  cbn [map fold_right].
  assert (Ew : ls3_wk (bzs (snd r)) = 5 * Z.of_nat (length (snd r)) + 1)
    by (unfold ls3_wk; rewrite SlotReads.bzs_length; reflexivity).
  unfold W_H in *. lia.
Qed.
Lemma ls3_keys_parts : forall ks,
  gestures_end_b_c.keys_total ks =
    zsum (map (fun k => Z.of_nat (length (gestures_end_b_c.key_text k))) ks) + 5 * Z.of_nat (length ks) /\
  dr3_ksz ks = zsum (map (fun k => Z.of_nat (length (gestures_end_b_c.key_text k))) ks) + Z.of_nat (length ks).
Proof.
  induction ks as [|k ks IH]; [split; reflexivity|].
  unfold dr3_ksz, gestures_end_b_c.keys_total in *. cbn [map fold_right length]. lia.
Qed.
(* the pending stream is the pending bytes past the read offset, when the offset is inside the first text *)
Lemma ls3_concat_len : forall rs : list (Z * list byte),
  Z.of_nat (length (concat (map snd rs))) = zsum (map (fun r : Z * list byte => Z.of_nat (length (snd r))) rs).
Proof. induction rs as [|r rs IH]; [reflexivity|]. cbn [map concat fold_right]. rewrite length_app. lia. Qed.
Lemma ls3_ps_sp : forall h,
  ((hl_recs (hs_pending h) = [] /\ hs_off h = 0) \/
   (exists r rs, hl_recs (hs_pending h) = r :: rs /\ 0 <= hs_off h < Z.of_nat (length (snd r)))) ->
  Z.of_nat (length (pending_stream h)) = slot_pend (Some h).
Proof.
  intros h [(E & Ho) | (r & rs & E & Ho)]; unfold pending_stream; cbn [slot_pend]; unfold hl_bytes; rewrite E.
  - cbn [map fold_right length Z.of_nat]. lia.
  - cbn [map fold_right]. rewrite length_app, length_skipn, Nat2Z.inj_add, ls3_concat_len.
    pose proof (zsum_map_nonneg (fun r0 : Z * list byte => Z.of_nat (length (snd r0))) rs
                  ltac:(intros; cbv beta; lia)).
    lia.
Qed.

(* ================================================================== the held vector, the expected vector *)
(* a list's vector, its slack and its first-allocation credit: check_no_loss's held list (cnl_post bounds hl_cap H'
   from above only) costs at most 32 per begin line and 64 *)
Lemma ls3_phi_held : forall c n c' n' cb, 0 <= n <= c -> 0 <= n' <= c' -> n' <= n + cb -> 0 <= cb ->
  c' <= Z.max 8 (Z.max c (2 * (n + cb))) ->
  dr3_vec c' + AREC * Z.max 0 (2 * n' - c') + AREC * Z.max 0 (8 - c') <=
  dr3_vec c + AREC * Z.max 0 (2 * n - c) + AREC * Z.max 0 (8 - c) + 32 * cb + 64.
Proof. intros c n c' n' cb H1 H2 H3 H4 H5. unfold dr3_vec, AREC. destruct (Z.eqb_spec c' 0), (Z.eqb_spec c 0); lia. Qed.
(* the expected list, empty before the drain and after check_no_loss: at most 32 per line *)
Lemma ls3_exp_vec : forall c0 c1 nl, 0 <= c0 -> 0 <= nl <= c1 -> c1 <= Z.max 8 (Z.max c0 (2 * nl)) ->
  dr3_vec c1 + AREC * Z.max 0 (0 - c1) + AREC * Z.max 0 (8 - c1) <=
  dr3_vec c0 + AREC * Z.max 0 (0 - c0) + AREC * Z.max 0 (8 - c0) + 32 * nl.
Proof. intros c0 c1 nl H1 H2 H3. unfold dr3_vec, AREC. destruct (Z.eqb_spec c1 0), (Z.eqb_spec c0 0); lia. Qed.

(* ================================================================== drain_run: the relay's mass and its key array *)
(* gesture_seen: a new begin (a line of at least 21 bytes with its NUL) grows the key array to 8 * (|H| + 1) *)
Lemma ls3_seen : forall H ka l j ha ks KA no,
  168 * Z.of_nat (length H) <= 21 * KA + 8 * no -> 21 * ka <= 21 * KA + 8 * no ->
  168 * Z.of_nat (length (RelayKeys.seen_arr H l)) <= 21 * KA + 8 * (no + (Z.of_nat (length l) + 1)) /\
  21 * snd (fst (drain_b_c.seen_tr H ka l j ha ks)) <= 21 * KA + 8 * (no + (Z.of_nat (length l) + 1)).
Proof.
  intros H ka l j ha ks KA no HH Hk.
  unfold RelayKeys.seen_arr, drain_b_c.seen_tr.
  destruct (RelayModel.gesture l) as [[kd x]|] eqn:G; [|cbn [fst snd]; lia].
  destruct kd; destruct (RelayKeys.index_of x H) as [n|] eqn:I; cbn [fst snd].
  - lia.
  - pose proof (SlotReads.gesture_begin_len l x G). rewrite length_app. cbn [length]. lia.
  - unfold RelayKeys.swap_remove. rewrite length_firstn. lia.
  - lia.
Qed.
Lemma ls3_lines_run : forall ls live mx no cap H ka j o ha ks KA,
  168 * Z.of_nat (length H) <= 21 * KA + 8 * no -> 21 * ka <= 21 * KA + 8 * no ->
  168 * Z.of_nat (length (snd (fst (snd (fst (drain_b_c.lines_run live mx no cap H ka ls j o ha ks)))))) <=
    21 * KA + 8 * (no + Z.of_nat (length (with_nul ls))) /\
  21 * snd (snd (fst (drain_b_c.lines_run live mx no cap H ka ls j o ha ks))) <=
    21 * KA + 8 * (no + Z.of_nat (length (with_nul ls))).
Proof.
  induction ls as [|l r IH]; intros live mx no cap H ka j o ha ks KA HH Hk; cbn [drain_b_c.lines_run].
  - cbn [fst snd]. rewrite RelayCap.with_nul_nil_len. lia.
  - rewrite RelayCap.with_nul_cons_len.
    match goal with |- context [drain_b_c.lines_run live mx ?a1 ?a2 (RelayKeys.seen_arr H l)
                                  (snd (fst (drain_b_c.seen_tr H ka l ?jj ?hh ?kk))) r ?a5 ?a6 ?a7 ?a8] =>
      pose proof (ls3_seen H ka l jj hh kk KA no HH Hk) as [S1 S2];
      destruct (IH live mx a1 a2 (RelayKeys.seen_arr H l) (snd (fst (drain_b_c.seen_tr H ka l jj hh kk)))
                  a5 a6 a7 a8 KA ltac:(lia) ltac:(lia)) as [I1 I2] end.
    cbn [fst snd]. lia.
Qed.
(* the round invariant: the read offset and the bytes still pending, g_nout + the unfinished line + the bytes still
   pending (the relay's mass), and the key array and the held keys against g_nout *)
Definition ls3_dinv (KA A : Z) (s : drain_b_c.dstate) : Prop :=
  0 <= drain_b_c.ds_off s /\ 0 <= dpre_rem s /\
  drain_b_c.ds_no s + Z.of_nat (length (drain_b_c.ds_u s)) + dpre_rem s <= A /\
  21 * drain_b_c.ds_ka s <= 21 * KA + 8 * drain_b_c.ds_no s /\
  168 * Z.of_nat (length (drain_b_c.ds_H s)) <= 21 * KA + 8 * drain_b_c.ds_no s.
Lemma ls3_drain_run : forall f live mx s j a KA A, ls3_dinv KA A s ->
  ls3_dinv KA A (fst (snd (drain_b_c.drain_run f live mx s j a))).
Proof.
  induction f as [|f IH]; intros live mx s j a KA A HI; [exact HI|].
  pose proof HI as (Io & Ir & Ia & Ik & Ih).
  cbn [drain_b_c.drain_run].
  destruct (drain_b_c.ds_eintr s).
  - cbn [fst snd]. apply IH. unfold ls3_dinv, dpre_rem in HI |- *.
    cbn [drain_b_c.ds_u drain_b_c.ds_off drain_b_c.ds_no drain_b_c.ds_H drain_b_c.ds_ka drain_b_c.ds_pend]. lia.
  - destruct (drain_b_c.ds_pend s) as [|r0 rs] eqn:EP.
    + cbn [fst snd]. unfold ls3_dinv, dpre_rem in HI |- *. rewrite EP in HI.
      cbn [drain_b_c.ds_u drain_b_c.ds_off drain_b_c.ds_no drain_b_c.ds_H drain_b_c.ds_ka drain_b_c.ds_pend]. lia.
    + assert (Hrem : dpre_rem s = Z.of_nat (length r0) + Z.of_nat (length (concat rs)) - drain_b_c.ds_off s).
      { unfold dpre_rem. rewrite EP. cbn [concat]. rewrite length_app. lia. }
      match goal with |- context [Z.leb ?x 0] => destruct (Z.leb_spec x 0) as [Hn0|Hn0] end.
      * cbn [fst snd]. unfold ls3_dinv, dpre_rem.
        cbn [drain_b_c.ds_u drain_b_c.ds_off drain_b_c.ds_no drain_b_c.ds_H drain_b_c.ds_ka drain_b_c.ds_pend concat].
        rewrite length_app. lia.
      * match type of Hn0 with 0 < ?x =>
          assert (Hn1 : x <= Z.of_nat (length r0) - drain_b_c.ds_off s) by lia;
          set (n := x) in * end.
        assert (Hd : Z.of_nat (length (firstn (Z.to_nat n) (skipn (Z.to_nat (drain_b_c.ds_off s)) r0))) = n)
          by (rewrite length_firstn, length_skipn; lia).
        set (d := firstn (Z.to_nat n) (skipn (Z.to_nat (drain_b_c.ds_off s)) r0)) in *.
        destruct (RelayModel.chunk (drain_b_c.ds_u s) (drain_b_c.ds_skip s) d) as [[u' sk'] rl] eqn:EC.
        destruct (dpre_chunk _ _ _ _ _ _ EC) as (C1 & C2 & C3).
        cbv beta iota.
        match goal with |- context [drain_b_c.lines_run ?l1 ?l2 ?l3 ?l4 ?l5 ?l6 ?l7 ?l8 ?l9 ?l10 ?l11] =>
          pose proof (ls3_lines_run l7 l1 l2 l3 l4 l5 l6 l8 l9 l10 l11 KA ltac:(lia) ltac:(lia)) as [L1 L2];
          revert L1 L2;
          destruct (drain_b_c.lines_run l1 l2 l3 l4 l5 l6 l7 l8 l9 l10 l11) as [[tl [[oc' H'] ka']] [[o' ha'] ks']];
          intros L1 L2 end.
        cbn [fst snd] in L1, L2 |- *.
        destruct (Z.eqb_spec (drain_b_c.ds_off s + n) (Z.of_nat (length r0))) as [Ew|Ew].
        -- apply IH. unfold ls3_dinv, dpre_rem.
           cbn [drain_b_c.ds_u drain_b_c.ds_off drain_b_c.ds_no drain_b_c.ds_H drain_b_c.ds_ka drain_b_c.ds_pend].
           lia.
        -- apply IH. unfold ls3_dinv, dpre_rem.
           cbn [drain_b_c.ds_u drain_b_c.ds_off drain_b_c.ds_no drain_b_c.ds_H drain_b_c.ds_ka drain_b_c.ds_pend concat].
           rewrite length_app. lia.
Qed.
(* a drain from g_nout = 0: the lines' bytes with their NULs and the new unfinished line are at most the old one and
   the pending bytes; the key array grows by at most 8 per 21 bytes of lines *)
Lemma ls3_rem_init : forall NO CAP e h,
  ((hl_recs (hs_pending h) = [] /\ hs_off h = 0) \/
   (exists r rs, hl_recs (hs_pending h) = r :: rs /\ 0 <= hs_off h < Z.of_nat (length (snd r)))) ->
  0 <= hs_off h /\ 0 <= dpre_rem (drain_b_c.drain_init NO CAP e h).
Proof.
  intros NO CAP e h [(E & Ho) | (r & rs & E & Ho)]; unfold dpre_rem;
    cbn [drain_b_c.drain_init drain_b_c.ds_pend drain_b_c.ds_off]; rewrite E; cbn [map concat].
  - rewrite Ho. cbn [length Z.of_nat]. lia.
  - rewrite length_app, SlotReads.bzs_length. lia.
Qed.
Lemma ls3_drain_fin : forall live mx CAP e h,
  ((hl_recs (hs_pending h) = [] /\ hs_off h = 0) \/
   (exists r rs, hl_recs (hs_pending h) = r :: rs /\ 0 <= hs_off h < Z.of_nat (length (snd r)))) ->
  168 * Z.of_nat (length (re_keys e)) <= 21 * drain_b_c.ent_ka e ->
  drain_b_c.ds_no (drain_b_c.drain_fin live mx 0 CAP e h) +
    Z.of_nat (length (drain_b_c.ds_u (drain_b_c.drain_fin live mx 0 CAP e h))) <=
    Z.of_nat (length (re_U e)) + Z.of_nat (length (pending_stream h)) /\
  21 * drain_b_c.ds_ka (drain_b_c.drain_fin live mx 0 CAP e h) <=
    21 * drain_b_c.ent_ka e + 8 * drain_b_c.ds_no (drain_b_c.drain_fin live mx 0 CAP e h).
Proof.
  intros live mx CAP e h Hoffc Hk.
  destruct (ls3_rem_init 0 CAP e h Hoffc) as (Ho & Hr0).
  assert (HI : ls3_dinv (drain_b_c.ent_ka e) (Z.of_nat (length (re_U e)) + Z.of_nat (length (pending_stream h)))
                 (drain_b_c.drain_fin live mx 0 CAP e h)).
  { unfold drain_b_c.drain_fin, drain_b_c.drain_go. apply ls3_drain_run.
    pose proof (dpre_rem_init 0 CAP e h Ho) as Hr.
    unfold ls3_dinv.
    cbn [drain_b_c.drain_init drain_b_c.ds_u drain_b_c.ds_off drain_b_c.ds_no drain_b_c.ds_H drain_b_c.ds_ka]
      in Hr, Hr0 |- *.
    rewrite SlotReads.bzs_length. unfold drain_b_c.keys_texts. rewrite length_map. lia. }
  destruct HI as (_ & Ir & Ia & Ik & _). lia.
Qed.

(* ================================================================== the proposed premises' bundles (v3's additions) *)
(* aentry_ok's held-array clause, W_rep.v:131-132 (the drain call's entry: DLK's HMOD, drain.v:5413) *)
Definition ls3_kh (e : rentry) : Prop :=
  (re_hp e = 0 /\ re_keys e = []) \/ (re_hp e <> 0 /\ 8 * re_nheld e <= re_kh e).
(* alist_at's count clause, W_rep.v:81, of the source's three lists at the drain call (asrc_at :101, :111, :112) *)
Definition ls3_hn (h : hsrc) : Prop :=
  hl_n (hs_pending h) <= hl_cap (hs_pending h) /\ hl_n (hs_expected h) <= hl_cap (hs_expected h) /\
  hl_n (hs_held h) <= hl_cap (hs_held h).
(* dr_post's clauses (W_contract.v at 129f255c729): :954 the unfinished line, :956 the key array, :966 the read offset,
   :970 the expected texts, :972 the held list, and :961 asrc_at h' (alist_at :81 of its expected list) *)
Definition ls3_dpost (m : lmod) (j : nat) (h : hsrc) (e' : rentry) (h1 : hsrc) : Prop :=
  let fin := dr_fin (lm_c m) (lm_mx m) (Z.of_nat (length (lm_O m))) (lm_cap m) (nth j (lm_es m) dr_e0) h in
  bzs (re_U e') = drain_b_c.ds_u fin /\ drain_b_c.ent_ka e' = drain_b_c.ds_ka fin /\
  hs_off h1 = 0 /\
  map snd (hl_recs (hs_expected h1)) = map snd (hl_recs (hs_expected h)) ++ map (map (Z_to_bv 8)) (dr_lines h) /\
  hs_held h1 = hs_held h /\ hl_n (hs_expected h1) <= hl_cap (hs_expected h1).
(* cnl_post's clauses (the drain arm's stub _drain.v:223-241 at 129f255c729, its dr_cfun) and its asrc_at
   (set_exp_held h1 E' H') (alist_at W_rep.v:81 of the held list) *)
Definition ls3_cpost (h1 : hsrc) (E' H' : hlist) : Prop :=
  hl_recs E' = [] /\ hl_cap E' = hl_cap (hs_expected h1) /\
  NoDup (texts H') /\ texts H' = RelayModel.upds (texts (hs_held h1)) (texts (hs_expected h1)) /\
  hl_cap H' <= Z.max 8 (Z.max (hl_cap (hs_held h1))
                             (2 * (hl_n (hs_held h1) + Z.of_nat (count_begin (texts (hs_expected h1)))))) /\
  hl_n H' <= hl_cap H'.

Section arms3.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : asyms.

(* ================================================================== LS_drain_step at v3 *)
(* 129f255c729 _drain.v:765 LS_drain_step, AT THE PROPOSED TEXT of ReplyLSDrain3.v fr_LS_drain_step_p with LS v3 and
   without Hpay: the published premises; dr_post's blocks' change and pending list; check_no_loss's blocks' change; then
   the premises dc_calls holds (the header): dr_at_op, RINV, the drained pair's fd and eof, the entry's and the source's
   model clauses at the drain call, 0 <= g_capout, the cap' dr_post names, and dr_post's / cnl_post's clauses. *)
Lemma fr_LS3_drain_step_p : forall cx t m ly S (S1 : astate) (ly' : alayout) (S' : astate)
    si h j h'' e' c' O' cap' out' (E H : hlist) (ly1 : alayout) (h1 : hsrc) (E' H' : hlist),
  fr_LS3 B cx t m ly S -> dr_pick cx m si h -> (j < length (lm_es m))%nat ->
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
  (* v3: dr_at_op (Hatop), RINV (HRI), the pair's fd and eof (Hfdj, Hef0): drain.v:5413-5414 *)
  dr_at_op cx m -> fr_RINV cx t m -> re_fd (nth j (lm_es m) dr_e0) = hs_fd h ->
  re_eof (nth j (lm_es m) dr_e0) = 0 ->
  (* v3: the entry's and the source's model clauses at the drain call (aentry_ok W_rep.v:124-139, asrc_at :91,
     :101-105, :111-112 with alist_at :81, aout_at :187-188) *)
  dr3_epre (nth j (lm_es m) dr_e0) -> ls3_kh (nth j (lm_es m) dr_e0) -> dr3_hpre h -> ls3_hn h -> 0 <= lm_cap m ->
  (* v3: dr_post :943 *)
  cap' = (if dr_live (lm_c m) h
          then drain_b_c.ds_ocap (dr_fin (lm_c m) (lm_mx m) (Z.of_nat (length (lm_O m))) (lm_cap m)
                                   (nth j (lm_es m) dr_e0) h)
          else lm_cap m) ->
  (* v3: dr_post :952 (aentry_ok e'), :957-959; :966, :967, :964; :954, :956, :966, :970, :972, :961; cnl_post *)
  dr3_epost (nth j (lm_es m) dr_e0) e' h -> dr3_hpost h h1 -> ls3_dpost m j h e' h1 -> ls3_cpost h1 E' H' ->
  fr_LS3 B cx (t + 1) (dr_step m (dr_k' cx m) si h'' j e' c' O' cap' out') ly' S'.
Proof.
  intros cx t m ly S S1 ly' S' si h j h'' e' c' O' cap' out' E H ly1 h1 E' H' HLS Hpick Hj _ _
    (rest_d & HPd1 & HPd2) Hpend HEq HHq Hcnl Hh'' Hat HRI Hfd Heof Hepre Hkh Hhpre Hhn Hcap0 Hcap'
    Hepost Hhpost Hdpost Hcpost.
  subst E H h''.
  pose proof Hpick as (_ & Hsi & Hh).
  destruct Hat as (Hk & HO & _).
  destruct (dr3_rinv cx t m si h j HRI Hpick Hj Hfd Heof)
    as ((Hsk & HskU) & Hsk01 & _ & _ & Hexp & _ & _ & _ & Hoff & _).
  destruct Hdpost as (HU' & Hka' & Hoff1 & Hmap & Hheld & HnE1).
  replace (Z.of_nat (length (lm_O m))) with 0 in Hcap', HU', Hka' by (rewrite HO; reflexivity).
  unfold dr_fin in HU', Hka'.
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
  { rewrite Ha1 in HPd2. clear - HPd2. ls3_perm. }
  specialize (HP3 HP2'). clear HP2' Hcnl.
  (* the model's blocks: the drained entry and slot against the rest *)
  pose proof (dr3_dset_perm aentry_blks j e' e (lm_es m) Hej) as PA.
  pose proof (dr3_dset_perm slot_blks si (Some h'') (Some h) (lm_hs m) Hhi) as PS.
  change (slot_blks (Some h'')) with (asrc_blks h'') in PS. change (slot_blks (Some h)) with (asrc_blks h) in PS.
  assert (Bm : bsum (model_blks m') + bsum (aentry_blks e) + bsum (asrc_blks h) + bsum (aout_blks (lm_cap m) (lm_out m)) =
               bsum (model_blks m) + bsum (aentry_blks e') + bsum (asrc_blks h'') + bsum (aout_blks cap' out')).
  { pose proof (bsum_perm _ _ PA) as BA. pose proof (bsum_perm _ _ PS) as BS. rewrite !bsum_app in BA, BS.
    unfold model_blks, m'. cbn [dr_step lm_G lm_es lm_hs lm_cap lm_out]. rewrite !bsum_cons, !bsum_app. lia. }
  rewrite Ha'' in PS.
  assert (Hlen' : length (lm_hs m') = 4%nat) by (unfold m'; cbn [dr_step lm_hs]; rewrite dr3_dset_len; exact Hl).
  assert (Hk' : kk cx m + 1 <= kk cx m').
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
  { unfold model_blks in HP |- *. unfold m'. cbn [dr_step lm_G lm_es lm_hs lm_cap lm_out].
    change (list_blks E') with (alist_blks E') in HP3. change (list_blks H') with (alist_blks H') in HP3.
    clear - HP HPd1 HP3 PA PS. ls3_perm. }
  { lia. }
  (* ---------------------------------------------------------------- the potential *)
  clear PA PS HP3 HPd1 HPd2 HP.
  destruct Hepre as (Hce & HU & HUz & Hkh8 & H14).
  destruct Hepost as (Hce' & Hkh' & Hnd' & Hss').
  destruct Hhpost as (Hpd1 & Hpc1 & Hec1).
  destruct Hcpost as (HrE' & HcE' & HndH' & HtH' & HcH' & HnH').
  destruct Hhn as (Hnp0 & HnE0 & HnH0).
  set (Ls := dr_lines h) in *.
  set (TOT := Z.of_nat (length (with_nul Ls))).
  set (P := Z.of_nat (length (pending_stream h))).
  set (U := Z.of_nat (length (re_U e))).
  set (U' := Z.of_nat (length (re_U e'))).
  set (NL := Z.of_nat (length Ls)).
  set (CB := Z.of_nat (count_begin Ls)).
  set (SNK := zsum (map ls3_wk (dr3_nk Ls))).
  pose proof (dr3_lines h) as (HLn & _ & HZr & HCB). fold Ls in HLn, HZr, HCB.
  assert (HNL : NL <= P) by (unfold NL, P; lia).
  assert (HCB' : 21 * CB <= TOT) by (unfold CB, TOT; lia).
  assert (HSNK : SNK <= 5 * TOT) by exact (ls3_nk_wk Ls).
  assert (HTOT0 : 0 <= TOT) by (unfold TOT; lia).
  assert (HP0 : 0 <= P) by (unfold P; lia).
  (* the relay's run: its mass and its key array *)
  assert (HJ : J1 (bzs (re_U e)) (re_skip e =? 1) (hs_state h)) by exact (dr3_J1 e h Hsk HskU Hsk01 HU HUz).
  assert (Hce0 : re_cap e = 0 \/ 8192 <= re_cap e) by lia.
  pose proof (relay_remove_b_aux.rma_fin_no (dr_live (lm_c m) h) (lm_mx m) 0 (lm_cap m) e h HJ
                (dr3_pok 0 (lm_cap m) e h Hoff Hhpre) Hce0) as Hno.
  change (lines (hs_state h) (bzs (pending_stream h))) with Ls in Hno. fold TOT in Hno.
  assert (Hkh168 : 168 * Z.of_nat (length (re_keys e)) <= 21 * drain_b_c.ent_ka e).
  { unfold drain_b_c.ent_ka. destruct Hkh as [(E1 & E2) | (E1 & E2)].
    - rewrite E1, E2. cbn [length Z.of_nat Z.eqb]. lia.
    - rewrite (proj2 (Z.eqb_neq _ _) E1). unfold re_nheld in E2. lia. }
  destruct (ls3_drain_fin (dr_live (lm_c m) h) (lm_mx m) (lm_cap m) e h (proj1 Hhpre) Hkh168) as (RM & RK).
  rewrite <- HU' in RM. rewrite <- Hka' in RK. rewrite SlotReads.bzs_length in RM. fold U' in RM.
  assert (HMASS : TOT + U' <= U + P) by (unfold U, P in *; lia).
  assert (HKA : 21 * (drain_b_c.ent_ka e' - drain_b_c.ent_ka e) <= 8 * TOT) by lia.
  clear RM RK Hno.
  (* the expected texts after the drain are the lines *)
  assert (HT : texts (hs_expected h1) = Ls).
  { unfold texts. rewrite <- (map_map snd bzs). rewrite Hmap, Hexp. cbn [map app]. exact (fr_bzs_lines _ HZr). }
  assert (HnE : hl_n (hs_expected h1) = NL).
  { unfold hl_n, NL. rewrite <- (length_map snd (hl_recs (hs_expected h1))), Hmap, Hexp. cbn [map app].
    rewrite length_map. reflexivity. }
  rewrite HT in HtH', HcH'. fold CB in HcH'.
  (* ---- the entry: its buffer and credit, its key array, its keys, its unfinished line ---- *)
  assert (CE : bsum (aentry_blks e') + W_H * entry_held e' + ent_cred e' <=
               bsum (aentry_blks e) + W_H * entry_held e + ent_cred e +
               (drain_b_c.ent_ka e' - drain_b_c.ent_ka e) + SNK + W_U * (U' - U)).
  { rewrite !dr3_bsum_aentry.
    assert (G1 : E_ENT <= dr3_ce e + Z.max 0 (E_ENT - re_cap e)) by (unfold dr3_ce; apply ent_buf_ge).
    assert (G2 : dr3_ce e' + Z.max 0 (E_ENT - re_cap e') <= E_ENT)
      by (unfold dr3_ce; apply ent_buf_le; unfold E_ENT; lia).
    assert (EK : dr3_ke e = drain_b_c.ent_ka e) by reflexivity.
    assert (EK' : dr3_ke e' = drain_b_c.ent_ka e') by reflexivity.
    pose proof (ls3_keys_wk (re_keys e)) as W1. pose proof (ls3_keys_wk (re_keys e')) as W2.
    assert (KI : zsum (map ls3_wk (drain_b_c.keys_texts (re_keys e'))) <=
                 zsum (map ls3_wk (drain_b_c.keys_texts (re_keys e))) + SNK).
    { pose proof Hnd' as Hnd2. apply NoDup_ListNoDup in Hnd2.
      pose proof (ls3_sum_incl (drain_b_c.keys_texts (re_keys e'))
                    (drain_b_c.keys_texts (re_keys e) ++ dr3_nk Ls) Hnd2) as X.
      rewrite map_app, zsum_app in X. fold SNK in X. apply X. intros y Hy. apply in_or_app.
      destruct (dr3_upds_in Ls _ y (proj1 (Hss' y) Hy)) as [Hy'|Hy']; [left | right]; exact Hy'. }
    unfold entry_held, ent_cred. fold U U'. unfold W_H, W_U in *. lia. }
  (* ---- the source: pending list freed, expected list emptied, held list grown by check_no_loss ---- *)
  assert (CS : bsum (asrc_blks h'') + W_P * slot_pend (Some h'') + W_H * slot_held (Some h'') +
               slot_vsl (Some h'') + slot_cred (Some h'') <=
               bsum (asrc_blks h) + W_P * slot_pend (Some h) + W_H * slot_held (Some h) + slot_vsl (Some h) +
               slot_cred (Some h) + SNK + 32 * CB + 64 + 32 * NL - W_P * P).
  { rewrite !dr3_bsum_asrc, !dr3_bsum_alist.
    unfold h''. cbn [slot_pend slot_held slot_vsl slot_cred set_exp_held hs_pending hs_off hs_expected hs_held].
    unfold vsl, lst_cred.
    pose proof (ls3_ps_sp h (proj1 Hhpre)) as EP. cbn [slot_pend] in EP. fold P in EP.
    (* pending: its texts and credit released, its vector kept *)
    assert (Ep1 : hl_bytes (hs_pending h1) = 0) by (unfold hl_bytes; rewrite Hpend; reflexivity).
    assert (Ep2 : hl_n (hs_pending h1) = 0) by (unfold hl_n; rewrite Hpend; reflexivity).
    assert (Ep3 : dr3_tsz (hl_recs (hs_pending h1)) = 0) by (rewrite Hpend; reflexivity).
    rewrite Ep1, Ep2, Ep3, Hpc1, Hoff1.
    assert (Hcp : 0 <= hl_cap (hs_pending h)) by (unfold hl_n in Hnp0; lia).
    pose proof (dr3_tsz_nonneg (hl_recs (hs_pending h))) as Tp.
    (* expected: empty before (fr_pair_ok) and after (cnl_post) *)
    assert (Ee1 : hl_n E' = 0) by (unfold hl_n; rewrite HrE'; reflexivity).
    assert (Ee2 : dr3_tsz (hl_recs E') = 0) by (rewrite HrE'; reflexivity).
    assert (Ee3 : hl_n (hs_expected h) = 0) by (unfold hl_n; rewrite Hexp; reflexivity).
    assert (Ee4 : dr3_tsz (hl_recs (hs_expected h)) = 0) by (rewrite Hexp; reflexivity).
    rewrite Ee1, Ee2, Ee3, Ee4, HcE'.
    assert (HcE0 : 0 <= hl_cap (hs_expected h)) by lia.
    pose proof (ls3_exp_vec (hl_cap (hs_expected h)) (hl_cap (hs_expected h1)) NL HcE0
                  ltac:(rewrite HnE in HnE1; unfold NL in *; lia) ltac:(rewrite HnE in Hec1; exact Hec1)) as XE.
    (* held: the keys check_no_loss adds, and its vector *)
    rewrite Hheld in HtH', HcH'.
    assert (HnHt : hl_n (hs_held h) = Z.of_nat (length (texts (hs_held h))))
      by (unfold hl_n, texts; rewrite length_map; reflexivity).
    assert (HnHt' : hl_n H' = Z.of_nat (length (texts H'))) by (unfold hl_n, texts; rewrite length_map; reflexivity).
    pose proof (ls3_upds_len Ls (texts (hs_held h))) as UL. rewrite <- HtH' in UL. fold CB in UL.
    assert (Hn0 : 0 <= hl_n (hs_held h)) by (unfold hl_n; lia).
    assert (Hn0' : 0 <= hl_n H') by (unfold hl_n; lia).
    pose proof (ls3_phi_held (hl_cap (hs_held h)) (hl_n (hs_held h)) (hl_cap H') (hl_n H') CB
                  ltac:(lia) ltac:(lia) ltac:(lia) ltac:(unfold CB; lia) HcH') as XH.
    pose proof (ls3_held_wk (hs_held h)) as WH. pose proof (ls3_held_wk H') as WH'.
    assert (KH : zsum (map ls3_wk (texts H')) <= zsum (map ls3_wk (texts (hs_held h))) + SNK).
    { pose proof HndH' as Hnd2. apply NoDup_ListNoDup in Hnd2.
      pose proof (ls3_sum_incl (texts H') (texts (hs_held h) ++ dr3_nk Ls) Hnd2) as X.
      rewrite map_app, zsum_app in X. fold SNK in X. apply X. intros y Hy. apply in_or_app. rewrite HtH' in Hy.
      destruct (dr3_upds_in Ls _ y Hy) as [Hy'|Hy']; [left | right]; exact Hy'. }
    unfold W_P, W_H, AREC in *. lia. }
  (* ---- the output buffer: the lines, at most twice their bytes ---- *)
  assert (CO : bsum (aout_blks cap' out') <= bsum (aout_blks (lm_cap m) (lm_out m)) + 2 * TOT).
  { rewrite !dr3_bsum_aout.
    pose proof (dr3_ocap (lm_c m) (lm_mx m) (lm_cap m) e h HJ (dr3_pok 0 (lm_cap m) e h Hoff Hhpre) Hce0) as Ho.
    fold Ls TOT in Ho.
    unfold dr3_bo. rewrite Hcap'. destruct (dr_live (lm_c m) h); cbv beta iota.
    - destruct (Z.eqb_spec (drain_b_c.ds_ocap (dr_fin (lm_c m) (lm_mx m) 0 (lm_cap m) e h)) 0),
        (Z.eqb_spec (lm_cap m) 0); lia.
    - lia. }
  (* ---- the potential's step ---- *)
  assert (Zp : zsum (map slot_pend (lm_hs m')) + slot_pend (Some h) = zsum (map slot_pend (lm_hs m)) + slot_pend (Some h''))
    by exact (dr3_dset_zsum slot_pend si (Some h'') (Some h) (lm_hs m) Hhi).
  assert (Zh : zsum (map slot_held (lm_hs m')) + slot_held (Some h) = zsum (map slot_held (lm_hs m)) + slot_held (Some h''))
    by exact (dr3_dset_zsum slot_held si (Some h'') (Some h) (lm_hs m) Hhi).
  assert (Zv : zsum (map slot_vsl (lm_hs m')) + slot_vsl (Some h) = zsum (map slot_vsl (lm_hs m)) + slot_vsl (Some h''))
    by exact (dr3_dset_zsum slot_vsl si (Some h'') (Some h) (lm_hs m) Hhi).
  assert (Zc : zsum (map slot_cred (lm_hs m')) + slot_cred (Some h) = zsum (map slot_cred (lm_hs m)) + slot_cred (Some h''))
    by exact (dr3_dset_zsum slot_cred si (Some h'') (Some h) (lm_hs m) Hhi).
  assert (Ze : zsum (map entry_held (lm_es m')) + entry_held e = zsum (map entry_held (lm_es m)) + entry_held e')
    by exact (dr3_dset_zsum entry_held j e' e (lm_es m) Hej).
  assert (Zr : zsum (map ent_cred (lm_es m')) + ent_cred e = zsum (map ent_cred (lm_es m)) + ent_cred e')
    by exact (dr3_dset_zsum ent_cred j e' e (lm_es m) Hej).
  unfold PHI3, PHI, ECRED, pend_bytes, held_bytes, vslack in HM |- *. rewrite Hno'.
  clear - HM Bm Zp Zh Zv Zc Ze Zr CE CS CO HMASS HKA HSNK HCB' HNL HTOT0 HP0 Hk'.
  unfold W_OPEN, E_ENT, K0, APARTIAL, MB_K, W_P, W_H, W_U in *. lia.
Qed.

(* ================================================================== LS_rm_step at v3 *)
(* g_capout after relay_remove (drain's lines, then the gesture ends of the entry's keys): ReplyLSRemove3.v's
   fr_LS_rm_cnl_pre_p, its Hcap2 in both cases, as a lemma *)
Lemma ls3_rm_cap2 : forall cx t m si h j0 e1 h1 ev LB c2 O2 cap2,
  fr_RINV cx t m -> rm_at cx m si h j0 -> rm_rr_ok m h j0 e1 h1 ev LB c2 O2 cap2 ->
  cap2 <= Z.max (lm_cap m)
            (2 * (3 * ((if re_skip (rm_ent m j0) =? 0 then Z.of_nat (length (re_U (rm_ent m j0))) else 0) +
                       Z.of_nat (length (pending_stream h))) +
                  gestures_end_b_c.keys_total (re_keys (rm_ent m j0)))).
Proof.
  intros cx t m si h j0 e1 h1 ev LB c2 O2 cap2 HRI Hat Hrr.
  pose proof Hat as (_ & HO & _ & _ & Hsi & Hh & Hj0 & _).
  destruct (rm3_pair cx t m si h j0 HRI Hat) as (HP & HE & HC & Hcn).
  destruct HP as (_ & _ & _ & HP4 & HP5 & HP6 & HP7 & HP8 & HP9 & _ & HP11).
  cbn [fst snd] in HP4, HP5, HP6, HP7, HP8, HP9, HP11.
  destruct HE as (_ & _ & _ & HEnd & HEsk).
  unfold rm_rr_ok in Hrr. cbv zeta in Hrr. rewrite HO in Hrr. change (Z.of_nat (length (@nil byte))) with 0 in Hrr.
  set (e := rm_ent m j0) in *.
  set (U := Z.of_nat (length (re_U e))) in *.
  set (PS := Z.of_nat (length (pending_stream h))) in *.
  set (KT := gestures_end_b_c.keys_total (re_keys e)) in *.
  assert (HU0 : 0 <= U) by (unfold U; lia).
  assert (HPS0 : 0 <= PS) by (unfold PS; lia).
  assert (HKT0 : 0 <= KT) by (apply fr_keys_total_nonneg).
  set (X := if re_skip e =? 0 then U else 0) in *.
  assert (EX : X = if re_skip e =? 0 then U else 0) by reflexivity.
  clearbody X.
  assert (HX0 : 0 <= X) by (rewrite EX; destruct (re_skip e =? 0); cbv iota; lia).
  assert (HXs : re_skip e = 0 -> X = U) by (intros E; rewrite EX, E; reflexivity).
  assert (HXs1 : re_skip e = 1 -> X = 0) by (intros E; rewrite EX, E; reflexivity).
  clear EX.
  remember (X + PS) as P eqn:EP.
  assert (HNF : forall live mx CAP, drain_b_c.ds_no (drain_b_c.drain_fin live mx 0 CAP e h) <= P).
  { intros live mx CAP. pose proof (rm3_no_fin live mx CAP e h HP11) as NF. rewrite EP.
    destruct HEsk as [E|E]; rewrite E in NF.
    - change (0 =? 1) with false in NF. cbv iota in NF. fold U PS in NF. rewrite (HXs E). lia.
    - change (1 =? 1) with true in NF. cbv iota in NF. fold PS in NF. rewrite (HXs1 E). lia. }
  revert Hrr. destruct (re_eof e =? 0) eqn:Eo; intros Hrr; cbn [andb] in Hrr.
  - apply Z.eqb_eq in Eo.
    destruct Hrr as [HD HS].
    destruct HD as (_ & _ & _ & _ & _ & _ & _ & _ & D9 & D10 & _ & D12 & _ & _ & _ & D16 & _ & _ & D19 & _ & _ &
                    D22 & _ & D24 & _ & _ & D27).
    set (DT := Z.of_nat (length (with_nul (dr_lines h)))) in *.
    assert (HDT0 : 0 <= DT) by (unfold DT; lia).
    assert (Hdt : DT <= P).
    { destruct (HP4 Eo) as (Hov & HU).
      pose proof (SlotReads.lines_bytes (bzs (pending_stream h)) (hs_state h)) as LB0.
      assert (W0 : 0 <= SlotReads.wcost (feed (hs_state h) (bzs (pending_stream h))))
        by (unfold SlotReads.wcost; destruct (ls_k (feed (hs_state h) (bzs (pending_stream h)))); cbv iota; lia).
      change (SlotReads.wcost (hs_state h)) with
        (if hs_overlong h =? 1 then 0 else Z.of_nat (length (bzs (hs_W h)))) in LB0.
      change (lines (hs_state h) (bzs (pending_stream h))) with (dr_lines h) in LB0. fold DT in LB0.
      rewrite !RelayCap.rc_length_bzs in LB0. fold PS in LB0.
      rewrite EP. destruct HEsk as [E|E].
      - assert (LU : length (hs_W h) = length (re_U e)).
        { specialize (HU E). rewrite <- (RelayCap.rc_length_bzs (hs_W h)), <- HU, RelayCap.rc_length_bzs.
          reflexivity. }
        rewrite E in Hov. rewrite <- Hov in LB0. rewrite LU in LB0. fold U in LB0.
        change (0 =? 1) with false in LB0. cbv iota in LB0. rewrite (HXs E). lia.
      - rewrite E in Hov. rewrite <- Hov in LB0.
        change (1 =? 1) with true in LB0. cbv iota in LB0. rewrite (HXs1 E). lia. }
    assert (Hkt1 : gestures_end_b_c.keys_total (re_keys e1) <= KT + 2 * DT).
    { unfold KT, DT. rewrite !rm3_kt_kw.
      eapply Z.le_trans; [apply (rm3_kw_incl _ (upds (drain_b_c.keys_texts (re_keys e)) (dr_lines h)))|].
      - first [exact (proj1 (NoDup_ListNoDup _) D9) | exact D9].
      - intros y Hy. exact (proj1 (D10 y) Hy).
      - apply rm3_upds_kw. }
    set (cap1 := if dr_live (lm_c m) h then drain_b_c.ds_ocap (dr_fin (lm_c m) (lm_mx m) 0 (lm_cap m) e h)
                 else lm_cap m) in HS.
    set (O1 := if dr_live (lm_c m) h then [] ++ LB else []) in HS.
    assert (Hc1 : cap1 <= Z.max (lm_cap m) (2 * P)).
    { unfold cap1. destruct (dr_live (lm_c m) h); cbv iota; [|lia].
      unfold dr_fin. pose proof (RelayCap.drain_ocap_le (dr_live (lm_c m) h) (lm_mx m) 0 (lm_cap m) e h) as [_ OC].
      pose proof (HNF (dr_live (lm_c m) h) (lm_mx m) (lm_cap m)) as NF. lia. }
    assert (HO1 : Z.of_nat (length O1) <= DT).
    { unfold O1. destruct (dr_live (lm_c m) h); cbv iota; cbn [app length]; [|lia].
      rewrite <- RelayCap.rc_length_bzs, D27. unfold DT. lia. }
    clearbody cap1 O1.
    pose proof (f_equal snd HS) as HS2. cbn [snd] in HS2. rewrite <- HS2.
    eapply Z.le_trans; [apply rm3_sends_cap|]. rewrite rm3_tot_ge. lia.
  - destruct Hrr as [[He1 Hh1] HS]. subst e1 h1.
    pose proof (f_equal snd HS) as HS2. cbn [snd] in HS2. rewrite <- HS2.
    eapply Z.le_trans; [apply rm3_sends_cap|]. rewrite rm3_tot_ge. fold KT. cbn [length]. lia.
Qed.

(* 30d91cacb63 _remove.v:5460 LS_rm_step, AT THE PROPOSED TEXT of ReplyLSRemove3.v fr_LS_rm_step_p with LS v3 and
   without Hout: the published premises and (P2'), then three facts the arm holds at rm_rr's state (_remove.v:2398)
   and carries with the LS in rm_Q as it carries (P1) for LS_rm_cnl_pre:
   (P1) the model's blocks have nonnegative sizes (rr_blks_pos :2155, amodel_at);
   (P3) the removed entry's keys are at least 14 bytes (HREL :2411, arelay_at's aentry_ok, W_rep.v:139);
   (P4) the source's read offset is inside its first pending text (HSRC :2418, asrc_at, W_rep.v:104-105). *)
Lemma fr_LS3_rm_step_p : forall cx t m ly0 S0 (ly : alayout) (S : astate)
    si h j0 e1 h1 ev LB c2 O2 cap2 out2 E' H' H'' ds cc ev5,
  fr_LS3 B cx t m ly0 S0 ->
  mo_le MT S0 S (W_LLVMFuzzerTestOneInput_remove.rm_rr_cost MT m h +
                 W_LLVMFuzzerTestOneInput_remove.rm_cnl_cost MT (hs_expected h1) (hs_held h1) +
                 W_LLVMFuzzerTestOneInput_remove.rm_cshe_cost MT H' +
                 sr_cost MT (Some (set_held (set_exp_held h1 E' H') H''))) ->
  fr_RINV cx t m -> rm_at cx m si h j0 ->
  rm_rr_ok m h j0 e1 h1 ev LB c2 O2 cap2 -> rm_cnl_ok h1 E' H' ->
  rm_cshe_ok m (set_exp_held h1 E' H') O2 (rm_A1 m h1) H'' ds cc ->
  (forall rest, Permutation (ablocks B ly0 S0) (input_blks cx ++ model_blks m ++ rest) ->
     Permutation (ablocks B ly S)
       (input_blks cx ++ model_blks (rm_mk cx m si None j0 (rm_cev c2 ev5) O2 cap2 out2) ++ rest)) ->
  (forall b, In b (model_blks m) -> 0 <= snd b) ->
  Forall (fun k => 14 <= Z.of_nat (length (gestures_end_b_c.key_text k))) (re_keys (rm_ent m j0)) ->
  ((hl_recs (hs_pending h) = [] /\ hs_off h = 0) \/
   (exists r rs, hl_recs (hs_pending h) = r :: rs /\ 0 <= hs_off h < Z.of_nat (length (snd r)))) ->
  fr_LS3 B cx (t + 1) (rm_mk cx m si None j0 (rm_cev c2 ev5) O2 cap2 out2) ly S.
Proof.
  intros cx t m ly0 S0 ly S si h j0 e1 h1 ev LB c2 O2 cap2 out2 E' H' H'' ds cc ev5 HLS _ HRI Hat Hrr _ _ Hfr
    Hpos H14 Hoffc.
  pose proof (ls3_rm_cap2 cx t m si h j0 e1 h1 ev LB c2 O2 cap2 HRI Hat Hrr) as Hc2.
  pose proof Hat as (Hk & _ & _ & _ & Hsi & Hh & Hj0 & _).
  destruct HLS as (rest & e0 & HPm & HR & HEr & Hcx & Hl & Hnp & HM).
  pose proof (rm3_model_bsum cx m si None j0 (rm_cev c2 ev5) O2 cap2 out2 h Hh Hj0) as HMB.
  change (slot_blks None) with (@nil (Z * Z)) in HMB. rewrite bsum_nil in HMB.
  set (m' := rm_mk cx m si None j0 (rm_cev c2 ev5) O2 cap2 out2) in *.
  set (e := rm_ent m j0) in *.
  pose proof (nth_some_error _ _ _ Hh) as Hi.
  assert (Zs : forall g : option hsrc -> Z, zsum (map g (lm_hs m')) + g (Some h) = zsum (map g (lm_hs m)) + g None)
    by (intros g; exact (rm3_set_zsum _ g si None (Some h) (lm_hs m) Hi)).
  assert (Ze : forall g : rentry -> Z, zsum (map g (lm_es m')) + g e = zsum (map g (lm_es m))).
  { intros g. pose proof (fr_sum_perm _ g _ _ (fr_remove_perm _ (lm_es m) j0 relay_remove_b_c.no_entry Hj0)) as Pe.
    cbn [map fold_right] in Pe. change (lm_es m') with (relay_remove_b_c.remove_at j0 (lm_es m)).
    unfold e, rm_ent. lia. }
  assert (Hkk : kk cx m + 1 <= kk cx m').
  { unfold kk, m', rm_mk, rm_k'. cbn [lm_k]. destruct (lm_k m + 1 <? c_n cx); cbv iota; lia. }
  exists rest, e0.
  split; [exact (Hfr rest HPm)|].
  split; [exact HR|]. split; [exact HEr|]. split; [exact Hcx|].
  split; [unfold m', rm_mk; cbn [lm_hs]; rewrite fr_rm_set_nth_length; exact Hl|].
  pose proof (Zs slot_pend) as Z1. pose proof (Zs slot_held) as Z2. pose proof (Zs slot_vsl) as Z3.
  pose proof (Zs slot_npend) as Z4. pose proof (Zs slot_open) as Z5. pose proof (Zs slot_cred) as Z6.
  pose proof (Ze entry_held) as Z7. pose proof (Ze ent_cred) as Z8.
  assert (N1 : slot_pend None = 0) by reflexivity. assert (N2 : slot_held None = 0) by reflexivity.
  assert (N3 : slot_vsl None = 0) by reflexivity. assert (N4 : slot_npend None = 0) by reflexivity.
  assert (N5 : slot_open None = 0) by reflexivity. assert (N6 : slot_cred None = 0) by reflexivity.
  assert (P5 : slot_open (Some h) = 1) by reflexivity.
  pose proof (slot_npend_nonneg (Some h)) as Hsn.
  split; [unfold npend in *; lia|].
  (* ---------------------------------------------------------------- what the remove releases *)
  (* the out buffer's growth: the lines (with the unfinished line when kept) and the entry's gesture ends *)
  assert (Hcap0 : 0 <= lm_cap m).
  { destruct (Z.eqb_spec (lm_cap m) 0) as [E|E]; [lia|].
    assert (Hb : In (lm_out m, lm_cap m) (aout_blks (lm_cap m) (lm_out m)))
      by (unfold aout_blks; rewrite (proj2 (Z.eqb_neq _ _) E); left; reflexivity).
    exact (Hpos _ (rm3_in_model_out m _ Hb)). }
  assert (CO : bsum (aout_blks cap2 out2) - bsum (aout_blks (lm_cap m) (lm_out m)) <=
               6 * (if re_skip e =? 0 then Z.of_nat (length (re_U e)) else 0) +
               6 * Z.of_nat (length (pending_stream h)) + 2 * gestures_end_b_c.keys_total (re_keys e)).
  { pose proof (ev3_bsum_aout cap2 out2) as A1. pose proof (ev3_bsum_aout_eq (lm_cap m) (lm_out m) Hcap0) as A2.
    assert (A3 : 0 <= (if re_skip e =? 0 then Z.of_nat (length (re_U e)) else 0))
      by (destruct (re_skip e =? 0); lia).
    pose proof (fr_keys_total_nonneg (re_keys e)). lia. }
  (* the entry: its buffer and credit (>= E_ENT), its key array (>= 0), its keys and their credit, re_U's credit *)
  assert (CE : E_ENT + W_U * (if re_skip e =? 0 then Z.of_nat (length (re_U e)) else 0) +
               2 * gestures_end_b_c.keys_total (re_keys e) <=
               bsum (aentry_blks e) + W_H * entry_held e + ent_cred e).
  { rewrite dr3_bsum_aentry. unfold ent_cred.
    assert (G1 : E_ENT <= dr3_ce e + Z.max 0 (E_ENT - re_cap e)) by (unfold dr3_ce; apply ent_buf_ge).
    assert (Hke : 0 <= dr3_ke e).
    { unfold dr3_ke. destruct (Z.eqb_spec (re_hp e) 0) as [E|E]; [lia|].
      assert (Hb : In (re_hp e, re_kh e) (aentry_blks e)).
      { unfold aentry_blks. apply in_or_app. right. rewrite (proj2 (Z.eqb_neq _ _) E). apply in_or_app.
        left. left. reflexivity. }
      exact (Hpos _ (rm3_in_model_entry m j0 _ Hj0 Hb)). }
    destruct (ls3_keys_parts (re_keys e)) as (KP1 & KP2).
    pose proof (SlotReads.keys_total_count (re_keys e) H14) as KC.
    assert (A3 : 0 <= (if re_skip e =? 0 then Z.of_nat (length (re_U e)) else 0) <= Z.of_nat (length (re_U e)))
      by (destruct (re_skip e =? 0); lia).
    unfold entry_held. unfold W_U, W_H in *. lia. }
  (* the source: its partial buffer, the first vectors' credit of its two lists, its pending credit *)
  assert (CS : APARTIAL + K0 + W_P * Z.of_nat (length (pending_stream h)) <=
               bsum (asrc_blks h) + W_P * slot_pend (Some h) + W_H * slot_held (Some h) + slot_vsl (Some h) +
               slot_cred (Some h)).
  { rewrite dr3_bsum_asrc, (dr3_bsum_alist (hs_expected h)), (dr3_bsum_alist (hs_held h)).
    rewrite (ls3_ps_sp h Hoffc).
    assert (Hpd : 0 <= bsum (alist_blks (hs_pending h))).
    { apply rm3_bsum_nonneg. intros b Hb. apply Hpos. apply (rm3_in_model_slot m si h b Hh).
      unfold asrc_blks. right. apply in_or_app. left. exact Hb. }
    pose proof (lst_vec_ge (hl_cap (hs_expected h))) as V1. pose proof (lst_vec_ge (hl_cap (hs_held h))) as V2.
    pose proof (dr3_tsz_nonneg (hl_recs (hs_expected h))) as T1. pose proof (dr3_tsz_nonneg (hl_recs (hs_held h))) as T2.
    pose proof (slot_vsl_nonneg (Some h)) as V3. pose proof (slot_held_nonneg (Some h)) as V4.
    cbn [slot_cred]. unfold lst_cred. unfold dr3_vec. unfold K0, W_P, W_H, AREC in *. lia. }
  unfold PHI3, PHI, ECRED, pend_bytes, held_bytes, vslack in HM |- *. rewrite !nopen_zsum in *.
  assert (HX0 : 0 <= (if re_skip e =? 0 then Z.of_nat (length (re_U e)) else 0))
    by (destruct (re_skip e =? 0); lia).
  clear - HM HMB Z1 Z2 Z3 Z5 Z6 Z7 Z8 N1 N2 N3 N5 N6 P5 CO CE CS Hkk HX0.
  unfold W_OPEN, MB_K, W_P, W_H, W_U, E_ENT, K0, APARTIAL in *. lia.
Qed.
End arms3.

(* ================================================================== B1c's other rules at v3 *)
(* Each is the text of its v2 lemma (ReplyLSArms.v, ReplyLSDrainPre.v, ReplyLSDrain3.v, ReplyLSRemove3.v,
   ReplyLSEvent3.v) with fr_LS -> fr_LS3; the proofs read LS v3's room (fr_LS3_room / fr_LS3_room_x) and keep rules. *)
Section arms3b.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : asyms.

(* ---------------------------------------------------------------- drain *)
(* 129f255c729 _drain.v:760 LS_drain_skip (ReplyLSArms.v fr_LS_drain_skip) *)
Lemma fr_LS3_drain_skip : forall cx t m ly S,
  fr_LS3 B cx t m ly S -> fr_LS3 B cx (t + 1) (dr_skip m (dr_k' cx m)) ly S.
Proof.
  intros cx t m ly S H.
  apply (fr_LS3_k_only B cx t (t + 1) m (dr_skip m (dr_k' cx m)) ly S); try reflexivity; [|exact H].
  left. unfold dr_skip, dr_k'. cbn [lm_k]. destruct (lm_k m + 1 <? c_n cx); lia.
Qed.
(* _drain.v:730 LS_drain_pre, conjuncts 1, 2, 3, 6 at the arm's exact premises (ReplyLSDrainPre.v
   fr_LS_drain_pre_c1236; the proof reads RINV only) *)
Lemma fr_LS3_drain_pre_c1236 : forall cx t m ly S si h j,
  fr_LS3 B cx t m ly S -> fr_RINV cx t m -> dr_at_op cx m -> dr_pick cx m si h ->
  (j < length (lm_es m))%nat -> re_fd (nth j (lm_es m) dr_e0) = hs_fd h ->
  re_eof (nth j (lm_es m) dr_e0) = 0 ->
  Z.of_nat (length (pending_stream h)) < 2 ^ 26 /\
  hl_cap (hs_expected h) < 2 ^ 26 /\
  re_nheld (nth j (lm_es m) dr_e0) + Z.of_nat (length (pending_stream h)) < 2 ^ 26 /\
  mo_ok MT S (dr_cost MT (lm_c m) (lm_mx m) (Z.of_nat (length (lm_O m))) (lm_cap m) (nth j (lm_es m) dr_e0) h).
Proof.
  intros cx t m ly S si h j _ HRI _ Hpick Hj Hfdj _.
  destruct (dpre_pair cx t m si h j HRI Hpick Hj Hfdj) as (Hp & _ & Hcost).
  destruct Hp as (_ & _ & _ & _ & _ & _ & _ & Hec & _ & _ & _). cbn [fst snd] in Hec.
  unfold fr_pair_cost in Hcost. cbn [fst] in Hcost.
  pose proof (dpre_keys_le (re_keys (nth j (lm_es m) dr_e0))) as Hkl.
  assert (HU : 0 <= (if re_skip (nth j (lm_es m) dr_e0) =? 0
                     then Z.of_nat (length (re_U (nth j (lm_es m) dr_e0))) else 0))
    by (destruct (re_skip (nth j (lm_es m) dr_e0) =? 0); lia).
  pose proof (SlotInv.ecap_ok_lt _ Hec) as Hc.
  unfold re_nheld. split; [lia|]. split; [lia|]. split; [lia | exact I].
Qed.
(* conjunct 4 at ReplyLSDrainPre.v's proposed text (fr_LS_drain_pre_c4: dc_regs' Ht, aentry_ok's |re_U| bound) *)
Lemma fr_LS3_drain_pre_c4 : forall cx t m ly S si h j,
  fr_LS3 B cx t m ly S -> fr_RINV cx t m -> dr_at_op cx m -> dr_pick cx m si h ->
  (j < length (lm_es m))%nat -> re_fd (nth j (lm_es m) dr_e0) = hs_fd h ->
  re_eof (nth j (lm_es m) dr_e0) = 0 ->
  0 <= t < OPS_MAX ->
  Z.of_nat (length (re_U (nth j (lm_es m) dr_e0))) <= APARTIAL ->
  tr_max (dr_tr (lm_c m) (lm_mx m) (Z.of_nat (length (lm_O m))) (lm_cap m) (nth j (lm_es m) dr_e0) h) < MMAX.
Proof.
  intros cx t m ly S si h j _ HRI Hat Hpick Hj Hfdj Heof Ht HU.
  destruct (dpre_pair cx t m si h j HRI Hpick Hj Hfdj) as (Hp & Hent & Hcost).
  destruct Hp as (_ & _ & _ & Hre & _ & _ & Hexp & _ & _ & Hpe & Hoff). cbn [fst snd] in *.
  destruct Hent as (_ & _ & _ & _ & Hsk).
  destruct (Hre Heof) as (S1 & W1).
  destruct Hat as (_ & HO & _).
  replace (Z.of_nat (length (lm_O m))) with 0 by (rewrite HO; reflexivity).
  apply dpre_dr_tr_max.
  - exact HU.
  - destruct (Z.eq_dec (hs_overlong h) 1) as [E|E]; [left; exact E | right]. apply W1. lia.
  - exact Hoff.
  - exact Hexp.
  - unfold fr_pair_cost in Hcost. cbn [fst] in Hcost.
    pose proof (dpre_keys_le (re_keys (nth j (lm_es m) dr_e0))) as Hkl.
    destruct (re_skip (nth j (lm_es m) dr_e0) =? 0); lia.
  - unfold SlotInv.WRITE_MAX, OPS_MAX in *. lia.
Qed.
(* _drain.v:730 LS_drain_pre, all six conjuncts, conjunct 5 carried as Halloc (ReplyLSDrainPre.v fr_LS_drain_pre:
   NOT PROVABLE for any LS, tr_alloc of one drain exceeds LIVE_MAX at reachable states) *)
Lemma fr_LS3_drain_pre : forall cx t m ly S si h j,
  fr_LS3 B cx t m ly S -> fr_RINV cx t m -> dr_at_op cx m -> dr_pick cx m si h ->
  (j < length (lm_es m))%nat -> re_fd (nth j (lm_es m) dr_e0) = hs_fd h ->
  re_eof (nth j (lm_es m) dr_e0) = 0 ->
  0 <= t < OPS_MAX ->
  Z.of_nat (length (re_U (nth j (lm_es m) dr_e0))) <= APARTIAL ->
  forall Halloc : blocks_bytes S +
    tr_alloc (dr_tr (lm_c m) (lm_mx m) (Z.of_nat (length (lm_O m))) (lm_cap m) (nth j (lm_es m) dr_e0) h)
    <= LIVE_MAX,
  Z.of_nat (length (pending_stream h)) < 2 ^ 26 /\
  hl_cap (hs_expected h) < 2 ^ 26 /\
  re_nheld (nth j (lm_es m) dr_e0) + Z.of_nat (length (pending_stream h)) < 2 ^ 26 /\
  tr_max (dr_tr (lm_c m) (lm_mx m) (Z.of_nat (length (lm_O m))) (lm_cap m) (nth j (lm_es m) dr_e0) h) < MMAX /\
  blocks_bytes S +
    tr_alloc (dr_tr (lm_c m) (lm_mx m) (Z.of_nat (length (lm_O m))) (lm_cap m) (nth j (lm_es m) dr_e0) h)
    <= LIVE_MAX /\
  mo_ok MT S (dr_cost MT (lm_c m) (lm_mx m) (Z.of_nat (length (lm_O m))) (lm_cap m) (nth j (lm_es m) dr_e0) h).
Proof.
  intros cx t m ly S si h j HLS HRI Hat Hpick Hj Hfdj Heof Ht HU Halloc.
  destruct (fr_LS3_drain_pre_c1236 cx t m ly S si h j HLS HRI Hat Hpick Hj Hfdj Heof) as (C1 & C2 & C3 & C6).
  pose proof (fr_LS3_drain_pre_c4 cx t m ly S si h j HLS HRI Hat Hpick Hj Hfdj Heof Ht HU) as C4.
  exact (conj C1 (conj C2 (conj C3 (conj C4 (conj Halloc C6))))).
Qed.
(* _drain.v:743 LS_cnl_pre at ReplyLSDrain3.v's proposed text (fr_LS_cnl_pre_p), fr_LS -> fr_LS3, at a meter Variable
   (implicit; the mo_le premise is not read) and without the row's mo_ok conjunct (ReplyLSI.v's, from its fr_SEC) *)
Lemma fr_LS3_cnl_pre_p {MT : ameter_ops} : forall cx t m ly S (ly' : alayout) (S' : astate) si h j h'' e' cap' out',
  fr_LS3 B cx t m ly S -> fr_RINV cx t m -> dr_pick cx m si h ->
  (j < length (lm_es m))%nat -> re_fd (nth j (lm_es m) dr_e0) = hs_fd h ->
  re_eof (nth j (lm_es m) dr_e0) = 0 ->
  mo_le MT S S' (dr_cost MT (lm_c m) (lm_mx m) (Z.of_nat (length (lm_O m))) (lm_cap m)
                   (nth j (lm_es m) dr_e0) h) ->
  hl_cap (hs_expected h'') = drain_b_c.ds_ecap
    (dr_fin (lm_c m) (lm_mx m) (Z.of_nat (length (lm_O m))) (lm_cap m) (nth j (lm_es m) dr_e0) h) ->
  map snd (hl_recs (hs_expected h'')) =
    map snd (hl_recs (hs_expected h)) ++ map (map (Z_to_bv 8)) (dr_lines h) ->
  hs_held h'' = hs_held h ->
  0 <= t < OPS_MAX -> lm_O m = [] ->
  dr3_epre (nth j (lm_es m) dr_e0) -> dr3_hpre h -> 0 <= lm_cap m ->
  (exists rest,
     Permutation (ablocks B ly S)
       (aentry_blks (nth j (lm_es m) dr_e0) ++ asrc_blks h ++ aout_blks (lm_cap m) (lm_out m) ++ rest) /\
     Permutation (ablocks B ly' S') (aentry_blks e' ++ asrc_blks h'' ++ aout_blks cap' out' ++ rest)) ->
  cap' = (if dr_live (lm_c m) h
          then drain_b_c.ds_ocap (dr_fin (lm_c m) (lm_mx m) (Z.of_nat (length (lm_O m))) (lm_cap m)
                                   (nth j (lm_es m) dr_e0) h)
          else lm_cap m) ->
  dr3_epost (nth j (lm_es m) dr_e0) e' h -> dr3_hpost h h'' ->
  NoDup (texts (hs_held h'')) /\ hl_n (hs_expected h'') < 2 ^ 26 /\
  hl_n (hs_held h'') + Z.of_nat (count_begin (texts (hs_expected h''))) < 2 ^ 22 /\
  cnl_room MMAX (blocks_bytes S') (texts (hs_held h'')) (hl_cap (hs_held h'')) (hl_recs (hs_expected h'')) /\
  AREC * capb (hs_held h'') (hs_expected h'') < 2 ^ 32.
Proof.
  intros cx t m ly S ly' S' si h j h'' e' cap' out' HLS HRI Hpick Hj Hfd Heof _ _ Hmap Hheld Ht HO
    Hepre Hhpre Hcap0 (rest & HP1 & HP2) Hcap' Hepost Hhpost.
  pose proof (fr_LS3_room_x B cx t m ly S HLS) as Hroom.
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
  assert (HT : texts (hs_expected h'') = Ls).
  { unfold texts. rewrite <- (map_map snd bzs). rewrite Hmap, Hexp. cbn [map app]. exact (fr_bzs_lines _ HZr). }
  assert (HnE : hl_n (hs_expected h'') = Z.of_nat (length Ls)).
  { unfold hl_n. rewrite <- (length_map snd (hl_recs (hs_expected h''))), Hmap, Hexp. cbn [map app].
    rewrite length_map. reflexivity. }
  pose proof (dr3_held_len (re_keys e) (hs_held h) Hnd Hss) as HHL.
  pose proof (SlotReads.keys_total_count (re_keys e) H14) as HKC. fold K in HKC.
  assert (HnH : hl_n (hs_held h) = Z.of_nat (length (texts (hs_held h))))
    by (unfold hl_n, texts; rewrite length_map; reflexivity).
  assert (N3 : hl_n (hs_held h'') + Z.of_nat (count_begin (texts (hs_expected h''))) < 2 ^ 22).
  { rewrite Hheld, HT, HnH. lia. }
  assert (N2 : hl_n (hs_expected h'') < 2 ^ 26) by (rewrite HnE; lia).
  set (Mx := capb (hs_held h) (hs_expected h'')).
  assert (HMx : Mx < 2 ^ 24) by (unfold Mx, capb; pose proof N3 as N3'; rewrite Hheld in N3'; lia).
  refine (conj _ (conj N2 (conj N3 (conj _ _)))).
  - rewrite Hheld. exact Hnd.
  - rewrite Hheld.
    assert (HB1 : blocks_bytes S = bsum (aentry_blks e) + bsum (asrc_blks h) + bsum (aout_blks (lm_cap m) (lm_out m)) +
                                   bsum rest)
      by (rewrite (blocks_bytes_bsum B ly S), (bsum_perm _ _ HP1), !bsum_app; lia).
    assert (HB2 : blocks_bytes S' = bsum (aentry_blks e') + bsum (asrc_blks h'') + bsum (aout_blks cap' out') +
                                    bsum rest)
      by (rewrite (blocks_bytes_bsum B ly' S'), (bsum_perm _ _ HP2), !bsum_app; lia).
    rewrite !dr3_bsum_aentry, !dr3_bsum_asrc, !dr3_bsum_aout, !dr3_bsum_alist in HB1, HB2.
    rewrite Hheld in HB2.
    assert (Da : dr3_ce e' <= 16384 /\ 0 <= dr3_ce e) by (unfold dr3_ce; destruct (re_cap e' =? 0), (re_cap e =? 0); lia).
    assert (Db : dr3_ke e' - dr3_ke e <= 2 ^ 30).
    { unfold dr3_ke. destruct Hkh' as [(E1 & E2) | Hk]; [rewrite E1, E2; lia|].
      destruct (Z.eqb_spec (re_hp e') 0), (Z.eqb_spec (re_hp e) 0); try lia;
        specialize (Hkh ltac:(assumption)); lia. }
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
    assert (Dd : dr3_vec (hl_cap (hs_pending h'')) + dr3_tsz (hl_recs (hs_pending h'')) <=
                 dr3_vec (hl_cap (hs_pending h)) + dr3_tsz (hl_recs (hs_pending h))).
    { rewrite Hpc'', Hpd''. pose proof (dr3_tsz_nonneg (hl_recs (hs_pending h))).
      assert (E0 : dr3_tsz [] = 0) by reflexivity. rewrite E0. lia. }
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
    assert (Dg : dr3_bo cap' - dr3_bo (lm_cap m) <= 2 * TOT).
    { replace (Z.of_nat (length (lm_O m))) with 0 in Hcap' by (rewrite HO; reflexivity).
      assert (HJ : J1 (bzs (re_U e)) (re_skip e =? 1) (hs_state h)) by exact (dr3_J1 e h Hsk HskU Hsk01 HU HUz).
      pose proof (dr3_ocap (lm_c m) (lm_mx m) (lm_cap m) e h HJ (dr3_pok 0 (lm_cap m) e h Hoff Hhpre)
                    ltac:(lia)) as Ho. fold Ls TOT in Ho.
      unfold dr3_bo. rewrite Hcap'. destruct (dr_live (lm_c m) h); cbv beta iota.
      - destruct (Z.eqb_spec (drain_b_c.ds_ocap (dr_fin (lm_c m) (lm_mx m) 0 (lm_cap m) e h)) 0),
          (Z.eqb_spec (lm_cap m) 0); lia.
      - lia. }
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

(* ---------------------------------------------------------------- remove *)
(* 30d91cacb63 _remove.v:1971 LS_rm_rr_pre, its sizes and meter conjuncts (ReplyLSRemove3.v fr_LS_rm_rr_pre_sizes;
   the proof reads RINV only) *)
Lemma fr_LS3_rm_rr_pre_sizes : forall cx t m ly S si h j0,
  fr_LS3 B cx t m ly S -> fr_RINV cx t m -> rm_at cx m si h j0 ->
  (re_eof (rm_ent m j0) = 0 ->
     Z.of_nat (length (pending_stream h)) < 2 ^ 26 /\ hl_cap (hs_expected h) < 2 ^ 26 /\
     re_nheld (rm_ent m j0) + Z.of_nat (length (pending_stream h)) < 2 ^ 26) /\
  mo_ok MT S (W_LLVMFuzzerTestOneInput_remove.rm_rr_cost MT m h).
Proof.
  intros cx t m ly S si h j0 _ HRI Hat.
  destruct (rm3_pair cx t m si h j0 HRI Hat) as (HP & _ & Hc & Hn).
  destruct HP as (_ & _ & _ & _ & _ & _ & _ & Hecap & _). cbn [fst snd] in Hecap.
  pose proof (SlotInv.ecap_ok_lt _ Hecap) as He.
  pose proof (rm3_kt_len (re_keys (rm_ent m j0))) as Hk.
  unfold fr_pair_cost in Hc. cbn [fst] in Hc. unfold re_nheld.
  split; [|exact I]. intros _.
  revert Hc. destruct (re_skip (rm_ent m j0) =? 0); intros Hc; cbv iota in Hc; (split; [lia | split; lia]).
Qed.
(* its two lm_cap conjuncts from Hcap (ReplyLSRemove3.v fr_LS_rm_rr_pre_cap; neither LS v2 nor v3 bounds lm_cap) *)
Lemma fr_LS3_rm_rr_pre_cap : forall cx t m ly S,
  fr_LS3 B cx t m ly S -> lm_cap m <= 2 ^ 29 ->
  lm_cap m < MMAX /\ blocks_bytes S + 4 * lm_cap m <= LIVE_MAX.
Proof.
  intros cx t m ly S H Hcap. pose proof (fr_LS3_room B cx t m ly S H) as Hr.
  assert (HW : WR_MMAX = 1072693248) by reflexivity. unfold ROOM_SPARE in Hr. lia.
Qed.
Lemma fr_LS3_rm_rr_pre_part : forall cx t m ly S si h j0,
  fr_LS3 B cx t m ly S -> fr_RINV cx t m -> rm_at cx m si h j0 ->
  forall (Hcap : lm_cap m <= 2 ^ 29),
  (re_eof (rm_ent m j0) = 0 ->
     Z.of_nat (length (pending_stream h)) < 2 ^ 26 /\ hl_cap (hs_expected h) < 2 ^ 26 /\
     re_nheld (rm_ent m j0) + Z.of_nat (length (pending_stream h)) < 2 ^ 26) /\
  mo_ok MT S (W_LLVMFuzzerTestOneInput_remove.rm_rr_cost MT m h) /\ lm_cap m < MMAX /\
  blocks_bytes S + 4 * lm_cap m <= LIVE_MAX.
Proof.
  intros cx t m ly S si h j0 H HRI Hat Hcap.
  destruct (fr_LS3_rm_rr_pre_sizes cx t m ly S si h j0 H HRI Hat) as (A1 & A2).
  destruct (fr_LS3_rm_rr_pre_cap cx t m ly S H Hcap) as (A3 & A4).
  exact (conj A1 (conj A2 (conj A3 A4))).
Qed.
(* _remove.v:2622 LS_rm_cnl_pre at ReplyLSRemove3.v's proposed text (fr_LS_rm_cnl_pre_p), fr_LS -> fr_LS3, at a meter
   Variable (implicit; the mo_le premise is not read) and without the row's mo_ok conjunct (ReplyLSI.v's) *)
Lemma fr_LS3_rm_cnl_pre_p {MT : ameter_ops} :
  forall cx t m ly0 S0 (ly : alayout) (S : astate) si h j0 e1 h1 ev LB c2 O2 cap2 out2,
  fr_LS3 B cx t m ly0 S0 -> fr_RINV cx t m -> rm_at cx m si h j0 -> rm_rr_ok m h j0 e1 h1 ev LB c2 O2 cap2 ->
  mo_le MT S0 S (W_LLVMFuzzerTestOneInput_remove.rm_rr_cost MT m h) ->
  (forall b, In b (model_blks m) -> 0 <= snd b) ->
  (forall rest, Permutation (ablocks B ly0 S0) (input_blks cx ++ model_blks m ++ rest) ->
     Permutation (ablocks B ly S) (input_blks cx ++ model_blks (rm_mk cx m si (Some h1) j0 c2 O2 cap2 out2) ++ rest)) ->
  cnl_room MMAX (blocks_bytes S) (texts (hs_held h1)) (hl_cap (hs_held h1)) (hl_recs (hs_expected h1)).
Proof.
  intros cx t m ly0 S0 ly S si h j0 e1 h1 ev LB c2 O2 cap2 out2 HLS HRI Hat Hrr _ Hpos Hfr.
  pose proof Hat as (_ & HO & _ & _ & Hsi & Hh & Hj0 & _).
  destruct (rm3_pair cx t m si h j0 HRI Hat) as (HP & HE & HC & Hcn).
  destruct HP as (_ & _ & _ & HP4 & HP5 & HP6 & HP7 & HP8 & HP9 & _ & HP11).
  cbn [fst snd] in HP4, HP5, HP6, HP7, HP8, HP9, HP11.
  destruct HE as (_ & _ & _ & HEnd & HEsk).
  unfold fr_pair_cost in HC. cbn [fst] in HC.
  unfold rm_rr_ok in Hrr. cbv zeta in Hrr. rewrite HO in Hrr. change (Z.of_nat (length (@nil byte))) with 0 in Hrr.
  set (e := rm_ent m j0) in *.
  set (U := Z.of_nat (length (re_U e))) in *.
  set (PS := Z.of_nat (length (pending_stream h))) in *.
  set (KT := gestures_end_b_c.keys_total (re_keys e)) in *.
  assert (HU0 : 0 <= U) by (unfold U; lia).
  assert (HPS0 : 0 <= PS) by (unfold PS; lia).
  assert (HKT0 : 0 <= KT) by (apply fr_keys_total_nonneg).
  set (X := if re_skip e =? 0 then U else 0) in HC.
  assert (EX : X = if re_skip e =? 0 then U else 0) by reflexivity.
  clearbody X.
  assert (HX0 : 0 <= X) by (rewrite EX; destruct (re_skip e =? 0); cbv iota; lia).
  assert (HXs : re_skip e = 0 -> X = U) by (intros E; rewrite EX, E; reflexivity).
  assert (HXs1 : re_skip e = 1 -> X = 0) by (intros E; rewrite EX, E; reflexivity).
  clear EX.
  remember (X + PS) as P eqn:EP.
  assert (HPC : P + KT <= c_n cx) by lia.
  pose proof (SlotInv.ecap_ok_lt _ HP8) as HEC.
  assert (Hent0 : 0 <= bsum (aentry_blks e)).
  { apply rm3_bsum_nonneg. intros b Hb. apply Hpos. exact (rm3_in_model_entry m j0 b Hj0 Hb). }
  assert (Hcap0 : 0 <= lm_cap m).
  { destruct (Z.eqb_spec (lm_cap m) 0) as [E|E]; [lia|].
    assert (Hb : In (lm_out m, lm_cap m) (aout_blks (lm_cap m) (lm_out m)))
      by (unfold aout_blks; rewrite (proj2 (Z.eqb_neq _ _) E); left; reflexivity).
    exact (Hpos _ (rm3_in_model_out m _ Hb)). }
  assert (Hhc0 : 0 <= hl_cap (hs_held h)).
  { destruct (Z.eqb_spec (hl_cap (hs_held h)) 0) as [E|E]; [lia|].
    assert (Hb : In (hl_v (hs_held h), AREC * hl_cap (hs_held h)) (asrc_blks h)).
    { unfold asrc_blks. right. rewrite !in_app_iff. right. right. unfold alist_blks.
      rewrite (proj2 (Z.eqb_neq _ _) E). apply in_or_app. left. left. reflexivity. }
    pose proof (Hpos _ (rm3_in_model_slot m si h _ Hh Hb)) as Hq. cbn [snd] in Hq. unfold AREC in Hq. lia. }
  pose proof (rm3_model_bsum cx m si (Some h1) j0 c2 O2 cap2 out2 h Hh Hj0) as HMB. fold e in HMB.
  change (slot_blks (Some h1)) with (asrc_blks h1) in HMB.
  assert (Ha1 : bsum (aout_blks (lm_cap m) (lm_out m)) = lm_cap m).
  { unfold aout_blks. destruct (Z.eqb_spec (lm_cap m) 0) as [E|E]; cbv iota;
      [rewrite bsum_nil; lia | rewrite bsum_cons, bsum_nil; cbn [snd]; lia]. }
  assert (Ha2 : bsum (aout_blks cap2 out2) <= Z.max 0 cap2).
  { unfold aout_blks. destruct (Z.eqb_spec cap2 0) as [E|E]; cbv iota;
      [rewrite bsum_nil; lia | rewrite bsum_cons, bsum_nil; cbn [snd]; lia]. }
  assert (HNF : forall live mx CAP, drain_b_c.ds_no (drain_b_c.drain_fin live mx 0 CAP e h) <= P).
  { intros live mx CAP. pose proof (rm3_no_fin live mx CAP e h HP11) as NF. rewrite EP.
    destruct HEsk as [E|E]; rewrite E in NF.
    - change (0 =? 1) with false in NF. cbv iota in NF. fold U PS in NF. rewrite (HXs E). lia.
    - change (1 =? 1) with true in NF. cbv iota in NF. fold PS in NF. rewrite (HXs1 E). lia. }
  assert (HK : bsum (model_blks (rm_mk cx m si (Some h1) j0 c2 O2 cap2 out2)) <=
                 bsum (model_blks m) + 128 + 39 * (P + KT) /\
               hs_held h1 = hs_held h /\
               (forall r, In r (hl_recs (hs_expected h1)) -> Z.of_nat (length (snd r)) + 1 <= 2 ^ 26) /\
               21 * Z.of_nat (count_begin (texts (hs_expected h1))) <= P).
  { revert Hrr. destruct (re_eof e =? 0) eqn:Eo; intros Hrr; cbn [andb] in Hrr.
    - apply Z.eqb_eq in Eo.
      destruct Hrr as [HD HS].
      destruct HD as (_ & _ & _ & _ & _ & _ & _ & _ & D9 & D10 & _ & D12 & _ & _ & _ & D16 & _ & _ & D19 & _ & _ &
                      D22 & _ & D24 & _ & _ & D27).
      set (DT := Z.of_nat (length (with_nul (dr_lines h)))) in *.
      assert (HDT0 : 0 <= DT) by (unfold DT; lia).
      assert (Hdt : DT <= P).
      { destruct (HP4 Eo) as (Hov & HU).
        pose proof (SlotReads.lines_bytes (bzs (pending_stream h)) (hs_state h)) as LB0.
        assert (W0 : 0 <= SlotReads.wcost (feed (hs_state h) (bzs (pending_stream h))))
          by (unfold SlotReads.wcost; destruct (ls_k (feed (hs_state h) (bzs (pending_stream h)))); cbv iota; lia).
        change (SlotReads.wcost (hs_state h)) with
          (if hs_overlong h =? 1 then 0 else Z.of_nat (length (bzs (hs_W h)))) in LB0.
        change (lines (hs_state h) (bzs (pending_stream h))) with (dr_lines h) in LB0. fold DT in LB0.
        rewrite !RelayCap.rc_length_bzs in LB0. fold PS in LB0.
        rewrite EP. destruct HEsk as [E|E].
        - assert (LU : length (hs_W h) = length (re_U e)).
          { specialize (HU E). rewrite <- (RelayCap.rc_length_bzs (hs_W h)), <- HU, RelayCap.rc_length_bzs.
            reflexivity. }
          rewrite E in Hov. rewrite <- Hov in LB0. rewrite LU in LB0. fold U in LB0.
          change (0 =? 1) with false in LB0. cbv iota in LB0. rewrite (HXs E). lia.
        - rewrite E in Hov. rewrite <- Hov in LB0.
          change (1 =? 1) with true in LB0. cbv iota in LB0. rewrite (HXs1 E). lia. }
      assert (Hkt1 : gestures_end_b_c.keys_total (re_keys e1) <= KT + 2 * DT).
      { unfold KT, DT. rewrite !rm3_kt_kw.
        eapply Z.le_trans; [apply (rm3_kw_incl _ (upds (drain_b_c.keys_texts (re_keys e)) (dr_lines h)))|].
        - first [exact (proj1 (NoDup_ListNoDup _) D9) | exact D9].
        - intros y Hy. exact (proj1 (D10 y) Hy).
        - apply rm3_upds_kw. }
      set (cap1 := if dr_live (lm_c m) h then drain_b_c.ds_ocap (dr_fin (lm_c m) (lm_mx m) 0 (lm_cap m) e h)
                   else lm_cap m) in HS.
      set (O1 := if dr_live (lm_c m) h then [] ++ LB else []) in HS.
      assert (Hc1 : cap1 <= Z.max (lm_cap m) (2 * P)).
      { unfold cap1. destruct (dr_live (lm_c m) h); cbv iota; [|lia].
        unfold dr_fin. pose proof (RelayCap.drain_ocap_le (dr_live (lm_c m) h) (lm_mx m) 0 (lm_cap m) e h) as [_ OC].
        pose proof (HNF (dr_live (lm_c m) h) (lm_mx m) (lm_cap m)) as NF. lia. }
      assert (HO1 : Z.of_nat (length O1) <= DT).
      { unfold O1. destruct (dr_live (lm_c m) h); cbv iota; cbn [app length]; [|lia].
        rewrite <- RelayCap.rc_length_bzs, D27. unfold DT. lia. }
      clearbody cap1 O1.
      assert (Hcap2 : cap2 <= Z.max (lm_cap m) (2 * (3 * P + KT))).
      { pose proof (f_equal snd HS) as HS2. cbn [snd] in HS2. rewrite <- HS2.
        eapply Z.le_trans; [apply rm3_sends_cap|]. rewrite rm3_tot_ge. lia. }
      destruct (rm3_rsum_lines (hl_recs (hs_expected h1)) (dr_lines h)) as [R1 R2].
      { rewrite D22, HP7. reflexivity. }
      fold DT in R1.
      assert (HDE : bsum (asrc_blks h1) - bsum (asrc_blks h) <= 128 + 33 * DT).
      { rewrite !rm3_asrc_bsum, !rm3_alist_bsum. rewrite D24, D16, D19, HP7, R1.
        pose proof (rm3_rsum_nonneg (hl_recs (hs_pending h))) as Rp.
        pose proof (rm3_wn_len (dr_lines h)) as WL. fold DT in WL.
        assert (HnE : hl_n (hs_expected h1) = Z.of_nat (length (dr_lines h))) by (unfold hl_n; rewrite R2; reflexivity).
        assert (V1 : rm3_V (hl_cap (hs_expected h1)) <= 128 + 16 * hl_cap (hs_expected h) + 32 * hl_n (hs_expected h1)).
        { unfold rm3_V, AREC. destruct (Z.eqb_spec (hl_cap (hs_expected h1)) 0); cbv iota; lia. }
        assert (V0 : rm3_V (hl_cap (hs_expected h)) = 16 * hl_cap (hs_expected h)).
        { unfold rm3_V, AREC. destruct (Z.eqb_spec (hl_cap (hs_expected h)) 0) as [E|E]; cbv iota; [rewrite E|]; lia. }
        change (rm3_rsum []) with 0. lia. }
      split; [lia|]. split; [exact D24|]. split.
      { intros r Hr.
        assert (Q : Z.of_nat (length (snd r)) + 1 <= rm3_rsum (hl_recs (hs_expected h1)))
          by exact (rm3_in_le_sum _ (fun r => Z.of_nat (length (snd r)) + 1) _ r ltac:(intros y; cbv beta; lia) Hr).
        lia. }
      assert (Hz : Forall SlotReads.zrange (dr_lines h)).
      { apply (SlotReads.lines_range (bzs (pending_stream h)) (hs_state h)); [|apply SlotReads.zrange_bzs].
        change (ls_w (hs_state h)) with (bzs (hs_W h)). apply SlotReads.zrange_bzs. }
      rewrite (SlotReads.texts_lines (hs_expected h1) (dr_lines h)) by first [exact Hz | rewrite D22, HP7; reflexivity].
      pose proof (SlotReads.count_begin_bytes (dr_lines h)) as CB.
      assert (CB' : 21 * Z.of_nat (count_begin (dr_lines h)) <= DT) by (unfold DT; lia). lia.
    - destruct Hrr as [[He1 Hh1] HS]. subst e1 h1.
      assert (Hcap2 : cap2 <= Z.max (lm_cap m) (2 * KT)).
      { pose proof (f_equal snd HS) as HS2. cbn [snd] in HS2. rewrite <- HS2.
        eapply Z.le_trans; [apply rm3_sends_cap|]. rewrite rm3_tot_ge. fold KT. cbn [length]. lia. }
      split; [lia|]. split; [reflexivity|]. split; [intros r Hr; rewrite HP7 in Hr; destruct Hr|].
      unfold texts. rewrite HP7. cbn [map]. replace (count_begin []) with 0%nat by reflexivity. lia. }
  clear Hrr. destruct HK as (HD & Hheld & Hrec & HCB).
  assert (HNH : 5 * hl_n (hs_held h1) <= KT).
  { rewrite Hheld. unfold hl_n. replace (length (hl_recs (hs_held h))) with (length (texts (hs_held h)))
      by (unfold texts; apply length_map).
    rewrite <- (SlotReads.same_set_length _ _ HEnd HP6 HP5). unfold drain_b_c.keys_texts. rewrite length_map.
    unfold KT. apply rm3_kt_len. }
  destruct HLS as (rest & e0 & HPm & HR & HEr & Hcx & Hl & Hnp & HM).
  pose proof (Hfr rest HPm) as HP1.
  assert (HBS : blocks_bytes S =
                bsum (input_blks cx) + bsum (model_blks (rm_mk cx m si (Some h1) j0 c2 O2 cap2 out2)) + bsum rest)
    by (rewrite (blocks_bytes_bsum B ly S), (bsum_perm _ _ HP1), !bsum_app; lia).
  pose proof (PHI3_ge m) as HG. pose proof (nopen_le4 _ Hl) as H4.
  assert (Hkk : kk cx m <= c_n cx) by (unfold kk; lia).
  assert (HCR : ACfn_cf.CALL_ROOM = 8589934592) by reflexivity.
  assert (HL : LIVE_MAX = 17179869184) by reflexivity.
  apply rm3_cnl_room.
  - rewrite Hheld. lia.
  - assert (LT : Z.of_nat (length (texts (hs_held h1))) = hl_n (hs_held h1))
      by (unfold texts, hl_n; rewrite length_map; reflexivity).
    change (txs (hl_recs (hs_expected h1))) with (texts (hs_expected h1)). lia.
  - exact Hrec.
  - assert (HV : 0 <= rm3_V (hl_cap (hs_held h1))).
    { rewrite Hheld. unfold rm3_V, AREC. destruct (hl_cap (hs_held h) =? 0); cbv iota; lia. }
    unfold W_OPEN, E_ENT, K0, MB_K, MB_C, APARTIAL in *. lia.
Qed.
(* ---------------------------------------------------------------- event *)
(* 1172d6d9065 _event.v:1031 LS_event_malloc's two room conjuncts (ReplyLSArms.v fr_LS_event_malloc); its meter
   conjunct is ReplyLSI.v's *)
Lemma fr_LS3_event_malloc : forall cx t m ly S e,
  fr_LS3 B cx t m ly S -> fr_RINV cx t m -> ev_evt cx m e ->
  re_len e < MMAX /\ blocks_bytes S + re_len e <= LIVE_MAX.
Proof.
  intros cx t m ly S e H _ (He & _).
  pose proof (fr_LS3_room B cx t m ly S H) as Hroom. pose proof (fr_LS3_k B cx t m ly S H) as Hk.
  destruct H as (rest & e0 & _ & _ & _ & Hc & _).
  assert (Hk0 : 0 <= lm_k m) by (unfold kk in Hk; lia).
  pose proof (ev_len_le cx m Hk0 ltac:(lia)) as Hl.
  assert (HW : WR_MMAX = 1072693248) by reflexivity.
  unfold re_len, ROOM_SPARE in *. split; lia.
Qed.
(* :1034 LS_event_relay at ReplyLSEvent3.v's proposed text with Hcap (fr_LS_event_relay_p) *)
Lemma fr_LS3_event_relay_p : forall cx t m ly S (S1 : astate) e (ly1 : alayout) q,
  fr_LS3 B cx t m ly S -> fr_RINV cx t m -> ev_evt cx m e ->
  mo_le MT S S1 (mo_malloc MT (re_len e)) ->
  lm_O m = [] ->
  ablocks B ly1 S1 = ablocks B ly S ++ [(q, re_len e)] ->
  forall (Hcap : lm_cap m < MMAX),
  sl_cap (lm_c m) (lm_mx m) (Z.of_nat (length (lm_O m))) (lm_cap m) (re_len e) < MMAX /\
  blocks_bytes S1 + 2 * sl_cap (lm_c m) (lm_mx m) (Z.of_nat (length (lm_O m))) (lm_cap m) (re_len e) <= LIVE_MAX /\
  mo_ok MT S1 (sl_cost MT (lm_c m) (lm_mx m) (Z.of_nat (length (lm_O m))) (lm_cap m) (re_len e)).
Proof.
  intros cx t m ly S S1 e ly1 q H _ (He & _) _ HO Hm Hcap.
  pose proof (fr_LS3_room_x B cx t m ly S H) as Hroom. pose proof (fr_LS3_k B cx t m ly S H) as Hk.
  pose proof (ev3_malloc_bb B ly S ly1 S1 q (re_len e) Hm) as Hbb.
  destruct H as (rest & e0 & _ & _ & _ & Hc & _).
  assert (Hk0 : 0 <= lm_k m) by (unfold kk in Hk; lia).
  pose proof (ev3_len_le cx m Hk0 ltac:(lia)) as Hl.
  pose proof (ev3_cap_le (lm_c m) (lm_mx m) (Z.of_nat (length (lm_O m))) (lm_cap m) (re_len e)) as Hcb.
  assert (Hno : Z.of_nat (length (lm_O m)) = 0) by (rewrite HO; reflexivity).
  assert (HL : re_len e = Z.of_nat (length e) + 1) by reflexivity.
  assert (HW : WR_MMAX = 1072693248) by reflexivity.
  refine (conj _ (conj _ I)); lia.
Qed.
(* LS_event_relay's RELAXED room conjuncts (ReplyLSEvent3.v fr_LS_event_relay_r, send_line's own room premises); its
   meter conjunct is ReplyLSI.v's *)
Lemma fr_LS3_event_relay_r : forall cx t m ly S (S1 : astate) e (ly1 : alayout) q,
  fr_LS3 B cx t m ly S -> fr_RINV cx t m -> ev_evt cx m e ->
  mo_le MT S S1 (mo_malloc MT (re_len e)) ->
  lm_O m = [] ->
  ablocks B ly1 S1 = ablocks B ly S ++ [(q, re_len e)] ->
  sl_maxr (lm_c m) (lm_mx m) (Z.of_nat (length (lm_O m))) (lm_cap m) (re_len e) < MMAX /\
  blocks_bytes S1 + sl_alloc (lm_c m) (lm_mx m) (Z.of_nat (length (lm_O m))) (lm_cap m) (re_len e) <= LIVE_MAX.
Proof.
  intros cx t m ly S S1 e ly1 q H _ (He & _) _ HO Hm.
  pose proof (fr_LS3_room B cx t m ly S H) as Hroom. pose proof (fr_LS3_k B cx t m ly S H) as Hk.
  pose proof (ev3_malloc_bb B ly S ly1 S1 q (re_len e) Hm) as Hbb.
  destruct H as (rest & e0 & _ & _ & _ & Hc & _).
  assert (Hk0 : 0 <= lm_k m) by (unfold kk in Hk; lia).
  pose proof (ev3_len_le cx m Hk0 ltac:(lia)) as Hl.
  pose proof (ev3_maxr_le (lm_c m) (lm_mx m) (Z.of_nat (length (lm_O m))) (lm_cap m) (re_len e)) as Hmx.
  pose proof (ev3_alloc_le (lm_c m) (lm_mx m) (Z.of_nat (length (lm_O m))) (lm_cap m) (re_len e)) as Hal.
  assert (Hno : Z.of_nat (length (lm_O m)) = 0) by (rewrite HO; reflexivity).
  assert (HL : re_len e = Z.of_nat (length e) + 1) by reflexivity.
  assert (HW : WR_MMAX = 1072693248) by reflexivity.
  unfold ROOM_SPARE in Hroom. split; lia.
Qed.
(* :1045 LS_event_step at ReplyLSEvent3.v's proposed text (fr_LS_event_step_p): the out buffer's growth is paid by
   the input the event consumes; ECRED is unchanged (the event keeps the entries and the sources) *)
Lemma fr_LS3_event_step_p : forall cx t m ly S (S1 S2 S3 : astate) (ly3 : alayout) e v out' (ly1 ly2 : alayout) q,
  fr_LS3 B cx t m ly S -> ev_evt cx m e ->
  mo_le MT S S1 (mo_malloc MT (re_len e)) ->
  mo_le MT S1 S2 (sl_cost MT (lm_c m) (lm_mx m) (Z.of_nat (length (lm_O m))) (lm_cap m) (re_len e)) ->
  mo_le MT S2 S3 (mo_free MT) ->
  0 <= lm_k m < c_n cx -> lm_O m = [] -> 0 <= lm_cap m ->
  ablocks B ly1 S1 = ablocks B ly S ++ [(q, re_len e)] ->
  (exists rest, Permutation (ablocks B ly1 S1) (aout_blks (lm_cap m) (lm_out m) ++ rest) /\
     Permutation (ablocks B ly2 S2)
       (aout_blks (sl_cap (lm_c m) (lm_mx m) (Z.of_nat (length (lm_O m))) (lm_cap m) (re_len e)) out' ++ rest)) ->
  (exists l1 l2, ablocks B ly2 S2 = l1 ++ (q, re_len e) :: l2 /\ ablocks B ly3 S3 = l1 ++ l2) ->
  fr_LS3 B cx (t + 1) (ev_step cx m e v out') ly3 S3.
Proof.
  intros cx t m ly S S1 S2 S3 ly3 e v out' ly1 ly2 q H HE _ _ _ Hk HO Hc0 Hm (restR & HR1 & HR2)
    (l1 & l2 & Hf2 & Hf3).
  pose proof (ev3_k2 cx m e Hk HE) as Hk2.
  pose proof (ev3_cap_le (lm_c m) (lm_mx m) (Z.of_nat (length (lm_O m))) (lm_cap m) (re_len e)) as Hcb.
  destruct H as (rest & e0 & HP & HR & HEn & Hc & Hl & Hnp & HM).
  set (cap' := sl_cap (lm_c m) (lm_mx m) (Z.of_nat (length (lm_O m))) (lm_cap m) (re_len e)) in *.
  assert (EM' : model_blks (ev_step cx m e v out') = ev3_pfx m ++ aout_blks cap' out')
    by (rewrite ev3_model_blks; reflexivity).
  exists rest, e0. split; [| split; [exact HR | split; [exact HEn | split; [exact Hc | split]]]].
  - rewrite Hf3, EM'. rewrite Hf2 in HR2. rewrite Hm in HR1. rewrite ev3_model_blks in HP.
    clear - HP HR1 HR2. ls3_perm.
  - exact Hl.
  - assert (En : npend (ev_step cx m e v out') = npend m) by reflexivity.
    assert (Ek' : kk cx (ev_step cx m e v out') = Z.min (ev_k2 cx m) (c_n cx)) by reflexivity.
    assert (Ek : kk cx m = Z.min (lm_k m) (c_n cx)) by reflexivity.
    assert (Eo : nopen (lm_hs (ev_step cx m e v out')) = nopen (lm_hs m)) by reflexivity.
    assert (EP : PHI3 (ev_step cx m e v out') =
                 PHI3 m - bsum (aout_blks (lm_cap m) (lm_out m)) + bsum (aout_blks cap' out')).
    { unfold PHI3, PHI. rewrite EM', ev3_model_blks, !bsum_app.
      change (pend_bytes (ev_step cx m e v out')) with (pend_bytes m).
      change (held_bytes (ev_step cx m e v out')) with (held_bytes m).
      change (vslack (ev_step cx m e v out')) with (vslack m).
      change (ECRED (ev_step cx m e v out')) with (ECRED m). lia. }
    pose proof (ev3_bsum_aout cap' out') as Hnew.
    pose proof (ev3_bsum_aout_eq (lm_cap m) (lm_out m) Hc0) as Hold.
    assert (Hno : Z.of_nat (length (lm_O m)) = 0) by (rewrite HO; reflexivity).
    assert (HL : re_len e = Z.of_nat (length e) + 1) by reflexivity.
    rewrite En, Ek', Eo, EP. rewrite Ek in Hnp, HM. unfold W_OPEN, E_ENT, K0, MB_K, MB_C, APARTIAL in *.
    split; lia.
Qed.
End arms3b.
