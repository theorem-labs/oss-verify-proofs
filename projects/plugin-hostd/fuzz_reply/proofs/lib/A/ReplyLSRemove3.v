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
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_reply/lib/A/ReplyLSDrain3.v, with its module names changed; 542 of its 649 lines of code are new or changed and 481 lines of the source are left out. *)
(* a Theorem Labs lane's FREE-PIECES row B1c (a Theorem Labs lane): the remove arm's LS rules at the instance LS := fr_LS B,
   RINV := fr_RINV, MT := ameter_triv, MMAX := WR_MMAX (lib/A/ReplyLS.v v2, lib/A/ReplyRINV.v), against the texts of
   a working branch 30d91cacb63 lib/A/W_LLVMFuzzerTestOneInput_remove.v (every definition the
   texts name is the worktree's: W_contract.v's rr_tr / tr_alloc / tr_max / cnl_room / sl_sends / dr_rel / rr_found
   and ReplyRINV.v's copies rm_at / rm_mk / rm_rr_ok / rm_cnl_ok / rm_cshe_ok are textually the arm head's; rm_rr_tr
   and the rm_*_cost meters are W_LLVMFuzzerTestOneInput_remove.v's own).
   - LS_rm_rr_pre :1971.  Proved: its sizes and meter conjuncts (fr_LS_rm_rr_pre_sizes, no extra fact) and, with
     the one extra fact Hcap : lm_cap m <= 2 ^ 29, its two lm_cap bounds (fr_LS_rm_rr_pre_part).  Not provable:
     `blocks_bytes S + tr_alloc (rm_rr_tr m h) <= LIVE_MAX` (rm_rr_tr: _remove.v's; tr_alloc sums every request;
     drain_b_c.v seen_tr
     reallocs the held-key array to (n + 1) * 8 per new begin line, so K distinct begin lines ask >= 4 K (K + 1):
     65,536 of them, a 1.6 MB pending stream that fr_RINV allows, ask more than LIVE_MAX) and so the conjunct with
     4 * Z.max; `tr_max (rm_rr_tr m h) < MMAX` needs `t < OPS_MAX`, which the text lacks.
   - LS_rm_cnl_pre :2622.  Proved at a PROPOSED text (fr_LS_rm_cnl_pre_p): two premises the arm holds at its
     check_no_loss call (the model's block sizes and relay_remove's frame on the live blocks), no extra fact.
   - LS_rm_step :5460.  Proved at a PROPOSED text (fr_LS_rm_step_p) with one premise the arm holds and one named
     extra fact Hout (the stream buffer's growth is paid by the released credit), which fr_LS v2 lacks for the relay's
     unfinished line. *)
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
  drain_b_c gestures_end_b_c gesture_end_c relay_remove_b_c RelayCap SlotReads SlotInv.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require ACfn_cf.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require W_LLVMFuzzerTestOneInput_remove.
Import ListNotations.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.


Local Notation MT := ameter_triv.
Local Notation MMAX := WR_MMAX.
Local Notation zsum l := (fold_right Z.add 0 l).

(* ================================================================== pure helpers *)
Lemma rm3_in_le_sum : forall (X : Type) (g : X -> Z) l x, (forall y, 0 <= g y) -> In x l -> g x <= zsum (map g l).
Proof.
  intros X g l x Hg. induction l as [|y l IH]; intros Hx; [destruct Hx|].
  cbn [map fold_right]. pose proof (zsum_map_nonneg g l Hg). destruct Hx as [<- | Hx]; [lia|].
  specialize (IH Hx). specialize (Hg y). lia.
Qed.
Lemma rm3_nodup_inj : forall (X Y : Type) (f : X -> Y) l x y, List.NoDup (map f l) -> In x l -> In y l -> f x = f y ->
  x = y.
Proof.
  intros X Y f l. induction l as [|a l IH]; intros x y Hnd Hx Hy E; [destruct Hx|].
  cbn [map] in Hnd. apply NoDup_cons_iff in Hnd as [Ha Hnd].
  destruct Hx as [<- | Hx]; destruct Hy as [<- | Hy]; [reflexivity | | | exact (IH x y Hnd Hx Hy E)].
  - exfalso. apply Ha. rewrite E. apply in_map. exact Hy.
  - exfalso. apply Ha. rewrite <- E. apply in_map. exact Hx.
Qed.
Lemma rm3_bsum_nonneg : forall l, (forall b, In b l -> 0 <= snd b) -> 0 <= bsum l.
Proof.
  induction l as [|b l IH]; intros H; [rewrite bsum_nil; lia|]. rewrite bsum_cons.
  pose proof (H b (or_introl eq_refl)). pose proof (IH (fun b' Hb => H b' (or_intror Hb))). lia.
Qed.
Lemma rm3_bsum_concat : forall (X : Type) (f : X -> list (Z * Z)) l,
  bsum (concat (map f l)) = zsum (map (fun x => bsum (f x)) l).
Proof.
  intros X f l. induction l as [|x l IH]; [reflexivity|]. cbn [map concat fold_right]. rewrite bsum_app, IH. reflexivity.
Qed.
Lemma rm3_set_zsum : forall (X : Type) (g : X -> Z) i x y l, nth_error l i = Some y ->
  zsum (map g (rm_set_nth i x l)) + g y = zsum (map g l) + g x.
Proof.
  intros X g i. induction i as [|i IH]; intros x y [|z l] H; cbn in H; try discriminate.
  - injection H as ->. cbn. lia.
  - cbn [rm_set_nth map fold_right]. specialize (IH x y l H). lia.
Qed.
Lemma rm3_nth_lt : forall (hs : list (option hsrc)) i h, nth i hs None = Some h -> (i < length hs)%nat.
Proof.
  intros hs i h H. destruct (Nat.lt_ge_cases i (length hs)) as [L|L]; [exact L|].
  rewrite nth_overflow in H by exact L. discriminate H.
Qed.
Lemma rm3_wn_len : forall ls, Z.of_nat (length ls) <= Z.of_nat (length (with_nul ls)).
Proof. intros ls. pose proof (SlotReads.lines_count ls). lia. Qed.
Lemma rm3_skip_if : forall s (X : Z), (s = 0 \/ s = 1) -> (if s =? 1 then 0 else X) = (if s =? 0 then X else 0).
Proof. intros s X [-> | ->]; reflexivity. Qed.

(* ---- the relay's lines: bytes in, bytes out (RelayModel.scan / chunk, the relay's own splitter) ---- *)
Lemma rm3_scan_mass : forall d skip acc,
  Z.of_nat (length (with_nul (snd (scan skip acc d)))) +
  (if fst (fst (scan skip acc d)) then 0 else Z.of_nat (length (snd (fst (scan skip acc d))))) <=
  (if skip then 0 else Z.of_nat (length acc)) + Z.of_nat (length d).
Proof.
  induction d as [|b d IH]; intros skip acc.
  - cbn [scan fst snd]. rewrite RelayCap.with_nul_nil_len. cbn [length]. destruct skip; lia.
  - destruct (Z.eq_dec b 0) as [-> | Hb].
    + rewrite scan_zero. pose proof (IH false []) as I. cbn [length] in I |- *.
      destruct (scan false [] d) as [[sk r] ls]. cbv beta iota in I |- *. cbn [fst snd] in I |- *.
      destruct (skip || Nat.ltb LINE_LIMIT (length acc))%bool eqn:C.
      * destruct skip, sk; lia.
      * apply orb_false_iff in C as [C _]. subst skip. rewrite RelayCap.with_nul_cons_len. destruct sk; lia.
    + rewrite (scan_nz skip acc b d Hb). pose proof (IH skip (acc ++ [b])) as I.
      rewrite length_app in I. cbn [length] in I |- *.
      destruct (fst (fst (scan skip (acc ++ [b]) d))), skip; lia.
Qed.
Lemma rm3_chunk_mass : forall u skip d u' sk' rl, chunk u skip d = (u', sk', rl) ->
  Z.of_nat (length (with_nul rl)) + (if sk' then 0 else Z.of_nat (length u')) <=
  (if skip then 0 else Z.of_nat (length u)) + Z.of_nat (length d).
Proof.
  intros u skip d u' sk' rl E. unfold chunk in E. pose proof (rm3_scan_mass d skip u) as M.
  destruct (scan skip u d) as [[sk r] ls]. cbv beta iota in E. cbn [fst snd] in M.
  destruct (Nat.ltb LINE_LIMIT (length r)); injection E as <- <- <-; cbn [length]; [destruct sk; lia | exact M].
Qed.

(* ---- drain's g_nout: at most the relay's unfinished line (when it keeps it) and the pending stream ---- *)
Definition rm3_dstr (s : drain_b_c.dstate) : list Z :=
  match drain_b_c.ds_pend s with [] => [] | r :: rs => skipn (Z.to_nat (drain_b_c.ds_off s)) r ++ concat rs end.
Definition rm3_dm (s : drain_b_c.dstate) : Z :=
  drain_b_c.ds_no s + (if drain_b_c.ds_skip s then 0 else Z.of_nat (length (drain_b_c.ds_u s))) +
  Z.of_nat (length (rm3_dstr s)).
Lemma rm3_dstr0 : forall rs : list (list Z),
  length (match rs with [] => [] | r :: rs' => skipn (Z.to_nat 0) r ++ concat rs' end) = length (concat rs).
Proof. intros [|r rs]; reflexivity. Qed.
Lemma rm3_dm_run : forall f lv mx s j a, 0 <= drain_b_c.ds_off s ->
  rm3_dm (fst (snd (drain_b_c.drain_run f lv mx s j a))) <= rm3_dm s.
Proof.
  intros f lv mx. induction f as [|f IH]; intros s j a Ho; [cbn [drain_b_c.drain_run fst snd]; lia|].
  cbn [drain_b_c.drain_run]. cbv zeta.
  destruct (drain_b_c.ds_eintr s).
  - cbn [fst snd].
    match goal with |- rm3_dm (fst (snd (drain_b_c.drain_run f lv mx ?s1 ?j1 ?a1))) <= _ =>
      eapply Z.le_trans; [apply (IH s1 j1 a1); exact Ho|] end.
    unfold rm3_dm, rm3_dstr.
    cbn [drain_b_c.ds_no drain_b_c.ds_skip drain_b_c.ds_u drain_b_c.ds_pend drain_b_c.ds_off]. lia.
  - unfold rm3_dm at 2. unfold rm3_dstr.
    destruct (drain_b_c.ds_pend s) as [|r0 rs] eqn:Ep.
    + cbn [fst snd]. unfold rm3_dm, rm3_dstr.
      cbn [drain_b_c.ds_no drain_b_c.ds_skip drain_b_c.ds_u drain_b_c.ds_pend drain_b_c.ds_off]. lia.
    + match goal with |- context [Z.min ?x ?y <=? 0] => set (n := Z.min x y) in * end.
      assert (Hnr : n <= Z.of_nat (length r0) - drain_b_c.ds_off s) by (unfold n; apply Z.le_min_l).
      destruct (Z.leb_spec n 0) as [Hn | Hn].
      * cbn [fst snd]. unfold rm3_dm, rm3_dstr.
        cbn [drain_b_c.ds_no drain_b_c.ds_skip drain_b_c.ds_u drain_b_c.ds_pend drain_b_c.ds_off]. lia.
      * match goal with |- context [chunk (drain_b_c.ds_u s) (drain_b_c.ds_skip s) ?d] =>
          set (dd := d) in *;
          destruct (chunk (drain_b_c.ds_u s) (drain_b_c.ds_skip s) dd) as [[u' sk'] rl] eqn:EC end.
        pose proof (rm3_chunk_mass _ _ _ _ _ _ EC) as CM.
        assert (Ld : Z.of_nat (length dd) = n) by (unfold dd; rewrite length_firstn, length_skipn; lia).
        try (cbv beta iota).
        match goal with |- context [drain_b_c.lines_run lv mx (drain_b_c.ds_no s) (drain_b_c.ds_ocap s)
                                      (drain_b_c.ds_H s) (drain_b_c.ds_ka s) rl ?j3 ?o ?ha ?ks] =>
          destruct (drain_b_c.lines_run lv mx (drain_b_c.ds_no s) (drain_b_c.ds_ocap s) (drain_b_c.ds_H s)
                      (drain_b_c.ds_ka s) rl j3 o ha ks) as [[tl [[oc' H'] ka']] [[o' ha'] ks']] end.
        cbn [fst snd].
        match goal with |- rm3_dm (fst (snd (drain_b_c.drain_run f lv mx ?s2 ?j4 ?a2))) <= _ =>
          eapply Z.le_trans; [apply (IH s2 j4 a2)|] end.
        { cbn [drain_b_c.ds_off]. destruct (_ =? _); lia. }
        unfold rm3_dm, rm3_dstr.
        cbn [drain_b_c.ds_no drain_b_c.ds_skip drain_b_c.ds_u drain_b_c.ds_pend drain_b_c.ds_off].
        rewrite length_app, length_skipn.
        destruct (Z.eqb_spec (drain_b_c.ds_off s + n) (Z.of_nat (length r0))) as [W|W].
        -- rewrite rm3_dstr0. lia.
        -- rewrite length_app, length_skipn. lia.
Qed.
Lemma rm3_skipn_map : forall (X Y : Type) (f : X -> Y) n l, skipn n (map f l) = map f (skipn n l).
Proof. intros X Y f n. induction n as [|n IH]; intros [|x l]; cbn; try reflexivity. apply IH. Qed.
Lemma rm3_dstr_init : forall NO CAP e h, rm3_dstr (drain_b_c.drain_init NO CAP e h) = bzs (pending_stream h).
Proof.
  intros NO CAP e h. unfold rm3_dstr, drain_b_c.drain_init, pending_stream. cbn [drain_b_c.ds_pend drain_b_c.ds_off].
  destruct (hl_recs (hs_pending h)) as [|r rs]; [reflexivity|]. cbn [map].
  unfold bzs. rewrite map_app, rm3_skipn_map, concat_map, map_map. reflexivity.
Qed.
Lemma rm3_no_fin : forall live mx CAP e h, 0 <= hs_off h ->
  drain_b_c.ds_no (drain_b_c.drain_fin live mx 0 CAP e h) <=
  (if re_skip e =? 1 then 0 else Z.of_nat (length (re_U e))) + Z.of_nat (length (pending_stream h)).
Proof.
  intros live mx CAP e h Ho. unfold drain_b_c.drain_fin, drain_b_c.drain_go.
  pose proof (rm3_dm_run (S (S (length (pending_stream h)))) live mx (drain_b_c.drain_init 0 CAP e h) 0%nat
    drain_b_c.dadr0 Ho) as D.
  unfold rm3_dm at 2 in D. rewrite rm3_dstr_init in D.
  cbn [drain_b_c.drain_init drain_b_c.ds_no drain_b_c.ds_skip drain_b_c.ds_u] in D.
  rewrite !RelayCap.rc_length_bzs in D.
  revert D. generalize (fst (snd (drain_b_c.drain_run (S (S (length (pending_stream h)))) live mx
    (drain_b_c.drain_init 0 CAP e h) 0 drain_b_c.dadr0))). intros s D.
  unfold rm3_dm in D. destruct (drain_b_c.ds_skip s); lia.
Qed.

(* ---- the gesture ends' bytes and g_capout after sends ---- *)
Definition rm3_tot (Bs : list (list byte)) : Z := zsum (map (fun Bl => Z.of_nat (length Bl)) Bs).
Lemma rm3_tot_ge : forall ks, rm3_tot (ge_bytes ks) = gestures_end_b_c.keys_total ks.
Proof.
  intros ks. unfold rm3_tot, ge_bytes. induction ks as [|k ks IH]; [reflexivity|].
  cbn [map concat app fold_right]. rewrite IH. change (length gesture_end_c.END5) with 5%nat.
  change (gestures_end_b_c.keys_total (k :: ks)) with
    (Z.of_nat (length (gestures_end_b_c.key_text k)) + 5 + gestures_end_b_c.keys_total ks). lia.
Qed.
Lemma rm3_sends_cap : forall Bs mx c O cap,
  snd (sl_sends mx c O cap Bs) <= Z.max cap (2 * (Z.of_nat (length O) + rm3_tot Bs)).
Proof.
  induction Bs as [|Bl r IH]; intros mx c O cap.
  - cbn [sl_sends snd]. apply Z.le_max_l.
  - cbn [sl_sends]. cbv zeta.
    assert (LO : Z.of_nat (length (sl_O c O Bl)) <= Z.of_nat (length O) + Z.of_nat (length Bl)).
    { unfold sl_O. destruct (sl_live c (Z.of_nat (length Bl))); [rewrite length_app|]; lia. }
    assert (T0 : 0 <= rm3_tot r) by (apply zsum_map_nonneg; intros; lia).
    assert (TC : rm3_tot (Bl :: r) = Z.of_nat (length Bl) + rm3_tot r) by reflexivity.
    rewrite TC.
    apply (RelayCap.rc_step cap (sl_cap c mx (Z.of_nat (length O)) cap (Z.of_nat (length Bl))) _
             (Z.of_nat (length O) + Z.of_nat (length Bl)) (Z.of_nat (length (sl_O c O Bl)) + rm3_tot r));
      [apply RelayCap.send_line_cap_le | apply IH | lia | lia].
Qed.

(* ---- the held keys after drain: the keys' bytes grow by at most twice the lines' ---- *)
Definition rm3_kw (T : list (list Z)) : Z := zsum (map (fun x => Z.of_nat (length x) + 5) T).
Lemma rm3_kw_filter : forall (p : list Z -> bool) T, rm3_kw (List.filter p T) <= rm3_kw T.
Proof.
  intros p T. unfold rm3_kw. induction T as [|x T IH]; [cbn; lia|]. cbn [List.filter].
  destruct (p x); cbn [map fold_right]; lia.
Qed.
Lemma rm3_gesture_len : forall l k x, gesture l = Some (k, x) -> (length x <= length l)%nat.
Proof.
  intros l k x H. unfold gesture in H.
  destruct (list_eqb (firstn 13 l) K_GESTURE && Z.eqb (nth 13 l 0) SPACE && Nat.ltb 13 (length l)); [|discriminate].
  destruct (last_space_from 0 l) as [j|]; [|discriminate].
  destruct (Nat.ltb 13 j); [|discriminate].
  destruct (list_eqb (skipn (S j) l) W_BEGIN); [injection H as _ <-; rewrite length_firstn; lia|].
  destruct (list_eqb (skipn (S j) l) W_END); [injection H as _ <-; rewrite length_firstn; lia | discriminate].
Qed.
Lemma rm3_upd_kw : forall T l, rm3_kw (upd T l) <= rm3_kw T + 2 * (Z.of_nat (length l) + 1).
Proof.
  intros T l. unfold upd. destruct (gesture l) as [[[|] x]|] eqn:G.
  - destruct (existsb (list_eqb x) T); [lia|].
    unfold rm3_kw. rewrite map_app, zsum_app. cbn [map fold_right].
    pose proof (rm3_gesture_len l GBegin x G). pose proof (SlotReads.gesture_begin_len l x G). lia.
  - pose proof (rm3_kw_filter (fun y => negb (list_eqb x y)) T). lia.
  - lia.
Qed.
Lemma rm3_upds_kw : forall ls T, rm3_kw (upds T ls) <= rm3_kw T + 2 * Z.of_nat (length (with_nul ls)).
Proof.
  induction ls as [|l ls IH]; intros T.
  - unfold upds. cbn [fold_left]. rewrite RelayCap.with_nul_nil_len. lia.
  - unfold upds in *. cbn [fold_left]. rewrite RelayCap.with_nul_cons_len.
    pose proof (IH (upd T l)). pose proof (rm3_upd_kw T l). lia.
Qed.
Lemma rm3_kw_incl : forall A Bl, List.NoDup A -> incl A Bl -> rm3_kw A <= rm3_kw Bl.
Proof.
  induction A as [|a A IH]; intros Bl Hnd Hinc.
  - unfold rm3_kw at 1. cbn [map fold_right]. apply zsum_map_nonneg. intros x. lia.
  - apply NoDup_cons_iff in Hnd as [Ha Hnd].
    assert (Hin : In a Bl) by (apply Hinc; left; reflexivity).
    destruct (in_split _ _ Hin) as (l1 & l2 & ->).
    assert (Hi : incl A (l1 ++ l2)).
    { intros x Hx. assert (Hx' : In x (l1 ++ a :: l2)) by (apply Hinc; right; exact Hx).
      apply in_app_iff in Hx' as [H1 | [H2 | H3]]; apply in_app_iff;
        [left; exact H1 | subst x; contradiction | right; exact H3]. }
    specialize (IH (l1 ++ l2) Hnd Hi).
    unfold rm3_kw in *.
    rewrite (fr_sum_perm _ _ (l1 ++ a :: l2) (a :: l1 ++ l2) (Permutation_sym (Permutation_middle l1 l2 a))).
    cbn [map fold_right]. lia.
Qed.
Lemma rm3_kt_kw : forall ks, gestures_end_b_c.keys_total ks = rm3_kw (drain_b_c.keys_texts ks).
Proof.
  induction ks as [|k ks IH]; [reflexivity|].
  change (gestures_end_b_c.keys_total (k :: ks)) with
    (Z.of_nat (length (gestures_end_b_c.key_text k)) + 5 + gestures_end_b_c.keys_total ks).
  change (drain_b_c.keys_texts (k :: ks)) with (bzs (gestures_end_b_c.key_text k) :: drain_b_c.keys_texts ks).
  unfold rm3_kw in *. cbn [map fold_right]. rewrite IH, RelayCap.rc_length_bzs. lia.
Qed.

(* ---- check_no_loss's room (cnl_room, W_contract.v / arm head W_check_no_loss.v:89) from a fixed slack ---- *)
Definition rm3_V (cap : Z) : Z := if cap =? 0 then 0 else AREC * cap.
Lemma rm3_tbytes_app : forall T T', tbytes (T ++ T') = tbytes T + tbytes T'.
Proof. intros T T'. induction T as [|x T IH]; cbn [app tbytes fold_right]; unfold tbytes in *; cbn; lia. Qed.
Lemma rm3_tbytes_filter : forall (p : list Z -> bool) T, tbytes (List.filter p T) <= tbytes T.
Proof.
  intros p T. induction T as [|x T IH]; [cbn; lia|]. cbn [List.filter].
  destruct (p x); unfold tbytes in *; cbn [fold_right]; lia.
Qed.
Lemma rm3_tbytes_upd : forall T l, tbytes (upd T l) <= tbytes T + Z.of_nat (length l) + 1.
Proof.
  intros T l. unfold upd. destruct (gesture l) as [[[|] x]|] eqn:G.
  - destruct (existsb (list_eqb x) T); [lia|]. rewrite rm3_tbytes_app.
    pose proof (rm3_gesture_len l GBegin x G). unfold tbytes at 2. cbn [fold_right]. lia.
  - pose proof (rm3_tbytes_filter (fun y => negb (list_eqb x y)) T). lia.
  - lia.
Qed.
Lemma rm3_filter_len : forall (p : list Z -> bool) T, (length (List.filter p T) <= length T)%nat.
Proof. intros p T. induction T as [|x T IH]; [cbn; lia|]. cbn [List.filter]. destruct (p x); cbn [length]; lia. Qed.
Lemma rm3_len_upd : forall T l, (length (upd T l) <= length T + (if is_begin l then 1 else 0))%nat.
Proof.
  intros T l. unfold upd, is_begin. destruct (gesture l) as [[[|] x]|].
  - destruct (existsb (list_eqb x) T); [lia | rewrite length_app; cbn [length]; lia].
  - pose proof (rm3_filter_len (fun y => negb (list_eqb x y)) T). lia.
  - lia.
Qed.
Lemma rm3_cnl_room : forall rs T cap bb,
  0 <= cap <= 2 ^ 25 ->
  Z.of_nat (length T) + Z.of_nat (count_begin (txs rs)) < 2 ^ 24 ->
  (forall r, In r rs -> Z.of_nat (length (snd r)) + 1 <= 2 ^ 26) ->
  bb - rm3_V cap + 2 ^ 29 + 2 ^ 29 + 2 ^ 26 <= LIVE_MAX ->
  cnl_room MMAX bb T cap rs.
Proof.
  induction rs as [|r rs IH]; intros T cap bb Hc Hn Hr Hb; [exact I|].
  cbn [cnl_room].
  change (txs (r :: rs)) with (bzs (snd r) :: txs rs) in Hn. rewrite SlotReads.count_begin_cons in Hn.
  set (l := bzs (snd r)) in *.
  assert (Hl : Z.of_nat (length l) = Z.of_nat (length (snd r))) by (unfold l; rewrite RelayCap.rc_length_bzs; reflexivity).
  assert (Hr0 : Z.of_nat (length (snd r)) + 1 <= 2 ^ 26) by (apply Hr; left; reflexivity).
  assert (HV : 0 <= rm3_V cap <= 2 ^ 29) by (unfold rm3_V, AREC; destruct (cap =? 0); cbv iota; lia).
  assert (HW : WR_MMAX = 1072693248) by reflexivity.
  pose proof (rm3_len_upd T l) as HU.
  assert (HT : Z.of_nat (length T) < 2 ^ 24 /\ Z.of_nat (length (upd T l)) + Z.of_nat (count_begin (txs rs)) < 2 ^ 24)
    by (revert Hn HU; destruct (is_begin l); intros Hn HU; cbv iota in Hn, HU; split; lia).
  clear Hn HU. destruct HT as [HT HnI].
  assert (Hg : Z.of_nat (length T) = cap -> AREC * grow_cap (Z.of_nat (length T)) cap <= 2 ^ 29).
  { intros E. unfold grow_cap, AREC. rewrite E, Z.eqb_refl. cbv iota. destruct (cap =? 0); cbv iota; lia. }
  split; [intros E; specialize (Hg E); lia|].
  split.
  { destruct (Z.eqb_spec (Z.of_nat (length T)) cap) as [E|E]; [specialize (Hg E)|]; cbv iota; lia. }
  apply IH.
  - unfold capstep. destruct (Nat.ltb (length T) (length (upd T l))); cbv iota; [|exact Hc].
    unfold grow_cap. destruct (Z.eqb_spec (Z.of_nat (length T)) cap) as [E|E]; cbv iota; [|exact Hc].
    destruct (cap =? 0); cbv iota; lia.
  - exact HnI.
  - intros r' Hr'. apply Hr. right. exact Hr'.
  - unfold hbytes. fold (rm3_V cap) (rm3_V (capstep T l cap)). pose proof (rm3_tbytes_upd T l). lia.
Qed.

(* ================================================================== the model's blocks *)
Section rm3.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : asyms.

Lemma rm3_in_model_entry : forall m j0 b, (j0 < length (lm_es m))%nat -> In b (aentry_blks (rm_ent m j0)) ->
  In b (model_blks m).
Proof.
  intros m j0 b Hj Hb. unfold model_blks. right. apply in_or_app. left. apply in_concat.
  exists (aentry_blks (rm_ent m j0)). split; [apply in_map; unfold rm_ent; apply nth_In; exact Hj | exact Hb].
Qed.
Lemma rm3_in_model_slot : forall m si h b, nth si (lm_hs m) None = Some h -> In b (asrc_blks h) -> In b (model_blks m).
Proof.
  intros m si h b Hh Hb. unfold model_blks. right. apply in_or_app. right. apply in_or_app. left. apply in_concat.
  exists (slot_blks (Some h)). split; [|exact Hb]. apply in_map. rewrite <- Hh. apply nth_In. exact (rm3_nth_lt _ _ _ Hh).
Qed.
Lemma rm3_in_model_out : forall m b, In b (aout_blks (lm_cap m) (lm_out m)) -> In b (model_blks m).
Proof. intros m b Hb. unfold model_blks. right. apply in_or_app. right. apply in_or_app. right. exact Hb. Qed.

Definition rm3_rsum (rs : list (Z * list byte)) : Z := zsum (map (fun r => Z.of_nat (length (snd r)) + 1) rs).
Lemma rm3_rsum_nonneg : forall rs, 0 <= rm3_rsum rs.
Proof. intros rs. apply zsum_map_nonneg. intros r. lia. Qed.
Lemma rm3_alist_bsum : forall l, bsum (alist_blks l) = rm3_V (hl_cap l) + rm3_rsum (hl_recs l).
Proof.
  intros l. unfold alist_blks, rm3_V, rm3_rsum. rewrite bsum_app.
  assert (E : forall rs : list (Z * list byte), bsum (map (fun r => (fst r, Z.of_nat (length (snd r)) + 1)) rs) =
                         zsum (map (fun r => Z.of_nat (length (snd r)) + 1) rs))
    by (induction rs as [|r rs IH]; [reflexivity | cbn [map fold_right]; rewrite bsum_cons, IH; reflexivity]).
  rewrite E. destruct (hl_cap l =? 0); [rewrite bsum_nil | rewrite bsum_cons, bsum_nil; cbn [snd]]; lia.
Qed.
Lemma rm3_asrc_bsum : forall h, bsum (asrc_blks h) =
  APARTIAL + bsum (alist_blks (hs_pending h)) + bsum (alist_blks (hs_expected h)) + bsum (alist_blks (hs_held h)).
Proof. intros h. unfold asrc_blks. rewrite bsum_cons, !bsum_app. cbn [snd]. lia. Qed.
(* the expected records drain pushes: one per line, its bytes and NUL *)
Lemma rm3_rsum_lines : forall rs ls, map snd rs = map (map (Z_to_bv 8)) ls ->
  rm3_rsum rs = Z.of_nat (length (with_nul ls)) /\ length rs = length ls.
Proof.
  unfold rm3_rsum. induction rs as [|r rs IH]; intros [|l ls] E; cbn [map] in E; try discriminate.
  - split; reflexivity.
  - injection E as E1 E2. destruct (IH ls E2) as [I1 I2]. cbn [map fold_right length].
    rewrite RelayCap.with_nul_cons_len, E1, length_map. split; [lia | rewrite I2; reflexivity].
Qed.

(* the model after the remove arm's calls: entry j0 left the table, slot si holds o, the stream's buffer is (cap, out) *)
Lemma rm3_model_bsum : forall cx m si o j0 c O cap out h,
  nth si (lm_hs m) None = Some h -> (j0 < length (lm_es m))%nat ->
  bsum (model_blks (rm_mk cx m si o j0 c O cap out)) + bsum (aentry_blks (rm_ent m j0)) + bsum (asrc_blks h) +
    bsum (aout_blks (lm_cap m) (lm_out m)) =
  bsum (model_blks m) + bsum (slot_blks o) + bsum (aout_blks cap out).
Proof.
  intros cx m si o j0 c O cap out h Hh Hj. unfold model_blks, rm_mk. cbn [lm_G lm_es lm_hs lm_cap lm_out].
  rewrite !bsum_cons, !bsum_app, !rm3_bsum_concat.
  pose proof (fr_sum_perm _ (fun x => bsum (aentry_blks x)) _ _
    (fr_remove_perm _ (lm_es m) j0 relay_remove_b_c.no_entry Hj)) as Pe.
  cbn [map fold_right] in Pe. fold (rm_ent m j0) in Pe.
  pose proof (rm3_set_zsum _ (fun x => bsum (slot_blks x)) si o (Some h) (lm_hs m) (nth_some_error _ _ _ Hh)) as Ps.
  cbn beta in Ps. change (slot_blks (Some h)) with (asrc_blks h) in Ps. lia.
Qed.

(* ================================================================== RINV at the operation's source *)
(* the relay entry j0 and slot si's source h are one pair of fr_relay; its cost is under the input *)
Lemma rm3_pair : forall cx t m si h j0, fr_RINV cx t m -> rm_at cx m si h j0 ->
  fr_pair_ok m t (rm_ent m j0) (h, si) /\ fr_entry_ok (rm_ent m j0) /\
  fr_pair_cost (rm_ent m j0) (h, si) <= c_n cx /\ c_n cx < 2 ^ 26.
Proof.
  intros cx t m si h j0 HRI Hat.
  pose proof HRI as (_ & HR & Hn & _).
  destruct Hat as (_ & _ & _ & _ & Hsi & Hh & Hj0 & Hfd & _).
  destruct HR as (Hlen & Hnd & _ & Hent & hj & HF & _ & Hcl & _ & Hcn).
  destruct (fr_pair_of_open m t hj si h HF Hcl Hsi Hh) as (e & p & Hin & HRp & Hs & Hf).
  destruct p as [p1 p2]. cbn [fst snd] in Hs, Hf. subst p1 p2.
  assert (He : In e (lm_es m)) by (eapply in_combine_l; exact Hin).
  assert (He0 : In (rm_ent m j0) (lm_es m)) by (unfold rm_ent; apply nth_In; exact Hj0).
  assert (Ee : e = rm_ent m j0).
  { apply (rm3_nodup_inj _ _ re_fd (lm_es m)); [apply NoDup_ListNoDup; exact Hnd | exact He | exact He0 |].
    destruct HRp as (_ & _ & Hf' & _). cbn [fst] in Hf'. rewrite <- Hf'. symmetry. exact Hfd. }
  subst e.
  split; [exact HRp|]. split; [rewrite Forall_forall in Hent; exact (Hent _ He0)|].
  split; [|lia].
  eapply Z.le_trans; [|exact Hcn]. unfold fr_cost.
  exact (rm3_in_le_sum _ (fun q => fr_pair_cost (fst q) (snd q)) _ (rm_ent m j0, (h, si))
    (fun q => fr_pair_cost_nonneg _ _) Hin).
Qed.
Lemma rm3_kt_len : forall ks, 5 * Z.of_nat (length ks) <= gestures_end_b_c.keys_total ks.
Proof. unfold gestures_end_b_c.keys_total. induction ks as [|k ks IH]; cbn [fold_right length]; lia. Qed.

(* ================================================================== LS_rm_rr_pre (_remove.v:1971) *)
(* its first and fourth conjuncts (the sizes drain takes, dr_src_ok, and the meter): no lm_cap bound needed *)
Lemma fr_LS_rm_rr_pre_sizes : forall cx t m ly S si h j0,
  fr_LS B cx t m ly S -> fr_RINV cx t m -> rm_at cx m si h j0 ->
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
(* the two lm_cap conjuncts' bound, from Hcap (a fact fr_LS v2 + fr_RINV lack): with lm_cap m <= 2 ^ 29 (the weakest
   such bound that closes both), lm_cap m < MMAX and four times it fits in fr_LS's 2 ^ 31 to spare (fr_LS_room) *)
Lemma fr_LS_rm_rr_pre_cap : forall cx t m ly S,
  fr_LS B cx t m ly S -> lm_cap m <= 2 ^ 29 ->
  lm_cap m < MMAX /\ blocks_bytes S + 4 * lm_cap m <= LIVE_MAX.
Proof.
  intros cx t m ly S H Hcap. pose proof (fr_LS_room B cx t m ly S H) as Hr.
  assert (HW : WR_MMAX = 1072693248) by reflexivity. unfold ROOM_SPARE in Hr. lia.
Qed.
(* the conjuncts of LS_rm_rr_pre that hold at fr_LS v2 + fr_RINV with Hcap.  The two trace conjuncts are NOT here:
   blocks_bytes S + tr_alloc (rm_rr_tr m h) <= LIVE_MAX is false at states fr_LS v2 + fr_RINV allow (tr_alloc sums
   every request, and drain's seen_tr reallocs the held-key array to (n + 1) * 8 per new begin line), and
   tr_max (rm_rr_tr m h) < MMAX needs t < OPS_MAX (a pending stream of 2 ^ 25 + 1 NUL bytes asks 16 * 2 ^ 26 for the
   expected vector) *)
Lemma fr_LS_rm_rr_pre_part : forall cx t m ly S si h j0,
  fr_LS B cx t m ly S -> fr_RINV cx t m -> rm_at cx m si h j0 ->
  forall (Hcap : lm_cap m <= 2 ^ 29),
  (re_eof (rm_ent m j0) = 0 ->
     Z.of_nat (length (pending_stream h)) < 2 ^ 26 /\ hl_cap (hs_expected h) < 2 ^ 26 /\
     re_nheld (rm_ent m j0) + Z.of_nat (length (pending_stream h)) < 2 ^ 26) /\
  mo_ok MT S (W_LLVMFuzzerTestOneInput_remove.rm_rr_cost MT m h) /\ lm_cap m < MMAX /\
  blocks_bytes S + 4 * lm_cap m <= LIVE_MAX.
Proof.
  intros cx t m ly S si h j0 H HRI Hat Hcap.
  destruct (fr_LS_rm_rr_pre_sizes cx t m ly S si h j0 H HRI Hat) as (A1 & A2).
  destruct (fr_LS_rm_rr_pre_cap cx t m ly S H Hcap) as (A3 & A4).
  exact (conj A1 (conj A2 (conj A3 A4))).
Qed.

(* ================================================================== LS_rm_cnl_pre (_remove.v:2622), PROPOSED text *)
(* The published text ties S to S0 only by mo_le (True at ameter_triv), so blocks_bytes S is free.  Two premises
   are added, each one the arm holds at its check_no_loss call (rm_cnl, _remove.v:3380-3382):
   (P1) the model's blocks have nonnegative sizes at the arm's start: rr_blks_pos (_remove.v:2155, 0 < size, from
        amodel_at) at rm_rr's LS state (ly3, S3, _remove.v:2398), carried with the LS in rm_Q;
   (P2) relay_remove moved only the model's blocks: rr_found's two Permutations over one rest (W_contract.v:1299-1303,
        rr_post :1284), which rm_rr already composes into the same-rest pair it passes rm_sep_step (_remove.v:2384,
        :2474, :2589), carried with the LS in rm_Q.
   The model in (P2) is rm_rr's (c2); the cnl call's model has rm_cev c2 ev1, which has the same blocks.
   No other fact is needed: drain's growth (its lines, their expected records and vector, g_capout after the lines
   and the gesture ends) is bounded by the pair's input cost (fr_relay's fr_cost <= c_n < 2 ^ 26), and fr_LS leaves
   2 ^ 31 to spare. *)
Lemma fr_LS_rm_cnl_pre_p : forall cx t m ly0 S0 (ly : alayout) (S : astate) si h j0 e1 h1 ev LB c2 O2 cap2 out2,
  fr_LS B cx t m ly0 S0 -> fr_RINV cx t m -> rm_at cx m si h j0 -> rm_rr_ok m h j0 e1 h1 ev LB c2 O2 cap2 ->
  mo_le MT S0 S (W_LLVMFuzzerTestOneInput_remove.rm_rr_cost MT m h) ->
  (forall b, In b (model_blks m) -> 0 <= snd b) ->
  (forall rest, Permutation (ablocks B ly0 S0) (input_blks cx ++ model_blks m ++ rest) ->
     Permutation (ablocks B ly S) (input_blks cx ++ model_blks (rm_mk cx m si (Some h1) j0 c2 O2 cap2 out2) ++ rest)) ->
  cnl_room MMAX (blocks_bytes S) (texts (hs_held h1)) (hl_cap (hs_held h1)) (hl_recs (hs_expected h1)) /\
  mo_ok MT S (W_LLVMFuzzerTestOneInput_remove.rm_cnl_cost MT (hs_expected h1) (hs_held h1)).
Proof.
  intros cx t m ly0 S0 ly S si h j0 e1 h1 ev LB c2 O2 cap2 out2 HLS HRI Hat Hrr _ Hpos Hfr.
  split; [|exact I].
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
  (* X: the relay's unfinished line when the relay keeps it (fr_pair_cost's third term) *)
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
  (* sizes the model's blocks give (P1) *)
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
  (* drain's g_nout (RelayCap's drain_ocap_le bounds g_capout by it) *)
  assert (HNF : forall live mx CAP, drain_b_c.ds_no (drain_b_c.drain_fin live mx 0 CAP e h) <= P).
  { intros live mx CAP. pose proof (rm3_no_fin live mx CAP e h HP11) as NF. rewrite EP.
    destruct HEsk as [E|E]; rewrite E in NF.
    - change (0 =? 1) with false in NF. cbv iota in NF. fold U PS in NF. rewrite (HXs E). lia.
    - change (1 =? 1) with true in NF. cbv iota in NF. fold PS in NF. rewrite (HXs1 E). lia. }
  (* relay_remove's growth of the model's blocks, in its two cases *)
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
      (* drain's lines: at most the unfinished line (when kept) and the pending stream *)
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
      (* the keys drain leaves: the old ones and at most one per begin line *)
      assert (Hkt1 : gestures_end_b_c.keys_total (re_keys e1) <= KT + 2 * DT).
      { unfold KT, DT. rewrite !rm3_kt_kw.
        eapply Z.le_trans; [apply (rm3_kw_incl _ (upds (drain_b_c.keys_texts (re_keys e)) (dr_lines h)))|].
        - first [exact (proj1 (NoDup_ListNoDup _) D9) | exact D9].
        - intros y Hy. exact (proj1 (D10 y) Hy).
        - apply rm3_upds_kw. }
      (* g_capout after drain, and the stream it starts the gesture ends from *)
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
      (* the source: its pending records freed, its expected list holding drain's lines *)
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
      (* the expected texts are drain's lines, each begin line at least 21 bytes with its NUL *)
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
  (* the held keys: as many as the relay entry's (fr_pair_ok's same_set, both NoDup), each at least 5 bytes of cost *)
  assert (HNH : 5 * hl_n (hs_held h1) <= KT).
  { rewrite Hheld. unfold hl_n. replace (length (hl_recs (hs_held h))) with (length (texts (hs_held h)))
      by (unfold texts; apply length_map).
    rewrite <- (SlotReads.same_set_length _ _ HEnd HP6 HP5). unfold drain_b_c.keys_texts. rewrite length_map.
    unfold KT. apply rm3_kt_len. }
  (* the live bytes after relay_remove (P2), and fr_LS at the arm's start *)
  destruct HLS as (rest & e0 & HPm & HR & HEr & Hcx & Hl & Hnp & HM).
  pose proof (Hfr rest HPm) as HP1.
  assert (HBS : blocks_bytes S =
                bsum (input_blks cx) + bsum (model_blks (rm_mk cx m si (Some h1) j0 c2 O2 cap2 out2)) + bsum rest)
    by (rewrite (blocks_bytes_bsum B ly S), (bsum_perm _ _ HP1), !bsum_app; lia).
  pose proof (PHI_ge m) as HG. pose proof (nopen_le4 _ Hl) as H4.
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
    unfold MB_K, MB_C, APARTIAL in *. lia.
Qed.

(* ================================================================== LS_rm_step (_remove.v:5460), PROPOSED text *)
(* The published text ties S to S0 only by mo_le.  Added: (P2') the arm's four calls moved only the model's blocks,
   from the LS state's model m to the step's model (the composition of rr_found :1264-1268, cnl_post
   W_check_no_loss.v:398-399, cshe_post W_check_shape_ends.v:176 and sr_post W_contract.v:419, each over one rest:
   the pairs the arm passes rm_sep_step at _remove.v:2589, :3443, :4835, :5365; check_no_loss_read and
   check_shape_done are leaves that keep the blocks), carried with the LS in rm_Q.
   Hout is the one fact fr_LS v2 + fr_RINV lack: the stream buffer's growth over the operation is paid by the
   credit the operation releases (the removed entry's and source's blocks but the partial buffer, the queued and
   held bytes' credit, the vector slack and the input it consumes).  It fails for the relay's unfinished line:
   relay_remove's drain sends re_U (= hs_W, up to LINE_LIMIT bytes) and send_line doubles g_out for it, and PHI
   (ReplyLS.v:102) carries no credit for those bytes. *)
Lemma fr_LS_rm_step_p : forall cx t m ly0 S0 (ly : alayout) (S : astate)
    si h j0 e1 h1 ev LB c2 O2 cap2 out2 E' H' H'' ds cc ev5,
  fr_LS B cx t m ly0 S0 ->
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
  forall (Hout : bsum (aout_blks cap2 out2) - bsum (aout_blks (lm_cap m) (lm_out m)) <=
     bsum (aentry_blks (rm_ent m j0)) + (bsum (asrc_blks h) - APARTIAL) + W_P * slot_pend (Some h) +
     W_H * (slot_held (Some h) + entry_held (rm_ent m j0)) + slot_vsl (Some h) +
     MB_K * (kk cx (rm_mk cx m si None j0 (rm_cev c2 ev5) O2 cap2 out2) - kk cx m)),
  fr_LS B cx (t + 1) (rm_mk cx m si None j0 (rm_cev c2 ev5) O2 cap2 out2) ly S.
Proof.
  intros cx t m ly0 S0 ly S si h j0 e1 h1 ev LB c2 O2 cap2 out2 E' H' H'' ds cc ev5 HLS _ _ Hat _ _ _ Hfr Hout.
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
  pose proof (Zs slot_npend) as Z4. pose proof (Zs slot_open) as Z5. pose proof (Ze entry_held) as Z6.
  assert (N1 : slot_pend None = 0) by reflexivity. assert (N2 : slot_held None = 0) by reflexivity.
  assert (N3 : slot_vsl None = 0) by reflexivity. assert (N4 : slot_npend None = 0) by reflexivity.
  assert (N5 : slot_open None = 0) by reflexivity. assert (P5 : slot_open (Some h) = 1) by reflexivity.
  pose proof (slot_npend_nonneg (Some h)) as Hsn.
  assert (Eb : lm_es m' = relay_remove_b_c.remove_at j0 (lm_es m)) by reflexivity.
  split.
  - unfold npend in *. lia.
  - unfold PHI, pend_bytes, held_bytes, vslack in *. rewrite !nopen_zsum in *.
    unfold MB_K, MB_C, W_P, W_H, APARTIAL in *. lia.
Qed.
End rm3.
