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

From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation FunctionalExtensionality.
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
HarnessRep RelayRep CheckRep RelayKeys RelayModel.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require RelayRunT drain_b_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Lib Require Mem.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import W_rep W_contract W_sites W_frame.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import W_LLVMFuzzerTestOneInput_cut.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YCbqG.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import
W_kit_x W_journal_x W_contract_x W_sites_x W_frame_x.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import W_LLVMFuzzerTestOneInput_cut_x.
(* route R (Section drxR below): drain's and check_no_loss's contract texts at R, Required and named qualified, so no
   name of theirs shadows one this file cites; the step relation SRrG and its lemmas *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require W_contract_xR W_contract_xR_g6.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YA0nH.
(* the room round: the live counts (ReplyCnt.acnt), Required and named qualified.  A Theorem Labs lane's texts this arm
   takes (LS_cnt's guard msz_ok of ReplyLSCntM.v, the step rules' bundles of ReplyLSDrain3.v / ReplyLS3Arms.v) are
   restated below (msz_ok, dr3_epre ..), and check_no_loss's peak after the drain is the parameter dr_cnl_pk: those
   files and ReplyLScnt.v Require the AR head / small / write / add / event arms, which this arm does not need *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require ReplyCnt.
(* LAST, so the names this file cites from _drain.v are not shadowed by a kit file's *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import W_LLVMFuzzerTestOneInput_drain.

Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.


(* ---- the AR-reading part of _drain.v Section dr_kit, over ARx ---- *)
Section dr_kitx.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Notation segs := (@pa_segs _ fr_prog_listing PB_fr).
Variable B : asyms.
Variable ARx : alayout -> astate -> list Z -> world segs -> (word -> option byte) -> Model -> Prop.
Context {hl : Z}.
Hypothesis LAWS : AR_laws_x segs B ARx hl.
(* a live block's request is in [0, 2 ^ 30) (see the file header) *)
Hypothesis BLKR : forall ly S Hp (W : world segs) mem md p n, ARx ly S Hp W mem md -> In (p, n) (ablocks B ly S) ->
  0 <= n < 2 ^ 30.

(* a bound on a range of fuzz_reply.asan's globals, or on errno from the premises *)
(* copied from W_LLVMFuzzerTestOneInput_latch.v lt_low *)
Ltac dr_low :=
  cbn [fst snd gfp]; unfold DR_CEIL8 in *;
  cbn [fr_globals rg_s rg_src rg_nsrc rg_capsrc rg_out rg_nout rg_capout rg_send_max rg_send_eintr
       rg_send_dead rg_gone rg_client rg_client_broken rg_lock rg_wake] in *;
  pose proof dr_ceil_lo; lia.

(* a live block: its bytes, and the 7 bytes of alignment slack a key's text may carry past them *)
(* copied from W_LLVMFuzzerTestOneInput_latch.v lt_blk *)
Lemma dr_blk : forall ly S Hp (W : world segs) mem md p n,
  ARx ly S Hp W mem md -> In (p, n) (ablocks B ly S) ->
  4096 <= p /\ p + req_size n <= alloc_ceiling /\ 0 <= n <= req_size n.
Proof.
  intros ly S Hp W mem md p n HAR Hin.
  destruct (alx_blocks _ _ _ LAWS ly S Hp W mem md p n HAR Hin) as (_ & H1 & H2 & _ & _ & _); pose proof (BLKR ly S Hp W mem md p n HAR Hin) as H3.
  pose proof (req_size_pos n ltac:(lia)) as [Hr1 Hr2]. split; [lia|]. split; [lia | lia].
Qed.

(* ---- struct list ---- *)
(* copied from W_LLVMFuzzerTestOneInput_latch.v lt_alist *)
Lemma dr_alist : forall ly S Hp (W : world segs) mem md LA l lines,
  ARx ly S Hp W mem md -> alist_at B ly S W mem LA l lines -> 0 <= LA -> LA + 16 <= DR_CEIL8 ->
  dr_fp_low (alist_fp LA l) /\ (forall b, In b (alist_blks l) -> In b (ablocks B ly S)).
Proof.
  intros ly S Hp W mem md LA l lines HAR (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9) HL0 HL1.
  assert (HREC : dr_fp_low (map (fun r => gfp (fst r) (bzs (snd r ++ [Z_to_bv 8 0]))) (hl_recs l))
                 /\ (forall b, In b (map (fun r => (fst r, Z.of_nat (length (snd r)) + 1)) (hl_recs l)) ->
                       In b (ablocks B ly S))).
  { rewrite Forall_forall in H9. split.
    - rewrite dr_fp_low_forall. intros r Hr. apply in_map_iff in Hr as (x & <- & Hx).
      destruct (H9 x Hx) as (K1 & _). destruct (dr_blk ly S Hp W mem md _ _ HAR K1) as (P1 & P2 & P3).
      cbn [gfp fst snd]. rewrite dr_bzs_len, length_app. cbn [length].
      unfold DR_CEIL8 in *. split; [lia | lia].
    - intros b Hb. apply in_map_iff in Hb as (x & <- & Hx). exact (proj1 (H9 x Hx)). }
  destruct HREC as [HR1 HR2].
  unfold alist_fp, alist_blks. split.
  - apply dr_fp_low_cons; [cbn; lia | cbn; lia|]. apply dr_fp_low_app; [|exact HR1].
    destruct (Z.eqb_spec (hl_cap l) 0) as [Hc|Hc]; [apply dr_fp_low_nil|].
    destruct H6 as [[Hc0 _] | (Hcp & Hin & Hj & Hg)]; [lia|].
    destruct (dr_blk ly S Hp W mem md _ _ HAR Hin) as (P1 & P2 & P3).
    apply dr_fp_low_cons; [cbn; lia | | apply dr_fp_low_nil].
    cbn [gfp fst snd]. rewrite dr_bzs_len, length_app, dr_concat_len.
    unfold hl_n in Hj. unfold AREC in *. unfold DR_CEIL8 in *. lia.
  - intros b Hb. apply in_app_or in Hb as [Hb | Hb]; [|exact (HR2 b Hb)].
    destruct (Z.eqb_spec (hl_cap l) 0) as [Hc|Hc]; [destruct Hb|].
    destruct H6 as [[Hc0 _] | (Hcp & Hin & _)]; [lia|].
    destruct Hb as [<- | []]. exact Hin.
Qed.

(* ---- struct source ---- *)
(* copied from W_LLVMFuzzerTestOneInput_latch.v lt_asrc *)
Lemma dr_asrc : forall ly S Hp (W : world segs) mem md HA h,
  ARx ly S Hp W mem md -> asrc_at B ly S W mem HA h -> 0 <= HA -> HA + ASRC <= DR_CEIL8 ->
  dr_fp_low (asrc_fp HA h) /\ (forall b, In b (asrc_blks h) -> In b (ablocks B ly S)).
Proof.
  intros ly S Hp W mem md HA h HAR HS HL0 HL1.
  pose proof HS as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Hpend & _ & _ & _ & _ & _ & _ & _ & Hpb & Hpj & _ &
                    _ & Hexp & Hheld & _).
  destruct (dr_alist ly S Hp W mem md (HA + 16) (hs_pending h) false HAR Hpend ltac:(unfold ASRC in *; lia)
                     ltac:(unfold ASRC in *; lia)) as [A1 A2].
  destruct (dr_alist ly S Hp W mem md (HA + 64) (hs_expected h) true HAR Hexp ltac:(unfold ASRC in *; lia)
                     ltac:(unfold ASRC in *; lia)) as [E1 E2].
  destruct (dr_alist ly S Hp W mem md (HA + 80) (hs_held h) true HAR Hheld ltac:(unfold ASRC in *; lia)
                     ltac:(unfold ASRC in *; lia)) as [H1 H2].
  destruct (dr_blk ly S Hp W mem md _ _ HAR Hpb) as (P1 & P2 & P3).
  unfold asrc_fp, asrc_blks. split.
  - apply dr_fp_low_cons; [cbn; lia | cbn; unfold ASRC in *; lia|].
    apply dr_fp_low_cons.
    + cbn [gfp fst]. lia.
    + cbn [gfp snd]. rewrite dr_bzs_len, Hpj. unfold APARTIAL, DR_CEIL8 in *. lia.
    + apply dr_fp_low_app; [exact A1|]. apply dr_fp_low_app; [exact E1 | exact H1].
  - intros b [<- | Hb]; [exact Hpb|].
    apply in_app_or in Hb as [Hb | Hb]; [exact (A2 b Hb)|].
    apply in_app_or in Hb as [Hb | Hb]; [exact (E2 b Hb) | exact (H2 b Hb)].
Qed.

(* ---- one source_t of the relay's table ---- *)
(* copied from W_LLVMFuzzerTestOneInput_latch.v lt_aentry *)
Lemma dr_aentry : forall ly S Hp (W : world segs) mem md e,
  ARx ly S Hp W mem md -> aentry_ok B ly S W mem e ->
  dr_fp_low (aentry_fp e) /\ (forall b, In b (aentry_blks e) -> In b (ablocks B ly S)).
Proof.
  intros ly S Hp W mem md e HAR (K1 & K2 & K3 & K4 & K5 & K6 & K7 & K8 & K9 & K10 & K11 & K12 & K13 & K14 & K15).
  assert (HK : dr_fp_low (map (fun k => gfp (gestures_end_b_c.key_addr k)
                  (bzs (gestures_end_b_c.key_text k ++ [Z_to_bv 8 0]))) (re_keys e))
               /\ (forall b, In b (map (fun k => (gestures_end_b_c.key_addr k,
                     Z.of_nat (length (gestures_end_b_c.key_text k)) + 1)) (re_keys e)) ->
                     In b (ablocks B ly S))).
  { rewrite Forall_forall in K15. split.
    - rewrite dr_fp_low_forall. intros r Hr. apply in_map_iff in Hr as (k & <- & Hk).
      destruct (K15 k Hk) as (M1 & _).
      destruct (dr_blk ly S Hp W mem md _ _ HAR M1) as (P1 & P2 & P3).
      cbn [gfp fst snd]. rewrite dr_bzs_len, length_app. cbn [length].
      unfold DR_CEIL8 in *. split; [lia | lia].
    - intros b Hb. apply in_map_iff in Hb as (k & <- & Hk). exact (proj1 (K15 k Hk)). }
  destruct HK as [HK1 HK2]. unfold aentry_fp, aentry_blks. split.
  - apply dr_fp_low_app.
    + destruct (Z.eqb_spec (re_cap e) 0) as [Hc|Hc]; [apply dr_fp_low_nil|].
      destruct K10 as [(Hc0 & _) | (Hcp & Hin & Hj & Hg)]; [lia|].
      destruct (dr_blk ly S Hp W mem md _ _ HAR Hin) as (P1 & P2 & P3).
      apply dr_fp_low_cons; [cbn; lia | | apply dr_fp_low_nil].
      cbn [gfp snd]. rewrite dr_bzs_len, length_app. unfold DR_CEIL8 in *. lia.
    + apply dr_fp_low_cons; [| |exact HK1].
      * cbn [gfp fst]. destruct K12 as [(Hz & _) | (Hz & Hin & _)]; [lia|].
        destruct (dr_blk ly S Hp W mem md _ _ HAR Hin) as (P1 & _). lia.
      * cbn [gfp snd]. rewrite dr_bzs_len, dr_key_ptrs_len.
        destruct K12 as [(Hz & Hks) | (Hz & Hin & Hk1 & Hk2 & Hg)].
        { rewrite Hz, Hks. cbn [length]. unfold DR_CEIL8. pose proof dr_ceil_lo. lia. }
        destruct (dr_blk ly S Hp W mem md _ _ HAR Hin) as (P1 & P2 & P3).
        unfold re_nheld in Hk1. unfold DR_CEIL8 in *. lia.
  - intros b Hb. apply in_app_or in Hb as [Hb | Hb].
    + destruct (Z.eqb_spec (re_cap e) 0) as [Hc|Hc]; [destruct Hb|].
      destruct K10 as [(Hc0 & _) | (Hcp & Hin & _)]; [lia|]. destruct Hb as [<- | []]. exact Hin.
    + apply in_app_or in Hb as [Hb | Hb]; [|exact (HK2 b Hb)].
      destruct (Z.eqb_spec (re_hp e) 0) as [Hz|Hz]; [destruct Hb|].
      destruct K12 as [(Hz0 & _) | (_ & Hin & _)]; [lia|]. destruct Hb as [<- | []]. exact Hin.
Qed.

(* ---- the relay's table, at fuzz_reply.asan's globals ---- *)
(* copied from W_LLVMFuzzerTestOneInput_latch.v lt_arelay *)
Lemma dr_arelay : forall ly S Hp (W : world segs) mem md G es,
  ARx ly S Hp W mem md -> arelay_at B fr_globals ly S W mem G es ->
  dr_fp_low (arelay_fp fr_globals G es) /\ (forall b, In b (arelay_blks G es) -> In b (ablocks B ly S)).
Proof.
  intros ly S Hp W mem md G es HAR (R1 & R2 & R3 & R4 & R5 & R6 & R7 & R8 & R9 & R10 & R11).
  destruct (dr_blk ly S Hp W mem md _ _ HAR R8) as (P1 & P2 & P3).
  assert (HE : dr_fp_low (concat (map aentry_fp es))
               /\ (forall b, In b (concat (map aentry_blks es)) -> In b (ablocks B ly S))).
  { rewrite Forall_forall in R10. split.
    - rewrite dr_fp_low_forall. intros r Hr. apply in_concat in Hr as (f & Hf & Hr).
      apply in_map_iff in Hf as (e & <- & He).
      destruct (dr_aentry ly S Hp W mem md e HAR (R10 e He)) as [F1 _].
      rewrite dr_fp_low_forall in F1. exact (F1 r Hr).
    - intros b Hb. apply in_concat in Hb as (f & Hf & Hb). apply in_map_iff in Hf as (e & <- & He).
      destruct (dr_aentry ly S Hp W mem md e HAR (R10 e He)) as [_ F2]. exact (F2 b Hb). }
  destruct HE as [HE1 HE2]. unfold arelay_fp, arelay_blks. split.
  - apply dr_fp_low_cons; [dr_low | dr_low|].
    apply dr_fp_low_cons; [dr_low | dr_low|].
    apply dr_fp_low_cons; [dr_low | dr_low|].
    apply dr_fp_low_cons; [cbn; lia | cbn [fst snd]; unfold ATABLE, DR_CEIL8 in *; lia | exact HE1].
  - intros b [<- | Hb]; [exact R8 | exact (HE2 b Hb)].
Qed.

(* ---- the controller's stream ---- *)
(* copied from W_LLVMFuzzerTestOneInput_latch.v lt_aout *)
Lemma dr_aout : forall ly S Hp (W : world segs) mem md c O mx no cap out,
  ARx ly S Hp W mem md -> aout_at B fr_globals ly S W mem c O mx no cap out ->
  0 <= as_errno B -> as_errno B + 4 <= DR_CEIL8 ->
  dr_fp_low (aout_fp B fr_globals cap out) /\ (forall b, In b (aout_blks cap out) -> In b (ablocks B ly S)).
Proof.
  intros ly S Hp W mem md c O mx no cap out HAR HO HE0 HE1.
  pose proof HO as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
                    _ & Hblk).
  unfold aout_fp, aout_blks. split.
  - do 9 (apply dr_fp_low_cons; [dr_low | dr_low|]).
    destruct (Z.eqb_spec cap 0) as [Hc|Hc]; [apply dr_fp_low_nil|].
    destruct Hblk as [(Hc0 & _) | (Hcp & Hno & Hin & junk & Hj & Hg)]; [lia|].
    destruct (dr_blk ly S Hp W mem md _ _ HAR Hin) as (P1 & P2 & P3).
    apply dr_fp_low_cons; [cbn; lia | cbn; unfold DR_CEIL8 in *; lia | apply dr_fp_low_nil].
  - intros b Hb. destruct (Z.eqb_spec cap 0) as [Hc|Hc]; [destruct Hb|].
    destruct Hblk as [(Hc0 & _) | (Hcp & Hno & Hin & _)]; [lia|]. destruct Hb as [<- | []]. exact Hin.
Qed.
End dr_kitx.

(* ---- the step rules' bundles, a Theorem Labs lane's texts restated word for word (the top's TX_LS_drain_step /
   TX_LS_cnl_pre name the originals, which unfold to these): dr3_epre / dr3_hpre / dr3_epost / dr3_hpost are
   lib/A/ReplyLSDrain3.v:78-98, ls3_kh / ls3_hn / ls3_dpost / ls3_cpost are lib/A/ReplyLS3Arms.v:306-328, at meet
   393c0b2cb2a ---- *)
(* LS_cnt's guard, lib/A/ReplyLSCntM.v:47-52: the model's sizes (amodel_at gives them, dr_msz_x) *)
Definition texts_ok (l : hlist) : Prop := Forall (fun r => Z.of_nat (length (snd r)) <= APARTIAL) (hl_recs l).
Definition msz_ok (m : lmod) : Prop :=
  Forall (fun e => 0 <= re_cap e <= 16384 /\
    Forall (fun k => Z.of_nat (length (gestures_end_b_c.key_text k)) <= APARTIAL) (re_keys e)) (lm_es m) /\
  Forall (fun o => match o with Some h => texts_ok (hs_expected h) /\ texts_ok (hs_held h) | None => True end)
    (lm_hs m).
(* aentry_ok's clauses at the drain call: the re_cap clause W_rep.v:124, |re_U| = re_used <= APARTIAL and no NUL in
   re_U :125, the held array's 8 <= re_kh :131-132, the keys' 14 <= |text| :139 *)
Definition dr3_epre (e : rentry) : Prop :=
  (re_cap e = 0 \/ re_cap e = 8192 \/ re_cap e = 16384) /\
  Z.of_nat (length (re_U e)) <= APARTIAL /\ ~ In (Z_to_bv 8 0) (re_U e) /\
  (re_hp e <> 0 -> 8 <= re_kh e) /\
  Forall (fun k => 14 <= Z.of_nat (length (gestures_end_b_c.key_text k))) (re_keys e).
(* asrc_at's pending list at the drain call: its offset clause (W_rep.v:104-105) and its texts' non-emptiness
   (alist_at (HA + 16) (hs_pending h) false, W_rep.v:91) *)
Definition dr3_hpre (h : hsrc) : Prop :=
  ((hl_recs (hs_pending h) = [] /\ hs_off h = 0) \/
   (exists r rs, hl_recs (hs_pending h) = r :: rs /\ 0 <= hs_off h < Z.of_nat (length (snd r)))) /\
  Forall (fun r => (1 <= length (snd r))%nat) (hl_recs (hs_pending h)).
(* dr_post's clauses on the entry it leaves: aentry_ok e' (W_rep.v:124), the held array, the keys *)
Definition dr3_epost (e e' : rentry) (h : hsrc) : Prop :=
  (re_cap e' = 0 \/ re_cap e' = 8192 \/ re_cap e' = 16384) /\
  ((re_hp e' = re_hp e /\ re_kh e' = re_kh e) \/ re_kh e' <= 2 ^ 30) /\
  NoDup (drain_b_c.keys_texts (re_keys e')) /\
  same_set (drain_b_c.keys_texts (re_keys e')) (upds (drain_b_c.keys_texts (re_keys e)) (dr_lines h)).
(* dr_post's clauses on the source it leaves: the pending list emptied, its capacity, the expected list's capacity *)
Definition dr3_hpost (h h' : hsrc) : Prop :=
  hl_recs (hs_pending h') = [] /\ hl_cap (hs_pending h') = hl_cap (hs_pending h) /\
  hl_cap (hs_expected h') <= Z.max 8 (Z.max (hl_cap (hs_expected h)) (2 * hl_n (hs_expected h'))).
(* aentry_ok's held-array clause, W_rep.v:131-132 *)
Definition ls3_kh (e : rentry) : Prop :=
  (re_hp e = 0 /\ re_keys e = []) \/ (re_hp e <> 0 /\ 8 * re_nheld e <= re_kh e).
(* alist_at's count clause, W_rep.v:81, of the source's three lists *)
Definition ls3_hn (h : hsrc) : Prop :=
  hl_n (hs_pending h) <= hl_cap (hs_pending h) /\ hl_n (hs_expected h) <= hl_cap (hs_expected h) /\
  hl_n (hs_held h) <= hl_cap (hs_held h).
(* dr_post's clauses: the unfinished line, the key array, the read offset, the expected texts, the held list, and
   asrc_at h' (alist_at :81 of its expected list) *)
Definition ls3_dpost (m : lmod) (j : nat) (h : hsrc) (e' : rentry) (h1 : hsrc) : Prop :=
  let fin := dr_fin (lm_c m) (lm_mx m) (Z.of_nat (length (lm_O m))) (lm_cap m) (nth j (lm_es m) dr_e0) h in
  bzs (re_U e') = drain_b_c.ds_u fin /\ drain_b_c.ent_ka e' = drain_b_c.ds_ka fin /\
  hs_off h1 = 0 /\
  map snd (hl_recs (hs_expected h1)) = map snd (hl_recs (hs_expected h)) ++ map (map (Z_to_bv 8)) (dr_lines h) /\
  hs_held h1 = hs_held h /\ hl_n (hs_expected h1) <= hl_cap (hs_expected h1).
(* cnl_post's clauses (dr_cfun) and its asrc_at (set_exp_held h1 E' H') (alist_at W_rep.v:81 of the held list) *)
Definition ls3_cpost (h1 : hsrc) (E' H' : hlist) : Prop :=
  hl_recs E' = [] /\ hl_cap E' = hl_cap (hs_expected h1) /\
  NoDup (texts H') /\ texts H' = RelayModel.upds (texts (hs_held h1)) (texts (hs_expected h1)) /\
  hl_cap H' <= Z.max 8 (Z.max (hl_cap (hs_held h1))
                             (2 * (hl_n (hs_held h1) + Z.of_nat (count_begin (texts (hs_expected h1)))))) /\
  hl_n H' <= hl_cap H'.

Section drx.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
#[local] Notation segs := (@pa_segs _ fr_prog_listing PB_fr).
#[local] Notation VAL := (@pa_val _ fr_prog_listing PB_fr).
#[local] Notation SIGMA := (@pa_sigma _ fr_prog_listing PB_fr).
#[local] Notation BASE := (@pa_val _ fr_prog_listing PB_fr A_TEXT).
(* ---- cut_x's Section w (W_LLVMFuzzerTestOneInput_cut_x.v:191-235), verbatim ---- *)
Variable B : asyms.
Variable MT : ameter_ops.
Variables XM_LIB XN_LIB : Z -> Z.
Variables RLO RHI : Z.
Variable fr_live_pre : astate -> Prop.
Variable fr_live_post : astate -> astate -> Z -> Prop.
Variable fr_surv : alayout -> astate -> world segs -> (word -> option byte) -> alayout -> astate -> world segs ->
  (word -> option byte) -> Prop.
Variable LIBROOM NP : astate -> Prop.
Variable G_fr : list (Z * Z).
Variable fr_FP : bvmap 5 word -> alayout -> astate -> world segs -> (word -> option byte) -> list (Z * Z).
Variable PST : list (Z * Z).
Variable ARx : alayout -> astate -> list Z -> world segs -> (word -> option byte) -> Model -> Prop.
Context {hl : Z}.
Hypothesis LAWS : AR_laws_x segs B ARx hl.
Hypothesis HP0 : forall ly S Hp (W : world segs) mem md, ARx ly S Hp W mem md -> Hp = [].
Hypothesis HG : gx_ok segs B G_fr.
Variable LSx : lfcx -> Z -> lmod -> alayout -> astate -> Prop.
Variable RINV : lfcx -> Z -> lmod -> Prop.


(* ------------------------------------------------------------------ the arm's register predicates *)
(* every state inside the arm keeps the loop's registers and the operation's number *)
Definition lregs_base (cx : lfcx) (t : Z) (FF : Z) (regs : bvmap 5 word) : Prop :=
  lregs_common B cx FF regs /\ getr regs 27 = w64 t /\ 0 <= t < OPS_MAX.
(* 0x84550, the table scan's head: a0 = s6 = &g_src[i], a1 = entries left, a2 = s->fd, a3 = its shadow;
   n is the trip count the induction runs on *)
Definition lregs_scan (cx : lfcx) (t : Z) (n : nat) (i : Z) (m : lmod) (FF : Z)
  (regs : bvmap 5 word) (W : world segs) (mem : word -> option byte) : Prop :=
  lregs_base cx t FF regs /\ dr_at_op cx m /\
  getr regs 28 = w64 (c_p cx + dr_k' cx m) /\
  sv8 W mem (lf_F cx + DR_N) (c_n cx - dr_k' cx m) /\
  (exists si h, dr_pick cx m si h /\
     getr regs 21 = w64 (rg_s fr_RG + ASRC * Z.of_nat si) /\
     getr regs 12 = w64 (hs_fd h) /\ dr_nomatch m h i) /\
  0 <= i < Z.of_nat (length (lm_es m)) /\ Z.of_nat n = Z.of_nat (length (lm_es m)) - i /\
  getr regs 10 = w64 (lm_G m + AENT * i) /\ getr regs 22 = w64 (lm_G m + AENT * i) /\
  getr regs 11 = w64 (Z.of_nat (length (lm_es m)) - i) /\
  getr regs 13 = w64 (SB + lm_G m / 8 + 7 * i).
(* 0x846c8, no entry carries the source's fd *)
Definition lregs_nf (cx : lfcx) (t : Z) (m : lmod) (FF : Z)
  (regs : bvmap 5 word) (W : world segs) (mem : word -> option byte) : Prop :=
  lregs_base cx t FF regs /\ dr_at_op cx m /\
  getr regs 28 = w64 (c_p cx + dr_k' cx m) /\
  sv8 W mem (lf_F cx + DR_N) (c_n cx - dr_k' cx m) /\
  (exists si h, dr_pick cx m si h /\ dr_nomatch m h (Z.of_nat (length (lm_es m)))).
(* 0x84a20, the entry at index j carries the source's fd *)
Definition lregs_found (cx : lfcx) (t : Z) (j : nat) (m : lmod) (FF : Z)
  (regs : bvmap 5 word) (W : world segs) (mem : word -> option byte) : Prop :=
  lregs_base cx t FF regs /\ dr_at_op cx m /\
  getr regs 28 = w64 (c_p cx + dr_k' cx m) /\
  sv8 W mem (lf_F cx + DR_N) (c_n cx - dr_k' cx m) /\
  (exists si h, dr_pick cx m si h /\
     getr regs 21 = w64 (rg_s fr_RG + ASRC * Z.of_nat si) /\
     re_fd (nth j (lm_es m) dr_e0) = hs_fd h /\ dr_nomatch m h (Z.of_nat j)) /\
  (j < length (lm_es m))%nat /\
  getr regs 10 = w64 (lm_G m + AENT * Z.of_nat j) /\ getr regs 22 = w64 (lm_G m + AENT * Z.of_nat j).
(* 0x84a80, the arm's join: s9 carries the new in.p, s6 is about to take it, F+144 the new in.n;
   this is lregs_K's content with s9 not yet restored from F+104 *)
Definition lregs_join (cx : lfcx) (t : Z) (m : lmod) (FF : Z)
  (regs : bvmap 5 word) (W : world segs) (mem : word -> option byte) : Prop :=
  getr regs 2 = w64 (lf_F cx) /\ getr regs 8 = getr (c_regs cx) 2 /\ getr regs 9 = w64 (lf_F cx) /\
  getr regs 18 = w64 HI_G_SRC /\ getr regs 19 = w64 (FF + 32) /\ getr regs 20 = w64 10 /\
  getr regs 23 = w64 HI_G_NSRC /\ getr regs 24 = w64 (SB + FF / 8) /\
  getr regs 26 = w64 SB /\ getr regs 3 = w64 (as_gp B) /\ getr regs 4 = w64 (as_tp B) /\
  getr regs 27 = w64 t /\ 0 <= t < OPS_MAX /\
  getr regs 25 = w64 (c_p cx + lm_k m) /\
  sv8 W mem (lf_F cx + DR_N) (c_n cx - lm_k m) /\ 0 <= lm_k m <= c_n cx.


(* a state of the arm: a pc, the journal and the model of lcut, and a register predicate *)
Definition DST (pc : Z) (cx : lfcx) (Hpe : list Z) (t : Z)
  (R : lmod -> Z -> bvmap 5 word -> world segs -> (word -> option byte) -> Prop)
  : world segs -> config -> Prop :=
  fun W c => exists regs mem md, c = cfg_at segs (fr_B0 + pc) regs mem md /\
    jt_rom W mem /\ lcut_x B NP G_fr fr_FP PST ARx LSx RINV cx Hpe t true R regs mem md W.

(* ------------------------------------------------------------------ what the other lanes owe *)
Variable MMAX : Z.                                  (* W7's request bound, dr_spec's parameter *)
Hypothesis TL : PALib B.                            (* the allocator instance (W_kit.v) *)
(* the room round (ROOM-TEXTS.md (sha256 767baa12f13c; internal record) (a), (d)): drain's and check_no_loss's room record RP, at RM := the cut's
   NP (the cf instance: rp_RM := fun S _ => room_live_cf S = NP, so RP_NP is iff_refl) *)
Variable RP : roomp.
Hypothesis RP_NP : forall S k, rp_RM RP S k <-> NP S.
(* W7, lib/A/W_contract.v, verbatim *)
Hypothesis DRAIN : dr_spec_x B PST ARx MT RP MMAX fr_RG (BASE + AF_fr_drain).
(* W6's W_sites.v forms, proved by R5 (a working branch b1c048a98a5) *)
Hypothesis ALOCK : alock_realizes_x B ARx (SIGMA WS_pthread_mutex_lock).
Hypothesis AUNLOCK : aunlock_realizes_x B ARx (SIGMA WS_pthread_mutex_unlock).
(* proved: lib/A/W_check_shape_done.v pb_check_shape_done *)
Hypothesis CSD : csd_spec_x B PST ARx (BASE + AF_fr_check_shape_done).
(* W_contract.v's cnlr_spec (W3's restated check_no_loss_read), verbatim: proved on this base by
   lib/A/W_check_no_loss_read.v:250 pb_check_no_loss_read (Qed). *)
Hypothesis CNLR : cnlr_spec_x B PST ARx (BASE + AF_fr_check_no_loss_read).
(* check_no_loss: W3's cnl_spec (lib/A/W_contract.v Section w3n), at every G its proof takes:
   the G-dependent Section hypotheses of pb_check_no_loss are gx_ok SEGS B G and gx_rt B G (W_check_no_loss.v
   Section c).  The call site takes it at the slot's two list headers G = [(HA + 64, 32)]: a G covering the other
   three slots would let the callee change their bytes, and the other slots' asrc_at could not be carried. *)
Hypothesis CNL : forall G, gx_ok segs B G -> gx_rt B G -> cnl_spec_x B PST ARx MT RP G MMAX (BASE + AF_fr_check_no_loss).

(* ---- the G-coverage facts: every global a callee writes is one of the entry's G_fr ---- *)
Hypothesis HGs : forall a, rg_s fr_RG <= a < rg_s fr_RG + 4 * ASRC -> inG G_fr a.
Hypothesis HG_DR : forall a, inG (G_DR B fr_RG) a -> inG G_fr a.
Hypothesis HGlock : forall a, rg_lock fr_RG <= a < rg_lock fr_RG + 12 -> inG G_fr a.
Hypothesis HG_GK : forall a, inG DR_GK a -> inG G_fr a.
(* errno's cell (tp - 164, musl's static TLS: 0x5d93cc on image A) lies above every program global amodel_at
   names (g_out, the highest, ends at 0x5d8b48) *)
Hypothesis HERR_HI : rg_out fr_RG + 8 <= as_errno B.
(* _cut's errno_law, verbatim: errno's cell is readable and writable in every AR state.  check_no_loss_read,
   check_no_loss and check_shape_done keep no errno byte (their journals exclude it), so the stream's errno value
   is re-read after them *)
Hypothesis ERR : errno_law_x B ARx.
(* W_journal.v's rom_out at G_fr (a working branch 45a3cc9bdd0's text): ROM is outside G_fr, errno and the
   sink's overflow head, and an owned ROM byte is pinned; so rom_view survives every callee's journal *)
Hypothesis DR_ROM_OUT : rom_out segs B G_fr.
(* _cut's glob_wr_law at G_fr, verbatim: a byte of G_fr is writable in every memory (so a kept view keeps it
   writable) *)
Hypothesis GWR : glob_wr_law G_fr.
(* g_s and the relay's buffers lie in the instance's zero-shadow ranges (globals of the image) *)
Hypothesis HZS : azs B (rg_s fr_RG) (4 * ASRC).
(* the image objects this arm reads are apart; vm_compute at PB_fr *)
Hypothesis HAP : (rg_s fr_RG + 4 * ASRC <= VAL (A_OBJ 0) \/ VAL (A_OBJ 0) + 8 <= rg_s fr_RG) /\
                 (rg_s fr_RG + 4 * ASRC <= VAL (A_OBJ 32) \/ VAL (A_OBJ 32) + 8 <= rg_s fr_RG).
(* ---- the image is off PST (W_op_add.v Section x's HPST): a callee's journal keeps every image byte outside
   the callee's own G, and ROM.  At the instance's PST := [] it holds trivially. ---- *)
Hypothesis HPST : forall a, in_img segs a -> ~ Exists (in_zr a) PST.
(* ---- a live block's request is in [0, 2 ^ 30) (see the file header) ---- *)
Hypothesis BLKR : forall ly S Hp (W : world segs) mem md p n, ARx ly S Hp W mem md -> In (p, n) (ablocks B ly S) ->
  0 <= n < 2 ^ 30.
(* ROM is image, so off PST (W_op_add.v oa_pstr) *)
Lemma dr_pstr : forall a, in_rom segs a -> ~ Exists (in_zr a) PST.
Proof. intros a (sg & Hin & _ & Hr). apply HPST. exists sg. split; [exact Hin | exact Hr]. Qed.


(* ---- the arm's open model obligations (pure, over lmod and the plain records) ---- *)
(* the operation did nothing: the relay has no entry for the source's fd, or its entry is at end of file *)
Hypothesis RI_drain_skip : forall cx t m si h,
  RINV cx t m -> dr_at_op cx m -> dr_pick cx m si h ->
  (dr_nomatch m h (Z.of_nat (length (lm_es m))) \/
   (exists j, (j < length (lm_es m))%nat /\ re_fd (nth j (lm_es m) dr_e0) = hs_fd h /\
      re_eof (nth j (lm_es m) dr_e0) = 1)) ->
  RINV cx (t + 1) (dr_skip m (dr_k' cx m)).
Hypothesis RI_drain_step : forall cx t m si h j e' h' c' O' cap' out' ev' LB E' H',
  RINV cx t m -> 0 <= t < OPS_MAX ->
  hl_n (hs_held h') + Z.of_nat (count_begin (texts (hs_expected h'))) < 2 ^ 22 ->
  dr_at_op cx m -> dr_pick cx m si h ->
  (j < length (lm_es m))%nat -> re_fd (nth j (lm_es m) dr_e0) = hs_fd h ->
  re_eof (nth j (lm_es m) dr_e0) = 0 ->
  dr_step_ok cx m si h j e' h' c' O' cap' out' ev' LB E' H' ->
  RINV cx (t + 1) (dr_step m (dr_k' cx m) si (set_exp_held h' E' H') j e' c' O' cap' out').
(* ---- the drain's count growth (the room round's count rule).  check_no_loss's count premise is at the state the
   drain leaves; LS_cnt bounds the counts at the cut.  dr_post's two Permutations (W_contract_x.v dr_post_x) make the
   change of every count the change over the drained entry's, source's and g_out's blocks, with the same rest; this
   rule says that change is at most the drain trace's count peak, for every count predicate P.  A PURE MODEL rule
   (no astate; W8Entry-2's 04:20Z pattern, as the gone arm's GN_CNT_step), with the premises the walk holds at the
   drain's return (dc_stB): the cut's model facts at the call (dc_static, LS_cnt's guards, the dr3 / ls3 bundles of the
   entry and the source) and dr_post's model clauses (dr_dfun, dr3_epost, dr3_hpost, ls3_dpost).  The entry's re_skip is
   0 or 1 (aentry_ok, W_rep.v:121; s5-spd: at re_skip = 2 drain_init gives skip = false with no re_U = hs_W fact), and
   the entry the drain leaves has aentry_ok's held-array clause (W_rep.v:131-132, from dr_post's aentry_ok e'; s5-spd:
   without it a re_hp e' <> 0 with re_kh e' = 0 is a 0-byte block no request made) ---- *)
Hypothesis DR_CNT_grow : forall cx t m si h j e' h' LB out' (P : Z -> bool),
  RINV cx t m -> dr_at_op cx m -> dr_pick cx m si h ->
  (j < length (lm_es m))%nat -> re_fd (nth j (lm_es m) dr_e0) = hs_fd h ->
  re_eof (nth j (lm_es m) dr_e0) = 0 ->
  re_skip (nth j (lm_es m) dr_e0) = 0 \/ re_skip (nth j (lm_es m) dr_e0) = 1 ->
  msz_ok m -> 0 <= t < OPS_MAX ->
  Z.of_nat (length (re_U (nth j (lm_es m) dr_e0))) <= APARTIAL ->
  (forall b, In b (aentry_blks (nth j (lm_es m) dr_e0) ++ asrc_blks h ++ aout_blks (lm_cap m) (lm_out m)) ->
     0 < snd b) ->
  dr3_epre (nth j (lm_es m) dr_e0) -> ls3_kh (nth j (lm_es m) dr_e0) ->
  dr3_hpre h -> ls3_hn h -> 0 <= lm_cap m ->
  dr_dfun m si h j e' h' LB ->
  dr3_epost (nth j (lm_es m) dr_e0) e' h ->
  (re_hp e' = 0 /\ re_keys e' = []) \/ (re_hp e' <> 0 /\ 8 <= re_kh e') ->
  dr3_hpost h h' ->
  ls3_dpost m j h e' h' ->
  (ReplyCnt.acnt P (aentry_blks e' ++ asrc_blks h' ++ aout_blks (dr_cap1 m j h) out') <=
   ReplyCnt.acnt P (aentry_blks (nth j (lm_es m) dr_e0) ++ asrc_blks h ++ aout_blks (lm_cap m) (lm_out m)) +
   Z.to_nat (ReplyCnt.tr_peakP P
     (dr_tr (lm_c m) (lm_mx m) (Z.of_nat (length (lm_O m))) (lm_cap m) (nth j (lm_es m) dr_e0) h)))%nat.
(* ---- the model facts the callees' premises need, read off RINV (projections, not steps) ---- *)
(* the picked source at the top of an operation: check_no_loss emptied its expected list, its held texts are
   distinct (the plain proof's pair_ok, Prog/SlotInv.v:253-263) *)
Hypothesis RI_src : forall cx t m si h,
  RINV cx t m -> dr_pick cx m si h ->
  hl_recs (hs_expected h) = [] /\ NoDup (texts (hs_held h)) /\ 0 <= hs_fd h < 2 ^ 31.
(* the open sources have distinct fds (so drain's aothers_at holds of the other three slots) *)
Hypothesis RI_fds : forall cx t m i1 i2 h1 h2,
  RINV cx t m -> (i1 < 4)%nat -> (i2 < 4)%nat -> i1 <> i2 ->
  nth i1 (lm_hs m) None = Some h1 -> nth i2 (lm_hs m) None = Some h2 -> hs_fd h1 <> hs_fd h2.
(* the relay's entry for an open source it still reads, and the source, agree (pair_ok's re_eof = 0 clauses) *)
Hypothesis RI_pair : forall cx t m si h j,
  RINV cx t m -> dr_pick cx m si h -> (j < length (lm_es m))%nat ->
  re_fd (nth j (lm_es m) dr_e0) = hs_fd h -> re_eof (nth j (lm_es m) dr_e0) = 0 ->
  re_skip (nth j (lm_es m) dr_e0) = hs_overlong h /\
  (re_skip (nth j (lm_es m) dr_e0) = 0 -> bzs (re_U (nth j (lm_es m) dr_e0)) = bzs (hs_W h)) /\
  length (re_pad1 (nth j (lm_es m) dr_e0)) = 4%nat /\ length (re_pad2 (nth j (lm_es m) dr_e0)) = 4%nat.
(* the controller went away exactly when it is closed, broken or dead (the plain proof's slot invariant over the
   output flags: g_gone = 0 means a live, unbroken, connected controller), so check_no_loss's `gone = 0` stream
   premise and check_shape_done's at = g_nout hold after the drain *)
Hypothesis RI_gone : forall cx t m,
  RINV cx t m ->
  (lm_gn m = 0 -> ct_cl (lm_c m) = 3 /\ ct_br (lm_c m) = 0 /\ ct_dd (lm_c m) = 0) /\
  (lm_gn m = 1 -> ct_cl (lm_c m) = -1 \/ ct_br (lm_c m) = 1 \/ ct_dd (lm_c m) = 1).

(* ---- the allocator-state facts the two calls take, read off LSx; the instance discharges them ---- *)
(* the peak form (a Theorem Labs lane's ROOM-ROUND row #19; dr_spec's byte premise is the drain trace's byte PEAK, C3): conjunct 5
   is s5-r1d's fr_LS_drain_pre_c5p (lib/A/ReplyTrPeak.v:927), and the three premises after re_eof are the ones its
   rows take (fr_LS3_drain_pre_c4 ReplyLS3Arms.v:791, fr_LS_drain_pre_c5p): dc_regs' Ht, aentry_ok's |re_U| bound and
   the drained blocks' sizes (dc_stB's HXP).  The sum form (tr_alloc) was FALSE at reachable states. *)
Hypothesis LS_drain_pre : forall cx t m ly S si h j,
  LSx cx t m ly S -> RINV cx t m -> dr_at_op cx m -> dr_pick cx m si h ->
  (j < length (lm_es m))%nat -> re_fd (nth j (lm_es m) dr_e0) = hs_fd h ->
  re_eof (nth j (lm_es m) dr_e0) = 0 ->
  0 <= t < OPS_MAX ->
  Z.of_nat (length (re_U (nth j (lm_es m) dr_e0))) <= APARTIAL ->
  (forall b, In b (aentry_blks (nth j (lm_es m) dr_e0) ++ asrc_blks h ++ aout_blks (lm_cap m) (lm_out m)) ->
     0 < snd b) ->
  Z.of_nat (length (pending_stream h)) < 2 ^ 26 /\
  hl_cap (hs_expected h) < 2 ^ 26 /\
  re_nheld (nth j (lm_es m) dr_e0) + Z.of_nat (length (pending_stream h)) < 2 ^ 26 /\
  tr_max (dr_tr (lm_c m) (lm_mx m) (Z.of_nat (length (lm_O m))) (lm_cap m) (nth j (lm_es m) dr_e0) h) < MMAX /\
  blocks_bytes S +
    tr_peak (dr_tr (lm_c m) (lm_mx m) (Z.of_nat (length (lm_O m))) (lm_cap m) (nth j (lm_es m) dr_e0) h)
    <= LIVE_MAX /\
  mo_ok MT S (dr_cost MT (lm_c m) (lm_mx m) (Z.of_nat (length (lm_O m))) (lm_cap m) (nth j (lm_es m) dr_e0) h).
(* after the drain: what check_no_loss takes of the state it is called in.  A Theorem Labs lane's TX_LS_cnl_pre
   (commit d0d75bf92db, lib/A/ReplyLS3cTopxPost.v:146; proved as ReplyLS3Arms.v:841 fr_LS3_cnl_pre_p), with
   CfParamsReply.fr_MMAX -> MMAX: the binders e' cap' out' and nine premises after the old ten, each held at
   dc_calls (dc_regs' Ht, dr_at_op's lm_O m = [], and dc_stB's dcB_out: the cut's entry and source at the call,
   dr_post's frame and its entry / source clauses) *)
Hypothesis LS_cnl_pre : forall cx t m ly S (ly' : alayout) (S' : astate) si h j h'' e' cap' out',
  LSx cx t m ly S -> RINV cx t m -> dr_pick cx m si h ->
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
  mo_ok MT S' (cnl_cost MT (hs_expected h'') (hs_held h'')) /\
  AREC * capb (hs_held h'') (hs_expected h'') < 2 ^ 32.
(* the two steps of the allocator-state invariant *)
Hypothesis LS_drain_skip : forall cx t m ly S,
  LSx cx t m ly S -> LSx cx (t + 1) (dr_skip m (dr_k' cx m)) ly S.
(* the drain charges the meter dr_cost of the entry and source it was called with (S to S1), check_no_loss
   cnl_cost of the lists it was called with (S1 to S'); lock, unlock, check_no_loss_read and check_shape_done
   keep the allocator state.  A Theorem Labs lane's TX_LS_drain_step (commit d0d75bf92db, lib/A/ReplyLS3cTopxPost.v:118;
   proved as ReplyLS3cArms.v:119 fr_LS3c_drain_step_p): the binders ly1 h1 E' H' and twenty premises after the old
   five, each held at dc_calls (the drain's and check_no_loss's frames, dcB_out and dc_stE's exports); and, last,
   dc_regs' `0 <= t < OPS_MAX`, as s5-r1d's TX_LS_drain_step_t (1318828167d lib/A/ReplyLSI.v:134, its LS instance's
   lsi_LS_drain_step :509) *)
Hypothesis LS_drain_step : forall cx t m ly S (S1 : astate) (ly' : alayout) (S' : astate)
    si h j h'' e' c' O' cap' out' (E H : hlist) (ly1 : alayout) (h1 : hsrc) (E' H' : hlist),
  LSx cx t m ly S -> dr_pick cx m si h -> (j < length (lm_es m))%nat ->
  mo_le MT S S1
    (dr_cost MT (lm_c m) (lm_mx m) (Z.of_nat (length (lm_O m))) (lm_cap m) (nth j (lm_es m) dr_e0) h) ->
  mo_le MT S1 S' (cnl_cost MT E H) ->
  (exists rest,
     Permutation (ablocks B ly S)
       (aentry_blks (nth j (lm_es m) dr_e0) ++ asrc_blks h ++ aout_blks (lm_cap m) (lm_out m) ++ rest) /\
     Permutation (ablocks B ly1 S1) (aentry_blks e' ++ asrc_blks h1 ++ aout_blks cap' out' ++ rest)) ->
  hl_recs (hs_pending h1) = [] ->
  E = hs_expected h1 -> H = hs_held h1 ->
  (forall rest, Permutation (ablocks B ly1 S1) (list_blks E ++ list_blks H ++ rest) ->
     Permutation (ablocks B ly' S') (list_blks E' ++ list_blks H' ++ rest)) ->
  h'' = set_exp_held h1 E' H' ->
  dr_at_op cx m -> RINV cx t m -> re_fd (nth j (lm_es m) dr_e0) = hs_fd h ->
  re_eof (nth j (lm_es m) dr_e0) = 0 ->
  dr3_epre (nth j (lm_es m) dr_e0) -> ls3_kh (nth j (lm_es m) dr_e0) ->
  dr3_hpre h -> ls3_hn h -> 0 <= lm_cap m ->
  cap' = (if dr_live (lm_c m) h
          then drain_b_c.ds_ocap (dr_fin (lm_c m) (lm_mx m) (Z.of_nat (length (lm_O m))) (lm_cap m)
                                   (nth j (lm_es m) dr_e0) h)
          else lm_cap m) ->
  dr3_epost (nth j (lm_es m) dr_e0) e' h -> dr3_hpost h h1 ->
  ls3_dpost m j h e' h1 -> ls3_cpost h1 E' H' ->
  0 <= t < OPS_MAX ->
  LSx cx (t + 1) (dr_step m (dr_k' cx m) si h'' j e' c' O' cap' out') ly' S'.
(* the live counts at the cut leave room for the arm's peak (ROOM-TEXTS.md (sha256 767baa12f13c; internal record) (c), CORRECTION 2):
   a Theorem Labs lane's row fr_LS3cp_cnt_drain (commit ba8e99b5bd2, lib/A/ReplyLScnt.v:371) with its guards, over the
   room record's count fields (at the cf instance they are ReplyCnt's Psec / P24 / Lsec / L24 / Pcls / LPRIM; the
   top plugs it with ReplyLScntRP.v's lsc_rp_of_acnt).  Its peak is the row's pk_drain m h j (ReplyLScnt.v:151) with
   check_no_loss's part the parameter dr_cnl_pk (below): drain's trace peak + check_no_loss's peak over the drained
   lines + 2, which covers dr_spec's count premise (dr_pk) at the cut and cnl_spec's (cnl_pk) at the state the drain
   leaves (DR_CNT_grow, DR_CNT_cnl) *)
(* check_no_loss's count peak after the drain, a function of the source the drain was called with: at the top it is
   ReplyTrPeakCnl.cnl_pk (hs_held h) (map (map (Z_to_bv 8)) (dr_lines h)) (the row's part of pk_drain, a file that
   Requires the AR event / write arms) *)
Variable dr_cnl_pk : hsrc -> (Z -> bool) -> nat.
(* the kit's check_no_loss trace after a drain has at most that peak: the expected list was empty at the operation's
   start (RI_src) and the drain appended the lines (dr_dfun), the held list is kept (a PURE MODEL rule; at the top
   ReplyLScnt.lsc_cnl_call proves it with = at j := 0, nm := fun _ => RelayRunF.adr0) *)
Hypothesis DR_CNT_cnl : forall (h h'' : hsrc) (P : Z -> bool),
  hl_recs (hs_expected h) = [] ->
  map snd (hl_recs (hs_expected h'')) = map snd (hl_recs (hs_expected h)) ++ map (map (Z_to_bv 8)) (dr_lines h) ->
  hs_held h'' = hs_held h ->
  (Z.to_nat (ReplyCnt.tr_peakP P (cnl_tr (hs_expected h'') (hs_held h''))) <= dr_cnl_pk h P)%nat.
Hypothesis LS_cnt : forall cx t m ly S si h j,
  LSx cx t m ly S -> RINV cx t m -> dr_at_op cx m -> dr_pick cx m si h ->
  (j < length (lm_es m))%nat -> re_fd (nth j (lm_es m) dr_e0) = hs_fd h ->
  re_eof (nth j (lm_es m) dr_e0) = 0 ->
  msz_ok m -> 0 <= t < OPS_MAX ->
  Z.of_nat (length (re_U (nth j (lm_es m) dr_e0))) <= APARTIAL ->
  (forall b, In b (aentry_blks (nth j (lm_es m) dr_e0) ++ asrc_blks h ++ aout_blks (lm_cap m) (lm_out m)) ->
     0 < snd b) ->
  ((hl_recs (hs_pending h) = [] /\ hs_off h = 0) \/
   (exists r rs, hl_recs (hs_pending h) = r :: rs /\ 0 <= hs_off h < Z.of_nat (length (snd r)))) ->
  cnt_ok_pk RP
    (fun P => (Z.to_nat (ReplyCnt.tr_peakP P
       (dr_tr (lm_c m) (lm_mx m) (Z.of_nat (length (lm_O m))) (lm_cap m) (nth j (lm_es m) dr_e0) h)) +
       (dr_cnl_pk h P + 2))%nat)
    (ablocks B ly S).
(* copied from W_LLVMFuzzerTestOneInput_latch.v lt_amodel_kept *)
Lemma dr_amodel_kept : forall ly S Hp (W : world segs) mem md (W' : world segs) mem' m,
  ARx ly S Hp W mem md -> amodel_at B ly S W mem m ->
  0 <= as_errno B -> as_errno B + 4 <= DR_CEIL8 ->
  (forall a, 0 <= a < DR_CEIL8 -> abyte_kept W mem W' mem' a) ->
  amodel_at B ly S W' mem' m.
Proof.
  intros ly S Hp W mem md W' mem' m HAR (M1 & M2 & M3 & M4 & M5 & M6 & M7 & M8 & M9 & M10) HE0 HE1 KEEP.
  split; [exact M1|]. split.
  { intros i Hi. specialize (M2 i Hi). unfold aslot in *.
    assert (HB0 : 0 <= rg_s fr_RG + ASRC * Z.of_nat i) by (unfold fr_RG; cbn; unfold ASRC; lia).
    assert (HB1 : rg_s fr_RG + ASRC * Z.of_nat i + ASRC <= DR_CEIL8)
      by (unfold fr_RG, DR_CEIL8; cbn; unfold ASRC; pose proof dr_ceil_lo; lia).
    destruct (nth i (lm_hs m) None) as [h|].
    - destruct (dr_asrc B ARx LAWS BLKR ly S Hp W mem md _ h HAR M2 HB0 HB1) as [F1 F2].
      exact (asrc_at_kept B ly S W mem ly S W' mem' _ h M2 (dr_akept_of_low _ _ _ _ _ KEEP F1) F2).
    - destruct M2 as [G1 G2]. split.
      + apply (akept_garr8 W mem); [|exact G1]. intros x Hx. rewrite repeat_length in Hx.
        apply (dr_akept_of_rng W W' mem mem' (rg_s fr_RG + ASRC * Z.of_nat i)
                 (rg_s fr_RG + ASRC * Z.of_nat i + ASRC) KEEP HB0 HB1). unfold ASRC in *. lia.
      + apply (akept_awr W mem); [|exact G2]. intros x Hx.
        apply (dr_akept_of_rng W W' mem mem' (rg_s fr_RG + ASRC * Z.of_nat i)
                 (rg_s fr_RG + ASRC * Z.of_nat i + ASRC) KEEP HB0 HB1). unfold ASRC in *. lia. }
  split.
  { destruct (dr_arelay B ARx LAWS BLKR ly S Hp W mem md (lm_G m) (lm_es m) HAR M3) as [F1 F2].
    exact (arelay_at_kept B fr_globals ly S W mem ly S W' mem' _ _ M3
             (dr_akept_of_low _ _ _ _ _ KEEP F1) F2). }
  split.
  { destruct (dr_aout B ARx LAWS BLKR ly S Hp W mem md _ _ _ _ _ _ HAR M4 HE0 HE1) as [F1 F2].
    exact (aout_at_kept B fr_globals ly S W mem ly S W' mem' _ _ _ _ _ _ M4
             (dr_akept_of_low _ _ _ _ _ KEEP F1) F2). }
  split.
  { apply (agone_at_kept fr_globals W mem W' mem' _ M5).
    apply dr_akept_rng; [exact KEEP | cbn; lia | unfold DR_CEIL8; cbn; pose proof dr_ceil_lo; lia]. }
  split.
  { apply (alock_at_kept fr_globals W mem W' mem' _ M6).
    apply dr_akept_rng; [exact KEEP | cbn; lia | unfold DR_CEIL8; cbn; pose proof dr_ceil_lo; lia]. }
  split.
  { apply (awake_at_kept fr_globals W mem W' mem' M7).
    apply dr_akept_rng; [exact KEEP | cbn; lia | unfold DR_CEIL8; cbn; pose proof dr_ceil_lo; lia]. }
  split.
  { apply (akept_vm W mem); [|exact M8]. intros x Hx. apply KEEP.
    unfold AG_NFD, DR_CEIL8 in *. pose proof dr_ceil_lo. cbn in Hx. lia. }
  split.
  { apply (akept_awr W mem); [|exact M9]. intros x Hx. apply KEEP.
    unfold AG_NFD, DR_CEIL8 in *. pose proof dr_ceil_lo. lia. }
  destruct M10 as (M10 & M11 & (lst & M12) & M13).
  split; [exact M10|].
  split.
  { apply (akept_vm W mem); [|exact M11]. intros x Hx. apply KEEP.
    unfold AG_THREAD_UP, DR_CEIL8 in *. pose proof dr_ceil_lo. cbn in Hx. lia. }
  split.
  { exists lst. apply (akept_vm W mem); [|exact M12]. intros x Hx. apply KEEP.
    unfold AG_LISTEN, DR_CEIL8 in *. pose proof dr_ceil_lo. cbn in Hx. lia. }
  apply (akept_awr W mem); [|exact M13]. intros x Hx. apply KEEP.
  unfold AG_LISTEN, DR_CEIL8 in *. pose proof dr_ceil_lo. lia.
Qed.
(* copied from W_LLVMFuzzerTestOneInput_latch.v lt_ainput_kept *)
Lemma dr_ainput_kept : forall cx ly S Hp (W : world segs) mem md (W' : world segs) mem',
  ARx ly S Hp W mem md -> ainput_at B cx ly S W mem ->
  Z.of_nat (length (c_pl cx)) = c_n cx ->
  (forall a, 0 <= a < DR_CEIL8 -> abyte_kept W mem W' mem' a) ->
  ainput_at B cx ly S W' mem'.
Proof.
  intros cx ly S Hp W mem md W' mem' HAR (I1 & I2) Hlen KEEP.
  split; [exact I1|]. apply (akept_garr8 W mem); [|exact I2].
  intros x Hx. rewrite length_map in Hx. rewrite Hlen in Hx. apply KEEP.
  destruct I1 as [(Hn & Hpo) | (Hn & Hin)]; [lia|].
  destruct (dr_blk B ARx LAWS BLKR ly S Hp W mem md _ _ HAR Hin) as (P1 & P2 & P3).
  unfold DR_CEIL8. lia.
Qed.
Let de_RUN := paj_run_x_x (PL := PL_fr) (PI := PB_fr) B PST ARx LAWS G_fr HG 0 [].
Let de_RUNTO := paj_run_to_x_x (PL := PL_fr) (PI := PB_fr) B PST ARx LAWS G_fr HG 0 [].
Let de_BR := paj_branch (PI := PB_fr).
(* a run's write obligation: the in.n cell is in the function's own stack window, the other regions are read-only *)
Ltac de_awr U9 :=
  cbn [ss_mem add_cond ss_de de_regions];
  repeat (apply awr_ok_x_cons;
    [ let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha;
      cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha;
      rewrite ?ew_ewset_other in Ha by lia; rewrite ?U9 in Ha;
      first [ lia | left; split; [left; unfold LLVMF_STK; lia | lia] ]
    | ]);
  apply awr_ok_x_nil.
(* a byte outside the in.n cell is outside every region's writable window *)
Ltac de_nowr U9 Hna :=
  let r := fresh "r" in let Hin := fresh "Hin" in let Hr := fresh "Hr" in
  intros (r & Hin & Hr); cbn [ss_mem add_cond ss_de de_regions In] in Hin;
  repeat (destruct Hin as [<- | Hin];
    [ cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr;
      rewrite ?ew_ewset_other in Hr by lia; rewrite ?U9 in Hr; unfold DR_N in Hna; lia | ]);
  destruct Hin.


(* everything lcut says of the memory, carried across the entry's runs (their only store is the in.n cell) *)
Lemma de_carry : forall cx (W : world segs) mem mem' md ly3 S3 Hp3 fpos m,
  ARx ly3 S3 Hp3 W mem md -> In (1, fpos) (frames S3) ->
  Z.of_nat (length (c_pl cx)) = c_n cx ->
  alloc_ceiling + 32768 <= spZ (c_regs cx) <= 2 ^ 47 ->
  aframe_at cx true (frame_addr ly3 1 fpos) W mem -> amodel_at B ly3 S3 W mem m ->
  ainput_at B cx ly3 S3 W mem -> rom_view segs W mem -> jt_rom W mem ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (lf_F cx + DR_N <= a < lf_F cx + DR_N + 8) -> abyte_kept W mem W mem' a) ->
  (forall a, writable_at segs (arm W mem) a -> writable_at segs (arm W mem') a) ->
  aframe_at cx true (frame_addr ly3 1 fpos) W mem' /\ amodel_at B ly3 S3 W mem' m /\
  ainput_at B cx ly3 S3 W mem' /\ rom_view segs W mem' /\ jt_rom W mem'.
Proof.
  intros cx W mem mem' md ly3 S3 Hp3 fpos m HAR Hfin Hlen Hsp HFR HMOD HIN HRV HJT KEEP WK.
  pose proof dr_ceil_lo as HCL. pose proof (pal_env B TL) as ((HE0 & HE1) & _).
  assert (HFb : spZ (c_regs cx) - 352 < lf_F cx <= spZ (c_regs cx) - 320).
  { unfold lf_F. pose proof (Z.mod_pos_bound (spZ (c_regs cx) - 320) 32 ltac:(lia)). lia. }
  destruct (frames_bounds_x segs B ARx LAWS ly3 S3 Hp3 W mem md 1 fpos HAR Hfin) as (HFF1 & HFF2 & _).
  replace (fs_frame_bytes 1) with 128 in HFF2 by reflexivity.
  assert (FF8 : 0 <= frame_addr ly3 1 fpos / 8 /\ 8 * (frame_addr ly3 1 fpos / 8) <= frame_addr ly3 1 fpos)
    by (split; [apply Z.div_pos; lia | apply Z.mul_div_le; lia]).
  assert (KL : forall a, 0 <= a < DR_CEIL8 -> abyte_kept W mem W mem' a).
  { intros a Ha. apply KEEP; unfold DR_N, DR_CEIL8 in *; lia. }
  split.
  { apply (de_aframe_kept cx true _ W W mem mem' HFR KEEP WK); unfold DR_CEIL8, SB in *; lia. }
  split; [exact (dr_amodel_kept ly3 S3 Hp3 W mem md W mem' m HAR HMOD HE0
                   ltac:(unfold DR_CEIL8, kLowMemEnd in *; lia) KL)|].
  split; [exact (dr_ainput_kept cx ly3 S3 Hp3 W mem md W mem' HAR HIN Hlen KL)|].
  split; [exact (dr_rom_kept W W mem mem' HRV KL)|].
  exact (dr_jt_kept W W mem mem' HJT KL).
Qed.
(* the fake frame's flag word (lcut's conjunct after aframe_at), across the same keep as de_carry's *)
Lemma de_flag_kept : forall cx (W : world segs) mem mem' md ly3 S3 Hp3 fpos,
  ARx ly3 S3 Hp3 W mem md -> In (1, fpos) (frames S3) ->
  alloc_ceiling + 32768 <= spZ (c_regs cx) <= 2 ^ 47 ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (lf_F cx + DR_N <= a < lf_F cx + DR_N + 8) -> abyte_kept W mem W mem' a) ->
  sv8 W mem (frame_addr ly3 1 fpos + 120) (flag_addr ly3 1 fpos) ->
  sv8 W mem' (frame_addr ly3 1 fpos + 120) (flag_addr ly3 1 fpos).
Proof.
  intros cx W mem mem' md ly3 S3 Hp3 fpos HAR Hfin Hsp KEEP Hv.
  pose proof dr_ceil_lo as HCL.
  assert (HFb : spZ (c_regs cx) - 352 < lf_F cx <= spZ (c_regs cx) - 320).
  { unfold lf_F. pose proof (Z.mod_pos_bound (spZ (c_regs cx) - 320) 32 ltac:(lia)). lia. }
  destruct (frames_bounds_x segs B ARx LAWS ly3 S3 Hp3 W mem md 1 fpos HAR Hfin) as (HFF1 & HFF2 & _).
  replace (fs_frame_bytes 1) with 128 in HFF2 by reflexivity.
  unfold sv8 in *. apply (akept_vm W mem); [|exact Hv].
  intros x Hx. cbn in Hx. apply KEEP; unfold DR_N, DR_CEIL8 in *; lia.
Qed.
(* the paddings and the fd range of every entry, from the relay's representation (aentry_ok) *)
Lemma dr_pads_of_relay : forall ly S W mem G es,
  arelay_at B fr_RG ly S W mem G es ->
  Forall (fun e => length (re_pad1 e) = 4%nat /\ length (re_pad2 e) = 4%nat) es /\
  Forall (fun e => 0 <= re_fd e < 2 ^ 31) es.
Proof.
  intros ly S W mem G es (_ & _ & _ & _ & _ & _ & _ & _ & _ & HE & _).
  split; rewrite Forall_forall in HE |- *; intros e He;
    destruct (HE e He) as (_ & _ & H3 & H4 & H5 & _); [split; assumption | exact H5].
Qed.

(* ---- (DrainScan) the entry state of the scan's head 0x84550 ----
   a0 = s6 = &g_src[i] (the body reads only the 4-byte fd at its start), a1 = the entries left, a2 = s->fd,
   a3 = SB + (G + 56 i)/8 the shadow cell of the entry.  The entry lies inside the table's 896-byte block, so
   its granule is addressable and the shadow check at 0x84550-0x84554 is decided inside the run: the partial
   test at 0x84578 never appears. *)
Let ds_RUN := paj_run_x_x (PL := PL_fr) (PI := PB_fr) B PST ARx LAWS G_fr HG 0 [].
Let ds_RUNTO := paj_run_to_x_x (PL := PL_fr) (PI := PB_fr) B PST ARx LAWS G_fr HG 0 [].
Let ds_BR := paj_branch (PI := PB_fr).
(* a run over read-only regions leaves the memory as it was *)
Ltac ds_meq HF Em := lazymatch type of HF with frame_of ?E ?rs ?m ?m' =>
  pose proof (frame_of_read_only E rs m m' ltac:(vm_compute; reflexivity) HF) as Em end.
Lemma ds_common_kept : forall cx FF (regs regs' : bvmap 5 word),
  (forall r, In r DS_KEPT -> getr regs' r = getr regs r) ->
  lregs_common B cx FF regs -> lregs_common B cx FF regs'.
Proof.
  intros cx FF regs regs' HK H. unfold lregs_common in H |- *.
  destruct H as (A2 & A8 & A9 & A18 & A19 & A20 & A23 & A24 & A25 & A26 & A3 & A4).
  rewrite (HK 2%bv ltac:(cbv; tauto)), (HK 8%bv ltac:(cbv; tauto)), (HK 9%bv ltac:(cbv; tauto)),
          (HK 18%bv ltac:(cbv; tauto)), (HK 19%bv ltac:(cbv; tauto)), (HK 20%bv ltac:(cbv; tauto)),
          (HK 23%bv ltac:(cbv; tauto)), (HK 24%bv ltac:(cbv; tauto)), (HK 25%bv ltac:(cbv; tauto)),
          (HK 26%bv ltac:(cbv; tauto)), (HK 3%bv ltac:(cbv; tauto)), (HK 4%bv ltac:(cbv; tauto)).
  repeat split; assumption.
Qed.
Lemma ds_base_kept : forall cx t FF (regs regs' : bvmap 5 word),
  (forall r, In r DS_KEPT -> getr regs' r = getr regs r) ->
  lregs_base cx t FF regs -> lregs_base cx t FF regs'.
Proof.
  intros cx t FF regs regs' HK H. unfold lregs_base in H |- *.
  destruct H as (HC & H27 & Ht).
  split; [exact (ds_common_kept cx FF regs regs' HK HC)|].
  split; [rewrite (HK 27%bv ltac:(cbv; tauto)); exact H27 | exact Ht].
Qed.

(* (2) the table scan 0x84550-0x84584, by induction on the entries left. *)
Lemma dr_scan : forall n cx Hpe t i W c,
  lf_base_x B MT XM_LIB RLO RHI fr_live_pre LIBROOM NP G_fr ARx cx Hpe ->
  DST A_dr_loop cx Hpe t (lregs_scan cx t n i) W c ->
  SRr segs W c (fun W' c' => (exists j, DST A_dr_found cx Hpe t (lregs_found cx t j) W' c') \/
                             DST A_dr_nf cx Hpe t (lregs_nf cx t) W' c').
Proof.
  intros n. induction n as [|n IH]; intros cx Hpe t i W c HB HD;
    destruct HD as (regs & mem & md & -> & HROM & HLC);
    destruct HLC as (own & ly3 & S3 & Hp3 & kk & m & fpos & HJ & Hown & HFRM & HFLM & HMOD & HINP & HRV & HBLK & HLS & HNP & HRI & HREG);
    unfold lregs_scan in HREG;
    destruct HREG as (HBASEr & HATOP & H28 & HSV8 & (sl & h & HPICK & H21 & H12 & HNM) & Hi & Hnn & H10 & H22 & H11 & H13).
  { exfalso. lia. }
  (* ---- the model side: the table's block, the fd of entry i, the picked source's fd ---- *)
  pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs.
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  assert (HAR : ARx ly3 S3 Hp3 W mem md) by (eapply ajournal_gx_AR_x; exact HJ).
  pose proof (proj1 (proj2 (proj2 HMOD))) as HREL.
  pose proof HREL as HREL2.
  destruct HREL2 as (_ & _ & _ & _ & _ & _ & Hle16 & HGin & (tl & HTAB) & _ & _).
  destruct (dr_pads_of_relay ly3 S3 W mem (lm_G m) (lm_es m) HREL) as (HPAD & HFDS).
  assert (Hle16Z : Z.of_nat (length (lm_es m)) <= 16) by lia.
  assert (Hin : (Z.to_nat i < length (lm_es m))%nat) by lia.
  pose proof (dr_tbl_fd W mem (lm_G m) (lm_es m) tl (Z.to_nat i) HTAB HPAD HFDS Hin) as Mu.
  rewrite Z2Nat.id in Mu by lia.
  assert (Hfdb : 0 <= re_fd (nth (Z.to_nat i) (lm_es m) dr_e0) < 2 ^ 31)
    by (rewrite Forall_forall in HFDS; apply HFDS, nth_In; lia).
  destruct (RI_src cx t m sl h HRI HPICK) as (_ & _ & Hhfd).
  unfold AENT in Mu, H10, H22.
  destruct (alx_blocks _ _ _ LAWS ly3 S3 Hp3 W mem md (lm_G m) ATABLE HAR HGin) as (HP16 & HP4096 & HPceil & HPapp & _).
  assert (RQ : req_size ATABLE = 896) by reflexivity.
  rewrite RQ in HPceil, HPapp.
  assert (G8 : lm_G m = 8 * (lm_G m / 8)).
  { pose proof (Z.div_mod (lm_G m) 16 ltac:(lia)) as D. rewrite HP16, Z.add_0_r in D.
    rewrite D at 2. replace (16 * (lm_G m / 16)) with ((2 * (lm_G m / 16)) * 8) by ring.
    rewrite Z.div_mul by lia. lia. }
  assert (XQ : (lm_G m + 56 * i) / 8 = lm_G m / 8 + 7 * i).
  { rewrite G8 at 1. replace (8 * (lm_G m / 8) + 56 * i) with ((lm_G m / 8 + 7 * i) * 8) by ring.
    apply Z.div_mul. lia. }
  pose proof HBASEr as HBASE2. unfold lregs_base in HBASE2.
  destruct HBASE2 as (HCOM & H27 & Ht).
  pose proof HCOM as HCOM2. unfold lregs_common in HCOM2.
  destruct HCOM2 as (R2 & R8 & R9 & R18 & R19 & R20 & R23 & R24 & R25 & R26 & R3 & R4).
  (* ---- the entry state at the head ---- *)
  remember (Eimg (Ereg regs (ds_extra (re_fd (nth (Z.to_nat i) (lm_es m) dr_e0))))) as E eqn:HE.
  assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
  assert (HAE : env_agree 32 (Ereg regs (ds_extra (re_fd (nth (Z.to_nat i) (lm_es m) dr_e0)))) E)
    by (rewrite HE; split; [intros mm Hm; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
  assert (EEo : forall mm (rr : bv 5), Z.of_nat mm = bv_unsigned rr -> ew E mm = getr regs rr)
    by (intros mm rr Hm; subst E; pose proof (bv_unsigned_in_range 5 rr) as Hr5;
        change (bv_modulus 5) with 32 in Hr5; rewrite Eimg_low by (unfold A_TEXT; lia);
        apply ew_Ereg_nat; exact Hm).
  assert (E10 : ew E 10 = Z_to_bv 64 (lm_G m + 56 * i)) by (rewrite (EEo 10%nat 10%bv eq_refl); exact H10).
  assert (E11 : ew E 11 = Z_to_bv 64 (Z.of_nat (length (lm_es m)) - i))
    by (rewrite (EEo 11%nat 11%bv eq_refl); exact H11).
  assert (E12 : ew E 12 = Z_to_bv 64 (hs_fd h)) by (rewrite (EEo 12%nat 12%bv eq_refl); exact H12).
  assert (E22 : ew E 22 = Z_to_bv 64 (lm_G m + 56 * i)) by (rewrite (EEo 22%nat 22%bv eq_refl); exact H22).
  assert (E26 : ew E 26 = Z_to_bv 64 SB) by (rewrite (EEo 26%nat 26%bv eq_refl); exact R26).
  assert (E32 : ew E 32 = Z_to_bv 64 (re_fd (nth (Z.to_nat i) (lm_es m) dr_e0)))
    by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
  assert (USH : U E (SAlu ALU_ADD (SOff 26 0) (SAlu ALU_SRL (SOff 22 0) (SLit 3)))
                = SB + lm_G m / 8 + 7 * i).
  { rewrite !U_SAlu, (U_atom E 26 SB E26), (U_atom E 22 _ E22), U_lit by (unfold SB; lia). cbn [zalu_raw].
    change (Z.land 3 63) with 3. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8. unfold zcanon, M64.
    rewrite XQ. rewrite (Z.mod_small (lm_G m / 8 + 7 * i)) by lia.
    rewrite Z.mod_small by (unfold SB; lia). lia. }
  assert (HS : st_ok_pi segs VAL E ss_ds
                 (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + A_dr_loop)) mem (seg_rom segs)))).
  { rewrite restrict_mkst_fx. unfold ss_ds. apply pa_entry_st_ok_full.
    - unfold ds_sr. rewrite HE. apply regs_ok_pin; [apply regs_ok_Eimg_Ereg | intros X; discriminate X |].
      rewrite <- HE, H13. apply bv_eq.
      fold (U E (SAlu ALU_ADD (SOff 26 0) (SAlu ALU_SRL (SOff 22 0) (SLit 3)))). rewrite USH.
      apply unsigned_lit_small. unfold SB; lia.
    - vm_compute. reflexivity.
    - unfold ds_regions. repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
        cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
      cbn [base_val]. rewrite E22, unsigned_lit_small by lia.
      split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val segs E _ (lm_G m + 56 * i) 0 4 (SOff 32 0)
               (re_fd (nth (Z.to_nat i) (lm_es m) dr_e0)));
        [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
      rewrite Z.add_0_r. exact Mu.
    - cbn [pairwise_disjoint all_disjoint]. repeat split.
    - split; [|split; [exact I | exact I]].
      cbn [ds_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
      rewrite E22, E26, E32, !unsigned_lit_small by (unfold SB; lia).
      change (2 ^ 3) with 8. rewrite !Z.pow_0_r, !Z.mod_1_r.
      repeat match goal with |- _ /\ _ => split end; try (unfold SB; lia).
      rewrite G8. replace (8 * (lm_G m / 8) + 56 * i) with ((lm_G m / 8 + 7 * i) * 8) by ring.
      apply Z_mod_mult. }
  clear HE.
  assert (HBx : U E ds_Bx = SHADOW_OFF)
    by (unfold ds_Bx; rewrite (U_atom E 26 SB E26) by (unfold SB; lia); reflexivity).
  assert (SHOK : sh_ok segs ds_Bx ds_SH E (mrestrict (w_H W) mem)).
  { constructor; [|constructor].
    eapply shent_ok_of_range.
    + apply (range_addressable_of_block_hp0_x segs B ARx LAWS HP0 ly3 S3 Hp3 W mem md (lm_G m) ATABLE
               (lm_G m + 56 * i) 8 HAR HGin); rewrite ?RQ; lia.
    + exact HBx.
    + rewrite (U_atom E 22 _ E22) by lia. reflexivity.
    + lia.
    + lia.
    + intros x Hx. unfold in_app, SHADOW_OFF, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *. lia. }
  unfold cfg_at. change (w64 (fr_B0 + A_dr_loop)) with (Z_to_bv 64 (BASE + A_dr_loop)).
  (* ---- 0x84550-0x8455c: the shadow check, the load of the entry's fd, and the match test ---- *)
  paj_run_tok_x ds_RUN HS HJ SHOK ds_span.
  { apply awr_ok_x_cons; [intros a Ha; cbn in Ha; lia | apply awr_ok_x_nil]. }
  ds_meq HF Em1. clear HF HFr HG0.
  psrr_branch_tok ds_RUN ds_BR HS SHOK ds_span.
  - (* 0x8455c beq taken: entry i carries the source's fd - on to 0x84a20 *)
    rewrite branch_eq_U, (U_atom E 32 _ E32), (U_atom E 12 _ E12) in Hc by lia.
    apply Z.eqb_eq in Hc.
    paj_run_to_tok_x ds_RUNTO HS HJ SHOK ds_span A_dr_found.
    { apply awr_ok_x_cons; [intros a Ha; cbn in Ha; lia | apply awr_ok_x_nil]. }
    ds_meq HF Em2.
    pose proof (regs_kept_of_st_ok_pi (PI := PB_fr) _ _ _ regs _ DS_KEPT HS HAE
                  ltac:(vm_compute; reflexivity)) as KR.
    cbn [ms_regs restrict] in KR.
    prreg HS (10%bv : bv 5) N10. prreg HS (22%bv : bv 5) N22.
    pmkst HS. rewrite Em2, Em1 in HJ |- *.
    apply SRr_ret. left. exists (Z.to_nat i).
    lazymatch goal with |- DST _ _ _ _ _ _ (mkCfg (mkst ?r _ ?mm _) ?d) => exists r, mm, d end.
    split; [reflexivity|]. split; [exact HROM|].
    exists own, ly3, S3, Hp3, kk, m, fpos.
    split; [exact HJ|]. split; [exact Hown|]. split; [exact HFRM|]. split; [exact HFLM|]. split; [exact HMOD|].
    split; [exact HINP|]. split; [exact HRV|]. split; [exact HBLK|]. split; [exact HLS|]. split; [exact HNP|].
    split; [exact HRI|].
    unfold lregs_found.
    split; [exact (ds_base_kept cx t _ regs _ KR HBASEr)|].
    split; [exact HATOP|].
    split; [rewrite (KR 28%bv ltac:(cbv; tauto)); exact H28|].
    split; [exact HSV8|].
    split.
    { exists sl, h. split; [exact HPICK|].
      split; [rewrite (KR 21%bv ltac:(cbv; tauto)); exact H21|].
      split; [exact Hc|]. rewrite Z2Nat.id by lia. exact HNM. }
    split; [exact Hin|].
    split.
    + rewrite N10, E10. unfold w64, AENT. rewrite Z2Nat.id by lia. reflexivity.
    + rewrite N22, E22. unfold w64, AENT. rewrite Z2Nat.id by lia. reflexivity.
  - (* 0x8455c beq not taken: entry i is not the one *)
    rewrite branch_eq_U, (U_atom E 32 _ E32), (U_atom E 12 _ E12) in Hc by lia.
    apply Z.eqb_neq in Hc.
    paj_run_tok_x ds_RUN HS HJ SHOK ds_span.
    { apply awr_ok_x_cons; [intros a Ha; cbn in Ha; lia | apply awr_ok_x_nil]. }
    ds_meq HF Em2. clear HF HFr HG0.
    psrr_branch_tok ds_RUN ds_BR HS SHOK ds_span.
    + (* 0x84570 bnez taken: entries left, back to the head at i + 1 *)
      rewrite branch_ne_U, (U_atom_off E 11 _ (-1) E11), U_lit in Hc0 by lia.
      assert (Hlt : i + 1 < Z.of_nat (length (lm_es m)))
        by (destruct (Z.eqb_spec (Z.of_nat (length (lm_es m)) - i + -1) 0); [discriminate | lia]).
      paj_run_to_tok_x ds_RUNTO HS HJ SHOK ds_span A_dr_loop.
      { apply awr_ok_x_cons; [intros a Ha; cbn in Ha; lia | apply awr_ok_x_nil]. }
      ds_meq HF Em3.
      pose proof (regs_kept_of_st_ok_pi (PI := PB_fr) _ _ _ regs _ DS_KEPT HS HAE
                    ltac:(vm_compute; reflexivity)) as KR.
      cbn [ms_regs restrict] in KR.
      prreg HS (10%bv : bv 5) N10. prreg HS (11%bv : bv 5) N11.
      prreg HS (13%bv : bv 5) N13. prreg HS (22%bv : bv 5) N22.
      rewrite E10, unsigned_lit_small in N10 by lia.
      rewrite E11, unsigned_lit_small in N11 by lia.
      rewrite E22, unsigned_lit_small in N22 by lia.
      assert (Q3 : alu64 ALU_SRL (Z_to_bv 64 (lm_G m + 56 * i)) (Z_to_bv 64 3)
                   = Z_to_bv 64 (lm_G m / 8 + 7 * i)).
      { apply bv_eq. rewrite alu64_unsigned. cbn [zalu_raw]. rewrite !unsigned_lit_small by lia.
        change (Z.land 3 63) with 3. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
        rewrite XQ. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64). apply Z.mod_small. lia. }
      rewrite E26, E22, Q3, !ds_add_lit in N13.
      pmkst HS. rewrite Em3, Em2, Em1 in HJ |- *.
      eapply (IH cx Hpe t (i + 1)); [exact HB|].
      lazymatch goal with |- DST _ _ _ _ _ _ (mkCfg (mkst ?r _ ?mm _) ?d) => exists r, mm, d end.
      split; [reflexivity|]. split; [exact HROM|].
      exists own, ly3, S3, Hp3, kk, m, fpos.
      split; [exact HJ|]. split; [exact Hown|]. split; [exact HFRM|]. split; [exact HFLM|]. split; [exact HMOD|].
      split; [exact HINP|]. split; [exact HRV|]. split; [exact HBLK|]. split; [exact HLS|]. split; [exact HNP|].
      split; [exact HRI|].
      unfold lregs_scan.
      split; [exact (ds_base_kept cx t _ regs _ KR HBASEr)|].
      split; [exact HATOP|].
      split; [rewrite (KR 28%bv ltac:(cbv; tauto)); exact H28|].
      split; [exact HSV8|].
      split.
      { exists sl, h. split; [exact HPICK|].
        split; [rewrite (KR 21%bv ltac:(cbv; tauto)); exact H21|].
        split; [rewrite (KR 12%bv ltac:(cbv; tauto)); exact H12|].
        apply ds_nomatch_step; [exact HNM | lia | exact Hc]. }
      split; [lia|].
      split; [lia|].
      split; [rewrite N10; unfold w64, AENT; f_equal; lia|].
      split; [rewrite N22; unfold w64, AENT; f_equal; lia|].
      split; [rewrite N11; unfold w64; f_equal; lia|].
      rewrite N13; unfold w64; f_equal; lia.
    + (* 0x84570 bnez not taken: no entry carries the fd - 0x84574 j 0x846c8 *)
      rewrite branch_ne_U, (U_atom_off E 11 _ (-1) E11), U_lit in Hc0 by lia.
      assert (Hend : i + 1 = Z.of_nat (length (lm_es m)))
        by (destruct (Z.eqb_spec (Z.of_nat (length (lm_es m)) - i + -1) 0); [lia | discriminate]).
      paj_run_to_tok_x ds_RUNTO HS HJ SHOK ds_span A_dr_nf.
      { apply awr_ok_x_cons; [intros a Ha; cbn in Ha; lia | apply awr_ok_x_nil]. }
      ds_meq HF Em3.
      pose proof (regs_kept_of_st_ok_pi (PI := PB_fr) _ _ _ regs _ DS_KEPT HS HAE
                    ltac:(vm_compute; reflexivity)) as KR.
      cbn [ms_regs restrict] in KR.
      pmkst HS. rewrite Em3, Em2, Em1 in HJ |- *.
      apply SRr_ret. right.
      lazymatch goal with |- DST _ _ _ _ _ _ (mkCfg (mkst ?r _ ?mm _) ?d) => exists r, mm, d end.
      split; [reflexivity|]. split; [exact HROM|].
      exists own, ly3, S3, Hp3, kk, m, fpos.
      split; [exact HJ|]. split; [exact Hown|]. split; [exact HFRM|]. split; [exact HFLM|]. split; [exact HMOD|].
      split; [exact HINP|]. split; [exact HRV|]. split; [exact HBLK|]. split; [exact HLS|]. split; [exact HNP|].
      split; [exact HRI|].
      unfold lregs_nf.
      split; [exact (ds_base_kept cx t _ regs _ KR HBASEr)|].
      split; [exact HATOP|].
      split; [rewrite (KR 28%bv ltac:(cbv; tauto)); exact H28|].
      split; [exact HSV8|].
      exists sl, h. split; [exact HPICK|].
      rewrite <- Hend. apply ds_nomatch_step; [exact HNM | lia | exact Hc].
Qed.

(* (3) the arm's entry 0x84520-0x8453c: the source's fd, g_nsrc, the store of in.n, and the empty-table test. *)
Lemma dr_entry : forall cx Hpe t W c,
  lf_base_x B MT XM_LIB RLO RHI fr_live_pre LIBROOM NP G_fr ARx cx Hpe ->
  INV_A_x B NP G_fr fr_FP PST ARx LSx RINV 2 cx Hpe t W c ->
  SRr segs W c (fun W' c' => (exists n, DST A_dr_loop cx Hpe t (lregs_scan cx t n 0) W' c') \/
                             DST A_dr_nf cx Hpe t (lregs_nf cx t) W' c').
Proof.
  intros cx Hpe t W c HB (regs & regsD & mem & md & -> & KR0 & HD11 & HJOUR & HROM & HLF).
  destruct HLF as (own & ly3 & S3 & Hp3 & k & m & fpos & HJ & Hown & HFR & HFL & HMOD & HIN & HRV & HSEP & HLS & HNP & HRI & HR).
  unfold lregs_D in HR. cbv zeta in HR.
  destruct HR as ((C2 & C8 & C9 & C18 & C19 & C20 & C23 & C24 & C25 & C26 & C3 & C4) & R6 & R7 & R27 & Ht & Hk & HO
    & R11 & HPK).
  pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
  pose proof dr_ceil_lo as HCL.
  (* the operation is 2, and pick() gave slot si, which holds h *)
  assert (Hop : in_byte cx (lm_k m) mod 10 = 2).
  { pose proof (Z.mod_pos_bound (in_byte cx (lm_k m)) 10 ltac:(lia)) as Hb.
    rewrite HD11 in R11. apply (f_equal bv_unsigned) in R11. unfold w64 in R11.
    rewrite !unsigned_lit_small in R11 by lia. lia. }
  rewrite Hop in HPK. change (picks 2) with true in HPK.
  destruct HPK as (R28 & R29 & [(si & Hpk & R21) | (Hf & _)]); [|lia].
  change (if lm_k m + 1 <? c_n cx then lm_k m + 2 else lm_k m + 1) with (dr_k' cx m) in R28, R29.
  change (if lm_k m + 1 <? c_n cx then in_byte cx (lm_k m + 1) else 0) with (dr_kb cx m) in Hpk.
  assert (Hk' : 0 <= dr_k' cx m <= c_n cx)
    by (unfold dr_k'; destruct (Z.ltb_spec (lm_k m + 1) (c_n cx)); lia).
  pose proof HMOD as (Hlen4 & HSL & HREL & _).
  destruct (de_pick_some (lm_hs m) (dr_kb cx m) si Hpk) as [Hsi [h Hh]].
  rewrite Hlen4 in Hsi.
  assert (HPICK : dr_pick cx m si h) by (split; [exact Hpk | split; [exact Hsi | exact Hh]]).
  pose proof (HSL si Hsi) as HSRC. unfold aslot in HSRC. rewrite Hh in HSRC.
  pose proof HSRC as (Mfd & _ & _ & _ & _ & _ & _ & _ & Rfd & _).
  pose proof HREL as (Msrc & _ & Mnsrc & _ & _ & _ & Hl16 & HGin & _).
  (* AR, the relay's block, the stack window, errno, the fake frame *)
  pose proof (ajournal_gx_AR_x segs B PST ARx G_fr 0 [] LLVMF_STK _ _ _ _ _ _ _ _ own ly3 S3 Hp3 W mem md k HJ) as HAR.
  destruct (alx_blocks _ _ _ LAWS ly3 S3 Hp3 W mem md (lm_G m) ATABLE HAR HGin) as (HG16 & HG4096 & HGceil & _).
  assert (RQ : req_size ATABLE = 896) by reflexivity. rewrite RQ in HGceil.
  pose proof HB as (HAI & HPRE).
  pose proof HPRE as (HFNP & _ & _ & _ & Hnrng & Hnlen & _).
  assert (Hn26 : c_n cx < 2 ^ 26) by (destruct Hnrng as [(Hz & _) | (Hz & _)]; lia).
  pose proof HFNP as (_ & _ & _ & _ & _ & Hstk & _).
  pose proof Hstk as (_ & _ & Hceil & Hslo & Hshi & H47 & _).
  unfold LLVMF_STK in Hslo.
  assert (HFb : spZ (c_regs cx) - 352 < lf_F cx <= spZ (c_regs cx) - 320).
  { unfold lf_F. pose proof (Z.mod_pos_bound (spZ (c_regs cx) - 320) 32 ltac:(lia)). lia. }
  pose proof (pal_env B TL) as ((HE0 & HE1) & _).
  assert (HE1' : as_errno B + 4 <= DR_CEIL8) by (unfold DR_CEIL8, kLowMemEnd in *; lia).
  assert (Hfin : In (1, fpos) (frames S3)).
  { pose proof HJ as (_ & _ & (memS & HJ0 & _) & _). pose proof HJ0 as (_ & _ & _ & _ & _ & Hfrs & _).
    rewrite Hfrs, Hown. left. reflexivity. }
  destruct (frames_bounds_x segs B ARx LAWS ly3 S3 Hp3 W mem md 1 fpos HAR Hfin) as (HFF1 & HFF2 & _).
  replace (fs_frame_bytes 1) with 128 in HFF2 by reflexivity.
  set (FF := frame_addr ly3 1 fpos) in *.
  assert (VS : rg_s fr_RG = 0x5d88e0) by reflexivity.
  set (HA := rg_s fr_RG + ASRC * Z.of_nat si) in *.
  assert (HAr : 0x5d88e0 <= HA <= 0x5d88e0 + 288 /\ HA mod 8 = 0).
  { unfold HA. rewrite VS. unfold ASRC. split; [lia|].
    replace (0x5d88e0 + 96 * Z.of_nat si) with ((0xbb11c + 12 * Z.of_nat si) * 8) by lia. apply Z_mod_mult. }
  (* the entry state *)
  remember (Eimg (Ereg regs (de_extra (hs_fd h) (Z.of_nat (length (lm_es m))) (lm_G m)))) as E eqn:HE.
  assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
  assert (HAE : env_agree 32 (Ereg regs (de_extra (hs_fd h) (Z.of_nat (length (lm_es m))) (lm_G m))) E)
    by (rewrite HE; split; [intros q Hq; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
  assert (EEo : forall q (rr : bv 5), Z.of_nat q = bv_unsigned rr -> ew E q = getr regs rr)
    by (intros q rr Hq; subst E; pose proof (bv_unsigned_in_range 5 rr) as Hr5; change (bv_modulus 5) with 32 in Hr5;
        rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_nat; exact Hq).
  assert (E9 : ew E 9 = Z_to_bv 64 (lf_F cx))
    by (rewrite (EEo 9%nat 9%bv eq_refl), (KR0 9%bv ltac:(cbv; tauto)); exact C9).
  assert (VN : rg_nsrc fr_RG = 0x5d87a0) by reflexivity.
  assert (VG : rg_src fr_RG = 0x5d87c0) by reflexivity.
  assert (EO7 : ew E (A_OBJ 7) = Z_to_bv 64 (rg_nsrc fr_RG))
    by (subst E; rewrite Eimg_img by (unfold A_OBJ, A_TEXT, A_LIM; lia);
        rewrite (proj1 (proj2 (proj2 de_hi))); reflexivity).
  assert (EO8 : ew E (A_OBJ 8) = Z_to_bv 64 (rg_src fr_RG))
    by (subst E; rewrite Eimg_img by (unfold A_OBJ, A_TEXT, A_LIM; lia);
        rewrite (proj2 (proj2 (proj2 de_hi))); reflexivity).
  assert (E21 : ew E 21 = Z_to_bv 64 HA)
    by (rewrite (EEo 21%nat 21%bv eq_refl), (KR0 21%bv ltac:(cbv; tauto)); exact R21).
  assert (E26 : ew E 26 = Z_to_bv 64 SB)
    by (rewrite (EEo 26%nat 26%bv eq_refl), (KR0 26%bv ltac:(cbv; tauto)); exact C26).
  assert (E29 : ew E 29 = Z_to_bv 64 (c_n cx - dr_k' cx m))
    by (rewrite (EEo 29%nat 29%bv eq_refl), (KR0 29%bv ltac:(cbv; tauto)); exact R29).
  assert (E32 : ew E 32 = Z_to_bv 64 (hs_fd h))
    by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
  assert (E33 : ew E 33 = Z_to_bv 64 (Z.of_nat (length (lm_es m))))
    by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
  assert (E34 : ew E 34 = Z_to_bv 64 (lm_G m))
    by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 2)).
  assert (U9 : bv_unsigned (ew E 9) = lf_F cx) by (rewrite E9; apply unsigned_lit_small; lia).
  assert (U21 : bv_unsigned (ew E 21) = HA) by (rewrite E21; apply unsigned_lit_small; lia).
  assert (UO7 : bv_unsigned (ew E (A_OBJ 7)) = rg_nsrc fr_RG) by (rewrite EO7; apply unsigned_lit_small; lia).
  assert (UO8 : bv_unsigned (ew E (A_OBJ 8)) = rg_src fr_RG) by (rewrite EO8; apply unsigned_lit_small; lia).
  pose proof HFR as (_ & HAWR & _).
  assert (HS : st_ok_pi segs VAL E ss_de
                 (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + A_dr_arm)) mem (seg_rom segs)))).
  { rewrite restrict_mkst_fx. unfold ss_de. apply pa_entry_st_ok_full.
    - unfold de_sr. rewrite HE.
      apply regs_ok_pin; [apply regs_ok_pin; [apply regs_ok_Eimg_Ereg | intros X; discriminate X |]
                         | intros X; discriminate X |]; rewrite <- HE.
      + rewrite (KR0 23%bv ltac:(cbv; tauto)), C23. apply bv_eq. fold (U E (SOff (A_HI 74) 0)).
        rewrite (U_img_atom E HEI (A_HI 74)) by (unfold A_HI, A_TEXT, A_LIM; lia).
        rewrite (proj1 (de_hi (rc := rc))). unfold w64. apply unsigned_lit_small. unfold HI_G_NSRC; lia.
      + rewrite (KR0 18%bv ltac:(cbv; tauto)), C18. apply bv_eq. fold (U E (SOff (A_HI 75) 0)).
        rewrite (U_img_atom E HEI (A_HI 75)) by (unfold A_HI, A_TEXT, A_LIM; lia).
        rewrite (proj1 (proj2 (de_hi (rc := rc)))). unfold w64. apply unsigned_lit_small. unfold HI_G_SRC; lia.
    - vm_compute. reflexivity.
    - unfold de_regions. repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
        cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      + rewrite U9. split; [lia|]. split; [lia|]. split; [|constructor].
        intros o Ho. exact (HAWR o ltac:(lia)).
      + rewrite U21. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
        constructor; [|constructor].
        apply (chunk_ok_val segs E _ HA 0 4 (SOff 32 0) (hs_fd h));
          [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
        rewrite Z.add_0_r. exact Mfd.
      + rewrite UO7. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
        constructor; [|constructor].
        apply (chunk_ok_val segs E _ (rg_nsrc fr_RG) 0 4 (SOff 33 0) (Z.of_nat (length (lm_es m))));
          [cbn [sv_denot]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
        rewrite Z.add_0_r. exact Mnsrc.
      + rewrite UO8. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
        constructor; [|constructor].
        apply (chunk_ok_val segs E _ (rg_src fr_RG) 0 8 (SOff 34 0) (lm_G m));
          [cbn [sv_denot]; rewrite E34, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
        rewrite Z.add_0_r. exact Msrc.
    - unfold de_regions. cbn [pairwise_disjoint all_disjoint]. unfold extent_disjoint.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite U9, U21, UO7, UO8.
      repeat split; lia.
    - split; [|split; [exact I | exact I]].
      cbn [de_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
      rewrite E9, E21, E26, E32, E33, !unsigned_lit_small by (unfold SB; lia).
      rewrite !Z.pow_0_r, !Z.mod_1_r. change (2 ^ 3) with 8.
      unfold SB. repeat match goal with |- _ /\ _ => split end; lia. }
  assert (EH74 : ew E 354 = Z_to_bv 64 HI_G_NSRC)
    by (subst E; rewrite Eimg_img by (unfold A_TEXT, A_LIM; lia); exact (f_equal (Z_to_bv 64) (proj1 de_hi))).
  assert (EH75 : ew E 355 = Z_to_bv 64 HI_G_SRC)
    by (subst E; rewrite Eimg_img by (unfold A_TEXT, A_LIM; lia); exact (f_equal (Z_to_bv 64) (proj1 (proj2 de_hi)))).
  clear HE.
  assert (HBx : U E de_Bx = SHADOW_OFF)
    by (unfold de_Bx; rewrite (U_atom E 26 SB E26) by (unfold SB; lia); reflexivity).
  assert (SHOK : sh_ok segs de_Bx de_SH E (mrestrict (w_H W) mem)).
  { constructor; [|constructor].
    eapply shent_ok_of_range.
    - apply (azs_range_addressable_x B ARx LAWS ly3 S3 Hp3 W mem md HA 4 HAR).
      destruct HZS as (zr & Hzin & Hz8 & Hzlo & Hzhi). unfold ASRC in Hzhi.
      exists zr. refine (conj Hzin (conj Hz8 _)). lia.
    - exact HBx.
    - rewrite (U_atom E 21 _ E21) by lia. reflexivity.
    - lia.
    - lia.
    - intros x Hx. unfold SHADOW_OFF in *. lia. }
  unfold cfg_at. change (w64 (fr_B0 + fr_arm 2)) with (Z_to_bv 64 (BASE + A_dr_arm)).
  (* 0x84520-0x84538: the shadow check of s5, lw a1 = g_nsrc, sd t4 -> F+144, to the blez *)
  paj_run_tok_x de_RUN HS HJ SHOK de_span.
  { de_awr U9. }
  rename HFr into HFr1, HG0 into HG1. clear HF.
  assert (K1 : forall a, 0 <= a < 2 ^ 64 -> ~ (lf_F cx + DR_N <= a < lf_F cx + DR_N + 8) ->
      aview segs (w_H W) (ms_mem ms) a = aview segs (w_H W) mem a)
    by (intros a Ha Hna; apply (aview_kept_out _ _ _ _ _ HFr1 a Ha); de_nowr U9 Hna).
  assert (P1 : forall a, apresent (w_H W) mem a -> apresent (w_H W) (ms_mem ms) a)
    by (intros a Hpo; exact (de_pres_grows W _ _ a HG1 Hpo)).
  clear HFr1 HG1.
  lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
    assert (S33 : bv_signed (sv_denot Ev (SOff 33 0)) = Z.of_nat (length (lm_es m)))
      by (assert (U33 : U Ev (SOff 33 0) = Z.of_nat (length (lm_es m)))
            by (apply U_atom; [rewrite !ew_ewset_other by lia; exact E33 | lia]);
          unfold U in U33; rewrite bv_signed_small; [exact U33 | rewrite U33; lia]);
    assert (S0 : bv_signed (sv_denot Ev (SLit 0)) = 0) by reflexivity
  end.
  (* blez a1: g_nsrc <= 0 *)
  psrr_branch_tok de_RUN de_BR HS SHOK de_span.
  - cbn [branch_taken] in Hc. rewrite bv_lts_signed, S0, S33 in Hc.
    apply Bool.negb_true_iff, Z.ltb_ge in Hc.
    assert (Hn0 : length (lm_es m) = 0%nat) by lia.
    (* 0x846c8 *)
    paj_run_to_tok_x de_RUNTO HS HJ SHOK de_span A_dr_nf.
    { de_awr U9. }
    assert (K2 : forall a, 0 <= a < 2 ^ 64 -> ~ (lf_F cx + DR_N <= a < lf_F cx + DR_N + 8) ->
        aview segs (w_H W) (ms_mem ms0) a = aview segs (w_H W) mem a)
      by (intros a Ha Hna; rewrite (aview_kept_out _ _ _ _ _ HFr a Ha) by (de_nowr U9 Hna); exact (K1 a Ha Hna)).
    assert (WK : forall a, writable_at segs (arm W mem) a -> writable_at segs (arm W (ms_mem ms0)) a).
    { intros a Hw. apply (writable_kept (w_H W) mem (ms_mem ms0) a); [|exact Hw].
      intros Hpo. exact (de_pres_grows W _ _ a HG0 (P1 a Hpo)). }
    assert (KEEP : forall a, 0 <= a < 2 ^ 64 -> ~ (lf_F cx + DR_N <= a < lf_F cx + DR_N + 8) ->
        abyte_kept W mem W (ms_mem ms0) a)
      by (intros a Ha Hna; split; [exact (K2 a Ha Hna) | apply WK]).
    destruct (de_carry cx W mem (ms_mem ms0) md ly3 S3 Hp3 fpos m HAR Hfin (eq_sym Hnlen) ltac:(lia)
                HFR HMOD HIN HRV HROM KEEP WK) as (HFR2 & HMOD2 & HIN2 & HRV2 & HROM2).
    pose proof (de_flag_kept cx W mem (ms_mem ms0) md ly3 S3 Hp3 fpos HAR Hfin ltac:(lia) KEEP HFL) as HFL2.
    pose proof (st_ok_pi_region_nth _ _ _ 0 _ HS eq_refl) as RG0. cbn [ms_mem restrict] in RG0.
    assert (SVN : sv8 W (ms_mem ms0) (lf_F cx + DR_N) (c_n cx - dr_k' cx m)).
    { unfold sv8, DR_N.
      lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
        apply (field_of_region Ev _ 9%nat (lf_F cx) _ _ _ _ _ 144 8%N (SOff 29 0) (c_n cx - dr_k' cx m) RG0) end.
      - rewrite !ew_ewset_other by lia. exact U9.
      - left. reflexivity.
      - cbn [sv_denot]. rewrite !ew_ewset_other by lia. rewrite E29, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
      - zside.
      - zside. }
    lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
      assert (HAE2 : env_agree 32 (Ereg regs (de_extra (hs_fd h) (Z.of_nat (length (lm_es m))) (lm_G m))) Ev)
        by (split; [intros q Hq; rewrite !ew_ewset_other by lia; exact (proj1 HAE q Hq)
                   | rewrite !ed_ewset; exact (proj2 HAE)]) end.
    pose proof (regs_kept_of_st_ok_pi _ _ _ regs _ DE_KEPT HS HAE2 ltac:(vm_compute; reflexivity)) as KR.
    cbn [ms_regs restrict] in KR.
    assert (KK : forall rr, In rr DE_KEPT -> getr (ms_regs ms0) rr = getr regsD rr).
    { intros rr Hrr. rewrite (KR rr Hrr). apply KR0. cbv [DE_KEPT In] in Hrr.
      repeat (destruct Hrr as [<- | Hrr]; [cbv; tauto|]). destruct Hrr. }
    prreg HS (18%bv : bv 5) Q18. prreg HS (23%bv : bv 5) Q23. rewrite EH75 in Q18. rewrite EH74 in Q23.
    assert (LB : lregs_base cx t FF (ms_regs ms0)).
    { split; [|split; [rewrite (KK 27%bv ltac:(cbv; tauto)); exact R27 | exact Ht]].
      split; [rewrite (KK 2%bv ltac:(cbv; tauto)); exact C2|].
      split; [rewrite (KK 8%bv ltac:(cbv; tauto)); exact C8|].
      split; [rewrite (KK 9%bv ltac:(cbv; tauto)); exact C9|].
      split; [exact Q18|].
      split; [rewrite (KK 19%bv ltac:(cbv; tauto)); exact C19|].
      split; [rewrite (KK 20%bv ltac:(cbv; tauto)); exact C20|].
      split; [exact Q23|].
      split; [rewrite (KK 24%bv ltac:(cbv; tauto)); exact C24|].
      split; [rewrite (KK 25%bv ltac:(cbv; tauto)); exact C25|].
      split; [rewrite (KK 26%bv ltac:(cbv; tauto)); exact C26|].
      split; [rewrite (KK 3%bv ltac:(cbv; tauto)); exact C3|].
      rewrite (KK 4%bv ltac:(cbv; tauto)); exact C4. }
    assert (L28 : getr (ms_regs ms0) 28 = w64 (c_p cx + dr_k' cx m))
      by (rewrite (KK 28%bv ltac:(cbv; tauto)); exact R28).
    pmkst HS. apply SRr_ret.
    right.
      lazymatch goal with |- context [mkCfg (mkst ?r _ ?mm _) ?d] => exists r, mm, d end.
      split; [reflexivity|]. split; [exact HROM2|].
      exists own, ly3, S3, Hp3, k, m, fpos.
      split; [exact HJ|]. split; [exact Hown|]. split; [exact HFR2|]. split; [exact HFL2|]. split; [exact HMOD2|].
      split; [exact HIN2|]. split; [exact HRV2|]. split; [exact HSEP|]. split; [exact HLS|]. split; [exact HNP|]. split; [exact HRI|].
      split; [exact LB|]. split; [exact (conj Hk (conj HO Hop))|]. split; [exact L28|]. split; [exact SVN|].
      exists si, h. split; [exact HPICK|]. intros q Hq. rewrite Hn0 in Hq. cbn in Hq. lia.
  - cbn [branch_taken] in Hc. rewrite bv_lts_signed, S0, S33 in Hc.
    apply Bool.negb_false_iff, Z.ltb_lt in Hc.
    (* 0x8453c-0x8454c: g_src, s->fd, the shadow address of g_src[0], to the scan's head *)
    paj_run_to_tok_x de_RUNTO HS HJ SHOK de_span A_dr_loop.
    { de_awr U9. }
    assert (K2 : forall a, 0 <= a < 2 ^ 64 -> ~ (lf_F cx + DR_N <= a < lf_F cx + DR_N + 8) ->
        aview segs (w_H W) (ms_mem ms0) a = aview segs (w_H W) mem a)
      by (intros a Ha Hna; rewrite (aview_kept_out _ _ _ _ _ HFr a Ha) by (de_nowr U9 Hna); exact (K1 a Ha Hna)).
    assert (WK : forall a, writable_at segs (arm W mem) a -> writable_at segs (arm W (ms_mem ms0)) a).
    { intros a Hw. apply (writable_kept (w_H W) mem (ms_mem ms0) a); [|exact Hw].
      intros Hpo. exact (de_pres_grows W _ _ a HG0 (P1 a Hpo)). }
    assert (KEEP : forall a, 0 <= a < 2 ^ 64 -> ~ (lf_F cx + DR_N <= a < lf_F cx + DR_N + 8) ->
        abyte_kept W mem W (ms_mem ms0) a)
      by (intros a Ha Hna; split; [exact (K2 a Ha Hna) | apply WK]).
    destruct (de_carry cx W mem (ms_mem ms0) md ly3 S3 Hp3 fpos m HAR Hfin (eq_sym Hnlen) ltac:(lia)
                HFR HMOD HIN HRV HROM KEEP WK) as (HFR2 & HMOD2 & HIN2 & HRV2 & HROM2).
    pose proof (de_flag_kept cx W mem (ms_mem ms0) md ly3 S3 Hp3 fpos HAR Hfin ltac:(lia) KEEP HFL) as HFL2.
    pose proof (st_ok_pi_region_nth _ _ _ 0 _ HS eq_refl) as RG0. cbn [ms_mem restrict] in RG0.
    assert (SVN : sv8 W (ms_mem ms0) (lf_F cx + DR_N) (c_n cx - dr_k' cx m)).
    { unfold sv8, DR_N.
      lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
        apply (field_of_region Ev _ 9%nat (lf_F cx) _ _ _ _ _ 144 8%N (SOff 29 0) (c_n cx - dr_k' cx m) RG0) end.
      - rewrite !ew_ewset_other by lia. exact U9.
      - left. reflexivity.
      - cbn [sv_denot]. rewrite !ew_ewset_other by lia. rewrite E29, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
      - zside.
      - zside. }
    lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
      assert (HAE2 : env_agree 32 (Ereg regs (de_extra (hs_fd h) (Z.of_nat (length (lm_es m))) (lm_G m))) Ev)
        by (split; [intros q Hq; rewrite !ew_ewset_other by lia; exact (proj1 HAE q Hq)
                   | rewrite !ed_ewset; exact (proj2 HAE)]) end.
    pose proof (regs_kept_of_st_ok_pi _ _ _ regs _ DE_KEPT HS HAE2 ltac:(vm_compute; reflexivity)) as KR.
    cbn [ms_regs restrict] in KR.
    assert (KK : forall rr, In rr DE_KEPT -> getr (ms_regs ms0) rr = getr regsD rr).
    { intros rr Hrr. rewrite (KR rr Hrr). apply KR0. cbv [DE_KEPT In] in Hrr.
      repeat (destruct Hrr as [<- | Hrr]; [cbv; tauto|]). destruct Hrr. }
    prreg HS (18%bv : bv 5) Q18. prreg HS (23%bv : bv 5) Q23. rewrite EH75 in Q18. rewrite EH74 in Q23.
    assert (LB : lregs_base cx t FF (ms_regs ms0)).
    { split; [|split; [rewrite (KK 27%bv ltac:(cbv; tauto)); exact R27 | exact Ht]].
      split; [rewrite (KK 2%bv ltac:(cbv; tauto)); exact C2|].
      split; [rewrite (KK 8%bv ltac:(cbv; tauto)); exact C8|].
      split; [rewrite (KK 9%bv ltac:(cbv; tauto)); exact C9|].
      split; [exact Q18|].
      split; [rewrite (KK 19%bv ltac:(cbv; tauto)); exact C19|].
      split; [rewrite (KK 20%bv ltac:(cbv; tauto)); exact C20|].
      split; [exact Q23|].
      split; [rewrite (KK 24%bv ltac:(cbv; tauto)); exact C24|].
      split; [rewrite (KK 25%bv ltac:(cbv; tauto)); exact C25|].
      split; [rewrite (KK 26%bv ltac:(cbv; tauto)); exact C26|].
      split; [rewrite (KK 3%bv ltac:(cbv; tauto)); exact C3|].
      rewrite (KK 4%bv ltac:(cbv; tauto)); exact C4. }
    assert (L28 : getr (ms_regs ms0) 28 = w64 (c_p cx + dr_k' cx m))
      by (rewrite (KK 28%bv ltac:(cbv; tauto)); exact R28).
    pmkst HS. apply SRr_ret.
    prreg HS (10%bv : bv 5) Q10. prreg HS (11%bv : bv 5) Q11. prreg HS (12%bv : bv 5) Q12.
    prreg HS (13%bv : bv 5) Q13. prreg HS (22%bv : bv 5) Q22.
    rewrite E34 in Q10, Q22. rewrite E33 in Q11. rewrite E32 in Q12.
    assert (G8 : 0 <= lm_G m / 8 /\ 8 * (lm_G m / 8) <= lm_G m)
      by (split; [apply Z.div_pos; lia | apply Z.mul_div_le; lia]).
    assert (USH : U E (SAlu ALU_ADD (SOff 26 0) (SAlu ALU_SRL (SOff 34 0) (SLit 3))) = SB + lm_G m / 8).
    { rewrite !U_SAlu, (U_atom E 26 SB E26), (U_atom E 34 _ E34), U_lit by (unfold SB; lia). cbn [zalu_raw].
      change (Z.land 3 63) with 3. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8. unfold zcanon, M64.
      rewrite (Z.mod_small (lm_G m / 8)) by lia. rewrite Z.mod_small by (unfold SB; lia). reflexivity. }
    assert (Hsd : sv_denot E (SAlu ALU_ADD (SOff 26 0) (SAlu ALU_SRL (SOff 34 0) (SLit 3))) =
                  alu64 ALU_ADD (ew E 26) (alu64 ALU_SRL (ew E 34) (Z_to_bv 64 3)))
      by (cbn [sv_denot]; rewrite !Z.add_0_r, !Z_to_bv_bv_unsigned; reflexivity).
    rewrite <- Hsd in Q13.
    left. exists (length (lm_es m)).
      lazymatch goal with |- context [mkCfg (mkst ?r _ ?mm _) ?d] => exists r, mm, d end.
      split; [reflexivity|]. split; [exact HROM2|].
      exists own, ly3, S3, Hp3, k, m, fpos.
      split; [exact HJ|]. split; [exact Hown|]. split; [exact HFR2|]. split; [exact HFL2|]. split; [exact HMOD2|].
      split; [exact HIN2|]. split; [exact HRV2|]. split; [exact HSEP|]. split; [exact HLS|]. split; [exact HNP|]. split; [exact HRI|].
      split; [exact LB|]. split; [exact (conj Hk (conj HO Hop))|]. split; [exact L28|]. split; [exact SVN|].
      split.
      { exists si, h. split; [exact HPICK|].
        split; [rewrite (KK 21%bv ltac:(cbv; tauto)); exact R21|].
        split; [exact Q12|]. intros q Hq. lia. }
      split; [lia|]. split; [lia|].
      split; [rewrite Q10; f_equal; unfold AENT; lia|].
      split; [rewrite Q22; f_equal; unfold AENT; lia|].
      split; [rewrite Q11; f_equal; lia|].
      rewrite Q13. apply bv_eq. fold (U E (SAlu ALU_ADD (SOff 26 0) (SAlu ALU_SRL (SOff 34 0) (SLit 3)))).
      rewrite USH. unfold w64. rewrite unsigned_lit_small by (unfold SB; lia). lia.
Qed.

(* ---- the two joins' entry states (0x846c8 and 0x84a80): registers only, and the frame slot F+104 that
   0x84b28 reloads s9 from.  Neither join writes memory, so both runs are over read-only regions. *)
Let RUN := paj_run_x_x (PL := PL_fr) (PI := PB_fr) B PST ARx LAWS G_fr HG 0 [].
Let RUNTO := paj_run_to_x_x (PL := PL_fr) (PI := PB_fr) B PST ARx LAWS G_fr HG 0 [].
(* after a run whose regions have no writable window, the memory is the one it began in *)
Ltac dr_meq HF Em := lazymatch type of HF with frame_of ?E ?rs ?m ?m' =>
  pose proof (frame_of_read_only E rs m m' ltac:(vm_compute; reflexivity) HF) as Em end.

(* (4) 0x846c8: the no-entry path joins the arm's tail. *)
Lemma dr_nf_join : forall cx Hpe t W c,
  lf_base_x B MT XM_LIB RLO RHI fr_live_pre LIBROOM NP G_fr ARx cx Hpe ->
  DST A_dr_nf cx Hpe t (lregs_nf cx t) W c ->
  SRr segs W c (DST A_dr_join cx Hpe (t + 1) (lregs_join cx t)).
Proof.
  intros cx Hpe t W c HB (regs & mem & md & -> & HROM &
    (own & ly3 & S3 & Hp3 & k & m & fpos & HJ & -> & HFR & HFL & HMOD & HIN & HRV & HSEP & HLS & HNP & HRI & HR)).
  destruct HR as (((R2 & R8 & R9 & R18 & R19 & R20 & R23 & R24 & R25 & R26 & R3 & R4) & R27 & Ht)
    & Hatop & R28 & SVN & (si & h & Hpick & Hnom)).
  pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs.
  pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
  pose proof Hatop as (Hk0 & _ & _).
  assert (Hk' : 0 <= dr_k' cx m <= c_n cx)
    by (unfold dr_k'; destruct (Z.ltb_spec (lm_k m + 1) (c_n cx)); lia).
  destruct (dr_nf_entry W regs mem R26) as [HS SHOK].
  remember (Eimg (Ereg regs [])) as E eqn:HE.
  assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
  assert (E28 : ew E 28 = Z_to_bv 64 (c_p cx + dr_k' cx m))
    by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia);
        rewrite (ew_Ereg_nat regs _ 28 28%bv eq_refl); exact R28).
  assert (HAE : env_agree 32 (Ereg regs []) E)
    by (rewrite HE; split; [intros n Hn; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
  clear HE.
  unfold cfg_at. change (w64 (fr_B0 + A_dr_nf)) with (Z_to_bv 64 (BASE + A_dr_nf)).
  (* mv s9,t3 ; j 0x84a80 *)
  paj_run_to_tok_x RUNTO HS HJ SHOK DRspan A_dr_join.
  { apply awr_ok_x_nil. }
  dr_meq HF Em.
  pose proof (regs_kept_of_st_ok_pi _ _ _ regs _ DR_KEPT HS HAE ltac:(vm_compute; reflexivity)) as KR.
  cbn [ms_regs restrict] in KR.
  prreg HS (25%bv : bv 5) Q25. rewrite E28 in Q25.
  pmkst HS. rewrite Em in *.
  apply SRr_ret.
  lazymatch goal with |- context [mkCfg (mkst ?r _ ?mm _) ?d] => exists r, mm, d end.
  split; [reflexivity|]. split; [exact HROM|].
  exists [(1, fpos)], ly3, S3, Hp3, k, (dr_skip m (dr_k' cx m)), fpos.
  split; [exact HJ|]. split; [reflexivity|]. split; [exact HFR|]. split; [exact HFL|]. split; [exact HMOD|].
  split; [exact HIN|]. split; [exact HRV|]. split; [exact HSEP|].
  split; [apply LS_drain_skip; exact HLS|]. split; [exact HNP|].
  split; [apply (RI_drain_skip cx t m si h HRI Hatop Hpick); left; exact Hnom|].
  split; [rewrite (KR 2%bv ltac:(cbv; tauto)); exact R2|].
  split; [rewrite (KR 8%bv ltac:(cbv; tauto)); exact R8|].
  split; [rewrite (KR 9%bv ltac:(cbv; tauto)); exact R9|].
  split; [rewrite (KR 18%bv ltac:(cbv; tauto)); exact R18|].
  split; [rewrite (KR 19%bv ltac:(cbv; tauto)); exact R19|].
  split; [rewrite (KR 20%bv ltac:(cbv; tauto)); exact R20|].
  split; [rewrite (KR 23%bv ltac:(cbv; tauto)); exact R23|].
  split; [rewrite (KR 24%bv ltac:(cbv; tauto)); exact R24|].
  split; [rewrite (KR 26%bv ltac:(cbv; tauto)); exact R26|].
  split; [rewrite (KR 3%bv ltac:(cbv; tauto)); exact R3|].
  split; [rewrite (KR 4%bv ltac:(cbv; tauto)); exact R4|].
  split; [rewrite (KR 27%bv ltac:(cbv; tauto)); exact R27|].
  split; [exact Ht|].
  split; [rewrite Q25; reflexivity|].
  split; [exact SVN|]. exact Hk'.
Qed.
(* Reusable/YCbq.v:2523 shent_ok_of_block, for a range INSIDE a live block rather than at its base: the
   shadow-checked field is at G + AENT * j + 4, the block is the relay's table at G. *)
Lemma dc_shent_block : forall ly S Hp (W : world segs) mem md E Bx (m : nat) p n q lo hi,
  ARx ly S Hp W mem md -> In (p, n) (ablocks B ly S) ->
  U E Bx = SHADOW_OFF -> U E (SOff m 0) = q -> p <= q + lo -> lo <= hi -> q + hi <= p + req_size n ->
  shent_ok segs Bx E (mrestrict (w_H W) mem) (mkSHE m lo hi).
Proof.
  intros ly S Hp W mem md E Bx m p n q lo hi HAR Hin HB Hm Hlo Hle Hhi.
  unfold shent_ok, app_apart. cbn [she_m she_lo she_hi]. rewrite HB, Hm. rewrite <- (aview_rd_of segs).
  destruct (alx_shadow _ _ _ LAWS ly S Hp W mem md p n HAR Hin (hp_off_block_hp0 _ _ HP0 _ _ _ _ _ _ _ _ HAR)) as [Hbs _].
  split.
  - destruct (Z_lt_le_dec lo hi); [|apply range_addressable_nil; lia].
    eapply block_shadow_range; [exact Hbs | lia | lia].
  - destruct (alx_blocks _ _ _ LAWS ly S Hp W mem md p n HAR Hin) as (_ & _ & _ & Happ & _).
    intros a Ha. unfold in_app, SHADOW_OFF, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *. lia.
Qed.
Lemma dc_found_entry : forall ly S Hp (W : world segs) mem md regs F G (j : nat) ef,
  ARx ly S Hp W mem md ->
  getr regs 9 = w64 F -> getr regs 10 = w64 (G + AENT * Z.of_nat j) ->
  getr regs 22 = w64 (G + AENT * Z.of_nat j) -> getr regs 26 = w64 SB ->
  2 ^ 46 <= F -> F + 200 <= 2 ^ 47 -> F mod 32 = 0 ->
  (forall a, F + 40 <= a < F + 48 -> writable_at segs (arm W mem) a) ->
  (forall a, F + 192 <= a < F + 200 -> writable_at segs (arm W mem) a) ->
  In (G, ATABLE) (ablocks B ly S) ->
  4096 <= G + AENT * Z.of_nat j -> (G + AENT * Z.of_nat j) mod 8 = 0 ->
  G + AENT * Z.of_nat j + 8 <= F ->
  G <= G + AENT * Z.of_nat j -> AENT * Z.of_nat j + 8 <= ATABLE ->
  val_mem segs (arm W mem) (G + AENT * Z.of_nat j + 4) 4 ef -> 0 <= ef <= 1 ->
  st_ok_pi segs VAL (Eimg (Ereg regs (dc_extra ef))) ss_dc_found
    (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + A_dr_found)) mem (seg_rom segs)))
  /\ sh_ok segs drBx dc_SH (Eimg (Ereg regs (dc_extra ef))) (mrestrict (w_H W) mem).
Proof.
  intros ly S Hp W mem md regs F G j ef HAR R9 R10 R22 R26 HF0 HF1 HF32 HWL HWA Hin Hq0 Hq8 Hqhi HGq Hjt Mef Hef.
  pose proof (req_size_pos ATABLE ltac:(unfold ATABLE; lia)) as [Hr1 Hr2].
  rewrite restrict_mkst_fx.
  remember (Eimg (Ereg regs (dc_extra ef))) as E eqn:HE.
  assert (EEo : forall q (rr : bv 5), Z.of_nat q = bv_unsigned rr -> ew E q = getr regs rr)
    by (intros q rr Hq; subst E; pose proof (bv_unsigned_in_range 5 rr) as Hr5; change (bv_modulus 5) with 32 in Hr5;
        rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_nat; exact Hq).
  assert (E9 : ew E 9 = Z_to_bv 64 F) by (rewrite (EEo 9%nat 9%bv eq_refl); exact R9).
  assert (E10 : ew E 10 = Z_to_bv 64 (G + AENT * Z.of_nat j)) by (rewrite (EEo 10%nat 10%bv eq_refl); exact R10).
  assert (E22 : ew E 22 = Z_to_bv 64 (G + AENT * Z.of_nat j)) by (rewrite (EEo 22%nat 22%bv eq_refl); exact R22).
  assert (E26 : ew E 26 = Z_to_bv 64 SB) by (rewrite (EEo 26%nat 26%bv eq_refl); exact R26).
  assert (E32 : ew E 32 = Z_to_bv 64 ef)
    by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
  split.
  - unfold ss_dc_found. apply pa_entry_st_ok_full.
    + rewrite HE. apply regs_ok_Eimg_Ereg.
    + vm_compute. reflexivity.
    + repeat apply Forall_cons; try apply Forall_nil; unfold region_ok, dc_rA, dc_rL, dc_rE;
        cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      * rewrite E9, unsigned_lit_small by lia.
        split; [lia|]. split; [lia|].
        split; [intros o Ho; apply HWA; lia | apply Forall_nil].
      * rewrite E9, unsigned_lit_small by lia.
        split; [lia|]. split; [lia|].
        split; [intros o Ho; apply HWL; lia | apply Forall_nil].
      * rewrite E22, unsigned_lit_small by lia.
        split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
        apply Forall_cons; [|apply Forall_nil].
        apply (chunk_ok_val segs E _ (G + AENT * Z.of_nat j) 4 4 (SOff 32 0) ef);
          [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | exact Mef].
    + apply pairwise_disjoint_of_extents. unfold dc_rA, dc_rL, dc_rE, extent_of_region.
      cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite E9, E22, !unsigned_lit_small by lia.
      cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. repeat split; lia.
    + split; [|split; [exact I | exact I]].
      cbn [dc_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
      rewrite E9, E10, E22, E26, E32, !unsigned_lit_small by (unfold SB; lia).
      rewrite !Z.pow_0_r, !Z.mod_1_r. change (2 ^ 5) with 32. change (2 ^ 3) with 8.
      unfold SB. repeat match goal with |- _ /\ _ => split end; lia.
  - unfold sh_ok, dc_SH. constructor; [|constructor].
    apply (dc_shent_block ly S Hp W mem md E drBx 10 G ATABLE (G + AENT * Z.of_nat j) 4 8 HAR Hin).
    + unfold U, drBx. cbn [sv_denot]. rewrite E26, Z.add_0_r, Z_to_bv_bv_unsigned.
      rewrite unsigned_lit_small by (unfold SB; lia). reflexivity.
    + unfold U. cbn [sv_denot]. rewrite E10, Z.add_0_r, Z_to_bv_bv_unsigned.
      rewrite unsigned_lit_small by lia. reflexivity.
    + lia.
    + lia.
    + lia.
Qed.

Lemma dc_carry : forall cx (W : world segs) mem mem' md ly3 S3 Hp3 fpos m,
  ARx ly3 S3 Hp3 W mem md -> In (1, fpos) (frames S3) ->
  Z.of_nat (length (c_pl cx)) = c_n cx ->
  alloc_ceiling + 32768 <= spZ (c_regs cx) <= 2 ^ 47 ->
  aframe_at cx true (frame_addr ly3 1 fpos) W mem -> amodel_at B ly3 S3 W mem m ->
  ainput_at B cx ly3 S3 W mem -> rom_view segs W mem -> jt_rom W mem ->
  (forall a, 0 <= a < 2 ^ 64 -> dc_out cx a -> abyte_kept W mem W mem' a) ->
  (forall a, writable_at segs (arm W mem) a -> writable_at segs (arm W mem') a) ->
  aframe_at cx true (frame_addr ly3 1 fpos) W mem' /\ amodel_at B ly3 S3 W mem' m /\
  ainput_at B cx ly3 S3 W mem' /\ rom_view segs W mem' /\ jt_rom W mem'.
Proof.
  intros cx W mem mem' md ly3 S3 Hp3 fpos m HAR Hfin Hlen Hsp HFR HMOD HIN HRV HJT KEEP WK.
  pose proof dr_ceil_lo as HCL. pose proof (pal_env B TL) as ((HE0 & HE1) & _).
  assert (HFb : spZ (c_regs cx) - 352 < lf_F cx <= spZ (c_regs cx) - 320).
  { unfold lf_F. pose proof (Z.mod_pos_bound (spZ (c_regs cx) - 320) 32 ltac:(lia)). lia. }
  destruct (frames_bounds_x segs B ARx LAWS ly3 S3 Hp3 W mem md 1 fpos HAR Hfin) as (HFF1 & HFF2 & _).
  replace (fs_frame_bytes 1) with 128 in HFF2 by reflexivity.
  assert (FF8 : 0 <= frame_addr ly3 1 fpos / 8 /\ 8 * (frame_addr ly3 1 fpos / 8) <= frame_addr ly3 1 fpos)
    by (split; [apply Z.div_pos; lia | apply Z.mul_div_le; lia]).
  assert (KL : forall a, 0 <= a < DR_CEIL8 -> abyte_kept W mem W mem' a).
  { intros a Ha. apply KEEP; unfold dc_out, DR_AT, DR_CEIL8 in *; lia. }
  split.
  { apply (dc_aframe_kept cx true _ W W mem mem' HFR KEEP WK); unfold DR_CEIL8, SB in *; lia. }
  split; [exact (dr_amodel_kept ly3 S3 Hp3 W mem md W mem' m HAR HMOD HE0
                   ltac:(unfold DR_CEIL8, kLowMemEnd in *; lia) KL)|].
  split; [exact (dr_ainput_kept cx ly3 S3 Hp3 W mem md W mem' HAR HIN Hlen KL)|].
  split; [exact (dr_rom_kept W W mem mem' HRV KL)|].
  exact (dr_jt_kept W W mem mem' HJT KL).
Qed.


(* ---- (5)'s journal kit ---- *)
(* a byte whose ASan view is kept is kept (writable_at reads the memory only at the byte) *)
Lemma dj_bk : forall (W W' : world segs) mem mem' a, 0 <= a < 2 ^ 64 -> (in_img segs a -> inG G_fr a) ->
  aview segs (w_H W') mem' a = aview segs (w_H W) mem a -> abyte_kept W mem W' mem' a.
Proof.
  intros W W' mem mem' a Hr Hg Ha. split; [exact Ha|]. intros Hw.
  destruct (dj_in_img_dec a) as [Hi | Hi]; [exact (GWR _ _ a (Hg Hi))|].
  pose proof (mbyte_of_aview segs (w_H W) (w_H W') mem mem' a Ha) as Hm. unfold mbyte in Hm.
  rewrite (seg_rom_none segs a Hr Hi) in Hm.
  unfold writable_at, wview, arm in *.
  destruct (mrestrict (w_H W') mem' (Z_to_bv 64 a)) eqn:E1, (mrestrict (w_H W) mem (Z_to_bv 64 a)) eqn:E2;
    try discriminate; try exact Hw; try (intros X; discriminate X).
Qed.
(* what a callee's journal keeps, outside its G: the stack above its window, its out window outside the out
   cells, the blocks live before and after outside its footprint, the image bytes that are no allocator static
   and not errno, and the fake frames outside its footprint *)
Lemma dj_keep : forall G XO OUT STK sp FP ly S Hp (W : world segs) mem md own ly' S' Hp' (W' : world segs) mem' md' k a,
  gx_ok segs B G ->
  ajournal_gx_x segs B PST ARx G XO OUT STK sp FP ly S Hp W mem md own ly' S' Hp' W' mem' md' k ->
  0 <= a < 2 ^ 64 -> ~ inG G a ->
  ((alloc_ceiling <= a /\ ~ (sp - STK <= a < sp + XO)) \/
   (sp <= a < sp + XO /\ ~ inFP OUT a) \/
   (exists p n, In (p, n) (ablocks B ly S) /\ In (p, n) (ablocks B ly' S') /\ p <= a < p + req_size n /\
      ~ inFP FP a) \/
   (in_img segs a /\ ~ Exists (in_zr a) (as_owned_static B) /\ ~ (as_errno B <= a < as_errno B + 4) /\
      fp_spares FP a) \/
   (exists cid pos, In (cid, pos) (frames S) /\
      (in_zr a (frame_rng ly (cid, pos)) \/ in_zr a (shadow_addr (frame_addr ly cid pos), fs_frame_bytes cid / 8)) /\
      ~ inFP FP a)) ->
  aview segs (w_H W') mem' a = aview segs (w_H W) mem a.
Proof.
  intros G XO OUT STK sp FP ly S Hp W mem md own ly' S' Hp' W' mem' md' k a HGx HJX Ha HnG Hc.
  pose proof HJX as (HS0 & HX0 & (memS & HJi & Hag) & Hout).
  assert (HmS : aview segs (w_H W) memS a = aview segs (w_H W) mem a).
  { apply (aview_gagree segs G _ _ _ a Hag). apply inGb_false. rewrite unsigned_lit_small by lia. exact HnG. }
  pose proof HJi as (_ & _ & _ & _ & _ & _ & _ & _ & F1 & F2 & F3 & F4 & _).
  destruct Hc as [(H1 & H2) | [(H1 & H2) | [(p & n & H1 & H2 & H3 & H4) | [(H1 & H2 & H3 & H4) | (cid & pos & H1 & H2 & H3)]]]].
  - rewrite (F1 a ltac:(lia) ltac:(lia)). exact HmS.
  - exact (Hout a H1 H2).
  - replace a with (p + (a - p)) in * by lia.
    rewrite (F2 p n (a - p) H1 H2 ltac:(lia) H4). exact HmS.
  - rewrite (F3 a H1 H2 H3 (HPST a H1) H4). exact HmS.
  - rewrite (F4 cid pos a H1 H2 H3). exact HmS.
Qed.
(* the live blocks are pairwise distinct (W_gesture_end.v ablocks_nodup, W4Gesture) *)
Lemma dj_nodup : forall ly S Hp (W : world segs) mem md, ARx ly S Hp W mem md -> List.NoDup (ablocks B ly S).
Proof.
  intros ly S Hp W mem md HAR.
  assert (Hpos : Forall (fun b => 1 <= req_size (snd b)) (ablocks B ly S)).
  { apply Forall_forall. intros [p n] Hin. destruct (alx_blocks _ _ _ LAWS ly S Hp W mem md p n HAR Hin) as (_ & _ & _ & _ & _ & _); pose proof (BLKR ly S Hp W mem md p n HAR Hin) as Hn.
    cbn [snd]. apply req_size_pos. lia. }
  destruct (alx_sep _ _ _ LAWS ly S Hp W mem md HAR) as [Hpo _]. apply pairwise_app_l in Hpo as [Hpo _].
  revert Hpos Hpo. induction (ablocks B ly S) as [|b l IH]; intros Hpos Hpo; [constructor|].
  inversion Hpos as [|b0 l0 Hb Hl]; subst.
  cbn [map pairwise] in Hpo. destruct Hpo as [Hf Hpo]. constructor; [|exact (IH Hl Hpo)].
  intros Hin. rewrite Forall_forall in Hf. specialize (Hf (fst b, req_size (snd b)) (in_map _ _ _ Hin)).
  unfold zdisjoint in Hf. cbn [fst snd] in Hf. lia.
Qed.
(* two distinct live blocks share no byte *)
Lemma dj_apart : forall ly S Hp (W : world segs) mem md p n q r a,
  ARx ly S Hp W mem md -> In (p, n) (ablocks B ly S) -> In (q, r) (ablocks B ly S) -> (p, n) <> (q, r) ->
  p <= a < p + req_size n -> ~ (q <= a < q + req_size r).
Proof.
  intros ly S Hp W mem md p n q r a HAR H1 H2 Hne Ha Hb.
  pose proof (sep_blocks_x segs B ARx LAWS ly S Hp W mem md p n q r HAR H1 H2 Hne) as Hd.
  unfold zdisjoint in Hd. cbn [fst snd] in Hd. lia.
Qed.
(* the bytes of a range inside a live block are writable (they are present) *)
Lemma dr_awr_of_garr8 : forall ly S Hp (W : world segs) mem md p n a (l : list Z),
  ARx ly S Hp W mem md -> In (p, n) (ablocks B ly S) -> p <= a -> a + Z.of_nat (length l) <= p + req_size n ->
  garr8 segs (arm W mem) a l -> awr W mem a (Z.of_nat (length l)).
Proof.
  intros ly S Hp W mem md p n a l HAR Hin Hpo Hq _ i Hi. unfold arm. apply (apresent_writable segs).
  destruct (alx_blocks _ _ _ LAWS ly S Hp W mem md p n HAR Hin) as (_ & _ & _ & _ & Hpr & _).
  exact (proj1 (Hpr (a + i) ltac:(lia))).
Qed.

(* copied from W_LLVMFuzzerTestOneInput_exit.v lx_afn_pre_at (W8SegExit) *)
Lemma dr_afn_pre_at : forall cx Hpe ly3 S3 Hp3 fpos k (W : world segs) mem md regs STK1,
  lf_base_x B MT XM_LIB RLO RHI fr_live_pre LIBROOM NP G_fr ARx cx Hpe ->
  ajournal_gx_x segs B PST ARx G_fr 0 [] LLVMF_STK (spZ (c_regs cx)) (lf_FP fr_FP cx)
    (c_ly cx) (c_S cx) Hpe (c_W cx) (c_mem cx) (c_md cx) [(1, fpos)] ly3 S3 Hp3 W mem md k ->
  aframe_at cx false (frame_addr ly3 1 fpos) W mem ->
  spZ regs = lf_F cx -> YK0s.ret_ok (getr regs 1) -> 4096 <= raZ regs ->
  getr regs 3 = w64 (as_gp B) -> getr regs 4 = w64 (as_tp B) -> getr regs 8 = getr (c_regs cx) 2 ->
  0 <= STK1 -> STK1 + 352 <= LLVMF_STK ->
  exists ch, afn_pre_x segs B ARx STK1 ly3 S3 Hp3 W regs mem md ch.
Proof.
  intros cx Hpe ly3 S3 Hp3 fpos k W mem md regs STK1 HB HJ HFR Hsp Hret Hra4 Hgp Htp Hs0 HSTK0 HSTKb.
  destruct HB as (_ & HPRE).
  assert (HPREE : afn_pre_x segs B ARx LLVMF_STK (c_ly cx) (c_S cx) Hpe (c_W cx) (c_regs cx) (c_mem cx) (c_md cx) [])
    by (unfold fr_lib_pre_cf_x in HPRE; tauto).
  pose proof HPREE as (HAR0 & Hra0 & Hra40 & Hgp0 & Htp0 & Hstk0 & Hpres0 & Hch0 & HQT0).
  pose proof Hstk0 as (Hal16 & Hslo0 & Hceil0 & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
  destruct (ajournal_gx_inner_x segs B PST ARx G_fr 0 [] LLVMF_STK (spZ (c_regs cx)) (lf_FP fr_FP cx)
    (c_ly cx) (c_S cx) Hpe (c_W cx) (c_mem cx) (c_md cx) [(1, fpos)] ly3 S3 Hp3 W mem md k HJ) as (memS & HJ0 & HSG).
  rewrite !Z.add_0_r in HJ0.
  (* the frame base is 320 or 336 below the entry sp, and 32-aligned *)
  set (sp0 := spZ (c_regs cx)) in *.
  assert (HF32 : lf_F cx = sp0 - 320 - (sp0 - 320) mod 32) by reflexivity.
  pose proof (Z.mod_pos_bound (sp0 - 320) 32 ltac:(lia)) as Hmb.
  assert (Ho16 : (lf_F cx - sp0) mod 16 = 0).
  { rewrite HF32.
    replace (sp0 - 320 - (sp0 - 320) mod 32 - sp0) with (- (320 + (sp0 - 320) mod 32)) by lia.
    assert (H32 : (sp0 - 320) mod 32 = 0 \/ (sp0 - 320) mod 32 = 16).
    { pose proof (Z.mod_divide (sp0 - 320) 16 ltac:(lia)) as _.
      assert (E16 : (sp0 - 320) mod 16 = 0)
        by (replace (sp0 - 320) with (sp0 + (-20) * 16) by lia; rewrite Z.mod_add by lia; exact Hal16).
      pose proof (Z.div_mod ((sp0 - 320) mod 32) 16 ltac:(lia)) as D.
      assert (E2 : ((sp0 - 320) mod 32) mod 16 = 0)
        by (rewrite <- Znumtheory.Zmod_div_mod by (try lia; exists 2; reflexivity); exact E16).
      rewrite E2, Z.add_0_r in D.
      assert (Hq : (sp0 - 320) mod 32 / 16 = 0 \/ (sp0 - 320) mod 32 / 16 = 1) by lia.
      destruct Hq as [Hq | Hq]; rewrite Hq in D; lia. }
    destruct H32 as [H32 | H32]; rewrite H32; reflexivity. }
  assert (HoNeg : lf_F cx - sp0 <= 0) by (rewrite HF32; lia).
  assert (HoBud : STK1 - (lf_F cx - sp0) <= LLVMF_STK) by (rewrite HF32; lia).
  (* the chain: the entry's, with this frame pushed *)
  pose proof (aview_above_of_journal_x (PI := PB_fr) B PST ARx LLVMF_STK sp0 (lf_FP fr_FP cx)
    (c_ly cx) (c_S cx) Hpe (c_W cx) memS (c_md cx) [(1, fpos)] ly3 S3 Hp3 W mem md k HJ0) as HAB.
  pose proof HFR as (HSV & _).
  assert (Hra8 : rdword (aview segs (w_H W) mem) (sp0 - 8) = Some (bv_unsigned (getr (c_regs cx) 1))).
  { apply (rdword_of_val_mem segs (w_H W) mem); [exact (HSV 8 1 ltac:(left; reflexivity)) |].
    pose proof (bv_unsigned_in_range 64 (getr (c_regs cx) 1)) as Hr.
    change (bv_modulus 64) with (2 ^ 64) in Hr. lia. }
  assert (Hs016 : rdword (aview segs (w_H W) mem) (sp0 - 16) = Some (bv_unsigned (getr (c_regs cx) 8))).
  { apply (rdword_of_val_mem segs (w_H W) mem); [exact (HSV 16 8 ltac:(right; left; reflexivity)) |].
    pose proof (bv_unsigned_in_range 64 (getr (c_regs cx) 8)) as Hr.
    change (bv_modulus 64) with (2 ^ 64) in Hr. lia. }
  clear Hpres0.
  assert (HTOPeq : ly_top ly3 = ly_top (c_ly cx)).
  { pose proof HJ0 as (_ & Hly & _). pose proof Hly as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & _). exact Etop. }
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  assert (Hsp8 : sp0 mod 8 = 0).
  { assert (Hq : sp0 = 16 * (sp0 / 16)) by (pose proof (Z.div_mod sp0 16 ltac:(lia)); lia).
    rewrite Hq. replace (16 * (sp0 / 16)) with ((2 * (sp0 / 16)) * 8) by ring. apply Z_mod_mult. }
  assert (HCH : exists ch, achain ly3 (aview segs (w_H W) mem) (lf_F cx) sp0 ch).
  { destruct (Z_lt_ge_dec sp0 (ly_top (c_ly cx) - 16)) as [Hlt | Hge].
    - exists ((sp0, bv_unsigned (getr (c_regs cx) 1), bv_unsigned (getr (c_regs cx) 8)) :: []).
      apply (achain_ly_top (c_ly cx) ly3 _ _ _ _ ltac:(exact HTOPeq)).
      eapply (achain_push (c_ly cx) (aview segs (w_H (c_W cx)) (c_mem cx)) (aview segs (w_H W) mem)
        sp0 (bv_unsigned (getr (c_regs cx) 8)) (bv_unsigned (getr (c_regs cx) 1)) [] (lf_F cx));
        [ exact Hch0 | lia
        | intros a Ha; rewrite (HAB a ltac:(lia)); apply HSG; rewrite unsigned_lit_small by lia; intros HGa;
          pose proof (inG_low segs B pa_segs_low G_fr a HG HGa); lia
        | exact Hra8 | exact Hs016
        | unfold raZ in Hra40; lia | lia | exact Hsp8 | exact Hlt | rewrite HF32; lia ].
    - exists []. left. split; [right; left; rewrite HTOPeq; lia | reflexivity]. }
  destruct HCH as (ch & HCH).
  exists ch.
  eapply (afn_pre_x_at segs B PST ARx LLVMF_STK sp0 (lf_FP fr_FP cx) (c_ly cx) (c_S cx) Hpe (c_W cx) memS (c_md cx)
    [(1, fpos)] ly3 S3 Hp3 W mem md k regs STK1 (lf_F cx - sp0) _ HJ0);
    [ rewrite Hsp; lia | exact Ho16 | exact HoNeg | exact HSTK0 | exact HoBud | exact Hret | exact Hra4
    | exact Hgp | exact Htp | ].
  rewrite Hsp. replace (s0Z regs) with sp0 by (unfold s0Z, sp0, spZ; rewrite Hs0; reflexivity).
  exact HCH.
Qed.
(* the cut's STKR (fr_lib_pre_cf's last conjunct) at a callee's sp F = lf_F cx: the arm's own window
   [sp0 - LLVMF_STK, sp0) is present (the journal's presence clause), and above sp0 the journal keeps the entry's view
   (its view clause above alloc_ceiling outside the window; G_fr is image, below it) *)
Lemma dr_stkr : forall cx Hpe fpos ly S Hp (W : world segs) mem md k,
  lf_base_x B MT XM_LIB RLO RHI fr_live_pre LIBROOM NP G_fr ARx cx Hpe ->
  ajournal_gx_x segs B PST ARx G_fr 0 [] LLVMF_STK (spZ (c_regs cx)) (lf_FP fr_FP cx)
    (c_ly cx) (c_S cx) Hpe (c_W cx) (c_mem cx) (c_md cx) [(1, fpos)] ly S Hp W mem md k ->
  forall a, lf_F cx <= a < ly_top ly -> aview segs (w_H W) mem a <> None.
Proof.
  intros cx Hpe fpos ly S Hp W mem md k HB HJ a Ha.
  pose proof dr_ceil_lo as HCL.
  destruct HB as (_ & HPRE).
  pose proof HPRE as (HFNP & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & STKR & _).
  pose proof HFNP as (_ & _ & _ & _ & _ & Hstk & _).
  pose proof Hstk as (Hal16 & _ & Hceil & Hslo & Hshi & H47 & _ & Htop & Htop2).
  unfold LLVMF_STK in Hslo.
  destruct (ajournal_gx_inner_x segs B PST ARx G_fr 0 [] LLVMF_STK (spZ (c_regs cx)) (lf_FP fr_FP cx)
    (c_ly cx) (c_S cx) Hpe (c_W cx) (c_mem cx) (c_md cx) [(1, fpos)] ly S Hp W mem md k HJ) as (memS & HJ0 & HSG).
  rewrite !Z.add_0_r in HJ0.
  pose proof HJ0 as (_ & HLY & _ & _ & _ & _ & _ & _ & F1 & _ & _ & _ & _ & Hpres & _).
  assert (Etop : ly_top ly = ly_top (c_ly cx)) by (pose proof HLY as (_ & _ & _ & _ & _ & _ & _ & _ & X & _); exact X).
  pose proof (Z.mod_pos_bound (spZ (c_regs cx) - 320) 32 ltac:(lia)) as HFm.
  assert (HFb : spZ (c_regs cx) - 352 < lf_F cx) by (unfold lf_F; lia).
  destruct (Z_lt_le_dec a (spZ (c_regs cx))) as [Hlt | Hge].
  - apply aview_some_of_apresent. apply Hpres. unfold LLVMF_STK. lia.
  - rewrite (F1 a ltac:(lia) ltac:(lia)). rewrite HSG.
    + apply STKR. rewrite <- Etop. lia.
    + rewrite unsigned_lit_small by lia. intros HGa. pose proof (pa_segs_low a (proj1 (HG a HGa))).
      unfold kLowMemEnd in *. lia.
Qed.


(* A call to a program function inside this walk (W_gesture_end.v gx_callS, W4Gesture), with the callee's afn_pre
   given (dr_afn_pre_at builds it at sp = F): the callee's contract applied at its entry, and its journal - with XO /
   OUT, an out-parameter cell of the caller's frame inside the callee's raised window - composed into the caller's
   (W_journal.v ajournal_gx_sub). *)
Lemma dr_callZ : forall G W (regsc : bvmap 5 word) memc pc STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k STK1 FP1
  XO1 OUT1 (o : Z) raw ch1
  (K : alayout -> astate -> list Z -> world segs -> bvmap 5 word -> (word -> option byte) -> Model -> Prop),
  gx_ok segs B G ->
  ajournal_gx_x segs B PST ARx G 0 [] STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W memc mdc k ->
  spZ regsc = sp0 + o -> o <= 0 -> STK1 - o <= STK ->
  0 <= XO1 -> o + XO1 <= 0 -> (forall a, inFP OUT1 a -> sp0 - STK <= a < sp0) ->
  getr regsc 1 = raw ->
  afn_pre_x segs B ARx STK1 lyc Sc Hpc W regsc memc mdc ch1 ->
  SRr segs W (mkCfg (mkst regsc pc memc (seg_rom segs)) mdc)
   (fun W2 c2 => exists ly2 S2 Hp2 regs2 mem2 md2 k1,
    c2 = mkCfg (mkst regs2 raw mem2 (seg_rom segs)) md2 /\
    ajournal_gx_x segs B PST ARx G XO1 OUT1 STK1 (spZ regsc) FP1 lyc Sc Hpc W memc mdc [] ly2 S2 Hp2 W2 mem2 md2 k1 /\
    aregs_preserved regsc regs2 /\ K ly2 S2 Hp2 W2 regs2 mem2 md2) ->
  (forall a, inFP FP1 a -> (inFP FP a /\ exists b n, In (b, n) (ablocks B lyc Sc) /\ b <= a < b + req_size n) \/
   in_tmp_block (ablocks B ly S) (ablocks B lyc Sc) a) ->
  SRr segs W (mkCfg (mkst regsc pc memc (seg_rom segs)) mdc)
  (fun W2 c2 => exists ly2 S2 Hp2 regs2 mem2 md2 k1,
   c2 = mkCfg (mkst regs2 raw mem2 (seg_rom segs)) md2 /\
   ajournal_gx_x segs B PST ARx G 0 [] STK sp0 FP ly S Hp W0 mem md own ly2 S2 Hp2 W2 mem2 md2 (k + k1) /\
   ajournal_gx_x segs B PST ARx G XO1 OUT1 STK1 (sp0 + o) FP1 lyc Sc Hpc W memc mdc [] ly2 S2 Hp2 W2 mem2 md2 k1 /\
   aregs_preserved regsc regs2 /\ K ly2 S2 Hp2 W2 regs2 mem2 md2).
Proof.
  intros G W regsc memc pc STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k STK1 FP1 XO1 OUT1 o raw ch1 K
    HGx HJ Hsp Hneg Hbud HXO HXO2 HOUT Hra HPRE Hcallee HF.
  eapply SRr_mono; [exact Hcallee|].
  cbv beta. intros W2 c2 _ (ly2 & S2 & Hp2 & regs2 & mem2 & md2 & k1 & -> & HJ1 & HP & HK).
  exists ly2, S2, Hp2, regs2, mem2, md2, k1. split; [reflexivity|].
  rewrite Hsp in HJ1.
  split; [| split; [exact HJ1 | split; [exact HP | exact HK]]].
  change own with ([] ++ own).
  pose proof HJ as (HS0 & _).
  pose proof HPRE as (_ & _ & _ & _ & _ & (_ & HS1 & _) & _).
  eapply (ajournal_gx_sub_x segs B PST ARx LAWS pa_segs_low); [exact HJ | exact HJ1 | lia | lia | lia | | exact HGx | exact HF].
  intros a Ha. left. exact (HOUT a Ha).
Qed.
Ltac dj_cs := unfold acallee_saved;
  match goal with |- context [bv_unsigned ?r] => let v := eval vm_compute in (bv_unsigned r) in
    change (bv_unsigned r) with v end; lia.
Lemma dj_alist_fp : forall ly S (W : world segs) mem LA l lines,
  alist_at B ly S W mem LA l lines -> fp_in (alist_fp LA l) (fun a => LA <= a < LA + 16) (alist_blks l).
Proof.
  intros ly S W mem LA l lines (_ & _ & _ & _ & H5 & H6 & _).
  unfold alist_fp, alist_blks, gfp.
  apply dra_fp_in_cons; [intros a Ha; left; exact Ha|].
  apply dj_fp_in_app.
  - destruct (Z.eqb_spec (hl_cap l) 0) as [E | E]; [apply dra_fp_in_nil|].
    destruct H6 as [(Hc & _) | (Hc & Hin & Hj & Hg)]; [lia|].
    apply dra_fp_in_cons; [|apply dra_fp_in_nil].
    intros a Ha. right. exists (hl_v l, AREC * hl_cap l).
    split; [apply in_or_app; left; left; reflexivity|]. cbn [fst snd].
    rewrite dra_bzs_length, length_app, dra_concat_text_len in Ha. unfold hl_n in Hj. unfold AREC in *. lia.
  - apply dra_fp_in_map. intros r Hr a Ha. cbn [fst snd] in Ha.
    rewrite dra_bzs_length, length_app in Ha. cbn [length] in Ha.
    right. exists (fst r, Z.of_nat (length (snd r)) + 1).
    split; [apply in_or_app; right; apply in_map_iff; exists r; split; [reflexivity | exact Hr]|].
    cbn [fst snd]. lia.
Qed.
Lemma dj_asrc_fp : forall ly S (W : world segs) mem HA h,
  asrc_at B ly S W mem HA h -> fp_in (asrc_fp HA h) (fun a => HA <= a < HA + ASRC) (asrc_blks h).
Proof.
  intros ly S W mem HA h
    (_ & _ & _ & _ & _ & _ & _ & _ & _ & H10 & _ & _ & _ & _ & _ & _ & _ & _ & H19 & _ & _ & H22 & H23 & _).
  unfold asrc_fp, asrc_blks.
  apply dra_fp_in_cons; [intros a Ha; left; exact Ha|].
  unfold gfp at 1. apply dra_fp_in_cons.
  { intros a Ha. right. exists (hs_partial h, APARTIAL). split; [left; reflexivity|]. cbn [fst snd].
    rewrite dra_bzs_length in Ha. lia. }
  apply dj_fp_in_app; [|apply dj_fp_in_app].
  - apply (dj_fp_in_mono _ _ _ _ _ (dj_alist_fp ly S W mem (HA + 16) (hs_pending h) false H10)).
    + intros a Ha. unfold ASRC. lia.
    + intros b Hb. right. apply in_or_app. left. exact Hb.
  - apply (dj_fp_in_mono _ _ _ _ _ (dj_alist_fp ly S W mem (HA + 64) (hs_expected h) true H22)).
    + intros a Ha. unfold ASRC. lia.
    + intros b Hb. right. apply in_or_app. right. apply in_or_app. left. exact Hb.
  - apply (dj_fp_in_mono _ _ _ _ _ (dj_alist_fp ly S W mem (HA + 80) (hs_held h) true H23)).
    + intros a Ha. unfold ASRC. lia.
    + intros b Hb. right. apply in_or_app. right. apply in_or_app. right. exact Hb.
Qed.
Lemma dj_aentry_fp : forall ly S (W : world segs) mem e,
  aentry_ok B ly S W mem e -> Z.of_nat (length (re_keys e)) <= re_nheld e ->
  fp_in (aentry_fp e) (fun _ => False) (aentry_blks e).
Proof.
  intros ly S W mem e (_ & _ & _ & _ & _ & _ & H7 & _ & _ & H10 & _ & H12 & _ & _ & _) Hk.
  unfold aentry_fp, aentry_blks, gfp.
  apply dj_fp_in_app.
  - destruct (Z.eqb_spec (re_cap e) 0) as [E | E]; [apply dra_fp_in_nil|].
    destruct H10 as [(Hc & _) | (Hc & Hin & Hj & Hg)]; [lia|].
    apply dra_fp_in_cons; [|apply dra_fp_in_nil].
    intros a Ha. right. exists (re_buf e, re_cap e).
    split; [apply in_or_app; left; left; reflexivity|]. cbn [fst snd].
    rewrite dra_bzs_length, length_app in Ha. lia.
  - apply dra_fp_in_cons.
    + intros a Ha. rewrite dra_bzs_length, dra_key_ptrs_len in Ha.
      destruct H12 as [(Hz & Hkeys) | (Hz & Hin & Hk1 & Hk2 & Hg)].
      * rewrite Hkeys in Ha. cbn [length] in Ha. lia.
      * right. exists (re_hp e, re_kh e). split.
        -- apply in_or_app. right. apply in_or_app. left. rewrite (proj2 (Z.eqb_neq _ _) Hz). left. reflexivity.
        -- cbn [fst snd]. lia.
    + apply dra_fp_in_map. intros k Hk' a Ha. cbn [fst snd] in Ha.
      rewrite dra_bzs_length, length_app in Ha. cbn [length] in Ha.
      right. eexists.
      split; [apply in_or_app; right; apply in_or_app; right; apply in_map_iff; exists k; split; [reflexivity | exact Hk']|].
      cbn [fst snd]. lia.
Qed.
Lemma dj_arelay_fp : forall ly S (W : world segs) mem G es,
  arelay_at B fr_RG ly S W mem G es ->
  Forall (fun e => Z.of_nat (length (re_keys e)) <= re_nheld e) es ->
  fp_in (arelay_fp fr_RG G es)
    (fun a => rg_src fr_RG <= a < rg_src fr_RG + 8 \/ rg_nsrc fr_RG <= a < rg_nsrc fr_RG + 4 \/
              rg_capsrc fr_RG <= a < rg_capsrc fr_RG + 4)
    (arelay_blks G es).
Proof.
  intros ly S W mem G es (_ & _ & _ & _ & _ & _ & _ & _ & _ & H10 & _) Hk.
  unfold arelay_fp, arelay_blks.
  apply dra_fp_in_cons; [intros a Ha; left; left; exact Ha|].
  apply dra_fp_in_cons; [intros a Ha; left; right; left; exact Ha|].
  apply dra_fp_in_cons; [intros a Ha; left; right; right; exact Ha|].
  apply dra_fp_in_cons; [intros a Ha; right; exists (G, ATABLE); split; [left; reflexivity | cbn [fst snd]; lia]|].
  apply dra_fp_in_concat. intros e He. rewrite Forall_forall in H10, Hk.
  apply (dj_fp_in_mono _ _ _ _ _ (dj_aentry_fp ly S W mem e (H10 e He) (Hk e He))).
  - intros a Ha. destruct Ha.
  - intros b Hb. right. apply in_concat. exists (aentry_blks e).
    split; [apply in_map_iff; exists e; split; [reflexivity | exact He] | exact Hb].
Qed.
Lemma dj_aout_fp : forall ly S (W : world segs) mem c O mx no cap out,
  aout_at B fr_RG ly S W mem c O mx no cap out ->
  fp_in (aout_fp B fr_RG cap out) (fun a => exists r, In r (aout_fp B fr_RG 0 0) /\ fst r <= a < snd r)
    (aout_blks cap out).
Proof.
  intros ly S W mem c O mx no cap out _.
  assert (E : aout_fp B fr_RG cap out = aout_fp B fr_RG 0 0 ++ (if cap =? 0 then [] else [(out, out + cap)]))
    by reflexivity.
  rewrite E. apply dj_fp_in_app.
  - intros r Hr a Ha. left. exists r. split; [exact Hr | exact Ha].
  - unfold aout_blks. destruct (Z.eqb_spec cap 0) as [Ec | Ec]; [apply dra_fp_in_nil|].
    apply dra_fp_in_cons; [|apply dra_fp_in_nil].
    intros a Ha. right. exists (out, cap). split; [left; reflexivity | cbn [fst snd]; lia].
Qed.

(* ---- the state at `jal pthread_mutex_lock` (0x84a50) on the eof = 0 path: lcut's facts at the found entry,
   with s9 = the new in.p, F+192 = 0 (at), F+40 = &g_lock, a0 = &g_lock, ra = 0x84a54 ---- *)
Definition DLK (cx : lfcx) (Hpe : list Z) (t : Z) (m : lmod) (j si : nat) (h : hsrc) (fpos : Z) (ly3 : alayout) (S3 : astate) (Hp3 : list Z)
  (k : Z) : world segs -> config -> Prop :=
  fun W c => exists regs mem md,
  c = mkCfg (mkst regs (Z_to_bv 64 (SIGMA WS_pthread_mutex_lock)) mem (seg_rom segs)) md /\
  ajournal_gx_x segs B PST ARx G_fr 0 [] LLVMF_STK (spZ (c_regs cx)) (lf_FP fr_FP cx)
    (c_ly cx) (c_S cx) Hpe (c_W cx) (c_mem cx) (c_md cx) [(1, fpos)] ly3 S3 Hp3 W mem md k /\
  aframe_at cx true (frame_addr ly3 1 fpos) W mem /\ sv8 W mem (frame_addr ly3 1 fpos + 120) (flag_addr ly3 1 fpos) /\
  amodel_at B ly3 S3 W mem m /\
  ainput_at B cx ly3 S3 W mem /\ rom_view segs W mem /\ jt_rom W mem /\
  ablocks_sep B fr_FP cx m ly3 S3 /\ LSx cx t m ly3 S3 /\ NP S3 /\ RINV cx t m /\
  dr_at_op cx m /\ dr_pick cx m si h /\ (j < length (lm_es m))%nat /\
  re_fd (nth j (lm_es m) dr_e0) = hs_fd h /\ re_eof (nth j (lm_es m) dr_e0) = 0 /\
  sv8 W mem (lf_F cx + DR_N) (c_n cx - dr_k' cx m) /\ sv8 W mem (lf_F cx + DR_AT) 0 /\
  sv8 W mem (lf_F cx + 40) (rg_lock fr_RG) /\
  getr regs 1 = Z_to_bv 64 (BASE + A_dc_r1) /\ getr regs 10 = w64 (rg_lock fr_RG) /\
  getr regs 2 = w64 (lf_F cx) /\ getr regs 8 = getr (c_regs cx) 2 /\ getr regs 9 = w64 (lf_F cx) /\
  getr regs 18 = w64 HI_G_SRC /\ getr regs 19 = w64 (frame_addr ly3 1 fpos + 32) /\ getr regs 20 = w64 10 /\
  getr regs 23 = w64 HI_G_NSRC /\ getr regs 24 = w64 (SB + frame_addr ly3 1 fpos / 8) /\ getr regs 26 = w64 SB /\
  getr regs 3 = w64 (as_gp B) /\ getr regs 4 = w64 (as_tp B) /\ getr regs 27 = w64 t /\ 0 <= t < OPS_MAX /\
  getr regs 21 = w64 (rg_s fr_RG + ASRC * Z.of_nat si) /\ getr regs 22 = w64 (lm_G m + AENT * Z.of_nat j) /\
  getr regs 25 = w64 (c_p cx + dr_k' cx m).

(* ---- the eof = 0 path, cut at each return point.  dc_regs: the registers the six calls keep (all callee-saved);
   amodel_ne: amodel_at with g_lock's state a parameter and errno's value free (check_no_loss_read,
   check_no_loss and check_shape_done keep no errno byte, so the stream's ctl takes errno's value at the end) ---- *)
Definition dc_regs (cx : lfcx) (t : Z) (m : lmod) (j si : nat) (FF : Z) (regs : bvmap 5 word) : Prop :=
  getr regs 2 = w64 (lf_F cx) /\ getr regs 8 = getr (c_regs cx) 2 /\ getr regs 9 = w64 (lf_F cx) /\
  getr regs 18 = w64 HI_G_SRC /\ getr regs 19 = w64 (FF + 32) /\ getr regs 20 = w64 10 /\
  getr regs 23 = w64 HI_G_NSRC /\ getr regs 24 = w64 (SB + FF / 8) /\ getr regs 26 = w64 SB /\
  getr regs 3 = w64 (as_gp B) /\ getr regs 4 = w64 (as_tp B) /\ getr regs 27 = w64 t /\ 0 <= t < OPS_MAX /\
  getr regs 21 = w64 (rg_s fr_RG + ASRC * Z.of_nat si) /\ getr regs 22 = w64 (lm_G m + AENT * Z.of_nat j) /\
  getr regs 25 = w64 (c_p cx + dr_k' cx m).
Definition amodel_ne (ly : alayout) (S : astate) (W : world segs) (mem : word -> option byte) (m : lmod)
  (held : bool) : Prop :=
  length (lm_hs m) = 4%nat /\ (forall i, (i < 4)%nat -> aslot B ly S W mem i (nth i (lm_hs m) None)) /\
  arelay_at B fr_RG ly S W mem (lm_G m) (lm_es m) /\
  (exists ev, aout_at B fr_RG ly S W mem (dc_ctl (lm_c m) ev) (lm_O m) (lm_mx m) (Z.of_nat (length (lm_O m)))
                (lm_cap m) (lm_out m)) /\
  agone_at fr_RG W mem (lm_gn m) /\ alock_at fr_RG W mem held /\ awake_at fr_RG W mem /\
  val_mem segs (arm W mem) AG_NFD 4 (lm_nfd m) /\ awr W mem AG_NFD 4 /\ 0 <= lm_nfd m <= OPS_MAX /\
  val_mem segs (arm W mem) AG_THREAD_UP 1 0 /\
  (exists lst, val_mem segs (arm W mem) AG_LISTEN 4 lst) /\ awr W mem AG_LISTEN 4.
(* a state of the eof = 0 path at BASE + pc: the journal from the entry, the frame and fake frame (with lcut's flag
   word at FF + 120), the input, the ROM and the jump table, in.n at F+144, `at` = A at F+192, &g_lock at F+40, the
   model mc (lock state held), its blocks' separation, and the entries' key-count bound *)
Definition dc_at (cx : lfcx) (Hpe : list Z) (t : Z) (m : lmod) (j si : nat) (fpos FF pc : Z) (ly : alayout) (S : astate) (Hp : list Z)
  (mc : lmod) (held : bool) (A : Z) : world segs -> config -> Prop :=
  fun W c => exists regs mem md k,
    c = mkCfg (mkst regs (Z_to_bv 64 (BASE + pc)) mem (seg_rom segs)) md /\
    dc_regs cx t m j si FF regs /\
    ajournal_gx_x segs B PST ARx G_fr 0 [] LLVMF_STK (spZ (c_regs cx)) (lf_FP fr_FP cx)
      (c_ly cx) (c_S cx) Hpe (c_W cx) (c_mem cx) (c_md cx) [(1, fpos)] ly S Hp W mem md k /\
    frame_addr ly 1 fpos = FF /\
    aframe_at cx true FF W mem /\ sv8 W mem (FF + 120) (flag_addr ly 1 fpos) /\
    ainput_at B cx ly S W mem /\ rom_view segs W mem /\ jt_rom W mem /\
    sv8 W mem (lf_F cx + DR_N) (c_n cx - dr_k' cx m) /\ sv8 W mem (lf_F cx + DR_AT) A /\
    sv8 W mem (lf_F cx + 40) (rg_lock fr_RG) /\
    amodel_ne ly S W mem mc held /\ ablocks_sep B fr_FP cx mc ly S /\
    Forall (fun e => Z.of_nat (length (re_keys e)) <= re_nheld e) (lm_es mc).
Definition dc_static (cx : lfcx) (t : Z) (m : lmod) (j si : nat) (h : hsrc) : Prop :=
  dr_at_op cx m /\ dr_pick cx m si h /\ (j < length (lm_es m))%nat /\
  re_fd (nth j (lm_es m) dr_e0) = hs_fd h /\ re_eof (nth j (lm_es m) dr_e0) = 0 /\ RINV cx t m.

(* ---- transports shared by the stages ---- *)
(* the facts of dc_at that are not the model: the frame, the fake frame's flag word (FL), the input, the ROM, the
   jump table and the three cells *)
Definition dc_ctxp (cx : lfcx) (m : lmod) (FF A FL : Z) (ly : alayout) (S : astate) (W : world segs)
  (mem : word -> option byte) : Prop :=
  aframe_at cx true FF W mem /\ sv8 W mem (FF + 120) FL /\
  ainput_at B cx ly S W mem /\ rom_view segs W mem /\ jt_rom W mem /\
  sv8 W mem (lf_F cx + DR_N) (c_n cx - dr_k' cx m) /\ sv8 W mem (lf_F cx + DR_AT) A /\
  sv8 W mem (lf_F cx + 40) (rg_lock fr_RG).

(* ---------------- dt_: the kit the five transports share ---------------- *)
(* membership in a literal list (W_rep.v w_infp, which its Section keeps) *)
Ltac dt_infp := repeat (first [left; reflexivity | right]).
(* every arithmetic side condition of this block: the literals, errno's place, and lia *)
Ltac dt_num :=
  let V := fresh "V" in pose proof dt_rgv as V; destruct V as (?&?&?&?&?&?&?&?&?&?&?&?&?&?&?);
  let C := fresh "C" in pose proof dt_cst as C; destruct C as (?&?&?&?);
  pose proof HERR_HI; lia.

(* (c) each global cell the model reads is one of the entry's G_fr *)
Lemma dt_G_s : forall a, rg_s fr_RG <= a < rg_s fr_RG + 4 * ASRC -> inG G_fr a.
Proof. exact HGs. Qed.
Lemma dt_G_lock : forall a, rg_lock fr_RG <= a < rg_lock fr_RG + 12 -> inG G_fr a.
Proof. exact HGlock. Qed.
Lemma dt_G_src : forall a, rg_src fr_RG <= a < rg_src fr_RG + 8 -> inG G_fr a.
Proof. intros a Ha. apply HG_GK, Exists_exists. exists (rg_src fr_RG, 8).
  split; [unfold DR_GK; dt_infp | unfold in_zr; cbn [fst snd]; lia]. Qed.
Lemma dt_G_nsrc : forall a, rg_nsrc fr_RG <= a < rg_nsrc fr_RG + 4 -> inG G_fr a.
Proof. intros a Ha. apply HG_GK, Exists_exists. exists (rg_nsrc fr_RG, 4).
  split; [unfold DR_GK; dt_infp | unfold in_zr; cbn [fst snd]; lia]. Qed.
Lemma dt_G_capsrc : forall a, rg_capsrc fr_RG <= a < rg_capsrc fr_RG + 4 -> inG G_fr a.
Proof. intros a Ha. apply HG_GK, Exists_exists. exists (rg_capsrc fr_RG, 4).
  split; [unfold DR_GK; dt_infp | unfold in_zr; cbn [fst snd]; lia]. Qed.
Lemma dt_G_smax : forall a, rg_send_max fr_RG <= a < rg_send_max fr_RG + 8 -> inG G_fr a.
Proof. intros a Ha. apply HG_GK, Exists_exists. exists (rg_send_max fr_RG, 8).
  split; [unfold DR_GK; dt_infp | unfold in_zr; cbn [fst snd]; lia]. Qed.
Lemma dt_G_client : forall a, rg_client fr_RG <= a < rg_client fr_RG + 4 -> inG G_fr a.
Proof. intros a Ha. apply HG_GK, Exists_exists. exists (rg_client fr_RG, 4).
  split; [unfold DR_GK; dt_infp | unfold in_zr; cbn [fst snd]; lia]. Qed.
Lemma dt_G_sdead : forall a, rg_send_dead fr_RG <= a < rg_send_dead fr_RG + 1 -> inG G_fr a.
Proof. intros a Ha. apply HG_GK, Exists_exists. exists (rg_send_dead fr_RG, 1).
  split; [unfold DR_GK; dt_infp | unfold in_zr; cbn [fst snd]; lia]. Qed.
Lemma dt_G_gone : forall a, rg_gone fr_RG <= a < rg_gone fr_RG + 1 -> inG G_fr a.
Proof. intros a Ha. apply HG_GK, Exists_exists. exists (rg_gone fr_RG, 1).
  split; [unfold DR_GK; dt_infp | unfold in_zr; cbn [fst snd]; lia]. Qed.
Lemma dt_G_wake : forall a, rg_wake fr_RG <= a < rg_wake fr_RG + 8 -> inG G_fr a.
Proof. intros a Ha. apply HG_GK, Exists_exists. exists (rg_wake fr_RG, 8).
  split; [unfold DR_GK; dt_infp | unfold in_zr; cbn [fst snd]; lia]. Qed.
Lemma dt_G_nfd : forall a, AG_NFD <= a < AG_NFD + 4 -> inG G_fr a.
Proof. intros a Ha. apply HG_GK, Exists_exists. exists (AG_NFD, 4).
  split; [unfold DR_GK; dt_infp | unfold in_zr; cbn [fst snd]; lia]. Qed.
Lemma dt_G_up : forall a, AG_THREAD_UP <= a < AG_THREAD_UP + 1 -> inG G_fr a.
Proof. intros a Ha. apply HG_GK, Exists_exists. exists (AG_THREAD_UP, 1).
  split; [unfold DR_GK; dt_infp | unfold in_zr; cbn [fst snd]; lia]. Qed.
Lemma dt_G_listen : forall a, AG_LISTEN <= a < AG_LISTEN + 4 -> inG G_fr a.
Proof. intros a Ha. apply HG_GK, Exists_exists. exists (AG_LISTEN, 4).
  split; [unfold DR_GK; dt_infp | unfold in_zr; cbn [fst snd]; lia]. Qed.
Lemma dt_G_cbr : forall a, rg_client_broken fr_RG <= a < rg_client_broken fr_RG + 1 -> inG G_fr a.
Proof. intros a Ha. apply HG_DR, Exists_exists. exists (rg_client_broken fr_RG, 1).
  split; [unfold G_DR, G_SL; dt_infp | unfold in_zr; cbn [fst snd]; lia]. Qed.
Lemma dt_G_sei : forall a, rg_send_eintr fr_RG <= a < rg_send_eintr fr_RG + 1 -> inG G_fr a.
Proof. intros a Ha. apply HG_DR, Exists_exists. exists (rg_send_eintr fr_RG, 1).
  split; [unfold G_DR, G_SL; dt_infp | unfold in_zr; cbn [fst snd]; lia]. Qed.
Lemma dt_G_nout : forall a, rg_nout fr_RG <= a < rg_nout fr_RG + 8 -> inG G_fr a.
Proof. intros a Ha. apply HG_DR, Exists_exists. exists (rg_nout fr_RG, 8).
  split; [unfold G_DR, G_SL; dt_infp | unfold in_zr; cbn [fst snd]; lia]. Qed.
Lemma dt_G_capout : forall a, rg_capout fr_RG <= a < rg_capout fr_RG + 8 -> inG G_fr a.
Proof. intros a Ha. apply HG_DR, Exists_exists. exists (rg_capout fr_RG, 8).
  split; [unfold G_DR, G_SL; dt_infp | unfold in_zr; cbn [fst snd]; lia]. Qed.
Lemma dt_G_out : forall a, rg_out fr_RG <= a < rg_out fr_RG + 8 -> inG G_fr a.
Proof. intros a Ha. apply HG_DR, Exists_exists. exists (rg_out fr_RG, 8).
  split; [unfold G_DR, G_SL; dt_infp | unfold in_zr; cbn [fst snd]; lia]. Qed.
Lemma dt_G_err : forall a, as_errno B <= a < as_errno B + 4 -> inG G_fr a.
Proof. intros a Ha. apply HG_DR, Exists_exists. exists (as_errno B, 4).
  split; [unfold G_DR, G_SL; dt_infp | unfold in_zr; cbn [fst snd]; lia]. Qed.
Ltac dt_ing := solve
  [ apply dt_G_s; dt_num | apply dt_G_src; lia | apply dt_G_nsrc; lia | apply dt_G_capsrc; lia
  | apply dt_G_smax; lia | apply dt_G_client; lia | apply dt_G_sdead; lia | apply dt_G_gone; lia
  | apply dt_G_wake; lia | apply dt_G_nfd; lia | apply dt_G_up; lia | apply dt_G_listen; lia
  | apply dt_G_cbr; lia | apply dt_G_sei; lia | apply dt_G_nout; lia | apply dt_G_capout; lia
  | apply dt_G_out; lia | apply dt_G_err; lia | apply dt_G_lock; lia ].

(* (d) a byte whose view is kept, and which is a G_fr byte or lies off the image, is kept *)
Lemma dt_G_rng : forall a, inG G_fr a -> 0x10000 <= a < 0x5fb000.
Proof. intros a Hg. exact (pa_img_range a (proj1 (HG a Hg))). Qed.
Lemma dt_bkG : forall (W W' : world segs) mem mem' a, inG G_fr a ->
  aview segs (w_H W') mem' a = aview segs (w_H W) mem a -> abyte_kept W mem W' mem' a.
Proof.
  intros W W' mem mem' a Hg Ha. pose proof (dt_G_rng a Hg).
  apply dj_bk; [lia | intros _; exact Hg | exact Ha].
Qed.
Lemma dt_bkN : forall (W W' : world segs) mem mem' a, 0 <= a < 2 ^ 64 -> ~ in_img segs a ->
  aview segs (w_H W') mem' a = aview segs (w_H W) mem a -> abyte_kept W mem W' mem' a.
Proof.
  intros W W' mem mem' a Hr Hi Ha. apply dj_bk; [exact Hr | intros H; exfalso; exact (Hi H) | exact Ha].
Qed.

(* (e) the two keepers the model's transport runs on *)
Definition dt_KG (W : world segs) (mem : word -> option byte) (W' : world segs)
  (mem' : word -> option byte) : Prop :=
  forall a, inG G_fr a -> ~ (rg_lock fr_RG + 4 <= a < rg_lock fr_RG + 8) ->
    ~ (as_errno B <= a < as_errno B + 4) -> abyte_kept W mem W' mem' a.
Definition dt_KB (ly : alayout) (S : astate) (W : world segs) (mem : word -> option byte)
  (W' : world segs) (mem' : word -> option byte) : Prop :=
  forall p n a, In (p, n) (ablocks B ly S) -> p <= a < p + n -> abyte_kept W mem W' mem' a.

(* (f) the blocks each component of the model names are live *)
Lemma dt_alist_blks : forall ly S (W : world segs) mem LA l lines,
  alist_at B ly S W mem LA l lines -> forall b, In b (alist_blks l) -> In b (ablocks B ly S).
Proof.
  intros ly S W mem LA l lines (_ & _ & _ & _ & _ & H6 & _ & _ & H9) b Hb.
  unfold alist_blks in Hb. apply in_app_or in Hb as [Hb | Hb].
  - destruct H6 as [(Hc & _) | (Hcp & Hin & _)].
    + rewrite (proj2 (Z.eqb_eq (hl_cap l) 0) Hc) in Hb. destruct Hb.
    + assert (Ec : (hl_cap l =? 0) = false) by (apply Z.eqb_neq; lia).
      rewrite Ec in Hb. destruct Hb as [<- | []]. exact Hin.
  - apply in_map_iff in Hb as (r & <- & Hr). rewrite Forall_forall in H9. exact (proj1 (H9 r Hr)).
Qed.
Lemma dt_asrc_blks : forall ly S (W : world segs) mem HA h,
  asrc_at B ly S W mem HA h -> forall b, In b (asrc_blks h) -> In b (ablocks B ly S).
Proof.
  intros ly S W mem HA h
    (_ & _ & _ & _ & _ & _ & _ & _ & _ & H10 & _ & _ & _ & _ & _ & _ & _ & H18 & _ & _ & _ & H22 & H23 & _) b Hb.
  destruct Hb as [<- | Hb]; [exact H18|].
  apply in_app_or in Hb as [Hb | Hb];
    [exact (dt_alist_blks ly S W mem (HA + 16) (hs_pending h) false H10 b Hb)|].
  apply in_app_or in Hb as [Hb | Hb];
    [exact (dt_alist_blks ly S W mem (HA + 64) (hs_expected h) true H22 b Hb)
    | exact (dt_alist_blks ly S W mem (HA + 80) (hs_held h) true H23 b Hb)].
Qed.
Lemma dt_aentry_blks : forall ly S (W : world segs) mem e,
  aentry_ok B ly S W mem e -> forall b, In b (aentry_blks e) -> In b (ablocks B ly S).
Proof.
  intros ly S W mem e (_ & _ & _ & _ & _ & _ & _ & _ & _ & H10 & _ & H12 & _ & _ & H15) b Hb.
  unfold aentry_blks in Hb. apply in_app_or in Hb as [Hb | Hb].
  - destruct H10 as [(Hc & _) | (Hcp & Hin & _)].
    + rewrite (proj2 (Z.eqb_eq (re_cap e) 0) Hc) in Hb. destruct Hb.
    + assert (Ec : (re_cap e =? 0) = false) by (apply Z.eqb_neq; lia).
      rewrite Ec in Hb. destruct Hb as [<- | []]. exact Hin.
  - apply in_app_or in Hb as [Hb | Hb].
    + destruct H12 as [(Hz & _) | (Hz & Hin & _)].
      * rewrite (proj2 (Z.eqb_eq (re_hp e) 0) Hz) in Hb. destruct Hb.
      * assert (Ez : (re_hp e =? 0) = false) by (apply Z.eqb_neq; exact Hz).
        rewrite Ez in Hb. destruct Hb as [<- | []]. exact Hin.
    + apply in_map_iff in Hb as (k & <- & Hk). rewrite Forall_forall in H15. exact (proj1 (H15 k Hk)).
Qed.
Lemma dt_arelay_blks : forall ly S (W : world segs) mem G es,
  arelay_at B fr_RG ly S W mem G es -> forall b, In b (arelay_blks G es) -> In b (ablocks B ly S).
Proof.
  intros ly S W mem G es (_ & _ & _ & _ & _ & _ & _ & H8 & _ & H10 & _) b Hb.
  destruct Hb as [<- | Hb]; [exact H8|].
  apply in_concat in Hb as (l & Hl & Hb). apply in_map_iff in Hl as (e & <- & He).
  rewrite Forall_forall in H10. exact (dt_aentry_blks ly S W mem e (H10 e He) b Hb).
Qed.
Lemma dt_aout_blks : forall ly S (W : world segs) mem c O mx no cap out,
  aout_at B fr_RG ly S W mem c O mx no cap out -> forall b, In b (aout_blks cap out) -> In b (ablocks B ly S).
Proof.
  intros ly S W mem c O mx no cap out
    (_&_&_&_&_&_&_&_&_&_&_&_&_&_&_&_&_&_&_&_&_&_&_&_&_& H26) b Hb.
  unfold aout_blks in Hb. destruct H26 as [(Hc & _) | (Hcp & _ & Hin & _)].
  - rewrite (proj2 (Z.eqb_eq cap 0) Hc) in Hb. destruct Hb.
  - assert (Ec : (cap =? 0) = false) by (apply Z.eqb_neq; lia).
    rewrite Ec in Hb. destruct Hb as [<- | []]. exact Hin.
Qed.

(* (g) the output stream, with errno re-read at the new state *)
Lemma dt_aoutg : forall a, (exists r, In r (aout_fp B fr_RG 0 0) /\ fst r <= a < snd r) ->
  inG G_fr a /\ ~ (rg_lock fr_RG + 4 <= a < rg_lock fr_RG + 8).
Proof.
  intros a (r & Hin & Ha). unfold aout_fp in Hin. cbn [In] in Hin.
  destruct Hin as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]]; cbn [fst snd] in Ha;
    (split; [dt_ing | dt_num]).
Qed.
Lemma dt_aout_ne : forall ly S (W : world segs) mem (W' : world segs) mem' c O mx no cap out ev,
  aout_at B fr_RG ly S W mem c O mx no cap out ->
  dt_KG W mem W' mem' -> dt_KB ly S W mem W' mem' ->
  val_mem segs (arm W' mem') (as_errno B) 4 ev -> awr W' mem' (as_errno B) 4 -> 0 <= ev < 2 ^ 32 ->
  aout_at B fr_RG ly S W' mem' (dc_ctl c ev) O mx no cap out.
Proof.
  intros ly S W mem W' mem' c O mx no cap out ev HO KG KB HEV HEW HEB.
  assert (AK : forall lo hi, In (lo, hi) (aout_fp B fr_RG cap out) ->
                 (forall x, lo <= x < hi -> ~ (as_errno B <= x < as_errno B + 4)) ->
                 forall x, lo <= x < hi -> abyte_kept W mem W' mem' x).
  { intros lo hi Hin Hne x Hx.
    destruct (dj_aout_fp ly S W mem c O mx no cap out HO (lo, hi) Hin x Hx) as [Hg | ([p n] & Hb & Hab)].
    - destruct (dt_aoutg x Hg) as (P1 & P2). exact (KG x P1 P2 (Hne x Hx)).
    - cbn [fst snd] in Hab.
      exact (KB p n x (dt_aout_blks ly S W mem c O mx no cap out HO (p, n) Hb) Hab). }
  pose proof HO as (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11 & H12 & H13 & H14 & H15 & H16 &
                    _ & _ & _ & H20 & H21 & H22 & H23 & H24 & H25 & H26).
  unfold dc_ctl. cbn [ct_cl ct_br ct_dd ct_ei ct_ev].
  split; [apply (akept_vm W mem); [intros x Hx; apply (AK (rg_send_max fr_RG) (rg_send_max fr_RG + 8));
    [unfold aout_fp; dt_infp | intros y Hy; dt_num | dt_num] | exact H1]|].
  split; [apply (akept_awr W mem); [intros x Hx; apply (AK (rg_send_max fr_RG) (rg_send_max fr_RG + 8));
    [unfold aout_fp; dt_infp | intros y Hy; dt_num | lia] | exact H2]|].
  split; [apply (akept_vm W mem); [intros x Hx; apply (AK (rg_nout fr_RG) (rg_nout fr_RG + 8));
    [unfold aout_fp; dt_infp | intros y Hy; dt_num | dt_num] | exact H3]|].
  split; [apply (akept_awr W mem); [intros x Hx; apply (AK (rg_nout fr_RG) (rg_nout fr_RG + 8));
    [unfold aout_fp; dt_infp | intros y Hy; dt_num | lia] | exact H4]|].
  split; [apply (akept_vm W mem); [intros x Hx; apply (AK (rg_capout fr_RG) (rg_capout fr_RG + 8));
    [unfold aout_fp; dt_infp | intros y Hy; dt_num | dt_num] | exact H5]|].
  split; [apply (akept_awr W mem); [intros x Hx; apply (AK (rg_capout fr_RG) (rg_capout fr_RG + 8));
    [unfold aout_fp; dt_infp | intros y Hy; dt_num | lia] | exact H6]|].
  split; [apply (akept_vm W mem); [intros x Hx; apply (AK (rg_out fr_RG) (rg_out fr_RG + 8));
    [unfold aout_fp; dt_infp | intros y Hy; dt_num | dt_num] | exact H7]|].
  split; [apply (akept_awr W mem); [intros x Hx; apply (AK (rg_out fr_RG) (rg_out fr_RG + 8));
    [unfold aout_fp; dt_infp | intros y Hy; dt_num | lia] | exact H8]|].
  split; [apply (akept_vm W mem); [intros x Hx; apply (AK (rg_client fr_RG) (rg_client fr_RG + 4));
    [unfold aout_fp; dt_infp | intros y Hy; dt_num | dt_num] | exact H9]|].
  split; [apply (akept_awr W mem); [intros x Hx; apply (AK (rg_client fr_RG) (rg_client fr_RG + 4));
    [unfold aout_fp; dt_infp | intros y Hy; dt_num | lia] | exact H10]|].
  split; [apply (akept_vm W mem); [intros x Hx;
    apply (AK (rg_client_broken fr_RG) (rg_client_broken fr_RG + 1));
    [unfold aout_fp; dt_infp | intros y Hy; dt_num | dt_num] | exact H11]|].
  split; [apply (akept_awr W mem); [intros x Hx;
    apply (AK (rg_client_broken fr_RG) (rg_client_broken fr_RG + 1));
    [unfold aout_fp; dt_infp | intros y Hy; dt_num | lia] | exact H12]|].
  split; [apply (akept_vm W mem); [intros x Hx; apply (AK (rg_send_dead fr_RG) (rg_send_dead fr_RG + 1));
    [unfold aout_fp; dt_infp | intros y Hy; dt_num | dt_num] | exact H13]|].
  split; [apply (akept_awr W mem); [intros x Hx; apply (AK (rg_send_dead fr_RG) (rg_send_dead fr_RG + 1));
    [unfold aout_fp; dt_infp | intros y Hy; dt_num | lia] | exact H14]|].
  split; [apply (akept_vm W mem); [intros x Hx; apply (AK (rg_send_eintr fr_RG) (rg_send_eintr fr_RG + 1));
    [unfold aout_fp; dt_infp | intros y Hy; dt_num | dt_num] | exact H15]|].
  split; [apply (akept_awr W mem); [intros x Hx; apply (AK (rg_send_eintr fr_RG) (rg_send_eintr fr_RG + 1));
    [unfold aout_fp; dt_infp | intros y Hy; dt_num | lia] | exact H16]|].
  split; [exact HEV|]. split; [exact HEW|]. split; [exact HEB|].
  split; [exact H20|]. split; [exact H21|]. split; [exact H22|]. split; [exact H23|].
  split; [exact H24|]. split; [exact H25|].
  destruct H26 as [H26 | (Hc & Hno & Hin & junk & Hj & Hg)]; [left; exact H26|right].
  assert (Ec : (cap =? 0) = false) by (apply Z.eqb_neq; lia).
  split; [exact Hc|]. split; [exact Hno|]. split; [exact Hin|].
  exists junk. split; [exact Hj|].
  apply (akept_garr8 W mem); [|exact Hg].
  intros x Hx. unfold bzs in Hx. rewrite length_map, length_app, Nat2Z.inj_add in Hx.
  exact (KB out cap x (dt_aout_blks ly S W mem c O mx no cap out HO (out, cap)
           ltac:(unfold aout_blks; rewrite Ec; left; reflexivity)) ltac:(lia)).
Qed.

(* (h) the model, under the two keepers, with the lock and errno given at the new state *)
Lemma dt_ne_core : forall ly S (W : world segs) mem (W' : world segs) mem' m (held held' : bool) ev,
  Forall (fun e => Z.of_nat (length (re_keys e)) <= re_nheld e) (lm_es m) ->
  amodel_ne ly S W mem m held ->
  dt_KG W mem W' mem' -> dt_KB ly S W mem W' mem' ->
  alock_at fr_RG W' mem' held' ->
  val_mem segs (arm W' mem') (as_errno B) 4 ev -> awr W' mem' (as_errno B) 4 -> 0 <= ev < 2 ^ 32 ->
  amodel_ne ly S W' mem' m held'.
Proof.
  intros ly S W mem W' mem' m held held' ev HK
    (M1 & M2 & M3 & M4 & M5 & M6 & M7 & M8 & M9 & M10 & M11 & M12 & M13) KG KB HLK HEV HEW HEB.
  split; [exact M1|].
  split.
  { intros i Hi. pose proof (M2 i Hi) as Mi. assert (Hi4 : Z.of_nat i < 4) by lia.
    unfold aslot in Mi |- *. destruct (nth i (lm_hs m) None) as [h|].
    - apply (asrc_at_kept B ly S W mem ly S W' mem' (rg_s fr_RG + ASRC * Z.of_nat i) h Mi).
      + intros r Hr a Ha.
        destruct (dj_asrc_fp ly S W mem (rg_s fr_RG + ASRC * Z.of_nat i) h Mi r Hr a Ha)
          as [Hg | ([p n] & Hb & Hab)].
        * apply KG; [apply dt_G_s; dt_num | dt_num | dt_num].
        * cbn [fst snd] in Hab.
          exact (KB p n a (dt_asrc_blks ly S W mem _ h Mi (p, n) Hb) Hab).
      + intros b Hb. exact (dt_asrc_blks ly S W mem _ h Mi b Hb).
    - destruct Mi as (G1 & G2).
      assert (HL : length (repeat 0 (Z.to_nat ASRC)) = 96%nat) by (vm_compute; reflexivity).
      split.
      + apply (akept_garr8 W mem); [|exact G1]. intros x Hx. rewrite HL in Hx.
        apply KG; [apply dt_G_s; dt_num | dt_num | dt_num].
      + apply (akept_awr W mem); [|exact G2]. intros x Hx.
        apply KG; [apply dt_G_s; dt_num | dt_num | dt_num]. }
  split.
  { apply (arelay_at_kept B fr_RG ly S W mem ly S W' mem' (lm_G m) (lm_es m) M3).
    - intros r Hr a Ha.
      destruct (dj_arelay_fp ly S W mem (lm_G m) (lm_es m) M3 HK r Hr a Ha) as [Hg | ([p n] & Hb & Hab)].
      + destruct Hg as [Hg | [Hg | Hg]]; apply KG; solve [dt_ing | dt_num].
      + cbn [fst snd] in Hab.
        exact (KB p n a (dt_arelay_blks ly S W mem (lm_G m) (lm_es m) M3 (p, n) Hb) Hab).
    - intros b Hb. exact (dt_arelay_blks ly S W mem (lm_G m) (lm_es m) M3 b Hb). }
  split.
  { destruct M4 as (ev0 & HO). exists ev.
    exact (dt_aout_ne ly S W mem W' mem' (dc_ctl (lm_c m) ev0) (lm_O m) (lm_mx m)
             (Z.of_nat (length (lm_O m))) (lm_cap m) (lm_out m) ev HO KG KB HEV HEW HEB). }
  split.
  { apply (agone_at_kept fr_RG W mem W' mem' (lm_gn m) M5).
    apply dt_akept1. intros x Hx. apply KG; [apply dt_G_gone; lia | dt_num | dt_num]. }
  split; [exact HLK|].
  split.
  { apply (awake_at_kept fr_RG W mem W' mem' M7).
    apply dt_akept1. intros x Hx. apply KG; [apply dt_G_wake; lia | dt_num | dt_num]. }
  split.
  { apply (akept_vm W mem); [|exact M8]. intros x Hx.
    apply KG; [apply dt_G_nfd; dt_num | dt_num | dt_num]. }
  split.
  { apply (akept_awr W mem); [|exact M9]. intros x Hx.
    apply KG; [apply dt_G_nfd; lia | dt_num | dt_num]. }
  split; [exact M10|].
  split.
  { apply (akept_vm W mem); [|exact M11]. intros x Hx.
    apply KG; [apply dt_G_up; dt_num | dt_num | dt_num]. }
  split.
  { destruct M12 as (lst & Hlst). exists lst. apply (akept_vm W mem); [|exact Hlst]. intros x Hx.
    apply KG; [apply dt_G_listen; dt_num | dt_num | dt_num]. }
  apply (akept_awr W mem); [|exact M13]. intros x Hx.
  apply KG; [apply dt_G_listen; lia | dt_num | dt_num].
Qed.

(* a pthread_mutex_lock / _unlock step (aj_gx_entry_at's post): every byte but the lock word and the entry's
   scratch [sp - ESTACK, sp) keeps its view *)
Lemma dj_ne_lockstep : forall ly S Hp (W : world segs) mem md mem' m (held held' : bool) sp,
  ARx ly S Hp W mem md ->
  Forall (fun e => Z.of_nat (length (re_keys e)) <= re_nheld e) (lm_es m) ->
  amodel_ne ly S W mem m held ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (rg_lock fr_RG + 4 <= a < rg_lock fr_RG + 8) -> ~ (sp - ESTACK <= a < sp) ->
     aview segs (w_H W) mem' a = aview segs (w_H W) mem a) ->
  alloc_ceiling + 8 <= sp - ESTACK ->
  val_mem segs (mrestrict (w_H W) mem') (rg_lock fr_RG + 4) 4 (if held' then 16 else 0) ->
  amodel_ne ly S W mem' m held'.
Proof.
  intros ly S Hp W mem md mem' m held held' sp HAR HK HM KV Hsp HLW.
  pose proof asan_consts as ((HCL & HCU) & _).
  (* every G_fr byte but the lock word keeps its view, so it is kept *)
  assert (KGall : forall a, inG G_fr a -> ~ (rg_lock fr_RG + 4 <= a < rg_lock fr_RG + 8) ->
                    abyte_kept W mem W mem' a).
  { intros a Hg Hl. pose proof (dt_G_rng a Hg) as Hr.
    apply dt_bkG; [exact Hg|]. apply KV; [lia | exact Hl | lia]. }
  assert (KG : dt_KG W mem W mem') by (intros a Hg Hl _; exact (KGall a Hg Hl)).
  (* a live block's bytes are no image bytes, so they are no lock word either *)
  assert (KB : dt_KB ly S W mem W mem').
  { intros p n a Hin Ha.
    destruct (dr_blk B ARx LAWS BLKR ly S Hp W mem md p n HAR Hin) as (P1 & P2 & P3).
    assert (Hni : ~ in_img segs a)
      by exact (blk_img_x segs B ARx LAWS ly S Hp W mem md p n a HAR Hin (dt_reqr p n a Ha)).
    apply dt_bkN; [lia | exact Hni|].
    apply KV; [lia | intros Hc; apply Hni; exact (proj1 (HG a (dt_G_lock a ltac:(lia)))) | lia]. }
  pose proof HM as (_ & _ & _ & (ev0 & HO) & _ & M6 & _).
  (* the lock: its two other words are kept, its lock word is the premise, its cells stay writable *)
  assert (HLK : alock_at fr_RG W mem' held').
  { destruct M6 as (L1 & L2 & L3 & L4).
    split; [apply (akept_vm W mem); [|exact L1]; intros x Hx;
      apply KGall; [apply dt_G_lock; dt_num | dt_num]|].
    split; [exact HLW|].
    split; [apply (akept_vm W mem); [|exact L3]; intros x Hx;
      apply KGall; [apply dt_G_lock; dt_num | dt_num]|].
    intros i Hi. exact (GWR _ _ (rg_lock fr_RG + i) (dt_G_lock (rg_lock fr_RG + i) ltac:(lia))). }
  (* errno keeps its view (it is above every global the lock step touches) *)
  pose proof HO as (_&_&_&_&_&_&_&_&_&_&_&_&_&_&_&_& E1 & E2 & E3 & _).
  assert (KE : forall x, as_errno B <= x < as_errno B + 4 -> abyte_kept W mem W mem' x)
    by (intros x Hx; apply KGall; [apply dt_G_err; lia | dt_num]).
  exact (dt_ne_core ly S W mem W mem' m held held' (ct_ev (dc_ctl (lm_c m) ev0)) HK HM KG KB HLK
           (akept_vm W mem W mem' (as_errno B) 4 (ct_ev (dc_ctl (lm_c m) ev0))
              ltac:(intros x Hx; apply KE; dt_num) E1)
           (akept_awr W mem W mem' (as_errno B) 4 ltac:(intros x Hx; apply KE; lia) E2) E3).
Qed.
Lemma dt_ainput_kept : forall cx ly S (W : world segs) mem (W' : world segs) mem',
  ainput_at B cx ly S W mem -> Z.of_nat (length (c_pl cx)) = c_n cx ->
  dt_KB ly S W mem W' mem' -> ainput_at B cx ly S W' mem'.
Proof.
  intros cx ly S W mem W' mem' (H1 & H2) Hlen KB.
  split; [exact H1|]. apply (akept_garr8 W mem); [|exact H2].
  intros x Hx. rewrite length_map, Hlen in Hx.
  destruct H1 as [(Hn0 & _) | (Hn & Hin)]; [lia|]. exact (KB (c_p cx) (c_n cx) x Hin Hx).
Qed.
(* sp and the frame base of this call, from the entry's contract *)
Lemma dt_spF : forall cx Hpe, lf_base_x B MT XM_LIB RLO RHI fr_live_pre LIBROOM NP G_fr ARx cx Hpe ->
  alloc_ceiling + 32768 <= spZ (c_regs cx) /\ spZ (c_regs cx) <= 2 ^ 47 /\
  spZ (c_regs cx) - 352 < lf_F cx /\ lf_F cx + 320 <= spZ (c_regs cx) /\
  Z.of_nat (length (c_pl cx)) = c_n cx.
Proof.
  intros cx Hpe (_ & HP & _ & _ & _ & _ & Hlen & _).
  destruct HP as (_ & _ & _ & _ & _ & (_ & _ & H3 & H4 & H5 & H6 & _) & _).
  unfold LLVMF_STK in H4. unfold lf_F.
  pose proof (Z.mod_pos_bound (spZ (c_regs cx) - 320) 32 ltac:(lia)).
  repeat split; lia.
Qed.
Lemma dt_ctx_core : forall cx Hpe m FF A FL ly S (W : world segs) mem (W' : world segs) mem',
  lf_base_x B MT XM_LIB RLO RHI fr_live_pre LIBROOM NP G_fr ARx cx Hpe ->
  dc_ctxp cx m FF A FL ly S W mem ->
  (forall a, lf_F cx <= a < 2 ^ 64 -> abyte_kept W mem W' mem' a) ->
  (forall a, FF <= a < FF + 128 -> abyte_kept W mem W' mem' a) ->
  (forall a, SB + FF / 8 <= a < SB + FF / 8 + 16 -> abyte_kept W mem W' mem' a) ->
  dt_KB ly S W mem W' mem' -> rom_view segs W' mem' ->
  dc_ctxp cx m FF A FL ly S W' mem'.
Proof.
  intros cx Hpe m FF A FL ly S W mem W' mem' HLB (HFR & HFL & HIN & HRV & HJT & HN & HAT & HL) KS KF KFS KB HRV'.
  destruct (dt_spF cx Hpe HLB) as (Q1 & Q2 & Q3 & Q4 & Q5).
  assert (KS' : forall a, lf_F cx <= a < spZ (c_regs cx) -> abyte_kept W mem W' mem' a)
    by (intros a Ha; apply KS; lia).
  split; [exact (dt_aframe_kept cx true FF W W' mem mem' HFR KS' KF KFS Q4)|].
  split; [apply (dr_sv8_kept W W' mem mem'); [intros x Hx; apply KF; lia | exact HFL]|].
  split; [exact (dt_ainput_kept cx ly S W mem W' mem' HIN Q5 KB)|].
  split; [exact HRV'|].
  split.
  { intros i Hi k Hk.
    assert (Hrm : in_rom segs (fr_jtab + 4 * i + Z.of_nat k)) by (apply dj_jt_rom; lia).
    rewrite (mbyte_of_aview segs (w_H W) (w_H W') mem mem' (fr_jtab + 4 * i + Z.of_nat k)
               (dt_romkeep W W' mem mem' HRV HRV' (fr_jtab + 4 * i + Z.of_nat k) Hrm)).
    exact (HJT i Hi k Hk). }
  split; [apply (dr_sv8_kept W W' mem mem'); [intros x Hx; apply KS; unfold DR_N in *; lia | exact HN]|].
  split; [apply (dr_sv8_kept W W' mem mem'); [intros x Hx; apply KS; unfold DR_AT in *; lia | exact HAT]|].
  apply (dr_sv8_kept W W' mem mem'); [intros x Hx; apply KS; lia | exact HL].
Qed.

Lemma dj_ctx_lockstep : forall cx Hpe m FF A FL ly S Hp (W : world segs) mem md mem',
  lf_base_x B MT XM_LIB RLO RHI fr_live_pre LIBROOM NP G_fr ARx cx Hpe ->
  ARx ly S Hp W mem md -> (exists pos, In (1, pos) (frames S) /\ FF = frame_addr ly 1 pos) ->
  dc_ctxp cx m FF A FL ly S W mem ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (rg_lock fr_RG + 4 <= a < rg_lock fr_RG + 8) ->
     ~ (lf_F cx - ESTACK <= a < lf_F cx) -> aview segs (w_H W) mem' a = aview segs (w_H W) mem a) ->
  (forall a, apresent (w_H W) mem a -> apresent (w_H W) mem' a) ->
  dc_ctxp cx m FF A FL ly S W mem'.
Proof.
  intros cx Hpe m FF A FL ly S Hp W mem md mem' HLB HAR (pos & Hfin & HFF) HCX KV HPR.
  pose proof asan_consts as ((HCL & HCU) & HSE & _ & HME & HLE).
  assert (HES : ESTACK = 4096) by reflexivity.
  destruct (dt_spF cx Hpe HLB) as (Q1 & Q2 & Q3 & Q4 & Q5).
  destruct (frames_bounds_x segs B ARx LAWS ly S Hp W mem md 1 pos HAR Hfin) as (HF1 & HF2 & _).
  change (fs_frame_bytes 1) with 128 in HF2. rewrite <- HFF in HF1, HF2.
  pose proof (dt_shadow FF) as Hsh.
  pose proof (shadow_addr_bounds FF ltac:(lia)) as Hsb.
  pose proof (shadow_addr_bounds (FF + 128) ltac:(lia)) as Hsb2.
  pose proof (shadow_range_end FF 128 ltac:(lia)) as Hsr.
  assert (Hlockimg : forall a, rg_lock fr_RG + 4 <= a < rg_lock fr_RG + 8 -> in_img segs a)
    by (intros a Ha; exact (proj1 (HG a (dt_G_lock a ltac:(lia))))).
  (* the stack above the frame base: off the image, above the entry's scratch *)
  assert (KS : forall a, lf_F cx <= a < 2 ^ 64 -> abyte_kept W mem W mem' a).
  { intros a Ha.
    assert (Hni : ~ in_img segs a) by (intros Hi; pose proof (pa_segs_low a Hi) as Hb; lia).
    apply dt_bkN; [lia | exact Hni|].
    apply KV; [lia | intros Hc; exact (Hni (Hlockimg a Hc)) | lia]. }
  (* the fake frame and its shadow: both off the image, both below the entry's scratch *)
  assert (KF : forall a, FF <= a < FF + 128 -> abyte_kept W mem W mem' a).
  { intros a Ha.
    assert (Hni : ~ in_img segs a)
      by (apply (frm_img_x segs B ARx LAWS ly S Hp W mem md 1 pos a HAR Hfin);
          rewrite <- HFF; change (fs_frame_bytes 1) with 128; lia).
    apply dt_bkN; [lia | exact Hni|].
    apply KV; [lia | intros Hc; exact (Hni (Hlockimg a Hc)) | lia]. }
  assert (KFS : forall a, SB + FF / 8 <= a < SB + FF / 8 + 16 -> abyte_kept W mem W mem' a).
  { intros a Ha.
    assert (Hni : ~ in_img segs a) by (intros Hi; pose proof (pa_segs_low a Hi) as Hb; lia).
    apply dt_bkN; [lia | exact Hni|].
    apply KV; [lia | intros Hc; exact (Hni (Hlockimg a Hc)) | lia]. }
  (* the live blocks: off the image, below the entry's scratch *)
  assert (KB : dt_KB ly S W mem W mem').
  { intros p n a Hin Ha.
    destruct (dr_blk B ARx LAWS BLKR ly S Hp W mem md p n HAR Hin) as (P1 & P2 & P3).
    assert (Hni : ~ in_img segs a)
      by exact (blk_img_x segs B ARx LAWS ly S Hp W mem md p n a HAR Hin (dt_reqr p n a Ha)).
    apply dt_bkN; [lia | exact Hni|].
    apply KV; [lia | intros Hc; exact (Hni (Hlockimg a Hc)) | lia]. }
  (* the read-only image: no G_fr byte is read-only, and it is far below the entry's scratch *)
  assert (HRV' : rom_view segs W mem').
  { pose proof HCX as (_ & _ & _ & HRV & _). intros a Ha. pose proof (dt_rom_rng a Ha) as Hr.
    rewrite (KV a ltac:(lia) ltac:(intros Hc; exact (proj1 (DR_ROM_OUT a Ha) (dt_G_lock a ltac:(lia))))
               ltac:(lia)).
    exact (HRV a Ha). }
  exact (dt_ctx_core cx Hpe m FF A FL ly S W mem W mem' HLB HCX KS KF KFS KB HRV').
Qed.

(* a leaf callee (aleaf_post's journal: no footprint, the allocator state kept) called at sp = F *)
Lemma dj_ne_plain : forall ly S Hp (W W' : world segs) mem mem' md md' m held STK sp,
  ajournal_x segs B PST ARx STK sp [] ly S Hp W mem md [] ly S Hp W' mem' md' 0 -> alloc_ceiling + 8 <= sp - STK ->
  Forall (fun e => Z.of_nat (length (re_keys e)) <= re_nheld e) (lm_es m) ->
  amodel_ne ly S W mem m held -> amodel_ne ly S W' mem' m held.
Proof.
  intros ly S Hp W W' mem mem' md md' m held STK sp HJ Hsp HK HM.
  pose proof asan_consts as ((HCL & HCU) & _).
  pose proof HJ as (HAR' & _ & _ & _ & _ & _ & _ & _ & _ & F2 & F3 & _).
  (* every G_fr byte but errno is an image byte the journal keeps *)
  assert (KGall : forall a, ~ (as_errno B <= a < as_errno B + 4) -> inG G_fr a ->
                    abyte_kept W mem W' mem' a).
  { intros a He Hg. destruct (HG a Hg) as (Hi & Ho & _).
    apply dt_bkG; [exact Hg|].
    apply F3; [exact Hi | exact Ho | exact He | exact (HPST a Hi) |].
    apply fp_spares_closed. intros (r & Hr & _). destruct Hr. }
  assert (KG : dt_KG W mem W' mem') by (intros a Hg _ He; exact (KGall a He Hg)).
  (* every live block's bytes: nothing is in the empty footprint *)
  assert (KB : dt_KB ly S W mem W' mem').
  { intros p n a Hin Ha.
    destruct (dr_blk B ARx LAWS BLKR ly S Hp W' mem' md' p n HAR' Hin) as (P1 & P2 & P3).
    assert (Hni : ~ in_img segs a)
      by exact (blk_img_x segs B ARx LAWS ly S Hp W' mem' md' p n a HAR' Hin (dt_reqr p n a Ha)).
    apply dt_bkN; [lia | exact Hni|].
    replace a with (p + (a - p)) by lia.
    apply (F2 p n (a - p) Hin Hin (dt_reqi p n a Ha)). intros Hc. exact (inFP_nil _ Hc). }
  pose proof HM as (_ & _ & _ & _ & _ & M6 & _).
  assert (HLK : alock_at fr_RG W' mem' held).
  { apply (alock_at_kept fr_RG W mem W' mem' held M6). apply dt_akept1. intros x Hx.
    apply KGall; [dt_num | apply dt_G_lock; lia]. }
  destruct (ERR ly S Hp W' mem' md' HAR') as ((ev & HEV & HEB) & HEW).
  exact (dt_ne_core ly S W mem W' mem' m held held ev HK HM KG KB HLK HEV HEW HEB).
Qed.
Lemma dj_ctx_plain : forall cx Hpe m FF A FL ly S Hp (W W' : world segs) mem mem' md md' STK,
  lf_base_x B MT XM_LIB RLO RHI fr_live_pre LIBROOM NP G_fr ARx cx Hpe ->
  ajournal_x segs B PST ARx STK (lf_F cx) [] ly S Hp W mem md [] ly S Hp W' mem' md' 0 -> 0 <= STK <= 16384 ->
  (exists pos, In (1, pos) (frames S) /\ FF = frame_addr ly 1 pos) ->
  dc_ctxp cx m FF A FL ly S W mem -> dc_ctxp cx m FF A FL ly S W' mem'.
Proof.
  intros cx Hpe m FF A FL ly S Hp W W' mem mem' md md' STK HLB HJ HSTK (pos & Hfin & HFF) HCX.
  pose proof asan_consts as ((HCL & HCU) & HSE & _ & HME & HLE).
  destruct (dt_spF cx Hpe HLB) as (Q1 & Q2 & Q3 & Q4 & Q5).
  pose proof HJ as (HAR' & _ & _ & _ & _ & _ & _ & _ & F1 & F2 & _ & F4 & _).
  destruct (frames_bounds_x segs B ARx LAWS ly S Hp W' mem' md' 1 pos HAR' Hfin) as (HF1 & HF2 & _).
  change (fs_frame_bytes 1) with 128 in HF2. rewrite <- HFF in HF1, HF2.
  pose proof (dt_shadow FF) as Hsh.
  pose proof (shadow_addr_bounds FF ltac:(lia)) as Hsb.
  pose proof (shadow_addr_bounds (FF + 128) ltac:(lia)) as Hsb2.
  pose proof (shadow_range_end FF 128 ltac:(lia)) as Hsr.
  (* the stack above the frame base *)
  assert (KS : forall a, lf_F cx <= a < 2 ^ 64 -> abyte_kept W mem W' mem' a).
  { intros a Ha.
    assert (Hni : ~ in_img segs a) by (intros Hi; pose proof (pa_segs_low a Hi) as Hb; lia).
    apply dt_bkN; [lia | exact Hni|]. apply F1; lia. }
  (* the fake frame of class 1 and its shadow, both outside the empty footprint *)
  assert (KF : forall a, FF <= a < FF + 128 -> abyte_kept W mem W' mem' a).
  { intros a Ha.
    assert (Hni : ~ in_img segs a)
      by (apply (frm_img_x segs B ARx LAWS ly S Hp W' mem' md' 1 pos a HAR' Hfin);
          rewrite <- HFF; change (fs_frame_bytes 1) with 128; lia).
    apply dt_bkN; [lia | exact Hni|].
    apply (F4 1 pos a Hfin); [left | intros Hc; exact (inFP_nil _ Hc)].
    unfold in_zr, frame_rng. cbn [fst snd]. rewrite <- HFF.
    change (fs_frame_bytes 1) with 128. lia. }
  assert (KFS : forall a, SB + FF / 8 <= a < SB + FF / 8 + 16 -> abyte_kept W mem W' mem' a).
  { intros a Ha.
    assert (Hni : ~ in_img segs a) by (intros Hi; pose proof (pa_segs_low a Hi) as Hb; lia).
    apply dt_bkN; [lia | exact Hni|].
    apply (F4 1 pos a Hfin); [right | intros Hc; exact (inFP_nil _ Hc)].
    unfold in_zr. cbn [fst snd]. rewrite <- HFF.
    change (fs_frame_bytes 1) with 128. change (128 / 8) with 16. rewrite <- dt_shadow. lia. }
  assert (KB : dt_KB ly S W mem W' mem').
  { intros p n a Hin Ha.
    destruct (dr_blk B ARx LAWS BLKR ly S Hp W' mem' md' p n HAR' Hin) as (P1 & P2 & P3).
    assert (Hni : ~ in_img segs a)
      by exact (blk_img_x segs B ARx LAWS ly S Hp W' mem' md' p n a HAR' Hin (dt_reqr p n a Ha)).
    apply dt_bkN; [lia | exact Hni|].
    replace a with (p + (a - p)) by lia.
    apply (F2 p n (a - p) Hin Hin (dt_reqi p n a Ha)). intros Hc. exact (inFP_nil _ Hc). }
  (* the ROM: the journal's own rom_view, at G = [] (W_journal.v ajournal_gx_rom_view) *)
  assert (HRO : rom_out segs B []).
  { intros a Ha. destruct (DR_ROM_OUT a Ha) as (_ & R2 & R3 & R4).
    split; [intros Hc; exact (inG_nil a Hc)|]. split; [exact R2 | split; [exact R3 | exact R4]]. }
  assert (HJx : ajournal_gx_x segs B PST ARx [] 0 [] STK (lf_F cx) [] ly S Hp W mem md [] ly S Hp W' mem' md' 0)
    by (apply ajournal_gx_nil_x; exact HJ).
  assert (HRV' : rom_view segs W' mem').
  { pose proof HCX as (_ & _ & _ & HRV & _).
    eapply ajournal_gx_rom_view_x; first [exact HJx | exact HRO | exact dr_pstr | exact HRV | exact LAWS | exact pa_segs_low]. }
  exact (dt_ctx_core cx Hpe m FF A FL ly S W mem W' mem' HLB HCX KS KF KFS KB HRV').
Qed.


Lemma dj_ne_of_at : forall ly S (W : world segs) mem m, amodel_at B ly S W mem m -> amodel_ne ly S W mem m false.
Proof.
  intros ly S W mem m (M1 & M2 & M3 & M4 & M5 & M6 & M7 & M8 & M9 & M10 & M11 & M12 & M13).
  split; [exact M1|]. split; [exact M2|]. split; [exact M3|].
  split; [exists (ct_ev (lm_c m)); rewrite dc_ctl_eta; exact M4|].
  repeat (split; [assumption|]). exact M13.
Qed.

(* ---- the six stages ---- *)

Lemma dc_stA : forall cx Hpe t m j si h fpos ly3 S3 Hp3 k W c,
  lf_base_x B MT XM_LIB RLO RHI fr_live_pre LIBROOM NP G_fr ARx cx Hpe ->
  DLK cx Hpe t m j si h fpos ly3 S3 Hp3 k W c ->
  SRr segs W c (dc_at cx Hpe t m j si fpos (frame_addr ly3 1 fpos) A_dc_r1 ly3 S3 Hp3 m true 0).
Proof.
  intros cx Hpe t m j si h fpos ly3 S3 Hp3 k W c HB
    (regs & mem & md & -> & HJ & HFR & HFL & HMOD & HIN & HRV & HROM & HSEP & HLS & HNP & HRI & Hatop & Hpick & Hj & Hfdj & Hef0 &
     SVN & S192 & S40 & Q1 & Q10 & R2 & R8 & R9 & R18 & R19 & R20 & R23 & R24 & R26 & R3 & R4 & R27 & Ht & R21 & R22 & R25).
  pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs.
  pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  pose proof dr_ceil_lo as HCL.
  assert (HAR : ARx ly3 S3 Hp3 W mem md) by (eapply ajournal_gx_AR_x; exact HJ).
  pose proof HMOD as (Hlen4 & HSL & HREL & HOUT & HGONE & HLOCK & HWAKE & HNFD & HNFDW & HNFDr & HTUP & HLST & HLSTW).
  pose proof HB as (HAI & HPRE).
  pose proof HPRE as (HFNP & _ & _ & _ & Hnrng & Hnlen & _).
  assert (Hn26 : c_n cx < 2 ^ 26) by (destruct Hnrng as [(Hz & _) | (Hz & _)]; lia).
  pose proof HFNP as (_ & _ & _ & _ & _ & Hstk & _).
  pose proof Hstk as (Hal16 & _ & Hceil & Hslo & Hshi & H47 & _).
  unfold LLVMF_STK in Hslo.
  assert (HFb : spZ (c_regs cx) - 352 < lf_F cx <= spZ (c_regs cx) - 320).
  { unfold lf_F. pose proof (Z.mod_pos_bound (spZ (c_regs cx) - 320) 32 ltac:(lia)). lia. }
  assert (HF32 : lf_F cx mod 32 = 0).
  { unfold lf_F. rewrite Zminus_mod, Z.mod_mod, Z.sub_diag by lia. reflexivity. }
  pose proof (pal_env B TL) as ((HE0 & HE1) & _).
  set (sp0 := spZ (c_regs cx)) in *.
  set (F := lf_F cx) in *.
  set (FF := frame_addr ly3 1 fpos) in *.
  assert (Hsp : spZ regs = F) by (unfold spZ; rewrite R2; unfold w64; apply unsigned_lit_small; unfold DR_CEIL8 in *; lia).
  assert (VLK : rg_lock fr_RG = 0x5d8ac0) by reflexivity.
  pose proof HLOCK as (LK0 & LK4 & LK8 & LKW). unfold arm in LK0, LK4, LK8, LKW.

  assert (Ho16 : (F - sp0) mod 16 = 0).
  { assert (HF32' : F = sp0 - 320 - (sp0 - 320) mod 32) by reflexivity.
    pose proof (Z.mod_pos_bound (sp0 - 320) 32 ltac:(lia)) as Hmb.
    rewrite HF32'.
    replace (sp0 - 320 - (sp0 - 320) mod 32 - sp0) with (- (320 + (sp0 - 320) mod 32)) by lia.
    assert (H32 : (sp0 - 320) mod 32 = 0 \/ (sp0 - 320) mod 32 = 16).
    { assert (E16 : (sp0 - 320) mod 16 = 0)
        by (replace (sp0 - 320) with (sp0 + (-20) * 16) by lia; rewrite Z.mod_add by lia; exact Hal16).
      pose proof (Z.div_mod ((sp0 - 320) mod 32) 16 ltac:(lia)) as D.
      assert (E2 : ((sp0 - 320) mod 32) mod 16 = 0)
        by (rewrite <- Znumtheory.Zmod_div_mod by (try lia; exists 2; reflexivity); exact E16).
      rewrite E2, Z.add_0_r in D.
      assert (Hq : (sp0 - 320) mod 32 / 16 = 0 \/ (sp0 - 320) mod 32 / 16 = 1) by lia.
      destruct Hq as [Hq | Hq]; rewrite Hq in D; lia. }
    destruct H32 as [H32 | H32]; rewrite H32; reflexivity. }

  (* ---- pthread_mutex_lock(&g_lock) ---- *)
  assert (HNOWN : forall a, rg_lock fr_RG <= a < rg_lock fr_RG + 12 -> ~ aowned B ly3 S3 a).
  { intros a Ha Ho. destruct (HG a (HGlock a Ha)) as (Hi & Hno & _).
    apply Hno. exact (proj1 (alx_owned_image _ _ _ LAWS ly3 S3 Hp3 W mem _ a HAR Hi) Ho). }
  assert (AVL : aview segs (w_H W) mem (rg_lock fr_RG) = Some 0).
  { pose proof (dj_av1 W mem (rg_lock fr_RG) 4%nat 0 LK0 ltac:(lia)) as HA.
    replace (YO0f.le_byte 0 4 0) with 0 in HA by (vm_compute; reflexivity). exact HA. }
  eapply SRr_bind.
  { eapply (aj_gx_entry_at_x B PST ARx LAWS G_fr 0 [] ESTACK (SIGMA WS_pthread_mutex_lock)
      (fun a => rg_lock fr_RG + 4 <= a < rg_lock fr_RG + 8)
      (fun _ mem' => val_mem segs (mrestrict (w_H W) mem') (rg_lock fr_RG + 4) 4 16)
      W regs mem LLVMF_STK sp0 (lf_FP fr_FP cx) (c_ly cx) (c_S cx) Hpe (c_W cx) (c_mem cx) (c_md cx)
      [(1, fpos)] ly3 S3 Hp3 md k (F - sp0) _ HG eq_refl HJ
      ltac:(rewrite Hsp; lia) Ho16
      ltac:(lia) ltac:(lia) ltac:(unfold ESTACK, LLVMF_STK; lia) R3 R4 Q1
      (ret_ok_codeptr_v A_dc_r1 ltac:(unfold A_dc_r1, A_dr_found, AF_fr_LLVMFuzzerTestOneInput; lia) eq_refl)).
    - intros a. lia.
    - intros a Hwa _. exact (dj_av_ne W mem (rg_lock fr_RG + 4) 4%nat 0 a LK4 ltac:(cbn; lia)).
    - intros a Hwa HnG. exfalso. apply HnG. apply HGlock. lia.
    - intros HPRE2 HSC2.
      exact (ALOCK ly3 S3 Hp3 W regs mem _ (rg_lock fr_RG) 0 HPRE2
        Q10 ltac:(lia) ltac:(rewrite VLK; reflexivity) ltac:(lia) AVL eq_refl LK4
        ltac:(intros a Ha; split;
              [ destruct (Z_lt_le_dec a (rg_lock fr_RG + 4)) as [Hlt | Hge];
                [ exact (dj_av_ne W mem (rg_lock fr_RG) 4%nat 0 a LK0 ltac:(cbn; lia))
                | exact (dj_av_ne W mem (rg_lock fr_RG + 4) 4%nat 0 a LK4 ltac:(cbn; lia)) ]
              | rewrite Hsp; unfold ESTACK, DR_CEIL8 in *; lia ])
        ltac:(intros a Ha; split;
              [ replace a with (rg_lock fr_RG + (a - rg_lock fr_RG)) by lia; exact (LKW (a - rg_lock fr_RG) ltac:(lia))
              | split; [ apply HNOWN; lia | rewrite Hsp; unfold ESTACK, DR_CEIL8 in *; lia ] ])
        (fun a Ha HK => proj2 (proj2 (HG a (HGlock a ltac:(lia)))) (proj1 (proj2 HK)))). }
  cbv beta. intros W2 c2 Hwle2 (-> & regs2 & mem2 & md2 & -> & HJa & HPa & Hlk2 & Hfra & Hpresa).

  assert (PR2 : forall r : bv 5, acallee_saved (bv_unsigned r) -> getr regs2 r = getr regs r)
    by (intros r Hr; exact (dj_pres regs regs2 r HPa Hr)).
  assert (KL : forall a, 0 <= a < 2 ^ 64 -> ~ (rg_lock fr_RG + 4 <= a < rg_lock fr_RG + 8) -> ~ (F - ESTACK <= a < F) ->
      aview segs (w_H W) mem2 a = aview segs (w_H W) mem a)
    by (intros a Ha H1 H2; apply Hfra; [exact Ha | exact H1 | replace (sp0 + (F - sp0)) with F by lia; exact H2]).
  assert (Hfin : In (1, fpos) (frames S3)).
  { pose proof HJ as (_ & _ & (memS & HJ0 & _) & _). pose proof HJ0 as (_ & _ & _ & _ & _ & Hfrs & _).
    rewrite Hfrs. left. reflexivity. }
  assert (HKY : Forall (fun e => Z.of_nat (length (re_keys e)) <= re_nheld e) (lm_es m))
    by (apply Forall_forall; intros e _; apply dr_keys_le).
  pose proof (dj_ne_lockstep ly3 S3 Hp3 W mem md mem2 m false true F HAR HKY (dj_ne_of_at ly3 S3 W mem m HMOD) KL
                ltac:(unfold ESTACK, DR_CEIL8 in *; lia) Hlk2) as HNE2.
  pose proof (dj_ctx_lockstep cx Hpe m FF 0 (flag_addr ly3 1 fpos) ly3 S3 Hp3 W mem md mem2 HB HAR
                (ex_intro _ fpos (conj Hfin eq_refl))
                (conj HFR (conj HFL (conj HIN (conj HRV (conj HROM (conj SVN (conj S192 S40))))))) KL Hpresa)
    as (HFR2 & HFL2 & HIN2 & HRV2 & HROM2 & SVN2 & S1922 & S402).
  apply SRr_ret.
  exists regs2, mem2, md2, k. split; [reflexivity|].
  split.
  { unfold dc_regs.
    rewrite !PR2 by dj_cs.
    repeat (split; [assumption|]). exact R25. }
  split; [exact HJa|]. split; [reflexivity|].
  split; [exact HFR2|]. split; [exact HFL2|]. split; [exact HIN2|]. split; [exact HRV2|]. split; [exact HROM2|].
  split; [exact SVN2|]. split; [exact S1922|]. split; [exact S402|].
  split; [exact HNE2|]. split; [exact HSEP|]. exact HKY.
Qed.
Ltac dcB_perm := apply (Permutation_count_occ dcB_dec); intros ?x;
  repeat first [rewrite count_occ_app | rewrite dcB_cnt_cons]; lia.
(* every block the representation names has a positive size *)
Lemma dcB_pos_alist : forall ly S (W : world segs) mem LA l lines b,
  alist_at B ly S W mem LA l lines -> In b (alist_blks l) -> 0 < snd b.
Proof.
  intros ly S W mem LA l lines b (_ & _ & _ & _ & _ & H6 & _) Hb. unfold alist_blks in Hb.
  apply in_app_or in Hb as [Hb | Hb].
  - destruct (hl_cap l =? 0) eqn:E; [destruct Hb|]. apply Z.eqb_neq in E.
    destruct Hb as [<- | []]. cbn [snd]. destruct H6 as [(Hc & _) | (Hc & _)]; [lia|]. unfold AREC. lia.
  - apply in_map_iff in Hb as (r & <- & _). cbn [snd]. lia.
Qed.
Lemma dcB_pos_asrc : forall ly S (W : world segs) mem HA h b,
  asrc_at B ly S W mem HA h -> In b (asrc_blks h) -> 0 < snd b.
Proof.
  intros ly S W mem HA h b
    (_ & _ & _ & _ & _ & _ & _ & _ & _ & H10 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & H22 & H23 & _) Hb.
  unfold asrc_blks in Hb. destruct Hb as [<- | Hb]; [cbn [snd]; unfold APARTIAL; lia|].
  apply in_app_or in Hb as [Hb | Hb]; [exact (dcB_pos_alist _ _ _ _ _ _ _ _ H10 Hb)|].
  apply in_app_or in Hb as [Hb | Hb]; [exact (dcB_pos_alist _ _ _ _ _ _ _ _ H22 Hb) | exact (dcB_pos_alist _ _ _ _ _ _ _ _ H23 Hb)].
Qed.
(* LS_cnt's guard (msz_ok) at a cut's model: the relay's entries have a capacity and
   key texts of bounded length (aentry_ok, W_rep.v:118 / :139), each held slot's two line lists records of bounded
   length (alist_at .. true, W_rep.v:103).  The proof is _event_x.v's ev_msz_x, at the three conjuncts of amodel_at
   (and of amodel_ne) it reads *)
Lemma dr_msz_x : forall ly S (W : world segs) mem m,
  length (lm_hs m) = 4%nat -> (forall i, (i < 4)%nat -> aslot B ly S W mem i (nth i (lm_hs m) None)) ->
  arelay_at B fr_RG ly S W mem (lm_G m) (lm_es m) -> msz_ok m.
Proof.
  intros ly S W mem m Hlen Hslots HREL. unfold msz_ok, texts_ok.
  assert (Hlist : forall LA l, alist_at B ly S W mem LA l true ->
      Forall (fun r => Z.of_nat (length (snd r)) <= APARTIAL) (hl_recs l)).
  { intros LA l (_ & _ & _ & _ & _ & _ & _ & _ & HF). revert HF. apply Forall_impl.
    intros r (_ & _ & Hr & _). exact (proj2 (Hr eq_refl)). }
  split.
  - pose proof HREL as (_ & _ & _ & _ & _ & _ & _ & _ & _ & HAE & _). revert HAE. apply Forall_impl.
    intros e0 He0.
    pose proof He0 as (_ & _ & _ & _ & _ & Hcap & _). split; [lia|].
    pose proof He0 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HK).
    revert HK. apply Forall_impl. intros kk (_ & _ & _ & Hkk). lia.
  - apply Forall_forall. intros o Ho.
    destruct (In_nth_error _ _ Ho) as (i & Hi).
    assert (Hi4 : (i < 4)%nat) by (rewrite <- Hlen; apply nth_error_Some; rewrite Hi; discriminate).
    pose proof (Hslots i Hi4) as Hsl.
    rewrite (nth_error_nth _ _ None Hi) in Hsl.
    destruct o as [h|]; [|exact I]. cbn [aslot] in Hsl.
    pose proof Hsl as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HEX & HHD & _).
    split; [exact (Hlist _ _ HEX) | exact (Hlist _ _ HHD)].
Qed.
(* the entry's bundles at the drain's call (s5-r1d's dr3_epre, ReplyLSDrain3.v:78; ls3_kh, ReplyLS3Arms.v:305):
   aentry_ok's clauses W_rep.v:124-125, :131-132, :139 *)
Lemma dcB_epre : forall ly S (W : world segs) mem e, aentry_ok B ly S W mem e ->
  dr3_epre e /\ ls3_kh e.
Proof.
  intros ly S W mem e (_ & _ & _ & _ & _ & Hc & Hu1 & Hu2 & Hnul & _ & _ & Hkh & _ & _ & HK).
  split.
  - unfold dr3_epre. split; [exact Hc|]. split; [lia|]. split; [exact Hnul|].
    split; [intros Hz; destruct Hkh as [(Hz0 & _) | (_ & _ & _ & H8 & _)]; [contradiction | exact H8]|].
    revert HK. apply Forall_impl. intros kk (_ & _ & _ & Hkk & _). exact Hkk.
  - unfold ls3_kh. destruct Hkh as [(Hz & Hk) | (Hz & _ & Hn & _)].
    + left. split; assumption.
    + right. split; assumption.
Qed.
(* the source's bundles at the drain's call (dr3_hpre, ReplyLSDrain3.v:85; ls3_hn, ReplyLS3Arms.v:308): asrc_at's
   offset clause W_rep.v:104-105 and its three lists' alist_at (count clause :81, pending texts non-empty :91) *)
Lemma dcB_hpre : forall ly S (W : world segs) mem HA h, asrc_at B ly S W mem HA h ->
  dr3_hpre h /\ ls3_hn h.
Proof.
  intros ly S W mem HA h Hs.
  pose proof Hs as (_ & _ & _ & _ & _ & _ & _ & _ & _ & HP & _ & _ & _ & _ & Hoff & _ & _ & _ & _ & _ & _ & HE & HH & _).
  pose proof HP as (_ & _ & _ & _ & (HnP & _) & _ & _ & _ & HFP).
  pose proof HE as (_ & _ & _ & _ & (HnE & _) & _).
  pose proof HH as (_ & _ & _ & _ & (HnH & _) & _).
  split.
  - unfold dr3_hpre. split; [exact Hoff|].
    revert HFP. apply Forall_impl. intros r (_ & _ & _ & Hr). exact (Hr eq_refl).
  - unfold ls3_hn. split; [exact HnP|]. split; [exact HnE | exact HnH].
Qed.
(* g_out's capacity is not negative (aout_at's last clause, W_rep.v) *)
Lemma dcB_cap0 : forall ly S (W : world segs) mem c O mx no cap out,
  aout_at B fr_RG ly S W mem c O mx no cap out -> 0 <= cap.
Proof.
  intros ly S W mem c O mx no cap out HO.
  pose proof HO as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hblk).
  destruct Hblk as [(Hc & _) | (Hc & _)]; lia.
Qed.
Lemma dcB_pos_aentry : forall ly S (W : world segs) mem e b,
  aentry_ok B ly S W mem e -> In b (aentry_blks e) -> 0 < snd b.
Proof.
  intros ly S W mem e b (_ & _ & _ & _ & _ & _ & _ & _ & _ & K10 & _ & K12 & _ & _ & _) Hb.
  unfold aentry_blks in Hb. apply in_app_or in Hb as [Hb | Hb].
  - destruct (re_cap e =? 0) eqn:E; [destruct Hb|]. apply Z.eqb_neq in E.
    destruct Hb as [<- | []]. cbn [snd]. destruct K10 as [(Hc & _) | (Hc & _)]; lia.
  - apply in_app_or in Hb as [Hb | Hb].
    + destruct (re_hp e =? 0) eqn:E; [destruct Hb|]. apply Z.eqb_neq in E.
      destruct Hb as [<- | []]. cbn [snd]. destruct K12 as [(Hz & _) | (_ & _ & _ & Hk & _)]; lia.
    + apply in_map_iff in Hb as (kk & <- & _). cbn [snd]. lia.
Qed.
Lemma dcB_pos_aout : forall ly S (W : world segs) mem c O mx no cap out b,
  aout_at B fr_RG ly S W mem c O mx no cap out -> In b (aout_blks cap out) -> 0 < snd b.
Proof.
  intros ly S W mem c O mx no cap out b HO Hb.
  pose proof HO as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hblk).
  unfold aout_blks in Hb. destruct (cap =? 0) eqn:E; [destruct Hb|]. apply Z.eqb_neq in E.
  destruct Hb as [<- | []]. cbn [snd]. destruct Hblk as [(Hc & _) | (Hc & _)]; lia.
Qed.
(* drain's G is the entry's; ROM is outside it; the cells amodel_ne keeps beside drain's G are outside it and errno *)
Lemma dcB_GDR_ok : gx_ok segs B (G_DR B fr_RG).
Proof. intros a Ha. exact (HG a (HG_DR a Ha)). Qed.
Lemma dcB_rom_out : rom_out segs B (G_DR B fr_RG).
Proof.
  intros a Ha. destruct (DR_ROM_OUT a Ha) as (H1 & H2 & H3 & H4).
  split; [intros HGa; exact (H1 (HG_DR a HGa))|]. split; [exact H2|]. split; [exact H3 | exact H4].
Qed.
Lemma dcB_GK_out : forall a, inG DR_GK a \/ rg_lock fr_RG <= a < rg_lock fr_RG + 12 ->
  ~ inG (G_DR B fr_RG) a /\ ~ (as_errno B <= a < as_errno B + 4).
Proof.
  intros a Ha. pose proof HERR_HI as He.
  unfold inG, DR_GK, G_DR, G_SL in *. rewrite !Exists_cons, Exists_nil in *.
  unfold in_zr, AG_NFD, AG_THREAD_UP, AG_LISTEN, ASRC in *. cbn [fst snd] in *.
  cbn [fr_RG fr_globals rg_s rg_src rg_nsrc rg_capsrc rg_out rg_nout rg_capout rg_send_max rg_send_eintr
       rg_send_dead rg_gone rg_client rg_client_broken rg_lock rg_wake] in *.
  lia.
Qed.
(* a model block of the call's footprint is the entry's footprint's or new since the entry *)
Lemma dcB_fp_blk : forall cx m ly S b a,
  ablocks_sep B fr_FP cx m ly S -> In b (model_blks m) -> 0 < snd b -> fst b <= a < fst b + req_size (snd b) ->
  (inFP (lf_FP fr_FP cx) a /\ exists p n, In (p, n) (ablocks B ly S) /\ p <= a < p + req_size n) \/
  in_tmp_block (ablocks B (c_ly cx) (c_S cx)) (ablocks B ly S) a.
Proof.
  intros cx m ly S [p n] a ((rest & HP) & H2) Hb Hpos Ha. cbn [fst snd] in Hpos, Ha.
  assert (HbL : In (p, n) (ablocks B ly S)).
  { apply (Permutation_in _ (Permutation_sym HP)). apply in_or_app. right. apply in_or_app. left. exact Hb. }
  destruct (in_dec dcB_dec (p, n) (ablocks B (c_ly cx) (c_S cx))) as [Hin | Hnin].
  - left. split; [|exists p, n; split; [exact HbL | exact Ha]].
    destruct (H2 _ Hb) as [Hc | Hc]; [exfalso; exact (Hc Hin)|].
    exact (Hc a Ha).
  - right. exists p, n. split; [exact HbL|]. split; [exact Hnin | exact Ha].
Qed.
Lemma dcB_nfp_blk : forall ly S Hp (W : world segs) mem md G SA X p0 n0 a,
  ARx ly S Hp W mem md -> In (G, ATABLE) (ablocks B ly S) -> G <= SA -> SA + AENT <= G + ATABLE ->
  (forall b, In b X -> In b (ablocks B ly S)) ->
  In (p0, n0) (ablocks B ly S) -> ~ In (p0, n0) X -> p0 <= a < p0 + req_size n0 ->
  ((p0, n0) <> (G, ATABLE) \/ ~ (SA <= a < SA + AENT)) ->
  ~ inFP ((SA, SA + AENT) :: ablocks_fp X) a.
Proof.
  intros ly S Hp W mem md G SA X p0 n0 a HAR HGin H1 H2 HXL Hb0 HnX Ha Hor.
  apply (dcB_nfp G); [exact H1 | exact H2 | |].
  - intros (Ht & Hs). destruct Hor as [Hne | Hn]; [|exact (Hn Hs)].
    apply (dj_apart ly S Hp W mem md p0 n0 G ATABLE a HAR Hb0 HGin Hne Ha).
    replace (req_size ATABLE) with ATABLE by reflexivity. exact Ht.
  - intros [q r] Hb Hq. cbn [fst snd] in Hq.
    assert (Hne : (p0, n0) <> (q, r)) by (intros E; apply HnX; rewrite E; exact Hb).
    exact (dj_apart ly S Hp W mem md p0 n0 q r a HAR Hb0 (HXL _ Hb) Hne Ha Hq).
Qed.
Lemma dcB_nfp_frm : forall ly S Hp (W : world segs) mem md G SA X cid pos a,
  ARx ly S Hp W mem md -> In (G, ATABLE) (ablocks B ly S) -> G <= SA -> SA + AENT <= G + ATABLE ->
  (forall b, In b X -> In b (ablocks B ly S)) -> In (cid, pos) (frames S) ->
  (frame_addr ly cid pos <= a < frame_addr ly cid pos + fs_frame_bytes cid \/
   shadow_addr (frame_addr ly cid pos) <= a < shadow_addr (frame_addr ly cid pos) + fs_frame_bytes cid / 8) ->
  ~ inFP ((SA, SA + AENT) :: ablocks_fp X) a.
Proof.
  intros ly S Hp W mem md G SA X cid pos a HAR HGin H1 H2 HXL Hfr Ha.
  assert (HNB : forall p n, In (p, n) (ablocks B ly S) -> ~ (p <= a < p + req_size n)).
  { intros p n Hin Hpa.
    destruct (frames_bounds_x segs B ARx LAWS ly S Hp W mem md cid pos HAR Hfr) as (Hf0 & Hfc & _).
    destruct (alx_blocks _ _ _ LAWS ly S Hp W mem md p n HAR Hin) as (_ & _ & _ & Happ & _).
    pose proof (sep_block_frame_x segs B ARx LAWS ly S Hp W mem md p n cid pos HAR Hin Hfr) as Hd.
    unfold zdisjoint in Hd. cbn [fst snd] in Hd.
    pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
    pose proof (fs_frame_bytes_nonneg cid) as Hfb.
    pose proof (shadow_addr_bounds (frame_addr ly cid pos) ltac:(lia)) as Hs1.
    pose proof (shadow_addr_bounds (frame_addr ly cid pos + fs_frame_bytes cid) ltac:(lia)) as Hs2.
    pose proof (shadow_range_end (frame_addr ly cid pos) (fs_frame_bytes cid) Hfb) as Hs3.
    unfold in_app, kLowShadowBeg in Happ.
    destruct Ha as [Ha | Ha]; lia. }
  apply (dcB_nfp G); [exact H1 | exact H2 | |].
  - intros (Ht & _). apply (HNB G ATABLE HGin). replace (req_size ATABLE) with ATABLE by reflexivity. exact Ht.
  - intros [q r] Hb Hq. exact (HNB q r (HXL _ Hb) Hq).
Qed.
(* dr_post without the return configuration, the composed journal at G_fr and the callee-saved registers *)
Definition dcB_post (regs : bvmap 5 word) ly S Hp (W : world segs) (mem : word -> option byte) (md : Model)
  (SA HA : Z) (e : rentry) (h : hsrc) (c : ctl) (O : list byte) (mx no cap out : Z)
  (ly' : alayout) (S' : astate) (Hp' : list Z) (W' : world segs) (regs' : bvmap 5 word) (mem' : word -> option byte) (md' : Model)
  : Prop :=
exists k (e' : rentry) (h' : hsrc) (out' ev' : Z) (LB : list byte) rest,
let fin := dr_fin c mx no cap e h in
let live := dr_live c h in
let cap' := if live then drain_b_c.ds_ocap fin else cap in
ajournal_gx_x segs B PST ARx (G_DR B fr_RG) 0 [] DRAIN_STK_x (spZ regs) (dr_fp SA e h cap out) ly S Hp W mem md [] ly' S' Hp' W' mem' md' k /\
apres_kept B W mem W' mem' /\
mo_le MT S S' (dr_cost MT c mx no cap e h) /\ NP S' /\
Permutation (ablocks B ly S) (aentry_blks e ++ asrc_blks h ++ aout_blks cap out ++ rest) /\
Permutation (ablocks B ly' S') (aentry_blks e' ++ asrc_blks h' ++ aout_blks cap' out' ++ rest) /\
garr8 segs (arm W' mem') SA (bzs (entry_bytes e')) /\ awr W' mem' SA AENT /\ aentry_ok B ly' S' W' mem' e' /\
Z.of_nat (length (re_keys e')) <= re_nheld e' /\
re_fd e' = re_fd e /\ re_eof e' = (if hs_closed h =? 1 then 1 else re_eof e) /\ 0 < re_cap e' /\
re_cap e' = drain_b_c.ds_cap fin /\ bzs (re_U e') = drain_b_c.ds_u fin /\
re_skip e' = (if drain_b_c.ds_skip fin then 1 else 0) /\
drain_b_c.keys_texts (re_keys e') = drain_b_c.ds_H fin /\ drain_b_c.ent_ka e' = drain_b_c.ds_ka fin /\
((re_hp e' = re_hp e /\ re_kh e' = re_kh e) \/ re_kh e' <= 2 ^ 30) /\
NoDup (drain_b_c.keys_texts (re_keys e')) /\
same_set (drain_b_c.keys_texts (re_keys e')) (upds (drain_b_c.keys_texts (re_keys e)) (dr_lines h)) /\
asrc_at B ly' S' W' mem' HA h' /\
(forall a, rg_s fr_RG <= a < rg_s fr_RG + 4 * ASRC -> ~ (HA <= a < HA + ASRC) -> abyte_kept W mem W' mem' a) /\
hl_cap (hs_expected h') = drain_b_c.ds_ecap fin /\
hl_cap (hs_expected h') <= Z.max 8 (Z.max (hl_cap (hs_expected h)) (2 * hl_n (hs_expected h'))) /\
hs_fd h' = hs_fd h /\ hs_closed h' = hs_closed h /\ hs_eintr h' = 0 /\
hl_recs (hs_pending h') = [] /\ hs_off h' = 0 /\
hl_v (hs_pending h') = hl_v (hs_pending h) /\ hl_cap (hs_pending h') = hl_cap (hs_pending h) /\
hs_partial h' = hs_partial h /\
hs_state h' = feed (hs_state h) (bzs (pending_stream h)) /\
map snd (hl_recs (hs_expected h')) = map snd (hl_recs (hs_expected h)) ++ map (map (Z_to_bv 8)) (dr_lines h) /\
firstn (length (hl_recs (hs_expected h))) (hl_recs (hs_expected h')) = hl_recs (hs_expected h) /\
hs_held h' = hs_held h /\
re_skip e' = hs_overlong h' /\ (re_skip e' = 0 -> bzs (re_U e') = bzs (hs_W h')) /\
bzs LB = with_nul (dr_lines h) /\
aout_at B fr_RG ly' S' W' mem' (dr_ctl c h ev') (if live then O ++ LB else O) mx (if live then no + dr_tot h else no) cap' out'.
Lemma dcB_post_of : forall regs ly S Hp (W : world segs) mem md SA HA e h c O mx no cap out kr (W' : world segs) c',
  dr_post_x B PST ARx MT RP fr_RG regs ly S Hp W mem md SA HA e h c O mx no cap out kr W' c' ->
  exists ly' S' Hp' regs' mem' md' k, c' = mkCfg (mkst regs' (getr regs 1) mem' (seg_rom segs)) md' /\
    ajournal_gx_x segs B PST ARx G_fr 0 [] DRAIN_STK_x (spZ regs) (dr_fp SA e h cap out) ly S Hp W mem md [] ly' S' Hp' W' mem' md' k /\
    aregs_preserved regs regs' /\
    dcB_post regs ly S Hp W mem md SA HA e h c O mx no cap out ly' S' Hp' W' regs' mem' md'.
Proof.
  intros regs ly S Hp W mem md SA HA e h c O mx no cap out kr W' c'
    (ly' & S' & Hp' & regs' & mem' & md' & k & e' & h' & out' & ev' & LB & rest & HP).
  cbv zeta in HP. destruct HP as (Hc & HJ & HPR & HAPK & HMO & HRM & HP1 & HP2 & HG8 & HAW & HEOK & REST).
  exists ly', S', Hp', regs', mem', md', k. split; [exact Hc|].
  split; [exact (ajournal_gx_G_mono_x segs B PST ARx (G_DR B fr_RG) G_fr 0 [] DRAIN_STK_x (spZ regs) _ ly S Hp W mem md [] ly' S' Hp' W' mem' md'
                   k HG_DR HJ)|].
  split; [exact HPR|].
  exists k, e', h', out', ev', LB, rest. cbv zeta. split; [exact HJ|].
  exact (conj HAPK (conj HMO (conj (proj1 (RP_NP S' kr) HRM) (conj HP1 (conj HP2 (conj HG8 (conj HAW (conj HEOK
    (conj (dr_keys_le e') REST))))))))).
Qed.
Lemma dcB_cost_ctl : forall c ev mx no cap e h, dr_cost MT (dc_ctl c ev) mx no cap e h = dr_cost MT c mx no cap e h.
Proof. intros. unfold dr_cost. rewrite dcB_tr_ctl. reflexivity. Qed.
(* a member of a literal list *)
Ltac dcB_in := repeat (first [left; reflexivity | right]).
(* a byte of one of DR_GK's cells (the cell's range is the hypothesis H) *)
Ltac dcB_gk H := left; unfold inG, DR_GK;
  repeat (first [apply Exists_cons_hd; unfold in_zr; cbn [fst snd]; clear - H; lia | apply Exists_cons_tl]).

(* what dc_stB hands the step rules (TX_LS_cnl_pre / TX_LS_drain_step / check_no_loss's count): the entry's and the
   source's bundles at the call (s5-r1d's dr3_epre / ls3_kh / dr3_hpre / ls3_hn and g_out's 0 <= cap), dr_post's
   frame (its two Permutations with one rest, W_contract_x.v dr_post_x), its entry / source clauses beyond dr_dfun
   (dr3_epost: aentry_ok's capacity clause and the held-array disjunct; dr3_hpost: the pending list's capacity and the
   expected list's capacity bound; ls3_dpost: asrc_at's count clause of the expected list), the cut's NP at the
   return (dr_post_x's rp_RM) and check_no_loss's count premise at the return (LS_cnt, DR_CNT_grow, lsc_cnl_call) *)
Definition dcB_out (m : lmod) (j : nat) (h : hsrc) (ly : alayout) (S : astate) (e' : rentry) (h' : hsrc)
  (out' : Z) (ly' : alayout) (S' : astate) : Prop :=
  dr3_epre (nth j (lm_es m) dr_e0) /\ ls3_kh (nth j (lm_es m) dr_e0) /\
  dr3_hpre h /\ ls3_hn h /\ 0 <= lm_cap m /\
  (exists rest,
     Permutation (ablocks B ly S)
       (aentry_blks (nth j (lm_es m) dr_e0) ++ asrc_blks h ++ aout_blks (lm_cap m) (lm_out m) ++ rest) /\
     Permutation (ablocks B ly' S') (aentry_blks e' ++ asrc_blks h' ++ aout_blks (dr_cap1 m j h) out' ++ rest)) /\
  dr3_epost (nth j (lm_es m) dr_e0) e' h /\ dr3_hpost h h' /\
  ls3_dpost m j h e' h' /\
  NP S' /\ cnt_ok_pk RP (cnl_pk (hs_expected h') (hs_held h')) (ablocks B ly' S').
Lemma dc_stB : forall cx Hpe t m j si h fpos FF ly S Hp W c,
  lf_base_x B MT XM_LIB RLO RHI fr_live_pre LIBROOM NP G_fr ARx cx Hpe ->
  dc_static cx t m j si h -> LSx cx t m ly S -> NP S ->
  dc_at cx Hpe t m j si fpos FF A_dc_r1 ly S Hp m true 0 W c ->
  SRr segs W c (fun W' c' => exists ly' S' Hp' e' h' out' ev' LB,
    dc_at cx Hpe t m j si fpos FF A_dc_r2 ly' S' Hp' (dr_m1 m j si h h' e' ev' LB out') true 0 W' c' /\
    mo_le MT S S' (dr_cost MT (lm_c m) (lm_mx m) (Z.of_nat (length (lm_O m))) (lm_cap m) (nth j (lm_es m) dr_e0) h) /\
    dr_dfun m si h j e' h' LB /\ dcB_out m j h ly S e' h' out' ly' S').
Proof.
  intros cx Hpe t m j si h fpos FF ly S Hp W c HB (Hatop & Hpick & Hj & Hfdj & Hef0 & HRI) HLS HNP
    (regs & mem & md & k & -> & HR & HJ & HFFe & HFR & HFL & HIN & HRV & HJT & SVN & S192 & S40 & HNE & HSEP & HKY).
  pose proof HR as (R2 & R8 & R9 & R18 & R19 & R20 & R23 & R24 & R26 & R3 & R4 & R27 & Ht & R21 & R22 & R25).
  pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs.
  pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  pose proof dr_ceil_lo as HCL.
  assert (HAR : ARx ly S Hp W mem md) by (eapply ajournal_gx_AR_x; exact HJ).
  pose proof HNE as (Hlen4 & HSL & HREL & (ev0 & HOUT) & HGONE & HLOCK & HWAKE & HNFD & HNFDW & HNFDr & HTUP & HLST & HLSTW).
  pose proof HB as (HAI & HPRE).
  pose proof HPRE as (HFNP & _ & _ & _ & Hnrng & Hnlen & _).
  pose proof HFNP as (_ & _ & _ & _ & _ & Hstk & _).
  pose proof Hstk as (Hal16 & _ & Hceil & Hslo & Hshi & H47 & _).
  unfold LLVMF_STK in Hslo.
  assert (HFb : spZ (c_regs cx) - 352 < lf_F cx <= spZ (c_regs cx) - 320).
  { unfold lf_F. pose proof (Z.mod_pos_bound (spZ (c_regs cx) - 320) 32 ltac:(lia)). lia. }
  pose proof (pal_env B TL) as ((HE0 & HE1) & _).
  assert (Hsp : spZ regs = lf_F cx)
    by (unfold spZ; rewrite R2; unfold w64; apply unsigned_lit_small; unfold DR_CEIL8 in *; lia).
  (* ---- 0x84a54: mv a0,s6 ; jal drain ---- *)
  destruct (dc_plain_entry A_dc_r1 W regs mem R26) as [HS SHOK].
  remember (Eimg (Ereg regs [])) as E eqn:HE.
  assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
  assert (HAE : env_agree 32 (Ereg regs []) E)
    by (rewrite HE; split; [intros n Hn; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
  clear HE.
  paj_run_to_tok_x RUNTO HS HJ SHOK DRspan AF_fr_drain.
  { apply awr_ok_x_nil. }
  dr_meq HF Em.
  pose proof (regs_kept_of_st_ok_pi _ _ _ regs _ [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv
                HS HAE ltac:(vm_compute; reflexivity)) as KR3.
  cbn [ms_regs restrict] in KR3.
  prreg HS (1%bv : bv 5) Q1d. prreg HS (10%bv : bv 5) Q10d.
  pmkst HS. rewrite Em in *. clear HF HFr HG0.
  set (mdD := with_vm_backing (m_vm_lazy md) mat md) in *.
  rewrite (proj1 HAE 22%nat ltac:(lia)), (ew_Ereg_nat regs [] 22 22%bv eq_refl), R22 in Q10d.
  assert (HspD : spZ (ms_regs ms) = lf_F cx) by (unfold spZ; rewrite (KR3 2%bv ltac:(dcB_in)); exact Hsp).
  (* ---- the journal at the call: the fake frame, the blocks freed since the entry ---- *)
  assert (Hfin : In (1, fpos) (frames S)).
  { pose proof HJ as (_ & _ & (memS & HJ0 & _) & _). pose proof HJ0 as (_ & _ & _ & _ & _ & Hfrs & _).
    rewrite Hfrs. left. reflexivity. }
  assert (HGONE0 : forall p n i, In (p, n) (ablocks B (c_ly cx) (c_S cx)) -> ~ In (p, n) (ablocks B ly S) ->
      0 <= i < req_size n -> inFP (lf_FP fr_FP cx) (p + i)).
  { pose proof HJ as (_ & _ & (memS & HJ0 & _) & _).
    pose proof HJ0 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hg & _). exact Hg. }
  (* ---- drain's premises ---- *)
  pose proof Hpick as (_ & Hsi4 & Hhsi).
  destruct (dr_pads_of_relay ly S W mem (lm_G m) (lm_es m) HREL) as (HPAD & HFDS).
  pose proof HREL as (RL1 & RL2 & RL3 & RL4 & RL5 & RL6 & RL7 & HGin & (tl & HTAB) & HENT & HNDF & HTBN).
  (* drain's entry pointer is 8-aligned: the table is a live block (16-aligned) and an entry is 56 bytes *)
  assert (HSA8 : (lm_G m + AENT * Z.of_nat j) mod 8 = 0).
  { destruct (alx_blocks _ _ _ LAWS ly S Hp W mem md _ _ HAR HGin) as (HG16 & _).
    pose proof (Z.div_mod (lm_G m) 16 ltac:(lia)) as HGd. rewrite HG16, Z.add_0_r in HGd.
    rewrite HGd. unfold AENT.
    replace (16 * (lm_G m / 16) + 56 * Z.of_nat j) with ((2 * (lm_G m / 16) + 7 * Z.of_nat j) * 8) by ring.
    apply Z_mod_mult. }
  assert (HEOK : aentry_ok B ly S W mem (nth j (lm_es m) dr_e0))
    by (rewrite Forall_forall in HENT; apply HENT, nth_In; exact Hj).
  destruct (RI_pair cx t m si h j HRI Hpick Hj Hfdj Hef0) as (HSK & HSKU & _ & _).
  destruct (dr_blk B ARx LAWS BLKR ly S Hp W mem md (lm_G m) ATABLE HAR HGin) as (HG4096 & HGceil & _).
  assert (HSA : lm_G m <= lm_G m + AENT * Z.of_nat j /\ lm_G m + AENT * Z.of_nat j + AENT <= lm_G m + ATABLE)
    by (unfold AENT, ATABLE; lia).
  assert (HSRC0 : asrc_at B ly S W mem (rg_s fr_RG + ASRC * Z.of_nat si) h).
  { pose proof (HSL si Hsi4) as Hs. rewrite Hhsi in Hs. exact Hs. }
  pose proof (dr_tbl_entry W mem (lm_G m) (lm_es m) tl j HTAB HPAD Hj) as HEB.
  assert (HEL : length (bzs (entry_bytes (nth j (lm_es m) dr_e0))) = 56%nat).
  { pose proof HEOK as (_ & _ & Hq1 & Hq2 & _). rewrite dra_bzs_length. apply entry_bytes_length; assumption. }
  assert (HEW : awr W mem (lm_G m + AENT * Z.of_nat j) AENT).
  { pose proof (dr_awr_of_garr8 ly S Hp W mem md (lm_G m) ATABLE (lm_G m + AENT * Z.of_nat j)
                  (bzs (entry_bytes (nth j (lm_es m) dr_e0))) HAR HGin ltac:(lia)
                  ltac:(rewrite HEL; replace (req_size ATABLE) with ATABLE by reflexivity; unfold AENT, ATABLE in *; lia)
                  HEB) as Hw.
    rewrite HEL in Hw. exact Hw. }
  assert (HOTH : aothers_at fr_RG W mem si (re_fd (nth j (lm_es m) dr_e0))).
  { intros i Hi Hne. pose proof (HSL i Hi) as Hs. revert Hs.
    destruct (nth i (lm_hs m) None) as [hi|] eqn:Ehi; intros Hs; cbn [aslot] in Hs.
    - exists (hs_fd hi), (hs_open hi). pose proof Hs as (V1 & V2 & _).
      split; [exact V1|]. split; [exact V2|]. right. rewrite Hfdj.
      assert (Fi : 0 <= hs_fd hi < 2 ^ 31) by (unfold asrc_at in Hs; tauto).
      assert (Fh : 0 <= hs_fd h < 2 ^ 31) by (unfold asrc_at in HSRC0; tauto).
      rewrite !Z.mod_small by lia.
      exact (RI_fds cx t m i si hi h HRI Hi Hsi4 Hne Ehi Hhsi).
    - exists 0, 0. destruct Hs as (Hz & _).
      pose proof (dcB_zero_vm _ _ (Z.to_nat ASRC) 0 Hz ltac:(lia)
                    ltac:(rewrite Z2Nat.id by (unfold ASRC; lia); unfold ASRC; lia)) as Hz0.
      rewrite Z.add_0_r in Hz0.
      split; [exact Hz0|]. split; [|left; reflexivity].
      exact (dcB_zero_vm _ _ (Z.to_nat ASRC) 4 Hz ltac:(lia)
               ltac:(rewrite Z2Nat.id by (unfold ASRC; lia); unfold ASRC; lia)). }
  assert (HXM : forall b, In b (aentry_blks (nth j (lm_es m) dr_e0) ++ asrc_blks h ++ aout_blks (lm_cap m) (lm_out m)) ->
      In b (model_blks m)).
  { intros b Hb. unfold model_blks. right. apply in_app_or in Hb as [Hb | Hb].
    - apply in_or_app. left. apply in_concat. exists (aentry_blks (nth j (lm_es m) dr_e0)).
      split; [apply in_map, nth_In; exact Hj | exact Hb].
    - apply in_or_app. right. apply in_app_or in Hb as [Hb | Hb].
      + apply in_or_app. left. apply in_concat. exists (slot_blks (Some h)). split; [|exact Hb].
        rewrite <- Hhsi. apply in_map, nth_In. lia.
      + apply in_or_app. right. exact Hb. }
  pose proof HSEP as HSEPc.
  destruct HSEP as ((rest0 & HPm0) & HSEP2).
  assert (HXL : forall b, In b (aentry_blks (nth j (lm_es m) dr_e0) ++ asrc_blks h ++ aout_blks (lm_cap m) (lm_out m)) ->
      In b (ablocks B ly S)).
  { intros b Hb. apply (Permutation_in _ (Permutation_sym HPm0)).
    apply in_or_app. right. apply in_or_app. left. exact (HXM b Hb). }
  assert (HXP : forall b, In b (aentry_blks (nth j (lm_es m) dr_e0) ++ asrc_blks h ++ aout_blks (lm_cap m) (lm_out m)) ->
      0 < snd b).
  { intros b Hb. apply in_app_or in Hb as [Hb | Hb]; [exact (dcB_pos_aentry _ _ _ _ _ _ HEOK Hb)|].
    apply in_app_or in Hb as [Hb | Hb];
      [exact (dcB_pos_asrc _ _ _ _ _ _ _ HSRC0 Hb) | exact (dcB_pos_aout _ _ _ _ _ _ _ _ _ _ _ HOUT Hb)]. }
  unfold model_blks in HPm0.
  pose proof (dr_concat_nth_perm _ _ aentry_blks (lm_es m) j dr_e0 Hj) as HCA.
  pose proof (dr_concat_nth_perm _ _ slot_blks (lm_hs m) si None ltac:(lia)) as HCS.
  rewrite Hhsi in HCS. cbn [slot_blks] in HCS.
  pose proof (dcB_perm_pre _ _ _ _ _ _ _ _ _ _ _ HPm0 HCA HCS) as HPERM0.
  assert (HU : Z.of_nat (length (re_U (nth j (lm_es m) dr_e0))) <= APARTIAL)
    by (pose proof HEOK as (_ & _ & _ & _ & _ & _ & Hu1 & Hu2 & _); lia).
  destruct (LS_drain_pre cx t m ly S si h j HLS HRI Hatop Hpick Hj Hfdj Hef0 Ht HU HXP) as (L1 & L2 & L3 & L4 & L5 & L6).
  rewrite <- (dcB_tr_ctl (lm_c m) ev0) in L4, L5. rewrite <- (dcB_cost_ctl (lm_c m) ev0) in L6.
  (* ---- the room round: the entry's and the source's bundles, LS_cnt's counts at the cut, the cut's NP ---- *)
  destruct (dcB_epre ly S W mem _ HEOK) as (EPRE & EKH).
  destruct (dcB_hpre ly S W mem _ h HSRC0) as (HPRE3 & HHN3).
  pose proof (dcB_cap0 _ _ _ _ _ _ _ _ _ _ HOUT) as CAP0.
  pose proof (dr_msz_x ly S W mem m Hlen4 HSL HREL) as HMSZ.
  destruct (RI_src cx t m si h HRI Hpick) as (Hexp0 & _ & _).
  pose proof (LS_cnt cx t m ly S si h j HLS HRI Hatop Hpick Hj Hfdj Hef0 HMSZ Ht HU HXP (proj1 HPRE3)) as HCNT.
  assert (HCNTd : cnt_ok_pk RP (dr_pk (dc_ctl (lm_c m) ev0) (lm_mx m) (Z.of_nat (length (lm_O m))) (lm_cap m)
      (nth j (lm_es m) dr_e0) h) (ablocks B ly S)).
  { refine (cnt_ok_pk_mono RP _ _ (ablocks B ly S) (ablocks B ly S) _ HCNT).
    intros P. unfold dr_pk. cbv beta. rewrite dcB_tr_ctl. lia. }
  assert (HRMd : rp_RM RP S (Z.to_nat (dr_cost MT_rk (dc_ctl (lm_c m) ev0) (lm_mx m) (Z.of_nat (length (lm_O m)))
      (lm_cap m) (nth j (lm_es m) dr_e0) h) + 0)%nat) by (apply RP_NP; exact HNP).
  destruct (dr_afn_pre_at cx Hpe ly S Hp fpos k W mem mdD (ms_regs ms) DRAIN_STK_x HB HJ) as (ch & HPRED).
  { rewrite HFFe. exact (dr_aframe_false cx FF W mem HFR). }
  { exact HspD. }
  { rewrite Q1d. apply ret_ok_codeptr_v; [lia | reflexivity]. }
  { unfold raZ. rewrite Q1d, unsigned_lit_small by lia. lia. }
  { rewrite (KR3 3%bv ltac:(dcB_in)). exact R3. }
  { rewrite (KR3 4%bv ltac:(dcB_in)). exact R4. }
  { rewrite (KR3 8%bv ltac:(dcB_in)). exact R8. }
  { unfold DRAIN_STK_x, DRAIN_STK, DRAIN_FRAME, SL_STK, SL_FRAME, ASTACK. lia. }
  { unfold DRAIN_STK_x, DRAIN_STK, DRAIN_FRAME, SL_STK, SL_FRAME, ASTACK, LLVMF_STK. lia. }
  (* ---- drain(r), composed into the function's journal ---- *)
  eapply SRr_mono.
  { apply (dr_callZ G_fr W (ms_regs ms) mem (Z_to_bv 64 (BASE + 3568)) LLVMF_STK (spZ (c_regs cx)) (lf_FP fr_FP cx)
      (c_ly cx) (c_S cx) Hpe (c_W cx) (c_mem cx) (c_md cx) [(1, fpos)] ly S Hp mdD k DRAIN_STK_x
      (dr_fp (lm_G m + AENT * Z.of_nat j) (nth j (lm_es m) dr_e0) h (lm_cap m) (lm_out m)) 0 []
      (lf_F cx - spZ (c_regs cx)) (Z_to_bv 64 (BASE + 10096)) ch
      (fun ly2 S2 Hp2 W2 regs2 mem2 md2 => dcB_post (ms_regs ms) ly S Hp W mem mdD (lm_G m + AENT * Z.of_nat j)
         (rg_s fr_RG + ASRC * Z.of_nat si) (nth j (lm_es m) dr_e0) h (dc_ctl (lm_c m) ev0) (lm_O m) (lm_mx m)
         (Z.of_nat (length (lm_O m))) (lm_cap m) (lm_out m) ly2 S2 Hp2 W2 regs2 mem2 md2)
      HG HJ).
    - rewrite HspD. lia.
    - lia.
    - unfold DRAIN_STK_x, DRAIN_STK, DRAIN_FRAME, SL_STK, SL_FRAME, ASTACK, LLVMF_STK. lia.
    - lia.
    - lia.
    - intros a Ha. exfalso. exact (inFP_nil a Ha).
    - exact Q1d.
    - exact HPRED.
    - eapply SRr_mono.
      { exact (DRAIN W ly S Hp (ms_regs ms) mem mdD ch (lm_G m) (lm_G m + AENT * Z.of_nat j)
                 (nth j (lm_es m) dr_e0) si h (dc_ctl (lm_c m) ev0) (lm_O m) (lm_mx m)
                 (Z.of_nat (length (lm_O m))) (lm_cap m) (lm_out m) HPRED Q10d HGin (proj1 HSA) (proj2 HSA) HSA8
                 HEB HEW HEOK Hsi4 HSRC0 HOTH (eq_sym Hfdj) HSK HSKU HOUT HRV (ex_intro _ _ HPERM0)
                 L1 L2 L3 L4 L5 L6 0%nat HRMd HCNTd). }
      cbv beta. intros W2 c2 _ HPOST.
      destruct (dcB_post_of _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HPOST)
        as (ly2 & S2 & Hp2 & regs2 & mem2 & md2 & k2 & Hc2 & HJ2 & HPR2 & HK2).
      exists ly2, S2, Hp2, regs2, mem2, md2, k2. rewrite Q1d in Hc2.
      split; [exact Hc2|]. split; [exact HJ2|]. split; [exact HPR2 | exact HK2].
    - intros a (r & Hr & Ha). destruct Hr as [<- | Hr].
      + cbn [fst snd] in Ha.
        apply (dcB_fp_blk cx m ly S (lm_G m, ATABLE) a HSEPc);
          [unfold model_blks; left; reflexivity | cbn [snd]; unfold ATABLE; lia
          | cbn [fst snd]; replace (req_size ATABLE) with ATABLE by reflexivity; unfold AENT, ATABLE in *; lia].
      + unfold ablocks_fp in Hr. apply in_map_iff in Hr as (b & <- & Hb). cbn [fst snd] in Ha.
        exact (dcB_fp_blk cx m ly S b a HSEPc (HXM b Hb) (HXP b Hb) Ha). }
  cbv beta. intros W2 c2 _ (ly2 & S2 & Hp2 & regs2 & mem2 & md2 & k1 & -> & HJ2 & _ & HPR & HK).
  destruct HK as (k2 & e' & h' & out' & ev' & LB & rest & HK). cbv zeta in HK.
  destruct HK as (HJD & HPK & HMO & HNP2 & HP1 & HP2 & HN1 & HN2 & HN3 & HKE & D9 & D10 & D11 & D12 & D13 & D14 & D15 & D16
                  & D17 & D18 & D19 & HSRC & HGS & D22 & D23 & D24 & D25 & D26 & D27 & D28 & D29 & D30 & D31 & D32 & D33
                  & D34 & D35 & D36 & D37 & D38 & HOUT2).
  rewrite HspD in HJD.
  rewrite dcB_cost_ctl in HMO. rewrite dcB_fin_ctl in D12, D13, D14, D15, D16, D22.
  rewrite ?dcB_live_ctl, ?dcB_fin_ctl, ?dcB_dctl_ctl in HOUT2. rewrite ?dcB_live_ctl, ?dcB_fin_ctl in HP2.
  (* ---- the room round: dr_post's functional half, its clauses for the step rules, check_no_loss's count ---- *)
  assert (HDF : dr_dfun m si h j e' h' LB).
  { unfold dr_dfun. cbv zeta.
    split; [exact D9|]. split; [exact D10|]. split; [exact D11|]. split; [exact D12|]. split; [exact D13|].
    split; [exact D14|]. split; [exact D15|]. split; [exact D16|]. split; [exact D18|]. split; [exact D19|].
    split; [exact D24|]. split; [exact D25|]. split; [exact D26|]. split; [exact D27|]. split; [exact D28|].
    split; [exact D32|]. split; [exact D33|]. split; [exact D35|]. split; [exact D36|]. split; [exact D37|].
    split; [exact D38|]. split; [exact D22|].
    pose proof HN3 as (_ & _ & Hpd1 & Hpd2 & _). split; [exact Hpd1 | exact Hpd2]. }
  assert (EPOST : dr3_epost (nth j (lm_es m) dr_e0) e' h).
  { pose proof HN3 as (_ & _ & _ & _ & _ & Hc' & _). exact (conj Hc' (conj D17 (conj D18 D19))). }
  (* aentry_ok e''s held-array clause (W_rep.v:131-132), for DR_CNT_grow *)
  assert (EKH' : (re_hp e' = 0 /\ re_keys e' = []) \/ (re_hp e' <> 0 /\ 8 <= re_kh e')).
  { pose proof HN3 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hkh' & _).
    destruct Hkh' as [(Hz' & Hk') | (Hz' & _ & _ & H8' & _)]; [left; split; assumption | right; split; assumption]. }
  assert (HPOST3 : dr3_hpost h h') by exact (conj D27 (conj D30 D23)).
  assert (DPOST : ls3_dpost m j h e' h').
  { pose proof HSRC as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HEX2 & _).
    pose proof HEX2 as (_ & _ & _ & _ & (HnX2 & _) & _).
    exact (conj D13 (conj D16 (conj D28 (conj D33 (conj D35 HnX2))))). }
  assert (HGR : forall P, (ReplyCnt.acnt P (ablocks B ly2 S2) <= ReplyCnt.acnt P (ablocks B ly S) +
      Z.to_nat (ReplyCnt.tr_peakP P (dr_tr (lm_c m) (lm_mx m) (Z.of_nat (length (lm_O m))) (lm_cap m)
                                      (nth j (lm_es m) dr_e0) h)))%nat).
  { intros P.
    pose proof (DR_CNT_grow cx t m si h j e' h' LB out' P HRI Hatop Hpick Hj Hfdj Hef0 (proj1 (proj2 HEOK)) HMSZ Ht HU
      HXP EPRE EKH HPRE3 HHN3 CAP0 HDF EPOST EKH' HPOST3 DPOST) as Hgr.
    unfold dr_cap1 in Hgr.
    rewrite (ReplyCnt.acnt_perm P _ _ HP1), (ReplyCnt.acnt_perm P _ _ HP2), !ReplyCnt.acnt_app.
    rewrite !ReplyCnt.acnt_app in Hgr. lia. }
  assert (HCNTc : cnt_ok_pk RP (cnl_pk (hs_expected h') (hs_held h')) (ablocks B ly2 S2)).
  { refine (cnt_ok_pk_mono RP _ _ (ablocks B ly S) (ablocks B ly2 S2) _ HCNT).
    intros P. specialize (HGR P). pose proof (DR_CNT_cnl h h' P Hexp0 D33 D35) as EC.
    unfold cnl_pk. cbv beta. lia. }
  (* ---- the blocks across the call ---- *)
  pose proof dcB_GDR_ok as HGDR.
  pose proof (dj_nodup ly S Hp W mem md HAR) as HNDS.
  assert (HAR2 : ARx ly2 S2 Hp2 W2 mem2 md2) by (eapply ajournal_gx_AR_x; exact HJD).
  pose proof (dj_nodup ly2 S2 Hp2 W2 mem2 md2 HAR2) as HNDS2.
  assert (HP1' : Permutation (ablocks B ly S)
      ((aentry_blks (nth j (lm_es m) dr_e0) ++ asrc_blks h ++ aout_blks (lm_cap m) (lm_out m)) ++ rest))
    by (rewrite <- !app_assoc; exact HP1).
  assert (HRT : Permutation rest ((lm_G m, ATABLE) :: dcB_T cx m j si rest0))
    by exact (dcB_perm_rest _ _ _ _ _ _ _ HPERM0 HP1).
  assert (KTR : forall b, In b (dcB_T cx m j si rest0) -> In b rest)
    by (intros b Hb; apply (Permutation_in _ (Permutation_sym HRT)); right; exact Hb).
  assert (KTL2 : forall b, In b rest -> In b (ablocks B ly2 S2)).
  { intros b Hb. apply (Permutation_in _ (Permutation_sym HP2)).
    apply in_or_app; right; apply in_or_app; right; apply in_or_app; right; exact Hb. }
  assert (HGr : In (lm_G m, ATABLE) rest) by (apply (Permutation_in _ (Permutation_sym HRT)); left; reflexivity).
  assert (HCSin : forall i hi b, (i < 4)%nat -> i <> si -> nth i (lm_hs m) None = Some hi -> In b (asrc_blks hi) ->
      In b (dcB_T cx m j si rest0)).
  { intros i hi b Hi Hne Ehi Hb. unfold dcB_T. apply in_or_app. right. apply in_or_app. left. unfold dcB_CS.
    apply in_concat. exists (slot_blks (Some hi)). split; [|exact Hb]. apply in_map. rewrite <- Ehi.
    apply dcB_in_rm_nth; lia. }
  assert (HCAin : forall y b, In y (firstn j (lm_es m) ++ skipn (Datatypes.S j) (lm_es m)) -> In b (aentry_blks y) ->
      In b (dcB_T cx m j si rest0)).
  { intros y b Hy Hb. unfold dcB_T. apply in_or_app. left. unfold dcB_CA.
    apply in_concat. exists (aentry_blks y). split; [apply in_map; exact Hy | exact Hb]. }
  (* ---- the bytes drain keeps ---- *)
  assert (KBLK : forall p n a, In (p, n) (ablocks B ly S) -> In (p, n) (ablocks B ly2 S2) -> p <= a < p + req_size n ->
      ~ inFP (dr_fp (lm_G m + AENT * Z.of_nat j) (nth j (lm_es m) dr_e0) h (lm_cap m) (lm_out m)) a ->
      abyte_kept W mem W2 mem2 a).
  { intros p n a H1 H2 Ha Hnf.
    pose proof (blk_img_x segs B ARx LAWS ly S Hp W mem md p n a HAR H1 Ha) as Hni.
    destruct (dr_blk B ARx LAWS BLKR ly S Hp W mem md p n HAR H1) as (Hp1o & Hp2o & _).
    apply dj_bk; [lia | intros Hi; exfalso; exact (Hni Hi) |].
    eapply dj_keep; [exact HGDR | exact HJD | lia | intros HGa; exact (Hni (proj1 (HGDR a HGa))) |].
    right; right; left. exists p, n. split; [exact H1|]. split; [exact H2|]. split; [exact Ha | exact Hnf]. }
  assert (KT : forall b a, In b (dcB_T cx m j si rest0) -> fst b <= a < fst b + snd b -> abyte_kept W mem W2 mem2 a).
  { intros [p n] a HbT Ha. cbn [fst snd] in Ha.
    destruct (dcB_in_rest _ _ _ _ HNDS HP1' (KTR _ HbT)) as (HnX & HbL).
    pose proof (dcB_T_ne _ _ _ _ _ _ HNDS HP1' HRT HbT) as Hng.
    destruct (dr_blk B ARx LAWS BLKR ly S Hp W mem md p n HAR HbL) as (_ & _ & Hn0).
    apply (KBLK p n a HbL (KTL2 _ (KTR _ HbT)) ltac:(lia)).
    exact (dcB_nfp_blk ly S Hp W mem md (lm_G m) (lm_G m + AENT * Z.of_nat j) _ p n a HAR HGin (proj1 HSA) (proj2 HSA)
             HXL HbL HnX ltac:(lia) (or_introl Hng)). }
  assert (KTAB : forall a, lm_G m <= a < lm_G m + ATABLE ->
      ~ (lm_G m + AENT * Z.of_nat j <= a < lm_G m + AENT * Z.of_nat j + AENT) -> abyte_kept W mem W2 mem2 a).
  { intros a Ha Hn.
    destruct (dcB_in_rest _ _ _ _ HNDS HP1' HGr) as (HnX & HbL).
    apply (KBLK (lm_G m) ATABLE a HbL (KTL2 _ HGr) ltac:(replace (req_size ATABLE) with ATABLE by reflexivity; lia)).
    exact (dcB_nfp_blk ly S Hp W mem md (lm_G m) (lm_G m + AENT * Z.of_nat j) _ (lm_G m) ATABLE a HAR HGin (proj1 HSA)
             (proj2 HSA) HXL HbL HnX ltac:(replace (req_size ATABLE) with ATABLE by reflexivity; lia) (or_intror Hn)). }
  assert (KSTK : forall a, lf_F cx <= a < spZ (c_regs cx) -> abyte_kept W mem W2 mem2 a).
  { intros a Ha.
    assert (Hni : ~ in_img segs a) by (intros Hi; pose proof (Hsegs a Hi); lia).
    apply dj_bk; [lia | intros Hi; exfalso; exact (Hni Hi) |].
    eapply dj_keep; [exact HGDR | exact HJD | lia | intros HGa; exact (Hni (proj1 (HGDR a HGa))) |].
    left. split; [lia | lia]. }
  assert (FFb : 4096 <= FF /\ FF + 128 <= alloc_ceiling).
  { destruct (frames_bounds_x segs B ARx LAWS ly S Hp W mem md 1 fpos HAR Hfin) as (Hf0 & Hfc & _).
    rewrite HFFe in Hf0, Hfc. replace (fs_frame_bytes 1) with 128 in Hfc by reflexivity. lia. }
  assert (KFF : forall a, FF <= a < FF + 128 -> abyte_kept W mem W2 mem2 a).
  { intros a Ha.
    assert (Hfr : frame_addr ly 1 fpos <= a < frame_addr ly 1 fpos + fs_frame_bytes 1)
      by (rewrite HFFe; replace (fs_frame_bytes 1) with 128 by reflexivity; exact Ha).
    pose proof (frm_img_x segs B ARx LAWS ly S Hp W mem md 1 fpos a HAR Hfin Hfr) as Hni.
    apply dj_bk; [lia | intros Hi; exfalso; exact (Hni Hi) |].
    eapply dj_keep; [exact HGDR | exact HJD | lia | intros HGa; exact (Hni (proj1 (HGDR a HGa))) |].
    right; right; right; right. exists 1, fpos. split; [exact Hfin|].
    split; [left; unfold in_zr, frame_rng; cbn [fst snd]; exact Hfr|].
    exact (dcB_nfp_frm ly S Hp W mem md (lm_G m) (lm_G m + AENT * Z.of_nat j) _ 1 fpos a HAR HGin (proj1 HSA) (proj2 HSA)
             HXL Hfin (or_introl Hfr)). }
  assert (KSH : forall a, SB + FF / 8 <= a < SB + FF / 8 + 16 -> abyte_kept W mem W2 mem2 a).
  { intros a Ha.
    assert (FF8 : 0 <= FF / 8 /\ 8 * (FF / 8) <= FF) by (split; [apply Z.div_pos; lia | apply Z.mul_div_le; lia]).
    unfold SB in Ha.
    assert (Hni : ~ in_img segs a) by (intros Hi; pose proof (Hsegs a Hi); lia).
    apply dj_bk; [lia | intros Hi; exfalso; exact (Hni Hi) |].
    eapply dj_keep; [exact HGDR | exact HJD | lia | intros HGa; exact (Hni (proj1 (HGDR a HGa))) |].
    right; right; right; right. exists 1, fpos. split; [exact Hfin|].
    assert (Hsh : shadow_addr (frame_addr ly 1 fpos) <= a < shadow_addr (frame_addr ly 1 fpos) + fs_frame_bytes 1 / 8).
    { rewrite HFFe. replace (fs_frame_bytes 1 / 8) with 16 by reflexivity. unfold shadow_addr, SHADOW_OFF. lia. }
    split; [right; unfold in_zr; cbn [fst snd]; exact Hsh|].
    exact (dcB_nfp_frm ly S Hp W mem md (lm_G m) (lm_G m + AENT * Z.of_nat j) _ 1 fpos a HAR HGin (proj1 HSA) (proj2 HSA)
             HXL Hfin (or_intror Hsh)). }
  assert (HFPpos : Forall (fun r => 0 < fst r)
      (dr_fp (lm_G m + AENT * Z.of_nat j) (nth j (lm_es m) dr_e0) h (lm_cap m) (lm_out m))).
  { unfold dr_fp. constructor; [cbn [fst]; lia|]. apply Forall_forall. intros r Hr. unfold ablocks_fp in Hr.
    apply in_map_iff in Hr as ([p n] & <- & Hb). cbn [fst].
    destruct (dr_blk B ARx LAWS BLKR ly S Hp W mem md p n HAR (HXL _ Hb)) as (Hpo & _).
    lia. }
  assert (KIMG : forall a, inG DR_GK a \/ rg_lock fr_RG <= a < rg_lock fr_RG + 12 -> abyte_kept W mem W2 mem2 a).
  { intros a Ha. destruct (dcB_GK_out a Ha) as (HnD & Hne).
    assert (HGa : inG G_fr a) by (destruct Ha as [Ha | Ha]; [exact (HG_GK a Ha) | exact (HGlock a Ha)]).
    destruct (HG a HGa) as (Hi & Hno & _). pose proof (Hsegs a Hi) as Hlo.
    apply dj_bk; [lia | intros _; exact HGa |].
    eapply dj_keep; [exact HGDR | exact HJD | lia | exact HnD |].
    right; right; right; left. split; [exact Hi|]. split; [exact Hno|]. split; [exact Hne|].
    apply fp_spares_closed. apply sink_closed_pos. exact HFPpos. }
  (* ---- the context after the call ---- *)
  assert (HFF2 : frame_addr ly2 1 fpos = FF).
  { pose proof HJD as (_ & _ & (memS & HJi & _) & _). pose proof HJi as (_ & Hly & _).
    pose proof Hly as (_ & _ & _ & _ & _ & EF & _). unfold frame_addr. rewrite EF. exact HFFe. }
  assert (HFR2 : aframe_at cx true FF W2 mem2) by (apply (dcB_aframe_kept cx true FF W W2 mem mem2 HFR KSTK KFF KSH); lia).
  assert (HFL2 : sv8 W2 mem2 (FF + 120) (flag_addr ly2 1 fpos)).
  { pose proof HJD as (_ & _ & (memS & HJi & _) & _). pose proof HJi as (_ & Hly & _).
    pose proof Hly as (_ & _ & _ & _ & _ & EF & _). unfold flag_addr. rewrite EF.
    apply (dr_sv8_kept W W2 mem mem2); [intros x Hx; apply KFF; lia | exact HFL]. }
  assert (HIN2 : ainput_at B cx ly2 S2 W2 mem2).
  { destruct HIN as (Hn & Hpl).
    assert (HbT : 0 < c_n cx -> In (c_p cx, c_n cx) (dcB_T cx m j si rest0)).
    { intros Hn1. unfold dcB_T. apply in_or_app. right. apply in_or_app. right. apply in_or_app. left.
      unfold input_blks. rewrite (proj2 (Z.eqb_neq (c_n cx) 0) ltac:(lia)). left. reflexivity. }
    split.
    - destruct Hn as [Hn | (Hn1 & Hin)]; [left; exact Hn | right; split; [exact Hn1|]].
      exact (KTL2 _ (KTR _ (HbT (proj1 Hn1)))).
    - apply (akept_garr8 W mem); [|exact Hpl]. intros x Hx. rewrite length_map, <- Hnlen in Hx.
      destruct Hn as [(Hn0 & _) | (Hn1 & _)]; [lia|].
      exact (KT (c_p cx, c_n cx) x (HbT (proj1 Hn1)) ltac:(cbn [fst snd]; lia)). }
  assert (HRV2 : rom_view segs W2 mem2)
    by exact (ajournal_gx_rom_view_x segs B PST ARx LAWS pa_segs_low _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJD dcB_rom_out dr_pstr HRV).
  pose proof (dcB_jt W W2 mem mem2 HRV HRV2 HJT) as HJT2.
  assert (SVN2 : sv8 W2 mem2 (lf_F cx + DR_N) (c_n cx - dr_k' cx m)).
  { apply (dr_sv8_kept W W2 mem mem2); [|exact SVN]. intros x Hx. apply KSTK. unfold DR_N in Hx. lia. }
  assert (S1922 : sv8 W2 mem2 (lf_F cx + DR_AT) 0).
  { apply (dr_sv8_kept W W2 mem mem2); [|exact S192]. intros x Hx. apply KSTK. unfold DR_AT in Hx. lia. }
  assert (S402 : sv8 W2 mem2 (lf_F cx + 40) (rg_lock fr_RG)).
  { apply (dr_sv8_kept W W2 mem mem2); [|exact S40]. intros x Hx. apply KSTK. lia. }
  (* ---- the model after the call ---- *)
  assert (HLEN1 : Z.of_nat (length (dr_O1 m h LB)) =
      (if dr_live (lm_c m) h then Z.of_nat (length (lm_O m)) + dr_tot h else Z.of_nat (length (lm_O m)))).
  { unfold dr_O1. destruct (dr_live (lm_c m) h); [|reflexivity].
    rewrite length_app, Nat2Z.inj_add, (dc_LB_len LB _ D38). reflexivity. }
  assert (HO1 : aout_at B fr_RG ly2 S2 W2 mem2 (dc_ctl (dr_ctl (lm_c m) h ev') ev') (dr_O1 m h LB) (lm_mx m)
                  (Z.of_nat (length (dr_O1 m h LB))) (dr_cap1 m j h) out').
  { rewrite HLEN1. unfold dr_O1, dr_cap1. exact HOUT2. }
  assert (HREL2 : arelay_at B fr_RG ly2 S2 W2 mem2 (lm_G m) (set_nth j e' (lm_es m))).
  { pose proof HN3 as (_ & _ & Hq1 & Hq2 & _).
    split; [apply (akept_vm W mem); [intros x Hx; apply KIMG; dcB_gk Hx | exact RL1]|].
    split; [apply (akept_awr W mem); [intros x Hx; apply KIMG; dcB_gk Hx | exact RL2]|].
    split; [rewrite set_nth_length; apply (akept_vm W mem); [intros x Hx; apply KIMG; dcB_gk Hx | exact RL3]|].
    split; [apply (akept_awr W mem); [intros x Hx; apply KIMG; dcB_gk Hx | exact RL4]|].
    split; [apply (akept_vm W mem); [intros x Hx; apply KIMG; dcB_gk Hx | exact RL5]|].
    split; [apply (akept_awr W mem); [intros x Hx; apply KIMG; dcB_gk Hx | exact RL6]|].
    split; [rewrite set_nth_length; exact RL7|].
    split; [exact (KTL2 _ HGr)|].
    split.
    { exists tl. apply (dr_tbl_upd W W2 mem mem2 (lm_G m) (lm_es m) tl j e' HTAB HPAD Hq1 Hq2 Hj HN1).
      intros a Ha Hn. exact (proj1 (KTAB a Ha Hn)). }
    split.
    { apply Forall_forall. intros y Hy.
      destruct (dr_in_set_nth rentry j e' y (lm_es m) Hy) as [-> | Hy']; [exact HN3|].
      assert (HyE : In y (lm_es m)) by exact (dr_in_rm rentry j y (lm_es m) Hy').
      rewrite Forall_forall in HENT, HKY.
      apply (aentry_ok_kept B ly S W mem ly2 S2 W2 mem2 y (HENT y HyE)).
      - intros r Hr x Hx.
        destruct (dj_aentry_fp ly S W mem y (HENT y HyE) (HKY y HyE) r Hr x Hx) as [[] | (b & Hb & Hbx)].
        exact (KT b x (HCAin y b Hy' Hb) Hbx).
      - intros b Hb. exact (KTL2 b (KTR b (HCAin y b Hy' Hb))). }
    rewrite dr_map_set_nth, D9.
    assert (Hfe : re_fd (nth j (lm_es m) dr_e0) = nth j (map re_fd (lm_es m)) (re_fd dr_e0))
      by (rewrite map_nth; reflexivity).
    split; [rewrite Hfe, dcB_set_nth_nth; exact HNDF|].
    (* arelay_at's twelfth conjunct: no entry block is the table.  The new entry's blocks are drain's post's first
       part of the live blocks, the table is in its `rest` (HGr), and the live blocks are distinct *)
    apply Forall_forall. intros y Hy b Hb Heq. subst b.
    destruct (dr_in_set_nth rentry j e' y (lm_es m) Hy) as [-> | Hy'].
    - apply (dcB_nd_app (aentry_blks e') _ (lm_G m, ATABLE) (Permutation_NoDup HP2 HNDS2) Hb).
      apply in_or_app. right. apply in_or_app. right. exact HGr.
    - rewrite Forall_forall in HTBN. exact (HTBN y (dr_in_rm rentry j y (lm_es m) Hy') _ Hb eq_refl). }
  assert (HNE2 : amodel_ne ly2 S2 W2 mem2 (dr_m1 m j si h h' e' ev' LB out') true).
  { unfold dr_m1, dr_step, amodel_ne. cbn [lm_hs lm_G lm_es lm_c lm_O lm_mx lm_cap lm_out lm_gn lm_nfd].
    split; [rewrite set_nth_length; exact Hlen4|].
    split.
    { intros i Hi. destruct (Nat.eq_dec i si) as [-> | Hne].
      - rewrite set_nth_same by lia. exact HSRC.
      - rewrite set_nth_other by lia.
        pose proof (HSL i Hi) as Hs. revert Hs.
        destruct (nth i (lm_hs m) None) as [hi|] eqn:Ehi; intros Hs; cbn [aslot] in Hs |- *.
        + apply (asrc_at_kept B ly S W mem ly2 S2 W2 mem2 _ hi Hs).
          * intros r Hr x Hx. destruct (dj_asrc_fp ly S W mem _ hi Hs r Hr x Hx) as [Hin | (b & Hb & Hbx)].
            -- cbv beta in Hin. apply HGS; unfold ASRC in *; lia.
            -- exact (KT b x (HCSin i hi b Hi Hne Ehi Hb) Hbx).
          * intros b Hb. exact (KTL2 b (KTR b (HCSin i hi b Hi Hne Ehi Hb))).
        + destruct Hs as (Hz & Hw). split.
          * apply (akept_garr8 W mem); [|exact Hz]. intros x Hx. rewrite repeat_length in Hx.
            rewrite Z2Nat.id in Hx by (unfold ASRC; lia). apply HGS; unfold ASRC in *; lia.
          * apply (akept_awr W mem); [|exact Hw]. intros x Hx. apply HGS; unfold ASRC in *; lia. }
    split; [exact HREL2|].
    split; [exists ev'; exact HO1|].
    split; [apply (agone_at_kept fr_RG W mem W2 mem2 (lm_gn m) HGONE); intros r [<- | []] x Hx;
            cbn [fst snd] in Hx; apply KIMG; dcB_gk Hx|].
    split; [apply (alock_at_kept fr_RG W mem W2 mem2 true HLOCK); intros r [<- | []] x Hx;
            cbn [fst snd] in Hx; apply KIMG; right; exact Hx|].
    split; [apply (awake_at_kept fr_RG W mem W2 mem2 HWAKE); intros r [<- | []] x Hx;
            cbn [fst snd] in Hx; apply KIMG; dcB_gk Hx|].
    split; [apply (akept_vm W mem); [intros x Hx; apply KIMG; dcB_gk Hx | exact HNFD]|].
    split; [apply (akept_awr W mem); [intros x Hx; apply KIMG; dcB_gk Hx | exact HNFDW]|].
    split; [exact HNFDr|].
    split; [apply (akept_vm W mem); [intros x Hx; apply KIMG; dcB_gk Hx | exact HTUP]|].
    split; [destruct HLST as (lst & Hl); exists lst; apply (akept_vm W mem); [intros x Hx; apply KIMG; dcB_gk Hx | exact Hl]|].
    apply (akept_awr W mem); [intros x Hx; apply KIMG; dcB_gk Hx | exact HLSTW]. }
  assert (HPm1 : Permutation (ablocks B ly2 S2)
      (input_blks cx ++ model_blks (dr_m1 m j si h h' e' ev' LB out') ++ rest0)).
  { unfold dr_m1, dr_step, model_blks. cbn [lm_G lm_es lm_hs lm_cap lm_out]. unfold dr_cap1.
    apply (dcB_perm_post _ _ _ _ _ _ _ _ (dcB_CA (lm_es m) j) (dcB_CS (lm_hs m) si) rest _ HP2 HRT).
    - exact (dr_concat_set_nth_perm _ _ aentry_blks (lm_es m) j e' Hj).
    - pose proof (dr_concat_set_nth_perm _ _ slot_blks (lm_hs m) si (Some h') ltac:(lia)) as Hq.
      cbn [slot_blks] in Hq. exact Hq. }
  assert (HSEP1 : ablocks_sep B fr_FP cx (dr_m1 m j si h h' e' ev' LB out') ly2 S2).
  { split; [exists rest0; exact HPm1|].
    intros b Hb.
    assert (HbL2 : In b (ablocks B ly2 S2)).
    { apply (Permutation_in _ (Permutation_sym HPm1)). apply in_or_app. right. apply in_or_app. left. exact Hb. }
    destruct (in_dec dcB_dec b (ablocks B ly S)) as [HbS | HbS].
    - apply HSEP2.
      apply (Permutation_in _ HP1') in HbS. apply in_app_or in HbS as [HbX | HbR]; [exact (HXM b HbX)|].
      apply (Permutation_in _ HRT) in HbR. destruct HbR as [<- | HbT]; [unfold model_blks; left; reflexivity|].
      unfold dcB_T in HbT. apply in_app_or in HbT as [HbA | HbT].
      + unfold model_blks. right. apply in_or_app. left.
        apply (Permutation_in _ (Permutation_sym HCA)). apply in_or_app. right. exact HbA.
      + apply in_app_or in HbT as [HbC | HbT].
        * unfold model_blks. right. apply in_or_app. right. apply in_or_app. left.
          apply (Permutation_in _ (Permutation_sym HCS)). apply in_or_app. right. exact HbC.
        * exfalso. pose proof (Permutation_NoDup HPm1 HNDS2) as Hnd.
          apply in_app_or in HbT as [HbI | HbR0].
          -- exact (dcB_nd_app _ _ b Hnd HbI (in_or_app _ _ _ (or_introl Hb))).
          -- apply (dcB_nd_app (input_blks cx ++ model_blks (dr_m1 m j si h h' e' ev' LB out')) rest0 b);
               [rewrite <- app_assoc; exact Hnd | apply in_or_app; right; exact Hb | exact HbR0].
    - destruct (in_dec dcB_dec b (ablocks B (c_ly cx) (c_S cx))) as [HbE | HbE]; [right | left; exact HbE].
      intros a Ha. destruct b as [p n]. cbn [fst snd] in Ha.
      destruct (dr_blk B ARx LAWS BLKR ly2 S2 Hp2 W2 mem2 md2 p n HAR2 HbL2) as (_ & _ & Hn0).
      replace a with (p + (a - p)) by lia. apply (HGONE0 p n (a - p) HbE HbS). lia. }
  assert (HKY1 : Forall (fun e0 => Z.of_nat (length (re_keys e0)) <= re_nheld e0)
      (lm_es (dr_m1 m j si h h' e' ev' LB out'))).
  { unfold dr_m1, dr_step. cbn [lm_es]. apply Forall_forall. intros y Hy.
    destruct (dr_in_set_nth rentry j e' y (lm_es m) Hy) as [-> | Hy']; [exact HKE|].
    rewrite Forall_forall in HKY. exact (HKY y (dr_in_rm rentry j y (lm_es m) Hy')). }
  (* ---- the state at 0x84a5c ---- *)
  exists ly2, S2, Hp2, e', h', out', ev', LB.
  split; [|split; [|split]].
  - exists regs2, mem2, md2, (k + k1). split; [reflexivity|].
    split.
    { assert (PR2 : forall r : bv 5, acallee_saved (bv_unsigned r) ->
          In r [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv -> getr regs2 r = getr regs r)
        by (intros r H1 H2; rewrite (dj_pres _ _ r HPR H1); exact (KR3 r H2)).
      unfold dc_regs. rewrite !PR2 by first [dj_cs | dcB_in].
      repeat (split; [assumption|]). exact R25. }
    split; [exact HJ2|]. split; [exact HFF2|].
    split; [exact HFR2|]. split; [exact HFL2|]. split; [exact HIN2|]. split; [exact HRV2|]. split; [exact HJT2|].
    split; [exact SVN2|]. split; [exact S1922|]. split; [exact S402|].
    split; [exact HNE2|]. split; [exact HSEP1 | exact HKY1].
  - exact HMO.
  - exact HDF.
  - exact (conj EPRE (conj EKH (conj HPRE3 (conj HHN3 (conj CAP0 (conj (ex_intro _ rest (conj HP1 HP2))
      (conj EPOST (conj HPOST3 (conj DPOST (conj HNP2 HCNTc)))))))))).
Qed.

(* the frame base F = lf_F cx against the entry sp *)
Lemma dcF_F : forall cx Hpe, lf_base_x B MT XM_LIB RLO RHI fr_live_pre LIBROOM NP G_fr ARx cx Hpe ->
  spZ (c_regs cx) - 352 < lf_F cx <= spZ (c_regs cx) - 320 /\ lf_F cx mod 32 = 0 /\
  (lf_F cx - spZ (c_regs cx)) mod 16 = 0 /\ alloc_ceiling + 32768 <= spZ (c_regs cx) <= 2 ^ 47.
Proof.
  intros cx Hpe HB.
  pose proof HB as (HAI & HPRE).
  pose proof HPRE as (HFNP & _).
  pose proof HFNP as (_ & _ & _ & _ & _ & Hstk & _).
  pose proof Hstk as (Hal16 & _ & Hceil & Hslo & Hshi & H47 & _).
  unfold LLVMF_STK in Hslo.
  assert (HFb : spZ (c_regs cx) - 352 < lf_F cx <= spZ (c_regs cx) - 320).
  { unfold lf_F. pose proof (Z.mod_pos_bound (spZ (c_regs cx) - 320) 32 ltac:(lia)). lia. }
  assert (HF32 : lf_F cx mod 32 = 0).
  { unfold lf_F. rewrite Zminus_mod, Z.mod_mod, Z.sub_diag by lia. reflexivity. }
  set (sp0 := spZ (c_regs cx)) in *.
  set (F := lf_F cx) in *.
  assert (Ho16 : (F - sp0) mod 16 = 0).
  { assert (HF32' : F = sp0 - 320 - (sp0 - 320) mod 32) by reflexivity.
    pose proof (Z.mod_pos_bound (sp0 - 320) 32 ltac:(lia)) as Hmb.
    rewrite HF32'.
    replace (sp0 - 320 - (sp0 - 320) mod 32 - sp0) with (- (320 + (sp0 - 320) mod 32)) by lia.
    assert (H32 : (sp0 - 320) mod 32 = 0 \/ (sp0 - 320) mod 32 = 16).
    { assert (E16 : (sp0 - 320) mod 16 = 0)
        by (replace (sp0 - 320) with (sp0 + (-20) * 16) by lia; rewrite Z.mod_add by lia; exact Hal16).
      pose proof (Z.div_mod ((sp0 - 320) mod 32) 16 ltac:(lia)) as D.
      assert (E2 : ((sp0 - 320) mod 32) mod 16 = 0)
        by (rewrite <- Znumtheory.Zmod_div_mod by (try lia; exists 2; reflexivity); exact E16).
      rewrite E2, Z.add_0_r in D.
      assert (Hq : (sp0 - 320) mod 32 / 16 = 0 \/ (sp0 - 320) mod 32 / 16 = 1) by lia.
      destruct Hq as [Hq | Hq]; rewrite Hq in D; lia. }
    destruct H32 as [H32 | H32]; rewrite H32; reflexivity. }
  repeat split; try lia; exact Ho16.
Qed.
(* the walk's own frame is the one live frame of its journal *)
Lemma dcF_fin : forall cx Hpe fpos ly S Hp (W : world segs) mem md k,
  ajournal_gx_x segs B PST ARx G_fr 0 [] LLVMF_STK (spZ (c_regs cx)) (lf_FP fr_FP cx)
    (c_ly cx) (c_S cx) Hpe (c_W cx) (c_mem cx) (c_md cx) [(1, fpos)] ly S Hp W mem md k ->
  In (1, fpos) (frames S).
Proof.
  intros cx Hpe fpos ly S Hp W mem md k HJ.
  pose proof HJ as (_ & _ & (memS & HJ0 & _) & _). pose proof HJ0 as (_ & _ & _ & _ & _ & Hfrs & _).
  rewrite Hfrs. left. reflexivity.
Qed.
Lemma dcF_regs_kept : forall cx t m j si FF regs regs',
  (forall r, In r dcF_K -> getr regs' r = getr regs r) ->
  dc_regs cx t m j si FF regs -> dc_regs cx t m j si FF regs'.
Proof.
  intros cx t m j si FF regs regs' HK
    (R2 & R8 & R9 & R18 & R19 & R20 & R23 & R24 & R26 & R3 & R4 & R27 & Ht & R21 & R22 & R25).
  unfold dc_regs. rewrite !HK by (cbv; tauto).
  exact (conj R2 (conj R8 (conj R9 (conj R18 (conj R19 (conj R20 (conj R23 (conj R24 (conj R26 (conj R3 (conj R4
    (conj R27 (conj Ht (conj R21 (conj R22 R25))))))))))))))).
Qed.
(* a part of a zero-shadow range is one *)
Lemma dcF_azs_sub : forall a n a' n', azs B a n -> a <= a' -> a' + n' <= a + n -> azs B a' n'.
Proof. intros a n a' n' (r & Hin & H8 & Hlo & Hhi) H1 H2. exists r. split; [exact Hin|]. repeat split; lia. Qed.

Lemma dc_stC : forall cx Hpe t m j si fpos FF ly S Hp mc W c,
  lf_base_x B MT XM_LIB RLO RHI fr_live_pre LIBROOM NP G_fr ARx cx Hpe ->
  dc_at cx Hpe t m j si fpos FF A_dc_r2 ly S Hp mc true 0 W c ->
  SRr segs W c (dc_at cx Hpe t m j si fpos FF A_dc_r3 ly S Hp mc false 0).
Proof.
  intros cx Hpe t m j si fpos FF ly S Hp mc W c HB
    (regs & mem & md & k & -> & HR & HJ & HFF & HFR & HFL & HIN & HROM & HJT & SVN & S192 & S40 & HNE & HSEP & HKB).
  pose proof HR as (R2 & R8 & R9 & R18 & R19 & R20 & R23 & R24 & R26 & R3 & R4 & R27 & Ht & R21 & R22 & R25).
  pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  destruct (dcF_F cx Hpe HB) as (HFb & HF32 & Ho16 & Hsp0).
  assert (HAR : ARx ly S Hp W mem md) by (eapply ajournal_gx_AR_x; exact HJ).
  pose proof (dcF_fin cx Hpe fpos ly S Hp W mem md k HJ) as Hfin.
  assert (HCTX : dc_ctxp cx m FF 0 (flag_addr ly 1 fpos) ly S W mem)
    by exact (conj HFR (conj HFL (conj HIN (conj HROM (conj HJT (conj SVN (conj S192 S40))))))).
  set (sp0 := spZ (c_regs cx)) in *.
  set (F := lf_F cx) in *.
  assert (VLK : rg_lock fr_RG = 0x5d8ac0) by reflexivity.
  pose proof HNE as (_ & _ & _ & _ & _ & HLOCK & _).
  pose proof HLOCK as (LK0 & LK4 & LK8 & LKW). unfold arm in LK0, LK4, LK8.
  assert (HNOWN : forall a, rg_lock fr_RG <= a < rg_lock fr_RG + 12 -> ~ aowned B ly S a).
  { intros a Ha Ho. destruct (HG a (HGlock a Ha)) as (Hi & Hno & _).
    apply Hno. exact (proj1 (alx_owned_image _ _ _ LAWS ly S Hp W mem _ a HAR Hi) Ho). }
  (* 0x84a5c-0x84a60: ld a0,40(s1) ; jal pthread_mutex_unlock *)
  destruct (dc_cell_entry A_dc_r2 40 W regs mem F (rg_lock fr_RG) R9 R26 ltac:(lia) ltac:(lia) HF32
              ltac:(lia) ltac:(lia) ltac:(vm_compute; reflexivity) S40 ltac:(rewrite VLK; lia)) as [HS SHOK].
  remember (Eimg (Ereg regs (dc_cell_extra (rg_lock fr_RG)))) as E eqn:HE.
  assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
  assert (HAE : env_agree 32 (Ereg regs (dc_cell_extra (rg_lock fr_RG))) E)
    by (rewrite HE; split; [intros n Hn; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
  assert (E32 : ew E 32 = Z_to_bv 64 (rg_lock fr_RG))
    by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
  clear HE.
  paj_run_tok_x RUN HS HJ SHOK DRspan.
  { unfold ss_dc_cell. cbn [ss_mem]. apply awr_ok_x_cons; [|apply awr_ok_x_nil].
    intros a Ha. cbn [dc_cell YP09.r_wlo YP09.r_whi] in Ha. lia. }
  dr_meq HF Em.
  pose proof (regs_kept_of_st_ok segs _ _ _ regs _ dcF_K HS HAE ltac:(vm_compute; reflexivity)) as KR.
  cbn [ms_regs restrict] in KR.
  prreg HS (1%bv : bv 5) Q1. prreg HS (10%bv : bv 5) Q10.
  rewrite E32 in Q10.
  pmkst HS. rewrite Em in *. clear HF HFr HG0.
  set (md1 := with_vm_backing (m_vm_lazy md) mat md) in *.
  set (regs1 := ms_regs ms) in *.
  assert (Hsp1 : spZ regs1 = F)
    by (unfold spZ; rewrite (KR 2%bv ltac:(cbv; tauto)), R2; unfold w64; apply unsigned_lit_small; lia).
  assert (Q1' : getr regs1 1 = Z_to_bv 64 (BASE + A_dc_r3)) by exact Q1.
  eapply SRr_bind.
  { eapply (aj_gx_entry_at_x B PST ARx LAWS G_fr 0 [] ESTACK (SIGMA WS_pthread_mutex_unlock)
      (fun a => rg_lock fr_RG + 4 <= a < rg_lock fr_RG + 8)
      (fun regs' mem' => getr regs' 10 = w64 0 /\ val_mem segs (mrestrict (w_H W) mem') (rg_lock fr_RG + 4) 4 0)
      W regs1 mem LLVMF_STK sp0 (lf_FP fr_FP cx) (c_ly cx) (c_S cx) Hpe (c_W cx) (c_mem cx) (c_md cx)
      [(1, fpos)] ly S Hp md1 k (F - sp0) _ HG eq_refl HJ
      ltac:(rewrite Hsp1; lia) Ho16
      ltac:(lia) ltac:(lia) ltac:(unfold ESTACK, LLVMF_STK; lia)
      ltac:(rewrite (KR 3%bv ltac:(cbv; tauto)); exact R3) ltac:(rewrite (KR 4%bv ltac:(cbv; tauto)); exact R4) Q1'
      (ret_ok_codeptr_v A_dc_r3 ltac:(unfold A_dc_r3, A_dr_found, AF_fr_LLVMFuzzerTestOneInput; lia) eq_refl)).
    - intros a. lia.
    - intros a Hwa _. exact (dj_av_ne W mem (rg_lock fr_RG + 4) 4%nat 16 a LK4 ltac:(cbn; lia)).
    - intros a Hwa HnG. exfalso. apply HnG. apply HGlock. lia.
    - intros HPRE2 HSC2.
      exact (AUNLOCK ly S Hp W regs1 mem md1 (rg_lock fr_RG) HPRE2 Q10 ltac:(lia) ltac:(rewrite VLK; reflexivity) ltac:(lia)
        LK0 LK4 LK8
        ltac:(intros a Ha; split;
              [ destruct (Z_lt_le_dec a (rg_lock fr_RG + 4)) as [Hlt | Hge];
                [ exact (dj_av_ne W mem (rg_lock fr_RG) 4%nat 0 a LK0 ltac:(cbn; lia))
                | destruct (Z_lt_le_dec a (rg_lock fr_RG + 8)) as [Hlt2 | Hge2];
                  [ exact (dj_av_ne W mem (rg_lock fr_RG + 4) 4%nat 16 a LK4 ltac:(cbn; lia))
                  | exact (dj_av_ne W mem (rg_lock fr_RG + 8) 4%nat 0 a LK8 ltac:(cbn; lia)) ] ]
              | rewrite Hsp1; unfold ESTACK; lia ])
        ltac:(intros a Ha; split;
              [ replace a with (rg_lock fr_RG + (a - rg_lock fr_RG)) by lia; exact (LKW (a - rg_lock fr_RG) ltac:(lia))
              | split; [ apply HNOWN; lia | rewrite Hsp1; unfold ESTACK; lia ] ])
        (fun a Ha HK => proj2 (proj2 (HG a (HGlock a ltac:(lia)))) (proj1 (proj2 HK)))). }
  (* back at 0x84a64, g_lock free *)
  cbv beta. intros W2 c2 Hwle2 (-> & regs2 & mem2 & md2 & -> & HJa & HPa & (Ha0 & Hlk2) & Hfra & Hpresa).
  assert (KL : forall a, 0 <= a < 2 ^ 64 -> ~ (rg_lock fr_RG + 4 <= a < rg_lock fr_RG + 8) -> ~ (F - ESTACK <= a < F) ->
      aview segs (w_H W) mem2 a = aview segs (w_H W) mem a)
    by (intros a Ha H1 H2; apply Hfra; [exact Ha | exact H1 | replace (sp0 + (F - sp0)) with F by lia; exact H2]).
  pose proof (dj_ne_lockstep ly S Hp W mem md mem2 mc true false F HAR HKB HNE KL ltac:(unfold ESTACK; lia) Hlk2) as HNE2.
  destruct (dj_ctx_lockstep cx Hpe m FF 0 (flag_addr ly 1 fpos) ly S Hp W mem md mem2 HB HAR
              (ex_intro _ fpos (conj Hfin (eq_sym HFF))) HCTX KL Hpresa)
    as (HFR2 & HFL2 & HIN2 & HROM2 & HJT2 & SVN2 & S1922 & S402).
  apply SRr_ret.
  exists regs2, mem2, md2, k.
  split; [reflexivity|].
  split; [exact (dcF_regs_kept cx t m j si FF regs regs2
                   (fun r Hr => eq_trans (dcF_pres_K regs1 regs2 HPa r Hr) (KR r Hr)) HR)|].
  split; [exact HJa|]. split; [exact HFF|].
  split; [exact HFR2|]. split; [exact HFL2|]. split; [exact HIN2|]. split; [exact HROM2|]. split; [exact HJT2|].
  split; [exact SVN2|]. split; [exact S1922|]. split; [exact S402|].
  split; [exact HNE2|]. split; [exact HSEP|]. exact HKB.
Qed.

Lemma dc_stD : forall cx Hpe t m j si fpos FF ly S Hp mc h1 W c,
  lf_base_x B MT XM_LIB RLO RHI fr_live_pre LIBROOM NP G_fr ARx cx Hpe ->
  (si < 4)%nat -> nth si (lm_hs mc) None = Some h1 -> hl_recs (hs_pending h1) = [] ->
  dc_at cx Hpe t m j si fpos FF A_dc_r3 ly S Hp mc false 0 W c ->
  SRr segs W c (dc_at cx Hpe t m j si fpos FF A_dc_r4 ly S Hp mc false 0).
Proof.
  intros cx Hpe t m j si fpos FF ly S Hp mc h1 W c HB Hsi Hh1 Hpend
    (regs & mem & md & k & -> & HR & HJ & HFF & HFR & HFL & HIN & HROM & HJT & SVN & S192 & S40 & HNE & HSEP & HKB).
  pose proof HR as (R2 & R8 & R9 & R18 & R19 & R20 & R23 & R24 & R26 & R3 & R4 & R27 & Ht & R21 & R22 & R25).
  pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  destruct (dcF_F cx Hpe HB) as (HFb & HF32 & Ho16 & Hsp0).
  pose proof (dcF_fin cx Hpe fpos ly S Hp W mem md k HJ) as Hfin.
  assert (HCTX : dc_ctxp cx m FF 0 (flag_addr ly 1 fpos) ly S W mem)
    by exact (conj HFR (conj HFL (conj HIN (conj HROM (conj HJT (conj SVN (conj S192 S40))))))).
  set (sp0 := spZ (c_regs cx)) in *.
  set (F := lf_F cx) in *.
  (* s = &g_s[si]; check_no_loss_read reads its pending.n at s + 24, 0 here *)
  set (HA := rg_s fr_RG + ASRC * Z.of_nat si) in *.
  assert (VS : rg_s fr_RG = 0x5d88e0) by reflexivity.
  pose proof HNE as (_ & HSL & _).
  pose proof (HSL si Hsi) as HSLi. rewrite Hh1 in HSLi.
  destruct HSLi as (_ & _ & _ & _ & _ & _ & _ & _ & _ & HPL & _).
  destruct HPL as (_ & HPn & _).
  assert (HV0 : val_mem segs (mrestrict (w_H W) mem) (HA + 24) 4 0).
  { replace (HA + 24) with (HA + 16 + 8) by lia. unfold hl_n in HPn. rewrite Hpend in HPn. exact HPn. }
  assert (HPm : HA mod 16 = 0).
  { unfold HA. rewrite VS. unfold ASRC.
    replace (0x5d88e0 + 96 * Z.of_nat si) with ((0x5d88e + 6 * Z.of_nat si) * 16) by lia. apply Z_mod_mult. }
  assert (HAZ : azs B HA 28) by (apply (dcF_azs_sub _ _ _ _ HZS); unfold HA, ASRC; lia).
  destruct HAP as (HAP0 & HAP32).
  (* 0x84a64-0x84a68: mv a0,s5 ; jal check_no_loss_read *)
  destruct (dc_plain_entry A_dc_r3 W regs mem R26) as [HS SHOK].
  remember (Eimg (Ereg regs [])) as E eqn:HE.
  assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
  assert (HAE : env_agree 32 (Ereg regs []) E)
    by (rewrite HE; split; [intros n Hn; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
  assert (EEo : forall q (rr : bv 5), Z.of_nat q = bv_unsigned rr -> ew E q = getr regs rr)
    by (intros q rr Hq; subst E; pose proof (bv_unsigned_in_range 5 rr) as Hr5; change (bv_modulus 5) with 32 in Hr5;
        rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_nat; exact Hq).
  clear HE.
  paj_run_to_tok_x RUNTO HS HJ SHOK DRspan AF_fr_check_no_loss_read.
  { apply awr_ok_x_nil. }
  dr_meq HF Em.
  pose proof (regs_kept_of_st_ok_pi _ _ _ regs _ dcF_K HS HAE ltac:(vm_compute; reflexivity)) as KR.
  cbn [ms_regs restrict] in KR.
  prreg HS (1%bv : bv 5) Q1. prreg HS (10%bv : bv 5) Q10.
  rewrite (EEo 21%nat 21%bv eq_refl), R21 in Q10.
  pmkst HS. rewrite Em in *. clear HF HFr HG0.
  set (md1 := with_vm_backing (m_vm_lazy md) mat md) in *.
  set (regs1 := ms_regs ms) in *.
  assert (Hsp1 : spZ regs1 = F)
    by (unfold spZ; rewrite (KR 2%bv ltac:(cbv; tauto)), R2; unfold w64; apply unsigned_lit_small; lia).
  assert (Q1' : getr regs1 1 = Z_to_bv 64 (BASE + A_dc_r4)) by exact Q1.
  destruct (dr_afn_pre_at cx Hpe ly S Hp fpos k W mem md1 regs1 CNLR_STK HB HJ
              ltac:(rewrite HFF; exact (dr_aframe_false cx FF W mem HFR)) Hsp1
              ltac:(rewrite Q1'; exact (ret_ok_codeptr_v A_dc_r4
                      ltac:(unfold A_dc_r4, A_dr_found, AF_fr_LLVMFuzzerTestOneInput; lia) eq_refl))
              ltac:(unfold raZ; rewrite Q1', unsigned_lit_small; unfold A_dc_r4, A_dr_found, AF_fr_LLVMFuzzerTestOneInput; lia)
              ltac:(rewrite (KR 3%bv ltac:(cbv; tauto)); exact R3) ltac:(rewrite (KR 4%bv ltac:(cbv; tauto)); exact R4)
              ltac:(rewrite (KR 8%bv ltac:(cbv; tauto)); exact R8)
              ltac:(unfold CNLR_STK; lia) ltac:(unfold CNLR_STK, LLVMF_STK; lia)) as (ch & HPRE1).
  eapply SRr_mono.
  { eapply (dr_callZ G_fr W regs1 mem (Z_to_bv 64 (BASE + AF_fr_check_no_loss_read)) LLVMF_STK sp0 (lf_FP fr_FP cx)
      (c_ly cx) (c_S cx) Hpe (c_W cx) (c_mem cx) (c_md cx) [(1, fpos)] ly S Hp md1 k CNLR_STK [] 0 [] (F - sp0)
      (Z_to_bv 64 (BASE + A_dc_r4)) ch
      (fun ly2 S2 Hp2 W2 _ mem2 md2 => ly2 = ly /\ S2 = S /\ Hp2 = Hp /\ ajournal_x segs B PST ARx CNLR_STK F [] ly S Hp W mem md1 [] ly S Hp W2 mem2 md2 0)
      HG HJ ltac:(rewrite Hsp1; lia) ltac:(lia) ltac:(unfold CNLR_STK, LLVMF_STK; lia) ltac:(lia) ltac:(lia)
      ltac:(intros a Ha; exfalso; exact (inFP_nil a Ha)) Q1' HPRE1).
    - eapply SRr_mono;
        [exact (CNLR W ly S Hp regs1 mem md1 ch HA 0 HPRE1 Q10 HPm ltac:(unfold HA, ASRC; lia) ltac:(unfold HA, ASRC; lia) HAZ
                  ltac:(unfold HA, ASRC in *; lia) ltac:(unfold HA, ASRC in *; lia) HV0 ltac:(lia) ltac:(left; reflexivity))|].
      cbv beta. intros W2 c2 _ (regs2 & mem2 & md2 & -> & HJc & HP2 & _ & _).
      rewrite Hsp1 in HJc.
      exists ly, S, Hp, regs2, mem2, md2, 0.
      split; [rewrite Q1'; reflexivity|].
      split; [rewrite Hsp1; apply (ajournal_gx_G_mono_x segs B PST ARx [] G_fr);
              [intros a Ha; exfalso; exact (inG_nil a Ha) | apply ajournal_gx_nil_x; exact HJc]|].
      split; [exact HP2|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. exact HJc.
    - intros a Ha. exfalso. exact (inFP_nil a Ha). }
  (* back at 0x84a6c *)
  cbv beta. intros W2 c2 _ (ly2 & S2 & Hp2 & regs2 & mem2 & md2 & k1 & -> & HJ2 & _ & HP2 & (-> & -> & -> & HJp)).
  pose proof (dj_ne_plain ly S Hp W W2 mem mem2 md1 md2 mc false CNLR_STK F HJp ltac:(unfold CNLR_STK; lia) HKB HNE) as HNE2.
  destruct (dj_ctx_plain cx Hpe m FF 0 (flag_addr ly 1 fpos) ly S Hp W W2 mem mem2 md1 md2 CNLR_STK HB HJp
              ltac:(unfold CNLR_STK; lia) (ex_intro _ fpos (conj Hfin (eq_sym HFF))) HCTX)
    as (HFR2 & HFL2 & HIN2 & HROM2 & HJT2 & SVN2 & S1922 & S402).
  exists regs2, mem2, md2, (k + k1).
  split; [reflexivity|].
  split; [exact (dcF_regs_kept cx t m j si FF regs regs2
                   (fun r Hr => eq_trans (dcF_pres_K regs1 regs2 HP2 r Hr) (KR r Hr)) HR)|].
  split; [exact HJ2|]. split; [exact HFF|].
  split; [exact HFR2|]. split; [exact HFL2|]. split; [exact HIN2|]. split; [exact HROM2|]. split; [exact HJT2|].
  split; [exact SVN2|]. split; [exact S1922|]. split; [exact S402|].
  split; [exact HNE2|]. split; [exact HSEP|]. exact HKB.
Qed.

Lemma dc_stF : forall cx Hpe t m j si fpos FF ly S Hp mc W c,
  lf_base_x B MT XM_LIB RLO RHI fr_live_pre LIBROOM NP G_fr ARx cx Hpe ->
  dr_at_op cx m -> NP S ->
  (forall ev, RINV cx (t + 1) (dc_fin cx m mc ev)) -> (forall ev, LSx cx (t + 1) (dc_fin cx m mc ev) ly S) ->
  dc_at cx Hpe t m j si fpos FF A_dc_r5 ly S Hp mc false (Z.of_nat (length (lm_O mc))) W c ->
  SRr segs W c (DST A_dr_join cx Hpe (t + 1) (lregs_join cx t)).
Proof.
  intros cx Hpe t m j si fpos FF ly S Hp mc W c HB Hatop HNP HRI HLS
    (regs & mem & md & k & -> & HR & HJ & HFF & HFR & HFL & HIN & HROM & HJT & SVN & S192 & S40 & HNE & HSEP & HKB).
  pose proof HR as (R2 & R8 & R9 & R18 & R19 & R20 & R23 & R24 & R26 & R3 & R4 & R27 & Ht & R21 & R22 & R25).
  pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  destruct (dcF_F cx Hpe HB) as (HFb & HF32 & Ho16 & Hsp0).
  assert (HAR : ARx ly S Hp W mem md) by (eapply ajournal_gx_AR_x; exact HJ).
  pose proof (dcF_fin cx Hpe fpos ly S Hp W mem md k HJ) as Hfin.
  assert (Hk' : 0 <= dr_k' cx m <= c_n cx)
    by (pose proof Hatop as (Hk0 & _ & _); unfold dr_k'; destruct (Z.ltb_spec (lm_k m + 1) (c_n cx)); lia).
  (* at = |O| = g_nout *)
  pose proof HNE as (_ & _ & _ & (ev0 & HOUT0) & _).
  destruct HOUT0 as (_ & _ & HNO & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
                     _ & Hcap).
  unfold arm in HNO.
  assert (HA : 0 <= Z.of_nat (length (lm_O mc)) < 2 ^ 64).
  { destruct Hcap as [(_ & _ & Hz) | (Hc0 & Hle & Hin & _)]; [lia|].
    destruct (dr_blk B ARx LAWS BLKR ly S Hp W mem md _ _ HAR Hin) as (Hb1 & Hb2 & Hb3). lia. }
  assert (VN : VAL A_g_nout = rg_nout fr_RG) by (vm_compute; reflexivity).
  assert (HCTX : dc_ctxp cx m FF (Z.of_nat (length (lm_O mc))) (flag_addr ly 1 fpos) ly S W mem)
    by exact (conj HFR (conj HFL (conj HIN (conj HROM (conj HJT (conj SVN (conj S192 S40))))))).
  set (sp0 := spZ (c_regs cx)) in *.
  set (F := lf_F cx) in *.
  set (NO := Z.of_nat (length (lm_O mc))) in *.
  (* 0x84a78-0x84a7c: ld a0,192(s1) ; jal check_shape_done *)
  destruct (dc_cell_entry A_dc_r5 192 W regs mem F NO R9 R26 ltac:(lia) ltac:(lia) HF32
              ltac:(lia) ltac:(lia) ltac:(vm_compute; reflexivity) S192 HA) as [HS SHOK].
  remember (Eimg (Ereg regs (dc_cell_extra NO))) as E eqn:HE.
  assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
  assert (HAE : env_agree 32 (Ereg regs (dc_cell_extra NO)) E)
    by (rewrite HE; split; [intros n Hn; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
  assert (E32 : ew E 32 = Z_to_bv 64 NO)
    by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
  clear HE.
  paj_run_to_tok_x RUNTO HS HJ SHOK DRspan AF_fr_check_shape_done.
  { unfold ss_dc_cell. cbn [ss_mem]. apply awr_ok_x_cons; [|apply awr_ok_x_nil].
    intros a Ha. cbn [dc_cell YP09.r_wlo YP09.r_whi] in Ha. lia. }
  dr_meq HF Em.
  pose proof (regs_kept_of_st_ok_pi _ _ _ regs _ dcF_K HS HAE ltac:(vm_compute; reflexivity)) as KR.
  cbn [ms_regs restrict] in KR.
  prreg HS (1%bv : bv 5) Q1. prreg HS (10%bv : bv 5) Q10.
  rewrite E32 in Q10.
  pmkst HS. rewrite Em in *. clear HF HFr HG0.
  set (md1 := with_vm_backing (m_vm_lazy md) mat md) in *.
  set (regs1 := ms_regs ms) in *.
  assert (Hsp1 : spZ regs1 = F)
    by (unfold spZ; rewrite (KR 2%bv ltac:(cbv; tauto)), R2; unfold w64; apply unsigned_lit_small; lia).
  assert (Q1' : getr regs1 1 = Z_to_bv 64 (BASE + A_dr_join)) by exact Q1.
  destruct (dr_afn_pre_at cx Hpe ly S Hp fpos k W mem md1 regs1 CSD_STK HB HJ
              ltac:(rewrite HFF; exact (dr_aframe_false cx FF W mem HFR)) Hsp1
              ltac:(rewrite Q1'; exact (ret_ok_codeptr_v A_dr_join
                      ltac:(unfold A_dr_join, AF_fr_LLVMFuzzerTestOneInput; lia) eq_refl))
              ltac:(unfold raZ; rewrite Q1', unsigned_lit_small; unfold A_dr_join, AF_fr_LLVMFuzzerTestOneInput; lia)
              ltac:(rewrite (KR 3%bv ltac:(cbv; tauto)); exact R3) ltac:(rewrite (KR 4%bv ltac:(cbv; tauto)); exact R4)
              ltac:(rewrite (KR 8%bv ltac:(cbv; tauto)); exact R8)
              ltac:(unfold CSD_STK; lia) ltac:(unfold CSD_STK, LLVMF_STK; lia)) as (ch & HPRE1).
  eapply SRr_mono.
  { eapply (dr_callZ G_fr W regs1 mem (Z_to_bv 64 (BASE + AF_fr_check_shape_done)) LLVMF_STK sp0 (lf_FP fr_FP cx)
      (c_ly cx) (c_S cx) Hpe (c_W cx) (c_mem cx) (c_md cx) [(1, fpos)] ly S Hp md1 k CSD_STK [] 0 [] (F - sp0)
      (Z_to_bv 64 (BASE + A_dr_join)) ch
      (fun ly2 S2 Hp2 W2 _ mem2 md2 => ly2 = ly /\ S2 = S /\ Hp2 = Hp /\ ajournal_x segs B PST ARx CSD_STK F [] ly S Hp W mem md1 [] ly S Hp W2 mem2 md2 0)
      HG HJ ltac:(rewrite Hsp1; lia) ltac:(lia) ltac:(unfold CSD_STK, LLVMF_STK; lia) ltac:(lia) ltac:(lia)
      ltac:(intros a Ha; exfalso; exact (inFP_nil a Ha)) Q1' HPRE1).
    - eapply SRr_mono;
        [exact (CSD W ly S Hp regs1 mem md1 ch NO HPRE1 Q10 HA ltac:(rewrite VN; exact HNO))|].
      cbv beta. intros W2 c2 _ (regs2 & mem2 & md2 & -> & HJc & HP2 & _ & _).
      rewrite Hsp1 in HJc.
      exists ly, S, Hp, regs2, mem2, md2, 0.
      split; [rewrite Q1'; reflexivity|].
      split; [rewrite Hsp1; apply (ajournal_gx_G_mono_x segs B PST ARx [] G_fr);
              [intros a Ha; exfalso; exact (inG_nil a Ha) | apply ajournal_gx_nil_x; exact HJc]|].
      split; [exact HP2|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. exact HJc.
    - intros a Ha. exfalso. exact (inFP_nil a Ha). }
  (* back at 0x84a80, the arm's join *)
  cbv beta. intros W2 c2 _ (ly2 & S2 & Hp2 & regs2 & mem2 & md2 & k1 & -> & HJ2 & _ & HP2 & (-> & -> & -> & HJp)).
  pose proof (dj_ne_plain ly S Hp W W2 mem mem2 md1 md2 mc false CSD_STK F HJp ltac:(unfold CSD_STK; lia) HKB HNE) as HNE2.
  destruct (dj_ctx_plain cx Hpe m FF NO (flag_addr ly 1 fpos) ly S Hp W W2 mem mem2 md1 md2 CSD_STK HB HJp
              ltac:(unfold CSD_STK; lia) (ex_intro _ fpos (conj Hfin (eq_sym HFF))) HCTX)
    as (HFR2 & HFL2 & HIN2 & HROM2 & HJT2 & SVN2 & S1922 & S402).
  destruct HNE2 as (N1 & N2 & N3 & (ev & N4) & N5 & N6 & N7 & N8 & N9 & N10 & N11 & N12 & N13).
  pose proof (dcF_regs_kept cx t m j si FF regs regs2
                (fun r Hr => eq_trans (dcF_pres_K regs1 regs2 HP2 r Hr) (KR r Hr)) HR)
    as (R2' & R8' & R9' & R18' & R19' & R20' & R23' & R24' & R26' & R3' & R4' & R27' & Ht' & R21' & R22' & R25').
  exists regs2, mem2, md2.
  split; [reflexivity|].
  split; [exact HJT2|].
  exists [(1, fpos)], ly, S, Hp, (k + k1), (dc_fin cx m mc ev), fpos.
  split; [exact HJ2|]. split; [reflexivity|]. split; [rewrite HFF; exact HFR2|]. split; [rewrite HFF; exact HFL2|].
  split; [exact (conj N1 (conj N2 (conj N3 (conj N4 (conj N5 (conj N6 (conj N7 (conj N8 (conj N9 (conj N10
                   (conj N11 (conj N12 N13))))))))))))|].
  split; [exact HIN2|]. split; [exact HROM2|].
  split; [exact HSEP|]. split; [exact (HLS ev)|]. split; [exact HNP|]. split; [exact (HRI ev)|].
  rewrite HFF.
  exact (conj R2' (conj R8' (conj R9' (conj R18' (conj R19' (conj R20' (conj R23' (conj R24' (conj R26' (conj R3'
    (conj R4' (conj R27' (conj Ht' (conj R25' (conj SVN2 Hk'))))))))))))))).
Qed.
(* a list's blocks have a positive size *)
Lemma dcE_blks_pos : forall ly S (W : world segs) mem LA l lines,
  alist_at B ly S W mem LA l lines -> forall b, In b (alist_blks l) -> 0 < snd b.
Proof.
  intros ly S W mem LA l lines (_ & _ & _ & _ & H5 & H6 & _) b Hb. unfold alist_blks in Hb.
  apply in_app_or in Hb as [Hb | Hb].
  - destruct (Z.eqb_spec (hl_cap l) 0) as [Ec | Ec]; [destruct Hb|].
    destruct Hb as [<- | []]. cbn [snd]. unfold AREC. unfold hl_n in H5. lia.
  - apply in_map_iff in Hb as (r & <- & _). cbn [snd]. lia.
Qed.
(* what a callee's journal (empty own) keeps, as abyte_kept: dj_keep and dj_bk *)
Lemma dcE_kept : forall Gc XO OUT STK sp FP ly S Hp (W : world segs) mem md ly' S' Hp' (W' : world segs) mem' md' kk a,
  gx_ok segs B Gc ->
  ajournal_gx_x segs B PST ARx Gc XO OUT STK sp FP ly S Hp W mem md [] ly' S' Hp' W' mem' md' kk ->
  0 <= a < 2 ^ 64 -> ~ inG Gc a -> (in_img segs a -> inG G_fr a) ->
  ((alloc_ceiling <= a /\ ~ (sp - STK <= a < sp + XO)) \/
   (sp <= a < sp + XO /\ ~ inFP OUT a) \/
   (exists p n, In (p, n) (ablocks B ly S) /\ In (p, n) (ablocks B ly' S') /\ p <= a < p + req_size n /\
      ~ inFP FP a) \/
   (in_img segs a /\ ~ Exists (in_zr a) (as_owned_static B) /\ ~ (as_errno B <= a < as_errno B + 4) /\
      fp_spares FP a) \/
   (exists cid pos, In (cid, pos) (frames S) /\
      (in_zr a (frame_rng ly (cid, pos)) \/ in_zr a (shadow_addr (frame_addr ly cid pos), fs_frame_bytes cid / 8)) /\
      ~ inFP FP a)) ->
  abyte_kept W mem W' mem' a.
Proof.
  intros Gc XO OUT STK sp FP ly S Hp W mem md ly' S' Hp' W' mem' md' kk a HGx HJX Ha HnG Hig Hc.
  apply (dj_bk W W' mem mem' a Ha Hig).
  exact (dj_keep Gc XO OUT STK sp FP ly S Hp W mem md [] ly' S' Hp' W' mem' md' kk a HGx HJX Ha HnG Hc).
Qed.
(* a footprint of live blocks does not reach the sink's token at 0 *)
Lemma dcE_fp_closed : forall ly S Hp (W : world segs) mem md L,
  ARx ly S Hp W mem md -> (forall b, In b L -> In b (ablocks B ly S)) -> ~ YI16.sink_open_fp (blk_FP L).
Proof.
  intros ly S Hp W mem md L HAR HL (r & Hr & H0). unfold blk_FP in Hr. apply in_map_iff in Hr as ([p n] & <- & Hb).
  destruct (alx_blocks _ _ _ LAWS ly S Hp W mem md p n HAR (HL _ Hb)) as (_ & H4 & _). cbn [fst snd] in H0. lia.
Qed.
(* a byte of another live block is outside the footprint of the blocks L *)
Lemma dcE_notFP : forall ly S Hp (W : world segs) mem md L p n a,
  ARx ly S Hp W mem md -> (forall b, In b L -> In b (ablocks B ly S)) -> In (p, n) (ablocks B ly S) ->
  ~ In (p, n) L -> p <= a < p + req_size n -> ~ inFP (blk_FP L) a.
Proof.
  intros ly S Hp W mem md L p n a HAR HL Hpn Hnot Ha (r & Hr & Hra). unfold blk_FP in Hr.
  apply in_map_iff in Hr as ([q m] & <- & Hb). cbn [fst snd] in Hra.
  apply (dj_apart ly S Hp W mem md p n q m a HAR Hpn (HL _ Hb)); [| exact Ha | exact Hra].
  intros E. apply Hnot. rewrite E. exact Hb.
Qed.
Section dcE_keep.
Variables (Gc : list (Z * Z)) (XO : Z) (OUT : list (Z * Z)) (STK sp : Z) (L : list (Z * Z)).
Variables (ly : alayout) (S : astate) (Hp : list Z) (W : world segs) (mem : word -> option byte) (md : Model).
Variables (ly' : alayout) (S' : astate) (Hp' : list Z) (W' : world segs) (mem' : word -> option byte) (md' : Model) (kk : Z).
Hypothesis KGx : gx_ok segs B Gc.
Hypothesis KJ : ajournal_gx_x segs B PST ARx Gc XO OUT STK sp (blk_FP L) ly S Hp W mem md [] ly' S' Hp' W' mem' md' kk.
Hypothesis KAR : ARx ly S Hp W mem md.
Hypothesis KL : forall b, In b L -> In b (ablocks B ly S).
Lemma dcE_nG_img : forall a, inG Gc a -> in_img segs a.
Proof. intros a Ha. exact (proj1 (KGx a Ha)). Qed.
(* a live block's byte, the block live after and none of L *)
Lemma dcE_kept_blk : forall p n a,
  In (p, n) (ablocks B ly S) -> In (p, n) (ablocks B ly' S') -> ~ In (p, n) L -> p <= a < p + req_size n ->
  abyte_kept W mem W' mem' a.
Proof.
  intros p n a H1 H2 Hnot Ha.
  destruct (alx_blocks _ _ _ LAWS ly S Hp W mem md p n KAR H1) as (_ & H4 & Hc & _).
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  assert (Hni : ~ in_img segs a) by exact (blk_img_x segs B ARx LAWS ly S Hp W mem md p n a KAR H1 Ha).
  apply (dcE_kept Gc XO OUT STK sp (blk_FP L) ly S Hp W mem md ly' S' Hp' W' mem' md' kk a KGx KJ);
    [lia | intros HGa; exact (Hni (dcE_nG_img a HGa)) | intros Hi; exact (False_ind _ (Hni Hi)) |].
  right; right; left. exists p, n. repeat split; try assumption; try lia.
  exact (dcE_notFP ly S Hp W mem md L p n a KAR KL H1 Hnot Ha).
Qed.
(* an image byte of G_fr, outside Gc and errno *)
Lemma dcE_kept_img : forall a, inG G_fr a -> ~ inG Gc a -> ~ (as_errno B <= a < as_errno B + 4) ->
  abyte_kept W mem W' mem' a.
Proof.
  intros a HGa HnG He. destruct (HG a HGa) as (Hi & Hno & _).
  pose proof (pa_segs_low a Hi) as Hlo. pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  apply (dcE_kept Gc XO OUT STK sp (blk_FP L) ly S Hp W mem md ly' S' Hp' W' mem' md' kk a KGx KJ);
    [lia | exact HnG | intros _; exact HGa |].
  right; right; right; left. split; [exact Hi|]. split; [exact Hno|]. split; [exact He|].
  apply fp_spares_closed. exact (dcE_fp_closed ly S Hp W mem md L KAR KL).
Qed.
(* a byte of a fake frame or of its shadow *)
Lemma dcE_kept_frame : forall cid pos a, In (cid, pos) (frames S) ->
  (in_zr a (frame_rng ly (cid, pos)) \/ in_zr a (shadow_addr (frame_addr ly cid pos), fs_frame_bytes cid / 8)) ->
  abyte_kept W mem W' mem' a.
Proof.
  intros cid pos a Hfr Hr.
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  destruct (frames_bounds_x segs B ARx LAWS ly S Hp W mem md cid pos KAR Hfr) as (Hf0 & Hfc & Hfh).
  pose proof (fs_frame_bytes_nonneg cid) as Hfs.
  pose proof (shadow_addr_bounds (frame_addr ly cid pos) ltac:(zlia)) as SB1.
  pose proof (shadow_addr_bounds (frame_addr ly cid pos + fs_frame_bytes cid) ltac:(zlia)) as SB2.
  pose proof (shadow_range_end (frame_addr ly cid pos) (fs_frame_bytes cid) (fs_frame_bytes_nonneg cid)) as SB3.
  assert (Hni : ~ in_img segs a).
  { intros Hi. destruct Hr as [Hr | Hr].
    - exact (frm_img_x segs B ARx LAWS ly S Hp W mem md cid pos a KAR Hfr Hr Hi).
    - pose proof (pa_segs_low a Hi). unfold in_zr in Hr. cbn [fst snd] in Hr. zlia. }
  apply (dcE_kept Gc XO OUT STK sp (blk_FP L) ly S Hp W mem md ly' S' Hp' W' mem' md' kk a KGx KJ);
    [ unfold frame_rng, in_zr in Hr; cbn [fst snd] in Hr; destruct Hr as [Hr | Hr]; zlia
    | intros HGa; exact (Hni (dcE_nG_img a HGa)) | intros Hi; exact (False_ind _ (Hni Hi)) |].
  right; right; right; right. exists cid, pos. split; [exact Hfr|]. split; [exact Hr|].
  intros (r & Hrin & Hra). unfold blk_FP in Hrin. apply in_map_iff in Hrin as ([b m] & <- & Hb). cbn [fst snd] in Hra.
  pose proof (KL _ Hb) as Hbin.
  destruct (alx_blocks _ _ _ LAWS ly S Hp W mem md b m KAR Hbin) as (_ & _ & _ & [Hh1 Hh2] & _).
  pose proof (sep_block_frame_x segs B ARx LAWS ly S Hp W mem md b m cid pos KAR Hbin Hfr) as Hd.
  unfold zdisjoint, frame_rng, in_zr in Hd, Hr. cbn [fst snd] in Hd, Hr.
  destruct Hr as [Hr|Hr]; zlia.
Qed.
End dcE_keep.
(* the controller's stream across a callee that keeps every byte of it but errno, which it re-reads *)
Ltac dcE_infp := repeat (first [left; reflexivity | right]).
Lemma dcE_aout : forall ly S (W : world segs) mem ly' S' (W' : world segs) mem' c O mx no cap out v,
  aout_at B fr_RG ly S W mem c O mx no cap out ->
  akept W mem W' mem' (dcE_ofp cap out) ->
  (forall b, In b (aout_blks cap out) -> In b (ablocks B ly' S')) ->
  val_mem segs (arm W' mem') (as_errno B) 4 v -> awr W' mem' (as_errno B) 4 -> 0 <= v < 2 ^ 32 ->
  aout_at B fr_RG ly' S' W' mem' (dc_ctl c v) O mx no cap out.
Proof.
  intros ly S W mem ly' S' W' mem' c O mx no cap out v
    (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11 & H12 & H13 & H14 & H15 & H16 & H17 & H18 &
     H19 & H20 & H21 & H22 & H23 & H24 & H25 & H26) HK HB Hv Hw Hvr.
  assert (KC : forall a n, In (a, a + n) (dcE_ofp cap out) -> forall x, a <= x < a + n -> abyte_kept W mem W' mem' x)
    by (intros a n Hin x Hx; exact (HK (a, a + n) Hin x Hx)).
  cbn [dc_ctl ct_cl ct_br ct_dd ct_ei ct_ev].
  split; [apply (akept_vm W mem); [intros x Hx; apply (KC (rg_send_max fr_RG) 8); [unfold dcE_ofp; dcE_infp | lia] | exact H1]|].
  split; [apply (akept_awr W mem); [apply (KC (rg_send_max fr_RG) 8); unfold dcE_ofp; dcE_infp | exact H2]|].
  split; [apply (akept_vm W mem); [intros x Hx; apply (KC (rg_nout fr_RG) 8); [unfold dcE_ofp; dcE_infp | lia] | exact H3]|].
  split; [apply (akept_awr W mem); [apply (KC (rg_nout fr_RG) 8); unfold dcE_ofp; dcE_infp | exact H4]|].
  split; [apply (akept_vm W mem); [intros x Hx; apply (KC (rg_capout fr_RG) 8); [unfold dcE_ofp; dcE_infp | lia] | exact H5]|].
  split; [apply (akept_awr W mem); [apply (KC (rg_capout fr_RG) 8); unfold dcE_ofp; dcE_infp | exact H6]|].
  split; [apply (akept_vm W mem); [intros x Hx; apply (KC (rg_out fr_RG) 8); [unfold dcE_ofp; dcE_infp | lia] | exact H7]|].
  split; [apply (akept_awr W mem); [apply (KC (rg_out fr_RG) 8); unfold dcE_ofp; dcE_infp | exact H8]|].
  split; [apply (akept_vm W mem); [intros x Hx; apply (KC (rg_client fr_RG) 4); [unfold dcE_ofp; dcE_infp | lia] | exact H9]|].
  split; [apply (akept_awr W mem); [apply (KC (rg_client fr_RG) 4); unfold dcE_ofp; dcE_infp | exact H10]|].
  split; [apply (akept_vm W mem); [intros x Hx; apply (KC (rg_client_broken fr_RG) 1); [unfold dcE_ofp; dcE_infp | lia] | exact H11]|].
  split; [apply (akept_awr W mem); [apply (KC (rg_client_broken fr_RG) 1); unfold dcE_ofp; dcE_infp | exact H12]|].
  split; [apply (akept_vm W mem); [intros x Hx; apply (KC (rg_send_dead fr_RG) 1); [unfold dcE_ofp; dcE_infp | lia] | exact H13]|].
  split; [apply (akept_awr W mem); [apply (KC (rg_send_dead fr_RG) 1); unfold dcE_ofp; dcE_infp | exact H14]|].
  split; [apply (akept_vm W mem); [intros x Hx; apply (KC (rg_send_eintr fr_RG) 1); [unfold dcE_ofp; dcE_infp | lia] | exact H15]|].
  split; [apply (akept_awr W mem); [apply (KC (rg_send_eintr fr_RG) 1); unfold dcE_ofp; dcE_infp | exact H16]|].
  split; [exact Hv|]. split; [exact Hw|]. split; [exact Hvr|].
  do 6 (split; [assumption|]).
  destruct H26 as [H26 | (Hc & Hno & Hin & junk & Hj & Hg)]; [left; exact H26|right].
  assert (Ec : (cap =? 0) = false) by (apply Z.eqb_neq; lia).
  split; [exact Hc|]. split; [exact Hno|].
  split; [apply HB; unfold aout_blks; rewrite Ec; left; reflexivity|].
  exists junk. split; [exact Hj|].
  apply (akept_garr8 W mem); [|exact Hg].
  intros x Hx. unfold bzs in Hx. rewrite length_map, length_app, Nat2Z.inj_add in Hx.
  apply (KC out cap); [unfold dcE_ofp; rewrite Ec; dcE_infp | lia].
Qed.

(* the registers the arm keeps across the run and the call (all callee-saved) *)
Lemma dcE_regs_kept : forall cx t m j si FF (regs regs1 regs2 : bvmap 5 word),
  (forall r : bv 5, In r [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv -> getr regs1 r = getr regs r) ->
  aregs_preserved regs1 regs2 -> dc_regs cx t m j si FF regs -> dc_regs cx t m j si FF regs2.
Proof.
  intros cx t m j si FF regs regs1 regs2 KR HP
    (R2 & R8 & R9 & R18 & R19 & R20 & R23 & R24 & R26 & R3 & R4 & R27 & Ht & R21 & R22 & R25).
  assert (PR : forall r : bv 5, acallee_saved (bv_unsigned r) ->
      In r [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv -> getr regs2 r = getr regs r)
    by (intros r Hr Hin; rewrite (dj_pres regs1 regs2 r HP Hr); exact (KR r Hin)).
  unfold dc_regs.
  rewrite (PR 2%bv ltac:(dj_cs) ltac:(dcE_infp)), (PR 8%bv ltac:(dj_cs) ltac:(dcE_infp)),
    (PR 9%bv ltac:(dj_cs) ltac:(dcE_infp)), (PR 18%bv ltac:(dj_cs) ltac:(dcE_infp)),
    (PR 19%bv ltac:(dj_cs) ltac:(dcE_infp)), (PR 20%bv ltac:(dj_cs) ltac:(dcE_infp)),
    (PR 23%bv ltac:(dj_cs) ltac:(dcE_infp)), (PR 24%bv ltac:(dj_cs) ltac:(dcE_infp)),
    (PR 26%bv ltac:(dj_cs) ltac:(dcE_infp)), (PR 3%bv ltac:(dj_cs) ltac:(dcE_infp)),
    (PR 4%bv ltac:(dj_cs) ltac:(dcE_infp)), (PR 27%bv ltac:(dj_cs) ltac:(dcE_infp)),
    (PR 21%bv ltac:(dj_cs) ltac:(dcE_infp)), (PR 22%bv ltac:(dj_cs) ltac:(dcE_infp)),
    (PR 25%bv ltac:(dj_cs) ltac:(dcE_infp)).
  repeat (split; [assumption|]). exact R25.
Qed.
(* the model after check_no_loss: slot si is the callee's, every other byte the model reads is kept (the other
   slots, the relay, the stream with errno re-read, g_gone, g_lock, g_wake, g_nfd, g_thread_up, g_listen) *)
Lemma dcE_model_kept : forall ly S (W : world segs) mem ly2 S2 Hp2 (W2 : world segs) mem2 md2 mc si h' R HA,
  ARx ly2 S2 Hp2 W2 mem2 md2 -> (si < 4)%nat -> HA = rg_s fr_RG + ASRC * Z.of_nat si ->
  amodel_ne ly S W mem mc false ->
  Forall (fun e => Z.of_nat (length (re_keys e)) <= re_nheld e) (lm_es mc) ->
  asrc_at B ly2 S2 W2 mem2 HA h' ->
  (forall i b, (i < 4)%nat -> i <> si -> In b (slot_blks (nth i (lm_hs mc) None)) -> In b R) ->
  (forall b, In b (arelay_blks (lm_G mc) (lm_es mc)) -> In b R) ->
  (forall b, In b (aout_blks (lm_cap mc) (lm_out mc)) -> In b R) ->
  (forall b, In b R -> In b (ablocks B ly2 S2)) ->
  (forall b a, In b R -> fst b <= a < fst b + snd b -> abyte_kept W mem W2 mem2 a) ->
  (forall a, inG G_fr a -> ~ inG [(HA + 64, 32)] a -> ~ (as_errno B <= a < as_errno B + 4) ->
     abyte_kept W mem W2 mem2 a) ->
  amodel_ne ly2 S2 W2 mem2 (dc_setsrc mc si h') false.
Proof.
  intros ly S W mem ly2 S2 Hp2 W2 mem2 md2 mc si h' R HA AR2 Hsi EHA HMOD HKY HSRC2 HOi HGER HAOR Rin2 KBLK KI0.
  pose proof dcE_rg as (Es & Esrc & Ensrc & Ecap & Eout & Enout & Ecapout & Esmax & Eseintr & Esdead & Egone & Eclient
    & Ecb & Elock & Ewake).
  assert (EASRC : ASRC = 96) by reflexivity.
  assert (EHA' : HA = rg_s fr_RG + 96 * Z.of_nat si) by (rewrite EHA, EASRC; reflexivity).
  pose proof HERR_HI as HEH.
  pose proof HMOD as (Hlen4 & HSL & HREL & (ev & HOUT) & HGONE & HLOCK & HWAKE & HNFD & HNFDW & HNFDr & HTUP & HLST & HLSTW).
  assert (KGL : forall a, inG G_fr a -> (a < rg_s fr_RG \/ rg_s fr_RG + 4 * ASRC <= a) -> a < rg_out fr_RG + 8 ->
      abyte_kept W mem W2 mem2 a).
  { intros a HGa Hs He. apply KI0; [exact HGa | rewrite dcE_inG1; lia | lia]. }
  assert (KGS : forall a, rg_s fr_RG <= a < rg_s fr_RG + 4 * ASRC -> ~ (HA + 64 <= a < HA + 96) ->
      abyte_kept W mem W2 mem2 a).
  { intros a Ha Hn. apply KI0; [apply HGs; exact Ha | rewrite dcE_inG1; lia | lia]. }
  assert (KDG : forall x n a, In (x, n) DR_GK -> x <= a < x + n -> abyte_kept W mem W2 mem2 a).
  { intros x n a Hx Ha. apply KGL; [apply HG_GK; exact (dcE_inG_mem _ x n a Hx Ha) | |];
      unfold DR_GK in Hx; cbn [In] in Hx;
      repeat (destruct Hx as [Hx | Hx]; [injection Hx as <- <-; unfold AG_NFD, AG_THREAD_UP, AG_LISTEN in *; lia|]);
      destruct Hx. }
  assert (KSL : forall x n a, In (x, n) [(rg_client_broken fr_RG, 1); (rg_send_eintr fr_RG, 1); (rg_nout fr_RG, 8);
      (rg_capout fr_RG, 8); (rg_out fr_RG, 8)] -> x <= a < x + n -> abyte_kept W mem W2 mem2 a).
  { intros x n a Hx Ha. apply KGL.
    - apply HG_DR. apply (dcE_inG_mem _ x n a); [|exact Ha]. unfold G_DR, G_SL. right. cbn [In] in Hx |- *. tauto.
    - cbn [In] in Hx. repeat (destruct Hx as [Hx | Hx]; [injection Hx as <- <-; lia|]). destruct Hx.
    - cbn [In] in Hx. repeat (destruct Hx as [Hx | Hx]; [injection Hx as <- <-; lia|]). destruct Hx. }
  assert (HSL2 : forall i, (i < 4)%nat -> aslot B ly2 S2 W2 mem2 i (nth i (set_nth si (Some h') (lm_hs mc)) None)).
  { intros i Hi. destruct (Nat.eq_dec i si) as [-> | Hne].
    - rewrite set_nth_same by lia. cbn [aslot]. rewrite <- EHA. exact HSRC2.
    - rewrite set_nth_other by lia.
      pose proof (HOi i) as HOi'. pose proof (HSL i Hi) as Hs.
      destruct (nth i (lm_hs mc) None) as [hi|] eqn:Ehi; rewrite ?Ehi in Hs, HOi'; cbn [aslot slot_blks] in Hs, HOi' |- *.
      + apply (asrc_at_kept B ly S W mem ly2 S2 W2 mem2 _ hi Hs).
        * intros r Hr a Ha. destruct (dj_asrc_fp ly S W mem _ hi Hs r Hr a Ha) as [Hin | (b & Hb & Hab)].
          -- cbv beta in Hin. rewrite EASRC in Hin. apply KGS; lia.
          -- exact (KBLK b a (HOi' b Hi Hne Hb) Hab).
        * intros b Hb. exact (Rin2 _ (HOi' b Hi Hne Hb)).
      + destruct Hs as [G1 G2]. split.
        * apply (akept_garr8 W mem); [|exact G1]. intros x Hx. rewrite repeat_length in Hx. rewrite EASRC in Hx.
          apply KGS; lia.
        * apply (akept_awr W mem); [|exact G2]. intros x Hx. rewrite EASRC in Hx. apply KGS; lia. }
  assert (HREL2 : arelay_at B fr_RG ly2 S2 W2 mem2 (lm_G mc) (lm_es mc)).
  { apply (arelay_at_kept B fr_RG ly S W mem ly2 S2 W2 mem2 _ _ HREL).
    - intros r Hr a Ha. destruct (dj_arelay_fp ly S W mem _ _ HREL HKY r Hr a Ha) as [Hg | (b & Hb & Hab)].
      + destruct Hg as [Hg | [Hg | Hg]].
        * apply (KDG (rg_src fr_RG) 8 a); [unfold DR_GK; dcE_infp | exact Hg].
        * apply (KDG (rg_nsrc fr_RG) 4 a); [unfold DR_GK; dcE_infp | exact Hg].
        * apply (KDG (rg_capsrc fr_RG) 4 a); [unfold DR_GK; dcE_infp | exact Hg].
      + exact (KBLK b a (HGER b Hb) Hab).
    - intros b Hb. exact (Rin2 _ (HGER b Hb)). }
  destruct (ERR ly2 S2 Hp2 W2 mem2 md2 AR2) as ((ev2 & Mev2 & Hev2) & Wev2).
  assert (HOUT2 : aout_at B fr_RG ly2 S2 W2 mem2 (dc_ctl (lm_c mc) ev2) (lm_O mc) (lm_mx mc)
                    (Z.of_nat (length (lm_O mc))) (lm_cap mc) (lm_out mc)).
  { apply (dcE_aout ly S W mem ly2 S2 W2 mem2 _ _ _ _ _ _ ev2 HOUT);
      [| intros b Hb; exact (Rin2 _ (HAOR b Hb)) | exact Mev2 | exact Wev2 | exact Hev2].
    intros r Hr a Ha. unfold dcE_ofp in Hr. apply in_app_or in Hr as [Hr | Hr].
    - cbn [In] in Hr.
      destruct Hr as [<- | [<- | [<- | [<- | [<- | [<- | [<- | [<- | []]]]]]]]]; cbn [fst snd] in Ha.
      + apply (KDG (rg_send_max fr_RG) 8 a); [unfold DR_GK; dcE_infp | lia].
      + apply (KSL (rg_nout fr_RG) 8 a); [dcE_infp | lia].
      + apply (KSL (rg_capout fr_RG) 8 a); [dcE_infp | lia].
      + apply (KSL (rg_out fr_RG) 8 a); [dcE_infp | lia].
      + apply (KDG (rg_client fr_RG) 4 a); [unfold DR_GK; dcE_infp | lia].
      + apply (KSL (rg_client_broken fr_RG) 1 a); [dcE_infp | lia].
      + apply (KDG (rg_send_dead fr_RG) 1 a); [unfold DR_GK; dcE_infp | lia].
      + apply (KSL (rg_send_eintr fr_RG) 1 a); [dcE_infp | lia].
    - revert Hr. destruct (Z.eqb_spec (lm_cap mc) 0) as [Ec | Ec]; intros Hr; cbn in Hr.
      + destruct Hr.
      + destruct Hr as [<- | []]. cbn [fst snd] in Ha.
        apply (KBLK (lm_out mc, lm_cap mc) a); [|cbn [fst snd]; lia].
        apply HAOR. unfold aout_blks. rewrite (proj2 (Z.eqb_neq (lm_cap mc) 0) Ec). left. reflexivity. }
  assert (HGONE2 : agone_at fr_RG W2 mem2 (lm_gn mc)).
  { apply (agone_at_kept fr_RG W mem W2 mem2 _ HGONE). intros r [<- | []] a Ha. cbn [fst snd] in Ha.
    apply (KDG (rg_gone fr_RG) 1 a); [unfold DR_GK; dcE_infp | lia]. }
  assert (HLOCK2 : alock_at fr_RG W2 mem2 false).
  { apply (alock_at_kept fr_RG W mem W2 mem2 _ HLOCK). intros r [<- | []] a Ha. cbn [fst snd] in Ha.
    apply KGL; [apply HGlock; lia | lia | lia]. }
  assert (HWAKE2 : awake_at fr_RG W2 mem2).
  { apply (awake_at_kept fr_RG W mem W2 mem2 HWAKE). intros r [<- | []] a Ha. cbn [fst snd] in Ha.
    apply (KDG (rg_wake fr_RG) 8 a); [unfold DR_GK; dcE_infp | lia]. }
  unfold amodel_ne. cbn [dc_setsrc lm_hs lm_G lm_es lm_c lm_O lm_mx lm_cap lm_out lm_gn lm_nfd].
  split; [rewrite set_nth_length; exact Hlen4|].
  split; [exact HSL2|]. split; [exact HREL2|]. split; [exists ev2; exact HOUT2|].
  split; [exact HGONE2|]. split; [exact HLOCK2|]. split; [exact HWAKE2|].
  split; [apply (akept_vm W mem); [|exact HNFD]; intros x Hx; apply (KDG AG_NFD 4 x); [unfold DR_GK; dcE_infp | lia]|].
  split; [apply (akept_awr W mem); [|exact HNFDW]; intros x Hx; apply (KDG AG_NFD 4 x); [unfold DR_GK; dcE_infp | lia]|].
  split; [exact HNFDr|].
  split; [apply (akept_vm W mem); [|exact HTUP]; intros x Hx; apply (KDG AG_THREAD_UP 1 x); [unfold DR_GK; dcE_infp | lia]|].
  split; [destruct HLST as (lst & HL); exists lst; apply (akept_vm W mem); [|exact HL]; intros x Hx;
          apply (KDG AG_LISTEN 4 x); [unfold DR_GK; dcE_infp | lia]|].
  apply (akept_awr W mem); [|exact HLSTW]. intros x Hx. apply (KDG AG_LISTEN 4 x); [unfold DR_GK; dcE_infp | lia].
Qed.

Lemma dc_stE : forall cx Hpe t m j si fpos FF ly S Hp mc h1 W c,
  lf_base_x B MT XM_LIB RLO RHI fr_live_pre LIBROOM NP G_fr ARx cx Hpe ->
  (si < 4)%nat -> nth si (lm_hs mc) None = Some h1 ->
  NoDup (texts (hs_held h1)) -> hl_n (hs_expected h1) < 2 ^ 26 ->
  hl_n (hs_held h1) + Z.of_nat (count_begin (texts (hs_expected h1))) < 2 ^ 22 ->
  cnl_room MMAX (blocks_bytes S) (texts (hs_held h1)) (hl_cap (hs_held h1)) (hl_recs (hs_expected h1)) ->
  mo_ok MT S (cnl_cost MT (hs_expected h1) (hs_held h1)) ->
  AREC * capb (hs_held h1) (hs_expected h1) < 2 ^ 32 ->
  NP S -> cnt_ok_pk RP (cnl_pk (hs_expected h1) (hs_held h1)) (ablocks B ly S) ->
  (lm_gn mc = 0 -> exists rest, lm_O mc = bstream (hs_expected h1) ++ rest) ->
  dc_at cx Hpe t m j si fpos FF A_dc_r4 ly S Hp mc false 0 W c ->
  SRr segs W c (fun W' c' => exists ly' S' Hp' E' H',
    dc_at cx Hpe t m j si fpos FF A_dc_r5 ly' S' Hp' (dc_setsrc mc si (set_exp_held h1 E' H')) false
      (if lm_gn mc =? 0 then Z.of_nat (length (bstream (hs_expected h1))) else 0) W' c' /\
    mo_le MT S S' (cnl_cost MT (hs_expected h1) (hs_held h1)) /\
    dr_cfun h1 E' H' /\ NP S' /\
    (forall rest, Permutation (ablocks B ly S) (list_blks (hs_expected h1) ++ list_blks (hs_held h1) ++ rest) ->
       Permutation (ablocks B ly' S') (list_blks E' ++ list_blks H' ++ rest)) /\
    hl_n H' <= hl_cap H').
Proof.
  intros cx Hpe t m j si fpos FF ly S Hp mc h1 W c HB Hsi Hh1 HND HnE HnH HROOM HMO HCAPB HNPs HCNTc HOB
    (regs & mem & md & k & -> & DR & HJ & HFF & HFR & HFL & HIN & HRV & HROM & SVN & SAT & SLK & HMOD & HSEP & HKY).
  pose proof DR as DR0.
  destruct DR as (R2 & R8 & R9 & R18 & R19 & R20 & R23 & R24 & R26 & R3 & R4 & R27 & Ht & R21 & R22 & R25).
  pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs.
  pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  pose proof dr_ceil_lo as HCL.
  assert (HAR : ARx ly S Hp W mem md) by (eapply ajournal_gx_AR_x; exact HJ).
  pose proof HB as (HAI & HPRE).
  pose proof HPRE as (HFNP & _ & _ & _ & _ & Hnlen & _).
  pose proof HFNP as (_ & _ & _ & _ & _ & Hstk & _).
  pose proof Hstk as (Hal16 & _ & Hceil & Hslo & Hshi & H47 & _ & Htop & _).
  unfold LLVMF_STK in Hslo.
  assert (HFb : spZ (c_regs cx) - 352 < lf_F cx <= spZ (c_regs cx) - 320).
  { unfold lf_F. pose proof (Z.mod_pos_bound (spZ (c_regs cx) - 320) 32 ltac:(lia)). lia. }
  assert (HF32 : lf_F cx mod 32 = 0).
  { unfold lf_F. rewrite Zminus_mod, Z.mod_mod, Z.sub_diag by lia. reflexivity. }
  pose proof (pal_env B TL) as ((HE0 & HE1) & _).
  set (sp0 := spZ (c_regs cx)) in *.
  set (F := lf_F cx) in *.
  assert (Hsp : spZ regs = F) by (unfold spZ; rewrite R2; unfold w64; apply unsigned_lit_small; unfold DR_CEIL8 in *; lia).
  destruct (dc_plain_entry A_dc_r4 W regs mem R26) as [HS SHOK].
  remember (Eimg (Ereg regs [])) as E eqn:HE.
  assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
  assert (HAE : env_agree 32 (Ereg regs []) E)
    by (rewrite HE; split; [intros n Hn; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
  clear HE.
  paj_run_to_tok_x RUNTO HS HJ SHOK DRspan AF_fr_check_no_loss.
  { apply awr_ok_x_nil. }
  dr_meq HF Em.
  pose proof (regs_kept_of_st_ok_pi _ _ _ regs _ [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv
                HS HAE ltac:(vm_compute; reflexivity)) as KR3.
  cbn [ms_regs restrict] in KR3.
  prreg HS (1%bv : bv 5) Q1. prreg HS (10%bv : bv 5) Q10. prreg HS (11%bv : bv 5) Q11.
  pmkst HS. rewrite Em in *. clear HF HFr HG0.
  (* ---- the call's registers ---- *)
  set (regsc := ms_regs ms) in *.
  set (mdc := with_vm_backing (m_vm_lazy md) mat md) in *.
  pose proof dcE_rg as (Es & Esrc & Ensrc & Ecap & Eout & Enout & Ecapout & Esmax & Eseintr & Esdead & Egone & Eclient
    & Ecb & Elock & Ewake).
  pose proof dcE_vals as (Vnout & Vout & Vgone & Vs).
  assert (EASRC : ASRC = 96) by reflexivity.
  set (HA := rg_s fr_RG + ASRC * Z.of_nat si) in *.
  assert (EHA : HA = rg_s fr_RG + ASRC * Z.of_nat si) by reflexivity.
  assert (HFlo : DR_CEIL8 + 32000 <= F) by (unfold DR_CEIL8; lia).
  assert (E21 : ew E 21 = getr regs 21)
    by (rewrite (proj1 HAE 21%nat ltac:(apply Nat.ltb_lt; reflexivity)); apply ew_Ereg_nat; reflexivity).
  assert (E9 : ew E 9 = getr regs 9)
    by (rewrite (proj1 HAE 9%nat ltac:(apply Nat.ltb_lt; reflexivity)); apply ew_Ereg_nat; reflexivity).
  assert (Rc10 : getr regsc 10 = w64 HA) by (rewrite Q10, E21; exact R21).
  assert (Rc11 : getr regsc 11 = w64 (F + 192)).
  { rewrite Q11, E9, R9. unfold w64. rewrite unsigned_lit_small by (unfold DR_CEIL8 in *; lia). reflexivity. }
  assert (Hspc : spZ regsc = F).
  { unfold spZ. rewrite (KR3 2%bv ltac:(dcE_infp)). exact Hsp. }
  assert (HJin : exists memS, ajournal_x segs B PST ARx LLVMF_STK sp0 (lf_FP fr_FP cx) (c_ly cx) (c_S cx) Hpe (c_W cx) memS (c_md cx)
      [(1, fpos)] ly S Hp W mem mdc k).
  { pose proof HJ as (_ & _ & (memS & HJ0 & _) & _). rewrite !Z.add_0_r in HJ0. exists memS. exact HJ0. }
  destruct HJin as (memS & HJ0).
  pose proof HJ0 as (HARc & HLY & _ & _ & _ & HFRS0 & _ & _ & _ & _ & _ & _ & HJgone & HJpres & _).
  assert (Etop : ly_top ly = ly_top (c_ly cx)) by (pose proof HLY as (_ & _ & _ & _ & _ & _ & _ & _ & X & _); exact X).
  assert (Hfin : In (1, fpos) (frames S)) by (rewrite HFRS0; left; reflexivity).
  (* ---- the model at the call ---- *)
  pose proof HMOD as (Hlen4 & HSL & HREL & (ev & HOUT) & HGONE & HLOCK & HWAKE & HNFD & HNFDW & HNFDr & HTUP & HLST & HLSTW).
  assert (HSRC : asrc_at B ly S W mem HA h1) by (pose proof (HSL si Hsi) as X; rewrite Hh1 in X; exact X).
  pose proof HSRC as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HLE & HLH & _).
  set (LE := list_blks (hs_expected h1)). set (LH := list_blks (hs_held h1)).
  set (PP := (hs_partial h1, APARTIAL) :: alist_blks (hs_pending h1)).
  set (OTH := concat (map slot_blks (firstn si (lm_hs mc) ++ skipn (Datatypes.S si) (lm_hs mc)))).
  set (ENT := concat (map aentry_blks (lm_es mc))).
  set (AO := aout_blks (lm_cap mc) (lm_out mc)).
  set (GE := [(lm_G mc, ATABLE)]).
  destruct HSEP as ((RS & HPm0) & HSEP2).
  set (R := PP ++ input_blks cx ++ GE ++ ENT ++ OTH ++ AO ++ RS).
  assert (HCS : Permutation (concat (map slot_blks (lm_hs mc))) ((PP ++ LE ++ LH) ++ OTH)).
  { pose proof (dr_concat_nth_perm _ _ slot_blks (lm_hs mc) si None ltac:(lia)) as X. rewrite Hh1 in X. exact X. }
  assert (HP1 : Permutation (ablocks B ly S) ((LE ++ LH) ++ R)).
  { apply (Permutation_trans HPm0).
    exact (dcE_perm_shape (input_blks cx) GE ENT OTH AO RS PP LE LH (concat (map slot_blks (lm_hs mc))) HCS). }
  assert (HND1 : List.NoDup ((LE ++ LH) ++ R)) by exact (Permutation_NoDup HP1 (dj_nodup ly S Hp W mem md HAR)).
  assert (LEHin : forall b, In b (LE ++ LH) -> In b (ablocks B ly S)).
  { intros b Hb. apply (Permutation_in _ (Permutation_sym HP1)). apply in_or_app. left. exact Hb. }
  assert (Rin : forall b, In b R -> In b (ablocks B ly S)).
  { intros b Hb. apply (Permutation_in _ (Permutation_sym HP1)). apply in_or_app. right. exact Hb. }
  assert (RnLEH : forall b, In b R -> ~ In b (LE ++ LH)) by (intros b H1 H2; exact (dcE_nodup_app _ _ b HND1 H2 H1)).
  assert (CSmodel : forall b, In b (concat (map slot_blks (lm_hs mc))) -> In b (model_blks mc)).
  { intros b Hb. unfold model_blks. right. apply in_or_app. right. apply in_or_app. left. exact Hb. }
  assert (H1CS : forall b, In b (PP ++ LE ++ LH) -> In b (concat (map slot_blks (lm_hs mc)))).
  { intros b Hb. apply in_concat. exists (slot_blks (Some h1)). split; [apply in_map; rewrite <- Hh1; apply nth_In; lia|].
    exact Hb. }
  assert (LEHmodel : forall b, In b (LE ++ LH) -> In b (model_blks mc)).
  { intros b Hb. apply CSmodel, H1CS. apply in_or_app. right. exact Hb. }
  assert (LEHpos : forall b, In b (LE ++ LH) -> 0 < snd b).
  { intros b Hb. apply in_app_or in Hb as [Hb | Hb].
    - exact (dcE_blks_pos ly S W mem _ _ _ HLE b Hb).
    - exact (dcE_blks_pos ly S W mem _ _ _ HLH b Hb). }
  (* ---- check_no_loss's G: slot si's two list headers ---- *)
  assert (HGcG : forall a, inG [(HA + 64, 32)] a -> inG G_fr a).
  { intros a Ha. apply dcE_inG1 in Ha. apply HGs. lia. }
  assert (HGc : gx_ok segs B [(HA + 64, 32)]) by exact (gx_ok_sub segs B _ _ HGcG HG).
  assert (HGrt : gx_rt B [(HA + 64, 32)]).
  { intros a Ha. apply dcE_inG1 in Ha. destruct HAP as [HAP0 HAP32]. split; [|split]; lia. }
  assert (HZc : azs B (HA + 64) 32).
  { destruct HZS as (r & Hr & H8 & H1 & H2). exists r. split; [exact Hr|]. split; [exact H8|]. split; lia. }
  (* ---- check_no_loss's premises ---- *)
  pose proof HOUT as (_ & _ & O3 & _ & _ & _ & O7 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
                      _ & _ & _ & _ & _ & _ & _ & O26).
  assert (HAOR : forall b, In b AO -> In b R)
    by (intros b Hb; unfold R; do 5 (apply in_or_app; right); apply in_or_app; left; exact Hb).
  assert (HPPR : forall b, In b PP -> In b R) by (intros b Hb; unfold R; apply in_or_app; left; exact Hb).
  assert (HOBX : ob_at W mem (lm_out mc) (lm_O mc) /\
     Z.of_nat (length (lm_O mc)) <= 2 ^ 40 /\ (0 < Z.of_nat (length (lm_O mc)) -> Z.of_nat (length (lm_O mc)) < 2 ^ 32) /\
     amem_range (lm_out mc) (Z.of_nat (length (lm_O mc)) + 8) /\
     (lm_O mc = [] \/ exists CO, Z.of_nat (length (lm_O mc)) <= CO /\ In (lm_out mc, CO) (ablocks B ly S) /\
        ~ In (lm_out mc) (hs_blocks h1))).
  { destruct O26 as [(Hc0 & Hout0 & Hno0) | (Hcp & Hno & Hin & junk & Hj & Hg)].
    - assert (HO0 : lm_O mc = []) by (apply length_zero_iff_nil; lia).
      rewrite HO0, Hout0. cbn [length]. split; [intros i Hi; cbn in Hi; lia|].
      split; [lia|]. split; [lia|]. split; [left; unfold kLowMemEnd; lia | left; reflexivity].
    - destruct (alx_blocks _ _ _ LAWS ly S Hp W mem md _ _ HAR Hin) as (_ & _ & _ & Happ & _ & _); pose proof (BLKR ly S Hp W mem md _ _ HAR Hin) as Hmx.
      assert (Ers : req_size (lm_cap mc) = lm_cap mc) by (unfold req_size; rewrite (proj2 (Z.eqb_neq (lm_cap mc) 0) ltac:(lia)); reflexivity).
      rewrite Ers in Happ.
      split; [exact (dcE_ob_at W mem _ _ _ Hg)|].
      split; [lia|]. split; [lia|].
      split; [zlia|].
      right. exists (lm_cap mc). split; [lia|]. split; [exact Hin|].
      intros Hx. destruct (dcE_hs_blocks h1 _ Hx) as (n & Hn).
      assert (HnPP : In (lm_out mc, n) (PP ++ LE ++ LH)) by exact Hn.
      assert (HAOc : In (lm_out mc, lm_cap mc) AO)
        by (unfold AO, aout_blks; rewrite (proj2 (Z.eqb_neq (lm_cap mc) 0) ltac:(lia)); left; reflexivity).
      assert (Hn1 : In (lm_out mc, n) (ablocks B ly S)).
      { apply in_app_or in HnPP as [Hpo | Hpo]; [exact (Rin _ (HPPR _ Hpo)) | exact (LEHin _ Hpo)]. }
      destruct (dcE_dec (lm_out mc, n) (lm_out mc, lm_cap mc)) as [Heq | Hne].
      + rewrite Heq in HnPP. apply in_app_or in HnPP as [Hpo | Hpo].
        * apply (dcE_nodup_app PP (input_blks cx ++ GE ++ ENT ++ OTH ++ AO ++ RS) (lm_out mc, lm_cap mc)
            (dcE_nodup_r _ _ HND1) Hpo). do 4 (apply in_or_app; right). apply in_or_app. left. exact HAOc.
        * exact (RnLEH _ (HAOR _ HAOc) Hpo).
      + destruct (alx_blocks _ _ _ LAWS ly S Hp W mem md _ _ HAR Hn1) as (_ & _ & _ & _ & _ & _); pose proof (BLKR ly S Hp W mem md _ _ HAR Hn1) as Hn0.
        pose proof (req_size_pos n ltac:(lia)) as [Hr1 _]. pose proof (req_size_pos (lm_cap mc) ltac:(lia)) as [Hr2 _].
        exact (dj_apart ly S Hp W mem md _ _ _ _ (lm_out mc) HAR Hin Hn1 (fun E => Hne (eq_sym E)) ltac:(lia) ltac:(lia)). }
  destruct HOBX as (HOBAT & HNO40 & HNO32 & HMR & HOB0). clear O26.
  assert (P5 : forall a, spZ regsc <= a < spZ regsc + 208 -> apresent (w_H W) mem a).
  { intros a Ha. apply HJpres. rewrite Hspc in Ha. unfold LLVMF_STK. lia. }
  assert (P21 : val_mem segs (arm W mem) (VAL A_g_gone) 1 (lm_gn mc)) by (rewrite Vgone; exact (proj1 HGONE)).
  assert (P22 : 0 <= lm_gn mc < 256) by (destruct HGONE as (_ & _ & [G0 | G0]); lia).
  assert (P23 : val_mem segs (arm W mem) (VAL A_g_nout) 8 (Z.of_nat (length (lm_O mc)))) by (rewrite Vnout; exact O3).
  assert (P24 : val_mem segs (arm W mem) (VAL A_g_out) 8 (lm_out mc)) by (rewrite Vout; exact O7).
  assert (HF8 : (F + 192) mod 8 = 0).
  { pose proof (Z.div_mod F 32 ltac:(lia)) as D. rewrite HF32, Z.add_0_r in D. rewrite D.
    replace (32 * (F / 32) + 192) with ((4 * (F / 32) + 24) * 8) by ring. apply Z_mod_mult. }
  (* ---- check_no_loss's afn_pre at sp = F ---- *)
  destruct (dr_afn_pre_at cx Hpe ly S Hp fpos k W mem mdc regsc CNL_STK HB HJ) as (ch & HPREc).
  { rewrite HFF. exact (dr_aframe_false cx FF W mem HFR). }
  { exact Hspc. }
  { rewrite Q1. apply ret_ok_codeptr_v; [lia | reflexivity]. }
  { unfold raZ. rewrite Q1, unsigned_lit_small by lia. lia. }
  { rewrite (KR3 3%bv ltac:(dcE_infp)). exact R3. }
  { rewrite (KR3 4%bv ltac:(dcE_infp)). exact R4. }
  { rewrite (KR3 8%bv ltac:(dcE_infp)). exact R8. }
  { rewrite dcE_cnl_stk. lia. }
  { rewrite dcE_cnl_stk. unfold LLVMF_STK. lia. }
  assert (P4 : spZ regsc + 208 <= ly_top ly) by (rewrite Hspc, Etop; lia).
  assert (P8 : HA = VAL A_g_s + ASRC * Z.of_nat si) by (rewrite Vs; reflexivity).
  assert (P11 : spZ regsc <= F + 192) by (rewrite Hspc; lia).
  assert (P12 : F + 192 + 8 <= spZ regsc + 208) by (rewrite Hspc; lia).
  assert (P14 : forall a, HA + 64 <= a < HA + 96 -> inG [(HA + 64, 32)] a) by (intros a Ha; apply dcE_inG1; lia).
  pose proof (dcE_lit W mem _ _ HRV (proj1 dcE_lits)) as L1.
  pose proof (dcE_lit W mem _ _ HRV (proj1 (proj2 dcE_lits))) as L2.
  pose proof (dcE_lit W mem _ _ HRV (proj2 (proj2 dcE_lits))) as L3.
  assert (P20 : 0 <= 0 <= Z.of_nat (length (lm_O mc))) by lia.
  (* ---- the call ---- *)
  set (FPc := blk_FP (LE ++ LH)).
  set (K := fun (ly2 : alayout) (S2 : astate) (Hp2 : list Z) (W2 : world segs) (regs2 : bvmap 5 word)
      (mem2 : word -> option byte) (md2 : Model) =>
    exists kk (E' H' : hlist),
      ajournal_gx_x segs B PST ARx [(HA + 64, 32)] 208 [(F + 192, F + 192 + 8)] CNL_STK (spZ regsc) FPc ly S Hp W mem mdc []
        ly2 S2 Hp2 W2 mem2 md2 kk /\
      asrc_at B ly2 S2 W2 mem2 HA (set_exp_held h1 E' H') /\
      hl_recs E' = [] /\ hl_v E' = hl_v (hs_expected h1) /\ hl_cap E' = hl_cap (hs_expected h1) /\
      NoDup (texts H') /\ texts H' = RelayModel.upds (texts (hs_held h1)) (texts (hs_expected h1)) /\
      hl_cap H' <= Z.max 8 (Z.max (hl_cap (hs_held h1))
                                  (2 * (hl_n (hs_held h1) + Z.of_nat (count_begin (texts (hs_expected h1)))))) /\
      val_mem segs (arm W2 mem2) (F + 192) 8
        (if lm_gn mc =? 0 then 0 + Z.of_nat (length (bstream (hs_expected h1))) else 0) /\
      (forall rest, Permutation (ablocks B ly S) (LE ++ LH ++ rest) ->
         Permutation (ablocks B ly2 S2) (list_blks E' ++ list_blks H' ++ rest)) /\
      mo_le MT S S2 (cnl_cost MT (hs_expected h1) (hs_held h1)) /\ NP S2).
  eapply SRr_mono.
  { apply (dr_callZ G_fr W regsc mem (Z_to_bv 64 (BASE + 13932)) LLVMF_STK sp0 (lf_FP fr_FP cx)
      (c_ly cx) (c_S cx) Hpe (c_W cx) (c_mem cx) (c_md cx) [(1, fpos)] ly S Hp mdc k CNL_STK FPc 208
      [(F + 192, F + 192 + 8)] (F - sp0) (getr regsc 1) ch K HG HJ).
    - rewrite Hspc. lia.
    - lia.
    - rewrite dcE_cnl_stk. unfold LLVMF_STK. lia.
    - lia.
    - lia.
    - intros a (r & [<- | []] & Hr). cbn [fst snd] in Hr. unfold LLVMF_STK. lia.
    - reflexivity.
    - exact HPREc.
    - eapply SRr_mono.
      { exact (CNL [(HA + 64, 32)] HGc HGrt W ly S Hp regsc mem mdc ch 208 HA si (F + 192) h1 (lm_gn mc) 0
          (Z.of_nat (length (lm_O mc))) (lm_out mc) (lm_O mc)
          HPREc ltac:(lia) eq_refl P4 P5 Rc10 Rc11 P8 Hsi HF8 P11 P12 HSRC P14 HZc
          HND HnE HnH SAT P20 P21 P22 P23 P24 HOBAT eq_refl HNO40 HNO32 HMR HOB0 HOB HRV L1 L2 L3 HROOM HMO
          0%nat ltac:(apply RP_NP; exact HNPs) HCNTc HCAPB
          ltac:(intros a Ha; rewrite Hspc in Ha; exact (dr_stkr cx Hpe fpos ly S Hp W mem mdc k HB HJ a Ha))). }
      cbv beta. intros W2 c2 _ (ly2 & S2 & Hp2 & regs2 & mem2 & md2 & kk & E' & H' & -> & JC & HPR & HPK & _ & HSRC2 & ER & EV & EC &
        HNDH & HTX & HCAPH & MAT & MGN & MNO & MOUT & HOB2 & HPERM & HFRS & HMO2 & HRM2 & _ & _).
      exists ly2, S2, Hp2, regs2, mem2, md2, kk. split; [reflexivity|].
      split; [eapply ajournal_gx_G_mono_x; [exact HGcG | exact JC]|].
      split; [exact HPR|].
      unfold K. exists kk, E', H'. split; [exact JC|]. split; [exact HSRC2|].
      do 6 (split; [assumption|]). split; [exact MAT|]. split; [exact HPERM|].
      split; [exact HMO2 | exact (proj1 (RP_NP S2 0%nat) HRM2)].
    - intros a (r & Hr & Hra). unfold FPc, blk_FP in Hr. apply in_map_iff in Hr as ([p n] & <- & Hb). cbn [fst snd] in Hra.
      pose proof (LEHin _ Hb) as Hbl.
      destruct (in_dec dcE_dec (p, n) (ablocks B (c_ly cx) (c_S cx))) as [Hc | Hc].
      + left. destruct (HSEP2 _ (LEHmodel _ Hb)) as [Hn | Hfp]; [exfalso; exact (Hn Hc)|].
        split; [exact (Hfp a Hra)|].
        exists p, n. split; [exact Hbl | exact Hra].
      + right. exists p, n. split; [exact Hbl|]. split; [exact Hc | exact Hra]. }
  cbv beta. intros W2 c2 _ (ly2 & S2 & Hp2 & regs2 & mem2 & md2 & k1 & -> & HJ2 & _ & HPR2 & HK2).
  unfold K in HK2.
  destruct HK2 as (kk & E' & H' & JC & HSRC2 & ER & EV & EC & HNDH & HTX & HCAPH & MAT & HPERM & HMO2 & HNP2).
  (* the held list's count clause at the return (asrc_at's alist_at of the held list, W_rep.v:81) *)
  assert (HHN : hl_n H' <= hl_cap H').
  { pose proof HSRC2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HHD & _).
    cbn [set_exp_held hs_held] in HHD. pose proof HHD as (_ & _ & _ & _ & (Hn6 & _) & _). exact Hn6. }
  rewrite Hspc in JC. clear HOB0.
  assert (AR2 : ARx ly2 S2 Hp2 W2 mem2 md2) by (eapply ajournal_gx_AR_x; exact JC).
  assert (EHA' : HA = rg_s fr_RG + 96 * Z.of_nat si) by (rewrite EHA, EASRC; reflexivity).
  set (h' := set_exp_held h1 E' H') in *.
  set (LE' := list_blks E'). set (LH' := list_blks H').
  assert (HP2 : Permutation (ablocks B ly2 S2) ((LE' ++ LH') ++ R)).
  { rewrite <- app_assoc. apply HPERM. rewrite app_assoc. exact HP1. }
  assert (HND2 : List.NoDup ((LE' ++ LH') ++ R)) by exact (Permutation_NoDup HP2 (dj_nodup ly2 S2 Hp2 W2 mem2 md2 AR2)).
  assert (Rin2 : forall b, In b R -> In b (ablocks B ly2 S2)).
  { intros b Hb. apply (Permutation_in _ (Permutation_sym HP2)). apply in_or_app. right. exact Hb. }
  assert (LEHin2 : forall b, In b (LE' ++ LH') -> In b (ablocks B ly2 S2)).
  { intros b Hb. apply (Permutation_in _ (Permutation_sym HP2)). apply in_or_app. left. exact Hb. }
  (* ---- what check_no_loss keeps ---- *)
  pose proof (dcE_kept_blk _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HGc JC HARc LEHin) as KB0.
  pose proof (dcE_kept_img _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HGc JC HARc LEHin) as KI0.
  pose proof (dcE_kept_frame _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HGc JC HARc LEHin) as KF0.
  assert (KBLK : forall b a, In b R -> fst b <= a < fst b + snd b -> abyte_kept W mem W2 mem2 a).
  { intros [p n] a HbR Ha. cbn [fst snd] in Ha. pose proof (Rin _ HbR) as Hin1.
    destruct (alx_blocks _ _ _ LAWS ly S Hp W mem md p n HAR Hin1) as (_ & _ & _ & _ & _ & _); pose proof (BLKR ly S Hp W mem md p n HAR Hin1) as Hn.
    pose proof (req_size_pos n ltac:(lia)) as [_ Hrs].
    exact (KB0 p n a Hin1 (Rin2 _ HbR) (RnLEH _ HbR) ltac:(lia)). }
  assert (HOi : forall i b, (i < 4)%nat -> i <> si -> In b (slot_blks (nth i (lm_hs mc) None)) -> In b R).
  { intros i b Hi Hne Hb. assert (Hb' : In b OTH).
    { unfold OTH. apply in_concat. exists (slot_blks (nth i (lm_hs mc) None)). split; [|exact Hb].
      apply in_map. apply dcE_nth_rm; [rewrite Hlen4; exact Hi | exact Hne]. }
    unfold R. do 4 (apply in_or_app; right). apply in_or_app. left. exact Hb'. }
  assert (HGER : forall b, In b (arelay_blks (lm_G mc) (lm_es mc)) -> In b R).
  { intros b [<- | Hb]; unfold R.
    - do 2 (apply in_or_app; right). apply in_or_app. left. unfold GE. left. reflexivity.
    - do 3 (apply in_or_app; right). apply in_or_app. left. exact Hb. }
  pose proof (dcE_model_kept ly S W mem ly2 S2 Hp2 W2 mem2 md2 mc si h' R HA AR2 Hsi EHA HMOD HKY HSRC2 HOi HGER HAOR
    Rin2 KBLK KI0) as HMOD2.
  (* ---- the blocks after the call ---- *)
  assert (HCS' : Permutation (concat (map slot_blks (set_nth si (Some h') (lm_hs mc)))) ((PP ++ LE' ++ LH') ++ OTH))
    by exact (dr_concat_set_nth_perm _ _ slot_blks (lm_hs mc) si (Some h') ltac:(lia)).
  assert (HP3 : Permutation (input_blks cx ++ model_blks (dc_setsrc mc si h') ++ RS) ((LE' ++ LH') ++ R))
    by exact (dcE_perm_shape (input_blks cx) GE ENT OTH AO RS PP LE' LH' _ HCS').
  assert (HSEP' : ablocks_sep B fr_FP cx (dc_setsrc mc si h') ly2 S2).
  { split; [exists RS; exact (Permutation_trans HP2 (Permutation_sym HP3))|].
    intros b Hb.
    assert (Hcase : In b (LE' ++ LH') \/ In b (model_blks mc)).
    { unfold model_blks in Hb. cbn [dc_setsrc lm_G lm_es lm_hs lm_cap lm_out] in Hb.
      destruct Hb as [<- | Hb]; [right; unfold model_blks; left; reflexivity|].
      apply in_app_or in Hb as [Hb | Hb]; [right; unfold model_blks; right; apply in_or_app; left; exact Hb|].
      apply in_app_or in Hb as [Hb | Hb];
        [|right; unfold model_blks; right; apply in_or_app; right; apply in_or_app; right; exact Hb].
      apply (Permutation_in _ HCS') in Hb. apply in_app_or in Hb as [Hb | Hb].
      - apply in_app_or in Hb as [Hb | Hb]; [right; apply CSmodel, H1CS, in_or_app; left; exact Hb | left; exact Hb].
      - right. apply CSmodel. unfold OTH in Hb. apply in_concat in Hb as (l & Hl & Hbl). apply in_concat.
        exists l. split; [|exact Hbl]. apply in_map_iff in Hl as (o & <- & Ho). apply in_map.
        exact (dr_in_rm _ si o (lm_hs mc) Ho). }
    destruct Hcase as [Hnew | Hold]; [|exact (HSEP2 b Hold)].
    destruct (in_dec dcE_dec b (ablocks B (c_ly cx) (c_S cx))) as [Hc | Hc]; [|left; exact Hc]. right.
    destruct (in_dec dcE_dec b (ablocks B ly S)) as [Hb1 | Hb1].
    - apply (Permutation_in _ HP1) in Hb1. apply in_app_or in Hb1 as [Hb1 | Hb1].
      + destruct (HSEP2 b (LEHmodel b Hb1)) as [Hn | Hfp]; [exfalso; exact (Hn Hc) | exact Hfp].
      + exfalso. exact (dcE_nodup_app _ _ b HND2 Hnew Hb1).
    - destruct b as [p n]. intros a Ha. cbn [fst snd] in Ha.
      pose proof (LEHin2 _ Hnew) as Hb2.
      destruct (alx_blocks _ _ _ LAWS ly2 S2 Hp2 W2 mem2 md2 p n AR2 Hb2) as (_ & _ & _ & _ & _ & _); pose proof (BLKR ly2 S2 Hp2 W2 mem2 md2 p n AR2 Hb2) as Hn.
      pose proof (req_size_pos n ltac:(lia)) as [_ Hrs].
      replace a with (p + (a - p)) by lia. exact (HJgone p n (a - p) Hc Hb1 ltac:(lia)). }
  (* ---- the frame, the input, the ROM, the cells ---- *)
  assert (KOUT : forall a, F <= a < sp0 -> ~ (F + DR_AT <= a < F + DR_AT + 8) -> abyte_kept W mem W2 mem2 a).
  { intros a Ha Hn. unfold DR_AT in Hn.
    apply (dcE_kept _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ a HGc JC).
    - unfold DR_CEIL8 in *. lia.
    - rewrite dcE_inG1. unfold DR_CEIL8 in *. lia.
    - intros Hi. pose proof (Hsegs a Hi). unfold DR_CEIL8 in *. lia.
    - destruct (Z_lt_le_dec a (F + 208)) as [Hlt | Hge].
      + right; left. split; [lia|]. intros (r & [<- | []] & Hr). cbn [fst snd] in Hr. lia.
      + left. unfold DR_CEIL8 in *. split; lia. }
  assert (WF : forall a, F <= a < sp0 -> writable_at segs (arm W2 mem2) a).
  { pose proof HJ2 as (_ & _ & (memS2 & HJ20 & _) & _). rewrite !Z.add_0_r in HJ20.
    pose proof HJ20 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HJ2pres & _).
    intros a Ha. apply (apresent_writable segs). apply HJ2pres. unfold LLVMF_STK. lia. }
  assert (KFF : forall a, FF <= a < FF + 128 -> abyte_kept W mem W2 mem2 a).
  { intros a Ha. apply (KF0 1 fpos a Hfin). left. unfold in_zr, frame_rng. cbn [fst snd].
    rewrite HFF. replace (fs_frame_bytes 1) with 128 by reflexivity. lia. }
  assert (KSH : forall a, SB + FF / 8 <= a < SB + FF / 8 + 16 -> abyte_kept W mem W2 mem2 a).
  { intros a Ha. apply (KF0 1 fpos a Hfin). right. unfold in_zr. cbn [fst snd].
    rewrite HFF. replace (fs_frame_bytes 1 / 8) with 16 by reflexivity. unfold shadow_addr.
    unfold SB, SHADOW_OFF in *. lia. }
  assert (H320 : lf_F cx + 320 <= spZ (c_regs cx)) by (change (F + 320 <= sp0); lia).
  assert (HFR2 : aframe_at cx true FF W2 mem2) by exact (dcE_aframe_kept cx true FF W W2 mem mem2 HFR H320 KOUT WF KFF KSH).
  assert (HFL2 : sv8 W2 mem2 (FF + 120) (flag_addr ly2 1 fpos)).
  { pose proof JC as (_ & _ & (memC & JC0 & _) & _). pose proof JC0 as (_ & HLY2 & _).
    pose proof HLY2 as (_ & _ & _ & _ & _ & EF & _). unfold flag_addr. rewrite EF.
    apply (dr_sv8_kept W W2 mem mem2); [intros x Hx; apply KFF; lia | exact HFL]. }
  assert (HIN2 : ainput_at B cx ly2 S2 W2 mem2).
  { destruct HIN as (Hcase & Hg).
    assert (HINR : c_n cx <> 0 -> In (c_p cx, c_n cx) R).
    { intros Hn0. unfold R. apply in_or_app. right. apply in_or_app. left. unfold input_blks.
      rewrite (proj2 (Z.eqb_neq (c_n cx) 0) Hn0). left. reflexivity. }
    split.
    - destruct Hcase as [Hc | (Hn & Hin)]; [left; exact Hc | right; split; [exact Hn|]].
      exact (Rin2 _ (HINR ltac:(lia))).
    - apply (akept_garr8 W mem); [|exact Hg]. intros x Hx. rewrite length_map in Hx.
      destruct Hcase as [(Hc & _) | (Hn & Hin)].
      + lia.
      + apply (KBLK (c_p cx, c_n cx) x (HINR ltac:(lia))). cbn [fst snd]. lia. }
  assert (HRO : rom_out segs B [(HA + 64, 32)]).
  { intros a Ha. destruct (DR_ROM_OUT a Ha) as (H1 & H2 & H3 & H4).
    split; [intros HGa; exact (H1 (HGcG a HGa))|]. split; [exact H2|]. split; [exact H3 | exact H4]. }
  assert (HRV2 : rom_view segs W2 mem2)
    by exact (ajournal_gx_rom_view_x segs B PST ARx LAWS pa_segs_low _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ JC HRO dr_pstr HRV).
  assert (HROM2 : jt_rom W2 mem2) by exact (dcE_jt_kept W W2 mem mem2 HRV HRV2 HROM).
  assert (SVN2 : sv8 W2 mem2 (F + DR_N) (c_n cx - dr_k' cx m)).
  { apply (dr_sv8_kept W W2 mem mem2); [|exact SVN]. intros x Hx. apply KOUT; unfold DR_N, DR_AT in *; lia. }
  assert (SLK2 : sv8 W2 mem2 (F + 40) (rg_lock fr_RG)).
  { apply (dr_sv8_kept W W2 mem mem2); [|exact SLK]. intros x Hx. apply KOUT; unfold DR_AT in *; lia. }
  assert (SAT2 : sv8 W2 mem2 (F + DR_AT) (if lm_gn mc =? 0 then Z.of_nat (length (bstream (hs_expected h1))) else 0)).
  { replace (0 + Z.of_nat (length (bstream (hs_expected h1)))) with (Z.of_nat (length (bstream (hs_expected h1))))
      in MAT by lia. exact MAT. }
  pose proof (dcE_regs_kept cx t m j si FF regs regsc regs2 KR3 HPR2 DR0) as DR2.
  (* ---- the state at 0x84a78 ---- *)
  exists ly2, S2, Hp2, E', H'.
  split; [|split; [exact HMO2 | split; [exact (conj ER (conj EV (conj EC (conj HNDH (conj HTX HCAPH))))) |
    split; [exact HNP2 | split; [exact HPERM | exact HHN]]]]].
  exists regs2, mem2, md2, (k + k1).
  split; [rewrite Q1; reflexivity|].
  split; [exact DR2|].
  split; [exact HJ2|].
  split.
  { pose proof JC as (_ & _ & (memC & JC0 & _) & _). pose proof JC0 as (_ & HLY2 & _).
    pose proof HLY2 as (_ & _ & _ & _ & _ & EF & _). unfold frame_addr in HFF |- *. rewrite EF. exact HFF. }
  split; [exact HFR2|]. split; [exact HFL2|]. split; [exact HIN2|]. split; [exact HRV2|]. split; [exact HROM2|].
  split; [exact SVN2|]. split; [exact SAT2|]. split; [exact SLK2|].
  split; [exact HMOD2|]. split; [exact HSEP'|]. exact HKY.
Qed.



Lemma dc_calls : forall cx Hpe t m j si h fpos ly3 S3 Hp3 k W c,
  lf_base_x B MT XM_LIB RLO RHI fr_live_pre LIBROOM NP G_fr ARx cx Hpe ->
  DLK cx Hpe t m j si h fpos ly3 S3 Hp3 k W c ->
  SRr segs W c (DST A_dr_join cx Hpe (t + 1) (lregs_join cx t)).
Proof.
  intros cx Hpe t m j si h fpos ly3 S3 Hp3 k W c HB HD.
  pose proof HD as (regs & mem & md & -> & HJ & HFR & _ & HMOD & HIN & HRV & HROM & HSEP & HLS & HNP & HRI & Hatop & Hpick & Hj &
                    Hfdj & Hef0 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Ht & _).
  pose proof HMOD as (Hlen4 & _ & _ & _ & (_ & _ & Hgn01) & _).
  pose proof Hpick as (_ & Hsi & Hhsi).
  pose proof Hatop as (_ & HO0 & _).
  assert (HST : dc_static cx t m j si h) by exact (conj Hatop (conj Hpick (conj Hj (conj Hfdj (conj Hef0 HRI))))).
  set (FF := frame_addr ly3 1 fpos).
  eapply SRr_bind; [exact (dc_stA cx Hpe t m j si h fpos ly3 S3 Hp3 k W _ HB HD)|]. intros W1 c1 _ H1.
  eapply SRr_bind; [exact (dc_stB cx Hpe t m j si h fpos FF ly3 S3 Hp3 W1 c1 HB HST HLS HNP H1)|].
  intros W2 c2 _ (ly4 & S4 & Hp4 & e' & h' & out' & ev' & LB & H2 & HMO1 & HDF & HOUT4).
  destruct HOUT4 as (EPRE & EKH & HPRE3 & HHN3 & CAP0 & HPERMD & EPOST & HPOST3 & DPOST & HNP4 & HCNTc).
  eapply SRr_bind; [exact (dc_stC cx Hpe t m j si fpos FF ly4 S4 Hp4 _ W2 c2 HB H2)|]. intros W3 c3 _ H3.
  set (m1 := dr_m1 m j si h h' e' ev' LB out') in *.
  pose proof HDF as (D1 & D2 & D3 & D4 & D5 & D6 & D7 & D8 & D9 & D10 & D11 & D12 & D13 & D14 & D15 & D16 & D17 & D18 &
                     D19 & D20 & D21 & D22 & D23 & D24).
  assert (Hh1 : nth si (lm_hs m1) None = Some h').
  { unfold m1, dr_m1, dr_step. cbn [lm_hs]. apply set_nth_same. lia. }
  eapply SRr_bind; [exact (dc_stD cx Hpe t m j si fpos FF ly4 S4 Hp4 m1 h' W3 c3 HB Hsi Hh1 D14 H3)|]. intros W4 c4 _ H4.
  destruct (RI_src cx t m si h HRI Hpick) as (Hexp0 & _ & _).
  destruct (LS_cnl_pre cx t m ly3 S3 ly4 S4 si h j h' e' (dr_cap1 m j h) out' HLS HRI Hpick Hj Hfdj Hef0 HMO1 D22 D17 D18
             Ht HO0 EPRE HPRE3 CAP0 HPERMD eq_refl EPOST HPOST3)
    as (N1 & N2 & N3 & N4 & N5 & N6).
  (* the stream after the drain is the expected lines' bytes, when the controller is there *)
  assert (HBS : bstream (hs_expected h') = LB) by (rewrite Hexp0 in D17; exact (dc_bstream_LB _ _ LB D17 D21)).
  destruct (RI_gone cx t m HRI) as (G0 & G1).
  assert (HOB : lm_gn m1 = 0 -> exists rest, lm_O m1 = bstream (hs_expected h') ++ rest).
  { intros Hg. exists []. rewrite app_nil_r, HBS. cbn [m1 dr_m1 dr_step lm_gn lm_O] in Hg |- *. unfold dr_O1.
    rewrite HO0. cbn [app]. destruct (G0 Hg) as (C3 & C0 & D0).
    unfold dr_live, sl_live, send_line_c.send_live, send_line_c.send_off. rewrite C3, C0, D0. cbn.
    destruct (Z.eqb_spec (dr_tot h) 0) as [Ht0 | Ht0]; cbn; [|reflexivity].
    pose proof (dc_LB_len LB _ D21) as HL. unfold dr_tot in Ht0. rewrite Ht0 in HL.
    destruct LB; [reflexivity | cbn [length] in HL; lia]. }
  eapply SRr_bind;
    [exact (dc_stE cx Hpe t m j si fpos FF ly4 S4 Hp4 m1 h' W4 c4 HB Hsi Hh1 N1 N2 N3 N4 N5 N6 HNP4 HCNTc HOB H4)|].
  intros W5 c5 _ (ly6 & S6 & Hp6 & E' & H' & H5 & HMO2 & HCF & HNP6 & HCFR & HHN6).
  set (m2 := dc_setsrc m1 si (set_exp_held h' E' H')) in *.
  (* the at cell: |bstream| when the controller is there, 0 else; g_nout: |O1| *)
  assert (HA : (if lm_gn m1 =? 0 then Z.of_nat (length (bstream (hs_expected h'))) else 0) = Z.of_nat (length (lm_O m2))).
  { cbn [m2 dc_setsrc m1 dr_m1 dr_step lm_gn lm_O]. unfold dr_O1. rewrite HO0. cbn [app].
    destruct Hgn01 as [Hg | Hg]; rewrite Hg; cbn [Z.eqb].
    - destruct (HOB ltac:(cbn [m1 dr_m1 dr_step lm_gn]; exact Hg)) as (rest & Hr).
      cbn [m1 dr_m1 dr_step lm_O] in Hr. unfold dr_O1 in Hr. rewrite HO0 in Hr. cbn [app] in Hr.
      rewrite HBS. destruct (dr_live (lm_c m) h); [reflexivity|].
      rewrite HBS in Hr. destruct LB; [reflexivity | cbn in Hr; discriminate].
    - assert (Hlv : dr_live (lm_c m) h = false).
      { destruct (G1 Hg) as [C | [C | C]]; unfold dr_live, sl_live, send_line_c.send_live, send_line_c.send_off;
          rewrite C; cbn; [reflexivity | rewrite orb_true_r; reflexivity | rewrite andb_false_r; reflexivity]. }
      rewrite Hlv. reflexivity. }
  rewrite HA in H5.
  assert (Hfin : forall ev, dc_fin cx m m2 ev =
    dr_step m (dr_k' cx m) si (set_exp_held h' E' H') j e' (dr_ctl (lm_c m) h ev) (dr_O1 m h LB) (dr_cap1 m j h) out').
  { intros ev. unfold dc_fin, m2, dc_setsrc, m1, dr_m1, dr_step. cbn [lm_hs lm_G lm_es lm_c lm_O lm_mx lm_cap lm_out lm_gn lm_nfd].
    rewrite dc_set_nth_twice, dc_ctl_dr. reflexivity. }
  apply (dc_stF cx Hpe t m j si fpos FF ly6 S6 Hp6 m2 W5 c5 HB Hatop HNP6).
  - intros ev. rewrite Hfin.
    apply (RI_drain_step cx t m si h j e' h' (dr_ctl (lm_c m) h ev) (dr_O1 m h LB) (dr_cap1 m j h) out' ev LB E' H'
             HRI Ht N3 Hatop Hpick Hj Hfdj Hef0).
    unfold dr_step_ok. cbv zeta.
    destruct HCF as (F1 & F2 & F3 & F4 & F5 & F6).
    repeat (split; [first [assumption | reflexivity]|]). first [assumption | reflexivity].
  - intros ev. rewrite Hfin.
    pose proof HCF as (F1 & F2 & F3 & F4 & F5 & F6).
    exact (LS_drain_step cx t m ly3 S3 S4 ly6 S6 si h j (set_exp_held h' E' H') e' (dr_ctl (lm_c m) h ev)
             (dr_O1 m h LB) (dr_cap1 m j h) out' (hs_expected h') (hs_held h') ly4 h' E' H'
             HLS Hpick Hj HMO1 HMO2 HPERMD D14 eq_refl eq_refl HCFR eq_refl Hatop HRI Hfdj Hef0
             EPRE EKH HPRE3 HHN3 CAP0 eq_refl EPOST HPOST3 DPOST
             (conj F1 (conj F3 (conj F4 (conj F5 (conj F6 HHN6))))) Ht).
  - exact H5.
Qed.

(* (5) 0x84a20-0x84a7c: the eof test and, when the relay still reads the source, the six calls. *)

Lemma dr_found_join : forall cx Hpe t j W c,
  lf_base_x B MT XM_LIB RLO RHI fr_live_pre LIBROOM NP G_fr ARx cx Hpe ->
  DST A_dr_found cx Hpe t (lregs_found cx t j) W c ->
  SRr segs W c (DST A_dr_join cx Hpe (t + 1) (lregs_join cx t)).
Proof.
  intros cx Hpe t j W c HB (regs & mem & md & -> & HROM &
    (own & ly3 & S3 & Hp3 & k & m & fpos & HJ & Hown & HFR & HFL & HMOD & HIN & HRV & HSEP & HLS & HNP & HRI & HR)).
  destruct HR as (((R2 & R8 & R9 & R18 & R19 & R20 & R23 & R24 & R25 & R26 & R3 & R4) & R27 & Ht)
    & Hatop & R28 & SVN & (si & h & Hpick & R21 & Hfdj & Hnom) & Hj & R10 & R22).
  pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs.
  pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  pose proof dr_ceil_lo as HCL.
  assert (HAR : ARx ly3 S3 Hp3 W mem md) by (eapply ajournal_gx_AR_x; exact HJ).
  pose proof HMOD as (Hlen4 & HSL & HREL & HOUT & HGONE & HLOCK & HWAKE & HNFD & HNFDW & HNFDr & HTUP & HLST & HLSTW).
  pose proof HREL as (Msrc & Wsrc & Mnsrc & Wnsrc & Mcap & Wcap & Hle16 & HGin & (tl & HTAB) & HENT & HNDF & _).
  destruct (dr_pads_of_relay ly3 S3 W mem (lm_G m) (lm_es m) HREL) as (HPAD & HFDS).
  remember (nth j (lm_es m) dr_e0) as e eqn:Hedef.
  assert (HEOK : aentry_ok B ly3 S3 W mem e) by (rewrite Hedef; rewrite Forall_forall in HENT; apply HENT, nth_In; exact Hj).
  pose proof HEOK as (Heof01 & _).
  pose proof (dr_tbl_eof W mem (lm_G m) (lm_es m) tl j HTAB HPAD Hj ltac:(rewrite <- Hedef; lia)) as Mef.
  rewrite <- Hedef in Mef.

  pose proof HB as (HAI & HPRE).
  pose proof HPRE as (HFNP & _ & _ & _ & Hnrng & Hnlen & _).
  assert (Hn26 : c_n cx < 2 ^ 26) by (destruct Hnrng as [(Hz & _) | (Hz & _)]; lia).
  pose proof HFNP as (_ & _ & _ & _ & _ & Hstk & _).
  pose proof Hstk as (Hal16 & _ & Hceil & Hslo & Hshi & H47 & _).
  unfold LLVMF_STK in Hslo.
  assert (HFb : spZ (c_regs cx) - 352 < lf_F cx <= spZ (c_regs cx) - 320).
  { unfold lf_F. pose proof (Z.mod_pos_bound (spZ (c_regs cx) - 320) 32 ltac:(lia)). lia. }
  assert (HF32 : lf_F cx mod 32 = 0).
  { unfold lf_F. rewrite Zminus_mod, Z.mod_mod, Z.sub_diag by lia. reflexivity. }
  pose proof (pal_env B TL) as ((HE0 & HE1) & _).
  assert (Hfin : In (1, fpos) (frames S3)).
  { pose proof HJ as (_ & _ & (memS & HJ0 & _) & _). pose proof HJ0 as (_ & _ & _ & _ & _ & Hfrs & _).
    rewrite Hfrs, Hown. left. reflexivity. }
  destruct (frames_bounds_x segs B ARx LAWS ly3 S3 Hp3 W mem md 1 fpos HAR Hfin) as (HFF1 & HFF2 & _).
  replace (fs_frame_bytes 1) with 128 in HFF2 by reflexivity.
  set (FF := frame_addr ly3 1 fpos) in *.
  pose proof HFR as (_ & HAWR & _).
  destruct (alx_blocks _ _ _ LAWS ly3 S3 Hp3 W mem md (lm_G m) ATABLE HAR HGin) as (HG16 & HG4096 & HGceil & _).
  assert (RQ : req_size ATABLE = 896) by reflexivity. rewrite RQ in HGceil.
  assert (Hj16 : Z.of_nat j < 16) by lia.
  assert (HSA8 : (lm_G m + AENT * Z.of_nat j) mod 8 = 0).
  { unfold AENT. pose proof (Z.div_mod (lm_G m) 16 ltac:(lia)) as D. rewrite HG16, Z.add_0_r in D.
    rewrite D. replace (16 * (lm_G m / 16) + 56 * Z.of_nat j) with ((2 * (lm_G m / 16) + 7 * Z.of_nat j) * 8) by ring.
    apply Z_mod_mult. }
  destruct (dc_found_entry ly3 S3 Hp3 W mem md regs (lf_F cx) (lm_G m) j (re_eof e) HAR R9 R10 R22 R26)
    as [HS SHOK].
  { unfold DR_CEIL8 in *. lia. }
  { lia. }
  { exact HF32. }
  { intros a Ha. replace a with (lf_F cx + (a - lf_F cx)) by lia. apply HAWR. lia. }
  { intros a Ha. replace a with (lf_F cx + (a - lf_F cx)) by lia. apply HAWR. lia. }
  { exact HGin. }
  { unfold AENT; lia. }
  { exact HSA8. }
  { unfold AENT, DR_CEIL8 in *; lia. }
  { unfold AENT; lia. }
  { unfold AENT, ATABLE; lia. }
  { exact Mef. }
  { lia. }

  remember (Eimg (Ereg regs (dc_extra (re_eof e)))) as E eqn:HE.
  assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
  assert (HAE : env_agree 32 (Ereg regs (dc_extra (re_eof e))) E)
    by (rewrite HE; split; [intros n Hn; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
  assert (EEo : forall q (rr : bv 5), Z.of_nat q = bv_unsigned rr -> ew E q = getr regs rr)
    by (intros q rr Hq; subst E; pose proof (bv_unsigned_in_range 5 rr) as Hr5; change (bv_modulus 5) with 32 in Hr5;
        rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_nat; exact Hq).
  assert (E9 : ew E 9 = Z_to_bv 64 (lf_F cx)) by (rewrite (EEo 9%nat 9%bv eq_refl); exact R9).
  assert (E32 : ew E 32 = Z_to_bv 64 (re_eof e))
    by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
  assert (U9 : bv_unsigned (ew E 9) = lf_F cx) by (rewrite E9; apply unsigned_lit_small; unfold DR_CEIL8 in *; lia).
  clear HE.
  unfold cfg_at. change (w64 (fr_B0 + A_dr_found)) with (Z_to_bv 64 (BASE + A_dr_found)).
  paj_run_tok_x RUN HS HJ SHOK DRspan.
  { unfold ss_dc_found, dc_rA, dc_rL, dc_rE. cbn [ss_mem].
    repeat (apply awr_ok_x_cons;
      [ let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha;
        cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; rewrite ?U9 in Ha;
        first [ lia | left; split; [left; unfold LLVMF_STK; lia | lia] ]
      | ]).
    apply awr_ok_x_nil. }
  rename HFr into HFr1, HG0 into HG1. clear HF.
  psrr_branch_tok RUN de_BR HS SHOK DRspan.

  - (* 0x84a40 bnez a0 taken: the relay's entry is at end of file, the operation is a no-op - to 0x84a80 *)
    lazymatch type of Hc with branch_taken _ (sv_denot ?Ev _) _ = _ =>
      assert (U32 : U Ev (SOff 32 0) = re_eof e) by (apply U_atom; [rewrite !ew_ewset_other by lia; exact E32 | lia]) end.
    rewrite branch_ne_U, U32, U_lit in Hc by lia. apply Bool.negb_true_iff, Z.eqb_neq in Hc.
    assert (Hef1 : re_eof e = 1) by lia.
    paj_run_to_tok_x RUNTO HS HJ SHOK DRspan A_dr_join.
    { unfold dc_rA, dc_rL, dc_rE. cbn [ss_mem add_cond].
      repeat (apply awr_ok_x_cons;
        [ let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha;
          cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; rewrite ?ew_ewset_other in Ha by lia; rewrite ?U9 in Ha;
          first [ lia | left; split; [left; unfold LLVMF_STK; lia | lia] ]
        | ]).
      apply awr_ok_x_nil. }

    assert (Hk' : 0 <= dr_k' cx m <= c_n cx)
      by (pose proof Hatop as (Hk0 & _ & _); unfold dr_k'; destruct (Z.ltb_spec (lm_k m + 1) (c_n cx)); lia).
    assert (K1 : forall a, 0 <= a < 2 ^ 64 -> dc_out cx a -> aview segs (w_H W) (ms_mem ms) a = aview segs (w_H W) mem a).
    { intros a Ha (Hn1 & Hn2). apply (aview_kept_out _ _ _ _ _ HFr1 a Ha).
      intros (r & Hin & Hr). cbn [ss_mem ss_dc_found In] in Hin.
      repeat (destruct Hin as [<- | Hin];
        [ cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val dc_rA dc_rL dc_rE] in Hr; rewrite ?U9 in Hr; unfold DR_AT in Hn2; lia | ]).
      destruct Hin. }
    assert (K2 : forall a, 0 <= a < 2 ^ 64 -> dc_out cx a -> aview segs (w_H W) (ms_mem ms0) a = aview segs (w_H W) mem a).
    { intros a Ha Hno. rewrite <- (K1 a Ha Hno). destruct Hno as (Hn1 & Hn2). apply (aview_kept_out _ _ _ _ _ HFr a Ha).
      intros (r & Hin & Hr). cbn [ss_mem add_cond In] in Hin.
      repeat (destruct Hin as [<- | Hin];
        [ cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr; rewrite ?ew_ewset_other in Hr by lia; rewrite ?U9 in Hr;
          unfold DR_AT in Hn2; lia | ]).
      destruct Hin. }
    assert (WK : forall a, writable_at segs (arm W mem) a -> writable_at segs (arm W (ms_mem ms0)) a).
    { intros a Hw. apply (writable_kept (w_H W) mem (ms_mem ms0) a); [|exact Hw].
      intros Hpo. exact (de_pres_grows W _ _ a HG0 (de_pres_grows W _ _ a HG1 Hpo)). }
    assert (KEEP : forall a, 0 <= a < 2 ^ 64 -> dc_out cx a -> abyte_kept W mem W (ms_mem ms0) a)
      by (intros a Ha Hna; split; [exact (K2 a Ha Hna) | apply WK]).
    destruct (dc_carry cx W mem (ms_mem ms0) md ly3 S3 Hp3 fpos m HAR Hfin (eq_sym Hnlen) ltac:(lia)
                HFR HMOD HIN HRV HROM KEEP WK) as (HFR2 & HMOD2 & HIN2 & HRV2 & HROM2).
    assert (SVN2 : sv8 W (ms_mem ms0) (lf_F cx + DR_N) (c_n cx - dr_k' cx m)).
    { apply (dr_sv8_kept W W mem (ms_mem ms0)); [|exact SVN].
      intros x Hx. apply KEEP; [unfold DR_N, DR_CEIL8 in *; lia | unfold dc_out, DR_N, DR_AT in *; lia]. }
    assert (HFL2 : sv8 W (ms_mem ms0) (FF + 120) (flag_addr ly3 1 fpos)).
    { apply (dr_sv8_kept W W mem (ms_mem ms0)); [|exact HFL].
      intros x Hx. apply KEEP; [unfold DR_CEIL8 in *; lia | unfold dc_out, DR_AT in *; lia]. }
    assert (E28 : ew E 28 = Z_to_bv 64 (c_p cx + dr_k' cx m)) by (rewrite (EEo 28%nat 28%bv eq_refl); exact R28).
    lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
      assert (HAE2 : env_agree 32 (Ereg regs (dc_extra (re_eof e))) Ev)
        by (split; [intros q Hq; rewrite !ew_ewset_other by lia; exact (proj1 HAE q Hq)
                   | rewrite !ed_ewset; exact (proj2 HAE)]) end.
    pose proof (regs_kept_of_st_ok_pi _ _ _ regs _ DR_KEPT HS HAE2 ltac:(vm_compute; reflexivity)) as KR.
    cbn [ms_regs restrict] in KR.
    prreg HS (25%bv : bv 5) Q25. rewrite ?ew_ewset_other in Q25 by lia. rewrite E28 in Q25.
    pmkst HS.
    apply SRr_ret.
    lazymatch goal with |- context [mkCfg (mkst ?r _ ?mm _) ?d] => exists r, mm, d end.
    split; [reflexivity|]. split; [exact HROM2|].
    exists own, ly3, S3, Hp3, k, (dr_skip m (dr_k' cx m)), fpos.
    split; [exact HJ|]. split; [exact Hown|]. split; [exact HFR2|]. split; [exact HFL2|]. split; [exact HMOD2|].
    split; [exact HIN2|]. split; [exact HRV2|]. split; [exact HSEP|].
    split; [apply LS_drain_skip; exact HLS|]. split; [exact HNP|].
    split; [apply (RI_drain_skip cx t m si h HRI Hatop Hpick); right; exists j;
            split; [exact Hj|]; rewrite <- Hedef; split; [exact Hfdj | exact Hef1]|].
    split; [rewrite (KR 2%bv ltac:(cbv; tauto)); exact R2|].
    split; [rewrite (KR 8%bv ltac:(cbv; tauto)); exact R8|].
    split; [rewrite (KR 9%bv ltac:(cbv; tauto)); exact R9|].
    split; [rewrite (KR 18%bv ltac:(cbv; tauto)); exact R18|].
    split; [rewrite (KR 19%bv ltac:(cbv; tauto)); exact R19|].
    split; [rewrite (KR 20%bv ltac:(cbv; tauto)); exact R20|].
    split; [rewrite (KR 23%bv ltac:(cbv; tauto)); exact R23|].
    split; [rewrite (KR 24%bv ltac:(cbv; tauto)); exact R24|].
    split; [rewrite (KR 26%bv ltac:(cbv; tauto)); exact R26|].
    split; [rewrite (KR 3%bv ltac:(cbv; tauto)); exact R3|].
    split; [rewrite (KR 4%bv ltac:(cbv; tauto)); exact R4|].
    split; [rewrite (KR 27%bv ltac:(cbv; tauto)); exact R27|].
    split; [exact Ht|].
    split; [rewrite Q25; reflexivity|].
    split; [exact SVN2|]. exact Hk'.

  - (* 0x84a40 bnez a0 not taken: the relay still reads the source - the six calls *)
    lazymatch type of Hc with branch_taken _ (sv_denot ?Ev _) _ = _ =>
      assert (U32 : U Ev (SOff 32 0) = re_eof e) by (apply U_atom; [rewrite !ew_ewset_other by lia; exact E32 | lia]) end.
    rewrite branch_ne_U, U32, U_lit in Hc by lia. apply Bool.negb_false_iff, Z.eqb_eq in Hc.
    rename Hc into Hef0.
    (* 0x84a44-0x84a50: a0 = &g_lock, sd a0,40(s1), jal pthread_mutex_lock *)
    paj_run_tok_x RUN HS HJ SHOK DRspan.
    { unfold dc_rA, dc_rL, dc_rE. cbn [ss_mem add_cond].
      repeat (apply awr_ok_x_cons;
        [ let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha;
          cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; rewrite ?ew_ewset_other in Ha by lia; rewrite ?U9 in Ha;
          first [ lia | left; split; [left; unfold LLVMF_STK; lia | lia] ]
        | ]).
      apply awr_ok_x_nil. }

    rename HFr into HFr2, HG0 into HG2. clear HF.
    assert (Hk' : 0 <= dr_k' cx m <= c_n cx)
      by (pose proof Hatop as (Hk0 & _ & _); unfold dr_k'; destruct (Z.ltb_spec (lm_k m + 1) (c_n cx)); lia).
    assert (K1 : forall a, 0 <= a < 2 ^ 64 -> dc_out cx a -> aview segs (w_H W) (ms_mem ms) a = aview segs (w_H W) mem a).
    { intros a Ha (Hn1 & Hn2). apply (aview_kept_out _ _ _ _ _ HFr1 a Ha).
      intros (r & Hin & Hr). cbn [ss_mem ss_dc_found In] in Hin.
      repeat (destruct Hin as [<- | Hin];
        [ cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val dc_rA dc_rL dc_rE] in Hr; rewrite ?U9 in Hr; unfold DR_AT in Hn2; lia | ]).
      destruct Hin. }
    assert (K2 : forall a, 0 <= a < 2 ^ 64 -> dc_out cx a -> aview segs (w_H W) (ms_mem ms0) a = aview segs (w_H W) mem a).
    { intros a Ha Hno. rewrite <- (K1 a Ha Hno). destruct Hno as (Hn1 & Hn2). apply (aview_kept_out _ _ _ _ _ HFr2 a Ha).
      intros (r & Hin & Hr). cbn [ss_mem add_cond In] in Hin.
      repeat (destruct Hin as [<- | Hin];
        [ cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr; rewrite ?ew_ewset_other in Hr by lia; rewrite ?U9 in Hr;
          unfold DR_AT in Hn2; lia | ]).
      destruct Hin. }
    assert (WK : forall a, writable_at segs (arm W mem) a -> writable_at segs (arm W (ms_mem ms0)) a).
    { intros a Hw. apply (writable_kept (w_H W) mem (ms_mem ms0) a); [|exact Hw].
      intros Hpo. exact (de_pres_grows W _ _ a HG2 (de_pres_grows W _ _ a HG1 Hpo)). }
    assert (KEEP : forall a, 0 <= a < 2 ^ 64 -> dc_out cx a -> abyte_kept W mem W (ms_mem ms0) a)
      by (intros a Ha Hna; split; [exact (K2 a Ha Hna) | apply WK]).
    destruct (dc_carry cx W mem (ms_mem ms0) md ly3 S3 Hp3 fpos m HAR Hfin (eq_sym Hnlen) ltac:(lia)
                HFR HMOD HIN HRV HROM KEEP WK) as (HFR2 & HMOD2 & HIN2 & HRV2 & HROM2).
    assert (SVN2 : sv8 W (ms_mem ms0) (lf_F cx + DR_N) (c_n cx - dr_k' cx m)).
    { apply (dr_sv8_kept W W mem (ms_mem ms0)); [|exact SVN].
      intros x Hx. apply KEEP; [unfold DR_N, DR_CEIL8 in *; lia | unfold dc_out, DR_N, DR_AT in *; lia]. }
    assert (HFL2 : sv8 W (ms_mem ms0) (FF + 120) (flag_addr ly3 1 fpos)).
    { apply (dr_sv8_kept W W mem (ms_mem ms0)); [|exact HFL].
      intros x Hx. apply KEEP; [unfold DR_CEIL8 in *; lia | unfold dc_out, DR_AT in *; lia]. }
    pose proof (st_ok_region_nth _ _ _ 0 _ HS eq_refl) as RG0. cbn [ms_mem restrict] in RG0.
    pose proof (st_ok_region_nth _ _ _ 1 _ HS eq_refl) as RG1. cbn [ms_mem restrict] in RG1.

    assert (S192 : sv8 W (ms_mem ms0) (lf_F cx + DR_AT) 0).
    { unfold sv8, DR_AT.
      lazymatch type of HS with st_ok _ ?Ev _ _ =>
        apply (field_of_region Ev _ 9%nat (lf_F cx) _ _ _ _ _ 192 8%N (SLit 0) 0 RG0) end.
      - rewrite !ew_ewset_other by lia. exact U9.
      - left. reflexivity.
      - reflexivity.
      - lia.
      - lia. }
    assert (VLK : rg_lock fr_RG = 0x5d8ac0) by reflexivity.
    assert (E247 : ew E 247 = Z_to_bv 64 (rg_lock fr_RG)).
    { change 247%nat with (A_OBJ 6). apply bv_eq. rewrite (HEI (A_OBJ 6) ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia)).
      rewrite unsigned_lit_small by (rewrite VLK; lia). vm_compute. reflexivity. }
    assert (S40 : sv8 W (ms_mem ms0) (lf_F cx + 40) (rg_lock fr_RG)).
    { unfold sv8.
      lazymatch type of HS with st_ok _ ?Ev _ _ =>
        apply (field_of_region Ev _ 9%nat (lf_F cx) _ _ _ _ _ 40 8%N (SOff 247 0) (rg_lock fr_RG) RG1) end.
      - rewrite !ew_ewset_other by lia. exact U9.
      - left. reflexivity.
      - cbn [sv_denot]. rewrite !ew_ewset_other by lia. rewrite E247, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
      - rewrite VLK; lia.
      - lia. }

    assert (E28 : ew E 28 = Z_to_bv 64 (c_p cx + dr_k' cx m)) by (rewrite (EEo 28%nat 28%bv eq_refl); exact R28).
    lazymatch type of HS with st_ok _ ?Ev _ _ =>
      assert (HAE2 : env_agree 32 (Ereg regs (dc_extra (re_eof e))) Ev)
        by (split; [intros q Hq; rewrite !ew_ewset_other by lia; exact (proj1 HAE q Hq)
                   | rewrite !ed_ewset; exact (proj2 HAE)]) end.
    pose proof (regs_kept_of_st_ok segs _ _ _ regs _ [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 26; 27]%bv
                  HS HAE2 ltac:(vm_compute; reflexivity)) as KR.
    cbn [ms_regs restrict] in KR.
    prreg HS (1%bv : bv 5) Q1. prreg HS (10%bv : bv 5) Q10. prreg HS (25%bv : bv 5) Q25.
    rewrite ?ew_ewset_other in Q10, Q25 by lia. rewrite E247 in Q10. rewrite E28 in Q25.
    pmkst HS. subst own.
    apply (dc_calls cx Hpe t m j si h fpos ly3 S3 Hp3 k W _ HB).
    lazymatch goal with |- context [mkCfg (mkst ?r _ ?mm _) ?d] => exists r, mm, d end.
    split; [reflexivity|].
    split; [exact HJ|]. split; [exact HFR2|]. split; [exact HFL2|]. split; [exact HMOD2|]. split; [exact HIN2|].
    split; [exact HRV2|]. split; [exact HROM2|]. split; [exact HSEP|]. split; [exact HLS|]. split; [exact HNP|]. split; [exact HRI|].
    split; [exact Hatop|]. split; [exact Hpick|]. split; [exact Hj|].
    rewrite <- Hedef. split; [exact Hfdj|]. split; [exact Hef0|].
    split; [exact SVN2|]. split; [exact S192|]. split; [exact S40|].
    split; [exact Q1|]. split; [exact Q10|].
    split; [rewrite (KR 2%bv ltac:(cbv; tauto)); exact R2|].
    split; [rewrite (KR 8%bv ltac:(cbv; tauto)); exact R8|].
    split; [rewrite (KR 9%bv ltac:(cbv; tauto)); exact R9|].
    split; [rewrite (KR 18%bv ltac:(cbv; tauto)); exact R18|].
    split; [rewrite (KR 19%bv ltac:(cbv; tauto)); exact R19|].
    split; [rewrite (KR 20%bv ltac:(cbv; tauto)); exact R20|].
    split; [rewrite (KR 23%bv ltac:(cbv; tauto)); exact R23|].
    split; [rewrite (KR 24%bv ltac:(cbv; tauto)); exact R24|].
    split; [rewrite (KR 26%bv ltac:(cbv; tauto)); exact R26|].
    split; [rewrite (KR 3%bv ltac:(cbv; tauto)); exact R3|].
    split; [rewrite (KR 4%bv ltac:(cbv; tauto)); exact R4|].
    split; [rewrite (KR 27%bv ltac:(cbv; tauto)); exact R27|].
    split; [exact Ht|].
    split; [rewrite (KR 21%bv ltac:(cbv; tauto)); exact R21|].
    split; [rewrite (KR 22%bv ltac:(cbv; tauto)); exact R22|].
    exact Q25.
Qed.
Lemma dr_join_latch : forall cx Hpe t W c,
  lf_base_x B MT XM_LIB RLO RHI fr_live_pre LIBROOM NP G_fr ARx cx Hpe ->
  DST A_dr_join cx Hpe (t + 1) (lregs_join cx t) W c ->
  SRr segs W c (INV_K_x B NP G_fr fr_FP PST ARx LSx RINV cx Hpe t).
Proof.
  intros cx Hpe t W c HB (regs & mem & md & -> & HROM &
    (own & ly3 & S3 & Hp3 & k & m & fpos & HJ & -> & HFR & HFL & HMOD & HIN & HRV & HSEP & HLS & HNP & HRI & HR)).
  destruct HR as (R2 & R8 & R9 & R18 & R19 & R20 & R23 & R24 & R26 & R3 & R4 & R27 & Ht & R25 & SVN & Hk).
  pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs.
  pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  pose proof HB as (HAI & HPRE & _).
  pose proof HPRE as (HAR0 & Hra0 & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
  pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
  pose proof (Z.mod_pos_bound (spZ (c_regs cx) - 320) 32 ltac:(lia)) as HFm.
  assert (HFb : spZ (c_regs cx) - 352 <= lf_F cx <= spZ (c_regs cx) - 320) by (unfold lf_F; lia).
  unfold LLVMF_STK in *.
  pose proof HFR as (FS & FW & F24 & F48 & F56 & F64 & F72 & F80 & F88 & F96 & F184 & Ffull & _).
  destruct (Ffull eq_refl) as (F32 & F104 & F112 & F120 & F128 & F136 & F152).
  destruct (dr_jn_entry W regs mem (lf_F cx) R9 R26 ltac:(lia) ltac:(lia) F104) as [HS SHOK].
  remember (Eimg (Ereg regs [])) as E eqn:HE.
  assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
  assert (E25 : ew E 25 = Z_to_bv 64 (c_p cx + lm_k m))
    by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia);
        rewrite (ew_Ereg_nat regs _ 25 25%bv eq_refl); exact R25).
  assert (HAE : env_agree 32 (Ereg regs []) E)
    by (rewrite HE; split; [intros n Hn; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
  clear HE.
  unfold cfg_at. change (w64 (fr_B0 + A_dr_join)) with (Z_to_bv 64 (BASE + A_dr_join)).
  (* mv s6,s9 ; j 0x84b28 ; ld s9,104(s1) ; j 0x84490 *)
  paj_run_to_tok_x RUNTO HS HJ SHOK DRspan AF_LLVM_latch.
  { apply awr_ok_x_cons; [intros a Ha; cbn in Ha; lia | apply awr_ok_x_nil]. }
  dr_meq HF Em.
  pose proof (regs_kept_of_st_ok_pi _ _ _ regs _ DR_KEPT HS HAE ltac:(vm_compute; reflexivity)) as KR.
  cbn [ms_regs restrict] in KR.
  prreg HS (22%bv : bv 5) Q22. rewrite E25 in Q22.
  prreg HS (25%bv : bv 5) Q25.
  pmkst HS. rewrite Em in *.
  apply SRr_ret.
  lazymatch goal with |- context [mkCfg (mkst ?r _ ?mm _) ?d] => exists r, mm, d end.
  split; [reflexivity|]. split; [exact HROM|].
  exists [(1, fpos)], ly3, S3, Hp3, k, m, fpos.
  split; [exact HJ|]. split; [reflexivity|]. split; [exact HFR|]. split; [exact HFL|]. split; [exact HMOD|].
  split; [exact HIN|]. split; [exact HRV|]. split; [exact HSEP|]. split; [exact HLS|].
  split; [exact HNP|]. split; [exact HRI|].
  split.
  { split; [rewrite (KR 2%bv ltac:(cbv; tauto)); exact R2|].
    split; [rewrite (KR 8%bv ltac:(cbv; tauto)); exact R8|].
    split; [rewrite (KR 9%bv ltac:(cbv; tauto)); exact R9|].
    split; [rewrite (KR 18%bv ltac:(cbv; tauto)); exact R18|].
    split; [rewrite (KR 19%bv ltac:(cbv; tauto)); exact R19|].
    split; [rewrite (KR 20%bv ltac:(cbv; tauto)); exact R20|].
    split; [rewrite (KR 23%bv ltac:(cbv; tauto)); exact R23|].
    split; [rewrite (KR 24%bv ltac:(cbv; tauto)); exact R24|].
    split; [rewrite Q25; reflexivity|].
    split; [rewrite (KR 26%bv ltac:(cbv; tauto)); exact R26|].
    split; [rewrite (KR 3%bv ltac:(cbv; tauto)); exact R3|].
    rewrite (KR 4%bv ltac:(cbv; tauto)); exact R4. }
  split; [rewrite (KR 27%bv ltac:(cbv; tauto)); exact R27|].
  split; [exact Ht|].
  split; [rewrite Q22; reflexivity|].
  split; [exact SVN|]. exact Hk.
Qed.

(* ------------------------------------------------------------------ the arm *)
(* the text of cut_x's Section w hypothesis ARM_drain (W_LLVMFuzzerTestOneInput_cut_x.v:554) *)
Theorem lf_arm_drain_x : forall cx Hp t W c,
  lf_base_x B MT XM_LIB RLO RHI fr_live_pre LIBROOM NP G_fr ARx cx Hp ->
  INV_A_x B NP G_fr fr_FP PST ARx LSx RINV 2 cx Hp t W c -> SRr segs W c (INV_K_x B NP G_fr fr_FP PST ARx LSx RINV cx Hp t).
Proof.
  intros cx Hpe t W c HB HA.
  eapply SRr_bind; [exact (dr_entry cx Hpe t W c HB HA)|].
  intros W1 c1 _ [(n & HL) | HN].
  - eapply SRr_bind; [exact (dr_scan n cx Hpe t 0 W1 c1 HB HL)|].
    intros W2 c2 _ [(j & HF) | HN].
    + eapply SRr_bind; [exact (dr_found_join cx Hpe t j W2 c2 HB HF)|].
      intros W3 c3 _ HJ. exact (dr_join_latch cx Hpe t W3 c3 HB HJ).
    + eapply SRr_bind; [exact (dr_nf_join cx Hpe t W2 c2 HB HN)|].
      intros W3 c3 _ HJ. exact (dr_join_latch cx Hpe t W3 c3 HB HJ).
  - eapply SRr_bind; [exact (dr_nf_join cx Hpe t W1 c1 HB HN)|].
    intros W3 c3 _ HJ. exact (dr_join_latch cx Hpe t W3 c3 HB HJ).
Qed.

(* CHECK (cut_x's scope): lf_arm_drain_x's type is the Section w hypothesis ARM_drain of
   W_LLVMFuzzerTestOneInput_cut_x.v:554, restated with the generic invariants at this Section's variables *)
Lemma lf_arm_drain_x_check : forall cx Hp t W c,
  lf_base_x B MT XM_LIB RLO RHI fr_live_pre LIBROOM NP G_fr ARx cx Hp ->
  INV_A_x B NP G_fr fr_FP PST ARx LSx RINV 2 cx Hp t W c -> SRr segs W c (INV_K_x B NP G_fr fr_FP PST ARx LSx RINV cx Hp t).
Proof. exact lf_arm_drain_x. Qed.

(* ================================================================== route R *)
(* The arm at a world relation R (RULE-SHAPES.md (sha256 2e856ce788dd; internal record) sec 0; the layout of the 14 twins: a nested Section at the end of the
   strict one, the laws in this order, then the R callee specs in the strict order).  The cut's journal runs from the
   entry, so across earlier operations' frees / reallocs; drain and check_no_loss may re-hide, so their steps are
   SRrG segs R and their journals are at R. *)
Section drxR.
Variable R : world segs -> world segs -> Prop.
Hypothesis R_refl : forall W, R W W.
Hypothesis R_trans : forall W1 W2 W3, R W1 W2 -> R W2 W3 -> R W1 W3.
Hypothesis WLE_R : forall W W', wle W W' -> R W W'.
(* DRAIN and CNL at R: W_contract_xR.v:294 dr_spec_xR, W_contract_xR_g6.v:267 cnl_spec_xR *)
Hypothesis DRAIN_R : W_contract_xR.dr_spec_xR B PST ARx R MT RP MMAX fr_RG (BASE + AF_fr_drain).
Hypothesis CNL_R : forall G, gx_ok segs B G -> gx_rt B G ->
  W_contract_xR_g6.cnl_spec_xR B PST ARx R MT RP G MMAX (BASE + AF_fr_check_no_loss).
(* the runs over the R journal: concluding strict SRr (call-free segments) or SRrG segs R (stages with a call) *)
Let RUNR := paj_run_x_xR (PL := PL_fr) (PI := PB_fr) B PST ARx LAWS R G_fr HG 0 [].
Let RUNTOR := paj_run_to_x_xR (PL := PL_fr) (PI := PB_fr) B PST ARx LAWS R G_fr HG 0 [].
Let RUNG := paj_run_x_xG (PL := PL_fr) (PI := PB_fr) B PST ARx LAWS R G_fr HG 0 [].
Let RUNTOG := paj_run_to_x_xG (PL := PL_fr) (PI := PB_fr) B PST ARx LAWS R G_fr HG 0 [].
Let BRG := paj_branch_xR (PI := PB_fr) (R := R).

(* DST at R: lcut_x -> cut_x's lcut_xR *)
Definition DSTR (pc : Z) (cx : lfcx) (Hpe : list Z) (t : Z)
  (RC : lmod -> Z -> bvmap 5 word -> world segs -> (word -> option byte) -> Prop)
  : world segs -> config -> Prop :=
  fun W c => exists regs mem md, c = cfg_at segs (fr_B0 + pc) regs mem md /\
    jt_rom W mem /\ lcut_xR B NP G_fr fr_FP PST ARx LSx RINV R cx Hpe t true RC regs mem md W.

(* dr_scan at R *)
Lemma dr_scanR : forall n cx Hpe t i W c,
  lf_base_x B MT XM_LIB RLO RHI fr_live_pre LIBROOM NP G_fr ARx cx Hpe ->
  DSTR A_dr_loop cx Hpe t (lregs_scan cx t n i) W c ->
  SRr segs W c (fun W' c' => (exists j, DSTR A_dr_found cx Hpe t (lregs_found cx t j) W' c') \/
                             DSTR A_dr_nf cx Hpe t (lregs_nf cx t) W' c').
Proof.
  intros n. induction n as [|n IH]; intros cx Hpe t i W c HB HD;
    destruct HD as (regs & mem & md & -> & HROM & HLC);
    destruct HLC as (own & ly3 & S3 & Hp3 & kk & m & fpos & HJ & Hown & HFRM & HFLM & HMOD & HINP & HRV & HBLK & HLS & HNP & HRI & HREG);
    unfold lregs_scan in HREG;
    destruct HREG as (HBASEr & HATOP & H28 & HSV8 & (sl & h & HPICK & H21 & H12 & HNM) & Hi & Hnn & H10 & H22 & H11 & H13).
  { exfalso. lia. }
  pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs.
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  assert (HAR : ARx ly3 S3 Hp3 W mem md) by (eapply ajournal_gx_AR_xR; exact HJ).
  pose proof (proj1 (proj2 (proj2 HMOD))) as HREL.
  pose proof HREL as HREL2.
  destruct HREL2 as (_ & _ & _ & _ & _ & _ & Hle16 & HGin & (tl & HTAB) & _ & _).
  destruct (dr_pads_of_relay ly3 S3 W mem (lm_G m) (lm_es m) HREL) as (HPAD & HFDS).
  assert (Hle16Z : Z.of_nat (length (lm_es m)) <= 16) by lia.
  assert (Hin : (Z.to_nat i < length (lm_es m))%nat) by lia.
  pose proof (dr_tbl_fd W mem (lm_G m) (lm_es m) tl (Z.to_nat i) HTAB HPAD HFDS Hin) as Mu.
  rewrite Z2Nat.id in Mu by lia.
  assert (Hfdb : 0 <= re_fd (nth (Z.to_nat i) (lm_es m) dr_e0) < 2 ^ 31)
    by (rewrite Forall_forall in HFDS; apply HFDS, nth_In; lia).
  destruct (RI_src cx t m sl h HRI HPICK) as (_ & _ & Hhfd).
  unfold AENT in Mu, H10, H22.
  destruct (alx_blocks _ _ _ LAWS ly3 S3 Hp3 W mem md (lm_G m) ATABLE HAR HGin) as (HP16 & HP4096 & HPceil & HPapp & _).
  assert (RQ : req_size ATABLE = 896) by reflexivity.
  rewrite RQ in HPceil, HPapp.
  assert (G8 : lm_G m = 8 * (lm_G m / 8)).
  { pose proof (Z.div_mod (lm_G m) 16 ltac:(lia)) as D. rewrite HP16, Z.add_0_r in D.
    rewrite D at 2. replace (16 * (lm_G m / 16)) with ((2 * (lm_G m / 16)) * 8) by ring.
    rewrite Z.div_mul by lia. lia. }
  assert (XQ : (lm_G m + 56 * i) / 8 = lm_G m / 8 + 7 * i).
  { rewrite G8 at 1. replace (8 * (lm_G m / 8) + 56 * i) with ((lm_G m / 8 + 7 * i) * 8) by ring.
    apply Z.div_mul. lia. }
  pose proof HBASEr as HBASE2. unfold lregs_base in HBASE2.
  destruct HBASE2 as (HCOM & H27 & Ht).
  pose proof HCOM as HCOM2. unfold lregs_common in HCOM2.
  destruct HCOM2 as (R2 & R8 & R9 & R18 & R19 & R20 & R23 & R24 & R25 & R26 & R3 & R4).
  remember (Eimg (Ereg regs (ds_extra (re_fd (nth (Z.to_nat i) (lm_es m) dr_e0))))) as E eqn:HE.
  assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
  assert (HAE : env_agree 32 (Ereg regs (ds_extra (re_fd (nth (Z.to_nat i) (lm_es m) dr_e0)))) E)
    by (rewrite HE; split; [intros mm Hm; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
  assert (EEo : forall mm (rr : bv 5), Z.of_nat mm = bv_unsigned rr -> ew E mm = getr regs rr)
    by (intros mm rr Hm; subst E; pose proof (bv_unsigned_in_range 5 rr) as Hr5;
        change (bv_modulus 5) with 32 in Hr5; rewrite Eimg_low by (unfold A_TEXT; lia);
        apply ew_Ereg_nat; exact Hm).
  assert (E10 : ew E 10 = Z_to_bv 64 (lm_G m + 56 * i)) by (rewrite (EEo 10%nat 10%bv eq_refl); exact H10).
  assert (E11 : ew E 11 = Z_to_bv 64 (Z.of_nat (length (lm_es m)) - i))
    by (rewrite (EEo 11%nat 11%bv eq_refl); exact H11).
  assert (E12 : ew E 12 = Z_to_bv 64 (hs_fd h)) by (rewrite (EEo 12%nat 12%bv eq_refl); exact H12).
  assert (E22 : ew E 22 = Z_to_bv 64 (lm_G m + 56 * i)) by (rewrite (EEo 22%nat 22%bv eq_refl); exact H22).
  assert (E26 : ew E 26 = Z_to_bv 64 SB) by (rewrite (EEo 26%nat 26%bv eq_refl); exact R26).
  assert (E32 : ew E 32 = Z_to_bv 64 (re_fd (nth (Z.to_nat i) (lm_es m) dr_e0)))
    by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
  assert (USH : U E (SAlu ALU_ADD (SOff 26 0) (SAlu ALU_SRL (SOff 22 0) (SLit 3)))
                = SB + lm_G m / 8 + 7 * i).
  { rewrite !U_SAlu, (U_atom E 26 SB E26), (U_atom E 22 _ E22), U_lit by (unfold SB; lia). cbn [zalu_raw].
    change (Z.land 3 63) with 3. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8. unfold zcanon, M64.
    rewrite XQ. rewrite (Z.mod_small (lm_G m / 8 + 7 * i)) by lia.
    rewrite Z.mod_small by (unfold SB; lia). lia. }
  assert (HS : st_ok_pi segs VAL E ss_ds
                 (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + A_dr_loop)) mem (seg_rom segs)))).
  { rewrite restrict_mkst_fx. unfold ss_ds. apply pa_entry_st_ok_full.
    - unfold ds_sr. rewrite HE. apply regs_ok_pin; [apply regs_ok_Eimg_Ereg | intros X; discriminate X |].
      rewrite <- HE, H13. apply bv_eq.
      fold (U E (SAlu ALU_ADD (SOff 26 0) (SAlu ALU_SRL (SOff 22 0) (SLit 3)))). rewrite USH.
      apply unsigned_lit_small. unfold SB; lia.
    - vm_compute. reflexivity.
    - unfold ds_regions. repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
        cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
      cbn [base_val]. rewrite E22, unsigned_lit_small by lia.
      split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val segs E _ (lm_G m + 56 * i) 0 4 (SOff 32 0)
               (re_fd (nth (Z.to_nat i) (lm_es m) dr_e0)));
        [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
      rewrite Z.add_0_r. exact Mu.
    - cbn [pairwise_disjoint all_disjoint]. repeat split.
    - split; [|split; [exact I | exact I]].
      cbn [ds_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
      rewrite E22, E26, E32, !unsigned_lit_small by (unfold SB; lia).
      change (2 ^ 3) with 8. rewrite !Z.pow_0_r, !Z.mod_1_r.
      repeat match goal with |- _ /\ _ => split end; try (unfold SB; lia).
      rewrite G8. replace (8 * (lm_G m / 8) + 56 * i) with ((lm_G m / 8 + 7 * i) * 8) by ring.
      apply Z_mod_mult. }
  clear HE.
  assert (HBx : U E ds_Bx = SHADOW_OFF)
    by (unfold ds_Bx; rewrite (U_atom E 26 SB E26) by (unfold SB; lia); reflexivity).
  assert (SHOK : sh_ok segs ds_Bx ds_SH E (mrestrict (w_H W) mem)).
  { constructor; [|constructor].
    eapply shent_ok_of_range.
    + apply (range_addressable_of_block_hp0_x segs B ARx LAWS HP0 ly3 S3 Hp3 W mem md (lm_G m) ATABLE
               (lm_G m + 56 * i) 8 HAR HGin); rewrite ?RQ; lia.
    + exact HBx.
    + rewrite (U_atom E 22 _ E22) by lia. reflexivity.
    + lia.
    + lia.
    + intros x Hx. unfold in_app, SHADOW_OFF, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *. lia. }
  unfold cfg_at. change (w64 (fr_B0 + A_dr_loop)) with (Z_to_bv 64 (BASE + A_dr_loop)).
  paj_run_tok_x RUNR HS HJ SHOK ds_span.
  { apply awr_ok_x_cons; [intros a Ha; cbn in Ha; lia | apply awr_ok_x_nil]. }
  ds_meq HF Em1. clear HF HFr HG0.
  psrr_branch_tok RUNR ds_BR HS SHOK ds_span.
  - rewrite branch_eq_U, (U_atom E 32 _ E32), (U_atom E 12 _ E12) in Hc by lia.
    apply Z.eqb_eq in Hc.
    paj_run_to_tok_x RUNTOR HS HJ SHOK ds_span A_dr_found.
    { apply awr_ok_x_cons; [intros a Ha; cbn in Ha; lia | apply awr_ok_x_nil]. }
    ds_meq HF Em2.
    pose proof (regs_kept_of_st_ok_pi (PI := PB_fr) _ _ _ regs _ DS_KEPT HS HAE
                  ltac:(vm_compute; reflexivity)) as KR.
    cbn [ms_regs restrict] in KR.
    prreg HS (10%bv : bv 5) N10. prreg HS (22%bv : bv 5) N22.
    pmkst HS. rewrite Em2, Em1 in HJ |- *.
    apply SRr_ret. left. exists (Z.to_nat i).
    lazymatch goal with |- DSTR _ _ _ _ _ _ (mkCfg (mkst ?r _ ?mm _) ?d) => exists r, mm, d end.
    split; [reflexivity|]. split; [exact HROM|].
    exists own, ly3, S3, Hp3, kk, m, fpos.
    split; [exact HJ|]. split; [exact Hown|]. split; [exact HFRM|]. split; [exact HFLM|]. split; [exact HMOD|].
    split; [exact HINP|]. split; [exact HRV|]. split; [exact HBLK|]. split; [exact HLS|]. split; [exact HNP|].
    split; [exact HRI|].
    unfold lregs_found.
    split; [exact (ds_base_kept cx t _ regs _ KR HBASEr)|].
    split; [exact HATOP|].
    split; [rewrite (KR 28%bv ltac:(cbv; tauto)); exact H28|].
    split; [exact HSV8|].
    split.
    { exists sl, h. split; [exact HPICK|].
      split; [rewrite (KR 21%bv ltac:(cbv; tauto)); exact H21|].
      split; [exact Hc|]. rewrite Z2Nat.id by lia. exact HNM. }
    split; [exact Hin|].
    split.
    + rewrite N10, E10. unfold w64, AENT. rewrite Z2Nat.id by lia. reflexivity.
    + rewrite N22, E22. unfold w64, AENT. rewrite Z2Nat.id by lia. reflexivity.
  - rewrite branch_eq_U, (U_atom E 32 _ E32), (U_atom E 12 _ E12) in Hc by lia.
    apply Z.eqb_neq in Hc.
    paj_run_tok_x RUNR HS HJ SHOK ds_span.
    { apply awr_ok_x_cons; [intros a Ha; cbn in Ha; lia | apply awr_ok_x_nil]. }
    ds_meq HF Em2. clear HF HFr HG0.
    psrr_branch_tok RUNR ds_BR HS SHOK ds_span.
    + rewrite branch_ne_U, (U_atom_off E 11 _ (-1) E11), U_lit in Hc0 by lia.
      assert (Hlt : i + 1 < Z.of_nat (length (lm_es m)))
        by (destruct (Z.eqb_spec (Z.of_nat (length (lm_es m)) - i + -1) 0); [discriminate | lia]).
      paj_run_to_tok_x RUNTOR HS HJ SHOK ds_span A_dr_loop.
      { apply awr_ok_x_cons; [intros a Ha; cbn in Ha; lia | apply awr_ok_x_nil]. }
      ds_meq HF Em3.
      pose proof (regs_kept_of_st_ok_pi (PI := PB_fr) _ _ _ regs _ DS_KEPT HS HAE
                    ltac:(vm_compute; reflexivity)) as KR.
      cbn [ms_regs restrict] in KR.
      prreg HS (10%bv : bv 5) N10. prreg HS (11%bv : bv 5) N11.
      prreg HS (13%bv : bv 5) N13. prreg HS (22%bv : bv 5) N22.
      rewrite E10, unsigned_lit_small in N10 by lia.
      rewrite E11, unsigned_lit_small in N11 by lia.
      rewrite E22, unsigned_lit_small in N22 by lia.
      assert (Q3 : alu64 ALU_SRL (Z_to_bv 64 (lm_G m + 56 * i)) (Z_to_bv 64 3)
                   = Z_to_bv 64 (lm_G m / 8 + 7 * i)).
      { apply bv_eq. rewrite alu64_unsigned. cbn [zalu_raw]. rewrite !unsigned_lit_small by lia.
        change (Z.land 3 63) with 3. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
        rewrite XQ. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64). apply Z.mod_small. lia. }
      rewrite E26, E22, Q3, !ds_add_lit in N13.
      pmkst HS. rewrite Em3, Em2, Em1 in HJ |- *.
      eapply (IH cx Hpe t (i + 1)); [exact HB|].
      lazymatch goal with |- DSTR _ _ _ _ _ _ (mkCfg (mkst ?r _ ?mm _) ?d) => exists r, mm, d end.
      split; [reflexivity|]. split; [exact HROM|].
      exists own, ly3, S3, Hp3, kk, m, fpos.
      split; [exact HJ|]. split; [exact Hown|]. split; [exact HFRM|]. split; [exact HFLM|]. split; [exact HMOD|].
      split; [exact HINP|]. split; [exact HRV|]. split; [exact HBLK|]. split; [exact HLS|]. split; [exact HNP|].
      split; [exact HRI|].
      unfold lregs_scan.
      split; [exact (ds_base_kept cx t _ regs _ KR HBASEr)|].
      split; [exact HATOP|].
      split; [rewrite (KR 28%bv ltac:(cbv; tauto)); exact H28|].
      split; [exact HSV8|].
      split.
      { exists sl, h. split; [exact HPICK|].
        split; [rewrite (KR 21%bv ltac:(cbv; tauto)); exact H21|].
        split; [rewrite (KR 12%bv ltac:(cbv; tauto)); exact H12|].
        apply ds_nomatch_step; [exact HNM | lia | exact Hc]. }
      split; [lia|].
      split; [lia|].
      split; [rewrite N10; unfold w64, AENT; f_equal; lia|].
      split; [rewrite N22; unfold w64, AENT; f_equal; lia|].
      split; [rewrite N11; unfold w64; f_equal; lia|].
      rewrite N13; unfold w64; f_equal; lia.
    + rewrite branch_ne_U, (U_atom_off E 11 _ (-1) E11), U_lit in Hc0 by lia.
      assert (Hend : i + 1 = Z.of_nat (length (lm_es m)))
        by (destruct (Z.eqb_spec (Z.of_nat (length (lm_es m)) - i + -1) 0); [lia | discriminate]).
      paj_run_to_tok_x RUNTOR HS HJ SHOK ds_span A_dr_nf.
      { apply awr_ok_x_cons; [intros a Ha; cbn in Ha; lia | apply awr_ok_x_nil]. }
      ds_meq HF Em3.
      pose proof (regs_kept_of_st_ok_pi (PI := PB_fr) _ _ _ regs _ DS_KEPT HS HAE
                    ltac:(vm_compute; reflexivity)) as KR.
      cbn [ms_regs restrict] in KR.
      pmkst HS. rewrite Em3, Em2, Em1 in HJ |- *.
      apply SRr_ret. right.
      lazymatch goal with |- DSTR _ _ _ _ _ _ (mkCfg (mkst ?r _ ?mm _) ?d) => exists r, mm, d end.
      split; [reflexivity|]. split; [exact HROM|].
      exists own, ly3, S3, Hp3, kk, m, fpos.
      split; [exact HJ|]. split; [exact Hown|]. split; [exact HFRM|]. split; [exact HFLM|]. split; [exact HMOD|].
      split; [exact HINP|]. split; [exact HRV|]. split; [exact HBLK|]. split; [exact HLS|]. split; [exact HNP|].
      split; [exact HRI|].
      unfold lregs_nf.
      split; [exact (ds_base_kept cx t _ regs _ KR HBASEr)|].
      split; [exact HATOP|].
      split; [rewrite (KR 28%bv ltac:(cbv; tauto)); exact H28|].
      split; [exact HSV8|].
      exists sl, h. split; [exact HPICK|].
      rewrite <- Hend. apply ds_nomatch_step; [exact HNM | lia | exact Hc].
Qed.

(* dr_entry at R *)
Lemma dr_entryR : forall cx Hpe t W c,
  lf_base_x B MT XM_LIB RLO RHI fr_live_pre LIBROOM NP G_fr ARx cx Hpe ->
  INV_A_xR B NP G_fr fr_FP PST ARx LSx RINV R 2 cx Hpe t W c ->
  SRr segs W c (fun W' c' => (exists n, DSTR A_dr_loop cx Hpe t (lregs_scan cx t n 0) W' c') \/
                             DSTR A_dr_nf cx Hpe t (lregs_nf cx t) W' c').
Proof.
  intros cx Hpe t W c HB (regs & regsD & mem & md & -> & KR0 & HD11 & HJOUR & HROM & HLF).
  destruct HLF as (own & ly3 & S3 & Hp3 & k & m & fpos & HJ & Hown & HFR & HFL & HMOD & HIN & HRV & HSEP & HLS & HNP & HRI & HR).
  unfold lregs_D in HR. cbv zeta in HR.
  destruct HR as ((C2 & C8 & C9 & C18 & C19 & C20 & C23 & C24 & C25 & C26 & C3 & C4) & R6 & R7 & R27 & Ht & Hk & HO
    & R11 & HPK).
  pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
  pose proof dr_ceil_lo as HCL.
  assert (Hop : in_byte cx (lm_k m) mod 10 = 2).
  { pose proof (Z.mod_pos_bound (in_byte cx (lm_k m)) 10 ltac:(lia)) as Hb.
    rewrite HD11 in R11. apply (f_equal bv_unsigned) in R11. unfold w64 in R11.
    rewrite !unsigned_lit_small in R11 by lia. lia. }
  rewrite Hop in HPK. change (picks 2) with true in HPK.
  destruct HPK as (R28 & R29 & [(si & Hpk & R21) | (Hf & _)]); [|lia].
  change (if lm_k m + 1 <? c_n cx then lm_k m + 2 else lm_k m + 1) with (dr_k' cx m) in R28, R29.
  change (if lm_k m + 1 <? c_n cx then in_byte cx (lm_k m + 1) else 0) with (dr_kb cx m) in Hpk.
  assert (Hk' : 0 <= dr_k' cx m <= c_n cx)
    by (unfold dr_k'; destruct (Z.ltb_spec (lm_k m + 1) (c_n cx)); lia).
  pose proof HMOD as (Hlen4 & HSL & HREL & _).
  destruct (de_pick_some (lm_hs m) (dr_kb cx m) si Hpk) as [Hsi [h Hh]].
  rewrite Hlen4 in Hsi.
  assert (HPICK : dr_pick cx m si h) by (split; [exact Hpk | split; [exact Hsi | exact Hh]]).
  pose proof (HSL si Hsi) as HSRC. unfold aslot in HSRC. rewrite Hh in HSRC.
  pose proof HSRC as (Mfd & _ & _ & _ & _ & _ & _ & _ & Rfd & _).
  pose proof HREL as (Msrc & _ & Mnsrc & _ & _ & _ & Hl16 & HGin & _).
  pose proof (ajournal_gx_AR_xR segs B PST ARx G_fr 0 [] LLVMF_STK _ _ _ _ _ _ _ _ own ly3 S3 Hp3 W mem md k HJ) as HAR.
  destruct (alx_blocks _ _ _ LAWS ly3 S3 Hp3 W mem md (lm_G m) ATABLE HAR HGin) as (HG16 & HG4096 & HGceil & _).
  assert (RQ : req_size ATABLE = 896) by reflexivity. rewrite RQ in HGceil.
  pose proof HB as (HAI & HPRE).
  pose proof HPRE as (HFNP & _ & _ & _ & Hnrng & Hnlen & _).
  assert (Hn26 : c_n cx < 2 ^ 26) by (destruct Hnrng as [(Hz & _) | (Hz & _)]; lia).
  pose proof HFNP as (_ & _ & _ & _ & _ & Hstk & _).
  pose proof Hstk as (_ & _ & Hceil & Hslo & Hshi & H47 & _).
  unfold LLVMF_STK in Hslo.
  assert (HFb : spZ (c_regs cx) - 352 < lf_F cx <= spZ (c_regs cx) - 320).
  { unfold lf_F. pose proof (Z.mod_pos_bound (spZ (c_regs cx) - 320) 32 ltac:(lia)). lia. }
  pose proof (pal_env B TL) as ((HE0 & HE1) & _).
  assert (HE1' : as_errno B + 4 <= DR_CEIL8) by (unfold DR_CEIL8, kLowMemEnd in *; lia).
  assert (Hfin : In (1, fpos) (frames S3)).
  { pose proof HJ as (_ & _ & (memS & HJ0 & _) & _). pose proof HJ0 as (_ & _ & _ & _ & _ & Hfrs & _).
    rewrite Hfrs, Hown. left. reflexivity. }
  destruct (frames_bounds_x segs B ARx LAWS ly3 S3 Hp3 W mem md 1 fpos HAR Hfin) as (HFF1 & HFF2 & _).
  replace (fs_frame_bytes 1) with 128 in HFF2 by reflexivity.
  set (FF := frame_addr ly3 1 fpos) in *.
  assert (VS : rg_s fr_RG = 0x5d88e0) by reflexivity.
  set (HA := rg_s fr_RG + ASRC * Z.of_nat si) in *.
  assert (HAr : 0x5d88e0 <= HA <= 0x5d88e0 + 288 /\ HA mod 8 = 0).
  { unfold HA. rewrite VS. unfold ASRC. split; [lia|].
    replace (0x5d88e0 + 96 * Z.of_nat si) with ((0xbb11c + 12 * Z.of_nat si) * 8) by lia. apply Z_mod_mult. }
  remember (Eimg (Ereg regs (de_extra (hs_fd h) (Z.of_nat (length (lm_es m))) (lm_G m)))) as E eqn:HE.
  assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
  assert (HAE : env_agree 32 (Ereg regs (de_extra (hs_fd h) (Z.of_nat (length (lm_es m))) (lm_G m))) E)
    by (rewrite HE; split; [intros q Hq; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
  assert (EEo : forall q (rr : bv 5), Z.of_nat q = bv_unsigned rr -> ew E q = getr regs rr)
    by (intros q rr Hq; subst E; pose proof (bv_unsigned_in_range 5 rr) as Hr5; change (bv_modulus 5) with 32 in Hr5;
        rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_nat; exact Hq).
  assert (E9 : ew E 9 = Z_to_bv 64 (lf_F cx))
    by (rewrite (EEo 9%nat 9%bv eq_refl), (KR0 9%bv ltac:(cbv; tauto)); exact C9).
  assert (VN : rg_nsrc fr_RG = 0x5d87a0) by reflexivity.
  assert (VG : rg_src fr_RG = 0x5d87c0) by reflexivity.
  assert (EO7 : ew E (A_OBJ 7) = Z_to_bv 64 (rg_nsrc fr_RG))
    by (subst E; rewrite Eimg_img by (unfold A_OBJ, A_TEXT, A_LIM; lia);
        rewrite (proj1 (proj2 (proj2 de_hi))); reflexivity).
  assert (EO8 : ew E (A_OBJ 8) = Z_to_bv 64 (rg_src fr_RG))
    by (subst E; rewrite Eimg_img by (unfold A_OBJ, A_TEXT, A_LIM; lia);
        rewrite (proj2 (proj2 (proj2 de_hi))); reflexivity).
  assert (E21 : ew E 21 = Z_to_bv 64 HA)
    by (rewrite (EEo 21%nat 21%bv eq_refl), (KR0 21%bv ltac:(cbv; tauto)); exact R21).
  assert (E26 : ew E 26 = Z_to_bv 64 SB)
    by (rewrite (EEo 26%nat 26%bv eq_refl), (KR0 26%bv ltac:(cbv; tauto)); exact C26).
  assert (E29 : ew E 29 = Z_to_bv 64 (c_n cx - dr_k' cx m))
    by (rewrite (EEo 29%nat 29%bv eq_refl), (KR0 29%bv ltac:(cbv; tauto)); exact R29).
  assert (E32 : ew E 32 = Z_to_bv 64 (hs_fd h))
    by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
  assert (E33 : ew E 33 = Z_to_bv 64 (Z.of_nat (length (lm_es m))))
    by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
  assert (E34 : ew E 34 = Z_to_bv 64 (lm_G m))
    by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 2)).
  assert (U9 : bv_unsigned (ew E 9) = lf_F cx) by (rewrite E9; apply unsigned_lit_small; lia).
  assert (U21 : bv_unsigned (ew E 21) = HA) by (rewrite E21; apply unsigned_lit_small; lia).
  assert (UO7 : bv_unsigned (ew E (A_OBJ 7)) = rg_nsrc fr_RG) by (rewrite EO7; apply unsigned_lit_small; lia).
  assert (UO8 : bv_unsigned (ew E (A_OBJ 8)) = rg_src fr_RG) by (rewrite EO8; apply unsigned_lit_small; lia).
  pose proof HFR as (_ & HAWR & _).
  assert (HS : st_ok_pi segs VAL E ss_de
                 (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + A_dr_arm)) mem (seg_rom segs)))).
  { rewrite restrict_mkst_fx. unfold ss_de. apply pa_entry_st_ok_full.
    - unfold de_sr. rewrite HE.
      apply regs_ok_pin; [apply regs_ok_pin; [apply regs_ok_Eimg_Ereg | intros X; discriminate X |]
                         | intros X; discriminate X |]; rewrite <- HE.
      + rewrite (KR0 23%bv ltac:(cbv; tauto)), C23. apply bv_eq. fold (U E (SOff (A_HI 74) 0)).
        rewrite (U_img_atom E HEI (A_HI 74)) by (unfold A_HI, A_TEXT, A_LIM; lia).
        rewrite (proj1 (de_hi (rc := rc))). unfold w64. apply unsigned_lit_small. unfold HI_G_NSRC; lia.
      + rewrite (KR0 18%bv ltac:(cbv; tauto)), C18. apply bv_eq. fold (U E (SOff (A_HI 75) 0)).
        rewrite (U_img_atom E HEI (A_HI 75)) by (unfold A_HI, A_TEXT, A_LIM; lia).
        rewrite (proj1 (proj2 (de_hi (rc := rc)))). unfold w64. apply unsigned_lit_small. unfold HI_G_SRC; lia.
    - vm_compute. reflexivity.
    - unfold de_regions. repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
        cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      + rewrite U9. split; [lia|]. split; [lia|]. split; [|constructor].
        intros o Ho. exact (HAWR o ltac:(lia)).
      + rewrite U21. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
        constructor; [|constructor].
        apply (chunk_ok_val segs E _ HA 0 4 (SOff 32 0) (hs_fd h));
          [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
        rewrite Z.add_0_r. exact Mfd.
      + rewrite UO7. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
        constructor; [|constructor].
        apply (chunk_ok_val segs E _ (rg_nsrc fr_RG) 0 4 (SOff 33 0) (Z.of_nat (length (lm_es m))));
          [cbn [sv_denot]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
        rewrite Z.add_0_r. exact Mnsrc.
      + rewrite UO8. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
        constructor; [|constructor].
        apply (chunk_ok_val segs E _ (rg_src fr_RG) 0 8 (SOff 34 0) (lm_G m));
          [cbn [sv_denot]; rewrite E34, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
        rewrite Z.add_0_r. exact Msrc.
    - unfold de_regions. cbn [pairwise_disjoint all_disjoint]. unfold extent_disjoint.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite U9, U21, UO7, UO8.
      repeat split; lia.
    - split; [|split; [exact I | exact I]].
      cbn [de_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
      rewrite E9, E21, E26, E32, E33, !unsigned_lit_small by (unfold SB; lia).
      rewrite !Z.pow_0_r, !Z.mod_1_r. change (2 ^ 3) with 8.
      unfold SB. repeat match goal with |- _ /\ _ => split end; lia. }
  assert (EH74 : ew E 354 = Z_to_bv 64 HI_G_NSRC)
    by (subst E; rewrite Eimg_img by (unfold A_TEXT, A_LIM; lia); exact (f_equal (Z_to_bv 64) (proj1 de_hi))).
  assert (EH75 : ew E 355 = Z_to_bv 64 HI_G_SRC)
    by (subst E; rewrite Eimg_img by (unfold A_TEXT, A_LIM; lia); exact (f_equal (Z_to_bv 64) (proj1 (proj2 de_hi)))).
  clear HE.
  assert (HBx : U E de_Bx = SHADOW_OFF)
    by (unfold de_Bx; rewrite (U_atom E 26 SB E26) by (unfold SB; lia); reflexivity).
  assert (SHOK : sh_ok segs de_Bx de_SH E (mrestrict (w_H W) mem)).
  { constructor; [|constructor].
    eapply shent_ok_of_range.
    - apply (azs_range_addressable_x B ARx LAWS ly3 S3 Hp3 W mem md HA 4 HAR).
      destruct HZS as (zr & Hzin & Hz8 & Hzlo & Hzhi). unfold ASRC in Hzhi.
      exists zr. refine (conj Hzin (conj Hz8 _)). lia.
    - exact HBx.
    - rewrite (U_atom E 21 _ E21) by lia. reflexivity.
    - lia.
    - lia.
    - intros x Hx. unfold SHADOW_OFF in *. lia. }
  unfold cfg_at. change (w64 (fr_B0 + fr_arm 2)) with (Z_to_bv 64 (BASE + A_dr_arm)).
  paj_run_tok_x RUNR HS HJ SHOK de_span.
  { de_awr U9. }
  rename HFr into HFr1, HG0 into HG1. clear HF.
  assert (K1 : forall a, 0 <= a < 2 ^ 64 -> ~ (lf_F cx + DR_N <= a < lf_F cx + DR_N + 8) ->
      aview segs (w_H W) (ms_mem ms) a = aview segs (w_H W) mem a)
    by (intros a Ha Hna; apply (aview_kept_out _ _ _ _ _ HFr1 a Ha); de_nowr U9 Hna).
  assert (P1 : forall a, apresent (w_H W) mem a -> apresent (w_H W) (ms_mem ms) a)
    by (intros a Hpo; exact (de_pres_grows W _ _ a HG1 Hpo)).
  clear HFr1 HG1.
  lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
    assert (S33 : bv_signed (sv_denot Ev (SOff 33 0)) = Z.of_nat (length (lm_es m)))
      by (assert (U33 : U Ev (SOff 33 0) = Z.of_nat (length (lm_es m)))
            by (apply U_atom; [rewrite !ew_ewset_other by lia; exact E33 | lia]);
          unfold U in U33; rewrite bv_signed_small; [exact U33 | rewrite U33; lia]);
    assert (S0 : bv_signed (sv_denot Ev (SLit 0)) = 0) by reflexivity
  end.
  psrr_branch_tok RUNR de_BR HS SHOK de_span.
  - cbn [branch_taken] in Hc. rewrite bv_lts_signed, S0, S33 in Hc.
    apply Bool.negb_true_iff, Z.ltb_ge in Hc.
    assert (Hn0 : length (lm_es m) = 0%nat) by lia.
    paj_run_to_tok_x RUNTOR HS HJ SHOK de_span A_dr_nf.
    { de_awr U9. }
    assert (K2 : forall a, 0 <= a < 2 ^ 64 -> ~ (lf_F cx + DR_N <= a < lf_F cx + DR_N + 8) ->
        aview segs (w_H W) (ms_mem ms0) a = aview segs (w_H W) mem a)
      by (intros a Ha Hna; rewrite (aview_kept_out _ _ _ _ _ HFr a Ha) by (de_nowr U9 Hna); exact (K1 a Ha Hna)).
    assert (WK : forall a, writable_at segs (arm W mem) a -> writable_at segs (arm W (ms_mem ms0)) a).
    { intros a Hw. apply (writable_kept (w_H W) mem (ms_mem ms0) a); [|exact Hw].
      intros Hpo. exact (de_pres_grows W _ _ a HG0 (P1 a Hpo)). }
    assert (KEEP : forall a, 0 <= a < 2 ^ 64 -> ~ (lf_F cx + DR_N <= a < lf_F cx + DR_N + 8) ->
        abyte_kept W mem W (ms_mem ms0) a)
      by (intros a Ha Hna; split; [exact (K2 a Ha Hna) | apply WK]).
    destruct (de_carry cx W mem (ms_mem ms0) md ly3 S3 Hp3 fpos m HAR Hfin (eq_sym Hnlen) ltac:(lia)
                HFR HMOD HIN HRV HROM KEEP WK) as (HFR2 & HMOD2 & HIN2 & HRV2 & HROM2).
    pose proof (de_flag_kept cx W mem (ms_mem ms0) md ly3 S3 Hp3 fpos HAR Hfin ltac:(lia) KEEP HFL) as HFL2.
    pose proof (st_ok_pi_region_nth _ _ _ 0 _ HS eq_refl) as RG0. cbn [ms_mem restrict] in RG0.
    assert (SVN : sv8 W (ms_mem ms0) (lf_F cx + DR_N) (c_n cx - dr_k' cx m)).
    { unfold sv8, DR_N.
      lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
        apply (field_of_region Ev _ 9%nat (lf_F cx) _ _ _ _ _ 144 8%N (SOff 29 0) (c_n cx - dr_k' cx m) RG0) end.
      - rewrite !ew_ewset_other by lia. exact U9.
      - left. reflexivity.
      - cbn [sv_denot]. rewrite !ew_ewset_other by lia. rewrite E29, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
      - zside.
      - zside. }
    lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
      assert (HAE2 : env_agree 32 (Ereg regs (de_extra (hs_fd h) (Z.of_nat (length (lm_es m))) (lm_G m))) Ev)
        by (split; [intros q Hq; rewrite !ew_ewset_other by lia; exact (proj1 HAE q Hq)
                   | rewrite !ed_ewset; exact (proj2 HAE)]) end.
    pose proof (regs_kept_of_st_ok_pi _ _ _ regs _ DE_KEPT HS HAE2 ltac:(vm_compute; reflexivity)) as KR.
    cbn [ms_regs restrict] in KR.
    assert (KK : forall rr, In rr DE_KEPT -> getr (ms_regs ms0) rr = getr regsD rr).
    { intros rr Hrr. rewrite (KR rr Hrr). apply KR0. cbv [DE_KEPT In] in Hrr.
      repeat (destruct Hrr as [<- | Hrr]; [cbv; tauto|]). destruct Hrr. }
    prreg HS (18%bv : bv 5) Q18. prreg HS (23%bv : bv 5) Q23. rewrite EH75 in Q18. rewrite EH74 in Q23.
    assert (LB : lregs_base cx t FF (ms_regs ms0)).
    { split; [|split; [rewrite (KK 27%bv ltac:(cbv; tauto)); exact R27 | exact Ht]].
      split; [rewrite (KK 2%bv ltac:(cbv; tauto)); exact C2|].
      split; [rewrite (KK 8%bv ltac:(cbv; tauto)); exact C8|].
      split; [rewrite (KK 9%bv ltac:(cbv; tauto)); exact C9|].
      split; [exact Q18|].
      split; [rewrite (KK 19%bv ltac:(cbv; tauto)); exact C19|].
      split; [rewrite (KK 20%bv ltac:(cbv; tauto)); exact C20|].
      split; [exact Q23|].
      split; [rewrite (KK 24%bv ltac:(cbv; tauto)); exact C24|].
      split; [rewrite (KK 25%bv ltac:(cbv; tauto)); exact C25|].
      split; [rewrite (KK 26%bv ltac:(cbv; tauto)); exact C26|].
      split; [rewrite (KK 3%bv ltac:(cbv; tauto)); exact C3|].
      rewrite (KK 4%bv ltac:(cbv; tauto)); exact C4. }
    assert (L28 : getr (ms_regs ms0) 28 = w64 (c_p cx + dr_k' cx m))
      by (rewrite (KK 28%bv ltac:(cbv; tauto)); exact R28).
    pmkst HS. apply SRr_ret.
    right.
      lazymatch goal with |- context [mkCfg (mkst ?r _ ?mm _) ?d] => exists r, mm, d end.
      split; [reflexivity|]. split; [exact HROM2|].
      exists own, ly3, S3, Hp3, k, m, fpos.
      split; [exact HJ|]. split; [exact Hown|]. split; [exact HFR2|]. split; [exact HFL2|]. split; [exact HMOD2|].
      split; [exact HIN2|]. split; [exact HRV2|]. split; [exact HSEP|]. split; [exact HLS|]. split; [exact HNP|]. split; [exact HRI|].
      split; [exact LB|]. split; [exact (conj Hk (conj HO Hop))|]. split; [exact L28|]. split; [exact SVN|].
      exists si, h. split; [exact HPICK|]. intros q Hq. rewrite Hn0 in Hq. cbn in Hq. lia.
  - cbn [branch_taken] in Hc. rewrite bv_lts_signed, S0, S33 in Hc.
    apply Bool.negb_false_iff, Z.ltb_lt in Hc.
    paj_run_to_tok_x RUNTOR HS HJ SHOK de_span A_dr_loop.
    { de_awr U9. }
    assert (K2 : forall a, 0 <= a < 2 ^ 64 -> ~ (lf_F cx + DR_N <= a < lf_F cx + DR_N + 8) ->
        aview segs (w_H W) (ms_mem ms0) a = aview segs (w_H W) mem a)
      by (intros a Ha Hna; rewrite (aview_kept_out _ _ _ _ _ HFr a Ha) by (de_nowr U9 Hna); exact (K1 a Ha Hna)).
    assert (WK : forall a, writable_at segs (arm W mem) a -> writable_at segs (arm W (ms_mem ms0)) a).
    { intros a Hw. apply (writable_kept (w_H W) mem (ms_mem ms0) a); [|exact Hw].
      intros Hpo. exact (de_pres_grows W _ _ a HG0 (P1 a Hpo)). }
    assert (KEEP : forall a, 0 <= a < 2 ^ 64 -> ~ (lf_F cx + DR_N <= a < lf_F cx + DR_N + 8) ->
        abyte_kept W mem W (ms_mem ms0) a)
      by (intros a Ha Hna; split; [exact (K2 a Ha Hna) | apply WK]).
    destruct (de_carry cx W mem (ms_mem ms0) md ly3 S3 Hp3 fpos m HAR Hfin (eq_sym Hnlen) ltac:(lia)
                HFR HMOD HIN HRV HROM KEEP WK) as (HFR2 & HMOD2 & HIN2 & HRV2 & HROM2).
    pose proof (de_flag_kept cx W mem (ms_mem ms0) md ly3 S3 Hp3 fpos HAR Hfin ltac:(lia) KEEP HFL) as HFL2.
    pose proof (st_ok_pi_region_nth _ _ _ 0 _ HS eq_refl) as RG0. cbn [ms_mem restrict] in RG0.
    assert (SVN : sv8 W (ms_mem ms0) (lf_F cx + DR_N) (c_n cx - dr_k' cx m)).
    { unfold sv8, DR_N.
      lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
        apply (field_of_region Ev _ 9%nat (lf_F cx) _ _ _ _ _ 144 8%N (SOff 29 0) (c_n cx - dr_k' cx m) RG0) end.
      - rewrite !ew_ewset_other by lia. exact U9.
      - left. reflexivity.
      - cbn [sv_denot]. rewrite !ew_ewset_other by lia. rewrite E29, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
      - zside.
      - zside. }
    lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
      assert (HAE2 : env_agree 32 (Ereg regs (de_extra (hs_fd h) (Z.of_nat (length (lm_es m))) (lm_G m))) Ev)
        by (split; [intros q Hq; rewrite !ew_ewset_other by lia; exact (proj1 HAE q Hq)
                   | rewrite !ed_ewset; exact (proj2 HAE)]) end.
    pose proof (regs_kept_of_st_ok_pi _ _ _ regs _ DE_KEPT HS HAE2 ltac:(vm_compute; reflexivity)) as KR.
    cbn [ms_regs restrict] in KR.
    assert (KK : forall rr, In rr DE_KEPT -> getr (ms_regs ms0) rr = getr regsD rr).
    { intros rr Hrr. rewrite (KR rr Hrr). apply KR0. cbv [DE_KEPT In] in Hrr.
      repeat (destruct Hrr as [<- | Hrr]; [cbv; tauto|]). destruct Hrr. }
    prreg HS (18%bv : bv 5) Q18. prreg HS (23%bv : bv 5) Q23. rewrite EH75 in Q18. rewrite EH74 in Q23.
    assert (LB : lregs_base cx t FF (ms_regs ms0)).
    { split; [|split; [rewrite (KK 27%bv ltac:(cbv; tauto)); exact R27 | exact Ht]].
      split; [rewrite (KK 2%bv ltac:(cbv; tauto)); exact C2|].
      split; [rewrite (KK 8%bv ltac:(cbv; tauto)); exact C8|].
      split; [rewrite (KK 9%bv ltac:(cbv; tauto)); exact C9|].
      split; [exact Q18|].
      split; [rewrite (KK 19%bv ltac:(cbv; tauto)); exact C19|].
      split; [rewrite (KK 20%bv ltac:(cbv; tauto)); exact C20|].
      split; [exact Q23|].
      split; [rewrite (KK 24%bv ltac:(cbv; tauto)); exact C24|].
      split; [rewrite (KK 25%bv ltac:(cbv; tauto)); exact C25|].
      split; [rewrite (KK 26%bv ltac:(cbv; tauto)); exact C26|].
      split; [rewrite (KK 3%bv ltac:(cbv; tauto)); exact C3|].
      rewrite (KK 4%bv ltac:(cbv; tauto)); exact C4. }
    assert (L28 : getr (ms_regs ms0) 28 = w64 (c_p cx + dr_k' cx m))
      by (rewrite (KK 28%bv ltac:(cbv; tauto)); exact R28).
    pmkst HS. apply SRr_ret.
    prreg HS (10%bv : bv 5) Q10. prreg HS (11%bv : bv 5) Q11. prreg HS (12%bv : bv 5) Q12.
    prreg HS (13%bv : bv 5) Q13. prreg HS (22%bv : bv 5) Q22.
    rewrite E34 in Q10, Q22. rewrite E33 in Q11. rewrite E32 in Q12.
    assert (G8 : 0 <= lm_G m / 8 /\ 8 * (lm_G m / 8) <= lm_G m)
      by (split; [apply Z.div_pos; lia | apply Z.mul_div_le; lia]).
    assert (USH : U E (SAlu ALU_ADD (SOff 26 0) (SAlu ALU_SRL (SOff 34 0) (SLit 3))) = SB + lm_G m / 8).
    { rewrite !U_SAlu, (U_atom E 26 SB E26), (U_atom E 34 _ E34), U_lit by (unfold SB; lia). cbn [zalu_raw].
      change (Z.land 3 63) with 3. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8. unfold zcanon, M64.
      rewrite (Z.mod_small (lm_G m / 8)) by lia. rewrite Z.mod_small by (unfold SB; lia). reflexivity. }
    assert (Hsd : sv_denot E (SAlu ALU_ADD (SOff 26 0) (SAlu ALU_SRL (SOff 34 0) (SLit 3))) =
                  alu64 ALU_ADD (ew E 26) (alu64 ALU_SRL (ew E 34) (Z_to_bv 64 3)))
      by (cbn [sv_denot]; rewrite !Z.add_0_r, !Z_to_bv_bv_unsigned; reflexivity).
    rewrite <- Hsd in Q13.
    left. exists (length (lm_es m)).
      lazymatch goal with |- context [mkCfg (mkst ?r _ ?mm _) ?d] => exists r, mm, d end.
      split; [reflexivity|]. split; [exact HROM2|].
      exists own, ly3, S3, Hp3, k, m, fpos.
      split; [exact HJ|]. split; [exact Hown|]. split; [exact HFR2|]. split; [exact HFL2|]. split; [exact HMOD2|].
      split; [exact HIN2|]. split; [exact HRV2|]. split; [exact HSEP|]. split; [exact HLS|]. split; [exact HNP|]. split; [exact HRI|].
      split; [exact LB|]. split; [exact (conj Hk (conj HO Hop))|]. split; [exact L28|]. split; [exact SVN|].
      split.
      { exists si, h. split; [exact HPICK|].
        split; [rewrite (KK 21%bv ltac:(cbv; tauto)); exact R21|].
        split; [exact Q12|]. intros q Hq. lia. }
      split; [lia|]. split; [lia|].
      split; [rewrite Q10; f_equal; unfold AENT; lia|].
      split; [rewrite Q22; f_equal; unfold AENT; lia|].
      split; [rewrite Q11; f_equal; lia|].
      rewrite Q13. apply bv_eq. fold (U E (SAlu ALU_ADD (SOff 26 0) (SAlu ALU_SRL (SOff 34 0) (SLit 3)))).
      rewrite USH. unfold w64. rewrite unsigned_lit_small by (unfold SB; lia). lia.
Qed.

(* dr_nf_join at R *)
Lemma dr_nf_joinR : forall cx Hpe t W c,
  lf_base_x B MT XM_LIB RLO RHI fr_live_pre LIBROOM NP G_fr ARx cx Hpe ->
  DSTR A_dr_nf cx Hpe t (lregs_nf cx t) W c ->
  SRr segs W c (DSTR A_dr_join cx Hpe (t + 1) (lregs_join cx t)).
Proof.
  intros cx Hpe t W c HB (regs & mem & md & -> & HROM &
    (own & ly3 & S3 & Hp3 & k & m & fpos & HJ & -> & HFR & HFL & HMOD & HIN & HRV & HSEP & HLS & HNP & HRI & HR)).
  destruct HR as (((R2 & R8 & R9 & R18 & R19 & R20 & R23 & R24 & R25 & R26 & R3 & R4) & R27 & Ht)
    & Hatop & R28 & SVN & (si & h & Hpick & Hnom)).
  pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs.
  pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
  pose proof Hatop as (Hk0 & _ & _).
  assert (Hk' : 0 <= dr_k' cx m <= c_n cx)
    by (unfold dr_k'; destruct (Z.ltb_spec (lm_k m + 1) (c_n cx)); lia).
  destruct (dr_nf_entry W regs mem R26) as [HS SHOK].
  remember (Eimg (Ereg regs [])) as E eqn:HE.
  assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
  assert (E28 : ew E 28 = Z_to_bv 64 (c_p cx + dr_k' cx m))
    by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia);
        rewrite (ew_Ereg_nat regs _ 28 28%bv eq_refl); exact R28).
  assert (HAE : env_agree 32 (Ereg regs []) E)
    by (rewrite HE; split; [intros n Hn; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
  clear HE.
  unfold cfg_at. change (w64 (fr_B0 + A_dr_nf)) with (Z_to_bv 64 (BASE + A_dr_nf)).
  paj_run_to_tok_x RUNTOR HS HJ SHOK DRspan A_dr_join.
  { apply awr_ok_x_nil. }
  dr_meq HF Em.
  pose proof (regs_kept_of_st_ok_pi _ _ _ regs _ DR_KEPT HS HAE ltac:(vm_compute; reflexivity)) as KR.
  cbn [ms_regs restrict] in KR.
  prreg HS (25%bv : bv 5) Q25. rewrite E28 in Q25.
  pmkst HS. rewrite Em in *.
  apply SRr_ret.
  lazymatch goal with |- context [mkCfg (mkst ?r _ ?mm _) ?d] => exists r, mm, d end.
  split; [reflexivity|]. split; [exact HROM|].
  exists [(1, fpos)], ly3, S3, Hp3, k, (dr_skip m (dr_k' cx m)), fpos.
  split; [exact HJ|]. split; [reflexivity|]. split; [exact HFR|]. split; [exact HFL|]. split; [exact HMOD|].
  split; [exact HIN|]. split; [exact HRV|]. split; [exact HSEP|].
  split; [apply LS_drain_skip; exact HLS|]. split; [exact HNP|].
  split; [apply (RI_drain_skip cx t m si h HRI Hatop Hpick); left; exact Hnom|].
  split; [rewrite (KR 2%bv ltac:(cbv; tauto)); exact R2|].
  split; [rewrite (KR 8%bv ltac:(cbv; tauto)); exact R8|].
  split; [rewrite (KR 9%bv ltac:(cbv; tauto)); exact R9|].
  split; [rewrite (KR 18%bv ltac:(cbv; tauto)); exact R18|].
  split; [rewrite (KR 19%bv ltac:(cbv; tauto)); exact R19|].
  split; [rewrite (KR 20%bv ltac:(cbv; tauto)); exact R20|].
  split; [rewrite (KR 23%bv ltac:(cbv; tauto)); exact R23|].
  split; [rewrite (KR 24%bv ltac:(cbv; tauto)); exact R24|].
  split; [rewrite (KR 26%bv ltac:(cbv; tauto)); exact R26|].
  split; [rewrite (KR 3%bv ltac:(cbv; tauto)); exact R3|].
  split; [rewrite (KR 4%bv ltac:(cbv; tauto)); exact R4|].
  split; [rewrite (KR 27%bv ltac:(cbv; tauto)); exact R27|].
  split; [exact Ht|].
  split; [rewrite Q25; reflexivity|].
  split; [exact SVN|]. exact Hk'.
Qed.

(* ---- (5)'s journal kit at R ---- *)
(* dr_afn_pre_at at R *)
Lemma dr_afn_pre_atR : forall cx Hpe ly3 S3 Hp3 fpos k (W : world segs) mem md regs STK1,
  lf_base_x B MT XM_LIB RLO RHI fr_live_pre LIBROOM NP G_fr ARx cx Hpe ->
  ajournal_gx_xR segs B PST ARx R G_fr 0 [] LLVMF_STK (spZ (c_regs cx)) (lf_FP fr_FP cx)
    (c_ly cx) (c_S cx) Hpe (c_W cx) (c_mem cx) (c_md cx) [(1, fpos)] ly3 S3 Hp3 W mem md k ->
  aframe_at cx false (frame_addr ly3 1 fpos) W mem ->
  spZ regs = lf_F cx -> YK0s.ret_ok (getr regs 1) -> 4096 <= raZ regs ->
  getr regs 3 = w64 (as_gp B) -> getr regs 4 = w64 (as_tp B) -> getr regs 8 = getr (c_regs cx) 2 ->
  0 <= STK1 -> STK1 + 352 <= LLVMF_STK ->
  exists ch, afn_pre_x segs B ARx STK1 ly3 S3 Hp3 W regs mem md ch.
Proof.
  intros cx Hpe ly3 S3 Hp3 fpos k W mem md regs STK1 HB HJ HFR Hsp Hret Hra4 Hgp Htp Hs0 HSTK0 HSTKb.
  destruct HB as (_ & HPRE).
  assert (HPREE : afn_pre_x segs B ARx LLVMF_STK (c_ly cx) (c_S cx) Hpe (c_W cx) (c_regs cx) (c_mem cx) (c_md cx) [])
    by (unfold fr_lib_pre_cf_x in HPRE; tauto).
  pose proof HPREE as (HAR0 & Hra0 & Hra40 & Hgp0 & Htp0 & Hstk0 & Hpres0 & Hch0 & HQT0).
  pose proof Hstk0 as (Hal16 & Hslo0 & Hceil0 & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
  destruct (ajournal_gx_inner_xR segs B PST ARx G_fr 0 [] LLVMF_STK (spZ (c_regs cx)) (lf_FP fr_FP cx)
    (c_ly cx) (c_S cx) Hpe (c_W cx) (c_mem cx) (c_md cx) [(1, fpos)] ly3 S3 Hp3 W mem md k HJ) as (memS & HJ0 & HSG).
  rewrite !Z.add_0_r in HJ0.
  set (sp0 := spZ (c_regs cx)) in *.
  assert (HF32 : lf_F cx = sp0 - 320 - (sp0 - 320) mod 32) by reflexivity.
  pose proof (Z.mod_pos_bound (sp0 - 320) 32 ltac:(lia)) as Hmb.
  assert (Ho16 : (lf_F cx - sp0) mod 16 = 0).
  { rewrite HF32.
    replace (sp0 - 320 - (sp0 - 320) mod 32 - sp0) with (- (320 + (sp0 - 320) mod 32)) by lia.
    assert (H32 : (sp0 - 320) mod 32 = 0 \/ (sp0 - 320) mod 32 = 16).
    { pose proof (Z.mod_divide (sp0 - 320) 16 ltac:(lia)) as _.
      assert (E16 : (sp0 - 320) mod 16 = 0)
        by (replace (sp0 - 320) with (sp0 + (-20) * 16) by lia; rewrite Z.mod_add by lia; exact Hal16).
      pose proof (Z.div_mod ((sp0 - 320) mod 32) 16 ltac:(lia)) as D.
      assert (E2 : ((sp0 - 320) mod 32) mod 16 = 0)
        by (rewrite <- Znumtheory.Zmod_div_mod by (try lia; exists 2; reflexivity); exact E16).
      rewrite E2, Z.add_0_r in D.
      assert (Hq : (sp0 - 320) mod 32 / 16 = 0 \/ (sp0 - 320) mod 32 / 16 = 1) by lia.
      destruct Hq as [Hq | Hq]; rewrite Hq in D; lia. }
    destruct H32 as [H32 | H32]; rewrite H32; reflexivity. }
  assert (HoNeg : lf_F cx - sp0 <= 0) by (rewrite HF32; lia).
  assert (HoBud : STK1 - (lf_F cx - sp0) <= LLVMF_STK) by (rewrite HF32; lia).
  pose proof (aview_above_of_journal_xR (PI := PB_fr) B PST ARx LLVMF_STK sp0 (lf_FP fr_FP cx)
    (c_ly cx) (c_S cx) Hpe (c_W cx) memS (c_md cx) [(1, fpos)] ly3 S3 Hp3 W mem md k HJ0) as HAB.
  pose proof HFR as (HSV & _).
  assert (Hra8 : rdword (aview segs (w_H W) mem) (sp0 - 8) = Some (bv_unsigned (getr (c_regs cx) 1))).
  { apply (rdword_of_val_mem segs (w_H W) mem); [exact (HSV 8 1 ltac:(left; reflexivity)) |].
    pose proof (bv_unsigned_in_range 64 (getr (c_regs cx) 1)) as Hr.
    change (bv_modulus 64) with (2 ^ 64) in Hr. lia. }
  assert (Hs016 : rdword (aview segs (w_H W) mem) (sp0 - 16) = Some (bv_unsigned (getr (c_regs cx) 8))).
  { apply (rdword_of_val_mem segs (w_H W) mem); [exact (HSV 16 8 ltac:(right; left; reflexivity)) |].
    pose proof (bv_unsigned_in_range 64 (getr (c_regs cx) 8)) as Hr.
    change (bv_modulus 64) with (2 ^ 64) in Hr. lia. }
  clear Hpres0.
  assert (HTOPeq : ly_top ly3 = ly_top (c_ly cx)).
  { pose proof HJ0 as (_ & Hly & _). pose proof Hly as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & _). exact Etop. }
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  assert (Hsp8 : sp0 mod 8 = 0).
  { assert (Hq : sp0 = 16 * (sp0 / 16)) by (pose proof (Z.div_mod sp0 16 ltac:(lia)); lia).
    rewrite Hq. replace (16 * (sp0 / 16)) with ((2 * (sp0 / 16)) * 8) by ring. apply Z_mod_mult. }
  assert (HCH : exists ch, achain ly3 (aview segs (w_H W) mem) (lf_F cx) sp0 ch).
  { destruct (Z_lt_ge_dec sp0 (ly_top (c_ly cx) - 16)) as [Hlt | Hge].
    - exists ((sp0, bv_unsigned (getr (c_regs cx) 1), bv_unsigned (getr (c_regs cx) 8)) :: []).
      apply (achain_ly_top (c_ly cx) ly3 _ _ _ _ ltac:(exact HTOPeq)).
      eapply (achain_push (c_ly cx) (aview segs (w_H (c_W cx)) (c_mem cx)) (aview segs (w_H W) mem)
        sp0 (bv_unsigned (getr (c_regs cx) 8)) (bv_unsigned (getr (c_regs cx) 1)) [] (lf_F cx));
        [ exact Hch0 | lia
        | intros a Ha; rewrite (HAB a ltac:(lia)); apply HSG; rewrite unsigned_lit_small by lia; intros HGa;
          pose proof (inG_low segs B pa_segs_low G_fr a HG HGa); lia
        | exact Hra8 | exact Hs016
        | unfold raZ in Hra40; lia | lia | exact Hsp8 | exact Hlt | rewrite HF32; lia ].
    - exists []. left. split; [right; left; rewrite HTOPeq; lia | reflexivity]. }
  destruct HCH as (ch & HCH).
  exists ch.
  eapply (afn_pre_x_atR segs B PST ARx LLVMF_STK sp0 (lf_FP fr_FP cx) (c_ly cx) (c_S cx) Hpe (c_W cx) memS (c_md cx)
    [(1, fpos)] ly3 S3 Hp3 W mem md k regs STK1 (lf_F cx - sp0) _ HJ0);
    [ rewrite Hsp; lia | exact Ho16 | exact HoNeg | exact HSTK0 | exact HoBud | exact Hret | exact Hra4
    | exact Hgp | exact Htp | ].
  rewrite Hsp. replace (s0Z regs) with sp0 by (unfold s0Z, sp0, spZ; rewrite Hs0; reflexivity).
  exact HCH.
Qed.
(* dr_stkr at R *)
Lemma dr_stkrR : forall cx Hpe fpos ly S Hp (W : world segs) mem md k,
  lf_base_x B MT XM_LIB RLO RHI fr_live_pre LIBROOM NP G_fr ARx cx Hpe ->
  ajournal_gx_xR segs B PST ARx R G_fr 0 [] LLVMF_STK (spZ (c_regs cx)) (lf_FP fr_FP cx)
    (c_ly cx) (c_S cx) Hpe (c_W cx) (c_mem cx) (c_md cx) [(1, fpos)] ly S Hp W mem md k ->
  forall a, lf_F cx <= a < ly_top ly -> aview segs (w_H W) mem a <> None.
Proof.
  intros cx Hpe fpos ly S Hp W mem md k HB HJ a Ha.
  pose proof dr_ceil_lo as HCL.
  destruct HB as (_ & HPRE).
  pose proof HPRE as (HFNP & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & STKR & _).
  pose proof HFNP as (_ & _ & _ & _ & _ & Hstk & _).
  pose proof Hstk as (Hal16 & _ & Hceil & Hslo & Hshi & H47 & _ & Htop & Htop2).
  unfold LLVMF_STK in Hslo.
  destruct (ajournal_gx_inner_xR segs B PST ARx G_fr 0 [] LLVMF_STK (spZ (c_regs cx)) (lf_FP fr_FP cx)
    (c_ly cx) (c_S cx) Hpe (c_W cx) (c_mem cx) (c_md cx) [(1, fpos)] ly S Hp W mem md k HJ) as (memS & HJ0 & HSG).
  rewrite !Z.add_0_r in HJ0.
  pose proof HJ0 as (_ & HLY & _ & _ & _ & _ & _ & _ & F1 & _ & _ & _ & _ & Hpres & _).
  assert (Etop : ly_top ly = ly_top (c_ly cx)) by (pose proof HLY as (_ & _ & _ & _ & _ & _ & _ & _ & X & _); exact X).
  pose proof (Z.mod_pos_bound (spZ (c_regs cx) - 320) 32 ltac:(lia)) as HFm.
  assert (HFb : spZ (c_regs cx) - 352 < lf_F cx) by (unfold lf_F; lia).
  destruct (Z_lt_le_dec a (spZ (c_regs cx))) as [Hlt | Hge].
  - apply aview_some_of_apresent. apply Hpres. unfold LLVMF_STK. lia.
  - rewrite (F1 a ltac:(lia) ltac:(lia)). rewrite HSG.
    + apply STKR. rewrite <- Etop. lia.
    + rewrite unsigned_lit_small by lia. intros HGa. pose proof (pa_segs_low a (proj1 (HG a HGa))).
      unfold kLowMemEnd in *. lia.
Qed.
(* dr_callZ at R: the callee's step is SRrG segs R and its journal is at R; the composition is
   W_journal_x.v ajournal_gx_sub_xR (R_trans) *)
Lemma dr_callZR : forall G W (regsc : bvmap 5 word) memc pc STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k STK1 FP1
  XO1 OUT1 (o : Z) raw ch1
  (K : alayout -> astate -> list Z -> world segs -> bvmap 5 word -> (word -> option byte) -> Model -> Prop),
  gx_ok segs B G ->
  ajournal_gx_xR segs B PST ARx R G 0 [] STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W memc mdc k ->
  spZ regsc = sp0 + o -> o <= 0 -> STK1 - o <= STK ->
  0 <= XO1 -> o + XO1 <= 0 -> (forall a, inFP OUT1 a -> sp0 - STK <= a < sp0) ->
  getr regsc 1 = raw ->
  afn_pre_x segs B ARx STK1 lyc Sc Hpc W regsc memc mdc ch1 ->
  SRrG segs R W (mkCfg (mkst regsc pc memc (seg_rom segs)) mdc)
   (fun W2 c2 => exists ly2 S2 Hp2 regs2 mem2 md2 k1,
    c2 = mkCfg (mkst regs2 raw mem2 (seg_rom segs)) md2 /\
    ajournal_gx_xR segs B PST ARx R G XO1 OUT1 STK1 (spZ regsc) FP1 lyc Sc Hpc W memc mdc [] ly2 S2 Hp2 W2 mem2 md2 k1 /\
    aregs_preserved regsc regs2 /\ K ly2 S2 Hp2 W2 regs2 mem2 md2) ->
  (forall a, inFP FP1 a -> (inFP FP a /\ exists b n, In (b, n) (ablocks B lyc Sc) /\ b <= a < b + req_size n) \/
   in_tmp_block (ablocks B ly S) (ablocks B lyc Sc) a) ->
  SRrG segs R W (mkCfg (mkst regsc pc memc (seg_rom segs)) mdc)
  (fun W2 c2 => exists ly2 S2 Hp2 regs2 mem2 md2 k1,
   c2 = mkCfg (mkst regs2 raw mem2 (seg_rom segs)) md2 /\
   ajournal_gx_xR segs B PST ARx R G 0 [] STK sp0 FP ly S Hp W0 mem md own ly2 S2 Hp2 W2 mem2 md2 (k + k1) /\
   ajournal_gx_xR segs B PST ARx R G XO1 OUT1 STK1 (sp0 + o) FP1 lyc Sc Hpc W memc mdc [] ly2 S2 Hp2 W2 mem2 md2 k1 /\
   aregs_preserved regsc regs2 /\ K ly2 S2 Hp2 W2 regs2 mem2 md2).
Proof.
  intros G W regsc memc pc STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k STK1 FP1 XO1 OUT1 o raw ch1 K
    HGx HJ Hsp Hneg Hbud HXO HXO2 HOUT Hra HPRE Hcallee HF.
  eapply (SRrG_mono segs R); [exact Hcallee|].
  cbv beta. intros W2 c2 _ (ly2 & S2 & Hp2 & regs2 & mem2 & md2 & k1 & -> & HJ1 & HP & HK).
  exists ly2, S2, Hp2, regs2, mem2, md2, k1. split; [reflexivity|].
  rewrite Hsp in HJ1.
  split; [| split; [exact HJ1 | split; [exact HP | exact HK]]].
  change own with ([] ++ own).
  pose proof HJ as (HS0 & _).
  pose proof HPRE as (_ & _ & _ & _ & _ & (_ & HS1 & _) & _).
  eapply (ajournal_gx_sub_xR segs B PST ARx LAWS pa_segs_low R_trans);
    [exact HJ | exact HJ1 | lia | lia | lia | | exact HGx | exact HF].
  intros a Ha. left. exact (HOUT a Ha).
Qed.
(* dj_keep at R (a callee's journal at R) *)
Lemma dj_keepR : forall G XO OUT STK sp FP ly S Hp (W : world segs) mem md own ly' S' Hp' (W' : world segs) mem' md' k a,
  gx_ok segs B G ->
  ajournal_gx_xR segs B PST ARx R G XO OUT STK sp FP ly S Hp W mem md own ly' S' Hp' W' mem' md' k ->
  0 <= a < 2 ^ 64 -> ~ inG G a ->
  ((alloc_ceiling <= a /\ ~ (sp - STK <= a < sp + XO)) \/
   (sp <= a < sp + XO /\ ~ inFP OUT a) \/
   (exists p n, In (p, n) (ablocks B ly S) /\ In (p, n) (ablocks B ly' S') /\ p <= a < p + req_size n /\
      ~ inFP FP a) \/
   (in_img segs a /\ ~ Exists (in_zr a) (as_owned_static B) /\ ~ (as_errno B <= a < as_errno B + 4) /\
      fp_spares FP a) \/
   (exists cid pos, In (cid, pos) (frames S) /\
      (in_zr a (frame_rng ly (cid, pos)) \/ in_zr a (shadow_addr (frame_addr ly cid pos), fs_frame_bytes cid / 8)) /\
      ~ inFP FP a)) ->
  aview segs (w_H W') mem' a = aview segs (w_H W) mem a.
Proof.
  intros G XO OUT STK sp FP ly S Hp W mem md own ly' S' Hp' W' mem' md' k a HGx HJX Ha HnG Hc.
  pose proof HJX as (HS0 & HX0 & (memS & HJi & Hag) & Hout).
  assert (HmS : aview segs (w_H W) memS a = aview segs (w_H W) mem a).
  { apply (aview_gagree segs G _ _ _ a Hag). apply inGb_false. rewrite unsigned_lit_small by lia. exact HnG. }
  pose proof HJi as (_ & _ & _ & _ & _ & _ & _ & _ & F1 & F2 & F3 & F4 & _).
  destruct Hc as [(H1 & H2) | [(H1 & H2) | [(p & n & H1 & H2 & H3 & H4) | [(H1 & H2 & H3 & H4) | (cid & pos & H1 & H2 & H3)]]]].
  - rewrite (F1 a ltac:(lia) ltac:(lia)). exact HmS.
  - exact (Hout a H1 H2).
  - replace a with (p + (a - p)) in * by lia.
    rewrite (F2 p n (a - p) H1 H2 ltac:(lia) H4). exact HmS.
  - rewrite (F3 a H1 H2 H3 (HPST a H1) H4). exact HmS.
  - rewrite (F4 cid pos a H1 H2 H3). exact HmS.
Qed.
(* DLK at R *)
Definition DLKR (cx : lfcx) (Hpe : list Z) (t : Z) (m : lmod) (j si : nat) (h : hsrc) (fpos : Z) (ly3 : alayout) (S3 : astate) (Hp3 : list Z)
  (k : Z) : world segs -> config -> Prop :=
  fun W c => exists regs mem md,
  c = mkCfg (mkst regs (Z_to_bv 64 (SIGMA WS_pthread_mutex_lock)) mem (seg_rom segs)) md /\
  ajournal_gx_xR segs B PST ARx R G_fr 0 [] LLVMF_STK (spZ (c_regs cx)) (lf_FP fr_FP cx)
    (c_ly cx) (c_S cx) Hpe (c_W cx) (c_mem cx) (c_md cx) [(1, fpos)] ly3 S3 Hp3 W mem md k /\
  aframe_at cx true (frame_addr ly3 1 fpos) W mem /\ sv8 W mem (frame_addr ly3 1 fpos + 120) (flag_addr ly3 1 fpos) /\
  amodel_at B ly3 S3 W mem m /\
  ainput_at B cx ly3 S3 W mem /\ rom_view segs W mem /\ jt_rom W mem /\
  ablocks_sep B fr_FP cx m ly3 S3 /\ LSx cx t m ly3 S3 /\ NP S3 /\ RINV cx t m /\
  dr_at_op cx m /\ dr_pick cx m si h /\ (j < length (lm_es m))%nat /\
  re_fd (nth j (lm_es m) dr_e0) = hs_fd h /\ re_eof (nth j (lm_es m) dr_e0) = 0 /\
  sv8 W mem (lf_F cx + DR_N) (c_n cx - dr_k' cx m) /\ sv8 W mem (lf_F cx + DR_AT) 0 /\
  sv8 W mem (lf_F cx + 40) (rg_lock fr_RG) /\
  getr regs 1 = Z_to_bv 64 (BASE + A_dc_r1) /\ getr regs 10 = w64 (rg_lock fr_RG) /\
  getr regs 2 = w64 (lf_F cx) /\ getr regs 8 = getr (c_regs cx) 2 /\ getr regs 9 = w64 (lf_F cx) /\
  getr regs 18 = w64 HI_G_SRC /\ getr regs 19 = w64 (frame_addr ly3 1 fpos + 32) /\ getr regs 20 = w64 10 /\
  getr regs 23 = w64 HI_G_NSRC /\ getr regs 24 = w64 (SB + frame_addr ly3 1 fpos / 8) /\ getr regs 26 = w64 SB /\
  getr regs 3 = w64 (as_gp B) /\ getr regs 4 = w64 (as_tp B) /\ getr regs 27 = w64 t /\ 0 <= t < OPS_MAX /\
  getr regs 21 = w64 (rg_s fr_RG + ASRC * Z.of_nat si) /\ getr regs 22 = w64 (lm_G m + AENT * Z.of_nat j) /\
  getr regs 25 = w64 (c_p cx + dr_k' cx m).
(* dc_at at R *)
Definition dc_atR (cx : lfcx) (Hpe : list Z) (t : Z) (m : lmod) (j si : nat) (fpos FF pc : Z) (ly : alayout) (S : astate) (Hp : list Z)
  (mc : lmod) (held : bool) (A : Z) : world segs -> config -> Prop :=
  fun W c => exists regs mem md k,
    c = mkCfg (mkst regs (Z_to_bv 64 (BASE + pc)) mem (seg_rom segs)) md /\
    dc_regs cx t m j si FF regs /\
    ajournal_gx_xR segs B PST ARx R G_fr 0 [] LLVMF_STK (spZ (c_regs cx)) (lf_FP fr_FP cx)
      (c_ly cx) (c_S cx) Hpe (c_W cx) (c_mem cx) (c_md cx) [(1, fpos)] ly S Hp W mem md k /\
    frame_addr ly 1 fpos = FF /\
    aframe_at cx true FF W mem /\ sv8 W mem (FF + 120) (flag_addr ly 1 fpos) /\
    ainput_at B cx ly S W mem /\ rom_view segs W mem /\ jt_rom W mem /\
    sv8 W mem (lf_F cx + DR_N) (c_n cx - dr_k' cx m) /\ sv8 W mem (lf_F cx + DR_AT) A /\
    sv8 W mem (lf_F cx + 40) (rg_lock fr_RG) /\
    amodel_ne ly S W mem mc held /\ ablocks_sep B fr_FP cx mc ly S /\
    Forall (fun e => Z.of_nat (length (re_keys e)) <= re_nheld e) (lm_es mc).

(* dc_stA at R: pthread_mutex_lock's strict realization, lifted by aj_gx_entry_at_xR *)
Lemma dc_stAR : forall cx Hpe t m j si h fpos ly3 S3 Hp3 k W c,
  lf_base_x B MT XM_LIB RLO RHI fr_live_pre LIBROOM NP G_fr ARx cx Hpe ->
  DLKR cx Hpe t m j si h fpos ly3 S3 Hp3 k W c ->
  SRrG segs R W c (dc_atR cx Hpe t m j si fpos (frame_addr ly3 1 fpos) A_dc_r1 ly3 S3 Hp3 m true 0).
Proof.
  intros cx Hpe t m j si h fpos ly3 S3 Hp3 k W c HB
    (regs & mem & md & -> & HJ & HFR & HFL & HMOD & HIN & HRV & HROM & HSEP & HLS & HNP & HRI & Hatop & Hpick & Hj & Hfdj & Hef0 &
     SVN & S192 & S40 & Q1 & Q10 & R2 & R8 & R9 & R18 & R19 & R20 & R23 & R24 & R26 & R3 & R4 & R27 & Ht & R21 & R22 & R25).
  pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs.
  pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  pose proof dr_ceil_lo as HCL.
  assert (HAR : ARx ly3 S3 Hp3 W mem md) by (eapply ajournal_gx_AR_xR; exact HJ).
  pose proof HMOD as (Hlen4 & HSL & HREL & HOUT & HGONE & HLOCK & HWAKE & HNFD & HNFDW & HNFDr & HTUP & HLST & HLSTW).
  pose proof HB as (HAI & HPRE).
  pose proof HPRE as (HFNP & _ & _ & _ & Hnrng & Hnlen & _).
  assert (Hn26 : c_n cx < 2 ^ 26) by (destruct Hnrng as [(Hz & _) | (Hz & _)]; lia).
  pose proof HFNP as (_ & _ & _ & _ & _ & Hstk & _).
  pose proof Hstk as (Hal16 & _ & Hceil & Hslo & Hshi & H47 & _).
  unfold LLVMF_STK in Hslo.
  assert (HFb : spZ (c_regs cx) - 352 < lf_F cx <= spZ (c_regs cx) - 320).
  { unfold lf_F. pose proof (Z.mod_pos_bound (spZ (c_regs cx) - 320) 32 ltac:(lia)). lia. }
  assert (HF32 : lf_F cx mod 32 = 0).
  { unfold lf_F. rewrite Zminus_mod, Z.mod_mod, Z.sub_diag by lia. reflexivity. }
  pose proof (pal_env B TL) as ((HE0 & HE1) & _).
  set (sp0 := spZ (c_regs cx)) in *.
  set (F := lf_F cx) in *.
  set (FF := frame_addr ly3 1 fpos) in *.
  assert (Hsp : spZ regs = F) by (unfold spZ; rewrite R2; unfold w64; apply unsigned_lit_small; unfold DR_CEIL8 in *; lia).
  assert (VLK : rg_lock fr_RG = 0x5d8ac0) by reflexivity.
  pose proof HLOCK as (LK0 & LK4 & LK8 & LKW). unfold arm in LK0, LK4, LK8, LKW.

  assert (Ho16 : (F - sp0) mod 16 = 0).
  { assert (HF32' : F = sp0 - 320 - (sp0 - 320) mod 32) by reflexivity.
    pose proof (Z.mod_pos_bound (sp0 - 320) 32 ltac:(lia)) as Hmb.
    rewrite HF32'.
    replace (sp0 - 320 - (sp0 - 320) mod 32 - sp0) with (- (320 + (sp0 - 320) mod 32)) by lia.
    assert (H32 : (sp0 - 320) mod 32 = 0 \/ (sp0 - 320) mod 32 = 16).
    { assert (E16 : (sp0 - 320) mod 16 = 0)
        by (replace (sp0 - 320) with (sp0 + (-20) * 16) by lia; rewrite Z.mod_add by lia; exact Hal16).
      pose proof (Z.div_mod ((sp0 - 320) mod 32) 16 ltac:(lia)) as D.
      assert (E2 : ((sp0 - 320) mod 32) mod 16 = 0)
        by (rewrite <- Znumtheory.Zmod_div_mod by (try lia; exists 2; reflexivity); exact E16).
      rewrite E2, Z.add_0_r in D.
      assert (Hq : (sp0 - 320) mod 32 / 16 = 0 \/ (sp0 - 320) mod 32 / 16 = 1) by lia.
      destruct Hq as [Hq | Hq]; rewrite Hq in D; lia. }
    destruct H32 as [H32 | H32]; rewrite H32; reflexivity. }

  assert (HNOWN : forall a, rg_lock fr_RG <= a < rg_lock fr_RG + 12 -> ~ aowned B ly3 S3 a).
  { intros a Ha Ho. destruct (HG a (HGlock a Ha)) as (Hi & Hno & _).
    apply Hno. exact (proj1 (alx_owned_image _ _ _ LAWS ly3 S3 Hp3 W mem _ a HAR Hi) Ho). }
  assert (AVL : aview segs (w_H W) mem (rg_lock fr_RG) = Some 0).
  { pose proof (dj_av1 W mem (rg_lock fr_RG) 4%nat 0 LK0 ltac:(lia)) as HA.
    replace (YO0f.le_byte 0 4 0) with 0 in HA by (vm_compute; reflexivity). exact HA. }
  eapply (SRrG_bind segs R R_trans).
  { eapply (aj_gx_entry_at_xR B PST ARx LAWS R_trans WLE_R G_fr 0 [] ESTACK (SIGMA WS_pthread_mutex_lock)
      (fun a => rg_lock fr_RG + 4 <= a < rg_lock fr_RG + 8)
      (fun _ mem' => val_mem segs (mrestrict (w_H W) mem') (rg_lock fr_RG + 4) 4 16)
      W regs mem LLVMF_STK sp0 (lf_FP fr_FP cx) (c_ly cx) (c_S cx) Hpe (c_W cx) (c_mem cx) (c_md cx)
      [(1, fpos)] ly3 S3 Hp3 md k (F - sp0) _ HG eq_refl HJ
      ltac:(rewrite Hsp; lia) Ho16
      ltac:(lia) ltac:(lia) ltac:(unfold ESTACK, LLVMF_STK; lia) R3 R4 Q1
      (ret_ok_codeptr_v A_dc_r1 ltac:(unfold A_dc_r1, A_dr_found, AF_fr_LLVMFuzzerTestOneInput; lia) eq_refl)).
    - intros a. lia.
    - intros a Hwa _. exact (dj_av_ne W mem (rg_lock fr_RG + 4) 4%nat 0 a LK4 ltac:(cbn; lia)).
    - intros a Hwa HnG. exfalso. apply HnG. apply HGlock. lia.
    - intros HPRE2 HSC2.
      exact (ALOCK ly3 S3 Hp3 W regs mem _ (rg_lock fr_RG) 0 HPRE2
        Q10 ltac:(lia) ltac:(rewrite VLK; reflexivity) ltac:(lia) AVL eq_refl LK4
        ltac:(intros a Ha; split;
              [ destruct (Z_lt_le_dec a (rg_lock fr_RG + 4)) as [Hlt | Hge];
                [ exact (dj_av_ne W mem (rg_lock fr_RG) 4%nat 0 a LK0 ltac:(cbn; lia))
                | exact (dj_av_ne W mem (rg_lock fr_RG + 4) 4%nat 0 a LK4 ltac:(cbn; lia)) ]
              | rewrite Hsp; unfold ESTACK, DR_CEIL8 in *; lia ])
        ltac:(intros a Ha; split;
              [ replace a with (rg_lock fr_RG + (a - rg_lock fr_RG)) by lia; exact (LKW (a - rg_lock fr_RG) ltac:(lia))
              | split; [ apply HNOWN; lia | rewrite Hsp; unfold ESTACK, DR_CEIL8 in *; lia ] ])
        (fun a Ha HK => proj2 (proj2 (HG a (HGlock a ltac:(lia)))) (proj1 (proj2 HK)))). }
  cbv beta. intros W2 c2 Hwle2 (-> & regs2 & mem2 & md2 & -> & HJa & HPa & Hlk2 & Hfra & Hpresa).

  assert (PR2 : forall r : bv 5, acallee_saved (bv_unsigned r) -> getr regs2 r = getr regs r)
    by (intros r Hr; exact (dj_pres regs regs2 r HPa Hr)).
  assert (KL : forall a, 0 <= a < 2 ^ 64 -> ~ (rg_lock fr_RG + 4 <= a < rg_lock fr_RG + 8) -> ~ (F - ESTACK <= a < F) ->
      aview segs (w_H W) mem2 a = aview segs (w_H W) mem a)
    by (intros a Ha H1 H2; apply Hfra; [exact Ha | exact H1 | replace (sp0 + (F - sp0)) with F by lia; exact H2]).
  assert (Hfin : In (1, fpos) (frames S3)).
  { pose proof HJ as (_ & _ & (memS & HJ0 & _) & _). pose proof HJ0 as (_ & _ & _ & _ & _ & Hfrs & _).
    rewrite Hfrs. left. reflexivity. }
  assert (HKY : Forall (fun e => Z.of_nat (length (re_keys e)) <= re_nheld e) (lm_es m))
    by (apply Forall_forall; intros e _; apply dr_keys_le).
  pose proof (dj_ne_lockstep ly3 S3 Hp3 W mem md mem2 m false true F HAR HKY (dj_ne_of_at ly3 S3 W mem m HMOD) KL
                ltac:(unfold ESTACK, DR_CEIL8 in *; lia) Hlk2) as HNE2.
  pose proof (dj_ctx_lockstep cx Hpe m FF 0 (flag_addr ly3 1 fpos) ly3 S3 Hp3 W mem md mem2 HB HAR
                (ex_intro _ fpos (conj Hfin eq_refl))
                (conj HFR (conj HFL (conj HIN (conj HRV (conj HROM (conj SVN (conj S192 S40))))))) KL Hpresa)
    as (HFR2 & HFL2 & HIN2 & HRV2 & HROM2 & SVN2 & S1922 & S402).
  apply (SRrG_ret segs R R_refl).
  exists regs2, mem2, md2, k. split; [reflexivity|].
  split.
  { unfold dc_regs.
    rewrite !PR2 by dj_cs.
    repeat (split; [assumption|]). exact R25. }
  split; [exact HJa|]. split; [reflexivity|].
  split; [exact HFR2|]. split; [exact HFL2|]. split; [exact HIN2|]. split; [exact HRV2|]. split; [exact HROM2|].
  split; [exact SVN2|]. split; [exact S1922|]. split; [exact S402|].
  split; [exact HNE2|]. split; [exact HSEP|]. exact HKY.
Qed.

(* dcB_post at R: dr_post_xR without the return configuration, the callee's journal at R *)
Definition dcB_postR (regs : bvmap 5 word) ly S Hp (W : world segs) (mem : word -> option byte) (md : Model)
  (SA HA : Z) (e : rentry) (h : hsrc) (c : ctl) (O : list byte) (mx no cap out : Z)
  (ly' : alayout) (S' : astate) (Hp' : list Z) (W' : world segs) (regs' : bvmap 5 word) (mem' : word -> option byte) (md' : Model)
  : Prop :=
exists k (e' : rentry) (h' : hsrc) (out' ev' : Z) (LB : list byte) rest,
let fin := dr_fin c mx no cap e h in
let live := dr_live c h in
let cap' := if live then drain_b_c.ds_ocap fin else cap in
ajournal_gx_xR segs B PST ARx R (G_DR B fr_RG) 0 [] DRAIN_STK_x (spZ regs) (dr_fp SA e h cap out) ly S Hp W mem md [] ly' S' Hp' W' mem' md' k /\
apres_kept B W mem W' mem' /\
mo_le MT S S' (dr_cost MT c mx no cap e h) /\ NP S' /\
Permutation (ablocks B ly S) (aentry_blks e ++ asrc_blks h ++ aout_blks cap out ++ rest) /\
Permutation (ablocks B ly' S') (aentry_blks e' ++ asrc_blks h' ++ aout_blks cap' out' ++ rest) /\
garr8 segs (arm W' mem') SA (bzs (entry_bytes e')) /\ awr W' mem' SA AENT /\ aentry_ok B ly' S' W' mem' e' /\
Z.of_nat (length (re_keys e')) <= re_nheld e' /\
re_fd e' = re_fd e /\ re_eof e' = (if hs_closed h =? 1 then 1 else re_eof e) /\ 0 < re_cap e' /\
re_cap e' = drain_b_c.ds_cap fin /\ bzs (re_U e') = drain_b_c.ds_u fin /\
re_skip e' = (if drain_b_c.ds_skip fin then 1 else 0) /\
drain_b_c.keys_texts (re_keys e') = drain_b_c.ds_H fin /\ drain_b_c.ent_ka e' = drain_b_c.ds_ka fin /\
((re_hp e' = re_hp e /\ re_kh e' = re_kh e) \/ re_kh e' <= 2 ^ 30) /\
NoDup (drain_b_c.keys_texts (re_keys e')) /\
same_set (drain_b_c.keys_texts (re_keys e')) (upds (drain_b_c.keys_texts (re_keys e)) (dr_lines h)) /\
asrc_at B ly' S' W' mem' HA h' /\
(forall a, rg_s fr_RG <= a < rg_s fr_RG + 4 * ASRC -> ~ (HA <= a < HA + ASRC) -> abyte_kept W mem W' mem' a) /\
hl_cap (hs_expected h') = drain_b_c.ds_ecap fin /\
hl_cap (hs_expected h') <= Z.max 8 (Z.max (hl_cap (hs_expected h)) (2 * hl_n (hs_expected h'))) /\
hs_fd h' = hs_fd h /\ hs_closed h' = hs_closed h /\ hs_eintr h' = 0 /\
hl_recs (hs_pending h') = [] /\ hs_off h' = 0 /\
hl_v (hs_pending h') = hl_v (hs_pending h) /\ hl_cap (hs_pending h') = hl_cap (hs_pending h) /\
hs_partial h' = hs_partial h /\
hs_state h' = feed (hs_state h) (bzs (pending_stream h)) /\
map snd (hl_recs (hs_expected h')) = map snd (hl_recs (hs_expected h)) ++ map (map (Z_to_bv 8)) (dr_lines h) /\
firstn (length (hl_recs (hs_expected h))) (hl_recs (hs_expected h')) = hl_recs (hs_expected h) /\
hs_held h' = hs_held h /\
re_skip e' = hs_overlong h' /\ (re_skip e' = 0 -> bzs (re_U e') = bzs (hs_W h')) /\
bzs LB = with_nul (dr_lines h) /\
aout_at B fr_RG ly' S' W' mem' (dr_ctl c h ev') (if live then O ++ LB else O) mx (if live then no + dr_tot h else no) cap' out'.
Lemma dcB_post_ofR : forall regs ly S Hp (W : world segs) mem md SA HA e h c O mx no cap out kr (W' : world segs) c',
  W_contract_xR.dr_post_xR B PST ARx R MT RP fr_RG regs ly S Hp W mem md SA HA e h c O mx no cap out kr W' c' ->
  exists ly' S' Hp' regs' mem' md' k, c' = mkCfg (mkst regs' (getr regs 1) mem' (seg_rom segs)) md' /\
    ajournal_gx_xR segs B PST ARx R G_fr 0 [] DRAIN_STK_x (spZ regs) (dr_fp SA e h cap out) ly S Hp W mem md [] ly' S' Hp' W' mem' md' k /\
    aregs_preserved regs regs' /\
    dcB_postR regs ly S Hp W mem md SA HA e h c O mx no cap out ly' S' Hp' W' regs' mem' md'.
Proof.
  intros regs ly S Hp W mem md SA HA e h c O mx no cap out kr W' c'
    (ly' & S' & Hp' & regs' & mem' & md' & k & e' & h' & out' & ev' & LB & rest & HP).
  cbv zeta in HP. destruct HP as (Hc & HJ & HPR & HAPK & HMO & HRM & HP1 & HP2 & HG8 & HAW & HEOK & REST).
  exists ly', S', Hp', regs', mem', md', k. split; [exact Hc|].
  split; [exact (ajournal_gx_G_mono_xR segs B PST ARx (G_DR B fr_RG) G_fr 0 [] DRAIN_STK_x (spZ regs) _ ly S Hp W mem md [] ly' S' Hp' W' mem' md'
                   k HG_DR HJ)|].
  split; [exact HPR|].
  exists k, e', h', out', ev', LB, rest. cbv zeta. split; [exact HJ|].
  exact (conj HAPK (conj HMO (conj (proj1 (RP_NP S' kr) HRM) (conj HP1 (conj HP2 (conj HG8 (conj HAW (conj HEOK
    (conj (dr_keys_le e') REST))))))))).
Qed.
(* dc_stB at R: drain at its R spec *)
Lemma dc_stBR : forall cx Hpe t m j si h fpos FF ly S Hp W c,
  lf_base_x B MT XM_LIB RLO RHI fr_live_pre LIBROOM NP G_fr ARx cx Hpe ->
  dc_static cx t m j si h -> LSx cx t m ly S -> NP S ->
  dc_atR cx Hpe t m j si fpos FF A_dc_r1 ly S Hp m true 0 W c ->
  SRrG segs R W c (fun W' c' => exists ly' S' Hp' e' h' out' ev' LB,
    dc_atR cx Hpe t m j si fpos FF A_dc_r2 ly' S' Hp' (dr_m1 m j si h h' e' ev' LB out') true 0 W' c' /\
    mo_le MT S S' (dr_cost MT (lm_c m) (lm_mx m) (Z.of_nat (length (lm_O m))) (lm_cap m) (nth j (lm_es m) dr_e0) h) /\
    dr_dfun m si h j e' h' LB /\ dcB_out m j h ly S e' h' out' ly' S').
Proof.
  intros cx Hpe t m j si h fpos FF ly S Hp W c HB (Hatop & Hpick & Hj & Hfdj & Hef0 & HRI) HLS HNP
    (regs & mem & md & k & -> & HR & HJ & HFFe & HFR & HFL & HIN & HRV & HJT & SVN & S192 & S40 & HNE & HSEP & HKY).
  pose proof HR as (R2 & R8 & R9 & R18 & R19 & R20 & R23 & R24 & R26 & R3 & R4 & R27 & Ht & R21 & R22 & R25).
  pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs.
  pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  pose proof dr_ceil_lo as HCL.
  assert (HAR : ARx ly S Hp W mem md) by (eapply ajournal_gx_AR_xR; exact HJ).
  pose proof HNE as (Hlen4 & HSL & HREL & (ev0 & HOUT) & HGONE & HLOCK & HWAKE & HNFD & HNFDW & HNFDr & HTUP & HLST & HLSTW).
  pose proof HB as (HAI & HPRE).
  pose proof HPRE as (HFNP & _ & _ & _ & Hnrng & Hnlen & _).
  pose proof HFNP as (_ & _ & _ & _ & _ & Hstk & _).
  pose proof Hstk as (Hal16 & _ & Hceil & Hslo & Hshi & H47 & _).
  unfold LLVMF_STK in Hslo.
  assert (HFb : spZ (c_regs cx) - 352 < lf_F cx <= spZ (c_regs cx) - 320).
  { unfold lf_F. pose proof (Z.mod_pos_bound (spZ (c_regs cx) - 320) 32 ltac:(lia)). lia. }
  pose proof (pal_env B TL) as ((HE0 & HE1) & _).
  assert (Hsp : spZ regs = lf_F cx)
    by (unfold spZ; rewrite R2; unfold w64; apply unsigned_lit_small; unfold DR_CEIL8 in *; lia).
  destruct (dc_plain_entry A_dc_r1 W regs mem R26) as [HS SHOK].
  remember (Eimg (Ereg regs [])) as E eqn:HE.
  assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
  assert (HAE : env_agree 32 (Ereg regs []) E)
    by (rewrite HE; split; [intros n Hn; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
  clear HE.
  paj_run_to_tok_x RUNTOG HS HJ SHOK DRspan AF_fr_drain.
  { apply awr_ok_x_nil. }
  dr_meq HF Em.
  pose proof (regs_kept_of_st_ok_pi _ _ _ regs _ [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv
                HS HAE ltac:(vm_compute; reflexivity)) as KR3.
  cbn [ms_regs restrict] in KR3.
  prreg HS (1%bv : bv 5) Q1d. prreg HS (10%bv : bv 5) Q10d.
  pmkst HS. rewrite Em in *. clear HF HFr HG0.
  set (mdD := with_vm_backing (m_vm_lazy md) mat md) in *.
  rewrite (proj1 HAE 22%nat ltac:(lia)), (ew_Ereg_nat regs [] 22 22%bv eq_refl), R22 in Q10d.
  assert (HspD : spZ (ms_regs ms) = lf_F cx) by (unfold spZ; rewrite (KR3 2%bv ltac:(dcB_in)); exact Hsp).
  assert (Hfin : In (1, fpos) (frames S)).
  { pose proof HJ as (_ & _ & (memS & HJ0 & _) & _). pose proof HJ0 as (_ & _ & _ & _ & _ & Hfrs & _).
    rewrite Hfrs. left. reflexivity. }
  assert (HGONE0 : forall p n i, In (p, n) (ablocks B (c_ly cx) (c_S cx)) -> ~ In (p, n) (ablocks B ly S) ->
      0 <= i < req_size n -> inFP (lf_FP fr_FP cx) (p + i)).
  { pose proof HJ as (_ & _ & (memS & HJ0 & _) & _).
    pose proof HJ0 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hg & _). exact Hg. }
  pose proof Hpick as (_ & Hsi4 & Hhsi).
  destruct (dr_pads_of_relay ly S W mem (lm_G m) (lm_es m) HREL) as (HPAD & HFDS).
  pose proof HREL as (RL1 & RL2 & RL3 & RL4 & RL5 & RL6 & RL7 & HGin & (tl & HTAB) & HENT & HNDF & HTBN).
  assert (HSA8 : (lm_G m + AENT * Z.of_nat j) mod 8 = 0).
  { destruct (alx_blocks _ _ _ LAWS ly S Hp W mem md _ _ HAR HGin) as (HG16 & _).
    pose proof (Z.div_mod (lm_G m) 16 ltac:(lia)) as HGd. rewrite HG16, Z.add_0_r in HGd.
    rewrite HGd. unfold AENT.
    replace (16 * (lm_G m / 16) + 56 * Z.of_nat j) with ((2 * (lm_G m / 16) + 7 * Z.of_nat j) * 8) by ring.
    apply Z_mod_mult. }
  assert (HEOK : aentry_ok B ly S W mem (nth j (lm_es m) dr_e0))
    by (rewrite Forall_forall in HENT; apply HENT, nth_In; exact Hj).
  destruct (RI_pair cx t m si h j HRI Hpick Hj Hfdj Hef0) as (HSK & HSKU & _ & _).
  destruct (dr_blk B ARx LAWS BLKR ly S Hp W mem md (lm_G m) ATABLE HAR HGin) as (HG4096 & HGceil & _).
  assert (HSA : lm_G m <= lm_G m + AENT * Z.of_nat j /\ lm_G m + AENT * Z.of_nat j + AENT <= lm_G m + ATABLE)
    by (unfold AENT, ATABLE; lia).
  assert (HSRC0 : asrc_at B ly S W mem (rg_s fr_RG + ASRC * Z.of_nat si) h).
  { pose proof (HSL si Hsi4) as Hs. rewrite Hhsi in Hs. exact Hs. }
  pose proof (dr_tbl_entry W mem (lm_G m) (lm_es m) tl j HTAB HPAD Hj) as HEB.
  assert (HEL : length (bzs (entry_bytes (nth j (lm_es m) dr_e0))) = 56%nat).
  { pose proof HEOK as (_ & _ & Hq1 & Hq2 & _). rewrite dra_bzs_length. apply entry_bytes_length; assumption. }
  assert (HEW : awr W mem (lm_G m + AENT * Z.of_nat j) AENT).
  { pose proof (dr_awr_of_garr8 ly S Hp W mem md (lm_G m) ATABLE (lm_G m + AENT * Z.of_nat j)
                  (bzs (entry_bytes (nth j (lm_es m) dr_e0))) HAR HGin ltac:(lia)
                  ltac:(rewrite HEL; replace (req_size ATABLE) with ATABLE by reflexivity; unfold AENT, ATABLE in *; lia)
                  HEB) as Hw.
    rewrite HEL in Hw. exact Hw. }
  assert (HOTH : aothers_at fr_RG W mem si (re_fd (nth j (lm_es m) dr_e0))).
  { intros i Hi Hne. pose proof (HSL i Hi) as Hs. revert Hs.
    destruct (nth i (lm_hs m) None) as [hi|] eqn:Ehi; intros Hs; cbn [aslot] in Hs.
    - exists (hs_fd hi), (hs_open hi). pose proof Hs as (V1 & V2 & _).
      split; [exact V1|]. split; [exact V2|]. right. rewrite Hfdj.
      assert (Fi : 0 <= hs_fd hi < 2 ^ 31) by (unfold asrc_at in Hs; tauto).
      assert (Fh : 0 <= hs_fd h < 2 ^ 31) by (unfold asrc_at in HSRC0; tauto).
      rewrite !Z.mod_small by lia.
      exact (RI_fds cx t m i si hi h HRI Hi Hsi4 Hne Ehi Hhsi).
    - exists 0, 0. destruct Hs as (Hz & _).
      pose proof (dcB_zero_vm _ _ (Z.to_nat ASRC) 0 Hz ltac:(lia)
                    ltac:(rewrite Z2Nat.id by (unfold ASRC; lia); unfold ASRC; lia)) as Hz0.
      rewrite Z.add_0_r in Hz0.
      split; [exact Hz0|]. split; [|left; reflexivity].
      exact (dcB_zero_vm _ _ (Z.to_nat ASRC) 4 Hz ltac:(lia)
               ltac:(rewrite Z2Nat.id by (unfold ASRC; lia); unfold ASRC; lia)). }
  assert (HXM : forall b, In b (aentry_blks (nth j (lm_es m) dr_e0) ++ asrc_blks h ++ aout_blks (lm_cap m) (lm_out m)) ->
      In b (model_blks m)).
  { intros b Hb. unfold model_blks. right. apply in_app_or in Hb as [Hb | Hb].
    - apply in_or_app. left. apply in_concat. exists (aentry_blks (nth j (lm_es m) dr_e0)).
      split; [apply in_map, nth_In; exact Hj | exact Hb].
    - apply in_or_app. right. apply in_app_or in Hb as [Hb | Hb].
      + apply in_or_app. left. apply in_concat. exists (slot_blks (Some h)). split; [|exact Hb].
        rewrite <- Hhsi. apply in_map, nth_In. lia.
      + apply in_or_app. right. exact Hb. }
  pose proof HSEP as HSEPc.
  destruct HSEP as ((rest0 & HPm0) & HSEP2).
  assert (HXL : forall b, In b (aentry_blks (nth j (lm_es m) dr_e0) ++ asrc_blks h ++ aout_blks (lm_cap m) (lm_out m)) ->
      In b (ablocks B ly S)).
  { intros b Hb. apply (Permutation_in _ (Permutation_sym HPm0)).
    apply in_or_app. right. apply in_or_app. left. exact (HXM b Hb). }
  assert (HXP : forall b, In b (aentry_blks (nth j (lm_es m) dr_e0) ++ asrc_blks h ++ aout_blks (lm_cap m) (lm_out m)) ->
      0 < snd b).
  { intros b Hb. apply in_app_or in Hb as [Hb | Hb]; [exact (dcB_pos_aentry _ _ _ _ _ _ HEOK Hb)|].
    apply in_app_or in Hb as [Hb | Hb];
      [exact (dcB_pos_asrc _ _ _ _ _ _ _ HSRC0 Hb) | exact (dcB_pos_aout _ _ _ _ _ _ _ _ _ _ _ HOUT Hb)]. }
  unfold model_blks in HPm0.
  pose proof (dr_concat_nth_perm _ _ aentry_blks (lm_es m) j dr_e0 Hj) as HCA.
  pose proof (dr_concat_nth_perm _ _ slot_blks (lm_hs m) si None ltac:(lia)) as HCS.
  rewrite Hhsi in HCS. cbn [slot_blks] in HCS.
  pose proof (dcB_perm_pre _ _ _ _ _ _ _ _ _ _ _ HPm0 HCA HCS) as HPERM0.
  assert (HU : Z.of_nat (length (re_U (nth j (lm_es m) dr_e0))) <= APARTIAL)
    by (pose proof HEOK as (_ & _ & _ & _ & _ & _ & Hu1 & Hu2 & _); lia).
  destruct (LS_drain_pre cx t m ly S si h j HLS HRI Hatop Hpick Hj Hfdj Hef0 Ht HU HXP) as (L1 & L2 & L3 & L4 & L5 & L6).
  rewrite <- (dcB_tr_ctl (lm_c m) ev0) in L4, L5. rewrite <- (dcB_cost_ctl (lm_c m) ev0) in L6.
  destruct (dcB_epre ly S W mem _ HEOK) as (EPRE & EKH).
  destruct (dcB_hpre ly S W mem _ h HSRC0) as (HPRE3 & HHN3).
  pose proof (dcB_cap0 _ _ _ _ _ _ _ _ _ _ HOUT) as CAP0.
  pose proof (dr_msz_x ly S W mem m Hlen4 HSL HREL) as HMSZ.
  destruct (RI_src cx t m si h HRI Hpick) as (Hexp0 & _ & _).
  pose proof (LS_cnt cx t m ly S si h j HLS HRI Hatop Hpick Hj Hfdj Hef0 HMSZ Ht HU HXP (proj1 HPRE3)) as HCNT.
  assert (HCNTd : cnt_ok_pk RP (dr_pk (dc_ctl (lm_c m) ev0) (lm_mx m) (Z.of_nat (length (lm_O m))) (lm_cap m)
      (nth j (lm_es m) dr_e0) h) (ablocks B ly S)).
  { refine (cnt_ok_pk_mono RP _ _ (ablocks B ly S) (ablocks B ly S) _ HCNT).
    intros P. unfold dr_pk. cbv beta. rewrite dcB_tr_ctl. lia. }
  assert (HRMd : rp_RM RP S (Z.to_nat (dr_cost MT_rk (dc_ctl (lm_c m) ev0) (lm_mx m) (Z.of_nat (length (lm_O m)))
      (lm_cap m) (nth j (lm_es m) dr_e0) h) + 0)%nat) by (apply RP_NP; exact HNP).
  destruct (dr_afn_pre_atR cx Hpe ly S Hp fpos k W mem mdD (ms_regs ms) DRAIN_STK_x HB HJ) as (ch & HPRED).
  { rewrite HFFe. exact (dr_aframe_false cx FF W mem HFR). }
  { exact HspD. }
  { rewrite Q1d. apply ret_ok_codeptr_v; [lia | reflexivity]. }
  { unfold raZ. rewrite Q1d, unsigned_lit_small by lia. lia. }
  { rewrite (KR3 3%bv ltac:(dcB_in)). exact R3. }
  { rewrite (KR3 4%bv ltac:(dcB_in)). exact R4. }
  { rewrite (KR3 8%bv ltac:(dcB_in)). exact R8. }
  { unfold DRAIN_STK_x, DRAIN_STK, DRAIN_FRAME, SL_STK, SL_FRAME, ASTACK. lia. }
  { unfold DRAIN_STK_x, DRAIN_STK, DRAIN_FRAME, SL_STK, SL_FRAME, ASTACK, LLVMF_STK. lia. }
  (* ---- drain(r) at its R spec, composed into the function's R journal ---- *)
  eapply (SRrG_mono segs R).
  { apply (dr_callZR G_fr W (ms_regs ms) mem (Z_to_bv 64 (BASE + 3568)) LLVMF_STK (spZ (c_regs cx)) (lf_FP fr_FP cx)
      (c_ly cx) (c_S cx) Hpe (c_W cx) (c_mem cx) (c_md cx) [(1, fpos)] ly S Hp mdD k DRAIN_STK_x
      (dr_fp (lm_G m + AENT * Z.of_nat j) (nth j (lm_es m) dr_e0) h (lm_cap m) (lm_out m)) 0 []
      (lf_F cx - spZ (c_regs cx)) (Z_to_bv 64 (BASE + 10096)) ch
      (fun ly2 S2 Hp2 W2 regs2 mem2 md2 => dcB_postR (ms_regs ms) ly S Hp W mem mdD (lm_G m + AENT * Z.of_nat j)
         (rg_s fr_RG + ASRC * Z.of_nat si) (nth j (lm_es m) dr_e0) h (dc_ctl (lm_c m) ev0) (lm_O m) (lm_mx m)
         (Z.of_nat (length (lm_O m))) (lm_cap m) (lm_out m) ly2 S2 Hp2 W2 regs2 mem2 md2)
      HG HJ).
    - rewrite HspD. lia.
    - lia.
    - unfold DRAIN_STK_x, DRAIN_STK, DRAIN_FRAME, SL_STK, SL_FRAME, ASTACK, LLVMF_STK. lia.
    - lia.
    - lia.
    - intros a Ha. exfalso. exact (inFP_nil a Ha).
    - exact Q1d.
    - exact HPRED.
    - eapply (SRrG_mono segs R).
      { exact (DRAIN_R W ly S Hp (ms_regs ms) mem mdD ch (lm_G m) (lm_G m + AENT * Z.of_nat j)
                 (nth j (lm_es m) dr_e0) si h (dc_ctl (lm_c m) ev0) (lm_O m) (lm_mx m)
                 (Z.of_nat (length (lm_O m))) (lm_cap m) (lm_out m) HPRED Q10d HGin (proj1 HSA) (proj2 HSA) HSA8
                 HEB HEW HEOK Hsi4 HSRC0 HOTH (eq_sym Hfdj) HSK HSKU HOUT HRV (ex_intro _ _ HPERM0)
                 L1 L2 L3 L4 L5 L6 0%nat HRMd HCNTd). }
      cbv beta. intros W2 c2 _ HPOST.
      destruct (dcB_post_ofR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HPOST)
        as (ly2 & S2 & Hp2 & regs2 & mem2 & md2 & k2 & Hc2 & HJ2 & HPR2 & HK2).
      exists ly2, S2, Hp2, regs2, mem2, md2, k2. rewrite Q1d in Hc2.
      split; [exact Hc2|]. split; [exact HJ2|]. split; [exact HPR2 | exact HK2].
    - intros a (r & Hr & Ha). destruct Hr as [<- | Hr].
      + cbn [fst snd] in Ha.
        apply (dcB_fp_blk cx m ly S (lm_G m, ATABLE) a HSEPc);
          [unfold model_blks; left; reflexivity | cbn [snd]; unfold ATABLE; lia
          | cbn [fst snd]; replace (req_size ATABLE) with ATABLE by reflexivity; unfold AENT, ATABLE in *; lia].
      + unfold ablocks_fp in Hr. apply in_map_iff in Hr as (b & <- & Hb). cbn [fst snd] in Ha.
        exact (dcB_fp_blk cx m ly S b a HSEPc (HXM b Hb) (HXP b Hb) Ha). }
  cbv beta. intros W2 c2 _ (ly2 & S2 & Hp2 & regs2 & mem2 & md2 & k1 & -> & HJ2 & _ & HPR & HK).
  destruct HK as (k2 & e' & h' & out' & ev' & LB & rest & HK). cbv zeta in HK.
  destruct HK as (HJD & HPK & HMO & HNP2 & HP1 & HP2 & HN1 & HN2 & HN3 & HKE & D9 & D10 & D11 & D12 & D13 & D14 & D15 & D16
                  & D17 & D18 & D19 & HSRC & HGS & D22 & D23 & D24 & D25 & D26 & D27 & D28 & D29 & D30 & D31 & D32 & D33
                  & D34 & D35 & D36 & D37 & D38 & HOUT2).
  rewrite HspD in HJD.
  rewrite dcB_cost_ctl in HMO. rewrite dcB_fin_ctl in D12, D13, D14, D15, D16, D22.
  rewrite ?dcB_live_ctl, ?dcB_fin_ctl, ?dcB_dctl_ctl in HOUT2. rewrite ?dcB_live_ctl, ?dcB_fin_ctl in HP2.
  assert (HDF : dr_dfun m si h j e' h' LB).
  { unfold dr_dfun. cbv zeta.
    split; [exact D9|]. split; [exact D10|]. split; [exact D11|]. split; [exact D12|]. split; [exact D13|].
    split; [exact D14|]. split; [exact D15|]. split; [exact D16|]. split; [exact D18|]. split; [exact D19|].
    split; [exact D24|]. split; [exact D25|]. split; [exact D26|]. split; [exact D27|]. split; [exact D28|].
    split; [exact D32|]. split; [exact D33|]. split; [exact D35|]. split; [exact D36|]. split; [exact D37|].
    split; [exact D38|]. split; [exact D22|].
    pose proof HN3 as (_ & _ & Hpd1 & Hpd2 & _). split; [exact Hpd1 | exact Hpd2]. }
  assert (EPOST : dr3_epost (nth j (lm_es m) dr_e0) e' h).
  { pose proof HN3 as (_ & _ & _ & _ & _ & Hc' & _). exact (conj Hc' (conj D17 (conj D18 D19))). }
  assert (EKH' : (re_hp e' = 0 /\ re_keys e' = []) \/ (re_hp e' <> 0 /\ 8 <= re_kh e')).
  { pose proof HN3 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hkh' & _).
    destruct Hkh' as [(Hz' & Hk') | (Hz' & _ & _ & H8' & _)]; [left; split; assumption | right; split; assumption]. }
  assert (HPOST3 : dr3_hpost h h') by exact (conj D27 (conj D30 D23)).
  assert (DPOST : ls3_dpost m j h e' h').
  { pose proof HSRC as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HEX2 & _).
    pose proof HEX2 as (_ & _ & _ & _ & (HnX2 & _) & _).
    exact (conj D13 (conj D16 (conj D28 (conj D33 (conj D35 HnX2))))). }
  assert (HGR : forall P, (ReplyCnt.acnt P (ablocks B ly2 S2) <= ReplyCnt.acnt P (ablocks B ly S) +
      Z.to_nat (ReplyCnt.tr_peakP P (dr_tr (lm_c m) (lm_mx m) (Z.of_nat (length (lm_O m))) (lm_cap m)
                                      (nth j (lm_es m) dr_e0) h)))%nat).
  { intros P.
    pose proof (DR_CNT_grow cx t m si h j e' h' LB out' P HRI Hatop Hpick Hj Hfdj Hef0 (proj1 (proj2 HEOK)) HMSZ Ht HU
      HXP EPRE EKH HPRE3 HHN3 CAP0 HDF EPOST EKH' HPOST3 DPOST) as Hgr.
    unfold dr_cap1 in Hgr.
    rewrite (ReplyCnt.acnt_perm P _ _ HP1), (ReplyCnt.acnt_perm P _ _ HP2), !ReplyCnt.acnt_app.
    rewrite !ReplyCnt.acnt_app in Hgr. lia. }
  assert (HCNTc : cnt_ok_pk RP (cnl_pk (hs_expected h') (hs_held h')) (ablocks B ly2 S2)).
  { refine (cnt_ok_pk_mono RP _ _ (ablocks B ly S) (ablocks B ly2 S2) _ HCNT).
    intros P. specialize (HGR P). pose proof (DR_CNT_cnl h h' P Hexp0 D33 D35) as EC.
    unfold cnl_pk. cbv beta. lia. }
  pose proof dcB_GDR_ok as HGDR.
  pose proof (dj_nodup ly S Hp W mem md HAR) as HNDS.
  assert (HAR2 : ARx ly2 S2 Hp2 W2 mem2 md2) by (eapply ajournal_gx_AR_xR; exact HJD).
  pose proof (dj_nodup ly2 S2 Hp2 W2 mem2 md2 HAR2) as HNDS2.
  assert (HP1' : Permutation (ablocks B ly S)
      ((aentry_blks (nth j (lm_es m) dr_e0) ++ asrc_blks h ++ aout_blks (lm_cap m) (lm_out m)) ++ rest))
    by (rewrite <- !app_assoc; exact HP1).
  assert (HRT : Permutation rest ((lm_G m, ATABLE) :: dcB_T cx m j si rest0))
    by exact (dcB_perm_rest _ _ _ _ _ _ _ HPERM0 HP1).
  assert (KTR : forall b, In b (dcB_T cx m j si rest0) -> In b rest)
    by (intros b Hb; apply (Permutation_in _ (Permutation_sym HRT)); right; exact Hb).
  assert (KTL2 : forall b, In b rest -> In b (ablocks B ly2 S2)).
  { intros b Hb. apply (Permutation_in _ (Permutation_sym HP2)).
    apply in_or_app; right; apply in_or_app; right; apply in_or_app; right; exact Hb. }
  assert (HGr : In (lm_G m, ATABLE) rest) by (apply (Permutation_in _ (Permutation_sym HRT)); left; reflexivity).
  assert (HCSin : forall i hi b, (i < 4)%nat -> i <> si -> nth i (lm_hs m) None = Some hi -> In b (asrc_blks hi) ->
      In b (dcB_T cx m j si rest0)).
  { intros i hi b Hi Hne Ehi Hb. unfold dcB_T. apply in_or_app. right. apply in_or_app. left. unfold dcB_CS.
    apply in_concat. exists (slot_blks (Some hi)). split; [|exact Hb]. apply in_map. rewrite <- Ehi.
    apply dcB_in_rm_nth; lia. }
  assert (HCAin : forall y b, In y (firstn j (lm_es m) ++ skipn (Datatypes.S j) (lm_es m)) -> In b (aentry_blks y) ->
      In b (dcB_T cx m j si rest0)).
  { intros y b Hy Hb. unfold dcB_T. apply in_or_app. left. unfold dcB_CA.
    apply in_concat. exists (aentry_blks y). split; [apply in_map; exact Hy | exact Hb]. }
  assert (KBLK : forall p n a, In (p, n) (ablocks B ly S) -> In (p, n) (ablocks B ly2 S2) -> p <= a < p + req_size n ->
      ~ inFP (dr_fp (lm_G m + AENT * Z.of_nat j) (nth j (lm_es m) dr_e0) h (lm_cap m) (lm_out m)) a ->
      abyte_kept W mem W2 mem2 a).
  { intros p n a H1 H2 Ha Hnf.
    pose proof (blk_img_x segs B ARx LAWS ly S Hp W mem md p n a HAR H1 Ha) as Hni.
    destruct (dr_blk B ARx LAWS BLKR ly S Hp W mem md p n HAR H1) as (Hp1o & Hp2o & _).
    apply dj_bk; [lia | intros Hi; exfalso; exact (Hni Hi) |].
    eapply dj_keepR; [exact HGDR | exact HJD | lia | intros HGa; exact (Hni (proj1 (HGDR a HGa))) |].
    right; right; left. exists p, n. split; [exact H1|]. split; [exact H2|]. split; [exact Ha | exact Hnf]. }
  assert (KT : forall b a, In b (dcB_T cx m j si rest0) -> fst b <= a < fst b + snd b -> abyte_kept W mem W2 mem2 a).
  { intros [p n] a HbT Ha. cbn [fst snd] in Ha.
    destruct (dcB_in_rest _ _ _ _ HNDS HP1' (KTR _ HbT)) as (HnX & HbL).
    pose proof (dcB_T_ne _ _ _ _ _ _ HNDS HP1' HRT HbT) as Hng.
    destruct (dr_blk B ARx LAWS BLKR ly S Hp W mem md p n HAR HbL) as (_ & _ & Hn0).
    apply (KBLK p n a HbL (KTL2 _ (KTR _ HbT)) ltac:(lia)).
    exact (dcB_nfp_blk ly S Hp W mem md (lm_G m) (lm_G m + AENT * Z.of_nat j) _ p n a HAR HGin (proj1 HSA) (proj2 HSA)
             HXL HbL HnX ltac:(lia) (or_introl Hng)). }
  assert (KTAB : forall a, lm_G m <= a < lm_G m + ATABLE ->
      ~ (lm_G m + AENT * Z.of_nat j <= a < lm_G m + AENT * Z.of_nat j + AENT) -> abyte_kept W mem W2 mem2 a).
  { intros a Ha Hn.
    destruct (dcB_in_rest _ _ _ _ HNDS HP1' HGr) as (HnX & HbL).
    apply (KBLK (lm_G m) ATABLE a HbL (KTL2 _ HGr) ltac:(replace (req_size ATABLE) with ATABLE by reflexivity; lia)).
    exact (dcB_nfp_blk ly S Hp W mem md (lm_G m) (lm_G m + AENT * Z.of_nat j) _ (lm_G m) ATABLE a HAR HGin (proj1 HSA)
             (proj2 HSA) HXL HbL HnX ltac:(replace (req_size ATABLE) with ATABLE by reflexivity; lia) (or_intror Hn)). }
  assert (KSTK : forall a, lf_F cx <= a < spZ (c_regs cx) -> abyte_kept W mem W2 mem2 a).
  { intros a Ha.
    assert (Hni : ~ in_img segs a) by (intros Hi; pose proof (Hsegs a Hi); lia).
    apply dj_bk; [lia | intros Hi; exfalso; exact (Hni Hi) |].
    eapply dj_keepR; [exact HGDR | exact HJD | lia | intros HGa; exact (Hni (proj1 (HGDR a HGa))) |].
    left. split; [lia | lia]. }
  assert (FFb : 4096 <= FF /\ FF + 128 <= alloc_ceiling).
  { destruct (frames_bounds_x segs B ARx LAWS ly S Hp W mem md 1 fpos HAR Hfin) as (Hf0 & Hfc & _).
    rewrite HFFe in Hf0, Hfc. replace (fs_frame_bytes 1) with 128 in Hfc by reflexivity. lia. }
  assert (KFF : forall a, FF <= a < FF + 128 -> abyte_kept W mem W2 mem2 a).
  { intros a Ha.
    assert (Hfr : frame_addr ly 1 fpos <= a < frame_addr ly 1 fpos + fs_frame_bytes 1)
      by (rewrite HFFe; replace (fs_frame_bytes 1) with 128 by reflexivity; exact Ha).
    pose proof (frm_img_x segs B ARx LAWS ly S Hp W mem md 1 fpos a HAR Hfin Hfr) as Hni.
    apply dj_bk; [lia | intros Hi; exfalso; exact (Hni Hi) |].
    eapply dj_keepR; [exact HGDR | exact HJD | lia | intros HGa; exact (Hni (proj1 (HGDR a HGa))) |].
    right; right; right; right. exists 1, fpos. split; [exact Hfin|].
    split; [left; unfold in_zr, frame_rng; cbn [fst snd]; exact Hfr|].
    exact (dcB_nfp_frm ly S Hp W mem md (lm_G m) (lm_G m + AENT * Z.of_nat j) _ 1 fpos a HAR HGin (proj1 HSA) (proj2 HSA)
             HXL Hfin (or_introl Hfr)). }
  assert (KSH : forall a, SB + FF / 8 <= a < SB + FF / 8 + 16 -> abyte_kept W mem W2 mem2 a).
  { intros a Ha.
    assert (FF8 : 0 <= FF / 8 /\ 8 * (FF / 8) <= FF) by (split; [apply Z.div_pos; lia | apply Z.mul_div_le; lia]).
    unfold SB in Ha.
    assert (Hni : ~ in_img segs a) by (intros Hi; pose proof (Hsegs a Hi); lia).
    apply dj_bk; [lia | intros Hi; exfalso; exact (Hni Hi) |].
    eapply dj_keepR; [exact HGDR | exact HJD | lia | intros HGa; exact (Hni (proj1 (HGDR a HGa))) |].
    right; right; right; right. exists 1, fpos. split; [exact Hfin|].
    assert (Hsh : shadow_addr (frame_addr ly 1 fpos) <= a < shadow_addr (frame_addr ly 1 fpos) + fs_frame_bytes 1 / 8).
    { rewrite HFFe. replace (fs_frame_bytes 1 / 8) with 16 by reflexivity. unfold shadow_addr, SHADOW_OFF. lia. }
    split; [right; unfold in_zr; cbn [fst snd]; exact Hsh|].
    exact (dcB_nfp_frm ly S Hp W mem md (lm_G m) (lm_G m + AENT * Z.of_nat j) _ 1 fpos a HAR HGin (proj1 HSA) (proj2 HSA)
             HXL Hfin (or_intror Hsh)). }
  assert (HFPpos : Forall (fun r => 0 < fst r)
      (dr_fp (lm_G m + AENT * Z.of_nat j) (nth j (lm_es m) dr_e0) h (lm_cap m) (lm_out m))).
  { unfold dr_fp. constructor; [cbn [fst]; lia|]. apply Forall_forall. intros r Hr. unfold ablocks_fp in Hr.
    apply in_map_iff in Hr as ([p n] & <- & Hb). cbn [fst].
    destruct (dr_blk B ARx LAWS BLKR ly S Hp W mem md p n HAR (HXL _ Hb)) as (Hpo & _).
    lia. }
  assert (KIMG : forall a, inG DR_GK a \/ rg_lock fr_RG <= a < rg_lock fr_RG + 12 -> abyte_kept W mem W2 mem2 a).
  { intros a Ha. destruct (dcB_GK_out a Ha) as (HnD & Hne).
    assert (HGa : inG G_fr a) by (destruct Ha as [Ha | Ha]; [exact (HG_GK a Ha) | exact (HGlock a Ha)]).
    destruct (HG a HGa) as (Hi & Hno & _). pose proof (Hsegs a Hi) as Hlo.
    apply dj_bk; [lia | intros _; exact HGa |].
    eapply dj_keepR; [exact HGDR | exact HJD | lia | exact HnD |].
    right; right; right; left. split; [exact Hi|]. split; [exact Hno|]. split; [exact Hne|].
    apply fp_spares_closed. apply sink_closed_pos. exact HFPpos. }
  assert (HFF2 : frame_addr ly2 1 fpos = FF).
  { pose proof HJD as (_ & _ & (memS & HJi & _) & _). pose proof HJi as (_ & Hly & _).
    pose proof Hly as (_ & _ & _ & _ & _ & EF & _). unfold frame_addr. rewrite EF. exact HFFe. }
  assert (HFR2 : aframe_at cx true FF W2 mem2) by (apply (dcB_aframe_kept cx true FF W W2 mem mem2 HFR KSTK KFF KSH); lia).
  assert (HFL2 : sv8 W2 mem2 (FF + 120) (flag_addr ly2 1 fpos)).
  { pose proof HJD as (_ & _ & (memS & HJi & _) & _). pose proof HJi as (_ & Hly & _).
    pose proof Hly as (_ & _ & _ & _ & _ & EF & _). unfold flag_addr. rewrite EF.
    apply (dr_sv8_kept W W2 mem mem2); [intros x Hx; apply KFF; lia | exact HFL]. }
  assert (HIN2 : ainput_at B cx ly2 S2 W2 mem2).
  { destruct HIN as (Hn & Hpl).
    assert (HbT : 0 < c_n cx -> In (c_p cx, c_n cx) (dcB_T cx m j si rest0)).
    { intros Hn1. unfold dcB_T. apply in_or_app. right. apply in_or_app. right. apply in_or_app. left.
      unfold input_blks. rewrite (proj2 (Z.eqb_neq (c_n cx) 0) ltac:(lia)). left. reflexivity. }
    split.
    - destruct Hn as [Hn | (Hn1 & Hin)]; [left; exact Hn | right; split; [exact Hn1|]].
      exact (KTL2 _ (KTR _ (HbT (proj1 Hn1)))).
    - apply (akept_garr8 W mem); [|exact Hpl]. intros x Hx. rewrite length_map, <- Hnlen in Hx.
      destruct Hn as [(Hn0 & _) | (Hn1 & _)]; [lia|].
      exact (KT (c_p cx, c_n cx) x (HbT (proj1 Hn1)) ltac:(cbn [fst snd]; lia)). }
  assert (HRV2 : rom_view segs W2 mem2)
    by exact (ajournal_gx_rom_view_xR segs B PST ARx LAWS pa_segs_low _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJD dcB_rom_out dr_pstr HRV).
  pose proof (dcB_jt W W2 mem mem2 HRV HRV2 HJT) as HJT2.
  assert (SVN2 : sv8 W2 mem2 (lf_F cx + DR_N) (c_n cx - dr_k' cx m)).
  { apply (dr_sv8_kept W W2 mem mem2); [|exact SVN]. intros x Hx. apply KSTK. unfold DR_N in Hx. lia. }
  assert (S1922 : sv8 W2 mem2 (lf_F cx + DR_AT) 0).
  { apply (dr_sv8_kept W W2 mem mem2); [|exact S192]. intros x Hx. apply KSTK. unfold DR_AT in Hx. lia. }
  assert (S402 : sv8 W2 mem2 (lf_F cx + 40) (rg_lock fr_RG)).
  { apply (dr_sv8_kept W W2 mem mem2); [|exact S40]. intros x Hx. apply KSTK. lia. }
  assert (HLEN1 : Z.of_nat (length (dr_O1 m h LB)) =
      (if dr_live (lm_c m) h then Z.of_nat (length (lm_O m)) + dr_tot h else Z.of_nat (length (lm_O m)))).
  { unfold dr_O1. destruct (dr_live (lm_c m) h); [|reflexivity].
    rewrite length_app, Nat2Z.inj_add, (dc_LB_len LB _ D38). reflexivity. }
  assert (HO1 : aout_at B fr_RG ly2 S2 W2 mem2 (dc_ctl (dr_ctl (lm_c m) h ev') ev') (dr_O1 m h LB) (lm_mx m)
                  (Z.of_nat (length (dr_O1 m h LB))) (dr_cap1 m j h) out').
  { rewrite HLEN1. unfold dr_O1, dr_cap1. exact HOUT2. }
  assert (HREL2 : arelay_at B fr_RG ly2 S2 W2 mem2 (lm_G m) (set_nth j e' (lm_es m))).
  { pose proof HN3 as (_ & _ & Hq1 & Hq2 & _).
    split; [apply (akept_vm W mem); [intros x Hx; apply KIMG; dcB_gk Hx | exact RL1]|].
    split; [apply (akept_awr W mem); [intros x Hx; apply KIMG; dcB_gk Hx | exact RL2]|].
    split; [rewrite set_nth_length; apply (akept_vm W mem); [intros x Hx; apply KIMG; dcB_gk Hx | exact RL3]|].
    split; [apply (akept_awr W mem); [intros x Hx; apply KIMG; dcB_gk Hx | exact RL4]|].
    split; [apply (akept_vm W mem); [intros x Hx; apply KIMG; dcB_gk Hx | exact RL5]|].
    split; [apply (akept_awr W mem); [intros x Hx; apply KIMG; dcB_gk Hx | exact RL6]|].
    split; [rewrite set_nth_length; exact RL7|].
    split; [exact (KTL2 _ HGr)|].
    split.
    { exists tl. apply (dr_tbl_upd W W2 mem mem2 (lm_G m) (lm_es m) tl j e' HTAB HPAD Hq1 Hq2 Hj HN1).
      intros a Ha Hn. exact (proj1 (KTAB a Ha Hn)). }
    split.
    { apply Forall_forall. intros y Hy.
      destruct (dr_in_set_nth rentry j e' y (lm_es m) Hy) as [-> | Hy']; [exact HN3|].
      assert (HyE : In y (lm_es m)) by exact (dr_in_rm rentry j y (lm_es m) Hy').
      rewrite Forall_forall in HENT, HKY.
      apply (aentry_ok_kept B ly S W mem ly2 S2 W2 mem2 y (HENT y HyE)).
      - intros r Hr x Hx.
        destruct (dj_aentry_fp ly S W mem y (HENT y HyE) (HKY y HyE) r Hr x Hx) as [[] | (b & Hb & Hbx)].
        exact (KT b x (HCAin y b Hy' Hb) Hbx).
      - intros b Hb. exact (KTL2 b (KTR b (HCAin y b Hy' Hb))). }
    rewrite dr_map_set_nth, D9.
    assert (Hfe : re_fd (nth j (lm_es m) dr_e0) = nth j (map re_fd (lm_es m)) (re_fd dr_e0))
      by (rewrite map_nth; reflexivity).
    split; [rewrite Hfe, dcB_set_nth_nth; exact HNDF|].
    apply Forall_forall. intros y Hy b Hb Heq. subst b.
    destruct (dr_in_set_nth rentry j e' y (lm_es m) Hy) as [-> | Hy'].
    - apply (dcB_nd_app (aentry_blks e') _ (lm_G m, ATABLE) (Permutation_NoDup HP2 HNDS2) Hb).
      apply in_or_app. right. apply in_or_app. right. exact HGr.
    - rewrite Forall_forall in HTBN. exact (HTBN y (dr_in_rm rentry j y (lm_es m) Hy') _ Hb eq_refl). }
  assert (HNE2 : amodel_ne ly2 S2 W2 mem2 (dr_m1 m j si h h' e' ev' LB out') true).
  { unfold dr_m1, dr_step, amodel_ne. cbn [lm_hs lm_G lm_es lm_c lm_O lm_mx lm_cap lm_out lm_gn lm_nfd].
    split; [rewrite set_nth_length; exact Hlen4|].
    split.
    { intros i Hi. destruct (Nat.eq_dec i si) as [-> | Hne].
      - rewrite set_nth_same by lia. exact HSRC.
      - rewrite set_nth_other by lia.
        pose proof (HSL i Hi) as Hs. revert Hs.
        destruct (nth i (lm_hs m) None) as [hi|] eqn:Ehi; intros Hs; cbn [aslot] in Hs |- *.
        + apply (asrc_at_kept B ly S W mem ly2 S2 W2 mem2 _ hi Hs).
          * intros r Hr x Hx. destruct (dj_asrc_fp ly S W mem _ hi Hs r Hr x Hx) as [Hin | (b & Hb & Hbx)].
            -- cbv beta in Hin. apply HGS; unfold ASRC in *; lia.
            -- exact (KT b x (HCSin i hi b Hi Hne Ehi Hb) Hbx).
          * intros b Hb. exact (KTL2 b (KTR b (HCSin i hi b Hi Hne Ehi Hb))).
        + destruct Hs as (Hz & Hw). split.
          * apply (akept_garr8 W mem); [|exact Hz]. intros x Hx. rewrite repeat_length in Hx.
            rewrite Z2Nat.id in Hx by (unfold ASRC; lia). apply HGS; unfold ASRC in *; lia.
          * apply (akept_awr W mem); [|exact Hw]. intros x Hx. apply HGS; unfold ASRC in *; lia. }
    split; [exact HREL2|].
    split; [exists ev'; exact HO1|].
    split; [apply (agone_at_kept fr_RG W mem W2 mem2 (lm_gn m) HGONE); intros r [<- | []] x Hx;
            cbn [fst snd] in Hx; apply KIMG; dcB_gk Hx|].
    split; [apply (alock_at_kept fr_RG W mem W2 mem2 true HLOCK); intros r [<- | []] x Hx;
            cbn [fst snd] in Hx; apply KIMG; right; exact Hx|].
    split; [apply (awake_at_kept fr_RG W mem W2 mem2 HWAKE); intros r [<- | []] x Hx;
            cbn [fst snd] in Hx; apply KIMG; dcB_gk Hx|].
    split; [apply (akept_vm W mem); [intros x Hx; apply KIMG; dcB_gk Hx | exact HNFD]|].
    split; [apply (akept_awr W mem); [intros x Hx; apply KIMG; dcB_gk Hx | exact HNFDW]|].
    split; [exact HNFDr|].
    split; [apply (akept_vm W mem); [intros x Hx; apply KIMG; dcB_gk Hx | exact HTUP]|].
    split; [destruct HLST as (lst & Hl); exists lst; apply (akept_vm W mem); [intros x Hx; apply KIMG; dcB_gk Hx | exact Hl]|].
    apply (akept_awr W mem); [intros x Hx; apply KIMG; dcB_gk Hx | exact HLSTW]. }
  assert (HPm1 : Permutation (ablocks B ly2 S2)
      (input_blks cx ++ model_blks (dr_m1 m j si h h' e' ev' LB out') ++ rest0)).
  { unfold dr_m1, dr_step, model_blks. cbn [lm_G lm_es lm_hs lm_cap lm_out]. unfold dr_cap1.
    apply (dcB_perm_post _ _ _ _ _ _ _ _ (dcB_CA (lm_es m) j) (dcB_CS (lm_hs m) si) rest _ HP2 HRT).
    - exact (dr_concat_set_nth_perm _ _ aentry_blks (lm_es m) j e' Hj).
    - pose proof (dr_concat_set_nth_perm _ _ slot_blks (lm_hs m) si (Some h') ltac:(lia)) as Hq.
      cbn [slot_blks] in Hq. exact Hq. }
  assert (HSEP1 : ablocks_sep B fr_FP cx (dr_m1 m j si h h' e' ev' LB out') ly2 S2).
  { split; [exists rest0; exact HPm1|].
    intros b Hb.
    assert (HbL2 : In b (ablocks B ly2 S2)).
    { apply (Permutation_in _ (Permutation_sym HPm1)). apply in_or_app. right. apply in_or_app. left. exact Hb. }
    destruct (in_dec dcB_dec b (ablocks B ly S)) as [HbS | HbS].
    - apply HSEP2.
      apply (Permutation_in _ HP1') in HbS. apply in_app_or in HbS as [HbX | HbR]; [exact (HXM b HbX)|].
      apply (Permutation_in _ HRT) in HbR. destruct HbR as [<- | HbT]; [unfold model_blks; left; reflexivity|].
      unfold dcB_T in HbT. apply in_app_or in HbT as [HbA | HbT].
      + unfold model_blks. right. apply in_or_app. left.
        apply (Permutation_in _ (Permutation_sym HCA)). apply in_or_app. right. exact HbA.
      + apply in_app_or in HbT as [HbC | HbT].
        * unfold model_blks. right. apply in_or_app. right. apply in_or_app. left.
          apply (Permutation_in _ (Permutation_sym HCS)). apply in_or_app. right. exact HbC.
        * exfalso. pose proof (Permutation_NoDup HPm1 HNDS2) as Hnd.
          apply in_app_or in HbT as [HbI | HbR0].
          -- exact (dcB_nd_app _ _ b Hnd HbI (in_or_app _ _ _ (or_introl Hb))).
          -- apply (dcB_nd_app (input_blks cx ++ model_blks (dr_m1 m j si h h' e' ev' LB out')) rest0 b);
               [rewrite <- app_assoc; exact Hnd | apply in_or_app; right; exact Hb | exact HbR0].
    - destruct (in_dec dcB_dec b (ablocks B (c_ly cx) (c_S cx))) as [HbE | HbE]; [right | left; exact HbE].
      intros a Ha. destruct b as [p n]. cbn [fst snd] in Ha.
      destruct (dr_blk B ARx LAWS BLKR ly2 S2 Hp2 W2 mem2 md2 p n HAR2 HbL2) as (_ & _ & Hn0).
      replace a with (p + (a - p)) by lia. apply (HGONE0 p n (a - p) HbE HbS). lia. }
  assert (HKY1 : Forall (fun e0 => Z.of_nat (length (re_keys e0)) <= re_nheld e0)
      (lm_es (dr_m1 m j si h h' e' ev' LB out'))).
  { unfold dr_m1, dr_step. cbn [lm_es]. apply Forall_forall. intros y Hy.
    destruct (dr_in_set_nth rentry j e' y (lm_es m) Hy) as [-> | Hy']; [exact HKE|].
    rewrite Forall_forall in HKY. exact (HKY y (dr_in_rm rentry j y (lm_es m) Hy')). }
  exists ly2, S2, Hp2, e', h', out', ev', LB.
  split; [|split; [|split]].
  - exists regs2, mem2, md2, (k + k1). split; [reflexivity|].
    split.
    { assert (PR2 : forall r : bv 5, acallee_saved (bv_unsigned r) ->
          In r [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv -> getr regs2 r = getr regs r)
        by (intros r H1 H2; rewrite (dj_pres _ _ r HPR H1); exact (KR3 r H2)).
      unfold dc_regs. rewrite !PR2 by first [dj_cs | dcB_in].
      repeat (split; [assumption|]). exact R25. }
    split; [exact HJ2|]. split; [exact HFF2|].
    split; [exact HFR2|]. split; [exact HFL2|]. split; [exact HIN2|]. split; [exact HRV2|]. split; [exact HJT2|].
    split; [exact SVN2|]. split; [exact S1922|]. split; [exact S402|].
    split; [exact HNE2|]. split; [exact HSEP1 | exact HKY1].
  - exact HMO.
  - exact HDF.
  - exact (conj EPRE (conj EKH (conj HPRE3 (conj HHN3 (conj CAP0 (conj (ex_intro _ rest (conj HP1 HP2))
      (conj EPOST (conj HPOST3 (conj DPOST (conj HNP2 HCNTc)))))))))).
Qed.

(* dcF_fin at R *)
Lemma dcF_finR : forall cx Hpe fpos ly S Hp (W : world segs) mem md k,
  ajournal_gx_xR segs B PST ARx R G_fr 0 [] LLVMF_STK (spZ (c_regs cx)) (lf_FP fr_FP cx)
    (c_ly cx) (c_S cx) Hpe (c_W cx) (c_mem cx) (c_md cx) [(1, fpos)] ly S Hp W mem md k ->
  In (1, fpos) (frames S).
Proof.
  intros cx Hpe fpos ly S Hp W mem md k HJ.
  pose proof HJ as (_ & _ & (memS & HJ0 & _) & _). pose proof HJ0 as (_ & _ & _ & _ & _ & Hfrs & _).
  rewrite Hfrs. left. reflexivity.
Qed.
(* dc_stC at R: pthread_mutex_unlock's strict realization, lifted by aj_gx_entry_at_xR *)
Lemma dc_stCR : forall cx Hpe t m j si fpos FF ly S Hp mc W c,
  lf_base_x B MT XM_LIB RLO RHI fr_live_pre LIBROOM NP G_fr ARx cx Hpe ->
  dc_atR cx Hpe t m j si fpos FF A_dc_r2 ly S Hp mc true 0 W c ->
  SRrG segs R W c (dc_atR cx Hpe t m j si fpos FF A_dc_r3 ly S Hp mc false 0).
Proof.
  intros cx Hpe t m j si fpos FF ly S Hp mc W c HB
    (regs & mem & md & k & -> & HR & HJ & HFF & HFR & HFL & HIN & HROM & HJT & SVN & S192 & S40 & HNE & HSEP & HKB).
  pose proof HR as (R2 & R8 & R9 & R18 & R19 & R20 & R23 & R24 & R26 & R3 & R4 & R27 & Ht & R21 & R22 & R25).
  pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  destruct (dcF_F cx Hpe HB) as (HFb & HF32 & Ho16 & Hsp0).
  assert (HAR : ARx ly S Hp W mem md) by (eapply ajournal_gx_AR_xR; exact HJ).
  pose proof (dcF_finR cx Hpe fpos ly S Hp W mem md k HJ) as Hfin.
  assert (HCTX : dc_ctxp cx m FF 0 (flag_addr ly 1 fpos) ly S W mem)
    by exact (conj HFR (conj HFL (conj HIN (conj HROM (conj HJT (conj SVN (conj S192 S40))))))).
  set (sp0 := spZ (c_regs cx)) in *.
  set (F := lf_F cx) in *.
  assert (VLK : rg_lock fr_RG = 0x5d8ac0) by reflexivity.
  pose proof HNE as (_ & _ & _ & _ & _ & HLOCK & _).
  pose proof HLOCK as (LK0 & LK4 & LK8 & LKW). unfold arm in LK0, LK4, LK8.
  assert (HNOWN : forall a, rg_lock fr_RG <= a < rg_lock fr_RG + 12 -> ~ aowned B ly S a).
  { intros a Ha Ho. destruct (HG a (HGlock a Ha)) as (Hi & Hno & _).
    apply Hno. exact (proj1 (alx_owned_image _ _ _ LAWS ly S Hp W mem _ a HAR Hi) Ho). }
  destruct (dc_cell_entry A_dc_r2 40 W regs mem F (rg_lock fr_RG) R9 R26 ltac:(lia) ltac:(lia) HF32
              ltac:(lia) ltac:(lia) ltac:(vm_compute; reflexivity) S40 ltac:(rewrite VLK; lia)) as [HS SHOK].
  remember (Eimg (Ereg regs (dc_cell_extra (rg_lock fr_RG)))) as E eqn:HE.
  assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
  assert (HAE : env_agree 32 (Ereg regs (dc_cell_extra (rg_lock fr_RG))) E)
    by (rewrite HE; split; [intros n Hn; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
  assert (E32 : ew E 32 = Z_to_bv 64 (rg_lock fr_RG))
    by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
  clear HE.
  paj_run_tok_x RUNG HS HJ SHOK DRspan.
  { unfold ss_dc_cell. cbn [ss_mem]. apply awr_ok_x_cons; [|apply awr_ok_x_nil].
    intros a Ha. cbn [dc_cell YP09.r_wlo YP09.r_whi] in Ha. lia. }
  dr_meq HF Em.
  pose proof (regs_kept_of_st_ok segs _ _ _ regs _ dcF_K HS HAE ltac:(vm_compute; reflexivity)) as KR.
  cbn [ms_regs restrict] in KR.
  prreg HS (1%bv : bv 5) Q1. prreg HS (10%bv : bv 5) Q10.
  rewrite E32 in Q10.
  pmkst HS. rewrite Em in *. clear HF HFr HG0.
  set (md1 := with_vm_backing (m_vm_lazy md) mat md) in *.
  set (regs1 := ms_regs ms) in *.
  assert (Hsp1 : spZ regs1 = F)
    by (unfold spZ; rewrite (KR 2%bv ltac:(cbv; tauto)), R2; unfold w64; apply unsigned_lit_small; lia).
  assert (Q1' : getr regs1 1 = Z_to_bv 64 (BASE + A_dc_r3)) by exact Q1.
  eapply (SRrG_bind segs R R_trans).
  { eapply (aj_gx_entry_at_xR B PST ARx LAWS R_trans WLE_R G_fr 0 [] ESTACK (SIGMA WS_pthread_mutex_unlock)
      (fun a => rg_lock fr_RG + 4 <= a < rg_lock fr_RG + 8)
      (fun regs' mem' => getr regs' 10 = w64 0 /\ val_mem segs (mrestrict (w_H W) mem') (rg_lock fr_RG + 4) 4 0)
      W regs1 mem LLVMF_STK sp0 (lf_FP fr_FP cx) (c_ly cx) (c_S cx) Hpe (c_W cx) (c_mem cx) (c_md cx)
      [(1, fpos)] ly S Hp md1 k (F - sp0) _ HG eq_refl HJ
      ltac:(rewrite Hsp1; lia) Ho16
      ltac:(lia) ltac:(lia) ltac:(unfold ESTACK, LLVMF_STK; lia)
      ltac:(rewrite (KR 3%bv ltac:(cbv; tauto)); exact R3) ltac:(rewrite (KR 4%bv ltac:(cbv; tauto)); exact R4) Q1'
      (ret_ok_codeptr_v A_dc_r3 ltac:(unfold A_dc_r3, A_dr_found, AF_fr_LLVMFuzzerTestOneInput; lia) eq_refl)).
    - intros a. lia.
    - intros a Hwa _. exact (dj_av_ne W mem (rg_lock fr_RG + 4) 4%nat 16 a LK4 ltac:(cbn; lia)).
    - intros a Hwa HnG. exfalso. apply HnG. apply HGlock. lia.
    - intros HPRE2 HSC2.
      exact (AUNLOCK ly S Hp W regs1 mem md1 (rg_lock fr_RG) HPRE2 Q10 ltac:(lia) ltac:(rewrite VLK; reflexivity) ltac:(lia)
        LK0 LK4 LK8
        ltac:(intros a Ha; split;
              [ destruct (Z_lt_le_dec a (rg_lock fr_RG + 4)) as [Hlt | Hge];
                [ exact (dj_av_ne W mem (rg_lock fr_RG) 4%nat 0 a LK0 ltac:(cbn; lia))
                | destruct (Z_lt_le_dec a (rg_lock fr_RG + 8)) as [Hlt2 | Hge2];
                  [ exact (dj_av_ne W mem (rg_lock fr_RG + 4) 4%nat 16 a LK4 ltac:(cbn; lia))
                  | exact (dj_av_ne W mem (rg_lock fr_RG + 8) 4%nat 0 a LK8 ltac:(cbn; lia)) ] ]
              | rewrite Hsp1; unfold ESTACK; lia ])
        ltac:(intros a Ha; split;
              [ replace a with (rg_lock fr_RG + (a - rg_lock fr_RG)) by lia; exact (LKW (a - rg_lock fr_RG) ltac:(lia))
              | split; [ apply HNOWN; lia | rewrite Hsp1; unfold ESTACK; lia ] ])
        (fun a Ha HK => proj2 (proj2 (HG a (HGlock a ltac:(lia)))) (proj1 (proj2 HK)))). }
  cbv beta. intros W2 c2 Hwle2 (-> & regs2 & mem2 & md2 & -> & HJa & HPa & (Ha0 & Hlk2) & Hfra & Hpresa).
  assert (KL : forall a, 0 <= a < 2 ^ 64 -> ~ (rg_lock fr_RG + 4 <= a < rg_lock fr_RG + 8) -> ~ (F - ESTACK <= a < F) ->
      aview segs (w_H W) mem2 a = aview segs (w_H W) mem a)
    by (intros a Ha H1 H2; apply Hfra; [exact Ha | exact H1 | replace (sp0 + (F - sp0)) with F by lia; exact H2]).
  pose proof (dj_ne_lockstep ly S Hp W mem md mem2 mc true false F HAR HKB HNE KL ltac:(unfold ESTACK; lia) Hlk2) as HNE2.
  destruct (dj_ctx_lockstep cx Hpe m FF 0 (flag_addr ly 1 fpos) ly S Hp W mem md mem2 HB HAR
              (ex_intro _ fpos (conj Hfin (eq_sym HFF))) HCTX KL Hpresa)
    as (HFR2 & HFL2 & HIN2 & HROM2 & HJT2 & SVN2 & S1922 & S402).
  apply (SRrG_ret segs R R_refl).
  exists regs2, mem2, md2, k.
  split; [reflexivity|].
  split; [exact (dcF_regs_kept cx t m j si FF regs regs2
                   (fun r Hr => eq_trans (dcF_pres_K regs1 regs2 HPa r Hr) (KR r Hr)) HR)|].
  split; [exact HJa|]. split; [exact HFF|].
  split; [exact HFR2|]. split; [exact HFL2|]. split; [exact HIN2|]. split; [exact HROM2|]. split; [exact HJT2|].
  split; [exact SVN2|]. split; [exact S1922|]. split; [exact S402|].
  split; [exact HNE2|]. split; [exact HSEP|]. exact HKB.
Qed.
(* a leaf callee's strict journal (aleaf_post's, empty own) as the gx journal at R that dr_callZR composes *)
Lemma dc_leaf_jR : forall STK sp ly S Hp (W W' : world segs) mem mem' md md',
  ajournal_x segs B PST ARx STK sp [] ly S Hp W mem md [] ly S Hp W' mem' md' 0 ->
  ajournal_gx_xR segs B PST ARx R G_fr 0 [] STK sp [] ly S Hp W mem md [] ly S Hp W' mem' md' 0.
Proof.
  intros STK sp ly S Hp W W' mem mem' md md' HJc.
  apply (ajournal_gx_G_mono_xR segs B PST ARx [] G_fr); [intros a Ha; exfalso; exact (inG_nil a Ha)|].
  apply ajournal_gx_nil_xR.
  eapply (ajournal_xR_mono segs B PST ARx (@wle segs) R WLE_R). exact HJc.
Qed.
(* dc_stD at R: check_no_loss_read's strict spec, lifted by SRr_SRrG (WLE_R) *)
Lemma dc_stDR : forall cx Hpe t m j si fpos FF ly S Hp mc h1 W c,
  lf_base_x B MT XM_LIB RLO RHI fr_live_pre LIBROOM NP G_fr ARx cx Hpe ->
  (si < 4)%nat -> nth si (lm_hs mc) None = Some h1 -> hl_recs (hs_pending h1) = [] ->
  dc_atR cx Hpe t m j si fpos FF A_dc_r3 ly S Hp mc false 0 W c ->
  SRrG segs R W c (dc_atR cx Hpe t m j si fpos FF A_dc_r4 ly S Hp mc false 0).
Proof.
  intros cx Hpe t m j si fpos FF ly S Hp mc h1 W c HB Hsi Hh1 Hpend
    (regs & mem & md & k & -> & HR & HJ & HFF & HFR & HFL & HIN & HROM & HJT & SVN & S192 & S40 & HNE & HSEP & HKB).
  pose proof HR as (R2 & R8 & R9 & R18 & R19 & R20 & R23 & R24 & R26 & R3 & R4 & R27 & Ht & R21 & R22 & R25).
  pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  destruct (dcF_F cx Hpe HB) as (HFb & HF32 & Ho16 & Hsp0).
  pose proof (dcF_finR cx Hpe fpos ly S Hp W mem md k HJ) as Hfin.
  assert (HCTX : dc_ctxp cx m FF 0 (flag_addr ly 1 fpos) ly S W mem)
    by exact (conj HFR (conj HFL (conj HIN (conj HROM (conj HJT (conj SVN (conj S192 S40))))))).
  set (sp0 := spZ (c_regs cx)) in *.
  set (F := lf_F cx) in *.
  set (HA := rg_s fr_RG + ASRC * Z.of_nat si) in *.
  assert (VS : rg_s fr_RG = 0x5d88e0) by reflexivity.
  pose proof HNE as (_ & HSL & _).
  pose proof (HSL si Hsi) as HSLi. rewrite Hh1 in HSLi.
  destruct HSLi as (_ & _ & _ & _ & _ & _ & _ & _ & _ & HPL & _).
  destruct HPL as (_ & HPn & _).
  assert (HV0 : val_mem segs (mrestrict (w_H W) mem) (HA + 24) 4 0).
  { replace (HA + 24) with (HA + 16 + 8) by lia. unfold hl_n in HPn. rewrite Hpend in HPn. exact HPn. }
  assert (HPm : HA mod 16 = 0).
  { unfold HA. rewrite VS. unfold ASRC.
    replace (0x5d88e0 + 96 * Z.of_nat si) with ((0x5d88e + 6 * Z.of_nat si) * 16) by lia. apply Z_mod_mult. }
  assert (HAZ : azs B HA 28) by (apply (dcF_azs_sub _ _ _ _ HZS); unfold HA, ASRC; lia).
  destruct HAP as (HAP0 & HAP32).
  destruct (dc_plain_entry A_dc_r3 W regs mem R26) as [HS SHOK].
  remember (Eimg (Ereg regs [])) as E eqn:HE.
  assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
  assert (HAE : env_agree 32 (Ereg regs []) E)
    by (rewrite HE; split; [intros n Hn; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
  assert (EEo : forall q (rr : bv 5), Z.of_nat q = bv_unsigned rr -> ew E q = getr regs rr)
    by (intros q rr Hq; subst E; pose proof (bv_unsigned_in_range 5 rr) as Hr5; change (bv_modulus 5) with 32 in Hr5;
        rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_nat; exact Hq).
  clear HE.
  paj_run_to_tok_x RUNTOG HS HJ SHOK DRspan AF_fr_check_no_loss_read.
  { apply awr_ok_x_nil. }
  dr_meq HF Em.
  pose proof (regs_kept_of_st_ok_pi _ _ _ regs _ dcF_K HS HAE ltac:(vm_compute; reflexivity)) as KR.
  cbn [ms_regs restrict] in KR.
  prreg HS (1%bv : bv 5) Q1. prreg HS (10%bv : bv 5) Q10.
  rewrite (EEo 21%nat 21%bv eq_refl), R21 in Q10.
  pmkst HS. rewrite Em in *. clear HF HFr HG0.
  set (md1 := with_vm_backing (m_vm_lazy md) mat md) in *.
  set (regs1 := ms_regs ms) in *.
  assert (Hsp1 : spZ regs1 = F)
    by (unfold spZ; rewrite (KR 2%bv ltac:(cbv; tauto)), R2; unfold w64; apply unsigned_lit_small; lia).
  assert (Q1' : getr regs1 1 = Z_to_bv 64 (BASE + A_dc_r4)) by exact Q1.
  destruct (dr_afn_pre_atR cx Hpe ly S Hp fpos k W mem md1 regs1 CNLR_STK HB HJ
              ltac:(rewrite HFF; exact (dr_aframe_false cx FF W mem HFR)) Hsp1
              ltac:(rewrite Q1'; exact (ret_ok_codeptr_v A_dc_r4
                      ltac:(unfold A_dc_r4, A_dr_found, AF_fr_LLVMFuzzerTestOneInput; lia) eq_refl))
              ltac:(unfold raZ; rewrite Q1', unsigned_lit_small; unfold A_dc_r4, A_dr_found, AF_fr_LLVMFuzzerTestOneInput; lia)
              ltac:(rewrite (KR 3%bv ltac:(cbv; tauto)); exact R3) ltac:(rewrite (KR 4%bv ltac:(cbv; tauto)); exact R4)
              ltac:(rewrite (KR 8%bv ltac:(cbv; tauto)); exact R8)
              ltac:(unfold CNLR_STK; lia) ltac:(unfold CNLR_STK, LLVMF_STK; lia)) as (ch & HPRE1).
  eapply (SRrG_mono segs R).
  { eapply (dr_callZR G_fr W regs1 mem (Z_to_bv 64 (BASE + AF_fr_check_no_loss_read)) LLVMF_STK sp0 (lf_FP fr_FP cx)
      (c_ly cx) (c_S cx) Hpe (c_W cx) (c_mem cx) (c_md cx) [(1, fpos)] ly S Hp md1 k CNLR_STK [] 0 [] (F - sp0)
      (Z_to_bv 64 (BASE + A_dc_r4)) ch
      (fun ly2 S2 Hp2 W2 _ mem2 md2 => ly2 = ly /\ S2 = S /\ Hp2 = Hp /\ ajournal_x segs B PST ARx CNLR_STK F [] ly S Hp W mem md1 [] ly S Hp W2 mem2 md2 0)
      HG HJ ltac:(rewrite Hsp1; lia) ltac:(lia) ltac:(unfold CNLR_STK, LLVMF_STK; lia) ltac:(lia) ltac:(lia)
      ltac:(intros a Ha; exfalso; exact (inFP_nil a Ha)) Q1' HPRE1).
    - eapply (SRrG_mono segs R);
        [exact (SRr_SRrG segs R WLE_R _ _ _
                  (CNLR W ly S Hp regs1 mem md1 ch HA 0 HPRE1 Q10 HPm ltac:(unfold HA, ASRC; lia) ltac:(unfold HA, ASRC; lia) HAZ
                     ltac:(unfold HA, ASRC in *; lia) ltac:(unfold HA, ASRC in *; lia) HV0 ltac:(lia) ltac:(left; reflexivity)))|].
      cbv beta. intros W2 c2 _ (regs2 & mem2 & md2 & -> & HJc & HP2 & _ & _).
      rewrite Hsp1 in HJc.
      exists ly, S, Hp, regs2, mem2, md2, 0.
      split; [rewrite Q1'; reflexivity|].
      split; [rewrite Hsp1; exact (dc_leaf_jR _ _ _ _ _ _ _ _ _ _ _ HJc)|].
      split; [exact HP2|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. exact HJc.
    - intros a Ha. exfalso. exact (inFP_nil a Ha). }
  cbv beta. intros W2 c2 _ (ly2 & S2 & Hp2 & regs2 & mem2 & md2 & k1 & -> & HJ2 & _ & HP2 & (-> & -> & -> & HJp)).
  pose proof (dj_ne_plain ly S Hp W W2 mem mem2 md1 md2 mc false CNLR_STK F HJp ltac:(unfold CNLR_STK; lia) HKB HNE) as HNE2.
  destruct (dj_ctx_plain cx Hpe m FF 0 (flag_addr ly 1 fpos) ly S Hp W W2 mem mem2 md1 md2 CNLR_STK HB HJp
              ltac:(unfold CNLR_STK; lia) (ex_intro _ fpos (conj Hfin (eq_sym HFF))) HCTX)
    as (HFR2 & HFL2 & HIN2 & HROM2 & HJT2 & SVN2 & S1922 & S402).
  exists regs2, mem2, md2, (k + k1).
  split; [reflexivity|].
  split; [exact (dcF_regs_kept cx t m j si FF regs regs2
                   (fun r Hr => eq_trans (dcF_pres_K regs1 regs2 HP2 r Hr) (KR r Hr)) HR)|].
  split; [exact HJ2|]. split; [exact HFF|].
  split; [exact HFR2|]. split; [exact HFL2|]. split; [exact HIN2|]. split; [exact HROM2|]. split; [exact HJT2|].
  split; [exact SVN2|]. split; [exact S1922|]. split; [exact S402|].
  split; [exact HNE2|]. split; [exact HSEP|]. exact HKB.
Qed.
(* dc_stF at R: check_shape_done's strict spec, lifted by SRr_SRrG (WLE_R) *)
Lemma dc_stFR : forall cx Hpe t m j si fpos FF ly S Hp mc W c,
  lf_base_x B MT XM_LIB RLO RHI fr_live_pre LIBROOM NP G_fr ARx cx Hpe ->
  dr_at_op cx m -> NP S ->
  (forall ev, RINV cx (t + 1) (dc_fin cx m mc ev)) -> (forall ev, LSx cx (t + 1) (dc_fin cx m mc ev) ly S) ->
  dc_atR cx Hpe t m j si fpos FF A_dc_r5 ly S Hp mc false (Z.of_nat (length (lm_O mc))) W c ->
  SRrG segs R W c (DSTR A_dr_join cx Hpe (t + 1) (lregs_join cx t)).
Proof.
  intros cx Hpe t m j si fpos FF ly S Hp mc W c HB Hatop HNP HRI HLS
    (regs & mem & md & k & -> & HR & HJ & HFF & HFR & HFL & HIN & HROM & HJT & SVN & S192 & S40 & HNE & HSEP & HKB).
  pose proof HR as (R2 & R8 & R9 & R18 & R19 & R20 & R23 & R24 & R26 & R3 & R4 & R27 & Ht & R21 & R22 & R25).
  pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  destruct (dcF_F cx Hpe HB) as (HFb & HF32 & Ho16 & Hsp0).
  assert (HAR : ARx ly S Hp W mem md) by (eapply ajournal_gx_AR_xR; exact HJ).
  pose proof (dcF_finR cx Hpe fpos ly S Hp W mem md k HJ) as Hfin.
  assert (Hk' : 0 <= dr_k' cx m <= c_n cx)
    by (pose proof Hatop as (Hk0 & _ & _); unfold dr_k'; destruct (Z.ltb_spec (lm_k m + 1) (c_n cx)); lia).
  pose proof HNE as (_ & _ & _ & (ev0 & HOUT0) & _).
  destruct HOUT0 as (_ & _ & HNO & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
                     _ & Hcap).
  unfold arm in HNO.
  assert (HA : 0 <= Z.of_nat (length (lm_O mc)) < 2 ^ 64).
  { destruct Hcap as [(_ & _ & Hz) | (Hc0 & Hle & Hin & _)]; [lia|].
    destruct (dr_blk B ARx LAWS BLKR ly S Hp W mem md _ _ HAR Hin) as (Hb1 & Hb2 & Hb3). lia. }
  assert (VN : VAL A_g_nout = rg_nout fr_RG) by (vm_compute; reflexivity).
  assert (HCTX : dc_ctxp cx m FF (Z.of_nat (length (lm_O mc))) (flag_addr ly 1 fpos) ly S W mem)
    by exact (conj HFR (conj HFL (conj HIN (conj HROM (conj HJT (conj SVN (conj S192 S40))))))).
  set (sp0 := spZ (c_regs cx)) in *.
  set (F := lf_F cx) in *.
  set (NO := Z.of_nat (length (lm_O mc))) in *.
  destruct (dc_cell_entry A_dc_r5 192 W regs mem F NO R9 R26 ltac:(lia) ltac:(lia) HF32
              ltac:(lia) ltac:(lia) ltac:(vm_compute; reflexivity) S192 HA) as [HS SHOK].
  remember (Eimg (Ereg regs (dc_cell_extra NO))) as E eqn:HE.
  assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
  assert (HAE : env_agree 32 (Ereg regs (dc_cell_extra NO)) E)
    by (rewrite HE; split; [intros n Hn; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
  assert (E32 : ew E 32 = Z_to_bv 64 NO)
    by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
  clear HE.
  paj_run_to_tok_x RUNTOG HS HJ SHOK DRspan AF_fr_check_shape_done.
  { unfold ss_dc_cell. cbn [ss_mem]. apply awr_ok_x_cons; [|apply awr_ok_x_nil].
    intros a Ha. cbn [dc_cell YP09.r_wlo YP09.r_whi] in Ha. lia. }
  dr_meq HF Em.
  pose proof (regs_kept_of_st_ok_pi _ _ _ regs _ dcF_K HS HAE ltac:(vm_compute; reflexivity)) as KR.
  cbn [ms_regs restrict] in KR.
  prreg HS (1%bv : bv 5) Q1. prreg HS (10%bv : bv 5) Q10.
  rewrite E32 in Q10.
  pmkst HS. rewrite Em in *. clear HF HFr HG0.
  set (md1 := with_vm_backing (m_vm_lazy md) mat md) in *.
  set (regs1 := ms_regs ms) in *.
  assert (Hsp1 : spZ regs1 = F)
    by (unfold spZ; rewrite (KR 2%bv ltac:(cbv; tauto)), R2; unfold w64; apply unsigned_lit_small; lia).
  assert (Q1' : getr regs1 1 = Z_to_bv 64 (BASE + A_dr_join)) by exact Q1.
  destruct (dr_afn_pre_atR cx Hpe ly S Hp fpos k W mem md1 regs1 CSD_STK HB HJ
              ltac:(rewrite HFF; exact (dr_aframe_false cx FF W mem HFR)) Hsp1
              ltac:(rewrite Q1'; exact (ret_ok_codeptr_v A_dr_join
                      ltac:(unfold A_dr_join, AF_fr_LLVMFuzzerTestOneInput; lia) eq_refl))
              ltac:(unfold raZ; rewrite Q1', unsigned_lit_small; unfold A_dr_join, AF_fr_LLVMFuzzerTestOneInput; lia)
              ltac:(rewrite (KR 3%bv ltac:(cbv; tauto)); exact R3) ltac:(rewrite (KR 4%bv ltac:(cbv; tauto)); exact R4)
              ltac:(rewrite (KR 8%bv ltac:(cbv; tauto)); exact R8)
              ltac:(unfold CSD_STK; lia) ltac:(unfold CSD_STK, LLVMF_STK; lia)) as (ch & HPRE1).
  eapply (SRrG_mono segs R).
  { eapply (dr_callZR G_fr W regs1 mem (Z_to_bv 64 (BASE + AF_fr_check_shape_done)) LLVMF_STK sp0 (lf_FP fr_FP cx)
      (c_ly cx) (c_S cx) Hpe (c_W cx) (c_mem cx) (c_md cx) [(1, fpos)] ly S Hp md1 k CSD_STK [] 0 [] (F - sp0)
      (Z_to_bv 64 (BASE + A_dr_join)) ch
      (fun ly2 S2 Hp2 W2 _ mem2 md2 => ly2 = ly /\ S2 = S /\ Hp2 = Hp /\ ajournal_x segs B PST ARx CSD_STK F [] ly S Hp W mem md1 [] ly S Hp W2 mem2 md2 0)
      HG HJ ltac:(rewrite Hsp1; lia) ltac:(lia) ltac:(unfold CSD_STK, LLVMF_STK; lia) ltac:(lia) ltac:(lia)
      ltac:(intros a Ha; exfalso; exact (inFP_nil a Ha)) Q1' HPRE1).
    - eapply (SRrG_mono segs R);
        [exact (SRr_SRrG segs R WLE_R _ _ _ (CSD W ly S Hp regs1 mem md1 ch NO HPRE1 Q10 HA ltac:(rewrite VN; exact HNO)))|].
      cbv beta. intros W2 c2 _ (regs2 & mem2 & md2 & -> & HJc & HP2 & _ & _).
      rewrite Hsp1 in HJc.
      exists ly, S, Hp, regs2, mem2, md2, 0.
      split; [rewrite Q1'; reflexivity|].
      split; [rewrite Hsp1; exact (dc_leaf_jR _ _ _ _ _ _ _ _ _ _ _ HJc)|].
      split; [exact HP2|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. exact HJc.
    - intros a Ha. exfalso. exact (inFP_nil a Ha). }
  cbv beta. intros W2 c2 _ (ly2 & S2 & Hp2 & regs2 & mem2 & md2 & k1 & -> & HJ2 & _ & HP2 & (-> & -> & -> & HJp)).
  pose proof (dj_ne_plain ly S Hp W W2 mem mem2 md1 md2 mc false CSD_STK F HJp ltac:(unfold CSD_STK; lia) HKB HNE) as HNE2.
  destruct (dj_ctx_plain cx Hpe m FF NO (flag_addr ly 1 fpos) ly S Hp W W2 mem mem2 md1 md2 CSD_STK HB HJp
              ltac:(unfold CSD_STK; lia) (ex_intro _ fpos (conj Hfin (eq_sym HFF))) HCTX)
    as (HFR2 & HFL2 & HIN2 & HROM2 & HJT2 & SVN2 & S1922 & S402).
  destruct HNE2 as (N1 & N2 & N3 & (ev & N4) & N5 & N6 & N7 & N8 & N9 & N10 & N11 & N12 & N13).
  pose proof (dcF_regs_kept cx t m j si FF regs regs2
                (fun r Hr => eq_trans (dcF_pres_K regs1 regs2 HP2 r Hr) (KR r Hr)) HR)
    as (R2' & R8' & R9' & R18' & R19' & R20' & R23' & R24' & R26' & R3' & R4' & R27' & Ht' & R21' & R22' & R25').
  exists regs2, mem2, md2.
  split; [reflexivity|].
  split; [exact HJT2|].
  exists [(1, fpos)], ly, S, Hp, (k + k1), (dc_fin cx m mc ev), fpos.
  split; [exact HJ2|]. split; [reflexivity|]. split; [rewrite HFF; exact HFR2|]. split; [rewrite HFF; exact HFL2|].
  split; [exact (conj N1 (conj N2 (conj N3 (conj N4 (conj N5 (conj N6 (conj N7 (conj N8 (conj N9 (conj N10
                   (conj N11 (conj N12 N13))))))))))))|].
  split; [exact HIN2|]. split; [exact HROM2|].
  split; [exact HSEP|]. split; [exact (HLS ev)|]. split; [exact HNP|]. split; [exact (HRI ev)|].
  rewrite HFF.
  exact (conj R2' (conj R8' (conj R9' (conj R18' (conj R19' (conj R20' (conj R23' (conj R24' (conj R26' (conj R3'
    (conj R4' (conj R27' (conj Ht' (conj R25' (conj SVN2 Hk'))))))))))))))).
Qed.
(* dcE_kept at R (a callee's journal at R) *)
Lemma dcE_keptR : forall Gc XO OUT STK sp FP ly S Hp (W : world segs) mem md ly' S' Hp' (W' : world segs) mem' md' kk a,
  gx_ok segs B Gc ->
  ajournal_gx_xR segs B PST ARx R Gc XO OUT STK sp FP ly S Hp W mem md [] ly' S' Hp' W' mem' md' kk ->
  0 <= a < 2 ^ 64 -> ~ inG Gc a -> (in_img segs a -> inG G_fr a) ->
  ((alloc_ceiling <= a /\ ~ (sp - STK <= a < sp + XO)) \/
   (sp <= a < sp + XO /\ ~ inFP OUT a) \/
   (exists p n, In (p, n) (ablocks B ly S) /\ In (p, n) (ablocks B ly' S') /\ p <= a < p + req_size n /\
      ~ inFP FP a) \/
   (in_img segs a /\ ~ Exists (in_zr a) (as_owned_static B) /\ ~ (as_errno B <= a < as_errno B + 4) /\
      fp_spares FP a) \/
   (exists cid pos, In (cid, pos) (frames S) /\
      (in_zr a (frame_rng ly (cid, pos)) \/ in_zr a (shadow_addr (frame_addr ly cid pos), fs_frame_bytes cid / 8)) /\
      ~ inFP FP a)) ->
  abyte_kept W mem W' mem' a.
Proof.
  intros Gc XO OUT STK sp FP ly S Hp W mem md ly' S' Hp' W' mem' md' kk a HGx HJX Ha HnG Hig Hc.
  apply (dj_bk W W' mem mem' a Ha Hig).
  exact (dj_keepR Gc XO OUT STK sp FP ly S Hp W mem md [] ly' S' Hp' W' mem' md' kk a HGx HJX Ha HnG Hc).
Qed.
(* Section dcE_keep at R: check_no_loss's journal at R *)
Section dcE_keepR.
Variables (Gc : list (Z * Z)) (XO : Z) (OUT : list (Z * Z)) (STK sp : Z) (L : list (Z * Z)).
Variables (ly : alayout) (S : astate) (Hp : list Z) (W : world segs) (mem : word -> option byte) (md : Model).
Variables (ly' : alayout) (S' : astate) (Hp' : list Z) (W' : world segs) (mem' : word -> option byte) (md' : Model) (kk : Z).
Hypothesis KGx : gx_ok segs B Gc.
Hypothesis KJ : ajournal_gx_xR segs B PST ARx R Gc XO OUT STK sp (blk_FP L) ly S Hp W mem md [] ly' S' Hp' W' mem' md' kk.
Hypothesis KAR : ARx ly S Hp W mem md.
Hypothesis KL : forall b, In b L -> In b (ablocks B ly S).
Lemma dcE_kept_blkR : forall p n a,
  In (p, n) (ablocks B ly S) -> In (p, n) (ablocks B ly' S') -> ~ In (p, n) L -> p <= a < p + req_size n ->
  abyte_kept W mem W' mem' a.
Proof.
  intros p n a H1 H2 Hnot Ha.
  destruct (alx_blocks _ _ _ LAWS ly S Hp W mem md p n KAR H1) as (_ & H4 & Hc & _).
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  assert (Hni : ~ in_img segs a) by exact (blk_img_x segs B ARx LAWS ly S Hp W mem md p n a KAR H1 Ha).
  apply (dcE_keptR Gc XO OUT STK sp (blk_FP L) ly S Hp W mem md ly' S' Hp' W' mem' md' kk a KGx KJ);
    [lia | intros HGa; exact (Hni (proj1 (KGx a HGa))) | intros Hi; exact (False_ind _ (Hni Hi)) |].
  right; right; left. exists p, n. repeat split; try assumption; try lia.
  exact (dcE_notFP ly S Hp W mem md L p n a KAR KL H1 Hnot Ha).
Qed.
Lemma dcE_kept_imgR : forall a, inG G_fr a -> ~ inG Gc a -> ~ (as_errno B <= a < as_errno B + 4) ->
  abyte_kept W mem W' mem' a.
Proof.
  intros a HGa HnG He. destruct (HG a HGa) as (Hi & Hno & _).
  pose proof (pa_segs_low a Hi) as Hlo. pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  apply (dcE_keptR Gc XO OUT STK sp (blk_FP L) ly S Hp W mem md ly' S' Hp' W' mem' md' kk a KGx KJ);
    [lia | exact HnG | intros _; exact HGa |].
  right; right; right; left. split; [exact Hi|]. split; [exact Hno|]. split; [exact He|].
  apply fp_spares_closed. exact (dcE_fp_closed ly S Hp W mem md L KAR KL).
Qed.
Lemma dcE_kept_frameR : forall cid pos a, In (cid, pos) (frames S) ->
  (in_zr a (frame_rng ly (cid, pos)) \/ in_zr a (shadow_addr (frame_addr ly cid pos), fs_frame_bytes cid / 8)) ->
  abyte_kept W mem W' mem' a.
Proof.
  intros cid pos a Hfr Hr.
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  destruct (frames_bounds_x segs B ARx LAWS ly S Hp W mem md cid pos KAR Hfr) as (Hf0 & Hfc & Hfh).
  pose proof (fs_frame_bytes_nonneg cid) as Hfs.
  pose proof (shadow_addr_bounds (frame_addr ly cid pos) ltac:(zlia)) as SB1.
  pose proof (shadow_addr_bounds (frame_addr ly cid pos + fs_frame_bytes cid) ltac:(zlia)) as SB2.
  pose proof (shadow_range_end (frame_addr ly cid pos) (fs_frame_bytes cid) (fs_frame_bytes_nonneg cid)) as SB3.
  assert (Hni : ~ in_img segs a).
  { intros Hi. destruct Hr as [Hr | Hr].
    - exact (frm_img_x segs B ARx LAWS ly S Hp W mem md cid pos a KAR Hfr Hr Hi).
    - pose proof (pa_segs_low a Hi). unfold in_zr in Hr. cbn [fst snd] in Hr. zlia. }
  apply (dcE_keptR Gc XO OUT STK sp (blk_FP L) ly S Hp W mem md ly' S' Hp' W' mem' md' kk a KGx KJ);
    [ unfold frame_rng, in_zr in Hr; cbn [fst snd] in Hr; destruct Hr as [Hr | Hr]; zlia
    | intros HGa; exact (Hni (proj1 (KGx a HGa))) | intros Hi; exact (False_ind _ (Hni Hi)) |].
  right; right; right; right. exists cid, pos. split; [exact Hfr|]. split; [exact Hr|].
  intros (r & Hrin & Hra). unfold blk_FP in Hrin. apply in_map_iff in Hrin as ([b m] & <- & Hb). cbn [fst snd] in Hra.
  pose proof (KL _ Hb) as Hbin.
  destruct (alx_blocks _ _ _ LAWS ly S Hp W mem md b m KAR Hbin) as (_ & _ & _ & [Hh1 Hh2] & _).
  pose proof (sep_block_frame_x segs B ARx LAWS ly S Hp W mem md b m cid pos KAR Hbin Hfr) as Hd.
  unfold zdisjoint, frame_rng, in_zr in Hd, Hr. cbn [fst snd] in Hd, Hr.
  destruct Hr as [Hr|Hr]; zlia.
Qed.
End dcE_keepR.

(* dc_stE at R: check_no_loss at its R spec (the strict proof's block list R is RB here, R being the relation) *)
Lemma dc_stER : forall cx Hpe t m j si fpos FF ly S Hp mc h1 W c,
  lf_base_x B MT XM_LIB RLO RHI fr_live_pre LIBROOM NP G_fr ARx cx Hpe ->
  (si < 4)%nat -> nth si (lm_hs mc) None = Some h1 ->
  NoDup (texts (hs_held h1)) -> hl_n (hs_expected h1) < 2 ^ 26 ->
  hl_n (hs_held h1) + Z.of_nat (count_begin (texts (hs_expected h1))) < 2 ^ 22 ->
  cnl_room MMAX (blocks_bytes S) (texts (hs_held h1)) (hl_cap (hs_held h1)) (hl_recs (hs_expected h1)) ->
  mo_ok MT S (cnl_cost MT (hs_expected h1) (hs_held h1)) ->
  AREC * capb (hs_held h1) (hs_expected h1) < 2 ^ 32 ->
  NP S -> cnt_ok_pk RP (cnl_pk (hs_expected h1) (hs_held h1)) (ablocks B ly S) ->
  (lm_gn mc = 0 -> exists rest, lm_O mc = bstream (hs_expected h1) ++ rest) ->
  dc_atR cx Hpe t m j si fpos FF A_dc_r4 ly S Hp mc false 0 W c ->
  SRrG segs R W c (fun W' c' => exists ly' S' Hp' E' H',
    dc_atR cx Hpe t m j si fpos FF A_dc_r5 ly' S' Hp' (dc_setsrc mc si (set_exp_held h1 E' H')) false
      (if lm_gn mc =? 0 then Z.of_nat (length (bstream (hs_expected h1))) else 0) W' c' /\
    mo_le MT S S' (cnl_cost MT (hs_expected h1) (hs_held h1)) /\
    dr_cfun h1 E' H' /\ NP S' /\
    (forall rest, Permutation (ablocks B ly S) (list_blks (hs_expected h1) ++ list_blks (hs_held h1) ++ rest) ->
       Permutation (ablocks B ly' S') (list_blks E' ++ list_blks H' ++ rest)) /\
    hl_n H' <= hl_cap H').
Proof.
  intros cx Hpe t m j si fpos FF ly S Hp mc h1 W c HB Hsi Hh1 HND HnE HnH HROOM HMO HCAPB HNPs HCNTc HOB
    (regs & mem & md & k & -> & DR & HJ & HFF & HFR & HFL & HIN & HRV & HROM & SVN & SAT & SLK & HMOD & HSEP & HKY).
  pose proof DR as DR0.
  destruct DR as (R2 & R8 & R9 & R18 & R19 & R20 & R23 & R24 & R26 & R3 & R4 & R27 & Ht & R21 & R22 & R25).
  pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs.
  pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  pose proof dr_ceil_lo as HCL.
  assert (HAR : ARx ly S Hp W mem md) by (eapply ajournal_gx_AR_xR; exact HJ).
  pose proof HB as (HAI & HPRE).
  pose proof HPRE as (HFNP & _ & _ & _ & _ & Hnlen & _).
  pose proof HFNP as (_ & _ & _ & _ & _ & Hstk & _).
  pose proof Hstk as (Hal16 & _ & Hceil & Hslo & Hshi & H47 & _ & Htop & _).
  unfold LLVMF_STK in Hslo.
  assert (HFb : spZ (c_regs cx) - 352 < lf_F cx <= spZ (c_regs cx) - 320).
  { unfold lf_F. pose proof (Z.mod_pos_bound (spZ (c_regs cx) - 320) 32 ltac:(lia)). lia. }
  assert (HF32 : lf_F cx mod 32 = 0).
  { unfold lf_F. rewrite Zminus_mod, Z.mod_mod, Z.sub_diag by lia. reflexivity. }
  pose proof (pal_env B TL) as ((HE0 & HE1) & _).
  set (sp0 := spZ (c_regs cx)) in *.
  set (F := lf_F cx) in *.
  assert (Hsp : spZ regs = F) by (unfold spZ; rewrite R2; unfold w64; apply unsigned_lit_small; unfold DR_CEIL8 in *; lia).
  destruct (dc_plain_entry A_dc_r4 W regs mem R26) as [HS SHOK].
  remember (Eimg (Ereg regs [])) as E eqn:HE.
  assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
  assert (HAE : env_agree 32 (Ereg regs []) E)
    by (rewrite HE; split; [intros n Hn; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
  clear HE.
  paj_run_to_tok_x RUNTOG HS HJ SHOK DRspan AF_fr_check_no_loss.
  { apply awr_ok_x_nil. }
  dr_meq HF Em.
  pose proof (regs_kept_of_st_ok_pi _ _ _ regs _ [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv
                HS HAE ltac:(vm_compute; reflexivity)) as KR3.
  cbn [ms_regs restrict] in KR3.
  prreg HS (1%bv : bv 5) Q1. prreg HS (10%bv : bv 5) Q10. prreg HS (11%bv : bv 5) Q11.
  pmkst HS. rewrite Em in *. clear HF HFr HG0.
  set (regsc := ms_regs ms) in *.
  set (mdc := with_vm_backing (m_vm_lazy md) mat md) in *.
  pose proof dcE_rg as (Es & Esrc & Ensrc & Ecap & Eout & Enout & Ecapout & Esmax & Eseintr & Esdead & Egone & Eclient
    & Ecb & Elock & Ewake).
  pose proof dcE_vals as (Vnout & Vout & Vgone & Vs).
  assert (EASRC : ASRC = 96) by reflexivity.
  set (HA := rg_s fr_RG + ASRC * Z.of_nat si) in *.
  assert (EHA : HA = rg_s fr_RG + ASRC * Z.of_nat si) by reflexivity.
  assert (HFlo : DR_CEIL8 + 32000 <= F) by (unfold DR_CEIL8; lia).
  assert (E21 : ew E 21 = getr regs 21)
    by (rewrite (proj1 HAE 21%nat ltac:(apply Nat.ltb_lt; reflexivity)); apply ew_Ereg_nat; reflexivity).
  assert (E9 : ew E 9 = getr regs 9)
    by (rewrite (proj1 HAE 9%nat ltac:(apply Nat.ltb_lt; reflexivity)); apply ew_Ereg_nat; reflexivity).
  assert (Rc10 : getr regsc 10 = w64 HA) by (rewrite Q10, E21; exact R21).
  assert (Rc11 : getr regsc 11 = w64 (F + 192)).
  { rewrite Q11, E9, R9. unfold w64. rewrite unsigned_lit_small by (unfold DR_CEIL8 in *; lia). reflexivity. }
  assert (Hspc : spZ regsc = F).
  { unfold spZ. rewrite (KR3 2%bv ltac:(dcE_infp)). exact Hsp. }
  assert (HJin : exists memS, ajournal_xR segs B PST ARx R LLVMF_STK sp0 (lf_FP fr_FP cx) (c_ly cx) (c_S cx) Hpe (c_W cx) memS (c_md cx)
      [(1, fpos)] ly S Hp W mem mdc k).
  { pose proof HJ as (_ & _ & (memS & HJ0 & _) & _). rewrite !Z.add_0_r in HJ0. exists memS. exact HJ0. }
  destruct HJin as (memS & HJ0).
  pose proof HJ0 as (HARc & HLY & _ & _ & _ & HFRS0 & _ & _ & _ & _ & _ & _ & HJgone & HJpres & _).
  assert (Etop : ly_top ly = ly_top (c_ly cx)) by (pose proof HLY as (_ & _ & _ & _ & _ & _ & _ & _ & X & _); exact X).
  assert (Hfin : In (1, fpos) (frames S)) by (rewrite HFRS0; left; reflexivity).
  pose proof HMOD as (Hlen4 & HSL & HREL & (ev & HOUT) & HGONE & HLOCK & HWAKE & HNFD & HNFDW & HNFDr & HTUP & HLST & HLSTW).
  assert (HSRC : asrc_at B ly S W mem HA h1) by (pose proof (HSL si Hsi) as X; rewrite Hh1 in X; exact X).
  pose proof HSRC as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HLE & HLH & _).
  set (LE := list_blks (hs_expected h1)). set (LH := list_blks (hs_held h1)).
  set (PP := (hs_partial h1, APARTIAL) :: alist_blks (hs_pending h1)).
  set (OTH := concat (map slot_blks (firstn si (lm_hs mc) ++ skipn (Datatypes.S si) (lm_hs mc)))).
  set (ENT := concat (map aentry_blks (lm_es mc))).
  set (AO := aout_blks (lm_cap mc) (lm_out mc)).
  set (GE := [(lm_G mc, ATABLE)]).
  destruct HSEP as ((RS & HPm0) & HSEP2).
  set (RB := PP ++ input_blks cx ++ GE ++ ENT ++ OTH ++ AO ++ RS).
  assert (HCS : Permutation (concat (map slot_blks (lm_hs mc))) ((PP ++ LE ++ LH) ++ OTH)).
  { pose proof (dr_concat_nth_perm _ _ slot_blks (lm_hs mc) si None ltac:(lia)) as X. rewrite Hh1 in X. exact X. }
  assert (HP1 : Permutation (ablocks B ly S) ((LE ++ LH) ++ RB)).
  { apply (Permutation_trans HPm0).
    exact (dcE_perm_shape (input_blks cx) GE ENT OTH AO RS PP LE LH (concat (map slot_blks (lm_hs mc))) HCS). }
  assert (HND1 : List.NoDup ((LE ++ LH) ++ RB)) by exact (Permutation_NoDup HP1 (dj_nodup ly S Hp W mem md HAR)).
  assert (LEHin : forall b, In b (LE ++ LH) -> In b (ablocks B ly S)).
  { intros b Hb. apply (Permutation_in _ (Permutation_sym HP1)). apply in_or_app. left. exact Hb. }
  assert (Rin : forall b, In b RB -> In b (ablocks B ly S)).
  { intros b Hb. apply (Permutation_in _ (Permutation_sym HP1)). apply in_or_app. right. exact Hb. }
  assert (RnLEH : forall b, In b RB -> ~ In b (LE ++ LH)) by (intros b H1 H2; exact (dcE_nodup_app _ _ b HND1 H2 H1)).
  assert (CSmodel : forall b, In b (concat (map slot_blks (lm_hs mc))) -> In b (model_blks mc)).
  { intros b Hb. unfold model_blks. right. apply in_or_app. right. apply in_or_app. left. exact Hb. }
  assert (H1CS : forall b, In b (PP ++ LE ++ LH) -> In b (concat (map slot_blks (lm_hs mc)))).
  { intros b Hb. apply in_concat. exists (slot_blks (Some h1)). split; [apply in_map; rewrite <- Hh1; apply nth_In; lia|].
    exact Hb. }
  assert (LEHmodel : forall b, In b (LE ++ LH) -> In b (model_blks mc)).
  { intros b Hb. apply CSmodel, H1CS. apply in_or_app. right. exact Hb. }
  assert (LEHpos : forall b, In b (LE ++ LH) -> 0 < snd b).
  { intros b Hb. apply in_app_or in Hb as [Hb | Hb].
    - exact (dcE_blks_pos ly S W mem _ _ _ HLE b Hb).
    - exact (dcE_blks_pos ly S W mem _ _ _ HLH b Hb). }
  assert (HGcG : forall a, inG [(HA + 64, 32)] a -> inG G_fr a).
  { intros a Ha. apply dcE_inG1 in Ha. apply HGs. lia. }
  assert (HGc : gx_ok segs B [(HA + 64, 32)]) by exact (gx_ok_sub segs B _ _ HGcG HG).
  assert (HGrt : gx_rt B [(HA + 64, 32)]).
  { intros a Ha. apply dcE_inG1 in Ha. destruct HAP as [HAP0 HAP32]. split; [|split]; lia. }
  assert (HZc : azs B (HA + 64) 32).
  { destruct HZS as (r & Hr & H8 & H1 & H2). exists r. split; [exact Hr|]. split; [exact H8|]. split; lia. }
  pose proof HOUT as (_ & _ & O3 & _ & _ & _ & O7 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
                      _ & _ & _ & _ & _ & _ & _ & O26).
  assert (HAOR : forall b, In b AO -> In b RB)
    by (intros b Hb; unfold RB; do 5 (apply in_or_app; right); apply in_or_app; left; exact Hb).
  assert (HPPR : forall b, In b PP -> In b RB) by (intros b Hb; unfold RB; apply in_or_app; left; exact Hb).
  assert (HOBX : ob_at W mem (lm_out mc) (lm_O mc) /\
     Z.of_nat (length (lm_O mc)) <= 2 ^ 40 /\ (0 < Z.of_nat (length (lm_O mc)) -> Z.of_nat (length (lm_O mc)) < 2 ^ 32) /\
     amem_range (lm_out mc) (Z.of_nat (length (lm_O mc)) + 8) /\
     (lm_O mc = [] \/ exists CO, Z.of_nat (length (lm_O mc)) <= CO /\ In (lm_out mc, CO) (ablocks B ly S) /\
        ~ In (lm_out mc) (hs_blocks h1))).
  { destruct O26 as [(Hc0 & Hout0 & Hno0) | (Hcp & Hno & Hin & junk & Hj & Hg)].
    - assert (HO0 : lm_O mc = []) by (apply length_zero_iff_nil; lia).
      rewrite HO0, Hout0. cbn [length]. split; [intros i Hi; cbn in Hi; lia|].
      split; [lia|]. split; [lia|]. split; [left; unfold kLowMemEnd; lia | left; reflexivity].
    - destruct (alx_blocks _ _ _ LAWS ly S Hp W mem md _ _ HAR Hin) as (_ & _ & _ & Happ & _ & _); pose proof (BLKR ly S Hp W mem md _ _ HAR Hin) as Hmx.
      assert (Ers : req_size (lm_cap mc) = lm_cap mc) by (unfold req_size; rewrite (proj2 (Z.eqb_neq (lm_cap mc) 0) ltac:(lia)); reflexivity).
      rewrite Ers in Happ.
      split; [exact (dcE_ob_at W mem _ _ _ Hg)|].
      split; [lia|]. split; [lia|].
      split; [zlia|].
      right. exists (lm_cap mc). split; [lia|]. split; [exact Hin|].
      intros Hx. destruct (dcE_hs_blocks h1 _ Hx) as (n & Hn).
      assert (HnPP : In (lm_out mc, n) (PP ++ LE ++ LH)) by exact Hn.
      assert (HAOc : In (lm_out mc, lm_cap mc) AO)
        by (unfold AO, aout_blks; rewrite (proj2 (Z.eqb_neq (lm_cap mc) 0) ltac:(lia)); left; reflexivity).
      assert (Hn1 : In (lm_out mc, n) (ablocks B ly S)).
      { apply in_app_or in HnPP as [Hpo | Hpo]; [exact (Rin _ (HPPR _ Hpo)) | exact (LEHin _ Hpo)]. }
      destruct (dcE_dec (lm_out mc, n) (lm_out mc, lm_cap mc)) as [Heq | Hne].
      + rewrite Heq in HnPP. apply in_app_or in HnPP as [Hpo | Hpo].
        * apply (dcE_nodup_app PP (input_blks cx ++ GE ++ ENT ++ OTH ++ AO ++ RS) (lm_out mc, lm_cap mc)
            (dcE_nodup_r _ _ HND1) Hpo). do 4 (apply in_or_app; right). apply in_or_app. left. exact HAOc.
        * exact (RnLEH _ (HAOR _ HAOc) Hpo).
      + destruct (alx_blocks _ _ _ LAWS ly S Hp W mem md _ _ HAR Hn1) as (_ & _ & _ & _ & _ & _); pose proof (BLKR ly S Hp W mem md _ _ HAR Hn1) as Hn0.
        pose proof (req_size_pos n ltac:(lia)) as [Hr1 _]. pose proof (req_size_pos (lm_cap mc) ltac:(lia)) as [Hr2 _].
        exact (dj_apart ly S Hp W mem md _ _ _ _ (lm_out mc) HAR Hin Hn1 (fun E => Hne (eq_sym E)) ltac:(lia) ltac:(lia)). }
  destruct HOBX as (HOBAT & HNO40 & HNO32 & HMR & HOB0). clear O26.
  assert (P5 : forall a, spZ regsc <= a < spZ regsc + 208 -> apresent (w_H W) mem a).
  { intros a Ha. apply HJpres. rewrite Hspc in Ha. unfold LLVMF_STK. lia. }
  assert (P21 : val_mem segs (arm W mem) (VAL A_g_gone) 1 (lm_gn mc)) by (rewrite Vgone; exact (proj1 HGONE)).
  assert (P22 : 0 <= lm_gn mc < 256) by (destruct HGONE as (_ & _ & [G0 | G0]); lia).
  assert (P23 : val_mem segs (arm W mem) (VAL A_g_nout) 8 (Z.of_nat (length (lm_O mc)))) by (rewrite Vnout; exact O3).
  assert (P24 : val_mem segs (arm W mem) (VAL A_g_out) 8 (lm_out mc)) by (rewrite Vout; exact O7).
  assert (HF8 : (F + 192) mod 8 = 0).
  { pose proof (Z.div_mod F 32 ltac:(lia)) as D. rewrite HF32, Z.add_0_r in D. rewrite D.
    replace (32 * (F / 32) + 192) with ((4 * (F / 32) + 24) * 8) by ring. apply Z_mod_mult. }
  destruct (dr_afn_pre_atR cx Hpe ly S Hp fpos k W mem mdc regsc CNL_STK HB HJ) as (ch & HPREc).
  { rewrite HFF. exact (dr_aframe_false cx FF W mem HFR). }
  { exact Hspc. }
  { rewrite Q1. apply ret_ok_codeptr_v; [lia | reflexivity]. }
  { unfold raZ. rewrite Q1, unsigned_lit_small by lia. lia. }
  { rewrite (KR3 3%bv ltac:(dcE_infp)). exact R3. }
  { rewrite (KR3 4%bv ltac:(dcE_infp)). exact R4. }
  { rewrite (KR3 8%bv ltac:(dcE_infp)). exact R8. }
  { rewrite dcE_cnl_stk. lia. }
  { rewrite dcE_cnl_stk. unfold LLVMF_STK. lia. }
  assert (P4 : spZ regsc + 208 <= ly_top ly) by (rewrite Hspc, Etop; lia).
  assert (P8 : HA = VAL A_g_s + ASRC * Z.of_nat si) by (rewrite Vs; reflexivity).
  assert (P11 : spZ regsc <= F + 192) by (rewrite Hspc; lia).
  assert (P12 : F + 192 + 8 <= spZ regsc + 208) by (rewrite Hspc; lia).
  assert (P14 : forall a, HA + 64 <= a < HA + 96 -> inG [(HA + 64, 32)] a) by (intros a Ha; apply dcE_inG1; lia).
  pose proof (dcE_lit W mem _ _ HRV (proj1 dcE_lits)) as L1.
  pose proof (dcE_lit W mem _ _ HRV (proj1 (proj2 dcE_lits))) as L2.
  pose proof (dcE_lit W mem _ _ HRV (proj2 (proj2 dcE_lits))) as L3.
  assert (P20 : 0 <= 0 <= Z.of_nat (length (lm_O mc))) by lia.
  set (FPc := blk_FP (LE ++ LH)).
  set (K := fun (ly2 : alayout) (S2 : astate) (Hp2 : list Z) (W2 : world segs) (regs2 : bvmap 5 word)
      (mem2 : word -> option byte) (md2 : Model) =>
    exists kk (E' H' : hlist),
      ajournal_gx_xR segs B PST ARx R [(HA + 64, 32)] 208 [(F + 192, F + 192 + 8)] CNL_STK (spZ regsc) FPc ly S Hp W mem mdc []
        ly2 S2 Hp2 W2 mem2 md2 kk /\
      asrc_at B ly2 S2 W2 mem2 HA (set_exp_held h1 E' H') /\
      hl_recs E' = [] /\ hl_v E' = hl_v (hs_expected h1) /\ hl_cap E' = hl_cap (hs_expected h1) /\
      NoDup (texts H') /\ texts H' = RelayModel.upds (texts (hs_held h1)) (texts (hs_expected h1)) /\
      hl_cap H' <= Z.max 8 (Z.max (hl_cap (hs_held h1))
                                  (2 * (hl_n (hs_held h1) + Z.of_nat (count_begin (texts (hs_expected h1)))))) /\
      val_mem segs (arm W2 mem2) (F + 192) 8
        (if lm_gn mc =? 0 then 0 + Z.of_nat (length (bstream (hs_expected h1))) else 0) /\
      (forall rest, Permutation (ablocks B ly S) (LE ++ LH ++ rest) ->
         Permutation (ablocks B ly2 S2) (list_blks E' ++ list_blks H' ++ rest)) /\
      mo_le MT S S2 (cnl_cost MT (hs_expected h1) (hs_held h1)) /\ NP S2).
  eapply (SRrG_mono segs R).
  { apply (dr_callZR G_fr W regsc mem (Z_to_bv 64 (BASE + 13932)) LLVMF_STK sp0 (lf_FP fr_FP cx)
      (c_ly cx) (c_S cx) Hpe (c_W cx) (c_mem cx) (c_md cx) [(1, fpos)] ly S Hp mdc k CNL_STK FPc 208
      [(F + 192, F + 192 + 8)] (F - sp0) (getr regsc 1) ch K HG HJ).
    - rewrite Hspc. lia.
    - lia.
    - rewrite dcE_cnl_stk. unfold LLVMF_STK. lia.
    - lia.
    - lia.
    - intros a (r & [<- | []] & Hr). cbn [fst snd] in Hr. unfold LLVMF_STK. lia.
    - reflexivity.
    - exact HPREc.
    - eapply (SRrG_mono segs R).
      { exact (CNL_R [(HA + 64, 32)] HGc HGrt W ly S Hp regsc mem mdc ch 208 HA si (F + 192) h1 (lm_gn mc) 0
          (Z.of_nat (length (lm_O mc))) (lm_out mc) (lm_O mc)
          HPREc ltac:(lia) eq_refl P4 P5 Rc10 Rc11 P8 Hsi HF8 P11 P12 HSRC P14 HZc
          HND HnE HnH SAT P20 P21 P22 P23 P24 HOBAT eq_refl HNO40 HNO32 HMR HOB0 HOB HRV L1 L2 L3 HROOM HMO
          0%nat ltac:(apply RP_NP; exact HNPs) HCNTc HCAPB
          ltac:(intros a Ha; rewrite Hspc in Ha; exact (dr_stkrR cx Hpe fpos ly S Hp W mem mdc k HB HJ a Ha))). }
      cbv beta. intros W2 c2 _ (ly2 & S2 & Hp2 & regs2 & mem2 & md2 & kk & E' & H' & -> & JC & HPR & HPK & _ & HSRC2 & ER & EV & EC &
        HNDH & HTX & HCAPH & MAT & MGN & MNO & MOUT & HOB2 & HPERM & HFRS & HMO2 & HRM2 & _ & _).
      exists ly2, S2, Hp2, regs2, mem2, md2, kk. split; [reflexivity|].
      split; [eapply ajournal_gx_G_mono_xR; [exact HGcG | exact JC]|].
      split; [exact HPR|].
      unfold K. exists kk, E', H'. split; [exact JC|]. split; [exact HSRC2|].
      do 6 (split; [assumption|]). split; [exact MAT|]. split; [exact HPERM|].
      split; [exact HMO2 | exact (proj1 (RP_NP S2 0%nat) HRM2)].
    - intros a (r & Hr & Hra). unfold FPc, blk_FP in Hr. apply in_map_iff in Hr as ([p n] & <- & Hb). cbn [fst snd] in Hra.
      pose proof (LEHin _ Hb) as Hbl.
      destruct (in_dec dcE_dec (p, n) (ablocks B (c_ly cx) (c_S cx))) as [Hc | Hc].
      + left. destruct (HSEP2 _ (LEHmodel _ Hb)) as [Hn | Hfp]; [exfalso; exact (Hn Hc)|].
        split; [exact (Hfp a Hra)|].
        exists p, n. split; [exact Hbl | exact Hra].
      + right. exists p, n. split; [exact Hbl|]. split; [exact Hc | exact Hra]. }
  cbv beta. intros W2 c2 _ (ly2 & S2 & Hp2 & regs2 & mem2 & md2 & k1 & -> & HJ2 & _ & HPR2 & HK2).
  unfold K in HK2.
  destruct HK2 as (kk & E' & H' & JC & HSRC2 & ER & EV & EC & HNDH & HTX & HCAPH & MAT & HPERM & HMO2 & HNP2).
  assert (HHN : hl_n H' <= hl_cap H').
  { pose proof HSRC2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HHD & _).
    cbn [set_exp_held hs_held] in HHD. pose proof HHD as (_ & _ & _ & _ & (Hn6 & _) & _). exact Hn6. }
  rewrite Hspc in JC. clear HOB0.
  assert (AR2 : ARx ly2 S2 Hp2 W2 mem2 md2) by (eapply ajournal_gx_AR_xR; exact JC).
  assert (EHA' : HA = rg_s fr_RG + 96 * Z.of_nat si) by (rewrite EHA, EASRC; reflexivity).
  set (h' := set_exp_held h1 E' H') in *.
  set (LE' := list_blks E'). set (LH' := list_blks H').
  assert (HP2 : Permutation (ablocks B ly2 S2) ((LE' ++ LH') ++ RB)).
  { rewrite <- app_assoc. apply HPERM. rewrite app_assoc. exact HP1. }
  assert (HND2 : List.NoDup ((LE' ++ LH') ++ RB)) by exact (Permutation_NoDup HP2 (dj_nodup ly2 S2 Hp2 W2 mem2 md2 AR2)).
  assert (Rin2 : forall b, In b RB -> In b (ablocks B ly2 S2)).
  { intros b Hb. apply (Permutation_in _ (Permutation_sym HP2)). apply in_or_app. right. exact Hb. }
  assert (LEHin2 : forall b, In b (LE' ++ LH') -> In b (ablocks B ly2 S2)).
  { intros b Hb. apply (Permutation_in _ (Permutation_sym HP2)). apply in_or_app. left. exact Hb. }
  pose proof (dcE_kept_blkR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HGc JC HARc LEHin) as KB0.
  pose proof (dcE_kept_imgR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HGc JC HARc LEHin) as KI0.
  pose proof (dcE_kept_frameR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HGc JC HARc LEHin) as KF0.
  assert (KBLK : forall b a, In b RB -> fst b <= a < fst b + snd b -> abyte_kept W mem W2 mem2 a).
  { intros [p n] a HbR Ha. cbn [fst snd] in Ha. pose proof (Rin _ HbR) as Hin1.
    destruct (alx_blocks _ _ _ LAWS ly S Hp W mem md p n HAR Hin1) as (_ & _ & _ & _ & _ & _); pose proof (BLKR ly S Hp W mem md p n HAR Hin1) as Hn.
    pose proof (req_size_pos n ltac:(lia)) as [_ Hrs].
    exact (KB0 p n a Hin1 (Rin2 _ HbR) (RnLEH _ HbR) ltac:(lia)). }
  assert (HOi : forall i b, (i < 4)%nat -> i <> si -> In b (slot_blks (nth i (lm_hs mc) None)) -> In b RB).
  { intros i b Hi Hne Hb. assert (Hb' : In b OTH).
    { unfold OTH. apply in_concat. exists (slot_blks (nth i (lm_hs mc) None)). split; [|exact Hb].
      apply in_map. apply dcE_nth_rm; [rewrite Hlen4; exact Hi | exact Hne]. }
    unfold RB. do 4 (apply in_or_app; right). apply in_or_app. left. exact Hb'. }
  assert (HGER : forall b, In b (arelay_blks (lm_G mc) (lm_es mc)) -> In b RB).
  { intros b [<- | Hb]; unfold RB.
    - do 2 (apply in_or_app; right). apply in_or_app. left. unfold GE. left. reflexivity.
    - do 3 (apply in_or_app; right). apply in_or_app. left. exact Hb. }
  pose proof (dcE_model_kept ly S W mem ly2 S2 Hp2 W2 mem2 md2 mc si h' RB HA AR2 Hsi EHA HMOD HKY HSRC2 HOi HGER HAOR
    Rin2 KBLK KI0) as HMOD2.
  assert (HCS' : Permutation (concat (map slot_blks (set_nth si (Some h') (lm_hs mc)))) ((PP ++ LE' ++ LH') ++ OTH))
    by exact (dr_concat_set_nth_perm _ _ slot_blks (lm_hs mc) si (Some h') ltac:(lia)).
  assert (HP3 : Permutation (input_blks cx ++ model_blks (dc_setsrc mc si h') ++ RS) ((LE' ++ LH') ++ RB))
    by exact (dcE_perm_shape (input_blks cx) GE ENT OTH AO RS PP LE' LH' _ HCS').
  assert (HSEP' : ablocks_sep B fr_FP cx (dc_setsrc mc si h') ly2 S2).
  { split; [exists RS; exact (Permutation_trans HP2 (Permutation_sym HP3))|].
    intros b Hb.
    assert (Hcase : In b (LE' ++ LH') \/ In b (model_blks mc)).
    { unfold model_blks in Hb. cbn [dc_setsrc lm_G lm_es lm_hs lm_cap lm_out] in Hb.
      destruct Hb as [<- | Hb]; [right; unfold model_blks; left; reflexivity|].
      apply in_app_or in Hb as [Hb | Hb]; [right; unfold model_blks; right; apply in_or_app; left; exact Hb|].
      apply in_app_or in Hb as [Hb | Hb];
        [|right; unfold model_blks; right; apply in_or_app; right; apply in_or_app; right; exact Hb].
      apply (Permutation_in _ HCS') in Hb. apply in_app_or in Hb as [Hb | Hb].
      - apply in_app_or in Hb as [Hb | Hb]; [right; apply CSmodel, H1CS, in_or_app; left; exact Hb | left; exact Hb].
      - right. apply CSmodel. unfold OTH in Hb. apply in_concat in Hb as (l & Hl & Hbl). apply in_concat.
        exists l. split; [|exact Hbl]. apply in_map_iff in Hl as (o & <- & Ho). apply in_map.
        exact (dr_in_rm _ si o (lm_hs mc) Ho). }
    destruct Hcase as [Hnew | Hold]; [|exact (HSEP2 b Hold)].
    destruct (in_dec dcE_dec b (ablocks B (c_ly cx) (c_S cx))) as [Hc | Hc]; [|left; exact Hc]. right.
    destruct (in_dec dcE_dec b (ablocks B ly S)) as [Hb1 | Hb1].
    - apply (Permutation_in _ HP1) in Hb1. apply in_app_or in Hb1 as [Hb1 | Hb1].
      + destruct (HSEP2 b (LEHmodel b Hb1)) as [Hn | Hfp]; [exfalso; exact (Hn Hc) | exact Hfp].
      + exfalso. exact (dcE_nodup_app _ _ b HND2 Hnew Hb1).
    - destruct b as [p n]. intros a Ha. cbn [fst snd] in Ha.
      pose proof (LEHin2 _ Hnew) as Hb2.
      destruct (alx_blocks _ _ _ LAWS ly2 S2 Hp2 W2 mem2 md2 p n AR2 Hb2) as (_ & _ & _ & _ & _ & _); pose proof (BLKR ly2 S2 Hp2 W2 mem2 md2 p n AR2 Hb2) as Hn.
      pose proof (req_size_pos n ltac:(lia)) as [_ Hrs].
      replace a with (p + (a - p)) by lia. exact (HJgone p n (a - p) Hc Hb1 ltac:(lia)). }
  assert (KOUT : forall a, F <= a < sp0 -> ~ (F + DR_AT <= a < F + DR_AT + 8) -> abyte_kept W mem W2 mem2 a).
  { intros a Ha Hn. unfold DR_AT in Hn.
    apply (dcE_keptR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ a HGc JC).
    - unfold DR_CEIL8 in *. lia.
    - rewrite dcE_inG1. unfold DR_CEIL8 in *. lia.
    - intros Hi. pose proof (Hsegs a Hi). unfold DR_CEIL8 in *. lia.
    - destruct (Z_lt_le_dec a (F + 208)) as [Hlt | Hge].
      + right; left. split; [lia|]. intros (r & [<- | []] & Hr). cbn [fst snd] in Hr. lia.
      + left. unfold DR_CEIL8 in *. split; lia. }
  assert (WF : forall a, F <= a < sp0 -> writable_at segs (arm W2 mem2) a).
  { pose proof HJ2 as (_ & _ & (memS2 & HJ20 & _) & _). rewrite !Z.add_0_r in HJ20.
    pose proof HJ20 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HJ2pres & _).
    intros a Ha. apply (apresent_writable segs). apply HJ2pres. unfold LLVMF_STK. lia. }
  assert (KFF : forall a, FF <= a < FF + 128 -> abyte_kept W mem W2 mem2 a).
  { intros a Ha. apply (KF0 1 fpos a Hfin). left. unfold in_zr, frame_rng. cbn [fst snd].
    rewrite HFF. replace (fs_frame_bytes 1) with 128 by reflexivity. lia. }
  assert (KSH : forall a, SB + FF / 8 <= a < SB + FF / 8 + 16 -> abyte_kept W mem W2 mem2 a).
  { intros a Ha. apply (KF0 1 fpos a Hfin). right. unfold in_zr. cbn [fst snd].
    rewrite HFF. replace (fs_frame_bytes 1 / 8) with 16 by reflexivity. unfold shadow_addr.
    unfold SB, SHADOW_OFF in *. lia. }
  assert (H320 : lf_F cx + 320 <= spZ (c_regs cx)) by (change (F + 320 <= sp0); lia).
  assert (HFR2 : aframe_at cx true FF W2 mem2) by exact (dcE_aframe_kept cx true FF W W2 mem mem2 HFR H320 KOUT WF KFF KSH).
  assert (HFL2 : sv8 W2 mem2 (FF + 120) (flag_addr ly2 1 fpos)).
  { pose proof JC as (_ & _ & (memC & JC0 & _) & _). pose proof JC0 as (_ & HLY2 & _).
    pose proof HLY2 as (_ & _ & _ & _ & _ & EF & _). unfold flag_addr. rewrite EF.
    apply (dr_sv8_kept W W2 mem mem2); [intros x Hx; apply KFF; lia | exact HFL]. }
  assert (HIN2 : ainput_at B cx ly2 S2 W2 mem2).
  { destruct HIN as (Hcase & Hg).
    assert (HINR : c_n cx <> 0 -> In (c_p cx, c_n cx) RB).
    { intros Hn0. unfold RB. apply in_or_app. right. apply in_or_app. left. unfold input_blks.
      rewrite (proj2 (Z.eqb_neq (c_n cx) 0) Hn0). left. reflexivity. }
    split.
    - destruct Hcase as [Hc | (Hn & Hin)]; [left; exact Hc | right; split; [exact Hn|]].
      exact (Rin2 _ (HINR ltac:(lia))).
    - apply (akept_garr8 W mem); [|exact Hg]. intros x Hx. rewrite length_map in Hx.
      destruct Hcase as [(Hc & _) | (Hn & Hin)].
      + lia.
      + apply (KBLK (c_p cx, c_n cx) x (HINR ltac:(lia))). cbn [fst snd]. lia. }
  assert (HRO : rom_out segs B [(HA + 64, 32)]).
  { intros a Ha. destruct (DR_ROM_OUT a Ha) as (H1 & H2 & H3 & H4).
    split; [intros HGa; exact (H1 (HGcG a HGa))|]. split; [exact H2|]. split; [exact H3 | exact H4]. }
  assert (HRV2 : rom_view segs W2 mem2)
    by exact (ajournal_gx_rom_view_xR segs B PST ARx LAWS pa_segs_low _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ JC HRO dr_pstr HRV).
  assert (HROM2 : jt_rom W2 mem2) by exact (dcE_jt_kept W W2 mem mem2 HRV HRV2 HROM).
  assert (SVN2 : sv8 W2 mem2 (F + DR_N) (c_n cx - dr_k' cx m)).
  { apply (dr_sv8_kept W W2 mem mem2); [|exact SVN]. intros x Hx. apply KOUT; unfold DR_N, DR_AT in *; lia. }
  assert (SLK2 : sv8 W2 mem2 (F + 40) (rg_lock fr_RG)).
  { apply (dr_sv8_kept W W2 mem mem2); [|exact SLK]. intros x Hx. apply KOUT; unfold DR_AT in *; lia. }
  assert (SAT2 : sv8 W2 mem2 (F + DR_AT) (if lm_gn mc =? 0 then Z.of_nat (length (bstream (hs_expected h1))) else 0)).
  { replace (0 + Z.of_nat (length (bstream (hs_expected h1)))) with (Z.of_nat (length (bstream (hs_expected h1))))
      in MAT by lia. exact MAT. }
  pose proof (dcE_regs_kept cx t m j si FF regs regsc regs2 KR3 HPR2 DR0) as DR2.
  exists ly2, S2, Hp2, E', H'.
  split; [|split; [exact HMO2 | split; [exact (conj ER (conj EV (conj EC (conj HNDH (conj HTX HCAPH))))) |
    split; [exact HNP2 | split; [exact HPERM | exact HHN]]]]].
  exists regs2, mem2, md2, (k + k1).
  split; [rewrite Q1; reflexivity|].
  split; [exact DR2|].
  split; [exact HJ2|].
  split.
  { pose proof JC as (_ & _ & (memC & JC0 & _) & _). pose proof JC0 as (_ & HLY2 & _).
    pose proof HLY2 as (_ & _ & _ & _ & _ & EF & _). unfold frame_addr in HFF |- *. rewrite EF. exact HFF. }
  split; [exact HFR2|]. split; [exact HFL2|]. split; [exact HIN2|]. split; [exact HRV2|]. split; [exact HROM2|].
  split; [exact SVN2|]. split; [exact SAT2|]. split; [exact SLK2|].
  split; [exact HMOD2|]. split; [exact HSEP'|]. exact HKY.
Qed.

(* dc_calls at R: the six stages composed by SRrG_bind (R_trans) *)
Lemma dc_callsR : forall cx Hpe t m j si h fpos ly3 S3 Hp3 k W c,
  lf_base_x B MT XM_LIB RLO RHI fr_live_pre LIBROOM NP G_fr ARx cx Hpe ->
  DLKR cx Hpe t m j si h fpos ly3 S3 Hp3 k W c ->
  SRrG segs R W c (DSTR A_dr_join cx Hpe (t + 1) (lregs_join cx t)).
Proof.
  intros cx Hpe t m j si h fpos ly3 S3 Hp3 k W c HB HD.
  pose proof HD as (regs & mem & md & -> & HJ & HFR & _ & HMOD & HIN & HRV & HROM & HSEP & HLS & HNP & HRI & Hatop & Hpick & Hj &
                    Hfdj & Hef0 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Ht & _).
  pose proof HMOD as (Hlen4 & _ & _ & _ & (_ & _ & Hgn01) & _).
  pose proof Hpick as (_ & Hsi & Hhsi).
  pose proof Hatop as (_ & HO0 & _).
  assert (HST : dc_static cx t m j si h) by exact (conj Hatop (conj Hpick (conj Hj (conj Hfdj (conj Hef0 HRI))))).
  set (FF := frame_addr ly3 1 fpos).
  eapply (SRrG_bind segs R R_trans); [exact (dc_stAR cx Hpe t m j si h fpos ly3 S3 Hp3 k W _ HB HD)|]. intros W1 c1 _ H1.
  eapply (SRrG_bind segs R R_trans); [exact (dc_stBR cx Hpe t m j si h fpos FF ly3 S3 Hp3 W1 c1 HB HST HLS HNP H1)|].
  intros W2 c2 _ (ly4 & S4 & Hp4 & e' & h' & out' & ev' & LB & H2 & HMO1 & HDF & HOUT4).
  destruct HOUT4 as (EPRE & EKH & HPRE3 & HHN3 & CAP0 & HPERMD & EPOST & HPOST3 & DPOST & HNP4 & HCNTc).
  eapply (SRrG_bind segs R R_trans); [exact (dc_stCR cx Hpe t m j si fpos FF ly4 S4 Hp4 _ W2 c2 HB H2)|]. intros W3 c3 _ H3.
  set (m1 := dr_m1 m j si h h' e' ev' LB out') in *.
  pose proof HDF as (D1 & D2 & D3 & D4 & D5 & D6 & D7 & D8 & D9 & D10 & D11 & D12 & D13 & D14 & D15 & D16 & D17 & D18 &
                     D19 & D20 & D21 & D22 & D23 & D24).
  assert (Hh1 : nth si (lm_hs m1) None = Some h').
  { unfold m1, dr_m1, dr_step. cbn [lm_hs]. apply set_nth_same. lia. }
  eapply (SRrG_bind segs R R_trans); [exact (dc_stDR cx Hpe t m j si fpos FF ly4 S4 Hp4 m1 h' W3 c3 HB Hsi Hh1 D14 H3)|].
  intros W4 c4 _ H4.
  destruct (RI_src cx t m si h HRI Hpick) as (Hexp0 & _ & _).
  destruct (LS_cnl_pre cx t m ly3 S3 ly4 S4 si h j h' e' (dr_cap1 m j h) out' HLS HRI Hpick Hj Hfdj Hef0 HMO1 D22 D17 D18
             Ht HO0 EPRE HPRE3 CAP0 HPERMD eq_refl EPOST HPOST3)
    as (N1 & N2 & N3 & N4 & N5 & N6).
  assert (HBS : bstream (hs_expected h') = LB) by (rewrite Hexp0 in D17; exact (dc_bstream_LB _ _ LB D17 D21)).
  destruct (RI_gone cx t m HRI) as (G0 & G1).
  assert (HOB : lm_gn m1 = 0 -> exists rest, lm_O m1 = bstream (hs_expected h') ++ rest).
  { intros Hg. exists []. rewrite app_nil_r, HBS. cbn [m1 dr_m1 dr_step lm_gn lm_O] in Hg |- *. unfold dr_O1.
    rewrite HO0. cbn [app]. destruct (G0 Hg) as (C3 & C0 & D0).
    unfold dr_live, sl_live, send_line_c.send_live, send_line_c.send_off. rewrite C3, C0, D0. cbn.
    destruct (Z.eqb_spec (dr_tot h) 0) as [Ht0 | Ht0]; cbn; [|reflexivity].
    pose proof (dc_LB_len LB _ D21) as HL. unfold dr_tot in Ht0. rewrite Ht0 in HL.
    destruct LB; [reflexivity | cbn [length] in HL; lia]. }
  eapply (SRrG_bind segs R R_trans);
    [exact (dc_stER cx Hpe t m j si fpos FF ly4 S4 Hp4 m1 h' W4 c4 HB Hsi Hh1 N1 N2 N3 N4 N5 N6 HNP4 HCNTc HOB H4)|].
  intros W5 c5 _ (ly6 & S6 & Hp6 & E' & H' & H5 & HMO2 & HCF & HNP6 & HCFR & HHN6).
  set (m2 := dc_setsrc m1 si (set_exp_held h' E' H')) in *.
  assert (HA : (if lm_gn m1 =? 0 then Z.of_nat (length (bstream (hs_expected h'))) else 0) = Z.of_nat (length (lm_O m2))).
  { cbn [m2 dc_setsrc m1 dr_m1 dr_step lm_gn lm_O]. unfold dr_O1. rewrite HO0. cbn [app].
    destruct Hgn01 as [Hg | Hg]; rewrite Hg; cbn [Z.eqb].
    - destruct (HOB ltac:(cbn [m1 dr_m1 dr_step lm_gn]; exact Hg)) as (rest & Hr).
      cbn [m1 dr_m1 dr_step lm_O] in Hr. unfold dr_O1 in Hr. rewrite HO0 in Hr. cbn [app] in Hr.
      rewrite HBS. destruct (dr_live (lm_c m) h); [reflexivity|].
      rewrite HBS in Hr. destruct LB; [reflexivity | cbn in Hr; discriminate].
    - assert (Hlv : dr_live (lm_c m) h = false).
      { destruct (G1 Hg) as [C | [C | C]]; unfold dr_live, sl_live, send_line_c.send_live, send_line_c.send_off;
          rewrite C; cbn; [reflexivity | rewrite orb_true_r; reflexivity | rewrite andb_false_r; reflexivity]. }
      rewrite Hlv. reflexivity. }
  rewrite HA in H5.
  assert (Hfin : forall ev, dc_fin cx m m2 ev =
    dr_step m (dr_k' cx m) si (set_exp_held h' E' H') j e' (dr_ctl (lm_c m) h ev) (dr_O1 m h LB) (dr_cap1 m j h) out').
  { intros ev. unfold dc_fin, m2, dc_setsrc, m1, dr_m1, dr_step. cbn [lm_hs lm_G lm_es lm_c lm_O lm_mx lm_cap lm_out lm_gn lm_nfd].
    rewrite dc_set_nth_twice, dc_ctl_dr. reflexivity. }
  apply (dc_stFR cx Hpe t m j si fpos FF ly6 S6 Hp6 m2 W5 c5 HB Hatop HNP6).
  - intros ev. rewrite Hfin.
    apply (RI_drain_step cx t m si h j e' h' (dr_ctl (lm_c m) h ev) (dr_O1 m h LB) (dr_cap1 m j h) out' ev LB E' H'
             HRI Ht N3 Hatop Hpick Hj Hfdj Hef0).
    unfold dr_step_ok. cbv zeta.
    destruct HCF as (F1 & F2 & F3 & F4 & F5 & F6).
    repeat (split; [first [assumption | reflexivity]|]). first [assumption | reflexivity].
  - intros ev. rewrite Hfin.
    pose proof HCF as (F1 & F2 & F3 & F4 & F5 & F6).
    exact (LS_drain_step cx t m ly3 S3 S4 ly6 S6 si h j (set_exp_held h' E' H') e' (dr_ctl (lm_c m) h ev)
             (dr_O1 m h LB) (dr_cap1 m j h) out' (hs_expected h') (hs_held h') ly4 h' E' H'
             HLS Hpick Hj HMO1 HMO2 HPERMD D14 eq_refl eq_refl HCFR eq_refl Hatop HRI Hfdj Hef0
             EPRE EKH HPRE3 HHN3 CAP0 eq_refl EPOST HPOST3 DPOST
             (conj F1 (conj F3 (conj F4 (conj F5 (conj F6 HHN6))))) Ht).
  - exact H5.
Qed.

(* dr_found_join at R: the eof test, then the eof = 1 skip or the six calls (dc_callsR); the goal is SRrG segs R, so
   the runs are paj_run_x_xG's and the branch paj_branch_xR *)
Lemma dr_found_joinR : forall cx Hpe t j W c,
  lf_base_x B MT XM_LIB RLO RHI fr_live_pre LIBROOM NP G_fr ARx cx Hpe ->
  DSTR A_dr_found cx Hpe t (lregs_found cx t j) W c ->
  SRrG segs R W c (DSTR A_dr_join cx Hpe (t + 1) (lregs_join cx t)).
Proof.
  intros cx Hpe t j W c HB (regs & mem & md & -> & HROM &
    (own & ly3 & S3 & Hp3 & k & m & fpos & HJ & Hown & HFR & HFL & HMOD & HIN & HRV & HSEP & HLS & HNP & HRI & HR)).
  destruct HR as (((R2 & R8 & R9 & R18 & R19 & R20 & R23 & R24 & R25 & R26 & R3 & R4) & R27 & Ht)
    & Hatop & R28 & SVN & (si & h & Hpick & R21 & Hfdj & Hnom) & Hj & R10 & R22).
  pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs.
  pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  pose proof dr_ceil_lo as HCL.
  assert (HAR : ARx ly3 S3 Hp3 W mem md) by (eapply ajournal_gx_AR_xR; exact HJ).
  pose proof HMOD as (Hlen4 & HSL & HREL & HOUT & HGONE & HLOCK & HWAKE & HNFD & HNFDW & HNFDr & HTUP & HLST & HLSTW).
  pose proof HREL as (Msrc & Wsrc & Mnsrc & Wnsrc & Mcap & Wcap & Hle16 & HGin & (tl & HTAB) & HENT & HNDF & _).
  destruct (dr_pads_of_relay ly3 S3 W mem (lm_G m) (lm_es m) HREL) as (HPAD & HFDS).
  remember (nth j (lm_es m) dr_e0) as e eqn:Hedef.
  assert (HEOK : aentry_ok B ly3 S3 W mem e) by (rewrite Hedef; rewrite Forall_forall in HENT; apply HENT, nth_In; exact Hj).
  pose proof HEOK as (Heof01 & _).
  pose proof (dr_tbl_eof W mem (lm_G m) (lm_es m) tl j HTAB HPAD Hj ltac:(rewrite <- Hedef; lia)) as Mef.
  rewrite <- Hedef in Mef.

  pose proof HB as (HAI & HPRE).
  pose proof HPRE as (HFNP & _ & _ & _ & Hnrng & Hnlen & _).
  assert (Hn26 : c_n cx < 2 ^ 26) by (destruct Hnrng as [(Hz & _) | (Hz & _)]; lia).
  pose proof HFNP as (_ & _ & _ & _ & _ & Hstk & _).
  pose proof Hstk as (Hal16 & _ & Hceil & Hslo & Hshi & H47 & _).
  unfold LLVMF_STK in Hslo.
  assert (HFb : spZ (c_regs cx) - 352 < lf_F cx <= spZ (c_regs cx) - 320).
  { unfold lf_F. pose proof (Z.mod_pos_bound (spZ (c_regs cx) - 320) 32 ltac:(lia)). lia. }
  assert (HF32 : lf_F cx mod 32 = 0).
  { unfold lf_F. rewrite Zminus_mod, Z.mod_mod, Z.sub_diag by lia. reflexivity. }
  pose proof (pal_env B TL) as ((HE0 & HE1) & _).
  assert (Hfin : In (1, fpos) (frames S3)).
  { pose proof HJ as (_ & _ & (memS & HJ0 & _) & _). pose proof HJ0 as (_ & _ & _ & _ & _ & Hfrs & _).
    rewrite Hfrs, Hown. left. reflexivity. }
  destruct (frames_bounds_x segs B ARx LAWS ly3 S3 Hp3 W mem md 1 fpos HAR Hfin) as (HFF1 & HFF2 & _).
  replace (fs_frame_bytes 1) with 128 in HFF2 by reflexivity.
  set (FF := frame_addr ly3 1 fpos) in *.
  pose proof HFR as (_ & HAWR & _).
  destruct (alx_blocks _ _ _ LAWS ly3 S3 Hp3 W mem md (lm_G m) ATABLE HAR HGin) as (HG16 & HG4096 & HGceil & _).
  assert (RQ : req_size ATABLE = 896) by reflexivity. rewrite RQ in HGceil.
  assert (Hj16 : Z.of_nat j < 16) by lia.
  assert (HSA8 : (lm_G m + AENT * Z.of_nat j) mod 8 = 0).
  { unfold AENT. pose proof (Z.div_mod (lm_G m) 16 ltac:(lia)) as D. rewrite HG16, Z.add_0_r in D.
    rewrite D. replace (16 * (lm_G m / 16) + 56 * Z.of_nat j) with ((2 * (lm_G m / 16) + 7 * Z.of_nat j) * 8) by ring.
    apply Z_mod_mult. }
  destruct (dc_found_entry ly3 S3 Hp3 W mem md regs (lf_F cx) (lm_G m) j (re_eof e) HAR R9 R10 R22 R26)
    as [HS SHOK].
  { unfold DR_CEIL8 in *. lia. }
  { lia. }
  { exact HF32. }
  { intros a Ha. replace a with (lf_F cx + (a - lf_F cx)) by lia. apply HAWR. lia. }
  { intros a Ha. replace a with (lf_F cx + (a - lf_F cx)) by lia. apply HAWR. lia. }
  { exact HGin. }
  { unfold AENT; lia. }
  { exact HSA8. }
  { unfold AENT, DR_CEIL8 in *; lia. }
  { unfold AENT; lia. }
  { unfold AENT, ATABLE; lia. }
  { exact Mef. }
  { lia. }

  remember (Eimg (Ereg regs (dc_extra (re_eof e)))) as E eqn:HE.
  assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
  assert (HAE : env_agree 32 (Ereg regs (dc_extra (re_eof e))) E)
    by (rewrite HE; split; [intros n Hn; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
  assert (EEo : forall q (rr : bv 5), Z.of_nat q = bv_unsigned rr -> ew E q = getr regs rr)
    by (intros q rr Hq; subst E; pose proof (bv_unsigned_in_range 5 rr) as Hr5; change (bv_modulus 5) with 32 in Hr5;
        rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_nat; exact Hq).
  assert (E9 : ew E 9 = Z_to_bv 64 (lf_F cx)) by (rewrite (EEo 9%nat 9%bv eq_refl); exact R9).
  assert (E32 : ew E 32 = Z_to_bv 64 (re_eof e))
    by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
  assert (U9 : bv_unsigned (ew E 9) = lf_F cx) by (rewrite E9; apply unsigned_lit_small; unfold DR_CEIL8 in *; lia).
  clear HE.
  unfold cfg_at. change (w64 (fr_B0 + A_dr_found)) with (Z_to_bv 64 (BASE + A_dr_found)).
  paj_run_tok_x RUNG HS HJ SHOK DRspan.
  { unfold ss_dc_found, dc_rA, dc_rL, dc_rE. cbn [ss_mem].
    repeat (apply awr_ok_x_cons;
      [ let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha;
        cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; rewrite ?U9 in Ha;
        first [ lia | left; split; [left; unfold LLVMF_STK; lia | lia] ]
      | ]).
    apply awr_ok_x_nil. }
  rename HFr into HFr1, HG0 into HG1. clear HF.
  psrr_branch_tok RUNG BRG HS SHOK DRspan.

  - lazymatch type of Hc with branch_taken _ (sv_denot ?Ev _) _ = _ =>
      assert (U32 : U Ev (SOff 32 0) = re_eof e) by (apply U_atom; [rewrite !ew_ewset_other by lia; exact E32 | lia]) end.
    rewrite branch_ne_U, U32, U_lit in Hc by lia. apply Bool.negb_true_iff, Z.eqb_neq in Hc.
    assert (Hef1 : re_eof e = 1) by lia.
    paj_run_to_tok_x RUNTOG HS HJ SHOK DRspan A_dr_join.
    { unfold dc_rA, dc_rL, dc_rE. cbn [ss_mem add_cond].
      repeat (apply awr_ok_x_cons;
        [ let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha;
          cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; rewrite ?ew_ewset_other in Ha by lia; rewrite ?U9 in Ha;
          first [ lia | left; split; [left; unfold LLVMF_STK; lia | lia] ]
        | ]).
      apply awr_ok_x_nil. }

    assert (Hk' : 0 <= dr_k' cx m <= c_n cx)
      by (pose proof Hatop as (Hk0 & _ & _); unfold dr_k'; destruct (Z.ltb_spec (lm_k m + 1) (c_n cx)); lia).
    assert (K1 : forall a, 0 <= a < 2 ^ 64 -> dc_out cx a -> aview segs (w_H W) (ms_mem ms) a = aview segs (w_H W) mem a).
    { intros a Ha (Hn1 & Hn2). apply (aview_kept_out _ _ _ _ _ HFr1 a Ha).
      intros (r & Hin & Hr). cbn [ss_mem ss_dc_found In] in Hin.
      repeat (destruct Hin as [<- | Hin];
        [ cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val dc_rA dc_rL dc_rE] in Hr; rewrite ?U9 in Hr; unfold DR_AT in Hn2; lia | ]).
      destruct Hin. }
    assert (K2 : forall a, 0 <= a < 2 ^ 64 -> dc_out cx a -> aview segs (w_H W) (ms_mem ms0) a = aview segs (w_H W) mem a).
    { intros a Ha Hno. rewrite <- (K1 a Ha Hno). destruct Hno as (Hn1 & Hn2). apply (aview_kept_out _ _ _ _ _ HFr a Ha).
      intros (r & Hin & Hr). cbn [ss_mem add_cond In] in Hin.
      repeat (destruct Hin as [<- | Hin];
        [ cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr; rewrite ?ew_ewset_other in Hr by lia; rewrite ?U9 in Hr;
          unfold DR_AT in Hn2; lia | ]).
      destruct Hin. }
    assert (WK : forall a, writable_at segs (arm W mem) a -> writable_at segs (arm W (ms_mem ms0)) a).
    { intros a Hw. apply (writable_kept (w_H W) mem (ms_mem ms0) a); [|exact Hw].
      intros Hpo. exact (de_pres_grows W _ _ a HG0 (de_pres_grows W _ _ a HG1 Hpo)). }
    assert (KEEP : forall a, 0 <= a < 2 ^ 64 -> dc_out cx a -> abyte_kept W mem W (ms_mem ms0) a)
      by (intros a Ha Hna; split; [exact (K2 a Ha Hna) | apply WK]).
    destruct (dc_carry cx W mem (ms_mem ms0) md ly3 S3 Hp3 fpos m HAR Hfin (eq_sym Hnlen) ltac:(lia)
                HFR HMOD HIN HRV HROM KEEP WK) as (HFR2 & HMOD2 & HIN2 & HRV2 & HROM2).
    assert (SVN2 : sv8 W (ms_mem ms0) (lf_F cx + DR_N) (c_n cx - dr_k' cx m)).
    { apply (dr_sv8_kept W W mem (ms_mem ms0)); [|exact SVN].
      intros x Hx. apply KEEP; [unfold DR_N, DR_CEIL8 in *; lia | unfold dc_out, DR_N, DR_AT in *; lia]. }
    assert (HFL2 : sv8 W (ms_mem ms0) (FF + 120) (flag_addr ly3 1 fpos)).
    { apply (dr_sv8_kept W W mem (ms_mem ms0)); [|exact HFL].
      intros x Hx. apply KEEP; [unfold DR_CEIL8 in *; lia | unfold dc_out, DR_AT in *; lia]. }
    assert (E28 : ew E 28 = Z_to_bv 64 (c_p cx + dr_k' cx m)) by (rewrite (EEo 28%nat 28%bv eq_refl); exact R28).
    lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
      assert (HAE2 : env_agree 32 (Ereg regs (dc_extra (re_eof e))) Ev)
        by (split; [intros q Hq; rewrite !ew_ewset_other by lia; exact (proj1 HAE q Hq)
                   | rewrite !ed_ewset; exact (proj2 HAE)]) end.
    pose proof (regs_kept_of_st_ok_pi _ _ _ regs _ DR_KEPT HS HAE2 ltac:(vm_compute; reflexivity)) as KR.
    cbn [ms_regs restrict] in KR.
    prreg HS (25%bv : bv 5) Q25. rewrite ?ew_ewset_other in Q25 by lia. rewrite E28 in Q25.
    pmkst HS.
    apply (SRrG_ret segs R R_refl).
    lazymatch goal with |- context [mkCfg (mkst ?r _ ?mm _) ?d] => exists r, mm, d end.
    split; [reflexivity|]. split; [exact HROM2|].
    exists own, ly3, S3, Hp3, k, (dr_skip m (dr_k' cx m)), fpos.
    split; [exact HJ|]. split; [exact Hown|]. split; [exact HFR2|]. split; [exact HFL2|]. split; [exact HMOD2|].
    split; [exact HIN2|]. split; [exact HRV2|]. split; [exact HSEP|].
    split; [apply LS_drain_skip; exact HLS|]. split; [exact HNP|].
    split; [apply (RI_drain_skip cx t m si h HRI Hatop Hpick); right; exists j;
            split; [exact Hj|]; rewrite <- Hedef; split; [exact Hfdj | exact Hef1]|].
    split; [rewrite (KR 2%bv ltac:(cbv; tauto)); exact R2|].
    split; [rewrite (KR 8%bv ltac:(cbv; tauto)); exact R8|].
    split; [rewrite (KR 9%bv ltac:(cbv; tauto)); exact R9|].
    split; [rewrite (KR 18%bv ltac:(cbv; tauto)); exact R18|].
    split; [rewrite (KR 19%bv ltac:(cbv; tauto)); exact R19|].
    split; [rewrite (KR 20%bv ltac:(cbv; tauto)); exact R20|].
    split; [rewrite (KR 23%bv ltac:(cbv; tauto)); exact R23|].
    split; [rewrite (KR 24%bv ltac:(cbv; tauto)); exact R24|].
    split; [rewrite (KR 26%bv ltac:(cbv; tauto)); exact R26|].
    split; [rewrite (KR 3%bv ltac:(cbv; tauto)); exact R3|].
    split; [rewrite (KR 4%bv ltac:(cbv; tauto)); exact R4|].
    split; [rewrite (KR 27%bv ltac:(cbv; tauto)); exact R27|].
    split; [exact Ht|].
    split; [rewrite Q25; reflexivity|].
    split; [exact SVN2|]. exact Hk'.

  - lazymatch type of Hc with branch_taken _ (sv_denot ?Ev _) _ = _ =>
      assert (U32 : U Ev (SOff 32 0) = re_eof e) by (apply U_atom; [rewrite !ew_ewset_other by lia; exact E32 | lia]) end.
    rewrite branch_ne_U, U32, U_lit in Hc by lia. apply Bool.negb_false_iff, Z.eqb_eq in Hc.
    rename Hc into Hef0.
    paj_run_tok_x RUNG HS HJ SHOK DRspan.
    { unfold dc_rA, dc_rL, dc_rE. cbn [ss_mem add_cond].
      repeat (apply awr_ok_x_cons;
        [ let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha;
          cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; rewrite ?ew_ewset_other in Ha by lia; rewrite ?U9 in Ha;
          first [ lia | left; split; [left; unfold LLVMF_STK; lia | lia] ]
        | ]).
      apply awr_ok_x_nil. }

    rename HFr into HFr2, HG0 into HG2. clear HF.
    assert (Hk' : 0 <= dr_k' cx m <= c_n cx)
      by (pose proof Hatop as (Hk0 & _ & _); unfold dr_k'; destruct (Z.ltb_spec (lm_k m + 1) (c_n cx)); lia).
    assert (K1 : forall a, 0 <= a < 2 ^ 64 -> dc_out cx a -> aview segs (w_H W) (ms_mem ms) a = aview segs (w_H W) mem a).
    { intros a Ha (Hn1 & Hn2). apply (aview_kept_out _ _ _ _ _ HFr1 a Ha).
      intros (r & Hin & Hr). cbn [ss_mem ss_dc_found In] in Hin.
      repeat (destruct Hin as [<- | Hin];
        [ cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val dc_rA dc_rL dc_rE] in Hr; rewrite ?U9 in Hr; unfold DR_AT in Hn2; lia | ]).
      destruct Hin. }
    assert (K2 : forall a, 0 <= a < 2 ^ 64 -> dc_out cx a -> aview segs (w_H W) (ms_mem ms0) a = aview segs (w_H W) mem a).
    { intros a Ha Hno. rewrite <- (K1 a Ha Hno). destruct Hno as (Hn1 & Hn2). apply (aview_kept_out _ _ _ _ _ HFr2 a Ha).
      intros (r & Hin & Hr). cbn [ss_mem add_cond In] in Hin.
      repeat (destruct Hin as [<- | Hin];
        [ cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr; rewrite ?ew_ewset_other in Hr by lia; rewrite ?U9 in Hr;
          unfold DR_AT in Hn2; lia | ]).
      destruct Hin. }
    assert (WK : forall a, writable_at segs (arm W mem) a -> writable_at segs (arm W (ms_mem ms0)) a).
    { intros a Hw. apply (writable_kept (w_H W) mem (ms_mem ms0) a); [|exact Hw].
      intros Hpo. exact (de_pres_grows W _ _ a HG2 (de_pres_grows W _ _ a HG1 Hpo)). }
    assert (KEEP : forall a, 0 <= a < 2 ^ 64 -> dc_out cx a -> abyte_kept W mem W (ms_mem ms0) a)
      by (intros a Ha Hna; split; [exact (K2 a Ha Hna) | apply WK]).
    destruct (dc_carry cx W mem (ms_mem ms0) md ly3 S3 Hp3 fpos m HAR Hfin (eq_sym Hnlen) ltac:(lia)
                HFR HMOD HIN HRV HROM KEEP WK) as (HFR2 & HMOD2 & HIN2 & HRV2 & HROM2).
    assert (SVN2 : sv8 W (ms_mem ms0) (lf_F cx + DR_N) (c_n cx - dr_k' cx m)).
    { apply (dr_sv8_kept W W mem (ms_mem ms0)); [|exact SVN].
      intros x Hx. apply KEEP; [unfold DR_N, DR_CEIL8 in *; lia | unfold dc_out, DR_N, DR_AT in *; lia]. }
    assert (HFL2 : sv8 W (ms_mem ms0) (FF + 120) (flag_addr ly3 1 fpos)).
    { apply (dr_sv8_kept W W mem (ms_mem ms0)); [|exact HFL].
      intros x Hx. apply KEEP; [unfold DR_CEIL8 in *; lia | unfold dc_out, DR_AT in *; lia]. }
    pose proof (st_ok_region_nth _ _ _ 0 _ HS eq_refl) as RG0. cbn [ms_mem restrict] in RG0.
    pose proof (st_ok_region_nth _ _ _ 1 _ HS eq_refl) as RG1. cbn [ms_mem restrict] in RG1.

    assert (S192 : sv8 W (ms_mem ms0) (lf_F cx + DR_AT) 0).
    { unfold sv8, DR_AT.
      lazymatch type of HS with st_ok _ ?Ev _ _ =>
        apply (field_of_region Ev _ 9%nat (lf_F cx) _ _ _ _ _ 192 8%N (SLit 0) 0 RG0) end.
      - rewrite !ew_ewset_other by lia. exact U9.
      - left. reflexivity.
      - reflexivity.
      - lia.
      - lia. }
    assert (VLK : rg_lock fr_RG = 0x5d8ac0) by reflexivity.
    assert (E247 : ew E 247 = Z_to_bv 64 (rg_lock fr_RG)).
    { change 247%nat with (A_OBJ 6). apply bv_eq. rewrite (HEI (A_OBJ 6) ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia)).
      rewrite unsigned_lit_small by (rewrite VLK; lia). vm_compute. reflexivity. }
    assert (S40 : sv8 W (ms_mem ms0) (lf_F cx + 40) (rg_lock fr_RG)).
    { unfold sv8.
      lazymatch type of HS with st_ok _ ?Ev _ _ =>
        apply (field_of_region Ev _ 9%nat (lf_F cx) _ _ _ _ _ 40 8%N (SOff 247 0) (rg_lock fr_RG) RG1) end.
      - rewrite !ew_ewset_other by lia. exact U9.
      - left. reflexivity.
      - cbn [sv_denot]. rewrite !ew_ewset_other by lia. rewrite E247, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
      - rewrite VLK; lia.
      - lia. }

    assert (E28 : ew E 28 = Z_to_bv 64 (c_p cx + dr_k' cx m)) by (rewrite (EEo 28%nat 28%bv eq_refl); exact R28).
    lazymatch type of HS with st_ok _ ?Ev _ _ =>
      assert (HAE2 : env_agree 32 (Ereg regs (dc_extra (re_eof e))) Ev)
        by (split; [intros q Hq; rewrite !ew_ewset_other by lia; exact (proj1 HAE q Hq)
                   | rewrite !ed_ewset; exact (proj2 HAE)]) end.
    pose proof (regs_kept_of_st_ok segs _ _ _ regs _ [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 26; 27]%bv
                  HS HAE2 ltac:(vm_compute; reflexivity)) as KR.
    cbn [ms_regs restrict] in KR.
    prreg HS (1%bv : bv 5) Q1. prreg HS (10%bv : bv 5) Q10. prreg HS (25%bv : bv 5) Q25.
    rewrite ?ew_ewset_other in Q10, Q25 by lia. rewrite E247 in Q10. rewrite E28 in Q25.
    pmkst HS. subst own.
    apply (dc_callsR cx Hpe t m j si h fpos ly3 S3 Hp3 k W _ HB).
    lazymatch goal with |- context [mkCfg (mkst ?r _ ?mm _) ?d] => exists r, mm, d end.
    split; [reflexivity|].
    split; [exact HJ|]. split; [exact HFR2|]. split; [exact HFL2|]. split; [exact HMOD2|]. split; [exact HIN2|].
    split; [exact HRV2|]. split; [exact HROM2|]. split; [exact HSEP|]. split; [exact HLS|]. split; [exact HNP|]. split; [exact HRI|].
    split; [exact Hatop|]. split; [exact Hpick|]. split; [exact Hj|].
    rewrite <- Hedef. split; [exact Hfdj|]. split; [exact Hef0|].
    split; [exact SVN2|]. split; [exact S192|]. split; [exact S40|].
    split; [exact Q1|]. split; [exact Q10|].
    split; [rewrite (KR 2%bv ltac:(cbv; tauto)); exact R2|].
    split; [rewrite (KR 8%bv ltac:(cbv; tauto)); exact R8|].
    split; [rewrite (KR 9%bv ltac:(cbv; tauto)); exact R9|].
    split; [rewrite (KR 18%bv ltac:(cbv; tauto)); exact R18|].
    split; [rewrite (KR 19%bv ltac:(cbv; tauto)); exact R19|].
    split; [rewrite (KR 20%bv ltac:(cbv; tauto)); exact R20|].
    split; [rewrite (KR 23%bv ltac:(cbv; tauto)); exact R23|].
    split; [rewrite (KR 24%bv ltac:(cbv; tauto)); exact R24|].
    split; [rewrite (KR 26%bv ltac:(cbv; tauto)); exact R26|].
    split; [rewrite (KR 3%bv ltac:(cbv; tauto)); exact R3|].
    split; [rewrite (KR 4%bv ltac:(cbv; tauto)); exact R4|].
    split; [rewrite (KR 27%bv ltac:(cbv; tauto)); exact R27|].
    split; [exact Ht|].
    split; [rewrite (KR 21%bv ltac:(cbv; tauto)); exact R21|].
    split; [rewrite (KR 22%bv ltac:(cbv; tauto)); exact R22|].
    exact Q25.
Qed.
(* dr_join_latch at R *)
Lemma dr_join_latchR : forall cx Hpe t W c,
  lf_base_x B MT XM_LIB RLO RHI fr_live_pre LIBROOM NP G_fr ARx cx Hpe ->
  DSTR A_dr_join cx Hpe (t + 1) (lregs_join cx t) W c ->
  SRr segs W c (INV_K_xR B NP G_fr fr_FP PST ARx LSx RINV R cx Hpe t).
Proof.
  intros cx Hpe t W c HB (regs & mem & md & -> & HROM &
    (own & ly3 & S3 & Hp3 & k & m & fpos & HJ & -> & HFR & HFL & HMOD & HIN & HRV & HSEP & HLS & HNP & HRI & HR)).
  destruct HR as (R2 & R8 & R9 & R18 & R19 & R20 & R23 & R24 & R26 & R3 & R4 & R27 & Ht & R25 & SVN & Hk).
  pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs.
  pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  pose proof HB as (HAI & HPRE & _).
  pose proof HPRE as (HAR0 & Hra0 & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
  pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
  pose proof (Z.mod_pos_bound (spZ (c_regs cx) - 320) 32 ltac:(lia)) as HFm.
  assert (HFb : spZ (c_regs cx) - 352 <= lf_F cx <= spZ (c_regs cx) - 320) by (unfold lf_F; lia).
  unfold LLVMF_STK in *.
  pose proof HFR as (FS & FW & F24 & F48 & F56 & F64 & F72 & F80 & F88 & F96 & F184 & Ffull & _).
  destruct (Ffull eq_refl) as (F32 & F104 & F112 & F120 & F128 & F136 & F152).
  destruct (dr_jn_entry W regs mem (lf_F cx) R9 R26 ltac:(lia) ltac:(lia) F104) as [HS SHOK].
  remember (Eimg (Ereg regs [])) as E eqn:HE.
  assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
  assert (E25 : ew E 25 = Z_to_bv 64 (c_p cx + lm_k m))
    by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia);
        rewrite (ew_Ereg_nat regs _ 25 25%bv eq_refl); exact R25).
  assert (HAE : env_agree 32 (Ereg regs []) E)
    by (rewrite HE; split; [intros n Hn; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
  clear HE.
  unfold cfg_at. change (w64 (fr_B0 + A_dr_join)) with (Z_to_bv 64 (BASE + A_dr_join)).
  paj_run_to_tok_x RUNTOR HS HJ SHOK DRspan AF_LLVM_latch.
  { apply awr_ok_x_cons; [intros a Ha; cbn in Ha; lia | apply awr_ok_x_nil]. }
  dr_meq HF Em.
  pose proof (regs_kept_of_st_ok_pi _ _ _ regs _ DR_KEPT HS HAE ltac:(vm_compute; reflexivity)) as KR.
  cbn [ms_regs restrict] in KR.
  prreg HS (22%bv : bv 5) Q22. rewrite E25 in Q22.
  prreg HS (25%bv : bv 5) Q25.
  pmkst HS. rewrite Em in *.
  apply SRr_ret.
  lazymatch goal with |- context [mkCfg (mkst ?r _ ?mm _) ?d] => exists r, mm, d end.
  split; [reflexivity|]. split; [exact HROM|].
  exists [(1, fpos)], ly3, S3, Hp3, k, m, fpos.
  split; [exact HJ|]. split; [reflexivity|]. split; [exact HFR|]. split; [exact HFL|]. split; [exact HMOD|].
  split; [exact HIN|]. split; [exact HRV|]. split; [exact HSEP|]. split; [exact HLS|].
  split; [exact HNP|]. split; [exact HRI|].
  split.
  { split; [rewrite (KR 2%bv ltac:(cbv; tauto)); exact R2|].
    split; [rewrite (KR 8%bv ltac:(cbv; tauto)); exact R8|].
    split; [rewrite (KR 9%bv ltac:(cbv; tauto)); exact R9|].
    split; [rewrite (KR 18%bv ltac:(cbv; tauto)); exact R18|].
    split; [rewrite (KR 19%bv ltac:(cbv; tauto)); exact R19|].
    split; [rewrite (KR 20%bv ltac:(cbv; tauto)); exact R20|].
    split; [rewrite (KR 23%bv ltac:(cbv; tauto)); exact R23|].
    split; [rewrite (KR 24%bv ltac:(cbv; tauto)); exact R24|].
    split; [rewrite Q25; reflexivity|].
    split; [rewrite (KR 26%bv ltac:(cbv; tauto)); exact R26|].
    split; [rewrite (KR 3%bv ltac:(cbv; tauto)); exact R3|].
    rewrite (KR 4%bv ltac:(cbv; tauto)); exact R4. }
  split; [rewrite (KR 27%bv ltac:(cbv; tauto)); exact R27|].
  split; [exact Ht|].
  split; [rewrite Q22; reflexivity|].
  split; [exact SVN|]. exact Hk.
Qed.

(* ------------------------------------------------------------------ the arm at R *)
(* the text of cut_x's Section wR hypothesis ARM_drain_R (W_LLVMFuzzerTestOneInput_cut_x.v:458): the call-free
   segments lifted by SRr_SRrG (WLE_R), composed by SRrG_bind (R_trans) *)
Theorem lf_arm_drain_xR : forall cx Hp t W c,
  lf_base_x B MT XM_LIB RLO RHI fr_live_pre LIBROOM NP G_fr ARx cx Hp ->
  INV_A_xR B NP G_fr fr_FP PST ARx LSx RINV R 2 cx Hp t W c ->
  SRrG segs R W c (INV_K_xR B NP G_fr fr_FP PST ARx LSx RINV R cx Hp t).
Proof.
  intros cx Hpe t W c HB HA.
  eapply (SRrG_bind segs R R_trans); [exact (SRr_SRrG segs R WLE_R _ _ _ (dr_entryR cx Hpe t W c HB HA))|].
  intros W1 c1 _ [(n & HL) | HN].
  - eapply (SRrG_bind segs R R_trans); [exact (SRr_SRrG segs R WLE_R _ _ _ (dr_scanR n cx Hpe t 0 W1 c1 HB HL))|].
    intros W2 c2 _ [(j & HF) | HN].
    + eapply (SRrG_bind segs R R_trans); [exact (dr_found_joinR cx Hpe t j W2 c2 HB HF)|].
      intros W3 c3 _ HJ. exact (SRr_SRrG segs R WLE_R _ _ _ (dr_join_latchR cx Hpe t W3 c3 HB HJ)).
    + eapply (SRrG_bind segs R R_trans); [exact (SRr_SRrG segs R WLE_R _ _ _ (dr_nf_joinR cx Hpe t W2 c2 HB HN))|].
      intros W3 c3 _ HJ. exact (SRr_SRrG segs R WLE_R _ _ _ (dr_join_latchR cx Hpe t W3 c3 HB HJ)).
  - eapply (SRrG_bind segs R R_trans); [exact (SRr_SRrG segs R WLE_R _ _ _ (dr_nf_joinR cx Hpe t W1 c1 HB HN))|].
    intros W3 c3 _ HJ. exact (SRr_SRrG segs R WLE_R _ _ _ (dr_join_latchR cx Hpe t W3 c3 HB HJ)).
Qed.

(* CHECK (cut_x's scope): lf_arm_drain_xR's type is the Section wR hypothesis ARM_drain_R of
   W_LLVMFuzzerTestOneInput_cut_x.v:458, restated with the generic invariants at this Section's variables *)
Lemma lf_arm_drain_xR_check : forall cx Hp t W c,
  lf_base_x B MT XM_LIB RLO RHI fr_live_pre LIBROOM NP G_fr ARx cx Hp ->
  INV_A_xR B NP G_fr fr_FP PST ARx LSx RINV R 2 cx Hp t W c ->
  SRrG segs R W c (INV_K_xR B NP G_fr fr_FP PST ARx LSx RINV R cx Hp t).
Proof. exact lf_arm_drain_xR. Qed.
End drxR.
End drx.
