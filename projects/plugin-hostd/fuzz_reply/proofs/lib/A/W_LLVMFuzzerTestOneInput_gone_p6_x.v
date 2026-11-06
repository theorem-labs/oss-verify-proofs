(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs, 2026-10: the ARx-GENERIC conversion of PHASE 6 of ARM_gone (lib/A/W_LLVMFuzzerTestOneInput_gone_p6.v,
   a Theorem Labs lane's gp6_csd_latch: from GCSD at 0x8494c through check_shape_done and the re-poison of prefix[48] to INV_K
   at the latch 0x84490) to the cut invariants of lib/A/W_LLVMFuzzerTestOneInput_cut_x.v (a Theorem Labs lane's route (b),
   step 7). _gone_p6.v is not edited.
   - gp6_csd_latch_x is gp6_csd_latch's statement over ARx: lf_base_x at the entry's ghost list [], the cut points
     GCSD_x (_gone_base_x.v) and INV_K_x (cut_x) with both ghost lists [], LS -> LSx.  Its proof is _gone_p6.v's,
     converted: the run wrapper SRr_run_to_pi_AJX0_x and W_frame_x's paj_run_to_sh_x, gn_nums_x, W_journal_x's journal
     lemmas (_nil_x, _G_mono_x, _sub_x, _AR_x, _inner_x, rom_pinned_view_x), YCbqG.afn_pre_x_at, W_frame_x's
     aview_above_of_journal_x.
   - The callee check_shape_done is W_contract_x.v:128 csd_spec_x, applied at Hp = []; its post aleaf_post_x keeps the
     ghost list it was called with, so no ghost list is read off its journal.  The journal's image clause has one
     premise more than AR's (the byte is off PST): HPST gives it.
   - Section g6k_x: the nine lemmas of _gone_p6.v's Section g6k that read AR (g6_blk, g6_ib_app, g6_alist, g6_asrc,
     g6_aentry, g6_arelay, g6_aout, g6_amodel_kept, g6_ainput_kept), restated under their names + _x over ARx at the
     ghost list [] (cut_x's HP0), with _gone_p6.v's proofs; cgif's al_blocks -> _gone_tk_x.v's al0_blocks, whose size
     conjunct is BLKN's.  Section gp6_x: g6_afn_pre_at_x and the phase.  Every AR-free name of _gone_p6.v is CITED
     (g6_ib, g6_fp and their lemmas, g6_kcls with the Section's B; g6_sv8_kept, g6_wr_kept, g6_jt_kept,
     g6_gframe_carry, g6_entry1 / g6_entry2, g6_pres, g6_saved, ...); its two section-local tactics g6_inl / g6_cs do
     not survive its Sections and are restated.
   - Section hypotheses beyond the arm's common ones: TL, HGCELLS, HROMPIN verbatim (_gone_p6.v's); CSD at csd_spec_x;
     BLKN (OWED: kit _x twin of al_blocks' last conjunct, W_kit_x.v's text) and HPST (the image is off PST), both
     forced by the generic relation. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YCbqG FCiface YCe5x YGcallx.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import
W_kit_x W_journal_x W_frame_x W_contract_x W_sites_x W_LLVMFuzzerTestOneInput_cut_x.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require W_img_x.
(* _gone_p6.v's own imports, AFTER the generic kit's: the copied proofs see the names they were written against *)
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
HarnessRep RelayRep CheckRep RelayKeys RelayModel.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import W_rep.
Import ListNotations.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import
W_LLVMFuzzerTestOneInput_cut W_contract W_sites W_frame W_rebase W_rep.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import W_LLVMFuzzerTestOneInput_gone_base.
Import ListNotations.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import W_LLVMFuzzerTestOneInput_gone_tk.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import
W_LLVMFuzzerTestOneInput_gone_base_x W_LLVMFuzzerTestOneInput_gone_tk_x W_LLVMFuzzerTestOneInput_gone_p6.
(* the zify flag as _gone_p6.v's proofs expect it (its imports leave the default, true): _gone_tk.v, which _gone_tk_x.v
   requires, sets it to false globally *)
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

(* ================================================================== the transport kit over ARx
   _gone_p6.v:61-494 Section g6k: its AR-reading lemmas at the ghost list [], each with _gone_p6.v's proof *)
Section g6k_x.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Notation segs := (@pa_segs _ fr_prog_listing PB_fr).
Variable B : asyms.
Variable ARx : alayout -> astate -> list Z -> world segs -> (word -> option byte) -> Model -> Prop.
Context {hl : Z}.
Hypothesis LAWS : AR_laws_x segs B ARx hl.
(* OWED: kit _x twin of al_blocks' last conjunct (AR's 0 <= n < MALLOC_MAX, YG0d.v:441; ARx_blocks_law has no size
   conjunct).  The text is W_kit_x.v's BLKN (_gone_tk_x.v's). *)
Hypothesis BLKN : forall ly S Hp (W : world segs) mem md p n, ARx ly S Hp W mem md -> In (p, n) (ablocks B ly S) -> 0 <= n.
Local Notation AR0 ly S W mem md := (ARx ly S [] W mem md).
(* _gone_p6.v's AR-free names that take this Section's B *)
Local Notation g6_ib := (W_LLVMFuzzerTestOneInput_gone_p6.g6_ib B).
Local Notation g6_fp := (W_LLVMFuzzerTestOneInput_gone_p6.g6_fp B).
Local Notation g6_fp_nil := (W_LLVMFuzzerTestOneInput_gone_p6.g6_fp_nil B).
Local Notation g6_fp_cons := (W_LLVMFuzzerTestOneInput_gone_p6.g6_fp_cons B).
Local Notation g6_fp_app := (W_LLVMFuzzerTestOneInput_gone_p6.g6_fp_app B).
Local Notation g6_akept := (W_LLVMFuzzerTestOneInput_gone_p6.g6_akept B).
Local Notation g6_ib_cell := (W_LLVMFuzzerTestOneInput_gone_p6.g6_ib_cell B).
Local Notation g6_ib_blk := (W_LLVMFuzzerTestOneInput_gone_p6.g6_ib_blk B).
(* _gone_p6.v:94 g6_inl, restated (a section-local tactic there) *)
Ltac g6_inl := cbn [In gn_cells]; repeat (first [left; reflexivity | right]).

(* a live block is wholly in low or wholly in high memory (AR_blocks_law's in_app) *)
Lemma g6_blk_x : forall ly S (W : world segs) mem md p n,
  AR0 ly S W mem md -> In (p, n) (ablocks B ly S) ->
  4096 <= p /\ p + req_size n <= alloc_ceiling /\ 0 <= n <= req_size n /\
  (p + req_size n <= kLowMemEnd \/ kHighMemBeg <= p).
Proof.
  intros ly S W mem md p n HAR Hin.
  destruct (al0_blocks B ARx LAWS BLKN ly S W mem md p n HAR Hin) as (_ & H1 & H2 & Happ & _ & _ & H3).
  pose proof (req_size_pos n ltac:(lia)) as [Hr1 Hr2].
  unfold in_app, kLowShadowBeg in Happ.
  split; [lia|]. split; [lia|]. split; [lia|]. unfold kLowMemEnd. lia.
Qed.
(* every byte g6_ib names is app memory below the ceiling, so apart from every shadow byte *)
Lemma g6_ib_app_x : forall ly S (W : world segs) mem md a,
  AR0 ly S W mem md ->
  (forall x, inG gn_cells x -> 0 <= x < kLowMemEnd) ->
  0 <= as_errno B -> as_errno B + 4 <= kLowMemEnd ->
  g6_ib ly S a -> g6_app a.
Proof.
  intros ly S W mem md a HAR HC HE0 HE1 Hib. pose proof g6_ceil_lo as HCL.
  destruct Hib as [Hc | [He | (p & n & Hin & Hb)]];
    [pose proof (HC a Hc) | | destruct (g6_blk_x ly S W mem md p n HAR Hin) as (P1 & P2 & P3 & P4)];
    unfold g6_app, g6_CEIL8, kLowMemEnd, kHighMemBeg in *; lia.
Qed.
(* ---- struct list ---- *)
Lemma g6_alist_x : forall ly S (W : world segs) mem md LA l lines,
  AR0 ly S W mem md -> alist_at B ly S W mem LA l lines ->
  (forall a, LA <= a < LA + 16 -> g6_ib ly S a) ->
  g6_fp ly S (alist_fp LA l) /\ (forall b, In b (alist_blks l) -> In b (ablocks B ly S)).
Proof.
  intros ly S W mem md LA l lines HAR (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9) HLA.
  rewrite Forall_forall in H9.
  assert (HREC : g6_fp ly S (map (fun r => gfp (fst r) (bzs (snd r ++ [Z_to_bv 8 0]))) (hl_recs l))).
  { intros r Hr. apply in_map_iff in Hr as (x & <- & Hx). destruct (H9 x Hx) as (K1 & _).
    destruct (g6_blk_x ly S W mem md _ _ HAR K1) as (P1 & P2 & P3 & P4).
    apply (g6_ib_blk ly S _ _ _ _ K1); cbn [gfp fst snd]; [lia|].
    rewrite g6_bzs_len, length_app. cbn [length]. lia. }
  split.
  - unfold alist_fp. apply g6_fp_cons; [cbn [fst snd]; exact HLA|].
    apply g6_fp_app; [|exact HREC].
    destruct (Z.eqb_spec (hl_cap l) 0) as [Hc|Hc]; [apply g6_fp_nil|].
    destruct H6 as [[Hc0 _] | (Hcp & Hin & Hj & Hg)]; [lia|].
    destruct (g6_blk_x ly S W mem md _ _ HAR Hin) as (P1 & P2 & P3 & P4).
    apply g6_fp_cons; [|apply g6_fp_nil].
    apply (g6_ib_blk ly S _ _ _ _ Hin); cbn [gfp fst snd]; [lia|].
    rewrite g6_bzs_len, length_app, g6_concat_len. unfold hl_n in *. unfold AREC in *. lia.
  - intros b Hb. unfold alist_blks in Hb. apply in_app_or in Hb as [Hb | Hb].
    + destruct (Z.eqb_spec (hl_cap l) 0) as [Hc|Hc]; [destruct Hb|].
      destruct H6 as [[Hc0 _] | (Hcp & Hin & _)]; [lia|]. destruct Hb as [<- | []]. exact Hin.
    + apply in_map_iff in Hb as (x & <- & Hx). exact (proj1 (H9 x Hx)).
Qed.
(* ---- struct source ---- *)
Lemma g6_asrc_x : forall ly S (W : world segs) mem md HA h,
  AR0 ly S W mem md -> asrc_at B ly S W mem HA h ->
  (forall a, HA <= a < HA + ASRC -> g6_ib ly S a) ->
  g6_fp ly S (asrc_fp HA h) /\ (forall b, In b (asrc_blks h) -> In b (ablocks B ly S)).
Proof.
  intros ly S W mem md HA h HAR HS HHA.
  pose proof HS as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Hpend & _ & _ & _ & _ & _ & _ & _ & Hpb & Hpj & _ &
                    _ & Hexp & Hheld & _).
  destruct (g6_alist_x ly S W mem md (HA + 16) (hs_pending h) false HAR Hpend
              ltac:(intros a Ha; apply HHA; unfold ASRC in *; lia)) as [A1 A2].
  destruct (g6_alist_x ly S W mem md (HA + 64) (hs_expected h) true HAR Hexp
              ltac:(intros a Ha; apply HHA; unfold ASRC in *; lia)) as [E1 E2].
  destruct (g6_alist_x ly S W mem md (HA + 80) (hs_held h) true HAR Hheld
              ltac:(intros a Ha; apply HHA; unfold ASRC in *; lia)) as [H1 H2].
  destruct (g6_blk_x ly S W mem md _ _ HAR Hpb) as (P1 & P2 & P3 & P4).
  unfold asrc_fp, asrc_blks. split.
  - apply g6_fp_cons; [cbn [fst snd]; exact HHA|].
    apply g6_fp_cons.
    + apply (g6_ib_blk ly S _ _ _ _ Hpb); cbn [gfp fst snd]; [lia|].
      rewrite g6_bzs_len, Hpj. lia.
    + apply g6_fp_app; [exact A1|]. apply g6_fp_app; [exact E1 | exact H1].
  - intros b [<- | Hb]; [exact Hpb|].
    apply in_app_or in Hb as [Hb | Hb]; [exact (A2 b Hb)|].
    apply in_app_or in Hb as [Hb | Hb]; [exact (E2 b Hb) | exact (H2 b Hb)].
Qed.
(* ---- one source_t of the relay's table: every byte of it is a block byte ---- *)
Lemma g6_aentry_x : forall ly S (W : world segs) mem md e,
  AR0 ly S W mem md -> aentry_ok B ly S W mem e ->
  g6_fp ly S (aentry_fp e) /\ (forall b, In b (aentry_blks e) -> In b (ablocks B ly S)).
Proof.
  intros ly S W mem md e HAR (K1 & K2 & K3 & K4 & K5 & K6 & K7 & K8 & K9 & K10 & K11 & K12 & K13 & K14 & K15).
  rewrite Forall_forall in K15.
  assert (HK : g6_fp ly S (map (fun k => gfp (gestures_end_b_c.key_addr k)
                  (bzs (gestures_end_b_c.key_text k ++ [Z_to_bv 8 0]))) (re_keys e))).
  { intros r Hr. apply in_map_iff in Hr as (k & <- & Hk). destruct (K15 k Hk) as (M1 & _).
    destruct (g6_blk_x ly S W mem md _ _ HAR M1) as (P1 & P2 & P3 & P4).
    apply (g6_ib_blk ly S _ _ _ _ M1); cbn [gfp fst snd]; [lia|].
    rewrite g6_bzs_len, length_app. cbn [length]. lia. }
  unfold aentry_fp, aentry_blks. split.
  - apply g6_fp_app.
    + destruct (Z.eqb_spec (re_cap e) 0) as [Hc|Hc]; [apply g6_fp_nil|].
      destruct K10 as [(Hc0 & _) | (Hcp & Hin & Hj & Hg)]; [lia|].
      destruct (g6_blk_x ly S W mem md _ _ HAR Hin) as (P1 & P2 & P3 & P4).
      apply g6_fp_cons; [|apply g6_fp_nil].
      apply (g6_ib_blk ly S _ _ _ _ Hin); cbn [gfp fst snd]; [lia|].
      rewrite g6_bzs_len, length_app. lia.
    + apply g6_fp_cons; [|exact HK].
      destruct K12 as [(Hz & Hks) | (Hz & Hin & Hk1 & Hk2 & Hg)].
      * intros a Ha. cbn [gfp fst snd] in Ha. rewrite g6_bzs_len, g6_key_ptrs_len, Hks in Ha.
        cbn [length] in Ha. lia.
      * destruct (g6_blk_x ly S W mem md _ _ HAR Hin) as (P1 & P2 & P3 & P4).
        apply (g6_ib_blk ly S _ _ _ _ Hin); cbn [gfp fst snd]; [lia|].
        rewrite g6_bzs_len, g6_key_ptrs_len. unfold re_nheld in Hk1. lia.
  - intros b Hb. apply in_app_or in Hb as [Hb | Hb].
    + destruct (Z.eqb_spec (re_cap e) 0) as [Hc|Hc]; [destruct Hb|].
      destruct K10 as [(Hc0 & _) | (Hcp & Hin & _)]; [lia|]. destruct Hb as [<- | []]. exact Hin.
    + apply in_app_or in Hb as [Hb | Hb]; [|apply in_map_iff in Hb as (k & <- & Hk); exact (proj1 (K15 k Hk))].
      destruct (Z.eqb_spec (re_hp e) 0) as [Hz|Hz]; [destruct Hb|].
      destruct K12 as [(Hz0 & _) | (_ & Hin & _)]; [lia|]. destruct Hb as [<- | []]. exact Hin.
Qed.
(* ---- the relay's table, at fuzz_reply.asan's globals ---- *)
Lemma g6_arelay_x : forall ly S (W : world segs) mem md G es,
  AR0 ly S W mem md -> arelay_at B fr_RG ly S W mem G es ->
  g6_fp ly S (arelay_fp fr_RG G es) /\ (forall b, In b (arelay_blks G es) -> In b (ablocks B ly S)).
Proof.
  intros ly S W mem md G es HAR (R1 & R2 & R3 & R4 & R5 & R6 & R7 & R8 & R9 & R10 & R11).
  destruct (g6_blk_x ly S W mem md _ _ HAR R8) as (P1 & P2 & P3 & P4).
  rewrite Forall_forall in R10.
  assert (HF1 : g6_fp ly S (concat (map aentry_fp es))).
  { intros r Hr. apply in_concat in Hr as (f & Hf & Hr). apply in_map_iff in Hf as (e & <- & He).
    exact (proj1 (g6_aentry_x ly S W mem md e HAR (R10 e He)) r Hr). }
  assert (HF2 : forall b, In b (concat (map aentry_blks es)) -> In b (ablocks B ly S)).
  { intros b Hb. apply in_concat in Hb as (f & Hf & Hb). apply in_map_iff in Hf as (e & <- & He).
    exact (proj2 (g6_aentry_x ly S W mem md e HAR (R10 e He)) b Hb). }
  unfold arelay_fp, arelay_blks. split.
  - apply g6_fp_cons; [cbn [fst snd]; apply (g6_ib_cell ly S (rg_src fr_RG) 8); [g6_inl | lia | lia]|].
    apply g6_fp_cons; [cbn [fst snd]; apply (g6_ib_cell ly S (rg_nsrc fr_RG) 4); [g6_inl | lia | lia]|].
    apply g6_fp_cons; [cbn [fst snd]; apply (g6_ib_cell ly S (rg_capsrc fr_RG) 4); [g6_inl | lia | lia]|].
    apply g6_fp_cons; [|exact HF1].
    apply (g6_ib_blk ly S _ _ _ _ R8); cbn [fst snd]; lia.
  - intros b [<- | Hb]; [exact R8 | exact (HF2 b Hb)].
Qed.
(* ---- the controller's stream: eight cells, errno, and the g_out block ---- *)
Lemma g6_aout_x : forall ly S (W : world segs) mem md c O mx no cap out,
  AR0 ly S W mem md -> aout_at B fr_RG ly S W mem c O mx no cap out ->
  g6_fp ly S (aout_fp B fr_RG cap out) /\ (forall b, In b (aout_blks cap out) -> In b (ablocks B ly S)).
Proof.
  intros ly S W mem md c O mx no cap out HAR HO.
  pose proof HO as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
                    _ & Hblk).
  unfold aout_fp, aout_blks. split.
  - apply g6_fp_cons; [cbn [fst snd]; apply (g6_ib_cell ly S (rg_send_max fr_RG) 8); [g6_inl | lia | lia]|].
    apply g6_fp_cons; [cbn [fst snd]; apply (g6_ib_cell ly S (rg_nout fr_RG) 8); [g6_inl | lia | lia]|].
    apply g6_fp_cons; [cbn [fst snd]; apply (g6_ib_cell ly S (rg_capout fr_RG) 8); [g6_inl | lia | lia]|].
    apply g6_fp_cons; [cbn [fst snd]; apply (g6_ib_cell ly S (rg_out fr_RG) 8); [g6_inl | lia | lia]|].
    apply g6_fp_cons; [cbn [fst snd]; apply (g6_ib_cell ly S (rg_client fr_RG) 4); [g6_inl | lia | lia]|].
    apply g6_fp_cons; [cbn [fst snd]; apply (g6_ib_cell ly S (rg_client_broken fr_RG) 1); [g6_inl | lia | lia]|].
    apply g6_fp_cons; [cbn [fst snd]; apply (g6_ib_cell ly S (rg_send_dead fr_RG) 1); [g6_inl | lia | lia]|].
    apply g6_fp_cons; [cbn [fst snd]; apply (g6_ib_cell ly S (rg_send_eintr fr_RG) 1); [g6_inl | lia | lia]|].
    apply g6_fp_cons; [cbn [fst snd]; intros a Ha; right; left; lia|].
    destruct (Z.eqb_spec cap 0) as [Hc|Hc]; [apply g6_fp_nil|].
    destruct Hblk as [(Hc0 & _) | (Hcp & Hno & Hin & junk & Hj & Hg)]; [lia|].
    destruct (g6_blk_x ly S W mem md _ _ HAR Hin) as (P1 & P2 & P3 & P4).
    apply g6_fp_cons; [|apply g6_fp_nil]. apply (g6_ib_blk ly S _ _ _ _ Hin); cbn [fst snd]; lia.
  - intros b Hb. destruct (Z.eqb_spec cap 0) as [Hc|Hc]; [destruct Hb|].
    destruct Hblk as [(Hc0 & _) | (Hcp & Hno & Hin & _)]; [lia|]. destruct Hb as [<- | []]. exact Hin.
Qed.
(* ---- the model ---- *)
Lemma g6_amodel_kept_x : forall ly S (W : world segs) mem md (W' : world segs) mem' m,
  AR0 ly S W mem md -> amodel_at B ly S W mem m ->
  (forall a, g6_ib ly S a -> abyte_kept W mem W' mem' a) ->
  amodel_at B ly S W' mem' m.
Proof.
  intros ly S W mem md W' mem' m HAR (M1 & M2 & M3 & M4 & M5 & M6 & M7 & M8 & M9 & M10) KEEP.
  assert (KC : forall lo n x, In (lo, n) gn_cells -> lo <= x < lo + n -> abyte_kept W mem W' mem' x).
  { intros lo n x Hin Hx. apply KEEP. left. unfold inG. apply Exists_exists.
    exists (lo, n). split; [exact Hin | unfold in_zr; cbn [fst snd]; lia]. }
  split; [exact M1|]. split.
  { intros i Hi. specialize (M2 i Hi). unfold aslot in *.
    assert (HB : forall a, rg_s fr_RG + ASRC * Z.of_nat i <= a < rg_s fr_RG + ASRC * Z.of_nat i + ASRC ->
                   g6_ib ly S a)
      by (apply (g6_ib_cell ly S (rg_s fr_RG) (4 * ASRC));
          [g6_inl | unfold ASRC in *; lia | unfold ASRC in *; lia]).
    destruct (nth i (lm_hs m) None) as [h|].
    - destruct (g6_asrc_x ly S W mem md _ h HAR M2 HB) as [F1 F2].
      exact (asrc_at_kept B ly S W mem ly S W' mem' _ h M2 (g6_akept ly S W W' mem mem' _ KEEP F1) F2).
    - destruct M2 as [G1 G2]. split.
      + apply (akept_garr8 W mem); [|exact G1]. intros x Hx. rewrite repeat_length in Hx.
        apply KEEP. apply HB. unfold ASRC in *. lia.
      + apply (akept_awr W mem); [|exact G2]. intros x Hx. apply KEEP. apply HB. unfold ASRC in *. lia. }
  split.
  { destruct (g6_arelay_x ly S W mem md (lm_G m) (lm_es m) HAR M3) as [F1 F2].
    exact (arelay_at_kept B fr_RG ly S W mem ly S W' mem' _ _ M3 (g6_akept ly S W W' mem mem' _ KEEP F1) F2). }
  split.
  { destruct (g6_aout_x ly S W mem md _ _ _ _ _ _ HAR M4) as [F1 F2].
    exact (aout_at_kept B fr_RG ly S W mem ly S W' mem' _ _ _ _ _ _ M4
             (g6_akept ly S W W' mem mem' _ KEEP F1) F2). }
  split.
  { apply (agone_at_kept fr_RG W mem W' mem' _ M5).
    intros r [<- | []] x Hx. cbn [fst snd] in Hx. apply (KC (rg_gone fr_RG) 1); [g6_inl | lia]. }
  split.
  { apply (alock_at_kept fr_RG W mem W' mem' _ M6).
    intros r [<- | []] x Hx. cbn [fst snd] in Hx. apply (KC (rg_lock fr_RG) 12); [g6_inl | lia]. }
  split.
  { apply (awake_at_kept fr_RG W mem W' mem' M7).
    intros r [<- | []] x Hx. cbn [fst snd] in Hx. apply (KC (rg_wake fr_RG + 4) 4); [g6_inl | lia]. }
  split.
  { apply (akept_vm W mem); [|exact M8]. intros x Hx. cbn in Hx.
    apply (KC AG_NFD 4); [g6_inl | lia]. }
  split.
  { apply (akept_awr W mem); [|exact M9]. intros x Hx. apply (KC AG_NFD 4); [g6_inl | lia]. }
  destruct M10 as (M10 & M11 & (lst & M12) & M13).
  split; [exact M10|].
  split.
  { apply (akept_vm W mem); [|exact M11]. intros x Hx. cbn in Hx.
    apply (KC AG_THREAD_UP 1); [g6_inl | lia]. }
  split.
  { exists lst. apply (akept_vm W mem); [|exact M12]. intros x Hx. cbn in Hx.
    apply (KC AG_LISTEN 4); [g6_inl | lia]. }
  apply (akept_awr W mem); [|exact M13]. intros x Hx. apply (KC AG_LISTEN 4); [g6_inl | lia].
Qed.
(* ---- the input block ---- *)
Lemma g6_ainput_kept_x : forall cx ly S (W : world segs) mem md (W' : world segs) mem',
  AR0 ly S W mem md -> ainput_at B cx ly S W mem ->
  Z.of_nat (length (c_pl cx)) = c_n cx ->
  (forall a, g6_ib ly S a -> abyte_kept W mem W' mem' a) ->
  ainput_at B cx ly S W' mem'.
Proof.
  intros cx ly S W mem md W' mem' HAR (I1 & I2) Hlen KEEP.
  split; [exact I1|]. apply (akept_garr8 W mem); [|exact I2].
  intros x Hx. rewrite length_map in Hx. rewrite Hlen in Hx.
  destruct I1 as [(Hn & Hp) | (Hn & Hin)]; [lia|].
  destruct (g6_blk_x ly S W mem md _ _ HAR Hin) as (P1 & P2 & P3 & P4).
  apply KEEP. right. right. exists (c_p cx), (c_n cx). split; [exact Hin | lia].
Qed.
End g6k_x.

(* ================================================================== the phase *)
Section gp6_x.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
#[local] Notation segs := (@pa_segs _ fr_prog_listing PB_fr).
Variable B : asyms.
Variable MT : ameter_ops.
Variables XM_LIB : Z -> Z.
Variables RLO RHI : Z.
Variable fr_live_pre : astate -> Prop.
Variables LIBROOM NP : astate -> Prop.
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
#[local] Notation VAL := (@pa_val _ fr_prog_listing PB_fr).
#[local] Notation BASE := (@pa_val _ fr_prog_listing PB_fr A_TEXT).
#[local] Notation SIGMA := (@pa_sigma _ fr_prog_listing PB_fr).
(* the allocator instance (W_kit.v): its api_env (pal_env) puts errno's 4 bytes below kLowMemEnd (_gone_p6.v's TL,
   verbatim) *)
Hypothesis TL : PALib B.
(* check_shape_done (0x85734): W_contract_x.v:128 csd_spec_x, the twin of _gone_p6.v's CSD (W_contract.v:156 csd_spec) *)
Hypothesis CSD : csd_spec_x B PST ARx (BASE + AF_fr_check_shape_done).
(* what carries the model and the read-only image across that call (_gone_p6.v's HGCELLS / HROMPIN, verbatim: base
   GN_HGcells / GN_ROM_PIN): the model's cells are bytes of G_fr, so image bytes that are no allocator static, which the
   callee's journal keeps; and the allocator's own read-only bytes are pinned in every state *)
Hypothesis HGCELLS : GN_HGcells G_fr.
Hypothesis HROMPIN : GN_ROM_PIN B.
(* ---- forced by the generic relation and the placement PST ---- *)
(* OWED: kit _x twin of al_blocks' last conjunct; W_kit_x.v's BLKN *)
Hypothesis BLKN : forall ly S Hp (W : world segs) mem md p n, ARx ly S Hp W mem md -> In (p, n) (ablocks B ly S) -> 0 <= n.
(* the image is off PST (add_x's HPST): the callee journal's image clause takes it; trivial at PST = [] *)
Hypothesis HPST : forall a, in_img segs a -> ~ Exists (in_zr a) PST.
Local Notation AR0 ly S W mem md := (ARx ly S [] W mem md).
Local Notation AJ0 G XO OUT STK sp0 FP ly S W mem md own ly' S' W' mem' md' k :=
  (ajournal_gx_x segs B PST ARx G XO OUT STK sp0 FP ly S [] W mem md own ly' S' [] W' mem' md' k).
Local Notation AJi0 STK sp0 FP ly S W mem md own ly' S' W' mem' md' k :=
  (ajournal_x segs B PST ARx STK sp0 FP ly S [] W mem md own ly' S' [] W' mem' md' k).
Local Notation AFN0 STK ly S W regs mem md ch := (afn_pre_x segs B ARx STK ly S [] W regs mem md ch).
Local Notation LFB0 cx := (lf_base_x B MT XM_LIB RLO RHI fr_live_pre LIBROOM NP G_fr ARx cx []).
(* a ghost list read off an ARx fact, or off a journal's last state, is [] *)
Ltac hp0a H := let E := fresh "EHp" in pose proof (HP0 _ _ _ _ _ _ H) as E;
  lazymatch type of E with ?h = [] => subst h end.
Ltac hp0g HJ := let H := fresh "HARg" in
  pose proof (ajournal_gx_AR_x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as H; hp0a H; clear H.
(* _gone_p6.v's AR-free definition over this Section's B (_gone_p6.v:527 g6_kcls), cited *)
Local Notation g6_kcls := (W_LLVMFuzzerTestOneInput_gone_p6.g6_kcls B).
(* _gone_p6.v:616 g6_cs, restated (a section-local tactic there) *)
Ltac g6_cs := unfold acallee_saved;
  match goal with |- context [bv_unsigned ?r] => let v := eval vm_compute in (bv_unsigned r) in
    change (bv_unsigned r) with v end; lia.

(* _p6.v:535 g6_afn_pre_at: check_shape_done's afn_pre (afn_pre_x at the ghost list []) at sp = F,
   W_LLVMFuzzerTestOneInput_latch.v's lt_afn_pre_at, which reads only the saved ra / s0 of aframe_at (gframe's first
   conjunct is the same) *)
Lemma g6_afn_pre_at_x : forall cx ly3 S3 fpos k (W : world segs) mem md regs STK1,
  LFB0 cx ->
  AJ0 G_fr 0 [] LLVMF_STK (spZ (c_regs cx)) (lf_FP fr_FP cx)
    (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx) [(1, fpos)] ly3 S3 W mem md k ->
  (forall o r, In (o, r) saved_regs ->
     sv8 W mem (spZ (c_regs cx) - o) (bv_unsigned (getr (c_regs cx) (Z_to_bv 5 r)))) ->
  spZ regs = lf_F cx -> YK0s.ret_ok (getr regs 1) -> 4096 <= raZ regs ->
  getr regs 3 = w64 (as_gp B) -> getr regs 4 = w64 (as_tp B) -> getr regs 8 = getr (c_regs cx) 2 ->
  0 <= STK1 -> STK1 + 352 <= LLVMF_STK ->
  exists ch, AFN0 STK1 ly3 S3 W regs mem md ch.
Proof.
  intros cx ly3 S3 fpos k W mem md regs STK1 HB HJ HSV Hsp Hret Hra4 Hgp Htp Hs0 HSTK0 HSTKb.
  destruct HB as (_ & HPRE).
  assert (HPREE : AFN0 LLVMF_STK (c_ly cx) (c_S cx) (c_W cx) (c_regs cx) (c_mem cx) (c_md cx) [])
    by (unfold fr_lib_pre_cf_x in HPRE; tauto).
  pose proof HPREE as (HAR0 & Hra0 & Hra40 & Hgp0 & Htp0 & Hstk0 & Hpres0 & Hch0 & HQT0).
  pose proof Hstk0 as (Hal16 & Hslo0 & Hceil0 & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
  destruct (ajournal_gx_inner_x segs B PST ARx G_fr 0 [] LLVMF_STK (spZ (c_regs cx)) (lf_FP fr_FP cx)
    (c_ly cx) (c_S cx) [] (c_W cx) (c_mem cx) (c_md cx) [(1, fpos)] ly3 S3 [] W mem md k HJ) as (memS & HJ0 & Hmg).
  rewrite !Z.add_0_r in HJ0.
  set (sp0 := spZ (c_regs cx)) in *.
  assert (HF32 : lf_F cx = sp0 - 320 - (sp0 - 320) mod 32) by reflexivity.
  pose proof (Z.mod_pos_bound (sp0 - 320) 32 ltac:(lia)) as Hmb.
  assert (Ho16 : (lf_F cx - sp0) mod 16 = 0).
  { rewrite HF32.
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
  assert (HoNeg : lf_F cx - sp0 <= 0) by (rewrite HF32; lia).
  assert (HoBud : STK1 - (lf_F cx - sp0) <= LLVMF_STK) by (rewrite HF32; lia).
  assert (HTOPeq : ly_top ly3 = ly_top (c_ly cx)).
  { pose proof HJ0 as (_ & Hly & _). pose proof Hly as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & _). exact Etop. }
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  assert (Hs0Z : s0Z regs = sp0) by (unfold s0Z, sp0, spZ; rewrite Hs0; reflexivity).
  destruct (Z_lt_le_dec sp0 (ly_top (c_ly cx) - 16)) as [Hlt | Hge].
  - pose proof (aview_above_of_journal_x (PI := PB_fr) B PST ARx LLVMF_STK sp0 (lf_FP fr_FP cx)
      (c_ly cx) (c_S cx) [] (c_W cx) memS (c_md cx) [(1, fpos)] ly3 S3 [] W mem md k HJ0) as HAB.
    assert (Hra8 : rdword (aview segs (w_H W) mem) (sp0 - 8) = Some (bv_unsigned (getr (c_regs cx) 1))).
    { apply (rdword_of_val_mem segs (w_H W) mem); [exact (HSV 8 1 ltac:(left; reflexivity)) |].
      pose proof (bv_unsigned_in_range 64 (getr (c_regs cx) 1)) as Hr.
      change (bv_modulus 64) with (2 ^ 64) in Hr. lia. }
    assert (Hs016 : rdword (aview segs (w_H W) mem) (sp0 - 16) = Some (bv_unsigned (getr (c_regs cx) 8))).
    { apply (rdword_of_val_mem segs (w_H W) mem); [exact (HSV 16 8 ltac:(right; left; reflexivity)) |].
      pose proof (bv_unsigned_in_range 64 (getr (c_regs cx) 8)) as Hr.
      change (bv_modulus 64) with (2 ^ 64) in Hr. lia. }
    exists ((sp0, bv_unsigned (getr (c_regs cx) 1), bv_unsigned (getr (c_regs cx) 8)) :: []).
    eapply (afn_pre_x_at segs B PST ARx LLVMF_STK sp0 (lf_FP fr_FP cx) (c_ly cx) (c_S cx) [] (c_W cx) memS
      (c_md cx) [(1, fpos)] ly3 S3 [] W mem md k regs STK1 (lf_F cx - sp0) _ HJ0);
      [ rewrite Hsp; lia | exact Ho16 | exact HoNeg | exact HSTK0 | exact HoBud | exact Hret | exact Hra4
      | exact Hgp | exact Htp | ].
    rewrite Hsp, Hs0Z.
    apply (achain_ly_top (c_ly cx) ly3 _ _ _ _ ltac:(exact HTOPeq)).
    eapply (achain_push (c_ly cx) (aview segs (w_H (c_W cx)) (c_mem cx)) (aview segs (w_H W) mem)
      sp0 (bv_unsigned (getr (c_regs cx) 8)) (bv_unsigned (getr (c_regs cx) 1)) [] (lf_F cx));
      [ exact Hch0 | lia
      | intros a Ha; rewrite (HAB a ltac:(lia)); apply Hmg; rewrite unsigned_lit_small by lia; intros HGa;
        pose proof (pa_segs_low a (proj1 (HG a HGa))); lia
      | exact Hra8 | exact Hs016
      | unfold raZ in Hra40; lia | lia | lia | lia | rewrite HF32; lia ].
  - exists [].
    eapply (afn_pre_x_at segs B PST ARx LLVMF_STK sp0 (lf_FP fr_FP cx) (c_ly cx) (c_S cx) [] (c_W cx) memS
      (c_md cx) [(1, fpos)] ly3 S3 [] W mem md k regs STK1 (lf_F cx - sp0) _ HJ0);
      [ rewrite Hsp; lia | exact Ho16 | exact HoNeg | exact HSTK0 | exact HoBud | exact Hret | exact Hra4
      | exact Hgp | exact Htp | ].
    rewrite Hs0Z. left. split; [right; left; rewrite HTOPeq; exact Hge | reflexivity].
Qed.

Theorem gp6_csd_latch_x : forall cx t m mc W c,
  lf_base_x B MT XM_LIB RLO RHI fr_live_pre LIBROOM NP G_fr ARx cx [] ->
  GCSD_x B NP G_fr fr_FP PST ARx LSx RINV cx t m mc W c ->
  SRr segs W c (INV_K_x B NP G_fr fr_FP PST ARx LSx RINV cx [] t).
Proof.
  intros cx t m mc W c HB HC.
  pose (RUNTOP := SRr_run_to_pi_AJX0_x (PL := PL_fr) (PI := PB_fr) B PST ARx LAWS G_fr).
  destruct HC as (regs & mem & md & ly & S & kk & fpos & -> & ((HJ & HGF & S40 & S144 & HIN & HRV & HJT & HFL) & HMOD & HSEP & HNP) &
    HLS & HRI & Hk & Hkq & Ht & S208 & AW192 & R2 & R8 & R9 & R18 & R19 & R23 & R26 & R3 & R4 & R27).
  pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  pose proof (gn_nums_x B MT XM_LIB RLO RHI fr_live_pre LIBROOM NP G_fr fr_FP PST ARx LAWS cx [(1, fpos)] ly S W mem md kk
    fpos HB HJ eq_refl) as NUMS.
  cbv zeta in NUMS.
  destruct NUMS as (Hsp16 & Hsp0 & HF32 & HFb & HFF4 & HFFc & HFFapp & Hfrs & HAR).
  pose proof HB as (HAI0 & HPRE0).
  assert (HlenP : c_n cx = Z.of_nat (length (c_pl cx))) by (unfold fr_lib_pre_cf_x in HPRE0; tauto).
  pose proof (pal_env B TL) as ((HE0 & HE1) & _).
  assert (HFlo : g6_CEIL8 + 32000 <= lf_F cx) by (unfold g6_CEIL8, LLVMF_STK in *; lia).
  assert (HF46 : 2 ^ 46 <= lf_F cx /\ lf_F cx + 320 <= 2 ^ 47) by (unfold LLVMF_STK in *; lia).
  assert (HFF8 : 0 <= frame_addr ly 1 fpos / 8 /\ frame_addr ly 1 fpos / 8 + 16 <= 2 ^ 44)
    by (split; [apply Z.div_pos; lia | lia]).
  (* at = |O| = g_nout (aout_at), the value check_shape_done compares a0 with *)
  pose proof HMOD as (_ & _ & _ & HOUT & _).
  pose proof HOUT as (_ & _ & Mno & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
    _ & Hblk).
  assert (Hn : 0 <= Z.of_nat (length (lm_O mc)) < 2 ^ 64).
  { destruct Hblk as [(Hc0 & _ & Hno) | (Hcp & Hno & Hin & _)]; [lia|].
    destruct (g6_blk_x B ARx LAWS BLKN ly S W mem md _ _ HAR Hin) as (P1 & P2 & P3 & P4). lia. }
  assert (Mno' : val_mem segs (mrestrict (w_H W) mem) (VAL A_g_nout) 8 (Z.of_nat (length (lm_O mc)))).
  { replace (VAL A_g_nout) with (rg_nout fr_RG) by (vm_compute; reflexivity). exact Mno. }
  (* in.p = c_p + kq, the value s6 reloads *)
  assert (HP : 0 <= c_p cx + gn_kq cx m < 2 ^ 64).
  { pose proof HIN as ([(Hn0 & Hp0) | (Hn0 & Hin)] & _).
    - rewrite Hp0. unfold A_EMPTY. lia.
    - destruct (g6_blk_x B ARx LAWS BLKN ly S W mem md _ _ HAR Hin) as (P1 & P2 & P3 & P4). lia. }
  (* ---- 0x8494c-0x84950: ld a0,208(s1); jal check_shape_done ---- *)
  pose proof (g6_entry1 W regs mem (lf_F cx) (Z.of_nat (length (lm_O mc))) (proj1 HF46) (proj2 HF46) HF32 R2 R9
    S208 Hn) as HS.
  remember (Eimg (Ereg regs (g6_extra1 (Z.of_nat (length (lm_O mc)))))) as E eqn:HE.
  assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
  assert (E32 : ew E 32 = Z_to_bv 64 (Z.of_nat (length (lm_O mc))))
    by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
  assert (HAE : env_agree 32 (Ereg regs (g6_extra1 (Z.of_nat (length (lm_O mc))))) E)
    by (rewrite HE; split; [intros q Hq; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
  clear HE.
  unfold cfg_at. change (w64 (fr_B0 + AF_gn_csd)) with (Z_to_bv 64 (BASE + AF_gn_csd)).
  paj_run_to_sh_x RUNTOP HS HJ AF_fr_check_shape_done.
  { intros a (r & Hin & Hr). vm_compute in Hin. destruct Hin as [<- | []].
    cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr. lia. }
  lazymatch goal with H : mem_grows _ _ |- _ => rename H into HGR1 end.
  cbn [ms_mem mkst] in HF, HFr, HGR1.
  lazymatch type of HF with frame_of ?E0 ?rs ?m0 ?m1 =>
    pose proof (frame_of_read_only E0 rs m0 m1 ltac:(vm_compute; reflexivity) HF) as Em1 end.
  pose proof (regs_kept_of_st_ok_pi _ _ _ regs _ g6_saved HS HAE ltac:(vm_compute; reflexivity)) as KR1.
  cbn [ms_regs restrict] in KR1.
  prreg HS (1%bv : bv 5) Q1. prreg HS (10%bv : bv 5) Q10. rewrite E32 in Q10.
  pmkst HS. rewrite Em1 in *.
  clear HF HFr HGR1.
  rename ms into ms1, mat into mat1.
  set (mdc := with_vm_backing (m_vm_lazy md) mat1 md) in *.
  assert (Hsp1 : spZ (ms_regs ms1) = lf_F cx).
  { unfold spZ. rewrite (KR1 2%bv ltac:(cbv; tauto)), R2. unfold w64. apply unsigned_lit_small. lia. }
  pose proof HGF as (HSV & HFW & G24 & G48 & G56 & G64 & G72 & G80 & G88 & G96 & G184 & G32 & G104 & G112 & G120 &
    G128 & G136 & G152 & GFF0 & GFF8 & GFF16 & GFFW & GSH & GSHW).
  destruct (g6_afn_pre_at_x cx ly S fpos kk W mem mdc (ms_regs ms1) CSD_STK HB HJ HSV Hsp1) as (ch & HPREc).
  { rewrite Q1. apply ret_ok_codeptr_v; [lia | reflexivity]. }
  { unfold raZ. rewrite Q1, unsigned_lit_small by lia. lia. }
  { rewrite (KR1 3%bv ltac:(cbv; tauto)). exact R3. }
  { rewrite (KR1 4%bv ltac:(cbv; tauto)). exact R4. }
  { rewrite (KR1 8%bv ltac:(cbv; tauto)). exact R8. }
  { unfold CSD_STK. lia. }
  { unfold CSD_STK, LLVMF_STK. lia. }
  eapply SRr_bind.
  { exact (CSD W ly S [] (ms_regs ms1) mem mdc ch (Z.of_nat (length (lm_O mc))) HPREc Q10 Hn Mno'). }
  intros W2 c2 Hwle2 (regs2 & mem2 & md2 & -> & HJc & HP2 & _ & HPR2 & HEV).
  rewrite Hsp1 in HJc.
  pose proof HJc as (_ & _ & _ & _ & _ & _ & _ & _ & JH & JB & JI & JF & _).
  (* check_shape_done's journal inside this function's: W2's ajournal_gx_sub at G_fr, lifted from the donor's journal
     (G = []), as p4 does for check_no_loss_read *)
  assert (HJc0 : AJ0 [] 0 [] CSD_STK (lf_F cx) [] ly S W mem mdc [] ly S W2 mem2 md2 0)
    by (apply ajournal_gx_nil_x; exact HJc).
  assert (HJc' : AJ0 G_fr 0 [] CSD_STK (lf_F cx) [] ly S W mem mdc [] ly S W2 mem2 md2 0).
  { refine (ajournal_gx_G_mono_x segs B PST ARx [] G_fr 0 [] CSD_STK (lf_F cx) [] ly S [] W mem mdc [] ly S [] W2 mem2 md2
      0 _ HJc0).
    intros a Ha. exfalso. exact (inG_nil a Ha). }
  pose proof (ajournal_gx_sub_x segs B PST ARx LAWS pa_segs_low G_fr LLVMF_STK (spZ (c_regs cx)) 0 [] (lf_FP fr_FP cx)
     (c_ly cx) (c_S cx) [] (c_W cx) (c_mem cx) (c_md cx) [(1, fpos)] ly S [] W mem mdc kk
     CSD_STK (lf_F cx) 0 [] [] [] ly S [] W2 mem2 md2 0 HJ HJc'
     ltac:(unfold CSD_STK, LLVMF_STK in *; lia) ltac:(lia) ltac:(lia)
     ltac:(intros a Ha; exfalso; exact (inFP_nil a Ha)) HG
     ltac:(intros a Ha; exfalso; exact (inFP_nil a Ha))) as HJ2.
  cbn [app] in HJ2. rewrite Z.add_0_r in HJ2.
  clear HJc HJc0 HJc'.
  (* the bytes the call kept (g6_kcls): the post's view clauses and errno's view; writability from presence and wle *)
  assert (HK2 : forall a, g6_kcls cx ly S a -> abyte_kept W mem W2 mem2 a).
  { intros a Kc. split; [|exact (g6_wr_kept W W2 mem mem2 a (HPR2 a) Hwle2)].
    destruct Kc as [(Kh1 & Kh2) | [(pb & nb & Kin & Kr) | [(Ki & Ko) | [Ke | (cid & pos & Kin & Kr)]]]].
    - apply JH; [exact Kh1 | unfold CSD_STK; lia].
    - replace a with (pb + (a - pb)) by lia.
      apply (JB pb nb (a - pb)); [exact Kin | exact Kin | lia | intros Kf; exact (inFP_nil _ Kf)].
    - destruct (Z_le_dec (as_errno B) a) as [Ke1|Ke1]; [destruct (Z_lt_dec a (as_errno B + 4)) as [Ke2|Ke2]|].
      + replace a with (as_errno B + (a - as_errno B)) by lia. apply HEV. lia.
      + apply JI; [exact Ki | exact Ko | lia | exact (HPST a Ki) | apply fp_spares_closed; exact sink_closed_nil].
      + apply JI; [exact Ki | exact Ko | lia | exact (HPST a Ki) | apply fp_spares_closed; exact sink_closed_nil].
    - replace a with (as_errno B + (a - as_errno B)) by lia. apply HEV. lia.
    - apply (JF cid pos a Kin Kr). intros Kf. exact (inFP_nil _ Kf). }
  (* the cells the tail reads, kept across the call *)
  assert (KCh : forall a, lf_F cx <= a < 2 ^ 64 -> abyte_kept W mem W2 mem2 a).
  { intros a Ha. apply HK2. left. split; [unfold g6_CEIL8 in HFlo; lia | lia]. }
  assert (M40 : sv8 W2 mem2 (lf_F cx + 40) (c_p cx + gn_kq cx m))
    by (apply (g6_sv8_kept W W2 mem mem2); [intros x Hx; apply KCh; lia | exact S40]).
  assert (M96 : sv8 W2 mem2 (lf_F cx + 96) (SB + frame_addr ly 1 fpos / 8))
    by (apply (g6_sv8_kept W W2 mem mem2); [intros x Hx; apply KCh; lia | exact G96]).
  assert (M104 : sv8 W2 mem2 (lf_F cx + 104) HI_G_NOUT)
    by (apply (g6_sv8_kept W W2 mem mem2); [intros x Hx; apply KCh; lia | exact G104]).
  (* the fake frame (class 1, the frame S holds) and its shadow are frame bytes of S *)
  assert (Hfin : In (1, fpos) (frames S)) by (rewrite Hfrs; left; reflexivity).
  assert (KFS : forall a, frame_addr ly 1 fpos <= a < frame_addr ly 1 fpos + 128 \/
      SB + frame_addr ly 1 fpos / 8 <= a < SB + frame_addr ly 1 fpos / 8 + 16 -> g6_kcls cx ly S a).
  { intros a Ha. right; right; right; right. exists 1, fpos. split; [exact Hfin|].
    unfold in_zr, frame_rng, shadow_addr, SHADOW_OFF. cbn [fst snd]. change (fs_frame_bytes 1) with 128.
    change (128 / 8) with 16. unfold SB in Ha. lia. }
  assert (AWsh : awr W2 mem2 (SB + frame_addr ly 1 fpos / 8) 16).
  { apply (akept_awr W mem W2 mem2); [|exact GSHW]. intros x Hx. apply HK2, KFS. right. lia. }
  assert (R9b : getr regs2 9 = w64 (lf_F cx)).
  { rewrite (g6_pres (ms_regs ms1) regs2 9%bv HP2 ltac:(g6_cs)). rewrite (KR1 9%bv ltac:(cbv; tauto)). exact R9. }
  (* ---- 0x84954-0x84980: the re-poison of prefix[48], s9, s4, s6, and the jump to the latch ---- *)
  rewrite Q1. change (Z_to_bv 64 (BASE + 9832)) with (Z_to_bv 64 (BASE + AF_g6_ret)).
  pose proof (g6_entry2 W2 regs2 mem2 (lf_F cx) (c_p cx + gn_kq cx m) (frame_addr ly 1 fpos)
    (proj1 HF46) (proj2 HF46) HF32 R9b ltac:(lia) ltac:(lia) HP M40 M96 M104 AWsh) as HS2.
  remember (Eimg (Ereg regs2 (g6_extra2 (c_p cx + gn_kq cx m) (SB + frame_addr ly 1 fpos / 8)))) as E2 eqn:HE2.
  assert (HEI2 : img_env VAL A_LIM E2) by (subst E2; apply Eimg_env).
  assert (E2_32 : ew E2 32 = Z_to_bv 64 (c_p cx + gn_kq cx m))
    by (subst E2; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs2 _ 0)).
  assert (E2_33 : ew E2 33 = Z_to_bv 64 (SB + frame_addr ly 1 fpos / 8))
    by (subst E2; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs2 _ 1)).
  assert (U2_33 : bv_unsigned (ew E2 33) = SB + frame_addr ly 1 fpos / 8)
    by (rewrite E2_33; apply unsigned_lit_small; unfold SB; lia).
  assert (HAE2 : env_agree 32 (Ereg regs2 (g6_extra2 (c_p cx + gn_kq cx m) (SB + frame_addr ly 1 fpos / 8))) E2)
    by (rewrite HE2; split; [intros q Hq; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
  clear HE2.
  paj_run_to_sh_x RUNTOP HS2 HJ2 AF_LLVM_latch.
  { (* the six stores hit the shadow of the fake frame the function owns *)
    intros a (r & Hin & Hr). vm_compute in Hin.
    destruct Hin as [<- | [<- | []]]; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr; [lia|].
    rewrite U2_33 in Hr. right; right; right.
    exists 1, fpos. split; [left; reflexivity|]. right. unfold in_zr, shadow_addr, SHADOW_OFF. cbn [fst snd].
    change (fs_frame_bytes 1 / 8) with 16. unfold SB in Hr. lia. }
  lazymatch goal with H : mem_grows _ _ |- _ => rename H into HGR2 end.
  cbn [ms_mem mkst] in HF, HFr, HGR2.
  pose proof (regs_kept_of_st_ok_pi _ _ _ regs2 _ g6_saved HS2 HAE2 ltac:(vm_compute; reflexivity)) as KR2.
  cbn [ms_regs restrict] in KR2.
  prreg HS2 (20%bv : bv 5) Q20. prreg HS2 (22%bv : bv 5) Q22. prreg HS2 (24%bv : bv 5) Q24.
  prreg HS2 (25%bv : bv 5) Q25.
  rewrite E2_32 in Q22. rewrite E2_33 in Q24.
  pose proof (st_ok_pi_region_nth _ _ _ 1 _ HS2 eq_refl) as RG1. cbn [ms_mem restrict] in RG1.
  pmkst HS2.
  (* the six shadow bytes now hold 0xf8, and are still writable *)
  assert (NEW : forall i, 4 <= i < 10 ->
      mbyte segs (arm W2 (ms_mem ms)) (SB + frame_addr ly 1 fpos / 8 + i) = Some (Z_to_bv 8 248) /\
      writable_at segs (arm W2 (ms_mem ms)) (SB + frame_addr ly 1 fpos / 8 + i)).
  { destruct RG1 as (_ & _ & RW & RC).
    cbn [YP09.r_base YP09.r_wlo YP09.r_whi YP09.r_chunks base_val] in RW, RC. rewrite U2_33 in RW, RC.
    intros i Hi. split; [|exact (RW i Hi)].
    rewrite Forall_forall in RC.
    assert (Hi6 : i = 4 \/ i = 5 \/ i = 6 \/ i = 7 \/ i = 8 \/ i = 9) by lia.
    unfold arm.
    destruct Hi6 as [-> | [-> | [-> | [-> | [-> | ->]]]]];
      (lazymatch goal with |- mbyte _ _ (_ + ?o) = _ =>
         destruct (RC (YP09.mkChunk o (CVal 1 (SLit 18446744073709551608)))
                    ltac:(cbn [In]; repeat (first [left; reflexivity | right])) 0 ltac:(cbn; lia))
           as (bb & Hcb & Hmb) end;
       cbn [YP09.c_off YP09.c_val YP09.cbyte sv_denot] in Hcb, Hmb; rewrite Z.add_0_r in Hmb; rewrite Hmb;
       injection Hcb as <-; f_equal; apply bv_eq; vm_compute; reflexivity). }
  (* every byte the call kept (g6_kcls) is kept from the cut point but the six shadow bytes the re-poison writes *)
  assert (KALL : forall a, 0 <= a < 2 ^ 64 -> g6_kcls cx ly S a ->
      ~ (SB + frame_addr ly 1 fpos / 8 + 4 <= a < SB + frame_addr ly 1 fpos / 8 + 10) ->
      abyte_kept W mem W2 (ms_mem ms) a).
  { intros a Ha Kc Hn2. destruct (HK2 a Kc) as [V1 Wr1]. split.
    - rewrite <- V1. apply (aview_kept_out E2 _ (w_H W2) mem2 (ms_mem ms) HFr a Ha).
      intros (r & Hin & Hr). vm_compute in Hin.
      destruct Hin as [<- | [<- | []]]; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr; [lia|].
      rewrite U2_33 in Hr. exact (Hn2 Hr).
    - intros Hw. apply (writable_kept (w_H W2) mem2 (ms_mem ms) a);
        [intros Hp; exact (apresent_grows _ _ _ _ HGR2 Hp) | exact (Wr1 Hw)]. }
  (* the stack from F up; the fake frame; its shadow but the six re-poisoned bytes *)
  assert (KH : forall a, lf_F cx <= a < 2 ^ 64 -> abyte_kept W mem W2 (ms_mem ms) a).
  { intros a Ha. apply KALL; [lia | left; split; [unfold g6_CEIL8 in HFlo; lia | lia] | unfold SB in *; lia]. }
  assert (KF : forall a, frame_addr ly 1 fpos <= a < frame_addr ly 1 fpos + 128 -> abyte_kept W mem W2 (ms_mem ms) a).
  { intros a Ha. apply KALL; [lia | apply KFS; left; exact Ha |].
    revert Ha HFF8 HFF4 HFFc HFFapp. clear.
    unfold in_app, kLowShadowBeg, kLowMemEnd, kHighMemBeg, ASAN_CEIL, SB. intros. lia. }
  assert (KS : forall i, 0 <= i < 16 -> ~ (4 <= i < 10) ->
      abyte_kept W mem W2 (ms_mem ms) (SB + frame_addr ly 1 fpos / 8 + i)).
  { intros i Hi Hi'. apply KALL; [unfold SB; lia | apply KFS; right; lia | lia]. }
  (* the model's cells, errno and the live blocks (g6_ib): app memory below the ceiling, so not the shadow *)
  assert (HC : forall x, inG gn_cells x -> 0 <= x < kLowMemEnd).
  { intros x Hx. pose proof (pa_segs_low x (proj1 (HG x (HGCELLS x Hx)))) as HL. unfold kLowMemEnd in *. lia. }
  assert (KIB : forall a, g6_ib B ly S a -> abyte_kept W mem W2 (ms_mem ms) a).
  { intros a Hib. pose proof (g6_ib_app_x B ARx LAWS BLKN ly S W mem md a HAR HC HE0 HE1 Hib) as (Ha1 & Ha2).
    apply KALL; [unfold g6_CEIL8 in Ha1; lia | | unfold g6_CEIL8, SB, kLowMemEnd, kHighMemBeg in *; lia].
    destruct Hib as [Hc | [He | (pb & nb & Hin & Hr)]].
    - right; right; left. exact (conj (proj1 (HG a (HGCELLS a Hc))) (proj1 (proj2 (HG a (HGCELLS a Hc))))).
    - right; right; right; left. exact He.
    - right; left. exists pb, nb. split; [exact Hin | exact Hr]. }
  (* the read-only image: the allocator's own bytes pinned in both states, the others kept by the call's image
     clause (p4's ROMK) *)
  pose proof (ajournal_gx_AR_x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ2) as HAR2.
  assert (ROMK : forall a, in_rom segs a -> aview segs (w_H W2) (ms_mem ms) a = aview segs (w_H W) mem a).
  { intros a Ha.
    assert (Him : in_img segs a) by (destruct Ha as (sg & Hs & _ & Hr); exists sg; split; [exact Hs | exact Hr]).
    destruct (Exists_dec (in_zr a) (as_owned_static B)) as [Ho|Ho].
    { intros r. unfold in_zr. destruct (Z_le_dec (fst r) a); destruct (Z_lt_dec a (fst r + snd r));
        [left; lia | right; lia | right; lia | right; lia]. }
    - pose proof (HROMPIN a Ha Ho) as Hp.
      rewrite (rom_pinned_view_x segs B ARx LAWS ly S [] W2 (ms_mem ms) _ a HAR2 Hp),
        (rom_pinned_view_x segs B ARx LAWS ly S [] W mem md a HAR Hp).
      reflexivity.
    - pose proof (pa_segs_low a Him) as HL.
      refine (proj1 (KALL a _ _ _)); [unfold kLowMemEnd in HL; lia | right; right; left; exact (conj Him Ho) |].
      unfold SB, kLowMemEnd in *. lia. }
  (* the cut's facts at the latch *)
  assert (HGF2 : gframe cx fake_shadow (frame_addr ly 1 fpos) W2 (ms_mem ms))
    by exact (g6_gframe_carry cx (frame_addr ly 1 fpos) W W2 mem (ms_mem ms) HGF KH KF KS NEW
                ltac:(lia) ltac:(lia)).
  pose proof (aframe_of_gframe cx (frame_addr ly 1 fpos) W2 (ms_mem ms) HGF2) as HFR2.
  pose proof (g6_amodel_kept_x B ARx LAWS BLKN ly S W mem md W2 (ms_mem ms) mc HAR HMOD KIB) as HMOD2.
  pose proof (g6_ainput_kept_x B ARx LAWS BLKN cx ly S W mem md W2 (ms_mem ms) HAR HIN (eq_sym HlenP) KIB) as HIN2.
  assert (HRV2 : rom_view segs W2 (ms_mem ms)) by (intros a Ha; rewrite (ROMK a Ha); exact (HRV a Ha)).
  pose proof (g6_jt_kept W W2 mem (ms_mem ms) HRV HRV2 HJT) as HJT2.
  assert (S144' : sv8 W2 (ms_mem ms) (lf_F cx + 144) (c_n cx - gn_kq cx m)).
  { apply (g6_sv8_kept W W2 mem (ms_mem ms)); [|exact S144]. intros x Hx. apply KH. lia. }
  (* the fake frame's flag word: FF + 120 lies in the fake frame *)
  assert (HFL' : sv8 W2 (ms_mem ms) (frame_addr ly 1 fpos + 120) (flag_addr ly 1 fpos)).
  { apply (g6_sv8_kept W W2 mem (ms_mem ms)); [|exact HFL]. intros x Hx. apply KF. lia. }
  (* the registers: the call keeps the callee-saved ones, the two runs write a0, s4, s6, s8, s9 only *)
  assert (RR : forall r : bv 5, In r g6_saved -> getr (ms_regs ms) r = getr regs r).
  { intros r Hr. rewrite (KR2 r Hr). rewrite <- (KR1 r Hr).
    unfold g6_saved in Hr. cbn [In] in Hr.
    repeat (destruct Hr as [<- | Hr]; [apply (g6_pres _ _ _ HP2); g6_cs |]). destruct Hr. }
  apply SRr_ret.
  lazymatch goal with |- context [mkCfg (mkst ?r _ ?mm _) ?d] => exists r, mm, d end.
  split; [reflexivity|]. split; [exact HJT2|].
  exists [(1, fpos)], ly, S, [], kk, mc, fpos.
  split; [exact HJ2|]. split; [reflexivity|]. split; [exact HFR2|]. split; [exact HFL'|]. split; [exact HMOD2|].
  split; [exact HIN2|]. split; [exact HRV2|]. split; [exact HSEP|]. split; [exact HLS|]. split; [exact HNP|]. split; [exact HRI|].
  split.
  { split; [rewrite (RR 2%bv ltac:(cbv; tauto)); exact R2|].
    split; [rewrite (RR 8%bv ltac:(cbv; tauto)); exact R8|].
    split; [rewrite (RR 9%bv ltac:(cbv; tauto)); exact R9|].
    split; [rewrite (RR 18%bv ltac:(cbv; tauto)); exact R18|].
    split; [rewrite (RR 19%bv ltac:(cbv; tauto)); exact R19|].
    split; [exact Q20|].
    split; [rewrite (RR 23%bv ltac:(cbv; tauto)); exact R23|].
    split; [exact Q24|].
    split; [exact Q25|].
    split; [rewrite (RR 26%bv ltac:(cbv; tauto)); exact R26|].
    split; [rewrite (RR 3%bv ltac:(cbv; tauto)); exact R3|].
    rewrite (RR 4%bv ltac:(cbv; tauto)); exact R4. }
  split; [rewrite (RR 27%bv ltac:(cbv; tauto)); exact R27|].
  split; [exact Ht|].
  split; [rewrite Q22, Hk; reflexivity|].
  split; [rewrite Hk; exact S144'|].
  rewrite Hk. exact Hkq.
Qed.

(* ---- route R (RULE-SHAPES.md (sha256 2e856ce788dd; internal record) sec 0): GP6 over the cut journal at a world relation R (the base's GCSD_xR to cut_x's
   INV_K_xR).  check_shape_done stays at its strict spec CSD (a leaf that frees nothing; a Theorem Labs lane's ruling), so the
   phase stays strict SRr over the R journal: its plain runs are the base's SRr_run_to_pi_AJX0_xR, its journal reads
   the _xR twins (ajournal_gx_inner_xR, aview_above_of_journal_xR, afn_pre_x_atR, ajournal_gx_AR_xR, gn_nums_xR); the
   callee's strict journal, made a gx journal at G_fr as in the strict proof, is lifted to R by ajournal_gx_xR_mono
   (WLE_R) and composed with the cut journal by ajournal_gx_sub_xR (R_trans).  The proofs are the strict ones above
   with those names.  At R := wle each text is the strict one. *)
Section gp6_xR.
Variable R : world segs -> world segs -> Prop.
Hypothesis R_refl : forall W, R W W.
Hypothesis R_trans : forall W1 W2 W3, R W1 W2 -> R W2 W3 -> R W1 W3.
Hypothesis WLE_R : forall W W', wle W W' -> R W W'.
Local Notation AJ0R G XO OUT STK sp0 FP ly S W mem md own ly' S' W' mem' md' k :=
  (ajournal_gx_xR segs B PST ARx R G XO OUT STK sp0 FP ly S [] W mem md own ly' S' [] W' mem' md' k).
Local Notation AJi0R STK sp0 FP ly S W mem md own ly' S' W' mem' md' k :=
  (ajournal_xR segs B PST ARx R STK sp0 FP ly S [] W mem md own ly' S' [] W' mem' md' k).
(* g6_afn_pre_at_x over the journal at R *)
Lemma g6_afn_pre_at_xR : forall cx ly3 S3 fpos k (W : world segs) mem md regs STK1,
  LFB0 cx ->
  AJ0R G_fr 0 [] LLVMF_STK (spZ (c_regs cx)) (lf_FP fr_FP cx)
    (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx) [(1, fpos)] ly3 S3 W mem md k ->
  (forall o r, In (o, r) saved_regs ->
     sv8 W mem (spZ (c_regs cx) - o) (bv_unsigned (getr (c_regs cx) (Z_to_bv 5 r)))) ->
  spZ regs = lf_F cx -> YK0s.ret_ok (getr regs 1) -> 4096 <= raZ regs ->
  getr regs 3 = w64 (as_gp B) -> getr regs 4 = w64 (as_tp B) -> getr regs 8 = getr (c_regs cx) 2 ->
  0 <= STK1 -> STK1 + 352 <= LLVMF_STK ->
  exists ch, AFN0 STK1 ly3 S3 W regs mem md ch.
Proof.
  intros cx ly3 S3 fpos k W mem md regs STK1 HB HJ HSV Hsp Hret Hra4 Hgp Htp Hs0 HSTK0 HSTKb.
  destruct HB as (_ & HPRE).
  assert (HPREE : AFN0 LLVMF_STK (c_ly cx) (c_S cx) (c_W cx) (c_regs cx) (c_mem cx) (c_md cx) [])
    by (unfold fr_lib_pre_cf_x in HPRE; tauto).
  pose proof HPREE as (HAR0 & Hra0 & Hra40 & Hgp0 & Htp0 & Hstk0 & Hpres0 & Hch0 & HQT0).
  pose proof Hstk0 as (Hal16 & Hslo0 & Hceil0 & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
  destruct (ajournal_gx_inner_xR segs B PST ARx G_fr 0 [] LLVMF_STK (spZ (c_regs cx)) (lf_FP fr_FP cx)
    (c_ly cx) (c_S cx) [] (c_W cx) (c_mem cx) (c_md cx) [(1, fpos)] ly3 S3 [] W mem md k HJ) as (memS & HJ0 & Hmg).
  rewrite !Z.add_0_r in HJ0.
  set (sp0 := spZ (c_regs cx)) in *.
  assert (HF32 : lf_F cx = sp0 - 320 - (sp0 - 320) mod 32) by reflexivity.
  pose proof (Z.mod_pos_bound (sp0 - 320) 32 ltac:(lia)) as Hmb.
  assert (Ho16 : (lf_F cx - sp0) mod 16 = 0).
  { rewrite HF32.
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
  assert (HoNeg : lf_F cx - sp0 <= 0) by (rewrite HF32; lia).
  assert (HoBud : STK1 - (lf_F cx - sp0) <= LLVMF_STK) by (rewrite HF32; lia).
  assert (HTOPeq : ly_top ly3 = ly_top (c_ly cx)).
  { pose proof HJ0 as (_ & Hly & _). pose proof Hly as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & _). exact Etop. }
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  assert (Hs0Z : s0Z regs = sp0) by (unfold s0Z, sp0, spZ; rewrite Hs0; reflexivity).
  destruct (Z_lt_le_dec sp0 (ly_top (c_ly cx) - 16)) as [Hlt | Hge].
  - pose proof (aview_above_of_journal_xR (PI := PB_fr) B PST ARx LLVMF_STK sp0 (lf_FP fr_FP cx)
      (c_ly cx) (c_S cx) [] (c_W cx) memS (c_md cx) [(1, fpos)] ly3 S3 [] W mem md k HJ0) as HAB.
    assert (Hra8 : rdword (aview segs (w_H W) mem) (sp0 - 8) = Some (bv_unsigned (getr (c_regs cx) 1))).
    { apply (rdword_of_val_mem segs (w_H W) mem); [exact (HSV 8 1 ltac:(left; reflexivity)) |].
      pose proof (bv_unsigned_in_range 64 (getr (c_regs cx) 1)) as Hr.
      change (bv_modulus 64) with (2 ^ 64) in Hr. lia. }
    assert (Hs016 : rdword (aview segs (w_H W) mem) (sp0 - 16) = Some (bv_unsigned (getr (c_regs cx) 8))).
    { apply (rdword_of_val_mem segs (w_H W) mem); [exact (HSV 16 8 ltac:(right; left; reflexivity)) |].
      pose proof (bv_unsigned_in_range 64 (getr (c_regs cx) 8)) as Hr.
      change (bv_modulus 64) with (2 ^ 64) in Hr. lia. }
    exists ((sp0, bv_unsigned (getr (c_regs cx) 1), bv_unsigned (getr (c_regs cx) 8)) :: []).
    eapply (afn_pre_x_atR segs B PST ARx LLVMF_STK sp0 (lf_FP fr_FP cx) (c_ly cx) (c_S cx) [] (c_W cx) memS
      (c_md cx) [(1, fpos)] ly3 S3 [] W mem md k regs STK1 (lf_F cx - sp0) _ HJ0);
      [ rewrite Hsp; lia | exact Ho16 | exact HoNeg | exact HSTK0 | exact HoBud | exact Hret | exact Hra4
      | exact Hgp | exact Htp | ].
    rewrite Hsp, Hs0Z.
    apply (achain_ly_top (c_ly cx) ly3 _ _ _ _ ltac:(exact HTOPeq)).
    eapply (achain_push (c_ly cx) (aview segs (w_H (c_W cx)) (c_mem cx)) (aview segs (w_H W) mem)
      sp0 (bv_unsigned (getr (c_regs cx) 8)) (bv_unsigned (getr (c_regs cx) 1)) [] (lf_F cx));
      [ exact Hch0 | lia
      | intros a Ha; rewrite (HAB a ltac:(lia)); apply Hmg; rewrite unsigned_lit_small by lia; intros HGa;
        pose proof (pa_segs_low a (proj1 (HG a HGa))); lia
      | exact Hra8 | exact Hs016
      | unfold raZ in Hra40; lia | lia | lia | lia | rewrite HF32; lia ].
  - exists [].
    eapply (afn_pre_x_atR segs B PST ARx LLVMF_STK sp0 (lf_FP fr_FP cx) (c_ly cx) (c_S cx) [] (c_W cx) memS
      (c_md cx) [(1, fpos)] ly3 S3 [] W mem md k regs STK1 (lf_F cx - sp0) _ HJ0);
      [ rewrite Hsp; lia | exact Ho16 | exact HoNeg | exact HSTK0 | exact HoBud | exact Hret | exact Hra4
      | exact Hgp | exact Htp | ].
    rewrite Hs0Z. left. split; [right; left; rewrite HTOPeq; exact Hge | reflexivity].
Qed.

(* GP6 at R: GCSD_xR at 0x8494c to INV_K_xR at the latch 0x84490 *)
Theorem gp6_csd_latch_xR : forall cx t m mc W c,
  lf_base_x B MT XM_LIB RLO RHI fr_live_pre LIBROOM NP G_fr ARx cx [] ->
  GCSD_xR B NP G_fr fr_FP PST ARx LSx RINV R cx t m mc W c ->
  SRr segs W c (INV_K_xR B NP G_fr fr_FP PST ARx LSx RINV R cx [] t).
Proof.
  intros cx t m mc W c HB HC.
  pose (RUNTOP := SRr_run_to_pi_AJX0_xR (PL := PL_fr) (PI := PB_fr) B PST ARx LAWS G_fr R).
  destruct HC as (regs & mem & md & ly & S & kk & fpos & -> & ((HJ & HGF & S40 & S144 & HIN & HRV & HJT & HFL) & HMOD & HSEP & HNP) &
    HLS & HRI & Hk & Hkq & Ht & S208 & AW192 & R2 & R8 & R9 & R18 & R19 & R23 & R26 & R3 & R4 & R27).
  pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  pose proof (gn_nums_xR B MT XM_LIB RLO RHI fr_live_pre LIBROOM NP G_fr fr_FP PST ARx LAWS R cx [(1, fpos)] ly S W mem
    md kk fpos HB HJ eq_refl) as NUMS.
  cbv zeta in NUMS.
  destruct NUMS as (Hsp16 & Hsp0 & HF32 & HFb & HFF4 & HFFc & HFFapp & Hfrs & HAR).
  pose proof HB as (HAI0 & HPRE0).
  assert (HlenP : c_n cx = Z.of_nat (length (c_pl cx))) by (unfold fr_lib_pre_cf_x in HPRE0; tauto).
  pose proof (pal_env B TL) as ((HE0 & HE1) & _).
  assert (HFlo : g6_CEIL8 + 32000 <= lf_F cx) by (unfold g6_CEIL8, LLVMF_STK in *; lia).
  assert (HF46 : 2 ^ 46 <= lf_F cx /\ lf_F cx + 320 <= 2 ^ 47) by (unfold LLVMF_STK in *; lia).
  assert (HFF8 : 0 <= frame_addr ly 1 fpos / 8 /\ frame_addr ly 1 fpos / 8 + 16 <= 2 ^ 44)
    by (split; [apply Z.div_pos; lia | lia]).
  (* at = |O| = g_nout (aout_at), the value check_shape_done compares a0 with *)
  pose proof HMOD as (_ & _ & _ & HOUT & _).
  pose proof HOUT as (_ & _ & Mno & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
    _ & Hblk).
  assert (Hn : 0 <= Z.of_nat (length (lm_O mc)) < 2 ^ 64).
  { destruct Hblk as [(Hc0 & _ & Hno) | (Hcp & Hno & Hin & _)]; [lia|].
    destruct (g6_blk_x B ARx LAWS BLKN ly S W mem md _ _ HAR Hin) as (P1 & P2 & P3 & P4). lia. }
  assert (Mno' : val_mem segs (mrestrict (w_H W) mem) (VAL A_g_nout) 8 (Z.of_nat (length (lm_O mc)))).
  { replace (VAL A_g_nout) with (rg_nout fr_RG) by (vm_compute; reflexivity). exact Mno. }
  (* in.p = c_p + kq, the value s6 reloads *)
  assert (HP : 0 <= c_p cx + gn_kq cx m < 2 ^ 64).
  { pose proof HIN as ([(Hn0 & Hp0) | (Hn0 & Hin)] & _).
    - rewrite Hp0. unfold A_EMPTY. lia.
    - destruct (g6_blk_x B ARx LAWS BLKN ly S W mem md _ _ HAR Hin) as (P1 & P2 & P3 & P4). lia. }
  (* ---- 0x8494c-0x84950: ld a0,208(s1); jal check_shape_done ---- *)
  pose proof (g6_entry1 W regs mem (lf_F cx) (Z.of_nat (length (lm_O mc))) (proj1 HF46) (proj2 HF46) HF32 R2 R9
    S208 Hn) as HS.
  remember (Eimg (Ereg regs (g6_extra1 (Z.of_nat (length (lm_O mc)))))) as E eqn:HE.
  assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
  assert (E32 : ew E 32 = Z_to_bv 64 (Z.of_nat (length (lm_O mc))))
    by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
  assert (HAE : env_agree 32 (Ereg regs (g6_extra1 (Z.of_nat (length (lm_O mc))))) E)
    by (rewrite HE; split; [intros q Hq; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
  clear HE.
  unfold cfg_at. change (w64 (fr_B0 + AF_gn_csd)) with (Z_to_bv 64 (BASE + AF_gn_csd)).
  paj_run_to_sh_x RUNTOP HS HJ AF_fr_check_shape_done.
  { intros a (r & Hin & Hr). vm_compute in Hin. destruct Hin as [<- | []].
    cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr. lia. }
  lazymatch goal with H : mem_grows _ _ |- _ => rename H into HGR1 end.
  cbn [ms_mem mkst] in HF, HFr, HGR1.
  lazymatch type of HF with frame_of ?E0 ?rs ?m0 ?m1 =>
    pose proof (frame_of_read_only E0 rs m0 m1 ltac:(vm_compute; reflexivity) HF) as Em1 end.
  pose proof (regs_kept_of_st_ok_pi _ _ _ regs _ g6_saved HS HAE ltac:(vm_compute; reflexivity)) as KR1.
  cbn [ms_regs restrict] in KR1.
  prreg HS (1%bv : bv 5) Q1. prreg HS (10%bv : bv 5) Q10. rewrite E32 in Q10.
  pmkst HS. rewrite Em1 in *.
  clear HF HFr HGR1.
  rename ms into ms1, mat into mat1.
  set (mdc := with_vm_backing (m_vm_lazy md) mat1 md) in *.
  assert (Hsp1 : spZ (ms_regs ms1) = lf_F cx).
  { unfold spZ. rewrite (KR1 2%bv ltac:(cbv; tauto)), R2. unfold w64. apply unsigned_lit_small. lia. }
  pose proof HGF as (HSV & HFW & G24 & G48 & G56 & G64 & G72 & G80 & G88 & G96 & G184 & G32 & G104 & G112 & G120 &
    G128 & G136 & G152 & GFF0 & GFF8 & GFF16 & GFFW & GSH & GSHW).
  destruct (g6_afn_pre_at_xR cx ly S fpos kk W mem mdc (ms_regs ms1) CSD_STK HB HJ HSV Hsp1) as (ch & HPREc).
  { rewrite Q1. apply ret_ok_codeptr_v; [lia | reflexivity]. }
  { unfold raZ. rewrite Q1, unsigned_lit_small by lia. lia. }
  { rewrite (KR1 3%bv ltac:(cbv; tauto)). exact R3. }
  { rewrite (KR1 4%bv ltac:(cbv; tauto)). exact R4. }
  { rewrite (KR1 8%bv ltac:(cbv; tauto)). exact R8. }
  { unfold CSD_STK. lia. }
  { unfold CSD_STK, LLVMF_STK. lia. }
  (* the strict callee: SRr_bind at CSD (csd_spec_x) *)
  eapply SRr_bind.
  { exact (CSD W ly S [] (ms_regs ms1) mem mdc ch (Z.of_nat (length (lm_O mc))) HPREc Q10 Hn Mno'). }
  intros W2 c2 Hwle2 (regs2 & mem2 & md2 & -> & HJc & HP2 & _ & HPR2 & HEV).
  rewrite Hsp1 in HJc.
  pose proof HJc as (_ & _ & _ & _ & _ & _ & _ & _ & JH & JB & JI & JF & _).
  (* check_shape_done's strict journal inside this function's: the gx journal at G_fr as in the strict proof, lifted to
     R (WLE_R), then composed with the cut journal at R (R_trans) *)
  assert (HJc0 : AJ0 [] 0 [] CSD_STK (lf_F cx) [] ly S W mem mdc [] ly S W2 mem2 md2 0)
    by (apply ajournal_gx_nil_x; exact HJc).
  assert (HJc' : AJ0 G_fr 0 [] CSD_STK (lf_F cx) [] ly S W mem mdc [] ly S W2 mem2 md2 0).
  { refine (ajournal_gx_G_mono_x segs B PST ARx [] G_fr 0 [] CSD_STK (lf_F cx) [] ly S [] W mem mdc [] ly S [] W2 mem2 md2
      0 _ HJc0).
    intros a Ha. exfalso. exact (inG_nil a Ha). }
  assert (HJcR : AJ0R G_fr 0 [] CSD_STK (lf_F cx) [] ly S W mem mdc [] ly S W2 mem2 md2 0).
  { apply (ajournal_gx_xR_mono segs B PST ARx (@wle segs) R WLE_R). rewrite <- ajournal_gx_x_wle. exact HJc'. }
  pose proof (ajournal_gx_sub_xR segs B PST ARx LAWS pa_segs_low R_trans G_fr LLVMF_STK (spZ (c_regs cx)) 0 []
     (lf_FP fr_FP cx) (c_ly cx) (c_S cx) [] (c_W cx) (c_mem cx) (c_md cx) [(1, fpos)] ly S [] W mem mdc kk
     CSD_STK (lf_F cx) 0 [] [] [] ly S [] W2 mem2 md2 0 HJ HJcR
     ltac:(unfold CSD_STK, LLVMF_STK in *; lia) ltac:(lia) ltac:(lia)
     ltac:(intros a Ha; exfalso; exact (inFP_nil a Ha)) HG
     ltac:(intros a Ha; exfalso; exact (inFP_nil a Ha))) as HJ2.
  cbn [app] in HJ2. rewrite Z.add_0_r in HJ2.
  clear HJc HJc0 HJc' HJcR.
  (* the bytes the call kept (g6_kcls): the post's view clauses and errno's view; writability from presence and wle *)
  assert (HK2 : forall a, g6_kcls cx ly S a -> abyte_kept W mem W2 mem2 a).
  { intros a Kc. split; [|exact (g6_wr_kept W W2 mem mem2 a (HPR2 a) Hwle2)].
    destruct Kc as [(Kh1 & Kh2) | [(pb & nb & Kin & Kr) | [(Ki & Ko) | [Ke | (cid & pos & Kin & Kr)]]]].
    - apply JH; [exact Kh1 | unfold CSD_STK; lia].
    - replace a with (pb + (a - pb)) by lia.
      apply (JB pb nb (a - pb)); [exact Kin | exact Kin | lia | intros Kf; exact (inFP_nil _ Kf)].
    - destruct (Z_le_dec (as_errno B) a) as [Ke1|Ke1]; [destruct (Z_lt_dec a (as_errno B + 4)) as [Ke2|Ke2]|].
      + replace a with (as_errno B + (a - as_errno B)) by lia. apply HEV. lia.
      + apply JI; [exact Ki | exact Ko | lia | exact (HPST a Ki) | apply fp_spares_closed; exact sink_closed_nil].
      + apply JI; [exact Ki | exact Ko | lia | exact (HPST a Ki) | apply fp_spares_closed; exact sink_closed_nil].
    - replace a with (as_errno B + (a - as_errno B)) by lia. apply HEV. lia.
    - apply (JF cid pos a Kin Kr). intros Kf. exact (inFP_nil _ Kf). }
  (* the cells the tail reads, kept across the call *)
  assert (KCh : forall a, lf_F cx <= a < 2 ^ 64 -> abyte_kept W mem W2 mem2 a).
  { intros a Ha. apply HK2. left. split; [unfold g6_CEIL8 in HFlo; lia | lia]. }
  assert (M40 : sv8 W2 mem2 (lf_F cx + 40) (c_p cx + gn_kq cx m))
    by (apply (g6_sv8_kept W W2 mem mem2); [intros x Hx; apply KCh; lia | exact S40]).
  assert (M96 : sv8 W2 mem2 (lf_F cx + 96) (SB + frame_addr ly 1 fpos / 8))
    by (apply (g6_sv8_kept W W2 mem mem2); [intros x Hx; apply KCh; lia | exact G96]).
  assert (M104 : sv8 W2 mem2 (lf_F cx + 104) HI_G_NOUT)
    by (apply (g6_sv8_kept W W2 mem mem2); [intros x Hx; apply KCh; lia | exact G104]).
  (* the fake frame (class 1, the frame S holds) and its shadow are frame bytes of S *)
  assert (Hfin : In (1, fpos) (frames S)) by (rewrite Hfrs; left; reflexivity).
  assert (KFS : forall a, frame_addr ly 1 fpos <= a < frame_addr ly 1 fpos + 128 \/
      SB + frame_addr ly 1 fpos / 8 <= a < SB + frame_addr ly 1 fpos / 8 + 16 -> g6_kcls cx ly S a).
  { intros a Ha. right; right; right; right. exists 1, fpos. split; [exact Hfin|].
    unfold in_zr, frame_rng, shadow_addr, SHADOW_OFF. cbn [fst snd]. change (fs_frame_bytes 1) with 128.
    change (128 / 8) with 16. unfold SB in Ha. lia. }
  assert (AWsh : awr W2 mem2 (SB + frame_addr ly 1 fpos / 8) 16).
  { apply (akept_awr W mem W2 mem2); [|exact GSHW]. intros x Hx. apply HK2, KFS. right. lia. }
  assert (R9b : getr regs2 9 = w64 (lf_F cx)).
  { rewrite (g6_pres (ms_regs ms1) regs2 9%bv HP2 ltac:(g6_cs)). rewrite (KR1 9%bv ltac:(cbv; tauto)). exact R9. }
  (* ---- 0x84954-0x84980: the re-poison of prefix[48], s9, s4, s6, and the jump to the latch ---- *)
  rewrite Q1. change (Z_to_bv 64 (BASE + 9832)) with (Z_to_bv 64 (BASE + AF_g6_ret)).
  pose proof (g6_entry2 W2 regs2 mem2 (lf_F cx) (c_p cx + gn_kq cx m) (frame_addr ly 1 fpos)
    (proj1 HF46) (proj2 HF46) HF32 R9b ltac:(lia) ltac:(lia) HP M40 M96 M104 AWsh) as HS2.
  remember (Eimg (Ereg regs2 (g6_extra2 (c_p cx + gn_kq cx m) (SB + frame_addr ly 1 fpos / 8)))) as E2 eqn:HE2.
  assert (HEI2 : img_env VAL A_LIM E2) by (subst E2; apply Eimg_env).
  assert (E2_32 : ew E2 32 = Z_to_bv 64 (c_p cx + gn_kq cx m))
    by (subst E2; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs2 _ 0)).
  assert (E2_33 : ew E2 33 = Z_to_bv 64 (SB + frame_addr ly 1 fpos / 8))
    by (subst E2; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs2 _ 1)).
  assert (U2_33 : bv_unsigned (ew E2 33) = SB + frame_addr ly 1 fpos / 8)
    by (rewrite E2_33; apply unsigned_lit_small; unfold SB; lia).
  assert (HAE2 : env_agree 32 (Ereg regs2 (g6_extra2 (c_p cx + gn_kq cx m) (SB + frame_addr ly 1 fpos / 8))) E2)
    by (rewrite HE2; split; [intros q Hq; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
  clear HE2.
  paj_run_to_sh_x RUNTOP HS2 HJ2 AF_LLVM_latch.
  { (* the six stores hit the shadow of the fake frame the function owns *)
    intros a (r & Hin & Hr). vm_compute in Hin.
    destruct Hin as [<- | [<- | []]]; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr; [lia|].
    rewrite U2_33 in Hr. right; right; right.
    exists 1, fpos. split; [left; reflexivity|]. right. unfold in_zr, shadow_addr, SHADOW_OFF. cbn [fst snd].
    change (fs_frame_bytes 1 / 8) with 16. unfold SB in Hr. lia. }
  lazymatch goal with H : mem_grows _ _ |- _ => rename H into HGR2 end.
  cbn [ms_mem mkst] in HF, HFr, HGR2.
  pose proof (regs_kept_of_st_ok_pi _ _ _ regs2 _ g6_saved HS2 HAE2 ltac:(vm_compute; reflexivity)) as KR2.
  cbn [ms_regs restrict] in KR2.
  prreg HS2 (20%bv : bv 5) Q20. prreg HS2 (22%bv : bv 5) Q22. prreg HS2 (24%bv : bv 5) Q24.
  prreg HS2 (25%bv : bv 5) Q25.
  rewrite E2_32 in Q22. rewrite E2_33 in Q24.
  pose proof (st_ok_pi_region_nth _ _ _ 1 _ HS2 eq_refl) as RG1. cbn [ms_mem restrict] in RG1.
  pmkst HS2.
  (* the six shadow bytes now hold 0xf8, and are still writable *)
  assert (NEW : forall i, 4 <= i < 10 ->
      mbyte segs (arm W2 (ms_mem ms)) (SB + frame_addr ly 1 fpos / 8 + i) = Some (Z_to_bv 8 248) /\
      writable_at segs (arm W2 (ms_mem ms)) (SB + frame_addr ly 1 fpos / 8 + i)).
  { destruct RG1 as (_ & _ & RW & RC).
    cbn [YP09.r_base YP09.r_wlo YP09.r_whi YP09.r_chunks base_val] in RW, RC. rewrite U2_33 in RW, RC.
    intros i Hi. split; [|exact (RW i Hi)].
    rewrite Forall_forall in RC.
    assert (Hi6 : i = 4 \/ i = 5 \/ i = 6 \/ i = 7 \/ i = 8 \/ i = 9) by lia.
    unfold arm.
    destruct Hi6 as [-> | [-> | [-> | [-> | [-> | ->]]]]];
      (lazymatch goal with |- mbyte _ _ (_ + ?o) = _ =>
         destruct (RC (YP09.mkChunk o (CVal 1 (SLit 18446744073709551608)))
                    ltac:(cbn [In]; repeat (first [left; reflexivity | right])) 0 ltac:(cbn; lia))
           as (bb & Hcb & Hmb) end;
       cbn [YP09.c_off YP09.c_val YP09.cbyte sv_denot] in Hcb, Hmb; rewrite Z.add_0_r in Hmb; rewrite Hmb;
       injection Hcb as <-; f_equal; apply bv_eq; vm_compute; reflexivity). }
  (* every byte the call kept (g6_kcls) is kept from the cut point but the six shadow bytes the re-poison writes *)
  assert (KALL : forall a, 0 <= a < 2 ^ 64 -> g6_kcls cx ly S a ->
      ~ (SB + frame_addr ly 1 fpos / 8 + 4 <= a < SB + frame_addr ly 1 fpos / 8 + 10) ->
      abyte_kept W mem W2 (ms_mem ms) a).
  { intros a Ha Kc Hn2. destruct (HK2 a Kc) as [V1 Wr1]. split.
    - rewrite <- V1. apply (aview_kept_out E2 _ (w_H W2) mem2 (ms_mem ms) HFr a Ha).
      intros (r & Hin & Hr). vm_compute in Hin.
      destruct Hin as [<- | [<- | []]]; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr; [lia|].
      rewrite U2_33 in Hr. exact (Hn2 Hr).
    - intros Hw. apply (writable_kept (w_H W2) mem2 (ms_mem ms) a);
        [intros Hp; exact (apresent_grows _ _ _ _ HGR2 Hp) | exact (Wr1 Hw)]. }
  (* the stack from F up; the fake frame; its shadow but the six re-poisoned bytes *)
  assert (KH : forall a, lf_F cx <= a < 2 ^ 64 -> abyte_kept W mem W2 (ms_mem ms) a).
  { intros a Ha. apply KALL; [lia | left; split; [unfold g6_CEIL8 in HFlo; lia | lia] | unfold SB in *; lia]. }
  assert (KF : forall a, frame_addr ly 1 fpos <= a < frame_addr ly 1 fpos + 128 -> abyte_kept W mem W2 (ms_mem ms) a).
  { intros a Ha. apply KALL; [lia | apply KFS; left; exact Ha |].
    revert Ha HFF8 HFF4 HFFc HFFapp. clear.
    unfold in_app, kLowShadowBeg, kLowMemEnd, kHighMemBeg, ASAN_CEIL, SB. intros. lia. }
  assert (KS : forall i, 0 <= i < 16 -> ~ (4 <= i < 10) ->
      abyte_kept W mem W2 (ms_mem ms) (SB + frame_addr ly 1 fpos / 8 + i)).
  { intros i Hi Hi'. apply KALL; [unfold SB; lia | apply KFS; right; lia | lia]. }
  (* the model's cells, errno and the live blocks (g6_ib): app memory below the ceiling, so not the shadow *)
  assert (HC : forall x, inG gn_cells x -> 0 <= x < kLowMemEnd).
  { intros x Hx. pose proof (pa_segs_low x (proj1 (HG x (HGCELLS x Hx)))) as HL. unfold kLowMemEnd in *. lia. }
  assert (KIB : forall a, g6_ib B ly S a -> abyte_kept W mem W2 (ms_mem ms) a).
  { intros a Hib. pose proof (g6_ib_app_x B ARx LAWS BLKN ly S W mem md a HAR HC HE0 HE1 Hib) as (Ha1 & Ha2).
    apply KALL; [unfold g6_CEIL8 in Ha1; lia | | unfold g6_CEIL8, SB, kLowMemEnd, kHighMemBeg in *; lia].
    destruct Hib as [Hc | [He | (pb & nb & Hin & Hr)]].
    - right; right; left. exact (conj (proj1 (HG a (HGCELLS a Hc))) (proj1 (proj2 (HG a (HGCELLS a Hc))))).
    - right; right; right; left. exact He.
    - right; left. exists pb, nb. split; [exact Hin | exact Hr]. }
  (* the read-only image: the allocator's own bytes pinned in both states, the others kept by the call's image
     clause (p4's ROMK) *)
  pose proof (ajournal_gx_AR_xR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ2) as HAR2.
  assert (ROMK : forall a, in_rom segs a -> aview segs (w_H W2) (ms_mem ms) a = aview segs (w_H W) mem a).
  { intros a Ha.
    assert (Him : in_img segs a) by (destruct Ha as (sg & Hs & _ & Hr); exists sg; split; [exact Hs | exact Hr]).
    destruct (Exists_dec (in_zr a) (as_owned_static B)) as [Ho|Ho].
    { intros r. unfold in_zr. destruct (Z_le_dec (fst r) a); destruct (Z_lt_dec a (fst r + snd r));
        [left; lia | right; lia | right; lia | right; lia]. }
    - pose proof (HROMPIN a Ha Ho) as Hp.
      rewrite (rom_pinned_view_x segs B ARx LAWS ly S [] W2 (ms_mem ms) _ a HAR2 Hp),
        (rom_pinned_view_x segs B ARx LAWS ly S [] W mem md a HAR Hp).
      reflexivity.
    - pose proof (pa_segs_low a Him) as HL.
      refine (proj1 (KALL a _ _ _)); [unfold kLowMemEnd in HL; lia | right; right; left; exact (conj Him Ho) |].
      unfold SB, kLowMemEnd in *. lia. }
  (* the cut's facts at the latch *)
  assert (HGF2 : gframe cx fake_shadow (frame_addr ly 1 fpos) W2 (ms_mem ms))
    by exact (g6_gframe_carry cx (frame_addr ly 1 fpos) W W2 mem (ms_mem ms) HGF KH KF KS NEW
                ltac:(lia) ltac:(lia)).
  pose proof (aframe_of_gframe cx (frame_addr ly 1 fpos) W2 (ms_mem ms) HGF2) as HFR2.
  pose proof (g6_amodel_kept_x B ARx LAWS BLKN ly S W mem md W2 (ms_mem ms) mc HAR HMOD KIB) as HMOD2.
  pose proof (g6_ainput_kept_x B ARx LAWS BLKN cx ly S W mem md W2 (ms_mem ms) HAR HIN (eq_sym HlenP) KIB) as HIN2.
  assert (HRV2 : rom_view segs W2 (ms_mem ms)) by (intros a Ha; rewrite (ROMK a Ha); exact (HRV a Ha)).
  pose proof (g6_jt_kept W W2 mem (ms_mem ms) HRV HRV2 HJT) as HJT2.
  assert (S144' : sv8 W2 (ms_mem ms) (lf_F cx + 144) (c_n cx - gn_kq cx m)).
  { apply (g6_sv8_kept W W2 mem (ms_mem ms)); [|exact S144]. intros x Hx. apply KH. lia. }
  (* the fake frame's flag word: FF + 120 lies in the fake frame *)
  assert (HFL' : sv8 W2 (ms_mem ms) (frame_addr ly 1 fpos + 120) (flag_addr ly 1 fpos)).
  { apply (g6_sv8_kept W W2 mem (ms_mem ms)); [|exact HFL]. intros x Hx. apply KF. lia. }
  (* the registers: the call keeps the callee-saved ones, the two runs write a0, s4, s6, s8, s9 only *)
  assert (RR : forall r : bv 5, In r g6_saved -> getr (ms_regs ms) r = getr regs r).
  { intros r Hr. rewrite (KR2 r Hr). rewrite <- (KR1 r Hr).
    unfold g6_saved in Hr. cbn [In] in Hr.
    repeat (destruct Hr as [<- | Hr]; [apply (g6_pres _ _ _ HP2); g6_cs |]). destruct Hr. }
  apply SRr_ret.
  lazymatch goal with |- context [mkCfg (mkst ?r _ ?mm _) ?d] => exists r, mm, d end.
  split; [reflexivity|]. split; [exact HJT2|].
  exists [(1, fpos)], ly, S, [], kk, mc, fpos.
  split; [exact HJ2|]. split; [reflexivity|]. split; [exact HFR2|]. split; [exact HFL'|]. split; [exact HMOD2|].
  split; [exact HIN2|]. split; [exact HRV2|]. split; [exact HSEP|]. split; [exact HLS|]. split; [exact HNP|]. split; [exact HRI|].
  split.
  { split; [rewrite (RR 2%bv ltac:(cbv; tauto)); exact R2|].
    split; [rewrite (RR 8%bv ltac:(cbv; tauto)); exact R8|].
    split; [rewrite (RR 9%bv ltac:(cbv; tauto)); exact R9|].
    split; [rewrite (RR 18%bv ltac:(cbv; tauto)); exact R18|].
    split; [rewrite (RR 19%bv ltac:(cbv; tauto)); exact R19|].
    split; [exact Q20|].
    split; [rewrite (RR 23%bv ltac:(cbv; tauto)); exact R23|].
    split; [exact Q24|].
    split; [exact Q25|].
    split; [rewrite (RR 26%bv ltac:(cbv; tauto)); exact R26|].
    split; [rewrite (RR 3%bv ltac:(cbv; tauto)); exact R3|].
    rewrite (RR 4%bv ltac:(cbv; tauto)); exact R4. }
  split; [rewrite (RR 27%bv ltac:(cbv; tauto)); exact R27|].
  split; [exact Ht|].
  split; [rewrite Q22, Hk; reflexivity|].
  split; [rewrite Hk; exact S144'|].
  rewrite Hk. exact Hkq.
Qed.
End gp6_xR.
End gp6_x.
