(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ARM_gone of the ASan walk of fuzz_reply's LLVMFuzzerTestOneInput, PHASE 6
   (W_LLVMFuzzerTestOneInput_gone.v GP6): from GCSD at 0x8494c to INV_K at the latch 0x84490 (fuzz_reply.c:654 and
   the arm's tail):
     0x8494c  ld a0,208(s1); jal check_shape_done      a0 = at = |O|, the value of g_nout (the error path is not reached)
     0x84954  ld s8,96(s1); li a0,-8; sb a0,4..9(s8)    prefix[48]'s six shadow bytes go back to 0xf8
     0x84974  ld s9,104(s1); li s4,10; ld s6,40(s1); j 84490
   check_shape_done is TAKEN FROM W3's PUBLISHED CONTRACT (CSD : csd_spec, W_contract.v:130 on the W8 lane head
   a3c72093c22, over aleaf_post :102), not re-walked.
   What this file proves besides the phase:
   - the transport kit of W_LLVMFuzzerTestOneInput_latch.v (its lt_ lemmas, via _gone_tk.v's gk_ copy) over the
     bytes W3's post keeps: a cell of the model (gn_cells, base), errno, or a byte of a live block (g6_ib).
     aleaf_post's journal keeps an image byte's view only where the byte is not an allocator static
     (Reusable/YCbq.v:363) and its last conjunct keeps errno's view, so the kit's old "every byte below
     alloc_ceiling + 8" is not available; the fake frame and its shadow, which the re-poison writes, are outside
     g6_ib anyway and are carried by the journal's high-memory and frame clauses (g6_kcls, p4's gp4_kcls);
   - g6_gframe_carry: the frame with prefix[48] unpoisoned (fake_shadow_open), carried across the call and the
     re-poison, is the frame with the shadow poisoned again (fake_shadow), i.e. aframe_at (aframe_of_gframe).
   Section hypotheses beyond the arm's common ones: TL : PALib B (the allocator instance, W_kit.v), for its
   api_env (errno lies in the image, below kLowMemEnd); CSD, the callee contract; and the base's model
   obligations HGCELLS : GN_HGcells G_fr and HROMPIN : GN_ROM_PIN B, already hypotheses of lf_arm_gone (p3 / p4 /
   p5 take them), for the model's cells and for rom_view / jt_rom across the call. *)
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
HarnessRep RelayRep CheckRep RelayKeys RelayModel.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import W_rep.
Import ListNotations.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import
W_LLVMFuzzerTestOneInput_cut W_contract W_sites W_frame W_rebase W_rep.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import W_LLVMFuzzerTestOneInput_gone_base.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

(* ================================================================== the transport kit
   W_LLVMFuzzerTestOneInput_latch.v's Section kit and lt_*_kept (here from _gone_tk.v's copy, gk_ -> g6_), with
   "every byte below alloc_ceiling + 8" sharpened to g6_ib: a cell of the model (gn_cells), errno, or a byte of a
   live block.  That is what W3's aleaf_post keeps: the journal's image clause asks the byte not to be an
   allocator static (Reusable/YCbq.v:363), which GN_HGcells gives through gx_ok for a cell, and the post's last
   conjunct keeps errno's view.  Every such byte is also apart from the fake frame's shadow, which the re-poison
   writes (g6_ib_app: it is app memory below the ceiling, so below kLowMemEnd or at or above kHighMemBeg). *)
Section g6k.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Notation segs := (@pa_segs _ fr_prog_listing PB_fr).
Variable B : asyms.
Hypothesis LAWS : AR_laws segs B.

Definition g6_CEIL8 : Z := alloc_ceiling + 8.
Definition g6_app (a : Z) : Prop := 0 <= a < g6_CEIL8 /\ (a < kLowMemEnd \/ kHighMemBeg <= a).
Lemma g6_ceil_lo : 0x7fff7f800000 <= alloc_ceiling.
Proof. pose proof asan_consts as (C1 & _). lia. Qed.
(* the bytes the model, the input and the read-only image read *)
Definition g6_ib (ly : alayout) (S : astate) (a : Z) : Prop :=
  inG gn_cells a \/ (as_errno B <= a < as_errno B + 4) \/
  (exists b n, In (b, n) (ablocks B ly S) /\ b <= a < b + req_size n).
Definition g6_fp (ly : alayout) (S : astate) (fp : list (Z * Z)) : Prop :=
  forall r, In r fp -> forall a, fst r <= a < snd r -> g6_ib ly S a.
Lemma g6_fp_nil : forall ly S, g6_fp ly S [].
Proof. intros ly S r []. Qed.
Lemma g6_fp_cons : forall ly S r fp, (forall a, fst r <= a < snd r -> g6_ib ly S a) -> g6_fp ly S fp ->
  g6_fp ly S (r :: fp).
Proof. intros ly S r fp H1 H2 r' [<- | Hr] a Ha; [exact (H1 a Ha) | exact (H2 r' Hr a Ha)]. Qed.
Lemma g6_fp_app : forall ly S f1 f2, g6_fp ly S f1 -> g6_fp ly S f2 -> g6_fp ly S (f1 ++ f2).
Proof. intros ly S f1 f2 H1 H2 r Hr. apply in_app_or in Hr as [Hr|Hr]; [exact (H1 r Hr) | exact (H2 r Hr)]. Qed.
Lemma g6_akept : forall ly S (W W' : world segs) mem mem' fp,
  (forall a, g6_ib ly S a -> abyte_kept W mem W' mem' a) -> g6_fp ly S fp -> akept W mem W' mem' fp.
Proof. intros ly S W W' mem mem' fp HK Hf r Hr a Ha. exact (HK a (Hf r Hr a Ha)). Qed.
Ltac g6_inl := cbn [In gn_cells]; repeat (first [left; reflexivity | right]).
Lemma g6_ib_cell : forall ly S lo n lo' hi', In (lo, n) gn_cells -> lo <= lo' -> hi' <= lo + n ->
  forall a, lo' <= a < hi' -> g6_ib ly S a.
Proof.
  intros ly S lo n lo' hi' Hin H1 H2 a Ha. left. unfold inG. apply Exists_exists.
  exists (lo, n). split; [exact Hin | unfold in_zr; cbn [fst snd]; lia].
Qed.
Lemma g6_ib_blk : forall ly S b n lo hi, In (b, n) (ablocks B ly S) -> b <= lo -> hi <= b + req_size n ->
  forall a, lo <= a < hi -> g6_ib ly S a.
Proof. intros ly S b n lo hi Hin H1 H2 a Ha. right. right. exists b, n. split; [exact Hin | lia]. Qed.

(* a live block is wholly in low or wholly in high memory (AR_blocks_law's in_app) *)
Lemma g6_blk : forall ly S (W : world segs) mem md p n,
  AR segs B ly S W mem md -> In (p, n) (ablocks B ly S) ->
  4096 <= p /\ p + req_size n <= alloc_ceiling /\ 0 <= n <= req_size n /\
  (p + req_size n <= kLowMemEnd \/ kHighMemBeg <= p).
Proof.
  intros ly S W mem md p n HAR Hin.
  destruct (al_blocks _ _ LAWS ly S W mem md p n HAR Hin) as (_ & H1 & H2 & Happ & _ & _ & H3).
  pose proof (req_size_pos n ltac:(lia)) as [Hr1 Hr2].
  unfold in_app, kLowShadowBeg in Happ.
  split; [lia|]. split; [lia|]. split; [lia|]. unfold kLowMemEnd. lia.
Qed.
(* every byte g6_ib names is app memory below the ceiling, so apart from every shadow byte *)
Lemma g6_ib_app : forall ly S (W : world segs) mem md a,
  AR segs B ly S W mem md ->
  (forall x, inG gn_cells x -> 0 <= x < kLowMemEnd) ->
  0 <= as_errno B -> as_errno B + 4 <= kLowMemEnd ->
  g6_ib ly S a -> g6_app a.
Proof.
  intros ly S W mem md a HAR HC HE0 HE1 Hib. pose proof g6_ceil_lo as HCL.
  destruct Hib as [Hc | [He | (p & n & Hin & Hb)]];
    [pose proof (HC a Hc) | | destruct (g6_blk ly S W mem md p n HAR Hin) as (P1 & P2 & P3 & P4)];
    unfold g6_app, g6_CEIL8, kLowMemEnd, kHighMemBeg in *; lia.
Qed.

Lemma g6_bzs_len : forall l, Z.of_nat (length (bzs l)) = Z.of_nat (length l).
Proof. intros l. unfold bzs. rewrite length_map. reflexivity. Qed.
Lemma g6_text_rec_len : forall r, length (text_rec r) = 16%nat.
Proof. intros r. unfold text_rec. rewrite length_app. reflexivity. Qed.
Lemma g6_concat_len : forall rs, length (concat (map text_rec rs)) = (16 * length rs)%nat.
Proof.
  induction rs as [|r rs IH]; [reflexivity|].
  cbn [map concat]. rewrite length_app, g6_text_rec_len, IH. cbn [length]. lia.
Qed.
Lemma g6_key_ptrs_len : forall ks, length (gestures_end_b_c.key_ptrs ks) = (8 * length ks)%nat.
Proof.
  induction ks as [|k ks IH]; [reflexivity|].
  unfold gestures_end_b_c.key_ptrs in *. cbn [map concat]. rewrite length_app, IH, Mem.length_le8.
  cbn [length]. lia.
Qed.

(* ---- struct list ---- *)
Lemma g6_alist : forall ly S (W : world segs) mem md LA l lines,
  AR segs B ly S W mem md -> alist_at B ly S W mem LA l lines ->
  (forall a, LA <= a < LA + 16 -> g6_ib ly S a) ->
  g6_fp ly S (alist_fp LA l) /\ (forall b, In b (alist_blks l) -> In b (ablocks B ly S)).
Proof.
  intros ly S W mem md LA l lines HAR (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9) HLA.
  rewrite Forall_forall in H9.
  assert (HREC : g6_fp ly S (map (fun r => gfp (fst r) (bzs (snd r ++ [Z_to_bv 8 0]))) (hl_recs l))).
  { intros r Hr. apply in_map_iff in Hr as (x & <- & Hx). destruct (H9 x Hx) as (K1 & _).
    destruct (g6_blk ly S W mem md _ _ HAR K1) as (P1 & P2 & P3 & P4).
    apply (g6_ib_blk ly S _ _ _ _ K1); cbn [gfp fst snd]; [lia|].
    rewrite g6_bzs_len, length_app. cbn [length]. lia. }
  split.
  - unfold alist_fp. apply g6_fp_cons; [cbn [fst snd]; exact HLA|].
    apply g6_fp_app; [|exact HREC].
    destruct (Z.eqb_spec (hl_cap l) 0) as [Hc|Hc]; [apply g6_fp_nil|].
    destruct H6 as [[Hc0 _] | (Hcp & Hin & Hj & Hg)]; [lia|].
    destruct (g6_blk ly S W mem md _ _ HAR Hin) as (P1 & P2 & P3 & P4).
    apply g6_fp_cons; [|apply g6_fp_nil].
    apply (g6_ib_blk ly S _ _ _ _ Hin); cbn [gfp fst snd]; [lia|].
    rewrite g6_bzs_len, length_app, g6_concat_len. unfold hl_n in *. unfold AREC in *. lia.
  - intros b Hb. unfold alist_blks in Hb. apply in_app_or in Hb as [Hb | Hb].
    + destruct (Z.eqb_spec (hl_cap l) 0) as [Hc|Hc]; [destruct Hb|].
      destruct H6 as [[Hc0 _] | (Hcp & Hin & _)]; [lia|]. destruct Hb as [<- | []]. exact Hin.
    + apply in_map_iff in Hb as (x & <- & Hx). exact (proj1 (H9 x Hx)).
Qed.

(* ---- struct source ---- *)
Lemma g6_asrc : forall ly S (W : world segs) mem md HA h,
  AR segs B ly S W mem md -> asrc_at B ly S W mem HA h ->
  (forall a, HA <= a < HA + ASRC -> g6_ib ly S a) ->
  g6_fp ly S (asrc_fp HA h) /\ (forall b, In b (asrc_blks h) -> In b (ablocks B ly S)).
Proof.
  intros ly S W mem md HA h HAR HS HHA.
  pose proof HS as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Hpend & _ & _ & _ & _ & _ & _ & _ & Hpb & Hpj & _ &
                    _ & Hexp & Hheld & _).
  destruct (g6_alist ly S W mem md (HA + 16) (hs_pending h) false HAR Hpend
              ltac:(intros a Ha; apply HHA; unfold ASRC in *; lia)) as [A1 A2].
  destruct (g6_alist ly S W mem md (HA + 64) (hs_expected h) true HAR Hexp
              ltac:(intros a Ha; apply HHA; unfold ASRC in *; lia)) as [E1 E2].
  destruct (g6_alist ly S W mem md (HA + 80) (hs_held h) true HAR Hheld
              ltac:(intros a Ha; apply HHA; unfold ASRC in *; lia)) as [H1 H2].
  destruct (g6_blk ly S W mem md _ _ HAR Hpb) as (P1 & P2 & P3 & P4).
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
Lemma g6_aentry : forall ly S (W : world segs) mem md e,
  AR segs B ly S W mem md -> aentry_ok B ly S W mem e ->
  g6_fp ly S (aentry_fp e) /\ (forall b, In b (aentry_blks e) -> In b (ablocks B ly S)).
Proof.
  intros ly S W mem md e HAR (K1 & K2 & K3 & K4 & K5 & K6 & K7 & K8 & K9 & K10 & K11 & K12 & K13 & K14 & K15).
  rewrite Forall_forall in K15.
  assert (HK : g6_fp ly S (map (fun k => gfp (gestures_end_b_c.key_addr k)
                  (bzs (gestures_end_b_c.key_text k ++ [Z_to_bv 8 0]))) (re_keys e))).
  { intros r Hr. apply in_map_iff in Hr as (k & <- & Hk). destruct (K15 k Hk) as (M1 & _).
    destruct (g6_blk ly S W mem md _ _ HAR M1) as (P1 & P2 & P3 & P4).
    apply (g6_ib_blk ly S _ _ _ _ M1); cbn [gfp fst snd]; [lia|].
    rewrite g6_bzs_len, length_app. cbn [length]. lia. }
  unfold aentry_fp, aentry_blks. split.
  - apply g6_fp_app.
    + destruct (Z.eqb_spec (re_cap e) 0) as [Hc|Hc]; [apply g6_fp_nil|].
      destruct K10 as [(Hc0 & _) | (Hcp & Hin & Hj & Hg)]; [lia|].
      destruct (g6_blk ly S W mem md _ _ HAR Hin) as (P1 & P2 & P3 & P4).
      apply g6_fp_cons; [|apply g6_fp_nil].
      apply (g6_ib_blk ly S _ _ _ _ Hin); cbn [gfp fst snd]; [lia|].
      rewrite g6_bzs_len, length_app. lia.
    + apply g6_fp_cons; [|exact HK].
      destruct K12 as [(Hz & Hks) | (Hz & Hin & Hk1 & Hk2 & Hg)].
      * intros a Ha. cbn [gfp fst snd] in Ha. rewrite g6_bzs_len, g6_key_ptrs_len, Hks in Ha.
        cbn [length] in Ha. lia.
      * destruct (g6_blk ly S W mem md _ _ HAR Hin) as (P1 & P2 & P3 & P4).
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
Lemma g6_arelay : forall ly S (W : world segs) mem md G es,
  AR segs B ly S W mem md -> arelay_at B fr_RG ly S W mem G es ->
  g6_fp ly S (arelay_fp fr_RG G es) /\ (forall b, In b (arelay_blks G es) -> In b (ablocks B ly S)).
Proof.
  intros ly S W mem md G es HAR (R1 & R2 & R3 & R4 & R5 & R6 & R7 & R8 & R9 & R10 & R11).
  destruct (g6_blk ly S W mem md _ _ HAR R8) as (P1 & P2 & P3 & P4).
  rewrite Forall_forall in R10.
  assert (HF1 : g6_fp ly S (concat (map aentry_fp es))).
  { intros r Hr. apply in_concat in Hr as (f & Hf & Hr). apply in_map_iff in Hf as (e & <- & He).
    exact (proj1 (g6_aentry ly S W mem md e HAR (R10 e He)) r Hr). }
  assert (HF2 : forall b, In b (concat (map aentry_blks es)) -> In b (ablocks B ly S)).
  { intros b Hb. apply in_concat in Hb as (f & Hf & Hb). apply in_map_iff in Hf as (e & <- & He).
    exact (proj2 (g6_aentry ly S W mem md e HAR (R10 e He)) b Hb). }
  unfold arelay_fp, arelay_blks. split.
  - apply g6_fp_cons; [cbn [fst snd]; apply (g6_ib_cell ly S (rg_src fr_RG) 8); [g6_inl | lia | lia]|].
    apply g6_fp_cons; [cbn [fst snd]; apply (g6_ib_cell ly S (rg_nsrc fr_RG) 4); [g6_inl | lia | lia]|].
    apply g6_fp_cons; [cbn [fst snd]; apply (g6_ib_cell ly S (rg_capsrc fr_RG) 4); [g6_inl | lia | lia]|].
    apply g6_fp_cons; [|exact HF1].
    apply (g6_ib_blk ly S _ _ _ _ R8); cbn [fst snd]; lia.
  - intros b [<- | Hb]; [exact R8 | exact (HF2 b Hb)].
Qed.

(* ---- the controller's stream: eight cells, errno, and the g_out block ---- *)
Lemma g6_aout : forall ly S (W : world segs) mem md c O mx no cap out,
  AR segs B ly S W mem md -> aout_at B fr_RG ly S W mem c O mx no cap out ->
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
    destruct (g6_blk ly S W mem md _ _ HAR Hin) as (P1 & P2 & P3 & P4).
    apply g6_fp_cons; [|apply g6_fp_nil]. apply (g6_ib_blk ly S _ _ _ _ Hin); cbn [fst snd]; lia.
  - intros b Hb. destruct (Z.eqb_spec cap 0) as [Hc|Hc]; [destruct Hb|].
    destruct Hblk as [(Hc0 & _) | (Hcp & Hno & Hin & _)]; [lia|]. destruct Hb as [<- | []]. exact Hin.
Qed.

(* ---- the model ---- *)
Lemma g6_amodel_kept : forall ly S (W : world segs) mem md (W' : world segs) mem' m,
  AR segs B ly S W mem md -> amodel_at B ly S W mem m ->
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
    - destruct (g6_asrc ly S W mem md _ h HAR M2 HB) as [F1 F2].
      exact (asrc_at_kept B ly S W mem ly S W' mem' _ h M2 (g6_akept ly S W W' mem mem' _ KEEP F1) F2).
    - destruct M2 as [G1 G2]. split.
      + apply (akept_garr8 W mem); [|exact G1]. intros x Hx. rewrite repeat_length in Hx.
        apply KEEP. apply HB. unfold ASRC in *. lia.
      + apply (akept_awr W mem); [|exact G2]. intros x Hx. apply KEEP. apply HB. unfold ASRC in *. lia. }
  split.
  { destruct (g6_arelay ly S W mem md (lm_G m) (lm_es m) HAR M3) as [F1 F2].
    exact (arelay_at_kept B fr_RG ly S W mem ly S W' mem' _ _ M3 (g6_akept ly S W W' mem mem' _ KEEP F1) F2). }
  split.
  { destruct (g6_aout ly S W mem md _ _ _ _ _ _ HAR M4) as [F1 F2].
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
Lemma g6_sv8_kept : forall (W W' : world segs) mem mem' a v,
  (forall x, a <= x < a + 8 -> abyte_kept W mem W' mem' x) -> sv8 W mem a v -> sv8 W' mem' a v.
Proof.
  intros W W' mem mem' a v HK Hv. unfold sv8 in *. apply (akept_vm W mem); [|exact Hv].
  intros x Hx. apply HK. cbn in Hx. lia.
Qed.
(* writability survives a step that keeps presence and hides no more (p4's gp4k_wr_kept, from W_list_drop.v
   writable_kept_w) *)
Lemma g6_wr_kept : forall (W W' : world segs) (m m' : word -> option byte) a,
  (apresent (w_H W) m a -> apresent (w_H W') m' a) -> wle W W' ->
  writable_at segs (mrestrict (w_H W) m) a -> writable_at segs (mrestrict (w_H W') m') a.
Proof.
  intros W W' m m' a Hp Hh Hw. unfold writable_at, wview, mrestrict in Hw |- *.
  destruct (w_H W' (Z_to_bv 64 a)) eqn:EH'.
  - rewrite (Hh _ EH') in Hw. exact Hw.
  - destruct (w_H W (Z_to_bv 64 a)) eqn:EH.
    + destruct (m' (Z_to_bv 64 a)); [discriminate | exact Hw].
    + destruct (m (Z_to_bv 64 a)) as [b|] eqn:Em.
      * destruct (Hp (conj EH (ex_intro _ b Em))) as [_ [b2 Hb2]]. rewrite Hb2. discriminate.
      * destruct (m' (Z_to_bv 64 a)); [discriminate | exact Hw].
Qed.
(* ---- the input block ---- *)
Lemma g6_ainput_kept : forall cx ly S (W : world segs) mem md (W' : world segs) mem',
  AR segs B ly S W mem md -> ainput_at B cx ly S W mem ->
  Z.of_nat (length (c_pl cx)) = c_n cx ->
  (forall a, g6_ib ly S a -> abyte_kept W mem W' mem' a) ->
  ainput_at B cx ly S W' mem'.
Proof.
  intros cx ly S W mem md W' mem' HAR (I1 & I2) Hlen KEEP.
  split; [exact I1|]. apply (akept_garr8 W mem); [|exact I2].
  intros x Hx. rewrite length_map in Hx. rewrite Hlen in Hx.
  destruct I1 as [(Hn & Hp) | (Hn & Hin)]; [lia|].
  destruct (g6_blk ly S W mem md _ _ HAR Hin) as (P1 & P2 & P3 & P4).
  apply KEEP. right. right. exists (c_p cx), (c_n cx). split; [exact Hin | lia].
Qed.
(* ---- the jump table: read-only, so the two rom_views decide it (p3's gp3_jt_kept, copied) ---- *)
Lemma g6_mbyte_of_view : forall (W W' : world segs) mem mem' a,
  aview segs (w_H W') mem' a = aview segs (w_H W) mem a ->
  mbyte segs (arm W' mem') a = mbyte segs (arm W mem) a.
Proof.
  intros W W' mem mem' a H. unfold aview, arm in *.
  destruct (mbyte segs (mrestrict (w_H W') mem') a) as [b1|] eqn:E1;
    destruct (mbyte segs (mrestrict (w_H W) mem) a) as [b2|] eqn:E2; cbn [option_map] in H;
    try discriminate; [|reflexivity].
  injection H as H. f_equal. apply bv_eq. exact H.
Qed.
Lemma g6_vm_of_view : forall (W W' : world segs) mem mem' a n v,
  (forall x, a <= x < a + Z.of_nat n -> aview segs (w_H W') mem' x = aview segs (w_H W) mem x) ->
  val_mem segs (arm W mem) a n v -> val_mem segs (arm W' mem') a n v.
Proof.
  intros W W' mem mem' a n v Hav Hv k Hk.
  rewrite (g6_mbyte_of_view W W' mem mem' (a + Z.of_nat k) (Hav (a + Z.of_nat k) ltac:(lia))).
  exact (Hv k Hk).
Qed.
Definition g6_inromb (a : Z) : bool :=
  existsb (fun sg => (negb (seg_writable sg) && (Z.of_N (seg_base sg) <=? a) &&
                      (a <? Z.of_N (seg_base sg) + Z.of_N (seg_size sg)))%bool) segs.
Lemma g6_inromb_ok : forall a, g6_inromb a = true -> in_rom segs a.
Proof.
  intros a H. unfold g6_inromb in H. apply existsb_exists in H as (sg & Hs & Hb).
  apply andb_prop in Hb as [Hb H2]. apply andb_prop in Hb as [H0 H1].
  apply negb_true_iff in H0. apply Z.leb_le in H1. apply Z.ltb_lt in H2.
  exists sg. split; [exact Hs|]. split; [exact H0 | lia].
Qed.
Lemma g6_jt_in_rom : forall a, fr_jtab <= a < fr_jtab + 36 -> in_rom segs a.
Proof.
  intros a Ha. apply g6_inromb_ok.
  assert (K : forallb (fun i => g6_inromb (fr_jtab + Z.of_nat i)) (seq 0 36) = true)
    by (vm_compute; reflexivity).
  rewrite forallb_forall in K. replace a with (fr_jtab + Z.of_nat (Z.to_nat (a - fr_jtab))) by lia.
  apply K. apply in_seq. lia.
Qed.
Lemma g6_jt_kept : forall (W W' : world segs) mem mem',
  rom_view segs W mem -> rom_view segs W' mem' -> jt_rom W mem -> jt_rom W' mem'.
Proof.
  intros W W' mem mem' HR HR' HJ i Hi.
  apply (g6_vm_of_view W W' mem mem'); [|exact (HJ i Hi)].
  intros x Hx. assert (Hrx : in_rom segs x) by (apply g6_jt_in_rom; cbn in Hx; lia).
  rewrite (HR' x Hrx), (HR x Hrx). reflexivity.
Qed.

(* ---- the frame, across the call and the re-poison ---- *)
(* the fake frame's shadow: bytes 4..9 (prefix[48]) now 0xf8, the other ten kept *)
Lemma g6_shadow_close : forall (W W' : world segs) mem mem' a,
  garr8 segs (arm W mem) a fake_shadow_open ->
  (forall i, 0 <= i < 16 -> ~ (4 <= i < 10) -> abyte_kept W mem W' mem' (a + i)) ->
  (forall i, 4 <= i < 10 -> mbyte segs (arm W' mem') (a + i) = Some (Z_to_bv 8 248)) ->
  garr8 segs (arm W' mem') a fake_shadow.
Proof.
  intros W W' mem mem' a HGa HK HN j Hj. cbn [length fake_shadow] in Hj.
  assert (Hc : (4 <= j < 10)%nat \/ ~ (4 <= j < 10)%nat) by lia.
  destruct Hc as [Hc | Hc].
  - assert (Ev : nth j fake_shadow 0 = 248).
    { unfold fake_shadow. do 10 (destruct j as [|j]; [cbn [nth]; first [reflexivity | lia] |]). lia. }
    rewrite Ev. split; [|lia].
    intros k Hk. assert (Ek : k = 0%nat) by lia. subst k. cbn [Z.of_nat]. rewrite Z.add_0_r.
    rewrite (HN (Z.of_nat j) ltac:(lia)). vm_compute. reflexivity.
  - assert (Ev : nth j fake_shadow 0 = nth j fake_shadow_open 0).
    { unfold fake_shadow, fake_shadow_open.
      do 16 (destruct j as [|j]; [cbn [nth]; first [reflexivity | lia] |]). lia. }
    destruct (HGa j ltac:(cbn [length fake_shadow_open]; lia)) as [Hv Hr].
    rewrite Ev. split; [|exact Hr].
    apply (akept_vm W mem W' mem'); [|exact Hv]. intros x Hx.
    replace x with (a + Z.of_nat j) by lia. apply HK; lia.
Qed.
(* the three groups of bytes the frame reads, each kept by its own clause of W3's post: the stack at or above
   lf_F cx (the journal's high-memory clause), the fake frame of class 1 and its shadow (the frame clause) *)
Lemma g6_gframe_carry : forall cx FF (W W' : world segs) mem mem',
  gframe cx fake_shadow_open FF W mem ->
  (forall a, lf_F cx <= a < 2 ^ 64 -> abyte_kept W mem W' mem' a) ->
  (forall a, FF <= a < FF + 128 -> abyte_kept W mem W' mem' a) ->
  (forall i, 0 <= i < 16 -> ~ (4 <= i < 10) -> abyte_kept W mem W' mem' (SB + FF / 8 + i)) ->
  (forall i, 4 <= i < 10 -> mbyte segs (arm W' mem') (SB + FF / 8 + i) = Some (Z_to_bv 8 248) /\
     writable_at segs (arm W' mem') (SB + FF / 8 + i)) ->
  lf_F cx + 320 <= spZ (c_regs cx) -> spZ (c_regs cx) <= 2 ^ 47 ->
  gframe cx fake_shadow FF W' mem'.
Proof.
  intros cx FF W W' mem mem' (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11 & B1 & B2 & B3 & B4 & B5 & B6 & B7 &
    H13 & H14 & H15 & H16 & H17 & H18) KH KF KS HN HF1 HF2.
  split.
  { intros o r Hin. apply (g6_sv8_kept W W' mem mem'); [|exact (H1 o r Hin)].
    intros x Hx. apply KH.
    assert (Ho : 8 <= o <= 104).
    { cbn in Hin. repeat (destruct Hin as [E | Hin]; [inversion E; lia|]). destruct Hin. }
    lia. }
  split.
  { apply (akept_awr W mem); [|exact H2]. intros x Hx. apply KH. lia. }
  split; [apply (g6_sv8_kept W W' mem mem'); [intros x Hx; apply KH; lia | exact H3]|].
  split; [apply (g6_sv8_kept W W' mem mem'); [intros x Hx; apply KH; lia | exact H4]|].
  split; [apply (g6_sv8_kept W W' mem mem'); [intros x Hx; apply KH; lia | exact H5]|].
  split; [apply (g6_sv8_kept W W' mem mem'); [intros x Hx; apply KH; lia | exact H6]|].
  split; [apply (g6_sv8_kept W W' mem mem'); [intros x Hx; apply KH; lia | exact H7]|].
  split; [apply (g6_sv8_kept W W' mem mem'); [intros x Hx; apply KH; lia | exact H8]|].
  split; [apply (g6_sv8_kept W W' mem mem'); [intros x Hx; apply KH; lia | exact H9]|].
  split; [apply (g6_sv8_kept W W' mem mem'); [intros x Hx; apply KH; lia | exact H10]|].
  split; [apply (g6_sv8_kept W W' mem mem'); [intros x Hx; apply KH; lia | exact H11]|].
  split; [apply (g6_sv8_kept W W' mem mem'); [intros x Hx; apply KH; lia | exact B1]|].
  split; [apply (g6_sv8_kept W W' mem mem'); [intros x Hx; apply KH; lia | exact B2]|].
  split; [apply (g6_sv8_kept W W' mem mem'); [intros x Hx; apply KH; lia | exact B3]|].
  split; [apply (g6_sv8_kept W W' mem mem'); [intros x Hx; apply KH; lia | exact B4]|].
  split; [apply (g6_sv8_kept W W' mem mem'); [intros x Hx; apply KH; lia | exact B5]|].
  split; [apply (g6_sv8_kept W W' mem mem'); [intros x Hx; apply KH; lia | exact B6]|].
  split; [apply (g6_sv8_kept W W' mem mem'); [intros x Hx; apply KH; lia | exact B7]|].
  split; [apply (g6_sv8_kept W W' mem mem'); [intros x Hx; apply KF; lia | exact H13]|].
  split; [apply (g6_sv8_kept W W' mem mem'); [intros x Hx; apply KF; lia | exact H14]|].
  split; [apply (g6_sv8_kept W W' mem mem'); [intros x Hx; apply KF; lia | exact H15]|].
  split; [apply (akept_awr W mem); [intros x Hx; apply KF; lia | exact H16]|].
  split.
  { exact (g6_shadow_close W W' mem mem' (SB + FF / 8) H17 KS (fun i Hi => proj1 (HN i Hi))). }
  intros i Hi.
  destruct (Z_lt_le_dec i 4) as [Hl | Hl]; [exact (proj2 (KS i ltac:(lia) ltac:(lia)) (H18 i Hi))|].
  destruct (Z_lt_le_dec i 10) as [Hl2 | Hl2]; [exact (proj2 (HN i ltac:(lia)))|].
  exact (proj2 (KS i ltac:(lia) ltac:(lia)) (H18 i Hi)).
Qed.
End g6k.

(* ================================================================== the phase *)
Section gp6.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
#[local] Notation segs := (@pa_segs _ fr_prog_listing PB_fr).
Variable B : asyms.
Variable MT : ameter_ops.
Variables XM_LIB : Z -> Z.
Variables RLO RHI : Z.
Variable fr_live_pre : astate -> Prop.
Variable G_fr : list (Z * Z).
Variable fr_FP : bvmap 5 word -> alayout -> astate -> world segs -> (word -> option byte) -> list (Z * Z).
Hypothesis LAWS : AR_laws segs B.
Hypothesis HG : gx_ok segs B G_fr.
Variable LS : lfcx -> Z -> lmod -> alayout -> astate -> Prop.
Variable RINV : lfcx -> Z -> lmod -> Prop.
(* the allocator instance (W_kit.v): its api_env (pal_env) puts errno's 4 bytes below kLowMemEnd *)
Hypothesis TL : PALib B.
#[local] Notation VAL := (@pa_val _ fr_prog_listing PB_fr).
#[local] Notation BASE := (@pa_val _ fr_prog_listing PB_fr A_TEXT).
(* check_shape_done (0x85734): W_contract.v csd_spec (:130) on the W8 lane head a3c72093c22, verbatim (lf_arm_gone's
   CSD; _remove.v:403 takes the same text) *)
Hypothesis CSD : csd_spec B (BASE + AF_fr_check_shape_done).
(* what carries the model and the read-only image across that call (base GN_HGcells / GN_ROM_PIN, as p4 / p5 take
   them): the model's cells are bytes of G_fr, so image bytes that are no allocator static, which the callee's journal
   keeps (Reusable/YCbq.v:363); and the allocator's own read-only bytes are pinned in every AR state *)
Hypothesis HGCELLS : GN_HGcells G_fr.
Hypothesis HROMPIN : GN_ROM_PIN B.
(* the bytes check_shape_done's post keeps at its call sp = F (aleaf_post: the donor journal's view clauses,
   Reusable/YCbq.v:358-366, and errno's view), p4's gp4_kcls: the stack from alloc_ceiling up but the callee's
   16-byte frame below F, every live block, the image bytes that are no allocator static, errno, and every frame of
   S with its shadow *)
Definition g6_kcls (cx : lfcx) (ly : alayout) (S : astate) (a : Z) : Prop :=
  (alloc_ceiling <= a < 2 ^ 64 /\ ~ (lf_F cx - 16 <= a < lf_F cx)) \/
  (exists p n, In (p, n) (ablocks B ly S) /\ p <= a < p + req_size n) \/
  (in_img segs a /\ ~ Exists (in_zr a) (as_owned_static B)) \/
  (as_errno B <= a < as_errno B + 4) \/
  (exists cid pos, In (cid, pos) (frames S) /\
     (in_zr a (frame_rng ly (cid, pos)) \/ in_zr a (shadow_addr (frame_addr ly cid pos), fs_frame_bytes cid / 8))).

(* check_shape_done's afn_pre at sp = F: W_LLVMFuzzerTestOneInput_latch.v's lt_afn_pre_at, which reads only the
   saved ra / s0 of aframe_at (gframe's first conjunct is the same) *)
Lemma g6_afn_pre_at : forall cx ly3 S3 fpos k (W : world segs) mem md regs STK1,
  lf_base B MT XM_LIB RLO RHI fr_live_pre G_fr cx ->
  ajournal_gx segs B G_fr 0 [] LLVMF_STK (spZ (c_regs cx)) (lf_FP fr_FP cx)
    (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx) [(1, fpos)] ly3 S3 W mem md k ->
  (forall o r, In (o, r) saved_regs ->
     sv8 W mem (spZ (c_regs cx) - o) (bv_unsigned (getr (c_regs cx) (Z_to_bv 5 r)))) ->
  spZ regs = lf_F cx -> YK0s.ret_ok (getr regs 1) -> 4096 <= raZ regs ->
  getr regs 3 = w64 (as_gp B) -> getr regs 4 = w64 (as_tp B) -> getr regs 8 = getr (c_regs cx) 2 ->
  0 <= STK1 -> STK1 + 352 <= LLVMF_STK ->
  exists ch, afn_pre segs B STK1 ly3 S3 W regs mem md ch.
Proof.
  intros cx ly3 S3 fpos k W mem md regs STK1 HB HJ HSV Hsp Hret Hra4 Hgp Htp Hs0 HSTK0 HSTKb.
  destruct HB as (_ & HPRE).
  assert (HPREE : afn_pre segs B LLVMF_STK (c_ly cx) (c_S cx) (c_W cx) (c_regs cx) (c_mem cx) (c_md cx) [])
    by (unfold fr_lib_pre_cf in HPRE; tauto).
  pose proof HPREE as (HAR0 & Hra0 & Hra40 & Hgp0 & Htp0 & Hstk0 & Hpres0 & Hch0 & HQT0).
  pose proof Hstk0 as (Hal16 & Hslo0 & Hceil0 & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
  destruct (ajournal_gx_inner segs B G_fr 0 [] LLVMF_STK (spZ (c_regs cx)) (lf_FP fr_FP cx)
    (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx) [(1, fpos)] ly3 S3 W mem md k HJ) as (memS & HJ0 & Hmg).
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
  - pose proof (aview_above_of_journal (PI := PB_fr) B LLVMF_STK sp0 (lf_FP fr_FP cx)
      (c_ly cx) (c_S cx) (c_W cx) memS (c_md cx) [(1, fpos)] ly3 S3 W mem md k HJ0) as HAB.
    assert (Hra8 : rdword (aview segs (w_H W) mem) (sp0 - 8) = Some (bv_unsigned (getr (c_regs cx) 1))).
    { apply (rdword_of_val_mem segs (w_H W) mem); [exact (HSV 8 1 ltac:(left; reflexivity)) |].
      pose proof (bv_unsigned_in_range 64 (getr (c_regs cx) 1)) as Hr.
      change (bv_modulus 64) with (2 ^ 64) in Hr. lia. }
    assert (Hs016 : rdword (aview segs (w_H W) mem) (sp0 - 16) = Some (bv_unsigned (getr (c_regs cx) 8))).
    { apply (rdword_of_val_mem segs (w_H W) mem); [exact (HSV 16 8 ltac:(right; left; reflexivity)) |].
      pose proof (bv_unsigned_in_range 64 (getr (c_regs cx) 8)) as Hr.
      change (bv_modulus 64) with (2 ^ 64) in Hr. lia. }
    exists ((sp0, bv_unsigned (getr (c_regs cx) 1), bv_unsigned (getr (c_regs cx) 8)) :: []).
    eapply (afn_pre_at segs B LLVMF_STK sp0 (lf_FP fr_FP cx) (c_ly cx) (c_S cx) (c_W cx) memS (c_md cx)
      [(1, fpos)] ly3 S3 W mem md k regs STK1 (lf_F cx - sp0) _ HJ0);
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
    eapply (afn_pre_at segs B LLVMF_STK sp0 (lf_FP fr_FP cx) (c_ly cx) (c_S cx) (c_W cx) memS (c_md cx)
      [(1, fpos)] ly3 S3 W mem md k regs STK1 (lf_F cx - sp0) _ HJ0);
      [ rewrite Hsp; lia | exact Ho16 | exact HoNeg | exact HSTK0 | exact HoBud | exact Hret | exact Hra4
      | exact Hgp | exact Htp | ].
    rewrite Hs0Z. left. split; [right; left; rewrite HTOPeq; exact Hge | reflexivity].
Qed.

(* a callee-saved register across the call (the latch's lt_pres) *)
Lemma g6_pres : forall regs regs' (r : bv 5), aregs_preserved regs regs' -> acallee_saved (bv_unsigned r) ->
  getr regs' r = getr regs r.
Proof. intros regs regs' r HP Hr. pose proof (HP _ Hr) as H. rewrite !Z_to_bv_bv_unsigned in H. exact H. Qed.
Ltac g6_cs := unfold acallee_saved;
  match goal with |- context [bv_unsigned ?r] => let v := eval vm_compute in (bv_unsigned r) in
    change (bv_unsigned r) with v end; lia.
(* the registers the cut point names that neither run writes and the call keeps *)
Definition g6_saved : list (bv 5) := [2; 3; 4; 8; 9; 18; 19; 23; 26; 27]%bv.

(* 0x8494c: `ld a0,208(s1)` reads at out of the frame cell F+208 *)
Definition g6_atR : YP09.region :=
  YP09.mkRegion (Some 9%nat) 208 216 0 0 [YP09.mkChunk 208 (CVal 8 (SOff 32 0))].
Definition g6_facts1 : facts :=
  mkFacts [ (2%nat, mkAF (2^46) (2^47) 5); (9%nat, mkAF (2^46) (2^47) 5); (32%nat, mkAF 0 (2 ^ 64 - 1) 0) ] [] [].
Definition ss_g6a : sstate := mkSS AF_gn_csd sr_atoms [g6_atR] None g6_facts1.
Definition g6_extra1 (A : Z) : list word := map (Z_to_bv 64) [A].
Lemma g6_entry1 : forall (W : world segs) regs mem (F A : Z),
  2 ^ 46 <= F -> F + 320 <= 2 ^ 47 -> F mod 32 = 0 ->
  getr regs 2 = w64 F -> getr regs 9 = w64 F ->
  sv8 W mem (F + 208) A -> 0 <= A < 2 ^ 64 ->
  st_ok_pi segs VAL (Eimg (Ereg regs (g6_extra1 A))) ss_g6a
    (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + AF_gn_csd)) mem (seg_rom segs))).
Proof.
  intros W regs mem F A HFlo HFhi HF32 R2 R9 Mat HA.
  pose proof pa_B_ok as HBASE.
  rewrite restrict_mkst_fx.
  set (E := Eimg (Ereg regs (g6_extra1 A))).
  assert (E2 : ew E 2 = getr regs 2) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
  assert (E9 : ew E 9 = getr regs 9) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 9 9%bv eq_refl)).
  assert (E32 : ew E 32 = Z_to_bv 64 A) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
  assert (Usp : bv_unsigned (ew E 2) = F) by (rewrite E2, R2; apply unsigned_lit_small; lia).
  assert (U9 : bv_unsigned (ew E 9) = F) by (rewrite E9, R9; apply unsigned_lit_small; lia).
  unfold ss_g6a. apply pa_entry_st_ok_full.
  - apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - constructor; [|constructor]. unfold region_ok, g6_atR.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite U9. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val segs E _ F 208 8 (SOff 32 0) A);
      [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | exact Mat].
  - cbn [pairwise_disjoint all_disjoint]. repeat split.
  - split; [|split; [exact I | exact I]].
    cbn [g6_facts1 f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite Usp, U9, E32, unsigned_lit_small by lia.
    change (2 ^ 5) with 32. rewrite !Z.pow_0_r, !Z.mod_1_r.
    repeat match goal with |- _ /\ _ => split end; lia.
Qed.

(* 0x84954, back from check_shape_done: s8 = F+96 (the fake frame's shadow), s9 = F+104, s6 = F+40 (in.p); the
   six stores `sb a0,4..9(s8)` write the shadow region's window [4, 10) *)
Definition AF_g6_ret : Z := 0x2668.
Definition g6_frR : YP09.region :=
  YP09.mkRegion (Some 9%nat) 40 112 0 0
    [YP09.mkChunk 40 (CVal 8 (SOff 32 0)); YP09.mkChunk 96 (CVal 8 (SOff 33 0));
     YP09.mkChunk 104 (CVal 8 (SLit HI_G_NOUT))].
Definition g6_shR : YP09.region := YP09.mkRegion (Some 33%nat) 4 10 4 10 [].
Definition g6_facts2 : facts :=
  mkFacts [ (9%nat, mkAF (2^46) (2^47) 5); (32%nat, mkAF 0 (2 ^ 64 - 1) 0);
            (33%nat, mkAF SB (SB + 2 ^ 44) 0) ] [] [].
Definition ss_g6b : sstate := mkSS AF_g6_ret sr_atoms [g6_frR; g6_shR] None g6_facts2.
Definition g6_extra2 (P SH : Z) : list word := map (Z_to_bv 64) [P; SH].
Lemma g6_entry2 : forall (W : world segs) regs mem (F P FF : Z),
  2 ^ 46 <= F -> F + 320 <= 2 ^ 47 -> F mod 32 = 0 -> getr regs 9 = w64 F ->
  0 <= FF -> FF + 128 <= 2 ^ 47 -> 0 <= P < 2 ^ 64 ->
  sv8 W mem (F + 40) P -> sv8 W mem (F + 96) (SB + FF / 8) -> sv8 W mem (F + 104) HI_G_NOUT ->
  awr W mem (SB + FF / 8) 16 ->
  st_ok_pi segs VAL (Eimg (Ereg regs (g6_extra2 P (SB + FF / 8)))) ss_g6b
    (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + AF_g6_ret)) mem (seg_rom segs))).
Proof.
  intros W regs mem F P FF HFlo HFhi HF32 R9 HFF0 HFF1 HP M40 M96 M104 AW.
  pose proof pa_B_ok as HBASE.
  assert (HF8 : 0 <= FF / 8 /\ FF / 8 + 16 <= 2 ^ 44) by (split; [apply Z.div_pos; lia | lia]).
  rewrite restrict_mkst_fx.
  set (E := Eimg (Ereg regs (g6_extra2 P (SB + FF / 8)))).
  assert (E9 : ew E 9 = getr regs 9) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 9 9%bv eq_refl)).
  assert (E32 : ew E 32 = Z_to_bv 64 P) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
  assert (E33 : ew E 33 = Z_to_bv 64 (SB + FF / 8))
    by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
  assert (U9 : bv_unsigned (ew E 9) = F) by (rewrite E9, R9; apply unsigned_lit_small; lia).
  assert (U32 : bv_unsigned (ew E 32) = P) by (rewrite E32; apply unsigned_lit_small; lia).
  assert (U33 : bv_unsigned (ew E 33) = SB + FF / 8) by (rewrite E33; apply unsigned_lit_small; unfold SB; lia).
  unfold ss_g6b. apply pa_entry_st_ok_full.
  - apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - constructor; [|constructor; [|constructor]].
    + unfold region_ok, g6_frR.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      rewrite U9. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor; [|constructor; [|constructor]]].
      * apply (chunk_ok_val segs E _ F 40 8 (SOff 32 0) P);
          [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | exact M40].
      * apply (chunk_ok_val segs E _ F 96 8 (SOff 33 0) (SB + FF / 8));
          [cbn [sv_denot]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | unfold SB; zside | zside
          | exact M96].
      * apply (chunk_ok_val segs E _ F 104 8 (SLit HI_G_NOUT) HI_G_NOUT);
          [reflexivity | unfold HI_G_NOUT; zside | zside | exact M104].
    + unfold region_ok, g6_shR.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      rewrite U33. split; [unfold SB; lia|]. split; [unfold SB; lia|].
      split; [intros o Ho; exact (AW o ltac:(lia)) | constructor].
  - apply pairwise_disjoint_of_extents. unfold g6_frR, g6_shR, extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite U9, U33.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. unfold SB. repeat split; lia.
  - split; [|split; [exact I | exact I]].
    cbn [g6_facts2 f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite U9, U32, U33.
    change (2 ^ 5) with 32. rewrite !Z.pow_0_r, !Z.mod_1_r. unfold SB.
    repeat match goal with |- _ /\ _ => split end; lia.
Qed.

Theorem gp6_csd_latch : forall cx t m mc W c,
  lf_base B MT XM_LIB RLO RHI fr_live_pre G_fr cx -> GCSD B G_fr fr_FP LS RINV cx t m mc W c ->
  SRr segs W c (INV_K B G_fr fr_FP LS RINV cx t).
Proof.
  intros cx t m mc W c HB HC.
  pose (RUNTOP := SRr_run_to_pi_AJX0 (PL := PL_fr) (PI := PB_fr) B LAWS G_fr).
  destruct HC as (regs & mem & md & ly & S & kk & fpos & -> & ((HJ & HGF & S40 & S144 & HIN & HRV & HJT & HFL) & HMOD & HSEP) &
    HLS & HRI & Hk & Hkq & Ht & S208 & AW192 & R2 & R8 & R9 & R18 & R19 & R23 & R26 & R3 & R4 & R27).
  pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  pose proof (gn_nums B MT XM_LIB RLO RHI fr_live_pre G_fr fr_FP LAWS cx [(1, fpos)] ly S W mem md kk fpos HB HJ eq_refl)
    as NUMS.
  cbv zeta in NUMS.
  destruct NUMS as (Hsp16 & Hsp0 & HF32 & HFb & HFF4 & HFFc & HFFapp & Hfrs & HAR).
  pose proof HB as (HAI0 & HPRE0).
  assert (HlenP : c_n cx = Z.of_nat (length (c_pl cx))) by (unfold fr_lib_pre_cf in HPRE0; tauto).
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
    destruct (g6_blk B LAWS ly S W mem md _ _ HAR Hin) as (P1 & P2 & P3 & P4). lia. }
  assert (Mno' : val_mem segs (mrestrict (w_H W) mem) (VAL A_g_nout) 8 (Z.of_nat (length (lm_O mc)))).
  { replace (VAL A_g_nout) with (rg_nout fr_RG) by (vm_compute; reflexivity). exact Mno. }
  (* in.p = c_p + kq, the value s6 reloads *)
  assert (HP : 0 <= c_p cx + gn_kq cx m < 2 ^ 64).
  { pose proof HIN as ([(Hn0 & Hp0) | (Hn0 & Hin)] & _).
    - rewrite Hp0. unfold A_EMPTY. lia.
    - destruct (g6_blk B LAWS ly S W mem md _ _ HAR Hin) as (P1 & P2 & P3 & P4). lia. }
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
  paj_run_to_shx RUNTOP HS HJ AF_fr_check_shape_done.
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
  destruct (g6_afn_pre_at cx ly S fpos kk W mem mdc (ms_regs ms1) CSD_STK HB HJ HSV Hsp1) as (ch & HPREc).
  { rewrite Q1. apply ret_ok_codeptr_v; [lia | reflexivity]. }
  { unfold raZ. rewrite Q1, unsigned_lit_small by lia. lia. }
  { rewrite (KR1 3%bv ltac:(cbv; tauto)). exact R3. }
  { rewrite (KR1 4%bv ltac:(cbv; tauto)). exact R4. }
  { rewrite (KR1 8%bv ltac:(cbv; tauto)). exact R8. }
  { unfold CSD_STK. lia. }
  { unfold CSD_STK, LLVMF_STK. lia. }
  eapply SRr_bind.
  { exact (CSD W ly S (ms_regs ms1) mem mdc ch (Z.of_nat (length (lm_O mc))) HPREc Q10 Hn Mno'). }
  intros W2 c2 Hwle2 (regs2 & mem2 & md2 & -> & HJc & HP2 & _ & HPR2 & HEV).
  rewrite Hsp1 in HJc.
  pose proof HJc as (_ & _ & _ & _ & _ & _ & _ & _ & JH & JB & JI & JF & _).
  (* check_shape_done's journal inside this function's: W2's ajournal_gx_sub at G_fr, lifted from the donor's journal
     (G = []), as p4 does for check_no_loss_read *)
  assert (HJc0 : ajournal_gx segs B [] 0 [] CSD_STK (lf_F cx) [] ly S W mem mdc [] ly S W2 mem2 md2 0)
    by (apply ajournal_gx_nil; exact HJc).
  assert (HJc' : ajournal_gx segs B G_fr 0 [] CSD_STK (lf_F cx) [] ly S W mem mdc [] ly S W2 mem2 md2 0).
  { refine (ajournal_gx_G_mono segs B [] G_fr 0 [] CSD_STK (lf_F cx) [] ly S W mem mdc [] ly S W2 mem2 md2 0 _ HJc0).
    intros a Ha. exfalso. exact (inG_nil a Ha). }
  pose proof (ajournal_gx_sub segs B LAWS pa_segs_low G_fr LLVMF_STK (spZ (c_regs cx)) 0 [] (lf_FP fr_FP cx)
     (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx) [(1, fpos)] ly S W mem mdc kk
     CSD_STK (lf_F cx) 0 [] [] [] ly S W2 mem2 md2 0 HJ HJc'
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
      + apply JI; [exact Ki | exact Ko | lia | apply fp_spares_closed; exact sink_closed_nil].
      + apply JI; [exact Ki | exact Ko | lia | apply fp_spares_closed; exact sink_closed_nil].
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
  paj_run_to_shx RUNTOP HS2 HJ2 AF_LLVM_latch.
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
  { intros a Hib. pose proof (g6_ib_app B LAWS ly S W mem md a HAR HC HE0 HE1 Hib) as (Ha1 & Ha2).
    apply KALL; [unfold g6_CEIL8 in Ha1; lia | | unfold g6_CEIL8, SB, kLowMemEnd, kHighMemBeg in *; lia].
    destruct Hib as [Hc | [He | (pb & nb & Hin & Hr)]].
    - right; right; left. exact (conj (proj1 (HG a (HGCELLS a Hc))) (proj1 (proj2 (HG a (HGCELLS a Hc))))).
    - right; right; right; left. exact He.
    - right; left. exists pb, nb. split; [exact Hin | exact Hr]. }
  (* the read-only image: the allocator's own bytes pinned in both states, the others kept by the call's image
     clause (p4's ROMK) *)
  pose proof (ajournal_gx_AR segs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ2) as HAR2.
  assert (ROMK : forall a, in_rom segs a -> aview segs (w_H W2) (ms_mem ms) a = aview segs (w_H W) mem a).
  { intros a Ha.
    assert (Him : in_img segs a) by (destruct Ha as (sg & Hs & _ & Hr); exists sg; split; [exact Hs | exact Hr]).
    destruct (Exists_dec (in_zr a) (as_owned_static B)) as [Ho|Ho].
    { intros r. unfold in_zr. destruct (Z_le_dec (fst r) a); destruct (Z_lt_dec a (fst r + snd r));
        [left; lia | right; lia | right; lia | right; lia]. }
    - pose proof (HROMPIN a Ha Ho) as Hp.
      rewrite (rom_pinned_view segs B ly S W2 (ms_mem ms) _ a HAR2 Hp), (rom_pinned_view segs B ly S W mem md a HAR Hp).
      reflexivity.
    - pose proof (pa_segs_low a Him) as HL.
      refine (proj1 (KALL a _ _ _)); [unfold kLowMemEnd in HL; lia | right; right; left; exact (conj Him Ho) |].
      unfold SB, kLowMemEnd in *. lia. }
  (* the cut's facts at the latch *)
  assert (HGF2 : gframe cx fake_shadow (frame_addr ly 1 fpos) W2 (ms_mem ms))
    by exact (g6_gframe_carry cx (frame_addr ly 1 fpos) W W2 mem (ms_mem ms) HGF KH KF KS NEW
                ltac:(lia) ltac:(lia)).
  pose proof (aframe_of_gframe cx (frame_addr ly 1 fpos) W2 (ms_mem ms) HGF2) as HFR2.
  pose proof (g6_amodel_kept B LAWS ly S W mem md W2 (ms_mem ms) mc HAR HMOD KIB) as HMOD2.
  pose proof (g6_ainput_kept B LAWS cx ly S W mem md W2 (ms_mem ms) HAR HIN (eq_sym HlenP) KIB) as HIN2.
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
  exists [(1, fpos)], ly, S, kk, mc, fpos.
  split; [exact HJ2|]. split; [reflexivity|]. split; [exact HFR2|]. split; [exact HFL'|]. split; [exact HMOD2|].
  split; [exact HIN2|]. split; [exact HRV2|]. split; [exact HSEP|]. split; [exact HLS|]. split; [exact HRI|].
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
End gp6.
