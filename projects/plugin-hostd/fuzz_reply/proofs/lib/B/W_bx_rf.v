(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: new file, block `rf` of image B's SEG_EXIT (fuzz_reply.asan-ubsan): proves
   lib/B/W_bx_defs.v's lx_rf_site_S, the two relay_finish call sites `sd zero,-1892(s10); jal relay_finish` at
   0x84f00 (AX_join, back at 0x84f08 = AX_after_rf) and 0x84fe0 (AX_noord, back at 0x84fe8 = AX_done), relay_finish
   at 0x82344 (AF_fr_relay_finish 0).  Ported from the PROVED image-A donor (b86949b953d
   lib/A/W_LLVMFuzzerTestOneInput_exit.v) lines 1817-2932 (xrf_clear_O ..
   lx_rf_site) and :959-965 (lxk_sv8_kept).  B vs A here (B's objdump, asan-ubsan sha256 10ffb5f9202ae2bd...):
   g_nout = s10 - 1892 (x26 = HI_G_NOUT 0x5d95a4; A: s9 + 1668), SB in x27 (A: x26), aframe_at without `full`,
   relay_finish's rf_spec of lib/B/W_contract.v (RF_FRAME 48, RF_STK 16672), ablocks_sep over request sizes (the B
   cut), and every global of lib/B/W_rep.v fr_globals_b (g_nout 0x5d8e40, g_out 0x5d90c0, ...) and the image top
   0x5fc000 of lib/B/W_img.v fr_img_range.  Two lemmas are new here: xrf_errno_lo (errno >= g_out + 8 = 0x5d90c8, from
   XRF_ERRNO) and xrf_frm_off_img (a fake frame is off image B's top 0x5fc000: lib/B/W_frame.v frm_off_imgP states the
   shared core's off_img, whose top is image A's 0x5fb000). *)
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
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YB1v.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YI16 YE00.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YE01 YE2k.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YC5d.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require YCfn.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib Require Import ZTraceSpec.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import
W_syms W_listing W_place W_tbl W_kit W_pl W_img W_journal.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import HarnessRep RelayRep.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require CheckRep.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_rep W_contract W_shadow_pin W_frame.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_LLVMFuzzerTestOneInput_cut.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_bx_defs W_traps.
(* B's K0 tables (5128b798413, by path): rf_spec's caller-context table is K0's free table *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require YCk0.
(* RelocB's sink-instance guard, after every Import of YE2k: no sink class is a hint after it *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require ReplyGuardB.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Import ListNotations.
Local Unset Lia Cache. Local Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

(* the program interface's constants (lib/B/YCfn.v), as the cut names them *)
Local Notation A_LLVMF := YCfn.A_LLVMF.
Local Notation RA_LLVMF := YCfn.RA_LLVMF.
Local Notation LLVMF_STK := YCfn.LLVMF_STK.

Section lx.
Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
#[local] Notation segs := (@pa_segs _ fr_prog_listing PB_fr).
#[local] Notation VAL := (@pa_val _ fr_prog_listing PB_fr).
#[local] Notation BASE := (@pa_val _ fr_prog_listing PB_fr A_TEXT).

(* ---- W_LLVMFuzzerTestOneInput_cut.v's Section w, verbatim (W_bx_defs.v's Section lx) ---- *)
Variable B : asyms.
Variable MT : ameter_ops.
Variables XM_LIB XN_LIB : Z -> Z.
Variables RLO RHI : Z.
Variable fr_live_pre : astate -> Prop.
Variable fr_live_post : astate -> astate -> Z -> Prop.
Variable fr_surv : alayout -> astate -> alayout -> astate -> Prop.
Variable G_fr : list (Z * Z).
Variable fr_FP : bvmap 5 word -> alayout -> astate -> world segs -> (word -> option byte) -> list (Z * Z).
Variable LS : lfcx -> Z -> lmod -> alayout -> astate -> Prop.
Variable RINV : lfcx -> Z -> lmod -> Prop.
Variable MMAX : Z.

(* ---- the hypotheses this block uses: (a) lib/B/W_LLVMFuzzerTestOneInput_exit.v's Section lx, verbatim ---- *)
Hypothesis LAWS : AR_laws segs B.
Hypothesis HG : gx_ok segs B G_fr.
Hypothesis HG_SL : forall a, inG (G_SL B fr_RG) a -> inG G_fr a.
Hypothesis RFg : rf_spec B MT MMAX (RF_G fr_RG AG_LISTEN ++ G_SL B fr_RG) fr_RG AG_THREAD_UP AG_LISTEN
  YCk0.CTX_AFREE (BASE + AF_fr_relay_finish).
Hypothesis XRF_ERRNO : rg_out fr_RG + 8 <= as_errno B /\ as_errno B + 4 <= 2 ^ 64.
Hypothesis XRF_ROM_OUT : rom_out segs B G_fr.
Hypothesis LS_rf_room : forall cx t m ly S,
  LS cx t m ly S -> lx_rf_room MMAX (blocks_bytes S) (lm_c m) [] (lm_mx m) 0 (lm_cap m) (lm_es m).
(* ---- (b) the derived facts the spine proves from (a), verbatim ---- *)
Hypothesis HGs : forall a, rg_s fr_RG <= a < rg_s fr_RG + 4 * ASRC -> inG G_fr a.
Hypothesis HG_RFc : forall a, inG [(rg_lock fr_RG, 12); (rg_nsrc fr_RG, 4); (rg_client fr_RG, 4); (AG_LISTEN, 4)] a ->
  inG G_fr a.
Hypothesis XRF_Gcells : forall a,
  rg_gone fr_RG <= a < rg_gone fr_RG + 1 \/ rg_wake fr_RG + 4 <= a < rg_wake fr_RG + 8 \/
  AG_NFD <= a < AG_NFD + 4 \/ AG_THREAD_UP <= a < AG_THREAD_UP + 1 -> inG G_fr a.
Hypothesis XRF_JTAB_ROM : forall a, fr_jtab <= a < fr_jtab + 36 -> in_rom segs a.
Hypothesis XRF_END5 : forall (W : world segs) (mem : word -> option byte),
  rom_view segs W mem -> garr8 segs (arm W mem) (VAL A_lit_end5) (bzs END5).
Hypothesis LS_rf_mok : forall cx t m ly S,
  LS cx t m ly S -> mo_ok MT S (lx_rf_cost MT (lm_c m) [] (lm_mx m) 0 (lm_cap m) (lm_es m)).

(* the symbolic-run scaffolding (the cut's) *)
Let RUNTO := paj_run_to_x (PL := PL_fr) (PI := PB_fr) B LAWS G_fr HG 0 [].

(* errno lies at or above g_out + 8 (B: g_out 0x5d90c0, lib/B/W_rep.v fr_globals_b) *)
Lemma xrf_errno_lo : 0x5d90c8 <= as_errno B.
Proof.
  pose proof (proj1 XRF_ERRNO) as H. assert (E : rg_out fr_RG + 8 = 0x5d90c8) by (vm_compute; reflexivity).
  rewrite E in H. exact H.
Qed.

(* copied from W_LLVMFuzzerTestOneInput_latch.v lt_sv8_kept *)
Lemma lxk_sv8_kept : forall (W W' : world segs) mem mem' a v,
  (forall x, a <= x < a + 8 -> abyte_kept W mem W' mem' x) -> sv8 W mem a v -> sv8 W' mem' a v.
Proof.
  intros W W' mem mem' a v HK Hv. unfold sv8 in *. apply (akept_vm W mem); [|exact Hv].
  intros x Hx. apply HK. cbn in Hx. lia.
Qed.

(* g_nout := 0 forgets what the controller read in the previous operation (_head.v lm_clear_O) *)
Definition xrf_clear_O (m : lmod) : lmod :=
  LM (lm_k m) (lm_hs m) (lm_G m) (lm_es m) (lm_c m) [] (lm_mx m) (lm_cap m) (lm_out m) (lm_gn m) (lm_nfd m).
Definition xrf_offw (lo hi a : Z) : Prop := 0 <= a < 2 ^ 64 /\ ~ (lo <= a < hi).
Definition xrf_rng_off (lo hi : Z) (r : Z * Z) : Prop := forall a, fst r <= a < snd r -> xrf_offw lo hi a.

Lemma xrf_writable_kept : forall (W : world segs) mem mem',
  mem_grows (mrestrict (w_H W) mem) (mrestrict (w_H W) mem') ->
  forall a, writable_at segs (arm W mem) a -> writable_at segs (arm W mem') a.
Proof.
  intros W mem mem' HGR a. unfold arm. apply writable_kept. intros [Hh [b Hb]]. split; [exact Hh|].
  specialize (HGR (Z_to_bv 64 a)). unfold mrestrict in HGR. rewrite Hh, Hb in HGR.
  destruct (mem' (Z_to_bv 64 a)) as [b'|]; [exists b'; reflexivity|]. exfalso. apply HGR; first [discriminate | reflexivity].
Qed.
Lemma xrf_kept_off : forall (W : world segs) mem mem' lo hi,
  (forall x : word, ~ (lo <= bv_unsigned x < hi) -> mrestrict (w_H W) mem' x = mrestrict (w_H W) mem x) ->
  mem_grows (mrestrict (w_H W) mem) (mrestrict (w_H W) mem') ->
  forall a, xrf_offw lo hi a -> abyte_kept W mem W mem' a.
Proof.
  intros W mem mem' lo hi HKX HGR a [Ha Hn]. split.
  - apply aview_eq_of. apply HKX. rewrite unsigned_lit_small by lia. exact Hn.
  - exact (xrf_writable_kept W mem mem' HGR a).
Qed.
Lemma xrf_akept : forall (W : world segs) mem mem' lo hi fp,
  (forall a, xrf_offw lo hi a -> abyte_kept W mem W mem' a) ->
  (forall r, In r fp -> xrf_rng_off lo hi r) -> akept W mem W mem' fp.
Proof. intros W mem mem' lo hi fp KB Hfp r Hr a Ha. apply KB. exact (Hfp r Hr a Ha). Qed.
Lemma xrf_rng_off_sub : forall lo hi a n a' n', xrf_rng_off lo hi (a, a + n) -> a <= a' -> a' + n' <= a + n ->
  xrf_rng_off lo hi (a', a' + n').
Proof. intros lo hi a n a' n' H H1 H2 x Hx. apply H. cbn [fst snd] in Hx |- *. lia. Qed.

Lemma xrf_len_text : forall recs, length (concat (map text_rec recs)) = (16 * length recs)%nat.
Proof.
  induction recs as [|r recs IH]; [reflexivity|]. cbn [map concat]. rewrite length_app, IH.
  assert (Hx : length (text_rec r) = 16%nat) by reflexivity. rewrite Hx. cbn [length]. lia.
Qed.
Lemma xrf_len_kptrs : forall ks, length (gestures_end_b_c.key_ptrs ks) = (8 * length ks)%nat.
Proof.
  induction ks as [|k ks IH]; [reflexivity|]. unfold gestures_end_b_c.key_ptrs in *. cbn [map concat]. rewrite length_app, IH.
  match goal with |- (length ?x + _)%nat = _ => assert (Hx : length x = 8%nat) by reflexivity; rewrite Hx end.
  cbn [length]. lia.
Qed.

Section fo.
Variables lo hi : Z.
Hypothesis Hlo : 0x10008 <= lo.
Hypothesis Hhi : hi <= 0x5fc000.
(* a byte of a live block, or within 8 bytes after it *)
Lemma xrf_blk_off : forall ly S W mem md p n a, AR segs B ly S W mem md -> In (p, n) (ablocks B ly S) ->
  p <= a < p + req_size n + 8 -> xrf_offw lo hi a.
Proof.
  intros ly S W mem md p n a HAR Hin Ha.
  destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR Hin) as (_ & Hp4096 & Hpceil & _ & _ & _).
  pose proof (blk_off_imgP B _ _ _ _ _ _ _ HAR Hin) as Himg. red in Himg.
  pose proof asan_consts as (C1 & _). split; lia.
Qed.
Lemma xrf_alist_fp_off : forall ly S W mem md LA l lines, AR segs B ly S W mem md ->
  alist_at B ly S W mem LA l lines -> xrf_rng_off lo hi (LA, LA + 16) ->
  forall r, In r (alist_fp LA l) -> xrf_rng_off lo hi r.
Proof.
  intros ly S W mem md LA l lines HAR (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9) HLA r Hr.
  unfold alist_fp in Hr. destruct Hr as [<- | Hr]; [exact HLA|].
  apply in_app_or in Hr as [Hr | Hr].
  - destruct (hl_cap l =? 0) eqn:Ec; [destruct Hr|]. destruct Hr as [<- | []].
    apply Z.eqb_neq in Ec.
    destruct H6 as [(Hc & _) | (Hc & Hin & Hj & _)]; [lia|].
    intros a Ha. unfold gfp, bzs in Ha. cbn [fst snd] in Ha. rewrite length_map, length_app, xrf_len_text in Ha.
    unfold hl_n in Hj, H5.
    apply (xrf_blk_off ly S W mem md (hl_v l) (AREC * hl_cap l) a HAR Hin).
    pose proof (req_size_pos (AREC * hl_cap l) ltac:(unfold AREC; lia)) as [_ Hq]. unfold AREC in *. lia.
  - apply in_map_iff in Hr as (rr & <- & Hrr). rewrite Forall_forall in H9. destruct (H9 rr Hrr) as (Hb & _).
    intros a Ha. unfold gfp, bzs in Ha. cbn [fst snd] in Ha. rewrite length_map, length_app in Ha. cbn [length] in Ha.
    apply (xrf_blk_off ly S W mem md (fst rr) (Z.of_nat (length (snd rr)) + 1) a HAR Hb).
    pose proof (req_size_pos (Z.of_nat (length (snd rr)) + 1) ltac:(lia)) as [_ Hq]. lia.
Qed.
Lemma xrf_alist_blks_in : forall ly S W mem LA l lines, alist_at B ly S W mem LA l lines ->
  forall b, In b (alist_blks l) -> In b (ablocks B ly S).
Proof.
  intros ly S W mem LA l lines (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9) b Hb.
  unfold alist_blks in Hb. apply in_app_or in Hb as [Hb | Hb].
  - destruct (hl_cap l =? 0) eqn:Ec; [destruct Hb|]. destruct Hb as [<- | []]. apply Z.eqb_neq in Ec.
    destruct H6 as [(Hc & _) | (Hc & Hin & _)]; [lia | exact Hin].
  - apply in_map_iff in Hb as (rr & <- & Hrr). rewrite Forall_forall in H9. exact (proj1 (H9 rr Hrr)).
Qed.
Lemma xrf_asrc_fp_off : forall ly S W mem md HA h, AR segs B ly S W mem md -> asrc_at B ly S W mem HA h ->
  xrf_rng_off lo hi (HA, HA + ASRC) -> forall r, In r (asrc_fp HA h) -> xrf_rng_off lo hi r.
Proof.
  intros ly S W mem md HA h HAR Hs HHA r Hr.
  pose proof Hs as (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11 & H12 & H13 & H14 & H15 & H16 & H17 & H18 &
    H19 & H20 & H21 & H22 & H23 & H24).
  unfold asrc_fp in Hr. destruct Hr as [<- | [<- | Hr]]; [exact HHA | |].
  - intros a Ha. unfold gfp, bzs in Ha. cbn [fst snd] in Ha. rewrite length_map, H19 in Ha.
    apply (xrf_blk_off ly S W mem md (hs_partial h) APARTIAL a HAR H18).
    pose proof (req_size_pos APARTIAL ltac:(unfold APARTIAL; lia)) as [_ Hq]. lia.
  - apply in_app_or in Hr as [Hr | Hr]; [|apply in_app_or in Hr as [Hr | Hr]].
    + apply (xrf_alist_fp_off ly S W mem md (HA + 16) (hs_pending h) false HAR H10); [|exact Hr].
      apply (xrf_rng_off_sub lo hi HA ASRC); [exact HHA | lia | unfold ASRC; lia].
    + apply (xrf_alist_fp_off ly S W mem md (HA + 64) (hs_expected h) true HAR H22); [|exact Hr].
      apply (xrf_rng_off_sub lo hi HA ASRC); [exact HHA | lia | unfold ASRC; lia].
    + apply (xrf_alist_fp_off ly S W mem md (HA + 80) (hs_held h) true HAR H23); [|exact Hr].
      apply (xrf_rng_off_sub lo hi HA ASRC); [exact HHA | lia | unfold ASRC; lia].
Qed.
Lemma xrf_asrc_blks_in : forall ly S W mem HA h, asrc_at B ly S W mem HA h ->
  forall b, In b (asrc_blks h) -> In b (ablocks B ly S).
Proof.
  intros ly S W mem HA h Hs b Hb.
  pose proof Hs as (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11 & H12 & H13 & H14 & H15 & H16 & H17 & H18 &
    H19 & H20 & H21 & H22 & H23 & H24).
  unfold asrc_blks in Hb. destruct Hb as [<- | Hb]; [exact H18|].
  apply in_app_or in Hb as [Hb | Hb]; [|apply in_app_or in Hb as [Hb | Hb]].
  - exact (xrf_alist_blks_in ly S W mem _ _ _ H10 b Hb).
  - exact (xrf_alist_blks_in ly S W mem _ _ _ H22 b Hb).
  - exact (xrf_alist_blks_in ly S W mem _ _ _ H23 b Hb).
Qed.
Lemma xrf_aentry_fp_off : forall ly S W mem md e, AR segs B ly S W mem md -> aentry_ok B ly S W mem e ->
  forall r, In r (aentry_fp e) -> xrf_rng_off lo hi r.
Proof.
  intros ly S W mem md e HAR (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11 & H12 & H13 & H14 & H15) r Hr.
  unfold aentry_fp in Hr. apply in_app_or in Hr as [Hr | Hr].
  - destruct (re_cap e =? 0) eqn:Ec; [destruct Hr|]. destruct Hr as [<- | []]. apply Z.eqb_neq in Ec.
    destruct H10 as [(Hc & _) | (Hc & Hin & Hj & _)]; [lia|].
    intros a Ha. unfold gfp, bzs in Ha. cbn [fst snd] in Ha. rewrite length_map, length_app in Ha.
    apply (xrf_blk_off ly S W mem md (re_buf e) (re_cap e) a HAR Hin).
    pose proof (req_size_pos (re_cap e) ltac:(lia)) as [_ Hq]. lia.
  - destruct Hr as [<- | Hr].
    + intros a Ha. unfold gfp, bzs in Ha. cbn [fst snd] in Ha. rewrite length_map, xrf_len_kptrs in Ha.
      destruct H12 as [(Hz & Hk) | (Hz & Hin & Hk1 & Hk2 & _)]; [rewrite Hk in Ha; cbn in Ha; lia|].
      apply (xrf_blk_off ly S W mem md (re_hp e) (re_kh e) a HAR Hin).
      pose proof (req_size_pos (re_kh e) ltac:(lia)) as [_ Hq]. unfold re_nheld in Hk1. lia.
    + apply in_map_iff in Hr as (k & <- & Hk). rewrite Forall_forall in H15. destruct (H15 k Hk) as (K1 & K2 & K3 & K4 & K5).
      intros a Ha. unfold gfp, bzs in Ha. cbn [fst snd] in Ha. rewrite length_map, length_app in Ha. cbn [length] in Ha.
      apply (xrf_blk_off ly S W mem md (gestures_end_b_c.key_addr k) (Z.of_nat (length (gestures_end_b_c.key_text k)) + 1) a HAR K1).
      pose proof (req_size_pos (Z.of_nat (length (gestures_end_b_c.key_text k)) + 1) ltac:(lia)) as [_ Hq]. lia.
Qed.
Lemma xrf_aentry_blks_in : forall ly S W mem e, aentry_ok B ly S W mem e ->
  forall b, In b (aentry_blks e) -> In b (ablocks B ly S).
Proof.
  intros ly S W mem e (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11 & H12 & H13 & H14 & H15) b Hb.
  unfold aentry_blks in Hb. apply in_app_or in Hb as [Hb | Hb]; [|apply in_app_or in Hb as [Hb | Hb]].
  - destruct (re_cap e =? 0) eqn:Ec; [destruct Hb|]. destruct Hb as [<- | []]. apply Z.eqb_neq in Ec.
    destruct H10 as [(Hc & _) | (Hc & Hin & _)]; [lia | exact Hin].
  - destruct (re_hp e =? 0) eqn:Ez; [destruct Hb|]. destruct Hb as [<- | []]. apply Z.eqb_neq in Ez.
    destruct H12 as [(Hz & _) | (Hz & Hin & _)]; [lia | exact Hin].
  - apply in_map_iff in Hb as (k & <- & Hk). rewrite Forall_forall in H15. exact (proj1 (H15 k Hk)).
Qed.
Lemma xrf_arelay_fp_off : forall RG ly S W mem md G es, AR segs B ly S W mem md -> arelay_at B RG ly S W mem G es ->
  xrf_rng_off lo hi (rg_src RG, rg_src RG + 8) -> xrf_rng_off lo hi (rg_nsrc RG, rg_nsrc RG + 4) ->
  xrf_rng_off lo hi (rg_capsrc RG, rg_capsrc RG + 4) ->
  forall r, In r (arelay_fp RG G es) -> xrf_rng_off lo hi r.
Proof.
  intros RG ly S W mem md G es HAR (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11) R1 R2 R3 r Hr.
  unfold arelay_fp in Hr. destruct Hr as [<- | [<- | [<- | [<- | Hr]]]]; [exact R1 | exact R2 | exact R3 | |].
  - intros a Ha. cbn [fst snd] in Ha. apply (xrf_blk_off ly S W mem md G ATABLE a HAR H8).
    pose proof (req_size_pos ATABLE ltac:(unfold ATABLE; lia)) as [_ Hq]. lia.
  - apply in_concat in Hr as (l & Hl & Hr). apply in_map_iff in Hl as (e & <- & He).
    rewrite Forall_forall in H10. exact (xrf_aentry_fp_off ly S W mem md e HAR (H10 e He) r Hr).
Qed.
Lemma xrf_arelay_blks_in : forall RG ly S W mem G es, arelay_at B RG ly S W mem G es ->
  forall b, In b (arelay_blks G es) -> In b (ablocks B ly S).
Proof.
  intros RG ly S W mem G es (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11) b Hb.
  unfold arelay_blks in Hb. destruct Hb as [<- | Hb]; [exact H8|].
  apply in_concat in Hb as (l & Hl & Hb). apply in_map_iff in Hl as (e & <- & He).
  rewrite Forall_forall in H10. exact (xrf_aentry_blks_in ly S W mem e (H10 e He) b Hb).
Qed.
End fo.

Definition xrf_seg_rom_hit (lo hi : Z) : bool :=
  existsb (fun sg => negb (seg_writable sg) && (Z.of_N (seg_base sg) <? hi) && (lo <? Z.of_N (seg_base sg) + Z.of_N (seg_size sg)))
    segs.
Lemma xrf_not_rom : forall lo hi a, xrf_seg_rom_hit lo hi = false -> lo <= a < hi -> ~ in_rom segs a.
Proof.
  intros lo hi a Hh Ha (sg & Hin & Hw & Hr). unfold xrf_seg_rom_hit in Hh.
  assert (Hx : existsb (fun sg => negb (seg_writable sg) && (Z.of_N (seg_base sg) <? hi) &&
    (lo <? Z.of_N (seg_base sg) + Z.of_N (seg_size sg))) segs = true).
  { apply existsb_exists. exists sg. split; [exact Hin|]. rewrite Hw. cbn [negb andb].
    apply andb_true_intro. split; apply Z.ltb_lt; lia. }
  rewrite Hh in Hx. discriminate.
Qed.
Lemma xrf_rom_low : forall a, in_rom segs a -> 0 <= a < 2 ^ 64.
Proof.
  intros a (sg & Hin & _ & Hr). pose proof (pa_segs_low a (ex_intro _ sg (conj Hin Hr))) as H.
  unfold kLowMemEnd in H. lia.
Qed.
Lemma xrf_nout_not_rom : xrf_seg_rom_hit 6131264 6131272 = false.
Proof. vm_compute. reflexivity. Qed.

Lemma xrf_aout_clear : forall ly S W mem md mem' c O mx no cap out,
  AR segs B ly S W mem md ->
  (forall a, xrf_offw 6131264 6131272 a -> abyte_kept W mem W mem' a) ->
  (forall a, writable_at segs (arm W mem) a -> writable_at segs (arm W mem') a) ->
  val_mem segs (arm W mem') (rg_nout fr_RG) 8 0 -> xrf_rng_off 6131264 6131272 (as_errno B, as_errno B + 4) ->
  aout_at B fr_RG ly S W mem c O mx no cap out -> aout_at B fr_RG ly S W mem' c [] mx 0 cap out.
Proof.
  intros ly S W mem md mem' c O mx no cap out HAR KB KW HN0 HER
    (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11 & H12 & H13 & H14 & H15 & H16 & H17 & H18 &
     H19 & H20 & H21 & H22 & H23 & H24 & H25 & H26).
  assert (KK : forall x, 0 <= x < 6131264 \/ 6131272 <= x < 2 ^ 64 -> abyte_kept W mem W mem' x)
    by (intros x Hx; apply KB; split; lia).
  unfold aout_at. cbn [rg_send_max rg_nout rg_capout rg_out rg_client rg_client_broken rg_send_dead rg_send_eintr fr_RG fr_globals_b]
    in *.
  pose proof HER as HER'. unfold xrf_rng_off, xrf_offw in HER'. cbn [fst snd] in HER'.
  split; [apply (akept_vm W mem); [intros x Hx; apply KK; cbn in Hx; lia | exact H1]|].
  split; [apply (akept_awr W mem); [intros x Hx; apply KK; lia | exact H2]|].
  split; [exact HN0|].
  split; [intros i Hi; apply KW; exact (H4 i Hi)|].
  split; [apply (akept_vm W mem); [intros x Hx; apply KK; cbn in Hx; lia | exact H5]|].
  split; [apply (akept_awr W mem); [intros x Hx; apply KK; lia | exact H6]|].
  split; [apply (akept_vm W mem); [intros x Hx; apply KK; cbn in Hx; lia | exact H7]|].
  split; [apply (akept_awr W mem); [intros x Hx; apply KK; lia | exact H8]|].
  split; [apply (akept_vm W mem); [intros x Hx; apply KK; cbn in Hx; lia | exact H9]|].
  split; [apply (akept_awr W mem); [intros x Hx; apply KK; lia | exact H10]|].
  split; [apply (akept_vm W mem); [intros x Hx; apply KK; cbn in Hx; lia | exact H11]|].
  split; [apply (akept_awr W mem); [intros x Hx; apply KK; lia | exact H12]|].
  split; [apply (akept_vm W mem); [intros x Hx; apply KK; cbn in Hx; lia | exact H13]|].
  split; [apply (akept_awr W mem); [intros x Hx; apply KK; lia | exact H14]|].
  split; [apply (akept_vm W mem); [intros x Hx; apply KK; cbn in Hx; lia | exact H15]|].
  split; [apply (akept_awr W mem); [intros x Hx; apply KK; lia | exact H16]|].
  split; [apply (akept_vm W mem); [intros x Hx; apply KB; apply HER'; cbn in Hx; lia | exact H17]|].
  split; [apply (akept_awr W mem); [intros x Hx; apply KB; apply HER'; lia | exact H18]|].
  do 6 (split; [assumption|]).
  split; [reflexivity|].
  destruct H26 as [(Hc & Ho & Hn) | (Hc & Hno & Hin & junk & Hj & Hg)]; [left; lia|right].
  split; [exact Hc|]. split; [lia|]. split; [exact Hin|].
  exists (O ++ junk). split; [rewrite length_app, Nat2Z.inj_add; lia|].
  cbn [app]. apply (akept_garr8 W mem); [|exact Hg].
  intros x Hx. unfold bzs in Hx. rewrite length_map, length_app, Nat2Z.inj_add in Hx. apply KB.
  apply (xrf_blk_off 6131264 6131272 ltac:(lia) ltac:(lia) ly S W mem md out cap x HAR Hin).
  pose proof (req_size_pos cap ltac:(lia)) as [_ Hq]. lia.
Qed.

(* a fake frame is off image B (top 0x5fc000, lib/B/W_img.v fr_img_range): lib/B/W_frame.v frm_off_imgP's proof at
   B's top (its statement's off_img is the shared core's, with image A's top 0x5fb000) *)
Lemma xrf_frm_off_img : forall ly S (W : world segs) mem md cid pos,
  AR segs B ly S W mem md -> In (cid, pos) (frames S) ->
  frame_addr ly cid pos + fs_frame_bytes cid <= 0x10000 \/ 0x5fc000 <= frame_addr ly cid pos.
Proof.
  intros ly S W mem md cid pos (M & LG & _) Hin. pose proof (pa_img_cover ly S md LG) as [C1 C2].
  pose proof (OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable.YG0s.frame_facts B ly S _ cid pos M Hin)
    as (Fc & Fp & _ & _ & _ & _ & _ & _ & F64 & _).
  destruct (Z.le_gt_cases (frame_addr ly cid pos + fs_frame_bytes cid) 0x10000) as [|H1]; [left; lia|].
  destruct (Z.le_gt_cases 0x5fc000 (frame_addr ly cid pos)) as [|H2]; [right; lia|]. exfalso.
  apply (OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable.YG0s.client_byte_not_img B ly S _
    (Z.max (frame_addr ly cid pos) 0x10000) M).
  - right. exists (cid, pos). split; [exact Hin|]. left. unfold in_zr. cbn [fst snd]. lia.
  - unfold in_zr. lia.
Qed.
Lemma xrf_store_kept : forall cx ly3 S3 W mem md mem' fpos m,
  lf_base B MT XM_LIB RLO RHI fr_live_pre G_fr cx ->
  AR segs B ly3 S3 W mem md -> In (1, fpos) (frames S3) ->
  (forall x : word, ~ (rg_nout fr_RG <= bv_unsigned x < rg_nout fr_RG + 8) -> mrestrict (w_H W) mem' x = mrestrict (w_H W) mem x) ->
  mem_grows (mrestrict (w_H W) mem) (mrestrict (w_H W) mem') ->
  val_mem segs (arm W mem') (rg_nout fr_RG) 8 0 ->
  aframe_at cx (frame_addr ly3 1 fpos) W mem -> amodel_at B ly3 S3 W mem m -> ainput_at B cx ly3 S3 W mem ->
  rom_view segs W mem -> jt_rom W mem ->
  aframe_at cx (frame_addr ly3 1 fpos) W mem' /\ amodel_at B ly3 S3 W mem' (xrf_clear_O m) /\
  ainput_at B cx ly3 S3 W mem' /\ rom_view segs W mem' /\ jt_rom W mem'.
Proof.
  intros cx ly3 S3 W mem md mem' fpos m HB HAR Hfp HKX HGR HN0 HFR HMOD HIN HRV HJT.
  change (rg_nout fr_RG) with 6131264 in HKX, HN0.
  pose proof (xrf_kept_off W mem mem' 6131264 (6131264 + 8) HKX HGR) as KB. change (6131264 + 8) with 6131272 in KB.
  pose proof (xrf_writable_kept W mem mem' HGR) as KW.
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  pose proof HB as (HAI & HPRE & Hra & Ha0 & Ha1 & Hblk0 & Hlen & _).
  pose proof HPRE as (HAR0 & Hra0 & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
  pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
  unfold LLVMF_STK in *.
  pose proof (Z.mod_pos_bound (spZ (c_regs cx) - 320) 32 ltac:(lia)) as HFm.
  assert (HF : spZ (c_regs cx) - 351 <= lf_F cx <= spZ (c_regs cx) - 320) by (unfold lf_F; lia).
  destruct (frames_bounds _ _ LAWS _ _ _ _ _ _ _ HAR Hfp) as (HFF0 & HFF1 & _).
  pose proof (xrf_frm_off_img _ _ _ _ _ _ _ HAR Hfp) as HFFi.
  change (fs_frame_bytes 1) with 128 in HFF1, HFFi.
  assert (KX : forall a n, 0 <= a -> a + n <= 6131264 \/ 6131272 <= a -> a + n <= 2 ^ 64 ->
    forall x, a <= x < a + n -> abyte_kept W mem W mem' x)
    by (intros a n Ha Hn Hb x Hx; apply KB; split; lia).
  split; [|split; [|split; [|split]]].
  - (* the frame and the fake frame *)
    unfold aframe_at in *. cbv zeta in *.
    destruct HFR as (FS & FW & F32 & F40 & F48 & F56 & F64 & F72 & F80 & F96 & F104 & F120 & F128 & F136 & F152 &
      F184 & FF0 & FF8 & FF16 & FFw & FFsh & FFshw).
    unfold sv8 in *.
    assert (KV : forall a v, lf_F cx <= a -> a + 8 <= spZ (c_regs cx) ->
      val_mem segs (arm W mem) a 8 v -> val_mem segs (arm W mem') a 8 v)
      by (intros a v H1 H2 Hv; apply (akept_vm W mem); [intros x Hx; apply (KX a 8); lia | exact Hv]).
    assert (KF : forall a v, frame_addr ly3 1 fpos <= a -> a + 8 <= frame_addr ly3 1 fpos + 128 ->
      val_mem segs (arm W mem) a 8 v -> val_mem segs (arm W mem') a 8 v)
      by (intros a v H1 H2 Hv; apply (akept_vm W mem); [intros x Hx; apply (KX a 8); lia | exact Hv]).
    split.
    { intros o r Hor. assert (Ho : 8 <= o <= 104).
      { unfold saved_regs in Hor. cbn [In] in Hor.
        repeat (destruct Hor as [Hor | Hor]; [injection Hor as <- _; lia |]). destruct Hor. }
      apply KV; [lia | lia | exact (FS o r Hor)]. }
    split; [apply (akept_awr W mem); [intros x Hx; apply (KX (lf_F cx) (spZ (c_regs cx) - lf_F cx)); lia | exact FW]|].
    split; [apply KV; [lia | lia | exact F32]|]. split; [apply KV; [lia | lia | exact F40]|].
    split; [apply KV; [lia | lia | exact F48]|]. split; [apply KV; [lia | lia | exact F56]|].
    split; [apply KV; [lia | lia | exact F64]|]. split; [apply KV; [lia | lia | exact F72]|].
    split; [apply KV; [lia | lia | exact F80]|]. split; [apply KV; [lia | lia | exact F96]|].
    split; [apply KV; [lia | lia | exact F104]|]. split; [apply KV; [lia | lia | exact F120]|].
    split; [apply KV; [lia | lia | exact F128]|]. split; [apply KV; [lia | lia | exact F136]|].
    split; [apply KV; [lia | lia | exact F152]|]. split; [apply KV; [lia | lia | exact F184]|].
    split; [apply KF; [lia | lia | exact FF0]|]. split; [apply KF; [lia | lia | exact FF8]|].
    split; [apply KF; [lia | lia | exact FF16]|].
    split; [apply (akept_awr W mem); [intros x Hx; apply (KX (frame_addr ly3 1 fpos) 128); lia | exact FFw]|].
    assert (HSB : 0 <= SB + frame_addr ly3 1 fpos / 8 /\ SB + frame_addr ly3 1 fpos / 8 + 16 <= 2 ^ 64 /\
      6131272 <= SB + frame_addr ly3 1 fpos / 8).
    { unfold SB. pose proof (Z.div_pos (frame_addr ly3 1 fpos) 8 ltac:(lia) ltac:(lia)).
      pose proof (Z.div_le_upper_bound (frame_addr ly3 1 fpos) 8 (2 ^ 47) ltac:(lia) ltac:(lia)). lia. }
    split.
    { apply (akept_garr8 W mem); [|exact FFsh]. intros x Hx. change (length fake_shadow) with 16%nat in Hx.
      apply (KX (SB + frame_addr ly3 1 fpos / 8) 16); lia. }
    apply (akept_awr W mem); [intros x Hx; apply (KX (SB + frame_addr ly3 1 fpos / 8) 16); lia | exact FFshw].
  - (* the model, with what the controller read in this operation forgotten *)
    destruct HMOD as (Hhs4 & Hslots & Hrel & Hout & Hgone & Hlock & Hwake & Hnfd & Hnfdw & Hnfdr & Htu & Hlst & Hlstw).
    unfold amodel_at. cbn [lm_hs lm_G lm_es lm_c lm_O lm_mx lm_cap lm_out lm_gn lm_nfd xrf_clear_O].
    split; [exact Hhs4|].
    split.
    { intros i Hi. specialize (Hslots i Hi). unfold aslot in *.
      assert (HHA : xrf_rng_off 6131264 6131272 (rg_s fr_RG + ASRC * Z.of_nat i, rg_s fr_RG + ASRC * Z.of_nat i + ASRC)).
      { intros x Hx. cbn [fst snd rg_s fr_RG fr_globals_b] in Hx. unfold ASRC in Hx. split; lia. }
      destruct (nth i (lm_hs m) None) as [h|].
      - apply (asrc_at_kept B ly3 S3 W mem ly3 S3 W mem' _ h Hslots).
        + apply (xrf_akept W mem mem' 6131264 6131272); [exact KB|].
          exact (xrf_asrc_fp_off 6131264 6131272 ltac:(lia) ltac:(lia) ly3 S3 W mem md _ h HAR Hslots HHA).
        + exact (xrf_asrc_blks_in ly3 S3 W mem _ h Hslots).
      - destruct Hslots as [Hz Hw]. split.
        + apply (akept_garr8 W mem); [|exact Hz]. intros x Hx. rewrite repeat_length in Hx. apply KB. apply HHA.
          cbn [fst snd]. unfold ASRC in *. lia.
        + apply (akept_awr W mem); [|exact Hw]. intros x Hx. apply KB. apply HHA. cbn [fst snd]. lia. }
    split.
    { apply (arelay_at_kept B fr_RG ly3 S3 W mem ly3 S3 W mem' _ _ Hrel).
      + apply (xrf_akept W mem mem' 6131264 6131272); [exact KB|].
        apply (xrf_arelay_fp_off 6131264 6131272 ltac:(lia) ltac:(lia) fr_RG ly3 S3 W mem md _ _ HAR Hrel);
          intros x Hx; cbn [fst snd rg_src rg_nsrc rg_capsrc fr_RG fr_globals_b] in Hx; split; lia.
      + exact (xrf_arelay_blks_in fr_RG ly3 S3 W mem _ _ Hrel). }
    split.
    { eapply (xrf_aout_clear ly3 S3 W mem md mem' _ _ _ _ _ _ HAR KB KW HN0); [|exact Hout].
      intros x Hx. cbn [fst snd] in Hx. pose proof xrf_errno_lo as He0. pose proof (proj2 XRF_ERRNO) as He1.
      split; lia. }
    split.
    { apply (agone_at_kept fr_RG W mem W mem' _ Hgone). intros r Hr a Ha. destruct Hr as [<- | []].
      apply KB. cbn in Ha |- *. split; lia. }
    split.
    { apply (alock_at_kept fr_RG W mem W mem' _ Hlock). intros r Hr a Ha. destruct Hr as [<- | []].
      apply KB. cbn in Ha |- *. split; lia. }
    split.
    { apply (awake_at_kept fr_RG W mem W mem' Hwake). intros r Hr a Ha. destruct Hr as [<- | []].
      apply KB. cbn in Ha |- *. split; lia. }
    split; [apply (akept_vm W mem); [intros x Hx; apply KB; unfold AG_NFD in *; cbn in Hx; split; lia | exact Hnfd]|].
    split; [apply (akept_awr W mem); [intros x Hx; apply KB; unfold AG_NFD in *; split; lia | exact Hnfdw]|].
    split; [exact Hnfdr|].
    split; [apply (akept_vm W mem); [intros x Hx; apply KB; unfold AG_THREAD_UP in *; cbn in Hx; split; lia | exact Htu]|].
    split; [destruct Hlst as [lst Hlst]; exists lst;
      apply (akept_vm W mem); [intros x Hx; apply KB; unfold AG_LISTEN in *; cbn in Hx; split; lia | exact Hlst]|].
    apply (akept_awr W mem); [intros x Hx; apply KB; unfold AG_LISTEN in *; split; lia | exact Hlstw].
  - (* the input block *)
    destruct HIN as [Hblk Hg]. split; [exact Hblk|]. apply (akept_garr8 W mem); [|exact Hg].
    intros x Hx. rewrite length_map, <- Hlen in Hx. apply KB.
    destruct Hblk as [(Hn0 & _) | (Hn & Hin)]; [lia|].
    apply (xrf_blk_off 6131264 6131272 ltac:(lia) ltac:(lia) ly3 S3 W mem md (c_p cx) (c_n cx) x HAR Hin).
    pose proof (req_size_pos (c_n cx) ltac:(lia)) as [_ Hq]. lia.
  - (* .rodata *)
    intros a Ha. pose proof (xrf_rom_low a Ha) as Hrl.
    destruct (Z_lt_le_dec a 6131264) as [Hlt | Hge].
    + rewrite (proj1 (KB a ltac:(split; lia))). apply HRV. exact Ha.
    + destruct (Z_lt_le_dec a 6131272) as [Hlt2 | Hge2].
      * exfalso. exact (xrf_not_rom 6131264 6131272 a xrf_nout_not_rom ltac:(lia) Ha).
      * rewrite (proj1 (KB a ltac:(split; lia))). apply HRV. exact Ha.
  - (* the jump table *)
    intros i Hi. apply (akept_vm W mem); [|exact (HJT i Hi)].
    intros x Hx. apply KB. unfold fr_jtab in Hx. cbn in Hx. split; lia.
Qed.
(* the fake frame's flag word across the same store: the fake frame is off the image, so off g_nout *)
Lemma xrf_store_flag : forall ly3 S3 W mem md mem' fpos,
  AR segs B ly3 S3 W mem md -> In (1, fpos) (frames S3) ->
  (forall x : word, ~ (rg_nout fr_RG <= bv_unsigned x < rg_nout fr_RG + 8) -> mrestrict (w_H W) mem' x = mrestrict (w_H W) mem x) ->
  mem_grows (mrestrict (w_H W) mem) (mrestrict (w_H W) mem') ->
  sv8 W mem (frame_addr ly3 1 fpos + 120) (flag_addr ly3 1 fpos) ->
  sv8 W mem' (frame_addr ly3 1 fpos + 120) (flag_addr ly3 1 fpos).
Proof.
  intros ly3 S3 W mem md mem' fpos HAR Hfp HKX HGR HFL.
  change (rg_nout fr_RG) with 6131264 in HKX.
  pose proof (xrf_kept_off W mem mem' 6131264 (6131264 + 8) HKX HGR) as KB. change (6131264 + 8) with 6131272 in KB.
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  destruct (frames_bounds _ _ LAWS _ _ _ _ _ _ _ HAR Hfp) as (HFF0 & HFF1 & _).
  pose proof (xrf_frm_off_img _ _ _ _ _ _ _ HAR Hfp) as HFFi.
  change (fs_frame_bytes 1) with 128 in HFF1, HFFi.
  apply (lxk_sv8_kept W W mem mem'); [|exact HFL]. intros x Hx. apply KB. split; lia.
Qed.

(* ------------------------------------------------------------------ the call's kit *)
(* lx_rf_* are W5's rf_* (W_contract.v Section rfs) at MT / MMAX *)
Lemma xrf_run_eq : forall es c O mx no cap, lx_rf_run c O mx no cap es = rf_run c O mx no cap es.
Proof. induction es as [|e es IH]; intros c O mx no cap; [reflexivity|]. cbn [lx_rf_run rf_run]. apply IH. Qed.
Lemma xrf_cost_eq : forall es c O mx no cap, lx_rf_cost MT c O mx no cap es = rf_cost MT c O mx no cap es.
Proof. induction es as [|e es IH]; intros c O mx no cap; [reflexivity|]. cbn [lx_rf_cost rf_cost]. rewrite IH. reflexivity. Qed.
Lemma xrf_room_eq : forall es bb c O mx no cap, lx_rf_room MMAX bb c O mx no cap es -> rf_room MMAX bb c O mx no cap es.
Proof.
  induction es as [|e es IH]; intros bb c O mx no cap H; [exact I|]. cbn [lx_rf_room rf_room] in *.
  destruct H as [H1 H2]. split; [exact H1 | apply IH; exact H2].
Qed.
(* relay_finish's G, and where its bytes lie *)
Definition xrf_G : list (Z * Z) := RF_G fr_RG AG_LISTEN ++ G_SL B fr_RG.
(* B's fr_globals_b (lib/B/W_rep.v) and AG_LISTEN (the cut): g_lock 0x5d9040 (12), g_nsrc 0x5d8d20, g_client 0xa2560,
   g_listen 0xa2540, g_client_broken 0x5d8d60, g_send_eintr 0x5d8e20, g_nout 0x5d8e40, g_capout 0x5d90a0,
   g_out 0x5d90c0, errno *)
Lemma xrf_inG_RF : forall a, inG xrf_G a ->
  (0x5d9040 <= a < 0x5d904c) \/ (0x5d8d20 <= a < 0x5d8d24) \/ (0xa2560 <= a < 0xa2564) \/ (0xa2540 <= a < 0xa2544) \/
  (0x5d8d60 <= a < 0x5d8d61) \/ (0x5d8e20 <= a < 0x5d8e21) \/ (0x5d8e40 <= a < 0x5d8e48) \/
  (0x5d90a0 <= a < 0x5d90a8) \/ (0x5d90c0 <= a < 0x5d90c8) \/ (as_errno B <= a < as_errno B + 4).
Proof.
  intros a Ha. unfold xrf_G in Ha. apply inG_app in Ha as [Ha | Ha]; unfold RF_G, G_SL in Ha;
  repeat (apply inG_cons in Ha as [Ha | Ha]; [unfold in_zr, AG_LISTEN in Ha; cbn in Ha; lia |]);
  exfalso; exact (inG_nil a Ha).
Qed.
Lemma xrf_G_sub : forall a, inG xrf_G a -> inG G_fr a.
Proof.
  intros a Ha. unfold xrf_G in Ha. apply inG_app in Ha as [Ha | Ha]; [apply HG_RFc; exact Ha | apply HG_SL; exact Ha].
Qed.
Lemma xrf_G_ok : gx_ok segs B xrf_G.
Proof. exact (gx_ok_sub segs B xrf_G G_fr xrf_G_sub HG). Qed.
(* a byte a reader sees, off the read-only segments, is writable (W_gestures_end.v gse_writable_view) *)
Lemma xrf_writable_view : forall H (m : word -> option byte) a v, 0 <= a < 2 ^ 64 ->
  aview segs H m a = Some v -> ~ in_rom segs a -> writable_at segs (mrestrict H m) a.
Proof.
  intros H m a v Ha Hv Hn. unfold aview, mbyte in Hv. unfold writable_at, wview.
  destruct (mrestrict H m (Z_to_bv 64 a)) as [b|] eqn:Em; [discriminate|].
  unfold seg_rom, memory_read in Hv.
  destruct (find_segment segs (bv_unsigned (Z_to_bv 64 a)) (Z.of_N 1)) as [sg|] eqn:Ef; [|discriminate].
  change (Z.of_N 1) with 1 in Ef. rewrite Ef.
  destruct (seg_readable sg); [|discriminate].
  destruct (find_segment_hit _ _ _ _ Ef) as (Hin & Hlo & Hhi). rewrite unsigned_lit_small in Hlo, Hhi by lia.
  destruct (seg_writable sg) eqn:Ew.
  - destruct (segment_byte_at (seg_bytes sg) (Z.to_N (bv_unsigned (Z_to_bv 64 a) - Z.of_N (seg_base sg)))) eqn:Eb; [discriminate|].
    exfalso. change (N.to_nat 1) with 1%nat in Hv. cbn [segment_read_bytes] in Hv. rewrite Eb in Hv. cbn in Hv. discriminate Hv.
  - exfalso. apply Hn. exists sg. split; [exact Hin|]. split; [exact Ew | lia].
Qed.
(* a byte whose view is kept, off the read-only segments, is kept: writability is presence or a writable
   segment's file byte, and the latter does not depend on the memory *)
Lemma xrf_abyte_kept : forall (W W' : world segs) m m' a, 0 <= a < 2 ^ 64 ->
  aview segs (w_H W') m' a = aview segs (w_H W) m a -> ~ in_rom segs a -> abyte_kept W m W' m' a.
Proof.
  intros W W' m m' a Ha He Hr. split; [exact He|]. intros Hw. unfold arm in *.
  destruct (aview segs (w_H W) m a) as [v|] eqn:Ev.
  - exact (xrf_writable_view (w_H W') m' a v Ha He Hr).
  - unfold aview, mbyte in Ev.
    destruct (mrestrict (w_H W) m (Z_to_bv 64 a)) as [b|] eqn:Em; [cbn in Ev; discriminate Ev|].
    unfold writable_at, wview in Hw |- *. rewrite Em in Hw.
    destruct (mrestrict (w_H W') m' (Z_to_bv 64 a)); [discriminate | exact Hw].
Qed.
Lemma xrf_vm_aview : forall (W W' : world segs) mem mem' a n v,
  (forall x, a <= x < a + Z.of_nat n -> aview segs (w_H W') mem' x = aview segs (w_H W) mem x) ->
  val_mem segs (arm W mem) a n v -> val_mem segs (arm W' mem') a n v.
Proof.
  intros W W' mem mem' a n v HK Hv kk Hk. unfold arm.
  rewrite (mbyte_of_aview segs (w_H W) (w_H W') mem mem' (a + Z.of_nat kk)); [exact (Hv kk Hk)|].
  apply HK. lia.
Qed.
(* What a callee's journal keeps (W_gestures_end.v gse_keep_img / gse_keep_high / gse_keep_blk / gse_fp_spares /
   gse_nodup), and its frames clause *)
Lemma xrf_keep_img : forall G XO OUT STK sp0 FP ly S W mem md own ly' S' W' mem' md' k,
  ajournal_gx segs B G XO OUT STK sp0 FP ly S W mem md own ly' S' W' mem' md' k ->
  forall a, in_img segs a -> ~ Exists (in_zr a) (as_owned_static B) -> ~ (as_errno B <= a < as_errno B + 4) ->
  fp_spares FP a -> ~ inG G a -> aview segs (w_H W') mem' a = aview segs (w_H W) mem a.
Proof.
  intros G XO OUT STK sp0 FP ly S W mem md own ly' S' W' mem' md' k (HS0 & HX0 & (memS & HJi & Hag) & _) a Hi Ho He Hf Hg.
  pose proof HJi as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & F3 & _). rewrite (F3 a Hi Ho He Hf).
  pose proof (pa_segs_low a Hi) as HL.
  apply (aview_gagree segs G _ _ _ a Hag). apply inGb_false. rewrite unsigned_lit_small by (unfold kLowMemEnd in HL; lia). exact Hg.
Qed.
Lemma xrf_keep_high : forall G XO OUT STK sp0 FP ly S W mem md own ly' S' W' mem' md' k,
  gx_ok segs B G -> ajournal_gx segs B G XO OUT STK sp0 FP ly S W mem md own ly' S' W' mem' md' k ->
  forall a, alloc_ceiling <= a < 2 ^ 64 -> ~ (sp0 + XO - (STK + XO) <= a < sp0 + XO) ->
  aview segs (w_H W') mem' a = aview segs (w_H W) mem a.
Proof.
  intros G XO OUT STK sp0 FP ly S W mem md own ly' S' W' mem' md' k HGx (HS0 & HX0 & (memS & HJi & Hag) & _) a Ha Hno.
  pose proof HJi as (_ & _ & _ & _ & _ & _ & _ & _ & F1 & _). rewrite (F1 a Ha Hno).
  pose proof asan_consts as (C1 & _).
  apply (aview_gagree segs G _ _ _ a Hag). apply inGb_false. rewrite unsigned_lit_small by lia. intros HGa.
  pose proof (inG_low segs B pa_segs_low G a HGx HGa) as HL. unfold kLowMemEnd in HL. lia.
Qed.
Lemma xrf_keep_blk : forall G XO OUT STK sp0 FP ly S W mem md own ly' S' W' mem' md' k p n i,
  gx_ok segs B G -> ajournal_gx segs B G XO OUT STK sp0 FP ly S W mem md own ly' S' W' mem' md' k ->
  In (p, n) (ablocks B ly S) -> In (p, n) (ablocks B ly' S') -> 0 <= i < req_size n -> ~ inFP FP (p + i) ->
  aview segs (w_H W') mem' (p + i) = aview segs (w_H W) mem (p + i).
Proof.
  intros G XO OUT STK sp0 FP ly S W mem md own ly' S' W' mem' md' k p n i HGx (HS0 & HX0 & (memS & HJi & Hag) & _) H1 H2 Hi Hf.
  pose proof HJi as (HAR0 & _ & _ & _ & _ & _ & _ & _ & _ & F2 & _). rewrite (F2 p n i H1 H2 Hi Hf).
  apply (aview_gagree segs G _ _ _ (p + i) Hag). apply inGb_false. intros HGa.
  destruct (al_blocks _ _ LAWS ly' S' W' mem' md' p n HAR0 H2) as (_ & H4096 & Hc & _).
  pose proof asan_consts as (C1 & _).
  rewrite unsigned_lit_small in HGa by lia.
  destruct (HGx _ HGa) as [Hi' _].
  pose proof (blk_off_imgP B ly' S' W' mem' md' p n HAR0 H2) as Hoff.
  pose proof (pa_img_range _ Hi') as HR. red in Hoff. lia.
Qed.
Lemma xrf_keep_frm : forall G XO OUT STK sp0 FP ly S W mem md own ly' S' W' mem' md' k cid pos a,
  gx_ok segs B G -> ajournal_gx segs B G XO OUT STK sp0 FP ly S W mem md own ly' S' W' mem' md' k ->
  AR segs B ly S W mem md -> In (cid, pos) (frames S) ->
  (in_zr a (frame_rng ly (cid, pos)) \/ in_zr a (shadow_addr (frame_addr ly cid pos), fs_frame_bytes cid / 8)) ->
  ~ inFP FP a -> aview segs (w_H W') mem' a = aview segs (w_H W) mem a.
Proof.
  intros G XO OUT STK sp0 FP ly S W mem md own ly' S' W' mem' md' k cid pos a HGx (HS0 & HX0 & (memS & HJi & Hag) & _)
    HAR Hin Ha Hf.
  pose proof HJi as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & F4 & _). rewrite (F4 cid pos a Hin Ha Hf).
  destruct (frames_bounds segs B LAWS ly S W mem md cid pos HAR Hin) as (Hf0 & Hf1 & _).
  pose proof (xrf_frm_off_img ly S W mem md cid pos HAR Hin) as Hoff.
  pose proof (fs_frame_bytes_nonneg cid) as Hfb.
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  pose proof (Z.div_pos (frame_addr ly cid pos) 8 ltac:(lia) ltac:(lia)) as Hd0.
  pose proof (Z.div_le_upper_bound (frame_addr ly cid pos) 8 (2 ^ 47) ltac:(lia) ltac:(lia)) as Hd1.
  pose proof (Z.div_pos (fs_frame_bytes cid) 8 ltac:(lia) ltac:(lia)) as Hd2.
  pose proof (Z.div_le_upper_bound (fs_frame_bytes cid) 8 (fs_frame_bytes cid) ltac:(lia) ltac:(lia)) as Hd3.
  unfold frame_rng, in_zr, shadow_addr, SHADOW_OFF in Ha. cbn [fst snd] in Ha.
  assert (Ha64 : 0 <= a < 2 ^ 64) by lia.
  apply (aview_gagree segs G _ _ _ a Hag). apply inGb_false. rewrite unsigned_lit_small by lia. intros HGa.
  destruct (HGx _ HGa) as [Hi _]. pose proof (pa_img_range _ Hi) as HR. pose proof (pa_segs_low a Hi) as HL.
  unfold kLowMemEnd in HL. lia.
Qed.
Lemma xrf_fp_spares : forall bl a, (forall b, In b bl -> 4096 <= fst b) -> fp_spares (ablocks_fp bl) a.
Proof.
  intros bl a Hb Ho. exfalso. destruct Ho as (r & Hr & H0).
  unfold ablocks_fp in Hr. apply in_map_iff in Hr as (b & <- & Hin). cbn [fst snd] in H0. pose proof (Hb b Hin). lia.
Qed.
Lemma xrf_nodup : forall ly S W mem md, AR segs B ly S W mem md -> List.NoDup (ablocks B ly S).
Proof.
  intros ly S W mem md HAR. destruct (al_sep _ _ LAWS ly S W mem md HAR) as [Hp _]. apply pairwise_app_l in Hp as [Hp _].
  assert (Hpos : Forall (fun b => 0 < req_size (snd b)) (ablocks B ly S)).
  { apply Forall_forall. intros [p n] Hin. destruct (al_blocks _ _ LAWS ly S W mem md p n HAR Hin) as (_ & _ & _ & _ & _ & _ & Hn).
    cbn [snd]. pose proof (req_size_pos n ltac:(lia)). lia. }
  induction (ablocks B ly S) as [|b l IH]; [apply List.NoDup_nil|].
  cbn [map pairwise] in Hp. destruct Hp as [Hf Hp]. inversion Hpos as [|? ? Hb Hl]; subst.
  apply List.NoDup_cons; [|exact (IH Hp Hl)].
  intros Hin. rewrite Forall_forall in Hf. specialize (Hf (fst b, req_size (snd b)) (in_map _ _ _ Hin)).
  unfold zdisjoint in Hf. cbn [fst snd] in Hf. lia.
Qed.
Lemma xrf_nodup_app : forall (l1 l2 : list (Z * Z)) x, List.NoDup (l1 ++ l2) -> In x l1 -> In x l2 -> False.
Proof.
  induction l1 as [|y l1 IH]; intros l2 x Hn H1 H2; [destruct H1|].
  cbn [app] in Hn. inversion Hn as [|? ? Hy Hn']; subst.
  destruct H1 as [<- | H1]; [apply Hy; apply in_or_app; right; exact H2 | exact (IH l2 x Hn' H1 H2)].
Qed.
Definition xrf_peq (x y : Z * Z) : {x = y} + {x <> y}.
Proof. decide equality; apply Z.eq_dec. Defined.
Lemma xrf_inFP_blk : forall bl a, inFP (ablocks_fp bl) a -> exists p n, In (p, n) bl /\ p <= a < p + req_size n.
Proof.
  intros bl a (r & Hr & Ha). unfold ablocks_fp in Hr. apply in_map_iff in Hr as ([p n] & <- & Hin).
  exists p, n. split; [exact Hin | exact Ha].
Qed.
(* every block relay_finish's footprint names has a positive size *)
Lemma xrf_L_pos : forall ly S (W : world segs) mem G es c O mx no cap out b,
  arelay_at B fr_RG ly S W mem G es -> aout_at B fr_RG ly S W mem c O mx no cap out ->
  In b (rf_tblk G ++ rf_eblks es ++ aout_blks cap out) -> 0 < snd b.
Proof.
  intros ly S W mem G es c O mx no cap out b (R1 & R2 & R3 & R4 & R5 & R6 & R7 & R8 & R9 & R10 & R11) HO Hb.
  apply in_app_or in Hb as [Hb | Hb]; [|apply in_app_or in Hb as [Hb | Hb]].
  - unfold rf_tblk in Hb. destruct (G =? 0); [destruct Hb|]. destruct Hb as [<- | []]. cbn. unfold ATABLE. lia.
  - unfold rf_eblks in Hb. apply in_concat in Hb as (l & Hl & Hb). apply in_map_iff in Hl as (e & <- & He).
    rewrite Forall_forall in R10. pose proof (R10 e He) as (E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8 & E9 & E10 & E11 & E12 & E13 & E14 & E15).
    unfold aentry_blks in Hb. apply in_app_or in Hb as [Hb | Hb]; [|apply in_app_or in Hb as [Hb | Hb]].
    + destruct (re_cap e =? 0) eqn:Ec; [destruct Hb|]. destruct Hb as [<- | []]. apply Z.eqb_neq in Ec. cbn. lia.
    + destruct (re_hp e =? 0) eqn:Ez; [destruct Hb|]. destruct Hb as [<- | []]. apply Z.eqb_neq in Ez.
      destruct E12 as [(Hz & _) | (_ & _ & _ & Hk & _)]; [lia | cbn; lia].
    + apply in_map_iff in Hb as (kk & <- & _). cbn. lia.
  - unfold aout_blks in Hb. destruct (cap =? 0) eqn:Ec; [destruct Hb|]. destruct Hb as [<- | []]. apply Z.eqb_neq in Ec.
    pose proof HO as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HO26).
    cbn. destruct HO26 as [(Hc & _) | (Hc & _)]; lia.
Qed.
(* the source fields' footprint lies in the struct and its blocks (generic over what is kept) *)
Lemma xrf_alist_fp_in : forall (Q : Z -> Prop) ly S (W : world segs) mem LA l lines,
  alist_at B ly S W mem LA l lines ->
  (forall a, LA <= a < LA + 16 -> Q a) ->
  (forall b, In b (alist_blks l) -> forall a, fst b <= a < fst b + snd b -> Q a) ->
  forall r, In r (alist_fp LA l) -> forall a, fst r <= a < snd r -> Q a.
Proof.
  intros Q ly S W mem LA l lines (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9) HLA HB r Hr.
  unfold alist_fp in Hr. destruct Hr as [<- | Hr]; [exact HLA|].
  apply in_app_or in Hr as [Hr | Hr].
  - destruct (hl_cap l =? 0) eqn:Ec; [destruct Hr|]. destruct Hr as [<- | []].
    pose proof Ec as Ec0. apply Z.eqb_neq in Ec.
    destruct H6 as [(Hc & _) | (Hc & Hin & Hj & _)]; [lia|].
    intros a Ha. unfold gfp, bzs in Ha. cbn [fst snd] in Ha. rewrite length_map, length_app, xrf_len_text in Ha.
    unfold hl_n in Hj, H5.
    apply (HB (hl_v l, AREC * hl_cap l)); [unfold alist_blks; rewrite Ec0; left; reflexivity|]. cbn [fst snd].
    unfold AREC in *. lia.
  - apply in_map_iff in Hr as (rr & <- & Hrr).
    intros a Ha. unfold gfp, bzs in Ha. cbn [fst snd] in Ha. rewrite length_map, length_app in Ha. cbn [length] in Ha.
    apply (HB (fst rr, Z.of_nat (length (snd rr)) + 1)); [|cbn [fst snd]; lia].
    unfold alist_blks. apply in_or_app. right. apply in_map_iff. exists rr. split; [reflexivity | exact Hrr].
Qed.
Lemma xrf_asrc_fp_in : forall (Q : Z -> Prop) ly S (W : world segs) mem HA h,
  asrc_at B ly S W mem HA h ->
  (forall a, HA <= a < HA + ASRC -> Q a) ->
  (forall b, In b (asrc_blks h) -> forall a, fst b <= a < fst b + snd b -> Q a) ->
  forall r, In r (asrc_fp HA h) -> forall a, fst r <= a < snd r -> Q a.
Proof.
  intros Q ly S W mem HA h Hs HHA HB r Hr.
  pose proof Hs as (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11 & H12 & H13 & H14 & H15 & H16 & H17 & H18 &
    H19 & H20 & H21 & H22 & H23 & H24).
  unfold asrc_fp in Hr. destruct Hr as [<- | [<- | Hr]]; [exact HHA | |].
  - intros a Ha. unfold gfp, bzs in Ha. cbn [fst snd] in Ha. rewrite length_map, H19 in Ha.
    apply (HB (hs_partial h, APARTIAL)); [left; reflexivity | cbn [fst snd]; lia].
  - apply in_app_or in Hr as [Hr | Hr]; [|apply in_app_or in Hr as [Hr | Hr]].
    + apply (xrf_alist_fp_in Q ly S W mem (HA + 16) (hs_pending h) false H10); [| |exact Hr].
      * intros a Ha. apply HHA. unfold ASRC. lia.
      * intros b Hb. apply HB. unfold asrc_blks. right. apply in_or_app. left. exact Hb.
    + apply (xrf_alist_fp_in Q ly S W mem (HA + 64) (hs_expected h) true H22); [| |exact Hr].
      * intros a Ha. apply HHA. unfold ASRC. lia.
      * intros b Hb. apply HB. unfold asrc_blks. right. apply in_or_app. right. apply in_or_app. left. exact Hb.
    + apply (xrf_alist_fp_in Q ly S W mem (HA + 80) (hs_held h) true H23); [| |exact Hr].
      * intros a Ha. apply HHA. unfold ASRC. lia.
      * intros b Hb. apply HB. unfold asrc_blks. right. apply in_or_app. right. apply in_or_app. right. exact Hb.
Qed.
Lemma xrf_slot_in : forall (hs : list (option hsrc)) i h, (i < length hs)%nat -> nth i hs None = Some h ->
  forall b, In b (asrc_blks h) -> In b (concat (map slot_blks hs)).
Proof.
  intros hs i h Hi Eh b Hb. apply in_concat. exists (slot_blks (Some h)). split; [|exact Hb].
  apply in_map. rewrite <- Eh. apply nth_In. exact Hi.
Qed.
(* the live blocks, rearranged: relay_finish's (table, entries, buffer) first *)
Lemma xrf_perm : forall (t : Z * Z) e s a i r,
  Permutation (i ++ (t :: e ++ s ++ a) ++ r) ([t] ++ e ++ a ++ (i ++ s ++ r)).
Proof.
  intros t e s a i r. cbn [app].
  eapply Permutation_trans; [apply Permutation_app_comm|]. cbn [app]. apply perm_skip.
  rewrite <- !app_assoc. apply Permutation_app_head.
  eapply Permutation_trans; [apply Permutation_app_comm|]. rewrite <- !app_assoc. apply Permutation_app_head.
  eapply Permutation_trans; [apply Permutation_app_comm|]. rewrite <- !app_assoc. apply Permutation_refl.
Qed.

(* ------------------------------------------------------------------ the two instructions, to relay_finish's entry *)
Definition xrf_rnout : YP09.region := YP09.mkRegion (Some 26%nat) (-1892) (-1884) (-1892) (-1884) [].
Definition xrf_facts : facts := mkFacts [ (26%nat, mkAF HI_G_NOUT HI_G_NOUT 0); (32%nat, mkAF SB SB 0) ] [] [].
Definition xrf_ss (pc : Z) : sstate := mkSS pc sr_atoms [xrf_rnout] None xrf_facts.
Definition xrf_extra : list word := map (Z_to_bv 64) [SB].
Definition xrf_Bx : sv := SOff 32 0.
Definition xrf_Bspan : Z * Z := (SB, SB + 2 ^ 44 - 1).
(* every register but ra, which the jal sets *)
Definition xrf_kept : list (bv 5) :=
  [2; 3; 4; 5; 6; 7; 8; 9; 10; 11; 12; 13; 14; 15; 16; 17; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%bv.
Lemma xrf_entry : forall (W : world segs) regs mem pc,
  getr regs 26 = w64 HI_G_NOUT -> awr W mem (rg_nout fr_RG) 8 ->
  st_ok_pi segs VAL (Eimg (Ereg regs xrf_extra)) (xrf_ss pc)
    (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + pc)) mem (seg_rom segs)))
  /\ sh_ok segs xrf_Bx [] (Eimg (Ereg regs xrf_extra)) (mrestrict (w_H W) mem).
Proof.
  intros W regs mem pc R26 AWN. rewrite restrict_mkst_fx.
  set (E := Eimg (Ereg regs xrf_extra)).
  assert (E26 : ew E 26 = Z_to_bv 64 HI_G_NOUT)
    by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 26 26%bv eq_refl); exact R26).
  assert (E32 : ew E 32 = Z_to_bv 64 SB)
    by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
  split.
  - unfold xrf_ss. apply pa_entry_st_ok_full.
    + apply regs_ok_Eimg_Ereg.
    + vm_compute. reflexivity.
    + apply Forall_cons; [|apply Forall_nil]. unfold region_ok, xrf_rnout.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks YP09.base_val].
      rewrite E26, unsigned_lit_small by (unfold HI_G_NOUT; lia). split; [unfold HI_G_NOUT; lia|].
      split; [unfold HI_G_NOUT; lia|]. split; [|constructor].
      intros o Ho. replace (HI_G_NOUT + o) with (rg_nout fr_RG + (o + 1892)) by (cbn; unfold HI_G_NOUT; lia).
      apply AWN. lia.
    + cbn. repeat split.
    + split; [|split; [exact I | exact I]].
      cbn [xrf_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
      rewrite E26, E32, !unsigned_lit_small by (unfold HI_G_NOUT, SB; lia).
      rewrite !Z.pow_0_r, !Z.mod_1_r. unfold HI_G_NOUT, SB. repeat match goal with |- _ /\ _ => split end; lia.
  - unfold sh_ok. constructor.
Qed.
Lemma xrf_frame_nout : forall E rs (m m' : word -> option byte),
  frame_of E rs m m' -> (forall a, in_wrange E rs a -> rg_nout fr_RG <= a < rg_nout fr_RG + 8) ->
  forall x : word, ~ (rg_nout fr_RG <= bv_unsigned x < rg_nout fr_RG + 8) -> m' x = m x.
Proof. intros E rs m m' HF Hw x Hx. apply HF. intros Hin. apply Hx. apply Hw. exact Hin. Qed.
Lemma xrf_Gnout : forall a, rg_nout fr_RG <= a < rg_nout fr_RG + 8 -> inG G_fr a.
Proof.
  intros a Ha. apply HG_SL. unfold G_SL. apply inG_cons. right. apply inG_cons. right. apply inG_cons. left.
  unfold in_zr. cbn [fst snd]. exact Ha.
Qed.
(* writes of the run: g_nout's 8 bytes only *)
Ltac xrf_wr E26 :=
  let a := fresh "a" in let r := fresh "r" in let Hin := fresh "Hin" in let Hr := fresh "Hr" in
  intros a (r & Hin & Hr); vm_compute in Hin;
  repeat (destruct Hin as [<- | Hin]; [cbn [YP09.r_base YP09.r_wlo YP09.r_whi YP09.base_val] in Hr;
    first [ lia
          | rewrite ?ew_ewset_other in Hr by lia; rewrite E26, unsigned_lit_small in Hr by (unfold HI_G_NOUT; lia);
            cbn; unfold HI_G_NOUT in Hr; lia ] |]);
  destruct Hin.
Ltac xrf_awr E26 :=
  lazymatch goal with |- awr_ok_x ?Ev ?rs ?G ?XO ?OUT ?STK ?sp0 ?FP ?b0 ?bc ?ly ?own =>
    let rs' := eval vm_compute in rs in change (awr_ok_x Ev rs' G XO OUT STK sp0 FP b0 bc ly own) end;
  repeat first
   [ apply awr_ok_x_nil
   | apply awr_ok_x_cons; [let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha;
       cbn [YP09.r_base YP09.r_wlo YP09.r_whi YP09.base_val] in Ha;
       first [ lia
             | right; left; apply xrf_Gnout; rewrite ?ew_ewset_other in Ha by lia;
               rewrite E26, unsigned_lit_small in Ha by (unfold HI_G_NOUT; lia); cbn; unfold HI_G_NOUT in Ha; lia ] |] ].
Ltac xrf_run_body E26 HS HJ SHOK HAE :=
  paj_run_to_tok RUNTO HS HJ SHOK xrf_Bspan AF_fr_relay_finish;
  [ xrf_awr E26 |];
  lazymatch goal with HFx : frame_of _ _ (mrestrict _ ?mem0) (mrestrict _ (ms_mem ?ms1)) |- _ =>
    let MEQ := fresh "MEQ" in
    assert (MEQ : forall x : word, ~ (rg_nout fr_RG <= bv_unsigned x < rg_nout fr_RG + 8) ->
        mrestrict (w_H _) (ms_mem ms1) x = mrestrict (w_H _) mem0 x)
      by (apply (xrf_frame_nout _ _ _ _ HFx); xrf_wr E26) end;
  lazymatch goal with H : mem_grows (mrestrict _ ?mem0) (mrestrict _ (ms_mem _)) |- _ =>
    let MG := fresh "MG" in rename H into MG end;
  repeat match goal with H : frame_of _ _ _ _ |- _ => clear H end;
  let KR := fresh "KR" in
  pose proof (regs_kept_of_st_ok_pi _ _ _ _ _ xrf_kept HS HAE ltac:(vm_compute; reflexivity)) as KR;
  cbn [ms_regs restrict] in KR;
  let Q1 := fresh "Q1" in prreg HS (1%bv : bv 5) Q1;
  lazymatch type of HS with st_ok_pi ?sg ?vl ?Ev ?ss (restrict ?H ?ms) =>
    let r := eval vm_compute in (nth 0 (ss_mem ss) xrf_rnout) in
    let HRN := fresh "HRN" in let HN0 := fresh "HN0" in
    pose proof (st_ok_pi_region_nth Ev ss (restrict H ms) 0 r HS ltac:(vm_compute; reflexivity)) as HRN;
    cbn [ms_mem restrict] in HRN;
    pose proof (field_of_region Ev _ 26 HI_G_NOUT _ _ _ _ _ (-1892) 8 (SLit 0) 0 HRN
      ltac:(rewrite ?ew_ewset_other by lia; rewrite E26; apply unsigned_lit_small; unfold HI_G_NOUT; lia)
      ltac:(left; reflexivity) eq_refl ltac:(lia) ltac:(lia)) as HN0;
    change (HI_G_NOUT + -1892) with (rg_nout fr_RG) in HN0; change (N.to_nat 8) with 8%nat in HN0; clear HRN
  end;
  pmkst HS;
  apply SRr_ret; split; [reflexivity|];
  lazymatch goal with |- exists _ _ _, {| cfg_ms := mkst ?r _ ?mm _; cfg_model := ?d |} = _ /\ _ =>
    exists r, mm, d end;
  split; [reflexivity|];
  split; [rewrite Q1; f_equal; unfold AX_join, AX_noord, AF_fr_LLVMFuzzerTestOneInput; lia|];
  split; [exact KR|];
  split; [rewrite ?wvb_collapse in HJ; exact HJ|];
  split; [assumption|]; split; [assumption | assumption].
Lemma xrf_to_rf : forall pcj (W : world segs) regs mem md STK sp0 FP ly S W0 mem0 md0 own ly3 S3 k,
  pcj = AX_join \/ pcj = AX_noord ->
  ajournal_gx segs B G_fr 0 [] STK sp0 FP ly S W0 mem0 md0 own ly3 S3 W mem md k ->
  getr regs 26 = w64 HI_G_NOUT -> awr W mem (rg_nout fr_RG) 8 ->
  SRr segs W (cfg_at segs (fr_B0 + pcj) regs mem md) (fun W' c' => W' = W /\ exists regs1 mem1 md1,
    c' = cfg_at segs (BASE + AF_fr_relay_finish) regs1 mem1 md1 /\
    getr regs1 1 = Z_to_bv 64 (BASE + (pcj + 8)) /\
    (forall r, In r xrf_kept -> getr regs1 r = getr regs r) /\
    ajournal_gx segs B G_fr 0 [] STK sp0 FP ly S W0 mem0 md0 own ly3 S3 W mem1 md1 k /\
    (forall x : word, ~ (rg_nout fr_RG <= bv_unsigned x < rg_nout fr_RG + 8) ->
       mrestrict (w_H W) mem1 x = mrestrict (w_H W) mem x) /\
    mem_grows (mrestrict (w_H W) mem) (mrestrict (w_H W) mem1) /\
    val_mem segs (arm W mem1) (rg_nout fr_RG) 8 0).
Proof.
  intros pcj W regs mem md STK sp0 FP ly S W0 mem0 md0 own ly3 S3 k Hpcj HJ R26 AWN.
  destruct (xrf_entry W regs mem pcj R26 AWN) as [HS SHOK].
  remember (Eimg (Ereg regs xrf_extra)) as E eqn:HE.
  assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
  assert (HAE : env_agree 32 (Ereg regs xrf_extra) E)
    by (rewrite HE; split; [intros q Hq; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
  assert (E26 : ew E 26 = Z_to_bv 64 HI_G_NOUT)
    by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 26 26%bv eq_refl); exact R26).
  clear HE.
  pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
  unfold cfg_at. rewrite <- BASE_B0. change (w64 (BASE + pcj)) with (Z_to_bv 64 (BASE + pcj)).
  destruct Hpcj as [-> | ->]; unfold xrf_ss in HS; xrf_run_body E26 HS HJ SHOK HAE.
Qed.

(* a callee-saved register across the call *)
Lemma xrf_pres : forall regs regs' (r : bv 5), aregs_preserved regs regs' -> acallee_saved (bv_unsigned r) ->
  getr regs' r = getr regs r.
Proof. intros regs regs' r HP Hr. pose proof (HP _ Hr) as H. rewrite !Z_to_bv_bv_unsigned in H. exact H. Qed.
Ltac xrf_cs := unfold acallee_saved;
  match goal with |- context [bv_unsigned ?r] => let v := eval vm_compute in (bv_unsigned r) in
    change (bv_unsigned r) with v end; lia.

(* ------------------------------------------------------------------ the site, both call sites in one lemma
   (lib/B/W_bx_defs.v lx_rf_site_S; relay_finish's spec RFg is applied once, below, for both sites) *)
Lemma lx_rf_site : lx_rf_site_S B MT XM_LIB RLO RHI fr_live_pre G_fr fr_FP LS.
Proof.
  unfold lx_rf_site_S.
  intros cx pcj t W regs mem md ly3 S3 fpos k m HB Hpcj HJ HFR HFL HMOD HIN HRV HJT HSEP HLS HR HAT.
  pose proof HR as (R2 & R8 & R9 & R18 & R26 & R27 & R3 & R4 & Rk).
  pose proof HMOD as (_ & _ & _ & Hout & _).
  pose proof Hout as (O1 & O2 & O3 & O4 & _).
  pose proof xrf_errno_lo as HE0. pose proof (proj2 XRF_ERRNO) as HE1.
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
  (* the two instructions *)
  eapply SRr_bind; [exact (xrf_to_rf pcj W regs mem md _ _ _ _ _ _ _ _ _ _ _ _ Hpcj HJ R26 O4)|].
  intros W1 c1 _ (-> & regs1 & mem1 & md1 & -> & Q1 & KR & HJ1 & MEQ & MG & HN0).
  (* the cut facts across the store *)
  pose proof (ajournal_gx_AR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as HAR.
  pose proof (ajournal_gx_AR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ1) as HAR1.
  destruct (ajournal_gx_inner _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as (memS0 & HJi0 & _).
  pose proof HJi0 as (_ & _ & _ & _ & _ & Hfrs & _ & _ & _ & _ & _ & _ & Hfreed & _).
  pose proof HB as (HAI & HPRE & Hra & Ha0 & Ha1 & Hblk0 & Hlen & Hgarr & Hfr0 & _).
  assert (Hfp : In (1, fpos) (frames S3)) by (rewrite Hfrs; left; reflexivity).
  assert (HFRS3 : frames S3 = [(1, fpos)]) by (rewrite Hfrs, Hfr0; reflexivity).
  destruct (xrf_store_kept cx ly3 S3 W mem md mem1 fpos m HB HAR Hfp MEQ MG HN0 HFR HMOD HIN HRV HJT)
    as (HFR1 & HMOD1 & HIN1 & HRV1 & HJT1).
  pose proof (xrf_store_flag ly3 S3 W mem md mem1 fpos HAR Hfp MEQ MG HFL) as HFL1.
  pose proof HMOD1 as (Hhs1 & Hslots1 & Hrel1 & Hout1 & Hgone1 & Hlock1 & Hwake1 & Hnfd1 & Hnfdw1 & Hnfdr1 & Htu1 &
    Hlst1 & Hlstw1).
  cbn [lm_hs lm_G lm_es lm_c lm_O lm_mx lm_cap lm_out lm_gn lm_nfd xrf_clear_O] in Hhs1, Hslots1, Hrel1, Hout1,
    Hgone1, Hnfd1, Hnfdr1.
  (* the frame's numbers *)
  pose proof HPRE as (HAR0 & Hra0 & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
  pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
  pose proof (Z.mod_pos_bound (spZ (c_regs cx) - 320) 32 ltac:(lia)) as HFm.
  assert (HFb : spZ (c_regs cx) - 351 <= lf_F cx <= spZ (c_regs cx) - 320) by (unfold lf_F; lia).
  assert (HFlo : alloc_ceiling + 32000 <= lf_F cx) by (unfold LLVMF_STK in *; lia).
  assert (HF32 : lf_F cx mod 32 = 0).
  { unfold lf_F. set (x := spZ (c_regs cx) - 320).
    assert (Hq : x - x mod 32 = 32 * (x / 32)) by (pose proof (Z.div_mod x 32 ltac:(lia)); lia).
    rewrite Hq, Z.mul_comm. apply Z_mod_mult. }
  assert (Hsp1 : spZ regs1 = lf_F cx).
  { unfold spZ. rewrite (KR 2%bv ltac:(cbv; tauto)), R2. unfold w64. apply unsigned_lit_small. lia. }
  assert (Hpc8 : 0 <= pcj + 8 < 2 ^ 40 /\ (pcj + 8) mod 2 = 0)
    by (destruct Hpcj as [-> | ->]; (unfold AX_join, AX_noord, AF_fr_LLVMFuzzerTestOneInput; split; [lia | reflexivity])).
  assert (HSTKv : RF_STK = 16672) by reflexivity.
  (* relay_finish's afn_pre at sp = F *)
  destruct (lx_afn_pre_at B MT XM_LIB RLO RHI fr_live_pre G_fr fr_FP HG cx ly3 S3 fpos k W mem1 md1 regs1 RF_STK HB HJ1
    (bx_frame_of_aframe _ _ _ _ HFR1) Hsp1) as (ch & HPREc).
  { rewrite Q1. apply ret_ok_codeptr_v; lia. }
  { unfold raZ. rewrite Q1, unsigned_lit_small by lia. lia. }
  { rewrite (KR 3%bv ltac:(cbv; tauto)). exact R3. }
  { rewrite (KR 4%bv ltac:(cbv; tauto)). exact R4. }
  { rewrite (KR 8%bv ltac:(cbv; tauto)). exact R8. }
  { lia. }
  { unfold LLVMF_STK. lia. }
  (* the blocks: relay_finish's three kinds first, then the rest Rr *)
  destruct HSEP as ((rest0 & HP0) & HSEP2).
  pose proof Hrel1 as (Rr1 & Rr2 & Rr3 & Rr4 & Rr5 & Rr6 & Rr7 & Rr8 & Rr9 & Rr10 & Rr11).
  destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR1 Rr8) as (_ & HT4096 & _).
  assert (HTB : rf_tblk (lm_G m) = [(lm_G m, ATABLE)])
    by (unfold rf_tblk; destruct (Z.eqb_spec (lm_G m) 0); [lia | reflexivity]).
  set (Rr := input_blks cx ++ concat (map slot_blks (lm_hs m)) ++ rest0).
  set (L := rf_tblk (lm_G m) ++ rf_eblks (lm_es m) ++ aout_blks (lm_cap m) (lm_out m)).
  assert (HPRF : Permutation (ablocks B ly3 S3) (L ++ Rr)).
  { eapply Permutation_trans; [exact HP0|]. unfold L, Rr. rewrite HTB. unfold model_blks, rf_eblks.
    rewrite <- !app_assoc. apply xrf_perm. }
  assert (HND3 : List.NoDup (L ++ Rr)) by exact (Permutation_NoDup HPRF (xrf_nodup _ _ _ _ _ HAR1)).
  assert (HL3 : forall b, In b L -> In b (ablocks B ly3 S3))
    by (intros b Hb; apply (Permutation_in _ (Permutation_sym HPRF)); apply in_or_app; left; exact Hb).
  assert (HR3 : forall b, In b Rr -> In b (ablocks B ly3 S3))
    by (intros b Hb; apply (Permutation_in _ (Permutation_sym HPRF)); apply in_or_app; right; exact Hb).
  assert (HLM : forall b, In b L -> In b (model_blks m)).
  { intros b Hb. unfold L in Hb. rewrite HTB in Hb. unfold model_blks, rf_eblks.
    destruct Hb as [<- | Hb]; [left; reflexivity|]. right. cbn [app] in Hb.
    apply in_app_or in Hb as [Hb | Hb]; apply in_or_app; [left; exact Hb|]. right. apply in_or_app. right. exact Hb. }
  (* relay_finish *)
  eapply SRr_bind.
  { apply (RFg W ly3 S3 regs1 mem1 md1 ch (lm_G m) (lm_es m) (lm_c m) [] (lm_mx m) 0 (lm_cap m) (lm_out m) Rr HPREc).
    - rewrite Hsp1. exact HF32.
    - rewrite HFRS3. reflexivity.
    - exact Htu1.
    - exact Hlock1.
    - right. exact Hrel1.
    - exact Hlst1.
    - exact Hlstw1.
    - exact Hout1.
    - unfold L in HPRF. rewrite <- !app_assoc in HPRF. exact HPRF.
    - exact (XRF_END5 W mem1 HRV1).
    - exact HRV1.
    - intros a Ha. apply inG_app. left. exact Ha.
    - intros a Ha. apply inG_app. right. exact Ha.
    - intros a Ha He. unfold RF_G in Ha.
      repeat (apply inG_cons in Ha as [Ha | Ha]; [unfold in_zr, AG_LISTEN in Ha; cbn in Ha; lia |]).
      exact (inG_nil a Ha).
    - apply xrf_room_eq. exact (LS_rf_room cx t m ly3 S3 HLS).
    - (* relay_finish's own free returns at entry + 200 = 0x8240c, the one-entry trace K0's free table holds
         (lib/B/YCk0.v CTX_AFREE row [0x8240c]; the edge (CTX_relay_finish, 0x8240c, CTX_AFREE, K0Lit)) *)
      assert (E200 : BASE + AF_fr_relay_finish + 200 = 0x8240c) by (vm_compute; reflexivity).
      rewrite E200. unfold YCk0.CTX_AFREE. cbn [In]. repeat first [left; reflexivity | right].
    - rewrite <- xrf_cost_eq. exact (LS_rf_mok cx t m ly3 S3 HLS). }
  intros W2 c2 _ (ly' & S' & regs' & mem' & md' & k' & out' & -> & HJc & HPR & HPK & HFRM & HMO & HPERM & HOUT &
    HLOCK & HRA & HGL & HGLw).
  rewrite Hsp1 in HJc.
  fold xrf_G in HJc.
  unfold rf_FP in HJc. fold L in HJc.
  rewrite HTB in HPERM.
  set (R := rf_run (lm_c m) [] (lm_mx m) 0 (lm_cap m) (lm_es m)) in *.
  pose proof (ajournal_gx_AR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJc) as HAR2.
  assert (HR2 : forall b, In b Rr -> In b (ablocks B ly' S'))
    by (intros b Hb; apply (Permutation_in _ (Permutation_sym HPERM)); right; cbn [app]; apply in_or_app; right; exact Hb).
  assert (HND2 : List.NoDup ([(lm_G m, ATABLE)] ++ aout_blks (gse_cap R) out' ++ Rr))
    by exact (Permutation_NoDup HPERM (xrf_nodup _ _ _ _ _ HAR2)).
  (* what the call keeps *)
  assert (HL4096 : forall b, In b L -> 4096 <= fst b).
  { intros [p n] Hb. destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR1 (HL3 _ Hb)) as (_ & H4 & _). exact H4. }
  assert (KIMG : forall a, inG G_fr a -> ~ inG xrf_G a -> a < 0x5d90c8 -> abyte_kept W mem1 W2 mem' a).
  { intros a HGa HnR Hlt. destruct (HG a HGa) as (Hi & Ho & _). pose proof (pa_segs_low a Hi) as HL.
    apply xrf_abyte_kept.
    - unfold kLowMemEnd in HL. lia.
    - apply (xrf_keep_img _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJc a Hi Ho); [lia | apply xrf_fp_spares; exact HL4096 | exact HnR].
    - intros Hro. exact (proj1 (XRF_ROM_OUT a Hro) HGa). }
  assert (KHIGH : forall a, lf_F cx <= a < 2 ^ 64 -> abyte_kept W mem1 W2 mem' a).
  { intros a Ha. apply xrf_abyte_kept; [lia | |].
    - apply (xrf_keep_high _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ xrf_G_ok HJc a); lia.
    - intros (sg & Hsg & _ & Hr). pose proof (pa_segs_low a (ex_intro _ sg (conj Hsg Hr))) as HL.
      unfold kLowMemEnd in HL. lia. }
  assert (HnFP : forall p n i, In (p, n) Rr -> 0 <= i < req_size n -> ~ inFP (ablocks_fp L) (p + i)).
  { intros p n i Hb Hi Hf. destruct (xrf_inFP_blk L (p + i) Hf) as (p' & n' & Hb' & Ha').
    assert (Hne : (p', n') <> (p, n)) by (intros E; rewrite E in Hb'; exact (xrf_nodup_app L Rr (p, n) HND3 Hb' Hb)).
    pose proof (sep_blocks segs B LAWS ly3 S3 W mem1 md1 p' n' p n HAR1 (HL3 _ Hb') (HR3 _ Hb) Hne) as Hd.
    unfold zdisjoint in Hd. cbn [fst snd] in Hd. lia. }
  assert (KB : forall b, In b Rr -> forall a, fst b <= a < fst b + snd b -> abyte_kept W mem1 W2 mem' a).
  { intros [p n] Hb a Ha. cbn [fst snd] in Ha.
    destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR1 (HR3 _ Hb)) as (_ & Hp4 & Hpc & _ & _ & _ & Hn).
    pose proof (req_size_pos n ltac:(lia)) as [_ Hq].
    pose proof (blk_off_imgP B _ _ _ _ _ _ _ HAR1 (HR3 _ Hb)) as Hoff. red in Hoff.
    replace a with (p + (a - p)) by lia.
    apply xrf_abyte_kept; [lia | |].
    - apply (xrf_keep_blk _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ p n (a - p) xrf_G_ok HJc (HR3 _ Hb) (HR2 _ Hb));
        [lia | apply (HnFP p n); [exact Hb | lia]].
    - intros (sg & Hsg & _ & Hr). pose proof (pa_img_range _ (ex_intro _ sg (conj Hsg Hr))) as HIR. lia. }
  assert (HFF := frames_bounds segs B LAWS ly3 S3 W mem1 md1 1 fpos HAR1 Hfp).
  destruct HFF as (HFF0 & HFF1 & HFFa).
  change (fs_frame_bytes 1) with 128 in HFF1, HFFa.
  assert (KFRM : forall a, (frame_addr ly3 1 fpos <= a < frame_addr ly3 1 fpos + 128 \/
      SB + frame_addr ly3 1 fpos / 8 <= a < SB + frame_addr ly3 1 fpos / 8 + 16) -> abyte_kept W mem1 W2 mem' a).
  { intros a Ha.
    pose proof (Z.div_pos (frame_addr ly3 1 fpos) 8 ltac:(lia) ltac:(lia)) as Hd0.
    pose proof (Z.div_le_upper_bound (frame_addr ly3 1 fpos) 8 0xfffffff0000 ltac:(lia) ltac:(lia)) as Hd1.
    assert (Hd2 : 512 <= frame_addr ly3 1 fpos / 8) by (apply Z.div_le_lower_bound; lia).
    pose proof (xrf_frm_off_img _ _ _ _ _ _ _ HAR1 Hfp) as Hoff. change (fs_frame_bytes 1) with 128 in Hoff.
    apply xrf_abyte_kept; [unfold SB in Ha; lia | |].
    - apply (xrf_keep_frm _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ 1 fpos a xrf_G_ok HJc HAR1 Hfp).
      + unfold frame_rng, in_zr, shadow_addr, SHADOW_OFF. cbn [fst snd]. change (fs_frame_bytes 1 / 8) with 16.
        change (fs_frame_bytes 1) with 128. unfold SB in Ha.
        destruct Ha as [Ha | Ha]; [left | right]; lia.
      + intros Hf. destruct (xrf_inFP_blk L a Hf) as (p' & n' & Hb' & Ha').
        destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR1 (HL3 _ Hb')) as (_ & Hp4 & Hpc & Happ & _).
        pose proof (sep_block_frame segs B LAWS ly3 S3 W mem1 md1 p' n' 1 fpos HAR1 (HL3 _ Hb') Hfp) as Hd.
        unfold zdisjoint in Hd. cbn [fst snd] in Hd. change (fs_frame_bytes 1) with 128 in Hd.
        unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Happ. unfold SB in Ha.
        destruct Ha as [Ha | Ha]; lia.
    - intros (sg & Hsg & _ & Hr). pose proof (pa_segs_low a (ex_intro _ sg (conj Hsg Hr))) as HL.
      pose proof (pa_img_range _ (ex_intro _ sg (conj Hsg Hr))) as HIR.
      unfold kLowMemEnd in HL. unfold SB in Ha. destruct Ha as [Ha | Ha]; lia. }
  (* the journal from the entry *)
  assert (HJc' : ajournal_gx segs B G_fr 0 [] RF_STK (lf_F cx) (ablocks_fp L) ly3 S3 W mem1 md1 [] ly' S' W2 mem' md' k')
    by exact (ajournal_gx_G_mono segs B xrf_G G_fr 0 [] RF_STK (lf_F cx) (ablocks_fp L) ly3 S3 W mem1 md1 [] ly' S' W2 mem' md'
      k' xrf_G_sub HJc).
  assert (HJ2 : ajournal_gx segs B G_fr 0 [] LLVMF_STK (spZ (c_regs cx)) (lf_FP fr_FP cx)
      (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx) ([] ++ [(1, fpos)]) ly' S' W2 mem' md' (k + k')).
  { apply (ajournal_gx_sub segs B LAWS pa_segs_low G_fr LLVMF_STK (spZ (c_regs cx)) 0 [] (lf_FP fr_FP cx)
      (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx) [(1, fpos)] ly3 S3 W mem1 md1 k
      RF_STK (lf_F cx) 0 [] (ablocks_fp L) [] ly' S' W2 mem' md' k' HJ1 HJc');
      [unfold LLVMF_STK; lia | lia | lia | intros a Ha; exfalso; exact (inFP_nil a Ha) | exact HG |].
    intros a Hf. destruct (xrf_inFP_blk L a Hf) as (p & n & Hb & Ha).
    pose proof (xrf_L_pos _ _ _ _ _ _ _ _ _ _ _ _ (p, n) Hrel1 Hout1 Hb) as Hpos. cbn [snd] in Hpos.
    unfold req_size in Ha. destruct (Z.eqb_spec n 0) as [Hn0 | _]; [lia|].
    destruct (HSEP2 (p, n) (HLM _ Hb)) as [Hne | Hin].
    - right. exists p, n. split; [exact (HL3 _ Hb)|]. split; [exact Hne|]. unfold req_size.
      destruct (Z.eqb_spec n 0); [lia | exact Ha].
    - left. split; [apply Hin; cbn [fst snd]; unfold req_size; destruct (Z.eqb_spec n 0); [lia | exact Ha]|].
      exists p, n. split; [exact (HL3 _ Hb)|].
      unfold req_size. destruct (Z.eqb_spec n 0); [lia | exact Ha]. }
  cbn [app] in HJ2.
  (* the frame address *)
  assert (HFA : frame_addr ly' 1 fpos = frame_addr ly3 1 fpos).
  { destruct (ajournal_gx_inner _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJc) as (memSc & HJic & _).
    pose proof HJic as (_ & Hly & _). destruct Hly as (_ & _ & _ & _ & _ & EF & _). unfold frame_addr. rewrite EF.
    reflexivity. }
  (* the stream after: g_nout = |O| *)
  pose proof HOUT as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
    HOno & _).
  (* the post *)
  apply SRr_ret.
  exists ly', S', regs', mem', md', (k + k'),
    (LM (lm_k m) (lm_hs m) (lm_G m) [] (lx_rf_ctl (gse_c R)) (gse_O R) (lm_mx m) (gse_cap R) out' (lm_gn m) (lm_nfd m)).
  cbn [lm_k lm_hs lm_G lm_es lm_c lm_O lm_mx lm_cap lm_out lm_gn lm_nfd].
  assert (HPM : Permutation (ablocks B ly' S') (input_blks cx ++
      model_blks (LM (lm_k m) (lm_hs m) (lm_G m) [] (lx_rf_ctl (gse_c R)) (gse_O R) (lm_mx m) (gse_cap R) out'
        (lm_gn m) (lm_nfd m)) ++ rest0)).
  { eapply Permutation_trans; [exact HPERM|]. apply Permutation_sym. unfold model_blks. cbn [lm_G lm_es lm_hs lm_cap lm_out].
    exact (xrf_perm (lm_G m, ATABLE) [] (concat (map slot_blks (lm_hs m))) (aout_blks (gse_cap R) out') (input_blks cx) rest0). }
  split.
  { (* the configuration *)
    unfold cfg_at, w64. rewrite Q1, BASE_B0, Z.add_assoc. reflexivity. }
  split; [exact HJ2|].
  split.
  { (* the frame and the fake frame *)
    rewrite HFA.
    unfold aframe_at in HFR1 |- *. cbv zeta in HFR1 |- *.
    destruct HFR1 as (FS & FW & F32 & F40 & F48 & F56 & F64 & F72 & F80 & F96 & F104 & F120 & F128 & F136 & F152 &
      F184 & FF0 & FF8 & FF16 & FFw & FFsh & FFshw).
    unfold sv8 in *.
    assert (KV : forall a v, lf_F cx <= a -> a + 8 <= spZ (c_regs cx) ->
      val_mem segs (arm W mem1) a 8 v -> val_mem segs (arm W2 mem') a 8 v)
      by (intros a v H1 H2 Hv; apply (akept_vm W mem1); [intros x Hx; apply KHIGH; lia | exact Hv]).
    assert (KF : forall a v, frame_addr ly3 1 fpos <= a -> a + 8 <= frame_addr ly3 1 fpos + 128 ->
      val_mem segs (arm W mem1) a 8 v -> val_mem segs (arm W2 mem') a 8 v)
      by (intros a v H1 H2 Hv; apply (akept_vm W mem1); [intros x Hx; apply KFRM; left; lia | exact Hv]).
    split.
    { intros o r Hor. assert (Ho : 8 <= o <= 104).
      { unfold saved_regs in Hor. cbn [In] in Hor.
        repeat (destruct Hor as [Hor | Hor]; [injection Hor as <- _; lia |]). destruct Hor. }
      apply KV; [lia | lia | exact (FS o r Hor)]. }
    split; [apply (akept_awr W mem1); [intros x Hx; apply KHIGH; lia | exact FW]|].
    split; [apply KV; [lia | lia | exact F32]|]. split; [apply KV; [lia | lia | exact F40]|].
    split; [apply KV; [lia | lia | exact F48]|]. split; [apply KV; [lia | lia | exact F56]|].
    split; [apply KV; [lia | lia | exact F64]|]. split; [apply KV; [lia | lia | exact F72]|].
    split; [apply KV; [lia | lia | exact F80]|]. split; [apply KV; [lia | lia | exact F96]|].
    split; [apply KV; [lia | lia | exact F104]|]. split; [apply KV; [lia | lia | exact F120]|].
    split; [apply KV; [lia | lia | exact F128]|]. split; [apply KV; [lia | lia | exact F136]|].
    split; [apply KV; [lia | lia | exact F152]|]. split; [apply KV; [lia | lia | exact F184]|].
    split; [apply KF; [lia | lia | exact FF0]|]. split; [apply KF; [lia | lia | exact FF8]|].
    split; [apply KF; [lia | lia | exact FF16]|].
    split; [apply (akept_awr W mem1); [intros x Hx; apply KFRM; left; lia | exact FFw]|].
    split.
    { apply (akept_garr8 W mem1); [|exact FFsh]. intros x Hx. change (length fake_shadow) with 16%nat in Hx.
      apply KFRM. right. lia. }
    apply (akept_awr W mem1); [intros x Hx; apply KFRM; right; lia | exact FFshw]. }
  split.
  { (* the fake frame's flag word: kept by the store (above) and by the call (it lies in the fake frame) *)
    rewrite HFA, (lx_fla_kept B HJc). apply (lxk_sv8_kept W W2 mem1 mem'); [|exact HFL1].
    intros x Hx. apply KFRM. left. lia. }
  split; [exact HFA|].
  split.
  { (* the model *)
    unfold amodel_at. cbn [lm_hs lm_G lm_es lm_c lm_O lm_mx lm_cap lm_out lm_gn lm_nfd].
    split; [exact Hhs1|].
    split.
    { intros i Hi. specialize (Hslots1 i Hi). unfold aslot in *.
      assert (HHA : forall a, rg_s fr_RG + ASRC * Z.of_nat i <= a < rg_s fr_RG + ASRC * Z.of_nat i + ASRC ->
        abyte_kept W mem1 W2 mem' a).
      { intros a Ha. cbn [rg_s fr_RG fr_globals_b] in Ha. unfold ASRC in Ha. apply KIMG.
        - apply HGs. cbn [rg_s fr_RG fr_globals_b]. unfold ASRC. lia.
        - intros HR'. apply xrf_inG_RF in HR'. lia.
        - lia. }
      destruct (nth i (lm_hs m) None) as [h|] eqn:Eh.
      - apply (asrc_at_kept B ly3 S3 W mem1 ly' S' W2 mem' _ h Hslots1).
        + intros r Hr a Ha. refine (xrf_asrc_fp_in (abyte_kept W mem1 W2 mem') ly3 S3 W mem1 _ h Hslots1 HHA _ r Hr a Ha).
          intros b Hb x Hx. apply (KB b); [|exact Hx].
          unfold Rr. apply in_or_app. right. apply in_or_app. left.
          exact (xrf_slot_in (lm_hs m) i h ltac:(rewrite Hhs1; exact Hi) Eh b Hb).
        + intros b Hb. apply HR2. unfold Rr. apply in_or_app. right. apply in_or_app. left.
          exact (xrf_slot_in (lm_hs m) i h ltac:(rewrite Hhs1; exact Hi) Eh b Hb).
      - destruct Hslots1 as [Hz Hw]. split.
        + apply (akept_garr8 W mem1); [|exact Hz]. intros x Hx. rewrite repeat_length in Hx. apply HHA.
          unfold ASRC in *. lia.
        + apply (akept_awr W mem1); [|exact Hw]. intros x Hx. apply HHA. lia. }
    split.
    { destruct HRA as [(HT0 & _) | HRA]; [lia | exact HRA]. }
    split.
    { rewrite <- HOno in HOUT. exact HOUT. }
    split.
    { apply (agone_at_kept fr_RG W mem1 W2 mem' _ Hgone1). intros r Hr a Ha. destruct Hr as [<- | []].
      cbn [fst snd rg_gone fr_RG fr_globals_b] in Ha. apply KIMG; [apply XRF_Gcells; left; cbn; lia | | lia].
      intros HR'. apply xrf_inG_RF in HR'. lia. }
    split; [exact HLOCK|].
    split.
    { apply (awake_at_kept fr_RG W mem1 W2 mem' Hwake1). intros r Hr a Ha. destruct Hr as [<- | []].
      cbn [fst snd rg_wake fr_RG fr_globals_b] in Ha. apply KIMG; [apply XRF_Gcells; right; left; cbn; lia | | lia].
      intros HR'. apply xrf_inG_RF in HR'. lia. }
    assert (KN : forall a, AG_NFD <= a < AG_NFD + 4 -> abyte_kept W mem1 W2 mem' a).
    { intros a Ha. unfold AG_NFD in Ha. apply KIMG; [apply XRF_Gcells; right; right; left; unfold AG_NFD; lia | | lia].
      intros HR'. apply xrf_inG_RF in HR'. lia. }
    split; [apply (akept_vm W mem1); [intros x Hx; apply KN; cbn in Hx; lia | exact Hnfd1]|].
    split; [apply (akept_awr W mem1); [intros x Hx; apply KN; lia | exact Hnfdw1]|].
    split; [exact Hnfdr1|].
    split.
    { apply (akept_vm W mem1); [|exact Htu1]. intros x Hx. cbn in Hx. unfold AG_THREAD_UP in Hx.
      apply KIMG; [apply XRF_Gcells; right; right; right; unfold AG_THREAD_UP; lia | | lia].
      intros HR'. apply xrf_inG_RF in HR'. lia. }
    split; [exists (2 ^ 32 - 1); exact HGL | exact HGLw]. }
  split.
  { (* the input block *)
    destruct HIN1 as [Hblk Hg]. split.
    - destruct Hblk as [Hb0 | (Hn & Hin)]; [left; exact Hb0|]. right. split; [exact Hn|].
      apply HR2. unfold Rr, input_blks. destruct (Z.eqb_spec (c_n cx) 0); [lia|]. left. reflexivity.
    - apply (akept_garr8 W mem1); [|exact Hg]. intros x Hx. rewrite length_map, <- Hlen in Hx.
      destruct Hblk as [(Hn0 & _) | (Hn & Hin)]; [lia|].
      apply (KB (c_p cx, c_n cx)); [|cbn [fst snd]; exact Hx].
      unfold Rr, input_blks. destruct (Z.eqb_spec (c_n cx) 0); [lia|]. left. reflexivity. }
  assert (HROM2 : rom_view segs W2 mem').
  { eapply ajournal_gx_rom_view; [exact pa_segs_low | exact HJc | | exact HRV1].
    intros a Ha. destruct (XRF_ROM_OUT a Ha) as (H1 & H2 & H3 & H4). split; [|split; [exact H2 | split; assumption]].
    intros HGa. exact (H1 (xrf_G_sub a HGa)). }
  split; [exact HROM2|].
  split.
  { (* the jump table *)
    intros i Hi. apply (xrf_vm_aview W W2 mem1 mem'); [|exact (HJT1 i Hi)].
    intros x Hx. cbn in Hx. assert (Hro : in_rom segs x) by (apply XRF_JTAB_ROM; lia).
    rewrite (HROM2 x Hro), (HRV1 x Hro). reflexivity. }
  split.
  { (* the blocks *)
    split; [exists rest0; exact HPM|].
    intros b Hb. unfold model_blks in Hb. cbn [lm_G lm_es lm_hs lm_cap lm_out map concat app] in Hb.
    destruct Hb as [<- | Hb]; [apply HSEP2; left; reflexivity|].
    apply in_app_or in Hb as [Hb | Hb].
    { apply HSEP2. unfold model_blks. right. apply in_or_app. right. apply in_or_app. left. exact Hb. }
    destruct (in_dec xrf_peq b (ablocks B (c_ly cx) (c_S cx))) as [Hbe | Hbe]; [|left; exact Hbe].
    destruct (in_dec xrf_peq b (ablocks B ly3 S3)) as [Hb3 | Hb3].
    - pose proof (Permutation_in _ HPRF Hb3) as HbLR. apply in_app_or in HbLR as [HbL | HbR].
      + apply HSEP2. exact (HLM _ HbL).
      + exfalso. cbn [app] in HND2. apply List.NoDup_cons_iff in HND2 as [_ Hn2].
        exact (xrf_nodup_app (aout_blks (gse_cap R) out') Rr b Hn2 Hb HbR).
    - right. destruct b as [p n]. intros a Ha. cbn [fst snd] in Ha.
      assert (Hb' : In (p, n) (ablocks B ly' S'))
        by (apply (Permutation_in _ (Permutation_sym HPERM)); right; cbn [app]; apply in_or_app; left; exact Hb).
      destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR2 Hb') as (_ & _ & _ & _ & _ & _ & Hn).
      pose proof (req_size_pos n ltac:(lia)) as [_ Hq].
      replace a with (p + (a - p)) by lia. apply (Hfreed p n (a - p) Hbe Hb3). lia. }
  assert (RR : forall r : bv 5, acallee_saved (bv_unsigned r) -> In r xrf_kept -> getr regs' r = getr regs r)
    by (intros r H1 H2; rewrite (xrf_pres regs1 regs' r HPR H1); exact (KR r H2)).
  split; [rewrite (RR 2%bv ltac:(xrf_cs) ltac:(cbv; tauto)); exact R2|].
  split; [rewrite (RR 8%bv ltac:(xrf_cs) ltac:(cbv; tauto)); exact R8|].
  split; [rewrite (RR 9%bv ltac:(xrf_cs) ltac:(cbv; tauto)); exact R9|].
  split; [rewrite (RR 3%bv ltac:(xrf_cs) ltac:(cbv; tauto)); exact R3|].
  split; [rewrite (RR 4%bv ltac:(xrf_cs) ltac:(cbv; tauto)); exact R4|].
  split; [rewrite (RR 27%bv ltac:(xrf_cs) ltac:(cbv; tauto)); exact R27|].
  split; [exact (RR 19%bv ltac:(xrf_cs) ltac:(cbv; tauto))|].
  (* the caller's frame: kept by the store (off g_nout) and by the call (above its frame) *)
  assert (KC : forall a, lf_F cx <= a < spZ (c_regs cx) -> aview segs (w_H W2) mem' a = aview segs (w_H W) mem a).
  { intros a Ha. rewrite (proj1 (KHIGH a ltac:(lia))). apply aview_eq_of. apply MEQ.
    rewrite unsigned_lit_small by lia. cbn [rg_nout fr_RG fr_globals_b]. lia. }
  split.
  { apply (xrf_vm_aview W W2 mem mem'); [|exact HAT]. intros x Hx. apply KC. unfold AX_AT in Hx. cbn in Hx. lia. }
  split; [exact KC|].
  split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
  split; [reflexivity|]. split; [reflexivity|].
  split; [intros Hes; unfold R; rewrite Hes; reflexivity|].
  split; [rewrite xrf_run_eq; reflexivity|].
  split.
  { intros rest Hrest.
    assert (Hrr : Permutation rest rest0).
    { apply (Permutation_app_inv_l (input_blks cx ++ model_blks m)). rewrite <- !app_assoc.
      eapply Permutation_trans; [apply Permutation_sym; exact Hrest | exact HP0]. }
    eapply Permutation_trans; [exact HPM|]. apply Permutation_app_head. apply Permutation_app_head.
    apply Permutation_sym. exact Hrr. }
  split; [rewrite HFRM; reflexivity|].
  split; [rewrite xrf_cost_eq; exact HMO|].
  rewrite xrf_run_eq. reflexivity.
Qed.

End lx.
