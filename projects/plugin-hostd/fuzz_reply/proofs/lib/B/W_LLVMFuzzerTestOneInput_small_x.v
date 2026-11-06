(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs, 2026-10: the ARx-GENERIC conversion of image B's four small arms of fuzz_reply's
   LLVMFuzzerTestOneInput (lib/B/W_LLVMFuzzerTestOneInput_small.v, the AR proofs, Qed at
   commit b48d2f61046; they build unchanged on this cut) to the cut invariants of
   lib/B/W_LLVMFuzzerTestOneInput_cut_x.v (the generic allocator relation ARx).  Each theorem is exactly one of B
   cut_x's Section w hypotheses: lf_arm_close_x = ARM_close, lf_arm_eintr_x = ARM_eintr, lf_arm_sendmax_x =
   ARM_sendmax, lf_arm_default_x = ARM_default.  Neither _small.v nor cut_x is edited.  The template is image A's
   lib/A/W_LLVMFuzzerTestOneInput_small_x.v; each conversion step below is that file's, applied to B's text.
   - The Section header is B cut_x's Section w header (B .. RINV, with PST / ARx / hl / LAWS / HP0 / HG / LSx).  The
     piece's own Section hypotheses follow, in _small.v's text: HGs .. HGlk, HZS, TL, HERRHI (no allocator relation
     in them); ALOCK / AUNLOCK at their W_sites_x.v twins alock_realizes_x / aunlock_realizes_x over ARx; RI_* / LS_*
     carried verbatim, LS renamed LSx (cut_x's name).
   - The AR-free lemmas and definitions of _small.v are CITED from it; its section-local tactics are restated.  Each
     lemma of _small.v that takes an AR state is converted here under its name + _x, with _small.v's proof: its AR
     premise becomes `ARE ly S W mem md` (some ghost list Hp with ARx ly S Hp W mem md), the AR laws AR_laws_x's
     fields, the journal W_journal_x.ajournal_gx_x (Hp after S), the runs W_journal_x's paj_run_x_x / paj_run_to_x_x
     through W_kit_x's paj_run(_to)_tok_x, the lock / unlock liftings W_sites_x's aj_gx_entry_at_x.
   - blk_off_imgP (W_kit.v) is re-derived as sm_blk_off_x from W_img_x.fr_img_cover_x (B's image top 0x5fc000 =
     YImgTop.IMG_TOP_B) and the client-image law; its size premise 0 <= n is a premise of sm_blk_off_x /
     sm_blk_kept_x, which every caller has.  So no IMGC / BLKN Section hypothesis.
   - Image-constant steps of the runs end in `first [reflexivity | apply unsigned_lit_small; lia]` (A's small_x). *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YCbqG.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import
W_kit_x W_journal_x W_contract_x W_sites_x W_img_x W_LLVMFuzzerTestOneInput_cut_x.
(* _small.v's own imports, AFTER the generic kit's: the copied proofs see the names they were written against *)
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
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import HarnessRep RelayRep gestures_end_b_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_rep W_contract W_frame W_sites.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require ReplyGuardB.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_LLVMFuzzerTestOneInput_cut.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_LLVMFuzzerTestOneInput_small.
Import ListNotations.
Local Unset Lia Cache. Local Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
(* the zify flag _small.v's proofs (copied here) expect *)
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope Z_scope.
(* the program interface's stack bound (as the B cut names it) *)
Local Notation LLVMF_STK := YCfn.LLVMF_STK.

Section smx.
Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Local Notation segs := (@pa_segs _ fr_prog_listing PB_fr).
(* ---- B cut_x's Section w header (W_LLVMFuzzerTestOneInput_cut_x.v:200-244) ---- *)
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
#[local] Notation VAL := (@pa_val _ fr_prog_listing PB_fr).
#[local] Notation BASE := (@pa_val _ fr_prog_listing PB_fr A_TEXT).
#[local] Notation SIGMA := (@pa_sigma _ fr_prog_listing PB_fr).

(* ---------------------------------------------------------------- the piece's own hypotheses (_small.v :455-496) *)
(* the globals these arms store to are covered by G_fr (at the pin: W_LLVMFuzzerTestOneInput_G.v c_HGs, c_HG_smax,
   c_HG_seintr, c_HG_sdead, c_HG_gone, c_HG_client, c_HGlock, each by vm_compute at G_fr_c) *)
Hypothesis HGs : forall a, rg_s fr_RG <= a < rg_s fr_RG + 4 * ASRC -> inG G_fr a.
Hypothesis HGmx : forall a, rg_send_max fr_RG <= a < rg_send_max fr_RG + 8 -> inG G_fr a.
Hypothesis HGei : forall a, rg_send_eintr fr_RG <= a < rg_send_eintr fr_RG + 1 -> inG G_fr a.
Hypothesis HGdd : forall a, rg_send_dead fr_RG <= a < rg_send_dead fr_RG + 1 -> inG G_fr a.
Hypothesis HGgn : forall a, rg_gone fr_RG <= a < rg_gone fr_RG + 1 -> inG G_fr a.
Hypothesis HGcl : forall a, rg_client fr_RG <= a < rg_client fr_RG + 4 -> inG G_fr a.
Hypothesis HGlk : forall a, rg_lock fr_RG <= a < rg_lock fr_RG + 12 -> inG G_fr a.
(* g_s's four sources are in the instance's zero-shadow ranges: the arms' checks of g_s[i] pass (at the pin: YF0m's
   Tfib_zero_shadow holds the range (0x5d8e60, 384), W_LLVMFuzzerTestOneInput_G.v's header) *)
Hypothesis HZS : azs B (rg_s fr_RG) (4 * ASRC).
(* the allocator instance (W_kit.v PALib; W_asm.v's I_TL): its api_env puts errno's cell in the image, below
   kLowMemEnd *)
Hypothesis TL : PALib B.
(* errno's cell lies above g_out (0x5d90c0), the highest of the program's globals (errno = 0x5d994c at the pin;
   W_LLVMFuzzerTestOneInput_G.v c_HERRHI) *)
Hypothesis HERRHI : rg_out fr_RG + 8 <= as_errno B.
(* the default arm's two libc calls: W_sites_x.v's site contracts, the twins of _small.v's ALOCK / AUNLOCK (W_sites.v's
   at their B SIGMA names) over ARx *)
Hypothesis ALOCK : alock_realizes_x (PI := PB_fr) B ARx (SIGMA WS_pthread_mutex_lock).
Hypothesis AUNLOCK : aunlock_realizes_x (PI := PB_fr) B ARx (SIGMA WS_pthread_mutex_unlock).
(* the model step of each arm (the open obligations of this file), each at the choice the walk makes: the source
   pick() returns for the second byte (or 0), the second byte (or 0), the default arm's branch *)
Hypothesis RI_close : forall cx t m i, RINV cx t m ->
  pick (lm_hs m) (if lm_k m + 1 <? c_n cx then in_byte cx (lm_k m + 1) else 0) = Some i ->
  RINV cx (t + 1) (sm_close cx m i).
Hypothesis RI_eintr : forall cx t m i, RINV cx t m ->
  pick (lm_hs m) (if lm_k m + 1 <? c_n cx then in_byte cx (lm_k m + 1) else 0) = Some i ->
  RINV cx (t + 1) (sm_eintr cx m i).
Hypothesis RI_sendmax : forall cx t m, RINV cx t m ->
  RINV cx (t + 1) (sm_sendmax cx m (if lm_k m + 1 <? c_n cx then in_byte cx (lm_k m + 1) else 0)).
Hypothesis RI_default : forall cx t m, RINV cx t m -> RINV cx (t + 1) (sm_default cx m (sm_dg cx m)).
Hypothesis LS_close : forall cx t m i ly S, LSx cx t m ly S ->
  pick (lm_hs m) (if lm_k m + 1 <? c_n cx then in_byte cx (lm_k m + 1) else 0) = Some i ->
  LSx cx (t + 1) (sm_close cx m i) ly S.
Hypothesis LS_eintr : forall cx t m i ly S, LSx cx t m ly S ->
  pick (lm_hs m) (if lm_k m + 1 <? c_n cx then in_byte cx (lm_k m + 1) else 0) = Some i ->
  LSx cx (t + 1) (sm_eintr cx m i) ly S.
Hypothesis LS_sendmax : forall cx t m ly S, LSx cx t m ly S ->
  LSx cx (t + 1) (sm_sendmax cx m (if lm_k m + 1 <? c_n cx then in_byte cx (lm_k m + 1) else 0)) ly S.
Hypothesis LS_default : forall cx t m ly S, LSx cx t m ly S -> LSx cx (t + 1) (sm_default cx m (sm_dg cx m)) ly S.

(* an allocator state over ARx at some ghost list: the form the converted helpers take their AR premise in *)
Local Notation ARE ly S W mem md := (exists Hp : list Z, ARx ly S Hp W mem md).

(* ---------------------------------------------------------------- the image's place, from the laws *)
(* W_kit_x.v blk_off_imgP_x's proof, with IMGC := W_img_x.fr_img_cover_x (B's segments) and its BLKN premise as the
   premise 0 <= n *)
Lemma sm_blk_off_x : forall ly S Hp (W : world segs) mem md p n,
  ARx ly S Hp W mem md -> In (p, n) (ablocks B ly S) -> 0 <= n ->
  OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B.YCbq.off_img p (req_size n).
Proof.
  intros ly S Hp W mem md p n HAR Hin Hn. unfold OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B.YCbq.off_img.
  destruct (W_img_x.fr_img_cover_x B ARx LAWS ly S Hp W mem md HAR) as [C1 C2].
  pose proof (req_size_pos n Hn) as [Q _].
  destruct (Z.le_gt_cases (p + req_size n) 0x10000) as [|H1]; [left; lia|].
  destruct (Z.le_gt_cases 0x5fc000 p) as [|H2]; [right; lia|]. exfalso.
  assert (Hc : ~ in_zr (Z.max p 0x10000) (ly_img ly)).
  { refine (proj1 (alx_client_img _ _ _ LAWS ly S Hp W mem md (Z.max p 0x10000) HAR _)).
    left. exists p, n. split; [exact Hin | lia]. }
  apply Hc. unfold in_zr. lia.
Qed.

Lemma sm_blk_kept_x : forall ly S (W : world segs) mem md mem' X b n a,
  ARE ly S W mem md -> XOK X -> KEPT W mem mem' X ->
  In (b, n) (ablocks B ly S) -> 0 <= n -> b <= a < b + req_size n + 8 -> abyte_kept W mem W mem' a.
Proof.
  intros ly S W mem md mem' X b n a [Hp HAR] HX HK Hin Hn Ha.
  destruct (alx_blocks _ _ _ LAWS ly S Hp W mem md b n HAR Hin) as (_ & H4096 & Hceil & _).
  pose proof (sm_blk_off_x ly S Hp W mem md b n HAR Hin Hn) as Hoff.
  pose proof sm_ceil_lo as Hac.
  unfold OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B.YCbq.off_img in Hoff.
  apply HK; [lia|].
  intros HinX. destruct (HX a HinX) as [Hc | Hc]; lia.
Qed.

Lemma sm_frm_kept_x : forall ly S (W : world segs) mem md mem' X cid pos a,
  ARE ly S W mem md -> XOK X -> KEPT W mem mem' X -> In (cid, pos) (frames S) ->
  frame_addr ly cid pos <= a < frame_addr ly cid pos + fs_frame_bytes cid -> abyte_kept W mem W mem' a.
Proof.
  intros ly S W mem md mem' X cid pos a [Hp HAR] HX HK Hin Ha.
  destruct (frames_bounds_x _ _ _ LAWS ly S Hp W mem md cid pos HAR Hin) as (H1 & H2 & _).
  pose proof sm_ceil_lo as Hac.
  apply HK; [lia|]. intros HinX. destruct (HX a HinX) as [Hc | Hc]; [|lia].
  destruct (alx_client_img _ _ _ LAWS ly S Hp W mem md a HAR
    (or_intror (or_introl (ex_intro _ cid (ex_intro _ pos (conj Hin Ha)))))) as [_ Hni].
  exact (Hni (sm_img_of XM_LIB XN_LIB RLO a Hc)).
Qed.

Lemma sm_alist_fp_kept_x : forall X (W : world segs) (mem mem' : word -> option byte), XOK X -> KEPT W mem mem' X -> forall ly S md LA l lines, ARE ly S W mem md ->
  alist_at B ly S W mem LA l lines -> sm_koff W mem mem' (LA, LA + 16) ->
  forall r, In r (alist_fp LA l) -> sm_koff W mem mem' r.
Proof.
  intros X W mem mem' HX HK ly S md LA l lines HAR (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9) HLA r Hr.
  unfold alist_fp in Hr. destruct Hr as [<- | Hr]; [exact HLA|].
  apply in_app_or in Hr as [Hr | Hr].
  - destruct (hl_cap l =? 0) eqn:Ec; [destruct Hr|]. destruct Hr as [<- | []].
    apply Z.eqb_neq in Ec.
    destruct H6 as [(Hc & _) | (Hc & Hin & Hj & _)]; [lia|].
    intros a Ha. unfold gfp, bzs in Ha. cbn [fst snd] in Ha. rewrite length_map, length_app, sm_len_text in Ha.
    unfold hl_n in Hj, H5.
    apply (sm_blk_kept_x ly S W mem md mem' X (hl_v l) (AREC * hl_cap l) a HAR HX HK Hin ltac:(unfold AREC; lia)).
    pose proof (req_size_pos (AREC * hl_cap l) ltac:(unfold AREC; lia)) as [_ Hq]. unfold AREC in *. lia.
  - apply in_map_iff in Hr as (rr & <- & Hrr). rewrite Forall_forall in H9. destruct (H9 rr Hrr) as (Hb & _).
    intros a Ha. unfold gfp, bzs in Ha. cbn [fst snd] in Ha. rewrite length_map, length_app in Ha. cbn [length] in Ha.
    apply (sm_blk_kept_x ly S W mem md mem' X (fst rr) (Z.of_nat (length (snd rr)) + 1) a HAR HX HK Hb ltac:(lia)).
    pose proof (req_size_pos (Z.of_nat (length (snd rr)) + 1) ltac:(lia)) as [_ Hq]. lia.
Qed.

Lemma sm_asrc_fp_kept_x : forall X (W : world segs) (mem mem' : word -> option byte), XOK X -> KEPT W mem mem' X -> forall ly S md HA h, ARE ly S W mem md -> asrc_at B ly S W mem HA h ->
  sm_koff W mem mem' (HA, HA + ASRC) -> forall r, In r (asrc_fp HA h) -> sm_koff W mem mem' r.
Proof.
  intros X W mem mem' HX HK ly S md HA h HAR Hs HHA r Hr.
  pose proof Hs as (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11 & H12 & H13 & H14 & H15 & H16 & H17 & H18 &
    H19 & H20 & H21 & H22 & H23 & H24).
  unfold asrc_fp in Hr. destruct Hr as [<- | [<- | Hr]]; [exact HHA | |].
  - intros a Ha. unfold gfp, bzs in Ha. cbn [fst snd] in Ha. rewrite length_map, H19 in Ha.
    apply (sm_blk_kept_x ly S W mem md mem' X (hs_partial h) APARTIAL a HAR HX HK H18 ltac:(unfold APARTIAL; lia)).
    pose proof (req_size_pos APARTIAL ltac:(unfold APARTIAL; lia)) as [_ Hq]. lia.
  - apply in_app_or in Hr as [Hr | Hr]; [|apply in_app_or in Hr as [Hr | Hr]].
    + apply (sm_alist_fp_kept_x X W mem mem' HX HK ly S md (HA + 16) (hs_pending h) false HAR H10); [|exact Hr].
      apply (sm_koff_sub W mem mem' HA ASRC); [exact HHA | lia | unfold ASRC; lia].
    + apply (sm_alist_fp_kept_x X W mem mem' HX HK ly S md (HA + 64) (hs_expected h) true HAR H22); [|exact Hr].
      apply (sm_koff_sub W mem mem' HA ASRC); [exact HHA | lia | unfold ASRC; lia].
    + apply (sm_alist_fp_kept_x X W mem mem' HX HK ly S md (HA + 80) (hs_held h) true HAR H23); [|exact Hr].
      apply (sm_koff_sub W mem mem' HA ASRC); [exact HHA | lia | unfold ASRC; lia].
Qed.

Lemma sm_aentry_fp_kept_x : forall X (W : world segs) (mem mem' : word -> option byte), XOK X -> KEPT W mem mem' X -> forall ly S md e, ARE ly S W mem md -> aentry_ok B ly S W mem e ->
  forall r, In r (aentry_fp e) -> sm_koff W mem mem' r.
Proof.
  intros X W mem mem' HX HK ly S md e HAR (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11 & H12 & H13 & H14 & H15) r Hr.
  unfold aentry_fp in Hr. apply in_app_or in Hr as [Hr | Hr].
  - destruct (re_cap e =? 0) eqn:Ec; [destruct Hr|]. destruct Hr as [<- | []]. apply Z.eqb_neq in Ec.
    destruct H10 as [(Hc & _) | (Hc & Hin & Hj & _)]; [lia|].
    intros a Ha. unfold gfp, bzs in Ha. cbn [fst snd] in Ha. rewrite length_map, length_app in Ha.
    apply (sm_blk_kept_x ly S W mem md mem' X (re_buf e) (re_cap e) a HAR HX HK Hin ltac:(lia)).
    pose proof (req_size_pos (re_cap e) ltac:(lia)) as [_ Hq]. lia.
  - destruct Hr as [<- | Hr].
    + intros a Ha. unfold gfp, bzs in Ha. cbn [fst snd] in Ha. rewrite length_map, sm_len_kptrs in Ha.
      destruct H12 as [(Hz & Hk) | (Hz & Hin & Hk1 & Hk2 & _)]; [rewrite Hk in Ha; cbn in Ha; lia|].
      apply (sm_blk_kept_x ly S W mem md mem' X (re_hp e) (re_kh e) a HAR HX HK Hin ltac:(lia)).
      pose proof (req_size_pos (re_kh e) ltac:(lia)) as [_ Hq]. unfold re_nheld in Hk1. lia.
    + apply in_map_iff in Hr as (k & <- & Hk). rewrite Forall_forall in H15.
      destruct (H15 k Hk) as (K1 & K2 & K3 & K4).
      intros a Ha. unfold gfp, bzs in Ha. cbn [fst snd] in Ha. rewrite length_map, length_app in Ha. cbn [length] in Ha.
      apply (sm_blk_kept_x ly S W mem md mem' X (key_addr k) (Z.of_nat (length (key_text k)) + 1) a HAR HX HK K1 ltac:(lia)).
      pose proof (req_size_pos (Z.of_nat (length (key_text k)) + 1) ltac:(lia)) as [_ Hq]. lia.
Qed.

Lemma sm_arelay_fp_kept_x : forall X (W : world segs) (mem mem' : word -> option byte), XOK X -> KEPT W mem mem' X -> forall RG ly S md G es, ARE ly S W mem md -> arelay_at B RG ly S W mem G es ->
  sm_koff W mem mem' (rg_src RG, rg_src RG + 8) -> sm_koff W mem mem' (rg_nsrc RG, rg_nsrc RG + 4) ->
  sm_koff W mem mem' (rg_capsrc RG, rg_capsrc RG + 4) ->
  forall r, In r (arelay_fp RG G es) -> sm_koff W mem mem' r.
Proof.
  intros X W mem mem' HX HK RG ly S md G es HAR (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11) R1 R2 R3 r Hr.
  unfold arelay_fp in Hr. destruct Hr as [<- | [<- | [<- | [<- | Hr]]]]; [exact R1 | exact R2 | exact R3 | |].
  - intros a Ha. cbn [fst snd] in Ha. apply (sm_blk_kept_x ly S W mem md mem' X G ATABLE a HAR HX HK H8 ltac:(unfold ATABLE; lia)).
    pose proof (req_size_pos ATABLE ltac:(unfold ATABLE; lia)) as [_ Hq]. lia.
  - apply in_concat in Hr as (l & Hl & Hr). apply in_map_iff in Hl as (e & <- & He).
    rewrite Forall_forall in H10. exact (sm_aentry_fp_kept_x X W mem mem' HX HK ly S md e HAR (H10 e He) r Hr).
Qed.

Lemma sm_fl_entry_x : forall (W : world segs) regs mem ly S md F HA fo pc,
  ARE ly S W mem md ->
  getr regs 23 = w64 1 -> getr regs 9 = w64 F -> getr regs 21 = w64 HA -> getr regs 27 = w64 SB ->
  2 ^ 46 <= F <= 2 ^ 47 -> F mod 32 = 0 ->
  rg_s fr_RG <= HA <= rg_s fr_RG + 4 * ASRC -> HA mod 32 = 0 ->
  (fo = 8 \/ fo = 12) ->
  (forall a, F + 144 <= a < F + 152 -> writable_at segs (arm W mem) a) ->
  (forall a, HA + fo <= a < HA + fo + 4 -> writable_at segs (arm W mem) a) ->
  azs B HA ASRC ->
  st_ok_pi segs VAL (Eimg (Ereg regs (@nil word))) (mkSS pc sm_fl_sr (sm_fl_regions fo) None sm_fl_facts)
    (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + pc)) mem (seg_rom segs)))
  /\ sh_ok segs sm_Bx sm_fl_SH (Eimg (Ereg regs (@nil word))) (mrestrict (w_H W) mem).
Proof.
  intros W regs mem ly S md F HA fo pc [Hp HAR] H23 H9 H21 H27 HF1 HF2 HH1 HH2 Hfo HW1 HW2 HZ.
  rewrite restrict_mkst_fx.
  set (E := Eimg (Ereg regs (@nil word))).
  assert (EE : forall m (rr : bv 5), Z.of_nat m = bv_unsigned rr -> ew E m = getr regs rr)
    by (intros m rr Hm; subst E; pose proof (bv_unsigned_in_range 5 rr) as Hr5;
        change (bv_modulus 5) with 32 in Hr5; rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_nat; exact Hm).
  assert (E23 : ew E 23 = w64 1) by (rewrite (EE 23%nat 23%bv eq_refl); exact H23).
  assert (E9 : ew E 9 = w64 F) by (rewrite (EE 9%nat 9%bv eq_refl); exact H9).
  assert (E21 : ew E 21 = w64 HA) by (rewrite (EE 21%nat 21%bv eq_refl); exact H21).
  assert (E27 : ew E 27 = w64 SB) by (rewrite (EE 27%nat 27%bv eq_refl); exact H27).
  assert (HRS : rg_s fr_RG = 6131296) by reflexivity.
  assert (HAS : ASRC = 96) by reflexivity.
  assert (HSB : SB = 2147450880) by reflexivity.
  assert (HSO : SHADOW_OFF = 2147450880) by reflexivity.
  destruct Hfo as [-> | ->];
  (split;
   [ apply pa_entry_st_ok_full;
     [ unfold sm_fl_sr; apply regs_ok_Eimg_Ereg
     | vm_compute; reflexivity
     | unfold sm_fl_regions; repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
       cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val];
       [ rewrite E9, unsigned_lit_small by lia;
         split; [lia|]; split; [lia|]; split; [intros o Ho; apply HW1; lia | apply Forall_nil]
       | rewrite E21, unsigned_lit_small by lia;
         split; [lia|]; split; [lia|]; split; [intros o Ho; apply HW2; lia | apply Forall_nil] ]
     | apply pairwise_disjoint_of_extents; unfold sm_fl_regions, extent_of_region;
       cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val];
       rewrite E9, E21, !unsigned_lit_small by lia;
       cbn [zpairwise_disjoint zall_disjoint]; unfold zdisj; cbn [fst snd]; repeat split; lia
     | split; [|split; [exact I | exact I]];
       cbn [sm_fl_facts f_atoms atoms_ok]; unfold afact_ok; cbn [af_lo af_hi af_al2];
       rewrite E9, E21, E23, E27, !unsigned_lit_small by lia;
       rewrite !Z.pow_0_r, !Z.mod_1_r;
       repeat match goal with |- _ /\ _ => split end; try change (2 ^ 5) with 32; lia ]
   | unfold sh_ok, sm_fl_SH; constructor; [|constructor];
     eapply shent_ok_of_range;
     [ exact (azs_range_addressable_x B ARx LAWS ly S Hp W mem md HA ASRC HAR HZ)
     | unfold sm_Bx; rewrite (U_atom E 27 SB E27) by lia; reflexivity
     | rewrite (U_atom E 21 HA E21) by lia; reflexivity
     | lia
     | lia
     | intros x Hx; cbn [Z.min Z.max] in Hx; lia ] ]).
Qed.

Lemma sm_slot_store_x : forall ly S (W : world segs) mem md mem' X HA h h' fo,
  ARE ly S W mem md -> XOK X -> KEPT W mem mem' X ->
  mem_grows (mrestrict (w_H W) mem) (mrestrict (w_H W) mem') ->
  asrc_at B ly S W mem HA h -> same_but_flags h h' ->
  ((fo = 8 /\ hs_closed h' = 1 /\ hs_eintr h' = hs_eintr h) \/
   (fo = 12 /\ hs_eintr h' = 1 /\ hs_closed h' = hs_closed h)) ->
  (forall a, HA <= a < HA + ASRC -> ~ (HA + fo <= a < HA + fo + 4) -> ~ inFP X a) ->
  0 <= HA -> HA + ASRC < 2 ^ 64 ->
  val_mem segs (arm W mem') (HA + fo) 4 1 ->
  asrc_at B ly S W mem' HA h'.
Proof.
  intros ly S W mem md mem' X HA h h' fo HAR HX HK HGr Hs Hsame Hfo Hdis HA0 HA1 Hnew.
  destruct Hsame as (Efd & Eopen & Epend & Eoff & Epart & Epjunk & Enp & Eov & Epad & Eexp & Eheld).
  pose proof Hs as (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11 & H12 & H13 & H14 & H15 & H16 & H17 & H18 &
    H19 & H20 & H21 & H22 & H23 & H24).
  assert (HAS : ASRC = 96) by reflexivity.
  assert (KH : forall a, HA <= a < HA + ASRC -> ~ (HA + fo <= a < HA + fo + 4) -> abyte_kept W mem W mem' a)
    by (intros a Ha Hn; apply HK; [lia | exact (Hdis a Ha Hn)]).
  assert (KV : forall a n v, HA <= a -> a + Z.of_nat n <= HA + ASRC ->
      (forall x, a <= x < a + Z.of_nat n -> ~ (HA + fo <= x < HA + fo + 4)) ->
      val_mem segs (arm W mem) a n v -> val_mem segs (arm W mem') a n v)
    by (intros a n v Ha Hn Hd Hv; apply (akept_vm W mem); [intros x Hx; apply KH; [lia | exact (Hd x Hx)] | exact Hv]).
  assert (KL : forall LA, HA <= LA -> LA + 16 <= HA + ASRC ->
      (forall x, LA <= x < LA + 16 -> ~ (HA + fo <= x < HA + fo + 4)) -> sm_koff W mem mem' (LA, LA + 16))
    by (intros LA Ha Hn Hd x Hx; cbn [fst snd] in Hx; apply KH; [lia | exact (Hd x Hx)]).
  assert (KAL : forall LA l lines, HA <= LA -> LA + 16 <= HA + ASRC ->
      (forall x, LA <= x < LA + 16 -> ~ (HA + fo <= x < HA + fo + 4)) ->
      alist_at B ly S W mem LA l lines -> alist_at B ly S W mem' LA l lines).
  { intros LA l lines Ha Hn Hd Hl.
    apply (alist_at_kept B ly S W mem ly S W mem' LA l lines Hl).
    - apply (sm_akept_of W mem mem'). intros r Hr.
      exact (sm_alist_fp_kept_x X W mem mem' HX HK ly S md LA l lines HAR Hl (KL LA Ha Hn Hd) r Hr).
    - exact (sm_alist_blks_in B W mem ly S LA l lines Hl). }
  assert (HBW : forall a, hs_partial h <= a < hs_partial h + req_size APARTIAL + 8 -> abyte_kept W mem W mem' a)
    by (intros a Ha; exact (sm_blk_kept_x ly S W mem md mem' X (hs_partial h) APARTIAL a HAR HX HK H18
          ltac:(unfold APARTIAL; lia) Ha)).
  assert (HFO : fo = 8 \/ fo = 12) by (destruct Hfo as [(-> & _) | (-> & _)]; [left | right]; reflexivity).
  split; [|split; [|split; [|split; [|split; [|split; [|split; [|split; [|split; [|split; [|split; [|split; [|split; [|split; [|split; [|split; [|split; [|split; [|split; [|split; [|split; [|split; [|split]]]]]]]]]]]]]]]]]]]]]].
  - rewrite Efd. apply (KV HA 4%nat (hs_fd h)); [lia | cbn; lia | cbn; intros x Hx; lia | exact H1].
  - rewrite Eopen. apply (KV (HA + 4) 4%nat (hs_open h)); [lia | cbn; lia | cbn; intros x Hx; lia | exact H2].
  - destruct Hfo as [(-> & Hc & _) | (-> & _ & Hc)].
    + rewrite Hc. exact Hnew.
    + rewrite Hc. apply (KV (HA + 8) 4%nat (hs_closed h)); [lia | cbn; lia | cbn; intros x Hx; lia | exact H3].
  - destruct Hfo as [(-> & _ & He) | (-> & He & _)].
    + rewrite He. apply (KV (HA + 12) 4%nat (hs_eintr h)); [lia | cbn; lia | cbn; intros x Hx; lia | exact H4].
    + rewrite He. exact Hnew.
  - exact (sm_awr W mem mem' HA ASRC HGr H5).
  - destruct Hfo as [(_ & Hc & _) | (_ & _ & Hc)]; [rewrite Hc; right; reflexivity | rewrite Hc; exact H6].
  - destruct Hfo as [(_ & _ & He) | (_ & He & _)]; [rewrite He; exact H7 | rewrite He; right; reflexivity].
  - rewrite Eopen. exact H8.
  - rewrite Efd. exact H9.
  - rewrite Epend. apply (KAL (HA + 16)); [lia | cbn; lia | intros x Hx; lia | exact H10].
  - rewrite Eoff. apply (KV (HA + 32) 8%nat (hs_off h)); [lia | cbn; lia | cbn; intros x Hx; lia | exact H11].
  - rewrite Epart. apply (KV (HA + 40) 8%nat (hs_partial h)); [lia | cbn; lia | cbn; intros x Hx; lia | exact H12].
  - rewrite Enp. apply (KV (HA + 48) 8%nat (hs_npartial h)); [lia | cbn; lia | cbn; intros x Hx; lia | exact H13].
  - rewrite Eov. apply (KV (HA + 56) 4%nat (hs_overlong h)); [lia | cbn; lia | cbn; intros x Hx; lia | exact H14].
  - rewrite Epend, Eoff. exact H15.
  - rewrite Enp. exact H16.
  - rewrite Eov. exact H17.
  - rewrite Epart. exact H18.
  - rewrite Epjunk. exact H19.
  - rewrite Epart, Epjunk. apply (akept_garr8 W mem); [|exact H20].
    intros x Hx. unfold bzs in Hx. rewrite length_map, H19 in Hx. apply HBW.
    pose proof (req_size_pos APARTIAL ltac:(unfold APARTIAL; lia)) as [_ Hq]. lia.
  - unfold hs_W. rewrite Enp, Epjunk. exact H21.
  - rewrite Eexp. apply (KAL (HA + 64)); [lia | cbn; lia | intros x Hx; lia | exact H22].
  - rewrite Eheld. apply (KAL (HA + 80)); [lia | cbn; lia | intros x Hx; lia | exact H23].
  - unfold hs_blocks. rewrite Epend, Epart, Eexp, Eheld. exact H24.
Qed.

Ltac sm_rgl :=
  let R := fresh "RV" in pose proof sm_rgv as R;
  unfold ASRC, AG_NFD, AG_THREAD_UP, AG_LISTEN in *;
  destruct R as (?&?&?&?&?&?&?&?&?&?&?&?&?&?&?); lia.

Lemma sm_aframe_kept_x : forall cx ly S (W : world segs) mem md mem' fpos XG,
  ARE ly S W mem md -> In (1, fpos) (frames S) ->
  alloc_ceiling + 32768 <= spZ (c_regs cx) <= 2 ^ 47 ->
  XGOK XG -> KEPT W mem mem' (XS (lf_F cx) XG) ->
  mem_grows (mrestrict (w_H W) mem) (mrestrict (w_H W) mem') ->
  aframe_at cx (frame_addr ly 1 fpos) W mem -> aframe_at cx (frame_addr ly 1 fpos) W mem'.
Proof.
  intros cx ly S W mem md mem' fpos XG HAR Hfin Hsp HXG HK HGr
    (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & A10 & A11 & A12 & A13 & A14 & A15 & A16 & A17 & A18 & A19 &
     A20 & A21 & A22).
  pose proof sm_ceil_lo as Hac. assert (HES : ESTACK = 4096) by reflexivity.
  assert (HFb : spZ (c_regs cx) - 352 < lf_F cx <= spZ (c_regs cx) - 320).
  { unfold lf_F. pose proof (Z.mod_pos_bound (spZ (c_regs cx) - 320) 32 ltac:(lia)). lia. }
  assert (HXOK : XOK (XS (lf_F cx) XG)) by (apply sm_xok; [lia | exact HXG]).
  pose proof HAR as [Hp HARx].
  destruct (frames_bounds_x _ _ _ LAWS ly S Hp W mem md 1 fpos HARx Hfin) as (HFF1 & HFF2 & _).
  replace (fs_frame_bytes 1) with 128 in HFF2 by reflexivity.
  assert (FF8 : 0 <= frame_addr ly 1 fpos / 8 /\ 8 * (frame_addr ly 1 fpos / 8) <= frame_addr ly 1 fpos)
    by (split; [apply Z.div_pos; lia | apply Z.mul_div_le; lia]).
  assert (KS : forall a, 0x5fc000 <= a < 2 ^ 64 -> ~ (lf_F cx - ESTACK <= a < lf_F cx) ->
      ~ (lf_F cx + 144 <= a < lf_F cx + 152) -> abyte_kept W mem W mem' a)
    by (intros a Ha H0 Hn; apply (sm_kept_off W mem mem' (lf_F cx) XG HXG HK); lia).
  assert (KF : forall a, frame_addr ly 1 fpos <= a < frame_addr ly 1 fpos + 128 -> abyte_kept W mem W mem' a)
    by (intros a Ha; exact (sm_frm_kept_x ly S W mem md mem' _ _ _ a HAR HXOK HK Hfin
          ltac:(change (fs_frame_bytes 1) with 128; lia))).
  assert (KV : forall a v, 0x5fc000 <= a -> a + 8 <= 2 ^ 64 ->
      ((lf_F cx <= a /\ a + 8 <= lf_F cx + 144) \/ lf_F cx + 152 <= a) ->
      sv8 W mem a v -> sv8 W mem' a v).
  { intros a v H0 H1 H2 Hv. unfold sv8 in *. apply (akept_vm W mem); [|exact Hv].
    intros x Hx. apply KS; cbn in Hx; lia. }
  assert (KFV : forall o v, 0 <= o -> o + 8 <= 128 -> sv8 W mem (frame_addr ly 1 fpos + o) v ->
      sv8 W mem' (frame_addr ly 1 fpos + o) v).
  { intros o v H0 H1 Hv. unfold sv8 in *. apply (akept_vm W mem); [|exact Hv].
    intros x Hx. apply KF. cbn in Hx. lia. }
  assert (KW : forall a n, awr W mem a n -> awr W mem' a n) by (intros a n Hw; exact (sm_awr W mem mem' a n HGr Hw)).
  split.
  { intros o r Hin.
    assert (Ho : 8 <= o <= 104).
    { cbn in Hin. repeat (destruct Hin as [Eo | Hin]; [inversion Eo; lia|]). destruct Hin. }
    apply KV; [lia | lia | lia | exact (A1 o r Hin)]. }
  split; [exact (KW _ _ A2)|].
  do 14 (split; [apply KV; [lia | lia | lia | assumption]|]).
  split; [rewrite <- (Z.add_0_r (frame_addr ly 1 fpos)); apply KFV; [lia | lia | rewrite Z.add_0_r; exact A17]|].
  split; [apply KFV; [lia | lia | exact A18]|].
  split; [apply KFV; [lia | lia | exact A19]|].
  split; [exact (KW _ _ A20)|].
  split; [|exact (KW _ _ A22)].
  apply (akept_garr8 W mem); [|exact A21]. intros x Hx.
  unfold fake_shadow in Hx. cbn [length] in Hx. apply KS; unfold SB in *; lia.
Qed.

Lemma sm_flag_kept_x : forall ly S (W : world segs) mem md mem' X fpos v,
  ARE ly S W mem md -> XOK X -> KEPT W mem mem' X -> In (1, fpos) (frames S) ->
  sv8 W mem (frame_addr ly 1 fpos + 120) v -> sv8 W mem' (frame_addr ly 1 fpos + 120) v.
Proof.
  intros ly S W mem md mem' X fpos v HAR HX HK Hfin Hv. unfold sv8 in *.
  apply (akept_vm W mem); [|exact Hv]. intros x Hx. cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in Hx.
  apply (sm_frm_kept_x ly S W mem md mem' X 1 fpos x HAR HX HK Hfin).
  change (fs_frame_bytes 1) with 128. lia.
Qed.

Lemma sm_ainput_kept_x : forall cx ly S (W : world segs) mem md mem' X,
  ARE ly S W mem md -> XOK X -> KEPT W mem mem' X ->
  Z.of_nat (length (c_pl cx)) = c_n cx -> ainput_at B cx ly S W mem -> ainput_at B cx ly S W mem'.
Proof.
  intros cx ly S W mem md mem' X HAR HX HK Hlen (I1 & I2). split; [exact I1|].
  apply (akept_garr8 W mem); [|exact I2]. intros x Hx. rewrite length_map, Hlen in Hx.
  destruct I1 as [(Hn & _) | (Hn & Hin)]; [lia|].
  apply (sm_blk_kept_x ly S W mem md mem' X (c_p cx) (c_n cx) x HAR HX HK Hin ltac:(lia)).
  pose proof (req_size_pos (c_n cx) ltac:(lia)) as [_ Hq]. lia.
Qed.

Lemma sm_aslot_kept_x : forall ly S (W : world segs) mem md mem' F XG j o,
  ARE ly S W mem md -> alloc_ceiling + 1024 + ESTACK <= F -> XGOK XG -> KEPT W mem mem' (XS F XG) ->
  mem_grows (mrestrict (w_H W) mem) (mrestrict (w_H W) mem') -> (j < 4)%nat ->
  (forall a, rg_s fr_RG + ASRC * Z.of_nat j <= a < rg_s fr_RG + ASRC * Z.of_nat j + ASRC -> ~ inFP XG a) ->
  aslot B ly S W mem j o -> aslot B ly S W mem' j o.
Proof.
  intros ly S W mem md mem' F XG j o HAR HF HXG HK HGr Hj Hd Hs.
  assert (HXOK : XOK (XS F XG)) by (apply sm_xok; [exact HF | exact HXG]).
  pose proof sm_ceil_lo as Hac. assert (HES : ESTACK = 4096) by reflexivity.
  assert (KJ : forall a, rg_s fr_RG + ASRC * Z.of_nat j <= a < rg_s fr_RG + ASRC * Z.of_nat j + ASRC ->
      abyte_kept W mem W mem' a)
    by (intros a Ha; apply (sm_cell_kept W mem mem' F XG (rg_s fr_RG + ASRC * Z.of_nat j) ASRC HK);
        [lia | sm_rgl | sm_rgl | exact Hd | exact Ha]).
  unfold aslot in *. destruct o as [h|].
  - apply (asrc_at_kept B ly S W mem ly S W mem' _ h Hs).
    + apply (sm_akept_of W mem mem'). intros r Hr.
      exact (sm_asrc_fp_kept_x _ W mem mem' HXOK HK ly S md _ h HAR Hs (fun a Ha => KJ a Ha) r Hr).
    + exact (sm_asrc_blks_in B W mem ly S _ h Hs).
  - destruct Hs as [G1 G2]. split.
    + apply (akept_garr8 W mem); [|exact G1]. intros x Hx.
      rewrite repeat_length, Z2Nat.id in Hx by (unfold ASRC; lia). exact (KJ x Hx).
    + apply (akept_awr W mem); [|exact G2]. exact KJ.
Qed.

Lemma sm_arelay_kept_x : forall ly S (W : world segs) mem md mem' F XG G es,
  ARE ly S W mem md -> alloc_ceiling + 1024 + ESTACK <= F -> XGOK XG -> KEPT W mem mem' (XS F XG) ->
  (forall a, rg_src fr_RG <= a < rg_src fr_RG + 8 \/ rg_nsrc fr_RG <= a < rg_nsrc fr_RG + 4 \/
     rg_capsrc fr_RG <= a < rg_capsrc fr_RG + 4 -> ~ inFP XG a) ->
  arelay_at B fr_RG ly S W mem G es -> arelay_at B fr_RG ly S W mem' G es.
Proof.
  intros ly S W mem md mem' F XG G es HAR HF HXG HK Hd Hr.
  assert (HXOK : XOK (XS F XG)) by (apply sm_xok; [exact HF | exact HXG]).
  pose proof sm_ceil_lo as Hac. assert (HES : ESTACK = 4096) by reflexivity.
  apply (arelay_at_kept B fr_RG ly S W mem ly S W mem' G es Hr).
  - apply (sm_akept_of W mem mem'). intros r Hr'.
    assert (CK : forall lo n, 0 <= lo -> lo + n <= alloc_ceiling -> (forall a, lo <= a < lo + n -> ~ inFP XG a) ->
        sm_koff W mem mem' (lo, lo + n))
      by (intros lo n H0 H1 Hn a Ha; cbn [fst snd] in Ha;
          exact (sm_cell_kept W mem mem' F XG lo n HK ltac:(lia) H0 H1 Hn a Ha)).
    apply (sm_arelay_fp_kept_x _ W mem mem' HXOK HK fr_RG ly S md G es HAR Hr); [| | | exact Hr'];
      (apply CK; [sm_rgl | sm_rgl | intros y Hy; apply Hd; lia]).
  - exact (sm_arelay_blks_in B W mem fr_RG ly S G es Hr).
Qed.

Lemma sm_aout_kept_x : forall ly S (W : world segs) mem md mem' F XG c O mx no cap out,
  ARE ly S W mem md -> alloc_ceiling + 1024 + ESTACK <= F -> XGOK XG -> KEPT W mem mem' (XS F XG) ->
  (forall a, aout_glob B a -> ~ inFP XG a) ->
  aout_at B fr_RG ly S W mem c O mx no cap out -> aout_at B fr_RG ly S W mem' c O mx no cap out.
Proof.
  intros ly S W mem md mem' F XG c O mx no cap out HAR HF HXG HK Hd Ho.
  assert (HXOK : XOK (XS F XG)) by (apply sm_xok; [exact HF | exact HXG]).
  pose proof sm_ceil_lo as Hac. pose proof (sm_errno B TL) as (HE0 & HE1). assert (HES : ESTACK = 4096) by reflexivity.
  assert (CK : forall a, aout_glob B a -> abyte_kept W mem W mem' a).
  { intros a Ha. pose proof (Hd a Ha) as Hn. apply (sm_kept_ng W mem mem' F XG HK); [| | | exact Hn];
      unfold aout_glob in Ha; sm_rgl. }
  pose proof Ho as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
    _ & Hblk).
  apply (aout_at_kept B fr_RG ly S W mem ly S W mem' c O mx no cap out Ho).
  - intros r Hr a Ha. unfold aout_fp in Hr.
    destruct Hr as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|Hr]]]]]]]]]; cbn [fst snd] in Ha;
      try (apply CK; unfold aout_glob; lia).
    destruct (cap =? 0) eqn:Ec; [destruct Hr|]. destruct Hr as [<- | []]. apply Z.eqb_neq in Ec.
    cbn [fst snd] in Ha.
    destruct Hblk as [(Hc & _) | (Hcp & Hno & Hin & _)]; [lia|].
    apply (sm_blk_kept_x ly S W mem md mem' (XS F XG) out cap a HAR HXOK HK Hin ltac:(lia)).
    pose proof (req_size_pos cap ltac:(lia)) as [_ Hq]. lia.
  - intros b Hb. unfold aout_blks in Hb. destruct (cap =? 0) eqn:Ec; [destruct Hb|].
    apply Z.eqb_neq in Ec. destruct Hb as [<- | []].
    destruct Hblk as [(Hc & _) | (Hcp & Hno & Hin & _)]; [lia | exact Hin].
Qed.

Lemma sm_amodel_fl_x : forall ly S (W : world segs) mem md mem' F m i h (upd : hsrc -> hsrc) fo kx,
  ARE ly S W mem md -> alloc_ceiling + 1024 + ESTACK <= F ->
  KEPT W mem mem' (XS F [(rg_s fr_RG + ASRC * Z.of_nat i + fo, rg_s fr_RG + ASRC * Z.of_nat i + fo + 4)]) ->
  mem_grows (mrestrict (w_H W) mem) (mrestrict (w_H W) mem') ->
  amodel_at B ly S W mem m -> (i < 4)%nat -> nth i (lm_hs m) None = Some h ->
  same_but_flags h (upd h) ->
  ((fo = 8 /\ hs_closed (upd h) = 1 /\ hs_eintr (upd h) = hs_eintr h) \/
   (fo = 12 /\ hs_eintr (upd h) = 1 /\ hs_closed (upd h) = hs_closed h)) ->
  val_mem segs (arm W mem') (rg_s fr_RG + ASRC * Z.of_nat i + fo) 4 1 ->
  amodel_at B ly S W mem' (LM kx (upd_hs i upd (lm_hs m)) (lm_G m) (lm_es m) (lm_c m) (lm_O m)
    (lm_mx m) (lm_cap m) (lm_out m) (lm_gn m) (lm_nfd m)).
Proof.
  intros ly S W mem md mem' F m i h upd fo kx HAR HF HK HGr HM Hi Hnth Hsf Hfl Hnew.
  assert (Hfo : fo = 8 \/ fo = 12) by (destruct Hfl as [(-> & _) | (-> & _)]; [left | right]; reflexivity).
  pose proof sm_ceil_lo as Hac. pose proof (sm_errno B TL) as (HE0 & HE1). assert (HES : ESTACK = 4096) by reflexivity.
  set (HA := rg_s fr_RG + ASRC * Z.of_nat i) in *.
  set (XG := [(HA + fo, HA + fo + 4)]) in *.
  assert (NX : forall a, ~ (HA + fo <= a < HA + fo + 4) -> ~ inFP XG a).
  { intros a Hn Ha. unfold XG in Ha. apply inFP_cons in Ha as [Ha | Ha]; [exact (Hn Ha) | exact (inFP_nil a Ha)]. }
  assert (HXG : XGOK XG).
  { intros a Ha. unfold XG in Ha. apply inFP_cons in Ha as [Ha | Ha]; [unfold HA in Ha; sm_rgl | destruct (inFP_nil a Ha)]. }
  assert (HXOK : XOK (XS F XG)) by (apply sm_xok; [exact HF | exact HXG]).
  assert (CK : forall lo n, 0 <= lo -> lo + n <= alloc_ceiling ->
      (forall a, lo <= a < lo + n -> ~ (HA + fo <= a < HA + fo + 4)) ->
      forall a, lo <= a < lo + n -> abyte_kept W mem W mem' a).
  { intros lo n H0 H1 Hd. apply (sm_cell_kept W mem mem' F XG lo n HK); [lia | lia | lia |].
    intros a Ha. exact (NX a (Hd a Ha)). }
  pose proof HM as (M1 & M2 & M3 & M4 & M5 & M6 & M7 & M8 & M9 & M10 & M11 & M12 & M13).
  unfold amodel_at. cbn [lm_hs lm_G lm_es lm_c lm_O lm_mx lm_cap lm_out lm_gn lm_nfd].
  split; [rewrite upd_hs_length; exact M1|].
  split.
  { intros j Hj. destruct (Nat.eq_dec j i) as [-> | Hne].
    - rewrite (upd_hs_nth_same i upd (lm_hs m) h Hnth). unfold aslot.
      pose proof (M2 i Hi) as Hs. unfold aslot in Hs. rewrite Hnth in Hs.
      apply (sm_slot_store_x ly S W mem md mem' (XS F XG) HA h (upd h) fo HAR HXOK HK HGr Hs Hsf Hfl).
      + intros a Ha Hn Hin. unfold XS in Hin. apply inFP_cons in Hin as [Hin | Hin]; [unfold HA in Ha; sm_rgl|].
        apply inFP_cons in Hin as [Hin | Hin]; [unfold HA in Ha; sm_rgl|].
        exact (NX a Hn Hin).
      + unfold HA; sm_rgl.
      + unfold HA; sm_rgl.
      + exact Hnew.
    - rewrite (upd_hs_nth_other i upd (lm_hs m) j Hne).
      apply (sm_aslot_kept_x ly S W mem md mem' F XG j _ HAR HF HXG HK HGr Hj); [|exact (M2 j Hj)].
      intros a Ha. apply NX. unfold HA. sm_rgl. }
  split.
  { apply (sm_arelay_kept_x ly S W mem md mem' F XG (lm_G m) (lm_es m) HAR HF HXG HK); [|exact M3].
    intros a Ha. apply NX. unfold HA. sm_rgl. }
  split.
  { apply (sm_aout_kept_x ly S W mem md mem' F XG _ _ _ _ _ _ HAR HF HXG HK); [|exact M4].
    intros a Ha Hin. unfold XG in Hin. apply inFP_cons in Hin as [Hin | Hin]; [|exact (inFP_nil a Hin)].
    pose proof HERRHI as He.
    unfold aout_glob in Ha. unfold HA in Hin. sm_rgl. }
  split.
  { apply (agone_at_kept fr_RG W mem W mem' _ M5). intros r Hr a Ha. destruct Hr as [<- | []]. cbn [fst snd] in Ha.
    apply (CK (rg_gone fr_RG) 1); [sm_rgl | sm_rgl | intros y Hy; unfold HA; sm_rgl | exact Ha]. }
  split.
  { apply (alock_at_kept fr_RG W mem W mem' _ M6). intros r Hr a Ha. destruct Hr as [<- | []]. cbn [fst snd] in Ha.
    apply (CK (rg_lock fr_RG) 12); [sm_rgl | sm_rgl | intros y Hy; unfold HA; sm_rgl | exact Ha]. }
  split.
  { apply (awake_at_kept fr_RG W mem W mem' M7). intros r Hr a Ha. destruct Hr as [<- | []]. cbn [fst snd] in Ha.
    apply (CK (rg_wake fr_RG + 4) 4); [sm_rgl | sm_rgl | intros y Hy; unfold HA; sm_rgl | lia]. }
  split.
  { apply (akept_vm W mem); [|exact M8]. intros x Hx.
    apply (CK AG_NFD 4); [sm_rgl | sm_rgl | intros y Hy; unfold HA; sm_rgl | lia]. }
  split.
  { apply (akept_awr W mem); [|exact M9]. intros x Hx.
    apply (CK AG_NFD 4); [sm_rgl | sm_rgl | intros y Hy; unfold HA; sm_rgl | lia]. }
  split; [exact M10|].
  split.
  { apply (akept_vm W mem); [|exact M11]. intros x Hx.
    apply (CK AG_THREAD_UP 1); [sm_rgl | sm_rgl | intros y Hy; unfold HA; sm_rgl | lia]. }
  split.
  { destruct M12 as (lst & M12). exists lst. apply (akept_vm W mem); [|exact M12]. intros x Hx.
    apply (CK AG_LISTEN 4); [sm_rgl | sm_rgl | intros y Hy; unfold HA; sm_rgl | lia]. }
  apply (akept_awr W mem); [|exact M13]. intros x Hx.
  apply (CK AG_LISTEN 4); [sm_rgl | sm_rgl | intros y Hy; unfold HA; sm_rgl | lia].
Qed.

Let RUN := paj_run_x_x (PL := PL_fr) (PI := PB_fr) B PST ARx LAWS G_fr HG 0 [].

Let RUNTO := paj_run_to_x_x (PL := PL_fr) (PI := PB_fr) B PST ARx LAWS G_fr HG 0 [].

Let BR := paj_branch (PI := PB_fr).

Ltac sm_in := cbn [In jt_kept sm_fl_kept sm_mx_kept sm_df_kept]; repeat (first [left; reflexivity | right]).

Definition sm_fl_post_x (W : world segs) (regs : bvmap 5 word) (mem : word -> option byte) (STK sp0 : Z)
    (FP : list (Z * Z)) (ly0 : alayout) (S0 : astate) (Hp0 : list Z) (W0 : world segs) (mem0 : word -> option byte) (md0 : Model)
    (own : list (Z * Z)) (ly : alayout) (S : astate) (Hp : list Z) (kk F HA fo N6 : Z) : world segs -> config -> Prop :=
  fun W' c' => W' = W /\ exists regs' mem' md',
    c' = cfg_at segs (fr_B0 + AF_LLVM_latch) regs' mem' md' /\
    ajournal_gx_x segs B PST ARx G_fr 0 [] STK sp0 FP ly0 S0 Hp0 W0 mem0 md0 own ly S Hp W mem' md' kk /\
    KEPT W mem mem' (XS F [(HA + fo, HA + fo + 4)]) /\
    mem_grows (mrestrict (w_H W) mem) (mrestrict (w_H W) mem') /\
    val_mem segs (arm W mem') (F + 144) 8 N6 /\ val_mem segs (arm W mem') (HA + fo) 4 1 /\
    (forall r, In r sm_fl_kept -> getr regs' r = getr regs r).

Lemma sm_fl_run_x : forall (W : world segs) regs mem md STK sp0 FP ly0 S0 Hp0 (W0 : world segs) mem0 md0 own ly S Hp kk
    F HA fo N6 pc,
  (fo = 8 /\ pc = AF_arm_close) \/ (fo = 12 /\ pc = AF_arm_eintr) ->
  ajournal_gx_x segs B PST ARx G_fr 0 [] STK sp0 FP ly0 S0 Hp0 W0 mem0 md0 own ly S Hp W mem md kk ->
  getr regs 23 = w64 1 -> getr regs 9 = w64 F -> getr regs 21 = w64 HA -> getr regs 27 = w64 SB ->
  getr regs 6 = w64 N6 -> 0 <= N6 < 2 ^ 64 ->
  2 ^ 46 <= F <= 2 ^ 47 -> F mod 32 = 0 ->
  rg_s fr_RG <= HA <= rg_s fr_RG + 3 * ASRC -> HA mod 32 = 0 ->
  sp0 - STK <= F + 144 -> F + 152 <= sp0 ->
  (forall a, F + 144 <= a < F + 152 -> writable_at segs (arm W mem) a) ->
  (forall a, HA + fo <= a < HA + fo + 4 -> writable_at segs (arm W mem) a) ->
  azs B HA ASRC ->
  SRr segs W (cfg_at segs (fr_B0 + pc) regs mem md)
    (sm_fl_post_x W regs mem STK sp0 FP ly0 S0 Hp0 W0 mem0 md0 own ly S Hp kk F HA fo N6).
Proof.
  intros W regs mem md STK sp0 FP ly0 S0 Hp0 W0 mem0 md0 own ly S Hp kk F HA fo N6 pc Hcase HJ H23 H9 H21 H27 H6 HN6
    HF1 HF2 HH1 HH2 Hs1 Hs2 HW1 HW2 HZ.
  pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
  assert (HAR : ARE ly S W mem md) by (exists Hp; eapply ajournal_gx_AR_x; exact HJ).
  assert (HRS : rg_s fr_RG = 6131296) by reflexivity.
  assert (HAS : ASRC = 96) by reflexivity.
  assert (Hfo : fo = 8 \/ fo = 12) by (destruct Hcase as [(-> & _) | (-> & _)]; [left | right]; reflexivity).
  destruct (sm_fl_entry_x W regs mem ly S md F HA fo pc HAR H23 H9 H21 H27 HF1 HF2 ltac:(lia) HH2 Hfo HW1 HW2 HZ)
    as [HS SHOK].
  assert (HEI : img_env VAL A_LIM (Eimg (Ereg regs (@nil word)))) by apply Eimg_env.
  assert (HAE : env_agree 32 (Ereg regs (@nil word)) (Eimg (Ereg regs (@nil word))))
    by (split; [intros mm Hmm; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
  assert (EE : forall m (rr : bv 5), Z.of_nat m = bv_unsigned rr -> ew (Eimg (Ereg regs (@nil word))) m = getr regs rr)
    by (intros m rr Hm; pose proof (bv_unsigned_in_range 5 rr) as Hr5;
        change (bv_modulus 5) with 32 in Hr5; rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_nat; exact Hm).
  assert (E9 : ew (Eimg (Ereg regs (@nil word))) 9 = w64 F) by (rewrite (EE 9%nat 9%bv eq_refl); exact H9).
  assert (E21 : ew (Eimg (Ereg regs (@nil word))) 21 = w64 HA) by (rewrite (EE 21%nat 21%bv eq_refl); exact H21).
  assert (E23 : ew (Eimg (Ereg regs (@nil word))) 23 = w64 1) by (rewrite (EE 23%nat 23%bv eq_refl); exact H23).
  assert (E6 : ew (Eimg (Ereg regs (@nil word))) 6 = w64 N6) by (rewrite (EE 6%nat 6%bv eq_refl); exact H6).
  assert (E9b : base_val (Eimg (Ereg regs (@nil word))) (Some 9%nat) = F)
    by (cbn [base_val]; rewrite E9; apply unsigned_lit_small; lia).
  assert (E21b : base_val (Eimg (Ereg regs (@nil word))) (Some 21%nat) = HA)
    by (cbn [base_val]; rewrite E21; apply unsigned_lit_small; rewrite HRS, HAS in HH1; lia).
  clear EE.
  set (E := Eimg (Ereg regs (@nil word))) in *. clearbody E.
  unfold cfg_at. change (w64 (fr_B0 + pc)) with (Z_to_bv 64 (BASE + pc)).
  destruct Hcase as [(-> & ->) | (-> & ->)].
  all: paj_run_to_tok_x RUNTO HS HJ SHOK SMspan AF_LLVM_latch.
  1,3: apply awr_ok_x_cons;
    [ intros a Ha; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi] in Ha; rewrite E9b in Ha;
      left; split; [left; lia | lia]
    | apply awr_ok_x_cons_g;
      [ intros a Ha; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi] in Ha; rewrite E21b in Ha;
        apply HGs; rewrite HAS; lia
      | apply awr_ok_x_nil ] ].
  all: lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
    assert (HAE2 : env_agree 32 (Ereg regs (@nil word)) Ev)
      by (split; [intros q Hq; rewrite ?ew_ewset_other by lia; exact (proj1 HAE q Hq)
                 | rewrite ?ed_ewset; exact (proj2 HAE)]) end.
  all: pose proof (regs_kept_of_st_ok_pi (PI := PB_fr) _ _ _ regs (@nil word) sm_fl_kept HS HAE2
    ltac:(vm_compute; reflexivity)) as KR.
  all: cbn [ms_regs restrict] in KR.
  all: pose proof (st_ok_pi_region_nth _ _ _ 0 _ HS eq_refl) as RG0.
  all: pose proof (st_ok_pi_region_nth _ _ _ 1 _ HS eq_refl) as RG1.
  all: cbn [ms_mem restrict] in RG0, RG1.
  all: assert (V144 : val_mem segs (arm W (ms_mem ms)) (F + 144) 8 N6)
    by (apply (field_of_region E _ 9%nat F _ _ _ _ _ 144 8%N (SOff 6 0) N6 RG0);
        [ rewrite E9; apply unsigned_lit_small; lia
        | left; reflexivity
        | cbn [sv_denot]; rewrite E6, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
        | zside | zside ]).
  all: lazymatch type of RG1 with region_ok _ _ _ (YP09.mkRegion _ ?o _ _ _ _) =>
    assert (VHA : val_mem segs (arm W (ms_mem ms)) (HA + o) 4 1)
      by (apply (field_of_region E _ 21%nat HA _ _ _ _ _ o 4%N (SOff 23 0) 1 RG1);
          [ rewrite E21; apply unsigned_lit_small; rewrite HRS, HAS in HH1; lia
          | left; reflexivity
          | cbn [sv_denot]; rewrite E23, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
          | zside | zside ]) end.
  all: pmkst HS.
  all: apply SRr_ret.
  all: split; [reflexivity|].
  all: exists (ms_regs ms), (ms_mem ms), (with_vm_backing (m_vm_lazy md) mat md).
  all: split; [reflexivity|].
  all: split; [exact HJ|].
  all: split; [intros a Ha Hn; split;
    [ apply (aview_kept_out _ _ _ _ _ HFr a Ha); intros (r & Hin & Hr); cbn [ss_mem sm_fl_regions In] in Hin;
      destruct Hin as [<- | [<- | []]]; cbn [YP09.r_base YP09.r_wlo YP09.r_whi] in Hr;
      [ rewrite E9b in Hr; apply Hn; unfold XS; apply inFP_cons; right; apply inFP_cons; left; lia
      | rewrite E21b in Hr; apply Hn; unfold XS; apply inFP_cons; right; apply inFP_cons; right;
        apply inFP_cons; left; lia ]
    | exact (sm_wkeep W mem (ms_mem ms) a HG0) ] |].
  all: split; [exact HG0|].
  all: split; [exact V144|].
  all: split; [exact VHA|].
  all: exact KR.
Qed.

Lemma sm_fl_walk_x : forall (ii fo : Z) (upd : hsrc -> hsrc) (mk : lfcx -> lmod -> nat -> lmod) cx Hp t W c,
  (ii = 3 /\ fo = 8) \/ (ii = 6 /\ fo = 12) ->
  (forall h, same_but_flags h (upd h)) ->
  (forall h, (fo = 8 /\ hs_closed (upd h) = 1 /\ hs_eintr (upd h) = hs_eintr h) \/
             (fo = 12 /\ hs_eintr (upd h) = 1 /\ hs_closed (upd h) = hs_closed h)) ->
  (forall m0 i0, mk cx m0 i0 = LM (sm_kn cx m0) (upd_hs i0 upd (lm_hs m0)) (lm_G m0) (lm_es m0)
      (lm_c m0) [] (lm_mx m0) (lm_cap m0) (lm_out m0) (lm_gn m0) (lm_nfd m0)) ->
  (forall m0 i0, RINV cx t m0 ->
     pick (lm_hs m0) (if lm_k m0 + 1 <? c_n cx then in_byte cx (lm_k m0 + 1) else 0) = Some i0 ->
     RINV cx (t + 1) (mk cx m0 i0)) ->
  (forall m0 i0 ly0 S0, LSx cx t m0 ly0 S0 ->
     pick (lm_hs m0) (if lm_k m0 + 1 <? c_n cx then in_byte cx (lm_k m0 + 1) else 0) = Some i0 ->
     LSx cx (t + 1) (mk cx m0 i0) ly0 S0) ->
  (forall h, asrc_blks (upd h) = asrc_blks h) ->
  lf_base_x B MT XM_LIB RLO RHI fr_live_pre LIBROOM NP G_fr ARx cx Hp -> INV_A_x B NP G_fr fr_FP PST ARx LSx RINV ii cx Hp t W c ->
  SRr segs W c (INV_K_x B NP G_fr fr_FP PST ARx LSx RINV cx Hp t).
Proof.
  intros ii fo upd mk cx Hp t W c Hcase Hsf Hfl Hmk Hri Hls Hblks HB HA.
  destruct HA as (regs & regsD & mem & md & Hc & Hkept & HopD & _ & HROM & HLF).
  destruct HLF as (own & ly3 & S3 & Hp3 & kk & m & fpos & HJ & Hown & Hframe & Hflag & Hmodel & Hinput & Hrom & Hsep &
    HLS & HNP & HRINV & HRD).
  subst own.
  pose proof HRD as (Hcommon & HD25 & Htb & Hkb & HO & Hoprest).
  cbv zeta in Hoprest. destruct Hoprest as (Hop11 & Hpick).
  assert (Hiirange : 0 <= ii <= 9) by (destruct Hcase as [[-> _]|[-> _]]; lia).
  assert (Hopeq : in_byte cx (lm_k m) mod 10 = ii).
  { pose proof (Z.mod_pos_bound (in_byte cx (lm_k m)) 10 ltac:(lia)) as Hmb.
    apply (f_equal bv_unsigned) in HopD. rewrite Hop11 in HopD.
    rewrite !unsigned_lit_small in HopD by lia. lia. }
  rewrite Hopeq in Hpick.
  assert (Hpk3 : picks ii = true) by (destruct Hcase as [[-> _]|[-> _]]; reflexivity).
  rewrite Hpk3 in Hpick. cbv zeta in Hpick. destruct Hpick as (HD20 & HD6 & Hpk).
  destruct Hpk as [(i & Hpicki & HD21) | (Hbad & _)];
    [| exfalso; destruct Hcase as [[Hii _]|[Hii _]]; rewrite Hii in Hbad; discriminate Hbad].
  destruct (sm_pick (lm_hs m) _ i Hpicki) as (Hilen & hsome & Hnthi).
  pose proof Hmodel as (Hlen4 & Hslots & _).
  rewrite Hlen4 in Hilen.
  pose proof (Hslots i Hilen) as Haslot. unfold aslot in Haslot. rewrite Hnthi in Haslot.
  assert (HARx : ARx ly3 S3 Hp3 W mem md) by (eapply ajournal_gx_AR_x; exact HJ).
  assert (HAR : ARE ly3 S3 W mem md) by (exists Hp3; exact HARx).
  assert (Hfin : In (1, fpos) (frames S3)).
  { pose proof HJ as (_ & _ & (memS & HJ0 & _) & _). pose proof HJ0 as (_ & _ & _ & _ & _ & Hfrs & _).
    rewrite Hfrs. left. reflexivity. }
  destruct HB as (HAI & Hpre). pose proof Hpre as (Hafn & _ & _ & _ & _ & Hlen & _).
  pose proof Hafn as (_ & _ & _ & _ & _ & Hstk & _).
  pose proof Hstk as (Hsp16 & HstkK & Hceil & Hlo & Hhi & Hhi2 & _).
  set (sp0 := spZ (c_regs cx)) in *.
  set (HAc := rg_s fr_RG + ASRC * Z.of_nat i) in *.
  assert (HRS : rg_s fr_RG = 6131296) by reflexivity.
  assert (HAS : ASRC = 96) by reflexivity.
  assert (HSTK : LLVMF_STK = 32768) by reflexivity.
  pose proof sm_ceil_lo as Hac. assert (HES : ESTACK = 4096) by reflexivity.
  assert (Hsp0 : alloc_ceiling + 32768 <= sp0 <= 2 ^ 47) by lia.
  pose proof (Z.mod_pos_bound (sp0 - 320) 32 ltac:(lia)) as Hm32.
  assert (HFeq : lf_F cx = sp0 - 320 - (sp0 - 320) mod 32) by reflexivity.
  assert (HFbound : 2 ^ 46 <= lf_F cx <= 2 ^ 47) by lia.
  assert (HFmod : lf_F cx mod 32 = 0)
    by (rewrite HFeq; rewrite Zminus_mod, Zmod_mod, Z.sub_diag; reflexivity).
  assert (Hi4 : (i < 4)%nat) by lia.
  assert (HHbound : rg_s fr_RG <= HAc <= rg_s fr_RG + 3 * ASRC) by (unfold HAc; rewrite HAS; lia).
  assert (HHmod : HAc mod 32 = 0)
    by (unfold HAc; rewrite HRS, HAS; replace (6131296 + 96 * Z.of_nat i) with ((191603 + 3 * Z.of_nat i) * 32) by lia;
        apply Z_mod_mult).
  assert (Hfo : fo = 8 \/ fo = 12) by (destruct Hcase as [[_ ->]|[_ ->]]; [left|right]; reflexivity).
  (* the registers: regs agrees with regsD outside a0 / a1 *)
  assert (KD : forall r : bv 5, In r jt_kept -> getr regs r = getr regsD r) by exact Hkept.
  pose proof Hcommon as (C2 & C8 & C9 & C18 & C19 & C23 & C24 & C26 & C27 & C3 & C4).
  assert (Hr23 : getr regs 23 = w64 1) by (rewrite (KD 23%bv ltac:(sm_in)); exact C23).
  assert (Hr9 : getr regs 9 = w64 (lf_F cx)) by (rewrite (KD 9%bv ltac:(sm_in)); exact C9).
  assert (Hr27 : getr regs 27 = w64 SB) by (rewrite (KD 27%bv ltac:(sm_in)); exact C27).
  assert (Hr21 : getr regs 21 = w64 HAc) by (rewrite (KD 21%bv ltac:(sm_in)); exact HD21).
  set (k1 := if lm_k m + 1 <? c_n cx then lm_k m + 2 else lm_k m + 1) in *.
  assert (Hk1 : lm_k m + 1 <= k1 <= c_n cx)
    by (unfold k1; destruct (lm_k m + 1 <? c_n cx) eqn:Ek; [apply Z.ltb_lt in Ek | apply Z.ltb_ge in Ek]; lia).
  assert (Hn26 : c_n cx < 2 ^ 26)
    by (pose proof Hpre as (_ & _ & _ & _ & Hpn & _); destruct Hpn as [(H0 & _) | (H0 & _)]; lia).
  assert (Hr6 : getr regs 6 = w64 (c_n cx - k1)) by (rewrite (KD 6%bv ltac:(sm_in)); exact HD6).
  pose proof Hframe as (_ & Hawr & _).
  assert (HW1 : forall a, lf_F cx + 144 <= a < lf_F cx + 152 -> writable_at segs (arm W mem) a).
  { intros a Ha. replace a with (lf_F cx + (a - lf_F cx)) by lia. apply Hawr. lia. }
  pose proof Haslot as (_ & _ & _ & _ & Hs5 & _).
  assert (HW2 : forall a, HAc + fo <= a < HAc + fo + 4 -> writable_at segs (arm W mem) a).
  { intros a Ha. replace a with (HAc + (a - HAc)) by lia. apply Hs5. unfold ASRC; lia. }
  assert (HZslot : azs B HAc ASRC) by (apply (azs_sub B (rg_s fr_RG) (4 * ASRC)); [exact HZS | lia | unfold HAc; lia]).
  assert (Hpcs : (fo = 8 /\ fr_arm ii = AF_arm_close) \/ (fo = 12 /\ fr_arm ii = AF_arm_eintr))
    by (destruct Hcase as [(-> & ->) | (-> & ->)]; [left | right]; split; reflexivity).
  rewrite Hc.
  eapply SRr_mono.
  { exact (sm_fl_run_x W regs mem md LLVMF_STK sp0 (lf_FP fr_FP cx) (c_ly cx) (c_S cx) Hp (c_W cx) (c_mem cx) (c_md cx)
      [(1, fpos)] ly3 S3 Hp3 kk (lf_F cx) HAc fo (c_n cx - k1) (fr_arm ii) Hpcs HJ Hr23 Hr9 Hr21 Hr27 Hr6
      ltac:(lia) HFbound HFmod HHbound HHmod ltac:(lia) ltac:(lia) HW1 HW2 HZslot). }
  intros W' c' _ (-> & regs' & mem' & md' & -> & HJ' & KP & HGr & V144 & VHA & KR).
  set (XG := [(HAc + fo, HAc + fo + 4)]) in *.
  assert (HXG : XGOK XG).
  { intros a Ha. unfold XG in Ha. apply inFP_cons in Ha as [Ha | Ha]; [unfold HAc in Ha; sm_rgl | destruct (inFP_nil a Ha)]. }
  assert (HXOK : XOK (XS (lf_F cx) XG)) by (apply sm_xok; [lia | exact HXG]).
  assert (KK : forall r : bv 5, In r sm_fl_kept -> In r jt_kept -> getr regs' r = getr regsD r)
    by (intros r H1 H2; rewrite (KR r H1); exact (KD r H2)).
  exists regs', mem', md'. split; [reflexivity|].
  split; [exact (sm_jt_kept W mem mem' _ HXOK KP HROM)|].
  exists [(1, fpos)], ly3, S3, Hp3, kk, (mk cx m i), fpos.
  split; [exact HJ'|]. split; [reflexivity|].
  split; [exact (sm_aframe_kept_x cx ly3 S3 W mem md mem' fpos XG HAR Hfin Hsp0 HXG KP HGr Hframe)|].
  split; [exact (sm_flag_kept_x ly3 S3 W mem md mem' _ fpos _ HAR HXOK KP Hfin Hflag)|].
  split.
  { rewrite Hmk.
    pose proof (sm_amodel_fl_x ly3 S3 W mem md mem' (lf_F cx) m i hsome upd fo (sm_kn cx m) HAR ltac:(lia) KP HGr
      Hmodel Hi4 Hnthi (Hsf hsome) (Hfl hsome) VHA) as HM2.
    rewrite HO in HM2. exact HM2. }
  split; [exact (sm_ainput_kept_x cx ly3 S3 W mem md mem' _ HAR HXOK KP (eq_sym Hlen) Hinput)|].
  split; [exact (sm_rom_kept W mem mem' _ HXOK KP Hrom)|].
  split; [rewrite Hmk; apply (sm_sep_fl B fr_FP); [exact Hblks | exact Hsep]|].
  split; [exact (Hls m i ly3 S3 HLS Hpicki)|].
  split; [exact HNP|].
  split; [exact (Hri m i HRINV Hpicki)|].
  unfold lregs_K, lregs_common. rewrite Hmk. cbn [lm_k].
  assert (Hkn : sm_kn cx m = k1) by reflexivity. rewrite Hkn.
  split.
  { split; [rewrite (KK 2%bv ltac:(sm_in) ltac:(sm_in)); exact C2|].
    split; [rewrite (KK 8%bv ltac:(sm_in) ltac:(sm_in)); exact C8|].
    split; [rewrite (KK 9%bv ltac:(sm_in) ltac:(sm_in)); exact C9|].
    split; [rewrite (KK 18%bv ltac:(sm_in) ltac:(sm_in)); exact C18|].
    split; [rewrite (KK 19%bv ltac:(sm_in) ltac:(sm_in)); exact C19|].
    split; [rewrite (KK 23%bv ltac:(sm_in) ltac:(sm_in)); exact C23|].
    split; [rewrite (KK 24%bv ltac:(sm_in) ltac:(sm_in)); exact C24|].
    split; [rewrite (KK 26%bv ltac:(sm_in) ltac:(sm_in)); exact C26|].
    split; [rewrite (KK 27%bv ltac:(sm_in) ltac:(sm_in)); exact C27|].
    split; [rewrite (KK 3%bv ltac:(sm_in) ltac:(sm_in)); exact C3|].
    rewrite (KK 4%bv ltac:(sm_in) ltac:(sm_in)); exact C4. }
  split; [rewrite (KK 25%bv ltac:(sm_in) ltac:(sm_in)); exact HD25|].
  split; [exact Htb|].
  split; [rewrite (KK 20%bv ltac:(sm_in) ltac:(sm_in)); exact HD20|].
  split; [unfold sv8; exact V144|].
  lia.
Qed.

Theorem lf_arm_close_x : forall cx Hp t W c,
  lf_base_x B MT XM_LIB RLO RHI fr_live_pre LIBROOM NP G_fr ARx cx Hp -> INV_A_x B NP G_fr fr_FP PST ARx LSx RINV 3 cx Hp t W c ->
  SRr segs W c (INV_K_x B NP G_fr fr_FP PST ARx LSx RINV cx Hp t).
Proof.
  intros cx Hp t W c HB HA.
  exact (sm_fl_walk_x 3 8 upd_closed sm_close cx Hp t W c (or_introl (conj eq_refl eq_refl)) same_but_flags_closed
    (fun h => or_introl (conj eq_refl (conj eq_refl eq_refl))) (fun m0 i0 => eq_refl)
    (fun m0 i0 H Hpk => RI_close cx t m0 i0 H Hpk) (fun m0 i0 ly0 S0 H Hpk => LS_close cx t m0 i0 ly0 S0 H Hpk)
    upd_closed_blks HB HA).
Qed.

Theorem lf_arm_eintr_x : forall cx Hp t W c,
  lf_base_x B MT XM_LIB RLO RHI fr_live_pre LIBROOM NP G_fr ARx cx Hp -> INV_A_x B NP G_fr fr_FP PST ARx LSx RINV 6 cx Hp t W c ->
  SRr segs W c (INV_K_x B NP G_fr fr_FP PST ARx LSx RINV cx Hp t).
Proof.
  intros cx Hp t W c HB HA.
  exact (sm_fl_walk_x 6 12 upd_eintr sm_eintr cx Hp t W c (or_intror (conj eq_refl eq_refl)) same_but_flags_eintr
    (fun h => or_intror (conj eq_refl (conj eq_refl eq_refl))) (fun m0 i0 => eq_refl)
    (fun m0 i0 H Hpk => RI_eintr cx t m0 i0 H Hpk) (fun m0 i0 ly0 S0 H Hpk => LS_eintr cx t m0 i0 ly0 S0 H Hpk)
    upd_eintr_blks HB HA).
Qed.

Ltac sm_kv KV H :=
  apply KV; [intros x Hx; cbn in Hx; unfold aout_glob; sm_rgl | intros x Hx; cbn in Hx; sm_rgl
            | intros x Hx; cbn in Hx; sm_rgl | exact H].

Lemma sm_aout_mx_x : forall ly S (W : world segs) mem md mem' F c O mx no cap out u,
  ARE ly S W mem md -> alloc_ceiling + 1024 + ESTACK <= F -> KEPT W mem mem' (XS F sm_mx_XG) ->
  mem_grows (mrestrict (w_H W) mem) (mrestrict (w_H W) mem') ->
  aout_at B fr_RG ly S W mem c O mx no cap out -> 0 <= u <= 255 ->
  val_mem segs (arm W mem') (rg_send_max fr_RG) 8 u -> val_mem segs (arm W mem') (rg_send_eintr fr_RG) 1 1 ->
  aout_at B fr_RG ly S W mem' (CTL (ct_cl c) (ct_br c) (ct_dd c) 1 (ct_ev c)) O u no cap out.
Proof.
  intros ly S W mem md mem' F c O mx no cap out u HAR HF HK HGr Ho Hu Vmx Vei.
  assert (HXOK : XOK (XS F sm_mx_XG)) by (apply sm_xok; [exact HF | exact sm_mx_xgok]).
  pose proof sm_ceil_lo as Hac. pose proof (sm_errno B TL) as (HE0 & HE1). pose proof HERRHI as HEH.
  assert (HES : ESTACK = 4096) by reflexivity.
  assert (CK : forall a, aout_glob B a -> ~ (rg_send_max fr_RG <= a < rg_send_max fr_RG + 8) ->
      ~ (rg_send_eintr fr_RG <= a < rg_send_eintr fr_RG + 1) -> abyte_kept W mem W mem' a).
  { intros a Ha H1 H2. apply (sm_kept_ng W mem mem' F sm_mx_XG HK);
      [unfold aout_glob in Ha; sm_rgl | unfold aout_glob in Ha; sm_rgl | unfold aout_glob in Ha; sm_rgl |].
    intros Hin. apply sm_inFP2 in Hin. destruct Hin as [Hin | Hin]; [exact (H1 Hin) | exact (H2 Hin)]. }
  assert (KV : forall a n v, (forall x, a <= x < a + Z.of_nat n -> aout_glob B x) ->
      (forall x, a <= x < a + Z.of_nat n -> ~ (rg_send_max fr_RG <= x < rg_send_max fr_RG + 8)) ->
      (forall x, a <= x < a + Z.of_nat n -> ~ (rg_send_eintr fr_RG <= x < rg_send_eintr fr_RG + 1)) ->
      val_mem segs (arm W mem) a n v -> val_mem segs (arm W mem') a n v).
  { intros a n v H1 H2 H3 Hv. apply (akept_vm W mem); [|exact Hv].
    intros x Hx. apply CK; [exact (H1 x Hx) | exact (H2 x Hx) | exact (H3 x Hx)]. }
  destruct Ho as (O1 & O2 & O3 & O4 & O5 & O6 & O7 & O8 & O9 & O10 & O11 & O12 & O13 & O14 & O15 & O16 & O17 & O18 &
    O19 & O20 & O21 & O22 & O23 & O24 & O25 & O26).
  unfold aout_at. cbn [ct_cl ct_br ct_dd ct_ei ct_ev].
  split; [exact Vmx|]. split; [exact (sm_awr W mem mem' _ _ HGr O2)|].
  split; [sm_kv KV O3|]. split; [exact (sm_awr W mem mem' _ _ HGr O4)|].
  split; [sm_kv KV O5|]. split; [exact (sm_awr W mem mem' _ _ HGr O6)|].
  split; [sm_kv KV O7|]. split; [exact (sm_awr W mem mem' _ _ HGr O8)|].
  split; [sm_kv KV O9|]. split; [exact (sm_awr W mem mem' _ _ HGr O10)|].
  split; [sm_kv KV O11|]. split; [exact (sm_awr W mem mem' _ _ HGr O12)|].
  split; [sm_kv KV O13|]. split; [exact (sm_awr W mem mem' _ _ HGr O14)|].
  split; [exact Vei|]. split; [exact (sm_awr W mem mem' _ _ HGr O16)|].
  split; [sm_kv KV O17|]. split; [exact (sm_awr W mem mem' _ _ HGr O18)|].
  split; [exact O19|]. split; [exact O20|]. split; [exact O21|]. split; [exact O22|].
  split; [right; reflexivity|]. split; [lia|]. split; [exact O25|].
  destruct O26 as [O26 | (Hc & Hno & Hin & junk & Hj & Hg)]; [left; exact O26 | right].
  split; [exact Hc|]. split; [exact Hno|]. split; [exact Hin|]. exists junk. split; [exact Hj|].
  apply (akept_garr8 W mem); [|exact Hg]. intros x Hx. unfold bzs in Hx. rewrite length_map, length_app, Nat2Z.inj_add in Hx.
  apply (sm_blk_kept_x ly S W mem md mem' (XS F sm_mx_XG) out cap x HAR HXOK HK Hin ltac:(lia)).
  pose proof (req_size_pos cap ltac:(lia)) as [_ Hq]. lia.
Qed.

Lemma sm_amodel_mx_x : forall ly S (W : world segs) mem md mem' F cx m u,
  ARE ly S W mem md -> alloc_ceiling + 1024 + ESTACK <= F ->
  KEPT W mem mem' (XS F sm_mx_XG) -> mem_grows (mrestrict (w_H W) mem) (mrestrict (w_H W) mem') ->
  amodel_at B ly S W mem m -> lm_O m = [] -> 0 <= u <= 255 ->
  val_mem segs (arm W mem') (rg_send_max fr_RG) 8 u -> val_mem segs (arm W mem') (rg_send_eintr fr_RG) 1 1 ->
  amodel_at B ly S W mem' (sm_sendmax cx m u).
Proof.
  intros ly S W mem md mem' F cx m u HAR HF HK HGr HM HO Hu Vmx Vei.
  pose proof sm_ceil_lo as Hac. pose proof sm_mx_xgok as HXG.
  assert (NX : forall lo n, (forall a, lo <= a < lo + n -> ~ (rg_send_max fr_RG <= a < rg_send_max fr_RG + 8) /\
      ~ (rg_send_eintr fr_RG <= a < rg_send_eintr fr_RG + 1)) -> forall a, lo <= a < lo + n -> ~ inFP sm_mx_XG a).
  { intros lo n Hd a Ha Hin. apply sm_inFP2 in Hin. destruct (Hd a Ha) as [N1 N2].
    destruct Hin as [Hin | Hin]; [exact (N1 Hin) | exact (N2 Hin)]. }
  assert (CK : forall lo n, 0 <= lo -> lo + n <= alloc_ceiling ->
      (forall a, lo <= a < lo + n -> ~ (rg_send_max fr_RG <= a < rg_send_max fr_RG + 8) /\
        ~ (rg_send_eintr fr_RG <= a < rg_send_eintr fr_RG + 1)) ->
      forall a, lo <= a < lo + n -> abyte_kept W mem W mem' a).
  { intros lo n H0 H1 Hd. apply (sm_cell_kept W mem mem' F sm_mx_XG lo n HK); [lia | lia | lia | exact (NX lo n Hd)]. }
  pose proof HM as (M1 & M2 & M3 & M4 & M5 & M6 & M7 & M8 & M9 & M10 & M11 & M12 & M13).
  unfold amodel_at, sm_sendmax. cbn [lm_hs lm_G lm_es lm_c lm_O lm_mx lm_cap lm_out lm_gn lm_nfd].
  split; [exact M1|].
  split.
  { intros j Hj. apply (sm_aslot_kept_x ly S W mem md mem' F sm_mx_XG j _ HAR HF HXG HK HGr Hj); [|exact (M2 j Hj)].
    apply NX. intros a Ha. split; sm_rgl. }
  split.
  { apply (sm_arelay_kept_x ly S W mem md mem' F sm_mx_XG (lm_G m) (lm_es m) HAR HF HXG HK); [|exact M3].
    intros a Ha Hin. apply sm_inFP2 in Hin. sm_rgl. }
  split.
  { rewrite HO in M4. exact (sm_aout_mx_x ly S W mem md mem' F _ _ _ _ _ _ u HAR HF HK HGr M4 Hu Vmx Vei). }
  split.
  { apply (agone_at_kept fr_RG W mem W mem' _ M5). intros r Hr a Ha. destruct Hr as [<- | []]. cbn [fst snd] in Ha.
    apply (CK (rg_gone fr_RG) 1); [sm_rgl | sm_rgl | intros y Hy; split; sm_rgl | exact Ha]. }
  split.
  { apply (alock_at_kept fr_RG W mem W mem' _ M6). intros r Hr a Ha. destruct Hr as [<- | []]. cbn [fst snd] in Ha.
    apply (CK (rg_lock fr_RG) 12); [sm_rgl | sm_rgl | intros y Hy; split; sm_rgl | exact Ha]. }
  split.
  { apply (awake_at_kept fr_RG W mem W mem' M7). intros r Hr a Ha. destruct Hr as [<- | []]. cbn [fst snd] in Ha.
    apply (CK (rg_wake fr_RG + 4) 4); [sm_rgl | sm_rgl | intros y Hy; split; sm_rgl | lia]. }
  split.
  { apply (akept_vm W mem); [|exact M8]. intros x Hx.
    apply (CK AG_NFD 4); [sm_rgl | sm_rgl | intros y Hy; split; sm_rgl | lia]. }
  split.
  { apply (akept_awr W mem); [|exact M9]. intros x Hx.
    apply (CK AG_NFD 4); [sm_rgl | sm_rgl | intros y Hy; split; sm_rgl | lia]. }
  split; [exact M10|].
  split.
  { apply (akept_vm W mem); [|exact M11]. intros x Hx.
    apply (CK AG_THREAD_UP 1); [sm_rgl | sm_rgl | intros y Hy; split; sm_rgl | lia]. }
  split.
  { destruct M12 as (lst & M12). exists lst. apply (akept_vm W mem); [|exact M12]. intros x Hx.
    apply (CK AG_LISTEN 4); [sm_rgl | sm_rgl | intros y Hy; split; sm_rgl | lia]. }
  apply (akept_awr W mem); [|exact M13]. intros x Hx.
  apply (CK AG_LISTEN 4); [sm_rgl | sm_rgl | intros y Hy; split; sm_rgl | lia].
Qed.

Definition sm_mx_post_x (W : world segs) (regs : bvmap 5 word) (mem : word -> option byte) (STK sp0 : Z)
    (FP : list (Z * Z)) (ly0 : alayout) (S0 : astate) (Hp0 : list Z) (W0 : world segs) (mem0 : word -> option byte) (md0 : Model)
    (own : list (Z * Z)) (ly : alayout) (S : astate) (Hp : list Z) (kk F P1 N1 u : Z) : world segs -> config -> Prop :=
  fun W' c' => W' = W /\ exists regs' mem' md',
    c' = cfg_at segs (fr_B0 + AF_LLVM_latch) regs' mem' md' /\
    ajournal_gx_x segs B PST ARx G_fr 0 [] STK sp0 FP ly0 S0 Hp0 W0 mem0 md0 own ly S Hp W mem' md' kk /\
    KEPT W mem mem' (XS F sm_mx_XG) /\
    mem_grows (mrestrict (w_H W) mem) (mrestrict (w_H W) mem') /\
    val_mem segs (arm W mem') (F + 144) 8 (if N1 =? 0 then 0 else N1 - 1) /\
    val_mem segs (arm W mem') (rg_send_max fr_RG) 8 u /\ val_mem segs (arm W mem') (rg_send_eintr fr_RG) 1 1 /\
    (forall r, In r sm_mx_kept -> getr regs' r = getr regs r) /\
    getr regs' 20 = w64 (if N1 =? 0 then P1 else P1 + 1).

Lemma sm_mx_run_x : forall (W : world segs) regs mem md STK sp0 FP ly0 S0 Hp0 (W0 : world segs) mem0 md0 own ly S Hp kk
    F P1 N1 kb,
  ajournal_gx_x segs B PST ARx G_fr 0 [] STK sp0 FP ly0 S0 Hp0 W0 mem0 md0 own ly S Hp W mem md kk ->
  getr regs 23 = w64 1 -> getr regs 9 = w64 F -> getr regs 27 = w64 SB -> getr regs 20 = w64 P1 ->
  getr regs 6 = w64 N1 -> 0 <= N1 < 2 ^ 26 ->
  2 ^ 46 <= F <= 2 ^ 47 -> F mod 32 = 0 -> 4096 <= P1 <= 2 ^ 47 - 16 -> 0 <= kb < 256 ->
  sp0 - STK <= F + 144 -> F + 152 <= sp0 ->
  (N1 <> 0 -> P1 + 1 <= 0x10000 \/ 0x5fc000 <= P1) ->
  (N1 <> 0 -> P1 + 1 <= kLowShadowBeg \/ kHighMemBeg <= P1) ->
  (N1 <> 0 -> P1 + 1 <= F) ->
  (N1 <> 0 -> val_mem segs (arm W mem) P1 1 kb) ->
  (N1 <> 0 -> range_addressable (aview segs (w_H W) mem) SHADOW_OFF P1 1) ->
  sv8 W mem (F + 56) 0x5d956c -> sv8 W mem (F + 72) 0x5d9550 ->
  (forall a, F + 144 <= a < F + 152 -> writable_at segs (arm W mem) a) ->
  awr W mem (rg_send_max fr_RG) 8 -> awr W mem (rg_send_eintr fr_RG) 1 ->
  SRr segs W (cfg_at segs (fr_B0 + AF_arm_sendmax) regs mem md)
    (sm_mx_post_x W regs mem STK sp0 FP ly0 S0 Hp0 W0 mem0 md0 own ly S Hp kk F P1 N1 (if N1 =? 0 then 0 else kb)).
Proof.
  intros W regs mem md STK sp0 FP ly0 S0 Hp0 W0 mem0 md0 own ly S Hp kk F P1 N1 kb HJ H23 H9 H27 H20 H6 HN1
    HF1 HF2 HP Hkb Hs1 Hs2 HPi HPa HPc MB RA M56 M72 HW1 HWmx HWei.
  pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
  assert (HRmx : rg_send_max fr_RG = 0x5d8dc0) by reflexivity.
  assert (HRei : rg_send_eintr fr_RG = 0x5d8e20) by reflexivity.
  assert (Hmo : negb (N1 =? 0) = true -> N1 <> 0) by (intros Hb; apply negb_true_iff, Z.eqb_neq in Hb; exact Hb).
  destruct (sm_mx_entry W regs mem (negb (N1 =? 0)) F P1 kb H23 H9 H27 H20 HF1 HF2 HP Hkb
    (fun Hb => HPi (Hmo Hb)) (fun Hb => HPa (Hmo Hb)) (fun Hb => HPc (Hmo Hb)) (fun Hb => MB (Hmo Hb))
    (fun Hb => RA (Hmo Hb)) M56 M72 HW1 HWmx HWei) as [HS SHOK].
  assert (HEI : img_env VAL A_LIM (Eimg (Ereg regs (sm_x1 kb)))) by apply Eimg_env.
  assert (HAE : env_agree 32 (Ereg regs (sm_x1 kb)) (Eimg (Ereg regs (sm_x1 kb))))
    by (split; [intros mm Hmm; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
  assert (EE : forall m (rr : bv 5), Z.of_nat m = bv_unsigned rr -> ew (Eimg (Ereg regs (sm_x1 kb))) m = getr regs rr)
    by (intros m rr Hm; pose proof (bv_unsigned_in_range 5 rr) as Hr5;
        change (bv_modulus 5) with 32 in Hr5; rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_nat; exact Hm).
  assert (E20 : ew (Eimg (Ereg regs (sm_x1 kb))) 20 = w64 P1) by (rewrite (EE 20%nat 20%bv eq_refl); exact H20).
  assert (E6 : ew (Eimg (Ereg regs (sm_x1 kb))) 6 = w64 N1) by (rewrite (EE 6%nat 6%bv eq_refl); exact H6).
  assert (E23 : ew (Eimg (Ereg regs (sm_x1 kb))) 23 = w64 1) by (rewrite (EE 23%nat 23%bv eq_refl); exact H23).
  assert (E32 : ew (Eimg (Ereg regs (sm_x1 kb))) 32 = Z_to_bv 64 kb)
    by (rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
  assert (U9 : bv_unsigned (ew (Eimg (Ereg regs (sm_x1 kb))) 9) = F)
    by (rewrite (EE 9%nat 9%bv eq_refl), H9; apply unsigned_lit_small; lia).
  assert (U343 : bv_unsigned (ew (Eimg (Ereg regs (sm_x1 kb))) 343) = 0x5d9550)
    by (rewrite Eimg_img by (unfold A_TEXT, A_LIM; lia); change 343%nat with (A_HI 63);
        rewrite (proj1 sm_mx_vals); first [reflexivity | apply unsigned_lit_small; lia]).
  assert (U346 : bv_unsigned (ew (Eimg (Ereg regs (sm_x1 kb))) 346) = 0x5d956c)
    by (rewrite Eimg_img by (unfold A_TEXT, A_LIM; lia); change 346%nat with (A_HI 66);
        rewrite (proj2 sm_mx_vals); first [reflexivity | apply unsigned_lit_small; lia]).
  clear EE.
  set (E := Eimg (Ereg regs (sm_x1 kb))) in *. clearbody E.
  assert (E9b : base_val E (Some 9%nat) = F) by exact U9.
  assert (E343b : base_val E (Some 343%nat) = 0x5d9550) by exact U343.
  assert (E346b : base_val E (Some 346%nat) = 0x5d956c) by exact U346.
  unfold cfg_at. change (w64 (fr_B0 + AF_arm_sendmax)) with (Z_to_bv 64 (BASE + AF_arm_sendmax)).
  revert HS SHOK. destruct (N1 =? 0) eqn:EN; intros HS SHOK; cbn [negb] in HS, SHOK.
  all: pose proof EN as EN'; first [apply Z.eqb_eq in EN' | apply Z.eqb_neq in EN'].
  all: psrr_branch_tok RUN BR HS SHOK SMspan.
  all: rewrite branch_eq_U, (U_atom E 6 N1 E6), U_lit in Hc by lia.
  all: try (exfalso; first [apply Z.eqb_eq in Hc | apply Z.eqb_neq in Hc]; lia).
  all: clear Hc.
  all: paj_run_to_tok_x RUNTO HS HJ SHOK SMspan AF_LLVM_latch.
  1,3: lazymatch goal with |- awr_ok_x ?Ev ?rs ?G ?XO ?OUT ?STK ?sp0 ?FP ?b0 ?bc ?ly ?own =>
      let rs' := eval vm_compute in rs in change (awr_ok_x Ev rs' G XO OUT STK sp0 FP b0 bc ly own) end;
    repeat first
     [ apply awr_ok_x_nil
     | apply awr_ok_x_cons; [intros a Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi] in Ha; rewrite ?E9b in Ha;
         first [exfalso; lia | left; split; [left; lia | lia]] |]
     | apply awr_ok_x_cons_g; [intros a Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi] in Ha;
         rewrite ?E343b, ?E346b in Ha; first [apply HGmx; lia | apply HGei; lia] |] ].
  all: lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
    assert (HAE2 : env_agree 32 (Ereg regs (sm_x1 kb)) Ev)
      by (split; [intros q Hq; rewrite ?ew_ewset_other by lia; exact (proj1 HAE q Hq)
                 | rewrite ?ed_ewset; exact (proj2 HAE)]);
    assert (EV9 : bv_unsigned (ew Ev 9) = F) by (rewrite ?ew_ewset_other by lia; exact U9);
    assert (EV6 : bv_unsigned (ew Ev 6) = N1)
      by (rewrite ?ew_ewset_other by lia; rewrite E6; apply unsigned_lit_small; lia);
    assert (EV23 : bv_unsigned (ew Ev 23) = 1)
      by (rewrite ?ew_ewset_other by lia; rewrite E23; apply unsigned_lit_small; lia);
    assert (EV32 : bv_unsigned (ew Ev 32) = kb)
      by (rewrite ?ew_ewset_other by lia; rewrite E32; apply unsigned_lit_small; lia);
    assert (EV343 : bv_unsigned (ew Ev 343) = 0x5d9550) by (rewrite ?ew_ewset_other by lia; exact U343);
    assert (EV346 : bv_unsigned (ew Ev 346) = 0x5d956c) by (rewrite ?ew_ewset_other by lia; exact U346)
  end.
  all: pose proof (regs_kept_of_st_ok_pi (PI := PB_fr) _ _ _ regs (sm_x1 kb) sm_mx_kept HS HAE2
    ltac:(vm_compute; reflexivity)) as KR.
  all: cbn [ms_regs restrict] in KR.
  all: prreg HS (20%bv : bv 5) Q20.
  all: rewrite ?ew_ewset_other in Q20 by lia.
  all: assert (Q20' : getr (ms_regs ms) 20 = w64 (if N1 =? 0 then P1 else P1 + 1))
    by (rewrite Q20, EN; cbv iota; rewrite ?E20; first [reflexivity | rewrite unsigned_lit_small by lia; reflexivity]).
  all: pose proof (st_ok_pi_region_nth _ _ _ 0 _ HS eq_refl) as RG0.
  all: pose proof (st_ok_pi_region_nth _ _ _ 2 _ HS eq_refl) as RG2.
  all: pose proof (st_ok_pi_region_nth _ _ _ 3 _ HS eq_refl) as RG3.
  all: cbn [ms_mem restrict] in RG0, RG2, RG3.
  all: assert (V144 : val_mem segs (arm W (ms_mem ms)) (F + 144) 8 (if N1 =? 0 then 0 else N1 - 1))
    by (rewrite EN; cbv iota; eapply (field_of_region _ _ 9%nat F _ _ _ _ _ 144 8%N _ _ RG0);
        [ exact EV9 | left; reflexivity
        | cbn [sv_denot]; rewrite ?EV6; first [reflexivity | f_equal; lia]
        | zside | zside ]).
  all: assert (Vmx : val_mem segs (arm W (ms_mem ms)) (rg_send_max fr_RG) 8 (if N1 =? 0 then 0 else kb))
    by (rewrite EN; cbv iota; replace (rg_send_max fr_RG) with (0x5d9550 + -1936) by reflexivity;
        eapply (field_of_region _ _ 343%nat 0x5d9550 _ _ _ _ _ (-1936) 8%N _ _ RG2);
        [ exact EV343 | left; reflexivity
        | cbn [sv_denot]; rewrite ?EV32, ?Z.add_0_r; reflexivity | zside | zside ]).
  all: assert (Vei : val_mem segs (arm W (ms_mem ms)) (rg_send_eintr fr_RG) 1 1)
    by (replace (rg_send_eintr fr_RG) with (0x5d956c + -1868) by reflexivity;
        eapply (field_of_region _ _ 346%nat 0x5d956c _ _ _ _ _ (-1868) 1%N _ _ RG3);
        [ exact EV346 | left; reflexivity | cbn [sv_denot]; rewrite ?EV23; reflexivity | zside | zside ]).
  all: assert (KP : KEPT W mem (ms_mem ms) (XS F sm_mx_XG))
    by (intros a Ha Hn; split;
        [ apply (aview_kept_out _ _ _ _ _ HFr a Ha); intros (r & Hin & Hr); vm_compute in Hin;
          repeat (destruct Hin as [<- | Hin];
            [ cbn [YP09.r_base YP09.r_wlo YP09.r_whi] in Hr; rewrite ?E9b, ?E343b, ?E346b in Hr;
              first [ lia | apply Hn; unfold XS, sm_mx_XG; apply inFP_cons; right; apply inFP_cons;
                first [ left; lia | right; apply inFP_cons; left; lia
                      | right; apply inFP_cons; right; apply inFP_cons; left; lia ] ]
            | ]);
          destruct Hin
        | exact (sm_wkeep W mem (ms_mem ms) a HG0) ]).
  all: pmkst HS.
  all: apply SRr_ret.
  all: unfold sm_mx_post_x; cbv beta.
  all: split; [reflexivity|].
  all: exists (ms_regs ms), (ms_mem ms), (with_vm_backing (m_vm_lazy md) mat md).
  all: split; [reflexivity|].
  all: split; [exact HJ|].
  all: split; [exact KP|].
  all: split; [exact HG0|].
  all: split; [exact V144|].
  all: split; [rewrite EN in Vmx; exact Vmx|].
  all: split; [exact Vei|].
  all: split; [exact KR|].
  all: exact Q20'.
Qed.

Theorem lf_arm_sendmax_x : forall cx Hp t W c,
  lf_base_x B MT XM_LIB RLO RHI fr_live_pre LIBROOM NP G_fr ARx cx Hp -> INV_A_x B NP G_fr fr_FP PST ARx LSx RINV 8 cx Hp t W c ->
  SRr segs W c (INV_K_x B NP G_fr fr_FP PST ARx LSx RINV cx Hp t).
Proof.
  intros cx Hp t W c HB HA.
  destruct HA as (regs & regsD & mem & md & Hc & Hkept & HopD & _ & HROM & HLF).
  destruct HLF as (own & ly3 & S3 & Hp3 & kk & m & fpos & HJ & Hown & Hframe & Hflag & Hmodel & Hinput & Hrom & Hsep &
    HLS & HNP & HRINV & HRD).
  subst own.
  pose proof HRD as (Hcommon & HD25 & Htb & Hkb & HO & Hoprest).
  cbv zeta in Hoprest. destruct Hoprest as (Hop11 & Hpick).
  assert (Hopeq : in_byte cx (lm_k m) mod 10 = 8).
  { pose proof (Z.mod_pos_bound (in_byte cx (lm_k m)) 10 ltac:(lia)) as Hmb.
    apply (f_equal bv_unsigned) in HopD. rewrite Hop11 in HopD.
    rewrite !unsigned_lit_small in HopD by lia. lia. }
  rewrite Hopeq in Hpick.
  assert (Hpk8 : picks 8 = false) by reflexivity.
  rewrite Hpk8 in Hpick. destruct Hpick as (HD20 & HD6 & _).
  assert (HARx : ARx ly3 S3 Hp3 W mem md) by (eapply ajournal_gx_AR_x; exact HJ).
  assert (HAR : ARE ly3 S3 W mem md) by (exists Hp3; exact HARx).
  assert (Hfin : In (1, fpos) (frames S3)).
  { pose proof HJ as (_ & _ & (memS & HJ0 & _) & _). pose proof HJ0 as (_ & _ & _ & _ & _ & Hfrs & _).
    rewrite Hfrs. left. reflexivity. }
  destruct HB as (HAI & Hpre). pose proof Hpre as (Hafn & _ & _ & _ & _ & Hlen & _).
  pose proof Hafn as (_ & _ & _ & _ & _ & Hstk & _).
  pose proof Hstk as (Hsp16 & HstkK & Hceil & Hlo & Hhi & Hhi2 & _).
  set (sp0 := spZ (c_regs cx)) in *.
  assert (HSTK : LLVMF_STK = 32768) by reflexivity.
  pose proof sm_ceil_lo as Hac. assert (HES : ESTACK = 4096) by reflexivity.
  assert (Hsp0 : alloc_ceiling + 32768 <= sp0 <= 2 ^ 47) by lia.
  pose proof (Z.mod_pos_bound (sp0 - 320) 32 ltac:(lia)) as Hm32.
  assert (HFeq : lf_F cx = sp0 - 320 - (sp0 - 320) mod 32) by reflexivity.
  assert (HFbound : 2 ^ 46 <= lf_F cx <= 2 ^ 47) by lia.
  assert (HFmod : lf_F cx mod 32 = 0)
    by (rewrite HFeq; rewrite Zminus_mod, Zmod_mod, Z.sub_diag; reflexivity).
  assert (KD : forall r : bv 5, In r jt_kept -> getr regs r = getr regsD r) by exact Hkept.
  pose proof Hcommon as (C2 & C8 & C9 & C18 & C19 & C23 & C24 & C26 & C27 & C3 & C4).
  assert (Hr23 : getr regs 23 = w64 1) by (rewrite (KD 23%bv ltac:(sm_in)); exact C23).
  assert (Hr9 : getr regs 9 = w64 (lf_F cx)) by (rewrite (KD 9%bv ltac:(sm_in)); exact C9).
  assert (Hr27 : getr regs 27 = w64 SB) by (rewrite (KD 27%bv ltac:(sm_in)); exact C27).
  assert (Hr20 : getr regs 20 = w64 (c_p cx + lm_k m + 1)) by (rewrite (KD 20%bv ltac:(sm_in)); exact HD20).
  assert (Hr6 : getr regs 6 = w64 (c_n cx - lm_k m - 1)) by (rewrite (KD 6%bv ltac:(sm_in)); exact HD6).
  (* the input block and the byte in.p[0] *)
  pose proof Hinput as [[[Hn0 _] | [Hnr Hblk]] Hgarr]; [lia|].
  destruct (alx_blocks _ _ _ LAWS _ _ _ _ _ _ _ _ HARx Hblk) as (Hp16 & Hp4096 & Hpceil & Hpia & _ & _).
  pose proof (sm_blk_off_x _ _ _ _ _ _ _ _ HARx Hblk ltac:(lia)) as Hpimg.
  unfold OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B.YCbq.off_img in Hpimg.
  pose proof (req_size_pos (c_n cx) ltac:(lia)) as [_ Hreq].
  pose proof (sm_in_byte_rng cx (lm_k m + 1)) as Hkb8.
  (* the frame and the stream's two cells *)
  pose proof Hframe as (_ & Hawr & _ & _ & _ & F56 & _ & F72 & _).
  assert (HW1 : forall a, lf_F cx + 144 <= a < lf_F cx + 152 -> writable_at segs (arm W mem) a).
  { intros a Ha. replace a with (lf_F cx + (a - lf_F cx)) by lia. apply Hawr. lia. }
  pose proof Hmodel as (_ & _ & _ & Hout & _).
  pose proof Hout as (_ & Omx & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Oei & _).
  rewrite Hc.
  eapply SRr_mono.
  { exact (sm_mx_run_x W regs mem md LLVMF_STK sp0 (lf_FP fr_FP cx) (c_ly cx) (c_S cx) Hp (c_W cx) (c_mem cx) (c_md cx)
      [(1, fpos)] ly3 S3 Hp3 kk (lf_F cx) (c_p cx + lm_k m + 1) (c_n cx - lm_k m - 1) (in_byte cx (lm_k m + 1))
      HJ Hr23 Hr9 Hr27 Hr20 Hr6 ltac:(lia) HFbound HFmod ltac:(lia) Hkb8 ltac:(lia) ltac:(lia)
      ltac:(intros HN; lia)
      ltac:(intros HN; unfold in_app in Hpia; unfold kLowShadowBeg, kHighMemBeg in *; lia)
      ltac:(intros HN; lia)
      ltac:(intros HN; rewrite <- Z.add_assoc; exact (proj1 (sm_in_byte cx (arm W mem) (lm_k m + 1) Hgarr ltac:(lia))))
      ltac:(intros HN; apply (range_addressable_of_block_hp0_x segs B ARx LAWS HP0 ly3 S3 Hp3 W mem md (c_p cx) (c_n cx));
            [exact HARx | exact Hblk | lia | lia])
      F56 F72 HW1 Omx Oei). }
  intros W' c' _ (-> & regs' & mem' & md' & -> & HJ' & KP & HGr & V144 & Vmx & Vei & KR & Q20).
  pose proof sm_mx_xgok as HXG.
  assert (HXOK : XOK (XS (lf_F cx) sm_mx_XG)) by (apply sm_xok; [lia | exact HXG]).
  assert (KK : forall r : bv 5, In r sm_mx_kept -> In r jt_kept -> getr regs' r = getr regsD r)
    by (intros r H1 H2; rewrite (KR r H1); exact (KD r H2)).
  set (u := if c_n cx - lm_k m - 1 =? 0 then 0 else in_byte cx (lm_k m + 1)) in *.
  assert (Hu : 0 <= u <= 255) by (unfold u; destruct (_ =? 0); lia).
  exists regs', mem', md'. split; [reflexivity|].
  split; [exact (sm_jt_kept W mem mem' _ HXOK KP HROM)|].
  exists [(1, fpos)], ly3, S3, Hp3, kk, (sm_sendmax cx m u), fpos.
  split; [exact HJ'|]. split; [reflexivity|].
  split; [exact (sm_aframe_kept_x cx ly3 S3 W mem md mem' fpos sm_mx_XG HAR Hfin Hsp0 HXG KP HGr Hframe)|].
  split; [exact (sm_flag_kept_x ly3 S3 W mem md mem' _ fpos _ HAR HXOK KP Hfin Hflag)|].
  split; [exact (sm_amodel_mx_x ly3 S3 W mem md mem' (lf_F cx) cx m u HAR ltac:(lia) KP HGr Hmodel HO Hu Vmx Vei)|].
  split; [exact (sm_ainput_kept_x cx ly3 S3 W mem md mem' _ HAR HXOK KP (eq_sym Hlen) Hinput)|].
  split; [exact (sm_rom_kept W mem mem' _ HXOK KP Hrom)|].
  split; [exact Hsep|].
  assert (Hud : u = (if lm_k m + 1 <? c_n cx then in_byte cx (lm_k m + 1) else 0)).
  { unfold u. destruct (lm_k m + 1 <? c_n cx) eqn:Ek; [apply Z.ltb_lt in Ek | apply Z.ltb_ge in Ek].
    - replace (c_n cx - lm_k m - 1 =? 0) with false by (symmetry; apply Z.eqb_neq; lia). reflexivity.
    - replace (c_n cx - lm_k m - 1 =? 0) with true by (symmetry; apply Z.eqb_eq; lia). reflexivity. }
  split; [rewrite Hud; exact (LS_sendmax cx t m ly3 S3 HLS)|].
  split; [exact HNP|].
  split; [rewrite Hud; exact (RI_sendmax cx t m HRINV)|].
  unfold lregs_K, lregs_common, sm_sendmax. cbn [lm_k]. unfold sm_kn.
  split.
  { split; [rewrite (KK 2%bv ltac:(sm_in) ltac:(sm_in)); exact C2|].
    split; [rewrite (KK 8%bv ltac:(sm_in) ltac:(sm_in)); exact C8|].
    split; [rewrite (KK 9%bv ltac:(sm_in) ltac:(sm_in)); exact C9|].
    split; [rewrite (KK 18%bv ltac:(sm_in) ltac:(sm_in)); exact C18|].
    split; [rewrite (KK 19%bv ltac:(sm_in) ltac:(sm_in)); exact C19|].
    split; [rewrite (KK 23%bv ltac:(sm_in) ltac:(sm_in)); exact C23|].
    split; [rewrite (KK 24%bv ltac:(sm_in) ltac:(sm_in)); exact C24|].
    split; [rewrite (KK 26%bv ltac:(sm_in) ltac:(sm_in)); exact C26|].
    split; [rewrite (KK 27%bv ltac:(sm_in) ltac:(sm_in)); exact C27|].
    split; [rewrite (KK 3%bv ltac:(sm_in) ltac:(sm_in)); exact C3|].
    rewrite (KK 4%bv ltac:(sm_in) ltac:(sm_in)); exact C4. }
  split; [rewrite (KK 25%bv ltac:(sm_in) ltac:(sm_in)); exact HD25|].
  split; [exact Htb|].
  unfold sv8.
  destruct (lm_k m + 1 <? c_n cx) eqn:Ek; [apply Z.ltb_lt in Ek | apply Z.ltb_ge in Ek].
  - assert (EN : (c_n cx - lm_k m - 1 =? 0) = false) by (apply Z.eqb_neq; lia).
    rewrite EN in Q20, V144. cbv iota in Q20, V144.
    split; [rewrite Q20; f_equal; lia|].
    split; [replace (c_n cx - (lm_k m + 2)) with (c_n cx - lm_k m - 1 - 1) by lia; exact V144|]. lia.
  - assert (EN : (c_n cx - lm_k m - 1 =? 0) = true) by (apply Z.eqb_eq; lia).
    rewrite EN in Q20, V144. cbv iota in Q20, V144.
    split; [rewrite Q20; f_equal; lia|].
    split; [replace (c_n cx - (lm_k m + 1)) with 0 by lia; exact V144|]. lia.
Qed.

Definition sm_df_post_x (W : world segs) (regs : bvmap 5 word) (mem : word -> option byte) (STK sp0 : Z)
    (FP : list (Z * Z)) (ly0 : alayout) (S0 : astate) (Hp0 : list Z) (W0 : world segs) (mem0 : word -> option byte) (md0 : Model)
    (own : list (Z * Z)) (ly : alayout) (S : astate) (Hp : list Z) (kk F P1 N1 kb dd cl : Z) : world segs -> config -> Prop :=
  fun W' c' => W' = W /\ exists (g : bool) regs' mem' md',
    g = negb (N1 =? 0) && Z.odd kb /\
    c' = cfg_at segs (fr_B0 + AF_LLVM_latch) regs' mem' md' /\
    ajournal_gx_x segs B PST ARx G_fr 0 [] STK sp0 FP ly0 S0 Hp0 W0 mem0 md0 own ly S Hp W mem' md' kk /\
    KEPT W mem mem' (XS F (sm_df_XG g)) /\
    mem_grows (mrestrict (w_H W) mem) (mrestrict (w_H W) mem') /\
    val_mem segs (arm W mem') (F + 144) 8 (if N1 =? 0 then 0 else N1 - 1) /\
    val_mem segs (arm W mem') (rg_send_dead fr_RG) 1 (if g then dd else 1) /\
    val_mem segs (arm W mem') (rg_gone fr_RG) 1 1 /\
    val_mem segs (arm W mem') (rg_client fr_RG) 4 (if g then 2 ^ 32 - 1 else cl) /\
    (g = true -> val_mem segs (arm W mem') (rg_lock fr_RG + 4) 4 0) /\
    (forall r, In r sm_df_kept -> getr regs' r = getr regs r) /\
    getr regs' 20 = w64 (if N1 =? 0 then P1 else P1 + 1).

Ltac sm_dfb H :=
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val] in H;
  repeat (first [rewrite ew_ewset_other in H by (cbv; lia) | rewrite ew_havoc_old in H by (cbv; lia)]);
  repeat match goal with U : bv_unsigned (ew _ _) = _ |- _ => rewrite U in H end.

Ltac sm_df_awr :=
  lazymatch goal with |- awr_ok_x ?Ev ?rs ?G ?XO ?OUT ?STK ?sp0 ?FP ?b0 ?bc ?ly ?own =>
    let rs' := eval vm_compute in rs in change (awr_ok_x Ev rs' G XO OUT STK sp0 FP b0 bc ly own) end;
  repeat first
   [ apply awr_ok_x_nil
   | apply awr_ok_x_cons; [intros a Ha; sm_dfb Ha; first [exfalso; lia | left; split; [left; lia | lia]] |]
   | apply awr_ok_x_cons_g; [intros a Ha; sm_dfb Ha; first [apply HGdd; lia | apply HGgn; lia | apply HGcl; lia] |] ].

Ltac sm_inFP := repeat (first [apply inFP_cons; left; lia | apply inFP_cons; right]).

Ltac sm_inX :=
  let a := fresh "a" in let r := fresh "r" in let Hin := fresh "Hin" in let Hr := fresh "Hr" in
  intros a (r & Hin & Hr); vm_compute in Hin;
  repeat (destruct Hin as [<- | Hin]; [sm_dfb Hr; unfold XS, sm_df_XG; cbn [app]; sm_inFP | ]);
  destruct Hin.

Ltac sm_notw :=
  let r := fresh "r" in let Hin := fresh "Hin" in let Hr := fresh "Hr" in
  intros (r & Hin & Hr); vm_compute in Hin;
  repeat (destruct Hin as [<- | Hin]; [sm_dfb Hr; lia | ]); destruct Hin.

Ltac sm_base :=
  repeat (first [rewrite ew_ewset_other by (cbv; lia) | rewrite ew_havoc_old by (cbv; lia)]);
  match goal with U : bv_unsigned (ew _ ?n) = _ |- bv_unsigned (ew _ ?n) = _ => exact U end.

Ltac sm_env HS := lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ => Ev end.

Lemma sm_df_run_x : forall (W : world segs) regs mem md STK sp0 FP ly0 S0 Hp0 (W0 : world segs) mem0 md0 own ly S Hp kk
    F P1 N1 kb dd cl,
  ajournal_gx_x segs B PST ARx G_fr 0 [] STK sp0 FP ly0 S0 Hp0 W0 mem0 md0 own ly S Hp W mem md kk ->
  getr regs 2 = w64 F -> getr regs 3 = w64 (as_gp B) -> getr regs 4 = w64 (as_tp B) ->
  getr regs 23 = w64 1 -> getr regs 9 = w64 F -> getr regs 27 = w64 SB ->
  getr regs 20 = w64 P1 -> getr regs 6 = w64 N1 -> 0 <= N1 < 2 ^ 26 ->
  2 ^ 46 <= F <= 2 ^ 47 -> F mod 32 = 0 -> 4096 <= P1 <= 2 ^ 47 - 16 -> 0 <= kb < 256 ->
  F + 152 <= sp0 -> (F - sp0) mod 16 = 0 -> ESTACK + (sp0 - F) <= STK ->
  (N1 <> 0 -> P1 + 1 <= 0x10000 \/ 0x5fc000 <= P1) ->
  (N1 <> 0 -> P1 + 1 <= kLowShadowBeg \/ kHighMemBeg <= P1) ->
  (N1 <> 0 -> P1 + 1 <= F) ->
  (N1 <> 0 -> val_mem segs (arm W mem) P1 1 kb) ->
  (N1 <> 0 -> range_addressable (aview segs (w_H W) mem) SHADOW_OFF P1 1) ->
  sv8 W mem (F + 32) 0xa2540 -> sv8 W mem (F + 40) 0x5d9564 -> sv8 W mem (F + 64) 0x5d955c ->
  (forall a, F + 144 <= a < F + 152 -> writable_at segs (arm W mem) a) ->
  val_mem segs (arm W mem) (rg_send_dead fr_RG) 1 dd -> 0 <= dd < 256 -> awr W mem (rg_send_dead fr_RG) 1 ->
  awr W mem (rg_gone fr_RG) 1 ->
  val_mem segs (arm W mem) (rg_client fr_RG) 4 cl -> 0 <= cl < 2 ^ 32 -> awr W mem (rg_client fr_RG) 4 ->
  alock_at fr_RG W mem false ->
  SRr segs W (cfg_at segs (fr_B0 + AF_arm_default) regs mem md)
    (sm_df_post_x W regs mem STK sp0 FP ly0 S0 Hp0 W0 mem0 md0 own ly S Hp kk F P1 N1 kb dd cl).
Proof.
  intros W regs mem md STK sp0 FP ly0 S0 Hp0 W0 mem0 md0 own ly S Hp kk F P1 N1 kb dd cl HJ H2 H3 H4 H23 H9 H27
    H20 H6 HN1 HF1 HF2 HP Hkb Hs1 Hs16 Hs2 HPi HPa HPc MB RA M32 M40 M64 HW1 Vdd Hdd HWdd HWgn Vcl Hcl HWcl HLK.
  pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
  pose proof sm_ceil_lo as Hac. assert (HES : ESTACK = 4096) by reflexivity.
  pose proof sm_rgv as (_ & _ & _ & _ & _ & _ & _ & _ & _ & HRdd & HRgn & HRcl & _ & HRlk & _).
  assert (Hmo : negb (N1 =? 0) = true -> N1 <> 0) by (intros Hb; apply negb_true_iff, Z.eqb_neq in Hb; exact Hb).
  destruct (sm_df_entry W regs mem (negb (N1 =? 0)) F P1 kb dd cl H23 H9 H27 H20 HF1 HF2 HP Hkb Hdd Hcl
    (fun Hb => HPi (Hmo Hb)) (fun Hb => HPa (Hmo Hb)) (fun Hb => HPc (Hmo Hb)) (fun Hb => MB (Hmo Hb))
    (fun Hb => RA (Hmo Hb)) M32 M40 M64 HW1 Vdd HWdd HWgn Vcl HWcl) as [HS SHOK].
  set (E := Eimg (Ereg regs (sm_x1 kb))) in *.
  assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
  assert (HAE : env_agree 32 (Ereg regs (sm_x1 kb)) E)
    by (subst E; split; [intros mm Hmm; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
  assert (EE : forall m (rr : bv 5), Z.of_nat m = bv_unsigned rr -> ew E m = getr regs rr)
    by (intros m rr Hm; subst E; pose proof (bv_unsigned_in_range 5 rr) as Hr5;
        change (bv_modulus 5) with 32 in Hr5; rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_nat; exact Hm).
  assert (E2 : ew E 2 = w64 F) by (rewrite (EE 2%nat 2%bv eq_refl); exact H2).
  assert (E3 : ew E 3 = w64 (as_gp B)) by (rewrite (EE 3%nat 3%bv eq_refl); exact H3).
  assert (E4 : ew E 4 = w64 (as_tp B)) by (rewrite (EE 4%nat 4%bv eq_refl); exact H4).
  assert (E6 : ew E 6 = w64 N1) by (rewrite (EE 6%nat 6%bv eq_refl); exact H6).
  assert (E20 : ew E 20 = w64 P1) by (rewrite (EE 20%nat 20%bv eq_refl); exact H20).
  assert (E23 : ew E 23 = w64 1) by (rewrite (EE 23%nat 23%bv eq_refl); exact H23).
  assert (E32 : ew E 32 = Z_to_bv 64 kb)
    by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
  assert (U9 : bv_unsigned (ew E 9) = F) by (rewrite (EE 9%nat 9%bv eq_refl), H9; apply unsigned_lit_small; lia).
  assert (U20 : bv_unsigned (ew E 20) = P1) by (rewrite E20; apply unsigned_lit_small; lia).
  assert (U23 : bv_unsigned (ew E 23) = 1) by (rewrite E23; apply unsigned_lit_small; lia).
  pose proof sm_df_vals as (V60 & V64 & V65).
  assert (U340 : bv_unsigned (ew E 340) = 0xa2540)
    by (subst E; rewrite Eimg_img by (unfold A_TEXT, A_LIM; lia); change 340%nat with (A_HI 60);
        rewrite V60; first [reflexivity | apply unsigned_lit_small; lia]).
  assert (U344 : bv_unsigned (ew E 344) = 0x5d955c)
    by (subst E; rewrite Eimg_img by (unfold A_TEXT, A_LIM; lia); change 344%nat with (A_HI 64);
        rewrite V64; first [reflexivity | apply unsigned_lit_small; lia]).
  assert (U345 : bv_unsigned (ew E 345) = 0x5d9564)
    by (subst E; rewrite Eimg_img by (unfold A_TEXT, A_LIM; lia); change 345%nat with (A_HI 65);
        rewrite V65; first [reflexivity | apply unsigned_lit_small; lia]).
  assert (E244 : ew E 244 = Z_to_bv 64 (rg_lock fr_RG))
    by (subst E; rewrite Eimg_img by (unfold A_TEXT, A_LIM; lia); change 244%nat with (A_OBJ 3);
        rewrite sm_hv3; reflexivity).
  clear EE.
  clearbody E.
  unfold cfg_at. change (w64 (fr_B0 + AF_arm_default)) with (Z_to_bv 64 (BASE + AF_arm_default)).
  revert HS SHOK. destruct (N1 =? 0) eqn:EN; intros HS SHOK; cbn [negb] in HS, SHOK.
  all: pose proof EN as EN'; first [apply Z.eqb_eq in EN' | apply Z.eqb_neq in EN'].
  all: psrr_branch_tok RUN BR HS SHOK SMspan.
  all: rewrite branch_eq_U, (U_atom E 6 N1 E6), U_lit in Hc by lia.
  all: try (exfalso; first [apply Z.eqb_eq in Hc | apply Z.eqb_neq in Hc]; lia).
  all: clear Hc.
  - (* no input left: in.n := 0, g_send_dead := 1, g_gone := 1 *)
    paj_run_to_tok_x RUNTO HS HJ SHOK SMspan AF_LLVM_latch.
    + sm_df_awr.
    + let Ev := sm_env HS in
      assert (HAE2 : env_agree 32 (Ereg regs (sm_x1 kb)) Ev)
        by (split; [intros q Hq; rewrite ?ew_ewset_other by lia; exact (proj1 HAE q Hq)
                   | rewrite ?ed_ewset; exact (proj2 HAE)]);
      assert (EV9 : bv_unsigned (ew Ev 9) = F) by sm_base;
      assert (EV344 : bv_unsigned (ew Ev 344) = 0x5d955c) by sm_base;
      assert (EV345 : bv_unsigned (ew Ev 345) = 0x5d9564) by sm_base;
      assert (EV340 : bv_unsigned (ew Ev 340) = 0xa2540) by sm_base;
      assert (EV23 : bv_unsigned (ew Ev 23) = 1) by sm_base.
      pose proof (regs_kept_of_st_ok_pi (PI := PB_fr) _ _ _ regs (sm_x1 kb) sm_df_kept HS HAE2
        ltac:(vm_compute; reflexivity)) as KR.
      cbn [ms_regs restrict] in KR.
      prreg HS (20%bv : bv 5) Q20.
      rewrite ?ew_ewset_other in Q20 by lia. rewrite E20 in Q20.
      pose proof (st_ok_pi_region_nth _ _ _ 0 _ HS eq_refl) as RG0.
      pose proof (st_ok_pi_region_nth _ _ _ 2 _ HS eq_refl) as RG2.
      pose proof (st_ok_pi_region_nth _ _ _ 3 _ HS eq_refl) as RG3.
      pose proof (st_ok_pi_region_nth _ _ _ 4 _ HS eq_refl) as RG4.
      cbn [ms_mem restrict] in RG0, RG2, RG3, RG4.
      assert (V144 : val_mem segs (arm W (ms_mem ms)) (F + 144) 8 0)
        by (eapply (field_of_region _ _ 9%nat F _ _ _ _ _ 144 8%N _ _ RG0);
            [exact EV9 | left; reflexivity | reflexivity | zside | zside]).
      assert (Vdd' : val_mem segs (arm W (ms_mem ms)) (rg_send_dead fr_RG) 1 1)
        by (replace (rg_send_dead fr_RG) with (0x5d9564 + -1892) by lia;
            eapply (field_of_region _ _ 345%nat 0x5d9564 _ _ _ _ _ (-1892) 1%N _ _ RG2);
            [exact EV345 | left; reflexivity | cbn [sv_denot]; rewrite EV23; reflexivity | zside | zside]).
      assert (Vgn' : val_mem segs (arm W (ms_mem ms)) (rg_gone fr_RG) 1 1)
        by (replace (rg_gone fr_RG) with (0x5d955c + -1916) by lia;
            eapply (field_of_region _ _ 344%nat 0x5d955c _ _ _ _ _ (-1916) 1%N _ _ RG3);
            [exact EV344 | left; reflexivity | cbn [sv_denot]; rewrite EV23; reflexivity | zside | zside]).
      assert (Vcl' : val_mem segs (arm W (ms_mem ms)) (rg_client fr_RG) 4 cl)
        by (replace (rg_client fr_RG) with (0xa2540 + 32) by lia;
            eapply (field_of_region _ _ 340%nat 0xa2540 _ _ _ _ _ 32 4%N _ _ RG4);
            [exact EV340 | left; reflexivity | reflexivity | zside | zside]).
      pmkst HS. apply SRr_ret. unfold sm_df_post_x; cbv beta. split; [reflexivity|].
      exists false. do 3 eexists. split; [rewrite EN; reflexivity|].
      split; [reflexivity|]. split; [exact HJ|].
      split; [apply (sm_kept_run W _ _ mem (ms_mem ms) _ HFr HG0); sm_inX|].
      split; [exact HG0|].
      split; [rewrite EN; exact V144|].
      split; [exact Vdd'|]. split; [exact Vgn'|]. split; [exact Vcl'|].
      split; [intros Hf; discriminate Hf|].
      split; [exact KR|]. rewrite EN; exact Q20.
  - (* input left: the byte, in.n := t1 - 1, then its low bit *)
    paj_run_tok_x RUN HS HJ SHOK SMspan.
    + sm_df_awr.
    + rename HF into HFa, HFr into HFra, HG0 into HGa.
      psrr_branch_tok RUN BR HS SHOK SMspan.
      all: let Ev := sm_env HS in
           assert (EV32 : ew Ev 32 = Z_to_bv 64 kb) by (rewrite ?ew_ewset_other by lia; exact E32).
      all: rewrite branch_eq_U, U_and_lit, (U_atom _ 32 kb EV32), U_lit in Hc by lia.
      all: pose proof (sm_odd_land kb) as Hodd; rewrite Hc in Hodd; cbn [negb] in Hodd; clear Hc.
      * (* even: g_send_dead := 1, g_gone := 1 *)
        paj_run_to_tok_x RUNTO HS HJ SHOK SMspan AF_LLVM_latch.
        -- sm_df_awr.
        -- let Ev := sm_env HS in
           assert (HAE2 : env_agree 32 (Ereg regs (sm_x1 kb)) Ev)
             by (split; [intros q Hq; rewrite ?ew_ewset_other by lia; exact (proj1 HAE q Hq)
                        | rewrite ?ed_ewset; exact (proj2 HAE)]);
           assert (EV9 : bv_unsigned (ew Ev 9) = F) by sm_base;
           assert (EV344 : bv_unsigned (ew Ev 344) = 0x5d955c) by sm_base;
           assert (EV345 : bv_unsigned (ew Ev 345) = 0x5d9564) by sm_base;
           assert (EV340 : bv_unsigned (ew Ev 340) = 0xa2540) by sm_base;
           assert (EV23 : bv_unsigned (ew Ev 23) = 1) by sm_base;
           assert (EV6 : bv_unsigned (ew Ev 6) = N1)
             by (rewrite !ew_ewset_other by lia; rewrite E6; apply unsigned_lit_small; lia).
           pose proof (regs_kept_of_st_ok_pi (PI := PB_fr) _ _ _ regs (sm_x1 kb) sm_df_kept HS HAE2
             ltac:(vm_compute; reflexivity)) as KR.
           cbn [ms_regs restrict] in KR.
           prreg HS (20%bv : bv 5) Q20.
           rewrite ?ew_ewset_other in Q20 by lia. rewrite U20 in Q20.
           pose proof (st_ok_pi_region_nth _ _ _ 0 _ HS eq_refl) as RG0.
           pose proof (st_ok_pi_region_nth _ _ _ 2 _ HS eq_refl) as RG2.
           pose proof (st_ok_pi_region_nth _ _ _ 3 _ HS eq_refl) as RG3.
           pose proof (st_ok_pi_region_nth _ _ _ 4 _ HS eq_refl) as RG4.
           cbn [ms_mem restrict] in RG0, RG2, RG3, RG4.
           assert (V144 : val_mem segs (arm W (ms_mem ms0)) (F + 144) 8 (N1 - 1))
             by (eapply (field_of_region _ _ 9%nat F _ _ _ _ _ 144 8%N _ _ RG0);
                 [exact EV9 | left; reflexivity | cbn [sv_denot]; rewrite EV6; f_equal; lia | zside | zside]).
           assert (Vdd' : val_mem segs (arm W (ms_mem ms0)) (rg_send_dead fr_RG) 1 1)
             by (replace (rg_send_dead fr_RG) with (0x5d9564 + -1892) by lia;
                 eapply (field_of_region _ _ 345%nat 0x5d9564 _ _ _ _ _ (-1892) 1%N _ _ RG2);
                 [exact EV345 | left; reflexivity | cbn [sv_denot]; rewrite EV23; reflexivity | zside | zside]).
           assert (Vgn' : val_mem segs (arm W (ms_mem ms0)) (rg_gone fr_RG) 1 1)
             by (replace (rg_gone fr_RG) with (0x5d955c + -1916) by lia;
                 eapply (field_of_region _ _ 344%nat 0x5d955c _ _ _ _ _ (-1916) 1%N _ _ RG3);
                 [exact EV344 | left; reflexivity | cbn [sv_denot]; rewrite EV23; reflexivity | zside | zside]).
           assert (Vcl' : val_mem segs (arm W (ms_mem ms0)) (rg_client fr_RG) 4 cl)
             by (replace (rg_client fr_RG) with (0xa2540 + 32) by lia;
                 eapply (field_of_region _ _ 340%nat 0xa2540 _ _ _ _ _ 32 4%N _ _ RG4);
                 [exact EV340 | left; reflexivity | reflexivity | zside | zside]).
           pmkst HS. apply SRr_ret. unfold sm_df_post_x; cbv beta. split; [reflexivity|].
           exists false. do 3 eexists. split; [rewrite EN, Hodd; reflexivity|].
           split; [reflexivity|]. split; [exact HJ|].
           split; [apply (sm_kept_trans W mem (ms_mem ms) (ms_mem ms0));
                   [apply (sm_kept_run W _ _ mem (ms_mem ms) _ HFra HGa); sm_inX
                   | apply (sm_kept_run W _ _ (ms_mem ms) (ms_mem ms0) _ HFr HG0); sm_inX]|].
           split; [exact (mem_grows_trans _ _ _ HGa HG0)|].
           split; [rewrite EN; exact V144|].
           split; [exact Vdd'|]. split; [exact Vgn'|]. split; [exact Vcl'|].
           split; [intros Hf; discriminate Hf|].
           split; [exact KR|]. rewrite EN. rewrite Q20. reflexivity.
      * (* odd: to pthread_mutex_lock *)
        paj_run_tok_x RUN HS HJ SHOK SMspan.
        -- sm_df_awr.
        -- rename HF into HFb, HFr into HFrb, HG0 into HGb.
           (* pthread_mutex_lock (&g_lock): a0 = s4 = A_OBJ 3 *)
           pmkst HS.
           prreg HS (1%bv : bv 5) Q1. prreg HS (2%bv : bv 5) Q2. prreg HS (3%bv : bv 5) Q3.
           prreg HS (4%bv : bv 5) Q4. prreg HS (10%bv : bv 5) Q10.
           rewrite ?ew_ewset_other in Q2, Q3, Q4, Q10 by lia.
           rewrite E2 in Q2. rewrite E3 in Q3. rewrite E4 in Q4. rewrite E244 in Q10.
           assert (Usp : spZ (ms_regs ms0) = F) by (unfold spZ; rewrite Q2; apply unsigned_lit_small; lia).
           pose proof HLK as (LK0 & LK4 & LK8 & LKW). unfold arm in LK0, LK4, LK8, LKW.
           assert (KL1 : forall a, rg_lock fr_RG <= a < rg_lock fr_RG + 12 ->
               aview segs (w_H W) (ms_mem ms0) a = aview segs (w_H W) mem a).
           { intros a Ha. transitivity (aview segs (w_H W) (ms_mem ms) a).
             - apply (aview_kept_out _ _ _ _ _ HFrb a ltac:(lia)). sm_notw.
             - apply (aview_kept_out _ _ _ _ _ HFra a ltac:(lia)). sm_notw. }
           pose proof (ajournal_gx_AR_x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as HARc.
           assert (HNOWN : forall a, rg_lock fr_RG <= a < rg_lock fr_RG + 12 -> ~ aowned B ly S a).
           { intros a Ha Ho. destruct (HG a (HGlk a Ha)) as (Hi & Hno & _). apply Hno.
             exact (proj1 (alx_owned_image _ _ _ LAWS ly S Hp W (ms_mem ms0) _ a HARc Hi) Ho). }
           assert (LKV : forall a, rg_lock fr_RG <= a < rg_lock fr_RG + 12 ->
               aview segs (w_H W) (ms_mem ms0) a <> None).
           { intros a Ha. rewrite (KL1 a Ha).
             destruct (Z_lt_le_dec a (rg_lock fr_RG + 4)) as [h1 | h1];
               [exact (sm_av_ne W mem _ 4 0 a LK0 ltac:(cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia)) |].
             destruct (Z_lt_le_dec a (rg_lock fr_RG + 8)) as [h2 | h2];
               [ exact (sm_av_ne W mem _ 4 0 a LK4 ltac:(cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia))
               | exact (sm_av_ne W mem _ 4 0 a LK8 ltac:(cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia)) ]. }
           assert (AVL : aview segs (w_H W) (ms_mem ms0) (rg_lock fr_RG) = Some 0)
             by (rewrite (KL1 (rg_lock fr_RG) ltac:(lia)); exact (sm_av0 W mem _ LK0)).
           assert (LK4m : val_mem segs (mrestrict (w_H W) (ms_mem ms0)) (rg_lock fr_RG + 4) 4 0).
           { apply (val_mem_moved segs (w_H W) (w_H W) mem (ms_mem ms0) (rg_lock fr_RG + 4) (rg_lock fr_RG + 4) 4 0);
               [intros j Hj; apply KL1; cbn in Hj; lia | exact LK4]. }
           eapply SRr_bind.
           { eapply (aj_gx_entry_at_x B PST ARx LAWS G_fr 0 [] ESTACK (SIGMA WS_pthread_mutex_lock)
               (fun a => rg_lock fr_RG + 4 <= a < rg_lock fr_RG + 8)
               (fun (_ : bvmap 5 word) (mem' : word -> option byte) =>
                  val_mem segs (mrestrict (w_H W) mem') (rg_lock fr_RG + 4) 4 16)
               W (ms_regs ms0) (ms_mem ms0) STK sp0 FP ly0 S0 Hp0 W0 mem0 md0 own ly S Hp _ kk (F - sp0) _ HG eq_refl HJ
               ltac:(rewrite Usp; lia) Hs16 ltac:(lia) ltac:(lia) ltac:(lia) Q3 Q4 Q1
               (ret_ok_codeptr_v 10028 ltac:(lia) eq_refl)).
             - intros a. lia.
             - intros a Ha _. exact (LKV a ltac:(lia)).
             - intros a Ha HnG. exfalso. apply HnG. apply HGlk. lia.
             - intros HPRE2 HSC2.
               exact (ALOCK ly S Hp W (ms_regs ms0) (ms_mem ms0) _ (rg_lock fr_RG) 0 HPRE2 Q10
                 ltac:(lia) ltac:(rewrite HRlk; reflexivity) ltac:(lia) AVL eq_refl LK4m
                 ltac:(intros a Ha; split; [exact (LKV a ltac:(lia)) | rewrite Usp; lia])
                 ltac:(intros a Ha; split;
                       [ apply (sm_wkeep W (ms_mem ms) (ms_mem ms0) a HGb);
                         apply (sm_wkeep W mem (ms_mem ms) a HGa);
                         replace a with (rg_lock fr_RG + (a - rg_lock fr_RG)) by lia; apply LKW; lia
                       | split; [apply HNOWN; lia | rewrite Usp; lia] ])
                 (fun a Ha HK => proj2 (proj2 (HG a (HGlk a ltac:(lia)))) (proj1 (proj2 HK)))). }
           cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HP2 & HLK2 & Hfr2 & Hpres2).
           jafter_call_keep_hi HS 600%nat regs2 (mrestrict (w_H W) mem2) HP2 [0; 1; 2; 3; 4]%nat HS2.
           match type of HS2 with ?ty -> _ => assert (HRK : ty); [|specialize (HS2 HRK); clear HRK] end.
           { cbn [ms_mem restrict].
             repeat apply Forall_cons; [| | | | | apply Forall_nil];
               (eapply region_kept_aview; [sm_base | intros a Ha; apply Hfr2; lia | exact Hpres2]). }
           clear HS. rewrite <- restrict_mkst_fx in HS2. rename HS2 into HS.
           (* back from the lock: ld a0,32(s1); li a1,-1; sw a1,32(a0) (g_client := -1); to the unlock *)
           let Ev := sm_env HS in
           assert (HEIl : img_env VAL A_LIM Ev)
             by (apply img_env_havoc_hi; [assumption | cbv; lia]);
           assert (SHOK2 : sh_ok segs sm_Bx [] Ev (mrestrict (w_H W) mem2)) by (unfold sh_ok; constructor).
           paj_run_tok_x RUN HS HJ2 SHOK2 SMspan.
           ++ sm_df_awr.
           ++ rename HF into HFc, HFr into HFrc, HG0 into HGc.
              (* pthread_mutex_unlock (&g_lock): a0 = s4 = A_OBJ 3, kept by the lock *)
              pmkst HS.
              prreg HS (1%bv : bv 5) R1. prreg HS (2%bv : bv 5) R2. prreg HS (3%bv : bv 5) R3.
              prreg HS (4%bv : bv 5) R4. prreg HS (10%bv : bv 5) R10.
              rewrite ?ew_ewset_other in R2, R3, R4, R10 by lia.
              rewrite E2 in R2. rewrite E3 in R3. rewrite E4 in R4. rewrite E244 in R10.
              assert (Usp3 : spZ (ms_regs ms1) = F) by (unfold spZ; rewrite R2; apply unsigned_lit_small; lia).
              assert (KL3 : forall a, rg_lock fr_RG <= a < rg_lock fr_RG + 12 ->
                  aview segs (w_H W) (ms_mem ms1) a = aview segs (w_H W) mem2 a).
              { intros a Ha. apply (aview_kept_out _ _ _ _ _ HFrc a ltac:(lia)). sm_notw. }
              assert (KL13 : forall a, rg_lock fr_RG <= a < rg_lock fr_RG + 12 ->
                  ~ (rg_lock fr_RG + 4 <= a < rg_lock fr_RG + 8) ->
                  aview segs (w_H W) (ms_mem ms1) a = aview segs (w_H W) mem a).
              { intros a Ha Hn. rewrite (KL3 a Ha), (Hfr2 a ltac:(lia) Hn ltac:(lia)), (KL1 a Ha). reflexivity. }
              assert (V0u : val_mem segs (mrestrict (w_H W) (ms_mem ms1)) (rg_lock fr_RG) 4 0).
              { apply (val_mem_moved segs (w_H W) (w_H W) mem (ms_mem ms1) (rg_lock fr_RG) (rg_lock fr_RG) 4 0); [|exact LK0].
                intros j Hj. cbn in Hj. apply KL13; lia. }
              assert (V8u : val_mem segs (mrestrict (w_H W) (ms_mem ms1)) (rg_lock fr_RG + 8) 4 0).
              { apply (val_mem_moved segs (w_H W) (w_H W) mem (ms_mem ms1) (rg_lock fr_RG + 8) (rg_lock fr_RG + 8) 4 0);
                  [|exact LK8].
                intros j Hj. cbn in Hj. apply KL13; lia. }
              assert (V4u : val_mem segs (mrestrict (w_H W) (ms_mem ms1)) (rg_lock fr_RG + 4) 4 16).
              { apply (val_mem_moved segs (w_H W) (w_H W) mem2 (ms_mem ms1) (rg_lock fr_RG + 4) (rg_lock fr_RG + 4) 4 16);
                  [|exact HLK2].
                intros j Hj. cbn in Hj. apply KL3; lia. }
              assert (AV13 : forall a, rg_lock fr_RG <= a < rg_lock fr_RG + 12 ->
                  aview segs (w_H W) (ms_mem ms1) a <> None).
              { intros a Ha.
                destruct (Z_lt_le_dec a (rg_lock fr_RG + 4)) as [h1 | h1];
                  [exact (sm_av_ne W (ms_mem ms1) _ 4 0 a V0u ltac:(cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia)) |].
                destruct (Z_lt_le_dec a (rg_lock fr_RG + 8)) as [h2 | h2];
                  [ exact (sm_av_ne W (ms_mem ms1) _ 4 16 a V4u ltac:(cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia))
                  | exact (sm_av_ne W (ms_mem ms1) _ 4 0 a V8u ltac:(cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia)) ]. }
              eapply SRr_bind.
              { eapply (aj_gx_entry_at_x B PST ARx LAWS G_fr 0 [] ESTACK (SIGMA WS_pthread_mutex_unlock)
                  (fun a => rg_lock fr_RG + 4 <= a < rg_lock fr_RG + 8)
                  (fun (regs' : bvmap 5 word) (mem' : word -> option byte) =>
                     getr regs' 10 = w64 0 /\ val_mem segs (mrestrict (w_H W) mem') (rg_lock fr_RG + 4) 4 0)
                  W (ms_regs ms1) (ms_mem ms1) STK sp0 FP ly0 S0 Hp0 W0 mem0 md0 own ly S Hp _ kk (F - sp0) _ HG eq_refl HJ2
                  ltac:(rewrite Usp3; lia) Hs16 ltac:(lia) ltac:(lia) ltac:(lia) R3 R4 R1
                  (ret_ok_codeptr_v 10048 ltac:(lia) eq_refl)).
                - intros a. lia.
                - intros a Ha _. exact (AV13 a ltac:(lia)).
                - intros a Ha HnG. exfalso. apply HnG. apply HGlk. lia.
                - intros HPRE3 HSC3.
                  exact (AUNLOCK ly S Hp W (ms_regs ms1) (ms_mem ms1) _ (rg_lock fr_RG) HPRE3 R10
                    ltac:(lia) ltac:(rewrite HRlk; reflexivity) ltac:(lia) V0u V4u V8u
                    ltac:(intros a Ha; split; [exact (AV13 a ltac:(lia)) | rewrite Usp3; lia])
                    ltac:(intros a Ha; split;
                          [ apply (sm_wkeep W mem2 (ms_mem ms1) a HGc);
                            apply (writable_kept (w_H W) (ms_mem ms0) mem2 a (Hpres2 a));
                            apply (sm_wkeep W (ms_mem ms) (ms_mem ms0) a HGb);
                            apply (sm_wkeep W mem (ms_mem ms) a HGa);
                            replace a with (rg_lock fr_RG + (a - rg_lock fr_RG)) by lia; apply LKW; lia
                          | split; [apply HNOWN; lia | rewrite Usp3; lia] ])
                 (fun a Ha HK => proj2 (proj2 (HG a (HGlk a ltac:(lia)))) (proj1 (proj2 HK)))). }
              cbv beta. intros W3 c3 _ (-> & regs3 & mem3 & md3 & -> & HJ3 & HP3 & [HR10 HLK3] & Hfr3 & Hpres3).
              jafter_call_keep_hi HS 616%nat regs3 (mrestrict (w_H W) mem3) HP3 [0; 1; 2; 3; 4]%nat HS3.
              match type of HS3 with ?ty -> _ => assert (HRK : ty); [|specialize (HS3 HRK); clear HRK] end.
              { cbn [ms_mem restrict].
                repeat apply Forall_cons; [| | | | | apply Forall_nil];
                  (eapply region_kept_aview; [sm_base | intros a Ha; apply Hfr3; lia | exact Hpres3]). }
              clear HS. rewrite <- restrict_mkst_fx in HS3. rename HS3 into HS.
              (* back from the unlock: j 0x84ce4; g_gone := 1, s4 := s5 and the latch *)
              let Ev := sm_env HS in
              assert (HEIu : img_env VAL A_LIM Ev)
                by (apply img_env_havoc_hi; [exact HEIl | cbv; lia]);
              assert (SHOK3 : sh_ok segs sm_Bx [] Ev (mrestrict (w_H W) mem3)) by (unfold sh_ok; constructor).
              paj_run_to_tok_x RUNTO HS HJ3 SHOK3 SMspan AF_LLVM_latch.
              ** sm_df_awr.
              ** let Ev := sm_env HS in
                 assert (HAE2 : env_agree 32 (Ereg regs (sm_x1 kb)) Ev)
                   by (apply env_agree_havoc_ge; [cbv; lia|]; apply env_agree_havoc_ge; [cbv; lia|];
                       split; [intros q Hq; rewrite ?ew_ewset_other by lia; exact (proj1 HAE q Hq)
                              | rewrite ?ed_ewset; exact (proj2 HAE)]);
                 assert (EV9 : bv_unsigned (ew Ev 9) = F) by sm_base;
                 assert (EV344 : bv_unsigned (ew Ev 344) = 0x5d955c) by sm_base;
                 assert (EV345 : bv_unsigned (ew Ev 345) = 0x5d9564) by sm_base;
                 assert (EV340 : bv_unsigned (ew Ev 340) = 0xa2540) by sm_base;
                 assert (EV23 : bv_unsigned (ew Ev 23) = 1) by sm_base;
                 assert (EV6 : bv_unsigned (ew Ev 6) = N1)
                   by (repeat (first [rewrite ew_ewset_other by (cbv; lia) | rewrite ew_havoc_old by (cbv; lia)]);
                       rewrite E6; apply unsigned_lit_small; lia).
                 pose proof (regs_kept_of_st_ok_pi (PI := PB_fr) _ _ _ regs (sm_x1 kb) sm_df_kept HS HAE2
                   ltac:(vm_compute; reflexivity)) as KR.
                 cbn [ms_regs restrict] in KR.
                 prreg HS (20%bv : bv 5) Q20.
                 repeat (first [rewrite ew_ewset_other in Q20 by (cbv; lia) | rewrite ew_havoc_old in Q20 by (cbv; lia)]).
                 rewrite U20 in Q20.
                 pose proof (st_ok_pi_region_nth _ _ _ 0 _ HS eq_refl) as RG0.
                 pose proof (st_ok_pi_region_nth _ _ _ 2 _ HS eq_refl) as RG2.
                 pose proof (st_ok_pi_region_nth _ _ _ 3 _ HS eq_refl) as RG3.
                 pose proof (st_ok_pi_region_nth _ _ _ 4 _ HS eq_refl) as RG4.
                 cbn [ms_mem restrict] in RG0, RG2, RG3, RG4.
                 assert (V144 : val_mem segs (arm W (ms_mem ms2)) (F + 144) 8 (N1 - 1))
                   by (eapply (field_of_region _ _ 9%nat F _ _ _ _ _ 144 8%N _ _ RG0);
                       [exact EV9 | left; reflexivity | cbn [sv_denot]; rewrite EV6; f_equal; lia | zside | zside]).
                 assert (Vdd' : val_mem segs (arm W (ms_mem ms2)) (rg_send_dead fr_RG) 1 dd)
                   by (replace (rg_send_dead fr_RG) with (0x5d9564 + -1892) by lia;
                       eapply (field_of_region _ _ 345%nat 0x5d9564 _ _ _ _ _ (-1892) 1%N _ _ RG2);
                       [exact EV345 | left; reflexivity | reflexivity | zside | zside]).
                 assert (Vgn' : val_mem segs (arm W (ms_mem ms2)) (rg_gone fr_RG) 1 1)
                   by (replace (rg_gone fr_RG) with (0x5d955c + -1916) by lia;
                       eapply (field_of_region _ _ 344%nat 0x5d955c _ _ _ _ _ (-1916) 1%N _ _ RG3);
                       [exact EV344 | left; reflexivity | cbn [sv_denot]; rewrite EV23; reflexivity | zside | zside]).
                 assert (Vcl' : val_mem segs (arm W (ms_mem ms2)) (rg_client fr_RG) 4 (2 ^ 32 - 1))
                   by (replace (rg_client fr_RG) with (0xa2540 + 32) by lia;
                       eapply (sm_val_m1 _ _ 340%nat 0xa2540 _ _ _ _ _ 32 _ RG4);
                       [ exact EV340 | left; reflexivity
                       | cbn [sv_denot]; apply bv_eq; rewrite !Z_to_bv_unsigned; vm_compute; reflexivity ]).
                 assert (VLK : val_mem segs (arm W (ms_mem ms2)) (rg_lock fr_RG + 4) 4 0).
                 { apply (val_mem_moved segs (w_H W) (w_H W) mem3 (ms_mem ms2) (rg_lock fr_RG + 4)
                     (rg_lock fr_RG + 4) 4 0); [|exact HLK3].
                   intros j Hj. cbn in Hj.
                   apply (aview_kept_out _ _ _ _ _ HFr (rg_lock fr_RG + 4 + j) ltac:(lia)). sm_notw. }
                 pmkst HS. apply SRr_ret. unfold sm_df_post_x; cbv beta. split; [reflexivity|].
                 exists true. do 3 eexists. split; [rewrite EN, Hodd; reflexivity|].
                 split; [reflexivity|]. split; [exact HJ3|].
                 split.
                 { apply (sm_kept_trans W mem (ms_mem ms) (ms_mem ms2));
                     [apply (sm_kept_run W _ _ mem (ms_mem ms) _ HFra HGa); sm_inX|].
                   apply (sm_kept_trans W (ms_mem ms) (ms_mem ms0) (ms_mem ms2));
                     [apply (sm_kept_run W _ _ (ms_mem ms) (ms_mem ms0) _ HFrb HGb); sm_inX|].
                   apply (sm_kept_trans W (ms_mem ms0) mem2 (ms_mem ms2));
                     [ apply (sm_kept_call W (ms_mem ms0) mem2 _ _ _ _ Hfr2 Hpres2); intros a Ha; cbv beta in Ha;
                       unfold XS, sm_df_XG; cbn [app]; sm_inFP |].
                   apply (sm_kept_trans W mem2 (ms_mem ms1) (ms_mem ms2));
                     [apply (sm_kept_run W _ _ mem2 (ms_mem ms1) _ HFrc HGc); sm_inX|].
                   apply (sm_kept_trans W (ms_mem ms1) mem3 (ms_mem ms2));
                     [ apply (sm_kept_call W (ms_mem ms1) mem3 _ _ _ _ Hfr3 Hpres3); intros a Ha; cbv beta in Ha;
                       unfold XS, sm_df_XG; cbn [app]; sm_inFP |].
                   apply (sm_kept_run W _ _ mem3 (ms_mem ms2) _ HFr HG0); sm_inX. }
                 split.
                 { apply (mem_grows_trans _ _ _ HGa). apply (mem_grows_trans _ _ _ HGb).
                   apply (mem_grows_trans _ _ _ (sm_grows_of_pres W _ _ Hpres2)). apply (mem_grows_trans _ _ _ HGc).
                   apply (mem_grows_trans _ _ _ (sm_grows_of_pres W _ _ Hpres3)). exact HG0. }
                 split; [rewrite EN; exact V144|].
                 split; [exact Vdd'|]. split; [exact Vgn'|]. split; [exact Vcl'|].
                 split; [intros _; exact VLK|].
                 split; [exact KR|]. rewrite EN. rewrite Q20. reflexivity.
Qed.

Ltac sm_nXG Hin :=
  unfold sm_df_XG in Hin; cbn [app] in Hin;
  repeat (apply inFP_cons in Hin as [Hin | Hin]; [sm_rgl|]); exact (inFP_nil _ Hin).

Lemma sm_aout_df_x : forall ly S (W : world segs) mem md mem' F c O mx no cap out (g : bool),
  ARE ly S W mem md -> alloc_ceiling + 1024 + ESTACK <= F -> KEPT W mem mem' (XS F (sm_df_XG g)) ->
  mem_grows (mrestrict (w_H W) mem) (mrestrict (w_H W) mem') ->
  aout_at B fr_RG ly S W mem c O mx no cap out ->
  val_mem segs (arm W mem') (rg_send_dead fr_RG) 1 (if g then ct_dd c else 1) ->
  val_mem segs (arm W mem') (rg_client fr_RG) 4 (if g then 2 ^ 32 - 1 else ct_cl c mod 2 ^ 32) ->
  aout_at B fr_RG ly S W mem'
    (CTL (if g then -1 else ct_cl c) (ct_br c) (if g then ct_dd c else 1) (ct_ei c) (ct_ev c)) O mx no cap out.
Proof.
  intros ly S W mem md mem' F c O mx no cap out g HAR HF HK HGr Ho Vdd Vcl.
  pose proof (sm_df_xgok g) as HXG.
  assert (HXOK : XOK (XS F (sm_df_XG g))) by (apply sm_xok; [exact HF | exact HXG]).
  pose proof sm_ceil_lo as Hac. pose proof (sm_errno B TL) as (HE0 & HE1). pose proof HERRHI as HEH.
  assert (HES : ESTACK = 4096) by reflexivity.
  assert (CK : forall a, aout_glob B a -> ~ (rg_send_dead fr_RG <= a < rg_send_dead fr_RG + 1) ->
      ~ (rg_client fr_RG <= a < rg_client fr_RG + 4) -> abyte_kept W mem W mem' a).
  { intros a Ha H1 H2. apply (sm_kept_ng W mem mem' F (sm_df_XG g) HK);
      [unfold aout_glob in Ha; sm_rgl | unfold aout_glob in Ha; sm_rgl | unfold aout_glob in Ha; sm_rgl |].
    intros Hin. unfold aout_glob in Ha. destruct g; sm_nXG Hin. }
  assert (KV : forall a n v, (forall x, a <= x < a + Z.of_nat n -> aout_glob B x) ->
      (forall x, a <= x < a + Z.of_nat n -> ~ (rg_send_dead fr_RG <= x < rg_send_dead fr_RG + 1)) ->
      (forall x, a <= x < a + Z.of_nat n -> ~ (rg_client fr_RG <= x < rg_client fr_RG + 4)) ->
      val_mem segs (arm W mem) a n v -> val_mem segs (arm W mem') a n v).
  { intros a n v H1 H2 H3 Hv. apply (akept_vm W mem); [|exact Hv].
    intros x Hx. apply CK; [exact (H1 x Hx) | exact (H2 x Hx) | exact (H3 x Hx)]. }
  destruct Ho as (O1 & O2 & O3 & O4 & O5 & O6 & O7 & O8 & O9 & O10 & O11 & O12 & O13 & O14 & O15 & O16 & O17 & O18 &
    O19 & O20 & O21 & O22 & O23 & O24 & O25 & O26).
  unfold aout_at. cbn [ct_cl ct_br ct_dd ct_ei ct_ev].
  split; [sm_kv KV O1|]. split; [exact (sm_awr W mem mem' _ _ HGr O2)|].
  split; [sm_kv KV O3|]. split; [exact (sm_awr W mem mem' _ _ HGr O4)|].
  split; [sm_kv KV O5|]. split; [exact (sm_awr W mem mem' _ _ HGr O6)|].
  split; [sm_kv KV O7|]. split; [exact (sm_awr W mem mem' _ _ HGr O8)|].
  split; [destruct g; exact Vcl|]. split; [exact (sm_awr W mem mem' _ _ HGr O10)|].
  split; [sm_kv KV O11|]. split; [exact (sm_awr W mem mem' _ _ HGr O12)|].
  split; [destruct g; exact Vdd|]. split; [exact (sm_awr W mem mem' _ _ HGr O14)|].
  split; [sm_kv KV O15|]. split; [exact (sm_awr W mem mem' _ _ HGr O16)|].
  split; [sm_kv KV O17|]. split; [exact (sm_awr W mem mem' _ _ HGr O18)|].
  split; [exact O19|]. split; [destruct g; [right; reflexivity | exact O20]|].
  split; [exact O21|]. split; [destruct g; [exact O22 | right; reflexivity]|].
  split; [exact O23|]. split; [exact O24|]. split; [exact O25|].
  destruct O26 as [O26 | (Hc & Hno & Hin & junk & Hj & Hg)]; [left; exact O26 | right].
  split; [exact Hc|]. split; [exact Hno|]. split; [exact Hin|]. exists junk. split; [exact Hj|].
  apply (akept_garr8 W mem); [|exact Hg]. intros x Hx. unfold bzs in Hx. rewrite length_map, length_app, Nat2Z.inj_add in Hx.
  apply (sm_blk_kept_x ly S W mem md mem' (XS F (sm_df_XG g)) out cap x HAR HXOK HK Hin ltac:(lia)).
  pose proof (req_size_pos cap ltac:(lia)) as [_ Hq]. lia.
Qed.

Lemma sm_amodel_df_x : forall ly S (W : world segs) mem md mem' F cx m (g : bool),
  ARE ly S W mem md -> alloc_ceiling + 1024 + ESTACK <= F ->
  KEPT W mem mem' (XS F (sm_df_XG g)) -> mem_grows (mrestrict (w_H W) mem) (mrestrict (w_H W) mem') ->
  amodel_at B ly S W mem m -> lm_O m = [] ->
  val_mem segs (arm W mem') (rg_send_dead fr_RG) 1 (if g then ct_dd (lm_c m) else 1) ->
  val_mem segs (arm W mem') (rg_gone fr_RG) 1 1 ->
  val_mem segs (arm W mem') (rg_client fr_RG) 4 (if g then 2 ^ 32 - 1 else ct_cl (lm_c m) mod 2 ^ 32) ->
  (g = true -> val_mem segs (arm W mem') (rg_lock fr_RG + 4) 4 0) ->
  amodel_at B ly S W mem' (sm_default cx m g).
Proof.
  intros ly S W mem md mem' F cx m g HAR HF HK HGr HM HO Vdd Vgn Vcl Vlk.
  pose proof sm_ceil_lo as Hac. assert (HES : ESTACK = 4096) by reflexivity.
  pose proof (sm_df_xgok g) as HXG.
  assert (CK : forall lo n, 0 <= lo -> lo + n <= alloc_ceiling -> (forall a, lo <= a < lo + n -> ~ inFP (sm_df_XG g) a) ->
      forall a, lo <= a < lo + n -> abyte_kept W mem W mem' a).
  { intros lo n H0 H1 Hd. apply (sm_cell_kept W mem mem' F (sm_df_XG g) lo n HK); [lia | lia | lia | exact Hd]. }
  pose proof HM as (M1 & M2 & M3 & M4 & M5 & M6 & M7 & M8 & M9 & M10 & M11 & M12 & M13).
  unfold amodel_at, sm_default. cbn [lm_hs lm_G lm_es lm_c lm_O lm_mx lm_cap lm_out lm_gn lm_nfd].
  split; [exact M1|].
  split.
  { intros j Hj. apply (sm_aslot_kept_x ly S W mem md mem' F (sm_df_XG g) j _ HAR HF HXG HK HGr Hj); [|exact (M2 j Hj)].
    intros a Ha Hin. destruct g; sm_nXG Hin. }
  split.
  { apply (sm_arelay_kept_x ly S W mem md mem' F (sm_df_XG g) (lm_G m) (lm_es m) HAR HF HXG HK); [|exact M3].
    intros a Ha Hin. destruct g; sm_nXG Hin. }
  split.
  { rewrite HO in M4. exact (sm_aout_df_x ly S W mem md mem' F _ _ _ _ _ _ g HAR HF HK HGr M4 Vdd Vcl). }
  split.
  { split; [exact Vgn|]. split; [exact (sm_awr W mem mem' _ _ HGr (proj1 (proj2 M5)))|]. right; reflexivity. }
  split.
  { pose proof M6 as (L0 & L4 & L8 & LW). destruct g.
    - split; [|split; [|split]].
      + apply (akept_vm W mem); [|exact L0]. intros x Hx. cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in Hx.
        apply (CK (rg_lock fr_RG) 4); [sm_rgl | sm_rgl | intros y Hy Hin; sm_nXG Hin | lia].
      + exact (Vlk eq_refl).
      + apply (akept_vm W mem); [|exact L8]. intros x Hx. cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in Hx.
        apply (CK (rg_lock fr_RG + 8) 4); [sm_rgl | sm_rgl | intros y Hy Hin; sm_nXG Hin | lia].
      + exact (sm_awr W mem mem' _ _ HGr LW).
    - apply (alock_at_kept fr_RG W mem W mem' _ M6). intros r Hr a Ha. destruct Hr as [<- | []]. cbn [fst snd] in Ha.
      apply (CK (rg_lock fr_RG) 12); [sm_rgl | sm_rgl | intros y Hy Hin; sm_nXG Hin | exact Ha]. }
  split.
  { apply (awake_at_kept fr_RG W mem W mem' M7). intros r Hr a Ha. destruct Hr as [<- | []]. cbn [fst snd] in Ha.
    apply (CK (rg_wake fr_RG + 4) 4); [sm_rgl | sm_rgl | intros y Hy Hin; destruct g; sm_nXG Hin | lia]. }
  split.
  { apply (akept_vm W mem); [|exact M8]. intros x Hx.
    apply (CK AG_NFD 4); [sm_rgl | sm_rgl | intros y Hy Hin; destruct g; sm_nXG Hin | lia]. }
  split.
  { apply (akept_awr W mem); [|exact M9]. intros x Hx.
    apply (CK AG_NFD 4); [sm_rgl | sm_rgl | intros y Hy Hin; destruct g; sm_nXG Hin | lia]. }
  split; [exact M10|].
  split.
  { apply (akept_vm W mem); [|exact M11]. intros x Hx.
    apply (CK AG_THREAD_UP 1); [sm_rgl | sm_rgl | intros y Hy Hin; destruct g; sm_nXG Hin | lia]. }
  split.
  { destruct M12 as (lst & M12). exists lst. apply (akept_vm W mem); [|exact M12]. intros x Hx.
    apply (CK AG_LISTEN 4); [sm_rgl | sm_rgl | intros y Hy Hin; destruct g; sm_nXG Hin | lia]. }
  apply (akept_awr W mem); [|exact M13]. intros x Hx.
  apply (CK AG_LISTEN 4); [sm_rgl | sm_rgl | intros y Hy Hin; destruct g; sm_nXG Hin | lia].
Qed.

Theorem lf_arm_default_x : forall cx Hp t W c,
  lf_base_x B MT XM_LIB RLO RHI fr_live_pre LIBROOM NP G_fr ARx cx Hp -> INV_A_x B NP G_fr fr_FP PST ARx LSx RINV 9 cx Hp t W c ->
  SRr segs W c (INV_K_x B NP G_fr fr_FP PST ARx LSx RINV cx Hp t).
Proof.
  intros cx Hp t W c HB HA.
  destruct HA as (regs & regsD & mem & md & Hc & Hkept & HopD & _ & HROM & HLF).
  destruct HLF as (own & ly3 & S3 & Hp3 & kk & m & fpos & HJ & Hown & Hframe & Hflag & Hmodel & Hinput & Hrom & Hsep &
    HLS & HNP & HRINV & HRD).
  subst own.
  pose proof HRD as (Hcommon & HD25 & Htb & Hkb & HO & Hoprest).
  cbv zeta in Hoprest. destruct Hoprest as (Hop11 & Hpick).
  assert (Hopeq : in_byte cx (lm_k m) mod 10 = 9).
  { pose proof (Z.mod_pos_bound (in_byte cx (lm_k m)) 10 ltac:(lia)) as Hmb.
    apply (f_equal bv_unsigned) in HopD. rewrite Hop11 in HopD.
    rewrite !unsigned_lit_small in HopD by lia. lia. }
  rewrite Hopeq in Hpick.
  assert (Hpk9 : picks 9 = false) by reflexivity.
  rewrite Hpk9 in Hpick. destruct Hpick as (HD20 & HD6 & _).
  assert (HARx : ARx ly3 S3 Hp3 W mem md) by (eapply ajournal_gx_AR_x; exact HJ).
  assert (HAR : ARE ly3 S3 W mem md) by (exists Hp3; exact HARx).
  assert (Hfin : In (1, fpos) (frames S3)).
  { pose proof HJ as (_ & _ & (memS & HJ0 & _) & _). pose proof HJ0 as (_ & _ & _ & _ & _ & Hfrs & _).
    rewrite Hfrs. left. reflexivity. }
  destruct HB as (HAI & Hpre). pose proof Hpre as (Hafn & _ & _ & _ & _ & Hlen & _).
  pose proof Hafn as (_ & _ & _ & _ & _ & Hstk & _).
  pose proof Hstk as (Hsp16 & HstkK & Hceil & Hlo & Hhi & Hhi2 & _).
  set (sp0 := spZ (c_regs cx)) in *.
  assert (HSTK : LLVMF_STK = 32768) by reflexivity.
  pose proof sm_ceil_lo as Hac. assert (HES : ESTACK = 4096) by reflexivity.
  assert (Hsp0 : alloc_ceiling + 32768 <= sp0 <= 2 ^ 47) by lia.
  pose proof (Z.mod_pos_bound (sp0 - 320) 32 ltac:(lia)) as Hm32.
  assert (HFeq : lf_F cx = sp0 - 320 - (sp0 - 320) mod 32) by reflexivity.
  assert (HFbound : 2 ^ 46 <= lf_F cx <= 2 ^ 47) by lia.
  assert (HFmod : lf_F cx mod 32 = 0)
    by (rewrite HFeq; rewrite Zminus_mod, Zmod_mod, Z.sub_diag; reflexivity).
  assert (HF16 : (lf_F cx - sp0) mod 16 = 0).
  { pose proof (Z.div_mod (lf_F cx) 32 ltac:(lia)) as D1. pose proof (Z.div_mod sp0 16 ltac:(lia)) as D2.
    rewrite HFmod in D1. rewrite Hsp16 in D2.
    replace (lf_F cx - sp0) with ((2 * (lf_F cx / 32) - sp0 / 16) * 16) by lia. apply Z_mod_mult. }
  assert (KD : forall r : bv 5, In r jt_kept -> getr regs r = getr regsD r) by exact Hkept.
  pose proof Hcommon as (C2 & C8 & C9 & C18 & C19 & C23 & C24 & C26 & C27 & C3 & C4).
  assert (Hr2 : getr regs 2 = w64 (lf_F cx)) by (rewrite (KD 2%bv ltac:(sm_in)); exact C2).
  assert (Hr3 : getr regs 3 = w64 (as_gp B)) by (rewrite (KD 3%bv ltac:(sm_in)); exact C3).
  assert (Hr4 : getr regs 4 = w64 (as_tp B)) by (rewrite (KD 4%bv ltac:(sm_in)); exact C4).
  assert (Hr23 : getr regs 23 = w64 1) by (rewrite (KD 23%bv ltac:(sm_in)); exact C23).
  assert (Hr9 : getr regs 9 = w64 (lf_F cx)) by (rewrite (KD 9%bv ltac:(sm_in)); exact C9).
  assert (Hr27 : getr regs 27 = w64 SB) by (rewrite (KD 27%bv ltac:(sm_in)); exact C27).
  assert (Hr20 : getr regs 20 = w64 (c_p cx + lm_k m + 1)) by (rewrite (KD 20%bv ltac:(sm_in)); exact HD20).
  assert (Hr6 : getr regs 6 = w64 (c_n cx - lm_k m - 1)) by (rewrite (KD 6%bv ltac:(sm_in)); exact HD6).
  (* the input block and the byte in.p[0] *)
  pose proof Hinput as [[[Hn0 _] | [Hnr Hblk]] Hgarr]; [lia|].
  destruct (alx_blocks _ _ _ LAWS _ _ _ _ _ _ _ _ HARx Hblk) as (Hp16 & Hp4096 & Hpceil & Hpia & _ & _).
  pose proof (sm_blk_off_x _ _ _ _ _ _ _ _ HARx Hblk ltac:(lia)) as Hpimg.
  unfold OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B.YCbq.off_img in Hpimg.
  pose proof (req_size_pos (c_n cx) ltac:(lia)) as [_ Hreq].
  pose proof (sm_in_byte_rng cx (lm_k m + 1)) as Hkb8.
  (* the frame's three address copies, the stream's two flags, g_gone and the lock *)
  pose proof Hframe as (_ & Hawr & F32 & F40 & _ & _ & F64 & _).
  assert (HW1 : forall a, lf_F cx + 144 <= a < lf_F cx + 152 -> writable_at segs (arm W mem) a).
  { intros a Ha. replace a with (lf_F cx + (a - lf_F cx)) by lia. apply Hawr. lia. }
  pose proof Hmodel as (_ & _ & _ & Hout & Hgone & Hlock & _).
  pose proof Hout as (_ & _ & _ & _ & _ & _ & _ & _ & Ocl & Owcl & _ & _ & Odd & Owdd & _ & _ & _ & _ & _ & _ & _ &
    Odd01 & _).
  pose proof Hgone as (_ & Owgn & _).
  rewrite Hc.
  eapply SRr_mono.
  { exact (sm_df_run_x W regs mem md LLVMF_STK sp0 (lf_FP fr_FP cx) (c_ly cx) (c_S cx) Hp (c_W cx) (c_mem cx) (c_md cx)
      [(1, fpos)] ly3 S3 Hp3 kk (lf_F cx) (c_p cx + lm_k m + 1) (c_n cx - lm_k m - 1) (in_byte cx (lm_k m + 1))
      (ct_dd (lm_c m)) (ct_cl (lm_c m) mod 2 ^ 32)
      HJ Hr2 Hr3 Hr4 Hr23 Hr9 Hr27 Hr20 Hr6 ltac:(lia) HFbound HFmod ltac:(lia) Hkb8 ltac:(lia) HF16
      ltac:(lia)
      ltac:(intros HN; lia)
      ltac:(intros HN; unfold in_app in Hpia; unfold kLowShadowBeg, kHighMemBeg in *; lia)
      ltac:(intros HN; lia)
      ltac:(intros HN; rewrite <- Z.add_assoc; exact (proj1 (sm_in_byte cx (arm W mem) (lm_k m + 1) Hgarr ltac:(lia))))
      ltac:(intros HN; apply (range_addressable_of_block_hp0_x segs B ARx LAWS HP0 ly3 S3 Hp3 W mem md (c_p cx) (c_n cx));
            [exact HARx | exact Hblk | lia | lia])
      F32 F40 F64 HW1 Odd ltac:(lia) Owdd Owgn Ocl ltac:(apply Z.mod_pos_bound; lia) Owcl Hlock). }
  intros W' c' _ (-> & g & regs' & mem' & md' & Hg & -> & HJ' & KP & HGr & V144 & Vdd & Vgn & Vcl & Vlk & KR & Q20).
  assert (Hgd : g = sm_dg cx m).
  { rewrite Hg. unfold sm_dg. destruct (lm_k m + 1 <? c_n cx) eqn:Ek; [apply Z.ltb_lt in Ek | apply Z.ltb_ge in Ek].
    - replace (c_n cx - lm_k m - 1 =? 0) with false by (symmetry; apply Z.eqb_neq; lia). reflexivity.
    - replace (c_n cx - lm_k m - 1 =? 0) with true by (symmetry; apply Z.eqb_eq; lia). reflexivity. }
  pose proof (sm_df_xgok g) as HXG.
  assert (HXOK : XOK (XS (lf_F cx) (sm_df_XG g))) by (apply sm_xok; [lia | exact HXG]).
  assert (KK : forall r : bv 5, In r sm_df_kept -> In r jt_kept -> getr regs' r = getr regsD r)
    by (intros r H1 H2; rewrite (KR r H1); exact (KD r H2)).
  exists regs', mem', md'. split; [reflexivity|].
  split; [exact (sm_jt_kept W mem mem' _ HXOK KP HROM)|].
  exists [(1, fpos)], ly3, S3, Hp3, kk, (sm_default cx m g), fpos.
  split; [exact HJ'|]. split; [reflexivity|].
  split; [exact (sm_aframe_kept_x cx ly3 S3 W mem md mem' fpos (sm_df_XG g) HAR Hfin Hsp0 HXG KP HGr Hframe)|].
  split; [exact (sm_flag_kept_x ly3 S3 W mem md mem' _ fpos _ HAR HXOK KP Hfin Hflag)|].
  split; [exact (sm_amodel_df_x ly3 S3 W mem md mem' (lf_F cx) cx m g HAR ltac:(lia) KP HGr Hmodel HO Vdd Vgn Vcl Vlk)|].
  split; [exact (sm_ainput_kept_x cx ly3 S3 W mem md mem' _ HAR HXOK KP (eq_sym Hlen) Hinput)|].
  split; [exact (sm_rom_kept W mem mem' _ HXOK KP Hrom)|].
  split; [exact Hsep|].
  split; [rewrite Hgd; exact (LS_default cx t m ly3 S3 HLS)|].
  split; [exact HNP|].
  split; [rewrite Hgd; exact (RI_default cx t m HRINV)|].
  unfold lregs_K, lregs_common, sm_default. cbn [lm_k]. unfold sm_kn.
  split.
  { split; [rewrite (KK 2%bv ltac:(sm_in) ltac:(sm_in)); exact C2|].
    split; [rewrite (KK 8%bv ltac:(sm_in) ltac:(sm_in)); exact C8|].
    split; [rewrite (KK 9%bv ltac:(sm_in) ltac:(sm_in)); exact C9|].
    split; [rewrite (KK 18%bv ltac:(sm_in) ltac:(sm_in)); exact C18|].
    split; [rewrite (KK 19%bv ltac:(sm_in) ltac:(sm_in)); exact C19|].
    split; [rewrite (KK 23%bv ltac:(sm_in) ltac:(sm_in)); exact C23|].
    split; [rewrite (KK 24%bv ltac:(sm_in) ltac:(sm_in)); exact C24|].
    split; [rewrite (KK 26%bv ltac:(sm_in) ltac:(sm_in)); exact C26|].
    split; [rewrite (KK 27%bv ltac:(sm_in) ltac:(sm_in)); exact C27|].
    split; [rewrite (KK 3%bv ltac:(sm_in) ltac:(sm_in)); exact C3|].
    rewrite (KK 4%bv ltac:(sm_in) ltac:(sm_in)); exact C4. }
  split; [rewrite (KK 25%bv ltac:(sm_in) ltac:(sm_in)); exact HD25|].
  split; [exact Htb|].
  unfold sv8.
  destruct (lm_k m + 1 <? c_n cx) eqn:Ek; [apply Z.ltb_lt in Ek | apply Z.ltb_ge in Ek].
  - assert (EN : (c_n cx - lm_k m - 1 =? 0) = false) by (apply Z.eqb_neq; lia).
    rewrite EN in Q20, V144. cbv iota in Q20, V144.
    split; [rewrite Q20; f_equal; lia|].
    split; [replace (c_n cx - (lm_k m + 2)) with (c_n cx - lm_k m - 1 - 1) by lia; exact V144|]. lia.
  - assert (EN : (c_n cx - lm_k m - 1 =? 0) = true) by (apply Z.eqb_eq; lia).
    rewrite EN in Q20, V144. cbv iota in Q20, V144.
    split; [rewrite Q20; f_equal; lia|].
    split; [replace (c_n cx - (lm_k m + 1)) with 0 by lia; exact V144|]. lia.
Qed.

(* ---- THE CHECK: B cut_x Section w's ARM_close / ARM_eintr / ARM_sendmax / ARM_default
   (W_LLVMFuzzerTestOneInput_cut_x.v), restated in their text at cut_x's names (the forms B lib/B/W_LLVMFuzzerTestOneInput_top_x.v uses) and closed by
   `exact` from the four theorems ---- *)
Local Notation BASEx cx Hp := (lf_base_x B MT XM_LIB RLO RHI fr_live_pre LIBROOM NP G_fr ARx cx Hp).
Local Notation IA := (INV_A_x B NP G_fr fr_FP PST ARx LSx RINV).
Local Notation IK := (INV_K_x B NP G_fr fr_FP PST ARx LSx RINV).
Lemma lf_arm_close_x_check : forall cx Hp t W c, BASEx cx Hp -> IA 3 cx Hp t W c -> SRr segs W c (IK cx Hp t).
Proof. exact lf_arm_close_x. Qed.
Lemma lf_arm_eintr_x_check : forall cx Hp t W c, BASEx cx Hp -> IA 6 cx Hp t W c -> SRr segs W c (IK cx Hp t).
Proof. exact lf_arm_eintr_x. Qed.
Lemma lf_arm_sendmax_x_check : forall cx Hp t W c, BASEx cx Hp -> IA 8 cx Hp t W c -> SRr segs W c (IK cx Hp t).
Proof. exact lf_arm_sendmax_x. Qed.
Lemma lf_arm_default_x_check : forall cx Hp t W c, BASEx cx Hp -> IA 9 cx Hp t W c -> SRr segs W c (IK cx Hp t).
Proof. exact lf_arm_default_x. Qed.
(* ---- route R (RULE-SHAPES.md (sha256 2e856ce788dd; internal record) section 0): the four small arms at a world relation R: every text of Section smx that
   names the journal, a cut_x carrier or the step relation, with ajournal_gx_x -> ajournal_gx_xR .. R, INV_*_x /
   lcut_x / LF_x / lf_jour_x -> their B cut_x Section wR twins, SRr segs -> SRrG segs R, the runs and the branch ->
   their SRrG forms (W_journal_x.v paj_run_x_xG / paj_run_to_x_xG, W_kit.v paj_branch_xR), and the default arm's
   lock / unlock sites -> W_sites_x.v aj_gx_entry_at_xR (the strict site contracts ALOCK / AUNLOCK are kept: the
   engine lifts them).  lf_arm_close_xR / lf_arm_eintr_xR / lf_arm_sendmax_xR / lf_arm_default_xR conclude B cut_x
   Section wR's ARM_close_R / ARM_eintr_R / ARM_sendmax_R / ARM_default_R.  The strict text above is unchanged. ---- *)
Section smxR.
Variable R : world segs -> world segs -> Prop.
Hypothesis R_refl : forall W, R W W.
Hypothesis R_trans : forall W1 W2 W3, R W1 W2 -> R W2 W3 -> R W1 W3.
Hypothesis WLE_R : forall W W', @wle segs W W' -> R W W'.
Let RUNG := paj_run_x_xG (PL := PL_fr) (PI := PB_fr) B PST ARx LAWS R G_fr HG 0 [].
Let RUNTOG := paj_run_to_x_xG (PL := PL_fr) (PI := PB_fr) B PST ARx LAWS R G_fr HG 0 [].
Let BRR := paj_branch_xR (R := R) (PI := PB_fr).

(* R twin of sm_fl_post_x *)
Definition sm_fl_post_xR (W : world segs) (regs : bvmap 5 word) (mem : word -> option byte) (STK sp0 : Z)
    (FP : list (Z * Z)) (ly0 : alayout) (S0 : astate) (Hp0 : list Z) (W0 : world segs) (mem0 : word -> option byte) (md0 : Model)
    (own : list (Z * Z)) (ly : alayout) (S : astate) (Hp : list Z) (kk F HA fo N6 : Z) : world segs -> config -> Prop :=
  fun W' c' => W' = W /\ exists regs' mem' md',
    c' = cfg_at segs (fr_B0 + AF_LLVM_latch) regs' mem' md' /\
    ajournal_gx_xR segs B PST ARx R G_fr 0 [] STK sp0 FP ly0 S0 Hp0 W0 mem0 md0 own ly S Hp W mem' md' kk /\
    KEPT W mem mem' (XS F [(HA + fo, HA + fo + 4)]) /\
    mem_grows (mrestrict (w_H W) mem) (mrestrict (w_H W) mem') /\
    val_mem segs (arm W mem') (F + 144) 8 N6 /\ val_mem segs (arm W mem') (HA + fo) 4 1 /\
    (forall r, In r sm_fl_kept -> getr regs' r = getr regs r).
(* R twin of sm_fl_run_x *)
Lemma sm_fl_run_xR : forall (W : world segs) regs mem md STK sp0 FP ly0 S0 Hp0 (W0 : world segs) mem0 md0 own ly S Hp kk
    F HA fo N6 pc,
  (fo = 8 /\ pc = AF_arm_close) \/ (fo = 12 /\ pc = AF_arm_eintr) ->
  ajournal_gx_xR segs B PST ARx R G_fr 0 [] STK sp0 FP ly0 S0 Hp0 W0 mem0 md0 own ly S Hp W mem md kk ->
  getr regs 23 = w64 1 -> getr regs 9 = w64 F -> getr regs 21 = w64 HA -> getr regs 27 = w64 SB ->
  getr regs 6 = w64 N6 -> 0 <= N6 < 2 ^ 64 ->
  2 ^ 46 <= F <= 2 ^ 47 -> F mod 32 = 0 ->
  rg_s fr_RG <= HA <= rg_s fr_RG + 3 * ASRC -> HA mod 32 = 0 ->
  sp0 - STK <= F + 144 -> F + 152 <= sp0 ->
  (forall a, F + 144 <= a < F + 152 -> writable_at segs (arm W mem) a) ->
  (forall a, HA + fo <= a < HA + fo + 4 -> writable_at segs (arm W mem) a) ->
  azs B HA ASRC ->
  YA0nH.SRrG segs R W (cfg_at segs (fr_B0 + pc) regs mem md)
    (sm_fl_post_xR W regs mem STK sp0 FP ly0 S0 Hp0 W0 mem0 md0 own ly S Hp kk F HA fo N6).
Proof.
  intros W regs mem md STK sp0 FP ly0 S0 Hp0 W0 mem0 md0 own ly S Hp kk F HA fo N6 pc Hcase HJ H23 H9 H21 H27 H6 HN6
    HF1 HF2 HH1 HH2 Hs1 Hs2 HW1 HW2 HZ.
  pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
  assert (HAR : ARE ly S W mem md) by (exists Hp; eapply ajournal_gx_AR_xR; exact HJ).
  assert (HRS : rg_s fr_RG = 6131296) by reflexivity.
  assert (HAS : ASRC = 96) by reflexivity.
  assert (Hfo : fo = 8 \/ fo = 12) by (destruct Hcase as [(-> & _) | (-> & _)]; [left | right]; reflexivity).
  destruct (sm_fl_entry_x W regs mem ly S md F HA fo pc HAR H23 H9 H21 H27 HF1 HF2 ltac:(lia) HH2 Hfo HW1 HW2 HZ)
    as [HS SHOK].
  assert (HEI : img_env VAL A_LIM (Eimg (Ereg regs (@nil word)))) by apply Eimg_env.
  assert (HAE : env_agree 32 (Ereg regs (@nil word)) (Eimg (Ereg regs (@nil word))))
    by (split; [intros mm Hmm; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
  assert (EE : forall m (rr : bv 5), Z.of_nat m = bv_unsigned rr -> ew (Eimg (Ereg regs (@nil word))) m = getr regs rr)
    by (intros m rr Hm; pose proof (bv_unsigned_in_range 5 rr) as Hr5;
        change (bv_modulus 5) with 32 in Hr5; rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_nat; exact Hm).
  assert (E9 : ew (Eimg (Ereg regs (@nil word))) 9 = w64 F) by (rewrite (EE 9%nat 9%bv eq_refl); exact H9).
  assert (E21 : ew (Eimg (Ereg regs (@nil word))) 21 = w64 HA) by (rewrite (EE 21%nat 21%bv eq_refl); exact H21).
  assert (E23 : ew (Eimg (Ereg regs (@nil word))) 23 = w64 1) by (rewrite (EE 23%nat 23%bv eq_refl); exact H23).
  assert (E6 : ew (Eimg (Ereg regs (@nil word))) 6 = w64 N6) by (rewrite (EE 6%nat 6%bv eq_refl); exact H6).
  assert (E9b : base_val (Eimg (Ereg regs (@nil word))) (Some 9%nat) = F)
    by (cbn [base_val]; rewrite E9; apply unsigned_lit_small; lia).
  assert (E21b : base_val (Eimg (Ereg regs (@nil word))) (Some 21%nat) = HA)
    by (cbn [base_val]; rewrite E21; apply unsigned_lit_small; rewrite HRS, HAS in HH1; lia).
  clear EE.
  set (E := Eimg (Ereg regs (@nil word))) in *. clearbody E.
  unfold cfg_at. change (w64 (fr_B0 + pc)) with (Z_to_bv 64 (BASE + pc)).
  destruct Hcase as [(-> & ->) | (-> & ->)].
  all: paj_run_to_tok_xR RUNTOG HS HJ SHOK SMspan AF_LLVM_latch.
  1,3: apply awr_ok_x_cons;
    [ intros a Ha; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi] in Ha; rewrite E9b in Ha;
      left; split; [left; lia | lia]
    | apply awr_ok_x_cons_g;
      [ intros a Ha; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi] in Ha; rewrite E21b in Ha;
        apply HGs; rewrite HAS; lia
      | apply awr_ok_x_nil ] ].
  all: lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
    assert (HAE2 : env_agree 32 (Ereg regs (@nil word)) Ev)
      by (split; [intros q Hq; rewrite ?ew_ewset_other by lia; exact (proj1 HAE q Hq)
                 | rewrite ?ed_ewset; exact (proj2 HAE)]) end.
  all: pose proof (regs_kept_of_st_ok_pi (PI := PB_fr) _ _ _ regs (@nil word) sm_fl_kept HS HAE2
    ltac:(vm_compute; reflexivity)) as KR.
  all: cbn [ms_regs restrict] in KR.
  all: pose proof (st_ok_pi_region_nth _ _ _ 0 _ HS eq_refl) as RG0.
  all: pose proof (st_ok_pi_region_nth _ _ _ 1 _ HS eq_refl) as RG1.
  all: cbn [ms_mem restrict] in RG0, RG1.
  all: assert (V144 : val_mem segs (arm W (ms_mem ms)) (F + 144) 8 N6)
    by (apply (field_of_region E _ 9%nat F _ _ _ _ _ 144 8%N (SOff 6 0) N6 RG0);
        [ rewrite E9; apply unsigned_lit_small; lia
        | left; reflexivity
        | cbn [sv_denot]; rewrite E6, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
        | zside | zside ]).
  all: lazymatch type of RG1 with region_ok _ _ _ (YP09.mkRegion _ ?o _ _ _ _) =>
    assert (VHA : val_mem segs (arm W (ms_mem ms)) (HA + o) 4 1)
      by (apply (field_of_region E _ 21%nat HA _ _ _ _ _ o 4%N (SOff 23 0) 1 RG1);
          [ rewrite E21; apply unsigned_lit_small; rewrite HRS, HAS in HH1; lia
          | left; reflexivity
          | cbn [sv_denot]; rewrite E23, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
          | zside | zside ]) end.
  all: pmkst HS.
  all: apply (YA0nH.SRrG_ret segs R R_refl).
  all: split; [reflexivity|].
  all: exists (ms_regs ms), (ms_mem ms), (with_vm_backing (m_vm_lazy md) mat md).
  all: split; [reflexivity|].
  all: split; [exact HJ|].
  all: split; [intros a Ha Hn; split;
    [ apply (aview_kept_out _ _ _ _ _ HFr a Ha); intros (r & Hin & Hr); cbn [ss_mem sm_fl_regions In] in Hin;
      destruct Hin as [<- | [<- | []]]; cbn [YP09.r_base YP09.r_wlo YP09.r_whi] in Hr;
      [ rewrite E9b in Hr; apply Hn; unfold XS; apply inFP_cons; right; apply inFP_cons; left; lia
      | rewrite E21b in Hr; apply Hn; unfold XS; apply inFP_cons; right; apply inFP_cons; right;
        apply inFP_cons; left; lia ]
    | exact (sm_wkeep W mem (ms_mem ms) a HG0) ] |].
  all: split; [exact HG0|].
  all: split; [exact V144|].
  all: split; [exact VHA|].
  all: exact KR.
Qed.
(* R twin of sm_fl_walk_x *)
Lemma sm_fl_walk_xR : forall (ii fo : Z) (upd : hsrc -> hsrc) (mk : lfcx -> lmod -> nat -> lmod) cx Hp t W c,
  (ii = 3 /\ fo = 8) \/ (ii = 6 /\ fo = 12) ->
  (forall h, same_but_flags h (upd h)) ->
  (forall h, (fo = 8 /\ hs_closed (upd h) = 1 /\ hs_eintr (upd h) = hs_eintr h) \/
             (fo = 12 /\ hs_eintr (upd h) = 1 /\ hs_closed (upd h) = hs_closed h)) ->
  (forall m0 i0, mk cx m0 i0 = LM (sm_kn cx m0) (upd_hs i0 upd (lm_hs m0)) (lm_G m0) (lm_es m0)
      (lm_c m0) [] (lm_mx m0) (lm_cap m0) (lm_out m0) (lm_gn m0) (lm_nfd m0)) ->
  (forall m0 i0, RINV cx t m0 ->
     pick (lm_hs m0) (if lm_k m0 + 1 <? c_n cx then in_byte cx (lm_k m0 + 1) else 0) = Some i0 ->
     RINV cx (t + 1) (mk cx m0 i0)) ->
  (forall m0 i0 ly0 S0, LSx cx t m0 ly0 S0 ->
     pick (lm_hs m0) (if lm_k m0 + 1 <? c_n cx then in_byte cx (lm_k m0 + 1) else 0) = Some i0 ->
     LSx cx (t + 1) (mk cx m0 i0) ly0 S0) ->
  (forall h, asrc_blks (upd h) = asrc_blks h) ->
  lf_base_x B MT XM_LIB RLO RHI fr_live_pre LIBROOM NP G_fr ARx cx Hp -> INV_A_xR B NP G_fr fr_FP PST ARx LSx RINV R ii cx Hp t W c ->
  YA0nH.SRrG segs R W c (INV_K_xR B NP G_fr fr_FP PST ARx LSx RINV R cx Hp t).
Proof.
  intros ii fo upd mk cx Hp t W c Hcase Hsf Hfl Hmk Hri Hls Hblks HB HA.
  destruct HA as (regs & regsD & mem & md & Hc & Hkept & HopD & _ & HROM & HLF).
  destruct HLF as (own & ly3 & S3 & Hp3 & kk & m & fpos & HJ & Hown & Hframe & Hflag & Hmodel & Hinput & Hrom & Hsep &
    HLS & HNP & HRINV & HRD).
  subst own.
  pose proof HRD as (Hcommon & HD25 & Htb & Hkb & HO & Hoprest).
  cbv zeta in Hoprest. destruct Hoprest as (Hop11 & Hpick).
  assert (Hiirange : 0 <= ii <= 9) by (destruct Hcase as [[-> _]|[-> _]]; lia).
  assert (Hopeq : in_byte cx (lm_k m) mod 10 = ii).
  { pose proof (Z.mod_pos_bound (in_byte cx (lm_k m)) 10 ltac:(lia)) as Hmb.
    apply (f_equal bv_unsigned) in HopD. rewrite Hop11 in HopD.
    rewrite !unsigned_lit_small in HopD by lia. lia. }
  rewrite Hopeq in Hpick.
  assert (Hpk3 : picks ii = true) by (destruct Hcase as [[-> _]|[-> _]]; reflexivity).
  rewrite Hpk3 in Hpick. cbv zeta in Hpick. destruct Hpick as (HD20 & HD6 & Hpk).
  destruct Hpk as [(i & Hpicki & HD21) | (Hbad & _)];
    [| exfalso; destruct Hcase as [[Hii _]|[Hii _]]; rewrite Hii in Hbad; discriminate Hbad].
  destruct (sm_pick (lm_hs m) _ i Hpicki) as (Hilen & hsome & Hnthi).
  pose proof Hmodel as (Hlen4 & Hslots & _).
  rewrite Hlen4 in Hilen.
  pose proof (Hslots i Hilen) as Haslot. unfold aslot in Haslot. rewrite Hnthi in Haslot.
  assert (HARx : ARx ly3 S3 Hp3 W mem md) by (eapply ajournal_gx_AR_xR; exact HJ).
  assert (HAR : ARE ly3 S3 W mem md) by (exists Hp3; exact HARx).
  assert (Hfin : In (1, fpos) (frames S3)).
  { pose proof HJ as (_ & _ & (memS & HJ0 & _) & _). pose proof HJ0 as (_ & _ & _ & _ & _ & Hfrs & _).
    rewrite Hfrs. left. reflexivity. }
  destruct HB as (HAI & Hpre). pose proof Hpre as (Hafn & _ & _ & _ & _ & Hlen & _).
  pose proof Hafn as (_ & _ & _ & _ & _ & Hstk & _).
  pose proof Hstk as (Hsp16 & HstkK & Hceil & Hlo & Hhi & Hhi2 & _).
  set (sp0 := spZ (c_regs cx)) in *.
  set (HAc := rg_s fr_RG + ASRC * Z.of_nat i) in *.
  assert (HRS : rg_s fr_RG = 6131296) by reflexivity.
  assert (HAS : ASRC = 96) by reflexivity.
  assert (HSTK : LLVMF_STK = 32768) by reflexivity.
  pose proof sm_ceil_lo as Hac. assert (HES : ESTACK = 4096) by reflexivity.
  assert (Hsp0 : alloc_ceiling + 32768 <= sp0 <= 2 ^ 47) by lia.
  pose proof (Z.mod_pos_bound (sp0 - 320) 32 ltac:(lia)) as Hm32.
  assert (HFeq : lf_F cx = sp0 - 320 - (sp0 - 320) mod 32) by reflexivity.
  assert (HFbound : 2 ^ 46 <= lf_F cx <= 2 ^ 47) by lia.
  assert (HFmod : lf_F cx mod 32 = 0)
    by (rewrite HFeq; rewrite Zminus_mod, Zmod_mod, Z.sub_diag; reflexivity).
  assert (Hi4 : (i < 4)%nat) by lia.
  assert (HHbound : rg_s fr_RG <= HAc <= rg_s fr_RG + 3 * ASRC) by (unfold HAc; rewrite HAS; lia).
  assert (HHmod : HAc mod 32 = 0)
    by (unfold HAc; rewrite HRS, HAS; replace (6131296 + 96 * Z.of_nat i) with ((191603 + 3 * Z.of_nat i) * 32) by lia;
        apply Z_mod_mult).
  assert (Hfo : fo = 8 \/ fo = 12) by (destruct Hcase as [[_ ->]|[_ ->]]; [left|right]; reflexivity).
  (* the registers: regs agrees with regsD outside a0 / a1 *)
  assert (KD : forall r : bv 5, In r jt_kept -> getr regs r = getr regsD r) by exact Hkept.
  pose proof Hcommon as (C2 & C8 & C9 & C18 & C19 & C23 & C24 & C26 & C27 & C3 & C4).
  assert (Hr23 : getr regs 23 = w64 1) by (rewrite (KD 23%bv ltac:(sm_in)); exact C23).
  assert (Hr9 : getr regs 9 = w64 (lf_F cx)) by (rewrite (KD 9%bv ltac:(sm_in)); exact C9).
  assert (Hr27 : getr regs 27 = w64 SB) by (rewrite (KD 27%bv ltac:(sm_in)); exact C27).
  assert (Hr21 : getr regs 21 = w64 HAc) by (rewrite (KD 21%bv ltac:(sm_in)); exact HD21).
  set (k1 := if lm_k m + 1 <? c_n cx then lm_k m + 2 else lm_k m + 1) in *.
  assert (Hk1 : lm_k m + 1 <= k1 <= c_n cx)
    by (unfold k1; destruct (lm_k m + 1 <? c_n cx) eqn:Ek; [apply Z.ltb_lt in Ek | apply Z.ltb_ge in Ek]; lia).
  assert (Hn26 : c_n cx < 2 ^ 26)
    by (pose proof Hpre as (_ & _ & _ & _ & Hpn & _); destruct Hpn as [(H0 & _) | (H0 & _)]; lia).
  assert (Hr6 : getr regs 6 = w64 (c_n cx - k1)) by (rewrite (KD 6%bv ltac:(sm_in)); exact HD6).
  pose proof Hframe as (_ & Hawr & _).
  assert (HW1 : forall a, lf_F cx + 144 <= a < lf_F cx + 152 -> writable_at segs (arm W mem) a).
  { intros a Ha. replace a with (lf_F cx + (a - lf_F cx)) by lia. apply Hawr. lia. }
  pose proof Haslot as (_ & _ & _ & _ & Hs5 & _).
  assert (HW2 : forall a, HAc + fo <= a < HAc + fo + 4 -> writable_at segs (arm W mem) a).
  { intros a Ha. replace a with (HAc + (a - HAc)) by lia. apply Hs5. unfold ASRC; lia. }
  assert (HZslot : azs B HAc ASRC) by (apply (azs_sub B (rg_s fr_RG) (4 * ASRC)); [exact HZS | lia | unfold HAc; lia]).
  assert (Hpcs : (fo = 8 /\ fr_arm ii = AF_arm_close) \/ (fo = 12 /\ fr_arm ii = AF_arm_eintr))
    by (destruct Hcase as [(-> & ->) | (-> & ->)]; [left | right]; split; reflexivity).
  rewrite Hc.
  eapply YA0nH.SRrG_mono.
  { exact (sm_fl_run_xR W regs mem md LLVMF_STK sp0 (lf_FP fr_FP cx) (c_ly cx) (c_S cx) Hp (c_W cx) (c_mem cx) (c_md cx)
      [(1, fpos)] ly3 S3 Hp3 kk (lf_F cx) HAc fo (c_n cx - k1) (fr_arm ii) Hpcs HJ Hr23 Hr9 Hr21 Hr27 Hr6
      ltac:(lia) HFbound HFmod HHbound HHmod ltac:(lia) ltac:(lia) HW1 HW2 HZslot). }
  intros W' c' _ (-> & regs' & mem' & md' & -> & HJ' & KP & HGr & V144 & VHA & KR).
  set (XG := [(HAc + fo, HAc + fo + 4)]) in *.
  assert (HXG : XGOK XG).
  { intros a Ha. unfold XG in Ha. apply inFP_cons in Ha as [Ha | Ha]; [unfold HAc in Ha; sm_rgl | destruct (inFP_nil a Ha)]. }
  assert (HXOK : XOK (XS (lf_F cx) XG)) by (apply sm_xok; [lia | exact HXG]).
  assert (KK : forall r : bv 5, In r sm_fl_kept -> In r jt_kept -> getr regs' r = getr regsD r)
    by (intros r H1 H2; rewrite (KR r H1); exact (KD r H2)).
  exists regs', mem', md'. split; [reflexivity|].
  split; [exact (sm_jt_kept W mem mem' _ HXOK KP HROM)|].
  exists [(1, fpos)], ly3, S3, Hp3, kk, (mk cx m i), fpos.
  split; [exact HJ'|]. split; [reflexivity|].
  split; [exact (sm_aframe_kept_x cx ly3 S3 W mem md mem' fpos XG HAR Hfin Hsp0 HXG KP HGr Hframe)|].
  split; [exact (sm_flag_kept_x ly3 S3 W mem md mem' _ fpos _ HAR HXOK KP Hfin Hflag)|].
  split.
  { rewrite Hmk.
    pose proof (sm_amodel_fl_x ly3 S3 W mem md mem' (lf_F cx) m i hsome upd fo (sm_kn cx m) HAR ltac:(lia) KP HGr
      Hmodel Hi4 Hnthi (Hsf hsome) (Hfl hsome) VHA) as HM2.
    rewrite HO in HM2. exact HM2. }
  split; [exact (sm_ainput_kept_x cx ly3 S3 W mem md mem' _ HAR HXOK KP (eq_sym Hlen) Hinput)|].
  split; [exact (sm_rom_kept W mem mem' _ HXOK KP Hrom)|].
  split; [rewrite Hmk; apply (sm_sep_fl B fr_FP); [exact Hblks | exact Hsep]|].
  split; [exact (Hls m i ly3 S3 HLS Hpicki)|].
  split; [exact HNP|].
  split; [exact (Hri m i HRINV Hpicki)|].
  unfold lregs_K, lregs_common. rewrite Hmk. cbn [lm_k].
  assert (Hkn : sm_kn cx m = k1) by reflexivity. rewrite Hkn.
  split.
  { split; [rewrite (KK 2%bv ltac:(sm_in) ltac:(sm_in)); exact C2|].
    split; [rewrite (KK 8%bv ltac:(sm_in) ltac:(sm_in)); exact C8|].
    split; [rewrite (KK 9%bv ltac:(sm_in) ltac:(sm_in)); exact C9|].
    split; [rewrite (KK 18%bv ltac:(sm_in) ltac:(sm_in)); exact C18|].
    split; [rewrite (KK 19%bv ltac:(sm_in) ltac:(sm_in)); exact C19|].
    split; [rewrite (KK 23%bv ltac:(sm_in) ltac:(sm_in)); exact C23|].
    split; [rewrite (KK 24%bv ltac:(sm_in) ltac:(sm_in)); exact C24|].
    split; [rewrite (KK 26%bv ltac:(sm_in) ltac:(sm_in)); exact C26|].
    split; [rewrite (KK 27%bv ltac:(sm_in) ltac:(sm_in)); exact C27|].
    split; [rewrite (KK 3%bv ltac:(sm_in) ltac:(sm_in)); exact C3|].
    rewrite (KK 4%bv ltac:(sm_in) ltac:(sm_in)); exact C4. }
  split; [rewrite (KK 25%bv ltac:(sm_in) ltac:(sm_in)); exact HD25|].
  split; [exact Htb|].
  split; [rewrite (KK 20%bv ltac:(sm_in) ltac:(sm_in)); exact HD20|].
  split; [unfold sv8; exact V144|].
  lia.
Qed.
(* R twin of lf_arm_close_x: B cut_x Section wR's ARM_close_R *)
Theorem lf_arm_close_xR : forall cx Hp t W c,
  lf_base_x B MT XM_LIB RLO RHI fr_live_pre LIBROOM NP G_fr ARx cx Hp -> INV_A_xR B NP G_fr fr_FP PST ARx LSx RINV R 3 cx Hp t W c ->
  YA0nH.SRrG segs R W c (INV_K_xR B NP G_fr fr_FP PST ARx LSx RINV R cx Hp t).
Proof.
  pose proof R_refl as _. pose proof R_trans as _. pose proof WLE_R as _.
  intros cx Hp t W c HB HA.
  exact (sm_fl_walk_xR 3 8 upd_closed sm_close cx Hp t W c (or_introl (conj eq_refl eq_refl)) same_but_flags_closed
    (fun h => or_introl (conj eq_refl (conj eq_refl eq_refl))) (fun m0 i0 => eq_refl)
    (fun m0 i0 H Hpk => RI_close cx t m0 i0 H Hpk) (fun m0 i0 ly0 S0 H Hpk => LS_close cx t m0 i0 ly0 S0 H Hpk)
    upd_closed_blks HB HA).
Qed.
(* R twin of lf_arm_eintr_x: B cut_x Section wR's ARM_eintr_R *)
Theorem lf_arm_eintr_xR : forall cx Hp t W c,
  lf_base_x B MT XM_LIB RLO RHI fr_live_pre LIBROOM NP G_fr ARx cx Hp -> INV_A_xR B NP G_fr fr_FP PST ARx LSx RINV R 6 cx Hp t W c ->
  YA0nH.SRrG segs R W c (INV_K_xR B NP G_fr fr_FP PST ARx LSx RINV R cx Hp t).
Proof.
  pose proof R_refl as _. pose proof R_trans as _. pose proof WLE_R as _.
  intros cx Hp t W c HB HA.
  exact (sm_fl_walk_xR 6 12 upd_eintr sm_eintr cx Hp t W c (or_intror (conj eq_refl eq_refl)) same_but_flags_eintr
    (fun h => or_intror (conj eq_refl (conj eq_refl eq_refl))) (fun m0 i0 => eq_refl)
    (fun m0 i0 H Hpk => RI_eintr cx t m0 i0 H Hpk) (fun m0 i0 ly0 S0 H Hpk => LS_eintr cx t m0 i0 ly0 S0 H Hpk)
    upd_eintr_blks HB HA).
Qed.
(* R twin of sm_mx_post_x *)
Definition sm_mx_post_xR (W : world segs) (regs : bvmap 5 word) (mem : word -> option byte) (STK sp0 : Z)
    (FP : list (Z * Z)) (ly0 : alayout) (S0 : astate) (Hp0 : list Z) (W0 : world segs) (mem0 : word -> option byte) (md0 : Model)
    (own : list (Z * Z)) (ly : alayout) (S : astate) (Hp : list Z) (kk F P1 N1 u : Z) : world segs -> config -> Prop :=
  fun W' c' => W' = W /\ exists regs' mem' md',
    c' = cfg_at segs (fr_B0 + AF_LLVM_latch) regs' mem' md' /\
    ajournal_gx_xR segs B PST ARx R G_fr 0 [] STK sp0 FP ly0 S0 Hp0 W0 mem0 md0 own ly S Hp W mem' md' kk /\
    KEPT W mem mem' (XS F sm_mx_XG) /\
    mem_grows (mrestrict (w_H W) mem) (mrestrict (w_H W) mem') /\
    val_mem segs (arm W mem') (F + 144) 8 (if N1 =? 0 then 0 else N1 - 1) /\
    val_mem segs (arm W mem') (rg_send_max fr_RG) 8 u /\ val_mem segs (arm W mem') (rg_send_eintr fr_RG) 1 1 /\
    (forall r, In r sm_mx_kept -> getr regs' r = getr regs r) /\
    getr regs' 20 = w64 (if N1 =? 0 then P1 else P1 + 1).
(* R twin of sm_mx_run_x *)
Lemma sm_mx_run_xR : forall (W : world segs) regs mem md STK sp0 FP ly0 S0 Hp0 (W0 : world segs) mem0 md0 own ly S Hp kk
    F P1 N1 kb,
  ajournal_gx_xR segs B PST ARx R G_fr 0 [] STK sp0 FP ly0 S0 Hp0 W0 mem0 md0 own ly S Hp W mem md kk ->
  getr regs 23 = w64 1 -> getr regs 9 = w64 F -> getr regs 27 = w64 SB -> getr regs 20 = w64 P1 ->
  getr regs 6 = w64 N1 -> 0 <= N1 < 2 ^ 26 ->
  2 ^ 46 <= F <= 2 ^ 47 -> F mod 32 = 0 -> 4096 <= P1 <= 2 ^ 47 - 16 -> 0 <= kb < 256 ->
  sp0 - STK <= F + 144 -> F + 152 <= sp0 ->
  (N1 <> 0 -> P1 + 1 <= 0x10000 \/ 0x5fc000 <= P1) ->
  (N1 <> 0 -> P1 + 1 <= kLowShadowBeg \/ kHighMemBeg <= P1) ->
  (N1 <> 0 -> P1 + 1 <= F) ->
  (N1 <> 0 -> val_mem segs (arm W mem) P1 1 kb) ->
  (N1 <> 0 -> range_addressable (aview segs (w_H W) mem) SHADOW_OFF P1 1) ->
  sv8 W mem (F + 56) 0x5d956c -> sv8 W mem (F + 72) 0x5d9550 ->
  (forall a, F + 144 <= a < F + 152 -> writable_at segs (arm W mem) a) ->
  awr W mem (rg_send_max fr_RG) 8 -> awr W mem (rg_send_eintr fr_RG) 1 ->
  YA0nH.SRrG segs R W (cfg_at segs (fr_B0 + AF_arm_sendmax) regs mem md)
    (sm_mx_post_xR W regs mem STK sp0 FP ly0 S0 Hp0 W0 mem0 md0 own ly S Hp kk F P1 N1 (if N1 =? 0 then 0 else kb)).
Proof.
  intros W regs mem md STK sp0 FP ly0 S0 Hp0 W0 mem0 md0 own ly S Hp kk F P1 N1 kb HJ H23 H9 H27 H20 H6 HN1
    HF1 HF2 HP Hkb Hs1 Hs2 HPi HPa HPc MB RA M56 M72 HW1 HWmx HWei.
  pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
  assert (HRmx : rg_send_max fr_RG = 0x5d8dc0) by reflexivity.
  assert (HRei : rg_send_eintr fr_RG = 0x5d8e20) by reflexivity.
  assert (Hmo : negb (N1 =? 0) = true -> N1 <> 0) by (intros Hb; apply negb_true_iff, Z.eqb_neq in Hb; exact Hb).
  destruct (sm_mx_entry W regs mem (negb (N1 =? 0)) F P1 kb H23 H9 H27 H20 HF1 HF2 HP Hkb
    (fun Hb => HPi (Hmo Hb)) (fun Hb => HPa (Hmo Hb)) (fun Hb => HPc (Hmo Hb)) (fun Hb => MB (Hmo Hb))
    (fun Hb => RA (Hmo Hb)) M56 M72 HW1 HWmx HWei) as [HS SHOK].
  assert (HEI : img_env VAL A_LIM (Eimg (Ereg regs (sm_x1 kb)))) by apply Eimg_env.
  assert (HAE : env_agree 32 (Ereg regs (sm_x1 kb)) (Eimg (Ereg regs (sm_x1 kb))))
    by (split; [intros mm Hmm; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
  assert (EE : forall m (rr : bv 5), Z.of_nat m = bv_unsigned rr -> ew (Eimg (Ereg regs (sm_x1 kb))) m = getr regs rr)
    by (intros m rr Hm; pose proof (bv_unsigned_in_range 5 rr) as Hr5;
        change (bv_modulus 5) with 32 in Hr5; rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_nat; exact Hm).
  assert (E20 : ew (Eimg (Ereg regs (sm_x1 kb))) 20 = w64 P1) by (rewrite (EE 20%nat 20%bv eq_refl); exact H20).
  assert (E6 : ew (Eimg (Ereg regs (sm_x1 kb))) 6 = w64 N1) by (rewrite (EE 6%nat 6%bv eq_refl); exact H6).
  assert (E23 : ew (Eimg (Ereg regs (sm_x1 kb))) 23 = w64 1) by (rewrite (EE 23%nat 23%bv eq_refl); exact H23).
  assert (E32 : ew (Eimg (Ereg regs (sm_x1 kb))) 32 = Z_to_bv 64 kb)
    by (rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
  assert (U9 : bv_unsigned (ew (Eimg (Ereg regs (sm_x1 kb))) 9) = F)
    by (rewrite (EE 9%nat 9%bv eq_refl), H9; apply unsigned_lit_small; lia).
  assert (U343 : bv_unsigned (ew (Eimg (Ereg regs (sm_x1 kb))) 343) = 0x5d9550)
    by (rewrite Eimg_img by (unfold A_TEXT, A_LIM; lia); change 343%nat with (A_HI 63);
        rewrite (proj1 sm_mx_vals); first [reflexivity | apply unsigned_lit_small; lia]).
  assert (U346 : bv_unsigned (ew (Eimg (Ereg regs (sm_x1 kb))) 346) = 0x5d956c)
    by (rewrite Eimg_img by (unfold A_TEXT, A_LIM; lia); change 346%nat with (A_HI 66);
        rewrite (proj2 sm_mx_vals); first [reflexivity | apply unsigned_lit_small; lia]).
  clear EE.
  set (E := Eimg (Ereg regs (sm_x1 kb))) in *. clearbody E.
  assert (E9b : base_val E (Some 9%nat) = F) by exact U9.
  assert (E343b : base_val E (Some 343%nat) = 0x5d9550) by exact U343.
  assert (E346b : base_val E (Some 346%nat) = 0x5d956c) by exact U346.
  unfold cfg_at. change (w64 (fr_B0 + AF_arm_sendmax)) with (Z_to_bv 64 (BASE + AF_arm_sendmax)).
  revert HS SHOK. destruct (N1 =? 0) eqn:EN; intros HS SHOK; cbn [negb] in HS, SHOK.
  all: pose proof EN as EN'; first [apply Z.eqb_eq in EN' | apply Z.eqb_neq in EN'].
  all: psrr_branch_tok RUNG BRR HS SHOK SMspan.
  all: rewrite branch_eq_U, (U_atom E 6 N1 E6), U_lit in Hc by lia.
  all: try (exfalso; first [apply Z.eqb_eq in Hc | apply Z.eqb_neq in Hc]; lia).
  all: clear Hc.
  all: paj_run_to_tok_xR RUNTOG HS HJ SHOK SMspan AF_LLVM_latch.
  1,3: lazymatch goal with |- awr_ok_x ?Ev ?rs ?G ?XO ?OUT ?STK ?sp0 ?FP ?b0 ?bc ?ly ?own =>
      let rs' := eval vm_compute in rs in change (awr_ok_x Ev rs' G XO OUT STK sp0 FP b0 bc ly own) end;
    repeat first
     [ apply awr_ok_x_nil
     | apply awr_ok_x_cons; [intros a Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi] in Ha; rewrite ?E9b in Ha;
         first [exfalso; lia | left; split; [left; lia | lia]] |]
     | apply awr_ok_x_cons_g; [intros a Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi] in Ha;
         rewrite ?E343b, ?E346b in Ha; first [apply HGmx; lia | apply HGei; lia] |] ].
  all: lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
    assert (HAE2 : env_agree 32 (Ereg regs (sm_x1 kb)) Ev)
      by (split; [intros q Hq; rewrite ?ew_ewset_other by lia; exact (proj1 HAE q Hq)
                 | rewrite ?ed_ewset; exact (proj2 HAE)]);
    assert (EV9 : bv_unsigned (ew Ev 9) = F) by (rewrite ?ew_ewset_other by lia; exact U9);
    assert (EV6 : bv_unsigned (ew Ev 6) = N1)
      by (rewrite ?ew_ewset_other by lia; rewrite E6; apply unsigned_lit_small; lia);
    assert (EV23 : bv_unsigned (ew Ev 23) = 1)
      by (rewrite ?ew_ewset_other by lia; rewrite E23; apply unsigned_lit_small; lia);
    assert (EV32 : bv_unsigned (ew Ev 32) = kb)
      by (rewrite ?ew_ewset_other by lia; rewrite E32; apply unsigned_lit_small; lia);
    assert (EV343 : bv_unsigned (ew Ev 343) = 0x5d9550) by (rewrite ?ew_ewset_other by lia; exact U343);
    assert (EV346 : bv_unsigned (ew Ev 346) = 0x5d956c) by (rewrite ?ew_ewset_other by lia; exact U346)
  end.
  all: pose proof (regs_kept_of_st_ok_pi (PI := PB_fr) _ _ _ regs (sm_x1 kb) sm_mx_kept HS HAE2
    ltac:(vm_compute; reflexivity)) as KR.
  all: cbn [ms_regs restrict] in KR.
  all: prreg HS (20%bv : bv 5) Q20.
  all: rewrite ?ew_ewset_other in Q20 by lia.
  all: assert (Q20' : getr (ms_regs ms) 20 = w64 (if N1 =? 0 then P1 else P1 + 1))
    by (rewrite Q20, EN; cbv iota; rewrite ?E20; first [reflexivity | rewrite unsigned_lit_small by lia; reflexivity]).
  all: pose proof (st_ok_pi_region_nth _ _ _ 0 _ HS eq_refl) as RG0.
  all: pose proof (st_ok_pi_region_nth _ _ _ 2 _ HS eq_refl) as RG2.
  all: pose proof (st_ok_pi_region_nth _ _ _ 3 _ HS eq_refl) as RG3.
  all: cbn [ms_mem restrict] in RG0, RG2, RG3.
  all: assert (V144 : val_mem segs (arm W (ms_mem ms)) (F + 144) 8 (if N1 =? 0 then 0 else N1 - 1))
    by (rewrite EN; cbv iota; eapply (field_of_region _ _ 9%nat F _ _ _ _ _ 144 8%N _ _ RG0);
        [ exact EV9 | left; reflexivity
        | cbn [sv_denot]; rewrite ?EV6; first [reflexivity | f_equal; lia]
        | zside | zside ]).
  all: assert (Vmx : val_mem segs (arm W (ms_mem ms)) (rg_send_max fr_RG) 8 (if N1 =? 0 then 0 else kb))
    by (rewrite EN; cbv iota; replace (rg_send_max fr_RG) with (0x5d9550 + -1936) by reflexivity;
        eapply (field_of_region _ _ 343%nat 0x5d9550 _ _ _ _ _ (-1936) 8%N _ _ RG2);
        [ exact EV343 | left; reflexivity
        | cbn [sv_denot]; rewrite ?EV32, ?Z.add_0_r; reflexivity | zside | zside ]).
  all: assert (Vei : val_mem segs (arm W (ms_mem ms)) (rg_send_eintr fr_RG) 1 1)
    by (replace (rg_send_eintr fr_RG) with (0x5d956c + -1868) by reflexivity;
        eapply (field_of_region _ _ 346%nat 0x5d956c _ _ _ _ _ (-1868) 1%N _ _ RG3);
        [ exact EV346 | left; reflexivity | cbn [sv_denot]; rewrite ?EV23; reflexivity | zside | zside ]).
  all: assert (KP : KEPT W mem (ms_mem ms) (XS F sm_mx_XG))
    by (intros a Ha Hn; split;
        [ apply (aview_kept_out _ _ _ _ _ HFr a Ha); intros (r & Hin & Hr); vm_compute in Hin;
          repeat (destruct Hin as [<- | Hin];
            [ cbn [YP09.r_base YP09.r_wlo YP09.r_whi] in Hr; rewrite ?E9b, ?E343b, ?E346b in Hr;
              first [ lia | apply Hn; unfold XS, sm_mx_XG; apply inFP_cons; right; apply inFP_cons;
                first [ left; lia | right; apply inFP_cons; left; lia
                      | right; apply inFP_cons; right; apply inFP_cons; left; lia ] ]
            | ]);
          destruct Hin
        | exact (sm_wkeep W mem (ms_mem ms) a HG0) ]).
  all: pmkst HS.
  all: apply (YA0nH.SRrG_ret segs R R_refl).
  all: unfold sm_mx_post_xR; cbv beta.
  all: split; [reflexivity|].
  all: exists (ms_regs ms), (ms_mem ms), (with_vm_backing (m_vm_lazy md) mat md).
  all: split; [reflexivity|].
  all: split; [exact HJ|].
  all: split; [exact KP|].
  all: split; [exact HG0|].
  all: split; [exact V144|].
  all: split; [rewrite EN in Vmx; exact Vmx|].
  all: split; [exact Vei|].
  all: split; [exact KR|].
  all: exact Q20'.
Qed.
(* R twin of lf_arm_sendmax_x: B cut_x Section wR's ARM_sendmax_R *)
Theorem lf_arm_sendmax_xR : forall cx Hp t W c,
  lf_base_x B MT XM_LIB RLO RHI fr_live_pre LIBROOM NP G_fr ARx cx Hp -> INV_A_xR B NP G_fr fr_FP PST ARx LSx RINV R 8 cx Hp t W c ->
  YA0nH.SRrG segs R W c (INV_K_xR B NP G_fr fr_FP PST ARx LSx RINV R cx Hp t).
Proof.
  pose proof R_refl as _. pose proof R_trans as _. pose proof WLE_R as _.
  intros cx Hp t W c HB HA.
  destruct HA as (regs & regsD & mem & md & Hc & Hkept & HopD & _ & HROM & HLF).
  destruct HLF as (own & ly3 & S3 & Hp3 & kk & m & fpos & HJ & Hown & Hframe & Hflag & Hmodel & Hinput & Hrom & Hsep &
    HLS & HNP & HRINV & HRD).
  subst own.
  pose proof HRD as (Hcommon & HD25 & Htb & Hkb & HO & Hoprest).
  cbv zeta in Hoprest. destruct Hoprest as (Hop11 & Hpick).
  assert (Hopeq : in_byte cx (lm_k m) mod 10 = 8).
  { pose proof (Z.mod_pos_bound (in_byte cx (lm_k m)) 10 ltac:(lia)) as Hmb.
    apply (f_equal bv_unsigned) in HopD. rewrite Hop11 in HopD.
    rewrite !unsigned_lit_small in HopD by lia. lia. }
  rewrite Hopeq in Hpick.
  assert (Hpk8 : picks 8 = false) by reflexivity.
  rewrite Hpk8 in Hpick. destruct Hpick as (HD20 & HD6 & _).
  assert (HARx : ARx ly3 S3 Hp3 W mem md) by (eapply ajournal_gx_AR_xR; exact HJ).
  assert (HAR : ARE ly3 S3 W mem md) by (exists Hp3; exact HARx).
  assert (Hfin : In (1, fpos) (frames S3)).
  { pose proof HJ as (_ & _ & (memS & HJ0 & _) & _). pose proof HJ0 as (_ & _ & _ & _ & _ & Hfrs & _).
    rewrite Hfrs. left. reflexivity. }
  destruct HB as (HAI & Hpre). pose proof Hpre as (Hafn & _ & _ & _ & _ & Hlen & _).
  pose proof Hafn as (_ & _ & _ & _ & _ & Hstk & _).
  pose proof Hstk as (Hsp16 & HstkK & Hceil & Hlo & Hhi & Hhi2 & _).
  set (sp0 := spZ (c_regs cx)) in *.
  assert (HSTK : LLVMF_STK = 32768) by reflexivity.
  pose proof sm_ceil_lo as Hac. assert (HES : ESTACK = 4096) by reflexivity.
  assert (Hsp0 : alloc_ceiling + 32768 <= sp0 <= 2 ^ 47) by lia.
  pose proof (Z.mod_pos_bound (sp0 - 320) 32 ltac:(lia)) as Hm32.
  assert (HFeq : lf_F cx = sp0 - 320 - (sp0 - 320) mod 32) by reflexivity.
  assert (HFbound : 2 ^ 46 <= lf_F cx <= 2 ^ 47) by lia.
  assert (HFmod : lf_F cx mod 32 = 0)
    by (rewrite HFeq; rewrite Zminus_mod, Zmod_mod, Z.sub_diag; reflexivity).
  assert (KD : forall r : bv 5, In r jt_kept -> getr regs r = getr regsD r) by exact Hkept.
  pose proof Hcommon as (C2 & C8 & C9 & C18 & C19 & C23 & C24 & C26 & C27 & C3 & C4).
  assert (Hr23 : getr regs 23 = w64 1) by (rewrite (KD 23%bv ltac:(sm_in)); exact C23).
  assert (Hr9 : getr regs 9 = w64 (lf_F cx)) by (rewrite (KD 9%bv ltac:(sm_in)); exact C9).
  assert (Hr27 : getr regs 27 = w64 SB) by (rewrite (KD 27%bv ltac:(sm_in)); exact C27).
  assert (Hr20 : getr regs 20 = w64 (c_p cx + lm_k m + 1)) by (rewrite (KD 20%bv ltac:(sm_in)); exact HD20).
  assert (Hr6 : getr regs 6 = w64 (c_n cx - lm_k m - 1)) by (rewrite (KD 6%bv ltac:(sm_in)); exact HD6).
  (* the input block and the byte in.p[0] *)
  pose proof Hinput as [[[Hn0 _] | [Hnr Hblk]] Hgarr]; [lia|].
  destruct (alx_blocks _ _ _ LAWS _ _ _ _ _ _ _ _ HARx Hblk) as (Hp16 & Hp4096 & Hpceil & Hpia & _ & _).
  pose proof (sm_blk_off_x _ _ _ _ _ _ _ _ HARx Hblk ltac:(lia)) as Hpimg.
  unfold OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B.YCbq.off_img in Hpimg.
  pose proof (req_size_pos (c_n cx) ltac:(lia)) as [_ Hreq].
  pose proof (sm_in_byte_rng cx (lm_k m + 1)) as Hkb8.
  (* the frame and the stream's two cells *)
  pose proof Hframe as (_ & Hawr & _ & _ & _ & F56 & _ & F72 & _).
  assert (HW1 : forall a, lf_F cx + 144 <= a < lf_F cx + 152 -> writable_at segs (arm W mem) a).
  { intros a Ha. replace a with (lf_F cx + (a - lf_F cx)) by lia. apply Hawr. lia. }
  pose proof Hmodel as (_ & _ & _ & Hout & _).
  pose proof Hout as (_ & Omx & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Oei & _).
  rewrite Hc.
  eapply YA0nH.SRrG_mono.
  { exact (sm_mx_run_xR W regs mem md LLVMF_STK sp0 (lf_FP fr_FP cx) (c_ly cx) (c_S cx) Hp (c_W cx) (c_mem cx) (c_md cx)
      [(1, fpos)] ly3 S3 Hp3 kk (lf_F cx) (c_p cx + lm_k m + 1) (c_n cx - lm_k m - 1) (in_byte cx (lm_k m + 1))
      HJ Hr23 Hr9 Hr27 Hr20 Hr6 ltac:(lia) HFbound HFmod ltac:(lia) Hkb8 ltac:(lia) ltac:(lia)
      ltac:(intros HN; lia)
      ltac:(intros HN; unfold in_app in Hpia; unfold kLowShadowBeg, kHighMemBeg in *; lia)
      ltac:(intros HN; lia)
      ltac:(intros HN; rewrite <- Z.add_assoc; exact (proj1 (sm_in_byte cx (arm W mem) (lm_k m + 1) Hgarr ltac:(lia))))
      ltac:(intros HN; apply (range_addressable_of_block_hp0_x segs B ARx LAWS HP0 ly3 S3 Hp3 W mem md (c_p cx) (c_n cx));
            [exact HARx | exact Hblk | lia | lia])
      F56 F72 HW1 Omx Oei). }
  intros W' c' _ (-> & regs' & mem' & md' & -> & HJ' & KP & HGr & V144 & Vmx & Vei & KR & Q20).
  pose proof sm_mx_xgok as HXG.
  assert (HXOK : XOK (XS (lf_F cx) sm_mx_XG)) by (apply sm_xok; [lia | exact HXG]).
  assert (KK : forall r : bv 5, In r sm_mx_kept -> In r jt_kept -> getr regs' r = getr regsD r)
    by (intros r H1 H2; rewrite (KR r H1); exact (KD r H2)).
  set (u := if c_n cx - lm_k m - 1 =? 0 then 0 else in_byte cx (lm_k m + 1)) in *.
  assert (Hu : 0 <= u <= 255) by (unfold u; destruct (_ =? 0); lia).
  exists regs', mem', md'. split; [reflexivity|].
  split; [exact (sm_jt_kept W mem mem' _ HXOK KP HROM)|].
  exists [(1, fpos)], ly3, S3, Hp3, kk, (sm_sendmax cx m u), fpos.
  split; [exact HJ'|]. split; [reflexivity|].
  split; [exact (sm_aframe_kept_x cx ly3 S3 W mem md mem' fpos sm_mx_XG HAR Hfin Hsp0 HXG KP HGr Hframe)|].
  split; [exact (sm_flag_kept_x ly3 S3 W mem md mem' _ fpos _ HAR HXOK KP Hfin Hflag)|].
  split; [exact (sm_amodel_mx_x ly3 S3 W mem md mem' (lf_F cx) cx m u HAR ltac:(lia) KP HGr Hmodel HO Hu Vmx Vei)|].
  split; [exact (sm_ainput_kept_x cx ly3 S3 W mem md mem' _ HAR HXOK KP (eq_sym Hlen) Hinput)|].
  split; [exact (sm_rom_kept W mem mem' _ HXOK KP Hrom)|].
  split; [exact Hsep|].
  assert (Hud : u = (if lm_k m + 1 <? c_n cx then in_byte cx (lm_k m + 1) else 0)).
  { unfold u. destruct (lm_k m + 1 <? c_n cx) eqn:Ek; [apply Z.ltb_lt in Ek | apply Z.ltb_ge in Ek].
    - replace (c_n cx - lm_k m - 1 =? 0) with false by (symmetry; apply Z.eqb_neq; lia). reflexivity.
    - replace (c_n cx - lm_k m - 1 =? 0) with true by (symmetry; apply Z.eqb_eq; lia). reflexivity. }
  split; [rewrite Hud; exact (LS_sendmax cx t m ly3 S3 HLS)|].
  split; [exact HNP|].
  split; [rewrite Hud; exact (RI_sendmax cx t m HRINV)|].
  unfold lregs_K, lregs_common, sm_sendmax. cbn [lm_k]. unfold sm_kn.
  split.
  { split; [rewrite (KK 2%bv ltac:(sm_in) ltac:(sm_in)); exact C2|].
    split; [rewrite (KK 8%bv ltac:(sm_in) ltac:(sm_in)); exact C8|].
    split; [rewrite (KK 9%bv ltac:(sm_in) ltac:(sm_in)); exact C9|].
    split; [rewrite (KK 18%bv ltac:(sm_in) ltac:(sm_in)); exact C18|].
    split; [rewrite (KK 19%bv ltac:(sm_in) ltac:(sm_in)); exact C19|].
    split; [rewrite (KK 23%bv ltac:(sm_in) ltac:(sm_in)); exact C23|].
    split; [rewrite (KK 24%bv ltac:(sm_in) ltac:(sm_in)); exact C24|].
    split; [rewrite (KK 26%bv ltac:(sm_in) ltac:(sm_in)); exact C26|].
    split; [rewrite (KK 27%bv ltac:(sm_in) ltac:(sm_in)); exact C27|].
    split; [rewrite (KK 3%bv ltac:(sm_in) ltac:(sm_in)); exact C3|].
    rewrite (KK 4%bv ltac:(sm_in) ltac:(sm_in)); exact C4. }
  split; [rewrite (KK 25%bv ltac:(sm_in) ltac:(sm_in)); exact HD25|].
  split; [exact Htb|].
  unfold sv8.
  destruct (lm_k m + 1 <? c_n cx) eqn:Ek; [apply Z.ltb_lt in Ek | apply Z.ltb_ge in Ek].
  - assert (EN : (c_n cx - lm_k m - 1 =? 0) = false) by (apply Z.eqb_neq; lia).
    rewrite EN in Q20, V144. cbv iota in Q20, V144.
    split; [rewrite Q20; f_equal; lia|].
    split; [replace (c_n cx - (lm_k m + 2)) with (c_n cx - lm_k m - 1 - 1) by lia; exact V144|]. lia.
  - assert (EN : (c_n cx - lm_k m - 1 =? 0) = true) by (apply Z.eqb_eq; lia).
    rewrite EN in Q20, V144. cbv iota in Q20, V144.
    split; [rewrite Q20; f_equal; lia|].
    split; [replace (c_n cx - (lm_k m + 1)) with 0 by lia; exact V144|]. lia.
Qed.
(* R twin of sm_df_post_x *)
Definition sm_df_post_xR (W : world segs) (regs : bvmap 5 word) (mem : word -> option byte) (STK sp0 : Z)
    (FP : list (Z * Z)) (ly0 : alayout) (S0 : astate) (Hp0 : list Z) (W0 : world segs) (mem0 : word -> option byte) (md0 : Model)
    (own : list (Z * Z)) (ly : alayout) (S : astate) (Hp : list Z) (kk F P1 N1 kb dd cl : Z) : world segs -> config -> Prop :=
  fun W' c' => W' = W /\ exists (g : bool) regs' mem' md',
    g = negb (N1 =? 0) && Z.odd kb /\
    c' = cfg_at segs (fr_B0 + AF_LLVM_latch) regs' mem' md' /\
    ajournal_gx_xR segs B PST ARx R G_fr 0 [] STK sp0 FP ly0 S0 Hp0 W0 mem0 md0 own ly S Hp W mem' md' kk /\
    KEPT W mem mem' (XS F (sm_df_XG g)) /\
    mem_grows (mrestrict (w_H W) mem) (mrestrict (w_H W) mem') /\
    val_mem segs (arm W mem') (F + 144) 8 (if N1 =? 0 then 0 else N1 - 1) /\
    val_mem segs (arm W mem') (rg_send_dead fr_RG) 1 (if g then dd else 1) /\
    val_mem segs (arm W mem') (rg_gone fr_RG) 1 1 /\
    val_mem segs (arm W mem') (rg_client fr_RG) 4 (if g then 2 ^ 32 - 1 else cl) /\
    (g = true -> val_mem segs (arm W mem') (rg_lock fr_RG + 4) 4 0) /\
    (forall r, In r sm_df_kept -> getr regs' r = getr regs r) /\
    getr regs' 20 = w64 (if N1 =? 0 then P1 else P1 + 1).
(* R twin of sm_df_run_x *)
Lemma sm_df_run_xR : forall (W : world segs) regs mem md STK sp0 FP ly0 S0 Hp0 (W0 : world segs) mem0 md0 own ly S Hp kk
    F P1 N1 kb dd cl,
  ajournal_gx_xR segs B PST ARx R G_fr 0 [] STK sp0 FP ly0 S0 Hp0 W0 mem0 md0 own ly S Hp W mem md kk ->
  getr regs 2 = w64 F -> getr regs 3 = w64 (as_gp B) -> getr regs 4 = w64 (as_tp B) ->
  getr regs 23 = w64 1 -> getr regs 9 = w64 F -> getr regs 27 = w64 SB ->
  getr regs 20 = w64 P1 -> getr regs 6 = w64 N1 -> 0 <= N1 < 2 ^ 26 ->
  2 ^ 46 <= F <= 2 ^ 47 -> F mod 32 = 0 -> 4096 <= P1 <= 2 ^ 47 - 16 -> 0 <= kb < 256 ->
  F + 152 <= sp0 -> (F - sp0) mod 16 = 0 -> ESTACK + (sp0 - F) <= STK ->
  (N1 <> 0 -> P1 + 1 <= 0x10000 \/ 0x5fc000 <= P1) ->
  (N1 <> 0 -> P1 + 1 <= kLowShadowBeg \/ kHighMemBeg <= P1) ->
  (N1 <> 0 -> P1 + 1 <= F) ->
  (N1 <> 0 -> val_mem segs (arm W mem) P1 1 kb) ->
  (N1 <> 0 -> range_addressable (aview segs (w_H W) mem) SHADOW_OFF P1 1) ->
  sv8 W mem (F + 32) 0xa2540 -> sv8 W mem (F + 40) 0x5d9564 -> sv8 W mem (F + 64) 0x5d955c ->
  (forall a, F + 144 <= a < F + 152 -> writable_at segs (arm W mem) a) ->
  val_mem segs (arm W mem) (rg_send_dead fr_RG) 1 dd -> 0 <= dd < 256 -> awr W mem (rg_send_dead fr_RG) 1 ->
  awr W mem (rg_gone fr_RG) 1 ->
  val_mem segs (arm W mem) (rg_client fr_RG) 4 cl -> 0 <= cl < 2 ^ 32 -> awr W mem (rg_client fr_RG) 4 ->
  alock_at fr_RG W mem false ->
  YA0nH.SRrG segs R W (cfg_at segs (fr_B0 + AF_arm_default) regs mem md)
    (sm_df_post_xR W regs mem STK sp0 FP ly0 S0 Hp0 W0 mem0 md0 own ly S Hp kk F P1 N1 kb dd cl).
Proof.
  intros W regs mem md STK sp0 FP ly0 S0 Hp0 W0 mem0 md0 own ly S Hp kk F P1 N1 kb dd cl HJ H2 H3 H4 H23 H9 H27
    H20 H6 HN1 HF1 HF2 HP Hkb Hs1 Hs16 Hs2 HPi HPa HPc MB RA M32 M40 M64 HW1 Vdd Hdd HWdd HWgn Vcl Hcl HWcl HLK.
  pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
  pose proof sm_ceil_lo as Hac. assert (HES : ESTACK = 4096) by reflexivity.
  pose proof sm_rgv as (_ & _ & _ & _ & _ & _ & _ & _ & _ & HRdd & HRgn & HRcl & _ & HRlk & _).
  assert (Hmo : negb (N1 =? 0) = true -> N1 <> 0) by (intros Hb; apply negb_true_iff, Z.eqb_neq in Hb; exact Hb).
  destruct (sm_df_entry W regs mem (negb (N1 =? 0)) F P1 kb dd cl H23 H9 H27 H20 HF1 HF2 HP Hkb Hdd Hcl
    (fun Hb => HPi (Hmo Hb)) (fun Hb => HPa (Hmo Hb)) (fun Hb => HPc (Hmo Hb)) (fun Hb => MB (Hmo Hb))
    (fun Hb => RA (Hmo Hb)) M32 M40 M64 HW1 Vdd HWdd HWgn Vcl HWcl) as [HS SHOK].
  set (E := Eimg (Ereg regs (sm_x1 kb))) in *.
  assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
  assert (HAE : env_agree 32 (Ereg regs (sm_x1 kb)) E)
    by (subst E; split; [intros mm Hmm; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
  assert (EE : forall m (rr : bv 5), Z.of_nat m = bv_unsigned rr -> ew E m = getr regs rr)
    by (intros m rr Hm; subst E; pose proof (bv_unsigned_in_range 5 rr) as Hr5;
        change (bv_modulus 5) with 32 in Hr5; rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_nat; exact Hm).
  assert (E2 : ew E 2 = w64 F) by (rewrite (EE 2%nat 2%bv eq_refl); exact H2).
  assert (E3 : ew E 3 = w64 (as_gp B)) by (rewrite (EE 3%nat 3%bv eq_refl); exact H3).
  assert (E4 : ew E 4 = w64 (as_tp B)) by (rewrite (EE 4%nat 4%bv eq_refl); exact H4).
  assert (E6 : ew E 6 = w64 N1) by (rewrite (EE 6%nat 6%bv eq_refl); exact H6).
  assert (E20 : ew E 20 = w64 P1) by (rewrite (EE 20%nat 20%bv eq_refl); exact H20).
  assert (E23 : ew E 23 = w64 1) by (rewrite (EE 23%nat 23%bv eq_refl); exact H23).
  assert (E32 : ew E 32 = Z_to_bv 64 kb)
    by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
  assert (U9 : bv_unsigned (ew E 9) = F) by (rewrite (EE 9%nat 9%bv eq_refl), H9; apply unsigned_lit_small; lia).
  assert (U20 : bv_unsigned (ew E 20) = P1) by (rewrite E20; apply unsigned_lit_small; lia).
  assert (U23 : bv_unsigned (ew E 23) = 1) by (rewrite E23; apply unsigned_lit_small; lia).
  pose proof sm_df_vals as (V60 & V64 & V65).
  assert (U340 : bv_unsigned (ew E 340) = 0xa2540)
    by (subst E; rewrite Eimg_img by (unfold A_TEXT, A_LIM; lia); change 340%nat with (A_HI 60);
        rewrite V60; first [reflexivity | apply unsigned_lit_small; lia]).
  assert (U344 : bv_unsigned (ew E 344) = 0x5d955c)
    by (subst E; rewrite Eimg_img by (unfold A_TEXT, A_LIM; lia); change 344%nat with (A_HI 64);
        rewrite V64; first [reflexivity | apply unsigned_lit_small; lia]).
  assert (U345 : bv_unsigned (ew E 345) = 0x5d9564)
    by (subst E; rewrite Eimg_img by (unfold A_TEXT, A_LIM; lia); change 345%nat with (A_HI 65);
        rewrite V65; first [reflexivity | apply unsigned_lit_small; lia]).
  assert (E244 : ew E 244 = Z_to_bv 64 (rg_lock fr_RG))
    by (subst E; rewrite Eimg_img by (unfold A_TEXT, A_LIM; lia); change 244%nat with (A_OBJ 3);
        rewrite sm_hv3; reflexivity).
  clear EE.
  clearbody E.
  unfold cfg_at. change (w64 (fr_B0 + AF_arm_default)) with (Z_to_bv 64 (BASE + AF_arm_default)).
  revert HS SHOK. destruct (N1 =? 0) eqn:EN; intros HS SHOK; cbn [negb] in HS, SHOK.
  all: pose proof EN as EN'; first [apply Z.eqb_eq in EN' | apply Z.eqb_neq in EN'].
  all: psrr_branch_tok RUNG BRR HS SHOK SMspan.
  all: rewrite branch_eq_U, (U_atom E 6 N1 E6), U_lit in Hc by lia.
  all: try (exfalso; first [apply Z.eqb_eq in Hc | apply Z.eqb_neq in Hc]; lia).
  all: clear Hc.
  - (* no input left: in.n := 0, g_send_dead := 1, g_gone := 1 *)
    paj_run_to_tok_xR RUNTOG HS HJ SHOK SMspan AF_LLVM_latch.
    + sm_df_awr.
    + let Ev := sm_env HS in
      assert (HAE2 : env_agree 32 (Ereg regs (sm_x1 kb)) Ev)
        by (split; [intros q Hq; rewrite ?ew_ewset_other by lia; exact (proj1 HAE q Hq)
                   | rewrite ?ed_ewset; exact (proj2 HAE)]);
      assert (EV9 : bv_unsigned (ew Ev 9) = F) by sm_base;
      assert (EV344 : bv_unsigned (ew Ev 344) = 0x5d955c) by sm_base;
      assert (EV345 : bv_unsigned (ew Ev 345) = 0x5d9564) by sm_base;
      assert (EV340 : bv_unsigned (ew Ev 340) = 0xa2540) by sm_base;
      assert (EV23 : bv_unsigned (ew Ev 23) = 1) by sm_base.
      pose proof (regs_kept_of_st_ok_pi (PI := PB_fr) _ _ _ regs (sm_x1 kb) sm_df_kept HS HAE2
        ltac:(vm_compute; reflexivity)) as KR.
      cbn [ms_regs restrict] in KR.
      prreg HS (20%bv : bv 5) Q20.
      rewrite ?ew_ewset_other in Q20 by lia. rewrite E20 in Q20.
      pose proof (st_ok_pi_region_nth _ _ _ 0 _ HS eq_refl) as RG0.
      pose proof (st_ok_pi_region_nth _ _ _ 2 _ HS eq_refl) as RG2.
      pose proof (st_ok_pi_region_nth _ _ _ 3 _ HS eq_refl) as RG3.
      pose proof (st_ok_pi_region_nth _ _ _ 4 _ HS eq_refl) as RG4.
      cbn [ms_mem restrict] in RG0, RG2, RG3, RG4.
      assert (V144 : val_mem segs (arm W (ms_mem ms)) (F + 144) 8 0)
        by (eapply (field_of_region _ _ 9%nat F _ _ _ _ _ 144 8%N _ _ RG0);
            [exact EV9 | left; reflexivity | reflexivity | zside | zside]).
      assert (Vdd' : val_mem segs (arm W (ms_mem ms)) (rg_send_dead fr_RG) 1 1)
        by (replace (rg_send_dead fr_RG) with (0x5d9564 + -1892) by lia;
            eapply (field_of_region _ _ 345%nat 0x5d9564 _ _ _ _ _ (-1892) 1%N _ _ RG2);
            [exact EV345 | left; reflexivity | cbn [sv_denot]; rewrite EV23; reflexivity | zside | zside]).
      assert (Vgn' : val_mem segs (arm W (ms_mem ms)) (rg_gone fr_RG) 1 1)
        by (replace (rg_gone fr_RG) with (0x5d955c + -1916) by lia;
            eapply (field_of_region _ _ 344%nat 0x5d955c _ _ _ _ _ (-1916) 1%N _ _ RG3);
            [exact EV344 | left; reflexivity | cbn [sv_denot]; rewrite EV23; reflexivity | zside | zside]).
      assert (Vcl' : val_mem segs (arm W (ms_mem ms)) (rg_client fr_RG) 4 cl)
        by (replace (rg_client fr_RG) with (0xa2540 + 32) by lia;
            eapply (field_of_region _ _ 340%nat 0xa2540 _ _ _ _ _ 32 4%N _ _ RG4);
            [exact EV340 | left; reflexivity | reflexivity | zside | zside]).
      pmkst HS. apply (YA0nH.SRrG_ret segs R R_refl). unfold sm_df_post_xR; cbv beta. split; [reflexivity|].
      exists false. do 3 eexists. split; [rewrite EN; reflexivity|].
      split; [reflexivity|]. split; [exact HJ|].
      split; [apply (sm_kept_run W _ _ mem (ms_mem ms) _ HFr HG0); sm_inX|].
      split; [exact HG0|].
      split; [rewrite EN; exact V144|].
      split; [exact Vdd'|]. split; [exact Vgn'|]. split; [exact Vcl'|].
      split; [intros Hf; discriminate Hf|].
      split; [exact KR|]. rewrite EN; exact Q20.
  - (* input left: the byte, in.n := t1 - 1, then its low bit *)
    paj_run_tok_xR RUNG HS HJ SHOK SMspan.
    + sm_df_awr.
    + rename HF into HFa, HFr into HFra, HG0 into HGa.
      psrr_branch_tok RUNG BRR HS SHOK SMspan.
      all: let Ev := sm_env HS in
           assert (EV32 : ew Ev 32 = Z_to_bv 64 kb) by (rewrite ?ew_ewset_other by lia; exact E32).
      all: rewrite branch_eq_U, U_and_lit, (U_atom _ 32 kb EV32), U_lit in Hc by lia.
      all: pose proof (sm_odd_land kb) as Hodd; rewrite Hc in Hodd; cbn [negb] in Hodd; clear Hc.
      * (* even: g_send_dead := 1, g_gone := 1 *)
        paj_run_to_tok_xR RUNTOG HS HJ SHOK SMspan AF_LLVM_latch.
        -- sm_df_awr.
        -- let Ev := sm_env HS in
           assert (HAE2 : env_agree 32 (Ereg regs (sm_x1 kb)) Ev)
             by (split; [intros q Hq; rewrite ?ew_ewset_other by lia; exact (proj1 HAE q Hq)
                        | rewrite ?ed_ewset; exact (proj2 HAE)]);
           assert (EV9 : bv_unsigned (ew Ev 9) = F) by sm_base;
           assert (EV344 : bv_unsigned (ew Ev 344) = 0x5d955c) by sm_base;
           assert (EV345 : bv_unsigned (ew Ev 345) = 0x5d9564) by sm_base;
           assert (EV340 : bv_unsigned (ew Ev 340) = 0xa2540) by sm_base;
           assert (EV23 : bv_unsigned (ew Ev 23) = 1) by sm_base;
           assert (EV6 : bv_unsigned (ew Ev 6) = N1)
             by (rewrite !ew_ewset_other by lia; rewrite E6; apply unsigned_lit_small; lia).
           pose proof (regs_kept_of_st_ok_pi (PI := PB_fr) _ _ _ regs (sm_x1 kb) sm_df_kept HS HAE2
             ltac:(vm_compute; reflexivity)) as KR.
           cbn [ms_regs restrict] in KR.
           prreg HS (20%bv : bv 5) Q20.
           rewrite ?ew_ewset_other in Q20 by lia. rewrite U20 in Q20.
           pose proof (st_ok_pi_region_nth _ _ _ 0 _ HS eq_refl) as RG0.
           pose proof (st_ok_pi_region_nth _ _ _ 2 _ HS eq_refl) as RG2.
           pose proof (st_ok_pi_region_nth _ _ _ 3 _ HS eq_refl) as RG3.
           pose proof (st_ok_pi_region_nth _ _ _ 4 _ HS eq_refl) as RG4.
           cbn [ms_mem restrict] in RG0, RG2, RG3, RG4.
           assert (V144 : val_mem segs (arm W (ms_mem ms0)) (F + 144) 8 (N1 - 1))
             by (eapply (field_of_region _ _ 9%nat F _ _ _ _ _ 144 8%N _ _ RG0);
                 [exact EV9 | left; reflexivity | cbn [sv_denot]; rewrite EV6; f_equal; lia | zside | zside]).
           assert (Vdd' : val_mem segs (arm W (ms_mem ms0)) (rg_send_dead fr_RG) 1 1)
             by (replace (rg_send_dead fr_RG) with (0x5d9564 + -1892) by lia;
                 eapply (field_of_region _ _ 345%nat 0x5d9564 _ _ _ _ _ (-1892) 1%N _ _ RG2);
                 [exact EV345 | left; reflexivity | cbn [sv_denot]; rewrite EV23; reflexivity | zside | zside]).
           assert (Vgn' : val_mem segs (arm W (ms_mem ms0)) (rg_gone fr_RG) 1 1)
             by (replace (rg_gone fr_RG) with (0x5d955c + -1916) by lia;
                 eapply (field_of_region _ _ 344%nat 0x5d955c _ _ _ _ _ (-1916) 1%N _ _ RG3);
                 [exact EV344 | left; reflexivity | cbn [sv_denot]; rewrite EV23; reflexivity | zside | zside]).
           assert (Vcl' : val_mem segs (arm W (ms_mem ms0)) (rg_client fr_RG) 4 cl)
             by (replace (rg_client fr_RG) with (0xa2540 + 32) by lia;
                 eapply (field_of_region _ _ 340%nat 0xa2540 _ _ _ _ _ 32 4%N _ _ RG4);
                 [exact EV340 | left; reflexivity | reflexivity | zside | zside]).
           pmkst HS. apply (YA0nH.SRrG_ret segs R R_refl). unfold sm_df_post_xR; cbv beta. split; [reflexivity|].
           exists false. do 3 eexists. split; [rewrite EN, Hodd; reflexivity|].
           split; [reflexivity|]. split; [exact HJ|].
           split; [apply (sm_kept_trans W mem (ms_mem ms) (ms_mem ms0));
                   [apply (sm_kept_run W _ _ mem (ms_mem ms) _ HFra HGa); sm_inX
                   | apply (sm_kept_run W _ _ (ms_mem ms) (ms_mem ms0) _ HFr HG0); sm_inX]|].
           split; [exact (mem_grows_trans _ _ _ HGa HG0)|].
           split; [rewrite EN; exact V144|].
           split; [exact Vdd'|]. split; [exact Vgn'|]. split; [exact Vcl'|].
           split; [intros Hf; discriminate Hf|].
           split; [exact KR|]. rewrite EN. rewrite Q20. reflexivity.
      * (* odd: to pthread_mutex_lock *)
        paj_run_tok_xR RUNG HS HJ SHOK SMspan.
        -- sm_df_awr.
        -- rename HF into HFb, HFr into HFrb, HG0 into HGb.
           (* pthread_mutex_lock (&g_lock): a0 = s4 = A_OBJ 3 *)
           pmkst HS.
           prreg HS (1%bv : bv 5) Q1. prreg HS (2%bv : bv 5) Q2. prreg HS (3%bv : bv 5) Q3.
           prreg HS (4%bv : bv 5) Q4. prreg HS (10%bv : bv 5) Q10.
           rewrite ?ew_ewset_other in Q2, Q3, Q4, Q10 by lia.
           rewrite E2 in Q2. rewrite E3 in Q3. rewrite E4 in Q4. rewrite E244 in Q10.
           assert (Usp : spZ (ms_regs ms0) = F) by (unfold spZ; rewrite Q2; apply unsigned_lit_small; lia).
           pose proof HLK as (LK0 & LK4 & LK8 & LKW). unfold arm in LK0, LK4, LK8, LKW.
           assert (KL1 : forall a, rg_lock fr_RG <= a < rg_lock fr_RG + 12 ->
               aview segs (w_H W) (ms_mem ms0) a = aview segs (w_H W) mem a).
           { intros a Ha. transitivity (aview segs (w_H W) (ms_mem ms) a).
             - apply (aview_kept_out _ _ _ _ _ HFrb a ltac:(lia)). sm_notw.
             - apply (aview_kept_out _ _ _ _ _ HFra a ltac:(lia)). sm_notw. }
           pose proof (ajournal_gx_AR_xR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as HARc.
           assert (HNOWN : forall a, rg_lock fr_RG <= a < rg_lock fr_RG + 12 -> ~ aowned B ly S a).
           { intros a Ha Ho. destruct (HG a (HGlk a Ha)) as (Hi & Hno & _). apply Hno.
             exact (proj1 (alx_owned_image _ _ _ LAWS ly S Hp W (ms_mem ms0) _ a HARc Hi) Ho). }
           assert (LKV : forall a, rg_lock fr_RG <= a < rg_lock fr_RG + 12 ->
               aview segs (w_H W) (ms_mem ms0) a <> None).
           { intros a Ha. rewrite (KL1 a Ha).
             destruct (Z_lt_le_dec a (rg_lock fr_RG + 4)) as [h1 | h1];
               [exact (sm_av_ne W mem _ 4 0 a LK0 ltac:(cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia)) |].
             destruct (Z_lt_le_dec a (rg_lock fr_RG + 8)) as [h2 | h2];
               [ exact (sm_av_ne W mem _ 4 0 a LK4 ltac:(cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia))
               | exact (sm_av_ne W mem _ 4 0 a LK8 ltac:(cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia)) ]. }
           assert (AVL : aview segs (w_H W) (ms_mem ms0) (rg_lock fr_RG) = Some 0)
             by (rewrite (KL1 (rg_lock fr_RG) ltac:(lia)); exact (sm_av0 W mem _ LK0)).
           assert (LK4m : val_mem segs (mrestrict (w_H W) (ms_mem ms0)) (rg_lock fr_RG + 4) 4 0).
           { apply (val_mem_moved segs (w_H W) (w_H W) mem (ms_mem ms0) (rg_lock fr_RG + 4) (rg_lock fr_RG + 4) 4 0);
               [intros j Hj; apply KL1; cbn in Hj; lia | exact LK4]. }
           eapply (YA0nH.SRrG_bind segs R R_trans).
           { eapply (aj_gx_entry_at_xR B PST ARx LAWS R_trans WLE_R G_fr 0 [] ESTACK (SIGMA WS_pthread_mutex_lock)
               (fun a => rg_lock fr_RG + 4 <= a < rg_lock fr_RG + 8)
               (fun (_ : bvmap 5 word) (mem' : word -> option byte) =>
                  val_mem segs (mrestrict (w_H W) mem') (rg_lock fr_RG + 4) 4 16)
               W (ms_regs ms0) (ms_mem ms0) STK sp0 FP ly0 S0 Hp0 W0 mem0 md0 own ly S Hp _ kk (F - sp0) _ HG eq_refl HJ
               ltac:(rewrite Usp; lia) Hs16 ltac:(lia) ltac:(lia) ltac:(lia) Q3 Q4 Q1
               (ret_ok_codeptr_v 10028 ltac:(lia) eq_refl)).
             - intros a. lia.
             - intros a Ha _. exact (LKV a ltac:(lia)).
             - intros a Ha HnG. exfalso. apply HnG. apply HGlk. lia.
             - intros HPRE2 HSC2.
               exact (ALOCK ly S Hp W (ms_regs ms0) (ms_mem ms0) _ (rg_lock fr_RG) 0 HPRE2 Q10
                 ltac:(lia) ltac:(rewrite HRlk; reflexivity) ltac:(lia) AVL eq_refl LK4m
                 ltac:(intros a Ha; split; [exact (LKV a ltac:(lia)) | rewrite Usp; lia])
                 ltac:(intros a Ha; split;
                       [ apply (sm_wkeep W (ms_mem ms) (ms_mem ms0) a HGb);
                         apply (sm_wkeep W mem (ms_mem ms) a HGa);
                         replace a with (rg_lock fr_RG + (a - rg_lock fr_RG)) by lia; apply LKW; lia
                       | split; [apply HNOWN; lia | rewrite Usp; lia] ])
                 (fun a Ha HK => proj2 (proj2 (HG a (HGlk a ltac:(lia)))) (proj1 (proj2 HK)))). }
           cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HP2 & HLK2 & Hfr2 & Hpres2).
           jafter_call_keep_hi HS 600%nat regs2 (mrestrict (w_H W) mem2) HP2 [0; 1; 2; 3; 4]%nat HS2.
           match type of HS2 with ?ty -> _ => assert (HRK : ty); [|specialize (HS2 HRK); clear HRK] end.
           { cbn [ms_mem restrict].
             repeat apply Forall_cons; [| | | | | apply Forall_nil];
               (eapply region_kept_aview; [sm_base | intros a Ha; apply Hfr2; lia | exact Hpres2]). }
           clear HS. rewrite <- restrict_mkst_fx in HS2. rename HS2 into HS.
           (* back from the lock: ld a0,32(s1); li a1,-1; sw a1,32(a0) (g_client := -1); to the unlock *)
           let Ev := sm_env HS in
           assert (HEIl : img_env VAL A_LIM Ev)
             by (apply img_env_havoc_hi; [assumption | cbv; lia]);
           assert (SHOK2 : sh_ok segs sm_Bx [] Ev (mrestrict (w_H W) mem2)) by (unfold sh_ok; constructor).
           paj_run_tok_xR RUNG HS HJ2 SHOK2 SMspan.
           ++ sm_df_awr.
           ++ rename HF into HFc, HFr into HFrc, HG0 into HGc.
              (* pthread_mutex_unlock (&g_lock): a0 = s4 = A_OBJ 3, kept by the lock *)
              pmkst HS.
              prreg HS (1%bv : bv 5) R1. prreg HS (2%bv : bv 5) R2. prreg HS (3%bv : bv 5) R3.
              prreg HS (4%bv : bv 5) R4. prreg HS (10%bv : bv 5) R10.
              rewrite ?ew_ewset_other in R2, R3, R4, R10 by lia.
              rewrite E2 in R2. rewrite E3 in R3. rewrite E4 in R4. rewrite E244 in R10.
              assert (Usp3 : spZ (ms_regs ms1) = F) by (unfold spZ; rewrite R2; apply unsigned_lit_small; lia).
              assert (KL3 : forall a, rg_lock fr_RG <= a < rg_lock fr_RG + 12 ->
                  aview segs (w_H W) (ms_mem ms1) a = aview segs (w_H W) mem2 a).
              { intros a Ha. apply (aview_kept_out _ _ _ _ _ HFrc a ltac:(lia)). sm_notw. }
              assert (KL13 : forall a, rg_lock fr_RG <= a < rg_lock fr_RG + 12 ->
                  ~ (rg_lock fr_RG + 4 <= a < rg_lock fr_RG + 8) ->
                  aview segs (w_H W) (ms_mem ms1) a = aview segs (w_H W) mem a).
              { intros a Ha Hn. rewrite (KL3 a Ha), (Hfr2 a ltac:(lia) Hn ltac:(lia)), (KL1 a Ha). reflexivity. }
              assert (V0u : val_mem segs (mrestrict (w_H W) (ms_mem ms1)) (rg_lock fr_RG) 4 0).
              { apply (val_mem_moved segs (w_H W) (w_H W) mem (ms_mem ms1) (rg_lock fr_RG) (rg_lock fr_RG) 4 0); [|exact LK0].
                intros j Hj. cbn in Hj. apply KL13; lia. }
              assert (V8u : val_mem segs (mrestrict (w_H W) (ms_mem ms1)) (rg_lock fr_RG + 8) 4 0).
              { apply (val_mem_moved segs (w_H W) (w_H W) mem (ms_mem ms1) (rg_lock fr_RG + 8) (rg_lock fr_RG + 8) 4 0);
                  [|exact LK8].
                intros j Hj. cbn in Hj. apply KL13; lia. }
              assert (V4u : val_mem segs (mrestrict (w_H W) (ms_mem ms1)) (rg_lock fr_RG + 4) 4 16).
              { apply (val_mem_moved segs (w_H W) (w_H W) mem2 (ms_mem ms1) (rg_lock fr_RG + 4) (rg_lock fr_RG + 4) 4 16);
                  [|exact HLK2].
                intros j Hj. cbn in Hj. apply KL3; lia. }
              assert (AV13 : forall a, rg_lock fr_RG <= a < rg_lock fr_RG + 12 ->
                  aview segs (w_H W) (ms_mem ms1) a <> None).
              { intros a Ha.
                destruct (Z_lt_le_dec a (rg_lock fr_RG + 4)) as [h1 | h1];
                  [exact (sm_av_ne W (ms_mem ms1) _ 4 0 a V0u ltac:(cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia)) |].
                destruct (Z_lt_le_dec a (rg_lock fr_RG + 8)) as [h2 | h2];
                  [ exact (sm_av_ne W (ms_mem ms1) _ 4 16 a V4u ltac:(cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia))
                  | exact (sm_av_ne W (ms_mem ms1) _ 4 0 a V8u ltac:(cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia)) ]. }
              eapply (YA0nH.SRrG_bind segs R R_trans).
              { eapply (aj_gx_entry_at_xR B PST ARx LAWS R_trans WLE_R G_fr 0 [] ESTACK (SIGMA WS_pthread_mutex_unlock)
                  (fun a => rg_lock fr_RG + 4 <= a < rg_lock fr_RG + 8)
                  (fun (regs' : bvmap 5 word) (mem' : word -> option byte) =>
                     getr regs' 10 = w64 0 /\ val_mem segs (mrestrict (w_H W) mem') (rg_lock fr_RG + 4) 4 0)
                  W (ms_regs ms1) (ms_mem ms1) STK sp0 FP ly0 S0 Hp0 W0 mem0 md0 own ly S Hp _ kk (F - sp0) _ HG eq_refl HJ2
                  ltac:(rewrite Usp3; lia) Hs16 ltac:(lia) ltac:(lia) ltac:(lia) R3 R4 R1
                  (ret_ok_codeptr_v 10048 ltac:(lia) eq_refl)).
                - intros a. lia.
                - intros a Ha _. exact (AV13 a ltac:(lia)).
                - intros a Ha HnG. exfalso. apply HnG. apply HGlk. lia.
                - intros HPRE3 HSC3.
                  exact (AUNLOCK ly S Hp W (ms_regs ms1) (ms_mem ms1) _ (rg_lock fr_RG) HPRE3 R10
                    ltac:(lia) ltac:(rewrite HRlk; reflexivity) ltac:(lia) V0u V4u V8u
                    ltac:(intros a Ha; split; [exact (AV13 a ltac:(lia)) | rewrite Usp3; lia])
                    ltac:(intros a Ha; split;
                          [ apply (sm_wkeep W mem2 (ms_mem ms1) a HGc);
                            apply (writable_kept (w_H W) (ms_mem ms0) mem2 a (Hpres2 a));
                            apply (sm_wkeep W (ms_mem ms) (ms_mem ms0) a HGb);
                            apply (sm_wkeep W mem (ms_mem ms) a HGa);
                            replace a with (rg_lock fr_RG + (a - rg_lock fr_RG)) by lia; apply LKW; lia
                          | split; [apply HNOWN; lia | rewrite Usp3; lia] ])
                 (fun a Ha HK => proj2 (proj2 (HG a (HGlk a ltac:(lia)))) (proj1 (proj2 HK)))). }
              cbv beta. intros W3 c3 _ (-> & regs3 & mem3 & md3 & -> & HJ3 & HP3 & [HR10 HLK3] & Hfr3 & Hpres3).
              jafter_call_keep_hi HS 616%nat regs3 (mrestrict (w_H W) mem3) HP3 [0; 1; 2; 3; 4]%nat HS3.
              match type of HS3 with ?ty -> _ => assert (HRK : ty); [|specialize (HS3 HRK); clear HRK] end.
              { cbn [ms_mem restrict].
                repeat apply Forall_cons; [| | | | | apply Forall_nil];
                  (eapply region_kept_aview; [sm_base | intros a Ha; apply Hfr3; lia | exact Hpres3]). }
              clear HS. rewrite <- restrict_mkst_fx in HS3. rename HS3 into HS.
              (* back from the unlock: j 0x84ce4; g_gone := 1, s4 := s5 and the latch *)
              let Ev := sm_env HS in
              assert (HEIu : img_env VAL A_LIM Ev)
                by (apply img_env_havoc_hi; [exact HEIl | cbv; lia]);
              assert (SHOK3 : sh_ok segs sm_Bx [] Ev (mrestrict (w_H W) mem3)) by (unfold sh_ok; constructor).
              paj_run_to_tok_xR RUNTOG HS HJ3 SHOK3 SMspan AF_LLVM_latch.
              ** sm_df_awr.
              ** let Ev := sm_env HS in
                 assert (HAE2 : env_agree 32 (Ereg regs (sm_x1 kb)) Ev)
                   by (apply env_agree_havoc_ge; [cbv; lia|]; apply env_agree_havoc_ge; [cbv; lia|];
                       split; [intros q Hq; rewrite ?ew_ewset_other by lia; exact (proj1 HAE q Hq)
                              | rewrite ?ed_ewset; exact (proj2 HAE)]);
                 assert (EV9 : bv_unsigned (ew Ev 9) = F) by sm_base;
                 assert (EV344 : bv_unsigned (ew Ev 344) = 0x5d955c) by sm_base;
                 assert (EV345 : bv_unsigned (ew Ev 345) = 0x5d9564) by sm_base;
                 assert (EV340 : bv_unsigned (ew Ev 340) = 0xa2540) by sm_base;
                 assert (EV23 : bv_unsigned (ew Ev 23) = 1) by sm_base;
                 assert (EV6 : bv_unsigned (ew Ev 6) = N1)
                   by (repeat (first [rewrite ew_ewset_other by (cbv; lia) | rewrite ew_havoc_old by (cbv; lia)]);
                       rewrite E6; apply unsigned_lit_small; lia).
                 pose proof (regs_kept_of_st_ok_pi (PI := PB_fr) _ _ _ regs (sm_x1 kb) sm_df_kept HS HAE2
                   ltac:(vm_compute; reflexivity)) as KR.
                 cbn [ms_regs restrict] in KR.
                 prreg HS (20%bv : bv 5) Q20.
                 repeat (first [rewrite ew_ewset_other in Q20 by (cbv; lia) | rewrite ew_havoc_old in Q20 by (cbv; lia)]).
                 rewrite U20 in Q20.
                 pose proof (st_ok_pi_region_nth _ _ _ 0 _ HS eq_refl) as RG0.
                 pose proof (st_ok_pi_region_nth _ _ _ 2 _ HS eq_refl) as RG2.
                 pose proof (st_ok_pi_region_nth _ _ _ 3 _ HS eq_refl) as RG3.
                 pose proof (st_ok_pi_region_nth _ _ _ 4 _ HS eq_refl) as RG4.
                 cbn [ms_mem restrict] in RG0, RG2, RG3, RG4.
                 assert (V144 : val_mem segs (arm W (ms_mem ms2)) (F + 144) 8 (N1 - 1))
                   by (eapply (field_of_region _ _ 9%nat F _ _ _ _ _ 144 8%N _ _ RG0);
                       [exact EV9 | left; reflexivity | cbn [sv_denot]; rewrite EV6; f_equal; lia | zside | zside]).
                 assert (Vdd' : val_mem segs (arm W (ms_mem ms2)) (rg_send_dead fr_RG) 1 dd)
                   by (replace (rg_send_dead fr_RG) with (0x5d9564 + -1892) by lia;
                       eapply (field_of_region _ _ 345%nat 0x5d9564 _ _ _ _ _ (-1892) 1%N _ _ RG2);
                       [exact EV345 | left; reflexivity | reflexivity | zside | zside]).
                 assert (Vgn' : val_mem segs (arm W (ms_mem ms2)) (rg_gone fr_RG) 1 1)
                   by (replace (rg_gone fr_RG) with (0x5d955c + -1916) by lia;
                       eapply (field_of_region _ _ 344%nat 0x5d955c _ _ _ _ _ (-1916) 1%N _ _ RG3);
                       [exact EV344 | left; reflexivity | cbn [sv_denot]; rewrite EV23; reflexivity | zside | zside]).
                 assert (Vcl' : val_mem segs (arm W (ms_mem ms2)) (rg_client fr_RG) 4 (2 ^ 32 - 1))
                   by (replace (rg_client fr_RG) with (0xa2540 + 32) by lia;
                       eapply (sm_val_m1 _ _ 340%nat 0xa2540 _ _ _ _ _ 32 _ RG4);
                       [ exact EV340 | left; reflexivity
                       | cbn [sv_denot]; apply bv_eq; rewrite !Z_to_bv_unsigned; vm_compute; reflexivity ]).
                 assert (VLK : val_mem segs (arm W (ms_mem ms2)) (rg_lock fr_RG + 4) 4 0).
                 { apply (val_mem_moved segs (w_H W) (w_H W) mem3 (ms_mem ms2) (rg_lock fr_RG + 4)
                     (rg_lock fr_RG + 4) 4 0); [|exact HLK3].
                   intros j Hj. cbn in Hj.
                   apply (aview_kept_out _ _ _ _ _ HFr (rg_lock fr_RG + 4 + j) ltac:(lia)). sm_notw. }
                 pmkst HS. apply (YA0nH.SRrG_ret segs R R_refl). unfold sm_df_post_xR; cbv beta. split; [reflexivity|].
                 exists true. do 3 eexists. split; [rewrite EN, Hodd; reflexivity|].
                 split; [reflexivity|]. split; [exact HJ3|].
                 split.
                 { apply (sm_kept_trans W mem (ms_mem ms) (ms_mem ms2));
                     [apply (sm_kept_run W _ _ mem (ms_mem ms) _ HFra HGa); sm_inX|].
                   apply (sm_kept_trans W (ms_mem ms) (ms_mem ms0) (ms_mem ms2));
                     [apply (sm_kept_run W _ _ (ms_mem ms) (ms_mem ms0) _ HFrb HGb); sm_inX|].
                   apply (sm_kept_trans W (ms_mem ms0) mem2 (ms_mem ms2));
                     [ apply (sm_kept_call W (ms_mem ms0) mem2 _ _ _ _ Hfr2 Hpres2); intros a Ha; cbv beta in Ha;
                       unfold XS, sm_df_XG; cbn [app]; sm_inFP |].
                   apply (sm_kept_trans W mem2 (ms_mem ms1) (ms_mem ms2));
                     [apply (sm_kept_run W _ _ mem2 (ms_mem ms1) _ HFrc HGc); sm_inX|].
                   apply (sm_kept_trans W (ms_mem ms1) mem3 (ms_mem ms2));
                     [ apply (sm_kept_call W (ms_mem ms1) mem3 _ _ _ _ Hfr3 Hpres3); intros a Ha; cbv beta in Ha;
                       unfold XS, sm_df_XG; cbn [app]; sm_inFP |].
                   apply (sm_kept_run W _ _ mem3 (ms_mem ms2) _ HFr HG0); sm_inX. }
                 split.
                 { apply (mem_grows_trans _ _ _ HGa). apply (mem_grows_trans _ _ _ HGb).
                   apply (mem_grows_trans _ _ _ (sm_grows_of_pres W _ _ Hpres2)). apply (mem_grows_trans _ _ _ HGc).
                   apply (mem_grows_trans _ _ _ (sm_grows_of_pres W _ _ Hpres3)). exact HG0. }
                 split; [rewrite EN; exact V144|].
                 split; [exact Vdd'|]. split; [exact Vgn'|]. split; [exact Vcl'|].
                 split; [intros _; exact VLK|].
                 split; [exact KR|]. rewrite EN. rewrite Q20. reflexivity.
Qed.
(* R twin of lf_arm_default_x: B cut_x Section wR's ARM_default_R *)
Theorem lf_arm_default_xR : forall cx Hp t W c,
  lf_base_x B MT XM_LIB RLO RHI fr_live_pre LIBROOM NP G_fr ARx cx Hp -> INV_A_xR B NP G_fr fr_FP PST ARx LSx RINV R 9 cx Hp t W c ->
  YA0nH.SRrG segs R W c (INV_K_xR B NP G_fr fr_FP PST ARx LSx RINV R cx Hp t).
Proof.
  pose proof R_refl as _. pose proof R_trans as _. pose proof WLE_R as _.
  intros cx Hp t W c HB HA.
  destruct HA as (regs & regsD & mem & md & Hc & Hkept & HopD & _ & HROM & HLF).
  destruct HLF as (own & ly3 & S3 & Hp3 & kk & m & fpos & HJ & Hown & Hframe & Hflag & Hmodel & Hinput & Hrom & Hsep &
    HLS & HNP & HRINV & HRD).
  subst own.
  pose proof HRD as (Hcommon & HD25 & Htb & Hkb & HO & Hoprest).
  cbv zeta in Hoprest. destruct Hoprest as (Hop11 & Hpick).
  assert (Hopeq : in_byte cx (lm_k m) mod 10 = 9).
  { pose proof (Z.mod_pos_bound (in_byte cx (lm_k m)) 10 ltac:(lia)) as Hmb.
    apply (f_equal bv_unsigned) in HopD. rewrite Hop11 in HopD.
    rewrite !unsigned_lit_small in HopD by lia. lia. }
  rewrite Hopeq in Hpick.
  assert (Hpk9 : picks 9 = false) by reflexivity.
  rewrite Hpk9 in Hpick. destruct Hpick as (HD20 & HD6 & _).
  assert (HARx : ARx ly3 S3 Hp3 W mem md) by (eapply ajournal_gx_AR_xR; exact HJ).
  assert (HAR : ARE ly3 S3 W mem md) by (exists Hp3; exact HARx).
  assert (Hfin : In (1, fpos) (frames S3)).
  { pose proof HJ as (_ & _ & (memS & HJ0 & _) & _). pose proof HJ0 as (_ & _ & _ & _ & _ & Hfrs & _).
    rewrite Hfrs. left. reflexivity. }
  destruct HB as (HAI & Hpre). pose proof Hpre as (Hafn & _ & _ & _ & _ & Hlen & _).
  pose proof Hafn as (_ & _ & _ & _ & _ & Hstk & _).
  pose proof Hstk as (Hsp16 & HstkK & Hceil & Hlo & Hhi & Hhi2 & _).
  set (sp0 := spZ (c_regs cx)) in *.
  assert (HSTK : LLVMF_STK = 32768) by reflexivity.
  pose proof sm_ceil_lo as Hac. assert (HES : ESTACK = 4096) by reflexivity.
  assert (Hsp0 : alloc_ceiling + 32768 <= sp0 <= 2 ^ 47) by lia.
  pose proof (Z.mod_pos_bound (sp0 - 320) 32 ltac:(lia)) as Hm32.
  assert (HFeq : lf_F cx = sp0 - 320 - (sp0 - 320) mod 32) by reflexivity.
  assert (HFbound : 2 ^ 46 <= lf_F cx <= 2 ^ 47) by lia.
  assert (HFmod : lf_F cx mod 32 = 0)
    by (rewrite HFeq; rewrite Zminus_mod, Zmod_mod, Z.sub_diag; reflexivity).
  assert (HF16 : (lf_F cx - sp0) mod 16 = 0).
  { pose proof (Z.div_mod (lf_F cx) 32 ltac:(lia)) as D1. pose proof (Z.div_mod sp0 16 ltac:(lia)) as D2.
    rewrite HFmod in D1. rewrite Hsp16 in D2.
    replace (lf_F cx - sp0) with ((2 * (lf_F cx / 32) - sp0 / 16) * 16) by lia. apply Z_mod_mult. }
  assert (KD : forall r : bv 5, In r jt_kept -> getr regs r = getr regsD r) by exact Hkept.
  pose proof Hcommon as (C2 & C8 & C9 & C18 & C19 & C23 & C24 & C26 & C27 & C3 & C4).
  assert (Hr2 : getr regs 2 = w64 (lf_F cx)) by (rewrite (KD 2%bv ltac:(sm_in)); exact C2).
  assert (Hr3 : getr regs 3 = w64 (as_gp B)) by (rewrite (KD 3%bv ltac:(sm_in)); exact C3).
  assert (Hr4 : getr regs 4 = w64 (as_tp B)) by (rewrite (KD 4%bv ltac:(sm_in)); exact C4).
  assert (Hr23 : getr regs 23 = w64 1) by (rewrite (KD 23%bv ltac:(sm_in)); exact C23).
  assert (Hr9 : getr regs 9 = w64 (lf_F cx)) by (rewrite (KD 9%bv ltac:(sm_in)); exact C9).
  assert (Hr27 : getr regs 27 = w64 SB) by (rewrite (KD 27%bv ltac:(sm_in)); exact C27).
  assert (Hr20 : getr regs 20 = w64 (c_p cx + lm_k m + 1)) by (rewrite (KD 20%bv ltac:(sm_in)); exact HD20).
  assert (Hr6 : getr regs 6 = w64 (c_n cx - lm_k m - 1)) by (rewrite (KD 6%bv ltac:(sm_in)); exact HD6).
  (* the input block and the byte in.p[0] *)
  pose proof Hinput as [[[Hn0 _] | [Hnr Hblk]] Hgarr]; [lia|].
  destruct (alx_blocks _ _ _ LAWS _ _ _ _ _ _ _ _ HARx Hblk) as (Hp16 & Hp4096 & Hpceil & Hpia & _ & _).
  pose proof (sm_blk_off_x _ _ _ _ _ _ _ _ HARx Hblk ltac:(lia)) as Hpimg.
  unfold OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B.YCbq.off_img in Hpimg.
  pose proof (req_size_pos (c_n cx) ltac:(lia)) as [_ Hreq].
  pose proof (sm_in_byte_rng cx (lm_k m + 1)) as Hkb8.
  (* the frame's three address copies, the stream's two flags, g_gone and the lock *)
  pose proof Hframe as (_ & Hawr & F32 & F40 & _ & _ & F64 & _).
  assert (HW1 : forall a, lf_F cx + 144 <= a < lf_F cx + 152 -> writable_at segs (arm W mem) a).
  { intros a Ha. replace a with (lf_F cx + (a - lf_F cx)) by lia. apply Hawr. lia. }
  pose proof Hmodel as (_ & _ & _ & Hout & Hgone & Hlock & _).
  pose proof Hout as (_ & _ & _ & _ & _ & _ & _ & _ & Ocl & Owcl & _ & _ & Odd & Owdd & _ & _ & _ & _ & _ & _ & _ &
    Odd01 & _).
  pose proof Hgone as (_ & Owgn & _).
  rewrite Hc.
  eapply YA0nH.SRrG_mono.
  { exact (sm_df_run_xR W regs mem md LLVMF_STK sp0 (lf_FP fr_FP cx) (c_ly cx) (c_S cx) Hp (c_W cx) (c_mem cx) (c_md cx)
      [(1, fpos)] ly3 S3 Hp3 kk (lf_F cx) (c_p cx + lm_k m + 1) (c_n cx - lm_k m - 1) (in_byte cx (lm_k m + 1))
      (ct_dd (lm_c m)) (ct_cl (lm_c m) mod 2 ^ 32)
      HJ Hr2 Hr3 Hr4 Hr23 Hr9 Hr27 Hr20 Hr6 ltac:(lia) HFbound HFmod ltac:(lia) Hkb8 ltac:(lia) HF16
      ltac:(lia)
      ltac:(intros HN; lia)
      ltac:(intros HN; unfold in_app in Hpia; unfold kLowShadowBeg, kHighMemBeg in *; lia)
      ltac:(intros HN; lia)
      ltac:(intros HN; rewrite <- Z.add_assoc; exact (proj1 (sm_in_byte cx (arm W mem) (lm_k m + 1) Hgarr ltac:(lia))))
      ltac:(intros HN; apply (range_addressable_of_block_hp0_x segs B ARx LAWS HP0 ly3 S3 Hp3 W mem md (c_p cx) (c_n cx));
            [exact HARx | exact Hblk | lia | lia])
      F32 F40 F64 HW1 Odd ltac:(lia) Owdd Owgn Ocl ltac:(apply Z.mod_pos_bound; lia) Owcl Hlock). }
  intros W' c' _ (-> & g & regs' & mem' & md' & Hg & -> & HJ' & KP & HGr & V144 & Vdd & Vgn & Vcl & Vlk & KR & Q20).
  assert (Hgd : g = sm_dg cx m).
  { rewrite Hg. unfold sm_dg. destruct (lm_k m + 1 <? c_n cx) eqn:Ek; [apply Z.ltb_lt in Ek | apply Z.ltb_ge in Ek].
    - replace (c_n cx - lm_k m - 1 =? 0) with false by (symmetry; apply Z.eqb_neq; lia). reflexivity.
    - replace (c_n cx - lm_k m - 1 =? 0) with true by (symmetry; apply Z.eqb_eq; lia). reflexivity. }
  pose proof (sm_df_xgok g) as HXG.
  assert (HXOK : XOK (XS (lf_F cx) (sm_df_XG g))) by (apply sm_xok; [lia | exact HXG]).
  assert (KK : forall r : bv 5, In r sm_df_kept -> In r jt_kept -> getr regs' r = getr regsD r)
    by (intros r H1 H2; rewrite (KR r H1); exact (KD r H2)).
  exists regs', mem', md'. split; [reflexivity|].
  split; [exact (sm_jt_kept W mem mem' _ HXOK KP HROM)|].
  exists [(1, fpos)], ly3, S3, Hp3, kk, (sm_default cx m g), fpos.
  split; [exact HJ'|]. split; [reflexivity|].
  split; [exact (sm_aframe_kept_x cx ly3 S3 W mem md mem' fpos (sm_df_XG g) HAR Hfin Hsp0 HXG KP HGr Hframe)|].
  split; [exact (sm_flag_kept_x ly3 S3 W mem md mem' _ fpos _ HAR HXOK KP Hfin Hflag)|].
  split; [exact (sm_amodel_df_x ly3 S3 W mem md mem' (lf_F cx) cx m g HAR ltac:(lia) KP HGr Hmodel HO Vdd Vgn Vcl Vlk)|].
  split; [exact (sm_ainput_kept_x cx ly3 S3 W mem md mem' _ HAR HXOK KP (eq_sym Hlen) Hinput)|].
  split; [exact (sm_rom_kept W mem mem' _ HXOK KP Hrom)|].
  split; [exact Hsep|].
  split; [rewrite Hgd; exact (LS_default cx t m ly3 S3 HLS)|].
  split; [exact HNP|].
  split; [rewrite Hgd; exact (RI_default cx t m HRINV)|].
  unfold lregs_K, lregs_common, sm_default. cbn [lm_k]. unfold sm_kn.
  split.
  { split; [rewrite (KK 2%bv ltac:(sm_in) ltac:(sm_in)); exact C2|].
    split; [rewrite (KK 8%bv ltac:(sm_in) ltac:(sm_in)); exact C8|].
    split; [rewrite (KK 9%bv ltac:(sm_in) ltac:(sm_in)); exact C9|].
    split; [rewrite (KK 18%bv ltac:(sm_in) ltac:(sm_in)); exact C18|].
    split; [rewrite (KK 19%bv ltac:(sm_in) ltac:(sm_in)); exact C19|].
    split; [rewrite (KK 23%bv ltac:(sm_in) ltac:(sm_in)); exact C23|].
    split; [rewrite (KK 24%bv ltac:(sm_in) ltac:(sm_in)); exact C24|].
    split; [rewrite (KK 26%bv ltac:(sm_in) ltac:(sm_in)); exact C26|].
    split; [rewrite (KK 27%bv ltac:(sm_in) ltac:(sm_in)); exact C27|].
    split; [rewrite (KK 3%bv ltac:(sm_in) ltac:(sm_in)); exact C3|].
    rewrite (KK 4%bv ltac:(sm_in) ltac:(sm_in)); exact C4. }
  split; [rewrite (KK 25%bv ltac:(sm_in) ltac:(sm_in)); exact HD25|].
  split; [exact Htb|].
  unfold sv8.
  destruct (lm_k m + 1 <? c_n cx) eqn:Ek; [apply Z.ltb_lt in Ek | apply Z.ltb_ge in Ek].
  - assert (EN : (c_n cx - lm_k m - 1 =? 0) = false) by (apply Z.eqb_neq; lia).
    rewrite EN in Q20, V144. cbv iota in Q20, V144.
    split; [rewrite Q20; f_equal; lia|].
    split; [replace (c_n cx - (lm_k m + 2)) with (c_n cx - lm_k m - 1 - 1) by lia; exact V144|]. lia.
  - assert (EN : (c_n cx - lm_k m - 1 =? 0) = true) by (apply Z.eqb_eq; lia).
    rewrite EN in Q20, V144. cbv iota in Q20, V144.
    split; [rewrite Q20; f_equal; lia|].
    split; [replace (c_n cx - (lm_k m + 1)) with 0 by lia; exact V144|]. lia.
Qed.
End smxR.

End smx.
