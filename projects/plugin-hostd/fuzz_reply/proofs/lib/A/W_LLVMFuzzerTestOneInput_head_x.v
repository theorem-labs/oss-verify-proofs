(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs, 2026-10: SEG_HEAD of the ASan walk of fuzz_reply's LLVMFuzzerTestOneInput OVER ARx (a Theorem Labs lane's route
   (b), step 7). lf_seg_head_x is the text of lib/A/W_LLVMFuzzerTestOneInput_cut_x.v Section w's hypothesis SEG_HEAD,
   so lib/A/W_LLVMFuzzerTestOneInput_top_x.v can take it in place of that hypothesis. It is the ARx conversion of W8's
   AR proof lf_seg_head (lib/A/W_LLVMFuzzerTestOneInput_head.v, Qed at a working branch 44de651f71b), which is NOT
   edited; the template is the converted check_bounded (convert_cb.py (sha256 e0f45fdf5a36; internal record)).
   - The Section header is cut_x's Section w header (B .. ARx, hl, LAWS, HP0, HG, LSx, RINV), then the AR file's own
     hypotheses, each text verbatim with LS named LSx: HGnout, HERRNO, RI_head_nout, LS_head_nout, HZS, RI_head_skip,
     LS_head_skip. No other hypothesis.
   - The AR-free names of the AR file are cited from it, not copied: the entry states hd_entry1 / hd_entry2, the
     byte / op / remainder / increment lemmas, the store-frame lemmas that name no AR (hd_writable_kept, hd_kept_off,
     hd_akept, hd_rng_off_sub, the four *_blks_in, hd_not_rom, hd_rom_low, hd_frame_nout, hd_open_val, ...), and the
     definitions lm_clear_O, lm_set_k, hd_kb, hd_k', lregs_P, HD_KEPT1/2/3.
   - Each AR-stated lemma has its twin NAME_x here (NAME_xR for the walk's, stated at R: ROUTE R below): the AR proof
     with W1Verify's substitutions (the relation ARx with the ghost list Hp after S, Hp3 after S3; alx_blocks /
     alx_zshadow for the AR laws; frames_bounds_x; W_journal_x's ajournal_gx_AR_xR / ajournal_gx_inner_xR; cut_x's
     lcut_xR / lf_base_x / INV_*_xR; paj_run(_to)_tok_x over RUN := paj_run_x_xR; range_addressable_of_block_hp0_x
     under HP0; W_frame_x's frm_off_imgP_x with its IMGC discharged by W_img_x's fr_img_cover_x). blk_off_imgP's ARx
     form is hd_blk_imgP_x: the proof of W_kit_x's blk_off_imgP_x with IMGC from fr_img_cover_x and BLKN's 0 <= n
     taken for the one block, which every caller has.
   - The AR file's Section-local Ltacs (dropped at its End h) are restated verbatim. One tactic differs from the AR
     text, for speed only: the last lregs_common discharge of hd_w2_xR (see the comment there).
   - ROUTE R (RULE-SHAPES.md (sha256 2e856ce788dd; internal record) sec 0): lf_seg_head_xR is the text of cut_x Section wR's hypothesis SEG_HEAD_R, so
     top_x's Section topxR can take it in place of that hypothesis.  Section hxR, nested at the end of Section hx, adds
     R, R_refl, R_trans, WLE_R: the theorem's arguments are lf_seg_head_x's followed by R R_refl R_trans WLE_R.  The
     segment calls nothing and moves no world: each walk is the strict walk over the R journal (lcut_xR, INV_*_xR,
     the runs paj_run(_to)_x_xR) concluding SRr, lifted by SRr_SRrG and composed by SRrG_bind.  The walk text is
     written once, at R: lf_seg_head_x is lf_seg_head_xR at R := wle (SRrG at wle is SRr, INV_*_xR at wle is
     INV_*_x, by conversion), as cut_x's lf_seg_jt_x is lf_seg_jt_xR's.
   No callee, no runtime site, no allocator rule. *)
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
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import W_rep.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YCbqG.
From Stdlib Require Import FunctionalExtensionality.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import gestures_end_b_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import W_frame W_LLVMFuzzerTestOneInput_cut.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import W_kit_x W_journal_x W_frame_x W_img_x.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import
W_LLVMFuzzerTestOneInput_cut_x W_LLVMFuzzerTestOneInput_head.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YA0nH.
(* the zify flag as the AR file's proofs see it (true there, through YN1e), whatever a Required file leaves *)
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Import ListNotations.
Local Unset Lia Cache. Local Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

Section hx.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Notation segs := (@pa_segs _ fr_prog_listing PB_fr).
#[local] Notation VAL := (@pa_val _ fr_prog_listing PB_fr).
#[local] Notation BASE := (@pa_val _ fr_prog_listing PB_fr A_TEXT).
(* ---- cut_x's Section w header (W_LLVMFuzzerTestOneInput_cut_x.v:191-235) ---- *)
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
(* ---- the AR file's own hypotheses (W_LLVMFuzzerTestOneInput_head.v:381-391, 948-950, 1002-1009), verbatim with LS
   named LSx ---- *)
(* g_nout's 8 bytes are in G_fr (the store at 0x842d0) *)
Hypothesis HGnout : forall a, rg_nout fr_RG <= a < rg_nout fr_RG + 8 -> inG G_fr a.
(* errno's cell (tp - 164, in musl's static TLS) is apart from g_nout *)
Hypothesis HERRNO : 0 <= as_errno B /\ as_errno B + 4 <= 2 ^ 64 /\
  (as_errno B + 4 <= rg_nout fr_RG \/ rg_nout fr_RG + 8 <= as_errno B).
(* RI_head_1: g_nout := 0 forgets what the controller read in the previous operation *)
Hypothesis RI_head_nout : forall cx t m, RINV cx t m -> RINV cx t (lm_clear_O m).
(* LS_head_1: the same step on the allocator state's invariant (no allocation, no block changes) *)
Hypothesis LS_head_nout : forall cx t m ly S, LSx cx t m ly S -> LSx cx t (lm_clear_O m) ly S.
(* g_s's shadow is zero: the instance lists g_s's 384 bytes among its zero-shadow ranges (W_contract.v azs) *)
Hypothesis HZS : exists r, In r (as_zero_shadow B) /\ fst r mod 8 = 0 /\ fst r <= rg_s fr_RG /\
  rg_s fr_RG + 4 * ASRC <= fst r + snd r / 8 * 8.
(* RI_head_2: `continue` (an op that picks, no open source, op <> 1) ends the operation with the input consumed *)
Hypothesis RI_head_skip : forall cx t m, 0 <= t < OPS_MAX -> 0 <= lm_k m < c_n cx -> lm_O m = [] ->
  picks (in_byte cx (lm_k m) mod 10) = true -> in_byte cx (lm_k m) mod 10 <> 1 ->
  pick (lm_hs m) (hd_kb cx m) = None -> RINV cx t m -> RINV cx (t + 1) (lm_set_k m (hd_k' cx m)).
(* LS_head_2: the same step on the allocator state's invariant *)
Hypothesis LS_head_skip : forall cx t m ly S, 0 <= t < OPS_MAX -> 0 <= lm_k m < c_n cx -> lm_O m = [] ->
  picks (in_byte cx (lm_k m) mod 10) = true -> in_byte cx (lm_k m) mod 10 <> 1 ->
  pick (lm_hs m) (hd_kb cx m) = None -> LSx cx t m ly S -> LSx cx (t + 1) (lm_set_k m (hd_k' cx m)) ly S.

Let BR := paj_branch (PI := PB_fr).

(* ---- the store frame's block lemmas over ARx (the AR file's Section fo, :252-374) ---- *)
(* W_kit_x.v:47 blk_off_imgP_x's proof: IMGC is W_img_x.v's fr_img_cover_x (the laws' field 17), and BLKN's
   0 <= n is a premise for the one block *)
Lemma hd_blk_imgP_x : forall ly S Hp (W : world segs) mem md p n,
  ARx ly S Hp W mem md -> In (p, n) (ablocks B ly S) -> 0 <= n ->
  p + req_size n <= 0x10000 \/ 0x5fb000 <= p.
Proof.
  intros ly S Hp W mem md p n HAR Hin Hn.
  destruct (fr_img_cover_x B ARx LAWS ly S Hp W mem md HAR) as [C1 C2].
  pose proof (req_size_pos n Hn) as [Q _].
  destruct (Z.le_gt_cases (p + req_size n) 0x10000) as [|H1]; [left; lia|].
  destruct (Z.le_gt_cases 0x5fb000 p) as [|H2]; [right; lia|]. exfalso.
  assert (Hc : ~ in_zr (Z.max p 0x10000) (ly_img ly)).
  { refine (proj1 (alx_client_img _ _ _ LAWS ly S Hp W mem md (Z.max p 0x10000) HAR _)).
    left. exists p, n. split; [exact Hin | lia]. }
  apply Hc. unfold in_zr. lia.
Qed.
Section fo.
Variables lo hi : Z.
Hypothesis Hlo : 0x10008 <= lo.
Hypothesis Hhi : hi <= 0x5fb000.
(* a byte of a live block, or within 8 bytes after it *)
Lemma hd_blk_off_x : forall ly S Hp W mem md p n a, ARx ly S Hp W mem md -> In (p, n) (ablocks B ly S) -> 0 <= n ->
  p <= a < p + req_size n + 8 -> offw lo hi a.
Proof.
  intros ly S Hp W mem md p n a HAR Hin Hn Ha.
  destruct (alx_blocks _ _ _ LAWS _ _ _ _ _ _ _ _ HAR Hin) as (_ & Hp4096 & Hpceil & _ & _ & _).
  pose proof (hd_blk_imgP_x ly S Hp W mem md p n HAR Hin Hn) as Himg.
  pose proof asan_consts as (C1 & _). split; lia.
Qed.
Lemma hd_alist_fp_off_x : forall ly S Hp W mem md LA l lines, ARx ly S Hp W mem md ->
  alist_at B ly S W mem LA l lines -> rng_off lo hi (LA, LA + 16) ->
  forall r, In r (alist_fp LA l) -> rng_off lo hi r.
Proof.
  intros ly S Hp W mem md LA l lines HAR (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9) HLA r Hr.
  unfold alist_fp in Hr. destruct Hr as [<- | Hr]; [exact HLA|].
  apply in_app_or in Hr as [Hr | Hr].
  - destruct (hl_cap l =? 0) eqn:Ec; [destruct Hr|]. destruct Hr as [<- | []].
    apply Z.eqb_neq in Ec.
    destruct H6 as [(Hc & _) | (Hc & Hin & Hj & _)]; [lia|].
    intros a Ha. unfold gfp, bzs in Ha. cbn [fst snd] in Ha. rewrite length_map, length_app, hd_len_text in Ha.
    unfold hl_n in Hj, H5.
    apply (hd_blk_off_x ly S Hp W mem md (hl_v l) (AREC * hl_cap l) a HAR Hin ltac:(unfold AREC; lia)).
    pose proof (req_size_pos (AREC * hl_cap l) ltac:(unfold AREC; lia)) as [_ Hq]. unfold AREC in *. lia.
  - apply in_map_iff in Hr as (rr & <- & Hrr). rewrite Forall_forall in H9. destruct (H9 rr Hrr) as (Hb & _).
    intros a Ha. unfold gfp, bzs in Ha. cbn [fst snd] in Ha. rewrite length_map, length_app in Ha. cbn [length] in Ha.
    apply (hd_blk_off_x ly S Hp W mem md (fst rr) (Z.of_nat (length (snd rr)) + 1) a HAR Hb ltac:(lia)).
    pose proof (req_size_pos (Z.of_nat (length (snd rr)) + 1) ltac:(lia)) as [_ Hq]. lia.
Qed.
Lemma hd_asrc_fp_off_x : forall ly S Hp W mem md HA h, ARx ly S Hp W mem md -> asrc_at B ly S W mem HA h ->
  rng_off lo hi (HA, HA + ASRC) -> forall r, In r (asrc_fp HA h) -> rng_off lo hi r.
Proof.
  intros ly S Hp W mem md HA h HAR Hs HHA r Hr.
  pose proof Hs as (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11 & H12 & H13 & H14 & H15 & H16 & H17 & H18 &
    H19 & H20 & H21 & H22 & H23 & H24).
  unfold asrc_fp in Hr. destruct Hr as [<- | [<- | Hr]]; [exact HHA | |].
  - intros a Ha. unfold gfp, bzs in Ha. cbn [fst snd] in Ha. rewrite length_map, H19 in Ha.
    apply (hd_blk_off_x ly S Hp W mem md (hs_partial h) APARTIAL a HAR H18 ltac:(unfold APARTIAL; lia)).
    pose proof (req_size_pos APARTIAL ltac:(unfold APARTIAL; lia)) as [_ Hq]. lia.
  - apply in_app_or in Hr as [Hr | Hr]; [|apply in_app_or in Hr as [Hr | Hr]].
    + apply (hd_alist_fp_off_x ly S Hp W mem md (HA + 16) (hs_pending h) false HAR H10); [|exact Hr].
      apply (hd_rng_off_sub lo hi HA ASRC); [exact HHA | lia | unfold ASRC; lia].
    + apply (hd_alist_fp_off_x ly S Hp W mem md (HA + 64) (hs_expected h) true HAR H22); [|exact Hr].
      apply (hd_rng_off_sub lo hi HA ASRC); [exact HHA | lia | unfold ASRC; lia].
    + apply (hd_alist_fp_off_x ly S Hp W mem md (HA + 80) (hs_held h) true HAR H23); [|exact Hr].
      apply (hd_rng_off_sub lo hi HA ASRC); [exact HHA | lia | unfold ASRC; lia].
Qed.
Lemma hd_aentry_fp_off_x : forall ly S Hp W mem md e, ARx ly S Hp W mem md -> aentry_ok B ly S W mem e ->
  forall r, In r (aentry_fp e) -> rng_off lo hi r.
Proof.
  intros ly S Hp W mem md e HAR (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11 & H12 & H13 & H14 & H15) r Hr.
  unfold aentry_fp in Hr. apply in_app_or in Hr as [Hr | Hr].
  - destruct (re_cap e =? 0) eqn:Ec; [destruct Hr|]. destruct Hr as [<- | []]. apply Z.eqb_neq in Ec.
    destruct H10 as [(Hc & _) | (Hc & Hin & Hj & _)]; [lia|].
    intros a Ha. unfold gfp, bzs in Ha. cbn [fst snd] in Ha. rewrite length_map, length_app in Ha.
    apply (hd_blk_off_x ly S Hp W mem md (re_buf e) (re_cap e) a HAR Hin ltac:(lia)).
    pose proof (req_size_pos (re_cap e) ltac:(lia)) as [_ Hq]. lia.
  - destruct Hr as [<- | Hr].
    + intros a Ha. unfold gfp, bzs in Ha. cbn [fst snd] in Ha. rewrite length_map, hd_len_kptrs in Ha.
      destruct H12 as [(Hz & Hk) | (Hz & Hin & Hk1 & Hk2 & _)]; [rewrite Hk in Ha; cbn in Ha; lia|].
      apply (hd_blk_off_x ly S Hp W mem md (re_hp e) (re_kh e) a HAR Hin ltac:(lia)).
      pose proof (req_size_pos (re_kh e) ltac:(lia)) as [_ Hq]. unfold re_nheld in Hk1. lia.
    + apply in_map_iff in Hr as (k & <- & Hk). rewrite Forall_forall in H15. destruct (H15 k Hk) as (K1 & K2 & K3 & K4 & K5).
      intros a Ha. unfold gfp, bzs in Ha. cbn [fst snd] in Ha. rewrite length_map, length_app in Ha. cbn [length] in Ha.
      apply (hd_blk_off_x ly S Hp W mem md (key_addr k) (Z.of_nat (length (key_text k)) + 1) a HAR K1 ltac:(lia)).
      pose proof (req_size_pos (Z.of_nat (length (key_text k)) + 1) ltac:(lia)) as [_ Hq]. lia.
Qed.
Lemma hd_arelay_fp_off_x : forall RG ly S Hp W mem md G es, ARx ly S Hp W mem md -> arelay_at B RG ly S W mem G es ->
  rng_off lo hi (rg_src RG, rg_src RG + 8) -> rng_off lo hi (rg_nsrc RG, rg_nsrc RG + 4) ->
  rng_off lo hi (rg_capsrc RG, rg_capsrc RG + 4) ->
  forall r, In r (arelay_fp RG G es) -> rng_off lo hi r.
Proof.
  intros RG ly S Hp W mem md G es HAR (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11) R1 R2 R3 r Hr.
  unfold arelay_fp in Hr. destruct Hr as [<- | [<- | [<- | [<- | Hr]]]]; [exact R1 | exact R2 | exact R3 | |].
  - intros a Ha. cbn [fst snd] in Ha. apply (hd_blk_off_x ly S Hp W mem md G ATABLE a HAR H8 ltac:(unfold ATABLE; lia)).
    pose proof (req_size_pos ATABLE ltac:(unfold ATABLE; lia)) as [_ Hq]. lia.
  - apply in_concat in Hr as (l & Hl & Hr). apply in_map_iff in Hl as (e & <- & He).
    rewrite Forall_forall in H10. exact (hd_aentry_fp_off_x ly S Hp W mem md e HAR (H10 e He) r Hr).
Qed.
End fo.

(* the controller's stream after g_nout := 0: what it read in this operation is forgotten (O = []), its bytes become
   part of the buffer's junk *)
Lemma hd_aout_clear_x : forall ly S Hp W mem md mem' c O mx no cap out,
  ARx ly S Hp W mem md ->
  (forall a, offw 6129856 6129864 a -> abyte_kept W mem W mem' a) ->
  (forall a, writable_at segs (arm W mem) a -> writable_at segs (arm W mem') a) ->
  val_mem segs (arm W mem') (rg_nout fr_RG) 8 0 -> rng_off 6129856 6129864 (as_errno B, as_errno B + 4) ->
  aout_at B fr_RG ly S W mem c O mx no cap out -> aout_at B fr_RG ly S W mem' c [] mx 0 cap out.
Proof.
  intros ly S Hp W mem md mem' c O mx no cap out HAR KB KW HN0 HER
    (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11 & H12 & H13 & H14 & H15 & H16 & H17 & H18 &
     H19 & H20 & H21 & H22 & H23 & H24 & H25 & H26).
  assert (KK : forall x, 0 <= x < 6129856 \/ 6129864 <= x < 2 ^ 64 -> abyte_kept W mem W mem' x)
    by (intros x Hx; apply KB; split; lia).
  unfold aout_at. cbn [rg_send_max rg_nout rg_capout rg_out rg_client rg_client_broken rg_send_dead rg_send_eintr fr_RG fr_globals]
    in *.
  pose proof HER as HER'. unfold rng_off, offw in HER'. cbn [fst snd] in HER'.
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
  apply (hd_blk_off_x 6129856 6129864 ltac:(lia) ltac:(lia) ly S Hp W mem md out cap x HAR Hin ltac:(lia)).
  pose proof (req_size_pos cap ltac:(lia)) as [_ Hq]. lia.
Qed.

Lemma hd_store_kept_x : forall cx Hp ly3 S3 Hp3 W mem md mem' fpos m,
  lf_base_x B MT XM_LIB RLO RHI fr_live_pre LIBROOM NP G_fr ARx cx Hp ->
  ARx ly3 S3 Hp3 W mem md -> In (1, fpos) (frames S3) ->
  (forall x : word, ~ (rg_nout fr_RG <= bv_unsigned x < rg_nout fr_RG + 8) -> mrestrict (w_H W) mem' x = mrestrict (w_H W) mem x) ->
  mem_grows (mrestrict (w_H W) mem) (mrestrict (w_H W) mem') ->
  val_mem segs (arm W mem') (rg_nout fr_RG) 8 0 ->
  aframe_at cx true (frame_addr ly3 1 fpos) W mem -> amodel_at B ly3 S3 W mem m -> ainput_at B cx ly3 S3 W mem ->
  rom_view segs W mem -> jt_rom W mem ->
  aframe_at cx true (frame_addr ly3 1 fpos) W mem' /\ amodel_at B ly3 S3 W mem' (lm_clear_O m) /\
  ainput_at B cx ly3 S3 W mem' /\ rom_view segs W mem' /\ jt_rom W mem'.
Proof.
  intros cx Hp ly3 S3 Hp3 W mem md mem' fpos m HB HAR Hfp HKX HGR HN0 HFR HMOD HIN HRV HJT.
  change (rg_nout fr_RG) with 6129856 in HKX, HN0.
  pose proof (hd_kept_off W mem mem' 6129856 (6129856 + 8) HKX HGR) as KB. change (6129856 + 8) with 6129864 in KB.
  pose proof (hd_writable_kept W mem mem' HGR) as KW.
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  pose proof HB as (HAI & HPRE & Hra & Ha0 & Ha1 & Hblk0 & Hlen & _).
  pose proof HPRE as (HAR0 & Hra0 & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
  pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
  unfold LLVMF_STK in *.
  pose proof (Z.mod_pos_bound (spZ (c_regs cx) - 320) 32 ltac:(lia)) as HFm.
  assert (HF : spZ (c_regs cx) - 351 <= lf_F cx <= spZ (c_regs cx) - 320) by (unfold lf_F; lia).
  destruct (frames_bounds_x _ _ _ LAWS _ _ _ _ _ _ _ _ HAR Hfp) as (HFF0 & HFF1 & _).
  pose proof (frm_off_imgP_x B ARx LAWS (fr_img_cover_x B ARx LAWS) _ _ _ _ _ _ _ _ HAR Hfp) as HFFi. unfold off_img in HFFi.
  change (fs_frame_bytes 1) with 128 in HFF1, HFFi.
  assert (KX : forall a n, 0 <= a -> a + n <= 6129856 \/ 6129864 <= a -> a + n <= 2 ^ 64 ->
    forall x, a <= x < a + n -> abyte_kept W mem W mem' x)
    by (intros a n Ha Hn Hb x Hx; apply KB; split; lia).
  split; [|split; [|split; [|split]]].
  - (* the frame and the fake frame *)
    unfold aframe_at in *. cbv zeta in *.
    destruct HFR as (FS & FW & F24 & F48 & F56 & F64 & F72 & F80 & F88 & F96 & F184 & Ffull & FF0 & FF8 & FF16 &
      FFw & FFsh & FFshw).
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
    split; [apply KV; [lia | lia | exact F24]|]. split; [apply KV; [lia | lia | exact F48]|].
    split; [apply KV; [lia | lia | exact F56]|]. split; [apply KV; [lia | lia | exact F64]|].
    split; [apply KV; [lia | lia | exact F72]|]. split; [apply KV; [lia | lia | exact F80]|].
    split; [apply KV; [lia | lia | exact F88]|]. split; [apply KV; [lia | lia | exact F96]|].
    split; [apply KV; [lia | lia | exact F184]|].
    split.
    { intros Hfull. destruct (Ffull Hfull) as (F32 & F104 & F112 & F120 & F128 & F136 & F152).
      split; [apply KV; [lia | lia | exact F32]|]. split; [apply KV; [lia | lia | exact F104]|].
      split; [apply KV; [lia | lia | exact F112]|]. split; [apply KV; [lia | lia | exact F120]|].
      split; [apply KV; [lia | lia | exact F128]|]. split; [apply KV; [lia | lia | exact F136]|].
      apply KV; [lia | lia | exact F152]. }
    split; [apply KF; [lia | lia | exact FF0]|]. split; [apply KF; [lia | lia | exact FF8]|].
    split; [apply KF; [lia | lia | exact FF16]|].
    split; [apply (akept_awr W mem); [intros x Hx; apply (KX (frame_addr ly3 1 fpos) 128); lia | exact FFw]|].
    assert (HSB : 0 <= SB + frame_addr ly3 1 fpos / 8 /\ SB + frame_addr ly3 1 fpos / 8 + 16 <= 2 ^ 64 /\
      6129864 <= SB + frame_addr ly3 1 fpos / 8).
    { unfold SB. pose proof (Z.div_pos (frame_addr ly3 1 fpos) 8 ltac:(lia) ltac:(lia)).
      pose proof (Z.div_le_upper_bound (frame_addr ly3 1 fpos) 8 (2 ^ 47) ltac:(lia) ltac:(lia)). lia. }
    split.
    { apply (akept_garr8 W mem); [|exact FFsh]. intros x Hx. change (length fake_shadow) with 16%nat in Hx.
      apply (KX (SB + frame_addr ly3 1 fpos / 8) 16); lia. }
    apply (akept_awr W mem); [intros x Hx; apply (KX (SB + frame_addr ly3 1 fpos / 8) 16); lia | exact FFshw].
  - (* the model, with what the controller read in this operation forgotten *)
    destruct HMOD as (Hhs4 & Hslots & Hrel & Hout & Hgone & Hlock & Hwake & Hnfd & Hnfdw & Hnfdr & Htu & Hlst & Hlstw).
    unfold amodel_at. cbn [lm_hs lm_G lm_es lm_c lm_O lm_mx lm_cap lm_out lm_gn lm_nfd lm_clear_O].
    split; [exact Hhs4|].
    split.
    { intros i Hi. specialize (Hslots i Hi). unfold aslot in *.
      assert (HHA : rng_off 6129856 6129864 (rg_s fr_RG + ASRC * Z.of_nat i, rg_s fr_RG + ASRC * Z.of_nat i + ASRC)).
      { intros x Hx. cbn [fst snd rg_s fr_RG fr_globals] in Hx. unfold ASRC in Hx. split; lia. }
      destruct (nth i (lm_hs m) None) as [h|].
      - apply (asrc_at_kept B ly3 S3 W mem ly3 S3 W mem' _ h Hslots).
        + apply (hd_akept W mem mem' 6129856 6129864); [exact KB|].
          exact (hd_asrc_fp_off_x 6129856 6129864 ltac:(lia) ltac:(lia) ly3 S3 Hp3 W mem md _ h HAR Hslots HHA).
        + exact (hd_asrc_blks_in B ly3 S3 W mem _ h Hslots).
      - destruct Hslots as [Hz Hw]. split.
        + apply (akept_garr8 W mem); [|exact Hz]. intros x Hx. rewrite repeat_length in Hx. apply KB. apply HHA.
          cbn [fst snd]. unfold ASRC in *. lia.
        + apply (akept_awr W mem); [|exact Hw]. intros x Hx. apply KB. apply HHA. cbn [fst snd]. lia. }
    split.
    { apply (arelay_at_kept B fr_RG ly3 S3 W mem ly3 S3 W mem' _ _ Hrel).
      + apply (hd_akept W mem mem' 6129856 6129864); [exact KB|].
        apply (hd_arelay_fp_off_x 6129856 6129864 ltac:(lia) ltac:(lia) fr_RG ly3 S3 Hp3 W mem md _ _ HAR Hrel);
          intros x Hx; cbn [fst snd rg_src rg_nsrc rg_capsrc fr_RG fr_globals] in Hx; split; lia.
      + exact (hd_arelay_blks_in B fr_RG ly3 S3 W mem _ _ Hrel). }
    split.
    { eapply (hd_aout_clear_x ly3 S3 Hp3 W mem md mem' _ _ _ _ _ _ HAR KB KW HN0); [|exact Hout].
      intros x Hx. cbn [fst snd] in Hx. pose proof HERRNO as (He0 & He1 & He2).
      cbn [rg_nout fr_RG fr_globals] in He2. split; lia. }
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
    apply (hd_blk_off_x 6129856 6129864 ltac:(lia) ltac:(lia) ly3 S3 Hp3 W mem md (c_p cx) (c_n cx) x HAR Hin ltac:(lia)).
    pose proof (req_size_pos (c_n cx) ltac:(lia)) as [_ Hq]. lia.
  - (* .rodata *)
    intros a Ha. pose proof (hd_rom_low a Ha) as Hrl.
    destruct (Z_lt_le_dec a 6129856) as [Hlt | Hge].
    + rewrite (proj1 (KB a ltac:(split; lia))). apply HRV. exact Ha.
    + destruct (Z_lt_le_dec a 6129864) as [Hlt2 | Hge2].
      * exfalso. exact (hd_not_rom 6129856 6129864 a hd_nout_not_rom ltac:(lia) Ha).
      * rewrite (proj1 (KB a ltac:(split; lia))). apply HRV. exact Ha.
  - (* the jump table *)
    intros i Hi. apply (akept_vm W mem); [|exact (HJT i Hi)].
    intros x Hx. apply KB. unfold fr_jtab in Hx. cbn in Hx. split; lia.
Qed.
(* the fake frame's flag word (lcut's conjunct after aframe_at) across a store to g_nout only *)
Lemma hd_flag_kept_x : forall cx Hp ly3 S3 Hp3 W mem md mem' fpos,
  lf_base_x B MT XM_LIB RLO RHI fr_live_pre LIBROOM NP G_fr ARx cx Hp ->
  ARx ly3 S3 Hp3 W mem md -> In (1, fpos) (frames S3) ->
  (forall x : word, ~ (rg_nout fr_RG <= bv_unsigned x < rg_nout fr_RG + 8) -> mrestrict (w_H W) mem' x = mrestrict (w_H W) mem x) ->
  mem_grows (mrestrict (w_H W) mem) (mrestrict (w_H W) mem') ->
  sv8 W mem (frame_addr ly3 1 fpos + 120) (flag_addr ly3 1 fpos) ->
  sv8 W mem' (frame_addr ly3 1 fpos + 120) (flag_addr ly3 1 fpos).
Proof.
  intros cx Hp ly3 S3 Hp3 W mem md mem' fpos HB HAR Hfp HKX HGR Hv.
  change (rg_nout fr_RG) with 6129856 in HKX.
  pose proof (hd_kept_off W mem mem' 6129856 (6129856 + 8) HKX HGR) as KB. change (6129856 + 8) with 6129864 in KB.
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  destruct (frames_bounds_x _ _ _ LAWS _ _ _ _ _ _ _ _ HAR Hfp) as (HFF0 & HFF1 & _).
  pose proof (frm_off_imgP_x B ARx LAWS (fr_img_cover_x B ARx LAWS) _ _ _ _ _ _ _ _ HAR Hfp) as HFFi. unfold off_img in HFFi.
  change (fs_frame_bytes 1) with 128 in HFF1, HFFi.
  unfold sv8 in *. apply (akept_vm W mem); [|exact Hv].
  intros x Hx. cbn in Hx. apply KB. split; lia.
Qed.

(* ---- route R (RULE-SHAPES.md (sha256 2e856ce788dd; internal record) sec 0): the walk at a world relation R, over cut_x Section wR's cut points.  The
   segment moves no world, so each walk is the strict walk over the R journal and concludes SRr: RUN / RUNTO are
   W_journal_x's runs over ajournal_gx_xR R (paj_run_x_xR / paj_run_to_x_xR), AJG is that journal. ---- *)
Section hxR.
Variable R : world segs -> world segs -> Prop.
Hypothesis R_refl : forall W, R W W.
Hypothesis R_trans : forall W1 W2 W3, R W1 W2 -> R W2 W3 -> R W1 W3.
Hypothesis WLE_R : forall W W', wle W W' -> R W W'.
Let RUN := paj_run_x_xR (PL := PL_fr) (PI := PB_fr) B PST ARx LAWS R G_fr HG 0 [].
Let RUNTO := paj_run_to_x_xR (PL := PL_fr) (PI := PB_fr) B PST ARx LAWS R G_fr HG 0 [].
Local Notation AJG := (ajournal_gx_xR segs B PST ARx R G_fr 0 []).

(* the pick P (0x842e0) over ARx: the AR file's INV_P (:400) with cut_x's lcut_xR *)
Definition INV_P_xR (cx : lfcx) (Hp : list Z) (t : Z) : world segs -> config -> Prop :=
  fun W c => exists regs mem md, c = cfg_at segs (fr_B0 + AF_LLVM_pick) regs mem md /\
    jt_rom W mem /\ lcut_xR B NP G_fr fr_FP PST ARx LSx RINV R cx Hp t true (lregs_P B cx t) regs mem md W.

(* the cut facts after walk 1's store to g_nout, at the run's final memory and registers *)
Lemma hd_w1_lcut_xR : forall cx Hp t W mem md mem' md' ly3 S3 Hp3 k m fpos
    (RC : lmod -> Z -> bvmap 5 word -> world segs -> (word -> option byte) -> Prop) regs',
  lf_base_x B MT XM_LIB RLO RHI fr_live_pre LIBROOM NP G_fr ARx cx Hp ->
  AJG LLVMF_STK (spZ (c_regs cx)) (lf_FP fr_FP cx) (c_ly cx) (c_S cx) Hp (c_W cx) (c_mem cx)
    (c_md cx) [(1, fpos)] ly3 S3 Hp3 W mem md k ->
  AJG LLVMF_STK (spZ (c_regs cx)) (lf_FP fr_FP cx) (c_ly cx) (c_S cx) Hp (c_W cx) (c_mem cx)
    (c_md cx) [(1, fpos)] ly3 S3 Hp3 W mem' md' k ->
  (forall x : word, ~ (rg_nout fr_RG <= bv_unsigned x < rg_nout fr_RG + 8) -> mrestrict (w_H W) mem' x = mrestrict (w_H W) mem x) ->
  mem_grows (mrestrict (w_H W) mem) (mrestrict (w_H W) mem') ->
  val_mem segs (arm W mem') (rg_nout fr_RG) 8 0 ->
  aframe_at cx true (frame_addr ly3 1 fpos) W mem -> sv8 W mem (frame_addr ly3 1 fpos + 120) (flag_addr ly3 1 fpos) ->
  amodel_at B ly3 S3 W mem m -> ainput_at B cx ly3 S3 W mem ->
  rom_view segs W mem -> ablocks_sep B fr_FP cx m ly3 S3 -> LSx cx t m ly3 S3 -> NP S3 -> RINV cx t m -> jt_rom W mem ->
  RC (lm_clear_O m) (frame_addr ly3 1 fpos) regs' W mem' ->
  jt_rom W mem' /\ lcut_xR B NP G_fr fr_FP PST ARx LSx RINV R cx Hp t true RC regs' mem' md' W.
Proof.
  intros cx Hp t W mem md mem' md' ly3 S3 Hp3 k m fpos RC regs' HB HJ HJ' HKX HGR HN0 HFR HFL HMOD HIN HRV HSEP HLS HNP HRI HJT HR.
  assert (HAR : ARx ly3 S3 Hp3 W mem md) by (eapply ajournal_gx_AR_xR; exact HJ).
  assert (Hfp : In (1, fpos) (frames S3)).
  { pose proof HJ as HJi0. apply ajournal_gx_inner_xR in HJi0. destruct HJi0 as (memS & HJi & _).
    pose proof HJi as (_ & _ & _ & _ & _ & Hfrs & _). rewrite Hfrs. left. reflexivity. }
  destruct (hd_store_kept_x cx Hp ly3 S3 Hp3 W mem md mem' fpos m HB HAR Hfp HKX HGR HN0 HFR HMOD HIN HRV HJT)
    as (F' & M' & I' & RV' & JT').
  split; [exact JT'|].
  exists [(1, fpos)], ly3, S3, Hp3, k, (lm_clear_O m), fpos.
  split; [exact HJ'|]. split; [reflexivity|]. split; [exact F'|].
  split; [exact (hd_flag_kept_x cx Hp ly3 S3 Hp3 W mem md mem' fpos HB HAR Hfp HKX HGR HFL)|].
  split; [exact M'|]. split; [exact I'|].
  split; [exact RV'|]. split; [exact HSEP|]. split; [apply LS_head_nout; exact HLS|]. split; [exact HNP|].
  split; [apply RI_head_nout; exact HRI|]. exact HR.
Qed.
(* writes of walk 1's runs: g_nout's 8 bytes only *)
Ltac hd_wr E25 :=
  let a := fresh "a" in let r := fresh "r" in let Hin := fresh "Hin" in let Hr := fresh "Hr" in
  intros a (r & Hin & Hr); vm_compute in Hin;
  repeat (destruct Hin as [<- | Hin]; [cbn [YP09.r_base YP09.r_wlo YP09.r_whi YP09.base_val] in Hr;
    first [ lia
          | rewrite ?ew_ewset_other in Hr by lia; rewrite E25, unsigned_lit_small in Hr by (unfold HI_G_NOUT; lia);
            cbn; unfold HI_G_NOUT in Hr; lia ] |]);
  destruct Hin.
Ltac hd_awr E25 HGn :=
  lazymatch goal with |- awr_ok_x ?Ev ?rs ?G ?XO ?OUT ?STK ?sp0 ?FP ?b0 ?bc ?ly ?own =>
    let rs' := eval vm_compute in rs in change (awr_ok_x Ev rs' G XO OUT STK sp0 FP b0 bc ly own) end;
  repeat first
   [ apply awr_ok_x_nil
   | apply awr_ok_x_cons; [let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha;
       cbn [YP09.r_base YP09.r_wlo YP09.r_whi YP09.base_val] in Ha;
       first [ lia
             | right; left; apply HGn; rewrite ?ew_ewset_other in Ha by lia;
               rewrite E25, unsigned_lit_small in Ha by (unfold HI_G_NOUT; lia); cbn; unfold HI_G_NOUT in Ha; lia ] |] ].
(* g_nout = 0 after the store, read off the run's g_nout region (the third region) *)
Ltac hd_nout0 HS E25 HN0 :=
  lazymatch type of HS with st_ok_pi ?sg ?vl ?Ev ?ss (restrict ?H ?ms) =>
    let r := eval vm_compute in (nth 2 (ss_mem ss) hd_rnout) in
    let HRN := fresh "HRN" in
    pose proof (st_ok_pi_region_nth Ev ss (restrict H ms) 2 r HS ltac:(vm_compute; reflexivity)) as HRN;
    cbn [ms_mem restrict] in HRN;
    pose proof (field_of_region Ev _ 25 HI_G_NOUT _ _ _ _ _ 1668 8 (SLit 0) 0 HRN
      ltac:(rewrite ?ew_ewset_other by lia; rewrite E25; apply unsigned_lit_small; unfold HI_G_NOUT; lia)
      ltac:(left; reflexivity) eq_refl ltac:(lia) ltac:(lia)) as HN0;
    change (HI_G_NOUT + 1668) with (rg_nout fr_RG) in HN0; change (N.to_nat 8) with 8%nat in HN0; clear HRN
  end.
Ltac hd_upd E25 MEQ MG :=
  lazymatch goal with HFx : frame_of ?Ev ?rs (mrestrict ?H (ms_mem ?ms0)) (mrestrict ?H (ms_mem ?ms1)) |- _ =>
  lazymatch goal with HGx : mem_grows (mrestrict H (ms_mem ms0)) (mrestrict H (ms_mem ms1)) |- _ =>
    let MEQn := fresh "MEQn" in let MGn := fresh "MGn" in
    lazymatch type of MEQ with forall x, _ -> mrestrict _ _ x = mrestrict _ ?m0 x =>
    assert (MEQn : forall x : word, ~ (rg_nout fr_RG <= bv_unsigned x < rg_nout fr_RG + 8) ->
        mrestrict H (ms_mem ms1) x = mrestrict H m0 x)
      by (let x := fresh "x" in let Hx := fresh "Hx" in intros x Hx;
          rewrite (hd_frame_nout Ev rs _ _ HFx ltac:(hd_wr E25) x Hx); exact (MEQ x Hx)) end;
    pose proof (hd_mem_grows_trans _ _ _ MG HGx) as MGn;
    clear MEQ MG HFx HGx; rename MEQn into MEQ; rename MGn into MG end end;
  repeat match goal with H : frame_of _ _ _ _ |- _ => clear H end.
Ltac prreg_raw HS r Hr :=
  lazymatch type of HS with st_ok_pi ?segs ?val ?E ?ss (restrict ?H ?ms) =>
    pose proof (st_ok_pi_restrict_reg H E ss ms r HS) as Hr;
    let e := eval vm_compute in (sr_get (ss_regs ss) r) in change (sr_get (ss_regs ss) r) with e in Hr;
    cbn [ms_regs restrict] in Hr end.

Lemma hd_w1_xR : forall cx Hp t W c, lf_base_x B MT XM_LIB RLO RHI fr_live_pre LIBROOM NP G_fr ARx cx Hp -> INV_H_xR B NP G_fr fr_FP PST ARx LSx RINV R cx Hp t W c ->
  SRr segs W c (fun W' c' => (exists op, 0 <= op <= 9 /\ INV_D_xR B NP G_fr fr_FP PST ARx LSx RINV R cx Hp t op W' c') \/ INV_P_xR cx Hp t W' c').
Proof.
  intros cx Hp t W c HB (regs & mem & md & -> & HROM &
    (own & ly3 & S3 & Hp3 & k & m & fpos & HJ & -> & HFR & HFL & HMOD & HIN & HRV & HSEP & HLS & HNP & HRI & HR)).
  destruct HR as ((R2 & R8 & R9 & R18 & R19 & R20 & R23 & R24 & R25 & R26 & R3 & R4) & R6 & R7 & R21 & R22 & R27 & Ht & Hk).
  pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  pose proof HB as (HAI & HPRE & Hra & Ha0 & Ha1 & Hblk0 & Hlen & _).
  pose proof HPRE as (HAR0 & Hra0 & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
  pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
  assert (HAR : ARx ly3 S3 Hp3 W mem md) by (eapply ajournal_gx_AR_xR; exact HJ).
  pose proof HIN as [[[Hn00 _] | [Hnr Hblk]] Hgarr]; [lia|].
  destruct (alx_blocks _ _ _ LAWS _ _ _ _ _ _ _ _ HAR Hblk) as (Hp16 & Hp4096 & Hpceil & Hpia & _ & _).
  pose proof (hd_blk_imgP_x _ _ _ _ _ _ _ _ HAR Hblk ltac:(lia)) as Hpimg.
  pose proof (req_size_pos (c_n cx) ltac:(lia)) as [_ Hreq].
  pose proof (Z.mod_pos_bound (spZ (c_regs cx) - 320) 32 ltac:(lia)) as HFm.
  assert (HFb : spZ (c_regs cx) - 351 <= lf_F cx <= spZ (c_regs cx) - 320) by (unfold lf_F; lia).
  unfold LLVMF_STK in *.
  destruct (hd_in_byte cx (arm W mem) (lm_k m) Hgarr ltac:(lia)) as [MB Rb0].
  pose proof HFR as (FS & FW & F24 & F48 & F56 & F64 & F72 & F80 & F88 & F96 & F184 & Ffull & FF0 & FF8 & FF16 & FFw & FFsh & FFshw).
  destruct (Ffull eq_refl) as (F32 & F104 & F112 & F120 & F128 & F136 & F152).
  pose proof HMOD as (Hhs4 & Hslots & Hrel & Hout & Hgone & Hlock & Hwake & Hnfd & Hnfdw & Hnfdr).
  pose proof Hout as (O1 & O2 & O3 & O4 & _).
  destruct (hd_entry1 W regs mem (c_p cx + lm_k m) (lf_F cx) (in_byte cx (lm_k m)) R6 R7 R20 R9 R22 R25 R26
    ltac:(lia) Rb0 ltac:(lia) ltac:(lia) MB F136 O4 ltac:(lia)
    ltac:(cbn; lia) ltac:(cbn; lia)
    ltac:(apply (range_addressable_of_block_hp0_x segs B ARx LAWS HP0 ly3 S3 Hp3 W mem md (c_p cx) (c_n cx)); [exact HAR | exact Hblk | lia | lia])
    ltac:(unfold in_app, SHADOW_OFF, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *; lia)) as [HS SHOK].
  remember (Eimg (Ereg regs (hd_x1 (in_byte cx (lm_k m))))) as E eqn:HE.
  assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
  assert (EEo : forall m (rr : bv 5), Z.of_nat m = bv_unsigned rr -> ew E m = getr regs rr)
    by (intros m0 rr Hm; subst E; pose proof (bv_unsigned_in_range 5 rr) as Hr5; change (bv_modulus 5) with 32 in Hr5;
        rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_nat; exact Hm).
  assert (E21 : ew E 21 = Z_to_bv 64 (c_n cx - lm_k m)) by (rewrite (EEo 21%nat 21%bv eq_refl); exact R21).
  assert (E22 : ew E 22 = Z_to_bv 64 (c_p cx + lm_k m)) by (rewrite (EEo 22%nat 22%bv eq_refl); exact R22).
  assert (E25 : ew E 25 = Z_to_bv 64 HI_G_NOUT) by (rewrite (EEo 25%nat 25%bv eq_refl); exact R25).
  assert (E32 : ew E 32 = Z_to_bv 64 (in_byte cx (lm_k m)))
    by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
  assert (HAE : env_agree 32 (Ereg regs (hd_x1 (in_byte cx (lm_k m)))) E)
    by (rewrite HE; split; [intros m0 Hm; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
  clear HE.
  pose proof HJ as HJ0.
  pose proof (Z.mod_pos_bound (in_byte cx (lm_k m)) 10 ltac:(lia)) as Rop.
  assert (UOP : forall Ev, ew Ev 32 = ew E 32 -> U Ev hd_opsv = in_byte cx (lm_k m) mod 10)
    by (intros Ev HEv; apply hd_op_U; [rewrite HEv; exact E32 | exact Rb0]).
  unfold cfg_at. change (w64 (fr_B0 + AF_LLVM_head)) with (Z_to_bv 64 (BASE + AF_LLVM_head)).
  (* the shadow check of in.p[0], its read, op = in.p[0] % 10, g_nout = 0, to the class test *)
  paj_run_tok_x RUN HS HJ SHOK hd_Bspan.
  { hd_awr E25 HGnout. }
  lazymatch goal with HFx : frame_of _ _ (mrestrict _ mem) (mrestrict _ (ms_mem ?ms1)) |- _ =>
    assert (MEQ1 : forall x : word, ~ (rg_nout fr_RG <= bv_unsigned x < rg_nout fr_RG + 8) ->
        mrestrict (w_H W) (ms_mem ms1) x = mrestrict (w_H W) mem x)
      by (apply (hd_frame_nout E (ss_mem hd_ss1)); [exact HFx | hd_wr E25]) end.
  lazymatch goal with H : mem_grows (mrestrict _ mem) _ |- _ => rename H into MG1 end.
  rename MEQ1 into MEQ. rename MG1 into MG.
  repeat match goal with H : frame_of _ _ _ _ |- _ => clear H end.
  lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
    assert (UO : U Ev hd_opsv = in_byte cx (lm_k m) mod 10) by (apply UOP; rewrite !ew_ewset_other by lia; reflexivity);
    assert (HAE1 : env_agree 32 (Ereg regs (hd_x1 (in_byte cx (lm_k m)))) Ev)
      by (split; [intros m0 Hm; rewrite !ew_ewset_other by lia; exact (proj1 HAE m0 Hm) | rewrite !ed_ewset; exact (proj2 HAE)])
  end.
  psrr_branch_tok RUN BR HS SHOK hd_Bspan.
  - (* op in 1..4: on to the pick *)
    unfold hd_opsv in UO. rewrite branch_ltu_U, U_SAlu, UO, hd_cls_ltu in Hc by lia.
    apply andb_prop in Hc as [Hc1 Hc2]. apply Z.leb_le in Hc1, Hc2. fold hd_opsv in UO.
    paj_run_to_tok_x RUNTO HS HJ SHOK hd_Bspan AF_LLVM_pick.
    { hd_awr E25 HGnout. }
    hd_upd E25 MEQ MG.
    pose proof (regs_kept_of_st_ok_pi _ _ _ regs _ HD_KEPT1 HS HAE1 ltac:(vm_compute; reflexivity)) as KR.
    cbn [ms_regs restrict] in KR.
    prreg HS (6%bv : bv 5) Q6. prreg HS (7%bv : bv 5) Q7. prreg HS (20%bv : bv 5) Q20.
    prreg_raw HS (11%bv : bv 5) Q11.
    prreg HS (21%bv : bv 5) Q21. prreg HS (28%bv : bv 5) Q28. prreg HS (29%bv : bv 5) Q29.
    hd_nout0 HS E25 HN0.
    pmkst HS.
    apply SRr_ret. right.
    lazymatch goal with |- INV_P_xR _ _ _ _ {| cfg_ms := mkst ?r _ ?mm _; cfg_model := ?d |} => exists r, mm, d end.
    split; [reflexivity|].
    apply (hd_w1_lcut_xR cx Hp t W mem md _ _ ly3 S3 Hp3 k m fpos (lregs_P B cx t) _ HB HJ0 HJ MEQ MG HN0 HFR HFL HMOD HIN HRV HSEP HLS HNP HRI HROM).
    unfold lregs_P. cbn [lm_k lm_O lm_clear_O].
    rewrite ?ew_ewset_other in Q21, Q28, Q29 by lia.
    rewrite E21 in Q21, Q29. rewrite E22 in Q28. rewrite ?unsigned_lit_small in Q21 by lia. rewrite ?unsigned_lit_small in Q28 by lia. rewrite ?unsigned_lit_small in Q29 by lia.
    split; [repeat split; first [rewrite (KR 2%bv ltac:(cbv; tauto)); assumption | rewrite (KR 8%bv ltac:(cbv; tauto)); assumption
      | rewrite (KR 9%bv ltac:(cbv; tauto)); assumption | rewrite (KR 18%bv ltac:(cbv; tauto)); assumption
      | rewrite (KR 19%bv ltac:(cbv; tauto)); assumption | rewrite Q20; reflexivity
      | rewrite (KR 23%bv ltac:(cbv; tauto)); assumption | rewrite (KR 24%bv ltac:(cbv; tauto)); assumption
      | rewrite (KR 25%bv ltac:(cbv; tauto)); assumption | rewrite (KR 26%bv ltac:(cbv; tauto)); assumption
      | rewrite (KR 3%bv ltac:(cbv; tauto)); assumption | rewrite (KR 4%bv ltac:(cbv; tauto)); assumption]|].
    split; [rewrite Q6; reflexivity|]. split; [rewrite Q7; reflexivity|].
    split; [rewrite (KR 27%bv ltac:(cbv; tauto)); exact R27|].
    split; [exact Ht|]. split; [exact Hk|]. split; [reflexivity|].
    split; [rewrite Q21; unfold w64; f_equal; lia|].
    split; [rewrite (KR 22%bv ltac:(cbv; tauto)); exact R22|].
    split; [rewrite Q11; apply hd_sv_of_U; [exact UO | lia]|].
    split; [apply hd_picks14; exact (conj Hc1 Hc2)|].
    split; [rewrite Q28; unfold w64; f_equal; lia|].
    rewrite Q29; unfold w64; f_equal; lia.
  - unfold hd_opsv in UO. rewrite branch_ltu_U, U_SAlu, UO, hd_cls_ltu in Hc by lia. fold hd_opsv in UO.
    rename Hc into Hcls.
    paj_run_tok_x RUN HS HJ SHOK hd_Bspan.
    { hd_awr E25 HGnout. }
    hd_upd E25 MEQ MG.
    lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
      assert (UO2 : U Ev hd_opsv = in_byte cx (lm_k m) mod 10) by (apply UOP; rewrite ?ew_ewset_other by lia; reflexivity);
      assert (HAE2 : env_agree 32 (Ereg regs (hd_x1 (in_byte cx (lm_k m)))) Ev)
        by (split; [intros m0 Hm; rewrite ?ew_ewset_other by lia; exact (proj1 HAE m0 Hm) | rewrite ?ed_ewset; exact (proj2 HAE)])
    end.
    clear UO HAE1. rename UO2 into UO. rename HAE2 into HAE1.
    psrr_branch_tok RUN BR HS SHOK hd_Bspan.
    + (* op not in 1..4, op <> 6: no source; to the dispatch *)
      unfold hd_opsv in UO. rewrite branch_ne_U, UO, U_lit in Hc by lia. fold hd_opsv in UO.
      apply negb_true_iff, Z.eqb_neq in Hc.
      pose proof (hd_picks_no (in_byte cx (lm_k m) mod 10) ltac:(lia) Hcls Hc) as Hpk.
      paj_run_to_tok_x RUNTO HS HJ SHOK hd_Bspan AF_LLVM_dispatch.
      { hd_awr E25 HGnout. }
      hd_upd E25 MEQ MG.
      pose proof (regs_kept_of_st_ok_pi _ _ _ regs _ HD_KEPT1 HS HAE1 ltac:(vm_compute; reflexivity)) as KR.
      cbn [ms_regs restrict] in KR.
      prreg HS (6%bv : bv 5) Q6. prreg HS (7%bv : bv 5) Q7. prreg HS (20%bv : bv 5) Q20.
      prreg_raw HS (11%bv : bv 5) Q11.
      prreg HS (21%bv : bv 5) Q21. prreg HS (28%bv : bv 5) Q28. prreg HS (29%bv : bv 5) Q29.
      hd_nout0 HS E25 HN0.
      pmkst HS.
      apply SRr_ret. left. exists (in_byte cx (lm_k m) mod 10). split; [lia|].
      lazymatch goal with |- INV_D_xR _ _ _ _ _ _ _ _ _ _ _ _ _ _ {| cfg_ms := mkst ?r _ ?mm _; cfg_model := ?d |} => exists r, mm, d end.
      split; [reflexivity|].
      split; [rewrite Q11; apply hd_sv_of_U; [exact UO | lia]|].
      rewrite ?wvb_collapse in HJ.
      split; [exists [(1, fpos)], ly3, S3, Hp3, k; exact HJ|].
      apply (hd_w1_lcut_xR cx Hp t W mem md _ _ ly3 S3 Hp3 k m fpos (lregs_D B cx t) _ HB HJ0 HJ MEQ MG HN0 HFR HFL HMOD HIN HRV HSEP HLS HNP HRI HROM).
      unfold lregs_D. cbv zeta. cbn [lm_k lm_O lm_clear_O]. rewrite Hpk. cbv iota.
      rewrite ?ew_ewset_other in Q28, Q29 by lia.
      rewrite E21 in Q29. rewrite E22 in Q28. rewrite ?unsigned_lit_small in Q28 by lia. rewrite ?unsigned_lit_small in Q29 by lia.
      split; [repeat split; first [rewrite (KR 2%bv ltac:(cbv; tauto)); assumption | rewrite (KR 8%bv ltac:(cbv; tauto)); assumption
        | rewrite (KR 9%bv ltac:(cbv; tauto)); assumption | rewrite (KR 18%bv ltac:(cbv; tauto)); assumption
        | rewrite (KR 19%bv ltac:(cbv; tauto)); assumption | rewrite Q20; reflexivity
        | rewrite (KR 23%bv ltac:(cbv; tauto)); assumption | rewrite (KR 24%bv ltac:(cbv; tauto)); assumption
        | rewrite (KR 25%bv ltac:(cbv; tauto)); assumption | rewrite (KR 26%bv ltac:(cbv; tauto)); assumption
        | rewrite (KR 3%bv ltac:(cbv; tauto)); assumption | rewrite (KR 4%bv ltac:(cbv; tauto)); assumption]|].
      split; [rewrite Q6; reflexivity|]. split; [rewrite Q7; reflexivity|].
      split; [rewrite (KR 27%bv ltac:(cbv; tauto)); exact R27|].
      split; [exact Ht|]. split; [exact Hk|]. split; [reflexivity|].
      split; [rewrite Q11; apply hd_sv_of_U; [exact UO | lia]|].
      split; [rewrite Q28; unfold w64; f_equal; lia|].
      split; [rewrite Q29; unfold w64; f_equal; lia|].
      rewrite Q21. reflexivity.
    + (* op = 6: on to the pick *)
      unfold hd_opsv in UO. rewrite branch_ne_U, UO, U_lit in Hc by lia. fold hd_opsv in UO.
      apply negb_false_iff, Z.eqb_eq in Hc.
      paj_run_to_tok_x RUNTO HS HJ SHOK hd_Bspan AF_LLVM_pick.
      { hd_awr E25 HGnout. }
      hd_upd E25 MEQ MG.
      pose proof (regs_kept_of_st_ok_pi _ _ _ regs _ HD_KEPT1 HS HAE1 ltac:(vm_compute; reflexivity)) as KR.
        cbn [ms_regs restrict] in KR.
        prreg HS (6%bv : bv 5) Q6. prreg HS (7%bv : bv 5) Q7. prreg HS (20%bv : bv 5) Q20.
        prreg_raw HS (11%bv : bv 5) Q11.
        prreg HS (21%bv : bv 5) Q21. prreg HS (28%bv : bv 5) Q28. prreg HS (29%bv : bv 5) Q29.
        hd_nout0 HS E25 HN0.
        pmkst HS.
        apply SRr_ret. right.
        lazymatch goal with |- INV_P_xR _ _ _ _ {| cfg_ms := mkst ?r _ ?mm _; cfg_model := ?d |} => exists r, mm, d end.
        split; [reflexivity|].
        apply (hd_w1_lcut_xR cx Hp t W mem md _ _ ly3 S3 Hp3 k m fpos (lregs_P B cx t) _ HB HJ0 HJ MEQ MG HN0 HFR HFL HMOD HIN HRV HSEP HLS HNP HRI HROM).
        unfold lregs_P. cbn [lm_k lm_O lm_clear_O].
        rewrite ?ew_ewset_other in Q21, Q28, Q29 by lia.
        rewrite E21 in Q21, Q29. rewrite E22 in Q28. rewrite ?unsigned_lit_small in Q21 by lia. rewrite ?unsigned_lit_small in Q28 by lia. rewrite ?unsigned_lit_small in Q29 by lia.
        split; [repeat split; first [rewrite (KR 2%bv ltac:(cbv; tauto)); assumption | rewrite (KR 8%bv ltac:(cbv; tauto)); assumption
          | rewrite (KR 9%bv ltac:(cbv; tauto)); assumption | rewrite (KR 18%bv ltac:(cbv; tauto)); assumption
          | rewrite (KR 19%bv ltac:(cbv; tauto)); assumption | rewrite Q20; reflexivity
          | rewrite (KR 23%bv ltac:(cbv; tauto)); assumption | rewrite (KR 24%bv ltac:(cbv; tauto)); assumption
          | rewrite (KR 25%bv ltac:(cbv; tauto)); assumption | rewrite (KR 26%bv ltac:(cbv; tauto)); assumption
          | rewrite (KR 3%bv ltac:(cbv; tauto)); assumption | rewrite (KR 4%bv ltac:(cbv; tauto)); assumption]|].
        split; [rewrite Q6; reflexivity|]. split; [rewrite Q7; reflexivity|].
        split; [rewrite (KR 27%bv ltac:(cbv; tauto)); exact R27|].
        split; [exact Ht|]. split; [exact Hk|]. split; [reflexivity|].
        split; [rewrite Q21; unfold w64; f_equal; lia|].
        split; [rewrite (KR 22%bv ltac:(cbv; tauto)); exact R22|].
        split; [rewrite Q11; apply hd_sv_of_U; [exact UO | lia]|].
        split; [rewrite Hc; reflexivity|].
        split; [rewrite Q28; unfold w64; f_equal; lia|].
        rewrite Q29; unfold w64; f_equal; lia.
Qed.

(* ------------------------------------------------------------------ walk 2: the pick (0x842e0 .. the dispatch) *)
Lemma hd_gs_shadow_x : forall ly S Hp W mem md, ARx ly S Hp W mem md ->
  forall j, 0 <= j < 4 -> val_mem segs (mrestrict (w_H W) mem) (hd_shgs + 12 * j) 1 0.
Proof.
  intros ly S Hp W mem md HAR j Hj. destruct HZS as ([lo len] & Hin & H8 & Hlo & Hhi). cbn [fst snd] in *.
  assert (Hz : zero_shadow (aview segs (w_H W) mem) SHADOW_OFF lo len).
  { apply (alx_zshadow _ _ _ LAWS ly S Hp W mem md (lo, len) HAR). unfold zero_shadow_ranges. right. exact Hin. }
  change (rg_s fr_RG) with 6129888 in *. unfold ASRC in Hhi.
  pose proof (Z.div_mod lo 8 ltac:(lia)) as Dl. rewrite H8, Z.add_0_r in Dl.
  pose proof (Z.mul_div_le len 8 ltac:(lia)) as Dn.
  specialize (Hz (766236 - lo / 8 + 12 * j) ltac:(split; [lia | lia])).
  apply hd_vm0_of_aview. rewrite hd_shgs_val.
  replace (2148217116 + 12 * j) with (shadow_of_addr SHADOW_OFF lo + (766236 - lo / 8 + 12 * j))
    by (unfold shadow_of_addr, SHADOW_OFF; lia).
  exact Hz.
Qed.

(* after a run with no writable window: the memory is the one walk 2 began with *)
Ltac hd_meq mem0 :=
  lazymatch goal with HFx : frame_of _ ?rs ?m0 (ms_mem ?ms1) |- _ =>
    let Hm := fresh "HMm" in
    assert (Hm : ms_mem ms1 = mem0) by
      (apply functional_extensionality; let x := fresh "x" in intros x; rewrite HFx;
       [ first [ reflexivity | match goal with Hp : ms_mem _ = mem0 |- _ => rewrite Hp; reflexivity end ]
       | let r := fresh "r" in let Hin := fresh "Hin" in let Hr := fresh "Hr" in
         intros (r & Hin & Hr); vm_compute in Hin;
         repeat (destruct Hin as [<- | Hin]; [cbn [YP09.r_base YP09.r_wlo YP09.r_whi] in Hr; lia |]); destruct Hin ]);
    clear HFx;
    repeat match goal with Ho : ms_mem _ = mem0 |- _ => lazymatch Ho with Hm => fail | _ => clear Ho end end;
    try rename Hm into HMm end;
  repeat match goal with H : frame_of _ _ _ _ |- _ => clear H | H : mem_grows _ _ |- _ => clear H end.
Ltac hd_awr0 :=
  lazymatch goal with |- awr_ok_x ?Ev ?rs ?G ?XO ?OUT ?STK ?sp0 ?FP ?b0 ?bc ?ly ?own =>
    let rs' := eval vm_compute in rs in change (awr_ok_x Ev rs' G XO OUT STK sp0 FP b0 bc ly own) end;
  repeat first
   [ apply awr_ok_x_nil
   | apply awr_ok_x_cons; [let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha;
       cbn [YP09.r_base YP09.r_wlo YP09.r_whi YP09.base_val] in Ha; lia |] ].
Ltac hd_cmn KR :=
  repeat split; first [rewrite (KR 2%bv ltac:(cbv; tauto)); assumption | rewrite (KR 8%bv ltac:(cbv; tauto)); assumption
    | rewrite (KR 9%bv ltac:(cbv; tauto)); assumption | rewrite (KR 18%bv ltac:(cbv; tauto)); assumption
    | rewrite (KR 19%bv ltac:(cbv; tauto)); assumption
    | rewrite (KR 23%bv ltac:(cbv; tauto)); assumption | rewrite (KR 24%bv ltac:(cbv; tauto)); assumption
    | rewrite (KR 25%bv ltac:(cbv; tauto)); assumption | rewrite (KR 26%bv ltac:(cbv; tauto)); assumption
    | rewrite (KR 3%bv ltac:(cbv; tauto)); assumption | rewrite (KR 4%bv ltac:(cbv; tauto)); assumption].

Lemma hd_w2_xR : forall cx Hp t W c, lf_base_x B MT XM_LIB RLO RHI fr_live_pre LIBROOM NP G_fr ARx cx Hp -> INV_P_xR cx Hp t W c ->
  SRr segs W c (fun W' c' => (exists op, 0 <= op <= 9 /\ INV_D_xR B NP G_fr fr_FP PST ARx LSx RINV R cx Hp t op W' c') \/
    INV_A_xR B NP G_fr fr_FP PST ARx LSx RINV R 1 cx Hp t W' c' \/ INV_H_xR B NP G_fr fr_FP PST ARx LSx RINV R cx Hp (t + 1) W' c' \/
    INV_X_xR B NP G_fr fr_FP PST ARx LSx RINV R cx Hp W' c').
Proof.
  intros cx Hp t W c HB (regs & mem & md & -> & HROM &
    (own & ly3 & S3 & Hp3 & k & m & fpos & HJ & -> & HFR & HFL & HMOD & HIN & HRV & HSEP & HLS & HNP & HRI & HR)).
  destruct HR as ((R2 & R8 & R9 & R18 & R19 & R20 & R23 & R24 & R25 & R26 & R3 & R4) & R6 & R7 & R27 & Ht & Hk & HO &
    R21 & R22 & R11 & Hpk & R28 & R29).
  pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  pose proof HB as (HAI & HPRE & Hra & Ha0 & Ha1 & Hblk0 & Hlen & _).
  pose proof HPRE as (HAR0 & Hra0 & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
  pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
  assert (HAR : ARx ly3 S3 Hp3 W mem md) by (eapply ajournal_gx_AR_xR; exact HJ).
  pose proof HIN as [[[Hn00 _] | [Hnr Hblk]] Hgarr]; [lia|].
  destruct (alx_blocks _ _ _ LAWS _ _ _ _ _ _ _ _ HAR Hblk) as (Hp16 & Hp4096 & Hpceil & Hpia & _ & _).
  pose proof (hd_blk_imgP_x _ _ _ _ _ _ _ _ HAR Hblk ltac:(lia)) as Hpimg.
  pose proof (req_size_pos (c_n cx) ltac:(lia)) as [_ Hreq].
  pose proof (Z.mod_pos_bound (spZ (c_regs cx) - 320) 32 ltac:(lia)) as HFm.
  assert (HFb : spZ (c_regs cx) - 351 <= lf_F cx <= spZ (c_regs cx) - 320) by (unfold lf_F; lia).
  unfold LLVMF_STK in *.
  pose proof HFR as (FS & FW & F24 & F48 & F56 & F64 & F72 & F80 & F88 & F96 & F184 & Ffull & _).
  destruct (Ffull eq_refl) as (F32 & F104 & F112 & F120 & F128 & F136 & F152).
  pose proof HMOD as (Hhs4 & Hslots & _).
  destruct (hd_in_byte cx (arm W mem) (lm_k m) Hgarr ltac:(lia)) as [MB0 Rb0].
  pose proof (Z.mod_pos_bound (in_byte cx (lm_k m)) 10 ltac:(lia)) as Rop.
  pose proof Ht as Ht'. unfold OPS_MAX in Ht'.
  assert (Hkb : 0 <= hd_kb cx m < 256).
  { unfold hd_kb. destruct (lm_k m + 1 <? c_n cx) eqn:Hm1; [|lia].
    apply Z.ltb_lt in Hm1. exact (proj2 (hd_in_byte cx (arm W mem) (lm_k m + 1) Hgarr ltac:(lia))). }
  assert (MB1 : (lm_k m + 1 <? c_n cx) = true ->
      val_mem segs (mrestrict (w_H W) mem) (c_p cx + lm_k m + 1) 1 (hd_kb cx m)).
  { intros Hm1. unfold hd_kb. rewrite Hm1. apply Z.ltb_lt in Hm1. rewrite <- Z.add_assoc.
    exact (proj1 (hd_in_byte cx (arm W mem) (lm_k m + 1) Hgarr ltac:(lia))). }
  assert (RA1 : (lm_k m + 1 <? c_n cx) = true ->
      range_addressable (aview segs (w_H W) mem) SHADOW_OFF (c_p cx + lm_k m + 1) 1).
  { intros Hm1. apply Z.ltb_lt in Hm1.
    apply (range_addressable_of_block_hp0_x segs B ARx LAWS HP0 ly3 S3 Hp3 W mem md (c_p cx) (c_n cx)); [exact HAR | exact Hblk | lia | lia]. }
  pose proof (hd_gs_shadow_x ly3 S3 Hp3 W mem md HAR) as SH0.
  pose proof (hd_open_val B ly3 S3 W mem 0 _ (Hslots 0%nat ltac:(lia))) as G0.
  pose proof (hd_open_val B ly3 S3 W mem 1 _ (Hslots 1%nat ltac:(lia))) as G1.
  pose proof (hd_open_val B ly3 S3 W mem 2 _ (Hslots 2%nat ltac:(lia))) as G2.
  pose proof (hd_open_val B ly3 S3 W mem 3 _ (Hslots 3%nat ltac:(lia))) as G3.
  pose proof Hhs4 as Hl4.
  destruct (lm_hs m) as [|o0 [|o1 [|o2 [|o3 [|o4 rest]]]]] eqn:Hhs; cbn [length] in Hl4; try discriminate Hl4.
  rewrite ?Hhs in G0, G1, G2, G3. cbn [nth] in G0, G1, G2, G3.
  destruct (hd_entry2 W regs mem (lm_k m + 1 <? c_n cx) (isS o0) (isS o1) (isS o2) (isS o3) (c_p cx + lm_k m + 1)
    (lf_F cx) (hd_kb cx m) R6 R7 R20 R9 R26 R28 ltac:(lia) Hkb ltac:(lia) ltac:(lia)
    ltac:(intros Hm1; apply Z.ltb_lt in Hm1; lia)
    ltac:(intros Hm1; apply Z.ltb_lt in Hm1; unfold in_app in Hpia; unfold kLowShadowBeg, kHighMemBeg in *; lia)
    ltac:(intros Hm1; apply Z.ltb_lt in Hm1; lia)
    MB1 RA1 F128 F152 G0 G1 G2 G3 SH0) as [HS SHOK].
  remember (Eimg (Ereg regs (hd_x1 (hd_kb cx m)))) as E eqn:HE.
  assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
  assert (EEo : forall m (rr : bv 5), Z.of_nat m = bv_unsigned rr -> ew E m = getr regs rr)
    by (intros m0 rr Hm; subst E; pose proof (bv_unsigned_in_range 5 rr) as Hr5; change (bv_modulus 5) with 32 in Hr5;
        rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_nat; exact Hm).
  assert (E11 : ew E 11 = Z_to_bv 64 (in_byte cx (lm_k m) mod 10)) by (rewrite (EEo 11%nat 11%bv eq_refl); exact R11).
  assert (E21 : ew E 21 = Z_to_bv 64 (c_n cx - lm_k m)) by (rewrite (EEo 21%nat 21%bv eq_refl); exact R21).
  assert (E22 : ew E 22 = Z_to_bv 64 (c_p cx + lm_k m)) by (rewrite (EEo 22%nat 22%bv eq_refl); exact R22).
  assert (E25 : ew E 25 = Z_to_bv 64 HI_G_NOUT) by (rewrite (EEo 25%nat 25%bv eq_refl); exact R25).
  assert (E27 : ew E 27 = Z_to_bv 64 t) by (rewrite (EEo 27%nat 27%bv eq_refl); exact R27).
  assert (E28 : ew E 28 = Z_to_bv 64 (c_p cx + lm_k m + 1)) by (rewrite (EEo 28%nat 28%bv eq_refl); exact R28).
  assert (E29 : ew E 29 = Z_to_bv 64 (c_n cx - lm_k m - 1)) by (rewrite (EEo 29%nat 29%bv eq_refl); exact R29).
  assert (E32 : ew E 32 = Z_to_bv 64 (hd_kb cx m))
    by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
  assert (UG : bv_unsigned (ew E 263) = rg_s fr_RG).
  { subst E. rewrite Eimg_img by (unfold A_TEXT, A_LIM; lia). change 263%nat with (A_OBJ 22). rewrite (hd_VAL_gs (rc := rc)).
    apply unsigned_lit_small. cbn; lia. }
  assert (HAE : env_agree 32 (Ereg regs (hd_x1 (hd_kb cx m))) E)
    by (rewrite HE; split; [intros m0 Hm; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
  clear HE.
  assert (EG' : ew E 263 = Z_to_bv 64 (rg_s fr_RG)) by (rewrite <- UG; symmetry; apply Z_to_bv_bv_unsigned).
  assert (Hnone : (lm_hs m = [None; None; None; None]) -> pick (lm_hs m) (hd_kb cx m) = None)
    by (intros Hn; unfold pick, nopen; rewrite Hn; reflexivity).
  unfold cfg_at. change (w64 (fr_B0 + AF_LLVM_pick)) with (Z_to_bv 64 (BASE + AF_LLVM_pick)).
  revert HS SHOK. destruct (lm_k m + 1 <? c_n cx) eqn:Hmore; intros HS SHOK.
  all: destruct o0 as [h0|]; destruct o1 as [h1|]; destruct o2 as [h2|]; destruct o3 as [h3|].
  all: cbn [isS] in HS; norm_ss HS; cbn [hd_SH2] in SHOK.
  (* the test of in.n - 1 (t4): the side that contradicts `more` is refuted *)
  all: psrr_branch_tok RUN BR HS SHOK hd_Bspan.
  all: rewrite branch_eq_U, (U_atom E 29 (c_n cx - lm_k m - 1) E29), U_lit in Hc by lia.
  all: try (exfalso; first [apply Z.eqb_eq in Hc | apply Z.eqb_neq in Hc];
    first [apply Z.ltb_lt in Hmore | apply Z.ltb_ge in Hmore]; lia).
  all: clear Hc.
  (* the second byte (when in.n > 1), the open count, to the remainder (or, with no open source, to the test op == 1) *)
  all: paj_run_to_tok_x RUNTO HS HJ SHOK hd_Bspan 8304.
  all: try hd_awr0.
  all: hd_meq mem.
  32:
  { psrr_branch_tok RUN BR HS SHOK hd_Bspan.
    - (* op <> 1: `continue`, to the loop test 0x844a0 *)
      lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
        rewrite branch_ne_U, (U_atom_off Ev 11 _ 0 ltac:(rewrite ?ew_ewset_other by lia; exact E11) ltac:(lia) ltac:(lia)), U_lit in Hc by lia end.
      rewrite Z.add_0_r in Hc. apply negb_true_iff, Z.eqb_neq in Hc. rename Hc into Hop1.
      paj_run_tok_x RUN HS HJ SHOK hd_Bspan. { hd_awr0. } hd_meq mem.
      psrr_branch_tok RUN BR HS SHOK hd_Bspan.
      + (* ops > 510: the loop ends *)
        lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
          rewrite branch_ltu_U, U_lit, (U_atom_off Ev 27 _ 0 ltac:(rewrite ?ew_ewset_other by lia; exact E27) ltac:(lia) ltac:(lia)) in Hc by lia end.
        paj_run_to_tok_x RUNTO HS HJ SHOK hd_Bspan AF_LLVM_exit. { hd_awr0. } hd_meq mem.
        lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
        assert (HAEv : env_agree 32 (Ereg regs (hd_x1 (hd_kb cx m))) Ev)
          by (split; [intros m0 Hm; rewrite ?ew_ewset_other by lia; exact (proj1 HAE m0 Hm) | rewrite ?ed_ewset; exact (proj2 HAE)]) end.
        pose proof (regs_kept_of_st_ok_pi _ _ _ regs _ HD_KEPT3 HS HAEv ltac:(vm_compute; reflexivity)) as KR.
        cbn [ms_regs restrict] in KR.
        pmkst HS. rewrite HMm. rewrite HMm in HJ.
        apply SRr_ret. right; right; right.
        lazymatch goal with |- INV_X_xR _ _ _ _ _ _ _ _ _ _ _ _ {| cfg_ms := mkst ?r _ ?mm _; cfg_model := ?d |} => exists r, mm, d, (t + 1) end.
        split; [reflexivity|]. split; [exact HROM|].
        exists [(1, fpos)], ly3, S3, Hp3, k, (lm_set_k m (hd_k' cx m)), fpos.
        split; [exact HJ|]. split; [reflexivity|]. split; [apply hd_aframe_false; exact HFR|]. split; [exact HFL|].
        split; [exact HMOD|]. split; [exact HIN|]. split; [exact HRV|]. split; [exact HSEP|].
        split; [apply LS_head_skip; [exact Ht | exact Hk | exact HO | exact Hpk | exact Hop1 | apply Hnone; exact Hhs |]; exact HLS|]. split; [exact HNP|].
        split; [apply RI_head_skip; [exact Ht | exact Hk | exact HO | exact Hpk | exact Hop1 | apply Hnone; exact Hhs |]; exact HRI|].
        cbv beta. unfold lregs_X. cbn [lm_k lm_set_k]. unfold hd_k'. rewrite Hmore. cbv iota.
        repeat split; first [rewrite (KR 2%bv ltac:(cbv; tauto)); assumption | rewrite (KR 8%bv ltac:(cbv; tauto)); assumption
          | rewrite (KR 9%bv ltac:(cbv; tauto)); assumption | rewrite (KR 18%bv ltac:(cbv; tauto)); assumption
          | rewrite (KR 23%bv ltac:(cbv; tauto)); assumption
          | rewrite (KR 25%bv ltac:(cbv; tauto)); assumption | rewrite (KR 26%bv ltac:(cbv; tauto)); assumption
          | rewrite (KR 3%bv ltac:(cbv; tauto)); assumption | rewrite (KR 4%bv ltac:(cbv; tauto)); assumption
          | (apply Z.ltb_lt in Hmore || apply Z.ltb_ge in Hmore); lia ].
      + lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
          rewrite branch_ltu_U, U_lit, (U_atom_off Ev 27 _ 0 ltac:(rewrite ?ew_ewset_other by lia; exact E27) ltac:(lia) ltac:(lia)) in Hc by lia end.
        rewrite Z.add_0_r in Hc. apply Z.ltb_ge in Hc. rename Hc into Ht510.
        paj_run_to_tok_x RUNTO HS HJ SHOK hd_Bspan AF_LLVM_exit. { hd_awr0. } hd_meq mem.
        lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
        assert (HAEv : env_agree 32 (Ereg regs (hd_x1 (hd_kb cx m))) Ev)
          by (split; [intros m0 Hm; rewrite ?ew_ewset_other by lia; exact (proj1 HAE m0 Hm) | rewrite ?ed_ewset; exact (proj2 HAE)]) end.
        pose proof (regs_kept_of_st_ok_pi _ _ _ regs _ HD_KEPT3 HS HAEv ltac:(vm_compute; reflexivity)) as KR.
        cbn [ms_regs restrict] in KR.
        pmkst HS. rewrite HMm. rewrite HMm in HJ.
        apply SRr_ret. right; right; right.
        lazymatch goal with |- INV_X_xR _ _ _ _ _ _ _ _ _ _ _ _ {| cfg_ms := mkst ?r _ ?mm _; cfg_model := ?d |} => exists r, mm, d, (t + 1) end.
        split; [reflexivity|]. split; [exact HROM|].
        exists [(1, fpos)], ly3, S3, Hp3, k, (lm_set_k m (hd_k' cx m)), fpos.
        split; [exact HJ|]. split; [reflexivity|]. split; [apply hd_aframe_false; exact HFR|]. split; [exact HFL|].
        split; [exact HMOD|]. split; [exact HIN|]. split; [exact HRV|]. split; [exact HSEP|].
        split; [apply LS_head_skip; [exact Ht | exact Hk | exact HO | exact Hpk | exact Hop1 | apply Hnone; exact Hhs |]; exact HLS|]. split; [exact HNP|].
        split; [apply RI_head_skip; [exact Ht | exact Hk | exact HO | exact Hpk | exact Hop1 | apply Hnone; exact Hhs |]; exact HRI|].
        cbv beta. unfold lregs_X. cbn [lm_k lm_set_k]. unfold hd_k'. rewrite Hmore. cbv iota.
        repeat split; first [rewrite (KR 2%bv ltac:(cbv; tauto)); assumption | rewrite (KR 8%bv ltac:(cbv; tauto)); assumption
          | rewrite (KR 9%bv ltac:(cbv; tauto)); assumption | rewrite (KR 18%bv ltac:(cbv; tauto)); assumption
          | rewrite (KR 23%bv ltac:(cbv; tauto)); assumption
          | rewrite (KR 25%bv ltac:(cbv; tauto)); assumption | rewrite (KR 26%bv ltac:(cbv; tauto)); assumption
          | rewrite (KR 3%bv ltac:(cbv; tauto)); assumption | rewrite (KR 4%bv ltac:(cbv; tauto)); assumption
          | (apply Z.ltb_lt in Hmore || apply Z.ltb_ge in Hmore); lia ].
    - (* op = 1 with no open source: arm 1 with s = NULL *)
      lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
        rewrite branch_ne_U, (U_atom_off Ev 11 _ 0 ltac:(rewrite ?ew_ewset_other by lia; exact E11) ltac:(lia) ltac:(lia)), U_lit in Hc by lia end.
      rewrite Z.add_0_r in Hc. apply negb_false_iff, Z.eqb_eq in Hc. rename Hc into Hop1.
      paj_run_to_tok_x RUNTO HS HJ SHOK hd_Bspan AF_arm_write. { hd_awr0. } hd_meq mem.
      lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
      assert (HAEv : env_agree 32 (Ereg regs (hd_x1 (hd_kb cx m))) Ev)
        by (split; [intros m0 Hm; rewrite ?ew_ewset_other by lia; exact (proj1 HAE m0 Hm) | rewrite ?ed_ewset; exact (proj2 HAE)]) end.
      pose proof (regs_kept_of_st_ok_pi _ _ _ regs _ HD_KEPT2 HS HAEv ltac:(vm_compute; reflexivity)) as KR.
      cbn [ms_regs restrict] in KR.
      prreg HS (6%bv : bv 5) Q6. prreg HS (7%bv : bv 5) Q7. prreg HS (20%bv : bv 5) Q20.
      prreg HS (21%bv : bv 5) Q21. prreg HS (28%bv : bv 5) Q28. prreg HS (29%bv : bv 5) Q29.
      pmkst HS. rewrite HMm. rewrite HMm in HJ.
      apply SRr_ret. right; left.
      lazymatch goal with |- INV_A_xR _ _ _ _ _ _ _ _ _ _ _ _ _ _ {| cfg_ms := mkst ?r _ ?mm _; cfg_model := ?d |} => exists r, r, mm, d end.
      split; [reflexivity|]. split; [intros rr _; reflexivity|].
      split; [rewrite (KR 11%bv ltac:(cbv; tauto)), R11, Hop1; reflexivity|].
      split; [exists [(1, fpos)], ly3, S3, Hp3, k; exact HJ|]. split; [exact HROM|].
      exists [(1, fpos)], ly3, S3, Hp3, k, m, fpos.
      split; [exact HJ|]. split; [reflexivity|]. split; [exact HFR|]. split; [exact HFL|].
      split; [exact HMOD|]. split; [exact HIN|]. split; [exact HRV|]. split; [exact HSEP|].
      split; [exact HLS|]. split; [exact HNP|]. split; [exact HRI|].
      unfold lregs_D. cbv zeta. rewrite Hpk. cbv iota. rewrite Hmore. cbv iota.
      rewrite ?ew_ewset_other in Q28, Q29 by lia. rewrite ?E22, ?E28 in Q28. rewrite ?E21, ?E29 in Q29.
      rewrite ?unsigned_lit_small in Q28 by lia. rewrite ?unsigned_lit_small in Q29 by lia.
      split; [repeat split; first [rewrite (KR 2%bv ltac:(cbv; tauto)); assumption | rewrite (KR 8%bv ltac:(cbv; tauto)); assumption
      | rewrite (KR 9%bv ltac:(cbv; tauto)); assumption | rewrite (KR 18%bv ltac:(cbv; tauto)); assumption
      | rewrite (KR 19%bv ltac:(cbv; tauto)); assumption | rewrite Q20; reflexivity
      | rewrite (KR 23%bv ltac:(cbv; tauto)); assumption | rewrite (KR 24%bv ltac:(cbv; tauto)); assumption
      | rewrite (KR 25%bv ltac:(cbv; tauto)); assumption | rewrite (KR 26%bv ltac:(cbv; tauto)); assumption
      | rewrite (KR 3%bv ltac:(cbv; tauto)); assumption | rewrite (KR 4%bv ltac:(cbv; tauto)); assumption]|].
      split; [rewrite Q6; reflexivity|]. split; [rewrite Q7; reflexivity|].
      split; [rewrite (KR 27%bv ltac:(cbv; tauto)); exact R27|].
      split; [exact Ht|]. split; [exact Hk|]. split; [exact HO|].
      split; [rewrite (KR 11%bv ltac:(cbv; tauto)); exact R11|].
      split; [rewrite Q28; unfold w64; f_equal; lia|].
      split; [rewrite Q29; unfold w64; f_equal; lia|].
      right. split; [exact Hop1|]. split; [unfold pick, nopen; rewrite Hhs; reflexivity|]. rewrite Q21. reflexivity.
  }
  16:
  { psrr_branch_tok RUN BR HS SHOK hd_Bspan.
    - (* op <> 1: `continue`, to the loop test 0x844a0 *)
      lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
        rewrite branch_ne_U, (U_atom_off Ev 11 _ 0 ltac:(rewrite ?ew_ewset_other by lia; exact E11) ltac:(lia) ltac:(lia)), U_lit in Hc by lia end.
      rewrite Z.add_0_r in Hc. apply negb_true_iff, Z.eqb_neq in Hc. rename Hc into Hop1.
      paj_run_tok_x RUN HS HJ SHOK hd_Bspan. { hd_awr0. } hd_meq mem.
      psrr_branch_tok RUN BR HS SHOK hd_Bspan.
      + (* ops > 510: the loop ends *)
        lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
          rewrite branch_ltu_U, U_lit, (U_atom_off Ev 27 _ 0 ltac:(rewrite ?ew_ewset_other by lia; exact E27) ltac:(lia) ltac:(lia)) in Hc by lia end.
        paj_run_to_tok_x RUNTO HS HJ SHOK hd_Bspan AF_LLVM_exit. { hd_awr0. } hd_meq mem.
        lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
        assert (HAEv : env_agree 32 (Ereg regs (hd_x1 (hd_kb cx m))) Ev)
          by (split; [intros m0 Hm; rewrite ?ew_ewset_other by lia; exact (proj1 HAE m0 Hm) | rewrite ?ed_ewset; exact (proj2 HAE)]) end.
        pose proof (regs_kept_of_st_ok_pi _ _ _ regs _ HD_KEPT3 HS HAEv ltac:(vm_compute; reflexivity)) as KR.
        cbn [ms_regs restrict] in KR.
        pmkst HS. rewrite HMm. rewrite HMm in HJ.
        apply SRr_ret. right; right; right.
        lazymatch goal with |- INV_X_xR _ _ _ _ _ _ _ _ _ _ _ _ {| cfg_ms := mkst ?r _ ?mm _; cfg_model := ?d |} => exists r, mm, d, (t + 1) end.
        split; [reflexivity|]. split; [exact HROM|].
        exists [(1, fpos)], ly3, S3, Hp3, k, (lm_set_k m (hd_k' cx m)), fpos.
        split; [exact HJ|]. split; [reflexivity|]. split; [apply hd_aframe_false; exact HFR|]. split; [exact HFL|].
        split; [exact HMOD|]. split; [exact HIN|]. split; [exact HRV|]. split; [exact HSEP|].
        split; [apply LS_head_skip; [exact Ht | exact Hk | exact HO | exact Hpk | exact Hop1 | apply Hnone; exact Hhs |]; exact HLS|]. split; [exact HNP|].
        split; [apply RI_head_skip; [exact Ht | exact Hk | exact HO | exact Hpk | exact Hop1 | apply Hnone; exact Hhs |]; exact HRI|].
        cbv beta. unfold lregs_X. cbn [lm_k lm_set_k]. unfold hd_k'. rewrite Hmore. cbv iota.
        repeat split; first [rewrite (KR 2%bv ltac:(cbv; tauto)); assumption | rewrite (KR 8%bv ltac:(cbv; tauto)); assumption
          | rewrite (KR 9%bv ltac:(cbv; tauto)); assumption | rewrite (KR 18%bv ltac:(cbv; tauto)); assumption
          | rewrite (KR 23%bv ltac:(cbv; tauto)); assumption
          | rewrite (KR 25%bv ltac:(cbv; tauto)); assumption | rewrite (KR 26%bv ltac:(cbv; tauto)); assumption
          | rewrite (KR 3%bv ltac:(cbv; tauto)); assumption | rewrite (KR 4%bv ltac:(cbv; tauto)); assumption
          | (apply Z.ltb_lt in Hmore || apply Z.ltb_ge in Hmore); lia ].
      + lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
          rewrite branch_ltu_U, U_lit, (U_atom_off Ev 27 _ 0 ltac:(rewrite ?ew_ewset_other by lia; exact E27) ltac:(lia) ltac:(lia)) in Hc by lia end.
        rewrite Z.add_0_r in Hc. apply Z.ltb_ge in Hc. rename Hc into Ht510.
        paj_run_tok_x RUN HS HJ SHOK hd_Bspan. { hd_awr0. } hd_meq mem.
        psrr_branch_tok RUN BR HS SHOK hd_Bspan.
        * (* in.n left: the next operation *)
          lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
            rewrite branch_ne_U, (U_atom_off Ev 21 _ (-2) ltac:(rewrite ?ew_ewset_other by lia; exact E21) ltac:(lia) ltac:(apply Z.ltb_lt in Hmore; lia)), U_lit in Hc by lia end.
          apply negb_true_iff, Z.eqb_neq in Hc. rename Hc into Hn2.
          paj_run_to_tok_x RUNTO HS HJ SHOK hd_Bspan AF_LLVM_head. { hd_awr0. } hd_meq mem.
          lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
          assert (HAEv : env_agree 32 (Ereg regs (hd_x1 (hd_kb cx m))) Ev)
            by (split; [intros m0 Hm; rewrite ?ew_ewset_other by lia; exact (proj1 HAE m0 Hm) | rewrite ?ed_ewset; exact (proj2 HAE)]) end.
          pose proof (regs_kept_of_st_ok_pi _ _ _ regs _ HD_KEPT3 HS HAEv ltac:(vm_compute; reflexivity)) as KR.
          cbn [ms_regs restrict] in KR.
          prreg HS (6%bv : bv 5) Q6. prreg HS (7%bv : bv 5) Q7. prreg HS (20%bv : bv 5) Q20.
          prreg HS (21%bv : bv 5) Q21. prreg HS (22%bv : bv 5) Q22. prreg_raw HS (27%bv : bv 5) Q27.
          lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
            assert (U27 : U Ev (SAluw ALU_ADD (SOff 27 0) (SLit 1)) = t + 1)
              by (apply hd_addiw_U; [rewrite ?ew_ewset_other by lia; exact E27 | lia]) end.
          pmkst HS. rewrite HMm. rewrite HMm in HJ.
          apply SRr_ret. right; right; left.
          lazymatch goal with |- INV_H_xR _ _ _ _ _ _ _ _ _ _ _ _ _ {| cfg_ms := mkst ?r _ ?mm _; cfg_model := ?d |} => exists r, mm, d end.
          split; [reflexivity|]. split; [exact HROM|].
          exists [(1, fpos)], ly3, S3, Hp3, k, (lm_set_k m (hd_k' cx m)), fpos.
          split; [exact HJ|]. split; [reflexivity|]. split; [exact HFR|]. split; [exact HFL|].
          split; [exact HMOD|]. split; [exact HIN|]. split; [exact HRV|]. split; [exact HSEP|].
          split; [apply LS_head_skip; [exact Ht | exact Hk | exact HO | exact Hpk | exact Hop1 | apply Hnone; exact Hhs |]; exact HLS|]. split; [exact HNP|].
          split; [apply RI_head_skip; [exact Ht | exact Hk | exact HO | exact Hpk | exact Hop1 | apply Hnone; exact Hhs |]; exact HRI|].
          unfold lregs_H. cbn [lm_k lm_set_k]. unfold hd_k'. rewrite Hmore. cbv iota.
          rewrite ?ew_ewset_other in Q21, Q22 by lia. rewrite E21 in Q21. rewrite E22 in Q22.
          rewrite ?unsigned_lit_small in Q21 by lia. rewrite ?unsigned_lit_small in Q22 by lia.
          apply Z.ltb_lt in Hmore.
          split; [repeat split; first [rewrite (KR 2%bv ltac:(cbv; tauto)); assumption | rewrite (KR 8%bv ltac:(cbv; tauto)); assumption
          | rewrite (KR 9%bv ltac:(cbv; tauto)); assumption | rewrite (KR 18%bv ltac:(cbv; tauto)); assumption
          | rewrite (KR 19%bv ltac:(cbv; tauto)); assumption | rewrite Q20; reflexivity
          | rewrite (KR 23%bv ltac:(cbv; tauto)); assumption | rewrite (KR 24%bv ltac:(cbv; tauto)); assumption
          | rewrite (KR 25%bv ltac:(cbv; tauto)); assumption | rewrite (KR 26%bv ltac:(cbv; tauto)); assumption
          | rewrite (KR 3%bv ltac:(cbv; tauto)); assumption | rewrite (KR 4%bv ltac:(cbv; tauto)); assumption]|].
          split; [rewrite Q6; reflexivity|]. split; [rewrite Q7; reflexivity|].
          split; [rewrite Q21; unfold w64; f_equal; lia|].
          split; [rewrite Q22; unfold w64; f_equal; lia|].
          split; [rewrite Q27; apply hd_sv_of_U; [exact U27 | lia]|].
          unfold OPS_MAX in *. lia.
        * lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
            rewrite branch_ne_U, (U_atom_off Ev 21 _ (-2) ltac:(rewrite ?ew_ewset_other by lia; exact E21) ltac:(lia) ltac:(apply Z.ltb_lt in Hmore; lia)), U_lit in Hc by lia end.
          apply negb_false_iff, Z.eqb_eq in Hc.
          paj_run_to_tok_x RUNTO HS HJ SHOK hd_Bspan AF_LLVM_exit. { hd_awr0. } hd_meq mem.
          lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
          assert (HAEv : env_agree 32 (Ereg regs (hd_x1 (hd_kb cx m))) Ev)
            by (split; [intros m0 Hm; rewrite ?ew_ewset_other by lia; exact (proj1 HAE m0 Hm) | rewrite ?ed_ewset; exact (proj2 HAE)]) end.
          pose proof (regs_kept_of_st_ok_pi _ _ _ regs _ HD_KEPT3 HS HAEv ltac:(vm_compute; reflexivity)) as KR.
          cbn [ms_regs restrict] in KR.
          pmkst HS. rewrite HMm. rewrite HMm in HJ.
          apply SRr_ret. right; right; right.
          lazymatch goal with |- INV_X_xR _ _ _ _ _ _ _ _ _ _ _ _ {| cfg_ms := mkst ?r _ ?mm _; cfg_model := ?d |} => exists r, mm, d, (t + 1) end.
          split; [reflexivity|]. split; [exact HROM|].
          exists [(1, fpos)], ly3, S3, Hp3, k, (lm_set_k m (hd_k' cx m)), fpos.
          split; [exact HJ|]. split; [reflexivity|]. split; [apply hd_aframe_false; exact HFR|]. split; [exact HFL|].
          split; [exact HMOD|]. split; [exact HIN|]. split; [exact HRV|]. split; [exact HSEP|].
          split; [apply LS_head_skip; [exact Ht | exact Hk | exact HO | exact Hpk | exact Hop1 | apply Hnone; exact Hhs |]; exact HLS|]. split; [exact HNP|].
          split; [apply RI_head_skip; [exact Ht | exact Hk | exact HO | exact Hpk | exact Hop1 | apply Hnone; exact Hhs |]; exact HRI|].
          cbv beta. unfold lregs_X. cbn [lm_k lm_set_k]. unfold hd_k'. rewrite Hmore. cbv iota.
          repeat split; first [rewrite (KR 2%bv ltac:(cbv; tauto)); assumption | rewrite (KR 8%bv ltac:(cbv; tauto)); assumption
            | rewrite (KR 9%bv ltac:(cbv; tauto)); assumption | rewrite (KR 18%bv ltac:(cbv; tauto)); assumption
            | rewrite (KR 23%bv ltac:(cbv; tauto)); assumption
            | rewrite (KR 25%bv ltac:(cbv; tauto)); assumption | rewrite (KR 26%bv ltac:(cbv; tauto)); assumption
            | rewrite (KR 3%bv ltac:(cbv; tauto)); assumption | rewrite (KR 4%bv ltac:(cbv; tauto)); assumption
            | (apply Z.ltb_lt in Hmore || apply Z.ltb_ge in Hmore); lia ].
    - (* op = 1 with no open source: arm 1 with s = NULL *)
      lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
        rewrite branch_ne_U, (U_atom_off Ev 11 _ 0 ltac:(rewrite ?ew_ewset_other by lia; exact E11) ltac:(lia) ltac:(lia)), U_lit in Hc by lia end.
      rewrite Z.add_0_r in Hc. apply negb_false_iff, Z.eqb_eq in Hc. rename Hc into Hop1.
      paj_run_to_tok_x RUNTO HS HJ SHOK hd_Bspan AF_arm_write. { hd_awr0. } hd_meq mem.
      lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
      assert (HAEv : env_agree 32 (Ereg regs (hd_x1 (hd_kb cx m))) Ev)
        by (split; [intros m0 Hm; rewrite ?ew_ewset_other by lia; exact (proj1 HAE m0 Hm) | rewrite ?ed_ewset; exact (proj2 HAE)]) end.
      pose proof (regs_kept_of_st_ok_pi _ _ _ regs _ HD_KEPT2 HS HAEv ltac:(vm_compute; reflexivity)) as KR.
      cbn [ms_regs restrict] in KR.
      prreg HS (6%bv : bv 5) Q6. prreg HS (7%bv : bv 5) Q7. prreg HS (20%bv : bv 5) Q20.
      prreg HS (21%bv : bv 5) Q21. prreg HS (28%bv : bv 5) Q28. prreg HS (29%bv : bv 5) Q29.
      pmkst HS. rewrite HMm. rewrite HMm in HJ.
      apply SRr_ret. right; left.
      lazymatch goal with |- INV_A_xR _ _ _ _ _ _ _ _ _ _ _ _ _ _ {| cfg_ms := mkst ?r _ ?mm _; cfg_model := ?d |} => exists r, r, mm, d end.
      split; [reflexivity|]. split; [intros rr _; reflexivity|].
      split; [rewrite (KR 11%bv ltac:(cbv; tauto)), R11, Hop1; reflexivity|].
      split; [exists [(1, fpos)], ly3, S3, Hp3, k; exact HJ|]. split; [exact HROM|].
      exists [(1, fpos)], ly3, S3, Hp3, k, m, fpos.
      split; [exact HJ|]. split; [reflexivity|]. split; [exact HFR|]. split; [exact HFL|].
      split; [exact HMOD|]. split; [exact HIN|]. split; [exact HRV|]. split; [exact HSEP|].
      split; [exact HLS|]. split; [exact HNP|]. split; [exact HRI|].
      unfold lregs_D. cbv zeta. rewrite Hpk. cbv iota. rewrite Hmore. cbv iota.
      rewrite ?ew_ewset_other in Q28, Q29 by lia. rewrite ?E22, ?E28 in Q28. rewrite ?E21, ?E29 in Q29.
      rewrite ?unsigned_lit_small in Q28 by lia. rewrite ?unsigned_lit_small in Q29 by lia.
      split; [repeat split; first [rewrite (KR 2%bv ltac:(cbv; tauto)); assumption | rewrite (KR 8%bv ltac:(cbv; tauto)); assumption
      | rewrite (KR 9%bv ltac:(cbv; tauto)); assumption | rewrite (KR 18%bv ltac:(cbv; tauto)); assumption
      | rewrite (KR 19%bv ltac:(cbv; tauto)); assumption | rewrite Q20; reflexivity
      | rewrite (KR 23%bv ltac:(cbv; tauto)); assumption | rewrite (KR 24%bv ltac:(cbv; tauto)); assumption
      | rewrite (KR 25%bv ltac:(cbv; tauto)); assumption | rewrite (KR 26%bv ltac:(cbv; tauto)); assumption
      | rewrite (KR 3%bv ltac:(cbv; tauto)); assumption | rewrite (KR 4%bv ltac:(cbv; tauto)); assumption]|].
      split; [rewrite Q6; reflexivity|]. split; [rewrite Q7; reflexivity|].
      split; [rewrite (KR 27%bv ltac:(cbv; tauto)); exact R27|].
      split; [exact Ht|]. split; [exact Hk|]. split; [exact HO|].
      split; [rewrite (KR 11%bv ltac:(cbv; tauto)); exact R11|].
      split; [rewrite Q28; unfold w64; f_equal; lia|].
      split; [rewrite Q29; unfold w64; f_equal; lia|].
      right. split; [exact Hop1|]. split; [unfold pick, nopen; rewrite Hhs; reflexivity|]. rewrite Q21. reflexivity.
  }
  (* an open source: the remainder kb % n (pinned to its value), the k-th open source, to the dispatch *)
  all: lazymatch goal with HS : st_ok_pi ?sg ?vl ?Ev ?ss (restrict ?H ?ms) |- _ =>
    let a2 := eval vm_compute in (sr_get (ss_regs ss) 12%bv) in
    lazymatch a2 with
    | SMdw M_REM (SOff 32 0) (SLit ?c) =>
        assert (UR : U Ev (SMdw M_REM (SOff 32 0) (SLit c)) = hd_kb cx m mod c)
          by (apply hd_rem_U; [rewrite ?ew_ewset_other by lia; exact E32 | exact Hkb | lia]);
        pose proof (st_ok_pi_restrict_reg H Ev ss ms 12%bv HS) as Q12;
        change (sr_get (ss_regs ss) 12%bv) with a2 in Q12; cbn [ms_regs restrict] in Q12;
        pose proof (Z.mod_pos_bound (hd_kb cx m) c ltac:(lia)) as Rr;
        assert (Hr4 : hd_kb cx m mod c = 0 \/ hd_kb cx m mod c = 1 \/ hd_kb cx m mod c = 2 \/ hd_kb cx m mod c = 3)
          by lia
    | _ => idtac
    end end.
  all: try (destruct Hr4 as [HR | [HR | [HR | HR]]]).
  all: try (match goal with HR : hd_kb _ _ mod ?c = ?r, Rr : 0 <= _ < ?c |- _ => exfalso; clear - HR Rr; lia end).
  all: try (lazymatch goal with HR : hd_kb _ _ mod _ = ?r, Q12 : getr _ 12%bv = _, UR : U _ _ = _ |- _ =>
       lazymatch goal with HS : st_ok_pi ?sg ?vl ?Ev ?ss (restrict ?H ?ms) |- _ =>
         pose proof (st_ok_pi_pin_reg' Ev ss (restrict H ms) 12%bv r HS
            ltac:(cbn [ms_regs restrict]; rewrite Q12; apply hd_sv_of_U; [rewrite UR; exact HR | lia]) eq_refl) as HS2;
         clear HS; rename HS2 into HS; cbn [ss_pc ss_regs ss_mem ss_resv ss_facts] in HS; norm_ss HS end end).
  all: try (unfold hd_kb in HR; rewrite Hmore in HR; cbv iota in HR).
  all: paj_run_to_tok_x RUNTO HS HJ SHOK hd_Bspan AF_LLVM_dispatch.
  all: try hd_awr0.
  all: hd_meq mem.
  all: lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
      assert (HAEv : env_agree 32 (Ereg regs (hd_x1 (hd_kb cx m))) Ev)
        by (split; [intros m0 Hm; rewrite ?ew_ewset_other by lia; exact (proj1 HAE m0 Hm) | rewrite ?ed_ewset; exact (proj2 HAE)]) end.
  all: pose proof (regs_kept_of_st_ok_pi _ _ _ regs _ HD_KEPT2 HS HAEv ltac:(vm_compute; reflexivity)) as KR.
  all: cbn [ms_regs restrict] in KR.
  all: prreg HS (6%bv : bv 5) Q6; prreg HS (7%bv : bv 5) Q7; prreg HS (20%bv : bv 5) Q20.
  all: prreg HS (21%bv : bv 5) Q21; prreg HS (28%bv : bv 5) Q28; prreg HS (29%bv : bv 5) Q29.
  all: pmkst HS.
  all: rewrite HMm; rewrite HMm in HJ.
  all: apply SRr_ret; left; exists (in_byte cx (lm_k m) mod 10); split; [lia|].
  all: lazymatch goal with |- INV_D_xR _ _ _ _ _ _ _ _ _ _ _ _ _ _ {| cfg_ms := mkst ?r _ ?mm _; cfg_model := ?d |} => exists r, mm, d end.
  all: split; [reflexivity|].
  all: split; [rewrite (KR 11%bv ltac:(cbv; tauto)); exact R11|].
  all: split; [exists [(1, fpos)], ly3, S3, Hp3, k; exact HJ|].
  all: split; [exact HROM|].
  all: exists [(1, fpos)], ly3, S3, Hp3, k, m, fpos.
  all: split; [exact HJ|]; split; [reflexivity|]; split; [exact HFR|]; split; [exact HFL|]; split; [exact HMOD|]; split; [exact HIN|].
  all: split; [exact HRV|]; split; [exact HSEP|]; split; [exact HLS|]; split; [exact HNP|]; split; [exact HRI|].
  all: unfold lregs_D; cbv zeta; rewrite Hpk; cbv iota; rewrite Hmore; cbv iota.
  all: rewrite ?ew_ewset_other in Q21, Q28, Q29 by lia.
  all: rewrite ?E22, ?E28 in Q28; rewrite ?E21, ?E29 in Q29; rewrite ?EG' in Q21.
  all: rewrite ?unsigned_lit_small in Q21 by (cbn; lia); rewrite ?unsigned_lit_small in Q28 by lia;
    rewrite ?unsigned_lit_small in Q29 by lia.
  (* SPEED, the one tactic that differs from the AR file: there this sentence (up to 12 alternatives per
     register, each elaborating `KR _ ltac:(cbv; tauto)`) took 346 s over the open-source goals. One attempt per register
     with the same tauto still took 329 s, 297 s of it in elaborating `KR r ltac:(cbv; tauto)` (564 calls, timed one by
     one): tauto works over the whole context. Here In r HD_KEPT2 is proved without the context. *)
  all: split; [unfold lregs_common; repeat (match goal with |- _ /\ _ => split end);
    lazymatch goal with |- getr _ ?r = _ =>
      first [rewrite (KR r ltac:(cbv [HD_KEPT2 In]; repeat (first [left; reflexivity | right]))); assumption
            | rewrite Q20; reflexivity] end|].
  all: split; [rewrite Q6; reflexivity|]; split; [rewrite Q7; reflexivity|].
  all: split; [rewrite (KR 27%bv ltac:(cbv; tauto)); exact R27|].
  all: split; [exact Ht|]; split; [exact Hk|]; split; [exact HO|].
  all: split; [rewrite (KR 11%bv ltac:(cbv; tauto)); exact R11|].
  all: split; [rewrite Q28; unfold w64; f_equal; lia|].
  all: split; [rewrite Q29; unfold w64; f_equal; lia|].
  all: left; eexists; split.
  all: try (unfold pick; rewrite Hhs;
    lazymatch goal with |- context [nopen ?l] => let v := eval vm_compute in (nopen l) in change (nopen l) with v end;
    try rewrite HR; reflexivity).
  all: rewrite Q21; unfold w64, ASRC; f_equal; cbn [Z.of_nat Pos.of_succ_nat]; cbn; lia.
Qed.

(* ------------------------------------------------------------------ SEG_HEAD_R *)
(* cut_x Section wR's SEG_HEAD_R: the two strict walks over the R journal, each lifted to SRrG segs R by SRr_SRrG
   (the segment moves no world), composed at R *)
Theorem lf_seg_head_xR : forall cx Hp t W c, lf_base_x B MT XM_LIB RLO RHI fr_live_pre LIBROOM NP G_fr ARx cx Hp ->
  INV_H_xR B NP G_fr fr_FP PST ARx LSx RINV R cx Hp t W c ->
  SRrG segs R W c (fun W' c' => (exists op, 0 <= op <= 9 /\ INV_D_xR B NP G_fr fr_FP PST ARx LSx RINV R cx Hp t op W' c') \/
    INV_A_xR B NP G_fr fr_FP PST ARx LSx RINV R 1 cx Hp t W' c' \/
    INV_H_xR B NP G_fr fr_FP PST ARx LSx RINV R cx Hp (t + 1) W' c' \/ INV_X_xR B NP G_fr fr_FP PST ARx LSx RINV R cx Hp W' c').
Proof.
  intros cx Hp t W c HB HH.
  eapply (SRrG_bind segs R R_trans); [exact (SRr_SRrG segs R WLE_R W c _ (hd_w1_xR cx Hp t W c HB HH))|].
  intros W1 c1 _ [HD | HP].
  - apply (SRrG_ret segs R R_refl). left. exact HD.
  - exact (SRr_SRrG segs R WLE_R W1 c1 _ (hd_w2_xR cx Hp t W1 c1 HB HP)).
Qed.
End hxR.

(* ------------------------------------------------------------------ SEG_HEAD *)
(* lf_seg_head_xR at R := wle (route R's rule: one walk text): SRrG at wle is SRr and each INV_*_xR at wle is INV_*_x,
   by conversion (W_journal_x's ajournal_gx_x_wle) *)
Theorem lf_seg_head_x : forall cx Hp t W c, lf_base_x B MT XM_LIB RLO RHI fr_live_pre LIBROOM NP G_fr ARx cx Hp ->
  INV_H_x B NP G_fr fr_FP PST ARx LSx RINV cx Hp t W c ->
  SRr segs W c (fun W' c' => (exists op, 0 <= op <= 9 /\ INV_D_x B NP G_fr fr_FP PST ARx LSx RINV cx Hp t op W' c') \/
    INV_A_x B NP G_fr fr_FP PST ARx LSx RINV 1 cx Hp t W' c' \/
    INV_H_x B NP G_fr fr_FP PST ARx LSx RINV cx Hp (t + 1) W' c' \/ INV_X_x B NP G_fr fr_FP PST ARx LSx RINV cx Hp W' c').
Proof. exact (lf_seg_head_xR (@wle segs) (wle_refl segs) (wle_trans segs) (fun W W' H => H)). Qed.
End hx.

(* ---- CHECK: lf_seg_head_x is cut_x Section w's SEG_HEAD. In a Section with cut_x's Section w header and the AR
   file's hypotheses, the theorem proves SEG_HEAD's text, and lf_contract_of_segments_x (cut_x.v:371) takes it as its
   SEG_HEAD argument. ---- *)
Section chk.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Notation segs := (@pa_segs _ fr_prog_listing PB_fr).
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
Hypothesis HGnout : forall a, rg_nout fr_RG <= a < rg_nout fr_RG + 8 -> inG G_fr a.
Hypothesis HERRNO : 0 <= as_errno B /\ as_errno B + 4 <= 2 ^ 64 /\
  (as_errno B + 4 <= rg_nout fr_RG \/ rg_nout fr_RG + 8 <= as_errno B).
Hypothesis RI_head_nout : forall cx t m, RINV cx t m -> RINV cx t (lm_clear_O m).
Hypothesis LS_head_nout : forall cx t m ly S, LSx cx t m ly S -> LSx cx t (lm_clear_O m) ly S.
Hypothesis HZS : exists r, In r (as_zero_shadow B) /\ fst r mod 8 = 0 /\ fst r <= rg_s fr_RG /\
  rg_s fr_RG + 4 * ASRC <= fst r + snd r / 8 * 8.
Hypothesis RI_head_skip : forall cx t m, 0 <= t < OPS_MAX -> 0 <= lm_k m < c_n cx -> lm_O m = [] ->
  picks (in_byte cx (lm_k m) mod 10) = true -> in_byte cx (lm_k m) mod 10 <> 1 ->
  pick (lm_hs m) (hd_kb cx m) = None -> RINV cx t m -> RINV cx (t + 1) (lm_set_k m (hd_k' cx m)).
Hypothesis LS_head_skip : forall cx t m ly S, 0 <= t < OPS_MAX -> 0 <= lm_k m < c_n cx -> lm_O m = [] ->
  picks (in_byte cx (lm_k m) mod 10) = true -> in_byte cx (lm_k m) mod 10 <> 1 ->
  pick (lm_hs m) (hd_kb cx m) = None -> LSx cx t m ly S -> LSx cx (t + 1) (lm_set_k m (hd_k' cx m)) ly S.
(* cut_x.v:299-301 SEG_HEAD, its text with cut_x's Section w arguments written out *)
Lemma lf_seg_head_x_check : forall cx Hp t W c,
  lf_base_x B MT XM_LIB RLO RHI fr_live_pre LIBROOM NP G_fr ARx cx Hp ->
  INV_H_x B NP G_fr fr_FP PST ARx LSx RINV cx Hp t W c ->
  SRr segs W c (fun W' c' => (exists op, 0 <= op <= 9 /\ INV_D_x B NP G_fr fr_FP PST ARx LSx RINV cx Hp t op W' c') \/
    INV_A_x B NP G_fr fr_FP PST ARx LSx RINV 1 cx Hp t W' c' \/
    INV_H_x B NP G_fr fr_FP PST ARx LSx RINV cx Hp (t + 1) W' c' \/ INV_X_x B NP G_fr fr_FP PST ARx LSx RINV cx Hp W' c').
Proof.
  exact (lf_seg_head_x B MT XM_LIB XN_LIB RLO RHI fr_live_pre LIBROOM NP G_fr fr_FP PST ARx LAWS HP0 HG LSx RINV
    HGnout HERRNO RI_head_nout LS_head_nout HZS RI_head_skip LS_head_skip).
Qed.
(* lf_contract_of_segments_x's SEG_HEAD argument is filled by the theorem: this term type-checks only if the two
   types are convertible *)
Definition lf_seg_head_x_plugs := fun SEG_PRO =>
  lf_contract_of_segments_x B MT XM_LIB XN_LIB RLO RHI fr_live_pre fr_live_post fr_surv LIBROOM NP G_fr fr_FP PST ARx
    LAWS HG LSx RINV SEG_PRO lf_seg_head_x_check.
(* lib/A/W_LLVMFuzzerTestOneInput_cut_x.v:453-455 SEG_HEAD_R, its text with cut_x's Section w / wR arguments written out; lf_contract_of_segments_xR
   (cut_x.v:525) takes it as its SEG_HEAD_R argument.  The theorem's arguments: lf_seg_head_x's, then R R_refl R_trans
   WLE_R. *)
Section chkR.
Variable R : world segs -> world segs -> Prop.
Hypothesis R_refl : forall W, R W W.
Hypothesis R_trans : forall W1 W2 W3, R W1 W2 -> R W2 W3 -> R W1 W3.
Hypothesis WLE_R : forall W W', wle W W' -> R W W'.
Lemma lf_seg_head_xR_check : forall cx Hp t W c,
  lf_base_x B MT XM_LIB RLO RHI fr_live_pre LIBROOM NP G_fr ARx cx Hp ->
  INV_H_xR B NP G_fr fr_FP PST ARx LSx RINV R cx Hp t W c ->
  SRrG segs R W c (fun W' c' => (exists op, 0 <= op <= 9 /\ INV_D_xR B NP G_fr fr_FP PST ARx LSx RINV R cx Hp t op W' c') \/
    INV_A_xR B NP G_fr fr_FP PST ARx LSx RINV R 1 cx Hp t W' c' \/
    INV_H_xR B NP G_fr fr_FP PST ARx LSx RINV R cx Hp (t + 1) W' c' \/ INV_X_xR B NP G_fr fr_FP PST ARx LSx RINV R cx Hp W' c').
Proof.
  exact (lf_seg_head_xR B MT XM_LIB XN_LIB RLO RHI fr_live_pre LIBROOM NP G_fr fr_FP PST ARx LAWS HP0 HG LSx RINV
    HGnout HERRNO RI_head_nout LS_head_nout HZS RI_head_skip LS_head_skip R R_refl R_trans WLE_R).
Qed.
Definition lf_seg_head_xR_plugs := fun SEG_PRO_R =>
  lf_contract_of_segments_xR B MT XM_LIB XN_LIB RLO RHI fr_live_pre fr_live_post fr_surv LIBROOM NP G_fr fr_FP PST ARx
    LAWS HG LSx RINV R R_refl R_trans WLE_R SEG_PRO_R lf_seg_head_xR_check.
End chkR.
End chk.
