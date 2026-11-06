(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs, 2026-10: SEG_HEAD of the ASan+UBSan walk of fuzz_reply's LLVMFuzzerTestOneInput (image B,
   fuzz_reply.asan-ubsan) OVER ARx (a Theorem Labs lane's route (b)).  lf_seg_head_x is the text of
   lib/B/W_LLVMFuzzerTestOneInput_cut_x.v Section w's hypothesis SEG_HEAD, so lib/B/W_LLVMFuzzerTestOneInput_top_x.v
   takes it in place of that hypothesis.  It is the ARx conversion of image B's AR proof lf_seg_head_b
   (lib/B/W_LLVMFuzzerTestOneInput_head.v, carried on a working branch fdb3ee1c6ffa), which is NOT edited;
   the method is image A's lib/A/W_LLVMFuzzerTestOneInput_head_x.v (HeadX, a working branch).
   - The Section header is B cut_x's Section w header (B .. ARx, hl, LAWS, HP0, HG, LSx, RINV), then the AR file's own
     seven hypotheses, each text verbatim with LS named LSx: HGnout, HERRNO, HZS (instance facts: B _G.v's c_HGnout,
     c_HERRNO, c_HZS) and the four model rules RI_head_nout, LS_head_nout, RI_head_skip, LS_head_skip (at the instance's
     fr_RINV / fr_LS, a Theorem Labs lane's RI_head_nout_b / LS_head_nout_b / RI_head_skip_b / LS_head_skip_b, restated in B
     _G.v as c_RI_head_nout / c_LS_head_nout / c_RI_head_skip / c_LS_head_skip).  No other hypothesis.
   - The AR-free names of the AR file are cited from it, not copied: the entry states hb_entry0 / hb_entry1 /
     hb_entry2, the byte / op / remainder / increment lemmas, the store-frame lemmas that name no AR, the four *_blks_in,
     hb_open_val, and the definitions lm_clear_O, lm_set_k, hd_kb, hd_k', hb_lregs_P, HB_KEPT*.
   - Each AR-stated lemma has its twin NAME_x here: the AR proof with W1Verify's substitutions (ARx with the ghost list
     after S; alx_blocks / alx_zshadow for the AR laws; frames_bounds_x; W_journal_x's ajournal_gx_AR_x /
     ajournal_gx_inner_x; cut_x's lcut_x / lf_base_x / INV_*_x; paj_run(_to)_tok_x over RUN := paj_run_x_x;
     range_addressable_of_block_hp0_x under HP0; W_frame_x's frm_off_imgP_x with IMGC := W_img_x.fr_img_cover_x).
     blk_off_imgP's ARx form is hb_blk_imgP_x (A's hd_blk_imgP_x): the proof of W_kit_x's blk_off_imgP_x with IMGC
     from fr_img_cover_x and 0 <= n taken for the one block, which every caller has; the store frame's block lemmas
     (Section fo) are A's twins, which are B's AR text with that premise.
   - The ghost list: HP0 makes it [] in every ARx state, so the walk's lemmas state it as []; lf_seg_head_x reads
     Hp = [] off the entry's afn_pre_x by HP0, and each walk reads the cut's Hp3 = [] off its journal's ARx.
   - The AR file's Section-local Ltacs (dropped at its End hb) are restated verbatim.  The positional destructs of the
     pre end in `_` (the B cut's coming harness-block clause is one more trailing conjunct). *)
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
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_rep W_contract W_frame.
(* RelocB's sink-instance guard (after the Import of YE2k): every sink argument is passed with @ or from the Context *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require ReplyGuardB.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_LLVMFuzzerTestOneInput_cut.
From Stdlib Require Import FunctionalExtensionality.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YCbqG.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_kit_x W_journal_x W_frame_x W_img_x.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import
W_LLVMFuzzerTestOneInput_cut_x W_LLVMFuzzerTestOneInput_head.
(* the zify flag as the AR file's proofs see it, whatever a Required file leaves (as A's head_x) *)
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Import ListNotations.
Local Unset Lia Cache. Local Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

Section hx.
Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Local Notation segs := (@pa_segs _ fr_prog_listing PB_fr).
#[local] Notation VAL := (@pa_val _ fr_prog_listing PB_fr).
#[local] Notation BASE := (@pa_val _ fr_prog_listing PB_fr A_TEXT).
(* ---- B cut_x's Section w header (W_LLVMFuzzerTestOneInput_cut_x.v:199-244) ---- *)
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
(* ---- the AR file's own hypotheses (W_LLVMFuzzerTestOneInput_head.v:260-283), verbatim with LS named LSx ---- *)
(* g_nout's 8 bytes are in G_fr (the store at 0x8461c); at the pin: B _G.v c_HGnout *)
Hypothesis HGnout : forall a, rg_nout fr_RG <= a < rg_nout fr_RG + 8 -> inG G_fr a.
(* errno's cell is apart from g_nout; at the pin: B _G.v c_HERRNO *)
Hypothesis HERRNO : 0 <= as_errno B /\ as_errno B + 4 <= 2 ^ 64 /\
  (as_errno B + 4 <= rg_nout fr_RG \/ rg_nout fr_RG + 8 <= as_errno B).
(* g_s's shadow is zero (W_contract.v azs B (rg_s fr_RG) (4 * ASRC), unfolded); at the pin: B _G.v c_HZS *)
Hypothesis HZS : exists r, In r (as_zero_shadow B) /\ fst r mod 8 = 0 /\ fst r <= rg_s fr_RG /\
  rg_s fr_RG + 4 * ASRC <= fst r + snd r / 8 * 8.
(* the model obligations on cut_x's RINV / LSx: g_nout := 0 (no allocation, no block changes) *)
Hypothesis RI_head_nout : forall cx t m, RINV cx t m -> RINV cx t (lm_clear_O m).
Hypothesis LS_head_nout : forall cx t m ly S, LSx cx t m ly S -> LSx cx t (lm_clear_O m) ly S.
(* `continue` (an op that picks, no open source, op <> 1) ends the operation with the input consumed *)
Hypothesis RI_head_skip : forall cx t m, 0 <= t < OPS_MAX -> 0 <= lm_k m < c_n cx -> lm_O m = [] ->
  picks (in_byte cx (lm_k m) mod 10) = true -> in_byte cx (lm_k m) mod 10 <> 1 ->
  pick (lm_hs m) (hd_kb cx m) = None -> RINV cx t m -> RINV cx (t + 1) (lm_set_k m (hd_k' cx m)).
Hypothesis LS_head_skip : forall cx t m ly S, 0 <= t < OPS_MAX -> 0 <= lm_k m < c_n cx -> lm_O m = [] ->
  picks (in_byte cx (lm_k m) mod 10) = true -> in_byte cx (lm_k m) mod 10 <> 1 ->
  pick (lm_hs m) (hd_kb cx m) = None -> LSx cx t m ly S -> LSx cx (t + 1) (lm_set_k m (hd_k' cx m)) ly S.

Let RUN := paj_run_x_x (PL := PL_fr) (PI := PB_fr) B PST ARx LAWS G_fr HG 0 [].
Let RUNTO := paj_run_to_x_x (PL := PL_fr) (PI := PB_fr) B PST ARx LAWS G_fr HG 0 [].
Let BR := paj_branch (PI := PB_fr).
(* ---- the AR file's AR-free names with the Section argument B, cited ---- *)
Local Notation hb_alist_blks_in := (W_LLVMFuzzerTestOneInput_head.hb_alist_blks_in B).
Local Notation hb_asrc_blks_in := (W_LLVMFuzzerTestOneInput_head.hb_asrc_blks_in B).
Local Notation hb_aentry_blks_in := (W_LLVMFuzzerTestOneInput_head.hb_aentry_blks_in B).
Local Notation hb_arelay_blks_in := (W_LLVMFuzzerTestOneInput_head.hb_arelay_blks_in B).
Local Notation hb_lregs_P := (W_LLVMFuzzerTestOneInput_head.hb_lregs_P B).
Local Notation hb_open_val := (W_LLVMFuzzerTestOneInput_head.hb_open_val B).

(* ---- the store frame's block lemmas over ARx (A's head_x Section fo, B's AR text :330-452 with 0 <= n) ---- *)
(* W_kit_x.v:47 blk_off_imgP_x's proof: IMGC is W_img_x.v's fr_img_cover_x (the laws' field 17), and BLKN's
   0 <= n is a premise for the one block *)
Lemma hb_blk_imgP_x : forall ly S Hp (W : world segs) mem md p n,
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
Lemma hb_blk_off_x : forall ly S Hp W mem md p n a, ARx ly S Hp W mem md -> In (p, n) (ablocks B ly S) -> 0 <= n ->
  p <= a < p + req_size n + 8 -> hb_offw lo hi a.
Proof.
  intros ly S Hp W mem md p n a HAR Hin Hn Ha.
  destruct (alx_blocks _ _ _ LAWS _ _ _ _ _ _ _ _ HAR Hin) as (_ & Hp4096 & Hpceil & _ & _ & _).
  pose proof (hb_blk_imgP_x ly S Hp W mem md p n HAR Hin Hn) as Himg.
  pose proof asan_consts as (C1 & _). unfold hb_offw. split; lia.
Qed.
Lemma hb_alist_fp_off_x : forall ly S Hp W mem md LA l lines, ARx ly S Hp W mem md ->
  alist_at B ly S W mem LA l lines -> hb_rng_off lo hi (LA, LA + 16) ->
  forall r, In r (alist_fp LA l) -> hb_rng_off lo hi r.
Proof.
  intros ly S Hp W mem md LA l lines HAR (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9) HLA r Hr.
  unfold alist_fp in Hr. destruct Hr as [<- | Hr]; [exact HLA|].
  apply in_app_or in Hr as [Hr | Hr].
  - destruct (hl_cap l =? 0) eqn:Ec; [destruct Hr|]. destruct Hr as [<- | []].
    apply Z.eqb_neq in Ec.
    destruct H6 as [(Hc & _) | (Hc & Hin & Hj & _)]; [lia|].
    intros a Ha. unfold gfp, bzs in Ha. cbn [fst snd] in Ha. rewrite length_map, length_app, hb_len_text in Ha.
    unfold hl_n in Hj, H5.
    apply (hb_blk_off_x ly S Hp W mem md (hl_v l) (AREC * hl_cap l) a HAR Hin ltac:(unfold AREC; lia)).
    pose proof (req_size_pos (AREC * hl_cap l) ltac:(unfold AREC; lia)) as [_ Hq]. unfold AREC in *. lia.
  - apply in_map_iff in Hr as (rr & <- & Hrr). rewrite Forall_forall in H9. destruct (H9 rr Hrr) as (Hb & _).
    intros a Ha. unfold gfp, bzs in Ha. cbn [fst snd] in Ha. rewrite length_map, length_app in Ha. cbn [length] in Ha.
    apply (hb_blk_off_x ly S Hp W mem md (fst rr) (Z.of_nat (length (snd rr)) + 1) a HAR Hb ltac:(lia)).
    pose proof (req_size_pos (Z.of_nat (length (snd rr)) + 1) ltac:(lia)) as [_ Hq]. lia.
Qed.
Lemma hb_asrc_fp_off_x : forall ly S Hp W mem md HA h, ARx ly S Hp W mem md -> asrc_at B ly S W mem HA h ->
  hb_rng_off lo hi (HA, HA + ASRC) -> forall r, In r (asrc_fp HA h) -> hb_rng_off lo hi r.
Proof.
  intros ly S Hp W mem md HA h HAR Hs HHA r Hr.
  pose proof Hs as (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11 & H12 & H13 & H14 & H15 & H16 & H17 & H18 &
    H19 & H20 & H21 & H22 & H23 & H24).
  unfold asrc_fp in Hr. destruct Hr as [<- | [<- | Hr]]; [exact HHA | |].
  - intros a Ha. unfold gfp, bzs in Ha. cbn [fst snd] in Ha. rewrite length_map, H19 in Ha.
    apply (hb_blk_off_x ly S Hp W mem md (hs_partial h) APARTIAL a HAR H18 ltac:(unfold APARTIAL; lia)).
    pose proof (req_size_pos APARTIAL ltac:(unfold APARTIAL; lia)) as [_ Hq]. lia.
  - apply in_app_or in Hr as [Hr | Hr]; [|apply in_app_or in Hr as [Hr | Hr]].
    + apply (hb_alist_fp_off_x ly S Hp W mem md (HA + 16) (hs_pending h) false HAR H10); [|exact Hr].
      apply (hb_rng_off_sub lo hi HA ASRC); [exact HHA | lia | unfold ASRC; lia].
    + apply (hb_alist_fp_off_x ly S Hp W mem md (HA + 64) (hs_expected h) true HAR H22); [|exact Hr].
      apply (hb_rng_off_sub lo hi HA ASRC); [exact HHA | lia | unfold ASRC; lia].
    + apply (hb_alist_fp_off_x ly S Hp W mem md (HA + 80) (hs_held h) true HAR H23); [|exact Hr].
      apply (hb_rng_off_sub lo hi HA ASRC); [exact HHA | lia | unfold ASRC; lia].
Qed.
Lemma hb_aentry_fp_off_x : forall ly S Hp W mem md e, ARx ly S Hp W mem md -> aentry_ok B ly S W mem e ->
  forall r, In r (aentry_fp e) -> hb_rng_off lo hi r.
Proof.
  intros ly S Hp W mem md e HAR (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11 & H12 & H13 & H14 & H15) r Hr.
  unfold aentry_fp in Hr. apply in_app_or in Hr as [Hr | Hr].
  - destruct (re_cap e =? 0) eqn:Ec; [destruct Hr|]. destruct Hr as [<- | []]. apply Z.eqb_neq in Ec.
    destruct H10 as [(Hc & _) | (Hc & Hin & Hj & _)]; [lia|].
    intros a Ha. unfold gfp, bzs in Ha. cbn [fst snd] in Ha. rewrite length_map, length_app in Ha.
    apply (hb_blk_off_x ly S Hp W mem md (re_buf e) (re_cap e) a HAR Hin ltac:(lia)).
    pose proof (req_size_pos (re_cap e) ltac:(lia)) as [_ Hq]. lia.
  - destruct Hr as [<- | Hr].
    + intros a Ha. unfold gfp, bzs in Ha. cbn [fst snd] in Ha. rewrite length_map, hb_len_kptrs in Ha.
      destruct H12 as [(Hz & Hk) | (Hz & Hin & Hk1 & Hk2 & _)]; [rewrite Hk in Ha; cbn in Ha; lia|].
      apply (hb_blk_off_x ly S Hp W mem md (re_hp e) (re_kh e) a HAR Hin ltac:(lia)).
      pose proof (req_size_pos (re_kh e) ltac:(lia)) as [_ Hq]. unfold re_nheld in Hk1. lia.
    + apply in_map_iff in Hr as (k & <- & Hk). rewrite Forall_forall in H15. destruct (H15 k Hk) as (K1 & _).
      intros a Ha. unfold gfp, bzs in Ha. cbn [fst snd] in Ha. rewrite length_map, length_app in Ha. cbn [length] in Ha.
      apply (hb_blk_off_x ly S Hp W mem md (key_addr k) (Z.of_nat (length (key_text k)) + 1) a HAR K1 ltac:(lia)).
      pose proof (req_size_pos (Z.of_nat (length (key_text k)) + 1) ltac:(lia)) as [_ Hq]. lia.
Qed.
Lemma hb_arelay_fp_off_x : forall RG ly S Hp W mem md G es, ARx ly S Hp W mem md -> arelay_at B RG ly S W mem G es ->
  hb_rng_off lo hi (rg_src RG, rg_src RG + 8) -> hb_rng_off lo hi (rg_nsrc RG, rg_nsrc RG + 4) ->
  hb_rng_off lo hi (rg_capsrc RG, rg_capsrc RG + 4) ->
  forall r, In r (arelay_fp RG G es) -> hb_rng_off lo hi r.
Proof.
  intros RG ly S Hp W mem md G es HAR (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11) R1 R2 R3 r Hr.
  unfold arelay_fp in Hr. destruct Hr as [<- | [<- | [<- | [<- | Hr]]]]; [exact R1 | exact R2 | exact R3 | |].
  - intros a Ha. cbn [fst snd] in Ha. apply (hb_blk_off_x ly S Hp W mem md G ATABLE a HAR H8 ltac:(unfold ATABLE; lia)).
    pose proof (req_size_pos ATABLE ltac:(unfold ATABLE; lia)) as [_ Hq]. lia.
  - apply in_concat in Hr as (l & Hl & Hr). apply in_map_iff in Hl as (e & <- & He).
    rewrite Forall_forall in H10. exact (hb_aentry_fp_off_x ly S Hp W mem md e HAR (H10 e He) r Hr).
Qed.
End fo.

Definition hb_INV_P_x (cx : lfcx) (t : Z) : world segs -> config -> Prop :=
  fun W c => exists regs mem md, c = cfg_at segs (fr_B0 + AF_LLVM_pick) regs mem md /\
    jt_rom W mem /\ lcut_x B NP G_fr fr_FP PST ARx LSx RINV cx [] t (hb_lregs_P cx t) regs mem md W.

(* the AR file's :497 hb_aout_clear: the controller's stream after g_nout := 0 (O = []), over ARx *)
Lemma hb_aout_clear_x : forall ly S W mem md mem' c O mx no cap out,
  ARx ly S [] W mem md ->
  (forall a, hb_offw 6131264 6131272 a -> abyte_kept W mem W mem' a) ->
  (forall a, writable_at segs (arm W mem) a -> writable_at segs (arm W mem') a) ->
  val_mem segs (arm W mem') (rg_nout fr_RG) 8 0 -> hb_rng_off 6131264 6131272 (as_errno B, as_errno B + 4) ->
  aout_at B fr_RG ly S W mem c O mx no cap out -> aout_at B fr_RG ly S W mem' c [] mx 0 cap out.
Proof.
  intros ly S W mem md mem' c O mx no cap out HAR KB KW HN0 HER
    (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11 & H12 & H13 & H14 & H15 & H16 & H17 & H18 &
     H19 & H20 & H21 & H22 & H23 & H24 & H25 & H26).
  assert (KK : forall x, 0 <= x < 6131264 \/ 6131272 <= x < 2 ^ 64 -> abyte_kept W mem W mem' x)
    by (intros x Hx; apply KB; split; lia).
  unfold aout_at. cbn [rg_send_max rg_nout rg_capout rg_out rg_client rg_client_broken rg_send_dead rg_send_eintr fr_RG
    fr_globals_b] in *.
  pose proof HER as HER'. unfold hb_rng_off, hb_offw in HER'. cbn [fst snd] in HER'.
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
  apply (hb_blk_off_x 6131264 6131272 ltac:(lia) ltac:(lia) ly S [] W mem md out cap x HAR Hin ltac:(lia)).
  pose proof (req_size_pos cap ltac:(lia)) as [_ Hq]. lia.
Qed.

(* every cut fact but the journal and the model's stream, across a store to g_nout only (B's frame: no `full` flag,
   the slots F+32 .. F+184) *)
Lemma hb_store_kept_x : forall cx ly3 S3 W mem md mem' fpos m,
  lf_base_x B MT XM_LIB RLO RHI fr_live_pre LIBROOM NP G_fr ARx cx [] ->
  ARx ly3 S3 [] W mem md -> In (1, fpos) (frames S3) ->
  (forall x : word, ~ (rg_nout fr_RG <= bv_unsigned x < rg_nout fr_RG + 8) -> mrestrict (w_H W) mem' x = mrestrict (w_H W) mem x) ->
  mem_grows (mrestrict (w_H W) mem) (mrestrict (w_H W) mem') ->
  val_mem segs (arm W mem') (rg_nout fr_RG) 8 0 ->
  aframe_at cx (frame_addr ly3 1 fpos) W mem -> amodel_at B ly3 S3 W mem m -> ainput_at B cx ly3 S3 W mem ->
  rom_view segs W mem -> jt_rom W mem ->
  aframe_at cx (frame_addr ly3 1 fpos) W mem' /\ amodel_at B ly3 S3 W mem' (lm_clear_O m) /\
  ainput_at B cx ly3 S3 W mem' /\ rom_view segs W mem' /\ jt_rom W mem'.
Proof.
  intros cx ly3 S3 W mem md mem' fpos m HB HAR Hfp HKX HGR HN0 HFR HMOD HIN HRV HJT.
  rewrite hb_nout_val in HKX, HN0.
  pose proof (hb_kept_off W mem mem' 6131264 (6131264 + 8) HKX HGR) as KB. change (6131264 + 8) with 6131272 in KB.
  pose proof (hb_writable_kept W mem mem' HGR) as KW.
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  pose proof HB as (HAI & HPRE & Hra & Ha0 & Ha1 & Hblk0 & Hlen & _).
  pose proof HPRE as (HAR0 & Hra0 & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
  pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
  unfold YCfn.LLVMF_STK in *.
  pose proof (Z.mod_pos_bound (spZ (c_regs cx) - 320) 32 ltac:(lia)) as HFm.
  assert (HF : spZ (c_regs cx) - 351 <= lf_F cx <= spZ (c_regs cx) - 320) by (unfold lf_F; lia).
  destruct (frames_bounds_x _ _ ARx LAWS _ _ [] _ _ _ _ _ HAR Hfp) as (HFF0 & HFF1 & _).
  pose proof (frm_off_imgP_x B ARx LAWS (fr_img_cover_x B ARx LAWS) _ _ [] _ _ _ _ _ HAR Hfp) as HFFi. unfold off_img in HFFi.
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
    unfold amodel_at. cbn [lm_hs lm_G lm_es lm_c lm_O lm_mx lm_cap lm_out lm_gn lm_nfd lm_clear_O].
    split; [exact Hhs4|].
    split.
    { intros i Hi. specialize (Hslots i Hi). unfold aslot in *.
      assert (HHA : hb_rng_off 6131264 6131272 (rg_s fr_RG + ASRC * Z.of_nat i, rg_s fr_RG + ASRC * Z.of_nat i + ASRC)).
      { intros x Hx. cbn [fst snd rg_s fr_RG fr_globals_b] in Hx. unfold ASRC in Hx. split; lia. }
      destruct (nth i (lm_hs m) None) as [h|].
      - apply (asrc_at_kept B ly3 S3 W mem ly3 S3 W mem' _ h Hslots).
        + apply (hb_akept W mem mem' 6131264 6131272); [exact KB|].
          exact (hb_asrc_fp_off_x 6131264 6131272 ltac:(lia) ltac:(lia) ly3 S3 [] W mem md _ h HAR Hslots HHA).
        + exact (hb_asrc_blks_in ly3 S3 W mem _ h Hslots).
      - destruct Hslots as [Hz Hw]. split.
        + apply (akept_garr8 W mem); [|exact Hz]. intros x Hx. rewrite repeat_length in Hx. apply KB. apply HHA.
          cbn [fst snd]. unfold ASRC in *. lia.
        + apply (akept_awr W mem); [|exact Hw]. intros x Hx. apply KB. apply HHA. cbn [fst snd]. lia. }
    split.
    { apply (arelay_at_kept B fr_RG ly3 S3 W mem ly3 S3 W mem' _ _ Hrel).
      + apply (hb_akept W mem mem' 6131264 6131272); [exact KB|].
        apply (hb_arelay_fp_off_x 6131264 6131272 ltac:(lia) ltac:(lia) fr_RG ly3 S3 [] W mem md _ _ HAR Hrel);
          intros x Hx; cbn [fst snd rg_src rg_nsrc rg_capsrc fr_RG fr_globals_b] in Hx; split; lia.
      + exact (hb_arelay_blks_in fr_RG ly3 S3 W mem _ _ Hrel). }
    split.
    { eapply (hb_aout_clear_x ly3 S3 W mem md mem' _ _ _ _ _ _ HAR KB KW); [rewrite hb_nout_val; exact HN0 | | exact Hout].
      intros x Hx. cbn [fst snd] in Hx. pose proof HERRNO as (He0 & He1 & He2).
      rewrite hb_nout_val in He2. split; lia. }
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
    apply (hb_blk_off_x 6131264 6131272 ltac:(lia) ltac:(lia) ly3 S3 [] W mem md (c_p cx) (c_n cx) x HAR Hin ltac:(lia)).
    pose proof (req_size_pos (c_n cx) ltac:(lia)) as [_ Hq]. lia.
  - (* .rodata *)
    intros a Ha. pose proof (hb_rom_low a Ha) as Hrl.
    destruct (Z_lt_le_dec a 6131264) as [Hlt | Hge].
    + rewrite (proj1 (KB a ltac:(split; lia))). apply HRV. exact Ha.
    + destruct (Z_lt_le_dec a 6131272) as [Hlt2 | Hge2].
      * exfalso. exact (hb_not_rom 6131264 6131272 a hb_nout_not_rom ltac:(lia) Ha).
      * rewrite (proj1 (KB a ltac:(split; lia))). apply HRV. exact Ha.
  - (* the jump table *)
    intros i Hi. apply (akept_vm W mem); [|exact (HJT i Hi)].
    intros x Hx. apply KB. unfold fr_jtab in Hx. cbn in Hx. split; lia.
Qed.
(* the fake frame's flag word (lcut's conjunct after aframe_at) across a store to g_nout only *)
Lemma hb_flag_kept_x : forall ly3 S3 W mem md mem' fpos,
  ARx ly3 S3 [] W mem md -> In (1, fpos) (frames S3) ->
  (forall x : word, ~ (rg_nout fr_RG <= bv_unsigned x < rg_nout fr_RG + 8) -> mrestrict (w_H W) mem' x = mrestrict (w_H W) mem x) ->
  mem_grows (mrestrict (w_H W) mem) (mrestrict (w_H W) mem') ->
  sv8 W mem (frame_addr ly3 1 fpos + 120) (flag_addr ly3 1 fpos) ->
  sv8 W mem' (frame_addr ly3 1 fpos + 120) (flag_addr ly3 1 fpos).
Proof.
  intros ly3 S3 W mem md mem' fpos HAR Hfp HKX HGR Hv.
  rewrite hb_nout_val in HKX.
  pose proof (hb_kept_off W mem mem' 6131264 (6131264 + 8) HKX HGR) as KB. change (6131264 + 8) with 6131272 in KB.
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  destruct (frames_bounds_x _ _ ARx LAWS _ _ [] _ _ _ _ _ HAR Hfp) as (HFF0 & HFF1 & _).
  pose proof (frm_off_imgP_x B ARx LAWS (fr_img_cover_x B ARx LAWS) _ _ [] _ _ _ _ _ HAR Hfp) as HFFi. unfold off_img in HFFi.
  change (fs_frame_bytes 1) with 128 in HFF1, HFFi.
  unfold sv8 in *. apply (akept_vm W mem); [|exact Hv].
  intros x Hx. cbn in Hx. apply KB. split; lia.
Qed.

(* the cut facts after walk 1's store to g_nout, at the run's final memory and registers *)
Lemma hb_w1_lcut_x : forall cx t W mem md mem' md' ly3 S3 k m fpos
    (R : lmod -> Z -> bvmap 5 word -> world segs -> (word -> option byte) -> Prop) regs',
  lf_base_x B MT XM_LIB RLO RHI fr_live_pre LIBROOM NP G_fr ARx cx [] ->
  ajournal_gx_x segs B PST ARx G_fr 0 [] YCfn.LLVMF_STK (spZ (c_regs cx)) (lf_FP fr_FP cx) (c_ly cx) (c_S cx) [] (c_W cx)
    (c_mem cx) (c_md cx) [(1, fpos)] ly3 S3 [] W mem md k ->
  ajournal_gx_x segs B PST ARx G_fr 0 [] YCfn.LLVMF_STK (spZ (c_regs cx)) (lf_FP fr_FP cx) (c_ly cx) (c_S cx) [] (c_W cx)
    (c_mem cx) (c_md cx) [(1, fpos)] ly3 S3 [] W mem' md' k ->
  (forall x : word, ~ (rg_nout fr_RG <= bv_unsigned x < rg_nout fr_RG + 8) -> mrestrict (w_H W) mem' x = mrestrict (w_H W) mem x) ->
  mem_grows (mrestrict (w_H W) mem) (mrestrict (w_H W) mem') ->
  val_mem segs (arm W mem') (rg_nout fr_RG) 8 0 ->
  aframe_at cx (frame_addr ly3 1 fpos) W mem -> sv8 W mem (frame_addr ly3 1 fpos + 120) (flag_addr ly3 1 fpos) ->
  amodel_at B ly3 S3 W mem m -> ainput_at B cx ly3 S3 W mem ->
  rom_view segs W mem -> ablocks_sep B fr_FP cx m ly3 S3 -> LSx cx t m ly3 S3 -> NP S3 -> RINV cx t m -> jt_rom W mem ->
  R (lm_clear_O m) (frame_addr ly3 1 fpos) regs' W mem' ->
  jt_rom W mem' /\ lcut_x B NP G_fr fr_FP PST ARx LSx RINV cx [] t R regs' mem' md' W.
Proof.
  intros cx t W mem md mem' md' ly3 S3 k m fpos R regs' HB HJ HJ' HKX HGR HN0 HFR HFL HMOD HIN HRV HSEP HLS HNP HRI HJT HR.
  pose proof (ajournal_gx_AR_x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as HAR.
  assert (Hfp : In (1, fpos) (frames S3)).
  { destruct (ajournal_gx_inner_x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as (memS & HJi & _).
    pose proof HJi as (_ & _ & _ & _ & _ & Hfrs & _). rewrite Hfrs. left. reflexivity. }
  destruct (hb_store_kept_x cx ly3 S3 W mem md mem' fpos m HB HAR Hfp HKX HGR HN0 HFR HMOD HIN HRV HJT)
    as (F' & M' & I' & RV' & JT').
  split; [exact JT'|].
  exists [(1, fpos)], ly3, S3, [], k, (lm_clear_O m), fpos.
  split; [exact HJ'|]. split; [reflexivity|]. split; [exact F'|].
  split; [exact (hb_flag_kept_x ly3 S3 W mem md mem' fpos HAR Hfp HKX HGR HFL)|].
  split; [exact M'|]. split; [exact I'|].
  split; [exact RV'|]. split; [exact HSEP|]. split; [apply LS_head_nout; exact HLS|]. split; [exact HNP|].
  split; [apply RI_head_nout; exact HRI|]. exact HR.
Qed.
(* the AR file's Section-local Ltacs (:737-790), restated: writes of walk 1's runs (g_nout's 8 bytes only) *)
Ltac hb_wr E26 :=
  let a := fresh "a" in let r := fresh "r" in let Hin := fresh "Hin" in let Hr := fresh "Hr" in
  intros a (r & Hin & Hr); vm_compute in Hin;
  repeat (destruct Hin as [<- | Hin]; [cbn [YP09.r_base YP09.r_wlo YP09.r_whi YP09.base_val] in Hr;
    first [ lia
          | rewrite ?ew_ewset_other in Hr by lia; rewrite E26, unsigned_lit_small in Hr by (unfold HI_G_NOUT; lia);
            rewrite hb_nout_val; unfold HI_G_NOUT in Hr; lia ] |]);
  destruct Hin.
Ltac hb_awr E26 HGn :=
  lazymatch goal with |- awr_ok_x ?Ev ?rs ?G ?XO ?OUT ?STK ?sp0 ?FP ?b0 ?bc ?ly ?own =>
    let rs' := eval vm_compute in rs in change (awr_ok_x Ev rs' G XO OUT STK sp0 FP b0 bc ly own) end;
  repeat first
   [ apply awr_ok_x_nil
   | apply awr_ok_x_cons; [let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha;
       cbn [YP09.r_base YP09.r_wlo YP09.r_whi YP09.base_val] in Ha;
       first [ lia
             | right; left; apply HGn; rewrite ?ew_ewset_other in Ha by lia;
               rewrite E26, unsigned_lit_small in Ha by (unfold HI_G_NOUT; lia); rewrite hb_nout_val;
               unfold HI_G_NOUT in Ha; lia ] |] ].
(* g_nout = 0 after the store, read off the run's g_nout region (the third region) *)
Ltac hb_nout0 HS E26 HN0 :=
  lazymatch type of HS with st_ok_pi ?sg ?vl ?Ev ?ss (restrict ?H ?ms) =>
    let r := eval vm_compute in (nth 2 (ss_mem ss) hb_rnout) in
    let HRN := fresh "HRN" in
    pose proof (st_ok_pi_region_nth Ev ss (restrict H ms) 2 r HS ltac:(vm_compute; reflexivity)) as HRN;
    cbn [ms_mem restrict] in HRN;
    pose proof (field_of_region Ev _ 26 HI_G_NOUT _ _ _ _ _ (-1892) 8 (SLit 0) 0 HRN
      ltac:(rewrite ?ew_ewset_other by lia; rewrite E26; apply unsigned_lit_small; unfold HI_G_NOUT; lia)
      ltac:(left; reflexivity) eq_refl ltac:(lia) ltac:(lia)) as HN0;
    change (HI_G_NOUT + -1892) with (rg_nout fr_RG) in HN0; change (N.to_nat 8) with 8%nat in HN0; clear HRN
  end.
Ltac hb_upd E26 MEQ MG :=
  lazymatch goal with HFx : frame_of ?Ev ?rs (mrestrict ?H (ms_mem ?ms0)) (mrestrict ?H (ms_mem ?ms1)) |- _ =>
  lazymatch goal with HGx : mem_grows (mrestrict H (ms_mem ms0)) (mrestrict H (ms_mem ms1)) |- _ =>
    let MEQn := fresh "MEQn" in let MGn := fresh "MGn" in
    lazymatch type of MEQ with forall x, _ -> mrestrict _ _ x = mrestrict _ ?m0 x =>
    assert (MEQn : forall x : word, ~ (rg_nout fr_RG <= bv_unsigned x < rg_nout fr_RG + 8) ->
        mrestrict H (ms_mem ms1) x = mrestrict H m0 x)
      by (let x := fresh "x" in let Hx := fresh "Hx" in intros x Hx;
          rewrite (hb_frame_nout Ev rs _ _ HFx ltac:(hb_wr E26) x Hx); exact (MEQ x Hx)) end;
    pose proof (hb_mem_grows_trans _ _ _ MG HGx) as MGn;
    clear MEQ MG HFx HGx; rename MEQn into MEQ; rename MGn into MG end end;
  repeat match goal with H : frame_of _ _ _ _ |- _ => clear H end.
Ltac hb_prreg_raw HS r Hr :=
  lazymatch type of HS with st_ok_pi ?segs ?val ?E ?ss (restrict ?H ?ms) =>
    pose proof (st_ok_pi_restrict_reg H E ss ms r HS) as Hr;
    let e := eval vm_compute in (sr_get (ss_regs ss) r) in change (sr_get (ss_regs ss) r) with e in Hr;
    cbn [ms_regs restrict] in Hr end.
Ltac hb_mem HF Em := lazymatch type of HF with frame_of ?E ?rs ?m ?m' =>
  pose proof (frame_of_read_only E rs m m' ltac:(vm_compute; reflexivity) HF) as Em end.
Ltac hb_in := cbn [In]; repeat (first [left; reflexivity | right]).
(* the AR file's :799 hb_w1 over ARx: walk 1, the head (0x845e0) to D, P or X *)
Lemma hb_w1_x : forall cx t W c, lf_base_x B MT XM_LIB RLO RHI fr_live_pre LIBROOM NP G_fr ARx cx [] -> INV_H_x B NP G_fr fr_FP PST ARx LSx RINV cx [] t W c ->
  SRr segs W c (fun W' c' => (exists op, 0 <= op <= 9 /\ INV_D_x B NP G_fr fr_FP PST ARx LSx RINV cx [] t op W' c') \/
    hb_INV_P_x cx t W' c' \/ INV_X_x B NP G_fr fr_FP PST ARx LSx RINV cx [] W' c').
Proof.
  intros cx t W c HB (regs & mem & md & -> & HROM &
    (own & ly3 & S3 & Hp3 & k & m & fpos & HJ & -> & HFR & HFL & HMOD & HIN & HRV & HSEP & HLS & HNP & HRI & HR)).
  destruct HR as ((R2 & R8 & R9 & R18 & R19 & R23 & R24 & R26 & R27 & R3 & R4) & R25 & R21 & R22 & Ht & Hk).
  pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  pose proof HB as (HAI & HPRE & Hra & Ha0 & Ha1 & Hblk0 & Hlen & _).
  pose proof HPRE as (HAR0 & Hra0 & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
  pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
  pose proof (ajournal_gx_AR_x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as HAR.
  (* the cut's ghost list is [] (HP0 at the journal's end state) *)
  pose proof (HP0 _ _ _ _ _ _ HAR) as Ehp3. subst Hp3.
  unfold cfg_at. change (w64 (fr_B0 + AF_LLVM_head)) with (Z_to_bv 64 (BASE + AF_LLVM_head)).
  destruct (Z.eq_dec (lm_k m) (c_n cx)) as [Hkn | Hkn].
  { (* in.n = 0: `beqz s5` to the shutdown block *)
    assert (R21' : getr regs 21 = w64 0) by (rewrite R21, Hkn, Z.sub_diag; reflexivity).
    destruct (hb_entry0 W regs mem R23 R21' R27) as [HS SHOK].
    remember (Eimg (Ereg regs [])) as E eqn:HE.
    assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
    assert (HAE : env_agree 32 (Ereg regs []) E)
      by (rewrite HE; split; [intros q Hq; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
    clear HE.
    paj_run_to_tok_x RUNTO HS HJ SHOK hb_Bspan AF_LLVM_exit.
    { apply awr_ok_x_nil. }
    hb_mem HF Em.
    pose proof (regs_kept_of_st_ok_pi (PI := PB_fr) _ _ _ regs [] HB_KEPTX HS HAE ltac:(vm_compute; reflexivity)) as KR.
    cbn [ms_regs restrict] in KR.
    pmkst HS. rewrite Em in *. clear HF HFr HG0.
    apply SRr_ret. right; right.
    lazymatch goal with |- INV_X_x _ _ _ _ PST ARx _ _ _ [] _ {| cfg_ms := mkst ?r _ _ _; cfg_model := ?d |} => exists r, mem, d, t end.
    split; [reflexivity|]. split; [exact HROM|].
    exists [(1, fpos)], ly3, S3, [], k, m, fpos.
    split; [exact HJ|]. split; [reflexivity|]. split; [exact HFR|]. split; [exact HFL|].
    split; [exact HMOD|]. split; [exact HIN|]. split; [exact HRV|]. split; [exact HSEP|].
    split; [exact HLS|]. split; [exact HNP|]. split; [exact HRI|].
    unfold lregs_X.
    repeat split; first [ match goal with |- getr _ ?r = _ => rewrite (KR r ltac:(hb_in)) end; assumption | lia ]. }
  pose proof HIN as [[[Hn00 _] | [Hnr Hblk]] Hgarr]; [lia|].
  destruct (alx_blocks _ _ ARx LAWS _ _ [] _ _ _ _ _ HAR Hblk) as (Hp16 & Hp4096 & Hpceil & Hpia & _ & _).
  pose proof (hb_blk_imgP_x _ _ _ _ _ _ _ _ HAR Hblk ltac:(lia)) as Hpimg.
  pose proof (req_size_pos (c_n cx) ltac:(lia)) as [_ Hreq].
  pose proof (Z.mod_pos_bound (spZ (c_regs cx) - 320) 32 ltac:(lia)) as HFm.
  assert (HFb : spZ (c_regs cx) - 351 <= lf_F cx <= spZ (c_regs cx) - 320) by (unfold lf_F; lia).
  unfold YCfn.LLVMF_STK in *.
  destruct (hb_in_byte cx (arm W mem) (lm_k m) Hgarr ltac:(lia)) as [MB Rb0].
  pose proof HFR as (FS & FW & F32 & F40 & F48 & F56 & F64 & F72 & F80 & F96 & F104 & F120 & F128 & F136 & F152 &
    F184 & FF0 & FF8 & FF16 & FFw & FFsh & FFshw).
  pose proof HMOD as (Hhs4 & Hslots & Hrel & Hout & Hgone & Hlock & Hwake & Hnfd & Hnfdw & Hnfdr).
  pose proof Hout as (O1 & O2 & O3 & O4 & _).
  destruct (hb_entry1 W regs mem (c_n cx - lm_k m) (c_p cx + lm_k m) (lf_F cx) (in_byte cx (lm_k m)) R23 R9 R21 R22 R26 R27
    ltac:(lia) ltac:(lia) Rb0 ltac:(lia) ltac:(lia) MB F136 O4 ltac:(lia)
    ltac:(rewrite hb_nout_val; lia) ltac:(rewrite hb_nout_val; lia)
    ltac:(apply (range_addressable_of_block_hp0_x segs B ARx LAWS HP0 ly3 S3 [] W mem md (c_p cx) (c_n cx)); [exact HAR | exact Hblk | lia | lia])
    ltac:(unfold in_app, SHADOW_OFF, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *; lia)) as [HS SHOK].
  remember (Eimg (Ereg regs (hb_x1 (in_byte cx (lm_k m))))) as E eqn:HE.
  assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
  assert (EEo : forall m (rr : bv 5), Z.of_nat m = bv_unsigned rr -> ew E m = getr regs rr)
    by (intros m0 rr Hm; subst E; pose proof (bv_unsigned_in_range 5 rr) as Hr5; change (bv_modulus 5) with 32 in Hr5;
        rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_nat; exact Hm).
  assert (E21 : ew E 21 = Z_to_bv 64 (c_n cx - lm_k m)) by (rewrite (EEo 21%nat 21%bv eq_refl); exact R21).
  assert (E22 : ew E 22 = Z_to_bv 64 (c_p cx + lm_k m)) by (rewrite (EEo 22%nat 22%bv eq_refl); exact R22).
  assert (E26 : ew E 26 = Z_to_bv 64 HI_G_NOUT) by (rewrite (EEo 26%nat 26%bv eq_refl); exact R26).
  assert (E32 : ew E 32 = Z_to_bv 64 (in_byte cx (lm_k m)))
    by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
  assert (HAE : env_agree 32 (Ereg regs (hb_x1 (in_byte cx (lm_k m)))) E)
    by (rewrite HE; split; [intros m0 Hm; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
  clear HE.
  pose proof HJ as HJ0.
  pose proof (Z.mod_pos_bound (in_byte cx (lm_k m)) 10 ltac:(lia)) as Rop.
  assert (UOP : forall Ev, ew Ev 32 = ew E 32 -> U Ev hb_opsv = in_byte cx (lm_k m) mod 10)
    by (intros Ev HEv; apply hb_op_U; [rewrite HEv; exact E32 | exact Rb0]).
  (* the head test, the PTR_INC trap, the shadow check and read of in.p[0], op = in.p[0] % 10, g_nout = 0, to the
     class test *)
  paj_run_tok_x RUN HS HJ SHOK hb_Bspan.
  { hb_awr E26 HGnout. }
  lazymatch goal with HFx : frame_of _ _ (mrestrict _ mem) (mrestrict _ (ms_mem ?ms1)) |- _ =>
    assert (MEQ1 : forall x : word, ~ (rg_nout fr_RG <= bv_unsigned x < rg_nout fr_RG + 8) ->
        mrestrict (w_H W) (ms_mem ms1) x = mrestrict (w_H W) mem x)
      by (apply (hb_frame_nout E (ss_mem hb_ss1)); [exact HFx | hb_wr E26]) end.
  lazymatch goal with H : mem_grows (mrestrict _ mem) _ |- _ => rename H into MG1 end.
  rename MEQ1 into MEQ. rename MG1 into MG.
  repeat match goal with H : frame_of _ _ _ _ |- _ => clear H end.
  lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
    assert (UO : U Ev hb_opsv = in_byte cx (lm_k m) mod 10) by (apply UOP; rewrite !ew_ewset_other by lia; reflexivity);
    assert (HAE1 : env_agree 32 (Ereg regs (hb_x1 (in_byte cx (lm_k m)))) Ev)
      by (split; [intros m0 Hm; rewrite !ew_ewset_other by lia; exact (proj1 HAE m0 Hm) | rewrite !ed_ewset; exact (proj2 HAE)])
  end.
  psrr_branch_tok RUN BR HS SHOK hb_Bspan.
  - (* op in 1..4: on to the pick *)
    unfold hb_opsv in UO. rewrite branch_ltu_U, U_SAlu, UO, hb_cls_ltu in Hc by lia.
    apply andb_prop in Hc as [Hc1 Hc2]. apply Z.leb_le in Hc1, Hc2. fold hb_opsv in UO.
    paj_run_to_tok_x RUNTO HS HJ SHOK hb_Bspan AF_LLVM_pick.
    { hb_awr E26 HGnout. }
    hb_upd E26 MEQ MG.
    pose proof (regs_kept_of_st_ok_pi _ _ _ regs _ HB_KEPT1 HS HAE1 ltac:(vm_compute; reflexivity)) as KR.
    cbn [ms_regs restrict] in KR.
    prreg HS (23%bv : bv 5) Q23. prreg HS (20%bv : bv 5) Q20. prreg HS (6%bv : bv 5) Q6.
    hb_prreg_raw HS (11%bv : bv 5) Q11.
    prreg HS (21%bv : bv 5) Q21.
    hb_nout0 HS E26 HN0.
    pmkst HS.
    apply SRr_ret. right; left.
    lazymatch goal with |- hb_INV_P_x _ _ _ {| cfg_ms := mkst ?r _ ?mm _; cfg_model := ?d |} => exists r, mm, d end.
    split; [reflexivity|].
    apply (hb_w1_lcut_x cx t W mem md _ _ ly3 S3 k m fpos (hb_lregs_P cx t) _ HB HJ0 HJ MEQ MG HN0 HFR HFL HMOD HIN HRV HSEP HLS HNP HRI HROM).
    unfold hb_lregs_P. cbn [lm_k lm_O lm_clear_O].
    rewrite E21 in Q21, Q6. rewrite E22 in Q20. rewrite unsigned_lit_small in Q20, Q6 by lia.
    split; [unfold lregs_common; repeat split; first [ rewrite Q23; reflexivity
      | match goal with |- getr _ ?r = _ => rewrite (KR r ltac:(hb_in)) end; assumption ]|].
    split; [rewrite (KR 25%bv ltac:(hb_in)); exact R25|].
    split; [exact Ht|]. split; [lia|]. split; [reflexivity|].
    split; [exact Q21|].
    split; [rewrite (KR 22%bv ltac:(hb_in)); exact R22|].
    split; [rewrite Q11; apply hb_sv_of_U; [exact UO | lia]|].
    split; [apply hb_picks14; exact (conj Hc1 Hc2)|].
    split; [rewrite Q20; unfold w64; f_equal; lia|].
    rewrite Q6; unfold w64; f_equal; lia.
  - unfold hb_opsv in UO. rewrite branch_ltu_U, U_SAlu, UO, hb_cls_ltu in Hc by lia. fold hb_opsv in UO.
    rename Hc into Hcls.
    paj_run_tok_x RUN HS HJ SHOK hb_Bspan.
    { hb_awr E26 HGnout. }
    hb_upd E26 MEQ MG.
    lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
      assert (UO2 : U Ev hb_opsv = in_byte cx (lm_k m) mod 10) by (apply UOP; rewrite ?ew_ewset_other by lia; reflexivity);
      assert (HAE2 : env_agree 32 (Ereg regs (hb_x1 (in_byte cx (lm_k m)))) Ev)
        by (split; [intros m0 Hm; rewrite ?ew_ewset_other by lia; exact (proj1 HAE m0 Hm) | rewrite ?ed_ewset; exact (proj2 HAE)])
    end.
    clear UO HAE1. rename UO2 into UO. rename HAE2 into HAE1.
    psrr_branch_tok RUN BR HS SHOK hb_Bspan.
    + (* op not in 1..4, op <> 6: no source (0x84758 li s5,0); to the dispatch *)
      unfold hb_opsv in UO. rewrite branch_ne_U, UO, U_lit in Hc by lia. fold hb_opsv in UO.
      apply negb_true_iff, Z.eqb_neq in Hc.
      pose proof (hb_picks_no (in_byte cx (lm_k m) mod 10) ltac:(lia) Hcls Hc) as Hpk.
      paj_run_to_tok_x RUNTO HS HJ SHOK hb_Bspan AF_LLVM_dispatch.
      { hb_awr E26 HGnout. }
      hb_upd E26 MEQ MG.
      pose proof (regs_kept_of_st_ok_pi _ _ _ regs _ HB_KEPT1 HS HAE1 ltac:(vm_compute; reflexivity)) as KR.
      cbn [ms_regs restrict] in KR.
      prreg HS (23%bv : bv 5) Q23. prreg HS (20%bv : bv 5) Q20. prreg HS (6%bv : bv 5) Q6.
      hb_prreg_raw HS (11%bv : bv 5) Q11.
      prreg HS (21%bv : bv 5) Q21.
      hb_nout0 HS E26 HN0.
      pmkst HS.
      apply SRr_ret. left. exists (in_byte cx (lm_k m) mod 10). split; [lia|].
      lazymatch goal with |- INV_D_x _ _ _ _ PST ARx _ _ _ [] _ _ _ {| cfg_ms := mkst ?r _ ?mm _; cfg_model := ?d |} => exists r, mm, d end.
      split; [reflexivity|].
      split; [rewrite Q11; apply hb_sv_of_U; [exact UO | lia]|].
      rewrite ?wvb_collapse in HJ.
      split; [exists [(1, fpos)], ly3, S3, [], k; exact HJ|].
      apply (hb_w1_lcut_x cx t W mem md _ _ ly3 S3 k m fpos (lregs_D B cx t) _ HB HJ0 HJ MEQ MG HN0 HFR HFL HMOD HIN HRV HSEP HLS HNP HRI HROM).
      unfold lregs_D. cbv zeta. cbn [lm_k lm_O lm_clear_O]. rewrite Hpk. cbv iota.
      rewrite E21 in Q6. rewrite E22 in Q20. rewrite unsigned_lit_small in Q20, Q6 by lia.
      split; [unfold lregs_common; repeat split; first [ rewrite Q23; reflexivity
        | match goal with |- getr _ ?r = _ => rewrite (KR r ltac:(hb_in)) end; assumption ]|].
      split; [rewrite (KR 25%bv ltac:(hb_in)); exact R25|].
      split; [exact Ht|]. split; [lia|]. split; [reflexivity|].
      split; [rewrite Q11; apply hb_sv_of_U; [exact UO | lia]|].
      split; [rewrite Q20; unfold w64; f_equal; lia|].
      split; [rewrite Q6; unfold w64; f_equal; lia|].
      rewrite Q21. reflexivity.
    + (* op = 6: on to the pick *)
      unfold hb_opsv in UO. rewrite branch_ne_U, UO, U_lit in Hc by lia. fold hb_opsv in UO.
      apply negb_false_iff, Z.eqb_eq in Hc.
      paj_run_to_tok_x RUNTO HS HJ SHOK hb_Bspan AF_LLVM_pick.
      { hb_awr E26 HGnout. }
      hb_upd E26 MEQ MG.
      pose proof (regs_kept_of_st_ok_pi _ _ _ regs _ HB_KEPT1 HS HAE1 ltac:(vm_compute; reflexivity)) as KR.
      cbn [ms_regs restrict] in KR.
      prreg HS (23%bv : bv 5) Q23. prreg HS (20%bv : bv 5) Q20. prreg HS (6%bv : bv 5) Q6.
      hb_prreg_raw HS (11%bv : bv 5) Q11.
      prreg HS (21%bv : bv 5) Q21.
      hb_nout0 HS E26 HN0.
      pmkst HS.
      apply SRr_ret. right; left.
      lazymatch goal with |- hb_INV_P_x _ _ _ {| cfg_ms := mkst ?r _ ?mm _; cfg_model := ?d |} => exists r, mm, d end.
      split; [reflexivity|].
      apply (hb_w1_lcut_x cx t W mem md _ _ ly3 S3 k m fpos (hb_lregs_P cx t) _ HB HJ0 HJ MEQ MG HN0 HFR HFL HMOD HIN HRV HSEP HLS HNP HRI HROM).
      unfold hb_lregs_P. cbn [lm_k lm_O lm_clear_O].
      rewrite E21 in Q21, Q6. rewrite E22 in Q20. rewrite unsigned_lit_small in Q20, Q6 by lia.
      split; [unfold lregs_common; repeat split; first [ rewrite Q23; reflexivity
        | match goal with |- getr _ ?r = _ => rewrite (KR r ltac:(hb_in)) end; assumption ]|].
      split; [rewrite (KR 25%bv ltac:(hb_in)); exact R25|].
      split; [exact Ht|]. split; [lia|]. split; [reflexivity|].
      split; [exact Q21|].
      split; [rewrite (KR 22%bv ltac:(hb_in)); exact R22|].
      split; [rewrite Q11; apply hb_sv_of_U; [exact UO | lia]|].
      split; [rewrite Hc; reflexivity|].
      split; [rewrite Q20; unfold w64; f_equal; lia|].
      rewrite Q6; unfold w64; f_equal; lia.
Qed.

(* the AR file's :1042 hb_gs_shadow over ARx: g_s's shadow is zero (HZS), read through the zero-shadow law *)
Lemma hb_gs_shadow_x : forall ly S W mem md, ARx ly S [] W mem md ->
  forall j, 0 <= j < 4 -> val_mem segs (mrestrict (w_H W) mem) (hb_shgs + 12 * j) 1 0.
Proof.
  intros ly S W mem md HAR j Hj. destruct HZS as ([lo len] & Hin & H8 & Hlo & Hhi). cbn [fst snd] in *.
  assert (Hz : zero_shadow (aview segs (w_H W) mem) SHADOW_OFF lo len).
  { apply (alx_zshadow _ _ ARx LAWS ly S [] W mem md (lo, len) HAR). unfold zero_shadow_ranges. right. exact Hin. }
  change (rg_s fr_RG) with 6131296 in *. unfold ASRC in Hhi.
  pose proof (Z.div_mod lo 8 ltac:(lia)) as Dl. rewrite H8, Z.add_0_r in Dl.
  pose proof (Z.mul_div_le len 8 ltac:(lia)) as Dn.
  specialize (Hz (766412 - lo / 8 + 12 * j) ltac:(split; [lia | lia])).
  apply hb_vm0_of_aview. rewrite hb_shgs_val.
  replace (2148217292 + 12 * j) with (shadow_of_addr SHADOW_OFF lo + (766412 - lo / 8 + 12 * j))
    by (unfold shadow_of_addr, SHADOW_OFF; lia).
  exact Hz.
Qed.
(* the AR file's :1184 / :1197 Section-local Ltacs, restated *)
Ltac hb_meq mem0 :=
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
Ltac hb_awr0 :=
  lazymatch goal with |- awr_ok_x ?Ev ?rs ?G ?XO ?OUT ?STK ?sp0 ?FP ?b0 ?bc ?ly ?own =>
    let rs' := eval vm_compute in rs in change (awr_ok_x Ev rs' G XO OUT STK sp0 FP b0 bc ly own) end;
  repeat first
   [ apply awr_ok_x_nil
   | apply awr_ok_x_cons; [let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha;
       cbn [YP09.r_base YP09.r_wlo YP09.r_whi YP09.base_val] in Ha; lia |] ].

Lemma hb_w2_x : forall cx t W c, lf_base_x B MT XM_LIB RLO RHI fr_live_pre LIBROOM NP G_fr ARx cx [] -> hb_INV_P_x cx t W c ->
  SRr segs W c (fun W' c' => (exists op, 0 <= op <= 9 /\ INV_D_x B NP G_fr fr_FP PST ARx LSx RINV cx [] t op W' c') \/
    INV_A_x B NP G_fr fr_FP PST ARx LSx RINV 1 cx [] t W' c' \/ INV_H_x B NP G_fr fr_FP PST ARx LSx RINV cx [] (t + 1) W' c' \/
    INV_X_x B NP G_fr fr_FP PST ARx LSx RINV cx [] W' c').
Proof.
  intros cx t W c HB (regs & mem & md & -> & HROM &
    (own & ly3 & S3 & Hp3 & k & m & fpos & HJ & -> & HFR & HFL & HMOD & HIN & HRV & HSEP & HLS & HNP & HRI & HR)).
  destruct HR as ((R2 & R8 & R9 & R18 & R19 & R23 & R24 & R26 & R27 & R3 & R4) & R25 & Ht & Hk & HO &
    R21 & R22 & R11 & Hpk & R20 & R6).
  pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  pose proof HB as (HAI & HPRE & Hra & Ha0 & Ha1 & Hblk0 & Hlen & _).
  pose proof HPRE as (HAR0 & Hra0 & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
  pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
  pose proof (ajournal_gx_AR_x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as HAR.
  (* the cut's ghost list is [] (HP0 at the journal's end state) *)
  pose proof (HP0 _ _ _ _ _ _ HAR) as Ehp3. subst Hp3.
  pose proof HIN as [[[Hn00 _] | [Hnr Hblk]] Hgarr]; [lia|].
  destruct (alx_blocks _ _ ARx LAWS _ _ [] _ _ _ _ _ HAR Hblk) as (Hp16 & Hp4096 & Hpceil & Hpia & _ & _).
  pose proof (hb_blk_imgP_x _ _ _ _ _ _ _ _ HAR Hblk ltac:(lia)) as Hpimg.
  pose proof (req_size_pos (c_n cx) ltac:(lia)) as [_ Hreq].
  pose proof (Z.mod_pos_bound (spZ (c_regs cx) - 320) 32 ltac:(lia)) as HFm.
  assert (HFb : spZ (c_regs cx) - 351 <= lf_F cx <= spZ (c_regs cx) - 320) by (unfold lf_F; lia).
  unfold YCfn.LLVMF_STK in *.
  pose proof HFR as (FS & FW & F32 & F40 & F48 & F56 & F64 & F72 & F80 & F96 & F104 & F120 & F128 & F136 & F152 & _).
  pose proof HMOD as (Hhs4 & Hslots & _).
  destruct (hb_in_byte cx (arm W mem) (lm_k m) Hgarr ltac:(lia)) as [MB0 Rb0].
  pose proof (Z.mod_pos_bound (in_byte cx (lm_k m)) 10 ltac:(lia)) as Rop.
  pose proof Ht as Ht'. unfold OPS_MAX in Ht'.
  assert (Hkb : 0 <= hd_kb cx m < 256).
  { unfold hd_kb. destruct (lm_k m + 1 <? c_n cx) eqn:Hm1; [|lia].
    apply Z.ltb_lt in Hm1. exact (proj2 (hb_in_byte cx (arm W mem) (lm_k m + 1) Hgarr ltac:(lia))). }
  assert (MB1 : (lm_k m + 1 <? c_n cx) = true ->
      val_mem segs (mrestrict (w_H W) mem) (c_p cx + lm_k m + 1) 1 (hd_kb cx m)).
  { intros Hm1. unfold hd_kb. rewrite Hm1. apply Z.ltb_lt in Hm1. rewrite <- Z.add_assoc.
    exact (proj1 (hb_in_byte cx (arm W mem) (lm_k m + 1) Hgarr ltac:(lia))). }
  assert (RA1 : (lm_k m + 1 <? c_n cx) = true ->
      range_addressable (aview segs (w_H W) mem) SHADOW_OFF (c_p cx + lm_k m + 1) 1).
  { intros Hm1. apply Z.ltb_lt in Hm1.
    apply (range_addressable_of_block_hp0_x segs B ARx LAWS HP0 ly3 S3 [] W mem md (c_p cx) (c_n cx)); [exact HAR | exact Hblk | lia | lia]. }
  pose proof (hb_gs_shadow_x ly3 S3 W mem md HAR) as SH0.
  pose proof (hb_open_val ly3 S3 W mem 0 _ (Hslots 0%nat ltac:(lia))) as G0.
  pose proof (hb_open_val ly3 S3 W mem 1 _ (Hslots 1%nat ltac:(lia))) as G1.
  pose proof (hb_open_val ly3 S3 W mem 2 _ (Hslots 2%nat ltac:(lia))) as G2.
  pose proof (hb_open_val ly3 S3 W mem 3 _ (Hslots 3%nat ltac:(lia))) as G3.
  pose proof Hhs4 as Hl4.
  destruct (lm_hs m) as [|o0 [|o1 [|o2 [|o3 [|o4 rest]]]]] eqn:Hhs; cbn [length] in Hl4; try discriminate Hl4.
  rewrite ?Hhs in G0, G1, G2, G3. cbn [nth] in G0, G1, G2, G3.
  destruct (hb_entry2 W regs mem (lm_k m + 1 <? c_n cx) (hb_isS o0) (hb_isS o1) (hb_isS o2) (hb_isS o3) (c_p cx + lm_k m + 1)
    (lf_F cx) (hd_kb cx m) R23 R9 R27 R20 ltac:(lia) Hkb ltac:(lia) ltac:(lia)
    ltac:(intros Hm1; apply Z.ltb_lt in Hm1; lia)
    ltac:(intros Hm1; apply Z.ltb_lt in Hm1; unfold in_app in Hpia; unfold kLowShadowBeg, kHighMemBeg in *; lia)
    ltac:(intros Hm1; apply Z.ltb_lt in Hm1; lia)
    MB1 RA1 F128 F152 G0 G1 G2 G3 SH0) as [HS SHOK].
  remember (Eimg (Ereg regs (hb_x1 (hd_kb cx m)))) as E eqn:HE.
  assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
  assert (EEo : forall m (rr : bv 5), Z.of_nat m = bv_unsigned rr -> ew E m = getr regs rr)
    by (intros m0 rr Hm; subst E; pose proof (bv_unsigned_in_range 5 rr) as Hr5; change (bv_modulus 5) with 32 in Hr5;
        rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_nat; exact Hm).
  assert (E11 : ew E 11 = Z_to_bv 64 (in_byte cx (lm_k m) mod 10)) by (rewrite (EEo 11%nat 11%bv eq_refl); exact R11).
  assert (E21 : ew E 21 = Z_to_bv 64 (c_n cx - lm_k m)) by (rewrite (EEo 21%nat 21%bv eq_refl); exact R21).
  assert (E22 : ew E 22 = Z_to_bv 64 (c_p cx + lm_k m)) by (rewrite (EEo 22%nat 22%bv eq_refl); exact R22).
  assert (E25 : ew E 25 = Z_to_bv 64 t) by (rewrite (EEo 25%nat 25%bv eq_refl); exact R25).
  assert (E20 : ew E 20 = Z_to_bv 64 (c_p cx + lm_k m + 1)) by (rewrite (EEo 20%nat 20%bv eq_refl); exact R20).
  assert (E6 : ew E 6 = Z_to_bv 64 (c_n cx - lm_k m - 1)) by (rewrite (EEo 6%nat 6%bv eq_refl); exact R6).
  assert (E32 : ew E 32 = Z_to_bv 64 (hd_kb cx m))
    by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
  assert (UG : bv_unsigned (ew E 260) = rg_s fr_RG).
  { subst E. rewrite Eimg_img by (unfold A_TEXT, A_LIM; lia). change 260%nat with (A_OBJ 19). rewrite hb_VAL_gs.
    first [reflexivity | apply unsigned_lit_small; cbn; lia]. }
  assert (HAE : env_agree 32 (Ereg regs (hb_x1 (hd_kb cx m))) E)
    by (rewrite HE; split; [intros m0 Hm; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
  clear HE.
  assert (EG' : ew E 260 = Z_to_bv 64 (rg_s fr_RG)) by (rewrite <- UG; symmetry; apply Z_to_bv_bv_unsigned).
  assert (Hnone : (lm_hs m = [None; None; None; None]) -> pick (lm_hs m) (hd_kb cx m) = None)
    by (intros Hn; unfold pick, nopen; rewrite Hn; reflexivity).
  unfold cfg_at. change (w64 (fr_B0 + AF_LLVM_pick)) with (Z_to_bv 64 (BASE + AF_LLVM_pick)).
  revert HS SHOK. destruct (lm_k m + 1 <? c_n cx) eqn:Hmore; intros HS SHOK.
  all: destruct o0 as [h0|]; destruct o1 as [h1|]; destruct o2 as [h2|]; destruct o3 as [h3|].
  all: cbn [hb_isS] in HS; norm_ss HS; cbn [hb_SH2] in SHOK.
  (* the test of in.n - 1 (t1): the side that contradicts `more` is refuted *)
  all: psrr_branch_tok RUN BR HS SHOK hb_Bspan.
  all: rewrite branch_eq_U, (U_atom E 6 (c_n cx - lm_k m - 1) E6), U_lit in Hc by lia.
  all: try (exfalso; first [apply Z.eqb_eq in Hc | apply Z.eqb_neq in Hc];
    first [apply Z.ltb_lt in Hmore | apply Z.ltb_ge in Hmore]; lia).
  all: clear Hc.
  (* the second byte (when in.n > 1) with its PTR_INC trap, the open count with its ADDW trap, to the remainder
     (0x846c4), or, with no open source, to `bne a1,s7` (0x8471c) *)
  all: paj_run_to_tok_x RUNTO HS HJ SHOK hb_Bspan 9088.
  all: try hb_awr0.
  all: hb_meq mem.
  32:
  { psrr_branch_tok RUN BR HS SHOK hb_Bspan.
    - (* op <> 1: `continue`, to B's latch tail 0x8480c *)
      lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
        rewrite branch_ne_U, (U_atom_off Ev 11 _ 0 ltac:(rewrite ?ew_ewset_other by lia; exact E11) ltac:(lia) ltac:(lia)), U_lit in Hc by lia end.
      rewrite Z.add_0_r in Hc. apply negb_true_iff, Z.eqb_neq in Hc. rename Hc into Hop1.
      paj_run_tok_x RUN HS HJ SHOK hb_Bspan. { hb_awr0. } hb_meq mem.
      psrr_branch_tok RUN BR HS SHOK hb_Bspan.
      + (* t + 1 <> 512: the head of operation t + 1 *)
        lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
          rewrite branch_ne_U, (hb_addiw_U Ev t ltac:(rewrite ?ew_ewset_other by lia; exact E25) ltac:(lia)), U_lit in Hc by lia end.
        apply negb_true_iff, Z.eqb_neq in Hc. rename Hc into Ht1.
        paj_run_to_tok_x RUNTO HS HJ SHOK hb_Bspan AF_LLVM_head. { hb_awr0. } hb_meq mem.
        lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
        assert (HAEv : env_agree 32 (Ereg regs (hb_x1 (hd_kb cx m))) Ev)
          by (split; [intros m0 Hm; rewrite ?ew_ewset_other by lia; exact (proj1 HAE m0 Hm) | rewrite ?ed_ewset; exact (proj2 HAE)]);
        assert (U25 : U Ev (SAluw ALU_ADD (SOff 25 0) (SLit 1)) = t + 1)
          by (apply hb_addiw_U; [rewrite ?ew_ewset_other by lia; exact E25 | lia]) end.
        pose proof (regs_kept_of_st_ok_pi _ _ _ regs _ HB_KEPT3 HS HAEv ltac:(vm_compute; reflexivity)) as KR.
        cbn [ms_regs restrict] in KR.
        prreg HS (23%bv : bv 5) Q23. prreg HS (21%bv : bv 5) Q21. prreg HS (22%bv : bv 5) Q22.
        hb_prreg_raw HS (25%bv : bv 5) Q25.
        pmkst HS. rewrite HMm. rewrite HMm in HJ.
        apply SRr_ret. right; right; left.
        lazymatch goal with |- INV_H_x _ _ _ _ PST ARx _ _ _ [] _ _ {| cfg_ms := mkst ?r _ ?mm _; cfg_model := ?d |} => exists r, mm, d end.
        split; [reflexivity|]. split; [exact HROM|].
        exists [(1, fpos)], ly3, S3, [], k, (lm_set_k m (hd_k' cx m)), fpos.
        split; [exact HJ|]. split; [reflexivity|]. split; [exact HFR|]. split; [exact HFL|].
        split; [exact HMOD|]. split; [exact HIN|]. split; [exact HRV|]. split; [exact HSEP|].
        split; [apply LS_head_skip; [exact Ht | exact Hk | exact HO | exact Hpk | exact Hop1 | apply Hnone; exact Hhs |]; exact HLS|]. split; [exact HNP|].
        split; [apply RI_head_skip; [exact Ht | exact Hk | exact HO | exact Hpk | exact Hop1 | apply Hnone; exact Hhs |]; exact HRI|].
        unfold lregs_H. cbn [lm_k lm_set_k]. unfold hd_k'. rewrite Hmore. cbv iota.
        rewrite ?ew_ewset_other in Q21, Q22 by lia.
        rewrite ?E21 in Q21. rewrite ?E6 in Q21. rewrite ?E22 in Q22. rewrite ?E20 in Q22.
        rewrite ?unsigned_lit_small in Q21 by lia. rewrite ?unsigned_lit_small in Q22 by lia.
        first [apply Z.ltb_lt in Hmore | apply Z.ltb_ge in Hmore].
        split; [unfold lregs_common; repeat split; first [ rewrite Q23; reflexivity
          | match goal with |- getr _ ?r = _ => rewrite (KR r ltac:(hb_in)) end; assumption ]|].
        split; [rewrite Q25; apply hb_sv_of_U; [exact U25 | lia]|].
        split; [rewrite Q21; unfold w64; f_equal; lia|].
        split; [rewrite Q22; unfold w64; f_equal; lia|].
        unfold OPS_MAX in *. lia.
      + (* t + 1 = 512: the shutdown block *)
        paj_run_to_tok_x RUNTO HS HJ SHOK hb_Bspan AF_LLVM_exit. { hb_awr0. } hb_meq mem.
        lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
        assert (HAEv : env_agree 32 (Ereg regs (hb_x1 (hd_kb cx m))) Ev)
          by (split; [intros m0 Hm; rewrite ?ew_ewset_other by lia; exact (proj1 HAE m0 Hm) | rewrite ?ed_ewset; exact (proj2 HAE)]) end.
        pose proof (regs_kept_of_st_ok_pi _ _ _ regs _ HB_KEPT3 HS HAEv ltac:(vm_compute; reflexivity)) as KR.
        cbn [ms_regs restrict] in KR.
        pmkst HS. rewrite HMm. rewrite HMm in HJ.
        apply SRr_ret. right; right; right.
        lazymatch goal with |- INV_X_x _ _ _ _ PST ARx _ _ _ [] _ {| cfg_ms := mkst ?r _ ?mm _; cfg_model := ?d |} => exists r, mm, d, (t + 1) end.
        split; [reflexivity|]. split; [exact HROM|].
        exists [(1, fpos)], ly3, S3, [], k, (lm_set_k m (hd_k' cx m)), fpos.
        split; [exact HJ|]. split; [reflexivity|]. split; [exact HFR|]. split; [exact HFL|].
        split; [exact HMOD|]. split; [exact HIN|]. split; [exact HRV|]. split; [exact HSEP|].
        split; [apply LS_head_skip; [exact Ht | exact Hk | exact HO | exact Hpk | exact Hop1 | apply Hnone; exact Hhs |]; exact HLS|]. split; [exact HNP|].
        split; [apply RI_head_skip; [exact Ht | exact Hk | exact HO | exact Hpk | exact Hop1 | apply Hnone; exact Hhs |]; exact HRI|].
        cbv beta. unfold lregs_X. cbn [lm_k lm_set_k]. unfold hd_k'. rewrite Hmore. cbv iota.
        first [apply Z.ltb_lt in Hmore | apply Z.ltb_ge in Hmore].
        repeat split; first [ match goal with |- getr _ ?r = _ => rewrite (KR r ltac:(hb_in)) end; assumption | lia ].
    - (* op = 1 with no open source: arm 1 (0x84724) with s5 = 0 *)
      lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
        rewrite branch_ne_U, (U_atom_off Ev 11 _ 0 ltac:(rewrite ?ew_ewset_other by lia; exact E11) ltac:(lia) ltac:(lia)), U_lit in Hc by lia end.
      rewrite Z.add_0_r in Hc. apply negb_false_iff, Z.eqb_eq in Hc. rename Hc into Hop1.
      paj_run_to_tok_x RUNTO HS HJ SHOK hb_Bspan AF_arm_write. { hb_awr0. } hb_meq mem.
      lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
      assert (HAEv : env_agree 32 (Ereg regs (hb_x1 (hd_kb cx m))) Ev)
        by (split; [intros m0 Hm; rewrite ?ew_ewset_other by lia; exact (proj1 HAE m0 Hm) | rewrite ?ed_ewset; exact (proj2 HAE)]) end.
      pose proof (regs_kept_of_st_ok_pi _ _ _ regs _ HB_KEPT2 HS HAEv ltac:(vm_compute; reflexivity)) as KR.
      cbn [ms_regs restrict] in KR.
      prreg HS (23%bv : bv 5) Q23. prreg HS (20%bv : bv 5) Q20. prreg HS (6%bv : bv 5) Q6.
      prreg HS (21%bv : bv 5) Q21.
      pmkst HS. rewrite HMm. rewrite HMm in HJ.
      apply SRr_ret. right; left.
      lazymatch goal with |- INV_A_x _ _ _ _ PST ARx _ _ _ _ [] _ _ {| cfg_ms := mkst ?r _ ?mm _; cfg_model := ?d |} => exists r, r, mm, d end.
      split; [reflexivity|]. split; [intros rr _; reflexivity|].
      split; [rewrite (KR 11%bv ltac:(hb_in)), R11, Hop1; reflexivity|].
      split; [exists [(1, fpos)], ly3, S3, [], k; exact HJ|]. split; [exact HROM|].
      exists [(1, fpos)], ly3, S3, [], k, m, fpos.
      split; [exact HJ|]. split; [reflexivity|]. split; [exact HFR|]. split; [exact HFL|].
      split; [exact HMOD|]. split; [exact HIN|]. split; [exact HRV|]. split; [exact HSEP|].
      split; [exact HLS|]. split; [exact HNP|]. split; [exact HRI|].
      unfold lregs_D. cbv zeta. rewrite Hpk. cbv iota. rewrite Hmore. cbv iota.
      rewrite ?ew_ewset_other in Q20, Q6 by lia.
      rewrite ?E22 in Q20. rewrite ?E20 in Q20. rewrite ?E21 in Q6. rewrite ?E6 in Q6.
      rewrite ?unsigned_lit_small in Q20 by lia. rewrite ?unsigned_lit_small in Q6 by lia.
      split; [unfold lregs_common; repeat split; first [ rewrite Q23; reflexivity
        | match goal with |- getr _ ?r = _ => rewrite (KR r ltac:(hb_in)) end; assumption ]|].
      split; [rewrite (KR 25%bv ltac:(hb_in)); exact R25|].
      split; [exact Ht|]. split; [exact Hk|]. split; [exact HO|].
      split; [rewrite (KR 11%bv ltac:(hb_in)); exact R11|].
      split; [rewrite Q20; unfold w64; f_equal; lia|].
      split; [rewrite Q6; unfold w64; f_equal; lia|].
      right. split; [exact Hop1|]. split; [unfold pick, nopen; rewrite Hhs; reflexivity|]. rewrite Q21. reflexivity.
  }
  16:
  { psrr_branch_tok RUN BR HS SHOK hb_Bspan.
    - (* op <> 1: `continue`, to B's latch tail 0x8480c *)
      lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
        rewrite branch_ne_U, (U_atom_off Ev 11 _ 0 ltac:(rewrite ?ew_ewset_other by lia; exact E11) ltac:(lia) ltac:(lia)), U_lit in Hc by lia end.
      rewrite Z.add_0_r in Hc. apply negb_true_iff, Z.eqb_neq in Hc. rename Hc into Hop1.
      paj_run_tok_x RUN HS HJ SHOK hb_Bspan. { hb_awr0. } hb_meq mem.
      psrr_branch_tok RUN BR HS SHOK hb_Bspan.
      + (* t + 1 <> 512: the head of operation t + 1 *)
        lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
          rewrite branch_ne_U, (hb_addiw_U Ev t ltac:(rewrite ?ew_ewset_other by lia; exact E25) ltac:(lia)), U_lit in Hc by lia end.
        apply negb_true_iff, Z.eqb_neq in Hc. rename Hc into Ht1.
        paj_run_to_tok_x RUNTO HS HJ SHOK hb_Bspan AF_LLVM_head. { hb_awr0. } hb_meq mem.
        lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
        assert (HAEv : env_agree 32 (Ereg regs (hb_x1 (hd_kb cx m))) Ev)
          by (split; [intros m0 Hm; rewrite ?ew_ewset_other by lia; exact (proj1 HAE m0 Hm) | rewrite ?ed_ewset; exact (proj2 HAE)]);
        assert (U25 : U Ev (SAluw ALU_ADD (SOff 25 0) (SLit 1)) = t + 1)
          by (apply hb_addiw_U; [rewrite ?ew_ewset_other by lia; exact E25 | lia]) end.
        pose proof (regs_kept_of_st_ok_pi _ _ _ regs _ HB_KEPT3 HS HAEv ltac:(vm_compute; reflexivity)) as KR.
        cbn [ms_regs restrict] in KR.
        prreg HS (23%bv : bv 5) Q23. prreg HS (21%bv : bv 5) Q21. prreg HS (22%bv : bv 5) Q22.
        hb_prreg_raw HS (25%bv : bv 5) Q25.
        pmkst HS. rewrite HMm. rewrite HMm in HJ.
        apply SRr_ret. right; right; left.
        lazymatch goal with |- INV_H_x _ _ _ _ PST ARx _ _ _ [] _ _ {| cfg_ms := mkst ?r _ ?mm _; cfg_model := ?d |} => exists r, mm, d end.
        split; [reflexivity|]. split; [exact HROM|].
        exists [(1, fpos)], ly3, S3, [], k, (lm_set_k m (hd_k' cx m)), fpos.
        split; [exact HJ|]. split; [reflexivity|]. split; [exact HFR|]. split; [exact HFL|].
        split; [exact HMOD|]. split; [exact HIN|]. split; [exact HRV|]. split; [exact HSEP|].
        split; [apply LS_head_skip; [exact Ht | exact Hk | exact HO | exact Hpk | exact Hop1 | apply Hnone; exact Hhs |]; exact HLS|]. split; [exact HNP|].
        split; [apply RI_head_skip; [exact Ht | exact Hk | exact HO | exact Hpk | exact Hop1 | apply Hnone; exact Hhs |]; exact HRI|].
        unfold lregs_H. cbn [lm_k lm_set_k]. unfold hd_k'. rewrite Hmore. cbv iota.
        rewrite ?ew_ewset_other in Q21, Q22 by lia.
        rewrite ?E21 in Q21. rewrite ?E6 in Q21. rewrite ?E22 in Q22. rewrite ?E20 in Q22.
        rewrite ?unsigned_lit_small in Q21 by lia. rewrite ?unsigned_lit_small in Q22 by lia.
        first [apply Z.ltb_lt in Hmore | apply Z.ltb_ge in Hmore].
        split; [unfold lregs_common; repeat split; first [ rewrite Q23; reflexivity
          | match goal with |- getr _ ?r = _ => rewrite (KR r ltac:(hb_in)) end; assumption ]|].
        split; [rewrite Q25; apply hb_sv_of_U; [exact U25 | lia]|].
        split; [rewrite Q21; unfold w64; f_equal; lia|].
        split; [rewrite Q22; unfold w64; f_equal; lia|].
        unfold OPS_MAX in *. lia.
      + (* t + 1 = 512: the shutdown block *)
        paj_run_to_tok_x RUNTO HS HJ SHOK hb_Bspan AF_LLVM_exit. { hb_awr0. } hb_meq mem.
        lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
        assert (HAEv : env_agree 32 (Ereg regs (hb_x1 (hd_kb cx m))) Ev)
          by (split; [intros m0 Hm; rewrite ?ew_ewset_other by lia; exact (proj1 HAE m0 Hm) | rewrite ?ed_ewset; exact (proj2 HAE)]) end.
        pose proof (regs_kept_of_st_ok_pi _ _ _ regs _ HB_KEPT3 HS HAEv ltac:(vm_compute; reflexivity)) as KR.
        cbn [ms_regs restrict] in KR.
        pmkst HS. rewrite HMm. rewrite HMm in HJ.
        apply SRr_ret. right; right; right.
        lazymatch goal with |- INV_X_x _ _ _ _ PST ARx _ _ _ [] _ {| cfg_ms := mkst ?r _ ?mm _; cfg_model := ?d |} => exists r, mm, d, (t + 1) end.
        split; [reflexivity|]. split; [exact HROM|].
        exists [(1, fpos)], ly3, S3, [], k, (lm_set_k m (hd_k' cx m)), fpos.
        split; [exact HJ|]. split; [reflexivity|]. split; [exact HFR|]. split; [exact HFL|].
        split; [exact HMOD|]. split; [exact HIN|]. split; [exact HRV|]. split; [exact HSEP|].
        split; [apply LS_head_skip; [exact Ht | exact Hk | exact HO | exact Hpk | exact Hop1 | apply Hnone; exact Hhs |]; exact HLS|]. split; [exact HNP|].
        split; [apply RI_head_skip; [exact Ht | exact Hk | exact HO | exact Hpk | exact Hop1 | apply Hnone; exact Hhs |]; exact HRI|].
        cbv beta. unfold lregs_X. cbn [lm_k lm_set_k]. unfold hd_k'. rewrite Hmore. cbv iota.
        first [apply Z.ltb_lt in Hmore | apply Z.ltb_ge in Hmore].
        repeat split; first [ match goal with |- getr _ ?r = _ => rewrite (KR r ltac:(hb_in)) end; assumption | lia ].
    - (* op = 1 with no open source: arm 1 (0x84724) with s5 = 0 *)
      lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
        rewrite branch_ne_U, (U_atom_off Ev 11 _ 0 ltac:(rewrite ?ew_ewset_other by lia; exact E11) ltac:(lia) ltac:(lia)), U_lit in Hc by lia end.
      rewrite Z.add_0_r in Hc. apply negb_false_iff, Z.eqb_eq in Hc. rename Hc into Hop1.
      paj_run_to_tok_x RUNTO HS HJ SHOK hb_Bspan AF_arm_write. { hb_awr0. } hb_meq mem.
      lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
      assert (HAEv : env_agree 32 (Ereg regs (hb_x1 (hd_kb cx m))) Ev)
        by (split; [intros m0 Hm; rewrite ?ew_ewset_other by lia; exact (proj1 HAE m0 Hm) | rewrite ?ed_ewset; exact (proj2 HAE)]) end.
      pose proof (regs_kept_of_st_ok_pi _ _ _ regs _ HB_KEPT2 HS HAEv ltac:(vm_compute; reflexivity)) as KR.
      cbn [ms_regs restrict] in KR.
      prreg HS (23%bv : bv 5) Q23. prreg HS (20%bv : bv 5) Q20. prreg HS (6%bv : bv 5) Q6.
      prreg HS (21%bv : bv 5) Q21.
      pmkst HS. rewrite HMm. rewrite HMm in HJ.
      apply SRr_ret. right; left.
      lazymatch goal with |- INV_A_x _ _ _ _ PST ARx _ _ _ _ [] _ _ {| cfg_ms := mkst ?r _ ?mm _; cfg_model := ?d |} => exists r, r, mm, d end.
      split; [reflexivity|]. split; [intros rr _; reflexivity|].
      split; [rewrite (KR 11%bv ltac:(hb_in)), R11, Hop1; reflexivity|].
      split; [exists [(1, fpos)], ly3, S3, [], k; exact HJ|]. split; [exact HROM|].
      exists [(1, fpos)], ly3, S3, [], k, m, fpos.
      split; [exact HJ|]. split; [reflexivity|]. split; [exact HFR|]. split; [exact HFL|].
      split; [exact HMOD|]. split; [exact HIN|]. split; [exact HRV|]. split; [exact HSEP|].
      split; [exact HLS|]. split; [exact HNP|]. split; [exact HRI|].
      unfold lregs_D. cbv zeta. rewrite Hpk. cbv iota. rewrite Hmore. cbv iota.
      rewrite ?ew_ewset_other in Q20, Q6 by lia.
      rewrite ?E22 in Q20. rewrite ?E20 in Q20. rewrite ?E21 in Q6. rewrite ?E6 in Q6.
      rewrite ?unsigned_lit_small in Q20 by lia. rewrite ?unsigned_lit_small in Q6 by lia.
      split; [unfold lregs_common; repeat split; first [ rewrite Q23; reflexivity
        | match goal with |- getr _ ?r = _ => rewrite (KR r ltac:(hb_in)) end; assumption ]|].
      split; [rewrite (KR 25%bv ltac:(hb_in)); exact R25|].
      split; [exact Ht|]. split; [exact Hk|]. split; [exact HO|].
      split; [rewrite (KR 11%bv ltac:(hb_in)); exact R11|].
      split; [rewrite Q20; unfold w64; f_equal; lia|].
      split; [rewrite Q6; unfold w64; f_equal; lia|].
      right. split; [exact Hop1|]. split; [unfold pick, nopen; rewrite Hhs; reflexivity|]. rewrite Q21. reflexivity.
  }
  (* an open source: the remainder kb % n (pinned to its value), the k-th open source, to the dispatch *)
  all: lazymatch goal with HS : st_ok_pi ?sg ?vl ?Ev ?ss (restrict ?H ?ms) |- _ =>
    let a2 := eval vm_compute in (sr_get (ss_regs ss) 12%bv) in
    lazymatch a2 with
    | SMdw M_REM (SOff 32 0) (SLit ?c) =>
        assert (UR : U Ev (SMdw M_REM (SOff 32 0) (SLit c)) = hd_kb cx m mod c)
          by (apply hb_rem_U; [rewrite ?ew_ewset_other by lia; exact E32 | exact Hkb | lia]);
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
            ltac:(cbn [ms_regs restrict]; rewrite Q12; apply hb_sv_of_U; [rewrite UR; exact HR | lia]) eq_refl) as HS2;
         clear HS; rename HS2 into HS; cbn [ss_pc ss_regs ss_mem ss_resv ss_facts] in HS; norm_ss HS end end).
  all: try (unfold hd_kb in HR; rewrite Hmore in HR; cbv iota in HR).
  all: paj_run_to_tok_x RUNTO HS HJ SHOK hb_Bspan AF_LLVM_dispatch.
  all: try hb_awr0.
  all: hb_meq mem.
  all: lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
      assert (HAEv : env_agree 32 (Ereg regs (hb_x1 (hd_kb cx m))) Ev)
        by (split; [intros m0 Hm; rewrite ?ew_ewset_other by lia; exact (proj1 HAE m0 Hm) | rewrite ?ed_ewset; exact (proj2 HAE)]) end.
  all: pose proof (regs_kept_of_st_ok_pi _ _ _ regs _ HB_KEPT2 HS HAEv ltac:(vm_compute; reflexivity)) as KR.
  all: cbn [ms_regs restrict] in KR.
  all: prreg HS (23%bv : bv 5) Q23; prreg HS (20%bv : bv 5) Q20; prreg HS (6%bv : bv 5) Q6.
  all: prreg HS (21%bv : bv 5) Q21.
  all: pmkst HS.
  all: rewrite HMm; rewrite HMm in HJ.
  all: apply SRr_ret; left; exists (in_byte cx (lm_k m) mod 10); split; [lia|].
  all: lazymatch goal with |- INV_D_x _ _ _ _ PST ARx _ _ _ [] _ _ _ {| cfg_ms := mkst ?r _ ?mm _; cfg_model := ?d |} => exists r, mm, d end.
  all: split; [reflexivity|].
  all: split; [rewrite (KR 11%bv ltac:(hb_in)); exact R11|].
  all: split; [exists [(1, fpos)], ly3, S3, [], k; exact HJ|].
  all: split; [exact HROM|].
  all: exists [(1, fpos)], ly3, S3, [], k, m, fpos.
  all: split; [exact HJ|]; split; [reflexivity|]; split; [exact HFR|]; split; [exact HFL|]; split; [exact HMOD|]; split; [exact HIN|].
  all: split; [exact HRV|]; split; [exact HSEP|]; split; [exact HLS|]; split; [exact HNP|]; split; [exact HRI|].
  all: unfold lregs_D; cbv zeta; rewrite Hpk; cbv iota; rewrite Hmore; cbv iota.
  all: rewrite ?ew_ewset_other in Q21, Q20, Q6 by lia.
  all: rewrite ?E22 in Q20; rewrite ?E20 in Q20; rewrite ?E21 in Q6; rewrite ?E6 in Q6; rewrite ?EG' in Q21.
  all: rewrite ?unsigned_lit_small in Q21 by (cbn; lia); rewrite ?unsigned_lit_small in Q20 by lia;
    rewrite ?unsigned_lit_small in Q6 by lia.
  all: split; [unfold lregs_common; repeat split; first [ rewrite Q23; reflexivity
      | match goal with |- getr _ ?r = _ => rewrite (KR r ltac:(hb_in)) end; assumption ]|].
  all: split; [rewrite (KR 25%bv ltac:(hb_in)); exact R25|].
  all: split; [exact Ht|]; split; [exact Hk|]; split; [exact HO|].
  all: split; [rewrite (KR 11%bv ltac:(hb_in)); exact R11|].
  all: split; [rewrite Q20; unfold w64; f_equal; lia|].
  all: split; [rewrite Q6; unfold w64; f_equal; lia|].
  all: left; eexists; split.
  all: try (unfold pick; rewrite Hhs;
    lazymatch goal with |- context [nopen ?l] => let v := eval vm_compute in (nopen l) in change (nopen l) with v end;
    try rewrite HR; reflexivity).
  all: rewrite Q21; unfold w64, ASRC; f_equal; cbn [Z.of_nat Pos.of_succ_nat]; cbn; lia.
Qed.

(* ------------------------------------------------------------------ the AR file's :1549 lf_seg_head_b over ARx at the
   entry's ghost list [] *)
Lemma lf_seg_head_nil_x : forall cx t W c, lf_base_x B MT XM_LIB RLO RHI fr_live_pre LIBROOM NP G_fr ARx cx [] ->
  INV_H_x B NP G_fr fr_FP PST ARx LSx RINV cx [] t W c ->
  SRr segs W c (fun W' c' => (exists op, 0 <= op <= 9 /\ INV_D_x B NP G_fr fr_FP PST ARx LSx RINV cx [] t op W' c') \/
    INV_A_x B NP G_fr fr_FP PST ARx LSx RINV 1 cx [] t W' c' \/
    INV_H_x B NP G_fr fr_FP PST ARx LSx RINV cx [] (t + 1) W' c' \/ INV_X_x B NP G_fr fr_FP PST ARx LSx RINV cx [] W' c').
Proof.
  intros cx t W c HB HH.
  eapply SRr_bind; [exact (hb_w1_x cx t W c HB HH)|].
  intros W1 c1 _ [HD | [HP | HX]].
  - apply SRr_ret. left. exact HD.
  - exact (hb_w2_x cx t W1 c1 HB HP).
  - apply SRr_ret. right; right; right. exact HX.
Qed.


(* ---- SEG_HEAD (B cut_x Section w :372): the entry's ghost list is [] by HP0 at lf_base_x's afn_pre_x, and the walk
   above is lf_seg_head_nil_x ---- *)
Theorem lf_seg_head_x : forall cx Hp t W c,
  lf_base_x B MT XM_LIB RLO RHI fr_live_pre LIBROOM NP G_fr ARx cx Hp ->
  INV_H_x B NP G_fr fr_FP PST ARx LSx RINV cx Hp t W c ->
  SRr segs W c (fun W' c' => (exists op, 0 <= op <= 9 /\ INV_D_x B NP G_fr fr_FP PST ARx LSx RINV cx Hp t op W' c') \/
    INV_A_x B NP G_fr fr_FP PST ARx LSx RINV 1 cx Hp t W' c' \/
    INV_H_x B NP G_fr fr_FP PST ARx LSx RINV cx Hp (t + 1) W' c' \/ INV_X_x B NP G_fr fr_FP PST ARx LSx RINV cx Hp W' c').
Proof.
  intros cx Hp t W c HB HH.
  assert (Ehp : Hp = []).
  { destruct HB as (_ & HPRE). unfold fr_lib_pre_cf_x in HPRE. destruct HPRE as ((HAR & _) & _).
    exact (HP0 _ _ _ _ _ _ HAR). }
  subst Hp. exact (lf_seg_head_nil_x cx t W c HB HH).
Qed.

(* ---- THE CHECK: B cut_x Section w's SEG_HEAD (W_LLVMFuzzerTestOneInput_cut_x.v:622), restated in its text at cut_x's
   names (the forms B top_x.v:123-128 uses) and closed by `exact` from lf_seg_head_x ---- *)
Local Notation BASEx cx Hp := (lf_base_x B MT XM_LIB RLO RHI fr_live_pre LIBROOM NP G_fr ARx cx Hp).
Local Notation IH := (INV_H_x B NP G_fr fr_FP PST ARx LSx RINV).
Local Notation ID := (INV_D_x B NP G_fr fr_FP PST ARx LSx RINV).
Local Notation IA := (INV_A_x B NP G_fr fr_FP PST ARx LSx RINV).
Local Notation IX := (INV_X_x B NP G_fr fr_FP PST ARx LSx RINV).
Lemma lf_seg_head_x_check : forall cx Hp t W c, BASEx cx Hp -> IH cx Hp t W c ->
  SRr segs W c (fun W' c' => (exists op, 0 <= op <= 9 /\ ID cx Hp t op W' c') \/ IA 1 cx Hp t W' c' \/
    IH cx Hp (t + 1) W' c' \/ IX cx Hp W' c').
Proof. exact lf_seg_head_x. Qed.
(* ---- route R (RULE-SHAPES.md (sha256 2e856ce788dd; internal record) section 0): the head at a world relation R.  The walk moves no world (it makes no call),
   so it is the strict walk over the R journal (W_journal_x.v paj_run_x_xR / paj_run_to_x_xR) with every cut_x
   carrier at R (INV_*_xR, lcut_xR, LF_xR, lf_jour_xR), lifted to SRrG by YA0nH.SRr_SRrG WLE_R; lf_seg_head_xR
   concludes B cut_x Section wR's SEG_HEAD_R.  The strict text above is unchanged. ---- *)
Section hxR.
Variable R : world segs -> world segs -> Prop.
Hypothesis R_refl : forall W, R W W.
Hypothesis R_trans : forall W1 W2 W3, R W1 W2 -> R W2 W3 -> R W1 W3.
Hypothesis WLE_R : forall W W', @wle segs W W' -> R W W'.
Let RUNR := paj_run_x_xR (PL := PL_fr) (PI := PB_fr) B PST ARx LAWS R G_fr HG 0 [].
Let RUNTOR := paj_run_to_x_xR (PL := PL_fr) (PI := PB_fr) B PST ARx LAWS R G_fr HG 0 [].

(* R twin of hb_INV_P_x *)
Definition hb_INV_P_xR (cx : lfcx) (t : Z) : world segs -> config -> Prop :=
  fun W c => exists regs mem md, c = cfg_at segs (fr_B0 + AF_LLVM_pick) regs mem md /\
    jt_rom W mem /\ lcut_xR B NP G_fr fr_FP PST ARx LSx RINV R cx [] t (hb_lregs_P cx t) regs mem md W.
(* R twin of hb_w1_lcut_x *)
Lemma hb_w1_lcut_xR : forall cx t W mem md mem' md' ly3 S3 k m fpos
    (RC : lmod -> Z -> bvmap 5 word -> world segs -> (word -> option byte) -> Prop) regs',
  lf_base_x B MT XM_LIB RLO RHI fr_live_pre LIBROOM NP G_fr ARx cx [] ->
  ajournal_gx_xR segs B PST ARx R G_fr 0 [] YCfn.LLVMF_STK (spZ (c_regs cx)) (lf_FP fr_FP cx) (c_ly cx) (c_S cx) [] (c_W cx)
    (c_mem cx) (c_md cx) [(1, fpos)] ly3 S3 [] W mem md k ->
  ajournal_gx_xR segs B PST ARx R G_fr 0 [] YCfn.LLVMF_STK (spZ (c_regs cx)) (lf_FP fr_FP cx) (c_ly cx) (c_S cx) [] (c_W cx)
    (c_mem cx) (c_md cx) [(1, fpos)] ly3 S3 [] W mem' md' k ->
  (forall x : word, ~ (rg_nout fr_RG <= bv_unsigned x < rg_nout fr_RG + 8) -> mrestrict (w_H W) mem' x = mrestrict (w_H W) mem x) ->
  mem_grows (mrestrict (w_H W) mem) (mrestrict (w_H W) mem') ->
  val_mem segs (arm W mem') (rg_nout fr_RG) 8 0 ->
  aframe_at cx (frame_addr ly3 1 fpos) W mem -> sv8 W mem (frame_addr ly3 1 fpos + 120) (flag_addr ly3 1 fpos) ->
  amodel_at B ly3 S3 W mem m -> ainput_at B cx ly3 S3 W mem ->
  rom_view segs W mem -> ablocks_sep B fr_FP cx m ly3 S3 -> LSx cx t m ly3 S3 -> NP S3 -> RINV cx t m -> jt_rom W mem ->
  RC (lm_clear_O m) (frame_addr ly3 1 fpos) regs' W mem' ->
  jt_rom W mem' /\ lcut_xR B NP G_fr fr_FP PST ARx LSx RINV R cx [] t RC regs' mem' md' W.
Proof.
  intros cx t W mem md mem' md' ly3 S3 k m fpos RC regs' HB HJ HJ' HKX HGR HN0 HFR HFL HMOD HIN HRV HSEP HLS HNP HRI HJT HR.
  pose proof (ajournal_gx_AR_xR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as HAR.
  assert (Hfp : In (1, fpos) (frames S3)).
  { destruct (ajournal_gx_inner_xR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as (memS & HJi & _).
    pose proof HJi as (_ & _ & _ & _ & _ & Hfrs & _). rewrite Hfrs. left. reflexivity. }
  destruct (hb_store_kept_x cx ly3 S3 W mem md mem' fpos m HB HAR Hfp HKX HGR HN0 HFR HMOD HIN HRV HJT)
    as (F' & M' & I' & RV' & JT').
  split; [exact JT'|].
  exists [(1, fpos)], ly3, S3, [], k, (lm_clear_O m), fpos.
  split; [exact HJ'|]. split; [reflexivity|]. split; [exact F'|].
  split; [exact (hb_flag_kept_x ly3 S3 W mem md mem' fpos HAR Hfp HKX HGR HFL)|].
  split; [exact M'|]. split; [exact I'|].
  split; [exact RV'|]. split; [exact HSEP|]. split; [apply LS_head_nout; exact HLS|]. split; [exact HNP|].
  split; [apply RI_head_nout; exact HRI|]. exact HR.
Qed.
(* R twin of hb_w1_x *)
Lemma hb_w1_xR : forall cx t W c, lf_base_x B MT XM_LIB RLO RHI fr_live_pre LIBROOM NP G_fr ARx cx [] -> INV_H_xR B NP G_fr fr_FP PST ARx LSx RINV R cx [] t W c ->
  SRr segs W c (fun W' c' => (exists op, 0 <= op <= 9 /\ INV_D_xR B NP G_fr fr_FP PST ARx LSx RINV R cx [] t op W' c') \/
    hb_INV_P_xR cx t W' c' \/ INV_X_xR B NP G_fr fr_FP PST ARx LSx RINV R cx [] W' c').
Proof.
  intros cx t W c HB (regs & mem & md & -> & HROM &
    (own & ly3 & S3 & Hp3 & k & m & fpos & HJ & -> & HFR & HFL & HMOD & HIN & HRV & HSEP & HLS & HNP & HRI & HR)).
  destruct HR as ((R2 & R8 & R9 & R18 & R19 & R23 & R24 & R26 & R27 & R3 & R4) & R25 & R21 & R22 & Ht & Hk).
  pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  pose proof HB as (HAI & HPRE & Hra & Ha0 & Ha1 & Hblk0 & Hlen & _).
  pose proof HPRE as (HAR0 & Hra0 & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
  pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
  pose proof (ajournal_gx_AR_xR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as HAR.
  (* the cut's ghost list is [] (HP0 at the journal's end state) *)
  pose proof (HP0 _ _ _ _ _ _ HAR) as Ehp3. subst Hp3.
  unfold cfg_at. change (w64 (fr_B0 + AF_LLVM_head)) with (Z_to_bv 64 (BASE + AF_LLVM_head)).
  destruct (Z.eq_dec (lm_k m) (c_n cx)) as [Hkn | Hkn].
  { (* in.n = 0: `beqz s5` to the shutdown block *)
    assert (R21' : getr regs 21 = w64 0) by (rewrite R21, Hkn, Z.sub_diag; reflexivity).
    destruct (hb_entry0 W regs mem R23 R21' R27) as [HS SHOK].
    remember (Eimg (Ereg regs [])) as E eqn:HE.
    assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
    assert (HAE : env_agree 32 (Ereg regs []) E)
      by (rewrite HE; split; [intros q Hq; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
    clear HE.
    paj_run_to_tok_x RUNTOR HS HJ SHOK hb_Bspan AF_LLVM_exit.
    { apply awr_ok_x_nil. }
    hb_mem HF Em.
    pose proof (regs_kept_of_st_ok_pi (PI := PB_fr) _ _ _ regs [] HB_KEPTX HS HAE ltac:(vm_compute; reflexivity)) as KR.
    cbn [ms_regs restrict] in KR.
    pmkst HS. rewrite Em in *. clear HF HFr HG0.
    apply SRr_ret. right; right.
    lazymatch goal with |- INV_X_xR _ _ _ _ PST ARx _ _ _ _ [] _ {| cfg_ms := mkst ?r _ _ _; cfg_model := ?d |} => exists r, mem, d, t end.
    split; [reflexivity|]. split; [exact HROM|].
    exists [(1, fpos)], ly3, S3, [], k, m, fpos.
    split; [exact HJ|]. split; [reflexivity|]. split; [exact HFR|]. split; [exact HFL|].
    split; [exact HMOD|]. split; [exact HIN|]. split; [exact HRV|]. split; [exact HSEP|].
    split; [exact HLS|]. split; [exact HNP|]. split; [exact HRI|].
    unfold lregs_X.
    repeat split; first [ match goal with |- getr _ ?r = _ => rewrite (KR r ltac:(hb_in)) end; assumption | lia ]. }
  pose proof HIN as [[[Hn00 _] | [Hnr Hblk]] Hgarr]; [lia|].
  destruct (alx_blocks _ _ ARx LAWS _ _ [] _ _ _ _ _ HAR Hblk) as (Hp16 & Hp4096 & Hpceil & Hpia & _ & _).
  pose proof (hb_blk_imgP_x _ _ _ _ _ _ _ _ HAR Hblk ltac:(lia)) as Hpimg.
  pose proof (req_size_pos (c_n cx) ltac:(lia)) as [_ Hreq].
  pose proof (Z.mod_pos_bound (spZ (c_regs cx) - 320) 32 ltac:(lia)) as HFm.
  assert (HFb : spZ (c_regs cx) - 351 <= lf_F cx <= spZ (c_regs cx) - 320) by (unfold lf_F; lia).
  unfold YCfn.LLVMF_STK in *.
  destruct (hb_in_byte cx (arm W mem) (lm_k m) Hgarr ltac:(lia)) as [MB Rb0].
  pose proof HFR as (FS & FW & F32 & F40 & F48 & F56 & F64 & F72 & F80 & F96 & F104 & F120 & F128 & F136 & F152 &
    F184 & FF0 & FF8 & FF16 & FFw & FFsh & FFshw).
  pose proof HMOD as (Hhs4 & Hslots & Hrel & Hout & Hgone & Hlock & Hwake & Hnfd & Hnfdw & Hnfdr).
  pose proof Hout as (O1 & O2 & O3 & O4 & _).
  destruct (hb_entry1 W regs mem (c_n cx - lm_k m) (c_p cx + lm_k m) (lf_F cx) (in_byte cx (lm_k m)) R23 R9 R21 R22 R26 R27
    ltac:(lia) ltac:(lia) Rb0 ltac:(lia) ltac:(lia) MB F136 O4 ltac:(lia)
    ltac:(rewrite hb_nout_val; lia) ltac:(rewrite hb_nout_val; lia)
    ltac:(apply (range_addressable_of_block_hp0_x segs B ARx LAWS HP0 ly3 S3 [] W mem md (c_p cx) (c_n cx)); [exact HAR | exact Hblk | lia | lia])
    ltac:(unfold in_app, SHADOW_OFF, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *; lia)) as [HS SHOK].
  remember (Eimg (Ereg regs (hb_x1 (in_byte cx (lm_k m))))) as E eqn:HE.
  assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
  assert (EEo : forall m (rr : bv 5), Z.of_nat m = bv_unsigned rr -> ew E m = getr regs rr)
    by (intros m0 rr Hm; subst E; pose proof (bv_unsigned_in_range 5 rr) as Hr5; change (bv_modulus 5) with 32 in Hr5;
        rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_nat; exact Hm).
  assert (E21 : ew E 21 = Z_to_bv 64 (c_n cx - lm_k m)) by (rewrite (EEo 21%nat 21%bv eq_refl); exact R21).
  assert (E22 : ew E 22 = Z_to_bv 64 (c_p cx + lm_k m)) by (rewrite (EEo 22%nat 22%bv eq_refl); exact R22).
  assert (E26 : ew E 26 = Z_to_bv 64 HI_G_NOUT) by (rewrite (EEo 26%nat 26%bv eq_refl); exact R26).
  assert (E32 : ew E 32 = Z_to_bv 64 (in_byte cx (lm_k m)))
    by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
  assert (HAE : env_agree 32 (Ereg regs (hb_x1 (in_byte cx (lm_k m)))) E)
    by (rewrite HE; split; [intros m0 Hm; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
  clear HE.
  pose proof HJ as HJ0.
  pose proof (Z.mod_pos_bound (in_byte cx (lm_k m)) 10 ltac:(lia)) as Rop.
  assert (UOP : forall Ev, ew Ev 32 = ew E 32 -> U Ev hb_opsv = in_byte cx (lm_k m) mod 10)
    by (intros Ev HEv; apply hb_op_U; [rewrite HEv; exact E32 | exact Rb0]).
  (* the head test, the PTR_INC trap, the shadow check and read of in.p[0], op = in.p[0] % 10, g_nout = 0, to the
     class test *)
  paj_run_tok_x RUNR HS HJ SHOK hb_Bspan.
  { hb_awr E26 HGnout. }
  lazymatch goal with HFx : frame_of _ _ (mrestrict _ mem) (mrestrict _ (ms_mem ?ms1)) |- _ =>
    assert (MEQ1 : forall x : word, ~ (rg_nout fr_RG <= bv_unsigned x < rg_nout fr_RG + 8) ->
        mrestrict (w_H W) (ms_mem ms1) x = mrestrict (w_H W) mem x)
      by (apply (hb_frame_nout E (ss_mem hb_ss1)); [exact HFx | hb_wr E26]) end.
  lazymatch goal with H : mem_grows (mrestrict _ mem) _ |- _ => rename H into MG1 end.
  rename MEQ1 into MEQ. rename MG1 into MG.
  repeat match goal with H : frame_of _ _ _ _ |- _ => clear H end.
  lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
    assert (UO : U Ev hb_opsv = in_byte cx (lm_k m) mod 10) by (apply UOP; rewrite !ew_ewset_other by lia; reflexivity);
    assert (HAE1 : env_agree 32 (Ereg regs (hb_x1 (in_byte cx (lm_k m)))) Ev)
      by (split; [intros m0 Hm; rewrite !ew_ewset_other by lia; exact (proj1 HAE m0 Hm) | rewrite !ed_ewset; exact (proj2 HAE)])
  end.
  psrr_branch_tok RUNR BR HS SHOK hb_Bspan.
  - (* op in 1..4: on to the pick *)
    unfold hb_opsv in UO. rewrite branch_ltu_U, U_SAlu, UO, hb_cls_ltu in Hc by lia.
    apply andb_prop in Hc as [Hc1 Hc2]. apply Z.leb_le in Hc1, Hc2. fold hb_opsv in UO.
    paj_run_to_tok_x RUNTOR HS HJ SHOK hb_Bspan AF_LLVM_pick.
    { hb_awr E26 HGnout. }
    hb_upd E26 MEQ MG.
    pose proof (regs_kept_of_st_ok_pi _ _ _ regs _ HB_KEPT1 HS HAE1 ltac:(vm_compute; reflexivity)) as KR.
    cbn [ms_regs restrict] in KR.
    prreg HS (23%bv : bv 5) Q23. prreg HS (20%bv : bv 5) Q20. prreg HS (6%bv : bv 5) Q6.
    hb_prreg_raw HS (11%bv : bv 5) Q11.
    prreg HS (21%bv : bv 5) Q21.
    hb_nout0 HS E26 HN0.
    pmkst HS.
    apply SRr_ret. right; left.
    lazymatch goal with |- hb_INV_P_xR _ _ _ {| cfg_ms := mkst ?r _ ?mm _; cfg_model := ?d |} => exists r, mm, d end.
    split; [reflexivity|].
    apply (hb_w1_lcut_xR cx t W mem md _ _ ly3 S3 k m fpos (hb_lregs_P cx t) _ HB HJ0 HJ MEQ MG HN0 HFR HFL HMOD HIN HRV HSEP HLS HNP HRI HROM).
    unfold hb_lregs_P. cbn [lm_k lm_O lm_clear_O].
    rewrite E21 in Q21, Q6. rewrite E22 in Q20. rewrite unsigned_lit_small in Q20, Q6 by lia.
    split; [unfold lregs_common; repeat split; first [ rewrite Q23; reflexivity
      | match goal with |- getr _ ?r = _ => rewrite (KR r ltac:(hb_in)) end; assumption ]|].
    split; [rewrite (KR 25%bv ltac:(hb_in)); exact R25|].
    split; [exact Ht|]. split; [lia|]. split; [reflexivity|].
    split; [exact Q21|].
    split; [rewrite (KR 22%bv ltac:(hb_in)); exact R22|].
    split; [rewrite Q11; apply hb_sv_of_U; [exact UO | lia]|].
    split; [apply hb_picks14; exact (conj Hc1 Hc2)|].
    split; [rewrite Q20; unfold w64; f_equal; lia|].
    rewrite Q6; unfold w64; f_equal; lia.
  - unfold hb_opsv in UO. rewrite branch_ltu_U, U_SAlu, UO, hb_cls_ltu in Hc by lia. fold hb_opsv in UO.
    rename Hc into Hcls.
    paj_run_tok_x RUNR HS HJ SHOK hb_Bspan.
    { hb_awr E26 HGnout. }
    hb_upd E26 MEQ MG.
    lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
      assert (UO2 : U Ev hb_opsv = in_byte cx (lm_k m) mod 10) by (apply UOP; rewrite ?ew_ewset_other by lia; reflexivity);
      assert (HAE2 : env_agree 32 (Ereg regs (hb_x1 (in_byte cx (lm_k m)))) Ev)
        by (split; [intros m0 Hm; rewrite ?ew_ewset_other by lia; exact (proj1 HAE m0 Hm) | rewrite ?ed_ewset; exact (proj2 HAE)])
    end.
    clear UO HAE1. rename UO2 into UO. rename HAE2 into HAE1.
    psrr_branch_tok RUNR BR HS SHOK hb_Bspan.
    + (* op not in 1..4, op <> 6: no source (0x84758 li s5,0); to the dispatch *)
      unfold hb_opsv in UO. rewrite branch_ne_U, UO, U_lit in Hc by lia. fold hb_opsv in UO.
      apply negb_true_iff, Z.eqb_neq in Hc.
      pose proof (hb_picks_no (in_byte cx (lm_k m) mod 10) ltac:(lia) Hcls Hc) as Hpk.
      paj_run_to_tok_x RUNTOR HS HJ SHOK hb_Bspan AF_LLVM_dispatch.
      { hb_awr E26 HGnout. }
      hb_upd E26 MEQ MG.
      pose proof (regs_kept_of_st_ok_pi _ _ _ regs _ HB_KEPT1 HS HAE1 ltac:(vm_compute; reflexivity)) as KR.
      cbn [ms_regs restrict] in KR.
      prreg HS (23%bv : bv 5) Q23. prreg HS (20%bv : bv 5) Q20. prreg HS (6%bv : bv 5) Q6.
      hb_prreg_raw HS (11%bv : bv 5) Q11.
      prreg HS (21%bv : bv 5) Q21.
      hb_nout0 HS E26 HN0.
      pmkst HS.
      apply SRr_ret. left. exists (in_byte cx (lm_k m) mod 10). split; [lia|].
      lazymatch goal with |- INV_D_xR _ _ _ _ PST ARx _ _ _ _ [] _ _ _ {| cfg_ms := mkst ?r _ ?mm _; cfg_model := ?d |} => exists r, mm, d end.
      split; [reflexivity|].
      split; [rewrite Q11; apply hb_sv_of_U; [exact UO | lia]|].
      rewrite ?wvb_collapse in HJ.
      split; [exists [(1, fpos)], ly3, S3, [], k; exact HJ|].
      apply (hb_w1_lcut_xR cx t W mem md _ _ ly3 S3 k m fpos (lregs_D B cx t) _ HB HJ0 HJ MEQ MG HN0 HFR HFL HMOD HIN HRV HSEP HLS HNP HRI HROM).
      unfold lregs_D. cbv zeta. cbn [lm_k lm_O lm_clear_O]. rewrite Hpk. cbv iota.
      rewrite E21 in Q6. rewrite E22 in Q20. rewrite unsigned_lit_small in Q20, Q6 by lia.
      split; [unfold lregs_common; repeat split; first [ rewrite Q23; reflexivity
        | match goal with |- getr _ ?r = _ => rewrite (KR r ltac:(hb_in)) end; assumption ]|].
      split; [rewrite (KR 25%bv ltac:(hb_in)); exact R25|].
      split; [exact Ht|]. split; [lia|]. split; [reflexivity|].
      split; [rewrite Q11; apply hb_sv_of_U; [exact UO | lia]|].
      split; [rewrite Q20; unfold w64; f_equal; lia|].
      split; [rewrite Q6; unfold w64; f_equal; lia|].
      rewrite Q21. reflexivity.
    + (* op = 6: on to the pick *)
      unfold hb_opsv in UO. rewrite branch_ne_U, UO, U_lit in Hc by lia. fold hb_opsv in UO.
      apply negb_false_iff, Z.eqb_eq in Hc.
      paj_run_to_tok_x RUNTOR HS HJ SHOK hb_Bspan AF_LLVM_pick.
      { hb_awr E26 HGnout. }
      hb_upd E26 MEQ MG.
      pose proof (regs_kept_of_st_ok_pi _ _ _ regs _ HB_KEPT1 HS HAE1 ltac:(vm_compute; reflexivity)) as KR.
      cbn [ms_regs restrict] in KR.
      prreg HS (23%bv : bv 5) Q23. prreg HS (20%bv : bv 5) Q20. prreg HS (6%bv : bv 5) Q6.
      hb_prreg_raw HS (11%bv : bv 5) Q11.
      prreg HS (21%bv : bv 5) Q21.
      hb_nout0 HS E26 HN0.
      pmkst HS.
      apply SRr_ret. right; left.
      lazymatch goal with |- hb_INV_P_xR _ _ _ {| cfg_ms := mkst ?r _ ?mm _; cfg_model := ?d |} => exists r, mm, d end.
      split; [reflexivity|].
      apply (hb_w1_lcut_xR cx t W mem md _ _ ly3 S3 k m fpos (hb_lregs_P cx t) _ HB HJ0 HJ MEQ MG HN0 HFR HFL HMOD HIN HRV HSEP HLS HNP HRI HROM).
      unfold hb_lregs_P. cbn [lm_k lm_O lm_clear_O].
      rewrite E21 in Q21, Q6. rewrite E22 in Q20. rewrite unsigned_lit_small in Q20, Q6 by lia.
      split; [unfold lregs_common; repeat split; first [ rewrite Q23; reflexivity
        | match goal with |- getr _ ?r = _ => rewrite (KR r ltac:(hb_in)) end; assumption ]|].
      split; [rewrite (KR 25%bv ltac:(hb_in)); exact R25|].
      split; [exact Ht|]. split; [lia|]. split; [reflexivity|].
      split; [exact Q21|].
      split; [rewrite (KR 22%bv ltac:(hb_in)); exact R22|].
      split; [rewrite Q11; apply hb_sv_of_U; [exact UO | lia]|].
      split; [rewrite Hc; reflexivity|].
      split; [rewrite Q20; unfold w64; f_equal; lia|].
      rewrite Q6; unfold w64; f_equal; lia.
Qed.
(* R twin of hb_w2_x *)
Lemma hb_w2_xR : forall cx t W c, lf_base_x B MT XM_LIB RLO RHI fr_live_pre LIBROOM NP G_fr ARx cx [] -> hb_INV_P_xR cx t W c ->
  SRr segs W c (fun W' c' => (exists op, 0 <= op <= 9 /\ INV_D_xR B NP G_fr fr_FP PST ARx LSx RINV R cx [] t op W' c') \/
    INV_A_xR B NP G_fr fr_FP PST ARx LSx RINV R 1 cx [] t W' c' \/ INV_H_xR B NP G_fr fr_FP PST ARx LSx RINV R cx [] (t + 1) W' c' \/
    INV_X_xR B NP G_fr fr_FP PST ARx LSx RINV R cx [] W' c').
Proof.
  intros cx t W c HB (regs & mem & md & -> & HROM &
    (own & ly3 & S3 & Hp3 & k & m & fpos & HJ & -> & HFR & HFL & HMOD & HIN & HRV & HSEP & HLS & HNP & HRI & HR)).
  destruct HR as ((R2 & R8 & R9 & R18 & R19 & R23 & R24 & R26 & R27 & R3 & R4) & R25 & Ht & Hk & HO &
    R21 & R22 & R11 & Hpk & R20 & R6).
  pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  pose proof HB as (HAI & HPRE & Hra & Ha0 & Ha1 & Hblk0 & Hlen & _).
  pose proof HPRE as (HAR0 & Hra0 & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
  pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
  pose proof (ajournal_gx_AR_xR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as HAR.
  (* the cut's ghost list is [] (HP0 at the journal's end state) *)
  pose proof (HP0 _ _ _ _ _ _ HAR) as Ehp3. subst Hp3.
  pose proof HIN as [[[Hn00 _] | [Hnr Hblk]] Hgarr]; [lia|].
  destruct (alx_blocks _ _ ARx LAWS _ _ [] _ _ _ _ _ HAR Hblk) as (Hp16 & Hp4096 & Hpceil & Hpia & _ & _).
  pose proof (hb_blk_imgP_x _ _ _ _ _ _ _ _ HAR Hblk ltac:(lia)) as Hpimg.
  pose proof (req_size_pos (c_n cx) ltac:(lia)) as [_ Hreq].
  pose proof (Z.mod_pos_bound (spZ (c_regs cx) - 320) 32 ltac:(lia)) as HFm.
  assert (HFb : spZ (c_regs cx) - 351 <= lf_F cx <= spZ (c_regs cx) - 320) by (unfold lf_F; lia).
  unfold YCfn.LLVMF_STK in *.
  pose proof HFR as (FS & FW & F32 & F40 & F48 & F56 & F64 & F72 & F80 & F96 & F104 & F120 & F128 & F136 & F152 & _).
  pose proof HMOD as (Hhs4 & Hslots & _).
  destruct (hb_in_byte cx (arm W mem) (lm_k m) Hgarr ltac:(lia)) as [MB0 Rb0].
  pose proof (Z.mod_pos_bound (in_byte cx (lm_k m)) 10 ltac:(lia)) as Rop.
  pose proof Ht as Ht'. unfold OPS_MAX in Ht'.
  assert (Hkb : 0 <= hd_kb cx m < 256).
  { unfold hd_kb. destruct (lm_k m + 1 <? c_n cx) eqn:Hm1; [|lia].
    apply Z.ltb_lt in Hm1. exact (proj2 (hb_in_byte cx (arm W mem) (lm_k m + 1) Hgarr ltac:(lia))). }
  assert (MB1 : (lm_k m + 1 <? c_n cx) = true ->
      val_mem segs (mrestrict (w_H W) mem) (c_p cx + lm_k m + 1) 1 (hd_kb cx m)).
  { intros Hm1. unfold hd_kb. rewrite Hm1. apply Z.ltb_lt in Hm1. rewrite <- Z.add_assoc.
    exact (proj1 (hb_in_byte cx (arm W mem) (lm_k m + 1) Hgarr ltac:(lia))). }
  assert (RA1 : (lm_k m + 1 <? c_n cx) = true ->
      range_addressable (aview segs (w_H W) mem) SHADOW_OFF (c_p cx + lm_k m + 1) 1).
  { intros Hm1. apply Z.ltb_lt in Hm1.
    apply (range_addressable_of_block_hp0_x segs B ARx LAWS HP0 ly3 S3 [] W mem md (c_p cx) (c_n cx)); [exact HAR | exact Hblk | lia | lia]. }
  pose proof (hb_gs_shadow_x ly3 S3 W mem md HAR) as SH0.
  pose proof (hb_open_val ly3 S3 W mem 0 _ (Hslots 0%nat ltac:(lia))) as G0.
  pose proof (hb_open_val ly3 S3 W mem 1 _ (Hslots 1%nat ltac:(lia))) as G1.
  pose proof (hb_open_val ly3 S3 W mem 2 _ (Hslots 2%nat ltac:(lia))) as G2.
  pose proof (hb_open_val ly3 S3 W mem 3 _ (Hslots 3%nat ltac:(lia))) as G3.
  pose proof Hhs4 as Hl4.
  destruct (lm_hs m) as [|o0 [|o1 [|o2 [|o3 [|o4 rest]]]]] eqn:Hhs; cbn [length] in Hl4; try discriminate Hl4.
  rewrite ?Hhs in G0, G1, G2, G3. cbn [nth] in G0, G1, G2, G3.
  destruct (hb_entry2 W regs mem (lm_k m + 1 <? c_n cx) (hb_isS o0) (hb_isS o1) (hb_isS o2) (hb_isS o3) (c_p cx + lm_k m + 1)
    (lf_F cx) (hd_kb cx m) R23 R9 R27 R20 ltac:(lia) Hkb ltac:(lia) ltac:(lia)
    ltac:(intros Hm1; apply Z.ltb_lt in Hm1; lia)
    ltac:(intros Hm1; apply Z.ltb_lt in Hm1; unfold in_app in Hpia; unfold kLowShadowBeg, kHighMemBeg in *; lia)
    ltac:(intros Hm1; apply Z.ltb_lt in Hm1; lia)
    MB1 RA1 F128 F152 G0 G1 G2 G3 SH0) as [HS SHOK].
  remember (Eimg (Ereg regs (hb_x1 (hd_kb cx m)))) as E eqn:HE.
  assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
  assert (EEo : forall m (rr : bv 5), Z.of_nat m = bv_unsigned rr -> ew E m = getr regs rr)
    by (intros m0 rr Hm; subst E; pose proof (bv_unsigned_in_range 5 rr) as Hr5; change (bv_modulus 5) with 32 in Hr5;
        rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_nat; exact Hm).
  assert (E11 : ew E 11 = Z_to_bv 64 (in_byte cx (lm_k m) mod 10)) by (rewrite (EEo 11%nat 11%bv eq_refl); exact R11).
  assert (E21 : ew E 21 = Z_to_bv 64 (c_n cx - lm_k m)) by (rewrite (EEo 21%nat 21%bv eq_refl); exact R21).
  assert (E22 : ew E 22 = Z_to_bv 64 (c_p cx + lm_k m)) by (rewrite (EEo 22%nat 22%bv eq_refl); exact R22).
  assert (E25 : ew E 25 = Z_to_bv 64 t) by (rewrite (EEo 25%nat 25%bv eq_refl); exact R25).
  assert (E20 : ew E 20 = Z_to_bv 64 (c_p cx + lm_k m + 1)) by (rewrite (EEo 20%nat 20%bv eq_refl); exact R20).
  assert (E6 : ew E 6 = Z_to_bv 64 (c_n cx - lm_k m - 1)) by (rewrite (EEo 6%nat 6%bv eq_refl); exact R6).
  assert (E32 : ew E 32 = Z_to_bv 64 (hd_kb cx m))
    by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
  assert (UG : bv_unsigned (ew E 260) = rg_s fr_RG).
  { subst E. rewrite Eimg_img by (unfold A_TEXT, A_LIM; lia). change 260%nat with (A_OBJ 19). rewrite hb_VAL_gs.
    first [reflexivity | apply unsigned_lit_small; cbn; lia]. }
  assert (HAE : env_agree 32 (Ereg regs (hb_x1 (hd_kb cx m))) E)
    by (rewrite HE; split; [intros m0 Hm; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
  clear HE.
  assert (EG' : ew E 260 = Z_to_bv 64 (rg_s fr_RG)) by (rewrite <- UG; symmetry; apply Z_to_bv_bv_unsigned).
  assert (Hnone : (lm_hs m = [None; None; None; None]) -> pick (lm_hs m) (hd_kb cx m) = None)
    by (intros Hn; unfold pick, nopen; rewrite Hn; reflexivity).
  unfold cfg_at. change (w64 (fr_B0 + AF_LLVM_pick)) with (Z_to_bv 64 (BASE + AF_LLVM_pick)).
  revert HS SHOK. destruct (lm_k m + 1 <? c_n cx) eqn:Hmore; intros HS SHOK.
  all: destruct o0 as [h0|]; destruct o1 as [h1|]; destruct o2 as [h2|]; destruct o3 as [h3|].
  all: cbn [hb_isS] in HS; norm_ss HS; cbn [hb_SH2] in SHOK.
  (* the test of in.n - 1 (t1): the side that contradicts `more` is refuted *)
  all: psrr_branch_tok RUNR BR HS SHOK hb_Bspan.
  all: rewrite branch_eq_U, (U_atom E 6 (c_n cx - lm_k m - 1) E6), U_lit in Hc by lia.
  all: try (exfalso; first [apply Z.eqb_eq in Hc | apply Z.eqb_neq in Hc];
    first [apply Z.ltb_lt in Hmore | apply Z.ltb_ge in Hmore]; lia).
  all: clear Hc.
  (* the second byte (when in.n > 1) with its PTR_INC trap, the open count with its ADDW trap, to the remainder
     (0x846c4), or, with no open source, to `bne a1,s7` (0x8471c) *)
  all: paj_run_to_tok_x RUNTOR HS HJ SHOK hb_Bspan 9088.
  all: try hb_awr0.
  all: hb_meq mem.
  32:
  { psrr_branch_tok RUNR BR HS SHOK hb_Bspan.
    - (* op <> 1: `continue`, to B's latch tail 0x8480c *)
      lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
        rewrite branch_ne_U, (U_atom_off Ev 11 _ 0 ltac:(rewrite ?ew_ewset_other by lia; exact E11) ltac:(lia) ltac:(lia)), U_lit in Hc by lia end.
      rewrite Z.add_0_r in Hc. apply negb_true_iff, Z.eqb_neq in Hc. rename Hc into Hop1.
      paj_run_tok_x RUNR HS HJ SHOK hb_Bspan. { hb_awr0. } hb_meq mem.
      psrr_branch_tok RUNR BR HS SHOK hb_Bspan.
      + (* t + 1 <> 512: the head of operation t + 1 *)
        lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
          rewrite branch_ne_U, (hb_addiw_U Ev t ltac:(rewrite ?ew_ewset_other by lia; exact E25) ltac:(lia)), U_lit in Hc by lia end.
        apply negb_true_iff, Z.eqb_neq in Hc. rename Hc into Ht1.
        paj_run_to_tok_x RUNTOR HS HJ SHOK hb_Bspan AF_LLVM_head. { hb_awr0. } hb_meq mem.
        lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
        assert (HAEv : env_agree 32 (Ereg regs (hb_x1 (hd_kb cx m))) Ev)
          by (split; [intros m0 Hm; rewrite ?ew_ewset_other by lia; exact (proj1 HAE m0 Hm) | rewrite ?ed_ewset; exact (proj2 HAE)]);
        assert (U25 : U Ev (SAluw ALU_ADD (SOff 25 0) (SLit 1)) = t + 1)
          by (apply hb_addiw_U; [rewrite ?ew_ewset_other by lia; exact E25 | lia]) end.
        pose proof (regs_kept_of_st_ok_pi _ _ _ regs _ HB_KEPT3 HS HAEv ltac:(vm_compute; reflexivity)) as KR.
        cbn [ms_regs restrict] in KR.
        prreg HS (23%bv : bv 5) Q23. prreg HS (21%bv : bv 5) Q21. prreg HS (22%bv : bv 5) Q22.
        hb_prreg_raw HS (25%bv : bv 5) Q25.
        pmkst HS. rewrite HMm. rewrite HMm in HJ.
        apply SRr_ret. right; right; left.
        lazymatch goal with |- INV_H_xR _ _ _ _ PST ARx _ _ _ _ [] _ _ {| cfg_ms := mkst ?r _ ?mm _; cfg_model := ?d |} => exists r, mm, d end.
        split; [reflexivity|]. split; [exact HROM|].
        exists [(1, fpos)], ly3, S3, [], k, (lm_set_k m (hd_k' cx m)), fpos.
        split; [exact HJ|]. split; [reflexivity|]. split; [exact HFR|]. split; [exact HFL|].
        split; [exact HMOD|]. split; [exact HIN|]. split; [exact HRV|]. split; [exact HSEP|].
        split; [apply LS_head_skip; [exact Ht | exact Hk | exact HO | exact Hpk | exact Hop1 | apply Hnone; exact Hhs |]; exact HLS|]. split; [exact HNP|].
        split; [apply RI_head_skip; [exact Ht | exact Hk | exact HO | exact Hpk | exact Hop1 | apply Hnone; exact Hhs |]; exact HRI|].
        unfold lregs_H. cbn [lm_k lm_set_k]. unfold hd_k'. rewrite Hmore. cbv iota.
        rewrite ?ew_ewset_other in Q21, Q22 by lia.
        rewrite ?E21 in Q21. rewrite ?E6 in Q21. rewrite ?E22 in Q22. rewrite ?E20 in Q22.
        rewrite ?unsigned_lit_small in Q21 by lia. rewrite ?unsigned_lit_small in Q22 by lia.
        first [apply Z.ltb_lt in Hmore | apply Z.ltb_ge in Hmore].
        split; [unfold lregs_common; repeat split; first [ rewrite Q23; reflexivity
          | match goal with |- getr _ ?r = _ => rewrite (KR r ltac:(hb_in)) end; assumption ]|].
        split; [rewrite Q25; apply hb_sv_of_U; [exact U25 | lia]|].
        split; [rewrite Q21; unfold w64; f_equal; lia|].
        split; [rewrite Q22; unfold w64; f_equal; lia|].
        unfold OPS_MAX in *. lia.
      + (* t + 1 = 512: the shutdown block *)
        paj_run_to_tok_x RUNTOR HS HJ SHOK hb_Bspan AF_LLVM_exit. { hb_awr0. } hb_meq mem.
        lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
        assert (HAEv : env_agree 32 (Ereg regs (hb_x1 (hd_kb cx m))) Ev)
          by (split; [intros m0 Hm; rewrite ?ew_ewset_other by lia; exact (proj1 HAE m0 Hm) | rewrite ?ed_ewset; exact (proj2 HAE)]) end.
        pose proof (regs_kept_of_st_ok_pi _ _ _ regs _ HB_KEPT3 HS HAEv ltac:(vm_compute; reflexivity)) as KR.
        cbn [ms_regs restrict] in KR.
        pmkst HS. rewrite HMm. rewrite HMm in HJ.
        apply SRr_ret. right; right; right.
        lazymatch goal with |- INV_X_xR _ _ _ _ PST ARx _ _ _ _ [] _ {| cfg_ms := mkst ?r _ ?mm _; cfg_model := ?d |} => exists r, mm, d, (t + 1) end.
        split; [reflexivity|]. split; [exact HROM|].
        exists [(1, fpos)], ly3, S3, [], k, (lm_set_k m (hd_k' cx m)), fpos.
        split; [exact HJ|]. split; [reflexivity|]. split; [exact HFR|]. split; [exact HFL|].
        split; [exact HMOD|]. split; [exact HIN|]. split; [exact HRV|]. split; [exact HSEP|].
        split; [apply LS_head_skip; [exact Ht | exact Hk | exact HO | exact Hpk | exact Hop1 | apply Hnone; exact Hhs |]; exact HLS|]. split; [exact HNP|].
        split; [apply RI_head_skip; [exact Ht | exact Hk | exact HO | exact Hpk | exact Hop1 | apply Hnone; exact Hhs |]; exact HRI|].
        cbv beta. unfold lregs_X. cbn [lm_k lm_set_k]. unfold hd_k'. rewrite Hmore. cbv iota.
        first [apply Z.ltb_lt in Hmore | apply Z.ltb_ge in Hmore].
        repeat split; first [ match goal with |- getr _ ?r = _ => rewrite (KR r ltac:(hb_in)) end; assumption | lia ].
    - (* op = 1 with no open source: arm 1 (0x84724) with s5 = 0 *)
      lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
        rewrite branch_ne_U, (U_atom_off Ev 11 _ 0 ltac:(rewrite ?ew_ewset_other by lia; exact E11) ltac:(lia) ltac:(lia)), U_lit in Hc by lia end.
      rewrite Z.add_0_r in Hc. apply negb_false_iff, Z.eqb_eq in Hc. rename Hc into Hop1.
      paj_run_to_tok_x RUNTOR HS HJ SHOK hb_Bspan AF_arm_write. { hb_awr0. } hb_meq mem.
      lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
      assert (HAEv : env_agree 32 (Ereg regs (hb_x1 (hd_kb cx m))) Ev)
        by (split; [intros m0 Hm; rewrite ?ew_ewset_other by lia; exact (proj1 HAE m0 Hm) | rewrite ?ed_ewset; exact (proj2 HAE)]) end.
      pose proof (regs_kept_of_st_ok_pi _ _ _ regs _ HB_KEPT2 HS HAEv ltac:(vm_compute; reflexivity)) as KR.
      cbn [ms_regs restrict] in KR.
      prreg HS (23%bv : bv 5) Q23. prreg HS (20%bv : bv 5) Q20. prreg HS (6%bv : bv 5) Q6.
      prreg HS (21%bv : bv 5) Q21.
      pmkst HS. rewrite HMm. rewrite HMm in HJ.
      apply SRr_ret. right; left.
      lazymatch goal with |- INV_A_xR _ _ _ _ PST ARx _ _ _ _ _ [] _ _ {| cfg_ms := mkst ?r _ ?mm _; cfg_model := ?d |} => exists r, r, mm, d end.
      split; [reflexivity|]. split; [intros rr _; reflexivity|].
      split; [rewrite (KR 11%bv ltac:(hb_in)), R11, Hop1; reflexivity|].
      split; [exists [(1, fpos)], ly3, S3, [], k; exact HJ|]. split; [exact HROM|].
      exists [(1, fpos)], ly3, S3, [], k, m, fpos.
      split; [exact HJ|]. split; [reflexivity|]. split; [exact HFR|]. split; [exact HFL|].
      split; [exact HMOD|]. split; [exact HIN|]. split; [exact HRV|]. split; [exact HSEP|].
      split; [exact HLS|]. split; [exact HNP|]. split; [exact HRI|].
      unfold lregs_D. cbv zeta. rewrite Hpk. cbv iota. rewrite Hmore. cbv iota.
      rewrite ?ew_ewset_other in Q20, Q6 by lia.
      rewrite ?E22 in Q20. rewrite ?E20 in Q20. rewrite ?E21 in Q6. rewrite ?E6 in Q6.
      rewrite ?unsigned_lit_small in Q20 by lia. rewrite ?unsigned_lit_small in Q6 by lia.
      split; [unfold lregs_common; repeat split; first [ rewrite Q23; reflexivity
        | match goal with |- getr _ ?r = _ => rewrite (KR r ltac:(hb_in)) end; assumption ]|].
      split; [rewrite (KR 25%bv ltac:(hb_in)); exact R25|].
      split; [exact Ht|]. split; [exact Hk|]. split; [exact HO|].
      split; [rewrite (KR 11%bv ltac:(hb_in)); exact R11|].
      split; [rewrite Q20; unfold w64; f_equal; lia|].
      split; [rewrite Q6; unfold w64; f_equal; lia|].
      right. split; [exact Hop1|]. split; [unfold pick, nopen; rewrite Hhs; reflexivity|]. rewrite Q21. reflexivity.
  }
  16:
  { psrr_branch_tok RUNR BR HS SHOK hb_Bspan.
    - (* op <> 1: `continue`, to B's latch tail 0x8480c *)
      lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
        rewrite branch_ne_U, (U_atom_off Ev 11 _ 0 ltac:(rewrite ?ew_ewset_other by lia; exact E11) ltac:(lia) ltac:(lia)), U_lit in Hc by lia end.
      rewrite Z.add_0_r in Hc. apply negb_true_iff, Z.eqb_neq in Hc. rename Hc into Hop1.
      paj_run_tok_x RUNR HS HJ SHOK hb_Bspan. { hb_awr0. } hb_meq mem.
      psrr_branch_tok RUNR BR HS SHOK hb_Bspan.
      + (* t + 1 <> 512: the head of operation t + 1 *)
        lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
          rewrite branch_ne_U, (hb_addiw_U Ev t ltac:(rewrite ?ew_ewset_other by lia; exact E25) ltac:(lia)), U_lit in Hc by lia end.
        apply negb_true_iff, Z.eqb_neq in Hc. rename Hc into Ht1.
        paj_run_to_tok_x RUNTOR HS HJ SHOK hb_Bspan AF_LLVM_head. { hb_awr0. } hb_meq mem.
        lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
        assert (HAEv : env_agree 32 (Ereg regs (hb_x1 (hd_kb cx m))) Ev)
          by (split; [intros m0 Hm; rewrite ?ew_ewset_other by lia; exact (proj1 HAE m0 Hm) | rewrite ?ed_ewset; exact (proj2 HAE)]);
        assert (U25 : U Ev (SAluw ALU_ADD (SOff 25 0) (SLit 1)) = t + 1)
          by (apply hb_addiw_U; [rewrite ?ew_ewset_other by lia; exact E25 | lia]) end.
        pose proof (regs_kept_of_st_ok_pi _ _ _ regs _ HB_KEPT3 HS HAEv ltac:(vm_compute; reflexivity)) as KR.
        cbn [ms_regs restrict] in KR.
        prreg HS (23%bv : bv 5) Q23. prreg HS (21%bv : bv 5) Q21. prreg HS (22%bv : bv 5) Q22.
        hb_prreg_raw HS (25%bv : bv 5) Q25.
        pmkst HS. rewrite HMm. rewrite HMm in HJ.
        apply SRr_ret. right; right; left.
        lazymatch goal with |- INV_H_xR _ _ _ _ PST ARx _ _ _ _ [] _ _ {| cfg_ms := mkst ?r _ ?mm _; cfg_model := ?d |} => exists r, mm, d end.
        split; [reflexivity|]. split; [exact HROM|].
        exists [(1, fpos)], ly3, S3, [], k, (lm_set_k m (hd_k' cx m)), fpos.
        split; [exact HJ|]. split; [reflexivity|]. split; [exact HFR|]. split; [exact HFL|].
        split; [exact HMOD|]. split; [exact HIN|]. split; [exact HRV|]. split; [exact HSEP|].
        split; [apply LS_head_skip; [exact Ht | exact Hk | exact HO | exact Hpk | exact Hop1 | apply Hnone; exact Hhs |]; exact HLS|]. split; [exact HNP|].
        split; [apply RI_head_skip; [exact Ht | exact Hk | exact HO | exact Hpk | exact Hop1 | apply Hnone; exact Hhs |]; exact HRI|].
        unfold lregs_H. cbn [lm_k lm_set_k]. unfold hd_k'. rewrite Hmore. cbv iota.
        rewrite ?ew_ewset_other in Q21, Q22 by lia.
        rewrite ?E21 in Q21. rewrite ?E6 in Q21. rewrite ?E22 in Q22. rewrite ?E20 in Q22.
        rewrite ?unsigned_lit_small in Q21 by lia. rewrite ?unsigned_lit_small in Q22 by lia.
        first [apply Z.ltb_lt in Hmore | apply Z.ltb_ge in Hmore].
        split; [unfold lregs_common; repeat split; first [ rewrite Q23; reflexivity
          | match goal with |- getr _ ?r = _ => rewrite (KR r ltac:(hb_in)) end; assumption ]|].
        split; [rewrite Q25; apply hb_sv_of_U; [exact U25 | lia]|].
        split; [rewrite Q21; unfold w64; f_equal; lia|].
        split; [rewrite Q22; unfold w64; f_equal; lia|].
        unfold OPS_MAX in *. lia.
      + (* t + 1 = 512: the shutdown block *)
        paj_run_to_tok_x RUNTOR HS HJ SHOK hb_Bspan AF_LLVM_exit. { hb_awr0. } hb_meq mem.
        lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
        assert (HAEv : env_agree 32 (Ereg regs (hb_x1 (hd_kb cx m))) Ev)
          by (split; [intros m0 Hm; rewrite ?ew_ewset_other by lia; exact (proj1 HAE m0 Hm) | rewrite ?ed_ewset; exact (proj2 HAE)]) end.
        pose proof (regs_kept_of_st_ok_pi _ _ _ regs _ HB_KEPT3 HS HAEv ltac:(vm_compute; reflexivity)) as KR.
        cbn [ms_regs restrict] in KR.
        pmkst HS. rewrite HMm. rewrite HMm in HJ.
        apply SRr_ret. right; right; right.
        lazymatch goal with |- INV_X_xR _ _ _ _ PST ARx _ _ _ _ [] _ {| cfg_ms := mkst ?r _ ?mm _; cfg_model := ?d |} => exists r, mm, d, (t + 1) end.
        split; [reflexivity|]. split; [exact HROM|].
        exists [(1, fpos)], ly3, S3, [], k, (lm_set_k m (hd_k' cx m)), fpos.
        split; [exact HJ|]. split; [reflexivity|]. split; [exact HFR|]. split; [exact HFL|].
        split; [exact HMOD|]. split; [exact HIN|]. split; [exact HRV|]. split; [exact HSEP|].
        split; [apply LS_head_skip; [exact Ht | exact Hk | exact HO | exact Hpk | exact Hop1 | apply Hnone; exact Hhs |]; exact HLS|]. split; [exact HNP|].
        split; [apply RI_head_skip; [exact Ht | exact Hk | exact HO | exact Hpk | exact Hop1 | apply Hnone; exact Hhs |]; exact HRI|].
        cbv beta. unfold lregs_X. cbn [lm_k lm_set_k]. unfold hd_k'. rewrite Hmore. cbv iota.
        first [apply Z.ltb_lt in Hmore | apply Z.ltb_ge in Hmore].
        repeat split; first [ match goal with |- getr _ ?r = _ => rewrite (KR r ltac:(hb_in)) end; assumption | lia ].
    - (* op = 1 with no open source: arm 1 (0x84724) with s5 = 0 *)
      lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
        rewrite branch_ne_U, (U_atom_off Ev 11 _ 0 ltac:(rewrite ?ew_ewset_other by lia; exact E11) ltac:(lia) ltac:(lia)), U_lit in Hc by lia end.
      rewrite Z.add_0_r in Hc. apply negb_false_iff, Z.eqb_eq in Hc. rename Hc into Hop1.
      paj_run_to_tok_x RUNTOR HS HJ SHOK hb_Bspan AF_arm_write. { hb_awr0. } hb_meq mem.
      lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
      assert (HAEv : env_agree 32 (Ereg regs (hb_x1 (hd_kb cx m))) Ev)
        by (split; [intros m0 Hm; rewrite ?ew_ewset_other by lia; exact (proj1 HAE m0 Hm) | rewrite ?ed_ewset; exact (proj2 HAE)]) end.
      pose proof (regs_kept_of_st_ok_pi _ _ _ regs _ HB_KEPT2 HS HAEv ltac:(vm_compute; reflexivity)) as KR.
      cbn [ms_regs restrict] in KR.
      prreg HS (23%bv : bv 5) Q23. prreg HS (20%bv : bv 5) Q20. prreg HS (6%bv : bv 5) Q6.
      prreg HS (21%bv : bv 5) Q21.
      pmkst HS. rewrite HMm. rewrite HMm in HJ.
      apply SRr_ret. right; left.
      lazymatch goal with |- INV_A_xR _ _ _ _ PST ARx _ _ _ _ _ [] _ _ {| cfg_ms := mkst ?r _ ?mm _; cfg_model := ?d |} => exists r, r, mm, d end.
      split; [reflexivity|]. split; [intros rr _; reflexivity|].
      split; [rewrite (KR 11%bv ltac:(hb_in)), R11, Hop1; reflexivity|].
      split; [exists [(1, fpos)], ly3, S3, [], k; exact HJ|]. split; [exact HROM|].
      exists [(1, fpos)], ly3, S3, [], k, m, fpos.
      split; [exact HJ|]. split; [reflexivity|]. split; [exact HFR|]. split; [exact HFL|].
      split; [exact HMOD|]. split; [exact HIN|]. split; [exact HRV|]. split; [exact HSEP|].
      split; [exact HLS|]. split; [exact HNP|]. split; [exact HRI|].
      unfold lregs_D. cbv zeta. rewrite Hpk. cbv iota. rewrite Hmore. cbv iota.
      rewrite ?ew_ewset_other in Q20, Q6 by lia.
      rewrite ?E22 in Q20. rewrite ?E20 in Q20. rewrite ?E21 in Q6. rewrite ?E6 in Q6.
      rewrite ?unsigned_lit_small in Q20 by lia. rewrite ?unsigned_lit_small in Q6 by lia.
      split; [unfold lregs_common; repeat split; first [ rewrite Q23; reflexivity
        | match goal with |- getr _ ?r = _ => rewrite (KR r ltac:(hb_in)) end; assumption ]|].
      split; [rewrite (KR 25%bv ltac:(hb_in)); exact R25|].
      split; [exact Ht|]. split; [exact Hk|]. split; [exact HO|].
      split; [rewrite (KR 11%bv ltac:(hb_in)); exact R11|].
      split; [rewrite Q20; unfold w64; f_equal; lia|].
      split; [rewrite Q6; unfold w64; f_equal; lia|].
      right. split; [exact Hop1|]. split; [unfold pick, nopen; rewrite Hhs; reflexivity|]. rewrite Q21. reflexivity.
  }
  (* an open source: the remainder kb % n (pinned to its value), the k-th open source, to the dispatch *)
  all: lazymatch goal with HS : st_ok_pi ?sg ?vl ?Ev ?ss (restrict ?H ?ms) |- _ =>
    let a2 := eval vm_compute in (sr_get (ss_regs ss) 12%bv) in
    lazymatch a2 with
    | SMdw M_REM (SOff 32 0) (SLit ?c) =>
        assert (UR : U Ev (SMdw M_REM (SOff 32 0) (SLit c)) = hd_kb cx m mod c)
          by (apply hb_rem_U; [rewrite ?ew_ewset_other by lia; exact E32 | exact Hkb | lia]);
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
            ltac:(cbn [ms_regs restrict]; rewrite Q12; apply hb_sv_of_U; [rewrite UR; exact HR | lia]) eq_refl) as HS2;
         clear HS; rename HS2 into HS; cbn [ss_pc ss_regs ss_mem ss_resv ss_facts] in HS; norm_ss HS end end).
  all: try (unfold hd_kb in HR; rewrite Hmore in HR; cbv iota in HR).
  all: paj_run_to_tok_x RUNTOR HS HJ SHOK hb_Bspan AF_LLVM_dispatch.
  all: try hb_awr0.
  all: hb_meq mem.
  all: lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
      assert (HAEv : env_agree 32 (Ereg regs (hb_x1 (hd_kb cx m))) Ev)
        by (split; [intros m0 Hm; rewrite ?ew_ewset_other by lia; exact (proj1 HAE m0 Hm) | rewrite ?ed_ewset; exact (proj2 HAE)]) end.
  all: pose proof (regs_kept_of_st_ok_pi _ _ _ regs _ HB_KEPT2 HS HAEv ltac:(vm_compute; reflexivity)) as KR.
  all: cbn [ms_regs restrict] in KR.
  all: prreg HS (23%bv : bv 5) Q23; prreg HS (20%bv : bv 5) Q20; prreg HS (6%bv : bv 5) Q6.
  all: prreg HS (21%bv : bv 5) Q21.
  all: pmkst HS.
  all: rewrite HMm; rewrite HMm in HJ.
  all: apply SRr_ret; left; exists (in_byte cx (lm_k m) mod 10); split; [lia|].
  all: lazymatch goal with |- INV_D_xR _ _ _ _ PST ARx _ _ _ _ [] _ _ _ {| cfg_ms := mkst ?r _ ?mm _; cfg_model := ?d |} => exists r, mm, d end.
  all: split; [reflexivity|].
  all: split; [rewrite (KR 11%bv ltac:(hb_in)); exact R11|].
  all: split; [exists [(1, fpos)], ly3, S3, [], k; exact HJ|].
  all: split; [exact HROM|].
  all: exists [(1, fpos)], ly3, S3, [], k, m, fpos.
  all: split; [exact HJ|]; split; [reflexivity|]; split; [exact HFR|]; split; [exact HFL|]; split; [exact HMOD|]; split; [exact HIN|].
  all: split; [exact HRV|]; split; [exact HSEP|]; split; [exact HLS|]; split; [exact HNP|]; split; [exact HRI|].
  all: unfold lregs_D; cbv zeta; rewrite Hpk; cbv iota; rewrite Hmore; cbv iota.
  all: rewrite ?ew_ewset_other in Q21, Q20, Q6 by lia.
  all: rewrite ?E22 in Q20; rewrite ?E20 in Q20; rewrite ?E21 in Q6; rewrite ?E6 in Q6; rewrite ?EG' in Q21.
  all: rewrite ?unsigned_lit_small in Q21 by (cbn; lia); rewrite ?unsigned_lit_small in Q20 by lia;
    rewrite ?unsigned_lit_small in Q6 by lia.
  all: split; [unfold lregs_common; repeat split; first [ rewrite Q23; reflexivity
      | match goal with |- getr _ ?r = _ => rewrite (KR r ltac:(hb_in)) end; assumption ]|].
  all: split; [rewrite (KR 25%bv ltac:(hb_in)); exact R25|].
  all: split; [exact Ht|]; split; [exact Hk|]; split; [exact HO|].
  all: split; [rewrite (KR 11%bv ltac:(hb_in)); exact R11|].
  all: split; [rewrite Q20; unfold w64; f_equal; lia|].
  all: split; [rewrite Q6; unfold w64; f_equal; lia|].
  all: left; eexists; split.
  all: try (unfold pick; rewrite Hhs;
    lazymatch goal with |- context [nopen ?l] => let v := eval vm_compute in (nopen l) in change (nopen l) with v end;
    try rewrite HR; reflexivity).
  all: rewrite Q21; unfold w64, ASRC; f_equal; cbn [Z.of_nat Pos.of_succ_nat]; cbn; lia.
Qed.
(* R twin of lf_seg_head_nil_x *)
Lemma lf_seg_head_nil_xR : forall cx t W c, lf_base_x B MT XM_LIB RLO RHI fr_live_pre LIBROOM NP G_fr ARx cx [] ->
  INV_H_xR B NP G_fr fr_FP PST ARx LSx RINV R cx [] t W c ->
  SRr segs W c (fun W' c' => (exists op, 0 <= op <= 9 /\ INV_D_xR B NP G_fr fr_FP PST ARx LSx RINV R cx [] t op W' c') \/
    INV_A_xR B NP G_fr fr_FP PST ARx LSx RINV R 1 cx [] t W' c' \/
    INV_H_xR B NP G_fr fr_FP PST ARx LSx RINV R cx [] (t + 1) W' c' \/ INV_X_xR B NP G_fr fr_FP PST ARx LSx RINV R cx [] W' c').
Proof.
  intros cx t W c HB HH.
  eapply SRr_bind; [exact (hb_w1_xR cx t W c HB HH)|].
  intros W1 c1 _ [HD | [HP | HX]].
  - apply SRr_ret. left. exact HD.
  - exact (hb_w2_xR cx t W1 c1 HB HP).
  - apply SRr_ret. right; right; right. exact HX.
Qed.
(* R twin of lf_seg_head_x: B cut_x Section wR's SEG_HEAD_R *)
Theorem lf_seg_head_xR : forall cx Hp t W c,
  lf_base_x B MT XM_LIB RLO RHI fr_live_pre LIBROOM NP G_fr ARx cx Hp ->
  INV_H_xR B NP G_fr fr_FP PST ARx LSx RINV R cx Hp t W c ->
  YA0nH.SRrG segs R W c (fun W' c' => (exists op, 0 <= op <= 9 /\ INV_D_xR B NP G_fr fr_FP PST ARx LSx RINV R cx Hp t op W' c') \/
    INV_A_xR B NP G_fr fr_FP PST ARx LSx RINV R 1 cx Hp t W' c' \/
    INV_H_xR B NP G_fr fr_FP PST ARx LSx RINV R cx Hp (t + 1) W' c' \/ INV_X_xR B NP G_fr fr_FP PST ARx LSx RINV R cx Hp W' c').
Proof.
  pose proof R_refl as _. pose proof R_trans as _. pose proof WLE_R as _.
  intros cx Hp t W c HB HH.
  apply (YA0nH.SRr_SRrG segs R WLE_R).
  assert (Ehp : Hp = []).
  { destruct HB as (_ & HPRE). unfold fr_lib_pre_cf_x in HPRE. destruct HPRE as ((HAR & _) & _).
    exact (HP0 _ _ _ _ _ _ HAR). }
  subst Hp. exact (lf_seg_head_nil_xR cx t W c HB HH).
Qed.
End hxR.

End hx.
