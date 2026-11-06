(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/B/Prog/CrcB.v, with its module paths and module names changed; 1179 of its 1254 lines of code are new or changed and 439 lines of the source are left out. *)
(* fuzz_preset, image B' (#102 pins, asan-ubsan d663f82d): segment X3_B of the walk of check_reject_clean_starved
   (row CRB-X3, a Theorem Labs lane's subagent CrsX3H3). Closing lemma crs_seg_X3_B : the B' kit's crs_from_X3_B (B' +1072 =
   0x82510, fuzz_pick's return site, .. the exits to F and R), from the instance fact HI_head (cf_head =
   PresetReqAt.HEAD; witness crs_seg_X3_B_HI_head_preset below), the callee texts of fuzz_alloc_fail / _live /
   _ran_out at prh_img_B, the kit's transport record (HK : CrsKeep_B), HB_took, the shared writer premise HW_exact
   (CrsWexBp.v: crs_wexact_B, its fourth call = X3_B's injected compact pj_write) and the continuations crs_from_F_B /
   crs_from_R_B. Points (offsets from the entry, read off the B' listing lib/B/Listing_prog.v slots 913 .. 926):
   X3_B +1072 (jal fuzz_alloc_fail, a0 = cPick0_B: on B' the pick comes from H3_B's fuzz_pick CALL, so there is no
   count == s7 arm and no inline remainder) -> P1 +1076 (mv a0, s3; li a1, 0; jal pj_write at +1084, refused; its
   entry events from the kit's run split at X3_B's prefix, PRH_Supply.prhWriter_pjw_evs_w_starved; float form) -> P2
   +1088 (mv s7, a0; li a0, -1; jal fuzz_alloc_fail) -> P3 +1100 (lbu a0, -1340(s8); bnez at +1104: the OWN arm
   refuted by prh_ledger_own) -> P4 +1112 (bnez a0: the RAN arm, ran = 1, -> F with q = 0 and crs_perm_B from the
   writer's failed arm; bnez s7 refuted; jal fuzz_alloc_live) -> P5 +1124 (beq a0, s6 -> R; ABORT refuted).
   DONOR (rule 24, reuse): lane CrsX3H3's own A' file lib/A/Prog/CrsSeg_X3.v blob 769caba6a7fe
   (a working branch 0a0dced97c5), name for name with the kit's _B names; every B' number recomputed on the
   B' listing / PAImg (the STK of pj_write at DOC_D is 23360 here, x3_stk), none shifted from A'.
   rule 24: proves function check_reject_clean_starved on image B' (reuse search: `proof-index check_reject_clean_starved 0x82160`, the internal file
   index-crcs-Aprime.out, and an internal record of that lookup; CONFIRM by checker LookupCheckCrcsAp. At that search origin/ossv/recipes had no lib/A or lib/B, its
   released rows were lib/Prog (plain) and lib/U/Prog (ubsan) only, and no released asan Proof.v existed for check_reject_clean_starved).
   INPUTS: pin B' asan-ubsan sha256 d663f82d7f488d30 (harness.yaml of release/fuzz-preset-ran-out-pins 8f3e7e1a07f1);
   listing lib/B/Listing_prog.v blob c97cc46b3e13 + lib/B/PAImg_prog.v blob 15fab93fe702; image record
   lib/B/PRH_ImgB.v (prh_img_B); the kit's texts at the #102 kit tip, by path; kit lib/B/Prog/CrsKitBp.v +
   CrsWexBp.v at a working branch fb124cd27931. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn YP0b YP0a.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YN3v YI04 YI00 YG0s YP07.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK0o YK06.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YI16 YG0p YCbqG YCbqGcall.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0d YP0c YC80 YPsym YC4aP YC1fP YC80x YC1fPx.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YImgTop YGcfNames YGcfRoomKeep.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YAkMemnorm.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YA0nH YSRrG.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcfRehidePost.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Ledger.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require WriterValue PjWriteHyp WriterApp WriterSpec.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PjTree PjGrammar PresetRoomPos PresetReqAt.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Base.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Reader PRH_FnCheck PRH_FnAlloc PRH_FnWriter.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require PRH_FnPj PRH_FnReader.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Supply CfParamsPreset.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B Require Import Img0 Listing_prog PAImg_prog PRH_ImgB.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require Import PRW_CrsModel PRW_CrcGen.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require Import CrsKitBp CrsWexBp.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require Import PRW_WalkEnvB.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require S1ImgB.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
(* the import closure leaves lia's division / modulo conversion off (the flag below: ZifyNat sets it true, and project modules this file imports after it set it back to false); this file's
   arithmetic over x / 8 needs it, so it is on for this file only *)
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Local Set Warnings "-abstract-large-number".
Local Set Warnings "-notation-for-abbreviation".
Open Scope bv_scope.
Open Scope Z_scope.

(* ======================================================================================================== *)
(* ---- image-free helpers ---- *)
Lemma x3_rget : forall (regs : bvmap 5 word) l (r : bv 5) v, crs_regsat_B regs l -> In (r, v) l -> getr regs r = w64 v.
Proof. intros regs l r v H Hin. unfold crs_regsat_B in H. rewrite Forall_forall in H. exact (H (r, v) Hin). Qed.

(* S10Env.v ts_ap / ts_cs (cold/h-hpreset-7-crt102-tail 090d18ff610, lib/A/Prog/S10Env.v :385-389), restated *)
Lemma x3_ap : forall rg rg' (r : bv 5), aregs_preserved rg rg' -> acallee_saved (bv_unsigned r) -> getr rg' r = getr rg r.
Proof. intros rg rg' r HP Hr. pose proof (HP _ Hr) as Hq. rewrite Z_to_bv_bv_unsigned in Hq. exact Hq. Qed.
Local Ltac x3_cs := unfold acallee_saved;
  lazymatch goal with |- context [bv_unsigned ?x] => let v := eval vm_compute in (bv_unsigned x) in change (bv_unsigned x) with v end;
  lia.

(* S10Env.v ts_rdword_keep (:223-228), restated *)
Lemma x3_rdword_keep : forall (rd rd' : reader) a, (forall j, 0 <= j < 8 -> rd' (a + j) = rd (a + j)) ->
  rdword rd' a = rdword rd a.
Proof.
intros rd rd' a H. pose proof (H 0 ltac:(lia)) as H0. rewrite Z.add_0_r in H0. unfold rdword.
rewrite H0, (H 1), (H 2), (H 3), (H 4), (H 5), (H 6), (H 7) by lia. reflexivity.
Qed.


(* the segment environment TE and its lemmas (lib/A/Prog/PRW_WalkEnv.v's TE part at B'): lib/B/Prog/PRW_WalkEnvB.v,
   Required above; this file's own copy is gone (one copy for the walk) *)

(* the struct pj's shadow hull (F + 32, 56 bytes) lies in its 128-byte frame's 16 shadow bytes, F 32-aligned *)
Lemma x3_hull_frame : forall F s, F mod 32 = 0 ->
  shadow_addr (F + 32) / 8 * 8 <= s < shadow_addr (F + 32 + 56 - 1) / 8 * 8 + 8 ->
  shadow_addr F <= s < shadow_addr F + 16.
Proof.
intros F s HF Hs. destruct (proj1 (Z.mod_divide F 32 ltac:(lia)) HF) as [q ->].
unfold shadow_addr, SHADOW_OFF in *.
replace ((q * 32 + 32) / 8) with (q * 4 + 4) in Hs by (Z.div_mod_to_equations; lia).
replace ((q * 32 + 32 + 56 - 1) / 8) with (q * 4 + 10) in Hs by (Z.div_mod_to_equations; lia).
replace (q * 32 / 8) with (q * 4) by (Z.div_mod_to_equations; lia).
Z.div_mod_to_equations. lia.
Qed.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams} {RL : PrhRoomLive}.
Context {SK : YI16.sink_head}.
#[local] Existing Instance prh_img_B.
(* S1ImgB loads lib/A's image (S1ImgA): the B' listing and image instances are preferred here, so an implicit PAImg /
   PAListing argument is the B' one *)
#[local] Existing Instance PI_prog_B | 0.
#[local] Existing Instance PL_prog_B | 0.
#[local] Notation PA := (PI_prog_B).
#[local] Notation PL := (PL_prog_B).
#[local] Notation SEGS := (@pa_segs _ B_prog_listing PA).
#[local] Notation VAL := (@pa_val _ B_prog_listing PA).
#[local] Notation SIGMA := (@pa_sigma _ B_prog_listing PA).
#[local] Notation BASE := (@pa_val _ B_prog_listing PA A_TEXT).
#[local] Notation RLO := (@pa_relro_lo _ B_prog_listing PA).
#[local] Notation RHI := (@pa_relro_hi _ B_prog_listing PA).
#[local] Notation PST := (prh_pst (PI := prh_img_B)).

(* S10Env.v ts_vm_av / ts_garr_av (:249-262), restated *)
Lemma x3_vm_av : forall (H H' : word -> bool) m m' a n v,
  (forall j, (j < n)%nat -> aview SEGS H' m' (a + Z.of_nat j) = aview SEGS H m (a + Z.of_nat j)) ->
  val_mem SEGS (mrestrict H m) a n v -> val_mem SEGS (mrestrict H' m') a n v.
Proof.
intros H H' m m' a n v Hag HV j Hj. rewrite (mbyte_of_aview SEGS H H' m m' _ (Hag j Hj)). exact (HV j Hj).
Qed.
Lemma x3_garr_av : forall (H H' : word -> bool) m m' a l,
  (forall j, (j < length l)%nat -> aview SEGS H' m' (a + Z.of_nat j) = aview SEGS H m (a + Z.of_nat j)) ->
  garr8 SEGS (mrestrict H m) a l -> garr8 SEGS (mrestrict H' m') a l.
Proof.
intros H H' m m' a l Hag HG j Hj. destruct (HG j Hj) as [V R]. split; [|exact R].
apply (x3_vm_av H H' m m' _ 1 _); [|exact V].
intros i Hi. assert (i = 0%nat) by lia. subst i. cbn [Z.of_nat]. rewrite Z.add_0_r. exact (Hag j Hj).
Qed.

(* ---- the image and the function's numbers, by computation (no ADDRESS literal) ---- *)
Lemma x3_stk : STK_check_reject_clean_starved (PI := prh_img_B) = 27312 /\
  STK_fuzz_alloc_fail (PI := prh_img_B) = 0 /\ STK_fuzz_alloc_live (PI := prh_img_B) = 0 /\
  STK_fuzz_alloc_ran_out (PI := prh_img_B) = 0 /\ STK_fuzz_alloc_count (PI := prh_img_B) = 0 /\
  STK_pj_write (PI := prh_img_B) DOC_D = 23360.
Proof. vm_compute. repeat split; reflexivity. Qed.
Lemma x3_base : 4096 <= BASE + CRS_PC0_B /\ BASE + CRS_PC0_B + 2048 < 2 ^ 31 /\ (BASE + CRS_PC0_B) mod 2 = 0 /\
  0 <= CRS_PC0_B < 2 ^ 20.
Proof. vm_compute. repeat split; first [reflexivity | discriminate]. Qed.

Section f.
Variable B : asyms.
Variable ARx : alayout -> astate -> list Z -> world SEGS -> (word -> option byte) -> Model -> Prop.
Hypothesis LAWS : AR_laws_x SEGS B ARx cf_head.
#[local] Notation AJ := (ajournal_x (SK := SK) SEGS B PST ARx).
#[local] Notation AJR := (ajournal_xR (SK := SK) SEGS B PST ARx).
(* the re-hiding relation of the cuts after pj_parse (the kit's crs_from_X3_B / F / R) *)
#[local] Notation WR := (wle' SEGS YGcfRehidePost.RZ_cf).
#[local] Notation WRr := (wle'_refl SEGS YGcfRehidePost.RZ_cf).
#[local] Notation WRt := (wle'_trans SEGS YGcfRehidePost.RZ_cf).
#[local] Notation WRw := (wle_wle' SEGS YGcfRehidePost.RZ_cf).
#[local] Notation LEDGER := (prh_ledger (PI := prh_img_B) (PA := PA) B).
#[local] Notation STK := (STK_check_reject_clean_starved (PI := prh_img_B)).

(* ---- what crs_pre_B gives about the entry stack ---- *)
Lemma x3_pre_stack : forall CTX0 C, crs_pre_B B ARx CTX0 C ->
  spZ (cb_regs C) mod 16 = 0 /\ YM05.alloc_ceiling + STK <= spZ (cb_regs C) /\ spZ (cb_regs C) + 64 <= ly_stk_hi (cb_ly C) /\
  ly_stk_hi (cb_ly C) <= 2 ^ 47 /\ spZ (cb_regs C) <= ly_top (cb_ly C) <= ly_stk_hi (cb_ly C) /\ 4096 <= raZ (cb_regs C) /\
  achain (cb_ly C) (aview SEGS (w_H (cb_W C)) (cb_mem C)) (spZ (cb_regs C)) (s0Z (cb_regs C)) (cb_ch C).
Proof.
intros CTX0 C HP.
destruct HP as (((HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT) & HROD & HSHI & HRAC) & _).
destruct Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
repeat split; try assumption; lia.
Qed.

(* ---- the rest of crs_pre_B's conjuncts a segment of X3 reads, by name ---- *)
Lemma x3_pre_more : forall CTX0 C, crs_pre_B B ARx CTX0 C ->
  prh_univ_closure B CTX0 /\
  LEDGER (cb_ly C) (cb_S C) (cb_Hp C) (cb_W C) (cb_mem C) (cb_Lam C) (cb_peak C) (cb_cnt C) SIZE_MAXZ (cb_ran C) (cb_most C) 0 /\
  cb_cnt C < 2 ^ 62 - 2 ^ 30 /\ cb_ran C = 0 /\ 0 <= cb_took C /\
  (cb_doc C = 0 \/
   (ck_read (cb_tb C) = Some (cb_t C) /\
    ck_tree_ok (cb_ly C) (cb_S C) (cb_Lam C) (cb_W C) (cb_mem C) (cb_doc C) (cb_t C) (cb_D C) /\
    PjWriteHyp.wlen (cb_t C) false + 1 < 2 ^ 24 /\ PjWriteHyp.wlen (cb_t C) true + 1 < 2 ^ 28 /\
    (PjTree.depth (cb_t C) <= 32)%nat)) /\
  blocks_bytes (cb_S C) + LIVE_check_reject_clean_starved (cb_tb C) (cb_t C) <= LIVE_MAX /\
  RQ_crcs (cb_tb C) + cf_head < cf_malloc_max /\
  Z.of_nat (length (frames (cb_S C))) <= ck_FRAMES_CAP - FR_check_reject_clean_starved.
Proof.
intros CTX0 C HP.
destruct HP as (_ & _ & Hcl & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Htk & Hdoc & HL0 & Hc0 & _ & Hr0 & _ & _ &
  Hlive & Hrq & Hfr & _).
split; [exact Hcl|]. split; [exact HL0|]. split; [exact Hc0|]. split; [exact Hr0|]. split; [lia|].
split; [exact Hdoc|]. split; [exact Hlive|]. split; [exact Hrq | exact Hfr].
Qed.

(* ---- the boundary facts at a state the runner reached without a write (same memory), at a world relation R ---- *)
Lemma x3_base_md : forall (R : world SEGS -> world SEGS -> Prop) CTX0 C fxk ly S Hp W regs mem md k sp2 regs' md',
  crs_baseR_B (fx := fx) B ARx R CTX0 C fxk ly S Hp W regs mem md k sp2 ->
  crs_JR_B B ARx R C ly S Hp W mem md' k ->
  getr regs' 3 = getr regs 3 -> getr regs' 4 = getr regs 4 ->
  crs_baseR_B (fx := fx) B ARx R CTX0 C fxk ly S Hp W regs' mem md' k sp2.
Proof.
intros R CTX0 C fxk ly S Hp W regs mem md k sp2 regs' md' HB HJ R3 R4.
destruct HB as (Hpre & HFZ & HFK & _ & HFR & HSV & HSL & HROD & HMN & HR3 & HR4 & Hs1 & Hs2 & Hs3 & HDPk).
exact (conj Hpre (conj HFZ (conj HFK (conj HJ (conj HFR (conj HSV (conj HSL (conj HROD (conj HMN
  (conj (eq_trans R3 HR3) (conj (eq_trans R4 HR4) (conj Hs1 (conj Hs2 (conj Hs3 HDPk)))))))))))))).
Qed.

(* ---- the boundary facts across a callee: its journal at the realigned sp (no footprint, no own frame), the
   composed journal from entry, the kept registers and the memnorm keep of the callee's m-form post, at a world
   relation R ---- *)
Lemma x3_base_keep : forall (R : world SEGS -> world SEGS -> Prop) CTX0 C fxk ly3 S3 Hp3 W3 regs3 mem3 md3 k sp2 STK1
  ly2 S2 Hp2 W2 regs2 mem2 md2 k1,
  crs_baseR_B (fx := fx) B ARx R CTX0 C fxk ly3 S3 Hp3 W3 regs3 mem3 md3 k sp2 ->
  AJR R STK1 sp2 [] ly3 S3 Hp3 W3 mem3 md3 [] ly2 S2 Hp2 W2 mem2 md2 k1 ->
  crs_JR_B B ARx R C ly2 S2 Hp2 W2 mem2 md2 (k + k1) ->
  aregs_preserved regs3 regs2 ->
  (YAkMemnorm.memnorm SEGS mem3 -> YAkMemnorm.memnorm SEGS mem2) ->
  crs_baseR_B (fx := fx) B ARx R CTX0 C fxk ly2 S2 Hp2 W2 regs2 mem2 md2 (k + k1) sp2.
Proof.
intros R CTX0 C fxk ly3 S3 Hp3 W3 regs3 mem3 md3 k sp2 STK1 ly2 S2 Hp2 W2 regs2 mem2 md2 k1 HB HJ1 HJ2 HP HMNk.
pose proof HB as (Hpre & HFZ & HFK & HJ3 & HFR & HSV & HSL & HROD & HMN & HR3 & HR4 & Hs1 & Hs2 & Hs3 & HDPk).
pose proof (x3_pre_stack CTX0 C Hpre) as (Hal0 & Hceil0 & Hhi0 & H47 & Htop0 & _ & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof x3_stk as (ESTK & _).
pose proof crs_frame_is_pi_B as EFR. unfold CRS_FRAME_B in EFR, Hs1.
destruct (crs_cF_keepR_B (fx := fx) B ARx LAWS R CTX0 C ly3 S3 Hp3 W3 mem3 md3 k Hpre HJ3) as (EF3 & EL3).
destruct (crs_cF_keepR_B (fx := fx) B ARx LAWS R CTX0 C ly2 S2 Hp2 W2 mem2 md2 (k + k1) Hpre HJ2) as (EF2 & EL2).
pose proof HJ1 as (HAR2 & HLE1 & _ & _ & _ & HFR2 & _ & _ & K1st & K1blk & K1img & K1frm & _ & _ & _ & _ & _).
destruct HFR as (Hfr3 & Hflw3 & Hfp3).
assert (Hin3 : In (CRS_CID_B, cb_fpos C) (frames S3)) by (rewrite Hfr3; left; reflexivity).
assert (Hin2 : In (CRS_CID_B, cb_fpos C) (frames S2)) by (rewrite HFR2; exact Hin3).
pose proof (alx_frames _ _ _ LAWS _ _ _ _ _ _ _ _ (proj1 HJ3) Hin3) as (F32 & Fapp & _ & _).
rewrite EF3 in F32, Fapp.
assert (EB : fs_frame_bytes CRS_CID_B = 128) by (vm_compute; reflexivity).
(* the frame's bytes and its shadow bytes are kept by the callee's frame clause *)
assert (KF : forall a, cF_B C <= a < cF_B C + 128 -> aview SEGS (w_H W2) mem2 a = aview SEGS (w_H W3) mem3 a).
{ intros a Ha. apply (K1frm CRS_CID_B (cb_fpos C) a Hin3); [left; unfold in_zr, frame_rng; cbn [fst snd]; rewrite EF3, EB; lia|].
  apply inFP_nil. }
assert (KS : forall a, shadow_addr (cF_B C) <= a < shadow_addr (cF_B C) + 16 ->
  aview SEGS (w_H W2) mem2 a = aview SEGS (w_H W3) mem3 a).
{ intros a Ha. apply (K1frm CRS_CID_B (cb_fpos C) a Hin3); [right; unfold in_zr; cbn [fst snd]; rewrite EF3, EB; change (128 / 8) with 16; lia|].
  apply inFP_nil. }
unfold crs_baseR_B. split; [exact Hpre|]. split; [exact HFZ|]. split; [exact HFK|]. split; [exact HJ2|].
split.
{ (* crs_frame_B *)
  split; [rewrite HFR2; exact Hfr3|]. split.
  - rewrite EL2, <- EL3, <- Hflw3. apply x3_rdword_keep. intros j Hj. apply KF. rewrite EB. lia.
  - intros a Ha. pose proof (alx_frames _ _ _ LAWS _ _ _ _ _ _ _ _ HAR2 Hin2) as (_ & _ & Ffr & _).
    rewrite EF2 in Ffr. exact (proj1 (Ffr a Ha)). }
split.
{ (* crs_saved_B: the real stack above the callee's window *)
  unfold crs_saved_B in *. rewrite Forall_forall in HSV |- *. intros p Hp. rewrite <- (HSV p Hp).
  assert (Hoff : 24 <= fst p <= 120).
  { cbv [CRS_SAVED_B In] in Hp. repeat (destruct Hp as [<- | Hp]; [cbn [fst]; lia|]). destruct Hp. }
  apply x3_rdword_keep. intros j Hj. apply K1st; lia. }
split.
{ (* crs_slot_B: the struct's shadow lies in the frame's shadow *)
  destruct HSL as (HRA & HHV). unfold cOut_B, CRS_OFF_DOC_B in *. split.
  - apply (range_addressable_agree (aview SEGS (w_H W3) mem3) (aview SEGS (w_H W2) mem2) SHADOW_OFF (cF_B C + 32) 56); [|exact HRA].
    intros x Hx. apply KS. unfold shadow_of_addr, shadow_addr. split.
    + apply Z.add_le_mono_l. apply Z.div_le_mono; lia.
    + assert (x / 8 < cF_B C / 8 + 16) by (apply Z.div_lt_upper_bound; lia). lia.
  - intros s Hs. rewrite (KS s); [exact (HHV s Hs)|].
    exact (x3_hull_frame (cF_B C) s F32 Hs). }
split.
{ (* the read-only view: image bytes outside alloc.c's statics, kept by the image clause *)
  intros a Hro Hno Herr. rewrite (K1img a); [exact (HROD a Hro Hno Herr) | | exact Hno | exact Herr | |].
  - destruct Hro as [(sg & Hsg & _ & Hr) | Hr]; [exists sg; split; [exact Hsg | exact Hr] | exact (@pa_relro_img _ _ PA a Hr)].
  - intros Hps. exact (S1ImgB.pst_not_ro_B a Hps Hro).
  - apply fp_spares_closed. exact sink_closed_nil. }
split; [exact (HMNk HMN)|].
split; [rewrite (x3_ap regs3 regs2 3%bv HP) by x3_cs; exact HR3|].
split; [rewrite (x3_ap regs3 regs2 4%bv HP) by x3_cs; exact HR4|].
split; [exact Hs1|]. split; [exact Hs2 | split; [exact Hs3 | exact HDPk]].
Qed.

(* ---- the call chain at a call of this function: s0 = the entry sp, the saved ra and s0 below it (crs_saved_B), the
   entry's chain above (the journal keeps the real stack above the entry sp) ---- *)
Lemma x3_chain : forall (R : world SEGS -> world SEGS -> Prop) CTX0 C ly S Hp W mem md k sp2,
  crs_pre_B (fx := fx) B ARx CTX0 C -> crs_JR_B B ARx R C ly S Hp W mem md k -> crs_saved_B C W mem ->
  sp2 + 16 <= spZ (cb_regs C) ->
  exists ch1, achain ly (aview SEGS (w_H W) mem) sp2 (spZ (cb_regs C)) ch1.
Proof.
intros R CTX0 C ly S Hp W mem md k sp2 Hpre HJ HSV Hsp.
pose proof (x3_pre_stack CTX0 C Hpre) as (Hal0 & Hceil0 & Hhi0 & H47 & Htop0 & Hra4 & Hch).
pose proof x3_stk as (ESTK & _).
pose proof HJ as (_ & HLE & _ & _ & _ & _ & _ & _ & Kst & _).
pose proof HLE as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & _ & Ehi & _).
destruct (Z_lt_le_dec (spZ (cb_regs C)) (ly_top ly - 16)) as [Hlt | Hge].
- exists ((spZ (cb_regs C), raZ (cb_regs C), s0Z (cb_regs C)) :: cb_ch C).
  unfold crs_saved_B in HSV. rewrite Forall_forall in HSV.
  pose proof (HSV (120, 1%bv) ltac:(cbv [CRS_SAVED_B In]; left; reflexivity)) as V1. cbn [fst snd] in V1.
  pose proof (HSV (112, 8%bv) ltac:(cbv [CRS_SAVED_B In]; right; left; reflexivity)) as V8. cbn [fst snd] in V8.
  apply (achain_push ly (aview SEGS (w_H (cb_W C)) (cb_mem C)) (aview SEGS (w_H W) mem) (spZ (cb_regs C))
    (s0Z (cb_regs C)) (raZ (cb_regs C)) (cb_ch C) sp2).
  + apply (achain_ly_top (cb_ly C) ly); [exact Etop | exact Hch].
  + rewrite Etop. lia.
  + intros a Ha. apply Kst; lia.
  + replace (spZ (cb_regs C) - 8) with (spZ (cb_regs C) - 128 + 120) by lia. exact V1.
  + replace (spZ (cb_regs C) - 16) with (spZ (cb_regs C) - 128 + 112) by lia. exact V8.
  + exact Hra4.
  + lia.
  + rewrite <- (Z.mod_mod (spZ (cb_regs C)) 16) in Hal0 by lia. Z.div_mod_to_equations. lia.
  + exact Hlt.
  + exact Hsp.
- exists []. left. split; [right; left; exact Hge | reflexivity].
Qed.

(* ---- A CALL OF THIS FUNCTION from the realigned sp (no footprint, no frame of the callee's own): the state at the
   callee's entry the run reached, the boundary facts there, the kept registers, the return site; the callee's text at
   the fpre the call builds (m-form post); the continuation gets the boundary facts at the return, the callee's journal,
   the kept registers and the callee's Q (Crt102Rewrite.v crt102rw_call, cold/h-hpreset-7-crt102-rw 370f759b1808, the
   model, over YCbqGcall.aj_call_x_sp) ---- *)
Lemma x3_call : forall (R : world SEGS -> world SEGS -> Prop) (Rr : forall W, R W W)
    (Rt : forall W1 W2 W3, R W1 W2 -> R W2 W3 -> R W1 W3) (Rw : forall W W', @wle SEGS W W' -> R W W')
    CTX0 C fxk STK1 (off : Z) W E ss ms mdc ly S Hp k sp2
    (Q : alayout -> astate -> list Z -> world SEGS -> bvmap 5 word -> (word -> option byte) -> Model -> Prop)
    (G : world SEGS -> config -> Prop),
  @st_ok SEGS fxk E ss (restrict (w_H W) ms) -> ss_resv ss = None ->
  crs_baseR_B (fx := fx) B ARx R CTX0 C fxk ly S Hp W (ms_regs ms) (ms_mem ms) mdc k sp2 ->
  getr (ms_regs ms) 2 = w64 sp2 -> getr (ms_regs ms) 8 = w64 (spZ (cb_regs C)) ->
  getr (ms_regs ms) 1 = Z_to_bv 64 (BASE + (CRS_PC0_B + off)) -> 0 <= off < 2048 -> off mod 2 = 0 ->
  0 <= STK1 -> STK1 + CRS_FRAME_B <= STK ->
  (forall ch1, fpre B ARx STK1 ly S Hp W (ms_regs ms) (ms_mem ms) mdc ch1 ->
     SRr SEGS W (mkCfg (@YK11.mkst fxk (ms_regs ms) (Z_to_bv 64 (ss_pc ss)) (ms_mem ms) (YK11.seg_rom SEGS)) mdc)
       (fpostm (fx := fxk) B ARx SK STK1 [] (ms_regs ms) ly S Hp W (ms_mem ms) mdc Q)) ->
  (forall ly2 S2 Hp2 W2 regs2 mem2 md2 k1,
     crs_baseR_B (fx := fx) B ARx R CTX0 C fxk ly2 S2 Hp2 W2 regs2 mem2 md2 (k + k1) sp2 ->
     AJR R STK1 sp2 [] ly S Hp W (ms_mem ms) mdc [] ly2 S2 Hp2 W2 mem2 md2 k1 ->
     aregs_preserved (ms_regs ms) regs2 -> Q ly2 S2 Hp2 W2 regs2 mem2 md2 ->
     SRrG SEGS R W2 (mkCfg (@YK11.mkst fxk regs2 (Z_to_bv 64 (BASE + (CRS_PC0_B + off))) mem2 (YK11.seg_rom SEGS)) md2)
       G) ->
  SRrG SEGS R W (mkCfg ms mdc) G.
Proof.
intros R Rr Rt Rw CTX0 C fxk STK1 off W E ss ms mdc ly S Hp k sp2 Q G HS Hrv HB R2 R8 Hra Hoff Hoff2 HSTK0 HSTK1
  Hcallee HK.
pose proof HB as (Hpre & HFZ & HFK & HJ & HFR & HSV & HSL & HROD & HMN & HR3 & HR4 & Hs1 & Hs2 & Hs3 & HDPk).
pose proof (x3_pre_stack CTX0 C Hpre) as (Hal0 & Hceil0 & Hhi0 & H47 & Htop0 & Hra4 & Hch).
pose proof Hpre as (((_ & _ & _ & Hgp & Htp & _) & _) & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof x3_stk as (ESTK & _).
pose proof x3_base as (Hb0 & Hb1 & Hb2 & Hb3).
pose proof crs_frame_is_pi_B as EFR. unfold CRS_FRAME_B in EFR, Hs1, HSTK1.
pose proof HJ as (_ & HLE & _).
pose proof HLE as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & _ & Ehi & _).
destruct (x3_chain R CTX0 C ly S Hp W (ms_mem ms) mdc k sp2 Hpre HJ HSV ltac:(lia)) as (ch1 & Hch1).
set (sp0 := spZ (cb_regs C)) in *.
assert (Hspz : spZ (ms_regs ms) = sp0 + (sp2 - sp0)).
{ unfold spZ at 1. rewrite R2. unfold w64. rewrite unsigned_lit_small by lia. lia. }
assert (Hs0z : s0Z (ms_regs ms) = sp0).
{ unfold s0Z. rewrite R8. unfold w64. apply unsigned_lit_small. lia. }
assert (Hraz : raZ (ms_regs ms) = BASE + (CRS_PC0_B + off)) by (unfold raZ; rewrite Hra; apply unsigned_lit_small; lia).
eapply (SRrG_bind SEGS R Rt).
{ refine (@aj_call_x_spR fxk rc SK SEGS B PST ARx cf_head LAWS (@pa_segs_low _ _ PA) R Rr Rt W E ss ms STK sp0 []
    (cb_ly C) (YG00.set_depot (cb_dp C) (cb_S C)) (cb_Hp C) (cb_W C) (cb_mem C) (cb_md C) [(CRS_CID_B, cb_fpos C)] ly S Hp mdc k STK1 [] (sp2 - sp0)
    (getr (ms_regs ms) 1) ch1 (fQmn (ms_mem ms) Q) HS Hrv HJ Hspz _ _ HSTK0 _ _ _ eq_refl _ _ _ _ _).
  - apply Z.mod_divide; [lia|]. apply Z.mod_divide in Hal0; [|lia]. destruct Hal0 as [q Hq].
    apply Z.mod_divide in Hs3; [|lia]. destruct Hs3 as [q' Hq']. exists (2 * q' - q). lia.
  - lia.
  - lia.
  - rewrite HR3. exact Hgp.
  - rewrite HR4. exact Htp.
  - rewrite Hra. apply (ret_ok_codeptr_v (PI := PA)); [lia | rewrite Z.add_mod by lia; replace (CRS_PC0_B mod 2) with 0 by (vm_compute; reflexivity); rewrite Hoff2; reflexivity].
  - rewrite Hra, unsigned_lit_small by lia. lia.
  - replace (sp0 + (sp2 - sp0)) with sp2 by lia. rewrite Hs0z. exact Hch1.
  - intros HPRE1.
    refine (SRrG_mono SEGS R _ _ _ _ (SRr_SRrG SEGS R Rw _ _ _ (Hcallee ch1 _)) _).
    + split; [exact HPRE1|]. split; [exact HROD|].
      split; [rewrite Hspz, Ehi; lia|]. split; [rewrite Hraz; lia | exact HFZ].
    + intros W' c' _ HPm. exact (apost_base_x_R_lift (SK := SK) SEGS B PST ARx R Rw _ _ _ _ _ _ _ _ _ _ _ _ HPm).
  - intros a Ha. exfalso. exact (inFP_nil a Ha). }
cbv beta. intros W2 c2 _ (ly2 & S2 & Hp2 & regs2 & mem2 & md2 & k1 & -> & HJ2 & HJ1 & HP & HQ & HMN2).
replace (sp0 + (sp2 - sp0)) with sp2 in HJ1 by lia.
rewrite Hra.
apply (HK ly2 S2 Hp2 W2 regs2 mem2 md2 k1); [| exact HJ1 | exact HP | exact HQ].
exact (x3_base_keep R CTX0 C fxk ly S Hp W (ms_regs ms) (ms_mem ms) mdc k sp2 STK1 ly2 S2 Hp2 W2 regs2 mem2 md2 k1
  HB HJ1 HJ2 HP HMN2).
Qed.

(* the boundary facts at another float state with the rounding mode 0 and fs0-fs11 kept from the entry's *)
Lemma x3_base_fx : forall (R : world SEGS -> world SEGS -> Prop) CTX0 C fxk fxk' ly S Hp W regs mem md k sp2,
  crs_baseR_B (fx := fx) B ARx R CTX0 C fxk ly S Hp W regs mem md k sp2 ->
  frm_zero (@YK11.fp_csr fxk') -> fregs_kept_x fx fxk' ->
  crs_baseR_B (fx := fx) B ARx R CTX0 C fxk' ly S Hp W regs mem md k sp2.
Proof.
intros R CTX0 C fxk fxk' ly S Hp W regs mem md k sp2 HB HZ HK'.
destruct HB as (Hpre & _ & _ & HR). exact (conj Hpre (conj HZ (conj HK' HR))).
Qed.
Lemma x3_fregs_trans : forall f1 f2 f3 : YK11.FPState, fregs_kept_x f1 f2 -> fregs_kept_x f2 f3 -> fregs_kept_x f1 f3.
Proof. intros f1 f2 f3 H1 H2 r Hr. rewrite (H2 r Hr). exact (H1 r Hr). Qed.

(* ---- x3_call for a callee whose text concludes in the float form fpostFm (it may change the float state: pj_write's
   text, PRH_FnWriter.v at the kit decff67d721f): over YCbqGcall.aj_call_xF_sp; the continuation runs at the callee's float
   state fx' (rounding mode 0, fs0-fs11 kept, so crs_base_B holds at fx') ---- *)
Lemma x3_callF : forall (R : world SEGS -> world SEGS -> Prop) (Rr : forall W, R W W)
    (Rt : forall W1 W2 W3, R W1 W2 -> R W2 W3 -> R W1 W3) CTX0 C fxk STK1 (off : Z) W E ss ms mdc ly S Hp k sp2
    (Q : alayout -> astate -> list Z -> world SEGS -> bvmap 5 word -> (word -> option byte) -> Model -> Prop)
    (G : world SEGS -> config -> Prop),
  @st_ok SEGS fxk E ss (restrict (w_H W) ms) -> ss_resv ss = None ->
  crs_baseR_B (fx := fx) B ARx R CTX0 C fxk ly S Hp W (ms_regs ms) (ms_mem ms) mdc k sp2 ->
  getr (ms_regs ms) 2 = w64 sp2 -> getr (ms_regs ms) 8 = w64 (spZ (cb_regs C)) ->
  getr (ms_regs ms) 1 = Z_to_bv 64 (BASE + (CRS_PC0_B + off)) -> 0 <= off < 2048 -> off mod 2 = 0 ->
  0 <= STK1 -> STK1 + CRS_FRAME_B <= STK ->
  (forall ch1, fpre B ARx STK1 ly S Hp W (ms_regs ms) (ms_mem ms) mdc ch1 ->
     SRrG SEGS R W (mkCfg (@YK11.mkst fxk (ms_regs ms) (Z_to_bv 64 (ss_pc ss)) (ms_mem ms) (YK11.seg_rom SEGS)) mdc)
       (apost_base_xFR (fx := fxk) (SK := SK) SEGS B PST ARx R STK1 [] (ms_regs ms) ly S Hp W (ms_mem ms) mdc
          (fQmn (ms_mem ms) Q))) ->
  (forall (fx' : YK11.FPState) ly2 S2 Hp2 W2 regs2 mem2 md2 k1,
     crs_baseR_B (fx := fx) B ARx R CTX0 C fx' ly2 S2 Hp2 W2 regs2 mem2 md2 (k + k1) sp2 ->
     AJR R STK1 sp2 [] ly S Hp W (ms_mem ms) mdc [] ly2 S2 Hp2 W2 mem2 md2 k1 ->
     aregs_preserved (ms_regs ms) regs2 -> Q ly2 S2 Hp2 W2 regs2 mem2 md2 ->
     SRrG SEGS R W2 (mkCfg (@YK11.mkst fx' regs2 (Z_to_bv 64 (BASE + (CRS_PC0_B + off))) mem2 (YK11.seg_rom SEGS)) md2)
       G) ->
  SRrG SEGS R W (mkCfg ms mdc) G.
Proof.
intros R Rr Rt CTX0 C fxk STK1 off W E ss ms mdc ly S Hp k sp2 Q G HS Hrv HB R2 R8 Hra Hoff Hoff2 HSTK0 HSTK1
  Hcallee HK.
pose proof HB as (Hpre & HFZ & HFK & HJ & HFR & HSV & HSL & HROD & HMN & HR3 & HR4 & Hs1 & Hs2 & Hs3 & HDPk).
pose proof (x3_pre_stack CTX0 C Hpre) as (Hal0 & Hceil0 & Hhi0 & H47 & Htop0 & Hra4 & Hch).
pose proof Hpre as (((_ & _ & _ & Hgp & Htp & _) & _) & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof x3_stk as (ESTK & _).
pose proof x3_base as (Hb0 & Hb1 & Hb2 & Hb3).
pose proof crs_frame_is_pi_B as EFR. unfold CRS_FRAME_B in EFR, Hs1, HSTK1.
pose proof HJ as (_ & HLE & _).
pose proof HLE as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & _ & Ehi & _).
destruct (x3_chain R CTX0 C ly S Hp W (ms_mem ms) mdc k sp2 Hpre HJ HSV ltac:(lia)) as (ch1 & Hch1).
set (sp0 := spZ (cb_regs C)) in *.
assert (Hspz : spZ (ms_regs ms) = sp0 + (sp2 - sp0)).
{ unfold spZ at 1. rewrite R2. unfold w64. rewrite unsigned_lit_small by lia. lia. }
assert (Hs0z : s0Z (ms_regs ms) = sp0).
{ unfold s0Z. rewrite R8. unfold w64. apply unsigned_lit_small. lia. }
assert (Hraz : raZ (ms_regs ms) = BASE + (CRS_PC0_B + off)) by (unfold raZ; rewrite Hra; apply unsigned_lit_small; lia).
eapply (SRrG_bind SEGS R Rt).
{ refine (@aj_call_xF_spR fxk rc SK SEGS B PST ARx cf_head LAWS (@pa_segs_low _ _ PA) R Rr Rt W E ss ms STK sp0 []
    (cb_ly C) (YG00.set_depot (cb_dp C) (cb_S C)) (cb_Hp C) (cb_W C) (cb_mem C) (cb_md C) [(CRS_CID_B, cb_fpos C)] ly S Hp mdc k STK1 [] (sp2 - sp0)
    (getr (ms_regs ms) 1) ch1 (fQmn (ms_mem ms) Q) HS Hrv HJ Hspz _ _ HSTK0 _ _ _ eq_refl _ _ _ _ _).
  - apply Z.mod_divide; [lia|]. apply Z.mod_divide in Hal0; [|lia]. destruct Hal0 as [q Hq].
    apply Z.mod_divide in Hs3; [|lia]. destruct Hs3 as [q' Hq']. exists (2 * q' - q). lia.
  - lia.
  - lia.
  - rewrite HR3. exact Hgp.
  - rewrite HR4. exact Htp.
  - rewrite Hra. apply (ret_ok_codeptr_v (PI := PA)); [lia | rewrite Z.add_mod by lia; replace (CRS_PC0_B mod 2) with 0 by (vm_compute; reflexivity); rewrite Hoff2; reflexivity].
  - rewrite Hra, unsigned_lit_small by lia. lia.
  - replace (sp0 + (sp2 - sp0)) with sp2 by lia. rewrite Hs0z. exact Hch1.
  - intros HPRE1. apply (Hcallee ch1). split; [exact HPRE1|]. split; [exact HROD|].
    split; [rewrite Hspz, Ehi; lia|]. split; [rewrite Hraz; lia | exact HFZ].
  - intros a Ha. exfalso. exact (inFP_nil a Ha). }
cbv beta. intros W2 c2 _ (fx' & ly2 & S2 & Hp2 & regs2 & mem2 & md2 & k1 & -> & HZ' & HK' & HJ2 & HJ1 & HP & HQ & HMN2).
replace (sp0 + (sp2 - sp0)) with sp2 in HJ1 by lia.
rewrite Hra.
apply (HK fx' ly2 S2 Hp2 W2 regs2 mem2 md2 k1); [| exact HJ1 | exact HP | exact HQ].
apply (x3_base_fx R CTX0 C fxk fx'); [| exact HZ' | exact (x3_fregs_trans _ _ _ HFK HK')].
exact (x3_base_keep R CTX0 C fxk ly S Hp W (ms_regs ms) (ms_mem ms) mdc k sp2 STK1 ly2 S2 Hp2 W2 regs2 mem2 md2 k1
  HB HJ1 HJ2 HP HMN2).
Qed.

(* ---- the state facts a segment of X3 carries between its stretches (the ledger at any g_fail_at, the counters'
   lower bounds, the room, the run position, Lam and the blocks back as at entry, the input's bytes, the tree) ---- *)
Definition x3_st (C : crsC_B) (evs : list PresetReqAt.hev) (ly : alayout) (S : astate) (Hp : list Z) (W : world SEGS)
  (mem : word -> option byte) (Lam : list (Z * Z)) (peak cnt fail ran : Z) : Prop :=
  LEDGER ly S Hp W mem Lam peak cnt fail ran (cb_most C) 0 /\ cb_peak C <= peak /\ ran = 0 /\ cb_cnt C <= cnt /\
  room_live_cf S /\ crs_pos_B C evs ran S /\ crs_perm_B B C ly S Lam /\
  PRH_Base.bytes_at W mem (cb_data C) (cb_tb C) /\ crs_tree_B C ly S Lam W mem.

Section k.
Variable HK : CrsKeep_B B ARx.

(* the input's bytes across a callee's journal with no footprint, whose blocks survive *)
Lemma x3_bytes_keep : forall (R : world SEGS -> world SEGS -> Prop) CTX0 C ly S Hp W mem md Lam peak cnt fail ran most
  own STK1 sp1 ly2 S2 Hp2 W2 mem2 md2 k1,
  crs_pre_B (fx := fx) B ARx CTX0 C -> ARx ly S Hp W mem md -> LEDGER ly S Hp W mem Lam peak cnt fail ran most own ->
  crs_perm_B B C ly S Lam ->
  AJR R STK1 sp1 [] ly S Hp W mem md [] ly2 S2 Hp2 W2 mem2 md2 k1 ->
  (forall x, In x (ablocks B ly S) -> In x (ablocks B ly2 S2)) ->
  PRH_Base.bytes_at W mem (cb_data C) (cb_tb C) -> PRH_Base.bytes_at W2 mem2 (cb_data C) (cb_tb C).
Proof.
intros R CTX0 C ly S Hp W mem md Lam peak cnt fail ran most own STK1 sp1 ly2 S2 Hp2 W2 mem2 md2 k1 Hpre HAR HL (HPL & HPA) HJ1
  Hbl HBY.
pose proof HJ1 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & K1blk & K1img & _).
pose proof cf_head_nonneg as Ch.
assert (HL0 : LEDGER (cb_ly C) (cb_S C) (cb_Hp C) (cb_W C) (cb_mem C) (cb_Lam C) (cb_peak C) (cb_cnt C) SIZE_MAXZ (cb_ran C) (cb_most C) 0)
  by (destruct Hpre as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HL0 & _); exact HL0).
assert (Hh0 : PRH_FnReader.prhReader_home B (cb_ly C) (cb_S C) (cb_Hp C) (cb_Lam C) (cb_data C) (cSize_B C))
  by (destruct Hpre as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hh0 & _); exact Hh0).
pose proof (kpb_home_move B ARx HK _ _ _ _ _ _ _ _ _ _ _ _ ly S Hp W mem Lam peak cnt fail ran most own _ _ HL0 HL HPL HPA Hh0) as Hh.
unfold PRH_Base.bytes_at in *. apply (x3_garr_av (w_H W) (w_H W2) mem mem2); [|exact HBY].
intros j Hj. unfold cSize_B in Hh. set (x := cb_data C + Z.of_nat j).
assert (Hx : cb_data C <= x < cb_data C + Z.of_nat (length (cb_tb C))) by (unfold x; lia).
destruct Hh as [[(b & m & Hin & Hb & Hm) | [(_ & _ & _ & Hro) | (_ & _ & Hro)]] | (b & m & Hin & _ & Hb & Hm)].
- pose proof (prh_ledger_blocks B ly S Hp W mem Lam peak cnt fail ran _ _ HL) as HF. rewrite Forall_forall in HF.
  destruct (HF (b, m) Hin) as (Hk0 & Hab & _). cbn [fst snd] in Hk0, Hab.
  replace x with (b - cf_head + (x - (b - cf_head))) by lia.
  apply (K1blk (b - cf_head) (m + cf_head)); [exact Hab | exact (Hbl _ Hab) | unfold req_size; destruct (Z.eqb_spec (m + cf_head) 0); lia |].
  apply inFP_nil.
- destruct (Hro x Hx) as (Hr & Hno & Her).
  apply K1img; [| exact Hno | exact Her | | apply fp_spares_closed; exact sink_closed_nil].
  + destruct Hr as [(sg & Hsg & _ & Hr) | Hr]; [exists sg; split; [exact Hsg | exact Hr] | exact (@pa_relro_img _ _ PA x Hr)].
  + intros Hps. exact (S1ImgB.pst_not_ro_B x Hps Hr).
- destruct (Hro x Hx) as (Hr & Hno & Her & _).
  apply K1img; [| exact Hno | exact Her | | apply fp_spares_closed; exact sink_closed_nil].
  + destruct Hr as [(sg & Hsg & _ & Hr) | Hr]; [exists sg; split; [exact Hsg | exact Hr] | exact (@pa_relro_img _ _ PA x Hr)].
  + intros Hps. exact (S1ImgB.pst_not_ro_B x Hps Hr).
- replace x with (b + (x - b)) by lia.
  apply (K1blk b m); [exact Hin | exact (Hbl _ Hin) | unfold req_size; destruct (Z.eqb_spec m 0); lia |].
  apply inFP_nil.
Qed.

(* the document's tree across a callee's journal with no footprint, whose blocks survive, at the same Lam *)
Lemma x3_tree_keep : forall (R : world SEGS -> world SEGS -> Prop) C ly S Hp W mem md Lam peak cnt fail ran most own
    STK1 sp1 ly2 S2 Hp2 W2 mem2 md2 k1 peak2 cnt2 fail2 ran2 most2 own2,
  ARx ly S Hp W mem md -> LEDGER ly S Hp W mem Lam peak cnt fail ran most own ->
  AJR R STK1 sp1 [] ly S Hp W mem md [] ly2 S2 Hp2 W2 mem2 md2 k1 ->
  LEDGER ly2 S2 Hp2 W2 mem2 Lam peak2 cnt2 fail2 ran2 most2 own2 ->
  (forall x, In x (ablocks B ly S) -> In x (ablocks B ly2 S2)) ->
  crs_tree_B C ly S Lam W mem -> crs_tree_B C ly2 S2 Lam W2 mem2.
Proof.
intros R C ly S Hp W mem md Lam peak cnt fail ran most own STK1 sp1 ly2 S2 Hp2 W2 mem2 md2 k1 peak2 cnt2 fail2 ran2 most2
  own2 HAR HL HJ1 HL2 Hbl HT Hdoc.
destruct (HT Hdoc) as (HN & HD & _ & HO).
pose proof HJ1 as (HAR2 & HLE1 & _ & _ & _ & HFR2 & _ & _ & _ & K1blk & _ & K1frm & _).
pose proof cf_head_nonneg as Ch.
split; [|split; [exact HD|]; split].
- apply (pj_nodeR_frame SEGS (cb_t C) (mrestrict (w_H W) mem) (mrestrict (w_H W2) mem2) (prh_lin Lam) (cb_doc C) (cb_D C) HN).
  intros x [Hx | (bk & Hbk & Hx)].
  + destruct HO as (_ & (cid & pos & Hin & H1 & H2) & _).
    assert (Hin2 : In (cid, pos) (frames S2)) by (rewrite HFR2; exact Hin).
    assert (EF : frame_addr ly2 cid pos = frame_addr ly cid pos).
    { unfold frame_addr. destruct HLE1 as (_ & _ & _ & _ & _ & EF & _). rewrite EF. reflexivity. }
    split.
    * apply (mbyte_of_aview SEGS). apply (K1frm cid pos x Hin); [left; unfold in_zr, frame_rng; cbn [fst snd]; lia|].
      apply inFP_nil.
    * intros _. apply (apresent_writable SEGS).
      pose proof (alx_frames _ _ _ LAWS _ _ _ _ _ _ _ _ HAR2 Hin2) as (_ & _ & Ffr & _). rewrite EF in Ffr.
      exact (proj1 (Ffr x ltac:(lia))).
  + destruct bk as (a, k). unfold pj_holdsR in Hx. cbn [fst snd] in Hx.
    pose proof (prh_ledger_blocks B ly S Hp W mem Lam peak cnt fail ran _ _ HL) as HF. rewrite Forall_forall in HF.
    destruct (HF (a, k) (HD _ Hbk)) as (Hk0 & Hab & _). cbn [fst snd] in Hk0, Hab.
    assert (Hrq : req_size (k + cf_head) = k + cf_head) by (unfold req_size; destruct (Z.eqb_spec (k + cf_head) 0); lia).
    replace x with (a - cf_head + (x - (a - cf_head))) by lia.
    split.
    * apply (mbyte_of_aview SEGS). apply (K1blk (a - cf_head) (k + cf_head)); [exact Hab | exact (Hbl _ Hab) | lia |].
      apply inFP_nil.
    * intros _. apply (apresent_writable SEGS).
      destruct (alx_blocks _ _ _ LAWS _ _ _ _ _ _ _ _ HAR2 (Hbl _ Hab)) as (_ & _ & _ & _ & Hbb & _).
      assert (Hxr : a - cf_head <= a - cf_head + (x - (a - cf_head)) < a - cf_head + req_size (k + cf_head))
        by (rewrite Hrq; lia).
      exact (proj1 (Hbb _ Hxr)).
- exact (kpb_tree_vis B ARx HK ly2 S2 Hp2 W2 mem2 md2 Lam peak2 cnt2 fail2 ran2 most2 own2 (cb_D C) HAR2 HL2 HD).
- exact (crs_obj_keepR_B B ARx LAWS R STK1 sp1 ly S Hp W mem md [] ly2 S2 Hp2 W2 mem2 md2 k1 (cb_doc C) HAR HJ1 HO).
Qed.

(* x3_st across an accessor of alloc.c (fuzz_alloc_fail / _ran_out / _live / _count): S, Hp and the blocks kept *)
Lemma x3_st_acc : forall (R : world SEGS -> world SEGS -> Prop) CTX0 C evs ly S Hp W mem md Lam peak cnt fail ran STK1
  sp1 ly2 S2 Hp2 W2 mem2 md2 k1 fail2,
  crs_pre_B (fx := fx) B ARx CTX0 C -> ARx ly S Hp W mem md ->
  x3_st C evs ly S Hp W mem Lam peak cnt fail ran ->
  AJR R STK1 sp1 [] ly S Hp W mem md [] ly2 S2 Hp2 W2 mem2 md2 k1 ->
  Hp2 = Hp -> S2 = S -> ablocks B ly2 S2 = ablocks B ly S ->
  LEDGER ly2 S2 Hp2 W2 mem2 Lam peak cnt fail2 ran (cb_most C) 0 ->
  x3_st C evs ly2 S2 Hp2 W2 mem2 Lam peak cnt fail2 ran.
Proof.
intros R CTX0 C evs ly S Hp W mem md Lam peak cnt fail ran STK1 sp1 ly2 S2 Hp2 W2 mem2 md2 k1 fail2 Hpre HAR
  (HL & Hpk & Hran & Hcn & HRL & HPOS & HPM & HBY & HT) HJ1 EHp ES EAB HL2.
assert (Hbl : forall x, In x (ablocks B ly S) -> In x (ablocks B ly2 S2)) by (intros x Hx; rewrite EAB; exact Hx).
split; [exact HL2|]. split; [exact Hpk|]. split; [exact Hran|]. split; [exact Hcn|].
split; [rewrite ES; exact HRL|]. split; [rewrite ES; exact HPOS|].
split; [destruct HPM as (HP1 & HP2); split; [exact HP1 | rewrite EAB; exact HP2]|].
split; [exact (x3_bytes_keep R CTX0 C ly S Hp W mem md Lam peak cnt fail ran _ _ STK1 sp1 ly2 S2 Hp2 W2 mem2 md2 k1
  Hpre HAR HL HPM HJ1 Hbl HBY)|].
exact (x3_tree_keep R C ly S Hp W mem md Lam peak cnt fail ran _ _ STK1 sp1 ly2 S2 Hp2 W2 mem2 md2 k1 peak cnt fail2 ran
  _ _ HAR HL HJ1 HL2 Hbl HT).
Qed.
(* ---- a call of one of alloc.c's accessors from X3: x3_call, then x3_st across it (S, Hp, the blocks kept) ---- *)
Lemma x3_acc_call : forall (R : world SEGS -> world SEGS -> Prop) (Rr : forall W, R W W)
    (Rt : forall W1 W2 W3, R W1 W2 -> R W2 W3 -> R W1 W3) (Rw : forall W W', @wle SEGS W W' -> R W W')
    CTX0 C evs fxk STK1 (off : Z) W E ss ms mdc ly S Hp k sp2 Lam peak cnt fail ran fail2
    (Qa : alayout -> astate -> list Z -> world SEGS -> bvmap 5 word -> (word -> option byte) -> Model -> Prop)
    (G : world SEGS -> config -> Prop),
  @st_ok SEGS fxk E ss (restrict (w_H W) ms) -> ss_resv ss = None ->
  crs_baseR_B (fx := fx) B ARx R CTX0 C fxk ly S Hp W (ms_regs ms) (ms_mem ms) mdc k sp2 ->
  getr (ms_regs ms) 2 = w64 sp2 -> getr (ms_regs ms) 8 = w64 (spZ (cb_regs C)) ->
  getr (ms_regs ms) 1 = Z_to_bv 64 (BASE + (CRS_PC0_B + off)) -> 0 <= off < 2048 -> off mod 2 = 0 ->
  0 <= STK1 -> STK1 + CRS_FRAME_B <= STK ->
  x3_st C evs ly S Hp W (ms_mem ms) Lam peak cnt fail ran ->
  (forall ch1, fpre B ARx STK1 ly S Hp W (ms_regs ms) (ms_mem ms) mdc ch1 ->
     SRr SEGS W (mkCfg (@YK11.mkst fxk (ms_regs ms) (Z_to_bv 64 (ss_pc ss)) (ms_mem ms) (YK11.seg_rom SEGS)) mdc)
       (fpostm (fx := fxk) B ARx SK STK1 [] (ms_regs ms) ly S Hp W (ms_mem ms) mdc Qa)) ->
  (forall ly2 S2 Hp2 W2 regs2 mem2 md2, Qa ly2 S2 Hp2 W2 regs2 mem2 md2 ->
     Hp2 = Hp /\ S2 = S /\ ablocks B ly2 S2 = ablocks B ly S /\ LEDGER ly2 S2 Hp2 W2 mem2 Lam peak cnt fail2 ran (cb_most C) 0) ->
  (forall ly2 S2 Hp2 W2 regs2 mem2 md2 k1,
     crs_baseR_B (fx := fx) B ARx R CTX0 C fxk ly2 S2 Hp2 W2 regs2 mem2 md2 (k + k1) sp2 ->
     aregs_preserved (ms_regs ms) regs2 -> Qa ly2 S2 Hp2 W2 regs2 mem2 md2 ->
     x3_st C evs ly2 S2 Hp2 W2 mem2 Lam peak cnt fail2 ran ->
     SRrG SEGS R W2 (mkCfg (@YK11.mkst fxk regs2 (Z_to_bv 64 (BASE + (CRS_PC0_B + off))) mem2 (YK11.seg_rom SEGS)) md2)
       G) ->
  SRrG SEGS R W (mkCfg ms mdc) G.
Proof.
intros R Rr Rt Rw CTX0 C evs fxk STK1 off W E ss ms mdc ly S Hp k sp2 Lam peak cnt fail ran fail2 Qa G HS Hrv HB R2 R8
  R1 Ho1 Ho2 HS0 HS1 HST Hcallee HQa HK2.
apply (x3_call R Rr Rt Rw CTX0 C fxk STK1 off W E ss ms mdc ly S Hp k sp2 Qa G HS Hrv HB R2 R8 R1 Ho1 Ho2 HS0 HS1
  Hcallee).
intros ly2 S2 Hp2 W2 regs2 mem2 md2 k1 HB2 HJ1 HP HQ.
destruct (HQa _ _ _ _ _ _ _ HQ) as (EHp & ES & EAB & HL2).
pose proof HB as (Hpre & _ & _ & HJ & _).
apply (HK2 ly2 S2 Hp2 W2 regs2 mem2 md2 k1 HB2 HP HQ).
exact (x3_st_acc R CTX0 C evs ly S Hp W (ms_mem ms) mdc Lam peak cnt fail ran STK1 sp2 ly2 S2 Hp2 W2 mem2 md2 k1 fail2
  Hpre (proj1 HJ) HST HJ1 EHp ES EAB HL2).
Qed.

End k.

(* the registers every point of X3 holds: the kit's base and shadow registers, s3 = doc, s6 = live at entry, s8 *)
Definition x3_regs (C : crsC_B) (sp2 : Z) : list (bv 5 * Z) :=
  crs_rbase_B C sp2 ++ crs_rsh_B C ++ [(19%bv, cb_doc C)] ++ crs_rlive_B C ++ crs_rro_B.

Lemma x3_regsat_sub : forall (regs regs' : bvmap 5 word) l l',
  crs_regsat_B regs l -> (forall p, In p l' -> In p l) -> (forall p, In p l' -> getr regs' (fst p) = getr regs (fst p)) ->
  crs_regsat_B regs' l'.
Proof.
intros regs regs' l l' H Hs Hk. unfold crs_regsat_B in *. rewrite Forall_forall in *. intros p Hp.
rewrite (Hk p Hp). exact (H p (Hs p Hp)).
Qed.

Lemma x3_regsat_app : forall (regs : bvmap 5 word) l1 l2, crs_regsat_B regs l1 -> crs_regsat_B regs l2 -> crs_regsat_B regs (l1 ++ l2).
Proof. intros regs l1 l2 H1 H2. unfold crs_regsat_B in *. apply Forall_app. split; assumption. Qed.
Lemma x3_regsat_one : forall (regs : bvmap 5 word) (r : bv 5) v, getr regs r = w64 v -> crs_regsat_B regs [(r, v)].
Proof. intros regs r v H. constructor; [exact H | constructor]. Qed.
Lemma x3_regsat_l : forall (regs : bvmap 5 word) l1 l2, crs_regsat_B regs (l1 ++ l2) -> crs_regsat_B regs l1.
Proof. intros regs l1 l2 H. unfold crs_regsat_B in *. apply Forall_app in H. exact (proj1 H). Qed.
(* the registers of x3_regs are callee-saved: a call keeps them *)
Lemma x3_regs_pres : forall (regs regs2 : bvmap 5 word) C sp2,
  crs_regsat_B regs (x3_regs C sp2) -> aregs_preserved regs regs2 -> crs_regsat_B regs2 (x3_regs C sp2).
Proof.
intros regs regs2 C sp2 H HP. apply (x3_regsat_sub regs regs2 _ _ H (fun p Hp => Hp)).
intros p Hp. cbv [x3_regs crs_rbase_B crs_rsh_B crs_rlive_B crs_rro_B app In] in Hp.
repeat (destruct Hp as [<- | Hp]; [cbn [fst]; apply (x3_ap regs regs2 _ HP); x3_cs |]). destruct Hp.
Qed.

(* the symbolic state at a point of X3 with no memory access: the TE environment, no region *)
Definition ss_x3 (off : Z) : sstate := mkSS (CRS_PC0_B + off) cur_atoms [] None (mkFacts [] [] []).

(* S10Env.v's te_close (:372-382) and Crt102Tail.v's ct_keep (:350-351), restated *)
Local Ltac x3_te_close :=
  lazymatch goal with |- ew (TE ?r0 ?rc ?mo) ?n = _ =>
    let nn := eval vm_compute in n in
    lazymatch eval vm_compute in (Nat.ltb nn 32) with
    | true => apply (te_entry r0 rc mo _ nn); reflexivity
    | false => lazymatch eval vm_compute in (Nat.ltb nn 64) with
      | true => let kk := eval vm_compute in (Nat.sub nn 32) in apply (te_cur r0 rc mo _ kk); reflexivity
      | false => let j := eval vm_compute in (Nat.sub nn 64) in rewrite (te_more_lt r0 rc mo j) by lia; reflexivity
      end
    end
  end.
Local Ltac x3_keep HS := lazymatch goal with |- getr _ ?rr = _ =>
  let H := fresh in prreg HS rr H; rewrite H; repeat rewrite ew_ewset_other by lia; x3_te_close end.

(* ---- P5 (+1124 = 0x82544, after fuzz_alloc_live): `beq a0, s6` - live == s6 jumps to R; the other arm (ABORT) is
   refuted: Lam is a permutation of the entry's, so g_live = lsum Lam = s6 ---- *)
Lemma x3_P5 : forall CTX0 C fxk ly S Hp W regs mem md k sp2 Lam peak cnt ran,
  crs_from_R_B (fx := fx) B ARx CTX0 C ->
  crs_baseR_B (fx := fx) B ARx WR CTX0 C fxk ly S Hp W regs mem md k sp2 ->
  crs_regsat_B regs (x3_regs C sp2 ++ [(10%bv, Ledger.lsum Lam)]) ->
  x3_st C (crs_evs_B C) ly S Hp W mem Lam peak cnt SIZE_MAXZ ran -> crs_cnt_end_B C cnt ran -> cnt < 2 ^ 62 ->
  SRr' SEGS YGcfRehidePost.RZ_cf W (crs_cfg_B fxk (BASE + (CRS_PC0_B + 1124)) regs mem md) (crs_post_B (fx := fx) B ARx C).
Proof.
intros CTX0 C fxk ly S Hp W regs mem md k sp2 Lam peak cnt ran HR HB HRG HST HCE Hc62.
pose proof HB as (Hpre & HFZ & HFK & HJ & HFR & HSV & HSL & HROD & HMN & HR3 & HR4 & Hs1 & Hs2 & Hs3 & HDPk).
pose proof HST as (HL & Hpk & Hran & Hcn & HRL & HPOS & (HPL & HPA) & HBY & HT).
unfold crs_cfg_B.
assert (HS : @st_ok_pi SEGS VAL fxk (TE (cb_regs C) regs []) (ss_x3 1124)
  (restrict (w_H W) (@YK11.mkst fxk regs (Z_to_bv 64 (BASE + (CRS_PC0_B + 1124))) mem (YK11.seg_rom SEGS)))).
{ apply ts_st_ok; [apply te_regs_ok | reflexivity | constructor | exact I | split; [exact I | split; exact I]]. }
assert (SHOK : sh_ok SEGS (SLit 0) [] (TE (cb_regs C) regs []) (mrestrict (w_H W) mem)) by apply Forall_nil.
assert (HEI : img_env VAL A_LIM (TE (cb_regs C) regs [])) by apply te_env.
unfold crs_JR_B in HJ.
pose (RUNTO := @paj_run_to_xR fxk rc SK B_prog_listing PL PA B PST ARx _ LAWS WR WRr WRt).
pose (BR := paj_branchR (fx := fxk) (L := B_prog_listing) (PI := PA) WR).
assert (E10 : getr regs 10 = w64 (Ledger.lsum Lam)) by (apply (x3_rget _ _ _ _ HRG); cbv [x3_regs crs_rbase_B crs_rsh_B crs_rlive_B crs_rro_B app In]; tauto).
assert (E22 : getr regs 22 = w64 (Ledger.lsum (cb_Lam C))) by (apply (x3_rget _ _ _ _ HRG); cbv [x3_regs crs_rbase_B crs_rsh_B crs_rlive_B crs_rro_B app In]; tauto).
psrr_branch_tokR RUNTO BR HS SHOK (0, 0).
- paj_run_to_tok_x RUNTO HS HJ SHOK (0, 0) CRS_PC_R_B.
  { cbv [ss_x3 ss_mem add_cond]. apply awr_ok_nil. }
  apply frame_of_read_only in HF; [|vm_compute; reflexivity]. clear HFr HG.
  assert (KR : forall p, In p (crs_rbase_B C sp2 ++ crs_rsh_B C) -> getr (ms_regs ms) (fst p) = getr regs (fst p)).
  { intros p Hpp. cbv [crs_rbase_B crs_rsh_B app In] in Hpp.
    repeat (destruct Hpp as [<- | Hpp]; [cbn [fst]; x3_keep HS |]). destruct Hpp. }
  assert (KR3 : getr (ms_regs ms) 3 = getr regs 3) by x3_keep HS.
  assert (KR4 : getr (ms_regs ms) 4 = getr regs 4) by x3_keep HS.
  pmkst HS. rewrite HF in *.
  lazymatch goal with |- context [{| cfg_ms := mkst _ (Z_to_bv 64 (_ + ?n)) _ _; cfg_model := _ |}] =>
    change n with CRS_PC_R_B end.
  pose proof (x3_pre_more CTX0 C Hpre) as (_ & _ & _ & Hcr0 & _).
  apply (HR fxk ly S Hp W (ms_regs ms) mem _ k sp2 Lam peak cnt ran).
  + exact (x3_base_md WR CTX0 C fxk ly S Hp W regs mem md k sp2 (ms_regs ms) _ HB HJ KR3 KR4).
  + apply (x3_regsat_sub regs (ms_regs ms) _ _ HRG); [|exact KR].
    intros p Hpp. unfold x3_regs. rewrite !in_app_iff in *. tauto.
  + split; [|split; [exact HPL | exact HPA]].
    split; [exact HL|]. split; [exact Hpk|]. split; [rewrite Hcr0; exact Hran|]. split; [exact Hcn|].
    split; [exact Hc62|]. split; [exact HRL | exact HPOS].
  + exact HBY.
  + exact HT.
  + exact HCE.
- exfalso.
  rewrite branch_eq_U in Hc.
  pose proof (prh_ledger_bounds B ly S Hp W mem Lam peak cnt SIZE_MAXZ ran _ _ HL) as (Hb1 & Hb2 & _).
  pose proof (crs_lsum_perm_B _ _ HPL) as Elsum.
  rewrite (U_atom _ 42 (Ledger.lsum Lam)) in Hc by (try lia; rewrite (te_cur (cb_regs C) regs [] 10%bv 10) by reflexivity; exact E10).
  rewrite (U_atom _ 54 (Ledger.lsum (cb_Lam C))) in Hc by (try lia; rewrite (te_cur (cb_regs C) regs [] 22%bv 22) by reflexivity; exact E22).
  rewrite Elsum, Z.eqb_refl in Hc. discriminate Hc.
Qed.

(* x3_st and the end count give crs_core_B (and crs_perm_B) at a boundary, g_fail_at = SIZE_MAX *)
Lemma x3_core_of_st : forall CTX0 C evs ly S Hp W mem Lam peak cnt ran,
  crs_pre_B (fx := fx) B ARx CTX0 C -> x3_st C evs ly S Hp W mem Lam peak cnt SIZE_MAXZ ran -> cnt < 2 ^ 62 ->
  crs_core_B B C ly S Hp W mem Lam peak cnt ran evs /\ crs_perm_B B C ly S Lam.
Proof.
intros CTX0 C evs ly S Hp W mem Lam peak cnt ran Hpre (HL & Hpk & Hran & Hcn & HRL & HPOS & HPM & _ & _) Hc62.
pose proof (x3_pre_more CTX0 C Hpre) as (_ & _ & _ & Hcr0 & _).
split; [|exact HPM]. split; [exact HL|]. split; [exact Hpk|]. split; [rewrite Hcr0; exact Hran|].
split; [exact Hcn|]. split; [exact Hc62|]. split; [exact HRL | exact HPOS].
Qed.

(* ---- P4 (+1112 = 0x82538, after fuzz_alloc_ran_out): `bnez a0` (the RAN arm) -> F with s7 = 0; `bnez s7` -> ABORT
   is refuted (s7 = 0, the injected write's NULL); `jal fuzz_alloc_live`, then P5 ---- *)
Lemma x3_P4 : forall CTX0 C,
  CrsKeep_B B ARx ->
  (forall fxq, tfuzz_alloc_live_specX (fx := fxq) (PI := prh_img_B) (RL := RL) (PA := PA) B ARx SK) ->
  crs_from_F_B (fx := fx) B ARx CTX0 C -> crs_from_R_B (fx := fx) B ARx CTX0 C ->
  forall fxk ly S Hp W regs mem md k sp2 Lam peak cnt ran,
  crs_baseR_B (fx := fx) B ARx WR CTX0 C fxk ly S Hp W regs mem md k sp2 ->
  crs_regsat_B regs (x3_regs C sp2 ++ [(23%bv, 0); (10%bv, ran)]) ->
  x3_st C (crs_evs_B C) ly S Hp W mem Lam peak cnt SIZE_MAXZ ran -> crs_cnt_end_B C cnt ran -> cnt < 2 ^ 62 ->
  SRr' SEGS YGcfRehidePost.RZ_cf W (crs_cfg_B fxk (BASE + (CRS_PC0_B + 1112)) regs mem md) (crs_post_B (fx := fx) B ARx C).
Proof.
intros CTX0 C HK HTL HF HR fxk ly S Hp W regs mem md k sp2 Lam peak cnt ran HB HRG HST HCE Hc62.
pose proof HB as (Hpre & HFZ & HFK & HJ & HFR & HSV & HSL & HROD & HMN & HR3 & HR4 & Hs1 & Hs2 & Hs3 & HDPk).
pose proof HST as (HL & Hpk & Hran & Hcn & HRL & HPOS & (HPL & HPA) & HBY & HT).
pose proof (x3_pre_stack CTX0 C Hpre) as (Hal0 & Hceil0 & Hhi0 & H47 & Htop0 & _ & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof x3_stk as (ESTK & EF0 & EL0 & ER0 & EC0 & EW0).
pose proof crs_frame_is_pi_B as EFR. unfold CRS_FRAME_B in EFR, Hs1.
unfold crs_cfg_B.
assert (HS : @st_ok_pi SEGS VAL fxk (TE (cb_regs C) regs []) (ss_x3 1112)
  (restrict (w_H W) (@YK11.mkst fxk regs (Z_to_bv 64 (BASE + (CRS_PC0_B + 1112))) mem (YK11.seg_rom SEGS)))).
{ apply ts_st_ok; [apply te_regs_ok | reflexivity | constructor | exact I | split; [exact I | split; exact I]]. }
assert (SHOK : sh_ok SEGS (SLit 0) [] (TE (cb_regs C) regs []) (mrestrict (w_H W) mem)) by apply Forall_nil.
assert (HEI : img_env VAL A_LIM (TE (cb_regs C) regs [])) by apply te_env.
unfold crs_JR_B in HJ.
pose (RUN := @paj_run_xR fxk rc SK B_prog_listing PL PA B PST ARx _ LAWS WR WRr WRt).
pose (RUNTO := @paj_run_to_xR fxk rc SK B_prog_listing PL PA B PST ARx _ LAWS WR WRr WRt).
pose (BR := paj_branchR (fx := fxk) (L := B_prog_listing) (PI := PA) WR).
assert (E10 : getr regs 10 = w64 ran) by (apply (x3_rget _ _ _ _ HRG); cbv [x3_regs crs_rbase_B crs_rsh_B crs_rlive_B crs_rro_B app In]; tauto).
assert (E23 : getr regs 23 = w64 0) by (apply (x3_rget _ _ _ _ HRG); cbv [x3_regs crs_rbase_B crs_rsh_B crs_rlive_B crs_rro_B app In]; tauto).
assert (E2 : getr regs 2 = w64 sp2) by (apply (x3_rget _ _ _ _ HRG); cbv [x3_regs crs_rbase_B crs_rsh_B crs_rlive_B crs_rro_B app In]; tauto).
assert (E8 : getr regs 8 = w64 (spZ (cb_regs C))) by (apply (x3_rget _ _ _ _ HRG); cbv [x3_regs crs_rbase_B crs_rsh_B crs_rlive_B crs_rro_B app In]; tauto).
psrr_branch_tokR RUN BR HS SHOK (0, 0).
- (* the RAN arm: g_ran_out <> 0 - refuted, nothing was refused (x3_st's ran = 0, K0-DEAD-PJWRITE) *)
  exfalso. rewrite branch_ne_U in Hc.
  rewrite (U_atom _ 42 ran) in Hc by (try lia; rewrite (te_cur (cb_regs C) regs [] 10%bv 10) by reflexivity; exact E10).
  rewrite U_SLit in Hc. rewrite Hran in Hc. discriminate Hc.
- (* g_ran_out = 0: `bnez s7` (s7 = 0, refuted), then `jal fuzz_alloc_live` *)
  paj_run_tok_x RUN HS HJ SHOK (0, 0).
  { cbv [ss_x3 ss_mem add_cond]. apply awr_ok_nil. }
  apply frame_of_read_only in HF0; [|vm_compute; reflexivity]. clear HFr HG.
  psrr_branch_tokR RUN BR HS SHOK (0, 0).
  + exfalso. rewrite branch_ne_U in Hc0.
    rewrite (U_atom _ 55 0) in Hc0 by (try lia; rewrite (te_cur (cb_regs C) regs [] 23%bv 23) by reflexivity; exact E23).
    rewrite U_SLit in Hc0. discriminate Hc0.
  + paj_run_tok_x RUN HS HJ SHOK (0, 0).
    { cbv [ss_x3 ss_mem add_cond]. apply awr_ok_nil. }
    apply frame_of_read_only in HF1; [|vm_compute; reflexivity]. clear HFr HG.
    rewrite wvb_collapse in HJ. rewrite HF1, HF0 in HJ.
    assert (KR : forall p, In p (x3_regs C sp2) -> getr (ms_regs ms0) (fst p) = getr regs (fst p)).
    { intros p Hpp. cbv [x3_regs crs_rbase_B crs_rsh_B crs_rlive_B crs_rro_B app In] in Hpp.
      repeat (destruct Hpp as [<- | Hpp]; [cbn [fst]; x3_keep HS |]). destruct Hpp. }
    assert (KR3 : getr (ms_regs ms0) 3 = getr regs 3) by x3_keep HS.
    assert (KR4 : getr (ms_regs ms0) 4 = getr regs 4) by x3_keep HS.
    prreg HS (1%bv : bv 5) Z1.
    assert (A1 : getr (ms_regs ms0) 1 = Z_to_bv 64 (BASE + (CRS_PC0_B + 1124))).
    { rewrite Z1. f_equal; try (vm_compute; reflexivity). }
    assert (HRG0 : crs_regsat_B regs (x3_regs C sp2)) by exact (x3_regsat_l _ _ _ HRG).
    assert (HRGm : crs_regsat_B (ms_regs ms0) (x3_regs C sp2)) by exact (x3_regsat_sub regs (ms_regs ms0) _ _ HRG0 (fun p Hp => Hp) KR).
    assert (HBm : crs_baseR_B (fx := fx) B ARx WR CTX0 C fxk ly S Hp W (ms_regs ms0) (ms_mem ms0)
      (with_vm_backing (m_vm_lazy md) mat0 md) k sp2).
    { rewrite HF1, HF0. exact (x3_base_md WR CTX0 C fxk ly S Hp W regs mem md k sp2 (ms_regs ms0) _ HB HJ KR3 KR4). }
    assert (HSTm : x3_st C (crs_evs_B C) ly S Hp W (ms_mem ms0) Lam peak cnt SIZE_MAXZ ran) by (rewrite HF1, HF0; exact HST).
    apply (x3_acc_call HK WR WRr WRt WRw CTX0 C (crs_evs_B C) fxk (STK_fuzz_alloc_live (PI := prh_img_B)) 1124 W _ _ ms0 _ ly S Hp k sp2 Lam peak cnt SIZE_MAXZ ran SIZE_MAXZ
      (fun ly' S' Hp' W' regs' mem' md' =>
         (room_live_cf S -> room_live_cf S') /\
         getr regs' 10 = w64 (Ledger.lsum Lam) /\ Hp' = Hp /\ S' = S /\ ablocks B ly' S' = ablocks B ly S /\
         LEDGER ly' S' Hp' W' mem' Lam peak cnt SIZE_MAXZ ran (cb_most C) 0) _ HS eq_refl HBm).
    * rewrite (KR (2%bv, sp2)) by (cbv [x3_regs crs_rbase_B crs_rsh_B crs_rlive_B crs_rro_B app In]; tauto). exact E2.
    * rewrite (KR (8%bv, spZ (cb_regs C))) by (cbv [x3_regs crs_rbase_B crs_rsh_B crs_rlive_B crs_rro_B app In]; tauto). exact E8.
    * exact A1.
    * lia.
    * reflexivity.
    * rewrite EL0. lia.
    * rewrite EL0, ESTK. unfold CRS_FRAME_B. rewrite EFR. lia.
    * exact HSTm.
    * intros ch1 HFPRE.
      exact (HTL fxk ly S Hp W (ms_regs ms0) (ms_mem ms0) _ ch1 Lam peak cnt SIZE_MAXZ ran (cb_most C) 0 HFPRE
        ltac:(rewrite HF1, HF0; exact HL)).
    * intros ly2 S2 Hp2 W2 regs2 mem2 md2 (_ & _ & EHp & ES & EAB & HL2). exact (conj EHp (conj ES (conj EAB HL2))).
    * intros ly2 S2 Hp2 W2 regs2 mem2 md2 k1 HB2 HP (_ & R10 & _) HST2.
      apply (x3_P5 CTX0 C fxk ly2 S2 Hp2 W2 regs2 mem2 md2 (k + k1) sp2 Lam peak cnt ran HR HB2); [| exact HST2 | exact HCE | exact Hc62].
      apply x3_regsat_app; [exact (x3_regs_pres _ _ C sp2 HRGm HP) | exact (x3_regsat_one _ _ _ R10)].
Qed.

End f.
End d.

(* ======== the points P3 .. P1 and the closing lemma: a second Section over the same Context ======== *)
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams} {RL : PrhRoomLive}.
Context {SK : YI16.sink_head}.
#[local] Existing Instance prh_img_B.
(* S1ImgB loads lib/A's image (S1ImgA): the B' listing and image instances are preferred here, so an implicit PAImg /
   PAListing argument is the B' one *)
#[local] Existing Instance PI_prog_B | 0.
#[local] Existing Instance PL_prog_B | 0.
#[local] Notation PA := (PI_prog_B).
#[local] Notation PL := (PL_prog_B).
#[local] Notation SEGS := (@pa_segs _ B_prog_listing PA).
#[local] Notation VAL := (@pa_val _ B_prog_listing PA).
#[local] Notation SIGMA := (@pa_sigma _ B_prog_listing PA).
#[local] Notation BASE := (@pa_val _ B_prog_listing PA A_TEXT).
#[local] Notation RLO := (@pa_relro_lo _ B_prog_listing PA).
#[local] Notation RHI := (@pa_relro_hi _ B_prog_listing PA).
#[local] Notation PST := (prh_pst (PI := prh_img_B)).

Local Ltac x3_te_close :=
  lazymatch goal with |- ew (TE ?r0 ?rc ?mo) ?n = _ =>
    let nn := eval vm_compute in n in
    lazymatch eval vm_compute in (Nat.ltb nn 32) with
    | true => apply (te_entry r0 rc mo _ nn); reflexivity
    | false => lazymatch eval vm_compute in (Nat.ltb nn 64) with
      | true => let kk := eval vm_compute in (Nat.sub nn 32) in apply (te_cur r0 rc mo _ kk); reflexivity
      | false => let j := eval vm_compute in (Nat.sub nn 64) in rewrite (te_more_lt r0 rc mo j) by lia; reflexivity
      end
    end
  end.
Local Ltac x3_keep HS := lazymatch goal with |- getr _ ?rr = _ =>
  let H := fresh in prreg HS rr H; rewrite H; repeat rewrite ew_ewset_other by lia; x3_te_close end.
Local Ltac x3_in := cbv [x3_regs crs_rbase_B crs_rsh_B crs_rlive_B crs_rro_B app In]; tauto.

Section f.
Variable B : asyms.
Variable ARx : alayout -> astate -> list Z -> world SEGS -> (word -> option byte) -> Model -> Prop.
Hypothesis LAWS : AR_laws_x SEGS B ARx cf_head.
#[local] Notation AJ := (ajournal_x (SK := SK) SEGS B PST ARx).
#[local] Notation AJR := (ajournal_xR (SK := SK) SEGS B PST ARx).
(* the re-hiding relation of the cuts after pj_parse (the kit's crs_from_X3_B / F / R) *)
#[local] Notation WR := (wle' SEGS YGcfRehidePost.RZ_cf).
#[local] Notation WRr := (wle'_refl SEGS YGcfRehidePost.RZ_cf).
#[local] Notation WRt := (wle'_trans SEGS YGcfRehidePost.RZ_cf).
#[local] Notation WRw := (wle_wle' SEGS YGcfRehidePost.RZ_cf).
#[local] Notation LEDGER := (prh_ledger (PI := prh_img_B) (PA := PA) B).
#[local] Notation STK := (STK_check_reject_clean_starved (PI := prh_img_B)).

(* ---- the count arithmetic of the injected compact write (pj_write (doc, 0) with g_fail_at = c + pick N0, c the
   count after the whole compact write): it is refused (NULL), it makes 1 .. pick N0 + 1 calls, exactly pick N0 + 1
   when g_ran_out stays 0; so the count meets crs_cnt_end_B, and stays below 2 ^ 62 under HB_took ---- *)
Lemma x3_inj_count : forall C ok ran',
  cb_doc C <> 0 -> 0 <= cb_cnt C < 2 ^ 62 - 2 ^ 30 -> 0 <= cb_took C <= 2 ^ 28 ->
  PjWriteHyp.wlen (cb_t C) false + 1 < 2 ^ 24 -> PjWriteHyp.wlen (cb_t C) true + 1 < 2 ^ 28 ->
  let P := WriterValue.wdpieces (cb_t C) false in
  let c := crs_cnt2_B C + cN0_B C in let j := ck_pick (cb_tb C) (cN0_B C) in
  let st' := prhWriter_putN ok (WriterApp.w0 c (c + j)) P in
  prh_oks ok c (c + j) (prhWriter_k ok (WriterApp.w0 c (c + j)) P) (prhWriter_reqs ok (WriterApp.w0 c (c + j)) P)
    (cb_most C) 0 ran' ->
  prh_granted ok c (c + j) (prhWriter_k ok (WriterApp.w0 c (c + j)) P) ->
  WriterApp.w_failed st' <> 0 /\ ran' = 0 /\ c <= WriterApp.w_cnt st' /\
  crs_cnt_end_B C (WriterApp.w_cnt st') ran' /\ WriterApp.w_cnt st' < 2 ^ 62.
Proof.
intros C ok ran' Hdoc Hc0 Htk Hw0 Hw1. cbv zeta. intros Hoks Hgr.
pose proof (crs_wN_pos (cb_t C) false) as N0p. pose proof (crs_wN_pos (cb_t C) true) as N1p.
pose proof (crs_wN_le (cb_t C) false ltac:(lia)) as N0l. pose proof (crs_wN_le (cb_t C) true ltac:(lia)) as N1l.
assert (EN0 : cN0_B C = Z.of_nat (length (WriterSpec.grow_calls 0 0 (WriterSpec.piece_lens (WriterValue.wdpieces (cb_t C) false)))))
  by reflexivity.
assert (EN1 : cN1_B C = Z.of_nat (length (WriterSpec.grow_calls 0 0 (WriterSpec.piece_lens (WriterValue.wdpieces (cb_t C) true)))))
  by reflexivity.
set (n0 := length (WriterSpec.grow_calls 0 0 (WriterSpec.piece_lens (WriterValue.wdpieces (cb_t C) false)))) in *.
set (n1 := length (WriterSpec.grow_calls 0 0 (WriterSpec.piece_lens (WriterValue.wdpieces (cb_t C) true)))) in *.
pose proof (crs_pick_lt (cb_tb C) (cN0_B C) ltac:(lia)) as Pj.
pose proof (crs_pick_lt (cb_tb C) (cN1_B C) ltac:(lia)) as P1.
assert (Hfirst : 0 <= crs_first_B C <= cb_took C).
{ unfold crs_first_B. destruct (Z.eqb_spec (cb_took C) 0) as [E|E]; [lia|].
  pose proof (crs_pick_lt (cb_tb C) (cb_took C) ltac:(lia)). lia. }
assert (E2 : crs_cnt2_B C = cb_cnt C + crs_first_B C + cN1_B C + ck_pick (cb_tb C) (cN1_B C) + 1)
  by (unfold crs_cnt2_B, crs_cnt1_B; lia).
set (c := crs_cnt2_B C + cN0_B C) in *. set (j := ck_pick (cb_tb C) (cN0_B C)) in *.
assert (Hjn : (Z.to_nat j < n0)%nat) by lia.
assert (Hcb : c + Z.of_nat n0 + 1 < 2 ^ 64) by lia.
destruct (crs_winj (WriterValue.wdpieces (cb_t C) false) c (Z.to_nat j) ok ltac:(lia) Hjn Hcb) as (Hfl & Hk & Hcnt & Hall).
rewrite Z2Nat.id in Hfl, Hk, Hcnt, Hall by lia.
set (kk := prhWriter_k ok (WriterApp.w0 c (c + j)) (WriterValue.wdpieces (cb_t C) false)) in *.
(* K0-DEAD-PJWRITE: no refusal (prh_granted), so g_ran_out is kept (PRW_CrsModel.crs_ran_of_granted) and every failed
   outcome is the injected one *)
pose proof (crs_ran_of_granted _ _ _ _ _ _ _ _ Hoks Hgr) as Hran.
assert (Hk0 : ran' = 0 -> kk = S (Z.to_nat j)).
{ intros _. apply Hall. intros i Hi Hok. exact (Hgr i Hi Hok). }
split; [exact Hfl|]. split; [exact Hran|]. split; [lia|].
assert (Hmax : ck_crcs_max (cb_tb C) (cb_took C) (cb_doc C) (cb_t C) = crs_first_B C + 2 * cN1_B C + 2 * cN0_B C).
{ unfold ck_crcs_max, crs_first_B, cN1_B, cN0_B. rewrite (proj2 (Z.eqb_neq (cb_doc C) 0) Hdoc). lia. }
split; [split|].
- rewrite Hcnt, Hmax. lia.
- intros Hr0. rewrite (crs_growth_doc_B C Hdoc), Hcnt, (Hk0 Hr0). unfold crs_cnt3_B. lia.
- rewrite Hcnt. lia.
Qed.

(* the symbolic state at P3: the own cell through s8 (read-only, its byte the extra atom 64) *)
Definition ss_x3own : sstate := mkSS (CRS_PC0_B + 1100) cur_atoms
  [YP09.mkRegion (Some (xr 24)) CRS_OFF_OWN_B (CRS_OFF_OWN_B + 1) 0 0 [YP09.mkChunk CRS_OFF_OWN_B (CVal 1 (SOff 64 0))]] None
  (mkFacts [] [] []).

(* ---- P3 (+1100 = 0x8252c, after fuzz_alloc_fail (-1)): `lbu a0, 540(s8)` and `bnez a0` (the OWN arm, check #5)
   is refuted: the boundary ledger's own cell g_own_ran_out = CRS_RO_B + 540 holds 0 (prh_ledger_own); then
   `jal fuzz_alloc_ran_out`, then P4 ---- *)
Lemma x3_P3 : forall CTX0 C,
  CrsKeep_B B ARx ->
  (forall fxq, tfuzz_alloc_live_specX (fx := fxq) (PI := prh_img_B) (RL := RL) (PA := PA) B ARx SK) ->
  (forall fxq, tfuzz_alloc_ran_out_specX (fx := fxq) (PI := prh_img_B) (RL := RL) (PA := PA) B ARx SK) ->
  crs_from_F_B (fx := fx) B ARx CTX0 C -> crs_from_R_B (fx := fx) B ARx CTX0 C ->
  forall fxk ly S Hp W regs mem md k sp2 Lam peak cnt ran,
  crs_baseR_B (fx := fx) B ARx WR CTX0 C fxk ly S Hp W regs mem md k sp2 ->
  crs_regsat_B regs (x3_regs C sp2 ++ [(23%bv, 0)]) ->
  x3_st B C (crs_evs_B C) ly S Hp W mem Lam peak cnt SIZE_MAXZ ran -> crs_cnt_end_B C cnt ran -> cnt < 2 ^ 62 ->
  SRr' SEGS YGcfRehidePost.RZ_cf W (crs_cfg_B fxk (BASE + (CRS_PC0_B + 1100)) regs mem md) (crs_post_B (fx := fx) B ARx C).
Proof.
intros CTX0 C HK HTL HTR HF HR fxk ly S Hp W regs mem md k sp2 Lam peak cnt ran HB HRG HST HCE Hc62.
pose proof HB as (Hpre & HFZ & HFK & HJ & HFR & HSV & HSL & HROD & HMN & HR3 & HR4 & Hs1 & Hs2 & Hs3 & HDPk).
pose proof HST as (HL & Hpk & Hran & Hcn & HRL & HPOS & (HPL & HPA) & HBY & HT).
pose proof (x3_pre_stack (fx := fx) B ARx CTX0 C Hpre) as (Hal0 & Hceil0 & Hhi0 & H47 & Htop0 & _ & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof x3_stk as (ESTK & EF0 & EL0 & ER0 & EC0 & EW0).
pose proof crs_frame_is_pi_B as EFR. unfold CRS_FRAME_B in EFR, Hs1.
assert (HVM0 : val_mem SEGS (mrestrict (w_H W) mem) (CRS_RO_B + CRS_OFF_OWN_B) 1 0).
{ pose proof (prh_ledger_own B _ _ _ _ _ _ _ _ _ _ _ _ HL) as (HOWN & _).
  replace (CRS_RO_B + CRS_OFF_OWN_B) with (@pi_g_own_ran_out prh_img_B) by (vm_compute; reflexivity). exact HOWN. }
destruct (ex_intro (fun v => v = 0 /\ val_mem SEGS (mrestrict (w_H W) mem) (CRS_RO_B + CRS_OFF_OWN_B) 1 v) 0
  (conj eq_refl HVM0)) as (v & Ev & HVM).
assert (Hv : 0 <= v < 256) by lia.
assert (E24 : getr regs 24 = w64 CRS_RO_B) by (apply (x3_rget _ _ _ _ HRG); x3_in).
assert (E23 : getr regs 23 = w64 0) by (apply (x3_rget _ _ _ _ HRG); x3_in).
assert (E2 : getr regs 2 = w64 sp2) by (apply (x3_rget _ _ _ _ HRG); x3_in).
assert (E8 : getr regs 8 = w64 (spZ (cb_regs C))) by (apply (x3_rget _ _ _ _ HRG); x3_in).
assert (ERO : CRS_RO_B = 0x5de2bc) by (vm_compute; reflexivity).
assert (X24 : bv_unsigned (ew (TE (cb_regs C) regs [w64 v]) (xr 24)) = CRS_RO_B).
{ unfold xr. rewrite (te_cur (cb_regs C) regs _ 24%bv 24) by reflexivity. rewrite E24. apply unsigned_lit_small. lia. }
assert (E64 : ew (TE (cb_regs C) regs [w64 v]) 64 = w64 v) by exact (te_more_lt (cb_regs C) regs [w64 v] 0 ltac:(lia)).
unfold crs_cfg_B.
assert (HS : @st_ok_pi SEGS VAL fxk (TE (cb_regs C) regs [w64 v]) ss_x3own
  (restrict (w_H W) (@YK11.mkst fxk regs (Z_to_bv 64 (BASE + (CRS_PC0_B + 1100))) mem (YK11.seg_rom SEGS)))).
{ apply ts_st_ok; [apply te_regs_ok | vm_compute; reflexivity | | | split; [exact I | split; exact I]].
  - constructor; [|constructor].
    apply (ts_rok _ _ (xr 24) CRS_RO_B); [exact X24 | unfold CRS_OFF_OWN_B; lia | unfold CRS_OFF_OWN_B; lia | intros o Ho; lia |].
    constructor; [|constructor].
    apply (ts_chunk _ _ _ CRS_OFF_OWN_B 1 (SOff 64 0) v);
      [cbn [sv_denot]; rewrite E64, Z.add_0_r; unfold w64; rewrite Z_to_bv_bv_unsigned; reflexivity | cbn; lia | cbn; lia | exact HVM].
  - cbn [pairwise_disjoint all_disjoint]. exact (conj I I). }
assert (SHOK : sh_ok SEGS (SLit 0) [] (TE (cb_regs C) regs [w64 v]) (mrestrict (w_H W) mem)) by apply Forall_nil.
assert (HEI : img_env VAL A_LIM (TE (cb_regs C) regs [w64 v])) by apply te_env.
unfold crs_JR_B in HJ.
pose (RUN := @paj_run_xR fxk rc SK B_prog_listing PL PA B PST ARx _ LAWS WR WRr WRt).
pose (RUNTO := @paj_run_to_xR fxk rc SK B_prog_listing PL PA B PST ARx _ LAWS WR WRr WRt).
pose (BR := paj_branchR (fx := fxk) (L := B_prog_listing) (PI := PA) WR).
assert (HAW : forall E' st0, awr_ok E' (ss_mem ss_x3own) STK (spZ (cb_regs C)) [] (ablocks B (cb_ly C) (cb_S C)) (ablocks B ly S) ly st0).
{ intros E' st0 a (rr & Hr & Ha). cbv [ss_x3own ss_mem In] in Hr. destruct Hr as [<- | []].
  cbn [YP09.r_wlo YP09.r_whi] in Ha. lia. }
paj_run_tok_x RUN HS HJ SHOK (0, 0).
{ apply HAW. }
apply frame_of_read_only in HF0; [|vm_compute; reflexivity]. clear HFr HG.
psrr_branch_tokR RUN BR HS SHOK (0, 0).
- (* the OWN arm, refuted: the cell holds 0 *)
  exfalso. subst v. cbn [sv_denot] in Hc. rewrite E64 in Hc. vm_compute in Hc. discriminate Hc.
- (* the cell reads 0: `jal fuzz_alloc_ran_out`, then P4 *)
  paj_run_tok_x RUN HS HJ SHOK (0, 0).
  { apply HAW. }
  apply frame_of_read_only in HF1; [|vm_compute; reflexivity]. clear HFr HG.
  rewrite wvb_collapse in HJ. rewrite HF1, HF0 in HJ.
  assert (KR : forall p, In p (x3_regs C sp2 ++ [(23%bv, 0)]) -> getr (ms_regs ms0) (fst p) = getr regs (fst p)).
  { intros p Hpp. cbv [x3_regs crs_rbase_B crs_rsh_B crs_rlive_B crs_rro_B app In] in Hpp.
    repeat (destruct Hpp as [<- | Hpp]; [cbn [fst]; x3_keep HS |]). destruct Hpp. }
  assert (KR3 : getr (ms_regs ms0) 3 = getr regs 3) by x3_keep HS.
  assert (KR4 : getr (ms_regs ms0) 4 = getr regs 4) by x3_keep HS.
  prreg HS (1%bv : bv 5) Z1.
  assert (A1 : getr (ms_regs ms0) 1 = Z_to_bv 64 (BASE + (CRS_PC0_B + 1112))).
  { rewrite Z1. f_equal; try (vm_compute; reflexivity). }
  assert (HRGm : crs_regsat_B (ms_regs ms0) (x3_regs C sp2 ++ [(23%bv, 0)])) by exact (x3_regsat_sub regs (ms_regs ms0) _ _ HRG (fun p Hp => Hp) KR).
  assert (HBm : crs_baseR_B (fx := fx) B ARx WR CTX0 C fxk ly S Hp W (ms_regs ms0) (ms_mem ms0)
    (with_vm_backing (m_vm_lazy md) mat0 md) k sp2).
  { rewrite HF1, HF0. exact (x3_base_md (fx := fx) B ARx WR CTX0 C fxk ly S Hp W regs mem md k sp2 (ms_regs ms0) _ HB HJ KR3 KR4). }
  assert (HSTm : x3_st B C (crs_evs_B C) ly S Hp W (ms_mem ms0) Lam peak cnt SIZE_MAXZ ran) by (rewrite HF1, HF0; exact HST).
  apply (x3_acc_call (fx := fx) B ARx LAWS HK WR WRr WRt WRw CTX0 C (crs_evs_B C) fxk (STK_fuzz_alloc_ran_out (PI := prh_img_B)) 1112 W _ _ ms0 _
    ly S Hp k sp2 Lam peak cnt SIZE_MAXZ ran SIZE_MAXZ
    (fun ly' S' Hp' W' regs' mem' md' =>
       (room_live_cf S -> room_live_cf S') /\
       getr regs' 10 = w64 ran /\ Hp' = Hp /\ S' = S /\ ablocks B ly' S' = ablocks B ly S /\
       LEDGER ly' S' Hp' W' mem' Lam peak cnt SIZE_MAXZ ran (cb_most C) 0) _ HS eq_refl HBm).
  + rewrite (KR (2%bv, sp2)) by x3_in. exact E2.
  + rewrite (KR (8%bv, spZ (cb_regs C))) by x3_in. exact E8.
  + exact A1.
  + lia.
  + reflexivity.
  + rewrite ER0. lia.
  + rewrite ER0, ESTK. unfold CRS_FRAME_B. rewrite EFR. lia.
  + exact HSTm.
  + intros ch1 HFPRE.
    exact (HTR fxk ly S Hp W (ms_regs ms0) (ms_mem ms0) _ ch1 Lam peak cnt SIZE_MAXZ ran (cb_most C) 0 HFPRE
      ltac:(rewrite HF1, HF0; exact HL)).
  + intros ly2 S2 Hp2 W2 regs2 mem2 md2 (_ & _ & EHp & ES & EAB & HL2). exact (conj EHp (conj ES (conj EAB HL2))).
  + intros ly2 S2 Hp2 W2 regs2 mem2 md2 k1 HB2 HP (_ & R10 & _) HST2.
    apply (x3_P4 (fx := fx) B ARx LAWS CTX0 C HK HTL HF HR fxk ly2 S2 Hp2 W2 regs2 mem2 md2 (k + k1) sp2 Lam peak cnt ran
      HB2); [| exact HST2 | exact HCE | exact Hc62].
    apply x3_regsat_app; [|apply (x3_regsat_app regs2 [((23%bv : bv 5), 0)] [((10%bv : bv 5), ran)])].
    * exact (x3_regs_pres (rc := rc) _ _ C sp2 (x3_regsat_l _ _ _ HRGm) HP).
    * apply x3_regsat_one. rewrite (x3_ap _ _ 23%bv HP) by x3_cs. apply (x3_rget _ _ 23%bv 0 HRGm). x3_in.
    * exact (x3_regsat_one _ _ _ R10).
Qed.

(* ---- P2 (+1088 = 0x82520, after pj_write (doc, 0)): `mv s7, a0` (the injected write's NULL), `li a0, -1`,
   `jal fuzz_alloc_fail` (g_fail_at = SIZE_MAX), then P3 ---- *)
Lemma x3_P2 : forall CTX0 C,
  CrsKeep_B B ARx ->
  (forall fxq, tfuzz_alloc_fail_specX (fx := fxq) (PI := prh_img_B) (RL := RL) (PA := PA) B ARx SK) ->
  (forall fxq, tfuzz_alloc_live_specX (fx := fxq) (PI := prh_img_B) (RL := RL) (PA := PA) B ARx SK) ->
  (forall fxq, tfuzz_alloc_ran_out_specX (fx := fxq) (PI := prh_img_B) (RL := RL) (PA := PA) B ARx SK) ->
  crs_from_F_B (fx := fx) B ARx CTX0 C -> crs_from_R_B (fx := fx) B ARx CTX0 C ->
  forall fxk ly S Hp W regs mem md k sp2 Lam peak cnt fail ran,
  crs_baseR_B (fx := fx) B ARx WR CTX0 C fxk ly S Hp W regs mem md k sp2 ->
  crs_regsat_B regs (x3_regs C sp2 ++ [(10%bv, 0)]) ->
  x3_st B C (crs_evs_B C) ly S Hp W mem Lam peak cnt fail ran -> crs_cnt_end_B C cnt ran -> cnt < 2 ^ 62 ->
  SRr' SEGS YGcfRehidePost.RZ_cf W (crs_cfg_B fxk (BASE + (CRS_PC0_B + 1088)) regs mem md) (crs_post_B (fx := fx) B ARx C).
Proof.
intros CTX0 C HK HTF HTL HTR HF HR fxk ly S Hp W regs mem md k sp2 Lam peak cnt fail ran HB HRG HST HCE Hc62.
pose proof HB as (Hpre & HFZ & HFK & HJ & HFR & HSV & HSL & HROD & HMN & HR3 & HR4 & Hs1 & Hs2 & Hs3 & HDPk).
pose proof HST as (HL & Hpk & Hran & Hcn & HRL & HPOS & (HPL & HPA) & HBY & HT).
pose proof x3_stk as (ESTK & EF0 & EL0 & ER0 & EC0 & EW0).
pose proof crs_frame_is_pi_B as EFR. unfold CRS_FRAME_B in EFR, Hs1.
pose proof (prh_ledger_bounds B ly S Hp W mem Lam peak cnt fail ran _ _ HL) as (_ & _ & Hcb & _).
assert (E10 : getr regs 10 = w64 0) by (apply (x3_rget _ _ _ _ HRG); x3_in).
assert (E2 : getr regs 2 = w64 sp2) by (apply (x3_rget _ _ _ _ HRG); x3_in).
assert (E8 : getr regs 8 = w64 (spZ (cb_regs C))) by (apply (x3_rget _ _ _ _ HRG); x3_in).
unfold crs_cfg_B.
assert (HS : @st_ok_pi SEGS VAL fxk (TE (cb_regs C) regs []) (ss_x3 1088)
  (restrict (w_H W) (@YK11.mkst fxk regs (Z_to_bv 64 (BASE + (CRS_PC0_B + 1088))) mem (YK11.seg_rom SEGS)))).
{ apply ts_st_ok; [apply te_regs_ok | reflexivity | constructor | exact I | split; [exact I | split; exact I]]. }
assert (SHOK : sh_ok SEGS (SLit 0) [] (TE (cb_regs C) regs []) (mrestrict (w_H W) mem)) by apply Forall_nil.
assert (HEI : img_env VAL A_LIM (TE (cb_regs C) regs [])) by apply te_env.
unfold crs_JR_B in HJ.
pose (RUN := @paj_run_xR fxk rc SK B_prog_listing PL PA B PST ARx _ LAWS WR WRr WRt).
paj_run_tok_x RUN HS HJ SHOK (0, 0).
{ cbv [ss_x3 ss_mem]. apply awr_ok_nil. }
apply frame_of_read_only in HF0; [|vm_compute; reflexivity]. clear HFr HG.
rewrite HF0 in HJ.
assert (KR : forall p, In p (x3_regs C sp2) -> getr (ms_regs ms) (fst p) = getr regs (fst p)).
{ intros p Hpp. cbv [x3_regs crs_rbase_B crs_rsh_B crs_rlive_B crs_rro_B app In] in Hpp.
  repeat (destruct Hpp as [<- | Hpp]; [cbn [fst]; x3_keep HS |]). destruct Hpp. }
assert (KR3 : getr (ms_regs ms) 3 = getr regs 3) by x3_keep HS.
assert (KR4 : getr (ms_regs ms) 4 = getr regs 4) by x3_keep HS.
prreg HS (1%bv : bv 5) Z1. prreg HS (10%bv : bv 5) Z10. prreg HS (23%bv : bv 5) Z23.
assert (A1 : getr (ms_regs ms) 1 = Z_to_bv 64 (BASE + (CRS_PC0_B + 1100))).
{ rewrite Z1. f_equal; try (vm_compute; reflexivity). }
assert (A10 : getr (ms_regs ms) 10 = w64 (2 ^ 64 - 1)) by (rewrite Z10; apply bv_eq; vm_compute; reflexivity).
assert (A23 : getr (ms_regs ms) 23 = w64 0).
{ rewrite Z23. rewrite <- E10. x3_te_close. }
assert (HRG0 : crs_regsat_B regs (x3_regs C sp2)) by exact (x3_regsat_l _ _ _ HRG).
assert (HRGm : crs_regsat_B (ms_regs ms) (x3_regs C sp2)) by exact (x3_regsat_sub regs (ms_regs ms) _ _ HRG0 (fun p Hp => Hp) KR).
assert (HBm : crs_baseR_B (fx := fx) B ARx WR CTX0 C fxk ly S Hp W (ms_regs ms) (ms_mem ms)
  (with_vm_backing (m_vm_lazy md) mat md) k sp2).
{ rewrite HF0. exact (x3_base_md (fx := fx) B ARx WR CTX0 C fxk ly S Hp W regs mem md k sp2 (ms_regs ms) _ HB HJ KR3 KR4). }
assert (HSTm : x3_st B C (crs_evs_B C) ly S Hp W (ms_mem ms) Lam peak cnt fail ran) by (rewrite HF0; exact HST).
apply (x3_acc_call (fx := fx) B ARx LAWS HK WR WRr WRt WRw CTX0 C (crs_evs_B C) fxk (STK_fuzz_alloc_fail (PI := prh_img_B)) 1100 W _ _ ms _
  ly S Hp k sp2 Lam peak cnt fail ran SIZE_MAXZ
  (fun ly' S' Hp' W' regs' mem' md' =>
     (room_live_cf S -> room_live_cf S') /\
     Hp' = Hp /\ S' = S /\ ablocks B ly' S' = ablocks B ly S /\
     LEDGER ly' S' Hp' W' mem' Lam peak cnt (if (2 ^ 64 - 1) <? SIZE_MAXZ - cnt then cnt + (2 ^ 64 - 1) else SIZE_MAXZ) ran (cb_most C) 0)
  _ HS eq_refl HBm).
- rewrite (KR (2%bv, sp2)) by x3_in. exact E2.
- rewrite (KR (8%bv, spZ (cb_regs C))) by x3_in. exact E8.
- exact A1.
- lia.
- reflexivity.
- rewrite EF0. lia.
- rewrite EF0, ESTK. unfold CRS_FRAME_B. rewrite EFR. lia.
- exact HSTm.
- intros ch1 HFPRE.
  exact (HTF fxk ly S Hp W (ms_regs ms) (ms_mem ms) _ ch1 Lam peak cnt fail ran (2 ^ 64 - 1) (cb_most C) 0 HFPRE
    ltac:(rewrite HF0; exact HL) A10 ltac:(lia)).
- intros ly2 S2 Hp2 W2 regs2 mem2 md2 (_ & EHp & ES & EAB & HL2).
  replace (if (2 ^ 64 - 1) <? SIZE_MAXZ - cnt then cnt + (2 ^ 64 - 1) else SIZE_MAXZ) with SIZE_MAXZ in HL2
    by (unfold SIZE_MAXZ; destruct (Z.ltb_spec (2 ^ 64 - 1) (2 ^ 64 - 1 - cnt)); [lia | reflexivity]).
  exact (conj EHp (conj ES (conj EAB HL2))).
- intros ly2 S2 Hp2 W2 regs2 mem2 md2 k1 HB2 HP _ HST2.
  apply (x3_P3 CTX0 C HK HTL HTR HF HR fxk ly2 S2 Hp2 W2 regs2 mem2 md2 (k + k1) sp2 Lam peak cnt ran HB2);
    [| exact HST2 | exact HCE | exact Hc62].
  apply x3_regsat_app.
  + exact (x3_regs_pres (rc := rc) _ _ C sp2 HRGm HP).
  + apply x3_regsat_one. rewrite (x3_ap _ _ 23%bv HP) by x3_cs. exact A23.
Qed.

Lemma x3_bsum_perm : forall l l', Permutation l l' -> bsum l = bsum l'.
Proof.
intros l l' H. induction H as [|x l1 l2 H IH|x y l|l1 l2 l3 H1 IH1 H2 IH2]; unfold bsum in *; cbn [fold_right] in *; lia.
Qed.


(* ---- the writer's entry events at X3's injected compact write: the kit's run (crs_pre_B) split at X3's prefix
   (crs_evs_doc_B, crs_run_split_B) is crs_ev_ws_B C false there, which is the text's prhWriter_pjw_evs at the call's counts
   (PRH_Supply.prhWriter_pjw_evs_w_starved, with cf_head = PresetReqAt.HEAD) ---- *)
Lemma x3_djb_fold : forall x h, ck_djb2 h x = fold_left (fun h b => (h * 33 + b) mod 2 ^ 64) x h.
Proof. induction x as [|c r IH]; intros h; cbn [ck_djb2 fold_left]; [reflexivity|]. rewrite IH. f_equal. f_equal. lia. Qed.
Lemma x3_pick_model : forall x n, (0 < n)%nat -> Z.of_nat (PresetReqAt.pick x n) = ck_pick x (Z.of_nat n).
Proof.
intros x n Hn. destruct n as [|n]; [lia|]. unfold PresetReqAt.pick, PresetReqAt.pick_h.
rewrite (crs_pick_eq x (Z.of_nat (S n))) by lia. rewrite x3_djb_fold.
rewrite Z2Nat.id; [reflexivity|]. apply Z.mod_pos_bound. lia.
Qed.
Lemma x3_wrun : forall CTX0 C, cf_head = PresetReqAt.HEAD -> cb_doc C <> 0 ->
  crs_pre_B (fx := fx) B ARx CTX0 C ->
  0 <= crs_cnt2_B C + cN0_B C -> crs_cnt2_B C + cN0_B C + ck_pick (cb_tb C) (cN0_B C) < 2 ^ 64 ->
  prh_run_at ReaderRes.jr_strtod (cb_rp_x C) (cb_rp_os C) (cb_rp_i C + length (crs_evs_at_X3_B C))%nat
    (prhWriter_pjw_evs [] (crs_cnt2_B C + cN0_B C) (crs_cnt2_B C + cN0_B C + ck_pick (cb_tb C) (cN0_B C))
       (WriterValue.wdpieces (cb_t C) (negb (0 =? 0)))).
Proof.
intros CTX0 C Hhd Hdoc Hpre Hc0 Hc64.
assert (Hrun : prh_run_at ReaderRes.jr_strtod (cb_rp_x C) (cb_rp_os C) (cb_rp_i C) (crs_evs_B C)) by (eapply crs_run_of_pre_B; eassumption).
assert (Hsp : prh_run_at ReaderRes.jr_strtod (cb_rp_x C) (cb_rp_os C) (cb_rp_i C + length (crs_evs_at_X3_B C))%nat (crs_ev_ws_B C false))
  by (eapply crs_run_split_B; [exact (crs_evs_doc_B C Hdoc) | exact Hrun]).
pose proof (crs_wcalls_pos_B (cb_t C) false) as Hw.
assert (EW : cN0_B C = Z.of_nat (PresetReqAt.wcalls (cb_t C) false)) by reflexivity.
assert (EK : ck_pick (cb_tb C) (cN0_B C) = Z.of_nat (PresetReqAt.pick (cb_tb C) (PresetReqAt.wcalls (cb_t C) false))).
{ rewrite EW. symmetry. apply x3_pick_model. lia. }
assert (HK : (PresetReqAt.pick (cb_tb C) (PresetReqAt.wcalls (cb_t C) false) < PresetReqAt.wcalls (cb_t C) false)%nat).
{ pose proof (crs_pick_lt (cb_tb C) (cN0_B C) ltac:(lia)) as Hl. lia. }
cbn [Z.eqb negb].
rewrite (prhWriter_pjw_evs_w_starved (cb_t C) false (crs_cnt2_B C + cN0_B C) (crs_cnt2_B C + cN0_B C + ck_pick (cb_tb C) (cN0_B C))
  (PresetReqAt.pick (cb_tb C) (PresetReqAt.wcalls (cb_t C) false)) Hhd Hc0 ltac:(lia) Hc64 HK).
exact Hsp.
Qed.

(* ... and its consumer window (the text's prh_cons_from at the call), from crs_pre_B's by the same split *)
Lemma x3_wcons : forall CTX0 C, cf_head = PresetReqAt.HEAD -> cb_doc C <> 0 ->
  crs_pre_B (fx := fx) B ARx CTX0 C ->
  0 <= crs_cnt2_B C + cN0_B C -> crs_cnt2_B C + cN0_B C + ck_pick (cb_tb C) (cN0_B C) < 2 ^ 64 ->
  PRH_Base.prh_cons_from ReaderRes.jr_strtod (cb_rp_x C) (cb_rp_os C) (cb_rp_i C + length (crs_evs_at_X3_B C))%nat
    (length (prhWriter_pjw_evs [] (crs_cnt2_B C + cN0_B C) (crs_cnt2_B C + cN0_B C + ck_pick (cb_tb C) (cN0_B C))
       (WriterValue.wdpieces (cb_t C) (negb (0 =? 0))))).
Proof.
intros CTX0 C Hhd Hdoc Hpre Hc0 Hc64.
assert (E : crs_evs_B C = crs_evs_at_X3_B C ++ crs_ev_ws_B C false ++ []) by (rewrite app_nil_r; exact (crs_evs_doc_B C Hdoc)).
pose proof (crs_cons_split_B B ARx CTX0 C _ _ _ E Hpre) as Hsp.
pose proof (crs_wcalls_pos_B (cb_t C) false) as Hw.
assert (EW : cN0_B C = Z.of_nat (PresetReqAt.wcalls (cb_t C) false)) by reflexivity.
assert (EK : ck_pick (cb_tb C) (cN0_B C) = Z.of_nat (PresetReqAt.pick (cb_tb C) (PresetReqAt.wcalls (cb_t C) false))).
{ rewrite EW. symmetry. apply x3_pick_model. lia. }
assert (HK : (PresetReqAt.pick (cb_tb C) (PresetReqAt.wcalls (cb_t C) false) < PresetReqAt.wcalls (cb_t C) false)%nat).
{ pose proof (crs_pick_lt (cb_tb C) (cN0_B C) ltac:(lia)) as Hl. lia. }
cbn [Z.eqb negb].
rewrite (prhWriter_pjw_evs_w_starved (cb_t C) false (crs_cnt2_B C + cN0_B C) (crs_cnt2_B C + cN0_B C + ck_pick (cb_tb C) (cN0_B C))
  (PresetReqAt.pick (cb_tb C) (PresetReqAt.wcalls (cb_t C) false)) Hhd Hc0 ltac:(lia) Hc64 HK).
exact Hsp.
Qed.

(* ---- P1 (+1076 = 0x82514, after fuzz_alloc_fail (h % N0)): `mv a0, s3`, `mv a1, zero`, `jal pj_write` (the
   injected compact write: refused, s7 <- NULL), then P2 ---- *)
Lemma x3_P1 : forall CTX0 C,
  (forall fxq, tfuzz_alloc_fail_specX (fx := fxq) (PI := prh_img_B) (RL := RL) (PA := PA) B ARx SK) ->
  (forall fxq, tfuzz_alloc_live_specX (fx := fxq) (PI := prh_img_B) (RL := RL) (PA := PA) B ARx SK) ->
  (forall fxq, tfuzz_alloc_ran_out_specX (fx := fxq) (PI := prh_img_B) (RL := RL) (PA := PA) B ARx SK) ->
  cf_head = PresetReqAt.HEAD ->
  CrsKeep_B B ARx -> cb_took C <= 2 ^ 28 ->
  (forall fxq, crs_wexact_B (fx := fxq) (rc := rc) B ARx CTX0 C) ->
  crs_from_F_B (fx := fx) B ARx CTX0 C -> crs_from_R_B (fx := fx) B ARx CTX0 C ->
  forall fxk ly S Hp W regs mem md k sp2 Lam peak,
  cb_doc C <> 0 -> crs_cnt2_B C + cN0_B C < 2 ^ 62 ->
  crs_baseR_B (fx := fx) B ARx WR CTX0 C fxk ly S Hp W regs mem md k sp2 ->
  crs_regsat_B regs (x3_regs C sp2) ->
  x3_st B C (crs_evs_at_X3_B C) ly S Hp W mem Lam peak (crs_cnt2_B C + cN0_B C) (crs_cnt2_B C + cN0_B C + ck_pick (cb_tb C) (cN0_B C)) 0 ->
  SRr' SEGS YGcfRehidePost.RZ_cf W (crs_cfg_B fxk (BASE + (CRS_PC0_B + 1076)) regs mem md) (crs_post_B (fx := fx) B ARx C).
Proof.
intros CTX0 C HTF HTL HTR HHD HK HBt HWX HF HR fxk ly S Hp W regs mem md k sp2 Lam peak Hdoc Hcw62 HB HRG HST.
pose proof HB as (Hpre & HFZ & HFK & HJ & HFR & HSV & HSL & HROD & HMN & HR3 & HR4 & Hs1 & Hs2 & Hs3 & HDPk).
pose proof HST as (HL & Hpk & Hran & Hcn & HRL & HPOS & (HPL & HPA) & HBY & HT).
pose proof x3_stk as (ESTK & EF0 & EL0 & ER0 & EC0 & EW0).
pose proof crs_frame_is_pi_B as EFR. unfold CRS_FRAME_B in EFR, Hs1.
pose proof (x3_pre_more (fx := fx) B ARx CTX0 C Hpre) as (HCL & HL0 & Hc0 & Hr0 & Htk0 & Hdocs & Hlive & Hrq & Hfr0).
destruct Hdocs as [Hd0 | (Hread & Htree0 & Hw0 & Hw1 & Hdep)]; [exact (False_ind _ (Hdoc Hd0))|].
pose proof (prh_ledger_bounds B _ _ _ _ _ _ _ _ _ _ _ _ HL0) as (_ & _ & Hc0b & _).
assert (E19 : getr regs 19 = w64 (cb_doc C)) by (apply (x3_rget _ _ _ _ HRG); x3_in).
assert (E2 : getr regs 2 = w64 sp2) by (apply (x3_rget _ _ _ _ HRG); x3_in).
assert (E8 : getr regs 8 = w64 (spZ (cb_regs C))) by (apply (x3_rget _ _ _ _ HRG); x3_in).
unfold crs_cfg_B.
assert (HS : @st_ok_pi SEGS VAL fxk (TE (cb_regs C) regs []) (ss_x3 1076)
  (restrict (w_H W) (@YK11.mkst fxk regs (Z_to_bv 64 (BASE + (CRS_PC0_B + 1076))) mem (YK11.seg_rom SEGS)))).
{ apply ts_st_ok; [apply te_regs_ok | reflexivity | constructor | exact I | split; [exact I | split; exact I]]. }
assert (SHOK : sh_ok SEGS (SLit 0) [] (TE (cb_regs C) regs []) (mrestrict (w_H W) mem)) by apply Forall_nil.
assert (HEI : img_env VAL A_LIM (TE (cb_regs C) regs [])) by apply te_env.
unfold crs_JR_B in HJ.
pose (RUN := @paj_run_xR fxk rc SK B_prog_listing PL PA B PST ARx _ LAWS WR WRr WRt).
paj_run_tok_x RUN HS HJ SHOK (0, 0).
{ cbv [ss_x3 ss_mem]. apply awr_ok_nil. }
apply frame_of_read_only in HF0; [|vm_compute; reflexivity]. clear HFr HG.
rewrite HF0 in HJ.
assert (KR : forall p, In p (x3_regs C sp2) -> getr (ms_regs ms) (fst p) = getr regs (fst p)).
{ intros p Hpp. cbv [x3_regs crs_rbase_B crs_rsh_B crs_rlive_B crs_rro_B app In] in Hpp.
  repeat (destruct Hpp as [<- | Hpp]; [cbn [fst]; x3_keep HS |]). destruct Hpp. }
assert (KR3 : getr (ms_regs ms) 3 = getr regs 3) by x3_keep HS.
assert (KR4 : getr (ms_regs ms) 4 = getr regs 4) by x3_keep HS.
prreg HS (1%bv : bv 5) Z1. prreg HS (10%bv : bv 5) Z10. prreg HS (11%bv : bv 5) Z11.
assert (A1 : getr (ms_regs ms) 1 = Z_to_bv 64 (BASE + (CRS_PC0_B + 1088))).
{ rewrite Z1. f_equal; try (vm_compute; reflexivity). }
assert (A10 : getr (ms_regs ms) 10 = w64 (cb_doc C)) by (rewrite Z10, <- E19; x3_te_close).
assert (A11 : getr (ms_regs ms) 11 = w64 0) by (rewrite Z11; reflexivity).
assert (HRGm : crs_regsat_B (ms_regs ms) (x3_regs C sp2)) by exact (x3_regsat_sub regs (ms_regs ms) _ _ HRG (fun p Hp => Hp) KR).
assert (HBm : crs_baseR_B (fx := fx) B ARx WR CTX0 C fxk ly S Hp W (ms_regs ms) (ms_mem ms)
  (with_vm_backing (m_vm_lazy md) mat md) k sp2).
{ rewrite HF0. exact (x3_base_md (fx := fx) B ARx WR CTX0 C fxk ly S Hp W regs mem md k sp2 (ms_regs ms) _ HB HJ KR3 KR4). }
destruct (HPOS eq_refl) as (rph & HRP).
set (rpi := (cb_rp_i C + length (crs_evs_at_X3_B C))%nat) in HRP.
destruct (HT Hdoc) as (HN & HD & HV & HO).
pose proof HO as (Hd8 & Hinf & HRA).
assert (Hfrs : Z.of_nat (length (frames S)) < fs_frames 0).
{ destruct HFR as (Hfr3 & _). exact (proj2 (proj2 (crs_cap_callee_B (cb_S C) S (cb_fpos C) Hfr3 Hfr0))). }
set (c := crs_cnt2_B C + cN0_B C) in *. set (j := ck_pick (cb_tb C) (cN0_B C)) in *.
eapply (x3_callF (fx := fx) B ARx LAWS WR WRr WRt CTX0 C fxk (STK_pj_write (PI := prh_img_B) DOC_D) 1088 W _ _ ms _ ly S Hp k sp2
  _ _ HS eq_refl HBm).
- rewrite (KR (2%bv, sp2)) by x3_in. exact E2.
- rewrite (KR (8%bv, spZ (cb_regs C))) by x3_in. exact E8.
- exact A1.
- lia.
- reflexivity.
- rewrite EW0. lia.
- rewrite EW0, ESTK. unfold CRS_FRAME_B. rewrite EFR. lia.
- (* the callee: tpj_write_specX at n = DOC_D, the injected compact write (pretty = 0) of the document, as the shared
     premise crs_wexact_B states it at this call (CrsWexAp.v: its fourth call, X3's) *)
  intros ch1 HFPRE.
  destruct (HWX fxk) as (_ & _ & _ & HW4).
  assert (HD33 : (PjTree.depth (cb_t C) <= DOC_D)%nat)
    by (assert (Z.of_nat DOC_D = 33) by (vm_compute; reflexivity); lia).
  assert (HD31 : Z.of_nat (PjTree.depth (cb_t C)) <= 2 ^ 31 - 1) by lia.
  pose proof (prh_ledger_bounds B _ _ _ _ _ _ _ _ _ _ _ _ HL) as (_ & _ & Hcb & Hfb & _).
  assert (HWR := x3_wrun CTX0 C HHD Hdoc Hpre ltac:(unfold c in Hcb; lia) ltac:(unfold c, j in *; lia)).
  assert (HWC := x3_wcons CTX0 C HHD Hdoc Hpre ltac:(unfold c in Hcb; lia) ltac:(unfold c, j in *; lia)).
  (* crs_wexact_B's text concludes SRr' at the re-hiding relation, the walk's own *)
  refine (HW4 rph ly S Hp W (ms_regs ms) (ms_mem ms) _ ch1 Lam peak c (c + j) 0 _ eq_refl Hcw62
    HFPRE HCL HRL HRP (crs_pre_los_B B ARx CTX0 C Hpre) HWC A10 A11 ltac:(lia) ltac:(rewrite HF0; exact HL) HWR
    ltac:(rewrite HF0; exact HN) _ ltac:(rewrite HF0; exact HRA) ltac:(rewrite HF0; exact HV) (fun a kk => HD (a, kk))
    HD33 HD31 Hfrs _ _ _).
  + reflexivity.
  + right; right. exact Hinf.
  + cbn [Z.eqb negb]. unfold PjWriteHyp.wlen in Hw0. unfold prhWriter_WMAX. lia.
  + unfold RQ_crcs, zmaxl in Hrq. cbn [fold_right] in Hrq. lia.
  + cbn [Z.eqb negb].
    assert (Ebb : blocks_bytes S = blocks_bytes (cb_S C)).
    { rewrite (blocks_bytes_bsum B ly S), (blocks_bytes_bsum B (cb_ly C) (cb_S C)). exact (x3_bsum_perm _ _ HPA). }
    unfold LIVE_check_reject_clean_starved, PRH_FnPj.LIVE_pj_parse, LIVE_pj_write in Hlive |- *.
    assert (Hhp : 0 <= hpeakR (PRH_FnPj.prhPj_ptrace (cb_tb C))) by (destruct (PRH_FnPj.prhPj_ptrace (cb_tb C)); cbn [hpeakR]; lia).
    pose proof cf_head_nonneg as Ch.
    assert (Hnc : forall x, 0 <= WriterSpec.newcap 0 x).
    { intros x. unfold WriterSpec.newcap. cbn [Z.eqb].
      assert (G : forall f c0, 0 <= c0 -> 0 <= WriterSpec.dbl f c0 x).
      { induction f as [|f IH]; intros c0 Hc; cbn [WriterSpec.dbl]; [lia|]. destruct (x <=? c0); [lia|]. apply IH. lia. }
      apply G. lia. }
    pose proof (Hnc (Z.of_nat (length (WriterValue.wdoc (cb_t C) true)) + 1)).
    assert (0 <= cf_head * (Z.of_nat (PjGrammar.calls (PRH_FnPj.prhPj_ptrace (cb_tb C))) + 1)) by (apply Z.mul_nonneg_nonneg; lia).
    rewrite Ebb. lia.
- (* after the call: the refused arm (s7 <- NULL, Lam back, the blocks back) *)
  intros fx' ly2 S2 Hp2 W2 regs2 mem2 md2 k1 HB2 HJ1 HP HQ.
  destruct HQ as (ok & ran' & q & Lam' & peak' & Hoks & R10 & HRL2 & Hgr2 & _ & HN2 & HV2 & HL2 & Harm & Hex).
  destruct (x3_inj_count C ok ran' Hdoc ltac:(lia) ltac:(lia) Hw0 Hw1 Hoks Hgr2) as (Hfl & Hran2 & Hcge & HCE2 & Hc62).
  cbv zeta in Hfl, Hcge, HCE2, Hc62.
  destruct Harm as [(Hfl0 & _) | (_ & Hq0 & ELam & HPA2 & Hpk2)]; [exact (False_ind _ (Hfl Hfl0))|].
  subst q Lam'.
  pose proof HB2 as (_ & _ & _ & HJ2 & _).
  assert (Hpk' : peak <= peak').
  { destruct Hpk2 as [(_ & ->) | (_ & ->)]; lia. }
  assert (Hbl : forall x, In x (ablocks B ly S) -> In x (ablocks B ly2 S2)).
  { intros x Hx. exact (Permutation_in _ (Permutation_sym HPA2) Hx). }
  apply (x3_P2 CTX0 C HK HTF HTL HTR HF HR fx' ly2 S2 Hp2 W2 regs2 mem2 md2 (k + k1) sp2 Lam peak'
    (WriterApp.w_cnt (prhWriter_putN ok (WriterApp.w0 c (c + j)) (WriterValue.wdpieces (cb_t C) false)))
    (WriterApp.w_fail (prhWriter_putN ok (WriterApp.w0 c (c + j)) (WriterValue.wdpieces (cb_t C) false))) ran' HB2);
    [| | exact HCE2 | exact Hc62].
  + apply x3_regsat_app; [exact (x3_regs_pres (rc := rc) _ _ C sp2 HRGm HP) | exact (x3_regsat_one _ _ _ R10)].
  + split; [exact HL2|]. split; [lia|]. split; [exact Hran2|]. split; [exact (Z.le_trans _ _ _ Hcn Hcge)|].
    split; [exact HRL2|].
    split.
    { intros Hrz. destruct (Hex Hrz) as (h & Hh). exists h. rewrite (crs_evs_doc_B C Hdoc), length_app, Nat.add_assoc.
      exact Hh. }
    split; [split; [exact HPL | exact (Permutation_trans HPA2 HPA)]|].
    split.
    * rewrite HF0 in HJ1.
      exact (x3_bytes_keep (fx := fx) B ARx HK WR CTX0 C ly S Hp W mem _ Lam peak c (c + j) 0 _ _ _ _ ly2 S2 Hp2 W2 mem2 md2 k1
        Hpre (proj1 HJ) HL (conj HPL HPA) HJ1 Hbl HBY).
    * intros _. split; [exact HN2|]. split; [exact HD|]. split; [exact HV2|].
      rewrite HF0 in HJ1.
      exact (crs_obj_keepR_B B ARx LAWS WR _ _ ly S Hp W mem _ [] ly2 S2 Hp2 W2 mem2 md2 k1 (cb_doc C) (proj1 HJ) HJ1 HO).
Qed.

(* ---- THE CLOSING LEMMA of row CRB-X3: X3_B (+1072 = 0x82510, fuzz_pick's return site): a0 = cPick0_B = ck_pick tb N0
   (B' reads the pick from the CALL of H3_B; there is no count == s7 arm), `jal fuzz_alloc_fail`, then P1 .. P5 ---- *)
Lemma crs_seg_X3_B : forall CTX0 C
  (HI_head : cf_head = PresetReqAt.HEAD)
  (HT_fuzz_alloc_fail : forall fxq, tfuzz_alloc_fail_specX (fx := fxq) (rc := rc) (PI := prh_img_B) (RL := RL) (PA := PA) B ARx SK)
  (HT_fuzz_alloc_live : forall fxq, tfuzz_alloc_live_specX (fx := fxq) (rc := rc) (PI := prh_img_B) (RL := RL) (PA := PA) B ARx SK)
  (HT_fuzz_alloc_ran_out : forall fxq, tfuzz_alloc_ran_out_specX (fx := fxq) (rc := rc) (PI := prh_img_B) (RL := RL) (PA := PA) B ARx SK)
  (HK : CrsKeep_B B ARx) (HB_took : cb_took C <= 2 ^ 28)
  (HW_exact : forall fxq, crs_wexact_B (fx := fxq) (rc := rc) B ARx CTX0 C),
  crs_from_F_B (fx := fx) (rc := rc) B ARx CTX0 C -> crs_from_R_B (fx := fx) (rc := rc) B ARx CTX0 C ->
  crs_from_X3_B (fx := fx) (rc := rc) B ARx CTX0 C.
Proof.
intros CTX0 C HHD HTF HTL HTR HK HBt HWX HF HR.
unfold crs_from_X3_B. intros fxk ly S Hp W regs mem md k sp2 Lam peak Hdoc HB HRG (HCO & HPM) HBY HT.
destruct HCO as (HL & Hpk & Hran0 & Hcn & Hc62 & HRL & HPOS).
pose proof HB as (Hpre & HFZ & HFK & HJ & HFR & HSV & HSL & HROD & HMN & HR3 & HR4 & Hs1 & Hs2 & Hs3 & HDPk).
pose proof x3_stk as (ESTK & EF0 & EL0 & ER0 & EC0 & EW0).
pose proof crs_frame_is_pi_B as EFR. unfold CRS_FRAME_B in EFR, Hs1.
pose proof (x3_pre_more (fx := fx) B ARx CTX0 C Hpre) as (HCL & HL0 & Hc0 & Hr0 & Htk0 & Hdocs & Hlive & Hrq & Hfr0).
destruct Hdocs as [Hd0 | (Hread & Htree0 & Hw0 & Hw1 & Hdep)]; [exact (False_ind _ (Hdoc Hd0))|].
pose proof (prh_ledger_bounds B _ _ _ _ _ _ _ _ _ _ _ _ HL) as (_ & _ & Hcb & _).
pose proof (crs_wN_pos (cb_t C) false) as N0p.
pose proof (crs_pick_lt (cb_tb C) (cN0_B C) ltac:(unfold cN0_B, PjWriteHyp.wcalls in *; lia)) as Pj.
pose proof (crs_wN_le (cb_t C) false ltac:(lia)) as N0l.
assert (EN0 : cN0_B C = Z.of_nat (length (WriterSpec.grow_calls 0 0 (WriterSpec.piece_lens (WriterValue.wdpieces (cb_t C) false)))))
  by reflexivity.
assert (E10 : getr regs 10 = w64 (cPick0_B C)) by (apply (x3_rget _ _ _ _ HRG); x3_in).
assert (E2 : getr regs 2 = w64 sp2) by (apply (x3_rget _ _ _ _ HRG); x3_in).
assert (E8 : getr regs 8 = w64 (spZ (cb_regs C))) by (apply (x3_rget _ _ _ _ HRG); x3_in).
assert (HRGx : crs_regsat_B regs (x3_regs C sp2)).
{ apply (x3_regsat_sub regs regs _ _ HRG); [|intros; reflexivity].
  intros pp Hpp. unfold x3_regs in *. rewrite !in_app_iff in *. tauto. }
assert (HST : x3_st B C (crs_evs_at_X3_B C) ly S Hp W mem Lam peak (crs_cnt2_B C + cN0_B C) SIZE_MAXZ 0).
{ split; [exact HL|]. split; [exact Hpk|]. split; [reflexivity|]. split; [exact Hcn|]. split; [exact HRL|].
  split; [exact HPOS|]. split; [exact HPM | split; [exact HBY | exact HT]]. }
unfold crs_cfg_B, CRS_PC_X3_B.
assert (HS : @st_ok_pi SEGS VAL fxk (TE (cb_regs C) regs []) (ss_x3 1072)
  (restrict (w_H W) (@YK11.mkst fxk regs (Z_to_bv 64 (BASE + (CRS_PC0_B + 1072))) mem (YK11.seg_rom SEGS)))).
{ apply ts_st_ok; [apply te_regs_ok | reflexivity | constructor | exact I | split; [exact I | split; exact I]]. }
assert (SHOK : sh_ok SEGS (SLit 0) [] (TE (cb_regs C) regs []) (mrestrict (w_H W) mem)) by apply Forall_nil.
assert (HEI : img_env VAL A_LIM (TE (cb_regs C) regs [])) by apply te_env.
unfold crs_JR_B in HJ.
pose (RUN := @paj_run_xR fxk rc SK B_prog_listing PL PA B PST ARx _ LAWS WR WRr WRt).
(* +1072 jal fuzz_alloc_fail (a0 = the pick) *)
paj_run_tok_x RUN HS HJ SHOK (0, 0).
{ cbv [ss_x3 ss_mem]. apply awr_ok_nil. }
apply frame_of_read_only in HF0; [|vm_compute; reflexivity]. clear HFr HG.
rewrite HF0 in HJ.
assert (KR : forall p, In p (x3_regs C sp2) -> getr (ms_regs ms) (fst p) = getr regs (fst p)).
{ intros pp Hpp. cbv [x3_regs crs_rbase_B crs_rsh_B crs_rlive_B crs_rro_B app In] in Hpp.
  repeat (destruct Hpp as [<- | Hpp]; [cbn [fst]; x3_keep HS |]). destruct Hpp. }
assert (KR3 : getr (ms_regs ms) 3 = getr regs 3) by x3_keep HS.
assert (KR4 : getr (ms_regs ms) 4 = getr regs 4) by x3_keep HS.
prreg HS (1%bv : bv 5) Z1.
assert (A1 : getr (ms_regs ms) 1 = Z_to_bv 64 (BASE + (CRS_PC0_B + 1076))).
{ rewrite Z1. f_equal; try (vm_compute; reflexivity). }
assert (A10 : getr (ms_regs ms) 10 = w64 (cPick0_B C)) by (rewrite <- E10; x3_keep HS).
assert (HRGm : crs_regsat_B (ms_regs ms) (x3_regs C sp2)) by exact (x3_regsat_sub regs (ms_regs ms) _ _ HRGx (fun p Hp => Hp) KR).
assert (HBm : crs_baseR_B (fx := fx) B ARx WR CTX0 C fxk ly S Hp W (ms_regs ms) (ms_mem ms)
  (with_vm_backing (m_vm_lazy md) mat md) k sp2).
{ rewrite HF0. exact (x3_base_md (fx := fx) B ARx WR CTX0 C fxk ly S Hp W regs mem md k sp2 (ms_regs ms) _ HB HJ KR3 KR4). }
assert (HSTm : x3_st B C (crs_evs_at_X3_B C) ly S Hp W (ms_mem ms) Lam peak (crs_cnt2_B C + cN0_B C) SIZE_MAXZ 0)
  by (rewrite HF0; exact HST).
unfold cPick0_B in A10.
set (j := ck_pick (cb_tb C) (cN0_B C)) in *. set (cc := crs_cnt2_B C + cN0_B C) in *.
apply (x3_acc_call (fx := fx) B ARx LAWS HK WR WRr WRt WRw CTX0 C (crs_evs_at_X3_B C) fxk (STK_fuzz_alloc_fail (PI := prh_img_B)) 1076 W _ _ ms _
  ly S Hp k sp2 Lam peak cc SIZE_MAXZ 0 (cc + j)
  (fun ly' S' Hp' W' regs' mem' md' =>
     (room_live_cf S -> room_live_cf S') /\
     Hp' = Hp /\ S' = S /\ ablocks B ly' S' = ablocks B ly S /\
     LEDGER ly' S' Hp' W' mem' Lam peak cc (if j <? SIZE_MAXZ - cc then cc + j else SIZE_MAXZ) 0 (cb_most C) 0)
  _ HS eq_refl HBm).
- rewrite (KR (2%bv, sp2)) by x3_in. exact E2.
- rewrite (KR (8%bv, spZ (cb_regs C))) by x3_in. exact E8.
- exact A1.
- lia.
- reflexivity.
- rewrite EF0. lia.
- rewrite EF0, ESTK. unfold CRS_FRAME_B. rewrite EFR. lia.
- exact HSTm.
- intros ch1 HFPRE.
  exact (HTF fxk ly S Hp W (ms_regs ms) (ms_mem ms) _ ch1 Lam peak cc SIZE_MAXZ 0 j (cb_most C) 0 HFPRE
    ltac:(rewrite HF0; exact HL) A10 ltac:(lia)).
- intros ly2 S2 Hp2 W2 regs2 mem2 md2 (_ & EHp & ES & EAB & HL2).
  replace (if j <? SIZE_MAXZ - cc then cc + j else SIZE_MAXZ) with (cc + j) in HL2
    by (unfold SIZE_MAXZ; destruct (Z.ltb_spec j (2 ^ 64 - 1 - cc)); [reflexivity | lia]).
  exact (conj EHp (conj ES (conj EAB HL2))).
- intros ly2 S2 Hp2 W2 regs2 mem2 md2 k1 HB2 HP _ HST2.
  exact (x3_P1 CTX0 C HTF HTL HTR HHD HK HBt HWX HF HR fxk ly2 S2 Hp2 W2 regs2 mem2 md2 (k + k1) sp2 Lam peak Hdoc Hc62 HB2
    (x3_regs_pres (rc := rc) _ _ C sp2 HRGm HP) HST2).
Qed.

End f.
End d.
(* INSTANCE WITNESS of HI_head (the internal file PART7-ROWS.md, unit ruling 16:45Z): at the preset CfParams instance the head is the
   model's PresetReqAt.HEAD *)
Lemma crs_seg_X3_B_HI_head_preset : @cf_head CfParams_preset = PresetReqAt.HEAD.
Proof. reflexivity. Qed.

Print Assumptions crs_seg_X3_B.
Print Assumptions crs_seg_X3_B_HI_head_preset.
