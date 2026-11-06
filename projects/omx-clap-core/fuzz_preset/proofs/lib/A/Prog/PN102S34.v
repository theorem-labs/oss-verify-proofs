(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* omx-clap-core/fuzz_preset, image A' (asan, harness fix #102, pin sha256
   1be0f53d96cb9d6c2d5c92820c254e9db28e4830054a02631390e27c9547dc44): SEGMENTS S3 and S4 of the walk of parse_noting
   (row N10-PNA; cut table lib/A/Prog/PN102Cuts.v):
     S3  +0x3c mv s2,a0; +0x40 jal fuzz_alloc_ran_out (its batch-kit text tfuzz_alloc_ran_out_specX, owner a Theorem Labs lane, no
         wild site, a plain text: PN102Help.v pn_call at the caller's budget pn_cw X and at the cut's relation
         YA0nH.wle' segs RZ_cf, since the walk has crossed pj_parse, which frees); cut_S3 -> cut_S4; the callee keeps
         the astate, so the hull use pn_hull X S' moves to the return by rewriting;
     S4  +0x44 beqz a0, +0x58: cut_S4 -> cut_S5 (g_ran_out <> 0) \/ cut_S6 (g_ran_out = 0); the frame at wle' and
         the hull use are kept.
   rule 24: proves function parse_noting (reuse search: `proof-index parse_noting` exit 4 at 2026-10-30 07:2xZ,
   index v5 06:36:24Z: 0 named / 0 by address / 0 related / 0 released; the unreleased hits are this lane's own N10-PNA
   files and the plain / UBSan / B' twins; R24Pna CONFIRM 2026-10-29 18:2xZ; own signed walk preset-tree-at-2026-10-29T20-00-00Z.tsv (sha256 84c0bfddb1f3; internal record), its one
   announced re-bind). This file: segments S3 and S4 of that walk.
   THE BATCH KIT'S RE-BIND: a Theorem Labs lane's signed A' file of the same role (a working branch 13970867e0c9),
   re-fit to the batch kit's cut (commit 7cdbb61b5fa0) as the B' twin was re-fit
   (a working branch c7276d935095 lib/B/Prog/PN102B<same role>.v, read back at PI_prog_A / prh_img_A).
   NUMERALS: the instruction offsets (LENGTH), 48 (the frame). No ADDRESS. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK1d YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn YP0b YP0a.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YN3v YI04 YI00 YG0s YP07.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq YM05 YI16 YG0p YCbqG YCbqGcall.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YP0d YP0c YC80 YPsym YC4aP YC1fP YC80x YC1fPx YImgTop.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YGcfNames YG01cf YG00cf YG0ncf YG0dcf YG0lawscf YGcallcf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YAkMemnorm.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Base.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import Listing_prog PAImg_prog PRH_Img.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import CfParamsPreset PRH_FnAlloc.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require Import PN102Cuts PN102Help PN102Keep.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YA0nH.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcfRehidePost.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Set Warnings "-notation-for-abbreviation".
Open Scope bv_scope.
Open Scope Z_scope.

Section I. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {SK : YI16.sink_head}.
#[local] Existing Instance CfParams_preset.
#[local] Existing Instance prh_img_A.
#[local] Abbreviation CP := CfParams_preset.
#[local] Abbreviation PA := (@PI_prog_A rc).
#[local] Abbreviation SEGS := (@pa_segs rc A_prog_listing PA).
#[local] Abbreviation BASE := (@pa_val rc A_prog_listing PA A_TEXT).
#[local] Abbreviation SIGMA := (@pa_sigma rc A_prog_listing PA).
#[local] Abbreviation PST := (@prh_pst prh_img_A).
#[local] Abbreviation RL := (prh_room_live_a8 (cp := CP)).
Variable B : asyms.
#[local] Abbreviation ARc := (fun ly S Hp (W : world SEGS) mem md =>
  ARcf (cp := CP) SEGS B ly S Hp W mem md /\ xs_placed_cf ly S).
Let LAWS : AR_laws_x SEGS B ARc (@cf_head CP) := AR_laws_x_xs (cp := CP) SEGS B (AR_laws_ok_cf (cp := CP) SEGS B).
#[local] Abbreviation Hsegs := (@pa_segs_low rc A_prog_listing PA).

(* registers across a write *)
Lemma pn_getr_upd_other : forall regs (rd r : bv 5) v, r <> rd -> getr (regupd regs rd v) r = getr regs r.
Proof. intros regs rd r v H. unfold getr. destruct (bv_eqb r 0); [reflexivity|]. apply regupd_other. exact H. Qed.
Lemma pn_getr_upd_same : forall regs (rd : bv 5) v, bv_eqb rd 0 = false -> getr (regupd regs rd v) rd = v.
Proof. intros regs rd v H. unfold getr. rewrite H. apply regupd_same. Qed.
Lemma pn_cs_upd : forall regs (rd : bv 5) v r, acallee_saved r -> Z_to_bv 5 r <> rd ->
  getr (regupd regs rd v) (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r).
Proof. intros regs rd v r _ H. apply pn_getr_upd_other. exact H. Qed.

(* ---------------------------------------------------------------------- *)
(* S4: the branch *)
Theorem pn_seg_S4 : forall CTX0,
  pn_seg_S4_stmt (fx := fx) (RL := RL) (PA := PA) B ARc SK CTX0.
Proof.
intros CTX0 X W' c HPRE
  (fy & regs & mem & md & ly & S & Hp & k & Lam' & peak' & cnt' & fail' & ran' & ok & res & tr &
   Ec & HF & R8 & R9 & R10 & HH & HRM & HR).
subst c. rewrite pn_cfg_eq.
pose proof pn_slot0_range as [Hs0 Hs1].
pn_fd (PN_SLOT0 + PN_S4) Hpl Hd.
eapply (pn_step_branch (fx := fy) W' regs mem md _ (PN_SLOT0 + PN_S4) _ (PN_SLOT0 + PN_S6) _ _ _ _
  ltac:(unfold PN_S4, PN_RET in *; lia) ltac:(unfold PN_S6, PN_RET in *; lia) Hpl Hd ltac:(vm_compute; reflexivity)).
- intros Hc Xm. apply SRr_ret. right.
  exists fy, regs, mem, (with_vm_backing (m_vm_lazy md) Xm md), ly, S, Hp, k, Lam', peak', cnt', fail', ran', ok, res, tr.
  split; [rewrite pn_cfg_eq; reflexivity|].
  split; [apply (pn_frame_stepR B LAWS (wle' SEGS YGcfRehidePost.RZ_cf) X fy W' regs regs mem md Xm ly S Hp k _ HF);
    intros; reflexivity|].
  split; [exact HH|]. split; [exact HRM | exact HR].
- intros Hc Xm. apply SRr_ret. left.
  exists fy, regs, mem, (with_vm_backing (m_vm_lazy md) Xm md), ly, S, Hp, k, Lam', peak', cnt', fail', ran', ok, res, tr.
  split; [rewrite pn_cfg_eq; reflexivity|].
  split; [apply (pn_frame_stepR B LAWS (wle' SEGS YGcfRehidePost.RZ_cf) X fy W' regs regs mem md Xm ly S Hp k _ HF);
    intros; reflexivity|].
  split; [exact R8|]. split; [exact R9|].
  split.
  { intros E. subst ran'. apply Bool.diff_false_true. rewrite <- Hc.
    lazymatch goal with |- branch_taken ?cc (getr regs ?r1) _ = _ =>
      replace (getr regs r1) with (w64 0) by (rewrite <- R10; f_equal; apply bv_eq; reflexivity) end.
    vm_compute. reflexivity. }
  split; [exact HH|]. split; [exact HRM | exact HR].
Qed.

(* registers by their unsigned index *)
Lemma pn_getr_eq : forall regs (r r' : bv 5), bv_unsigned r = bv_unsigned r' -> getr regs r = getr regs r'.
Proof. intros regs r r' H. apply bv_eq in H. subst r'. reflexivity. Qed.
Lemma pn_getr_upd_eq : forall regs (rd r : bv 5) v, bv_unsigned rd = bv_unsigned r -> bv_eqb rd 0 = false ->
  getr (regupd regs rd v) r = v.
Proof. intros regs rd r v H Hz. apply bv_eq in H. subst r. apply pn_getr_upd_same. exact Hz. Qed.
Lemma pn_getr_upd_ne : forall regs (rd r : bv 5) v, bv_unsigned rd <> bv_unsigned r ->
  getr (regupd regs rd v) r = getr regs r.
Proof. intros regs rd r v H. apply pn_getr_upd_other. intros E. subst r. exact (H eq_refl). Qed.
Lemma pn_cs_upd_ne : forall regs (rd : bv 5) v r, acallee_saved r -> bv_unsigned rd <> r ->
  getr (regupd regs rd v) (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r).
Proof.
intros regs rd v r Hr Hne. apply pn_getr_upd_ne. rewrite Z_to_bv_unsigned. unfold bv_wrap.
change (bv_modulus 5) with 32. unfold acallee_saved in Hr. rewrite Z.mod_small by lia. exact Hne.
Qed.
Ltac pn_regs := first [ reflexivity | vm_compute; reflexivity | vm_compute; congruence | vm_compute; lia ].

(* ---------------------------------------------------------------------- *)
(* S3: mv s2,a0; jal fuzz_alloc_ran_out *)
Theorem pn_seg_S3 : forall CTX0,
  pn_seg_S3_stmt (fx := fx) (RL := RL) (PA := PA) B ARc SK CTX0.
Proof.
intros CTX0 HT X W' c HPRE
  (fy & regs & mem & md & ly & S & Hp & k & Lam' & peak' & cnt' & fail' & ran' & ok & res & tr &
   Ec & HF & R8 & R9 & HH & HRM & HR).
subst c. rewrite pn_cfg_eq.
pose proof pn_slot0_range as [Hs0 Hs1].
pose proof (pp_fpre _ _ _ _ HPRE) as ((HAR0 & Hra0 & Hra40 & Hgp0 & Htp0 & Hstk0 & Hpres0 & Hch0 & HQT0) & HRO0 & HSH0 & HRAM0).
pose proof (pp_out _ _ _ _ HPRE) as (_ & (Hd0 & Hdceil & _)).
let v := eval vm_compute in (@STK_parse_noting prh_img_A) in
assert (EST : @STK_parse_noting prh_img_A = v) by (vm_compute; reflexivity).
let v := eval vm_compute in (@STK_fuzz_alloc_ran_out prh_img_A) in
assert (ESR : @STK_fuzz_alloc_ran_out prh_img_A = v) by (vm_compute; reflexivity).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
(* +0x3c mv s2,a0 *)
pn_fd (PN_SLOT0 + PN_S3) Hpl1 Hd1.
eapply (pn_step_addi (fx := fy) W' regs mem md _ (PN_SLOT0 + PN_S3) _ _ _ _ _ _
  ltac:(unfold PN_S3, PN_RET in *; lia) Hpl1 Hd1); [reflexivity | reflexivity | reflexivity | intros X1].
(* +0x40 jal fuzz_alloc_ran_out *)
pn_fdc (PN_SLOT0 + PN_S3 + 4) Hpl2.
eapply (pn_step_call (fx := fy) W' _ mem _ _ (PN_SLOT0 + PN_S3 + 4) _ _ _
  ltac:(unfold PN_S3, PN_RET in *; lia) Hpl2 eq_refl).
intros X2.
lazymatch goal with |- SRr _ _ (mkCfg (@YK11.mkst _ (regupd (regupd regs ?a ?b) ?c ?d) _ _ _) ?m2) _ =>
  set (regs1 := regupd regs a b); set (regs2 := regupd regs1 c d); set (md2 := m2) end.
assert (G18 : getr regs1 18 = getr regs 10).
{ unfold regs1. rewrite pn_getr_upd_eq by pn_regs.
  lazymatch goal with |- v_addi (getr regs ?r) ?i = _ =>
    replace i with 0 by pn_regs; rewrite (pn_getr_eq regs r 10) by pn_regs end.
  apply v_addi_0. }
assert (G1 : getr regs2 1 = Z_to_bv 64 (BASE + (PN_SLOT0 + PN_S3 + 4 + 4))) by (unfold regs2; apply pn_getr_upd_eq; pn_regs).
assert (GCS : forall r, acallee_saved r -> r <> 18 -> getr regs2 (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r)).
{ intros r Hr H18. unfold regs2. rewrite pn_cs_upd_ne by (try exact Hr; unfold acallee_saved in Hr; vm_compute; lia).
  unfold regs1. rewrite pn_cs_upd_ne by (try exact Hr; unfold acallee_saved in Hr; vm_compute; lia). reflexivity. }
assert (HF2 : pn_frameR (fx := fx) (PI := prh_img_A) (PA := PA) B ARc SK (wle' SEGS YGcfRehidePost.RZ_cf) X fy W'
  regs2 mem md2 ly S Hp k (pn_cw (PI := prh_img_A) (PA := PA) B X)).
{ unfold md2.
  apply (pn_frame_stepR B LAWS (wle' SEGS YGcfRehidePost.RZ_cf) X fy W' regs1 regs2 mem _ X2 ly S Hp k _).
  - apply (pn_frame_stepR B LAWS (wle' SEGS YGcfRehidePost.RZ_cf) X fy W' regs regs1 mem md X1 ly S Hp k _ HF).
    intros r Hr H8 H9 H18 H19. unfold regs1. apply pn_cs_upd_ne; [exact Hr|]. vm_compute. lia.
  - intros r Hr H8 H9 H18 H19. unfold regs2. apply pn_cs_upd_ne; [exact Hr|]. vm_compute. unfold acallee_saved in Hr. lia. }
pose proof HF2 as (HJ2 & Hsp2 & _ & _ & _ & _ & _ & Hcs2 & Hfrm2 & Hfk2 & Hmn2 & Hro2).
pose proof (ajxR_ly HJ2) as Hly2. pose proof (ajxR_stk HJ2) as Hstk2.
pose proof Hstk2 as (Hal16 & Hstk02 & Hceil2 & Hslo2 & Hshi2 & H472 & Hbot2 & Htop2' & Htop22).
assert (Eshi : ly_stk_hi ly = ly_stk_hi (px_ly X)).
{ destruct Hly2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Eshi & _). exact Eshi. }
unfold PN_FRAME in Hsp2.
change (mkCfg (@YK11.mkst fy regs2 (Z_to_bv 64 (SIGMA AS_fuzz_alloc_ran_out)) mem (YK11.seg_rom SEGS)) md2)
  with (cfg_at (fx := fy) SEGS (SIGMA AS_fuzz_alloc_ran_out) regs2 mem md2).
eapply (pn_call (fx := fy) (SK := SK) SEGS B PST ARc LAWS Hsegs (wle' SEGS YGcfRehidePost.RZ_cf)
  (wle_wle' SEGS YGcfRehidePost.RZ_cf) (wle'_trans SEGS YGcfRehidePost.RZ_cf) W' regs2 mem md2 STK_parse_noting
  (spZ (px_regs X)) [(px_doc X, px_doc X + 56)] (px_ly X) (px_S X) (px_Hp X) (px_W X) (px_mem X) (px_md X) [] ly S Hp k
  _ (@STK_fuzz_alloc_ran_out prh_img_A) [] (-48) [] (SIGMA AS_fuzz_alloc_ran_out) _ _ HJ2).
- lia.
- reflexivity.
- lia.
- rewrite ESR. lia.
- rewrite ESR, EST. lia.
- rewrite G1. apply (ret_ok_codeptr_v (PI := PA)); [unfold PN_S3, PN_RET in *; lia | reflexivity].
- unfold raZ. rewrite G1. apply Z.leb_le. vm_compute. reflexivity.
- transitivity (getr regs2 (Z_to_bv 5 3)); [apply pn_getr_eq; pn_regs|].
  rewrite (Hcs2 3 ltac:(unfold acallee_saved; lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)).
  rewrite <- Hgp0. apply pn_getr_eq. pn_regs.
- transitivity (getr regs2 (Z_to_bv 5 4)); [apply pn_getr_eq; pn_regs|].
  rewrite (Hcs2 4 ltac:(unfold acallee_saved; lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)).
  rewrite <- Htp0. apply pn_getr_eq. pn_regs.
- apply achain_low. unfold s0Z.
  rewrite (pn_getr_eq regs2 _ (Z_to_bv 5 8)) by pn_regs.
  rewrite (GCS 8 ltac:(unfold acallee_saved; lia) ltac:(lia)).
  rewrite (pn_getr_eq regs (Z_to_bv 5 8) 8) by pn_regs. rewrite R8. unfold w64.
  rewrite unsigned_lit_small by lia. lia.
- intros HPRE1. pose proof (pnR_ledger B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HR) as HLED.
  refine (HT fy ly S Hp W' regs2 mem md2 [] Lam' peak' cnt' fail' ran' (px_most X) (px_own X)
    (conj HPRE1 (conj Hro2 (conj _ (conj _ Hfrm2)))) HLED).
  + rewrite Hsp2, Eshi. lia.
  + unfold raZ. rewrite G1. pose proof (@ASAN_CEIL_range rc) as [HC _]. unfold ASAN_CEIL in HC.
    let v := eval vm_compute in (bv_unsigned (Z_to_bv 64 (BASE + (PN_SLOT0 + PN_S3 + 4 + 4)))) in
    replace (bv_unsigned (Z_to_bv 64 (BASE + (PN_SLOT0 + PN_S3 + 4 + 4)))) with v by (vm_compute; reflexivity).
    lia.
- exact (pn_fp_sub_nil B _ _ _ _ _ _ _ _).
- intros W2 ly2 S2 Hp2 regs3 mem2 md3 k1 Hle HJc HJ1 HP ((Hrl & R10' & EHp & ES & Eab & HL2) & Hmn3).
  apply SRr_ret.
  exists fy, regs3, mem2, md3, ly2, S2, Hp2, (k + k1), Lam', peak', cnt', fail', ran', ok, res, tr.
  split.
  { rewrite G1, pn_cfg_eq. unfold PN_S3, PN_S4. repeat f_equal; lia. }
  assert (HJ1' : ajournal_x (SK := SK) SEGS B PST ARc (@STK_fuzz_alloc_ran_out prh_img_A) (spZ regs2) []
      ly S Hp W' mem md2 [] ly2 S2 Hp2 W2 mem2 md3 k1).
  { rewrite Hsp2. replace (spZ (px_regs X) - 48) with (spZ (px_regs X) + -48) by lia. exact HJ1. }
  assert (P2 : forall r, acallee_saved r -> r <> 18 ->
      getr regs3 (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r)).
  { intros r Hr H18. rewrite (pn_pres regs2 regs3 r HP Hr). exact (GCS r Hr H18). }
  split; [exact (pn_frame_call B (wle' SEGS YGcfRehidePost.RZ_cf) (wle' SEGS YGcfRehidePost.RZ_cf) (@wle SEGS)
             X fy W' regs2 mem md2 ly S Hp k _ fy W2 regs3 mem2 md3 ly2 S2 Hp2 k1 [] _ _ []
             HF2 HJc HJ1' pn_sink_nil HP Hfrm2 (pn_fregs_refl fy) Hmn3)|].
  split.
  { rewrite (pn_getr_eq regs3 _ (Z_to_bv 5 8)) by pn_regs. rewrite (P2 8 ltac:(unfold acallee_saved; lia) ltac:(lia)).
    rewrite (pn_getr_eq regs (Z_to_bv 5 8) 8) by pn_regs. exact R8. }
  split.
  { rewrite (pn_getr_eq regs3 _ (Z_to_bv 5 9)) by pn_regs. rewrite (P2 9 ltac:(unfold acallee_saved; lia) ltac:(lia)).
    rewrite (pn_getr_eq regs (Z_to_bv 5 9) 9) by pn_regs. exact R9. }
  split; [exact R10'|].
  split; [rewrite ES; exact HH|].
  split; [rewrite ES; exact HRM|].
  assert (G18' : getr regs3 18 = getr regs 10).
  { rewrite (pn_getr_eq regs3 _ (Z_to_bv 5 18)) by pn_regs.
    rewrite (pn_pres regs2 regs3 18 HP ltac:(unfold acallee_saved; lia)).
    unfold regs2. rewrite pn_cs_upd_ne by (unfold acallee_saved; lia || (vm_compute; lia)).
    rewrite (pn_getr_eq regs1 (Z_to_bv 5 18) 18) by pn_regs. exact G18. }
  rewrite G18'.
  exact (pn_R_keep B LAWS (wle' SEGS YGcfRehidePost.RZ_cf) CTX0 X ly S Hp W' mem md2 k _ Lam' peak' cnt' fail' ran'
    ok res tr (getr regs 10) _ (spZ regs2) ly2 S2 Hp2 W2 mem2 md3 k1 HPRE HJ2 HR HJ1' ES Eab HL2).
Qed.
End I.
