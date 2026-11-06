(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* omx-clap-core/fuzz_preset, image A' (asan, harness fix #102, pin sha256
   1be0f53d96cb9d6c2d5c92820c254e9db28e4830054a02631390e27c9547dc44): SEGMENT S5 of the walk of parse_noting (row
   N10-PNA; cut table lib/A/Prog/PN102Cuts.v): from pn_cut_S5 (+0x48, the reading ran out) to pn_cut_S6 (+0x58).
   The slots, read on the listing (lib/A/Listing_prog.v, parse_noting's slots 607 .. 610): +0x48 mv a0,s2;
   +0x4c mv a1,s0; +0x50 mv a2,s1; +0x54 jal check_reject_clean.
   rule 24: proves function parse_noting (reuse search: `proof-index parse_noting` exit 4 at 2026-10-30 07:2xZ,
   index v5 06:36:24Z: 0 named / 0 by address / 0 related / 0 released; the unreleased hits are this lane's own N10-PNA
   files and the plain / UBSan / B' twins; R24Pna CONFIRM 2026-10-29 18:2xZ; own signed walk preset-tree-at-2026-10-29T20-00-00Z.tsv (sha256 84c0bfddb1f3; internal record), its one
   announced re-bind). This file: segment S5 of that walk.
   THE BATCH KIT'S RE-BIND: a Theorem Labs lane's signed A' file of the same role (a working branch 13970867e0c9),
   re-fit to the batch kit's cut (commit 7cdbb61b5fa0) as the B' twin was re-fit
   (a working branch c7276d935095 lib/B/Prog/PN102B<same role>.v, read back at PI_prog_A / prh_img_A).
   FORM: three concrete steps (PN102Help.v pn_step_addi), the jal (pn_step_call), the batch kit's text tcheck_reject_clean_specX
   at the cut's float state applied by PN102Help.v pn_call (o = -48 from the entry sp, footprint [], ch = [] since
   s0 = doc is below the ceiling; the caller's journal at the budget pn_cw X and at the cut's world relation
   wle' segs RZ_cf, since the walk crossed pj_parse, which frees; the callee is a plain text at wle). The text's
   premises: rc = -1 (the reading ran out, so pn_R gives res = None and r10 = -1), a1 = doc, src_rd of doc's 56 zero
   bytes (pj_zeroR; the batch kit's src_rd asks doc + 56 <= alloc_ceiling, which pp_out's wdest_ok gives - the signed walk's FIX
   (5) F6 is retired), a2 = live = lsum of the entry ledger list, which the refused reading's ledger list permutes. The
   return lands in pn_cut_S6 by PN102Keep.v pn_frame_call and pn_R_keep; the hull use pn_hull moves unchanged, since
   the callee keeps the astate (its post states S' = S).
   DOC'S SHADOW (pn5_doc_keptR / pn5_doc_addressableR / pn5_doc_hullR, over the journal from the entry at any world
   relation R, since S5 runs after pj_parse, at wle' segs RZ_cf; standalone for the other segments): doc's 56
   bytes lie in a fake frame live at entry (pp_out's ck_in_frame), whose address and size are 64-aligned at ARcf
   (YG0scf.v frame_facts_cf), so the 64-byte-aligned shadow hull of [doc, doc + 56) lies in that frame's shadow; the
   journal from the entry keeps those bytes (its frames clause, the shadow is off the footprint), so the entry's
   range_addressable and shadow_hull_vis (pp_out's wdest_ok) hold at the current state.
   SHAPES TAKEN: pn5_fd is lib/A/Prog/Ent102L3ASteps.v l3_fd (a working branch b1bc025047ea) at PL_prog_A;
   pn5_lsum_perm is lib/A/Prog/S1Ledger.v prh_lsum_perm; the call is shaped as Ent102L2A.v l2_pno (same branch).
   NUMERALS: 4 (an instruction), 8 (a word, a shadow granule), 48 (the frame), 56 (struct pj), 64 (the shadow hull
   and frame alignment), 4096 (a page), 2 ^ 31 (int range), 2 ^ 40 (the engine's code span), the instruction offsets
   0x48 .. 0x58 (LENGTH). No ADDRESS. *)
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
YGcfNames YG01cf YG00cf YG0ncf YG0dcf YG0lawscf YGcallcf YG0scf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YAkMemnorm.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YA0nH.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcfRehidePost.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Ledger.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Base.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import Listing_prog PAImg_prog PRH_Img.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Reader PRH_FnCheck.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import CfParamsPreset.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require Import PN102Cuts PN102Help PN102Keep.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Set Warnings "-notation-for-abbreviation".
Open Scope bv_scope.
Open Scope Z_scope.

(* ---------------------------------------------------------------------- *)
(* 1. Tactics and pure facts. *)
Ltac pn5_fd k ins Hpl Hd :=
  let r := eval vm_compute in (plookup (@pl_tpi _ PL_prog_A) k) in
  lazymatch r with
  | Some (PW ?w) =>
    assert (Hpl : plookup (@pl_tpi _ PL_prog_A) k = Some (PW w)) by (vm_compute; reflexivity);
    assert (Hd : decode_any (Z_to_bv 32 w) = Some (ins, 4%Z)) by vm_refl_bv
  | _ => fail "pn5_fd: no plain word at offset" k
  end.
Ltac pn5_gr := repeat first [rewrite getr_same by pn_regne | rewrite getr_other by pn_regne].

Lemma pn5_lsum_perm : forall l l', Permutation l l' -> Ledger.lsum l = Ledger.lsum l'.
Proof.
intros l l' H. induction H as [|[a k] l l' H IH|[a k] [a' k'] l|l l' l'' H1 IH1 H2 IH2]; cbn [Ledger.lsum]; lia.
Qed.

(* a write to a register that is not callee-saved keeps every callee-saved one (pn_frame_step's premise) *)
Lemma pn5_upd_cs : forall regs (rd : bv 5) v n, bv_unsigned rd = n -> ~ acallee_saved n ->
  forall r, acallee_saved r -> r <> 8 -> r <> 9 -> r <> 18 -> r <> 19 ->
  getr (regupd regs rd v) (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r).
Proof.
intros regs rd v n En Hn r Hr _ _ _ _. apply getr_other. intros E. apply Hn. rewrite <- En, <- E.
rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 5) with 32.
unfold acallee_saved in *. rewrite Z.mod_small by lia. exact Hr.
Qed.

(* a 4096-aligned base plus a 64-aligned offset is 64-aligned *)
Lemma pn5_mod64 : forall a b, a mod 4096 = 0 -> b mod 64 = 0 -> (a + b) mod 64 = 0.
Proof.
intros a b Ha Hb.
apply (proj1 (Z.mod_divide a 4096 ltac:(lia))) in Ha. apply (proj1 (Z.mod_divide b 64 ltac:(lia))) in Hb.
apply (proj2 (Z.mod_divide (a + b) 64 ltac:(lia))). destruct Ha as (x & ->). destruct Hb as (y & ->).
exists (64 * x + y). lia.
Qed.

(* the 64-byte-aligned shadow hull of [doc, doc + 56) inside a 64-aligned frame [fa, fa + fsb) is in its shadow *)
Lemma pn5_hull_in : forall fa fsb doc s, fa mod 64 = 0 -> fsb mod 64 = 0 -> fa <= doc -> doc + 56 <= fa + fsb ->
  shadow_addr doc / 8 * 8 <= s < shadow_addr (doc + 56 - 1) / 8 * 8 + 8 ->
  in_zr s (shadow_addr fa, fsb / 8).
Proof.
intros fa fsb doc s Hfa Hfsb H1 H2 Hs. unfold in_zr, shadow_addr, SHADOW_OFF in *. cbn [fst snd].
Z.div_mod_to_equations. lia.
Qed.

(* that hull is off doc's own bytes *)
Lemma pn5_hull_fp : forall doc s, amem_range doc 56 ->
  shadow_addr doc / 8 * 8 <= s < shadow_addr (doc + 56 - 1) / 8 * 8 + 8 -> ~ (doc <= s < doc + 56).
Proof.
intros doc s Ham Hs. unfold amem_range, shadow_addr, SHADOW_OFF, kLowMemEnd, kHighMemBeg, kHighMemEnd in *.
Z.div_mod_to_equations. lia.
Qed.

(* the shadow byte of a byte of [doc, doc + 56) is in the hull *)
Lemma pn5_addr_in_hull : forall doc x, doc <= x < doc + 56 ->
  shadow_addr doc / 8 * 8 <= shadow_of_addr SHADOW_OFF x < shadow_addr (doc + 56 - 1) / 8 * 8 + 8.
Proof. intros doc x Hx. unfold shadow_of_addr, shadow_addr, SHADOW_OFF. Z.div_mod_to_equations. lia. Qed.

(* ---------------------------------------------------------------------- *)
(* 2. At the A' instance: doc's shadow at any state the journal from the entry reaches, and the segment. *)
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
(* the world relation of the cuts after pj_parse (PN102Cuts.v pn_cut_S5 / pn_cut_S6): pj_parse frees *)
#[local] Abbreviation WR := (wle' SEGS YGcfRehidePost.RZ_cf).

(* doc lies in a live frame of the entry, at or above 4096 (ARx_sep_law at the entry) *)
Lemma pn5_doc_low : forall CTX0 X, pn_pre (fx := fx) (RL := RL) (PA := PA) B ARc CTX0 X -> 4096 <= px_doc X.
Proof.
intros CTX0 X HPRE.
pose proof (pp_fpre _ _ _ _ HPRE) as ((HAR0 & _) & _).
destruct (pp_out _ _ _ _ HPRE) as ((cid & pos & Hfin & Hd0 & _) & _).
destruct (alx_sep SEGS B ARc LAWS _ _ _ _ _ _ HAR0) as (_ & HF).
pose proof (proj1 (Forall_forall _ _) HF (cid, pos) Hfin) as (H4096 & _). cbn [fst snd] in H4096. lia.
Qed.

(* the bytes of doc's shadow hull are kept by the journal from the entry (at any budget, over any world relation R:
   only the journal's frames clause is read) *)
Lemma pn5_doc_keptR : forall (R : world SEGS -> world SEGS -> Prop) CTX0 X ly S Hp (W : world SEGS) mem md k WS s,
  pn_pre (fx := fx) (RL := RL) (PA := PA) B ARc CTX0 X ->
  ajournal_xwR (SK := SK) SEGS B PST ARc R STK_parse_noting (spZ (px_regs X)) [(px_doc X, px_doc X + 56)]
    (px_ly X) (px_S X) (px_Hp X) (px_W X) (px_mem X) (px_md X) [] ly S Hp W mem md k WS ->
  shadow_addr (px_doc X) / 8 * 8 <= s < shadow_addr (px_doc X + 56 - 1) / 8 * 8 + 8 ->
  aview SEGS (w_H W) mem s = aview SEGS (w_H (px_W X)) (px_mem X) s.
Proof.
intros R CTX0 X ly S Hp W mem md k WS s HPRE HJ Hs.
pose proof (pp_fpre _ _ _ _ HPRE) as ((HAR0 & _) & _).
destruct HAR0 as ((HM0 & _) & _).
destruct (pp_out _ _ _ _ HPRE) as ((cid & pos & Hfin & Hd0 & Hd1) & (_ & _ & Wam & _)).
pose proof (ajxR_frm HJ) as F4.
pose proof (frame_facts_cf B _ _ _ _ cid pos HM0 Hfin) as (_ & _ & _ & _ & Hpg & _ & _ & Hoff & _ & Hfsb & _).
apply (F4 cid pos s Hfin).
- right. apply (pn5_hull_in (frame_addr (px_ly X) cid pos) (fs_frame_bytes cid) (px_doc X) s);
    [| exact Hfsb | exact Hd0 | exact Hd1 | exact Hs].
  unfold frame_addr. unfold page_aligned in Hpg. exact (pn5_mod64 _ _ Hpg Hoff).
- intros Hfp. apply (proj1 (inFP_cons _ _ _ _)) in Hfp. destruct Hfp as [Hfp | Hfp]; [|exact (inFP_nil _ Hfp)].
  exact (pn5_hull_fp (px_doc X) s Wam Hs Hfp).
Qed.

(* doc's 56 bytes are addressable at any state the journal from the entry reaches (over any world relation R) *)
Lemma pn5_doc_addressableR : forall (R : world SEGS -> world SEGS -> Prop) CTX0 X ly S Hp (W : world SEGS) mem md k WS,
  pn_pre (fx := fx) (RL := RL) (PA := PA) B ARc CTX0 X ->
  ajournal_xwR (SK := SK) SEGS B PST ARc R STK_parse_noting (spZ (px_regs X)) [(px_doc X, px_doc X + 56)]
    (px_ly X) (px_S X) (px_Hp X) (px_W X) (px_mem X) (px_md X) [] ly S Hp W mem md k WS ->
  range_addressable (aview SEGS (w_H W) mem) SHADOW_OFF (px_doc X) 56.
Proof.
intros R CTX0 X ly S Hp W mem md k WS HPRE HJ x Hx.
destruct (pp_out _ _ _ _ HPRE) as (_ & (_ & _ & _ & _ & Wra & _)).
destruct (Wra x Hx) as (sv & Hsv & Hok). exists sv. split; [|exact Hok].
rewrite (pn5_doc_keptR R CTX0 X ly S Hp W mem md k WS _ HPRE HJ (pn5_addr_in_hull _ x Hx)). exact Hsv.
Qed.

(* doc's 64-byte-aligned shadow hull is visible at any state the journal from the entry reaches (over any world
   relation R) *)
Lemma pn5_doc_hullR : forall (R : world SEGS -> world SEGS -> Prop) CTX0 X ly S Hp (W : world SEGS) mem md k WS,
  pn_pre (fx := fx) (RL := RL) (PA := PA) B ARc CTX0 X ->
  ajournal_xwR (SK := SK) SEGS B PST ARc R STK_parse_noting (spZ (px_regs X)) [(px_doc X, px_doc X + 56)]
    (px_ly X) (px_S X) (px_Hp X) (px_W X) (px_mem X) (px_md X) [] ly S Hp W mem md k WS ->
  shadow_hull_vis (aview SEGS (w_H W) mem) (px_doc X) 56.
Proof.
intros R CTX0 X ly S Hp W mem md k WS HPRE HJ s Hs.
destruct (pp_out _ _ _ _ HPRE) as (_ & (_ & _ & _ & _ & _ & Whv)).
rewrite (pn5_doc_keptR R CTX0 X ly S Hp W mem md k WS s HPRE HJ Hs). exact (Whv ltac:(lia) s Hs).
Qed.

Theorem pn_seg_S5 : forall CTX0,
  pn_seg_S5_stmt (fx := fx) (cp := CP) (PI := prh_img_A) (RL := prh_room_live_a8 (cp := CP)) (PA := PA) B ARc SK CTX0.
Proof.
intros CTX0. unfold pn_seg_S5_stmt.
intros HT X W c HPRE Hcut.
unfold pn_cut_S5 in Hcut.
destruct Hcut as (fy & regs & mem & md & ly & S & Hp & k & Lam & peak & cnt & fail & ran & ok & res & tr
  & -> & HF & R8 & R9 & Hran & Hhull & Hroom & HR).
(* the entry's facts *)
pose proof (pp_fpre _ _ _ _ HPRE) as ((_ & _ & _ & Hgp0 & Htp0 & _) & _ & Hhi0 & _).
(* doc's 56 bytes end at or below the ceiling (pp_out's wdest_ok; the batch kit's src_rd bounds p + len only) *)
destruct (pp_out _ _ _ _ HPRE) as (_ & (Wd0 & Hdocc & Wam & _)).
pose proof (pn5_doc_low CTX0 X HPRE) as Hdoc4.
pose proof alloc_ceiling_val as (Hceil & _).
(* the cut's frame *)
pose proof HF as (HJ & Hsp & _ & _ & _ & _ & _ & Hcs & Hfz & Hfk & Hmn & Hro).
pose proof (ajxR_ly HJ) as Hly.
destruct Hly as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstkhi & _).
unfold PN_FRAME in Hsp.
(* the reading ran out: res = None, a0 = -1, the ledger list a permutation of the entry's, doc zero *)
pose proof (pnR_ledger B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HR) as HLED.
assert (Hres : res = None) by exact (pnR_ran_none B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HR Hran). subst res.
destruct (pnR_none B _ _ _ _ _ _ _ _ _ _ _ _ _ _ HR) as (H18 & HPL & _ & HZ).
(* the image's numbers *)
pose proof pn_slot0_range as (R0 & R1). unfold PN_RET in R1.
pose proof (@pa_B_ok rc A_prog_listing PA) as (HB0 & HB1 & _).
let v := eval vm_compute in BASE in assert (EB : BASE = v) by (vm_compute; reflexivity).
let v := eval vm_compute in PN_SLOT0 in assert (EP : PN_SLOT0 = v) by (vm_compute; reflexivity).
let v := eval vm_compute in (@STK_check_reject_clean prh_img_A) in
  assert (ESTK1 : @STK_check_reject_clean prh_img_A = v) by (vm_compute; reflexivity).
let v := eval vm_compute in (@STK_parse_noting prh_img_A) in
  assert (ESTK : @STK_parse_noting prh_img_A = v) by (vm_compute; reflexivity).
rewrite (pn_cfg_eq fy PN_S5 regs mem md).
(* +0x48 mv a0,s2 *)
pn5_fd (PN_SLOT0 + PN_S5) (OpImm ALU_ADD 10 18 (Z_to_bv 12 0)) Hpl1 Hd1.
apply (pn_step_addi (fx := fy) W regs mem md _ (PN_SLOT0 + PN_S5) _ 10 18 (Z_to_bv 12 0) 10 (getr regs 18)
  ltac:(unfold PN_S5; lia) Hpl1 Hd1 eq_refl eq_refl
  ltac:(change (bv_signed (Z_to_bv 12 0)) with 0; apply YK11.v_addi_0)).
intros mt1.
pose proof (pn_frame_stepR B LAWS WR X fy W regs _ mem md mt1 ly S Hp k _ HF
  (pn5_upd_cs regs 10 (getr regs 18) 10 eq_refl ltac:(unfold acallee_saved; lia))) as HF1.
(* +0x4c mv a1,s0 *)
pn5_fd (PN_SLOT0 + PN_S5 + 4) (OpImm ALU_ADD 11 8 (Z_to_bv 12 0)) Hpl2 Hd2.
apply (pn_step_addi (fx := fy) W _ mem _ _ (PN_SLOT0 + PN_S5 + 4) _ 11 8 (Z_to_bv 12 0) 11 (getr regs 8)
  ltac:(unfold PN_S5; lia) Hpl2 Hd2 eq_refl eq_refl);
  [pn5_gr; change (bv_signed (Z_to_bv 12 0)) with 0; apply YK11.v_addi_0 |].
intros mt2.
pose proof (pn_frame_stepR B LAWS WR X fy W _ _ mem _ mt2 ly S Hp k _ HF1
  (pn5_upd_cs _ 11 (getr regs 8) 11 eq_refl ltac:(unfold acallee_saved; lia))) as HF2.
(* +0x50 mv a2,s1 *)
pn5_fd (PN_SLOT0 + PN_S5 + 4 + 4) (OpImm ALU_ADD 12 9 (Z_to_bv 12 0)) Hpl3 Hd3.
apply (pn_step_addi (fx := fy) W _ mem _ _ (PN_SLOT0 + PN_S5 + 4 + 4) _ 12 9 (Z_to_bv 12 0) 12 (getr regs 9)
  ltac:(unfold PN_S5; lia) Hpl3 Hd3 eq_refl eq_refl);
  [pn5_gr; change (bv_signed (Z_to_bv 12 0)) with 0; apply YK11.v_addi_0 |].
intros mt3.
pose proof (pn_frame_stepR B LAWS WR X fy W _ _ mem _ mt3 ly S Hp k _ HF2
  (pn5_upd_cs _ 12 (getr regs 9) 12 eq_refl ltac:(unfold acallee_saved; lia))) as HF3.
(* +0x54 jal check_reject_clean *)
assert (Hpl4 : plookup (@pl_tpi _ PL_prog_A) (PN_SLOT0 + PN_S5 + 4 + 4 + 4) =
  Some (PCall AS_check_reject_clean (1%bv : bv 5))) by (vm_compute; reflexivity).
apply (pn_step_call (fx := fy) W _ mem _ _ (PN_SLOT0 + PN_S5 + 4 + 4 + 4) AS_check_reject_clean 1 1
  ltac:(unfold PN_S5; lia) Hpl4 eq_refl).
intros mt4.
lazymatch goal with |- SRr _ _ (mkCfg (@YK11.mkst _ ?r _ _ _) _) _ => remember r as R4 eqn:ER4 end.
pose proof (pn_frame_stepR B LAWS WR X fy W _ R4 mem _ mt4 ly S Hp k _ HF3
  ltac:(rewrite ER4; exact (pn5_upd_cs _ 1 _ 1 eq_refl ltac:(unfold acallee_saved; lia)))) as HF4.
pose proof HF4 as (HJ4 & Hsp4 & _).
unfold PN_FRAME in Hsp4.
(* the registers at the call *)
assert (E10 : getr R4 10 = w64 (-1)) by (rewrite ER4; pn5_gr; exact H18).
assert (E11 : getr R4 11 = w64 (px_doc X)) by (rewrite ER4; pn5_gr; exact R8).
assert (E12 : getr R4 12 = w64 (Ledger.lsum (px_Lam X))) by (rewrite ER4; pn5_gr; exact R9).
assert (E18 : getr R4 18 = getr regs 18) by (rewrite ER4; pn5_gr; reflexivity).
assert (RA : raZ R4 = BASE + (PN_SLOT0 + PN_S5 + 4 + 4 + 4 + 4)).
{ unfold raZ. rewrite ER4. pn5_gr. apply unsigned_lit_small. unfold PN_S5. lia. }
assert (Hrao : YK0s.ret_ok (getr R4 1)).
{ rewrite ER4. pn5_gr. apply (ret_ok_codeptr_v (PI := PA)); [unfold PN_S5; lia | vm_compute; reflexivity]. }
assert (Hra4 : 4096 <= raZ R4) by (rewrite RA, EB, EP; unfold PN_S5; lia).
assert (Hrac : raZ R4 < YM05.alloc_ceiling) by (rewrite RA, EB, EP; unfold PN_S5; lia).
assert (Hgp : getr R4 3 = w64 (as_gp B)).
{ rewrite ER4. pn5_gr. transitivity (getr (px_regs X) 3); [|exact Hgp0].
  exact (Hcs 3 ltac:(unfold acallee_saved; lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)). }
assert (Htp : getr R4 4 = w64 (as_tp B)).
{ rewrite ER4. pn5_gr. transitivity (getr (px_regs X) 4); [|exact Htp0].
  exact (Hcs 4 ltac:(unfold acallee_saved; lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)). }
assert (Hch : achain ly (aview SEGS (w_H W) mem) (spZ R4) (s0Z R4) []).
{ apply achain_low. unfold s0Z. rewrite ER4. pn5_gr. rewrite R8. unfold w64.
  rewrite unsigned_lit_small by lia. lia. }
assert (Hhi : spZ R4 + 64 <= ly_stk_hi ly) by (rewrite Hstkhi; lia).
assert (Hsp4' : spZ R4 = spZ (px_regs X) + -48) by lia.
(* doc: 56 zero bytes the callee may read *)
assert (Hsrc : src_rd W mem (px_doc X) (repeat 0 56)).
{ unfold src_rd. change (Z.of_nat (length (repeat 0 56))) with 56.
  split; [exact HZ|]. split; [exact Hdoc4|]. split; [exact Hdocc|]. split; [exact Wam|].
  split; [exact (pn5_doc_addressableR WR CTX0 X ly S Hp W mem _ k _ HPRE HJ4)|].
  intros _. exact (pn5_doc_hullR WR CTX0 X ly S Hp W mem _ k _ HPRE HJ4). }
assert (Hlive : Ledger.lsum (px_Lam X) = Ledger.lsum Lam) by (symmetry; exact (pn5_lsum_perm _ _ HPL)).
(* the call *)
lazymatch goal with |- SRr ?sg ?w (mkCfg (@YK11.mkst ?ff ?r (Z_to_bv 64 ?f) ?m _) ?d) ?Q =>
  change (SRr sg w (cfg_at (fx := ff) sg f r m d) Q) end.
eapply (pn_call (fx := fy) (SK := SK) SEGS B PST ARc LAWS Hsegs WR (wle_wle' SEGS YGcfRehidePost.RZ_cf)
  (wle'_trans SEGS YGcfRehidePost.RZ_cf) W R4 mem _ STK_parse_noting (spZ (px_regs X))
  [(px_doc X, px_doc X + 56)] (px_ly X) (px_S X) (px_Hp X) (px_W X) (px_mem X) (px_md X) [] ly S Hp k _
  STK_check_reject_clean [] (-48) [] (SIGMA AS_check_reject_clean) _ _ HJ4 Hsp4' eq_refl ltac:(lia)
  ltac:(rewrite ESTK1; lia) ltac:(rewrite ESTK1, ESTK; lia) Hrao Hra4 Hgp Htp Hch).
- intros Hafn.
  exact (HT fy ly S Hp W R4 mem _ [] (-1) (px_doc X) (Ledger.lsum (px_Lam X)) Lam peak cnt fail ran
    (px_most X) (px_own X) (conj Hafn (conj Hro (conj Hhi (conj Hrac Hfz)))) E10 ltac:(lia) ltac:(lia) E11 Hsrc E12 Hlive HLED).
- apply pn_fp_sub_nil.
- intros W2 ly2 S2 Hp2 regs2 mem2 md2 k1 Hle HJc HJ1 HP HQ.
  destruct HQ as ((EHp & ES & Eab & Hroom2 & HL2) & Hmn2).
  apply SRr_ret. unfold pn_cut_S6.
  exists fy, regs2, mem2, md2, ly2, S2, Hp2, (k + k1), Lam, peak, cnt, fail, ran, ok, None, tr.
  split.
  { rewrite pn_cfg_eq. rewrite ER4. pn5_gr.
    replace (PN_SLOT0 + PN_S5 + 4 + 4 + 4 + 4) with (PN_SLOT0 + PN_S6) by (unfold PN_S5, PN_S6; lia).
    reflexivity. }
  assert (HR2 : pn_R (PA := PA) B X Lam peak cnt fail ran ok None tr (getr regs 18) ly2 S2 Hp2 W2 mem2)
    by exact (pn_R_keep B LAWS WR CTX0 X ly S Hp W mem _ k _ Lam peak cnt fail ran ok None tr (getr regs 18)
      STK_check_reject_clean _ ly2 S2 Hp2 W2 mem2 md2 k1 HPRE HJ4 HR HJ1 ES Eab HL2).
  rewrite <- Hsp4' in HJ1.
  split; [exact (pn_frame_call B WR WR (@wle SEGS) X fy W R4 mem _ ly S Hp k _ fy W2 regs2 mem2 md2 ly2 S2 Hp2 k1
    [] _ STK_check_reject_clean [] HF4 HJc HJ1 pn_sink_nil HP Hfz (pn_fregs_refl fy) Hmn2)|].
  split; [rewrite ES; exact Hhull|].
  split; [exact (Hroom2 Hroom)|].
  assert (P18 : getr regs2 18 = getr regs 18).
  { rewrite <- E18. exact (HP 18 ltac:(unfold acallee_saved; lia)). }
  rewrite P18. exact HR2.
Qed.
End I.
