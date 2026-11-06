(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* omx-clap-core/fuzz_preset, image A' (asan, harness fix #102, pin sha256
   1be0f53d96cb9d6c2d5c92820c254e9db28e4830054a02631390e27c9547dc44): the KEEP LEMMAS of the walk of parse_noting
   (row N10-PNA; cut table lib/A/Prog/PN102Cuts.v): the frame invariant pn_frame (its journal at a budget WS, the batch kit's wild
   budget) across register steps and across a callee (its journal composed, the saved words above the callee's sp, the
   callee-saved registers, the float state, the memnorm keep, the read-only view), the reading's facts pn_R (the batch kit's post
   body) across a callee that changes no allocator state, and pj_parse's CW at A' (pn_cw_len, pn_cw_budget), at the A'
   instance. No function is proved here.
   rule 24: proves function parse_noting (reuse search: `proof-index parse_noting` exit 4 at 2026-10-30 07:2xZ,
   index v5 06:36:24Z: 0 named / 0 by address / 0 related / 0 released; the unreleased hits are this lane's own N10-PNA
   files and the plain / UBSan / B' twins; R24Pna CONFIRM 2026-10-29 18:2xZ; own signed walk 13970867e0c9, its one
   announced re-bind). This file: support lemmas of that walk only.
   THE BATCH KIT'S RE-BIND: a Theorem Labs lane's signed A' file of the same role (a working branch 13970867e0c9),
   re-fit to the batch kit's cut (commit 7cdbb61b5fa0) as the B' twin was re-fit
   (a working branch c7276d935095 lib/B/Prog/PN102B<same role>.v, read back at PI_prog_A / prh_img_A).
   The batch kit's changes: the journal carries a budget (pn_ajw_materialize: YCbqGwild.v rebase / unbase0 around YCbqG.v
   ajournal_x_materialize); pn_R_keep carries the batch kit's pn_R, the tree's free order and capacities by
   PRH_PjOrder.pj_foR_frame and PvB_Frees.pvf_ncap_frame (lane PValueB's image-free file, taken by path from
   a working branch c7276d935095, blob 67d0dad82edc). The statics' read-only check is S1ImgA.v
   pst_not_ro_A, as in the signed walk.
   OVER A WORLD RELATION R (the free / realloc move: after pj_parse, which frees, the cut's journal is at
   YA0nH.wle' segs RZ_cf): FRAME is PN102Cuts.v pn_frameR at R. Used on both sides of the free, so each with its
   form over R BESIDE it (pn_img_keepR, pn_frame_stepR) and the old name as the instance at wle: pn_img_keep,
   pn_frame_step. Used only over R (after or across the free), so restated in place over R: pn_ajw_materialize,
   pn_frame_call, pn_R_keep. The journals over R are YCbqG.v ajournal_xwR, read through the ajxR_* projections.
   SHAPES TAKEN: the read-only keep is lib/A/Prog/Ent102L2A.v l2_imgkeep's second half (a working branch
   b1bc025047ea), restated at PST := prh_pst prh_img_A with S1ImgA.v pst_not_ro_A.
   NUMERALS: 48 (the frame), 8 .. 40 (the save slots), 8 (a word). No ADDRESS. *)
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
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YAkMemnorm YCbqGwild.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Base.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import Listing_prog PAImg_prog PRH_Img.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import CfParamsPreset.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require PRH_Reader PRH_FnCheck PRH_PjOrder.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP08 YL0b.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require Import S1ImgA.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require Import PN102Cuts PN102Help.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require PvB_Frees.
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
#[local] Abbreviation RLO := (@pa_relro_lo rc A_prog_listing PA).
#[local] Abbreviation RHI := (@pa_relro_hi rc A_prog_listing PA).
#[local] Abbreviation PST := (@prh_pst prh_img_A).
Variable B : asyms.
#[local] Abbreviation ARc := (fun ly S Hp (W : world SEGS) mem md =>
  ARcf (cp := CP) SEGS B ly S Hp W mem md /\ xs_placed_cf ly S).
(* the frame at a cut over a world relation R (PN102Cuts.v pn_frameR): wle before pj_parse, wle' segs RZ_cf after it *)
#[local] Abbreviation FRAME R X fy W regs mem md ly S Hp k WS :=
  (pn_frameR (fx := fx) (PI := prh_img_A) (PA := PA) B ARc SK R X fy W regs mem md ly S Hp k WS).

(* the statics are not read-only (S1ImgA.v), at the instance's segments and relro range *)
Lemma pn_pst_not_ro : forall a, Exists (in_zr a) PST -> ~ in_roP SEGS RLO RHI a.
Proof. intros a Ha. exact (pst_not_ro_A a Ha). Qed.

(* the read-only view across a journal (at any budget, over any world relation R1) whose footprint does not open the
   sink (Ent102L2A.v l2_imgkeep's half) *)
Lemma pn_img_keepR : forall (R1 : world SEGS -> world SEGS -> Prop) STK1 A FP1 ly S Hp (W : world SEGS) mem md own
  ly2 S2 Hp2 (W2 : world SEGS) mem2 md2 k1 WS1,
  ajournal_xwR (SK := SK) SEGS B PST ARc R1 STK1 A FP1 ly S Hp W mem md own ly2 S2 Hp2 W2 mem2 md2 k1 WS1 ->
  ~ YI16.sink_open_fp FP1 ->
  arodata_okP SEGS RLO RHI B (aview SEGS (w_H W) mem) -> arodata_okP SEGS RLO RHI B (aview SEGS (w_H W2) mem2).
Proof.
intros R1 STK1 A FP1 ly S Hp W mem md own ly2 S2 Hp2 W2 mem2 md2 k1 WS1 HJ1 Hs0 HRO.
pose proof (ajxR_img HJ1) as G3.
intros a Hro Hn1 Hn2.
assert (Hi : in_img SEGS a).
{ destruct Hro as [(sg & Hin & _ & Hr) | Hr];
    [exists sg; split; [exact Hin | exact Hr] | exact (@pa_relro_img _ _ PA a Hr)]. }
assert (Hp' : ~ Exists (in_zr a) PST) by (intros Hx; exact (pn_pst_not_ro a Hx Hro)).
rewrite (G3 a Hi Hn1 Hn2 Hp' (fp_spares_closed FP1 a Hs0)). exact (HRO a Hro Hn1 Hn2).
Qed.
Lemma pn_img_keep : forall STK1 A FP1 ly S Hp (W : world SEGS) mem md own ly2 S2 Hp2 (W2 : world SEGS) mem2 md2 k1 WS1,
  ajournal_xw (SK := SK) SEGS B PST ARc STK1 A FP1 ly S Hp W mem md own ly2 S2 Hp2 W2 mem2 md2 k1 WS1 ->
  ~ YI16.sink_open_fp FP1 ->
  arodata_okP SEGS RLO RHI B (aview SEGS (w_H W) mem) -> arodata_okP SEGS RLO RHI B (aview SEGS (w_H W2) mem2).
Proof. exact (pn_img_keepR (@wle SEGS)). Qed.

(* the empty footprint and parse_noting's own do not open the sink *)
Lemma pn_sink_nil : ~ YI16.sink_open_fp [].
Proof. intros (r & Hr & _). destruct Hr. Qed.

(* the float state's callee-saved registers, through two calls *)
Lemma pn_fregs_trans : forall f1 f2 f3, fregs_kept_x f1 f2 -> fregs_kept_x f2 f3 -> fregs_kept_x f1 f3.
Proof. intros f1 f2 f3 H1 H2 r Hr. rewrite (H2 r Hr). exact (H1 r Hr). Qed.
Lemma pn_fregs_refl : forall f, fregs_kept_x f f.
Proof. intros f r _. reflexivity. Qed.

Hypothesis LAWS : AR_laws_x SEGS B ARc (@cf_head CP).
#[local] Abbreviation Hsegs := (@pa_segs_low rc A_prog_listing PA).

(* a callee-saved register across a call *)
Lemma pn_pres : forall (regs regs' : bvmap 5 word) r, aregs_preserved regs regs' -> acallee_saved r ->
  getr regs' (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r).
Proof. intros regs regs' r HP Hr. exact (HP r Hr). Qed.

(* the model materialized, at any budget and over any world relation R: rebase to the empty budget
   (YCbqGwild.v ajournal_xw_rebaseR), YCbqG.v's ajournal_x_materializeR, back (ajournal_xw_unbase0R with the journal's
   own wild clause) *)
Lemma pn_ajw_materialize : forall (R : world SEGS -> world SEGS -> Prop) STK sp0 FP ly S Hp (W : world SEGS) mem md
  own lyc Sc Hpc (Wc : world SEGS) memc mdc k WS Xm,
  ajournal_xwR (SK := SK) SEGS B PST ARc R STK sp0 FP ly S Hp W mem md own lyc Sc Hpc Wc memc mdc k WS ->
  ajournal_xwR (SK := SK) SEGS B PST ARc R STK sp0 FP ly S Hp W mem md own lyc Sc Hpc Wc memc
    (with_vm_backing (m_vm_lazy mdc) Xm mdc) k WS.
Proof.
intros R STK sp0 FP ly S Hp W mem md own lyc Sc Hpc Wc memc mdc k WS Xm HJ.
eapply (YCbqGwild.ajournal_xw_unbase0R (SK := SK) SEGS B PST ARc R); [|exact (ajxR_wild HJ)].
apply (ajournal_x_materializeR (SK := SK) SEGS B PST ARc LAWS Hsegs R).
exact (YCbqGwild.ajournal_xw_rebaseR (SK := SK) SEGS B PST ARc R _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ).
Qed.

(* the frame across register steps: a step that writes no callee-saved register but s0, s1, s2, s3 and leaves memory
   alone (the model is only materialized), over any world relation R *)
Lemma pn_frame_stepR : forall (R : world SEGS -> world SEGS -> Prop) X fy (W : world SEGS) regs regs' mem md Xm ly S
  Hp k WS,
  FRAME R X fy W regs mem md ly S Hp k WS ->
  (forall r, acallee_saved r -> r <> 8 -> r <> 9 -> r <> 18 -> r <> 19 ->
     getr regs' (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r)) ->
  FRAME R X fy W regs' mem (with_vm_backing (m_vm_lazy md) Xm md) ly S Hp k WS.
Proof.
intros R X fy W regs regs' mem md Xm ly S Hp k WS HF Hreg.
destruct HF as (HJ & Hsp & S1 & S2 & S3 & S4 & S5 & Hcs & Hfrm & Hfk & Hmn & Hro).
split; [exact (pn_ajw_materialize R _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Xm HJ)|].
split.
{ unfold spZ in *. rewrite <- Hsp. f_equal. exact (Hreg 2 ltac:(unfold acallee_saved; lia) ltac:(lia) ltac:(lia)
    ltac:(lia) ltac:(lia)). }
split; [exact S1|]. split; [exact S2|]. split; [exact S3|]. split; [exact S4|]. split; [exact S5|].
split; [intros r Hr H2 H8 H9 H18 H19; rewrite (Hreg r Hr H8 H9 H18 H19); exact (Hcs r Hr H2 H8 H9 H18 H19)|].
split; [exact Hfrm|]. split; [exact Hfk|]. split; [exact Hmn | exact Hro].
Qed.
Lemma pn_frame_step : forall X fy (W : world SEGS) regs regs' mem md Xm ly S Hp k WS,
  FRAME (@wle SEGS) X fy W regs mem md ly S Hp k WS ->
  (forall r, acallee_saved r -> r <> 8 -> r <> 9 -> r <> 18 -> r <> 19 ->
     getr regs' (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r)) ->
  FRAME (@wle SEGS) X fy W regs' mem (with_vm_backing (m_vm_lazy md) Xm md) ly S Hp k WS.
Proof. exact (pn_frame_stepR (@wle SEGS)). Qed.

(* the frame across a callee: the composed journal from parse_noting's entry (at the budget WS' the call rule gives,
   over the relation R the frame is stated at after the call), the callee's own journal (any budget, over any relation
   R1) at the call's sp (the caller's sp, 48 below the entry sp), the callee-saved registers preserved, the callee's
   float state, its memnorm keep, and a footprint that does not open the sink. The frame before the call may be at
   another relation R0 (pj_parse: wle before it, wle' segs RZ_cf after it); only its frame conjuncts are read. *)
Lemma pn_frame_call : forall (R0 R R1 : world SEGS -> world SEGS -> Prop) X fy (W : world SEGS) regs mem md ly S Hp
  k WS fy2 (W2 : world SEGS) regs2 mem2 md2 ly2 S2 Hp2 k1 WS1 WS' STK1 FP1,
  FRAME R0 X fy W regs mem md ly S Hp k WS ->
  ajournal_xwR (SK := SK) SEGS B PST ARc R STK_parse_noting (spZ (px_regs X)) [(px_doc X, px_doc X + 56)]
    (px_ly X) (px_S X) (px_Hp X) (px_W X) (px_mem X) (px_md X) [] ly2 S2 Hp2 W2 mem2 md2 (k + k1) WS' ->
  ajournal_xwR (SK := SK) SEGS B PST ARc R1 STK1 (spZ regs) FP1 ly S Hp W mem md [] ly2 S2 Hp2 W2 mem2 md2 k1 WS1 ->
  ~ YI16.sink_open_fp FP1 ->
  aregs_preserved regs regs2 ->
  YK0o.frm_zero (@YK11.fp_csr fy2) -> fregs_kept_x fy fy2 ->
  (YAkMemnorm.memnorm SEGS mem -> YAkMemnorm.memnorm SEGS mem2) ->
  FRAME R X fy2 W2 regs2 mem2 md2 ly2 S2 Hp2 (k + k1) WS'.
Proof.
intros R0 R R1 X fy W regs mem md ly S Hp k WS fy2 W2 regs2 mem2 md2 ly2 S2 Hp2 k1 WS1 WS' STK1 FP1 HF HJc HJ1 Hs0 HP
  Hz2 Hk2 Hmn2.
destruct HF as (HJ & Hsp & S1 & S2' & S3 & S4 & S5 & Hcs & Hfrm & Hfk & Hmn & Hro).
pose proof (ajxR_stk HJ) as Hstk.
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
assert (HSP : spZ regs2 = spZ regs).
{ unfold spZ. f_equal. exact (pn_pres regs regs2 2 HP ltac:(unfold acallee_saved; lia)). }
assert (KS : forall off v, 8 <= off <= 40 ->
  rd64 (aview SEGS (w_H W) mem) (spZ (px_regs X) - off) v -> rd64 (aview SEGS (w_H W2) mem2) (spZ (px_regs X) - off) v).
{ intros off v Hoff Hr. apply (pn_rd64_kept (aview SEGS (w_H W) mem)); [|exact Hr].
  intros i Hi.
  let v := eval vm_compute in (@STK_parse_noting prh_img_A) in
  assert (Ev : @STK_parse_noting prh_img_A = v) by (vm_compute; reflexivity).
  unfold PN_FRAME in Hsp.
  apply (ajxR_hi HJ1); lia. }
split; [exact HJc|].
split; [rewrite HSP; exact Hsp|].
split; [exact (KS 8 _ ltac:(lia) S1)|]. split; [exact (KS 16 _ ltac:(lia) S2')|].
split; [exact (KS 24 _ ltac:(lia) S3)|]. split; [exact (KS 32 _ ltac:(lia) S4)|].
split; [exact (KS 40 _ ltac:(lia) S5)|].
split; [intros r Hr H2 H8 H9 H18 H19; rewrite (pn_pres regs regs2 r HP Hr); exact (Hcs r Hr H2 H8 H9 H18 H19)|].
split; [exact Hz2|]. split; [exact (pn_fregs_trans _ _ _ Hfk Hk2)|].
split; [intros H0; exact (Hmn2 (Hmn H0))|].
exact (pn_img_keepR R1 STK1 (spZ regs) FP1 ly S Hp W mem md [] ly2 S2 Hp2 W2 mem2 md2 k1 WS1 HJ1 Hs0 Hro).
Qed.

(* ---- the reading's facts (pn_R) across a callee that changes no allocator state (fuzz_alloc_ran_out,
   check_reject_clean): its journal has an empty footprint, the same astate and the same blocks; the ledger at the
   callee's post is given ---- *)
#[local] Abbreviation RL := (prh_room_live_a8 (cp := CP)).

Lemma pn_req_pos : forall z, 0 < z -> req_size z = z.
Proof. intros z Hz. unfold req_size. destruct (Z.eqb_spec z 0); lia. Qed.

(* a byte string moves with its view (FuzzStrdup.v sd_garr8_move) *)
Lemma pn_garr8_move : forall (W W' : world SEGS) m m' x d l, garr8 SEGS (mrestrict (w_H W) m) x l ->
  (forall j, (j < length l)%nat -> aview SEGS (w_H W') m' (d + Z.of_nat j) = aview SEGS (w_H W) m (x + Z.of_nat j)) ->
  garr8 SEGS (mrestrict (w_H W') m') d l.
Proof.
intros W W' m m' x d l H HA j Hj. destruct (H j Hj) as [V R]. split; [|exact R].
intros kk Hkk. assert (kk = 0%nat) by lia. subst kk. cbn [Z.of_nat]. rewrite Z.add_0_r.
specialize (V 0%nat Hkk). cbn [Z.of_nat] in V. rewrite Z.add_0_r in V.
specialize (HA j Hj). unfold aview in HA. rewrite V in HA. cbn [option_map] in HA.
destruct (mbyte SEGS (mrestrict (w_H W') m') (d + Z.of_nat j)) as [b|] eqn:Eb; cbn [option_map] in HA; [|discriminate HA].
injection HA as Hb. f_equal. apply bv_eq. exact Hb.
Qed.

(* The batch kit's pn_R (the outcome, the ledger with g_most and the refusal peak, the Some arm's block sizes, free order and
   capacities): the live set, the position and the outcome are over S, which the callee keeps; the tree's bytes
   (header in doc's frame, blocks of D) are kept, so pj_nodeR, pj_foR and pj_ncapR move with them
   (PRH_Reader.pj_nodeR_frame, PRH_PjOrder.pj_foR_frame, PvB_Frees.pvf_ncap_frame). The entry journal over any world
   relation R (wle' segs RZ_cf after pj_parse); the callee's own journal plain *)
Lemma pn_R_keep : forall (R : world SEGS -> world SEGS -> Prop) CTX0 X ly S Hp (W : world SEGS) mem md k WS Lam' peak'
  cnt' fail' ran' ok res tr r10 STK1 sp1 ly2 S2 Hp2 (W2 : world SEGS) mem2 md2 k1,
  pn_pre (fx := fx) (RL := RL) (PA := PA) B ARc CTX0 X ->
  ajournal_xwR (SK := SK) SEGS B PST ARc R STK_parse_noting (spZ (px_regs X)) [(px_doc X, px_doc X + 56)]
    (px_ly X) (px_S X) (px_Hp X) (px_W X) (px_mem X) (px_md X) [] ly S Hp W mem md k WS ->
  pn_R (PA := PA) B X Lam' peak' cnt' fail' ran' ok res tr r10 ly S Hp W mem ->
  ajournal_x (SK := SK) SEGS B PST ARc STK1 sp1 [] ly S Hp W mem md [] ly2 S2 Hp2 W2 mem2 md2 k1 ->
  S2 = S -> ablocks B ly2 S2 = ablocks B ly S ->
  prh_ledger B ly2 S2 Hp2 W2 mem2 Lam' peak' cnt' fail' ran' (px_most X) (px_own X) ->
  pn_R (PA := PA) B X Lam' peak' cnt' fail' ran' ok res tr r10 ly2 S2 Hp2 W2 mem2.
Proof.
intros R CTX0 X ly S Hp W mem md k WS Lam' peak' cnt' fail' ran' ok res tr r10 STK1 sp1 ly2 S2 Hp2 W2 mem2 md2 k1
  HPRE HJ HR HJ1 ES Eab HL2.
pose proof (pp_home _ _ _ _ HPRE) as Hhome. pose proof (pp_out _ _ _ _ HPRE) as Hout.
pose proof (pp_ledger _ _ _ _ HPRE) as Hled0.
pose proof (ajxR_ly HJ) as Hly. pose proof (ajxR_frs HJ) as Hfrs.
pose proof (ajx_ar HJ1) as HAR2. pose proof (ajx_blk HJ1) as F2. pose proof (ajx_img HJ1) as F3.
pose proof (ajx_frm HJ1) as F4.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (Hh16 : @cf_head CP = 16) by reflexivity.
destruct HR as (HRUN & HLIVE & HPOS & HOUTC & HOKS & HCNT & HFA & HPK & HHB & HFW & HRO & HR0 & HBY & HLED & HM).
(* the entry blocks are blocks of the current state *)
assert (HBL : forall x, In x (ablocks B (px_ly X) (px_S X)) -> In x (ablocks B ly S)).
{ intros x Hx. destruct res as [t|].
  - destruct HM as (_ & D & _ & _ & _ & _ & _ & _ & Hab & _). apply (Permutation_in _ (Permutation_sym Hab)).
    apply in_or_app. left. exact Hx.
  - destruct HM as (_ & _ & Hab & _). apply (Permutation_in _ (Permutation_sym Hab)). exact Hx. }
(* a byte of a live block of the current state is kept *)
assert (KB : forall p n a, In (p, n) (ablocks B ly S) -> p <= a < p + req_size n ->
  aview SEGS (w_H W2) mem2 a = aview SEGS (w_H W) mem a).
{ intros p n a Hin Ha. replace a with (p + (a - p)) by lia.
  apply (F2 p n (a - p) Hin ltac:(rewrite Eab; exact Hin) ltac:(lia)). intros (r & Hr & _). destruct Hr. }
(* a byte of a live frame of the entry is kept *)
assert (EF : forall cid pos, frame_addr ly cid pos = frame_addr (px_ly X) cid pos).
{ intros cid pos. unfold frame_addr. destruct Hly as (_ & _ & _ & _ & _ & EF & _). rewrite EF. reflexivity. }
assert (KF : forall cid pos a, In (cid, pos) (frames (px_S X)) ->
  frame_addr (px_ly X) cid pos <= a < frame_addr (px_ly X) cid pos + fs_frame_bytes cid ->
  aview SEGS (w_H W2) mem2 a = aview SEGS (w_H W) mem a).
{ intros cid pos a Hin Ha. apply (F4 cid pos a); [rewrite Hfrs; exact Hin| |].
  - left. unfold in_zr, frame_rng. cbn [fst snd]. rewrite EF. lia.
  - intros (r & Hr & _). destruct Hr. }
(* the text's bytes *)
assert (KT : forall a, px_text X <= a < px_text X + pn_len X ->
  aview SEGS (w_H W2) mem2 a = aview SEGS (w_H W) mem a).
{ intros a Ha.
  assert (Himg : forall a, in_roP SEGS RLO RHI a -> ~ Exists (in_zr a) (as_owned_static B) ->
      ~ (as_errno B <= a < as_errno B + 4) -> aview SEGS (w_H W2) mem2 a = aview SEGS (w_H W) mem a).
  { intros a0 Hro Hn1 Hn2.
    assert (Hi : in_img SEGS a0).
    { destruct Hro as [(sg & Hin & _ & Hr) | Hr];
        [exists sg; split; [exact Hin | exact Hr] | exact (@pa_relro_img _ _ PA a0 Hr)]. }
    apply (F3 a0 Hi Hn1 Hn2 (fun Hx => pn_pst_not_ro a0 Hx Hro) (fp_spares_closed [] a0 pn_sink_nil)). }
  destruct Hhome as [[(b & m & Hin & Hb & Hm) | [(_ & _ & _ & Hro) | (_ & _ & Hro)]] | (b & m & Hin & _ & Hb & Hm)].
  - pose proof (proj1 (Forall_forall _ _) (prh_ledger_blocks B _ _ _ _ _ _ _ _ _ _ _ _ Hled0) (b, m) Hin) as Hhb.
    destruct Hhb as (Hm0 & Hab & _). cbn [fst snd] in Hab. rewrite Hh16 in Hab.
    apply (KB (b - 16) (m + 16) a (HBL _ Hab)). rewrite pn_req_pos by lia. lia.
  - destruct (Hro a Ha) as (H1 & H2 & H3). exact (Himg a H1 H2 H3).
  - destruct (Hro a Ha) as (H1 & H2 & H3 & _). exact (Himg a H1 H2 H3).
  - apply (KB b m a (HBL _ Hin)). rewrite pn_req_pos by lia. lia. }
(* doc's frame *)
destruct Hout as ((cid & pos & Hfin & Hd0 & Hd1) & _).
assert (KD : forall a, px_doc X <= a < px_doc X + 56 -> aview SEGS (w_H W2) mem2 a = aview SEGS (w_H W) mem a)
  by (intros a Ha; apply (KF cid pos a Hfin); lia).
split; [exact HRUN|]. split; [rewrite ES; exact HLIVE|]. split; [rewrite ES; exact HPOS|].
split; [rewrite ES; exact HOUTC|].
split; [exact HOKS|]. split; [exact HCNT|]. split; [exact HFA|]. split; [exact HPK|].
split; [exact HHB|]. split; [exact HFW|]. split; [exact HRO|]. split; [exact HR0|].
split.
{ unfold bytes_at in *. apply (pn_garr8_move W W2 mem mem2 (px_text X) (px_text X) (px_tb X) HBY).
  intros j Hj. apply KT. unfold pn_len. lia. }
split; [exact HL2|].
destruct res as [t|].
- destruct HM as (H10 & D & HP & HS & HN & HRB & HFO & HNew & Hab & HN0 & HNC). split; [exact H10|].
  (* the tree's footprint (doc's header and the blocks of D) agrees across the callee *)
  assert (HAG : PRH_Reader.pj_agreeR SEGS (mrestrict (w_H W) mem) (mrestrict (w_H W2) mem2)
    (PRH_Reader.pj_footR (px_doc X) D)).
  { intros x [Hx | (b & Hb & Hx)].
    + split; [apply (mbyte_of_aview SEGS); exact (KD x Hx)|].
      intros _. apply (apresent_writable SEGS).
      destruct (alx_frames SEGS B ARc LAWS ly2 S2 Hp2 W2 mem2 md2 cid pos HAR2 ltac:(rewrite ES, Hfrs; exact Hfin))
        as (_ & _ & Hfb & _).
      assert (EF2 : frame_addr ly2 cid pos = frame_addr ly cid pos).
      { pose proof (ajx_ly HJ1) as Hly1. unfold frame_addr. destruct Hly1 as (_ & _ & _ & _ & _ & EF1 & _).
        rewrite EF1. reflexivity. }
      apply (Hfb x). rewrite EF2, EF. lia.
    + destruct b as [a0 k0]. unfold PRH_Reader.pj_holdsR in Hx. cbn [fst snd] in Hx.
      assert (Hin : In (a0 - 16, k0 + 16) (ablocks B ly S)).
      { apply (Permutation_in _ (Permutation_sym Hab)). apply in_or_app. right. unfold PRH_FnCheck.ck_hblks.
        rewrite Hh16. exact (in_map (fun ak => (fst ak - 16, snd ak + 16)) D (a0, k0) Hb). }
      assert (Hk0 : 0 <= k0) by lia.
      split; [apply (mbyte_of_aview SEGS); apply (KB _ _ x Hin); rewrite pn_req_pos by lia; lia|].
      intros _. apply (apresent_writable SEGS).
      destruct (alx_blocks SEGS B ARc LAWS ly2 S2 Hp2 W2 mem2 md2 (a0 - 16) (k0 + 16) HAR2 ltac:(rewrite Eab; exact Hin))
        as (_ & _ & _ & _ & Hpb & _).
      apply (Hpb x). rewrite pn_req_pos by lia. lia. }
  exists D. split; [exact HP|]. split; [exact HS|]. split; [exact HN|]. split; [exact HRB|].
  split.
  { intros Hh n Hn. destruct (HFO Hh n Hn) as (F & HF & HFm). exists F. split; [|exact HFm].
    exact (PRH_PjOrder.pj_foR_frame SEGS n _ _ _ _ _ _ _ HF (PRH_PjOrder.pj_foR_lblk SEGS _ _ _ _ _ _ HF) HAG). }
  split; [exact HNew|].
  split; [rewrite Eab; exact Hab|].
  split; [exact (PRH_Reader.pj_nodeR_frame SEGS t (mrestrict (w_H W) mem) (mrestrict (w_H W2) mem2) _ _ D HN0 HAG)|].
  exact (PvB_Frees.pvf_ncap_frame SEGS t (w_H W) mem (mrestrict (w_H W2) mem2) _ _ D HN0 HAG HNC).
- destruct HM as (H10 & HP & Hab & HZ). split; [exact H10|]. split; [exact HP|].
  split; [rewrite Eab; exact Hab|].
  apply (PRH_Reader.pj_zeroR_frame SEGS (mrestrict (w_H W) mem) (mrestrict (w_H W2) mem2) (px_doc X) HZ).
  intros x Hx. apply (mbyte_of_aview SEGS). exact (KD x Hx).
Qed.

(* pj_parse's CW at A': two traces, the room prh_wk F_parse_noting pays (pn_free_sites_A, pn_wk_A) *)
Lemma pn_cw_len : forall X, length (pn_cw (PI := prh_img_A) (PA := PA) B X) = 2%nat.
Proof.
intros X. unfold pn_cw. rewrite length_app, !length_map. destruct pn_free_sites_A as [E1 E2]. rewrite E1, E2.
reflexivity.
Qed.
(* ... so the post's budget wbudget [] (prh_wk F_parse_noting) holds of it *)
Lemma pn_cw_budget : forall X, YCbqGwild.wbudget [] (prh_wk F_parse_noting) (pn_cw (PI := prh_img_A) (PA := PA) B X).
Proof.
intros X. unfold YCbqGwild.wbudget. rewrite YCbqGwild.wfresh_nil_set, pn_cw_len, pn_wk_A. lia.
Qed.
End I.
