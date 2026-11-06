(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/B/Prog/CrcB.v, with its module paths and module names changed; 996 of its 1069 lines of code are new or changed and 441 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/B/Prog/Crt102B_T7.v; 33 of its 93 lines of code are new or changed and 1009 lines of the source are left out. *)
(* fuzz_preset, walk of check_round_trip on the #102 pins, IMAGE B' (asan-ubsan
   d663f82d7f488d30, unstripped twin c90d4fa54d43160b), FREE-PIECES-102 Part 7a row T7 = CRT-B-CEXIT: THE ROW'S
   COMPOSITION.

   rule 24: proves function check_round_trip (image B' of fuzz_preset; reuse search CONFIRMED by name: the R24 confirmation
   note R24-CONFIRM.md (sha256 b58eb5e2e5e3; internal record): released proofs plain/ubsan only, its address runs no evidence; no released walk, no walk held outside this tree, and no walk on an internal branch of these B' segments).

   The row's stretches (Crt102B_T7_bd.v cuts C +0x6f8, FF +0x7f8, PF +0x800, E +0x808, X +0x30c), each Qed:
   - Crt102B_T7.v    t7_stretch_C  : T7_AT_FF -> T7_AT_C   (the two __wrap_strcmp checks and the type check)
   - Crt102B_T7_FP.v t7_stretch_FF : T7_AT_PF -> T7_AT_FF  (fuzz_free (saved))
   - Crt102B_T7_FP.v t7_stretch_PF : T7_AT_E -> T7_AT_PF   (pj_free (&back))
   - Crt102B_T7_E.v  t7_stretch_E  : T7_AT_X  -> T7_AT_E   (`mv s5, zero`; `j` X)
   composed here: crtB_T7 : CRT_B_SEG_T7, the glue's statement (Crt102Glue.v) at the B instance (PI_prog_B, CRT_PC_B,
   CRT_X_OFF_B, CRT_C_OFF_B), by conversion: T7_AT_X is CRT_B_AT_X and T7_AT_C is CRT_B_AT_C there. back's free order,
   which pj_free (&back) needs, is crt_at_C_B's own conjunct since 7281359fe8bc; no premise beyond the Section's.
   KB ROUND (Crt102Glue.v G3 / G4): the glue's crt_at_C_B and crt_at_X_B now carry crt_live at kb = prh_wk
   F_check_round_trip and QF is the budgeted post; the four stretches are re-fit at that budget, and crtB_T7's
   statement and this composition are unchanged.
   On the Step-1 contract texts (the re-hiding move): CRT_B_SEG_T7's text is unchanged,
   its cuts now conclude YA0nH.SRr' SEGS YGcfRehidePost.RZ_cf (Crt102Glue.v, the wle' contract); crtB_T7 takes one
   more Section hypothesis, HOS4 : (length rp_os <= 4)%nat (check_round_trip's own text premise, PRH_FnCheck.v:2363),
   which the two frees' hull budgets need (Crt102B_T7_FP.v t7f_hull0).

   NAMED SECTION HYPOTHESES (texts as in the stretch files; owners in their comments there):
   LAWS (engine), HPRE / HTREE / HRAN / HCL / HCTX / HKMA / HKST (tcheck_round_trip_specX's premises),
   BOK (image B's start-up record, YF0m ts_ok), IMGVIS (img_shadow_vis_cf at CfImgB.CfImg_B), FFREE / PJFREE (the
   tfuzz_free_specX / tpj_free_specX texts), STRCMP (the libc strcmp row, astrcmp_realizes_xrom at __wrap_strcmp).
   STRCMP stays a NAMED hypothesis of crtB_T7. Its B' discharge is the leaf Crt102B_T7_strcmp.v (crtB_T7_strcmp:
   crtB_T7 at B := YD2l.TfibB, ARx := ARcf, STRCMP := the libc row's lib/AU/PSstrRo.v ps_strcmp_xrom_B). This file
   does not Require PSstrRo.v: it loads lib/K/Lib/LiaTuning.v / lib/K5/Lib/LiaTuning.v, whose global `Ltac lia ::=`
   changes later proofs in any file that loads it.

   INPUTS OF RECORD: this tree's files (the row's base was commit cbe6d10993c2, an ancestor of this tree;
   Crt102Glue.v with back's free order in crt_at_C_B); the B' helpers Crt102KitB.v (through Crt102B_T7_kit.v); this
   row's Crt102B_T7_bd / _kit / _tree / T7 / _FP / _E.

   NUMERALS: none. *)
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
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YI16 YG0p YCbqG YGcallx YCbqGcall YCbqGcallW.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0d YP0c YC80 YPsym YC4aP YC1fP YC80x YC1fPx.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YImgTop YGcfNames FCiface YGcallSx YGcfRoomKeep.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfRoomLive YAkMemnorm YGcallMx YGcallMxmn YSRrMemnorm.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Ledger.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PjTree PjGrammar PjRoundTrip PresetRoomPos PresetReqAt PresetReqAtNoMiss PresetRun.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require ReaderRes WriterValue WriterApp PjWriteHyp.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Base PRH_Reader PRH_FnCheck CfParamsPreset.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require PRH_FnPj PRH_FnWriter PRH_FnAlloc.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B Require Import Img0 Listing_prog PAImg_prog PRH_ImgB.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require Import S10Env S1Ledger Crt102Glue Crt102Img Crt102Model.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require CfImgB.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require Import S1ImgB Crt102B_T7_bd.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require Crt102B_T7 Crt102B_T7_FP Crt102B_T7_E.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require Import Crt102ImgB.
Import ListNotations.
Local Set Warnings "-notation-for-abbreviation".
Local Open Scope Z_scope.

Section t7top. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg}.
#[local] Existing Instance CfParams_preset.
#[local] Existing Instance prh_img_B.
Context {RL : PrhRoomLive} {SK : YI16.sink_head}.
#[local] Notation PA := (PI_prog_B).
#[local] Notation SEGS := (@pa_segs _ B_prog_listing PA).
#[local] Notation SIGMA := (@pa_sigma _ B_prog_listing PA).
#[local] Notation RLO := (@pa_relro_lo _ B_prog_listing PA).
#[local] Notation RHI := (@pa_relro_hi _ B_prog_listing PA).
#[local] Notation STKC := (@STK_check_round_trip prh_img_B).

Section f.
Variable B : asyms.
Variable ARx : alayout -> astate -> list Z -> world SEGS -> (word -> option byte) -> Model -> Prop.

Section g.
Variables (rp_sm : list Z -> Z * Z) (rp_x : list Z) (rp_os : list (option nat * option nat * option nat))
  (rp_i : nat) (rp_H0 : list Z).
Variables (ly : alayout) (S : astate) (Hp : list Z) (W : world SEGS) (regs : bvmap 5 word)
  (mem : word -> option byte) (md : Model) (ch : list (Z * Z * Z))
  (doc : Z) (t : PjTree.jv) (D : list (Z * Z))
  (Lam : list (Z * Z)) (peak cnt ran most : Z)
  (CTX0 : list (list Z)).

Hypothesis LAWS : AR_laws_x SEGS B ARx cf_head.
Hypothesis HPRE : fpre B ARx STKC ly S Hp W regs mem md ch.
Hypothesis HTREE : ck_tree_ok ly S Lam W mem doc t D.
Hypothesis HRAN : ran = 0.
Hypothesis HCL : prh_univ_closure B CTX0.
Hypothesis HCTX : prh_ctx CTX0 F_check_round_trip (raZ regs :: spine ch).
Hypothesis HKMA : @kept_img _ B_prog_listing PA B (@CRT_MOD_AT_B _ PA) (Z.of_nat (length ck_MOD_AT) + 1).
Hypothesis HKST : @kept_img _ B_prog_listing PA B (@CRT_STAMP_B _ PA) (Z.of_nat (length ck_STAMP) + 1).
Hypothesis BOK : asyms_ok B.
Hypothesis IMGVIS : forall ly S Hp (W : world SEGS) mem md a,
  ARx ly S Hp W mem md -> @cf_img_lo CfImgB.CfImg_B <= a < @cf_img_top CfImgB.CfImg_B ->
  aview SEGS (w_H W) mem (shadow_addr a) <> None.
Hypothesis FFREE : forall fxk : YK11.FPState,
  @PRH_FnAlloc.tfuzz_free_specX fxk rc CfParams_preset prh_img_B RL B_prog_listing PA B ARx SK.
Hypothesis PJFREE : forall fxk : YK11.FPState,
  @PRH_FnPj.tpj_free_specX fxk rc ci CfParams_preset prh_img_B RL B_prog_listing PA B ARx SK CTX0 DOC_D.
Hypothesis STRCMP : forall fxk : YK11.FPState,
  astrcmp_realizes_xrom (fx := fxk) SEGS B ARx RLO RHI (SIGMA AS___wrap_strcmp).
(* THE LENGTH BOUND of the run (check_round_trip's text premise, PRH_FnCheck.v:2363), for the
   two frees' hull budgets in Crt102B_T7_FP.v *)
Hypothesis HOS4 : (length rp_os <= 4)%nat.

(* THE ROW: the glue's CRT_B_SEG_T7 at the B instance. C -> X: the walk, fuzz_free, pj_free (&back), the exit. *)
Theorem crtB_T7 :
  CRT_B_SEG_T7 (fx := fx) (rc := rc) (PI := prh_img_B) (RL := RL) (SK := SK) (L := B_prog_listing) (PA := PA)
    (CRT_PC := CRT_PC_B) (CRT_X_OFF := CRT_X_OFF_B) (CRT_C_OFF := CRT_C_OFF_B) (B := B) (ARx := ARx)
    (rp_sm := rp_sm) (rp_x := rp_x) (rp_os := rp_os) (rp_i := rp_i) (rp_H0 := rp_H0) (ly := ly) (S := S) (Hp := Hp)
    (W := W) (regs := regs) (mem := mem) (md := md) (doc := doc) (t := t) (D := D) (Lam := Lam) (peak := peak)
    (cnt := cnt) (ran := ran) (most := most).
Proof.
intros HX.
exact (Crt102B_T7.t7_stretch_C B ARx rp_sm rp_x rp_os rp_i rp_H0 ly S Hp W regs mem md ch doc t D Lam peak cnt ran most
  LAWS HPRE HTREE HKMA HKST BOK IMGVIS STRCMP
  (Crt102B_T7_FP.t7_stretch_FF B ARx rp_sm rp_x rp_os rp_i rp_H0 ly S Hp W regs mem md ch doc t D Lam peak cnt ran
     most CTX0 LAWS HPRE HTREE HCL HCTX FFREE HOS4
     (Crt102B_T7_FP.t7_stretch_PF B ARx rp_sm rp_x rp_os rp_i rp_H0 ly S Hp W regs mem md ch doc t D Lam peak cnt ran
        most CTX0 LAWS HPRE HTREE HCL PJFREE HOS4
        (Crt102B_T7_E.t7_stretch_E B ARx rp_sm rp_x rp_os rp_i rp_H0 ly S Hp W regs mem md doc t D Lam peak cnt ran
           most LAWS HRAN HX)))).
Qed.

End g.
End f.
End t7top.

(* the axioms the row rests on, printed into the build log (the Section hypotheses are crtB_T7's premises) *)
Print Assumptions crtB_T7.
