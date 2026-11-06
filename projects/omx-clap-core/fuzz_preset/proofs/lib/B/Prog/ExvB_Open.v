(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Rebound onto the old-pin kit 4f18c75d4900 (base cold/h-rw-pre-7-b-ex_value-rebind): EXB carries exv_rm, the
   memnorm keep from the entry memory, across every run by ExvB_Loop_exw.v's _inv runners at P := exvl_P (e_mem E)
   and across the ex_ws call by its m-form post. Does not rest on tex_word_specX. *)
(* Theorem Labs, 2026-10: fuzz_preset, image B (asan-ubsan), ex_value, SEGMENT CI (container open, B entry + 0x374 =
   0x838a0 .. 0x83a5c): exvB_open = ExvB_Top.v's seg_open with EXV_HYP. The segment, by its internal cuts
   (ExvB_Open_fin.v):
   - CI -> CX | CUT_CM (entry + 0x440): in->depth := dep + 1, refused at depth 32 (exo_front1 / exo_front0,
     ExvB_Open_f1.v), else the node type check (v <> 0) and 152(s1) := vv;
   - CUT_CM -> CUT_CR (entry + 0x460): in->p := p + 1, the ex_ws call (exo_mid, ExvB_Open_mid.v);
   - CUT_CR -> CC | CL: the closer test after the whitespace, the loop-init spills (exo_cr, ExvB_Open_cr.v).
   The functional reading is PjGrammar.jr_cont (ExvB_Open_pure.v). Rule 24: proves no function (kind: segment lemma).
   Numerals: 0 (WORD: the C NULL node). No ADDRESS. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK0s YK0o YK15 YK18 YP09 YK04 YA0i YA0n YG00 YG0a YG01 YG0f YG0v YG0n YG0d YCbq YI00 YI04 YI16 YK06 YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfNames YCbqG YP0b YPsym YC4aP.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import FCiface YGcfRoomKeep.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Base PRH_FnEx.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B Require Import PRH_ImgB Img0 Listing_prog PAImg_prog.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require Import
ExvB_Stmt ExvB_Open_fin ExvB_Open_f1 ExvB_Open_mid ExvB_Open_cr.
Import ListNotations.
Local Open Scope Z_scope.

#[local] Existing Instance prh_img_B.

Lemma exvB_open : forall {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams} {RL : PrhRoomLive} (B : asyms)
  (ARx : alayout -> astate -> list Z -> world rsegs -> (word -> option byte) -> Model -> Prop) (SK : YI16.sink_head),
  EXV_HYP B ARx SK ->
  forall n,
  (forall fx : YK11.FPState, CUT_CX (fx := fx) B ARx SK n) -> (forall fx : YK11.FPState, CUT_CC (fx := fx) B ARx SK n) ->
  (forall fx : YK11.FPState, CUT_CL (fx := fx) B ARx SK n) ->
  forall fx : YK11.FPState, CUT_CI (fx := fx) B ARx SK n.
Proof.
intros rc ci cp RL B ARx SK HYP n HX HC HL fx.
assert (HCR : CUT_CR (fx := fx) B ARx SK n) by exact (exo_cr B ARx SK HYP n (HC fx) (HL fx)).
assert (HCM : CUT_CM (fx := fx) B ARx SK n) by exact (exo_mid B ARx SK HYP n HCR).
unfold CUT_CI.
intros E lyc Sc Hpc Wc regs memc mdc k pos c Hn HPRE HB Hcur Hi1 Hnth Hc R10 R11 R27 R21 R20 R22 R23 S144 S152.
destruct (Z.eq_dec (e_v E) 0) as [Hv|Hv].
- exact (exo_front0 B ARx SK HYP n (HX fx) HCM E lyc Sc Hpc Wc regs memc mdc k pos c Hn HPRE HB Hcur Hi1 Hnth Hc
    R10 R11 R27 R21 R20 R22 R23 S144 S152 Hv).
- exact (exo_front1 B ARx SK HYP n (HX fx) HCM E lyc Sc Hpc Wc regs memc mdc k pos c Hn HPRE HB Hcur Hi1 Hnth Hc
    R10 R11 R27 R21 R20 R22 R23 S144 S152 Hv).
Qed.

Print Assumptions exvB_open.
