(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Image B' (pin d663f82d), the #102 kit: ex_word's text is the kit's tex_word_specX, discharged by the PROVED
   B' walk ExwB.ex_word_holds_B from EXV_HYP's eh_laws, eh_palib, eh_strlen and eh_bcmp. *)
(* Theorem Labs, 2026-10: fuzz_preset, image B (asan-ubsan, rebuilt pin f8f98a95bc52, unstripped twin 3b5e1a099b53),
   ex_value, segment C1 DISP (lane ExvDisp): THE SEGMENT LEMMA exvB_disp = ExvB_Top.v's Section hypothesis seg_disp
   with EXV_HYP added: from CUT_C1 (exv_pc 0x11c = B 0x83648) every run ends in EXV_POST, given CUT_CX, CUT_CN and
   CUT_CI at every float state. Composed from
   - lib/B/Prog/ExvB_Disp_run.v exvd_c1_all: the dispatch run (end of text, switch on the byte) to CUT_CX / CUT_CN /
     CUT_CI and to the two arm entries;
   - lib/B/Prog/ExvB_Disp_str.v exvd_str_holds: the string arm (ex_string, v->type, strcmp, in->differs) to CUT_CX;
   - lib/B/Prog/ExvB_Disp_word.v exvd_word_holds: the word arms (ex_word on true / false / null) to CUT_CX.
   Rule 24: proves no function (kind: segment lemma). No numeral. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK0s YK0o YK15 YK18 YP09 YK04 YA0i YA0n YG00 YG0a YG01 YG0f YG0v YG0n YG0d YCbq YI00 YI04 YI16 YK06 YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfNames YCbqG YP0b YPsym YC4aP.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Base PRH_FnEx.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B Require Import PRH_ImgB Img0 Listing_prog PAImg_prog.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require ExwB.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require Import ExvB_Stmt ExvB_Disp_arms.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require ExvB_Disp_run ExvB_Disp_str ExvB_Disp_word.
Import ListNotations.
Local Open Scope Z_scope.

#[local] Existing Instance prh_img_B.

Lemma exvB_disp : forall {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams} {RL : PrhRoomLive} B ARx SK,
  EXV_HYP B ARx SK ->
  forall n,
  (forall fx : YK11.FPState, CUT_CX (fx := fx) B ARx SK n) -> (forall fx : YK11.FPState, CUT_CN (fx := fx) B ARx SK n) ->
  (forall fx : YK11.FPState, CUT_CI (fx := fx) B ARx SK n) ->
  forall fx : YK11.FPState, CUT_C1 (fx := fx) B ARx SK n.
Proof.
intros rc ci cp RL B ARx SK HYP n CX CN CI.
(* ex_word: K0's tex_word_specX at B', by h-pre-b3's PROVED walk ex_word_holds_B (origin/cold/h-pre-b3-exword-bp
   e03676c00314, ExwB.v 56c3b5d735d4; Section inputs LAWS, PAL, STRLENm := eh_strlen, BCMPm := eh_bcmp) *)
pose proof (fun fx : YK11.FPState => ExwB.ex_word_holds_B (fx := fx) B ARx SK
  (eh_laws B ARx SK HYP) (eh_palib B ARx SK HYP) (eh_strlen B ARx SK HYP fx) (eh_bcmp B ARx SK HYP fx)) as EHW.
exact (ExvB_Disp_run.exvd_c1_all B ARx SK HYP n CX CN CI
  (ExvB_Disp_str.exvd_str_holds B ARx SK HYP n CX)
  (ExvB_Disp_word.exvd_word_holds B ARx SK HYP EHW n CX)).
Qed.

Print Assumptions exvB_disp.
