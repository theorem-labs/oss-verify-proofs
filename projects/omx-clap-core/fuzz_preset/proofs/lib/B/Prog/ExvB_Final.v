(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* ex_word by h-pre-b3's verbatim ExwB.ex_word_holds_B; memnorm threaded in the statements (EXB's exv_rm keep, m-form
   callee posts); no memnorm premise. *)
(* Theorem Labs, 2026-10: fuzz_preset, image B, ex_value: THE WALK, closed. ExvB_Top.v's ex_value_holds_B with its seven
   segment hypotheses discharged by the seven PROVED segment lemmas:
     seg_entry  ExvB_Entry.v  exvB_entry   (C0, B 0x8352c)
     seg_disp   ExvB_Disp.v   exvB_disp    (C1, +0x11c)
     seg_num    ExvB_Num.v    exvB_num     (CN, +0x278)
     seg_open   ExvB_Open.v   exvB_open    (CI, +0x374)
     seg_loop   ExvB_Loop.v   exvB_loop    (CL, +0x534; the recursive call at the text n - 1)
     seg_close  ExvB_Close.v  exvB_close   (CC, +0x9f8)
     seg_exit   ExvB_Exit.v   exvB_exit    (CX, +0xa7c)
   What remains open, by name: EXV_HYP B ARx SK only - the callee texts (eh_string: S8b; eh_strcmp / eh_strlen:
   c-libc-stdio's read-only-premise m-rows; eh_bcmp / eh_memcpy / eh_sm1: YGcallMxmn m-rows) and the laws and image facts
   (at the instance B := TfibB, ARx := ARcf, every image fact and allocator law is PROVED in ExvB_ImgFacts.v / PALibB.v).
   Kit of record: the kit's cut 7cdbb61b5fa0 (PRH_FnEx be1dd5ecaaf6: tex_value_specX with the memnorm entry premise and the
   fpostWFm post; the draft's tex_value_specX (PRH_FnEx.v:292), which ex_value_holds_B_final proves, adds, at PRH_FnEx.v:335,
   the hull use with no events, both secondary-map meters kept; PRH_Base ef7c8ca98529: src_rd without int102's `+ 8`, so the
   walk's bound on the text is `x0 + len <= alloc_ceiling` (ExvB_NumA exa_facts, ExvB_Loop_A2_w a2_seat, ExvB_Loop_B2_post)).
   Rule 24: proves function ex_value (image B) GIVEN the premises above; no released ASan-form walk of preset's
   ex_value exists (the internal file idx-ex_value.txt, the internal file RULE24-CHECK-B6.md CONFIRM). No numeral. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK0s YK0o YK15 YK18 YP09 YK04 YA0i YA0n YG00 YG0a YG01 YG0f YG0v YG0n YG0d YCbq YI00 YI04 YI16 YK06 YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfNames YCbqG YP0b YPsym YC4aP.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Base PRH_FnEx.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B Require Import PRH_ImgB Img0 Listing_prog PAImg_prog.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require Import ExvB_Stmt ExvB_Top.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require
  ExvB_Entry ExvB_Disp ExvB_Num ExvB_Open ExvB_Loop ExvB_Close ExvB_Exit.
Local Open Scope Z_scope.

#[local] Existing Instance prh_img_B.

Theorem ex_value_holds_B_final : forall {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams} {RL : PrhRoomLive}
  (B : asyms) (ARx : alayout -> astate -> list Z -> world rsegs -> (word -> option byte) -> Model -> Prop)
  (SK : YI16.sink_head),
  EXV_HYP B ARx SK ->
  forall n (fx : YK11.FPState), tex_value_specX (fx := fx) (PA := PI_prog_B) B ARx SK n.
Proof.
intros rc ci cp RL B ARx SK HYP n fx.
apply (ex_value_holds_B B ARx SK).
- exact (ExvB_Exit.exvB_exit B ARx SK HYP).
- exact (ExvB_Close.exvB_close B ARx SK HYP).
- exact (ExvB_Loop.exvB_loop B ARx SK HYP).
- exact (ExvB_Open.exvB_open B ARx SK HYP).
- exact (ExvB_Num.exvB_num B ARx SK HYP).
- exact (ExvB_Disp.exvB_disp B ARx SK HYP).
- exact (ExvB_Entry.exvB_entry B ARx SK HYP).
Qed.

Print Assumptions ex_value_holds_B_final.
