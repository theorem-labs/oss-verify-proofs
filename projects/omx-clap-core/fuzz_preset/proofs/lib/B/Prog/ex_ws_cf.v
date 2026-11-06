(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs, 2026-10: ex_ws of fuzz_preset's image B' (#102 pin d663f82d7f488d30; lib/B/Prog/ex_ws_x.v's
   ex_ws_holds_x) at preset's allocator instance: h-mani-a8's ARcf and the generic rules' instance ARcf /\ xs_placed_cf
   (YGcallcf.v 6d2b13c24437, engine set of record origin/cold/c-omx-alloc-preset-s1b 8a01e111a410 on YCbqG
   c3b5d0111037). AR_laws_x (head length cf_head) from AR_laws_ok_cf (YG0lawscf.v) through YGcallcf's AR_laws_x_cf /
   AR_laws_x_xs. K0's text tex_ws_specX is the #102 kit's (origin/cold/h-hpreset-7-walkkit-next decff67d721f, PRH_FnEx
   45ddb7a7d5ae): m-form post fpostWm, S' = S, ledger with most / own.
   ex_ws_holds_cf / ex_ws_holds keep the two image facts of B (asyms) the walk reads, as_got_shadow B and
   as_shadow_cell B (the atoms A_OBJ 0 / A_OBJ 12 of PI_prog_B), and the PrhRoomLive instance RL as hypotheses.
   ex_ws_holds_B discharges them at the B' instance: B := YD2l.TfibB (95803a8b9493), cp := CfParams_preset,
   RL := prh_room_live_a8, ARx := ARcf /\ xs_placed_cf; each image fact by vm_compute (exw_got_TfibB,
   exw_cell_TfibB). ex_ws makes no allocator call: its post's room_live_cf S -> room_live_cf S' holds with S' = S.
   No numeral. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK11 YM05 YI16 YG0f YCbqG YGcfNames.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YG0ncf YG0lawscf YGcallcf YD2l.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require CfParamsPreset.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Base PRH_FnEx.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B Require Import Img0 Listing_prog PAImg_prog PRH_ImgB.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require Import ex_ws_x.

(* ex_ws at image B and ARcf *)
Theorem ex_ws_holds_cf : forall {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams}
(SK : YI16.sink_head) (B : asyms) {RL : PrhRoomLive},
as_got_shadow B = EXW_GOT -> as_shadow_cell B = EXW_CELL ->
tex_ws_specX (PI := prh_img_B) (L := B_prog_listing) (PA := PI_prog_B) B
(fun ly S Hp W mem md => YG0ncf.ARcf rsegs B ly S Hp W mem md) SK.
Proof.
intros fx rc ci cp SK B RL HGOT HCELL.
exact (ex_ws_holds_x SK B _ (YGcallcf.AR_laws_x_cf rsegs B (YG0lawscf.AR_laws_ok_cf rsegs B)) HGOT HCELL).
Qed.

(* ex_ws at image B and the generic rules' cf instance ARcf /\ xs_placed_cf *)
Theorem ex_ws_holds : forall {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams}
(SK : YI16.sink_head) (B : asyms) {RL : PrhRoomLive},
as_got_shadow B = EXW_GOT -> as_shadow_cell B = EXW_CELL ->
tex_ws_specX (PI := prh_img_B) (L := B_prog_listing) (PA := PI_prog_B) B
(fun ly S Hp W mem md => YG0ncf.ARcf rsegs B ly S Hp W mem md /\ YG0ncf.xs_placed_cf ly S) SK.
Proof.
intros fx rc ci cp SK B RL HGOT HCELL.
exact (ex_ws_holds_x SK B _ (YGcallcf.AR_laws_x_xs rsegs B (YG0lawscf.AR_laws_ok_cf rsegs B)) HGOT HCELL).
Qed.

(* the two image facts at B' (YD2l.TfibB against the B' listing's atoms A_OBJ 0 / A_OBJ 12), by computation *)
Lemma exw_got_TfibB : as_got_shadow YD2l.TfibB = EXW_GOT.
Proof. vm_compute. reflexivity. Qed.
Lemma exw_cell_TfibB : as_shadow_cell YD2l.TfibB = EXW_CELL.
Proof. vm_compute. reflexivity. Qed.

(* ex_ws at the B' instance: B := TfibB, preset's CfParams, a8's room invariant, ARx := ARcf /\ xs_placed_cf *)
Theorem ex_ws_holds_B : forall {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} (SK : YI16.sink_head),
tex_ws_specX (cp := CfParamsPreset.CfParams_preset) (PI := prh_img_B)
  (RL := prh_room_live_a8 (cp := CfParamsPreset.CfParams_preset)) (L := B_prog_listing) (PA := PI_prog_B) YD2l.TfibB
  (fun ly S Hp W mem md => YG0ncf.ARcf (cp := CfParamsPreset.CfParams_preset) rsegs YD2l.TfibB ly S Hp W mem md /\
     YG0ncf.xs_placed_cf ly S) SK.
Proof.
intros fx rc ci SK.
exact (ex_ws_holds_x (cp := CfParamsPreset.CfParams_preset) (RL := prh_room_live_a8 (cp := CfParamsPreset.CfParams_preset))
  SK YD2l.TfibB _
  (YGcallcf.AR_laws_x_xs (cp := CfParamsPreset.CfParams_preset) rsegs YD2l.TfibB
     (YG0lawscf.AR_laws_ok_cf (cp := CfParamsPreset.CfParams_preset) rsegs YD2l.TfibB))
  exw_got_TfibB exw_cell_TfibB).
Qed.
