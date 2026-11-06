(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs, 2026-10: image B (asan-ubsan) instance of lib/Reusable/YStrtodRowX.v's strtod call-site row,
   discharged from lib/B/Prog/strtod_x.v's strtod_x_holds; the image constants are lib/B/Prog/strtod_c.v's. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK0s YK04 YK0o YA0i YA0n YG00 YG0a YG01 YG0d YG0f YG0n YG0p YG0v YI16 YM05 YI00 YI04 YCbq YCbqG FCiface YStrtodRowX.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B Require Import Img0.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require Import strtod_c strtod_x.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.CJ.Spec Require FloatScan.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.CJ.P Require FmtFp_facts3.
Import ListNotations.
Open Scope Z_scope.

Definition strtod_img_B : strtod_img :=
  MkStrtodImg STRTOD_K STRTOD_TP STRTOD_ERRNO STRTOD_GOT_GUARD STRTOD_GUARD STRTOD_GLOBALS_TOP STRTOD_IMG_LO.

Lemma strtod_model_scan_B : forall txt, strtod_model txt = FloatScan.scan_strtod (txt ++ [0]).
Proof. intros txt. reflexivity. Qed.

Lemma strtod_got_B : srx_got_b rsegs STRTOD_GOT_GUARD STRTOD_GUARD = true.
Proof. vm_compute. reflexivity. Qed.

Lemma strtod_cells_B : srx_cells_b rsegs STRTOD_GOT_GUARD 8 = true /\ srx_cells_b rsegs STRTOD_GUARD 8 = true /\
  srx_cells_b rsegs STRTOD_ERRNO 4 = true.
Proof. split; [vm_compute; reflexivity|]. split; vm_compute; reflexivity. Qed.

Lemma strtod_low_B : forall a, in_img rsegs a -> 0 <= a < kLowMemEnd.
Proof. apply (srx_segs_low rsegs). vm_compute. reflexivity. Qed.

Lemma strtod_ok_B : forall {rc : YM05.RunCeil}, si_globals_top strtod_img_B <= alloc_ceiling /\
  0 <= si_got_guard strtod_img_B /\ si_got_guard strtod_img_B + 8 <= 2 ^ 62 /\
  0 <= si_guard strtod_img_B /\ si_guard strtod_img_B + 8 <= 2 ^ 62 /\
  0 <= si_errno strtod_img_B /\ si_errno strtod_img_B + 4 <= 2 ^ 62.
Proof.
intros rc. pose proof asan_consts as (C1 & _).
cbn [si_globals_top si_got_guard si_guard si_errno strtod_img_B].
unfold STRTOD_GLOBALS_TOP, STRTOD_GOT_GUARD, STRTOD_GUARD, STRTOD_ERRNO. repeat split; lia.
Qed.

Lemma strtod_text_B : forall {fx : YK11.FPState} ainv aown,
  strtod_frame_g rsegs ainv aown -> strtod_contract_g rsegs strtod_img_B strtod_model ainv aown STRTOD.
Proof. intros fx ainv aown HF. exact (strtod_x_holds ainv aown HF). Qed.

Theorem strtod_row_B : forall {fx : YK11.FPState} {rc : YM05.RunCeil} {HL : Z} (B : asyms)
  (ARx : alayout -> astate -> list Z -> world rsegs -> (word -> option byte) -> Model -> Prop),
  AR_laws_x rsegs B ARx HL ->
  as_tp B = STRTOD_TP -> as_errno B = STRTOD_ERRNO ->
  (forall a, as_errno B <= a < as_errno B + 4 -> ~ Exists (in_zr a) (as_owned_static B)) ->
  forall STKS sm txt_ok, STRTOD_K <= STKS ->
  (forall txt, txt_ok txt -> Forall (fun c => FmtFp_facts3.is_numch c = true) txt /\ Z.of_nat (length txt) < 2 ^ 30) ->
  (forall txt bits c, txt_ok txt -> strtod_model txt = Some (bits, c) -> sm txt = Some (bits, c)) ->
  astrtod_realizes_x rsegs B ARx strtod_img_B STRTOD STKS sm txt_ok.
Proof.
intros fx rc HL B ARx LAWS Htp Herr Hown STKS sm txt_ok HK HTX HSM.
exact (astrtod_realizes_x_of rsegs B ARx strtod_img_B LAWS Htp Herr Hown strtod_got_B strtod_cells_B strtod_ok_B
  STRTOD strtod_model (@strtod_text_B fx) STKS sm txt_ok HK HTX HSM).
Qed.

Theorem strtod_row_aj_B : forall {fx : YK11.FPState} {rc : YM05.RunCeil} {HL : Z} (SK : YI16.sink_head) (B : asyms)
  (PST : list (Z * Z)) (ARx : alayout -> astate -> list Z -> world rsegs -> (word -> option byte) -> Model -> Prop),
  AR_laws_x rsegs B ARx HL ->
  as_tp B = STRTOD_TP -> as_errno B = STRTOD_ERRNO ->
  (forall a, as_errno B <= a < as_errno B + 4 -> ~ Exists (in_zr a) (as_owned_static B)) ->
  forall STKS sm txt_ok, STRTOD_K <= STKS ->
  (forall txt, txt_ok txt -> Forall (fun c => FmtFp_facts3.is_numch c = true) txt /\ Z.of_nat (length txt) < 2 ^ 30) ->
  (forall txt bits c, txt_ok txt -> strtod_model txt = Some (bits, c) -> sm txt = Some (bits, c)) ->
  aj_strtod_row (SK := SK) rsegs B ARx strtod_img_B PST STRTOD STKS sm txt_ok.
Proof.
intros fx rc HL SK B PST ARx LAWS Htp Herr Hown STKS sm txt_ok HK HTX HSM.
assert (EI : forall a, as_errno B <= a < as_errno B + 4 -> in_img rsegs a).
{ intros a Ha. rewrite Herr in Ha.
  exact (srx_cell_img rsegs a (srx_cells_b_sound rsegs STRTOD_ERRNO 4 a (proj2 (proj2 strtod_cells_B)) Ha)). }
apply (aj_strtod_at_x (SK := SK) rsegs B ARx strtod_img_B PST LAWS strtod_low_B EI STRTOD STKS sm txt_ok
  (strtod_row_B B ARx LAWS Htp Herr Hown STKS sm txt_ok HK HTX HSM)).
unfold ESTACK, STRTOD_K in *. lia.
Qed.
