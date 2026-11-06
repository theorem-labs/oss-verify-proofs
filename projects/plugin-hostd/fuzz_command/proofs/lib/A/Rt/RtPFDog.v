(* dest_off_globals (the premise of RtPFCmd.v's asnprintf_sh / asprintf_sh at the image range 0x10000 .. 0x606000) for
   a destination in an ASan fake frame of S, through fuzz_manifest's dest_off_globals_of_fake (RtPFSx.v): the image hull
   covers the range (CmdImg.cmd_img_cover) and ends at or below the fake stack (hull_below_F, from the layout's
   disjointness), and a frame of S starts above the fake stack's base (frame_facts). Nine of fuzz_command's ten
   printf destinations are such frames (measured at each call site in the image's listing). *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK11 YK0s YK0i YK15 YK0j YK18 YP09.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG0s YG0t YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A Require Import AB1v.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import CmdList CmdPa CmdImg.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Rt Require Import RtPFSx RtPFCmd.
Import ListNotations.
Local Open Scope Z_scope.

(* over any image instance of fuzz_command's listing (the walks' PI; pa_img_cover, CmdPa.v): the forms the
   answer walk (answer_br.v br_frame_above_img) and the check_words_chain walk (cwc_frame_above_img)
   proved locally; the tfibsegs lemmas below are their PB_cmd instances *)
Section g. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {PI : PAImg cmd_listing}.
#[local] Notation SEGS := (@pa_segs _ cmd_listing PI).
Variable B : asyms.
(* the fake stack lies above the image's range *)
Lemma pa_fake_above_img : forall ly S (W : world SEGS) mem md,
  AR SEGS B ly S W mem md -> CMD_IMG_HI <= ly_F ly.
Proof.
intros ly S W mem md (M & LG & _).
pose proof (pa_img_cover ly S md LG) as [_ C2]. pose proof (hull_below_F ly (am_layout _ _ _ _ M)) as HF.
unfold CMD_IMG_HI. lia.
Qed.
(* every fake frame of S lies above the image's range *)
Lemma pa_frame_above_img : forall ly S (W : world SEGS) mem md cid pos,
  AR SEGS B ly S W mem md -> In (cid, pos) (frames S) -> CMD_IMG_HI <= frame_addr ly cid pos.
Proof.
intros ly S W mem md cid pos HA Hin.
pose proof (pa_fake_above_img ly S W mem md HA) as HF.
destruct HA as (M & _ & _).
pose proof (frame_facts B ly S _ cid pos M Hin) as (Fc & _ & _ & _ & _ & P1 & _).
pose proof (Z.mul_nonneg_nonneg cid (2 ^ 20) ltac:(lia) ltac:(lia)) as CN.
unfold frame_addr, kFakeFramesOff in *. lia.
Qed.
(* a destination at or above a fake frame of S *)
Lemma pa_dest_off_globals_frame : forall ly S (W : world SEGS) mem md cid pos d w,
  AR SEGS B ly S W mem md -> In (cid, pos) (frames S) -> frame_addr ly cid pos <= d ->
  zdisjoint (d, w) (CMD_IMG_LO, CMD_IMG_HI - CMD_IMG_LO).
Proof.
intros ly S W mem md cid pos d w HA Hin Hd.
pose proof (pa_fake_above_img ly S W mem md HA) as HF.
destruct HA as (M & _ & _).
pose proof (frame_facts B ly S _ cid pos M Hin) as (Fc & _ & _ & _ & _ & P1 & _).
pose proof (Z.mul_nonneg_nonneg cid (2 ^ 20) ltac:(lia) ltac:(lia)) as CN.
apply (dest_off_globals_of_fake (ly_F ly) d w CMD_IMG_LO CMD_IMG_HI HF).
unfold frame_addr, kFakeFramesOff in *. lia.
Qed.
End g.

Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : asyms.
(* the fake stack lies above the image's range *)
Lemma cmd_fake_above_img : forall ly S (W : world tfibsegs) mem md,
  AR tfibsegs B ly S W mem md -> CMD_IMG_HI <= ly_F ly.
Proof. exact (pa_fake_above_img (PI := PB_cmd) B). Qed.
(* a destination at or above a fake frame of S *)
Lemma cmd_dest_off_globals_frame : forall ly S (W : world tfibsegs) mem md cid pos d w,
  AR tfibsegs B ly S W mem md -> In (cid, pos) (frames S) -> frame_addr ly cid pos <= d ->
  zdisjoint (d, w) (CMD_IMG_LO, CMD_IMG_HI - CMD_IMG_LO).
Proof. exact (pa_dest_off_globals_frame (PI := PB_cmd) B). Qed.
End b.
