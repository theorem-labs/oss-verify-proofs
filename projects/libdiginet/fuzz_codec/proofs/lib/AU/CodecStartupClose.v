(* The start-up facts of lib/AU/CodecStartupFacts.v at fuzz_codec.asan-ubsan's start-up record TfibB (lib/AU/YD2l.v),
   with no premise left, as lib/A/CodecStartupClose.v does for image A: HZS and HCONST hold of TfibB by conversion,
   because TFIB_ZERO_SHADOW_B and TFIB_CONST_SHADOW_B are lib/AU/YF0m.v's Tfib_zero_shadow and Tfib_const_shadow. *)
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YK11 YM05 YG00 YG0f YG0n.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.AU Require Import YF0l YF0m YD2l.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.AU.Prog Require Import CodecRo CodecGlobs.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.AU Require Import CodecStartupFacts.
Import ListNotations.
Local Open Scope Z_scope.

Lemma tfib_zsh_copy : as_zero_shadow TfibB = TFIB_ZERO_SHADOW_B.
Proof. reflexivity. Qed.

Lemma tfib_const_copy : forall ly, exists pre, as_const TfibB ly = pre ++ TFIB_CONST_SHADOW_B.
Proof.
intros ly. exists (Tfib_const_sym ++ Tfib_const_abs).
change (as_const TfibB ly) with (Tfib_const_sym ++ Tfib_const_abs ++ Tfib_const_shadow).
change TFIB_CONST_SHADOW_B with Tfib_const_shadow. apply app_assoc.
Qed.

Section C. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
(* GM at the start-up record: each of the 40 registered globals is marked, in every AR state. *)
Lemma codec_GM_TfibB : forall segs, globs_marked segs TfibB CODEC_GLOBS.
Proof. intros segs. exact (codec_GM segs TfibB tfib_zsh_copy tfib_const_copy). Qed.

(* IV at the start-up record: every shadow byte of the image's read range is mapped, in every AR state. *)
Lemma codec_IV_TfibB : forall segs, img_shadow_vis segs TfibB.
Proof. intros segs. exact (codec_IV segs TfibB tfib_zsh_copy tfib_const_copy). Qed.
End C.
