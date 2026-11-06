From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK11 YK15 YK18 YP0n YM02 YP0m YP09 YP0l YP06 YP08 YP03 YN3q YN3v YK04 YA0i YA0n YA0e YG00 YG0a YG01 YG0k YG0f YG0v YG0n YG0d.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05 YA0nH YA0oR.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YGcfNames.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import AB1v AD1vcf.

Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.

(* stk_up (AD1vcf.v) at a world step that may hide more at DS (wle_in, YA0nH.v; wle' = wle_in RZ): every byte of
   [usp, ly_top ly) that reads through the view at W reads through it at W' when it lies outside DS. *)
Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {ci : YGcfNames.CfImg} {cp : YGcfNames.CfParams}.

Lemma stk_up_wle_in_off : forall (DS : Z -> Prop) (W W' : world tfibsegs) usp ly mem,
  wle_in tfibsegs DS W W' ->
  (forall a, usp <= a < ly_top ly -> ~ DS (bv_unsigned (Z_to_bv 64 a))) ->
  stk_up usp ly W mem -> stk_up usp ly W' mem.
Proof.
  intros DS W W' usp ly mem H Hn HU a Ha. exact (aview_wle_in_off' tfibsegs DS W W' mem a H (Hn a Ha) (HU a Ha)).
Qed.
End b.
