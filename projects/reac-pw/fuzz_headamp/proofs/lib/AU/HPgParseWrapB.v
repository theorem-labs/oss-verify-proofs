(* reac-pw/fuzz_headamp image B (fuzz_headamp.asan-ubsan, pinned sha256
   53edda9bdeeba1803865babfecb1af6732babe47ab83c64d38cc59a90d717a94): reac_headamp_prop_parse 0x849a4, the 8-byte
   wrapper `mv a3,zero; j 0x849ac` (words 0x00000693, 0x0040006f, checked against the image's segments by computation
   below), level-3 identical to image A's 0x845ac. hd_parse_specX at 0x849a4 follows from hd_parse_result_specX at
   0x849ac by lib/A/HPgParseWrap.v's image-independent hp_parse_of_result (the port of headamp's plain
   reac_headamp_prop_parse_of_result to this engine). Proves function reac_headamp_prop_parse of image B from the
   contract of reac_headamp_prop_parse_result. *)
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YK11 YK0s YK15 YK18 YP09 YI04 YI00.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YK04 YA0i YA0n YP02.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.A Require Import HPgBase HPgCSpec.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.A Require HPgParseWrap.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.AU Require Import Img0U HPgImgB HPgParseCut.
Import ListNotations.
Open Scope Z_scope.

(* the wrapper's two words at 0x849a4 / 0x849a8 *)
Lemma pb_wrap_words : fetch_word rsegs (w64 PB_WRAP) = Some (Z_to_bv 32 0x00000693) /\
  fetch_word rsegs (w64 (PB_WRAP + 4)) = Some (Z_to_bv 32 0x0040006f).
Proof. split; vm_compute; reflexivity. Qed.

Section f. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Variable B : asyms.
Variable MT : ameter_ops.

Theorem hp_parse_of_result_B : forall RLO RHI akey aph apad asens gotw guard dcs,
hd_parse_result_specX rsegs B MT B_PARSE_RESULT RLO RHI akey aph apad asens gotw guard dcs ->
hd_parse_specX rsegs B MT PB_WRAP RLO RHI akey aph apad asens gotw guard dcs.
Proof.
intros RLO RHI akey aph apad asens gotw guard dcs H. destruct pb_wrap_words as [W0 W4].
apply (HPgParseWrap.hp_parse_of_result B MT rsegs PB_WRAP pb_wx pb_segs_low W0 W4).
replace (PB_WRAP + 8) with B_PARSE_RESULT by (unfold PB_WRAP, B_PARSE_RESULT; lia).
exact H.
Qed.
End f.

Print Assumptions hp_parse_of_result_B.
