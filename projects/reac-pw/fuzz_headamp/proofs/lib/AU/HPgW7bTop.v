(* reac-pw/fuzz_headamp image B (fuzz_headamp.asan-ubsan, pinned sha256
   53edda9bdeeba1803865babfecb1af6732babe47ab83c64d38cc59a90d717a94; addresses measured on the unstripped twin
   1674e30a0698f381704e66d2398d7906c881f4ba8fc619cb41b89fb97ad112ff, same loaded bytes except .note.gnu.build-id): the walk of
   LLVMFuzzerTestOneInput (0x80c40) from G 0x81afc to J 0x82618 (HPgW7bBase.hw7b_core_stmt) from the lane's proved
   parts: blocks A1 / A2 (HPgW7bBlkA.v), B / C / D / E1 (HPgW7bBlkB.v), E2 (HPgW7bBlkE.v), the memcpy and strlen call
   steps and the two string sources (HPgW7bKit.v), one parts-loop turn (HPgW7bIter.v) and their composition
   (HPgW7bCore.v). Proves no function (kind: segment lemma).
   The two runtime entries the walk calls are premises of exact type: the strlen wrapper at its trampoline 0x41c18
   (lib/A/Rt/StrlenDef.v astrlen_realizes at STRLEN_ENTRY_B) and the runtime's memcpy at 0x51d8c
   (lib/Reusable/YG0d.v aintrin_realizes OCpy, as HPgCaseB.cb_memcpy_at takes it).
   hsu_piece_W7b_ok: lib/AU/HPgSeg.v's piece hsu_piece_W7b_stmt at headamp_himg_B / headamp_bld_B (cut G -> cut J),
   from hw7b_core_ok and the bridge HPgW7b.hsu_piece_W7b_of_core. *)
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YK11 YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d YG0q YI16 YM05.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.A.Rt Require Import StrlenDef.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.AU Require Import Img0U HPgW7bBase HPgW7bBlkA HPgW7bBlkB
  HPgW7bBlkE HPgW7bKit HPgW7bIter HPgW7bCore.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.AU Require Import HPgImgB HPgSteps HPgSeg HPgW7b.

Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.

Lemma hw7b_core_ok : forall B, astrlen_realizes rsegs B HW7B_STRLEN -> aintrin_realizes rsegs B OCpy HW7B_MEMCPY ->
hw7b_core_stmt B.
Proof.
intros B ASTR AMC.
exact (hw7b_core B (hw7b_A1 B) (hw7b_A2 B) (hw7b_C B) (hw7b_D B) (hw7b_E1 B) (hw7b_E2 B)
  (hw7b_iter B ASTR AMC (hw7b_B B)) (hw7b_memcpy_at B AMC) hw7b_strok_cstr hw7b_strok_ch).
Qed.

Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis MTL : ameter_laws MT.
Lemma hsu_piece_W7b_ok : astrlen_realizes rsegs B HW7B_STRLEN -> aintrin_realizes rsegs B OCpy HW7B_MEMCPY ->
hsu_piece_W7b_stmt rsegs B MT headamp_himg_B headamp_bld_B.
Proof. intros ASTR AMC. exact (hsu_piece_W7b_of_core B MT MTL (hw7b_core_ok B ASTR AMC)). Qed.
End b.

Print Assumptions hw7b_core_ok.
Print Assumptions hsu_piece_W7b_ok.
