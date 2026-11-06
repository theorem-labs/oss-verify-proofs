(* a measurement file (BATCH-SAT joint witnesses); it proves no function *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
  YK11 YM05 YG00 YG01 YG0f YG0d YGcfNames YP0b YPsym YC4aP.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YCbqGwild YGcfRoom YGcfFrees YGcfRoomLive.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YD2l YCej YI04 YP09 YK04 YA0n YG0n.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Base.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require PRH_Img CfImgA AD2l ACej CfParamsPreset.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require PRH_FnTx PRH_FnPj K1BatchSat.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PresetRoomPos PresetRun PresetReqAt
  PresetLiveBounds PresetRoom.
Import ListNotations.
Local Open Scope Z_scope.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import K1JBase.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType.
Local Open Scope Z_scope.
Definition S24 : astate :=
  mkA (repeat region0 32) false (repeat pclass0 32) (repeat (mkChunk PNull 7000 CAllocated) 146223) [] [] 0 qc0 qc0
    (mkFS (repeat 0 11) []) [] false 0.
Theorem counts_ctl_24 : ~ (YGcfRoomLive.ccnt24 S24 <= PresetLiveBounds.L24 + PresetLiveBounds.DRV).
Proof.
  assert (E : YGcfRoomLive.ccnt24 S24 = 146223) by (vm_compute; reflexivity).
  rewrite E, PresetLiveBounds.L24_value. unfold PresetLiveBounds.DRV. lia.
Qed.
Print Assumptions counts_ctl_24.
