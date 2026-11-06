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
Section s. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {L : ptable asym} {PA : PAImg L}.
Lemma ledger28_A : prh_ledger (PI := PRH_Img.prh_img_A) (cp := CfParamsPreset.CfParams_preset) K1BatchSat.TA ly28 S28 []
  (W0 pa_segs) mem0 [] 0 0 0 0 0 0.
Proof.
  unfold prh_ledger, prh_glob, prh_most, prh_own. cbn [W0 YA0n.w_H].
  split; [|split; [constructor | split; [constructor | cbn [map]; constructor]]].
  split; [apply vz|]. split; [apply vz|]. split; [apply vz|]. split; [apply vz|]. split; [apply vz|].
  split; [split; [apply vz | lia]|]. split; [split; [apply vz | left; reflexivity]|].
  change (Ledger.lsum []) with 0. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. left; reflexivity.
Qed.
End s.
Print Assumptions ledger28_A.
