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
Lemma trace28_A : YM05.alloc_ceiling < ly_top ly28 /\
  PRH_FnTx.prhtx_trace (ci := CfImgA.CfImg_A) (PI := PRH_Img.prh_img_A) K1BatchSat.TA ly28 (W0 pa_segs) mem0 YM05.alloc_ceiling.
Proof.
  split; [unfold ly28; cbn [ly_top]; lia|]. intros _. split.
  - intros a _. unfold YG0n.aview, YP09.mbyte, YK04.mrestrict, mem0, W0. cbn [YA0n.w_H option_map]. discriminate.
  - intros rd ch _ _. apply K1BatchSat.tx_chain_inU_A.
Qed.
End s.
Print Assumptions trace28_A.
