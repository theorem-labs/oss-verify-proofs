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
Lemma i28e : YGcfFrees.cf_frees_follow [] (PresetRun.hfrees (firstn 28 (PresetRun.hruns K1BatchSat.sm6 K1BatchSat.x6 K1BatchSat.os6))) hist28.
Proof. unfold YGcfFrees.cf_frees_follow, hist28. rewrite map_map, app_nil_l. cbn [ck_req]. apply map_id. Qed.
