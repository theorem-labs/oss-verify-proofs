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
Lemma tx3_A :
  YCbqGwild.wild_room (as_universe K1BatchSat.TA) [] (length (PRH_FnTx.prhtx_evs 0 0 [0])) (st_depot S28) /\
  prh_cons_from K1BatchSat.sm6 K1BatchSat.x6 K1BatchSat.os6 28 (length (PRH_FnTx.prhtx_evs 0 0 [0])) /\
  nth_error (PresetRun.hruns K1BatchSat.sm6 K1BatchSat.x6 K1BatchSat.os6) 28 = Some (PresetReqAt.HMal 2) /\
  blocks_bytes S28 + PRH_FnTx.LIVE_tx <= LIVE_MAX /\ 2 < @cf_malloc_max CfParamsPreset.CfParams_preset.
Proof.
  split; [apply YCbqGwild.wild_room_of_count; vm_compute; lia|].
  split; [apply K1BatchSat.cons_fromb_ok; vm_compute; reflexivity|].
  split; [vm_compute; reflexivity|]. split; [apply Z.leb_le | apply Z.ltb_lt]; vm_compute; reflexivity.
Qed.
Print Assumptions tx3_A.
