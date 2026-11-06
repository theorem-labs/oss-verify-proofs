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
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType.
Local Open Scope Z_scope.
(* measurement: the shared definitions of the BATCH-SAT joint witnesses (one constructed state) *)
Definition pre28 : list PresetReqAt.hev := firstn 28 (PresetRun.hruns K1BatchSat.sm6 K1BatchSat.x6 K1BatchSat.os6).
Definition S28 : astate :=
  mkA (repeat region0 32) false (repeat pclass0 32)
    (map (fun n => mkChunk PNull n CAllocated) (PresetReqAt.hlive pre28)) [] [] 0 qc0 qc0
    (mkFS (repeat 0 11) []) [] false 0.
Definition hist28 : list chunk := map (fun n => mkChunk PNull n CQuarantined) (PresetRun.hfrees pre28).
Definition mem0 : word -> option byte := fun _ => Some (Z_to_bv 8 0).
Lemma le_byte0 : forall w k, YG0f.le_byte 0 w k = 0.
Proof.
  intros w k. unfold YG0f.le_byte. rewrite Z.mod_0_l by (apply Z.pow_nonzero; lia).
  rewrite Z.shiftr_0_l. reflexivity.
Qed.
Lemma vz : forall segs a n, YI04.val_mem segs (YK04.mrestrict (fun _ => false) mem0) a n 0.
Proof. intros segs a n k _. unfold YP09.mbyte, YK04.mrestrict, mem0. rewrite le_byte0. reflexivity. Qed.
Definition W0 {fx : YK11.FPState} (segs : list Segment) : YA0n.world segs :=
  YA0n.mkW segs (fun _ => false) [] (fun a (H : false = true) => False_ind _ (diff_false_true H)) (Forall_nil _)
    (fun _ _ => eq_refl).
Section ly. Context {rc : YM05.RunCeil}.
Definition ly28 : alayout :=
  YG0f.ALayout 0 0 0 0 0 0 0 0 (YM05.alloc_ceiling + 0x10000) 0 0 0 [] [] 0 [] (0, 0) (fun _ => 0).
End ly.
