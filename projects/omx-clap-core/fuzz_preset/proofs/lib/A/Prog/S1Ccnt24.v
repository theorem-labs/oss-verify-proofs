(* fuzz_preset, S1 ALLOC-HEAP (lib/A/Prog): the live class-24 count across one free, for S1's two fuzz_free walks
   (FuzzFree.v, FuzzFreeB.v: tfuzz_free_specX's ccnt24 arm). The two lemmas, prh_ccnt24_ablocks (:18) and prh_ccnt24_free (:22),
   were section 6 of S1Ledger.v on a working branch (as S1Ledger.v:851-862 at 67637094dec6); S1Ledger.v here is decff67d721f's file with comments edited in this series,
   and it still carries neither prh_ccnt24_ablocks nor prh_ccnt24_free, so they live here, unchanged.
   YGcfRoomLive.ccnt24 reads map snd (blocks S), which equals map snd (ablocks B ly S) (ablocks renames the pointers
   only), so the free's block equation (aj_free_x_ct's post) gives the count exactly. No image, no address. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Lia.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK11 YM05 YG00 YG0f YG0d.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcfRoomLive.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PresetRoom.
Import ListNotations.
Local Open Scope Z_scope.

Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : asyms.

Lemma prh_ccnt24_ablocks : forall ly S,
  YGcfRoomLive.ccnt24 S = Z.of_nat (PresetRoom.ccnt YG00.kBatchClass (map snd (ablocks B ly S))).
Proof. intros ly S. unfold YGcfRoomLive.ccnt24, ablocks. rewrite map_map. reflexivity. Qed.

Lemma prh_ccnt24_free : forall ly S ly' S' b1 b2 x,
  ablocks B ly S = b1 ++ x :: b2 -> ablocks B ly' S' = b1 ++ b2 ->
  YGcfRoomLive.ccnt24 S' + Z.of_nat (PresetRoom.ccnt YG00.kBatchClass [snd x]) = YGcfRoomLive.ccnt24 S.
Proof.
intros ly S ly' S' b1 b2 x E E'.
rewrite (prh_ccnt24_ablocks ly S), (prh_ccnt24_ablocks ly' S'), E, E', !map_app. cbn [map].
change (snd x :: map snd b2) with ([snd x] ++ map snd b2). rewrite !PresetRoom.ccnt_app. lia.
Qed.
End c.
