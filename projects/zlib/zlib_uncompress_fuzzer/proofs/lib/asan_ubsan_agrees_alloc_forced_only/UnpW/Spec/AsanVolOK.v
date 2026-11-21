(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool Lia Permutation.
From stdpp Require Import gmap.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.Spec Require Import AsanCtrl AsanCtrlProps AsanInv AsanFree AsanVol. From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.UnpW.Spec Require Import AsanOK.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Definition VOLCAP : Z := 2^30.

Theorem VOL_cost : forall RESV ATOP st mo, INV RESV ATOP [] [] st mo -> acost st <= Q_MAX ->
  commit_bytes st + zsum2 (CH [] [] st) <= VOLCAP.
Proof.
  intros RESV ATOP st mo HI HC. pose proof HI as [HA _]. pose proof (VOL_W ATOP [] [] st HA) as V. pose proof (W_cost _ _ _ _ HI) as WC.
  rewrite VOL_CONST_val in V. unfold VOLCAP, Q_MAX in *. change (2 ^ 30) with 1073741824. lia.
Qed.
