(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OSSVerify.coturn.FuzzStunClient.images Require Import Plain.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import PropExec CatExec StreamSim StoreOk.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require WsegFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

Lemma wseg_data_lit : wseg_ok Plain.M.loaded_segments (0x26000 : word) 204800%nat = true.
Proof. apply WsegFast.wseg_ok_fast_sound. vm_cast_no_check (@eq_refl bool true). Qed.

Lemma wseg_data_z : wseg_ok Plain.M.loaded_segments (Z_to_bv 64 0x26000) 204800%nat = true.
Proof.
  replace (Z_to_bv 64 0x26000) with (0x26000 : word) by (apply bv_eq; reflexivity).
  exact wseg_data_lit.
Qed.

(* [comment removed for export] *)
Lemma store_ok_data_win : forall m (a : word) n,
  (0x26000 <= bv_unsigned a)%Z -> (bv_unsigned a + Z.of_nat n <= 0x58000)%Z ->
  store_ok Plain.M.loaded_segments m a n = true.
Proof.
  intros m a n Hlo Hhi.
  eapply (store_ok_window Plain.M.loaded_segments m (0x26000 : word) a 204800%nat n 0x26000 0x58000);
    [ reflexivity | vm_cast_no_check (@eq_refl Z 0x58000%Z) | lia
    | exact wseg_data_lit | exact Hlo | exact Hhi ].
Qed.
