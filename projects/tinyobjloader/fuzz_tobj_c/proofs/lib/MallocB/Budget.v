(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Stdlib.ZArith.BinInt.Z"; "add"; "le"; "mul"; "div"; "pow"; "sub"; "@Corelib.Numbers.BinNums"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Budget"; "acost"; "KMAX"; "BETA_F"; "BETA_M"; "LIMIT"; "QMAX"; "U0"; "VMAX"; "ALPHA_DEN"; "MAX_INPUT"; "NCALLS"; "limit_ok_alloc"; "limit_ok_free"; "ALPHA_NUM"; "CK0"; "CK_DIV"; "CV"; "CV0"; "K_DRV"; "QPRIM"; "V_DRV"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry"; "PG"; "kDepotNodesBlock"; "kUserMapSize"; "kPtrArrayCommit"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith Lia.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Import Geometry.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.
Local Open Scope Z_scope.

Definition LIMIT : Z := 2 ^ 39.
Definition U0 : Z := 0x1800000.
Definition ALPHA_NUM : Z := 7.
Definition ALPHA_DEN : Z := 4.
Definition acost (v : Z) : Z := ltac2:(tb__ "0|0|
S3S5S0S2S14Vv;A2SfA2Z1A2SfA2").
Definition BETA_M : Z := 2048.
Definition BETA_F : Z := 2048.

Definition QPRIM : Z := 0x418000000.
Definition QMAX : Z := ltac2:(tb__ "0|2|
S0S0S0S0S0S0S0S2Z1eS2Z2M0S0S1eS3S1eZ8A2A2A2M1A2S1dA2S1cA2Z2404A2S1fA2Z10000A2S0S0G1S1dA2S2G0S1cA2A2A2S1aA2").

Definition CV : Z := 1000.
Definition CV0 : Z := 2 ^ 24.
Definition CK_DIV : Z := 32.
Definition CK0 : Z := 2 ^ 16.
Definition MAX_INPUT : Z := 2 ^ 26.
Definition NCALLS : Z := 4.

Definition V_DRV : Z := 2 ^ 27 + 2 ^ 26.
Definition K_DRV : Z := 24.
Definition VMAX : Z := ltac2:(tb__ "0|0|
S0S1bS2S11S0S2S17S10A2S18A2A2A2").
Definition KMAX : Z := ltac2:(tb__ "0|0|
S0S19S2S11S0S3S10S16A2S15A2A2A2").

Definition limit_ok_alloc (V Km Kf n : Z) : Prop := ltac2:(tb__ "0|0|
S1S0S0S0S0SdS7S0VV;Vn;A2A1A2S2SaS0VKm;Z1A2A2A2S2S9VKf;A2A2ScA2SbA2").
Definition limit_ok_free (V Km Kf : Z) : Prop := ltac2:(tb__ "0|0|
S1S0S0S0S0SdS7VV;A1A2S2SaVKm;A2A2S2S9S0VKf;Z1A2A2A2ScA2SbA2").

Lemma acost_mono : ltac2:(tb__ "0|0|
S6S6S1R2R1A2S1S7R3A1S7R2A1A2F_;Fb;Fa;").
Proof. intros. unfold acost, ALPHA_NUM, ALPHA_DEN. apply Z.div_le_mono; lia. Qed.
Lemma acost_le : ltac2:(tb__ "0|0|
S6S1Z0R1A2S1S7R2A1S2Z2R2A2A2F_;Fv;").
Proof.
  intros v Hv. unfold acost, ALPHA_NUM, ALPHA_DEN.
  pose proof (Z.div_mod (7 * v + 4 - 1) 4) as Hd. pose proof (Z.mod_pos_bound (7 * v + 4 - 1) 4) as Hm. lia.
Qed.

Lemma budget_closes : ltac2:(tb__ "0|0|
S1S0S0S0S0SdS7SeA1A2S2SaS8A2A2S2S9S8A2A2ScA2SbA2").
Proof. apply Z.leb_le. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma limit_ok_alloc_intro : ltac2:(tb__ "0|2|
S6S6S6S6S1Z0M0R1A2S1G0R5A2S1S0R6R3A2SeA2S1G0R6A2M1G1S1S0S0R8Z1A2R7A2S8A2S12RaR9R8R7A4F_;F_;F_;F_;F_;F_;Fn;FKf;FKm;FV;").
Proof.
  intros. unfold limit_ok_alloc. pose proof budget_closes as B.
  pose proof (acost_mono (V + n) VMAX ltac:(lia)). unfold BETA_M, BETA_F in *. lia.
Qed.
Lemma limit_ok_free_intro : ltac2:(tb__ "0|2|
S6S6S6S1Z0M0R3A2S1R4SeA2S1G0R4A2M1G1S1S0S0R6R5A2Z1A2S8A2S13R8R7R6A3F_;F_;F_;F_;F_;FKf;FKm;FV;").
Proof.
  intros. unfold limit_ok_free. pose proof budget_closes as B.
  pose proof (acost_mono V VMAX ltac:(lia)). unfold BETA_M, BETA_F in *. lia.
Qed.

Lemma QMAX_nonneg : 0 <= QMAX.
Proof. unfold Z.le. intro H. vm_compute in H. discriminate H. Qed.
Lemma U0_nonneg : 0 <= U0.
Proof. unfold Z.le. intro H. vm_compute in H. discriminate H. Qed.
Lemma acost_nonneg : ltac2:(tb__ "0|1|
S6S1Z0M0R1A2S1G0S7R2A1A2F_;Fv;").
Proof. intros v Hv. unfold acost, ALPHA_NUM, ALPHA_DEN. apply Z.div_pos; lia. Qed.
Lemma LIMIT_split : LIMIT = 2048 * 2 ^ 28.
Proof. reflexivity. Qed.
Lemma limit_ok_alloc_K : ltac2:(tb__ "0|0|
S6S6S6S6S1Z0S0R4R1A2A2S12R5R4R3R2A4S1S0S0R5Z1A2R4A2S4Z2Z1cA2A2F_;F_;Fn;FKf;FKm;FV;").
Proof.
  intros V Km Kf n HV H. unfold limit_ok_alloc, BETA_M, BETA_F in H. rewrite LIMIT_split in H.
  pose proof QMAX_nonneg. pose proof U0_nonneg. pose proof (acost_nonneg (V + n) HV).
  set (c := 2 ^ 28) in *. clearbody c. lia.
Qed.
Lemma limit_ok_free_K : ltac2:(tb__ "0|0|
S6S6S6S1Z0R3A2S13R4R3R2A3S1S0S0R4R3A2Z1A2S4Z2Z1cA2A2F_;F_;FKf;FKm;FV;").
Proof.
  intros V Km Kf HV H. unfold limit_ok_free, BETA_M, BETA_F in H. rewrite LIMIT_split in H.
  pose proof QMAX_nonneg. pose proof U0_nonneg. pose proof (acost_nonneg V HV).
  set (c := 2 ^ 28) in *. clearbody c. lia.
Qed.
