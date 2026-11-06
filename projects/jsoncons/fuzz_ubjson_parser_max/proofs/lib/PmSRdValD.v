(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith List Lia.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import PropExec CatExec CatSim StoreOk Hoare ShapeAlg SpinAlg HeapIface L5Defs L5Core PmLayout PmModel PmSpecs.
Import ListNotations.
Open Scope Z_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import SecKit.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module PMSRVD.
Definition rvQ (t : Z) : Prop := t = 70 \/ t = 78 \/ t = 84 \/ t = 90 \/ t = 69 \/ t = 71 \/ t = 74 \/ t = 75 \/ t = 77 \/ t = 79 \/ t = 80 \/ t = 81 \/ t = 82 \/ t = 86 \/ t = 87 \/ t = 88 \/ t = 89 \/ (0 <= t <= 66) \/ (92 <= t <= 99) \/ (101 <= t <= 104) \/ (106 <= t <= 107) \/ (109 <= t <= 122) \/ (124 <= t <= 255).
Definition rvR (t : Z) : Prop := t = 67 \/ t = 68 \/ t = 73 \/ t = 76 \/ t = 85 \/ t = 100 \/ t = 105 \/ t = 108.
Definition rvS (t : Z) : Prop := t = 72 \/ t = 83.
Definition rvA (t : Z) : Prop := t = 91 \/ t = 123.
Definition args_rvP (A : pm_addrs) (P : Z -> Prop) (R : bvmap 5 word) (fb : Z) (_ : PM.pst) : Prop :=
getr R 10%bv = Z_to_bv 64 (PMSP.o_p A fb) /\ getr R 11%bv = Z_to_bv 64 (PMSP.o_v A fb) /\ getr R 13%bv = Z_to_bv 64 (PMSP.o_ec A fb)
/\ exists t, 0 <= t < 256 /\ P t /\ getr R 12%bv = Z_to_bv 64 t.
Section S.
Local Abbreviation SECT := (forall t, 0 <= t < 256 -> rvQ t \/ rvR t \/ rvS t \/ rvA t) (only parsing).
Variable t : ltac:(sec_ty2 constr:(SECT) 0%nat 0%nat).
Lemma rv_split : ltac:(sec_stmt2 constr:(SECT) 1%nat 0%nat).
Proof.
intros Ht. unfold rvQ, rvR, rvS, rvA.
destruct (Z_le_gt_dec t 66) as [N0|N0]; [left; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; left; lia|].
destruct (Z.eq_dec t 67) as [->|N67]; [right; left; left; reflexivity|].
destruct (Z.eq_dec t 68) as [->|N68]; [right; left; right; left; reflexivity|].
destruct (Z.eq_dec t 69) as [->|N69]; [left; right; right; right; right; left; reflexivity|].
destruct (Z.eq_dec t 70) as [->|N70]; [left; left; reflexivity|].
destruct (Z.eq_dec t 71) as [->|N71]; [left; right; right; right; right; right; left; reflexivity|].
destruct (Z.eq_dec t 72) as [->|N72]; [right; right; left; left; reflexivity|].
destruct (Z.eq_dec t 73) as [->|N73]; [right; left; right; right; left; reflexivity|].
destruct (Z.eq_dec t 74) as [->|N74]; [left; right; right; right; right; right; right; left; reflexivity|].
destruct (Z.eq_dec t 75) as [->|N75]; [left; right; right; right; right; right; right; right; left; reflexivity|].
destruct (Z.eq_dec t 76) as [->|N76]; [right; left; right; right; right; left; reflexivity|].
destruct (Z.eq_dec t 77) as [->|N77]; [left; right; right; right; right; right; right; right; right; left; reflexivity|].
destruct (Z.eq_dec t 78) as [->|N78]; [left; right; left; reflexivity|].
destruct (Z.eq_dec t 79) as [->|N79]; [left; right; right; right; right; right; right; right; right; right; left; reflexivity|].
destruct (Z.eq_dec t 80) as [->|N80]; [left; right; right; right; right; right; right; right; right; right; right; left; reflexivity|].
destruct (Z.eq_dec t 81) as [->|N81]; [left; right; right; right; right; right; right; right; right; right; right; right; left; reflexivity|].
destruct (Z.eq_dec t 82) as [->|N82]; [left; right; right; right; right; right; right; right; right; right; right; right; right; left; reflexivity|].
destruct (Z.eq_dec t 83) as [->|N83]; [right; right; left; right; reflexivity|].
destruct (Z.eq_dec t 84) as [->|N84]; [left; right; right; left; reflexivity|].
destruct (Z.eq_dec t 85) as [->|N85]; [right; left; right; right; right; right; left; reflexivity|].
destruct (Z.eq_dec t 86) as [->|N86]; [left; right; right; right; right; right; right; right; right; right; right; right; right; right; left; reflexivity|].
destruct (Z.eq_dec t 87) as [->|N87]; [left; right; right; right; right; right; right; right; right; right; right; right; right; right; right; left; reflexivity|].
destruct (Z.eq_dec t 88) as [->|N88]; [left; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; left; reflexivity|].
destruct (Z.eq_dec t 89) as [->|N89]; [left; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; left; reflexivity|].
destruct (Z.eq_dec t 90) as [->|N90]; [left; right; right; right; left; reflexivity|].
destruct (Z.eq_dec t 91) as [->|N91]; [right; right; right; left; reflexivity|].
destruct (Z_le_gt_dec t 99) as [N92|N92]; [left; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; left; lia|].
destruct (Z.eq_dec t 100) as [->|N100]; [right; left; right; right; right; right; right; left; reflexivity|].
destruct (Z_le_gt_dec t 104) as [N101|N101]; [left; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; left; lia|].
destruct (Z.eq_dec t 105) as [->|N105]; [right; left; right; right; right; right; right; right; left; reflexivity|].
destruct (Z_le_gt_dec t 107) as [N106|N106]; [left; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; left; lia|].
destruct (Z.eq_dec t 108) as [->|N108]; [right; left; right; right; right; right; right; right; right; reflexivity|].
destruct (Z_le_gt_dec t 122) as [N109|N109]; [left; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; left; lia|].
destruct (Z.eq_dec t 123) as [->|N123]; [right; right; right; right; reflexivity|].
left; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; lia.
Qed.
End S.
End PMSRVD.
