(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Import AxSymExec3 AsanPlanCore LibSym SegRun SegPlan Pm8PlanKit.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert Require Import CutCert CutOps CutHeap CutAuto CutLib CutHeap2 CutAutoX CutCertA CutHeapA CutShC.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen Require Import PsoInstCA PsoKnCA ParseSomeChkCA.
Import ListNotations. Import AX2. Import PSOC.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
Local Ltac vmc_refl := first [ lazymatch goal with |- _ = ?b => vm_cast_no_check (@eq_refl _ b) end | vm_compute; reflexivity ].
Module PSOA.
Import PSO.
Lemma len_cps : length G.CPS = 275%nat. Proof. vmc_refl. Qed.
Lemma len_tags : length G.TAGS = 275%nat. Proof. vmc_refl. Qed.
Lemma heap_ok : CHA.heap_chkA GT.NF G.HDECL G.BLS FFS G.CPS G.TAGS = true.
Proof. vmc_refl. Qed.
Lemma cpf_all : forallb (fun i => cpf_ok i (CC.cp_F (cutn i))) (seq 0 NCUT) = true.
Proof. vmc_refl. Qed.
Lemma sites : CSLR.sites_ok Pm8PlanKit.RSEGS ROWS = true.
Proof. vmc_refl. Qed.

Lemma blv_all : forallb (fun i => CH2.blocks_vars_lt (CC.cp_nx (cutn i)) (nth i G.BLS []) && Nat.eqb (length (nth i G.BLS [])) 2)%bool (seq 0 NCUT) = true.
Proof. vmc_refl. Qed.

Lemma views_all : forallb (fun i => (isSome (pview (CC.cp_know (cutn i))) || kind_eqb (kind_of i) KSetsh) && Nat.leb 40 (CC.cp_nx (cutn i))
                                    && (Nat.ltb i 2 || has (CC.cp_know (cutn i)) (KWord (SA FE 1016) 8 FLE)))%bool (seq 0 NCUT) = true.
Proof. vmc_refl. Qed.
Lemma ret_at : CL.is_ret_at Pm8PlanKit.RSEGS RET.
Proof. CL.solve_is_ret. Qed.
Lemma retx_chk : CHA.retire_chk GT.NF G.HDECL (cutn 45) (nth 45 G.BLS []) (nth 45 FFS []) = Some FLE.
Proof. vmc_refl. Qed.

Lemma t0_kn : CC.cp_know GT.t0 = PSOK.KN0S.
Proof. vmc_refl. Qed.
Lemma t1_kn : CC.cp_know GT.t1 = PSOK.KN0N.
Proof. vmc_refl. Qed.
End PSOA.
