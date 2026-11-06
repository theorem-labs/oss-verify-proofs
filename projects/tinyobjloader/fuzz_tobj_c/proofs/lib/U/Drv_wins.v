(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Numbers.BinNums"; "Z"; "@Corelib.Init.Datatypes"; "cons"; "pair"; "bool"; "nil"; "prod"; "true"; "@Corelib.Init.Logic"; "eq"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.DrvWins"; "wins_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout"; "C_U"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Code"; "segs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_wins"; "WINS_U"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith List Bool.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import MallocLayout.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import DrvWins.
Require Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Code.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Definition WINS_U : list (Z * Z) := ltac2:(tb__ "0|3|
S1S5S0S0A2M0S2S0S0Z28cb0Z28d50A4S1G0S2S0S0Z28d58Z29fc9M1A4S1G0S2S0S0G1Z39fc9M2A4S1G0S2S0S0G2Z3a02cA4S1G0S2S0S0Z3a030Z5a338A4S1G0S2S0S0Z5a778Z5aba0A4S4G0A1A3A3A3A3A3A3").

Lemma WINS_U_ok : ltac2:(tb__ "0|0|
S7S3S8SaS9SbA3S6A3").
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
