(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Numbers.BinNums"; "Z"; "@Corelib.Init.Datatypes"; "cons"; "pair"; "bool"; "nil"; "prod"; "true"; "@Corelib.Init.Logic"; "eq"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.DrvWins"; "wins_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout"; "C_P"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Code"; "segs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Drv_wins"; "WINS_P"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith List Bool.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import MallocLayout.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import DrvWins.
Require Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Code.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Definition WINS_P : list (Z * Z) := ltac2:(tb__ "0|3|
S1S5S0S0A2M0S2S0S0Z28570Z28610A4S1G0S2S0S0Z28618Z29889M1A4S1G0S2S0S0G1Z39889M2A4S1G0S2S0S0G2Z398ecA4S1G0S2S0S0Z398f0Z59bf8A4S1G0S2S0S0Z5a038Z5a460A4S4G0A1A3A3A3A3A3A3").

Lemma WINS_P_ok : ltac2:(tb__ "0|0|
S7S3S8SaS9SbA3S6A3").
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
