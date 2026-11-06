(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "@Corelib.Init.Datatypes"; "bool"; "true"; "andb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "wsub_get"; "wsub"; "wsub_id_below"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "SVar"; "sv"; "sv_eqb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CallocBase2"; "wsub_idc"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy"; "NF"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith List Bool.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymFrame ExampleMemcpy.
Import ListNotations.
Definition wsub_idc (s : wsub) : bool := ltac2:(tb__ "0|2|
S3S3S6Vs;SbA2S9S4Vs;P8fM0A2S7G0A1A2A2S9S4Vs;P90M1A2S7G1A1A2A2").
Lemma wsub_idc_below : ltac2:(tb__ "0|0|
S5S0S1SaR1A1S2A3S0S1S6R2SbA2S2A3F_;Fs;").
Proof. intros s H. unfold wsub_idc in H. apply andb_prop in H as [H _]. apply andb_prop in H as [H _]. exact H. Qed.
Lemma wsub_idc_143 : ltac2:(tb__ "0|1|
S5S0S1SaR1A1S2A3S0S8S4R2P8fM0A2S7G0A1A3F_;Fs;").
Proof. intros s H. unfold wsub_idc in H. apply andb_prop in H as [H _]. apply andb_prop in H as [_ H]. exact (sv_eqb_sound _ _ H). Qed.
Lemma wsub_idc_144 : ltac2:(tb__ "0|1|
S5S0S1SaR1A1S2A3S0S8S4R2P90M0A2S7G0A1A3F_;Fs;").
Proof. intros s H. unfold wsub_idc in H. apply andb_prop in H as [_ H]. exact (sv_eqb_sound _ _ H). Qed.
