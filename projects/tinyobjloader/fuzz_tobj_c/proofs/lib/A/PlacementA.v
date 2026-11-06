(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)


From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@stdpp.bitvector.definitions"; "Z_to_bv"; "bv"; "@Corelib.Init.Datatypes"; "cons"; "pair"; "list"; "prod"; "nil"; "@LinuxProcessSemantics.LinuxProcessSem.Run"; "segments_reserved"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ImageFacts"; "segsA"; "@Corelib.Init.Logic"; "eq"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Placement"; "IMG_BAND_HI"; "IMG_BAND_LO"; "band_covered"; "@Corelib.Numbers.BinNums"; "Z"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "reserved_top"; "@Stdlib.Lists.List"; "incl"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase State Monad Specs Run.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Import ImageFacts Placement.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.
Import ListNotations.
Open Scope bv_scope.
Local Open Scope Z_scope.

Lemma segments_reserved_A : ltac2:(tb__ "0|3|
S9S4S5S1Q40M0A1M1G1A2M2A1S7S8A1S2G2S3G1G1S0G0Z10000A2S0G0Z2a000A2A4S2G2S3G1G1S0G0Z3a000A2S0G0Zaa000A2A4S2G2S3G1G1S0G0Ze4000A2S0G0Z5000A2A4S2G2S3G1G1S0G0Ze9000A2S0G0Z55d000A2A4S6G2A1A3A3A3A3A3").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.

Lemma reserved_top_A : ltac2:(tb__ "0|0|
S9SdSeS7S8A1A1SaA3").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.

Lemma img_band_covered : ltac2:(tb__ "0|2|
S4S5S1Q40A1M0G0A2M1A1SfG1S7S8A1R1A3ScR2SbSaA3F_;Fl;").
Proof.
  intros l Hincl. apply (band_covered_incl (segments_reserved segsA)); [|exact Hincl].
  rewrite segments_reserved_A. unfold IMG_BAND_LO, IMG_BAND_HI. intros x Hx.
  destruct (Z.lt_ge_cases x 0x3a000).
  { exists (Z_to_bv 64 0x10000), (Z_to_bv 64 0x2a000). split; [cbn; tauto|]. rewrite !fg_u64_lit by lia. lia. }
  destruct (Z.lt_ge_cases x 0xe4000).
  { exists (Z_to_bv 64 0x3a000), (Z_to_bv 64 0xaa000). split; [cbn; tauto|]. rewrite !fg_u64_lit by lia. lia. }
  destruct (Z.lt_ge_cases x 0xe9000).
  { exists (Z_to_bv 64 0xe4000), (Z_to_bv 64 0x5000). split; [cbn; tauto|]. rewrite !fg_u64_lit by lia. lia. }
  exists (Z_to_bv 64 0xe9000), (Z_to_bv 64 0x55d000). split; [cbn; tauto|]. rewrite !fg_u64_lit by lia. lia.
Qed.

