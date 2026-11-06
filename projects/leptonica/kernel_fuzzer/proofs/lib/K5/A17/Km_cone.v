(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.K5.A17 Require Import Layout.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.K5.AG Require Import Shadow.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.K5.A17 Require Import RT_iface RT_traces RT_gaps_iface Lept_kit Lept_iface Km_setelem Km_iface Km_create Km_destroy Km_getpixel Km_frompix Km_fuzz.
Import ListNotations.

Theorem km_cone : forall RT, art_facts RT -> rt_contracts RT -> rt_gaps RT -> calloc_contractK RT ->
  returnError_cps RT e_returnErrorPtr -> pixDeserialize_cps RT -> pixDestroy_cps RT ->
  In [0x90f74] CLIENT_TRACES -> In [0x9110c] CLIENT_TRACES -> In [0x91124] CLIENT_TRACES ->
  In [0x9130c] CLIENT_TRACES -> In [0x9134c] CLIENT_TRACES -> In [0x91354] CLIENT_TRACES ->
  km_fuzz_one_cps RT.
Proof.
  intros RT AF RC GP CK RERRP DESER DESTROY TRC1 TRC2 TRC3 TRK1 TRK2 TRK3.
  pose proof (kernelCreate_ok RT AF GP CK TRC1 TRC2 TRC3) as KCR.
  pose proof (kernelDestroy_ok RT AF GP TRK1 TRK2 TRK3) as KD.
  pose proof (kernelCreateFromPix_ok RT AF RC GP RERRP KCR (pixGetPixel_ok RT AF RC GP) (kernelSetElement_ok RT AF GP)) as KFP.
  exact (km_fuzz_ok RT AF RC GP DESER DESTROY KFP KD).
Qed.
