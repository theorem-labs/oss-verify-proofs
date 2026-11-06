(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List.
From OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.K5.B21 Require Import Layout.
From OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.K5.AG Require Import Shadow.
From OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.K5.B21 Require Import RT_iface RT_traces RT_gaps_iface Lept_kit Lept_iface Pm_gaps_iface Pm_iface Pm_iface2 Pm_iface3 Pm_iface4 Pm_getters Pm_top Pm_copycmap Pm_boxcreate Pm_boxdestroy Pm_boxgeom Pm_getindex Pm_selcmap Pm_selmasked Pm_fuzz.

Theorem pm_cone : forall RT, art_facts RT -> rt_contracts RT -> rt_gaps RT -> pm_gaps RT ->
  returnError_cps RT e_returnErrorPtr -> returnError_cps RT e_returnErrorInt -> lept_stderr_cps RT -> pixSetPadBits_cps RT ->
  pixcmapIsValid_cps RT -> pixDeserialize_cps RT -> pixDestroy_cps RT -> pm_fuzz_one_cps RT.
Proof.
  intros RT AF RC GP PG RERRP RERRI LSE PAD VALID DESER DESTROY.
  pose proof (pixCopyColormap_ok RT AF GP RERRI VALID (pixcmapCopy_closed RT AF RC GP RERRP)) as CCM.
  pose proof (pixcmapAddColor_closed RT AF GP RERRI) as ADDC.
  pose proof (pixGetColormap_ok RT AF GP) as GCM.
  pose proof (pixSetSelectCmap_ok RT AF RC GP PG LSE RERRI GCM (pixcmapGetCount_ok RT AF GP) (boxGetGeometry_ok RT AF GP)
                (pixcmapGetIndex_ok RT AF GP) ADDC) as SEL.
  exact (pm_fuzz_ok RT AF RC GP DESER DESTROY (boxCreate_ok RT AF GP) (boxDestroy_ok RT AF GP) (pixCopy_closed RT AF RC GP RERRI PAD CCM)
           SEL (pixSetSelectMaskedCmap_ok RT AF RC GP LSE RERRI GCM)).
Qed.
