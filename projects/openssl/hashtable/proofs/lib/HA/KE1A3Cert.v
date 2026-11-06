(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool.
From OSSVerify.Proofs.openssl.hashtable.lib Require Import AxSymExec3 AsanPlanCore AsanInit CertRefl CxRel CxPlan CxPlanSound HAPlanImage HAAtable HACheck0 HACheck1 AsanNodesIO HACheck3 CxfL9 CxfFast KInv KPA3Lit KE1b KE1A3Inv KE1A3Lit KE1A3Rng.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import CAP. Open Scope Z_scope.
Definition ke1a3_IT : itab := APC.mk_itab_ranges HASEGS ke1a3_ranges.
Lemma ke1a3_IT_ok : itab_sound HASEGS ke1a3_IT.
Proof. apply CXS.mk_itab_ranges_sound. Qed.
Definition ke1a3_shape_ (_ : unit) : shape := (SHole 201).
Abbreviation ke1a3_shape := (ke1a3_shape_ tt).
Lemma ke1a3_cert :
  CAP.check HASEGS ke1a3_IT HAT NX0 AsanInit.LIMIT (ha3_XN (ION.IOT (ION.OFile 65536 131071) 32 (Some (0, 32767)) (Some (0, 131065)) None None)) ha3_XE (ha3_XB (ION.IOT (ION.OFile 65536 131071) 32 (Some (0, 32767)) (Some (0, 131065)) None None)) KE1A3_HS 0 true false true 400000 3000 None kpa3_hs101 ke1a3_pl = COk ke1a3_shape.
Proof. apply CXFF.check_l_intro. ltac2:(cert_refl_vm constr:(COk ke1a3_shape)). Time Qed.
