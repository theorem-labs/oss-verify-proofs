(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool.
From OSSVerify.Proofs.openssl.hashtable.lib Require Import AxSymExec3 AsanPlanCore AsanInit CertRefl CxRel CxPlan CxPlanSound HAPlanImage HAAtable HACheck0 HACheck1 AsanNodesIO HACheck3 CxfL9 CxfFast KInv KW7A0Lit KE8a KE8A0Inv KE8A0Lit KE8A0Rng.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import CAP. Open Scope Z_scope.
Definition ke8a0_IT : itab := APC.mk_itab_ranges HASEGS ke8a0_ranges.
Lemma ke8a0_IT_ok : itab_sound HASEGS ke8a0_IT.
Proof. apply CXS.mk_itab_ranges_sound. Qed.
Definition ke8a0_shape_ (_ : unit) : shape := (SHole 208).
Abbreviation ke8a0_shape := (ke8a0_shape_ tt).
Lemma ke8a0_cert :
  CAP.check HASEGS ke8a0_IT HAT NX0 AsanInit.LIMIT (ha3_XN (ION.IOT (ION.OFile 8388608 16777215) 32 (Some (0, 32767)) (Some (0, 16777209)) None None)) ha3_XE (ha3_XB (ION.IOT (ION.OFile 8388608 16777215) 32 (Some (0, 32767)) (Some (0, 16777209)) None None)) KE8A0_HS 0 true false true 400000 3000 None kw7a0_hs108 ke8a0_pl = COk ke8a0_shape.
Proof. apply CXFF.check_l_intro. ltac2:(cert_refl_vm constr:(COk ke8a0_shape)). Time Qed.
