(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool.
From OSSVerify.Proofs.openssl.hashtable.lib Require Import AxSymExec3 AsanPlanCore AsanInit CertRefl CxRel CxPlan CxPlanSound HAPlanImage HAAtable HACheck0 HACheck1 Xu FEEndRB3 CxfL9 CxfFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import CAP. Open Scope Z_scope.
Definition xrb3_IT : itab := APC.mk_itab_ranges HASEGS xu_ranges.
Lemma xrb3_IT_ok : itab_sound HASEGS xrb3_IT.
Proof. apply CXS.mk_itab_ranges_sound. Qed.
Definition xrb3_shape_ (_ : unit) : shape := (SExit 2).
Abbreviation xrb3_shape := (xrb3_shape_ tt).
Lemma xrb3_cert :
  CAP.check HASEGS xrb3_IT HAT NX0 AsanInit.LIMIT ha1_XN ha1_XE ha1_XB (fun _ : nat => @None acs) 0 true false true 400000 3000 None feendrb3 xu_plan = COk xrb3_shape.
Proof. apply CXFF.check_l_intro. ltac2:(cert_refl_vm constr:(COk xrb3_shape)). Time Qed.
