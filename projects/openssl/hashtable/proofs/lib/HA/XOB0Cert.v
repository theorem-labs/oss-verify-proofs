(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool.
From OSSVerify.Proofs.openssl.hashtable.lib Require Import AxSymExec3 AsanPlanCore AsanInit CertRefl CxRel CxPlan CxPlanSound HAPlanImage HAAtable HACheck0 HACheck1 Xu FEEndOB0 CxfL9 CxfFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import CAP. Open Scope Z_scope.
Definition xob0_IT : itab := APC.mk_itab_ranges HASEGS xu_ranges.
Lemma xob0_IT_ok : itab_sound HASEGS xob0_IT.
Proof. apply CXS.mk_itab_ranges_sound. Qed.
Definition xob0_shape_ (_ : unit) : shape := (SExit 2).
Abbreviation xob0_shape := (xob0_shape_ tt).
Lemma xob0_cert :
  CAP.check HASEGS xob0_IT HAT NX0 AsanInit.LIMIT ha1_XN ha1_XE ha1_XB (fun _ : nat => @None acs) 0 true false true 400000 3000 None feendob0 xu_plan = COk xob0_shape.
Proof. apply CXFF.check_l_intro. ltac2:(cert_refl_vm constr:(COk xob0_shape)). Time Qed.
