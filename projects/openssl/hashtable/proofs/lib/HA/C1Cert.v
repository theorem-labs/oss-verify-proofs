(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3: the certificate is proved at each CONFIG_RSEQ value, from the start state init_acs_r, for the renumbered plan and the hand-off states computed in C1HS. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.openssl.hashtable.lib Require Import AxSymExec3 AsanPlanCore AsanInit CertRefl CxRel CxPlan CxPlanSound HAPlanImage HAAtable HACheck0 C1 C1HS CxfL9 CxfFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import CAP. Open Scope Z_scope.
Definition C1_IT : itab := APC.mk_itab_ranges HASEGS c1_ranges.
Lemma C1_IT_ok : itab_sound HASEGS C1_IT.
Proof. apply CXS.mk_itab_ranges_sound. Qed.
Definition c1_shape_ (_ : unit) : shape := SCase (EVar 6) 10 (SHole 0) (SHole 1).
Abbreviation c1_shape := (c1_shape_ tt).
Lemma c1_cert_0 :
  CAP.check HASEGS C1_IT HAT NX0 AsanInit.LIMIT ha0_XN ha0_XE ha0_XB C1_HS 0 true false true 400000 3000 None (init_acs_r 0 HAT) c1_plan_r = COk c1_shape.
Proof. apply CXFF.check_l_intro. ltac2:(cert_refl_vm constr:(COk c1_shape)). Time Qed.
Lemma c1_cert_1 :
  CAP.check HASEGS C1_IT HAT NX0 AsanInit.LIMIT ha0_XN ha0_XE ha0_XB C1_HS 0 true false true 400000 3000 None (init_acs_r 1 HAT) c1_plan_r = COk c1_shape.
Proof. apply CXFF.check_l_intro. ltac2:(cert_refl_vm constr:(COk c1_shape)). Qed.
(* the certificate at the run's own CONFIG_RSEQ value [r] *)
Lemma c1_cert : forall r, 0 <= r <= 1 ->
  CAP.check HASEGS C1_IT HAT NX0 AsanInit.LIMIT ha0_XN ha0_XE ha0_XB C1_HS 0 true false true 400000 3000 None (init_acs_r r HAT) c1_plan_r = COk c1_shape.
Proof. intros r Hr. assert (r = 0 \/ r = 1) as [-> | ->] by lia; [exact c1_cert_0 | exact c1_cert_1]. Qed.
