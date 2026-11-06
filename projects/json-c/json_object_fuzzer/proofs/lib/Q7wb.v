(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)


From OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib Require CodeAt StepGen GwInst GwApply. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q6nq.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QhAd.

From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QZAi.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QZAi.Mq1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QZAi.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QZAi. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QqdR.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QqdR.
Import ListNotations. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.zs_idioms ::= OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.mkr__zs_idioms_3. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.zs_idioms_in H ::= OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.mkr__zs_idioms_in_4 H. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.zs_wrap e ::= OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.mkr__zs_wrap_1 e. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.zs_wrap_in e H ::= OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.mkr__zs_wrap_in_2 e H.
Local Open Scope Z_scope.

Module GwI.
Definition segs := tt.
End GwI.

Definition is_numch (c : Z) : bool :=
((48 <=? c) && (c <=? 57)) || (c =? 43) || (c =? 45) || (c =? 46) || (c =? 69) || (c =? 101).
Lemma gw_eq_is_numch : @is_numch = ltac:(GwInst.gw_term (@QhAd.is_numch) (@is_numch)). Proof. unfold is_numch, QhAd.is_numch; first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[export] Hint Rewrite gw_eq_is_numch : gw_eqs.

Definition fmt_alpha_fact (d prec : Z) : Prop :=
forall o r, fmt_g d prec = Some (o, r) -> Forall (fun c => is_numch c = true) o.
Lemma gw_eq_fmt_alpha_fact : @fmt_alpha_fact = ltac:(GwInst.gw_term (@QhAd.fmt_alpha_fact) (@fmt_alpha_fact)). Proof. unfold fmt_alpha_fact, QhAd.fmt_alpha_fact; rewrite ?gw_eq_is_numch; first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[export] Hint Rewrite gw_eq_fmt_alpha_fact : gw_eqs.

Example fmt_alpha_probe1 : exists o r, fmt_g 0x3fb999999999999a 15 = Some (o, r) /\ forallb is_numch o = true.
Proof. rewrite ?gw_eq_is_numch; first [GwInst.gw_exact (@QhAd.fmt_alpha_probe1) | autorewrite with gw_eqs; GwInst.gw_exact (@QhAd.fmt_alpha_probe1)]. Qed.
Example fmt_alpha_probe2 : exists o r, fmt_g 0x7e37e43c8800759c 17 = Some (o, r) /\ forallb is_numch o = true.
Proof. rewrite ?gw_eq_is_numch; first [GwInst.gw_exact (@QhAd.fmt_alpha_probe2) | autorewrite with gw_eqs; GwInst.gw_exact (@QhAd.fmt_alpha_probe2)]. Qed.
Example fmt_alpha_probe3 : exists o r, fmt_g 0xbe90c6f7a0b5ed8d 15 = Some (o, r) /\ forallb is_numch o = true.
Proof. rewrite ?gw_eq_is_numch; first [GwInst.gw_exact (@QhAd.fmt_alpha_probe3) | autorewrite with gw_eqs; GwInst.gw_exact (@QhAd.fmt_alpha_probe3)]. Qed.
Example fmt_alpha_probe4 : exists o r, fmt_g 0xbe90c6f7a0b5ed8d 17 = Some (o, r) /\ forallb is_numch o = true.
Proof. rewrite ?gw_eq_is_numch; first [GwInst.gw_exact (@QhAd.fmt_alpha_probe4) | autorewrite with gw_eqs; GwInst.gw_exact (@QhAd.fmt_alpha_probe4)]. Qed.
Example fmt_alpha_probe5 : exists o r, fmt_g 0x437b69b4ba630f34 15 = Some (o, r) /\ forallb is_numch o = true.
Proof. rewrite ?gw_eq_is_numch; first [GwInst.gw_exact (@QhAd.fmt_alpha_probe5) | autorewrite with gw_eqs; GwInst.gw_exact (@QhAd.fmt_alpha_probe5)]. Qed.
