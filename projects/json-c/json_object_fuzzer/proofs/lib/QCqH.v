(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)


From OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib Require CodeAt StepGen GwInst GwApply. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q6nq.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QXfH.

From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QZAi.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QZAi.Mq1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QfYR.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QfYR.
Import ListNotations. Unset Keyed Unification. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.zs_idioms ::= OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.mkr__zs_idioms_3. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.zs_idioms_in H ::= OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.mkr__zs_idioms_in_4 H. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.zs_wrap e ::= OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.mkr__zs_wrap_1 e. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.zs_wrap_in e H ::= OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.mkr__zs_wrap_in_2 e H.
Open Scope Z_scope.
Unset Lia Cache.

Module GwI.
Definition segs := tt.
End GwI.

Lemma Forall_znth : forall (P : Z -> Prop) l i, Forall P l -> P 0 -> P (znth l i).
Proof. first [GwInst.gw_exact (@QXfH.Forall_znth) | autorewrite with gw_eqs; GwInst.gw_exact (@QXfH.Forall_znth)]. Qed.

Definition FB (f : shfile) : Prop := Forall (fun c => 0 <= c < 256) (sh_buf f).
Lemma gw_eq_FB : @FB = ltac:(GwInst.gw_term (@QXfH.FB) (@FB)). Proof. unfold FB, QXfH.FB; first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[export] Hint Rewrite gw_eq_FB : gw_eqs.

Lemma sh_getc_char : forall f, FB f -> -1 <= fst (sh_getc f) < 256 /\ FB (snd (sh_getc f)).
Proof. rewrite ?gw_eq_FB; first [GwInst.gw_exact (@QXfH.sh_getc_char) | autorewrite with gw_eqs; GwInst.gw_exact (@QXfH.sh_getc_char)]. Qed.

Lemma sh_unget_FB : forall f, FB f -> FB (sh_unget f).
Proof. rewrite ?gw_eq_FB; first [GwInst.gw_exact (@QXfH.sh_unget_FB) | autorewrite with gw_eqs; GwInst.gw_exact (@QXfH.sh_unget_FB)]. Qed.

Lemma isdigitc_range : forall c, -1 <= c < 256 -> isdigitc c = true -> 48 <= c <= 57.
Proof. first [GwInst.gw_exact (@QXfH.isdigitc_range) | autorewrite with gw_eqs; GwInst.gw_exact (@QXfH.isdigitc_range)]. Qed.

Lemma scanexp_l1_inv : ltac2:(Q6nq.tyx '(@QXfH.scanexp_l1_inv) [[@gw_eq_FB]] '([256]%Z : list Z) 'Q6nq.gwt_nil).
Proof. rewrite ?gw_eq_FB; first [GwInst.gw_exact (@QXfH.scanexp_l1_inv) | autorewrite with gw_eqs; GwInst.gw_exact (@QXfH.scanexp_l1_inv)]. Qed.

Lemma scanexp_l2_inv : ltac2:(Q6nq.tyx '(@QXfH.scanexp_l2_inv) [[@gw_eq_FB]] '([256]%Z : list Z) 'Q6nq.gwt_nil).
Proof. rewrite ?gw_eq_FB; first [GwInst.gw_exact (@QXfH.scanexp_l2_inv) | autorewrite with gw_eqs; GwInst.gw_exact (@QXfH.scanexp_l2_inv)]. Qed.

Lemma scanexp_l3_inv : forall n c f c' f',
scanexp_l3_loop n (c, f) = Some (c', f') -> FB f -> FB f'.
Proof. rewrite ?gw_eq_FB; first [GwInst.gw_exact (@QXfH.scanexp_l3_inv) | autorewrite with gw_eqs; GwInst.gw_exact (@QXfH.scanexp_l3_inv)]. Qed.

Lemma scanexp_bound : ltac2:(Q6nq.tyx '(@QXfH.scanexp_bound) [[@gw_eq_FB__3; @gw_eq_FB__2; @gw_eq_FB]] '([256]%Z : list Z) 'Q6nq.gwt_nil).
Proof. first [GwInst.gw_exact (@QXfH.scanexp_bound) | autorewrite with gw_eqs; GwInst.gw_exact (@QXfH.scanexp_bound)]. Qed.

Lemma sh_getc_stdio : forall f, sh_stdio (snd (sh_getc f)) = sh_stdio f /\ sh_buf (snd (sh_getc f)) = sh_buf f.
Proof. first [GwInst.gw_exact (@QXfH.sh_getc_stdio) | autorewrite with gw_eqs; GwInst.gw_exact (@QXfH.sh_getc_stdio)]. Qed.
Lemma sh_unget_stdio : forall f, sh_stdio (sh_unget f) = sh_stdio f /\ sh_buf (sh_unget f) = sh_buf f.
Proof. first [GwInst.gw_exact (@QXfH.sh_unget_stdio) | autorewrite with gw_eqs; GwInst.gw_exact (@QXfH.sh_unget_stdio)]. Qed.

Lemma scanexp_l1_stdio : ltac2:(Q6nq.tyx '(@QXfH.scanexp_l1_stdio) [[@gw_eq_FB__3; @gw_eq_FB__2; @gw_eq_FB]] '(@nil Z) 'Q6nq.gwt_nil).
Proof. first [GwInst.gw_exact (@QXfH.scanexp_l1_stdio) | autorewrite with gw_eqs; GwInst.gw_exact (@QXfH.scanexp_l1_stdio)]. Qed.

Lemma scanexp_stdio : ltac2:(Q6nq.tyx '(@QXfH.scanexp_stdio) [[@gw_eq_FB__3; @gw_eq_FB__2; @gw_eq_FB]] '(@nil Z) 'Q6nq.gwt_nil).
Proof. first [GwInst.gw_exact (@QXfH.scanexp_stdio) | autorewrite with gw_eqs; GwInst.gw_exact (@QXfH.scanexp_stdio)]. Qed.
