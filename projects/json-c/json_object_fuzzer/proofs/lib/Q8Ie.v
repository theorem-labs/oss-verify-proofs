(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)


From OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib Require CodeAt StepGen GwInst GwApply. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q6nq.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require G.T_shp.

From Stdlib Require Import ZArith.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.zs_idioms ::= OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.mkr__zs_idioms_3. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.zs_idioms_in H ::= OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.mkr__zs_idioms_in_4 H. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.zs_wrap e ::= OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.mkr__zs_wrap_1 e. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.zs_wrap_in e H ::= OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.mkr__zs_wrap_in_2 e H.
Open Scope Z_scope.

Module GwI.
Definition segs := tt.
End GwI.

Definition FMT_FP_DEPTH : Z := 4640.
Lemma gw_eq_FMT_FP_DEPTH : @FMT_FP_DEPTH = ltac:(GwInst.gw_term (@OSSVerify.Proofs.json_c.json_object_fuzzer.lib.G.T_shp.F_fmt_fp.FMT_FP_DEPTH) (@FMT_FP_DEPTH)). Proof. unfold FMT_FP_DEPTH, OSSVerify.Proofs.json_c.json_object_fuzzer.lib.G.T_shp.F_fmt_fp.FMT_FP_DEPTH; first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[export] Hint Rewrite gw_eq_FMT_FP_DEPTH : gw_eqs.

Definition fmt_fp_facts (y fl p t : Z) : Prop := False.
Lemma gw_eq_fmt_fp_facts : @fmt_fp_facts = ltac:(GwInst.gw_term (@OSSVerify.Proofs.json_c.json_object_fuzzer.lib.G.T_shp.F_fmt_fp.fmt_fp_facts) (@fmt_fp_facts)). Proof. unfold fmt_fp_facts, OSSVerify.Proofs.json_c.json_object_fuzzer.lib.G.T_shp.F_fmt_fp.fmt_fp_facts; first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[export] Hint Rewrite gw_eq_fmt_fp_facts : gw_eqs.
