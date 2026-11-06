(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Bool FunctionalExtensionality.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S9 Require Import PropExec AxSymExec3K AxSymExec3BK AsanPlanCoreK AsanPlanK AsanPlanFastK FxExecK.
Import ListNotations. Import AX2K.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module APKX.
Ltac has_const t c := lazymatch t with context [c] => idtac | _ => fail "abstraction target does not occur:" c end.
Definition check_g2 :=
  ltac:(let t := eval cbv beta delta [APK.check APCK.node_mmap2 APCK.node_brk2 APCK.mmap_null APCK.mmap_fixed_free
                                      APCK.mmap_fixed_free1 APCK.mmap_fixed_grant APCK.node_absword] in @APK.check in
        has_const t (@APCK.kn_grant_filter); has_const t (@APCK.run_block_gc); has_const t (@APCK.kn_havoc);
        let t' := eval pattern (@APCK.kn_grant_filter), (@APCK.run_block_gc), (@APCK.kn_havoc) in t in
        lazymatch t' with ?F _ _ _ => exact F end).
Lemma check_g2_ref : check_g2 (@APCK.kn_grant_filter) (@APCK.run_block_gc) (@APCK.kn_havoc) = @APK.check.
Proof. reflexivity. Qed.
Lemma run_block_gc_f_eqf : EXFK.run_block_gc_f = @APCK.run_block_gc.
Proof. repeat (apply functional_extensionality; intros ?). apply EXFK.run_block_gc_f_eq. Qed.
Definition check_fastx := check_g2 APKF.kgf_fast EXFK.run_block_gc_f (@APCK.kn_havocM).
Theorem check_fastx_eq : check_fastx = @APK.check.
Proof. unfold check_fastx. rewrite APKF.kgf_fast_eq, run_block_gc_f_eqf, APCK.kn_havocM_eq. exact check_g2_ref. Qed.
End APKX.
