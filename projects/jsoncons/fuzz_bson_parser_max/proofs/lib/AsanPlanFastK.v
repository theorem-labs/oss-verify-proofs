(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool FunctionalExtensionality.
From OSSVerify.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import AxSymExec3K AxSymExec3BK AsanPlanCoreK AsanPlanK.
Import ListNotations. Import AX2K. Import AX2BK.

Module APKF.

(* [comment removed for export] *)
Definition check_g :=
  ltac:(let t := eval cbv beta delta [APK.check APCK.node_mmap2 APCK.node_brk2 APCK.mmap_null APCK.mmap_fixed_free
                                      APCK.mmap_fixed_free1 APCK.mmap_fixed_grant] in @APK.check in
        let t' := eval pattern (@APCK.kn_grant_filter) in t in
        lazymatch t' with ?F _ => exact F end).

Lemma check_g_ref : check_g (@APCK.kn_grant_filter) = @APK.check.
Proof. reflexivity. Qed.

Definition kgf_fast (A : APCK.atable) (k : list kentry) (ms : list APCK.amap) : list kentry :=
  APCK.kn_grant_filterB A (mkbc k) ms.
Lemma kgf_fast_eq : kgf_fast = @APCK.kn_grant_filter.
Proof. apply functional_extensionality; intros A. apply functional_extensionality; intros k. apply functional_extensionality; intros ms.
  unfold kgf_fast. rewrite APCK.kn_grant_filterB_eqf. reflexivity. Qed.

Definition check_fast := check_g kgf_fast.
Theorem check_fast_eq : check_fast = @APK.check.
Proof. unfold check_fast. rewrite kgf_fast_eq. exact check_g_ref. Qed.

End APKF.
