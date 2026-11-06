(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith Lia List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase State Run.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import HeapIface.
Import ListNotations.
Open Scope Z_scope.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Ltac2 gd_tbl_P_layout () : Init.string Init.list := ["Corelib.Init.Logic.or"; "Corelib.Init.Logic.and"; "Stdlib.ZArith.BinInt.Z.le"; "Stdlib.ZArith.BinInt.Z.lt"; "OSSVerify.KrLib.Lib.HeapIface.HL"; "P_static"; "P_written"; "run_ceil"; "run_ceil_lo"; "run_ceil_hi"].


Definition P_static (a : Z) : Prop := ltac2:(CDefT.buildp (gd_tbl_P_layout ()) "(0.(0.(1.(2.+79<50.O1.)(3.O1.+7:068.))(0.(1.(2.+59924.O1.)(3.O1.+59928.))(0.(1.(2.+79<30.O1.)(3.O1.+79<38.))(1.(2.+485>0.O1.)(3.O1.+485>8.)))))(1.(2.+7:068.O1.)(3.O1.+7:06<.)))")
(* [comment removed for export] *).

Definition P_written (a : Z) : Prop := (0x485e0 <= a < 0x485e8) \/ (0x49638 <= a < 0x7a498).

(* [comment removed for export] *)
Definition run_ceil (sp0 : word) : Z :=
  Z.min (Z.max (bv_unsigned sp0 - 8388608) 0x7fff7f800000) 0x7fffff800000.
Lemma run_ceil_lo sp0 : 0x7fff7f800000 <= run_ceil sp0.
Proof. unfold run_ceil. lia. Qed.
Lemma run_ceil_hi sp0 : run_ceil sp0 <= 0x7fffff800000.
Proof. unfold run_ceil. lia. Qed.
Lemma run_ceil_eq sp0 : valid_sp sp0 -> run_ceil sp0 = bv_unsigned sp0 - 8388608.
Proof. unfold valid_sp, sp_window_lo, sp_window_hi, run_ceil. lia. Qed.

Definition P_layout (sp0 : word) : heap_layout := ltac2:(CDefT.buildp (gd_tbl_P_layout ()) "(4.+3<4>0.+3<268.+3<3:0.+599<8.+2020.+44000.+7;000.$5.$6.+10000.+7;000.(7.O1.)(8.O1.)(9.O1.))")
(* [comment removed for export] *).

(* [comment removed for export] *)
Lemma P_alloc_ceiling_eq sp0 : valid_sp sp0 -> @alloc_ceiling (P_layout sp0) = bv_unsigned sp0 - 8388608.
Proof. exact (run_ceil_eq sp0). Qed.

Lemma P_static_written : forall a, P_static a -> P_written a.
Proof. unfold P_static, P_written. intros a H. lia. Qed.
