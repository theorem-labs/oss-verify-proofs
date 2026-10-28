(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith Lia List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase State Run.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import HeapIface.
Import ListNotations.
Open Scope Z_scope.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Ltac2 gd_tbl_P_layout () : Init.string Init.list := ["Corelib.Init.Logic.or"; "Corelib.Init.Logic.and"; "Stdlib.ZArith.BinInt.Z.le"; "Stdlib.ZArith.BinInt.Z.lt"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.HL"; "U_static"; "U_written"; "run_ceil"; "run_ceil_lo"; "run_ceil_hi"].


Definition U_static (a : Z) : Prop := ltac2:(CDefT.buildp (gd_tbl_P_layout ()) "(0.(0.(1.(2.+7=350.O1.)(3.O1.+7=768.))(0.(1.(2.+5=024.O1.)(3.O1.+5=028.))(0.(1.(2.+7=330.O1.)(3.O1.+7=338.))(1.(2.+4;<=8.O1.)(3.O1.+4;<>0.)))))(1.(2.+7=768.O1.)(3.O1.+7=76<.)))")
(* [comment removed for export] *).

Definition U_written (a : Z) : Prop := (0x4bcd8 <= a < 0x4bce0) \/ (0x4cd30 <= a < 0x7db98).

(* [comment removed for export] *)
Definition run_ceil (sp0 : word) : Z :=
  Z.min (Z.max (bv_unsigned sp0 - 8388608) 0x7fff7f800000) 0x7fffff800000.
Lemma run_ceil_lo sp0 : 0x7fff7f800000 <= run_ceil sp0.
Proof. unfold run_ceil. lia. Qed.
Lemma run_ceil_hi sp0 : run_ceil sp0 <= 0x7fffff800000.
Proof. unfold run_ceil. lia. Qed.
Lemma run_ceil_eq sp0 : valid_sp sp0 -> run_ceil sp0 = bv_unsigned sp0 - 8388608.
Proof. unfold valid_sp, sp_window_lo, sp_window_hi, run_ceil. lia. Qed.

Definition U_layout (sp0 : word) : heap_layout := ltac2:(CDefT.buildp (gd_tbl_P_layout ()) "(4.+3?;=8.+3?960.+3?:98.+5=0<8.+2020.+48000.+7>000.$5.$6.+10000.+7>000.(7.O1.)(8.O1.)(9.O1.))")
(* [comment removed for export] *).

(* [comment removed for export] *)
Lemma U_alloc_ceiling_eq sp0 : valid_sp sp0 -> @alloc_ceiling (U_layout sp0) = bv_unsigned sp0 - 8388608.
Proof. exact (run_ceil_eq sp0). Qed.

Lemma U_static_written : forall a, U_static a -> U_written a.
Proof. unfold U_static, U_written. intros a H. lia. Qed.
