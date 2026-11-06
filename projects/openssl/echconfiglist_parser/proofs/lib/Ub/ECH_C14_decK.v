(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import Tac TacX.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Definition UP_get2 : Z := 0x2b3ac0.   (* [comment removed for export] *)
Definition UP_copy : Z := 0x2b3b68.   (* [comment removed for export] *)
Definition UP_get1 : Z := 0x2b3cc8.   (* [comment removed for export] *)
Definition UP_has0 : Z := 0x2b3d58.   (* [comment removed for export] *)

(* [comment removed for export] *)
Definition UDF_LOOP : Z := 0x2b32d8.  (* [comment removed for export] *)
Definition UDF_OK : Z := 0x2b3710.    (* [comment removed for export] *)
Definition UDF_ADV : Z := 0x2b37c4.   (* [comment removed for export] *)
Definition UDF_TA : Z := 0x2b3814.    (* [comment removed for export] *)
Definition UDF_TZ : Z := 0x2b384c.    (* [comment removed for export] *)
Definition UDF_TRAP : Z := 0x2b38f0.  (* [comment removed for export] *)
Definition UDE_R1 : Z := 0x2b32f8.   (* [comment removed for export] *)
Definition UDE_J1 : Z := 0x2b33b8.   (* [comment removed for export] *)
Definition UDE_SKIP : Z := 0x2b35a8. (* [comment removed for export] *)
Definition UDE_R2 : Z := 0x2b35b8.   (* [comment removed for export] *)
Definition UDE_R3 : Z := 0x2b3488.   (* [comment removed for export] *)
Definition UDE_R4a : Z := 0x2b3498.  (* [comment removed for export] *)
Definition UDE_R4 : Z := 0x2b34dc.   (* [comment removed for export] *)
Definition UDE_LH : Z := 0x2b3514.   (* [comment removed for export] *)
Definition UDE_J2 : Z := 0x2b35bc.   (* [comment removed for export] *)
Definition UDE_R5a : Z := 0x2b35d8.  (* [comment removed for export] *)
Definition UDE_R5b : Z := 0x2b35f0.  (* [comment removed for export] *)
Definition UDE_R5 : Z := 0x2b35fc.   (* [comment removed for export] *)
Definition UDE_R6 : Z := 0x2b3618.   (* [comment removed for export] *)
Definition UDE_R6a : Z := 0x2b3628.  (* [comment removed for export] *)
Definition UDE_R7 : Z := 0x2b3640.   (* [comment removed for export] *)
Definition UDE_J3 : Z := 0x2b3644.   (* [comment removed for export] *)
Definition UDE_R8 : Z := 0x2b3668.   (* [comment removed for export] *)
Definition UDE_A367 : Z := 0x2b38e8. Definition UDE_A425 : Z := 0x2b38f4. Definition UDE_A442 : Z := 0x2b38fc. Definition UDE_A447 : Z := 0x2b390c. Definition UDE_A414 : Z := 0x2b3810.
Definition UA_ECHS_FILE : Z := 0x36488.   (* [comment removed for export] *)
Definition UECH_VERSION : Z := 0xfe0d.     (* [comment removed for export] *)
(* [comment removed for export] *)
Definition UO_F3 : Z := 2120. Definition UO_SAVES : Z := 2264. Definition U_FRAME : Z := 2368.
Definition UFRM (w0 w1 w2 w3 w4 w5 w6 w7 w8 : word) : list cell := [C8 w0; C8 w1; C8 w2; C8 w3; C8 w4; C8 w5; C8 w6; C8 w7; C8 w8].
Definition UF3 (pad : list byte) (mxb : byte) (x0 x1 x2 n0 n1 n2 u0 u1 u2 p0 p1 p2 c0 c1 c2 tp0 tp1 : word) : list cell :=
  [CB 7 pad; C1 mxb; C8 x0; C8 x1; C8 x2; C8 n0; C8 n1; C8 n2; C8 u0; C8 u1; C8 u2; C8 p0; C8 p1; C8 p2; C8 c0; C8 c1; C8 c2; C8 tp0; C8 tp1].
