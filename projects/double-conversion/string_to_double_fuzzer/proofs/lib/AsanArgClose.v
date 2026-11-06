(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import PropExec.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import AxSymExec3 AxSymExec3Sound AsanPlanCore AsanPlan AsanPlanSound AsanPlanImages AsanPlanImagesInit
  AsanInit AsanStartup AsanNodesArg AsanNodesArgSound AsanNodesArgAsan AsanMainClosed.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AX2S. Import APC. Import AP. Import APS.
Open Scope Z_scope.

Theorem xarg_sound : forall LINV : (word -> option byte) -> Prop, LINV_STMT LINV -> XARG_STMT LINV.
Proof.
  intros LINV [HL0 HLf] fx sp rdraw brk0 argv envp FS0 Hsp Hva Hve uid hw Hfit SV HSV HSf HSa.
  split.
  - exact (asan_ext_sound sp rdraw brk0 argv envp Hsp Hva Hve uid hw Hfit FS0 SV HSV HSf HSa LINV HLf).
  - exact (asan_emit_sound sp rdraw brk0 argv envp Hsp Hva Hve uid hw Hfit FS0 SV HSV HSf HSa LINV HLf).
Qed.
