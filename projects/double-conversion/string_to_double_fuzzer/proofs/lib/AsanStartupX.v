(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import PropExec.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import AxSymExec3 AxSymExec3Sound AsanPlanCore AsanPlan AsanPlanSound AsanPlanSoundSums AsanPlanImages
  AsanPlanImagesInit AsanInit AsanStartup AsanNodesStartX AsanNodesStartXAsan SumsAsanClose.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AX2S. Import APC. Import AP. Import APS.
Open Scope Z_scope.

Theorem xall_sound : forall LINV : (word -> option byte) -> Prop, LINV_STMT LINV -> XALL_STMT LINV.
Proof.
  intros LINV [HL0 HLf] fx sp rdraw brk0 argv envp FS0 Hsp Hva Hve uid hw Hfit SINV HS0 HSf HSa x.
  pose proof (argH0_high APH sp rdraw argv envp uid hw Hsp Hva) as AH.
  pose proof (argH0_agree APH sp rdraw argv envp uid hw) as AA.
  pose proof (Nat.le_refl NX0 : APS.nx0_ok NX0) as NG.
  assert (AT : forall E M (a : word), SINV E M -> argH0 APH sp rdraw argv envp uid hw E a = true -> bv_unsigned (edenot E e_sp0) <= bv_unsigned a).
  { intros E M a HS Ha. exact (argH0_top APH sp rdraw brk0 argv envp uid hw Hsp Hva Hve Hfit E M a (HS0 E M HS) Ha). }
  destruct x.
  - exact (asan_node_x_sound_XIMemset NX0 AsanInit.LIMIT SINV _ LINV AH AA NG HSf HSa HLf FS0).
  - exact (asan_node_x_sound_XIMemcpy NX0 AsanInit.LIMIT SINV _ LINV AH AA NG HSf HSa HLf FS0).
  - exact (asan_node_x_sound_XMemset NX0 AsanInit.LIMIT SINV _ LINV AH AA AT NG HSf HSa HLf FS0).
  - exact (asan_node_x_sound_XMemcpy NX0 AsanInit.LIMIT SINV _ LINV AH AA NG HSf HSa HLf FS0).
  - exact (asan_node_x_sound_XMemIsZero NX0 AsanInit.LIMIT SINV _ LINV AH AA NG HSf HSa HLf FS0).
  - exact (node_x_sound_XEnvScan_asan_gen sp rdraw brk0 argv envp FS0 Hsp Hva Hve uid hw Hfit LINV HLf SINV HS0 HSf).
  - exact (node_x_sound_XPnScan_asan_gen sp rdraw brk0 argv envp FS0 Hsp Hva Hve uid hw Hfit LINV HLf SINV HS0 HSf HSa).
  - exact (node_x_sound_XLayout_asan_gen sp rdraw argv envp FS0 uid hw LINV SINV).
  - exact (asan_node_x_sound_XIStrncpy NX0 AsanInit.LIMIT SINV _ LINV AH AA NG HSf HSa HLf FS0).
  - exact (asan_node_x_sound_XPopFree NX0 AsanInit.LIMIT SINV _ LINV AH AA NG HSf HSa HLf FS0).
  - apply APS.node_x_sound_XUnwind_inert.   (* [comment removed for export] *)
Qed.
