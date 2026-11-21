(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (the launch's validity hypotheses; the SIGPIPE disposition). *)
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

(* The EnvScan/PnScan generators take, after `abt`, exactly `valid_launch` then
   `entry_launch_ok_va` and no recorded-kernel equation; XLayout takes neither.  Transcribed
   from `About node_x_sound_XEnvScan_asan_gen`.

   Read before editing this list: I inferred it five times from the character offsets in the
   error and was wrong every time, because an edit that changes the LENGTH of an argument list
   moves every offset after it -- so the next message points into a list you have never seen.
   Probe before the first inference, not the third. *)
Theorem xall_sound : forall LINV : (word -> option byte) -> Prop, LINV_STMT LINV -> XALL_STMT LINV.
Proof.
  intros LINV [HL0 HLf] fx sp rdraw brk0 argv envp FS0 apc mbase fs stdin gid groups net ur kern execfn nofile sigmask abt sdf Hsp Hva Hve uid hw Hfit Hkernel Hlaunch Hlau SINV HS0 HSf HSa x.
  (* The two generators do NOT take the same launch hypotheses, and that is why six rounds of
     inference failed: I kept applying one answer to two lemmas with different signatures.
     The prefix check printed the residual type after
     `… nofile sigmask abt sdf` for XEnvScan as
       valid_launch (inp …) -> entry_launch_ok_va Sv48 {| … |} (inp …) -> forall SINV, …
     so XEnvScan takes BOTH.  XPnScan's proof does not use valid_launch, so its section never
     abstracted it and it takes entry_launch_ok_va ALONE -- which the compiler then said
     outright once XEnvScan was right and the error moved to the next bullet. *)
  pose proof (argH0_high apc sp rdraw argv envp kern execfn Hsp Hva) as AH.
  pose proof (argH0_agree sp rdraw argv envp kern execfn) as AA.
  pose proof (Nat.le_refl NX0 : APS.nx0_ok NX0) as NG.
  assert (AT : forall E M (a : word), SINV E M -> argH0 sp rdraw argv envp kern execfn E a = true -> bv_unsigned (edenot E e_sp0) <= bv_unsigned a).
  { intros E M a HS Ha. exact (argH0_top APH apc sp rdraw brk0 mbase argv envp fs stdin uid gid hw groups net ur kern execfn Hsp Hva Hve Hfit nofile sigmask abt sdf Hlau E M a (HS0 E M HS) Ha). }
  destruct x.
  - exact (asan_node_x_sound_XIMemset NX0 AsanInit.LIMIT SINV _ LINV AH AA NG HSf HSa HLf FS0).
  - exact (asan_node_x_sound_XIMemcpy NX0 AsanInit.LIMIT SINV _ LINV AH AA NG HSf HSa HLf FS0).
  - exact (asan_node_x_sound_XMemset NX0 AsanInit.LIMIT SINV _ LINV AH AA AT NG HSf HSa HLf FS0).
  - exact (asan_node_x_sound_XMemcpy NX0 AsanInit.LIMIT SINV _ LINV AH AA NG HSf HSa HLf FS0).
  - exact (asan_node_x_sound_XMemIsZero NX0 AsanInit.LIMIT SINV _ LINV AH AA NG HSf HSa HLf FS0).
  - exact (node_x_sound_XEnvScan_asan_gen sp rdraw brk0 mbase argv envp fs stdin FS0 Hsp Hva Hve uid hw Hfit LINV HLf apc gid groups net ur kern execfn nofile sigmask abt sdf Hlaunch Hlau SINV HS0 HSf).
  - exact (node_x_sound_XPnScan_asan_gen sp rdraw brk0 mbase argv envp fs stdin FS0 Hsp Hva Hve uid hw Hfit LINV HLf apc gid groups net ur kern execfn nofile sigmask abt sdf Hlau SINV HS0 HSf HSa).
  - exact (node_x_sound_XLayout_asan_gen sp rdraw argv envp FS0 LINV kern execfn SINV).
  - exact (asan_node_x_sound_XIStrncpy NX0 AsanInit.LIMIT SINV _ LINV AH AA NG HSf HSa HLf FS0).
  - exact (asan_node_x_sound_XPopFree NX0 AsanInit.LIMIT SINV _ LINV AH AA NG HSf HSa HLf FS0).
  - apply APS.node_x_sound_XUnwind_inert.   (* [comment removed for export] *)
Qed.
