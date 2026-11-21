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
  BothPlanImages AsanPlanImagesInit AsanInit AsanStartup BothTableL BothStartup AsanNodesStartX AsanNodesStartXBoth SumsBothClose.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AX2S. Import APC. Import AP. Import APS.
Open Scope Z_scope.

Theorem xall_sound_B : forall LINV : (word -> option byte) -> Prop, LINV_STMT_B LINV -> XALL_STMT_B LINV.
Proof.
  intros LINV [HL0 HLf] fx sp rdraw brk0 argv envp FS0 apc mbase fs stdin gid groups net ur kern execfn nofile sigmask abt sdf Hsp Hva Hve uid hw Hfit Hkernel Hlaunch Hlau SINV HS0 HSf HSa x.
  pose proof (argH0_high apc sp rdraw argv envp kern execfn Hsp Hva) as AH.
  pose proof (argH0_agree sp rdraw argv envp kern execfn) as AA.
  pose proof (Nat.le_refl NX0 : APS.nx0_ok NX0) as NG.
  assert (AT : forall E M (a : word), SINV E M -> argH0 sp rdraw argv envp kern execfn E a = true -> bv_unsigned (edenot E e_sp0) <= bv_unsigned a).
  { intros E M a HS Ha. exact (argH0_top BPH apc sp rdraw brk0 mbase argv envp fs stdin uid gid hw groups net ur kern execfn Hsp Hva Hve Hfit nofile sigmask abt sdf Hlau E M a (HS0 E M HS) Ha). }
  destruct x.
  - exact (both_node_x_sound_XIMemset NX0 AsanInit.LIMIT SINV _ LINV AH AA NG HSf HSa HLf FS0).
  - exact (both_node_x_sound_XIMemcpy NX0 AsanInit.LIMIT SINV _ LINV AH AA NG HSf HSa HLf FS0).
  - exact (both_node_x_sound_XMemset NX0 AsanInit.LIMIT SINV _ LINV AH AA AT NG HSf HSa HLf FS0).
  - exact (both_node_x_sound_XMemcpy NX0 AsanInit.LIMIT SINV _ LINV AH AA NG HSf HSa HLf FS0).
  - exact (both_node_x_sound_XMemIsZero NX0 AsanInit.LIMIT SINV _ LINV AH AA NG HSf HSa HLf FS0).
  (* twin of AsanStartupX.v:35-42 *)
  - exact (node_x_sound_XEnvScan_both_gen sp rdraw brk0 mbase argv envp fs stdin FS0 Hsp Hva Hve uid hw Hfit LINV HLf apc gid groups net ur kern execfn nofile sigmask abt sdf Hlaunch Hlau SINV HS0 HSf).
  - exact (node_x_sound_XPnScan_both_gen sp rdraw brk0 mbase argv envp fs stdin FS0 Hsp Hva Hve uid hw Hfit LINV HLf apc gid groups net ur kern execfn nofile sigmask abt sdf Hlau SINV HS0 HSf HSa).   (* XPnScan takes entry_launch_ok_va alone; see AsanStartupX.v:27-34 *)
  - exact (node_x_sound_XLayout_both_gen sp rdraw argv envp FS0 LINV kern execfn SINV).
  - exact (both_node_x_sound_XIStrncpy NX0 AsanInit.LIMIT SINV _ LINV AH AA NG HSf HSa HLf FS0).
  - exact (both_node_x_sound_XPopFree NX0 AsanInit.LIMIT SINV _ LINV AH AA NG HSf HSa HLf FS0).
  - apply APS.node_x_sound_XUnwind_inert.   (* [comment removed for export] *)
Qed.
