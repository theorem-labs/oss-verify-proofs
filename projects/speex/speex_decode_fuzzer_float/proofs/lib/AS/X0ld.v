(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (node_x_sound_XEnvScan_asan_gen and node_x_sound_XPnScan_asan_gen over the launch's ProcInput, launch premises and CONFIG_RSEQ flag in place of argv/envp/uid/hw and entry_stack_fits; the XLayout and closed variants removed). *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.speex.speex_decode_fuzzer_float.images Require Import Asan.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.AS Require Import
X0ms X0mb X0mc X0mw X0na X0mx X0n0 X0jx
X0k2 X0k5 X0k3.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.AS Require Import X0ms.
Local Instance asanreflect_fx : X0ms.FPState := X0ms.fx0.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.AS Require Import X0m4 X0m6 X0m7 X0li X0lh X0ll X0kj X0lj.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.AS Require Import X0ly.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.AS Require Import X0l6 X0lu X0lc X0lf X0m2.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import AX2. Import AX2S. Import AP. Import APS.
Open Scope Z_scope.

Section AsanInstance.
  Variable apc : N.
  Variable sp : word.
  Variable rdraw : EntryDraw.
  Variable brk0 mbase : word.
  Variable inp : ProcInput.
  Variable FS0 : Fs.Fs.
  Hypothesis Hsp : valid_sp sp.
  Hypothesis Hva : valid_argv (in_argv inp).
  Hypothesis Hve : valid_envp (in_envp inp).
  Hypothesis Hapc : Z.of_N apc = a_entry ASAN_A.
  Hypothesis Hbrk : valid_brk ASEGS brk0.
  Hypothesis Hmb : valid_mmap_base mbase.
  Hypothesis Huid : valid_id (in_uid inp).
  Hypothesis Hlaunch : valid_launch inp.
  Hypothesis Hrdr : in_channel_reader inp = true.
  Hypothesis Hlau : entry_launch_ok_va Sv48 (mkEntry sp brk0 mbase rdraw) inp.

  Section AnySINV.
    Variable SINV : env -> (word -> option byte) -> Prop.
    Hypothesis SINV_SINV0 : forall E M, SINV E M -> SINV0 APH apc sp rdraw brk0 mbase inp E M.
    Hypothesis SINV_frame : forall E M M', (forall a, argH0 sp rdraw inp E a = true -> M' a = M a) -> SINV E M -> SINV E M'.
    Hypothesis SINV_agree : forall E E' M, env_agree NX0 E E' -> SINV E M -> SINV E' M.

    Theorem node_x_sound_XEnvScan_asan_gen :
      x_stmt ASEGS ASAN_A NX0 LIMIT (rseq_z (kb_rseq (in_kernel inp))) SINV (argH0 sp rdraw inp) FS0 XEnvScan.
    Proof.
      eapply (init_x_sound_envscan ASEGS ASAN_A APH asan_wx asan_in_hull asan_hull_ok
                W_88b50 W_88b54 W_88b58
                ltac:(cbn [x_envscan x_envscan_k ASAN_A]; lia)
                (fetch_lit _ _ _ _ eq_refl F_88b50) (fetch_lit _ _ _ _ eq_refl F_88b54) (fetch_lit _ _ _ _ eq_refl F_88b58)
                ltac:(repeat split; reflexivity)
                D_88b50 D_88b54 D_88b58); first [eassumption | exact asan_img_facts].
    Qed.

    Theorem node_x_sound_XPnScan_asan_gen :
      x_stmt ASEGS ASAN_A NX0 LIMIT (rseq_z (kb_rseq (in_kernel inp))) SINV (argH0 sp rdraw inp) FS0 XPnScan.
    Proof.
      eapply (init_x_sound_pnscan ASEGS ASAN_A APH asan_wx asan_in_hull asan_hull_ok
                W_88c0c W_88c10 W_88c14 W_88c18 W_88c1c
                ltac:(cbn [x_pnscan x_pnscan_k ASAN_A]; lia)
                (fetch_lit _ _ _ _ eq_refl F_88c0c) (fetch_lit _ _ _ _ eq_refl F_88c10) (fetch_lit _ _ _ _ eq_refl F_88c14)
                (fetch_lit _ _ _ _ eq_refl F_88c18) (fetch_lit _ _ _ _ eq_refl F_88c1c)
                ltac:(repeat split; reflexivity)
                D_88c0c D_88c10 D_88c14 D_88c18 D_88c1c); first [eassumption | exact asan_img_facts].
    Qed.
  End AnySINV.
End AsanInstance.
