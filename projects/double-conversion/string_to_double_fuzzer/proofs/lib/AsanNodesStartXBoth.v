(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import ImgB.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import PropExec CatExec CatSim SeqExec StoreOk ShapeAlg SpinAlg AgentLib.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import AsanAcct AsanAcctShape AsanAcctImages.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import AxSymExec3 AxSymExec3Sound AxSymRun3 AsanPlanCore AsanPlan AsanPlanSound AsanInit
  AsanPlanImages BothPlanImages AsanPlanImagesInit BothTableL.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import AsanNodesAux AsanStartLoops AsanNodesStartX AsanNodesStartXInit .
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import Both_code_10b000_10c000.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import AX2. Import AX2S. Import AP. Import APS.
Open Scope Z_scope.

Section BothInstance.
  Context {fx : PropExec.FPState}.
  Variable sp : word.
  Variable rdraw : EntryDraw.   (* [comment removed for export] *)
  Variable brk0 mbase : word.
  Variable argv envp : list (list byte).
  Variable fs : Fs.Fs.
  Variable stdin : InputStream.
  Variable FS0 : Fs.Fs.
  Hypothesis Hsp : valid_sp sp.
  Hypothesis Hva : valid_argv argv.
  Hypothesis Hve : valid_envp envp.
  Variable uid : word.
  Variable hw : word.   (* [comment removed for export] *)
  Hypothesis Hfit : entry_stack_fits sp argv envp.
  Variable LINV : (word -> option byte) -> Prop.
  Hypothesis LINV_frame : forall M M' : word -> option byte,
    (forall a : word, in_lfp BOTHL (bv_unsigned a) = true -> M' a = M a) -> LINV M -> LINV M'.

  Section AnySINV.
    (* [comment removed for export] *)
    Variable SINV : env -> (word -> option byte) -> Prop.
    Hypothesis SINV_SINV0 : forall E M, SINV E M -> SINV0 BPH sp rdraw brk0 argv envp uid hw E M.
    Hypothesis SINV_frame : forall E M M', (forall a, argH0 BPH sp rdraw argv envp uid hw E a = true -> M' a = M a) -> SINV E M -> SINV E M'.
    Hypothesis SINV_agree : forall E E' M, env_agree NX0 E E' -> SINV E M -> SINV E' M.

    Theorem node_x_sound_XEnvScan_both_gen : x_stmt BSEGS BOTHL NX0 LIMIT SINV (argH0 BPH sp rdraw argv envp uid hw) LINV FS0 XEnvScan.
    Proof.
      eapply (init_x_sound_envscan BSEGS BOTHL BPH both_wx bothL_in_hull bothL_hull_ok
                W_10b544 W_10b548 W_10b54c
                ltac:(cbn [x_envscan x_envscan_k BOTHL BOTH]; lia)
                (fetch_lit _ _ _ _ eq_refl F_10b544) (fetch_lit _ _ _ _ eq_refl F_10b548) (fetch_lit _ _ _ _ eq_refl F_10b54c)
                ltac:(repeat split; reflexivity)
                D_10b544 D_10b548 D_10b54c
                sp rdraw brk0 argv envp FS0 Hsp Hva Hve uid hw Hfit SINV SINV_SINV0 SINV_frame LINV LINV_frame).
    Qed.

    Theorem node_x_sound_XPnScan_both_gen : x_stmt BSEGS BOTHL NX0 LIMIT SINV (argH0 BPH sp rdraw argv envp uid hw) LINV FS0 XPnScan.
    Proof.
      eapply (init_x_sound_pnscan BSEGS BOTHL BPH both_wx bothL_in_hull bothL_hull_ok
                W_10b600 W_10b604 W_10b608 W_10b60c W_10b610
                ltac:(cbn [x_pnscan x_pnscan_k BOTHL BOTH]; lia)
                (fetch_lit _ _ _ _ eq_refl F_10b600) (fetch_lit _ _ _ _ eq_refl F_10b604) (fetch_lit _ _ _ _ eq_refl F_10b608)
                (fetch_lit _ _ _ _ eq_refl F_10b60c) (fetch_lit _ _ _ _ eq_refl F_10b610)
                ltac:(repeat split; reflexivity)
                D_10b600 D_10b604 D_10b608 D_10b60c D_10b610
                sp rdraw brk0 argv envp FS0 Hsp Hva Hve uid hw Hfit SINV SINV_SINV0 SINV_frame SINV_agree LINV LINV_frame).
    Qed.

    Theorem node_x_sound_XLayout_both_gen : x_stmt BSEGS BOTHL NX0 LIMIT SINV (argH0 BPH sp rdraw argv envp uid hw) LINV FS0 XLayout.
    Proof. apply x_sound_layout. Qed.
  End AnySINV.

  (* [comment removed for export] *)
  Theorem node_x_sound_XEnvScan_both :
    x_stmt BSEGS BOTHL NX0 LIMIT (SINV0 BPH sp rdraw brk0 argv envp uid hw) (argH0 BPH sp rdraw argv envp uid hw) LINV FS0 XEnvScan.
  Proof. apply node_x_sound_XEnvScan_both_gen; [auto | apply SINV0_frame]. Qed.

  Theorem node_x_sound_XPnScan_both :
    x_stmt BSEGS BOTHL NX0 LIMIT (SINV0 BPH sp rdraw brk0 argv envp uid hw) (argH0 BPH sp rdraw argv envp uid hw) LINV FS0 XPnScan.
  Proof. apply node_x_sound_XPnScan_both_gen; [auto | apply SINV0_frame | apply SINV0_agree]. Qed.

  Theorem node_x_sound_XLayout_both :
    x_stmt BSEGS BOTHL NX0 LIMIT (SINV0 BPH sp rdraw brk0 argv envp uid hw) (argH0 BPH sp rdraw argv envp uid hw) LINV FS0 XLayout.
  Proof. apply x_sound_layout. Qed.
End BothInstance.
