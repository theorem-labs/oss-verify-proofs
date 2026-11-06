(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys Require Import Uaccess.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.skcms.iccprofile_info.images Require Import Asan.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Asan Require Import
  PropExec CatExec CatSim SeqExec StoreOk StepTac ShapeAlg SpinAlg AgentLib Hoare RefLayout ArgvEnv StartupAux FileSim
  AsanAcct AsanAcctShape AsanAcctImages.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Asan Require Import AxSymExec3 AxSymExec3Sound AxSymRun3 AsanPlanCore AsanPlan AsanPlanSound AsanPlanImages AsanInit.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Asan Require Import AsanPlanSoundSums.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Asan Require Import AsanNodesArgSoundCfg AsanNodesArgAsanCfg.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Asan Require Import AsanNodesIO AsanNodesIOSoundCfg.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Asan Require Import SpinAlgCfg AsanPlanSoundCfg.
Unset Nia Cache.  (* [comment removed for export] *)
Import ListNotations.
Import AX2. Import AX2S. Import APC. Import AP. Import APS. Import ION.
Unset Lia Cache.
Open Scope Z_scope.

(* [comment removed for export] *)
Lemma map_byte_at_seq : forall s, map (byte_at s) (seq 0 (length s + 1)) = s ++ [Z_to_bv 8 0].
Proof.
  intros s. apply nth_ext with (d := Z_to_bv 8 0) (d' := Z_to_bv 8 0).
  - rewrite length_map, length_seq, length_app. cbn [length]. reflexivity.
  - intros n Hn. rewrite length_map, length_seq in Hn.
    rewrite (nth_indep (map (byte_at s) (seq 0 (length s + 1))) (Z_to_bv 8 0) (byte_at s 0)) by (rewrite length_map, length_seq; exact Hn).
    rewrite map_nth, seq_nth by exact Hn. cbn [Nat.add]. reflexivity.
Qed.

Section IOAsan.
  Variable sp : word.
  Variable rdraw : EntryDraw.
  Variable brk0 : word.
  Variables (argv envp : list (list byte)).
  Hypothesis Hsp : valid_sp sp.
  Hypothesis Hva : valid_argv argv.
  Hypothesis Hve : valid_envp envp.
  Variables uid hw : word.
  Hypothesis Hfit : entry_stack_fits sp argv envp.
  Variable FS0 : Fs.Fs.

  Let usp := bv_unsigned sp.
  Let argc := Z.of_nat (length argv).
  Let envc := Z.of_nat (length envp).
  Let argv0 := nth 0 argv [].
  Let argv1 := nth 1 argv [].
  Let L0 := Z.of_nat (length argv0).
  Let STR1 := usp + 8 * argc + 8 * envc + 184 + L0 + 1.

  Lemma io_argc_asan : 1 <= argc <= 1024.
  Proof. unfold argc. destruct Hva as [H _]. lia. Qed.

  (* [comment removed for export] *)
  Lemma io_vals_asan : forall E M, SINV1 sp rdraw brk0 argv envp uid hw E M ->
    ev E V_ARGC = Z_to_bv 64 argc /\ (2 <= argc -> uE E e_str1 = STR1 /\ uE E e_sp0 <= STR1).
  Proof.
    intros E M HS.
    destruct (vals_of_SINV1 sp rdraw brk0 argv envp Hsp Hva Hve uid hw Hfit E M HS) as (V0 & _ & _ & V3 & _).
    split; [exact V3|]. intros _. split.
    - destruct HS as ((Hev & _) & _). unfold uE.
      rewrite (edenot_ev_only E (E0 APH sp rdraw brk0 argv envp uid hw) NX0 e_str1 eq_refl eq_refl Hev).
      exact (u_e_str1 APH sp rdraw brk0 argv envp uid hw Hsp Hva Hve Hfit).
    - rewrite V0. pose proof io_argc_asan. unfold STR1, usp, L0, envc, argc in *. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma io_lay1_asan : 2 <= argc -> CEIL <= STR1 /\ STR1 + 8192 <= 2 ^ 64.
  Proof.
    intros H2. pose proof (Lay_asan sp rdraw argv envp Hsp Hva Hve uid hw Hfit) as LAY.
    destruct LAY as (L1 & L2 & L3 & L4 & L5 & L6 & L7 & L8 & L9).
    unfold CEIL, STR1, usp, argc, envc, L0, argv0 in *. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma io_rd1_asan : forall E M, SINV1 sp rdraw brk0 argv envp uid hw E M -> 2 <= argc ->
    rdn ASEGS M (Z_to_bv 64 STR1) (length argv1 + 1) = Some (argv1 ++ [Z_to_bv 8 0]).
  Proof.
    intros E M HS H2.
    assert (B : forall j, (j <= length argv1)%nat -> M (Z_to_bv 64 (STR1 + Z.of_nat j)) = Some (byte_at argv1 j)).
    { intros j Hj. exact (str_of_SINV1 sp rdraw brk0 argv envp Hsp Hva Hve uid hw Hfit E M 1%nat j HS H2 Hj). }
    destruct (io_lay1_asan H2) as [Ly1 Ly2]. unfold CEIL in Ly1.
    pose proof (Lay_asan sp rdraw argv envp Hsp Hva Hve uid hw Hfit) as (_ & _ & _ & L4 & _ & L6 & _ & L8 & _).
    specialize (L4 H2).
    rewrite (APSX.rdn_of_nth ASEGS M (length argv1 + 1) (Z_to_bv 64 STR1) (byte_at argv1)).
    - f_equal. apply map_byte_at_seq.
    - rewrite u64_lit by lia. unfold STR1, usp, argc, envc, L0, argv0, argv1 in *. lia.
    - intros j Hj. rewrite u64_lit by lia. cbn [rdn]. rewrite (B j ltac:(lia)). reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma io_arg1_asan : 2 <= argc ->
    Z.of_nat (length argv1) <= 131071 /\ ~ In (Z_to_bv 8 0) argv1 /\ path_has_slash argv1 = false /\ argv1 <> dotdot_path.
  Proof.
    intros H2. assert (Hl : (1 < length argv)%nat) by (unfold argc in H2; lia).
    split; [exact (valid_argv_str_len argv 1 Hva Hl)|].
    split; [exact (valid_argv_str_nz argv 1 Hva Hl)|].
    destruct Hva as (_ & _ & _ & _ & Htl).
    assert (Hin : In argv1 (tl argv)).
    { unfold argv1. destruct argv as [|a0 r]; [cbn in Hl; lia|]. cbn [nth tl]. apply nth_In. cbn in Hl. lia. }
    destruct (proj1 (Forall_forall _ _) Htl argv1 Hin) as [Hsl Hdd].
    split; [exact Hsl|]. intros E. rewrite E in Hdd. rewrite (proj2 (path_eqb_eq _ _) eq_refl) in Hdd. discriminate.
  Qed.

  (* [comment removed for export] *)
  Variable SV : env -> (word -> option byte) -> Prop.
  Hypothesis SV_to1 : forall E M, SV E M -> SINV1 sp rdraw brk0 argv envp uid hw E M.
  Hypothesis SV_frame : forall E M M', (forall a, argH0 APH sp rdraw argv envp uid hw E a = true -> M' a = M a) -> SV E M -> SV E M'.
  Hypothesis SV_agree : forall E E' M, env_agree NX0 E E' -> SV E M -> SV E' M.
  #[local] Notation AH := (argH0 APH sp rdraw argv envp uid hw).
  Variable T : iotab.
  (* [comment removed for export] *)
  Hypothesis H_class : match io_open T with
    | ONone => True
    | OTooLong => (4096 <= length argv1)%nat
    | ONoEnt => argv1 = [] \/ (argv1 <> dot_path /\ (length argv1 <= 4095)%nat /\ fs_lookup FS0 argv1 = None)
    | ODir => argv1 = dot_path
    | OFile lo hi => exists c, argv1 <> [] /\ argv1 <> dot_path /\ (length argv1 <= 4095)%nat /\ fs_lookup FS0 argv1 = Some c
                     /\ lo <= flen c <= hi
                     /\ (forall E M, SV E M -> forall j, 65536 * Z.of_nat j < 2 ^ 26 -> eb E (io_blob T + j)%nat = chunk j c)
                     /\ hdr_ok T c
    end.

  Theorem asan_io_ext_sound_fp : forall (FP : PropExec.FPState),
    APSC.ext_stmt_fp ASEGS INFO_ASAN NX0 LIMIT (ION.xn ASEGS T) SV AH FS0 FP.
  Proof.
    intros FP.
    exact (@io_ext_stmt FP ASEGS INFO_ASAN NX0 LIMIT SV AH FS0 asan_in_hull asan_hull_ok
             (argH0_high_asan sp rdraw argv envp Hsp Hva uid hw) (argH0_agree APH sp rdraw argv envp uid hw)
             SV_frame SV_agree NX0_sp0 T argc STR1 argv1
             (fun E M H => io_vals_asan E M (SV_to1 E M H)) (fun E M H => io_rd1_asan E M (SV_to1 E M H))
             io_argc_asan io_lay1_asan io_arg1_asan H_class (le_n NX0)).
  Qed.

  Theorem asan_io_ext2_sound_fp : forall (FP : PropExec.FPState),
    APSC.ext2_stmt_fp ASEGS INFO_ASAN NX0 LIMIT (ION.xb ASEGS NX0 T) SV AH FS0 FP.
  Proof.
    intros FP.
    exact (@io_ext2_stmt FP ASEGS INFO_ASAN NX0 LIMIT SV AH FS0
             (argH0_agree APH sp rdraw argv envp uid hw) SV_frame SV_agree NX0_sp0 T argc STR1 argv1
             (fun E M H => io_vals_asan E M (SV_to1 E M H)) (fun E M H => io_rd1_asan E M (SV_to1 E M H))
             io_argc_asan io_lay1_asan io_arg1_asan H_class).
  Qed.

  (* [comment removed for export] *)
  Theorem asan_io_ext_sound_cfg : forall (FPS : PropExec.FPState -> Prop),
    APSC.ext_stmt_cfg ASEGS INFO_ASAN NX0 LIMIT (ION.xn ASEGS T) SV AH FS0 FPS.
  Proof. intros FPS. apply APSC.ext_of_fp. intros FP _. exact (asan_io_ext_sound_fp FP). Qed.

  Theorem asan_io_ext2_sound_cfg : forall (FPS : PropExec.FPState -> Prop),
    APSC.ext2_stmt_cfg ASEGS INFO_ASAN NX0 LIMIT (ION.xb ASEGS NX0 T) SV AH FS0 FPS.
  Proof. intros FPS. apply APSC.ext2_of_fp. intros FP _. exact (asan_io_ext2_sound_fp FP). Qed.
End IOAsan.
