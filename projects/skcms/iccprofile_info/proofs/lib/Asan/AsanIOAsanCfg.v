(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: for LPS 727298f3, the section takes AsanInit's full launch (the input, mmap base, entry point, kernel build, exec file name and SIGPIPE disposition) and the image's table at the launch's own CONFIG_RSEQ layout (INFO_ASAN_at), and argv[1]'s address follows the launch's string layout (block_head_size, block_pad_len). *)
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

(* An AsanInit fact, whichever of AsanInit's Section variables its proof used (as in
   AsanNodesArgAsanCfg). *)
#[local] Ltac init_fact L := unshelve (eapply L; try eassumption); try exact APH; try reflexivity.

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
  Variable apc : N.
  Variable mbase : word.
  Variable fs : Fs.Fs.
  Variable stdin : InputStream.
  Variable gid : word.
  Variable groups : list word.
  Variable net : NetQueue.
  Variable nofile : word.
  Variable sigmask : word.
  Variable urnd : InputStream.
  Variable kern : KernelBuild.
  Variable execfn : list byte.
  Context {sigpipe_default : bool}.   (* AsanInit's: the launch's SIGPIPE disposition at entry *)
  (** [recorded_kernel]'s eight fields, from [Run.valid_input]'s last conjunct; CONFIG_RSEQ,
      thp, ASLR, the guard gap and the random bits are free.  See [AsanInit.pinned_kernel]. *)
  Hypothesis Hkernel : in_kernel (inp argv envp fs stdin uid gid hw groups net nofile sigmask urnd kern execfn (sigpipe_default := sigpipe_default))
    = pinned_kernel (in_kernel (inp argv envp fs stdin uid gid hw groups net nofile sigmask urnd kern execfn (sigpipe_default := sigpipe_default))).
  Hypothesis Hlaunch : valid_launch (inp argv envp fs stdin uid gid hw groups net nofile sigmask urnd kern execfn (sigpipe_default := sigpipe_default)).
  Hypothesis Hlau : entry_launch_ok_va Sv48 (mkEntry sp brk0 mbase rdraw) (inp argv envp fs stdin uid gid hw groups net nofile sigmask urnd kern execfn (sigpipe_default := sigpipe_default)).
  (* LPS 727298f3: the image's table at the launch's own CONFIG_RSEQ layout. *)
  #[local] Notation IA := (INFO_ASAN_at (rseq_z (kb_rseq kern))) (only parsing).

  Let usp := bv_unsigned sp.
  Let argc := Z.of_nat (length argv).
  Let argv0 := nth 0 argv [].
  Let argv1 := nth 1 argv [].
  Let L0 := Z.of_nat (length argv0).
  (* LPS 727298f3: argv[1] follows argv[0] in the strings, which start [block_head_size] plus
     [block_pad_len] above sp (AsanInit.u_e_str1). *)
  Let rseq := kb_rseq kern.
  Let top := ed_top rdraw.
  Let CHEAD := Z.of_nat (block_head_size rseq argv envp).
  Let W := Z.of_nat (block_pad_len rseq sp top argv envp execfn).
  Let STR1 := usp + CHEAD + W + L0 + 1.

  Lemma io_argc_asan : 1 <= argc <= 1024.
  Proof. unfold argc. destruct Hva as [H _]. lia. Qed.

  (* [comment removed for export] *)
  Lemma io_vals_asan : forall E M, SINV1 sp rdraw brk0 argv envp uid hw apc mbase fs stdin gid groups net nofile sigmask urnd kern execfn (sigpipe_default := sigpipe_default) E M ->
    ev E V_ARGC = Z_to_bv 64 argc /\ (2 <= argc -> uE E (e_str1 IA) = STR1 /\ uE E e_sp0 <= STR1).
  Proof using All.
    intros E M HS.
    destruct (vals_of_SINV1 sp rdraw brk0 argv envp Hsp Hva Hve uid hw Hfit FS0 apc mbase fs stdin gid groups net nofile sigmask urnd kern execfn Hkernel Hlau E M HS) as (V0 & _ & _ & V3 & _).
    split; [exact V3|]. intros _. split.
    - destruct HS as ((Hev & _) & _).
      (* the AsanInit fact against [uE] still folded, as AsanNodesArgAsanCfg.vals_of_SINV1 takes
         [u_e_str0]: against the unfolded [bv_unsigned (edenot …)] the unifier evaluates [E0]
         and never returns. *)
      assert (U : uE (E0 sp rdraw brk0 argv envp uid kern execfn) (e_str1 IA) = STR1)
        by (unfold STR1, usp, CHEAD, W, L0, argv0, rseq, top; init_fact AsanInit.u_e_str1).
      unfold uE in *.
      rewrite (edenot_ev_only E (E0 sp rdraw brk0 argv envp uid kern execfn) NX0 (e_str1 IA))
        by (first [exact Hev | unfold e_str1, e_str0, e_atrandom; cbn [a_rseq INFO_ASAN_at]; destruct (kb_rseq kern); vm_compute; reflexivity]).
      exact U.
    - rewrite V0. unfold STR1, usp, CHEAD, W, L0, argv0. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma io_lay1_asan : 2 <= argc -> CEIL <= STR1 /\ STR1 + 8192 <= 2 ^ 64
    /\ STR1 + Z.of_nat (length argv1) + 1 <= TASK_SIZE.
  Proof using All.
    intros H2. pose proof (Lay_asan sp rdraw brk0 argv envp Hsp Hva Hve uid hw Hfit FS0 apc mbase fs stdin gid groups net nofile sigmask urnd kern execfn Hkernel Hlau) as LAY.
    destruct LAY as (L1 & L2 & L3 & L4 & L5 & L6 & L7 & L8 & L9).
    specialize (L4 H2).
    unfold CEIL, TASK_SIZE, STR1, usp, CHEAD, W, rseq, top, argc, L0, argv0, argv1 in *. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma io_rd1_asan : forall E M, SINV1 sp rdraw brk0 argv envp uid hw apc mbase fs stdin gid groups net nofile sigmask urnd kern execfn (sigpipe_default := sigpipe_default) E M -> 2 <= argc ->
    rdn ASEGS M (Z_to_bv 64 STR1) (length argv1 + 1) = Some (argv1 ++ [Z_to_bv 8 0]).
  Proof using All.
    intros E M HS H2.
    assert (B : forall j, (j <= length argv1)%nat -> M (Z_to_bv 64 (STR1 + Z.of_nat j)) = Some (byte_at argv1 j)).
    { intros j Hj. exact (str_of_SINV1 sp rdraw brk0 argv envp Hsp Hva Hve uid hw Hfit FS0 apc mbase fs stdin gid groups net nofile sigmask urnd kern execfn Hkernel Hlau E M 1%nat j HS H2 Hj). }
    destruct (io_lay1_asan H2) as (Ly1 & Ly2 & Ly3). unfold CEIL in Ly1. unfold TASK_SIZE in Ly3.
    rewrite (APSX.rdn_of_nth ASEGS M (length argv1 + 1) (Z_to_bv 64 STR1) (byte_at argv1)).
    - f_equal. apply map_byte_at_seq.
    - rewrite u64_lit by lia. lia.
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
  Hypothesis SV_to1 : forall E M, SV E M -> SINV1 sp rdraw brk0 argv envp uid hw apc mbase fs stdin gid groups net nofile sigmask urnd kern execfn (sigpipe_default := sigpipe_default) E M.
  Hypothesis SV_frame : forall E M M', (forall a, argH0 sp rdraw argv envp kern execfn E a = true -> M' a = M a) -> SV E M -> SV E M'.
  Hypothesis SV_agree : forall E E' M, env_agree NX0 E E' -> SV E M -> SV E' M.
  #[local] Notation AH := (argH0 sp rdraw argv envp kern execfn).
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
    APSC.ext_stmt_fp ASEGS IA NX0 LIMIT (ION.xn ASEGS T IA) SV AH FS0 FP.
  Proof.
    intros FP.
    exact (@io_ext_stmt FP ASEGS IA NX0 LIMIT SV AH FS0 asan_in_hull asan_hull_ok
             (argH0_high_asan sp rdraw argv envp Hsp Hva kern execfn) (argH0_agree sp rdraw argv envp kern execfn)
             SV_frame SV_agree NX0_sp0 T argc STR1 argv1
             (fun E M H => io_vals_asan E M (SV_to1 E M H)) (fun E M H => io_rd1_asan E M (SV_to1 E M H))
             io_argc_asan io_lay1_asan io_arg1_asan H_class (le_n NX0)).
  Qed.

  Theorem asan_io_ext2_sound_fp : forall (FP : PropExec.FPState),
    APSC.ext2_stmt_fp ASEGS IA NX0 LIMIT (ION.xb ASEGS NX0 T IA) SV AH FS0 FP.
  Proof.
    intros FP.
    exact (@io_ext2_stmt FP ASEGS IA NX0 LIMIT SV AH FS0
             (argH0_agree sp rdraw argv envp kern execfn) SV_frame SV_agree NX0_sp0 T argc STR1 argv1
             (fun E M H => io_vals_asan E M (SV_to1 E M H)) (fun E M H => io_rd1_asan E M (SV_to1 E M H))
             io_argc_asan io_lay1_asan io_arg1_asan H_class).
  Qed.

  (* [comment removed for export] *)
  Theorem asan_io_ext_sound_cfg : forall (FPS : PropExec.FPState -> Prop),
    APSC.ext_stmt_cfg ASEGS IA NX0 LIMIT (ION.xn ASEGS T IA) SV AH FS0 FPS.
  Proof using All. intros FPS. apply APSC.ext_of_fp. intros FP _. exact (asan_io_ext_sound_fp FP). Qed.

  Theorem asan_io_ext2_sound_cfg : forall (FPS : PropExec.FPState -> Prop),
    APSC.ext2_stmt_cfg ASEGS IA NX0 LIMIT (ION.xb ASEGS NX0 T IA) SV AH FS0 FPS.
  Proof using All. intros FPS. apply APSC.ext2_of_fp. intros FP _. exact (asan_io_ext2_sound_fp FP). Qed.
End IOAsan.
