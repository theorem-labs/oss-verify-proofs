(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: for LPS 727298f3, the section takes AsanInit's full launch (the input, mmap base, entry point, kernel build, exec file name and SIGPIPE disposition) and the image's table at the launch's own CONFIG_RSEQ layout (INFO_ASAN_at). *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys Require Import Uaccess.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.skcms.iccprofile_info.images Require Import Asan.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Asan Require Import
  PropExec CatExec CatSim SeqExec StoreOk StepTac ShapeAlg SpinAlg AgentLib Hoare RefMemcpyLib RefLayout ArgvEnv StartupAux
  AsanAcct AsanAcctShape AsanAcctImages.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Asan Require Import AxSymExec3 AxSymExec3Sound AxSymRun3 AsanPlanCore AsanPlan AsanPlanSound AsanPlanImages AsanInit.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Asan Require Import AsanAcctNoLazy.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Asan Require Import ArgLoops AsanNodesArg AsanNodesArgSoundCfg AsanNodesArgAsanCfg Arg_code_istrlen_asan.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Asan Require Import AsanStdioDefs AsanStdioWriteSCfg AsanNodesEmitSoundCfg.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Asan Require Import SpinAlgCfg AsanPlanSoundCfg.
Unset Nia Cache.  (* [comment removed for export] *)
Import ListNotations.
Import AX2. Import AX2S. Import APC. Import AP. Import APS. Import AN.
Unset Lia Cache.
Open Scope Z_scope.

Section EmitAsan.
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
  Variable kern : KernelBuild.
  Variable execfn : list byte.
  Context {sigpipe_default : bool}.   (* AsanInit's: the launch's SIGPIPE disposition at entry *)
  (* LPS 727298f3: [SINV1] and the layout facts of AsanNodesArgAsanCfg read the full launch
     input, so this Section takes it as AsanNodesArgAsanCfg does. *)
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
  Hypothesis Hkernel : in_kernel (inp argv envp fs stdin uid gid hw groups net nofile sigmask urnd kern execfn (sigpipe_default := sigpipe_default))
    = pinned_kernel (in_kernel (inp argv envp fs stdin uid gid hw groups net nofile sigmask urnd kern execfn (sigpipe_default := sigpipe_default))).
  Hypothesis Hlau : entry_launch_ok_va Sv48 (mkEntry sp brk0 mbase rdraw) (inp argv envp fs stdin uid gid hw groups net nofile sigmask urnd kern execfn (sigpipe_default := sigpipe_default)).
  (* LPS 727298f3: the image's table at the launch's own CONFIG_RSEQ layout. *)
  #[local] Notation IA := (INFO_ASAN_at (rseq_z (kb_rseq kern))) (only parsing).

  Lemma Gfile_asan : img_lo IA <= g_file_lo (argtab_of IA) /\ g_file_hi (argtab_of IA) <= img_hi IA
                     /\ img_lo IA <= g_canary_got (argtab_of IA) /\ g_canary_got (argtab_of IA) + 8 <= img_hi IA
                     /\ img_lo IA <= g_canary (argtab_of IA) /\ g_canary (argtab_of IA) + 8 <= img_hi IA.
  Proof. cbn. lia. Qed.

  Section AnyFP.
  Context {FP : PropExec.FPState}.

  (* [comment removed for export] *)
  Lemma stdio_asan_cfg : forall (H : word -> bool) regs mem model (su f wb wp fd : Z) (s l bufp bufsz can ret : word)
         (pending extra : list byte) (K : TSet),
    H_off_segments ASEGS H -> lazy_all_hidden H model ->
    range_avoids H (Z_to_bv 64 (su - 112)) 112 -> range_avoids H (Z_to_bv 64 wb) (length pending) -> range_avoids H s (length extra) ->
    getr regs 2%bv = Z_to_bv 64 su -> getr regs 10%bv = Z_to_bv 64 f -> getr regs 11%bv = s -> getr regs 12%bv = l -> getr regs 1%bv = ret ->
    4294967296 + 112 <= su -> su <= 0x800000000000 ->
    store_ok ASEGS mem (Z_to_bv 64 (su - 112)) 112 = true ->
    g_file_lo (argtab_of IA) <= f -> f + 232 <= g_file_hi (argtab_of IA) ->
    rdn ASEGS mem (Z_to_bv 64 (f + 40)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 wp)) ->
    rdn ASEGS mem (Z_to_bv 64 (f + 56)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 wb)) ->
    rdn ASEGS mem (Z_to_bv 64 (f + 120)) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 fd)) ->
    rdn ASEGS mem (Z_to_bv 64 (f + 88)) 8 = Some (word_to_le_bytes 8 bufp) ->
    rdn ASEGS mem (Z_to_bv 64 (f + 96)) 8 = Some (word_to_le_bytes 8 bufsz) ->
    rdn ASEGS mem (Z_to_bv 64 (g_canary_got (argtab_of IA))) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 (g_canary (argtab_of IA)))) ->
    rdn ASEGS mem (Z_to_bv 64 (g_canary (argtab_of IA))) 8 = Some (word_to_le_bytes 8 can) ->
    0 < fd < 2147483648 ->
    fd_lookup (m_fds model) (Z_to_bv 64 fd) = Some (FdChannel (Z_to_bv 64 fd)) ->
    m_channel_reader model = true ->
    m_halted model = None ->
    0 <= wb <= wp -> wp <= 0x800000000000 -> wp - wb = Z.of_nat (length pending) -> bv_unsigned l = Z.of_nat (length extra) ->
    Z.of_nat (length pending) + Z.of_nat (length extra) <= 2 ^ 30 ->
    Z.of_nat (length pending) + Z.of_nat (length extra) <= 2 ^ 30 ->
    (wp <= su - 112 \/ su <= wb) -> (bv_unsigned s + bv_unsigned l <= su - 112 \/ su <= bv_unsigned s) ->
    bv_unsigned s + bv_unsigned l <= 0x800000000000 ->
    rdn ASEGS mem (Z_to_bv 64 wb) (length pending) = Some pending -> rdn ASEGS mem s (length extra) = Some extra ->
    ret_ok ret -> K [] ->
    (forall regs' mem',
       getr regs' 10%bv = l -> getr regs' 2%bv = Z_to_bv 64 su -> getr regs' 1%bv = ret ->
       getr regs' 8%bv = getr regs 8%bv -> getr regs' 9%bv = getr regs 9%bv ->
       getr regs' 18%bv = getr regs 18%bv -> getr regs' 19%bv = getr regs 19%bv -> getr regs' 20%bv = getr regs 20%bv ->
       getr regs' 21%bv = getr regs 21%bv -> getr regs' 22%bv = getr regs 22%bv -> getr regs' 23%bv = getr regs 23%bv ->
       getr regs' 24%bv = getr regs 24%bv -> getr regs' 25%bv = getr regs 25%bv -> getr regs' 26%bv = getr regs 26%bv ->
       getr regs' 27%bv = getr regs 27%bv -> getr regs' 3%bv = getr regs 3%bv -> getr regs' 4%bv = getr regs 4%bv ->
       (forall x : word, ~ (su - 112 <= bv_unsigned x < su) -> ~ (f + 32 <= bv_unsigned x < f + 48) ->
                          ~ (f + 56 <= bv_unsigned x < f + 64) -> mem' x = mem x) ->
       mem_grows mem mem' ->
       rdn ASEGS mem' (Z_to_bv 64 (f + 32)) 8 = Some (word_to_le_bytes 8 (v_add bufp bufsz)) ->
       rdn ASEGS mem' (Z_to_bv 64 (f + 40)) 8 = Some (word_to_le_bytes 8 bufp) ->
       rdn ASEGS mem' (Z_to_bv 64 (f + 56)) 8 = Some (word_to_le_bytes 8 bufp) ->
       srealizes_cfg ASEGS (mkCfg (mkst regs' ret mem' (seg_rom ASEGS)) model) K) ->
    srealizes_cfg ASEGS (mkCfg (mkst regs (Z_to_bv 64 (g_stdio_write (argtab_of IA))) mem (seg_rom ASEGS)) model)
             (t_emit (map (WriteEv (Z_to_bv 64 fd)) (pending ++ extra)) K).
  Proof.
    intros H regs mem model su f wb wp fd s l bufp bufsz can ret pending extra K
           HH HL AVF AVP AVE Hsp' Ha0 Ha1 Ha2 Hra SUlo SUhi SOK0 Flo Fhi Fwp Fwb Ffd Fbuf Fbsz C1 C2 FD Hfd Hrdr Hh WBP WPhi
           LENP LENE MAX M30 DISJP DISJE SNW RDP RDE Hret HKnil HK.
    replace (Z_to_bv 64 (g_stdio_write (argtab_of IA))) with (0x93b18%bv : word) by (apply bv_eq; reflexivity).
    apply (asan_stdio_write_s_cfg H regs mem model su f wb wp fd s l bufp bufsz can ret pending extra K); try assumption.
    - constructor; assumption.
    - split; [exact C1 | exact C2].
    - intros regs' mem' G10 G2 G1 G8 G9 G18 G19 G20 G21 G22 G23 G24 G25 G26 G27 G3 G4 HPOST.
      destruct HPOST as [Pagree Pgrows Pwend Pwpos Pwbase].
      apply (HK regs' mem'); assumption.
  Qed.

  (* [comment removed for export] *)
  Variable SV : env -> (word -> option byte) -> Prop.
  Hypothesis SV_to1 : forall E M, SV E M -> SINV1 sp rdraw brk0 argv envp uid hw apc mbase fs stdin gid groups net nofile sigmask urnd kern execfn (sigpipe_default := sigpipe_default) E M.
  Hypothesis SV_frame : forall E M M', (forall a, argH0 sp rdraw argv envp kern execfn E a = true -> M' a = M a) -> SV E M -> SV E M'.
  Hypothesis SV_agree : forall E E' M, env_agree NX0 E E' -> SV E M -> SV E' M.
  #[local] Notation AH := (argH0 sp rdraw argv envp kern execfn).

  Theorem asan_emit_sound_fp : APSC.emit_stmt_fp ASEGS IA NX0 LIMIT (xe ASEGS IA NX0) SV AH FS0 FP.
  Proof.
    pose proof (Lay_asan sp rdraw brk0 argv envp Hsp Hva Hve uid hw Hfit FS0 apc mbase fs stdin gid groups net nofile sigmask urnd kern execfn Hkernel Hlau) as LAY. pose proof istrlen_ecalls as EC.
    eapply (xe_sound ASEGS IA NX0 LIMIT SV AH FS0 asan_in_hull asan_hull_ok
             (argH0_high_asan sp rdraw argv envp Hsp Hva kern execfn)
             (argH0_agree sp rdraw argv envp kern execfn) SV_frame SV_agree NX0_sp0
             W_63514 W_63518 W_6351c W_63520 W_63524 W_63528 W_6352c);
      [cbn; lia | exact EC | exact LAY
      | exact (fun E M H => vals_of_SINV1 sp rdraw brk0 argv envp Hsp Hva Hve uid hw Hfit FS0 apc mbase fs stdin gid groups net nofile sigmask urnd kern execfn Hkernel Hlau E M (SV_to1 E M H))
      | exact (fun E M i j H => str_of_SINV1 sp rdraw brk0 argv envp Hsp Hva Hve uid hw Hfit FS0 apc mbase fs stdin gid groups net nofile sigmask urnd kern execfn Hkernel Hlau E M i j (SV_to1 E M H))
      | exact (Gro_asan kern) | exact stdio_asan_cfg | exact Gfile_asan].
  Qed.
  End AnyFP.

  (* [comment removed for export] *)
  Theorem asan_emit_sound_cfg : forall (SV : env -> (word -> option byte) -> Prop) (FPS : PropExec.FPState -> Prop),
    (forall E M, SV E M -> SINV1 sp rdraw brk0 argv envp uid hw apc mbase fs stdin gid groups net nofile sigmask urnd kern execfn (sigpipe_default := sigpipe_default) E M) ->
    (forall E M M', (forall a, argH0 sp rdraw argv envp kern execfn E a = true -> M' a = M a) -> SV E M -> SV E M') ->
    (forall E E' M, env_agree NX0 E E' -> SV E M -> SV E' M) ->
    APSC.emit_stmt_cfg ASEGS IA NX0 LIMIT (xe ASEGS IA NX0) SV (argH0 sp rdraw argv envp kern execfn) FS0 FPS.
  Proof using All.
    intros SV FPS H1 H2 H3. apply APSC.emit_of_fp. intros FP _.
    exact (@asan_emit_sound_fp FP SV H1 H2 H3).
  Qed.
End EmitAsan.
