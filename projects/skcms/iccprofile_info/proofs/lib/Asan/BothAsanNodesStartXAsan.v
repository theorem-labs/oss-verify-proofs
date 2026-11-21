(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* Modified by Theorem Labs, 2026-11: for LPS 727298f3, the section takes AsanInit's full launch (with the kernel build at pinned_kernel) and the image's table at the launch's own CONFIG_RSEQ layout (INFO_BOTH_at). *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.skcms.iccprofile_info.images Require Import AsanUbsan.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Asan Require Import
  PropExec CatExec CatSim SeqExec StoreOk ShapeAlg SpinAlg AgentLib
  AsanAcct AsanAcctShape BothAsanAcctImages.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Asan Require Import AxSymExec3 AxSymExec3Sound AxSymRun3 AsanPlanCore AsanPlan AsanPlanSound AsanInit BothAsanPlanImages.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Asan Require Import AsanNodesAux AsanStartLoops AsanNodesStartX AsanNodesStartXInit BothAsan_code_startx.
Unset Nia Cache.  (* [comment removed for export] *)
Import ListNotations.
Import AX2. Import AX2S. Import AP. Import APS.
Unset Lia Cache.
Local Instance asanreflect_fx : PropExec.FPState := PropExec.fx0.
Open Scope Z_scope.

(* [comment removed for export] *)
Lemma asan_Fe1 {r : Z} : fetch_word ASEGS (Z_to_bv 64 (x_envscan (INFO_BOTH_at r))) = Some W_8ea54.
Proof. exact (fetch_lit _ _ _ _ eq_refl F_8ea54). Qed.
Lemma asan_Fe2 {r : Z} : fetch_word ASEGS (Z_to_bv 64 (x_envscan (INFO_BOTH_at r) + 4)) = Some W_8ea58.
Proof. exact (fetch_lit _ _ _ _ eq_refl F_8ea58). Qed.
Lemma asan_Fe3 {r : Z} : fetch_word ASEGS (Z_to_bv 64 (x_envscan (INFO_BOTH_at r) + 8)) = Some W_8ea5c.
Proof. exact (fetch_lit _ _ _ _ eq_refl F_8ea5c). Qed.
Lemma asan_Fp0 {r : Z} : fetch_word ASEGS (Z_to_bv 64 (x_pnscan (INFO_BOTH_at r) - 8)) = Some W_8eb10.
Proof. exact (fetch_lit _ _ _ _ eq_refl F_8eb10). Qed.
Lemma asan_Fp1 {r : Z} : fetch_word ASEGS (Z_to_bv 64 (x_pnscan (INFO_BOTH_at r) - 4)) = Some W_8eb14.
Proof. exact (fetch_lit _ _ _ _ eq_refl F_8eb14). Qed.
Lemma asan_Fp2 {r : Z} : fetch_word ASEGS (Z_to_bv 64 (x_pnscan (INFO_BOTH_at r))) = Some W_8eb18.
Proof. exact (fetch_lit _ _ _ _ eq_refl F_8eb18). Qed.
Lemma asan_Fp3 {r : Z} : fetch_word ASEGS (Z_to_bv 64 (x_pnscan (INFO_BOTH_at r) + 4)) = Some W_8eb1c.
Proof. exact (fetch_lit _ _ _ _ eq_refl F_8eb1c). Qed.
Lemma asan_Fp4 {r : Z} : fetch_word ASEGS (Z_to_bv 64 (x_pnscan (INFO_BOTH_at r) + 8)) = Some W_8eb20.
Proof. exact (fetch_lit _ _ _ _ eq_refl F_8eb20). Qed.

Section AsanInstance.
  Variable sp : word.
  Variable rdraw : EntryDraw.
  Variable brk0 mbase : word.
  Variable argv envp : list (list byte).
  Variable fs : Fs.Fs.
  Variable stdin : InputStream.
  Variable FS0 : Fs.Fs.
  Hypothesis Hsp : valid_sp sp.
  Hypothesis Hva : valid_argv argv.
  Hypothesis Hve : valid_envp envp.
  Variable uid hw : word.
  Hypothesis Hfit : entry_stack_fits sp argv envp.
  Variable apc : N.
  Variable gid : word.
  Variable groups : list word.
  Variable net : NetQueue.
  Variable nofile : word.
  Variable sigmask : word.
  Variable urnd : InputStream.
  Variable kern : KernelBuild.
  Variable execfn : list byte.
  Context {sigpipe_default : bool}.   (* AsanInit's: the launch's SIGPIPE disposition at entry *)
  Hypothesis Hmb : valid_mmap_base mbase.
  (** see [AsanInit.pinned_kernel]: [recorded_kernel]'s eight fields; CONFIG_RSEQ free *)
  Hypothesis Hkernel : in_kernel (inp argv envp fs stdin uid gid hw groups net nofile sigmask urnd kern execfn (sigpipe_default := sigpipe_default))
    = pinned_kernel (in_kernel (inp argv envp fs stdin uid gid hw groups net nofile sigmask urnd kern execfn (sigpipe_default := sigpipe_default))).
  Hypothesis Hlaunch : valid_launch (inp argv envp fs stdin uid gid hw groups net nofile sigmask urnd kern execfn (sigpipe_default := sigpipe_default)).
  Hypothesis Hlau : entry_launch_ok_va Sv48 (mkEntry sp brk0 mbase rdraw) (inp argv envp fs stdin uid gid hw groups net nofile sigmask urnd kern execfn (sigpipe_default := sigpipe_default)).
  (* LPS 727298f3: the image's table at the launch's own CONFIG_RSEQ layout. *)
  #[local] Notation IA := (INFO_BOTH_at (rseq_z (kb_rseq kern))) (only parsing).

  Section AnySINV.
    (* [comment removed for export] *)
    Variable SINV : env -> (word -> option byte) -> Prop.
    Hypothesis SINV_SINV0 : forall E M, SINV E M -> SINV0 APH apc sp rdraw brk0 mbase argv envp fs stdin uid gid hw groups net nofile sigmask urnd kern execfn (sigpipe_default := sigpipe_default) E M.
    Hypothesis SINV_frame : forall E M M', (forall a, argH0 sp rdraw argv envp kern execfn E a = true -> M' a = M a) -> SINV E M -> SINV E M'.
    Hypothesis SINV_agree : forall E E' M, env_agree NX0 E E' -> SINV E M -> SINV E' M.

    Theorem node_x_sound_XEnvScan_asan_gen :
      x_stmt ASEGS IA NX0 LIMIT SINV (argH0 sp rdraw argv envp kern execfn) FS0 XEnvScan.
    Proof.
      eapply (init_x_sound_envscan ASEGS IA APH asan_wx asan_in_hull W_8ea54 W_8ea58 W_8ea5c);
        first [ exact asan_Fe1 | exact asan_Fe2 | exact asan_Fe3 | exact D_8ea54 | exact D_8ea58 | exact D_8ea5c
              | (cbn [x_envscan x_envscan_k INFO_BOTH_at]; lia) | (repeat split; reflexivity) | reflexivity | eassumption ].
    Qed.

    Theorem node_x_sound_XPnScan_asan_gen :
      x_stmt ASEGS IA NX0 LIMIT SINV (argH0 sp rdraw argv envp kern execfn) FS0 XPnScan.
    Proof.
      eapply (init_x_sound_pnscan ASEGS IA APH asan_wx asan_in_hull asan_hull_ok W_8eb10 W_8eb14 W_8eb18 W_8eb1c W_8eb20);
        first [ exact asan_Fp0 | exact asan_Fp1 | exact asan_Fp2 | exact asan_Fp3 | exact asan_Fp4
              | exact D_8eb10 | exact D_8eb14 | exact D_8eb18 | exact D_8eb1c | exact D_8eb20
              | (cbn [x_pnscan x_pnscan_k INFO_BOTH_at]; lia) | (repeat split; reflexivity) | reflexivity | eassumption ].
    Qed.

    Theorem node_x_sound_XLayout_asan_gen :
      x_stmt ASEGS IA NX0 LIMIT SINV (argH0 sp rdraw argv envp kern execfn) FS0 XLayout.
    Proof. apply x_sound_layout. Qed.
  End AnySINV.

  (* [comment removed for export] *)
  Theorem node_x_sound_XEnvScan_asan :
    x_stmt ASEGS IA NX0 LIMIT (SINV0 APH apc sp rdraw brk0 mbase argv envp fs stdin uid gid hw groups net nofile sigmask urnd kern execfn (sigpipe_default := sigpipe_default)) (argH0 sp rdraw argv envp kern execfn) FS0 XEnvScan.
  Proof. apply node_x_sound_XEnvScan_asan_gen; first [exact (fun E M H => H) | apply SINV0_frame | apply SINV0_agree]. Qed.

  Theorem node_x_sound_XPnScan_asan :
    x_stmt ASEGS IA NX0 LIMIT (SINV0 APH apc sp rdraw brk0 mbase argv envp fs stdin uid gid hw groups net nofile sigmask urnd kern execfn (sigpipe_default := sigpipe_default)) (argH0 sp rdraw argv envp kern execfn) FS0 XPnScan.
  Proof. apply node_x_sound_XPnScan_asan_gen; first [exact (fun E M H => H) | apply SINV0_frame | apply SINV0_agree]. Qed.

  Theorem node_x_sound_XLayout_asan :
    x_stmt ASEGS IA NX0 LIMIT (SINV0 APH apc sp rdraw brk0 mbase argv envp fs stdin uid gid hw groups net nofile sigmask urnd kern execfn (sigpipe_default := sigpipe_default)) (argH0 sp rdraw argv envp kern execfn) FS0 XLayout.
  Proof. apply x_sound_layout. Qed.
End AsanInstance.
