(* TRIAL NOT-OFFICIAL: AS/AsanNodesStartXAsan = our text + 's own edits to theories/Common/AsanNodesStartXAsan.v, 3-way merged (proposal md5 ); the old text is kept aside *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_agrees_alloc_forced_only.World Require Import Tgt_zlib_uncompress_fuzzer_asan.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_agrees_alloc_forced_only.AS Require Import PropExec CatExec CatSim SeqExec StoreOk ShapeAlg SpinAlg AgentLib AsanAcct AsanAcctShape. From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_agrees_alloc_forced_only.X1W.AS Require Import AsanAcctImages.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_agrees_alloc_forced_only.AS Require Import AxSymExec3 AxSymExec3Sound AxSymRun3 AsanPlanCore AsanPlan AsanPlanSound AsanInit. From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_agrees_alloc_forced_only.X1W.AS Require Import AsanPlanImages.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_agrees_alloc_forced_only.AS Require Import AsanNodesAux AsanStartLoops AsanNodesStartX AsanNodesStartXInit Asan_code_startx.
(* [comment removed for export] *)
Unset Lia Cache.
Local Instance asanreflect_fx : PropExec.FPState := PropExec.fx0.   (* [comment removed for export] *)
Import ListNotations.
Import AX2. Import AX2S. Import AP. Import APS.
Open Scope Z_scope.

Section AsanInstance.
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
  Hypothesis Hfit : entry_stack_fits sp argv envp.   (* [comment removed for export] *)
  (* a worker : the launch, as AsanInit takes it *)
  Variable apc : N.
  Variable gid : word.
  Variable groups : list word.
  Variable net : NetQueue.
  Variable kb : KernelBuild.
  Variables nof sigm : word.
  Variable abt : bool.
  Variable urnd : InputStream.
  Variable efn : list byte.
  Variable sigdef : bool.
  Let INP := AsanInit.inp argv envp fs stdin uid gid hw groups net nof sigm abt urnd kb efn sigdef.
  Hypothesis Hlaunch : valid_launch INP.
  Hypothesis Hlau : entry_launch_ok_va Sv48 (mkEntry sp brk0 mbase rdraw) INP.
  (* a worker A1: the run reads ASEGS ++ VSEGS (declared last, so callers append it after Hlau) *)
  Variable VSEGS : list Segment.
  Hypothesis VSEGS_nx : Forall (fun s => seg_executable s = false) VSEGS.

  #[local] Notation SINVA := (SINV0 APH apc sp rdraw brk0 mbase argv envp fs stdin uid gid hw groups net nof sigm abt urnd kb efn sigdef).
  #[local] Notation ARGH := (argH0 sp rdraw argv envp kb efn).
  #[local] Notation RZK := (rseq_z (kb_rseq kb)).

  Section AnySINV.
    (* [comment removed for export] *)
    Variable SINV : env -> (word -> option byte) -> Prop.
    Hypothesis SINV_SINV0 : forall E M, SINV E M -> SINVA E M.
    Hypothesis SINV_frame : forall E M M', (forall a, ARGH E a = true -> M' a = M a) -> SINV E M -> SINV E M'.
    (* [comment removed for export] *)
    Variable nx0 : nat.
    Hypothesis Hnx0 : (NX0 <= nx0)%nat.
    Hypothesis SINV_agree : forall E E' M, env_agree nx0 E E' -> SINV E M -> SINV E' M.

    Theorem node_x_sound_XEnvScan_asan_gen : x_stmt ASEGS VSEGS ASAN nx0 LIMIT RZK SINV ARGH FS0 XEnvScan.
    Proof.
      eapply (init_x_sound_envscan ASEGS VSEGS VSEGS_nx ASAN APH asan_wx asan_in_hull asan_hull_ok
                W_bb7d0 W_bb7d4 W_bb7d8
                ltac:(cbn [x_envscan x_envscan_k ASAN]; lia)
                (fetch_lit _ _ _ _ eq_refl F_bb7d0) (fetch_lit _ _ _ _ eq_refl F_bb7d4) (fetch_lit _ _ _ _ eq_refl F_bb7d8)
                ltac:(repeat split; reflexivity)
                D_bb7d0 D_bb7d4 D_bb7d8
                apc sp rdraw brk0 mbase argv envp fs stdin FS0 uid gid hw groups net kb nof sigm abt urnd efn sigdef
                Hsp Hva Hve Hfit Hlaunch Hlau SINV SINV_SINV0 SINV_frame nx0 Hnx0).
    Qed.

    Theorem node_x_sound_XPnScan_asan_gen : x_stmt ASEGS VSEGS ASAN nx0 LIMIT RZK SINV ARGH FS0 XPnScan.
    Proof.
      eapply (init_x_sound_pnscan ASEGS VSEGS VSEGS_nx ASAN APH asan_wx asan_in_hull asan_hull_ok
                W_bb88c W_bb890 W_bb894 W_bb898 W_bb89c
                ltac:(cbn [x_pnscan x_pnscan_k ASAN]; lia)
                (fetch_lit _ _ _ _ eq_refl F_bb88c) (fetch_lit _ _ _ _ eq_refl F_bb890) (fetch_lit _ _ _ _ eq_refl F_bb894)
                (fetch_lit _ _ _ _ eq_refl F_bb898) (fetch_lit _ _ _ _ eq_refl F_bb89c)
                ltac:(repeat split; reflexivity)
                D_bb88c D_bb890 D_bb894 D_bb898 D_bb89c
                apc sp rdraw brk0 mbase argv envp fs stdin FS0 uid gid hw groups net kb nof sigm abt urnd efn sigdef
                Hsp Hva Hve Hfit Hlau SINV SINV_SINV0 SINV_frame nx0 Hnx0 SINV_agree).
    Qed.

    Theorem node_x_sound_XLayout_asan_gen : x_stmt ASEGS VSEGS ASAN nx0 LIMIT RZK SINV ARGH FS0 XLayout.
    Proof. apply x_sound_layout. Qed.
  End AnySINV.

  (* [comment removed for export] *)
  Theorem node_x_sound_XEnvScan_asan :
    x_stmt ASEGS VSEGS ASAN NX0 LIMIT RZK SINVA ARGH FS0 XEnvScan.
  Proof. apply node_x_sound_XEnvScan_asan_gen; [auto | apply SINV0_frame | apply le_n]. Qed.

  Theorem node_x_sound_XPnScan_asan :
    x_stmt ASEGS VSEGS ASAN NX0 LIMIT RZK SINVA ARGH FS0 XPnScan.
  Proof.
    apply (node_x_sound_XPnScan_asan_gen _ (fun E M H => H)
             (SINV0_frame APH apc sp rdraw brk0 mbase argv envp fs stdin uid gid hw groups net nof sigm abt urnd kb efn sigdef)
             NX0 (le_n NX0)
             (SINV0_agree APH apc sp rdraw brk0 mbase argv envp fs stdin uid gid hw groups net nof sigm abt urnd kb efn sigdef)).
  Qed.

  Theorem node_x_sound_XLayout_asan :
    x_stmt ASEGS VSEGS ASAN NX0 LIMIT RZK SINVA ARGH FS0 XLayout.
  Proof. apply x_sound_layout. Qed.
End AsanInstance.
