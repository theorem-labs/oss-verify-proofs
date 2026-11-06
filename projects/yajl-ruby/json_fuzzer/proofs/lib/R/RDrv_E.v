(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation Strings.String.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Common Require Import ShapeAlg ShapeAlgCfg.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import Tac Image ZBridge SysStep ITree ITreeCfg Nodes NodesCfg Decode Arr FP InitMem.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import Images.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Top Require Import ImplRz ImplRzCfg TrzNodesCfg TrzStdioCfg TrzLeafCfg ImplSplitCfg.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Agent Require Import MallocBlocks.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.MS Require Import Malloc_iface.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Spec Require Import Prelim STree Malloc Monad StdioBase Stdio FmtFp Driver RawAlloc MSafe MLive.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.R Require Import RMallocRep RMallocTree RMalloc_iface R_StartupLib R_Startup R_Exit RF_pad RF_stdio_lib Stdio_iface RF_printf_iface Stdio_init RF_syscalls RF_memcpy RF_fwritex_gen Printf_model.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.R Require Import RDrv_iface RDrv_ctx RDrv_kio RDrv_A RDrv_B RDrv_C RDrv_run RDrv_run2 RDrv_D.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
Lemma open_classify_may : forall path mo ent, open_classify path mo = OcMay ent ->
  ent = FdDir \/ (exists d, ent = FdFile path (Z_to_bv 64 0) /\ fs_lookup (m_fs mo) path = Some d).
Proof.
  intros path mo ent H. unfold open_classify in H.
  destruct (path_max <=? length path)%nat; [discriminate H|].
  destruct path as [|c p]; [discriminate H|].
  destruct (path_is_dirref (c :: p)); [left; inversion H; reflexivity|].
  destruct (fs_lookup (m_fs mo) (c :: p)) as [d|] eqn:E; [| discriminate H].
  right. exists d. inversion H. split; [reflexivity | first [exact E | reflexivity]].
Qed.

Section E.
  Context {RC__ : OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.RunCeiling.RunCeiling}.
  Variables (sp0 : word) (argv envp : list (list byte)) (uid hw : word) (rnd : EntryDraw).
  Hypothesis VSP : valid_sp sp0.
  Hypothesis RCSP : rc_sp = bv_unsigned sp0.          (* [comment removed for export] *)
  Hypothesis RCS : rc_secret = bv_unsigned (secret_of (at_random_bytes (ed_random rnd))).   (* [comment removed for export] *)
  Hypothesis EFIT : entry_stack_fits sp0 argv envp.   (* [comment removed for export] *)
  Hypothesis VARGV : valid_argv argv.
  Hypothesis VENVP : valid_envp envp.
  Variable HKG : HKG_T.
  Hypothesis DI : drv_iface HKG.
  Variables (MO : Model) (FS0 : Fs.Fs).
  Notation HK := (HKG (G_fs FS0)).
  Hypothesis YF : yfuzz_rz_stmt HK.

  Notation usp0 := (bv_unsigned sp0).

  (* [comment removed for export] *)
  Hypothesis MOFS : m_fs MO = FS0.
  Hypothesis MOFD : alloc_fd (m_fds MO) = Z_to_bv 64 3.
  Hypothesis MOFD3 : fd_lookup (m_fds MO) (Z_to_bv 64 3) = None.
  Hypothesis MOh : m_halted MO = None.
  Hypothesis MOl : m_vm_lazy MO = [].
  (* [comment removed for export] *)
  Hypothesis HKI : forall m : mem,
    (forall a : word, 0x55040 <= bv_unsigned a < 0x553f0 -> m a = None) ->
    rw_cells rsegs m 0x54fd0 [C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C4 (Z_to_bv 64 0)] ->
    rw_cells rsegs m 0x54fd8 [C8 (Z_to_bv 64 (auxv_addr sp0 argv envp)); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 224); C8 (Z_to_bv 64 8); C8 (Z_to_bv 64 0);
                              C8 (Z_to_bv 64 4096); CB 48 (repeat (Z_to_bv 8 0) 48)] ->
    rw_cells rsegs m 0x23928 [C8 (Z_to_bv 64 0x54fb0)] ->
    rw_cells rsegs m 0x54fb0 [C8 rc_guard] ->   (* [comment removed for export] *)
    mem_inv rsegs m ->
    HK ps0 [] m MO /\ rw_cells rsegs m RAUXV_CELL [C8 (Z_to_bv 64 (auxv_addr sp0 argv envp))].

  Let DIR := di_run HKG DI.

  (* [comment removed for export] *)
  Theorem rz_main_usage : forall ms, rat_main sp0 argv envp uid hw rnd ms -> Z.of_nat (length argv) <> 2 ->
    realizes_cfg acfg rsegs (mkCfg ms MO) (TDIE (pieces_usage (map bv_unsigned (hd [] argv))) stdout_init FS0).
  Proof.
    intros ms AM HARGC. unfold TDIE, TEXIT2. rewrite <- MOFS.
    exact (main_usage sp0 argv envp uid hw rnd VSP RCSP RCS EFIT VARGV VENVP HK (DIR _) (di_frame HKG DI _) (di_ssp HKG DI _) (di_libc_head HKG DI _)
             MO HKI MOh MOl ms AM HARGC).
  Qed.

  (* [comment removed for export] *)
  Section Two.
    Variables (arg0 arg1 : list byte).
    Hypothesis EARGV : argv = [arg0; arg1].

    (* [comment removed for export] *)
    Definition KLOOP (ent : FdEntry) : TSet :=
      match ent with
      | FdDir => TDIE (pieces_read_error (map bv_unsigned arg1)) stdout_init FS0
      | FdFile p _ => match fs_lookup FS0 p with
                      | Some FILE => TFIN FS0 FILE (KDONE FS0 FILE)
                      | None => TDIE [] stdout_init FS0
                      end
      | _ => TDIE [] stdout_init FS0
      end.
    (* [comment removed for export] *)
    Definition DRV2 : TSet :=
      match open_classify arg1 MO with
      | OcErrno _ => TDIE (pieces_cannot_open (map bv_unsigned arg1)) stdout_init FS0
      | OcMay ent => t_alt2 (TDIE (pieces_cannot_open (map bv_unsigned arg1)) stdout_init FS0) (KLOOP ent)
      end.

    Lemma KLOOP_nil : forall ent, KLOOP ent [].
    Proof.
      intros ent. unfold KLOOP. destruct ent; try apply TDIE_nil.
      destruct (fs_lookup FS0 _); [| apply TDIE_nil]. apply TFIN_nil. apply KDONE_nil.
    Qed.

    Theorem rz_main2 : forall ms, rat_main sp0 argv envp uid hw rnd ms -> realizes_cfg acfg rsegs (mkCfg ms MO) DRV2.
    Proof.
      intros ms AM.
      assert (ARGC : argc argv = 2) by (unfold argc; rewrite EARGV; reflexivity).
      rz_seg MOh MOl.
      eapply (main_to_test sp0 argv envp uid hw rnd VSP RCSP RCS EFIT VARGV VENVP HK (di_frame HKG DI _) MO HKI); [exact AM|].
      intros t t0 t1 t2 a3 a4 a5 a6 a7 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 mm pad Ht FR BA HK0 ERR RSG.
      pose proof (sp_facts sp0 VSP RCSP) as SF. unfold LO in SF.
      pose proof BA as (ST & MI & _). unfold LO in ST.
      rewrite ARGC. zstep. if_cases K0; zify_cond K0; [exfalso; rewrite ?unsigned_lit in K0 by lia; lia|]. clear K0.
      apply evt_done. unfold DRV2.
      apply (rz_read_all_head sp0 argv envp uid hw rnd arg0 arg1 t pad s4 s5 s6 s7 s8 s9 s10 s11 VSP RCSP EFIT VARGV VENVP EARGV Ht HKG DI FS0
               MO MOFS MOFD MOFD3 KLOOP t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6 (Z_to_bv 32 0) mm FR BA HK0 ERR RSG
               ltac:(reflexivity) KLOOP_nil).
      intros ent s mo ms' P1v OC HP1 P1R RI.
      destruct (open_classify_may _ _ _ OC) as [-> | (d & -> & FSL)].
      - (* [comment removed for export] *)
        exact (rz_loop_dir sp0 argv envp uid hw rnd arg0 arg1 t pad s4 s5 s6 s7 s8 s9 s10 s11 VSP RCSP EFIT VARGV VENVP EARGV Ht HKG DI FS0 P1v HP1 P1R s mo ms' RI).
      - (* [comment removed for export] *)
        unfold KLOOP. rewrite MOFS in FSL. rewrite FSL.
        apply (rz_loop0 sp0 argv envp uid hw rnd arg0 arg1 t pad s4 s5 s6 s7 s8 s9 s10 s11 VSP RCSP EFIT VARGV VENVP EARGV Ht HKG DI FS0 P1v arg1 d
                 (KDONE FS0 d) (KDONE_nil FS0 d)) with (s := s).
        + intros cap s' mo' ms'' RB LTC.
          exact (rz_after_loop sp0 argv envp uid hw rnd arg0 arg1 t pad s4 s5 s6 s7 s8 s9 s10 s11 VSP RCSP EFIT VARGV VENVP EARGV Ht HKG DI FS0 YF P1v arg1 d cap s' mo' ms'' RB LTC).
        + exact RI.
        + destruct RI as (x1 & u0 & u1 & u2 & b0 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & x23 & u3 & u4 & u5 & u6 & F & fc & mm' & A & _ & RC & _).
          destruct RC as (junk & stg & errv & bufp & _ & _ & _ & FS & _). rewrite FS. exact FSL.
    Qed.
  End Two.
End E.


(* [comment removed for export] *)
Section RC__9.
Context {RC__ : OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.RunCeiling.RunCeiling}.
Definition DRV (MO : Model) (fs0 : Fs.Fs) (argv : list (list byte)) : TSet :=
  match argv with
  | [_; a1] => DRV2 MO fs0 a1
  | _ => TDIE (pieces_usage (map bv_unsigned (hd [] argv))) stdout_init fs0
  end.

Theorem rz_main_drv :
  forall (sp0 : word) (argv envp : list (list byte)) (uid hw : word) (rnd : EntryDraw),
  valid_sp sp0 ->
  rc_sp = bv_unsigned sp0 ->                                                  (* [comment removed for export] *)
  rc_secret = bv_unsigned (secret_of (at_random_bytes (ed_random rnd))) ->   (* [comment removed for export] *)
  entry_stack_fits sp0 argv envp ->                                          (* [comment removed for export] *)
  valid_argv argv -> valid_envp envp ->
  forall (HKG : HKG_T) (FS0 : Fs.Fs), drv_iface HKG -> yfuzz_rz_stmt (HKG (G_fs FS0)) ->
  forall (MO : Model),
  m_fs MO = FS0 -> alloc_fd (m_fds MO) = Z_to_bv 64 3 -> fd_lookup (m_fds MO) (Z_to_bv 64 3) = None ->
  m_halted MO = None -> m_vm_lazy MO = [] ->
  (forall m : mem,
    (forall a : word, 0x55040 <= bv_unsigned a < 0x553f0 -> m a = None) ->
    rw_cells rsegs m 0x54fd0 [C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C4 (Z_to_bv 64 0)] ->
    rw_cells rsegs m 0x54fd8 [C8 (Z_to_bv 64 (auxv_addr sp0 argv envp)); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 224); C8 (Z_to_bv 64 8); C8 (Z_to_bv 64 0);
                              C8 (Z_to_bv 64 4096); CB 48 (repeat (Z_to_bv 8 0) 48)] ->
    rw_cells rsegs m 0x23928 [C8 (Z_to_bv 64 0x54fb0)] ->
    rw_cells rsegs m 0x54fb0 [C8 rc_guard] ->   (* [comment removed for export] *)
    mem_inv rsegs m ->
    HKG (G_fs FS0) ps0 [] m MO /\ rw_cells rsegs m RAUXV_CELL [C8 (Z_to_bv 64 (auxv_addr sp0 argv envp))]) ->
  forall ms, rat_main sp0 argv envp uid hw rnd ms -> realizes_cfg acfg rsegs (mkCfg ms MO) (DRV MO FS0 argv).
Proof.
  intros sp0 argv envp uid hw rnd VSP RCSP RCS EFIT VARGV VENVP HKG FS0 DI YF MO MOFS MOFD MOFD3 MOh MOl HKI ms AM.
  destruct (Z.eq_dec (Z.of_nat (length argv)) 2) as [E2 | NE2].
  - destruct argv as [|a0 [|a1 [|a2 l]]]; try (exfalso; cbn in E2; lia).
    exact (rz_main2 sp0 [a0; a1] envp uid hw rnd VSP RCSP RCS EFIT VARGV VENVP HKG DI MO FS0 YF MOFS MOFD MOFD3 MOh MOl HKI a0 a1 eq_refl ms AM).
  - pose proof (rz_main_usage sp0 argv envp uid hw rnd VSP RCSP RCS EFIT VARGV VENVP HKG DI MO FS0 MOFS MOh MOl HKI ms AM NE2) as U.
    destruct argv as [|a0 [|a1 [|a2 l]]]; try exact U. exfalso. cbn in NE2. lia.
Qed.
End RC__9.
