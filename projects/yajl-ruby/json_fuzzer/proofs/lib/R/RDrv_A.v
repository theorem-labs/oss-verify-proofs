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
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Common Require Import ShapeAlgCfg.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes NodesCfg Decode Arr FP InitMem.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import Images.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Top Require Import ImplRz ImplRzCfg TrzNodesCfg TrzStdioCfg TrzLeafCfg.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Agent Require Import MallocBlocks.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.MS Require Import Malloc_iface.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Spec Require Import Prelim STree Malloc Monad StdioBase Stdio FmtFp Driver RawAlloc MSafe MLive.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.R Require Import RMallocRep RMallocTree RMalloc_iface R_StartupLib R_Startup R_Exit RF_pad RF_stdio_lib Stdio_iface RF_printf_iface Stdio_init.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.R Require Import RDrv_iface RDrv_ctx RDrv_kio.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Ltac rpc := apply ret_pc_even; [lia| reflexivity].

(* [comment removed for export] *)
Lemma u64ro_read : forall m A ws (i : Z) w a,
  bytes_at rsegs m A (u64s ws) -> nth_error ws (Z.to_nat i) = Some w -> (0 <= i)%Z -> a = wa (A + 8 * i) ->
  ov_read_bytes rsegs m a 8 = Some (le8 w).
Proof.
  intros m A ws i w a Hb Hn Hi ->.
  destruct (u64s_split _ _ _ Hn) as (pre & post & E & Hlen & Eu & Hlu).
  replace (8 * i)%Z with (Z.of_nat (8 * Z.to_nat i))%Z by lia.
  rewrite (bytes_at_ov_read rsegs m A (u64s ws) (8 * Z.to_nat i) 8 Hb).
  2:{ rewrite Eu, !app_length, length_le8, Hlu. lia. }
  rewrite Eu, skipn_app, skipn_all2, Hlu, Nat.sub_diag by lia. rewrite skipn_O, app_nil_l.
  rewrite firstn_app, firstn_all2 by (rewrite length_le8; lia).
  rewrite length_le8, Nat.sub_diag, firstn_O, app_nil_r. reflexivity.
Qed.

(* [comment removed for export] *)
Ltac rimg_chunk0 NONE m A cs H :=
  let bs := eval vm_compute in (cells_bytes cs) in
  assert (H : rw_cells rsegs m A cs);
  [ apply (InitMem.rw_cells_recast rsegs m A [CB (length bs) bs] cs);
    [ apply (InitMem.rw_cells_image0 rsegs m A bs);
      [ intros a Ha; cbn [length] in Ha; apply NONE; [lia| cbn [outside rcrt_written]; lia] | vm_compute; reflexivity | lia | cbn [length]; lia ]
    | cbn; repeat split; exact I | vm_compute; reflexivity | reflexivity ]
  | ].

(* [comment removed for export] *)

(* [comment removed for export] *)
Ltac rz_seg Hh Hl :=
  lazymatch goal with
  | |- realizes_cfg ?cf ?segs (mkCfg _ ?mo) ?K =>
      eapply (rz_evt (fun ms' => realizes_cfg cf segs (mkCfg ms' mo) K));
      [ | exact Hh | exact Hl | let X := fresh in intros ? X; exact X ]
  end.

Section A.
  Context {RC__ : OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.RunCeiling.RunCeiling}.
  Variables (sp0 : word) (argv envp : list (list byte)) (uid hw : word) (rnd : EntryDraw) (TID : Z).
  Hypothesis VSP : valid_sp sp0.
  Hypothesis RCSP : rc_sp = bv_unsigned sp0.          (* [comment removed for export] *)
  Hypothesis RCS : rc_secret = bv_unsigned (secret_of (at_random_bytes (ed_random rnd))).   (* [comment removed for export] *)
  Hypothesis EFIT : entry_stack_fits sp0 argv envp.   (* [comment removed for export] *)
  Hypothesis VARGV : valid_argv argv.
  Hypothesis VENVP : valid_envp envp.
  Hypothesis HT : 0 < TID < 4194304.
  Notation usp0 := (bv_unsigned sp0).
  Notation gpv := (Z_to_bv 64 0x10800).
  Notation tpv := (Z_to_bv 64 RATP).
  Notation IMGB := (build_stack_bytes rph sp0 argv envp uid hw rnd).
  Notation LO' := (LO sp0).

  (* [comment removed for export] *)
  Variable HK : HK_T.
  Hypothesis HKS : HK_run_stmt HK.
  Hypothesis HKF0 : HK_frame_stmt HK.
  Hypothesis HKSSP : HK_ssp_stmt HK.
  Hypothesis HKLH : HK_libc_head_stmt HK.

  (* [comment removed for export] *)
  (* [comment removed for export] *)

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma rz_exit_entry : forall (code : Z) (s st : PState) (LB : list block) (SP : Z) mo
      (ra t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (lo : Z),
    stk rsegs m lo SP -> lo <= SP - 176 -> 0x56000 <= lo -> 0 <= SP < 0x800000000000 ->
    RSTAT TID m -> HK s LB m mo -> stdout_file m (ps_so st) -> stderr_file m -> mem_inv rsegs m ->
    zlength (so_buf (ps_so st)) <= STDOUT_BUFSIZ ->
    realizes_cfg acfg rsegs (mkCfg (MS (mkR ra (Z_to_bv 64 SP) gpv tpv t0 t1 t2 s0 s1 (Z_to_bv 64 code) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                               F (Z_to_bv 64 0x175cc) fc None m (seg_rom rsegs)) mo)
             (ShapeAlg.t_emit (Wz 1 (fst (exit_flush_pure (ps_so st))))
                              (t_exit (bv_and (Z_to_bv 64 code) (Z_to_bv 64 255)) (m_fs mo))).
  Proof.
    intros until lo. intros ST LOS LOLO SPR ((TD & (reg & p3 & p4 & FJ & AJ & ATC & _ & FLG & DSO)) & EXL & GF & FA & FIN & GCX & OFL & SIN & SOU & SEU & _ & _) HKx SOF SEF MI Hb.
    destruct (HKLH _ _ _ _ HKx) as (cdt & thr & sec & tm1 & LC).
    destruct (HKSSP _ _ _ _ HKx) as [G1 G2]. unfold RGOT_SSP, RSSP_GUARD in G1, G2.
    destruct (HKS _ _ _ _ HKx) as (Hmi & Hh & _).
    eapply (rz_exit st); try first [exact TD | exact EXL | exact GF | exact FA | exact FIN | exact GCX | exact DSO | exact ATC | exact FLG | exact LC | exact OFL | exact SIN
                                  | exact SOU | exact SEU | exact SOF | exact SEF | exact G1 | exact G2 | exact MI | exact Hmi | exact Hh | exact Hb | exact HT];
      rewrite ?unsigned_lit by lia; [exact ST | reflexivity | reflexivity | lia | lia | lia].
  Qed.

  (* [comment removed for export] *)
  Lemma rz_main_return : forall (code : Z) (s st : PState) (LB : list block) mo
      (x1 t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (pad : list byte) (s7v s6v s5v s4v : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
    MFRAME sp0 argv m pad s7v s6v s5v s4v ->
    stk rsegs m LO' (usp0 + -128) ->
    RSTAT TID m -> HK s LB m mo -> stdout_file m (ps_so st) -> stderr_file m -> mem_inv rsegs m ->
    zlength (so_buf (ps_so st)) <= STDOUT_BUFSIZ ->
    realizes_cfg acfg rsegs (mkCfg (MS (mkR x1 (Z_to_bv 64 (usp0 + -128)) gpv tpv t0 t1 t2 (Z_to_bv 64 code) s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                               F (Z_to_bv 64 0x136d0) fc None m (seg_rom rsegs)) mo)
             (ShapeAlg.t_emit (Wz 1 (fst (exit_flush_pure (ps_so st))))
                              (t_exit (bv_and (Z_to_bv 64 code) (Z_to_bv 64 255)) (m_fs mo))).
  Proof.
    intros until m. intros FR ST RS HKx SOF SEF MI Hb. pose proof (sp_facts sp0 VSP RCSP) as SF. unfold LO in *. unfold MFRAME in FR.
    destruct (HKS _ _ _ _ HKx) as (Hmi & Hh & Hl).
    rz_seg Hh Hl.
    do 11 zstep. release_frame FR ST (usp0 + -48). zstep.
    replace (ret_pc (Z_to_bv 64 0x17048)) with (Z_to_bv 64 0x17048) by (symmetry; rpc).
    zstep.
    apply evt_done. eapply rz_exit_entry; [exact ST| lia| lia| lia| exact RS| exact HKx| exact SOF| exact SEF| exact MI| exact Hb].
  Qed.

  (* [comment removed for export] *)
  Lemma rz_exit2 : forall (s st : PState) (LB : list block) mo
      (x1 t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem),
    stk rsegs m LO' (usp0 + -128) ->
    RSTAT TID m -> HK s LB m mo -> stdout_file m (ps_so st) -> stderr_file m -> mem_inv rsegs m ->
    zlength (so_buf (ps_so st)) <= STDOUT_BUFSIZ ->
    realizes_cfg acfg rsegs (mkCfg (MS (mkR x1 (Z_to_bv 64 (usp0 + -128)) gpv tpv t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                               F (Z_to_bv 64 0x1375c) fc None m (seg_rom rsegs)) mo)
             (ShapeAlg.t_emit (Wz 1 (fst (exit_flush_pure (ps_so st))))
                              (t_exit (bv_and (Z_to_bv 64 2) (Z_to_bv 64 255)) (m_fs mo))).
  Proof.
    intros until m. intros ST RS HKx SOF SEF MI Hb. pose proof (sp_facts sp0 VSP RCSP) as SF. unfold LO in *.
    destruct (HKS _ _ _ _ HKx) as (Hmi & Hh & Hl).
    rz_seg Hh Hl.
    zstep. zstep.
    apply evt_done. eapply rz_exit_entry; [exact ST| lia| lia| lia| exact RS| exact HKx| exact SOF| exact SEF| exact MI| exact Hb].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma main_prologue : forall (Q : machine_state -> Prop) (ra s0 s1 a0 a1 a2 s2 s3 t0 t1 t2 a3 a4 a5 a6 a7 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem),
    stk rsegs m LO' (usp0 + -48) -> mem_inv rsegs m ->
    (forall m' (pad : list byte), rw_cells rsegs m' (usp0 + -128) [CB 8 pad; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
        stk rsegs m' LO' (usp0 + -128) ->
        munch [(usp0 - 128, usp0 - 48)] m m' -> wmono rsegs m m' -> mem_inv rsegs m' ->
        evt rsegs Q (MS (mkR ra (Z_to_bv 64 (usp0 + -128)) gpv tpv t0 t1 t2 (Z_to_bv 64 2) s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                        F (Z_to_bv 64 0x13500) fc None m' (seg_rom rsegs))) ->
    evt rsegs Q (MS (mkR ra (Z_to_bv 64 (usp0 + -48)) gpv tpv t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                    F (Z_to_bv 64 0x134d4) fc None m (seg_rom rsegs)).
  Proof.
    intros until m. intros ST MI K. pose proof (sp_facts sp0 VSP RCSP) as SF. unfold LO in *.
    pose proof (munch_refl [(usp0 - 128, usp0 - 48)] m) as MU. pose proof (wmono_refl rsegs m) as WM.
    zstep. carve_frame 80%nat ST.
    do 10 zstep.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => eapply (K mx) end; [exact FR| exact ST| exact MU| exact WM| assumption].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Section InitFacts.
    Variable m : mem.
    Hypothesis AUXC : rw_cells rsegs m RAUXV_CELL [C8 (Z_to_bv 64 (auxv_addr sp0 argv envp))].
    Hypothesis MI : mem_inv rsegs m.
    Hypothesis IMG : bytes_at rsegs m usp0 IMGB.

    (* [comment removed for export] *)
    Lemma rauxv_ok_init : rauxv_ok m usp0.
    Proof.
      destruct (stack_pieces sp0 argv envp uid hw rnd m IMG) as (_ & _ & _ & AUXW & _ & _ & RND).
      pose proof (build_stack_bytes_length rph sp0 argv envp uid hw rnd) as BL. pose proof (raw_len_nonneg rph sp0 argv envp uid hw rnd) as RLN.
      pose proof (bytes_at_bound _ _ _ _ IMG) as IB. pose proof (sp_facts sp0 VSP RCSP) as SF. unfold LO in SF.
      pose proof (bv_unsigned_in_range 64 uid) as RU. unfold bv_modulus in RU. cbn in RU.
      pose proof (bv_unsigned_in_range 64 hw) as RH. unfold bv_modulus in RH. cbn in RH.
      exists (auxv_addr sp0 argv envp), (Z.of_N (ph_addr rph)), (Z.of_N (ph_ent rph)), (Z.of_N (ph_num rph)), (bv_unsigned hw), 4096,
             (bv_unsigned uid), (bv_unsigned uid), 0, (rnd_addr sp0 argv envp).
      split; [exact AUXC|].
      split. { unfold auxv_addr. replace (auxv_list _ _ _ _ _ _ _ _ _) with (auxv_words rph sp0 argv envp uid hw). { exact AUXW. }
               unfold auxv_list, auxv_words, wz. cbn [map]. rewrite !Z_to_bv_bv_unsigned. reflexivity. }
      split. { rewrite at_random_bytes_split in RND. apply bytes_at_app in RND. destruct RND as [_ R].
               rewrite length_firstn, length_at_random_bytes in R. cbn [Nat.min Z.of_nat Pos.of_succ_nat Pos.succ] in R.
               replace (le8 (wz rc_secret)) with (secret_bytes (at_random_bytes (ed_random rnd))). { exact R. }
               rewrite RCS. unfold wz. rewrite Z_to_bv_bv_unsigned. symmetry. apply le8_secret_of. rewrite length_at_random_bytes. lia. }
      unfold auxv_addr, rnd_addr, raw_len, struct_size, argc, envc, alloc_ceiling, sp_window_lo, stack_max_size in *.
      pose proof (flatten_strings_length argv). pose proof (flatten_strings_length envp).
      repeat split; lia.
    Qed.
  End InitFacts.

End A.

Section A2.
  Context {RC__ : OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.RunCeiling.RunCeiling}.
  Variables (sp0 : word) (argv envp : list (list byte)) (uid hw : word) (rnd : EntryDraw).
  Hypothesis VSP : valid_sp sp0.
  Hypothesis RCSP : rc_sp = bv_unsigned sp0.          (* [comment removed for export] *)
  Hypothesis RCS : rc_secret = bv_unsigned (secret_of (at_random_bytes (ed_random rnd))).   (* [comment removed for export] *)
  Hypothesis EFIT : entry_stack_fits sp0 argv envp.   (* [comment removed for export] *)
  Hypothesis VARGV : valid_argv argv.
  Hypothesis VENVP : valid_envp envp.
  Notation usp0 := (bv_unsigned sp0).
  Notation gpv := (Z_to_bv 64 0x10800).
  Notation tpv := (Z_to_bv 64 RATP).
  Notation IMGB := (build_stack_bytes rph sp0 argv envp uid hw rnd).
  Notation LO' := (LO sp0).
  Variable HK : HK_T.
  Hypothesis HKS : HK_run_stmt HK.
  Hypothesis HKF0 : HK_frame_stmt HK.
  Hypothesis HKSSP : HK_ssp_stmt HK.
  Hypothesis HKLH : HK_libc_head_stmt HK.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Variable MO : Model.
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

  (* [comment removed for export] *)
  Definition P1 (TID : Z) (ms : machine_state) : Prop :=
    exists (t0 t1 t2 a3 a4 a5 a6 a7 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (fc : bv 32) (mm : mem) (pad junk : list byte),
      ms = MS (mkR (Z_to_bv 64 0x17048) (Z_to_bv 64 (usp0 + -128)) gpv tpv t0 t1 t2
                   (Z_to_bv 64 2) (Z_to_bv 64 2) (Z_to_bv 64 2) (Z_to_bv 64 (usp0 + 8)) (Z_to_bv 64 (envp_addr sp0 argv)) a3 a4 a5 a6 a7
                   (Z_to_bv 64 0x134d4) (Z_to_bv 64 (envp_addr sp0 argv)) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
              bvmap_empty (Z_to_bv 64 0x13504) fc None mm (seg_rom rsegs)
      /\ MFRAME sp0 argv mm pad s7 s6 s5 s4 /\ BASE sp0 argv envp uid hw rnd TID mm /\ HK ps0 [] mm MO
      /\ rw_cells rsegs mm RERRNO [C4 (Z_to_bv 64 0)] /\ RSTG mm junk /\ frm0 fc.

  (* [comment removed for export] *)
  Lemma main_to_test : forall (ms : machine_state) (Q : machine_state -> Prop),
    rat_main sp0 argv envp uid hw rnd ms ->
    (forall (t : Z) (t0 t1 t2 a3 a4 a5 a6 a7 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (mm : mem) (pad : list byte),
        0 < t < 4194304 ->
        MFRAME sp0 argv mm pad s7 s6 s5 s4 -> BASE sp0 argv envp uid hw rnd t mm -> HK ps0 [] mm MO ->
        rw_cells rsegs mm RERRNO [C4 (Z_to_bv 64 0)] -> RSTG mm (repeat (Z_to_bv 8 0) (Z.to_nat STAGE)) ->
        evt rsegs Q (MS (mkR (Z_to_bv 64 0x17048) (Z_to_bv 64 (usp0 + -128)) gpv tpv t0 t1 t2
                          (Z_to_bv 64 2) (Z_to_bv 64 (argc argv)) (Z_to_bv 64 (argc argv)) (Z_to_bv 64 (usp0 + 8)) (Z_to_bv 64 (envp_addr sp0 argv)) a3 a4 a5 a6 a7
                          (Z_to_bv 64 0x134d4) (Z_to_bv 64 (envp_addr sp0 argv)) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                        bvmap_empty (Z_to_bv 64 0x13500) (Z_to_bv 32 0) None mm (seg_rom rsegs))) ->
    evt rsegs Q ms.
  Proof.
    intros ms Q AM K.
    destruct AM as (t0 & t1 & t2 & a3 & a4 & a5 & a6 & a7 & s4 & s5 & s6 & s7 & s8 & s9 & s10 & s11 & t3 & t4 & t5 & t6 & t & P0 & pg & m
                    & -> & MI & ST & TD & ERR & TLS & LIBC1 & LIBC2 & MTLS & SYSI & PROG & HWCAP & ENV & DSS & GUARD & GOT0 & GOTM & GCX & G78 & G88 & GA0 & GOTG & GF & IA & FA & GD0 & INI & FIN & EXL & SOU & SEU & SIN & OFL & SOF & SEF & IMG & IMGW & HP0 & NONE & Ht).
    pose proof (sp_facts sp0 VSP RCSP) as SF. pose proof (IMGB_len sp0 argv envp uid hw rnd VSP VARGV VENVP) as IL. pose proof (IMGB_ts sp0 argv envp uid hw rnd EFIT) as ITS. unfold LO in *.
    pose proof (bytes_at_bound _ _ _ _ IMG) as IMGBD.
    destruct (HKI m) as [HK0 AUXC]; [intros a Ha; apply NONE; [lia| cbn; lia] | exact LIBC1 | exact LIBC2 | exact GOTG | exact GUARD | exact MI |].
    pose proof (rauxv_ok_init sp0 argv envp uid hw rnd VSP RCSP RCS m AUXC IMG) as AI.
    pose proof (stderr_wfile0_init m NONE) as SE.
    rimg_chunk0 NONE m 0x24968 [C8 (Z_to_bv 64 0x139f0); C8 (Z_to_bv 64 0x139f8); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0);
                          C8 (Z_to_bv 64 0x13a00); C8 (Z_to_bv 64 0x13a34); C8 (Z_to_bv 64 0x13a3c); C8 (Z_to_bv 64 0x13a54);
                          C8 (Z_to_bv 64 0x13a8c); C8 (Z_to_bv 64 0x13ad0); C8 (Z_to_bv 64 0x13ae8)] Y1.
    rimg_chunk0 NONE m 0x249c0 [C8 (Z_to_bv 64 0x15374); C8 (Z_to_bv 64 0x153a0); C8 (Z_to_bv 64 0x153cc); C8 (Z_to_bv 64 0)] Y2.
    rimg_chunk0 NONE m 0x249e0 [C4 (Z_to_bv 64 1); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0x249c0)] Y3.
    rimg_chunk0 NONE m 0x34c40 [C1 (Z_to_bv 8 0)] T1.
    rimg_chunk0 NONE m 0x238f0 [C8 (Z_to_bv 64 0)] T2.
    assert (YS0 : YST m) by (split; [exact Y1| split; [exact Y2| exact Y3]]).
    assert (TR00 : TR0 m) by (split; [exact T1| exact T2]).
    (* [comment removed for export] *)
    rimg_chunk0 NONE m 0x54d88 [C1 (Z_to_bv 8 0); CB 3 (repeat (Z_to_bv 8 0) 3); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); CB 4 (repeat (Z_to_bv 8 0) 4);
                          C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); CB 248 (repeat (Z_to_bv 8 0) 248);
                          C8 (Z_to_bv 64 0); CB 248 (repeat (Z_to_bv 8 0) 248)] AT1.
    rimg_chunk0 NONE m 0x34c44 [C1 (Z_to_bv 8 0)] AT2.
    rimg_chunk0 NONE m 0x24940 [C8 (Z_to_bv 64 0x24940)] AT3.
    assert (ATX0 : ATX m).
    { exists false, (repeat (Z_to_bv 8 0) 3), (repeat (Z_to_bv 8 0) 4), (repeat (Z_to_bv 8 0) 248), (repeat (Z_to_bv 8 0) 248).
      split; [exact AT1|]. split; [exact T1|]. split; [exact AT2| exact AT3]. }
    clear AT1 AT2 AT3.
    assert (RSG : RSTG m (repeat (Z_to_bv 8 0) (Z.to_nat STAGE))).
    { apply RSTG_image0. intros a Ha. pose proof STAGE_val. unfold RSTAGE in Ha. apply NONE; [lia| cbn [outside rcrt_written]; lia]. }
    clear TLS MTLS SYSI PROG HWCAP ENV DSS GOT0 GOTM IA INI IMGW HP0 Y1 Y2 Y3 T1 T2.
    replace (usp0 - 8388608) with (usp0 + -8388608) in ST by lia.
    eapply (main_prologue sp0 VSP RCSP); [unfold LO; replace (usp0 - 8388608) with (usp0 + -8388608) by lia; exact ST| exact MI|].
    intros m1 pad FR ST1 MU WM MI1. unfold LO in ST1.
    pose proof (agree_on_of_munch _ _ _ MU WM) as AG.
    assert (OUT : forall a, (a < usp0 - 128 \/ usp0 - 48 <= a) -> (fun a0 : Z => outside [(usp0 - 128, usp0 - 48)] a0) a) by (intros a Ha; cbn; lia).
    apply (K t t0 t1 t2 a3 a4 a5 a6 a7 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 m1 pad Ht).
    - exact FR.
    - split; [unfold LO; replace (usp0 - 8388608) with (usp0 + -8388608) by lia; exact ST1|]. split; [exact MI1|].
      split. { eapply (RSTAT_agree t _ _ _ AG); [intros a Ha; apply OUT; unfold rstat_addr in Ha; lia|].
               unfold RSTAT. split; [split; [exact TD| exact ATX0]|]. split; [exact EXL|]. split; [exact GF|]. split; [exact FA|]. split; [exact FIN|]. split; [exact GCX|].
               split; [exact OFL|]. split; [exact SIN|]. split; [exact SOU|]. split; [exact SEU|]. split; [exact G78| exact GD0]. }
      split. { eapply rauxv_ok_frame; [exact AI| exact MU| exact WM|]. constructor; [| constructor]. unfold RAUXV_CELL. cbn [fst snd]. lia. }
      split. { eapply bytes_at_agree; [exact AG| exact IMG| intros a Ha; apply OUT; lia]. }
      split. { eapply (stderr_wfile0_agree _ _ _ AG); [intros a Ha; apply OUT; unfold stderr_addr in Ha; lia| exact SE]. }
      split. { eapply (stdout_file_agree _ _ _ _ AG); [intros a Ha; apply OUT; unfold stdout_addr in Ha; lia| exact SOF]. }
      split. { eapply (YST_agree _ _ _ AG); [intros a Ha; apply OUT; unfold ytr_addr in Ha; lia| exact YS0]. }
      eapply (TR0_agree _ _ _ AG); [intros a Ha; apply OUT; unfold ytr_addr in Ha; lia| exact TR00].
    - eapply HKF0; [exact HK0| exact MU| exact WM|]. constructor; [| constructor]. left. cbn [fst snd]. unfold alloc_ceiling in *. lia.
    - eapply rw_cells_agree; [exact AG| unfold RERRNO; exact ERR| intros a Ha; apply OUT; cbn in Ha; unfold RERRNO in Ha; lia].
    - unfold RSTG in *. eapply rw_cells_agree; [exact AG| exact RSG| intros a Ha; apply OUT; pose proof STAGE_val; cbn [cells_size csize Nat.add] in Ha; unfold RSTAGE in Ha; lia].
  Qed.

  Hypothesis MOh : m_halted MO = None.
  Hypothesis MOl : m_vm_lazy MO = [].

  (* [comment removed for export] *)
  Lemma main_usage : forall ms, rat_main sp0 argv envp uid hw rnd ms -> Z.of_nat (length argv) <> 2 ->
    realizes_cfg acfg rsegs (mkCfg ms MO)
      (ShapeAlg.t_emit (Wz 2 (concat (pieces_usage (map bv_unsigned (hd [] argv)))))
         (ShapeAlg.t_emit (Wz 1 []) (t_exit (bv_and (Z_to_bv 64 2) (Z_to_bv 64 255)) (m_fs MO)))).
  Proof.
    intros ms AM HARGC.
    rz_seg MOh MOl.
    eapply main_to_test; [exact AM|]. intros t t0 t1 t2 a3 a4 a5 a6 a7 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 mm pad Ht FR BA HK0 ERR _.
    pose proof (sp_facts sp0 VSP RCSP) as SF. pose proof (IMGB_len sp0 argv envp uid hw rnd VSP VARGV VENVP) as IL. pose proof (IMGB_ts sp0 argv envp uid hw rnd EFIT) as ITS. unfold LO in *.
    pose proof BA as (ST & MI & RS & AUX & IMG & SE & SO & YSx & TRx). unfold LO in ST.
    pose proof RS as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & G78 & GD0).
    destruct (HKS _ _ _ _ HK0) as (Hmi & Hh & Hl).
    destruct (HKSSP _ _ _ _ HK0) as [SSP1 SSP2]. unfold RGOT_SSP, RSSP_GUARD in SSP1, SSP2.
    destruct VARGV as (ARGC & _ & ARGLEN & NONUL & _).
    destruct argv as [|arg0 argv'] eqn:EARGV; [cbn in ARGC; lia|]. rewrite <- EARGV in *.
    (* [comment removed for export] *)
    destruct (argv_cstring sp0 argv envp uid hw rnd mm IMG 0 arg0 ltac:(rewrite EARGV; reflexivity) ltac:(clear -SF; Z.div_mod_to_equations; lia))
      as (p0 & slack0 & HP0 & P0LO & P0HI & STR0 & SLK0). unfold str_base, struct_size, argc, envc in P0LO.
    destruct (stack_pieces sp0 argv envp uid hw rnd mm IMG) as (_ & ARGVP & _).
    assert (A0NN : ~ In (Z_to_bv 8 0) arg0) by (rewrite EARGV in NONUL; inversion NONUL; assumption).
    assert (A0LEN : Z.of_nat (length arg0) <= 131071) by (rewrite EARGV in ARGLEN; inversion ARGLEN; assumption).
    unfold argc. zstep. if_cases K0; zify_cond K0; try (exfalso; lia). clear K0.
    (* [comment removed for export] *)
    zstep. zstep. zstep.
    pose proof (u64ro_read mm (usp0 + 8) (argv_ptrs sp0 argv envp ++ [Z_to_bv 64 0]) 0 (Z_to_bv 64 p0) (Z_to_bv 64 (usp0 + 8))
                  ARGVP ltac:(rewrite nth_error_app1 by (rewrite argv_ptrs_length, EARGV; cbn; lia); exact HP0) ltac:(lia) ltac:(unfold wa; f_equal; lia)) as RD.
    zstep. clear RD. zstep. zstep. zstep.
    (* [comment removed for export] *)
    apply evt_done.
    rewrite EARGV. cbn [hd].
    eapply (rz_fprintf_diag (DUsage (map bv_unsigned arg0))) with (lo := usp0 - 8388608) (canary := rc_guard) (st := ps0);
      [ apply ShapeAlg.t_emit_has_nil | exact Hmi | exact Hh
      | apply stderr_wfile0_wfile; exact SE | reflexivity | | rewrite unsigned_lit by lia; exact ST
      | rewrite unsigned_lit by lia; unfold FPRINTF_DEPTH; lia | unfold GLOBALS_TOP; lia | rewrite unsigned_lit by lia; lia
      | split; [exact SSP1 | exact SSP2] | exact MI | vm_compute; reflexivity | | ].
    { cbn [diag_args]. split; [reflexivity|]. exists slack0.
      rewrite unsigned_lit by lia.
      unfold zb. rewrite zbytes_map_unsigned'. unfold zlength. rewrite !length_map.
      split; [exact STR0|]. split; [apply map_unsigned_pos; exact A0NN|]. split; [lia|].
      split; [unfold FmtFp.INT_MAX; lia|]. split; [right; rewrite unsigned_lit by lia; lia| unfold GLOBALS_TOP; lia]. }
    { cbn [diag_pieces pieces_usage]. unfold INTERNAL_BUFSIZ, WRITEV_MAX, zlength.
      repeat constructor; rewrite ?length_map, ?length_app; cbn [length str list_ascii_of_string map app]; lia. }
    intros u0 u1 u2 b0 b1 b2 b3 b4 b5 b6 b7 u3 u4 u5 u6 Ft fc' m2 MUc WMc MI2 FRM2 FEQ ST2 SEW SSP'.
    rewrite !unsigned_lit in MUc by lia.
    replace (ret_pc (Z_to_bv 64 0x13688)) with (Z_to_bv 64 0x13688) by (symmetry; rpc).
    pose proof (agree_on_of_munch _ _ _ MUc WMc) as AG.
    assert (OUT : forall a, (usp0 - 128 <= a /\ ~ (0x24a00 <= a < 0x24a00 + 232)) -> (fun a0 : Z => outside [(usp0 - 8388608, usp0 + -128); (0x24a00, 0x24a00 + 232)] a0) a).
    { intros a Ha. cbn. lia. }
    assert (OUT2 : forall a, (0x10000 <= a < 0x56000 /\ ~ (0x24a00 <= a < 0x24a00 + 232)) -> (fun a0 : Z => outside [(usp0 - 8388608, usp0 + -128); (0x24a00, 0x24a00 + 232)] a0) a).
    { intros a Ha. cbn. lia. }
    unfold MFRAME in FR.
    apply (rw_cells_agree _ _ _ _ _ AG) in FR; [| intros a Ha; apply OUT; cbn in Ha; lia].
    assert (HK2 : HK ps0 [] m2 MO).
    { eapply HKF0; [exact HK0| exact MUc| exact WMc|].
      constructor; [left; cbn [fst snd]; unfold alloc_ceiling in *; lia|]. constructor; [| constructor].
      right; left. cbn [fst snd]. unfold RLIBC, RCTX, RSSP_GUARD, RGOT_SSP. lia. }
    rz_seg Hh Hl.
    zstep. apply evt_done.
    eapply (rz_main_return sp0 argv t VSP RCSP Ht HK HKS HKSSP HKLH 2 ps0 ps0 []).
    - exact FR.
    - unfold LO. rewrite ?unsigned_lit in ST2 by lia. exact ST2.
    - eapply (RSTAT_agree t _ _ _ AG); [intros a Ha; apply OUT2; unfold rstat_addr in Ha; lia| exact RS].
    - exact HK2.
    - cbn [ps_so ps0 ps_init]. eapply (stdout_file_agree _ _ _ _ AG); [intros a Ha; apply OUT2; unfold stdout_addr in Ha; lia| exact SO].
    - apply stderr_wfile_file. exact SEW.
    - exact MI2.
    - unfold ps0. cbn [ps_so ps_init so_buf stdout_init]. unfold zlength, STDOUT_BUFSIZ. cbn [length]. lia.
  Qed.
End A2.
