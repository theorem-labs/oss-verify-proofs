(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from U/UDrv_A.v (the UBSan build's walk, as BudgetWit/UsageB.v is made from the plain build's R/RDrv_A.v): rz_exit_entry, rz_main_return and main_usage (the driver's argc <> 2 path) restated over BudgetWit.RzbCfg.rzb_cfg, with the released proof text. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (the launchT context, argv pointers from ed_top and the exec name, and the 6,144,513-byte stack window). *)
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
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.U Require Import UMallocRep UMallocTree UMalloc_iface U_StartupLib U_Startup U_Exit UF_pad.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.R Require Import RF_stdio_lib.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.U Require Import UStdio_iface UF_printf_iface UStdio_init.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.U Require Import UDrv_iface UDrv_ctx UDrv_kio UDrv_A.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.BudgetWit Require Import RzbCfg.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.BudgetWit.U Require Import KioB.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(** * [main]'s argc <> 2 path, over [rzb_cfg]

    [UDrv_A.main_usage] is the walk of the driver's [main] from its entry to the
    exit when argc is not 2: [main] tests argc, loads argv[0], calls
    [fprintf(stderr, "usage: %s INPUT\n", argv[0])] and returns 2 to musl's
    [exit].  This file restates it, and the two lemmas it calls that end in a
    trace set ([rz_main_return], [rz_exit_entry]), over [rzb_cfg], with the
    released proof text: [rz_evt] is [KioB.rzb_evt], [rz_fprintf_diag] is
    [KioB.rzb_fprintf_diag], [rz_exit] is [KioB.rzb_exit].  The machine-level
    parts ([UDrv_A.main_to_test], the [evt] steps) are the released lemmas,
    used as they are. *)

Ltac rzb_seg Hh Hl :=
  lazymatch goal with
  | |- rzb_cfg ?cf ?segs (mkCfg _ ?mo) ?K =>
      eapply (rzb_evt (fun ms' => rzb_cfg cf segs (mkCfg ms' mo) K));
      [ | exact Hh | exact Hl | let X := fresh in intros ? X; exact X ]
  end.

Section A.
  Context {RC__ : OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.RunCeiling.RunCeiling}.
  Context {LT : launchT}.
  Variables (sp0 : word) (argv envp : list (list byte)) (uid hw : word) (rnd : EntryDraw) (TID : Z).
  Hypothesis VSP : valid_sp sp0.
  Hypothesis RCSP : rc_sp = bv_unsigned sp0.
  Hypothesis RCS : rc_secret = bv_unsigned (secret_of (at_random_bytes (ed_random rnd))).
  Hypothesis EFIT : entry_stack_fits sp0 argv envp.
  Hypothesis VARGV : valid_argv argv.
  Hypothesis VENVP : valid_envp envp.
  Hypothesis HT : 0 < TID < 4194304.
  Notation usp0 := (bv_unsigned sp0).
  Notation gpv := (Z_to_bv 64 0x10800).
  Notation tpv := (Z_to_bv 64 RATP).
  Notation LO' := (LO sp0).

  Variable HK : HK_T.
  Hypothesis HKS : HK_run_stmt HK.
  Hypothesis HKF0 : HK_frame_stmt HK.
  Hypothesis HKSSP : HK_ssp_stmt HK.
  Hypothesis HKLH : HK_libc_head_stmt HK.

  (** [UDrv_A.rz_exit_entry] over [rzb_cfg]. *)
  Lemma rzb_exit_entry : forall (code : Z) (s st : PState) (LB : list block) (SP : Z) mo
      (ra t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (lo : Z),
    stk usegs m lo SP -> lo <= SP - 176 -> 0x57000 <= lo -> 0 <= SP < 0x800000000000 ->
    RSTAT TID m -> HK s LB m mo -> stdout_file m (ps_so st) -> stderr_file m -> mem_inv usegs m ->
    zlength (so_buf (ps_so st)) <= STDOUT_BUFSIZ ->
    rzb_cfg acfg usegs (mkCfg (MS (mkR ra (Z_to_bv 64 SP) gpv tpv t0 t1 t2 s0 s1 (Z_to_bv 64 code) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                               F (Z_to_bv 64 0x17f34) fc None m (seg_rom usegs)) mo)
             (ShapeAlg.t_emit (Wz 1 (fst (exit_flush_pure (ps_so st))))
                              (t_exit (bv_and (Z_to_bv 64 code) (Z_to_bv 64 255)) (m_fs mo))).
  Proof.
    intros until lo. intros ST LOS LOLO SPR ((TD & (reg & p3 & p4 & FJ & AJ & ATC & _ & FLG & DSO)) & EXL & GF & FA & FIN & GCX & OFL & SIN & SOU & SEU & _ & _) HKx SOF SEF MI Hb.
    destruct (HKLH _ _ _ _ HKx) as (cdt & thr & sec & tm1 & LC).
    destruct (HKSSP _ _ _ _ HKx) as [G1 G2]. unfold RGOT_SSP, RSSP_GUARD in G1, G2.
    destruct (HKS _ _ _ _ HKx) as (Hmi & Hh & _).
    eapply (rzb_exit st); try first [exact TD | exact EXL | exact GF | exact FA | exact FIN | exact GCX | exact DSO | exact ATC | exact FLG | exact LC | exact OFL | exact SIN
                                  | exact SOU | exact SEU | exact SOF | exact SEF | exact G1 | exact G2 | exact MI | exact Hmi | exact Hh | exact Hb | exact HT];
      rewrite ?unsigned_lit by lia; [exact ST | reflexivity | reflexivity | lia | lia | lia].
  Qed.

  (** [UDrv_A.rz_main_return] over [rzb_cfg]. *)
  Lemma rzb_main_return : forall (code : Z) (s st : PState) (LB : list block) mo
      (x1 t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (pad : list byte) (s7v s6v s5v s4v : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
    MFRAME sp0 argv m pad s7v s6v s5v s4v ->
    stk usegs m LO' (usp0 + -128) ->
    RSTAT TID m -> HK s LB m mo -> stdout_file m (ps_so st) -> stderr_file m -> mem_inv usegs m ->
    zlength (so_buf (ps_so st)) <= STDOUT_BUFSIZ ->
    rzb_cfg acfg usegs (mkCfg (MS (mkR x1 (Z_to_bv 64 (usp0 + -128)) gpv tpv t0 t1 t2 (Z_to_bv 64 code) s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                               F (Z_to_bv 64 0x136fc) fc None m (seg_rom usegs)) mo)
             (ShapeAlg.t_emit (Wz 1 (fst (exit_flush_pure (ps_so st))))
                              (t_exit (bv_and (Z_to_bv 64 code) (Z_to_bv 64 255)) (m_fs mo))).
  Proof.
    intros until m. intros FR ST RS HKx SOF SEF MI Hb. pose proof (sp_facts sp0 VSP RCSP) as SF. unfold LO in *. unfold MFRAME in FR.
    destruct (HKS _ _ _ _ HKx) as (Hmi & Hh & Hl).
    rzb_seg Hh Hl.
    do 11 zstep. release_frame FR ST (usp0 + -48). zstep.
    replace (ret_pc (Z_to_bv 64 0x179b0)) with (Z_to_bv 64 0x179b0) by (symmetry; rpc).
    zstep.
    apply evt_done. eapply rzb_exit_entry; [exact ST| lia| lia| lia| exact RS| exact HKx| exact SOF| exact SEF| exact MI| exact Hb].
  Qed.
End A.

Section A2.
  Context {RC__ : OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.RunCeiling.RunCeiling}.
  Context {LT : launchT}.
  Variables (sp0 : word) (argv envp : list (list byte)) (uid hw : word) (rnd : EntryDraw).
  Hypothesis VSP : valid_sp sp0.
  Hypothesis RCSP : rc_sp = bv_unsigned sp0.
  Hypothesis RCS : rc_secret = bv_unsigned (secret_of (at_random_bytes (ed_random rnd))).
  Hypothesis EFIT : entry_stack_fits sp0 argv envp.
  Hypothesis VARGV : valid_argv argv.
  Hypothesis VENVP : valid_envp envp.
  Notation usp0 := (bv_unsigned sp0).
  Notation gpv := (Z_to_bv 64 0x10800).
  Notation tpv := (Z_to_bv 64 RATP).
  Notation LO' := (LO sp0).
  Variable HK : HK_T.
  Hypothesis HKS : HK_run_stmt HK.
  Hypothesis HKF0 : HK_frame_stmt HK.
  Hypothesis HKSSP : HK_ssp_stmt HK.
  Hypothesis HKLH : HK_libc_head_stmt HK.

  Variable MO : Model.
  Hypothesis HKI : forall m : mem,
    (forall a : word, 0x559a0 <= bv_unsigned a < 0x55d50 -> m a = None) ->
    rw_cells usegs m 0x55930 [C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C4 (Z_to_bv 64 0)] ->
    rw_cells usegs m 0x55938 [C8 (Z_to_bv 64 (auxv_addr sp0 argv envp)); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 224); C8 (Z_to_bv 64 8); C8 (Z_to_bv 64 0);
                              C8 (Z_to_bv 64 4096); CB 48 (repeat (Z_to_bv 8 0) 48)] ->
    rw_cells usegs m 0x24290 [C8 (Z_to_bv 64 0x55910)] ->
    rw_cells usegs m 0x55910 [C8 rc_guard] ->
    mem_inv usegs m ->
    HK ps0 [] m MO /\ rw_cells usegs m RAUXV_CELL [C8 (Z_to_bv 64 (auxv_addr sp0 argv envp))].

  Hypothesis MOh : m_halted MO = None.
  Hypothesis MOl : m_vm_lazy MO = [].

  (** [UDrv_A.main_usage] over [rzb_cfg]: from [main]'s entry with argc <> 2,
      the usage line on fd 2, an empty flush of stdout, and exit status 2. *)
  Lemma main_usage_b : forall ms, rat_main sp0 argv envp uid hw rnd ms -> Z.of_nat (length argv) <> 2 ->
    rzb_cfg acfg usegs (mkCfg ms MO)
      (ShapeAlg.t_emit (Wz 2 (concat (pieces_usage (map bv_unsigned (hd [] argv)))))
         (ShapeAlg.t_emit (Wz 1 []) (t_exit (bv_and (Z_to_bv 64 2) (Z_to_bv 64 255)) (m_fs MO)))).
  Proof using All.
    intros ms AM HARGC.
    rzb_seg MOh MOl.
    eapply main_to_test.
    all: try eassumption.
    intros t t0 t1 t2 a3 a4 a5 a6 a7 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 mm pad Ht FR BA HK0 ERR _.
    pose proof (sp_facts sp0 VSP RCSP) as SF. pose proof (IMGB_len sp0 argv envp uid hw rnd VSP VARGV VENVP) as IL. pose proof (IMGB_ts sp0 argv envp uid hw rnd EFIT) as ITS. unfold LO in *.
    pose proof BA as (ST & MI & RS & AUX & IMG & SE & SO & YSx & TRx). unfold LO in ST.
    pose proof RS as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & G78 & GD0).
    destruct (HKS _ _ _ _ HK0) as (Hmi & Hh & Hl).
    destruct (HKSSP _ _ _ _ HK0) as [SSP1 SSP2]. unfold RGOT_SSP, RSSP_GUARD in SSP1, SSP2.
    destruct VARGV as (ARGC & _ & ARGLEN & NONUL & _).
    destruct argv as [|arg0 argv'] eqn:EARGV; [cbn in ARGC; lia|]. rewrite <- EARGV in *.
    destruct (argv_cstring sp0 argv envp uid hw rnd mm IMG 0 arg0 ltac:(rewrite EARGV; reflexivity) ltac:(clear -SF; Z.div_mod_to_equations; lia))
      as (p0 & slack0 & HP0 & P0LO & P0HI & STR0 & SLK0 & TOP0).
    destruct (stack_pieces sp0 argv envp uid hw rnd mm IMG) as (_ & ARGVP & _).
    assert (A0NN : ~ In (Z_to_bv 8 0) arg0) by (rewrite EARGV in NONUL; inversion NONUL; assumption).
    assert (A0LEN : Z.of_nat (length arg0) <= 131071) by (rewrite EARGV in ARGLEN; inversion ARGLEN; assumption).
    unfold argc. zstep. if_cases K0; zify_cond K0; try (exfalso; lia). clear K0.
    zstep. zstep. zstep.
    pose proof (u64ro_read mm (usp0 + 8) (argv_ptrs (ed_top rnd) argv envp L_EXECFN ++ [Z_to_bv 64 0]) 0 (Z_to_bv 64 p0) (Z_to_bv 64 (usp0 + 8))
                  ARGVP ltac:(rewrite nth_error_app1 by (rewrite argv_ptrs_length, EARGV; cbn; lia); exact HP0) ltac:(lia) ltac:(unfold wa; f_equal; lia)) as RD.
    zstep. clear RD. zstep. zstep. zstep.
    apply evt_done.
    rewrite EARGV. cbn [hd].
    eapply (rzb_fprintf_diag (DUsage (map bv_unsigned arg0))) with (lo := usp0 - 6144513) (canary := rc_guard) (st := ps0);
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
    replace (ret_pc (Z_to_bv 64 0x136b4)) with (Z_to_bv 64 0x136b4) by (symmetry; rpc).
    pose proof (agree_on_of_munch _ _ _ MUc WMc) as AG.
    assert (OUT : forall a, (usp0 - 128 <= a /\ ~ (0x25368 <= a < 0x25368 + 232)) -> (fun a0 : Z => outside [(usp0 - 6144513, usp0 + -128); (0x25368, 0x25368 + 232)] a0) a).
    { intros a Ha. cbn. lia. }
    assert (OUT2 : forall a, (0x10000 <= a < 0x57000 /\ ~ (0x25368 <= a < 0x25368 + 232)) -> (fun a0 : Z => outside [(usp0 - 6144513, usp0 + -128); (0x25368, 0x25368 + 232)] a0) a).
    { intros a Ha. cbn. lia. }
    unfold MFRAME in FR.
    apply (rw_cells_agree _ _ _ _ _ AG) in FR; [| intros a Ha; apply OUT; cbn in Ha; lia].
    assert (HK2 : HK ps0 [] m2 MO).
    { eapply HKF0; [exact HK0| exact MUc| exact WMc|].
      constructor; [left; cbn [fst snd]; unfold alloc_ceiling in *; lia|]. constructor; [| constructor].
      right; left. cbn [fst snd]. unfold RLIBC, RCTX, RSSP_GUARD, RGOT_SSP. lia. }
    rzb_seg Hh Hl.
    zstep. apply evt_done.
    eapply (rzb_main_return sp0 argv t VSP RCSP Ht HK HKS HKSSP HKLH 2 ps0 ps0 []).
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

Section TUs.
Context {RC__ : OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.RunCeiling.RunCeiling}.
(** The trace set of the argc <> 2 path: the usage line on fd 2, no bytes on
    fd 1 (the stdout flush has nothing to write), exit status 2. *)
Definition TU (argv : list (list byte)) (fs : Fs.Fs) : TSet :=
  ShapeAlg.t_emit (Wz 2 (concat (pieces_usage (map bv_unsigned (hd [] argv)))))
    (ShapeAlg.t_emit (Wz 1 []) (t_exit (bv_and (Z_to_bv 64 2) (Z_to_bv 64 255)) fs)).

Lemma TU_nil : forall argv fs, TU argv fs [].
Proof. intros. apply ShapeAlg.t_emit_has_nil. Qed.
End TUs.
