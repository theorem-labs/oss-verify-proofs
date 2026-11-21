(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3: the start model mo0 adds the entry draw's vDSO run state, its reserved list is init_reserved's and mo0_dmod takes the channel-reader premise; u_main_body and u_main_stmt_lim take the entry_launch_ok_va premise and state u_main_entry over the whole ProcInput and the mmap base; the entry facts take the launch premises, the heap start is built before the argv split, the argv pointers are placed from the stack top and execfn, and the stack bound is the one entry_stk now proves; dheap_init is given the start model's kernel build; the start model's vDSO run is the model's Vdso.vdso_run_init; p_main_body reads the stack pointer's window bounds off valid_sp directly; the driver calls read argc's register value (argcN) through the argv split. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Run.
From LinuxProcessSemantics.LinuxProcessSem Require Vdso.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib Require PropExec.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib Require WallSim.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib Require UStartup UStartupDefs UStartupFacts Amb RealizesEqv TopUbsan.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib Require PStartupDefs.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Fs Require Import Namei.   (* [comment removed for export] *)
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import Tac Bytes SCPS.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require Import Prelim Stdio.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U Require Import UImg CJ_iface CJ_tree F_pad Exit F_printf_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U Require SO_piface.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.SO_piface.Stdio_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U Require SO_piface.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.SO_piface.SO_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U Require Import RRealloc_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U Require CJ_heap_instR.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.CJ_heap_instR.CJ_heap_inst0.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U Require Drv_heap.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.Drv_heap.KB_drv.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U Require Import SO_diag SO_emit SO_exit.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U Require Import Drv_base Drv_entry Drv_heap.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U Require Drv_open.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.Drv_open.Drv_stmt.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U Require Drv_usage.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.Drv_usage.Drv_exit.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U Require Import Drv_usage Drv_open.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U Require Drv_open.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.Drv_open.Drv_loop.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U Require Drv_open.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.Drv_open.Drv_hdr.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U Require Import Drv_trun.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U Require Import CJ_heap_instR.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U Require CJ_heap_instR.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.CJ_heap_instR.RF_realloc_null.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib Require Import ShapeAlg ShapeSpec.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope Z_scope.
Module PS := OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.UStartup.
Module PD := OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.UStartupDefs.
Module CE := OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.WallSim.CatExec.
Module AM := OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Amb.
Module RE := OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RealizesEqv.
Module TU := OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.TopUbsan.
Module SSP := OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.PStartupDefs.StartupSsp.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U Require Drv_open.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.Drv_open.Drv_loop.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U Require Drv_open.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.Drv_open.Drv_hdr.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U Require Import Drv_trun Drv_open SO_exit SO_diag SO_emit.

From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib Require Import SspGuard.
(* [comment removed for export] *)
Section CeilWrap.
Context {ACEIL : Ceil} {AGRD : Guard}.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
Section Model.
  Set Default Proof Using "All".
  Variables (inp : ProcInput) (tid brk mbase sp : word) (lim : Z).   (* [comment removed for export] *)
  Variable rnd : EntryDraw.
  Let mo0 := with_tid tid (with_vdso (Vdso.vdso_run_init (ed_vdso rnd)) (init_model (segments_reserved usegs) brk mbase sp lim inp)).

  Lemma mo0_dmod : in_channel_reader inp = true -> DMOD (in_fs inp) FDS0 mo0.
  Proof. intros HR. subst mo0. split; [split| | |]; first [reflexivity | exact HR]. Qed.
  Lemma mo0_vmmaps : m_vmmaps mo0 = mkVmMapsFull (init_reserved (segments_reserved usegs) mbase sp (in_kernel inp)) [] [] brk brk lim mbase sp.
  Proof. subst mo0. reflexivity. Qed.
  Lemma mo0_lazy : m_vm_lazy mo0 = []. Proof. subst mo0. reflexivity. Qed.
  Lemma mo0_mat : m_vm_materialized mo0 = []. Proof. subst mo0. reflexivity. Qed.
  Lemma mo0_halted : m_halted mo0 = None. Proof. subst mo0. reflexivity. Qed.
End Model.

Lemma frm0_zero : frm0 (Z_to_bv 32 0).
Proof. reflexivity. Qed.

Section TOP.
  (* [comment removed for export] *)
  Let Hr : realloc_scps_stmt LHEAPd := lhd_realloc.
  Let Hrn : rrealloc_null_stmt := rrealloc_null_spec.

  (* [comment removed for export] *)
  Let TRUN : trun_all := trun_proof Hr Hrn so_emit_first_proof so_emit_again_proof.

  Let SO_EXIT : so_exit_stmt := so_exit_proof.
  Let SO_USAGE : so_diag_usage_stmt := so_diag_usage_proof.

  (* [comment removed for export] *)
  Lemma loop_closed : forall sp gp tp F fc fs lo SPB P1 tid path slack data fj v0 v1 v2 v3 v4 v5 v6 v7 q8 q9 q10 q11,
    loop_side sp tp fc lo SPB P1 tid path slack ->
    loop_stmt sp gp tp F fc fs lo SPB P1 tid (wz PSTAGE2_RET) path slack data fj v0 v1 v2 v3 v4 v5 v6 v7 q8 q9 q10 q11.
  Proof.
    intros until q11. intros SIDE.
    apply (loop_proof so_exit_proof so_diag_oom_proof so_diag_refused_proof so_diag_read_error_proof); [exact SIDE|].
    apply (post_proof so_exit_proof so_diag_short_proof so_diag_overrun_proof TRUN). exact SIDE.
  Qed.

  Lemma MAIN2 : main_two_stmt.
  Proof. exact (main_two_proof so_exit_proof so_diag_oom_proof so_diag_read_error_proof so_diag_cannot_open_proof loop_closed). Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Theorem u_main_body : forall (lim : Z) (sp0 brk mbase : word) (rnd : EntryDraw) (inp : ProcInput) (tid : word) (regs : bvmap 5 word) (mem : word -> option byte),
    KInv2.drv_limit <= lim ->
    valid_sp sp0 -> valid_brk usegs brk -> valid_mmap_base mbase -> valid_input inp ->
    entry_stack_fits sp0 (in_argv inp) (in_envp inp) ->
    (0 < bv_unsigned tid < 2^22)%Z ->
    entry_launch_ok_va Sv48 (mkEntry sp0 brk mbase rnd) inp ->
    PS.u_main_entry sp0 inp mbase rnd tid regs mem ->
    alloc_ceiling = bv_unsigned sp0 - stack_max_size ->
    ssp_guard_val = SSP.canary_w (ed_random rnd) ->
    malloc_secret_val = rnd_secret (ed_random rnd) ->
    realizes usegs
      (mkCfg (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.MState.MS (RE.mkR_of regs) bvmap_empty (Z_to_bv 64 0x1316c)
                (Z_to_bv 32 0) None mem (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.PropExec.seg_rom usegs))
             (with_tid tid (with_vdso (Vdso.vdso_run_init (ed_vdso rnd)) (init_model (segments_reserved usegs) brk mbase sp0 lim inp))))
      (spec (in_argv inp) (in_fs inp)).
  Proof.
    intros lim sp0 brk mbase rnd inp tid regs mem HLIM VSP VBRK VMB VINP FITS TID LAU ME CEQ GEQ SEQ.
    pose proof (valid_input_launch _ VINP) as VL.
    pose proof VINP as (VA & VE & VFS & _).
    pose proof VSP as (LO & HI & AL). unfold sp_window_lo in LO. unfold sp_window_hi in HI.
    assert (HCEIL : alloc_ceiling <= bv_unsigned sp0 - 8388608) by (rewrite CEQ; unfold stack_max_size; lia).
    unfold RE.mkR_of.
    rewrite (PS.me_ra _ _ _ _ _ _ _ ME), (PS.me_tp _ _ _ _ _ _ _ ME), (PS.me_a0 _ _ _ _ _ _ _ ME), (PS.me_a1 _ _ _ _ _ _ _ ME).
    lazymatch goal with |- context [mkR _ ?x2 _ _ _ _ _ _ _ _ _ _] => set (sp := x2) end.
    assert (USP : bv_unsigned sp = bv_unsigned sp0 - 48).
    { subst sp. rewrite (PS.me_sp _ _ _ _ _ _ _ ME). apply unsigned_lit. lia. }
    replace (Z_to_bv 64 (bv_unsigned sp0 + 8)) with (wz (bv_unsigned sp + 56)) by (unfold wz; f_equal; lia).
    pose proof (entry_stk sp0 inp mbase brk tid rnd regs mem ME VA VE VSP VL LAU HCEIL SEQ) as ST.
    replace (bv_unsigned sp0 - 48) with (bv_unsigned sp) in ST by lia.
    pose proof (entry_mem_inv sp0 inp mbase brk tid rnd regs mem ME VA VE VSP VL LAU HCEIL SEQ) as MI.
    pose proof (entry_dstat sp0 inp mbase brk tid rnd regs mem ME VA VE VSP VL LAU HCEIL SEQ) as DS.
    pose proof (entry_libc sp0 inp mbase brk tid rnd regs mem ME VA VE VSP VL LAU HCEIL SEQ) as LC.
    pose proof (entry_ssp sp0 inp mbase brk tid rnd regs mem ME VA VE VSP VL LAU HCEIL SEQ) as SSP0. rewrite <- GEQ in SSP0.
    pose proof (entry_stdout sp0 inp mbase brk tid rnd regs mem ME VA VE VSP VL LAU HCEIL SEQ) as SOF.
    pose proof (entry_stderr sp0 inp mbase brk tid rnd regs mem ME VA VE VSP VL LAU HCEIL SEQ) as SEF.
    pose proof (entry_cjst sp0 inp mbase brk tid rnd regs mem ME VA VE VSP VL LAU HCEIL SEQ) as CJ.
    pose proof (entry_errno sp0 inp mbase brk tid rnd regs mem ME VA VE VSP VL LAU HCEIL SEQ) as ER.
    pose proof (entry_initflag sp0 inp mbase brk tid rnd regs mem ME VA VE VSP VL LAU HCEIL SEQ) as IFL.
    pose proof (entry_rs sp0 inp mbase brk tid rnd regs mem ME VA VE VSP VL LAU HCEIL SEQ) as RSC.
    pose proof (entry_argv_str sp0 inp mbase brk tid rnd regs mem ME VA VE VSP VL LAU HCEIL SEQ) as EAS.
    pose proof (entry_argv_ptr sp0 inp mbase brk tid rnd regs mem ME VA VE VSP VL LAU HCEIL SEQ) as EAP.
    (* the heap's start: everything the image and the launch give it, before argv is split *)
    assert (DH : DHEAP0 (bv_unsigned sp + 48) mem (with_tid tid (with_vdso (Vdso.vdso_run_init (ed_vdso rnd)) (init_model (segments_reserved usegs) brk mbase sp0 lim inp)))).
    { rewrite USP. replace (bv_unsigned sp0 - 48 + 48) with (bv_unsigned sp0) by lia.
      eapply (dheap_init mem (PD.auxv_w sp0 inp) (bv_unsigned sp0) _ brk lim mbase sp0 (in_kernel inp)).
      - intros a Ha. apply (entry_none sp0 inp mbase brk tid rnd regs mem ME VA VE VSP VL LAU HCEIL SEQ). lia.
      - exact (entry_libc sp0 inp mbase brk tid rnd regs mem ME VA VE VSP VL LAU HCEIL SEQ).
      - exact (entry_libc2 sp0 inp mbase brk tid rnd regs mem ME VA VE VSP VL LAU HCEIL SEQ).
      - exact (entry_got_ssp sp0 inp mbase brk tid rnd regs mem ME VA VE VSP VL LAU HCEIL SEQ).
      - rewrite GEQ. exact (entry_guard sp0 inp mbase brk tid rnd regs mem ME VA VE VSP VL LAU HCEIL SEQ).
      - exact MI.
      - exact (entry_rauxv sp0 inp mbase brk tid rnd regs mem ME VA VE VSP VL LAU HCEIL SEQ).
      - apply mo0_vmmaps.
      - apply mo0_lazy.
      - apply mo0_mat.
      - apply mo0_halted.
      - reflexivity.
      - exact VBRK.
      - exact VMB.
      - exact HLIM.
      - symmetry. exact CEQ. }
    pose proof (mo0_dmod inp tid brk mbase sp0 lim rnd (valid_input_channel_reader _ VINP)) as DM.
    destruct (in_argv inp) as [|argv0 [|path [|x rest]]] eqn:EAV.
    - exfalso. destruct VA as [[H _] _]. cbn in H. lia.
    - (* [comment removed for export] *)
      destruct (EAS 0%nat ltac:(cbn; lia)) as (slack & BY & SLK & AB & _ & NONUL & LEN).
      pose proof (EAP 0%nat ltac:(cbn; lia)) as AV.
      cbn [nth] in BY, SLK, NONUL, LEN. cbn [hd].
      set (P0w := CE.cat_argv_ptr (ed_top rnd) [argv0] (in_envp inp) (in_execfn inp) 0) in *.
      replace (bv_unsigned sp0 + 8 + 8 * Z.of_nat 0) with (bv_unsigned sp + 56) in AV by lia.
      rewrite <- (Z_to_bv_bv_unsigned P0w) in AV. change (Z_to_bv 64 (bv_unsigned P0w)) with (wz (bv_unsigned P0w)) in AV.
      eapply (main_usage SO_EXIT SO_USAGE) with (lo := bv_unsigned sp0 - 6144512) (argc := 1) (P0 := bv_unsigned P0w) (argv0 := argv0) (slack := slack);
        first [exact DM| exact ST| exact MI| exact DS| exact TID| exact LC| exact SSP0| exact SOF| exact SEF| exact NONUL| exact AV| exact BY| exact SLK| apply frm0_zero
              | reflexivity | unfold PStartupDefs.ArgvEnv.argcN; rewrite EAV; reflexivity | unfold GLOBALS_TOP, zlength in *; lia].
    - (* [comment removed for export] *)
      destruct (EAS 1%nat ltac:(cbn; lia)) as (slack & BY & SLK & AB & _ & NONUL & LEN).
      pose proof (EAP 1%nat ltac:(cbn; lia)) as AV.
      cbn [nth] in BY, SLK, NONUL, LEN.
      set (P1w := CE.cat_argv_ptr (ed_top rnd) [argv0; path] (in_envp inp) (in_execfn inp) 1) in *.
      replace (bv_unsigned sp0 + 8 + 8 * Z.of_nat 1) with (bv_unsigned sp + 64) in AV by lia.
      rewrite <- (Z_to_bv_bv_unsigned P1w) in AV. change (Z_to_bv 64 (bv_unsigned P1w)) with (wz (bv_unsigned P1w)) in AV.
      (* [comment removed for export] *)
      pose proof VA as (_ & _ & _ & _ & VTL). cbn [tl] in VTL. apply Forall_cons_iff in VTL as [[HSL HDDb] _].
      assert (HDD : path <> dotdot_path).
      { intros E. rewrite E in HDDb. rewrite (proj2 (path_eqb_eq dotdot_path dotdot_path) eq_refl) in HDDb. discriminate. }
      rewrite spec_two.
      eapply MAIN2 with (lo := bv_unsigned sp0 - 6144512) (P1 := bv_unsigned P1w) (slack := slack);
        first [exact DM| exact DH| exact ST| exact MI| exact DS| exact TID| exact CJ| exact ER| exact IFL| exact SOF| exact SEF| exact NONUL| exact AV| exact BY| exact SLK| apply frm0_zero
              | exact HSL | exact HDD
              | eexists; exact RSC
              | reflexivity | unfold PStartupDefs.ArgvEnv.argcN; rewrite EAV; reflexivity | rewrite ?USP; unfold GLOBALS_TOP, zlength in *; lia ].
    - (* [comment removed for export] *)
      destruct (EAS 0%nat ltac:(cbn; lia)) as (slack & BY & SLK & AB & _ & NONUL & LEN).
      pose proof (EAP 0%nat ltac:(cbn; lia)) as AV.
      cbn [nth] in BY, SLK, NONUL, LEN. cbn [hd].
      set (P0w := CE.cat_argv_ptr (ed_top rnd) (argv0 :: path :: x :: rest) (in_envp inp) (in_execfn inp) 0) in *.
      replace (bv_unsigned sp0 + 8 + 8 * Z.of_nat 0) with (bv_unsigned sp + 56) in AV by lia.
      rewrite <- (Z_to_bv_bv_unsigned P0w) in AV. change (Z_to_bv 64 (bv_unsigned P0w)) with (wz (bv_unsigned P0w)) in AV.
      destruct VA as [[_ AC] _].
      change (spec (argv0 :: path :: x :: rest) (in_fs inp)) with (t_die (msg_usage argv0) (in_fs inp)).
      eapply (main_usage SO_EXIT SO_USAGE) with (lo := bv_unsigned sp0 - 6144512) (argc := Z.of_nat (length (argv0 :: path :: x :: rest))) (P0 := bv_unsigned P0w) (argv0 := argv0) (slack := slack);
        first [exact DM| exact ST| exact MI| exact DS| exact TID| exact LC| exact SSP0| exact SOF| exact SEF| exact NONUL| exact AV| exact BY| exact SLK| apply frm0_zero
              | reflexivity | unfold PStartupDefs.ArgvEnv.argcN; rewrite EAV; reflexivity | unfold GLOBALS_TOP, zlength in *; cbn [length] in *; lia ].
  Qed.
End TOP.

End CeilWrap.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition u_main_stmt_lim (lim : Z) : Prop :=
  forall (sp brk mbase : word) (rnd : EntryDraw) (inp : ProcInput) (tid : word) (regs : bvmap 5 word) (mem : word -> option byte),
    valid_sp sp -> valid_brk usegs brk -> valid_mmap_base mbase -> valid_input inp ->
    entry_stack_fits sp (in_argv inp) (in_envp inp) ->
    (0 < bv_unsigned tid < 2^22)%Z ->
    entry_launch_ok_va Sv48 (mkEntry sp brk mbase rnd) inp ->
    PS.u_main_entry sp inp mbase rnd tid regs mem ->
    realizes usegs
      (mkCfg (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.MState.MS (RE.mkR_of regs) bvmap_empty (Z_to_bv 64 0x1316c)
                (Z_to_bv 32 0) None mem (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.PropExec.seg_rom usegs))
             (with_tid tid (with_vdso (Vdso.vdso_run_init (ed_vdso rnd)) (init_model (segments_reserved usegs) brk mbase sp lim inp))))
      (spec (in_argv inp) (in_fs inp)).

Theorem u_main_proof_lim : forall lim, KInv2.drv_limit <= lim -> u_main_stmt_lim lim.
Proof.
  intros lim HLIM sp0 brk mbase rnd inp tid regs mem VSP VBRK VMB VINP FITS TID LAU ME.
  pose proof VSP as (V1 & V2 & V3). unfold sp_window_lo, sp_window_hi in V1, V2.
  assert (H1 : 0x7fff7f800000 <= bv_unsigned sp0 - stack_max_size) by (unfold stack_max_size; lia).
  assert (H2 : bv_unsigned sp0 - stack_max_size <= 0x7fffff800000) by (unfold stack_max_size; lia).
  assert (H3 : (bv_unsigned sp0 - stack_max_size) mod 16 = 0).
  { unfold stack_max_size. rewrite Zminus_mod, V3. reflexivity. }
  exact (@u_main_body (ceil_of_val _ H1 H2 H3) (guard_of (SSP.canary_w (ed_random rnd)) (rnd_secret (ed_random rnd))) lim sp0 brk mbase rnd inp tid regs mem
           HLIM VSP VBRK VMB VINP FITS TID LAU ME eq_refl eq_refl eq_refl).
Qed.

Theorem u_main_proof : TU.u_main_stmt.
Proof. apply (u_main_proof_lim target_alloc_limit). unfold KInv2.drv_limit, target_alloc_limit. lia. Qed.
