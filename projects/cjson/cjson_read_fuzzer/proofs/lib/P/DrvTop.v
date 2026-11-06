(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib Require PropExec.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib Require WallSim.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib Require PStartup PStartupDefs PStartupFacts Amb RealizesEqv TopUbsan.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib Require PStartupDefs.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Fs Require Import Namei.   (* [comment removed for export] *)
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import Tac Bytes SCPS.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require Import Prelim Stdio.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require Import PImg CJ_iface CJ_tree F_pad Exit F_printf_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require SO_fprintf.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.SO_fprintf.Stdio_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require SO_fprintf.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.SO_fprintf.SO_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require Import RRealloc_iface CJ_heap_inst0.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require Drv_heap.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Drv_heap.KB_drv.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require Import SO_diag SO_emit.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require SO_emit.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.SO_emit.SO_exit.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require Import Drv_base Drv_entry Drv_heap.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require Drv_hdr.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Drv_hdr.Drv_stmt.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require Drv_usage.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Drv_usage.Drv_exit.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require Import Drv_usage Drv_open Drv_loop Drv_hdr Drv_trun.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require Import CJ_heap_instR.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require CJ_heap_instR.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.CJ_heap_instR.RF_realloc_null.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib Require Import ShapeAlg ShapeSpec.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope Z_scope.
Module PS := OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.PStartup.
Module PD := OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.PStartupDefs.
Module CE := OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.WallSim.CatExec.
Module AM := OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Amb.
Module RE := OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RealizesEqv.
Module TU := OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.TopUbsan.
Module SSP := OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.PStartupDefs.StartupSsp.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require Import Drv_loop Drv_hdr Drv_trun Drv_open.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require SO_emit.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.SO_emit.SO_exit.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require Import SO_diag SO_emit.

From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib Require Import SspGuard.
(* [comment removed for export] *)
Section CeilWrap.
Context {ACEIL : Ceil} {AGRD : Guard}.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
Section Model.
  Variables (inp : ProcInput) (tid brk mbase sp : word) (lim : Z).   (* [comment removed for export] *)
  Let mo0 := with_tid tid (init_model (segments_reserved psegs) brk mbase sp lim inp).

  Lemma mo0_dmod : DMOD (in_fs inp) FDS0 mo0.
  Proof. subst mo0. split; [split| |]; reflexivity. Qed.
  Lemma mo0_vmmaps : m_vmmaps mo0 = mkVmMapsFull (segments_reserved psegs) [] [] brk brk lim mbase sp.
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
  Theorem p_main_body : forall (lim : Z) (sp0 brk mbase : word) (rnd : EntryDraw) (inp : ProcInput) (tid : word) (regs : bvmap 5 word) (mem : word -> option byte),
    KInv2.drv_limit <= lim ->
    valid_sp sp0 -> valid_brk psegs brk -> valid_mmap_base mbase -> valid_input inp ->
    entry_stack_fits sp0 (in_argv inp) (in_envp inp) ->
    (0 < bv_unsigned tid < 2^22)%Z ->
    @PS.p_main_entry (AM.amb_of inp) sp0 rnd (in_argv inp) (in_envp inp) tid regs mem ->
    alloc_ceiling = bv_unsigned sp0 - stack_max_size ->
    ssp_guard_val = SSP.canary_w (ed_random rnd) ->
    malloc_secret_val = rnd_secret (ed_random rnd) ->
    realizes psegs
      (mkCfg (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.MState.MS (RE.mkR_of regs) bvmap_empty (Z_to_bv 64 0x1214c)
                (Z_to_bv 32 0) None mem (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.PropExec.seg_rom psegs))
             (with_tid tid (init_model (segments_reserved psegs) brk mbase sp0 lim inp)))
      (spec (in_argv inp) (in_fs inp)).
  Proof.
    intros lim sp0 brk mbase rnd inp tid regs mem HLIM VSP VBRK VMB VINP FITS TID ME CEQ GEQ SEQ.
    pose proof VINP as (VA & VE & VFS & _).
    set (AMB := AM.amb_of inp) in *.
    pose proof (usp_lo sp0 VSP) as LO. pose proof (usp_hi sp0 VSP) as HI. pose proof (usp_al sp0 VSP) as AL.
    assert (HCEIL : alloc_ceiling <= bv_unsigned sp0 - 8388608) by (rewrite CEQ; unfold stack_max_size; lia).
    unfold RE.mkR_of.
    rewrite (PS.me_ra _ _ _ _ _ _ _ ME), (PS.me_tp _ _ _ _ _ _ _ ME), (PS.me_a0 _ _ _ _ _ _ _ ME), (PS.me_a1 _ _ _ _ _ _ _ ME).
    lazymatch goal with |- context [mkR _ ?x2 _ _ _ _ _ _ _ _ _ _] => set (sp := x2) end.
    assert (USP : bv_unsigned sp = bv_unsigned sp0 - 48).
    { subst sp. rewrite (PS.me_sp _ _ _ _ _ _ _ ME). apply unsigned_lit. lia. }
    replace (Z_to_bv 64 (bv_unsigned sp0 + 8)) with (wz (bv_unsigned sp + 56)) by (unfold wz; f_equal; lia).
    pose proof (entry_stk sp0 _ _ tid rnd regs mem ME VSP) as ST.
    replace (bv_unsigned sp0 - 48) with (bv_unsigned sp) in ST by lia.
    pose proof (entry_mem_inv sp0 _ _ tid rnd regs mem ME VSP FITS) as MI.
    pose proof (entry_dstat sp0 _ _ tid rnd regs mem ME VSP) as DS.
    pose proof (entry_libc sp0 _ _ tid rnd regs mem ME VSP) as LC.
    pose proof (entry_ssp sp0 _ _ tid rnd regs mem ME VSP) as SSP0. rewrite <- GEQ in SSP0.
    pose proof (entry_stdout sp0 _ _ tid rnd regs mem ME VSP) as SOF.
    pose proof (entry_stderr sp0 _ _ tid rnd regs mem ME VSP) as SEF.
    pose proof (mo0_dmod inp tid brk mbase sp0 lim) as DM.
    destruct (in_argv inp) as [|argv0 [|path [|x rest]]] eqn:EAV.
    - exfalso. destruct VA as [[H _] _]. cbn in H. lia.
    - (* [comment removed for export] *)
      destruct (entry_argv_str sp0 _ _ tid rnd regs mem ME VA VE VSP 0%nat ltac:(cbn; lia)) as (slack & BY & SLK & AB & _ & NONUL & LEN).
      pose proof (entry_argv_ptr sp0 _ _ tid rnd regs mem ME VA VE VSP 0%nat ltac:(cbn; lia)) as AV.
      cbn [nth] in BY, SLK, NONUL, LEN. cbn [hd].
      set (P0w := CE.cat_argv_ptr sp0 [argv0] (in_envp inp) 0) in *.
      replace (bv_unsigned sp0 + 8 + 8 * Z.of_nat 0) with (bv_unsigned sp + 56) in AV by lia.
      rewrite <- (Z_to_bv_bv_unsigned P0w) in AV. change (Z_to_bv 64 (bv_unsigned P0w)) with (wz (bv_unsigned P0w)) in AV.
      eapply (main_usage SO_EXIT SO_USAGE) with (lo := bv_unsigned sp0 - 8388608) (argc := 1) (P0 := bv_unsigned P0w) (argv0 := argv0) (slack := slack);
        first [exact DM| exact ST| exact MI| exact DS| exact TID| exact LC| exact SSP0| exact SOF| exact SEF| exact NONUL| exact AV| exact BY| exact SLK| apply frm0_zero
              | reflexivity | unfold GLOBALS_TOP, zlength in *; lia].
    - (* [comment removed for export] *)
      destruct (entry_argv_str sp0 _ _ tid rnd regs mem ME VA VE VSP 1%nat ltac:(cbn; lia)) as (slack & BY & SLK & AB & _ & NONUL & LEN).
      pose proof (entry_argv_ptr sp0 _ _ tid rnd regs mem ME VA VE VSP 1%nat ltac:(cbn; lia)) as AV.
      cbn [nth] in BY, SLK, NONUL, LEN.
      set (P1w := CE.cat_argv_ptr sp0 [argv0; path] (in_envp inp) 1) in *.
      replace (bv_unsigned sp0 + 8 + 8 * Z.of_nat 1) with (bv_unsigned sp + 64) in AV by lia.
      rewrite <- (Z_to_bv_bv_unsigned P1w) in AV. change (Z_to_bv 64 (bv_unsigned P1w)) with (wz (bv_unsigned P1w)) in AV.
      pose proof (entry_cjst sp0 _ _ tid rnd regs mem ME VSP) as CJ.
      pose proof (entry_errno sp0 _ _ tid rnd regs mem ME VSP) as ER.
      pose proof (entry_initflag sp0 _ _ tid rnd regs mem ME VSP) as IFL.
      pose proof (entry_rs sp0 _ _ tid rnd regs mem ME VSP) as RSC.
      (* [comment removed for export] *)
      pose proof VA as (_ & _ & _ & _ & VTL). cbn [tl] in VTL. apply Forall_cons_iff in VTL as [[HSL HDDb] _].
      assert (HDD : path <> dotdot_path).
      { intros E. rewrite E in HDDb. rewrite (proj2 (path_eqb_eq dotdot_path dotdot_path) eq_refl) in HDDb. discriminate. }
      assert (DH : DHEAP0 (bv_unsigned sp + 48) mem (with_tid tid (init_model (segments_reserved psegs) brk mbase sp0 lim inp))).
      { rewrite USP. replace (bv_unsigned sp0 - 48 + 48) with (bv_unsigned sp0) by lia.
        eapply (dheap_init mem (PD.auxv_w sp0 [argv0; path] (in_envp inp)) (bv_unsigned sp0) _ brk lim mbase sp0).
        - intros a Ha. apply (entry_none sp0 _ _ tid rnd regs mem ME VSP). lia.
        - exact (entry_libc sp0 _ _ tid rnd regs mem ME VSP).
        - exact (entry_libc2 sp0 _ _ tid rnd regs mem ME VA VSP).
        - exact (entry_got_ssp sp0 _ _ tid rnd regs mem ME VSP).
        - rewrite GEQ. exact (entry_guard sp0 _ _ tid rnd regs mem ME VSP).
        - exact MI.
        - exact (entry_rauxv sp0 _ _ tid rnd regs mem ME VA VE VSP HCEIL SEQ).
        - apply mo0_vmmaps.
        - apply mo0_lazy.
        - apply mo0_mat.
        - apply mo0_halted.
        - exact VBRK.
        - exact HLIM.
        - symmetry. exact CEQ. }
      rewrite spec_two.
      eapply MAIN2 with (lo := bv_unsigned sp0 - 8388608) (P1 := bv_unsigned P1w) (slack := slack);
        first [exact DM| exact DH| exact ST| exact MI| exact DS| exact TID| exact CJ| exact ER| exact IFL| exact SOF| exact SEF| exact NONUL| exact AV| exact BY| exact SLK| apply frm0_zero
              | exact HSL | exact HDD
              | eexists; exact RSC
              | reflexivity | rewrite ?USP; unfold GLOBALS_TOP, zlength in *; lia ].
    - (* [comment removed for export] *)
      destruct (entry_argv_str sp0 _ _ tid rnd regs mem ME VA VE VSP 0%nat ltac:(cbn; lia)) as (slack & BY & SLK & AB & _ & NONUL & LEN).
      pose proof (entry_argv_ptr sp0 _ _ tid rnd regs mem ME VA VE VSP 0%nat ltac:(cbn; lia)) as AV.
      cbn [nth] in BY, SLK, NONUL, LEN. cbn [hd].
      set (P0w := CE.cat_argv_ptr sp0 (argv0 :: path :: x :: rest) (in_envp inp) 0) in *.
      replace (bv_unsigned sp0 + 8 + 8 * Z.of_nat 0) with (bv_unsigned sp + 56) in AV by lia.
      rewrite <- (Z_to_bv_bv_unsigned P0w) in AV. change (Z_to_bv 64 (bv_unsigned P0w)) with (wz (bv_unsigned P0w)) in AV.
      destruct VA as [[_ AC] _].
      change (spec (argv0 :: path :: x :: rest) (in_fs inp)) with (t_die (msg_usage argv0) (in_fs inp)).
      eapply (main_usage SO_EXIT SO_USAGE) with (lo := bv_unsigned sp0 - 8388608) (argc := Z.of_nat (length (argv0 :: path :: x :: rest))) (P0 := bv_unsigned P0w) (argv0 := argv0) (slack := slack);
        first [exact DM| exact ST| exact MI| exact DS| exact TID| exact LC| exact SSP0| exact SOF| exact SEF| exact NONUL| exact AV| exact BY| exact SLK| apply frm0_zero
              | reflexivity | unfold GLOBALS_TOP, zlength in *; cbn [length] in *; lia ].
  Qed.
End TOP.

End CeilWrap.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition p_main_stmt_lim (lim : Z) : Prop :=
  forall (sp brk mbase : word) (rnd : EntryDraw) (inp : ProcInput) (tid : word) (regs : bvmap 5 word) (mem : word -> option byte),
    valid_sp sp -> valid_brk psegs brk -> valid_mmap_base mbase -> valid_input inp ->
    entry_stack_fits sp (in_argv inp) (in_envp inp) ->
    (0 < bv_unsigned tid < 2^22)%Z ->
    @PS.p_main_entry (AM.amb_of inp) sp rnd (in_argv inp) (in_envp inp) tid regs mem ->
    realizes psegs
      (mkCfg (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.MState.MS (RE.mkR_of regs) bvmap_empty (Z_to_bv 64 0x1214c)
                (Z_to_bv 32 0) None mem (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.PropExec.seg_rom psegs))
             (with_tid tid (init_model (segments_reserved psegs) brk mbase sp lim inp)))
      (spec (in_argv inp) (in_fs inp)).

Theorem p_main_proof_lim : forall lim, KInv2.drv_limit <= lim -> p_main_stmt_lim lim.
Proof.
  intros lim HLIM sp0 brk mbase rnd inp tid regs mem VSP VBRK VMB VINP FITS TID ME.
  pose proof VSP as (V1 & V2 & V3). unfold sp_window_lo, sp_window_hi in V1, V2.
  assert (H1 : 0x7fff7f800000 <= bv_unsigned sp0 - stack_max_size) by (unfold stack_max_size; lia).
  assert (H2 : bv_unsigned sp0 - stack_max_size <= 0x7fffff800000) by (unfold stack_max_size; lia).
  assert (H3 : (bv_unsigned sp0 - stack_max_size) mod 16 = 0).
  { unfold stack_max_size. rewrite Zminus_mod, V3. reflexivity. }
  exact (@p_main_body (ceil_of_val _ H1 H2 H3) (guard_of (SSP.canary_w (ed_random rnd)) (rnd_secret (ed_random rnd))) lim sp0 brk mbase rnd inp tid regs mem
           HLIM VSP VBRK VMB VINP FITS TID ME eq_refl eq_refl eq_refl).
Qed.

Theorem p_main_proof : TU.p_main_stmt.
Proof. apply (p_main_proof_lim source_alloc_limit). unfold KInv2.drv_limit, source_alloc_limit. lia. Qed.
