(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from D_Stmwg.v: the start-up walk (ref_startup) restated over BudgetWit.Rzb.rzb *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (the start-up walk over the launch input ProcInput, its mmap base, entry point and entry draw, the CONFIG_RSEQ flag, the vDSO model and the init stack window), as bzip2/bzip2_compress_target's BudgetWit start-up was. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.varnish.esi_parse_fuzzer.images Require Import Plain.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Amb ShapeAlg Nodes RefNodes.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require MmapSim.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Star5ef ArgvEnv RefL1zx.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require RefL1zx.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require D_St4s2 D_Sts1s.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require D_Stfzw.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require D_St53g.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require D_St53g D_Stfzw D_co4d2 D_coj29.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Amb OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.ShapeAlg OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Nodes OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.RefNodes OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.MmapSim.FileSim OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Star5ef OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.ArgvEnv OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.RefL1zx OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.RefL1zx.D_Img OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.D_St4s2 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.D_Sts1s OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.D_Stfzw.D_Memset OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.D_St53g.D_St6k6 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.D_St53g OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.D_Stfzw OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.D_co4d2 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.D_coj29.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import BWorld.
Import ListNotations.

Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_noeuclid ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_post_hook.

Open Scope bv_scope.

Abbreviation SEGS := Plain.M.loaded_segments.
Abbreviation RPH := Plain.M.phdrs.

Local Notation rsegs := Plain.M.loaded_segments (only parsing).
Local Notation rpc := Plain.M.init_pc (only parsing).
Local Notation rph := Plain.M.phdrs (only parsing).
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import D_Stmwg.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.BudgetWit Require Import Rzb Agenxn8B NodesB RefNodesB.

Lemma bwd_rz_b : forall segs model K,
  m_halted model = None -> m_vm_lazy model = [] ->
  bwd segs (fun st => rzb segs (mkCfg st model) K).
Proof.
  intros segs model K Hh Hlazy st st' Hms Hst'. eapply rzb_msteps; eassumption.
Qed.

Section Assembly.
  Variable inp : ProcInput.
  Variable mbase : word.
  Variable sp brk : word.
  Variable rdraw : EntryDraw.
  Hypothesis Hva : valid_argv (in_argv inp).
  Hypothesis Hve : valid_envp (in_envp inp).
  Hypothesis Hvl : valid_launch inp.
  Hypothesis Hlau : entry_launch_ok_va Sv48 (mkEntry sp brk mbase rdraw) inp.
  Hypothesis Hvsp : valid_sp sp.

  Lemma Hlo : (0x7fff80000000 <= bv_unsigned sp)%Z.
  Proof. destruct Hvsp as [H _]. exact H. Qed.
  Lemma Hhi : (bv_unsigned sp <= 0x800000000000)%Z.
  Proof. destruct Hvsp as [_ [H _]]. exact H. Qed.
  Lemma Hal : (bv_unsigned sp mod 16 = 0)%Z.
  Proof. destruct Hvsp as [_ [_ H]]. exact H. Qed.

  Let J0 : word -> option byte :=
    stack_zero (stack_window_lo (in_kernel inp) mbase rdraw).

  #[using="Hvl Hlau"] Lemma HJ0 : wfJ sp J0.
  Proof. exact (wfJ_stack_zero inp sp brk mbase rdraw Hvl Hlau). Qed.

  Ltac side Hva Hve HG :=
    first [ exact Hva | exact Hve | exact Hvl | exact Hlau | exact Hlo | exact Hhi | exact Hal | exact HG
          | exact HJ0
          | apply (wfJ_stack_zero inp sp brk mbase rdraw Hvl Hlau)
          | apply wfJ_const
          | lazymatch goal with |- getr _ _ = _ =>
              gres; first [ assumption | reflexivity | bveq
                          | match goal with H : getr ?rs ?n = _ |- getr ?rs ?n = _ =>
                              rewrite H; unfold envp_w, envp_ptr, argv_w, pn_w, argc_w;
                              first [reflexivity | f_equal; lia | bveq] end ] end
          | idtac ].

  #[using="J0 Hvsp Hve Hva Hvl Hlau"] Theorem ref_startup_sec_b : forall lim K,
    (forall tid regs mem,
       (0 < bv_unsigned tid < 2^22)%Z ->
       main_entry inp mbase (0x17a18 : word) sp rdraw tid regs mem ->
       rzb rsegs (mkCfg (mkst regs (0x17b64 : word) mem (seg_rom rsegs))
                             (with_tid tid (with_vdso (Vdso.vdso_run_init (ed_vdso rdraw))
                                (init_model (segments_reserved rsegs) brk mbase sp lim inp)))) K) ->
    rzb rsegs (init_config rsegs rpc rph sp brk mbase rdraw lim inp) K.
  Proof.
    intros lim K HK.
    pose proof Hlo as Hlo'. pose proof Hhi as Hhi'. pose proof Hal as Hal'.
    pose proof (u64_range sp) as Hsp.
    unfold init_config. cbn [cfg_ms cfg_model].
    set (model := with_vdso (Vdso.vdso_run_init (ed_vdso rdraw)) (init_model (segments_reserved rsegs) brk mbase sp lim inp)).
    assert (Hh : m_halted model = None) by reflexivity.
    assert (Hlazy : m_vm_lazy model = []) by reflexivity.
    assert (Ht0 : m_tid model = None) by reflexivity.
    set (RZ := fun st : machine_state => rzb rsegs (mkCfg st model) K).
    assert (HG : bwd rsegs RZ) by (apply bwd_rz_b; [exact Hh | exact Hlazy]).
    rewrite init_mkst.
    replace (Z_to_bv 64 (Z.of_N Plain.M.init_pc)) with (0x17a18 : word) by (apply bv_eq; reflexivity).
    rewrite (cmem_init inp mbase rph (0x17a18 : word) sp brk rdraw Hlau).
    fold (regs_init sp).
    
    destruct (p1_run sp inp mbase (0x17a18 : word) rdraw Hva Hve Hlo' Hhi' Hal' (seg_rom SEGS) J0 HJ0)
      as [regs1 (R1 & A1 & A2 & A3 & A4 & A8 & A9 & A10 & A11 & A12 & A18 & Az)].
    eapply rzb_msteps; [exact Hh | exact Hlazy | exact R1 |].
    
    assert (A1' : getr regs1 1 = (0x220ec : word)) by (rewrite A1; apply bv_eq; reflexivity).
    destruct (memset304_run regs1 (cmem sp (wrap_mem inp mbase RPH (0x17a18 : word) sp rdraw) (J1 sp inp J0) (fun _ => None))
                (seg_rom SEGS) (Z_to_bv 64 (bv_unsigned sp - 368)) (0x220ec : word) A1')
      as [regs2 [mem2 (R2 & M2 & G2)]].
    { unfold ret_ok. apply bv_eq. vm_compute. reflexivity. }
    { exact A10. } { exact A11. } { exact A12. }
    { rewrite u_Z2bv by lia. rewrite <- Zminus_mod_idemp_l.
      replace (bv_unsigned sp mod 8)%Z with 0%Z; [reflexivity|].
      symmetry. rewrite <- (Z.mod_mod_divide _ 16 8) by (exists 2%Z; reflexivity). rewrite Hal'. reflexivity. }
    { rewrite u_Z2bv by lia. lia. }
    { apply store_ok_cmem_win; [unfold J1; repeat apply wfJ_wbytes; exact HJ0 | region_side | region_side]. }
    eapply rzb_msteps; [exact Hh | exact Hlazy | exact R2 |]. subst mem2.
    rewrite wbytes_cmem_win by region_side.
    
    carry G2 A2 (2:reg) B2. carry G2 A8 (8:reg) B8. carry G2 A9 (9:reg) B9. carry G2 A10 (10:reg) B10.
    carry G2 A3 (3:reg) B3.
    change (rzb SEGS (mkCfg ?st model) K) with (RZ st).
    eapply (p3_run Sv48 inp mbase (0x17a18 : word) sp brk rdraw
              Hva Hve Hvl Hlau Hlo Hhi Hal) with (G := RZ); try side Hva Hve HG.
    { unfold J1; repeat apply wfJ_wbytes; exact HJ0. }
    intros regs3 C1 C2 C10 C18 G3.
    carry G3 B3 (3:reg) C3. carry G3 B8 (8:reg) C8.
    assert (Cz : forall r : reg, In r [5; 19; 20; 21; 22; 23; 24; 25; 26; 27]%list -> getr regs3 r = Z_to_bv 64 0).
    { intros r Hr. rewrite (G3 r), (G2 r); [apply Az; exact Hr | |];
        clear -Hr; cbn [In] in Hr; intros HH; cbn [In] in HH;
        repeat (destruct Hr as [<-|Hr]; [repeat (destruct HH as [HH|HH]; [apply bv_eq in HH; cbv in HH; discriminate HH|]); exact HH |]); exact Hr. }
    pose proof (Cz 19 ltac:(in_list)) as Z19. pose proof (Cz 20 ltac:(in_list)) as Z20.
    pose proof (Cz 21 ltac:(in_list)) as Z21. pose proof (Cz 22 ltac:(in_list)) as Z22.
    pose proof (Cz 23 ltac:(in_list)) as Z23. pose proof (Cz 24 ltac:(in_list)) as Z24.
    pose proof (Cz 25 ltac:(in_list)) as Z25. pose proof (Cz 26 ltac:(in_list)) as Z26.
    pose proof (Cz 27 ltac:(in_list)) as Z27.
    
    change (J1 sp inp J0) with (J_lsm inp sp J0).
    eapply (tls_c1 Sv48 inp mbase (0x17a18 : word) sp brk J0 rdraw
              Hva Hve Hvl Hlau Hlo Hhi Hal) with (G := RZ) (s1v := getr regs3 9) (tid := Z_to_bv 64 0); try side Hva Hve HG.
    intros regs4a; intros.
    eapply (tls_c2 Sv48 inp mbase (0x17a18 : word) sp brk J0 rdraw
              Hva Hve Hvl Hlau Hlo Hhi Hal) with (G := RZ) (tid := Z_to_bv 64 0); try side Hva Hve HG.
    intros regs4b; intros.
    eapply (tls_c3 Sv48 inp mbase (0x17a18 : word) sp brk J0 rdraw
              Hva Hve Hvl Hlau Hlo Hhi Hal) with (G := RZ) (tid := Z_to_bv 64 0); try side Hva Hve HG.
    intros regs4c; intros.
    eapply (tls_c4 Sv48 inp mbase (0x17a18 : word) sp brk J0 rdraw
              Hva Hve Hvl Hlau Hlo Hhi Hal) with (G := RZ) (tid := Z_to_bv 64 0); try side Hva Hve HG.
    intros regs4; intros.
    
    unfold RZ at 1.
    eapply (rzb_set_tid SEGS regs4 (0x2263c : word) _ (seg_rom SEGS) model K W_2263c F_2263c E_2263c);
      [exact Hh | exact Hlazy | assumption | exact Ht0 |].
    intros tid Htid.
    replace (v_addi (0x2263c : word) 4) with (0x22640 : word) by (apply bv_eq; reflexivity).
    set (model' := with_tid tid model).
    assert (Hh' : m_halted model' = None) by (unfold model'; rewrite with_tid_halted; exact Hh).
    assert (Hlazy' : m_vm_lazy model' = []) by (unfold model'; rewrite with_tid_lazy; exact Hlazy).
    set (RZ' := fun st : machine_state => rzb rsegs (mkCfg st model') K).
    assert (HG' : bwd rsegs RZ') by (apply bwd_rz_b; [exact Hh' | exact Hlazy']).
    change (rzb SEGS (mkCfg ?st model') K) with (RZ' st).
    eapply (tls_c5 Sv48 inp mbase (0x17a18 : word) sp brk J0 rdraw
              Hva Hve Hvl Hlau Hlo Hhi Hal) with (G := RZ'); try side Hva Hve HG'.
    intros regs5; intros.
    eapply (fin_c6 Sv48 inp mbase (0x17a18 : word) sp brk J0 rdraw
              Hva Hve Hvl Hlau Hlo Hhi Hal) with (G := RZ'); try side Hva Hve HG'.
    intros regs6; intros.
    eapply (fin_c7 Sv48 inp mbase (0x17a18 : word) sp brk J0 rdraw
              Hva Hve Hvl Hlau Hlo Hhi Hal) with (G := RZ'); try side Hva Hve HG'.
    intros regs7; intros.
    eapply (fin_c8 Sv48 inp mbase (0x17a18 : word) sp brk J0 rdraw
              Hva Hve Hvl Hlau Hlo Hhi Hal) with (G := RZ'); try side Hva Hve HG'.
    intros regs8; intros.
    eapply (fin_c9 Sv48 inp mbase (0x17a18 : word) sp brk J0 rdraw
              Hva Hve Hvl Hlau Hlo Hhi Hal) with (G := RZ'); try side Hva Hve HG'.
    intros regs9 M1 M2 M3 M4 M8 M9 M10 M11 M12 M18 M19 M20 M21 M22 M23 M24 M25 M26 M27 G9.
    unfold RZ'. apply (HK tid regs9). { exact Htid. }
    split; try assumption.
    - intros r Hr. cbn [In] in Hr.
      repeat (destruct Hr as [<-|Hr]; [assumption|]). destruct Hr.
    - eexists _, (getr regs3 9). split; [|split; [reflexivity|]].
      + unfold J_main, J_tls, J_aux, J_rseq, J_lsm.
        destruct (kb_rseq (in_kernel inp)); repeat apply wfJ_wbytes; exact HJ0.
      + unfold J_main, J_tls, D_main, D_fd, D_ssp, D_tls, D_tlsA, D_tlsB. reflexivity.
  Qed.

End Assembly.

Theorem ref_startup_b : forall sp brk mbase rdraw lim inp K,
  valid_sp sp -> valid_brk rsegs brk -> valid_argv (in_argv inp) -> valid_envp (in_envp inp) ->
  in_abort_terminal inp = false ->
  valid_launch inp ->
  entry_launch_ok_va Sv48 (mkEntry sp brk mbase rdraw) inp ->
  (forall tid regs mem,
     (0 < bv_unsigned tid < 2^22)%Z ->
     main_entry inp mbase (0x17a18 : word) sp rdraw tid regs mem ->
     rzb rsegs (mkCfg (mkst regs (0x17b64 : word) mem (seg_rom rsegs))
                           (with_tid tid (with_vdso (Vdso.vdso_run_init (ed_vdso rdraw))
                              (init_model (segments_reserved rsegs) brk mbase sp lim inp)))) K) ->
  rzb rsegs (init_config rsegs rpc rph sp brk mbase rdraw lim inp) K.
Proof.
  intros sp brk mbase rdraw lim inp K Hsp Hbrk Hva Hve Hab Hvl Hlau HK.
  eapply ref_startup_sec_b; eassumption.
Qed.
