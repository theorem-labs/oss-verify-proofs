(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from RefStartup.v: the start-up walk (ref_startup) restated over BudgetWit.Rzb.rzb *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From LinuxProcessSemantics.LinuxProcessSem Require Vdso.
From OSSVerify.boost_beast.http_request.images Require Import Plain.
From OSSVerify.Proofs.boost_beast.http_request.lib Require Import
  Amb ShapeAlg Nodes RefNodes FileSim
  StartupTac ArgvEnv RefLayout RefImg RefStartupDefs
  RefStartup1 RefMemset RefStartup2 RefStartup3 RefStartup4 RefStartup5 RefStartup6
 Ref_code_67254_67504   .
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.
From OSSVerify.Proofs.boost_beast.http_request.lib Require Import RefStartup.
From OSSVerify.Proofs.boost_beast.http_request.lib.BudgetWit Require Import Rzb AgentNodesB NodesB LibWritevB RefNodesB SymDriveB.
Abbreviation SEGS := Plain.M.loaded_segments.
Abbreviation RPH := Plain.M.phdrs.
Local Notation rsegs := Plain.M.loaded_segments (only parsing).
Local Notation rpc := Plain.M.init_pc (only parsing).
Local Notation rph := Plain.M.phdrs (only parsing).
Open Scope bv_scope.

Lemma bwd_rz_b : forall segs model K,
  m_halted model = None -> m_vm_lazy model = [] ->
  bwd segs (fun st => rzb segs (mkCfg st model) K).
Proof.
  intros segs model K Hh Hlazy st st' Hms Hst'. eapply rzb_msteps; eassumption.
Qed.

(* RefStartup.v's Section Assembly and [ref_startup], over [rzb]: the start-up walk over the
   run's input and the launch facts, on the binary's own segments.  [usage_never_refused]
   (BudgetWitness.v) lifts it to the run's segment list with [Rzb.rzb_run_init]. *)
Section Assembly.
  Context {AMB : Amb}.
  Variable inp : ProcInput.
  Variable mbase : word.
  Variable sp brk : word.
  Variable rnd : EntryDraw.
  Hypothesis Hva : valid_argv (in_argv inp).
  Hypothesis Hve : valid_envp (in_envp inp).
  Hypothesis Hvl : valid_launch inp.
  Hypothesis Hlau : entry_launch_ok_va Sv48 (mkEntry sp brk mbase rnd) inp.
  Hypothesis Hvsp : valid_sp sp.

  Lemma Hlo : (0x7fff80000000 <= bv_unsigned sp)%Z.
  Proof. destruct Hvsp as [H _]. exact H. Qed.
  Lemma Hhi : (bv_unsigned sp <= 0x800000000000)%Z.
  Proof. destruct Hvsp as [_ [H _]]. exact H. Qed.
  Lemma Hal : (bv_unsigned sp mod 16 = 0)%Z.
  Proof. destruct Hvsp as [_ [_ H]]. exact H. Qed.

  Let J0 : word -> option byte :=
    stack_zero (stack_window_lo (in_kernel inp) mbase rnd).

  Lemma HJ0 : wfJ sp J0.
  Proof. exact (wfJ_stack_zero inp sp brk mbase rnd Hvl Hlau). Qed.

  Ltac side Hva Hve HG :=
    first [ exact Hva | exact Hve | exact Hlo | exact Hhi | exact Hal | exact HG
          | apply (wfJ_stack_zero inp sp brk mbase rnd Hvl Hlau)
          | apply wfJ_const
          | lazymatch goal with |- getr _ _ = _ =>
              gres; first [ assumption | reflexivity | bveq
                          | match goal with H : getr ?rs ?n = _ |- getr ?rs ?n = _ =>
                              rewrite H; unfold envp_w, envp_ptr, argv_w, pn_w, argc_w;
                              first [reflexivity | f_equal; lia | bveq] end ] end
          | idtac ].

  Local Notation M0 lim := (with_vdso (Vdso.vdso_run_init (ed_vdso rnd))
                              (init_model (segments_reserved rsegs) brk mbase sp lim inp)) (only parsing).

  Theorem ref_startup_sec_b : forall lim K,
    (forall tid regs mem,
       (0 < bv_unsigned tid < 2^22)%Z ->
       main_entry inp mbase (0x2ab1c : word) sp rnd tid regs mem ->
       rzb rsegs (mkCfg (mkst regs (0x2ac68 : word) mem (seg_rom rsegs))
                        (with_tid tid (M0 lim))) K) ->
    rzb rsegs (init_config rsegs rpc rph sp brk mbase rnd lim inp) K.
  Proof.
    intros lim K HK.
    pose proof Hlo as Hlo'. pose proof Hhi as Hhi'. pose proof Hal as Hal'.
    pose proof (u64_range sp) as Hsp.
    unfold init_config. cbn [cfg_ms cfg_model].
    set (model := M0 lim).
    assert (Hh : m_halted model = None) by reflexivity.
    assert (Hlazy : m_vm_lazy model = []) by reflexivity.
    assert (Ht0 : m_tid model = None) by reflexivity.
    set (RZ := fun st : machine_state => rzb rsegs (mkCfg st model) K).
    assert (HG : bwd rsegs RZ) by (apply bwd_rz_b; [exact Hh | exact Hlazy]).
    rewrite init_mkst.
    replace (Z_to_bv 64 (Z.of_N Plain.M.init_pc)) with (0x2ab1c : word) by (apply bv_eq; reflexivity).
    rewrite (cmem_init inp mbase rph (0x2ab1c : word) sp brk rnd Hlau).
    fold (regs_init sp).
    destruct (p1_run Sv48 inp mbase (0x2ab1c : word) sp brk rnd
                Hva Hve Hvl Hlau Hlo' Hhi' Hal' (seg_rom rsegs) J0 HJ0)
      as [regs1 (R1 & A1 & A2 & A3 & A4 & A8 & A9 & A10 & A11 & A12 & A18 & Az)].
    eapply rzb_msteps; [exact Hh | exact Hlazy | exact R1 |].
    assert (A1' : getr regs1 1 = (0x66e88 : word)) by (rewrite A1; apply bv_eq; reflexivity).
    destruct (memset304_run regs1 (cmem sp (wrap_mem inp mbase RPH (0x2ab1c : word) sp rnd) (J1 inp sp J0) (fun _ => None))
                (seg_rom rsegs) (Z_to_bv 64 (bv_unsigned sp - 368)) (0x66e88 : word) A1')
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
    change (rzb rsegs (mkCfg ?st model) K) with (RZ st).
    eapply (p3_run Sv48 inp mbase (0x2ab1c : word) sp brk rnd
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
    change (J1 inp sp J0) with (J_lsm inp sp J0).
    eapply (tls_c1 Sv48 inp mbase (0x2ab1c : word) sp brk J0 rnd
              Hva Hve Hvl Hlau Hlo Hhi Hal) with (G := RZ) (s1v := getr regs3 9) (tid := Z_to_bv 64 0); try side Hva Hve HG.
    intros regs4a; intros.
    eapply (tls_c2 Sv48 inp mbase (0x2ab1c : word) sp brk J0 rnd
              Hva Hve Hvl Hlau Hlo Hhi Hal) with (G := RZ) (tid := Z_to_bv 64 0); try side Hva Hve HG.
    intros regs4b; intros.
    eapply (tls_c3 Sv48 inp mbase (0x2ab1c : word) sp brk J0 rnd
              Hva Hve Hvl Hlau Hlo Hhi Hal) with (G := RZ) (tid := Z_to_bv 64 0); try side Hva Hve HG.
    intros regs4c; intros.
    eapply (tls_c4 Sv48 inp mbase (0x2ab1c : word) sp brk J0 rnd
              Hva Hve Hvl Hlau Hlo Hhi Hal) with (G := RZ) (tid := Z_to_bv 64 0); try side Hva Hve HG.
    intros regs4; intros.
    unfold RZ at 1.
    eapply (rzb_set_tid rsegs regs4 (0x674b0 : word) _ (seg_rom rsegs) model K W_674b0 F_674b0 E_674b0);
      [exact Hh | exact Hlazy | assumption | exact Ht0 |].
    intros tid Htid'.
    assert (Htid : (0 < bv_unsigned tid < 2^22)%Z) by (unfold Fork.PID_MAX_ENVELOPE in Htid'; exact Htid').
    replace (v_addi (0x674b0 : word) 4) with (0x674b4 : word) by (apply bv_eq; reflexivity).
    set (model' := with_tid tid model).
    assert (Hh' : m_halted model' = None) by (unfold model'; rewrite with_tid_halted; exact Hh).
    assert (Hlazy' : m_vm_lazy model' = []) by (unfold model'; rewrite with_tid_lazy; exact Hlazy).
    set (RZ' := fun st : machine_state => rzb rsegs (mkCfg st model') K).
    assert (HG' : bwd rsegs RZ') by (apply bwd_rz_b; [exact Hh' | exact Hlazy']).
    change (rzb rsegs (mkCfg ?st model') K) with (RZ' st).
    eapply (tls_c5 Sv48 inp mbase (0x2ab1c : word) sp brk J0 rnd
              Hva Hve Hvl Hlau Hlo Hhi Hal) with (G := RZ'); try side Hva Hve HG'.
    intros regs5; intros.
    eapply (fin_c6 Sv48 inp mbase (0x2ab1c : word) sp brk J0 rnd
              Hva Hve Hvl Hlau Hlo Hhi Hal) with (G := RZ'); try side Hva Hve HG'.
    intros regs6; intros.
    eapply (fin_c7 Sv48 inp mbase (0x2ab1c : word) sp brk J0 rnd
              Hva Hve Hvl Hlau Hlo Hhi Hal) with (G := RZ'); try side Hva Hve HG'.
    intros regs7; intros.
    eapply (fin_c8 Sv48 inp mbase (0x2ab1c : word) sp brk J0 rnd
              Hva Hve Hvl Hlau Hlo Hhi Hal) with (G := RZ'); try side Hva Hve HG'.
    intros regs8; intros.
    eapply (fin_c9a Sv48 inp mbase (0x2ab1c : word) sp brk J0 rnd
              Hva Hve Hvl Hlau Hlo Hhi Hal) with (G := RZ'); try side Hva Hve HG'.
    intros regs9a; intros.
    eapply (fin_c9b Sv48 inp mbase (0x2ab1c : word) sp brk J0 rnd
              Hva Hve Hvl Hlau Hlo Hhi Hal) with (G := RZ'); try side Hva Hve HG'.
    intros regs9b; intros.
    eapply (fin_c9c Sv48 inp mbase (0x2ab1c : word) sp brk J0 rnd
              Hva Hve Hvl Hlau Hlo Hhi Hal) with (G := RZ'); try side Hva Hve HG'.
    intros regs9c; intros.
    eapply (fin_c9d Sv48 inp mbase (0x2ab1c : word) sp brk J0 rnd
              Hva Hve Hvl Hlau Hlo Hhi Hal) with (G := RZ'); try side Hva Hve HG'.
    intros regs9; intros.
    unfold RZ'. apply (HK tid regs9). { exact Htid. }
    split; try assumption.
    - intros r Hr. cbn [In] in Hr.
      repeat (destruct Hr as [<-|Hr]; [assumption|]). destruct Hr.
    - eexists _, (getr regs3 9). split; [|split; [reflexivity|]].
      + unfold J_main, J_tls, J_aux, J_lsm. repeat first [apply wfJ_J_rseq | apply wfJ_wbytes]. exact HJ0.
      + unfold J_main, J_tls, D_main, D_cx, D_fd, D_ssp, D_tls, D_tlsA, D_tlsB. reflexivity.
  Qed.

End Assembly.

Theorem ref_startup_b : forall sp brk mbase rnd lim inp K,
  valid_sp sp -> valid_brk rsegs brk -> valid_argv (in_argv inp) -> valid_envp (in_envp inp) ->
  valid_launch inp ->
  entry_launch_ok_va Sv48 (mkEntry sp brk mbase rnd) inp ->
  (forall tid regs mem,
     (0 < bv_unsigned tid < 2^22)%Z ->
     @main_entry (amb_of inp) inp mbase (0x2ab1c : word) sp rnd tid regs mem ->
     rzb rsegs
       (mkCfg (mkst regs (0x2ac68 : word) mem (seg_rom rsegs))
              (with_tid tid (with_vdso (Vdso.vdso_run_init (ed_vdso rnd))
                 (init_model (segments_reserved rsegs) brk mbase sp lim inp)))) K) ->
  rzb rsegs (init_config rsegs rpc rph sp brk mbase rnd lim inp) K.
Proof.
  intros sp brk mbase rnd lim inp K Hsp Hbrk Hva Hve Hvl Hlau HK.
  exact (@ref_startup_sec_b (amb_of inp) inp mbase sp brk rnd
           Hva Hve Hvl Hlau Hsp lim K HK).
Qed.
