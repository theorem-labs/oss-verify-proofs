(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* Modified by Theorem Labs, 2026-11: made from Src0Startup.v: the R-typed declarations restated over the budget carrier, with twin modules imported last. *)
(* Modified by Theorem Labs, 2026-11: for LPS 727298f3, the budget start-up is stated over the launch input with its launch facts (valid_launch, entry_launch_ok_va), the zero-filled part of the start-up memory is stack_zero below the launch's stack window, and the start model carries the vDSO pair. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Vdso Run.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import ExecutableSpecs.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_bigint.images Require Import Plain.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib Require Import
  ShapeAlg DivergeSim SpinAlg SpinAlgX Nodes RefNodes FileSim
  StartupTac ArgvEnv RefLayout Src0Img Src0StartupDefs
  Src0Startup1 Src0Memset Src0Startup2 Src0Startup3 Src0Startup4
 Src0_code_1ffac_20088 Src0_code_20088_210bc Src0_code_4abb8_4b0b4   Src0_code_4b104_4b654.
Import ListNotations.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib Require PropExec.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib Require Import Src0Startup.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib.BudgetWit Require Import RefNodesB SpinAlgB.

Open Scope bv_scope.
Local Notation rsegs := Plain.M.loaded_segments (only parsing).
Local Notation rpc := Plain.M.init_pc (only parsing).
Local Notation rph := Plain.M.phdrs (only parsing).
Unset Lia Cache.
Unset Nia Cache.
Unset Nra Cache.
Section FPX_1.
#[local] Existing Instance PropExec.fx0.
Lemma bwd_rz_b : forall segs scfg model K,
  m_halted model = None -> m_vm_lazy model = [] ->
  bwd segs (fun st => SpinAlgB.rzb segs scfg (mkCfg st model) K).
Proof.
  intros segs scfg model K Hh Hlazy st st' Hms Hst'. eapply SpinAlgB.rzb_msteps; eassumption.
Qed.
Section Assembly.
Variable scfg : SpuriousCfg.
Variable inp : ProcInput.
Variable mbase : word.
Variable sp brk : word.
Variable rdraw : EntryDraw.
Local Notation argv := (in_argv inp) (only parsing).
Local Notation envp := (in_envp inp) (only parsing).
Hypothesis Hva : valid_argv argv.
Hypothesis Hve : valid_envp envp.
Hypothesis Hvsp : valid_sp sp.
Hypothesis Hvl : valid_launch inp.
Hypothesis Hlau : entry_launch_ok_va Sv48 (mkEntry sp brk mbase rdraw) inp.
Local Notation ENT := (0x1ffac : word) (only parsing).
Lemma Hlo : (0x7fff80000000 <= bv_unsigned sp)%Z.
  Proof. destruct Hvsp as [H _]. exact H. Qed.
Lemma Hhi : (bv_unsigned sp <= 0x800000000000)%Z.
  Proof. destruct Hvsp as [_ [H _]]. exact H. Qed.
Lemma Hal : (bv_unsigned sp mod 16 = 0)%Z.
  Proof. destruct Hvsp as [_ [_ H]]. exact H. Qed.
Let J0 : word -> option byte := stack_zero (stack_window_lo (in_kernel inp) mbase rdraw).
Lemma HJ0 : wfJ sp J0.
  Proof. exact (wfJ_stack_zero inp sp brk mbase rdraw Hvl Hlau). Qed.
Ltac side Hva Hve HG :=
    first [ exact Hva | exact Hve | exact Hvl | exact Hlau | exact Hlo | exact Hhi | exact Hal | exact HG
          | exact HJ0
          | lazymatch goal with |- getr _ _ = _ =>
              gres; first [ assumption | reflexivity | bveq
                          | match goal with H : getr ?rs ?n = _ |- getr ?rs ?n = _ =>
                              rewrite H; unfold envp_w, envp_ptr, argv_w, pn_w, argc_w, argcN;
                              first [reflexivity | f_equal; lia | bveq] end ] end
          | idtac ].
Theorem ref_startup_sec_b : forall lim K,
    (forall tid regs mem,
       (0 < bv_unsigned tid < 2^22)%Z ->
       Src0Startup.main_entry inp mbase ENT sp argv envp (in_uid inp) (in_hwcap inp) rdraw tid regs mem ->
       SpinAlgB.rzb rsegs scfg (mkCfg (mkst regs (0x200f8 : word) mem (seg_rom rsegs))
                             (with_tid tid (with_vdso (Vdso.vdso_run_init (ed_vdso rdraw))
                                (init_model (segments_reserved rsegs) brk mbase sp lim inp)))) K) ->
    SpinAlgB.rzb rsegs scfg (init_config rsegs rpc rph sp brk mbase rdraw lim inp) K.
  Proof.
    intros lim K HK.
    pose proof Hlo as Hlo'. pose proof Hhi as Hhi'. pose proof Hal as Hal'.
    pose proof (u64_range sp) as Hsp.
    unfold init_config. cbn [cfg_ms cfg_model].
    set (model := with_vdso (Vdso.vdso_run_init (ed_vdso rdraw)) (init_model (segments_reserved rsegs) brk mbase sp lim inp)).
    assert (Hh : m_halted model = None) by reflexivity.
    assert (Hlazy : m_vm_lazy model = []) by reflexivity.
    assert (Ht0 : m_tid model = None) by reflexivity.
    set (RZ := fun st : machine_state => SpinAlgB.rzb rsegs scfg (mkCfg st model) K).
    assert (HG : bwd rsegs RZ) by (apply bwd_rz_b; [exact Hh | exact Hlazy]).
    rewrite init_mkst.
    replace (Z_to_bv 64 (Z.of_N Plain.M.init_pc)) with (0x1ffac : word) by (apply bv_eq; reflexivity).
    rewrite (cmem_init inp mbase RPH ENT sp brk rdraw Hlau). fold (regs_init sp). fold J0.
    destruct (p1_run Sv48 inp mbase ENT sp brk rdraw Hva Hve Hvl Hlau Hlo' Hhi' Hal' (seg_rom SEGS) J0 HJ0)
      as [regs1 (R1 & A1 & A2 & A3 & A4 & A8 & A9 & A10 & A11 & A12 & A18 & Az)].
    eapply SpinAlgB.rzb_msteps; [exact Hh | exact Hlazy | exact R1 |].
    assert (A1' : getr regs1 1 = (0x4abe8 : word)) by (rewrite A1; apply bv_eq; reflexivity).
    destruct (memset304_run regs1 (cmem sp (wrap_mem inp mbase RPH ENT sp rdraw) (J1 inp sp J0) (fun _ => None))
                (seg_rom SEGS) (Z_to_bv 64 (bv_unsigned sp - 368)) (0x4abe8 : word) A1')
      as [regs2 [mem2 (R2 & M2 & G2)]].
    { unfold ret_ok. apply bv_eq. vm_compute. reflexivity. }
    { exact A10. } { exact A11. } { exact A12. }
    { rewrite u_Z2bv by lia. rewrite <- Zminus_mod_idemp_l.
      replace (bv_unsigned sp mod 8)%Z with 0%Z; [reflexivity|].
      symmetry. rewrite <- (Z.mod_mod_divide _ 16 8) by (exists 2%Z; reflexivity). rewrite Hal'. reflexivity. }
    { rewrite u_Z2bv by lia. lia. }
    { apply store_ok_cmem_win; [unfold J1; repeat apply wfJ_wbytes; exact HJ0 | region_side | region_side]. }
    eapply SpinAlgB.rzb_msteps; [exact Hh | exact Hlazy | exact R2 |]. subst mem2.
    rewrite wbytes_cmem_win by region_side.
    carry G2 A2 (2:reg) B2. carry G2 A8 (8:reg) B8. carry G2 A9 (9:reg) B9. carry G2 A10 (10:reg) B10.
    carry G2 A3 (3:reg) B3.
    change (SpinAlgB.rzb SEGS scfg (mkCfg ?st model) K) with (RZ st).
    eapply (p3_run Sv48 inp mbase ENT sp brk rdraw) with (G := RZ); try side Hva Hve HG.
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
    eapply (tls_c1 Sv48 inp mbase ENT sp brk rdraw J0) with (G := RZ) (s1v := getr regs3 9) (tid := Z_to_bv 64 0); try side Hva Hve HG.
    intros regs4a; intros.
    eapply (tls_c2 Sv48 inp mbase ENT sp brk rdraw J0) with (G := RZ) (tid := Z_to_bv 64 0); try side Hva Hve HG.
    intros regs4b; intros.
    eapply (tls_c3 Sv48 inp mbase ENT sp brk rdraw J0) with (G := RZ) (tid := Z_to_bv 64 0); try side Hva Hve HG.
    intros regs4c; intros.
    eapply (tls_c4 Sv48 inp mbase ENT sp brk rdraw J0) with (G := RZ) (tid := Z_to_bv 64 0); try side Hva Hve HG.
    intros regs4; intros.
    unfold RZ at 1.
    eapply (RefNodesB.rz_set_tid_b SEGS scfg regs4 (0x4b138 : word) _ (seg_rom SEGS) model K W_4b138 F_4b138 E_4b138);
      [exact Hh | exact Hlazy | assumption | exact Ht0 |].
    intros tid Htid.
    replace (v_addi (0x4b138 : word) 4) with (0x4b13c : word) by (apply bv_eq; reflexivity).
    set (model' := with_tid tid model).
    assert (Hh' : m_halted model' = None) by (unfold model'; rewrite with_tid_halted; exact Hh).
    assert (Hlazy' : m_vm_lazy model' = []) by (unfold model'; rewrite with_tid_lazy; exact Hlazy).
    set (RZ' := fun st : machine_state => SpinAlgB.rzb rsegs scfg (mkCfg st model') K).
    assert (HG' : bwd rsegs RZ') by (apply bwd_rz_b; [exact Hh' | exact Hlazy']).
    change (SpinAlgB.rzb SEGS scfg (mkCfg ?st model') K) with (RZ' st).
    eapply (tls_c5 Sv48 inp mbase ENT sp brk rdraw J0) with (G := RZ'); try side Hva Hve HG'.
    intros regs5; intros.
    eapply (fin_c6 Sv48 inp mbase ENT sp brk rdraw J0) with (G := RZ'); try side Hva Hve HG'.
    intros regs6; intros.
    eapply (fin_c7 Sv48 inp mbase ENT sp brk rdraw J0) with (G := RZ'); try side Hva Hve HG'.
    intros regs7; intros.
    eapply (fin_c8 Sv48 inp mbase ENT sp brk rdraw J0) with (G := RZ'); try side Hva Hve HG'.
    intros regs8; intros.
    eapply (fin_c9 Sv48 inp mbase ENT sp brk rdraw J0) with (G := RZ'); try side Hva Hve HG'.
    intros regs9 M1 M2 M3 M4 M8 M9 M10 M11 M12 M18 M19 M20 M21 M22 M23 M24 M25 M26 M27 G9.
    unfold RZ'. apply (HK tid regs9). { exact Htid. }
    split; try assumption.
    - intros r Hr. cbn [In] in Hr.
      repeat (destruct Hr as [<-|Hr]; [assumption|]). destruct Hr.
    - exists brk, (Src0Startup.J_main inp mbase ENT sp rdraw J0 (getr regs3 9)).
      split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
      split; [exact Hvl|]. split; [exact Hlau|].
      split; [|split; [exists J0, (getr regs3 9); reflexivity|]].
      + unfold Src0Startup.J_main, J_tls, J_aux, J_lsm. repeat apply wfJ_wbytes. exact HJ0.
      + unfold Src0Startup.J_main, J_tls, D_main, D_fd, D_ssp, D_tls, D_tlsA, D_tlsB. reflexivity.
  Qed.
End Assembly.
Theorem ref_startup_b : forall scfg sp brk mbase (rdraw : EntryDraw) lim inp K,
  valid_sp sp -> valid_brk rsegs brk -> valid_argv (in_argv inp) -> valid_envp (in_envp inp) ->
  valid_launch inp -> entry_launch_ok_va Sv48 (mkEntry sp brk mbase rdraw) inp ->
  (forall tid regs mem,
     (0 < bv_unsigned tid < 2^22)%Z ->
     Src0Startup.main_entry inp mbase (0x1ffac : word) sp (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp) rdraw tid regs mem ->
     SpinAlgB.rzb rsegs scfg (mkCfg (mkst regs (0x200f8 : word) mem (seg_rom rsegs))
                           (with_tid tid (with_vdso (Vdso.vdso_run_init (ed_vdso rdraw))
                              (init_model (segments_reserved rsegs) brk mbase sp lim inp)))) K) ->
  SpinAlgB.rzb rsegs scfg (init_config rsegs rpc rph sp brk mbase rdraw lim inp) K.
Proof.
  intros scfg sp brk mbase rdraw lim inp K Hsp Hbrk Hva Hve Hvl Hlau HK.
  exact (ref_startup_sec_b scfg inp mbase sp brk rdraw Hva Hve Hsp Hvl Hlau lim K HK).
Qed.
End FPX_1.
