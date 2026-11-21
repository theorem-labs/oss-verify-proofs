(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from RefStartup.v: the R-typed declarations restated over the budget carrier, with twin modules imported last. *)
(* Modified by Theorem Labs, 2026-11: for LPS 727298f3, the budget start-up follows RefStartup.v's new assembly: the launch input lays out the stack block, the zero window is stack_zero below the launch's stack window, and the hand-off model carries the launch's vDSO draw. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.coturn.FuzzStunClient.images Require Import Plain.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib Require Import Amb.
From LinuxProcessSemantics.LinuxProcessSem Require Vdso.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import ShapeAlg Nodes RefNodes FileSim StartupTac ArgvEnv RefLayout.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib Require Import RefNodesX RefImg RefStartupDefs RefStartup1 RefMemset RefStartup2 RefStartup3 RefStartup4 Ref_code_13894_14104 Ref_code_1b104_1c2fc.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib Require Import Ref_code_1b598_1b848.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import WalkFast.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import WalkFastK.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import WalkFastS.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import WalkFastM.
Import ListNotations.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib Require Import RefStartup.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.BudgetWit Require Import RefNodesXB Rzb.

Unset Lia Cache.
Unset Nia Cache.
Unset Nra Cache.
Unset Lia Cache.
Unset Nia Cache.
Unset Nra Cache.
#[local] Ltac OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common.WalkTac.gres ::= gres_fast.
#[local] Ltac OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common.WalkTac.vnorm ::= vnorm_fast.
#[local] Ltac OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common.StepTac.step_simpl ::= step_simpl_fast.
#[local] Ltac OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common.RefMemcpyLib.not_kept ::= not_kept_fast.
#[local] Ltac OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common.StartupTac.in_list ::= in_list_fast.
#[local] Ltac OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common.StartupTac.peel ::= peel_fast.
#[local] Ltac OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common.StoreOk.store_ok_peel ::= store_ok_peel_fast.
#[local] Existing Instance PropExec.fx0.
Open Scope bv_scope.
Local Notation rsegs := Plain.M.loaded_segments (only parsing).
Local Notation rpc := Plain.M.init_pc (only parsing).
Local Notation rph := Plain.M.phdrs (only parsing).
Lemma bwd_rz_b : forall segs model K,
  m_halted model = None -> m_vm_lazy model = [] ->
  bwd segs (fun st => Rzb.rzb segs (mkCfg st model) K).
Proof.
  intros segs model K Hh Hlazy st st' Hms Hst'. eapply Rzb.rzb_msteps; eassumption.
Qed.
(* LPS 727298f3: this file is RefStartup.v's assembly over the budget carrier [Rzb.rzb].
   In that assembly the launch's own input lays out the stack block ([cmem_init] takes
   [inp mbase RPH ENT sp brk rdraw Hlau]), the zero window below sp is
   [stack_zero (stack_window_lo (in_kernel inp) mbase rdraw)], the hand-off model carries
   the launch's vDSO draw, and [main_entry] is a record over [inp].  Mirrored step for
   step from RefStartup.ref_startup_sec (RefStartup.v:87-234), with [realizes] replaced
   by [Rzb.rzb], [rz_msteps] by [Rzb.rzb_msteps], [bwd_rz] by [bwd_rz_b] and [rz_set_tid]
   by [RefNodesXB.rzb_set_tid].  Nothing else differs, and the record it hands off is
   RefStartup's own, not a copy. *)
Section Assembly.
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
Local Notation ENT := (0x13894 : word) (only parsing).

Lemma Hlo : (0x7fff80000000 <= bv_unsigned sp)%Z.
Proof. destruct Hvsp as [H _]. exact H. Qed.
Lemma Hhi : (bv_unsigned sp <= 0x800000000000)%Z.
Proof. destruct Hvsp as [_ [H _]]. exact H. Qed.
Lemma Hal : (bv_unsigned sp mod 16 = 0)%Z.
Proof. destruct Hvsp as [_ [_ H]]. exact H. Qed.

(** the launch's zero window below [sp] *)
Let J0 : word -> option byte := stack_zero (stack_window_lo (in_kernel inp) mbase rdraw).

Lemma HJ0 : wfJ sp J0.
Proof. exact (wfJ_stack_zero inp sp brk mbase rdraw Hvl Hlau). Qed.

Ltac side_std :=
    first [ exact Hva | exact Hve | exact Hlo | exact Hhi | exact Hal | exact HJ0
          | match goal with H : bwd _ ?G |- bwd _ ?G => exact H end
          | (unfold J1, J_lsm; repeat apply wfJ_wbytes; exact HJ0)
          | lazymatch goal with |- getr _ _ = _ =>
              gres; first [ assumption | reflexivity
                          | match goal with H : getr ?rs ?n = _ |- getr ?rs ?n = _ =>
                              rewrite H; unfold envp_w, envp_ptr, argv_w, pn_w, argc_w;
                              first [reflexivity | f_equal; lia | bveq] end
                          | match goal with H : forall r : reg, In r _ -> getr ?rs r = _ |- getr ?rs _ = _ =>
                              apply H; in_list end ] end ].

Theorem ref_startup_sec_b : forall lim K,
    (forall tid regs mem,
       (0 < bv_unsigned tid < 2^22)%Z ->
       RefStartup.main_entry inp mbase ENT sp argv envp (in_uid inp) (in_hwcap inp) rdraw tid regs mem ->
       Rzb.rzb rsegs (mkCfg (mkst regs (0x139e0 : word) mem (seg_rom rsegs))
                             (with_tid tid (with_vdso (Vdso.vdso_run_init (ed_vdso rdraw))
                                (init_model (segments_reserved rsegs) brk mbase sp lim inp)))) K) ->
    Rzb.rzb rsegs (init_config rsegs rpc rph sp brk mbase rdraw lim inp) K.
  Proof.
    intros lim K HK.
    pose proof Hlo as Hlo'. pose proof Hhi as Hhi'. pose proof Hal as Hal'.
    pose proof (u64_range sp) as Hsp.
    unfold init_config. cbn [cfg_ms cfg_model].
    set (model := with_vdso (Vdso.vdso_run_init (ed_vdso rdraw)) (init_model (segments_reserved rsegs) brk mbase sp lim inp)).
    assert (Hh : m_halted model = None) by reflexivity.
    assert (Hlazy : m_vm_lazy model = []) by reflexivity.
    assert (Ht0 : m_tid model = None) by reflexivity.
    set (RZ := fun st : machine_state => Rzb.rzb rsegs (mkCfg st model) K).
    assert (HG : bwd rsegs RZ) by (apply bwd_rz_b; [exact Hh | exact Hlazy]).
    rewrite init_mkst.
    replace (Z_to_bv 64 (Z.of_N Plain.M.init_pc)) with (0x13894 : word) by (apply bv_eq; reflexivity).
    rewrite (cmem_init inp mbase RPH ENT sp brk rdraw Hlau). fold (regs_init sp). fold J0.
    destruct (p1_run Sv48 inp mbase ENT sp brk rdraw Hva Hve Hvl Hlau Hlo' Hhi' Hal' (seg_rom SEGS) J0 HJ0)
      as [regs1 (R1 & A1 & A2 & A3 & A4 & A8 & A9 & A10 & A11 & A12 & A18 & Az)].
    eapply Rzb.rzb_msteps; [exact Hh | exact Hlazy | exact R1 |].
    assert (A1' : getr regs1 1 = (0x1b2a4 : word)) by (rewrite A1; apply bv_eq; reflexivity).
    destruct (memset304_run regs1 (cmem sp (wrap_mem inp mbase RPH ENT sp rdraw) (J1 inp sp J0) (fun _ => None))
                (seg_rom SEGS) (Z_to_bv 64 (bv_unsigned sp - 368)) (0x1b2a4 : word) A1')
      as [regs2 [mem2 (R2 & M2 & G2)]].
    { unfold ret_ok. apply bv_eq. vm_compute. reflexivity. }
    { exact A10. } { exact A11. } { exact A12. }
    { rewrite u_Z2bv by lia. rewrite <- Zminus_mod_idemp_l.
      replace (bv_unsigned sp mod 8)%Z with 0%Z; [reflexivity|].
      symmetry. rewrite <- (Z.mod_mod_divide _ 16 8) by (exists 2%Z; reflexivity). rewrite Hal'. reflexivity. }
    { rewrite u_Z2bv by lia. lia. }
    { apply store_ok_cmem_win; [unfold J1; repeat apply wfJ_wbytes; exact HJ0 | region_side | region_side]. }
    eapply Rzb.rzb_msteps; [exact Hh | exact Hlazy | exact R2 |]. subst mem2.
    rewrite wbytes_cmem_win by region_side.
    carry G2 A2 (2:reg) B2. carry G2 A8 (8:reg) B8. carry G2 A9 (9:reg) B9. carry G2 A10 (10:reg) B10.
    carry G2 A3 (3:reg) B3.
    assert (Bz : forall r : reg, In r [19; 20; 21; 22; 23; 24; 25; 26; 27]%list -> getr regs2 r = Z_to_bv 64 0).
    { intros r Hr. rewrite (G2 r); [apply Az; cbn [In] in Hr |- *; tauto|].
      clear -Hr; cbn [In] in Hr; intros HH; cbn [In memset_clob] in HH;
        repeat (destruct Hr as [<-|Hr]; [repeat (destruct HH as [HH|HH]; [apply bv_eq in HH; cbv in HH; discriminate HH|]); exact HH |]); exact Hr. }
    change (Rzb.rzb SEGS (mkCfg ?st model) K) with (RZ st).
    eapply (p3_run Sv48 inp mbase ENT sp brk rdraw Hva Hve Hvl Hlau Hlo' Hhi' Hal')
      with (G := RZ) (regs := regs2) (Jf := J1 inp sp J0) (rom := seg_rom SEGS);
      try solve [side_std].
    intros regs3 C1 C2 C8 C9 C10 C18 G3.
    carry G3 B3 (3:reg) C3.
    assert (Cz : forall r : reg, In r [19; 20; 21; 22; 23; 24; 25; 26; 27]%list -> getr regs3 r = Z_to_bv 64 0).
    { intros r Hr. rewrite (G3 r); [apply Bz; exact Hr|].
      clear -Hr; cbn [In] in Hr; intros HH; cbn [In] in HH;
        repeat (destruct Hr as [<-|Hr]; [repeat (destruct HH as [HH|HH]; [apply bv_eq in HH; cbv in HH; discriminate HH|]); exact HH |]); exact Hr. }
    change (J1 inp sp J0) with (J_lsm inp sp J0).
    eapply (p4_run Sv48 inp mbase ENT sp brk rdraw Hva Hve Hlo' Hhi' Hal')
      with (G := RZ) (regs := regs3) (Jf := J_lsm inp sp J0) (rom := seg_rom SEGS) (s1v := getr regs3 9);
      try solve [side_std].
    intros regs4 D2 D3 D4 D10 D11 D17 D18 D22 D23 D24 D25 D26 D27.
    unfold RZ at 1.
    eapply (RefNodesXB.rzb_set_tid SEGS regs4 (0x1b7f4 : word) _ (seg_rom SEGS) model K W_1b7f4 F_1b7f4 E_1b7f4);
      [exact Hh | exact Hlazy | exact D17 | exact Ht0 |].
    intros tid Htid.
    replace (v_addi (0x1b7f4 : word) 4) with (0x1b7f8 : word) by (apply bv_eq; reflexivity).
    set (model' := with_tid tid model).
    assert (Hh' : m_halted model' = None) by (unfold model'; rewrite with_tid_halted; exact Hh).
    assert (Hlazy' : m_vm_lazy model' = []) by (unfold model'; rewrite with_tid_lazy; exact Hlazy).
    set (RZ' := fun st : machine_state => Rzb.rzb rsegs (mkCfg st model') K).
    assert (HG' : bwd rsegs RZ') by (apply bwd_rz_b; [exact Hh' | exact Hlazy']).
    change (Rzb.rzb SEGS (mkCfg ?st model') K) with (RZ' st).
    eapply (p5_run Sv48 inp mbase ENT sp brk rdraw Hva Hve Hvl Hlau Hlo' Hhi' Hal')
      with (G := RZ') (regs := regupd regs4 10 tid) (Jb := J0) (rom := seg_rom SEGS)
           (s1v := getr regs3 9) (tid := tid);
      try solve [side_std].
    intros regs5 M1 M2 M3 M4 M8 M9 M10 M11 M12 M18 M19 M20 M21 M22 M23 M24 M25 M26 M27.
    unfold RZ'. apply (HK tid regs5).
    { unfold PID_MAX_ENVELOPE in Htid. exact Htid. }
    constructor; [exact M1 | exact M2 | exact M3 | exact M4 | exact M8 | exact M9 | exact M10
                 | exact M11 | exact M12 | exact M18 | exact M19 | | ].
    - intros r Hr. cbn [In] in Hr.
      repeat (destruct Hr as [<-|Hr]; [assumption|]). destruct Hr.
    - exists brk, (RefStartup.J_main inp mbase ENT sp rdraw J0 (getr regs3 9)).
      split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
      split; [exact Hvl|]. split; [exact Hlau|].
      split; [|split; [exists J0, (getr regs3 9); reflexivity | reflexivity]].
      unfold RefStartup.J_main, J5, J_tls, J_aux, J_rseq, J_lsm.
      destruct (kb_rseq (in_kernel inp)); cbv iota; repeat apply wfJ_wbytes; exact HJ0.
  Qed.
End Assembly.

Theorem ref_startup_b : forall sp brk mbase rdraw lim inp K,
  valid_sp sp -> valid_argv (in_argv inp) -> valid_envp (in_envp inp) ->
  valid_launch inp -> entry_launch_ok_va Sv48 (mkEntry sp brk mbase rdraw) inp ->
  (forall tid regs mem,
     (0 < bv_unsigned tid < 2^22)%Z ->
     RefStartup.main_entry inp mbase (0x13894 : word) sp (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp) rdraw tid regs mem ->
     Rzb.rzb rsegs (mkCfg (mkst regs (0x139e0 : word) mem (seg_rom rsegs))
                           (with_tid tid (with_vdso (Vdso.vdso_run_init (ed_vdso rdraw))
                              (init_model (segments_reserved rsegs) brk mbase sp lim inp)))) K) ->
  Rzb.rzb rsegs (init_config rsegs rpc rph sp brk mbase rdraw lim inp) K.
Proof.
  intros sp brk mbase rdraw lim inp K Hsp Hva Hve Hvl Hlau HK.
  exact (ref_startup_sec_b inp mbase sp brk rdraw Hva Hve Hsp Hvl Hlau lim K HK).
Qed.
