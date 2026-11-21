(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (the launch's ProcInput; the launch premises valid_launch and entry_launch_ok_va; the run's segment list run_segments; the vDSO run state; the launch's reservations with the vDSO pair). *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run Vdso.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.fast_float.from_chars.images Require Import Ubsan.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require StartupTac.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require RefLayout.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require RefLayout.
Import OSSVerify.Proofs.fast_float.from_chars.lib.Common.StartupTac OSSVerify.Proofs.fast_float.from_chars.lib.Common.RefLayout.ArgvEnv OSSVerify.Proofs.fast_float.from_chars.lib.Common.RefLayout.
From OSSVerify.Proofs.fast_float.from_chars.lib Require Import UbImg UbStartupDefs UbStartup1 UbMemset UbStartup2 UbStartup3 UbStartup4 Ub_code_22780_228cc Ub_code_5233c_52dd8 Ub_code_60628_60720 Ub_code_61234_61240 Ub_code_memcpy.
From OSSVerify.Proofs.fast_float.from_chars.lib Require Import Ub_code_52660_52910.
Import ListNotations.
Open Scope bv_scope.
Local Instance clf_fx : PropExec.FPState := PropExec.fx0.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Abbreviation SEGS := Ubsan.M.loaded_segments.
Abbreviation RPH := Ubsan.M.phdrs.
Local Notation rsegs := Ubsan.M.loaded_segments (only parsing).
Local Notation rpc := Ubsan.M.init_pc (only parsing).
Local Notation rph := Ubsan.M.phdrs (only parsing).

(* [comment removed for export] *)
Lemma with_tid_halted : forall t m, m_halted (with_tid t m) = m_halted m.
Proof. intros t m. destruct m; reflexivity. Qed.
Lemma with_tid_lazy : forall t m, m_vm_lazy (with_tid t m) = m_vm_lazy m.
Proof. intros t m. destruct m; reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Record main_entry (inp : ProcInput) (mbase entry sp0 : word) (rdraw : EntryDraw) (tid : word)
       (regs : bvmap 5 word) (mem : word -> option byte) : Prop := {
  me_ra  : getr regs 1 = Z_to_bv 64 0x5265c;
  me_sp  : getr regs 2 = Z_to_bv 64 (bv_unsigned sp0 - 48);
  me_gp  : getr regs 3 = Z_to_bv 64 0x10800;
  me_tp  : getr regs 4 = Z_to_bv 64 0x77990;
  me_s0  : getr regs 8 = Z_to_bv 64 (bv_unsigned sp0 + 8);
  me_s1  : getr regs 9 = argcN inp;
  me_a0  : getr regs 10 = argcN inp;
  me_a1  : getr regs 11 = Z_to_bv 64 (bv_unsigned sp0 + 8);
  me_a2  : getr regs 12 = Z_to_bv 64 (bv_unsigned sp0 + 16 + 8 * Z.of_nat (length (in_argv inp)));
  me_s2  : getr regs 18 = Z_to_bv 64 0x228cc;
  me_s3  : getr regs 19 = Z_to_bv 64 (bv_unsigned sp0 + 16 + 8 * Z.of_nat (length (in_argv inp)));
  me_szero : forall r : reg, In r [20; 21; 22; 23; 24; 25; 26; 27]%list -> getr regs r = Z_to_bv 64 0;
  me_mem : exists (J : word -> option byte),
             wfJ sp0 J /\ mem = cmem sp0 (wrap_mem inp mbase RPH entry sp0 rdraw) J (D_main inp sp0 rdraw tid)
}.

(* The run's segment list: the binary's own segments and the vDSO pair. *)
Local Notation VS inp sp mbase := (run_segments Ubsan.M.loaded_segments inp sp mbase) (only parsing).
(* The entry point the auxv's AT_ENTRY carries: the image's own [init_pc]. *)
Local Notation ENT := (0x22780 : word) (only parsing).

Section Assembly.
  Variable inp : ProcInput.
  Variable mbase : word.
  Variable sp brk : word.
  Variable rdraw : EntryDraw.
  Local Notation argv := (in_argv inp) (only parsing).
  Local Notation envp := (in_envp inp) (only parsing).
  Hypothesis Hva : valid_argv (in_argv inp).
  Hypothesis Hve : valid_envp (in_envp inp).
  Hypothesis Hvl : valid_launch inp.
  Hypothesis Hlau : entry_launch_ok_va Sv48 (mkEntry sp brk mbase rdraw) inp.
  Hypothesis Hvsp : valid_sp sp.

  (* [comment removed for export] *)
  Variable P : machine_state -> Model -> Prop.
  Hypothesis P_bwd : forall model, m_halted model = None -> m_vm_lazy model = [] ->
    bwd SEGS (fun st => P st model).
  (* [comment removed for export] *)
  Hypothesis P_set_tid : forall regs (pc : word) mem rom model w,
    fetch_word SEGS pc = Some w -> is_ecall w = true ->
    m_halted model = None -> m_vm_lazy model = [] ->
    getr regs 17 = Z_to_bv 64 96 ->
    m_tid model = None ->
    (forall tid, (0 < bv_unsigned tid < PID_MAX_ENVELOPE)%Z ->
       P (mkst (regupd regs 10 tid) (v_addi pc 4) mem rom) (with_tid tid model)) ->
    P (mkst regs pc mem rom) model.

  Lemma Hlo : (0x7fff80000000 <= bv_unsigned sp)%Z.
  Proof. destruct Hvsp as [H _]. exact H. Qed.
  Lemma Hhi : (bv_unsigned sp <= 0x800000000000)%Z.
  Proof. destruct Hvsp as [_ [H _]]. exact H. Qed.
  Lemma Hal : (bv_unsigned sp mod 16 = 0)%Z.
  Proof. destruct Hvsp as [_ [_ H]]. exact H. Qed.

  Let J0 : word -> option byte := stack_zero (stack_window_lo (in_kernel inp) mbase rdraw).

  Lemma HJ0 : wfJ sp J0.
  Proof. exact (wfJ_stack_zero inp sp brk mbase rdraw Hvl Hlau). Qed.

  (* [comment removed for export] *)
  Ltac side HG :=
    first [ exact Hva | exact Hve | exact Hvl | exact Hlau
          | exact Hlo | exact Hhi | exact Hal | exact HG
          | exact HJ0
          | lazymatch goal with |- getr _ _ = _ =>
              gres; first [ assumption | reflexivity | bveq
                          | match goal with H : getr ?rs ?n = _ |- getr ?rs ?n = _ =>
                              rewrite H; unfold envp_w, envp_ptr, argv_w, pn_w, argc_w;
                              first [reflexivity | f_equal; lia | bveq] end ] end
          | idtac ].

  Theorem ref_startup_sec : forall (model : Model),
    m_halted model = None -> m_vm_lazy model = [] -> m_tid model = None ->
    (forall tid regs mem,
       (0 < bv_unsigned tid < PID_MAX_ENVELOPE)%Z ->
       main_entry inp mbase ENT sp rdraw tid regs mem ->
       P (mkst regs (0x228cc : word) mem (seg_rom (VS inp sp mbase))) (with_tid tid model)) ->
    P (mkst (regs_init sp) (0x22780 : word) (wrap_mem inp mbase RPH ENT sp rdraw) (seg_rom (VS inp sp mbase))) model.
  Proof.
    intros model Hh Hlazy Ht0 HK.
    pose proof Hlo as Hlo'. pose proof Hhi as Hhi'. pose proof Hal as Hal'.
    pose proof (u64_range sp) as Hsp.
    set (RZ := fun st : machine_state => P st model).
    assert (HG : bwd rsegs RZ) by (apply P_bwd; [exact Hh | exact Hlazy]).
    rewrite (cmem_init inp mbase RPH ENT sp brk rdraw Hlau).
    (* [comment removed for export] *)
    destruct (p1_run sp Sv48 inp mbase ENT brk rdraw Hva Hve Hvl Hlau Hlo' Hhi' Hal'
                (seg_rom (VS inp sp mbase)) J0 HJ0)
      as [regs1 (R1 & A1 & A2 & A3 & A4 & A8 & A9 & A10 & A11 & A12 & A18 & Az)].
    eapply HG; [exact R1|].
    (* [comment removed for export] *)
    assert (A1' : getr regs1 1 = (0x5236c : word)) by (rewrite A1; apply bv_eq; reflexivity).
    destruct (memset304_run regs1 (cmem sp (wrap_mem inp mbase RPH ENT sp rdraw) (J1 sp inp J0) (fun _ => None))
                (seg_rom (VS inp sp mbase)) (Z_to_bv 64 (bv_unsigned sp - 368)) (0x5236c : word) A1')
      as [regs2 [mem2 (R2 & M2 & G2)]].
    { unfold ret_ok. apply bv_eq. vm_compute. reflexivity. }
    { exact A10. } { exact A11. } { exact A12. }
    { rewrite u_Z2bv by lia. rewrite <- Zminus_mod_idemp_l.
      replace (bv_unsigned sp mod 8)%Z with 0%Z; [reflexivity|].
      symmetry. rewrite <- (Z.mod_mod_divide _ 16 8) by (exists 2%Z; reflexivity). rewrite Hal'. reflexivity. }
    { rewrite u_Z2bv by lia. lia. }
    { apply store_ok_cmem_win; [unfold J1; repeat apply wfJ_wbytes; exact HJ0 | region_side | region_side]. }
    eapply HG; [exact R2|]. subst mem2.
    rewrite wbytes_cmem_win by region_side.
    (* [comment removed for export] *)
    carry G2 A2 (2:reg) B2. carry G2 A8 (8:reg) B8. carry G2 A9 (9:reg) B9. carry G2 A10 (10:reg) B10.
    carry G2 A3 (3:reg) B3.
    change (P ?st model) with (RZ st).
    eapply p3_run with (G := RZ); try side HG.
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
    (* [comment removed for export] *)
    change (J1 sp inp J0) with (J_lsm inp sp J0).
    eapply tls_c1 with (G := RZ) (s1v := getr regs3 9) (tid := Z_to_bv 64 0); try side HG.
    intros regs4a; intros.
    eapply tls_c2 with (G := RZ) (tid := Z_to_bv 64 0); try side HG.
    intros regs4b; intros.
    eapply tls_c3 with (G := RZ) (tid := Z_to_bv 64 0); try side HG.
    intros regs4c; intros.
    eapply tls_c4 with (G := RZ) (tid := Z_to_bv 64 0); try side HG.
    intros regs4; intros.
    (* [comment removed for export] *)
    unfold RZ at 1.
    eapply (P_set_tid regs4 (0x528bc : word) _ _ model W_528bc F_528bc E_528bc);
      [exact Hh | exact Hlazy | assumption | exact Ht0 |].
    intros tid Htid.
    replace (v_addi (0x528bc : word) 4) with (0x528c0 : word) by (apply bv_eq; reflexivity).
    set (model' := with_tid tid model).
    assert (Hh' : m_halted model' = None) by (unfold model'; rewrite with_tid_halted; exact Hh).
    assert (Hlazy' : m_vm_lazy model' = []) by (unfold model'; rewrite with_tid_lazy; exact Hlazy).
    set (RZ' := fun st : machine_state => P st model').
    assert (HG' : bwd rsegs RZ') by (apply P_bwd; [exact Hh' | exact Hlazy']).
    change (P ?st model') with (RZ' st).
    eapply tls_c5 with (G := RZ'); try side HG'.
    intros regs5; intros.
    eapply fin_c6 with (G := RZ'); try side HG'.
    intros regs6; intros.
    eapply fin_c7 with (G := RZ'); try side HG'.
    intros regs7; intros.
    eapply fin_c8 with (G := RZ'); try side HG'.
    intros regs8 P1 P2 P3 P4 P8 P9 P18 P19 P20 P21 P22 P23 P24 P25 P26 P27 AG8.
    (* [comment removed for export] *)
    lazymatch goal with |- RZ' (mkst _ _ (cmem _ _ ?J8 _) _) =>
      assert (WF8 : wfJ sp J8) by (unfold J_aux, J_aux0, J_lsm; repeat apply wfJ_wbytes; exact HJ0);
      assert (R56 : rdn SEGS J8 (Z_to_bv 64 (bv_unsigned sp - 56)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 337484)))
        by (unfold J_aux, J_aux0, J_lsm; peel; apply rdn_wbytes_hit8; unorm; lia);
      assert (R64 : rdn SEGS J8 (Z_to_bv 64 (bv_unsigned sp - 64)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 (bv_unsigned sp + 8))))
        by (unfold J_aux, J_aux0, J_lsm; peel; apply rdn_wbytes_hit8; unorm; lia);
      assert (R72 : rdn SEGS J8 (Z_to_bv 64 (bv_unsigned sp - 72)) 8 = Some (word_to_le_bytes 8 (argc_w inp)))
        by (unfold J_aux, J_aux0, J_lsm; peel; apply rdn_wbytes_hit8; unorm; lia);
      eapply fin_c9 with (G := RZ') (J9 := J8) (s1v := Z_to_bv 64 0) (tid := tid);
        try side HG';
      [exact WF8 | exact R56 | exact R64 | exact R72 |]
    end.
    intros regs11 M1 M2 M3 M4 M8 M9 M10 M11 M12 M18 M19 M20 M21 M22 M23 M24 M25 M26 M27 G9.
    unfold RZ'. apply (HK tid regs11). { exact Htid. }
    split; try assumption.
    - intros r Hr. cbn [In] in Hr.
      repeat (destruct Hr as [<-|Hr]; [assumption|]). destruct Hr.
    - eexists. split.
      2: { unfold D_main, D_pre_ios, D_fd, D_ssp, D_tls, D_tlsA, D_tlsB. reflexivity. }
      repeat apply wfJ_wbytes. exact HJ0.
  Qed.
End Assembly.

(* [comment removed for export] *)
Theorem ub_startup : forall sp brk mbase rnd lim inp (P : machine_state -> Model -> Prop),
  (forall model, m_halted model = None -> m_vm_lazy model = [] -> bwd SEGS (fun st => P st model)) ->
  (forall regs (pc : word) mem rom model w,
    fetch_word SEGS pc = Some w -> is_ecall w = true ->
    m_halted model = None -> m_vm_lazy model = [] ->
    getr regs 17 = Z_to_bv 64 96 -> m_tid model = None ->
    (forall tid, (0 < bv_unsigned tid < PID_MAX_ENVELOPE)%Z ->
       P (mkst (regupd regs 10 tid) (v_addi pc 4) mem rom) (with_tid tid model)) ->
    P (mkst regs pc mem rom) model) ->
  valid_sp sp -> valid_argv (in_argv inp) -> valid_envp (in_envp inp) ->
  valid_launch inp -> entry_launch_ok_va Sv48 (mkEntry sp brk mbase rnd) inp ->
  (forall tid regs mem,
     (0 < bv_unsigned tid < PID_MAX_ENVELOPE)%Z ->
     main_entry inp mbase ENT sp rnd tid regs mem ->
     P (mkst regs (0x228cc : word) mem (seg_rom (VS inp sp mbase)))
       (with_tid tid (cfg_model (init_config (VS inp sp mbase) rpc rph sp brk mbase rnd lim inp)))) ->
  P (cfg_ms (init_config (VS inp sp mbase) rpc rph sp brk mbase rnd lim inp))
    (cfg_model (init_config (VS inp sp mbase) rpc rph sp brk mbase rnd lim inp)).
Proof.
  intros sp brk mbase rnd lim inp P P_bwd P_set_tid Hsp Hva Hve Hvl Hlau HK.
  unfold init_config at 1. cbn [cfg_ms].
  rewrite init_mkst.
  replace (Z_to_bv 64 (Z.of_N Ubsan.M.init_pc)) with (0x22780 : word) by (apply bv_eq; reflexivity).
  fold (regs_init sp).
  apply (ref_startup_sec inp mbase sp brk rnd Hva Hve Hvl Hlau Hsp P P_bwd P_set_tid
           (cfg_model (init_config (VS inp sp mbase) rpc rph sp brk mbase rnd lim inp)));
    [reflexivity | reflexivity | reflexivity | exact HK].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section Consumers.
  Variable sp0 : word.
  Variable inp : ProcInput.
  Variables mbase entry tid : word.
  Variable rdraw : EntryDraw.
  Variable regs : bvmap 5 word.
  Variable mem : word -> option byte.
  Hypothesis ME : main_entry inp mbase entry sp0 rdraw tid regs mem.

  (* [comment removed for export] *)
  Lemma main_entry_rdn_above : forall segs (a : word) n,
    (bv_unsigned sp0 <= bv_unsigned a)%Z ->
    (bv_unsigned a + Z.of_nat n <= 2^64)%Z ->
    rdn segs mem a n = rdn segs (wrap_mem inp mbase RPH entry sp0 rdraw) a n.
  Proof.
    intros segs a n Ha Hn. destruct (me_mem _ _ _ _ _ _ _ _ ME) as (J & HJ & ->).
    apply rdn_cmem_above; assumption.
  Qed.

  Lemma main_entry_mem_above : forall (a : word),
    (bv_unsigned sp0 <= bv_unsigned a)%Z -> mem a = wrap_mem inp mbase RPH entry sp0 rdraw a.
  Proof.
    intros a Ha. destruct (me_mem _ _ _ _ _ _ _ _ ME) as (J & HJ & ->).
    apply cmem_at_above. exact Ha.
  Qed.

  (* [comment removed for export] *)
  Lemma main_entry_win_mapped : forall (a : word),
    (* LPS 08b1429: the window the launch guarantees is [wok_lo, sp0), not the whole 8 MiB *)
    (wok_lo sp0 <= bv_unsigned a < bv_unsigned sp0)%Z -> mem a <> None.
  Proof.
    intros a Ha. destruct (me_mem _ _ _ _ _ _ _ _ ME) as (J & HJ & ->).
    rewrite cmem_at_win by (unfold in_win; lia). apply HJ. unfold in_win. lia.
  Qed.

  Lemma main_entry_store_ok_win : forall segs (a : word) n,
    (* LPS 08b1429: J is defined only on the launch window [wok_lo, sp0) *)
    (wok_lo sp0 <= bv_unsigned a)%Z ->
    (bv_unsigned a + Z.of_nat n <= bv_unsigned sp0)%Z ->
    store_ok segs mem a n = true.
  Proof.
    intros segs a n Hlo Hhi. destruct (me_mem _ _ _ _ _ _ _ _ ME) as (J & HJ & ->).
    apply store_ok_cmem_win; [exact HJ | exact Hlo | exact Hhi].
  Qed.

  (* [comment removed for export] *)
  Lemma main_entry_mem_data : forall (a : word),
    (bv_unsigned a < bv_unsigned sp0 - stack_max_size)%Z ->
    mem a = D_main inp sp0 rdraw tid a.
  Proof.
    intros a Ha. destruct (me_mem _ _ _ _ _ _ _ _ ME) as (J & HJ & ->).
    apply cmem_at_data. unfold win_lo. exact Ha.
  Qed.

  Lemma main_entry_rdn_data : forall segs (a : word) n,
    (bv_unsigned a + Z.of_nat n <= bv_unsigned sp0 - stack_max_size)%Z ->
    rdn segs mem a n = rdn segs (D_main inp sp0 rdraw tid) a n.
  Proof.
    intros segs a n Ha. destruct (me_mem _ _ _ _ _ _ _ _ ME) as (J & HJ & ->).
    apply rdn_cmem_data. unfold win_lo. exact Ha.
  Qed.
End Consumers.
