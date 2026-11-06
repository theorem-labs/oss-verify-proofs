(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
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
Record main_entry (sp0 : word) (av ev : list (list byte)) (uid tid : word) (hw : word) (rdraw : EntryDraw)
       (regs : bvmap 5 word) (mem : word -> option byte) : Prop := {
  me_ra  : getr regs 1 = Z_to_bv 64 0x5265c;
  me_sp  : getr regs 2 = Z_to_bv 64 (bv_unsigned sp0 - 48);
  me_gp  : getr regs 3 = Z_to_bv 64 0x10800;
  me_tp  : getr regs 4 = Z_to_bv 64 0x77990;
  me_s0  : getr regs 8 = Z_to_bv 64 (bv_unsigned sp0 + 8);
  me_s1  : getr regs 9 = argcN av;
  me_a0  : getr regs 10 = argcN av;
  me_a1  : getr regs 11 = Z_to_bv 64 (bv_unsigned sp0 + 8);
  me_a2  : getr regs 12 = Z_to_bv 64 (bv_unsigned sp0 + 16 + 8 * Z.of_nat (length av));
  me_s2  : getr regs 18 = Z_to_bv 64 0x228cc;
  me_s3  : getr regs 19 = Z_to_bv 64 (bv_unsigned sp0 + 16 + 8 * Z.of_nat (length av));
  me_szero : forall r : reg, In r [20; 21; 22; 23; 24; 25; 26; 27]%list -> getr regs r = Z_to_bv 64 0;
  me_mem : exists (J : word -> option byte),
             wfJ sp0 J /\ mem = cmem sp0 (wrap_mem RPH sp0 av ev uid hw rdraw) J (D_main sp0 av ev hw rdraw tid)
}.

Section Assembly.
  Variable sp : word.
  Variables argv envp : list (list byte).
  Variable uid : word.
  Variable hw : word.
  Variable rdraw : EntryDraw.
  Hypothesis Hva : valid_argv argv.
  Hypothesis Hve : valid_envp envp.
  Hypothesis Hvsp : valid_sp sp.

  (* [comment removed for export] *)
  Variable P : machine_state -> Model -> Prop.
  Hypothesis P_bwd : forall model, m_halted model = None -> m_vm_lazy model = [] ->
    bwd SEGS (fun st => P st model).
  (* [comment removed for export] *)
  Hypothesis P_set_tid : forall regs (pc : word) mem model w,
    fetch_word SEGS pc = Some w -> is_ecall w = true ->
    m_halted model = None -> m_vm_lazy model = [] ->
    getr regs 17 = Z_to_bv 64 96 ->
    m_tid model = None ->
    (forall tid, (0 < bv_unsigned tid < PID_MAX_ENVELOPE)%Z ->
       P (mkst (regupd regs 10 tid) (v_addi pc 4) mem (seg_rom SEGS)) (with_tid tid model)) ->
    P (mkst regs pc mem (seg_rom SEGS)) model.

  #[using="Hvsp"] Lemma Hlo : (0x7fff80000000 <= bv_unsigned sp)%Z.
  Proof. LiaFast.lf_pins (fun (Hvsp : LiaFast.U) => LiaFast.u0). destruct Hvsp as [H _]. exact H. Qed.
  #[using="Hvsp"] Lemma Hhi : (bv_unsigned sp <= 0x800000000000)%Z.
  Proof. LiaFast.lf_pins (fun (Hvsp : LiaFast.U) => LiaFast.u0). destruct Hvsp as [_ [H _]]. exact H. Qed.
  #[using="Hvsp"] Lemma Hal : (bv_unsigned sp mod 16 = 0)%Z.
  Proof. LiaFast.lf_pins (fun (Hvsp : LiaFast.U) => LiaFast.u0). destruct Hvsp as [_ [_ H]]. exact H. Qed.

  Let J0 : word -> option byte := fun _ => Some (Z_to_bv 8 0).

  (* [comment removed for export] *)
  Ltac side Hva Hve HG :=
    first [ exact Hva | exact Hve | exact Hlo | exact Hhi | exact Hal | exact HG
          | apply wfJ_const
          | lazymatch goal with |- getr _ _ = _ =>
              gres; first [ assumption | reflexivity | bveq
                          | match goal with H : getr ?rs ?n = _ |- getr ?rs ?n = _ =>
                              rewrite H; unfold envp_w, envp_ptr, argv_w, pn_w, argc_w;
                              first [reflexivity | f_equal; lia | bveq] end ] end
          | idtac ].

  #[using="Hva Hve Hvsp P_bwd P_set_tid J0"] Theorem ref_startup_sec : forall (model : Model) (argvI envpI : list (list byte)),
    m_halted model = None -> m_vm_lazy model = [] -> m_tid model = None ->
    (forall tid regs mem,
       (0 < bv_unsigned tid < PID_MAX_ENVELOPE)%Z ->
       main_entry sp argv envp uid tid hw rdraw regs mem ->
       P (mkst regs (0x228cc : word) mem (seg_rom rsegs)) (with_tid tid model)) ->
    P (mkst (regs_init sp) (0x22780 : word) (wrap_mem RPH sp argv envp uid hw rdraw) (seg_rom rsegs)) model.
  Proof. LiaFast.lf_pins (fun (Hva Hve Hvsp P_bwd P_set_tid J0 : LiaFast.U) => LiaFast.u0).
    intros model argvI envpI Hh Hlazy Ht0 HK.
    pose proof Hlo as Hlo'. pose proof Hhi as Hhi'. pose proof Hal as Hal'.
    pose proof (u64_range sp) as Hsp.
    set (RZ := fun st : machine_state => P st model).
    assert (HG : bwd rsegs RZ) by (apply P_bwd; [exact Hh | exact Hlazy]).
    rewrite cmem_init.
    (* [comment removed for export] *)
    destruct (p1_run sp argv envp uid hw rdraw Hva Hve Hlo' Hhi' Hal' (seg_rom SEGS) J0 (wfJ_const sp _))
      as [regs1 (R1 & A1 & A2 & A3 & A4 & A8 & A9 & A10 & A11 & A12 & A18 & Az)].
    eapply HG; [exact R1|].
    (* [comment removed for export] *)
    assert (A1' : getr regs1 1 = (0x5236c : word)) by (rewrite A1; apply bv_eq; reflexivity).
    destruct (memset304_run regs1 (cmem sp (wrap_mem RPH sp argv envp uid hw rdraw) (J1 sp argv J0) (fun _ => None))
                (seg_rom SEGS) (Z_to_bv 64 (bv_unsigned sp - 368)) (0x5236c : word) A1')
      as [regs2 [mem2 (R2 & M2 & G2)]].
    { unfold ret_ok. apply bv_eq. vm_compute. reflexivity. }
    { exact A10. } { exact A11. } { exact A12. }
    { rewrite u_Z2bv by lia. rewrite <- Zminus_mod_idemp_l.
      replace (bv_unsigned sp mod 8)%Z with 0%Z; [reflexivity|].
      symmetry. rewrite <- (Z.mod_mod_divide _ 16 8) by (exists 2%Z; reflexivity). rewrite Hal'. reflexivity. }
    { rewrite u_Z2bv by lia. lia. }
    { apply store_ok_cmem_win; [unfold J1; repeat apply wfJ_wbytes; apply wfJ_const | region_side | region_side]. }
    eapply HG; [exact R2|]. subst mem2.
    rewrite wbytes_cmem_win by region_side.
    (* [comment removed for export] *)
    carry G2 A2 (2:reg) B2. carry G2 A8 (8:reg) B8. carry G2 A9 (9:reg) B9. carry G2 A10 (10:reg) B10.
    carry G2 A3 (3:reg) B3.
    change (P ?st model) with (RZ st).
    eapply (p3_run sp argv envp uid hw rdraw) with (G := RZ); try side Hva Hve HG.
    { unfold J1; repeat apply wfJ_wbytes; apply wfJ_const. }
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
    change (J1 sp argv J0) with (J_lsm sp argv J0).
    eapply (tls_c1 sp J0 argv envp uid hw rdraw) with (G := RZ) (s1v := getr regs3 9) (tid := Z_to_bv 64 0); try side Hva Hve HG.
    intros regs4a; intros.
    eapply (tls_c2 sp J0 argv envp uid hw rdraw) with (G := RZ) (tid := Z_to_bv 64 0); try side Hva Hve HG.
    intros regs4b; intros.
    eapply (tls_c3 sp J0 argv envp uid hw rdraw) with (G := RZ) (tid := Z_to_bv 64 0); try side Hva Hve HG.
    intros regs4c; intros.
    eapply (tls_c4 sp J0 argv envp uid hw rdraw) with (G := RZ) (tid := Z_to_bv 64 0); try side Hva Hve HG.
    intros regs4; intros.
    (* [comment removed for export] *)
    unfold RZ at 1.
    eapply (P_set_tid regs4 (0x528bc : word) _ model W_528bc F_528bc E_528bc);
      [exact Hh | exact Hlazy | assumption | exact Ht0 |].
    intros tid Htid.
    replace (v_addi (0x528bc : word) 4) with (0x528c0 : word) by (apply bv_eq; reflexivity).
    set (model' := with_tid tid model).
    assert (Hh' : m_halted model' = None) by (unfold model'; rewrite with_tid_halted; exact Hh).
    assert (Hlazy' : m_vm_lazy model' = []) by (unfold model'; rewrite with_tid_lazy; exact Hlazy).
    set (RZ' := fun st : machine_state => P st model').
    assert (HG' : bwd rsegs RZ') by (apply P_bwd; [exact Hh' | exact Hlazy']).
    change (P ?st model') with (RZ' st).
    eapply (tls_c5 sp J0 argv envp uid hw rdraw) with (G := RZ'); try side Hva Hve HG'.
    intros regs5; intros.
    eapply (fin_c6 sp J0 argv envp uid hw rdraw) with (G := RZ'); try side Hva Hve HG'.
    intros regs6; intros.
    eapply (fin_c7 sp J0 argv envp uid hw rdraw) with (G := RZ'); try side Hva Hve HG'.
    intros regs7; intros.
    eapply (fin_c8 sp J0 argv envp uid hw rdraw) with (G := RZ'); try side Hva Hve HG'.
    intros regs8 P1 P2 P3 P4 P8 P9 P18 P19 P20 P21 P22 P23 P24 P25 P26 P27 AG8.
    (* [comment removed for export] *)
    lazymatch goal with |- RZ' (mkst _ _ (cmem _ _ ?J8 _) _) =>
      assert (WF8 : wfJ sp J8) by (unfold J_aux, J_lsm; repeat apply wfJ_wbytes; apply wfJ_const);
      assert (R56 : rdn SEGS J8 (Z_to_bv 64 (bv_unsigned sp - 56)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 337484)))
        by (unfold J_aux, J_lsm; peel; apply rdn_wbytes_hit8; unorm; lia);
      assert (R64 : rdn SEGS J8 (Z_to_bv 64 (bv_unsigned sp - 64)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 (bv_unsigned sp + 8))))
        by (unfold J_aux, J_lsm; peel; apply rdn_wbytes_hit8; unorm; lia);
      assert (R72 : rdn SEGS J8 (Z_to_bv 64 (bv_unsigned sp - 72)) 8 = Some (word_to_le_bytes 8 (argc_w argv)))
        by (unfold J_aux, J_lsm; peel; apply rdn_wbytes_hit8; unorm; lia);
      eapply (fin_c9 sp argv envp uid hw rdraw) with (G := RZ') (J9 := J8) (s1v := Z_to_bv 64 0) (tid := tid);
        try side Hva Hve HG';
      [exact WF8 | exact R56 | exact R64 | exact R72 |]
    end.
    intros regs11 M1 M2 M3 M4 M8 M9 M10 M11 M12 M18 M19 M20 M21 M22 M23 M24 M25 M26 M27 G9.
    unfold RZ'. apply (HK tid regs11). { exact Htid. }
    split; try assumption.
    - intros r Hr. cbn [In] in Hr.
      repeat (destruct Hr as [<-|Hr]; [assumption|]). destruct Hr.
    - eexists. split.
      2: { unfold D_main, D_pre_ios, D_fd, D_ssp, D_tls, D_tlsA, D_tlsB. reflexivity. }
      repeat apply wfJ_wbytes. apply wfJ_const.
  Qed.
End Assembly.

(* [comment removed for export] *)
Theorem ub_startup : forall (P : machine_state -> Model -> Prop),
  (forall model, m_halted model = None -> m_vm_lazy model = [] -> bwd SEGS (fun st => P st model)) ->
  (forall regs (pc : word) mem model w,
    fetch_word SEGS pc = Some w -> is_ecall w = true ->
    m_halted model = None -> m_vm_lazy model = [] ->
    getr regs 17 = Z_to_bv 64 96 -> m_tid model = None ->
    (forall tid, (0 < bv_unsigned tid < PID_MAX_ENVELOPE)%Z ->
       P (mkst (regupd regs 10 tid) (v_addi pc 4) mem (seg_rom SEGS)) (with_tid tid model)) ->
    P (mkst regs pc mem (seg_rom SEGS)) model) ->
  forall sp brk mbase rnd lim inp,
  valid_sp sp -> valid_argv (in_argv inp) -> valid_envp (in_envp inp) ->
  (forall tid regs mem,
     (0 < bv_unsigned tid < PID_MAX_ENVELOPE)%Z ->
     main_entry sp (in_argv inp) (in_envp inp) (in_uid inp) tid (in_hwcap inp) rnd regs mem ->
     P (mkst regs (0x228cc : word) mem (seg_rom rsegs))
       (with_tid tid (init_model (segments_reserved rsegs) brk mbase sp lim inp))) ->
  P (cfg_ms (init_config rsegs rpc rph sp brk mbase rnd lim inp))
    (cfg_model (init_config rsegs rpc rph sp brk mbase rnd lim inp)).
Proof.
  intros P P_bwd P_set_tid sp brk mbase rnd lim inp Hsp Hva Hve HK.
  unfold init_config. cbn [cfg_ms cfg_model].
  rewrite init_mkst.
  replace (Z_to_bv 64 (Z.of_N Ubsan.M.init_pc)) with (0x22780 : word) by (apply bv_eq; reflexivity).
  fold (regs_init sp).
  apply (ref_startup_sec sp (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp) rnd Hva Hve Hsp P P_bwd P_set_tid
           (init_model (segments_reserved rsegs) brk mbase sp lim inp) (in_argv inp) (in_envp inp));
    [reflexivity | reflexivity | reflexivity | exact HK].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section Consumers.
  Variable sp0 : word.
  Variables av ev : list (list byte).
  Variables uid tid : word.
  Variable hw : word.
  Variable rdraw : EntryDraw.
  Variable regs : bvmap 5 word.
  Variable mem : word -> option byte.
  Hypothesis ME : main_entry sp0 av ev uid tid hw rdraw regs mem.

  (* [comment removed for export] *)
  #[using="tid regs ME"] Lemma main_entry_rdn_above : forall segs (a : word) n,
    (bv_unsigned sp0 <= bv_unsigned a)%Z ->
    (bv_unsigned a + Z.of_nat n <= 2^64)%Z ->
    rdn segs mem a n = rdn segs (wrap_mem RPH sp0 av ev uid hw rdraw) a n.
  Proof. LiaFast.lf_pins (fun (tid regs ME : LiaFast.U) => LiaFast.u0).
    intros segs a n Ha Hn. destruct (me_mem _ _ _ _ _ _ _ _ _ ME) as (J & HJ & ->).
    apply rdn_cmem_above; assumption.
  Qed.

  #[using="tid regs ME"] Lemma main_entry_mem_above : forall (a : word),
    (bv_unsigned sp0 <= bv_unsigned a)%Z -> mem a = wrap_mem RPH sp0 av ev uid hw rdraw a.
  Proof. LiaFast.lf_pins (fun (tid regs ME : LiaFast.U) => LiaFast.u0).
    intros a Ha. destruct (me_mem _ _ _ _ _ _ _ _ _ ME) as (J & HJ & ->).
    apply cmem_at_above. exact Ha.
  Qed.

  (* [comment removed for export] *)
  #[using="av ev uid tid hw rdraw regs ME"] Lemma main_entry_win_mapped : forall (a : word),
    (bv_unsigned sp0 - stack_max_size <= bv_unsigned a < bv_unsigned sp0)%Z -> mem a <> None.
  Proof. LiaFast.lf_pins (fun (av ev uid tid hw rdraw regs ME : LiaFast.U) => LiaFast.u0).
    intros a Ha. destruct (me_mem _ _ _ _ _ _ _ _ _ ME) as (J & HJ & ->).
    rewrite cmem_at_win by (unfold in_win, win_lo; lia). apply HJ. unfold in_win, win_lo. lia.
  Qed.

  #[using="av ev uid tid hw rdraw regs ME"] Lemma main_entry_store_ok_win : forall segs (a : word) n,
    (bv_unsigned sp0 - stack_max_size <= bv_unsigned a)%Z ->
    (bv_unsigned a + Z.of_nat n <= bv_unsigned sp0)%Z ->
    store_ok segs mem a n = true.
  Proof. LiaFast.lf_pins (fun (av ev uid tid hw rdraw regs ME : LiaFast.U) => LiaFast.u0).
    intros segs a n Hlo Hhi. destruct (me_mem _ _ _ _ _ _ _ _ _ ME) as (J & HJ & ->).
    apply store_ok_cmem_win; [exact HJ | unfold win_lo; lia | lia].
  Qed.

  (* [comment removed for export] *)
  #[using="uid regs ME"] Lemma main_entry_mem_data : forall (a : word),
    (bv_unsigned a < bv_unsigned sp0 - stack_max_size)%Z ->
    mem a = D_main sp0 av ev hw rdraw tid a.
  Proof. LiaFast.lf_pins (fun (uid regs ME : LiaFast.U) => LiaFast.u0).
    intros a Ha. destruct (me_mem _ _ _ _ _ _ _ _ _ ME) as (J & HJ & ->).
    apply cmem_at_data. unfold win_lo. exact Ha.
  Qed.

  #[using="uid regs ME"] Lemma main_entry_rdn_data : forall segs (a : word) n,
    (bv_unsigned a + Z.of_nat n <= bv_unsigned sp0 - stack_max_size)%Z ->
    rdn segs mem a n = rdn segs (D_main sp0 av ev hw rdraw tid) a n.
  Proof. LiaFast.lf_pins (fun (uid regs ME : LiaFast.U) => LiaFast.u0).
    intros segs a n Ha. destruct (me_mem _ _ _ _ _ _ _ _ _ ME) as (J & HJ & ->).
    apply rdn_cmem_data. unfold win_lo. exact Ha.
  Qed.
End Consumers.
