(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OssFuzzTheorems.openssl.hashtable.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import
  ShapeAlg Nodes RefNodes RefNodesEx ExistsRun FileSim
  StartupTac ArgvEnv RefLayout HUImg HUStartupDefs
  HUStartup1 HUMemset HUStartup2 HUStartup3 HUStartup4 HU_code_26b000_26c000 HU_code_dc000_dd000 HU_code_dd000_de000.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import ConeCfg.   (* [comment removed for export] *)
Import ListNotations.
Import ConeCfg.
Open Scope bv_scope.

Abbreviation SEGS := Ubsan.M.loaded_segments.
Abbreviation RPH := Ubsan.M.phdrs.
Local Notation rsegs := Ubsan.M.loaded_segments (only parsing).
Local Notation rpc := Ubsan.M.init_pc (only parsing).
Local Notation rph := Ubsan.M.phdrs (only parsing).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition J_main (sp0 : word) (av ev : list (list byte)) (uid hw : word) (s1v : word) : word -> option byte :=
  let J6 := J_tls sp0 (J_aux sp0 av ev uid hw (J_lsm sp0 av (fun _ => Some (Z_to_bv 8 0))))
              (Z_to_bv 64 0x2b0f4c) (pn_w sp0 av ev) s1v (Z_to_bv 64 0x351d78)
              (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) in
  wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes J6
    (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 0x2b0f54)))   (* [comment removed for export] *)
    (Z_to_bv 64 (bv_unsigned sp0 - 8)) (word_to_le_bytes 8 (Z_to_bv 64 0)))           (* [comment removed for export] *)
    (Z_to_bv 64 (bv_unsigned sp0 - 16)) (word_to_le_bytes 8 (Z_to_bv 64 0)))          (* [comment removed for export] *)
    (Z_to_bv 64 (bv_unsigned sp0 - 24)) (word_to_le_bytes 8 (Z_to_bv 64 0)))          (* [comment removed for export] *)
    (Z_to_bv 64 (bv_unsigned sp0 - 32)) (word_to_le_bytes 8 (Z_to_bv 64 0)))          (* [comment removed for export] *)
    (Z_to_bv 64 (bv_unsigned sp0 - 40)) (word_to_le_bytes 8 (Z_to_bv 64 0)))          (* [comment removed for export] *)
    (Z_to_bv 64 (bv_unsigned sp0 - 56)) (word_to_le_bytes 8 (Z_to_bv 64 0x2b1148)))    (* [comment removed for export] *)
    (Z_to_bv 64 (bv_unsigned sp0 - 64)) (word_to_le_bytes 8 (argv_w sp0)))             (* [comment removed for export] *)
    (Z_to_bv 64 (bv_unsigned sp0 - 72)) (word_to_le_bytes 8 (argc_w av)))              (* [comment removed for export] *)
    (Z_to_bv 64 (bv_unsigned sp0 - 88)) (word_to_le_bytes 8 (Z_to_bv 64 0x2b1098)))    (* [comment removed for export] *)
    (Z_to_bv 64 (bv_unsigned sp0 - 96)) (word_to_le_bytes 8 (Z_to_bv 64 0x2c1730)).    (* [comment removed for export] *)

(* [comment removed for export] *)
Record main_entry (sp0 : word) (av ev : list (list byte)) (uid hw : word) (rdraw : EntryDraw) (tid : word)
       (regs : bvmap 5 word) (mem : word -> option byte) : Prop := {
  me_ra  : getr regs 1 = Z_to_bv 64 0x2b1158;
  me_sp  : getr regs 2 = Z_to_bv 64 (bv_unsigned sp0 - 48);
  me_gp  : getr regs 3 = Z_to_bv 64 0x10800;
  me_tp  : getr regs 4 = Z_to_bv 64 0x331ae8;
  me_s0  : getr regs 8 = Z_to_bv 64 (bv_unsigned sp0 + 8);
  me_s1  : getr regs 9 = argcN av;
  me_a0  : getr regs 10 = argcN av;
  me_a1  : getr regs 11 = Z_to_bv 64 (bv_unsigned sp0 + 8);
  me_a2  : getr regs 12 = Z_to_bv 64 (bv_unsigned sp0 + 16 + 8 * Z.of_nat (length av));
  me_s2  : getr regs 18 = Z_to_bv 64 0xe1984;
  me_s3  : getr regs 19 = Z_to_bv 64 (bv_unsigned sp0 + 16 + 8 * Z.of_nat (length av));
  me_szero : forall r : reg, In r [20; 21; 22; 23; 24; 25; 26; 27]%list -> getr regs r = Z_to_bv 64 0;
  me_mem : exists (J : word -> option byte) (s1v : word),
             wfJ sp0 J /\ J = J_main sp0 av ev uid hw s1v
             /\ mem = cmem sp0 (wrap_mem RPH sp0 av ev uid hw rdraw) J (D_main sp0 av ev hw rdraw tid)
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
  Variable P : config -> Prop.
  Hypothesis HPbwd : forall model, m_halted model = None -> m_vm_lazy model = [] ->
    bwd rsegs (fun st => P (mkCfg st model)).
  Hypothesis HPtid : forall regs (pc : word) mem rom model w,
    fetch_word rsegs pc = Some w -> is_ecall w = true ->
    m_halted model = None -> m_vm_lazy model = [] ->
    getr regs 17 = Z_to_bv 64 96 ->
    m_tid model = None ->
    (forall tid, (0 < bv_unsigned tid < PID_MAX_ENVELOPE)%Z ->
       P (mkCfg (mkst (regupd regs 10 tid) (v_addi pc 4) mem rom) (with_tid tid model))) ->
    P (mkCfg (mkst regs pc mem rom) model).

  Lemma Hlo : (0x7fff80000000 <= bv_unsigned sp)%Z.
  Proof. destruct Hvsp as [H _]. exact H. Qed.
  Lemma Hhi : (bv_unsigned sp <= 0x800000000000)%Z.
  Proof. destruct Hvsp as [_ [H _]]. exact H. Qed.
  Lemma Hal : (bv_unsigned sp mod 16 = 0)%Z.
  Proof. destruct Hvsp as [_ [_ H]]. exact H. Qed.

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

  (* [comment removed for export] *)
  Theorem startup_gen : forall model,
    m_halted model = None -> m_vm_lazy model = [] -> m_tid model = None ->
    (forall tid, m_halted (with_tid tid model) = None) ->
    (forall tid, m_vm_lazy (with_tid tid model) = []) ->
    (forall tid regs mem,
       (0 < bv_unsigned tid < PID_MAX_ENVELOPE)%Z ->
       main_entry sp argv envp uid hw rdraw tid regs mem ->
       P (mkCfg (mkst regs (0xe1984 : word) mem (seg_rom rsegs)) (with_tid tid model))) ->
    P (mkCfg (mkst (regs_init sp) (0xe1830 : word) (wrap_mem RPH sp argv envp uid hw rdraw) (seg_rom rsegs)) model).
  Proof.
    intros model Hh Hlazy Ht0 Hh't Hlazy't HK.
    pose proof Hlo as Hlo'. pose proof Hhi as Hhi'. pose proof Hal as Hal'.
    pose proof (u64_range sp) as Hsp.
    set (RZ := fun st : machine_state => P (mkCfg st model)).
    assert (HG : bwd rsegs RZ) by (apply HPbwd; [exact Hh | exact Hlazy]).
    rewrite cmem_init.
    (* [comment removed for export] *)
    destruct (p1_run sp argv envp uid hw rdraw Hva Hve Hlo' Hhi' Hal' (seg_rom SEGS) J0 (wfJ_const sp _))
      as [regs1 (R1 & A1 & A2 & A3 & A4 & A8 & A9 & A10 & A11 & A12 & A18 & Az)].
    change (P (mkCfg ?st model)) with (RZ st).
    eapply HG; [exact R1|].
    (* [comment removed for export] *)
    assert (A1' : getr regs1 1 = (0x2b0e68 : word)) by (rewrite A1; apply bv_eq; reflexivity).
    destruct (memset304_run regs1 (cmem sp (wrap_mem RPH sp argv envp uid hw rdraw) (J1 sp argv J0) (fun _ => None))
                (seg_rom SEGS) (Z_to_bv 64 (bv_unsigned sp - 368)) (0x2b0e68 : word) A1')
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
    eapply (HPtid regs4 (0x2b1490 : word) _ (seg_rom SEGS) model W_26b8a4 F_26b8a4 E_26b8a4);
      [exact Hh | exact Hlazy | assumption | exact Ht0 |].
    intros tid Htid.
    replace (v_addi (0x2b1490 : word) 4) with (0x2b1494 : word) by (apply bv_eq; reflexivity).
    set (model' := with_tid tid model).
    assert (Hh' : m_halted model' = None) by (apply Hh't).
    assert (Hlazy' : m_vm_lazy model' = []) by (apply Hlazy't).
    set (RZ' := fun st : machine_state => P (mkCfg st model')).
    assert (HG' : bwd rsegs RZ') by (apply HPbwd; [exact Hh' | exact Hlazy']).
    change (P (mkCfg ?st model')) with (RZ' st).
    eapply (tls_c5 sp J0 argv envp uid hw rdraw) with (G := RZ'); try side Hva Hve HG'.
    intros regs5; intros.
    eapply (fin_c6 sp J0 argv envp uid hw rdraw) with (G := RZ'); try side Hva Hve HG'.
    intros regs6; intros.
    eapply (fin_c7 sp J0 argv envp uid hw rdraw) with (G := RZ'); try side Hva Hve HG'.
    intros regs7; intros.
    eapply (fin_c8 sp J0 argv envp uid hw rdraw) with (G := RZ'); try side Hva Hve HG'.
    intros regs8; intros.
    eapply (fin_c9 sp J0 argv envp uid hw rdraw) with (G := RZ'); try side Hva Hve HG'.
    intros regs9 M1 M2 M3 M4 M8 M9 M10 M11 M12 M18 M19 M20 M21 M22 M23 M24 M25 M26 M27 G9.
    unfold RZ'. apply (HK tid regs9). { exact Htid. }
    split; try assumption.
    - intros r Hr. cbn [In] in Hr.
      repeat (destruct Hr as [<-|Hr]; [assumption|]). destruct Hr.
    - eexists _, (getr regs3 9). split; [|split; [reflexivity|]].
      + unfold J_main, J_tls, J_aux, J_lsm. repeat apply wfJ_wbytes. apply wfJ_const.
      + unfold J_main, J_tls, D_main, D_fd, D_ssp, D_tls, D_tlsA, D_tlsB. reflexivity.
  Qed.
End Assembly.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma tid_range_22 : forall tid : word, (0 < bv_unsigned tid < PID_MAX_ENVELOPE)%Z -> (0 < bv_unsigned tid < 2^22)%Z.
Proof. intros tid H. unfold PID_MAX_ENVELOPE in H. exact H. Qed.

(* [comment removed for export] *)
Lemma bwd_rz : forall segs model K,
  m_halted model = None -> m_vm_lazy model = [] ->
  bwd segs (fun st => realizes segs (mkCfg st model) K).
Proof.
  intros segs model K Hh Hlazy st st' Hms Hst'. eapply rz_msteps; eassumption.
Qed.

(* [comment removed for export] *)
Theorem ref_startup : forall sp brk mbase rdraw lim inp K,
  valid_sp sp -> valid_brk rsegs brk -> valid_argv (in_argv inp) -> valid_envp (in_envp inp) ->
  (forall tid regs mem,
     (0 < bv_unsigned tid < 2^22)%Z ->
     main_entry sp (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp) rdraw tid regs mem ->
     realizes rsegs (mkCfg (mkst regs (0xe1984 : word) mem (seg_rom rsegs))
                           (with_tid tid (init_model (segments_reserved rsegs) brk mbase sp lim inp))) K) ->
  realizes rsegs (init_config rsegs rpc rph sp brk mbase rdraw lim inp) K.
Proof.
  intros sp brk mbase rdraw lim inp K Hsp Hbrk Hva Hve HK.
  unfold init_config. rewrite init_mkst. fold (regs_init sp).
  replace (Z_to_bv 64 (Z.of_N Ubsan.M.init_pc)) with (0xe1830 : word) by (apply bv_eq; reflexivity).
  apply (startup_gen sp (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp) rdraw Hva Hve Hsp
           (fun c => realizes rsegs c K)).
  - intros model Hh Hlazy. apply bwd_rz; assumption.
  - intros regs pc mem rom model w HF HE Hh Hlazy H17 Ht Hk. eapply rz_set_tid; eassumption.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - intros tid. reflexivity.
  - intros tid. reflexivity.
  - intros tid regs mem Htid ME. apply HK; [apply tid_range_22; exact Htid | exact ME].
Qed.

(* [comment removed for export] *)
Theorem ref_startup_fwd : forall sp brk mbase rdraw lim inp,
  valid_sp sp -> valid_argv (in_argv inp) -> valid_envp (in_envp inp) ->
  exists tid regs mem,
    (0 < bv_unsigned tid < 2^22)%Z /\
    main_entry sp (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp) rdraw tid regs mem /\
    reach rsegs (init_config rsegs rpc rph sp brk mbase rdraw lim inp)
                (mkCfg (mkst regs (0xe1984 : word) mem (seg_rom rsegs))
                       (with_tid tid (init_model (segments_reserved rsegs) brk mbase sp lim inp))).
Proof.
  intros sp brk mbase rdraw lim inp Hsp Hva Hve.
  set (model0 := init_model (segments_reserved rsegs) brk mbase sp lim inp).
  set (Post := fun c' : config => exists tid regs mem,
          (0 < bv_unsigned tid < 2^22)%Z /\
          main_entry sp (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp) rdraw tid regs mem /\
          c' = mkCfg (mkst regs (0xe1984 : word) mem (seg_rom rsegs)) (with_tid tid model0)).
  assert (HP : (fun c => exists c', reach rsegs c c' /\ Post c')
                 (init_config rsegs rpc rph sp brk mbase rdraw lim inp)).
  { unfold init_config. rewrite init_mkst. fold (regs_init sp).
    replace (Z_to_bv 64 (Z.of_N Ubsan.M.init_pc)) with (0xe1830 : word) by (apply bv_eq; reflexivity).
    apply (startup_gen sp (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp) rdraw Hva Hve Hsp
             (fun c => exists c', reach rsegs c c' /\ Post c')).
    - intros model Hh Hlazy st st' Hms (c' & Hr & HQ). exists c'. split; [| exact HQ].
      eapply reach_trans; [eapply reach_msteps; eassumption | exact Hr].
    - intros regs pc mem rom model w HF HE Hh Hlazy H17 Ht Hk.
      destruct (Hk (Z_to_bv 64 1) one_tid_ok) as (c' & Hr & HQ). exists c'. split; [| exact HQ].
      eapply reach_trans; [| exact Hr]. eapply ex_set_tid_1; eassumption.
    - reflexivity.
    - reflexivity.
    - reflexivity.
    - intros tid. reflexivity.
    - intros tid. reflexivity.
    - intros tid regs mem Htid ME. exists (mkCfg (mkst regs (0xe1984 : word) mem (seg_rom rsegs)) (with_tid tid model0)).
      split; [apply reach_refl |]. exists tid, regs, mem. split; [apply tid_range_22; exact Htid | split; [exact ME | reflexivity]]. }
  destruct HP as (c' & Hr & (tid & regs & mem & Htid & ME & ->)).
  exists tid, regs, mem. split; [exact Htid | split; [exact ME | exact Hr]].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section Consumers.
  Variable sp0 : word.
  Variables av ev : list (list byte).
  Variables uid hw : word.
  Variable rdraw : EntryDraw.
  Variable tid : word.
  Variable regs : bvmap 5 word.
  Variable mem : word -> option byte.
  Hypothesis ME : main_entry sp0 av ev uid hw rdraw tid regs mem.

  (* [comment removed for export] *)
  Lemma main_entry_rdn_above : forall segs (a : word) n,
    (bv_unsigned sp0 <= bv_unsigned a)%Z ->
    (bv_unsigned a + Z.of_nat n <= 2^64)%Z ->
    rdn segs mem a n = rdn segs (wrap_mem RPH sp0 av ev uid hw rdraw) a n.
  Proof.
    intros segs a n Ha Hn. destruct (me_mem _ _ _ _ _ _ _ _ _ ME) as (J & s1v & HJ & _ & ->).
    apply rdn_cmem_above; assumption.
  Qed.

  Lemma main_entry_mem_above : forall (a : word),
    (bv_unsigned sp0 <= bv_unsigned a)%Z -> mem a = wrap_mem RPH sp0 av ev uid hw rdraw a.
  Proof.
    intros a Ha. destruct (me_mem _ _ _ _ _ _ _ _ _ ME) as (J & s1v & HJ & _ & ->).
    apply cmem_at_above. exact Ha.
  Qed.

  (* [comment removed for export] *)
  Lemma main_entry_win_mapped : forall (a : word),
    (bv_unsigned sp0 - stack_max_size <= bv_unsigned a < bv_unsigned sp0)%Z -> mem a <> None.
  Proof.
    intros a Ha. destruct (me_mem _ _ _ _ _ _ _ _ _ ME) as (J & s1v & HJ & _ & ->).
    rewrite cmem_at_win by (unfold in_win, win_lo; lia). apply HJ. unfold in_win, win_lo. lia.
  Qed.

  Lemma main_entry_store_ok_win : forall segs (a : word) n,
    (bv_unsigned sp0 - stack_max_size <= bv_unsigned a)%Z ->
    (bv_unsigned a + Z.of_nat n <= bv_unsigned sp0)%Z ->
    store_ok segs mem a n = true.
  Proof.
    intros segs a n Hlo Hhi. destruct (me_mem _ _ _ _ _ _ _ _ _ ME) as (J & s1v & HJ & _ & ->).
    apply store_ok_cmem_win; [exact HJ | unfold win_lo; lia | lia].
  Qed.

  (* [comment removed for export] *)
  Lemma main_entry_mem_data : forall (a : word),
    (bv_unsigned a < bv_unsigned sp0 - stack_max_size)%Z ->
    mem a = D_main sp0 av ev hw rdraw tid a.
  Proof.
    intros a Ha. destruct (me_mem _ _ _ _ _ _ _ _ _ ME) as (J & s1v & HJ & _ & ->).
    apply cmem_at_data. unfold win_lo. exact Ha.
  Qed.

  Lemma main_entry_rdn_data : forall segs (a : word) n,
    (bv_unsigned a + Z.of_nat n <= bv_unsigned sp0 - stack_max_size)%Z ->
    rdn segs mem a n = rdn segs (D_main sp0 av ev hw rdraw tid) a n.
  Proof.
    intros segs a n Ha. destruct (me_mem _ _ _ _ _ _ _ _ _ ME) as (J & s1v & HJ & _ & ->).
    apply rdn_cmem_data. unfold win_lo. exact Ha.
  Qed.
End Consumers.
