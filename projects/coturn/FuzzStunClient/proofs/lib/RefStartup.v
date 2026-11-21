(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: for LPS 727298f3, the start-up assembly lays out the stack from the launch input, mmap base and entry point, the zero window is stack_zero below the launch's stack window, main_entry is restated over the launch input (main_entry_launch), and the hand-off model carries the launch's vDSO draw. *)

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
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import WalkFast.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import WalkFastK.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import WalkFastS.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import WalkFastM.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Ltac OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common.WalkTac.gres ::= gres_fast.
#[local] Ltac OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common.WalkTac.vnorm ::= vnorm_fast.
#[local] Ltac OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common.StepTac.step_simpl ::= step_simpl_fast.
#[local] Ltac OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common.RefMemcpyLib.not_kept ::= not_kept_fast.
#[local] Ltac OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common.StartupTac.in_list ::= in_list_fast.
#[local] Ltac OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common.StartupTac.peel ::= peel_fast.
#[local] Ltac OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common.StoreOk.store_ok_peel ::= store_ok_peel_fast.
(* [comment removed for export] *)
#[local] Existing Instance PropExec.fx0.  (* [comment removed for export] *)
Import ListNotations.
Open Scope bv_scope.

Abbreviation SEGS := Plain.M.loaded_segments.
Abbreviation RPH := Plain.M.phdrs.
(* [comment removed for export] *)
Local Notation rsegs := Plain.M.loaded_segments (only parsing).
Local Notation rpc := Plain.M.init_pc (only parsing).
Local Notation rph := Plain.M.phdrs (only parsing).

(* [comment removed for export] *)
Lemma bwd_rz : forall segs model K,
  m_halted model = None -> m_vm_lazy model = [] ->
  bwd segs (fun st => realizes segs (mkCfg st model) K).
Proof.
  intros segs model K Hh Hlazy st st' Hms Hst'. eapply rz_msteps; eassumption.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(** The window the start-up leaves behind: [RefStartup4.J5] over the launch's own zero window
    [stack_zero (stack_window_lo ..)] ([Run.init_machine_state]) and the start-up's s1 value. *)
Definition J_main (inp : ProcInput) (mbase entry sp0 : word) (rdraw : EntryDraw)
    (Jb : word -> option byte) (s1v : word) : word -> option byte :=
  J5 inp mbase entry sp0 rdraw Jb s1v.

(** The start-up's hand-off state.  At LPS 08b1429 the launch's own input [inp] (its kernel
    build, its exec file name, its gid), the mmap base and the entry point lay out the stack
    block, so [me_mem] names them; the argument, environment, uid and hwcap the consumers
    quantify over are its fields. *)
Record main_entry (inp : ProcInput) (mbase entry sp0 : word) (av ev : list (list byte))
       (uid hw : word) (rdraw : EntryDraw) (tid : word)
       (regs : bvmap 5 word) (mem : word -> option byte) : Prop := {
  me_ra  : getr regs 1 = Z_to_bv 64 0x1b594;
  me_sp  : getr regs 2 = Z_to_bv 64 (bv_unsigned sp0 - 48);
  me_gp  : getr regs 3 = Z_to_bv 64 0x10800;
  me_tp  : getr regs 4 = Z_to_bv 64 0x367b0;
  me_s0  : getr regs 8 = Z_to_bv 64 (bv_unsigned sp0 + 8);
  me_s1  : getr regs 9 = len_word av;
  me_a0  : getr regs 10 = len_word av;
  me_a1  : getr regs 11 = Z_to_bv 64 (bv_unsigned sp0 + 8);
  me_a2  : getr regs 12 = Z_to_bv 64 (bv_unsigned sp0 + 16 + 8 * Z.of_nat (length av));
  me_s2  : getr regs 18 = Z_to_bv 64 0x139e0;
  me_s3  : getr regs 19 = Z_to_bv 64 (bv_unsigned sp0 + 16 + 8 * Z.of_nat (length av));
  me_szero : forall r : reg, In r [20; 21; 22; 23; 24; 25; 26; 27]%list -> getr regs r = Z_to_bv 64 0;
  me_mem : exists (brk : word) (J : word -> option byte),
             in_argv inp = av /\ in_envp inp = ev /\ in_uid inp = uid /\ in_hwcap inp = hw
             /\ valid_launch inp /\ entry_launch_ok_va Sv48 (mkEntry sp0 brk mbase rdraw) inp
             /\ wfJ sp0 J /\ (exists (Jb : word -> option byte) (s1v : word), J = J_main inp mbase entry sp0 rdraw Jb s1v)
             /\ mem = cmem sp0 (wrap_mem inp mbase RPH entry sp0 rdraw) J (D_main inp sp0 rdraw tid)
}.

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
  (** the image's entry: [Run.init_machine_state]'s pc, and the auxv's AT_ENTRY *)
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

  (* [comment removed for export] *)
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

  Theorem ref_startup_sec : forall lim K,
    (forall tid regs mem,
       (0 < bv_unsigned tid < 2^22)%Z ->
       main_entry inp mbase ENT sp argv envp (in_uid inp) (in_hwcap inp) rdraw tid regs mem ->
       realizes rsegs (mkCfg (mkst regs (0x139e0 : word) mem (seg_rom rsegs))
                             (with_tid tid (with_vdso (Vdso.vdso_run_init (ed_vdso rdraw))
                                (init_model (segments_reserved rsegs) brk mbase sp lim inp)))) K) ->
    realizes rsegs (init_config rsegs rpc rph sp brk mbase rdraw lim inp) K.
  Proof.
    intros lim K HK.
    pose proof Hlo as Hlo'. pose proof Hhi as Hhi'. pose proof Hal as Hal'.
    pose proof (u64_range sp) as Hsp.
    unfold init_config. cbn [cfg_ms cfg_model].
    set (model := with_vdso (Vdso.vdso_run_init (ed_vdso rdraw)) (init_model (segments_reserved rsegs) brk mbase sp lim inp)).
    assert (Hh : m_halted model = None) by reflexivity.
    assert (Hlazy : m_vm_lazy model = []) by reflexivity.
    assert (Ht0 : m_tid model = None) by reflexivity.
    set (RZ := fun st : machine_state => realizes rsegs (mkCfg st model) K).
    assert (HG : bwd rsegs RZ) by (apply bwd_rz; [exact Hh | exact Hlazy]).
    rewrite init_mkst.
    replace (Z_to_bv 64 (Z.of_N Plain.M.init_pc)) with (0x13894 : word) by (apply bv_eq; reflexivity).
    rewrite (cmem_init inp mbase RPH ENT sp brk rdraw Hlau). fold (regs_init sp). fold J0.
    (* [comment removed for export] *)
    destruct (p1_run Sv48 inp mbase ENT sp brk rdraw Hva Hve Hvl Hlau Hlo' Hhi' Hal' (seg_rom SEGS) J0 HJ0)
      as [regs1 (R1 & A1 & A2 & A3 & A4 & A8 & A9 & A10 & A11 & A12 & A18 & Az)].
    eapply rz_msteps; [exact Hh | exact Hlazy | exact R1 |].
    (* [comment removed for export] *)
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
    eapply rz_msteps; [exact Hh | exact Hlazy | exact R2 |]. subst mem2.
    rewrite wbytes_cmem_win by region_side.
    carry G2 A2 (2:reg) B2. carry G2 A8 (8:reg) B8. carry G2 A9 (9:reg) B9. carry G2 A10 (10:reg) B10.
    carry G2 A3 (3:reg) B3.
    assert (Bz : forall r : reg, In r [19; 20; 21; 22; 23; 24; 25; 26; 27]%list -> getr regs2 r = Z_to_bv 64 0).
    { intros r Hr. rewrite (G2 r); [apply Az; cbn [In] in Hr |- *; tauto|].
      clear -Hr; cbn [In] in Hr; intros HH; cbn [In memset_clob] in HH;
        repeat (destruct Hr as [<-|Hr]; [repeat (destruct HH as [HH|HH]; [apply bv_eq in HH; cbv in HH; discriminate HH|]); exact HH |]); exact Hr. }
    (* [comment removed for export] *)
    change (realizes SEGS (mkCfg ?st model) K) with (RZ st).
    eapply (p3_run Sv48 inp mbase ENT sp brk rdraw Hva Hve Hvl Hlau Hlo' Hhi' Hal')
      with (G := RZ) (regs := regs2) (Jf := J1 inp sp J0) (rom := seg_rom SEGS);
      try solve [side_std].
    intros regs3 C1 C2 C8 C9 C10 C18 G3.
    carry G3 B3 (3:reg) C3.
    assert (Cz : forall r : reg, In r [19; 20; 21; 22; 23; 24; 25; 26; 27]%list -> getr regs3 r = Z_to_bv 64 0).
    { intros r Hr. rewrite (G3 r); [apply Bz; exact Hr|].
      clear -Hr; cbn [In] in Hr; intros HH; cbn [In] in HH;
        repeat (destruct Hr as [<-|Hr]; [repeat (destruct HH as [HH|HH]; [apply bv_eq in HH; cbv in HH; discriminate HH|]); exact HH |]); exact Hr. }
    (* [comment removed for export] *)
    change (J1 inp sp J0) with (J_lsm inp sp J0).
    eapply (p4_run Sv48 inp mbase ENT sp brk rdraw Hva Hve Hlo' Hhi' Hal')
      with (G := RZ) (regs := regs3) (Jf := J_lsm inp sp J0) (rom := seg_rom SEGS) (s1v := getr regs3 9);
      try solve [side_std].
    intros regs4 D2 D3 D4 D10 D11 D17 D18 D22 D23 D24 D25 D26 D27.
    (* [comment removed for export] *)
    unfold RZ at 1.
    eapply (rz_set_tid SEGS regs4 (0x1b7f4 : word) _ (seg_rom SEGS) model K W_1b7f4 F_1b7f4 E_1b7f4);
      [exact Hh | exact Hlazy | exact D17 | exact Ht0 |].
    intros tid Htid.
    replace (v_addi (0x1b7f4 : word) 4) with (0x1b7f8 : word) by (apply bv_eq; reflexivity).
    set (model' := with_tid tid model).
    assert (Hh' : m_halted model' = None) by (unfold model'; rewrite with_tid_halted; exact Hh).
    assert (Hlazy' : m_vm_lazy model' = []) by (unfold model'; rewrite with_tid_lazy; exact Hlazy).
    set (RZ' := fun st : machine_state => realizes rsegs (mkCfg st model') K).
    assert (HG' : bwd rsegs RZ') by (apply bwd_rz; [exact Hh' | exact Hlazy']).
    change (realizes SEGS (mkCfg ?st model') K) with (RZ' st).
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
    - exists brk, (J_main inp mbase ENT sp rdraw J0 (getr regs3 9)).
      split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
      split; [exact Hvl|]. split; [exact Hlau|].
      split; [|split; [exists J0, (getr regs3 9); reflexivity | reflexivity]].
      unfold J_main, J5, J_tls, J_aux, J_rseq, J_lsm.
      destruct (kb_rseq (in_kernel inp)); cbv iota; repeat apply wfJ_wbytes; exact HJ0.
  Qed.

End Assembly.

(* [comment removed for export] *)
Theorem ref_startup : forall sp brk mbase rdraw lim inp K,
  valid_sp sp -> valid_argv (in_argv inp) -> valid_envp (in_envp inp) ->
  valid_launch inp -> entry_launch_ok_va Sv48 (mkEntry sp brk mbase rdraw) inp ->
  (forall tid regs mem,
     (0 < bv_unsigned tid < 2^22)%Z ->
     main_entry inp mbase (0x13894 : word) sp (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp) rdraw tid regs mem ->
     realizes rsegs (mkCfg (mkst regs (0x139e0 : word) mem (seg_rom rsegs))
                           (with_tid tid (with_vdso (Vdso.vdso_run_init (ed_vdso rdraw))
                              (init_model (segments_reserved rsegs) brk mbase sp lim inp)))) K) ->
  realizes rsegs (init_config rsegs rpc rph sp brk mbase rdraw lim inp) K.
Proof.
  intros sp brk mbase rdraw lim inp K Hsp Hva Hve Hvl Hlau HK.
  exact (ref_startup_sec inp mbase sp brk rdraw Hva Hve Hsp Hvl Hlau lim K HK).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section Consumers.
  Variable inp : ProcInput.
  Variable mbase entry : word.
  Variable sp0 : word.
  Variables av ev : list (list byte).
  Variables uid hw : word.
  Variable rdraw : EntryDraw.
  Variable tid : word.
  Variable regs : bvmap 5 word.
  Variable mem : word -> option byte.
  Hypothesis ME : main_entry inp mbase entry sp0 av ev uid hw rdraw tid regs mem.

  (** The launch [main_entry] hides: the facts the consumers read the stack through. *)
  Lemma main_entry_launch : exists (brk : word),
    in_argv inp = av /\ in_envp inp = ev /\ in_uid inp = uid /\ in_hwcap inp = hw
    /\ valid_launch inp /\ entry_launch_ok_va Sv48 (mkEntry sp0 brk mbase rdraw) inp.
  Proof.
    destruct (me_mem _ _ _ _ _ _ _ _ _ _ _ _ ME) as (brk & J & E1 & E2 & E3 & E4 & Hvl & Hlau & _).
    exists brk. tauto.
  Qed.

  (* [comment removed for export] *)
  Lemma main_entry_rdn_above : forall segs (a : word) n,
    (bv_unsigned sp0 <= bv_unsigned a)%Z ->
    (bv_unsigned a + Z.of_nat n <= 2^64)%Z ->
    rdn segs mem a n = rdn segs (wrap_mem inp mbase RPH entry sp0 rdraw) a n.
  Proof.
    intros segs a n Ha Hn. destruct (me_mem _ _ _ _ _ _ _ _ _ _ _ _ ME) as (brk & J & _ & _ & _ & _ & _ & _ & HJ & _ & ->).
    apply rdn_cmem_above; assumption.
  Qed.

  Lemma main_entry_mem_above : forall (a : word),
    (bv_unsigned sp0 <= bv_unsigned a)%Z -> mem a = wrap_mem inp mbase RPH entry sp0 rdraw a.
  Proof.
    intros a Ha. destruct (me_mem _ _ _ _ _ _ _ _ _ _ _ _ ME) as (brk & J & _ & _ & _ & _ & _ & _ & HJ & _ & ->).
    apply cmem_at_above. exact Ha.
  Qed.

  (** At LPS 08b1429 the window every launch maps starts at [wok_lo] ([MemSplit.in_win]),
      not at [sp0 - stack_max_size]. *)
  Lemma main_entry_win_mapped : forall (a : word),
    (wok_lo sp0 <= bv_unsigned a < bv_unsigned sp0)%Z -> mem a <> None.
  Proof.
    intros a Ha. destruct (me_mem _ _ _ _ _ _ _ _ _ _ _ _ ME) as (brk & J & _ & _ & _ & _ & _ & _ & HJ & _ & ->).
    rewrite cmem_at_win by (unfold in_win; lia). apply HJ. unfold in_win. lia.
  Qed.

  Lemma main_entry_store_ok_win : forall segs (a : word) n,
    (wok_lo sp0 <= bv_unsigned a)%Z ->
    (bv_unsigned a + Z.of_nat n <= bv_unsigned sp0)%Z ->
    store_ok segs mem a n = true.
  Proof.
    intros segs a n Hlo Hhi. destruct (me_mem _ _ _ _ _ _ _ _ _ _ _ _ ME) as (brk & J & _ & _ & _ & _ & _ & _ & HJ & _ & ->).
    apply store_ok_cmem_win; [exact HJ | exact Hlo | exact Hhi].
  Qed.

  (* [comment removed for export] *)
  Lemma main_entry_mem_data : forall (a : word),
    (bv_unsigned a < bv_unsigned sp0 - stack_max_size)%Z ->
    mem a = D_main inp sp0 rdraw tid a.
  Proof.
    intros a Ha. destruct (me_mem _ _ _ _ _ _ _ _ _ _ _ _ ME) as (brk & J & _ & _ & _ & _ & _ & _ & HJ & _ & ->).
    apply cmem_at_data. unfold win_lo. exact Ha.
  Qed.

  Lemma main_entry_rdn_data : forall segs (a : word) n,
    (bv_unsigned a + Z.of_nat n <= bv_unsigned sp0 - stack_max_size)%Z ->
    rdn segs mem a n = rdn segs (D_main inp sp0 rdraw tid) a n.
  Proof.
    intros segs a n Ha. destruct (me_mem _ _ _ _ _ _ _ _ _ _ _ _ ME) as (brk & J & _ & _ & _ & _ & _ & _ & HJ & _ & ->).
    apply rdn_cmem_data. unfold win_lo. exact Ha.
  Qed.

End Consumers.
