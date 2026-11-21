(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (walks lifted to the run's segments, the zero-filled stack window, the vDSO, the launch input's kernel build): changed J0, J_main, ME and 15 more; added ENT, HJ0, Hlau and 7 more. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Vdso Run.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import ExecutableSpecs.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_json_cursor.images Require Import Plain.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Import
  ShapeAlg DivergeSim SpinAlg SpinAlgX Nodes RefNodes FileSim
  StartupTac ArgvEnv RefLayout Pm10Img Pm10StartupDefs
  Pm10Startup1 Pm10Memset Pm10Startup2 Pm10Startup3 Pm10Startup4
 Pm10_code_a4000_a5000 Pm10_code_a4d64_a5014     .
Import ListNotations.
Open Scope bv_scope.

Abbreviation SEGS := Plain.M.loaded_segments.
Abbreviation RPH := Plain.M.phdrs.

Local Notation rsegs := Plain.M.loaded_segments (only parsing).
Local Notation rpc := Plain.M.init_pc (only parsing).
Local Notation rph := Plain.M.phdrs (only parsing).
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require PropExec.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Section FPX_1. #[local] Existing Instance PropExec.fx0.

Lemma bwd_rz : forall segs scfg model K,
  m_halted model = None -> m_vm_lazy model = [] ->
  bwd segs (fun st => srealizes segs scfg (mkCfg st model) K).
Proof.
  intros segs scfg model K Hh Hlazy st st' Hms Hst'. eapply srz_msteps; eassumption.
Qed.

Definition J_main (inp : ProcInput) (mbase entry sp0 : word) (rdraw : EntryDraw) (Jb : word -> option byte) (s1v : word) : word -> option byte :=
  let J6 := J_tls sp0 (J_aux inp mbase entry sp0 rdraw (J_lsm inp sp0 Jb))
              (Z_to_bv 64 0xa4b54) (pn_w inp rdraw) s1v (Z_to_bv 64 0xf4c40)
              (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) in
  wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes J6
    (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 0xa4b5c)))
    (Z_to_bv 64 (bv_unsigned sp0 - 8)) (word_to_le_bytes 8 (Z_to_bv 64 0)))
    (Z_to_bv 64 (bv_unsigned sp0 - 16)) (word_to_le_bytes 8 (Z_to_bv 64 0)))
    (Z_to_bv 64 (bv_unsigned sp0 - 24)) (word_to_le_bytes 8 (Z_to_bv 64 0)))
    (Z_to_bv 64 (bv_unsigned sp0 - 32)) (word_to_le_bytes 8 (Z_to_bv 64 0)))
    (Z_to_bv 64 (bv_unsigned sp0 - 40)) (word_to_le_bytes 8 (Z_to_bv 64 0)))
    (Z_to_bv 64 (bv_unsigned sp0 - 56)) (word_to_le_bytes 8 (Z_to_bv 64 0xa4d50)))
    (Z_to_bv 64 (bv_unsigned sp0 - 64)) (word_to_le_bytes 8 (argv_w sp0)))
    (Z_to_bv 64 (bv_unsigned sp0 - 72)) (word_to_le_bytes 8 (argc_w inp)))
    (Z_to_bv 64 (bv_unsigned sp0 - 88)) (word_to_le_bytes 8 (Z_to_bv 64 0xa4ca0)))
    (Z_to_bv 64 (bv_unsigned sp0 - 96)) (word_to_le_bytes 8 (Z_to_bv 64 0xbbab0)).

(** The start-up's hand-off state.  The launch's own input [inp] (its
    kernel build, its execfn, its gid), the mmap base and the entry point
    lay out the stack block at the revision, so [me_mem] names them; the
    argument, environment, uid and hwcap the consumers quantify over are
    its fields. *)
Record main_entry (inp : ProcInput) (mbase entry sp0 : word) (av ev : list (list byte)) (uid hw : word) (rdraw : EntryDraw) (tid : word)
       (regs : bvmap 5 word) (mem : word -> option byte) : Prop := {
  me_ra  : getr regs 1 = Z_to_bv 64 0xa4d60;
  me_sp  : getr regs 2 = Z_to_bv 64 (bv_unsigned sp0 - 48);
  me_gp  : getr regs 3 = Z_to_bv 64 0x10800;
  me_tp  : getr regs 4 = Z_to_bv 64 0xd49b0;
  me_s0  : getr regs 8 = Z_to_bv 64 (bv_unsigned sp0 + 8);
  me_s1  : getr regs 9 = len_word av;
  me_a0  : getr regs 10 = len_word av;
  me_a1  : getr regs 11 = Z_to_bv 64 (bv_unsigned sp0 + 8);
  me_a2  : getr regs 12 = Z_to_bv 64 (bv_unsigned sp0 + 16 + 8 * Z.of_nat (length av));
  me_s2  : getr regs 18 = Z_to_bv 64 0x38f5c;
  me_s3  : getr regs 19 = Z_to_bv 64 (bv_unsigned sp0 + 16 + 8 * Z.of_nat (length av));
  me_szero : forall r : reg, In r [20; 21; 22; 23; 24; 25; 26; 27]%list -> getr regs r = Z_to_bv 64 0;
  me_mem : exists (brk : word) (J : word -> option byte),
             in_argv inp = av /\ in_envp inp = ev /\ in_uid inp = uid /\ in_hwcap inp = hw
             /\ valid_launch inp /\ entry_launch_ok_va Sv48 (mkEntry sp0 brk mbase rdraw) inp
             /\ wfJ sp0 J /\ (exists (Jb : word -> option byte) (s1v : word), J = J_main inp mbase entry sp0 rdraw Jb s1v)
             /\ mem = cmem sp0 (wrap_mem inp mbase RPH entry sp0 rdraw) J (D_main inp sp0 rdraw (ed_random rdraw) tid)
}.

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
  Local Notation ENT := (0x38e10 : word) (only parsing).

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

  Theorem ref_startup_sec : forall lim K,
    (forall tid regs mem,
       (0 < bv_unsigned tid < 2^22)%Z ->
       main_entry inp mbase ENT sp argv envp (in_uid inp) (in_hwcap inp) rdraw tid regs mem ->
       srealizes rsegs scfg (mkCfg (mkst regs (0x38f5c : word) mem (seg_rom rsegs))
                             (with_tid tid (with_vdso (Vdso.vdso_run_init (ed_vdso rdraw))
                                (init_model (segments_reserved rsegs) brk mbase sp lim inp)))) K) ->
    srealizes rsegs scfg (init_config rsegs rpc rph sp brk mbase rdraw lim inp) K.
  Proof.
    intros lim K HK.
    pose proof Hlo as Hlo'. pose proof Hhi as Hhi'. pose proof Hal as Hal'.
    pose proof (u64_range sp) as Hsp.
    unfold init_config. cbn [cfg_ms cfg_model].
    (* 08b1429: [vdso_run_init] is [Vdso.vdso_run_init] at this revision, as AllocSim.v:1216 writes it *)
    set (model := with_vdso (Vdso.vdso_run_init (ed_vdso rdraw)) (init_model (segments_reserved rsegs) brk mbase sp lim inp)).
    assert (Hh : m_halted model = None) by reflexivity.
    assert (Hlazy : m_vm_lazy model = []) by reflexivity.
    assert (Ht0 : m_tid model = None) by reflexivity.
    set (RZ := fun st : machine_state => srealizes rsegs scfg (mkCfg st model) K).
    assert (HG : bwd rsegs RZ) by (apply bwd_rz; [exact Hh | exact Hlazy]).
    rewrite init_mkst.
    replace (Z_to_bv 64 (Z.of_N Plain.M.init_pc)) with (0x38e10 : word) by (apply bv_eq; reflexivity).
    rewrite (cmem_init inp mbase RPH ENT sp brk rdraw Hlau). fold (regs_init sp). fold J0.

    destruct (p1_run Sv48 inp mbase ENT sp brk rdraw Hva Hve Hvl Hlau Hlo' Hhi' Hal' (seg_rom SEGS) J0 HJ0)
      as [regs1 (R1 & A1 & A2 & A3 & A4 & A8 & A9 & A10 & A11 & A12 & A18 & Az)].
    eapply srz_msteps; [exact Hh | exact Hlazy | exact R1 |].

    assert (A1' : getr regs1 1 = (0xa4a70 : word)) by (rewrite A1; apply bv_eq; reflexivity).
    destruct (memset304_run regs1 (cmem sp (wrap_mem inp mbase RPH ENT sp rdraw) (J1 inp sp J0) (fun _ => None))
                (seg_rom SEGS) (Z_to_bv 64 (bv_unsigned sp - 368)) (0xa4a70 : word) A1')
      as [regs2 [mem2 (R2 & M2 & G2)]].
    { unfold ret_ok. apply bv_eq. vm_compute. reflexivity. }
    { exact A10. } { exact A11. } { exact A12. }
    { rewrite u_Z2bv by lia. rewrite <- Zminus_mod_idemp_l.
      replace (bv_unsigned sp mod 8)%Z with 0%Z; [reflexivity|].
      symmetry. rewrite <- (Z.mod_mod_divide _ 16 8) by (exists 2%Z; reflexivity). rewrite Hal'. reflexivity. }
    { rewrite u_Z2bv by lia. lia. }
    { apply store_ok_cmem_win; [unfold J1; repeat apply wfJ_wbytes; exact HJ0 | region_side | region_side]. }
    eapply srz_msteps; [exact Hh | exact Hlazy | exact R2 |]. subst mem2.
    rewrite wbytes_cmem_win by region_side.

    carry G2 A2 (2:reg) B2. carry G2 A8 (8:reg) B8. carry G2 A9 (9:reg) B9. carry G2 A10 (10:reg) B10.
    carry G2 A3 (3:reg) B3.
    change (srealizes SEGS scfg (mkCfg ?st model) K) with (RZ st).
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
    eapply (rz_set_tid SEGS scfg regs4 (0xa4fc0 : word) _ (seg_rom SEGS) model K W_a4fc0 F_a4fc0 E_a4fc0);
      [exact Hh | exact Hlazy | assumption | exact Ht0 |].
    intros tid Htid.
    replace (v_addi (0xa4fc0 : word) 4) with (0xa4fc4 : word) by (apply bv_eq; reflexivity).
    set (model' := with_tid tid model).
    assert (Hh' : m_halted model' = None) by (unfold model'; rewrite with_tid_halted; exact Hh).
    assert (Hlazy' : m_vm_lazy model' = []) by (unfold model'; rewrite with_tid_lazy; exact Hlazy).
    set (RZ' := fun st : machine_state => srealizes rsegs scfg (mkCfg st model') K).
    assert (HG' : bwd rsegs RZ') by (apply bwd_rz; [exact Hh' | exact Hlazy']).
    change (srealizes SEGS scfg (mkCfg ?st model') K) with (RZ' st).
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
    - exists brk, (J_main inp mbase ENT sp rdraw J0 (getr regs3 9)).
      split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
      split; [exact Hvl|]. split; [exact Hlau|].
      split; [|split; [exists J0, (getr regs3 9); reflexivity|]].
      + unfold J_main, J_tls, J_aux, J_lsm. repeat apply wfJ_wbytes. exact HJ0.
      + unfold J_main, J_tls, D_main, D_fd, D_ssp, D_tls, D_tlsA, D_tlsB. reflexivity.
  Qed.

End Assembly.

Theorem ref_startup : forall scfg sp brk mbase (rdraw : EntryDraw) lim inp K,
  valid_sp sp -> valid_brk rsegs brk -> valid_argv (in_argv inp) -> valid_envp (in_envp inp) ->
  valid_launch inp -> entry_launch_ok_va Sv48 (mkEntry sp brk mbase rdraw) inp ->
  (forall tid regs mem,
     (0 < bv_unsigned tid < 2^22)%Z ->
     main_entry inp mbase (0x38e10 : word) sp (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp) rdraw tid regs mem ->
     srealizes rsegs scfg (mkCfg (mkst regs (0x38f5c : word) mem (seg_rom rsegs))
                           (with_tid tid (with_vdso (Vdso.vdso_run_init (ed_vdso rdraw))
                              (init_model (segments_reserved rsegs) brk mbase sp lim inp)))) K) ->
  srealizes rsegs scfg (init_config rsegs rpc rph sp brk mbase rdraw lim inp) K.
Proof.
  intros scfg sp brk mbase rdraw lim inp K Hsp Hbrk Hva Hve Hvl Hlau HK.
  exact (ref_startup_sec scfg inp mbase sp brk rdraw Hva Hve Hsp Hvl Hlau lim K HK).
Qed.

Section Consumers.
  Variable inp : ProcInput.
  Variable mbase entry : word.
  Variable sp0 : word.
  Variables av ev : list (list byte).
  Variable uid : word.
  Variable hw : word.
  Variable rdraw : EntryDraw.
  Variable tid : word.
  Variable regs : bvmap 5 word.
  Variable mem : word -> option byte.
  Hypothesis ME : main_entry inp mbase entry sp0 av ev uid hw rdraw tid regs mem.

  (** The launch [main_entry] hides, with the facts the consumers read. *)
  Lemma main_entry_launch : exists (brk : word),
    in_argv inp = av /\ in_envp inp = ev /\ in_uid inp = uid /\ in_hwcap inp = hw
    /\ valid_launch inp /\ entry_launch_ok_va Sv48 (mkEntry sp0 brk mbase rdraw) inp
    /\ (forall segs (a : word) n,
          (bv_unsigned sp0 <= bv_unsigned a)%Z -> (bv_unsigned a + Z.of_nat n <= 2^64)%Z ->
          rdn segs mem a n = rdn segs (wrap_mem inp mbase RPH entry sp0 rdraw) a n)
    /\ (forall (a : word), (bv_unsigned sp0 <= bv_unsigned a)%Z -> mem a = wrap_mem inp mbase RPH entry sp0 rdraw a)
    /\ (forall (a : word), (bv_unsigned a < bv_unsigned sp0 - stack_max_size)%Z ->
          mem a = D_main inp sp0 rdraw (ed_random rdraw) tid a)
    /\ (forall segs (a : word) n, (bv_unsigned a + Z.of_nat n <= bv_unsigned sp0 - stack_max_size)%Z ->
          rdn segs mem a n = rdn segs (D_main inp sp0 rdraw (ed_random rdraw) tid) a n).
  Proof.
    destruct (me_mem _ _ _ _ _ _ _ _ _ _ _ _ ME) as (brk & J & E1 & E2 & E3 & E4 & Hvl & Hlau & HJ & _ & ->).
    exists brk.
    do 6 (split; [assumption|]).
    split; [intros segs a n Ha Hn; apply rdn_cmem_above; assumption|].
    split; [intros a Ha; apply cmem_at_above; exact Ha|].
    split; [intros a Ha; apply cmem_at_data; unfold win_lo; exact Ha|].
    intros segs a n Ha. apply rdn_cmem_data. unfold win_lo. exact Ha.
  Qed.

  (* At the revision the window every launch maps starts at [wok_lo]
     ([MemSplit.wfJ]), not at [sp0 - stack_max_size]. *)
  Lemma main_entry_win_mapped : forall (a : word),
    (wok_lo sp0 <= bv_unsigned a < bv_unsigned sp0)%Z -> mem a <> None.
  Proof.
    intros a Ha. destruct (me_mem _ _ _ _ _ _ _ _ _ _ _ _ ME) as (brk & J & _ & _ & _ & _ & _ & _ & HJ & _ & ->).
    pose proof (win_lo_le_wok_lo sp0).
    rewrite cmem_at_win by (unfold in_win in *; lia). apply HJ. unfold in_win. lia.
  Qed.

  Lemma main_entry_store_ok_win : forall segs (a : word) n,
    (wok_lo sp0 <= bv_unsigned a)%Z ->
    (bv_unsigned a + Z.of_nat n <= bv_unsigned sp0)%Z ->
    store_ok segs mem a n = true.
  Proof.
    intros segs a n Hlo Hhi. destruct (me_mem _ _ _ _ _ _ _ _ _ _ _ _ ME) as (brk & J & _ & _ & _ & _ & _ & _ & HJ & _ & ->).
    apply store_ok_cmem_win; [exact HJ | exact Hlo | lia].
  Qed.
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

  Lemma main_entry_mem_data : forall (a : word),
    (bv_unsigned a < bv_unsigned sp0 - stack_max_size)%Z ->
    mem a = D_main inp sp0 rdraw (ed_random rdraw) tid a.
  Proof.
    intros a Ha. destruct (me_mem _ _ _ _ _ _ _ _ _ _ _ _ ME) as (brk & J & _ & _ & _ & _ & _ & _ & HJ & _ & ->).
    apply cmem_at_data. unfold win_lo. exact Ha.
  Qed.

  Lemma main_entry_rdn_data : forall segs (a : word) n,
    (bv_unsigned a + Z.of_nat n <= bv_unsigned sp0 - stack_max_size)%Z ->
    rdn segs mem a n = rdn segs (D_main inp sp0 rdraw (ed_random rdraw) tid) a n.
  Proof.
    intros segs a n Ha. destruct (me_mem _ _ _ _ _ _ _ _ _ _ _ _ ME) as (brk & J & _ & _ & _ & _ & _ & _ & HJ & _ & ->).
    apply rdn_cmem_data. unfold win_lo. exact Ha.
  Qed.

  (* the facts the launch fixes, in the consumers' own terms *)
  Lemma main_entry_inp : in_argv inp = av /\ in_envp inp = ev /\ in_uid inp = uid /\ in_hwcap inp = hw
    /\ valid_launch inp /\ exists brk, entry_launch_ok_va Sv48 (mkEntry sp0 brk mbase rdraw) inp.
  Proof.
    destruct (me_mem _ _ _ _ _ _ _ _ _ _ _ _ ME) as (brk & J & E1 & E2 & E3 & E4 & Hvl & Hlau & _).
    (* OLD [repeat split; try assumption. exists brk. exact Hlau.]  [repeat split] descends
       into every one-constructor inductive, so once [valid_launch] / [entry_launch_ok_va]
       gained structure at this revision it broke them apart too and [exists brk] met a
       leftover component ("Not an inductive goal with 1 constructor").  Split only the six
       top-level [and]s of the statement, by hand. *)
    split; [exact E1|]. split; [exact E2|]. split; [exact E3|]. split; [exact E4|].
    split; [exact Hvl|]. exists brk. exact Hlau.
  Qed.
End Consumers.

End FPX_1.
