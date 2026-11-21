(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3: recorded proofs written out as text, statements written out as text, lemmas added for the revision, the run's segment list (run_segments), the launch input as a ProcInput. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Vdso Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.boost_json.fuzz_parse.images Require Import Plain.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import
  Amb ShapeAlg Nodes RefNodes FileSim
  StartupTac ArgvEnv RefLayout RefImg RefStartupDefs
  RefStartup1 RefMemset RefStartup2 RefStartup3 RefStartup4
 Ref_code_47284_47870 Ref_code_d9dac_da94c    .
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.
(* the original sections used the model FP state fx0; it is made the file-local instance *)
#[local] Existing Instance OSSVerify.Proofs.boost_json.fuzz_parse.lib.PropExec.fx0.

(* LPS 75d69e00: written explicitly over the ProcInput (was zQ statements + KReplay terms).
   The assembly, main_entry and ref_startup follow boost-beast's ported RefStartup.v
   (a donor branch; not compiled by me, rule 15), translated by region (code +0x1c768 /
   +0x72f54 / +0x72e7c, data +0x79068): entry 0x47284, main 0x473d0, set_tid 0xda32c.
   J_main is boost-json's OWN old body (two constructor frames at sp0-88/-96, where boost-beast
   has more), retargeted onto inp with the model's stack_zero window, as boost-beast did.
   boost-beast's fin_c9a..fin_c9d are one fin_c9 here (RefStartup4). vdso_run_init lives in the
   model's Vdso.v, which Run.v imports but does not export, so Vdso is imported here. *)

Abbreviation SEGS := Plain.M.loaded_segments.
Abbreviation RPH := Plain.M.phdrs.
(* [comment removed for export] *)
Local Notation rsegs := Plain.M.loaded_segments (only parsing).
Local Notation rpc := Plain.M.init_pc (only parsing).
Local Notation rph := Plain.M.phdrs (only parsing).

(* [comment removed for export] *)

(* A walk over the binary's own segments is the same walk over the run's segment list
   ([StoreOk.step_run_segments]); boost-beast's StartupTac hunk, kept local here so that the
   checked StartupTac.v is not changed by uncompiled text. *)
Lemma msteps_run_segments : forall segs inp (sp mbase : word) st st',
  msteps segs st st' -> msteps (run_segments segs inp sp mbase) st st'.
Proof.
  intros segs inp sp mbase st st' H.
  induction H as [ms | ms ms' ms'' Hs Hstep _ IH]; [apply mst_refl|].
  eapply mst_step; [exact Hs | apply step_run_segments; exact Hstep | exact IH].
Qed.

Lemma bwd_run_segments : forall segs inp (sp mbase : word) G,
  bwd (run_segments segs inp sp mbase) G -> bwd segs G.
Proof.
  intros segs inp sp mbase G HG st st' Hm HG'.
  apply (HG st st'); [apply msteps_run_segments; exact Hm | exact HG'].
Qed.

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

(* [comment removed for export] *)
Definition J_main {AMB : Amb} (inp : ProcInput) (mbase entry sp0 : word) (rnd : EntryDraw)
    (s1v : word) : word -> option byte :=
  let J6 := J_tls sp0 (J_aux inp mbase entry sp0 rnd (J_lsm inp sp0
                         (stack_zero (stack_window_lo (in_kernel inp) mbase rnd))))
              (Z_to_bv 64 0xd9ec0) (pn_w inp rnd) s1v (Z_to_bv 64 0x12b948)
              (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) in
  wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes J6
    (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 0xd9ec8)))   (* [comment removed for export] *)
    (Z_to_bv 64 (bv_unsigned sp0 - 8)) (word_to_le_bytes 8 (Z_to_bv 64 0)))           (* [comment removed for export] *)
    (Z_to_bv 64 (bv_unsigned sp0 - 16)) (word_to_le_bytes 8 (Z_to_bv 64 0)))          (* [comment removed for export] *)
    (Z_to_bv 64 (bv_unsigned sp0 - 24)) (word_to_le_bytes 8 (Z_to_bv 64 0)))          (* [comment removed for export] *)
    (Z_to_bv 64 (bv_unsigned sp0 - 32)) (word_to_le_bytes 8 (Z_to_bv 64 0)))          (* [comment removed for export] *)
    (Z_to_bv 64 (bv_unsigned sp0 - 40)) (word_to_le_bytes 8 (Z_to_bv 64 0)))          (* [comment removed for export] *)
    (Z_to_bv 64 (bv_unsigned sp0 - 56)) (word_to_le_bytes 8 (Z_to_bv 64 0xda0bc)))    (* [comment removed for export] *)
    (Z_to_bv 64 (bv_unsigned sp0 - 64)) (word_to_le_bytes 8 (argv_w sp0)))             (* [comment removed for export] *)
    (Z_to_bv 64 (bv_unsigned sp0 - 72)) (word_to_le_bytes 8 (argc_w inp)))              (* [comment removed for export] *)
    (Z_to_bv 64 (bv_unsigned sp0 - 88)) (word_to_le_bytes 8 (Z_to_bv 64 0xda00c)))    (* [comment removed for export] *)
    (Z_to_bv 64 (bv_unsigned sp0 - 96)) (word_to_le_bytes 8 (Z_to_bv 64 0xf1210)))    (* [comment removed for export] *)
    (Z_to_bv 64 (bv_unsigned sp0 - 88)) (word_to_le_bytes 8 (Z_to_bv 64 0xda00c)))    (* [comment removed for export] *)
    (Z_to_bv 64 (bv_unsigned sp0 - 96)) (word_to_le_bytes 8 (Z_to_bv 64 0xf1210)).    (* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
Record main_entry {AMB : Amb} (inp : ProcInput) (mbase entry sp0 : word)
       (rnd : EntryDraw) (tid : word)
       (regs : bvmap 5 word) (mem : word -> option byte) : Prop := {
  me_ra  : getr regs 1 = Z_to_bv 64 0xda0cc;
  me_sp  : getr regs 2 = Z_to_bv 64 (bv_unsigned sp0 - 48);
  me_gp  : getr regs 3 = Z_to_bv 64 0x10800;
  me_tp  : getr regs 4 = Z_to_bv 64 0x10b6b8;
  me_s0  : getr regs 8 = Z_to_bv 64 (bv_unsigned sp0 + 8);
  me_s1  : getr regs 9 = argcN inp;
  me_a0  : getr regs 10 = argcN inp;
  me_a1  : getr regs 11 = Z_to_bv 64 (bv_unsigned sp0 + 8);
  me_a2  : getr regs 12 = Z_to_bv 64 (bv_unsigned sp0 + 16 + 8 * Z.of_nat (length (in_argv inp)));
  me_s2  : getr regs 18 = Z_to_bv 64 0x473d0;
  me_s3  : getr regs 19 = Z_to_bv 64 (bv_unsigned sp0 + 16 + 8 * Z.of_nat (length (in_argv inp)));
  me_szero : forall r : reg, In r [20; 21; 22; 23; 24; 25; 26; 27]%list -> getr regs r = Z_to_bv 64 0;
  me_mem : exists (J : word -> option byte) (s1v : word),
             wfJ sp0 J /\ J = J_main inp mbase entry sp0 rnd s1v
             /\ mem = cmem sp0 (wrap_mem inp mbase RPH entry sp0 rnd) J (D_main inp sp0 rnd tid)
}.

Section Assembly.
  Context {AMB : Amb}.
  Variable inp : ProcInput.
  Variable mbase : word.
  Variable sp brk : word.
  Variable rnd : EntryDraw.
  Local Notation argv := (in_argv inp) (only parsing).
  Local Notation envp := (in_envp inp) (only parsing).
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

  (* [comment removed for export] *)
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

  Local Notation RS := (run_segments rsegs inp sp mbase) (only parsing).
  Local Notation M0 lim := (with_vdso (vdso_run_init (ed_vdso rnd))
                              (init_model (segments_reserved RS) brk mbase sp lim inp)) (only parsing).

  Theorem ref_startup_sec : forall lim K,
    (forall tid regs mem,
       (0 < bv_unsigned tid < 2^22)%Z ->
       main_entry inp mbase (0x47284 : word) sp rnd tid regs mem ->
       realizes RS (mkCfg (mkst regs (0x473d0 : word) mem (seg_rom RS))
                          (with_tid tid (M0 lim))) K) ->
    realizes RS (init_config RS rpc rph sp brk mbase rnd lim inp) K.
  Proof.
    intros lim K HK.
    pose proof Hlo as Hlo'. pose proof Hhi as Hhi'. pose proof Hal as Hal'.
    pose proof (u64_range sp) as Hsp.
    unfold init_config. cbn [cfg_ms cfg_model].
    set (model := M0 lim).
    assert (Hh : m_halted model = None) by reflexivity.
    assert (Hlazy : m_vm_lazy model = []) by reflexivity.
    assert (Ht0 : m_tid model = None) by reflexivity.
    set (RZ := fun st : machine_state => realizes RS (mkCfg st model) K).
    assert (HG : bwd rsegs RZ)
      by (apply (bwd_run_segments rsegs inp sp mbase); apply bwd_rz; [exact Hh | exact Hlazy]).
    rewrite init_mkst.
    replace (Z_to_bv 64 (Z.of_N Plain.M.init_pc)) with (0x47284 : word) by (apply bv_eq; reflexivity).
    rewrite (cmem_init inp mbase rph (0x47284 : word) sp brk rnd Hlau).
    fold (regs_init sp).
    (* [comment removed for export] *)
    destruct (p1_run Sv48 inp mbase (0x47284 : word) sp brk rnd
                Hva Hve Hvl Hlau Hlo' Hhi' Hal' (seg_rom RS) J0 HJ0)
      as [regs1 (R1 & A1 & A2 & A3 & A4 & A8 & A9 & A10 & A11 & A12 & A18 & Az)].
    eapply rz_msteps; [exact Hh | exact Hlazy | apply msteps_run_segments; exact R1 |].
    (* [comment removed for export] *)
    assert (A1' : getr regs1 1 = (0xd9ddc : word)) by (rewrite A1; apply bv_eq; reflexivity).
    destruct (memset304_run regs1 (cmem sp (wrap_mem inp mbase RPH (0x47284 : word) sp rnd) (J1 inp sp J0) (fun _ => None))
                (seg_rom RS) (Z_to_bv 64 (bv_unsigned sp - 368)) (0xd9ddc : word) A1')
      as [regs2 [mem2 (R2 & M2 & G2)]].
    { unfold ret_ok. apply bv_eq. vm_compute. reflexivity. }
    { exact A10. } { exact A11. } { exact A12. }
    { rewrite u_Z2bv by lia. rewrite <- Zminus_mod_idemp_l.
      replace (bv_unsigned sp mod 8)%Z with 0%Z; [reflexivity|].
      symmetry. rewrite <- (Z.mod_mod_divide _ 16 8) by (exists 2%Z; reflexivity). rewrite Hal'. reflexivity. }
    { rewrite u_Z2bv by lia. lia. }
    { apply store_ok_cmem_win; [unfold J1; repeat apply wfJ_wbytes; exact HJ0 | region_side | region_side]. }
    eapply rz_msteps; [exact Hh | exact Hlazy | apply msteps_run_segments; exact R2 |]. subst mem2.
    rewrite wbytes_cmem_win by region_side.
    (* [comment removed for export] *)
    carry G2 A2 (2:reg) B2. carry G2 A8 (8:reg) B8. carry G2 A9 (9:reg) B9. carry G2 A10 (10:reg) B10.
    carry G2 A3 (3:reg) B3.
    change (realizes RS (mkCfg ?st model) K) with (RZ st).
    eapply (p3_run Sv48 inp mbase (0x47284 : word) sp brk rnd
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
    (* [comment removed for export] *)
    change (J1 inp sp J0) with (J_lsm inp sp J0).
    eapply (tls_c1 Sv48 inp mbase (0x47284 : word) sp brk J0 rnd
              Hva Hve Hvl Hlau Hlo Hhi Hal) with (G := RZ) (s1v := getr regs3 9) (tid := Z_to_bv 64 0); try side Hva Hve HG.
    intros regs4a; intros.
    eapply (tls_c2 Sv48 inp mbase (0x47284 : word) sp brk J0 rnd
              Hva Hve Hvl Hlau Hlo Hhi Hal) with (G := RZ) (tid := Z_to_bv 64 0); try side Hva Hve HG.
    intros regs4b; intros.
    eapply (tls_c3 Sv48 inp mbase (0x47284 : word) sp brk J0 rnd
              Hva Hve Hvl Hlau Hlo Hhi Hal) with (G := RZ) (tid := Z_to_bv 64 0); try side Hva Hve HG.
    intros regs4c; intros.
    eapply (tls_c4 Sv48 inp mbase (0x47284 : word) sp brk J0 rnd
              Hva Hve Hvl Hlau Hlo Hhi Hal) with (G := RZ) (tid := Z_to_bv 64 0); try side Hva Hve HG.
    intros regs4; intros.
    (* [comment removed for export] *)
    unfold RZ at 1.
    eapply (rz_set_tid RS regs4 (0xda32c : word) _ (seg_rom RS) model K W_da32c
              (eq_trans (fetch_word_run_segments rsegs inp sp mbase _) F_da32c) E_da32c);
      [exact Hh | exact Hlazy | assumption | exact Ht0 |].
    intros tid Htid'.
    assert (Htid : (0 < bv_unsigned tid < 2^22)%Z) by (unfold Fork.PID_MAX_ENVELOPE in Htid'; exact Htid').
    replace (v_addi (0xda32c : word) 4) with (0xda330 : word) by (apply bv_eq; reflexivity).
    set (model' := with_tid tid model).
    assert (Hh' : m_halted model' = None) by (unfold model'; rewrite with_tid_halted; exact Hh).
    assert (Hlazy' : m_vm_lazy model' = []) by (unfold model'; rewrite with_tid_lazy; exact Hlazy).
    set (RZ' := fun st : machine_state => realizes RS (mkCfg st model') K).
    assert (HG' : bwd rsegs RZ')
      by (apply (bwd_run_segments rsegs inp sp mbase); apply bwd_rz; [exact Hh' | exact Hlazy']).
    change (realizes RS (mkCfg ?st model') K) with (RZ' st).
    eapply (tls_c5 Sv48 inp mbase (0x47284 : word) sp brk J0 rnd
              Hva Hve Hvl Hlau Hlo Hhi Hal) with (G := RZ'); try side Hva Hve HG'.
    intros regs5; intros.
    eapply (fin_c6 Sv48 inp mbase (0x47284 : word) sp brk J0 rnd
              Hva Hve Hvl Hlau Hlo Hhi Hal) with (G := RZ'); try side Hva Hve HG'.
    intros regs6; intros.
    eapply (fin_c7 Sv48 inp mbase (0x47284 : word) sp brk J0 rnd
              Hva Hve Hvl Hlau Hlo Hhi Hal) with (G := RZ'); try side Hva Hve HG'.
    intros regs7; intros.
    eapply (fin_c8 Sv48 inp mbase (0x47284 : word) sp brk J0 rnd
              Hva Hve Hvl Hlau Hlo Hhi Hal) with (G := RZ'); try side Hva Hve HG'.
    intros regs8; intros.
    eapply (fin_c9 Sv48 inp mbase (0x47284 : word) sp brk J0 rnd
              Hva Hve Hvl Hlau Hlo Hhi Hal) with (G := RZ'); try side Hva Hve HG'.
    intros regs9; intros.
    unfold RZ'. apply (HK tid regs9). { exact Htid. }
    split; try assumption.
    - intros r Hr. cbn [In] in Hr.
      repeat (destruct Hr as [<-|Hr]; [assumption|]). destruct Hr.
    - eexists _, (getr regs3 9). split; [|split; [reflexivity|]].
      + unfold J_main, J_tls, J_aux, J_lsm. repeat first [ apply wfJ_wbytes | apply wfJ_J_rseq ]. exact HJ0.
      + unfold J_main, J_tls, D_main, D_cxx, D_fd, D_ssp, D_tls, D_tlsA, D_tlsB. reflexivity.
  Qed.

End Assembly.

(* [comment removed for export] *)
Theorem ref_startup : forall sp brk mbase rnd lim inp K,
  valid_sp sp -> valid_brk rsegs brk -> valid_argv (in_argv inp) -> valid_envp (in_envp inp) ->
  valid_launch inp ->
  entry_launch_ok_va Sv48 (mkEntry sp brk mbase rnd) inp ->
  (forall tid regs mem,
     (0 < bv_unsigned tid < 2^22)%Z ->
     @main_entry (amb_of inp) inp mbase (0x47284 : word) sp rnd tid regs mem ->
     realizes (run_segments rsegs inp sp mbase)
       (mkCfg (mkst regs (0x473d0 : word) mem (seg_rom (run_segments rsegs inp sp mbase)))
              (with_tid tid (with_vdso (vdso_run_init (ed_vdso rnd))
                 (init_model (segments_reserved (run_segments rsegs inp sp mbase)) brk mbase sp lim inp)))) K) ->
  realizes (run_segments rsegs inp sp mbase)
    (init_config (run_segments rsegs inp sp mbase) rpc rph sp brk mbase rnd lim inp) K.
Proof.
  intros sp brk mbase rnd lim inp K Hsp Hbrk Hva Hve Hvl Hlau HK.
  exact (@ref_startup_sec (amb_of inp) inp mbase sp brk rnd
           Hva Hve Hvl Hlau Hsp lim K HK).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section Consumers.
  Context {AMB : Amb}.
  Variable inp : ProcInput.
  Variable mbase entry : word.
  Variable sp0 : word.
  Variable rnd : EntryDraw.
  Variable tid : word.
  Variable regs : bvmap 5 word.
  Variable mem : word -> option byte.
  Local Notation av := (in_argv inp) (only parsing).
  Local Notation ev := (in_envp inp) (only parsing).
  Hypothesis ME : main_entry inp mbase entry sp0 rnd tid regs mem.

  (* [comment removed for export] *)
  Lemma main_entry_rdn_above : forall segs (a : word) n,
    (bv_unsigned sp0 <= bv_unsigned a)%Z ->
    (bv_unsigned a + Z.of_nat n <= 2^64)%Z ->
    rdn segs mem a n = rdn segs (wrap_mem inp mbase RPH entry sp0 rnd) a n.
  Proof.
    intros segs a n Ha Hn. destruct (me_mem _ _ _ _ _ _ _ _ ME) as (J & s1v & HJ & _ & ->).
    apply rdn_cmem_above; assumption.
  Qed.

  Lemma main_entry_mem_above : forall (a : word),
    (bv_unsigned sp0 <= bv_unsigned a)%Z -> mem a = wrap_mem inp mbase RPH entry sp0 rnd a.
  Proof.
    intros a Ha. destruct (me_mem _ _ _ _ _ _ _ _ ME) as (J & s1v & HJ & _ & ->).
    apply cmem_at_above. exact Ha.
  Qed.

  (* [comment removed for export] *)
  Lemma main_entry_win_mapped : forall (a : word),
    (wok_lo sp0 <= bv_unsigned a < bv_unsigned sp0)%Z -> mem a <> None.
  Proof.
    intros a Ha. destruct (me_mem _ _ _ _ _ _ _ _ ME) as (J & s1v & HJ & _ & ->).
    rewrite cmem_at_win by (unfold in_win, win_lo; lia). apply HJ. unfold in_win, win_lo. lia.
  Qed.

  Lemma main_entry_store_ok_win : forall segs (a : word) n,
    (wok_lo sp0 <= bv_unsigned a)%Z ->
    (bv_unsigned a + Z.of_nat n <= bv_unsigned sp0)%Z ->
    store_ok segs mem a n = true.
  Proof.
    intros segs a n Hlo Hhi. destruct (me_mem _ _ _ _ _ _ _ _ ME) as (J & s1v & HJ & _ & ->).
    apply store_ok_cmem_win; [exact HJ | unfold win_lo; lia | lia].
  Qed.

  (* [comment removed for export] *)
  Lemma main_entry_mem_data : forall (a : word),
    (bv_unsigned a < bv_unsigned sp0 - stack_max_size)%Z ->
    mem a = D_main inp sp0 rnd tid a.
  Proof.
    intros a Ha. destruct (me_mem _ _ _ _ _ _ _ _ ME) as (J & s1v & HJ & _ & ->).
    apply cmem_at_data. unfold win_lo. exact Ha.
  Qed.

  Lemma main_entry_rdn_data : forall segs (a : word) n,
    (bv_unsigned a + Z.of_nat n <= bv_unsigned sp0 - stack_max_size)%Z ->
    rdn segs mem a n = rdn segs (D_main inp sp0 rnd tid) a n.
  Proof.
    intros segs a n Ha. destruct (me_mem _ _ _ _ _ _ _ _ ME) as (J & s1v & HJ & _ & ->).
    apply rdn_cmem_data. unfold win_lo. exact Ha.
  Qed.
End Consumers.
