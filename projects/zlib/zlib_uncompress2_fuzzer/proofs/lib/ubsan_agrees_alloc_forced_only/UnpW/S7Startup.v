(* reloc-zl14c *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only Require Import RunCtx.  (* a worker (A1) tool *)
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only Require Import RunHit. (* reloc-zl14c *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only Require Import ModelAmb.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs Vdso State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import ExecutableSpecs.
From LinuxProcessSemantics.LinuxProcessSem.Checks.Sys Require Import DispatchCompute.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.World Require Import SrcO_zlib_zlib_uncompress2_fuzzer_repro.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only Require Import ShapeAlg Nodes RefNodes FileSim StartupTac ArgvEnv RefLayout MemSplit StoreOk. From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW Require Import S7Img S7StartupDefs S7Startup1 S7Memset S7Startup2 S7Startup3 S7Startup4 S7_code_146e4_15000 S7_code_18000_19000.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only Require Import LiaFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Existing Instance PropExec.fx0.
Import ListNotations.
Open Scope bv_scope.

Abbreviation SEGS := SrcO_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments.
Abbreviation RPH := SrcO_zlib_zlib_uncompress2_fuzzer_repro.M.phdrs.
(* [comment removed for export] *)
Local Notation rsegs := SrcO_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (only parsing).
Local Notation rpc := SrcO_zlib_zlib_uncompress2_fuzzer_repro.M.init_pc (only parsing).
Local Notation rph := SrcO_zlib_zlib_uncompress2_fuzzer_repro.M.phdrs (only parsing).
(* a worker port727 (): the entry pc as the launch block sees it (Run.init_machine_state's [entry]). *)
Local Notation ENT := (Z_to_bv 64 (Z.of_N SrcO_zlib_zlib_uncompress2_fuzzer_repro.M.init_pc)) (only parsing).

(* [comment removed for export] *)

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
(* a worker port727 (): over the launch (inp / mbase / rdraw); the window starts as the launch's own
   stack_zero (zero from Run.stack_window_lo, unmapped below), not as all zeros. *)
Definition J_main (sp0 : word) (inp : ProcInput) (mbase : word) (rdraw : EntryDraw) (s1v : word)
    : word -> option byte :=
  let J6 := J_tls sp0 (J_aux sp0 inp mbase rdraw
                         (J_lsm sp0 inp (stack_zero (stack_window_lo (in_kernel inp) mbase rdraw))))
              (Z_to_bv 64 0x18a60) (pn_w inp rdraw) s1v (Z_to_bv 64 0x93248)
              (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) in
  wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes J6
    (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 0x18a68)))   (* [comment removed for export] *)
    (Z_to_bv 64 (bv_unsigned sp0 - 8)) (word_to_le_bytes 8 (Z_to_bv 64 0)))           (* [comment removed for export] *)
    (Z_to_bv 64 (bv_unsigned sp0 - 16)) (word_to_le_bytes 8 (Z_to_bv 64 0)))          (* [comment removed for export] *)
    (Z_to_bv 64 (bv_unsigned sp0 - 24)) (word_to_le_bytes 8 (Z_to_bv 64 0)))          (* [comment removed for export] *)
    (Z_to_bv 64 (bv_unsigned sp0 - 32)) (word_to_le_bytes 8 (Z_to_bv 64 0)))          (* [comment removed for export] *)
    (Z_to_bv 64 (bv_unsigned sp0 - 40)) (word_to_le_bytes 8 (Z_to_bv 64 0)))          (* [comment removed for export] *)
    (Z_to_bv 64 (bv_unsigned sp0 - 56)) (word_to_le_bytes 8 (Z_to_bv 64 0x18c5c)))    (* [comment removed for export] *)
    (Z_to_bv 64 (bv_unsigned sp0 - 64)) (word_to_le_bytes 8 (argv_w sp0)))             (* [comment removed for export] *)
    (Z_to_bv 64 (bv_unsigned sp0 - 72)) (word_to_le_bytes 8 (argc_w inp)))             (* [comment removed for export] *)
    (Z_to_bv 64 (bv_unsigned sp0 - 88)) (word_to_le_bytes 8 (Z_to_bv 64 0x18bac)))    (* [comment removed for export] *)
    (Z_to_bv 64 (bv_unsigned sp0 - 96)) (word_to_le_bytes 8 (Z_to_bv 64 0x21bb0)).    (* [comment removed for export] *)

(* [comment removed for export] *)
Record main_entry (sp0 : word) (inp : ProcInput) (mbase : word) (rdraw : EntryDraw) (tid : word)
       (regs : bvmap 5 word) (mem : word -> option byte) : Prop := {
  me_ra  : getr regs 1 = Z_to_bv 64 0x18c6c;
  me_sp  : getr regs 2 = Z_to_bv 64 (bv_unsigned sp0 - 48);
  me_gp  : getr regs 3 = Z_to_bv 64 0x10800;
  me_tp  : getr regs 4 = Z_to_bv 64 0x72fc0;
  me_s0  : getr regs 8 = Z_to_bv 64 (bv_unsigned sp0 + 8);
  me_s1  : getr regs 9 = argcN inp;
  me_a0  : getr regs 10 = argcN inp;
  me_a1  : getr regs 11 = Z_to_bv 64 (bv_unsigned sp0 + 8);
  me_a2  : getr regs 12 = Z_to_bv 64 (bv_unsigned sp0 + 16 + 8 * Z.of_nat (length (in_argv inp)));
  me_s2  : getr regs 18 = Z_to_bv 64 0x148cc;
  me_s3  : getr regs 19 = Z_to_bv 64 (bv_unsigned sp0 + 16 + 8 * Z.of_nat (length (in_argv inp)));
  me_szero : forall r : reg, In r [20; 21; 22; 23; 24; 25; 26; 27]%list -> getr regs r = Z_to_bv 64 0;
  me_mem : exists (J : word -> option byte) (s1v : word),
             wfJ sp0 J /\ J = J_main sp0 inp mbase rdraw s1v
             /\ mem = cmem sp0 (wrap_mem inp mbase RPH ENT sp0 rdraw) J (D_main sp0 inp rdraw tid)
}.

Section Assembly.
  (* a worker port727 (): the launch as Common/ArgvEnv's Scaffold has it (VLAUNCH + LOK). *)
  Variable sp : word.
  Variable inp : ProcInput.
  Variables brk mbase : word.
#[local] Instance RC_a1_1 : RunCtx := mkRunCtx inp sp mbase.  (* a worker (A1) tool *)
  Variable draw : EntryDraw.
  Hypothesis Hva : valid_argv (in_argv inp).
  Hypothesis Hve : valid_envp (in_envp inp).
  Hypothesis Hvl : valid_launch inp.
  Hypothesis Hlau : entry_launch_ok_va Sv48 (mkEntry sp brk mbase draw) inp.
  Hypothesis Hvsp : valid_sp sp.

  Lemma Hlo : (0x7fff80000000 <= bv_unsigned sp)%Z.
  Proof. destruct Hvsp as [H _]. exact H. Qed.
  Lemma Hhi : (bv_unsigned sp <= 0x800000000000)%Z.
  Proof. destruct Hvsp as [_ [H _]]. exact H. Qed.
  Lemma Hal : (bv_unsigned sp mod 16 = 0)%Z.
  Proof. destruct Hvsp as [_ [_ H]]. exact H. Qed.

  Let J0 : word -> option byte := stack_zero (stack_window_lo (in_kernel inp) mbase draw).
  Lemma HJ0 : wfJ sp J0.
  Proof. exact (wfJ_stack_zero inp sp brk mbase draw Hvl Hlau). Qed.

  (* [comment removed for export] *)
  Ltac side Hva Hve HG :=
    first [ exact Hva | exact Hve | exact Hvl | exact Hlau | exact Hlo | exact Hhi | exact Hal | exact HG
          | exact HJ0 | apply wfJ_const
          | lazymatch goal with |- getr _ _ = _ =>
              gres; first [ assumption | reflexivity | bveq
                          | match goal with H : getr ?rs ?n = _ |- getr ?rs ?n = _ =>
                              rewrite H; unfold envp_w, envp_ptr, argv_w, pn_w, argc_w;
                              first [reflexivity | f_equal; lia | bveq] end ] end
          | idtac ].

  Theorem ref_startup_sec : forall lim K,
    (forall tid regs mem,
       (0 < bv_unsigned tid < 2^22)%Z ->
       main_entry sp inp mbase draw tid regs mem ->
       realizes (run_segments rsegs rc_inp rc_sp rc_mb) (mkCfg (mkst regs (0x148cc : word) mem (seg_rom (run_segments rsegs rc_inp rc_sp rc_mb)))
                             (with_tid tid (with_vdso (vdso_run_init (ed_vdso draw))
                                (init_model (segments_reserved rsegs) brk mbase sp lim inp)))) K) ->
    realizes (run_segments rsegs rc_inp rc_sp rc_mb) (init_config (run_segments rsegs rc_inp rc_sp rc_mb) rpc rph sp brk mbase draw lim inp) K.
  Proof.
    intros lim K HK.
    pose proof Hlo as Hlo'. pose proof Hhi as Hhi'. pose proof Hal as Hal'.
    pose proof (u64_range sp) as Hsp.
    unfold init_config. cbn [cfg_ms cfg_model]. rewrite segments_reserved_run.  (* a worker (A1) *)
    set (model := with_vdso (vdso_run_init (ed_vdso draw))
                    (init_model (segments_reserved rsegs) brk mbase sp lim inp)).
    assert (Hh : m_halted model = None) by reflexivity.
    assert (Hlazy : m_vm_lazy model = []) by reflexivity.
    assert (Ht0 : m_tid model = None) by reflexivity.
    set (RZ := fun st : machine_state => realizes (run_segments rsegs rc_inp rc_sp rc_mb) (mkCfg st model) K).
    assert (HG : bwd (run_segments rsegs rc_inp rc_sp rc_mb) RZ) by (apply bwd_rz; [exact Hh | exact Hlazy]).
    rewrite init_mkst.
    (* the pc only: the launch block keeps its [entry] (ENT) *)
    match goal with |- context [mkst ?R ENT ?M ?ROM] =>
      replace (mkst R ENT M ROM) with (mkst R (0x14780 : word) M ROM) by (f_equal; apply bv_eq; reflexivity)
    end.
    rewrite (cmem_init inp mbase rph ENT sp brk draw Hlau). fold (regs_init sp).
    (* [comment removed for export] *)
    destruct (p1_run sp inp mbase brk draw Hva Hvl Hlau Hlo' Hhi' Hal' (seg_rom (run_segments SEGS rc_inp rc_sp rc_mb)) J0 HJ0)
      as [regs1 (R1 & A1 & A2 & A3 & A4 & A8 & A9 & A10 & A11 & A12 & A18 & Az)].
    eapply rz_msteps; [exact Hh | exact Hlazy | exact R1 |].
    (* [comment removed for export] *)
    assert (A1' : getr regs1 1 = (0x1897c : word)) by (rewrite A1; apply bv_eq; reflexivity).
    destruct (memset304_run regs1 (cmem sp (wrap_mem inp mbase RPH ENT sp draw) (J1 sp inp J0) (fun _ => None))
                (seg_rom (run_segments SEGS rc_inp rc_sp rc_mb)) (Z_to_bv 64 (bv_unsigned sp - 368)) (0x1897c : word) A1')
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
    (* [comment removed for export] *)
    carry G2 A2 (2:reg) B2. carry G2 A8 (8:reg) B8. carry G2 A9 (9:reg) B9. carry G2 A10 (10:reg) B10.
    carry G2 A3 (3:reg) B3.
    change (realizes (run_segments SEGS rc_inp rc_sp rc_mb) (mkCfg ?st model) K) with (RZ st).
    eapply (p3_run sp inp mbase brk draw) with (G := RZ); try side Hva Hve HG.
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
    change (J1 sp inp J0) with (J_lsm sp inp J0).
    eapply (tls_c1 sp J0 inp mbase draw) with (G := RZ) (s1v := getr regs3 9) (tid := Z_to_bv 64 0); try side Hva Hve HG.
    intros regs4a; intros.
    eapply (tls_c2 sp J0 inp mbase draw) with (G := RZ) (tid := Z_to_bv 64 0); try side Hva Hve HG.
    intros regs4b; intros.
    eapply (tls_c3 sp J0 inp mbase draw) with (G := RZ) (tid := Z_to_bv 64 0); try side Hva Hve HG.
    intros regs4c; intros.
    eapply (tls_c4 sp J0 inp mbase draw) with (G := RZ) (tid := Z_to_bv 64 0); try side Hva Hve HG.
    intros regs4; intros.
    (* [comment removed for export] *)
    unfold RZ at 1.
    eapply (rz_set_tid (run_segments SEGS rc_inp rc_sp rc_mb) regs4 (0x18ecc : word) _ (seg_rom (run_segments SEGS rc_inp rc_sp rc_mb)) model K TW_18e84 TF_18e84 TE_18e84);
      [exact Hh | exact Hlazy | assumption | exact Ht0 |].
    intros tid Htid.
    replace (v_addi (0x18ecc : word) 4) with (0x18ed0 : word) by (apply bv_eq; reflexivity).
    set (model' := with_tid tid model).
    assert (Hh' : m_halted model' = None) by (unfold model'; rewrite with_tid_halted; exact Hh).
    assert (Hlazy' : m_vm_lazy model' = []) by (unfold model'; rewrite with_tid_lazy; exact Hlazy).
    set (RZ' := fun st : machine_state => realizes (run_segments rsegs rc_inp rc_sp rc_mb) (mkCfg st model') K).
    assert (HG' : bwd (run_segments rsegs rc_inp rc_sp rc_mb) RZ') by (apply bwd_rz; [exact Hh' | exact Hlazy']).
    change (realizes (run_segments SEGS rc_inp rc_sp rc_mb) (mkCfg ?st model') K) with (RZ' st).
    eapply (tls_c5 sp J0 inp mbase draw) with (G := RZ'); try side Hva Hve HG'.
    intros regs5; intros.
    eapply (fin_c6 sp J0 inp mbase brk draw) with (G := RZ'); try side Hva Hve HG'.
    intros regs6; intros.
    eapply (fin_c7 sp J0 inp mbase brk draw) with (G := RZ'); try side Hva Hve HG'.
    intros regs7; intros.
    eapply (fin_c8 sp J0 inp mbase brk draw) with (G := RZ'); try side Hva Hve HG'.
    intros regs8; intros.
    eapply (fin_c9 sp J0 inp mbase brk draw) with (G := RZ'); try side Hva Hve HG'.
    intros regs9 M1 M2 M3 M4 M8 M9 M10 M11 M12 M18 M19 M20 M21 M22 M23 M24 M25 M26 M27 G9.
    unfold RZ'. apply (HK tid regs9). { exact Htid. }
    split; try assumption.
    - intros r Hr. cbn [In] in Hr.
      repeat (destruct Hr as [<-|Hr]; [assumption|]). destruct Hr.
    - eexists _, (getr regs3 9). split; [|split; [reflexivity|]].
      + unfold J_main, J_tls, J_aux, J_aux0, J_lsm.
        destruct (kb_rseq (in_kernel inp)); repeat apply wfJ_wbytes; exact HJ0.
      + unfold J_main, J_tls, D_main, D_fd, D_ssp, D_tls, D_tlsA, D_tlsB. reflexivity.
  Qed.

End Assembly.

(* a worker port727 (): the launch facts are the ruled VLAUNCH + LOK (a worker); the model after the
   vDSO install is Run.init_config's own (with_vdso over init_model). No ProcInput destructuring is needed: the
   Section is over inp. *)
Theorem ref_startup : forall sp brk mbase draw lim inp K,
  valid_sp sp -> valid_brk rsegs brk -> valid_argv (in_argv inp) -> valid_envp (in_envp inp) ->
  valid_launch inp -> entry_launch_ok_va Sv48 (mkEntry sp brk mbase draw) inp ->
  (forall tid regs mem,
     (0 < bv_unsigned tid < 2^22)%Z ->
     main_entry sp inp mbase draw tid regs mem ->
     realizes (run_segments rsegs inp sp mbase) (mkCfg (mkst regs (0x148cc : word) mem (seg_rom (run_segments rsegs inp sp mbase)))
                           (with_tid tid (with_vdso (vdso_run_init (ed_vdso draw))
                              (init_model (segments_reserved rsegs) brk mbase sp lim inp)))) K) ->
  realizes (run_segments rsegs inp sp mbase) (init_config (run_segments rsegs inp sp mbase) rpc rph sp brk mbase draw lim inp) K.
Proof.
  intros sp brk mbase draw lim inp K Hsp Hbrk Hva Hve Hvl Hlau HK.
  apply ref_startup_sec; assumption.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section Consumers.
  Variable sp0 : word.
  Variable inp : ProcInput.
  Variable mbase : word.
#[local] Instance RC_a1_2 : RunCtx := mkRunCtx inp sp0 mbase.  (* a worker (A1) tool *)
  Variable rdraw : EntryDraw.   (* [comment removed for export] *)
  Variable tid : word.
  Variable regs : bvmap 5 word.
  Variable mem : word -> option byte.
  Hypothesis ME : main_entry sp0 inp mbase rdraw tid regs mem.

  (* [comment removed for export] *)
  Lemma main_entry_rdn_above : forall segs (a : word) n,
    (bv_unsigned sp0 <= bv_unsigned a)%Z ->
    (bv_unsigned a + Z.of_nat n <= 2^64)%Z ->
    rdn segs mem a n = rdn segs (wrap_mem inp mbase RPH ENT sp0 rdraw) a n.
  Proof.
    intros segs a n Ha Hn. destruct (me_mem _ _ _ _ _ _ _ ME) as (J & s1v & HJ & _ & ->).
    apply rdn_cmem_above; assumption.
  Qed.

  (* [comment removed for export] *)

  (* [comment removed for export] *)
  (* [comment removed for export] *)

  (* a worker port727 (): the ruled stack figure: every admissible launch maps [sp0 - 6144513, sp0)
     (MemSplit.wok_lo = sp0 + stack_window_reach - stack_max_size), not the whole 8 MiB below sp0. *)
  Lemma main_entry_store_ok_win : forall segs (a : word) n,
    (bv_unsigned sp0 - 6144513 <= bv_unsigned a)%Z ->
    (bv_unsigned a + Z.of_nat n <= bv_unsigned sp0)%Z ->
    store_ok segs mem a n = true.
  Proof.
    intros segs a n Hlo Hhi. destruct (me_mem _ _ _ _ _ _ _ ME) as (J & s1v & HJ & _ & ->).
    apply store_ok_cmem_win; [exact HJ | unfold wok_lo, stack_window_reach; rewrite stack_max_size_val; lia | lia].
  Qed.

  (* [comment removed for export] *)
  Lemma main_entry_mem_data : forall (a : word),
    (bv_unsigned a < bv_unsigned sp0 - stack_max_size)%Z ->
    mem a = D_main sp0 inp rdraw tid a.
  Proof.
    intros a Ha. destruct (me_mem _ _ _ _ _ _ _ ME) as (J & s1v & HJ & _ & ->).
    apply cmem_at_data. unfold win_lo. exact Ha.
  Qed.

  Lemma main_entry_rdn_data : forall segs (a : word) n,
    (bv_unsigned a + Z.of_nat n <= bv_unsigned sp0 - stack_max_size)%Z ->
    rdn segs mem a n = rdn segs (D_main sp0 inp rdraw tid) a n.
  Proof.
    intros segs a n Ha. destruct (me_mem _ _ _ _ _ _ _ ME) as (J & s1v & HJ & _ & ->).
    apply rdn_cmem_data. unfold win_lo. exact Ha.
  Qed.
End Consumers.
