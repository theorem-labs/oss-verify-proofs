(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (the start-up over the launch input ProcInput, its mmap base, entry point and entry draw, the CONFIG_RSEQ flag, the vDSO model and the init stack window; main_entry over the launch input), as bzip2/bzip2_compress_target's start-up was. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
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
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.varnish.esi_parse_fuzzer.images Require Import Ubsan.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Amb ShapeAlg Nodes RefNodes.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require MmapSim.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Star5ef ArgvEnv RefL1zx.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require RefL1zx.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require DU_Ssji DU_Shm0.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require DU_Sf1h.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require DU_S4e6.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require DU_S4e6 DU_Sf1h DU_co77 DU_cb3t.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Amb OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.ShapeAlg OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Nodes OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.RefNodes OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.MmapSim.FileSim OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Star5ef OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.ArgvEnv OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.RefL1zx OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.RefL1zx.DU_Img OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.DU_Ssji OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.DU_Shm0 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.DU_Sf1h.DU_Mv2g OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.DU_S4e6.DU_S428 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.DU_S4e6 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.DU_Sf1h OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.DU_co77 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.DU_cb3t.
(* [comment removed for export] *)
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_noeuclid ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_post_hook.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require LiaLt.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import BWorld.
Local Ltac lia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaLt.lia_tuned.
(* [comment removed for export] *)
Import ListNotations.
Open Scope bv_scope.

Abbreviation SEGS := Ubsan.M.loaded_segments.
Abbreviation RPH := Ubsan.M.phdrs.
(* [comment removed for export] *)
Local Notation rsegs := Ubsan.M.loaded_segments (only parsing).
Local Notation rpc := Ubsan.M.init_pc (only parsing).
Local Notation rph := Ubsan.M.phdrs (only parsing).

(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma bwd_rz {BW : BWorld} : forall segs model K,
  m_halted model = None -> m_vm_lazy model = [] ->
  bwd segs (fun st => realizes segs (mkCfg st model) K).
Proof.
  intros segs model K Hh Hlazy st st' Hms Hst'. eapply rz_msteps; eassumption.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition J_main (inp : ProcInput) (mbase entry sp0 : word) (rdraw : EntryDraw)
    (s1v : word) : word -> option byte :=
  let J6 := J_tls sp0 (J_aux inp mbase entry sp0 rdraw (J_lsm inp sp0
                         (stack_zero (stack_window_lo (in_kernel inp) mbase rdraw))))
              (Z_to_bv 64 0x22570) (pn_w inp rdraw) s1v (Z_to_bv 64 0x62788)
              (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) in
  wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes J6
    (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 0x22578)))   (* [comment removed for export] *)
    (Z_to_bv 64 (bv_unsigned sp0 - 8)) (word_to_le_bytes 8 (Z_to_bv 64 0)))           (* [comment removed for export] *)
    (Z_to_bv 64 (bv_unsigned sp0 - 16)) (word_to_le_bytes 8 (Z_to_bv 64 0)))          (* [comment removed for export] *)
    (Z_to_bv 64 (bv_unsigned sp0 - 24)) (word_to_le_bytes 8 (Z_to_bv 64 0)))          (* [comment removed for export] *)
    (Z_to_bv 64 (bv_unsigned sp0 - 32)) (word_to_le_bytes 8 (Z_to_bv 64 0)))          (* [comment removed for export] *)
    (Z_to_bv 64 (bv_unsigned sp0 - 40)) (word_to_le_bytes 8 (Z_to_bv 64 0)))          (* [comment removed for export] *)
    (Z_to_bv 64 (bv_unsigned sp0 - 56)) (word_to_le_bytes 8 (Z_to_bv 64 0x2276c)))    (* [comment removed for export] *)
    (Z_to_bv 64 (bv_unsigned sp0 - 64)) (word_to_le_bytes 8 (argv_w sp0)))             (* [comment removed for export] *)
    (Z_to_bv 64 (bv_unsigned sp0 - 72)) (word_to_le_bytes 8 (argc_w inp)))              (* [comment removed for export] *)
    (Z_to_bv 64 (bv_unsigned sp0 - 88)) (word_to_le_bytes 8 (Z_to_bv 64 0x226bc)))    (* [comment removed for export] *)
    (Z_to_bv 64 (bv_unsigned sp0 - 96)) (word_to_le_bytes 8 (Z_to_bv 64 0x30608)).    (* [comment removed for export] *)

(* [comment removed for export] *)
Record main_entry (inp : ProcInput) (mbase entry sp0 : word)
       (rdraw : EntryDraw) (tid : word)
       (regs : bvmap 5 word) (mem : word -> option byte) : Prop := {
  me_ra  : getr regs 1 = Z_to_bv 64 0x2277c;
  me_sp  : getr regs 2 = Z_to_bv 64 (bv_unsigned sp0 - 48);
  me_gp  : getr regs 3 = Z_to_bv 64 0x10800;
  me_tp  : getr regs 4 = Z_to_bv 64 0x424f8;
  me_s0  : getr regs 8 = Z_to_bv 64 (bv_unsigned sp0 + 8);
  me_s1  : getr regs 9 = argcN inp;
  me_a0  : getr regs 10 = argcN inp;
  me_a1  : getr regs 11 = Z_to_bv 64 (bv_unsigned sp0 + 8);
  me_a2  : getr regs 12 = Z_to_bv 64 (bv_unsigned sp0 + 16 + 8 * Z.of_nat (length (in_argv inp)));
  me_s2  : getr regs 18 = Z_to_bv 64 0x17b98;
  me_s3  : getr regs 19 = Z_to_bv 64 (bv_unsigned sp0 + 16 + 8 * Z.of_nat (length (in_argv inp)));
  me_szero : forall r : reg, In r [20; 21; 22; 23; 24; 25; 26; 27]%list -> getr regs r = Z_to_bv 64 0;
  me_mem : exists (J : word -> option byte) (s1v : word),
             wfJ sp0 J /\ J = J_main inp mbase entry sp0 rdraw s1v
             /\ mem = cmem sp0 (wrap_mem inp mbase RPH entry sp0 rdraw) J (D_main inp sp0 rdraw tid)
}.

Section Assembly.
  Context {BW : BWorld}.
  Variable inp : ProcInput.
  Variable mbase : word.
  Variable sp brk : word.
  Variable rdraw : EntryDraw.
  Hypothesis Hva : valid_argv (in_argv inp).
  Hypothesis Hve : valid_envp (in_envp inp).
  Hypothesis Hvl : valid_launch inp.
  Hypothesis Hlau : entry_launch_ok_va Sv48 (mkEntry sp brk mbase rdraw) inp.
  Hypothesis Hvsp : valid_sp sp.

  #[using="Hvsp"] Lemma Hlo : (0x7fff80000000 <= bv_unsigned sp)%Z.
  Proof. destruct Hvsp as [H _]. exact H. Qed.
  #[using="Hvsp"] Lemma Hhi : (bv_unsigned sp <= 0x800000000000)%Z.
  Proof. destruct Hvsp as [_ [H _]]. exact H. Qed.
  #[using="Hvsp"] Lemma Hal : (bv_unsigned sp mod 16 = 0)%Z.
  Proof. destruct Hvsp as [_ [_ H]]. exact H. Qed.

  (* The zero-filled stack window below sp, from [stack_window_lo] ([Run.init_machine_state]). *)
  Let J0 : word -> option byte :=
    stack_zero (stack_window_lo (in_kernel inp) mbase rdraw).

  #[using="Hvl Hlau"] Lemma HJ0 : wfJ sp J0.
  Proof. exact (wfJ_stack_zero inp sp brk mbase rdraw Hvl Hlau). Qed.

  (* [comment removed for export] *)
  Ltac side Hva Hve HG :=
    first [ exact Hva | exact Hve | exact Hvl | exact Hlau | exact Hlo | exact Hhi | exact Hal | exact HG
          | exact HJ0
          | apply (wfJ_stack_zero inp sp brk mbase rdraw Hvl Hlau)
          | apply wfJ_const
          | lazymatch goal with |- getr _ _ = _ =>
              gres; first [ assumption | reflexivity | bveq
                          | match goal with H : getr ?rs ?n = _ |- getr ?rs ?n = _ =>
                              rewrite H; unfold envp_w, envp_ptr, argv_w, pn_w, argc_w;
                              first [reflexivity | f_equal; lia | bveq] end ] end
          | idtac ].

  #[using="J0 Hvsp Hve Hva Hvl Hlau"] Theorem ref_startup_sec : forall lim K,
    (forall tid regs mem,
       (0 < bv_unsigned tid < 2^22)%Z ->
       main_entry inp mbase (0x17a4c : word) sp rdraw tid regs mem ->
       realizes rsegs (mkCfg (mkst regs (0x17b98 : word) mem (seg_rom rsegs))
                             (with_tid tid (with_vdso (Vdso.vdso_run_init (ed_vdso rdraw))
                                (init_model (segments_reserved rsegs) brk mbase sp lim inp)))) K) ->
    realizes rsegs (init_config rsegs rpc rph sp brk mbase rdraw lim inp) K.
  Proof.
    intros lim K HK.
    pose proof Hlo as Hlo'. pose proof Hhi as Hhi'. pose proof Hal as Hal'.
    pose proof (u64_range sp) as Hsp.
    unfold init_config. cbn [cfg_ms cfg_model].
    (* LPS 727298f3: [Run.init_config] installs the run's vDSO draw over [init_model] *)
    set (model := with_vdso (Vdso.vdso_run_init (ed_vdso rdraw)) (init_model (segments_reserved rsegs) brk mbase sp lim inp)).
    assert (Hh : m_halted model = None) by reflexivity.
    assert (Hlazy : m_vm_lazy model = []) by reflexivity.
    assert (Ht0 : m_tid model = None) by reflexivity.
    set (RZ := fun st : machine_state => realizes rsegs (mkCfg st model) K).
    assert (HG : bwd rsegs RZ) by (apply bwd_rz; [exact Hh | exact Hlazy]).
    rewrite init_mkst.
    replace (Z_to_bv 64 (Z.of_N Ubsan.M.init_pc)) with (0x17a4c : word) by (apply bv_eq; reflexivity).
    rewrite (cmem_init inp mbase rph (0x17a4c : word) sp brk rdraw Hlau).
    fold (regs_init sp).
    (* [comment removed for export] *)
    destruct (p1_run sp inp mbase (0x17a4c : word) rdraw Hva Hve Hlo' Hhi' Hal' (seg_rom SEGS) J0 HJ0)
      as [regs1 (R1 & A1 & A2 & A3 & A4 & A8 & A9 & A10 & A11 & A12 & A18 & Az)].
    eapply rz_msteps; [exact Hh | exact Hlazy | exact R1 |].
    (* [comment removed for export] *)
    assert (A1' : getr regs1 1 = (0x2248c : word)) by (rewrite A1; apply bv_eq; reflexivity).
    destruct (memset304_run regs1 (cmem sp (wrap_mem inp mbase RPH (0x17a4c : word) sp rdraw) (J1 sp inp J0) (fun _ => None))
                (seg_rom SEGS) (Z_to_bv 64 (bv_unsigned sp - 368)) (0x2248c : word) A1')
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
    change (realizes SEGS (mkCfg ?st model) K) with (RZ st).
    eapply (p3_run Sv48 inp mbase (0x17a4c : word) sp brk rdraw
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
    change (J1 sp inp J0) with (J_lsm inp sp J0).
    eapply (tls_c1 Sv48 inp mbase (0x17a4c : word) sp brk J0 rdraw
              Hva Hve Hvl Hlau Hlo Hhi Hal) with (G := RZ) (s1v := getr regs3 9) (tid := Z_to_bv 64 0); try side Hva Hve HG.
    intros regs4a; intros.
    eapply (tls_c2 Sv48 inp mbase (0x17a4c : word) sp brk J0 rdraw
              Hva Hve Hvl Hlau Hlo Hhi Hal) with (G := RZ) (tid := Z_to_bv 64 0); try side Hva Hve HG.
    intros regs4b; intros.
    eapply (tls_c3 Sv48 inp mbase (0x17a4c : word) sp brk J0 rdraw
              Hva Hve Hvl Hlau Hlo Hhi Hal) with (G := RZ) (tid := Z_to_bv 64 0); try side Hva Hve HG.
    intros regs4c; intros.
    eapply (tls_c4 Sv48 inp mbase (0x17a4c : word) sp brk J0 rdraw
              Hva Hve Hvl Hlau Hlo Hhi Hal) with (G := RZ) (tid := Z_to_bv 64 0); try side Hva Hve HG.
    intros regs4; intros.
    (* [comment removed for export] *)
    unfold RZ at 1.
    eapply (rz_set_tid SEGS regs4 (0x229dc : word) _ (seg_rom SEGS) model K W_229dc F_229dc E_229dc);
      [exact Hh | exact Hlazy | assumption | exact Ht0 |].
    intros tid Htid.
    replace (v_addi (0x229dc : word) 4) with (0x229e0 : word) by (apply bv_eq; reflexivity).
    set (model' := with_tid tid model).
    assert (Hh' : m_halted model' = None) by (unfold model'; rewrite with_tid_halted; exact Hh).
    assert (Hlazy' : m_vm_lazy model' = []) by (unfold model'; rewrite with_tid_lazy; exact Hlazy).
    set (RZ' := fun st : machine_state => realizes rsegs (mkCfg st model') K).
    assert (HG' : bwd rsegs RZ') by (apply bwd_rz; [exact Hh' | exact Hlazy']).
    change (realizes SEGS (mkCfg ?st model') K) with (RZ' st).
    eapply (tls_c5 Sv48 inp mbase (0x17a4c : word) sp brk J0 rdraw
              Hva Hve Hvl Hlau Hlo Hhi Hal) with (G := RZ'); try side Hva Hve HG'.
    intros regs5; intros.
    eapply (fin_c6 Sv48 inp mbase (0x17a4c : word) sp brk J0 rdraw
              Hva Hve Hvl Hlau Hlo Hhi Hal) with (G := RZ'); try side Hva Hve HG'.
    intros regs6; intros.
    eapply (fin_c7 Sv48 inp mbase (0x17a4c : word) sp brk J0 rdraw
              Hva Hve Hvl Hlau Hlo Hhi Hal) with (G := RZ'); try side Hva Hve HG'.
    intros regs7; intros.
    eapply (fin_c8 Sv48 inp mbase (0x17a4c : word) sp brk J0 rdraw
              Hva Hve Hvl Hlau Hlo Hhi Hal) with (G := RZ'); try side Hva Hve HG'.
    intros regs8; intros.
    eapply (fin_c9 Sv48 inp mbase (0x17a4c : word) sp brk J0 rdraw
              Hva Hve Hvl Hlau Hlo Hhi Hal) with (G := RZ'); try side Hva Hve HG'.
    intros regs9 M1 M2 M3 M4 M8 M9 M10 M11 M12 M18 M19 M20 M21 M22 M23 M24 M25 M26 M27 G9.
    unfold RZ'. apply (HK tid regs9). { exact Htid. }
    split; try assumption.
    - intros r Hr. cbn [In] in Hr.
      repeat (destruct Hr as [<-|Hr]; [assumption|]). destruct Hr.
    - eexists _, (getr regs3 9). split; [|split; [reflexivity|]].
      + unfold J_main, J_tls, J_aux, J_rseq, J_lsm.
        destruct (kb_rseq (in_kernel inp)); repeat apply wfJ_wbytes; exact HJ0.
      + unfold J_main, J_tls, D_main, D_fd, D_ssp, D_tls, D_tlsA, D_tlsB. reflexivity.
  Qed.

End Assembly.

(* [comment removed for export] *)
(* The launch facts are premises a lib lemma may take: [valid_launch] and [entry_launch_ok_va]
   are conjuncts of [valid_input] / [valid_entry], which the top theorems discharge. *)
Theorem ref_startup {BW : BWorld} : forall sp brk mbase rdraw lim inp K,
  valid_sp sp -> valid_brk rsegs brk -> valid_argv (in_argv inp) -> valid_envp (in_envp inp) ->
  in_abort_terminal inp = false ->
  valid_launch inp ->
  entry_launch_ok_va Sv48 (mkEntry sp brk mbase rdraw) inp ->
  (forall tid regs mem,
     (0 < bv_unsigned tid < 2^22)%Z ->
     main_entry inp mbase (0x17a4c : word) sp rdraw tid regs mem ->
     realizes rsegs (mkCfg (mkst regs (0x17b98 : word) mem (seg_rom rsegs))
                           (with_tid tid (with_vdso (Vdso.vdso_run_init (ed_vdso rdraw))
                              (init_model (segments_reserved rsegs) brk mbase sp lim inp)))) K) ->
  realizes rsegs (init_config rsegs rpc rph sp brk mbase rdraw lim inp) K.
Proof.
  intros sp brk mbase rdraw lim inp K Hsp Hbrk Hva Hve Hab Hvl Hlau HK.
  eapply ref_startup_sec; eassumption.
Qed.

(* The launch input read back through the AMB world the consumers are stated in: an input
   whose abort flag is clear is [mkProcInputC (amb_of inp) ..] field for field. *)
Lemma main_entry_C_of : forall inp mbase entry sp0 rdraw tid regs mem,
  in_abort_terminal inp = false ->
  main_entry inp mbase entry sp0 rdraw tid regs mem ->
  main_entry (@mkProcInputC (amb_of inp) (in_argv inp) (in_envp inp) (in_fs inp) (in_stdin inp))
    mbase entry sp0 rdraw tid regs mem.
Proof.
  intros [av ev fs si u g gs n nf sm hw ab va ur tm kb ex cr sd st] mbase entry sp0 rdraw tid regs mem Hab ME.
  cbn in Hab. subst ab. destruct ME; constructor; assumption.
Qed.

Lemma valid_launch_C_of : forall inp,
  in_abort_terminal inp = false -> valid_launch inp ->
  valid_launch (@mkProcInputC (amb_of inp) (in_argv inp) (in_envp inp) (in_fs inp) (in_stdin inp)).
Proof.
  intros [av ev fs si u g gs n nf sm hw ab va ur tm kb ex cr sd st] Hab H.
  cbn in Hab. subst ab. exact H.
Qed.

Lemma entry_launch_ok_C_of : forall inp sp brk mbase rdraw,
  in_abort_terminal inp = false ->
  entry_launch_ok_va Sv48 (mkEntry sp brk mbase rdraw) inp ->
  entry_launch_ok_va Sv48 (mkEntry sp brk mbase rdraw)
    (@mkProcInputC (amb_of inp) (in_argv inp) (in_envp inp) (in_fs inp) (in_stdin inp)).
Proof.
  intros [av ev fs si u g gs n nf sm hw ab va ur tm kb ex cr sd st] sp brk mbase rdraw Hab H.
  cbn in Hab. subst ab. exact H.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section Consumers.
  Variable inp : ProcInput.
  Variable mbase entry : word.
  Variable sp0 : word.
  Variable rdraw : EntryDraw.
  Variable tid : word.
  Variable regs : bvmap 5 word.
  Variable mem : word -> option byte.
  Hypothesis ME : main_entry inp mbase entry sp0 rdraw tid regs mem.

  (* [comment removed for export] *)
  #[using="ME regs tid"] Lemma main_entry_rdn_above : forall segs (a : word) n,
    (bv_unsigned sp0 <= bv_unsigned a)%Z ->
    (bv_unsigned a + Z.of_nat n <= 2^64)%Z ->
    rdn segs mem a n = rdn segs (wrap_mem inp mbase RPH entry sp0 rdraw) a n.
  Proof.
    intros segs a n Ha Hn. destruct (me_mem _ _ _ _ _ _ _ _ ME) as (J & s1v & HJ & _ & ->).
    apply rdn_cmem_above; assumption.
  Qed.

  (* [comment removed for export] *)

  (* LPS 727298f3: the window main_entry gives is the stack span from [wok_lo sp0]
     (= sp0 - 6144513, MemSplit.store_ok_cmem_win), no longer [sp0 - stack_max_size], which is
     the allocator ceiling and stays with the data half below. *)
  #[using="ME regs tid"] Lemma main_entry_win_mapped : forall (a : word),
    (wok_lo sp0 <= bv_unsigned a < bv_unsigned sp0)%Z -> mem a <> None.
  Proof.
    intros a Ha. destruct (me_mem _ _ _ _ _ _ _ _ ME) as (J & s1v & HJ & _ & ->).
    rewrite cmem_at_win by (unfold in_win; lia). apply HJ. unfold in_win. lia.
  Qed.

  #[using="ME regs tid"] Lemma main_entry_store_ok_win : forall segs (a : word) n,
    (wok_lo sp0 <= bv_unsigned a)%Z ->
    (bv_unsigned a + Z.of_nat n <= bv_unsigned sp0)%Z ->
    store_ok segs mem a n = true.
  Proof.
    intros segs a n Hlo Hhi. destruct (me_mem _ _ _ _ _ _ _ _ ME) as (J & s1v & HJ & _ & ->).
    apply store_ok_cmem_win; [exact HJ | exact Hlo | exact Hhi].
  Qed.

  (* [comment removed for export] *)
  #[using="ME regs"] Lemma main_entry_mem_data : forall (a : word),
    (bv_unsigned a < bv_unsigned sp0 - stack_max_size)%Z ->
    mem a = D_main inp sp0 rdraw tid a.
  Proof.
    intros a Ha. destruct (me_mem _ _ _ _ _ _ _ _ ME) as (J & s1v & HJ & _ & ->).
    apply cmem_at_data. unfold win_lo. exact Ha.
  Qed.

  #[using="ME regs"] Lemma main_entry_rdn_data : forall segs (a : word) n,
    (bv_unsigned a + Z.of_nat n <= bv_unsigned sp0 - stack_max_size)%Z ->
    rdn segs mem a n = rdn segs (D_main inp sp0 rdraw tid) a n.
  Proof.
    intros segs a n Ha. destruct (me_mem _ _ _ _ _ _ _ _ ME) as (J & s1v & HJ & _ & ->).
    apply rdn_cmem_data. unfold win_lo. exact Ha.
  Qed.
End Consumers.
