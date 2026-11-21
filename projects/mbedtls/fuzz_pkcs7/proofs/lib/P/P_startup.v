(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (CDefT import and name table removed, bwd_rz, ref_startup_sec and ref_startup decoded to plain text; J_main takes the launch input, mmap base, entry point and zero window, main_entry's me_s1 and me_a0 read len_word and its me_mem names the launch with valid_launch and entry_launch_ok_va; ref_startup gains the channel-reader, valid_launch and entry_launch_ok_va premises and the vDSO initial model; the consumer lemmas replaced by main_entry_launch, and main_entry_store_ok_win restated over the wok_lo window). *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.mbedtls.fuzz_pkcs7.images Require Import Plain.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Shape.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.BB Require Import Amb ShapeX FileSim StartupTac ArgvEnv Layout.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Sys Require Import Nodes SysNodes.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.P Require Import P_img P_startup_defs P_startup1 P_startup_memset P_startup2 P_startup3 P_startup4 P_code_3b000_3c000.
Import ListNotations.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import PropExec.
#[local] Existing Instance PropExec.fx0.
Open Scope bv_scope.

Abbreviation SEGS := Plain.M.loaded_segments.
Abbreviation RPH := Plain.M.phdrs.
(* [comment removed for export] *)
Local Notation rsegs := Plain.M.loaded_segments (only parsing).
Local Notation rpc := Plain.M.init_pc (only parsing).
Local Notation rph := Plain.M.phdrs (only parsing).

Lemma bwd_rz : forall segs (model : Model) (K : TSet),
  m_halted model = None -> m_vm_lazy model = [] ->
  bwd segs (fun st : machine_state => realizes segs (mkCfg st model) K).
Proof.
  intros segs model K Hh Hlazy st st' Hms Hst'. eapply rz_msteps; eassumption.
Qed.

(* The window overlay at main's entry: the start-up's stack stores over the launch's own
   zero window [Jb] ([MemSplit.stack_zero] from [Run.stack_window_lo]). *)
Definition J_main (inp : ProcInput) (mbase entry sp0 : word) (rd : EntryDraw)
    (Jb : word -> option byte) (s1v : word) : word -> option byte :=
  let J6 := J_tls sp0 (J_aux sp0 inp mbase entry rd (J_lsm sp0 inp Jb))
              (Z_to_bv 64 0x3b9a4) (pn_w inp rd) s1v (Z_to_bv 64 0x79c50)
              (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) in
  wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes J6
    (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 0x3b9ac)))
    (Z_to_bv 64 (bv_unsigned sp0 - 8)) (word_to_le_bytes 8 (Z_to_bv 64 0)))
    (Z_to_bv 64 (bv_unsigned sp0 - 16)) (word_to_le_bytes 8 (Z_to_bv 64 0)))
    (Z_to_bv 64 (bv_unsigned sp0 - 24)) (word_to_le_bytes 8 (Z_to_bv 64 0)))
    (Z_to_bv 64 (bv_unsigned sp0 - 32)) (word_to_le_bytes 8 (Z_to_bv 64 0)))
    (Z_to_bv 64 (bv_unsigned sp0 - 40)) (word_to_le_bytes 8 (Z_to_bv 64 0)))
    (Z_to_bv 64 (bv_unsigned sp0 - 56)) (word_to_le_bytes 8 (Z_to_bv 64 0x3bba0)))
    (Z_to_bv 64 (bv_unsigned sp0 - 64)) (word_to_le_bytes 8 (argv_w sp0)))
    (Z_to_bv 64 (bv_unsigned sp0 - 72)) (word_to_le_bytes 8 (argc_w inp)))
    (Z_to_bv 64 (bv_unsigned sp0 - 88)) (word_to_le_bytes 8 (Z_to_bv 64 0x3baf0)))
    (Z_to_bv 64 (bv_unsigned sp0 - 96)) (word_to_le_bytes 8 (Z_to_bv 64 0x44c60)).

(* The start-up's hand-off state.  At the revision the stack block depends on the launch's own
   input (its kernel build, its exec file name, its gid), the mmap base and the entry point; [me_mem]
   names them existentially, so the record keeps its arguments: the input's fields the consumers read
   are [av], [ev] and the ambient uid/gid/AT_HWCAP/kernel/exec file name. *)
Record main_entry {AMB : Amb} (sp0 : word) (av ev : list (list byte))
       (tid : word) (rd : EntryDraw) (regs : bvmap 5 word) (mem : word -> option byte) : Prop := {
  me_ra  : getr regs 1 = Z_to_bv 64 0x3bbb0;
  me_sp  : getr regs 2 = Z_to_bv 64 (bv_unsigned sp0 - 48);
  me_gp  : getr regs 3 = Z_to_bv 64 0x10800;
  me_tp  : getr regs 4 = Z_to_bv 64 0x599c8;
  me_s0  : getr regs 8 = Z_to_bv 64 (bv_unsigned sp0 + 8);
  me_s1  : getr regs 9 = len_word av;
  me_a0  : getr regs 10 = len_word av;
  me_a1  : getr regs 11 = Z_to_bv 64 (bv_unsigned sp0 + 8);
  me_a2  : getr regs 12 = Z_to_bv 64 (bv_unsigned sp0 + 16 + 8 * Z.of_nat (length av));
  me_s2  : getr regs 18 = Z_to_bv 64 0x1cdcc;
  me_s3  : getr regs 19 = Z_to_bv 64 (bv_unsigned sp0 + 16 + 8 * Z.of_nat (length av));
  me_szero : forall r : reg, In r [20; 21; 22; 23; 24; 25; 26; 27]%list -> getr regs r = Z_to_bv 64 0;
  me_fits : entry_stack_fits sp0 av ev;
  me_mem : exists (inp : ProcInput) (mbase brk : word) (J : word -> option byte),
             in_argv inp = av /\ in_envp inp = ev /\ in_uid inp = a_uid /\ in_gid inp = a_gid
             /\ in_hwcap inp = a_hwcap /\ in_kernel inp = a_kernel /\ in_execfn inp = a_execfn
             /\ valid_launch inp /\ entry_launch_ok_va Sv48 (mkEntry sp0 brk mbase rd) inp
             /\ wfJ sp0 J
             /\ (exists (Jb : word -> option byte) (s1v : word), J = J_main inp mbase (0x1cc80 : word) sp0 rd Jb s1v)
             /\ mem = cmem sp0 (wrap_mem inp mbase RPH (0x1cc80 : word) sp0 rd) J (D_main sp0 inp rd tid)
}.

Section Assembly.
  Variable inp : ProcInput.
  Hypothesis Hrd : in_channel_reader inp = true.
  Variable rd : EntryDraw.
  Local Notation AMB := (amb_of inp Hrd (Vdso.vdso_run_init (ed_vdso rd))) (only parsing).
  Local Notation argv := (in_argv inp) (only parsing).
  Local Notation envp := (in_envp inp) (only parsing).
  Variable sp : word.
  Hypothesis Hva : valid_argv argv.
  Hypothesis Hve : valid_envp envp.
  Hypothesis Hvsp : valid_sp sp.
  Hypothesis Hfit : entry_stack_fits sp argv envp.
  Local Notation ENT := (0x1cc80 : word) (only parsing).

  Lemma Hlo : (0x7fff80000000 <= bv_unsigned sp)%Z.
  Proof using Hvsp. destruct Hvsp as [H _]. exact H. Qed.
  Lemma Hhi : (bv_unsigned sp <= 0x800000000000)%Z.
  Proof using Hvsp. destruct Hvsp as [_ [H _]]. exact H. Qed.
  Lemma Hal : (bv_unsigned sp mod 16 = 0)%Z.
  Proof using Hvsp. destruct Hvsp as [_ [_ H]]. exact H. Qed.

  (* [comment removed for export] *)
  Ltac side Hva Hve HG :=
    first [ exact Hva | exact Hve | exact Hlo | exact Hhi | exact Hal | exact HG
          | assumption
          | lazymatch goal with |- getr _ _ = _ =>
              gres; first [ assumption | reflexivity | bveq
                          | match goal with H : getr ?rs ?n = _ |- getr ?rs ?n = _ =>
                              rewrite H; unfold envp_w, envp_ptr, argv_w, pn_w, argc_w, argcN;
                              first [reflexivity | f_equal; lia | bveq] end ] end
          | idtac ].

  Theorem ref_startup_sec : forall brk mbase lim K,
    valid_launch inp ->
    entry_launch_ok_va Sv48 (mkEntry sp brk mbase rd) inp ->
    (forall tid regs mem,
       (0 < bv_unsigned tid < 2^22)%Z ->
       @main_entry AMB sp argv envp tid rd regs mem ->
       realizes rsegs (mkCfg (mkst regs (0x1cdcc : word) mem (seg_rom rsegs))
                             (with_tid tid (with_vdso (Vdso.vdso_run_init (ed_vdso rd))
                                (init_model (segments_reserved rsegs) brk mbase sp lim inp)))) K) ->
    realizes rsegs (init_config rsegs rpc rph sp brk mbase rd lim inp) K.
  Proof using Hrd Hva Hve Hvsp Hfit.
    intros brk mbase lim K Hvl Hlau HK.
    set (J0 := stack_zero (stack_window_lo (in_kernel inp) mbase rd)).
    assert (HJ0 : wfJ sp J0) by exact (wfJ_stack_zero inp sp brk mbase rd Hvl Hlau).
    pose proof Hlo as Hlo'. pose proof Hhi as Hhi'. pose proof Hal as Hal'.
    pose proof (u64_range sp) as Hsp.
    unfold init_config. cbn [cfg_ms cfg_model].
    set (model := with_vdso (Vdso.vdso_run_init (ed_vdso rd))
                    (init_model (segments_reserved rsegs) brk mbase sp lim inp)).
    assert (Hh : m_halted model = None) by reflexivity.
    assert (Hlazy : m_vm_lazy model = []) by reflexivity.
    assert (Ht0 : m_tid model = None) by reflexivity.
    set (RZ := fun st : machine_state => realizes rsegs (mkCfg st model) K).
    assert (HG : bwd rsegs RZ) by (apply bwd_rz; [exact Hh | exact Hlazy]).
    rewrite init_mkst.
    replace (Z_to_bv 64 (Z.of_N Plain.M.init_pc)) with (0x1cc80 : word) by (apply bv_eq; reflexivity).
    rewrite (cmem_init inp mbase RPH ENT sp brk rd Hlau). fold (regs_init sp). fold J0.
    (* [comment removed for export] *)
    destruct (p1_run Sv48 inp mbase ENT sp brk rd Hva Hve Hvl Hlau Hlo' Hhi' Hal' (seg_rom SEGS) J0 HJ0)
      as [regs1 (R1 & A1 & A2 & A3 & A4 & A8 & A9 & A10 & A11 & A12 & A18 & Az)].
    eapply rz_msteps; [exact Hh | exact Hlazy | exact R1 |].
    (* [comment removed for export] *)
    assert (A1' : getr regs1 1 = (0x3b8c0 : word)) by (rewrite A1; apply bv_eq; reflexivity).
    destruct (memset304_run regs1 (cmem sp (wrap_mem inp mbase RPH ENT sp rd) (J1 inp sp J0) (fun _ => None))
                (seg_rom SEGS) (Z_to_bv 64 (bv_unsigned sp - 368)) (0x3b8c0 : word) A1')
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
    eapply (p3_run Sv48 inp mbase ENT sp brk rd) with (G := RZ); try side Hva Hve HG.
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
    change (J1 inp sp J0) with (J_lsm sp inp J0).
    eapply (tls_c1 Sv48 inp mbase ENT sp brk rd J0) with (G := RZ) (s1v := getr regs3 9) (tid := Z_to_bv 64 0); try side Hva Hve HG.
    intros regs4a; intros.
    eapply (tls_c2 Sv48 inp mbase ENT sp brk rd J0) with (G := RZ) (tid := Z_to_bv 64 0); try side Hva Hve HG.
    intros regs4b; intros.
    eapply (tls_c3 Sv48 inp mbase ENT sp brk rd J0) with (G := RZ) (tid := Z_to_bv 64 0); try side Hva Hve HG.
    intros regs4c; intros.
    eapply (tls_c4 Sv48 inp mbase ENT sp brk rd J0) with (G := RZ) (tid := Z_to_bv 64 0); try side Hva Hve HG.
    intros regs4; intros.
    (* [comment removed for export] *)
    unfold RZ at 1.
    eapply (rz_set_tid SEGS regs4 (0x3be10 : word) _ (seg_rom SEGS) model K W_3bdbc F_3bdbc E_3bdbc);
      [exact Hh | exact Hlazy | assumption | exact Ht0 |].
    intros tid Htid.
    replace (v_addi (0x3be10 : word) 4) with (0x3be14 : word) by (apply bv_eq; reflexivity).
    set (model' := with_tid tid model).
    assert (Hh' : m_halted model' = None) by (unfold model'; rewrite with_tid_halted; exact Hh).
    assert (Hlazy' : m_vm_lazy model' = []) by (unfold model'; rewrite with_tid_lazy; exact Hlazy).
    set (RZ' := fun st : machine_state => realizes rsegs (mkCfg st model') K).
    assert (HG' : bwd rsegs RZ') by (apply bwd_rz; [exact Hh' | exact Hlazy']).
    change (realizes SEGS (mkCfg ?st model') K) with (RZ' st).
    eapply (tls_c5 Sv48 inp mbase ENT sp brk rd J0) with (G := RZ'); try side Hva Hve HG'.
    intros regs5; intros.
    eapply (fin_c6 Sv48 inp mbase ENT sp brk rd J0) with (G := RZ'); try side Hva Hve HG'.
    intros regs6; intros.
    eapply (fin_c7 Sv48 inp mbase ENT sp brk rd J0) with (G := RZ'); try side Hva Hve HG'.
    intros regs7; intros.
    eapply (fin_c8 Sv48 inp mbase ENT sp brk rd J0) with (G := RZ'); try side Hva Hve HG'.
    intros regs8; intros.
    eapply (fin_c9 Sv48 inp mbase ENT sp brk rd J0) with (G := RZ'); try side Hva Hve HG'.
    intros regs9 M1 M2 M3 M4 M8 M9 M10 M11 M12 M18 M19 M20 M21 M22 M23 M24 M25 M26 M27 G9.
    unfold RZ'. apply (HK tid regs9). { exact Htid. }
    split; try assumption.
    - intros r Hr. cbn [In] in Hr.
      repeat (destruct Hr as [<-|Hr]; [assumption|]). destruct Hr.
    - exists inp, mbase, brk, (J_main inp mbase ENT sp rd J0 (getr regs3 9)).
      do 7 (split; [reflexivity|]).
      split; [exact Hvl|]. split; [exact Hlau|].
      split; [|split; [exists J0, (getr regs3 9); reflexivity|]].
      + unfold J_main, J_tls, J_aux, J_lsm. repeat apply wfJ_wbytes. exact HJ0.
      + unfold J_main, J_tls, D_main, D_fd, D_ssp, D_tls, D_tlsA, D_tlsB. reflexivity.
  Qed.

End Assembly.

(* [comment removed for export] *)
Theorem ref_startup : forall sp brk mbase (rd : EntryDraw) (lim : Z) (inp : ProcInput) (K : TSet)
  (Hrd : in_channel_reader inp = true),
  valid_sp sp -> valid_brk rsegs brk ->
  valid_argv (in_argv inp) -> valid_envp (in_envp inp) ->
  entry_stack_fits sp (in_argv inp) (in_envp inp) ->
  valid_launch inp -> entry_launch_ok_va Sv48 (mkEntry sp brk mbase rd) inp ->
  (forall tid regs mem,
     (0 < bv_unsigned tid < 2^22)%Z ->
     @main_entry (amb_of inp Hrd (Vdso.vdso_run_init (ed_vdso rd))) sp (in_argv inp) (in_envp inp) tid rd regs mem ->
     realizes rsegs (mkCfg (mkst regs (0x1cdcc : word) mem (seg_rom rsegs))
                           (with_tid tid (with_vdso (Vdso.vdso_run_init (ed_vdso rd))
                              (init_model (segments_reserved rsegs) brk mbase sp lim inp)))) K) ->
  realizes rsegs (init_config rsegs rpc rph sp brk mbase rd lim inp) K.
Proof.
  intros sp brk mbase rd lim inp K Hrd Hsp Hbrk Hva Hve Hfit Hvl Hlau HK.
  exact (ref_startup_sec inp Hrd rd sp Hva Hve Hsp Hfit brk mbase lim K Hvl Hlau HK).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section Consumers.
  Context {AMB : Amb}.
  Variable sp0 : word.
  Variables av ev : list (list byte).
  Variable tid : word.
  Variable rd : EntryDraw.
  Variable regs : bvmap 5 word.
  Variable mem : word -> option byte.
  Hypothesis ME : main_entry sp0 av ev tid rd regs mem.

  (* The launch [main_entry] hides, with the facts the consumers read. *)
  Lemma main_entry_launch : exists (inp : ProcInput) (mbase brk : word),
    in_argv inp = av /\ in_envp inp = ev /\ in_uid inp = a_uid /\ in_gid inp = a_gid
    /\ in_hwcap inp = a_hwcap /\ in_kernel inp = a_kernel /\ in_execfn inp = a_execfn
    /\ valid_launch inp /\ entry_launch_ok_va Sv48 (mkEntry sp0 brk mbase rd) inp
    /\ (forall segs (a : word) n,
          (bv_unsigned sp0 <= bv_unsigned a)%Z -> (bv_unsigned a + Z.of_nat n <= 2^64)%Z ->
          rdn segs mem a n = rdn segs (wrap_mem inp mbase RPH (0x1cc80 : word) sp0 rd) a n)
    /\ (forall (a : word), (bv_unsigned a < bv_unsigned sp0 - stack_max_size)%Z ->
          mem a = D_main sp0 inp rd tid a)
    /\ (forall segs (a : word) n, (bv_unsigned a + Z.of_nat n <= bv_unsigned sp0 - stack_max_size)%Z ->
          rdn segs mem a n = rdn segs (D_main sp0 inp rd tid) a n).
  Proof using ME.
    destruct (me_mem _ _ _ _ _ _ _ ME)
      as (inp & mbase & brk & J & E1 & E2 & E3 & E4 & E5 & E6 & E7 & Hvl & Hlau & HJ & _ & ->).
    exists inp, mbase, brk.
    do 9 (split; [assumption|]).
    split; [intros segs a n Ha Hn; apply rdn_cmem_above; assumption|].
    split; [intros a Ha; apply cmem_at_data; unfold win_lo; exact Ha|].
    intros segs a n Ha. apply rdn_cmem_data. unfold win_lo. exact Ha.
  Qed.

  (* At the revision the window every launch maps starts at [wok_lo] ([MemSplit.wfJ]),
     not at [sp0 - stack_max_size]. *)
  Lemma main_entry_store_ok_win : forall segs (a : word) n,
    (wok_lo sp0 <= bv_unsigned a)%Z ->
    (bv_unsigned a + Z.of_nat n <= bv_unsigned sp0)%Z ->
    store_ok segs mem a n = true.
  Proof using ME.
    intros segs a n Hlo Hhi.
    destruct (me_mem _ _ _ _ _ _ _ ME) as (inp & mbase & brk & J & _ & _ & _ & _ & _ & _ & _ & _ & _ & HJ & _ & ->).
    pose proof (win_lo_le_wok_lo sp0).
    apply store_ok_cmem_win; [exact HJ | lia | lia].
  Qed.
End Consumers.
