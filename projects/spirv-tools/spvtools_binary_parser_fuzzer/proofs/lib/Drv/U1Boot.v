(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import ArgvEnv RefLayout.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.Cls Require Import ClsTac.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.Drv Require Import U1BootCode U1BootDefs U1Boot1 U1BootMemset U1Boot2 U1Boot3 U1Boot3b U1Boot4.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import RefMemcpyLib.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.

Section Img.
  Variable SEGS : list Segment.
  Hypothesis HX : u1b_ok SEGS = true.

Lemma with_tid_halted : forall t m, m_halted (with_tid t m) = m_halted m.
Proof. intros t m. destruct m; reflexivity. Qed.
Lemma with_tid_lazy : forall t m, m_vm_lazy (with_tid t m) = m_vm_lazy m.
Proof. intros t m. destruct m; reflexivity. Qed.

Definition J8 (sp0 : word) (av ev : list (list byte)) (uid hw : word) (Jb : word -> option byte) (s1v : word)
    : word -> option byte :=
  (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 av ev uid hw (J_lsm sp0 av Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 857596))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w sp0 av ev))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 1189544))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 857604))) (Z_to_bv 64 (bv_unsigned sp0 - 8)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 16)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 24)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 32)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 40)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 56)) (word_to_le_bytes 8 (Z_to_bv 64 858104))) (Z_to_bv 64 (bv_unsigned sp0 - 64)) (word_to_le_bytes 8 (Z_to_bv 64 (bv_unsigned sp0 + 8)))) (Z_to_bv 64 (bv_unsigned sp0 - 72)) (word_to_le_bytes 8 (argc_w av))).
Definition D8 (sp0 : word) (av ev : list (list byte)) (hw tid : word) (rdraw : EntryDraw) : word -> option byte :=
  (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (D_libc sp0 av ev hw) (Z_to_bv 64 1188928) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 1188944) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 1188936) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 1189568) (word_to_le_bytes 8 (Z_to_bv 64 224))) (Z_to_bv 64 1189576) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 1057832) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 1057808) (word_to_le_bytes 8 (Z_to_bv 64 1057832))) (Z_to_bv 64 1057616) (word_to_le_bytes 8 (Z_to_bv 64 1057616))) (Z_to_bv 64 1189544) ([Z_to_bv 8 1])) (Z_to_bv 64 1057656) (word_to_le_bytes 4 (Z_to_bv 64 2))) (Z_to_bv 64 1057648) (word_to_le_bytes 4 tid)) (Z_to_bv 64 1057768) (word_to_le_bytes 8 (Z_to_bv 64 1189600))) (Z_to_bv 64 1057736) (word_to_le_bytes 8 (Z_to_bv 64 1057736))) (Z_to_bv 64 1057624) (word_to_le_bytes 8 (Z_to_bv 64 1057616))) (Z_to_bv 64 1057632) (word_to_le_bytes 8 (Z_to_bv 64 1057616))) (Z_to_bv 64 1057640) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 1189512) (word_to_le_bytes 4 (LWv (firstn 4 (skipn 0 (at_random_bytes (ed_random rdraw))))))) (Z_to_bv 64 1189516) (word_to_le_bytes 4 (LWv (firstn 4 (skipn 4 (at_random_bytes (ed_random rdraw))))))) (Z_to_bv 64 1189513) [Z_to_bv 8 0]) (Z_to_bv 64 1057800) (word_to_le_bytes 8 (canary rdraw))).

Record cxx_entry (sp0 : word) (rdraw : EntryDraw) (av ev : list (list byte)) (uid hw tid : word)
       (regs : bvmap 5 word) (mem : word -> option byte) : Prop := {
  ce_ra  : getr regs 1 = Z_to_bv 64 857928;
  ce_sp  : getr regs 2 = Z_to_bv 64 (bv_unsigned sp0 - 80);
  ce_gp  : getr regs 3 = Z_to_bv 64 67584;
  ce_tp  : getr regs 4 = Z_to_bv 64 1057816;
  ce_s0  : getr regs 8 = Z_to_bv 64 953456;
  ce_s1  : getr regs 9 = Z_to_bv 64 953440;
  ce_s2  : getr regs 18 = Z_to_bv 64 415804;
  ce_s3  : getr regs 19 = Z_to_bv 64 (bv_unsigned sp0 + 16 + 8 * Z.of_nat (length av));
  ce_szero : forall r : reg, In r [20; 21; 22; 23; 24; 25; 26; 27]%list -> getr regs r = Z_to_bv 64 0;
  ce_mem : exists (Jb : word -> option byte) (s1v : word),
             wfJ sp0 Jb /\ mem = cmem sp0 (wrap_mem RPH sp0 av ev uid hw rdraw) (J8 sp0 av ev uid hw Jb s1v) (D8 sp0 av ev hw tid rdraw)
}.

Section Assembly.
  Variable sp : word.
  Variable rdraw : EntryDraw.
  Variables argv envp : list (list byte).
  Variable uid : word.
  Variable hw : word.
  Hypothesis Hva : valid_argv argv.
  Hypothesis Hve : valid_envp envp.
  Hypothesis Hvsp : valid_sp sp.

  Variable P : machine_state -> Model -> Prop.
  Hypothesis P_bwd : forall model, m_halted model = None -> m_vm_lazy model = [] ->
    bwd SEGS (fun st => P st model).

  Hypothesis P_set_tid : forall regs (pc : word) mem model w,
    fetch_word SEGS pc = Some w -> is_ecall w = true ->
    m_halted model = None -> m_vm_lazy model = [] ->
    getr regs 17 = Z_to_bv 64 96 ->
    m_tid model = None ->
    (forall tid, (0 < bv_unsigned tid < PID_MAX_ENVELOPE)%Z ->
       P (mkst (regupd regs 10 tid) (v_addi pc 4) mem (seg_rom SEGS)) (with_tid tid model)) ->
    P (mkst regs pc mem (seg_rom SEGS)) model.

  Lemma Hlo : (0x7fff80000000 <= bv_unsigned sp)%Z.
  Proof. destruct Hvsp as [H _]. exact H. Qed.
  Lemma Hhi : (bv_unsigned sp <= 0x800000000000)%Z.
  Proof. destruct Hvsp as [_ [H _]]. exact H. Qed.
  Lemma Hal : (bv_unsigned sp mod 16 = 0)%Z.
  Proof. destruct Hvsp as [_ [_ H]]. exact H. Qed.

  Let J0 : word -> option byte := fun _ => Some (Z_to_bv 8 0).

  Ltac side Hva Hve HG :=
    first [ exact Hva | exact Hve | exact Hlo | exact Hhi | exact Hal | exact HG
          | apply wfJ_const
          | lazymatch goal with |- getr _ _ = _ =>
              gres; first [ assumption | reflexivity | bveq
                          | match goal with H : getr ?rs ?n = _ |- getr ?rs ?n = _ =>
                              rewrite H; unfold envp_w, envp_ptr, argv_w, pn_w, argc_w;
                              first [reflexivity | f_equal; lia | bveq] end ] end
          | idtac ].

  Theorem u1_boot_sec : forall (model : Model) (argvI envpI : list (list byte)),
    m_halted model = None -> m_vm_lazy model = [] -> m_tid model = None ->
    (forall tid regs mem,
       (0 < bv_unsigned tid < PID_MAX_ENVELOPE)%Z ->
       cxx_entry sp rdraw argv envp uid hw tid regs mem ->
       P (mkst regs (0x94e14 : word) mem (seg_rom SEGS)) (with_tid tid model)) ->
    P (mkst (regs_init sp) (0x656f0 : word) (wrap_mem RPH sp argv envp uid hw rdraw) (seg_rom SEGS)) model.
  Proof.
    intros model argvI envpI Hh Hlazy Ht0 HK.
    pose proof Hlo as Hlo'. pose proof Hhi as Hhi'. pose proof Hal as Hal'.
    pose proof (u64_range sp) as Hsp.
    set (RZ := fun st : machine_state => P st model).
    assert (HG : bwd SEGS RZ) by (apply P_bwd; [exact Hh | exact Hlazy]).
    rewrite cmem_init.

    destruct (p1_run SEGS HX sp rdraw argv envp uid hw Hva Hve Hlo' Hhi' Hal' (seg_rom SEGS) J0 (wfJ_const sp _))
      as [regs1 (R1 & A1 & A2 & A3 & A4 & A8 & A9 & A10 & A11 & A12 & A18 & Az)].
    eapply HG; [exact R1|].

    assert (A1' : getr regs1 1 = (0xd1518 : word)) by (rewrite A1; apply bv_eq; reflexivity).
    destruct (memset304_run SEGS HX regs1 (cmem sp (wrap_mem RPH sp argv envp uid hw rdraw) (J1 sp argv J0) (fun _ => None))
                (seg_rom SEGS) (Z_to_bv 64 (bv_unsigned sp - 368)) (0xd1518 : word) A1')
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

    carry G2 A2 (2:reg) B2. carry G2 A8 (8:reg) B8. carry G2 A9 (9:reg) B9. carry G2 A10 (10:reg) B10.
    carry G2 A3 (3:reg) B3.
    change (P ?st model) with (RZ st).
    eapply (p3_run SEGS HX sp rdraw argv envp uid hw) with (G := RZ); try side Hva Hve HG.
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

    change (J1 sp argv J0) with (J_lsm sp argv J0).
    eapply (tls_c1 SEGS HX sp rdraw J0 argv envp uid hw) with (G := RZ) (s1v := getr regs3 9) (tid := Z_to_bv 64 0); try side Hva Hve HG.
    intros regs4a; intros.
    eapply (tls_c2 SEGS HX sp rdraw J0 argv envp uid hw) with (G := RZ) (tid := Z_to_bv 64 0); try side Hva Hve HG.
    intros regs4b; intros.
    eapply (tls_c3 SEGS HX sp rdraw J0 argv envp uid hw) with (G := RZ) (tid := Z_to_bv 64 0); try side Hva Hve HG.
    intros regs4c; intros.
    eapply (tls_c4 SEGS HX sp rdraw J0 argv envp uid hw) with (G := RZ) (tid := Z_to_bv 64 0); try side Hva Hve HG.
    intros regs4; intros.

    unfold RZ at 1.
    eapply (P_set_tid regs4 (0xd1a68 : word) _ model W_d1a68 (F_d1a68 _ HX) E_d1a68);
      [exact Hh | exact Hlazy | assumption | exact Ht0 |].
    intros tid Htid.
    replace (v_addi (0xd1a68 : word) 4) with (0xd1a6c : word) by (apply bv_eq; reflexivity).
    set (model' := with_tid tid model).
    assert (Hh' : m_halted model' = None) by (unfold model'; rewrite with_tid_halted; exact Hh).
    assert (Hlazy' : m_vm_lazy model' = []) by (unfold model'; rewrite with_tid_lazy; exact Hlazy).
    set (RZ' := fun st : machine_state => P st model').
    assert (HG' : bwd SEGS RZ') by (apply P_bwd; [exact Hh' | exact Hlazy']).
    change (P ?st model') with (RZ' st).
    eapply (tls_c5 SEGS HX sp rdraw J0 argv envp uid hw) with (G := RZ'); try side Hva Hve HG'.
    intros regs5; intros.
    eapply (fin_c6 SEGS HX sp rdraw J0 argv envp uid hw) with (G := RZ'); try side Hva Hve HG'.
    intros regs6; intros.
    eapply (fin_c7 SEGS HX sp rdraw J0 argv envp uid hw) with (G := RZ'); try side Hva Hve HG'.
    intros regs7; intros.
    eapply (fin_c8 SEGS HX sp rdraw J0 argv envp uid hw) with (G := RZ'); try side Hva Hve HG'.
    intros regs8 P1 P2 P3 P4 P8 P9 P18 P19 P20 P21 P22 P23 P24 P25 P26 P27 AG8.
    unfold RZ'. apply (HK tid regs8). { exact Htid. }
    split; try assumption.
    - intros r Hr. cbn [In] in Hr.
      repeat (destruct Hr as [<-|Hr]; [assumption|]). destruct Hr.
    - exists J0, (getr regs3 9). split; [apply wfJ_const|]. unfold J8, D8. reflexivity.
  Qed.
End Assembly.

Theorem u1_boot : forall (P : machine_state -> Model -> Prop),
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
     cxx_entry sp rnd (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp) tid regs mem ->
     P (mkst regs (0x94e14 : word) mem (seg_rom SEGS))
       (with_tid tid (init_model (segments_reserved SEGS) brk mbase sp lim inp))) ->
  P (cfg_ms (init_config SEGS 0x656f0%N RPH sp brk mbase rnd lim inp))
    (cfg_model (init_config SEGS 0x656f0%N RPH sp brk mbase rnd lim inp)).
Proof.
  intros P P_bwd P_set_tid sp brk mbase rnd lim inp Hsp Hva Hve HK.
  unfold init_config. cbn [cfg_ms cfg_model].
  rewrite init_mkst.
  replace (Z_to_bv 64 (Z.of_N 0x656f0%N)) with (0x656f0 : word) by (apply bv_eq; reflexivity).
  fold (regs_init sp).
  apply (u1_boot_sec sp rnd (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp) Hva Hve Hsp P P_bwd P_set_tid
           (init_model (segments_reserved SEGS) brk mbase sp lim inp) (in_argv inp) (in_envp inp));
    [reflexivity | reflexivity | reflexivity | exact HK].
Qed.

End Img.
