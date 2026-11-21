(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.plain_halts_any_exit Require Import RunCtx.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.plain_halts_any_exit Require Import ModelAmb.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.plain_halts_any_exit.World Require Import Src_zlib_zlib_uncompress2_fuzzer_repro.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.plain_halts_any_exit Require Import
  WsegFast PropExec CatExec CatSim SeqExec StoreOk Frame StreamSim ShapeAlg Nodes AgentLib SpecConsts
  SymExec SymExec2 SymExec2Sound SymRun SymDrive SymDriveX LibKnowFrame SymAux RefMemcpyLib RefNodes RefNodesDir
  Hoare S7ExitBase S7ReadBase S7World S7Header_defs.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.plain_halts_any_exit Require Spec.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.plain_halts_any_exit.MrP7 Require Import S7SoDefs S7PrintfFirst S7LfBase.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.plain_halts_any_exit.MrP7 Require S7LfReadErr.
#[local] Existing Instance PropExec.fx0.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
Import SX2. Import SX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).


Definition dr_regions (sp0 : word) : list (word * Z) :=
  [(Z_to_bv 64 (bv_unsigned sp0 - 512), 384); (Z_to_bv 64 0x72edc, 4)].

Record dr_pre {RCa1 : RunCtx}  (sp0 pp : word) (tid cw : Z) (t8 : list byte) (R : bvmap 5 word) (M : word -> option byte) : Prop := DR_PRE {
  dr_sp  : getr R 2 = Z_to_bv 64 (bv_unsigned sp0 - 128);
  dr_gp  : getr R 3 = Z_to_bv 64 0x10800;
  dr_tp  : getr R 4 = Z_to_bv 64 0x72f80;
  dr_s2  : getr R 18 = pp;
  dr_s3  : getr R 19 = Z_to_bv 64 0;
  dr_s4  : getr R 20 = Z_to_bv 64 3;
  dr_s5  : getr R 21 = Z_to_bv 64 65536;
  dr_s6  : getr R 22 = Z_to_bv 64 0x22e79;
  dr_stack : stack_writable M sp0;
  dr_img   : Forall (fun iv => img_clear M (fst iv) (snd iv)) lf_ivs;
  dr_tid   : cell M 0x72ed8 4 tid;
  dr_tidr  : 0 < tid < 2 ^ 22;
  dr_got   : cell M 0x21c00 8 0x931e8;
  dr_can   : cell M 0x931e8 8 cw;
  dr_nl    : cell M 0x9320b 1 0;
  dr_pp1   : bv_unsigned sp0 <= bv_unsigned pp;
  dr_pp2   : bv_unsigned pp + 9 <= bv_unsigned sp0 + 4194304;
  dr_str   : rdn (run_segments RSEGS rc_inp rc_sp rc_mb) M pp 2 = Some [Z_to_bv 8 46; Z_to_bv 8 0];
  dr_t8    : rdn (run_segments RSEGS rc_inp rc_sp rc_mb) M (Z_to_bv 64 (bv_unsigned pp + 1)) 8 = Some t8
}.
Arguments DR_PRE {RCa1}.


Definition sr_DR : list expr :=
  [ELit 0; J 1; spx (-128); J 3; ELit 0x72f80; J 5; J 6; J 7;
   J 8; J 9; J 10; J 11; J 12; J 13; J 14; J 15;
   J 16; J 17; J 18; ELit 0; ELit 3; ELit 65536; ELit 0x22e79; J 23;
   J 24; J 25; J 26; J 27; J 28; J 29; J 30; J 31].

Definition kn_DR : list kentry :=
  [KAlign (EVar 0) 16; KRange (EVar 0) 0x7fff80000000 0x800000000000;
   KWr (SA (EVar 0) (-6144513)) 6144513;
   KWr (SA (ELit 0) 0x22000) 0x72000].

Definition DR_FUEL : nat := 5000.
Definition dr_sregions : list sregion := [(SA (EVar 0) (-512), 384); (SA (ELit 0) 0x72edc, 4)].
Definition dr_kept : list reg := [2; 3; 4; 18]%bv.

Lemma dr_itinerary {RCa1 : RunCtx}  :
  let a := sym_exec (run_segments RSEGS rc_inp rc_sp rc_mb) DR_FUEL true [] scr0 (SS 0x14998 sr_DR [] kn_DR 43) [] in
  (s_pc (fst (fst a)), snd (fst a)) = (0x20aa8, []).
Proof. vm_compute. reflexivity. Qed.

Section Entry.
Context {RCa1 : RunCtx}.
  Variable sp0 : word.
  Hypothesis Hvsp : valid_sp sp0.
  Variables (pp : word) (tid cw : Z) (t8 : list byte) (R : bvmap 5 word) (M : word -> option byte).
  Hypothesis DP : dr_pre sp0 pp tid cw t8 R M.

  Let SPlo : 0x7fff80000000 <= bv_unsigned sp0 := proj1 Hvsp.
  Let SPhi : bv_unsigned sp0 <= 0x800000000000 := proj1 (proj2 Hvsp).
  Let SPal : bv_unsigned sp0 mod 16 = 0 := proj2 (proj2 Hvsp).

  Definition dr_vals : list word := [sp0; Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 0;
                                     Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 0] ++ junk_vals R.
  Let E : env := ENVh [] dr_vals.

  Lemma dr_vals_length : length dr_vals = 43%nat.
  Proof. unfold dr_vals. rewrite length_app, junk_vals_length. reflexivity. Qed.

  Lemma dr_EJ : forall i, (i < 32)%nat -> ev E (11 + i) = getr R (Z_to_bv 5 (Z.of_nat i)).
  Proof.
    intros i Hi. unfold E, ENVh, dr_vals. cbn [ev]. unfold vals_ev.
    change (11 + i)%nat with (length [sp0; Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 0;
                                      Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 0] + i)%nat.
    rewrite app_nth2_plus. unfold junk_vals. rewrite (nth_map_seq (fun i => getr R (Z_to_bv 5 (Z.of_nat i)))) by exact Hi.
    reflexivity.
  Qed.

  Lemma dr_regs_ok : regs_ok E sr_DR R.
  Proof.
    destruct DP as [R2 R3 R4 R18 R19 R20 R21 R22 _ _ _ _ _ _ _ _ _ _ _].
    pose proof SPlo. pose proof SPhi.
    assert (E0 : ev E 0 = sp0) by reflexivity.
    apply S7ReadBase.regs_ok_by_index. intros i Hi.
    destruct i as [|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|i]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]; [ .. | lia];
      cbn [nth sr_DR S7ReadBase.all_regs].
    all: try (lazymatch goal with |- _ = edenot _ (J ?n) =>
                unfold J; change (edenot E (EVar (11 + n))) with (ev E (11 + n)%nat); rewrite dr_EJ by lia; reflexivity end).
    all: try (lazymatch goal with |- _ = edenot _ (spx ?z) =>
                unfold spx; rewrite edenot_add_lit; unfold adenot, v_addi; cbn [a_base a_off edenot]; rewrite E0;
                rewrite R2; f_equal; lia end).
    all: cbn [edenot]; first [assumption | apply getr_zero | reflexivity].
  Qed.

  Lemma dr_know_ok : know_ok (run_segments RSEGS rc_inp rc_sp rc_mb) E M kn_DR.
  Proof.
    pose proof SPlo. pose proof SPhi. pose proof SPal.
    pose proof (dr_stack _ _ _ _ _ _ _ DP) as HST.
    assert (Z0 : bv_unsigned (Z_to_bv 64 0) = 0) by reflexivity.
    assert (E0 : ev E 0 = sp0) by reflexivity.
    unfold kn_DR. repeat (apply Forall_cons); [ .. | apply Forall_nil ].
    - apply kalign_intro; [lia|]. cbn [edenot]. rewrite E0. assumption.
    - apply krange_intro. cbn [edenot]. rewrite E0. lia.
    - cbn [kentry_ok]. unfold flat, estart. cbn [a_base a_off edenot]. rewrite E0.
      split; [lia|]. intros d m Hd Hm.
      replace (bv_unsigned sp0 + -6144513 + d) with (bv_unsigned sp0 - 6144513 + d) by lia. apply HST; lia.
    - cbn [kentry_ok]. unfold flat, estart. cbn [a_base a_off edenot]. rewrite Z0.
      split; [lia|]. intros d m Hd Hm. apply store_ok_data; rewrite u64_lit by lia; lia.
  Qed.

  Lemma dr_regions_denot : forall (E' : env), ev E' 0 = sp0 -> map (rdenot E') dr_sregions = dr_regions sp0.
  Proof.
    intros E' H. unfold dr_sregions, dr_regions, rdenot, estart. cbn [map fst snd a_base a_off edenot]. rewrite H.
    change (bv_unsigned (Z_to_bv 64 0)) with 0.
    replace (bv_unsigned sp0 + -512) with (bv_unsigned sp0 - 512) by lia. reflexivity.
  Qed.

  Lemma dr_regions_flat : forall (E' : env), ev E' 0 = sp0 -> regions_flat E' dr_sregions.
  Proof.
    intros E' H r Hr. pose proof SPlo. pose proof SPhi. unfold dr_sregions in Hr. cbn [In] in Hr.
    destruct Hr as [<-|[<-|[]]]; unfold flat, estart; cbn [fst snd a_base a_off edenot]; rewrite ?H;
      change (bv_unsigned (Z_to_bv 64 0)) with 0; lia.
  Qed.

  Lemma dr_block_frame : forall (E' : env) base log,
    ev E' 0 = sp0 -> log_covered dr_sregions log = true -> log_flat E' log ->
    frame_mod base (mem_denot E' base log) (dr_regions sp0).
  Proof.
    intros E' base log H Hc Hlf. rewrite <- (dr_regions_denot E' H).
    apply log_covered_frame; [exact Hc | apply (dr_regions_flat E' H) | exact Hlf].
  Qed.

  Lemma dr_outside : forall i, 0 <= i < 2 ^ 64 ->
    (bv_unsigned sp0 - 128 <= i \/ (i < 0x72edc \/ 0x72ee0 <= i) /\ i < 0x94000) -> outside (Z_to_bv 64 i) (dr_regions sp0).
  Proof.
    intros i Hi H. pose proof SPlo. pose proof SPhi. unfold dr_regions. cbn [outside]. unfold in_rng.
    rewrite !u64_lit by lia. lia.
  Qed.

  Lemma dr_rdn_frame : forall M' a n bs,
    frame_mod M M' (dr_regions sp0) -> rdn (run_segments RSEGS rc_inp rc_sp rc_mb) M (Z_to_bv 64 a) n = Some bs ->
    0 <= a < 2 ^ 64 -> a + Z.of_nat n <= 2 ^ 64 ->
    (bv_unsigned sp0 - 128 <= a \/ (a + Z.of_nat n <= 0x72edc \/ 0x72ee0 <= a) /\ a + Z.of_nat n <= 0x94000) ->
    rdn (run_segments RSEGS rc_inp rc_sp rc_mb) M' (Z_to_bv 64 a) n = Some bs.
  Proof.
    intros M' a n bs [He _] H Ha Hn HD. rewrite (rdn_ext (run_segments RSEGS rc_inp rc_sp rc_mb) n M' M); [exact H | rewrite u64_lit by lia; lia |].
    intros x Hx. rewrite u64_lit in Hx by lia. rewrite <- (Z_to_bv_bv_unsigned 64 x). apply He, dr_outside; lia.
  Qed.

  Lemma dr_img_frame : forall M', frame_mod M M' (dr_regions sp0) ->
    Forall (fun iv => img_clear M' (fst iv) (snd iv)) lf_ivs.
  Proof.
    intros M' [He _]. pose proof (dr_img _ _ _ _ _ _ _ DP) as IMG.
    rewrite Forall_forall in IMG |- *. intros [lo hi] IN. specialize (IMG (lo, hi) IN). cbn [fst snd] in *.
    intros i Hi. rewrite He; [exact (IMG i Hi)|].
    apply dr_outside; unfold lf_ivs in IN; cbn [In] in IN;
      repeat (destruct IN as [IN|IN]; [injection IN as <- <-; lia|]); destruct IN.
  Qed.
End Entry.


Lemma fetch_20978 {RCa1 : RunCtx}  : fetch_word (run_segments RSEGS rc_inp rc_sp rc_mb) (Z_to_bv 64 0x20aa8) = Some ECALLW.
Proof. vm_compute. reflexivity. Qed.

Theorem dir_read_leaf {RCa1 : RunCtx}  : forall (sp0 pp : word) (tid cw : Z) (t8 : list byte) (R : bvmap 5 word) (M : word -> option byte) (model : Model),
  valid_sp sp0 -> dr_pre sp0 pp tid cw t8 R M ->
  m_halted model = None -> m_vm_lazy model = [] ->
  fd_lookup (m_fds model) (Z_to_bv 64 3) = Some FdDir ->
  fd_lookup (m_fds model) (Z_to_bv 64 2) = Some (FdChannel (Z_to_bv 64 2)) ->
  m_channel_reader model = true ->
  realizes (run_segments RSEGS rc_inp rc_sp rc_mb) (mkCfg (mkst R (Z_to_bv 64 0x14998) M (seg_rom (run_segments RSEGS rc_inp rc_sp rc_mb))) model)
             (Spec.t_die (Spec.msg_read_error Spec.dot_path) (m_fs model)).
Proof.
  intros sp0 pp tid cw t8 R M model Hvsp DP Hh Hl Hfd3 Hfd2 Hrdr.
  pose proof (proj1 Hvsp) as SPlo. pose proof (proj1 (proj2 Hvsp)) as SPhi. unfold sp_window_lo, sp_window_hi in *.
  pose proof (dr_regs_ok sp0 Hvsp pp tid cw t8 R M DP) as HR.
  pose proof (dr_know_ok sp0 Hvsp pp tid cw t8 R M DP) as HK.
  set (vals := dr_vals sp0 R) in *.
  assert (HL : length vals = 43%nat) by apply dr_vals_length.
  assert (P0 : vals_ev vals 0 = sp0) by reflexivity.
  pose proof HR as HR0.
  run_block_lf HR HK DR_FUEL (@nil Z) scr0 43%nat.
  clear HR HK. intros Ra Ma HR HK EQa LFa. cbn [s_pc s_regs s_log] in HR, EQa, LFa |- *.
  assert (FMa : frame_mod M Ma (dr_regions sp0)).
  { rewrite EQa. apply (dr_block_frame sp0 Hvsp); [exact P0 | vm_compute; reflexivity | exact LFa]. }
  clear EQa LFa.
  eapply (rz_read_dir_mapped (run_segments RSEGS rc_inp rc_sp rc_mb) Ra (Z_to_bv 64 0x20aa8) Ma model ECALLW (Z_to_bv 64 3) 65536 _ fetch_20978 is_ecall_ECALLW Hh Hl).
  - regv HR (17%bv : reg). reflexivity.
  - regv HR (10%bv : reg). reflexivity.
  - change (bv_unsigned (Z_to_bv 64 3)) with 3. lia.
  - exact Hfd3.
  - regv HR (12%bv : reg). reflexivity.
  - lia.
  - lia.
  - regv HR (11%bv : reg). cbn [edenot]. rewrite u64_lit by lia. lia.
  - rewrite (v_addi_pc4 0x20aa8) by lia. change (0x20aa8 + 4) with 0x20aac.
    assert (HR' := regs_set_a0 _ _ _ (errno_ret EISDIR) (ELit (2 ^ 64 - 21)) HR ltac:(apply bv_eq; reflexivity)).
    clear HR. rename HR' into HR.
    run_block_lf HR HK DR_FUEL [0x14af8] scr0 43%nat.
    clear HR HK. intros Rb Mb HR HK EQb LFb. cbn [s_pc s_regs s_log] in HR, EQb, LFb |- *.
    assert (FMb : frame_mod Ma Mb (dr_regions sp0)).
    { rewrite EQb. apply (dr_block_frame sp0 Hvsp); [exact P0 | vm_compute; reflexivity | exact LFb]. }
    clear EQb LFb.
    assert (FM : frame_mod M Mb (dr_regions sp0)) by (eapply frame_mod_trans_same; [exact FMa | exact FMb]).
    assert (KEPT : forall r : reg, In r dr_kept -> getr Rb r = getr R r).
    { eapply (same_regs_sound _ sr_DR _ R Rb dr_kept); [ | exact HR0 | exact HR]. vm_compute. reflexivity. }
    pose proof DP as [R2 R3 R4 R18 _ _ _ _ HST IMG TID TIDR GOT CANC NLC PP1 PP2 STR T8].
    pose proof (dr_rdn_frame sp0 Hvsp M) as TR.
    eapply (S7LfReadErr.ref_read_error_dot sp0 [] model Hvsp Hh Hl Hfd2 Hrdr pp tid Rb Mb).
    + rewrite (KEPT 2%bv ltac:(clear; cbn; tauto)). exact R2.
    + rewrite (KEPT 3%bv ltac:(clear; cbn; tauto)). exact R3.
    + rewrite (KEPT 4%bv ltac:(clear; cbn; tauto)). exact R4.
    + rewrite (KEPT 18%bv ltac:(clear; cbn; tauto)). exact R18.
    + intros d m Hd Hm. eapply store_ok_mono; [exact (proj2 FM) | apply HST; assumption].
    + exact (dr_img_frame sp0 Hvsp pp tid cw t8 R M DP Mb FM).
    + unfold cell in *. apply (TR Mb _ _ _ FM TID); cbn; lia.
    + exact TIDR.
    + unfold cell in *. apply (TR Mb _ _ _ FM GOT); cbn; lia.
    + unfold cell in *. apply (TR Mb _ _ _ FM CANC); cbn; lia.
    + unfold cell in *. apply (TR Mb _ _ _ FM NLC); cbn; lia.
    + exact PP1.
    + exact PP2.
    + rewrite <- (Z_to_bv_bv_unsigned 64 pp). pose proof (u64_range pp) as UP.
      apply (TR Mb _ _ _ FM); [rewrite Z_to_bv_bv_unsigned; exact STR | lia | cbn; lia | left; lia].
    + pose proof (u64_range pp) as UP.
      apply (TR Mb _ _ _ FM T8); [lia | cbn; lia | left; lia].
Qed.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
