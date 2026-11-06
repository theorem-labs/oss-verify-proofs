(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.spirv_tools.spvtools_binary_parser_fuzzer.images Require Import Plain.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import Amb RunRandom PropExec CatExec CatSim SeqExec StoreOk ShapeAlg Nodes ShapeLaws MmapSim FileSim AgentLib Frame SymExec SymExec2 SymExec2Sound SymRun SymDrive SymDriveX RefNodes RefMemcpyLib Hoare SRealizes SNodes LibIface LibBudget S1Layout.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.Drv Require Import SymDriveS2 RunsLib S1CxxTable StaticsGen S1Statics S1SpecConsts S1Spec S1Cells S1KnCells S1KnIvs S1RwWindow
  S1ExitKn S1TargetInv S1RBase S1RKn DrvMallocT S1LibStdioCall S1RHeader_defs S1ReadErr S1DirTail SNodesDir S1Start S1BootDefs S1MainEntry.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Import SX2. Import SX2S.

Abbreviation RSEGS := Plain.M.loaded_segments.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Section FX.
Context {fx : FPState}.
Context {AC : AllocCeiling}.

Definition STOPSd : list Z := [0x65814].
Definition FUELd : nat := 5000.
Definition rund (ss : sym_state) := sym_exec RSEGS FUELd true STOPSd scr0 ss [].

Definition sr_D : list expr :=
  [ELit 0; J 1; spx (-128); ELit 0x10800; ELit 0x1006b8; J 5; J 6; J 7;
   ELit 2; EVar 3; J 10; J 11; J 12; J 13; J 14; J 15;
   J 16; J 17; EVar 1; ELit 0; ELit 3; ELit 65536; ELit 0xee4e9; J 23;
   J 24; J 25; J 26; J 27; J 28; J 29; J 30; J 31].

Definition hd1 := Eval vm_compute in rund (SS 0x656b4 sr_D [] kn_H 41).
Definition srD1 : list expr := Eval vm_compute in s_regs (fst (fst hd1)).
Definition lgD1 : list sentry := Eval vm_compute in s_log (fst (fst hd1)).
Definition knD1 : list kentry := Eval vm_compute in kn_after hd1 kn_H.
Definition srD2 : list expr := Eval vm_compute in sr_upd srD1 (ridx 10) (ELit (2 ^ 64 - 21)).
Definition hd2 := Eval vm_compute in rund (SS 0xe1e50 srD2 [] knD1 41).
Definition srD3 : list expr := Eval vm_compute in s_regs (fst (fst hd2)).
Definition lgD2 : list sentry := Eval vm_compute in s_log (fst (fst hd2)).
Definition knD3 : list kentry := Eval vm_compute in kn_after hd2 knD1.

Lemma fetch_e1ce0 : fetch_word RSEGS (Z_to_bv 64 0xe1e4c) = Some ECALLW.
Proof. vm_compute. reflexivity. Qed.
End FX.

Tactic Notation "run_blockd_keep" constr(NX) := run_block_gen_s FUELd STOPSd scr0 NX true.

Section FXALL.
Context {fx : FPState}.
Context {AC : AllocCeiling}.

Definition entry_in_d (e : sentry) : bool :=
  match e with
  | SE (SA (EVar i) k) w _ => (Nat.eqb i 0 && (-4096 <=? k) && (k + Z.of_nat w <=? -128))%bool
  | SE (SA (ELit z) a) w _ => (Z.eqb z 0 && (0x100614 <=? a) && (a + Z.of_nat w <=? 0x100618))%bool
  | _ => false
  end.

Lemma mem_denot_foot_d : forall E base log (x : word),
  forallb entry_in_d log = true ->
  (0x100618 + 4096 <= bv_unsigned (ev E 0))%Z ->
  ~ (bv_unsigned (ev E 0) - 4096 <= bv_unsigned x < bv_unsigned (ev E 0) - 128)%Z ->
  ~ (0x100614 <= bv_unsigned x < 0x100618)%Z ->
  mem_denot E base log x = base x.
Proof.
  intros E base log x Hb Hhi N1 N2. pose proof (u64_range (ev E 0)) as Usp. pose proof (u64_range x) as Ux.
  induction log as [|[[b k] w v] rest IH]; [reflexivity|].
  cbn [forallb] in Hb. apply andb_prop in Hb as [He Hrest].
  cbn [entry_in_d] in He. destruct b as [z|i| | | | | |]; try discriminate He.
  - apply andb_prop in He as [He H2]. apply andb_prop in He as [H0 H1].
    apply Z.eqb_eq in H0. subst z. apply Z.leb_le in H1. apply Z.leb_le in H2.
    cbn [mem_denot]. rewrite wbytes_outside.
    + apply IH. exact Hrest.
    + rewrite length_N_to_le_bytes. unfold in_rng, adenot, v_addi. cbn [a_base a_off edenot].
      rewrite (u64_lit 0), u64_lit by lia. lia.
    + rewrite length_N_to_le_bytes. unfold adenot, v_addi. cbn [a_base a_off edenot]. rewrite (u64_lit 0), u64_lit by lia. lia.
  - apply andb_prop in He as [He H2]. apply andb_prop in He as [H0 H1].
    apply Nat.eqb_eq in H0. subst i. apply Z.leb_le in H1. apply Z.leb_le in H2.
    cbn [mem_denot]. rewrite wbytes_outside.
    + apply IH. exact Hrest.
    + rewrite length_N_to_le_bytes. unfold in_rng, adenot, v_addi. cbn [a_base a_off edenot]. rewrite u64_lit by lia. lia.
    + rewrite length_N_to_le_bytes. unfold adenot, v_addi. cbn [a_base a_off edenot]. rewrite u64_lit by lia. lia.
Qed.

Lemma lgD1_in : forallb entry_in_d lgD1 = true. Proof. vm_compute. reflexivity. Qed.
Lemma lgD2_in : forallb entry_in_d lgD2 = true. Proof. vm_compute. reflexivity. Qed.

Lemma drv_cells_range2 : Forall (fun c : Z * nat * Z => match c with (a, w, v) =>
    0xee4a0 <= a /\ a + Z.of_nat w <= 0x120980 /\ (a + Z.of_nat w <= 0x100614 \/ 0x100618 <= a) end) drv_cells.
Proof.
  assert (HA : forallb (fun c : Z * nat * Z => let '(a, w, v) := c in ((0xee4a0 <=? a) && (a + Z.of_nat w <=? 0x120980) && ((a + Z.of_nat w <=? 0x100614) || (0x100618 <=? a)))%bool) drv_cells = true)
    by (vm_compute; reflexivity).
  apply Forall_forall. intros [[a w] v] Hin. pose proof (proj1 (forallb_forall _ _) HA _ Hin) as HB.
  cbv beta iota in HB |- *. apply andb_prop in HB as [HB H3]. apply andb_prop in HB as [H0 H1]. apply Z.leb_le in H0, H1. apply orb_true_iff in H3. destruct H3 as [H3|H3]; apply Z.leb_le in H3; lia.
Qed.

Lemma drv_cells_ok_agree2 : forall M M',
  (forall i, 0xee4a0 <= i < 0x120980 -> ~ (0x100614 <= i < 0x100618) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i)) ->
  drv_cells_ok M -> drv_cells_ok M'.
Proof.
  intros M M' Hag H. unfold drv_cells_ok in *.
  pose proof drv_cells_range2 as HR.
  induction drv_cells as [|[[a w] v] rest IH]; [constructor|].
  apply Forall_cons_iff in H as [H1 H2]. apply Forall_cons_iff in HR as [R1 R2].
  constructor; [|apply IH; assumption].
  rewrite <- H1. apply rdn_ext; [rewrite u64_lit by lia; lia|].
  intros x Hx. rewrite u64_lit in Hx by lia.
  replace x with (Z_to_bv 64 (bv_unsigned x)) by (apply bv_eq; rewrite u64_lit by (pose proof (u64_range x); lia); reflexivity).
  apply Hag; lia.
Qed.

Section Mid.
  Context {AMB : Amb} {RRND : RunRandom}.
  Variable MI : MallocIface SEGS L.
  Hypothesis MC : mi_constsG MI.
  Variables (sp0 tid p1 : Z) (path : list byte) (fs0 : Fs).
  Hypothesis Hsp : 0x7fff80000000 <= sp0 <= 0x800000000000 /\ sp0 mod 16 = 0.
  Hypothesis Hp1 : sp0 <= p1 /\ p1 + Z.of_nat (length path) + 1 < 2 ^ 63.
  Hypothesis Htid : 0 < tid < 2 ^ 22.
  Variables (p : Z) (A : AS MI) (R0 : bvmap 5 word) (M0 : word -> option byte) (mo : Model).

  Hypothesis Q2 : getr R0 2 = Z_to_bv 64 (sp0 - 128).
  Hypothesis Q3 : getr R0 3 = Z_to_bv 64 0x10800.
  Hypothesis Q4 : getr R0 4 = Z_to_bv 64 0x1006b8.
  Hypothesis Q8 : getr R0 8 = Z_to_bv 64 2.
  Hypothesis Q9 : getr R0 9 = Z_to_bv 64 p.
  Hypothesis Q18 : getr R0 18 = Z_to_bv 64 p1.
  Hypothesis Q19 : getr R0 19 = Z_to_bv 64 0.
  Hypothesis Q20 : getr R0 20 = Z_to_bv 64 3.
  Hypothesis Q21 : getr R0 21 = Z_to_bv 64 65536.
  Hypothesis Q22 : getr R0 22 = Z_to_bv 64 0xee4e9.
  Hypothesis RM : rmem sp0 tid p1 path M0.
  Hypothesis RA : rabs MI A M0 mo.
  Hypothesis LV : live MI A = [(p, 65536)].
  Hypothesis FD3 : fd_lookup (m_fds mo) (Z_to_bv 64 3) = Some FdDir.

  Let spw : word := Z_to_bv 64 sp0.
  Let pw : word := Z_to_bv 64 p.
  Let AI := ra_ainv _ _ _ _ RA.

  Definition valsd : list word :=
    [spw; Z_to_bv 64 p1; Z_to_bv 64 65536; pw; Z_to_bv 64 tid; Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 rr_canary] ++ junk_vals R0.

  Lemma p_facts : 0x122000 <= p /\ p + 65536 <= alloc_ceiling /\ p mod 16 = 0.
  Proof.
    assert (Hin : In (p, 65536) (live MI A)) by (rewrite LV; left; reflexivity).
    destruct (ai_live_block MI A M0 mo p 65536 AI Hin) as (_ & Hal & _ & Hce & _).
    split; [exact (live_above_img MI A M0 mo p 65536 AI Hin ltac:(lia)) | split; [exact Hce | exact Hal]].
  Qed.

  Lemma static_cell : forall (a : Z) (zs : list Z) (n : nat) (v : Z),
    In (a, zs) (static_cells MI) -> length zs = n ->
    map (Z_to_bv 8) zs = word_to_le_bytes n (Z_to_bv 64 v) -> cell M0 a n v.
  Proof.
    intros a zs n v Hin Hl He. unfold cell. rewrite <- He, <- Hl.
    exact (ai_static_cells MI A M0 mo a zs AI Hin).
  Qed.

  Lemma dir_sym : regs_ok (ENVh [] valsd) sr_D R0 /\ know_ok RSEGS (ENVh [] valsd) M0 kn_H.
  Proof.
    pose proof p_facts as (P1f & P2 & P3). pose proof ac_bounds_lit as Hcv.
    pose proof MC as [MSc BIGc NMAXc RBc SCg SCn SCp].
    set (vals := valsd). set (E := ENVh [] vals).
    assert (E0 : ev E 0 = spw) by reflexivity.
    assert (E1 : ev E 1 = Z_to_bv 64 p1) by reflexivity.
    assert (E2 : ev E 2 = Z_to_bv 64 65536) by reflexivity.
    assert (E3 : ev E 3 = pw) by reflexivity.
    assert (E4 : ev E 4 = Z_to_bv 64 tid) by reflexivity.
    assert (EJ : forall i, (i < 32)%nat -> ev E (9 + i) = getr R0 (Z_to_bv 5 (Z.of_nat i))).
    { intros i Hi. unfold E, ENVh, vals, valsd. cbn [ev]. unfold vals_ev.
      change (9 + i)%nat with (length [spw; Z_to_bv 64 p1; Z_to_bv 64 65536; pw; Z_to_bv 64 tid; Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 rr_canary] + i)%nat.
      rewrite app_nth2_plus. unfold junk_vals. rewrite (nth_map_seq (fun i => getr R0 (Z_to_bv 5 (Z.of_nat i)))) by exact Hi.
      reflexivity. }
    assert (Uspw : bv_unsigned spw = sp0) by (unfold spw; apply u_small; lia).
    assert (Upw : bv_unsigned pw = p) by (unfold pw; apply u_small; lia).
    split.
    -
      apply S1MainEntry.regs_ok_by_index. intros i Hi.
      destruct i as [|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|i]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]; [ .. | lia];
        cbn [nth sr_D S1MainEntry.all_regs].
      all: try (lazymatch goal with |- _ = edenot _ (J ?n) =>
                  unfold J; change (edenot E (EVar (9 + n))) with (ev E (9 + n)%nat); rewrite EJ by lia; reflexivity end).
      all: try (lazymatch goal with |- _ = edenot _ (spx ?k) =>
                  unfold spx; rewrite edenot_add_lit; unfold adenot, v_addi; cbn [a_base a_off edenot]; rewrite E0, Uspw;
                  rewrite Q2; f_equal; lia end).
      all: try (change (edenot E (EVar 1)) with (ev E 1); rewrite E1; assumption).
      all: try (change (edenot E (EVar 3)) with (ev E 3); rewrite E3; unfold pw; assumption).
      all: cbn [edenot]; first [assumption | apply getr_zero | rewrite getr_zero; apply bv_eq; reflexivity | reflexivity].
    -
      assert (SPX : forall k, edenot E (spx k) = Z_to_bv 64 (sp0 + k)).
      { intros k. unfold spx. rewrite edenot_add_lit. unfold adenot, v_addi. cbn [a_base a_off edenot]. rewrite E0, Uspw. reflexivity. }
      unfold kn_H.
      apply know_ok_app; split; [ | apply know_ok_app; split; [ | apply know_ok_app; split; [ | apply know_ok_app; split;
        [ apply S1KnIvs.know_ivs; rewrite S1KnIvs.hdr_ivs_eq; exact (rm_img _ _ _ _ _ RM)
        | apply know_drv_cells; exact (rmem_drv_cells _ _ _ _ _ RM) ]]]].
      +
        destruct (rm_mf _ _ _ _ _ RM) as [F1 F2 F3 F4 F5 F6 F7 F8 F9]. unfold cell in *.
        unfold kn_Hstack, know_ok. repeat apply Forall_cons; try apply Forall_nil;
          cbn [kentry_ok]; unfold flat, estart, elenZ, adenot, v_addi; cbn [a_base a_off]; rewrite ?SPX; cbn [edenot]; rewrite ?E0, ?Uspw.
        * split; [lia | exact (proj2 Hsp)].
        * lia.
        * split; [lia|]. intros d m Hd Hm. replace (sp0 + -8388608 + d)%Z with (sp0 - 8388608 + d)%Z by lia. apply (rm_stack _ _ _ _ _ RM); lia.
        * split; [lia|]. split; [lia|]. replace (sp0 + -56)%Z with (sp0 - 56)%Z by lia. exact F1.
        * split; [lia|]. split; [lia|]. replace (sp0 + -64)%Z with (sp0 - 64)%Z by lia. exact F2.
        * split; [lia|]. split; [lia|]. replace (sp0 + -72)%Z with (sp0 - 72)%Z by lia. exact F3.
        * split; [lia|]. split; [lia|]. replace (sp0 + -80)%Z with (sp0 - 80)%Z by lia. exact F4.
        * split; [lia|]. split; [lia|]. replace (sp0 + -88)%Z with (sp0 - 88)%Z by lia. exact F5.
        * split; [lia|]. split; [lia|]. replace (sp0 + -96)%Z with (sp0 - 96)%Z by lia. exact F6.
        * split; [lia|]. split; [lia|]. replace (sp0 + -104)%Z with (sp0 - 104)%Z by lia. exact F7.
        * split; [lia|]. split; [lia|]. replace (sp0 + -112)%Z with (sp0 - 112)%Z by lia. exact F8.
        * split; [lia|]. split; [lia|]. replace (sp0 + -120)%Z with (sp0 - 120)%Z by lia. exact F9.
      +
        unfold kn_Hbuf, know_ok. repeat apply Forall_cons; try apply Forall_nil;
          cbn [kentry_ok]; unfold flat, estart, elenZ, adenot, v_addi; cbn [a_base a_off edenot]; rewrite ?E0, ?E2, ?E3, ?Uspw, ?Upw.
        * lia.
        * rewrite u_small by lia. lia.
      +
        unfold kn_Himage, know_ok. repeat apply Forall_cons; try apply Forall_nil;
          cbn [kentry_ok]; unfold flat, estart, elenZ, adenot, v_addi; cbn [a_base a_off edenot]; rewrite ?E4;
          change (bv_unsigned (Z_to_bv 64 0)) with 0%Z; rewrite ?Z.add_0_l.
        * split; [lia|]. intros d m Hd Hm. apply S1RwWindow.store_ok_rwZ; lia.
        * split; [lia|]. split; [lia|]. exact (rm_tid _ _ _ _ _ RM).
        * split; [lia|]. split; [lia|]. exact (rm_self _ _ _ _ _ RM).
        * split; [lia|]. split; [lia|]. change (ev (ENVh [] valsd) 8) with (Z_to_bv 64 rr_canary).
          exact (mcg_guard_cell MI MC A M0 mo AI).
        * split; [lia|]. split; [lia|]. eapply static_cell; [exact SCp | reflexivity | apply byte_list_eq; vm_compute; reflexivity].
        * split; [lia|]. split; [lia|]. eapply static_cell; [exact SCn | reflexivity | apply byte_list_eq; vm_compute; reflexivity].
        * rewrite u_small by lia. lia.
  Qed.

  Theorem dir_mid : forall (mem0 : word -> option byte) (spw0 p1w : word),
    bv_unsigned spw0 = sp0 -> bv_unsigned p1w = p1 -> path = dot_path ->
    (exists t8, rdn RSEGS M0 (Z_to_bv 64 (p1 + Z.of_nat (length path))) 8 = Some t8) ->
    (forall R M, dir_tail_pre spw0 p1w tid mem0 R M ->
       srealizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x65814) M (seg_rom RSEGS)) mo) (t_die (msg_read_error dot_path) (m_fs mo))) ->
    srealizes RSEGS (mkCfg (mkst R0 (Z_to_bv 64 0x656b4) M0 (seg_rom RSEGS)) mo) (t_die (msg_read_error dot_path) (m_fs mo)).
  Proof.
    intros mem0 spw0 p1w Usp0 Up1 Hdot [t8 Ht8] TAIL.
    pose proof p_facts as (P1f & P2 & P3). pose proof ac_bounds_lit as Hcv.
    pose proof MC as [MSc BIGc NMAXc RBc SCg SCn SCp].
    destruct dir_sym as [HR HK]. destruct (ra_mstd _ _ _ _ RA) as [Hh Hlz Hmat].
    assert (Uspw : bv_unsigned spw = sp0) by (unfold spw; apply u_small; lia).
    set (vals := valsd) in *.
    assert (HL : length vals = 41%nat) by (subst vals; unfold valsd; rewrite length_app, junk_vals_length; reflexivity).
    assert (P0 : vals_ev vals 0 = spw) by reflexivity.
    assert (P1v : vals_ev vals 1 = Z_to_bv 64 p1) by reflexivity.
    assert (P3v : vals_ev vals 3 = pw) by reflexivity.
    assert (P4v : vals_ev vals 4 = Z_to_bv 64 tid) by reflexivity.
    clearbody vals.

    run_blockd_keep 41%nat.
    lazymatch goal with EQM : ?M1 = mem_denot _ M0 ?lg |- _ =>
      assert (AG1 : forall x : word, ~ (sp0 - 4096 <= bv_unsigned x < sp0 - 128)%Z -> ~ (0x100614 <= bv_unsigned x < 0x100618)%Z -> M1 x = M0 x)
        by (intros x N1 N2; rewrite EQM; apply (mem_denot_foot_d (ENVh [] vals) M0 lg x lgD1_in); cbn [ev ENVh]; rewrite ?P0, ?Uspw; lia);
      assert (HG1 : mem_grows M0 M1) by (rewrite EQM; apply mem_denot_grows);
      clear EQM
    end.

    eapply (srz_read_dir_mapped RSEGS R (Z_to_bv 64 0xe1e4c) M mo ECALLW (Z_to_bv 64 3) 65536 _ fetch_e1ce0 is_ecall_ECALLW Hh Hlz).
    - regv HR (17%bv : reg). reflexivity.
    - regv HR (10%bv : reg). reflexivity.
    - change (bv_unsigned (Z_to_bv 64 3)) with 3%Z. lia.
    - exact FD3.
    - regv HR (12%bv : reg). reflexivity.
    - lia.
    - lia.
    - regv HR (11%bv : reg). cbn [edenot]. rewrite u_small by lia. unfold TASK_SIZE. lia.
    - regv HR (11%bv : reg). cbn [edenot]. apply S1RwWindow.store_ok_rwZ; cbn; lia.
    - replace (v_addi (Z_to_bv 64 0xe1e4c) 4) with (Z_to_bv 64 0xe1e50) by (apply bv_eq; reflexivity).
      lazymatch type of HR with regs_ok ?E ?sr ?Rc =>
        pose proof (regs_set_a0 E sr Rc (errno_ret EISDIR) (ELit (2 ^ 64 - 21)) HR ltac:(apply bv_eq; reflexivity)) as HR2 end.
      clear HR. rename HR2 into HR. change (sr_upd srD1 (ridx 10) (ELit (2 ^ 64 - 21))) with srD2 in HR.

      run_blockd_keep 41%nat.
      lazymatch goal with EQM : ?M2 = mem_denot _ ?M1 ?lg |- _ =>
        assert (AG2 : forall x : word, ~ (sp0 - 4096 <= bv_unsigned x < sp0 - 128)%Z -> ~ (0x100614 <= bv_unsigned x < 0x100618)%Z -> M2 x = M1 x)
          by (intros x N1 N2; rewrite EQM; apply (mem_denot_foot_d (ENVh [] vals) M1 lg x lgD2_in); cbn [ev ENVh]; rewrite ?P0, ?Uspw; lia);
        assert (HG2 : mem_grows M1 M2) by (rewrite EQM; apply mem_denot_grows);
        clear EQM
      end.
      lazymatch goal with |- srealizes _ (mkCfg (mkst ?Rc _ ?Mc _) _) _ =>
        assert (AG : forall i, ~ (sp0 - 4096 <= i < sp0 - 128)%Z -> ~ (0x100614 <= i < 0x100618)%Z -> 0 <= i < 2 ^ 64 -> Mc (Z_to_bv 64 i) = M0 (Z_to_bv 64 i))
          by (intros i N1 N2 Hi; rewrite AG2, AG1; try reflexivity; rewrite u64_lit by lia; lia);
        apply (TAIL Rc Mc)
      end.
      pose proof (rm_img _ _ _ _ _ RM) as RI.
      constructor.
      + regv HR (2%bv : reg). rewrite edenot_add_lit. unfold adenot, v_addi. cbn [a_base a_off edenot ev ENVh]. rewrite P0, Uspw, Usp0. f_equal; lia.
      + regv HR (3%bv : reg). reflexivity.
      + regv HR (4%bv : reg). reflexivity.
      + regv HR (18%bv : reg). cbn [edenot ev ENVh]. rewrite P1v. apply bv_eq. rewrite u_small by lia. symmetry. exact Up1.
      + intros d m Hd Hm. rewrite Usp0. eapply store_ok_mono; [exact HG2|]. eapply store_ok_mono; [exact HG1|]. apply (rm_stack _ _ _ _ _ RM); lia.
      + rewrite re_ivs_eq. apply Forall_forall. intros [lo hi] Hin. cbn [fst snd].
        pose proof (proj1 (Forall_forall _ _) rimg_facts _ Hin) as F. cbn [fst snd] in F.
        pose proof (proj1 (Forall_forall _ _) RI _ Hin) as C. cbn [fst snd] in C.
        intros i Hi. rewrite AG by lia. apply C. lia.
      + eapply cell_agree; [lia | lia | intros; apply AG; lia | exact (rm_tid _ _ _ _ _ RM)].
      + exact Htid.
      + eapply cell_agree; [lia | lia | intros; apply AG; lia | exact (rm_self _ _ _ _ _ RM)].
      + eapply cell_agree; [lia | lia | intros; apply AG; lia | ].
        exact (mcg_guard_cell MI MC A M0 mo AI).
      + eapply cell_agree; [lia | lia | intros; apply AG; lia | ].
        eapply static_cell; [exact SCp | reflexivity | apply byte_list_eq; vm_compute; reflexivity].
      + eapply cell_agree; [lia | lia | intros; apply AG; lia | ].
        eapply static_cell; [exact SCn | reflexivity | apply byte_list_eq; vm_compute; reflexivity].
      +
        pose proof (rm_path _ _ _ _ _ RM) as RP. rewrite Hdot in RP. cbn [length Nat.add app dot_path] in RP.
        rewrite <- RP. replace p1w with (Z_to_bv 64 p1) by (apply bv_eq; rewrite u_small by lia; symmetry; exact Up1).
        apply rdn_ext; [rewrite u_small by lia; lia|]. intros x Hx. rewrite u_small in Hx by lia.
        rewrite <- (Z_to_bv_bv_unsigned 64 x). apply AG; lia.
      + exists t8. rewrite <- Ht8. rewrite Up1. rewrite Hdot. cbn [length Z.of_nat Pos.of_succ_nat Pos.succ dot_path].
        apply rdn_ext; [rewrite u_small by lia; lia|]. intros x Hx. rewrite u_small in Hx by lia.
        rewrite <- (Z_to_bv_bv_unsigned 64 x). apply AG; lia.
      + eapply drv_cells_ok_agree2; [|exact (rmem_drv_cells _ _ _ _ _ RM)]. intros i Hi Hne. apply AG; lia.
  Qed.
End Mid.
End FXALL.
