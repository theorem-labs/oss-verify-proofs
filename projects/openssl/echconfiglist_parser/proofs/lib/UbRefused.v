(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool String.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.openssl.echconfiglist_parser.images Require Import Ubsan.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib Require Import Amb PropExec CatExec CatSim SeqExec StoreOk ShapeAlg Nodes Hoare Frame SpecConsts MmapSim AllocSim FileSim AgentLib SymExec SymExec2 SymExec2Sound SymRun SymDrive SymDriveX SymDriveH4 Spec ShapeLaws LibWritev UbExitBase UbStdioDefs UbExit UbLibStdioCall RefMemcpyLib UbMemcpyBase UbMemcpy LibTail UbLibDiagKn UbPrintfBufBase UbReadErr_defs UbReadErr_tail UbReadErr.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib Require Import UbRefused_defs.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.
Import SX2. Import SX2S.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
Definition PRE14 : list byte := s2b "cli: input >= "%string.
Definition DIG8 : list byte := s2b "67108864"%string.
Definition SUF16 : list byte := s2b " bytes, refused"%string ++ [Z_to_bv 8 10].

Lemma msg_refused_split : msg_refused = PRE14 ++ DIG8 ++ SUF16.
Proof. reflexivity. Qed.

Lemma PRE14_words :
  word_to_le_bytes 8 (Z_to_bv 64 8101528366825958499) ++ word_to_le_bytes 4 (Z_to_bv 64 1042314357)
  ++ word_to_le_bytes 2 (Z_to_bv 64 8253) = PRE14.
Proof. vm_compute. repeat (apply (f_equal2 cons); [apply bv_eq; reflexivity|]). reflexivity. Qed.
Lemma DIG8_word : word_to_le_bytes 8 (Z_to_bv 64 3762256352692483894) = DIG8.
Proof. vm_compute. repeat (apply (f_equal2 cons); [apply bv_eq; reflexivity|]). reflexivity. Qed.
Lemma DIG8_bytes :
  word_to_le_bytes 1 (Z_to_bv 64 54) ++ word_to_le_bytes 1 (Z_to_bv 64 55) ++ word_to_le_bytes 1 (Z_to_bv 64 49)
  ++ word_to_le_bytes 1 (Z_to_bv 64 48) ++ word_to_le_bytes 1 (Z_to_bv 64 56) ++ word_to_le_bytes 1 (Z_to_bv 64 56)
  ++ word_to_le_bytes 1 (Z_to_bv 64 54) ++ word_to_le_bytes 1 (Z_to_bv 64 52) = DIG8.
Proof. vm_compute. repeat (apply (f_equal2 cons); [apply bv_eq; reflexivity|]). reflexivity. Qed.
Lemma SUF16_words :
  word_to_le_bytes 8 (Z_to_bv 64 2318354787771965984) ++ word_to_le_bytes 8 (Z_to_bv 64 748834984615634290) = SUF16.
Proof. vm_compute. repeat (apply (f_equal2 cons); [apply bv_eq; reflexivity|]). reflexivity. Qed.
Lemma pre14_img : rdn RSEGS (fun _ => None) (Z_to_bv 64 0x2641d) 14 = Some PRE14.
Proof. vm_compute. reflexivity. Qed.
Lemma suf16_img : rdn RSEGS (fun _ => None) (Z_to_bv 64 0x2642d) 16 = Some SUF16.
Proof. vm_compute. reflexivity. Qed.
Lemma PRE14_len : length PRE14 = 14%nat. Proof. reflexivity. Qed.
Lemma DIG8_len : length DIG8 = 8%nat. Proof. reflexivity. Qed.
Lemma SUF16_len : length SUF16 = 16%nat. Proof. reflexivity. Qed.

Section Refused.
  Variable sp0 : word.
  Ltac at_addr k H :=
    lazymatch goal with |- rdn _ _ (Z_to_bv 64 ?a) _ = _ => replace a with (bv_unsigned sp0 + k)%Z by lia; exact H end.
  Variable BL : list (list byte).
  Variable model : Model.
  Hypothesis Hvsp : valid_sp sp0.
  Hypothesis Hh : m_halted model = None.
  Hypothesis Hlazy : m_vm_lazy model = [].
  Hypothesis Hfd2 : fd_lookup (m_fds model) (Z_to_bv 64 2) = Some (FdChannel (Z_to_bv 64 2)).

  Let SPlo : (0x7fff80000000 <= bv_unsigned sp0)%Z := proj1 Hvsp.
  Let SPhi : (bv_unsigned sp0 <= 0x800000000000)%Z := proj1 (proj2 Hvsp).
  Let T : TSet := t_emit (W 2 msg_refused) (t_exit (exit_code 2) (m_fs model)).

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma rf_segH : forall vals R M,
    length vals = 231%nat -> vals_ev vals 0 = sp0 ->
    regs_ok (ENV BL vals) srH0 R -> know_ok RSEGS (ENV BL vals) M knH0 ->
    realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x2ba6f0) M (seg_rom RSEGS)) model)
               (t_exit (exit_code 2) (m_fs model)).
  Proof.
    intros vals R M HL P0 HR HK.
    pose proof SPlo as Hlo. pose proof SPhi as Hhi.
    run_blk scr0 231%nat.
    apply (rz_conseq RSEGS _ (t_emit (W 1 []) (t_exit (bv_and (Z_to_bv 64 2) (Z_to_bv 64 255)) (m_fs model)))).
    2:{ cbn [W map].
        replace (bv_and (Z_to_bv 64 2) (Z_to_bv 64 255)) with (exit_code 2) by (apply bv_eq; reflexivity).
        apply t_eq_sym. apply t_emit_nil_exit. }
    apply ref_exit_Z.
    pose proof (know_nth RSEGS _ _ knH ltac:(let i := kidx knH (is_krange (EVar 5)) in exact i) _ HK eq_refl)
      as Ktid; cbn [kentry_ok edenot ev ENV] in Ktid.
    exists (Z_to_bv 64 (bv_unsigned sp0 - 128)), (Z_to_bv 64 0x336098), (bv_unsigned (vals_ev vals 5)),
           (Z_to_bv 64 0), (Z_to_bv 64 0).
    split; [|split; [exact Hh|split; [exact Hlazy|]]].
    + constructor.
      * regv HR (2 : reg). rewrite edenot_add_lit. unfold adenot, v_addi. cbn [a_base a_off edenot ev ENV].
        rewrite P0. f_equal; lia.
      * regv HR (4 : reg). reflexivity.
      * regv HR (10 : reg). reflexivity.
      * rewrite u_small by lia. lia.
      * rewrite u_small by lia. lia.
      * rewrite u_small by lia.
        pose proof (kwr_store_ok RSEGS (ENV BL vals) _ knH ltac:(let i := kidx knH (is_kwr_cov (EVar 0) (-272) 144) in exact i)
                      _ _ _ (-272) 144 HK eq_refl ltac:(lia) ltac:(cbn; lia)) as Hst.
        unfold adenot, v_addi in Hst. cbn [a_base a_off edenot ev ENV] in Hst. rewrite P0 in Hst.
        replace (bv_unsigned sp0 - 128 - 144)%Z with (bv_unsigned sp0 + -272)%Z by lia. exact Hst.
      * lit_u. lia.
      * lit_u. lia.
      * lia.
      * lit_u. change (3367064 - 168)%Z with 0x335ff0%Z.
        krd HK 0x335ff0%Z 4%nat Htc. rewrite Htc. cbn [ev ENV].
        rewrite ext_val_zx_id by (change (2 ^ (8 * Z.of_nat 4))%Z with 4294967296%Z; lia).
        rewrite Z_to_bv_bv_unsigned. reflexivity.
      * krd_solve HK.
      * krd_solve HK.
      * krd_solve HK.
      * krd_solve HK.
      * krd_solve HK.
      * krd_solve HK.
      * krd_solve HK.
      * krd_solve HK.
      * krd_solve HK.
      * exists false. cbn [atexit_cells]. krd_solve HK.   (* [comment removed for export] *)
      * krd_solve HK.   (* [comment removed for export] *)
      * eexists. krd_solve HK.   (* [comment removed for export] *)
      * krd_solve HK.   (* [comment removed for export] *)
      * repeat split; krd_solve HK.
      * repeat split; krd_solve HK.   (* [comment removed for export] *)
      * repeat split; krd_solve HK.
    + left. split; [reflexivity|].
      exists (Z_to_bv 64 0), (Z_to_bv 64 0). repeat split; krd_solve HK.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma rf_segG : forall vals R M,
    length vals = 199%nat -> vals_ev vals 0 = sp0 ->
    regs_ok (ENV BL vals) srG0 R -> know_ok RSEGS (ENV BL vals) M knG0 ->
    realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x2ba360) M (seg_rom RSEGS)) model) T.
  Proof.
    intros vals R M HL P0 HR HK.
    pose proof SPlo as Hlo. pose proof SPhi as Hhi.
    run_blk scr0 199%nat.
    (* [comment removed for export] *)
    krdv HK 0%nat (-560)%Z 8%nat Hw0. { apply flat_intro; cbn [edenot ev ENV]; rewrite ?P0; lia. }
    krdv HK 0%nat (-552)%Z 4%nat Hw1. { apply flat_intro; cbn [edenot ev ENV]; rewrite ?P0; lia. }
    krdv HK 0%nat (-548)%Z 2%nat Hw2. { apply flat_intro; cbn [edenot ev ENV]; rewrite ?P0; lia. }
    krdv HK 0%nat (-546)%Z 8%nat Hw3. { apply flat_intro; cbn [edenot ev ENV]; rewrite ?P0; lia. }
    krdv HK 0%nat (-538)%Z 8%nat Hw4. { apply flat_intro; cbn [edenot ev ENV]; rewrite ?P0; lia. }
    krdv HK 0%nat (-530)%Z 8%nat Hw5. { apply flat_intro; cbn [edenot ev ENV]; rewrite ?P0; lia. }
    unfold adenot, v_addi in Hw0, Hw1, Hw2, Hw3, Hw4, Hw5.
    cbn [a_base a_off edenot ev ENV] in Hw0, Hw1, Hw2, Hw3, Hw4, Hw5.
    rewrite P0 in Hw0, Hw1, Hw2, Hw3, Hw4, Hw5.
    assert (MSG : rdn RSEGS M (Z_to_bv 64 (bv_unsigned sp0 + -560)) ((8 + (4 + 2)) + (8 + (8 + 8)))
                  = Some msg_refused).
    { rewrite msg_refused_split, <- PRE14_words, <- DIG8_word, <- SUF16_words.
      apply rdn_app_Z; [ | | lia | lia].
      - apply rdn_app_Z; [exact Hw0 | | lia | lia].
        apply rdn_app_Z; [at_addr (-552)%Z Hw1 | at_addr (-548)%Z Hw2 | lia | lia].
      - apply rdn_app_Z; [at_addr (-546)%Z Hw3 | | lia | lia].
        apply rdn_app_Z; [at_addr (-538)%Z Hw4 | at_addr (-530)%Z Hw5 | lia | lia]. }
    (* [comment removed for export] *)
    unfold T.
    replace (W 2 msg_refused) with (map (WriteEv (Z_to_bv 64 2)) (msg_refused ++ []))
      by (unfold W; rewrite app_nil_r; reflexivity).
    pose proof itinerary_rf as (_ & _ & _ & _ & _ & _ & SC & _).
    lazymatch goal with |- realizes _ (mkCfg (mkst ?Rc _ ?Mc _) _) _ =>
    apply (stdio_call_sound vals (blobs_ev BL) srG knG Rc Mc model scRF msg_refused []
             (t_exit (exit_code 2) (m_fs model)) HR HK (eq_trans (f_equal (fun n => stdio_call n srG knG) HL) SC));
      cbn [sc_f sc_fd sc_ret sc_wb sc_wp sc_bufp sc_bufsz sc_s sc_l sc_sp sc_sr sc_kn scRF];
      change (@length byte msg_refused) with 38%nat; cbn [length Z.of_nat Pos.of_succ_nat Pos.succ] end.
    - ed_lin ltac:(cbn [ev ENV]; rewrite ?P0). unorm. lia.
    - ed_lin ltac:(cbn [ev ENV]; rewrite ?P0). unorm. lia.
    - ed_lin ltac:(cbn [ev ENV]; rewrite ?P0). unorm. lia.
    - cbn [edenot]. reflexivity.
    - lia.
    - right. ed_lin ltac:(cbn [ev ENV]; rewrite ?P0). unorm. lia.
    - left. ed_lin ltac:(cbn [ev ENV]; rewrite ?P0). unorm. lia.
    - cbn [edenot]. unorm. lia.
    - ed_lin ltac:(cbn [ev ENV]; rewrite ?P0). unorm.
      change 38%nat with ((8 + (4 + 2)) + (8 + (8 + 8)))%nat. exact MSG.
    - reflexivity.
    - exact Hfd2.
    - exact Hh.
    - exact Hlazy.
    - apply t_exit_has_nil.
    - (* [comment removed for export] *)
      clear HR HK. intros R2 M2 HR HK.
      eapply (rf_segH (vals ++ junk_vals R2));
        [ rewrite length_app, junk_vals_length, HL; reflexivity
        | rewrite vals_ev_app_l by (rewrite HL; lia); exact P0
        | exact HR | exact HK ].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  (* [comment removed for export] *)
  Lemma memcpy1_denot : forall vals M, vals_ev vals 0 = sp0 ->
    mem_denot (ENV BL vals) M logM1 = wbytes M (Z_to_bv 64 (bv_unsigned sp0 - 560)) PRE14.
  Proof.
    intros vals M P0. pose proof SPlo. pose proof SPhi.
    rewrite <- PRE14_words. cbn [mem_denot logM1]. rewrite !wbytes_app.
    unfold adenot, v_addi, at_. cbn [a_base a_off edenot ev ENV length Z.of_nat Pos.of_succ_nat Pos.succ]. rewrite P0.
    rewrite !length_N_to_le_bytes. cbn [Z.of_nat Pos.of_succ_nat Pos.succ]. unorm.
    repeat (f_equal; try (f_equal; lia)).
  Qed.
  Lemma memcpy4_denot : forall vals M, vals_ev vals 0 = sp0 ->
    mem_denot (ENV BL vals) M logM4 = wbytes M (Z_to_bv 64 (bv_unsigned sp0 - 546)) DIG8.
  Proof.
    intros vals M P0. pose proof SPlo. pose proof SPhi.
    rewrite <- DIG8_word. cbn [mem_denot logM4].
    unfold adenot, v_addi. cbn [a_base a_off edenot ev ENV]. rewrite P0.
    repeat (f_equal; try (f_equal; lia)).
  Qed.
  Lemma memcpy5_denot : forall vals M, vals_ev vals 0 = sp0 ->
    mem_denot (ENV BL vals) M logM5 = wbytes M (Z_to_bv 64 (bv_unsigned sp0 - 538)) SUF16.
  Proof.
    intros vals M P0. pose proof SPlo. pose proof SPhi.
    rewrite <- SUF16_words. cbn [mem_denot logM5]. rewrite !wbytes_app.
    unfold adenot, v_addi, at_. cbn [a_base a_off edenot ev ENV length Z.of_nat Pos.of_succ_nat Pos.succ]. rewrite P0.
    rewrite !length_N_to_le_bytes. cbn [Z.of_nat Pos.of_succ_nat Pos.succ]. unorm.
    repeat (f_equal; try (f_equal; lia)).
  Qed.

  (* [comment removed for export] *)
  Ltac after_memcpy HL Hms Hkeep :=
    replace (Z_to_bv 64 2884848) with (0x2c04f0 : word) by (apply bv_eq; reflexivity);
    eapply rz_msteps; [exact Hh | exact Hlazy | exact Hms |]; clear Hms;
    replace (0x2ba360 : word) with (Z_to_bv 64 0x2ba360) by (apply bv_eq; reflexivity);
    lazymatch goal with H : regs_ok ?E ?sr ?Rc |- realizes _ (mkCfg (mkst ?R2 _ _ _) _) _ =>
      pose proof (regs_after_keeps _ (blobs_ev BL) sr Rc R2 callee_kept
                    ltac:(rewrite HL; vm_compute; reflexivity) H Hkeep callee_kept_no0) as HR2;
      rewrite HL in HR2; clear H Hkeep; rename HR2 into HR
    end.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma rf_segF : forall vals R M,
    length vals = 167%nat -> vals_ev vals 0 = sp0 ->
    regs_ok (ENV BL vals) srF0 R -> know_ok RSEGS (ENV BL vals) M knF0 ->
    realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x2ba360) M (seg_rom RSEGS)) model) T.
  Proof.
    intros vals R M HL P0 HR HK.
    pose proof SPlo as Hlo. pose proof SPhi as Hhi.
    run_blk scr0 167%nat.
    set (dst := Z_to_bv 64 (bv_unsigned sp0 - 538)).
    assert (Hsrc : rdn RSEGS M (Z_to_bv 64 0x2642d) 16 = Some SUF16).
    { rewrite (kimg_rdn RSEGS (ENV BL vals) _ knF ltac:(let i := kidx knF (is_kimg_cov 0x2642d 16) in exact i)
                 _ _ 0x2642d 16 HK eq_refl) by (cbn; lia). apply suf16_img. }
    assert (Hdst : store_ok RSEGS M dst 16 = true).
    { pose proof (kwr_store_ok RSEGS (ENV BL vals) _ knF ltac:(let i := kidx knF (is_kwr_cov (EVar 0) (-538) 16) in exact i)
                    _ _ _ (-538) 16 HK eq_refl ltac:(lia) ltac:(cbn; lia)) as Hst.
      unfold adenot, v_addi in Hst. cbn [a_base a_off edenot ev ENV] in Hst. rewrite P0 in Hst.
      subst dst. replace (bv_unsigned sp0 - 538)%Z with (bv_unsigned sp0 + -538)%Z by lia. exact Hst. }
    assert (MC : mcH M dst (Z_to_bv 64 0x2642d) 16 SUF16).
    { constructor; subst dst; rewrite ?u_small by lia; try (cbn; lia).
      - exact Hsrc.
      - exact Hdst. }
    lazymatch goal with |- realizes _ (mkCfg (mkst ?Rc _ _ _) _) _ =>
      assert (A1 : getr Rc 1 = (0x2ba360 : word)) by (regv HR (1 : reg); apply bv_eq; reflexivity);
      assert (A10 : getr Rc 10 = dst)
        by (regv HR (10 : reg); subst dst; ed_lin ltac:(cbn [ev ENV]; rewrite ?P0); f_equal; lia);
      assert (A11 : getr Rc 11 = Z_to_bv 64 0x2642d) by (regv HR (11 : reg); reflexivity);
      assert (A12 : getr Rc 12 = Z_to_bv 64 16) by (regv HR (12 : reg); reflexivity);
      destruct (ref_memcpy M dst (Z_to_bv 64 0x2642d) 16 _ (seg_rom RSEGS) MC Rc (0x2ba360 : word)
                  ltac:(apply ret_ok_even; reflexivity) A1 A10 A11 A12) as (R2 & Hms & Hkeep);
      clear A1 A10 A11 A12
    end.
    after_memcpy HL Hms Hkeep.
    assert (HK2 : know_ok RSEGS (ENV BL vals) (wbytes M dst SUF16) knG0).
    { subst dst. rewrite <- (memcpy5_denot vals M P0).
      eapply (carry_after RSEGS (ENV BL vals) M logM5 knF [] knG0 [] []);
        [vm_compute; reflexivity | | exact HK | constructor].
      cbn [log_flat logM5].
      repeat match goal with
             | |- flat _ _ _ => apply flat_intro; cbn [edenot ev ENV]; rewrite ?P0; lia
             | |- (_ <= _)%nat => lia
             | |- True => exact I
             | |- _ /\ _ => split
             end. }
    clear HK.
    pose proof (env_app_know RSEGS vals (junk_vals R2) (blobs_ev BL) (wbytes M dst SUF16) knG0
                  ltac:(rewrite HL; vm_compute; reflexivity) HK2) as HK.
    clear HK2.
    set (vals1 := vals ++ junk_vals R2) in *.
    assert (HL1 : length vals1 = 199%nat) by (subst vals1; rewrite length_app, junk_vals_length, HL; reflexivity).
    assert (Q0 : vals_ev vals1 0 = sp0) by (subst vals1; rewrite vals_ev_app_l by (rewrite HL; lia); exact P0).
    clearbody vals1.
    change (Env (vals_ev vals1) (blobs_ev BL)) with (ENV BL vals1) in HR, HK.
    eapply (rf_segG vals1); eassumption.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma rf_segE : forall vals R M,
    length vals = 135%nat -> vals_ev vals 0 = sp0 ->
    regs_ok (ENV BL vals) srE0 R -> know_ok RSEGS (ENV BL vals) M knD ->
    realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x2ba360) M (seg_rom RSEGS)) model) T.
  Proof.
    intros vals R M HL P0 HR HK.
    pose proof SPlo as Hlo. pose proof SPhi as Hhi.
    run_blk scr0 135%nat.
    set (dst := Z_to_bv 64 (bv_unsigned sp0 - 546)).
    set (src := Z_to_bv 64 (bv_unsigned sp0 - 952)).
    (* [comment removed for export] *)
    krdv HK 0%nat (-952)%Z 1%nat Hd0. { apply flat_intro; cbn [edenot ev ENV]; rewrite ?P0; lia. }
    krdv HK 0%nat (-951)%Z 1%nat Hd1. { apply flat_intro; cbn [edenot ev ENV]; rewrite ?P0; lia. }
    krdv HK 0%nat (-950)%Z 1%nat Hd2. { apply flat_intro; cbn [edenot ev ENV]; rewrite ?P0; lia. }
    krdv HK 0%nat (-949)%Z 1%nat Hd3. { apply flat_intro; cbn [edenot ev ENV]; rewrite ?P0; lia. }
    krdv HK 0%nat (-948)%Z 1%nat Hd4. { apply flat_intro; cbn [edenot ev ENV]; rewrite ?P0; lia. }
    krdv HK 0%nat (-947)%Z 1%nat Hd5. { apply flat_intro; cbn [edenot ev ENV]; rewrite ?P0; lia. }
    krdv HK 0%nat (-946)%Z 1%nat Hd6. { apply flat_intro; cbn [edenot ev ENV]; rewrite ?P0; lia. }
    krdv HK 0%nat (-945)%Z 1%nat Hd7. { apply flat_intro; cbn [edenot ev ENV]; rewrite ?P0; lia. }
    unfold adenot, v_addi in Hd0, Hd1, Hd2, Hd3, Hd4, Hd5, Hd6, Hd7.
    cbn [a_base a_off edenot ev ENV] in Hd0, Hd1, Hd2, Hd3, Hd4, Hd5, Hd6, Hd7.
    rewrite P0 in Hd0, Hd1, Hd2, Hd3, Hd4, Hd5, Hd6, Hd7.
    assert (Hsrc : rdn RSEGS M src (1 + (1 + (1 + (1 + (1 + (1 + (1 + 1))))))) = Some DIG8).
    { subst src. replace (bv_unsigned sp0 - 952)%Z with (bv_unsigned sp0 + -952)%Z by lia. rewrite <- DIG8_bytes.
      apply rdn_app_Z; [exact Hd0 | | lia | lia].
      apply rdn_app_Z; [at_addr (-951)%Z Hd1 | | lia | lia].
      apply rdn_app_Z; [at_addr (-950)%Z Hd2 | | lia | lia].
      apply rdn_app_Z; [at_addr (-949)%Z Hd3 | | lia | lia].
      apply rdn_app_Z; [at_addr (-948)%Z Hd4 | | lia | lia].
      apply rdn_app_Z; [at_addr (-947)%Z Hd5 | | lia | lia].
      apply rdn_app_Z; [at_addr (-946)%Z Hd6 | at_addr (-945)%Z Hd7 | lia | lia]. }
    assert (Hdst : store_ok RSEGS M dst 8 = true).
    { pose proof (kwr_store_ok RSEGS (ENV BL vals) _ knE ltac:(let i := kidx knE (is_kwr_cov (EVar 0) (-546) 8) in exact i)
                    _ _ _ (-546) 8 HK eq_refl ltac:(lia) ltac:(cbn; lia)) as Hst.
      unfold adenot, v_addi in Hst. cbn [a_base a_off edenot ev ENV] in Hst. rewrite P0 in Hst.
      subst dst. replace (bv_unsigned sp0 - 546)%Z with (bv_unsigned sp0 + -546)%Z by lia. exact Hst. }
    assert (MC : mcH M dst src 8 DIG8).
    { constructor; subst dst src; rewrite ?u_small by lia; try (cbn; lia).
      - exact Hsrc.
      - exact Hdst. }
    lazymatch goal with |- realizes _ (mkCfg (mkst ?Rc _ _ _) _) _ =>
      assert (A1 : getr Rc 1 = (0x2ba360 : word)) by (regv HR (1 : reg); apply bv_eq; reflexivity);
      assert (A10 : getr Rc 10 = dst)
        by (regv HR (10 : reg); subst dst; ed_lin ltac:(cbn [ev ENV]; rewrite ?P0); f_equal; lia);
      assert (A11 : getr Rc 11 = src)
        by (regv HR (11 : reg); subst src; ed_lin ltac:(cbn [ev ENV]; rewrite ?P0); f_equal; lia);
      assert (A12 : getr Rc 12 = Z_to_bv 64 8) by (regv HR (12 : reg); reflexivity);
      destruct (ref_memcpy M dst src 8 _ (seg_rom RSEGS) MC Rc (0x2ba360 : word)
                  ltac:(apply ret_ok_even; reflexivity) A1 A10 A11 A12) as (R2 & Hms & Hkeep);
      clear A1 A10 A11 A12
    end.
    after_memcpy HL Hms Hkeep.
    assert (HK2 : know_ok RSEGS (ENV BL vals) (wbytes M dst DIG8) knF0).
    { subst dst. rewrite <- (memcpy4_denot vals M P0).
      eapply (carry_after RSEGS (ENV BL vals) M logM4 knE [] knF0 [] []);
        [vm_compute; reflexivity | | exact HK | constructor].
      cbn [log_flat logM4].
      repeat match goal with
             | |- flat _ _ _ => apply flat_intro; cbn [edenot ev ENV]; rewrite ?P0; lia
             | |- (_ <= _)%nat => lia
             | |- True => exact I
             | |- _ /\ _ => split
             end. }
    clear HK.
    pose proof (env_app_know RSEGS vals (junk_vals R2) (blobs_ev BL) (wbytes M dst DIG8) knF0
                  ltac:(rewrite HL; vm_compute; reflexivity) HK2) as HK.
    clear HK2.
    set (vals1 := vals ++ junk_vals R2) in *.
    assert (HL1 : length vals1 = 167%nat) by (subst vals1; rewrite length_app, junk_vals_length, HL; reflexivity).
    assert (Q0 : vals_ev vals1 0 = sp0) by (subst vals1; rewrite vals_ev_app_l by (rewrite HL; lia); exact P0).
    clearbody vals1.
    change (Env (vals_ev vals1) (blobs_ev BL)) with (ENV BL vals1) in HR, HK.
    eapply (rf_segF vals1); eassumption.
  Qed.

  (* [comment removed for export] *)
  Ltac memcpy0_step HL P0 srcZ :=
    let dst := fresh "dst" in
    set (dst := Z_to_bv 64 (bv_unsigned sp0 - 546));
    lazymatch goal with HR : regs_ok _ _ ?Rc |- realizes _ (mkCfg (mkst ?Rc _ ?Mc _) _) _ =>
      assert (MC : mcH Mc dst (Z_to_bv 64 srcZ) 0 [])
        by (constructor; subst dst; rewrite ?u_small by lia; cbn [length]; try lia; reflexivity);
      assert (A1 : getr Rc 1 = (0x2ba360 : word)) by (regv HR (1 : reg); apply bv_eq; reflexivity);
      assert (A10 : getr Rc 10 = dst)
        by (regv HR (10 : reg); subst dst; ed_lin ltac:(cbn [ev ENV]; rewrite ?P0); f_equal; lia);
      assert (A11 : getr Rc 11 = Z_to_bv 64 srcZ) by (regv HR (11 : reg); reflexivity);
      assert (A12 : getr Rc 12 = Z_to_bv 64 0) by (regv HR (12 : reg); reflexivity);
      destruct (ref_memcpy Mc dst (Z_to_bv 64 srcZ) 0 _ (seg_rom RSEGS) MC Rc (0x2ba360 : word)
                  ltac:(apply ret_ok_even; reflexivity) A1 A10 A11 A12) as (R2 & Hms & Hkeep);
      clear A1 A10 A11 A12 MC;
      after_memcpy HL Hms Hkeep;
      change (wbytes Mc dst []) with Mc
    end.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma rf_segD : forall vals R M,
    length vals = 103%nat -> vals_ev vals 0 = sp0 ->
    regs_ok (ENV BL vals) srD0 R -> know_ok RSEGS (ENV BL vals) M knC ->
    realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x2ba360) M (seg_rom RSEGS)) model) T.
  Proof.
    intros vals R M HL P0 HR HK.
    pose proof SPlo as Hlo. pose proof SPhi as Hhi.
    run_blk scr0 103%nat.
    memcpy0_step HL P0 0x11686%Z.
    lazymatch goal with |- realizes _ (mkCfg (mkst ?R2 _ ?Mc _) _) _ =>
      pose proof (env_app_know RSEGS vals (junk_vals R2) (blobs_ev BL) Mc knD ltac:(rewrite HL; vm_compute; reflexivity) HK) as HK2;
      clear HK; rename HK2 into HK;
      set (vals1 := vals ++ junk_vals R2) in *
    end.
    assert (HL1 : length vals1 = 135%nat) by (subst vals1; rewrite length_app, junk_vals_length, HL; reflexivity).
    assert (Q0 : vals_ev vals1 0 = sp0) by (subst vals1; rewrite vals_ev_app_l by (rewrite HL; lia); exact P0).
    clearbody vals1.
    change (Env (vals_ev vals1) (blobs_ev BL)) with (ENV BL vals1) in HR, HK.
    eapply (rf_segE vals1); eassumption.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma rf_segC : forall vals R M,
    length vals = 71%nat -> vals_ev vals 0 = sp0 ->
    regs_ok (ENV BL vals) srC0 R -> know_ok RSEGS (ENV BL vals) M knC0 ->
    realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x2ba360) M (seg_rom RSEGS)) model) T.
  Proof.
    intros vals R M HL P0 HR HK.
    pose proof SPlo as Hlo. pose proof SPhi as Hhi.
    run_blk scr0 71%nat.
    memcpy0_step HL P0 0x2642b%Z.
    lazymatch goal with |- realizes _ (mkCfg (mkst ?R2 _ ?Mc _) _) _ =>
      pose proof (env_app_know RSEGS vals (junk_vals R2) (blobs_ev BL) Mc knC ltac:(rewrite HL; vm_compute; reflexivity) HK) as HK2;
      clear HK; rename HK2 into HK;
      set (vals1 := vals ++ junk_vals R2) in *
    end.
    assert (HL1 : length vals1 = 103%nat) by (subst vals1; rewrite length_app, junk_vals_length, HL; reflexivity).
    assert (Q0 : vals_ev vals1 0 = sp0) by (subst vals1; rewrite vals_ev_app_l by (rewrite HL; lia); exact P0).
    clearbody vals1.
    change (Env (vals_ev vals1) (blobs_ev BL)) with (ENV BL vals1) in HR, HK.
    eapply (rf_segD vals1); eassumption.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma rf_segB : forall vals R M,
    length vals = 39%nat -> vals_ev vals 0 = sp0 ->
    regs_ok (ENV BL vals) srRF0 R -> know_ok RSEGS (ENV BL vals) M knRE0 ->
    realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0xe255c) M (seg_rom RSEGS)) model) T.
  Proof.
    intros vals R M HL P0 HR HK.
    pose proof SPlo as Hlo. pose proof SPhi as Hhi.
    run_blk scr0 39%nat.
    set (dst := Z_to_bv 64 (bv_unsigned sp0 - 560)).
    assert (Hsrc : rdn RSEGS M (Z_to_bv 64 0x2641d) 14 = Some PRE14).
    { rewrite (kimg_rdn RSEGS (ENV BL vals) _ knB ltac:(let i := kidx knB (is_kimg_cov 0x2641d 14) in exact i)
                 _ _ 0x2641d 14 HK eq_refl) by (cbn; lia). apply pre14_img. }
    assert (Hdst : store_ok RSEGS M dst 14 = true).
    { pose proof (kwr_store_ok RSEGS (ENV BL vals) _ knB ltac:(let i := kidx knB (is_kwr_cov (EVar 0) (-560) 14) in exact i)
                    _ _ _ (-560) 14 HK eq_refl ltac:(lia) ltac:(cbn; lia)) as Hst.
      unfold adenot, v_addi in Hst. cbn [a_base a_off edenot ev ENV] in Hst. rewrite P0 in Hst.
      subst dst. replace (bv_unsigned sp0 - 560)%Z with (bv_unsigned sp0 + -560)%Z by lia. exact Hst. }
    assert (MC : mcH M dst (Z_to_bv 64 0x2641d) 14 PRE14).
    { constructor; subst dst; rewrite ?u_small by lia; try (cbn; lia).
      - exact Hsrc.
      - exact Hdst. }
    lazymatch goal with |- realizes _ (mkCfg (mkst ?Rc _ _ _) _) _ =>
      assert (A1 : getr Rc 1 = (0x2ba360 : word)) by (regv HR (1 : reg); apply bv_eq; reflexivity);
      assert (A10 : getr Rc 10 = dst)
        by (regv HR (10 : reg); subst dst; ed_lin ltac:(cbn [ev ENV]; rewrite ?P0); f_equal; lia);
      assert (A11 : getr Rc 11 = Z_to_bv 64 0x2641d) by (regv HR (11 : reg); reflexivity);
      assert (A12 : getr Rc 12 = Z_to_bv 64 14) by (regv HR (12 : reg); reflexivity);
      destruct (ref_memcpy M dst (Z_to_bv 64 0x2641d) 14 _ (seg_rom RSEGS) MC Rc (0x2ba360 : word)
                  ltac:(apply ret_ok_even; reflexivity) A1 A10 A11 A12) as (R2 & Hms & Hkeep);
      clear A1 A10 A11 A12
    end.
    after_memcpy HL Hms Hkeep.
    assert (HK2 : know_ok RSEGS (ENV BL vals) (wbytes M dst PRE14) knC0).
    { subst dst. rewrite <- (memcpy1_denot vals M P0).
      eapply (carry_after RSEGS (ENV BL vals) M logM1 knB [] knC0 [] []);
        [vm_compute; reflexivity | | exact HK | constructor].
      cbn [log_flat logM1].
      repeat match goal with
             | |- flat _ _ _ => apply flat_intro; cbn [edenot ev ENV]; rewrite ?P0; lia
             | |- (_ <= _)%nat => lia
             | |- True => exact I
             | |- _ /\ _ => split
             end. }
    clear HK.
    pose proof (env_app_know RSEGS vals (junk_vals R2) (blobs_ev BL) (wbytes M dst PRE14) knC0
                  ltac:(rewrite HL; vm_compute; reflexivity) HK2) as HK.
    clear HK2.
    set (vals1 := vals ++ junk_vals R2) in *.
    assert (HL1 : length vals1 = 71%nat) by (subst vals1; rewrite length_app, junk_vals_length, HL; reflexivity).
    assert (Q0 : vals_ev vals1 0 = sp0) by (subst vals1; rewrite vals_ev_app_l by (rewrite HL; lia); exact P0).
    clearbody vals1.
    change (Env (vals_ev vals1) (blobs_ev BL)) with (ENV BL vals1) in HR, HK.
    eapply (rf_segC vals1); eassumption.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  Variables (tid can : Z) (R : bvmap 5 word) (M : word -> option byte).
  (* [comment removed for export] *)
  Hypothesis Rsp : getr R 2 = Z_to_bv 64 (bv_unsigned sp0 - 128).
  Hypothesis Rtp : getr R 4 = Z_to_bv 64 0x336098.
  (* [comment removed for export] *)
  Hypothesis Mstack : stk_ok RSEGS M (Z_to_bv 64 (bv_unsigned sp0 - 128)) RE_STK.
  Hypothesis Mro : forall i, (0x10000 <= i < 0x2c5000)%Z -> M (Z_to_bv 64 i) = None.
  Hypothesis Mcells : cells_ok M diag_cells.
  Hypothesis Mtid : rdn RSEGS M (Z_to_bv 64 0x335ff0) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 tid)).
  Hypothesis Htid : (0 < tid < 2 ^ 22)%Z.
  Hypothesis Mcan : canary_ok M can.

  Let E : env := ENV BL (valsRE sp0 sp0 tid can R).

  Lemma evRF_junk : forall i, (i < 32)%nat -> ev E (6 + i) = getr R (Z_to_bv 5 (Z.of_nat i)).
  Proof. intros i Hi. apply (evRE_junk sp0 BL sp0 tid can R i Hi). Qed.

  Ltac reg_caseRF :=
    cbn [nth srRF0 allregs32];
    first [ lazymatch goal with |- _ = edenot _ (EVar ?n) =>
              change (edenot E (EVar n)) with (ev E n);
              first [ rewrite (evRF_junk (n - 6)) by lia; reflexivity | idtac ]
            | |- _ => cbn [edenot] end ];
    first [ reflexivity
          | exact Rtp
          | rewrite Rsp, alu_add; change (ev E 0) with sp0; unfold v_add; apply bv_eq;
            rewrite !Z_to_bv_unsigned, !bv_wrap64_mod, Zplus_mod_idemp_r; f_equal; lia
          | idtac ].

  Lemma regs_okRF : regs_ok E srRF0 R.
  Proof.
    pose proof SPlo. pose proof SPhi.
    apply regs_ok_by_idx.
    intros i Hi.
    destruct i as [|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|i]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]; [ .. | lia]; reg_caseRF.
  Qed.

  Theorem ref_refused_tail :
    realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0xe255c) M (seg_rom RSEGS)) model)
               (t_die msg_refused (m_fs model)).
  Proof.
    pose proof SPlo. pose proof SPhi.
    unfold t_die.
    eapply (rf_segB (valsRE sp0 sp0 tid can R) R M (valsRE_len sp0 sp0 tid can R) eq_refl regs_okRF).
    apply (know_okRE sp0 BL Hvsp sp0 tid can R M Mstack Mro Mcells Mtid Htid Mcan); lia.
  Qed.
End Refused.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
