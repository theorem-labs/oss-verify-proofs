(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool String.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.mbedtls.fuzz_pkcs7.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import PropExec Shape.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BB Require Import Amb CatExec CatSim SeqExec StoreOk ShapeX Hoare BBFrame SpecConsts MmapSim AllocSim FileSim AgentLib SymExec SymExec2 SymExec2Sound SymRun SymDrive SymDriveX SymDriveH4 ShapeLaws MemcpyLib LibTail.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Sys Require Import Nodes LibWritev.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Spec Require Import Spec.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U Require Import U_exit_base U_stdio_defs U_exit U_stdio_call U_memcpy_base U_memcpy U_main_entry U_read_base U_world U_stdio_readerr_defs U_stdio_readerr_tail U_stdio_readerr.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U Require Import U_stdio_refused_defs.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import DietDestruct.   (* [comment removed for export] *)
Import ListNotations.
Open Scope bv_scope.
Import SX2. Import SX2S.
#[local] Existing Instance PropExec.fx0.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Ltac2 gd_tbl_P_stdio_refused () : Init.string Init.list := ["Corelib.Init.Logic.eq"; "Corelib.Init.Datatypes.list"; "stdpp.bitvector.definitions.bv"; "Corelib.Init.Datatypes.app"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.word_to_le_bytes"; "stdpp.bitvector.definitions.Z_to_bv"; "PRE14"; "DIG8"; "SUF16"; "LinuxProcessSemantics.Riscv.Prelude.bvmap"; "Corelib.Init.Datatypes.option"; "Corelib.Init.Datatypes.nat"; "Corelib.Init.Datatypes.length"; "RocqVerifyHarness.AgentSubmission.BB.SymRun.vals_ev"; "RocqVerifyHarness.AgentSubmission.BB.SymExec2Sound.SX2S.regs_ok"; "RocqVerifyHarness.AgentSubmission.U.U_stdio_readerr_tail.ENV"; "RocqVerifyHarness.AgentSubmission.U.U_stdio_refused_defs.srH0"; "RocqVerifyHarness.AgentSubmission.BB.SymExec2Sound.SX2S.know_ok"; "RocqVerifyHarness.ProcessOversight.Tgt_fuzz_pkcs7_ubsan.M.loaded_segments"; "RocqVerifyHarness.AgentSubmission.U.U_stdio_refused_defs.knH0"; "RocqVerifyHarness.AgentSubmission.Lib.Shape.realizes"; "LinuxProcessSemantics.LinuxProcessSem.Run.mkCfg"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.mkst"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.fx0"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.seg_rom"; "RocqVerifyHarness.AgentSubmission.Lib.Shape.t_exit"; "RocqVerifyHarness.AgentSubmission.Spec.Spec.exit_code"; "LinuxProcessSemantics.LinuxProcessSem.State.m_fs"; "RocqVerifyHarness.AgentSubmission.U.U_stdio_refused_defs.srG0"; "RocqVerifyHarness.AgentSubmission.U.U_stdio_refused_defs.knG0"; "RocqVerifyHarness.AgentSubmission.BB.SymExec2Sound.SX2S.mem_denot"; "RocqVerifyHarness.AgentSubmission.U.U_stdio_refused_defs.logM1"; "RocqVerifyHarness.AgentSubmission.BB.CatExec.wbytes"; "Stdlib.ZArith.BinInt.Z.sub"; "stdpp.bitvector.definitions.bv_unsigned"; "RocqVerifyHarness.AgentSubmission.U.U_stdio_refused_defs.logM4"; "RocqVerifyHarness.AgentSubmission.U.U_stdio_refused_defs.logM5"; "RocqVerifyHarness.AgentSubmission.U.U_stdio_refused_defs.srF0"; "RocqVerifyHarness.AgentSubmission.U.U_stdio_refused_defs.knF0"; "RocqVerifyHarness.AgentSubmission.U.U_stdio_refused_defs.srE0"; "RocqVerifyHarness.AgentSubmission.U.U_stdio_refused_defs.knD"; "RocqVerifyHarness.AgentSubmission.U.U_stdio_refused_defs.srD0"; "RocqVerifyHarness.AgentSubmission.U.U_stdio_refused_defs.knC"; "RocqVerifyHarness.AgentSubmission.U.U_stdio_refused_defs.srC0"; "RocqVerifyHarness.AgentSubmission.U.U_stdio_refused_defs.knC0"; "RocqVerifyHarness.AgentSubmission.U.U_stdio_refused_defs.srRF0"; "RocqVerifyHarness.AgentSubmission.U.U_stdio_readerr_defs.knRE0"; "RocqVerifyHarness.AgentSubmission.Spec.Spec.t_die"; "RocqVerifyHarness.AgentSubmission.Spec.Spec.msg_refused"].


(* [comment removed for export] *)
Definition PRE14 : list byte := s2b "cli: input >= "%string.
Definition DIG8 : list byte := s2b "67108864"%string.
Definition SUF16 : list byte := s2b " bytes, refused"%string ++ [Z_to_bv 8 10].

Lemma msg_refused_split : msg_refused = PRE14 ++ DIG8 ++ SUF16.
Proof. reflexivity. Qed.

Lemma PRE14_words : ltac2:(CDefT.buildp (gd_tbl_P_stdio_refused ()) "(0.(1.(2.&8.))(3.(2.&8.)(4.#8.(5.&40.+706>69203:696<63.))(3.(2.&8.)(4.#4.(5.&40.+3>207475.))(4.#2.(5.&40.+203=.))))$6.)")
(* [comment removed for export] *).
Proof. vm_compute. repeat (apply (f_equal2 cons); [apply bv_eq; reflexivity|]). reflexivity. Qed.
Lemma DIG8_word : word_to_le_bytes 8 (Z_to_bv 64 3762256352692483894) = DIG8.
Proof. vm_compute. repeat (apply (f_equal2 cons); [apply bv_eq; reflexivity|]). reflexivity. Qed.
Lemma DIG8_bytes : ltac2:(CDefT.buildp (gd_tbl_P_stdio_refused ()) "(0.(1.(2.&8.))(3.(2.&8.)(4.#1.(5.&40.+36.))(3.(2.&8.)(4.#1.(5.&40.+37.))(3.(2.&8.)(4.#1.(5.&40.+31.))(3.(2.&8.)(4.#1.(5.&40.+30.))(3.(2.&8.)(4.#1.(5.&40.+38.))(3.(2.&8.)(4.#1.(5.&40.+38.))(3.(2.&8.)(4.#1.(5.&40.+36.))(4.#1.(5.&40.+34.)))))))))$7.)")
(* [comment removed for export] *).
Proof. vm_compute. repeat (apply (f_equal2 cons); [apply bv_eq; reflexivity|]). reflexivity. Qed.
Lemma SUF16_words : ltac2:(CDefT.buildp (gd_tbl_P_stdio_refused ()) "(0.(1.(2.&8.))(3.(2.&8.)(4.#8.(5.&40.+202<736574796220.))(4.#8.(5.&40.+:64657375666572.)))$8.)")
(* [comment removed for export] *).
Proof. vm_compute. repeat (apply (f_equal2 cons); [apply bv_eq; reflexivity|]). reflexivity. Qed.
Lemma pre14_img : rdn RSEGS (fun _ => None) (Z_to_bv 64 0x106b7) 14 = Some PRE14.
Proof. vm_compute. reflexivity. Qed.
Lemma suf16_img : rdn RSEGS (fun _ => None) (Z_to_bv 64 0x106c7) 16 = Some SUF16.
Proof. vm_compute. reflexivity. Qed.

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
  #[using="Hvsp Hh Hlazy SPlo SPhi"] Lemma rf_segH : ltac2:(CDefT.buildp (gd_tbl_P_stdio_refused ()) "Pvals,(1.(2.&40.))PR,(9.&5.(2.&40.))PM,P,(2.&40.)(:.(2.&8.))P,(0.$;.(<.(2.&40.)R3.)#>7.)P,(0.(2.&40.)(=.R4.#0.)Vsp0,)P,(>.(?.VBL,R5.)$10.R4.)P,(11.$12.(?.VBL,R6.)R4.$13.)(14.$12.(15.(16.$17.R6.(5.&40.+420:8.)R5.(18.$12.))Vmodel,)(19.(1:.+2.)(1;.Vmodel,)))")
(* [comment removed for export] *).
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
    dexists (Z_to_bv 64 (bv_unsigned sp0 - 128)), (Z_to_bv 64 0x5d0c8), (bv_unsigned (vals_ev vals 5)),
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
      * lit_u. change (381128 - 168)%Z with 0x5d020%Z.
        krd HK 0x5d020%Z 4%nat Htc. rewrite Htc. cbn [ev ENV].
        rewrite ext_val_zx_id by (change (2 ^ (8 * Z.of_nat 4))%Z with 4294967296%Z; lia).
        rewrite Z_to_bv_bv_unsigned. reflexivity.
      * krd_solve HK.
      * krd_solve HK.
      * krd_solve HK.
      * krd_solve HK.
      * krd_solve HK.
      * krd_solve HK.
      * krd_solve HK.
      * repeat split; krd_solve HK.
      * repeat split; krd_solve HK.
      * krd_solve HK.                                                     (* [comment removed for export] *)
      * exists false. unfold atexit_st, atexit_none. split; krd_solve HK.  (* [comment removed for export] *)
    + left. split; [reflexivity|].
      dexists (Z_to_bv 64 0), (Z_to_bv 64 0). repeat split; krd_solve HK.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  #[using="Hvsp Hh Hlazy Hfd2 SPlo SPhi"] Lemma rf_segG : ltac2:(CDefT.buildp (gd_tbl_P_stdio_refused ()) "Pvals,(1.(2.&40.))PR,(9.&5.(2.&40.))PM,P,(2.&40.)(:.(2.&8.))P,(0.$;.(<.(2.&40.)R3.)#<7.)P,(0.(2.&40.)(=.R4.#0.)Vsp0,)P,(>.(?.VBL,R5.)$1<.R4.)P,(11.$12.(?.VBL,R6.)R4.$1=.)(14.$12.(15.(16.$17.R6.(5.&40.+41=64.)R5.(18.$12.))Vmodel,)VT,)")
(* [comment removed for export] *).
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
    dpose itinerary_rf as (_ & _ & _ & _ & _ & _ & SC & _).
    lazymatch goal with |- realizes _ (mkCfg (mkst ?Rc _ ?Mc _) _) _ =>
    apply (stdio_call_sound vals (blobs_ev BL) srG knG Rc Mc model scRF msg_refused []
             (t_exit (exit_code 2) (m_fs model)) HR HK (eq_trans (f_equal (fun n => stdio_call n srG knG) HL) SC));
      cbn [sc_f sc_fd sc_ret sc_wb sc_wp sc_bufp sc_bufsz sc_s sc_l sc_sp sc_sr sc_kn scRF];
      change (@length byte msg_refused) with 38%nat; cbn [length Z.of_nat Pos.of_succ_nat Pos.succ] end.
    - ed_lin ltac:(cbn [ev ENV]; rewrite ?P0). unorm. lia.
    - ed_lin ltac:(cbn [ev ENV]; rewrite ?P0). unorm. lia.
    - cbn [edenot]. reflexivity.
    - lia.
    - right. ed_lin ltac:(cbn [ev ENV]; rewrite ?P0). unorm. lia.
    - left. ed_lin ltac:(cbn [ev ENV]; rewrite ?P0). unorm. lia.
    - cbn [edenot]. unorm. lia.
    - ed_lin ltac:(cbn [ev ENV]; rewrite ?P0). unorm. lia.   (* [comment removed for export] *)
    - cbn [edenot]. unorm. lia.                                 (* [comment removed for export] *)
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
  #[using="Hvsp SPlo SPhi"] Lemma memcpy1_denot : ltac2:(CDefT.buildp (gd_tbl_P_stdio_refused ()) "Pvals,(1.(2.&40.))PM,P,(2.&40.)(:.(2.&8.))P,(0.(2.&40.)(=.R2.#0.)Vsp0,)(0.P,(2.&40.)(:.(2.&8.))(1>.(?.VBL,R3.)R2.$1?.)(20.R2.(5.&40.(21.(22.&40.Vsp0,)+230.))$6.))")
(* [comment removed for export] *).
  Proof.
    intros vals M P0. pose proof SPlo. pose proof SPhi.
    rewrite <- PRE14_words. cbn [mem_denot logM1]. rewrite !wbytes_app.
    unfold adenot, v_addi, at_. cbn [a_base a_off edenot ev ENV length Z.of_nat Pos.of_succ_nat Pos.succ]. rewrite P0.
    rewrite !length_N_to_le_bytes. cbn [Z.of_nat Pos.of_succ_nat Pos.succ]. unorm.
    repeat (f_equal; try (f_equal; lia)).
  Qed.
  #[using="Hvsp SPlo SPhi"] Lemma memcpy4_denot : ltac2:(CDefT.buildp (gd_tbl_P_stdio_refused ()) "Pvals,(1.(2.&40.))PM,P,(2.&40.)(:.(2.&8.))P,(0.(2.&40.)(=.R2.#0.)Vsp0,)(0.P,(2.&40.)(:.(2.&8.))(1>.(?.VBL,R3.)R2.$23.)(20.R2.(5.&40.(21.(22.&40.Vsp0,)+222.))$7.))")
(* [comment removed for export] *).
  Proof.
    intros vals M P0. pose proof SPlo. pose proof SPhi.
    rewrite <- DIG8_word. cbn [mem_denot logM4].
    unfold adenot, v_addi. cbn [a_base a_off edenot ev ENV]. rewrite P0.
    repeat (f_equal; try (f_equal; lia)).
  Qed.
  #[using="Hvsp SPlo SPhi"] Lemma memcpy5_denot : ltac2:(CDefT.buildp (gd_tbl_P_stdio_refused ()) "Pvals,(1.(2.&40.))PM,P,(2.&40.)(:.(2.&8.))P,(0.(2.&40.)(=.R2.#0.)Vsp0,)(0.P,(2.&40.)(:.(2.&8.))(1>.(?.VBL,R3.)R2.$24.)(20.R2.(5.&40.(21.(22.&40.Vsp0,)+21:.))$8.))")
(* [comment removed for export] *).
  Proof.
    intros vals M P0. pose proof SPlo. pose proof SPhi.
    rewrite <- SUF16_words. cbn [mem_denot logM5]. rewrite !wbytes_app.
    unfold adenot, v_addi, at_. cbn [a_base a_off edenot ev ENV length Z.of_nat Pos.of_succ_nat Pos.succ]. rewrite P0.
    rewrite !length_N_to_le_bytes. cbn [Z.of_nat Pos.of_succ_nat Pos.succ]. unorm.
    repeat (f_equal; try (f_equal; lia)).
  Qed.

  (* [comment removed for export] *)
  Ltac after_memcpy HL Hms Hkeep :=
    replace (Z_to_bv 64 289344) with (0x46a40 : word) by (apply bv_eq; reflexivity);
    eapply rz_msteps; [exact Hh | exact Hlazy | exact Hms |]; clear Hms;
    replace (0x41d64 : word) with (Z_to_bv 64 0x41d64) by (apply bv_eq; reflexivity);
    lazymatch goal with H : regs_ok ?E ?sr ?Rc |- realizes _ (mkCfg (mkst ?R2 _ _ _) _) _ =>
      pose proof (regs_after_keeps _ (blobs_ev BL) sr Rc R2 callee_kept
                    ltac:(rewrite HL; vm_compute; reflexivity) H Hkeep callee_kept_no0) as HR2;
      rewrite HL in HR2; clear H Hkeep; rename HR2 into HR
    end.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  #[using="Hvsp Hh Hlazy Hfd2 SPlo SPhi"] Lemma rf_segF : ltac2:(CDefT.buildp (gd_tbl_P_stdio_refused ()) "Pvals,(1.(2.&40.))PR,(9.&5.(2.&40.))PM,P,(2.&40.)(:.(2.&8.))P,(0.$;.(<.(2.&40.)R3.)#:7.)P,(0.(2.&40.)(=.R4.#0.)Vsp0,)P,(>.(?.VBL,R5.)$25.R4.)P,(11.$12.(?.VBL,R6.)R4.$26.)(14.$12.(15.(16.$17.R6.(5.&40.+41=64.)R5.(18.$12.))Vmodel,)VT,)")
(* [comment removed for export] *).
  Proof.
    intros vals R M HL P0 HR HK.
    pose proof SPlo as Hlo. pose proof SPhi as Hhi.
    run_blk scr0 167%nat.
    set (dst := Z_to_bv 64 (bv_unsigned sp0 - 538)).
    assert (Hsrc : rdn RSEGS M (Z_to_bv 64 0x106c7) 16 = Some SUF16).
    { rewrite (kimg_rdn RSEGS (ENV BL vals) _ knF ltac:(let i := kidx knF (is_kimg_cov 0x106c7 16) in exact i)
                 _ _ 0x106c7 16 HK eq_refl) by (cbn; lia). apply suf16_img. }
    assert (Hdst : store_ok RSEGS M dst 16 = true).
    { pose proof (kwr_store_ok RSEGS (ENV BL vals) _ knF ltac:(let i := kidx knF (is_kwr_cov (EVar 0) (-538) 16) in exact i)
                    _ _ _ (-538) 16 HK eq_refl ltac:(lia) ltac:(cbn; lia)) as Hst.
      unfold adenot, v_addi in Hst. cbn [a_base a_off edenot ev ENV] in Hst. rewrite P0 in Hst.
      subst dst. replace (bv_unsigned sp0 - 538)%Z with (bv_unsigned sp0 + -538)%Z by lia. exact Hst. }
    assert (MC : mcH M dst (Z_to_bv 64 0x106c7) 16 SUF16).
    { constructor; subst dst; rewrite ?u_small by lia; try (cbn; lia).
      - exact Hsrc.
      - exact Hdst. }
    lazymatch goal with |- realizes _ (mkCfg (mkst ?Rc _ _ _) _) _ =>
      assert (A1 : getr Rc 1 = (0x41d64 : word)) by (regv HR (1 : reg); apply bv_eq; reflexivity);
      assert (A10 : getr Rc 10 = dst)
        by (regv HR (10 : reg); subst dst; ed_lin ltac:(cbn [ev ENV]; rewrite ?P0); f_equal; lia);
      assert (A11 : getr Rc 11 = Z_to_bv 64 0x106c7) by (regv HR (11 : reg); reflexivity);
      assert (A12 : getr Rc 12 = Z_to_bv 64 16) by (regv HR (12 : reg); reflexivity);
      destruct (ref_memcpy M dst (Z_to_bv 64 0x106c7) 16 _ (seg_rom RSEGS) MC Rc (0x41d64 : word)
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
  #[using="Hvsp Hh Hlazy Hfd2 SPlo SPhi"] Lemma rf_segE : ltac2:(CDefT.buildp (gd_tbl_P_stdio_refused ()) "Pvals,(1.(2.&40.))PR,(9.&5.(2.&40.))PM,P,(2.&40.)(:.(2.&8.))P,(0.$;.(<.(2.&40.)R3.)#87.)P,(0.(2.&40.)(=.R4.#0.)Vsp0,)P,(>.(?.VBL,R5.)$27.R4.)P,(11.$12.(?.VBL,R6.)R4.$28.)(14.$12.(15.(16.$17.R6.(5.&40.+41=64.)R5.(18.$12.))Vmodel,)VT,)")
(* [comment removed for export] *).
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
      assert (A1 : getr Rc 1 = (0x41d64 : word)) by (regv HR (1 : reg); apply bv_eq; reflexivity);
      assert (A10 : getr Rc 10 = dst)
        by (regv HR (10 : reg); subst dst; ed_lin ltac:(cbn [ev ENV]; rewrite ?P0); f_equal; lia);
      assert (A11 : getr Rc 11 = src)
        by (regv HR (11 : reg); subst src; ed_lin ltac:(cbn [ev ENV]; rewrite ?P0); f_equal; lia);
      assert (A12 : getr Rc 12 = Z_to_bv 64 8) by (regv HR (12 : reg); reflexivity);
      destruct (ref_memcpy M dst src 8 _ (seg_rom RSEGS) MC Rc (0x41d64 : word)
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
      assert (A1 : getr Rc 1 = (0x41d64 : word)) by (regv HR (1 : reg); apply bv_eq; reflexivity);
      assert (A10 : getr Rc 10 = dst)
        by (regv HR (10 : reg); subst dst; ed_lin ltac:(cbn [ev ENV]; rewrite ?P0); f_equal; lia);
      assert (A11 : getr Rc 11 = Z_to_bv 64 srcZ) by (regv HR (11 : reg); reflexivity);
      assert (A12 : getr Rc 12 = Z_to_bv 64 0) by (regv HR (12 : reg); reflexivity);
      destruct (ref_memcpy Mc dst (Z_to_bv 64 srcZ) 0 _ (seg_rom RSEGS) MC Rc (0x41d64 : word)
                  ltac:(apply ret_ok_even; reflexivity) A1 A10 A11 A12) as (R2 & Hms & Hkeep);
      clear A1 A10 A11 A12 MC;
      after_memcpy HL Hms Hkeep;
      change (wbytes Mc dst []) with Mc
    end.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  #[using="Hvsp Hh Hlazy Hfd2 SPlo SPhi"] Lemma rf_segD : ltac2:(CDefT.buildp (gd_tbl_P_stdio_refused ()) "Pvals,(1.(2.&40.))PR,(9.&5.(2.&40.))PM,P,(2.&40.)(:.(2.&8.))P,(0.$;.(<.(2.&40.)R3.)#67.)P,(0.(2.&40.)(=.R4.#0.)Vsp0,)P,(>.(?.VBL,R5.)$29.R4.)P,(11.$12.(?.VBL,R6.)R4.$2:.)(14.$12.(15.(16.$17.R6.(5.&40.+41=64.)R5.(18.$12.))Vmodel,)VT,)")
(* [comment removed for export] *).
  Proof.
    intros vals R M HL P0 HR HK.
    pose proof SPlo as Hlo. pose proof SPhi as Hhi.
    run_blk scr0 103%nat.
    memcpy0_step HL P0 0x102a5%Z.
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
  #[using="Hvsp Hh Hlazy Hfd2 SPlo SPhi"] Lemma rf_segC : ltac2:(CDefT.buildp (gd_tbl_P_stdio_refused ()) "Pvals,(1.(2.&40.))PR,(9.&5.(2.&40.))PM,P,(2.&40.)(:.(2.&8.))P,(0.$;.(<.(2.&40.)R3.)#47.)P,(0.(2.&40.)(=.R4.#0.)Vsp0,)P,(>.(?.VBL,R5.)$2;.R4.)P,(11.$12.(?.VBL,R6.)R4.$2<.)(14.$12.(15.(16.$17.R6.(5.&40.+41=64.)R5.(18.$12.))Vmodel,)VT,)")
(* [comment removed for export] *).
  Proof.
    intros vals R M HL P0 HR HK.
    pose proof SPlo as Hlo. pose proof SPhi as Hhi.
    run_blk scr0 71%nat.
    memcpy0_step HL P0 0x106c5%Z.
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
  #[using="Hvsp Hh Hlazy Hfd2 SPlo SPhi"] Lemma rf_segB : ltac2:(CDefT.buildp (gd_tbl_P_stdio_refused ()) "Pvals,(1.(2.&40.))PR,(9.&5.(2.&40.))PM,P,(2.&40.)(:.(2.&8.))P,(0.$;.(<.(2.&40.)R3.)#27.)P,(0.(2.&40.)(=.R4.#0.)Vsp0,)P,(>.(?.VBL,R5.)$2=.R4.)P,(11.$12.(?.VBL,R6.)R4.$2>.)(14.$12.(15.(16.$17.R6.(5.&40.+1=494.)R5.(18.$12.))Vmodel,)VT,)")
(* [comment removed for export] *).
  Proof.
    intros vals R M HL P0 HR HK.
    pose proof SPlo as Hlo. pose proof SPhi as Hhi.
    run_blk scr0 39%nat.
    set (dst := Z_to_bv 64 (bv_unsigned sp0 - 560)).
    assert (Hsrc : rdn RSEGS M (Z_to_bv 64 0x106b7) 14 = Some PRE14).
    { rewrite (kimg_rdn RSEGS (ENV BL vals) _ knB ltac:(let i := kidx knB (is_kimg_cov 0x106b7 14) in exact i)
                 _ _ 0x106b7 14 HK eq_refl) by (cbn; lia). apply pre14_img. }
    assert (Hdst : store_ok RSEGS M dst 14 = true).
    { pose proof (kwr_store_ok RSEGS (ENV BL vals) _ knB ltac:(let i := kidx knB (is_kwr_cov (EVar 0) (-560) 14) in exact i)
                    _ _ _ (-560) 14 HK eq_refl ltac:(lia) ltac:(cbn; lia)) as Hst.
      unfold adenot, v_addi in Hst. cbn [a_base a_off edenot ev ENV] in Hst. rewrite P0 in Hst.
      subst dst. replace (bv_unsigned sp0 - 560)%Z with (bv_unsigned sp0 + -560)%Z by lia. exact Hst. }
    assert (MC : mcH M dst (Z_to_bv 64 0x106b7) 14 PRE14).
    { constructor; subst dst; rewrite ?u_small by lia; try (cbn; lia).
      - exact Hsrc.
      - exact Hdst. }
    lazymatch goal with |- realizes _ (mkCfg (mkst ?Rc _ _ _) _) _ =>
      assert (A1 : getr Rc 1 = (0x41d64 : word)) by (regv HR (1 : reg); apply bv_eq; reflexivity);
      assert (A10 : getr Rc 10 = dst)
        by (regv HR (10 : reg); subst dst; ed_lin ltac:(cbn [ev ENV]; rewrite ?P0); f_equal; lia);
      assert (A11 : getr Rc 11 = Z_to_bv 64 0x106b7) by (regv HR (11 : reg); reflexivity);
      assert (A12 : getr Rc 12 = Z_to_bv 64 14) by (regv HR (12 : reg); reflexivity);
      destruct (ref_memcpy M dst (Z_to_bv 64 0x106b7) 14 _ (seg_rom RSEGS) MC Rc (0x41d64 : word)
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

  Variables (tid : Z) (R : bvmap 5 word) (M : word -> option byte) (canw : word).   (* [comment removed for export] *)
  Hypothesis Rsp : getr R 2 = Z_to_bv 64 (bv_unsigned sp0 - 128).
  Hypothesis Rgp : getr R 3 = Z_to_bv 64 0x10800.
  Hypothesis Rtp : getr R 4 = Z_to_bv 64 0x5d0c8.
  Hypothesis Mstack : stack_writable M sp0.
  Hypothesis Mimg : Forall (fun iv => img_clear M (fst iv) (snd iv)) re_ivs.
  Hypothesis Mgot : cell M 0x4bcd8 8 0x7d330.
  Hypothesis Mcomp : rdn RSEGS M (Z_to_bv 64 0x4cf68) 1 = Some [Z_to_bv 8 0].
  Hypothesis Mtid : cell M 0x5d020 4 tid.
  Hypothesis Htid : (0 < tid < 2 ^ 22)%Z.
  Hypothesis Mlock : cell M 0x7d328 4 0.
  Hypothesis Mcanary : rdn RSEGS M (Z_to_bv 64 0x7d330) 8 = Some (word_to_le_bytes 8 canw).   (* [comment removed for export] *)
  Hypothesis Mneedlocks : rdn RSEGS M (Z_to_bv 64 0x7d353) 1 = Some [Z_to_bv 8 0].
  Hypothesis Mstdin : cell M 0x7d770 8 0.
  Hypothesis Mofl : cell M 0x7d780 8 0.

  Let E : env := ENV BL (valsRE sp0 sp0 tid R canw).

  #[using="Type"] Lemma evRF_junk : forall i, (i < 32)%nat -> ev E (6 + i) = getr R (Z_to_bv 5 (Z.of_nat i)).
  Proof. intros i Hi. apply (evRE_junk sp0 BL sp0 tid R canw i Hi). Qed.

  Ltac reg_caseRF :=
    cbn [nth srRF0 all_regs];
    first [ lazymatch goal with |- _ = edenot _ (EVar ?n) =>
              change (edenot E (EVar n)) with (ev E n);
              first [ rewrite (evRF_junk (n - 6)) by lia; reflexivity | idtac ]
            | |- _ => cbn [edenot] end ];
    first [ reflexivity
          | exact Rgp | exact Rtp
          | rewrite Rsp, alu_add; change (ev E 0) with sp0; unfold v_add; apply bv_eq;
            rewrite !Z_to_bv_unsigned, !bv_wrap64_mod, Zplus_mod_idemp_r; f_equal; lia
          | idtac ].

  #[using="Hvsp SPlo SPhi Rsp Rgp Rtp"] Lemma regs_okRF : regs_ok E srRF0 R.
  Proof.
    pose proof SPlo. pose proof SPhi.
    apply regs_ok_by_index.
    intros i Hi.
    destruct i as [|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|i]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]; [ .. | lia]; reg_caseRF.
  Qed.

  #[using="sp0 BL Hvsp Hh Hlazy Hfd2 SPlo SPhi T tid canw Rsp Rgp Rtp Mstack Mimg Mgot Mcomp Mtid Htid Mlock Mcanary Mneedlocks Mstdin Mofl E"] Theorem ref_refused_tail : ltac2:(CDefT.buildp (gd_tbl_P_stdio_refused ()) "(14.$12.(15.(16.$17.VR,(5.&40.+1=494.)VM,(18.$12.))Vmodel,)(2?.$30.(1;.Vmodel,)))")
(* [comment removed for export] *).
  Proof.
    pose proof SPlo. pose proof SPhi.
    unfold t_die.
    eapply (rf_segB (valsRE sp0 sp0 tid R canw) R M (valsRE_len sp0 sp0 tid R canw) eq_refl regs_okRF).
    apply (know_okRE sp0 BL Hvsp sp0 tid R M canw Mstack Mimg Mgot Mcomp Mtid Htid Mlock Mcanary Mneedlocks Mstdin Mofl); lia.
  Qed.
End Refused.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
