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
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BB Require Import Amb CatExec CatSim SeqExec StoreOk ShapeX Hoare BBFrame ShapeLaws SpecConsts MmapSim AllocSim FileSim AgentLib SymExec SymExec2 SymExec2Sound SymRun SymDrive SymDriveX SymDriveH4 LibKnowFrame MemcpyLib LibTail.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Sys Require Import Nodes LibWritev.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Spec Require Import Spec.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U Require Import U_exit_base U_stdio_defs U_exit U_stdio_call U_memcpy_base U_memcpy U_memchr U_strnlen U_startup U_main_entry.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U Require Import U_mainleaf_openfail_defs U_mainleaf_openfail_tail.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import DietDestruct.   (* [comment removed for export] *)
Import ListNotations.
Open Scope bv_scope.
Import SX2. Import SX2S.
#[local] Existing Instance PropExec.fx0.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
Ltac close_exit HR HK P0 Hh Hlazy sp0 :=
  lazymatch type of HK with know_ok ?segs ?E ?M ?kn =>
  lazymatch goal with |- realizes _ (mkCfg _ ?model) _ =>
    apply (rz_conseq segs _ (t_emit (W 1 []) (t_exit (bv_and (Z_to_bv 64 2) (Z_to_bv 64 255)) (m_fs model))));
    [ | cbn [W map];
        replace (bv_and (Z_to_bv 64 2) (Z_to_bv 64 255)) with (exit_code 2) by (apply bv_eq; reflexivity);
        apply t_eq_sym; apply t_emit_nil_exit ];
    apply ref_exit_Z;
    let Ktid := fresh "Ktid" in
    pose proof (know_nth segs _ _ kn ltac:(let i := kidx kn (is_krange (EVar 5)) in exact i) _ HK eq_refl)
      as Ktid; cbn [kentry_ok edenot ev ENV] in Ktid;
    lazymatch type of HR with regs_ok _ _ ?Rc =>
    exists (Z_to_bv 64 (bv_unsigned sp0 - 128)), (Z_to_bv 64 0x5d0c8), (bv_unsigned (ev E 5)),
           (Z_to_bv 64 0), (Z_to_bv 64 0);
    split; [|split; [exact Hh|split; [exact Hlazy|]]];
    [ constructor;
      [ regv HR (2 : reg); rewrite edenot_add_lit; unfold adenot, v_addi; cbn [a_base a_off edenot ev ENV];
        rewrite P0; f_equal; lia
      | regv HR (4 : reg); reflexivity
      | regv HR (10 : reg); reflexivity
      | rewrite u_small by lia; lia
      | rewrite u_small by lia; lia
      | rewrite u_small by lia;
        let Hst := fresh "Hst" in
        pose proof (kwr_store_ok segs E _ kn ltac:(let i := kidx kn (is_kwr_cov (EVar 0) (-272) 144) in exact i)
                      _ _ _ (-272) 144 HK eq_refl ltac:(lia) ltac:(cbn; lia)) as Hst;
        unfold adenot, v_addi in Hst; cbn [a_base a_off edenot ev ENV] in Hst; rewrite P0 in Hst;
        replace (bv_unsigned sp0 - 128 - 144)%Z with (bv_unsigned sp0 + -272)%Z by lia; exact Hst
      | lit_u; cbn [ev ENV] in Ktid |- *; lia
      | lit_u; cbn [ev ENV] in Ktid |- *; lia
      | cbn [ev ENV] in Ktid |- *; lia
      | lit_u; change (381128 - 168)%Z with 0x5d020%Z;
        let Htc := fresh "Htc" in
        krd HK 0x5d020%Z 4%nat Htc; rewrite Htc; cbn [ev ENV] in Ktid |- *;
        rewrite ext_val_zx_id by (change (2 ^ (8 * Z.of_nat 4))%Z with 4294967296%Z; lia);
        rewrite Z_to_bv_bv_unsigned; reflexivity
      | krd_solve HK | krd_solve HK | krd_solve HK | krd_solve HK | krd_solve HK | krd_solve HK | krd_solve HK
      | repeat split; krd_solve HK
      | repeat split; krd_solve HK
      | krd_solve HK                                                       (* [comment removed for export] *)
      | exists false; unfold atexit_st, atexit_none; split; krd_solve HK ]  (* [comment removed for export] *)
    | left; split; [reflexivity|]; exists (Z_to_bv 64 0), (Z_to_bv 64 0); repeat split; krd_solve HK ]
  end end end.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Ltac2 gd_tbl_P_mainleaf_openfail_tail2 () : Init.string Init.list := ["Corelib.Init.Datatypes.list"; "stdpp.bitvector.definitions.bv"; "LinuxProcessSemantics.Riscv.Prelude.bvmap"; "Corelib.Init.Datatypes.option"; "Corelib.Init.Logic.eq"; "Corelib.Init.Datatypes.nat"; "Corelib.Init.Datatypes.length"; "RocqVerifyHarness.AgentSubmission.BB.SymRun.vals_ev"; "RocqVerifyHarness.AgentSubmission.BB.SymExec2Sound.SX2S.regs_ok"; "RocqVerifyHarness.AgentSubmission.U.U_mainleaf_openfail_tail.ENV"; "RocqVerifyHarness.AgentSubmission.U.U_mainleaf_openfail_defs.srI30"; "RocqVerifyHarness.AgentSubmission.BB.SymExec2Sound.SX2S.know_ok"; "RocqVerifyHarness.ProcessOversight.Tgt_fuzz_pkcs7_ubsan.M.loaded_segments"; "RocqVerifyHarness.AgentSubmission.U.U_mainleaf_openfail_defs.knI30"; "RocqVerifyHarness.AgentSubmission.Lib.Shape.realizes"; "LinuxProcessSemantics.LinuxProcessSem.Run.mkCfg"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.mkst"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.fx0"; "stdpp.bitvector.definitions.Z_to_bv"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.seg_rom"; "RocqVerifyHarness.AgentSubmission.Lib.Shape.t_exit"; "RocqVerifyHarness.AgentSubmission.Spec.Spec.exit_code"; "LinuxProcessSemantics.LinuxProcessSem.State.m_fs"; "RocqVerifyHarness.AgentSubmission.U.U_mainleaf_openfail_defs.srH30"; "RocqVerifyHarness.AgentSubmission.U.U_mainleaf_openfail_defs.knH30"; "Corelib.Numbers.BinNums.Z"; "Stdlib.ZArith.BinInt.Z.of_nat"; "RocqVerifyHarness.AgentSubmission.U.U_mainleaf_openfail_tail.atG0"; "RocqVerifyHarness.AgentSubmission.Lib.Shape.t_emit"; "RocqVerifyHarness.AgentSubmission.Spec.Spec.W"; "RocqVerifyHarness.AgentSubmission.Spec.Spec.msg_cannot_open"; "RocqVerifyHarness.AgentSubmission.U.U_mainleaf_openfail_defs.srI40"; "RocqVerifyHarness.AgentSubmission.U.U_mainleaf_openfail_defs.knI40"; "RocqVerifyHarness.AgentSubmission.U.U_mainleaf_openfail_defs.srH40"; "RocqVerifyHarness.AgentSubmission.U.U_mainleaf_openfail_defs.knH40"; "Corelib.Init.Datatypes.cons"; "Corelib.Init.Datatypes.nil"; "Corelib.Init.Logic.and"; "Stdlib.ZArith.BinInt.Z.le"; "stdpp.bitvector.definitions.bv_unsigned"; "Stdlib.ZArith.BinInt.Z.add"; "RocqVerifyHarness.AgentSubmission.U.U_mainleaf_openfail_defs.srF0"; "RocqVerifyHarness.AgentSubmission.U.U_mainleaf_openfail_defs.knE"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.rdn"; "Corelib.Init.Nat.add"; "Corelib.Init.Datatypes.Some"; "Corelib.Init.Datatypes.app"; "Corelib.Init.Logic.not"; "Stdlib.Lists.List.In"; "Stdlib.ZArith.BinInt.Z.sub"; "Stdlib.ZArith.BinInt.Z.pow"; "RocqVerifyHarness.AgentSubmission.BB.SymExec2.SX2.sr_upd"; "RocqVerifyHarness.AgentSubmission.U.U_mainleaf_openfail_defs.srA"; "RocqVerifyHarness.AgentSubmission.BB.SymExec2.SX2.ridx"; "stdpp.bitvector.definitions.BV"; "Corelib.Init.Logic.I"; "RocqVerifyHarness.AgentSubmission.BB.SymExec2.SX2.EVar"; "RocqVerifyHarness.AgentSubmission.U.U_mainleaf_openfail_defs.knA"; "RocqVerifyHarness.AgentSubmission.Spec.Spec.t_die"].


Section Tail2.
  Variable sp0 : word.
  Variable BL : list (list byte).
  Variable model : Model.
  Hypothesis Hvsp : valid_sp sp0.
  Hypothesis Hh : m_halted model = None.
  Hypothesis Hlazy : m_vm_lazy model = [].
  Hypothesis Hfd2 : fd_lookup (m_fds model) (Z_to_bv 64 2) = Some (FdChannel (Z_to_bv 64 2)).

  Let SPlo : (0x7fff80000000 <= bv_unsigned sp0)%Z := proj1 Hvsp.
  Let SPhi : (bv_unsigned sp0 <= 0x800000000000)%Z := proj1 (proj2 Hvsp).

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  #[using="Hvsp Hh Hlazy SPlo SPhi"] Lemma of_segI3 : ltac2:(CDefT.buildp (gd_tbl_P_mainleaf_openfail_tail2 ()) "Pvals,(0.(1.&40.))PR,(2.&5.(1.&40.))PM,P,(1.&40.)(3.(1.&8.))P,(4.$5.(6.(1.&40.)R3.)#107.)P,(4.(1.&40.)(7.R4.#0.)Vsp0,)P,(8.(9.VBL,R5.)$:.R4.)P,(;.$<.(9.VBL,R6.)R4.$=.)(>.$<.(?.(10.$11.R6.(12.&40.+420:8.)R5.(13.$<.))Vmodel,)(14.(15.+2.)(16.Vmodel,)))")
(* [comment removed for export] *).
  Proof.
    intros vals R M HL P0 HR HK.
    pose proof SPlo as Hlo. pose proof SPhi as Hhi.
    run_blk scr0 263%nat.
    close_exit HR HK P0 Hh Hlazy sp0.
  Qed.

  #[using="Hvsp Hh Hlazy Hfd2 SPlo SPhi"] Lemma of_segH3 : ltac2:(CDefT.buildp (gd_tbl_P_mainleaf_openfail_tail2 ()) "Pvals,(0.(1.&40.))PR,(2.&5.(1.&40.))PM,P,(1.&40.)(3.(1.&8.))P,(4.$5.(6.(1.&40.)R3.)#>7.)P,(4.(1.&40.)(7.R4.#0.)Vsp0,)P,(8.(9.VBL,R5.)$17.R4.)P,(;.$<.(9.VBL,R6.)R4.$18.)(>.$<.(?.(10.$11.R6.(12.&40.+42278.)R5.(13.$<.))Vmodel,)(14.(15.+2.)(16.Vmodel,)))")
(* [comment removed for export] *).
  Proof.
    intros vals R M HL P0 HR HK.
    pose proof SPlo as Hlo. pose proof SPhi as Hhi.
    (* [comment removed for export] *)
    run_blk scr0 231%nat.
    apply (rz_conseq RSEGS _ (t_emit (map (WriteEv (Z_to_bv 64 2)) ([] ++ [])) (t_exit (exit_code 2) (m_fs model)))).
    2:{ cbn [map app]. apply t_eq_sym. apply t_emit_nil_exit. }
    dpose itinerary_63_64 as (_ & _ & _ & _ & _ & SC & _).
    lazymatch goal with |- realizes _ (mkCfg (mkst ?Rc _ ?Mc _) _) _ =>
    apply (stdio_call_sound vals (blobs_ev BL) srH3 knH3 Rc Mc model scH3 [] []
             (t_exit (exit_code 2) (m_fs model)) HR HK (eq_trans (f_equal (fun n => stdio_call n srH3 knH3) HL) SC));
      cbn [sc_f sc_fd sc_ret sc_wb sc_wp sc_bufp sc_bufsz sc_s sc_l sc_sp sc_sr sc_kn scH3 length Z.of_nat] end.
    - lia.
    - lia.
    - cbn [edenot]. apply u_small. lia.
    - lia.
    - right. ed_lin ltac:(cbn [ev ENV]; rewrite ?P0). unorm. lia.
    - left. cbn [edenot]. ed_lin ltac:(cbn [ev ENV]; rewrite ?P0). unorm. lia.
    - cbn [edenot]. unorm. lia.
    - first [lia | cbn [edenot]; unorm; lia | ed_lin ltac:(cbn [ev ENV]; rewrite ?P0); unorm; lia].   (* [comment removed for export] *)
    - cbn [edenot]. unorm. lia.   (* [comment removed for export] *)
    - reflexivity.
    - reflexivity.
    - exact Hfd2.
    - exact Hh.
    - exact Hlazy.
    - apply t_exit_has_nil.
    - clear HR HK. intros R2 M2 HR HK.
      eapply (of_segI3 (vals ++ junk_vals R2));
        [ rewrite length_app, junk_vals_length, HL; reflexivity
        | rewrite vals_ev_app_l by (rewrite HL; lia); exact P0
        | exact HR | exact HK ].
  Qed.

  (* [comment removed for export] *)
  #[using="Hvsp Hh Hlazy Hfd2 SPlo SPhi"] Lemma of_segG3 : ltac2:(CDefT.buildp (gd_tbl_P_mainleaf_openfail_tail2 ()) "Ppath,(0.(1.&8.))P,(4.$19.(1:.(6.(1.&8.)R1.))+3?.)(1;.Vsp0,VBL,Vmodel,R2.+3?.(1<.(1=.+2.(1>.R2.))(14.(15.+2.)(16.Vmodel,))))")
(* [comment removed for export] *).
  Proof.
    intros path HP vals R M HL P0 P113 HR HK SBp.
    pose proof SPlo as Hlo. pose proof SPhi as Hhi.
    (* [comment removed for export] *)
    run_blk_keep scrG3 199%nat.
    { (* [comment removed for export] *)
      unfold sc_denot. cbn [branch_taken]. ed_lin ltac:(cbn [ev ENV]; rewrite ?P0, ?P113).
      replace (-1 * 63 + 63)%Z with 0%Z by lia.
      rewrite ltu_ZZ by lia. reflexivity. }
    assert (WOK : win_ok (ENV BL vals) 0 BUF_LO BUF_HI IHI).
    { unfold win_ok, BUF_LO, BUF_HI, IHI. cbn [ev ENV]. rewrite P0. lia. }
    assert (SBp' : rdn RSEGS M0 (Z_to_bv 64 (bv_unsigned sp0 - 543)) (length path) = Some path).
    { rewrite EQM, (rdn_mem_denot_out RSEGS (ENV BL vals) M _ 0 BUF_LO BUF_HI IHI);
        [exact SBp | vm_compute; reflexivity | exact WOK | cbn [ev ENV]; rewrite P0; unfold BUF_LO; rewrite u_small by lia; lia
        | cbn [ev ENV]; rewrite P0; unfold BUF_HI; rewrite u_small by lia; lia]. }
    clear EQM SBp. rename M0 into M'.
    krdv HK 0%nat (-560)%Z 8%nat Hw0. { apply flat_intro; cbn [edenot ev ENV]; rewrite ?P0; lia. }
    krdv HK 0%nat (-552)%Z 8%nat Hw1. { apply flat_intro; cbn [edenot ev ENV]; rewrite ?P0; lia. }
    krdv HK 0%nat (-544)%Z 1%nat Hw2. { apply flat_intro; cbn [edenot ev ENV]; rewrite ?P0; lia. }
    unfold adenot, v_addi in Hw0, Hw1, Hw2. cbn [a_base a_off edenot ev ENV] in Hw0, Hw1, Hw2.
    rewrite P0 in Hw0, Hw1, Hw2.
    assert (H17 : rdn RSEGS M' (Z_to_bv 64 (bv_unsigned sp0 + -560)) 17 = Some PRE17).
    { rewrite <- PRE17_words. change 17%nat with (8 + (8 + 1))%nat.
      apply rdn_app_Z; [exact Hw0 | | lia | lia].
      apply rdn_app_Z; [ | | lia | lia].
      + replace (bv_unsigned sp0 + -560 + Z.of_nat 8)%Z with (bv_unsigned sp0 + -552)%Z by lia. exact Hw1.
      + replace (bv_unsigned sp0 + -560 + Z.of_nat 8 + Z.of_nat 8)%Z with (bv_unsigned sp0 + -544)%Z by lia. exact Hw2. }
    assert (B80 : rdn RSEGS M' (Z_to_bv 64 (bv_unsigned sp0 + -560)) (17 + length path) = Some (PRE17 ++ path)).
    { apply rdn_app_Z; [exact H17 | | lia | lia].
      replace (bv_unsigned sp0 + -560 + Z.of_nat 17)%Z with (bv_unsigned sp0 - 543)%Z by lia. exact SBp'. }
    assert (Hnl : rdn RSEGS M' (Z_to_bv 64 0x1084c) 1 = Some [Z_to_bv 8 10]).
    { rewrite (kimg_rdn RSEGS (ENV BL vals) _ knG3 ltac:(let i := kidx knG3 (is_kimg_cov 0x1084c 1) in exact i)
                 _ _ 0x1084c 1 HK eq_refl) by (cbn; lia). apply nl_img. }
    (* [comment removed for export] *)
    unfold msg_cannot_open. change (s2b _) with PRE17. rewrite app_assoc. unfold W.
    dpose itinerary_63_64 as (_ & SC & _).
    lazymatch goal with |- realizes _ (mkCfg (mkst ?Rc _ ?Mc _) _) _ =>
    apply (stdio_call_sound vals (blobs_ev BL) srG3 knG3 Rc Mc model scG3 (PRE17 ++ path) [Z_to_bv 8 10]
             (t_exit (exit_code 2) (m_fs model)) HR HK (eq_trans (f_equal (fun n => stdio_call n srG3 knG3) HL) SC));
      cbn [sc_f sc_fd sc_ret sc_wb sc_wp sc_bufp sc_bufsz sc_s sc_l sc_sp sc_sr sc_kn scG3];
      rewrite ?length_app, ?PRE17_len end.
    - ed_lin ltac:(cbn [ev ENV]; rewrite ?P0, ?P113). unorm. lia.
    - ed_lin ltac:(cbn [ev ENV]; rewrite ?P0, ?P113). unorm. lia.
    - cbn [edenot length]. apply u_small. lia.
    - cbn [length Z.of_nat]. lia.
    - right. ed_lin ltac:(cbn [ev ENV]; rewrite ?P0, ?P113). unorm. lia.
    - left. cbn [edenot]. ed_lin ltac:(cbn [ev ENV]; rewrite ?P0). unorm. lia.
    - cbn [edenot]. unorm. lia.
    - ed_lin ltac:(cbn [ev ENV]; rewrite ?P0, ?P113). unorm. lia.   (* [comment removed for export] *)
    - cbn [edenot]. unorm. lia.   (* [comment removed for export] *)
    - ed_lin ltac:(cbn [ev ENV]; rewrite ?P0, ?P113). unorm.
      replace (17 + length path)%nat with (17 + length path)%nat by lia. exact B80.
    - cbn [edenot]. exact Hnl.
    - exact Hfd2.
    - exact Hh.
    - exact Hlazy.
    - apply t_exit_has_nil.
    - (* [comment removed for export] *)
      clear HR HK. intros R2 M2 HR HK.
      eapply (of_segH3 (vals ++ junk_vals R2));
        [ rewrite length_app, junk_vals_length, HL; reflexivity
        | rewrite vals_ev_app_l by (rewrite HL; lia); exact P0
        | exact HR | exact HK ].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  #[using="Type"] Lemma NL_word : word_to_le_bytes 1 (Z_to_bv 64 10) = [Z_to_bv 8 10].
  Proof. vm_compute. repeat (apply (f_equal2 cons); [apply bv_eq; reflexivity|]). reflexivity. Qed.

  #[using="Hvsp Hh Hlazy SPlo SPhi"] Lemma of_segI4 : ltac2:(CDefT.buildp (gd_tbl_P_mainleaf_openfail_tail2 ()) "Pvals,(0.(1.&40.))PR,(2.&5.(1.&40.))PM,P,(1.&40.)(3.(1.&8.))P,(4.$5.(6.(1.&40.)R3.)#107.)P,(4.(1.&40.)(7.R4.#0.)Vsp0,)P,(8.(9.VBL,R5.)$1?.R4.)P,(;.$<.(9.VBL,R6.)R4.$20.)(>.$<.(?.(10.$11.R6.(12.&40.+420:8.)R5.(13.$<.))Vmodel,)(14.(15.+2.)(16.Vmodel,)))")
(* [comment removed for export] *).
  Proof.
    intros vals R M HL P0 HR HK.
    pose proof SPlo as Hlo. pose proof SPhi as Hhi.
    run_blk scr0 263%nat.
    close_exit HR HK P0 Hh Hlazy sp0.
  Qed.

  #[using="Hvsp Hh Hlazy Hfd2 SPlo SPhi"] Lemma of_segH4 : ltac2:(CDefT.buildp (gd_tbl_P_mainleaf_openfail_tail2 ()) "Pvals,(0.(1.&40.))PR,(2.&5.(1.&40.))PM,P,(1.&40.)(3.(1.&8.))P,(4.$5.(6.(1.&40.)R3.)#>7.)P,(4.(1.&40.)(7.R4.#0.)Vsp0,)P,(8.(9.VBL,R5.)$21.R4.)P,(;.$<.(9.VBL,R6.)R4.$22.)(>.$<.(?.(10.$11.R6.(12.&40.+41=64.)R5.(13.$<.))Vmodel,)(1<.(1=.+2.(23.(1.&8.)(12.&8.+:.)(24.(1.&8.))))(14.(15.+2.)(16.Vmodel,))))")
(* [comment removed for export] *).
  Proof.
    intros vals R M HL P0 HR HK.
    pose proof SPlo as Hlo. pose proof SPhi as Hhi.
    (* [comment removed for export] *)
    run_blk scr0 231%nat.
    krdv HK 0%nat (-560)%Z 1%nat Hb. { apply flat_intro; cbn [edenot ev ENV]; rewrite ?P0; lia. }
    rewrite NL_word in Hb.
    unfold adenot, v_addi in Hb. cbn [a_base a_off edenot ev ENV] in Hb. rewrite P0 in Hb.
    replace (W 2 [Z_to_bv 8 10]) with (map (WriteEv (Z_to_bv 64 2)) ([Z_to_bv 8 10] ++ [])) by reflexivity.
    dpose itinerary_63_64 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & SC & _).
    lazymatch goal with |- realizes _ (mkCfg (mkst ?Rc _ ?Mc _) _) _ =>
    apply (stdio_call_sound vals (blobs_ev BL) srH4 knH4 Rc Mc model scH4 [Z_to_bv 8 10] []
             (t_exit (exit_code 2) (m_fs model)) HR HK (eq_trans (f_equal (fun n => stdio_call n srH4 knH4) HL) SC));
      cbn [sc_f sc_fd sc_ret sc_wb sc_wp sc_bufp sc_bufsz sc_s sc_l sc_sp sc_sr sc_kn scH4 length Z.of_nat] end.
    - ed_lin ltac:(cbn [ev ENV]; rewrite ?P0). unorm. lia.
    - ed_lin ltac:(cbn [ev ENV]; rewrite ?P0). unorm. lia.
    - cbn [edenot]. apply u_small. lia.
    - lia.
    - right. ed_lin ltac:(cbn [ev ENV]; rewrite ?P0). unorm. lia.
    - left. cbn [edenot]. ed_lin ltac:(cbn [ev ENV]; rewrite ?P0). unorm. lia.
    - cbn [edenot]. unorm. lia.
    - ed_lin ltac:(cbn [ev ENV]; rewrite ?P0). unorm. lia.   (* [comment removed for export] *)
    - cbn [edenot]. unorm. lia.   (* [comment removed for export] *)
    - ed_lin ltac:(cbn [ev ENV]; rewrite ?P0). unorm.
      replace (bv_unsigned sp0 + -560)%Z with (bv_unsigned sp0 + -560)%Z by lia. exact Hb.
    - reflexivity.
    - exact Hfd2.
    - exact Hh.
    - exact Hlazy.
    - apply t_exit_has_nil.
    - clear HR HK. intros R2 M2 HR HK.
      eapply (of_segI4 (vals ++ junk_vals R2));
        [ rewrite length_app, junk_vals_length, HL; reflexivity
        | rewrite vals_ev_app_l by (rewrite HL; lia); exact P0
        | exact HR | exact HK ].
  Qed.

  (* [comment removed for export] *)
  #[using="Hvsp Hh Hlazy Hfd2 SPlo SPhi"] Lemma of_segFG4 : ltac2:(CDefT.buildp (gd_tbl_P_mainleaf_openfail_tail2 ()) "Ppath,(0.(1.&8.))Ppp,(1.&40.)PP,$19.Pvals,(0.(1.&40.))PR,(2.&5.(1.&40.))PM,P,(1.&40.)(3.(1.&8.))P,(4.$19.(1:.(6.(1.&8.)R6.))R4.)P,(25.(26.+40.R5.)(26.R5.+1????.))P,(4.$5.(6.(1.&40.)R5.)#:7.)P,(4.(1.&40.)(7.R6.#0.)Vsp0,)P,(4.(1.&40.)(7.R7.#2.)R9.)P,(4.(1.&40.)(7.R8.#71.)(12.&40.R9.))P,(26.(27.&40.Vsp0,)(27.&40.R;.))P,(26.(28.(28.(27.&40.R<.)R;.)+8.)(28.(27.&40.Vsp0,)+400000.))P,(26.(28.(28.(27.&40.R=.)R<.)+1.)+800000000000.)P,(8.(9.VBL,R<.)$29.R;.)P,(;.$<.(9.VBL,R=.)R;.$2:.)P,(4.(3.(0.(1.&8.)))(2;.$<.R<.R10.(2<.(6.(1.&8.)R11.)#1.))(2=.(0.(1.&8.))(2>.(1.&8.)R11.(23.(1.&8.)(12.&8.=)(24.(1.&8.))))))(>.$<.(?.(10.$11.R>.(12.&40.+41=64.)R=.(13.$<.))Vmodel,)(1<.(1=.+2.(1>.R12.))(14.(15.+2.)(16.Vmodel,))))")
(* [comment removed for export] *).
  Proof.
    intros path pp P vals R M HP HPr HL P0 P2 P113 Hpp1 Hpp2 Hpp3 HR HK Hstr.
    pose proof SPlo as Hlo. pose proof SPhi as Hhi. pose proof (u64_range pp) as Hppr.
    assert (Psmall : (bv_unsigned (edenot (ENV BL vals) (EVar 113)) < 2 ^ 31)%Z).
    { cbn [edenot ev ENV]. rewrite P113, u_small by lia. lia. }
    (* [comment removed for export] *)
    run_blk_keep scrF4 167%nat.
    { (* [comment removed for export] *)
      unfold sc_denot. cbn [branch_taken]. ed_lin ltac:(cbn [ev ENV]; rewrite ?P113).
      rewrite ltu_ZZ by lia. rewrite (proj2 (Z.ltb_lt _ _)) by lia. reflexivity. }
    { (* [comment removed for export] *)
      unfold sc_denot. cbn [branch_taken].
      rewrite (edenot_exts4 _ _ Psmall), !(edenot_addw0_r _ _) by (rewrite ?edenot_addw0_r by exact Psmall; exact Psmall).
      unfold bv_lts. rewrite Z.ltb_irrefl. reflexivity. }
    assert (WOKS : win_ok (ENV BL vals) 0 0 4194304 IHI).
    { unfold win_ok, IHI. cbn [ev ENV]. rewrite P0. lia. }
    assert (Hstr' : rdn RSEGS M0 pp (length path + 1) = Some (path ++ [Z_to_bv 8 0])).
    { rewrite EQM, (rdn_mem_denot_out RSEGS (ENV BL vals) M _ 0 0 4194304 IHI);
        [exact Hstr | vm_compute; reflexivity | exact WOKS | cbn [ev ENV]; rewrite P0; lia | cbn [ev ENV]; rewrite P0; lia]. }
    clear EQM Hstr. rename M0 into M'.
    assert (Hsrc : rdn RSEGS M' pp (length path) = Some path).
    { replace path with (firstn (length path) (path ++ [Z_to_bv 8 0])) at 2
        by (rewrite firstn_app, firstn_all, Nat.sub_diag; cbn [firstn]; apply app_nil_r).
      eapply rdn_firstn; [exact Hstr' | lia]. }
    krdv HK 0%nat (-560)%Z 8%nat Hw0. { apply flat_intro; cbn [edenot ev ENV]; rewrite ?P0; lia. }
    krdv HK 0%nat (-552)%Z 8%nat Hw1. { apply flat_intro; cbn [edenot ev ENV]; rewrite ?P0; lia. }
    krdv HK 0%nat (-544)%Z 1%nat Hw2. { apply flat_intro; cbn [edenot ev ENV]; rewrite ?P0; lia. }
    unfold adenot, v_addi in Hw0, Hw1, Hw2. cbn [a_base a_off edenot ev ENV] in Hw0, Hw1, Hw2.
    rewrite P0 in Hw0, Hw1, Hw2.
    assert (H17 : rdn RSEGS M' (Z_to_bv 64 (bv_unsigned sp0 + -560)) 17 = Some PRE17).
    { rewrite <- PRE17_words. change 17%nat with (8 + (8 + 1))%nat.
      apply rdn_app_Z; [exact Hw0 | | lia | lia].
      apply rdn_app_Z; [ | | lia | lia].
      + replace (bv_unsigned sp0 + -560 + Z.of_nat 8)%Z with (bv_unsigned sp0 + -552)%Z by lia. exact Hw1.
      + replace (bv_unsigned sp0 + -560 + Z.of_nat 8 + Z.of_nat 8)%Z with (bv_unsigned sp0 + -544)%Z by lia. exact Hw2. }
    (* [comment removed for export] *)
    apply (rz_conseq RSEGS _ (t_emit (W 2 (PRE17 ++ path)) (t_emit (W 2 [Z_to_bv 8 10]) (t_exit (exit_code 2) (m_fs model))))).
    2:{ unfold msg_cannot_open. change (s2b _) with PRE17. rewrite app_assoc. unfold W. rewrite (map_app _ (PRE17 ++ path)).
        apply t_eq_sym. apply t_emit_app. }
    unfold W at 1.
    dpose itinerary_63_64 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & SC & _).
    lazymatch goal with |- realizes _ (mkCfg (mkst ?Rc _ ?Mc _) _) _ =>
    apply (stdio_call_sound vals (blobs_ev BL) srF4 knF4 Rc Mc model scF4 PRE17 path
             (t_emit (W 2 [Z_to_bv 8 10]) (t_exit (exit_code 2) (m_fs model))) HR HK
             (eq_trans (f_equal (fun n => stdio_call n srF4 knF4) HL) SC));
      cbn [sc_f sc_fd sc_ret sc_wb sc_wp sc_bufp sc_bufsz sc_s sc_l sc_sp sc_sr sc_kn scF4];
      rewrite ?PRE17_len end.
    - ed_lin ltac:(cbn [ev ENV]; rewrite ?P0). unorm. lia.
    - ed_lin ltac:(cbn [ev ENV]; rewrite ?P0). unorm. lia.
    - cbn [edenot ev ENV PX]. rewrite P113. rewrite u_small by lia. lia.
    - cbn [length Z.of_nat]. lia.
    - right. ed_lin ltac:(cbn [ev ENV]; rewrite ?P0). unorm. lia.
    - right. cbn [edenot ev ENV PX]. rewrite P2. ed_lin ltac:(cbn [ev ENV]; rewrite ?P0). unorm. lia.
    - cbn [edenot ev ENV PX]. rewrite P2, P113. rewrite u_small by lia. lia.
    - ed_lin ltac:(cbn [ev ENV]; rewrite ?P0). unorm. lia.                        (* [comment removed for export] *)
    - cbn [edenot ev ENV PX]. rewrite P2, P113. rewrite u_small by lia. lia.      (* [comment removed for export] *)
    - ed_lin ltac:(cbn [ev ENV]; rewrite ?P0). unorm.
      replace (bv_unsigned sp0 + -560)%Z with (bv_unsigned sp0 + -560)%Z by lia. exact H17.
    - cbn [edenot ev ENV PX]. rewrite P2. exact Hsrc.
    - exact Hfd2.
    - exact Hh.
    - exact Hlazy.
    - apply t_emit_has_nil.
    - (* [comment removed for export] *)
      clear HR HK. intros R1 M1 HR HK.
      clear Hstr' Hsrc Hw0 Hw1 Hw2 H17 Psmall.
      lazymatch type of HK with know_ok _ _ _ ?k => change k with knG40 in HK end.
      lazymatch type of HR with regs_ok _ ?sr _ => change sr with srG40 in HR end.
      set (vals0 := vals) in P2, P113.
      set (vals1 := vals ++ junk_vals R1) in *.
      assert (HL1 : length vals1 = 199%nat) by (subst vals1; rewrite length_app, junk_vals_length, HL; reflexivity).
      assert (Q0 : vals_ev vals1 0 = sp0) by (subst vals1; rewrite vals_ev_app_l by (rewrite HL; lia); exact P0).
      clearbody vals1 vals0. clear HL P0 WOKS. clear vals. rename HL1 into HL. rename Q0 into P0.
      change (Env (vals_ev vals1) (blobs_ev BL)) with (ENV BL vals1) in HR, HK.
      run_blk scr0 199%nat.
      lazymatch goal with |- realizes _ (mkCfg (mkst _ _ ?Mc _) _) _ => rename Mc into MG end.
      (* [comment removed for export] *)
      set (dst := Z_to_bv 64 (bv_unsigned sp0 - 560)).
      assert (Hnl : rdn RSEGS MG (Z_to_bv 64 0x1084c) 1 = Some [Z_to_bv 8 10]).
      { rewrite (kimg_rdn RSEGS (ENV BL vals1) _ knG4 ltac:(let i := kidx knG4 (is_kimg_cov 0x1084c 1) in exact i)
                   _ _ 0x1084c 1 HK eq_refl) by (cbn; lia). apply nl_img. }
      assert (Hdst : store_ok RSEGS MG dst 1 = true).
      { pose proof (kwr_store_ok RSEGS (ENV BL vals1) _ knG4 ltac:(let i := kidx knG4 (is_kwr_cov (EVar 0) (-560) 1) in exact i)
                      _ _ _ (-560) 1 HK eq_refl ltac:(lia) ltac:(cbn; lia)) as Hst.
        unfold adenot, v_addi in Hst. cbn [a_base a_off edenot ev ENV] in Hst. rewrite P0 in Hst.
        subst dst. replace (bv_unsigned sp0 - 560)%Z with (bv_unsigned sp0 + -560)%Z by lia. exact Hst. }
      assert (MC : mcH MG dst (Z_to_bv 64 0x1084c) 1 [Z_to_bv 8 10]).
      { constructor; cbn [length Z.to_nat Z.of_nat Pos.to_nat]; subst dst; rewrite ?u_small by lia; try lia.
        - exact Hnl.
        - exact Hdst. }
      lazymatch goal with |- realizes _ (mkCfg (mkst ?Rc _ _ _) _) _ =>
        assert (A1 : getr Rc 1 = (0x41d64 : word)) by (regv HR (1 : reg); apply bv_eq; reflexivity);
        assert (A10 : getr Rc 10 = dst)
          by (regv HR (10 : reg); subst dst; ed_lin ltac:(cbn [ev ENV]; rewrite ?P0); f_equal; lia);
        assert (A11 : getr Rc 11 = Z_to_bv 64 0x1084c) by (regv HR (11 : reg); reflexivity);
        assert (A12 : getr Rc 12 = Z_to_bv 64 1) by (regv HR (12 : reg); reflexivity);
        destruct (ref_memcpy MG dst (Z_to_bv 64 0x1084c) 1 _ (seg_rom RSEGS) MC Rc (0x41d64 : word)
                    ltac:(apply ret_ok_even; reflexivity) A1 A10 A11 A12) as (R2 & Hms & Hkeep);
        clear A1 A10 A11 A12
      end.
      replace (Z_to_bv 64 289344) with (0x46a40 : word) by (apply bv_eq; reflexivity).
      eapply rz_msteps; [exact Hh | exact Hlazy | exact Hms |]. clear Hms.
      replace (0x41d64 : word) with (Z_to_bv 64 0x41d64) by (apply bv_eq; reflexivity).
      lazymatch type of HR with regs_ok ?E ?sr ?Rc =>
        pose proof (regs_after_keeps vals1 (blobs_ev BL) sr Rc R2 callee_kept
                      ltac:(rewrite HL; vm_compute; reflexivity) HR Hkeep callee_kept_no0) as HR2 end.
      rewrite HL in HR2. clear HR Hkeep. rename HR2 into HR.
      (* [comment removed for export] *)
      pose proof (know_after_store RSEGS (ENV BL vals1) MG knG4 (SA (EVar 0) (-560)) 1 (ELit 10) [Z_to_bv 8 10]
                    knH40 [] [] ltac:(vm_compute; reflexivity) eq_refl HK ltac:(lia)
                    ltac:(apply flat_intro; cbn [edenot ev ENV]; rewrite ?P0; lia)
                    ltac:(cbn [edenot]; symmetry; apply NL_word)) as HK2.
      clear HK.
      assert (Edst : adenot (ENV BL vals1) (SA (EVar 0) (-560)) = dst).
      { unfold adenot, v_addi. cbn [a_base a_off edenot ev ENV]. rewrite P0. subst dst. f_equal; lia. }
      rewrite Edst in HK2.
      pose proof (env_app_know RSEGS vals1 (junk_vals R2) (blobs_ev BL) (wbytes MG dst [Z_to_bv 8 10]) knH40
                    ltac:(rewrite HL; vm_compute; reflexivity) HK2) as HK.
      clear HK2.
      set (vals2 := vals1 ++ junk_vals R2) in *.
      assert (HL2 : length vals2 = 231%nat) by (subst vals2; rewrite length_app, junk_vals_length, HL; reflexivity).
      assert (Q0 : vals_ev vals2 0 = sp0) by (subst vals2; rewrite vals_ev_app_l by (rewrite HL; lia); exact P0).
      clearbody vals2.
      change (Env (vals_ev vals2) (blobs_ev BL)) with (ENV BL vals2) in HR, HK.
      eapply (of_segH4 vals2); [exact HL2 | exact Q0 | exact HR | exact HK].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  #[using="Hvsp Hh Hlazy Hfd2 SPlo SPhi"] Theorem of_tail : ltac2:(CDefT.buildp (gd_tbl_P_mainleaf_openfail_tail2 ()) "Ppath,(0.(1.&8.))Ppp,(1.&40.)Pt8,(0.(1.&8.))Pvals,(0.(1.&40.))PR,(2.&5.(1.&40.))PM,P,(1.&40.)(3.(1.&8.))P,(2?.(30.(1.&8.)(12.&8.=)R6.))P,(26.(1:.(6.(1.&8.)R7.))+1????.)P,(4.$5.(6.(1.&40.)R5.)#27.)P,(4.(1.&40.)(7.R6.#0.)Vsp0,)P,(4.(1.&40.)(7.R7.#2.)R9.)P,(26.(31.(32.+2.+40.)+???.)(27.&40.(7.R8.#26.)))P,(26.(27.&40.Vsp0,)(27.&40.R;.))P,(26.(28.(28.(27.&40.R<.)(1:.(6.(1.&8.)R=.)))+8.)(28.(27.&40.Vsp0,)+400000.))P,(26.(28.(28.(27.&40.R=.)(1:.(6.(1.&8.)R>.)))+1.)+800000000000.)P,(8.(9.VBL,R<.)(33.$34.(35.(36.&5.+:.$37.))(38.#26.))R;.)P,(;.$<.(9.VBL,R=.)R;.$39.)P,(4.(3.(0.(1.&8.)))(2;.$<.R<.R10.(2<.(6.(1.&8.)R11.)#1.))(2=.(0.(1.&8.))(2>.(1.&8.)R11.(23.(1.&8.)(12.&8.=)(24.(1.&8.))))))P,(4.(3.(0.(1.&8.)))(2;.$<.R=.(12.&40.(28.(27.&40.R11.)(1:.(6.(1.&8.)R12.))))#8.)(2=.(0.(1.&8.))R10.))(>.$<.(?.(10.$11.R?.(12.&40.+4729<.)R>.(13.$<.))Vmodel,)(3:.(1>.R13.)(16.Vmodel,)))")
(* [comment removed for export] *).
  Proof.
    intros path pp t8 vals R M Hnonul HPl HL P0 P2 P38 Hpp1 Hpp2 Hpp3 HR HK Hstr Ht8.
    unfold t_die.
    eapply (of_segBC sp0 BL model Hvsp Hh Hlazy path pp (Z.of_nat (length path)) _ t8 vals);
      try eassumption; try lia.
    intros vals' R' M' HL' Q0 Q2 Q113 HR' HK' Hstr'.
    destruct (Z.le_gt_cases (Z.of_nat (length path)) 62) as [Hle | Hgt].
    - eapply (of_segF sp0 BL model Hvsp Hh Hlazy Hfd2 path pp _ vals'); try eassumption; lia.
    - destruct (Z.le_gt_cases (Z.of_nat (length path)) 63) as [Hle2 | Hgt2].
      + assert (E63 : Z.of_nat (length path) = 63%Z) by lia. rewrite E63 in Q113.
        eapply (of_segF_gen sp0 BL model Hvsp Hh Hlazy path pp 63 _ vals'); try eassumption; try lia.
        apply of_segG3. exact E63.
      + eapply (of_segFG4 path pp _ vals'); try eassumption; lia.
  Qed.

End Tail2.
