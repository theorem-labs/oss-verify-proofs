(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
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
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U Require Import U_mainleaf_openfail_defs.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import DietDestruct.   (* [comment removed for export] *)
Import ListNotations.
Open Scope bv_scope.
Import SX2. Import SX2S.
#[local] Existing Instance PropExec.fx0.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import LiaOrc. (* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= orc_lia. (* [comment removed for export] *)
Ltac2 gd_tbl_P_mainleaf_openfail_tail () : Init.string Init.list := ["Corelib.Init.Datatypes.list"; "stdpp.bitvector.definitions.bv"; "LinuxProcessSemantics.Riscv.Prelude.bvmap"; "Corelib.Init.Datatypes.option"; "Corelib.Init.Logic.eq"; "Corelib.Init.Datatypes.nat"; "Corelib.Init.Datatypes.length"; "RocqVerifyHarness.AgentSubmission.BB.SymRun.vals_ev"; "RocqVerifyHarness.AgentSubmission.BB.SymExec2Sound.SX2S.regs_ok"; "Tail.ENV"; "RocqVerifyHarness.AgentSubmission.U.U_mainleaf_openfail_defs.srI0"; "RocqVerifyHarness.AgentSubmission.BB.SymExec2Sound.SX2S.know_ok"; "RocqVerifyHarness.ProcessOversight.Tgt_fuzz_pkcs7_ubsan.M.loaded_segments"; "RocqVerifyHarness.AgentSubmission.U.U_mainleaf_openfail_defs.knI0"; "RocqVerifyHarness.AgentSubmission.Lib.Shape.realizes"; "LinuxProcessSemantics.LinuxProcessSem.Run.mkCfg"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.mkst"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.fx0"; "stdpp.bitvector.definitions.Z_to_bv"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.seg_rom"; "RocqVerifyHarness.AgentSubmission.Lib.Shape.t_exit"; "RocqVerifyHarness.AgentSubmission.Spec.Spec.exit_code"; "LinuxProcessSemantics.LinuxProcessSem.State.m_fs"; "Corelib.Init.Datatypes.app"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.word_to_le_bytes"; "Tail.PRE17"; "Corelib.Numbers.BinNums.Z"; "Stdlib.ZArith.BinInt.Z.of_nat"; "Corelib.Init.Logic.and"; "Stdlib.ZArith.BinInt.Z.le"; "RocqVerifyHarness.AgentSubmission.U.U_mainleaf_openfail_defs.srH0"; "RocqVerifyHarness.AgentSubmission.U.U_mainleaf_openfail_defs.knH0"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.rdn"; "Stdlib.ZArith.BinInt.Z.sub"; "stdpp.bitvector.definitions.bv_unsigned"; "Corelib.Init.Datatypes.Some"; "Stdlib.ZArith.BinInt.Z.add"; "Corelib.Init.Datatypes.cons"; "Corelib.Init.Datatypes.nil"; "RocqVerifyHarness.AgentSubmission.Lib.Shape.t_emit"; "RocqVerifyHarness.AgentSubmission.Spec.Spec.W"; "RocqVerifyHarness.AgentSubmission.Spec.Spec.msg_cannot_open"; "RocqVerifyHarness.AgentSubmission.U.U_mainleaf_openfail_defs.srG0"; "RocqVerifyHarness.AgentSubmission.U.U_mainleaf_openfail_defs.knG0"; "RocqVerifyHarness.AgentSubmission.Lib.Shape.TSet"; "RocqVerifyHarness.AgentSubmission.U.U_mainleaf_openfail_defs.srF0"; "RocqVerifyHarness.AgentSubmission.U.U_mainleaf_openfail_defs.knE"; "Corelib.Init.Nat.add"; "Tail.atG0"; "Corelib.Init.Logic.not"; "Stdlib.Lists.List.In"; "RocqVerifyHarness.AgentSubmission.U.U_mainleaf_openfail_defs.srD0"; "RocqVerifyHarness.AgentSubmission.U.U_mainleaf_openfail_defs.knC"; "Tail.atF0"; "RocqVerifyHarness.AgentSubmission.BB.SymExec2Sound.SX2S.mem_denot"; "RocqVerifyHarness.AgentSubmission.U.U_mainleaf_openfail_defs.logM1"; "RocqVerifyHarness.AgentSubmission.BB.CatExec.wbytes"; "Stdlib.ZArith.BinInt.Z.pow"; "RocqVerifyHarness.AgentSubmission.BB.SymExec2.SX2.sr_upd"; "RocqVerifyHarness.AgentSubmission.U.U_mainleaf_openfail_defs.srA"; "RocqVerifyHarness.AgentSubmission.BB.SymExec2.SX2.ridx"; "stdpp.bitvector.definitions.BV"; "Corelib.Init.Logic.I"; "RocqVerifyHarness.AgentSubmission.BB.SymExec2.SX2.EVar"; "RocqVerifyHarness.AgentSubmission.U.U_mainleaf_openfail_defs.knA"].


(* [comment removed for export] *)
Tactic Notation "run_blk" constr(scr) constr(NX) := run_block_gen FUEL STOPS scr NX false.
Tactic Notation "run_blk_keep" constr(scr) constr(NX) := run_block_gen FUEL STOPS scr NX true.

Section Tail.
  Variable sp0 : word.
  Variable BL : list (list byte).          (* [comment removed for export] *)
  Variable model : Model.
  Hypothesis Hvsp : valid_sp sp0.
  Hypothesis Hh : m_halted model = None.
  Hypothesis Hlazy : m_vm_lazy model = [].
  Hypothesis Hfd2 : fd_lookup (m_fds model) (Z_to_bv 64 2) = Some (FdChannel (Z_to_bv 64 2)).

  Definition ENV (vals : list word) : env := Env (vals_ev vals) (blobs_ev BL).

  Let SPlo : (0x7fff80000000 <= bv_unsigned sp0)%Z := proj1 Hvsp.
  Let SPhi : (bv_unsigned sp0 <= 0x800000000000)%Z := proj1 (proj2 Hvsp).

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00O0?L25276050947.19L25329248598.19L29746160968.19L29884719432.19L30614036831.19L31302360648.19L3154234440.19 L34058993625.20L36883086024.19L37583384136.19L42868787934.19L4329799800.19 L43745135966.19L44581741512.19L46121157832.19L47039351654.19L47679846856.19L53176470819.19L53277344840.19L59153296392.19L5931004077.19 L59552903458.19L60410236885.20L63338158024.19L64541015021.19L66020815454.19L67822791560.19L67974104776.19L7091981256.19 L7931362120.19 L9964233391.19 00000900P00Y00b01001901B01O01X01a01j02302<02E02N02W02`02i03203;03D03V03d03m04604?04H04Q04Z04c055S4vals2HLS3sp04SPlo4SPhi4vals2HLS4vals2HLS4vals2HLS4vals2HL4KtidS4vals2HLS4vals2HLS3sp04vals2HLS4vals2HLS4vals2HLS4vals2HLS4vals2HLS4vals2HLS4vals2HLS4vals2HLS4vals2HLS4vals2HLS4vals2HLS4vals2HLS4vals2HLS4vals2HLS3sp04SPlo4vals2HLS4vals2HL4KtidS4vals2HLS4vals2HLS4vals2HLS4vals2HLS4vals2HLS4vals2HLS4vals2HLS3sp04SPhi4vals2HL". (* [comment removed for export] *)
  #[using="Hvsp Hh Hlazy SPlo SPhi"] Lemma of_segI : ltac2:(CDefT.buildp (gd_tbl_P_mainleaf_openfail_tail ()) "Pvals,(0.(1.&40.))PR,(2.&5.(1.&40.))PM,P,(1.&40.)(3.(1.&8.))P,(4.$5.(6.(1.&40.)R3.)#107.)P,(4.(1.&40.)(7.R4.#0.)Vsp0,)P,(8.(9.R5.)$:.R4.)P,(;.$<.(9.R6.)R4.$=.)(>.$<.(?.(10.$11.R6.(12.&40.+420:8.)R5.(13.$<.))Vmodel,)(14.(15.+2.)(16.Vmodel,)))")
(* [comment removed for export] *).
  Proof.
    intros vals R M HL P0 HR HK.
    pose proof SPlo as Hlo. pose proof SPhi as Hhi.
    run_blk scr0 263%nat.
    (* [comment removed for export] *)
    apply (rz_conseq RSEGS _ (t_emit (W 1 []) (t_exit (bv_and (Z_to_bv 64 2) (Z_to_bv 64 255)) (m_fs model)))).
    2:{ cbn [W map].
        replace (bv_and (Z_to_bv 64 2) (Z_to_bv 64 255)) with (exit_code 2) by (apply bv_eq; reflexivity).
        apply t_eq_sym. apply t_emit_nil_exit. }
    apply ref_exit_Z.
    pose proof (know_nth RSEGS _ _ knI ltac:(let i := kidx knI (is_krange (EVar 5)) in exact i) _ HK eq_refl)
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
        pose proof (kwr_store_ok RSEGS (ENV vals) _ knI ltac:(let i := kidx knI (is_kwr_cov (EVar 0) (-272) 144) in exact i)
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
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  (* [comment removed for export] *)
  Definition PRE17 : list byte := s2b "cli: cannot open "%string.

  #[using="Type"] Lemma PRE17_words : ltac2:(CDefT.buildp (gd_tbl_P_mainleaf_openfail_tail ()) "(4.(0.(1.&8.))(17.(1.&8.)(18.#8.(12.&40.+6>6163203:696<63.))(17.(1.&8.)(18.#8.(12.&40.+6>65706?20746?6>.))(18.#1.(12.&40.+20.))))$19.)")
(* [comment removed for export] *).
  Proof. vm_compute. repeat (apply (f_equal2 cons); [apply bv_eq; reflexivity|]). reflexivity. Qed.

  Local Ltac2 Set LiaOrc.tbl := fun () => "00g0?L12245466970.29L14418071291.30L15045278903.35L15634797243.35L16639375087.35L20824379164.35L20923401285.35L2133530424.32 L24134822011.32L25278098835.29L25278098835.30L27836886250.35L30226912948.37L30452499962.31L30452506865.32L30467067489.28L32857128880.28L32858771744.32L32858780715.31L32861317660.35L33656270521.28L33671292192.29L3651887136.35 L37803532303.32L38478037260.31L38884559273.29L38948788060.35L40465950858.35L41231950618.31L41493492207.35L41506071619.28L44247534562.32L44247543529.31L44911943466.30L4826696077.35 L48269158559.29L49702778536.31L50040071339.35L51702320857.30L53089041842.35L53178551987.31L5933052733.29 L5933052733.30 L5933052733.31 L622633325.35  L6384997240.29 L64149391721.35L65473109180.35L65903738011.29L67396173106.30L68056979096.30L68446033860.29L7213634117.30 L8534631579.30 L9359554572.28 00000G00^01001P01k02F02X03703N03\03j04<04N04e05<05S05j06A06X07307A07O07k08=08O08f09809S09e0:@0:W0:n0;E0;\0<70<S0<j0=@0=W0>20>@0>N0>\0>j0?I0?`0@60@V0@h0A@0AN0Ai0BA0Bd0C@S3sp04SPhi4path4vals2HLS3sp04SPhi4path4vals2HLS4path4vals2HL3LENS3sp04path1P4vals3HPr2HL3Hhi3LENS3sp04SPhi4path4vals2HL3LENS3sp04SPlo4path4vals2HL3LENS4path4vals2HL3LENS3sp04path1P4vals2HP3HPr2HL3HhiS3sp04path1P4vals2HP2HLS4path4vals2HLS4path4vals2HLS4path4vals2HL3LENS4path4vals2HL3LENS3sp04SPhi4path4vals2HLS3sp04SPhi4path4vals2HLS3sp04SPhi4path4vals2HLS3sp04SPlo4path4vals2HLS3sp04SPlo4path4vals2HLS3sp04SPlo4path4vals2HLS3sp04SPlo4path4vals2HL3LENS4path4vals2HLS4path4vals2HLS3sp04path1P4vals3HPr2HL3LENS3sp04path4vals2HLS3sp04path4vals2HLS3sp04SPlo4path4vals2HLS4path4vals2HL3LENS3sp04path1P4vals2HP2HL3LENS3sp04path4vals2HLS3sp04SPhi4path4vals2HL3LENS3sp04SPhi4path4vals2HLS3sp04SPlo4path4vals2HLS3sp04SPlo4path4vals2HLS3sp04SPlo4path4vals2HLS4path1P4vals2HP3HPr2HL3LENS3sp04SPlo4SPhi4path4vals2HLS3sp04SPhi4path4vals2HLS3sp04path4vals2HL3LENS3sp04SPhi4path4vals2HLS3sp04SPlo4path4vals2HL3LENS4path4vals2HLS4path4vals2HLS4path4vals2HLS4path4vals2HLS3sp04path1P4vals2HP2HL3Hlo3LENS3sp04SPhi4path4vals2HLS3sp04path4vals2HL3LENS3sp04path1P4vals3HPr2HL3Hhi3LENS3sp04path4vals2HLS3sp04path1P4vals3HPr2HLS4path4vals2HLS3sp04path1P4vals2HP3HPr2HLS3sp04path1P4vals3HPr2HLS3sp04path1P4vals2HP3HPr2HL3Hlo3HhiS3sp04SPlo4SPhi4path4vals2HL". (* [comment removed for export] *)
  #[using="Hvsp Hh Hlazy Hfd2 SPlo SPhi"] Lemma of_segH : ltac2:(CDefT.buildp (gd_tbl_P_mainleaf_openfail_tail ()) "Ppath,(0.(1.&8.))PP,$1:.Pvals,(0.(1.&40.))PR,(2.&5.(1.&40.))PM,P,(1.&40.)(3.(1.&8.))P,(4.$1:.(1;.(6.(1.&8.)R5.))R4.)P,(1<.(1=.=R5.)(1=.R5.+3>.))P,(4.$5.(6.(1.&40.)R5.)#>7.)P,(4.(1.&40.)(7.R6.#0.)Vsp0,)P,(4.(1.&40.)(7.R7.#71.)(12.&40.R8.))P,(8.(9.R8.)$1>.R7.)P,(;.$<.(9.R9.)R7.$1?.)P,(4.(3.(0.(1.&8.)))(20.$<.R8.(12.&40.(21.(22.&40.Vsp0,)+21?.))(6.(1.&8.)R<.))(23.(0.(1.&8.))R<.))P,(4.(3.(0.(1.&8.)))(20.$<.R9.(12.&40.(24.(21.(22.&40.Vsp0,)+21?.)R<.))#1.)(23.(0.(1.&8.))(25.(1.&8.)(12.&8.+:.)(26.(1.&8.)))))(>.$<.(?.(10.$11.R;.(12.&40.+41=64.)R:.(13.$<.))Vmodel,)(27.(28.+2.(29.R>.))(14.(15.+2.)(16.Vmodel,))))")
(* [comment removed for export] *).
  Proof.
    intros path P vals R M HP HPr HL P0 P113 HR HK SBp SBn.
    pose proof SPlo as Hlo. pose proof SPhi as Hhi.
    (* [comment removed for export] *)
    run_blk_keep scr0 231%nat.
    (* [comment removed for export] *)
    assert (WOK : win_ok (ENV vals) 0 BUF_LO BUF_HI IHI).
    { unfold win_ok, BUF_LO, BUF_HI, IHI. cbn [ev ENV]. rewrite P0. lia. }
    assert (SBp' : rdn RSEGS M0 (Z_to_bv 64 (bv_unsigned sp0 - 543)) (length path) = Some path).
    { rewrite EQM, (rdn_mem_denot_out RSEGS (ENV vals) M _ 0 BUF_LO BUF_HI IHI);
        [exact SBp | vm_compute; reflexivity | exact WOK | cbn [ev ENV]; rewrite P0; unfold BUF_LO; rewrite u_small by lia; lia
        | cbn [ev ENV]; rewrite P0; unfold BUF_HI; rewrite u_small by lia; lia]. }
    assert (SBn' : rdn RSEGS M0 (Z_to_bv 64 (bv_unsigned sp0 - 543 + P)) 1 = Some [Z_to_bv 8 10]).
    { rewrite EQM, (rdn_mem_denot_out RSEGS (ENV vals) M _ 0 BUF_LO BUF_HI IHI);
        [exact SBn | vm_compute; reflexivity | exact WOK | cbn [ev ENV]; rewrite P0; unfold BUF_LO; rewrite u_small by lia; lia
        | cbn [ev ENV]; rewrite P0; unfold BUF_HI; rewrite u_small by lia; cbn; lia]. }
    clear EQM SBp SBn. rename M0 into M'. 
    (* [comment removed for export] *)
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
    assert (MSG : rdn RSEGS M' (Z_to_bv 64 (bv_unsigned sp0 + -560)) (17 + (length path + 1))
                  = Some (msg_cannot_open path)).
    { unfold msg_cannot_open. change (s2b _) with PRE17.
      apply rdn_app_Z; [exact H17 | | lia | lia].
      apply rdn_app_Z; [| | lia | lia].
      + replace (bv_unsigned sp0 + -560 + Z.of_nat 17)%Z with (bv_unsigned sp0 - 543)%Z by lia. exact SBp'.
      + replace (bv_unsigned sp0 + -560 + Z.of_nat 17 + Z.of_nat (length path))%Z
          with (bv_unsigned sp0 - 543 + P)%Z by lia. exact SBn'. }
    (* [comment removed for export] *)
    assert (LEN : length (msg_cannot_open path) = (17 + (length path + 1))%nat)
      by (unfold msg_cannot_open; rewrite !length_app; reflexivity).
    replace (W 2 (msg_cannot_open path)) with (map (WriteEv (Z_to_bv 64 2)) (msg_cannot_open path ++ []))
      by (unfold W; rewrite app_nil_r; reflexivity).
    dpose itinerary_le62 as (_ & _ & _ & _ & _ & _ & _ & _ & SC & _).
    lazymatch goal with |- realizes _ (mkCfg (mkst ?Rc _ ?Mc _) _) _ =>
    apply (stdio_call_sound vals (blobs_ev BL) srH knH Rc Mc model scOF (msg_cannot_open path) []
             (t_exit (exit_code 2) (m_fs model)) HR HK (eq_trans (f_equal (fun n => stdio_call n srH knH) HL) SC));
      cbn [sc_f sc_fd sc_ret sc_wb sc_wp sc_bufp sc_bufsz sc_s sc_l sc_sp sc_sr sc_kn scOF]; rewrite ?LEN end.
    - ed_lin ltac:(cbn [ev ENV]; rewrite ?P0, ?P113). unorm. lia.
    - ed_lin ltac:(cbn [ev ENV]; rewrite ?P0, ?P113). unorm. lia.
    - cbn [edenot length]. reflexivity.
    - cbn [length Z.of_nat]. lia.
    - right. ed_lin ltac:(cbn [ev ENV]; rewrite ?P0, ?P113). unorm. lia.
    - left. ed_lin ltac:(cbn [ev ENV]; rewrite ?P0, ?P113). unorm. lia.
    - cbn [edenot]. unorm. lia.
    - ed_lin ltac:(cbn [ev ENV]; rewrite ?P0, ?P113). unorm. lia.   (* [comment removed for export] *)
    - cbn [edenot]. unorm. lia.   (* [comment removed for export] *)
    - ed_lin ltac:(cbn [ev ENV]; rewrite ?P0, ?P113). unorm.
      replace (bv_unsigned sp0 + -560)%Z with (bv_unsigned sp0 + -560)%Z in MSG by lia. exact MSG.
    - reflexivity.
    - exact Hfd2.
    - exact Hh.
    - exact Hlazy.
    - apply t_exit_has_nil.
    - (* [comment removed for export] *)
      clear HR HK. intros R2 M2 HR HK.
      eapply (of_segI (vals ++ junk_vals R2));
        [ rewrite length_app, junk_vals_length, HL; reflexivity
        | rewrite vals_ev_app_l by (rewrite HL; lia); exact P0
        | exact HR | exact HK ].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  #[using="Type"] Lemma nl_img : rdn RSEGS (fun _ => None) (Z_to_bv 64 0x1084c) 1 = Some [Z_to_bv 8 10].
  Proof. vm_compute. reflexivity. Qed.

  Local Ltac2 Set LiaOrc.tbl := fun () => "00U0?L16264749317.29L16970013023.35L16974067588.36L22039677358.28L22915966606.28L26823884495.29L29809534340.29L30224815626.33L32714571052.29L37787127474.35L38844734437.24L39110999443.31L40637660828.35L48269158559.28L48283867559.35L49282067897.31L50497024192.24L52516262761.24L52526751222.29L54441417064.34L55371345329.29L60358885047.29L62550700534.29L63308151236.29L65903738011.28L68446033860.28L6875801538.29 L7200670590.31 L79974662.24   L8530357212.36 L8530359712.31 L8534550086.29 L8534656263.35 L9152800632.31 L9317012995.29 L9359554572.27 L9361438865.32 00000D00j01P01^01l01m02;02P02d03E03Y03m04V05205X06006@06N06\07107207@07N07b08408O08j09B09V0:C0:f0;I0<60<M0<i0=E0=aS4path1P4vals3HPr2HLS3sp04path1P4vals3HPr2HL3Hhi5vals13HL1S3sp04path1P4vals3HPr2HL3Hhi5vals13HL1S4path4vals2HLS4path4vals2HLFS4path4vals2HLS4path4vals2HL2R23HL1S3sp04path1P4vals2HLS3sp04path1P4vals2HP2HL5vals13HL1S4path1P4vals3HPr2HLS3sp04path1P4vals2HLS3sp04path1P4vals2HP3HPr2HL3Hhi5vals13HL1S3sp04SPlo4SPhi4path4vals2HLS3sp04SPlo4SPhi4path4vals2HL5vals13HL1S3sp04path1P4vals3HPr2HLS4path1P4vals2HLS4path4vals2HLS4path4vals2HLS4path4vals2HL2R23HL1FS4path4vals2HLS4path4vals2HLS4path1P4vals3HPr2HLS3sp04path4vals2HLS3sp04path1P4vals2HP3HPr2HLS3sp04path1P4vals2HP2HL3HloS3sp04path1P4vals3HPr2HLS4path1P4vals3HPr2HLS3sp04path1P4vals2HP3HPr2HL3Hlo3Hhi5vals13HL1S3sp04path1P4vals2HP3HPr2HL3Hlo3HhiS3sp04path1P4vals2HP3HPr2HL3Hlo3HhiS3sp04path1P4vals2HP3HPr2HL3Hlo3Hhi5vals13HL1S3sp04SPhi4path4vals2HLS3sp04path1P4vals3HPr2HL3HhiS3sp04SPlo4SPhi4path4vals2HLS3sp04SPlo4SPhi4path4vals2HL". (* [comment removed for export] *)
  #[using="Hvsp Hh Hlazy Hfd2 SPlo SPhi"] Lemma of_segG : ltac2:(CDefT.buildp (gd_tbl_P_mainleaf_openfail_tail ()) "Ppath,(0.(1.&8.))PP,$1:.Pvals,(0.(1.&40.))PR,(2.&5.(1.&40.))PM,P,(1.&40.)(3.(1.&8.))P,(4.$1:.(1;.(6.(1.&8.)R5.))R4.)P,(1<.(1=.=R5.)(1=.R5.+3>.))P,(4.$5.(6.(1.&40.)R5.)#<7.)P,(4.(1.&40.)(7.R6.#0.)Vsp0,)P,(4.(1.&40.)(7.R7.#71.)(12.&40.R8.))P,(8.(9.R8.)$2:.R7.)P,(;.$<.(9.R9.)R7.$2;.)P,(4.(3.(0.(1.&8.)))(20.$<.R8.(12.&40.(21.(22.&40.Vsp0,)+21?.))(6.(1.&8.)R<.))(23.(0.(1.&8.))R<.))(>.$<.(?.(10.$11.R:.(12.&40.+41=64.)R9.(13.$<.))Vmodel,)(27.(28.+2.(29.R=.))(14.(15.+2.)(16.Vmodel,))))")
(* [comment removed for export] *).
  Proof.
    intros path P vals R M HP HPr HL P0 P113 HR HK SBp.
    pose proof SPlo as Hlo. pose proof SPhi as Hhi.
    (* [comment removed for export] *)
    run_blk_keep scrG 199%nat.
    { (* [comment removed for export] *)
      unfold sc_denot. cbn [branch_taken]. ed_lin ltac:(cbn [ev ENV]; rewrite ?P0, ?P113).
      replace (-1 * P + 63)%Z with (63 - P)%Z by lia.
      rewrite ltu_ZZ by lia. cbn [negb]. rewrite (proj2 (Z.ltb_ge _ _)) by lia. reflexivity. }
    assert (WOK : win_ok (ENV vals) 0 BUF_LO BUF_HI IHI).
    { unfold win_ok, BUF_LO, BUF_HI, IHI. cbn [ev ENV]. rewrite P0. lia. }
    assert (SBp' : rdn RSEGS M0 (Z_to_bv 64 (bv_unsigned sp0 - 543)) (length path) = Some path).
    { rewrite EQM, (rdn_mem_denot_out RSEGS (ENV vals) M _ 0 BUF_LO BUF_HI IHI);
        [exact SBp | vm_compute; reflexivity | exact WOK | cbn [ev ENV]; rewrite P0; unfold BUF_LO; rewrite u_small by lia; lia
        | cbn [ev ENV]; rewrite P0; unfold BUF_HI; rewrite u_small by lia; lia]. }
    clear EQM SBp. rename M0 into M'.
    (* [comment removed for export] *)
    set (dst := Z_to_bv 64 (bv_unsigned sp0 - 543 + P)).
    assert (Hsrc : rdn RSEGS M' (Z_to_bv 64 0x1084c) 1 = Some [Z_to_bv 8 10]).
    { rewrite (kimg_rdn RSEGS (ENV vals) _ knG ltac:(let i := kidx knG (is_kimg_cov 0x1084c 1) in exact i)
                 _ _ 0x1084c 1 HK eq_refl) by (cbn; lia). apply nl_img. }
    assert (Hdst : store_ok RSEGS M' dst 1 = true).
    { pose proof (kwr_store_ok RSEGS (ENV vals) _ knG ltac:(let i := kidx knG (is_kwr_cov (EVar 0) (-543) 64) in exact i)
                    _ _ _ (-543 + P) 1 HK eq_refl ltac:(lia) ltac:(cbn; lia)) as Hst.
      unfold adenot, v_addi in Hst. cbn [a_base a_off edenot ev ENV] in Hst. rewrite P0 in Hst.
      subst dst. replace (bv_unsigned sp0 - 543 + P)%Z with (bv_unsigned sp0 + (-543 + P))%Z by lia. exact Hst. }
    assert (MC : mcH M' dst (Z_to_bv 64 0x1084c) 1 [Z_to_bv 8 10]).
    { constructor; cbn [length Z.to_nat Z.of_nat Pos.to_nat]; subst dst; rewrite ?u_small by lia; try lia.
      - exact Hsrc.
      - exact Hdst. }
    lazymatch goal with |- realizes _ (mkCfg (mkst ?Rc _ _ _) _) _ =>
      assert (A1 : getr Rc 1 = (0x41d64 : word)) by (regv HR (1 : reg); apply bv_eq; reflexivity);
      assert (A10 : getr Rc 10 = dst)
        by (regv HR (10 : reg); subst dst; ed_lin ltac:(cbn [ev ENV]; rewrite ?P0, ?P113); f_equal; lia);
      assert (A11 : getr Rc 11 = Z_to_bv 64 0x1084c) by (regv HR (11 : reg); reflexivity);
      assert (A12 : getr Rc 12 = Z_to_bv 64 1) by (regv HR (12 : reg); reflexivity);
      destruct (ref_memcpy M' dst (Z_to_bv 64 0x1084c) 1 _ (seg_rom RSEGS) MC Rc (0x41d64 : word)
                  ltac:(apply ret_ok_even; reflexivity) A1 A10 A11 A12) as (R2 & Hms & Hkeep);
      clear A1 A10 A11 A12
    end.
    replace (Z_to_bv 64 289344) with (0x46a40 : word) by (apply bv_eq; reflexivity).
    eapply rz_msteps; [exact Hh | exact Hlazy | exact Hms |]. clear Hms.
    replace (0x41d64 : word) with (Z_to_bv 64 0x41d64) by (apply bv_eq; reflexivity).
    (* [comment removed for export] *)
    lazymatch type of HR with regs_ok ?E ?sr ?Rc =>
      pose proof (regs_after_keeps vals (blobs_ev BL) sr Rc R2 callee_kept
                    ltac:(rewrite HL; vm_compute; reflexivity) HR Hkeep callee_kept_no0) as HR2 end.
    rewrite HL in HR2. clear HR Hkeep. rename HR2 into HR.
    (* [comment removed for export] *)
    pose proof (know_cut_sound RSEGS (ENV vals) M' (wbytes M' dst [Z_to_bv 8 10]) 0 (-543) BUF_HI IHI knG
                  ltac:(unfold win_ok, BUF_HI, IHI; cbn [ev ENV]; rewrite P0; lia)
                  ltac:(apply (wbytes_agree_out M' dst [Z_to_bv 8 10] (ENV vals) 0 (-543) BUF_HI);
                        cbn [ev ENV length]; rewrite P0; subst dst; unfold BUF_HI; rewrite ?u_small by lia; lia)
                  (wbytes_grows _ _ _) HK) as HK2.
    clear HK. change (kn_cut 0 (-543) BUF_HI IHI knG) with knH0 in HK2.
    pose proof (env_app_know RSEGS vals (junk_vals R2) (blobs_ev BL) _ knH0 ltac:(rewrite HL; vm_compute; reflexivity) HK2) as HK.
    clear HK2.
    set (vals1 := vals ++ junk_vals R2) in *.
    assert (HL1 : length vals1 = 231%nat) by (subst vals1; rewrite length_app, junk_vals_length, HL; reflexivity).
    assert (Q0 : vals_ev vals1 0 = sp0) by (subst vals1; rewrite vals_ev_app_l by (rewrite HL; lia); exact P0).
    assert (Q113 : vals_ev vals1 113 = Z_to_bv 64 P) by (subst vals1; rewrite vals_ev_app_l by (rewrite HL; lia); exact P113).
    clearbody vals1.
    change (Env (vals_ev vals1) (blobs_ev BL)) with (ENV vals1) in HR, HK.
    eapply (of_segH path P vals1); try eassumption.
    - (* [comment removed for export] *)
      rewrite rdn_wbytes_out; [exact SBp' | | |]; cbn [length]; subst dst; rewrite ?u_small by lia; lia.
    - (* [comment removed for export] *)
      subst dst. pose proof (rdn_wbytes_hit RSEGS [Z_to_bv 8 10] M' (Z_to_bv 64 (bv_unsigned sp0 - 543 + P))) as Hn.
      cbn [length] in Hn. apply Hn. rewrite u_small by lia. lia.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  (* [comment removed for export] *)
  Definition atG0 (path : list byte) (P : Z) (T : TSet) : Prop := ltac2:(CDefT.buildp (gd_tbl_P_mainleaf_openfail_tail ()) "Pvals,(0.(1.&40.))PR,(2.&5.(1.&40.))PM,P,(1.&40.)(3.(1.&8.))P,(4.$5.(6.(1.&40.)R3.)#<7.)P,(4.(1.&40.)(7.R4.#0.)Vsp0,)P,(4.(1.&40.)(7.R5.#71.)(12.&40.O2.))P,(8.(9.R6.)$2:.R5.)P,(;.$<.(9.R7.)R5.$2;.)P,(4.(3.(0.(1.&8.)))(20.$<.R6.(12.&40.(21.(22.&40.Vsp0,)+21?.))(6.(1.&8.)O3.))(23.(0.(1.&8.))O3.))(>.$<.(?.(10.$11.R8.(12.&40.+41=64.)R7.(13.$<.))Vmodel,)O1.)")
(* [comment removed for export] *).

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00M0?L10305706566.30L11660218926.31L11664808246.36L11671099305.30L19061701751.35L20545408631.36L21646784878.31L21934777294.31L25351397799.36L30224815626.40L31309203627.35L33398751146.36L39460800308.38L40650610124.43L48220654016.36L48271665408.38L48271667959.43L48284252902.36L51701270147.36L54441417064.41L55760775311.36L57112669364.36L65340997948.35L66262088256.36L67862706547.36L68443985499.38L9152800632.38 L9359554572.34 L9361438865.39 00000D00X00l01@01Z02102?02S02f03;03Z04:04L05505G05c06I06e06f07;07I07J07X08808T08o09F09b0:>S4path1P4vals3HPr2HLS4path1P4vals3HPr2HLS4path1P4vals3HPr2HLS4path1P4vals3HPr2HLS3sp04path2pp4vals2HL4Hpp1S4path1P4vals2HP3HPr2HLS4path4vals2HLS4path1P4vals3HPr2HLS4path1P4vals2HP2HLS4path4vals2HL2R23HL1S3sp04path2pp1P4vals2HP2HL4Hpp2S3sp04path2pp1P4vals3HPr2HL4Hpp1S3sp04path4vals2HLS3sp04path1P4vals2HP3HPr2HL3Hhi5vals13HL1S3sp04path4vals2HLS3sp04SPlo4SPhi4path4vals2HLS3sp04SPlo4SPhi4path4vals2HL5vals13HL1S3sp04SPlo4SPhi4path4vals2HLFS4path4vals2HL2R23HL1S4path4vals2HLFS4path4vals2HLS3sp04path2pp1P4vals2HL4Hpp23HhiS3sp04path1P4vals3HPr2HL3HhiS3sp04path1P4vals2HP3HPr2HLS3sp04SPhi4path4vals2HLS3sp04SPlo4SPhi4path4vals2HLS3sp04SPlo4SPhi4path4vals2HL". (* [comment removed for export] *)
  #[using="Hvsp Hh Hlazy SPlo SPhi"] Lemma of_segF_gen : ltac2:(CDefT.buildp (gd_tbl_P_mainleaf_openfail_tail ()) "Ppath,(0.(1.&8.))Ppp,(1.&40.)PP,$1:.PT,$2<.Pvals,(0.(1.&40.))PR,(2.&5.(1.&40.))PM,P,(1.&40.)(3.(1.&8.))P,(4.$1:.(1;.(6.(1.&8.)R7.))R5.)P,(1<.(1=.=R6.)(1=.R6.+3?.))P,(4.$5.(6.(1.&40.)R5.)#:7.)P,(4.(1.&40.)(7.R6.#0.)Vsp0,)P,(4.(1.&40.)(7.R7.#2.)R:.)P,(4.(1.&40.)(7.R8.#71.)(12.&40.R:.))P,(1=.(22.&40.Vsp0,)(22.&40.R<.))P,(1=.(24.(24.(22.&40.R=.)R<.)+8.)(24.(22.&40.Vsp0,)+400000.))P,(8.(9.R;.)$2=.R:.)P,(;.$<.(9.R<.)R:.$2>.)P,(4.(3.(0.(1.&8.)))(20.$<.R;.R10.(2?.(6.(1.&8.)R11.)#1.))(23.(0.(1.&8.))(17.(1.&8.)R11.(25.(1.&8.)(12.&8.=)(26.(1.&8.))))))P,(30.R12.R10.R?.)(>.$<.(?.(10.$11.R>.(12.&40.+41=64.)R=.(13.$<.))Vmodel,)R10.)")
(* [comment removed for export] *).
  Proof.
    intros path pp P T vals R M HP HPr HL P0 P2 P113 Hpp1 Hpp2 HR HK Hstr HG0.
    pose proof SPlo as Hlo. pose proof SPhi as Hhi.
    assert (Psmall : (bv_unsigned (edenot (ENV vals) PX) < 2 ^ 31)%Z).
    { cbn [edenot ev ENV PX]. rewrite P113, u_small by lia. lia. }
    unfold PX in Psmall.
    (* [comment removed for export] *)
    run_blk_keep scrF 167%nat.
    { (* [comment removed for export] *)
      unfold sc_denot. cbn [branch_taken]. ed_lin ltac:(cbn [ev ENV]; rewrite ?P113).
      rewrite ltu_ZZ by lia. cbn [negb]. rewrite (proj2 (Z.ltb_ge _ _)) by lia. reflexivity. }
    { (* [comment removed for export] *)
      unfold sc_denot. cbn [branch_taken].
      rewrite (edenot_exts4 _ _ Psmall), !(edenot_addw0_r _ _) by (rewrite ?edenot_addw0_r by exact Psmall; exact Psmall).
      unfold bv_lts. rewrite Z.ltb_irrefl. reflexivity. }
    assert (WOKS : win_ok (ENV vals) 0 0 4194304 IHI).
    { unfold win_ok, IHI. cbn [ev ENV]. rewrite P0. lia. }
    assert (Hstr' : rdn RSEGS M0 pp (length path + 1) = Some (path ++ [Z_to_bv 8 0])).
    { rewrite EQM, (rdn_mem_denot_out RSEGS (ENV vals) M _ 0 0 4194304 IHI);
        [exact Hstr | vm_compute; reflexivity | exact WOKS | cbn [ev ENV]; rewrite P0; lia
        | cbn [ev ENV]; rewrite P0; lia]. }
    clear EQM Hstr. rename M0 into M'.
    (* [comment removed for export] *)
    set (dst := Z_to_bv 64 (bv_unsigned sp0 - 543)).
    assert (Hsrc : rdn RSEGS M' pp (length path) = Some path).
    { rewrite <- (firstn_app_l _ path [Z_to_bv 8 0]) at 2 || idtac.
      replace path with (firstn (length path) (path ++ [Z_to_bv 8 0])) at 2
        by (rewrite firstn_app, firstn_all, Nat.sub_diag; cbn [firstn]; apply app_nil_r).
      eapply rdn_firstn; [exact Hstr' | lia]. }
    assert (Hdst : store_ok RSEGS M' dst (length path) = true).
    { pose proof (kwr_store_ok RSEGS (ENV vals) _ knF ltac:(let i := kidx knF (is_kwr_cov (EVar 0) (-543) 63) in exact i)
                    _ _ _ (-543) (length path) HK eq_refl ltac:(lia) ltac:(cbn; lia)) as Hst.
      unfold adenot, v_addi in Hst. cbn [a_base a_off edenot ev ENV] in Hst. rewrite P0 in Hst.
      subst dst. replace (bv_unsigned sp0 - 543)%Z with (bv_unsigned sp0 + -543)%Z by lia. exact Hst. }
    assert (MC : mcH M' dst pp P path).
    { constructor; subst dst; rewrite ?u_small by lia; try lia.
      - exact Hsrc.
      - exact Hdst. }
    lazymatch goal with |- realizes _ (mkCfg (mkst ?Rc _ _ _) _) _ =>
      assert (A1 : getr Rc 1 = (0x41d64 : word)) by (regv HR (1 : reg); apply bv_eq; reflexivity);
      assert (A10 : getr Rc 10 = dst)
        by (regv HR (10 : reg); subst dst; ed_lin ltac:(cbn [ev ENV]; rewrite ?P0); f_equal; lia);
      assert (A11 : getr Rc 11 = pp) by (regv HR (11 : reg); cbn [edenot ev ENV]; exact P2);
      assert (A12 : getr Rc 12 = Z_to_bv 64 P) by (regv HR (12 : reg); cbn [edenot ev ENV]; exact P113);
      destruct (ref_memcpy M' dst pp P _ (seg_rom RSEGS) MC Rc (0x41d64 : word)
                  ltac:(apply ret_ok_even; reflexivity) A1 A10 A11 A12) as (R2 & Hms & Hkeep);
      clear A1 A10 A11 A12
    end.
    replace (Z_to_bv 64 289344) with (0x46a40 : word) by (apply bv_eq; reflexivity).
    eapply rz_msteps; [exact Hh | exact Hlazy | exact Hms |]. clear Hms.
    replace (0x41d64 : word) with (Z_to_bv 64 0x41d64) by (apply bv_eq; reflexivity).
    (* [comment removed for export] *)
    lazymatch type of HR with regs_ok ?E ?sr ?Rc =>
      pose proof (regs_after_keeps vals (blobs_ev BL) sr Rc R2 callee_kept
                    ltac:(rewrite HL; vm_compute; reflexivity) HR Hkeep callee_kept_no0) as HR2 end.
    rewrite HL in HR2. clear HR Hkeep. rename HR2 into HR.
    (* [comment removed for export] *)
    pose proof (know_cut_sound RSEGS (ENV vals) M' (wbytes M' dst path) 0 (-543) BUF_HI IHI knF
                  ltac:(unfold win_ok, BUF_HI, IHI; cbn [ev ENV]; rewrite P0; lia)
                  ltac:(apply (wbytes_agree_out M' dst path (ENV vals) 0 (-543) BUF_HI);
                        cbn [ev ENV]; rewrite P0; subst dst; unfold BUF_HI; rewrite ?u_small by lia; lia)
                  (wbytes_grows _ _ _) HK) as HK2.
    clear HK. change (kn_cut 0 (-543) BUF_HI IHI knF) with knG0 in HK2.
    pose proof (env_app_know RSEGS vals (junk_vals R2) (blobs_ev BL) _ knG0 ltac:(rewrite HL; vm_compute; reflexivity) HK2) as HK.
    clear HK2.
    set (vals1 := vals ++ junk_vals R2) in *.
    assert (HL1 : length vals1 = 199%nat) by (subst vals1; rewrite length_app, junk_vals_length, HL; reflexivity).
    assert (Q0 : vals_ev vals1 0 = sp0) by (subst vals1; rewrite vals_ev_app_l by (rewrite HL; lia); exact P0).
    assert (Q113 : vals_ev vals1 113 = Z_to_bv 64 P) by (subst vals1; rewrite vals_ev_app_l by (rewrite HL; lia); exact P113).
    clearbody vals1.
    change (Env (vals_ev vals1) (blobs_ev BL)) with (ENV vals1) in HR, HK.
    eapply (HG0 vals1); try eassumption.
    (* [comment removed for export] *)
    subst dst. rewrite <- HP at 1 || idtac.
    pose proof (rdn_wbytes_hit RSEGS path M' (Z_to_bv 64 (bv_unsigned sp0 - 543))) as Hc.
    apply Hc. rewrite u_small by lia. lia.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  Local Ltac2 Set LiaOrc.tbl := fun () => "0010?L66345289113.2600000DS4path1P4vals3HPr2HL". (* [comment removed for export] *)
  #[using="Hvsp Hh Hlazy Hfd2 SPlo SPhi"] Lemma of_segF : ltac2:(CDefT.buildp (gd_tbl_P_mainleaf_openfail_tail ()) "Ppath,(0.(1.&8.))Ppp,(1.&40.)PP,$1:.Pvals,(0.(1.&40.))PR,(2.&5.(1.&40.))PM,P,(1.&40.)(3.(1.&8.))P,(4.$1:.(1;.(6.(1.&8.)R6.))R4.)P,(1<.(1=.=R5.)(1=.R5.+3>.))P,(4.$5.(6.(1.&40.)R5.)#:7.)P,(4.(1.&40.)(7.R6.#0.)Vsp0,)P,(4.(1.&40.)(7.R7.#2.)R9.)P,(4.(1.&40.)(7.R8.#71.)(12.&40.R9.))P,(1=.(22.&40.Vsp0,)(22.&40.R;.))P,(1=.(24.(24.(22.&40.R<.)R;.)+8.)(24.(22.&40.Vsp0,)+400000.))P,(8.(9.R;.)$2=.R:.)P,(;.$<.(9.R<.)R:.$2>.)P,(4.(3.(0.(1.&8.)))(20.$<.R;.R?.(2?.(6.(1.&8.)R10.)#1.))(23.(0.(1.&8.))(17.(1.&8.)R10.(25.(1.&8.)(12.&8.=)(26.(1.&8.))))))(>.$<.(?.(10.$11.R=.(12.&40.+41=64.)R<.(13.$<.))Vmodel,)(27.(28.+2.(29.R11.))(14.(15.+2.)(16.Vmodel,))))")
(* [comment removed for export] *).
  Proof.
    intros path pp P vals R M HP HPr HL P0 P2 P113 Hpp1 Hpp2 HR HK Hstr.
    eapply (of_segF_gen path pp P _ vals); try eassumption; [lia|].
    intros vals' R' M' HL' Q0 Q113 HR' HK' SB. eapply (of_segG path P vals'); eassumption.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  Definition atF0 (path : list byte) (pp : word) (P : Z) (T : TSet) : Prop := ltac2:(CDefT.buildp (gd_tbl_P_mainleaf_openfail_tail ()) "Pvals,(0.(1.&40.))PR,(2.&5.(1.&40.))PM,P,(1.&40.)(3.(1.&8.))P,(4.$5.(6.(1.&40.)R3.)#:7.)P,(4.(1.&40.)(7.R4.#0.)Vsp0,)P,(4.(1.&40.)(7.R5.#2.)O3.)P,(4.(1.&40.)(7.R6.#71.)(12.&40.O2.))P,(8.(9.R7.)$2=.R6.)P,(;.$<.(9.R8.)R6.$2>.)P,(4.(3.(0.(1.&8.)))(20.$<.R7.O3.(2?.(6.(1.&8.)O4.)#1.))(23.(0.(1.&8.))(17.(1.&8.)O4.(25.(1.&8.)(12.&8.=)(26.(1.&8.))))))(>.$<.(?.(10.$11.R9.(12.&40.+41=64.)R8.(13.$<.))Vmodel,)O1.)")
(* [comment removed for export] *).

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  Local Ltac2 Set LiaOrc.tbl := fun () => "0190?L10309899295.43L10742216961.46L11664407159.51L11666905584.43L11879121292.40L14307436141.40L18335669935.40L18534106001.41L19072480109.37L19072480109.47L1954334414.40 L19963725408.52L24077028727.37L24078750703.51L24078821722.39L24078821722.40L24087004302.44L25612613803.45L25612713248.39L25614647967.41L28378693749.44L29378782958.46L30224815626.47L30224815627.50L30226819466.40L31154219891.40L31227397377.44L31227520582.40L31319394225.37L31319394225.47L314458845.52  L34301895276.52L34301897727.47L35159558105.40L36474080581.44L37371372047.38L3851856731.46 L40197912676.40L42116375652.43L43363525287.47L43363527476.52L45050765751.46L48227411914.47L48227413593.52L48282155559.46L49030424061.46L51306172107.46L53504481175.46L54441416810.49L54441515114.52L54467711090.41L54845076111.44L54853263195.39L54856104822.37L55890242748.45L55892356284.40L56277679942.46L57406519004.52L57406521167.47L58833951326.51L64162542827.51L64162575595.48L64775433197.38L65141012212.47L65141014375.52L65341309917.37L67697006827.44L67705075007.39L8532453019.38 L9271624767.40 L9348852209.33 L9359554572.47 L9361438865.46 00000N00f01D01b02002D02^03703Q04504O05A05d06Q07:07c08P08h09<09P09g0:H0:]0;<0;P0<90<U0=10=P0>90>f0?O0?f0@80@R0@n0AJ0B00BI0B`0CF0C^0D50D[0EA0EY0EZ0F20FG0Ff0GB0Gb0H>0HT0I70I`0Ia0JG0J^0K<0K[0L00LO0Lf0ML0MZ0N20NF0O20O@0O\0PB0P^S4path1P4vals3HPr2HL5vals13HL1S4path4vals2HL5vals13HL1S4path1P4vals3HPr2HL5vals13HL1S4path1P4vals3HPr2HL5vals13HL1S4path4vals2HLS4path2t84vals2HL2L8S4path1P2t84vals3HPr2HL2L8S4path2pp1P2t84vals2HL2L8S3sp04path2pp4vals2HL4Hpp1S3sp04path2pp4vals2HL4Hpp15vals13HL1S4path1P2t84vals3HPr2HL2L8S3sp04path2pp1P4vals2HP2HL4Hpp23Hhi5vals13HL11i2HiS3sp04path2pp1P4vals2HP2HL4Hpp23HhiS3sp04path2pp1P4vals2HP2HL4Hpp23Hhi5vals13HL1S3sp04path2pp1P2t84vals2HP2HL4Hpp23Hhi2L8S3sp04path2pp1P2t84vals2HP2HL4Hpp23Hhi2L8S3sp04path2pp1P4vals2HP2HL4Hpp23Hhi5vals13HL1S4path4vals2HL5vals13HL1S4path2t84vals2HL2L8S4path2t84vals2HL2L8S3sp04SPlo4path4vals2HLS3sp04SPhi4path4vals2HL5vals13HL1S4path4vals2HL2R23HL1S4path4vals2HL5vals13HL12R43HL2S4path2t84vals2HL2L8S3sp04path2pp1P2t84vals2HP2HL4Hpp13Hlo2L8S3sp04SPlo4SPhi4path4vals2HLS3sp04SPlo4SPhi4path4vals2HLS3sp04path2pp1P4vals2HP2HL4Hpp2S3sp04path2pp1P4vals2HP2HL4Hpp25vals13HL1S3sp04path2pp4vals2HL4Hpp13Hlo5vals13HL11i2HiS3sp04path2pp4vals2HL4Hpp15vals13HL11i2HiS3sp04path4vals2HL1x2HxS3sp04path4vals2HLS3sp04path2pp4vals2HL4Hpp1S3sp04path2pp1P4vals2HL4Hpp2S3sp04path4vals2HL5vals13HL1S3sp04path2pp1P2t84vals2HL4Hpp23Hhi2L8S4path2t84vals2HL2L81i2HiS3sp04SPhi4path4vals2HLS3sp04SPhi4path4vals2HL5vals13HL11i2HiS4path4vals2HL5vals13HL1S3sp04SPlo4path4vals2HLS3sp04SPlo4path4vals2HL5vals13HL11i2HiS3sp04SPlo4SPhi4path4vals2HL5vals13HL1S4path4vals2HL5vals13HL1FS4path4vals2HL5vals13HL1S4path4vals2HL2R23HL1S4path4vals2HL5vals13HL12R43HL2S4path2pp1P2t84vals2HP2HL2L8S4path2pp4vals2HL4Hppr5vals13HL1S4path2pp2t84vals2HL4Hppr2L8S4path2pp4vals2HL4HpprS3sp04path2pp1P4vals2HP2HL4Hpp13HloS3sp04path2pp1P2t84vals2HP2HL4Hpp13Hlo2L8FS3sp04SPlo4path4vals2HL5vals13HL11i2HiS3sp04SPlo4path4vals2HLS4path1P4vals3HPr2HL5vals13HL1S4path4vals2HL5vals13HL12R43HL2S4path4vals2HL2R23HL1S3sp04path2pp1P4vals2HP2HL4Hpp1S3sp04SPhi4path4vals2HLS3sp04SPhi4path4vals2HL5vals13HL11i2HiS4path4vals2HLS4path4vals2HL5vals13HL1S4path2t84vals2HL2L8S3sp04path2pp1P4vals2HP2HL4Hpp14Hpp23Hlo3HhiS4path4vals2HLS3sp04SPlo4SPhi4path4vals2HLS3sp04SPlo4SPhi4path4vals2HL5vals13HL1S3sp04SPlo4SPhi4path4vals2HL". (* [comment removed for export] *)
  #[using="Hvsp Hh Hlazy SPlo SPhi"] Lemma of_segDE : ltac2:(CDefT.buildp (gd_tbl_P_mainleaf_openfail_tail ()) "Ppath,(0.(1.&8.))Ppp,(1.&40.)PP,$1:.PT,$2<.Pt8,(0.(1.&8.))Pvals,(0.(1.&40.))PR,(2.&5.(1.&40.))PM,P,(1.&40.)(3.(1.&8.))P,(4.$1:.(1;.(6.(1.&8.)R8.))R6.)P,(1<.(1=.=R7.)(1=.R7.+1????.))P,(31.(32.(1.&8.)(12.&8.=)R:.))P,(4.$5.(6.(1.&40.)R6.)#67.)P,(4.(1.&40.)(7.R7.#0.)Vsp0,)P,(4.(1.&40.)(7.R8.#2.)R<.)P,(1=.(22.&40.Vsp0,)(22.&40.R=.))P,(1=.(24.(24.(22.&40.R>.)R=.)+8.)(24.(22.&40.Vsp0,)+400000.))P,(8.(9.R;.)$33.R:.)P,(;.$<.(9.R<.)R:.$34.)P,(4.(3.(0.(1.&8.)))(20.$<.R;.R11.(2?.(6.(1.&8.)R12.)#1.))(23.(0.(1.&8.))(17.(1.&8.)R12.(25.(1.&8.)(12.&8.=)(26.(1.&8.))))))P,(4.(3.(0.(1.&8.)))(20.$<.R<.(12.&40.(24.(22.&40.R12.)R11.))#8.)(23.(0.(1.&8.))R?.))P,(35.R14.R13.R12.R11.)(>.$<.(?.(10.$11.R?.(12.&40.+41=64.)R>.(13.$<.))Vmodel,)R12.)")
(* [comment removed for export] *).
  Proof.
    intros path pp P T t8 vals R M HP HPr Hnonul HL P0 P2 Hpp1 Hpp2 HR HK Hstr Ht8 HF0.
    pose proof SPlo as Hlo. pose proof SPhi as Hhi. pose proof (u64_range pp) as Hppr.
    assert (WOKS : win_ok (ENV vals) 0 0 4194304 IHI).
    { unfold win_ok, IHI. cbn [ev ENV]. rewrite P0. lia. }
    (* [comment removed for export] *)
    run_blk_keep scr0 103%nat.
    assert (Hstr' : rdn RSEGS M0 pp (length path + 1) = Some (path ++ [Z_to_bv 8 0])).
    { rewrite EQM, (rdn_mem_denot_out RSEGS (ENV vals) M _ 0 0 4194304 IHI);
        [exact Hstr | vm_compute; reflexivity | exact WOKS | cbn [ev ENV]; rewrite P0; lia | cbn [ev ENV]; rewrite P0; lia]. }
    assert (Ht8' : rdn RSEGS M0 (Z_to_bv 64 (bv_unsigned pp + P)) 8 = Some t8).
    { rewrite EQM, (rdn_mem_denot_out RSEGS (ENV vals) M _ 0 0 4194304 IHI);
        [exact Ht8 | vm_compute; reflexivity | exact WOKS | cbn [ev ENV]; rewrite P0, u_small by lia; lia
        | cbn [ev ENV]; rewrite P0, u_small by lia; lia]. }
    clear EQM Hstr Ht8. rename M0 into M'.
    (* [comment removed for export] *)
    set (spS := Z_to_bv 64 (bv_unsigned sp0 - 1120)).
    assert (Hbuf : rdn RSEGS M' pp (length (path ++ t8)) = Some (path ++ t8)).
    { rewrite length_app. rewrite (word_Z pp). apply rdn_app_Z; [ | | lia | lia].
      - rewrite <- (word_Z pp). replace path with (firstn (length path) (path ++ [Z_to_bv 8 0])) at 2
          by (rewrite firstn_app, firstn_all, Nat.sub_diag; cbn [firstn]; apply app_nil_r).
        eapply rdn_firstn; [exact Hstr' | lia].
      - pose proof (rdn_length _ _ _ _ _ Ht8') as L8. rewrite L8, HP. exact Ht8'. }
    assert (Hz : nth (length path) (path ++ t8) (Z_to_bv 8 0) = Z_to_bv 8 0).
    { pose proof (rdn_length _ _ _ _ _ Ht8') as L8.
      rewrite app_nth2, Nat.sub_diag by lia.
      pose proof (rdn_byte_Z RSEGS M' (bv_unsigned pp) (length path + 1) _ (length path)
                    ltac:(rewrite <- (word_Z pp); exact Hstr') ltac:(lia) ltac:(lia) ltac:(lia)) as B1.
      pose proof (rdn_byte_Z RSEGS M' (bv_unsigned pp + P) 8 t8 0 Ht8' ltac:(lia) ltac:(lia) ltac:(lia)) as B2.
      replace (bv_unsigned pp + Z.of_nat (length path))%Z with (bv_unsigned pp + P)%Z in B1 by lia.
      replace (bv_unsigned pp + P + Z.of_nat 0)%Z with (bv_unsigned pp + P)%Z in B2 by lia.
      rewrite B1 in B2. injection B2 as E. rewrite <- E. rewrite app_nth2, Nat.sub_diag by lia. reflexivity. }
    assert (MC : mchrH M' pp (path ++ t8) P 0x7fffffff).
    { pose proof (rdn_length _ _ _ _ _ Ht8') as L8.
      constructor.
      - exact Hbuf.
      - rewrite length_app, L8.
        Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
        lia.
        Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
      - rewrite length_app, L8. lia.
      - lia.
      - rewrite <- HP, Nat2Z.id, Hz. reflexivity.
      - intros j Hj. rewrite <- HP, Nat2Z.id in Hj. rewrite nth_app_l by exact Hj.
        intros E. apply (In_nth_neq path (Z_to_bv 8 0) (Z_to_bv 8 0) j Hnonul Hj). apply bv_eq. exact E.
      - lia.
      - lia.
      - intros i Hi.
        pose proof (know_nth RSEGS _ _ knD ltac:(let k := kidx knD (is_kimg_cov 0x10c30 24) in exact k) _ HK eq_refl)
          as (_ & _ & Hnone). apply Hnone. lia. }
    assert (Hstk : store_ok RSEGS M' (Z_to_bv 64 (bv_unsigned spS - 32)) 32 = true).
    { pose proof (kwr_store_ok RSEGS (ENV vals) _ knD ltac:(let i := kidx knD (is_kwr_cov (EVar 0) (-1152) 32) in exact i)
                    _ _ _ (-1152) 32 HK eq_refl ltac:(lia) ltac:(cbn; lia)) as Hst.
      unfold adenot, v_addi in Hst. cbn [a_base a_off edenot ev ENV] in Hst. rewrite P0 in Hst.
      subst spS. rewrite u_small by lia.
      replace (bv_unsigned sp0 - 1120 - 32)%Z with (bv_unsigned sp0 + -1152)%Z by lia. exact Hst. }
    lazymatch goal with |- realizes _ (mkCfg (mkst ?Rc _ _ _) _) _ =>
      assert (A1 : getr Rc 1 = (0x42748 : word)) by (regv HR (1 : reg); apply bv_eq; reflexivity);
      assert (A2 : getr Rc 2 = spS)
        by (regv HR (2 : reg); subst spS; ed_lin ltac:(cbn [ev ENV]; rewrite ?P0); f_equal; lia);
      assert (A10 : getr Rc 10 = pp) by (regv HR (10 : reg); cbn [edenot ev ENV]; exact P2);
      assert (A11 : getr Rc 11 = Z_to_bv 64 0x7fffffff) by (regv HR (11 : reg); reflexivity);
      ddestruct (ref_strnlen M' pp spS (path ++ t8) P 0x7fffffff (seg_rom RSEGS) Rc (0x42748 : word) MC
                  ltac:(lia) Hstk ltac:(subst spS; rewrite u_small by lia; lia)
                  ltac:(right; subst spS; rewrite u_small by lia; lia)
                  ltac:(apply ret_ok_even; reflexivity) A1 A2 A10 A11) as (R2 & M2 & Hms & Hkeep & HresP & Hfr);
      clear A1 A2 A10 A11
    end.
    replace (Z_to_bv 64 290620) with (0x46f3c : word) by (apply bv_eq; reflexivity).
    eapply rz_msteps; [exact Hh | exact Hlazy | exact Hms |]. clear Hms.
    replace (0x42748 : word) with (Z_to_bv 64 0x42748) by (apply bv_eq; reflexivity).
    (* [comment removed for export] *)
    lazymatch type of HR with regs_ok ?E ?sr ?Rc =>
      pose proof (regs_after_keeps vals (blobs_ev BL) sr Rc R2 callee_saved
                    ltac:(rewrite HL; vm_compute; reflexivity) HR Hkeep callee_saved_no0) as HR2 end.
    rewrite HL in HR2. clear HR Hkeep. rename HR2 into HR.
    (* [comment removed for export] *)
    destruct Hfr as [Hagree Hgrow].
    pose proof (know_cut_sound RSEGS (ENV vals) M' M2 0 (-1152) (-1120) IHI knD
                  ltac:(unfold win_ok, IHI; cbn [ev ENV]; rewrite P0; lia)
                  ltac:(intros x Hx; apply Hagree; cbn [outside]; split; [|exact I];
                        unfold in_rng; subst spS; unorm;
                        cbn [ev ENV] in Hx; rewrite P0 in Hx; lia)
                  Hgrow HK) as HK2.
    clear HK.
    pose proof (env_app_know RSEGS vals (junk_vals R2) (blobs_ev BL) M2 (kn_cut 0 (-1152) (-1120) IHI knD)
                  ltac:(rewrite HL; vm_compute; reflexivity) HK2) as HK3.
    clear HK2.
    set (vals1 := vals ++ junk_vals R2) in *.
    assert (HL1 : length vals1 = 135%nat) by (subst vals1; rewrite length_app, junk_vals_length, HL; reflexivity).
    assert (Q0 : vals_ev vals1 0 = sp0) by (subst vals1; rewrite vals_ev_app_l by (rewrite HL; lia); exact P0).
    assert (Q2 : vals_ev vals1 2 = pp) by (subst vals1; rewrite vals_ev_app_l by (rewrite HL; lia); exact P2).
    assert (Q113 : vals_ev vals1 113 = Z_to_bv 64 P).
    { subst vals1. change 113%nat with (103 + 10)%nat. rewrite <- HL. rewrite vals_ev_junk by lia. exact HresP. }
    clearbody vals1.
    change (Env (vals_ev vals1) (blobs_ev BL)) with (ENV vals1) in HR, HK3.
    assert (HK : know_ok RSEGS (ENV vals1) M2 knE0).
    { unfold knE0. apply know_ok_cons; [|exact HK3].
      apply krange_intro. cbn [edenot ev ENV PX]. rewrite Q113, u_small by lia. lia. }
    clear HK3.
    (* [comment removed for export] *)
    assert (Hstr2 : rdn RSEGS M2 pp (length path + 1) = Some (path ++ [Z_to_bv 8 0])).
    { rewrite (frame_mod_rdn RSEGS M' M2 _ _ pp (conj Hagree Hgrow)); [exact Hstr' | | lia].
      intros i Hi. cbn [outside]. split; [|exact I]. unfold in_rng. subst spS. unorm. lia. }
    clear Hstr' Ht8' Hbuf Hz MC Hstk Hagree Hgrow HresP.
    assert (Psmall : (bv_unsigned (edenot (ENV vals1) (EVar 113)) < 2 ^ 31)%Z).
    { cbn [edenot ev ENV]. rewrite Q113, u_small by lia. lia. }
    (* [comment removed for export] *)
    run_blk_keep scrE 135%nat.
    { (* [comment removed for export] *)
      unfold sc_denot. cbn [branch_taken]. rewrite (edenot_addw0_r _ _ Psmall).
      unfold bv_lts. rewrite Z.ltb_irrefl. reflexivity. }
    { (* [comment removed for export] *)
      unfold sc_denot. exists [Z_to_bv 8 0]. split.
      - unfold adenot, v_addi. cbn [a_base a_off]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned.
        ed_lin ltac:(cbn [ev ENV]; rewrite ?Q2, ?Q113). rewrite <- HP.
        pose proof (rdn_byte_Z RSEGS M2 (bv_unsigned pp) (length path + 1) _ (length path)
                      ltac:(rewrite <- (word_Z pp); exact Hstr2) ltac:(lia) ltac:(lia) ltac:(lia)) as B1.
        rewrite app_nth2, Nat.sub_diag in B1 by lia. cbn [nth] in B1. exact B1.
      - reflexivity. }
    assert (Hstr3 : rdn RSEGS M0 pp (length path + 1) = Some (path ++ [Z_to_bv 8 0])).
    { rewrite EQM, (rdn_mem_denot_out RSEGS (ENV vals1) M2 _ 0 0 4194304 IHI);
        [exact Hstr2 | vm_compute; reflexivity | unfold win_ok, IHI; cbn [ev ENV]; rewrite Q0; lia
        | cbn [ev ENV]; rewrite Q0; lia | cbn [ev ENV]; rewrite Q0; lia]. }
    clear EQM Hstr2. rename M0 into M3.
    (* [comment removed for export] *)
    set (dst := Z_to_bv 64 (bv_unsigned sp0 - 543)).
    assert (MC : mcH M3 dst (Z_to_bv 64 0x102a5) 0 []).
    { constructor; subst dst; rewrite ?u_small by lia; cbn [length]; try lia; reflexivity. }
    lazymatch goal with |- realizes _ (mkCfg (mkst ?Rc _ _ _) _) _ =>
      assert (A1 : getr Rc 1 = (0x41d64 : word)) by (regv HR (1 : reg); apply bv_eq; reflexivity);
      assert (A10 : getr Rc 10 = dst)
        by (regv HR (10 : reg); subst dst; ed_lin ltac:(cbn [ev ENV]; rewrite ?Q0); f_equal; lia);
      assert (A11 : getr Rc 11 = Z_to_bv 64 0x102a5) by (regv HR (11 : reg); reflexivity);
      assert (A12 : getr Rc 12 = Z_to_bv 64 0) by (regv HR (12 : reg); reflexivity);
      destruct (ref_memcpy M3 dst (Z_to_bv 64 0x102a5) 0 _ (seg_rom RSEGS) MC Rc (0x41d64 : word)
                  ltac:(apply ret_ok_even; reflexivity) A1 A10 A11 A12) as (R4 & Hms & Hkeep);
      clear A1 A10 A11 A12
    end.
    replace (Z_to_bv 64 289344) with (0x46a40 : word) by (apply bv_eq; reflexivity).
    eapply rz_msteps; [exact Hh | exact Hlazy | exact Hms |]. clear Hms.
    change (wbytes M3 dst []) with M3.
    replace (0x41d64 : word) with (Z_to_bv 64 0x41d64) by (apply bv_eq; reflexivity).
    lazymatch type of HR with regs_ok ?E ?sr ?Rc =>
      pose proof (regs_after_keeps vals1 (blobs_ev BL) sr Rc R4 callee_kept
                    ltac:(rewrite HL1; vm_compute; reflexivity) HR Hkeep callee_kept_no0) as HR2 end.
    rewrite HL1 in HR2. clear HR Hkeep. rename HR2 into HR.
    pose proof (env_app_know RSEGS vals1 (junk_vals R4) (blobs_ev BL) M3 knE ltac:(rewrite HL1; vm_compute; reflexivity) HK) as HK2.
    clear HK. rename HK2 into HK.
    set (vals2 := vals1 ++ junk_vals R4) in *.
    assert (HL2 : length vals2 = 167%nat) by (subst vals2; rewrite length_app, junk_vals_length, HL1; reflexivity).
    assert (W0 : vals_ev vals2 0 = sp0) by (subst vals2; rewrite vals_ev_app_l by (rewrite HL1; lia); exact Q0).
    assert (W2 : vals_ev vals2 2 = pp) by (subst vals2; rewrite vals_ev_app_l by (rewrite HL1; lia); exact Q2).
    assert (W113 : vals_ev vals2 113 = Z_to_bv 64 P) by (subst vals2; rewrite vals_ev_app_l by (rewrite HL1; lia); exact Q113).
    clearbody vals2.
    change (Env (vals_ev vals2) (blobs_ev BL)) with (ENV vals2) in HR, HK.
    eapply (HF0 vals2); eassumption.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  #[using="Type"] Lemma pre17_img : rdn RSEGS (fun _ => None) (Z_to_bv 64 0x10839) 17 = Some PRE17.
  Proof. vm_compute. reflexivity. Qed.

  #[using="Type"] Lemma PRE17_len : length PRE17 = 17%nat.
  Proof. reflexivity. Qed.

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0070?L37504097574.14L38475949454.14L38803581625.14L45527366623.14L64238114748.14L65069231746.14L66445618183.1400000500:00D00E00O00Y00cS3sp0S3sp0S3sp04SPloFS3sp04SPhiS3sp04SPhiS3sp04SPlo". (* [comment removed for export] *)
  #[using="Hvsp SPlo SPhi"] Lemma memcpy1_denot : ltac2:(CDefT.buildp (gd_tbl_P_mainleaf_openfail_tail ()) "Pvals,(0.(1.&40.))PM,P,(1.&40.)(3.(1.&8.))P,(4.(1.&40.)(7.R2.#0.)Vsp0,)(4.P,(1.&40.)(3.(1.&8.))(36.(9.R3.)R2.$37.)(38.R2.(12.&40.(21.(22.&40.Vsp0,)+230.))$19.))")
(* [comment removed for export] *).
  Proof.
    intros vals M P0. pose proof SPlo. pose proof SPhi.
    rewrite <- PRE17_words. cbn [mem_denot logM1]. rewrite !wbytes_app.
    unfold adenot, v_addi, at_. cbn [a_base a_off edenot ev ENV length Z.of_nat Pos.of_succ_nat Pos.succ]. rewrite P0.
    rewrite !length_N_to_le_bytes. cbn [Z.of_nat Pos.of_succ_nat Pos.succ]. unorm.
    repeat (f_equal; try (f_equal; lia)).
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  Local Ltac2 Set LiaOrc.tbl := fun () => "0150?L12243364600.42L14415977306.42L16967776984.47L19072480109.39L19072480109.47L19480113726.39L23364498358.46L23892179444.40L24078642256.46L25271808757.42L27463909009.40L29380870382.46L30056746828.36L30224815626.44L30224815627.50L30454599770.42L31319394225.39L31319394225.47L31378304330.40L32860873099.42L33669197954.42L34024036933.47L37371372047.40L37371372051.48L38057172332.40L38767783414.40L38882466827.42L38910230927.36L39489673143.46L40438911199.40L41493379704.42L43459505280.40L44909841035.42L44993770998.40L4636064337.46 L48284245031.46L49028318205.46L5106095775.36 L51308275915.46L51700226936.42L53012581002.40L53506584983.46L54646596486.36L55093830608.40L55894544189.47L56668139067.46L5926759515.42 L61369196286.39L6387091162.42 L64162542827.51L64162575595.45L64223442366.47L64238229182.46L64775433197.40L64775433201.48L65069117312.46L65071320192.47L66264185478.47L66445241605.46L66447707653.47L66643383483.40L68059071289.42L8532452999.48 L8532453019.40 L9095194694.40 L9262871491.36 L9348844977.43 L9348845041.35 L9540659342.46 00000G00^01H01b02F02T02U02c03P03^03l04M05905N05m06D06c07L07c08:08H09109M0:30:A0:O0:f0;40;L0;Z0<10<C0<Z0<h0=@0=f0>>0>P0>Q0>h0>i0?A0?X0?Y0@F0@b0A00A>0AU0B40BI0Bj0CK0Cj0DS0E40EU0F?0F`0GA0GX0Gf0H\0IH0Id0J60J\0K80K\S3sp04SPhi4path4vals2HLS3sp04SPhi4path4vals2HLS3sp04path2pp1P4vals2HL4Hpp23Hhi5vals13HL1S3sp04path2pp4vals2HL4Hpp1S3sp04path2pp4vals2HL4Hpp15vals13HL1S4path4vals2HLFS4path4vals2HLS3sp04path2pp1P4vals2HP2HL4Hpp23Hhi5vals13HL1S4path4vals2HLS4path4vals2HLS3sp04SPhi4path4vals2HL5vals13HL1S3sp04path2pp1P4vals2HP2HL4Hpp14Hpp23Hlo3HhiS4path4vals2HL2R23HL1S4path4vals2HL5vals13HL12R43HL2S3sp04SPhi4path4vals2HLS3sp04path2pp1P4vals2HP2HL4Hpp2S3sp04path2pp1P4vals2HP2HL4Hpp25vals13HL1S3sp04SPlo4path4vals2HLS3sp04SPlo4path4vals2HLS4path4vals2HLS3sp04path2pp1P4vals2HP2HL4Hpp15vals13HL1S3sp04path2pp1P4vals2HL4Hpp2S3sp04path2pp1P4vals2HL4Hpp25vals13HL1S4path4vals2HLS4path4vals2HLS3sp04SPlo4path4vals2HLS4path4vals2HLS4path4vals2HL5vals13HL1S4path4vals2HLS3sp04SPhi4path4vals2HLS3sp04path4vals2HLS3sp04SPlo4path4vals2HLS4path4vals2HLS4path4vals2HL5vals13HL1S3sp04SPlo4SPhi4path4vals2HL5vals13HL1S4path4vals2HL5vals13HL1S4path4vals2HL3P38FS3sp04SPhi4path4vals2HLFS4path4vals2HL5vals13HL1S4path4vals2HL3P384H38rFS3sp04path2pp1P4vals2HP2HL4Hpp13Hlo5vals13HL1S3sp04path4vals2HL5vals13HL1S4path4vals2HLS4path4vals2HLS3sp04SPhi4path4vals2HLS4path4vals2HL5vals13HL12R43HL2S4path4vals2HL2R23HL1S3sp04SPhi4path4vals2HL5vals13HL1S3sp04SPhi4path4vals2HL5vals13HL1S3sp04path2pp1P4vals2HP2HL4Hpp1S3sp04path2pp1P4vals2HP2HL4Hpp15vals13HL1S3sp04SPhi4path4vals2HL5vals13HL1S3sp04SPhi4path4vals2HL5vals13HL1S3sp04path2pp1P4vals2HL4Hpp23Hhi5vals13HL1S3sp04SPlo4path4vals2HL5vals13HL1S3sp04SPlo4path4vals2HL5vals13HL1S3sp04SPhi4path4vals2HLS4path4vals2HLS3sp04path2pp1P4vals2HP2HL4Hpp14Hpp23Hlo3Hhi5vals13HL1S3sp04path2pp1P4vals2HP2HL4Hpp14Hpp23Hlo3HhiS3sp04SPlo4SPhi4path4vals2HLS4path4vals2HL3P38S3sp04SPlo4SPhi4path4vals2HL5vals13HL1S3sp04SPlo4SPhi4path4vals2HLS3sp04path2pp4vals2HL4Hpp15vals13HL1". (* [comment removed for export] *)
  #[using="Hvsp Hh Hlazy SPlo SPhi"] Lemma of_segBC : ltac2:(CDefT.buildp (gd_tbl_P_mainleaf_openfail_tail ()) "Ppath,(0.(1.&8.))Ppp,(1.&40.)PP,$1:.PT,$2<.Pt8,(0.(1.&8.))Pvals,(0.(1.&40.))PR,(2.&5.(1.&40.))PM,P,(1.&40.)(3.(1.&8.))P,(4.$1:.(1;.(6.(1.&8.)R8.))R6.)P,(1<.(1=.=R7.)(1=.R7.+1????.))P,(31.(32.(1.&8.)(12.&8.=)R:.))P,(4.$5.(6.(1.&40.)R6.)#27.)P,(4.(1.&40.)(7.R7.#0.)Vsp0,)P,(4.(1.&40.)(7.R8.#2.)R<.)P,(1=.(21.(39.+2.+40.)+???.)(22.&40.(7.R9.#26.)))P,(1=.(22.&40.Vsp0,)(22.&40.R>.))P,(1=.(24.(24.(22.&40.R?.)R>.)+8.)(24.(22.&40.Vsp0,)+400000.))P,(8.(9.R<.)(3:.$3;.(3<.(3=.&5.+:.$3>.))(3?.#26.))R;.)P,(;.$<.(9.R=.)R;.$40.)P,(4.(3.(0.(1.&8.)))(20.$<.R<.R12.(2?.(6.(1.&8.)R13.)#1.))(23.(0.(1.&8.))(17.(1.&8.)R13.(25.(1.&8.)(12.&8.=)(26.(1.&8.))))))P,(4.(3.(0.(1.&8.)))(20.$<.R=.(12.&40.(24.(22.&40.R13.)R12.))#8.)(23.(0.(1.&8.))R10.))P,(35.R15.R14.R13.R12.)(>.$<.(?.(10.$11.R10.(12.&40.+4729<.)R?.(13.$<.))Vmodel,)R13.)")
(* [comment removed for export] *).
  Proof.
    intros path pp P T t8 vals R M HP HPr Hnonul HL P0 P2 P38 Hpp1 Hpp2 HR HK0 Hstr Ht8 HF0.
    pose proof SPlo as Hlo. pose proof SPhi as Hhi. pose proof (u64_range pp) as Hppr.
    pose proof (u64_range (vals_ev vals 38)) as H38r.
    assert (WOKS : win_ok (ENV vals) 0 0 4194304 IHI).
    { unfold win_ok, IHI. cbn [ev ENV]. rewrite P0. lia. }
    assert (HK : know_ok RSEGS (ENV vals) M knB0).
    { unfold knB0. apply know_ok_cons; [|apply know_ok_cons; [|exact HK0]].
      - apply krange_intro. cbn [edenot ev ENV]. rewrite P2. lia.
      - apply krange_intro. cbn [edenot ev ENV]. lia. }
    clear HK0. change (sr_upd srA (ridx 10) (EVar 38)) with srB0 in HR.
    (* [comment removed for export] *)
    run_blk_keep scrB 39%nat.
    { (* [comment removed for export] *)
      unfold sc_denot. cbn [branch_taken]. rewrite edenot_addw0_errno by (cbn [edenot ev ENV]; lia).
      cbn [edenot ev ENV]. unfold bv_ltu. rewrite (u_small 18446744073709547521) by lia.
      apply (proj2 (Z.ltb_ge _ _)). lia. }
    assert (Hstr' : rdn RSEGS M0 pp (length path + 1) = Some (path ++ [Z_to_bv 8 0])).
    { rewrite EQM, (rdn_mem_denot_out RSEGS (ENV vals) M _ 0 0 4194304 IHI);
        [exact Hstr | vm_compute; reflexivity | exact WOKS | cbn [ev ENV]; rewrite P0; lia | cbn [ev ENV]; rewrite P0; lia]. }
    assert (Ht8' : rdn RSEGS M0 (Z_to_bv 64 (bv_unsigned pp + P)) 8 = Some t8).
    { rewrite EQM, (rdn_mem_denot_out RSEGS (ENV vals) M _ 0 0 4194304 IHI);
        [exact Ht8 | vm_compute; reflexivity | exact WOKS | cbn [ev ENV]; rewrite P0, u_small by lia; lia
        | cbn [ev ENV]; rewrite P0, u_small by lia; lia]. }
    clear EQM Hstr Ht8. rename M0 into M'.
    (* [comment removed for export] *)
    set (dst := Z_to_bv 64 (bv_unsigned sp0 - 560)).
    assert (Hsrc : rdn RSEGS M' (Z_to_bv 64 0x10839) 17 = Some PRE17).
    { rewrite (kimg_rdn RSEGS (ENV vals) _ knB ltac:(let i := kidx knB (is_kimg_cov 0x10839 17) in exact i)
                 _ _ 0x10839 17 HK eq_refl) by (cbn; lia). apply pre17_img. }
    assert (Hdst : store_ok RSEGS M' dst 17 = true).
    { pose proof (kwr_store_ok RSEGS (ENV vals) _ knB ltac:(let i := kidx knB (is_kwr_cov (EVar 0) (-560) 17) in exact i)
                    _ _ _ (-560) 17 HK eq_refl ltac:(lia) ltac:(cbn; lia)) as Hst.
      unfold adenot, v_addi in Hst. cbn [a_base a_off edenot ev ENV] in Hst. rewrite P0 in Hst.
      subst dst. replace (bv_unsigned sp0 - 560)%Z with (bv_unsigned sp0 + -560)%Z by lia. exact Hst. }
    assert (MC : mcH M' dst (Z_to_bv 64 0x10839) 17 PRE17).
    { constructor; subst dst; rewrite ?u_small by lia; try (cbn; lia).
      - exact Hsrc.
      - exact Hdst. }
    lazymatch goal with |- realizes _ (mkCfg (mkst ?Rc _ _ _) _) _ =>
      assert (A1 : getr Rc 1 = (0x41d64 : word)) by (regv HR (1 : reg); apply bv_eq; reflexivity);
      assert (A10 : getr Rc 10 = dst)
        by (regv HR (10 : reg); subst dst; ed_lin ltac:(cbn [ev ENV]; rewrite ?P0); f_equal; lia);
      assert (A11 : getr Rc 11 = Z_to_bv 64 0x10839) by (regv HR (11 : reg); reflexivity);
      assert (A12 : getr Rc 12 = Z_to_bv 64 17) by (regv HR (12 : reg); reflexivity);
      destruct (ref_memcpy M' dst (Z_to_bv 64 0x10839) 17 _ (seg_rom RSEGS) MC Rc (0x41d64 : word)
                  ltac:(apply ret_ok_even; reflexivity) A1 A10 A11 A12) as (R2 & Hms & Hkeep);
      clear A1 A10 A11 A12
    end.
    replace (Z_to_bv 64 289344) with (0x46a40 : word) by (apply bv_eq; reflexivity).
    eapply rz_msteps; [exact Hh | exact Hlazy | exact Hms |]. clear Hms.
    replace (0x41d64 : word) with (Z_to_bv 64 0x41d64) by (apply bv_eq; reflexivity).
    lazymatch type of HR with regs_ok ?E ?sr ?Rc =>
      pose proof (regs_after_keeps vals (blobs_ev BL) sr Rc R2 callee_kept
                    ltac:(rewrite HL; vm_compute; reflexivity) HR Hkeep callee_kept_no0) as HR2 end.
    rewrite HL in HR2. clear HR Hkeep. rename HR2 into HR.
    (* [comment removed for export] *)
    assert (HK2 : know_ok RSEGS (ENV vals) (wbytes M' dst PRE17) knC0).
    { subst dst. rewrite <- (memcpy1_denot vals M' P0).
      eapply (carry_after RSEGS (ENV vals) M' logM1 knB [] knC0 [] []);
        [vm_compute; reflexivity | | exact HK | constructor].
      cbn [log_flat logM1].
      repeat match goal with
             | |- flat _ _ _ => apply flat_intro; cbn [edenot ev ENV]; rewrite ?P0; lia
             | |- (_ <= _)%nat => lia
             | |- True => exact I
             | |- _ /\ _ => split
             end. }
    clear HK.
    pose proof (env_app_know RSEGS vals (junk_vals R2) (blobs_ev BL) (wbytes M' dst PRE17) knC0
                  ltac:(rewrite HL; vm_compute; reflexivity) HK2) as HK.
    clear HK2.
    set (vals1 := vals ++ junk_vals R2) in *.
    assert (HL1 : length vals1 = 71%nat) by (subst vals1; rewrite length_app, junk_vals_length, HL; reflexivity).
    assert (Q0 : vals_ev vals1 0 = sp0) by (subst vals1; rewrite vals_ev_app_l by (rewrite HL; lia); exact P0).
    assert (Q2 : vals_ev vals1 2 = pp) by (subst vals1; rewrite vals_ev_app_l by (rewrite HL; lia); exact P2).
    clearbody vals1.
    change (Env (vals_ev vals1) (blobs_ev BL)) with (ENV vals1) in HR, HK.
    (* [comment removed for export] *)
    assert (Hstr2 : rdn RSEGS (wbytes M' dst PRE17) pp (length path + 1) = Some (path ++ [Z_to_bv 8 0])).
    { rewrite rdn_wbytes_out; [exact Hstr' | | |]; subst dst; rewrite ?PRE17_len; unorm; lia. }
    assert (Ht82 : rdn RSEGS (wbytes M' dst PRE17) (Z_to_bv 64 (bv_unsigned pp + P)) 8 = Some t8).
    { rewrite rdn_wbytes_out; [exact Ht8' | | |]; subst dst; rewrite ?PRE17_len; unorm; lia. }
    clear Hstr' Ht8' Hsrc Hdst MC. clearbody dst.
    set (M1 := wbytes M' dst PRE17) in *. clearbody M1. clear M' dst.
    assert (WOKS1 : win_ok (ENV vals1) 0 0 4194304 IHI).
    { unfold win_ok, IHI. cbn [ev ENV]. rewrite Q0. lia. }
    (* [comment removed for export] *)
    run_blk_keep scr0 71%nat.
    assert (Hstr3 : rdn RSEGS M0 pp (length path + 1) = Some (path ++ [Z_to_bv 8 0])).
    { rewrite EQM, (rdn_mem_denot_out RSEGS (ENV vals1) M1 _ 0 0 4194304 IHI);
        [exact Hstr2 | vm_compute; reflexivity | exact WOKS1 | cbn [ev ENV]; rewrite Q0; lia | cbn [ev ENV]; rewrite Q0; lia]. }
    assert (Ht83 : rdn RSEGS M0 (Z_to_bv 64 (bv_unsigned pp + P)) 8 = Some t8).
    { rewrite EQM, (rdn_mem_denot_out RSEGS (ENV vals1) M1 _ 0 0 4194304 IHI);
        [exact Ht82 | vm_compute; reflexivity | exact WOKS1 | cbn [ev ENV]; rewrite Q0, u_small by lia; lia
        | cbn [ev ENV]; rewrite Q0, u_small by lia; lia]. }
    clear EQM Hstr2 Ht82. rename M0 into M3.
    (* [comment removed for export] *)
    set (dst := Z_to_bv 64 (bv_unsigned sp0 - 543)).
    assert (MC : mcH M3 dst (Z_to_bv 64 0x1084a) 0 []).
    { constructor; subst dst; rewrite ?u_small by lia; cbn [length]; try lia; reflexivity. }
    lazymatch goal with |- realizes _ (mkCfg (mkst ?Rc _ _ _) _) _ =>
      assert (A1 : getr Rc 1 = (0x41d64 : word)) by (regv HR (1 : reg); apply bv_eq; reflexivity);
      assert (A10 : getr Rc 10 = dst)
        by (regv HR (10 : reg); subst dst; ed_lin ltac:(cbn [ev ENV]; rewrite ?Q0); f_equal; lia);
      assert (A11 : getr Rc 11 = Z_to_bv 64 0x1084a) by (regv HR (11 : reg); reflexivity);
      assert (A12 : getr Rc 12 = Z_to_bv 64 0) by (regv HR (12 : reg); reflexivity);
      destruct (ref_memcpy M3 dst (Z_to_bv 64 0x1084a) 0 _ (seg_rom RSEGS) MC Rc (0x41d64 : word)
                  ltac:(apply ret_ok_even; reflexivity) A1 A10 A11 A12) as (R4 & Hms & Hkeep);
      clear A1 A10 A11 A12
    end.
    replace (Z_to_bv 64 289344) with (0x46a40 : word) by (apply bv_eq; reflexivity).
    eapply rz_msteps; [exact Hh | exact Hlazy | exact Hms |]. clear Hms.
    change (wbytes M3 dst []) with M3.
    replace (0x41d64 : word) with (Z_to_bv 64 0x41d64) by (apply bv_eq; reflexivity).
    lazymatch type of HR with regs_ok ?E ?sr ?Rc =>
      pose proof (regs_after_keeps vals1 (blobs_ev BL) sr Rc R4 callee_kept
                    ltac:(rewrite HL1; vm_compute; reflexivity) HR Hkeep callee_kept_no0) as HR2 end.
    rewrite HL1 in HR2. clear HR Hkeep. rename HR2 into HR.
    pose proof (env_app_know RSEGS vals1 (junk_vals R4) (blobs_ev BL) M3 knC ltac:(rewrite HL1; vm_compute; reflexivity) HK) as HK2.
    clear HK. rename HK2 into HK.
    set (vals2 := vals1 ++ junk_vals R4) in *.
    assert (HL2 : length vals2 = 103%nat) by (subst vals2; rewrite length_app, junk_vals_length, HL1; reflexivity).
    assert (W0 : vals_ev vals2 0 = sp0) by (subst vals2; rewrite vals_ev_app_l by (rewrite HL1; lia); exact Q0).
    assert (W2 : vals_ev vals2 2 = pp) by (subst vals2; rewrite vals_ev_app_l by (rewrite HL1; lia); exact Q2).
    clearbody vals2.
    change (Env (vals_ev vals2) (blobs_ev BL)) with (ENV vals2) in HR, HK.
    eapply (of_segDE path pp P T t8 vals2); eassumption.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

End Tail.
