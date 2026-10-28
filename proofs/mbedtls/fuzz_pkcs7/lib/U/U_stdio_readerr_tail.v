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
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BB Require Import Amb CatExec CatSim SeqExec StoreOk ShapeX Hoare BBFrame ShapeLaws SpecConsts MmapSim AllocSim FileSim AgentLib SymExec SymExec2 SymExec2Sound SymRun SymDrive SymDriveX SymDriveH4 MemcpyLib LibTail.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Sys Require Import Nodes LibWritev.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Spec Require Import Spec.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U Require Import U_exit_base U_stdio_defs U_exit U_stdio_call U_memcpy_base U_memcpy U_memchr U_strnlen U_startup U_main_entry.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U Require Import U_stdio_readerr_defs.
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
Ltac2 gd_tbl_P_stdio_readerr_tail () : Init.string Init.list := ["Corelib.Init.Datatypes.list"; "stdpp.bitvector.definitions.bv"; "LinuxProcessSemantics.Riscv.Prelude.bvmap"; "Corelib.Init.Datatypes.option"; "Corelib.Init.Logic.eq"; "Corelib.Init.Datatypes.nat"; "Corelib.Init.Datatypes.length"; "RocqVerifyHarness.AgentSubmission.BB.SymRun.vals_ev"; "RocqVerifyHarness.AgentSubmission.BB.SymExec2Sound.SX2S.regs_ok"; "Tail.ENV"; "RocqVerifyHarness.AgentSubmission.U.U_stdio_readerr_defs.srI0"; "RocqVerifyHarness.AgentSubmission.BB.SymExec2Sound.SX2S.know_ok"; "RocqVerifyHarness.ProcessOversight.Tgt_fuzz_pkcs7_ubsan.M.loaded_segments"; "RocqVerifyHarness.AgentSubmission.U.U_stdio_readerr_defs.knI0"; "RocqVerifyHarness.AgentSubmission.Lib.Shape.realizes"; "LinuxProcessSemantics.LinuxProcessSem.Run.mkCfg"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.mkst"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.fx0"; "stdpp.bitvector.definitions.Z_to_bv"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.seg_rom"; "RocqVerifyHarness.AgentSubmission.Lib.Shape.t_exit"; "RocqVerifyHarness.AgentSubmission.Spec.Spec.exit_code"; "LinuxProcessSemantics.LinuxProcessSem.State.m_fs"; "Corelib.Init.Datatypes.app"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.word_to_le_bytes"; "Tail.PRE19"; "Corelib.Numbers.BinNums.Z"; "Stdlib.ZArith.BinInt.Z.of_nat"; "Corelib.Init.Logic.and"; "Stdlib.ZArith.BinInt.Z.le"; "RocqVerifyHarness.AgentSubmission.U.U_stdio_readerr_defs.srH0"; "RocqVerifyHarness.AgentSubmission.U.U_stdio_readerr_defs.knH0"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.rdn"; "Stdlib.ZArith.BinInt.Z.sub"; "stdpp.bitvector.definitions.bv_unsigned"; "Corelib.Init.Datatypes.Some"; "Stdlib.ZArith.BinInt.Z.add"; "Corelib.Init.Datatypes.cons"; "Corelib.Init.Datatypes.nil"; "RocqVerifyHarness.AgentSubmission.Lib.Shape.t_emit"; "RocqVerifyHarness.AgentSubmission.Spec.Spec.W"; "RocqVerifyHarness.AgentSubmission.Spec.Spec.msg_read_error"; "RocqVerifyHarness.AgentSubmission.U.U_stdio_readerr_defs.srG0"; "RocqVerifyHarness.AgentSubmission.U.U_stdio_readerr_defs.knG0"; "RocqVerifyHarness.AgentSubmission.Lib.Shape.TSet"; "RocqVerifyHarness.AgentSubmission.U.U_stdio_readerr_defs.srF0"; "RocqVerifyHarness.AgentSubmission.U.U_stdio_readerr_defs.knE"; "Corelib.Init.Nat.add"; "Tail.reG0"; "Corelib.Init.Logic.not"; "Stdlib.Lists.List.In"; "RocqVerifyHarness.AgentSubmission.U.U_stdio_readerr_defs.srD0"; "RocqVerifyHarness.AgentSubmission.U.U_stdio_readerr_defs.knC"; "Tail.reF0"; "RocqVerifyHarness.AgentSubmission.BB.SymExec2Sound.SX2S.mem_denot"; "RocqVerifyHarness.AgentSubmission.U.U_stdio_readerr_defs.logM1"; "RocqVerifyHarness.AgentSubmission.BB.CatExec.wbytes"; "RocqVerifyHarness.AgentSubmission.U.U_stdio_readerr_defs.srRE0"; "RocqVerifyHarness.AgentSubmission.U.U_stdio_readerr_defs.knRE0"].


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
  #[using="Hvsp Hh Hlazy SPlo SPhi"] Lemma re_segI : ltac2:(CDefT.buildp (gd_tbl_P_stdio_readerr_tail ()) "Pvals,(0.(1.&40.))PR,(2.&5.(1.&40.))PM,P,(1.&40.)(3.(1.&8.))P,(4.$5.(6.(1.&40.)R3.)#107.)P,(4.(1.&40.)(7.R4.#0.)Vsp0,)P,(8.(9.R5.)$:.R4.)P,(;.$<.(9.R6.)R4.$=.)(>.$<.(?.(10.$11.R6.(12.&40.+420:8.)R5.(13.$<.))Vmodel,)(14.(15.+2.)(16.Vmodel,)))")
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
  Definition PRE19 : list byte := s2b "cli: read error on "%string.

  #[using="Type"] Lemma PRE19_words : ltac2:(CDefT.buildp (gd_tbl_P_stdio_readerr_tail ()) "(4.(0.(1.&8.))(17.(1.&8.)(18.#8.(12.&40.+616572203:696<63.))(17.(1.&8.)(18.#8.(12.&40.+20726?7272652064.))(17.(1.&8.)(18.#2.(12.&40.+6>6?.))(18.#1.(12.&40.+20.)))))$19.)")
(* [comment removed for export] *).
  Proof. vm_compute. repeat (apply (f_equal2 cons); [apply bv_eq; reflexivity|]). reflexivity. Qed.

  Local Ltac2 Set LiaOrc.tbl := fun () => "00o0?L10158629020.36L12245466970.29L14418071291.30L15045278903.36L16639375087.36L20824379164.36L20923401285.36L2133530424.33 L23092048984.31L23923508984.31L24615534379.32L25278098835.29L25278098835.30L26203440164.29L26548451830.31L27836886250.36L30226912948.38L30452499965.32L30452506865.33L30467067489.28L32857128880.28L32858771744.33L32858780716.32L32861317660.36L33656270521.28L33671292192.29L33671292195.30L35847184554.36L38353938875.29L38478037259.32L38884559273.29L38948788060.36L41231950621.32L41493492207.36L41506071619.28L41920312205.36L42994380186.31L44247534562.33L44247543534.32L44502089051.33L44911943466.30L4826696077.36 L49702778543.32L50040071339.36L51702320857.30L52795551.29   L53089041842.36L53178551987.32L5431447131.36 L54719003339.31L5933052733.29 L5933052733.30 L5933052733.32 L60220051006.32L62260912303.33L6384997240.29 L64149391721.36L68056979097.31L68449847360.36L7213634117.30 L8503243218.30 L8534631579.30 L9359554572.28 00000P00g01>01P01k02F02X03703E03\03n04<04J04e05305E05W05n06E06\07307J07a08<08J08X08f09A09S09e0:<0:N0:`0;;0;R0<10<H0<_0=60=M0=d0>?0>V0>l0?C0?_0@:0@H0@h0A?0AM0A[0Ai0B@0BR0Bi0C?0CM0Ci0DA0DY0E<0EXS3sp04path1P4vals3HPr2HL3Hhi3LENS3sp04SPhi4path4vals2HLS3sp04SPhi4path4vals2HLS4path4vals2HL3LENS3sp04SPhi4path4vals2HL3LENS3sp04SPlo4path4vals2HL3LENS4path4vals2HL3LENS3sp04path1P4vals2HP3HPr2HL3HhiS4path4vals2HLS3sp04SPhi4path4vals2HLS3sp04path4vals2HLS4path4vals2HLS4path4vals2HLS3sp04path1P4vals2HP3HPr2HLS4path4vals2HLS4path4vals2HL3LENS4path4vals2HL3LENS3sp04SPhi4path4vals2HLS3sp04SPhi4path4vals2HLS3sp04SPhi4path4vals2HLS3sp04SPlo4path4vals2HLS3sp04SPlo4path4vals2HLS3sp04SPlo4path4vals2HLS3sp04SPlo4path4vals2HL3LENS4path4vals2HLS4path4vals2HLS4path4vals2HLS3sp04path1P4vals2HP2HL3LENS3sp04path4vals2HLS3sp04path4vals2HLS3sp04SPlo4path4vals2HLS4path4vals2HL3LENS3sp04path4vals2HLS3sp04SPhi4path4vals2HL3LENS3sp04SPhi4path4vals2HLS3sp04path1P4vals2HP2HL3Hlo3LENS3sp04SPhi4path4vals2HLS3sp04SPlo4path4vals2HLS3sp04SPlo4path4vals2HLS3sp04path1P4vals2HP2HLS3sp04SPlo4path4vals2HLS4path1P4vals2HP3HPr2HL3LENS3sp04SPhi4path4vals2HLS3sp04path4vals2HL3LENS3sp04SPhi4path4vals2HLS3sp04SPlo4SPhi4path4vals2HLS3sp04SPlo4path4vals2HL3LENS4path4vals2HLS3sp04path1P4vals3HPr2HL3Hhi3LENS3sp04SPlo4path4vals2HLS4path4vals2HLS4path4vals2HLS4path4vals2HLS3sp04SPlo4path4vals2HLS3sp04path4vals2HLS3sp04SPhi4path4vals2HLS3sp04path4vals2HL3LENS4path4vals2HLS3sp04path1P4vals3HPr2HL3LENS3sp04path1P4vals3HPr2HLS3sp04path1P4vals3HPr2HLS3sp04path1P4vals2HP3HPr2HL3Hlo3HhiS3sp04SPlo4SPhi4path4vals2HL". (* [comment removed for export] *)
  #[using="Hvsp Hh Hlazy Hfd2 SPlo SPhi"] Lemma re_segH : ltac2:(CDefT.buildp (gd_tbl_P_stdio_readerr_tail ()) "Ppath,(0.(1.&8.))PP,$1:.Pvals,(0.(1.&40.))PR,(2.&5.(1.&40.))PM,P,(1.&40.)(3.(1.&8.))P,(4.$1:.(1;.(6.(1.&8.)R5.))R4.)P,(1<.(1=.=R5.)(1=.R5.+3<.))P,(4.$5.(6.(1.&40.)R5.)#>7.)P,(4.(1.&40.)(7.R6.#0.)Vsp0,)P,(4.(1.&40.)(7.R7.#71.)(12.&40.R8.))P,(8.(9.R8.)$1>.R7.)P,(;.$<.(9.R9.)R7.$1?.)P,(4.(3.(0.(1.&8.)))(20.$<.R8.(12.&40.(21.(22.&40.Vsp0,)+21=.))(6.(1.&8.)R<.))(23.(0.(1.&8.))R<.))P,(4.(3.(0.(1.&8.)))(20.$<.R9.(12.&40.(24.(21.(22.&40.Vsp0,)+21=.)R<.))#1.)(23.(0.(1.&8.))(25.(1.&8.)(12.&8.+:.)(26.(1.&8.)))))(>.$<.(?.(10.$11.R;.(12.&40.+41=64.)R:.(13.$<.))Vmodel,)(27.(28.+2.(29.R>.))(14.(15.+2.)(16.Vmodel,))))")
(* [comment removed for export] *).
  Proof.
    intros path P vals R M HP HPr HL P0 P113 HR HK SBp SBn.
    pose proof SPlo as Hlo. pose proof SPhi as Hhi.
    (* [comment removed for export] *)
    run_blk_keep scr0 231%nat.
    (* [comment removed for export] *)
    assert (WOK : win_ok (ENV vals) 0 BUF_LO BUF_HI IHI).
    { unfold win_ok, BUF_LO, BUF_HI, IHI. cbn [ev ENV]. rewrite P0. lia. }
    assert (SBp' : rdn RSEGS M0 (Z_to_bv 64 (bv_unsigned sp0 - 541)) (length path) = Some path).
    { rewrite EQM, (rdn_mem_denot_out RSEGS (ENV vals) M _ 0 BUF_LO BUF_HI IHI);
        [exact SBp | vm_compute; reflexivity | exact WOK | cbn [ev ENV]; rewrite P0; unfold BUF_LO; rewrite u_small by lia; lia
        | cbn [ev ENV]; rewrite P0; unfold BUF_HI; rewrite u_small by lia; lia]. }
    assert (SBn' : rdn RSEGS M0 (Z_to_bv 64 (bv_unsigned sp0 - 541 + P)) 1 = Some [Z_to_bv 8 10]).
    { rewrite EQM, (rdn_mem_denot_out RSEGS (ENV vals) M _ 0 BUF_LO BUF_HI IHI);
        [exact SBn | vm_compute; reflexivity | exact WOK | cbn [ev ENV]; rewrite P0; unfold BUF_LO; rewrite u_small by lia; lia
        | cbn [ev ENV]; rewrite P0; unfold BUF_HI; rewrite u_small by lia; cbn; lia]. }
    clear EQM SBp SBn. rename M0 into M'. 
    (* [comment removed for export] *)
    krdv HK 0%nat (-560)%Z 8%nat Hw0. { apply flat_intro; cbn [edenot ev ENV]; rewrite ?P0; lia. }
    krdv HK 0%nat (-552)%Z 8%nat Hw1. { apply flat_intro; cbn [edenot ev ENV]; rewrite ?P0; lia. }
    krdv HK 0%nat (-544)%Z 2%nat Hw2. { apply flat_intro; cbn [edenot ev ENV]; rewrite ?P0; lia. }
    krdv HK 0%nat (-542)%Z 1%nat Hw3. { apply flat_intro; cbn [edenot ev ENV]; rewrite ?P0; lia. }
    unfold adenot, v_addi in Hw0, Hw1, Hw2, Hw3. cbn [a_base a_off edenot ev ENV] in Hw0, Hw1, Hw2, Hw3.
    rewrite P0 in Hw0, Hw1, Hw2, Hw3.
    assert (H17 : rdn RSEGS M' (Z_to_bv 64 (bv_unsigned sp0 + -560)) 19 = Some PRE19).
    { rewrite <- PRE19_words. change 19%nat with (8 + (8 + (2 + 1)))%nat.
      apply rdn_app_Z; [exact Hw0 | | lia | lia].
      apply rdn_app_Z; [ | | lia | lia].
      + replace (bv_unsigned sp0 + -560 + Z.of_nat 8)%Z with (bv_unsigned sp0 + -552)%Z by lia. exact Hw1.
      + apply rdn_app_Z; [ | | lia | lia].
        * replace (bv_unsigned sp0 + -560 + Z.of_nat 8 + Z.of_nat 8)%Z with (bv_unsigned sp0 + -544)%Z by lia. exact Hw2.
        * replace (bv_unsigned sp0 + -560 + Z.of_nat 8 + Z.of_nat 8 + Z.of_nat 2)%Z with (bv_unsigned sp0 + -542)%Z by lia.
          exact Hw3. }
    assert (MSG : rdn RSEGS M' (Z_to_bv 64 (bv_unsigned sp0 + -560)) (19 + (length path + 1))
                  = Some (msg_read_error path)).
    { unfold msg_read_error. change (s2b _) with PRE19.
      apply rdn_app_Z; [exact H17 | | lia | lia].
      apply rdn_app_Z; [| | lia | lia].
      + replace (bv_unsigned sp0 + -560 + Z.of_nat 19)%Z with (bv_unsigned sp0 - 541)%Z by lia. exact SBp'.
      + replace (bv_unsigned sp0 + -560 + Z.of_nat 19 + Z.of_nat (length path))%Z
          with (bv_unsigned sp0 - 541 + P)%Z by lia. exact SBn'. }
    (* [comment removed for export] *)
    assert (LEN : length (msg_read_error path) = (19 + (length path + 1))%nat)
      by (unfold msg_read_error; rewrite !length_app; reflexivity).
    replace (W 2 (msg_read_error path)) with (map (WriteEv (Z_to_bv 64 2)) (msg_read_error path ++ []))
      by (unfold W; rewrite app_nil_r; reflexivity).
    dpose itinerary_re as (_ & _ & _ & _ & _ & _ & _ & SC & _).
    lazymatch goal with |- realizes _ (mkCfg (mkst ?Rc _ ?Mc _) _) _ =>
    apply (stdio_call_sound vals (blobs_ev BL) srH knH Rc Mc model scRE (msg_read_error path) []
             (t_exit (exit_code 2) (m_fs model)) HR HK (eq_trans (f_equal (fun n => stdio_call n srH knH) HL) SC));
      cbn [sc_f sc_fd sc_ret sc_wb sc_wp sc_bufp sc_bufsz sc_s sc_l sc_sp sc_sr sc_kn scRE]; rewrite ?LEN end.
    - ed_lin ltac:(cbn [ev ENV]; rewrite ?P0, ?P113). unorm. lia.
    - ed_lin ltac:(cbn [ev ENV]; rewrite ?P0, ?P113). unorm. lia.
    - cbn [edenot length]. reflexivity.
    - cbn [length Z.of_nat]. lia.
    - right. ed_lin ltac:(cbn [ev ENV]; rewrite ?P0, ?P113). unorm. lia.
    - left. ed_lin ltac:(cbn [ev ENV]; rewrite ?P0, ?P113). unorm. lia.
    - cbn [edenot]. unorm. lia.
    - ed_lin ltac:(cbn [ev ENV]; rewrite ?P0, ?P113). unorm. lia.   (* [comment removed for export] *)
    - cbn [edenot]. unorm. lia.                                         (* [comment removed for export] *)
    - ed_lin ltac:(cbn [ev ENV]; rewrite ?P0, ?P113). unorm.
      replace (bv_unsigned sp0 + -560)%Z with (bv_unsigned sp0 + -560)%Z in MSG by lia. exact MSG.
    - reflexivity.
    - exact Hfd2.
    - exact Hh.
    - exact Hlazy.
    - apply t_exit_has_nil.
    - (* [comment removed for export] *)
      clear HR HK. intros R2 M2 HR HK.
      eapply (re_segI (vals ++ junk_vals R2));
        [ rewrite length_app, junk_vals_length, HL; reflexivity
        | rewrite vals_ev_app_l by (rewrite HL; lia); exact P0
        | exact HR | exact HK ].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  #[using="Type"] Lemma re_nl_img : rdn RSEGS (fun _ => None) (Z_to_bv 64 0x10863) 1 = Some [Z_to_bv 8 10].
  Proof. vm_compute. reflexivity. Qed.

  Local Ltac2 Set LiaOrc.tbl := fun () => "00U0?L15212191020.29L16970013023.35L16974067588.36L18259526332.35L19326057569.29L20137366566.24L20304433124.29L26203440164.28L26823884495.29L30224815626.33L31823992798.28L31839455507.31L32049632222.28L38353938875.28L42801992018.35L43012614646.29L46442192258.29L49123047700.29L52516262761.24L52526751222.29L52795551.28   L54441417064.34L54530852096.24L55774847545.31L60358885047.29L63187367.35   L64550211237.29L64641015077.24L7200670590.31 L8530357212.36 L8530359712.31 L8534550086.29 L8534656263.35 L9152800632.31 L9317012995.29 L9359554572.27 L9361438865.32 00000D00j01P02902:02N02b03=03>03S03a04504C04U05605D05_05m06;06I06e07:07J07b08008V08j09>09V0:C0:f0;I0<60<M0<i0=E0=aS3sp04path1P4vals2HLS3sp04path1P4vals3HPr2HL3Hhi5vals13HL1S3sp04path1P4vals3HPr2HL3Hhi5vals13HL1S3sp04path1P4vals2HP3HPr2HL3Hhi5vals13HL1FS4path1P4vals3HPr2HLS4path1P4vals3HPr2HLS3sp04path1P4vals2HP3HPr2HLFS4path4vals2HL2R23HL1S4path4vals2HLS3sp04path1P4vals2HLS4path4vals2HLS3sp04path4vals2HLS3sp04path1P4vals2HP2HL5vals13HL1S4path4vals2HLS3sp04path1P4vals2HP2HL3HloS4path4vals2HLS4path4vals2HLS4path4vals2HLS3sp04SPlo4SPhi4path4vals2HLS4path4vals2HL2R23HL1S4path1P4vals2HLS3sp04path1P4vals3HPr2HLS4path4vals2HLS3sp04SPlo4SPhi4path4vals2HL5vals13HL1S4path1P4vals3HPr2HLS4path1P4vals3HPr2HLS3sp04path1P4vals3HPr2HLS3sp04path1P4vals2HP3HPr2HL3Hlo3Hhi5vals13HL1S3sp04path1P4vals2HP3HPr2HL3Hlo3HhiS3sp04path1P4vals2HP3HPr2HL3Hlo3HhiS3sp04path1P4vals2HP3HPr2HL3Hlo3Hhi5vals13HL1S3sp04SPhi4path4vals2HLS3sp04path1P4vals3HPr2HL3HhiS3sp04SPlo4SPhi4path4vals2HLS3sp04SPlo4SPhi4path4vals2HL". (* [comment removed for export] *)
  #[using="Hvsp Hh Hlazy Hfd2 SPlo SPhi"] Lemma re_segG : ltac2:(CDefT.buildp (gd_tbl_P_stdio_readerr_tail ()) "Ppath,(0.(1.&8.))PP,$1:.Pvals,(0.(1.&40.))PR,(2.&5.(1.&40.))PM,P,(1.&40.)(3.(1.&8.))P,(4.$1:.(1;.(6.(1.&8.)R5.))R4.)P,(1<.(1=.=R5.)(1=.R5.+3<.))P,(4.$5.(6.(1.&40.)R5.)#<7.)P,(4.(1.&40.)(7.R6.#0.)Vsp0,)P,(4.(1.&40.)(7.R7.#71.)(12.&40.R8.))P,(8.(9.R8.)$2:.R7.)P,(;.$<.(9.R9.)R7.$2;.)P,(4.(3.(0.(1.&8.)))(20.$<.R8.(12.&40.(21.(22.&40.Vsp0,)+21=.))(6.(1.&8.)R<.))(23.(0.(1.&8.))R<.))(>.$<.(?.(10.$11.R:.(12.&40.+41=64.)R9.(13.$<.))Vmodel,)(27.(28.+2.(29.R=.))(14.(15.+2.)(16.Vmodel,))))")
(* [comment removed for export] *).
  Proof.
    intros path P vals R M HP HPr HL P0 P113 HR HK SBp.
    pose proof SPlo as Hlo. pose proof SPhi as Hhi.
    (* [comment removed for export] *)
    run_blk_keep scrG 199%nat.
    { (* [comment removed for export] *)
      unfold sc_denot. cbn [branch_taken]. ed_lin ltac:(cbn [ev ENV]; rewrite ?P0, ?P113).
      replace (-1 * P + 61)%Z with (61 - P)%Z by lia.
      rewrite ltu_ZZ by lia. cbn [negb]. rewrite (proj2 (Z.ltb_ge _ _)) by lia. reflexivity. }
    assert (WOK : win_ok (ENV vals) 0 BUF_LO BUF_HI IHI).
    { unfold win_ok, BUF_LO, BUF_HI, IHI. cbn [ev ENV]. rewrite P0. lia. }
    assert (SBp' : rdn RSEGS M0 (Z_to_bv 64 (bv_unsigned sp0 - 541)) (length path) = Some path).
    { rewrite EQM, (rdn_mem_denot_out RSEGS (ENV vals) M _ 0 BUF_LO BUF_HI IHI);
        [exact SBp | vm_compute; reflexivity | exact WOK | cbn [ev ENV]; rewrite P0; unfold BUF_LO; rewrite u_small by lia; lia
        | cbn [ev ENV]; rewrite P0; unfold BUF_HI; rewrite u_small by lia; lia]. }
    clear EQM SBp. rename M0 into M'.
    (* [comment removed for export] *)
    set (dst := Z_to_bv 64 (bv_unsigned sp0 - 541 + P)).
    assert (Hsrc : rdn RSEGS M' (Z_to_bv 64 0x10863) 1 = Some [Z_to_bv 8 10]).
    { rewrite (kimg_rdn RSEGS (ENV vals) _ knG ltac:(let i := kidx knG (is_kimg_cov 0x10863 1) in exact i)
                 _ _ 0x10863 1 HK eq_refl) by (cbn; lia). apply re_nl_img. }
    assert (Hdst : store_ok RSEGS M' dst 1 = true).
    { pose proof (kwr_store_ok RSEGS (ENV vals) _ knG ltac:(let i := kidx knG (is_kwr_cov (EVar 0) (-541) 64) in exact i)
                    _ _ _ (-541 + P) 1 HK eq_refl ltac:(lia) ltac:(cbn; lia)) as Hst.
      unfold adenot, v_addi in Hst. cbn [a_base a_off edenot ev ENV] in Hst. rewrite P0 in Hst.
      subst dst. replace (bv_unsigned sp0 - 541 + P)%Z with (bv_unsigned sp0 + (-541 + P))%Z by lia. exact Hst. }
    assert (MC : mcH M' dst (Z_to_bv 64 0x10863) 1 [Z_to_bv 8 10]).
    { constructor; cbn [length Z.to_nat Z.of_nat Pos.to_nat]; subst dst; rewrite ?u_small by lia; try lia.
      - exact Hsrc.
      - exact Hdst. }
    lazymatch goal with |- realizes _ (mkCfg (mkst ?Rc _ _ _) _) _ =>
      assert (A1 : getr Rc 1 = (0x41d64 : word)) by (regv HR (1 : reg); apply bv_eq; reflexivity);
      assert (A10 : getr Rc 10 = dst)
        by (regv HR (10 : reg); subst dst; ed_lin ltac:(cbn [ev ENV]; rewrite ?P0, ?P113); f_equal; lia);
      assert (A11 : getr Rc 11 = Z_to_bv 64 0x10863) by (regv HR (11 : reg); reflexivity);
      assert (A12 : getr Rc 12 = Z_to_bv 64 1) by (regv HR (12 : reg); reflexivity);
      destruct (ref_memcpy M' dst (Z_to_bv 64 0x10863) 1 _ (seg_rom RSEGS) MC Rc (0x41d64 : word)
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
    pose proof (know_cut_sound RSEGS (ENV vals) M' (wbytes M' dst [Z_to_bv 8 10]) 0 (-541) BUF_HI IHI knG
                  ltac:(unfold win_ok, BUF_HI, IHI; cbn [ev ENV]; rewrite P0; lia)
                  ltac:(apply (wbytes_agree_out M' dst [Z_to_bv 8 10] (ENV vals) 0 (-541) BUF_HI);
                        cbn [ev ENV length]; rewrite P0; subst dst; unfold BUF_HI; rewrite ?u_small by lia; lia)
                  (wbytes_grows _ _ _) HK) as HK2.
    clear HK. change (kn_cut 0 (-541) BUF_HI IHI knG) with knH0 in HK2.
    pose proof (env_app_know RSEGS vals (junk_vals R2) (blobs_ev BL) _ knH0 ltac:(rewrite HL; vm_compute; reflexivity) HK2) as HK.
    clear HK2.
    set (vals1 := vals ++ junk_vals R2) in *.
    assert (HL1 : length vals1 = 231%nat) by (subst vals1; rewrite length_app, junk_vals_length, HL; reflexivity).
    assert (Q0 : vals_ev vals1 0 = sp0) by (subst vals1; rewrite vals_ev_app_l by (rewrite HL; lia); exact P0).
    assert (Q113 : vals_ev vals1 113 = Z_to_bv 64 P) by (subst vals1; rewrite vals_ev_app_l by (rewrite HL; lia); exact P113).
    clearbody vals1.
    change (Env (vals_ev vals1) (blobs_ev BL)) with (ENV vals1) in HR, HK.
    eapply (re_segH path P vals1); try eassumption.
    - (* [comment removed for export] *)
      rewrite rdn_wbytes_out; [exact SBp' | | |]; cbn [length]; subst dst; rewrite ?u_small by lia; lia.
    - (* [comment removed for export] *)
      subst dst. pose proof (rdn_wbytes_hit RSEGS [Z_to_bv 8 10] M' (Z_to_bv 64 (bv_unsigned sp0 - 541 + P))) as Hn.
      cbn [length] in Hn. apply Hn. rewrite u_small by lia. lia.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  (* [comment removed for export] *)
  Definition reG0 (path : list byte) (P : Z) (T : TSet) : Prop := ltac2:(CDefT.buildp (gd_tbl_P_stdio_readerr_tail ()) "Pvals,(0.(1.&40.))PR,(2.&5.(1.&40.))PM,P,(1.&40.)(3.(1.&8.))P,(4.$5.(6.(1.&40.)R3.)#<7.)P,(4.(1.&40.)(7.R4.#0.)Vsp0,)P,(4.(1.&40.)(7.R5.#71.)(12.&40.O2.))P,(8.(9.R6.)$2:.R5.)P,(;.$<.(9.R7.)R5.$2;.)P,(4.(3.(0.(1.&8.)))(20.$<.R6.(12.&40.(21.(22.&40.Vsp0,)+21=.))(6.(1.&8.)O3.))(23.(0.(1.&8.))O3.))(>.$<.(?.(10.$11.R8.(12.&40.+41=64.)R7.(13.$<.))Vmodel,)O1.)")
(* [comment removed for export] *).

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00M0?L10172926255.36L10305706566.30L11660218926.31L11664808246.36L11671099305.30L13522892627.36L14518609262.31L18263845356.43L19061701751.35L25351397799.36L26205947323.38L30224815626.40L31309203627.35L33806152151.36L45091832686.31L50479863.43   L50485504.38   L51701270147.36L54441417064.41L55291644544.36L57112669364.36L63064806.36   L65340997948.35L66262088256.36L68172719476.38L68176214858.36L9152800632.38 L9359554572.34 L9361438865.39 00000>00R00f01:01N01j02802a03;03N03i04>04]05405H05n06J06K06`07207307O07]08=08O08o09F09b0:>S4path4vals2HLS4path1P4vals3HPr2HLS4path1P4vals3HPr2HLS4path1P4vals3HPr2HLS4path1P4vals3HPr2HLS3sp04path1P4vals3HPr2HL3HhiS4path4vals2HLS3sp04path1P4vals2HP3HPr2HL3Hhi5vals13HL1S3sp04path2pp4vals2HL4Hpp1S4path1P4vals2HP2HLS3sp04path1P4vals2HP3HPr2HLS4path4vals2HL2R23HL1S3sp04path2pp1P4vals2HP2HL4Hpp2S4path1P4vals2HP3HPr2HLS4path1P4vals3HPr2HLS3sp04SPlo4SPhi4path4vals2HL5vals13HL1S3sp04SPlo4SPhi4path4vals2HLFS4path4vals2HL2R23HL1S3sp04path4vals2HLFS3sp04SPlo4SPhi4path4vals2HLS4path4vals2HLS3sp04path2pp1P4vals2HL4Hpp23HhiS3sp04path4vals2HLS3sp04path2pp1P4vals3HPr2HL4Hpp1S3sp04SPhi4path4vals2HLS3sp04SPlo4SPhi4path4vals2HLS3sp04SPlo4SPhi4path4vals2HL". (* [comment removed for export] *)
  #[using="Hvsp Hh Hlazy SPlo SPhi"] Lemma re_segF_gen : ltac2:(CDefT.buildp (gd_tbl_P_stdio_readerr_tail ()) "Ppath,(0.(1.&8.))Ppp,(1.&40.)PP,$1:.PT,$2<.Pvals,(0.(1.&40.))PR,(2.&5.(1.&40.))PM,P,(1.&40.)(3.(1.&8.))P,(4.$1:.(1;.(6.(1.&8.)R7.))R5.)P,(1<.(1=.=R6.)(1=.R6.+3=.))P,(4.$5.(6.(1.&40.)R5.)#:7.)P,(4.(1.&40.)(7.R6.#0.)Vsp0,)P,(4.(1.&40.)(7.R7.#2.)R:.)P,(4.(1.&40.)(7.R8.#71.)(12.&40.R:.))P,(1=.(22.&40.Vsp0,)(22.&40.R<.))P,(1=.(24.(24.(22.&40.R=.)R<.)+8.)(24.(22.&40.Vsp0,)+400000.))P,(8.(9.R;.)$2=.R:.)P,(;.$<.(9.R<.)R:.$2>.)P,(4.(3.(0.(1.&8.)))(20.$<.R;.R10.(2?.(6.(1.&8.)R11.)#1.))(23.(0.(1.&8.))(17.(1.&8.)R11.(25.(1.&8.)(12.&8.=)(26.(1.&8.))))))P,(30.R12.R10.R?.)(>.$<.(?.(10.$11.R>.(12.&40.+41=64.)R=.(13.$<.))Vmodel,)R10.)")
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
    set (dst := Z_to_bv 64 (bv_unsigned sp0 - 541)).
    assert (Hsrc : rdn RSEGS M' pp (length path) = Some path).
    { rewrite <- (firstn_app_l _ path [Z_to_bv 8 0]) at 2 || idtac.
      replace path with (firstn (length path) (path ++ [Z_to_bv 8 0])) at 2
        by (rewrite firstn_app, firstn_all, Nat.sub_diag; cbn [firstn]; apply app_nil_r).
      eapply rdn_firstn; [exact Hstr' | lia]. }
    assert (Hdst : store_ok RSEGS M' dst (length path) = true).
    { pose proof (kwr_store_ok RSEGS (ENV vals) _ knF ltac:(let i := kidx knF (is_kwr_cov (EVar 0) (-541) 63) in exact i)
                    _ _ _ (-541) (length path) HK eq_refl ltac:(lia) ltac:(cbn; lia)) as Hst.
      unfold adenot, v_addi in Hst. cbn [a_base a_off edenot ev ENV] in Hst. rewrite P0 in Hst.
      subst dst. replace (bv_unsigned sp0 - 541)%Z with (bv_unsigned sp0 + -541)%Z by lia. exact Hst. }
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
    pose proof (know_cut_sound RSEGS (ENV vals) M' (wbytes M' dst path) 0 (-541) BUF_HI IHI knF
                  ltac:(unfold win_ok, BUF_HI, IHI; cbn [ev ENV]; rewrite P0; lia)
                  ltac:(apply (wbytes_agree_out M' dst path (ENV vals) 0 (-541) BUF_HI);
                        cbn [ev ENV]; rewrite P0; subst dst; unfold BUF_HI; rewrite ?u_small by lia; lia)
                  (wbytes_grows _ _ _) HK) as HK2.
    clear HK. change (kn_cut 0 (-541) BUF_HI IHI knF) with knG0 in HK2.
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
    pose proof (rdn_wbytes_hit RSEGS path M' (Z_to_bv 64 (bv_unsigned sp0 - 541))) as Hc.
    apply Hc. rewrite u_small by lia. lia.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  Local Ltac2 Set LiaOrc.tbl := fun () => "0010?L38795564793.2600000DS4path1P4vals3HPr2HL". (* [comment removed for export] *)
  #[using="Hvsp Hh Hlazy Hfd2 SPlo SPhi"] Lemma re_segF : ltac2:(CDefT.buildp (gd_tbl_P_stdio_readerr_tail ()) "Ppath,(0.(1.&8.))Ppp,(1.&40.)PP,$1:.Pvals,(0.(1.&40.))PR,(2.&5.(1.&40.))PM,P,(1.&40.)(3.(1.&8.))P,(4.$1:.(1;.(6.(1.&8.)R6.))R4.)P,(1<.(1=.=R5.)(1=.R5.+3<.))P,(4.$5.(6.(1.&40.)R5.)#:7.)P,(4.(1.&40.)(7.R6.#0.)Vsp0,)P,(4.(1.&40.)(7.R7.#2.)R9.)P,(4.(1.&40.)(7.R8.#71.)(12.&40.R9.))P,(1=.(22.&40.Vsp0,)(22.&40.R;.))P,(1=.(24.(24.(22.&40.R<.)R;.)+8.)(24.(22.&40.Vsp0,)+400000.))P,(8.(9.R;.)$2=.R:.)P,(;.$<.(9.R<.)R:.$2>.)P,(4.(3.(0.(1.&8.)))(20.$<.R;.R?.(2?.(6.(1.&8.)R10.)#1.))(23.(0.(1.&8.))(17.(1.&8.)R10.(25.(1.&8.)(12.&8.=)(26.(1.&8.))))))(>.$<.(?.(10.$11.R=.(12.&40.+41=64.)R<.(13.$<.))Vmodel,)(27.(28.+2.(29.R11.))(14.(15.+2.)(16.Vmodel,))))")
(* [comment removed for export] *).
  Proof.
    intros path pp P vals R M HP HPr HL P0 P2 P113 Hpp1 Hpp2 HR HK Hstr.
    eapply (re_segF_gen path pp P _ vals); try eassumption; [lia|].
    intros vals' R' M' HL' Q0 Q113 HR' HK' SB. eapply (re_segG path P vals'); eassumption.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  Definition reF0 (path : list byte) (pp : word) (P : Z) (T : TSet) : Prop := ltac2:(CDefT.buildp (gd_tbl_P_stdio_readerr_tail ()) "Pvals,(0.(1.&40.))PR,(2.&5.(1.&40.))PM,P,(1.&40.)(3.(1.&8.))P,(4.$5.(6.(1.&40.)R3.)#:7.)P,(4.(1.&40.)(7.R4.#0.)Vsp0,)P,(4.(1.&40.)(7.R5.#2.)O3.)P,(4.(1.&40.)(7.R6.#71.)(12.&40.O2.))P,(8.(9.R7.)$2=.R6.)P,(;.$<.(9.R8.)R6.$2>.)P,(4.(3.(0.(1.&8.)))(20.$<.R7.O3.(2?.(6.(1.&8.)O4.)#1.))(23.(0.(1.&8.))(17.(1.&8.)O4.(25.(1.&8.)(12.&8.=)(26.(1.&8.))))))(>.$<.(?.(10.$11.R9.(12.&40.+41=64.)R8.(13.$<.))Vmodel,)O1.)")
(* [comment removed for export] *).

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  Local Ltac2 Set LiaOrc.tbl := fun () => "0190?L10309899295.43L10742216961.46L11664407159.51L11666905584.43L11879121292.40L14307436141.40L18335669935.40L18534106001.41L19072480109.37L19072480109.47L1954334414.40 L19963725408.52L24077028727.37L24078750703.51L24078821722.39L24078821722.40L24087004302.44L25612613803.45L25612713248.39L25614647967.41L28378693749.44L30224815626.47L30224815627.50L30226819466.40L31154219891.40L31227397377.44L31227520582.40L31319394225.37L31319394225.47L314458845.52  L34301895276.52L34301897727.47L35159558105.40L36474080581.44L37371372047.38L37905072827.46L40197912676.40L43363525287.47L43363527476.52L45050765751.46L48227411914.47L48227413593.52L49030424061.46L51306172107.46L53504481175.46L54441416810.49L54441515114.52L54467711090.41L54845076111.44L54853263195.39L54856104822.37L55890242748.45L55892356284.40L56277679942.46L57406519004.52L57406521167.47L58833951326.51L60188794084.43L6196680142.46 L64162542827.51L64162575595.48L64775433197.38L65141012212.47L65141014375.52L65161767.46   L65341309917.37L67697006827.44L67705075007.39L8532453019.38 L9271624767.40 L9348852209.33 L9359554572.47 L9361438865.46 00000N00f01D01b02002D02^03703Q04504O05A05d06Q07:07c08P08h09<09P09g0:<0:[0:o0;X0<40<P0<o0=X0>E0>n0?E0?W0@10@M0@i0AO0Af0BL0Bd0C;0Ca0D90D:0DR0Dg0EF0Eb0FB0F^0G40GW0H@0HA0Hg0I>0I\0J50JV0K50KJ0Ki0L@0Lf0ML0MZ0N20NF0O20O@0O\0PB0P^S4path1P4vals3HPr2HL5vals13HL1S4path4vals2HL5vals13HL1S4path1P4vals3HPr2HL5vals13HL1S4path1P4vals3HPr2HL5vals13HL1S4path4vals2HLS4path2t84vals2HL2L8S4path1P2t84vals3HPr2HL2L8S4path2pp1P2t84vals2HL2L8S3sp04path2pp4vals2HL4Hpp1S3sp04path2pp4vals2HL4Hpp15vals13HL1S4path1P2t84vals3HPr2HL2L8S3sp04path2pp1P4vals2HP2HL4Hpp23Hhi5vals13HL11i2HiS3sp04path2pp1P4vals2HP2HL4Hpp23HhiS3sp04path2pp1P4vals2HP2HL4Hpp23Hhi5vals13HL1S3sp04path2pp1P2t84vals2HP2HL4Hpp23Hhi2L8S3sp04path2pp1P2t84vals2HP2HL4Hpp23Hhi2L8S3sp04path2pp1P4vals2HP2HL4Hpp23Hhi5vals13HL1S4path4vals2HL5vals13HL1S4path2t84vals2HL2L8S4path2t84vals2HL2L8S3sp04SPlo4path4vals2HLS4path4vals2HL2R23HL1S4path4vals2HL5vals13HL12R43HL2S4path2t84vals2HL2L8S3sp04path2pp1P2t84vals2HP2HL4Hpp13Hlo2L8S3sp04SPlo4SPhi4path4vals2HLS3sp04SPlo4SPhi4path4vals2HLS3sp04path2pp1P4vals2HP2HL4Hpp2S3sp04path2pp1P4vals2HP2HL4Hpp25vals13HL1S3sp04path2pp4vals2HL4Hpp13Hlo5vals13HL11i2HiS3sp04path2pp4vals2HL4Hpp15vals13HL11i2HiS3sp04path4vals2HL1x2HxS3sp04path4vals2HLS3sp04path2pp4vals2HL4Hpp1S3sp04path2pp1P4vals2HL4Hpp2S3sp04path4vals2HL5vals13HL1S3sp04path2pp1P2t84vals2HL4Hpp23Hhi2L8S3sp04SPhi4path4vals2HLS3sp04SPhi4path4vals2HL5vals13HL11i2HiS4path4vals2HL5vals13HL1S3sp04SPlo4path4vals2HLS3sp04SPlo4path4vals2HL5vals13HL11i2HiS4path4vals2HL5vals13HL1FS4path4vals2HL5vals13HL1S4path4vals2HL2R23HL1S4path4vals2HL5vals13HL12R43HL2S4path2pp1P2t84vals2HP2HL2L8S4path2pp4vals2HL4Hppr5vals13HL1S4path2pp2t84vals2HL4Hppr2L8S4path2pp4vals2HL4HpprS3sp04path2pp1P4vals2HP2HL4Hpp13HloS3sp04path2pp1P2t84vals2HP2HL4Hpp13Hlo2L8FS3sp04SPlo4path4vals2HL5vals13HL11i2HiS3sp04SPlo4path4vals2HLS4path1P4vals3HPr2HL5vals13HL1S4path2t84vals2HL2L81i2HiS3sp04SPhi4path4vals2HL5vals13HL1S4path4vals2HL5vals13HL12R43HL2S4path4vals2HL2R23HL1S3sp04path2pp1P4vals2HP2HL4Hpp1S3sp04SPhi4path4vals2HLS3sp04SPhi4path4vals2HL5vals13HL11i2HiS3sp04SPlo4SPhi4path4vals2HL5vals13HL1S4path4vals2HLS4path4vals2HL5vals13HL1S4path2t84vals2HL2L8S3sp04path2pp1P4vals2HP2HL4Hpp14Hpp23Hlo3HhiS4path4vals2HLS3sp04SPlo4SPhi4path4vals2HLS3sp04SPlo4SPhi4path4vals2HL5vals13HL1S3sp04SPlo4SPhi4path4vals2HL". (* [comment removed for export] *)
  #[using="Hvsp Hh Hlazy SPlo SPhi"] Lemma re_segDE : ltac2:(CDefT.buildp (gd_tbl_P_stdio_readerr_tail ()) "Ppath,(0.(1.&8.))Ppp,(1.&40.)PP,$1:.PT,$2<.Pt8,(0.(1.&8.))Pvals,(0.(1.&40.))PR,(2.&5.(1.&40.))PM,P,(1.&40.)(3.(1.&8.))P,(4.$1:.(1;.(6.(1.&8.)R8.))R6.)P,(1<.(1=.=R7.)(1=.R7.+1????.))P,(31.(32.(1.&8.)(12.&8.=)R:.))P,(4.$5.(6.(1.&40.)R6.)#67.)P,(4.(1.&40.)(7.R7.#0.)Vsp0,)P,(4.(1.&40.)(7.R8.#2.)R<.)P,(1=.(22.&40.Vsp0,)(22.&40.R=.))P,(1=.(24.(24.(22.&40.R>.)R=.)+8.)(24.(22.&40.Vsp0,)+400000.))P,(8.(9.R;.)$33.R:.)P,(;.$<.(9.R<.)R:.$34.)P,(4.(3.(0.(1.&8.)))(20.$<.R;.R11.(2?.(6.(1.&8.)R12.)#1.))(23.(0.(1.&8.))(17.(1.&8.)R12.(25.(1.&8.)(12.&8.=)(26.(1.&8.))))))P,(4.(3.(0.(1.&8.)))(20.$<.R<.(12.&40.(24.(22.&40.R12.)R11.))#8.)(23.(0.(1.&8.))R?.))P,(35.R14.R13.R12.R11.)(>.$<.(?.(10.$11.R?.(12.&40.+41=64.)R>.(13.$<.))Vmodel,)R12.)")
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
    set (dst := Z_to_bv 64 (bv_unsigned sp0 - 541)).
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

  #[using="Type"] Lemma pre19_img : rdn RSEGS (fun _ => None) (Z_to_bv 64 0x1084e) 19 = Some PRE19.
  Proof. vm_compute. reflexivity. Qed.

  #[using="Type"] Lemma PRE19_len : length PRE19 = 19%nat.
  Proof. reflexivity. Qed.

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00;0?L24613428142.14L34497755335.14L37504097574.14L38475949454.14L38803581625.14L45527366623.14L49704866346.14L60217961147.14L64238114748.14L65069231746.14L66445618183.1400000500600;00@00J00K00U00_00i01301=S3sp0FS3sp0S3sp0S3sp04SPloFS3sp04SPhiS3sp04SPloS3sp04SPhiS3sp04SPhiS3sp04SPlo". (* [comment removed for export] *)
  #[using="Hvsp SPlo SPhi"] Lemma re_memcpy1_denot : ltac2:(CDefT.buildp (gd_tbl_P_stdio_readerr_tail ()) "Pvals,(0.(1.&40.))PM,P,(1.&40.)(3.(1.&8.))P,(4.(1.&40.)(7.R2.#0.)Vsp0,)(4.P,(1.&40.)(3.(1.&8.))(36.(9.R3.)R2.$37.)(38.R2.(12.&40.(21.(22.&40.Vsp0,)+230.))$19.))")
(* [comment removed for export] *).
  Proof.
    intros vals M P0. pose proof SPlo. pose proof SPhi.
    rewrite <- PRE19_words. cbn [mem_denot logM1]. rewrite !wbytes_app.
    unfold adenot, v_addi, at_. cbn [a_base a_off edenot ev ENV length Z.of_nat Pos.of_succ_nat Pos.succ]. rewrite P0.
    rewrite !length_N_to_le_bytes. cbn [Z.of_nat Pos.of_succ_nat Pos.succ]. unorm.
    repeat (f_equal; try (f_equal; lia)).
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  Local Ltac2 Set LiaOrc.tbl := fun () => "0140?L11477405174.38L12243364600.40L14415977306.40L16967776984.45L17857222406.44L19072480109.37L19072480109.45L19457099854.37L20582536138.38L23533672305.38L23921415000.40L24078642256.44L25271808757.40L26550544016.40L30224815626.42L30224815627.48L30454599770.40L31319394225.37L31319394225.45L32860873099.40L33669197954.40L34024036933.45L37371372047.38L37371372051.46L38057172332.38L38882466827.40L40438911199.38L41493379704.40L41943671286.38L42992285754.40L43459505280.38L44909841035.40L49028318205.44L51308275915.44L51700226936.40L51928341303.44L53012581002.38L53506584983.44L54721097579.40L55093830608.38L55894544189.45L5926759515.40 L59358396091.44L6198784974.44 L63073319.44   L6387091162.40 L64121095105.44L64162542827.49L64162575595.43L64223442366.45L64238229182.44L64775433197.38L64775433201.46L65069117312.44L65071320192.45L66264185478.45L66445241605.44L66447707653.45L67116225307.38L68059071289.40L68618298606.37L8202147140.38 L8532452999.46 L8532453019.38 L9095194694.38 L9348844977.41 L9348852209.33 L9540659342.44 00000>00U00l01V01W02102U02c03:03H03_04L04Z04h05=05\06306R07;07R07`08I08e09K09Y0:00:>0:U0:c0;:0;L0;c0<;0<<0<S0<k0<l0=D0=[0=\0>I0>W0?30?T0@:0@Q0@i0AH0A]0B>0B_0C>0Cg0DH0Di0ES0F40FU0Fl0G:0GH0GV0HL0I80IT0J:0JV0K:S4path4vals2HLS3sp04SPhi4path4vals2HLS3sp04SPhi4path4vals2HLS3sp04path2pp1P4vals2HL4Hpp23Hhi5vals13HL1FS3sp04path2pp4vals2HL4Hpp1S3sp04path2pp4vals2HL4Hpp15vals13HL1S4path4vals2HLS3sp04SPlo4path4vals2HLS4path4vals2HLS3sp04SPhi4path4vals2HLS3sp04path2pp1P4vals2HP2HL4Hpp23Hhi5vals13HL1S4path4vals2HLS4path4vals2HLS4path4vals2HL2R23HL1S4path4vals2HL5vals13HL12R43HL2S3sp04SPhi4path4vals2HLS3sp04path2pp1P4vals2HP2HL4Hpp2S3sp04path2pp1P4vals2HP2HL4Hpp25vals13HL1S3sp04SPlo4path4vals2HLS4path4vals2HLS3sp04path2pp1P4vals2HP2HL4Hpp15vals13HL1S3sp04path2pp1P4vals2HL4Hpp2S3sp04path2pp1P4vals2HL4Hpp25vals13HL1S4path4vals2HLS3sp04SPlo4path4vals2HLS4path4vals2HLS3sp04SPhi4path4vals2HLS4path4vals2HLS3sp04SPhi4path4vals2HLS3sp04path4vals2HLS3sp04SPlo4path4vals2HLS4path4vals2HL5vals13HL1FS3sp04SPhi4path4vals2HLS4path4vals2HL5vals13HL1FS4path4vals2HL5vals13HL1S3sp04SPlo4path4vals2HLFS3sp04path2pp1P4vals2HP2HL4Hpp13Hlo5vals13HL1S4path4vals2HLS3sp04path4vals2HL5vals13HL1S3sp04SPhi4path4vals2HL5vals13HL1S3sp04SPlo4SPhi4path4vals2HL5vals13HL1S3sp04SPhi4path4vals2HLS4path4vals2HL5vals13HL1S4path4vals2HL5vals13HL12R43HL2S4path4vals2HL2R23HL1S3sp04SPhi4path4vals2HL5vals13HL1S3sp04SPhi4path4vals2HL5vals13HL1S3sp04path2pp1P4vals2HP2HL4Hpp1S3sp04path2pp1P4vals2HP2HL4Hpp15vals13HL1S3sp04SPhi4path4vals2HL5vals13HL1S3sp04SPhi4path4vals2HL5vals13HL1S3sp04path2pp1P4vals2HL4Hpp23Hhi5vals13HL1S3sp04SPlo4path4vals2HL5vals13HL1S3sp04SPlo4path4vals2HL5vals13HL1S3sp04SPhi4path4vals2HLS4path4vals2HLS4path4vals2HLS4path4vals2HLS3sp04path2pp1P4vals2HP2HL4Hpp14Hpp23Hlo3Hhi5vals13HL1S3sp04path2pp1P4vals2HP2HL4Hpp14Hpp23Hlo3HhiS3sp04SPlo4SPhi4path4vals2HLS3sp04SPlo4SPhi4path4vals2HL5vals13HL1S3sp04SPlo4SPhi4path4vals2HLS3sp04path2pp4vals2HL4Hpp15vals13HL1". (* [comment removed for export] *)
  #[using="Hvsp Hh Hlazy SPlo SPhi"] Lemma re_segBC : ltac2:(CDefT.buildp (gd_tbl_P_stdio_readerr_tail ()) "Ppath,(0.(1.&8.))Ppp,(1.&40.)PP,$1:.PT,$2<.Pt8,(0.(1.&8.))Pvals,(0.(1.&40.))PR,(2.&5.(1.&40.))PM,P,(1.&40.)(3.(1.&8.))P,(4.$1:.(1;.(6.(1.&8.)R8.))R6.)P,(1<.(1=.=R7.)(1=.R7.+1????.))P,(31.(32.(1.&8.)(12.&8.=)R:.))P,(4.$5.(6.(1.&40.)R6.)#27.)P,(4.(1.&40.)(7.R7.#0.)Vsp0,)P,(4.(1.&40.)(7.R8.#2.)R<.)P,(1=.(22.&40.Vsp0,)(22.&40.R=.))P,(1=.(24.(24.(22.&40.R>.)R=.)+8.)(24.(22.&40.Vsp0,)+400000.))P,(8.(9.R;.)$39.R:.)P,(;.$<.(9.R<.)R:.$3:.)P,(4.(3.(0.(1.&8.)))(20.$<.R;.R11.(2?.(6.(1.&8.)R12.)#1.))(23.(0.(1.&8.))(17.(1.&8.)R12.(25.(1.&8.)(12.&8.=)(26.(1.&8.))))))P,(4.(3.(0.(1.&8.)))(20.$<.R<.(12.&40.(24.(22.&40.R12.)R11.))#8.)(23.(0.(1.&8.))R?.))P,(35.R14.R13.R12.R11.)(>.$<.(?.(10.$11.R?.(12.&40.+1=478.)R>.(13.$<.))Vmodel,)R12.)")
(* [comment removed for export] *).
  Proof.
    intros path pp P T t8 vals R M HP HPr Hnonul HL P0 P2 Hpp1 Hpp2 HR HK Hstr Ht8 HF0.
    pose proof SPlo as Hlo. pose proof SPhi as Hhi. pose proof (u64_range pp) as Hppr.
    assert (WOKS : win_ok (ENV vals) 0 0 4194304 IHI).
    { unfold win_ok, IHI. cbn [ev ENV]. rewrite P0. lia. }
    (* [comment removed for export] *)
    run_blk_keep scr0 39%nat.
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
    assert (Hsrc : rdn RSEGS M' (Z_to_bv 64 0x1084e) 19 = Some PRE19).
    { rewrite (kimg_rdn RSEGS (ENV vals) _ knB ltac:(let i := kidx knB (is_kimg_cov 0x1084e 19) in exact i)
                 _ _ 0x1084e 19 HK eq_refl) by (cbn; lia). apply pre19_img. }
    assert (Hdst : store_ok RSEGS M' dst 19 = true).
    { pose proof (kwr_store_ok RSEGS (ENV vals) _ knB ltac:(let i := kidx knB (is_kwr_cov (EVar 0) (-560) 19) in exact i)
                    _ _ _ (-560) 19 HK eq_refl ltac:(lia) ltac:(cbn; lia)) as Hst.
      unfold adenot, v_addi in Hst. cbn [a_base a_off edenot ev ENV] in Hst. rewrite P0 in Hst.
      subst dst. replace (bv_unsigned sp0 - 560)%Z with (bv_unsigned sp0 + -560)%Z by lia. exact Hst. }
    assert (MC : mcH M' dst (Z_to_bv 64 0x1084e) 19 PRE19).
    { constructor; subst dst; rewrite ?u_small by lia; try (cbn; lia).
      - exact Hsrc.
      - exact Hdst. }
    lazymatch goal with |- realizes _ (mkCfg (mkst ?Rc _ _ _) _) _ =>
      assert (A1 : getr Rc 1 = (0x41d64 : word)) by (regv HR (1 : reg); apply bv_eq; reflexivity);
      assert (A10 : getr Rc 10 = dst)
        by (regv HR (10 : reg); subst dst; ed_lin ltac:(cbn [ev ENV]; rewrite ?P0); f_equal; lia);
      assert (A11 : getr Rc 11 = Z_to_bv 64 0x1084e) by (regv HR (11 : reg); reflexivity);
      assert (A12 : getr Rc 12 = Z_to_bv 64 19) by (regv HR (12 : reg); reflexivity);
      destruct (ref_memcpy M' dst (Z_to_bv 64 0x1084e) 19 _ (seg_rom RSEGS) MC Rc (0x41d64 : word)
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
    assert (HK2 : know_ok RSEGS (ENV vals) (wbytes M' dst PRE19) knC0).
    { subst dst. rewrite <- (re_memcpy1_denot vals M' P0).
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
    pose proof (env_app_know RSEGS vals (junk_vals R2) (blobs_ev BL) (wbytes M' dst PRE19) knC0
                  ltac:(rewrite HL; vm_compute; reflexivity) HK2) as HK.
    clear HK2.
    set (vals1 := vals ++ junk_vals R2) in *.
    assert (HL1 : length vals1 = 71%nat) by (subst vals1; rewrite length_app, junk_vals_length, HL; reflexivity).
    assert (Q0 : vals_ev vals1 0 = sp0) by (subst vals1; rewrite vals_ev_app_l by (rewrite HL; lia); exact P0).
    assert (Q2 : vals_ev vals1 2 = pp) by (subst vals1; rewrite vals_ev_app_l by (rewrite HL; lia); exact P2).
    clearbody vals1.
    change (Env (vals_ev vals1) (blobs_ev BL)) with (ENV vals1) in HR, HK.
    (* [comment removed for export] *)
    assert (Hstr2 : rdn RSEGS (wbytes M' dst PRE19) pp (length path + 1) = Some (path ++ [Z_to_bv 8 0])).
    { rewrite rdn_wbytes_out; [exact Hstr' | | |]; subst dst; rewrite ?PRE19_len; unorm; lia. }
    assert (Ht82 : rdn RSEGS (wbytes M' dst PRE19) (Z_to_bv 64 (bv_unsigned pp + P)) 8 = Some t8).
    { rewrite rdn_wbytes_out; [exact Ht8' | | |]; subst dst; rewrite ?PRE19_len; unorm; lia. }
    clear Hstr' Ht8' Hsrc Hdst MC. clearbody dst.
    set (M1 := wbytes M' dst PRE19) in *. clearbody M1. clear M' dst.
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
    set (dst := Z_to_bv 64 (bv_unsigned sp0 - 541)).
    assert (MC : mcH M3 dst (Z_to_bv 64 0x10861) 0 []).
    { constructor; subst dst; rewrite ?u_small by lia; cbn [length]; try lia; reflexivity. }
    lazymatch goal with |- realizes _ (mkCfg (mkst ?Rc _ _ _) _) _ =>
      assert (A1 : getr Rc 1 = (0x41d64 : word)) by (regv HR (1 : reg); apply bv_eq; reflexivity);
      assert (A10 : getr Rc 10 = dst)
        by (regv HR (10 : reg); subst dst; ed_lin ltac:(cbn [ev ENV]; rewrite ?Q0); f_equal; lia);
      assert (A11 : getr Rc 11 = Z_to_bv 64 0x10861) by (regv HR (11 : reg); reflexivity);
      assert (A12 : getr Rc 12 = Z_to_bv 64 0) by (regv HR (12 : reg); reflexivity);
      destruct (ref_memcpy M3 dst (Z_to_bv 64 0x10861) 0 _ (seg_rom RSEGS) MC Rc (0x41d64 : word)
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
    eapply (re_segDE path pp P T t8 vals2); eassumption.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

End Tail.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
