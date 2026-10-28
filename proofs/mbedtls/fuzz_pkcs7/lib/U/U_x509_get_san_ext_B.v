(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Walk AStep CellsX Image Asn1Aux Asn1AuxA X509Aux X509AuxB.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Spec Require Import Rep RepFacts RepName.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U Require Import UImg U_string U_asn1_get_tag U_asn1_get_len U_asn1_sequence_free U_asn1_free_named_data_list_shallow U_asn1_get_sequence_of_A U_x509_get_name_A U_x509_parse_san_A U_x509_parse_san U_x509_get_san_ext_A.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX Require Import LxExpr LxDec LxMem LxStep LxRun LxDenot LxSoundRun LxSum LxSoundSum LxTac.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LXP Require Import LxPTac.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LXP Require Import LxP_Flat.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LXP Require Import LxP_Flat2.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Import OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.LxhSyntax. #[local] Instance lxh_tab : OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.lx_hints := OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.lxh_parse "P194b61cb5562aad7 0 5 0 1 21 1 28 1 37 1 38 1"%lxh.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import LiaOrc. (* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= orc_lia. (* [comment removed for export] *)
Local Ltac dlia ::= orc_dlia. (* [comment removed for export] *)
Local Ltac plia ::= orc_plia. (* [comment removed for export] *)
Local Ltac lia_nodisj ::= orc_dlia. (* [comment removed for export] *)
Local Ltac clear_disj ::= fc_clear_disj. (* [comment removed for export] *)
Local Ltac prune_disj ::= fc_prune_disj. (* [comment removed for export] *)
Ltac2 gd_tbl_P_x509_get_san_ext_B () : Init.string Init.list := ["Corelib.Init.Datatypes.list"; "Corelib.Numbers.BinNums.Z"; "stdpp.bitvector.definitions.bv"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.cell"; "Corelib.Init.Datatypes.option"; "LinuxProcessSemantics.LinuxProcessSem.State.Model"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.HST"; "RocqVerifyHarness.AgentSubmission.U.UImg.usegs"; "RocqVerifyHarness.AgentSubmission.U.U_x509_get_san_ext_A.ninv"; "RocqVerifyHarness.AgentSubmission.Lib.Step.rw_cells"; "RocqVerifyHarness.AgentSubmission.Spec.RepFacts.seq_cells"; "Corelib.Init.Logic.or"; "Corelib.Init.Logic.and"; "Corelib.Init.Logic.eq"; "Corelib.Init.Datatypes.nil"; "Stdlib.ZArith.BinInt.Z.le"; "Stdlib.ZArith.BinInt.Z.add"; "Corelib.Init.Datatypes.cons"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C8"; "stdpp.bitvector.definitions.Z_to_bv"; "Stdlib.ZArith.BinInt.Z.lt"; "RocqVerifyHarness.AgentSubmission.Lib.AEvt.aevtM"; "RocqVerifyHarness.AgentSubmission.U.U_x509_get_san_ext_A.x509_get_san_ext_post"; "RocqVerifyHarness.AgentSubmission.Lib.MState.MS"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.mkR"; "stdpp.bitvector.definitions.bv_unsigned"; "Corelib.Init.Datatypes.None"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.seg_rom"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.CB"; "Corelib.Init.Datatypes.nat"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.cells_size"; "RocqVerifyHarness.AgentSubmission.U.U_x509_get_san_ext_A.frame_hi"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.stk"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.mem_inv"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.mo_frame"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.heap_top"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.HEAP"; "RocqVerifyHarness.AgentSubmission.U.U_x509_get_san_ext_A.nLBof"; "RocqVerifyHarness.AgentSubmission.Lib.Asn1Aux.heap_presx"; "Corelib.Init.Datatypes.prod"; "Corelib.Init.Datatypes.pair"; "Stdlib.Lists.List.hd"; "RocqVerifyHarness.AgentSubmission.Spec.RepFacts.seq_lseg"; "Stdlib.Lists.List.NoDup"; "RocqVerifyHarness.AgentSubmission.U.U_x509_get_san_ext_A.nfresh"].


Section Walk.
  Variable L : heap_layout.
  Variable HI : heap_iface usegs L.
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) (mo : Model)
            (h : HST usegs L HI) (LB : list blk) (PP CUR P END BUF lo : Z) (bs : list byte).
  Notation CTX := (ext_ctx usegs L HI U_CALLOC U_FREE sp tp h LB PP CUR P END BUF lo bs).
  Hypothesis HC : CTX.

  Notation X := [(PP, PP + 8); (CUR, CUR + 32)].
  Notation POST := (x509_get_san_ext_post usegs L HI ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc h LB PP CUR P END BUF lo m mo).
  Notation SPF := (Z_to_bv 64 (bv_unsigned sp + -224)).
  Notation INV := (ninv L HI ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m mo h LB PP CUR END BUF lo bs).
  Notation K4W := (Z_to_bv 64 (-9570)) (only parsing).
  Notation K7W := (Z_to_bv 64 (-9472)) (only parsing).
  Notation K8W := (Z_to_bv 64 (-8320)) (only parsing).
  Notation K9W := (Z_to_bv 64 (-9578)) (only parsing).
  Let sync_W' := sync_W L HI sp tp m h LB PP CUR P END BUF lo bs HC.
  Let presx_W' := presx_W L HI sp tp m h LB PP CUR P END BUF lo bs HC.
  Let heap_W' := heap_W L HI sp tp h LB PP CUR P END BUF lo bs HC.
  Let snoc_facts' := snoc_facts L HI sp tp h LB PP CUR P END BUF lo bs HC.
  Let others_apart' := others_apart L HI sp tp h LB PP CUR P END BUF lo bs HC.
  Let cur_wrange' := cur_wrange L HI sp tp h LB PP CUR P END BUF lo bs HC.
  Let headrep_pres' := headrep_pres L HI sp tp h LB PP CUR P END BUF lo bs HC.
  Let headrep_presx' := headrep_presx L HI sp tp h LB PP CUR P END BUF lo bs HC.
  Let presx_call' := presx_call L HI sp tp h LB PP CUR P END BUF lo bs HC.
  Let cur_cases' := cur_cases L HI sp tp h LB PP CUR P END BUF lo bs HC.
  Let in_block_below' := in_block_below L HI sp tp h LB PP CUR P END BUF lo bs HC.
  Let close_nodes' := close_nodes sp LB PP CUR END BUF lo bs.
  Let headrep_snoc' := headrep_snoc sp PP CUR END BUF lo bs.
  Let presx_munch' := presx_munch L sp LB PP CUR.
  Ltac chk :=
    let K := fresh "K" in if_cases K; zify_cond K;
    [ exfalso; rewrite ?land_7_mod in K; first [ clear_disj; lia | lia ] | clear K ].

  Ltac open_ninv INV :=
    pose proof INV as INVc;
    (flat constr:(INVc) 19%nat; flclear INVc; intros HH HT HND HFR HCF HHD HLS' F0 FB SZB FS SZS FT FRH ST MI HBUF HPX MF);
    pose proof (heap_mok _ _ HI _ _ _ _ HH) as MK; pose proof (conj HH I) as HHbox;
    pose proof HCF as HCFc; (flat constr:(HCFc) 7%nat; flclear HCFc; intros CAL CPOS C32 CPP CBF CSTK _);
    try unfold frame_hi in FRH.

  (* [comment removed for export] *)
  Ltac start_W cur :=
    lazymatch goal with |- aevtM _ _ _ (MS _ _ _ _ _ ?mx _) =>
      pose proof (munch_refl (W sp PP cur) mx) as MU; unfold W in MU; pose proof (wmono_refl usegs mx) as WM end.

  (* [comment removed for export] *)
  Ltac wsync :=
    lazymatch goal with |- aevtM _ _ _ (MS _ _ _ _ _ ?mx _) =>
      lazymatch goal with
      | HHbox : HEAP _ _ _ ?hc ?LBx ?mm ?moc /\ True, HT : heap_top _ _ _ ?hc = _, HCF : curF _ _ _ _ _ _ ?nodes ?cur,
        HND : List.NoDup ?nodes, HFR : nfresh _ _ ?nodes,
        MU : munch _ ?mm mx, WM : wmono _ ?mm mx, HHD : headrep CUR END BUF ?mm ?nodes,
        HLS' : seq_lseg _ ?mm _ BUF END (removelast ?nodes) _, HPX : heap_presx _ _ LB _ _ m ?mm |- _ =>
          let A := fresh "HH" in let B := fresh "HHD" in let C := fresh "HLS'" in let D := fresh "HPX" in
          let HS := fresh "HS" in
          assert (HS : forall b, In b (nLBof LB nodes) -> In b LBx)
            by first [ exact (fun b Hb => Hb) | exact (fun b Hb => or_intror Hb) | solve_sub ];
          repeat match goal with H : HEAP _ _ _ _ _ _ _ |- _ => clear H end;
          repeat match goal with H : MOK _ |- _ => clear H end;
          (flat constr:((sync_W' _ _ _ _ _ _ _ _ _ (proj1 HHbox) HT HS HND HFR HCF HHD HLS' HPX MU WM)) 4%nat; intros A B C D); clear HS;
          clear HHbox HHD HLS' HPX MU WM;
          match goal with HHn : HEAP _ _ _ _ _ mx _ |- _ => pose proof (conj HHn I) as HHbox; pose proof (heap_mok _ _ HI _ _ _ _ HHn) as MK end;
          rename A into HH; rename B into HHD; rename C into HLS'; rename D into HPX;
          pose proof (munch_refl (W sp PP cur) mx) as MU; unfold W in MU; pose proof (wmono_refl usegs mx) as WM
      end
    end.

  (* [comment removed for export] *)
  Ltac rebuild_ninv INVn :=
    lazymatch goal with |- aevtM _ ?mox _ (MS _ _ _ _ _ ?mx _) =>
    lazymatch goal with
    | HH : HEAP _ _ _ ?hc (nLBof LB ?nodes) mx mox, HCF : curF _ _ _ _ _ _ ?nodes ?cur,
      F0 : rw_cells _ mx (bv_unsigned sp + -224) [CB 8 ?j0], FB : rw_cells _ mx (bv_unsigned sp + -216) ?fb,
      FS : rw_cells _ mx (bv_unsigned sp + -192) ?fs, FT : rw_cells _ mx (bv_unsigned sp + -112) [C8 ?tl] |- _ =>
        assert (INVn : INV mx mox hc nodes cur j0 fb fs tl);
        [ unfold ninv; (flsplit; repeat match goal with |- _ /\ _ => split end); try assumption;
          try (simpl_sizes; reflexivity);
          try (etransitivity; eassumption); try (eapply mo_frame_trans; eassumption) | ]
    end end.

  (* [comment removed for export] *)
  Definition BodyOb (p : Z) : Prop :=
    forall (nodes : list Z) (cur : Z) (ct cpad : word) (cl cp : Z) (j0 : list byte) (fb fs : list cell) (tl : word)
      (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word) (mm : mem) (moc : Model) (hc : HST usegs L HI),
    INV mm moc hc nodes cur j0 fb fs tl -> rw_cells usegs mm cur (seq_cells ct cpad cl cp 0) ->
    (cp = 0 /\ cl = 0 /\ nodes = []) \/ (BUF <= cp /\ 0 <= cl /\ cp + cl <= END) ->
    rw_cells usegs mm PP [C8 (Z_to_bv 64 p)] -> P <= p -> p < END ->
    aevtM usegs moc POST
      (MS (mkR x1 SPF gp tp x5 x6 x7 (Z_to_bv 64 CUR) (Z_to_bv 64 END) x10 x11 x12 x13 x14 x15 x16 x17
             (Z_to_bv 64 (-9570)) (Z_to_bv 64 PP) (Z_to_bv 64 (-1)) (Z_to_bv 64 cur) (Z_to_bv 64 128) (Z_to_bv 64 4)
             (Z_to_bv 64 (-9472)) (Z_to_bv 64 (-8320)) (Z_to_bv 64 (-9578)) (Z_to_bv 64 p) x28 x29 x30 x31)
          F (Z_to_bv 64 0x2880c) fc None mm (seg_rom usegs))
(* [comment removed for export] *).

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00<0>L11186692248.1L19026237720.1L20944498222.4L30467547904.2L32923104513.5L45172172714.4L45674614936.1L48476763649.5L55102295192.1L59505226625.5L61492275334.2L8848177921.5 00000400800D00J00[00g00k01<01@01Q01W01hS2spS2spS1P3END1p2HpS1r2HrS1L2sp2lo3HLS3SLOS1P3END1p2HpS2spS1L2sp2lo3HLS3SLOS2spS1L2sp2lo3HLS3SLOS1r2HrS1L2sp2lo3HLS3SLO". (* [comment removed for export] *)
  Lemma epi_gen : ltac2:(CDefT.buildp (gd_tbl_P_x509_get_san_ext_B ()) "Pr,$1.Pp,$1.Pnodes,(0.$1.)Pt,(2.&40.)Ppd,(2.&40.)Pl,$1.Ppv,$1.Pj0,(0.(2.&8.))Pfb,(0.$3.)Pfs,(0.$3.)Ptl,(2.&40.)Px1,(2.&40.)Px5,(2.&40.)Px6,(2.&40.)Px7,(2.&40.)Px8,(2.&40.)Px9,(2.&40.)Px11,(2.&40.)Px12,(2.&40.)Px13,(2.&40.)Px14,(2.&40.)Px15,(2.&40.)Px16,(2.&40.)Px17,(2.&40.)Px18,(2.&40.)Px19,(2.&40.)Px20,(2.&40.)Px21,(2.&40.)Px22,(2.&40.)Px23,(2.&40.)Px24,(2.&40.)Px25,(2.&40.)Px26,(2.&40.)Px27,(2.&40.)Px28,(2.&40.)Px29,(2.&40.)Px30,(2.&40.)Px31,(2.&40.)Pmm,P,(2.&40.)(4.(2.&8.))Pmoc,$5.Phc,(6.$7.VL,VHI,)P,(9.$7.R3.(10.(19.&40.Vsp,)->0.)(11.$3.(1<.#8.R22.)(>.$3.)))P,(9.$7.R4.(10.(19.&40.Vsp,)-=8.)R22.)P,(=.$1=.(1>.R23.)#18.)P,(9.$7.R6.(10.(19.&40.Vsp,)-<0.)R23.)P,(=.$1=.(1>.R24.)#50.)P,(9.$7.R8.(10.(19.&40.Vsp,)-70.)(11.$3.(12.R24.)(>.$3.)))P,(9.$7.R9.(10.(19.&40.Vsp,)-68.)(1?.Vra,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,))P,(20.$7.R:.Vlo,(10.(19.&40.Vsp,)->0.))P,(21.$7.R;.)P,(22.Vmo,R;.)P,(=.$1.(23.$7.VL,VHI,R;.)(23.$7.VL,VHI,Vh,))P,(24.$7.VL,VHI,R<.(25.VLB,R32.)R>.R=.)P,(26.$7.VL,VLB,(19.&40.Vsp,)(11.(27.$1.$1.)(28.$1.$1.VPP,(10.VPP,+8.))(11.(27.$1.$1.)(28.$1.$1.VCUR,(10.VCUR,+20.))(>.(27.$1.$1.))))Vm,R?.)P,(<.(14.-3000.R36.)(?.R36.=))P,(9.$7.R11.VPP,(11.$3.(12.(13.&40.R36.))(>.$3.)))P,(<.(?.VP,R37.)(?.R37.VEND,))P,(9.$7.R13.VCUR,(:.R36.R35.R34.R33.(29.$1.=R37.)))P,(;.(<.(=.$1.R34.=)(<.(=.$1.R35.=)(=.(0.$1.)R38.(>.$1.))))(<.(?.VBUF,R34.)(<.(?.=R35.)(?.(10.R34.R35.)VEND,))))P,(2:.$7.R15.(25.VLB,R39.)VBUF,VEND,R39.=)P,(2;.$1.R3:.)P,(2<.VL,VLB,R3;.)(15.$7.R17.(16.$7.VL,VHI,Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,Vh,VLB,VPP,VCUR,VP,VEND,VBUF,Vlo,Vm,Vmo,)(17.(18.R33.(13.&40.(10.(19.&40.Vsp,)->0.))Vgp,Vtp,R32.R31.R30.R2?.R2>.(13.&40.R3>.)R2=.R2<.R2;.R2:.R29.R28.R27.R26.R25.R24.R23.R22.R21.R20.R1?.R1>.R1=.R1<.R1;.R1:.R19.)VF,(13.&40.+28938.)Vfc,(1:.(2.&40.))R18.(1;.$7.)))")
(* [comment removed for export] *).
  Proof.
    intros r p nodes t pd l pv j0 fb fs tl x1 x5 x6 x7 x8 x9 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 mm moc hc
      F0 FB SZB FS SZS FT FRH ST MI MF HT HH HPX Hr HPP Hp HCUR HCB HLSG HND HFR.
    open_ectx HC. pose proof (heap_mok _ _ HI _ _ _ _ HH) as MK. unfold frame_hi in FRH.
    (* [comment removed for export] *)
    pose proof (stk_release _ _ _ _ _ ST F0 ltac:(clear -SLO HLS; lia)) as ST1. cbn [cells_size csize Nat.add] in ST1.
    replace (bv_unsigned sp + -224 + Z.of_nat 8) with (bv_unsigned sp + -216) in ST1 by (clear; lia).
    pose proof (stk_release _ _ _ _ _ ST1 FB ltac:(clear -SLO HLS; lia)) as ST2. rewrite SZB in ST2.
    replace (bv_unsigned sp + -216 + Z.of_nat 24) with (bv_unsigned sp + -192) in ST2 by (clear; lia).
    pose proof (stk_release _ _ _ _ _ ST2 FS ltac:(clear -SLO HLS; lia)) as ST3. rewrite SZS in ST3.
    replace (bv_unsigned sp + -192 + Z.of_nat 80) with (bv_unsigned sp + -112) in ST3 by (clear; lia).
    pose proof (stk_release _ _ _ _ _ ST3 FT ltac:(clear -SLO HLS; lia)) as ST4. cbn [cells_size csize Nat.add] in ST4.
    replace (bv_unsigned sp + -112 + Z.of_nat 8) with (bv_unsigned sp + -104) in ST4 by (clear; lia).
    clear ST ST1 ST2 ST3 F0 FB FS FT.
    (* [comment removed for export] *)
    assert (LXSUMS : forall AL, Forall (summary_okG usegs AL []) (@nil summary)) by (intros AL; constructor).
    rewrite TP. apply (lxp_aevtM_of_evt usegs moc _ _ MK).
    lx_run_tac (PLANS (@nil Z) [] 40%N (@nil summary)); lx_tree.
    all: apply evt_done; cbv beta; rewrite <- TP.
    all: lazymatch goal with E : @eq mem ?mx ?mc0 |- _ => subst mx end.
    lazymatch goal with STx : stk _ mm lo (bv_unsigned sp) |- _ => rename STx into STf end.
    apply aevtM_done. unfold x509_get_san_ext_post. flexi 15%nat.
    exists mm, moc, hc, r, p, t, pd, l, pv, (hd 0 nodes), nodes.
    split; [reflexivity|].
    (flsplit; repeat match goal with |- _ /\ _ => split end); try assumption.
    - reflexivity.
    - clear -Hr; lia. - clear -Hr; lia. - clear -Hp; lia. - clear -Hp; lia.
    - reflexivity.
    - apply seq_lseg_chain in HLSG. exact HLSG.
    - intros y Hy. exact (proj2 (proj2 (HFR y Hy))).
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Lemma epi_inv : ltac2:(CDefT.buildp (gd_tbl_P_x509_get_san_ext_B ()) "Pr,$1.Pp,$1.Pnodes,(0.$1.)Pcur,$1.Pct,(2.&40.)Pcpad,(2.&40.)Pcl,$1.Pcp,$1.Pj0,(0.(2.&8.))Pfb,(0.$3.)Pfs,(0.$3.)Ptl,(2.&40.)Px1,(2.&40.)Px5,(2.&40.)Px6,(2.&40.)Px7,(2.&40.)Px8,(2.&40.)Px9,(2.&40.)Px11,(2.&40.)Px12,(2.&40.)Px13,(2.&40.)Px14,(2.&40.)Px15,(2.&40.)Px16,(2.&40.)Px17,(2.&40.)Px18,(2.&40.)Px19,(2.&40.)Px20,(2.&40.)Px21,(2.&40.)Px22,(2.&40.)Px23,(2.&40.)Px24,(2.&40.)Px25,(2.&40.)Px26,(2.&40.)Px27,(2.&40.)Px28,(2.&40.)Px29,(2.&40.)Px30,(2.&40.)Px31,(2.&40.)Pmm,P,(2.&40.)(4.(2.&8.))Pmoc,$5.Phc,(6.$7.VL,VHI,)P,(8.VL,VHI,Vra,Vsp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,Vm,Vmo,Vh,VLB,VPP,VCUR,VEND,VBUF,Vlo,Vbs,R3.R2.R1.R28.R27.R22.R21.R20.R1?.)P,(9.$7.R4.R28.(:.R27.R26.R25.R24.=))P,(;.(<.(=.$1.R25.=)(<.(=.$1.R26.=)(=.(0.$1.)R2:.(>.$1.))))(<.(?.VBUF,R25.)(<.(?.=R26.)(?.(10.R25.R26.)VEND,))))P,(9.$7.R6.VPP,(11.$3.(12.(13.&40.R2<.))(>.$3.)))P,(<.(?.VP,R2=.)(?.R2=.VEND,))P,(<.(14.-3000.R2?.)(?.R2?.=))(15.$7.R8.(16.$7.VL,VHI,Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,Vh,VLB,VPP,VCUR,VP,VEND,VBUF,Vlo,Vm,Vmo,)(17.(18.R24.(13.&40.(10.(19.&40.Vsp,)->0.))Vgp,Vtp,R23.R22.R21.R20.R1?.(13.&40.R30.)R1>.R1=.R1<.R1;.R1:.R19.R18.R17.R16.R15.R14.R13.R12.R11.R10.R?.R>.R=.R<.R;.R:.)VF,(13.&40.+28938.)Vfc,(1:.(2.&40.))R9.(1;.$7.)))")
(* [comment removed for export] *).
  Proof.
    intros r p nodes cur ct cpad cl cp j0 fb fs tl x1 x5 x6 x7 x8 x9 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 mm moc hc
      INV HCUR HCB HPP Hp Hr.
    open_ninv INV. clear INV.
    edestruct close_nodes' as [(t & pd & l & pv & HHEAD & HB) HLn]; [exact HCF| exact HHD| exact HLS'| exact HCUR| exact HCB|].
    eapply epi_gen; eassumption.
  Qed.

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00J0@D10333304081.154D1101800120.151 D31496456979.154D35612792593.154D43633546478.151D46259122193.154D46471466641.154D48591303134.154D56795294278.154D57142437777.154D9491433734.151 L10333304081.145L13977709985.0  L20653842230.2  L20660446595.2  L31166248013.142L35612792593.145L4111393891.7   L46259122193.145L46471466641.145L48591303134.145L52067113769.142L56795294278.145L57142437777.145L59331717639.7  L9816906285.142 00000100Y00Z00[01B01C01D01E01F01G01j03;03<03B03I04W05h06?07P08a09S09T0:J0;[0<20=@FS2sp2PP3CUR2bs3cur2fb2fs3SZB3SZS4CPOS2HBFFS2sp2PP3CUR2bs3cur2fb2fs3SZB3SZS3C322HBFFFFFS2sp2PP3CUR2bs3cur2fb2fs3SZB3SZS2HBS1L2sp2PP3CUR2lo2bs3cur2fb2fs3SZB3SZS4CPOS2HD3HLS3PPB4CURB3SLO3SPR2HB5Ha_st5Hl_stSS2r'1ES2r'2R2S2sp2PP3CUR1P3END3BUF2bs1p3cur2fb2fs2Hp3SZB3SZS4CPOS2B12B32B43PPB4CURB3NZ33SPRS1L2sp2PP3CUR2lo2bs3cur2fb2fs3SZB3SZS4CPOS2HD3HLS3PPB4CURB3SLO3SPR2HB5Ha_st5Hl_stS1P3END3BUF1p2Hp2B13NZ3S1L2sp2PP3CUR2lo2bs3cur2fb2fs3SZB3SZS4CPOS2HD3HLS3PPB4CURB3SLO3SPR2HB5Ha_st5Hl_stS1L2sp2PP3CUR2lo2bs3cur2fb2fs3SZB3SZS4CPOS2HD3HLS3PPB4CURB3SLO3SPR2HB5Ha_st5Hl_stS2sp2PP3CUR2bs3cur2fb2fs3SZB3SZS2HD2HB5Ha_st5Hl_stFS2sp2PP3CUR3BUF2bs3cur2fb2fs3SZB3SZS2HD2HB5Ha_st5Hl_stS1L2sp2PP3CUR2lo2bs3cur2fb2fs3SZB3SZS4CPOS2HD3HLS3PPB4CURB3SLO3SPR2HB5Ha_st5Hl_stS1P3END3BUF1p2Hp2B13NZ3S2sp2PP3CUR1P3END3BUF2bs1p3cur2fb2fs2Hp3SZB3SZS4CPOS2B12B32B43PPB4CURB3NZ33SPR". (* [comment removed for export] *)
  Lemma exit_walk : forall (p : Z) (nodes : list Z) (cur : Z) (ct cpad : word) (cl cp : Z) (j0 : list byte) (fb fs : list cell) (tl : word)
      (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x22 x23 x24 x25 x26 x28 x29 x30 x31 : word) (mm : mem) (moc : Model) (hc : HST usegs L HI),
    INV mm moc hc nodes cur j0 fb fs tl -> rw_cells usegs mm cur (seq_cells ct cpad cl cp 0) ->
    (cp = 0 /\ cl = 0 /\ nodes = []) \/ (BUF <= cp /\ 0 <= cl /\ cp + cl <= END) ->
    rw_cells usegs mm PP [C8 (Z_to_bv 64 p)] -> P <= p <= END ->
    aevtM usegs moc POST
      (MS (mkR x1 SPF gp tp x5 x6 x7 (Z_to_bv 64 CUR) (Z_to_bv 64 END) x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 (Z_to_bv 64 cur) x22 x23 x24 x25 x26 (Z_to_bv 64 p) x28 x29 x30 x31)
          F (Z_to_bv 64 0x2890c) fc None mm (seg_rom usegs))
(* [comment removed for export] *).
  Proof.
    intros p nodes cur ct cpad cl cp j0 fb fs tl x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x22 x23 x24 x25 x26 x28 x29 x30 x31 mm moc hc
      INV HCUR HCB HPP Hp.
    open_ninv INV. clear INV. open_ectx HC. unfold seq_cells in HCUR.
    pose proof (bytes_at_bound _ _ _ _ HBUF) as BB.
    start_W cur.
    zstep. chk. zstep. zstep. chk.
    zstep.
    wsync.
    zstep. zstep. zstep. zstep. zstep. zstep. zstep.
    destruct (x509_mismatch_select p END 18446744073709542042 ltac:(clear -Hp B1 NZ3; lia) ltac:(clear -Hp B1 NZ3; lia) ltac:(clear; lia))
      as (r' & ER & R1 & R2). rewrite ER. clear ER.
    rebuild_ninv INV2.
    eapply epi_inv; try exact INV2; try eassumption.
    destruct (Z.eq_dec p END) as [E|NE]; [apply R1 in E; clear -E; lia| specialize (R2 NE); clear -R2; lia].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00S0@D20175148606.184D20974617009.184D3981850291.184 D42502165041.184D43623715735.175D43636348975.157D55506784934.184D56420723160.181D63023255566.181D6364240049.184 D64412254129.184D6576609073.184 D9491433734.181 L13684441372.1  L1577139281.1   L19711631260.1  L20175148606.175L20974617009.175L22615520689.5  L25760451453.5  L32759928135.2  L33277234838.4  L35262143644.1  L38221604602.5  L42502165041.175L49168543.4     L55506784934.175L59340219036.1  L62959071656.2  L6364240049.175 L64412254129.175L64481468488.1  L65357366945.0  L6576609073.175 L8680020508.1   00000100200300401;02B02C02l03U03V03W03X04<04@04D04H05;06M06_06o07707F07J07W08i09709n0:20:<0;N0<`0<d0<e0>70>;FFFFS1L2sp2PP3CUR2lo2bs3cur2fb2fs3SZB3SZS4CPOS3HLS3PPB4CURB3SLO3ACL3ACP3SPRS1L2sp2PP3CUR2lo2bs3cur2fb2fs3SZB3SZS4CPOS3HLS3PPB4CURB3SLO3ACL3ACP3SPRFS2sp2PP3CUR2bs3cur2fb2fs3SZB3SZS4CURB3HB0S2sp2PP3CUR2bs3cur2fb2fs3SZB3SZS4CURB3HB0FFFS2sp2PP3CUR2bs3cur2fb2fs3SZB3SZS3HB0S2spS2spS2spS2sp2PP3CUR2bs3cur2fb2fs3SZB3SZS2HD3HB05Ha_st5Hl_stS1L2sp2PP3CUR2lo2bs3cur2fb2fs3SZB3SZS4CPOS3HLS3PPB4CURB3SLO2HD3SPR3HB05Ha_st5Hl_stS2sp3BUF2lo2bs3DS3S1L2HI2sp1h4HTOPS2sp3SPAS2sp3CUR2lo3DS2S2spS1L2sp2lo3SLOS1L2sp2PP3CUR2lo2bs3cur2fb2fs3SZB3SZS4CPOS3HLS3PPB4CURB3SLO2HD3SPR3HB05Ha_st5Hl_stS2sp2PP2lo3DS1S2sp2PP3CUR3BUF2bs3cur2fb2fs3SZB3SZS2HD3HB05Ha_st5Hl_stS2spS3CUR4CURBS1L2sp2PP3CUR2lo2bs3cur2fb2fs3SZB3SZS4CPOS3HLS3PPB4CURB3SLO2HD3SPR3HB05Ha_st5Hl_stS1L2sp2PP3CUR2lo2bs3cur2fb2fs3SZB3SZS4CPOS3HLS3PPB4CURB3SLO2HD3SPR3HB05Ha_st5Hl_stS2spSS1L2sp2PP3CUR2lo2bs3cur2fb2fs3SZB3SZS4CPOS3HLS3PPB4CURB3SLO2HD3SPR3HB05Ha_st5Hl_stS2sp". (* [comment removed for export] *)
  Lemma fatal_walk : ltac2:(CDefT.buildp (gd_tbl_P_x509_get_san_ext_B ()) "Pr,$1.Pp,$1.Pnodes,(0.$1.)Pcur,$1.Pct,(2.&40.)Pcpad,(2.&40.)Pcl,$1.Pcp,$1.Pj0,(0.(2.&8.))Pfb,(0.$3.)Pfs,(0.$3.)Ptl,(2.&40.)Px1,(2.&40.)Px5,(2.&40.)Px6,(2.&40.)Px7,(2.&40.)Px9,(2.&40.)Px11,(2.&40.)Px12,(2.&40.)Px13,(2.&40.)Px14,(2.&40.)Px15,(2.&40.)Px16,(2.&40.)Px17,(2.&40.)Px18,(2.&40.)Px19,(2.&40.)Px20,(2.&40.)Px21,(2.&40.)Px22,(2.&40.)Px23,(2.&40.)Px24,(2.&40.)Px25,(2.&40.)Px26,(2.&40.)Px27,(2.&40.)Px28,(2.&40.)Px29,(2.&40.)Px30,(2.&40.)Px31,(2.&40.)Pmm,P,(2.&40.)(4.(2.&8.))Pmoc,$5.Phc,(6.$7.VL,VHI,)P,(8.VL,VHI,Vra,Vsp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,Vm,Vmo,Vh,VLB,VPP,VCUR,VEND,VBUF,Vlo,Vbs,R3.R2.R1.R27.R26.R21.R20.R1?.R1>.)P,(9.$7.R4.R27.(:.R26.R25.R24.R23.=))P,(;.(<.(=.$1.R24.=)(<.(=.$1.R25.=)(=.(0.$1.)R29.(>.$1.))))(<.(?.VBUF,R24.)(<.(?.=R25.)(?.(10.R24.R25.)VEND,))))P,(9.$7.R6.VPP,(11.$3.(12.(13.&40.R2;.))(>.$3.)))P,(<.(?.VP,R2<.)(?.R2<.VEND,))P,(<.(14.-3000.R2>.)(?.R2>.=))(15.$7.R8.(16.$7.VL,VHI,Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,Vh,VLB,VPP,VCUR,VP,VEND,VBUF,Vlo,Vm,Vmo,)(17.(18.R23.(13.&40.(10.(19.&40.Vsp,)->0.))Vgp,Vtp,R22.R21.R20.(13.&40.VCUR,)R1?.(13.&40.R2?.)R1>.R1=.R1<.R1;.R1:.R19.R18.R17.R16.R15.R14.R13.R12.R11.R10.R?.R>.R=.R<.R;.R:.)VF,(13.&40.+28998.)Vfc,(1:.(2.&40.))R9.(1;.$7.)))")
(* [comment removed for export] *).
  Proof.
    intros r p nodes cur ct cpad cl cp j0 fb fs tl x1 x5 x6 x7 x9 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 mm moc hc
      INV HCUR HCB HPP Hp Hr.
    open_ninv INV. clear INV. open_ectx HC.
    pose proof (bytes_at_bound _ _ _ _ HBUF) as BB.
    edestruct close_nodes' as [(t & pd & l & pv & HHEAD & HB) HLn]; [exact HCF| exact HHD| exact HLS'| exact HCUR| exact HCB|].
    clear HCUR HCB HHD HLS'. unfold seq_cells in HHEAD.
    zstep. chk. zstep. zstep. zstep. chk. zstep. zstep.
    pose proof (U_asn1_sequence_free_spec L HI HFREE HLS) as SPF'. unfold asn1_sequence_free_stmt, U_ASN1_SEQUENCE_FREE in SPF'.
    eapply aevtM_cut; [ eapply SPF' with (LB := nLBof LB nodes) (a := hd 0 nodes) (nodes := nodes) (lo := lo) (h := hc);
       rewrite ?(unsigned_lit (bv_unsigned sp + -224)) by dlia; try eassumption; try reflexivity | ].
    { apply seq_lseg_chain in HLn. exact HLn. }
    { clear -SLO HLS. lia. }
    { rewrite HT. clear -HTOP. lia. }
    { clear -SPA. lia. }
    clear SPF'.
    intros ms' mo' PO. unfold asn1_sequence_free_post in PO. destruct_exs PO. flat constr:(PO) 2%nat. flclear PO. intros E PO.
    injection E as E1 E2. subst ms' mo'.
    rewrite ?(unsigned_lit (bv_unsigned sp + -224)) in PO by dlia.
    flat constr:(PO) 6%nat. flclear PO. intros MI7 ST7 MF7 HT7 HH7 HP7.
    unfold nLBof in HH7, HP7. rewrite (lb_remove_all_new32 nodes LB HND) in HH7, HP7.
    lazymatch goal with |- _ (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) =>
      replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [ clear; lia | reflexivity ]) end.
    lazymatch goal with |- aevtM _ ?mox _ (MS _ _ _ _ _ ?mx _) => rename mx into m7; rename mox into mo7 end.
    match type of HH7 with HEAP _ _ _ ?hh _ _ _ => rename hh into h7 end.
    pose proof (heap_mok _ _ HI _ _ _ _ HH7) as MK7. clear MK HHbox. pose proof (conj HH7 I) as HHbox7.
    (* [comment removed for export] *)
    apply (heap_pres_rw_cells usegs L _ _ _ _ _ _ HP7) in F0; [| apply client_range_stack; clear; lia].
    apply (heap_pres_rw_cells usegs L _ _ _ _ _ _ HP7) in FB; [| apply client_range_stack; clear; lia].
    apply (heap_pres_rw_cells usegs L _ _ _ _ _ _ HP7) in FS; [| apply client_range_stack; clear; lia].
    apply (heap_pres_rw_cells usegs L _ _ _ _ _ _ HP7) in FT; [| apply client_range_stack; clear; lia].
    apply (heap_pres_rw_cells usegs L _ _ _ _ _ _ HP7) in FRH; [| apply client_range_stack; simpl_sizes; clear; lia].
    apply (heap_pres_rw_cells usegs L _ _ _ _ _ _ HP7) in HPP;
      [| simpl_sizes; eapply client_range_wsep; [exact CWPP| intros b Hb; exact Hb| clear -DS1; lia] ].
    apply (heap_pres_rw_cells usegs L _ _ _ _ _ _ HP7) in HHEAD;
      [| simpl_sizes; eapply client_range_wsep; [exact CWCUR| intros b Hb; exact Hb| clear -DS2; lia] ].
    apply (heap_pres_bytes_at usegs L _ _ _ _ _ _ HP7) in HBUF;
      [| eapply client_range_sep; [exact CRBUF| intros b Hb; exact Hb| clear -DS3; lia] ].
    assert (HPX7 : heap_presx usegs L LB (bv_unsigned sp) X m m7).
    { eapply heap_presx_trans; [exact HPX|]. eapply heap_presx_of_pres_sub; [exact HP7| intros b Hb; exact Hb| clear; lia| clear; lia]. }
    clear HPX ST MI HP7.
    assert (HCF0 : curF sp PP CUR BUF lo bs [] CUR).
    { unfold curF. split; [exact AL2|]. split; [exact NZ2|]. split; [clear -CURB; lia|]. split; [exact D1|]. split; [exact D3|].
      split; [exact DS2|]. left; split; reflexivity. }
    assert (HFR0 : nfresh L LB []) by (intros y Hy; destruct Hy).
    start_W CUR.
    zstep. zstep. zstep.
    pose proof (heap_W' [] CUR h7 (nLBof LB []) _ _ mo7 HFR0 HCF0 (proj1 HHbox7) ltac:(etransitivity; eassumption) ltac:(intros b Hb; exact Hb) MU WM) as HH8.
    pose proof (presx_W' [] CUR _ _ HFR0 HCF0 MU WM HPX7) as HPX8.
    eapply epi_gen with (nodes := []) (moc := mo7) (hc := h7); try eassumption.
    - eapply mo_frame_trans; eassumption.
    - etransitivity; eassumption.
    - destruct HB as [(E1 & E2 & _)|HB']; [left; (flsplit; repeat split); assumption || reflexivity| right; exact HB'].
    - exact I.
    - constructor.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
End Walk.

