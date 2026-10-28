(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Walk Asn1Aux Asn1AuxA X509Aux AStep CellsX.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Spec Require Import Rep RepFacts RepName.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U Require Import UImg U_asn1_get_tag U_asn1_get_len U_asn1_free_named_data_list_shallow U_x509_get_name_A.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX Require Import LxExpr LxDec LxMem LxStep LxRun LxDenot LxSoundRun LxSum LxSoundSum LxTac.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LXP Require Import LxPTac.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LXP Require Import LxP_Flat.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LXP Require Import LxP_Flat2.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Import OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.LxhSyntax. #[local] Instance lxh_tab : OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.lx_hints := OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.lxh_parse "P002bdb7398974b3b 0 5 0 1 35 1 36 1 43 1 44 1P01c4eb95e2bd38cf 2 35 0 6 0 1 1 1 37 1 38 1 45 1 46 1 0 4 0 1 2 1 45 1 46 1P03cfc005731cebf8 0 3 0 1 26 1 27 1P0b840411e4feaf51 2 35 0 6 0 1 1 1 37 1 38 1 45 1 46 1 0 4 0 1 2 1 45 1 46 1P16ea9d7d5fc79737 2 35 0 6 0 1 1 1 37 1 38 1 45 1 46 1 0 4 0 1 2 1 45 1 46 1P1daa87609be9e245 2 35 0 6 0 1 1 1 37 1 38 1 45 1 46 1 0 4 0 1 2 1 45 1 46 1P27e543fbdf3355f0 0 5 0 1 35 1 36 1 43 1 44 1P27e95c3e5d612ba2 0 3 0 1 26 1 27 1P332f53e02b744806 0 5 0 1 35 1 36 1 43 1 44 1P34e13131a36d9c2e 0 3 0 1 26 1 27 1P3ac517a107c53e0c 0 5 0 1 35 1 36 1 43 1 44 1P3b50bf202dad7759 0 3 0 1 26 1 27 1"%lxh.
Ltac2 gd_tbl_P_x509_get_name_B () : Init.string Init.list := ["Corelib.Init.Datatypes.list"; "Corelib.Numbers.BinNums.Z"; "stdpp.bitvector.definitions.bv"; "Corelib.Init.Datatypes.option"; "LinuxProcessSemantics.LinuxProcessSem.State.Model"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.HST"; "RocqVerifyHarness.AgentSubmission.U.UImg.usegs"; "RocqVerifyHarness.AgentSubmission.U.U_x509_get_name_A.ninv"; "stdpp.bitvector.definitions.Z_to_bv"; "RocqVerifyHarness.AgentSubmission.Lib.Step.rw_cells"; "RocqVerifyHarness.AgentSubmission.Spec.RepName.name_blob"; "Corelib.Init.Datatypes.cons"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.cell"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C8"; "Corelib.Init.Datatypes.nil"; "Corelib.Init.Logic.and"; "Stdlib.ZArith.BinInt.Z.le"; "Stdlib.ZArith.BinInt.Z.lt"; "RocqVerifyHarness.AgentSubmission.Lib.AEvt.aevtM"; "RocqVerifyHarness.AgentSubmission.U.U_x509_get_name_A.x509_get_name_post"; "RocqVerifyHarness.AgentSubmission.Lib.MState.MS"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.mkR"; "Stdlib.ZArith.BinInt.Z.add"; "stdpp.bitvector.definitions.bv_unsigned"; "Corelib.Init.Datatypes.None"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.seg_rom"].


Section Walk.
  Variable L : heap_layout.
  Variable HI : heap_iface usegs L.
  Hypothesis HCALLOC : hl_calloc L = U_CALLOC.
  Hypothesis HFREE : hl_free L = U_FREE.
  Variables (ra sp gp tp t0 t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : mem) (mo : Model) (h : HST usegs L HI) (LB : list blk)
            (PP CUR P END BUF lo : Z) (bs : list byte).
  Hypothesis B1 : BUF <= P.
  Hypothesis B3 : END <= BUF + Z.of_nat (length bs).
  Hypothesis B4 : BUF + Z.of_nat (length bs) < 2^63.
  Hypothesis D1 : PP + 8 <= CUR \/ CUR + 64 <= PP.
  Hypothesis D2 : PP + 8 <= BUF \/ BUF + Z.of_nat (length bs) <= PP.
  Hypothesis D3 : CUR + 64 <= BUF \/ BUF + Z.of_nat (length bs) <= CUR.
  Hypothesis PPB : 0 <= PP /\ PP + 8 <= 2^64.
  Hypothesis CURB : 0 <= CUR /\ CUR + 64 <= 2^64.
  Hypothesis AL1 : PP mod 8 = 0.
  Hypothesis AL2 : CUR mod 8 = 0.
  Hypothesis NZ1 : 0 < PP.
  Hypothesis NZ2 : 0 < CUR.
  Hypothesis NZ3 : 0 < BUF.
  Hypothesis SLO : lo <= bv_unsigned sp - 160 - hl_stack L.
  Hypothesis HLS : 0 <= hl_stack L.
  Hypothesis ACL : alloc_ceiling <= lo.
  Hypothesis ACP : 4096 < alloc_ceiling.
  Hypothesis HTOP : bv_unsigned sp <= heap_top usegs L HI h.
  Hypothesis SPA : bv_unsigned sp mod 16 = 0.
  Hypothesis DHI : hl_data_hi L <= alloc_ceiling.
  Hypothesis DIM1 : hl_img_lo L <= hl_data_lo L.
  Hypothesis DIM2 : hl_data_hi L <= hl_img_hi L.
  Hypothesis DS1 : PP + 8 <= lo \/ bv_unsigned sp <= PP.
  Hypothesis DS2 : CUR + 64 <= lo \/ bv_unsigned sp <= CUR.
  Hypothesis DS3 : BUF + Z.of_nat (length bs) <= lo \/ bv_unsigned sp <= BUF.
  Hypothesis CWPP : client_wrange L LB lo (heap_top usegs L HI h) PP 8.
  Hypothesis CWCUR : client_wrange L LB lo (heap_top usegs L HI h) CUR 64.
  Hypothesis CRBUF : client_range L LB lo BUF (Z.of_nat (length bs)).
  Hypothesis TP : tp = Z_to_bv 64 (hl_tp L).
  Hypothesis SPB : bv_unsigned sp < 2^64.
  Hypothesis HBR0 : Forall (fun b => block_range L (fst b) (snd b)) LB.

  Notation X := [(PP, PP + 8); (CUR, CUR + 64)].
  Notation POST := (x509_get_name_post usegs L HI ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc h LB PP CUR P END lo m mo).
  Notation SPF := (Z_to_bv 64 (bv_unsigned sp + -144)).
  Notation INV := (ninv L HI ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m mo h LB PP CUR BUF lo bs K1W K2W).
  Notation WW := (W sp PP).
  Let sync_W' := sync_W L HI sp m h LB PP CUR BUF lo bs D1 SLO HLS ACL HTOP DHI DIM1 DIM2 DS2 CWPP CWCUR HBR0.
  Let snoc_facts' := snoc_facts L HI sp h LB PP CUR BUF lo bs SLO HLS ACL DIM1 DIM2 CWPP CWCUR CRBUF SPB.
  Let others_apart' := others_apart L HI sp h LB PP CUR BUF lo bs ACL DIM1 DIM2 CWPP.
  Let cur_wrange' := cur_wrange L HI sp h LB PP CUR BUF lo bs DIM1 DIM2 CWCUR.
  Let headrep_pres' := headrep_pres L HI sp h LB CUR lo DS2 CWCUR.
  Let cur_cases' := cur_cases L sp LB PP CUR BUF lo bs DIM1 DIM2.
  Let close_nodes' := close_nodes sp LB PP CUR BUF lo bs.
  Let close_fin' := close_fin sp LB PP CUR BUF lo bs.
  Let headrep_snoc' := headrep_snoc sp PP CUR BUF lo bs.
  Let in_block_below' := in_block_below L LB HBR0.
  Let presx_munch' := presx_munch L sp LB PP CUR.

  Ltac open_ninv INV :=
    pose proof INV as INVc;
    (flat constr:(INVc) 16%nat; flclear INVc; intros HH HT HND HFR HCF HHD HLS' FRA FRS FRL FRH ST MI HBUF HPX MF);
    pose proof (heap_mok _ _ HI _ _ _ _ HH) as MK; pose proof (conj HH I) as HHbox;
    pose proof HCF as HCFc; (flat constr:(HCFc) 7%nat; flclear HCFc; intros CAL CPOS C64 CPP CBF CSTK _);
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
        MU : munch _ ?mm mx, WM : wmono _ ?mm mx, HHD : headrep CUR ?mm ?nodes,
        HLS' : name_lseg _ ?mm _ (removelast ?nodes) _, HPX : heap_presx _ _ LB _ _ m ?mm |- _ =>
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
      FRA : rw_cells _ mx (bv_unsigned sp + -144) [CB 8 ?j8; _; _], FRS : rw_cells _ mx (bv_unsigned sp + -120) [C8 ?slen],
      FRL : rw_cells _ mx (bv_unsigned sp + -112) [C8 ?alen] |- _ =>
        assert (INVn : INV mx mox hc nodes cur slen alen j8);
        [ unfold ninv; (flsplit; repeat match goal with |- _ /\ _ => split end); try assumption;
          try (etransitivity; eassumption); try (eapply mo_frame_trans; eassumption) | ]
    end end.

  Ltac join_frame FR :=
    lazymatch goal with
    | FRA : rw_cells _ ?mx (bv_unsigned sp + -144) _, FRS : rw_cells _ ?mx (bv_unsigned sp + -120) _,
      FRL : rw_cells _ ?mx (bv_unsigned sp + -112) _, FRH : rw_cells _ ?mx (bv_unsigned sp + -104) _ |- _ =>
        let F1 := fresh "FRx" in let F2 := fresh "FRy" in
        chunk_join FRL FRH F1; chunk_join FRS F1 F2; chunk_join FRA F2 FR
    end.

  (* [comment removed for export] *)
  Lemma err_walk : ltac2:(CDefT.buildp (gd_tbl_P_x509_get_name_B ()) "Pnodes,(0.$1.)Pcur,$1.Pslen,(2.&40.)Palen,(2.&40.)Pj8,(0.(2.&8.))PJ,(0.(2.&8.))PMG,(2.&8.)PP7,(0.(2.&8.))Pr,$1.Pp,$1.Px1,(2.&40.)Px5,(2.&40.)Px6,(2.&40.)Px7,(2.&40.)Px8,(2.&40.)Px9,(2.&40.)Px10,(2.&40.)Px11,(2.&40.)Px12,(2.&40.)Px13,(2.&40.)Px14,(2.&40.)Px15,(2.&40.)Px16,(2.&40.)Px17,(2.&40.)Px18,(2.&40.)Px19,(2.&40.)Px21,(2.&40.)Px22,(2.&40.)Px23,(2.&40.)Px24,(2.&40.)Px25,(2.&40.)Px26,(2.&40.)Px28,(2.&40.)Px29,(2.&40.)Px30,(2.&40.)Px31,(2.&40.)Pmm,P,(2.&40.)(3.(2.&8.))Pmoc,$4.Phc,(5.$6.VL,VHI,)P,(7.VL,VHI,Vra,Vsp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,Vm,Vmo,Vh,VLB,VPP,VCUR,VBUF,Vlo,Vbs,(8.&40.+????????????=<1:.)(8.&40.+????????????=<20.)R3.R2.R1.R27.R26.R25.R24.R23.)P,(9.$6.R4.R27.(:.R23.=R22.R21.))P,(9.$6.R5.VPP,(;.$<.(=.(8.&40.R20.))(>.$<.)))P,(?.(10.VP,R21.)(10.R21.VEND,))P,(?.(11.-3000.R23.)(11.R23.=))(12.$6.R7.(13.$6.VL,VHI,Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,Vh,VLB,VPP,VCUR,VP,VEND,Vlo,Vm,Vmo,)(14.(15.R22.(8.&40.(16.(17.&40.Vsp,)-90.))Vgp,Vtp,R21.R20.R1?.R1>.(8.&40.R24.)R1<.R1;.R1:.R19.R18.R17.R16.R15.R14.R13.R1=.R12.R11.(8.&40.VCUR,)R?.R>.R=.R10.R<.R;.R:.R9.)VF,(8.&40.+27?84.)Vfc,(18.(2.&40.))R8.(19.$6.)))")
(* [comment removed for export] *).
  Proof.
    intros nodes cur slen alen j8 J MG P7 r p x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x21 x22 x23 x24 x25 x26 x28 x29 x30 x31 mm moc hc
      INV HCB HPP Hp Hr.
    open_ninv INV. clear INV.
    edestruct (close_nodes) as [(j48 & mg & p7 & HHEAD) HLn]; [exact HCF| exact HHD| exact HLS'| exact HCB|].
    clear HCB HHD HLS'. clear HHbox.
    (* [comment removed for export] *)
    clear sync_W' snoc_facts' others_apart' cur_wrange' headrep_pres' cur_cases' close_nodes' close_fin' headrep_snoc' in_block_below' presx_munch'.
    clear HCALLOC NZ1 NZ3 AL1 DIM1 DIM2 B4. pose proof HBR0 as HBR0k.
    unfold name_blob in HHEAD.
    (* [comment removed for export] *)
    assert (LXSUMS : forall AL, Forall (summary_okG usegs AL []) (@nil summary)) by (intros AL; constructor).
    lx_byte_cells.
    rewrite TP. apply (lxp_aevtM_of_evt usegs moc _ _ MK).
    lx_run_tac (PLANS [0x1efe0] [] 20%N (@nil summary)); lx_tree.
    all: apply evt_done; cbv beta; rewrite <- TP.
    all: lazymatch goal with E : @eq mem ?mx ?mc0 |- _ => subst mx end.
    repeat match goal with H : munch [] ?a ?a |- _ => clear H | H : wmono _ ?a ?a |- _ => clear H end.
    repeat match goal with H : rw_cells _ mm ?A ?cs, H' : rw_cells _ mm ?A ?cs |- _ => clear H' end.
    repeat match goal with H : bytes_at _ mm BUF bs, H' : bytes_at _ mm BUF bs |- _ => clear H' end.
    repeat match goal with H : stk _ mm lo ?x, H' : stk _ mm lo ?x |- _ => clear H' end.
    repeat match goal with H : mem_inv _ mm, H' : mem_inv _ mm |- _ => clear H' end.
    (* [comment removed for export] *)
    pose proof (U_asn1_free_named_data_list_shallow_spec L HI HFREE HLS) as SP.
    unfold asn1_free_named_data_list_shallow_stmt, U_ASN1_FREE_NAMED_DATA_LIST_SHALLOW in SP.
    eapply aevtM_cut; [ eapply SP with (a := hd 0 nodes) (nodes := nodes) (lo := lo) (LB := nLBof LB nodes) (h := hc);
      rewrite ?(unsigned_lit (bv_unsigned sp + -144)) by plia; try eassumption; try reflexivity; try plia | ].
    { eapply name_lseg_chain. exact HLn. }
    clear SP.
    intros ms' mo' PO. unfold asn1_free_named_data_list_shallow_post in PO. destruct_exs PO. flat constr:(PO) 2%nat. flclear PO. intros E PO.
    injection E as E1 E2. subst ms' mo'.
    rewrite ?(unsigned_lit (bv_unsigned sp + -144)) in PO by plia.
    flat constr:(PO) 6%nat. flclear PO. intros MI2 ST2 MF2 HT2 HH2 HPc.
    unfold nLBof in HH2, HPc. rewrite lb_remove_all_new in HH2, HPc by exact HND.
    lazymatch goal with |- _ (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) =>
      replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]) end.
    lazymatch goal with |- aevtM _ ?mox _ (MS _ _ _ _ _ ?mx _) => rename mx into m2; rename mox into mo2 end.
    match type of HH2 with HEAP _ _ _ ?hh _ _ _ => rename hh into h2 end.
    clear ST MI MK HLn. heap_transport HPc.
    pose proof (heap_mok _ _ HI _ _ _ _ HH2) as MK.
    pose proof CWCUR as CW2. rewrite <- HT, <- HT2 in CW2. pose proof HTOP as HTOP2. rewrite <- HT, <- HT2 in HTOP2.
    unfold frame_hi in FRH.
    (* [comment removed for export] *)
    rewrite TP. apply (lxp_aevtM_of_evt usegs mo2 _ _ MK).
    lx_run_tac (PLANS (@nil Z) [] 40%N (@nil summary)); lx_tree.
    all: apply evt_done; cbv beta; rewrite <- TP.
    lazymatch goal with |- aevtM _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m9 end.
    lazymatch goal with Hz : lx_hidden (?z = bv_unsigned _) |- _ => unfold lx_hidden in Hz; subst z end.
    lazymatch goal with Hs : rw_cells _ m9 CUR _ |- _ => rewrite (definitions.Z_to_bv_bv_unsigned 8 mg) in Hs; rename Hs into HHEAD9 end.
    lazymatch goal with Hm1 : munch ?W1 m2 m9, Hw1 : wmono _ m2 m9 |- _ => rename Hm1 into MU9; rename Hw1 into WM9 end.
    assert (HH9 : HEAP usegs L HI h2 LB m9 mo2).
    { eapply (HEAP_munch usegs L HI h2 LB m2 m9 mo2 lo); [exact HH2| exact ACL| exact MU9| exact WM9|].
      intros a Ha Hna. apply CW2. cbn [outside] in Hna. clear -Hna. lia. }
    apply aevtM_done. unfold x509_get_name_post. flexi 15%nat.
    exists m9, mo2, h2, r, p, j48, mg, p7, [].
    split; [reflexivity|]. cbn [hd map rev app].
    (flsplit; repeat match goal with |- _ /\ _ => split end); try assumption.
    - eapply mo_frame_trans; [exact MF| exact MF2].
    - rewrite HT2; exact HT.
    - reflexivity.
    - clear -Hr; lia. - clear -Hr; lia. - clear -Hp; lia. - clear -Hp; lia.
    - reflexivity.
    - constructor.
    - intros y [].
    - eapply heap_presx_trans; [exact HPX|]. eapply heap_presx_trans.
      + eapply heap_presx_of_pres_sub; [exact HPc| intros b Hb; exact Hb| lia| lia].
      + eapply (presx_munch L sp LB PP CUR); [exact MU9| exact WM9|]. intros a Ha Hc Ho; cbn [outside] in Ho |- *. clear -Ho. lia.
    - intros _; reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma ok_walk : ltac2:(CDefT.buildp (gd_tbl_P_x509_get_name_B ()) "Pnodes,(0.$1.)Pcur,$1.Pslen,(2.&40.)Palen,(2.&40.)Pj8,(0.(2.&8.))PJ,(0.(2.&8.))PMG,(2.&8.)PP7,(0.(2.&8.))Pp,$1.Px1,(2.&40.)Px5,(2.&40.)Px6,(2.&40.)Px7,(2.&40.)Px8,(2.&40.)Px9,(2.&40.)Px10,(2.&40.)Px11,(2.&40.)Px12,(2.&40.)Px13,(2.&40.)Px14,(2.&40.)Px15,(2.&40.)Px16,(2.&40.)Px17,(2.&40.)Px18,(2.&40.)Px19,(2.&40.)Px20,(2.&40.)Px21,(2.&40.)Px22,(2.&40.)Px23,(2.&40.)Px24,(2.&40.)Px25,(2.&40.)Px26,(2.&40.)Px27,(2.&40.)Px28,(2.&40.)Px29,(2.&40.)Px30,(2.&40.)Px31,(2.&40.)Pmm,P,(2.&40.)(3.(2.&8.))Pmoc,$4.Phc,(5.$6.VL,VHI,)P,(7.VL,VHI,Vra,Vsp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,Vm,Vmo,Vh,VLB,VPP,VCUR,VBUF,Vlo,Vbs,(8.&40.+????????????=<1:.)(8.&40.+????????????=<20.)R3.R2.R1.R28.R27.R26.R25.R24.)P,(9.$6.R4.R28.(:.R24.=R23.R22.))P,(9.$6.R5.VPP,(;.$<.(=.(8.&40.R22.))(>.$<.)))P,(?.(10.VP,R23.)(10.R23.VEND,))(12.$6.R6.(13.$6.VL,VHI,Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,Vh,VLB,VPP,VCUR,VP,VEND,Vlo,Vm,Vmo,)(14.(15.R23.(8.&40.(16.(17.&40.Vsp,)-90.))Vgp,Vtp,R22.R21.R20.R1?.R1>.R1=.R1<.R1;.R1:.R19.R18.R17.R16.R15.R14.R13.R12.R11.R10.R?.R>.R=.R<.R;.R:.R9.R8.)VF,(8.&40.+27??8.)Vfc,(18.(2.&40.))R7.(19.$6.)))")
(* [comment removed for export] *).
  Proof.
    intros nodes cur slen alen j8 J MG P7 p x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 mm moc hc
      INV HCB HPP Hp.
    open_ninv INV. clear INV.
    edestruct (close_nodes) as [(j48 & mg & p7 & HHEAD) HLn]; [exact HCF| exact HHD| exact HLS'| exact HCB|].
    clear HCB HHD HLS'. clear HHbox.
    (* [comment removed for export] *)
    clear sync_W' snoc_facts' others_apart' cur_wrange' headrep_pres' cur_cases' close_nodes' close_fin' headrep_snoc' in_block_below' presx_munch'.
    clear HCALLOC HFREE NZ1 NZ2 NZ3 AL1 AL2 DIM1 DIM2 DHI SPA HTOP B4 SPB TP CWPP CWCUR CRBUF HBR0.
    unfold frame_hi in FRH.
    (* [comment removed for export] *)
    assert (LXSUMS : forall AL, Forall (summary_okG usegs AL []) (@nil summary)) by (intros AL; constructor).
    apply (lxp_aevtM_of_evt usegs moc _ _ MK).
    lx_run_tac (PLANS (@nil Z) [] 40%N (@nil summary)); lx_tree.
    all: apply evt_done; cbv beta.
    all: lazymatch goal with E : @eq mem ?mx ?mc0 |- _ => subst mx end.
    lazymatch goal with STx : stk _ mm lo (bv_unsigned sp) |- _ => rename STx into STf end.
    apply aevtM_done. unfold x509_get_name_post. flexi 15%nat.
    exists mm, moc, hc, 0, p, j48, mg, p7, nodes.
    split; [reflexivity|].
    (flsplit; repeat match goal with |- _ /\ _ => split end); try assumption.
    - reflexivity.
    - lia. - lia. - lia. - lia.
    - apply name_lseg_chain. exact HLn.
    - intros y Hy. exact (proj2 (proj2 (HFR y Hy))).
    - intros NE. exfalso. exact (NE eq_refl).
  Qed.
End Walk.

