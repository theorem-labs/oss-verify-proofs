(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U Require Import U_x509_get_name_B.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Walk AStep CellsX Asn1Aux Asn1AuxA X509Aux X509AuxB.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Spec Require Import Rep RepFacts RepName.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U Require Import UImg U_asn1_get_tag U_asn1_get_len U_asn1_free_named_data_list_shallow U_x509_get_name_A.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import DietDestruct.   (* [comment removed for export] *)
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import LiaOrc. (* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= orc_lia. (* [comment removed for export] *)
Local Ltac dlia ::= orc_dlia. (* [comment removed for export] *)
Local Ltac plia ::= orc_plia. (* [comment removed for export] *)
Local Ltac lia_nodisj ::= orc_dlia. (* [comment removed for export] *)
Local Ltac clear_disj ::= fc_clear_disj. (* [comment removed for export] *)
Local Ltac prune_disj ::= fc_prune_disj. (* [comment removed for export] *)
Ltac2 gd_tbl_P_x509_get_name_C () : Init.string Init.list := ["Corelib.Init.Datatypes.list"; "Corelib.Numbers.BinNums.Z"; "stdpp.bitvector.definitions.bv"; "Corelib.Init.Datatypes.option"; "LinuxProcessSemantics.LinuxProcessSem.State.Model"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.HST"; "RocqVerifyHarness.AgentSubmission.U.UImg.usegs"; "RocqVerifyHarness.AgentSubmission.U.U_x509_get_name_A.ninv"; "stdpp.bitvector.definitions.Z_to_bv"; "RocqVerifyHarness.AgentSubmission.Lib.Step.rw_cells"; "Corelib.Init.Datatypes.cons"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.cell"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.CB"; "Corelib.Init.Datatypes.nil"; "Stdlib.ZArith.BinInt.Z.add"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C8"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C1"; "Stdlib.ZArith.BinInt.Z.le"; "RocqVerifyHarness.AgentSubmission.Lib.AEvt.aevtM"; "RocqVerifyHarness.AgentSubmission.U.U_x509_get_name_A.x509_get_name_post"; "RocqVerifyHarness.AgentSubmission.Lib.MState.MS"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.mkR"; "stdpp.bitvector.definitions.bv_unsigned"; "Corelib.Init.Datatypes.None"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.seg_rom"; "RocqVerifyHarness.AgentSubmission.Spec.RepName.name_blob"; "Stdlib.ZArith.BinInt.Z.lt"; "Walk.InnerOb"; "Walk.OuterOb"].


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
    destruct INVc as (HH & HT & HND & HFR & HCF & HHD & HLS' & FRA & FRS & FRL & FRH & ST & MI & HBUF & HPX & MF);
    pose proof (heap_mok _ _ HI _ _ _ _ HH) as MK; pose proof (conj HH I) as HHbox;
    pose proof HCF as HCFc; destruct HCFc as (CAL & CPOS & C64 & CPP & CBF & CSTK & _);
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
          destruct (sync_W' _ _ _ _ _ _ _ _ _ (proj1 HHbox) HT HS HND HFR HCF HHD HLS' HPX MU WM) as (A & B & C & D); clear HS;
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
      FRA : rw_cells _ mx (bv_unsigned sp + -144) [C8 _; _; _], FRS : rw_cells _ mx (bv_unsigned sp + -120) [C8 ?slen],
      FRL : rw_cells _ mx (bv_unsigned sp + -112) [C8 ?alen] |- _ =>
        assert (INVn : INV mx mox hc nodes cur slen alen (@nil byte));
        [ unfold ninv; repeat match goal with |- _ /\ _ => split end; try assumption;
          try (etransitivity; eassumption); try (eapply mo_frame_trans; eassumption) | ]
    end end.
  Ltac chk := first [ if_false | let K := fresh "KC" in if_cases K; zify_cond K;
    [ exfalso; first [ clear -K; lia | match goal with HP : 0 < ?c, HB : ?c + 64 <= 2 ^ 64 |- _ => clear -K HP HB; lia end ] | clear K ] ].
  Let err_walk' := err_walk L HI HFREE ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m mo h LB PP CUR P END BUF lo bs.
  Let ok_walk' := ok_walk L HI ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m mo h LB PP CUR P END BUF lo bs.

  (* [comment removed for export] *)
  Definition InnerOb (p es : Z) : Prop := ltac2:(CDefT.buildp (gd_tbl_P_x509_get_name_C ()) "Px24,(2.&40.)Pnodes,(0.$1.)Pcur,$1.Pslen,(2.&40.)Palen,(2.&40.)Pj8,(0.(2.&8.))Pj0,(0.(2.&8.))Polen,(2.&40.)Pj1,(0.(2.&8.))Pvlen,(2.&40.)Pj2,(0.(2.&8.))Pmg,(2.&8.)Pp7,(0.(2.&8.))Px1,(2.&40.)Px5,(2.&40.)Px6,(2.&40.)Px7,(2.&40.)Px10,(2.&40.)Px11,(2.&40.)Px12,(2.&40.)Px13,(2.&40.)Px14,(2.&40.)Px15,(2.&40.)Px16,(2.&40.)Px17,(2.&40.)Px20,(2.&40.)Px28,(2.&40.)Px29,(2.&40.)Px30,(2.&40.)Px31,(2.&40.)Pmm,P,(2.&40.)(3.(2.&8.))Pmoc,$4.Phc,(5.$6.VL,VHI,)P,(7.VL,VHI,Vra,Vsp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,Vm,Vmo,Vh,VLB,VPP,VCUR,VBUF,Vlo,Vbs,(8.&40.+????????????=<1:.)(8.&40.+????????????=<20.)R3.R2.R1.R20.R1?.R1>.R1=.R1<.)P,(9.$6.R4.R20.(:.$;.(<.#8.R1<.)(=.$;.)))P,(9.$6.R5.(>.R21.+8.)(:.$;.(?.R1<.)(=.$;.)))P,(9.$6.R6.(>.R22.+10.)(:.$;.(<.#10.R1<.)(=.$;.)))P,(9.$6.R7.(>.R23.+20.)(:.$;.(?.R1<.)(=.$;.)))P,(9.$6.R8.(>.R24.+28.)(:.$;.(<.#8.R1<.)(:.$;.(?.(8.&40.=))(:.$;.(10.R1;.)(:.$;.(<.#7.R1:.)(=.$;.))))))P,(9.$6.R9.VPP,(:.$;.(?.(8.&40.O2.))(=.$;.)))P,(11.VP,O2.)P,(11.O2.O1.)P,(11.O1.VEND,)(12.$6.R<.(13.$6.VL,VHI,Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,Vh,VLB,VPP,VCUR,VP,VEND,Vlo,Vm,Vmo,)(14.(15.R1>.(8.&40.(>.(16.&40.Vsp,)-90.))Vgp,Vtp,R1=.R1<.R1;.(8.&40.R29.)(8.&40.-2880.)R1:.R19.R18.R17.R16.R15.R14.R13.(8.&40.VEND,)(8.&40.VPP,)(8.&40.O1.)R12.(8.&40.+1.)(8.&40.VCUR,)R2;.(8.&40.+1.)(8.&40.+50581008.)(8.&40.-2380.)R11.R10.R?.R>.)VF,(8.&40.+27=?<.)Vfc,(17.(2.&40.))R=.(18.$6.)))")
(* [comment removed for export] *).

  (* [comment removed for export] *)
  Definition OuterOb (p : Z) : Prop := ltac2:(CDefT.buildp (gd_tbl_P_x509_get_name_C ()) "Px24,(2.&40.)Pnodes,(0.$1.)Pcur,$1.Pslen,(2.&40.)Palen,(2.&40.)Pj8,(0.(2.&8.))Pj0,(0.(2.&8.))Polen,(2.&40.)Pj1,(0.(2.&8.))Pvlen,(2.&40.)Pj2,(0.(2.&8.))Pmg,(2.&8.)Pp7,(0.(2.&8.))Px1,(2.&40.)Px5,(2.&40.)Px6,(2.&40.)Px7,(2.&40.)Px10,(2.&40.)Px11,(2.&40.)Px12,(2.&40.)Px13,(2.&40.)Px14,(2.&40.)Px15,(2.&40.)Px16,(2.&40.)Px17,(2.&40.)Px19,(2.&40.)Px20,(2.&40.)Px28,(2.&40.)Px29,(2.&40.)Px30,(2.&40.)Px31,(2.&40.)Pmm,P,(2.&40.)(3.(2.&8.))Pmoc,$4.Phc,(5.$6.VL,VHI,)P,(7.VL,VHI,Vra,Vsp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,Vm,Vmo,Vh,VLB,VPP,VCUR,VBUF,Vlo,Vbs,(8.&40.+????????????=<1:.)(8.&40.+????????????=<20.)R3.R2.R1.R21.R20.R1?.R1>.R1=.)P,(9.$6.R4.R21.(:.$;.(<.#8.R1=.)(=.$;.)))P,(9.$6.R5.(>.R22.+8.)(:.$;.(?.R1=.)(=.$;.)))P,(9.$6.R6.(>.R23.+10.)(:.$;.(<.#10.R1=.)(=.$;.)))P,(9.$6.R7.(>.R24.+20.)(:.$;.(?.R1=.)(=.$;.)))P,(9.$6.R8.(>.R25.+28.)(:.$;.(<.#8.R1=.)(:.$;.(?.(8.&40.=))(:.$;.(10.R1<.)(:.$;.(<.#7.R1;.)(=.$;.))))))P,(9.$6.R9.VPP,(:.$;.(?.(8.&40.O1.))(=.$;.)))P,(11.VP,O1.)P,(11.O1.VEND,)(12.$6.R;.(13.$6.VL,VHI,Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,Vh,VLB,VPP,VCUR,VP,VEND,Vlo,Vm,Vmo,)(14.(15.R1>.(8.&40.(>.(16.&40.Vsp,)-90.))Vgp,Vtp,R1=.R1<.R1;.(8.&40.R29.)(8.&40.-2880.)R1:.R19.R18.R17.R16.R15.R14.R13.(8.&40.VEND,)(8.&40.VPP,)R12.R11.(8.&40.+1.)(8.&40.VCUR,)R2;.(8.&40.+1.)(8.&40.+50581008.)(8.&40.-2380.)R10.R?.R>.R=.)VF,(8.&40.+27=<0.)Vfc,(17.(2.&40.))R<.(18.$6.)))")
(* [comment removed for export] *).

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "01U0@D10176803038.167D1095693892.154 D1095693892.173 D1095693892.191 D1101800120.152 D1101800120.171 D1101800120.189 D11530185118.154D11530185118.173D11530185118.191D15335256281.191D16179275102.167D18891867097.191D2030835994.191 D21055555661.167D25890039164.154D25890039164.173D25890039164.191D28232435806.167D29775215449.191D31496456979.154D31496456979.173D31496456979.191D35402782865.154D35402782865.173D35402782865.191D41257908958.167D43622973458.153D43622973458.154D43622973458.173D43622973458.191D43633546478.152D43633546478.171D43633546478.189D4493859161.191 D45785790777.167D46259122193.154D46259122193.173D46259122193.191D48591303134.154D48591303134.173D48591303134.191D56795294278.154D56795294278.173D56795294278.191D57142437777.154D57142437777.173D57142437777.191D64523690902.191D6775087633.154 D6775087633.173 D6775087633.191 D6790002647.167 D9491433734.152 D9491433734.171 D9491433734.189 L15335256281.181L18891867097.181L29765673068.179L29775215449.181L35402782865.148L35402782865.167L35402782865.181L4114546834.183 L4493859161.181 L46259122193.148L46259122193.167L46259122193.181L47402100242.183L48038554259.176L48591303134.148L48591303134.167L48591303134.181L53165669258.176L56795294278.148L56795294278.167L56795294278.181L57142437777.148L57142437777.167L57142437777.181L59308632045.1  L59308632045.3  L64523690902.181L66142635027.174L6775087633.148 L6775087633.167 L6775087633.181 L7913831106.183 R14366706081.173R14560309127.173R17295365210.152R19154682630.180R22237701920.167R26594891318.167R35497760785.152R42121493084.167R4911321225.152 R4911341463.170 R50860004161.152R64010002177.145R6755506945.152 00000B00h01N02602P02j03F03g04H04k04l05>05?05@05A05b06C06f07807907:07;07<07=07>07?07Q08008U09:09a0::0:S0:n0:o0;00;10;20;30;40;50;60;70;80;90;:0;;0;<0;=0;>0;?0;@0;A0;V0;k0<B0<h0=N0>M0?30@:0AA0BN0Bb0CH0DO0EV0Fc0G70GI0Gm0HQ0I70II0J10JY0KC0LJ0MQ0N^0Nb0Nl0OR0Od0Pk0R20S?0SS0T_0U10UL0Ue0V?0V\0Vn0WG0X@0Y90YY0Zo0[AS2sp2PP3CUR2bs3curS2sp2PP3CUR2bs3cur4CPOS2HB5Ha_st5Hl_stS2sp2PP3CUR2bs3cur4CPOS2HB5Ha_st5Hl_stS2sp2PP3CUR2bs3cur1N4CPOS2HB5Ha_st5Hl_stS2sp2PP3CUR2bs3cur4CPOS2HBS2sp2PP3CUR2bs3cur4CPOS2HBS2sp2PP3CUR2bs3cur1N4CPOS2HBS2sp2PP3CUR2bs3cur2HB5Ha_st5Hl_stS2sp2PP3CUR2bs3cur2HB5Ha_st5Hl_stS2sp2PP3CUR2bs3cur1N2HB5Ha_st5Hl_stFS2sp2PP3CUR2bs3curFFFS2sp2PP3CUR2bs3cur2HB5Ha_st5Hl_stS2sp2PP3CUR2bs3cur2HB5Ha_st5Hl_stS2sp2PP3CUR2bs3cur1N2HB5Ha_st5Hl_stS2sp2PP3CUR2bs3curFFFFFFFS2sp2PP3CUR2bs3curS2sp2PP3CUR2bs3cur3C642HB5Ha_stS2sp2PP3CUR2bs3cur3C642HB5Ha_st5Hl_stS2sp2PP3CUR2bs3cur3C642HB5Ha_st5Hl_stS2sp2PP3CUR2bs3cur1N3C642HB5Ha_st5Hl_stS2sp2PP3CUR2bs3cur3C642HBS2sp2PP3CUR2bs3cur3C642HBS2sp2PP3CUR2bs3cur1N3C642HBFFFFFFFFFFFFFFFFFFFS2sp2PP3CUR2bs3cur2HBS2sp2PP3CUR2bs3cur2HBS2sp2PP3CUR2bs3cur1N2HBS2sp2PP3CUR2bs3cur1N2HD2HB5Ha_st5Hl_stS2sp2PP3CUR2bs3cur1N2HD2HB5Ha_st5Hl_stS1L2sp2PP3CUR2lo2bs3PPB4CURB3SLO3HLS3ACL3SPB3cur1N4CPOS3HN03HNCS2sp2PP3CUR2bs3cur1N2HD2HB5Ha_st5Hl_stS1L2sp2PP3CUR2lo2bs3PPB4CURB3SLO3HLS3ACL3ACP3cur4CPOS2HD2HB5Ha_st5Hl_stS1L2sp2PP3CUR2lo2bs3PPB4CURB3SLO3HLS3ACL3ACP3cur4CPOS2HD2HB5Ha_st5Hl_stS1L2sp2PP3CUR2lo2bs3PPB4CURB3SLO3HLS3ACL3ACP3cur1N4CPOS2HD3HN02HB5Ha_st5Hl_stS2sp2PP3CUR2bs3cur1NS2sp2PP3CUR2bs3cur1N2HD2HB5Ha_st5Hl_stS1L2sp2PP3CUR2lo2bs3PPB4CURB3SLO3HLS3ACL3ACP3cur4CPOS2HD2HB5Ha_st5Hl_stS1L2sp2PP3CUR2lo2bs3PPB4CURB3SLO3HLS3ACL3ACP3cur4CPOS2HD2HB5Ha_st5Hl_stS1L2sp2PP3CUR2lo2bs3PPB4CURB3SLO3HLS3ACL3ACP3cur1N4CPOS2HD3HN02HB5Ha_st5Hl_stS2sp2PP3CUR2bs3cur1NS2sp2PP3CUR2bs3curS2sp2PP3CUR2bs3cur2HD2HB5Ha_st5Hl_stS2sp2PP3CUR2bs3cur2HD2HB5Ha_st5Hl_stS2sp2PP3CUR2bs3cur1N2HD2HB5Ha_st5Hl_stS2sp2PP3CUR2bs3curS2sp2PP3CUR3BUF2bs3cur2HD2HB5Ha_st5Hl_stS2sp2PP3CUR3BUF2bs3cur2HD2HB5Ha_st5Hl_stS2sp2PP3CUR3BUF2bs3cur2HD1N2HB5Ha_st5Hl_stS1L2sp2PP3CUR2lo2bs3PPB4CURB3SLO3HLS3ACL3ACP3cur4CPOS2HD2HB5Ha_st5Hl_stS1L2sp2PP3CUR2lo2bs3PPB4CURB3SLO3HLS3ACL3ACP3cur4CPOS2HD2HB5Ha_st5Hl_stS1L2sp2PP3CUR2lo2bs3PPB4CURB3SLO3HLS3ACL3ACP3cur1N4CPOS2HD3HN02HB5Ha_st5Hl_stS2KNS1N3HN02KNS2sp2PP3CUR2bs3cur1N2HD2HB5Ha_st5Hl_stS2sp2PP3CUR2bs3curS1L2sp2PP3CUR2lo2bs3PPB4CURB3SLO3HLS3ACL3ACP3cur4CPOS2HD2HB5Ha_st5Hl_stS1L2sp2PP3CUR2lo2bs3PPB4CURB3SLO3HLS3ACL3ACP3cur4CPOS2HD2HB5Ha_st5Hl_stS1L2sp2PP3CUR2lo2bs3PPB4CURB3SLO3HLS3ACL3ACP3cur1N4CPOS2HD3HN02HB5Ha_st5Hl_stS2sp2PP3CUR2bs3cur1NS1L2sp2PP3CUR1P3END2lo2bs3PPB4CURB3SLO3HLS3ACL3ACP3cur1p2es3Hp13Hp23Hp34CPOSS2sp2PP3CUR2bs3curS1L2sp2PP3CUR2lo2bs3SLO3curS2sp2PP3CUR2bs1p2es1N3Hp2S2sp2PP3CUR2lo2bs3cur4CSTKS2sp2PP3CUR3BUF2lo2bs3DS33curS2sp2PP3CUR2bs3curS2sp2PP3CUR2lo2bs3DS13curS1L2sp2PP3CUR2lo2bs3PPB4CURB3SLO3HLS3ACL3ACP3SPB3cur4CPOSS1L2sp2PP3CUR2lo2bs3PPB4CURB3SLO3HLS3ACL3ACP3SPB3cur4CPOSS1L2HI2sp2PP3CUR2bs3cur2hc5HTOPcS1L2sp2PP3CUR1P3END3BUF2lo2bs2B12B33PPB4CURB3SLO3HLS3ACL3ACP3cur1p2es3Hp13Hp23Hp34CPOSS2sp2PP3CUR2bs3cur". (* [comment removed for export] *)
  #[using="HCALLOC HFREE B1 B3 D1 D2 D3 PPB CURB NZ2 AL2 SLO HLS ACL ACP HTOP SPA DHI DIM1 DIM2 DS1 DS2 DS3 CWPP CWCUR CRBUF TP SPB HBR0 sync_W' snoc_facts' cur_wrange' headrep_pres' close_fin' headrep_snoc' err_walk'"] Lemma alloc_inner : ltac2:(CDefT.buildp (gd_tbl_P_x509_get_name_C ()) "Pnodes,(0.$1.)Pcur,$1.Pslen,(2.&40.)Palen,(2.&40.)Pj8,(0.(2.&8.))PJ,(0.(2.&8.))PMG,(2.&8.)PP7,(0.(2.&8.))Pp,$1.Pes,$1.Ppw,(2.&40.)Px1,(2.&40.)Px5,(2.&40.)Px6,(2.&40.)Px7,(2.&40.)Px10,(2.&40.)Px11,(2.&40.)Px12,(2.&40.)Px13,(2.&40.)Px14,(2.&40.)Px15,(2.&40.)Px16,(2.&40.)Px17,(2.&40.)Px28,(2.&40.)Px29,(2.&40.)Px30,(2.&40.)Px31,(2.&40.)Pmm,P,(2.&40.)(3.(2.&8.))Pmoc,$4.Phc,(5.$6.VL,VHI,)P,(7.VL,VHI,Vra,Vsp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,Vm,Vmo,Vh,VLB,VPP,VCUR,VBUF,Vlo,Vbs,(8.&40.+????????????=<1:.)(8.&40.+????????????=<20.)R3.R2.R1.R1>.R1=.R1<.R1;.R1:.)P,(9.$6.R4.R1>.(19.R1:.=R19.R18.))P,(9.$6.R5.VPP,(:.$;.(?.(8.&40.R18.))(=.$;.)))P,(11.VP,R19.)P,(1:.R1:.R19.)P,(11.R1:.VEND,)P,(1;.R1<.R1;.)(12.$6.R9.(13.$6.VL,VHI,Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,Vh,VLB,VPP,VCUR,VP,VEND,Vlo,Vm,Vmo,)(14.(15.R1:.(8.&40.(>.(16.&40.Vsp,)-90.))Vgp,Vtp,R19.R18.R17.(8.&40.R24.)(8.&40.-2880.)R16.R15.R14.R13.R12.R11.R10.R?.(8.&40.VEND,)(8.&40.VPP,)(8.&40.R1<.)R1;.(8.&40.+1.)(8.&40.VCUR,)(8.&40.=)(8.&40.+1.)(8.&40.+50581008.)(8.&40.-2380.)R>.R=.R<.R;.)VF,(8.&40.+27>?4.)Vfc,(17.(2.&40.))R:.(18.$6.)))")
(* [comment removed for export] *).
  Proof.
    intros nodes cur slen alen j8 J MG P7 p es pw x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 mm moc hc
      INV HCB HPP Hp1 Hp2 Hp3 KIN.
    open_ninv INV. clear INV.
    pose proof (bytes_at_bound _ _ _ _ HBUF) as BB.
    assert (LBS : 0 < Z.of_nat (length bs)) by plia.
    pose proof (cur_wrange' nodes cur _ HFR HCF ltac:(intros b Hb; exact Hb)) as CWc0.
    pose proof CWc0 as CWc. rewrite <- HT in CWc. pose proof HTOP as HTOPc. rewrite <- HT in HTOPc.
    unfold name_blob in HCB. start_W cur.
    zstep. chk. zstep. chk. zstep. zstep. zstep. wsync. zstep.
    replace (Z_to_bv 64 260448) with (Z_to_bv 64 (hl_calloc L)) by (rewrite HCALLOC; reflexivity).
    eapply aevtM_cut; [ eapply (heap_calloc usegs L HI) with (cnt := 1) (sz := 64) (lo := lo);
      rewrite ?(unsigned_lit (bv_unsigned sp + -144)) by plia; try eassumption; try reflexivity; try plia | ].
    intros ms' mo' PO. unfold call_post in PO. destruct_exs PO. destruct PO as [E PO].
    injection E as E1 E2. subst ms' mo'.
    rewrite ?(unsigned_lit (bv_unsigned sp + -144)) in PO by plia.
    destruct_ands PO.
    lazymatch goal with |- _ (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) =>
      replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]) end.
    lazymatch goal with |- aevtM _ ?mox _ (MS _ _ _ _ _ ?mx _) => rename mx into m2; rename mox into mo2 end.
    match goal with H : heap_pres _ _ _ _ _ m2 |- _ => rename H into HPc end.
    match goal with H : stk _ m2 _ _ |- _ => rename H into ST2 end.
    match goal with H : mem_inv _ m2 |- _ => rename H into MI2 end.
    match goal with H : mo_frame moc mo2 |- _ => rename H into MF2 end.
    (* [comment removed for export] *)
    pose proof (headrep_pres' nodes _ _ _ HPc (nLBof_sub LB nodes) HHD) as HHD2.
    pose proof (lseg_pres _ _ _ _ _ _ _ HPc HLS') as HLS2.
    assert (HPX2 : heap_presx usegs L LB (bv_unsigned sp) X m m2).
    { eapply heap_presx_trans; [exact HPX|]. eapply heap_presx_of_pres_sub; [exact HPc| apply nLBof_sub| lia| lia]. }
    clear ST MI MK HH HHbox HHD HLS' HPX MU WM. heap_transport HPc. clear HPc.
    rename HHD2 into HHD. rename HLS2 into HLS'. rename HPX2 into HPX.
    ddestruct PO as (h2 & HT2 & [[-> HH2] | (N & -> & HBN & HH2 & HNEW)]); rewrite HT in HT2; clear HT CWc HTOPc; rename HT2 into HT;
      pose proof CWc0 as CWc; rewrite <- HT in CWc; pose proof HTOP as HTOPc; rewrite <- HT in HTOPc.
    - (* [comment removed for export] *)
      pose proof (heap_mok _ _ HI _ _ _ _ HH2) as MK. rename HH2 into HH. pose proof (conj HH I) as HHbox.
      start_W cur.
      zstep. zstep. zstep. if_cases KN; zify_cond KN. { exfalso. clear -KN. cbn in KN. lia. }
      zstep.
      wsync. rebuild_ninv INV2.
      eapply err_walk'; try exact INV2; try eassumption; try plia.
    - (* [comment removed for export] *)
      change (1 * 64) with 64 in HBN, HH2, HNEW. cbn [Z.to_nat Pos.to_nat Pos.iter_op Nat.add Nat.mul] in HNEW.
      ddestruct (snoc_facts' nodes cur N h2 m2 mo2 HH2 HND HFR HCF HBN LBS) as (HND' & HFR' & HCF' & APcur & APP & APB).
      pose proof HBN as HBNc. ddestruct HBNc as (HN0 & HN16 & _ & HNC & HNI).
      apply (rw_cells_zeros usegs m2 N 64
               [CB 8 (repeat (Z_to_bv 8 0) 8); C8 (Z_to_bv 64 0); CB 16 (repeat (Z_to_bv 8 0) 16); C8 (Z_to_bv 64 0);
                CB 8 (repeat (Z_to_bv 8 0) 8); C8 (Z_to_bv 64 0); C1 (Z_to_bv 8 0); CB 7 (repeat (Z_to_bv 8 0) 7)]) in HNEW;
        [| cbn; repeat split; reflexivity | reflexivity].
      chunk_split HNEW 1%nat W0 HN1. chunk_split HN1 1%nat W1 HN2. chunk_split HN2 1%nat W2 HN3. chunk_split HN3 1%nat W3 W4.
      replace (N + 8 + 8) with (N + 16) in W2 by lia. replace (N + 8 + 8 + 16) with (N + 32) in W3 by lia.
      replace (N + 8 + 8 + 16 + 8) with (N + 40) in W4 by lia.
      pose proof (heap_mok _ _ HI _ _ _ _ HH2) as MK. rename HH2 into HH. pose proof (conj HH I) as HHbox.
      pose proof (cur_wrange' nodes cur ((N, 64) :: nLBof LB nodes) HFR HCF ltac:(intros b Hb; right; exact Hb)) as CW2. rewrite <- HT in CW2.
      start_W cur.
      zstep. zstep. zstep. if_cases KN; zify_cond KN. 2:{ exfalso. clear -KN HN0. rewrite ?unsigned_lit in KN by lia. cbn in KN. lia. }
      wsync.
      lazymatch goal with |- aevtM _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m3 end.
      pose proof (headrep_snoc' nodes cur m3 _ _ _ N HCF HHD HCB) as HHD3.
      pose proof (close_fin' nodes cur m3 _ _ _ N ((N, 64) :: nLBof LB nodes) HCF HLS' HCB ltac:(intros b Hb; right; exact Hb)) as HLS3.
      rewrite <- nLBof_snoc in HH, HLS3.
      clear HHD HLS' HCF HND HFR CAL CPOS C64 CPP CBF CSTK HCB HHbox.
      assert (INV3 : INV m3 mo2 h2 (nodes ++ [N]) N slen alen j8).
      { unfold ninv. rewrite removelast_last, last_last.
        repeat match goal with |- _ /\ _ => split end; try assumption. eapply mo_frame_trans; eassumption. }
      eapply KIN; try exact INV3; try eassumption; try plia.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "01@0@D10176803038.164D1095693892.170 D1095693892.188 D1101800120.168 D1101800120.186 D11530185118.170D11530185118.188D15335256281.188D16179275102.164D18891867097.188D2030835994.188 D21055555661.164D25890039164.170D25890039164.188D28232435806.164D29775215449.188D31496456979.170D31496456979.188D35402782865.170D35402782865.188D41257908958.164D43622973458.170D43622973458.188D43633546478.168D43633546478.186D4493859161.188 D45785790777.164D46259122193.170D46259122193.188D48591303134.170D48591303134.188D56795294278.170D56795294278.188D57142437777.170D57142437777.188D64523690902.188D6775087633.170 D6775087633.188 D6790002647.164 D9491433734.168 D9491433734.186 L15335256281.178L18891867097.178L29765673068.176L29775215449.178L35402782865.164L35402782865.178L4114546834.180 L4493859161.178 L46259122193.164L46259122193.178L47402100242.180L48038554259.173L48591303134.164L48591303134.178L53165669258.173L54312524819.171L56795294278.164L56795294278.178L57142437777.164L57142437777.178L59308632045.1  L59308632045.3  L64523690902.178L6775087633.164 L6775087633.178 L7913831106.180 R14366706081.170R14560309127.170R17295365210.149R20948712811.177R22237701920.164R26594891318.164R35497760785.149R42121493084.164R4911321225.149 R4911341463.167 R50860004161.149R64010002177.143R6755506945.149 00000B00h01P01j02F02g03J03K03]03^03_03`04A04d05605705805905:05;05M06206Y07207M07N07O07P07Q07R07S07T07U07V07W07X07Y07Z07[08008G08m09S0:R0;80<?0=L0=`0>F0?M0@Z0@n0A@0Ad0BJ0B\0Bn0CV0D@0EG0FT0FX0Fb0GH0HO0I\0J00JR0Jd0K?0KY0L30LP0Lb0M;0N40Nm0OM0P\0PnS2sp2PP3CUR2bs3curS2sp2PP3CUR2bs3cur4CPOS2HB5Ha_st5Hl_stS2sp2PP3CUR2bs3cur1N4CPOS2HB5Ha_st5Hl_stS2sp2PP3CUR2bs3cur4CPOS2HBS2sp2PP3CUR2bs3cur1N4CPOS2HBS2sp2PP3CUR2bs3cur2HB5Ha_st5Hl_stS2sp2PP3CUR2bs3cur1N2HB5Ha_st5Hl_stFS2sp2PP3CUR2bs3curFFFS2sp2PP3CUR2bs3cur2HB5Ha_st5Hl_stS2sp2PP3CUR2bs3cur1N2HB5Ha_st5Hl_stS2sp2PP3CUR2bs3curFFFFFS2sp2PP3CUR2bs3curS2sp2PP3CUR2bs3cur3C642HB5Ha_st5Hl_stS2sp2PP3CUR2bs3cur1N3C642HB5Ha_st5Hl_stS2sp2PP3CUR2bs3cur3C642HBS2sp2PP3CUR2bs3cur1N3C642HBFFFFFFFFFFFFFFS2sp2PP3CUR2bs3cur2HBS2sp2PP3CUR2bs3cur1N2HBS2sp2PP3CUR2bs3cur1N2HD2HB5Ha_st5Hl_stS2sp2PP3CUR2bs3cur1N2HD2HB5Ha_st5Hl_stS1L2sp2PP3CUR2lo2bs3PPB4CURB3SLO3HLS3ACL3SPB3cur1N4CPOS3HN03HNCS2sp2PP3CUR2bs3cur1N2HD2HB5Ha_st5Hl_stS1L2sp2PP3CUR2lo2bs3PPB4CURB3SLO3HLS3ACL3ACP3cur4CPOS2HD2HB5Ha_st5Hl_stS1L2sp2PP3CUR2lo2bs3PPB4CURB3SLO3HLS3ACL3ACP3cur1N4CPOS2HD3HN02HB5Ha_st5Hl_stS2sp2PP3CUR2bs3cur1NS2sp2PP3CUR2bs3cur1N2HD2HB5Ha_st5Hl_stS1L2sp2PP3CUR2lo2bs3PPB4CURB3SLO3HLS3ACL3ACP3cur4CPOS2HD2HB5Ha_st5Hl_stS1L2sp2PP3CUR2lo2bs3PPB4CURB3SLO3HLS3ACL3ACP3cur1N4CPOS2HD3HN02HB5Ha_st5Hl_stS2sp2PP3CUR2bs3cur1NS2sp2PP3CUR2bs3curS2sp2PP3CUR2bs3cur2HD2HB5Ha_st5Hl_stS2sp2PP3CUR2bs3cur1N2HD2HB5Ha_st5Hl_stS2sp2PP3CUR2bs3curS2sp2PP3CUR2bs3curS2sp2PP3CUR3BUF2bs3cur2HD2HB5Ha_st5Hl_stS2sp2PP3CUR3BUF2bs3cur2HD1N2HB5Ha_st5Hl_stS1L2sp2PP3CUR2lo2bs3PPB4CURB3SLO3HLS3ACL3ACP3cur4CPOS2HD2HB5Ha_st5Hl_stS1L2sp2PP3CUR2lo2bs3PPB4CURB3SLO3HLS3ACL3ACP3cur1N4CPOS2HD3HN02HB5Ha_st5Hl_stS2KNS1N3HN02KNS2sp2PP3CUR2bs3cur1N2HD2HB5Ha_st5Hl_stS1L2sp2PP3CUR2lo2bs3PPB4CURB3SLO3HLS3ACL3ACP3cur4CPOS2HD2HB5Ha_st5Hl_stS1L2sp2PP3CUR2lo2bs3PPB4CURB3SLO3HLS3ACL3ACP3cur1N4CPOS2HD3HN02HB5Ha_st5Hl_stS2sp2PP3CUR2bs3cur1NS2sp2PP3CUR1P3END2bs3cur1p3Hp13Hp2S2sp2PP3CUR2bs3curS1L2sp2PP3CUR2lo2bs3SLO3curS2sp2PP3CUR3END2bs1p1N3Hp2S2sp2PP3CUR2lo2bs3cur4CSTKS2sp2PP3CUR3BUF2lo2bs3DS33curS2sp2PP3CUR2bs3curS2sp2PP3CUR2lo2bs3DS13curS1L2sp2PP3CUR2lo2bs3PPB4CURB3SLO3HLS3ACL3ACP3SPB3cur4CPOSS1L2sp2PP3CUR2lo2bs3PPB4CURB3SLO3HLS3ACL3ACP3SPB3cur4CPOSS1L2HI2sp2PP3CUR2bs3cur2hc5HTOPcS1L2sp2PP3CUR1P3END3BUF2lo2bs2B12B33PPB4CURB3SLO3HLS3ACL3ACP3cur1p3Hp13Hp24CPOSS2sp2PP3CUR2bs3cur". (* [comment removed for export] *)
  #[using="HCALLOC HFREE B1 B3 D1 D2 D3 PPB CURB NZ2 AL2 SLO HLS ACL ACP HTOP SPA DHI DIM1 DIM2 DS1 DS2 DS3 CWPP CWCUR CRBUF TP SPB HBR0 sync_W' snoc_facts' cur_wrange' headrep_pres' close_fin' headrep_snoc' err_walk'"] Lemma alloc_outer : ltac2:(CDefT.buildp (gd_tbl_P_x509_get_name_C ()) "Pnodes,(0.$1.)Pcur,$1.Pslen,(2.&40.)Palen,(2.&40.)Pj8,(0.(2.&8.))PJ,(0.(2.&8.))PMG,(2.&8.)PP7,(0.(2.&8.))Pp,$1.Ppw,(2.&40.)Px1,(2.&40.)Px5,(2.&40.)Px6,(2.&40.)Px7,(2.&40.)Px10,(2.&40.)Px11,(2.&40.)Px12,(2.&40.)Px13,(2.&40.)Px14,(2.&40.)Px15,(2.&40.)Px16,(2.&40.)Px17,(2.&40.)Px28,(2.&40.)Px29,(2.&40.)Px30,(2.&40.)Px31,(2.&40.)Pmm,P,(2.&40.)(3.(2.&8.))Pmoc,$4.Phc,(5.$6.VL,VHI,)P,(7.VL,VHI,Vra,Vsp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,Vm,Vmo,Vh,VLB,VPP,VCUR,VBUF,Vlo,Vbs,(8.&40.+????????????=<1:.)(8.&40.+????????????=<20.)R3.R2.R1.R1=.R1<.R1;.R1:.R19.)P,(9.$6.R4.R1=.(19.R19.=R18.R17.))P,(9.$6.R5.VPP,(:.$;.(?.(8.&40.R17.))(=.$;.)))P,(11.VP,R18.)P,(1:.R19.VEND,)P,(1<.R1:.)(12.$6.R8.(13.$6.VL,VHI,Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,Vh,VLB,VPP,VCUR,VP,VEND,Vlo,Vm,Vmo,)(14.(15.R19.(8.&40.(>.(16.&40.Vsp,)-90.))Vgp,Vtp,R18.R17.R16.(8.&40.R22.)(8.&40.-2880.)R15.R14.R13.R12.R11.R10.R?.R>.(8.&40.VEND,)(8.&40.VPP,)(8.&40.R1;.)R1:.(8.&40.+1.)(8.&40.VCUR,)(8.&40.=)(8.&40.+1.)(8.&40.+50581008.)(8.&40.-2380.)R=.R<.R;.R:.)VF,(8.&40.+27?54.)Vfc,(17.(2.&40.))R9.(18.$6.)))")
(* [comment removed for export] *).
  Proof.
    intros nodes cur slen alen j8 J MG P7 p pw x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 mm moc hc
      INV HCB HPP Hp1 Hp2 KIN.
    open_ninv INV. clear INV.
    pose proof (bytes_at_bound _ _ _ _ HBUF) as BB.
    assert (LBS : 0 < Z.of_nat (length bs)) by plia.
    pose proof (cur_wrange' nodes cur _ HFR HCF ltac:(intros b Hb; exact Hb)) as CWc0.
    pose proof CWc0 as CWc. rewrite <- HT in CWc. pose proof HTOP as HTOPc. rewrite <- HT in HTOPc.
    unfold name_blob in HCB. start_W cur.
    zstep. zstep. zstep.
    replace (Z_to_bv 64 260448) with (Z_to_bv 64 (hl_calloc L)) by (rewrite HCALLOC; reflexivity).
    eapply aevtM_cut; [ eapply (heap_calloc usegs L HI) with (cnt := 1) (sz := 64) (lo := lo);
      rewrite ?(unsigned_lit (bv_unsigned sp + -144)) by plia; try eassumption; try reflexivity; try plia | ].
    intros ms' mo' PO. unfold call_post in PO. destruct_exs PO. destruct PO as [E PO].
    injection E as E1 E2. subst ms' mo'.
    rewrite ?(unsigned_lit (bv_unsigned sp + -144)) in PO by plia.
    destruct_ands PO.
    lazymatch goal with |- _ (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) =>
      replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]) end.
    lazymatch goal with |- aevtM _ ?mox _ (MS _ _ _ _ _ ?mx _) => rename mx into m2; rename mox into mo2 end.
    match goal with H : heap_pres _ _ _ _ _ m2 |- _ => rename H into HPc end.
    match goal with H : stk _ m2 _ _ |- _ => rename H into ST2 end.
    match goal with H : mem_inv _ m2 |- _ => rename H into MI2 end.
    match goal with H : mo_frame moc mo2 |- _ => rename H into MF2 end.
    (* [comment removed for export] *)
    pose proof (headrep_pres' nodes _ _ _ HPc (nLBof_sub LB nodes) HHD) as HHD2.
    pose proof (lseg_pres _ _ _ _ _ _ _ HPc HLS') as HLS2.
    assert (HPX2 : heap_presx usegs L LB (bv_unsigned sp) X m m2).
    { eapply heap_presx_trans; [exact HPX|]. eapply heap_presx_of_pres_sub; [exact HPc| apply nLBof_sub| lia| lia]. }
    clear ST MI MK HH HHbox HHD HLS' HPX MU WM. heap_transport HPc. clear HPc.
    rename HHD2 into HHD. rename HLS2 into HLS'. rename HPX2 into HPX.
    ddestruct PO as (h2 & HT2 & [[-> HH2] | (N & -> & HBN & HH2 & HNEW)]); rewrite HT in HT2; clear HT CWc HTOPc; rename HT2 into HT;
      pose proof CWc0 as CWc; rewrite <- HT in CWc; pose proof HTOP as HTOPc; rewrite <- HT in HTOPc.
    - (* [comment removed for export] *)
      pose proof (heap_mok _ _ HI _ _ _ _ HH2) as MK. rename HH2 into HH. pose proof (conj HH I) as HHbox.
      start_W cur.
      zstep. chk. zstep. chk. zstep. zstep. zstep. if_cases KN; zify_cond KN. { exfalso. clear -KN. cbn in KN. lia. }
      zstep.
      wsync. rebuild_ninv INV2.
      eapply err_walk'; try exact INV2; try eassumption; try plia.
    - (* [comment removed for export] *)
      change (1 * 64) with 64 in HBN, HH2, HNEW. cbn [Z.to_nat Pos.to_nat Pos.iter_op Nat.add Nat.mul] in HNEW.
      ddestruct (snoc_facts' nodes cur N h2 m2 mo2 HH2 HND HFR HCF HBN LBS) as (HND' & HFR' & HCF' & APcur & APP & APB).
      pose proof HBN as HBNc. ddestruct HBNc as (HN0 & HN16 & _ & HNC & HNI).
      apply (rw_cells_zeros usegs m2 N 64
               [CB 8 (repeat (Z_to_bv 8 0) 8); C8 (Z_to_bv 64 0); CB 16 (repeat (Z_to_bv 8 0) 16); C8 (Z_to_bv 64 0);
                CB 8 (repeat (Z_to_bv 8 0) 8); C8 (Z_to_bv 64 0); C1 (Z_to_bv 8 0); CB 7 (repeat (Z_to_bv 8 0) 7)]) in HNEW;
        [| cbn; repeat split; reflexivity | reflexivity].
      chunk_split HNEW 1%nat W0 HN1. chunk_split HN1 1%nat W1 HN2. chunk_split HN2 1%nat W2 HN3. chunk_split HN3 1%nat W3 W4.
      replace (N + 8 + 8) with (N + 16) in W2 by lia. replace (N + 8 + 8 + 16) with (N + 32) in W3 by lia.
      replace (N + 8 + 8 + 16 + 8) with (N + 40) in W4 by lia.
      pose proof (heap_mok _ _ HI _ _ _ _ HH2) as MK. rename HH2 into HH. pose proof (conj HH I) as HHbox.
      pose proof (cur_wrange' nodes cur ((N, 64) :: nLBof LB nodes) HFR HCF ltac:(intros b Hb; right; exact Hb)) as CW2. rewrite <- HT in CW2.
      start_W cur.
      zstep. chk. zstep. chk. zstep. zstep. zstep. if_cases KN; zify_cond KN. 2:{ exfalso. clear -KN HN0. rewrite ?unsigned_lit in KN by lia. cbn in KN. lia. }
      wsync.
      lazymatch goal with |- aevtM _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m3 end.
      pose proof (headrep_snoc' nodes cur m3 _ _ _ N HCF HHD HCB) as HHD3.
      pose proof (close_fin' nodes cur m3 _ _ _ N ((N, 64) :: nLBof LB nodes) HCF HLS' HCB ltac:(intros b Hb; right; exact Hb)) as HLS3.
      rewrite <- nLBof_snoc in HH, HLS3.
      clear HHD HLS' HCF HND HFR CAL CPOS C64 CPP CBF CSTK HCB HHbox.
      assert (INV3 : INV m3 mo2 h2 (nodes ++ [N]) N slen alen j8).
      { unfold ninv. rewrite removelast_last, last_last.
        repeat match goal with |- _ /\ _ => split end; try assumption. eapply mo_frame_trans; eassumption. }
      eapply KIN; try exact INV3; try eassumption; try plia.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
End Walk.
