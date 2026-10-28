(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U Require Import U_x509_get_name_B U_x509_get_name_C.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Walk AStep CellsX Asn1Aux Asn1AuxA X509Aux X509AuxB.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Spec Require Import Rep RepFacts RepName.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U Require Import UImg U_asn1_get_tag U_asn1_get_len U_asn1_free_named_data_list_shallow U_x509_get_name_A.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LXP Require Import LxP_Flat.
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
Ltac2 gd_tbl_P_x509_get_name_D () : Init.string Init.list := ["Corelib.Init.Datatypes.list"; "Corelib.Numbers.BinNums.Z"; "stdpp.bitvector.definitions.bv"; "Corelib.Init.Datatypes.option"; "LinuxProcessSemantics.LinuxProcessSem.State.Model"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.HST"; "RocqVerifyHarness.AgentSubmission.U.UImg.usegs"; "RocqVerifyHarness.AgentSubmission.U.U_x509_get_name_A.ninv"; "stdpp.bitvector.definitions.Z_to_bv"; "RocqVerifyHarness.AgentSubmission.Lib.Step.rw_cells"; "Corelib.Init.Datatypes.cons"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.cell"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C4"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.CB"; "Corelib.Init.Datatypes.nil"; "Stdlib.ZArith.BinInt.Z.add"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C8"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C1"; "Stdlib.ZArith.BinInt.Z.le"; "stdpp.bitvector.definitions.bv_unsigned"; "Stdlib.ZArith.BinInt.Z.sub"; "Stdlib.ZArith.BinInt.Z.lt"; "RocqVerifyHarness.AgentSubmission.U.U_x509_get_name_C.InnerOb"; "RocqVerifyHarness.AgentSubmission.U.U_x509_get_name_C.OuterOb"; "RocqVerifyHarness.AgentSubmission.Lib.AEvt.aevtM"; "RocqVerifyHarness.AgentSubmission.U.U_x509_get_name_A.x509_get_name_post"; "RocqVerifyHarness.AgentSubmission.Lib.MState.MS"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.mkR"; "Corelib.Init.Datatypes.None"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.seg_rom"].


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
      FRA : rw_cells _ mx (bv_unsigned sp + -144) [C8 _; _; _], FRS : rw_cells _ mx (bv_unsigned sp + -120) [C8 ?slen],
      FRL : rw_cells _ mx (bv_unsigned sp + -112) [C8 ?alen] |- _ =>
        assert (INVn : INV mx mox hc nodes cur slen alen (@nil byte));
        [ unfold ninv; repeat match goal with |- _ /\ _ => split end; try assumption;
          try (etransitivity; eassumption); try (eapply mo_frame_trans; eassumption) | ]
    end end.
  Ltac chk := first [ if_false | let K := fresh "KC" in if_cases K; zify_cond K;
    [ exfalso; rewrite ?unsigned_lit in K by plia;
      first [ clear -K; lia | plia
            | revert K; repeat (match goal with |- context [Z.ltb ?a ?b] => destruct (Z.ltb_spec a b)
                                         | |- context [Z.eqb ?a ?b] => destruct (Z.eqb_spec a b) end);
              let K' := fresh "KC" in intro K'; vm_compute in K'; first [ discriminate K' | plia ] ]
    | clear K ] ].

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Ltac spine_firstn k cs :=
    let k := eval cbv in k in
    lazymatch k with
    | Datatypes.O => eval lazy beta iota delta [firstn] in (firstn Datatypes.O cs)
    | Datatypes.S ?k' => lazymatch cs with
               | ?c :: ?cs' => let r := spine_firstn k' cs' in constr:(c :: r)
               | _ => eval cbv beta iota delta [firstn] in (firstn k cs)
               end
    end.
  Ltac spine_skipn k cs :=
    let k := eval cbv in k in
    lazymatch k with
    | Datatypes.O => cs
    | Datatypes.S ?k' => lazymatch cs with
               | _ :: ?cs' => spine_skipn k' cs'
               | _ => eval cbv beta iota delta [skipn] in (skipn k cs)
               end
    end.
  Ltac mk_blob W0 W1 W2 W3 W4 HCB :=
    let H1 := fresh "J" in let H2 := fresh "J" in let H3 := fresh "J" in
    chunk_join W3 W4 H1; chunk_join W2 H1 H2; chunk_join W1 H2 H3; chunk_join W0 H3 HCB;
    lazymatch type of HCB with rw_cells ?sg ?mx ?A ?cs =>
      let n := eval cbv in (length cs - 3)%nat in
      let mid := spine_firstn n cs in
      let post := spine_skipn n cs in
      change (rw_cells sg mx A cs) with (rw_cells sg mx A ([] ++ mid ++ post)) in HCB;
      apply (rw_cells_merge sg mx A [] mid post) in HCB;
      cbn [cells_size csize Nat.add app] in HCB;
      change (CB 48 ?j :: ?rest) with (name_blob j 0) in HCB || idtac
    end.

  (* [comment removed for export] *)
  Ltac err_addw r :=
    zstep; rewrite (swrap32_errsum r) by (match goal with H : _ < r <= 0 |- _ => clear -H end; lia);
    zstep;
    let KZ := fresh "KZ" in
    if_cases KZ; zify_cond KZ; [| exfalso; match goal with H : _ < r <= 0 |- _ => clear -H KZ end; rewrite ?unsigned_lit in KZ by lia; lia ].
  Let err_walk' := err_walk L HI HFREE ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m mo h LB PP CUR P END BUF lo bs.
  Let ok_walk' := ok_walk L HI ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m mo h LB PP CUR P END BUF lo bs.
  Notation INNEROB := (InnerOb L HI ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m mo h LB PP CUR P END BUF lo bs).
  Notation OUTEROB := (OuterOb L HI ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m mo h LB PP CUR P END BUF lo bs).


  Local Ltac2 Set LiaOrc.tbl := fun () => "01W0@D11583468241.170D12223852868.169D12223852868.170D15956239675.170D20139305660.170D23171990879.170D28496781288.170D29587001934.169D30051734150.167D30062397050.169D3335936668.170 D34028600543.170D35516918479.169D37216054521.168D37226362885.170D4043386555.170 D4058249799.168 D41254864699.170D43221703716.169D44492853884.170D4453582353.170 D44911907935.170D48538053563.170D49698585326.169D49698585326.170D49705053714.167D49705053714.168D52096270011.170D52208200820.170D54557901199.169D54557901199.170D54728065039.169D54728065039.170D55610685700.169D55610685700.170D59966391303.170D61556549392.170D61571118060.168D62374774592.169D62374774592.170D63263780575.170D65609840527.169D65609840527.170D7748513551.169 D7748513551.170 D9491433734.167 D9491433734.168 L12223852868.163L12223852868.164L15956239675.164L1848725797.165 L1848725797.166 L20141406284.164L23182481327.164L26443884051.166L26443884051.167L29503343994.161L31393302313.167L31393302313.168L3335936668.164 L33692271779.161L33692274097.162L34034888239.164L34478491677.161L3522762990.161 L39941802233.160L4042219941.161 L4042222783.161 L41202929119.160L41202929119.161L41254864699.164L44897224367.164L48538053563.164L52096270011.164L52152720728.162L53271535775.161L54000129951.160L54557901199.163L54557901199.164L54728065039.163L54728065039.164L55610685700.163L55610685700.164L56696518316.168L56696518316.169L63253298223.164L65609840527.163L65609840527.164L7748513551.163 L7748513551.164 L8575978233.160 L9817103909.162 R14961145985.165R17014368079.165R17014368079.166R17279059948.165R18814368075.168R21409711943.165R21843177352.169R22279390051.165R23400515578.165R43756181367.165R61094854874.16500000Q00R00S00T00U00V01?01@01Z02C02D02E02F02_03L04204L04M05105205[05\05]06E06j07C07\07]07^07_07`07a07b07c07d07e08R08k09O0:00:10:20:30:40:50:J0:_0;F0;j0<V0<h0=:0=j0?@0?R0?d0@60@H0@Z0AF0Bl0DQ0Eg0GT0Gf0H80I^0KK0K]0Ko0L[0N10N]0OI0O[0Om0P?0QI0RP0SZ0Ta0UL0V40VF0VX0Wn0Y80Z?0[I0\P0\b0^G0^k0`G0aZ0b?0cF0cX0d_0d`0eA0eB0fHS2sp2PP3CUR2bs3cur2HB5Ha_st5Hl_stFFFFFS2sp2PP3CUR2bs3cur4vlen2q32HB5Ha_st5Hl_stFS2sp2PP3CUR2bs3cur4CPOS2HBS2sp2PP3CUR2bs3cur2q34CPOS2HB5Ha_st5Hl_stFFFS2sp2PP3CUR2bs3PPB3cur2HBS2sp2PP3CUR2bs3PPB3cur4vlen2q32HB5Ha_st5Hl_stS2sp2PP3CUR2bs3cur4CPOS2HB5Ha_st5Hl_stS2sp2PP3CUR2bs3cur4CPOS2HBFS2sp2PP3CUR2bs3cur2q32HB5Ha_st5Hl_stFS2sp2PP3CUR2bs3cur4vlen2q32HB5Ha_st5Hl_stFFS2sp2PP3CUR2bs3cur2q33C642HB5Ha_st5Hl_stS2sp2PP3CUR2bs3cur3C642HB5Ha_st5Hl_stS2sp2PP3CUR2bs3cur3C642HBS2sp2PP3CUR2bs3cur3C642HBFFFFFFFFFS2sp2PP3CUR2bs3PPB3cur4vlen2q32HB5Ha_st5Hl_stS2sp2PP3CUR2bs3PPB3cur2HBS2sp2PP3CUR2bs3cur2q32HB5Ha_st5Hl_stS2sp2PP3CUR2bs3cur2HB5Ha_st5Hl_stFFFFFS2sp2PP3CUR2bs3cur2HBS2sp2PP3CUR2bs3cur2HBS2sp2PP3CUR2bs3cur2q32HD2HB5Ha_st5Hl_stS2sp2PP3CUR2bs3cur2HD2HB5Ha_st5Hl_stS2sp2PP3CUR2bs3cur4vlen2q32HD2HB5Ha_st5Hl_stS2sp2PP3CUR2bs3curS2sp2PP3CUR2bs3curS2sp2PP3CUR3BUF2bs3cur4vlen2q32HB5Ha_st5Hl_st2HDS1L2sp2PP3CUR2lo2bs2D13PPB4CURB3SLO3HLS3ACL3ACP3DS23cur4vlen2q34CPOS2HB5Ha_st5Hl_st2HDS2sp2PP3CUR2bs3curS2sp2PP3CUR2bs3curS2sp2PP3CUR2bs3curS2sp2PP3CUR2bs3curS2sp2PP3CUR2bs3curS2sp2PP3CUR2bs3cur4vlen2q32HD2HB5Ha_st5Hl_stS1L2sp2PP3CUR1P3END3BUF2lo2bs2B12B32B43PPB4CURB3NZ33SLO3HLS3ACL3ACP3cur4vlen2es2q33Hq13He23Hes4CPOS2LRS1L2sp2PP3CUR1P3END3BUF2lo2bs2B12B32B43PPB4CURB3NZ33SLO3HLS3ACL3ACP3cur4vlen2es2q33Hq13Hes4CPOS2LR2KSS1L2sp2PP3CUR2lo2bs2D13PPB4CURB3SLO3HLS3ACL3ACP3DS23cur4vlen2q34CPOS2HB5Ha_st5Hl_st2HDS1L2sp2PP3CUR1P3END3BUF2lo2bs2B12B32B43PPB4CURB3NZ33SLO3HLS3ACL3ACP3cur4vlen2e22es2q33Hq13Hq23He23Hes4CPOS2LRS2sp2PP3CUR2bs3curS2sp2PP3CUR2bs3curS1L2sp2PP3CUR1P3END3BUF2lo2bs2B12B32B43PPB4CURB3NZ33SLO3HLS3ACL3ACP3cur4vlen2es2q33Hq13He23Hes4CPOS2LRS1L2sp2PP3CUR1P3END3BUF2lo2bs2B12B32B43PPB4CURB3NZ33SLO3HLS3ACL3ACP3cur4vlen2e22es2q33Hq13Hq23He23Hes4CPOS2LRS2sp2PP3CUR2bs3curS2sp2PP3CUR2bs3curS2sp2PP3CUR2bs3cur4vlen2q32HD2HB5Ha_st5Hl_stS1L2sp2PP3CUR2lo2bs2D13PPB4CURB3SLO3HLS3ACL3ACP3DS23cur4vlen2q34CPOS2HB5Ha_st5Hl_st2HDS2sp2PP3CUR2bs3cur4vlen2q32HD2HB5Ha_st5Hl_stS2sp2PP3CUR2bs3cur4vlen2q32HD2HB5Ha_st5Hl_stS2sp2PP3CUR2bs3curS2sp2PP3CUR2bs3curS2sp2PP3CUR2bs3curS1L2sp2PP3CUR2lo2bs3PPB4CURB3SLO3HLS3ACL3ACP3cur2q34CPOS2HD2HB5Ha_st5Hl_stS1L2sp2PP3CUR2lo2bs3PPB4CURB3SLO3HLS3ACL3ACP3cur4CPOS2HD2HB5Ha_st5Hl_stS1L2sp2PP3CUR2lo2bs3PPB4CURB3SLO3HLS3ACL3ACP3cur2q34CPOS2HD2HB5Ha_st5Hl_stS1L2sp2PP3CUR2lo2bs3PPB4CURB3SLO3HLS3ACL3ACP3cur4CPOS2HD2HB5Ha_st5Hl_stS2sp2PP3CUR3BUF2bs3cur2q32HD2HB5Ha_st5Hl_stS2sp2PP3CUR3BUF2bs3cur2HD2HB5Ha_st5Hl_stS2sp2PP3CUR2bs3curS2sp2PP3CUR2bs3curS1L2sp2PP3CUR2lo2bs2D13PPB4CURB3SLO3HLS3ACL3ACP3DS23cur4vlen2q34CPOS2HB5Ha_st5Hl_st2HDS1L2sp2PP3CUR2lo2bs3PPB4CURB3SLO3HLS3ACL3ACP3cur2q34CPOS2HD2HB5Ha_st5Hl_stS1L2sp2PP3CUR2lo2bs3PPB4CURB3SLO3HLS3ACL3ACP3cur4CPOS2HD2HB5Ha_st5Hl_stS1L2sp2PP3CUR2lo2bs3PPB4CURB3SLO3HLS3ACL3ACP3cur2q34CPOS2HD2HB5Ha_st5Hl_stS1L2sp2PP3CUR2lo2bs3PPB4CURB3SLO3HLS3ACL3ACP3cur4CPOS2HD2HB5Ha_st5Hl_stS2sp2PP3CUR2bs3curS1L2sp2PP3CUR1P3END3BUF2lo2bs2B12B32B43PPB4CURB3NZ33SLO3HLS3ACL3ACP3cur4vlen2es2q33Hq13Hes4CPOS2LR2KSS2sp2PP3CUR2bs3cur4vlen2es2q33He22KSS1L2sp2PP3CUR1P3END2lo2bs3PPB4CURB3SLO3HLS3ACL3ACP3cur4vlen2e22es2q33Hq13Hq23He23Hes4CPOS2LRS1L2sp2PP3CUR1P3END2lo2bs3PPB4CURB3SLO3HLS3ACL3ACP3cur4vlen2es2q33Hq14CPOS2LR2KS2KES2sp2PP3CUR3END2bs3cur4vlen2q33Hes2KES1L2sp2PP3CUR2lo2bs3PPB4CURB3SLO3HLS3ACL3ACP3cur4vlen2e22q33Hq24CPOS2KMS2sp2PP3CUR2bs3curS1L2sp2PP3CUR2lo2bs3PPB4CURB3SLO3HLS3ACL3ACP3cur4vlen2es2q33He24CPOS2KSFS2sp2PP3CUR2bs3cur4vlen2p02q33Hp0FS1L2sp2PP3CUR1P2lo2bs3PPB4CURB3SLO3HLS3ACL3ACP3cur4vlen2q33Hq14CPOS2LR". (* [comment removed for export] *)
  Lemma l3_walk : ltac2:(CDefT.buildp (gd_tbl_P_x509_get_name_D ()) "Pnodes,(0.$1.)Pcur,$1.Pslen,(2.&40.)Palen,(2.&40.)Pj8,(0.(2.&8.))Potw,(2.&40.)Pr0,(0.(2.&8.))Polen,(2.&40.)Pop,$1.Pvtw,(2.&40.)Pr1,(0.(2.&8.))Pvlen,(2.&40.)Pj2,(0.(2.&8.))Pmg,(2.&8.)Pp7,(0.(2.&8.))Pp0,$1.Pe2,$1.Pes,$1.Pq3,$1.Px1,(2.&40.)Px5,(2.&40.)Px6,(2.&40.)Px7,(2.&40.)Px10,(2.&40.)Px11,(2.&40.)Px12,(2.&40.)Px13,(2.&40.)Px14,(2.&40.)Px15,(2.&40.)Px16,(2.&40.)Px17,(2.&40.)Px28,(2.&40.)Px29,(2.&40.)Px30,(2.&40.)Px31,(2.&40.)Pmm,P,(2.&40.)(3.(2.&8.))Pmoc,$4.Phc,(5.$6.VL,VHI,)P,(7.VL,VHI,Vra,Vsp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,Vm,Vmo,Vh,VLB,VPP,VCUR,VBUF,Vlo,Vbs,(8.&40.+????????????=<1:.)(8.&40.+????????????=<20.)R3.R2.R1.R26.R25.R24.R23.R22.)P,(9.$6.R4.R26.(:.$;.(<.R22.)(:.$;.(=.#4.R21.)(>.$;.))))P,(9.$6.R5.(?.R27.+8.)(:.$;.(10.R21.)(>.$;.)))P,(9.$6.R6.(?.R28.+10.)(:.$;.(10.(8.&40.R21.))(:.$;.(<.R20.)(:.$;.(=.#4.R1?.)(>.$;.)))))P,(9.$6.R7.(?.R29.+20.)(:.$;.(10.R1?.)(>.$;.)))P,(9.$6.R8.(?.R2:.+28.)(:.$;.(=.#8.R1?.)(:.$;.(10.(8.&40.=))(:.$;.(11.R1>.)(:.$;.(=.#7.R1=.)(>.$;.))))))P,(9.$6.R9.VPP,(:.$;.(10.(8.&40.R1:.))(>.$;.)))P,(12.VP,R1;.)P,(12.(13.&40.R23.)(14.R1>.R1<.))P,(15.R20.R1?.)P,(12.R20.R1?.)P,(12.R20.VEND,)P,Pp',$1.Pes',$1.P,(15.R25.R2.)(16.VL,VHI,Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,Vm,Vmo,Vh,VLB,VPP,VCUR,VP,VEND,VBUF,Vlo,Vbs,R3.R2.)P,Pp',$1.P,(15.R25.R1.)(17.VL,VHI,Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,Vm,Vmo,Vh,VLB,VPP,VCUR,VP,VEND,VBUF,Vlo,Vbs,R2.)(18.$6.R10.(19.$6.VL,VHI,Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,Vh,VLB,VPP,VCUR,VP,VEND,Vlo,Vm,Vmo,)(1:.(1;.R21.(8.&40.(?.(13.&40.Vsp,)-90.))Vgp,Vtp,R20.R1?.R1>.(8.&40.R33.)(8.&40.-2880.)R1=.R1<.R1;.R1:.R19.R18.R17.R16.(8.&40.VEND,)(8.&40.VPP,)(8.&40.R23.)(8.&40.R24.)(8.&40.+1.)(8.&40.VCUR,)(8.&40.=)(8.&40.+1.)(8.&40.+50581008.)(8.&40.-2380.)R15.R14.R13.R12.)VF,(8.&40.+27?1<.)Vfc,(1<.(2.&40.))R11.(1=.$6.)))")
(* [comment removed for export] *).
  Proof.
    intros nodes cur slen alen j8 otw r0 olen op vtw r1 vlen j2 mg p7 p0 e2 es q3 x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 mm moc hc
      INV W0 W1 W2 W3 W4 HPP Hq1 Hq2 Hp0 He2 Hes KIN KOUT.
    open_ninv INV. clear INV.
    pose proof (bv_unsigned_in_range 64 vlen) as LR. unfold bv_modulus in LR. cbn in LR.
    pose proof (cur_wrange' nodes cur _ HFR HCF ltac:(intros b Hb; exact Hb)) as CWc0.
    pose proof CWc0 as CWc. rewrite <- HT in CWc. pose proof HTOP as HTOPc. rewrite <- HT in HTOPc.
    pose proof CWPP as CWp. rewrite <- HT in CWp.
    start_W cur.
    zstep. zstep. zstep. zstep. zstep. chk. zstep. zstep. zstep. zstep. chk. zstep. zstep. if_cases KM; zify_cond KM.
    { (* [comment removed for export] *)
      zstep. zstep.
      replace (Z_to_bv 64 18446744073709542426) with (Z_to_bv 64 (-9190)) by (apply bv_eq; reflexivity).
      wsync. mk_blob W0 W1 W2 W3 W4 HCB. rebuild_ninv INV2.
      eapply err_walk'; try exact INV2; try eassumption; plia. }
    rewrite ?unsigned_lit in KM by plia. assert (Ee2 : e2 = q3 + bv_unsigned vlen) by plia. subst e2.
    zstep. zstep. if_cases KS; zify_cond KS.
    { (* [comment removed for export] *)
      rewrite ?unsigned_lit in KS by plia.
      wsync. mk_blob W0 W1 W2 W3 W4 HCB. rebuild_ninv INV2.
      eapply alloc_inner; try exact INV2; try eassumption; try plia. apply KIN. plia. }
    rewrite ?unsigned_lit in KS by plia.
    zstep. if_cases KE; zify_cond KE.
    { (* [comment removed for export] *)
      rewrite ?unsigned_lit in KE by plia.
      wsync. mk_blob W0 W1 W2 W3 W4 HCB. rebuild_ninv INV2.
      eapply ok_walk'; try exact INV2; try eassumption; plia. }
    (* [comment removed for export] *)
    rewrite ?unsigned_lit in KE by plia.
    assert (Ees : es = q3 + bv_unsigned vlen) by plia. subst es.
    wsync. mk_blob W0 W1 W2 W3 W4 HCB. rebuild_ninv INV2.
    eapply alloc_outer; try exact INV2; try eassumption; try plia. apply KOUT. plia.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

End Walk.
