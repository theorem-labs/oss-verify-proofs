(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Walk Asn1Aux AStep CellsX Image.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Spec Require Import Rep.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.P Require Import PImg P_string P_oid P_oid_x509_ext.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import DietDestruct.   (* [comment removed for export] *)
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import LiaOrc. (* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= orc_lia. (* [comment removed for export] *)
Local Ltac dlia ::= orc_dlia. (* [comment removed for export] *)
Local Ltac plia ::= orc_plia. (* [comment removed for export] *)
Local Ltac clear_disj ::= fc_clear_disj. (* [comment removed for export] *)
Local Ltac prune_disj ::= fc_prune_disj. (* [comment removed for export] *)
Ltac2 gd_tbl_P_oid_sig_alg_A () : Init.string Init.list := ["stdpp.bitvector.definitions.bv"; "Corelib.Init.Datatypes.list"; "Corelib.Init.Datatypes.option"; "OSSVerify.KrLib.Lib.Step.rw_cells"; "OSSVerify.KrLib.P.PImg.psegs"; "Stdlib.ZArith.BinInt.Z.add"; "stdpp.bitvector.definitions.bv_unsigned"; "Corelib.Init.Datatypes.cons"; "OSSVerify.KrLib.Lib.Cells.cell"; "OSSVerify.KrLib.Lib.Cells.CB"; "OSSVerify.KrLib.Lib.Cells.C8"; "Corelib.Init.Datatypes.nil"; "stdpp.bitvector.definitions.Z_to_bv"; "OSSVerify.KrLib.Lib.Frame.stk"; "OSSVerify.KrLib.Lib.Cells.C4"; "OSSVerify.KrLib.Lib.Mem.mem_inv"; "OSSVerify.KrLib.Lib.AStep.statics_ok"; "OSSVerify.KrLib.Lib.Frame.munch"; "Corelib.Init.Datatypes.prod"; "Corelib.Numbers.BinNums.Z"; "Corelib.Init.Datatypes.pair"; "Stdlib.ZArith.BinInt.Z.sub"; "OSSVerify.KrLib.Lib.Frame.wmono"; "OSSVerify.KrLib.Lib.Exec.evt"; "OSSVerify.KrLib.P.P_oid.oid_lookup2_post"; "OSSVerify.KrLib.Lib.MState.MS"; "OSSVerify.KrLib.Lib.Frame.mkR"; "Corelib.Init.Datatypes.None"; "OSSVerify.KrLib.Lib.PropExec.seg_rom"; "Stdlib.Lists.List.In"; "Walk.offsets"; "P_OID_SIG_ALG_TBL"].


Definition P_OID_GET_SIG_ALG : Z := 0x246cc.
Definition P_OID_SIG_ALG_TBL : Z := 0x44c80.
Notation OID_SIG_ALG_TBLN := 560 (only parsing).
Notation OID_SIG_ALG_STACK := 64 (only parsing).

Section Walk.
  Variable L : heap_layout.
  Variables (ra sp gp tp t0 t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : mem) (OID E1 E2 P LEN lo : Z) (tg pd : word) (xs : list byte).
  Hypothesis HLEN : Z.of_nat (length xs) = LEN.
  Hypothesis D1 : E1 + 4 <= OID \/ OID + 24 <= E1.
  Hypothesis D2 : E1 + 4 <= P \/ P + LEN <= E1.
  Hypothesis D3 : E2 + 4 <= OID \/ OID + 24 <= E2.
  Hypothesis D4 : E2 + 4 <= P \/ P + LEN <= E2.
  Hypothesis D5 : E1 + 4 <= E2 \/ E2 + 4 <= E1.
  Hypothesis AL1 : OID mod 8 = 0.
  Hypothesis AL2 : E1 mod 4 = 0.
  Hypothesis AL3 : E2 mod 4 = 0.
  Hypothesis NZ1 : 0 < OID.
  Hypothesis NZ2 : 0 < E1.
  Hypothesis NZ4 : 0 < E2.
  Hypothesis NZ3 : 0 < P.
  Hypothesis SLO : lo <= bv_unsigned sp - 64.
  Hypothesis ACL : alloc_ceiling <= lo.
  Hypothesis ACP : 4096 < alloc_ceiling.
  Hypothesis SPA : bv_unsigned sp mod 16 = 0.
  Hypothesis DS1 : OID + 24 <= lo \/ bv_unsigned sp <= OID.
  Hypothesis DS2 : E1 + 4 <= lo \/ bv_unsigned sp <= E1.
  Hypothesis DS4 : E2 + 4 <= lo \/ bv_unsigned sp <= E2.
  Hypothesis DS3 : P + LEN <= lo \/ bv_unsigned sp <= P.
  Hypothesis CA : const_at L P_OID_SIG_ALG_TBL 560.
  Hypothesis DHI : hl_data_hi L <= alloc_ceiling.
  Hypothesis OD1 : E1 + 4 <= hl_data_lo L \/ hl_data_hi L <= E1.
  Hypothesis OD2 : E2 + 4 <= hl_data_lo L \/ hl_data_hi L <= E2.
  Hypothesis SPR : bv_unsigned sp < 2^64.
  Hypothesis E1B : E1 + 4 <= 2^64.
  Hypothesis E2B : E2 + 4 <= 2^64.
  Hypothesis PB : P + LEN <= 2^64.
  Hypothesis OIDB : OID + 24 <= 2^64.

  Notation W := [(E1, E1 + 4); (E2, E2 + 4); (bv_unsigned sp - 64, bv_unsigned sp)].
  Notation POST := (oid_lookup2_post psegs L ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc E1 E2 64 lo m).
  Notation SPF := (Z_to_bv 64 (bv_unsigned sp + -64)).
  (* [comment removed for export] *)
  Notation FRAME1 mm j := (rw_cells psegs mm (bv_unsigned sp + -32) [CB 8 j; C8 s1; C8 s0; C8 ra]).
  Notation FRAME2 mm j := (rw_cells psegs mm (bv_unsigned sp + -64) [CB 8 j; C8 (Z_to_bv 64 E1); C8 (Z_to_bv 64 E2); C8 (Z_to_bv 64 0x246e8)]).
  Notation TBLC := P_OID_SIG_ALG_TBL (only parsing).

  Definition offsets : list Z := [0; 40; 80; 120; 160; 200; 240; 280; 320; 360; 400; 440; 480].

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00<0?L12283411672.83L21887662552.83L33510041944.83L36425601695.93L39945925021.93L40631351218.94L41564619544.92L44866963580.92L48429268312.83L55299355981.81L66083662040.83L8722184664.83 00000A00R00c01;01S01d02502F02W02X02i03:S2sp3OID2E12E22xsS2sp3OID2E12E22xsS2sp3OID2E12E22xsS2sp3OID2E12E22lo2xs3SLOS2sp3OID2E12E22lo2xs3SLOS2sp3OID2E12E22xsS2sp3OID2E12E22xsS2sp3OID2E12E22xsS2sp3OID2E12E22xsFS2sp3OID2E12E22xsS2sp3OID2E12E22xs". (* [comment removed for export] *)
  #[using="xs SLO"] Lemma nf_walk : ltac2:(CDefT.buildp (gd_tbl_P_oid_sig_alg_A ()) "Pv1,(0.&40.)Pv2,(0.&40.)Pj1,(1.(0.&8.))Pj2,(1.(0.&8.))Px1,(0.&40.)Px5,(0.&40.)Px6,(0.&40.)Px7,(0.&40.)Px9,(0.&40.)Px10,(0.&40.)Px11,(0.&40.)Px12,(0.&40.)Px13,(0.&40.)Px14,(0.&40.)Px15,(0.&40.)Px16,(0.&40.)Px17,(0.&40.)Pmm,P,(0.&40.)(2.(0.&8.))P,(3.$4.R1.(5.(6.&40.Vsp,)-20.)(7.$8.(9.#8.R10.)(7.$8.(:.Vs1,)(7.$8.(:.Vs0,)(7.$8.(:.Vra,)(;.$8.))))))P,(3.$4.R2.(5.(6.&40.Vsp,)-40.)(7.$8.(9.#8.R10.)(7.$8.(:.(<.&40.VE1,))(7.$8.(:.(<.&40.VE2,))(7.$8.(:.(<.&40.+246>8.))(;.$8.))))))P,(=.$4.R3.Vlo,(5.(6.&40.Vsp,)-40.))P,(3.$4.R4.VE1,(7.$8.(>.R15.)(;.$8.)))P,(3.$4.R5.VE2,(7.$8.(>.R15.)(;.$8.)))P,(?.$4.R6.)P,(10.$4.VL,R7.)P,(11.(7.(12.$13.$13.)(14.$13.$13.VE1,(5.VE1,+4.))(7.(12.$13.$13.)(14.$13.$13.VE2,(5.VE2,+4.))(7.(12.$13.$13.)(14.$13.$13.(15.(6.&40.Vsp,)+40.)(6.&40.Vsp,))(;.(12.$13.$13.)))))Vm,R8.)P,(16.$4.Vm,R9.)(17.$4.(18.$4.VL,Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,VE1,VE2,+40.Vlo,Vm,)(19.(1:.R17.(<.&40.(5.(6.&40.Vsp,)-40.))Vgp,Vtp,R16.R15.R14.(<.&40.VOID,)R13.R12.R11.R10.R?.R>.R=.R<.R;.Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,Vt3,Vt4,Vt5,Vt6,)VF,(<.&40.+245><.)Vfc,(1;.(0.&40.))R:.(1<.$4.)))")
(* [comment removed for export] *).
  Proof.
    intros v1 v2 j1 j2 x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 mm FR1 FR2 ST HE1 HE2 MI SOK MU WM.
    zstep. zstep. zstep. zstep. zstep. zstep.
    release_frame FR2 ST (bv_unsigned sp + -32).
    zstep. if_cases K; zify_cond K. 2:{ exfalso. apply K. reflexivity. }
    zstep. zstep. zstep. zstep. zstep. zstep.
    release_frame FR1 ST (bv_unsigned sp). fin. right; reflexivity.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "01K0?L12283411672.85L12846590103.94L12987450376.94L1436991255.94 L2168584584.94 L21887662552.84L23651565704.94L25873210038.88L25883691078.87L30250428181.88L30265112037.87L30516272663.94L31070219271.84L32338418312.94L32729788439.94L32756759073.87L32758851793.86L32968077845.88L32982753509.87L33509878807.94L33510041944.84L34391641495.94L34485128968.94L36066722455.94L36425585682.95L38748215187.84L39941747874.94L40631351218.96L41272978977.82L41475297813.88L41489973477.87L41564619544.93L42689139221.88L42691231973.87L4298385928.94 L42988009692.87L42994297388.88L43172096264.94L43322544743.85L43333142171.87L44866963580.94L45301914504.94L45567033239.94L47048265957.87L47054553621.88L47328731365.87L47343415829.88L48429268312.85L49412946197.88L49423428581.87L49563137643.84L49563137643.85L49714907543.94L52044530455.94L53888426957.87L53903110461.88L53990978952.94L56120780296.94L58558298389.88L58564586469.87L59042599634.86L59052934702.84L59564462979.84L59570866047.86L60344101143.94L60681600890.94L60719410440.94L6215885029.87 L6217986581.88 L6222738231.85 L62384512789.88L62386605541.87L62849228680.94L62936842773.88L62943138021.87L63342143480.87L63344390916.85L63454145687.94L63681051543.94L64223590835.87L64238267203.86L64663106325.88L64673587685.87L6597766280.94 L66083662040.84L66290485525.88L66300976101.87L67936503281.85L7852754538.86 L7867438234.87 L8722184664.85 00000A00R00c01401E01V01g02L02M03Q03R03c04404E04V05Z05[06_06`07107B07S07d08508M08^09609G09X0:\0:]0:n0<20<30<D0<E0=I0=Z0>20>V0>g0?80?I0?J0@N0@O0AS0Ad0Bh0Bi0C=0CQ0Cb0D30D40DW0Dh0E90F=0F>0Fb0G:0GR0H60HG0HX0Hi0Hj0In0J?0KC0KD0KU0LY0LZ0M>0MV0Mg0N80N]0N^0Ob0Oc0P40PE0QI0QJ0Q[0Q\0R?0RPS2sp3OID2E12E22xsS2sp3OID2E12E22xsS2sp3OID2E12E22xsS2sp3OID2E12E22xsS2sp3OID2E12E22xsS2sp3OID2E12E22xsS2sp3OID2E12E22xsS1L2sp3OID2E12E22xs2HB5Ha_st5Hl_st2HDFS1L2sp3OID2E12E22lo2xs3NZ13NZ43SLO3ACL3DHI3CA13CA22HB5Ha_st5Hl_st2HDFS2sp3OID2E12E22xsS2sp3OID2E12E22xsS2sp3OID2E12E22xsS2sp3OID2E12E22xsS1L2sp3OID2E12E22lo2xs3NZ13NZ23NZ43SLO3ACL3DHI3CA22HB5Ha_st5Hl_st2HDFS1L2sp3OID2E12E22lo2xs3NZ13NZ43SLO3ACL3DHI3CA13CA22HB5Ha_st5Hl_st2HDFS2sp3OID2E12E22xsS2sp3OID2E12E22xsS2sp3OID2E12E22xsS2sp3OID2E12E22xsS2sp3OID2E12E22xsS2sp3OID2E12E22lo2xs3SLOS2sp3OID2E12E22xsS2sp3OID2E12E22lo2xs3SLOS2sp3OID2E12E22xsS2sp3OID2E12E22xsS1L2sp3OID2E12E22lo2xs3NZ13NZ43SLO3ACL3DHI3CA13CA22HB5Ha_st5Hl_st2HDFS2sp3OID2E12E22xsS1L2sp3OID2E12E22lo2xs3NZ13NZ43SLO3ACL3DHI3CA13CA22HB5Ha_st5Hl_st2HDFS2sp3OID2E12E22xsFS1L2sp3OID2E12E22lo2xs3NZ13NZ23NZ43SLO3ACL3DHI3CA22HB5Ha_st5Hl_st2HDS2sp3OID2E12E22xsS2sp3OID2E12E22xs3E1B2HBS2sp3OID2E12E22xs3E1B2HB5Ha_st5Hl_stS2sp3OID2E12E22xsS2sp3OID2E12E22xsS2sp3OID2E12E22xsFS1L2sp3OID2E12E22lo2xs3NZ13NZ43SLO3ACL3DHI3CA13CA22HB5Ha_st5Hl_st2HDFS1L2sp3OID2E12E22lo2xs3NZ13NZ43SLO3ACL3DHI3CA13CA22HB5Ha_st5Hl_st2HDS2sp3OID2E12E22xsS1L2sp3OID2E12E22lo2xs3NZ13NZ43SLO3ACL3DHI3CA13CA22HB5Ha_st5Hl_st2HDFS2sp3OID2E12E22xs2HBS2sp3OID2E12E22xs2HBS2sp3OID2E12E22xsS2sp3OID2E12E22xsFS2sp3OID2E12E22xs2HB5Ha_st5Hl_st2HDS2sp3OID2E12E22xsS2sp3OID2E12E22xsS1L2sp3OID2E12E22lo2xs3NZ13NZ43SLO3ACL3DHI3CA13CA22HB5Ha_st5Hl_st2HDFS2sp3OID2E12E22xs3E2B2HB5Ha_st5Hl_stS2sp3OID2E12E22xs3E2B2HBS2sp3OID2E12E22xs3NZ42HBS2sp3OID2E12E22xs3NZ42HB5Ha_st5Hl_stS2sp3OID2E12E22xsS2sp3OID2E12E22xsS2sp3OID2E12E22xsFS1L2sp3OID2E12E22lo2xs3NZ13NZ43SLO3ACL3DHI3CA13CA22HB5Ha_st5Hl_st2HDS2sp3OID2E12E22xsS1L2sp3OID2E12E22lo2xs3NZ13NZ43SLO3ACL3DHI3CA13CA22HB5Ha_st5Hl_st2HDFS2sp3OID2E12E22xsS1L2sp3OID2E12E22lo2xs3NZ13NZ43SLO3ACL3DHI3CA13CA22HB5Ha_st5Hl_st2HDFS2sp3OID2E12E22xs3NZ22HB5Ha_st5Hl_stS2sp3OID2E12E22xs3NZ22HBS2sp3OID2E12E22xsS2sp3OID2E12E22xsS1L2sp3OID2E12E22xs2HB5Ha_st5Hl_st2HDFS1L2sp3OID2E12E22lo2xs3NZ13NZ43SLO3ACL3DHI3CA13CA22HB5Ha_st5Hl_st2HDFS2sp3OID2E12E22xsS2sp3OID2E12E22xsS1L2sp3OID2E12E22lo2xs3NZ13NZ43SLO3ACL3DHI3CA13CA22HB5Ha_st5Hl_st2HDFS2sp3OID2E12E22xsFS2sp3OID2E12E22xs2HB5Ha_st5Hl_st2HDS2sp3OID2E12E22xs". (* [comment removed for export] *)
  #[using="LEN xs HLEN D5 NZ1 NZ2 NZ4 SLO ACL DS2 DS4 CA DHI OD1 OD2 E1B E2B"] Lemma found_walk : ltac2:(CDefT.buildp (gd_tbl_P_oid_sig_alg_A ()) "Pk,$13.Pv1,(0.&40.)Pv2,(0.&40.)Pj1,(1.(0.&8.))Pj2,(1.(0.&8.))Px1,(0.&40.)Px5,(0.&40.)Px6,(0.&40.)Px7,(0.&40.)Px9,(0.&40.)Px11,(0.&40.)Px12,(0.&40.)Px13,(0.&40.)Px14,(0.&40.)Px15,(0.&40.)Px16,(0.&40.)Px17,(0.&40.)Pmm,P,(0.&40.)(2.(0.&8.))P,(1=.$13.R12.$1>.)P,(3.$4.R2.(5.(6.&40.Vsp,)-20.)(7.$8.(9.#8.R10.)(7.$8.(:.Vs1,)(7.$8.(:.Vs0,)(7.$8.(:.Vra,)(;.$8.))))))P,(3.$4.R3.(5.(6.&40.Vsp,)-40.)(7.$8.(9.#8.R10.)(7.$8.(:.(<.&40.VE1,))(7.$8.(:.(<.&40.VE2,))(7.$8.(:.(<.&40.+246>8.))(;.$8.))))))P,(=.$4.R4.Vlo,(5.(6.&40.Vsp,)-40.))P,(3.$4.R5.VE1,(7.$8.(>.R15.)(;.$8.)))P,(3.$4.R6.VE2,(7.$8.(>.R15.)(;.$8.)))P,(?.$4.R7.)P,(10.$4.VL,R8.)P,(11.(7.(12.$13.$13.)(14.$13.$13.VE1,(5.VE1,+4.))(7.(12.$13.$13.)(14.$13.$13.VE2,(5.VE2,+4.))(7.(12.$13.$13.)(14.$13.$13.(15.(6.&40.Vsp,)+40.)(6.&40.Vsp,))(;.(12.$13.$13.)))))Vm,R9.)P,(16.$4.Vm,R:.)(17.$4.(18.$4.VL,Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,VE1,VE2,+40.Vlo,Vm,)(19.(1:.R17.(<.&40.(5.(6.&40.Vsp,)-40.))Vgp,Vtp,R16.R15.R14.(<.&40.VOID,)R13.(<.&40.(5.$1?.R1<.))R12.R11.R10.R?.R>.R=.R<.Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,Vt3,Vt4,Vt5,Vt6,)VF,(<.&40.+245?0.)Vfc,(1;.(0.&40.))R;.(1<.$4.)))")
(* [comment removed for export] *).
  Proof.
    intros k v1 v2 j1 j2 x1 x5 x6 x7 x9 x11 x12 x13 x14 x15 x16 x17 mm Hk FR1 FR2 ST HE1 HE2 MI SOK MU WM.
    pose proof CA as CA'. unfold const_at in CA'. ddestruct CA' as (CA1 & CA2 & _).
    unfold P_OID_SIG_ALG_TBL in *.
    destruct Hk as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]]]]]]; cbn [Z.add].
    all: lazymatch goal with |- evt _ _ (MS (mkR _ _ _ _ _ _ _ _ _ (Z_to_bv 64 ?e) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _ _ _ _ _ _) =>
           let a := eval vm_compute in (e + 32) in
           let bs := eval vm_compute in (match image_bytes psegs a 8 with Some bs => bs | None => [] end) in
           pose proof (statics_ok_cells psegs L mm a bs SOK ltac:(eapply const_at_sub; [exact CA| cbn; lia| cbn; lia]) ltac:(vm_compute; reflexivity)) as TB;
           cbn [length] in TB
         end.
    all: zstep; zstep; zstep; zstep; zstep.
    all: release_frame FR2 ST (bv_unsigned sp + -32).
    all: zstep; if_cases K; zify_cond K; [exfalso; revert K; cbn; rewrite ?unsigned_lit by lia; lia|].
    all: zstep; zstep; zstep; zstep; zstep; clear TB; zstep; zstep.
    all: zstep; zstep; zstep; zstep; zstep.
    all: match goal with FR : rw_cells _ _ (bv_unsigned sp + -32) _, ST' : stk _ _ lo _ |- _ => release_frame FR ST' (bv_unsigned sp) end.
    all: fin; left; reflexivity.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
End Walk.
