(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Walk Asn1Aux AStep CellsX Image.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Spec Require Import Rep.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.P Require Import PImg P_string P_oid P_oid_x509_ext.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.LX Require Import LxExpr LxDec LxMem LxStep LxRun LxDenot LxSoundRun LxSum LxSoundSum LxTac.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.LXP Require Import LxPTac LxP_SumsOid.

Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Import OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.LxhSyntax. #[local] Instance lxh_tab : OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.lx_hints := OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.lxh_parse "P012a2afcc2c263b8 0 4 0 8 20 8 43 8 44 8P0205d7df41c6c505 2 19 1 1 4 3 2 1 30 1 31 1 5 0 4 21 4 29 4 32 4 33 16 1 1 4 3 1 1 29 1 32 1 4 0 4 30 4 31 4 33 16P05c9c13eed867fd9 2 20 1 1 8 3 2 1 30 1 31 1 5 0 2 21 2 29 2 32 2 33 16 1 1 8 3 1 1 29 1 32 1 4 0 2 30 2 31 2 33 16P061346c148ce5e2d 0 3 0 1 2 1 43 1P07f3bbf97193cc97 0 2 0 1 33 1P09bb3cf6b0835012 2 18 0 6 0 1 3 1 22 1 26 1 30 1 31 1 0 4 0 1 2 1 30 1 31 1P0b78801148a27326 2 19 1 1 4 3 2 1 30 1 31 1 5 0 4 21 4 29 4 32 4 33 16 1 1 4 3 1 1 29 1 32 1 4 0 4 30 4 31 4 33 16P0c4ad36a8aa757f7 0 2 0 1 32 1P0f6edee5474d33f2 0 3 0 1 2 1 44 1P1052e644de1eadff 0 2 0 1 2 1P121de041ac194f5e 0 4 0 1 5 1 36 1 40 1P12f5a2958353d23c 0 3 0 1 6 1 39 1P13295789f87a0fde 0 4 0 1 8 1 42 1 43 1P13cd86f1bb672430 2 20 1 1 8 3 2 1 30 1 31 1 5 0 2 21 2 29 2 32 2 33 16 1 1 8 3 1 1 29 1 32 1 4 0 2 30 2 31 2 33 16P14a87d04b59de1f7 0 2 0 1 2 1P159118c8ae5dc7a8 0 2 0 1 1 1P168ccdaff4e0adc4 0 3 0 1 6 1 39 1P171b30467ccb7045 0 4 0 1 9 1 43 1 44 1P19579ea892db8890 0 4 0 1 7 1 41 1 42 1P1c78194558de092d 0 2 0 1 40 1P1d19cda964062a6e 0 2 0 1 1 1P1db0972fc367a3c5 0 2 0 1 2 1P1ecfd3b3c4e7d227 0 2 0 1 27 1P204cf977d7bd1a4e 0 3 0 1 2 1 42 1P20ab1ecfaba58251 0 3 0 1 6 1 39 1P21451d708a2b3fc3 2 20 1 1 8 3 2 1 30 1 31 1 5 0 2 21 2 29 2 32 2 33 16 1 1 8 3 1 1 29 1 32 1 4 0 2 30 2 31 2 33 16P2326d8fae7cfaaeb 0 4 0 1 5 1 36 1 40 1P267fdac46d82b75e 0 2 0 1 30 1P26b83930d7cad1b7 0 2 0 1 38 1P274c79d09b5b79e7 2 18 0 6 0 1 3 1 22 1 26 1 30 1 31 1 0 4 0 1 2 1 30 1 31 1P2a85935a503b81d0 2 18 0 6 0 1 3 1 22 1 26 1 30 1 31 1 0 4 0 1 2 1 30 1 31 1P2c2f6a492cc09bab 0 2 0 1 29 1P2e28f385c2d0a69f 1 1 8 2 0 1 43 1 3 21 1 44 1 45 8P2e67cfddaf81ae8a 0 4 0 1 5 1 36 1 40 1P2f191162958d73f1 1 1 8 2 38 1 44 1 3 0 1 43 1 45 8P2fc02bf6e02eeb1f 0 3 0 1 6 1 39 1P3012a1fd08a26507 0 3 0 1 6 1 39 1P35240699bc3c68e5 0 2 0 1 2 1P352a6219cf910930 0 2 0 1 1 1P3574c813f7de95e2 0 3 0 1 6 1 39 1P38cfefdb65384116 2 19 1 1 4 3 2 1 30 1 31 1 5 0 4 21 4 29 4 32 4 33 16 1 1 4 3 1 1 29 1 32 1 4 0 4 30 4 31 4 33 16P3b381491ed3a217c 0 2 0 1 2 1P3b9ed26d90daddbe 0 2 0 1 39 1P3c10b7b343bdc56f 0 2 0 1 2 1P3fdf137707095afe 0 2 0 1 26 1N000c927d6fa92020N006d651852ca577bN0077611c95a4a53dN01dd16e1d027da2dN02208a630757d2ccN02719e6d21c2e0f3N02b8a7d382d3897cN03324b3be6a23e55N0395388d33491200N03bad6c4117f83a7N04559de9b6c0548aN049e19d5a9a4793fN0513397f8974d581N051ed8f255aa4ea2N052b3652be698c96N05bbac017b98d9a8N05ea5ecf206a3e10N05f1cdd605c872d6N07631670e99182bfN07aafa2eba984387N085ba63e556d4b01N0a00549ab8c5b23dN0a68ceb7762409f5N0aa3b704a358f4d1N0ad0fb30b409e28bN0b61f20ed27dabeaN0b937c3f2e974aa8N0bb24b2f054ceec9N0bcad20e227150d9N0c1a44a9f6905a2bN0cc02e07128f5c73N0ced0ad43cd5ee1dN0e9054cb00effa9bN0eb8949f697559fdN0ef5156a567ed853N0f55e97435ee3e59N0f805060cb95a599N0f89d555a0c3addeN0f9188b4d139bdf0N0fc142704a2afe44N100156813d6a37baN111a6ad4bc6c784aN1122f19edab5e0d2N114078c495ce8694N11a348097e9c877aN1240bdd31d7e37f7N126c9657d9bece66N1283681c307c2cbfN141f643b6b9751d5N14b02f85d93fbdd4N14df872acb9fad67N154414f9f644714aN154d6ff4d8091bd2N155551c78b7f10fbN15a7bcfb43d2bf57N15c7cfa374346d00N165328c9e8b7698cN1667bb9f3ef31374N1680bcecde16e058N16834236ab8ea6dfN169abb2e387f922cN16ff421120f656d0N17265289882d16cbN17baf7e8a7c9db01N17eaef17ade94e4bN17effc117fc9916fN180bc1dc2a3387f7N180cb53ad2390038N18f5deacfd152639N195031f831e9e668N196fdd6f8fb2fe20N198a160c254a6e7dN19f814b7a839a479N1a712c9ef917a3f2N1ad345c8d38651a3N1ae5c33a9e8942c2N1af27136a3feb373N1bb634b34710af33N1be87c60e1e0b59eN1bea379e82f288eaN1c03dadd6999a31cN1c07fd62d04c39b7N1c1d25abbf70e511N1c2fd32e03aff3e7N1c6d6fce4424fb82N1cf74be92cb71580N1d00f6529f651e02N1d3a3f99a300c68dN1d6f06ff5715cff9N1dd5c9832a8cdf0cN1dd8c2ebe45d1f99N1dfb30082ba0f10eN1e31dd9c1248eb18N1e5a359e81e51439N1e61683e8462cbc1N1ed3e7ad21cf8bccN1f3ce88ad80b9077N1f52f5adcd00d16eN1f9449feb9174d73N1fd811e4b54a45afN20f27a0732b43952N212f567aa8cf9863N21d7ecba1387d723N21f416b8488909a2N2226499f2de57f93N22b840d24f57fd4aN22f73b331e205d89N23120ca9dc6e6348N233e630e5b368ab9N23622e106fadd1a4N23911ae6a41eb967N23cd4b40430d8aa2N24265115ea41ac4eN2439c168d2e04664N24cd03f8298e98f4N2511e681166365d4N2536431ea8fe84a2N256adbf325dfd5e6N25b48a6473d109d9N25e5187d04c3c32fN25e6044645ccf254N260cef2b1560b7b4N2668654795316d27N26cd5f4a841b27d6N26f8df70af548560N2705a067961b8c54N2733e89a618948c5N28019c7f5ab0b9d3N28814cfdd3963a46N2886077a608e9ebdN28cb4e379caead6cN28ffbbcd18a63f63N29124acc4050f04eN2a69110f29127b5fN2a822a6f285c0d54N2b7105819b32a3b3N2baf7904966c881bN2be022f9e6187c43N2d613eec3858396cN2db94987bd98d8b5N2df9ee2242bffcbcN2e333294641c39b8N2e3c9130cbf45e49N2f1da1289db4e53eN2f3ecd0e478741b5N2f52e546af26208bN2f5892ca1b0e3e32N2f641eaba942f542N2f7e2a13f0345ee0N2f8c4ace2828aa7bN2fd35152f9fdb9c1N30a19d196f585a39N30bdf3348f72efddN31038df74ac145c1N31098872357d327bN3116284dec658673N3147c2801b25163bN31ce64b6d9747ecfN31e526c6334235e6N3235587aa162bb6aN3278c8742a90ba95N32a8b7e61e7d4919N33147a8e3c03465cN331c60798be77c13N3444428bbe0efc32N346735eb65a03451N34ae8eed47c6c152N34f8b4d0fa8e304aN354537313f8f0b07N3558eeb4bfd992dbN35b29f2711a93465N363a9c80c9e44edbN36d2b448ae6a8578N370e3318ea00e235N371b313aeabf9326N3769d70e9235e384N37d672ad02b395e3N3868fa070c87f121N38be95e824e6102fN399d2758e209e47cN3a193bf8ee280e17N3a427fdeeabded5aN3a4ab1ed27f96dddN3aa53010e663b652N3b019b62b48306b1N3b347a14890732d7N3c3602e6de00f7f0N3c4a36fe5bbb5188N3cf9e4f69550b421N3dc6368b6cad6feaN3debca5ca9fb1108N3dfa1d9edc229a2aN3e29a7358b5f9939N3e5ec9add66b4881N3e8a23777577d3b6N3f01f41948ec0762N3f74c08545662e63N3f77a605bc2459ffN3fc121dd06ba1f26N3fe72cbd6dd92f11"%lxh.
Ltac2 gd_tbl_P_oid_pk_alg () : Init.string Init.list := ["Corelib.Numbers.BinNums.Z"; "stdpp.bitvector.definitions.bv"; "Corelib.Init.Datatypes.list"; "Corelib.Init.Datatypes.option"; "Corelib.Init.Logic.or"; "Corelib.Init.Logic.eq"; "OSSVerify.KrLib.P.P_oid.MBEDTLS_ERR_OID_NOT_FOUND"; "OSSVerify.KrLib.Lib.Step.rw_cells"; "OSSVerify.KrLib.P.PImg.psegs"; "Stdlib.ZArith.BinInt.Z.add"; "stdpp.bitvector.definitions.bv_unsigned"; "Corelib.Init.Datatypes.cons"; "OSSVerify.KrLib.Lib.Cells.cell"; "OSSVerify.KrLib.Lib.Cells.CB"; "OSSVerify.KrLib.Lib.Cells.C8"; "Corelib.Init.Datatypes.nil"; "OSSVerify.KrLib.Lib.Frame.stk"; "OSSVerify.KrLib.Lib.Cells.C4"; "OSSVerify.KrLib.Lib.Mem.mem_inv"; "OSSVerify.KrLib.Lib.AStep.statics_ok"; "OSSVerify.KrLib.Lib.Frame.munch"; "Corelib.Init.Datatypes.prod"; "Corelib.Init.Datatypes.pair"; "Stdlib.ZArith.BinInt.Z.sub"; "OSSVerify.KrLib.Lib.Frame.wmono"; "OSSVerify.KrLib.Lib.Exec.evt"; "OSSVerify.KrLib.P.P_oid.oid_lookup1_post"; "OSSVerify.KrLib.Lib.MState.MS"; "OSSVerify.KrLib.Lib.Frame.mkR"; "stdpp.bitvector.definitions.Z_to_bv"; "Corelib.Init.Datatypes.None"; "OSSVerify.KrLib.Lib.PropExec.seg_rom"; "Stdlib.Lists.List.In"; "Walk.offsets"; "P_OID_PK_ALG_TBL"; "OSSVerify.KrLib.Lib.HeapIface.heap_layout"; "OSSVerify.KrLib.P.P_oid.oid_lookup1_stmt"; "P_OID_GET_PK_ALG"].


Definition P_OID_GET_PK_ALG : Z := 0x24720.
Definition P_OID_PK_ALG_TBL : Z := 0x45018.
Notation OID_PK_ALG_TBLN := 120 (only parsing).
Notation OID_PK_ALG_STACK := 32 (only parsing).

Section Walk.
  Variable L : heap_layout.
  Variables (ra sp gp tp t0 t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : mem) (OID EXT P LEN lo : Z) (tg pd : word) (xs : list byte).
  Hypothesis HLEN : Z.of_nat (length xs) = LEN.
  Hypothesis D1 : EXT + 4 <= OID \/ OID + 24 <= EXT.
  Hypothesis D2 : EXT + 4 <= P \/ P + LEN <= EXT.
  Hypothesis AL1 : OID mod 8 = 0.
  Hypothesis AL2 : EXT mod 4 = 0.
  Hypothesis NZ1 : 0 < OID.
  Hypothesis NZ2 : 0 < EXT.
  Hypothesis NZ3 : 0 < P.
  Hypothesis SLO : lo <= bv_unsigned sp - 32.
  Hypothesis ACL : alloc_ceiling <= lo.
  Hypothesis ACP : 4096 < alloc_ceiling.
  Hypothesis SPA : bv_unsigned sp mod 16 = 0.
  Hypothesis DS1 : OID + 24 <= lo \/ bv_unsigned sp <= OID.
  Hypothesis DS2 : EXT + 4 <= lo \/ bv_unsigned sp <= EXT.
  Hypothesis DS3 : P + LEN <= lo \/ bv_unsigned sp <= P.
  Hypothesis CA : const_at L P_OID_PK_ALG_TBL 120.
  Hypothesis DHI : hl_data_hi L <= alloc_ceiling.
  Hypothesis OD : EXT + 4 <= hl_data_lo L \/ hl_data_hi L <= EXT.
  Hypothesis SPR : bv_unsigned sp < 2^64.
  Hypothesis EXTB : EXT + 4 <= 2^64.
  Hypothesis PB : P + LEN <= 2^64.
  Hypothesis OIDB : OID + 24 <= 2^64.

  Notation W := [(EXT, EXT + 4); (bv_unsigned sp - 32, bv_unsigned sp)].
  Notation POST := (oid_lookup1_post psegs L ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc EXT 32 lo m).
  Notation SPF := (Z_to_bv 64 (bv_unsigned sp + -32)).
  Notation FRAME mm j := (rw_cells psegs mm (bv_unsigned sp + -32) [CB 8 j; C8 s1; C8 s0; C8 ra]).
  Notation TBLC := P_OID_PK_ALG_TBL (only parsing).

  Definition offsets : list Z := [0; 40; 80].

  Lemma exit_walk : ltac2:(CDefT.buildp (gd_tbl_P_oid_pk_alg ()) "Pr,$0.Pv,(1.&40.)Pj,(2.(1.&8.))Px1,(1.&40.)Px5,(1.&40.)Px6,(1.&40.)Px7,(1.&40.)Px8,(1.&40.)Px9,(1.&40.)Px10,(1.&40.)Px11,(1.&40.)Px12,(1.&40.)Px13,(1.&40.)Px14,(1.&40.)Px15,(1.&40.)Px16,(1.&40.)Px17,(1.&40.)Px18,(1.&40.)Px19,(1.&40.)Pmm,P,(1.&40.)(3.(1.&8.))P,(4.(5.$0.R14.=)(5.$0.R14.$6.))P,(7.$8.R2.(9.(:.&40.Vsp,)-20.)(;.$<.(=.#8.R13.)(;.$<.(>.Vs1,)(;.$<.(>.Vs0,)(;.$<.(>.Vra,)(?.$<.))))))P,(10.$8.R3.Vlo,(9.(:.&40.Vsp,)-20.))P,(7.$8.R4.VEXT,(;.$<.(11.R16.)(?.$<.)))P,(12.$8.R5.)P,(13.$8.VL,R6.)P,(14.(;.(15.$0.$0.)(16.$0.$0.VEXT,(9.VEXT,+4.))(;.(15.$0.$0.)(16.$0.$0.(17.(:.&40.Vsp,)+20.)(:.&40.Vsp,))(?.(15.$0.$0.))))Vm,R7.)P,(18.$8.Vm,R8.)(19.$8.(1:.$8.VL,Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,VEXT,+20.Vlo,Vm,)(1;.(1<.R19.(1=.&40.(9.(:.&40.Vsp,)-20.))Vgp,Vtp,R18.R17.R16.(1=.&40.R1<.)R14.R13.R12.R11.R10.R?.R>.R=.R<.Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,Vt3,Vt4,Vt5,Vt6,)VF,(1=.&40.+247=4.)Vfc,(1>.(1.&40.))R9.(1?.$8.)))")
(* [comment removed for export] *).
  Proof.
    intros r v j x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 mm Hr FR ST HEXT MI SOK MU WM.
    do 6 zstep.
    release_frame FR ST (bv_unsigned sp). fin.
  Qed.

  Lemma found_walk : ltac2:(CDefT.buildp (gd_tbl_P_oid_pk_alg ()) "Pk,$0.Pv,(1.&40.)Pj,(2.(1.&8.))Px1,(1.&40.)Px5,(1.&40.)Px6,(1.&40.)Px7,(1.&40.)Px8,(1.&40.)Px9,(1.&40.)Px10,(1.&40.)Px11,(1.&40.)Px12,(1.&40.)Px13,(1.&40.)Px14,(1.&40.)Px15,(1.&40.)Px16,(1.&40.)Px17,(1.&40.)Px18,(1.&40.)Px19,(1.&40.)Pmm,P,(1.&40.)(3.(1.&8.))P,(20.$0.R14.$21.)P,(7.$8.R2.(9.(:.&40.Vsp,)-20.)(;.$<.(=.#8.R13.)(;.$<.(>.Vs1,)(;.$<.(>.Vs0,)(;.$<.(>.Vra,)(?.$<.))))))P,(10.$8.R3.Vlo,(9.(:.&40.Vsp,)-20.))P,(7.$8.R4.VEXT,(;.$<.(11.R16.)(?.$<.)))P,(12.$8.R5.)P,(13.$8.VL,R6.)P,(14.(;.(15.$0.$0.)(16.$0.$0.VEXT,(9.VEXT,+4.))(;.(15.$0.$0.)(16.$0.$0.(17.(:.&40.Vsp,)+20.)(:.&40.Vsp,))(?.(15.$0.$0.))))Vm,R7.)P,(18.$8.Vm,R8.)(19.$8.(1:.$8.VL,Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,VEXT,+20.Vlo,Vm,)(1;.(1<.R19.(1=.&40.(9.(:.&40.Vsp,)-20.))Vgp,Vtp,R18.R17.R16.R15.(1=.&40.VEXT,)(1=.&40.(9.$22.R1<.))R12.R11.R10.R?.R>.R=.R<.Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,Vt3,Vt4,Vt5,Vt6,)VF,(1=.&40.+247<8.)Vfc,(1>.(1.&40.))R9.(1?.$8.)))")
(* [comment removed for export] *).
  Proof.
    intros k v j x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 mm Hk FR ST HEXT MI SOK MU WM.
    unfold P_OID_PK_ALG_TBL in *.
    destruct Hk as [<-|[<-|[<-|[]]]]; cbn [Z.add].
    all: lazymatch goal with |- evt _ _ (MS (mkR _ _ _ _ _ _ _ _ _ (Z_to_bv 64 ?e) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _ _ _ _ _ _) =>
           let a := eval vm_compute in (e + 32) in
           let bs := eval vm_compute in (match image_bytes psegs a 4 with Some bs => bs | None => [] end) in
           pose proof (statics_ok_cells psegs L mm a bs SOK ltac:(eapply const_at_sub; [exact CA| cbn; lia| cbn; lia]) ltac:(vm_compute; reflexivity)) as TB;
           cbn [length] in TB
         end.
    all: zstep; zstep; clear TB; zstep; eapply exit_walk; try eassumption; left; reflexivity.
  Qed.

End Walk.

Ltac found kk :=
  let a := eval vm_compute in (0x45018 + kk) in
  replace (Z_to_bv 64 a) with (Z_to_bv 64 (P_OID_PK_ALG_TBL + kk)) by reflexivity;
  eapply found_walk with (k := kk); try eassumption; try solve_in; try plia.
Ltac notfound := eapply exit_walk; try eassumption; right; reflexivity.

Ltac flia := first [clear_disj; lia | lia].
(* [comment removed for export] *)
Ltac ro_const' A0 n0 RO :=
  lazymatch goal with |- context [MS _ _ _ _ _ ?mx (seg_rom ?sg)] =>
    let cbs := eval vm_compute in (match image_bytes sg A0 n0 with Some cbs => cbs | None => [] end) in
    match goal with MI : mem_inv sg mx |- _ =>
      pose proof (ro_image_bytes_at sg mx A0 cbs MI ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(cbn; lia)) as RO;
      let nz := eval vm_compute in (Z.of_nat n0) in let ROL := fresh "ROL" in assert (ROL : Z.of_nat (length cbs) = nz) by reflexivity end
  end.

Lemma P_oid_get_pk_alg_spec : ltac2:(CDefT.buildp (gd_tbl_P_oid_pk_alg ()) "PL,$23.(24.$8.R1.$25.$22.+78.+20.)")
(* [comment removed for export] *).
Proof.
  intros L. unfold oid_lookup1_stmt, P_OID_GET_PK_ALG.
  intros until xs. intros HOID HXS HLEN HEXT D1 D2 AL1 AL2 NZ1 NZ2 NZ3 ST SLO ACL SPA DS1 DS2 DS3 MI SOK CA DHI OD -> ->.
  pose proof alloc_ceiling_pos as ACP.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
  pose proof (rw_cells_bound _ _ _ _ HEXT) as EXTB. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in EXTB.
  change (Z.of_nat 4) with 4 in EXTB.
  pose proof (rw_cells_bound _ _ _ _ HOID) as OIDB. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ buf_cells] in OIDB.
  change (Z.of_nat 24) with 24 in OIDB.
  pose proof (bytes_at_bound _ _ _ _ HXS) as PB. rewrite HLEN in PB.
  unfold buf_cells in HOID.
  assert (LEN0 : 0 <= LEN) by lia.
  carve_frame 32%nat ST.
  (* [comment removed for export] *)
  assert (LXSUMS : forall AL, Forall (summary_ok psegs AL) [SUM_bcmpCP 0x43248])
    by (intros AL; repeat constructor; apply sum_bcmpCP_ok; exact P_bcmp_spec).
  lx_run_tac (PLANS [0x24730] [] 40%N (@nil summary)); lx_tree.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.
  lazymatch goal with Hi : mem_inv _ m1 |- _ => rename Hi into MI1 end. clear MI.
  ro_const' 0x10388 9%nat RO1. ro_const' 0x10487 7%nat RO2. ro_const' 0x10619 5%nat RO3.
  lx_run_tac (PLANS [0x247d4; 0x247c8] [] 250%N [SUM_bcmpCP 0x43248]); lx_tree.
  (* [comment removed for export] *)
  all: lazymatch goal with |- evt _ _ (MS _ _ (Z_to_bv 64 ?pc) _ _ ?mx _) =>
       lazymatch goal with Hm : munch ?W1 ?mq mx |- _ =>
         let MUW := fresh "MUW" in
         assert (MUW : munch [(EXT, EXT + 4); (bv_unsigned sp - 32, bv_unsigned sp)] m mx)
           by (eapply munch_weaken; [| exact Hm]; intros xw Hxw; clear -Hxw; cbn in Hxw |- *; lia);
         pose proof (statics_ok_munch psegs L _ _ _ SOK MUW ltac:(intros a Ha NW; clear -Ha ACL SLO DHI OD; cbn; lia)) as SOKx
       end end.
  all: first [ lazymatch goal with |- evt _ _ (MS _ _ (Z_to_bv 64 0x247d4) _ _ _ _) => notfound end
             | lazymatch goal with |- evt _ _ (MS (mkR _ _ _ _ _ _ _ _ _ (Z_to_bv 64 ?az) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _ _ _ _ _ _) =>
                 let kk := eval vm_compute in (az - 0x45018) in found kk end ].
Qed.
