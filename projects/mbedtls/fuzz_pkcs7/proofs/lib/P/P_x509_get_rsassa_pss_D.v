(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Walk AStep CellsX Image Asn1Aux X509Aux X509AuxB.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Spec Require Import Rep.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.P Require Import PImg P_string P_asn1_get_tag P_asn1_get_int P_oid P_oid_md_alg P_asn1_get_mpi
     P_platform_zeroize P_asn1_get_alg_A P_asn1_get_alg P_asn1_get_alg_null P_x509_get_hash_alg P_x509_get_rsassa_pss_A P_x509_get_rsassa_pss_B P_x509_get_rsassa_pss_C.
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
Local Ltac lia_nodisj ::= orc_dlia. (* [comment removed for export] *)
Local Ltac clear_disj ::= fc_clear_disj. (* [comment removed for export] *)
Local Ltac prune_disj ::= fc_prune_disj. (* [comment removed for export] *)
Ltac2 gd_tbl_P_x509_get_rsassa_pss_D () : Init.string Init.list := ["Corelib.Numbers.BinNums.Z"; "Corelib.Init.Datatypes.list"; "stdpp.bitvector.definitions.bv"; "Corelib.Init.Datatypes.option"; "OSSVerify.KrLib.Lib.Step.rw_cells"; "OSSVerify.KrLib.P.PImg.psegs"; "Stdlib.ZArith.BinInt.Z.add"; "stdpp.bitvector.definitions.bv_unsigned"; "Corelib.Init.Datatypes.cons"; "OSSVerify.KrLib.Lib.Cells.cell"; "OSSVerify.KrLib.Lib.Cells.CB"; "OSSVerify.KrLib.Lib.Cells.C4"; "Corelib.Init.Datatypes.nil"; "OSSVerify.KrLib.Lib.Cells.C8"; "stdpp.bitvector.definitions.Z_to_bv"; "OSSVerify.KrLib.Lib.Mem.bytes_at"; "OSSVerify.KrLib.Lib.Frame.stk"; "OSSVerify.KrLib.Lib.Frame.munch"; "Corelib.Init.Datatypes.prod"; "Corelib.Init.Datatypes.pair"; "Stdlib.ZArith.BinInt.Z.sub"; "OSSVerify.KrLib.Lib.Frame.wmono"; "OSSVerify.KrLib.Lib.Mem.mem_inv"; "OSSVerify.KrLib.Lib.AStep.statics_ok"; "Stdlib.ZArith.BinInt.Z.le"; "OSSVerify.KrLib.Lib.Exec.evt"; "OSSVerify.KrLib.P.P_x509_get_rsassa_pss_A.x509_get_rsassa_pss_params_post"; "OSSVerify.KrLib.Lib.MState.MS"; "OSSVerify.KrLib.Lib.Frame.mkR"; "Corelib.Init.Datatypes.None"; "OSSVerify.KrLib.Lib.PropExec.seg_rom"].


Section Walk.
  Variable L : heap_layout.
  Variables (MSF MDTBL : Z).
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem)
            (PAR MD MGF SALT BUF pp lo : Z) (bs : list byte) (plen : word).

  Notation CTX := (rsassa_ctx psegs L MSF MDTBL P_ASN1_GET_ALG_NULL P_ASN1_GET_ALG P_OID_GET_MD_ALG P_X509_GET_HASH_ALG sp PAR MD MGF SALT BUF pp lo bs plen).
  Notation W := [(MD, MD + 4); (MGF, MGF + 4); (SALT, SALT + 4); (bv_unsigned sp - 240, bv_unsigned sp)].
  Notation POST := (x509_get_rsassa_pss_params_post psegs L ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc MD MGF SALT lo m).
  Notation SPF := (Z_to_bv 64 (bv_unsigned sp + -128)).
  Notation ENDv := (pp + bv_unsigned plen).
  Hypothesis HC : CTX.

  Let exit_walk' := exit_walk L MSF MDTBL ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m PAR MD MGF SALT BUF pp lo bs plen HC.
  Let s3_walk' := s3_walk L MSF MDTBL ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m PAR MD MGF SALT BUF pp lo bs plen HC.
  Let s2b_walk' := s2b_walk L MSF MDTBL ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m PAR MD MGF SALT BUF pp lo bs plen HC.

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "02C0@D11375003030.181D12218223161.155D12428150072.181D1343986644.181 D15037909945.181D16496876345.155D16496876345.181D16974982078.155D16974982078.181D17565844854.155D19418348606.181D20153598198.181D20264044729.155D20264044729.181D20994638648.155D2265817462.181 D2274929014.155 D24323521813.182D26291562981.181D26722167889.181D30210897849.155D30228025918.155D31162734262.181D36191331830.155D36191331830.181D36583815225.181D3827506166.155 D3827506166.181 D3863394750.181 D39823997752.181D40110156729.181D40129553998.181D40433219958.181D40741479608.181D43888467129.181D44022766142.181D44484923210.181D45347449913.181D46010008310.181D46029161400.155D46029161400.181D48356160441.155D51791381457.181D52101704109.158D52101704109.183D53786012350.181D55677588537.155D61623523385.181D6255928132.181 D62814340926.155D62814340926.181D63042527678.155D65179897657.181D66418546897.181D67071090489.155D67562352718.181D9195366073.155 D9730913345.157 L11275736598.156L11375003030.165L11518786483.137L12428150072.165L1343986644.165 L14946396720.165L16974982078.139L16974982078.165L17565844854.139L19418348606.165L20153598198.165L20660446724.4  L2265817462.165 L2274929014.139 L26291562981.165L29008372736.165L29008469930.139L29010574176.138L30228025918.139L31162734262.165L31165788229.116L31914898123.2  L34603895532.0  L36191331830.139L36191331830.165L3827506166.139 L3827506166.165 L3863394750.165 L39360104073.116L40129553998.165L40433219958.165L40828781442.3  L43090580551.2  L44022766142.165L44484923210.165L46010008310.165L52065245876.165L53786012350.165L59308659786.3  L60010937425.2  L6255928132.165 L62814340926.139L62814340926.165L63042527678.139L66151402056.3  L66986308662.0  L67158371251.137L67158371251.140L67562352718.165L8278980118.184 L8932515595.170 R12596958032.154R17698465547.156R17698853562.154R18042445946.184R19077775108.134R19079872285.154R22792027211.184R2383289167.154 R24235034530.154R27053815482.154R29946627972.134R30643776720.154R31542961003.154R33753208378.154R33879773476.154R34164561850.154R34848507725.154R35101928994.154R35516336640.154R3611875490.154 R36671363408.154R36673460553.134R40357422493.154R42695276489.134R43592025415.184R46366855808.154R51206884381.154R51273849101.154R51892457379.134R54652266240.154R54995020636.156R56114490102.184R62003914580.134R63054757965.154R6443869645.154 R6445966804.134 R66030093071.154R8532465613.154 00000100H00I00J00a01801O01P01Q01R01S01T01k02B02\02]02^03L03M03d04;04<04=04>04?04V04W04X04Y05305J05K05L05f06=06>06?06V06W07107K07b0890990:90::0:Q0:h0:i0:j0:k0:l0;C0;Z0<10<20<I0=O0=f0>[0?20?30?40?50?j0@_0AX0BM0CF0CR0DG0E<0E=0E>0E?0E@0F50Fj0H70H=0H>0I70J00Je0KZ0LO0MW0NL0OE0OO0OU0PJ0PK0Q@0QA0R60R@0RA0RB0S70Sl0Ta0Tj0Tk0UB0U[0VT0Vk0Vl0Wh0Xm0Yg0ZJ0\60^50^]0_<0`80`O0b;0c70d<0dS0e10eH0fH0gD0g^0hZ0iV0jR0lQ0mM0nQ0nk10j11L11c12=12f15A16A17A18A19A1:=1;=FS2sp3PAR2MD3MGF4SALT2bsFFS2sp3PAR2MD3MGF4SALT2bsS2sp3PAR2MD3MGF4SALT2bsS2sp3PAR2MD3MGF4SALT2bsFFFFFS2sp3PAR2MD3MGF4SALT2bsS2sp3PAR2MD3MGF4SALT2bsS2sp3PAR2MD3MGF4SALT2lo2bsFFS2sp3PAR2MD3MGF4SALT2pp2bs4plen1p3Hp12KE3x571HFS2sp3PAR2MD3MGF4SALT2bsS2sp3PAR2MD3MGF4SALT2bsFFFFS2sp3PAR2MD3MGF4SALT2bsFFFS2sp3PAR2MD3MGF4SALT2lo2bsS2sp3PAR2MD3MGF4SALT2bsFFS2sp3PAR2MD3MGF4SALT2lo2bsS2sp3PAR2MD3MGF4SALT2bsFFS2sp3PAR2MD3MGF4SALT2bsFS2sp3PAR2MD3MGF4SALT2lo2bsS2sp3PAR2MD3MGF4SALT2lo2bsS2sp3PAR2MD3MGF4SALT2bsS2sp3PAR2MD3MGF4SALT2bsS1L2sp3PAR2MD3MGF4SALT2lo2bs3NZP3NZ13NZ23NZ33SLO3ACL3DHI3SPR1a1HS1L2sp3PAR2MD3MGF4SALT2lo2bs3NZP3NZ13NZ23NZ33SLO3ACL3DHI3SPR1a1HFS2sp3PAR2MD3MGF4SALT2bsS2sp3PAR2MD3MGF4SALT2bsFFFFS2sp3PAR2MD3MGF4SALT2bsS2sp3PAR2MD3MGF4SALT2bsS2sp3PAR2MD3MGF4SALT2bsFS2sp3PAR2MD3MGF4SALT2bsS2sp3PAR2MD3MGF4SALT2pp2bs4plen1p3x323Hp12KE2x33x333x343x354POST3x361HS2sp3PAR2MD3MGF4SALT2bsS2sp3PAR2MD3MGF4SALT2lo2bs3NZP3NZ13NZ23NZ33SLO2HD3SPRS2sp3PAR2MD3MGF4SALT2bsFFFS2sp3PAR2MD3MGF4SALT2lo2bs3NZP3NZ13NZ23NZ33SLO2HD3SPRS2sp3PAR2MD3MGF4SALT2lo2bs3NZP3NZ13NZ23NZ33SLO2HD3SPRS2sp3PAR2MD3MGF4SALT3BUF2lo2bs3NZP3NZ13NZ23NZ33SLO2HD3SPRS2sp3PAR2MD3MGF4SALT2lo2bs3NZP3NZ13NZ23NZ33SLO2HD3SPRS2sp3PAR2MD3MGF4SALT3BUF2lo2bs3NZP3NZ13NZ23NZ33SLO2HD3SPRS1r2Hr2r'2R3S2sp3PAR2MD3MGF4SALT2lo2bs3NZP3NZ13NZ23NZ33SLO2HD3SPRS2sp3PAR2MD3MGF4SALT2lo2bs3NZP3NZ13NZ23NZ33SLO2HD3SPRFFFFS2sp3PAR2MD3MGF4SALT2lo2bs3NZP3NZ13NZ23NZ33SLO2HD3SPRS2sp3PAR2MD3MGF4SALT2lo2bs3NZP3NZ13NZ23NZ33SLO2HD3SPRS2sp3PAR2MD3MGF4SALT3BUF2pp2bs4plen1p3Hp03Hp14HPP22B43NZP3NZ13NZ23NZ33NZB3SPRS1r2HrSS2sp3PAR2MD3MGF4SALT3BUF2lo2bs3NZP3NZ13NZ23NZ33SLO2HD3SPRS2sp3PAR2MD3MGF4SALT3BUF2lo2bs3NZP3NZ13NZ23NZ33SLO2HD3SPRS2sp3PAR2MD3MGF4SALT2lo2bs3NZP3NZ13NZ23NZ33SLO2HD3SPRS2sp3PAR2MD3MGF4SALT2lo2bs3NZP3NZ13NZ23NZ33SLO2HD3SPRS2sp3PAR2MD3MGF4SALT2lo2bs3NZP3NZ13NZ23NZ33SLO2HD3SPRS2sp3PAR2MD3MGF4SALT3BUF2pp2bs4plen4HPP24HPP12B43NZP3NZ13NZ23NZ33SPR3PLRS2sp3PAR2MD3MGF4SALT2lo2bs3NZP3NZ13NZ23NZ33SLO2HD3SPRS2sp3PAR2MD3MGF4SALT3BUF2lo2bs3NZP3NZ13NZ23NZ33SLO2HD3SPRS2r'2R12KSS1r2HrS2sp3PAR2MD3MGF4SALT2lo2bs3NZP3NZ13NZ23NZ33SLO2HD3SPRFS2sp3PAR2MD3MGF4SALT2lo2bs3NZP3NZ13NZ23NZ33SLO2HD3SPRFS2sp3PAR2MD3MGF4SALT2lo2bs3NZP3NZ13NZ23NZ33SLO2HD3SPRS2r'2KS2E'SFS2sp3PAR2MD3MGF4SALT2lo2bs3NZP3NZ13NZ23NZ33SLO2HD3SPRS2sp3PAR2MD3MGF4SALT2lo2bs3NZP3NZ13NZ23NZ33SLO2HD3SPRS2sp3PAR2MD3MGF4SALT2lo2bs3NZP3NZ13NZ23NZ33SLO2HD3SPRS1r2Hr2KrSS2sp3PAR2MD3MGF4SALT2bsS2sp3PAR2MD3MGF4SALT2bs1rS2sp3PAR2MD3MGF4SALT3BUF2lo2bs3NZP3NZ13NZ23NZ33SLO2HD3SPRS2sp3PAR2MD3MGF4SALT2bsFS1L2sp3PAR2MD3MGF4SALT2lo2bs3NZP3NZ13NZ23NZ33SLO3ACL3ACP3SPRS2sp3PAR2MD3MGF4SALT3BUF2pp2bs4plen1p3Hp03NZP3NZ13NZ23NZ33SPR1r1q3PC3S2sp3PAR2MD3MGF4SALT3BUF2bs1p3Hp03NZP3NZ13NZ23NZ33SPR1q2HqS2sp3PAR2MD3MGF4SALT2bs1q2Lw2q23PC7S2sp3PAR2MD3MGF4SALT3BUF2pp2lo2bs4plen1p3Hp03Hp14HPP23D1B3D2B3D3B3NZP3NZ13NZ23NZ33SLO3DS13DS23DS33DSB3SPR2KES2sp3PAR2MD3MGF4SALT3BUF2pp2lo2bs4plen1p3Hp03Hp14HPP23D1B3D2B3D3B3NZP3NZ13NZ23NZ33SLO3DS13DS23DS33DSB3SPR2KE1q2Lw3PC32Hq3HqL2LRS2sp3PAR2MD3MGF4SALT2pp2bs4plen1q2Lw3HqLS2sp3PAR2MD3MGF4SALT2bs1q2Lw2LRS1L2sp3PAR2MD3MGF4SALT2lo2bs3NZP3NZ13NZ23NZ33SLO3ACL3DHI3SPRS2sp3PAR2MD3MGF4SALT2bsS2sp3PAR2MD3MGF4SALT3BUF2pp2lo2bs4plen1p3Hp03Hp14HPP23D1B3D2B3D3B3NZP3NZ13NZ23NZ33SLO3DS13DS23DS33DSB3SPR2KES1L2sp3PAR2MD3MGF4SALT2lo2bs3NZP3NZ13NZ23NZ33SLO3ACL3ACP3SPRS2sp3PAR2MD3MGF4SALT3BUF2pp2bs4plen4HPP23NZP3NZ13NZ23NZ33SPR1q2Lw3HqLS2sp3PAR2MD3MGF4SALT2bsS2sp3PAR2MD3MGF4SALT2lo2bs3SLOS2sp3PAR2MD3MGF4SALT2bsS1L2sp3PAR2MD3MGF4SALT2lo2bs3NZP3NZ13NZ23NZ33SLO3ACL3ACP3SPA3SPRS1L2sp3PAR2MD3MGF4SALT2lo2bs3NZP3NZ13NZ23NZ33SLO3ACL3DHI3SPRS2sp3PAR2MD3MGF4SALT2lo2bsS1L2sp3PAR2MD3MGF4SALT2lo2bs3NZP3NZ13NZ23NZ33SLO3ACL3DHI3SPRS1L2sp3PAR2MD3MGF4SALT2lo2bs3NZP3NZ13NZ23NZ33SLO3ACL3ACP3SPRS1L2sp3PAR2MD3MGF4SALT2lo2bs3NZP3NZ13NZ23NZ33SLO3ACL3ACP3SPRS2sp3PAR2MD3MGF4SALT3BUF2pp2lo2bs4plen1p3Hp03Hp14HPP23D1B3D2B3D3B3NZP3NZ13NZ23NZ33SLO3DS13DS23DS33DSB3SPR2KE1q2Lw3PC32Hq3HqL2LRS1L2sp3PAR2MD3MGF4SALT2lo2bs3NZP3NZ13NZ23NZ33SLO3ACL3ACP3SPRS2sp3PAR2MD3MGF4SALT3BUF2bs1p3Hp03NZP3NZ13NZ23NZ33SPR1q2Lw2Hq2q23PC7S2sp3PAR2MD3MGF4SALT2lo2bsS2sp3PAR2MD3MGF4SALT3BUF2pp2lo2bs4plen1p3Hp03Hp14HPP23D1B3D2B3D3B3NZP3NZ13NZ23NZ33SLO3DS13DS23DS33DSB3SPR2KE1q2Lw3PC32Hq3HqL2LRS2sp3PAR2MD3MGF4SALT3BUF2lo2bs3DSBS2sp3PAR2MD3MGF4SALT2bsS2sp3PAR2MD3MGF4SALT2lo2bsS2sp3PAR2MD3MGF4SALT2pp2bs4plen1p1r1q3PC3S1L2sp3PAR2MD3MGF4SALT3BUF2pp2lo2bs4plen1p3Hp03Hp13NZP3NZ13NZ23NZ33NZB3SLO3ACL3ACP3SPR3MDB4MGFB5SALTB2KE1q2Lw2Hq2q23ALw3x533QLw2ap2qp3PC74HAP14HAP23HQP3ALRS1L2sp3PAR2MD3MGF4SALT2lo2bs3NZP3NZ13NZ23NZ33SLO3ACL3ACP3SPA3SPRS1L2sp3PAR2MD3MGF4SALT2lo2bs3NZP3NZ13NZ23NZ33SLO3ACL3ACP3SPA3SPRS1L2sp3PAR2MD3MGF4SALT2lo2bs3NZP3NZ13NZ23NZ33SLO3ACL3ACP3SPA3SPRS1L2sp3PAR2MD3MGF4SALT2lo2bs3NZP3NZ13NZ23NZ33SLO3ACL3ACP3SPA3SPRS1L2sp3PAR2MD3MGF4SALT2lo2bs3NZP3NZ13NZ23NZ33SLO3ACL3ACP3SPRS1L2sp3PAR2MD3MGF4SALT2lo2bs3NZP3NZ13NZ23NZ33SLO3ACL3ACP3SPA3SPR". (* [comment removed for export] *)
  #[using="MSF MDTBL PAR HC exit_walk' s3_walk' s2b_walk'"] Lemma s2_walk : ltac2:(CDefT.buildp (gd_tbl_P_x509_get_rsassa_pss_D ()) "Pp,$0.Pj4,(1.(2.&8.))Ptfw,(2.&40.)Plw,(2.&40.)Pqtag,(2.&40.)Pqpad,(2.&40.)Pqlen,(2.&40.)Pqpw,(2.&40.)Patag,(2.&40.)Papad,(2.&40.)Palen,(2.&40.)Papw,(2.&40.)Pw1,(2.&40.)Pw2,(2.&40.)Pw3,(2.&40.)Px1,(2.&40.)Px5,(2.&40.)Px6,(2.&40.)Px7,(2.&40.)Px10,(2.&40.)Px11,(2.&40.)Px12,(2.&40.)Px13,(2.&40.)Px14,(2.&40.)Px15,(2.&40.)Px16,(2.&40.)Px17,(2.&40.)Px19,(2.&40.)Px21,(2.&40.)Px28,(2.&40.)Px29,(2.&40.)Px30,(2.&40.)Px31,(2.&40.)Pmm,P,(2.&40.)(3.(2.&8.))P,(4.$5.R1.(6.(7.&40.Vsp,)-80.)(8.$9.(:.#4.R21.)(8.$9.(;.R20.)(<.$9.))))P,(4.$5.R2.(6.(7.&40.Vsp,)-78.)(8.$9.(;.R1?.)(8.$9.(;.R1>.)(8.$9.(=.R1=.)(8.$9.(=.R1<.)(<.$9.))))))P,(4.$5.R3.(6.(7.&40.Vsp,)-60.)(8.$9.(;.R1<.)(8.$9.(;.R1;.)(8.$9.(=.R1:.)(8.$9.(=.R19.)(<.$9.))))))P,(4.$5.R4.(6.(7.&40.Vsp,)-48.)(8.$9.(=.R22.)(<.$9.)))P,(4.$5.R5.(6.(7.&40.Vsp,)-40.)(8.$9.(=.(>.&40.R26.))(<.$9.)))P,(4.$5.R6.(6.(7.&40.Vsp,)-38.)(8.$9.(=.Vs5,)(8.$9.(=.Vs4,)(8.$9.(=.Vs3,)(8.$9.(=.Vs2,)(8.$9.(=.Vs1,)(8.$9.(=.Vs0,)(8.$9.(=.Vra,)(<.$9.)))))))))P,(4.$5.R7.VMD,(8.$9.(;.R1<.)(<.$9.)))P,(4.$5.R8.VMGF,(8.$9.(;.R1<.)(<.$9.)))P,(4.$5.R9.VSALT,(8.$9.(;.R1<.)(<.$9.)))P,(?.$5.R:.VBUF,Vbs,)P,(10.$5.R;.Vlo,(6.(7.&40.Vsp,)-80.))P,(11.(8.(12.$0.$0.)(13.$0.$0.VMD,(6.VMD,+4.))(8.(12.$0.$0.)(13.$0.$0.VMGF,(6.VMGF,+4.))(8.(12.$0.$0.)(13.$0.$0.VSALT,(6.VSALT,+4.))(8.(12.$0.$0.)(13.$0.$0.(14.(7.&40.Vsp,)+?0.)(7.&40.Vsp,))(<.(12.$0.$0.))))))Vm,R<.)P,(15.$5.Vm,R=.)P,(16.$5.R>.)P,(17.$5.VL,R?.)P,(18.VBUF,R31.)P,(18.R32.(6.Vpp,(7.&40.Vplen,)))(19.$5.(1:.$5.VL,Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,VMD,VMGF,VSALT,Vlo,Vm,)(1;.(1<.R24.(>.&40.(6.(7.&40.Vsp,)-80.))Vgp,Vtp,R23.R22.R21.(>.&40.(6.Vpp,(7.&40.Vplen,)))(>.&40.VSALT,)R20.R1?.R1>.R1=.R1<.R1;.R1:.R19.(>.&40.VMGF,)R18.(>.&40.R33.)R17.Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,R16.R15.R14.R13.)VF,(>.&40.+25>:8.)Vfc,(1=.(2.&40.))R12.(1>.$5.)))")
(* [comment removed for export] *).
  Proof.
    intros p j4 tfw lw qtag qpad qlen qpw atag apad alen apw w1 w2 w3 x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x19 x21 x28 x29 x30 x31 mm
      F0 FPAR FALG FL FP FS HMD HMGF HSALT HBUF ST MU WM MI SOK Hp0 Hp1.
    open_ctx HC.
    pose proof (bv_unsigned_in_range 64 plen) as PLR. unfold bv_modulus in PLR. cbn in PLR.
    zstep. if_cases KE; zify_cond KE.
    { (* [comment removed for export] *) zstep. zstep. eapply exit_walk'; try eassumption; clear; lia. }
    zstep. zstep. zstep. zstep. zstep.
    pose proof P_asn1_get_tag_spec as SP. unfold asn1_get_tag_stmt, P_ASN1_GET_TAG in SP.
    callx_sp (bv_unsigned sp + -128)
      (eapply SP with (PP := bv_unsigned sp + -64) (LENP := bv_unsigned sp + -72) (P := p) (END := ENDv) (BUF := BUF) (bs := bs);
       rewrite ?(unsigned_lit (bv_unsigned sp + -128)) by plia; try eassumption; try reflexivity; try plia).
    clear SP.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m4 end.
    match goal with H : rw_cells _ m4 (bv_unsigned sp + -72) [C8 ?lw] |- _ => rename H into FL; rename lw into Lw end.
    match goal with H : rw_cells _ m4 (bv_unsigned sp + -64) [C8 (Z_to_bv 64 ?qq)] |- _ => rename H into FP; rename qq into q end.
    match goal with H : ?x = Z_to_bv 64 ?rr |- _ => subst x; rename rr into r end.
    match goal with H : r = 0 -> _ |- _ => rename H into HL0 end.
    match goal with H : _ < r <= 0 |- _ => rename H into Hr end.
    match goal with H : stk _ m4 lo _ |- _ => rename H into ST4 end.
    pose proof (bv_unsigned_in_range 64 Lw) as LR. unfold bv_modulus in LR. cbn in LR.
    zstep. if_cases Kr; zify_cond Kr.
    2:{ (* [comment removed for export] *)
      zstep. zstep. if_cases K98; zify_cond K98.
      { zstep. zstep. zstep. rewrite (swrap32_errsum r) by (clear -Hr; lia).
        eapply exit_walk'; try eassumption; clear -Hr; lia. }
      zstep. eapply s3_walk'; try eassumption; plia. }
    (* [comment removed for export] *)
    rewrite ?unsigned_lit in Kr by plia.
    assert (R0 : r = 0) by (clear -Kr Hr; lia). subst r. specialize (HL0 eq_refl). destruct HL0 as [Hq HqL]. clear Kr Hr.
    zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep.
    pose proof HALGS as SPG. unfold asn1_get_alg_stmt, P_ASN1_GET_ALG in SPG.
    callx_sp (bv_unsigned sp + -128)
      (eapply SPG with (PP := bv_unsigned sp + -64) (ALG := bv_unsigned sp + -96) (PAR := bv_unsigned sp + -120) (P := q) (END := q + bv_unsigned Lw) (BUF := BUF) (bs := bs) (lo := lo);
       rewrite ?(unsigned_lit (bv_unsigned sp + -128)) by plia; try eassumption; try reflexivity; try plia).
    clear SPG.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m5 end.
    match goal with H : rw_cells _ m5 (bv_unsigned sp + -96) [C4 ?a1_; C4 ?a2_; C8 ?a3_; C8 ?a4_] |- _ =>
      rename H into FALG; rename a3_ into ALw; rename a4_ into APw end.
    match goal with H : rw_cells _ m5 (bv_unsigned sp + -120) [C4 ?a1_; C4 ?a2_; C8 ?a3_; C8 ?a4_] |- _ =>
      rename H into FPAR; rename a3_ into QLw; rename a4_ into QPw end.
    match goal with H : rw_cells _ m5 (bv_unsigned sp + -64) [C8 (Z_to_bv 64 ?qq)] |- _ => rename H into FP; rename qq into q2 end.
    match goal with H : ?x = Z_to_bv 64 ?rr |- _ => subst x; rename rr into r end.
    match goal with H : r = 0 -> _ |- _ => rename H into HA0 end.
    match goal with H : _ < r <= 0 |- _ => rename H into Hr end.
    match goal with H : stk _ m5 lo _ |- _ => rename H into ST5 end.
    pose proof (bv_unsigned_in_range 64 ALw) as ALR. unfold bv_modulus in ALR. cbn in ALR.
    zstep. zstep. zstep. zstep. zstep. zstep.
    ddestruct (x509_err_select r 18446744073709542656 ltac:(clear -Hr; lia) ltac:(clear; lia)) as (r' & ER & R1 & R2 & R3). rewrite ER. clear ER.
    zstep. if_cases KS; zify_cond KS.
    { (* [comment removed for export] *)
      assert (NE : r <> 0) by (intros E; pose proof (proj2 R2 E) as E'; clear -E' KS; rewrite ?unsigned_lit in KS by lia; lia).
      specialize (R3 NE). eapply exit_walk'; try eassumption; clear -R3 Hr; lia. }
    rewrite ?unsigned_lit in KS by (clear -R1; lia).
    assert (R0 : r = 0) by (apply (proj1 R2); clear -KS R1; lia). subst r. clear KS R1 R2 R3.
    specialize (HA0 eq_refl). ddestruct HA0 as (ap & qp & -> & -> & HAP1 & HAP2 & HQP).
    eapply s2b_walk'; try eassumption; try plia.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
End Walk.
