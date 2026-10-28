(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Walk AStep CellsX Image Asn1Aux X509Aux X509AuxB.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Spec Require Import Rep.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U Require Import UImg U_string U_asn1_get_tag U_asn1_get_int U_oid U_oid_md_alg U_asn1_get_mpi U_platform_zeroize U_asn1_get_alg_A U_asn1_get_alg U_asn1_get_alg_null U_x509_get_hash_alg U_x509_get_rsassa_pss_A U_x509_get_rsassa_pss_B U_x509_get_rsassa_pss_C U_x509_get_rsassa_pss_D.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LXP Require Import LxPTac.
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
Ltac2 gd_tbl_P_x509_get_rsassa_pss_E () : Init.string Init.list := ["Corelib.Numbers.BinNums.Z"; "stdpp.bitvector.definitions.bv"; "Corelib.Init.Datatypes.list"; "Corelib.Init.Datatypes.option"; "RocqVerifyHarness.AgentSubmission.Lib.Step.rw_cells"; "RocqVerifyHarness.AgentSubmission.U.UImg.usegs"; "Stdlib.ZArith.BinInt.Z.add"; "stdpp.bitvector.definitions.bv_unsigned"; "Corelib.Init.Datatypes.cons"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.cell"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.CB"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C4"; "Corelib.Init.Datatypes.nil"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C8"; "stdpp.bitvector.definitions.Z_to_bv"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.bytes_at"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.stk"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.munch"; "Corelib.Init.Datatypes.prod"; "Corelib.Init.Datatypes.pair"; "Stdlib.ZArith.BinInt.Z.sub"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.wmono"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.mem_inv"; "RocqVerifyHarness.AgentSubmission.Lib.AStep.statics_ok"; "Stdlib.ZArith.BinInt.Z.le"; "RocqVerifyHarness.AgentSubmission.Lib.Exec.evt"; "RocqVerifyHarness.AgentSubmission.U.U_x509_get_rsassa_pss_A.x509_get_rsassa_pss_params_post"; "RocqVerifyHarness.AgentSubmission.Lib.MState.MS"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.mkR"; "Corelib.Init.Datatypes.None"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.seg_rom"].


Section Walk.
  Variable L : heap_layout.
  Variables (MSF MDTBL : Z).
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem)
            (PAR MD MGF SALT BUF pp lo : Z) (bs : list byte) (plen : word).

  Notation CTX := (rsassa_ctx usegs L MSF MDTBL U_ASN1_GET_ALG_NULL U_ASN1_GET_ALG U_OID_GET_MD_ALG U_X509_GET_HASH_ALG sp PAR MD MGF SALT BUF pp lo bs plen).
  Notation W := [(MD, MD + 4); (MGF, MGF + 4); (SALT, SALT + 4); (bv_unsigned sp - 240, bv_unsigned sp)].
  Notation POST := (x509_get_rsassa_pss_params_post usegs L ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc MD MGF SALT lo m).
  Notation SPF := (Z_to_bv 64 (bv_unsigned sp + -128)).
  Notation ENDv := (pp + bv_unsigned plen).
  Hypothesis HC : CTX.

  Let exit_walk' := exit_walk L MSF MDTBL ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m PAR MD MGF SALT BUF pp lo bs plen HC.
  Let s2_walk' := s2_walk L MSF MDTBL ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m PAR MD MGF SALT BUF pp lo bs plen HC.

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "02G0@D12428150072.158D14586790212.158D15466246502.183D15513432785.183D16496876345.158D16974982078.158D18384852558.158D19418348606.158D19854584726.158D20153598198.158D20264044729.158D21751847415.183D24073348689.158D26291562981.158D26307352806.183D27140428777.185D30166613141.159D31361227473.158D36191331830.158D37219266001.183D3827506166.158 D40110156729.158D40726337382.183D40741479608.158D40887155268.183D43460435001.158D44088023374.183D44484923210.158D44484923210.183D44489311462.183D45347449913.158D46010008310.158D46029161400.158D4638239569.183 D48047786982.183D48094983505.183D49259150293.184D49527457489.158D5030578015.183 D51393036470.158D51650724673.183D51792814043.183D52101704109.160D52101704109.185D53098526161.158D53786012350.158D55381830097.183D56451042966.183D57897420622.183D58203696206.158D58891522918.183D59130109777.183D61623523385.158D62814340926.158D65179897657.158D65556039985.184D67071090489.158D67264843998.183D67622256948.183D8252413915.183 L11518786483.117L12428150072.142L14586790212.142L14946396720.141L15466246502.167L16974982078.142L18384852558.142L19418348606.142L19854584726.142L20153598198.142L20660446724.4  L21751847415.167L26291562981.142L26307352806.167L27140428777.169L29008372736.141L29010574176.162L3574711452.0   L36191331830.142L3827506166.142 L40726337382.167L40828781442.3  L40887155268.167L43090580551.2  L44088023374.167L44484923210.142L44484923210.167L44489311462.167L46010008310.142L48047786982.167L48268480918.182L5030578015.167 L51393036470.142L51650724673.167L51792814043.167L52065245876.141L53089759638.160L53524301853.163L53786012350.142L55542367123.2  L56451042966.167L57897420622.167L58203696206.142L58891522918.167L59308659786.3  L60010937425.2  L62814340926.142L63039843019.163L66986308662.0  L67158371251.117L67158371251.163L67264843998.167L67622256948.167L8252413915.167 L8932515595.146 R12596958038.162R12596958039.134R19079872282.134R195016675.162  R22792687469.181R2383289160.134 R24235034533.134R30207324909.158R30210556245.159R31542961004.134R33753208381.134R34848507722.134R34848507723.162R35176309081.162R35516336646.162R35516336647.134R3611875493.134 R36671363415.134R40111078497.162R46779386223.162R49419279906.162R51196631534.162R51206884378.134R51273849098.134R54652266247.134R57954699043.134R58136324425.158R58149722865.159R6443869642.134 R65009985896.181R66030093064.134R66030093065.162R7149229104.158 R7162767240.159 R8532465610.134 R8532465611.162 00000100200300N00e00f00g00h00i00j01A01B01Y01Z01[01\02902P02Q02l02m03D03E03_03`04704804904:04;04R04S04m05H05I05d06E06\06]06^06_06`07`08d09;09<09W09X09Y09Z09[0:60:M0:N0:e0;F0;]0;^0;_0;`0<70<80<90<:0=30=h0>a0?V0@K0AD0AP0An0Ao0Bh0C`0Ca0Cb0Cc0D\0EQ0FJ0FT0FU0F[0GT0GU0GV0HO0ID0J=0JX0LA0M60MW0N90N:0NQ0Om0Pb0Ph0Qa0R^0SS0TL0TV0TW0UL0W>0W?0WV0X30Yc0Yd0ZB0ZC0[C0\?0]m0_U0`C0`b0a^0bA0bh0cm0dD0eD0fH0gG0ge0h?0i;0j70jY0l?0la0nF10410V11011N11m12S13S14i15e16e18=19U1:U1;YFFFS2sp3PAR2MD3MGF4SALT2bs3obsS2sp3PAR2MD3MGF4SALT2bsFFFFFS2sp3PAR2MD3MGF4SALT2bsFS2sp3PAR2MD3MGF4SALT2bsFFFS2sp3PAR2MD3MGF4SALT2bs3x391HS2sp3PAR2MD3MGF4SALT2bsFS2sp3PAR2MD3MGF4SALT2bs3obsFS2sp3PAR2MD3MGF4SALT2bsFS2sp3PAR2MD3MGF4SALT2lo2bsFS2sp3PAR2MD3MGF4SALT2bsFFFFS2sp3PAR2MD3MGF4SALT2bsFS2sp3PAR2MD3MGF4SALT2lo2bsS2sp3PAR2MD3MGF4SALT2bs3obsFS2sp3PAR2MD3MGF4SALT2bs3obsS2sp3PAR2MD3MGF4SALT2bs3obs3x511HS2sp3PAR2MD3MGF4SALT2bsFFFFS1L2sp3PAR2MD3MGF4SALT2lo2bs3NZP3NZ13NZ23NZ33SLO3ACL3DHI3SPR1a1HS1L2sp3PAR2MD3MGF4SALT2lo2bs3NZP3NZ13NZ23NZ33SLO3ACL3DHI3SPR3obs1a1HS2sp3PAR2MD3MGF4SALT2bsFS2sp3PAR2MD3MGF4SALT2bs3obsFFFFS2sp3PAR2MD3MGF4SALT2bs3obsS2sp3PAR2MD3MGF4SALT2bsFS2sp3PAR2MD3MGF4SALT2bsS2sp3PAR2MD3MGF4SALT2bs3obs3x511HS2sp3PAR2MD3MGF4SALT2bsFFFS2sp3PAR2MD3MGF4SALT2bsFFFS2sp3PAR2MD3MGF4SALT2lo2bs3NZP3NZ13NZ23NZ33SLO2HD3SPR3obsS2sp3PAR2MD3MGF4SALT2lo2bs3NZP3NZ13NZ23NZ33SLO2HD3SPRS2sp3PAR2MD3MGF4SALT3BUF2lo2bs3NZP3NZ13NZ23NZ33SLO2HD3SPRS2sp3PAR2MD3MGF4SALT2lo2bs3NZP3NZ13NZ23NZ33SLO2HD3SPRS2sp3PAR2MD3MGF4SALT2lo2bs3NZP3NZ13NZ23NZ33SLO2HD3SPRS2sp3PAR2MD3MGF4SALT3BUF2lo2bs3NZP3NZ13NZ23NZ33SLO2HD3SPRS1r2Hr2r'2R3S2sp3PAR2MD3MGF4SALT2bs2HD3obsFS2sp3PAR2MD3MGF4SALT2lo2bs3NZP3NZ13NZ23NZ33SLO2HD3SPR3obsS1L2sp3PAR2MD3MGF4SALT2bs3NZP3NZ13NZ23NZ32HD3SPR3obs1a1HFFSS2sp3PAR2MD3MGF4SALT3BUF2lo2bs3NZP3NZ13NZ23NZ33SLO2HD3SPRS2sp3PAR2MD3MGF4SALT2lo2bs3NZP3NZ13NZ23NZ33SLO2HD3SPRS2sp3PAR2MD3MGF4SALT2lo2bs3NZP3NZ13NZ23NZ33SLO2HD3SPR3obsS2r'2R12KSFS1r2HrS2sp3PAR2MD3MGF4SALT2lo2bs3NZP3NZ13NZ23NZ33SLO2HD3SPR3obsFFS2sp3PAR2MD3MGF4SALT2lo2bs3NZP3NZ13NZ23NZ33SLO2HD3SPR3obsS2sp3PAR2MD3MGF4SALT2lo2bs3NZP3NZ13NZ23NZ33SLO2HD3SPRS2sp3PAR2MD3MGF4SALT2lo2bs3NZP3NZ13NZ23NZ33SLO2HD3SPR3obsS2sp3PAR2MD3MGF4SALT2bs3obsS2sp3PAR2MD3MGF4SALT3BUF2bs2HD3NZP3NZ13NZ23NZ33SPR2ap4HAP13obs2pp4plen1q2Lw3HqL4HPP22q23ALw3PC54HAP24LENOS2sp3PAR2MD3MGF4SALT2lo2bs3NZP3NZ13NZ23NZ33SLO2HD3SPRS2sp3PAR2MD3MGF4SALT2lo2bs2HD3obsS2sp3PAR2MD3MGF4SALT3BUF2bs2HD3obsFS2sp3PAR2MD3MGF4SALT2bsS2sp3PAR2MD3MGF4SALT3BUF2pp2bs4plen1q2Lw2Hq3HqL4HPP22B43NZP3NZ13NZ23NZ33NZB3SPR2q23PC53obs1rS2sp3PAR2MD3MGF4SALT2lo2bs3NZP3NZ13NZ23NZ33SLO2HD3SPRS1r2HrS2sp3PAR2MD3MGF4SALT2lo2bs3NZP3NZ13NZ23NZ33SLO2HD3SPR3obsS2sp3PAR2MD3MGF4SALT3BUF2lo2bs3NZP3NZ13NZ23NZ33SLO2HD3SPR3obsS2sp3PAR2MD3MGF4SALT2lo2bs3NZP3NZ13NZ23NZ33SLO2HD3SPRS2sp3PAR2MD3MGF4SALT2lo2bs3NZP3NZ13NZ23NZ33SLO2HD3SPR3obsS2r'2KS2E'SS2sp3PAR2MD3MGF4SALT2lo2bs3NZP3NZ13NZ23NZ33SLO2HD3SPRS2sp3PAR2MD3MGF4SALT3BUF2pp2bs4plen1q2Lw3HqL4HPP22B43NZP3NZ13NZ23NZ33NZB3SPR2q23ALw2ap3PC54HAP14HAP23obs4LENO1r2HqSS2sp3PAR2MD3MGF4SALT2bsS2sp3PAR2MD3MGF4SALT2bs3obs1rS2sp3PAR2MD3MGF4SALT3BUF2pp2lo2bs4plen1q2Lw3HqL4HPP23NZP3NZ13NZ23NZ33SLO2HD3SPR2q23ALw2ap3PC54HAP23obs4LENO4HAP1FS2sp3PAR2MD3MGF4SALT2bs2HD3obsFS1L2sp3PAR2MD3MGF4SALT2lo2bs3NZP3NZ13NZ23NZ33SLO3ACL3ACP3SPR3obsS1L2sp3PAR2MD3MGF4SALT2lo2bs3NZP3NZ13NZ23NZ33SLO3ACL3ACP3SPRS2sp3PAR2MD3MGF4SALT3BUF2pp2lo2bs4plen1q2Lw2Hq3HqL4HPP23D1B3D2B3D3B3NZP3NZ13NZ23NZ33SLO3DS13DS23DS33DSB3SPR2LRS2sp3PAR2MD3MGF4SALT3BUF2pp2lo2bs4plen1q2Lw3HqL4HPP23NZP3NZ13NZ23NZ33DSB3SPR2q23ALw2ap3PC54HAP14HAP23obsS2sp3PAR2MD3MGF4SALT2pp2bs4plen1q2Lw3HqL3obs1rS2sp3PAR2MD3MGF4SALT2bs1q2Lw2LRS1L2sp3PAR2MD3MGF4SALT2lo2bs3NZP3NZ13NZ23NZ33SLO3ACL3DHI3SPRS2sp3PAR2MD3MGF4SALT3BUF2bs2ap4HAP1S2sp3PAR2MD3MGF4SALT3BUF2bs3ALw2ap4HAP1S2sp3PAR2MD3MGF4SALT3BUF2pp2bs4plen1q2Lw3HqL4HPP23NZP3NZ13NZ23NZ33SPRS2sp3PAR2MD3MGF4SALT2bsS1L2sp3PAR2MD3MGF4SALT2lo2bs3NZP3NZ13NZ23NZ33SLO3ACL3ACP3SPA3SPRS1L2sp3PAR2MD3MGF4SALT2lo2bs3NZP3NZ13NZ23NZ33SLO3ACL3ACP3SPA3SPR3obsS2sp3PAR2MD3MGF4SALT3BUF2bs3NZP3NZ13NZ23NZ33NZB3SPR2ap4HAP13obsS2sp3PAR2MD3MGF4SALT2lo2bs3obsS2sp3PAR2MD3MGF4SALT2lo2bsS1L2sp3PAR2MD3MGF4SALT2lo2bs3NZP3NZ13NZ23NZ33SLO3ACL3DHI3SPRS1L2sp3PAR2MD3MGF4SALT2lo2bs3NZP3NZ13NZ23NZ33SLO3ACL3ACP3SPRS2sp3PAR2MD3MGF4SALT2lo2bs3DS13obsS2sp3PAR2MD3MGF4SALT3BUF2lo2bs3D123D133D1P3D1B3AL13NZP3NZ13NZ23NZ33SLO3SPA3DSP3DS13DS23DS33DSB3SPR3obsS2sp3PAR2MD3MGF4SALT2lo2bs3SLO3obsS2sp3PAR2MD3MGF4SALT3BUF2pp2bs4plen1q2Lw3HqL4HPP23D1B3NZP3NZ13NZ23NZ33SPR2q23ALw2ap3PC54HAP14HAP23obsS2sp3PAR2MD3MGF4SALT3BUF2pp2lo2bs4plen1q2Lw2Hq3HqL4HPP23D1B3D2B3D3B3NZP3NZ13NZ23NZ33SLO3DS13DS23DS33DSB3SPR2LRS2sp3PAR2MD3MGF4SALT3BUF2lo2bs3DSBS2sp3PAR2MD3MGF4SALT2lo2bsS2sp3PAR2MD3MGF4SALT2lo2bs3SLOS2sp3PAR2MD3MGF4SALT2bs3ALw3ALRS2sp3PAR2MD3MGF4SALT3BUF2bs3ALw2ap3ALRS1L2sp3PAR2MD3MGF4SALT2lo2bs3NZP3NZ13NZ23NZ33SLO3ACL3ACP3SPA3SPRS2sp3PAR2MD3MGF4SALT3BUF2bs1q2Lw3NZP3NZ13NZ23NZ33SPR2q23ALw2ap4HAP14HAP23obs4LENO1r2KMS1L2sp3PAR2MD3MGF4SALT2lo2bs3NZP3NZ13NZ23NZ33SLO3ACL3ACP3SPRS1L2sp3PAR2MD3MGF4SALT2lo2bs3NZP3NZ13NZ23NZ33SLO3ACL3ACP3SPR3obsS2sp3PAR2MD3MGF4SALT3BUF2pp2bs4plen1q2Lw3HqL4HPP23NZP3NZ13NZ23NZ33SPR2q23ALw2ap3PC54HAP2S2sp3PAR2MD3MGF4SALT3BUF2pp2bs4plen1q2Lw3HqL4HPP23NZP3NZ13NZ23NZ33SPR2q23ALw2ap3PC54HAP2S1L2sp3PAR2MD3MGF4SALT2lo2bs3NZP3NZ13NZ23NZ33SLO3ACL3ACP3SPA3SPRS1L2sp3PAR2MD3MGF4SALT2lo2bs3NZP3NZ13NZ23NZ33SLO3ACL3ACP3SPA3SPR3obs". (* [comment removed for export] *)
  #[using="MSF MDTBL PAR HC exit_walk' s2_walk'"] Lemma s1h_walk : forall (q : Z) (Lw : word) (j4 : list byte) (tfw qtag qpad qlen qpw atag apad alen apw w1 w2 w3 : word)
      (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x28 x29 x30 x31 : word) mm,
    rw_cells usegs mm (bv_unsigned sp + -128) [CB 12 j4; C4 tfw] ->
    rw_cells usegs mm (bv_unsigned sp + -112) [C4 qtag; C4 qpad; C8 qlen; C8 qpw] ->
    rw_cells usegs mm (bv_unsigned sp + -88) [C4 atag; C4 apad; C8 alen; C8 apw] ->
    rw_cells usegs mm (bv_unsigned sp + -64) [C8 Lw] ->
    rw_cells usegs mm (bv_unsigned sp + -56) [C8 (Z_to_bv 64 q)] ->
    rw_cells usegs mm (bv_unsigned sp + -48) [C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
    rw_cells usegs mm MD [C4 w1] -> rw_cells usegs mm MGF [C4 w2] -> rw_cells usegs mm SALT [C4 w3] ->
    bytes_at usegs mm BUF bs ->
    stk usegs mm lo (bv_unsigned sp + -128) -> munch W m mm -> wmono usegs m mm -> mem_inv usegs mm -> statics_ok usegs L mm ->
    BUF <= q -> bv_unsigned Lw <= ENDv - q ->
    evt usegs POST
      (MS (mkR x1 SPF gp tp x5 x6 x7 (Z_to_bv 64 ENDv) (Z_to_bv 64 MGF) x10 x11 x12 x13 x14 x15 x16 x17 x18 (Z_to_bv 64 SALT) (Z_to_bv 64 MD) s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
          F (Z_to_bv 64 0x27a0c) fc None mm (seg_rom usegs))
(* [comment removed for export] *).
  Proof.
    intros q Lw j4 tfw qtag qpad qlen qpw atag apad alen apw w1 w2 w3 x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x28 x29 x30 x31 mm
      F0 FPAR FALG FL FP FS HMD HMGF HSALT HBUF ST MU WM MI SOK Hq HqL.
    open_ctx HC.
    pose proof (bv_unsigned_in_range 64 plen) as PLR. unfold bv_modulus in PLR. cbn in PLR.
    pose proof (bv_unsigned_in_range 64 Lw) as LR. unfold bv_modulus in LR. cbn in LR.
    pose proof (bytes_at_bound _ _ _ _ HBUF) as BB.
    lxp_run (PLAN [0x1e5b8; 0x1e6d0; 0x1edc0; 0x1ef8c; 0x2612c; 0x27964; 0x2798c; 0x279b4; 0x279dc; 0x27a7c; 0x27b00; 0x27bf8; 0x46940] [] 197%N).
    lxp_gc. try lxp_statics.
    lxp_frame_cut (bv_unsigned sp + -128) [40; 64; 72; 80].
    pose proof HALGN as SPN. unfold asn1_get_alg_null_stmt, U_ASN1_GET_ALG_NULL in SPN.
    callx_sp (bv_unsigned sp + -128)
      (eapply SPN with (PP := bv_unsigned sp + -56) (ALG := bv_unsigned sp + -88) (P := q) (END := q + bv_unsigned Lw) (BUF := BUF) (bs := bs) (lo := lo);
       rewrite ?(unsigned_lit (bv_unsigned sp + -128)) by plia; try eassumption; try reflexivity; try plia).
    clear SPN.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m5 end.
    match goal with H : rw_cells _ m5 (bv_unsigned sp + -88) [C4 ?a1_; C4 ?a2_; C8 ?a3_; C8 ?a4_] |- _ =>
      rename H into FALG; rename a3_ into ALw; rename a4_ into APw end.
    match goal with H : rw_cells _ m5 (bv_unsigned sp + -56) [C8 (Z_to_bv 64 ?qq)] |- _ => rename H into FP; rename qq into q2 end.
    match goal with H : ?x = Z_to_bv 64 ?rr |- _ => subst x; rename rr into r end.
    match goal with H : r = 0 -> _ |- _ => rename H into HA0 end.
    match goal with H : _ < r <= 0 |- _ => rename H into Hr end.
    match goal with H : stk _ m5 lo _ |- _ => rename H into ST5 end.
    pose proof (bv_unsigned_in_range 64 ALw) as ALR. unfold bv_modulus in ALR. cbn in ALR.
    lxp_gc.
    destruct (Z.eq_dec r 0) as [R0|R0].
    2:{ (* [comment removed for export] *)
      assert (RN : r < 0) by lia. clear R0.
      lxp_run (PLAN [0x1e5b8; 0x1e6d0; 0x1edc0; 0x1ef8c; 0x2612c; 0x27964; 0x2798c; 0x279b4; 0x279dc; 0x27a7c; 0x27b00; 0x27bf8; 0x46940] [] 197%N).
      all: lxp_apply exit_walk. }
    subst r. clear Hr.
    specialize (HA0 eq_refl). ddestruct HA0 as (ap & -> & HAP1 & HAP2).
    (* [comment removed for export] *)
    lxp_run (PLAN [0x1e5b8; 0x1e6d0; 0x1edc0; 0x1ef8c; 0x2612c; 0x27964; 0x2798c; 0x279b4; 0x279dc; 0x27a7c; 0x27b00; 0x27bf8; 0x46940] [] 197%N).
    lxp_gc. try lxp_statics.
    lxp_frame_cut (bv_unsigned sp + -128) [40; 64].
    match goal with H : rw_cells _ _ (bv_unsigned sp + -88) _ |- _ => rewrite <- (Z_to_bv_bv_unsigned ALw) in H; rename H into FALG end.
    set (obs := firstn (Z.to_nat (bv_unsigned ALw)) (skipn (Z.to_nat (ap - BUF)) bs)).
    assert (LENO : Z.of_nat (length obs) = bv_unsigned ALw) by (subst obs; apply bytes_at_sub_length; plia).
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
      lazymatch goal with HB : bytes_at _ mx BUF bs |- _ =>
        assert (HOB : bytes_at usegs mx ap obs) by (subst obs; eapply bytes_at_sub; [exact HB| plia| plia| plia]) end end.
    clearbody obs.
    pose proof HMDS as SPM. unfold oid_lookup1_stmt, U_OID_GET_MD_ALG, buf_cells in SPM.
    callx_sp (bv_unsigned sp + -128)
      (eapply SPM with (OID := bv_unsigned sp + -88) (EXT := MD) (P := ap) (LEN := bv_unsigned ALw) (xs := obs) (lo := lo);
       rewrite ?(unsigned_lit (bv_unsigned sp + -128)) by plia; try eassumption; try reflexivity; try plia).
    clear SPM.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m6 end.
    match goal with H : ?x = Z_to_bv 64 ?rr |- _ => subst x; rename rr into r end.
    match goal with H : r = 0 \/ _ |- _ => rename H into Hr end. unfold MBEDTLS_ERR_OID_NOT_FOUND in Hr.
    match goal with H : stk _ m6 lo _ |- _ => rename H into ST6 end.
    lxp_gc.
    lxp_run (PLAN [0x1e5b8; 0x1e6d0; 0x1edc0; 0x1ef8c; 0x2612c; 0x27964; 0x2798c; 0x279b4; 0x279dc; 0x27a7c; 0x27b00; 0x27bf8; 0x46940] [] 197%N).
    all: first [ lxp_at 162428; lxp_apply exit_walk | lxp_at 162148; lxp_apply s2_walk ].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
End Walk.
