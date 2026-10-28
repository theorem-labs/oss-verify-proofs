(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Walk AStep CellsX Image Asn1Aux X509Aux X509AuxB.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Spec Require Import Rep.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U Require Import UImg U_string U_asn1_get_tag U_asn1_get_int U_oid U_oid_md_alg U_asn1_get_mpi U_platform_zeroize U_asn1_get_alg_A U_asn1_get_alg U_asn1_get_alg_null U_x509_get_hash_alg U_x509_get_rsassa_pss_A U_x509_get_rsassa_pss_B U_x509_get_rsassa_pss_C.
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
Ltac2 gd_tbl_P_x509_get_rsassa_pss_D () : Init.string Init.list := ["Corelib.Numbers.BinNums.Z"; "Corelib.Init.Datatypes.list"; "stdpp.bitvector.definitions.bv"; "Corelib.Init.Datatypes.option"; "RocqVerifyHarness.AgentSubmission.Lib.Step.rw_cells"; "RocqVerifyHarness.AgentSubmission.U.UImg.usegs"; "Stdlib.ZArith.BinInt.Z.add"; "stdpp.bitvector.definitions.bv_unsigned"; "Corelib.Init.Datatypes.cons"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.cell"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.CB"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C4"; "Corelib.Init.Datatypes.nil"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C8"; "stdpp.bitvector.definitions.Z_to_bv"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.bytes_at"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.stk"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.munch"; "Corelib.Init.Datatypes.prod"; "Corelib.Init.Datatypes.pair"; "Stdlib.ZArith.BinInt.Z.sub"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.wmono"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.mem_inv"; "RocqVerifyHarness.AgentSubmission.Lib.AStep.statics_ok"; "Stdlib.ZArith.BinInt.Z.le"; "RocqVerifyHarness.AgentSubmission.Lib.Exec.evt"; "RocqVerifyHarness.AgentSubmission.U.U_x509_get_rsassa_pss_A.x509_get_rsassa_pss_params_post"; "RocqVerifyHarness.AgentSubmission.Lib.MState.MS"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.mkR"; "Corelib.Init.Datatypes.None"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.seg_rom"].


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
  Let s3_walk' := s3_walk L MSF MDTBL ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m PAR MD MGF SALT BUF pp lo bs plen HC.
  Let s2b_walk' := s2b_walk L MSF MDTBL ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m PAR MD MGF SALT BUF pp lo bs plen HC.

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "02C0@D11375003030.181D12218223161.155D12428150072.181D1343986644.181 D15037909945.181D16496876345.155D16496876345.181D16974982078.155D16974982078.181D17565844854.155D19418348606.181D20153598198.181D20264044729.155D20264044729.181D20994638648.155D2265817462.181 D2274929014.155 D24323521813.182D26291562981.181D26722167889.181D30210897849.155D30228025918.155D31162734262.181D36191331830.155D36191331830.181D36583815225.181D3827506166.155 D3827506166.181 D3863394750.181 D39823997752.181D40110156729.181D40129553998.181D40433219958.181D40741479608.181D43888467129.181D44022766142.181D44484923210.181D45347449913.181D46010008310.181D46029161400.155D46029161400.181D48356160441.155D51791381457.181D52101704109.158D52101704109.183D53786012350.181D55677588537.155D61623523385.181D6255928132.181 D62814340926.155D62814340926.181D63042527678.155D65179897657.181D66418546897.181D67071090489.155D67562352718.181D9195366073.155 D9730913345.157 L11275736598.156L11375003030.165L11518786483.137L12428150072.165L1343986644.165 L14946396720.165L16974982078.139L16974982078.165L17565844854.139L19418348606.165L20153598198.165L20660446724.4  L2265817462.165 L2274929014.139 L26291562981.165L29008372736.165L29008469930.139L29010574176.138L30228025918.139L31162734262.165L31165788229.116L31914898123.2  L34603895532.0  L36191331830.139L36191331830.165L3827506166.139 L3827506166.165 L3863394750.165 L39360104073.116L40129553998.165L40433219958.165L40828781442.3  L43090580551.2  L44022766142.165L44484923210.165L46010008310.165L52065245876.165L53786012350.165L59308659786.3  L60010937425.2  L6255928132.165 L62814340926.139L62814340926.165L63042527678.139L66151402056.3  L66986308662.0  L67158371251.137L67158371251.140L67562352718.165L8278980118.184 L8932515595.170 R12596958032.154R17698465547.156R17698853562.154R18042445946.184R19077775108.134R19079872285.154R22792027211.184R2383289167.154 R24235034530.154R27053815482.154R29946627972.134R30643776720.154R31542961003.154R33753208378.154R33879773476.154R34164561850.154R34848507725.154R35101928994.154R35516336640.154R3611875490.154 R36671363408.154R36673460553.134R40357422493.154R42695276489.134R43592025415.184R46366855808.154R51206884381.154R51273849101.154R51892457379.134R54652266240.154R54995020636.156R56114490102.184R62003914580.134R63054757965.154R6443869645.154 R6445966804.134 R66030093071.154R8532465613.154 00000100H00I00J00a01801O01P01Q01R01S01T01k02B02\02]02^03L03M03d04;04<04=04>04?04V04W04X04Y05305J05K05L05f06=06>06?06V06W07107K07b0890990:90::0:Q0:h0:i0:j0:k0:l0;C0;Z0<10<20<I0=O0=f0>[0?20?30?40?50?j0@_0AX0BM0CF0CR0DG0E<0E=0E>0E?0E@0F50Fj0H70H=0H>0I70J00Je0KZ0LO0MW0NL0OE0OO0OU0PJ0PK0Q@0QA0R60R@0RA0RB0S70Sl0Ta0Tj0Tk0UB0U[0VT0Vk0Vl0Wh0Xm0Yg0ZJ0\60^50^]0_<0`80`O0b;0c70d<0dS0e10eH0fH0gD0g^0hZ0iV0jR0lQ0mM0nQ0nk10j11L11c12=12f15A16A17A18A19A1:=1;=FS2sp3PAR2MD3MGF4SALT2bsFFS2sp3PAR2MD3MGF4SALT2bsS2sp3PAR2MD3MGF4SALT2bsS2sp3PAR2MD3MGF4SALT2bsFFFFFS2sp3PAR2MD3MGF4SALT2bsS2sp3PAR2MD3MGF4SALT2bsS2sp3PAR2MD3MGF4SALT2lo2bsFFS2sp3PAR2MD3MGF4SALT2pp2bs4plen1p3Hp12KE3x571HFS2sp3PAR2MD3MGF4SALT2bsS2sp3PAR2MD3MGF4SALT2bsFFFFS2sp3PAR2MD3MGF4SALT2bsFFFS2sp3PAR2MD3MGF4SALT2lo2bsS2sp3PAR2MD3MGF4SALT2bsFFS2sp3PAR2MD3MGF4SALT2lo2bsS2sp3PAR2MD3MGF4SALT2bsFFS2sp3PAR2MD3MGF4SALT2bsFS2sp3PAR2MD3MGF4SALT2lo2bsS2sp3PAR2MD3MGF4SALT2lo2bsS2sp3PAR2MD3MGF4SALT2bsS2sp3PAR2MD3MGF4SALT2bsS1L2sp3PAR2MD3MGF4SALT2lo2bs3NZP3NZ13NZ23NZ33SLO3ACL3DHI3SPR1a1HS1L2sp3PAR2MD3MGF4SALT2lo2bs3NZP3NZ13NZ23NZ33SLO3ACL3DHI3SPR1a1HFS2sp3PAR2MD3MGF4SALT2bsS2sp3PAR2MD3MGF4SALT2bsFFFFS2sp3PAR2MD3MGF4SALT2bsS2sp3PAR2MD3MGF4SALT2bsS2sp3PAR2MD3MGF4SALT2bsFS2sp3PAR2MD3MGF4SALT2bsS2sp3PAR2MD3MGF4SALT2pp2bs4plen1p3x323Hp12KE2x33x333x343x354POST3x361HS2sp3PAR2MD3MGF4SALT2bsS2sp3PAR2MD3MGF4SALT2lo2bs3NZP3NZ13NZ23NZ33SLO2HD3SPRS2sp3PAR2MD3MGF4SALT2bsFFFS2sp3PAR2MD3MGF4SALT2lo2bs3NZP3NZ13NZ23NZ33SLO2HD3SPRS2sp3PAR2MD3MGF4SALT2lo2bs3NZP3NZ13NZ23NZ33SLO2HD3SPRS2sp3PAR2MD3MGF4SALT3BUF2lo2bs3NZP3NZ13NZ23NZ33SLO2HD3SPRS2sp3PAR2MD3MGF4SALT2lo2bs3NZP3NZ13NZ23NZ33SLO2HD3SPRS2sp3PAR2MD3MGF4SALT3BUF2lo2bs3NZP3NZ13NZ23NZ33SLO2HD3SPRS1r2Hr2r'2R3S2sp3PAR2MD3MGF4SALT2lo2bs3NZP3NZ13NZ23NZ33SLO2HD3SPRS2sp3PAR2MD3MGF4SALT2lo2bs3NZP3NZ13NZ23NZ33SLO2HD3SPRFFFFS2sp3PAR2MD3MGF4SALT2lo2bs3NZP3NZ13NZ23NZ33SLO2HD3SPRS2sp3PAR2MD3MGF4SALT2lo2bs3NZP3NZ13NZ23NZ33SLO2HD3SPRS2sp3PAR2MD3MGF4SALT3BUF2pp2bs4plen1p3Hp03Hp14HPP22B43NZP3NZ13NZ23NZ33NZB3SPRS1r2HrSS2sp3PAR2MD3MGF4SALT3BUF2lo2bs3NZP3NZ13NZ23NZ33SLO2HD3SPRS2sp3PAR2MD3MGF4SALT3BUF2lo2bs3NZP3NZ13NZ23NZ33SLO2HD3SPRS2sp3PAR2MD3MGF4SALT2lo2bs3NZP3NZ13NZ23NZ33SLO2HD3SPRS2sp3PAR2MD3MGF4SALT2lo2bs3NZP3NZ13NZ23NZ33SLO2HD3SPRS2sp3PAR2MD3MGF4SALT2lo2bs3NZP3NZ13NZ23NZ33SLO2HD3SPRS2sp3PAR2MD3MGF4SALT3BUF2pp2bs4plen4HPP24HPP12B43NZP3NZ13NZ23NZ33SPR3PLRS2sp3PAR2MD3MGF4SALT2lo2bs3NZP3NZ13NZ23NZ33SLO2HD3SPRS2sp3PAR2MD3MGF4SALT3BUF2lo2bs3NZP3NZ13NZ23NZ33SLO2HD3SPRS2r'2R12KSS1r2HrS2sp3PAR2MD3MGF4SALT2lo2bs3NZP3NZ13NZ23NZ33SLO2HD3SPRFS2sp3PAR2MD3MGF4SALT2lo2bs3NZP3NZ13NZ23NZ33SLO2HD3SPRFS2sp3PAR2MD3MGF4SALT2lo2bs3NZP3NZ13NZ23NZ33SLO2HD3SPRS2r'2KS2E'SFS2sp3PAR2MD3MGF4SALT2lo2bs3NZP3NZ13NZ23NZ33SLO2HD3SPRS2sp3PAR2MD3MGF4SALT2lo2bs3NZP3NZ13NZ23NZ33SLO2HD3SPRS2sp3PAR2MD3MGF4SALT2lo2bs3NZP3NZ13NZ23NZ33SLO2HD3SPRS1r2Hr2KrSS2sp3PAR2MD3MGF4SALT2bsS2sp3PAR2MD3MGF4SALT2bs1rS2sp3PAR2MD3MGF4SALT3BUF2lo2bs3NZP3NZ13NZ23NZ33SLO2HD3SPRS2sp3PAR2MD3MGF4SALT2bsFS1L2sp3PAR2MD3MGF4SALT2lo2bs3NZP3NZ13NZ23NZ33SLO3ACL3ACP3SPRS2sp3PAR2MD3MGF4SALT3BUF2pp2bs4plen1p3Hp03NZP3NZ13NZ23NZ33SPR1r1q3PC3S2sp3PAR2MD3MGF4SALT3BUF2bs1p3Hp03NZP3NZ13NZ23NZ33SPR1q2HqS2sp3PAR2MD3MGF4SALT2bs1q2Lw2q23PC7S2sp3PAR2MD3MGF4SALT3BUF2pp2lo2bs4plen1p3Hp03Hp14HPP23D1B3D2B3D3B3NZP3NZ13NZ23NZ33SLO3DS13DS23DS33DSB3SPR2KES2sp3PAR2MD3MGF4SALT3BUF2pp2lo2bs4plen1p3Hp03Hp14HPP23D1B3D2B3D3B3NZP3NZ13NZ23NZ33SLO3DS13DS23DS33DSB3SPR2KE1q2Lw3PC32Hq3HqL2LRS2sp3PAR2MD3MGF4SALT2pp2bs4plen1q2Lw3HqLS2sp3PAR2MD3MGF4SALT2bs1q2Lw2LRS1L2sp3PAR2MD3MGF4SALT2lo2bs3NZP3NZ13NZ23NZ33SLO3ACL3DHI3SPRS2sp3PAR2MD3MGF4SALT2bsS2sp3PAR2MD3MGF4SALT3BUF2pp2lo2bs4plen1p3Hp03Hp14HPP23D1B3D2B3D3B3NZP3NZ13NZ23NZ33SLO3DS13DS23DS33DSB3SPR2KES1L2sp3PAR2MD3MGF4SALT2lo2bs3NZP3NZ13NZ23NZ33SLO3ACL3ACP3SPRS2sp3PAR2MD3MGF4SALT3BUF2pp2bs4plen4HPP23NZP3NZ13NZ23NZ33SPR1q2Lw3HqLS2sp3PAR2MD3MGF4SALT2bsS2sp3PAR2MD3MGF4SALT2lo2bs3SLOS2sp3PAR2MD3MGF4SALT2bsS1L2sp3PAR2MD3MGF4SALT2lo2bs3NZP3NZ13NZ23NZ33SLO3ACL3ACP3SPA3SPRS1L2sp3PAR2MD3MGF4SALT2lo2bs3NZP3NZ13NZ23NZ33SLO3ACL3DHI3SPRS2sp3PAR2MD3MGF4SALT2lo2bsS1L2sp3PAR2MD3MGF4SALT2lo2bs3NZP3NZ13NZ23NZ33SLO3ACL3DHI3SPRS1L2sp3PAR2MD3MGF4SALT2lo2bs3NZP3NZ13NZ23NZ33SLO3ACL3ACP3SPRS1L2sp3PAR2MD3MGF4SALT2lo2bs3NZP3NZ13NZ23NZ33SLO3ACL3ACP3SPRS2sp3PAR2MD3MGF4SALT3BUF2pp2lo2bs4plen1p3Hp03Hp14HPP23D1B3D2B3D3B3NZP3NZ13NZ23NZ33SLO3DS13DS23DS33DSB3SPR2KE1q2Lw3PC32Hq3HqL2LRS1L2sp3PAR2MD3MGF4SALT2lo2bs3NZP3NZ13NZ23NZ33SLO3ACL3ACP3SPRS2sp3PAR2MD3MGF4SALT3BUF2bs1p3Hp03NZP3NZ13NZ23NZ33SPR1q2Lw2Hq2q23PC7S2sp3PAR2MD3MGF4SALT2lo2bsS2sp3PAR2MD3MGF4SALT3BUF2pp2lo2bs4plen1p3Hp03Hp14HPP23D1B3D2B3D3B3NZP3NZ13NZ23NZ33SLO3DS13DS23DS33DSB3SPR2KE1q2Lw3PC32Hq3HqL2LRS2sp3PAR2MD3MGF4SALT3BUF2lo2bs3DSBS2sp3PAR2MD3MGF4SALT2bsS2sp3PAR2MD3MGF4SALT2lo2bsS2sp3PAR2MD3MGF4SALT2pp2bs4plen1p1r1q3PC3S1L2sp3PAR2MD3MGF4SALT3BUF2pp2lo2bs4plen1p3Hp03Hp13NZP3NZ13NZ23NZ33NZB3SLO3ACL3ACP3SPR3MDB4MGFB5SALTB2KE1q2Lw2Hq2q23ALw3x533QLw2ap2qp3PC74HAP14HAP23HQP3ALRS1L2sp3PAR2MD3MGF4SALT2lo2bs3NZP3NZ13NZ23NZ33SLO3ACL3ACP3SPA3SPRS1L2sp3PAR2MD3MGF4SALT2lo2bs3NZP3NZ13NZ23NZ33SLO3ACL3ACP3SPA3SPRS1L2sp3PAR2MD3MGF4SALT2lo2bs3NZP3NZ13NZ23NZ33SLO3ACL3ACP3SPA3SPRS1L2sp3PAR2MD3MGF4SALT2lo2bs3NZP3NZ13NZ23NZ33SLO3ACL3ACP3SPA3SPRS1L2sp3PAR2MD3MGF4SALT2lo2bs3NZP3NZ13NZ23NZ33SLO3ACL3ACP3SPRS1L2sp3PAR2MD3MGF4SALT2lo2bs3NZP3NZ13NZ23NZ33SLO3ACL3ACP3SPA3SPR". (* [comment removed for export] *)
  #[using="MSF MDTBL PAR HC exit_walk' s3_walk' s2b_walk'"] Lemma s2_walk : forall (p : Z) (j4 : list byte) (tfw lw qtag qpad qlen qpw atag apad alen apw w1 w2 w3 : word)
      (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x20 x28 x29 x30 x31 : word) mm,
    rw_cells usegs mm (bv_unsigned sp + -128) [CB 12 j4; C4 tfw] ->
    rw_cells usegs mm (bv_unsigned sp + -112) [C4 qtag; C4 qpad; C8 qlen; C8 qpw] ->
    rw_cells usegs mm (bv_unsigned sp + -88) [C4 atag; C4 apad; C8 alen; C8 apw] ->
    rw_cells usegs mm (bv_unsigned sp + -64) [C8 lw] ->
    rw_cells usegs mm (bv_unsigned sp + -56) [C8 (Z_to_bv 64 p)] ->
    rw_cells usegs mm (bv_unsigned sp + -48) [C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
    rw_cells usegs mm MD [C4 w1] -> rw_cells usegs mm MGF [C4 w2] -> rw_cells usegs mm SALT [C4 w3] ->
    bytes_at usegs mm BUF bs ->
    stk usegs mm lo (bv_unsigned sp + -128) -> munch W m mm -> wmono usegs m mm -> mem_inv usegs mm -> statics_ok usegs L mm ->
    BUF <= p -> p <= ENDv ->
    evt usegs POST
      (MS (mkR x1 SPF gp tp x5 x6 x7 (Z_to_bv 64 ENDv) (Z_to_bv 64 MGF) x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 p) (Z_to_bv 64 SALT) x20 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
          F (Z_to_bv 64 0x27964) fc None mm (seg_rom usegs))
(* [comment removed for export] *).
  Proof.
    intros p j4 tfw lw qtag qpad qlen qpw atag apad alen apw w1 w2 w3 x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x20 x28 x29 x30 x31 mm
      F0 FPAR FALG FL FP FS HMD HMGF HSALT HBUF ST MU WM MI SOK Hp0 Hp1.
    open_ctx HC.
    pose proof (bv_unsigned_in_range 64 plen) as PLR. unfold bv_modulus in PLR. cbn in PLR.
    lxp_run (PLAN [0x1e5b8; 0x1e6d0; 0x1edc0; 0x1ef8c; 0x2612c; 0x2798c; 0x279b4; 0x279dc; 0x27a7c; 0x27b00; 0x27bf8; 0x46940] [] 197%N).
    { (* [comment removed for export] *) lxp_apply exit_walk. }
    lxp_gc. try lxp_statics.
    lxp_frame_cut (bv_unsigned sp + -128) [64; 72; 80].
    pose proof U_asn1_get_tag_spec as SP. unfold asn1_get_tag_stmt, U_ASN1_GET_TAG in SP.
    callx_sp (bv_unsigned sp + -128)
      (eapply SP with (PP := bv_unsigned sp + -56) (LENP := bv_unsigned sp + -64) (P := p) (END := ENDv) (BUF := BUF) (bs := bs);
       rewrite ?(unsigned_lit (bv_unsigned sp + -128)) by plia; try eassumption; try reflexivity; try plia).
    clear SP.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m4 end.
    match goal with H : rw_cells _ m4 (bv_unsigned sp + -64) [C8 ?lw] |- _ => rename H into FL; rename lw into Lw end.
    match goal with H : rw_cells _ m4 (bv_unsigned sp + -56) [C8 (Z_to_bv 64 ?qq)] |- _ => rename H into FP; rename qq into q end.
    match goal with H : ?x = Z_to_bv 64 ?rr |- _ => subst x; rename rr into r end.
    match goal with H : r = 0 -> _ |- _ => rename H into HL0 end.
    match goal with H : _ < r <= 0 |- _ => rename H into Hr end.
    match goal with H : stk _ m4 lo _ |- _ => rename H into ST4 end.
    pose proof (bv_unsigned_in_range 64 Lw) as LR. unfold bv_modulus in LR. cbn in LR.
    lxp_gc.
    destruct (Z.eq_dec r 0) as [R0|R0].
    2:{ (* [comment removed for export] *)
      assert (RN : r < 0) by lia. clear R0.
      lxp_run (PLAN [0x1e5b8; 0x1e6d0; 0x1edc0; 0x1ef8c; 0x2612c; 0x2798c; 0x279b4; 0x279dc; 0x27a7c; 0x27b00; 0x27bf8; 0x46940] [] 197%N).
      all: first [ lxp_at 162428; lxp_apply exit_walk | lxp_at 162188; lxp_apply s3_walk ]. }
    (* [comment removed for export] *)
    subst r. specialize (HL0 eq_refl). destruct HL0 as [Hq HqL]. clear Hr.
    lxp_run (PLAN [0x1e5b8; 0x1e6d0; 0x1edc0; 0x1ef8c; 0x2612c; 0x2798c; 0x279b4; 0x279dc; 0x27a7c; 0x27b00; 0x27bf8; 0x46940] [] 197%N).
    lxp_gc. try lxp_statics.
    lxp_frame_cut (bv_unsigned sp + -128) [16; 40; 64; 72; 80].
    pose proof HALGS as SPG. unfold asn1_get_alg_stmt, U_ASN1_GET_ALG in SPG.
    callx_sp (bv_unsigned sp + -128)
      (eapply SPG with (PP := bv_unsigned sp + -56) (ALG := bv_unsigned sp + -88) (PAR := bv_unsigned sp + -112) (P := q) (END := q + bv_unsigned Lw) (BUF := BUF) (bs := bs) (lo := lo);
       rewrite ?(unsigned_lit (bv_unsigned sp + -128)) by plia; try eassumption; try reflexivity; try plia).
    clear SPG.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m5 end.
    match goal with H : rw_cells _ m5 (bv_unsigned sp + -88) [C4 ?a1_; C4 ?a2_; C8 ?a3_; C8 ?a4_] |- _ =>
      rename H into FALG; rename a3_ into ALw; rename a4_ into APw end.
    match goal with H : rw_cells _ m5 (bv_unsigned sp + -112) [C4 ?a1_; C4 ?a2_; C8 ?a3_; C8 ?a4_] |- _ =>
      rename H into FPAR; rename a3_ into QLw; rename a4_ into QPw end.
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
      lxp_run (PLAN [0x1e5b8; 0x1e6d0; 0x1edc0; 0x1ef8c; 0x2612c; 0x2798c; 0x279b4; 0x279dc; 0x27a7c; 0x27b00; 0x27bf8; 0x46940] [] 197%N).
      all: lxp_apply exit_walk. }
    subst r. clear Hr.
    specialize (HA0 eq_refl). ddestruct HA0 as (ap & qp & -> & -> & HAP1 & HAP2 & HQP).
    lxp_run (PLAN [0x1e5b8; 0x1e6d0; 0x1edc0; 0x1ef8c; 0x2612c; 0x2798c; 0x279b4; 0x279dc; 0x27a7c; 0x27b00; 0x27bf8; 0x46940] [] 197%N).
    lxp_apply s2b_walk.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
End Walk.
