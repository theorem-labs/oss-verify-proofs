(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import MpiCoreAux MpiWalkAux.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.P Require Import P_ct_memcpy_if.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import AImg.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BLX Require Import LxA.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LXB Require Import LxAMpiTac.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibB Require Import TacA.   (* [comment removed for export] *)
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Import OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.LxhSyntax. #[local] Instance lxh_tab : OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.lx_hints := OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.lxh_parse "P00398bab13eaf8ca 0 2 0 1 3 1P00448d5b0be53606 0 3 0 1 25 1 39 1P0174aaf3cd0fa757 0 2 0 1 1 1P01f7a368e8a57870 0 2 0 1 12 1P02e5cf0579d163d7 2 46 0 5 0 1 3 1 29 1 43 1 46 1 0 5 0 1 2 1 21 1 28 1 42 1P046f91fe67d898bf 0 2 0 1 12 1P04a49707dc53a270 0 2 0 1 12 1P04afaa2523398978 0 2 0 1 11 1P0682eef8bad0ad51 0 4 0 1 21 1 27 1 41 1P069ce33c6693c208 0 3 0 1 23 1 29 1P0727ef9bbaea1b76 0 2 0 1 1 1P0783c5f04ce40fa6 0 2 0 1 13 1P07b258366d1c68d1 0 2 0 1 2 1P082d87c300f16415 0 3 0 1 23 1 37 1P0832476c478522d6 0 3 0 1 24 1 38 1P087644d2c0fa9916 0 3 0 1 20 1 32 1P08de25905ecf2e5c 0 5 0 1 11 1 15 1 19 1 31 1P0916a76b4882d191 0 3 0 1 25 1 33 1P0a704262e0b2b839 0 3 0 1 25 1 36 1P0b58144f7540de91 0 3 0 1 24 1 30 1P0c1c734b202dfd39 0 3 0 1 23 1 37 1P0c375b342871d6f4 0 2 0 1 4 1P0cac13d725be0564 0 4 0 1 23 1 33 1 34 1P0cae66199582736b 0 3 0 1 19 1 31 1P0d43442207ca9f87 0 4 0 1 16 1 22 1 30 1P0d638bb7e2ae1144 0 2 0 1 4 1P0dd464fc9a8cb939 0 2 0 1 4 1P0fccbf01c8e3e39c 0 2 0 1 4 1P1084dc41ba008482 0 3 0 1 25 1 39 1P110780d50602090f 0 3 0 1 26 1 40 1P132c0dd2b378087e 0 3 0 1 22 1 30 1P13b646be0ce4b1dd 0 5 0 1 16 1 17 1 23 1 37 1P146141617524f7ed 0 3 0 1 25 1 36 1P15a412c5e3ccb4c8 0 5 0 1 16 1 23 1 28 1 29 1P170098ef664ca767 0 2 0 1 13 1P18af65e2adb713ee 0 3 0 1 26 1 40 1P199329e0743b69c8 0 3 0 1 27 1 41 1P1ae9cd45eb4bfe99 0 2 0 1 29 1P1c20ce4e55f8b847 0 2 0 1 35 1P1d04f54f576dee34 2 42 0 5 0 1 1 1 20 1 27 1 41 1 0 4 0 1 2 1 28 1 42 1P1e1eb3fb47999171 0 4 0 1 24 1 34 1 35 1P1e6d241c0fbb4437 0 4 0 1 21 1 29 1 30 1P1f26ca3a34f84a25 0 2 0 1 12 1P1fff1cc1c0c02ec8 0 2 0 1 3 1P2000420bbdaf0eaf 0 2 0 1 4 1P206f5e6d057953c7 0 2 0 1 2 1P21f313718ccacb2e 0 3 0 1 21 1 29 1P2276ce1654c132b7 0 3 0 1 22 1 34 1P22dd5747084af4de 0 2 0 1 43 1P23273f4a29f92ab8 0 5 0 1 18 1 25 1 30 1 39 1P239af13ee822390d 0 2 0 1 34 1P23d198619e139db7 0 3 0 1 24 1 30 1P242ec92a2fb8129e 0 3 0 1 21 1 29 1P257582d6885ad68d 0 5 0 1 13 1 21 1 33 1 40 1P25db72301178abfb 0 4 0 1 23 1 33 1 34 1P25fcf93933f316d8 0 3 0 1 22 1 34 1P267e622039a0406c 0 3 0 1 23 1 35 1P26d028fc6c4f237d 0 2 0 1 1 1P26fda6ca8888a7d5 0 3 0 1 24 1 38 1P2731621dd722a407 0 5 0 1 14 1 15 1 21 1 29 1P28711d840611ffeb 0 2 0 1 3 1P297d42823c7c8202 0 3 0 1 19 1 31 1P29a553d80733ec54 0 4 0 1 19 1 23 1 35 1P2ba9304264bea5b3 0 4 0 1 19 1 25 1 33 1P2c6dc413fe3756d8 0 4 0 1 16 1 20 1 32 1P2ef8333462b5bb4c 0 2 0 1 13 1P300963823ab75880 0 2 0 1 11 1P3014fd358d28a890 0 3 0 1 21 1 33 1P30e99e29a4aa5f52 0 3 0 1 25 1 36 1P31aa43290bf33b6c 0 3 0 1 20 1 32 1P3201725562ac9913 0 2 0 1 4 1P339d1ff7ed3c8dd5 0 2 0 1 12 1P33dde521bfd16a19 0 4 0 1 24 1 34 1 35 1P3435d3d70f5b38de 0 4 0 1 15 1 26 1 35 1P34be7f3e151527c3 0 3 0 1 26 1 40 1P36bc8408167f5012 0 2 0 1 1 1P37c14b06513dfa2f 0 2 0 1 2 1P380363af9adef29e 0 2 0 1 43 1P397f1b839f40f833 0 2 0 1 1 1P39c04c573df7476e 0 3 0 1 24 1 32 1P39cc72c5b2105ed2 0 2 0 1 34 1P3b75b5d2708c400f 0 2 0 1 33 1P3b83a5e29230099b 0 2 0 1 3 1P3c32571ca178fc3d 0 3 0 1 22 1 30 1P3c3535c7dbf4b6ed 0 3 0 1 22 1 34 1P3e26d114f6d8edc8 0 4 0 1 15 1 26 1 35 1P3ef2a9118424c939 0 4 0 1 18 1 24 1 38 1P3f66e6f28ce01c50 0 3 0 1 26 1 40 1N0000f3ca8dab77b2N00ac31f9e542ce5fN010d04338c663e41N016fa04e9d78e7b8N017f70d97910a7eeN01eb98091ea55539N02d03821c6eec965N034be85e322793e9N0388d19aba5a6b09N040d21f2eadfee9fN047625a093151bbdN04f139ba2bcae5b7N072dd7a11e1ea37dN07d4485521da6e95N07d85814007d25faN07ff245133cb8496N080aa2a5063d7435N087013dcb0bee06aN0979344169a79115N09bc9322f893bf33N0a176c7252b50016N0a34848b1c599f27N0a97f60c56c37170N0af72c8aa8d6387cN0b18e5c53c49cc9bN0bb8509ad5f93e26N0d12a9fef9f99449N0d1b89a7f5208f10N0e7ee64a63f803daN0ec86d6f55c10bb6N0f54eb6a7ce8fd81N0fc912eea8361fe2N0fcf4b5d75dbd1ceN0fdbf834aebc715cN102951d77066a9b3N104b1778555d1782N10691f80419237e5N10b335c0016a9861N10e472020d760f96N11131848b246f93eN11289dd8d11fe70aN1184622d7e5e86b8N11ca93d8ca8fbcfeN1241074049c83f76N1279b6274f8f34dcN132b87c669d23153N13dde4d572f5dcc9N14dbdabbe0ce76dfN1513c7444909b5e3N15c702f0150ff31aN15e7757d49124834N16427bfbd8bc2555N1684e882d264c7e2N16d3256747bddb9cN16e23edd6246b12fN178503168afe2ab5N1827fb8507bffc57N1839d040ecdc4d17N19689548d6380cd9N19834e4d118f165cN19a7fc213ffe9321N19c0906a46cb2f29N1a6a64e1f7e3500dN1a8a7ad2c2356304N1b0a970de1098423N1c1e11977a2bfb50N1c67ea02103ef1a8N1c6d48caba90af30N1cc3ca682b8fb702N1dcb04b384569389N1e7ebb8ff7c80fc6N1ebf28dedef76166N1f173576952b28b2N1f3efbb68df8a1f3N1f77c530935f87e8N20446c5c12e4684bN2182d3ab234a6ff2N2186b2af57de8463N219d613bad55ee40N22915a28f9530382N234362fbb7e1f304N23b9e4a8c7b554fcN25e103345388f4c9N260be2adeb7ef040N26276ee5120b89ddN27fe58644058bcb1N28015dd897ecfbe0N28533a739c6e96a8N285aaf4e5ea64d53N287e38df316a0e89N28a579a07f8e956cN29e7f8f6b5884988N2a22c05f00f48973N2ab917e091c2d36eN2c9998dfc9425caaN2d59e1fe224acaf3N2e376e2cd8589945N2fd5f09fe606e084N2fe82d840347188eN30b400b0ec46020eN310fde1a2e746f24N3318545a7e70774dN338eef3010e5f2d9N347759362e56e8caN34858207e76b13d4N34ea0a1e27e4a597N35550f1a6235f50eN358150d707c13e46N362f53073ff306e1N36a4f05c5320ece4N371372f98fa032c4N37210ec4ad0d8894N372296a612cb5d8aN37544b71566394adN383025e3fd47016dN3833218e6a055d7dN3891626d9c3d2ba6N3a1c9b3217c4c641N3ae4b417c03ec0a7N3ae64d16b6825a2dN3ae8ce67b2c2ae56N3af5bf505bb47410N3b15e74888fdc9afN3c5faa7a8c10eb6cN3c74bb2139195976N3c80ecb69d78b2ccN3cda8380945cfa3fN3d3763cd11537c06N3e6bb0947c219c20N3e998f1c8029865aN3f186562ca35f627"%lxh.
Ltac2 gd_tbl_A_ct_memcpy_if () : Init.string Init.list := ["Corelib.Numbers.BinNums.Z"; "stdpp.bitvector.definitions.bv"; "LinuxProcessSemantics.Riscv.Prelude.bvmap"; "Corelib.Init.Datatypes.option"; "Corelib.Init.Datatypes.list"; "RocqVerifyHarness.AgentSubmission.Lib.Arr.u8arr"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.bytes_at"; "Corelib.Init.Logic.and"; "Stdlib.ZArith.BinInt.Z.le"; "Stdlib.ZArith.BinInt.Z.of_nat"; "Corelib.Init.Datatypes.length"; "Corelib.Init.Logic.or"; "Stdlib.ZArith.BinInt.Z.add"; "Corelib.Init.Logic.eq"; "Stdlib.ZArith.BinInt.Z.lt"; "Stdlib.ZArith.BinInt.Z.pow"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.stk"; "stdpp.bitvector.definitions.bv_unsigned"; "Stdlib.ZArith.BinInt.Z.sub"; "CT_MEMCPY_IF_STACK_B"; "Stdlib.ZArith.BinInt.Z.modulo"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.mem_inv"; "RocqVerifyHarness.AgentSubmission.LibA.AShadow.al_wf"; "RocqVerifyHarness.AgentSubmission.LibA.AShadow.cs_ok"; "RocqVerifyHarness.AgentSubmission.LibA.AShadow.abase"; "RocqVerifyHarness.AgentSubmission.LibA.AShadow.aobj"; "RocqVerifyHarness.AgentSubmission.LibA.ALazy.crange"; "stdpp.bitvector.definitions.Z_to_bv"; "RocqVerifyHarness.AgentSubmission.LibA.AEvtA.evtA"; "ct_memcpy_if_postB"; "RocqVerifyHarness.AgentSubmission.Lib.MState.MS"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.mkR"; "Corelib.Init.Datatypes.None"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.seg_rom"; "Corelib.Init.Datatypes.nat"; "Stdlib.ZArith.BinInt.Z.to_nat"; "RocqVerifyHarness.AgentSubmission.B.AImg.asegs"; "RocqVerifyHarness.AgentSubmission.Lib.MpiCoreAux.same_from"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.munch"; "Corelib.Init.Datatypes.cons"; "Corelib.Init.Datatypes.prod"; "Corelib.Init.Datatypes.pair"; "Corelib.Init.Datatypes.nil"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.wmono"; "RocqVerifyHarness.AgentSubmission.Lib.Step.rw_cells"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.cell"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.CB"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C8"; "RocqVerifyHarness.AgentSubmission.LibA.ALazy.al_sb"].


Definition A_CT_MEMCPY_IF : Z := 0xa7cec.

Definition CT_MEMCPY_IF_STACK_B : Z := 48.

Definition ct_memcpy_if_postB (segs : list Segment)
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (D n : Z) (dbs : list byte) (lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms' => exists (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : mem) (dbs' : list byte),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (ret_pc ra) fc None m' (seg_rom segs) /\
    munch [(D, D + n); (bv_unsigned sp - CT_MEMCPY_IF_STACK_B, bv_unsigned sp)] m m' /\
    wmono segs m m' /\ mem_inv segs m' /\ u8arr segs m' D dbs' /\ length dbs' = length dbs /\
    skipn (Z.to_nat n) dbs' = skipn (Z.to_nat n) dbs /\ stk segs m' lo (bv_unsigned sp).

Definition ct_memcpy_if_stmtA (segs : list Segment) (AL : asan_layout) (ENTRY : Z) : Prop := ltac2:(CDefT.buildp (gd_tbl_A_ct_memcpy_if ()) "PCS,P,$0.SpPra,(1.&40.)Psp,(1.&40.)Pgp,(1.&40.)Ptp,(1.&40.)Pt0,(1.&40.)Pt1,(1.&40.)Pt2,(1.&40.)Ps0,(1.&40.)Ps1,(1.&40.)Pa0,(1.&40.)Pa1,(1.&40.)Pa2,(1.&40.)Pa3,(1.&40.)Pa4,(1.&40.)Pa5,(1.&40.)Pa6,(1.&40.)Pa7,(1.&40.)Ps2,(1.&40.)Ps3,(1.&40.)Ps4,(1.&40.)Ps5,(1.&40.)Ps6,(1.&40.)Ps7,(1.&40.)Ps8,(1.&40.)Ps9,(1.&40.)Ps10,(1.&40.)Ps11,(1.&40.)Pt3,(1.&40.)Pt4,(1.&40.)Pt5,(1.&40.)Pt6,(1.&40.)PF,(2.&5.(1.&40.))Pfc,(1.&20.)Pm,P,(1.&40.)(3.(1.&8.))PD,$0.PS1,$0.PS2,$0.Pn,$0.Plo,$0.Pdbs,(4.(1.&8.))Psbs,(4.(1.&8.))P,(5.O3.R8.R7.R2.)P,(6.O3.R9.R7.R2.)P,(7.(8.=R6.)(8.R6.+9<40.))P,(8.R7.(9.(:.(1.&8.)R5.)))P,(8.R8.(9.(:.(1.&8.)R5.)))P,(;.(8.(<.R;.(9.(:.(1.&8.)R6.)))R<.)(8.(<.R<.(9.(:.(1.&8.)R7.)))R;.))P,(;.(=.$0.R;.=)(=.$0.R;.R=.))P,(>.=R>.)P,(;.(=.$0.R<.=)(>.=R>.))P,(>.(<.R10.(9.(:.(1.&8.)R;.)))(?.+2.+40.))P,(>.(<.R10.(9.(:.(1.&8.)R;.)))(?.+2.+40.))P,(10.O3.R13.R>.(11.&40.R33.))P,(8.R?.(12.(11.&40.R34.)$13.))P,(=.$0.(14.(11.&40.R35.)+10.)=)P,(;.(8.(<.R15.(9.(:.(1.&8.)R10.)))(12.(11.&40.R36.)$13.))(8.(11.&40.R36.)R15.))P,(;.(8.(<.R15.(9.(:.(1.&8.)R10.)))(12.(11.&40.R37.)$13.))(8.(11.&40.R37.)R15.))P,(15.O3.R18.)P,(16.O2.)P,(17.O2.R3<.)P,(18.O3.O2.R1;.)P,(19.O3.O2.R3>.R1<.R1;.R18.)P,(19.O3.O2.R3?.R1=.R1;.R19.)P,(1:.R40.R19.(12.(11.&40.R3>.)R19.))P,(=.(1.&40.)R36.(1;.&40.R1>.))P,(=.(1.&40.)R36.(1;.&40.R1>.))P,(=.(1.&40.)R36.(1;.&40.R1>.))P,(=.(1.&40.)R36.(1;.&40.R1>.))(1<.O3.O2.R45.(1=.O3.R44.R43.R42.R41.R3=.R3<.R33.R32.R31.R30.R2?.R2>.R2=.R2<.R2;.R2:.R25.R24.R22.R1?.R1=.R1>.R23.)(1>.(1?.R44.R43.R42.R41.R40.R3?.R3>.R3=.R3<.R3;.R3:.R39.R38.R37.R36.R35.R34.R33.R32.R31.R30.R2?.R2>.R2=.R2<.R2;.R2:.R29.R28.R27.R26.)R25.(1;.&40.O1.)R24.(20.(1.&40.))R23.(21.O3.)))")
(* [comment removed for export] *).

Section Walk.
  Variable AL : asan_layout.
  Hypothesis IMG : asan_img_ok AL.
  Hypothesis ALWF : al_wf AL.
  Local Instance lxi : LxImg asegs AL := lxA_img AL IMG.
  Variable CS : Z -> Prop.
  Hypothesis CSOK : cs_ok AL CS.
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : mem)
            (D S1 n ld ls lo : Z) (dbs0 sbs : list byte).
  Hypothesis Hn : 0 <= n <= 40000.
  Hypothesis Ln : n <= ld /\ n <= ls.
  Hypothesis L0 : Z.of_nat (length dbs0) = ld.
  Hypothesis LS : Z.of_nat (length sbs) = ls.
  Hypothesis DIS : S1 + ls <= D \/ D + ld <= S1.
  Hypothesis DB : 0 < D /\ D + ld < 2^64.
  Hypothesis SB0 : 0 <= S1 /\ S1 + ls < 2^64.
  Hypothesis NZS : n = 0 \/ 0 < S1.
  Hypothesis SPR : 0 <= bv_unsigned sp < 2^64.
  Hypothesis LO0 : 0 <= lo.
  Hypothesis SLO : lo <= bv_unsigned sp - 48.
  Hypothesis SCS : crange CS lo (bv_unsigned sp - lo).
  Hypothesis SX : D + ld <= bv_unsigned sp - 48 \/ bv_unsigned sp <= D.
  Hypothesis SSX : S1 + ls <= bv_unsigned sp - 48 \/ bv_unsigned sp <= S1.
  Hypothesis HS0 : bytes_at asegs m S1 sbs.

  Notation POST := (ct_memcpy_if_postB asegs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc D n dbs0 lo m).
  Notation W := [(D, D + n); (bv_unsigned sp - 48, bv_unsigned sp)].
  Notation SP' := (Z_to_bv 64 (bv_unsigned sp + -48)).
  Notation SB := (Z_to_bv 64 (al_sb AL)).
  Notation DINV mm ds := (u8arr asegs mm D ds /\ Z.of_nat (length ds) = ld /\ same_from (Z.to_nat n) ds dbs0
                          /\ munch W m mm /\ wmono asegs m mm /\ mem_inv asegs mm /\ stk asegs mm lo (bv_unsigned sp + -48)).

  Ltac al_facts :=
    pose proof (cs_ok_sb _ _ CSOK) as SB64;
    pose proof ALWF as ALWF'; unfold al_wf in ALWF';
    pose proof IMG as IMG'; unfold asan_img_ok in IMG'.

  (* [comment removed for export] *)
  Lemma loop_walk : forall (k : nat) (i : Z) (ds : list byte) (mm : mem) (xt1 xs1 xa0 xs2 xs3 xs4 : word) (ed es en : Z),
    Z.to_nat (n - i) = k -> 0 <= i < n -> ed = D + i -> es = S1 + i -> en = n - i ->
    DINV mm ds -> aobj asegs AL CS mm D n -> aobj asegs AL CS mm S1 n ->
    rw_cells asegs mm (bv_unsigned sp + -48) [C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
    evtA asegs AL CS POST (MS (mkR ra SP' gp tp SB xt1 (Z_to_bv 64 1) (Z_to_bv 64 ed) xs1 xa0
        (Z_to_bv 64 D) (Z_to_bv 64 S1) (Z_to_bv 64 es) (Z_to_bv 64 en) (Z_to_bv 64 ed) (Z_to_bv 64 ed) (Z_to_bv 64 D)
        xs2 xs3 xs4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 1) (Z_to_bv 64 1) (Z_to_bv 64 es) (Z_to_bv 64 ed))
      F (Z_to_bv 64 0xa7d50) fc None mm (seg_rom asegs))
(* [comment removed for export] *).
  Proof.
    induction k as [|k IH]; intros i ds mm xt1 xs1 xa0 xs2 xs3 xs4 ed es en Hk Hi Ed Es En
      (HX & LX & FX & MU & WM & MI & ST) OD OS FR; [exfalso; xlia Hk Hi|].
    pose proof (cs_ok_sb _ _ CSOK) as SB64.
    pose proof (bytes_at_transport asegs _ m mm S1 sbs HS0 MU ltac:(cbn [disjoint_from]; xlia LS DIS Ln SSX)) as HS.
    assert (PS1 : 0 < S1) by (clear - NZS Hi; lia).
    lx_run_tac (PLAN [0xa7d50] [(0xa7d70, DJoin); (0xa7d98, DJoin); (0xa7dc0, DJoin)] 160%N); lx_tree.
    all: lx_gc.
    all: lx_rn_munch MU'; lx_rn_wmono WM'; lx_rn_mi MI'; lx_rn_stk ST'.
    all: match goal with K : u8arr _ _ D _ |- _ => rename K into HX' end.
    - (* [comment removed for export] *)
      lx_rn_rw (bv_unsigned sp + -48) FR'. lx_rn_aobj D OD'. lx_rn_aobj S1 OS'.
      match goal with K : 0 <= en + _ |- _ => rename K into BR end.
      eapply (IH (i + 1)); [xlia Hk Hi | xlia Hi BR En | xlia Ed | xlia Es | xlia En
        | refine (conj HX' (conj _ (conj _ (conj MU' (conj WM' (conj MI' ST'))))));
          [ eapply upd_bytes1_length_Z; [exact LX | apply length_le1 | xlia Ed Hi LX Ln]
          | eapply same_from_upd_bytes1; [exact FX | apply length_le1 | xlia Ed Hi | xlia LX Ln] ]
        | exact OD' | exact OS' | exact FR' ].
    - (* [comment removed for export] *)
      match goal with K : 0 <= _ + (- en + _) |- _ => rename K into BR | K : 0 <= - en + _ |- _ => rename K into BR end.
      lx_post.
      all: lazymatch goal with
           | |- u8arr _ _ _ _ => exact HX'
           | |- @eq nat (length _) _ => rewrite upd_bytes_length; [xlia LX L0 | rewrite length_le1; xlia Ed Hi LX Ln]
           | |- skipn _ _ = skipn _ _ => apply same_from_skipn; [eapply same_from_upd_bytes1; [exact FX | apply length_le1 | xlia Ed Hi | xlia LX Ln]
                                                               | rewrite upd_bytes_length; [xlia LX L0 | rewrite length_le1; xlia Ed Hi LX Ln]]
           | |- _ => first [reflexivity | assumption]
           end.
    all: match goal with |- ?g => idtac "LOOP-LEFT:" g end.
  Qed.
End Walk.

Lemma A_ct_memcpy_if_spec : forall AL, asan_img_ok AL -> ct_memcpy_if_stmtA asegs AL A_CT_MEMCPY_IF.
Proof.
  intros AL IMG. unfold ct_memcpy_if_stmtA, A_CT_MEMCPY_IF.
  intros until sbs. intros HX HS Hn LX LS DIS S2C NZD NZS DT ST1 ST LO SPA SX SSX MI ALWF CSOK ABS OD OS SCS -> -> -> ->.
  unfold CT_MEMCPY_IF_STACK_B in *.
  pose (lxi := lxA_img AL IMG).
  pose proof (cs_ok_sb _ _ CSOK) as SB64.
  pose proof (u8arr_bound _ _ _ _ HX) as DB. pose proof (bytes_at_bound _ _ _ _ HS) as SB0.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn [Z.pow Z.of_N Pos.pow] in SPR.
  pose proof (proj1 ST) as LO0.
  pose proof (munch_refl [(D, D + n); (bv_unsigned sp - 48, bv_unsigned sp)] m) as MU.
  pose proof (wmono_refl asegs m) as WM.
  carve_frame 48%nat ST.
  destruct S2C as [-> | ->]; pose proof NZS as NZS'; destruct NZS' as [N0 | PS1].
  (* [comment removed for export] *)
  all: lx_run_tac (PLAN [0xa7d50] [] 60%N); lx_tree.
  all: lx_gc.
  all: lazymatch goal with
       | |- evtA _ _ _ _ (MS _ _ (ret_pc _) _ _ _ _) =>
           lx_post; first [eassumption | reflexivity | idtac]
       | |- _ =>
           match goal with K : 0 <= ?nn + -1 |- _ => constr_eq nn n; rename K into BR end;
           lx_rn_munch MU'; lx_rn_wmono WM'; lx_rn_mi MI'; lx_rn_stk ST'; lx_rn_rw (bv_unsigned sp + -48) FR';
           match goal with K : u8arr _ _ ?dd _ |- _ => constr_eq dd D; rename K into HX' end;
           lx_rn_aobj D OD'; lx_rn_aobj S1 OS';
           eapply (loop_walk AL IMG ALWF CS CSOK) with (S1 := S1) (sbs := sbs) (k := Z.to_nat (n - 0)) (i := 0) (ld := Z.of_nat (length dbs)) (ls := Z.of_nat (length sbs));
           first [ eassumption | reflexivity | xlia Hn | xlia LX LS | xlia DT NZD | xlia SB0 ST1 | xlia BR | xlia0
                 | exact (conj HX' (conj eq_refl (conj (same_from_refl _ _) (conj MU' (conj WM' (conj MI' ST')))))) ]
       end.
  all: match goal with |- ?g => idtac "MAIN-LEFT:" g end.
Qed.
