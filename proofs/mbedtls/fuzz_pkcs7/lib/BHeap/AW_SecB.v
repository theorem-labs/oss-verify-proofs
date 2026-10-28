(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Arr Asn1Aux CellsX Bytes.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import AModel.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import AW_Unwind AW_Unwind2 AW_MmapFixed AW_MallocA AW_AllocA AW_DepotA AW_DepotB AW_Poison AW_AllocB.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import AW_ClassId AW_Large.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import A_stringA.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BLX Require Import LxA.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LXBW Require Import LxAWTac.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import ATac.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.AHeap Require Import ACeil.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Import OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.LxhSyntax. #[local] Instance lxh_tab : OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.lx_hints := OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.lxh_parse "P0067f7b16223750b 0 4 0 1 41 1 47 1 48 1P0121d1761ae94095 1 2 16 2 0 1 77 1 16 2 1 1 76 1 2 78 1 79 1P018a4398fbad2fae 1 1 16 2 1 1 76 1 5 60 1 69 1 70 1 77 1 78 16P01c800546e101e9f 1 2 16 2 0 1 77 1 16 2 1 1 76 1 2 78 1 79 1P021a182aa7d1b003 1 1 16 2 1 1 76 1 5 60 1 69 1 70 1 77 1 78 16P021d887e6c49c67b 0 6 0 1 69 1 70 1 71 1 76 1 77 1P02859465801178c4 1 1 16 2 1 1 76 1 5 60 1 69 1 70 1 77 1 78 16P02e81d98fd968179 1 2 16 2 0 1 77 1 16 2 1 1 76 1 2 78 1 79 1P0359d335976e7913 0 6 1 1 69 1 70 1 72 1 76 1 77 1P03aec266bc0ec1d5 0 2 0 1 72 1P05218136dc82307e 0 2 0 1 72 1P0823ad059a122043 0 2 0 1 46 1P083d4abe099ee895 0 6 0 1 69 1 70 1 71 1 76 1 77 1P09b6be303abcd23b 1 2 16 4 1 1 48 1 51 1 53 1 16 8 33 1 38 1 42 1 43 1 44 1 49 1 50 1 52 1 2 54 1 55 1P0a50aa8aa8170f55 0 4 0 1 68 1 75 1 76 1P0ac425db1980f536 0 2 0 1 46 1P0e1e4230aa969420 0 2 0 1 47 1P0f0e9bea14290075 0 6 0 1 69 1 70 1 71 1 76 1 77 1P116e2b142bcc2467 0 2 0 1 57 1P11c7af5730c4cc3f 0 6 1 16 60 16 69 16 70 16 76 16 77 16P12778220fed04221 1 2 16 2 0 1 77 1 16 2 1 1 76 1 2 78 1 79 1P134ac0bd55b6d43f 1 1 16 2 1 1 76 1 5 60 1 69 1 70 1 77 1 78 16P160365b437bcee83 0 2 0 1 23 1P167f8242d24ad421 0 6 1 1 69 1 70 1 71 1 76 1 77 1P17b5f20854ea4966 1 2 16 4 1 1 48 1 51 1 53 1 16 8 33 1 38 1 42 1 43 1 44 1 49 1 50 1 52 1 2 54 1 55 1P183326484e4b1281 0 4 0 1 41 1 47 1 48 1P198900a15eb9fbeb 1 1 16 2 1 1 76 1 5 60 1 69 1 70 1 77 1 78 16P19d1f03badf3a7f6 0 6 0 1 69 1 70 1 71 1 76 1 77 1P1a2959b683b50d46 1 1 16 2 1 1 48 1 5 37 1 42 1 43 1 49 1 50 16P1a5d99d4a1b96cac 0 6 1 1 69 1 70 1 71 1 76 1 77 1P1a8ecff0a68e8685 0 4 0 1 41 1 47 1 48 1P1b1ae83888f7aa20 1 2 16 4 1 1 48 1 51 1 53 1 16 8 33 1 38 1 42 1 43 1 44 1 49 1 50 1 52 1 2 54 1 55 1P1bda96d28ad00352 0 4 0 1 41 1 47 1 48 1P1bf0456dda921e17 1 2 16 2 0 1 77 1 16 2 1 1 76 1 2 78 1 79 1P1e2fec0e074f2be9 0 4 0 1 68 1 75 1 76 1P1e8fdd0ba0f3833e 0 2 0 1 57 1P1f4eafa5ae236f49 0 4 0 1 41 1 47 1 48 1P202ca7b48b4db99d 1 1 16 2 1 1 76 1 5 60 1 69 1 70 1 77 1 78 16P20c54ee17b583090 0 4 0 1 68 1 75 1 76 1P20d4dc5b91d15468 0 6 0 1 69 1 70 1 71 1 76 1 77 1P239f3ec7a5a89d29 1 2 16 2 0 1 77 1 16 2 1 1 76 1 2 78 1 79 1P23a7545d59aa7be4 1 1 16 2 1 1 48 1 5 37 1 42 1 43 1 49 1 50 16P2415486e50897b48 0 6 0 1 69 1 70 1 71 1 76 1 77 1P247510f32c9529e5 0 6 1 16 60 16 69 16 70 16 76 16 77 16P2531c70ae45bb5f9 0 4 0 1 41 1 47 1 48 1P2595ec908284bbcc 0 6 1 1 69 1 70 1 72 1 76 1 77 1P264fd292197085f6 0 4 0 1 68 1 75 1 76 1P2765e49aa6964dd9 1 2 16 2 0 1 77 1 16 2 1 1 76 1 2 78 1 79 1P2850223d14c644e6 0 2 0 1 48 1P2a0957adebf472b6 0 2 0 1 47 1P2a2134947eb6afba 1 2 16 2 0 1 77 1 16 2 1 1 76 1 2 78 1 79 1P2a2c28ce5a8a04c6 0 4 0 1 41 1 47 1 48 1P2bb406842dc7ba99 0 4 0 1 41 1 47 1 48 1P2bbe7ace34d50301 0 4 0 1 41 1 47 1 48 1P2bf0046e26574ad4 0 6 0 1 69 1 70 1 71 1 76 1 77 1P2ec46ae8301e7ac4 1 2 16 2 0 1 77 1 16 2 1 1 76 1 2 78 1 79 1P2fab536e41036d50 0 2 0 1 47 1P300a052cdb885bcb 1 1 16 2 1 1 76 1 5 60 1 69 1 70 1 77 1 78 16P32dd4d3a1727f785 1 1 16 2 1 1 76 1 5 60 1 69 1 70 1 77 1 78 16P36a50aea5266c578 1 1 16 2 1 1 76 1 5 60 1 69 1 70 1 77 1 78 16P37b8939da7b48415 1 1 16 2 1 1 76 1 5 60 1 69 1 70 1 77 1 78 16P3806505ac2631aa6 0 4 0 1 68 1 75 1 76 1P385b077a124b728c 0 6 0 1 69 1 70 1 71 1 76 1 77 1P39107ad8dce545b8 0 4 0 1 41 1 47 1 48 1P3915907583a4f480 0 6 1 1 69 1 70 1 71 1 76 1 77 1P39600838e38834aa 0 2 0 1 27 1P397cfdeaae418034 0 4 0 1 68 1 75 1 76 1P3a424b083f65e759 1 2 16 2 0 1 49 1 16 2 1 1 48 1 2 50 1 51 1P3ab729498ae28158 0 4 0 1 41 1 47 1 48 1P3b5e4c071f985499 0 4 0 1 68 1 75 1 76 1P3bed7361cc4141d0 0 2 0 1 48 1P3bf568504a2c9f04 1 2 16 2 0 1 77 1 16 2 1 1 76 1 2 78 1 79 1P3cba3bafd99b246b 0 6 1 1 69 1 70 1 71 1 76 1 77 1P3cf4258ca126275e 1 2 16 4 1 1 48 1 51 1 53 1 16 8 33 1 38 1 42 1 43 1 44 1 49 1 50 1 52 1 2 54 1 55 1P3f3f80c49668f182 1 2 16 2 0 1 49 1 16 2 1 1 48 1 2 50 1 51 1P3f5530cac96289dd 0 4 0 1 41 1 47 1 48 1P3f69a5c1bc1bea9f 0 7 0 1 44 1 56 1 60 1 61 1 64 1 65 1N028a861f607906b1N090f3cab74064af5N09fb2c6840b2123aN0ab65a8450735850N0ae01dac0ed15557N0e4d4cb8b016eb65N0fd767ae1648c773N10568bc5d718575fN120c8dc31b3093f3N19812cae3fdfab45N1db8d4849d3ee204N26d0cbb2f38bcf9aN2a9a100ddfb34c62N2bc9bce08cc6589dN2e83dff44a263eadN2f6f90a0079a98f2N30e7cb2d23a7c043N32bfbfec1aa2e485N3a6b73f5ee962e46N3f7b1b0dea635a26"%lxh.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import LiaOrc. (* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= orc_lia. (* [comment removed for export] *)
Local Ltac dlia ::= orc_dlia. (* [comment removed for export] *)
Local Ltac plia ::= orc_plia. (* [comment removed for export] *)
Local Ltac clear_disj ::= fc_clear_disj. (* [comment removed for export] *)
Local Ltac prune_disj ::= fc_prune_disj. (* [comment removed for export] *)
Ltac2 gd_tbl_AW_SecB () : Init.string Init.list := ["Corelib.Numbers.BinNums.Z"; "Corelib.Init.Logic.and"; "Stdlib.ZArith.BinInt.Z.le"; "Stdlib.ZArith.BinInt.Z.lt"; "Stdlib.ZArith.BinInt.Z.pow"; "Corelib.Init.Logic.eq"; "Corelib.Init.Datatypes.bool"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.from_primary"; "Corelib.Init.Datatypes.false"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.nfix"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.rz_size"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.needed2"; "Stdlib.ZArith.BinInt.Z.add"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.rounded"; "Stdlib.ZArith.BinInt.Z.modulo"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.machine_state"; "Corelib.Init.Logic.ex"; "stdpp.bitvector.definitions.bv"; "Corelib.Init.Datatypes.option"; "Stdlib.ZArith.BinInt.Z.mul"; "Stdlib.ZArith.BinInt.Z.div"; "RocqVerifyHarness.AgentSubmission.Lib.MState.MS"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.mkR"; "stdpp.bitvector.definitions.Z_to_bv"; "Stdlib.ZArith.BinInt.Z.sub"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_Poison.A_POISON"; "Corelib.Init.Datatypes.None"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.seg_rom"; "RocqVerifyHarness.AgentSubmission.B.AImg.asegs"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.munch"; "Corelib.Init.Datatypes.cons"; "Corelib.Init.Datatypes.prod"; "Corelib.Init.Datatypes.pair"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.wmono"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.mem_inv"; "RocqVerifyHarness.AgentSubmission.Lib.Step.rw_cells"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.cell"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C1"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C2"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C4"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C8"; "Stdlib.ZArith.BinInt.Z.lor"; "Corelib.Init.Datatypes.nil"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.stk"; "LinuxProcessSemantics.Riscv.Prelude.bvmap"; "Corelib.Init.Datatypes.list"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_Large.map_size"; "RocqVerifyHarness.AgentSubmission.AHeap.ACeil.ACEIL"; "Corelib.Init.Logic.or"; "RocqVerifyHarness.AgentSubmission.LibA.ALazy.crange"; "RocqVerifyHarness.AgentSubmission.Lib.Step.ro_cells"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.A_INSTANCE"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_Large.large_statics"; "RocqVerifyHarness.AgentSubmission.LibA.AEvtA.evtA"; "ARUN_1.SecB.smidA_post"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_AllocA.allocA_statics"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_AllocA.allocA_frame"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_Unwind2.A_TP"; "ARUN_1.SecB.sst_post"; "Stdlib.ZArith.BinInt.Z.shiftr"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_AllocB.pgv"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_Poison.poison_statics"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_AllocB.A_GOT_FLAGS"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.A_FLAGS"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_AllocB.A_FL_PPART"; "ARUN_1.SecB.spg_post"; "Stdlib.ZArith.BinInt.Z.min"; "Corelib.Init.Logic.not"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.CB"; "Stdlib.ZArith.BinInt.Z.to_nat"; "Corelib.Lists.ListDef.repeat"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_AllocB.fin_statics"; "ARUN_1.SecB.sfill_post"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_AllocB.fin_post"].

Section ARUN_1. Context {hAR : arun}.
Local Ltac2 Set LiaOrc.tbl := fun () => "00H0?L177981682.9   L24365080574.14L27540287649.7 L32100125626.10L32468341922.10L32601025391.13L3825125325.9  L38597169108.9 L41422282358.9 L41853556197.2 L41855999094.9 L4552497949.15 L46278950601.11L47019361263.9 L53451850460.9 L55216968871.9 L57219050999.9 L59314873579.9 L59509546328.12L60020930573.15L61030987380.5 L63374621462.6 L63969262006.9 L65119302229.9 00000500800@00C00O00R00^00j00m01201801@01C01O01U01X01a01n02102402502802;02GS1n1HS1nS1n1H2H0S1nS1n2RB2RL2H0S1nS1n2FP2RB2LOS1n2FP2RB2LOS1nS1n1GS1n2LOS1n1L2H5S1nS1n2FP2RB2LOS1n2FPS1nS1n2FP2LOS1n2FP2RB1L1HS1nS1nSS1nS1nS1n2FP2RB2LO". (* [comment removed for export] *)
#[using="Type"] Lemma sec_sizes : ltac2:(CDefT.buildp (gd_tbl_AW_SecB ()) "Pn,$0.P,(1.(2.=R1.)(3.R1.(4.+2.+20.)))P,(5.$6.(7.R2.)$8.)(1.(2.+?<01.R3.)(1.(5.$0.(9.R3.)R3.)(1.(5.$0.(:.R3.)+800.)(1.(5.$0.(;.R3.)(<.(=.R3.)+1000.))(1.(1.(2.R3.(=.R3.))(2.(=.R3.)(<.R3.+7.)))(1.(5.$0.(>.(=.R3.)+8.)=)(1.(3.+10000.(;.R3.))(2.(;.R3.)(<.R3.+1007.)))))))))")
(* [comment removed for export] *).
Proof.
  try lx_hide ASB.  (* [comment removed for export] *)
  intros n NB FP. pose proof FP as FP0.
  unfold from_primary, kMaxSize in FP. apply Z.leb_gt in FP.
  assert (RB : Z.max n 8 <= rounded n <= Z.max n 8 + 7 /\ rounded n mod 8 = 0).
  { unfold rounded, round_up. pose proof (Z.div_mod (Z.max n 8 + 8 - 1) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (Z.max n 8 + 8 - 1) 8 ltac:(lia)).
    split; [lia|]. apply Z_mod_mult. }
  assert (LO : 0xfc01 <= n).
  { destruct (Z_lt_ge_dec n 0xfc01) as [L|G]; [exfalso| clear - G; lia].
    unfold needed in FP. pose proof (rz_log_bound n) as RL.
    assert (rz_size n <= 1024).
    { unfold rz_size. assert (rz_log n <= 6).
      { unfold rz_log. destruct (Z.ltb_spec n 49); [lia|]. destruct (Z.ltb_spec n 97); [lia|]. destruct (Z.ltb_spec n 449); [lia|].
        destruct (Z.ltb_spec n 0xf81); [lia|]. destruct (Z.ltb_spec n 0x3f01); [lia|]. destruct (Z.ltb_spec n 0x7e01); [lia|].
        destruct (Z.ltb_spec n 0xfc01); lia. }
      assert (2 ^ rz_log n <= 2 ^ 6) by (apply Z.pow_le_mono_r; lia). change (2^6) with 64 in *. lia. }
    lia. }
  pose proof (rz_log_7 n LO) as R7. assert (RZ : rz_size n = 2048) by (unfold rz_size; rewrite R7; reflexivity).
  unfold needed2. rewrite FP0.
  unfold needed in *. rewrite RZ in *. unfold nfix. repeat split; lia.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

Section SecB.
  Variable AL : asan_layout.
  Hypothesis IMG : asan_img_ok AL.
  Hypothesis ALWF : al_wf AL.
  Variable CS : Z -> Prop.
  Hypothesis CSOK : cs_ok AL CS.
  Local Instance lxi : LxImg asegs AL := lxA_img AL IMG.   (* [comment removed for export] *)
  Hypothesis ASB : al_sb AL = 0x7fff8000.

  Ltac facts :=
    pose proof (cs_ok_sb _ _ CSOK) as SB64;
    pose proof ALWF as ALWF'; unfold al_wf in ALWF';
    pose proof IMG as IMG'; unfold asan_img_ok in IMG'.

  (* [comment removed for export] *)
  Definition smidA_post (SP : Z) (gp tp x5 x6 x7 x13 x14 x15 x16 x17 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
      (n AB STK T TID id lo ms : Z) (b0 : byte) (b1 : Z) (W : list (Z * Z)) (m0 : mem) : machine_state -> Prop := ltac2:(CDefT.buildp (gd_tbl_AW_SecB ()) "Lms',$?.(10.P,(11.&40.)(12.(11.&8.))Lm',P,(11.&40.)(12.(11.&8.))ZUB,$0.(<.O;.(:.O<.))ZCHB,$0.(<.R1.-10.)Zr8,$0.(13.(14.(<.(9.O<.)+7.)+8.)+8.)(1.(5.$?.R5.(15.(16.(17.&40.+47?18.)(17.&40.(<.O1=.-80.))O1<.O1;.O1:.O19.O18.(17.&40.(18.O5.+1000.))(17.&40.(9.O<.))(17.&40.O;.)(17.&40.(:.O<.))(17.&40.+?:.)O17.O16.O15.O14.O13.(17.&40.O;.)(17.&40.(;.O<.))(17.&40.R3.)(17.&40.R2.)(17.&40.(<.R3.R1.))(17.&40.O:.)(17.&40.(13.O8.(4.+2.+20.)))(17.&40.(<.(<.R3.(9.O<.))+7.))(17.&40.O9.)(17.&40.+1.)O12.O11.O10.O?.)O>.(17.&40.$19.)O=.(1:.(11.&40.))R4.(1;.$1<.)))(1.(1=.(1>.(1?.$0.$0.)(20.$0.$0.O6.(<.O1=.-80.))(1>.(1?.$0.$0.)(20.$0.$0.(<.R2.+8.)(<.R2.+10.))O2.))O1.R4.)(1.(21.$1<.O1.R4.)(1.(22.$1<.R4.)(1.(23.$1<.R4.R2.(1>.$24.(25.O4.)(1>.$24.(25.(17.&8.O3.))(1>.$24.(26.(17.&40.=))(1>.$24.(27.(17.&40.(9.O<.)))(1>.$24.(28.(17.&40.(29.(13.O8.(4.+2.+20.))O7.)))(2:.$24.)))))))(2;.$1<.R4.O6.(<.O1=.-80.))))))))")
(* [comment removed for export] *).

  Local Ltac2 Set LiaOrc.tbl := fun () => "00j0?L1295065869.83 L1330356182.3  L13446183429.87L15615277569.88L16591383828.89L17210349934.4 L17796680992.4 L18926556999.2 L18926759668.85L18928824262.83L18928852294.83L18930958230.84L19820322693.84L23808467220.89L25047882783.4 L25161402295.92L2591582825.87 L2875865527.92 L30507153921.88L30507154048.89L30509336091.95L32388375596.2 L33697794450.84L38797450130.84L40167153149.4 L42981755964.86L44239365629.4 L44530640592.86L45914037331.88L47133446560.87L47945201638.92L48193359348.89L49698585326.88L49713057094.83L51464947643.95L51464947848.13L53520049434.92L53534876991.84L53615921234.92L552445949.92  L55420003072.92L5622942713.2  L5629760784.3  L5629782459.95 L56481855939.84L5819018891.8  L58695594748.86L59047877439.95L59308628433.13L59579114288.86L60747865560.84L60864533053.87L61028859847.3 L61035084364.4 L62801389984.92L63654440446.90L63831025920.1 L8887191019.83 00000Y00c01501_03503603C03F03\04204A04W04X05n06:06D06S06h07V08D09209809B09W09_09`09h0:>0:S0:i0:j0;T0;o0<X0=U0>A0>T0>g0?10?C0?b0?j0@40A<0A=0AX0BP0CX0D@0DO0Da0E30E60E;0E<0FK0FN0FOS3hAR1n2AB1a2ms3EAB2A03NLO2RZ3N2E3RNB3MSZS2AB1a3EABS3hAR2SP1n2AB1a2msS3hAR2SP1n2lo2SB1a2ms2A03SB03SB15LOIMG3SPLS3hAR2SP1n2AB3TID2id2lo1a2ms3EAB2A05LOIMG3SPL3NLO2RZ3N2E3RNB3MSZ2DA3AB02HB5Ha_st5Hl_stSS2AB1a3EAB2A0S1aS3hAR2SP1n2AB1a2UB3CHBS3hAR2SP1n2AB1a2UB3CHBS3hAR2SP1n1a2msS3hAR2SP1n2AB1a2UB3CHBFS3hAR2SP1n2AB3TID2id2lo1a2ms3EAB2A05LOIMG3SPL3NLO2RZ3N2E3RNB3MSZ2DA3AB02HB5Ha_st5Hl_stS1n3N2B1H2H0S3hAR1a2msS3hAR2SP1n1a2msS3hAR2AL1a2ms2A04IMG'S3hAR2SP1n2AB2lo1a2ms2A05LOIMG3SPL3N2B3AB03ABHS3hAR2SP1n2AB2lo1a2ms2A05LOIMG3SPL3N2B3AB03ABHS3hAR2SP1n2AB2lo1a2ms2A05LOIMG3SPL3N2B3AB03ABHS1n2ABS3hAR1a2msS3hAR2AL1a2ms2A04IMG'S1n1a2DAFS1n1a2DAS3hAR2SP1n2id1a2ms3IDBS3hAR2SP1n2AB1a2ms2HBS3hAR2SP1n2id1a2ms3IDBFS3hAR2SP1n2lo2SB1a2ms2A03SB03SB15LOIMG3SPLS3hAR2SP1n2AB1a2ms2HB5Ha_stS3hAR1n2AB1a2ms3EAB2A03NLO2RZ3N2E3RNB3MSZS3hAR2SP1n2AB2lo1a2ms2A05LOIMG3SPL3NLO3NFX2RZ3N2E3RNB3AB03ABHS3hAR1n2AB1a2ms2NB3EAB2A03ACE3NFX2RZ3N2B3MSZS3hAR2AL1a2ms5ALWF'S3hAR2AL1a2ms5ALWF'S3hAR1a2msS3hAR2AL1a2ms4IMG'S3hAR1n1a2ms2A03NLO3N2E3RNB3MSZS2id3IDBS1n2NB3N2BS3hAR2SP1n2AB2lo1a2ms2NB3EAB2A03EMS3ACE5LOIMG3SPL3N2E3N2B3MSZ2DA3AB03ABHFS3hAR1n2AB1a2ms3EAB3ACE3MSZS3hAR2SP1n3TID2lo1a2ms2A04TIDB5LOIMG3SPL3NLO3N2E3RNB3MSZS3hAR2SP1n2AB2lo1a2ms3EAB2A05LOIMG3SPL3NLO2RZ3N2E3RNB3N2B3MSZ2DA3AB03ABHS3hAR1n2AB2SB1a2ms3EAB3APT3N2B3MSZ2K12K2S3hAR2SP1n1a2msS3hAR2AL1a2ms4IMG'S3hAR2SP1n2AB1a2msS1aS1n1aFS3hAR2SP1n2AB3TID2id2lo1a2ms3EAB2A05LOIMG3SPL3NLO2RZ3N2E3RNB3MSZ2HB5Ha_st5Hl_stS1nF". (* [comment removed for export] *)
  #[using="IMG ALWF CSOK"] Lemma sec_midA : ltac2:(CDefT.buildp (gd_tbl_AW_SecB ()) "Pgp,(11.&40.)Ptp,(11.&40.)Px5,(11.&40.)Px6,(11.&40.)Px7,(11.&40.)Px11,(11.&40.)Px12,(11.&40.)Px13,(11.&40.)Px14,(11.&40.)Px15,(11.&40.)Px16,(11.&40.)Px17,(11.&40.)Pt3,(11.&40.)Pt4,(11.&40.)Pt5,(11.&40.)Pt6,(11.&40.)Pb0,(11.&8.)Pw8,(11.&40.)PSP,$0.Pn,$0.PAB,$0.PSTK,$0.PT,$0.PTID,$0.Pid,$0.Plo,$0.Pb1,$0.PSB,$0.PPA,$0.Pa,$0.Pms,$0.Pncks,$0.PF,(2<.&5.(11.&40.))Pfc,(11.&20.)Pm0,P,(11.&40.)(12.(11.&8.))Pm,P,(11.&40.)(12.(11.&8.))PW,(2=.(1?.$0.$0.))ZUB,$0.(<.R11.(:.R12.))ZCHB,$0.(<.R1.-10.)P,(1.(2.=R14.)(3.R14.(4.+2.+20.)))P,(5.$6.(7.R15.)$8.)P,(5.$0.R15.(<.R<.+1000.))P,(5.$0.(>.R=.+1000.)=)P,(2.+65?000.R>.)P,(5.$0.R>.(2>.(;.R19.)))P,(2.(<.R10.R?.)(2?.VhAR,))P,(2.=R13.)P,(2.(<.(<.R14.(4.+2.+25.))+1000.)(2?.VhAR,))P,(30.(2.(<.R13.R12.)R15.)(2.(<.(<.R15.(4.+2.+25.))+1000.)R13.))P,(1.(2.=R1:.)(3.R1:.(4.+2.+1?.)))P,(1.(2.=R1:.)(3.R1:.(4.+2.+1?.)))P,(1.(2.=R19.)(3.R19.+100.))P,(31.VCS,R17.R16.)P,(23.$1<.R12.R?.(1>.$24.(25.R25.)(1>.$24.(25.(17.&8.R1;.))(1>.$24.(26.(17.&40.=))(1>.$24.(27.(17.&40.(9.R22.)))(1>.$24.(28.R24.)(2:.$24.)))))))P,(23.$1<.R13.R19.(1>.$24.(28.(17.&40.R19.))(1>.$24.(28.(17.&40.R18.))(1>.$24.(28.(17.&40.(;.R23.)))(1>.$24.(28.(17.&40.R17.))(2:.$24.))))))P,(32.$1<.R14.(<.$33.+20.)(1>.$24.(28.(17.&40.R1<.))(2:.$24.)))P,(34.R15.R1<.)P,(2;.$1<.R16.R20.(<.R27.-80.))P,(2.(2?.VhAR,)R21.)P,(2.R22.(18.R29.+200.))P,(2.R2:.(4.+2.+3>.))P,(5.$0.(>.R2;.+10.)=)P,(31.VCS,R25.(18.R2<.R25.))P,(1=.(1>.(1?.$0.$0.)(20.$0.$0.R26.(<.R2=.-80.))(1>.(1?.$0.$0.)(20.$0.$0.(<.R19.+8.)(<.R19.+10.))R1;.))R1=.R1<.)P,(21.$1<.R1>.R1=.)P,(22.$1<.R1>.)(35.$1<.VAL,VCS,(36.R30.R42.R41.R40.R3?.R3>.R3;.R3:.R39.R38.R37.R36.R35.R34.R33.R22.R21.R2?.R2>.R2=.R2<.R2;.R2:.R29.R24.R32.R28.R1>.R20.)(15.(16.(17.&40.+47>40.)(17.&40.(<.R30.-80.))R42.R41.R40.R3?.R3>.(17.&40.=)(17.&40.(9.R2?.))(17.&40.R2:.)R3=.R3<.R3;.R3:.R39.R38.R37.(17.&40.R2>.)(17.&40.(;.R2?.))(17.&40.R1=.)(17.&40.R1<.)(17.&40.$33.)(17.&40.R2=.)(17.&40.(13.R2;.(4.+2.+20.)))(17.&40.(<.R1=.(9.R2?.)))(17.&40.R2<.)(17.&40.+1.)R36.R35.R34.R33.)R22.(17.&40.+47>40.)R21.(1:.(11.&40.))R1?.(1;.$1<.)))")
(* [comment removed for export] *).
  Proof.
    try lx_hide ASB.  (* [comment removed for export] *)
    intros gp tp x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 t3 t4 t5 t6 b0 w8 SP n AB STK T TID id lo b1 SB PA a ms ncks F fc m0 m W UB CHB
      NB FP EAB AAL A0 EMS ACE SB0 SB1 APT TIDB IDB B1B BCS HDR HH SBC LS ST LOIMG SPL SPH SPA SCS MU WM MI.
    facts. destruct LS as (LS1 & LS2 & LS3). clear LS2 LS3. unfold A_INSTANCE, A_POISON in *.
    change (1074072 + 32) with 1074104 in SBC. change (1074072 + 64) with 1074136 in LS1.
    pose proof (sec_sizes n NB FP) as (NLO & NFX & RZ & N2E & RNB & RN8 & N2B).
    assert (MSZ : needed2 n + 4096 <= ms < needed2 n + 8192 /\ ms mod 4096 = 0).
    { rewrite EMS. unfold map_size. pose proof (Z.div_mod (needed2 n + 4095) 4096 ltac:(lia)). pose proof (Z.mod_pos_bound (needed2 n + 4095) 4096 ltac:(lia)).
      split; [clear - H H0 N2B; lia|]. rewrite Z.add_mod, Z_mod_mult, Z.add_0_l by lia. reflexivity. }
    assert (HUB : UB = AB + rz_size n) by reflexivity. subst CHB UB.
    pose proof (Z.div_mod a 4096 ltac:(lia)) as DA. rewrite AAL, Z.add_0_r in DA.
    assert (AB0 : 0x660000 <= AB) by (clear - EAB A0; lia). assert (ABH : AB + needed2 n <= ACEIL) by (clear - EAB ACE MSZ; lia).
    (* [comment removed for export] *)
    pose proof (munch_refl [(AB + rz_size n + -16 + 8, AB + rz_size n + -16 + 16)] m) as MU2.
    zstep. zstep. zstep. rewrite (Z.mod_small id 4294967296) by (clear - IDB; lia). change 4294967296 with (2^32). zstep.
    clear MU2.
    (* [comment removed for export] *)
    zstep.
    assert (TAIL : forall (y11 : word) (mc : mem),
      mc = write_to_mem m (wa (AB + rz_size n + -16 + 8)) (le8 (Z_to_bv 64 (Z.lor (TID * 2^32) id))) \/ True ->
      rw_cells asegs mc (AB + rz_size n + -16) [C1 b0; C1 (Z_to_bv 8 b1); C2 (Z_to_bv 64 0); C4 (Z_to_bv 64 (nfix n)); C8 (Z_to_bv 64 (Z.lor (TID * 2^32) id))] ->
      rw_cells asegs mc a [C8 (Z_to_bv 64 a); C8 (Z_to_bv 64 ms); C8 (Z_to_bv 64 (needed2 n)); C8 (Z_to_bv 64 ncks)] ->
      ro_cells asegs mc 1074136 [C8 (Z_to_bv 64 4096); C8 (Z_to_bv 64 PA); C8 (Z_to_bv 64 PA)] ->
      stk asegs mc lo (SP + -128) -> munch ((lo, SP + -128) :: (AB + rz_size n + -16 + 8, AB + rz_size n + -16 + 16) :: W) m0 mc ->
      wmono asegs m0 mc -> mem_inv asegs mc ->
      evtA asegs AL CS (smidA_post SP gp tp x5 x6 x7 x13 x14 x15 x16 x17 t3 t4 t5 t6 F fc n AB STK T TID id lo ms b0 b1 W m0)
        (MS (mkR (Z_to_bv 64 0x47e40) (Z_to_bv 64 (SP + -128)) gp tp x5 x6 x7 (Z_to_bv 64 0) (Z_to_bv 64 (nfix n))
                   (Z_to_bv 64 SB) y11 x12 x13 x14 x15 x16 x17
                   (Z_to_bv 64 AB) (Z_to_bv 64 (needed2 n)) (Z_to_bv 64 (AB + rz_size n)) (Z_to_bv 64 (AB + rz_size n + -16)) (Z_to_bv 64 1074072) (Z_to_bv 64 STK)
                   (Z_to_bv 64 (TID * 2^32)) (Z_to_bv 64 (AB + rz_size n + nfix n)) (Z_to_bv 64 T) (Z_to_bv 64 1) t3 t4 t5 t6)
               F (Z_to_bv 64 0x47eac) fc None mc (seg_rom asegs))).
    { intros y11 mc _ HDR' HH' LS1' ST' MU' WM' MI'.
      (* [comment removed for export] *)
      zstep. zstep. zstep.
      replace (Z.land 4095 AB) with 0.
      2:{ rewrite Z.land_comm. change 4095 with (Z.ones 12). rewrite Z.land_ones by (clear - EAB A0; lia). change (2^12) with 4096.
          rewrite EAB. clear - DA. symmetry. rewrite Z.add_mod, Z_mod_same_full by lia. rewrite DA at 1. rewrite Z.mul_comm, Z_mod_mult. reflexivity. }
      zstep. zstep. zstep.
      zstep. replace (AB - 4096) with a by (clear - EAB; lia).
      zstep.
      (* [comment removed for export] *)
      zstep. zstep. zstep.
      rewrite (land_align12 (needed2 n + 4095)) by (clear - N2B NB; lia).
      replace ((needed2 n + 4095) / 4096 * 4096) with (ms - 4096) by (rewrite EMS; unfold map_size; clear; lia).
      zstep.
      (* [comment removed for export] *)
      zstep. zstep.
      rewrite (land_align3 (AB + rz_size n + nfix n + 7)) by (clear - EAB A0 ACE MSZ N2B RZ NFX NB; lia).
      replace ((AB + rz_size n + nfix n + 7) / 8 * 8) with (AB + rz_size n + (nfix n + 7) / 8 * 8).
      2:{ rewrite EAB, RZ. clear - DA. pose proof (Z.div_mod (nfix n + 7) 8 ltac:(lia)).
          replace (a + 4096 + 2048 + nfix n + 7) with ((nfix n + 7) + (512 * (a / 4096) + 768) * 8) by lia.
          rewrite Z.div_add by lia. lia. }
      zstep. zstep. zstep. zstep.
      replace (AB + rz_size n - AB) with (rz_size n) by (clear; lia).
      apply evtA_done. unfold smidA_post. exists mc.
      split; [reflexivity|]. split; [exact MU'|]. split; [exact WM'|]. split; [exact MI'|]. split; [exact HDR'| exact ST']. }
    zstep. zstep. if_cases K1; zify_cond K1.
    - eapply TAIL; try eassumption. right; exact I.
    - zstep. zstep. zstep. zstep. if_cases K2; zify_cond K2.
      + eapply TAIL; try eassumption. right; exact I.
      + exfalso. clear - K1 K2 APT EAB MSZ N2B ACE. lia.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0060?L30508875696.54L51011430787.4 L55073523856.54L57247863376.5 L61030844230.53L63374621462.5400000M00Y01L01[01h025S3hAR1n2AB2ms3AB03ABH3MSZ3N2BS1n2AB2ms2r8S3hAR1n2AB2ms2r83AB03ABH3MSZ3NLO3NFX2RZ3N2E3RNB3R8BS1n2NB3NFX1H2H0S3hAR1n2AB2UBS3hAR1n2AB2UB". (* [comment removed for export] *)
  #[using="IMG ALWF CSOK"] Lemma sec_midB : ltac2:(CDefT.buildp (gd_tbl_AW_SecB ()) "Pgp,(11.&40.)Ptp,(11.&40.)Px5,(11.&40.)Px6,(11.&40.)Px7,(11.&40.)Pxa0,(11.&40.)Pxa1,(11.&40.)Pxa2,(11.&40.)Px13,(11.&40.)Px14,(11.&40.)Px15,(11.&40.)Px16,(11.&40.)Px17,(11.&40.)Px28,(11.&40.)Px29,(11.&40.)Px30,(11.&40.)Px31,(11.&40.)PSP,$0.Pn,$0.PAB,$0.PSTK,$0.PT,$0.PTID,$0.Pms,$0.Ps9v,$0.PCHBw,(11.&40.)PF,(2<.&5.(11.&40.))Pfc,(11.&20.)Pm,P,(11.&40.)(12.(11.&8.))ZUB,$0.(<.R:.(:.R;.))Zr8,$0.(13.(14.(<.(9.R<.)+7.)+8.)+8.)P,(1.(2.=R=.)(3.R=.(4.+2.+20.)))P,(5.$6.(7.R>.)$8.)P,(2.+65?000.R>.)P,(2.(<.R?.(18.R;.+1000.))(2?.VhAR,))P,(2.(<.(;.R11.)+1000.)R<.)P,(22.$1<.R8.)(35.$1<.VAL,VCS,Lms',$?.(5.$?.R1.(15.(16.(17.&40.+47?2<.)(17.&40.(<.R15.-80.))R26.R25.R24.R23.R22.(17.&40.(18.R?.+1000.))(17.&40.(9.R14.))(17.&40.(<.R9.R8.))(17.&40.(18.(<.R13.(18.R?.+1000.))(<.R9.R8.)))(17.&40.+?:.)R1>.R1=.R1<.R1;.R1:.(17.&40.R13.)(17.&40.(;.R14.))(17.&40.R9.)R=.(17.&40.(<.R9.R8.))(17.&40.R12.)(17.&40.(13.R10.(4.+2.+20.)))(17.&40.R>.)(17.&40.R11.)(17.&40.+1.)R19.R18.R17.R16.)R<.(17.&40.$19.)R;.(1:.(11.&40.))R:.(1;.$1<.)))(15.(16.(17.&40.+47?18.)(17.&40.(<.R14.-80.))R25.R24.R23.R22.R21.(17.&40.(18.R>.+1000.))(17.&40.(9.R13.))R20.R1?.R1>.R1=.R1<.R1;.R1:.R19.(17.&40.R12.)(17.&40.(;.R13.))(17.&40.R8.)R<.(17.&40.(<.R8.R7.))(17.&40.R11.)(17.&40.(13.R?.(4.+2.+20.)))(17.&40.R=.)(17.&40.R10.)(17.&40.+1.)R18.R17.R16.R15.)R;.(17.&40.+47?18.)R:.(1:.(11.&40.))R9.(1;.$1<.)))")
(* [comment removed for export] *).
  Proof.
    try lx_hide ASB.  (* [comment removed for export] *)
    intros gp tp x5 x6 x7 xa0 xa1 xa2 x13 x14 x15 x16 x17 x28 x29 x30 x31 SP n AB STK T TID ms s9v CHBw F fc m UB r8 NB FP AB0 ABH MSZ MI.
    facts. unfold A_POISON in *.
    pose proof (sec_sizes n NB FP) as (NLO & NFX & RZ & N2E & RNB & RN8 & N2B).
    assert (R8B : nfix n <= r8 <= nfix n + 7) by (subst r8; pose proof (Z.div_mod (nfix n + 7) 8 ltac:(lia)); pose proof (Z.mod_pos_bound (nfix n + 7) 8 ltac:(lia)); clear - H H0 NFX NB; lia).
    subst UB.
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep. zstep.
    match goal with |- context [Z_to_bv 64 ?e] =>
      match e with (AB - _ + (ms - 4096)) => replace e with (AB + (ms - 4096) - (AB + rz_size n + r8)) by (clear; lia) | _ => fail end end
    || idtac.
    apply evtA_done. repeat f_equal; try reflexivity; try (apply bv_eq; reflexivity); try (f_equal; clear; lia).
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0060?L39929975614.52L43935890344.53L54548667936.3 L59308633593.6 L61030844230.51L63370229784.5200000B00\00f01<01E01NS1n2NB3NLO3NFX3RNBS1n2NB3NLO3NFX3RNB3DNF3MNFS1n2NB3NFXS1n3NLO3NFX3DNF3MNF2KZS1n2AB2UBS1n2AB2UB". (* [comment removed for export] *)
  #[using="IMG ALWF CSOK"] Lemma sec_midC : ltac2:(CDefT.buildp (gd_tbl_AW_SecB ()) "Pgp,(11.&40.)Ptp,(11.&40.)Px5,(11.&40.)Px6,(11.&40.)Px7,(11.&40.)Pxa0,(11.&40.)Pxa1,(11.&40.)Pxa2,(11.&40.)Px13,(11.&40.)Px14,(11.&40.)Px15,(11.&40.)Px16,(11.&40.)Px17,(11.&40.)Px28,(11.&40.)Px29,(11.&40.)Px30,(11.&40.)Px31,(11.&40.)PSP,$0.Pn,$0.PAB,$0.PSTK,$0.PT,$0.PTID,$0.Ps0v,$0.Ps6v,$0.Ps9v,$0.PCHBw,(11.&40.)PF,(2<.&5.(11.&40.))Pfc,(11.&20.)Pm,P,(11.&40.)(12.(11.&8.))ZUB,$0.(<.R;.(:.R<.))P,(1.(2.=R=.)(3.R=.(4.+2.+20.)))P,(5.$6.(7.R>.)$8.)P,(22.$1<.R4.)(35.$1<.VAL,VCS,Lms',$?.(5.$?.R1.(15.(16.(17.&40.+47?4<.)(17.&40.(<.R12.-80.))R23.R22.R21.R20.R1?.(17.&40.R<.)(17.&40.(9.R11.))(17.&40.R5.)(17.&40.(13.(14.(9.R11.)+8.)+8.))(17.&40.=)R1;.R1:.R19.R18.R17.(17.&40.R10.)(17.&40.(;.R11.))(17.&40.R5.)R9.(17.&40.(13.(14.(9.R11.)+8.)+8.))(17.&40.R?.)(17.&40.(13.R=.(4.+2.+20.)))(17.&40.R:.)(17.&40.R>.)(17.&40.+1.)R16.R15.R14.R13.)R8.(17.&40.$19.)R7.(1:.(11.&40.))R6.(1;.$1<.)))(15.(16.(17.&40.+47?2<.)(17.&40.(<.R11.-80.))R22.R21.R20.R1?.R1>.(17.&40.R;.)(17.&40.(9.R10.))R1=.R1<.R1;.R1:.R19.R18.R17.R16.(17.&40.R?.)(17.&40.(;.R10.))(17.&40.R4.)R8.(17.&40.R:.)(17.&40.R>.)(17.&40.(13.R<.(4.+2.+20.)))(17.&40.R9.)(17.&40.R=.)(17.&40.+1.)R15.R14.R13.R12.)R7.(17.&40.+47?2<.)R6.(1:.(11.&40.))R5.(1;.$1<.)))")
(* [comment removed for export] *).
  Proof.
    try lx_hide ASB.  (* [comment removed for export] *)
    intros gp tp x5 x6 x7 xa0 xa1 xa2 x13 x14 x15 x16 x17 x28 x29 x30 x31 SP n AB STK T TID s0v s6v s9v CHBw F fc m UB NB FP MI.
    facts. unfold A_POISON in *.
    pose proof (sec_sizes n NB FP) as (NLO & NFX & RZ & N2E & RNB & RN8 & N2B).
    pose proof (Z.div_mod (nfix n) 8 ltac:(lia)) as DNF. pose proof (Z.mod_pos_bound (nfix n) 8 ltac:(lia)) as MNF.
    subst UB.
    (* [comment removed for export] *)
    zstep. zstep. zstep. rewrite (land_align3_48 (nfix n)) by (clear - NFX NB; lia).
    zstep. if_cases KZ; zify_cond KZ. { exfalso. clear - KZ NLO NFX DNF MNF. lia. }
    zstep. zstep. zstep. zstep.
    apply evtA_done. reflexivity.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Definition sst_post (SP : Z) (gp tp x8 x25 x28 t4 t5 t6 x22 : word) (F : bvmap 5 word) (fc : bv 32)
      (n AB STK T TID lo fill : Z) (W : list (Z * Z)) (m0 : mem) : machine_state -> Prop :=
    fun ms' => exists (x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 : word) (j0 j1 j2 j4 : word) (m' : mem),
      let UB := AB + rz_size n in let CHB := UB + -16 in
      ms' = MS (mkR x1 (Z_to_bv 64 (SP + -128)) gp tp x5 x6 x7 x8 (Z_to_bv 64 (nfix n))
                   (Z_to_bv 64 fill) x11 x12 x13 x14 x15 x16 x17
                   (Z_to_bv 64 AB) (Z_to_bv 64 (needed2 n)) (Z_to_bv 64 UB) (Z_to_bv 64 CHB) x22 (Z_to_bv 64 STK)
                   (Z_to_bv 64 (TID * 2^32)) x25 (Z_to_bv 64 T) (Z_to_bv 64 1) x28 t4 t5 t6)
               F (Z_to_bv 64 (if fill =? 0 then 0x48174 else 0x48140)) fc None m' (seg_rom asegs)
      /\ munch ((lo, SP + -128) :: (T + 2800, T + 2824) :: (T + 2904, T + 2912) :: W) m0 m' /\ wmono asegs m0 m' /\ mem_inv asegs m'
      /\ rw_cells asegs m' (T + 2800) [C8 j0; C8 j1; C8 j2] /\ rw_cells asegs m' (T + 2904) [C8 j4]
      /\ stk asegs m' lo (SP + -128).

  Local Ltac2 Set LiaOrc.tbl := fun () => "00I0@L10740496679.1  L11985143081.1  L15020562828.1  L19780390460.2  L29875947688.126L30129840862.1  L30726521175.2  L3091479790.1   L32992608088.2  L37964339962.1  L38335416942.1  L38555397984.1  L38797873596.2  L44421293205.1  L44625906644.1  L45394964183.2  L47497358871.83 L48959321276.2  L51609867272.83 L53525265815.83 L54509413076.1  L63064043092.1  L65561650839.83 L7142785895.83  L9627626300.2   00000400800<00=00J00K00L00M00W00[00_00`00a00e00f00g01801901J01[01_01`02102G02HS2SPS2SPS2SPFS3hAR2SP1n2ABFFFS4fill3H18S2SPS2SPFFS2SPFFS3hAR2SP1n2lo3SPLFS3hAR2SP1n2lo3SPLS3hAR2SP1n2lo3SPLS2SPFS3hAR2SP1n2lo3SPLS3hAR2SP1n4fill2FB3H18F". (* [comment removed for export] *)
  #[using="IMG ALWF CSOK"] Lemma sec_st : ltac2:(CDefT.buildp (gd_tbl_AW_SecB ()) "Pgp,(11.&40.)Ptp,(11.&40.)Px1,(11.&40.)Px5,(11.&40.)Px6,(11.&40.)Px7,(11.&40.)Px8,(11.&40.)Px10,(11.&40.)Px11,(11.&40.)Px12,(11.&40.)Px13,(11.&40.)Px14,(11.&40.)Px15,(11.&40.)Px16,(11.&40.)Px17,(11.&40.)Px22,(11.&40.)Px25,(11.&40.)Px28,(11.&40.)Pt4,(11.&40.)Pt5,(11.&40.)Pt6,(11.&40.)Pj0,(11.&40.)Pj1,(11.&40.)Pj2,(11.&40.)Pj4,(11.&40.)Pqra,(11.&40.)Pq0,(11.&40.)Pq1,(11.&40.)Pq2,(11.&40.)Pq3,(11.&40.)Pq4,(11.&40.)Pq5,(11.&40.)Pq6,(11.&40.)Pq7,(11.&40.)Pq8,(11.&40.)Pq9,(11.&40.)Pq10,(11.&40.)Pq11,(11.&40.)PSP,$0.Pn,$0.PAB,$0.PSTK,$0.PT,$0.PCTX,$0.PTID,$0.Plo,$0.Pfill,$0.PF,(2<.&5.(11.&40.))Pfc,(11.&20.)Pm0,P,(11.&40.)(12.(11.&8.))Pm,P,(11.&40.)(12.(11.&8.))Pfr0,(2=.(11.&8.))PW,(2=.(1?.$0.$0.))ZUB,$0.(<.R=.(:.R>.))ZCHB,$0.(<.R1.-10.)P,(1.(2.=R10.)(3.R10.(4.+2.+20.)))P,(5.$6.(7.R11.)$8.)P,(1.(2.=R;.)(2.R;.+1.))P,(37.R8.R10.R?.)P,(2.+65?000.R10.)P,(2.(<.R11.+10000.)(2?.VhAR,))P,(1.(2.+1000.R13.)(30.(2.(<.R13.+1000.)+10000.)(2.+65?000.R13.)))P,(2.(<.R14.+1000.)(2?.VhAR,))P,(31.VCS,R14.+10000.)P,(31.VCS,R16.+1000.)P,(30.(2.(<.R17.+1000.)R16.)(2.(<.R16.+10000.)R17.))P,(23.$1<.R10.(<.R18.+:?0.)(1>.$24.(28.R2=.)(1>.$24.(28.R2<.)(1>.$24.(28.R2;.)(2:.$24.)))))P,(23.$1<.R11.(<.R19.+;58.)(1>.$24.(28.R2;.)(2:.$24.)))P,(38.R12.R1>.R11.R16.R2;.R2:.R29.R28.R27.R26.R25.R24.R23.R22.R21.R20.R1?.)P,(2;.$1<.R13.R18.(<.R1?.-80.))P,(2.(2?.VhAR,)R19.)P,(2.R1:.(18.R21.+200.))P,(2.R22.(4.+2.+3>.))P,(5.$0.(>.R23.+10.)=)P,(31.VCS,R1=.(18.R24.R1=.))P,(1=.(1>.(1?.$0.$0.)(20.$0.$0.R1>.(<.R25.-80.))(1>.(1?.$0.$0.)(20.$0.$0.(<.R21.+:?0.)(<.R21.+;08.))(1>.(1?.$0.$0.)(20.$0.$0.(<.R21.+;58.)(<.R21.+;60.))R17.)))R1:.R19.)P,(21.$1<.R1;.R1:.)P,(22.$1<.R1;.)P,(5.(11.&40.)R4=.(17.&40.$39.))(35.$1<.VAL,VCS,(3:.R29.R4?.R4>.R49.R3?.R3>.R3=.R3<.R3;.R40.R20.R1?.R28.R27.R26.R25.R23.R22.R21.R1;.R1>.)(15.(16.R4=.(17.&40.(<.R29.-80.))R4?.R4>.R4<.R4;.R4:.R49.(17.&40.(9.R28.))R48.R47.R46.R45.R44.R43.R42.R41.(17.&40.R27.)(17.&40.(;.R28.))(17.&40.R1:.)(17.&40.R19.)R40.(17.&40.R26.)(17.&40.(13.R23.(4.+2.+20.)))R3?.(17.&40.R25.)(17.&40.+1.)R3>.R3=.R3<.R3;.)R20.(17.&40.+47?>0.)R1?.(1:.(11.&40.))R1=.(1;.$1<.)))")
(* [comment removed for export] *).
  Proof.
    try lx_hide ASB.  (* [comment removed for export] *)
    intros gp tp x1 x5 x6 x7 x8 x10 x11 x12 x13 x14 x15 x16 x17 x22 x25 x28 t4 t5 t6 j0 j1 j2 j4 qra q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11
      SP n AB STK T CTX TID lo fill F fc m0 m fr0 W UB CHB
      NB FP FB (INI & RSS & DBR & LT1 & LT2a & LT2b & RZC & MXU & TSD & TPC & TSA & CTH) C0 C1 T0 T1 CTXCS TCS TCSEP STH ST4 AFR
      ST LOIMG SPL SPH SPA SCS MU WM MI ->.
    facts. unfold A_ASAN_INITED, A_RSS_CELL, A_DEBRUIJN, A_LOGTBL1, A_LOGTBL2, A_MINRZ, A_MAXUSER, A_INSTANCE,
      A_TSD_INITED, A_TSD_PTR, A_TSD_ARR, A_TP in *.
    pose proof (sec_sizes n NB FP) as (NLO & NFX & RZ & N2E & RNB & RN8 & N2B).
    subst CHB UB. unfold allocA_frame in AFR.
    change (1074072 + 3624) with 1077696 in RZC. change (1074072 + 3616) with 1077688 in MXU.
    (* [comment removed for export] *)
    lx_hide MU. lx_hide WM.
    pose proof (munch_refl [(lo, SP + -128); (T + 2800, T + 2824); (T + 2904, T + 2912)] m) as MU1. pose proof (wmono_refl asegs m) as WM1.
    lx_aceil.
    lx_run (PLAN [0x48140; 0x48174] [] 80%N); lx_unhide; try clear LXlen; lx_stk_grow_to lo (SP + -128);
      lazymatch goal with MUl : munch _ m ?mx, WMl : wmono _ m _ |- _ =>
        apply evtA_done; unfold sst_post;
        first [ match goal with K : 0 <= - fill + 0 |- _ => rewrite (proj2 (Z.eqb_eq fill 0)) by (clear -K FB; lia) end
              | match goal with K : 0 <= fill + -1 |- _ => rewrite (proj2 (Z.eqb_neq fill 0)) by (clear -K; lia) end
              | rewrite (proj2 (Z.eqb_eq fill 0)) by lx_arith
              | rewrite (proj2 (Z.eqb_neq fill 0)) by lx_arith ];
        lx_exs; lx_ands;
        [ lx_mseq
        | lx_munch MU MUl
        | lx_wmono WM WMl
        | assumption
        | match goal with |- rw_cells _ _ ?a _ => eassumption end
        | match goal with |- rw_cells _ _ ?a _ => eassumption end
        | assumption ] end.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition spg_post (SP : Z) (gp tp x8 x25 x28 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
      (n AB STK T TID lo : Z) (W : list (Z * Z)) (pgb : byte) (m0 : mem) : machine_state -> Prop := ltac2:(CDefT.buildp (gd_tbl_AW_SecB ()) "Lms',$?.(10.(11.&40.)Lx1,(11.&40.)(10.(11.&40.)Lx5,(11.&40.)(10.(11.&40.)Lx6,(11.&40.)(10.(11.&40.)Lx7,(11.&40.)(10.(11.&40.)Lx10,(11.&40.)(10.(11.&40.)Lx11,(11.&40.)(10.(11.&40.)Lx12,(11.&40.)(10.(11.&40.)Lx13,(11.&40.)(10.(11.&40.)Lx14,(11.&40.)(10.(11.&40.)Lx15,(11.&40.)(10.(11.&40.)Lx16,(11.&40.)(10.(11.&40.)Lx17,(11.&40.)(10.(11.&40.)Lx22,(11.&40.)(10.P,(11.&40.)(12.(11.&8.))Lm',P,(11.&40.)(12.(11.&8.))ZUB,$0.(<.O8.(:.O9.))ZCHB,$0.(<.R1.-10.)Zrd,$0.(13.(14.(9.O9.)+8.)+8.)ZPGS,$0.(<.+7???8000.(3;.(<.R3.R1.)+3.))(1.(5.$?.R13.(15.(16.R12.(17.&40.(<.O14.-80.))O13.O12.R11.R10.R?.O11.(17.&40.(9.O9.))R>.R=.R<.R;.R:.R9.R8.R7.(17.&40.O8.)(17.&40.(;.O9.))(17.&40.R4.)(17.&40.R3.)R6.(17.&40.O7.)(17.&40.(13.O5.(4.+2.+20.)))O10.(17.&40.O6.)(17.&40.+1.)O?.O>.O=.O<.)O;.(17.&40.+47?>0.)O:.(1:.(11.&40.))R5.(1;.$1<.)))(1.(1=.(1>.(1?.$0.$0.)(20.$0.$0.O4.(<.O14.-80.))(1>.(1?.$0.$0.)(20.$0.$0.R1.(<.R1.+1.))O3.))O1.R5.)(1.(21.$1<.O1.R5.)(1.(22.$1<.R5.)(1.(23.$1<.R5.R1.(1>.$24.(25.(3<.O9.O2.))(2:.$24.)))(2;.$1<.R5.O4.(<.O14.-80.)))))))))))))))))))))")
(* [comment removed for export] *).

  Local Ltac2 Set LiaOrc.tbl := fun () => "01c0?L11138871060.91L11145742652.83L12502279885.10L12604415106.81L13265630597.83L13275677884.83L13279090888.81L13313927314.83L13666404454.84L15395562245.83L17765151508.89L17930621016.83L19182823186.83L19586266388.81L20071043032.83L21798222111.81L22518122871.88L22577265597.88L23251451895.88L23928002224.88L2491586324.94 L27134647468.84L2843556961.88 L28921179156.84L29057133935.78L29265817255.88L29448992590.92L30299332372.88L31394778632.81L31563693970.83L31736297728.92L33494084254.4 L34150196914.86L34265358118.81L35033948432.7 L3507171090.83 L35250499860.87L36193165570.2 L36721662623.81L36888738214.81L3824716112.3  L39017728265.88L39188636933.0 L39425713901.88L39930025786.3 L39930703233.91L39932041151.82L40228640085.0 L41148359740.83L41400680896.88L41553783782.84L43278729349.83L43465718732.88L43855564994.81L43935888693.82L43938083252.2 L44222736994.93L44743351468.84L45410778629.83L46097988652.84L46230795540.85L47296240642.3 L47298995385.88L49698585326.94L49705053714.78L50966866708.92L51178147495.88L51240883336.81L52064999472.84L5299353416.81 L53516929332.84L53519718666.88L53520131109.81L53522110849.84L53522114239.83L54412534036.90L55007345708.84L55676403476.95L55866193017.88L5641312914.83 L57400919124.82L5811897951.81 L58371358466.84L58775187672.83L59308628433.12L59308628566.12L59308628695.13L59579460628.84L60500005819.84L60501295036.83L61024598737.80L61028779636.82L61030858054.80L63036727106.81L63368316589.83L63370229784.81L63374621462.81L64147162642.83L64775989122.84L64781239060.84L65164610392.83L65840083814.81L66715365384.81L66904651835.84L67259945748.93L67805785736.81L68364611860.86L7258948116.83 L7781730322.83 L8926825899.91 L8929152288.87 L8929152550.89 L8929152679.88 L8929161758.86 L9911535506.83 00000100200Q00`00a00b00i01P01b01c01d02602]02^03003103D03S03Z03[03\03f04;04H04]04d05105205905`05m06306@06A06T06^06_06b06c06d06n06o07007?07I07a08908:08;08<08N08O08j09909f09m0:=0:d0:e0;L0;M0;N0<40<J0<Z0<[0<n0=50=60=I0=V0=f0>60>I0>\0>]0>g0>h0>i0?30?40?50?60?H0?U0@:0@b0@o0A00A10A>0AY0B40BC0B^0Bk0CF0Cm0Cn0Co0DA0DB0DU0DV0DW0Dj0Dk0Dl0E60E70E80E90E:0E;0EEFFS3hAR1n2AB3AB03RNG4RZSB3NFB3N2BS3hAR2AL1n4IMG'FFS3hAR1nS3hAR2AL1n2AB3AB04IMG'4RZSB3NFB3DNF3MNFS3hAR2AL1n2AB4IMG'FFS3hAR2AL1n2AB4IMG'S3hAR2AL1n2AB3AB04IMG'4RZSB3NFB3DNF3MNFFS3hAR2AL1n2AB4IMG'FS3hAR2AL1n4IMG'3NFBS3hAR2AL1n4IMG'S3hAR1nFFS3hAR1n2ABS3hAR1n2AB3NFB3N2B2KES3hAR2SP1n2ABS3hAR2SP1n2AB2lo1W2HBS3hAR1nS3hAR2SP1n2ABFS3hAR1nS3hAR2AL1n2AB3AB04IMG'4RZSB3NFB3DNF3MNFS3hAR2SP1n2ABS1n2KES3hAR2SP1n2ABFS1n1H2H02H12H24RZSBS3hAR1n2ABFS1nFFS1n3DNF2KEFSS3hAR2AL1n4IMG'S1n2NB3NFBS3hAR2SP1n2AB2NB3AB03NFBS3hAR2SP1n2AB2NB3AB03NFBSFFS3hAR2AL1n2AB4IMG'FS3hAR1n2AB4RZSB3NFB3DNF3MNFS3hAR2AL1n4IMG'S3hAR2SP1n2AB2lo2NB3AB05LOIMG3SPL3NFB3DNF3MNFS1n3MNFS3hAR2SP1n2AB2HBS3hAR2AL1n2AB3AB04IMG'4RZSB3NFB3DNF3MNFFS3hAR2AL1n2AB3AB04IMG'4RZSB3NFB3DNF3MNFFFS3hAR2AL3ASB1n2AB3AB04RZSB3NFB3DNF3MNFS3hAR2SP1n2AB2HB5Ha_stS3hAR2SP1n2AB2HBFS3hAR2AL1n4IMG'3NFBS3hAR1nFS3hAR2AL1n4IMG'3NFBS3hAR2SP1n2ABS3hAR2AL1n5ALWF'S3hAR2AL1n5ALWF'S3hAR2AL1n2AB5ALWF'S3hAR2AL1n2AB5ALWF'FS3hAR1n2ABFFS3hAR1n2ABFFFS3hAR2AL1n2AB4IMG'S1n2AB3NFB2K2S3hAR1n2AB3AB03RNG4RZSB3NFB3N2B2KE2K3S3hAR1n2AB3AB03RNG4RZSB3NFB3N2B2KE2KL2K4S3hAR2SP1n2ABFFS3hAR2SP1n2ABS3hAR2SP1n2AB2UB3CHB2rd3PGSS3hAR2SP1n2AB2UB3CHB2rd3PGSS3hAR2AL1n4IMG'S3hAR2SP1n2AB2UB3CHB2rd3PGSS3hAR2SP1n2ABS3hAR2SP1n2AB2UB3CHB2rd3PGSS3hAR2AL1n2AB3AB04IMG'4RZSB3NFB3DNF3MNFFFS3hAR2AL1n2AB4IMG'FS3hAR2AL1n4IMG'3NFBFFS3hAR2AL1n4IMG'3NFBFFS3hAR1n2ABFFFFFS3hAR1n2AB". (* [comment removed for export] *)
  #[using="IMG ALWF CSOK ASB"] Lemma sec_pg : ltac2:(CDefT.buildp (gd_tbl_AW_SecB ()) "Pgp,(11.&40.)Ptp,(11.&40.)Px1,(11.&40.)Px5,(11.&40.)Px6,(11.&40.)Px7,(11.&40.)Px8,(11.&40.)Px10,(11.&40.)Px11,(11.&40.)Px12,(11.&40.)Px13,(11.&40.)Px14,(11.&40.)Px15,(11.&40.)Px16,(11.&40.)Px17,(11.&40.)Px25,(11.&40.)Px28,(11.&40.)Pt4,(11.&40.)Pt5,(11.&40.)Pt6,(11.&40.)Ppgb,(11.&8.)PSP,$0.Pn,$0.PAB,$0.PSTK,$0.PT,$0.PTID,$0.Plo,$0.PF,(2<.&5.(11.&40.))Pfc,(11.&20.)Pm0,P,(11.&40.)(12.(11.&8.))Pm,P,(11.&40.)(12.(11.&8.))PW,(2=.(1?.$0.$0.))ZUB,$0.(<.R:.(:.R;.))ZCHB,$0.(<.R1.-10.)Zrd,$0.(13.(14.(9.R=.)+8.)+8.)ZPGS,$0.(<.+7???8000.(3;.(<.R3.R1.)+3.))P,(1.(2.=R?.)(3.R?.(4.+2.+20.)))P,(2.+65?000.R?.)P,(5.$0.(>.R10.+10.)=)P,(30.(2.(<.R11.(;.R12.))+7???8000.)(1.(2.+10007???8000.R11.)(2.(<.R11.(;.R12.))(2?.VhAR,))))P,(31.VCS,R12.(;.R13.))P,(23.$1<.R;.R6.(1>.$24.(25.R16.)(2:.$24.)))P,(3=.R<.)P,(32.$1<.R=.$3>.(1>.$24.(28.(17.&40.$3?.))(2:.$24.)))P,(32.$1<.R>.$40.(1>.$24.(25.(17.&8.+1.))(2:.$24.)))P,(2;.$1<.R?.R13.(<.R19.-80.))P,(2.(2?.VhAR,)R14.)P,(2.R15.(18.R1;.+200.))P,(2.R1<.(4.+2.+3>.))P,(5.$0.(>.R1=.+10.)=)P,(31.VCS,R18.(18.R1>.R18.))P,(1=.(1>.(1?.$0.$0.)(20.$0.$0.R19.(<.R1?.-80.))(1>.(1?.$0.$0.)(20.$0.$0.R10.(<.R10.+1.))R14.))R16.R15.)P,(21.$1<.R17.R16.)P,(22.$1<.R17.)(35.$1<.VAL,VCS,(41.R22.R37.R36.R31.R28.R27.R26.R25.R24.R1;.R1:.R21.R20.R1?.R1>.R1=.R1<.R17.R23.R19.)(15.(16.R35.(17.&40.(<.R22.-80.))R37.R36.R34.R33.R32.R31.(17.&40.(9.R21.))R30.R2?.R2>.R2=.R2<.R2;.R2:.R29.(17.&40.R20.)(17.&40.(;.R21.))(17.&40.R16.)(17.&40.R15.)(17.&40.R14.)(17.&40.R1?.)(17.&40.(13.R1=.(4.+2.+20.)))R28.(17.&40.R1>.)(17.&40.+1.)R27.R26.R25.R24.)R1;.(17.&40.+47?4<.)R1:.(1:.(11.&40.))R18.(1;.$1<.)))")
(* [comment removed for export] *).
  Proof.
    intros gp tp x1 x5 x6 x7 x8 x10 x11 x12 x13 x14 x15 x16 x17 x25 x28 t4 t5 t6 pgb SP n AB STK T TID lo F fc m0 m W UB CHB rd PGS
      NB AB0 ABAL RNG ACS PGC PS GOTFL PPART ST LOIMG SPL SPH SPA SCS MU WM MI.
    facts. pose proof PS as (CP & G1 & SB & G2 & MB & G3 & ME & G4 & HE & G5 & RM & G6 & CT).
    unfold A_CANPOISON, A_GOT_SB, A_SBCELL, A_GOT_MIDBEG, A_MIDBEG, A_GOT_MIDEND, A_MIDEND, A_GOT_HIGHEND, A_HIGHEND,
      A_GOT_RMEMSET, A_RMEMSET, A_GOT_CFLAGS, A_CFLAGS, A_CF_CSMT, A_MUSL_MEMSET, A_GOT_FLAGS, A_FLAGS, A_FL_PPART in *.
    pose proof (rz_size_bound n) as RZSB.
    assert (NFB : 1 <= nfix n <= Z.max n 1) by (unfold nfix; clear - NB; lia).
    assert (N2B : nfix n + rz_size n <= needed2 n /\ needed2 n <= needed2 n /\ (nfix n / 8 * 8 + 8 <= needed2 n - rz_size n \/ nfix n mod 8 = 0)).
    { unfold needed2. destruct (from_primary n); unfold needed, rounded, round_up in *;
      pose proof (Z.div_mod (Z.max n 8 + 8 - 1) 8 ltac:(lia)); pose proof (Z.mod_pos_bound (Z.max n 8 + 8 - 1) 8 ltac:(lia));
      pose proof (Z.div_mod (nfix n) 8 ltac:(lia)); pose proof (Z.mod_pos_bound (nfix n) 8 ltac:(lia));
      unfold nfix in *; clear - H H0 H1 H2 NB RZSB; lia. }
    assert (HUB : UB = AB + rz_size n) by reflexivity. assert (HRD : rd = nfix n / 8 * 8) by reflexivity.
    assert (HPGS : PGS = 0x7fff8000 + Z.shiftr (UB + rd) 3) by reflexivity. subst CHB PGS. subst UB rd.
    pose proof (Z.div_mod (nfix n) 8 ltac:(lia)) as DNF. pose proof (Z.mod_pos_bound (nfix n) 8 ltac:(lia)) as MNF.
    Ltac pg_leaf :=
      apply evtA_done; unfold spg_post; do 13 eexists; eexists; split; [reflexivity|];
      split; [eassumption|]; split; [eassumption|]; split; [eassumption|]; split; [| assumption].
    (* [comment removed for export] *)
    zstep. if_cases KE; zify_cond KE.
    - pg_leaf. unfold pgv. assert (E0 : nfix n mod 8 = 0) by (clear - KE DNF; lia). rewrite (proj2 (Z.eqb_eq (nfix n mod 8) 0) E0). exact PGC.
    - (* [comment removed for export] *)
      assert (E1 : nfix n mod 8 <> 0) by (clear - KE DNF MNF; lia). assert (PGV : pgv n pgb = Z_to_bv 8 (nfix n mod 8)) by (unfold pgv; rewrite (proj2 (Z.eqb_neq (nfix n mod 8) 0) E1); reflexivity).
      zstep. zstep. zstep. zstep. zstep. zstep.
      change (Z.b2z (0 <? bv_unsigned (sxb (Z_to_bv 8 1)))) with 1.
      zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep.
      change ((Z.b2z (2147450880 <? 2147450879) + -1) mod 18446744073709551616) with 18446744073709551615.
      change (Z.land 18446744073709551615 2147450879) with 2147450879.
      assert (TAILPG : forall (y11 y12 y13 y14 y15 y16 y17 : word) (mc : mem), mc = m ->
        evtA asegs AL CS (spg_post SP gp tp x8 x25 x28 t4 t5 t6 F fc n AB STK T TID lo W pgb m0)
          (MS (mkR (Z_to_bv 64 0x47f54) (Z_to_bv 64 (SP + -128)) gp tp x5 x6 x7 x8 (Z_to_bv 64 (nfix n))
                   (Z_to_bv 64 0x7fff8000) y11 y12 y13 y14 y15 y16 y17
                   (Z_to_bv 64 AB) (Z_to_bv 64 (needed2 n)) (Z_to_bv 64 (AB + rz_size n)) (Z_to_bv 64 (AB + rz_size n + -16))
                   (Z_to_bv 64 (AB + rz_size n + nfix n / 8 * 8)) (Z_to_bv 64 STK)
                   (Z_to_bv 64 (TID * 2^32)) x25 (Z_to_bv 64 T) (Z_to_bv 64 1) x28 t4 t5 t6)
               F (Z_to_bv 64 0x47fbc) fc None mc (seg_rom asegs))).
      { intros y11 y12 y13 y14 y15 y16 y17 mc ->.
        (* [comment removed for export] *)
        zstep. zstep. zstep. zstep.
        rewrite (Z.mod_small (AB + rz_size n + nfix n / 8 * 8) 18446744073709551616) by (clear - RNG AB0 RZSB NFB N2B DNF MNF; lia).
        zstep. zstep. zstep.
        change 18446744073709551615 with (Z.ones 64). rewrite Z.land_ones by (clear; lia). rewrite (Z.mod_small (nfix n) (2^64)) by (clear - NFB NB; lia).
        zstep. change 7 with (Z.ones 3). rewrite Z.land_ones by (clear; lia). change (2^3) with 8.
        zstep.
        pg_leaf. rewrite PGV.
        match goal with H : rw_cells _ _ (2147450880 + Z.shiftr _ 3) _ |- _ => rewrite unsigned_lit in H by (clear - MNF; lia); exact H end. }
      zstep. if_cases KL; zify_cond KL.
      + eapply TAILPG. reflexivity.
      + (* [comment removed for export] *)
        zstep. zstep. zstep. zstep. zstep. zstep. zstep.
        zstep. if_cases K2; zify_cond K2. 2:{ exfalso. clear - K2 KE RNG AB0 RZSB DNF MNF NFB N2B. lia. }
        zstep. zstep. zstep. zstep. zstep.
        zstep. if_cases K3; zify_cond K3. { exfalso. clear - K3 KE RNG AB0 RZSB DNF MNF NFB N2B. lia. }
        zstep. if_cases K4; zify_cond K4. { exfalso. clear - K4 KL KE RNG AB0 RZSB DNF MNF NFB N2B. lia. }
        eapply TAILPG. reflexivity.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  Definition sfill_post (SP : Z) (gp tp x8 x25 x28 t4 t5 t6 x22 : word) (F : bvmap 5 word) (fc : bv 32)
      (n AB STK T TID lo fill : Z) (W : list (Z * Z)) (m0 : mem) : machine_state -> Prop := ltac2:(CDefT.buildp (gd_tbl_AW_SecB ()) "Lms',$?.(10.(11.&40.)Lx1,(11.&40.)(10.(11.&40.)Lx5,(11.&40.)(10.(11.&40.)Lx6,(11.&40.)(10.(11.&40.)Lx7,(11.&40.)(10.(11.&40.)Lx10,(11.&40.)(10.(11.&40.)Lx11,(11.&40.)(10.(11.&40.)Lx12,(11.&40.)(10.(11.&40.)Lx13,(11.&40.)(10.(11.&40.)Lx14,(11.&40.)(10.(11.&40.)Lx15,(11.&40.)(10.(11.&40.)Lx16,(11.&40.)(10.(11.&40.)Lx17,(11.&40.)(10.(11.&40.)Ly28,(11.&40.)(10.(11.&40.)Ly29,(11.&40.)(10.(11.&40.)Ly30,(11.&40.)(10.(11.&40.)Ly31,(11.&40.)(10.P,(11.&40.)(12.(11.&8.))Lm',P,(11.&40.)(12.(11.&8.))ZUB,$0.(<.O8.(:.O9.))ZCHB,$0.(<.R1.-10.)Zk,$0.(42.(9.O9.)+1000.)(1.(5.$?.R15.(15.(16.R14.(17.&40.(<.O15.-80.))O14.O13.R13.R12.R11.O12.(17.&40.(9.O9.))R10.R?.R>.R=.R<.R;.R:.R9.(17.&40.O8.)(17.&40.(;.O9.))(17.&40.R3.)(17.&40.R2.)O<.(17.&40.O7.)(17.&40.(13.O5.(4.+2.+20.)))O11.(17.&40.O6.)(17.&40.+1.)R8.R7.R6.R5.)O;.(17.&40.+48174.)O:.(1:.(11.&40.))R4.(1;.$1<.)))(1.(1=.(1>.(1?.$0.$0.)(20.$0.$0.O4.(<.O15.-80.))(1>.(1?.$0.$0.)(20.$0.$0.R3.(<.R3.R1.))O2.))O1.R4.)(1.(21.$1<.O1.R4.)(1.(22.$1<.R4.)(1.P,(43.(5.$0.O3.=))(23.$1<.R5.R4.(1>.$24.(44.(45.R2.)(46.(11.&8.)(17.&8.+;>.)(45.R2.)))(2:.$24.)))(1.P,(5.$0.O3.=)(1.(5.P,(11.&40.)(12.(11.&8.))R5.O1.)(1.(5.(11.&40.)R9.O10.)(1.(5.(11.&40.)R8.O?.)(1.(5.(11.&40.)R7.O>.)(5.(11.&40.)R6.O=.)))))(2;.$1<.R4.O4.(<.O15.-80.)))))))))))))))))))))))))")
(* [comment removed for export] *).

  Local Ltac2 Set LiaOrc.tbl := fun () => "00\0?L10080313547.87L14397645527.4 L1938578203.86 L1958740530.87 L21898462210.7 L23634997940.11L23925614726.86L24611005100.2 L25553375254.87L25705851087.2 L27322058401.0 L27705282402.5 L28933518550.87L29264400529.86L29267737599.86L34075563420.87L36193165570.2 L37092081232.7 L37293927126.87L39016003391.86L39120847666.89L39424301275.86L39932040119.89L43275003996.87L5039651420.5  L51176747153.86L52870152178.87L52871111443.2 L53522310972.86L53534730161.87L54029594404.2 L55176146118.86L56083444363.87L57132990364.87L61030858054.87L62631259186.87L63374621462.88L64776702091.87L66324202908.87L6655726801.86 L66907368529.86L67118443646.0 L8276233180.87 L9533021084.87 00000100@00O00P00d01B01C01I01X01_01`01h02702>02?02N02Q02c03203303=03L04>04E04R04a04b04j05:05J05P05Q05R05Y05o06006F06G06N06]06d06e07407CFS1n2AB3AB04RZSBS3hAR2AL1n4IMG'FS1n2AB4RZSB3N2B1x2HxS3hAR2SP1n2AB2lo3AB15LOIMG3N2BFS1n2KMS3hAR2AL1n4IMG'S1n3NFBSS1n1H2H0S3hAR2AL1n4IMG'S3hAR1nFS3hAR2AL1n4IMG'S1nS3hAR1n2AB3AB13N2BS3hAR2AL1n4IMG'FS3hAR2SP1nS3hAR2AL1n4IMG'S3hAR2SP1n2AB2lo2NB3AB03AB15LOIMG3SPL4RZSB3NFB3N2BS3hAR1nS1n4RZSB1H2H0S3hAR2AL1n4IMG'FS1n4MINBS3hAR2AL1n5ALWF'S3hAR2AL1n5ALWF'S1n2KMFFS3hAR1nS3hAR2SP1n2AB2UB3CHB1kFS3hAR2SP1n2AB2UB3CHB1kFS3hAR1nS3hAR2AL1n4IMG'S3hAR1nSS3hAR2AL1n4IMG'S3hAR2AL1n4IMG'". (* [comment removed for export] *)
  #[using="IMG ALWF CSOK"] Lemma sec_fill : ltac2:(CDefT.buildp (gd_tbl_AW_SecB ()) "Pgp,(11.&40.)Ptp,(11.&40.)Px1,(11.&40.)Px5,(11.&40.)Px6,(11.&40.)Px7,(11.&40.)Px8,(11.&40.)Px10,(11.&40.)Px11,(11.&40.)Px12,(11.&40.)Px13,(11.&40.)Px14,(11.&40.)Px15,(11.&40.)Px16,(11.&40.)Px17,(11.&40.)Px22,(11.&40.)Px25,(11.&40.)Px28,(11.&40.)Pt4,(11.&40.)Pt5,(11.&40.)Pt6,(11.&40.)Pqra,(11.&40.)Pq0,(11.&40.)Pq1,(11.&40.)Pq2,(11.&40.)Pq3,(11.&40.)Pq4,(11.&40.)Pq5,(11.&40.)Pq6,(11.&40.)Pq7,(11.&40.)Pq8,(11.&40.)Pq9,(11.&40.)Pq10,(11.&40.)Pq11,(11.&40.)PSP,$0.Pn,$0.PAB,$0.PSTK,$0.PT,$0.PTID,$0.Plo,$0.Pfill,$0.PF,(2<.&5.(11.&40.))Pfc,(11.&20.)Pm,P,(11.&40.)(12.(11.&8.))Pfr0,(2=.(11.&8.))Puj,(2=.(11.&8.))PW,(2=.(1?.$0.$0.))ZUB,$0.(<.R<.(:.R=.))ZCHB,$0.(<.R1.-10.)Zk,$0.(42.(9.R?.)+1000.)P,(1.(2.=R10.)(3.R10.(4.+2.+20.)))P,(2.+65?000.R10.)P,(2.(<.R11.(;.R12.))(2?.VhAR,))P,(1.(2.=R=.)(2.R=.+1.))P,(43.(5.$0.R>.=))P,(31.VCS,R14.(;.R15.))P,P,(43.(5.$0.R10.=))(23.$1<.R>.R:.(1>.$24.(44.(45.R8.)R<.)(2:.$24.)))P,(47.R>.)P,(38.R?.R19.R>.R12.R26.R25.R24.R23.R22.R21.R20.R1?.R1>.R1=.R1<.R1;.R1:.)P,(2;.$1<.R10.R14.(<.R1:.-80.))P,(2.(2?.VhAR,)R15.)P,(2.R16.(18.R1<.+200.))P,(2.R1=.(4.+2.+3>.))P,(5.$0.(>.R1>.+10.)=)P,(31.VCS,R19.(18.R1?.R19.))P,(22.$1<.R16.)(35.$1<.VAL,VCS,(48.R21.R43.R42.R3=.R33.R32.R31.R30.R2?.R34.R19.R18.R20.R1?.R1>.R1=.R1<.R1;.R1:.R14.R17.)(15.(16.R41.(17.&40.(<.R21.-80.))R43.R42.R40.R3?.R3>.R3=.(17.&40.(9.R20.))R3<.R3;.R3:.R39.R38.R37.R36.R35.(17.&40.R1?.)(17.&40.(;.R20.))(17.&40.R13.)(17.&40.R12.)R34.(17.&40.R1>.)(17.&40.(13.R1<.(4.+2.+20.)))R33.(17.&40.R1=.)(17.&40.+1.)R32.R31.R30.R2?.)R19.(17.&40.+48140.)R18.(1:.(11.&40.))R17.(1;.$1<.)))")
(* [comment removed for export] *).
  Proof.
    try lx_hide ASB.  (* [comment removed for export] *)
    intros gp tp x1 x5 x6 x7 x8 x10 x11 x12 x13 x14 x15 x16 x17 x22 x25 x28 t4 t5 t6 qra q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11
      SP n AB STK T TID lo fill F fc m fr0 uj W UB CHB k
      NB AB0 AB1 FB KF ACS UC (L1 & L2 & MGC & MH & GF & FMX & FFB & G5 & RM) FR ST LOIMG SPL SPH SPA SCS MI.
    facts. unfold A_GOT_LSANTLS, A_LSAN_CNT, A_MAGIC_CELL, A_MHOOKS, A_GOT_FLAGS, A_FLAGS, A_FL_MAXFILL, A_FL_FILLB, A_GOT_RMEMSET, A_RMEMSET,
      A_MUSL_MEMSET in *.
    pose proof (rz_size_bound n) as RZSB.
    assert (NFB : 1 <= nfix n <= Z.max n 1) by (unfold nfix; clear - NB; lia).
    assert (N2B : nfix n + rz_size n <= needed2 n).
    { unfold needed2, needed, rounded, round_up. pose proof (Z.div_mod (Z.max n 8 + 8 - 1) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (Z.max n 8 + 8 - 1) 8 ltac:(lia)).
      destruct (from_primary n); unfold nfix; clear - H H0 NB RZSB; lia. }
    subst CHB UB k.
    unfold allocA_frame in FR.
    pose proof (munch_refl ((lo, SP + -128) :: (AB + rz_size n, AB + rz_size n + Z.min (nfix n) 4096) :: W) m) as MU. pose proof (wmono_refl asegs m) as WM.
    specialize (UC KF).
      (* [comment removed for export] *)
      zstep. zstep. zstep. zstep. zstep.
      replace (sx32 (Z_to_bv 64 4096)) with (Z_to_bv 64 4096) by (apply bv_eq; vm_compute; reflexivity).
      assert (TAILM : forall (q2 : word), 
        evtA asegs AL CS (sfill_post SP gp tp x8 x25 x28 t4 t5 t6 x22 F fc n AB STK T TID lo fill W m)
          (MS (mkR x1 (Z_to_bv 64 (SP + -128)) gp tp x5 x6 x7 x8 (Z_to_bv 64 (nfix n))
                   (Z_to_bv 64 1077752) (Z_to_bv 64 4096) (Z_to_bv 64 (Z.min (nfix n) 4096)) x13 x14 x15 x16 x17
                   (Z_to_bv 64 AB) (Z_to_bv 64 (needed2 n)) (Z_to_bv 64 (AB + rz_size n)) (Z_to_bv 64 (AB + rz_size n + -16)) x22 (Z_to_bv 64 STK)
                   (Z_to_bv 64 (TID * 2^32)) x25 (Z_to_bv 64 T) (Z_to_bv 64 1) x28 t4 t5 t6)
               F (Z_to_bv 64 0x4815c) fc None m (seg_rom asegs))).
      { intros _. assert (MINB : 1 <= Z.min (nfix n) 4096 <= nfix n) by (clear - NFB; lia).
        (* [comment removed for export] *)
        zstep. zstep. zstep. zstep. zstep. zstep.
        replace (sx32 (Z_to_bv 64 190)) with (Z_to_bv 64 190) by (apply bv_eq; vm_compute; reflexivity).
        eapply evtA_mono.
        { eapply (A_memset_evtA_aok AL CS IMG) with (junk := uj); [exact UC| exact MI| | | | | | reflexivity| reflexivity| reflexivity].
        2:{ clear - AB0 RZSB. lia. } 2:{ clear - MINB. lia. } 2:{ clear - AB1 N2B MINB RZSB. lia. } 2:{ clear. lia. }
          intros x Hx. left. apply ACS. clear - Hx RZSB N2B MINB. lia. }
        cbn beta. intros ms2 (z0 & z1 & z2 & w1 & w2 & w3 & w4 & w5 & w6 & w7 & z3 & z4 & z5 & z6 & m' & -> & MUm & WMm & MIm & SHm).
        replace (ret_pc (Z_to_bv 64 0x48174)) with (Z_to_bv 64 0x48174) by (symmetry; apply ret_pc_even; [ clear; lia | reflexivity ]).
        unfold sfill_post. do 16 eexists. exists m'. split; [reflexivity|].
        split. { eapply munch_weaken; [| exact MUm]. unfold sub_fp; cbn [outside]. clear. intros x Hx. tauto. }
        split; [exact WMm|]. split; [exact MIm|]. split; [intros _; exact SHm|].
        split; [intros F0; exfalso; apply KF; exact F0|].
        eapply stk_transport_disjoint; [exact ST| exact MUm| exact WMm|]. cbn [disjoint_from]. split; [| exact I]. clear - AB1 LOIMG SPL N2B MINB RZSB. lia. }
      zstep. if_cases KM; zify_cond KM.
      + replace (Z.min (nfix n) 4096) with (nfix n) in TAILM by (clear - KM; lia). apply TAILM. exact x12.
      + zstep. replace (Z.min (nfix n) 4096) with 4096 in TAILM by (clear - KM; lia). apply TAILM. exact x12.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  Local Ltac2 Set LiaOrc.tbl := fun () => "01X0@L10184747763.96 L10210849586.3  L11151000370.95 L11666481681.3  L11985143081.1  L13277838258.91 L13296972522.98 L13618020628.100L1495112192.94  L15393414155.91 L15636460711.100L18858039182.102L19129098672.98 L19160092211.100L19180804124.91 L19586266388.100L23426481611.80 L24886574194.93 L24989977372.91 L25805129492.100L27705282402.5  L2868317467.96  L29270158734.102L30507141665.98 L31919852430.102L32537519809.102L32729246119.1  L32852261457.96 L34430750804.1  L3509211164.91  L35250499860.100L3525608835.99  L3525611157.98  L35992898843.96 L36193165570.2  L36631107470.102L37396631557.0  L37964339962.1  L38465086153.102L38555397984.1  L38962019212.94 L39407456835.99 L39944775816.100L41137568973.98 L41388092302.102L41671761036.100L42031126465.98 L42650174943.100L43907602222.2  L44975803890.81 L45914037331.98 L46180902676.100L46444081826.101L46935889045.1  L47500037067.80 L49382159157.3  L49698585326.99 L49705053714.98 L5039651420.5   L50766042396.91 L50966866708.100L52137112076.96 L53516973216.94 L53520095665.91 L53522113078.96 L54082276882.3  L54780234875.94 L54780293584.91 L54780741077.94 L55474644110.102L55606901317.2  L56821025934.102L57056925710.96 L57936462681.3  L58127006740.100L58301450569.94 L58301759719.94 L58301791564.91 L59308630630.6  L59308632432.4  L59310676309.3  L59696744469.95 L59696744469.98 L60299333669.2  L60395280782.102L61030858054.95 L61051158381.96 L61580800532.100L62033406508.96 L62632109323.91 L63064043092.1  L63361644942.102L63374621462.96 L65166668886.91 L66532340722.98 L66732409525.96 L67259945748.100L704957270.91   L7807593471.2   L8458413483.2   L9001182386.91  L9143127683.2   L959706227.100  L9728771280.94  00000:00;00H00I00M00N00^01W01d01e02202R02_03303G04@04T04h04o05h06006D06d07W08708V08Z08i08j09109j0:Y0;L0;S0;V0<60<70<;0=<0==0=T0>C0>W0>d0?D0@B0@W0AX0A^0BM0B]0CV0Cl0D00DD0DE0D[0Dk0E80EL0FE0FF0FS0Fc0G30G>0GM0G\0Gk0HK0HS0I30IM0IY0JR0Ji0K@0KW0Kn0L?0LJ0LW0Ld0Ll0ML0M`0N:0O30O=0O>0O?0O_0P30PB0PO0PP0QI0QX0QY0QZ0Q[0Qd0R10R@S3hAR1n2ABFS3hAR2SP1n2ABFS2SPFS3hAR2SP1n2AB2HBS3hAR2SP1n2AB2lo2b13AB05LOIMG3SPL4RZSB2HB5Ha_st5Hl_st3RZES3hAR2SP1n2ABFS3hAR2SP1n2ABS3hAR2SP1n2AB3AB02HB5Ha_st5Hl_stS3hAR2SP1n2ABS3hAR2SP1n2AB3AB02HBS3hAR2AL1n4IMG'4RZSBS3hAR2SP1n2AB2lo2b13AB05LOIMG3SPL4RZSB2HB5Ha_st5Hl_st3RZES3hAR2SP1n2AB2lo3SPLS3hAR2SP1n2AB2UB3CHBS3hAR1nS3hAR2SP1n2AB2lo2b13AB05LOIMG3SPL4RZSB2HB5Ha_st5Hl_st3RZES1n1H2H0S3hAR2AL1n4IMG'4RZSBS3hAR2SP1n2AB3AB02HB5Ha_st5Hl_stS3hAR2SP1n2AB2lo3AB03AB15LOIMG3SPL4RZSB3NFB3N2B3RZES3hAR2SP1n2AB3AB02HB5Ha_st5Hl_stS3hAR2SP1n2AB2KC2HB5Ha_st5Hl_stS2SPS3hAR2AL1n4IMG'FS3hAR1nS3hAR2SP1n2AB2lo2b13AB05LOIMG3SPL4RZSB2HB5Ha_st5Hl_st3RZES3hAR2SP1n2AB2lo3AB03AB15LOIMG3SPL4RZSB3NFB3N2BS3hAR2SP1n2AB2lo3AB03AB15LOIMG3SPL4RZSB3NFB3N2B3RZES3hAR1nS1nS3hAR2SP1n2AB3AB02HB5Ha_st5Hl_stSS2SPS3hAR2SP1n2AB2lo3AB03AB15LOIMG3SPL4RZSB3NFB3N2B2KC2HB5Ha_st5Hl_stFS3hAR1n2AB4RZSB3NFB3N2BS3hAR2SP1n2AB2lo3AB03AB15LOIMG3SPL4RZSB3NFB3N2BS3hAR2SP1n2AB3AB02HBS3hAR2SP1n2ABS3hAR2SP1n2AB3AB02HB5Ha_st5Hl_stS3hAR2SP1n2AB2lo2b13AB05LOIMG3SPL4RZ164DR163RZL2HB5Ha_st5Hl_stS3hAR2SP1n2AB2lo1W2HBS3hAR2SP1n2AB2lo2b13AB03AB15LOIMG3SPL4RZSB3NFB3N2B2HB5Ha_st5Hl_stS1n2ABS3hAR2SP1n2AB2lo3AB03AB15LOIMG3SPL4RZSB3NFB3N2BS3hAR2SP1n2AB2HBS3hAR2SP1n2AB2lo2b13AB05LOIMG3SPL4RZSB2HB5Ha_st5Hl_st3RZES3hAR2SP1n2AB2HB5Ha_stS2SPS3hAR2SP1n2AB2lo3SPLFS3hAR2SP1n2AB2HB5Ha_stS3hAR2SP1n2AB2HBS1n4RZSB1H2H0S3hAR2AL1n4IMG'4RZSBS3hAR2SP1n2AB2lo2b13AB05LOIMG3SPL4RZSB2HB5Ha_st5Hl_st3RZEFS3hAR2SP1n2ABS3hAR2AL1n5ALWF'S3hAR2AL1n5ALWF'S2SP2lo3SPLS3hAR1n2AB4RZSBS3hAR1n2AB4RZSBS3hAR1n2AB4RZSBS3hAR2SP1n2AB3AB02HB5Ha_st5Hl_stS2b13B1BS3hAR2SP1n2AB3AB02HB5Ha_st5Hl_stS3hAR1n2AB4RZSB3NFB3N2B2KCS1n4RZSB3RZSS3hAR2SP1n2AB2lo2b13AB05LOIMG3SPL4RZSB2HB5Ha_st5Hl_st3RZES3hAR1n2AB4RZSB3NFB3N2BS3hAR1n2AB4RZSB3NFB3N2BS3hAR1n2AB4RZSB3NFB3N2BS1n2AB4RZ164DR163RZL2KCS1n2AB3RZL2KQ3RZES1n3RZE3H16S3hAR2SP1n2ABS3hAR2SP1n2ABS2SP3SPHS3hAR2SP1n2AB3AB02HB5Ha_st5Hl_stS3hAR2SP1n2AB2UB3CHBS3hAR1n2AB4RZSB3NFB3N2B2KCS3hAR2SP1n2AB2lo2b13AB05LOIMG3SPL4RZSB2HB5Ha_st5Hl_st3RZES3hAR1n2ABFFS3hAR2SP1n2AB3AB02HB5Ha_st5Hl_stS3hAR2SP1n2AB2UB3CHBS3hAR2AL1n4IMG'S3hAR2SP1n2ABFS3hAR2SP1n2AB2lo2b13AB05LOIMG3SPL4RZSB2HB5Ha_st5Hl_st3RZES3hAR2AL1n4IMG'FSFS2b14B1R'S3hAR2SP1n2ABS3hAR1n2AB4RZSB". (* [comment removed for export] *)
  #[using="IMG ALWF CSOK"] Lemma sec_fin2 : ltac2:(CDefT.buildp (gd_tbl_AW_SecB ()) "Pgp,(11.&40.)Ptp,(11.&40.)Px1,(11.&40.)Px5,(11.&40.)Px6,(11.&40.)Px7,(11.&40.)Px8,(11.&40.)Px10,(11.&40.)Px11,(11.&40.)Px12,(11.&40.)Px13,(11.&40.)Px14,(11.&40.)Px15,(11.&40.)Px16,(11.&40.)Px17,(11.&40.)Px22,(11.&40.)Px25,(11.&40.)Px28,(11.&40.)Pt4,(11.&40.)Pt5,(11.&40.)Pt6,(11.&40.)Pb0,(11.&8.)Pmg0,(11.&40.)Pmg1,(11.&40.)Pqra,(11.&40.)Pq0,(11.&40.)Pq1,(11.&40.)Pq2,(11.&40.)Pq3,(11.&40.)Pq4,(11.&40.)Pq5,(11.&40.)Pq6,(11.&40.)Pq7,(11.&40.)Pq8,(11.&40.)Pq9,(11.&40.)Pq10,(11.&40.)Pq11,(11.&40.)PSP,$0.Pn,$0.PAB,$0.PSTK,$0.PT,$0.PTID,$0.Pid,$0.Plo,$0.Pb1,$0.Pfill,$0.PF,(2<.&5.(11.&40.))Pfc,(11.&20.)Pm0,P,(11.&40.)(12.(11.&8.))Pm,P,(11.&40.)(12.(11.&8.))Pfr0,(2=.(11.&8.))PW,(2=.(1?.$0.$0.))ZUB,$0.(<.R>.(:.R?.))ZCHB,$0.(<.R1.-10.)P,(1.(2.=R11.)(3.R11.(4.+2.+20.)))P,(2.+65?000.R11.)P,(5.$0.(>.R12.+10.)=)P,(2.(<.R13.(;.R14.))(2?.VhAR,))P,(1.(2.=R>.)(3.R>.+100.))P,(31.VCS,R15.(;.R16.))P,(23.$1<.R;.R7.(1>.$24.(25.R28.)(1>.$24.(25.(17.&8.R10.))(1>.$24.(26.(17.&40.=))(1>.$24.(27.(17.&40.(9.R17.)))(1>.$24.(28.(17.&40.(29.(13.R13.(4.+2.+20.))R12.)))(2:.$24.)))))))P,P,(3.+10.(:.R18.))(23.$1<.R=.R18.(1>.$24.(28.R29.)(1>.$24.(28.R28.)(2:.$24.))))P,(47.R=.)P,(38.R>.R1;.R=.R12.R28.R27.R26.R25.R24.R23.R22.R21.R20.R1?.R1>.R1=.R1<.)P,(2;.$1<.R?.R15.(<.R1<.-80.))P,(2.(2?.VhAR,)R16.)P,(2.R17.(18.R1>.+200.))P,(2.R1?.(4.+2.+3>.))P,(5.$0.(>.R20.+10.)=)P,(31.VCS,R1:.(18.R21.R1:.))P,(1=.(1>.(1?.$0.$0.)(20.$0.$0.R1;.R22.)(1>.(1?.$0.$0.)(20.$0.$0.R11.(<.R11.+2.))(1>.(1?.$0.$0.)(20.$0.$0.R20.(<.R20.+10.))R13.)))R16.R15.)P,(21.$1<.R17.R16.)P,(22.$1<.R17.)P,(5.(11.&40.)R49.(17.&40.$39.))(35.$1<.VAL,VCS,(49.R26.R4;.R4:.R1<.R1;.R25.R24.R21.R20.R1?.R1>.R35.R34.R33.R32.R31.R30.R2?.R2>.R2=.R2<.R2;.R2:.R29.R28.R27.R17.R1:.)(15.(16.R49.(17.&40.(<.R26.-80.))R4;.R4:.R48.R47.R46.R45.(17.&40.(9.R25.))R44.R43.R42.R41.R40.R3?.R3>.R3=.(17.&40.R24.)(17.&40.(;.R25.))(17.&40.R16.)(17.&40.R15.)R3<.(17.&40.R23.)(17.&40.(13.R21.(4.+2.+20.)))R3;.(17.&40.R22.)(17.&40.+1.)R3:.R39.R38.R37.)R1<.(17.&40.+48174.)R1;.(1:.(11.&40.))R19.(1;.$1<.)))")
(* [comment removed for export] *).
  Proof.
    try lx_hide ASB.  (* [comment removed for export] *)
    intros gp tp x1 x5 x6 x7 x8 x10 x11 x12 x13 x14 x15 x16 x17 x22 x25 x28 t4 t5 t6 b0 mg0 mg1 qra q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11
      SP n AB STK T TID id lo b1 fill F fc m0 m fr0 W UB CHB
      NB AB0 ABAL AB1 B1B ACS HDR MG (L1 & L2 & MGC & MH & GF & FMX & FFB & G5 & RM) FR ST LOIMG SPL SPH SPA SCS MU WM MI ->.
    facts. unfold A_GOT_LSANTLS, A_LSAN_CNT, A_MAGIC_CELL, A_MHOOKS, A_GOT_FLAGS, A_FLAGS, A_FL_MAXFILL, A_FL_FILLB, A_GOT_RMEMSET, A_RMEMSET,
      A_MUSL_MEMSET, A_TP, kAllocBegMagic, CHUNK_ALLOCATED in *.
    pose proof (rz_size_bound n) as RZSB.
    assert (RZ16 : rz_size n mod 16 = 0) by (unfold rz_size; rewrite Z.mul_comm; apply Z_mod_mult).
    pose proof (Z.div_mod (rz_size n) 16 ltac:(lia)) as DR16.
    assert (NFB : 1 <= nfix n <= Z.max n 1) by (unfold nfix; clear - NB; lia).
    assert (N2B : nfix n + rz_size n <= needed2 n).
    { unfold needed2, needed, rounded, round_up. pose proof (Z.div_mod (Z.max n 8 + 8 - 1) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (Z.max n 8 + 8 - 1) 8 ltac:(lia)).
      destruct (from_primary n); unfold nfix; clear - H H0 NB RZSB; lia. }
    subst CHB UB. unfold allocA_frame in FR.
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep. zstep. zstep. zstep.
    match goal with |- context [Z_to_bv 64 (Z.b2z ?c)] => replace (Z.b2z c) with 0 by (vm_compute; reflexivity) end.
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep. zstep. zstep.
    rewrite Z.lor_0_r. replace (bv_unsigned (Z_to_bv 8 b1)) with b1
      by (rewrite Z_to_bv_unsigned; unfold bv_wrap, bv_modulus; change (2 ^ Z.of_N 8) with 256; rewrite Z.mod_small by (clear - B1B; lia); reflexivity).
    pose proof (land_lt_pow2 b1 243 8 ltac:(change (2^8) with 256; clear - B1B; lia) ltac:(clear; lia)) as B1R'. change (2^8) with 256 in B1R'.
    assert (TAILF : forall (y10 y11 y13 : word) (mc : mem),
      rw_cells asegs mc (AB + rz_size n + -16) [C1 (Z_to_bv 8 2); C1 (Z_to_bv 8 (Z.land b1 243)); C2 (Z_to_bv 64 0); C4 (Z_to_bv 64 (nfix n)); C8 (Z_to_bv 64 (Z.lor (TID * 2^32) id))] ->
      (16 < rz_size n -> rw_cells asegs mc AB [C8 (Z_to_bv 64 0xcc6e96b9cc6e96b9); C8 (Z_to_bv 64 (AB + rz_size n + -16))]) ->
      rw_cells asegs mc (SP + -128) [CB 8 fr0; C8 (Z_to_bv 64 fill); C8 (Z_to_bv 64 16); C8 q11; C8 q10; C8 q9; C8 q8; C8 q7; C8 q6; C8 q5; C8 q4; C8 q3; C8 q2; C8 q1; C8 q0; C8 qra] ->
      ro_cells asegs mc 1684672 [C8 (Z_to_bv 64 0)] ->
      stk asegs mc lo (SP + -128) -> munch ((lo, SP) :: (AB + rz_size n + -16, AB + rz_size n + -16 + 2) :: (AB, AB + 16) :: W) m0 mc ->
      wmono asegs m0 mc -> mem_inv asegs mc ->
      evtA asegs AL CS (fin_post SP gp (Z_to_bv 64 6539920) F fc n AB TID id lo b1 mg0 mg1 qra q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 W m0)
        (MS (mkR (Z_to_bv 64 0x48178) (Z_to_bv 64 (SP + -128)) gp (Z_to_bv 64 6539920) x5 x6 x7 x8 (Z_to_bv 64 (nfix n))
                   y10 y11 x12 y13 x14 x15 x16 x17
                   (Z_to_bv 64 AB) (Z_to_bv 64 (needed2 n)) (Z_to_bv 64 (AB + rz_size n)) (Z_to_bv 64 (AB + rz_size n + -16)) x22 (Z_to_bv 64 STK)
                   (Z_to_bv 64 (TID * 2^32)) x25 (Z_to_bv 64 T) (Z_to_bv 64 1) x28 t4 t5 t6)
               F (Z_to_bv 64 0x481bc) fc None mc (seg_rom asegs))).
    { intros y10 y11 y13 mc HDR' MG1 FR' MH' ST' MU' WM' MI'.
      (* [comment removed for export] *)
      lx_hide MU'. lx_hide WM'. lx_hide MG1.
      pose proof (munch_refl [(lo, SP)] mc) as MUF. pose proof (wmono_refl asegs mc) as WMF. lx_aceil.
      lx_run (PLAN [0x481c8] [] 40%N). lx_unhide. try clear LXlen. lx_stk_grow_to lo (SP + -128).
      try replace (AB + (rz_size n + -16)) with (AB + rz_size n + -16) in * by (clear; lia).
      try clear FR; try clear AFR; try clear ST; try clear HDR.
      lazymatch goal with MUl : munch _ mc ?mx, WMl : wmono _ mc ?mx, FRl : rw_cells _ ?mx (SP + -128) _, STl : stk _ ?mx lo (SP + -128) |- _ =>
        assert (MU2 : munch ((lo, SP) :: (AB + rz_size n + -16, AB + rz_size n + -16 + 2) :: (AB, AB + 16) :: W) m0 mx) by (lx_munch MU' MUl);
        assert (WM2 : wmono asegs m0 mx) by (lx_wmono WM' WMl);
        eapply evtA_mono;
        [ eapply (alloc_epi AL IMG ALWF CS CSOK); [exact FRl| exact STl| exact LOIMG| clear - SPL; lia| clear - SPH; lia| exact SPA| exact SCS| exact MU2| exact WM2| assumption]
        | cbn beta; intros ms1 (-> & STE9);
          unfold fin_post; do 14 eexists; eexists; split; [reflexivity|]; split; [exact MU2|]; split; [exact WM2|]; split; [assumption|];
          split; [match goal with H : rw_cells _ _ (AB + rz_size n + -16) _ |- _ => exact H end|]; split; [| exact STE9];
          let H16 := fresh "H16" in intros H16; eapply rw_cells_transport; [exact (MG1 H16)| exact MUl| exact WMl| lx_dj] ] end. }
    (* [comment removed for export] *)
    destruct (Z_lt_dec 16 (rz_size n)) as [RZL|RZS].
    + pose proof (MG RZL) as MG'. clear MG.
      zstep. zstep. zstep.
      match goal with H : rw_cells _ _ (AB + rz_size n + -16) _ |- _ => rewrite !unsigned_lit in H by (clear - B1R'; lia) end.
      (* [comment removed for export] *)
      zstep. if_cases KQ; zify_cond KQ. { exfalso. clear - KQ RZL. lia. }
      zstep. zstep. if_cases KC; zify_cond KC. { exfalso. clear - KC RZL RZ16 DR16. lia. }
      zstep. zstep. zstep. zstep. zstep.
      eapply TAILF; try eassumption. intros _. assumption.
    + clear MG. assert (RZE : rz_size n = 16) by (clear - RZS RZSB; lia).
      zstep. zstep. zstep.
      match goal with H : rw_cells _ _ (AB + rz_size n + -16) _ |- _ => rewrite !unsigned_lit in H by (clear - B1R'; lia) end.
      zstep. if_cases KQ; zify_cond KQ. 2:{ exfalso. clear - KQ RZE. lia. }
      eapply TAILF; try eassumption. intros H16. exfalso. clear - H16 RZE. lia.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

End SecB.

End ARUN_1.
