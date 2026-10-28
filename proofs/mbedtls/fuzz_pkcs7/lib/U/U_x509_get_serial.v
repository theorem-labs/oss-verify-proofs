(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Walk AStep CellsX Asn1Aux X509Aux X509AuxB.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Spec Require Import Rep.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U Require Import UImg U_asn1_get_tag U_asn1_get_len.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LXP Require Import LxPTac. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LXU Require Import LxU_Sums1.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Import OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.LxhSyntax. #[local] Instance lxh_tab : OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.lx_hints := OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.lxh_parse "P0080293d45c70479 0 3 0 1 2 1 29 1P00d070fd8ea13311 2 15 0 5 0 1 3 1 20 1 30 1 31 1 0 4 0 1 2 1 30 1 31 1P03202ad0529e2742 0 2 0 1 30 1P039a8fccd6439754 0 2 0 1 24 1P06e5b5ddd7f5b283 0 2 0 1 7 1P0890b07d29a0fe41 1 1 8 3 1 1 35 1 38 1 4 2 2 36 2 37 2 39 16P094662184c23f8b6 0 4 0 1 2 1 37 1 38 1P0aa23b80e5d2af3a 0 4 0 1 17 1 27 1 28 1P0b2e4eb32ccd0884 2 15 0 5 0 1 3 1 20 1 30 1 31 1 0 4 0 1 2 1 30 1 31 1P0b7796b4c8c7a265 2 22 1 1 8 3 1 1 36 1 37 1 5 0 2 25 2 35 2 38 2 39 16 1 1 8 3 2 1 35 1 38 1 4 0 2 36 2 37 2 39 16P0cc0ab4b63995f05 0 3 0 1 2 1 29 1P0e291dcb2112704a 2 15 0 5 0 1 3 1 20 1 30 1 31 1 0 4 0 1 2 1 30 1 31 1P0eedc23594faa574 0 2 0 1 5 1P0fde935703a46d62 0 2 0 1 1 1P108f348aa9a45b4b 0 4 0 1 30 1 40 1 41 1P15f962c75c97dad3 0 2 0 1 5 1P1671ef4cf57a71d4 2 32 1 1 8 3 1 1 45 1 46 1 5 0 2 34 2 44 2 47 2 48 16 1 1 8 3 2 1 44 1 47 1 4 0 2 45 2 46 2 48 16P181900e0d2f07e8c 2 21 1 1 8 3 1 1 34 1 35 1 5 0 2 23 2 33 2 36 2 37 16 1 1 8 3 2 1 33 1 36 1 4 0 2 34 2 35 2 37 16P1d282b1a667520a6 1 1 8 3 1 1 36 1 37 1 4 2 2 35 2 38 2 39 16P1d7c0d652109c78a 0 4 0 8 20 8 33 8 34 8P1d80dad8792002d6 2 17 1 1 8 3 2 1 30 1 31 1 5 0 2 19 2 29 2 32 2 33 16 1 1 8 3 1 1 29 1 32 1 4 0 2 30 2 31 2 33 16P1da30ece0d3bd024 2 17 1 1 8 3 2 1 30 1 31 1 5 0 2 19 2 29 2 32 2 33 16 1 1 8 3 1 1 29 1 32 1 4 0 2 30 2 31 2 33 16P1e297125af49d4b3 1 1 8 3 0 1 36 1 37 1 5 2 2 25 2 35 2 38 2 39 16P1ec7b7507c3824ff 1 1 8 3 1 1 35 1 38 1 4 2 2 36 2 37 2 39 16P206a0f890d1f6764 2 31 1 1 8 3 1 1 45 1 46 1 5 0 2 34 2 44 2 47 2 48 16 1 1 8 3 2 1 44 1 47 1 4 0 2 45 2 46 2 48 16P210f715590893cb3 2 16 1 1 8 3 2 1 30 1 31 1 5 0 2 19 2 29 2 32 2 33 16 1 1 8 3 1 1 29 1 32 1 4 0 2 30 2 31 2 33 16P212b9cf70ea5e2fc 0 4 0 1 19 1 29 1 30 1P212d32023683c577 0 3 0 1 1 1 22 1P213e792f77427080 0 4 0 1 32 1 42 1 43 1P23d07af533b51271 1 1 8 3 0 1 36 1 37 1 5 2 2 25 2 35 2 38 2 39 16P249fd4d93b7cac9a 0 2 0 1 1 1P2772d9f3830752cf 0 2 0 1 22 1P288fa3a9ac26d188 2 16 1 1 8 3 2 1 30 1 31 1 5 0 2 19 2 29 2 32 2 33 16 1 1 8 3 1 1 29 1 32 1 4 0 2 30 2 31 2 33 16P2a9a7faa6c2c6de0 0 2 0 1 28 1P2bf1bf61098a82e8 0 3 0 1 1 1 30 1P2c73f50aecbe0030 1 1 8 2 26 1 34 1 3 0 1 33 1 35 8P2cc93925ce635b72 0 5 0 1 17 1 20 1 21 1 23 1P2cf0bebb0608a947 0 2 0 1 6 1P2d498b5a192ccd51 0 4 1 1 2 1 35 1 36 1P2e6cadca13517c9b 0 2 0 1 24 1P2f8f63c330b3c9f2 1 1 8 3 1 1 35 1 38 1 4 2 1 36 1 37 1 39 8P3037827e7c997d25 0 2 0 1 28 1P307608ea6fe057a7 2 16 1 1 8 3 2 1 30 1 31 1 5 0 2 19 2 29 2 32 2 33 16 1 1 8 3 1 1 29 1 32 1 4 0 2 30 2 31 2 33 16P319b7defd3e00fb7 2 17 1 1 8 3 2 1 30 1 31 1 5 0 2 19 2 29 2 32 2 33 16 1 1 8 3 1 1 29 1 32 1 4 0 2 30 2 31 2 33 16P320dfa929896d4e9 1 1 8 3 0 1 36 1 37 1 4 2 1 35 1 38 1 39 8P33f6f19c8cd2b1dd 0 4 0 1 2 1 35 1 36 1P3658e58c98dd06dd 0 2 0 1 7 1P3673ac813839d525 1 1 8 3 1 1 36 1 37 1 4 2 2 35 2 38 2 39 16P36b462037980f3af 0 4 0 1 2 1 37 1 38 1P3965098511a2289b 0 3 0 1 1 1 30 1P3a5dbf3728a37131 0 3 0 1 5 1 26 1P3d56e18c3ee9c184 0 2 0 1 5 1P3ff83719a8ed2bfb 0 2 0 1 27 1N0022734ab7109251N00fe6a428e475650N02a127f4775056beN04c7902ce8146245N077f1d1d59d3dc5eN07936379565a36afN07966eae3fce1c68N07ce7b85447a9999N0846bf864bf7f3f8N084f5614bf8cfaffN095457dc95ce7b96N0ab3cf753bcd04e6N0aee3a71561784a4N0afa50866e2d9d7aN0bc4d121ae6af0e4N0c061eed7f680182N0c8228a73600dc5dN0d0e705e45e91ea4N0d171beb25323f4fN0d92d34d28a741bfN0dfa16daec0554a1N0e1e4a82922cedfdN0e59827baef9afdeN0f041fe99a3af021N0f620ebd80658c73N105564373bcd6619N12d0bdf066ec8c0dN13875fc2b1cb5672N14175f5200a412e2N143d2478959b6a9fN1460d51f2ea68419N1528d0fd465f8493N1598ef1c74d0f7ebN15aedd5ac7b0cef5N15f32cc2df25376cN161dfc63f18aac49N164407823a7bc4d6N165e292b533df65cN1757dd6101a408d6N17c7778295dc39ddN19a87401aecdb5d6N19f505bd7e4bbecaN19f812775ca3676bN1a4fc2ad23e86f51N1ab6a17ada91d2d6N1b0b70df0b5167d2N1b0b7fc3074cdf86N1bfe77ab860c5583N1cab3e13aa2ab801N1cce2c50ad87dfa3N1d3ab4b27829c148N1d81cfb47f5a111dN1d83db5449278374N1e7d51e16cf2e5edN1e9179221ff57d10N1f07b23203a6e0f7N1f7d289cdeb5900aN1fea03ff274cff7bN203332c7c2fd1540N205f073609d9820cN21338f00d2f0b104N216e3a0288eda901N218df42f632b40baN2201a46a7393abe4N2328fa7d3e2044e3N2382e5f14058bc15N23a94c9a33b60941N23d242b1a2524718N25a4713bb607fbcaN26233ad331814521N26b50796279ff2ceN26e7b4b97a03f364N288f34f6f8a73fdaN2983b7f1e70ebdf3N2a295e3a99fcbc58N2a300c0402ff0787N2a6241aba3d9c2dcN2ba2a160bb1857a9N2bed5f74c1c6aba2N2caa994f6a320dceN2d36a6cb28cbe7faN2d677eab80932da5N2d9059b20e06a5daN2ddfd090df12e97aN31473208cb51b4ffN31aac7fb9ebcad3fN31d71ba6727cae34N32435653e599af4dN32b07bcbbbcf38e7N330ba542e8b004d4N33e20efec94791f7N34fa1adebc362739N357c86fd6e51f7feN35e6ce78b85de91cN36d69295c0a03cb2N36d9b50550f9bd08N37f7d3543518c703N38d44a73de624f5cN3904ca22d97aeb22N392be6b977550e8dN398f5546a0993636N39f9c1c6001d35c7N39fff53908babd9cN3affeb1ad6128567N3b2dbeb869a81dcbN3b5e74546abb47f0N3b8325ac93540348N3df2aeebe5ea2bbaN3e7cf7ed159accd5N3e8ba2686528dfb0N3f813ba523b1faf6"%lxh.
Ltac2 gd_tbl_P_x509_get_serial () : Init.string Init.list := ["LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.machine_state"; "Corelib.Init.Logic.ex"; "stdpp.bitvector.definitions.bv"; "Corelib.Init.Datatypes.option"; "Corelib.Numbers.BinNums.Z"; "Corelib.Init.Logic.and"; "Corelib.Init.Logic.eq"; "RocqVerifyHarness.AgentSubmission.Lib.MState.MS"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.mkR"; "RocqVerifyHarness.AgentSubmission.Lib.MState.ret_pc"; "Corelib.Init.Datatypes.None"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.seg_rom"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.munch"; "Corelib.Init.Datatypes.cons"; "Corelib.Init.Datatypes.prod"; "Corelib.Init.Datatypes.pair"; "Stdlib.ZArith.BinInt.Z.add"; "Stdlib.ZArith.BinInt.Z.sub"; "stdpp.bitvector.definitions.bv_unsigned"; "Corelib.Init.Datatypes.nil"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.wmono"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.mem_inv"; "stdpp.bitvector.definitions.Z_to_bv"; "Stdlib.ZArith.BinInt.Z.lt"; "Stdlib.ZArith.BinInt.Z.le"; "RocqVerifyHarness.AgentSubmission.Lib.Step.rw_cells"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.cell"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C8"; "RocqVerifyHarness.AgentSubmission.Spec.Rep.buf_cells"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.stk"].


Definition U_X509_GET_SERIAL : Z := 0x27780.
Notation X509_GET_SERIAL_STACK := 32 (only parsing).

Definition x509_get_serial_post (segs : list Segment)
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (PP SER P END lo : Z) (pad : word) (m : mem) : machine_state -> Prop := ltac2:(CDefT.buildp (gd_tbl_P_x509_get_serial ()) "Lms',$0.(1.(2.&40.)Lt0,(2.&40.)(1.(2.&40.)Lt1,(2.&40.)(1.(2.&40.)Lt2,(2.&40.)(1.(2.&40.)La0,(2.&40.)(1.(2.&40.)La1,(2.&40.)(1.(2.&40.)La2,(2.&40.)(1.(2.&40.)La3,(2.&40.)(1.(2.&40.)La4,(2.&40.)(1.(2.&40.)La5,(2.&40.)(1.(2.&40.)La6,(2.&40.)(1.(2.&40.)La7,(2.&40.)(1.(2.&40.)Lt3,(2.&40.)(1.(2.&40.)Lt4,(2.&40.)(1.(2.&40.)Lt5,(2.&40.)(1.(2.&40.)Lt6,(2.&40.)(1.P,(2.&40.)(3.(2.&8.))Lm',P,(2.&40.)(3.(2.&8.))(1.$4.Lr,$4.(1.$4.Lp',$4.(1.(2.&40.)Ltg,(2.&40.)(1.$4.Llen,$4.(1.$4.Lq,$4.(5.(6.$0.R16.(7.(8.O19.O18.O17.O16.R15.R14.R13.O15.O14.R12.R11.R10.R?.R>.R=.R<.R;.O13.O12.O11.O10.O?.O>.O=.O<.O;.O:.R:.R9.R8.R7.)O9.(9.O19.)O8.(:.(2.&40.))R6.(;.O1:.)))(5.(<.(=.(>.$4.$4.)(?.$4.$4.O7.(10.O7.+8.))(=.(>.$4.$4.)(?.$4.$4.O6.(10.O6.+18.))(=.(>.$4.$4.)(?.$4.$4.(11.(12.&40.O18.)+20.)(12.&40.O18.))(13.(>.$4.$4.)))))O1.R6.)(5.(14.O1:.O1.R6.)(5.(15.O1:.R6.)(5.(6.(2.&40.)R12.(16.&40.R5.))(5.(5.(17.-3000.R5.)(18.R5.=))(5.(19.O1:.R6.O7.(=.$1:.(1;.(16.&40.R4.))(13.$1:.)))(5.(19.O1:.R6.O6.(1<.R3.O2.R2.R1.))(5.(1=.O1:.R6.O3.(12.&40.O18.))(5.(5.(18.O5.R4.)(18.R4.O4.))P,(6.$4.R5.=)(5.(18.(10.O5.+2.)R2.)(5.(18.=R3.)(6.$4.(10.R2.R3.)R5.))))))))))))))))))))))))))))))))))")
(* [comment removed for export] *).

Definition x509_get_serial_stmt {L : heap_layout} (segs : list Segment) (ENTRY : Z) : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem)
         (PP SER P END BUF lo : Z) (bs : list byte) (tg0 pad : word) (len0 q0 : Z),
  rw_cells segs m PP [C8 (Z_to_bv 64 P)] ->
  rw_cells segs m SER (buf_cells tg0 pad len0 q0) ->
  bytes_at segs m BUF bs ->
  BUF <= P -> P <= END -> END <= BUF + Z.of_nat (length bs) -> BUF + Z.of_nat (length bs) < 2^63 ->
  (PP + 8 <= SER \/ SER + 24 <= PP) ->
  (PP + 8 <= BUF \/ BUF + Z.of_nat (length bs) <= PP) ->
  (SER + 24 <= BUF \/ BUF + Z.of_nat (length bs) <= SER) ->
  PP mod 8 = 0 -> SER mod 8 = 0 -> 0 < PP -> 0 < SER -> 0 < BUF ->
  stk segs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - X509_GET_SERIAL_STACK -> alloc_ceiling <= lo ->
  bv_unsigned sp mod 16 = 0 ->
  (PP + 8 <= lo \/ bv_unsigned sp <= PP) -> (SER + 24 <= lo \/ bv_unsigned sp <= SER) ->
  (BUF + Z.of_nat (length bs) <= lo \/ bv_unsigned sp <= BUF) ->
  mem_inv segs m ->
  a0 = Z_to_bv 64 PP -> a1 = Z_to_bv 64 END -> a2 = Z_to_bv 64 SER ->
  evt segs (x509_get_serial_post segs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc PP SER P END lo pad m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 ENTRY) fc None m (seg_rom segs)).

Lemma U_x509_get_serial_spec {L : heap_layout} : x509_get_serial_stmt usegs U_X509_GET_SERIAL.
Proof.
  unfold x509_get_serial_stmt, U_X509_GET_SERIAL.
  intros until q0.
  intros HPP HSER HBUF B1 B2 B3 B4 D1 D2 D3 AL1 AL2 NZ1 NZ2 NZ3 ST SLO ACL SPA DS1 DS2 DS3 MI -> -> ->.
  pose proof alloc_ceiling_pos as ACP.
  pose proof (bv_unsigned_in_range 64 sp) as SPR.
  unfold bv_modulus in SPR.
  cbn in SPR.
  pose proof (rw_cells_bound _ _ _ _ HPP) as PPB.
  cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in PPB.
  change (Z.of_nat 8) with 8 in PPB.
  pose proof (rw_cells_bound _ _ _ _ HSER) as SERB.
  cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ buf_cells] in SERB.
  change (Z.of_nat 24) with 24 in SERB.
  pose proof (munch_refl [(PP, PP + 8); (SER, SER + 24); (bv_unsigned sp - 32, bv_unsigned sp)] m) as MU.
  pose proof (wmono_refl usegs m) as WM.
  unfold buf_cells in HSER.
  carve_frame 32%nat ST.
  lxp_split_frame [8;8;8;8]%nat. lxp_seps 32.
  (* [comment removed for export] *)
  pose proof (@sums1_ok) as LXSUMS.
  lxp_run (PLANS [] [] 59%N SUMS1).
  { (* [comment removed for export] *)
    lxp_ret.
  }
  { (* [comment removed for export] *)
    lxp_ret.
  }
  { (* [comment removed for export] *)
    lxp_ret.
  }
  { (* [comment removed for export] *)
    lxp_ret.
  }
Qed.
