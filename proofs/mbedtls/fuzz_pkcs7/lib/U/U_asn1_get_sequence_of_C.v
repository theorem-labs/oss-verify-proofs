(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Walk Asn1Aux AStep CellsX.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Spec Require Import Rep RepFacts.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U Require Import UImg U_asn1_get_tag U_asn1_get_sequence_of_A U_asn1_get_sequence_of_B.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LXP Require Import LxPHeap.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LXP Require Import LxP_Flat.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LXP Require Import LxP_Flat2.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Import OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.LxhSyntax. #[local] Instance lxh_tab : OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.lx_hints := OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.lxh_parse "P00c1d0f87b8653cc 0 4 0 1 20 1 43 1 44 1P0116bdc58f2417bd 2 27 0 6 0 1 2 1 34 1 35 1 45 1 46 1 0 4 0 1 1 1 45 1 46 1P01815f5d309119ed 0 5 0 1 32 1 33 1 43 1 44 1P01fb90a14acc843c 1 1 16 3 0 1 51 1 52 1 7 20 1 38 1 39 1 40 1 50 1 53 1 54 16P02821d0138f1bb19 2 25 0 6 0 1 3 1 35 1 36 1 46 1 47 1 0 4 0 1 2 1 46 1 47 1P032c8204714ab0d4 2 26 0 6 0 1 2 1 34 1 35 1 45 1 46 1 0 4 0 1 1 1 45 1 46 1P03338ed692ad3293 0 5 0 1 32 1 33 1 43 1 44 1P0371839198c4ec45 0 5 0 1 32 1 33 1 43 1 44 1P038f4ba2524284ee 2 25 0 6 0 1 3 1 35 1 36 1 46 1 47 1 0 4 0 1 2 1 46 1 47 1P041c1f9885db90b1 0 5 0 1 39 1 40 1 50 1 51 1P07023a1c9738ecf2 2 39 0 6 0 1 2 1 41 1 42 1 52 1 53 1 0 4 0 1 1 1 52 1 53 1P07d39335a17dcf19 1 1 16 3 1 1 52 1 53 1 7 21 1 39 1 40 1 41 1 51 1 54 1 55 16P07d433a9bf41aac8 2 40 0 6 0 1 2 1 41 1 42 1 52 1 53 1 0 4 0 1 1 1 52 1 53 1P084807ef8bedf4bd 1 1 16 3 0 1 51 1 52 1 7 20 1 38 1 39 1 40 1 50 1 53 1 54 16P08d9496f14c681f6 0 2 0 1 43 1P0972cc283e737732 2 27 0 6 0 1 2 1 34 1 35 1 45 1 46 1 0 4 0 1 1 1 45 1 46 1P0ad840506cb9835d 0 5 0 1 39 1 40 1 50 1 51 1P0bc03c7c5dc3b254 2 27 0 6 0 1 2 1 34 1 35 1 45 1 46 1 0 4 0 1 1 1 45 1 46 1P0c04f2defa4e1025 0 5 0 1 39 1 40 1 50 1 51 1P0c82f67083ba94bd 2 40 0 6 0 1 2 1 41 1 42 1 52 1 53 1 0 4 0 1 1 1 52 1 53 1P0d5ed74d24974549 0 5 0 1 39 1 40 1 50 1 51 1P0d715a236ae6605a 2 39 0 6 0 1 2 1 41 1 42 1 52 1 53 1 0 4 0 1 1 1 52 1 53 1P0dc7cf6a83b1481a 2 40 0 6 0 1 2 1 41 1 42 1 52 1 53 1 0 4 0 1 1 1 52 1 53 1P0e2fe640d1dd8d56 0 4 0 1 20 1 43 1 44 1P0f9dcf0415b86f63 2 38 0 6 0 1 3 1 42 1 43 1 53 1 54 1 0 4 0 1 2 1 53 1 54 1P122a5c115f42d2bf 2 29 0 6 0 1 2 1 36 1 37 1 49 1 50 1 0 4 0 1 1 1 49 1 50 1P1279ea0dec6d1c89 0 5 0 1 39 1 40 1 50 1 51 1P12a31ac78dd24e24 1 1 16 3 1 1 52 1 53 1 7 21 1 39 1 40 1 41 1 51 1 54 1 55 16P13e2b64ce302cdad 2 40 0 6 0 1 2 1 41 1 42 1 52 1 53 1 0 4 0 1 1 1 52 1 53 1P1418f6b0b2dd7d66 1 1 16 3 0 1 51 1 52 1 7 20 1 38 1 39 1 40 1 50 1 53 1 54 16P143dba8574c8bb1e 2 38 0 6 0 1 3 1 42 1 43 1 53 1 54 1 0 4 0 1 2 1 53 1 54 1P1446b9cc34d62cc1 0 5 0 1 39 1 40 1 50 1 51 1P14550fdaa3b9f52c 2 25 0 6 0 1 3 1 35 1 36 1 46 1 47 1 0 4 0 1 2 1 46 1 47 1P14bb0eb3c635e088 0 4 0 1 27 1 50 1 51 1P152716d380c8e287 1 1 16 3 1 1 52 1 53 1 7 21 1 39 1 40 1 41 1 51 1 54 1 55 16P15c176c82f25cc51 2 26 0 6 0 1 2 1 34 1 35 1 45 1 46 1 0 4 0 1 1 1 45 1 46 1P17bb729a8c8db558 0 4 0 1 27 1 50 1 51 1P184909f7b8ccb8b1 0 5 0 1 39 1 40 1 50 1 51 1P1932a8a376547b1f 2 38 0 6 0 1 3 1 42 1 43 1 53 1 54 1 0 4 0 1 2 1 53 1 54 1P199ac5ec9232a772 1 1 16 3 1 1 52 1 53 1 7 21 1 39 1 40 1 41 1 51 1 54 1 55 16P19ca9bcebc3960e7 0 4 0 1 20 1 43 1 44 1P1b28beb10f190cc4 0 5 0 1 39 1 40 1 50 1 51 1P1bdc8cbb2ec96929 2 40 0 6 0 1 2 1 41 1 42 1 52 1 53 1 0 4 0 1 1 1 52 1 53 1P1c0918a76447fdfa 1 1 16 3 1 1 52 1 53 1 7 21 1 39 1 40 1 41 1 51 1 54 1 55 16P1c36967dfbd6f2ab 0 4 0 1 20 1 43 1 44 1P1c4bff7b9bf4a13b 0 4 0 1 20 1 43 1 44 1P1c5e6a44c97467e5 0 4 0 1 27 1 50 1 51 1P1ca33161b013e355 2 27 0 6 0 1 2 1 34 1 35 1 45 1 46 1 0 4 0 1 1 1 45 1 46 1P1f0be427021c4313 2 38 0 6 0 1 3 1 42 1 43 1 53 1 54 1 0 4 0 1 2 1 53 1 54 1P1fe3f272ef20065b 2 28 0 6 0 1 1 1 36 1 37 1 49 1 50 1 0 4 0 1 2 1 49 1 50 1P23e8003005604891 2 38 0 6 0 1 3 1 42 1 43 1 53 1 54 1 0 4 0 1 2 1 53 1 54 1P257c18c363a91034 2 40 0 6 0 1 2 1 41 1 42 1 52 1 53 1 0 4 0 1 1 1 52 1 53 1P26122798590bd4fa 0 5 0 1 32 1 33 1 43 1 44 1P29cb07bc08e4afee 0 5 0 1 32 1 33 1 43 1 44 1P2ab599d5be5b7ec9 0 5 0 1 39 1 40 1 50 1 51 1P2bb3839b7db30165 0 4 0 1 27 1 50 1 51 1P2cb5d36ba74318d4 1 1 16 3 0 1 51 1 52 1 7 20 1 38 1 39 1 40 1 50 1 53 1 54 16P2cbb694c5074b779 0 5 0 1 39 1 40 1 50 1 51 1P2d00965ac89d31af 2 26 0 6 0 1 2 1 34 1 35 1 45 1 46 1 0 4 0 1 1 1 45 1 46 1P2eecc7ee8ccf5ec9 2 25 0 6 0 1 3 1 35 1 36 1 46 1 47 1 0 4 0 1 2 1 46 1 47 1P308d6cbf7eb6b0ef 1 1 16 3 0 1 51 1 52 1 7 20 1 38 1 39 1 40 1 50 1 53 1 54 16P3342de357804ae47 2 26 0 6 0 1 2 1 34 1 35 1 45 1 46 1 0 4 0 1 1 1 45 1 46 1P33443c31ece4a86e 2 27 0 6 0 1 2 1 34 1 35 1 45 1 46 1 0 4 0 1 1 1 45 1 46 1P34b6a9f40d904b6f 1 1 16 3 0 1 51 1 52 1 7 20 1 38 1 39 1 40 1 50 1 53 1 54 16P354bb23aa9260f4a 0 4 0 1 27 1 50 1 51 1P3579d49e6934d690 0 3 0 1 23 1 41 1P35f70c6e4c19ed5a 2 39 0 6 0 1 2 1 41 1 42 1 52 1 53 1 0 4 0 1 1 1 52 1 53 1P3726edc36c958d93 2 26 0 6 0 1 2 1 34 1 35 1 45 1 46 1 0 4 0 1 1 1 45 1 46 1P37293246c82e6661 0 5 0 1 21 1 22 1 42 1 43 1P378ff5b9f7946821 0 5 0 1 39 1 40 1 50 1 51 1P37944354c884d3ec 2 25 0 6 0 1 3 1 35 1 36 1 46 1 47 1 0 4 0 1 2 1 46 1 47 1P37e115476a968890 2 28 0 6 0 1 2 1 36 1 37 1 49 1 50 1 0 4 0 1 1 1 49 1 50 1P3838f56546e67929 2 39 0 6 0 1 2 1 41 1 42 1 52 1 53 1 0 4 0 1 1 1 52 1 53 1P38bcb3275ac152cb 2 39 0 6 0 1 2 1 41 1 42 1 52 1 53 1 0 4 0 1 1 1 52 1 53 1P38be8a2c5039ec51 0 4 0 1 20 1 43 1 44 1P38d719dc4a7834bc 1 1 16 3 1 1 52 1 53 1 7 21 1 39 1 40 1 41 1 51 1 54 1 55 16P38def08d8e39ffb8 0 3 0 1 23 1 41 1P3993f053e4d827e5 2 28 0 6 0 1 1 1 36 1 37 1 49 1 50 1 0 4 0 1 2 1 49 1 50 1P39b9c2c0f0b268ce 0 4 0 1 27 1 50 1 51 1P39d6509c9c9e73e0 2 39 0 6 0 1 2 1 41 1 42 1 52 1 53 1 0 4 0 1 1 1 52 1 53 1P3a949c7629236273 2 25 0 6 0 1 3 1 35 1 36 1 46 1 47 1 0 4 0 1 2 1 46 1 47 1P3cb4aeb514908d96 2 27 0 6 0 1 2 1 34 1 35 1 45 1 46 1 0 4 0 1 1 1 45 1 46 1P3d0deb1a4c2a946a 0 4 0 1 22 1 47 1 48 1P3dbd5bfb4049383a 2 26 0 6 0 1 2 1 34 1 35 1 45 1 46 1 0 4 0 1 1 1 45 1 46 1P3dd801145e012880 2 38 0 6 0 1 3 1 42 1 43 1 53 1 54 1 0 4 0 1 2 1 53 1 54 1P3ddc9c6436b8e42e 0 5 0 1 34 1 35 1 47 1 48 1P3e4b6906e1d60aad 2 27 0 6 0 1 3 1 37 1 38 1 50 1 51 1 0 4 0 1 2 1 50 1 51 1P3ed66a8fc9e9a421 2 28 0 6 0 1 1 1 36 1 37 1 49 1 50 1 0 4 0 1 2 1 49 1 50 1P3f22d0e8d300a357 0 5 0 1 32 1 33 1 43 1 44 1P3f7687a0c413eb1b 0 5 0 1 39 1 40 1 50 1 51 1N0021e746bd6d0665N005fca05499b0e83N00f5b968256bcee2N00f9b7a7c344abd4N012e981271156855N02d3baafb31e8793N03ce535bb1a6e08dN064434ea655e7269N0810ea532ecc9c3eN08900c6bc78487b3N09c748b39e6383beN09f7d765f597c328N0cacde67f0f3e76aN0cbbaae0ff3526baN0dac2767d68082b1N10d8f97f941f8201N1358e3d8236ea0c3N146c4dd1d8ad33b9N15c5624cddb14e07N15cd8e2a0e84307eN169d91ba12cfae94N16b7665811f2bfa6N17985fc33917b83aN1c74a71deae641bbN1f988b2984b9b170N1fab7376345b4e36N205f6b9705d24efcN21958f62175b6cefN21b95adc3864193dN22512047f6ce84c4N22ae891d048f1f4cN239b97f0bea5b44dN23d50d0ed00307a1N24e88d531a9cf10cN25d209fc2b8f79c5N25e876f1237a152cN274cf82ab3f113f4N27b045787e47bd19N28e14684e1abb29eN29573d27168455c8N2978b2b8d38294dcN2ac5319639192a67N2c9b15a59bdfde0aN2d176175e88f94ccN2d969acde6dff2c3N2dd602f6350af770N2ddddf992296c428N2deefb60c1cee6deN2e44d96c71074f9dN3022c76d03544abcN32437aa85c575593N3298914739efa7b9N3413232e719020d9N343346ae0ed8cc8bN34e8fc595d2e1c32N36e442caf38f7148N370441d644fc8325N384e2d49c807db9eN38bd4c676ec07a47N395eac1a57afd0dcN3b92dd08192707cbN3b94e1833b50dc97N3c60ab3b7ea9a1bbN3d6f0d0edc05ceeaN3ef4ebad0b0db955N3f6073003d94d6a0"%lxh.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import LiaOrc. (* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= orc_lia. (* [comment removed for export] *)
Local Ltac dlia ::= orc_dlia. (* [comment removed for export] *)
Local Ltac plia ::= orc_plia. (* [comment removed for export] *)
Local Ltac clear_disj ::= fc_clear_disj. (* [comment removed for export] *)
Local Ltac prune_disj ::= fc_prune_disj. (* [comment removed for export] *)
Ltac2 gd_tbl_P_asn1_get_sequence_of_C () : Init.string Init.list := ["Corelib.Init.Datatypes.list"; "Corelib.Numbers.BinNums.Z"; "stdpp.bitvector.definitions.bv"; "Corelib.Init.Datatypes.option"; "LinuxProcessSemantics.LinuxProcessSem.State.Model"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.HST"; "RocqVerifyHarness.AgentSubmission.U.UImg.usegs"; "RocqVerifyHarness.AgentSubmission.U.U_asn1_get_sequence_of_A.inv"; "RocqVerifyHarness.AgentSubmission.Lib.Step.rw_cells"; "Corelib.Init.Datatypes.cons"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.cell"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C8"; "stdpp.bitvector.definitions.Z_to_bv"; "Corelib.Init.Datatypes.nil"; "Stdlib.ZArith.BinInt.Z.le"; "Stdlib.ZArith.BinInt.Z.add"; "stdpp.bitvector.definitions.bv_unsigned"; "Corelib.Init.Logic.and"; "Stdlib.ZArith.BinInt.Z.lt"; "RocqVerifyHarness.AgentSubmission.Lib.AEvt.aevtM"; "RocqVerifyHarness.AgentSubmission.U.U_asn1_get_sequence_of_A.cb_post"; "RocqVerifyHarness.AgentSubmission.Lib.MState.MS"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.mkR"; "Corelib.Init.Datatypes.None"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.seg_rom"].


Section Walk.
  Variable L : heap_layout.
  Variable HI : heap_iface usegs L.
  Hypothesis HCALLOC : hl_calloc L = U_CALLOC.
  Variables (ra sp gp tp t0 t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : mem) (mo : Model) (h : HST usegs L HI) (LB : list blk)
            (PP CUR P END BUF lo tag : Z) (bs : list byte).
  Hypothesis B1 : BUF <= P.
  Hypothesis B3 : END <= BUF + Z.of_nat (length bs).
  Hypothesis B4 : BUF + Z.of_nat (length bs) < 2^63.
  Hypothesis D1 : PP + 8 <= CUR \/ CUR + 32 <= PP.
  Hypothesis D2 : PP + 8 <= BUF \/ BUF + Z.of_nat (length bs) <= PP.
  Hypothesis D3 : CUR + 32 <= BUF \/ BUF + Z.of_nat (length bs) <= CUR.
  Hypothesis PPB : 0 <= PP /\ PP + 8 <= 2^64.
  Hypothesis CURB : 0 <= CUR /\ CUR + 32 <= 2^64.
  Hypothesis AL1 : PP mod 8 = 0.
  Hypothesis AL2 : CUR mod 8 = 0.
  Hypothesis NZ1 : 0 < PP.
  Hypothesis NZ2 : 0 < CUR.
  Hypothesis NZ3 : 0 < BUF.
  Hypothesis SLO : lo <= bv_unsigned sp - 176 - hl_stack L.
  Hypothesis HLS : 0 <= hl_stack L.
  Hypothesis ACL : alloc_ceiling <= lo.
  Hypothesis ACP : 4096 < alloc_ceiling.
  Hypothesis HTOP : bv_unsigned sp <= heap_top usegs L HI h.
  Hypothesis SPA : bv_unsigned sp mod 16 = 0.
  Hypothesis DHI : hl_data_hi L <= alloc_ceiling.
  Hypothesis DIM1 : hl_img_lo L <= hl_data_lo L.
  Hypothesis DIM2 : hl_data_hi L <= hl_img_hi L.
  Hypothesis DS1 : PP + 8 <= lo \/ bv_unsigned sp <= PP.
  Hypothesis DS2 : CUR + 32 <= lo \/ bv_unsigned sp <= CUR.
  Hypothesis DS3 : BUF + Z.of_nat (length bs) <= lo \/ bv_unsigned sp <= BUF.
  Hypothesis CWPP : client_wrange L LB lo (heap_top usegs L HI h) PP 8.
  Hypothesis CWCUR : client_wrange L LB lo (heap_top usegs L HI h) CUR 32.
  Hypothesis CRBUF : client_range L LB lo BUF (Z.of_nat (length bs)).
  Hypothesis TP : tp = Z_to_bv 64 (hl_tp L).
  Hypothesis SPB : bv_unsigned sp < 2^64.
  Hypothesis HBR0 : Forall (fun b => block_range L (fst b) (snd b)) LB.

  Notation X := [(PP, PP + 8); (CUR, CUR + 32)].
  Notation POST := (asn1_get_sequence_of_post usegs L HI ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc h LB PP CUR P END BUF lo m mo).
  Notation CTX := (bv_unsigned sp + -24).
  (* [comment removed for export] *)
  Notation SPG := (Z_to_bv 64 (bv_unsigned sp + -32)).
  Notation SPT := (Z_to_bv 64 (bv_unsigned sp + -128)).

  Notation INV := (inv L HI ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 m mo h LB PP CUR END BUF lo bs).
  Notation CBPOST := (cb_post L HI ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m mo h LB PP CUR END BUF lo bs).

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  #[local] Ltac lxp_is_protected H ::= lazymatch H with HCALLOC => idtac | B1 => idtac | B3 => idtac | B4 => idtac | D1 => idtac | D2 => idtac | D3 => idtac | PPB => idtac | CURB => idtac | AL1 => idtac | AL2 => idtac | NZ1 => idtac | NZ2 => idtac | NZ3 => idtac | SLO => idtac | HLS => idtac | ACL => idtac | ACP => idtac | HTOP => idtac | SPA => idtac | DHI => idtac | DIM1 => idtac | DIM2 => idtac | DS1 => idtac | DS2 => idtac | DS3 => idtac | CWPP => idtac | CWCUR => idtac | CRBUF => idtac | TP => idtac | SPB => idtac | HBR0 => idtac end.
  Local Ltac2 Set LiaOrc.tbl := fun () => "00R0@D35472118848.174L11061728350.126L11102942022.4  L11143448846.125L15833686629.130L19028967064.131L23825731148.126L24046385023.117L24052734503.120L26049370394.1  L310573225.120  L31844304664.1  L36324901792.5  L38555086715.117L44010973198.173L44017151899.150L44017266586.149L44017268863.131L44022087408.153L48435940554.126L50064525582.125L50079278166.121L53232862556.4  L53445191478.122L54708443204.4  L55232748563.120L57777231065.124L60511893107.128L63370279195.150L64007178605.153L6952084072.1   L7744381536.8   L8698509550.166 L8698569769.129 00001;01<01N02R02Y04S04T06907F07K08e08i09<09=09k0:C0:[0;30;K0<V0<W0?10?C0?D0?V0?W0@b0B40BL0Bf0Bj0CM0CN0COS1L2sp3CUR2lo2bs3SLO3HLS3ACL3ACP2n15nrest2j02j13lst5HLPOS3LXJ4LXJ01y2cs3HszFS3CUR2n15nrest3lstS2sp3CUR3END3BUF2bs2n15nrest2j02j13lst2ll2lp4HLB14HLB24HLB33LXJ4LXJ0S2sp2bsS1L2sp2PP3CUR3END3BUF2lo2bs2B32D12D22D33SLO3HLS3ACL3ACP3DS13DS23DS32n15nrest1q2Lw2Hq3HqL3lst2LR5HLPOS2ll2lp4HLB14HLB24HLB3FS1L2HI2sp1h2lo2bs3SLO3HLS3ACL3ACP2j02j12hc2HT1j2j22j32j42j52j63LXJ4LXJ04LXJ14LXJ24LXJ34LXJ44LXJ54LXJ6S1L2HI2sp1h3CUR2lo2bs3SLO3HLS3ACL3ACP2n15nrest2j02j12hc3lst2HT5HLPOS3LXJ4LXJ0S3CURS1L2sp2lo2bs3SLO3HLS3ACL3ACP2j02j11j2j22j32j42j52j63LXJ4LXJ04LXJ14LXJ24LXJ34LXJ44LXJ54LXJ6S2spS1L4DIM14DIM21y3HXDFS2sp3CUR2bs2n15nrest2j02j13lst3LXJ4LXJ02cs3HszS2sp3CUR2bs2n15nrest3lstS2sp3CUR2bs2n15nrest3lstS2sp3CUR2bs2n15nrest3lstS2sp3CUR2bs2n15nrest3lstS1L2sp3CUR2lo2bs3SLO3HLS3ACL3ACP2n15nrest2j02j13lst4init3EHD5HLPOS3LXJ4LXJ0FS1L2sp2PP3CUR3END3BUF2lo2bs3PPB4CURB3SLO3HLS3ACL3ACP3SPA1q2Lw2cl2cp2j02j12Hq3HqL6HBUFOK2LR1j2j22j32j42j52j63LXJ4LXJ04LXJ14LXJ24LXJ34LXJ44LXJ54LXJ64LXKF2H6S3CUR2n15nrest3lstFS3CUR2n15nrest3lstFS2sp2bs2Lw2j02j12LR1j2j22j32j42j52j63LXJ4LXJ04LXJ14LXJ24LXJ34LXJ44LXJ54LXJ6S1L2sp2PP3CUR3END3BUF2lo2bs2B32D12D22D33SLO3HLS3ACL3ACP3DS13DS23DS31q2Lw2Hq3HqL2LRS2sp3CUR2bs2n15nrest3lstS2sp3CUR2bs2n15nrest3lst1nS2PPS1L3CUR4DIM14DIM22n15nrest3lst4HLD0FF". (* [comment removed for export] *)
  Lemma cb_walk : ltac2:(CDefT.buildp (gd_tbl_P_asn1_get_sequence_of_C ()) "Pnodes,(0.$1.)Pp,$1.Pq,$1.Ptb,$1.PLw,(2.&40.)Pct,(2.&40.)Pcpad,(2.&40.)Ptagw,(2.&40.)Pzpad,(2.&40.)Pcl,$1.Pcp,$1.Pj0,(0.(2.&8.))Pj1,(0.(2.&8.))Px5,(2.&40.)Px6,(2.&40.)Px7,(2.&40.)Px8,(2.&40.)Px9,(2.&40.)Px14,(2.&40.)Px15,(2.&40.)Px16,(2.&40.)Px17,(2.&40.)Px18,(2.&40.)Px19,(2.&40.)Px20,(2.&40.)Px21,(2.&40.)Px22,(2.&40.)Px23,(2.&40.)Px24,(2.&40.)Px25,(2.&40.)Px28,(2.&40.)Px29,(2.&40.)Px30,(2.&40.)Px31,(2.&40.)Pmm,P,(2.&40.)(3.(2.&8.))Pmoc,$4.Phc,(5.$6.VL,VHI,)P,(7.VL,VHI,Vra,Vsp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vm,Vmo,Vh,VLB,VPP,VCUR,VEND,VBUF,Vlo,Vbs,R3.R2.R1.R25.R20.R1?.R1<.R1;.R1>.R1=.R1:.R19.)P,(8.$6.R4.VPP,(9.$:.(;.(<.&40.R25.))(=.$:.)))P,(>.VBUF,R25.)P,(>.(?.R26.(10.&40.R24.))VEND,)P,(11.(>.=R26.)(12.R26.+100.))(13.$6.R7.(14.VL,VHI,Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,Vm,Vmo,Vh,VLB,VPP,VCUR,VEND,VBUF,Vlo,Vbs,R29.R1>.R1:.R19.R14.R13.R12.R11.R10.R?.R>.R=.)(15.(16.(<.&40.+1>;48.)(<.&40.(?.(10.&40.Vsp,)-80.))Vgp,Vtp,R1=.R1<.R1;.R1:.R19.(<.&40.(?.(10.&40.Vsp,)-18.))(<.&40.R27.)(<.&40.R28.)R26.R18.R17.R16.R15.R14.R13.R12.R11.R10.R?.R>.R=.Vs10,Vs11,R<.R;.R:.R9.)VF,(<.&40.+1>=14.)Vfc,(17.(2.&40.))R8.(18.$6.)))")
(* [comment removed for export] *).
  Proof.
  (* [comment removed for export] *)
  intros nodes p q tb Lw ct cpad tagw zpad cl cp j0 j1 x5 x6 x7 x8 x9 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x28 x29 x30 x31 mm moc hc
    INV HPP Hq HqL Htb.
  clear AL1 NZ1 B1.   (* [comment removed for export] *)
  flat constr:(INV) 14%nat. flclear INV. intros HH HT HND HFR HLS' HCUR HBUFOK FRG FRT ST MI HBUF HPX MF.
  pose proof (heap_mok _ _ HI _ _ _ _ HH) as MK.
  pose proof (bv_unsigned_in_range 64 Lw) as LR.
  try (unfold bv_modulus in LR).
  try (cbn in LR).
  pose proof (munch_refl [(bv_unsigned sp - 176, bv_unsigned sp - 128); (CUR, CUR + 32); (bv_unsigned sp - 32, bv_unsigned sp)] mm) as MU.
  pose proof (wmono_refl usegs mm) as WM.
  assert (HSUB : forall b, In b LB -> In b (LBof LB nodes)) by (intros b Hb; unfold LBof; apply in_or_app; right; exact Hb).
  pose proof (client_wrange_mono L _ _ _ _ _ _ CWCUR HSUB) as CWc.
  try (rewrite <- HT in CWc).
  pose proof (client_wrange_mono L _ _ _ _ _ _ CWPP HSUB) as CWp.
  try (rewrite <- HT in CWp).
  assert (HTOPc : bv_unsigned sp <= heap_top usegs L HI hc) by (rewrite HT; exact HTOP).
  try (unfold seq_cells in HCUR).
  destruct nodes as [|n1 nrest].
  carve_frame 48%nat ST.
  lxp_split_frame [8;8;8;8;8;8]%nat.
  (* [comment removed for export] *)
  - (* [comment removed for export] *)
    (* [comment removed for export] *)
      change (last [] CUR) with CUR in *.
    change (hd 0 []) with 0 in *.
    lxp_run (PLAN [0x1eb48; 0x1ed64; 0x3f960] [(0x1ed9c, DMerge 10)] 55%N).
    (* [comment removed for export] *)
    all: first [ lxp_at 126308; (try (assert (HB2 : BUF <= cp /\ 0 <= cl /\ cp + cl <= END) by (destruct HBUFOK as [(E & _)|HB]; [exfalso; clear -E KP NZ3; subst cp; apply KP; reflexivity| exact HB]))); lxp_apply cb_alloc_head | (try (lazymatch goal with |- aevtM _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m9 end)); lxp_ret_open; (try (rewrite <- (Z_to_bv_bv_unsigned Lw) in HCUR)); apply aevtM_done; unfold cb_post; flexi 15%nat; (exists m9, moc, hc, [], (Z_to_bv 64 tb), cpad, (bv_unsigned Lw), q, tagw, zpad, j0, 0); (split; [reflexivity|]); (split; [reflexivity|]); (split; [left; reflexivity|]); (split; [| exact HPP]); unfold inv; (change (last [] CUR) with CUR); (change (hd 0 []) with 0); (try ((flsplit; repeat match goal with |- _ /\ _ => split end); try assumption)); lxp_ret_close ].
  - (* [comment removed for export] *)
    (* [comment removed for export] *)
      pose proof (app_removelast_last CUR (ltac:(discriminate) : n1 :: nrest <> [])) as EN.
    set (init := removelast (n1 :: nrest)) in *.
    set (lst := last (n1 :: nrest) CUR) in *.
    assert (EHD : n1 = hd 0 (init ++ [lst])) by (rewrite <- EN; reflexivity).
    rewrite EN in HH, HND, HFR, HLS', HSUB, CWc, CWp.
    flat constr:((proj1 (seq_lseg_app _ _ _ _ _ _ _ _) HLS')) 2%nat. intros HLSI HLSL.
    try clear HLS'.
    try (cbn [seq_lseg hd] in HLSL).
    flat constr:(HLSL) 5%nat. flclear HLSL. intros HINL HL16 HLPOS FLt1 _. flat constr:(FLt1) 8%nat. flclear FLt1. intros lt lpad ll lp HLST HLB1 HLB2 HLB3.
    try (unfold seq_cells in HLST).
    try (change (hd 0 (n1 :: nrest)) with n1 in HCUR).
    destruct (HFR lst ltac:(apply in_or_app; right; left; reflexivity)) as (HLC & HLD0 & HLAP).
    assert (HLD : lst + 32 <= hl_data_lo L \/ hl_data_hi L <= lst) by (clear -HLD0 DIM1 DIM2; lia).
    assert (ALC : lst + 32 <= CUR \/ CUR + 32 <= lst)
      by (eapply client_wrange_apart; [exact CWCUR | lia | lia | exact ACL | exact HLC | exact HLD | exact HLAP]).
    assert (ALP : lst + 32 <= PP \/ PP + 8 <= lst)
      by (eapply client_wrange_apart; [exact CWPP | lia | lia | exact ACL | exact HLC | exact HLD | exact HLAP]).
    pose proof (bytes_at_bound _ _ _ _ HBUF) as BB.
    assert (ALB : Z.of_nat (length bs) = 0 \/ lst + 32 <= BUF \/ BUF + Z.of_nat (length bs) <= lst).
    {
      destruct (Z.eq_dec (Z.of_nat (length bs)) 0); [left; assumption| right].
      eapply client_range_apart; [exact CRBUF | lia | lia | exact ACL | exact HLC | exact HLD | exact HLAP].
    }
    lxp_run (PLAN [0x1eb48; 0x1ed64; 0x3f960] [(0x1ed9c, DMerge 10)] 55%N).
    (* [comment removed for export] *)
    all: first [ lxp_at 126308; (try (lazymatch goal with |- aevtM _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m5 end)); (try (assert (HLSI' : seq_lseg usegs m5 (LBof LB (init ++ [lst])) BUF END init lst); [> solve [ (eapply (seq_lseg_mem usegs mm m5); [exact HLSI| intros y Hy; eapply seq_lseg_in; [exact HLSI| exact Hy] |]); [> (intros y cs Hy HR Hsz) | idtac .. ]; [> (eapply rw_cells_transport; [exact HR| exact MU| exact WM|]) | idtac .. ]; [> (rewrite Hsz) | idtac .. ]; [> (destruct (HFR y ltac:(apply in_or_app; left; exact Hy)) as (HXC & HXD & HXAP)) | idtac .. ]; [> (assert (AXC : y + 32 <= CUR \/ CUR + 32 <= y)
          by (eapply client_wrange_apart; [exact CWCUR | lia | lia | exact ACL | exact HXC | clear -HXD DIM1 DIM2; lia | exact HXAP])) | idtac .. ]; [> (cbn [disjoint_from]) | idtac .. ]; [> (generalize AXC HXC; dlia) | idtac .. ] ] | idtac .. ])); lxp_apply cb_alloc_tail; (try (solve [ lia ])); (try (solve [ destruct HBUFOK as [(E1 & E2 & E3)|HB]; [exfalso; discriminate| right; exact HB] ])) | lxp_dead ].
  Unshelve. all: try lxp_default.   (* [comment removed for export] *)
Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
End Walk.
