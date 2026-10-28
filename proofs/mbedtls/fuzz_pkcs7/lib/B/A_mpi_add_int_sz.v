(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Arr CellsX HeapIface MpiCoreAux MpiWalkAux Asn1Aux ZBridge.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Spec Require Import Rep RepFacts MpiVal MpiFacts MpiOpnd.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.P Require Import P_mpi_addsub P_mpi_add_int.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import AImg AImgGlobals AImgRT A_rt_facts A_alloc_lib A_mpi_stmtA A_mpi_opnd A_mpi_journey A_mpi_copy A_mpi_add_abs_W A_mpi_add_sub A_mpi_add_abs_sz A_mpi_sub_abs_sz A_mpi_add_sub_sz A_mpi_read_binary_stmt A_mpi_stmtA_sz A_mpi_add_int.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BLX Require Import LxA.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LXB Require Import LxATac LxARt.
Local Ltac lxg_b8u := repeat match goal with H : context [Z_to_bv 8 (bv_unsigned (Z_to_bv 64 ?z))] |- _ => let k := eval vm_compute in (Z.modulo (bv_unsigned (Z_to_bv 64 z)) 256) in replace (Z_to_bv 8 (bv_unsigned (Z_to_bv 64 z))) with (Z_to_bv 8 k) in H by (apply bv_eq; vm_compute; reflexivity) end.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Ltac2 gd_tbl_A_mpi_add_int_sz () : Init.string Init.list := ["Corelib.Numbers.BinNums.Z"; "Corelib.Init.Logic.and"; "Stdlib.ZArith.BinInt.Z.le"; "Stdlib.ZArith.BinInt.Z.opp"; "Stdlib.ZArith.BinInt.Z.pow"; "Stdlib.ZArith.BinInt.Z.lt"; "Corelib.Init.Logic.eq"; "RocqVerifyHarness.AgentSubmission.LX.LxExpr.zswrap"; "RocqVerifyHarness.AgentSubmission.LX.LxExpr.zlow"; "Stdlib.ZArith.BinInt.Z.add"; "Stdlib.ZArith.BinInt.Z.lxor"; "Stdlib.ZArith.BinInt.Z.shiftr"; "RocqVerifyHarness.AgentSubmission.P.P_mpi_add_int.abs_limb_expr"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.machine_state"; "Corelib.Init.Logic.ex"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.HST"; "RocqVerifyHarness.AgentSubmission.B.AImg.asegs"; "stdpp.bitvector.definitions.bv"; "Corelib.Init.Datatypes.option"; "RocqVerifyHarness.AgentSubmission.Lib.MState.MS"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.mkR"; "stdpp.bitvector.definitions.Z_to_bv"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_addr"; "RocqVerifyHarness.AgentSubmission.LibA.ALazy.al_sb"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_AL"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_stmtA.A_ADD_SUB_MPI"; "Corelib.Init.Datatypes.None"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.seg_rom"; "Stdlib.ZArith.BinInt.Z.sub"; "stdpp.bitvector.definitions.bv_unsigned"; "Stdlib.ZArith.BinInt.Z.modulo"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.HM"; "Corelib.Init.Datatypes.cons"; "Corelib.Init.Datatypes.prod"; "Corelib.Init.Datatypes.pair"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.hcs"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.htop"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.hstkhi"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.hflag"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.havol"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.hfr"; "LinuxProcessSemantics.LinuxProcessSem.State.Model"; "Corelib.Init.Logic.iff"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.HK"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.fresh_apart"; "RocqVerifyHarness.AgentSubmission.Lib.Step.rw_cells"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.cell"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C8"; "Corelib.Init.Datatypes.nil"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C2"; "RocqVerifyHarness.AgentSubmission.P.P_mpi_add_int.sgn_of"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C4"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C1"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.stk"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.mem_inv"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.presW"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_stklo"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.ivl"; "RocqVerifyHarness.AgentSubmission.LibA.AEvtA.evtA"; "WalkI.Call.S1P"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_add_int.A_MPI_ADD_INT_E"; "RocqVerifyHarness.AgentSubmission.Lib.MState.ret_pc"; "Corelib.Init.Datatypes.list"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.blk"; "RocqVerifyHarness.AgentSubmission.LibA.ALazy.crange"; "Stdlib.Lists.List.In"; "Corelib.Init.Logic.or"; "WalkI.Call.EPOST"; "RocqVerifyHarness.AgentSubmission.Spec.Rep.limb_own"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_own"; "RocqVerifyHarness.AgentSubmission.Spec.Rep.LStatic"; "Stdlib.ZArith.BinInt.Z.mul"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_n"; "Corelib.Init.Datatypes.bool"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.ro_addr"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.wa"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_p"; "Corelib.Init.Datatypes.true"; "RocqVerifyHarness.AgentSubmission.B.AImgGlobals.img_norz"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_stmtA.mpd_aobjA"; "RocqVerifyHarness.AgentSubmission.LibA.AUnw.uwc"; "RocqVerifyHarness.AgentSubmission.LibA.AEvtS.aevtS"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_stmtA.mpi_binop_postA"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_stmtA_sz.add_int_Rsz"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_add_int.add_int_PHI"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_add_int.add_int_FR"; "LinuxProcessSemantics.LinuxProcessSem.Run.mkCfg"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.art_layout"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.artA"; "RocqVerifyHarness.AgentSubmission.B.AImg.asan_img_ok"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_uar_got"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_add_int.A_UAR_GOT_M"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_smalloc"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_add_int.A_SMALLOC_1_M"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_need_smalloc"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_read_binary_stmt.arl_need_rt"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_add_sub_sz.add_sub_mpi_stmtA_oz"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.hl_img_lo"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_L"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.hl_data_lo"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.hl_data_hi"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.hl_img_hi"; "mpi_add_int_stmtA_z"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_stmtA.A_MPI_ADD_INT"].

(* [comment removed for export] *)
Lemma lx_abs_limb : ltac2:(CDefT.buildp (gd_tbl_A_mpi_add_int_sz ()) "Pb,$0.P,(1.(2.(3.(4.+2.+1?.))R1.)(5.R1.(4.+2.+1?.)))(6.$0.(7.+20.(8.+20.(9.(:.R2.(;.R2.+1?.))(3.(;.R2.+1?.)))))(<.R2.))")
(* [comment removed for export] *).
Proof.
  intros b Hb. unfold zswrap, zlow, abs_limb_expr.
  change 18446744073709551616%Z with (2^64)%Z.
  unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus. cbn [Z.of_N N.sub].
  change (2 ^ Z.of_N 32)%Z with (2^32)%Z.
  replace (2 ^ 32 `div` 2)%Z with (2^31)%Z by reflexivity.
  change (2 ^ (32 - 1))%Z with (2^31)%Z.
  rewrite !Z.shiftr_div_pow2 by lia.
  destruct (Z.ltb_spec b 0) as [NEG|POS].
  - assert (D : (b / 2 ^ 31 = -1)%Z).
    { symmetry. apply (Z.div_unique b (2^31) (-1) (b + 2^31)); lia. }
    rewrite D. rewrite Z.lxor_m1_r. unfold Z.lnot.
    assert (E1 : (b mod 2^64 = 2^64 + b)%Z) by (rewrite <- (Z.mod_add _ 1) by lia; rewrite Z.mod_small; lia).
    rewrite E1.
    assert (E2 : ((2^64 + b + 2^31) mod 2^32 - 2^31 = b)%Z).
    { replace (2^64 + b + 2^31)%Z with ((b + 2^31) + 2^32 * 2^32)%Z by lia. rewrite Z.mod_add by lia. rewrite Z.mod_small; lia. }
    rewrite E2. rewrite D.
    replace (((-1 + 2^31) mod 2^32 - 2^31))%Z with (-1)%Z by reflexivity.
    replace ((-1) mod 2^64)%Z with (2^64 - 1)%Z by reflexivity.
    change (2^64 - 1)%Z with 18446744073709551615%Z. rewrite OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.MpiWalkAux.lxor_allones64 by lia.
    replace (Z.pred (- b) + - (-1))%Z with (-b)%Z by lia.
    rewrite (Z.mod_small (-b) (2^32)) by lia.
    replace (18446744073709551615 - (2 ^ 64 + b) - 18446744073709551615 + 2^31)%Z with ((- b + 2^31) + (- 2^32) * 2^32)%Z by lia.
    rewrite Z.mod_add by lia.
    reflexivity.
  - rewrite (Z.div_small b) by lia.
    rewrite Z.lxor_0_r. rewrite (Z.mod_small b (2^64)) by lia.
    replace (b + - 0)%Z with b by lia. rewrite (Z.mod_small b (2^32)) by lia.
    assert (E2 : ((b + 2^31) mod 2^32 - 2^31 = b)%Z) by (rewrite Z.mod_small; lia). rewrite !E2.
    rewrite (Z.div_small b) by lia.
    replace ((0 + 2 ^ 31) mod 2 ^ 32 - 2 ^ 31)%Z with 0%Z by reflexivity. change (0 mod 2^64)%Z with 0%Z.
    rewrite Z.lxor_0_r. rewrite Z.sub_0_r. rewrite !E2. reflexivity.
Qed.

From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import ACnt24 AUnw. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibB Require Import TacA.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import A_frame_lib A_frame_kit.   (* [comment removed for export] *)
Import ListNotations.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LXA Require Import LxFlat.
Import OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.LxhSyntax. #[local] Instance lxh_tab : OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.lx_hints := OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.lxh_parse "P002f2ce0c8190725 0 4 0 1 46 1 58 1 59 1P008cfd2b66faed57 1 1 16 3 0 1 82 1 83 1 8 45 1 68 1 71 1 72 1 73 1 81 1 84 1 85 16P00c05d3c9fbbfc9d 0 7 0 1 26 1 56 1 57 1 58 1 61 1 62 1P0201ccc79ee2d82b 0 3 0 1 37 1 67 1P02349da67b43d56b 0 4 0 1 68 1 69 1 70 1P03718d9bf9fca41a 1 2 32 3 0 1 85 1 88 1 32 3 1 1 86 1 87 1 2 89 2 90 2P037bacad8f3b090a 1 2 16 2 0 1 60 1 16 2 1 1 59 1 2 61 1 62 1P0384c7bd574fb530 0 4 0 1 46 1 58 1 59 1P043d1217a15c9113 1 2 32 3 0 1 84 1 87 1 32 8 43 1 48 1 71 1 74 1 75 1 76 1 85 1 86 1 2 88 1 89 1P05837880a6945a98 1 1 16 3 1 1 33 1 59 1 7 40 1 46 1 49 1 50 1 51 1 60 1 61 16P05c09a51e5c1e550 0 4 0 1 46 1 58 1 59 1P05d76a6414886134 0 4 0 1 46 1 58 1 59 1P05f517c702c5633e 0 6 0 1 48 1 49 1 50 1 58 1 59 1P065ac81ed75ccece 0 4 0 1 46 1 58 1 59 1P066f74ee88c83d5e 0 6 0 1 48 1 49 1 50 1 58 1 59 1P07070ce2e6ed4410 0 4 0 1 46 1 58 1 59 1P07f7f0e9ddf67dd4 1 2 32 3 0 1 86 1 87 1 32 3 1 1 85 1 88 1 2 89 2 90 2P0831e7346ac819f7 1 1 16 3 1 1 33 1 59 1 7 40 1 46 1 49 1 50 1 51 1 60 1 61 16P086763ab58f01cbb 0 6 0 1 26 1 68 1 70 1 73 1 74 1P092c822d2793507d 0 5 0 1 48 1 50 1 58 1 59 1P09d29bfa296e0eaf 0 4 0 1 56 1 57 1 58 1P09ec1e33a88b3434 1 2 16 3 0 1 34 1 60 1 16 3 1 1 33 1 59 1 2 61 1 62 1P0aa5cc7a282357c8 1 1 64 2 9 1 80 1 3 0 1 81 1 82 64P0ae46e08abaa5f88 1 1 16 4 1 1 35 1 37 1 59 1 7 40 1 46 1 49 1 50 1 51 1 60 1 61 16P0b25fdbdaeb6794c 0 6 0 1 48 1 49 1 50 1 58 1 59 1P0b76a1917d2414c9 1 2 32 3 0 1 81 1 84 1 32 3 1 1 82 1 83 1 2 85 2 86 2P0c6b39621359ba7c 1 1 16 3 0 1 86 1 87 1 8 49 1 72 1 75 1 76 1 77 1 85 1 88 1 89 16P0d40f0eb8297bb4c 0 4 0 1 68 1 69 1 70 1P0dc81fffe6d2e113 0 3 0 1 37 1 67 1P0df10213e4b0e98c 1 1 16 4 1 1 35 1 37 1 59 1 7 40 1 46 1 49 1 50 1 51 1 60 1 61 16P0e9baf08812b91e1 1 2 32 3 0 1 80 1 83 1 32 8 39 1 44 1 67 1 70 1 71 1 72 1 81 1 82 1 2 84 1 85 1P0f965841b70fbf2a 1 1 16 3 0 1 82 1 83 1 8 45 1 68 1 71 1 72 1 73 1 81 1 84 1 85 16P0faf6d856eb6da74 0 6 0 1 48 1 49 1 50 1 58 1 59 1P0fb05f82c84f369b 0 3 0 1 37 1 67 1P10ec812e212ac7e0 0 5 0 1 48 1 50 1 58 1 59 1P1424c7bf57547854 1 1 16 3 0 1 81 1 82 1 8 44 1 67 1 70 1 71 1 72 1 80 1 83 1 84 16P1488c45a4024903f 1 1 64 2 0 1 80 1 3 6 1 81 1 82 64P1583d0878e0ab813 1 2 32 3 0 1 81 1 84 1 32 3 1 1 82 1 83 1 2 85 2 86 2P15bc58dc87ef4653 1 1 64 2 47 1 62 1 3 0 1 61 1 63 64P1644875d1527942b 1 1 16 4 1 1 35 1 37 1 59 1 7 40 1 46 1 49 1 50 1 51 1 60 1 61 16P16636b1feda7c494 0 4 0 1 68 1 69 1 70 1P16a82529ad2bea89 1 1 16 3 0 1 81 1 82 1 4 58 1 80 1 83 1 84 16P172a732bd09fb0e9 0 5 0 1 48 1 50 1 58 1 59 1P18d8627d7aa7ed52 1 2 32 3 0 1 84 1 87 1 32 8 43 1 48 1 71 1 74 1 75 1 76 1 85 1 86 1 2 88 1 89 1P192172cda07c0c3a 1 2 16 2 0 1 60 1 16 2 1 1 59 1 2 61 1 62 1P195cfc633e09f4c2 0 4 0 1 68 1 69 1 70 1P19894188dde007a7 1 1 16 4 1 1 35 1 37 1 59 1 7 40 1 46 1 49 1 50 1 51 1 60 1 61 16P19a9a559bbd7b15e 1 1 16 2 1 1 59 1 7 40 1 46 1 49 1 50 1 51 1 60 1 61 16P1a5770fe7786ee00 1 1 16 3 0 1 86 1 87 1 8 49 1 72 1 75 1 76 1 77 1 85 1 88 1 89 16P1abead3410824be5 1 2 16 3 0 1 34 1 60 1 16 3 1 1 33 1 59 1 2 61 1 62 1P1b195389c57eb3d0 1 1 16 4 1 1 35 1 37 1 59 1 7 40 1 46 1 49 1 50 1 51 1 60 1 61 16P1ba58df0ca47efe7 1 2 16 3 0 1 34 1 60 1 16 3 1 1 33 1 59 1 2 61 1 62 1P1c2e01a1047a90cf 0 3 0 1 37 1 67 1P1de6d8d782e85022 0 4 0 1 25 1 73 1 74 1P1e8d6c03e66eb93b 0 4 0 1 68 1 69 1 70 1P1f129e824e605183 0 3 0 1 37 1 67 1P1f414d2127dcb549 1 1 16 4 1 1 35 1 37 1 59 1 7 40 1 46 1 49 1 50 1 51 1 60 1 61 16P201bb99977d01dd2 1 2 32 3 0 1 86 1 87 1 32 3 1 1 85 1 88 1 2 89 2 90 2P204c4d5367e1729e 0 4 0 1 25 1 73 1 74 1P207fda8db8eedacb 1 1 16 2 0 1 58 1 3 4 1 59 1 60 16P2114a9beb01ad157 1 1 16 3 0 1 85 1 86 1 4 62 1 84 1 87 1 88 16P21c4a5309b80ec91 0 6 0 1 48 1 49 1 50 1 58 1 59 1P21d86eaa32b898db 1 1 16 3 0 1 82 1 83 1 8 45 1 68 1 71 1 72 1 73 1 81 1 84 1 85 16P22581340aa19050a 0 4 0 1 46 1 58 1 59 1P22fb25b4b3955cfe 0 6 0 1 48 1 49 1 50 1 58 1 59 1P231cd15ffe238201 0 6 0 1 48 1 49 1 50 1 58 1 59 1P232ba5bc60657b6e 0 4 0 1 68 1 69 1 70 1P234824dbadbe348d 0 7 0 1 43 1 74 1 75 1 76 1 84 1 85 1P2494c2fd34c851cd 0 5 0 1 48 1 50 1 58 1 59 1P24eb5a683252d3e0 1 1 64 2 0 1 61 1 3 2 1 62 1 63 64P24fe518a2e915c77 0 6 0 1 43 1 74 1 76 1 84 1 85 1P25ee0adabf9f6f08 0 6 0 1 59 1 62 1 72 1 84 1 85 1P2615922b27ddc389 1 1 16 2 1 1 59 1 7 40 1 46 1 49 1 50 1 51 1 60 1 61 16P26efd9b527ef2355 0 8 0 1 47 1 51 1 57 1 58 1 59 1 62 1 63 1P28b8e19e74500c23 1 1 64 2 0 1 84 1 3 4 1 85 1 86 64P28e90ca44bb140f2 1 2 16 2 0 1 60 1 16 2 1 1 59 1 2 61 1 62 1P29cf2803abbf98d3 0 2 0 1 84 1P29d46b1dacce5883 1 1 16 4 1 1 35 1 37 1 59 1 7 40 1 46 1 49 1 50 1 51 1 60 1 61 16P2a5afe98b3c83815 0 3 0 1 37 1 67 1P2ac33d432a62bad8 1 2 16 2 0 1 60 1 16 2 1 1 59 1 2 61 1 62 1P2b6842f77e16d0e6 0 4 0 1 46 1 58 1 59 1P2bd57e5330a4e872 0 5 0 1 48 1 50 1 58 1 59 1P2bdd82765f6a81f0 0 4 0 1 46 1 58 1 59 1P2c350f19a0f3a7c6 0 5 0 1 48 1 50 1 58 1 59 1P2c7aa50bf57b39ca 1 1 16 3 1 1 33 1 59 1 7 40 1 46 1 49 1 50 1 51 1 60 1 61 16P2ccd9c5dc5f2594d 0 3 0 1 37 1 67 1P2d49556d9d0b8dfa 0 6 0 1 25 1 37 1 55 1 61 1 62 1P2d9d9d5c31c4249e 0 4 0 1 68 1 69 1 70 1P2e64ee8b76472dbe 0 6 0 1 48 1 49 1 50 1 58 1 59 1P2e677f70ef5af653 1 1 16 3 0 1 86 1 87 1 8 49 1 72 1 75 1 76 1 77 1 85 1 88 1 89 16P2e9769974a20230b 1 2 32 3 0 1 85 1 88 1 32 3 1 1 86 1 87 1 2 89 2 90 2P2f115e8199d8f96d 0 6 0 1 39 1 70 1 72 1 80 1 81 1P307417c30ab015be 1 2 32 3 0 1 86 1 87 1 32 3 1 1 85 1 88 1 2 89 2 90 2P309b9caa72f61730 1 1 16 4 1 1 35 1 37 1 59 1 7 40 1 46 1 49 1 50 1 51 1 60 1 61 16P30b785c900b906d4 1 1 16 3 1 1 33 1 59 1 7 40 1 46 1 49 1 50 1 51 1 60 1 61 16P30bf963e70f6e2b8 0 3 0 1 41 1 45 1P319e3d8fd5ce07ba 1 2 32 3 0 1 81 1 84 1 32 3 1 1 82 1 83 1 2 85 2 86 2P32c18778c1c5b35b 1 2 32 3 0 1 85 1 88 1 32 3 1 1 86 1 87 1 2 89 2 90 2P34143f67b3005fcc 1 2 32 3 0 1 62 1 65 1 32 3 1 1 63 1 64 1 2 66 2 67 2P342b70c04fe08899 1 1 16 2 1 1 59 1 7 40 1 46 1 49 1 50 1 51 1 60 1 61 16P343baaa3e122c722 0 5 0 1 48 1 50 1 58 1 59 1P346446d6708dcba3 0 5 0 1 70 1 72 1 80 1 81 1P34f0b0fedfe1ea8b 1 1 16 2 1 1 59 1 7 40 1 46 1 49 1 50 1 51 1 60 1 61 16P3508f042e855ab74 1 2 16 3 0 1 34 1 60 1 16 3 1 1 33 1 59 1 2 61 1 62 1P35223c8cee51f32d 1 2 16 3 0 1 34 1 60 1 16 3 1 1 33 1 59 1 2 61 1 62 1P3561ef038237b1e1 0 3 0 1 38 1 40 1P35d9f7db101bcb25 1 2 16 2 0 1 60 1 16 2 1 1 59 1 2 61 1 62 1P361d0db1c8883c64 1 2 64 2 0 1 85 1 64 2 10 1 84 1 2 86 1 87 1P36c95715e43266fe 1 1 16 4 1 1 35 1 37 1 59 1 7 40 1 46 1 49 1 50 1 51 1 60 1 61 16P373654a73bba8354 1 2 32 3 0 1 85 1 88 1 32 3 1 1 86 1 87 1 2 89 2 90 2P3873077ac94ca01d 0 4 0 1 25 1 73 1 74 1P3950e1a1611213fa 0 4 0 1 68 1 69 1 70 1P399f98531ad11388 1 1 16 3 0 1 86 1 87 1 4 63 1 85 1 88 1 89 16P3a0ccb83f9c2ffb2 0 4 0 1 25 1 73 1 74 1P3b2044266aff77eb 0 3 0 1 37 1 55 1P3c4399d87b08b48e 0 6 0 1 48 1 49 1 50 1 58 1 59 1P3c48bdff3fa6e20e 0 3 0 1 37 1 67 1P3d52a061168adab4 1 1 16 2 28 1 58 1 3 0 1 59 1 60 16P3df929b0fd802b2c 0 5 0 1 48 1 50 1 58 1 59 1P3e417711037af291 0 2 0 1 23 1P3ed378fddd1fd109 1 1 16 3 0 1 86 1 87 1 8 49 1 72 1 75 1 76 1 77 1 85 1 88 1 89 16P3edf03f6b72203a6 0 5 0 1 48 1 50 1 58 1 59 1P3ef355e18f191494 0 2 0 1 24 1P3ffc3ffebb357bc7 1 1 64 2 1 1 61 1 3 0 1 62 1 63 64N008cfece00cad1abN030eb9f84e2b2013N03cfedaa517ba500N03f15668709fdf46N046d2aa1e19b46c2N04a656221d3a308aN0544fd651d95f595N06572015abf1da73N07aa249e9fcaea72N07bd033100041588N087feb6e1ef9d13fN0c371269dc93f48bN0c5d44690ffcf586N0d4695d344ad39edN0d53df139461ef18N10a979ad99aafa08N12a6685a472e3a58N13f33de30d9defffN14c0866497528b07N1542877e59473e04N15e1c34ddce30e23N167b6e3131ee66afN1812925eca8e36b1N19f6f950a926aed0N1b3a7ffc3f0c9837N1c77b8d7273275daN1cc97ab06131eb20N1cfe1962487d3b5dN1dfae2dc9863c355N258c6ea8908d8108N26c1ddc5cf09e34aN279bc774a516d961N279c9b2fbf7313e3N27beda0e7af0818dN2898f504163dde2eN295e09c60488a951N29616c8cce9bf387N2a5c4de83cbf957eN2df4390814fd3c4bN2f9189a9e0186877N31dacdb90cb6d892N32db9725d059199cN38d64db842f4854dN3ac1fbcfc62bf218N3e289bf0b10ba47dN3f725ca6c9fad4ddN3fe6f3d0931a9cff"%lxh.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibB Require Import FF5. (* [comment removed for export] *)
Local Ltac pqlia ::= ff5_pqlia.
Local Ltac transport_after_call segs m m' MU WM ::= ff5_transport_after_call segs m m' MU WM.
Local Ltac solve_apart ::= ff5_solve_apart.
Local Ltac solve_apart0 ::= ff5_solve_apart0.
Local Ltac solve_disjoint ::= ff5_solve_disjoint.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
(* [comment removed for export] *)
Local Ltac2 e25kn_keep_near (t : Init.constr) : Init.unit :=
  let seed := FF5.ffn_vars (FSet.empty FSet.Tags.ident_tag) t in
  let e := LiaTuning.zf_mkenv () in
  let (ids, _) := List.fold_left (fun acc h =>
      let (ids, cache) := acc in
      let (id, body, ty) := h in
      match body with
      | Init.Some _ => acc
      | Init.None =>
          let (isp, cache) := LiaTuning.zf_is_prop cache ty in
          if isp then
            (if LiaTuning.zf_plain_arith e ty then
               (if FSet.is_empty (FSet.inter seed (FF5.ffn_vars (FSet.empty FSet.Tags.ident_tag) ty))
                then (id :: ids, cache) else (ids, cache))
             else (id :: ids, cache))
          else (ids, cache)
      end) ([], { LiaTuning.zc_c := FMap.empty FSet.Tags.constant_tag; LiaTuning.zc_i := FMap.empty FSet.Tags.inductive_tag })
      (Control.hyps ()) in
  match ids with
  | [] => ()
  | _ :: _ => match Control.case (fun () => Std.clear ids) with
              | Init.Val _ => ()
              | Init.Err _ => List.iter (fun id => match Control.case (fun () => Std.clear [id]) with Init.Val _ => () | Init.Err _ => () end) ids
              end
  end.
Ltac ff_keep_near t ::= let f := ltac2:(t |- e25kn_keep_near (Option.get (Ltac1.to_constr t))) in f t.
Unset Lia Cache.

Definition mpi_add_int_stmtA_z segs R HIA ENTRY := mpi_intop_stmtA_r segs R HIA ENTRY C24_ADD_INT add_int_Rsz.

Section WalkI.
  Variable R : art_layout.
  #[local] Hint Extern 0 heap_layout => exact (arl_L R) : typeclass_instances.
  Variable HIA : artA asegs R.
  Local Notation AL := (arl_AL R).
  Local Notation L := (arl_L R).
  Hypothesis IMG : asan_img_ok AL.
  Local Instance lxi : LxImg asegs AL := lxA_img AL IMG.   (* [comment removed for export] *)
  Hypothesis UARG : arl_uar_got R = A_UAR_GOT_M.
  Hypothesis SM1 : arl_smalloc R 1 = A_SMALLOC_1_M.
  Hypothesis NS1 : 0 <= arl_need_smalloc R.
  Hypothesis NEEDR : 0 <= arl_need_rt R.
  Hypothesis HAS : add_sub_mpi_stmtA_oz 1 asegs R HIA A_ADD_SUB_MPI.
  Hypothesis DIMG : hl_img_lo L <= hl_data_lo L /\ hl_data_hi L <= hl_img_hi L.
  Hypothesis ROIMG : forall a, ro_addr asegs (wa a) = true -> 0 <= a < 2^64 -> hl_img_lo L <= a < hl_img_hi L.

  Section Call.
  Variables (h : HST asegs R HIA) (LB LF : list blk).
  Local Notation CS := (hcs asegs R HIA h).
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) (mo0 : Model)
            (dX dA : mpd) (b lo d : Z).
  Hypothesis BB : -2^31 <= b < 2^31.
  Hypothesis LOS : arl_stklo R <= lo.
  Hypothesis SLO : lo <= bv_unsigned sp - 496 - arl_need_rt R.
  Hypothesis SLOS : lo <= bv_unsigned sp - 112 - arl_need_smalloc R.
  Hypothesis TOP : bv_unsigned sp <= htop asegs R HIA h.
  Hypothesis SPA : bv_unsigned sp mod 16 = 0.
  Hypothesis TPV : tp = Z_to_bv 64 (arl_tp R).
  Hypothesis LFB : (length LF < 512)%nat.

  Ltac rt_facts :=
    pose proof (hcs_ok asegs R HIA h) as CSOK;
    pose proof (cs_ok_sb _ _ CSOK) as SB64;
    pose proof (art_alwf asegs R HIA) as ALWF'; unfold al_wf in ALWF';
    pose proof IMG as IMG'; unfold asan_img_ok in IMG';
    pose proof (art_uar_img asegs R HIA) as UIMG;
    pose proof (art_lo asegs R HIA) as ALO;
    pose proof (alloc_ceiling_pos (L := arl_L R)) as ACP; pose proof (alloc_ceiling_val R) as ACV;
    unfold A_UAR_GOT_M in UARG; unfold A_SMALLOC_1_M in SM1;
    pose proof (hcs_stack asegs R HIA h) as SCS0;
    pose proof (bv_unsigned_in_range 64 sp) as SPR; unfold bv_modulus in SPR; cbn [Z.pow Z.of_N Pos.pow] in SPR.

  Local Notation FSHXL :=
    [C1 (Z_to_bv 8 241); C1 (Z_to_bv 8 241); C1 (Z_to_bv 8 241); C1 (Z_to_bv 8 241); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0);
     C1 (Z_to_bv 8 242); C1 (Z_to_bv 8 242); C1 (Z_to_bv 8 4);
     C1 (Z_to_bv 8 243); C1 (Z_to_bv 8 243); C1 (Z_to_bv 8 243); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)].
  Local Notation SAVEL := [C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

  (* [comment removed for export] *)
  Definition S1P : machine_state -> Prop := ltac2:(CDefT.buildp (gd_tbl_A_mpi_add_int_sz ()) "Lms,$=.(>.$0.LFB,$0.(>.$0.Lsp1,$0.(>.(?.$10.VR,VHIA,)Lh1,(?.$10.VR,VHIA,)(>.P,(11.&40.)(12.(11.&8.))Lm1,P,(11.&40.)(12.(11.&8.))(>.(11.&40.)Lt0,(11.&40.)(>.(11.&40.)Lt1,(11.&40.)(>.(11.&40.)Lt2,(11.&40.)(>.(11.&40.)La4,(11.&40.)(>.(11.&40.)La5,(11.&40.)(>.(11.&40.)La6,(11.&40.)(>.(11.&40.)La7,(11.&40.)(>.(11.&40.)Lt3,(11.&40.)(>.(11.&40.)Lt4,(11.&40.)(>.(11.&40.)Lt5,(11.&40.)(>.(11.&40.)Lt6,(11.&40.)(>.(11.&40.)Lw0,(11.&40.)(>.(11.&40.)Lw1,(11.&40.)(>.(11.&40.)Lw2,(11.&40.)(>.(11.&40.)Lpadw,(11.&40.)(1.(6.$=.R14.(13.(14.(15.&40.+9<>1<.)(15.&40.R12.)Vgp,Vtp,R?.R>.R=.Vsp,(15.&40.R12.)(15.&40.(16.VdX,))(15.&40.(16.VdA,))(15.&40.(9.R13.+20.))(15.&40.+1.)R<.R;.R:.R9.(15.&40.R13.)(15.&40.Vb,)(15.&40.(9.(;.R13.+3.)(17.(18.VR,))))(15.&40.R13.)(15.&40.(17.(18.VR,)))Vs7,Vs8,Vs9,Vs10,Vs11,R8.R7.R6.R5.)VF,(15.&40.$19.)Vfc,(1:.(11.&40.))R10.(1;.$10.)))(1.(1.(2.(1<.(1=.&40.Vsp,)+70.)R12.)(2.R12.(1<.(1=.&40.Vsp,)+60.)))(1.(6.$0.(1>.R12.+20.)=)(1.(1?.$10.VR,VHIA,R11.VLB,(20.(21.$0.$0.)(22.$0.$0.R13.+80.)VLF,)R10.)(1.(6.P,$0.Sp(23.$10.VR,VHIA,R11.)(23.$10.VR,VHIA,Vh,))(1.(6.$0.(24.$10.VR,VHIA,R11.)(24.$10.VR,VHIA,Vh,))(1.(6.$0.(25.$10.VR,VHIA,R11.)(25.$10.VR,VHIA,Vh,))(1.(6.$0.(26.$10.VR,VHIA,R11.)(26.$10.VR,VHIA,Vh,))(1.(6.$0.(27.$10.VR,VHIA,R11.)(27.$10.VR,VHIA,Vh,))(1.(6.$0.(28.$10.VR,VHIA,R11.)(28.$10.VR,VHIA,Vh,))(1.Pmo,$29.(2:.(2;.$10.VR,VHIA,R12.R1.)(2;.$10.VR,VHIA,Vh,R1.))(1.(6.$0.(1>.R13.+40.)=)(1.(2<.VR,VLB,VLF,R13.+80.)(1.(2=.$10.R10.R13.(20.$2>.(2?.R4.)(20.$2>.(2?.R3.)(20.$2>.(2?.R2.)(30.$2>.)))))(1.(2=.$10.R10.(9.R13.+20.)(20.$2>.(2?.(15.&40.(9.R13.+40.)))(20.$2>.(31.(15.&40.(32.Vb,)))(20.$2>.(31.(15.&40.+1.))(20.$2>.(33.R1.)(30.$2>.))))))(1.(2=.$10.R10.(9.R13.+40.)(20.$2>.(33.(15.&40.(<.Vb,)))(30.$2>.)))(1.(2=.$10.R10.(9.(;.R13.+3.)(17.(18.VR,)))(20.$2>.(34.(15.&8.+?1.))(20.$2>.(34.(15.&8.+?1.))(20.$2>.(34.(15.&8.+?1.))(20.$2>.(34.(15.&8.+?1.))(20.$2>.(34.(15.&8.=))(20.$2>.(34.(15.&8.=))(20.$2>.(34.(15.&8.+?2.))(20.$2>.(34.(15.&8.+?2.))(20.$2>.(34.(15.&8.+4.))(20.$2>.(34.(15.&8.+?3.))(20.$2>.(34.(15.&8.+?3.))(20.$2>.(34.(15.&8.+?3.))(20.$2>.(34.(15.&8.=))(20.$2>.(34.(15.&8.=))(20.$2>.(34.(15.&8.=))(20.$2>.(34.(15.&8.=))(30.$2>.))))))))))))))))))(1.(2=.$10.R10.(9.(1=.&40.Vsp,)-40.)(20.$2>.(2?.Vs6,)(20.$2>.(2?.Vs5,)(20.$2>.(2?.Vs4,)(20.$2>.(2?.Vs3,)(20.$2>.(2?.Vs2,)(20.$2>.(2?.Vs1,)(20.$2>.(2?.Vs0,)(20.$2>.(2?.Vra,)(30.$2>.))))))))))(1.(2=.$10.R10.(9.R12.+18.)(20.$2>.(2?.(15.&40.R13.))(30.$2>.)))(1.(35.$10.R10.R12.(9.R12.+18.))(1.(35.$10.R10.(9.R12.+20.)(9.(1=.&40.Vsp,)-40.))(1.(35.$10.R10.Vlo,R12.)(1.(36.$10.R10.)(37.$10.VR,VHIA,Vh,VLB,VLF,(1=.&40.Vsp,)(38.VR,)(30.$39.)Vm,R10.)))))))))))))))))))))))))))))))))))))))))))")
(* [comment removed for export] *).

  (* [comment removed for export] *)
  #[local] Ltac lx_pins_hook ::= try lx_pin1 d; try lx_pin1 mo0; try lx_pin1 ROIMG; try lx_pin1 DIMG; try lx_pin1 HAS.   (* [comment removed for export] *)
  #[using="LFB TPV SPA TOP SLOS SLO LOS BB NEEDR NS1 SM1 UARG IMG"]
  Lemma pro_walk : ltac2:(CDefT.buildp (gd_tbl_A_mpi_add_int_sz ()) "Pt0,(11.&40.)Pt1,(11.&40.)Pt2,(11.&40.)Pa3,(11.&40.)Pa4,(11.&40.)Pa5,(11.&40.)Pa6,(11.&40.)Pa7,(11.&40.)Pt3,(11.&40.)Pt4,(11.&40.)Pt5,(11.&40.)Pt6,(11.&40.)P,(1?.$10.VR,VHIA,Vh,VLB,VLF,Vm,)P,(35.$10.Vm,Vlo,(1=.&40.Vsp,))P,(36.$10.Vm,)(3:.$10.(18.VR,)(23.$10.VR,VHIA,Vh,)$3;.(13.(14.Vra,Vsp,Vgp,Vtp,R?.R>.R=.Vs0,Vs1,(15.&40.(16.VdX,))(15.&40.(16.VdA,))(15.&40.Vb,)R<.R;.R:.R9.R8.Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,R7.R6.R5.R4.)VF,(15.&40.$3<.)Vfc,(1:.(11.&40.))Vm,(1;.$10.)))")
(* [comment removed for export] *).
  Proof.
  intros until t6.
  intros HH ST MI.
  unfold A_MPI_ADD_INT_E.
  rt_facts.
  pose proof (hm_top asegs R HIA h LB LF _ HH) as HTOP.
  assert (SCS : crange CS lo (bv_unsigned sp - lo)) by (eapply crange_sub; [exact SCS0| qlia| qlia]).
  pose proof (hm_wlow asegs R HIA h LB LF m HH) as WL.
  pose proof (presW_init asegs R HIA h LB LF m (bv_unsigned sp) (arl_stklo R) [] HH ltac:(clear; lia)) as PRES.
  flat constr:(IMG') 3%nat. flclear IMG'. intros EGOT ELO EHI.
  carve_frame 96%nat ST.
  (* [comment removed for export] *)
  lazymatch goal with |- _ (MS _ _ _ _ _ ?mc _) =>
  lazymatch goal with HHc : HM _ _ _ h LB LF mc |- _ =>
  pose proof (hm_abase asegs R HIA h LB LF mc HHc) as AB;
  pose proof (abase_got _ _ _ AB) as GOT; pose proof (abase_gsb _ _ _ AB) as GSB;
  (flat constr:((hm_auar asegs R HIA h LB LF mc HHc)) 2%nat; intros UGOT UFLAG);
  pose proof (hm_flag_img asegs R HIA h LB LF mc HHc) as FLIMG
  end end.
  rewrite EGOT in GOT.
  rewrite UARG in UGOT.
  lxr_pose.
  lx_pre. lx_run_tac (PLAN [0x5306c] [] 160%N). lx_tree. all: try (let f := fresh "lxh" in rename H into f).
  lxr_leaf. lx_carry.
  lx_align32 sp1.
  assert (SP1 : bv_unsigned sp - 112 <= sp1 <= bv_unsigned sp - 96) by (lx_prune; clear_disj; lia).
  assert (SP1M : sp1 mod 32 = 0) by (lx_prune; clear_disj; lia).
  assert (SP1R : 0 <= sp1 < 2^64) by (first [ clear - SP1 SPR SLO LOS ALO ACV NEEDR; lia | lx_side_lia ]).
  try clear GOT. try clear GSB. try clear UGOT. try clear UFLAG. try clear AB. try clear FLIMG.
  (* [comment removed for export] *)
  lazymatch goal with |- _ (MS _ _ _ _ _ ?mc _) => rename mc into m1 end.
      destruct (stk_split asegs m1 lo sp1 (bv_unsigned sp + -96) ST ltac:(first [ clear - SP1 SLOS NS1; lia | lx_side_lia ])) as [ST1 ST2]. clear ST.
      replace (Z_to_bv 64 340076) with (Z_to_bv 64 (arl_smalloc R 1)) by (rewrite SM1; reflexivity).
      lazymatch goal with HHc : HM _ _ _ h LB LF m1 |- _ =>
      callrt sp1 (eapply (art_smalloc asegs R HIA 1) with (lo := lo) (sz := 96); rewrite ?(unsigned_lit sp1) by exact SP1R;
                  first [ exact HHc | exact LFB | reflexivity | exact TPV | exact LOS | exact ST1
                  | first [ clear - SLOS SP1 TOP NS1; lia | lx_side_lia ]
                  | clear; lia
                  | assumption | assumption | reflexivity | lx_arith | lx_side_lia | lx_app | match goal with |- ?g => idtac "SMPRE-LEFT:" g end ])
      end.
      all: match goal with |- evtA _ _ _ _ _ => idtac | |- ?g => idtac "SMALLOC-LEFT:" g end.
      try clear ST1.
      lazymatch goal with H : presA _ _ _ _ _ _ _ _ m1 ?m2 |- _ => rename H into HP1; rename m2 into m2' end.
      try clear HH.
      presA_transport HP1. clear HP1.
      lazymatch goal with H : exists h' : HST _ _ _, _ |- _ =>
        (flat constr:(H) 9%nat; flclear H; intros h1 Ehcs Ehtop Estk Eflag Evol Efr HKI SMC) end.
      flat constr:(SMC) 8%nat. flclear SMC. intros FB junkf Ea0 F64 FRSH HH1 FRM FSH. lazymatch type of Ea0 with ?x = _ => subst x end.
      cbn [Z.mul Z.pow Z.pow_pos Pos.iter Pos.mul Z.to_nat Pos.to_nat Pos.iter_op Nat.add Nat.mul] in FRSH, HH1, FRM, FSH.
      (* [comment removed for export] *)
      zstep. zstep. zstep. zstep.
      zstep. if_cases Kb; zify_cond Kb.
      2:{ exfalso. flat constr:(FRSH) 3%nat. flclear FRSH. intros F0 F1 _.
          try (change 18446744073709551615 with (Z.ones 64) in Kb; rewrite Z.land_ones in Kb by (clear; lia)).
          rewrite ?Z.mod_small in Kb by (first [ clear - F0 F1 ALO ACV LOS SLO SPR; lia | lx_side_lia ]). clear - Kb F0 F1 ALO ACV LOS SLO SPR. lia. }
      try clear Kb.
      change (64 * 2 ^ 1) with 128 in *. change (8 * 2 ^ 1) with 16 in FSH. change (Z.to_nat 128) with 128%nat in FRM. change (Z.to_nat 16) with 16%nat in FSH.
      lazymatch goal with |- _ (MS _ _ _ _ _ ?mc _) => rename mc into m3 end.
      (* [comment removed for export] *)
      destruct (frame_factsA R HIA CS h1 LB LF m3 FB 128 lo HH1 Ehcs FRSH F64 ltac:(clear; lia) ltac:(reflexivity) LOS)
        as (CFB & INF & INH & IND & AP & (F0 & F1 & F2 & F3) & F8 & FBLO & SBND & APS). change (128 / 8) with 16 in SBND, APS. change (128 - 40) with 88 in IND.
      pose proof (art_stk_high asegs R HIA) as STKH.
      (* [comment removed for export] *)
      lazymatch goal with FRx : rw_cells _ m3 (bv_unsigned sp + -96) _ |- _ => chunk_split FRx 2%nat FRa SAVE end.
      replace (bv_unsigned sp + -96 + 32) with (bv_unsigned sp + -64) in SAVE by (clear; lia).
      lazymatch goal with STx : stk _ m3 sp1 (bv_unsigned sp + -96) |- _ => release_frame FRa STx (bv_unsigned sp + -64); rename STx into STJ end.
      destruct (stk_split asegs m3 sp1 (sp1 + 32) (bv_unsigned sp + -64) STJ ltac:(first [ clear - SP1; lia | lx_side_lia ])) as [STlo SThi]. clear STJ.
      destruct (stk_carve asegs m3 sp1 (sp1 + 32) 8 STlo ltac:(clear; lia)) as [STlo' [jslot SLOT]].
      replace (sp1 + 32 - Z.of_nat 8) with (sp1 + 24) in STlo', SLOT by (clear; lia). clear STlo. rename STlo' into STlo.
      cb8_to_c8 SLOT (@nil cell).
      (* [comment removed for export] *)
      apply (rw_cells_split_CB asegs m3 FB [] 128 junkf [] [8; 8; 8; 8; 8; 2; 2; 4; 16; 4; 60]%nat) in FRM; [| reflexivity].
      cbn [mk_CB_cells app] in FRM.
      chunk_split FRM 3%nat FHD FRM1. chunk_split FRM1 1%nat FLNK FRM2. chunk_split FRM2 4%nat BST FRM3. chunk_split FRM3 1%nat RZC FRM4. chunk_split FRM4 1%nat LMB FREST.
      lazymatch type of BST with rw_cells _ _ ?a _ => replace a with (FB + 32) in BST by (clear; lia) end.
      lazymatch type of LMB with rw_cells _ _ ?a _ => replace a with (FB + 64) in LMB by (clear; lia) end.
      try clear FLNK. try clear FREST. try clear RZC.
      cb8_to_c8 FHD (@nil cell).
      cbn [zcells] in FSH.
  (* [comment removed for export] *)
  lx_mkR. lxr_pose. try lxg_b8u.
  lx_pre. lx_run_tac (PLAN [0x9cddc] [] 160%N). lx_tree. all: try (let f := fresh "lxh" in rename H into f).
  lxr_leaf. lx_carry.
  try (match goal with H : context [zswrap 32 (zlow 32 (Z.lxor ?bb (Z.shiftr ?bb 31) + - Z.shiftr ?bb 31))] |- _ => rewrite (lx_abs_limb bb) in H by (first [ assumption | lx_side_lia ]) end).
  try (match goal with H : rw_cells _ _ (Z.shiftr FB 3 + al_sb AL) _ |- _ => norm_b8 H; rename H into FSHX end).
  try (match goal with H : rw_cells _ _ (Z.shiftr _ 3 + al_sb _) _ |- _ => rename H into FSHX end).
  frame_aobj FSHX (FB + 32) 2%nat as OBS.
  (* [comment removed for export] *)
  lx_mkR. lxr_pose. try lxg_b8u.
  lx_pre. lx_run_tac (PLAN [0x9cdfc] [] 160%N). lx_tree. all: try (let f := fresh "lxh" in rename H into f).
  lxr_leaf. lx_carry.
  try (match goal with H : context [zswrap 32 (zlow 32 (Z.lxor ?bb (Z.shiftr ?bb 31) + - Z.shiftr ?bb 31))] |- _ => rewrite (lx_abs_limb bb) in H by (first [ assumption | lx_side_lia ]) end).
  (* [comment removed for export] *)
      lazymatch goal with |- _ (MS _ _ _ _ _ ?mx _) => lazymatch goal with HHc : HM _ _ _ h1 _ _ mx |- _ => pose proof (hm_abase asegs R HIA h1 LB _ mx HHc) as AB2 end end.
  (* [comment removed for export] *)
  lx_mkR. lxr_pose. try lxg_b8u.
  lx_pre. lx_run_tac (PLAN [0x9e9e0] [] 160%N). lx_tree. all: try (let f := fresh "lxh" in rename H into f).
  lxr_leaf. lx_carry.
  try (match goal with H : context [zswrap 32 (zlow 32 (Z.lxor ?bb (Z.shiftr ?bb 31) + - Z.shiftr ?bb 31))] |- _ => rewrite (lx_abs_limb bb) in H by (first [ assumption | lx_side_lia ]) end).
  try clear AB2. try clear OBS.
      lazymatch goal with |- _ (MS _ _ _ _ _ ?mx _) => rename mx into m9 end.
      match goal with H : rw_cells _ m9 (FB + 32) _ |- _ => rename H into BST9 end.
      match goal with H : rw_cells _ m9 (FB + 64) _ |- _ => rename H into LMB9 end.
      fold (abs_limb_expr b) in LMB9.
      lazymatch type of BST9 with rw_cells _ _ _ [C8 ?pp; C2 ?sw; C2 ?one; CB 4 ?j2] =>
        pose proof (rw_cells_C2_congr asegs m9 (FB + 32) [C8 pp] _ (sgn_of b) [C2 one; CB 4 j2] BST9 (sign_half_val b BB)) as BST';
        cbn [app] in BST'; clear BST9; set (jB := j2) in BST' end.
      change (rw_cells asegs m9 (FB + 32) ([C8 (Z_to_bv 64 (FB + 64)); C2 (Z_to_bv 64 (sgn_of b)); C2 (Z_to_bv 64 1)] ++ [CB 4 jB])) in BST'.
      apply rw_cells_app in BST'. flat constr:(BST') 2%nat. flclear BST'. intros BS1 BJ. cbn [cells_size csize Nat.add] in BJ.
      pose proof (cells_CB4_C4 asegs m9 _ jB BJ) as BJ'.
      pose proof (rw_cells_join2 asegs m9 _ _ _ BS1 BJ') as BST2. cbn [cells_size csize Nat.add app] in BST2.
      try clear BS1. try clear BJ. try clear BJ'.
  apply evtA_done. unfold S1P.
      lazymatch goal with |- context [MS _ _ _ _ _ ?mx _] => exists FB, sp1, h1, mx end.
      do 11 eexists. exists (Z_to_bv 64 1102416563), (Z_to_bv 64 95139), (Z_to_bv 64 642240), (le_bytes_to_word jB).
      split; [ first [ reflexivity | apply lx_MS_regs; apply mkR_eq31; first [ reflexivity | (f_equal; lia) | (apply bv_eq; rewrite ?Z_to_bv_unsigned; cbn; lia) ] ] | ].
      split; [exact SP1|]. split; [exact SP1M|].
      split; [exact HH1|]. split; [exact Ehcs|]. split; [exact Ehtop|]. split; [exact Estk|]. split; [exact Eflag|]. split; [exact Evol|]. split; [exact Efr|]. split; [exact HKI|].
      split; [exact F64|]. split; [exact FRSH|].
      split; [exact FHD|]. split; [exact BST2|]. split; [exact LMB9|].
      split; [exact FSHX|].
      split; [exact SAVE|]. split; [exact SLOT|]. split; [exact STlo|]. split; [exact SThi|].
      split; [assumption|]. split; [assumption|].
      exact PRES.
Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition EPOST (h3 : HST asegs R HIA) (LBa LBb : list blk) (m0 m2x : mem) (WA WB : list ivl) (r : Z)
      : machine_state -> Prop := ltac2:(CDefT.buildp (gd_tbl_A_mpi_add_int_sz ()) "Lms,$=.(>.P,(11.&40.)(12.(11.&8.))Lm',P,(11.&40.)(12.(11.&8.))(>.(?.$10.VR,VHIA,)Lh4,(?.$10.VR,VHIA,)(>.(11.&40.)Lt0,(11.&40.)(>.(11.&40.)Lt1,(11.&40.)(>.(11.&40.)Lt2,(11.&40.)(>.(11.&40.)La1,(11.&40.)(>.(11.&40.)La2,(11.&40.)(>.(11.&40.)La3,(11.&40.)(>.(11.&40.)La4,(11.&40.)(>.(11.&40.)La5,(11.&40.)(>.(11.&40.)La6,(11.&40.)(>.(11.&40.)La7,(11.&40.)(>.(11.&40.)Lt3,(11.&40.)(>.(11.&40.)Lt4,(11.&40.)(>.(11.&40.)Lt5,(11.&40.)(>.(11.&40.)Lt6,(11.&40.)(1.(6.$=.R11.(13.(14.Vra,Vsp,Vgp,Vtp,R>.R=.R<.Vs0,Vs1,(15.&40.O1.)R;.R:.R9.R8.R7.R6.R5.Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,R4.R3.R2.R1.)VF,(3=.Vra,)Vfc,(1:.(11.&40.))R10.(1;.$10.)))(1.(36.$10.R10.)(1.(35.$10.R10.Vlo,(1=.&40.Vsp,))(1.(37.$10.VR,VHIA,O8.O7.VLF,(1=.&40.Vsp,)(38.VR,)O3.O5.R10.)(1.(37.$10.VR,VHIA,O8.O6.VLF,(1=.&40.Vsp,)(38.VR,)O2.O4.R10.)(1.(6.P,$0.Sp(23.$10.VR,VHIA,R?.)(23.$10.VR,VHIA,O8.))(1.(6.$0.(24.$10.VR,VHIA,R?.)(24.$10.VR,VHIA,O8.))(1.(6.$0.(25.$10.VR,VHIA,R?.)(25.$10.VR,VHIA,O8.))(1.(6.$0.(26.$10.VR,VHIA,R?.)(26.$10.VR,VHIA,O8.))(1.(6.$0.(27.$10.VR,VHIA,R?.)(27.$10.VR,VHIA,O8.))(1.(6.$0.(28.$10.VR,VHIA,R?.)(28.$10.VR,VHIA,O8.))(1.Pmo,$29.(2:.(2;.$10.VR,VHIA,R10.R1.)(2;.$10.VR,VHIA,O8.R1.))(1?.$10.VR,VHIA,R?.O6.VLF,R10.)))))))))))))))))))))))))))))")
(* [comment removed for export] *).

  #[local] Ltac lx_pins_hook ::= try lx_pin1 TPV; try lx_pin1 SPA; try lx_pin1 SLOS; try lx_pin1 BB; try lx_pin1 d; try lx_pin1 b; try lx_pin1 dA; try lx_pin1 dX; try lx_pin1 mo0; try lx_pin1 m; try lx_pin1 s6; try lx_pin1 s5; try lx_pin1 s4; try lx_pin1 s3; try lx_pin1 s2; try lx_pin1 s1; try lx_pin1 s0; try lx_pin1 ra; try lx_pin1 LB; try lx_pin1 ROIMG; try lx_pin1 DIMG; try lx_pin1 HAS; try lx_pin1 NS1; try lx_pin1 SM1; try lx_pin1 UARG.   (* [comment removed for export] *)
  #[using="LFB TOP SLO LOS NEEDR IMG"]
  Lemma epi_walk : ltac2:(CDefT.buildp (gd_tbl_A_mpi_add_int_sz ()) "Ph3,(?.$10.VR,VHIA,)PLBa,(3>.$3?.)PLBb,(3>.$3?.)Pm0,P,(11.&40.)(12.(11.&8.))Pm2x,P,(11.&40.)(12.(11.&8.))Pmm,P,(11.&40.)(12.(11.&8.))PWA,(3>.$39.)PWB,(3>.$39.)PFB,$0.Psp1,$0.Pxra,(11.&40.)Pt0,(11.&40.)Pt1,(11.&40.)Pt2,(11.&40.)Pa1,(11.&40.)Pa2,(11.&40.)Pa3,(11.&40.)Pa4,(11.&40.)Pa5,(11.&40.)Pa6,(11.&40.)Pa7,(11.&40.)Pt3,(11.&40.)Pt4,(11.&40.)Pt5,(11.&40.)Pt6,(11.&40.)Ps3v,(11.&40.)Ps6v,(11.&40.)Pw0,(11.&40.)Pw1,(11.&40.)Pw2,(11.&40.)Pr,$0.P,(1?.$10.VR,VHIA,R1?.R1=.(20.(21.$0.$0.)(22.$0.$0.R17.+80.)VLF,)R1:.)P,Px,$0.P,(23.$10.VR,VHIA,Vh,R1.)(23.$10.VR,VHIA,R22.R2.)P,(6.$0.(24.$10.VR,VHIA,R21.)(24.$10.VR,VHIA,Vh,))P,(6.$0.(25.$10.VR,VHIA,R22.)(25.$10.VR,VHIA,Vh,))P,(1.(2.(1<.(1=.&40.Vsp,)+70.)R1:.)(2.R1:.(1<.(1=.&40.Vsp,)+60.)))P,(6.$0.(1>.R1;.+20.)=)P,(6.$0.(1>.R1=.+40.)=)P,(2<.VR,R25.VLF,R1>.+80.)P,(2<.VR,R25.VLF,R1?.+80.)P,(40.(23.$10.VR,VHIA,Vh,)R20.+80.)P,PB,$0.Pj,$0.P,(41.(21.$0.$0.)(22.$0.$0.R2.R1.)VLF,)(42.(2.(9.R24.+80.)R3.)(2.(9.R3.R2.)R24.))P,Pb',$3?.P,(41.$3?.R1.R2:.)(41.$3?.R2.R2:.)P,(2=.$10.R26.R23.(20.$2>.(2?.R10.)(20.$2>.(2?.R?.)(20.$2>.(2?.R>.)(30.$2>.)))))P,(2=.$10.R27.(9.(;.R24.+3.)(17.(18.VR,)))(20.$2>.(34.(15.&8.+?1.))(20.$2>.(34.(15.&8.+?1.))(20.$2>.(34.(15.&8.+?1.))(20.$2>.(34.(15.&8.+?1.))(20.$2>.(34.(15.&8.=))(20.$2>.(34.(15.&8.=))(20.$2>.(34.(15.&8.+?2.))(20.$2>.(34.(15.&8.+?2.))(20.$2>.(34.(15.&8.+4.))(20.$2>.(34.(15.&8.+?3.))(20.$2>.(34.(15.&8.+?3.))(20.$2>.(34.(15.&8.+?3.))(20.$2>.(34.(15.&8.=))(20.$2>.(34.(15.&8.=))(20.$2>.(34.(15.&8.=))(20.$2>.(34.(15.&8.=))(30.$2>.))))))))))))))))))P,(2=.$10.R28.(9.(1=.&40.Vsp,)-40.)(20.$2>.(2?.Vs6,)(20.$2>.(2?.Vs5,)(20.$2>.(2?.Vs4,)(20.$2>.(2?.Vs3,)(20.$2>.(2?.Vs2,)(20.$2>.(2?.Vs1,)(20.$2>.(2?.Vs0,)(20.$2>.(2?.Vra,)(30.$2>.))))))))))P,(2=.$10.R29.(9.R25.+18.)(20.$2>.(2?.(15.&40.R26.))(30.$2>.)))P,(35.$10.R2:.R26.(9.R26.+18.))P,(35.$10.R2;.(9.R27.+20.)(9.(1=.&40.Vsp,)-40.))P,(35.$10.R2<.Vlo,R28.)P,(36.$10.R2=.)P,(37.$10.VR,VHIA,R33.R32.VLF,(1=.&40.Vsp,)(38.VR,)R2=.R30.R2>.)P,(37.$10.VR,VHIA,R34.R32.VLF,(1=.&40.Vsp,)(38.VR,)R2=.R30.R2?.)(3:.$10.(18.VR,)(23.$10.VR,VHIA,R35.)(43.R35.R34.R33.R32.R31.R2?.R2>.R17.)(13.(14.R2;.(15.&40.R2<.)Vgp,Vtp,R2:.R29.R28.Vsp,(15.&40.R2<.)(15.&40.R17.)R27.R26.R25.R24.R23.R22.R21.(15.&40.R2=.)R1<.(15.&40.(9.(;.R2=.+3.)(17.(18.VR,))))(15.&40.R2=.)R1;.Vs7,Vs8,Vs9,Vs10,Vs11,R20.R1?.R1>.R1=.)VF,(15.&40.+9<>1<.)Vfc,(1:.(11.&40.))R30.(1;.$10.)))")
(* [comment removed for export] *).
  Proof.
  intros until r.
  intros HH3 HCS3 ET3 ES3 SP1 SP1M F64 FRSH FRSH3 CFB AP SUBK FHD FSH SAVE SLOT ST24 SThi STlo MI PRES PRES2.
  rt_facts.
  pose proof (hcs_ok asegs R HIA h3) as CSOK3.
  pose proof (hm_top asegs R HIA h3 _ _ _ HH3) as HTOP3.
  rewrite ET3, ES3 in HTOP3.
  assert (SP1R : 0 <= sp1 < 2^64) by (first [ clear - SP1 SPR SLO LOS ALO ACV NEEDR; lia | lx_side_lia ]).
  assert (CFB3 : crange (hcs asegs R HIA h3) FB 128) by (eapply crange_mono; [exact HCS3| exact CFB]).
  assert (SCS : crange CS lo (bv_unsigned sp - lo)) by (eapply crange_sub; [exact SCS0| first [ clear - LOS; lia | lx_side_lia ]| first [ clear - SLO NEEDR TOP HTOP3; lia | lx_side_lia ]]).
  assert (SCS3 : crange (hcs asegs R HIA h3) lo (bv_unsigned sp - lo)) by (eapply crange_mono; [exact HCS3| exact SCS]).
  assert (SCS03 : crange (hcs asegs R HIA h3) (arl_stklo R) (hstkhi asegs R HIA h - arl_stklo R)) by (eapply crange_mono; [exact HCS3| exact SCS0]).
  destruct (frame_factsA R HIA (hcs asegs R HIA h3) h3 LBb LF mm FB 128 lo HH3 eq_refl FRSH3 F64 ltac:(clear; lia) ltac:(reflexivity) LOS)
  as (_ & INF & INH3 & IND3 & _ & _ & F8 & FBLO & SBND & APS).
  change (128 / 8) with 16 in SBND, APS.
  pose proof FRSH as FRSH'.
  unfold fresh_apart in FRSH'.
  flat constr:(FRSH') 4%nat. flclear FRSH'. intros F0 F1 F2 F3.
  pose proof (art_stk_high asegs R HIA) as STKH.
  pose proof (hm_wlow asegs R HIA h3 _ _ _ HH3) as WL3.
  (* [comment removed for export] *)
  lxr_pose.
  lx_pre. lx_run_tac (PLAN [0x9ce80] [] 160%N). lx_tree. all: try (let f := fresh "lxh" in rename H into f).
  lxr_leaf. lx_carry.
  try (lazymatch goal with |- _ (MS _ _ _ _ _ ?mx _) => try match goal with MUx : munch _ _ mx |- _ => clear MUx end; try match goal with WMx : wmono _ _ mx |- _ => clear WMx end end).
  lazymatch goal with |- _ (MS _ _ _ _ _ ?mx _) => rename mx into me end.
  (* [comment removed for export] *)
  match goal with H : HM _ _ _ h3 _ _ me |- _ => rename H into HHe end.
  destruct (hm_fake_free asegs R HIA h3 LBb ((FB, 128) :: LF) me FB 128 HHe ltac:(left; reflexivity))
  as (p & h4 & ROp & [old Hold] & CRp & NCp & NSp & HM4 & E4cs & E4top & E4stk & E4flag & E4vol & E4fr & HKI4).
  replace (FB + 128 - 8) with (FB + 120) in ROp by (clear; lia).
  pose proof (rw_cells_bound _ _ _ _ Hold) as PB.
  cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in PB.
  pose proof (store_ok_of_rw1 _ _ _ _ Hold) as HSp.
  clear Hold.
  assert (SUB1 : forall b', In b' (LBa ++ fdata LF) -> In b' (LBb ++ fdata ((FB, 128) :: LF))).
  { intros b' Hb. apply in_app_iff in Hb. apply in_app_iff. destruct Hb as [Hb|Hb]; [left; apply SUBK; exact Hb| right]. eapply fdata_incl; [| exact Hb]. intros fb Hfb. right. exact Hfb. }
  assert (SUB2 : forall b', In b' (LBb ++ fdata LF) -> In b' (LBb ++ fdata ((FB, 128) :: LF))) by (intros b' Hb; apply fdata_cons_sub; exact Hb).
  assert (NP5 : bv_unsigned sp + -64 + 64 <= p \/ p + 1 <= bv_unsigned sp + -64).
  { eapply (nc_apart _ _ _ (arl_stklo R) _ p); [exact NCp| apply client_range_stack; first [ clear - SLO LOS NEEDR; lia | lx_side_lia ]| intros b' Hb; exact Hb| clear; lia| clear; lia]. }
  assert (NP6 : sp1 + 24 + 8 <= p \/ p + 1 <= sp1 + 24).
  { eapply (nc_apart _ _ _ (arl_stklo R) _ p); [exact NCp| apply client_range_stack; first [ clear - SLO LOS SP1 NEEDR; lia | lx_side_lia ]| intros b' Hb; exact Hb| clear; lia| clear; lia]. }
  assert (WCp1 : wcover R LBa LF (bv_unsigned sp) WA p 1) by (eapply wcover_nc; [exact NCp| exact SUB1| first [ clear - LOS SLO NEEDR; lia | lx_side_lia ]]).
  assert (WCp2 : wcover R LBb LF (bv_unsigned sp) WB p 1) by (eapply wcover_nc; [exact NCp| exact SUB2| first [ clear - LOS SLO NEEDR; lia | lx_side_lia ]]).
  clear HHe NCp NSp FHD.
  repeat match goal with H : rw_cells _ me (Z.shiftr FB 3 + al_sb AL) _ |- _ => clear H| H : rw_cells _ me (Z.shiftr FB 3 + al_sb AL + _) _ |- _ => clear H end.
  zstep.
  zstep.
  fake_free_done p HSp.
  (* [comment removed for export] *)
  lx_mkR. lx_pre. lx_run_tac (PLAN [] [] 40%N). lx_tree. all: try (let f := fresh "lxh" in rename H into f). subst lxm.
  lazymatch goal with |- _ (MS _ _ _ _ _ ?mx _) => rename mx into mf end.
  cbn [lb_remove fst Z.eqb] in HM4.
  rewrite Z.eqb_refl in HM4.
  apply evtA_done.
  unfold EPOST.
  exists mf, h4.
  do 14 eexists.
  split; [ first [ reflexivity | apply lx_MS_regs; apply mkR_eq31; first [ reflexivity | (f_equal; lia) | (apply bv_eq; rewrite ?Z_to_bv_unsigned; cbn; lia) ] ] | ].
  split; [assumption|].
  split.
  {
  chunk_to_stk SLOT.
  chunk_to_stk SAVE.
  lazymatch goal with ST0 : stk _ mf lo sp1, STA : stk _ mf sp1 (sp1 + 24), STB : stk _ mf (sp1 + 32) _ |- _ =>
          stk_merge_into ST0 STA; stk_merge_into ST0 SLOT; stk_merge_into ST0 STB; stk_merge_into ST0 SAVE;
          replace (bv_unsigned sp + -64 + 64) with (bv_unsigned sp) in ST0 by (clear; lia); exact ST0 end.
  }
  split; [exact PRES|].
  split; [exact PRES2|].
  split; [rewrite E4cs; reflexivity|].
  split; [exact E4top|].
  split; [exact E4stk|].
  split; [exact E4flag|].
  split; [exact E4vol|].
  split; [exact E4fr|].
  split; [exact HKI4|].
  exact HM4.
Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Hypothesis MX : mpd_at asegs m LB dX.
  Hypothesis MA : mpd_at asegs m LB dA.
  Hypothesis SXA : mpd_sep dX dA.
  Hypothesis NST : md_own dX <> LStatic.
  Hypothesis OA : opnd_sep dX dA lo (bv_unsigned sp).
  Hypothesis CRA : client_range L (LB ++ fdata LF) lo (md_addr dA) 16.
  Hypothesis CRAL : md_own dA = LHeap -> client_range L (LB ++ fdata LF) lo (md_p dA) (4 * md_n dA).
  Hypothesis XW : mpd_writableA R LB LF (bv_unsigned sp) (htop asegs R HIA h) dX.
  Hypothesis XLS : md_own dX <> LNull -> md_p dX + 4 * md_n dX <= lo \/ bv_unsigned sp <= md_p dX.
  Hypothesis RAE : bv_unsigned ra mod 2 = 0.
  Hypothesis IA1 : md_addr dA <> md_addr dX -> md_own dA = LStatic -> img_norz (md_p dA) (4 * md_n dA) = true.
  Hypothesis IA2 : ltac2:(CDefT.buildp (gd_tbl_A_mpi_add_int_sz ()) "P,(6.$44.(45.VdA,)$46.)P,Pi,$0.P,(1.(2.=R1.)(5.R1.(47.+4.(48.VdA,))))(6.$49.(4:.$10.(4;.(9.(4<.VdA,)R2.)))$4=.)(6.$49.(4>.(4<.VdA,)(47.+4.(48.VdA,)))$4=.)")
(* [comment removed for export] *).
  Hypothesis BUD : havol asegs R HIA h + add_int_PHI dX dA <= AVOL_MAX.
  Hypothesis UWX : uw_obj R (md_addr dX) 16 d.
  Hypothesis UWA : uw_obj R (md_addr dA) 16 d.
  Hypothesis BUDF : hfr asegs R HIA h + add_int_FR d <= FR_MAX.

  Lemma ai_main : ltac2:(CDefT.buildp (gd_tbl_A_mpi_add_int_sz ()) "Pt0,(11.&40.)Pt1,(11.&40.)Pt2,(11.&40.)Pa3,(11.&40.)Pa4,(11.&40.)Pa5,(11.&40.)Pa6,(11.&40.)Pa7,(11.&40.)Pt3,(11.&40.)Pt4,(11.&40.)Pt5,(11.&40.)Pt6,(11.&40.)P,(1?.$10.VR,VHIA,Vh,VLB,VLF,Vm,)P,(2;.$10.VR,VHIA,Vh,Vmo0,)P,(35.$10.Vm,Vlo,(1=.&40.Vsp,))P,(36.$10.Vm,)P,(4?.$10.(18.VR,)(23.$10.VR,VHIA,Vh,)Vm,VdX,)P,(4?.$10.(18.VR,)(23.$10.VR,VHIA,Vh,)Vm,VdA,)P,(50.$10.Vm,(38.VR,)(25.$10.VR,VHIA,Vh,)(1=.&40.Vs0,)(1=.&40.Vsp,)Vd,)(51.$10.(52.$10.VR,VHIA,Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,Vh,VLB,VLF,VdX,(53.VLB,VdX,VdA,Vb,)(54.VdX,VdA,)(55.Vd,)Vlo,Vm,Vmo0,)(56.(13.(14.Vra,Vsp,Vgp,Vtp,R13.R12.R11.Vs0,Vs1,(15.&40.(16.VdX,))(15.&40.(16.VdA,))(15.&40.Vb,)R10.R?.R>.R=.R<.Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,R;.R:.R9.R8.)VF,(15.&40.$3<.)Vfc,(1:.(11.&40.))Vm,(1;.$10.))Vmo0,))")
(* [comment removed for export] *).
  Proof.
    intros t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6 HH HK0 ST MI OXA OAA UW.
    rt_facts.
    pose proof (hm_top asegs R HIA h LB LF m HH) as HTOP.
    assert (SCS : crange CS lo (bv_unsigned sp - lo)) by (eapply crange_sub; [exact SCS0| clear - LOS; lia| clear - SLO NEEDR TOP HTOP; lia]).
    pose proof (uwc_nonneg _ _ _ _ _ _ _ UW) as D0.
    flat constr:(MX) 2%nat. intros FLt1 SGX. flat constr:(FLt1) 6%nat. flclear FLt1. intros CX0 XAL X0 LENX NRX OWNX. flat constr:(MA) 2%nat. intros FLt2 SGA. flat constr:(FLt2) 6%nat. flclear FLt2. intros CA0 AAL A0 LENA NRA OWNA.
    flat constr:(XW) 2%nat. intros XCW XP. flat constr:(OA) 5%nat. intros OA1 OA2 OA3 OA4 OA5.
    pose proof (rw_cells_bound _ _ _ _ CX0) as XB. unfold mpi_cells in XB. cbn [cells_size csize Nat.add] in XB.
    pose proof (rw_cells_bound _ _ _ _ CA0) as AB. unfold mpi_cells in AB. cbn [cells_size csize Nat.add] in AB.
    (* [comment removed for export] *)
    pose proof (client_wrange_where_A asegs R HIA h LB LF m LB (bv_unsigned sp) (md_addr dX) 16 lo HH ltac:(intros b' Hb; exact Hb) XCW ltac:(clear; lia) LOS ltac:(clear - SLO NEEDR; lia)) as XS.
    flat constr:((hm_apart asegs R HIA h LB LF m HH)) 2%nat. intros HBR _. rewrite Forall_forall in HBR.
    (* [comment removed for export] *)
    assert (XHL : md_own dX = LHeap -> md_p dX + 4 * md_n dX <= alloc_ceiling).
    { intros EO. rewrite EO in OWNX. flat constr:(OWNX) 3%nat. flclear OWNX. intros _ XIN _. destruct (HBR _ ltac:(apply in_app_iff; left; exact XIN)) as (_ & _ & HC & _). exact HC. }
    (* [comment removed for export] *)
    apply (aevtA_enter asegs (KF asegs R HIA h mo0) _ _ _ (conj HK0 (mo_frame_refl mo0))).
    (* [comment removed for export] *)
    eapply (aevtA_cut_evtA_KF asegs R HIA h mo0).
    { eapply pro_walk; eassumption. }
    intros ms1 P1.
    destruct P1 as (FB & sp1 & h1 & m1 & y0 & y1 & y2 & z4 & z5 & z6 & z7 & y3 & y4 & y5 & y6 & w0 & w1 & w2 & padw
                   & Ems & SP1 & SP1M & HH1 & Ehcs & Ehtop & Estk & Eflag & Evol & Efr & HKI & F64 & FRSH & FHD & BST & LMB & FSHX
                   & SAVE & SLOT & ST24 & SThi & STlo & MI1 & PRES0).
    subst ms1.
    assert (SP1R : 0 <= sp1 < 2^64) by (clear - SP1 SPR SLO LOS ALO ACV NEEDR; lia).
    destruct (frame_factsA R HIA CS h1 LB LF m1 FB 128 lo HH1 Ehcs FRSH F64 ltac:(clear; lia) ltac:(reflexivity) LOS)
      as (CFB & INF & INH & IND & AP & (F0 & F1 & F2 & F3) & F8 & FBLO & SBND & APS). change (128 / 8) with 16 in SBND, APS. change (128 - 40) with 88 in IND.
    pose proof (presW_presA asegs R HIA h LB LF _ _ _ m m1 PRES0) as HP01.
    pose proof (presA_presx asegs R _ _ _ _ _ _ _ _ HP01) as HPX01.
    (* [comment removed for export] *)
    assert (CRXs : client_range L (LB ++ fdata LF) (bv_unsigned sp) (md_addr dX) 16) by (eapply client_range_of_w; exact XCW).
    assert (CRXL : md_own dX = LHeap -> client_range L (LB ++ fdata LF) (bv_unsigned sp) (md_p dX) (4 * md_n dX)).
    { intros EO. rewrite EO in OWNX. flat constr:(OWNX) 3%nat. flclear OWNX. intros N1 XIN _. eapply client_range_block; [apply in_app_iff; left; exact XIN| clear; lia| clear - N1; lia]. }
    assert (CRAs : client_range L (LB ++ fdata LF) (bv_unsigned sp) (md_addr dA) 16).
    { intros a Ha. destruct (CRA a Ha) as [C|[C|C]]; [| right; left; exact C| right; right; exact C]. left. clear - C Ha OA4. lia. }
    assert (CRALs : md_own dA = LHeap -> client_range L (LB ++ fdata LF) (bv_unsigned sp) (md_p dA) (4 * md_n dA)).
    { intros EO. rewrite EO in OWNA. flat constr:(OWNA) 3%nat. flclear OWNA. intros N1 AIN _. eapply client_range_block; [apply in_app_iff; left; exact AIN| clear; lia| clear - N1; lia]. }
    assert (MX1 : mpd_at asegs m1 LB dX).
    { eapply (mpd_at_heap_presx asegs L); [exact MX| exact HPX01| exact MI| exact MI1| exact CRXs| exact CRXL| exact I| intros _; exact I| intros b' Hb; unfold mpd_blk in Hb; destruct (md_own dX) eqn:EO; try (destruct Hb; fail); destruct Hb as [<-|[]]; (flat constr:(OWNX) 3%nat; flclear OWNX; intros _ XIN _); exact XIN]. }
    assert (MA1 : mpd_at asegs m1 LB dA).
    { eapply (mpd_at_heap_presx asegs L); [exact MA| exact HPX01| exact MI| exact MI1| exact CRAs| exact CRALs| exact I| intros _; exact I| intros b' Hb; unfold mpd_blk in Hb; destruct (md_own dA) eqn:EO; try (destruct Hb; fail); destruct Hb as [<-|[]]; (flat constr:(OWNA) 3%nat; flclear OWNA; intros _ AIN _); exact AIN]. }
    (* [comment removed for export] *)
    assert (TOPCS : forall x, CS x -> x < hstkhi asegs R HIA h) by (intros x Hx; eapply hcs_below_top; exact Hx).
    assert (OXA1 : mpd_aobjA asegs AL (hcs asegs R HIA h1) m1 dX).
    { rewrite Ehcs. flat constr:(OXA) 2%nat. flclear OXA. intros OX1 _. split; [| intros EO; exfalso; exact (NST EO)].
      eapply (presA_aobj asegs R); [exact CSOK| exact HP01| exact OX1| exact CRXs| clear - LOS SLO NEEDR; lia| exact TOPCS]. }
    assert (OAA1 : mpd_aobjA asegs AL (hcs asegs R HIA h1) m1 dA).
    { flat constr:(OAA) 2%nat. flclear OAA. intros OA1' _. split.
      - rewrite Ehcs. eapply (presA_aobj asegs R); [exact CSOK| exact HP01| exact OA1'| exact CRAs| clear - LOS SLO NEEDR; lia| exact TOPCS].
      - intros EO. rewrite EO in OWNA. flat constr:(OWNA) 5%nat. flclear OWNA. intros _ _ _ _ RO.
        eapply (AImgGlobals.aobj_img asegs AL); [apply (hcs_img_cs_cp R HIA IMG)| eapply (hm_img_shadow asegs R HIA); exact HH1| exact (IA2 EO RO)]. }
    (* [comment removed for export] *)
    assert (UW1 : uwc asegs m1 (arl_stklo R) (hstkhi asegs R HIA h) (bv_unsigned s0) (bv_unsigned sp) d).
    { eapply (uwc_presA R); [exact HP01| exact UW| clear; lia| intros a Ha; exact I| clear - SPR; lia| apply hstkhi_le64; clear - LOS SLO SPR NEEDR; lia]. }
    assert (UWF : uwc asegs m1 (arl_stklo R) (hstkhi asegs R HIA h) (bv_unsigned sp) sp1 (d + 1)).
    { pose proof SAVE as SV. chunk_split SV 6%nat SVa SVb. chunk_split SVb 1%nat SV0 SVr. clear SVa SVr.
      replace (bv_unsigned sp + -64 + 48) with (bv_unsigned sp - 16) in SV0 by (clear; lia).
      eapply (uwc_frame_save R); [exact (proj1 SV0)| exact UW1| clear - SP1; lia| clear - SPA; Z.div_mod_to_equations; lia| exact D0]. }
    clear UW1.
    (* [comment removed for export] *)
    set (dB := mkMPD (FB + 32) (sgn_of b) 1 (FB + 64) [Z_to_bv 64 (abs_limb_expr b)] padw LStatic).
    assert (APX : FB + 128 <= md_addr dX \/ md_addr dX + 16 <= FB) by (eapply (frame_apart_obj R HIA); [exact FRSH| exact XCW| clear; lia| clear; lia| clear - LOS SLO NEEDR; lia]).
    assert (APA : FB + 128 <= md_addr dA \/ md_addr dA + 16 <= FB).
    { destruct (frame_apart_obj0 R HIA LB LF lo (md_addr dA) 16 FB 128 FRSH CRA ltac:(clear; lia) ltac:(clear; lia) LOS) as [C|C]; [exfalso; clear - C; lia| exact C]. }
    assert (BL : u32arr asegs m1 (FB + 64) [Z_to_bv 64 (abs_limb_expr b)]).
    { eapply (u32arr_of_cells _ _ _ 4 (le4 (Z_to_bv 64 (abs_limb_expr b)))); [eapply rw_cells_reshape; [exact LMB| cbn; split; [apply (length_le4 (Z_to_bv 64 (abs_limb_expr b)))| exact I]| cbn; rewrite ?app_nil_r; reflexivity]| cbn; rewrite ?app_nil_r; reflexivity]. }
    assert (OB : opnd_atA asegs R ((FB, 128) :: LF) m1 LB sp1 dB).
    { right. unfold temp_opndA, dB. cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own length].
      split; [reflexivity|]. split; [unfold mpi_cells; exact BST|]. split; [clear - F8; Z.div_mod_to_equations; lia|].
      split; [clear - F0; lia|]. split; [reflexivity|]. split; [unfold MPI_MAX_LIMBS; clear; lia|]. split; [clear; lia|].
      split; [clear - F8; Z.div_mod_to_equations; lia|]. split; [clear - F0; lia|]. split; [apply u32arr_ro; exact BL|].
      split; [| split; [clear - F1 ACV; lia| apply sgn_of_cases]].
      intros a Ha. right. right. exists (FB + 32, 88). split; [cbn [fdata]; right; left; reflexivity| cbn [fst snd]; clear - Ha; lia]. }
    assert (OBA : mpd_aobjA asegs AL (hcs asegs R HIA h1) m1 dB).
    { rewrite Ehcs. unfold dB. split; cbn [md_addr md_own md_p md_n].
      - frame_aobj FSHX (FB + 32) 2%nat as OBS. exact OBS.
      - intros _. eapply (aobj_of_partial_shadow_sh asegs AL CS m1 FB _ (FB + 64) 8%nat 4); [exact CSOK| exact FSHX| eapply crange_sub; [exact CFB| clear; lia| clear; lia]| exact F8| clear - F0; lia| clear; lia| clear; lia| reflexivity]. }
    pose proof (AIh_laws asegs R HIA h) as LAWS. pose proof (KF_kinv asegs R HIA h mo0) as KINV.
    pose proof HAS as HAS'. unfold add_sub_mpi_stmtA_oz, mpi_addsub_stmtA_o in HAS'.
    eapply aevtA_call.
    { intros mo1 [HK1 MF1].
      eapply HAS' with (h := h1) (LB := LB) (LF := (FB, 128) :: LF) (dX := dX) (dA := dA) (dB := dB) (lo := lo) (d := d + 1);
        rewrite ?(unsigned_lit sp1) by exact SP1R; rewrite ?Ehcs, ?Ehtop, ?Estk, ?Evol, ?Efr;
        first [ exact HH1 | exact MX1 | exact MA1 | exact OB | exact SXA | exact NST | exact STlo | exact LOS | exact MI1 | exact TPV | exact UWF | reflexivity
              | lazymatch goal with
                | |- HK _ _ _ h1 mo1 => apply (proj2 (HKI mo1)); exact HK1
                | |- mpd_sep dX dB => right; unfold dB; cbn [md_addr]; clear - APX; lia
                | |- mpd_sep dA dB => right; unfold dB; cbn [md_addr]; clear - APA; lia
                | |- opnd_sep dX dA _ _ => eapply opnd_sep_sp_le; [exact OA| clear - SP1; lia]
                | |- opnd_sep dX dB _ _ =>
                    unfold opnd_sep, dB; cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own];
                    split; [intros _; clear - APX; lia|];
                    split; [intros EO; rewrite EO in OWNX; (flat constr:(OWNX) 3%nat; flclear OWNX; intros N1 XIN _); pose proof (F3 _ _ ltac:(apply in_app_iff; left; exact XIN)) as K; clear - K N1; lia|];
                    split; [destruct (md_own dX) eqn:EO; [right; left; discriminate| right; right; right; (flat constr:(OWNX) 3%nat; flclear OWNX; intros N1 XIN _); pose proof (F3 _ _ ltac:(apply in_app_iff; left; exact XIN)) as K; clear - K N1; lia| right; left; discriminate]|];
                    split; [left; clear - FBLO; lia| intros _; left; clear - FBLO; lia]
                | |- client_range _ _ _ (md_addr dA) 16 => eapply client_range_temp; [exact CRA| clear; lia| intros b' Hb; apply fdata_cons_sub; exact Hb]
                | |- md_own dA = LHeap -> _ => intros EO; eapply client_range_temp; [exact (CRAL EO)| clear; lia| intros b' Hb; apply fdata_cons_sub; exact Hb]
                | |- client_range _ _ _ (md_addr dB) 16 => unfold dB; cbn [md_addr]; eapply client_range_block; [exact IND| clear; lia| clear; lia]
                | |- md_own dB = LHeap -> _ => intros EO; discriminate EO
                | |- mpd_writableA _ _ _ _ _ dX => split; [eapply client_wrange_sp_mono; [| eapply client_wrange_mono; [exact XCW| intros b' Hb; apply fdata_cons_sub; exact Hb]]; clear - SP1; lia| exact XP]
                | |- md_own dX <> LNull -> _ => intros XN; destruct (XLS XN) as [K|K]; [left; exact K| right; clear - K SP1; lia]
                | |- lo <= sp1 - _ - arl_need_rt _ => clear - SLO SP1; lia
                | |- sp1 <= htop _ _ _ _ => clear - SP1 TOP; lia
                | |- sp1 mod 16 = 0 => clear - SP1M; Z.div_mod_to_equations; lia
                | |- bv_unsigned (Z_to_bv 64 0x9ce1c) mod 2 = 0 => reflexivity
                | |- mpd_aobjA _ _ _ _ dX => rewrite <- Ehcs; exact OXA1
                | |- mpd_aobjA _ _ _ _ dA => rewrite <- Ehcs; exact OAA1
                | |- mpd_aobjA _ _ _ _ dB => rewrite <- Ehcs; exact OBA
                | |- md_addr dA <> md_addr dX -> _ => exact IA1
                | |- md_own dA = LStatic -> _ -> _ => exact IA2
                | |- md_own dB = LStatic -> (forall i, _) -> _ =>
                    intros _ RO; exfalso; unfold dB in RO; cbn [md_p md_n] in RO;
                    pose proof (ROIMG _ (RO 0 ltac:(clear; lia)) ltac:(clear - F0 F1 ACV; lia)) as K;
                    (flat constr:((hm_apart asegs R HIA h1 LB _ m1 HH1)) 2%nat; intros HBR1 _); rewrite Forall_forall in HBR1;
                    destruct (HBR1 (FB, 128) ltac:(apply in_app_iff; right; left; reflexivity)) as (_ & _ & _ & KI); cbn [fst snd] in KI; clear - K KI; lia
                | |- md_own dB = LStatic -> _ <= 2 ^ 47 => intros _; unfold dB; cbn [md_p md_n]; clear - F1 ACV; lia
                | |- havol _ _ _ _ + _ <= AVOL_MAX => unfold add_sub_PHI, add_abs_PHI, dB; cbn [md_n]; unfold add_int_PHI in BUD; exact BUD
                | |- uw_obj _ (md_addr dX) 16 _ => eapply uw_obj_mono_d; [exact UWX| clear; lia]
                | |- uw_obj _ (md_addr dA) 16 _ => eapply uw_obj_mono_d; [exact UWA| clear; lia]
                | |- uw_obj _ (md_addr dB) 16 _ => left; unfold dB; cbn [md_addr]; split; [clear - F1 ALO; lia| clear - D0; lia]
                | |- hfr _ _ _ _ + _ <= FR_MAX => unfold add_int_FR in BUDF; exact BUDF
                | |- _ = Z_to_bv 64 (md_addr dB) => reflexivity
                end
              | match goal with |- ?g => idtac "CALL-PRE-LEFT:" g end ]. }
    cbv beta. intros ms4 mo4 (mo1 & [HK1 MF1] & PO).
    destruct PO as (q0 & q1 & q2 & qa1 & qa2 & qa3 & qa4 & qa5 & qa6 & qa7 & q3 & q4 & q5 & q6 & m2 & mo2 & h3 & LB3 & dX3 & r
                    & E4 & MI2 & ST2 & MF2 & HP2 & HT3 & HS3 & HF3 & HK3 & HCS3 & HV3 & HFR3 & HH3 & MX3 & OUT3 & FRS3 & RR3).
    injection E4 as Ems Emo. subst ms4 mo4.
    replace (ret_pc (Z_to_bv 64 0x9ce1c)) with (Z_to_bv 64 0x9ce1c : word) by (symmetry; apply ret_pc_even; [clear; lia| reflexivity]).
    rewrite (unsigned_lit sp1) in ST2, HP2 by exact SP1R.
    rewrite Ehtop in HT3. rewrite Estk in HS3, HP2. rewrite Eflag in HF3. rewrite Evol in HV3. rewrite Efr in HFR3.
    assert (HCSh3 : forall x, hcs asegs R HIA h x -> hcs asegs R HIA h3 x) by (intros x Hx; apply HCS3; rewrite Ehcs; exact Hx).
    pose proof (hcs_ok asegs R HIA h3) as CSOK3.
    (* [comment removed for export] *)
    assert (HP2' : presA asegs R (mpd_keep LB dX) LF (bv_unsigned sp) (arl_stklo R) (hstkhi asegs R HIA h) [(md_addr dX, md_addr dX + 16)] m1 m2).
    { eapply presA_weaken; [exact HP2| intros b' Hb; exact Hb| intros b' Hb; right; exact Hb| clear - SP1; lia| clear; lia| clear; lia| intros x Hx; exact Hx]. }
    (* [comment removed for export] *)
    assert (PRESb : presW asegs R HIA h (mpd_keep LB dX) LF (bv_unsigned sp) (arl_stklo R) [(md_addr dX, md_addr dX + 16)] m m2).
    { pose proof (presW_sub_blocks asegs R HIA h LB (mpd_keep LB dX) LF _ _ _ m m1 PRES0 ltac:(intros b' Hb; eapply In_mpd_keep; exact Hb)) as (P0 & C1 & C2 & C3).
      split; [| split; [exact C1| split; [exact C2| exact C3]]].
      eapply presA_trans; [| exact HP2'].
      eapply presA_weaken; [exact P0| intros b' Hb; exact Hb| intros b' Hb; exact Hb| clear; lia| clear; lia| clear; lia| intros x _; exact I]. }
    (* [comment removed for export] *)
    pose proof (fresh_apart_relist R HIA h3 LB LB3 LF m2 FB 128 FRSH HH3) as FRSH3.
    pose proof (presW_init_at R HIA h3 _ _ LB3 LF m2 (bv_unsigned sp) (arl_stklo R) [] h HH3
                  ltac:(intros b' Hb; exact Hb) ltac:(intros fb Hfb; right; exact Hfb) HCSh3 HS3 ltac:(clear; lia)) as PRES2.
    (* [comment removed for export] *)
    assert (CSHD : forall LBq SSPq TOPq c, FB <= c < FB + 128 -> cshd R LBq ((FB, 128) :: LF) SSPq TOPq c).
    { intros LBq SSPq TOPq c Hc. right; right; left. exists (FB, 128). split; [left; reflexivity| cbn; exact Hc]. }
    assert (DJX : forall A k, (A + k <= md_addr dX \/ md_addr dX + 16 <= A) -> disjoint_from [(md_addr dX, md_addr dX + 16)] A k).
    { intros A k HA. cbn [disjoint_from]. split; [clear - HA; lia| exact I]. }
    apply (presA_shadow_cells_sh asegs R (hcs asegs R HIA h) (mpd_keep LB dX) ((FB, 128) :: LF) sp1 (arl_stklo R) (hstkhi asegs R HIA h) [(md_addr dX, md_addr dX + 16)] m1 m2 FB _ CSOK) in FSHX;
      [| cbn [cells_size csize Nat.add]; eapply crange_sub; [exact CFB| clear; lia| clear; lia] | exact F8 | clear - F0; lia | exact HP2 | cbn [cells_size csize Nat.add]; intros c Hc; apply CSHD; clear - Hc; lia ].
    apply (presA_rw_cells asegs R _ _ _ _ _ _ m1 m2 FB _ HP2) in FHD;
      [| cbn [cells_size csize Nat.add]; eapply client_range_block; [apply in_app_iff; right; left; reflexivity| clear; lia| clear; lia]
       | apply DJX; cbn [cells_size csize Nat.add]; clear - APX; lia ].
    apply (presA_rw_cells asegs R _ _ _ _ _ _ m1 m2 _ _ HP2) in SAVE; [| apply client_range_stack; clear - SP1; lia| apply DJX; cbn [cells_size csize Nat.add]; clear - XS SLO NEEDR; lia].
    apply (presA_rw_cells asegs R _ _ _ _ _ _ m1 m2 _ _ HP2) in SLOT; [| apply client_range_stack; clear; lia| apply DJX; cbn [cells_size csize Nat.add]; clear - XS SLO NEEDR SP1; lia].
    apply (presA_stk asegs R _ _ _ _ _ _ m1 m2 _ _ HP2) in ST24; [| clear; lia| apply DJX; clear - XS SLO NEEDR SP1; lia].
    apply (presA_stk asegs R _ _ _ _ _ _ m1 m2 _ _ HP2) in SThi; [| clear; lia| apply DJX; clear - XS SLO NEEDR SP1; lia].
    clear HP2 HP2' BST LMB BL OB OBA MX1 MA1 OXA1 OAA1 UWF HH1 STlo MI1 HP01 HPX01 PRES0.
    (* [comment removed for export] *)
    apply (aevtA_enter asegs (KF asegs R HIA h3 mo0) _ _ _ (conj HK3 (mo_frame_trans _ _ _ MF1 MF2))).
    clear LAWS KINV. pose proof (AIh_laws asegs R HIA h3) as LAWS. pose proof (KF_kinv asegs R HIA h3 mo0) as KINV.
    clear HK1 MF1 MF2 mo1.
    pose proof (presW_hmono R HIA h h3 (mpd_keep LB dX) LF _ _ _ m _ PRESb HCSh3 HS3) as PRESb3.
    eapply (aevtA_cut_evtA_KF asegs R HIA h3 mo0).
    { eapply epi_walk with (h3 := h3) (LBa := mpd_keep LB dX) (LBb := LB3) (r := r);
        first [ exact HH3 | exact HCSh3 | exact PRESb3 | exact PRES2 | exact FRSH3 | exact CFB | exact AP | eassumption | reflexivity
              | lazymatch goal with
                | |- fresh_apart _ (mpd_keep LB dX) LF FB 128 => apply fresh_apart_keep; exact FRSH
                | |- forall b', In b' (mpd_keep LB dX) -> In b' LB3 => intros b' Hb; eapply mpd_keep_out; [exact OUT3| exact Hb]
                end
              | match goal with |- ?g => idtac "EPI-PRE-LEFT:" g end ]. }
    cbv beta. intros ms9 EP.
    destruct EP as (m9 & h4 & z0' & z1' & z2' & za1 & za2 & za3 & za4 & za5 & za6 & za7 & z3' & z4' & z5' & z6'
                    & -> & MI9 & ST9 & PRES9 & PRES29 & E4cs & E4top & E4stk & E4flag & E4vol & E4fr & HKI4 & HH4).
    apply aevtA_done. intros mo9 [HK9 MF9].
    unfold mpi_binop_postA.
    do 14 eexists. exists m9, mo9, h4, LB3, dX3, r.
    split; [reflexivity|]. split; [exact MI9|]. split; [exact ST9|]. split; [exact MF9|].
    split; [pose proof (presW_presA asegs R HIA h3 _ LF _ _ _ _ _ PRES9) as HPF; rewrite HS3 in HPF; exact HPF|].
    split; [rewrite E4top; exact HT3|]. split; [rewrite E4stk; exact HS3|]. split; [rewrite E4flag; exact HF3|].
    split; [apply (proj2 (HKI4 mo9)); exact HK9|].
    split; [intros x Hx; rewrite E4cs; exact (HCSh3 x Hx)|].
    split; [rewrite E4vol; unfold add_sub_PHI, add_abs_PHI, dB in HV3; cbn [md_n] in HV3; unfold add_int_PHI; exact HV3|].
    split; [rewrite E4fr; unfold add_int_FR; exact HFR3|].
    split; [exact HH4|].
    flat constr:(OUT3) 5%nat. intros OU1 OU2 OU3 OU4 OU5.
    split.
    { (* [comment removed for export] *)
      flat constr:(MX3) 2%nat. intros FLt3 _. flat constr:(FLt3) 6%nat. flclear FLt3. intros CX3 _ _ _ _ OWN3.
      eapply (mpd_at_heap_presx asegs L) with (LBp := LB3 ++ fdata LF) (SP := bv_unsigned sp) (XI := []);
        [exact MX3| exact (presA_presx asegs R _ _ _ _ _ _ _ _ (presW_presA asegs R HIA h3 _ LF _ _ _ _ _ PRES29))| exact MI2| exact MI9| | | exact I| intros _; exact I|].
      - rewrite OU1. eapply client_range_temp; [eapply client_range_of_w; eapply mpd_writableA_keep; exact XW| clear; lia|].
        intros b' Hb. apply in_app_iff in Hb. apply in_app_iff. destruct Hb as [Hb|Hb]; [left; eapply mpd_keep_out; [exact OUT3| exact Hb]| right; exact Hb].
      - intros EO. rewrite EO in OWN3. flat constr:(OWN3) 3%nat. flclear OWN3. intros N1 XIN _. eapply client_range_block; [apply in_app_iff; left; exact XIN| clear; lia| clear - N1; lia].
      - intros b' Hb. unfold mpd_blk in Hb. destruct (md_own dX3) eqn:EO; try (destruct Hb; fail). destruct Hb as [<-|[]]. flat constr:(OWN3) 3%nat. flclear OWN3. intros _ XIN _. exact XIN. }
    split; [exact OUT3|].
    split.
    { intros b' Hb. destruct (FRS3 b' Hb) as [K|K]; [left; exact K| right].
      flat constr:(K) 4%nat. flclear K. intros K0 K1 K2 K3. split; [exact K0|]. split; [exact K1|]. split; [exact K2|].
      intros B j HB. apply K3. apply fdata_cons_sub. exact HB. }
    (* [comment removed for export] *)
    flat constr:(RR3) 2%nat. flclear RR3. intros (VAL & BK) NGX0. split; [| unfold intop_nz; unfold addsub_nz, dB in NGX0; cbn [md_n] in NGX0 |- *; first [exact NGX0 | clear - NGX0; lia]]. split; [| exact BK].
    destruct VAL as [[-> V]|V]; [left| right; exact V]. split; [reflexivity|].
    rewrite V. unfold dB, mpd_val at 2. cbn [md_sg md_limbs limbs_val].
    change (bv_unsigned (Z_to_bv 64 (abs_limb_expr b)) mod 2 ^ 32) with (w32 (Z_to_bv 64 (abs_limb_expr b))). rewrite (abs_limb_val b BB).
    pose proof (sgn_of_abs b) as SA. clear - SA. lia.
  Qed.
  End Call.

  Theorem A_mpi_add_int_spec_sz : mpi_add_int_stmtA_z asegs R HIA A_MPI_ADD_INT_E.
  Proof.
    unfold mpi_add_int_stmtA_z, mpi_intop_stmtA_r. intros until d.
    intros HH HK LFB MX MA SXA NST OA CRA CRAL XW BB XLS ST LOS SLO SLOS TOP SPA TPV MI RAE OXA OAA IA1 IA2 BUD UW UWX UWA BUDF C24H -> -> ->.
    eapply ai_main; eassumption.
  Qed.
End WalkI.

Theorem A_mpi_add_int_spec_z : ltac2:(CDefT.buildp (gd_tbl_A_mpi_add_int_sz ()) "PR,$57.PHIA,(58.$10.R1.)P,(59.(18.R2.))P,(6.$0.(5:.R3.)$5;.)P,(6.$0.(5<.R4.+1.)$5=.)P,(2.=(5>.R5.))P,(2.=(5?.R6.))P,(60.+1.$10.R7.R6.$19.)P,(1.(2.(61.(62.R8.))(63.(62.R8.)))(2.(64.(62.R8.))(65.(62.R8.))))P,Pa,$0.P,(6.$49.(4:.$10.(4;.R1.))$4=.)P,(1.(2.=R2.)(5.R2.(4.+2.+40.)))(1.(2.(61.(62.R<.))R3.)(5.R3.(65.(62.R<.))))(66.$10.R:.R9.$67.)")
(* [comment removed for export] *).
Proof. intros. change A_MPI_ADD_INT with A_MPI_ADD_INT_E. apply A_mpi_add_int_spec_sz; assumption. Qed.

(* [comment removed for export] *)
