(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Walk Asn1Aux AStep CellsX Image.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Spec Require Import Rep.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U Require Import UImg U_string U_oid U_oid_x509_ext.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX Require Import LxExpr LxDec LxMem LxStep LxRun LxDenot LxSoundRun LxSum LxSoundSum LxTac.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LXP Require Import LxPTac. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LXU Require Import LxU_SumsOid.

Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Import OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.LxhSyntax. #[local] Instance lxh_tab : OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.lx_hints := OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.lxh_parse "P01b6195ebdcab0a7 0 4 0 1 1 1 18 1 22 1P0724319fac81ec44 2 23 1 1 8 3 2 1 33 1 34 1 5 0 2 24 2 32 2 35 2 36 16 1 1 8 3 1 1 32 1 35 1 4 0 2 33 2 34 2 36 16P087ac84578a4531b 2 21 0 6 0 1 3 1 25 1 29 1 33 1 34 1 0 4 0 1 2 1 33 1 34 1P0d0244b66f970434 1 1 8 2 0 1 25 1 3 10 1 26 1 27 8P0f71b70ac5877e41 0 4 0 8 9 8 25 8 26 8P111803e3a13ba17d 0 3 0 1 2 1 21 1P12d79c880de0b2aa 0 2 0 1 35 1P13e86ac0ccd1a27f 0 3 0 1 25 1 37 1P154aea195fbf65a3 0 2 0 1 23 1P15bc0065d8ec856f 2 23 1 1 8 3 2 1 33 1 34 1 5 0 2 24 2 32 2 35 2 36 16 1 1 8 3 1 1 32 1 35 1 4 0 2 33 2 34 2 36 16P16adeb1358fe32f0 0 2 0 1 24 1P1710bfc01dcf949b 0 2 0 1 24 1P1b6a66bd1d0c6926 1 1 8 2 20 1 26 1 3 0 1 25 1 27 8P1bfa48b2cf1c16c6 0 2 0 1 33 1P1c75142395c572d4 2 22 1 1 4 3 2 1 33 1 34 1 5 0 4 24 4 32 4 35 4 36 16 1 1 4 3 1 1 32 1 35 1 4 0 4 33 4 34 4 36 16P234286584e66891c 0 2 0 1 2 1P25179e19b20ad3bc 2 23 1 1 8 3 2 1 33 1 34 1 5 0 2 24 2 32 2 35 2 36 16 1 1 8 3 1 1 32 1 35 1 4 0 2 33 2 34 2 36 16P29935fc55c0ccee1 0 2 0 1 1 1P2aaf7795dfa2ff0d 0 4 0 1 5 1 36 1 37 1P2bab4771975afecb 0 2 0 1 23 1P2be6295a4b2ffdf7 0 2 0 1 1 1P2c45cf39a503018a 2 22 1 1 4 3 2 1 33 1 34 1 5 0 4 24 4 32 4 35 4 36 16 1 1 4 3 1 1 32 1 35 1 4 0 4 33 4 34 4 36 16P2e5c7fbadeb38f2e 0 2 0 1 2 1P3060779628227ff7 0 3 0 1 2 1 21 1P334a573060fe0c52 0 3 0 1 27 1 39 1P36288b6d1531eb7b 0 4 0 1 7 1 38 1 39 1P36b4d5f3d81aea1a 2 22 1 1 4 3 2 1 33 1 34 1 5 0 4 24 4 32 4 35 4 36 16 1 1 4 3 1 1 32 1 35 1 4 0 4 33 4 34 4 36 16P3831687f0171ec0e 2 21 0 6 0 1 3 1 25 1 29 1 33 1 34 1 0 4 0 1 2 1 33 1 34 1P3cfd255d6744e86d 2 21 0 6 0 1 3 1 25 1 29 1 33 1 34 1 0 4 0 1 2 1 33 1 34 1N0043fc113cbf62abN00ff2775a8e889afN01ac62a03d7a0f83N02b0abdfbc5d487dN04bfefb8a73fcdeaN04d69d07cf6958d8N05593e517bb4cbdeN0642504cbe30f71dN074301751fbdfe30N07580a6d01b6c6c3N07ea8118cf4661b3N09e8ac5f4fa42fceN0a4e23df03807355N0b4ba8e8b4a8f133N0b90df3d1998e6a8N0d73ec048b5aea09N0d8b3f9205fd566bN0ea72749ccbab19cN0f121f39be3b6b6aN0f456e9aff7084fcN0fee40cddb2c06dcN1020abae4a74f08aN104f26abcf3a8bd7N12bf512f0f119085N12c471b82ed2d4b3N14071d6392b5bceaN14d62e0c6597aae9N1520cf0eb471778eN1538a8f86bca170bN162dcdda21c9fa1eN17af03ef2533c7f1N186c36f246280da9N18b6049265705df2N193bd04feb519693N195006ea6c469e53N19e05983268d78a4N1a1557f4aacee8abN1a4252cdc50ba0afN1a9b05552547e67fN1b0c1d37e839e16cN1c28371ded66757fN1cfb36cdc342a1b0N1db3cf4b534d7bcfN1ebb5d1552586924N1fa1b63d5de6a0baN1fe795641fbb0ad6N1ff765d833ba7813N206a63ff636e2aaaN2070cbe0cc6aad6cN22be4f5cbbf07795N231fcc1a9d980a54N2409c3781afc1b80N2411f1f9629dc1f0N244378e65921233cN251c6ef57073df26N25efb794e38184b7N268f1ba08144bc4cN26bb6ded91e9f535N271ec2ebaafac3e7N27381b00fc629bb8N2742f8d4eb1f5241N27ba20db1a6f07a0N281f3d9fa683ade2N284fd512703a4d8dN2ae55f1f633c772eN2ce0ba8a741cdac7N2e7d9e4d91af4daaN2f00fc05d2a25757N2fe823d34a5de7acN31ad773b16de2d00N31f9bd3b606f944dN320bf13c32110422N3217cf3f57da3e22N32600557b55e413eN3306a69ec9f77ab4N33bcbc479aa074e1N33edd9f5e2af1ecdN3409d253c4694adbN344765aa614a6a6aN3480377e74538823N34b31f42eda7b945N3563f47a8805e090N35a3229fb8a70898N36474311cd0efe4eN36ad46a28adb089cN3720c3aede2f67ddN37f4dde21b65ad3eN381ffe28dd3ea0dbN38290681f2b02db0N38879b5ec8c41fa8N38aeef63287a0a0aN3956c906e17b7dbcN39daf0fc60ac5a3aN3a1700750590cd54N3b7ac5c499508501N3b9a3eb233cf81a8N3c6c182814f36fbfN3cc3a8a378c102baN3d7c6148dca4a849N3f3393cd8cbc9f7eN3f87735e66d43351"%lxh.
Ltac2 gd_tbl_P_oid_ec_grp_algid () : Init.string Init.list := ["Corelib.Numbers.BinNums.Z"; "stdpp.bitvector.definitions.bv"; "Corelib.Init.Datatypes.list"; "Corelib.Init.Datatypes.option"; "Corelib.Init.Logic.or"; "Corelib.Init.Logic.eq"; "RocqVerifyHarness.AgentSubmission.U.U_oid.MBEDTLS_ERR_OID_NOT_FOUND"; "RocqVerifyHarness.AgentSubmission.Lib.Step.rw_cells"; "RocqVerifyHarness.AgentSubmission.U.UImg.usegs"; "Stdlib.ZArith.BinInt.Z.add"; "stdpp.bitvector.definitions.bv_unsigned"; "Corelib.Init.Datatypes.cons"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.cell"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.CB"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C8"; "Corelib.Init.Datatypes.nil"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.stk"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C4"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.mem_inv"; "RocqVerifyHarness.AgentSubmission.Lib.AStep.statics_ok"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.munch"; "Corelib.Init.Datatypes.prod"; "Corelib.Init.Datatypes.pair"; "Stdlib.ZArith.BinInt.Z.sub"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.wmono"; "RocqVerifyHarness.AgentSubmission.Lib.Exec.evt"; "RocqVerifyHarness.AgentSubmission.U.U_oid.oid_lookup1_post"; "RocqVerifyHarness.AgentSubmission.Lib.MState.MS"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.mkR"; "stdpp.bitvector.definitions.Z_to_bv"; "Corelib.Init.Datatypes.None"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.seg_rom"; "Stdlib.Lists.List.In"; "Walk.offsets"; "U_OID_EC_GRP_ALGID_TBL"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.heap_layout"; "RocqVerifyHarness.AgentSubmission.U.U_oid.oid_lookup1_stmt"; "U_OID_GET_EC_GRP_ALGID"].


Definition U_OID_GET_EC_GRP_ALGID : Z := 0x26074.
Definition U_OID_EC_GRP_ALGID_TBL : Z := 0x48990.
Notation OID_EC_GRP_ALGID_TBLN := 80 (only parsing).
Notation OID_EC_GRP_ALGID_STACK := 32 (only parsing).


Ltac flia := first [clear_disj; lia | lia].
(* [comment removed for export] *)
Ltac ro_const' A0 n0 RO :=
  lazymatch goal with |- context [MS _ _ _ _ _ ?mx (seg_rom ?sg)] =>
    let cbs := eval vm_compute in (match image_bytes sg A0 n0 with Some cbs => cbs | None => [] end) in
    match goal with MI : mem_inv sg mx |- _ =>
      pose proof (ro_image_bytes_at sg mx A0 cbs MI ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(cbn; lia)) as RO;
      let nz := eval vm_compute in (Z.of_nat n0) in let ROL := fresh "ROL" in assert (ROL : Z.of_nat (length cbs) = nz) by reflexivity end
  end.

Lemma U_oid_get_ec_grp_algid_spec : ltac2:(CDefT.buildp (gd_tbl_P_oid_ec_grp_algid ()) "PL,$23.(24.$8.R1.$25.$22.+50.+20.)")
(* [comment removed for export] *).
Proof.
  intros L. unfold oid_lookup1_stmt, U_OID_GET_EC_GRP_ALGID.
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
  (* [comment removed for export] *)
  assert (LXSUMS : forall AL, Forall (summary_ok usegs AL) [SUM_bcmpCP 0x46940])
    by (intros AL; repeat constructor; apply sum_bcmpCP_ok; exact U_bcmp_spec).
  carve_frame 32%nat ST.
  lx_run_tac (PLANS [0x260a4] [] 40%N (@nil summary)); lx_tree.
  all: try lxp_ret.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.
  lazymatch goal with Hi : mem_inv _ m1 |- _ => rename Hi into MI1 end.
  repeat match goal with H : mem_inv _ m |- _ => clear H end.
  ro_const' 0x10556 3%nat RO1. ro_const' 0x10724 3%nat RO2.
  oid_tbl_facts L EXT sp m SOK CA ACL SLO DHI OD 32 U_OID_EC_GRP_ALGID_TBL 2.
  lx_run_tac (PLANS [0x26128] [] 200%N [SUM_bcmpCP 0x46940]); lx_tree.
  all: first [ lxp_at 155944; kdead | lxp_ret ].
Qed.
