(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Arr Asn1Aux CellsX Bytes.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import AModel.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import AW_Unwind AW_Unwind2 AW_MmapFixed AW_MallocA AW_AllocA AW_DepotA AW_DepotB AW_Poison.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import AW_ClassId.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import A_stringA.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BLX Require Import LxA.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LXBW Require Import LxAWTac.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import ATac.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.AHeap Require Import ACeil.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Import OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.LxhSyntax. #[local] Instance lxh_tab : OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.lx_hints := OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.lxh_parse "P0067f7b16223750b 0 4 0 1 41 1 47 1 48 1P0083179b5edb3be8 1 2 16 2 0 1 75 1 16 2 1 1 74 1 2 76 1 77 1P045d78134a20a384 0 6 1 1 65 1 66 1 69 1 74 1 75 1P071b076e1b19e2a5 1 1 16 2 1 1 74 1 5 61 1 65 1 66 1 75 1 76 16P08000fb39a2eb8a1 0 1 1 1P089ad3a3dcbc0090 0 6 0 1 65 1 66 1 69 1 74 1 75 1P08a4b28403cdc3a8 1 2 16 2 0 1 75 1 16 2 1 1 74 1 2 76 1 77 1P08b49b11a6717eb6 0 4 0 1 53 1 55 1 57 1P08fd868d9d45ce62 0 2 0 1 45 1P098af5ee0a0d2c4f 0 6 0 16 29 16 31 16 32 16 33 16 34 16P09b6be303abcd23b 1 2 16 4 1 1 48 1 51 1 53 1 16 8 33 1 38 1 42 1 43 1 44 1 49 1 50 1 52 1 2 54 1 55 1P0a08754bf019dcb4 1 2 16 2 0 1 75 1 16 2 1 1 74 1 2 76 1 77 1P0a08da058a3fd093 0 4 0 1 24 1 26 1 27 1P0c289b2acf5f285f 0 4 0 16 64 16 73 16 74 16P0d3f2e5cbfb943bb 0 6 1 1 65 1 66 1 70 1 74 1 75 1P0e61581519611f77 1 1 16 2 1 1 74 1 5 61 1 65 1 66 1 75 1 76 16P0e6c3c9f541469d9 1 1 16 2 1 1 74 1 5 61 1 65 1 66 1 75 1 76 16P0fb8e8bcc7e6c7be 0 4 0 1 24 1 26 1 27 1P10c8eb65ef839083 1 1 16 2 1 1 74 1 5 61 1 65 1 66 1 75 1 76 16P112745ff73caa396 0 4 0 1 24 1 26 1 27 1P118375158b6e8fd3 0 4 0 16 64 16 73 16 74 16P11ec9f7d4c46abb8 0 1 1 1P13c13b7999e1021e 0 2 0 1 70 1P13f3ad14d4c0eaa5 1 1 16 2 1 1 74 1 5 61 1 65 1 66 1 75 1 76 16P148b7dbe0d38089f 0 6 1 1 65 1 66 1 69 1 74 1 75 1P17b5f20854ea4966 1 2 16 4 1 1 48 1 51 1 53 1 16 8 33 1 38 1 42 1 43 1 44 1 49 1 50 1 52 1 2 54 1 55 1P17e782c31b03e896 1 1 16 2 1 1 74 1 5 61 1 65 1 66 1 75 1 76 16P1810659164b88556 0 4 0 1 24 1 26 1 27 1P183326484e4b1281 0 4 0 1 41 1 47 1 48 1P186cf87340441c27 1 1 16 2 1 1 74 1 5 61 1 65 1 66 1 75 1 76 16P18b7fffbcec5e572 0 4 0 16 64 16 73 16 74 16P190fcde63423d4a5 1 2 16 2 0 1 75 1 16 2 1 1 74 1 2 76 1 77 1P1a2959b683b50d46 1 1 16 2 1 1 48 1 5 37 1 42 1 43 1 49 1 50 16P1a8ecff0a68e8685 0 4 0 1 41 1 47 1 48 1P1ad518b9b4af1779 0 2 0 1 25 1P1b1ae83888f7aa20 1 2 16 4 1 1 48 1 51 1 53 1 16 8 33 1 38 1 42 1 43 1 44 1 49 1 50 1 52 1 2 54 1 55 1P1bda96d28ad00352 0 4 0 1 41 1 47 1 48 1P1c87e61aa4a9c9e9 0 2 0 1 45 1P1ec883cad10dd4dd 0 6 1 16 61 16 65 16 66 16 74 16 75 16P1f4eafa5ae236f49 0 4 0 1 41 1 47 1 48 1P206a5d4a3a0415f0 0 4 0 1 24 1 26 1 27 1P20fac5439f276f94 0 2 0 1 55 1P212e6a0c52486916 0 4 0 16 64 16 73 16 74 16P213c9a3fc877ac30 1 2 16 2 0 1 75 1 16 2 1 1 74 1 2 76 1 77 1P21ec5947ec7b41b9 0 4 0 1 24 1 26 1 27 1P22149d45a0d4e2f7 0 1 1 1P23a7545d59aa7be4 1 1 16 2 1 1 48 1 5 37 1 42 1 43 1 49 1 50 16P2531c70ae45bb5f9 0 4 0 1 41 1 47 1 48 1P2603109299f5e8a9 1 1 16 2 1 1 74 1 5 61 1 65 1 66 1 75 1 76 16P2659457c12011069 0 6 0 1 65 1 66 1 69 1 74 1 75 1P271951da1a47784c 0 4 0 16 64 16 73 16 74 16P274246ee8d9a4c31 0 6 0 1 65 1 66 1 69 1 74 1 75 1P28aa8a72cf94704e 1 1 128 6 2 16 66 16 67 16 70 16 75 16 76 16 3 63 1 68 1 77 8P28f2d1d6cb88e9da 1 1 16 2 1 1 74 1 5 61 1 65 1 66 1 75 1 76 16P291318092dd6f17d 0 4 0 1 24 1 26 1 27 1P29cf6fde56602a9a 0 2 0 1 55 1P2a2c28ce5a8a04c6 0 4 0 1 41 1 47 1 48 1P2bb406842dc7ba99 0 4 0 1 41 1 47 1 48 1P2bbe7ace34d50301 0 4 0 1 41 1 47 1 48 1P2ca4acac40fd8879 0 4 0 1 24 1 26 1 27 1P2d0fdcd23d31e12c 0 2 0 1 70 1P2d9bd6c3870843d1 0 6 0 1 65 1 66 1 69 1 74 1 75 1P2e5432a8f731f76e 0 4 0 1 24 1 26 1 27 1P2fcc3968b7f2b5dc 0 2 0 1 23 1P3038de7a357e6a3a 1 2 16 2 0 1 75 1 16 2 1 1 74 1 2 76 1 77 1P318df5ff56c7e3e0 0 4 0 16 64 16 73 16 74 16P326d6db1a3772ed2 0 4 0 1 24 1 26 1 27 1P3462b3fb1e1fca05 0 4 0 1 52 1 54 1 56 1P353cf0a3c6f36be0 0 4 0 1 24 1 26 1 27 1P3611d6028ba6b1f5 0 6 0 1 65 1 66 1 69 1 74 1 75 1P36220299dada2665 0 4 0 1 24 1 26 1 27 1P372f641ca90c78e8 0 4 0 1 24 1 26 1 27 1P37f2d2e4731b274c 1 2 16 2 0 1 75 1 16 2 1 1 74 1 2 76 1 77 1P383e686b2913eedf 0 2 0 1 1 1P38abf0c557ebec3e 1 1 16 2 1 1 74 1 5 61 1 65 1 66 1 75 1 76 16P38cdbad514d7262c 1 2 16 2 0 1 75 1 16 2 1 1 74 1 2 76 1 77 1P3906015836d35a3f 1 1 128 6 2 16 66 16 67 16 70 16 75 16 76 16 3 63 1 68 1 77 8P390f1f236ef9c12a 0 6 1 16 61 16 65 16 66 16 74 16 75 16P39107ad8dce545b8 0 4 0 1 41 1 47 1 48 1P3974355e73428576 1 2 16 2 0 1 75 1 16 2 1 1 74 1 2 76 1 77 1P3a424b083f65e759 1 2 16 2 0 1 49 1 16 2 1 1 48 1 2 50 1 51 1P3ab729498ae28158 0 4 0 1 41 1 47 1 48 1P3aef7fe9329645fd 1 2 16 2 0 1 75 1 16 2 1 1 74 1 2 76 1 77 1P3c35a3486246e08d 0 4 0 1 24 1 26 1 27 1P3cf4258ca126275e 1 2 16 4 1 1 48 1 51 1 53 1 16 8 33 1 38 1 42 1 43 1 44 1 49 1 50 1 52 1 2 54 1 55 1P3f3f80c49668f182 1 2 16 2 0 1 49 1 16 2 1 1 48 1 2 50 1 51 1P3f5530cac96289dd 0 4 0 1 41 1 47 1 48 1P3f63c9f8ab485c95 0 6 1 1 65 1 66 1 70 1 74 1 75 1N0275c38a79f11cc4N0410538492e2c6b2N059f3a9bf4b5dcdaN0bc2551a91722906N0dd7c4da7c53c1ccN1059134359e509c4N1a599162b2b6e344N1ab4544f317f7ff2N1af5d44f60022034N254ed96c13d34075N25986d9c4941e605N27152ffe4a46558bN2d48c0b92f1bcebaN2e8306b23977ac14N30b9470d56184972N31da68752ab1e019N3524d6021609c3aaN3a8c2d12f88ced85"%lxh.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import LiaOrc. (* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= orc_lia. (* [comment removed for export] *)
Local Ltac dlia ::= orc_dlia. (* [comment removed for export] *)
Local Ltac plia ::= orc_plia. (* [comment removed for export] *)
Local Ltac clear_disj ::= fc_clear_disj. (* [comment removed for export] *)
Local Ltac prune_disj ::= fc_prune_disj. (* [comment removed for export] *)
Ltac2 gd_tbl_AW_AllocB () : Init.string Init.list := ["stdpp.bitvector.definitions.bv"; "Corelib.Numbers.BinNums.Z"; "LinuxProcessSemantics.Riscv.Prelude.bvmap"; "Corelib.Init.Datatypes.option"; "Corelib.Init.Datatypes.list"; "Corelib.Init.Datatypes.prod"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_AllocA.allocA_frame"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.stk"; "RocqVerifyHarness.AgentSubmission.B.AImg.asegs"; "Stdlib.ZArith.BinInt.Z.add"; "Stdlib.ZArith.BinInt.Z.le"; "RocqVerifyHarness.AgentSubmission.AHeap.ACeil.ACEIL"; "Stdlib.ZArith.BinInt.Z.sub"; "Stdlib.ZArith.BinInt.Z.pow"; "Corelib.Init.Logic.eq"; "Stdlib.ZArith.BinInt.Z.modulo"; "RocqVerifyHarness.AgentSubmission.LibA.ALazy.crange"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.munch"; "Corelib.Init.Datatypes.cons"; "Corelib.Init.Datatypes.pair"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.wmono"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.mem_inv"; "RocqVerifyHarness.AgentSubmission.LibA.AEvtA.evtA"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.machine_state"; "Corelib.Init.Logic.and"; "RocqVerifyHarness.AgentSubmission.Lib.MState.MS"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.mkR"; "stdpp.bitvector.definitions.Z_to_bv"; "RocqVerifyHarness.AgentSubmission.Lib.MState.ret_pc"; "Corelib.Init.Datatypes.None"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.seg_rom"; "A_ALLOC_EPI"; "RocqVerifyHarness.AgentSubmission.Lib.Step.rw_cells"; "A_OOM_CELL"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.cell"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C1"; "Corelib.Init.Datatypes.nil"; "RocqVerifyHarness.AgentSubmission.Lib.Step.ro_cells"; "A_MRN_CELL"; "Corelib.Init.Logic.ex"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.nfix"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.needed2"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.A_INSTANCE"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.rz_size"; "Stdlib.ZArith.BinInt.Z.b2z"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.from_primary"; "Stdlib.ZArith.BinInt.Z.mul"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_DepotA.A_STACK_DEPOT_PUT"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C2"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C4"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C8"; "Stdlib.ZArith.BinInt.Z.land"; "Stdlib.ZArith.BinInt.Z.lt"; "Corelib.Init.Logic.or"; "ARUN_2.AllocB.hdr_post"; "Stdlib.ZArith.BinInt.Z.div"; "Stdlib.ZArith.BinInt.Z.lor"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.CB"; "Stdlib.ZArith.BinInt.Z.to_nat"; "Corelib.Lists.ListDef.repeat"; "Corelib.Init.Datatypes.bool"; "Corelib.Init.Datatypes.true"; "Corelib.Init.Logic.not"; "stdpp.bitvector.definitions.bv_unsigned"; "Stdlib.ZArith.BinInt.Z.shiftr"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_Poison.poison_statics"; "ARUN_2.AllocB.mid_post"; "ARUN_2.AllocB.pgv"; "A_GOT_FLAGS"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.A_FLAGS"; "A_FL_PPART"; "ARUN_2.AllocB.pg_post"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.class_of"; "RocqVerifyHarness.AgentSubmission.Lib.Arr.u64arr"; "Corelib.Init.Datatypes.nat"; "Corelib.Init.Datatypes.length"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_AllocA.allocA_statics"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_Unwind2.A_TP"; "ARUN_2.AllocB.st_post"; "A_GOT_LSANTLS"; "A_LSAN_CNT"; "A_MAGIC_CELL"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.kAllocBegMagic"; "A_MHOOKS"; "A_FL_MAXFILL"; "A_FL_FILLB"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_Poison.A_GOT_RMEMSET"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_Poison.A_RMEMSET"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_Poison.A_MUSL_MEMSET"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.CHUNK_ALLOCATED"; "ARUN_2.AllocB.fin_statics"; "ARUN_2.AllocB.fin_post"; "Stdlib.ZArith.BinInt.Z.min"; "ARUN_2.AllocB.fill_post"].

Section ARUN_1. Context {hAR : arun}.
Definition A_OOM_CELL : Z := 0x18bc60.      (* [comment removed for export] *)
Definition A_MRN_CELL : Z := 0x18bc61.      (* [comment removed for export] *)
Definition A_ALLOC_EPI : Z := 0x481c8.
Definition A_GOT_FLAGS : Z := 0x0f5e48.     (* [comment removed for export] *)
Definition A_FL_PPART : Z := 0x10724d.     (* [comment removed for export] *)
Definition A_FL_MAXFILL : Z := 0x107224.   (* [comment removed for export] *)
Definition A_FL_FILLB : Z := 0x10722c.     (* [comment removed for export] *)
Definition A_GOT_LSANTLS : Z := 0x0f6aa8.  (* [comment removed for export] *)
Definition A_LSAN_CNT : Z := 0x63caa0.     (* [comment removed for export] *)
Definition A_MAGIC_CELL : Z := 0x10340.    (* [comment removed for export] *)
Definition A_MHOOKS : Z := 0x19b4c0.       (* [comment removed for export] *)

(* [comment removed for export] *)
End ARUN_1.
Ltac abbrev_by e v tac :=
  let HV := fresh "D" v in let HR := fresh "R" v in
  remember e as v eqn:HV in |- *;
  assert (HR : 0 <= v < 2^64) by (rewrite HV; tac).
Ltac abbrev e v := abbrev_by e v ltac:(change (inr64 e); zrange).
Ltac abb_lor v := lazymatch goal with |- context [Z_to_bv 64 (Z.lor ?a ?b)] => abbrev (Z.lor a b) v end.

Section ARUN_2. Context {hAR : arun}.
Section AllocB.
  Variable AL : asan_layout.
  Hypothesis IMG : asan_img_ok AL.
  Hypothesis ALWF : al_wf AL.
  Variable CS : Z -> Prop.
  Hypothesis CSOK : cs_ok AL CS.
  Hypothesis ASB : al_sb AL = 0x7fff8000.
  Local Instance lxi : LxImg asegs AL := lxA_img AL IMG.   (* [comment removed for export] *)

  Ltac facts :=
    pose proof (cs_ok_sb _ _ CSOK) as SB64;
    pose proof ALWF as ALWF'; unfold al_wf in ALWF';
    pose proof IMG as IMG'; unfold asan_img_ok in IMG'.

  (* [comment removed for export] *)
  #[using="IMG ALWF CSOK"] Lemma alloc_epi : ltac2:(CDefT.buildp (gd_tbl_AW_AllocB ()) "Pgp,(0.&40.)Ptp,(0.&40.)Pt0,(0.&40.)Pt1,(0.&40.)Pt2,(0.&40.)Pa0,(0.&40.)Pa1,(0.&40.)Pa2,(0.&40.)Pa3,(0.&40.)Pa4,(0.&40.)Pa5,(0.&40.)Pa6,(0.&40.)Pa7,(0.&40.)Pt3,(0.&40.)Pt4,(0.&40.)Pt5,(0.&40.)Pt6,(0.&40.)Px1,(0.&40.)Px8,(0.&40.)Px9,(0.&40.)Px18,(0.&40.)Px19,(0.&40.)Px21,(0.&40.)Px22,(0.&40.)Px23,(0.&40.)Px24,(0.&40.)Px25,(0.&40.)Px26,(0.&40.)Px27,(0.&40.)Pres,(0.&40.)Pq0,(0.&40.)Pq1,(0.&40.)Pq2,(0.&40.)Pq3,(0.&40.)Pq4,(0.&40.)Pq5,(0.&40.)Pq6,(0.&40.)Pq7,(0.&40.)Pq8,(0.&40.)Pq9,(0.&40.)Pq10,(0.&40.)Pq11,(0.&40.)Pqra,(0.&40.)PSP,$1.Plo,$1.Pfill,$1.PF,(2.&5.(0.&40.))Pfc,(0.&20.)Pm0,P,(0.&40.)(3.(0.&8.))Pm,P,(0.&40.)(3.(0.&8.))Pfr0,(4.(0.&8.))PW,(4.(5.$1.$1.))P,(6.R3.R9.R2.R7.R:.R16.R15.R14.R13.R12.R11.R10.R?.R>.R=.R<.R;.)P,(7.$8.R4.R9.(9.R:.-80.))P,(:.(;.VhAR,)R:.)P,(:.R;.(<.R<.+80.))P,(:.R=.(=.+2.+3?.))P,(>.$1.(?.R>.+10.)=)P,(10.VCS,R>.(<.R?.R>.))P,(11.(12.(5.$1.$1.)(13.$1.$1.R?.R10.)R8.)R;.R:.)P,(14.$8.R<.R;.)P,(15.$8.R<.)(16.$8.VAL,VCS,Lms',$17.(18.(>.$17.R1.(19.(1:.R15.(1;.&40.R14.)R3?.R3>.R3=.R3<.R3;.R21.R20.R22.R39.R38.R37.R36.R35.R34.R33.R1?.R1>.R1=.R1<.R1;.R1:.R19.R18.R17.R16.R32.R31.R30.R2?.)R11.(1<.R15.)R10.(1=.(0.&40.))R>.(1>.$8.)))(7.$8.R>.R13.R14.))(19.(1:.R2=.(1;.&40.(9.R13.-80.))R3>.R3=.R3<.R3;.R3:.R2<.R2;.R39.R38.R37.R36.R35.R34.R33.R32.R2:.R29.R21.R28.R27.R26.R25.R24.R23.R22.R31.R30.R2?.R2>.)R10.(1;.&40.$1?.)R?.(1=.(0.&40.))R=.(1>.$8.)))")
(* [comment removed for export] *).
  Proof.
    try lx_hide ASB.  (* [comment removed for export] *)
    intros gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 x1 x8 x9 x18 x19 x21 x22 x23 x24 x25 x26 x27 res q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 qra
      SP lo fill F fc m0 m fr0 W FR ST LOIMG SPL SPH SPA SCS MU WM MI.
    facts. unfold allocA_frame, A_ALLOC_EPI in *.
    (* [comment removed for export] *)
    lx_hide MU. lx_hide WM. pose proof (munch_refl [(lo, SP)] m) as MU1. pose proof (wmono_refl asegs m) as WM1. lx_aceil.
    lx_run (PLAN [] [] 30%N). subst lxm. lx_unhide.
    apply evtA_done. split; [reflexivity| assumption].
  Qed.

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0010>L54082276882.300000;S2SP2lo3SPL". (* [comment removed for export] *)
  #[using="IMG ALWF CSOK"] Lemma alloc_null : ltac2:(CDefT.buildp (gd_tbl_AW_AllocB ()) "Pgp,(0.&40.)Ptp,(0.&40.)Pt0,(0.&40.)Pt1,(0.&40.)Pt2,(0.&40.)Pa1,(0.&40.)Pa2,(0.&40.)Pa3,(0.&40.)Pa4,(0.&40.)Pa5,(0.&40.)Pa6,(0.&40.)Pa7,(0.&40.)Pt3,(0.&40.)Pt4,(0.&40.)Pt5,(0.&40.)Pt6,(0.&40.)Px8,(0.&40.)Px20,(0.&40.)Px26,(0.&40.)Poomb,(0.&8.)Pq0,(0.&40.)Pq1,(0.&40.)Pq2,(0.&40.)Pq3,(0.&40.)Pq4,(0.&40.)Pq5,(0.&40.)Pq6,(0.&40.)Pq7,(0.&40.)Pq8,(0.&40.)Pq9,(0.&40.)Pq10,(0.&40.)Pq11,(0.&40.)Pqra,(0.&40.)PSP,$1.Pn,$1.PSTK,$1.Plo,$1.Pfill,$1.PT,$1.PF,(2.&5.(0.&40.))Pfc,(0.&20.)Pm0,P,(0.&40.)(3.(0.&8.))Pm,P,(0.&40.)(3.(0.&8.))Pfr0,(4.(0.&8.))PW,(4.(5.$1.$1.))P,(6.R3.R<.R2.R8.R=.R19.R18.R17.R16.R15.R14.R13.R12.R11.R10.R?.R>.)P,(20.$8.R4.$21.(12.$22.(23.R1;.)(24.$22.)))P,(25.$8.R5.$26.(12.$22.(23.(1;.&8.+1.))(24.$22.)))P,(7.$8.R6.R<.(9.R?.-80.))P,(:.(;.VhAR,)R=.)P,(:.R>.(<.R11.+80.))P,(:.R12.(=.+2.+3?.))P,(>.$1.(?.R13.+10.)=)P,(10.VCS,R11.(<.R14.R11.))P,(11.(12.(5.$1.$1.)(13.$1.$1.R12.R15.)(12.(5.$1.$1.)(13.$1.$1.$21.(9.$21.+1.))R:.))R=.R<.)P,(14.$8.R>.R=.)P,(15.$8.R>.)(16.$8.VAL,VCS,Lms',$17.(27.(0.&40.)Ly5,(0.&40.)(27.(0.&40.)Ly6,(0.&40.)(27.(0.&40.)Ly7,(0.&40.)(27.(0.&40.)Ly11,(0.&40.)(27.(0.&40.)Ly12,(0.&40.)(27.(0.&40.)Ly13,(0.&40.)(27.(0.&40.)Ly14,(0.&40.)(27.(0.&40.)Ly15,(0.&40.)(27.(0.&40.)Ly16,(0.&40.)(27.(0.&40.)Ly17,(0.&40.)(27.(0.&40.)Ly28,(0.&40.)(27.(0.&40.)Ly29,(0.&40.)(27.(0.&40.)Ly30,(0.&40.)(27.(0.&40.)Ly31,(0.&40.)(27.P,(0.&40.)(3.(0.&8.))Lm',P,(0.&40.)(3.(0.&8.))(18.(>.$17.R10.(19.(1:.R29.(1;.&40.R28.)R49.R48.R?.R>.R=.R35.R34.(1;.&40.=)R<.R;.R:.R9.R8.R7.R6.R33.R32.R31.R30.R2?.R2>.R2=.R2<.R2;.R2:.R5.R4.R3.R2.)R22.(1<.R29.)R21.(1=.(0.&40.))R1.(1>.$8.)))(18.(11.(12.(5.$1.$1.)(13.$1.$1.R25.R28.)(12.(5.$1.$1.)(13.$1.$1.$21.(9.$21.+1.))R1=.))R20.R1.)(18.(14.$8.R20.R1.)(18.(15.$8.R1.)(18.(20.$8.R1.$21.(12.$22.(23.(1;.&8.+1.))(24.$22.)))(7.$8.R1.R25.R28.)))))))))))))))))))))(19.(1:.(1;.&40.+47=34.)(1;.&40.(9.R18.-80.))R39.R38.R37.R36.R35.R29.(1;.&40.(28.R17.))(1;.&40.=)R34.R33.R32.R31.R30.R2?.R2>.(1;.&40.+8.)(1;.&40.(29.R17.))R28.(1;.&40.R17.)(1;.&40.$2:.)(1;.&40.R16.)(1;.&40.-8.)(1;.&40.+7.)R27.(1;.&40.+1.)R2=.R2<.R2;.R2:.)R12.(1;.&40.+47=34.)R11.(1=.(0.&40.))R?.(1>.$8.)))")
(* [comment removed for export] *).
  Proof.
    try lx_hide ASB.  (* [comment removed for export] *)
    intros gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 x8 x20 x26 oomb q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 qra SP n STK lo fill T F fc m0 m fr0 W
      FR OOM MRN ST LOIMG SPL SPH SPA SCS MU WM MI.
    facts. unfold A_OOM_CELL, A_MRN_CELL, A_INSTANCE in *. unfold allocA_frame in FR.
    (* [comment removed for export] *)
    lx_hide MU. lx_hide WM. pose proof (munch_refl [(lo, SP); (1621088, 1621088 + 1)] m) as MU1. pose proof (wmono_refl asegs m) as WM1.
    lx_c1_norm. lx_aceil.
    lx_run (PLAN [0x481c8] [] 30%N). lx_unhide.
    lazymatch goal with MUl : munch _ m ?mx, WMl : wmono _ m ?mx', FRl : rw_cells _ ?mx'' (SP + -128) _, STl : stk _ _ lo (SP + -128) |- _ =>
      assert (MU' : munch ((lo, SP) :: (1621088, 1621088 + 1) :: W) m0 mx) by (lx_munch MU MUl);
      assert (WM' : wmono asegs m0 mx) by (lx_wmono WM WMl);
      eapply evtA_mono;
      [ eapply alloc_epi; [exact FRl| exact STl| exact LOIMG| clear - SPL; lia| exact SPH| exact SPA| exact SCS| exact MU'| exact WM'| assumption]
      | ] end.
    cbn beta. intros ms1 (-> & ST2).
    do 14 eexists. eexists. split; [reflexivity|]. split; [eassumption|]. split; [eassumption|]. split; [eassumption|]. split; [| exact ST2].
    assumption.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Definition hdr_post (SP : Z) (gp tp s6 s7 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
      (n AB STK T TR size TID fill lo : Z) (b0 : byte) (w8 qra q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 : word) (fr0 : list byte)
      (W : list (Z * Z)) (m0 : mem) : machine_state -> Prop := ltac2:(CDefT.buildp (gd_tbl_AW_AllocB ()) "Lms',$17.(27.(0.&40.)Lx5,(0.&40.)(27.(0.&40.)Lx6,(0.&40.)(27.(0.&40.)Lx7,(0.&40.)(27.(0.&40.)Lx12,(0.&40.)(27.(0.&40.)Lx13,(0.&40.)(27.(0.&40.)Lx14,(0.&40.)(27.(0.&40.)Lx15,(0.&40.)(27.(0.&40.)Lx16,(0.&40.)(27.(0.&40.)Lx17,(0.&40.)(27.$1.Lb1,$1.(27.P,(0.&40.)(3.(0.&8.))Lm',P,(0.&40.)(3.(0.&8.))ZUB,$1.(9.O1:.(2;.O1;.))ZCB,$1.(9.R1.-10.)(18.(>.$17.R>.(19.(1:.(1;.&40.+47>40.)(1;.&40.(9.O26.-80.))O25.O24.R=.R<.R;.(1;.&40.(2<.(2=.O1;.)))(1;.&40.(28.O1;.))(1;.&40.O17.)(1;.&40.O16.)R:.R9.R8.R7.R6.R5.(1;.&40.O1:.)(1;.&40.(29.O1;.))(1;.&40.R2.)(1;.&40.R1.)(1;.&40.$2:.)(1;.&40.O19.)(1;.&40.(2>.O15.(=.+2.+20.)))(1;.&40.(9.R2.(28.O1;.)))(1;.&40.O18.)(1;.&40.+1.)O21.O20.O1?.O1>.)O1=.(1;.&40.$2?.)O1<.(1=.(0.&40.))R3.(1>.$8.)))(18.(11.(12.(5.$1.$1.)(13.$1.$1.O13.O26.)(12.(5.$1.$1.)(13.$1.$1.R1.(9.R1.+8.))O2.))O1.R3.)(18.(14.$8.O1.R3.)(18.(15.$8.R3.)(18.(20.$8.R3.R1.(12.$22.(23.O12.)(12.$22.(23.(1;.&8.R4.))(12.$22.(30.(1;.&40.=))(12.$22.(31.(1;.&40.(28.O1;.)))(12.$22.(32.O11.)(24.$22.)))))))(18.(>.$1.(33.R4.+3.)+1.)(18.(18.(:.=R4.)(34.R4.+100.))(18.(6.R3.O26.O3.O14.O10.O?.O>.O=.O<.O;.O:.O9.O8.O7.O6.O5.O4.)(7.$8.R3.O13.(9.O26.-80.)))))))))))))))))))))")
(* [comment removed for export] *).

  Local Ltac2 Set LiaOrc.tbl := fun () => "0020>L36948952422.9L41415985948.9000001002SS". (* [comment removed for export] *)
  #[using="Type"] Lemma byte1_type : forall b, 0 <= b -> Z.land (Z.lor (Z.land (Z.lor (b / 4 * 4) 1) 143) 16) 3 = 1.
  Proof.
    try lx_hide ASB.  (* [comment removed for export] *)
    intros b Hb. rewrite Z.land_lor_distr_l. change (Z.land 16 3) with 0. rewrite Z.lor_0_r.
    rewrite <- Z.land_assoc. change (Z.land 143 3) with 3.
    rewrite Z.land_lor_distr_l. change (Z.land 1 3) with 1.
    replace (Z.land (b / 4 * 4) 3) with 0; [reflexivity|].
    change 3 with (Z.ones 2). rewrite Z.land_ones by lia. change (2^2) with 4. symmetry. apply Z.mod_mul. lia.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0060?L22628597481.13L36948952422.9 L40818989526.10L47285983339.11L51523493787.11L62997512221.1200000300400700:00E00HS1bSS1bS1bS1b2Hb1H2H0S1b". (* [comment removed for export] *)
  #[using="Type"] Lemma byte1_range : forall b, 0 <= b < 256 -> 0 <= Z.lor (Z.land (Z.lor (b / 4 * 4) 1) 143) 16 < 256.
  Proof.
    try lx_hide ASB.  (* [comment removed for export] *)
    intros b Hb.
    pose proof (Z.div_mod b 4 ltac:(lia)). pose proof (Z.mod_pos_bound b 4 ltac:(lia)).
    pose proof (lor_lt_pow2 (b / 4 * 4) 1 8 ltac:(change (2^8) with 256; lia) ltac:(change (2^8) with 256; lia)) as L1.
    pose proof (land_lt_pow2 _ 143 8 L1 ltac:(lia)) as L2.
    pose proof (lor_lt_pow2 _ 16 8 L2 ltac:(change (2^8) with 256; lia)) as L3. change (2^8) with 256 in L3. exact L3.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  Local Ltac2 Set LiaOrc.tbl := fun () => "0030>L22538140902.9L29784458902.9L59858123514.9000001002008SSS1x2Hx". (* [comment removed for export] *)
  #[using="Type"] Lemma land_align3_48 : forall x, 0 <= x < 2^48 -> Z.land x 281474976710648 = x / 8 * 8.
  Proof.
    try lx_hide ASB.  (* [comment removed for export] *)
    intros x Hx. change 281474976710648 with (Z.land (Z.ones 48) (Z.lnot (Z.ones 3))).
    rewrite Z.land_assoc. rewrite Z.land_ones by lia. rewrite Z.mod_small by lia.
    rewrite <- Z.ldiff_land. rewrite Z.ldiff_ones_r by lia. rewrite Z.shiftr_div_pow2, Z.shiftl_mul_pow2 by lia. reflexivity.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  Local Ltac2 Set LiaOrc.tbl := fun () => "01=0@L1436302703.105 L15529037723.2  L17103580878.108L17120848823.0  L18710949931.103L19266651282.113L19360177296.107L20820893526.103L21670288697.110L22536132876.110L23495232381.108L23551740665.111L23891804518.105L24636217014.103L24886574194.106L24886869106.107L25892384694.109L27288736413.108L27705282402.5  L28444277430.103L28618029051.103L28618181755.103L28620141803.102L29520871357.102L29522951341.103L29523101485.103L30509333168.7  L31060563217.105L32817229114.3  L33383682929.110L34541196294.103L34541301638.103L34543245078.102L34997063485.103L35818860552.2  L35909741472.107L36193165570.2  L38426169019.105L39188636933.0  L39566357149.103L39932040506.106L40486684892.113L41137568973.108L42650174943.113L42888437729.103L43352073929.113L44015215498.112L44017160204.110L45914037331.111L46260406027.103L48075607928.2  L49698585326.112L49705053714.111L5039651420.5   L50652529336.105L51037555200.106L51238711297.105L51517722631.6  L51721024632.105L52516259088.107L55473271140.106L58375705760.2  L59049942805.102L59308630368.3  L59308630497.5  L59308632823.3  L59696744469.107L59696744469.108L60078711951.110L61030858054.103L61929802144.106L63374621462.104L64748691813.108L65869151173.108L7134986454.105 L8171652662.109 L8929162512.106 00000A00J00[00\00]01d02502?02W02h03903S03b03l04=04N04k05<05D05X05Y05Z05[05e05o06906T06e06o07C07M07W07a07k08308h08k09<09=09G09k0:V0:g0;k0<;0<h0=<0=M0=b0=c0=k0>F0>[0>h0?90?J0?Y0@30@D0@U0AO0AU0BB0BM0BZ0Bc0C40CE0C[0D20DF0D]0Dn0E?0EP0F?0G?S3hAR2b11n2AB3STKS2b14B1R'S3hAR2SP1n2AB3STKSFS3hAR2b12SP1n2AB3STK2lo3AB02K02K12HB5LOIMG3SPL4RZSB3B1R3HB05Ha_st5Hl_stS3hAR2SP1n2AB3STKS3hAR1n2ABS3hAR2b12SP1n2AB3STK3CTXS3hAR2SP1n2AB3STKS3hAR2SP1n2AB3STKS3hAR2SP1n2AB3STK2lo1W3HB0S3hAR2b11n2AB1TS3hAR1n2ABS3hAR2SP1n2AB3STKS3hAR2SP1n2AB3STKS3hAR2b12SP1n2AB3STK3TID4TIDBS3hAR2SP1n2AB3STKS1n1H2H0S3hAR2SP1n2AB2lo3SPLFFFS3hAR1n2ABS3hAR1n2ABS3hAR1n2ABS1n2AB3AB03AB14RZSB3NFB3N2BS3hAR2b11n2AB3CTXS1n2NB3NFBS3hAR2b12SP1n2AB3STKS3hAR1n2ABS3hAR1n2ABS3hAR1n2ABS3hAR1n2ABS2b13B1RS3hAR2b12SP1n2AB3STK2lo3AB02K05LOIMG3SPL3SPA4RZSB3B1RS1nS3hAR2b11n2AB3STKSS3hAR1n2ABS3hAR2SP1n2AB3STK2NB3AB02K04RZSB3NFBS3hAR2b12SP1n2AB3STK1T4TSEP3HB05Ha_st5Hl_stS3hAR2SP1n2AB3STKS3hAR2b12SP1n2AB3STK2lo3AB02K02HB5LOIMG3SPL4RZSB3B1R3HB05Ha_st5Hl_stS3hAR2SP1n2AB2loS3hAR2b12SP1n2AB3STK3CTX4CSEP3HB05Ha_st5Hl_stS3hAR2b12SP1n2AB3STKS3hAR2SP1n2AB3STKS3hAR2SP1n2AB3STK3HB0FS2b13B1RS3hAR2SP1n2AB3STK3HB05Ha_stS3hAR2SP1n2AB3STK3HB0S1n4RZSB1H2H0S3hAR2b11n2AB3STKS3hAR2SP1n2AB3STKS3hAR2b11n2AB1TS1n2AB4ABAL4RZ164DA164DR16S3hAR2b11n2AB3CTXS3hAR2SP1n2AB3STKS3hAR2SP1n2AB3STK2lo3AB03AB12K05LOIMG3SPL4RZSB3NFB3N2B3ABRS1n2NBS3hAR2SP1n2AB3STK2lo3AB02K02HB5LOIMG3SPL4RZSBS2AB3AB02KAS1n2AB3N2B2KBS1T2T02KTS3hAR2SP1n2AB3STKS3hAR2SP1n2AB3STKS3hAR2b12SP1n2AB3STK1TS3hAR2SP1n2AB3STK2UB2CBS3hAR2SP1n2AB3STK2NBS3hAR2SP1n2AB3STK2UB2CBS3hAR2SP1n2AB3STKS3hAR2SP1n2AB3STKS3hAR2b11n2AB3STKS3hAR2b12SP1n2AB3STK1T3AB02K02T02T14RZSB2KA3B1RS3hAR2SP1n2AB3STK2lo2NB3AB03AB12K02HB5LOIMG3SPL4RZSB3NFB3N2B3ABR". (* [comment removed for export] *)
  #[using="IMG ALWF CSOK"] Lemma alloc_hdr : ltac2:(CDefT.buildp (gd_tbl_AW_AllocB ()) "Pgp,(0.&40.)Ptp,(0.&40.)Pt0,(0.&40.)Pt1,(0.&40.)Pt2,(0.&40.)Pa1,(0.&40.)Pa2,(0.&40.)Pa3,(0.&40.)Pa4,(0.&40.)Pa5,(0.&40.)Pa6,(0.&40.)Pa7,(0.&40.)Pt3,(0.&40.)Pt4,(0.&40.)Pt5,(0.&40.)Pt6,(0.&40.)Pb0,(0.&8.)Pb1,(0.&8.)Pw2,(0.&40.)Pw4,(0.&40.)Pw8,(0.&40.)Pq0,(0.&40.)Pq1,(0.&40.)Pq2,(0.&40.)Pq3,(0.&40.)Pq4,(0.&40.)Pq5,(0.&40.)Pq6,(0.&40.)Pq7,(0.&40.)Pq8,(0.&40.)Pq9,(0.&40.)Pq10,(0.&40.)Pq11,(0.&40.)Pqra,(0.&40.)PSP,$1.Pn,$1.PAB,$1.PSTK,$1.PT,$1.PCTX,$1.PTR,$1.Psize,$1.PTID,$1.Plo,$1.Pfill,$1.PF,(2.&5.(0.&40.))Pfc,(0.&20.)Pm0,P,(0.&40.)(3.(0.&8.))Pm,P,(0.&40.)(3.(0.&8.))Pfr0,(4.(0.&8.))PW,(4.(5.$1.$1.))ZUB,$1.(9.R?.(2;.R10.))ZCB,$1.(9.R1.-10.)P,(18.(:.=R12.)(34.R12.(=.+2.+20.)))P,(34.=R12.)P,(:.(9.R13.(29.R14.))(=.+2.+2?.))P,(>.$1.(?.R14.+10.)=)P,(18.(:.=R11.)(34.R11.(=.+2.+40.)))P,(18.(:.=R11.)(34.R11.(=.+2.+20.)))P,(18.(:.=R11.)(34.R11.(=.+2.+1?.)))P,(18.(:.=R10.)(:.R10.+1.))P,(:.+65?000.R18.)P,(:.R1<.R19.)P,(:.(9.R1:.+10.)(=.+2.+3>.))P,(>.$1.(?.R1;.+8.)=)P,(10.VCS,R1<.+10.)P,(18.(:.+1000.R1<.)(35.(:.(9.R1<.+1000.)+10000.)(:.+65?000.R1<.)))P,(:.(9.R1=.+1000.)(;.VhAR,))P,(10.VCS,R1>.+1000.)P,(:.+65?000.R1>.)P,(:.(9.R1?.+10000.)(;.VhAR,))P,(10.VCS,R20.+10000.)P,(10.VCS,R14.+10.)P,(35.(:.(9.R15.+10.)R24.)(:.(9.R24.+10.)R15.))P,(:.(9.R16.+10.)(;.VhAR,))P,(35.(:.(9.R17.+10.)R25.)(:.(9.R25.+1000.)R17.))P,(35.(:.(9.R18.+10.)R25.)(:.(9.R25.+10000.)R18.))P,(6.R1=.R2;.R1<.R21.R2<.R38.R37.R36.R35.R34.R33.R32.R31.R30.R2?.R2>.R2=.)P,(20.$8.R1>.R1:.(12.$22.(23.R3>.)(12.$22.(23.R3=.)(12.$22.(30.R3<.)(12.$22.(31.R3;.)(12.$22.(32.R3:.)(24.$22.)))))))P,(25.$8.R1?.R29.(12.$22.(32.(1;.&40.R28.))(24.$22.)))P,(25.$8.R20.(9.R29.+8.)(12.$22.(31.(1;.&40.R26.))(24.$22.)))P,(25.$8.R21.R2<.(12.$22.(32.(1;.&40.R29.))(12.$22.(32.(1;.&40.R28.))(24.$22.))))P,(7.$8.R22.R27.(9.R30.-80.))P,(:.(;.VhAR,)R28.)P,(:.R29.(<.R32.+80.))P,(:.R33.(=.+2.+3>.))P,(>.$1.(?.R34.+10.)=)P,(10.VCS,R2<.(<.R35.R2<.))P,(11.(12.(5.$1.$1.)(13.$1.$1.R2=.R36.)(12.(5.$1.$1.)(13.$1.$1.R24.(9.R24.+8.))R26.))R29.R28.)P,(14.$8.R2:.R29.)P,(15.$8.R2:.)(16.$8.VAL,VCS,(36.R39.R5;.R5:.(1;.&40.$2:.)(1;.&40.R36.)R4?.R4>.R4=.R4<.R2>.R2=.R38.R37.R36.R35.R33.R32.R31.R2?.R30.R4;.R47.R3:.R46.R45.R44.R43.R42.R41.R40.R3?.R3>.R3=.R3<.R3;.R2:.R29.R2<.)(19.(1:.(1;.&40.+47=34.)(1;.&40.(9.R39.-80.))R5;.R5:.R59.R58.R57.(1;.&40.(2<.(2=.R38.)))(1;.&40.(28.R38.))(1;.&40.R37.)R56.R55.R54.R53.R52.R51.R50.(1;.&40.+8.)(1;.&40.(29.R38.))(1;.&40.(2;.R38.))(1;.&40.R38.)(1;.&40.$2:.)(1;.&40.R36.)(1;.&40.-8.)(1;.&40.+7.)(1;.&40.R35.)(1;.&40.+1.)R4?.R4>.R4=.R4<.)R2>.(1;.&40.+47=34.)R2=.(1=.(0.&40.))R2;.(1>.$8.)))")
(* [comment removed for export] *).
  Proof.
    try lx_hide ASB.  (* [comment removed for export] *)
    intros gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 b0 b1 w2 w4 w8 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 qra SP n AB STK T CTX TR size TID lo fill F fc m0 m fr0 W
      UB CB NB AB0 AB1 ABAL TRB SZB TIDB FB K0 K1 K2 KAL KCS T0 T1 TCS C0 C1 CCS HCS HSEP HB TSEP CSEP FR HDR TH TIDC STC ST LOIMG SPL SPH SPA SCS MU WM MI.
    facts. unfold A_INSTANCE, A_STACK_DEPOT_PUT in *. unfold allocA_frame in FR.
    pose proof (rz_size_bound n) as RZSB.
    assert (NFB : 1 <= nfix n <= Z.max n 1) by (unfold nfix; clear - NB; lia).
    assert (N2B : nfix n + rz_size n <= needed2 n).
    { unfold needed2, needed, rounded, round_up. pose proof (Z.div_mod (Z.max n 8 + 8 - 1) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (Z.max n 8 + 8 - 1) 8 ltac:(lia)).
      destruct (from_primary n); unfold nfix; clear - H H0 NB RZSB; lia. }
    assert (HUB : UB = AB + rz_size n) by reflexivity. subst CB. subst UB.
    assert (ABR : 0 <= AB < 2^64) by (clear - AB0 AB1 RZSB NFB N2B; lia).
    (* [comment removed for export] *)
    zstep. zstep. if_cases KA; zify_cond KA. { exfalso. clear - KA AB0. lia. }
    zstep. zstep. zstep.
    assert (RZ16 : rz_size n mod 16 = 0) by (unfold rz_size; rewrite Z.mul_comm; apply Z_mod_mult).
    pose proof (Z.div_mod AB 16 ltac:(lia)) as DA16. pose proof (Z.div_mod (rz_size n) 16 ltac:(lia)) as DR16.
    replace (Z.land (AB + rz_size n) 7) with 0.
    2:{ symmetry. change 7 with (Z.ones 3). rewrite Z.land_ones by (clear; lia). change (2^3) with 8.
        replace (AB + rz_size n) with ((AB / 16 * 2 + rz_size n / 16 * 2) * 8) by (clear - DA16 DR16 ABAL RZ16; lia).
        apply Z.mod_mul. clear; lia. }
    zstep.
    (* [comment removed for export] *)
    zstep. zstep. if_cases KB; zify_cond KB. { exfalso. clear - KB N2B HUB. lia. }
    zstep. zstep. zstep. zstep. zstep. zstep.
    pose proof (bv_unsigned_in_range 8 b1) as B1R. unfold bv_modulus in B1R. change (2 ^ Z.of_N 8) with 256 in B1R.
    rewrite (land_align2 (bv_unsigned b1)) by (clear - B1R; lia).
    rewrite !Z.shiftr_div_pow2 by lia. rewrite (Z.div_small (nfix n) (2^32)) by (clear - NFB NB; lia). rewrite (Z.div_small n (2^48)) by (clear - NB; lia).
    zstep. zstep. zstep.
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep. zstep. zstep.
    pose proof (byte1_range (bv_unsigned b1) B1R) as B1R'.
    match goal with H : rw_cells _ _ (AB + rz_size n + -16) _ |- _ =>
      rewrite (unsigned_lit (Z.lor (Z.land (Z.lor (bv_unsigned b1 / 4 * 4) 1) 143) 16)) in H by (clear - B1R'; lia) end.
    zstep. if_cases KT; zify_cond KT. { exfalso. clear - KT T0. lia. }
    zstep. zstep. rewrite (sx32_small TID) by exact TIDB. zstep. rewrite Z.shiftl_mul_pow2 by lia. zstep. zstep. zstep. zstep.
    apply evtA_done. unfold hdr_post. do 9 eexists. exists (Z.lor (Z.land (Z.lor (bv_unsigned b1 / 4 * 4) 1) 143) 16). eexists.
    split; [reflexivity|]. split; [eassumption|]. split; [eassumption|]. split; [eassumption|].
    split.
    { match goal with H : rw_cells _ _ (AB + rz_size n + -16) _ |- _ => exact H end. }
    split; [apply byte1_type; clear - B1R; lia|]. split; [exact B1R'|].
    split; [exact FR| assumption].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Definition mid_post (SP : Z) (gp tp t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
      (n AB STK T TID id lo : Z) (b0 : byte) (b1 : Z) (W : list (Z * Z)) (m0 : mem) : machine_state -> Prop := ltac2:(CDefT.buildp (gd_tbl_AW_AllocB ()) "Lms',$17.(27.(0.&40.)Lx1,(0.&40.)(27.(0.&40.)Lx5,(0.&40.)(27.(0.&40.)Lx6,(0.&40.)(27.(0.&40.)Lx7,(0.&40.)(27.(0.&40.)Lx10,(0.&40.)(27.(0.&40.)Lx11,(0.&40.)(27.(0.&40.)Lx12,(0.&40.)(27.(0.&40.)Lx13,(0.&40.)(27.(0.&40.)Lx14,(0.&40.)(27.(0.&40.)Lx15,(0.&40.)(27.(0.&40.)Lx16,(0.&40.)(27.(0.&40.)Lx17,(0.&40.)(27.(0.&40.)Lx28,(0.&40.)(27.(0.&40.)Lx29,(0.&40.)(27.(0.&40.)Lx30,(0.&40.)(27.(0.&40.)Lx31,(0.&40.)(27.P,(0.&40.)(3.(0.&8.))Lm',P,(0.&40.)(3.(0.&8.))ZUB,$1.(9.O:.(2;.O;.))ZCHB,$1.(9.R1.-10.)Zrd,$1.(2>.(37.(28.O;.)+8.)+8.)ZS,$1.(9.+7???8000.(37.R3.+8.))(18.(>.$17.R16.(19.(1:.R15.(1;.&40.(9.O14.-80.))O13.O12.R14.R13.R12.(1;.&40.+1.)(1;.&40.(28.O;.))R11.R10.R?.R>.R=.R<.R;.R:.(1;.&40.O:.)(1;.&40.(29.O;.))(1;.&40.R4.)(1;.&40.R3.)(1;.&40.R2.)(1;.&40.O9.)(1;.&40.(2>.O7.(=.+2.+20.)))(1;.&40.(9.R4.(28.O;.)))(1;.&40.O8.)(1;.&40.+1.)R9.R8.R7.R6.)O=.(1;.&40.+47?4<.)O<.(1=.(0.&40.))R5.(1>.$8.)))(18.(11.(12.(5.$1.$1.)(13.$1.$1.O5.(9.O14.-80.))(12.(5.$1.$1.)(13.$1.$1.(9.R3.+8.)(9.R3.+10.))(12.(5.$1.$1.)(13.$1.$1.R1.(9.R1.(37.(28.O;.)+8.)))O2.)))O1.R5.)(18.(14.$8.O1.R5.)(18.(15.$8.R5.)(18.(20.$8.R5.R3.(12.$22.(23.O4.)(12.$22.(23.(1;.&8.O3.))(12.$22.(30.(1;.&40.=))(12.$22.(31.(1;.&40.(28.O;.)))(12.$22.(32.(1;.&40.(38.(2>.O7.(=.+2.+20.))O6.)))(24.$22.)))))))(18.(20.$8.R5.R1.(12.$22.(39.(3:.(37.(28.O;.)+8.))(3;.(0.&8.)(1;.&8.=)(3:.(37.(28.O;.)+8.))))(24.$22.)))(7.$8.R5.O5.(9.O14.-80.)))))))))))))))))))))))))")
(* [comment removed for export] *).

  Local Ltac2 Set LiaOrc.tbl := fun () => "01?0@L10199067881.90 L11138871060.96 L11359100080.6  L11803451283.8  L13137448400.94 L13446183429.93 L14240527925.3  L17765151508.96 L18709141715.6  L20752521299.3  L21804531514.90 L21866500762.90 L24886574194.88 L24886869106.89 L2491586324.96  L25500551059.96 L2592073154.93  L27848808849.2  L2941547076.2   L2945511925.90  L29786560764.94 L30299332372.96 L30510940417.93 L31401084973.90 L33226931961.15 L33719216517.3  L34271598851.90 L35250499860.96 L35549638197.2  L36193165570.2  L36711226554.90 L36882464643.90 L3703053403.89  L38235734261.1  L39188636933.0  L39932042925.94 L42982048663.92 L43840837351.90 L43903340878.5  L43935890344.95 L44530674043.92 L45914037331.94 L46230795540.96 L47133023755.93 L4886495495.89  L49698585326.95 L50966866708.96 L51251319469.90 L51517722631.6  L53534827008.90 L54412534036.96 L54548667962.3  L55676403476.96 L5622942713.2   L58695105879.92 L59579477147.92 L60864533053.93 L61024651250.90 L61030987373.87 L61031281911.96 L61031298161.118L61031299693.97 L63043066215.90 L63044210349.15 L63370229784.91 L63374621462.88 L63867716001.0  L64781239060.96 L66713253421.90 L67259945748.96 L67298408978.5  L67803736237.90 L68364611860.96 L68629982834.14 L7258948116.96  L7409756072.5   L8265267294.0   L8361534166.2   L938672012.7    00000:01K01W02602C02P02Z03k04?04J04K04f05305@06Q07d08108808908W08d0:50:W0:a0;<0;G0;H0<Y0<a0<d0<e0<f0=50=90=:0=X0=Y0=k0>=0?D0?X0?h0A90AM0Ah0B>0CO0CY0D30DF0EW0Ea0G20G:0H>0HK0HX0He0I;0IH0IU0Ib0J40JY0Jf0K<0K=0LN0Lm0N>0NP0No0P@0Pi0R:0RI0RJ0RR0RjS3hAR1n2ABS3hAR2SP1n2AB3TID2id2lo3AB04ABAL5LOIMG3SPL4RZSB3NFB4RZ164DA164DR162HB5Ha_st5Hl_stS1n3FP'1H2H0S3hAR1n2AB3AB03RNG4RZSB3NFB3N2BS3hAR2SP1n2ABS3hAR2SP1n2ABS1n3NFB2KZS3hAR2SP1n2AB3TID2id2lo3AB04ABAL5LOIMG3SPL4RZSB3NFB4RZ164DA164DR162HB5Ha_st5Hl_stS1n4RZSB3NFB3N2B3DNFS2SP2lo3SPLFS3hAR1n2AB3AB04RZSB3NFB3N2BS3hAR2SP1n2ABS3hAR2SP1n2ABS3hAR2SP1n2AB3TID2id2lo3AB04ABAL5LOIMG3SPL4RZSB3NFB4RZ164DA164DR162HB5Ha_st5Hl_stS3hAR2SP1n2AB3TID2id2lo3AB04ABAL3RNG5LOIMG3SPL3SPA4RZSB3NFB3N2B4RZ162HB5Ha_st5Hl_stS3hAR2SP1n2ABS2SP2loFS3hAR2AL3ASB1n2AB3AB04RZSB3NFBS3hAR2SP1n2ABS3hAR2SP1n2AB3TID2id2lo3AB04ABAL5LOIMG3SPL4RZSB3NFB4RZ164DA164DR162HB5Ha_st5Hl_stS3hAR2SP1n2AB3AB04RZSB3NFB3N2B3ABRS3hAR1n2ABS3hAR1n2AB3RNG4RZSB3NFB3N2BS1n2AB4RZSBFS3hAR2SP1n2AB3TID2id2lo3AB04ABAL5LOIMG3SPL4RZSB3NFB4RZ164DA164DR162HB5Ha_st5Hl_stS2SP3SPAS1nFFS3hAR1n2AB4RZSBS2loSS3hAR2SP1n2AB3AB04RZSB3NFB3N2BFS3hAR2AL1n2AB4IMG'S3hAR1n2AB3AB03RNGS3hAR2SP1n2AB2lo3AB04ABAL5LOIMG3SPL4RZSB3NFB3N2B4RZ164DA164DR163DNF3MNFS3hAR2SP1n2AB2id3IDBS3hAR2SP1n2AB2HBS3hAR2SP1n2AB3TID2id2lo3AB04ABAL5LOIMG3SPL4RZSB3NFB4RZ164DA164DR162HB5Ha_st5Hl_stS3hAR2SP1n2AB2id3IDBS3hAR1n2AB3AB04RZSB3NFB3N2BS3hAR2SP1n2AB2HB5Ha_stS3hAR2SP1n2AB3TID2id2lo3AB04ABAL5LOIMG3SPL4RZSB3NFB4RZ164DA164DR162HB5Ha_st5Hl_stS3hAR1n2ABS1n2AB4ABAL4RZ164DA164DR16S3hAR2AL1n2AB5ALWF'S3hAR2SP1n2AB3TID2id2lo3AB04ABAL5LOIMG3SPL4RZSB3NFB4RZ164DA164DR162HB5Ha_st5Hl_stS1n2NB3NFBS3hAR2SP1n2AB3TID2id2lo3AB04ABAL5LOIMG3SPL4RZSB3NFB4RZ164DA164DR162HB5Ha_st5Hl_stS2id3IDBS3hAR2SP1n2AB3TID2lo3AB04ABAL4TIDB5LOIMG3SPL4RZSB3NFB4RZ164DA164DR16S3hAR2SP1n2ABS3hAR2SP1n2ABS3hAR2SP1n2ABS3hAR2SP1n2AB2UB3CHB1SS3hAR2SP1n2ABS3hAR2SP1n2ABS3hAR2SP1n2ABS3hAR2AL1n2AB4IMG'S3hAR2SP1n2AB2lo3RNG5LOIMG3NFB3N2B2KZS3hAR2SP1n2ABS3hAR2SP1n2AB2UB3CHB1SSS3hAR2SP1n2AB3TID2id2lo3AB04ABAL5LOIMG3SPL4RZSB3NFB4RZ164DA164DR162HB5Ha_st5Hl_stS3hAR2AL1n2AB3AB04IMG'4RZSB3NFBS3hAR2SP1n2AB3TID2id2lo3AB04ABAL5LOIMG3SPL4RZSB3NFB4RZ164DA164DR162HB5Ha_st5Hl_stS1n2AB3N2B3DNF3MNFS3hAR2AL1n2AB3AB04IMG'4RZSB3NFBS3hAR2SP1n2AB3TID2id2lo3AB04ABAL5LOIMG3SPL4RZSB3NFB4RZ164DA164DR162HB5Ha_st5Hl_stS3hAR1n2AB3AB04ABAL3RNG4RZSB3NFB3N2B4RZ16S3hAR2SP1n2AB3TID2id2lo3AB04ABAL5LOIMG3SPL4RZSB3NFB4RZ164DA164DR162HB5Ha_st5Hl_stS1n3NFB3DNF3MNFSS2SP3SPHS1n2AB3AB04RZSB2A02k02Hk". (* [comment removed for export] *)
  #[using="IMG ALWF CSOK ASB"] Lemma alloc_mid : ltac2:(CDefT.buildp (gd_tbl_AW_AllocB ()) "Pgp,(0.&40.)Ptp,(0.&40.)Px5,(0.&40.)Px6,(0.&40.)Px7,(0.&40.)Px11,(0.&40.)Px12,(0.&40.)Px13,(0.&40.)Px14,(0.&40.)Px15,(0.&40.)Px16,(0.&40.)Px17,(0.&40.)Px28,(0.&40.)Pt3,(0.&40.)Pt4,(0.&40.)Pt5,(0.&40.)Pt6,(0.&40.)Pb0,(0.&8.)Pshb,(0.&8.)Pw8,(0.&40.)PSP,$1.Pn,$1.PAB,$1.PSTK,$1.PT,$1.PTID,$1.Pid,$1.Plo,$1.Pb1,$1.PF,(2.&5.(0.&40.))Pfc,(0.&20.)Pm0,P,(0.&40.)(3.(0.&8.))Pm,P,(0.&40.)(3.(0.&8.))Pjunk,(4.(0.&8.))PW,(4.(5.$1.$1.))ZUB,$1.(9.R=.(2;.R>.))ZCHB,$1.(9.R1.-10.)ZS,$1.(9.+7???8000.(37.R2.+8.))P,(18.(:.=R11.)(34.R11.(=.+2.+20.)))P,(>.$3<.(2=.R12.)$3=.)P,(:.+65?000.R12.)P,(>.$1.(?.R13.+10.)=)P,(35.(:.(9.R14.(29.R15.))+7???8000.)(18.(:.+10007???8000.R14.)(:.(9.R14.(29.R15.))(;.VhAR,))))P,(18.(:.=R12.)(34.R12.(=.+2.+1?.)))P,(18.(:.=R12.)(34.R12.(=.+2.+1?.)))P,(18.(:.=R11.)(34.R11.+100.))P,(3>.(>.$1.(3?.&8.R1<.)=))P,(10.VCS,R19.(29.R1:.))P,(20.$8.R10.R<.(12.$22.(23.R1?.)(12.$22.(23.(1;.&8.R14.))(12.$22.(30.(1;.&40.=))(12.$22.(31.(1;.&40.(28.R1;.)))(12.$22.(32.R1=.)(24.$22.)))))))P,(25.$8.R11.(9.+7???8000.(40.R1;.+3.))(12.$22.(23.R1?.)(24.$22.)))P,(20.$8.R12.R=.(12.$22.(39.(3:.(37.(28.R1=.)+8.))R11.)(24.$22.)))P,(41.R13.)P,(7.$8.R14.R19.(9.R20.-80.))P,(:.(;.VhAR,)R1:.)P,(:.R1;.(<.R22.+200.))P,(:.R23.(=.+2.+3>.))P,(>.$1.(?.R24.+10.)=)P,(10.VCS,R1>.(<.R25.R1>.))P,(11.(12.(5.$1.$1.)(13.$1.$1.R1?.(9.R26.-80.))(12.(5.$1.$1.)(13.$1.$1.(9.R16.+8.)(9.R16.+10.))(12.(5.$1.$1.)(13.$1.$1.R15.(9.R15.(37.(28.R25.)+8.)))R18.)))R1;.R1:.)P,(14.$8.R1<.R1;.)P,(15.$8.R1<.)(16.$8.VAL,VCS,(42.R29.R3=.R3<.R30.R2?.R2>.R2=.R20.R1?.R28.R27.R26.R25.R24.R23.R22.R2<.R21.R1;.R1>.)(19.(1:.(1;.&40.+47>40.)(1;.&40.(9.R29.-80.))R3=.R3<.R3;.R3:.R39.(1;.&40.+1.)(1;.&40.(28.R28.))(1;.&40.R23.)R38.R37.R36.R35.R34.R33.R32.(1;.&40.R27.)(1;.&40.(29.R28.))(1;.&40.R1:.)(1;.&40.R19.)(1;.&40.$2:.)(1;.&40.R26.)(1;.&40.(2>.R24.(=.+2.+20.)))(1;.&40.(9.R1:.(28.R28.)))(1;.&40.R25.)(1;.&40.+1.)R31.R2?.R2>.R2=.)R20.(1;.&40.+47>40.)R1?.(1=.(0.&40.))R1=.(1>.$8.)))")
(* [comment removed for export] *).
  Proof.
    intros gp tp x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 t3 t4 t5 t6 b0 shb w8 SP n AB STK T TID id lo b1 F fc m0 m junk W UB CHB S
      NB FP AB0 ABAL RNG TIDB IDB B1B SHB ACS HDR SHC SH PS ST LOIMG SPL SPH SPA SCS MU WM MI.
    facts. unfold A_INSTANCE in *.
    pose proof PS as (CP & G1 & SB & G2 & MB & G3 & ME & G4 & HE & G5 & RM & G6 & CT).
    unfold A_CANPOISON, A_GOT_SB, A_SBCELL, A_GOT_MIDBEG, A_MIDBEG, A_GOT_MIDEND, A_MIDEND, A_GOT_HIGHEND, A_HIGHEND,
      A_GOT_RMEMSET, A_RMEMSET, A_GOT_CFLAGS, A_CFLAGS, A_CF_CSMT, A_MUSL_MEMSET in *.
    pose proof (rz_size_bound n) as RZSB.
    assert (NFB : 1 <= nfix n <= Z.max n 1) by (unfold nfix; clear - NB; lia).
    assert (N2B : nfix n + rz_size n <= needed2 n /\ needed2 n <= 65536).
    { pose proof FP as FP'. unfold from_primary, kMaxSize in FP'. apply Z.leb_le in FP'.
      unfold needed2. rewrite FP. unfold needed, rounded, round_up in *.
      pose proof (Z.div_mod (Z.max n 8 + 8 - 1) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (Z.max n 8 + 8 - 1) 8 ltac:(lia)).
      unfold nfix; clear - H H0 NB RZSB FP'; lia. }
    assert (HUB : UB = AB + rz_size n) by reflexivity. assert (HS : S = 0x7fff8000 + UB / 8) by reflexivity. subst CHB S UB.
    assert (ABR : 0 <= AB /\ AB + needed2 n <= 2^47) by (clear - AB0 RNG; lia).
    assert (RZ16 : rz_size n mod 16 = 0) by (unfold rz_size; rewrite Z.mul_comm; apply Z_mod_mult).
    pose proof (Z.div_mod AB 16 ltac:(lia)) as DA16. pose proof (Z.div_mod (rz_size n) 16 ltac:(lia)) as DR16.
    pose proof (Z.div_mod (nfix n) 8 ltac:(lia)) as DNF. pose proof (Z.mod_pos_bound (nfix n) 8 ltac:(lia)) as MNF.
    (* [comment removed for export] *)
    pose proof (munch_refl [(AB + rz_size n + -16 + 8, AB + rz_size n + -16 + 16)] m) as MU2.
    assert (SHW : True -> ro_cells asegs m (2147450880 + Z.shiftr AB 3) [C1 shb]) by (intros _; exact SHC). clear SHC.
    zstep. zstep. zstep. rewrite (Z.mod_small id 4294967296) by (clear - IDB; lia). change 4294967296 with (2^32). zstep.
    lazymatch goal with |- context [MS _ _ _ _ _ ?mc _] =>
      assert (SHC1 : ro_cells asegs mc (2147450880 + Z.shiftr AB 3) [C1 shb])
        by (eapply ro_cells_transport; [exact (SHW I)| exact MU2|]; cbn [disjoint_from cells_size csize]; rewrite Z.shiftr_div_pow2 by lia;
            change (2^3) with 8; clear - RNG AB0 RZSB NFB N2B; lia) end.
    clear SHW.
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep. zstep. zstep. zstep.
    zstep. if_cases KS; zify_cond KS. 2:{ exfalso. apply SHB. clear - KS. exact KS || lia. }
    (* [comment removed for export] *)
    zstep. zstep. zstep. rewrite (land_align3_48 (nfix n)) by (clear - NFB NB; lia).
    Ltac mid_leaf :=
      apply evtA_done; unfold mid_post; do 16 eexists; eexists; split; [reflexivity|];
      split; [eassumption|]; split; [eassumption|]; split; [eassumption|];
      split; [ match goal with H : rw_cells _ _ (_ + rz_size _ + -16) _ |- _ => exact H end |];
      split; [| assumption].
    zstep. if_cases KZ; zify_cond KZ.
    - (* [comment removed for export] *)
      mid_leaf.
      replace (nfix n / 8) with 0 in * by (clear - KZ NFB; lia).
      match goal with H : rw_cells _ _ (2147450880 + (AB + rz_size n) / 8) [CB _ ?j] |- _ =>
        pose proof H as [[[JL _] _] _]; cbn [cell_wf Z.to_nat] in JL; destruct j; [| cbn in JL; discriminate];
        eapply (rw_cells_reshape asegs _ _ _ _ H); [cbn; tauto| reflexivity] end.
    - (* [comment removed for export] *)
      zstep. zstep. zstep. zstep.
      lazymatch goal with |- context [MS _ _ _ _ _ ?mc _] =>
        assert (PS1 : poison_statics mc)
          by (eapply (poison_statics_transport _ m mc PS MU2); intros A0 k0 Hk; cbn [disjoint_from]; clear - Hk AB0 RZSB; lia) end.
      clear MU2.
      lazymatch goal with |- context [MS _ _ _ _ _ ?mc _] =>
        assert (SH' : rw_cells asegs mc (2147450880 + (AB + rz_size n) / 8) [CB (Z.to_nat (nfix n / 8 * 8 / 8)) junk])
          by (rewrite Z.div_mul by lia; assumption) end.
      eapply evtA_mono.
      { eapply (poison_spec AL IMG ALWF CS CSOK ASB) with (W := []);
          [ | | | | | | | exact SH' | exact PS1 | eassumption | exact LOIMG | clear - SPL; lia | clear - SPH; lia | clear - SPA; lia | | apply munch_refl | apply wmono_refl | eassumption ].
        - change 8 with (2 * 4 + 0). clear - ABAL RZ16 DA16 DR16. rewrite Z.add_0_r.
          replace (AB + rz_size n) with ((AB / 16 * 2 + rz_size n / 16 * 2) * 8) by lia. apply Z_mod_mult.
        - apply Z_mod_mult.
        - clear - KZ DNF MNF NFB; lia.
        - clear; lia.
        - clear - RNG AB0 N2B NFB DNF MNF RZSB DA16 DR16 ABAL RZ16. lia.
        - right. rewrite Z.div_mul by lia. clear - NFB N2B RZSB DNF MNF; lia.
        - eapply (crange_sub CS AB (needed2 n)); [exact ACS| clear - RZSB; lia| clear - N2B DNF MNF; lia].
        - eapply (crange_sub CS lo (SP - lo)); [exact SCS| clear; lia| clear; lia]. }
      cbn beta. intros ms1 (y0 & y1 & y2 & z0 & z1 & z2 & z3 & z4 & z5 & z6 & z7 & y3 & y4 & y5 & y6 & m2 & -> & MU3 & WM3 & MI3 & SH3 & ST3).
      rewrite Z.div_mul in MU3, SH3 by lia.
      replace (ret_pc (Z_to_bv 64 0x47f4c)) with (Z_to_bv 64 0x47f4c) by (symmetry; apply ret_pc_even; [ clear; lia | reflexivity ]).
      unfold mid_post. do 16 eexists. exists m2. split; [reflexivity|].
      split. { eapply munch_trans. { eapply munch_weaken; [| exact MU]. unfold sub_fp; cbn [outside]. clear. intros x Hx. tauto. }
               eapply munch_weaken; [| exact MU3]. unfold sub_fp; cbn [outside]. clear - SPL. intros x Hx. decompose [and] Hx. repeat split; auto. }
      split; [eapply wmono_trans; [exact WM| exact WM3]|]. split; [exact MI3|].
      split. { eapply rw_cells_transport; [| exact MU3| exact WM3|].
               { match goal with H : rw_cells _ _ (AB + rz_size n + -16) _ |- _ => exact H end. }
               cbn [disjoint_from cells_size csize Nat.add].
               clear - SPL LOIMG RNG AB0 RZSB NFB N2B DNF MNF KZ. repeat split; lia. }
      split; [exact SH3| exact ST3].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition pgv (n : Z) (pgb : byte) : byte := if nfix n mod 8 =? 0 then pgb else Z_to_bv 8 (nfix n mod 8).

  Definition pg_post (SP : Z) (gp tp x28 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
      (n AB STK T TID lo : Z) (W : list (Z * Z)) (pgb : byte) (m0 : mem) : machine_state -> Prop := ltac2:(CDefT.buildp (gd_tbl_AW_AllocB ()) "Lms',$17.(27.(0.&40.)Lx1,(0.&40.)(27.(0.&40.)Lx5,(0.&40.)(27.(0.&40.)Lx6,(0.&40.)(27.(0.&40.)Lx7,(0.&40.)(27.(0.&40.)Lx10,(0.&40.)(27.(0.&40.)Lx11,(0.&40.)(27.(0.&40.)Lx12,(0.&40.)(27.(0.&40.)Lx13,(0.&40.)(27.(0.&40.)Lx14,(0.&40.)(27.(0.&40.)Lx15,(0.&40.)(27.(0.&40.)Lx16,(0.&40.)(27.(0.&40.)Lx17,(0.&40.)(27.(0.&40.)Lx22,(0.&40.)(27.P,(0.&40.)(3.(0.&8.))Lm',P,(0.&40.)(3.(0.&8.))ZUB,$1.(9.O8.(2;.O9.))ZCHB,$1.(9.R1.-10.)Zrd,$1.(2>.(37.(28.O9.)+8.)+8.)ZPGS,$1.(9.+7???8000.(40.(9.R3.R1.)+3.))(18.(>.$17.R13.(19.(1:.R12.(1;.&40.(9.O12.-80.))O11.O10.R11.R10.R?.(1;.&40.+1.)(1;.&40.(28.O9.))R>.R=.R<.R;.R:.R9.R8.R7.(1;.&40.O8.)(1;.&40.(29.O9.))(1;.&40.R4.)(1;.&40.R3.)R6.(1;.&40.O7.)(1;.&40.(2>.O5.(=.+2.+20.)))(1;.&40.(9.R4.(28.O9.)))(1;.&40.O6.)(1;.&40.+1.)O?.O>.O=.O<.)O;.(1;.&40.+47?>0.)O:.(1=.(0.&40.))R5.(1>.$8.)))(18.(11.(12.(5.$1.$1.)(13.$1.$1.O4.(9.O12.-80.))(12.(5.$1.$1.)(13.$1.$1.R1.(9.R1.+1.))O3.))O1.R5.)(18.(14.$8.O1.R5.)(18.(15.$8.R5.)(18.(20.$8.R5.R1.(12.$22.(23.(43.O9.O2.))(24.$22.)))(7.$8.R5.O4.(9.O12.-80.)))))))))))))))))))))")
(* [comment removed for export] *).

  Local Ltac2 Set LiaOrc.tbl := fun () => "01c0?L11138871060.90L11145742652.82L12502279885.10L12604415106.80L13265630597.82L13275677884.82L13279090888.80L13313927314.82L13666404454.83L15395562245.82L17765151508.88L17930621016.82L19182823186.82L19586266388.80L20071043032.82L21798222111.80L22518122871.87L22577265597.87L23251451895.87L23928002224.87L2491586324.93 L27134647468.83L2843556961.87 L28921179156.83L29057133935.77L29265817255.87L29448992590.91L30299332372.87L31394778632.80L31563693970.82L31736297728.91L33494084254.4 L34150196914.85L34265358118.80L3507171090.82 L35250499860.86L36193165570.2 L36721662623.80L36888738214.80L3824716112.3  L39017728265.87L39188636933.0 L39425713901.87L39930025786.3 L39930703233.90L39932041151.81L40228640085.0 L41148359740.82L41400680896.87L41553783782.83L43278729349.82L43465718732.87L43855564994.80L43935888693.81L43938083252.2 L44222736994.92L44743351468.83L45410778629.82L46097988652.83L46230795540.84L47296240642.3 L47298995385.87L49698585326.93L49705053714.77L50966866708.91L51178147495.87L51240883336.80L52064999472.83L5299353416.80 L53516929332.83L53519718666.87L53520131109.80L53522110849.83L53522114239.82L54412534036.89L55007345708.83L55676403476.94L55866193017.87L5641312914.82 L57400919124.81L5811897951.80 L58371358466.83L58775187672.82L59308628433.12L59308628566.12L59308628695.13L59579460628.83L60500005819.83L60501295036.82L61024598737.79L61028779636.82L61030987373.80L63036727106.80L63368316589.83L63370229784.80L63374621462.81L64147162642.82L64775989122.83L64781239060.83L65164610392.82L65840083814.80L66606509224.8 L66715365384.80L66904651835.83L67259945748.92L67805785736.80L68364611860.85L7258948116.82 L7781730322.82 L8926825899.90 L8929152288.86 L8929152550.88 L8929152679.87 L8929161758.85 L9911535506.82 00000100200Q00`00a00b00i01P01b01c01d02602]02^03003103D03S03Z03[03\03f04;04H04]04d05105205905`05m06306@06A06K06L06O06P06Q06[06\06]06l07607N07f07g07h07i08;08<08W08f09S09Z09j0:Q0:R0;90;:0;;0;a0<70<G0<H0<[0<b0<c0=60=C0=S0=c0>60>I0>J0>T0>U0>V0>`0>a0>b0>c0?50?B0?g0@O0@\0@]0@^0@k0AF0Aa0B00BK0BX0C30CZ0C[0C\0Cn0Co0DA0DT0DU0DV0Di0Dj0Dk0E50E60E70E80E90E:0EDFFS3hAR1n2AB3AB03RNG4RZSB3NFB3N2BS3hAR2AL1n4IMG'FFS3hAR1nS3hAR2AL1n2AB3AB04IMG'4RZSB3NFB3DNF3MNFS3hAR2AL1n2AB4IMG'FFS3hAR2AL1n2AB4IMG'S3hAR2AL1n2AB3AB04IMG'4RZSB3NFB3DNF3MNFFS3hAR2AL1n2AB4IMG'FS3hAR2AL1n4IMG'3NFBS3hAR2AL1n4IMG'S3hAR1nFFS3hAR1n2ABS3hAR1n2AB3NFB3N2B2KES3hAR2SP1n2ABS3hAR2SP1n2AB2lo1W2HBS3hAR1nS3hAR2SP1n2ABFS3hAR1nS3hAR2AL1n2AB3AB04IMG'4RZSB3NFB3DNF3MNFS3hAR2SP1n2ABS1n2KES3hAR2SP1n2ABFS3hAR1n2ABFS1nFFS1n3DNF2KEFSS3hAR2AL1n4IMG'S1n2NB3NFBS3hAR2SP1n2AB2NB3AB03NFBS3hAR2SP1n2AB2NB3AB03NFBSFFS3hAR2AL1n2AB4IMG'FS3hAR1n2AB4RZSB3NFB3DNF3MNFS3hAR2AL1n4IMG'S3hAR2SP1n2AB2lo2NB3AB05LOIMG3SPL3NFB3DNF3MNFS1n3MNFS3hAR2SP1n2AB2HBS3hAR2AL1n2AB3AB04IMG'4RZSB3NFB3DNF3MNFFS3hAR2AL1n2AB3AB04IMG'4RZSB3NFB3DNF3MNFFFS3hAR2AL3ASB1n2AB3AB04RZSB3NFB3DNF3MNFS3hAR2SP1n2AB2HB5Ha_stS3hAR2SP1n2AB2HBFS3hAR2AL1n4IMG'3NFBS3hAR1nFS3hAR2AL1n4IMG'3NFBS3hAR2SP1n2ABS3hAR2AL1n5ALWF'S3hAR2AL1n5ALWF'S3hAR2AL1n2AB5ALWF'S3hAR2AL1n2AB5ALWF'FS3hAR1n2ABFFS3hAR1n2ABFFFS3hAR2AL1n2AB4IMG'S1n2AB3NFB2K2S3hAR1n2AB3AB03RNG4RZSB3NFB3N2B2KE2K3S3hAR1n2AB3AB03RNG4RZSB3NFB3N2B2KE2KL2K4S3hAR2SP1n2ABFFS3hAR2SP1n2ABS3hAR2SP1n2AB2UB3CHB2rd3PGSS3hAR2SP1n2AB2UB3CHB2rd3PGSS3hAR2AL1n4IMG'S3hAR2SP1n2AB2UB3CHB2rd3PGSS3hAR2SP1n2ABS3hAR2SP1n2AB2UB3CHB2rd3PGSS3hAR2AL1n2AB3AB04IMG'4RZSB3NFB3DNF3MNFFFS3hAR2AL1n2AB4IMG'FS1n3FP'1H2H02H12H2S3hAR2AL1n4IMG'3NFBFFS3hAR2AL1n4IMG'3NFBFFS3hAR1n2ABFFFFFS3hAR1n2AB". (* [comment removed for export] *)
  #[using="IMG ALWF CSOK ASB"] Lemma alloc_pg : ltac2:(CDefT.buildp (gd_tbl_AW_AllocB ()) "Pgp,(0.&40.)Ptp,(0.&40.)Px1,(0.&40.)Px5,(0.&40.)Px6,(0.&40.)Px7,(0.&40.)Px10,(0.&40.)Px11,(0.&40.)Px12,(0.&40.)Px13,(0.&40.)Px14,(0.&40.)Px15,(0.&40.)Px16,(0.&40.)Px17,(0.&40.)Px28,(0.&40.)Pt4,(0.&40.)Pt5,(0.&40.)Pt6,(0.&40.)Ppgb,(0.&8.)PSP,$1.Pn,$1.PAB,$1.PSTK,$1.PT,$1.PTID,$1.Plo,$1.PF,(2.&5.(0.&40.))Pfc,(0.&20.)Pm0,P,(0.&40.)(3.(0.&8.))Pm,P,(0.&40.)(3.(0.&8.))PW,(4.(5.$1.$1.))ZUB,$1.(9.R:.(2;.R;.))ZCHB,$1.(9.R1.-10.)Zrd,$1.(2>.(37.(28.R=.)+8.)+8.)ZPGS,$1.(9.+7???8000.(40.(9.R3.R1.)+3.))P,(18.(:.=R?.)(34.R?.(=.+2.+20.)))P,(>.$3<.(2=.R10.)$3=.)P,(:.+65?000.R10.)P,(>.$1.(?.R11.+10.)=)P,(35.(:.(9.R12.(29.R13.))+7???8000.)(18.(:.+10007???8000.R12.)(:.(9.R12.(29.R13.))(;.VhAR,))))P,(10.VCS,R13.(29.R14.))P,(20.$8.R<.R7.(12.$22.(23.R17.)(24.$22.)))P,(41.R=.)P,(25.$8.R>.$44.(12.$22.(32.(1;.&40.$45.))(24.$22.)))P,(25.$8.R?.$46.(12.$22.(23.(1;.&8.+1.))(24.$22.)))P,(7.$8.R10.R14.(9.R1:.-80.))P,(:.(;.VhAR,)R15.)P,(:.R16.(<.R1<.+200.))P,(:.R1=.(=.+2.+3>.))P,(>.$1.(?.R1>.+10.)=)P,(10.VCS,R19.(<.R1?.R19.))P,(11.(12.(5.$1.$1.)(13.$1.$1.R1:.(9.R20.-80.))(12.(5.$1.$1.)(13.$1.$1.R11.(9.R11.+1.))R15.))R17.R16.)P,(14.$8.R18.R17.)P,(15.$8.R18.)(16.$8.VAL,VCS,(47.R23.R36.R35.R28.R27.R26.R25.R1<.R1;.R22.R21.R20.R1?.R1>.R1=.R18.R24.R1:.)(19.(1:.R34.(1;.&40.(9.R23.-80.))R36.R35.R33.R32.R31.(1;.&40.+1.)(1;.&40.(28.R22.))R30.R2?.R2>.R2=.R2<.R2;.R2:.R29.(1;.&40.R21.)(1;.&40.(29.R22.))(1;.&40.R17.)(1;.&40.R16.)(1;.&40.R15.)(1;.&40.R20.)(1;.&40.(2>.R1>.(=.+2.+20.)))(1;.&40.(9.R17.(28.R22.)))(1;.&40.R1?.)(1;.&40.+1.)R28.R27.R26.R25.)R1<.(1;.&40.+47?4<.)R1;.(1=.(0.&40.))R19.(1>.$8.)))")
(* [comment removed for export] *).
  Proof.
    intros gp tp x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 t4 t5 t6 pgb SP n AB STK T TID lo F fc m0 m W UB CHB rd PGS
      NB FP AB0 ABAL RNG ACS PGC PS GOTFL PPART ST LOIMG SPL SPH SPA SCS MU WM MI.
    facts. pose proof PS as (CP & G1 & SB & G2 & MB & G3 & ME & G4 & HE & G5 & RM & G6 & CT).
    unfold A_CANPOISON, A_GOT_SB, A_SBCELL, A_GOT_MIDBEG, A_MIDBEG, A_GOT_MIDEND, A_MIDEND, A_GOT_HIGHEND, A_HIGHEND,
      A_GOT_RMEMSET, A_RMEMSET, A_GOT_CFLAGS, A_CFLAGS, A_CF_CSMT, A_MUSL_MEMSET, A_GOT_FLAGS, A_FLAGS, A_FL_PPART in *.
    pose proof (rz_size_bound n) as RZSB.
    assert (NFB : 1 <= nfix n <= Z.max n 1) by (unfold nfix; clear - NB; lia).
    assert (N2B : nfix n + rz_size n <= needed2 n /\ needed2 n <= 65536 /\ (nfix n / 8 * 8 + 8 <= needed2 n - rz_size n \/ nfix n mod 8 = 0)).
    { pose proof FP as FP'. unfold from_primary, kMaxSize in FP'. apply Z.leb_le in FP'.
      unfold needed2. rewrite FP. unfold needed, rounded, round_up in *.
      pose proof (Z.div_mod (Z.max n 8 + 8 - 1) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (Z.max n 8 + 8 - 1) 8 ltac:(lia)).
      pose proof (Z.div_mod (nfix n) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (nfix n) 8 ltac:(lia)).
      unfold nfix in *; clear - H H0 H1 H2 NB RZSB FP'. lia. }
    assert (HUB : UB = AB + rz_size n) by reflexivity. assert (HRD : rd = nfix n / 8 * 8) by reflexivity.
    assert (HPGS : PGS = 0x7fff8000 + Z.shiftr (UB + rd) 3) by reflexivity. subst CHB PGS. subst UB rd.
    pose proof (Z.div_mod (nfix n) 8 ltac:(lia)) as DNF. pose proof (Z.mod_pos_bound (nfix n) 8 ltac:(lia)) as MNF.
    Ltac pg_leaf :=
      apply evtA_done; unfold pg_post; do 13 eexists; eexists; split; [reflexivity|];
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
        evtA asegs AL CS (pg_post SP gp tp x28 t4 t5 t6 F fc n AB STK T TID lo W pgb m0)
          (MS (mkR (Z_to_bv 64 0x47f54) (Z_to_bv 64 (SP + -128)) gp tp x5 x6 x7 (Z_to_bv 64 1) (Z_to_bv 64 (nfix n))
                   (Z_to_bv 64 0x7fff8000) y11 y12 y13 y14 y15 y16 y17
                   (Z_to_bv 64 AB) (Z_to_bv 64 (needed2 n)) (Z_to_bv 64 (AB + rz_size n)) (Z_to_bv 64 (AB + rz_size n + -16))
                   (Z_to_bv 64 (AB + rz_size n + nfix n / 8 * 8)) (Z_to_bv 64 STK)
                   (Z_to_bv 64 (TID * 2^32)) (Z_to_bv 64 (AB + rz_size n + nfix n)) (Z_to_bv 64 T) (Z_to_bv 64 1) x28 t4 t5 t6)
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

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00b0?L14946089560.80L15253791194.73L15254151642.72L15258154528.73L15258154528.74L22351964942.75L2537942390.77 L25875266104.69L26878554278.69L26882680664.70L27006251846.78L27468508909.80L28920986476.66L28921216760.80L29921300973.72L32457808536.76L34539781148.72L34540010524.73L34543774694.73L34543774694.74L34894458726.77L39659073912.80L40823377450.76L40823377515.54L40823606892.52L41417918856.70L41417918925.49L41418148300.51L44017203752.63L44017433129.61L44566935372.80L51266838984.80L52515836280.80L53516901336.80L5742541873.48 L5742901752.80 L5749041963.46 L59579268856.79L59579498232.80L63370226858.57L63370521771.55L64350097516.67L65499898154.58L65500127529.60L6751737895.46 L6753455968.67 L6753619773.48 L6758013062.70 L67644715620.79L8929201440.76 00000100900A00I00Q00Z00[00\00d00l01L01U01V01Z01j02202302402502602702;02<02=02>02?02@02A02B02C02D02K02O02S02Y02b02h02l03003103203303403503603703803903=03LFS2ev3RevS2ev3RevS2ev3RevS2ev3RevS2ev1H2H0SSS2en3RenS2en3RenS2ev2er3Der3Rer4Rer'2et3Det1H2H0S1x2Hx2etSS2etS2en3Ren1H2H02H1S2er3RerSSSSFS2etSSSSSSSSFS2et2lzS2etS2etS1x2HxS1x2Hx2etS1x2HxS2etS2etSSSSSSSSSS2etS2ev1H2H02H12H2". (* [comment removed for export] *)
  #[using="IMG ALWF CSOK"] Lemma stats_cls_big : ltac2:(CDefT.buildp (gd_tbl_AW_AllocB ()) "Pra,(0.&40.)Psp,(0.&40.)Pgp,(0.&40.)Ptp,(0.&40.)Pt0,(0.&40.)Pt1,(0.&40.)Pt2,(0.&40.)Ps0,(0.&40.)Ps1,(0.&40.)Pa0,(0.&40.)Pa1,(0.&40.)Pa2,(0.&40.)Pa3,(0.&40.)Pa4,(0.&40.)Pa5,(0.&40.)Pa6,(0.&40.)Pa7,(0.&40.)Ps2,(0.&40.)Ps4,(0.&40.)Ps5,(0.&40.)Ps6,(0.&40.)Ps7,(0.&40.)Ps8,(0.&40.)Ps9,(0.&40.)Ps10,(0.&40.)Ps11,(0.&40.)Pt3,(0.&40.)Pt4,(0.&40.)Pt5,(0.&40.)Pt6,(0.&40.)PF,(2.&5.(0.&40.))Pfc,(0.&20.)Pm,P,(0.&40.)(3.(0.&8.))Px,$1.P,(18.(34.+200.R1.)(:.R1.+10000.))P,(15.$8.R3.)(16.$8.VAL,VCS,Lms',$17.(27.(0.&40.)Lx12,(0.&40.)(27.(0.&40.)Lx13,(0.&40.)(27.(0.&40.)Lx14,(0.&40.)(27.(0.&40.)Lx15,(0.&40.)(27.(0.&40.)Lx16,(0.&40.)(>.$17.R6.(19.(1:.R2:.R29.R28.R27.R26.R25.R24.R23.R22.R21.(1;.&40.(48.R9.))R5.R4.R3.R2.R1.R1:.R19.(1;.&40.R9.)R18.R17.R16.R15.R14.R13.R12.R11.R10.R?.R>.R=.)R<.(1;.&40.+48124.)R;.(1=.(0.&40.))R:.(1>.$8.))))))))(19.(1:.R24.R23.R22.R21.R20.R1?.R1>.R1=.R1<.R1;.R1:.R19.R18.R17.R16.R15.R14.R13.(1;.&40.R3.)R12.R11.R10.R?.R>.R=.R<.R;.R:.R9.R8.R7.)R6.(1;.&40.+48048.)R5.(1=.(0.&40.))R4.(1>.$8.)))")
(* [comment removed for export] *).
  Proof.
    try lx_hide ASB.  (* [comment removed for export] *)
    intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m x Hx MI. facts.
    zstep. zstep. zstep. zstep. zstep. zstep. abb_lor e1.
    zstep. zstep. zstep. zstep. zstep. zstep. abb_lor e2.
    do 8 zstep. zstep. zstep. abb_lor e3.
    zstep. zstep. abb_lor e4.
    zstep. zstep. abb_lor e5.
    zstep. zstep. abb_lor e6.
    zstep.
    abbrev (Z.lxor e6 18446744073709551615) en.
    zstep. zstep. zstep.
    abbrev_by (en - Z.land (en ≫ 1) 6148914691236517205) ev
      ltac:(pose proof (Z_land_le_l (en ≫ 1) 6148914691236517205 ltac:(apply Z.shiftr_nonneg; lia) ltac:(lia));
            pose proof (Z_shiftr_le en 1 ltac:(lia) ltac:(lia));
            pose proof (Z.land_nonneg (en ≫ 1) 6148914691236517205); lia).
    zstep. zstep. zstep. zstep.
    abbrev_by (Z.land ev 3689348814741910323 + Z.land (ev ≫ 2) 3689348814741910323) er
      ltac:(pose proof (Z_land_le_r ev 3689348814741910323 ltac:(lia) ltac:(lia));
            pose proof (Z_land_le_r (ev ≫ 2) 3689348814741910323 ltac:(apply Z.shiftr_nonneg; lia) ltac:(lia));
            pose proof (Z.land_nonneg ev 3689348814741910323);
            pose proof (Z.land_nonneg (ev ≫ 2) 3689348814741910323); lia).
    assert (Rer' : er <= 2 * 3689348814741910323).
    { rewrite Der. pose proof (Z_land_le_r ev 3689348814741910323 ltac:(lia) ltac:(lia)).
      pose proof (Z_land_le_r (ev ≫ 2) 3689348814741910323 ltac:(apply Z.shiftr_nonneg; lia) ltac:(lia)). lia. }
    zstep. zstep.
    abbrev_by (er + er ≫ 4) et ltac:(pose proof (Z_shiftr_le er 4 ltac:(lia) ltac:(lia)); pose proof (Z.shiftr_nonneg er 4); lia).
    zstep. zstep. zstep. zstep. zstep.
    lazymatch goal with |- context [Z_to_bv 64 (?v ≫ 56)] => abbrev (Z.shiftr v 56) lz end.
    zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep.
    apply evtA_done. do 5 eexists.
    match goal with |- context [Z_to_bv 64 (?v + -2)] => replace (v + -2) with (class_of x); [reflexivity|] end.
    rewrite <- (classid_code_ok x) by lia. unfold classid_code.
    subst lz et er ev en e6 e5 e4 e3 e2 e1. reflexivity.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Definition st_post (SP : Z) (gp tp x28 t4 t5 t6 x22 : word) (F : bvmap 5 word) (fc : bv 32)
      (n AB STK T TID lo : Z) (W : list (Z * Z)) (m0 : mem) : machine_state -> Prop := ltac2:(CDefT.buildp (gd_tbl_AW_AllocB ()) "Lms',$17.(27.(0.&40.)Lx1,(0.&40.)(27.(0.&40.)Lx5,(0.&40.)(27.(0.&40.)Lx6,(0.&40.)(27.(0.&40.)Lx7,(0.&40.)(27.(0.&40.)Lx10,(0.&40.)(27.(0.&40.)Lx11,(0.&40.)(27.(0.&40.)Lx12,(0.&40.)(27.(0.&40.)Lx13,(0.&40.)(27.(0.&40.)Lx14,(0.&40.)(27.(0.&40.)Lx15,(0.&40.)(27.(0.&40.)Lx16,(0.&40.)(27.(0.&40.)Lx17,(0.&40.)(27.(0.&40.)Lj0,(0.&40.)(27.(0.&40.)Lj1,(0.&40.)(27.(0.&40.)Lj2,(0.&40.)(27.(4.(0.&40.))Lbs,(4.(0.&40.))(27.P,(0.&40.)(3.(0.&8.))Lm',P,(0.&40.)(3.(0.&8.))ZUB,$1.(9.O7.(2;.O8.))ZCHB,$1.(9.R1.-10.)(18.(>.$17.R14.(19.(1:.R13.(1;.&40.(9.O12.-80.))O11.O10.R12.R11.R10.(1;.&40.+1.)(1;.&40.(28.O8.))R?.R>.R=.R<.R;.R:.R9.R8.(1;.&40.O7.)(1;.&40.(29.O8.))(1;.&40.R2.)(1;.&40.R1.)O;.(1;.&40.O6.)(1;.&40.(2>.O4.(=.+2.+20.)))(1;.&40.(9.R2.(28.O8.)))(1;.&40.O5.)(1;.&40.+1.)O?.O>.O=.O<.)O:.(1;.&40.+48138.)O9.(1=.(0.&40.))R3.(1>.$8.)))(18.(11.(12.(5.$1.$1.)(13.$1.$1.O3.(9.O12.-80.))(12.(5.$1.$1.)(13.$1.$1.(9.O5.+:?0.)(9.O5.+<60.))O2.))O1.R3.)(18.(14.$8.O1.R3.)(18.(15.$8.R3.)(18.(20.$8.R3.(9.O5.+:?0.)(12.$22.(32.R7.)(12.$22.(32.R6.)(12.$22.(32.R5.)(24.$22.)))))(18.(49.$8.R3.(9.O5.+;60.)R4.)(18.(>.$4:.(4;.(0.&40.)R4.)#20.)(7.$8.R3.O3.(9.O12.-80.))))))))))))))))))))))))))")
(* [comment removed for export] *).

  Local Ltac2 Set LiaOrc.tbl := fun () => "00]0@L11261181176.101L11359100080.6  L15020562828.1  L16073379411.96 L21783816758.99 L21914493336.33 L22744504146.64 L23035205884.1  L27697007571.4  L29044811861.100L30129840862.1  L3091479790.1   L31202476619.100L31202476619.101L34340530477.1  L36193165570.2  L38335416942.1  L38797873596.2  L39188636933.0  L39284637285.0  L40172550548.2  L40337477085.103L40605467906.98 L40607551371.98 L43907602222.2  L44421293205.1  L44625906644.1  L46692551656.2  L48959321276.2  L49698585326.102L49700596520.100L51008972509.103L51609867272.64 L53525265815.64 L54509413076.1  L605727586.64   L6098833402.2   L61030987373.83 L63374621462.84 L65561650839.64 L66613687486.2  L67827763708.101L68141448525.1  L7419756466.98  L7421834555.98  00000B00N00R00e01702a03903<03L04304404504e05U05X05[05_05`05a05b05h05i06;06M06S06W06[06\06]07B07g08K08b09909=09k0:10:K0:e0;<0;B0;T0;W0;i0<;S3hAR2bs2SP1n1T2HLS1n3FP'1H2H0S2SPS3hAR2bs2SP1n2HL2CRS3hAR2bs2SP1n1T2HLS2AL2CS2gp2x52x62x73x173x223x282t42t52t62bs2SP1n2AB3STK1T3TID2lo1F2fc2m01W2HL2CR3y123y133y143y153y162mc2HNS3hAR2bs2SP1n2HL3N2B3H18S1nS1n4RZSB3NFB3N2BS3hAR2bs2SP1n1T2lo1W2T12HL5LOIMG3SPL2CRFFS3hAR2bs2SP1n1T3CTX2lo2C02T02HL5LOIMG3SPL3SPA2CRS3hAR2bs2SP1n1T3CTX2lo2C02T02HL5LOIMG3SPL3SPA2CRS1TS1nS2SPFSSS1n2CRFS3hAR2bs1n1T2HL2CRS3hAR2bs1n1T2HL2CRS1n2ABS2SPS2SPFFS3hAR2bs2SP1n1T2lo2T12HL5LOIMG3SPL2CRS3hAR2bs2SP1n1T2lo2T12HL5LOIMG3SPL2CRS3hAR2bs2SP1n1T2lo2HL5LOIMG3SPL2CR1wS3hAR2bs2SP1n2lo2HL3SPLS3hAR2bs2SP1n2lo2HL3SPLS2SPS3hAR2bs2SP1n2lo2HL5LOIMG3SPL4RZSB3NFB3N2B3H18S1n2ABS3hAR2bs2SP1n2AB2UB3CHB2HLS3hAR2bs2SP1n2AB2UB3CHB2HLS3hAR2bs2SP1n2lo2HL3SPLS1n2CRS3hAR2bs2SP1n1T2HLS1TS3hAR2bs1n1T2HL2CRS3hAR2bs1n1T2HL2CR". (* [comment removed for export] *)
  #[using="IMG ALWF CSOK"] Lemma alloc_st : ltac2:(CDefT.buildp (gd_tbl_AW_AllocB ()) "Pgp,(0.&40.)Ptp,(0.&40.)Px1,(0.&40.)Px5,(0.&40.)Px6,(0.&40.)Px7,(0.&40.)Px10,(0.&40.)Px11,(0.&40.)Px12,(0.&40.)Px13,(0.&40.)Px14,(0.&40.)Px15,(0.&40.)Px16,(0.&40.)Px17,(0.&40.)Px22,(0.&40.)Px28,(0.&40.)Pt4,(0.&40.)Pt5,(0.&40.)Pt6,(0.&40.)Pj0,(0.&40.)Pj1,(0.&40.)Pj2,(0.&40.)Pbs,(4.(0.&40.))PSP,$1.Pn,$1.PAB,$1.PSTK,$1.PT,$1.PCTX,$1.PTID,$1.Plo,$1.PF,(2.&5.(0.&40.))Pfc,(0.&20.)Pm0,P,(0.&40.)(3.(0.&8.))Pm,P,(0.&40.)(3.(0.&8.))PW,(4.(5.$1.$1.))ZUB,$1.(9.R;.(2;.R<.))ZCHB,$1.(9.R1.-10.)P,(18.(:.=R>.)(34.R>.(=.+2.+20.)))P,(>.$3<.(2=.R?.)$3=.)P,(4<.R6.R=.R<.)P,(:.+65?000.R=.)P,(:.(9.R>.+10000.)(;.VhAR,))P,(18.(:.+1000.R10.)(35.(:.(9.R10.+1000.)+10000.)(:.+65?000.R10.)))P,(:.(9.R11.+1000.)(;.VhAR,))P,(10.VCS,R11.+10000.)P,(10.VCS,R13.+1000.)P,(35.(:.(9.R14.+1000.)R13.)(:.(9.R13.+10000.)R14.))P,(20.$8.R>.(9.R15.+:?0.)(12.$22.(32.R1=.)(12.$22.(32.R1<.)(12.$22.(32.R1;.)(24.$22.)))))P,(49.$8.R?.(9.R16.+;60.)R1;.)P,(>.$4:.(4;.(0.&40.)R1<.)#20.)P,(7.$8.R11.R15.(9.R1<.-80.))P,(:.(;.VhAR,)R16.)P,(:.R17.(<.R1>.+200.))P,(:.R1?.(=.+2.+3>.))P,(>.$1.(?.R20.+10.)=)P,(10.VCS,R1:.(<.R21.R1:.))P,(11.(12.(5.$1.$1.)(13.$1.$1.R1;.(9.R22.-80.))(12.(5.$1.$1.)(13.$1.$1.(9.R1>.+:?0.)(9.R1>.+<60.))R16.))R18.R17.)P,(14.$8.R19.R18.)P,(15.$8.R19.)P,(>.(0.&40.)R3;.(1;.&40.$4=.))(16.$8.VAL,VCS,(4>.R26.R3=.R3<.R2>.R2=.R2<.R2;.R2?.R1>.R1=.R25.R24.R23.R22.R20.R1?.R1:.R1<.)(19.(1:.R3;.(1;.&40.(9.R26.-80.))R3=.R3<.R3:.R39.R38.(1;.&40.+1.)(1;.&40.(28.R25.))R37.R36.R35.R34.R33.R32.R31.R30.(1;.&40.R24.)(1;.&40.(29.R25.))(1;.&40.R19.)(1;.&40.R18.)R2?.(1;.&40.R23.)(1;.&40.(2>.R20.(=.+2.+20.)))(1;.&40.(9.R19.(28.R25.)))(1;.&40.R22.)(1;.&40.+1.)R2>.R2=.R2<.R2;.)R1>.(1;.&40.+47?>0.)R1=.(1=.(0.&40.))R1;.(1>.$8.)))")
(* [comment removed for export] *).
  Proof.
    try lx_hide ASB.  (* [comment removed for export] *)
    intros gp tp x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x22 x28 t4 t5 t6 j0 j1 j2 bs SP n AB STK T CTX TID lo F fc m0 m W UB CHB
      NB FP (INI & RSS & DBR & LT1 & LT2a & LT2b & RZC & MXU & TSD & TPC & TSA & CTH) C0 C1 T0 T1 CTXCS TCS TCSEP STH STB HL
      ST LOIMG SPL SPH SPA SCS MU WM MI ->.
    facts. unfold A_ASAN_INITED, A_RSS_CELL, A_DEBRUIJN, A_LOGTBL1, A_LOGTBL2, A_MINRZ, A_MAXUSER, A_INSTANCE,
      A_TSD_INITED, A_TSD_PTR, A_TSD_ARR, A_TP in *.
    pose proof (rz_size_bound n) as RZSB.
    assert (NFB : 1 <= nfix n <= Z.max n 1) by (unfold nfix; clear - NB; lia).
    assert (N2B : nfix n + rz_size n <= needed2 n /\ needed2 n <= 65536).
    { pose proof FP as FP'. unfold from_primary, kMaxSize in FP'. apply Z.leb_le in FP'.
      unfold needed2. rewrite FP. unfold needed, rounded, round_up in *.
      pose proof (Z.div_mod (Z.max n 8 + 8 - 1) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (Z.max n 8 + 8 - 1) 8 ltac:(lia)).
      unfold nfix; clear - H H0 NB RZSB FP'; lia. }
    pose proof (class_of_range (needed2 n) ltac:(clear - N2B NFB RZSB; lia)) as CR.
    subst CHB UB.
    change (1074072 + 3624) with 1077696 in RZC. change (1074072 + 3616) with 1077688 in MXU.
    assert (TAILST : forall (y12 y13 y14 y15 y16 z1 z2 z3 : word) (mc : mem),
      rw_cells asegs mc (T + 2800) [C8 z1; C8 z2; C8 z3] -> u64arr asegs mc (T + 2912) bs -> stk asegs mc lo (SP + -128) ->
      munch ((lo, SP + -128) :: (T + 2800, T + 3168) :: W) m0 mc -> wmono asegs m0 mc -> mem_inv asegs mc ->
      evtA asegs AL CS (st_post SP gp (Z_to_bv 64 A_TP) x28 t4 t5 t6 x22 F fc n AB STK T TID lo W m0)
        (MS (mkR (Z_to_bv 64 0x47fe4) (Z_to_bv 64 (SP + -128)) gp (Z_to_bv 64 A_TP) x5 x6 x7 (Z_to_bv 64 1) (Z_to_bv 64 (nfix n))
                 (Z_to_bv 64 (T + 2912)) (Z_to_bv 64 (class_of (needed2 n))) y12 y13 y14 y15 y16 x17
                 (Z_to_bv 64 AB) (Z_to_bv 64 (needed2 n)) (Z_to_bv 64 (AB + rz_size n)) (Z_to_bv 64 (AB + rz_size n + -16)) x22 (Z_to_bv 64 STK)
                 (Z_to_bv 64 (TID * 2^32)) (Z_to_bv 64 (AB + rz_size n + nfix n)) (Z_to_bv 64 T) (Z_to_bv 64 1) x28 t4 t5 t6)
             F (Z_to_bv 64 0x48124) fc None mc (seg_rom asegs))).
    { intros y12 y13 y14 y15 y16 z1 z2 z3 mc STH' STB' ST' MU' WM' MI'. unfold A_TP.
      (* [comment removed for export] *)
      zstep. rewrite Z.shiftl_mul_pow2 by (clear; lia). change (2^3) with 8. zstep.
      destruct (nth_error bs (Z.to_nat (class_of (needed2 n)))) as [w|] eqn:HN; [| apply nth_error_None in HN; clear - HN HL CR; lia].
      pose proof (u64arr_read asegs mc (T + 2912) bs (class_of (needed2 n)) w (wa (T + 2912 + class_of (needed2 n) * 8)) STB' HN ltac:(clear - CR; lia) ltac:(f_equal; lia)) as RD.
      zstep. clear RD. zstep.
      pose proof (u64arr_store_ok asegs _ (T + 2912) bs (class_of (needed2 n)) _ STB' ltac:(rewrite HL; clear - CR; lia) ltac:(f_equal; lia)) as SOK.
      zstep.
      lazymatch goal with |- _ (MS _ _ _ _ _ (write_to_mem ?mx ?a (le8 ?v)) _) =>
        pose proof (u64arr_write asegs mx (T + 2912) bs (class_of (needed2 n)) v STB' ltac:(rewrite HL; clear - CR; lia)) as STB2;
        let E := addr_expr a in replace (T + 2912 + 8 * class_of (needed2 n))%Z with E in STB2 by lia
      end.
      store_done.
      apply evtA_done. unfold st_post. do 12 eexists. do 3 eexists. exists (upd bs (Z.to_nat (class_of (needed2 n))) (Z_to_bv 64 (bv_unsigned w + 1))). eexists.
      split; [reflexivity|]. split; [eassumption|]. split; [eassumption|]. split; [eassumption|].
      split; [eassumption|]. split; [exact STB2|]. split; [rewrite upd_length; exact HL| assumption]. }
    (* [comment removed for export] *)
    destruct STB as [STBb STBw].
    assert (LU : Z.of_nat (length (u64s bs)) = 256) by (rewrite u64s_length, HL; reflexivity).
    lx_hide MU. lx_hide WM.
    pose proof (munch_refl [(lo, SP + -128); (T + 2800, T + 3168)] m) as MU1. pose proof (wmono_refl asegs m) as WM1.
    lx_aceil.
    lx_run (PLAN [0x48048; 0x48124] [] 80%N); lx_unhide; try clear LXlen; clear STBb; lx_stk_grow_to lo (SP + -128);
      lazymatch goal with MUl : munch _ m ?mx, WMl : wmono _ m ?mx', BYl : bytes_at _ ?mx'' (T + 2912) _ |- _ =>
        pose proof (conj BYl (wr_at_transport _ _ _ _ _ STBw WMl) : u64arr asegs mx (T + 2912) bs) as STB';
        assert (MU' : munch ((lo, SP + -128) :: (T + 2800, T + 3168) :: W) m0 mx) by (lx_munch MU MUl);
        assert (WM' : wmono asegs m0 mx) by (lx_wmono WM WMl);
        replace (T + 2047 + 753) with (T + 2800) in * by (clear; lia);
        try replace (AB + (rz_size n + -16)) with (AB + rz_size n + -16) by (clear; lia);
        try replace (nfix n + (AB + rz_size n)) with (AB + rz_size n + nfix n) by (clear; lia)
      end.
    - (* [comment removed for export] *)
      lazymatch goal with K : 0 <= needed2 n + _ |- _ => idtac | K : 0 <= _ + needed2 n |- _ => idtac end.
      eapply evtA_cut. { eapply stats_cls_big; [lx_arith| assumption]. }
      cbv beta. intros ms' (y12 & y13 & y14 & y15 & y16 & ->).
      replace (T + 2800 + 112) with (T + 2912) by (clear; lia).
      eapply TAILST; first [exact STB' | exact MU' | exact WM' | eassumption].
    - (* [comment removed for export] *)
      lazymatch goal with |- context [Z_to_bv 64 (Z.shiftr ?e 5)] =>
        rewrite (Z.shiftr_div_pow2 e 5) by (clear; lia); change (2^5) with 32;
        replace e with (needed2 n + 31) by (clear; lia) end.
      rewrite <- (class_of_small (needed2 n)) by lx_arith.
      replace (T + 2800 + 112) with (T + 2912) by (clear; lia).
      eapply TAILST; first [exact STB' | exact MU' | exact WM' | eassumption].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  Definition fin_statics (m : mem) : Prop := ltac2:(CDefT.buildp (gd_tbl_AW_AllocB ()) "(18.(25.$8.O1.$4?.(12.$22.(32.(1;.&40.+10.))(24.$22.)))(18.(25.$8.O1.$50.(12.$22.(31.(1;.&40.=))(24.$22.)))(18.(25.$8.O1.$51.(12.$22.(32.(1;.&40.$52.))(24.$22.)))(18.(25.$8.O1.$53.(12.$22.(32.(1;.&40.=))(24.$22.)))(18.(25.$8.O1.$44.(12.$22.(32.(1;.&40.$45.))(24.$22.)))(18.(25.$8.O1.$54.(12.$22.(31.(1;.&40.+1000.))(24.$22.)))(18.(25.$8.O1.$55.(12.$22.(31.(1;.&40.+;>.))(24.$22.)))(18.(25.$8.O1.$56.(12.$22.(32.(1;.&40.$57.))(24.$22.)))(25.$8.O1.$57.(12.$22.(32.(1;.&40.$58.))(24.$22.)))))))))))")
(* [comment removed for export] *).

  (* [comment removed for export] *)
  Definition fin_post (SP : Z) (gp tp : word) (F : bvmap 5 word) (fc : bv 32)
      (n AB TID id lo : Z) (b1 : Z) (mg0 mg1 qra q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 : word) (W : list (Z * Z)) (m0 : mem) : machine_state -> Prop := ltac2:(CDefT.buildp (gd_tbl_AW_AllocB ()) "Lms',$17.(27.(0.&40.)Lx5,(0.&40.)(27.(0.&40.)Lx6,(0.&40.)(27.(0.&40.)Lx7,(0.&40.)(27.(0.&40.)Lx11,(0.&40.)(27.(0.&40.)Lx12,(0.&40.)(27.(0.&40.)Lx13,(0.&40.)(27.(0.&40.)Lx14,(0.&40.)(27.(0.&40.)Lx15,(0.&40.)(27.(0.&40.)Lx16,(0.&40.)(27.(0.&40.)Lx17,(0.&40.)(27.(0.&40.)Lx28,(0.&40.)(27.(0.&40.)Lx29,(0.&40.)(27.(0.&40.)Lx30,(0.&40.)(27.(0.&40.)Lx31,(0.&40.)(27.P,(0.&40.)(3.(0.&8.))Lm',P,(0.&40.)(3.(0.&8.))ZUB,$1.(9.O16.(2;.O17.))ZCHB,$1.(9.R1.-10.)(18.(>.$17.R12.(19.(1:.O?.(1;.&40.O1<.)O1;.O1:.R11.R10.R?.O>.O=.(1;.&40.R2.)R>.R=.R<.R;.R:.R9.R8.O<.O;.O:.O9.O8.O7.O6.O5.O4.O3.R7.R6.R5.R4.)O19.(1<.O?.)O18.(1=.(0.&40.))R3.(1>.$8.)))(18.(11.(12.(5.$1.$1.)(13.$1.$1.O13.O1<.)(12.(5.$1.$1.)(13.$1.$1.R1.(9.R1.+2.))(12.(5.$1.$1.)(13.$1.$1.O16.(9.O16.+10.))O2.)))O1.R3.)(18.(14.$8.O1.R3.)(18.(15.$8.R3.)(18.(20.$8.R3.R1.(12.$22.(23.(1;.&8.$59.))(12.$22.(23.(1;.&8.(33.O12.+?3.)))(12.$22.(30.(1;.&40.=))(12.$22.(31.(1;.&40.(28.O17.)))(12.$22.(32.(1;.&40.(38.(2>.O15.(=.+2.+20.))O14.)))(24.$22.)))))))(18.P,(34.+10.(2;.O17.))(20.$8.R4.O16.(12.$22.(32.(1;.&40.$52.))(12.$22.(32.(1;.&40.R2.))(24.$22.))))(7.$8.R3.O13.O1<.))))))))))))))))))))))")
(* [comment removed for export] *).

  Local Ltac2 Set LiaOrc.tbl := fun () => "01X0@L10184747763.94 L10210849586.3  L11151000370.93 L11666481681.3  L11985143081.1  L13277838258.89 L13296972522.96 L13618020628.98 L1495112192.92  L15393414155.89 L15636460711.98 L18858039182.100L19129098672.96 L19160092211.98 L19180804124.89 L19586266388.98 L23426481611.78 L24886574194.91 L24989977372.89 L25805129492.98 L27705282402.5  L2868317467.94  L29270158734.100L30507141665.96 L31919852430.100L32537519809.100L32729246119.1  L32852261457.94 L34430750804.1  L3509211164.89  L35250499860.98 L3525608835.97  L3525611157.96  L35992898843.94 L36193165570.2  L36631107470.100L37396631557.0  L37964339962.1  L38465086153.100L38555397984.1  L38962019212.92 L39407456835.97 L39944775816.98 L41137568973.96 L41388092302.100L41671761036.98 L42031126465.96 L42650174943.98 L43907602222.2  L44975803890.79 L45914037331.96 L46180902676.98 L46444081826.99 L46935889045.1  L47500037067.78 L49382159157.3  L49698585326.97 L49705053714.96 L5039651420.5   L50766042396.89 L50966866708.98 L52137112076.94 L53516973216.92 L53520095665.89 L53522113078.94 L54082276882.3  L54780234875.92 L54780293584.89 L54780741077.92 L55474644110.100L55606901317.2  L56821025934.100L57056925710.94 L57936462681.3  L58127006740.98 L58301450569.92 L58301759719.92 L58301791564.89 L59308630630.6  L59308632432.4  L59310676309.3  L59696744469.93 L59696744469.96 L60299333669.2  L60395280782.100L61030858054.93 L61051158381.94 L61580800532.98 L62033406508.94 L62632109323.89 L63064043092.1  L63361644942.100L63374621462.94 L65166668886.89 L66532340722.96 L66732409525.94 L67259945748.98 L704957270.89   L7807593471.2   L8458413483.2   L9001182386.89  L9143127683.2   L959706227.98   L9728771280.92  00000:00;00H00I00M00N00^01W01d01e02202R02_03303G04@04T04h04o05h06006D06d07W08708V08Z08i08j09109j0:Y0;L0;S0;V0<60<70<;0=<0==0=T0>C0>W0>d0?D0@B0@W0AX0A^0BM0B]0CV0Cl0D00DD0DE0D[0Dk0E80EL0FE0FF0FS0Fc0G30G>0GM0G\0Gk0HK0HS0I30IM0IY0JR0Ji0K@0KW0Kn0L?0LJ0LW0Ld0Ll0ML0M`0N:0O30O=0O>0O?0O_0P30PB0PO0PP0QI0QX0QY0QZ0Q[0Qd0R10R@S3hAR1n2ABFS3hAR2SP1n2ABFS2SPFS3hAR2SP1n2AB2HBS3hAR2SP1n2AB2lo2b13AB05LOIMG3SPL4RZSB2HB5Ha_st5Hl_st3RZES3hAR2SP1n2ABFS3hAR2SP1n2ABS3hAR2SP1n2AB3AB02HB5Ha_st5Hl_stS3hAR2SP1n2ABS3hAR2SP1n2AB3AB02HBS3hAR2AL1n4IMG'4RZSBS3hAR2SP1n2AB2lo2b13AB05LOIMG3SPL4RZSB2HB5Ha_st5Hl_st3RZES3hAR2SP1n2AB2lo3SPLS3hAR2SP1n2AB2UB3CHBS3hAR1nS3hAR2SP1n2AB2lo2b13AB05LOIMG3SPL4RZSB2HB5Ha_st5Hl_st3RZES1n1H2H0S3hAR2AL1n4IMG'4RZSBS3hAR2SP1n2AB3AB02HB5Ha_st5Hl_stS3hAR2SP1n2AB2lo3AB03AB15LOIMG3SPL4RZSB3NFB3N2B3RZES3hAR2SP1n2AB3AB02HB5Ha_st5Hl_stS3hAR2SP1n2AB2KC2HB5Ha_st5Hl_stS2SPS3hAR2AL1n4IMG'FS3hAR1nS3hAR2SP1n2AB2lo2b13AB05LOIMG3SPL4RZSB2HB5Ha_st5Hl_st3RZES3hAR2SP1n2AB2lo3AB03AB15LOIMG3SPL4RZSB3NFB3N2BS3hAR2SP1n2AB2lo3AB03AB15LOIMG3SPL4RZSB3NFB3N2B3RZES3hAR1nS1nS3hAR2SP1n2AB3AB02HB5Ha_st5Hl_stSS2SPS3hAR2SP1n2AB2lo3AB03AB15LOIMG3SPL4RZSB3NFB3N2B2KC2HB5Ha_st5Hl_stFS3hAR1n2AB4RZSB3NFB3N2BS3hAR2SP1n2AB2lo3AB03AB15LOIMG3SPL4RZSB3NFB3N2BS3hAR2SP1n2AB3AB02HBS3hAR2SP1n2ABS3hAR2SP1n2AB3AB02HB5Ha_st5Hl_stS3hAR2SP1n2AB2lo2b13AB05LOIMG3SPL4RZ164DR163RZL2HB5Ha_st5Hl_stS3hAR2SP1n2AB2lo1W2HBS3hAR2SP1n2AB2lo2b13AB03AB15LOIMG3SPL4RZSB3NFB3N2B2HB5Ha_st5Hl_stS1n2ABS3hAR2SP1n2AB2lo3AB03AB15LOIMG3SPL4RZSB3NFB3N2BS3hAR2SP1n2AB2HBS3hAR2SP1n2AB2lo2b13AB05LOIMG3SPL4RZSB2HB5Ha_st5Hl_st3RZES3hAR2SP1n2AB2HB5Ha_stS2SPS3hAR2SP1n2AB2lo3SPLFS3hAR2SP1n2AB2HB5Ha_stS3hAR2SP1n2AB2HBS1n4RZSB1H2H0S3hAR2AL1n4IMG'4RZSBS3hAR2SP1n2AB2lo2b13AB05LOIMG3SPL4RZSB2HB5Ha_st5Hl_st3RZEFS3hAR2SP1n2ABS3hAR2AL1n5ALWF'S3hAR2AL1n5ALWF'S2SP2lo3SPLS3hAR1n2AB4RZSBS3hAR1n2AB4RZSBS3hAR1n2AB4RZSBS3hAR2SP1n2AB3AB02HB5Ha_st5Hl_stS2b13B1BS3hAR2SP1n2AB3AB02HB5Ha_st5Hl_stS3hAR1n2AB4RZSB3NFB3N2B2KCS1n4RZSB3RZSS3hAR2SP1n2AB2lo2b13AB05LOIMG3SPL4RZSB2HB5Ha_st5Hl_st3RZES3hAR1n2AB4RZSB3NFB3N2BS3hAR1n2AB4RZSB3NFB3N2BS3hAR1n2AB4RZSB3NFB3N2BS1n2AB4RZ164DR163RZL2KCS1n2AB3RZL2KQ3RZES1n3RZE3H16S3hAR2SP1n2ABS3hAR2SP1n2ABS2SP3SPHS3hAR2SP1n2AB3AB02HB5Ha_st5Hl_stS3hAR2SP1n2AB2UB3CHBS3hAR1n2AB4RZSB3NFB3N2B2KCS3hAR2SP1n2AB2lo2b13AB05LOIMG3SPL4RZSB2HB5Ha_st5Hl_st3RZES3hAR1n2ABFFS3hAR2SP1n2AB3AB02HB5Ha_st5Hl_stS3hAR2SP1n2AB2UB3CHBS3hAR2AL1n4IMG'S3hAR2SP1n2ABFS3hAR2SP1n2AB2lo2b13AB05LOIMG3SPL4RZSB2HB5Ha_st5Hl_st3RZES3hAR2AL1n4IMG'FSFS2b14B1R'S3hAR2SP1n2ABS3hAR1n2AB4RZSB". (* [comment removed for export] *)
  #[using="IMG ALWF CSOK"] Lemma alloc_fin2 : ltac2:(CDefT.buildp (gd_tbl_AW_AllocB ()) "Pgp,(0.&40.)Ptp,(0.&40.)Px1,(0.&40.)Px5,(0.&40.)Px6,(0.&40.)Px7,(0.&40.)Px10,(0.&40.)Px11,(0.&40.)Px12,(0.&40.)Px13,(0.&40.)Px14,(0.&40.)Px15,(0.&40.)Px16,(0.&40.)Px17,(0.&40.)Px22,(0.&40.)Px28,(0.&40.)Pt4,(0.&40.)Pt5,(0.&40.)Pt6,(0.&40.)Pb0,(0.&8.)Pmg0,(0.&40.)Pmg1,(0.&40.)Pqra,(0.&40.)Pq0,(0.&40.)Pq1,(0.&40.)Pq2,(0.&40.)Pq3,(0.&40.)Pq4,(0.&40.)Pq5,(0.&40.)Pq6,(0.&40.)Pq7,(0.&40.)Pq8,(0.&40.)Pq9,(0.&40.)Pq10,(0.&40.)Pq11,(0.&40.)PSP,$1.Pn,$1.PAB,$1.PSTK,$1.PT,$1.PTID,$1.Pid,$1.Plo,$1.Pb1,$1.Pfill,$1.PF,(2.&5.(0.&40.))Pfc,(0.&20.)Pm0,P,(0.&40.)(3.(0.&8.))Pm,P,(0.&40.)(3.(0.&8.))Pfr0,(4.(0.&8.))PW,(4.(5.$1.$1.))ZUB,$1.(9.R>.(2;.R?.))ZCHB,$1.(9.R1.-10.)P,(18.(:.=R11.)(34.R11.(=.+2.+20.)))P,(:.+65?000.R11.)P,(>.$1.(?.R12.+10.)=)P,(:.(9.R13.(29.R14.))(;.VhAR,))P,(18.(:.=R>.)(34.R>.+100.))P,(10.VCS,R15.(29.R16.))P,(20.$8.R;.R7.(12.$22.(23.R28.)(12.$22.(23.(1;.&8.R10.))(12.$22.(30.(1;.&40.=))(12.$22.(31.(1;.&40.(28.R17.)))(12.$22.(32.(1;.&40.(38.(2>.R13.(=.+2.+20.))R12.)))(24.$22.)))))))P,P,(34.+10.(2;.R18.))(20.$8.R=.R18.(12.$22.(32.R29.)(12.$22.(32.R28.)(24.$22.))))P,(5:.R=.)P,(6.R>.R1;.R=.R12.R28.R27.R26.R25.R24.R23.R22.R21.R20.R1?.R1>.R1=.R1<.)P,(7.$8.R?.R15.(9.R1<.-80.))P,(:.(;.VhAR,)R16.)P,(:.R17.(<.R1>.+200.))P,(:.R1?.(=.+2.+3>.))P,(>.$1.(?.R20.+10.)=)P,(10.VCS,R1:.(<.R21.R1:.))P,(11.(12.(5.$1.$1.)(13.$1.$1.R1;.R22.)(12.(5.$1.$1.)(13.$1.$1.R11.(9.R11.+2.))(12.(5.$1.$1.)(13.$1.$1.R20.(9.R20.+10.))R13.)))R16.R15.)P,(14.$8.R17.R16.)P,(15.$8.R17.)P,(>.(0.&40.)R47.(1;.&40.$4=.))(16.$8.VAL,VCS,(5;.R26.R49.R48.R1<.R1;.R25.R24.R21.R20.R1?.R1>.R35.R34.R33.R32.R31.R30.R2?.R2>.R2=.R2<.R2;.R2:.R29.R28.R27.R17.R1:.)(19.(1:.R47.(1;.&40.(9.R26.-80.))R49.R48.R46.R45.R44.(1;.&40.+1.)(1;.&40.(28.R25.))R43.R42.R41.R40.R3?.R3>.R3=.R3<.(1;.&40.R24.)(1;.&40.(29.R25.))(1;.&40.R16.)(1;.&40.R15.)R3;.(1;.&40.R23.)(1;.&40.(2>.R21.(=.+2.+20.)))(1;.&40.(9.R16.(28.R25.)))(1;.&40.R22.)(1;.&40.+1.)R3:.R39.R38.R37.)R1<.(1;.&40.+48174.)R1;.(1=.(0.&40.))R19.(1>.$8.)))")
(* [comment removed for export] *).
  Proof.
    try lx_hide ASB.  (* [comment removed for export] *)
    intros gp tp x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x22 x28 t4 t5 t6 b0 mg0 mg1 qra q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11
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
        (MS (mkR (Z_to_bv 64 0x48178) (Z_to_bv 64 (SP + -128)) gp (Z_to_bv 64 6539920) x5 x6 x7 (Z_to_bv 64 1) (Z_to_bv 64 (nfix n))
                   y10 y11 x12 y13 x14 x15 x16 x17
                   (Z_to_bv 64 AB) (Z_to_bv 64 (needed2 n)) (Z_to_bv 64 (AB + rz_size n)) (Z_to_bv 64 (AB + rz_size n + -16)) x22 (Z_to_bv 64 STK)
                   (Z_to_bv 64 (TID * 2^32)) (Z_to_bv 64 (AB + rz_size n + nfix n)) (Z_to_bv 64 T) (Z_to_bv 64 1) x28 t4 t5 t6)
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
        [ eapply alloc_epi; [exact FRl| exact STl| exact LOIMG| clear - SPL; lia| clear - SPH; lia| exact SPA| exact SCS| exact MU2| exact WM2| assumption]
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


  (* [comment removed for export] *)
  Definition fill_post (SP : Z) (gp tp x28 t4 t5 t6 x22 : word) (F : bvmap 5 word) (fc : bv 32)
      (n AB STK T TID lo fill : Z) (W : list (Z * Z)) (m0 : mem) : machine_state -> Prop := ltac2:(CDefT.buildp (gd_tbl_AW_AllocB ()) "Lms',$17.(27.(0.&40.)Lx1,(0.&40.)(27.(0.&40.)Lx5,(0.&40.)(27.(0.&40.)Lx6,(0.&40.)(27.(0.&40.)Lx7,(0.&40.)(27.(0.&40.)Lx10,(0.&40.)(27.(0.&40.)Lx11,(0.&40.)(27.(0.&40.)Lx12,(0.&40.)(27.(0.&40.)Lx13,(0.&40.)(27.(0.&40.)Lx14,(0.&40.)(27.(0.&40.)Lx15,(0.&40.)(27.(0.&40.)Lx16,(0.&40.)(27.(0.&40.)Lx17,(0.&40.)(27.(0.&40.)Ly28,(0.&40.)(27.(0.&40.)Ly29,(0.&40.)(27.(0.&40.)Ly30,(0.&40.)(27.(0.&40.)Ly31,(0.&40.)(27.P,(0.&40.)(3.(0.&8.))Lm',P,(0.&40.)(3.(0.&8.))ZUB,$1.(9.O8.(2;.O9.))ZCHB,$1.(9.R1.-10.)Zk,$1.(5<.(28.O9.)+1000.)(18.(>.$17.R15.(19.(1:.R14.(1;.&40.(9.O13.-80.))O12.O11.R13.R12.R11.(1;.&40.+1.)(1;.&40.(28.O9.))R10.R?.R>.R=.R<.R;.R:.R9.(1;.&40.O8.)(1;.&40.(29.O9.))(1;.&40.R3.)(1;.&40.R2.)O<.(1;.&40.O7.)(1;.&40.(2>.O5.(=.+2.+20.)))(1;.&40.(9.R3.(28.O9.)))(1;.&40.O6.)(1;.&40.+1.)R8.R7.R6.R5.)O;.(1;.&40.+48174.)O:.(1=.(0.&40.))R4.(1>.$8.)))(18.(11.(12.(5.$1.$1.)(13.$1.$1.O4.(9.O13.-80.))(12.(5.$1.$1.)(13.$1.$1.R3.(9.R3.R1.))O2.))O1.R4.)(18.(14.$8.O1.R4.)(18.(15.$8.R4.)(18.P,(3>.(>.$1.O3.=))(20.$8.R5.R4.(12.$22.(39.(3:.R2.)(3;.(0.&8.)(1;.&8.+;>.)(3:.R2.)))(24.$22.)))(18.P,(>.$1.O3.=)(18.(>.P,(0.&40.)(3.(0.&8.))R5.O1.)(18.(>.(0.&40.)R9.O10.)(18.(>.(0.&40.)R8.O?.)(18.(>.(0.&40.)R7.O>.)(>.(0.&40.)R6.O=.)))))(7.$8.R4.O4.(9.O13.-80.)))))))))))))))))))))))))")
(* [comment removed for export] *).

  Local Ltac2 Set LiaOrc.tbl := fun () => "00`0?L10080313547.85L11212407460.85L14397645527.4 L1938513810.84 L1958740530.85 L21898462210.7 L23634997940.11L23925681167.84L24611005100.2 L25553375254.85L25705851087.2 L27322058401.0 L27705282402.5 L28933518550.85L29264466968.84L29267410806.84L30092326652.83L34075563420.85L34455446187.83L36193165570.2 L37092081232.7 L37293927126.85L39016461238.84L39120847666.87L39423843410.84L39932040119.87L43275003996.85L5039651420.5  L51176289304.84L52870152178.85L52871111443.2 L53522113461.84L53534730161.85L54029594404.2 L55176472655.84L55440600398.85L56083444363.85L57132990364.85L61030858054.84L62631259186.85L63374621462.85L64776702091.85L66324202908.85L6655397976.84 L66907171032.84L67118443646.0 L8276233180.85 L9533021084.85 00000100C00R00a00b01601T01U01[01j02102202:02I02P02Q02^02m03>03A03S03b03c03m04<04n05505B05Q05R05Z05j06:06@06A06K06L06S06i06j07@07A07H07W07^07_07n08=FS3hAR2SP1n4fill2FBS1n2AB3AB04RZSBS3hAR2AL1n4IMG'FS1n2AB4RZSB3N2B1x2HxS3hAR2SP1n2AB2lo3AB15LOIMG3N2BFS1n2KMS3hAR2AL1n4IMG'S1n3NFBSS1n1H2H0S3hAR2AL1n4IMG'S3hAR1nFS3hAR2SP1n2loS3hAR2AL1n4IMG'S3hAR2SP1n2lo3SPLS1nS3hAR1n2AB3AB13N2BS3hAR2AL1n4IMG'FS3hAR2SP1nS3hAR2AL1n4IMG'S3hAR2SP1n2AB2lo2NB3AB03AB15LOIMG3SPL4RZSB3NFB3N2BS3hAR1nS1n4RZSB1H2H0S3hAR2AL1n4IMG'FS1n4MINBS3hAR2AL1n5ALWF'S3hAR2AL1n5ALWF'S1n2KMFS3hAR2SP1nFS3hAR1nS3hAR2SP1n2AB2UB3CHB1kFS3hAR2SP1n2AB2UB3CHB1kFS3hAR1nS3hAR2AL1n4IMG'S3hAR1nSS3hAR2AL1n4IMG'S3hAR2AL1n4IMG'". (* [comment removed for export] *)
  #[using="IMG ALWF CSOK"] Lemma alloc_fill : ltac2:(CDefT.buildp (gd_tbl_AW_AllocB ()) "Pgp,(0.&40.)Ptp,(0.&40.)Px1,(0.&40.)Px5,(0.&40.)Px6,(0.&40.)Px7,(0.&40.)Px10,(0.&40.)Px11,(0.&40.)Px12,(0.&40.)Px13,(0.&40.)Px14,(0.&40.)Px15,(0.&40.)Px16,(0.&40.)Px17,(0.&40.)Px22,(0.&40.)Px28,(0.&40.)Pt4,(0.&40.)Pt5,(0.&40.)Pt6,(0.&40.)Pqra,(0.&40.)Pq0,(0.&40.)Pq1,(0.&40.)Pq2,(0.&40.)Pq3,(0.&40.)Pq4,(0.&40.)Pq5,(0.&40.)Pq6,(0.&40.)Pq7,(0.&40.)Pq8,(0.&40.)Pq9,(0.&40.)Pq10,(0.&40.)Pq11,(0.&40.)PSP,$1.Pn,$1.PAB,$1.PSTK,$1.PT,$1.PTID,$1.Plo,$1.Pfill,$1.PF,(2.&5.(0.&40.))Pfc,(0.&20.)Pm,P,(0.&40.)(3.(0.&8.))Pfr0,(4.(0.&8.))Puj,(4.(0.&8.))PW,(4.(5.$1.$1.))ZUB,$1.(9.R<.(2;.R=.))ZCHB,$1.(9.R1.-10.)Zk,$1.(5<.(28.R?.)+1000.)P,(18.(:.=R10.)(34.R10.(=.+2.+20.)))P,(:.+65?000.R10.)P,(:.(9.R11.(29.R12.))(;.VhAR,))P,(18.(:.=R=.)(:.R=.+1.))P,(10.VCS,R13.(29.R14.))P,P,(3>.(>.$1.R?.=))(20.$8.R=.R9.(12.$22.(39.(3:.R7.)R;.)(24.$22.)))P,(5:.R=.)P,(6.R>.R18.R=.R11.R25.R24.R23.R22.R21.R20.R1?.R1>.R1=.R1<.R1;.R1:.R19.)P,(7.$8.R?.R13.(9.R19.-80.))P,(:.(;.VhAR,)R14.)P,(:.R15.(<.R1;.+200.))P,(:.R1<.(=.+2.+3>.))P,(>.$1.(?.R1=.+10.)=)P,(10.VCS,R18.(<.R1>.R18.))P,(15.$8.R15.)(16.$8.VAL,VCS,(5=.R20.R40.R3?.R31.R30.R2?.R2>.R32.R18.R17.R1?.R1>.R1=.R1<.R1;.R1:.R19.R13.R16.)(19.(1:.R3>.(1;.&40.(9.R20.-80.))R40.R3?.R3=.R3<.R3;.(1;.&40.+1.)(1;.&40.(28.R1?.))R3:.R39.R38.R37.R36.R35.R34.R33.(1;.&40.R1>.)(1;.&40.(29.R1?.))(1;.&40.R12.)(1;.&40.R11.)R32.(1;.&40.R1=.)(1;.&40.(2>.R1;.(=.+2.+20.)))(1;.&40.(9.R12.(28.R1?.)))(1;.&40.R1<.)(1;.&40.+1.)R31.R30.R2?.R2>.)R18.(1;.&40.+48138.)R17.(1=.(0.&40.))R16.(1>.$8.)))")
(* [comment removed for export] *).
  Proof.
    try lx_hide ASB.  (* [comment removed for export] *)
    intros gp tp x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x22 x28 t4 t5 t6 qra q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11
      SP n AB STK T TID lo fill F fc m fr0 uj W UB CHB k
      NB AB0 AB1 FB ACS UC (L1 & L2 & MGC & MH & GF & FMX & FFB & G5 & RM) FR ST LOIMG SPL SPH SPA SCS MI.
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
    (* [comment removed for export] *)
    zstep. zstep. if_cases KF; zify_cond KF.
    - (* [comment removed for export] *)
      apply evtA_done. unfold fill_post. do 16 eexists. exists m. split; [reflexivity|].
      split; [exact MU|]. split; [exact WM|]. split; [exact MI|].
      split; [intros NE; exfalso; apply NE; exact KF|]. split; [intros _; repeat split; reflexivity| exact ST].
    - specialize (UC KF).
      (* [comment removed for export] *)
      zstep. zstep. zstep. zstep. zstep.
      replace (sx32 (Z_to_bv 64 4096)) with (Z_to_bv 64 4096) by (apply bv_eq; vm_compute; reflexivity).
      assert (TAILM : forall (q2 : word), 
        evtA asegs AL CS (fill_post SP gp tp x28 t4 t5 t6 x22 F fc n AB STK T TID lo fill W m)
          (MS (mkR x1 (Z_to_bv 64 (SP + -128)) gp tp x5 x6 x7 (Z_to_bv 64 1) (Z_to_bv 64 (nfix n))
                   (Z_to_bv 64 1077752) (Z_to_bv 64 4096) (Z_to_bv 64 (Z.min (nfix n) 4096)) x13 x14 x15 x16 x17
                   (Z_to_bv 64 AB) (Z_to_bv 64 (needed2 n)) (Z_to_bv 64 (AB + rz_size n)) (Z_to_bv 64 (AB + rz_size n + -16)) x22 (Z_to_bv 64 STK)
                   (Z_to_bv 64 (TID * 2^32)) (Z_to_bv 64 (AB + rz_size n + nfix n)) (Z_to_bv 64 T) (Z_to_bv 64 1) x28 t4 t5 t6)
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
        unfold fill_post. do 16 eexists. exists m'. split; [reflexivity|].
        split. { eapply munch_weaken; [| exact MUm]. unfold sub_fp; cbn [outside]. clear. intros x Hx. tauto. }
        split; [exact WMm|]. split; [exact MIm|]. split; [intros _; exact SHm|].
        split; [intros F0; exfalso; apply KF; exact F0|].
        eapply stk_transport_disjoint; [exact ST| exact MUm| exact WMm|]. cbn [disjoint_from]. split; [| exact I]. clear - AB1 LOIMG SPL N2B MINB RZSB. lia. }
      zstep. if_cases KM; zify_cond KM.
      + replace (Z.min (nfix n) 4096) with (nfix n) in TAILM by (clear - KM; lia). apply TAILM. exact x12.
      + zstep. replace (Z.min (nfix n) 4096) with 4096 in TAILM by (clear - KM; lia). apply TAILM. exact x12.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
End AllocB.

End ARUN_2.
