(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Arr Asn1Aux CellsX.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import A_stringA.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import AW_Unwind AW_MmapFixed.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BLX Require Import LxA.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import ATac.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.AHeap Require Import ACeil.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LXAW Require Import LxFlat.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Import OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.LxhSyntax. #[local] Instance lxh_tab : OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.lx_hints := OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.lxh_parse "P002b8952e084d4a5 0 4 0 16 16 16 21 16 22 16P006acee546b704ba 0 4 0 64 48 8 51 8 54 8P0086a5ae9231fdad 0 4 0 1 42 1 51 1 52 1P009af121a3e36c04 0 2 0 1 8 1P00e2441353fc700d 0 4 0 1 42 1 51 1 52 1P01f52509674270ce 0 4 0 1 43 1 51 1 52 1P02ea5871283f4f65 0 4 0 1 43 1 51 1 52 1P05c2f8f8d9b04862 0 4 0 16 16 16 21 16 22 16P05dcac154e2e2380 0 4 0 1 43 1 51 1 52 1P06205780a0c5daa3 0 4 0 16 16 16 21 16 22 16P066926e731b7cec3 1 1 8 3 0 1 50 1 52 1 4 45 1 51 1 53 1 54 8P066e68a467cc401f 0 4 0 1 42 1 51 1 52 1P07794cd21e11aced 1 1 16 2 1 1 22 1 5 11 1 17 1 18 1 23 1 24 16P08cb277f283ffad3 1 1 8 2 0 1 50 1 3 46 1 51 1 52 8P0923cb6c083592e6 0 4 0 8 45 8 50 8 51 8P096fce4b3dbf203c 0 5 0 64 44 8 47 8 52 8 53 8P09843e4c5389bdec 1 2 16 2 0 1 23 1 16 2 1 1 22 1 2 24 1 25 1P09e42039e2eb158f 0 2 0 1 7 1P0ac515364ea5ff29 0 2 0 1 34 1P0c62558735bb3c55 0 2 0 1 33 1P0c9cf79e132a50eb 0 5 0 64 44 8 47 8 52 8 53 8P0cb61f4e23a56cbe 0 4 0 16 16 16 21 16 22 16P0d3ad33b369043d8 0 4 0 1 43 1 51 1 52 1P0d79907a96d76fb0 0 4 0 1 43 1 51 1 52 1P0e59b0a2dc7abcc5 0 4 0 16 16 16 21 16 22 16P0f6e03dba3d0f6c6 0 4 0 1 42 1 51 1 52 1P103b294efe599d01 0 4 0 1 42 1 51 1 52 1P120eec04be3f8a8a 0 4 0 1 42 1 51 1 52 1P12b881d09c8d95f3 0 4 0 1 43 1 51 1 52 1P12e948525977c0d6 0 2 0 1 33 1P1363b1f84cc4fda0 0 4 0 16 16 16 21 16 22 16P13b1ae766956923c 0 4 0 8 45 8 50 8 51 8P13f546b59be535d6 0 4 0 1 42 1 51 1 52 1P1561298ccf46c54e 0 4 0 1 42 1 51 1 52 1P163d7b6e977a89f3 1 1 16 2 1 1 22 1 5 11 1 17 1 18 1 23 1 24 16P17b6250689e7639c 0 4 0 16 16 16 21 16 22 16P18130eff171a2902 0 4 0 1 42 1 51 1 52 1P18132d373823653e 0 4 0 1 43 1 51 1 52 1P19994a5308831b37 0 2 0 1 8 1P19b920f02a3cb9eb 0 4 0 1 42 1 51 1 52 1P1ada1f120328005e 1 2 16 2 0 1 23 1 16 2 1 1 22 1 2 24 1 25 1P1c27d96fa5287708 0 4 0 1 42 1 51 1 52 1P1db17f70f16c7a88 0 4 0 16 16 16 21 16 22 16P1deeaa9db29a5e33 1 2 16 2 0 1 23 1 16 2 1 1 22 1 2 24 1 25 1P22f7ac1370b066f2 0 5 0 64 45 8 47 8 52 8 53 8P23b04ca2ee36e145 0 4 0 8 44 8 50 8 51 8P23b7a1f2b1161db3 1 1 8 3 0 1 50 1 52 1 5 46 8 47 8 51 8 53 8 54 64P23e69f762b3155a9 0 4 0 16 16 16 21 16 22 16P2458e9f3861414c0 0 4 0 1 43 1 51 1 52 1P253b2ed9dae5b2b5 0 4 0 1 42 1 51 1 52 1P26c4528d8b95b1f0 1 1 16 2 1 1 22 1 5 11 1 17 1 18 1 23 1 24 16P26c9b20bd301a1ee 0 4 0 16 16 16 21 16 22 16P271e144533fea8a7 0 4 0 16 16 16 21 16 22 16P274bdc7a9af0788e 1 1 16 2 1 1 22 1 5 11 1 17 1 18 1 23 1 24 16P290c8a2f150e7671 0 4 0 16 16 16 21 16 22 16P29e65e0c6b90cd7d 1 1 8 2 0 1 50 1 3 46 1 51 1 52 8P2a4b013fc9eb163e 0 2 0 1 33 1P2aa76f1f7ac95b46 0 4 0 16 16 16 21 16 22 16P2be6ec481d277d2c 0 4 0 16 16 16 21 16 22 16P2c05ad15bb37b3fe 1 1 8 2 0 1 50 1 3 46 1 51 1 52 8P2d3a0a769122bb71 0 4 0 16 16 16 21 16 22 16P2db141e08f18b2b8 0 4 0 16 16 16 21 16 22 16P2e384c1c5dcdd97f 0 6 0 8 43 8 50 8 51 8 52 8 53 8P2e9b3116d39b9731 0 4 0 16 16 16 21 16 22 16P2ef571552dc29bcf 0 4 0 1 43 1 51 1 52 1P2f316f74a0d97d89 0 4 0 1 43 1 51 1 52 1P2fd0f88600959ab5 0 4 0 16 16 16 21 16 22 16P2fee36b5741f0d0a 0 6 0 8 44 8 50 8 51 8 52 8 53 8P302672a5b176e8cb 0 2 0 1 8 1P30c9ea51a2876ee8 0 5 0 64 45 8 47 8 52 8 53 8P317e00463a759837 0 6 0 8 43 8 50 8 51 8 52 8 53 8P32442d61c740ebc2 0 2 0 1 33 1P3275b5427d3be17e 0 2 0 1 34 1P337338a54c4f3bb4 0 2 0 1 34 1P33f095304b2f8116 0 6 0 8 44 8 50 8 51 8 52 8 53 8P345983c695ce160c 0 4 0 8 44 8 50 8 51 8P34a9c56ac6aa83bf 0 4 0 16 16 16 21 16 22 16P34b99aa127c33266 0 4 0 1 43 1 51 1 52 1P34ddef3398b99b42 0 2 0 1 7 1P353f52298d86ce7a 1 1 8 2 0 1 50 1 3 46 1 51 1 52 8P354365cc6329f466 1 1 8 3 0 1 50 1 52 1 4 45 1 51 1 53 1 54 8P356109638bb3b8e0 0 4 0 64 48 8 51 8 54 8P35c0825e2b5c4de3 0 4 0 16 16 16 21 16 22 16P365de3f21806f513 0 2 0 1 34 1P37569a5be0a804a4 0 4 0 1 43 1 51 1 52 1P390d31b0d2148b59 0 4 0 1 43 1 51 1 52 1P399d7d5f31939674 1 1 8 3 0 1 50 1 52 1 4 45 1 51 1 53 1 54 8P3a4fa3e9d7e651f8 0 4 0 1 42 1 51 1 52 1P3c0d1c9ad5602208 0 4 0 16 16 16 21 16 22 16P3c1e8c01d2358eb5 0 2 0 1 34 1P3c7481f877b31203 0 4 0 1 42 1 51 1 52 1P3eb5cee1e328c673 0 2 0 1 34 1P3f78e89b890ae5d7 0 4 0 1 43 1 51 1 52 1N04c95b6bcd58e1d3N06fcdfd01ee421cdN0b94bd836f253f21N0c5bc1b2445f3182N0d3a1c946d5901ebN0e67c5e78fa00fa4N0f6606b311330233N0fa69968698233a6N20a9e2e3da8e4d2aN223ba655ccac380eN2252fbb77a422c39N2389e98004f25666N26586642da941351N26b8b0d945421109N29b877d5759aa614N2ac2558223ea965bN35846332f09a6c25N37c647024e61474bN395a040927bd18a8N3b8a8d2a15f1a94aN3df5bd3418206262N3ea9e6549ed68ca8N3ef910c162c966e8"%lxh.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import LiaOrc. (* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= orc_lia. (* [comment removed for export] *)
Local Ltac dlia ::= orc_dlia. (* [comment removed for export] *)
Local Ltac plia ::= orc_plia. (* [comment removed for export] *)
Local Ltac clear_disj ::= fc_clear_disj. (* [comment removed for export] *)
Local Ltac prune_disj ::= fc_prune_disj. (* [comment removed for export] *)
Ltac2 gd_tbl_AW_Poison () : Init.string Init.list := ["Corelib.Init.Logic.and"; "RocqVerifyHarness.AgentSubmission.Lib.Step.ro_cells"; "RocqVerifyHarness.AgentSubmission.B.AImg.asegs"; "ARUN_1.A_CANPOISON"; "Corelib.Init.Datatypes.cons"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.cell"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C1"; "stdpp.bitvector.definitions.Z_to_bv"; "Corelib.Init.Datatypes.nil"; "ARUN_1.A_GOT_SB"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C8"; "ARUN_1.A_SBCELL"; "ARUN_1.A_GOT_MIDBEG"; "ARUN_1.A_MIDBEG"; "ARUN_1.A_GOT_MIDEND"; "ARUN_1.A_MIDEND"; "ARUN_1.A_GOT_HIGHEND"; "ARUN_1.A_HIGHEND"; "ARUN_1.A_GOT_RMEMSET"; "ARUN_1.A_RMEMSET"; "ARUN_1.A_MUSL_MEMSET"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_MmapFixed.A_GOT_CFLAGS"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_MmapFixed.A_CFLAGS"; "ARUN_1.A_CF_CSMT"; "Corelib.Init.Datatypes.list"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.ivl"; "stdpp.bitvector.definitions.bv"; "Corelib.Init.Datatypes.option"; "ARUN_1.poison_statics"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.munch"; "Corelib.Numbers.BinNums.Z"; "Stdlib.ZArith.BinInt.Z.le"; "Stdlib.ZArith.BinInt.Z.add"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.disjoint_from"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.machine_state"; "Corelib.Init.Logic.ex"; "Corelib.Init.Logic.eq"; "RocqVerifyHarness.AgentSubmission.Lib.MState.MS"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.mkR"; "RocqVerifyHarness.AgentSubmission.Lib.MState.ret_pc"; "Corelib.Init.Datatypes.None"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.seg_rom"; "Corelib.Init.Datatypes.prod"; "Corelib.Init.Datatypes.pair"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.wmono"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.mem_inv"; "RocqVerifyHarness.AgentSubmission.Lib.Step.rw_cells"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.CB"; "Stdlib.ZArith.BinInt.Z.to_nat"; "Corelib.Lists.ListDef.repeat"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.stk"; "LinuxProcessSemantics.Riscv.Prelude.bvmap"; "Stdlib.ZArith.BinInt.Z.div"; "Stdlib.ZArith.BinInt.Z.modulo"; "Stdlib.ZArith.BinInt.Z.lt"; "Corelib.Init.Logic.or"; "RocqVerifyHarness.AgentSubmission.LibA.ALazy.crange"; "RocqVerifyHarness.AgentSubmission.AHeap.ACeil.ACEIL"; "Stdlib.ZArith.BinInt.Z.sub"; "Stdlib.ZArith.BinInt.Z.pow"; "RocqVerifyHarness.AgentSubmission.LibA.AEvtA.evtA"; "ARUN_1.Poison.poison_post"; "ARUN_1.A_POISON"; "Corelib.Init.Logic.not"].

Section ARUN_1. Context {hAR : arun}.
Definition A_POISON : Z := 0x6a55c.
Definition A_CANPOISON : Z := 0x10925c.     (* [comment removed for export] *)
Definition A_GOT_SB : Z := 0x0f5e50.        (* [comment removed for export] *)
Definition A_SBCELL : Z := 0x1099f8.
Definition A_GOT_MIDBEG : Z := 0x0f5e58.    (* [comment removed for export] *)
Definition A_MIDBEG : Z := 0x10a6e8.
Definition A_GOT_MIDEND : Z := 0x0f5e60.    (* [comment removed for export] *)
Definition A_MIDEND : Z := 0x10a6f0.
Definition A_GOT_HIGHEND : Z := 0x0f5e68.   (* [comment removed for export] *)
Definition A_HIGHEND : Z := 0x10a6e0.
Definition A_GOT_RMEMSET : Z := 0x0f5e70.   (* [comment removed for export] *)
Definition A_RMEMSET : Z := 0x0f7cd0.
Definition A_MUSL_MEMSET : Z := 0x0eadc4.
Definition A_CF_CSMT : Z := 0x19b5a0.       (* [comment removed for export] *)

Definition poison_statics (m : mem) : Prop := ltac2:(CDefT.buildp (gd_tbl_AW_Poison ()) "(0.(1.$2.O1.$3.(4.$5.(6.(7.&8.+1.))(8.$5.)))(0.(1.$2.O1.$9.(4.$5.(:.(7.&40.$;.))(8.$5.)))(0.(1.$2.O1.$;.(4.$5.(:.(7.&40.+7???8000.))(8.$5.)))(0.(1.$2.O1.$<.(4.$5.(:.(7.&40.$=.))(8.$5.)))(0.(1.$2.O1.$=.(4.$5.(:.(7.&40.=))(8.$5.)))(0.(1.$2.O1.$>.(4.$5.(:.(7.&40.$?.))(8.$5.)))(0.(1.$2.O1.$?.(4.$5.(:.(7.&40.=))(8.$5.)))(0.(1.$2.O1.$10.(4.$5.(:.(7.&40.$11.))(8.$5.)))(0.(1.$2.O1.$11.(4.$5.(:.(7.&40.+7???????????.))(8.$5.)))(0.(1.$2.O1.$12.(4.$5.(:.(7.&40.$13.))(8.$5.)))(0.(1.$2.O1.$13.(4.$5.(:.(7.&40.$14.))(8.$5.)))(0.(1.$2.O1.$15.(4.$5.(:.(7.&40.$16.))(8.$5.)))(1.$2.O1.$17.(4.$5.(:.(7.&40.+????????????????.))(8.$5.)))))))))))))))")
(* [comment removed for export] *).

Local Ltac2 Set LiaOrc.tbl := fun () => "00=0>L15546989475.8L18563722787.8L21065376163.8L33626540963.7L35947708835.8L3867243683.8 L4158894243.8 L48848155811.8L51649670051.8L51774008483.8L57919349667.8L64507403683.8L68409310627.800000100200300400500600700800900:00;00<00=SSSSSSSSSSSSS". (* [comment removed for export] *)
Lemma poison_statics_transport : ltac2:(CDefT.buildp (gd_tbl_AW_Poison ()) "PW,(18.$19.)Pm,P,(1:.&40.)(1;.(1:.&8.))Pm',P,(1:.&40.)(1;.(1:.&8.))P,(1<.R2.)P,(1=.R4.R3.R2.)P,PA,$1>.Pn,$1>.P,(0.(1?.+10000.R2.)(1?.(20.R2.R1.)+1=;8<8.))(21.R8.R3.R2.)(1<.R4.)")
(* [comment removed for export] *).
Proof.
  intros W m m' PS MU DJ. unfold poison_statics in *.
  unfold A_CANPOISON, A_GOT_SB, A_SBCELL, A_GOT_MIDBEG, A_MIDBEG, A_GOT_MIDEND, A_MIDEND, A_GOT_HIGHEND, A_HIGHEND,
    A_GOT_RMEMSET, A_RMEMSET, A_GOT_CFLAGS, A_CF_CSMT in *.
  repeat match goal with |- _ /\ _ => split end;
    match goal with |- ro_cells _ _ ?a _ => 
      repeat match type of PS with _ /\ _ => let H := fresh in (flat constr:(PS) 2%nat; flclear PS; intros H PS); first [ (eapply ro_cells_transport; [exact H| exact MU| apply DJ; cbn; lia]) | clear H ] end
    end.
  all: eapply ro_cells_transport; [exact PS| exact MU| apply DJ; cbn; lia].
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

Section Poison.
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

  Definition poison_post (ra : word) (SP : Z) (gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
      (F : bvmap 5 word) (fc : bv 32) (S k v lo : Z) (W : list (Z * Z)) (m0 : mem) : machine_state -> Prop := ltac2:(CDefT.buildp (gd_tbl_AW_Poison ()) "Lms',$22.(23.(1:.&40.)Lt0,(1:.&40.)(23.(1:.&40.)Lt1,(1:.&40.)(23.(1:.&40.)Lt2,(1:.&40.)(23.(1:.&40.)La0,(1:.&40.)(23.(1:.&40.)La1,(1:.&40.)(23.(1:.&40.)La2,(1:.&40.)(23.(1:.&40.)La3,(1:.&40.)(23.(1:.&40.)La4,(1:.&40.)(23.(1:.&40.)La5,(1:.&40.)(23.(1:.&40.)La6,(1:.&40.)(23.(1:.&40.)La7,(1:.&40.)(23.(1:.&40.)Lt3,(1:.&40.)(23.(1:.&40.)Lt4,(1:.&40.)(23.(1:.&40.)Lt5,(1:.&40.)(23.(1:.&40.)Lt6,(1:.&40.)(23.P,(1:.&40.)(1;.(1:.&8.))Lm',P,(1:.&40.)(1;.(1:.&8.))(0.(24.$22.R11.(25.(26.O18.(7.&40.O17.)O16.O15.R10.R?.R>.O14.O13.R=.R<.R;.R:.R9.R8.R7.R6.O12.O11.O10.O?.O>.O=.O<.O;.O:.O9.R5.R4.R3.R2.)O8.(27.O18.)O7.(28.(1:.&40.))R1.(29.$2.)))(0.(1=.(4.(2:.$1>.$1>.)(2;.$1>.$1>.O3.O17.)(4.(2:.$1>.$1>.)(2;.$1>.$1>.O6.(20.O6.O5.))O2.))O1.R1.)(0.(2<.$2.O1.R1.)(0.(2=.$2.R1.)(0.(2>.$2.R1.O6.(4.$5.(2?.(30.O5.)(31.(1:.&8.)(7.&8.O4.)(30.O5.)))(8.$5.)))(32.$2.R1.O3.O17.))))))))))))))))))))))")
(* [comment removed for export] *).

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00I0@L22706556426.7  L25199327600.14 L26362538504.4  L39188636933.0  L39937689165.1  L40480480168.3  L41157950393.3  L47055392484.6  L47413540911.21 L51794644481.6  L54942915530.18 L61028786748.118L61028786748.119L61028859847.111L61028859847.112L61031299700.110L61031299700.111L63368132624.112L63368132624.113L63368248989.113L63368248989.114L65567290536.21 L7637200128.118 L7637200128.119 L9690273311.4   00000B00b00k00l01001;01C01M02A02T03403E03V03g04804I04Z04k05<05M05^06N06c07807CS2SP2lo1W1S1k1y2HyS1A1n1S1k4NPOS2HS2HK2A82AN2DA2DNS1A1n3RNGSS2SPS2SP2lo3SPLS1A1S2HSS1A1S2HS1xS3hAR2SP1A1n2lo1S1k4NPOS5LOIMG2HS2HK2A83AHI2AN2DA2DNS1n1k4NPOS2HK2DN2MNS1A1n1S1k3NAL4NPOS2HK2A82DN1x2HxS3hAR2SP1A1n4NPOSS3hAR2SP1A1n4NPOSS3hAR2SP1A1n4NPOSS3hAR2SP1A1n4NPOSS3hAR2SP1A1n4NPOSS3hAR2SP1A1n4NPOSS3hAR2SP1A1n4NPOSS3hAR2SP1A1n4NPOSS3hAR2SP1A1n4NPOSS3hAR2SP1A1n4NPOSS3hAR2SP1A1n2lo1S1k4NPOS5LOIMG2HS2HK2A82AN2DA2DNS3hAR2SP1A1n1S4NPOS1xS3hAR2SP1A1n1S4NPOS1xS1A1S2HS2A8". (* [comment removed for export] *)
  Lemma poison_tail : ltac2:(CDefT.buildp (gd_tbl_AW_Poison ()) "Pra,(1:.&40.)Pgp,(1:.&40.)Ptp,(1:.&40.)Pt0,(1:.&40.)Pt1,(1:.&40.)Pt2,(1:.&40.)Ps0,(1:.&40.)Pa3,(1:.&40.)Pa5,(1:.&40.)Pa6,(1:.&40.)Pa7,(1:.&40.)Ps2,(1:.&40.)Ps3,(1:.&40.)Ps4,(1:.&40.)Ps5,(1:.&40.)Ps6,(1:.&40.)Ps7,(1:.&40.)Ps8,(1:.&40.)Ps9,(1:.&40.)Ps10,(1:.&40.)Ps11,(1:.&40.)Pt3,(1:.&40.)Pt4,(1:.&40.)Pt5,(1:.&40.)Pt6,(1:.&40.)Pq1,(1:.&40.)Pq2,(1:.&40.)Pq3,(1:.&40.)Pq4,(1:.&40.)Pq5,(1:.&40.)PSP,$1>.PA,$1>.Pn,$1>.Pv,$1>.Plo,$1>.PF,(33.&5.(1:.&40.))Pfc,(1:.&20.)Pm0,P,(1:.&40.)(1;.(1:.&8.))Pm,P,(1:.&40.)(1;.(1:.&8.))PW,(18.(2:.$1>.$1>.))Pjunk,(18.(1:.&8.))Pfr,(18.(1:.&8.))ZS,$1>.(20.+7???8000.(34.R;.+8.))Zk,$1>.(34.R;.+8.)P,(24.$1>.(35.R=.+8.)=)P,(24.$1>.(35.R=.+8.)=)P,(1?.=R>.)P,(0.(1?.=R>.)(36.R>.+100.))P,(37.(0.(1?.+8.R11.)(0.(1?.R11.+7???7??8.)(1?.(20.R11.R10.)+7???8000.)))(0.(1?.+10007???8000.R11.)(0.(1?.+10007???8008.(20.R11.R10.))(0.(1?.R11.+7??????????8.)(1?.(20.R11.R10.)+800000000000.)))))P,(38.VCS,R12.R11.)P,(2>.$2.R<.R8.(4.$5.(2?.(30.R7.)R:.)(8.$5.)))P,(1<.R=.)P,(2>.$2.R>.(20.R16.-40.)(4.$5.(2?.#8.R;.)(4.$5.(:.R17.)(4.$5.(:.R18.)(4.$5.(:.R19.)(4.$5.(:.R1:.)(4.$5.(:.R1;.)(4.$5.(:.R2>.)(4.$5.(:.R34.)(8.$5.))))))))))P,(32.$2.R?.R13.(20.R17.-40.))P,(1?.(39.VhAR,)R14.)P,(1?.R15.(3:.R19.+40.))P,(1?.R1:.(3;.+2.+3?.))P,(24.$1>.(35.R1;.+10.)=)P,(38.VCS,R18.(3:.R1<.R18.))P,(1=.(4.(2:.$1>.$1>.)(2;.$1>.$1>.R19.R1=.)(4.(2:.$1>.$1>.)(2;.$1>.$1>.R11.(20.R11.R10.))R14.))R16.R15.)P,(2<.$2.R17.R16.)P,(2=.$2.R17.)(3<.$2.VAL,VCS,(3=.R3>.R20.R3=.R3<.R38.R25.R24.R23.R22.R21.R2?.R2>.R2=.R2<.R2;.R2:.R1;.R1:.R14.R13.R1=.R1<.R17.R19.)(25.(26.R3>.(7.&40.(20.R20.-40.))R3=.R3<.R3;.R3:.R39.R38.(7.&40.+7???8000.)(7.&40.R1?.)(7.&40.R1>.)(7.&40.R1=.)R37.(7.&40.+7???7???.)R36.R35.R34.R33.R32.R31.R30.R2?.R2>.R2=.R2<.R2;.R2:.R29.R28.R27.R26.)R1;.(7.&40.+6:78<.)R1:.(28.(1:.&40.))R18.(29.$2.)))")
(* [comment removed for export] *).
  Proof.
    intros ra gp tp t0 t1 t2 s0 a3 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 q1 q2 q3 q4 q5 SP A n v lo F fc m0 m W junk fr S k
      AAL NAL NPOS VB RNG ACS SH PS FR ST LOIMG SPL SPH SPA SCS MU WM MI.
    flat constr:(PS) 13%nat. intros CP G1 SB G2 MB G3 ME G4 HE G5 RM G6 CT.
    unfold A_POISON, A_CANPOISON, A_GOT_SB, A_SBCELL, A_GOT_MIDBEG, A_MIDBEG, A_GOT_MIDEND, A_MIDEND, A_GOT_HIGHEND, A_HIGHEND,
      A_GOT_RMEMSET, A_RMEMSET, A_GOT_CFLAGS, A_CFLAGS, A_CF_CSMT, A_MUSL_MEMSET in *.
    assert (HS : S = 0x7fff8000 + A / 8) by reflexivity. assert (HK : k = n / 8) by reflexivity. clearbody S k. clear PS.
    assert (AB : 8 <= A <= 2^47 - 8 /\ A + n <= 2^47) by (clear - RNG NPOS; lia). flat constr:(AB) 2%nat. flclear AB. intros (A8 & AHI) AN.
    (* [comment removed for export] *)
    pose proof (conj MU (conj WM SH) : id (munch ((lo, SP) :: (S, S + k) :: W) m0 m /\ wmono asegs m0 m /\ rw_cells asegs m S [CB (Z.to_nat k) junk])) as MW0.
    clear MU WM SH. pose proof (munch_refl [(lo, SP)] m) as MU. pose proof (wmono_refl asegs m) as WM.
    (* [comment removed for export] *)
    destruct RNG as [(R1 & R2 & R3)|(R1 & R2 & R3 & R4)];
      (lx_run_tac (PLAN [0x0eadc4] [] 200%N); lx_tree;
       first [
lazymatch goal with |- False =>
    repeat match goal with K : _ = true |- _ => revert K | K : _ = false |- _ => revert K end;
    clear - AAL NAL A8 AHI AN NPOS VB R1 R2 R3; intros;
    pose proof (Z.div_mod A 8 ltac:(lia)) as DA; pose proof (Z.div_mod n 8 ltac:(lia)) as DN;
    pose proof (Z.mod_pos_bound A 8 ltac:(lia)) as MA; pose proof (Z.mod_pos_bound n 8 ltac:(lia)) as MN;
    repeat match goal with
    | K : (if ?c then false else true) = true |- _ => destruct c eqn:?LXE; [discriminate K| clear K]
    | K : (if ?c then false else true) = false |- _ => destruct c eqn:?LXE; [clear K| discriminate K]
    end;
    repeat match goal with
    | K : (?a <? ?b) = true |- _ => apply Z.ltb_lt in K
    | K : (?a <? ?b) = false |- _ => apply Z.ltb_ge in K
    | K : (?a <=? ?b) = true |- _ => apply Z.leb_le in K
    | K : (?a <=? ?b) = false |- _ => apply Z.leb_gt in K
    | K : (?a =? ?b) = true |- _ => apply Z.eqb_eq in K
    | K : (?a =? ?b) = false |- _ => apply Z.eqb_neq in K
    end;
    rewrite ?Z.shiftr_div_pow2 in * by (clear; lia); change (2^3) with 8 in *; unfold zlow in *;
    change ((-1) mod 2 ^ 64) with 18446744073709551615 in *;
    rewrite ?(Z.mod_small 18446744073709551615 (2 ^ 64)) in * by (clear; lia);
    rewrite ?(Z.mod_small 0 (2 ^ 64)) in * by (clear; lia);
    repeat match goal with K : context [?e mod 2 ^ 64] |- False =>
      first [ rewrite (Z.mod_small e (2 ^ 64)) in * by (clear - AAL NAL DA DN MA MN A8 AHI AN NPOS VB; nia)
            | lazymatch goal with _ : 0 <= e mod 2 ^ 64 < 2 ^ 64 |- _ => fail | |- _ => pose proof (Z.mod_pos_bound e (2 ^ 64) ltac:(clear; lia)) end ]
    end;
    nia
end
       |
lazymatch goal with MW0 : id _ |- _ => unfold id in MW0; (flat constr:(MW0) 3%nat; flclear MW0; intros MU0 WM0 SH0) end;
  pose proof (Z.div_mod A 8 ltac:(lia)) as DA; pose proof (Z.div_mod n 8 ltac:(lia)) as DN;
  pose proof (Z.mod_pos_bound A 8 ltac:(lia)) as MA; pose proof (Z.mod_pos_bound n 8 ltac:(lia)) as MN;
  rewrite !Z.shiftr_div_pow2 by (clear; lia); change (2^3) with 8;
  lazymatch goal with MUl : munch _ m ?mx, WMl : wmono _ m _, MIl : mem_inv _ ?my, STl : stk _ _ lo _, FRl : rw_cells _ _ (SP + -64) _,
                      SH0 : rw_cells _ m S _, MU0 : munch _ m0 m, WM0 : wmono _ m0 m, HS : S = _, HK : k = _ |- _ =>
  pose proof (rw_cells_transport _ _ m mx S _ SH0 MUl WMl ltac:(cbn [disjoint_from cells_size csize]; pose proof aceil_bounds; clear - HS HK DA DN MA MN LOIMG SPL H NPOS A8 AHI AN; lia)) as SHl;
  pose proof (stk_release _ mx lo _ _ STl FRl ltac:(clear - SPL; lia)) as STl2; cbn [cells_size csize Nat.add] in STl2;
  replace (SP + -64 + Z.of_nat 64) with SP in STl2 by (clear; lia);
  replace (A / 8 + 2147450880) with S by (clear - HS; lia);
  replace (- (A / 8) + ((A + (n + -8)) / 8 + 1)) with k by (clear - HK AAL NAL DA DN MA MN A8 NPOS; nia);
  eapply evtA_mono;
  [ eapply (A_memset_evtA_aok AL CS IMG) with (junk := junk);
     [exact SHl| exact MIl| | clear - HS A8; lia| clear - HK NPOS DN MN; lia| clear - HS HK A8 AHI AN DA DN MA MN NPOS; lia| exact VB
     | reflexivity| reflexivity| reflexivity];
    intros x Hx; right; left; exists (A + 8 * (x - S)); split;
    [ apply ACS; clear - Hx HS HK A8 AHI AN DA DN MA MN AAL NAL NPOS; lia
    | unfold shadow_of; rewrite ASB; replace (A + 8 * (x - S)) with (A + (x - S) * 8) by lia; rewrite Z.div_add by lia; clear - Hx HS; lia ]
  | cbn beta; intros ms2 (z0 & z1 & z2 & w1 & w2 & w3 & w4 & w5 & w6 & w7 & z3 & z4 & z5 & z6 & m' & -> & MUm & WMm & MIm & SHm);
    unfold poison_post; do 15 eexists; exists m'; split; [reflexivity|];
    split; [ eapply munch_trans; [exact MU0|]; eapply munch_trans; [eapply munch_weaken; [| exact MUl]| eapply munch_weaken; [| exact MUm]]; unfold sub_fp; cbn [outside]; clear; intros y Hy; lia |];
    split; [eapply wmono_trans; [exact WM0| eapply wmono_trans; [exact WMl| exact WMm]]|]; split; [exact MIm|]; split; [exact SHm|];
    eapply stk_transport_disjoint; [exact STl2| exact MUm| exact WMm|]; cbn [disjoint_from]; split; [| exact I];
    pose proof aceil_bounds; clear - HS HK A8 AHI AN LOIMG SPL DA DN MA MN H NPOS; lia ]
  end
       ]).
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0090@L11332654655.15 L22706556426.7  L26362538504.4  L39060842203.106L39060842203.107L61030877180.105L61030877180.106L61030877181.104L61030877181.10500000T00f00o01Z02E02V02g03803IS3hAR2SP1A1n2lo4NPOS5LOIMG2A83AHI2ANS2SP1A1n2lo1W1y2HyS1A1n3RNGS3hAR2SP1A1n2lo4NPOS2R15LOIMG3SPL2A02n03H17S3hAR2SP1A1n2lo4NPOS2R15LOIMG3SPL2A02n03H17S3hAR2SP1A1n4NPOSS3hAR2SP1A1n4NPOSS3hAR2SP1A1n4NPOSS3hAR2SP1A1n4NPOS". (* [comment removed for export] *)
  Lemma poison_body : ltac2:(CDefT.buildp (gd_tbl_AW_Poison ()) "Pra,(1:.&40.)Pgp,(1:.&40.)Ptp,(1:.&40.)Pt0,(1:.&40.)Pt1,(1:.&40.)Pt2,(1:.&40.)Ps0,(1:.&40.)Ps1,(1:.&40.)Pa3,(1:.&40.)Pa4,(1:.&40.)Pa5,(1:.&40.)Pa6,(1:.&40.)Pa7,(1:.&40.)Ps2,(1:.&40.)Ps3,(1:.&40.)Ps4,(1:.&40.)Ps5,(1:.&40.)Ps6,(1:.&40.)Ps7,(1:.&40.)Ps8,(1:.&40.)Ps9,(1:.&40.)Ps10,(1:.&40.)Ps11,(1:.&40.)Pt3,(1:.&40.)Pt4,(1:.&40.)Pt5,(1:.&40.)Pt6,(1:.&40.)PSP,$1>.PA,$1>.Pn,$1>.Pv,$1>.Plo,$1>.PF,(33.&5.(1:.&40.))Pfc,(1:.&20.)Pm0,P,(1:.&40.)(1;.(1:.&8.))Pm,P,(1:.&40.)(1;.(1:.&8.))PW,(18.(2:.$1>.$1>.))Pjunk,(18.(1:.&8.))Pfr,(18.(1:.&8.))ZS,$1>.(20.+7???8000.(34.R;.+8.))Zk,$1>.(34.R;.+8.)P,(24.$1>.(35.R=.+8.)=)P,(24.$1>.(35.R=.+8.)=)P,(1?.=R>.)P,(0.(1?.=R>.)(36.R>.+100.))P,(37.(0.(1?.+8.R11.)(0.(1?.R11.+7???7??8.)(1?.(20.R11.R10.)+7???8000.)))(0.(1?.+10007???8000.R11.)(0.(1?.+10007???8008.(20.R11.R10.))(0.(1?.R11.+7??????????8.)(1?.(20.R11.R10.)+800000000000.)))))P,(38.VCS,R12.R11.)P,(2>.$2.R<.R8.(4.$5.(2?.(30.R7.)R:.)(8.$5.)))P,(1<.R=.)P,(2>.$2.R>.(20.R16.-40.)(4.$5.(2?.#8.R;.)(4.$5.(:.R21.)(4.$5.(:.R22.)(4.$5.(:.R23.)(4.$5.(:.R24.)(4.$5.(:.R2:.)(4.$5.(:.R2;.)(4.$5.(:.R31.)(8.$5.))))))))))P,(32.$2.R?.R13.(20.R17.-40.))P,(1?.(39.VhAR,)R14.)P,(1?.R15.(3:.R19.+40.))P,(1?.R1:.(3;.+2.+3?.))P,(24.$1>.(35.R1;.+10.)=)P,(38.VCS,R18.(3:.R1<.R18.))P,(1=.(4.(2:.$1>.$1>.)(2;.$1>.$1>.R19.R1=.)(4.(2:.$1>.$1>.)(2;.$1>.$1>.R11.(20.R11.R10.))R14.))R16.R15.)P,(2<.$2.R17.R16.)P,(2=.$2.R17.)(3<.$2.VAL,VCS,(3=.R3;.R20.R3:.R39.R35.R34.R2>.R2=.R2<.R2;.R2:.R29.R28.R27.R26.R25.R1;.R1:.R14.R13.R1=.R1<.R17.R19.)(25.(26.R3;.(7.&40.(20.R20.-40.))R3:.R39.R38.R37.R36.R35.R34.(7.&40.R1?.)(7.&40.R1>.)(7.&40.R1=.)R33.R32.R31.R30.R2?.R2>.R2=.R2<.R2;.R2:.R29.R28.R27.R26.R25.R24.R23.R22.R21.)R1;.(7.&40.+6:590.)R1:.(28.(1:.&40.))R18.(29.$2.)))")
(* [comment removed for export] *).
  Proof.
    intros ra gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 SP A n v lo F fc m0 m W junk fr S k
      AAL NAL NPOS VB RNG ACS SH PS FR ST LOIMG SPL SPH SPA SCS MU WM MI.
    flat constr:(PS) 13%nat. intros CP G1 SB G2 MB G3 ME G4 HE G5 RM G6 CT.
    unfold A_POISON, A_CANPOISON, A_GOT_SB, A_SBCELL, A_GOT_MIDBEG, A_MIDBEG, A_GOT_MIDEND, A_MIDEND, A_GOT_HIGHEND, A_HIGHEND,
      A_GOT_RMEMSET, A_RMEMSET, A_GOT_CFLAGS, A_CFLAGS, A_CF_CSMT, A_MUSL_MEMSET in *.
    assert (HS : S = 0x7fff8000 + A / 8) by reflexivity. assert (HK : k = n / 8) by reflexivity. clearbody S k.
    assert (AB : 8 <= A <= 2^47 - 8 /\ A + n <= 2^47) by (clear - RNG NPOS; lia). flat constr:(AB) 2%nat. flclear AB. intros (A8 & AHI) AN.
    pose proof RNG as RNG0.
    pose proof (conj MU (conj WM (conj SH (conj PS RNG0))) : id (munch ((lo, SP) :: (S, S + k) :: W) m0 m /\ wmono asegs m0 m
                  /\ rw_cells asegs m S [CB (Z.to_nat k) junk] /\ poison_statics m /\ _)) as MW0.
    clear MU WM SH PS RNG0. pose proof (munch_refl [(lo, SP)] m) as MU. pose proof (wmono_refl asegs m) as WM.
    (* [comment removed for export] *)
    destruct RNG as [(R1 & R2 & R3)|(R1 & R2 & R3 & R4)];
      (lx_run_tac (PLAN [0x6a78c] [] 200%N); lx_tree;
       first [
lazymatch goal with |- False =>
    repeat match goal with K : _ = true |- _ => revert K | K : _ = false |- _ => revert K end;
    clear - AAL NAL A8 AHI AN NPOS VB R1 R2 R3; intros;
    pose proof (Z.div_mod A 8 ltac:(lia)) as DA; pose proof (Z.div_mod n 8 ltac:(lia)) as DN;
    pose proof (Z.mod_pos_bound A 8 ltac:(lia)) as MA; pose proof (Z.mod_pos_bound n 8 ltac:(lia)) as MN;
    repeat match goal with
    | K : (if ?c then false else true) = true |- _ => destruct c eqn:?LXE; [discriminate K| clear K]
    | K : (if ?c then false else true) = false |- _ => destruct c eqn:?LXE; [clear K| discriminate K]
    end;
    repeat match goal with
    | K : (?a <? ?b) = true |- _ => apply Z.ltb_lt in K
    | K : (?a <? ?b) = false |- _ => apply Z.ltb_ge in K
    | K : (?a <=? ?b) = true |- _ => apply Z.leb_le in K
    | K : (?a <=? ?b) = false |- _ => apply Z.leb_gt in K
    | K : (?a =? ?b) = true |- _ => apply Z.eqb_eq in K
    | K : (?a =? ?b) = false |- _ => apply Z.eqb_neq in K
    end;
    rewrite ?Z.shiftr_div_pow2 in * by (clear; lia); change (2^3) with 8 in *; unfold zlow in *;
    change ((-1) mod 2 ^ 64) with 18446744073709551615 in *;
    rewrite ?(Z.mod_small 18446744073709551615 (2 ^ 64)) in * by (clear; lia);
    rewrite ?(Z.mod_small 0 (2 ^ 64)) in * by (clear; lia);
    repeat match goal with K : context [?e mod 2 ^ 64] |- False =>
      first [ rewrite (Z.mod_small e (2 ^ 64)) in * by (clear - AAL NAL DA DN MA MN A8 AHI AN NPOS VB; nia)
            | lazymatch goal with _ : 0 <= e mod 2 ^ 64 < 2 ^ 64 |- _ => fail | |- _ => pose proof (Z.mod_pos_bound e (2 ^ 64) ltac:(clear; lia)) end ]
    end;
    nia
end
       | lazymatch goal with MUl : munch _ m ?mx, WMl : wmono _ m _ |- evtA _ _ _ _ _ =>
           unfold id in MW0; (flat constr:(MW0) 5%nat; flclear MW0; intros MU0 WM0 SH0 PS0 RNG0); subst S k;
           eapply poison_tail; try eassumption;
           [ eapply rw_cells_transport; [exact SH0| exact MUl| exact WMl| cbn [disjoint_from cells_size csize]; pose proof aceil_bounds;
               pose proof (Z.div_mod A 8 ltac:(lia)); pose proof (Z.div_mod n 8 ltac:(lia)); clear - A8 AHI AN NPOS LOIMG SPL H H0 H1; lia]
           | eapply (poison_statics_transport _ _ _ PS0 MUl); intros; cbn [disjoint_from]; lia
           | eapply munch_trans; [exact MU0| eapply munch_weaken; [| exact MUl]; unfold sub_fp; cbn [outside]; clear; intros y Hy; lia]
           | eapply wmono_trans; [exact WM0| exact WMl] ]
         end ]).
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  Local Ltac2 Set LiaOrc.tbl := fun () => "0080?L11336952636.20L22706556426.7 L39058744283.81L42001778030.1 L44832609772.3 L54740509038.1 L61024692342.78L61028778749.7900000O00a01H01L01W01[01l02=S3hAR2SP1A1n2lo4NPOS5LOIMG4RNG0S2SP1A1n2lo1W1y2HyS3hAR2SP1A1n2lo4NPOS5LOIMG3SPL2A02n02H7S2SPS2SP2lo3SPLS2SPS3hAR2SP1A1n4NPOSS3hAR2SP1A1n4NPOS". (* [comment removed for export] *)
  Lemma poison_spec_any : ltac2:(CDefT.buildp (gd_tbl_AW_Poison ()) "Pra,(1:.&40.)Pgp,(1:.&40.)Ptp,(1:.&40.)Pt0,(1:.&40.)Pt1,(1:.&40.)Pt2,(1:.&40.)Ps0,(1:.&40.)Ps1,(1:.&40.)Pa3,(1:.&40.)Pa4,(1:.&40.)Pa5,(1:.&40.)Pa6,(1:.&40.)Pa7,(1:.&40.)Ps2,(1:.&40.)Ps3,(1:.&40.)Ps4,(1:.&40.)Ps5,(1:.&40.)Ps6,(1:.&40.)Ps7,(1:.&40.)Ps8,(1:.&40.)Ps9,(1:.&40.)Ps10,(1:.&40.)Ps11,(1:.&40.)Pt3,(1:.&40.)Pt4,(1:.&40.)Pt5,(1:.&40.)Pt6,(1:.&40.)PSP,$1>.PA,$1>.Pn,$1>.Pv,$1>.Plo,$1>.PF,(33.&5.(1:.&40.))Pfc,(1:.&20.)Pm0,P,(1:.&40.)(1;.(1:.&8.))Pm,P,(1:.&40.)(1;.(1:.&8.))PW,(18.(2:.$1>.$1>.))Pjunk,(18.(1:.&8.))ZS,$1>.(20.+7???8000.(34.R:.+8.))Zk,$1>.(34.R:.+8.)P,(24.$1>.(35.R<.+8.)=)P,(24.$1>.(35.R<.+8.)=)P,(1?.=R=.)P,(0.(1?.=R=.)(36.R=.+100.))P,(37.(0.(1?.+8.R10.)(0.(1?.R10.+7???7??8.)(1?.(20.R10.R?.)+7???8000.)))(0.(1?.+10007???8000.R10.)(0.(1?.+10007???8008.(20.R10.R?.))(0.(1?.R10.+7??????????8.)(1?.(20.R10.R?.)+800000000000.)))))P,(38.VCS,R11.R10.)P,(2>.$2.R;.R8.(4.$5.(2?.(30.R7.)R9.)(8.$5.)))P,(1<.R<.)P,(32.$2.R=.R11.R15.)P,(1?.(39.VhAR,)R12.)P,(1?.R13.(3:.R17.+40.))P,(1?.R18.(3;.+2.+3?.))P,(24.$1>.(35.R19.+10.)=)P,(38.VCS,R16.(3:.R1:.R16.))P,(1=.(4.(2:.$1>.$1>.)(2;.$1>.$1>.R17.R1;.)(4.(2:.$1>.$1>.)(2;.$1>.$1>.R10.(20.R10.R?.))R12.))R14.R13.)P,(2<.$2.R15.R14.)P,(2=.$2.R15.)(3<.$2.VAL,VCS,(3=.R39.R1>.R38.R37.R33.R32.R2<.R2;.R2:.R29.R28.R27.R26.R25.R24.R23.R19.R18.R13.R12.R1;.R1:.R15.R17.)(25.(26.R39.(7.&40.R1>.)R38.R37.R36.R35.R34.R33.R32.(7.&40.R1=.)(7.&40.R1<.)(7.&40.R1;.)R31.R30.R2?.R2>.R2=.R2<.R2;.R2:.R29.R28.R27.R26.R25.R24.R23.R22.R21.R20.R1?.)R19.(7.&40.$3>.)R18.(28.(1:.&40.))R16.(29.$2.)))")
(* [comment removed for export] *).
  Proof.
    intros ra gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 SP A n v lo F fc m0 m W junk S k
      AAL NAL NPOS VB RNG ACS SH PS ST LOIMG SPL SPH SPA SCS MU WM MI.
    flat constr:(PS) 2%nat. intros CP _. unfold A_POISON, A_CANPOISON in *.
    assert (HS : S = 0x7fff8000 + A / 8) by reflexivity. assert (HK : k = n / 8) by reflexivity. clearbody S k.
    pose proof aceil_bounds as ACB.   (* [comment removed for export] *)
    pose proof (conj MU (conj WM (conj SH (conj PS RNG))) : id (munch ((lo, SP) :: (S, S + k) :: W) m0 m /\ wmono asegs m0 m
                  /\ rw_cells asegs m S [CB (Z.to_nat k) junk] /\ poison_statics m /\ _)) as MW0.
    clear MU WM SH PS RNG. pose proof (munch_refl [(lo, SP)] m) as MU. pose proof (wmono_refl asegs m) as WM.
    (* [comment removed for export] *)
    lx_run_tac (PLAN [0x6a590] [(0x6a57c, DJoin)] 60%N); lx_tree;
         lazymatch goal with MUl : munch _ m ?mx, WMl : wmono _ m _, STl : stk _ _ lo (SP + -56), FRl : rw_cells _ _ (SP + -56) ?fcs |- evtA _ _ _ _ _ =>
           unfold id in MW0; (flat constr:(MW0) 5%nat; flclear MW0; intros MU0 WM0 SH0 PS0 RNG0); subst S k;
           destruct (stk_carve _ lxm lo (SP + -56) 8 STl ltac:(clear - SPL; lia)) as [STl2 [fr FR8]];
           replace (SP + -56 - Z.of_nat 8) with (SP + -64) in STl2, FR8 by (clear; lia);
           assert (FRl2 : rw_cells asegs lxm (SP + -64) ([CB 8 fr] ++ fcs))
             by (apply (proj2 (rw_cells_app _ _ _ _ _)); split; [exact FR8|]; cbn [cells_size csize Nat.add];
                 replace (SP + -64 + Z.of_nat 8) with (SP + -56) by (clear; lia); exact FRl);
           cbn [app] in FRl2;
           eapply poison_body; try eassumption;
           [ eapply rw_cells_transport; [exact SH0| exact MUl| exact WMl| cbn [disjoint_from cells_size csize];
               pose proof (Z.div_mod A 8 ltac:(lia)); pose proof (Z.div_mod n 8 ltac:(lia)); clear - RNG0 NPOS LOIMG SPL ACB H H0; lia]
           | eapply (poison_statics_transport _ _ _ PS0 MUl); intros; cbn [disjoint_from]; lia
           | eapply munch_trans; [exact MU0| eapply munch_weaken; [| exact MUl]; unfold sub_fp; cbn [outside]; clear; intros y Hy; lia]
           | eapply wmono_trans; [exact WM0| exact WMl] ]
         end.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Lemma poison_spec : ltac2:(CDefT.buildp (gd_tbl_AW_Poison ()) "Pra,(1:.&40.)Pgp,(1:.&40.)Ptp,(1:.&40.)Pt0,(1:.&40.)Pt1,(1:.&40.)Pt2,(1:.&40.)Ps0,(1:.&40.)Ps1,(1:.&40.)Pa3,(1:.&40.)Pa4,(1:.&40.)Pa5,(1:.&40.)Pa6,(1:.&40.)Pa7,(1:.&40.)Ps2,(1:.&40.)Ps3,(1:.&40.)Ps4,(1:.&40.)Ps5,(1:.&40.)Ps6,(1:.&40.)Ps7,(1:.&40.)Ps8,(1:.&40.)Ps9,(1:.&40.)Ps10,(1:.&40.)Ps11,(1:.&40.)Pt3,(1:.&40.)Pt4,(1:.&40.)Pt5,(1:.&40.)Pt6,(1:.&40.)PSP,$1>.PA,$1>.Pn,$1>.Pv,$1>.Plo,$1>.PF,(33.&5.(1:.&40.))Pfc,(1:.&20.)Pm0,P,(1:.&40.)(1;.(1:.&8.))Pm,P,(1:.&40.)(1;.(1:.&8.))PW,(18.(2:.$1>.$1>.))Pjunk,(18.(1:.&8.))ZS,$1>.(20.+7???8000.(34.R:.+8.))Zk,$1>.(34.R:.+8.)P,(24.$1>.(35.R<.+8.)=)P,(24.$1>.(35.R<.+8.)=)P,(1?.=R=.)P,(0.(1?.=R=.)(36.R=.+100.))P,(37.(0.(1?.+8.R10.)(0.(1?.R10.+7???7??8.)(1?.(20.R10.R?.)+7???8000.)))(0.(1?.+10007???8000.R10.)(0.(1?.+10007???8008.(20.R10.R?.))(0.(1?.R10.+7??????????8.)(1?.(20.R10.R?.)+800000000000.)))))P,(37.(3?.(24.$1>.R?.=))(36.R6.+10000.))P,(38.VCS,R12.R11.)P,(2>.$2.R<.R9.(4.$5.(2?.(30.R8.)R:.)(8.$5.)))P,(1<.R=.)P,(32.$2.R>.R12.R16.)P,(1?.(39.VhAR,)R13.)P,(1?.R14.(3:.R18.+40.))P,(1?.R19.(3;.+2.+3?.))P,(24.$1>.(35.R1:.+10.)=)P,(38.VCS,R17.(3:.R1;.R17.))P,(1=.(4.(2:.$1>.$1>.)(2;.$1>.$1>.R18.R1<.)(4.(2:.$1>.$1>.)(2;.$1>.$1>.R11.(20.R11.R10.))R13.))R15.R14.)P,(2<.$2.R16.R15.)P,(2=.$2.R16.)(3<.$2.VAL,VCS,(3=.R3:.R1?.R39.R38.R34.R33.R2=.R2<.R2;.R2:.R29.R28.R27.R26.R25.R24.R1:.R19.R14.R13.R1<.R1;.R16.R18.)(25.(26.R3:.(7.&40.R1?.)R39.R38.R37.R36.R35.R34.R33.(7.&40.R1>.)(7.&40.R1=.)(7.&40.R1<.)R32.R31.R30.R2?.R2>.R2=.R2<.R2;.R2:.R29.R28.R27.R26.R25.R24.R23.R22.R21.R20.)R1:.(7.&40.$3>.)R19.(28.(1:.&40.))R17.(29.$2.)))")
(* [comment removed for export] *).
  Proof.
    intros ra gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 SP A n v lo F fc m0 m W junk S k
      AAL NAL NPOS VB RNG _ ACS SH PS ST LOIMG SPL SPH SPA SCS MU WM MI.
    eapply poison_spec_any; eassumption.
  Qed.
End Poison.

End ARUN_1.
