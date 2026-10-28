(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Arr Asn1Aux CellsX.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import AModel.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import AW_Unwind AW_Unwind2 AW_MmapFixed AW_MallocA.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import AW_IMemset AW_IAInit AW_Dealloc.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BLX Require Import LxA.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LXBW Require Import LxAWTac.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import ATac.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.AHeap Require Import ACeil.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Import OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.LxhSyntax. #[local] Instance lxh_tab : OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.lx_hints := OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.lxh_parse "P00a9472a30c816dd 1 1 16 2 1 1 49 1 5 39 1 41 1 42 1 50 1 51 16P01b496ebf7c07a8f 1 1 16 2 1 1 49 1 5 39 1 41 1 42 1 50 1 51 16P02f211b479f59fd3 1 2 16 2 0 1 50 1 16 2 1 1 49 1 2 51 1 52 1P0490efdf06c3b206 0 2 0 1 10 1P04d3bc0f13ad207a 1 1 16 2 1 1 49 1 5 39 1 41 1 42 1 50 1 51 16P057eed2f24e7a269 1 1 16 2 1 1 45 1 5 37 1 41 1 42 1 46 1 47 16P06ee8c3f9585a7c5 0 4 0 1 40 1 44 1 45 1P079f844153e5a10b 1 2 16 2 0 1 50 1 16 2 1 1 49 1 2 51 1 52 1P07aeb32582068b5f 1 1 16 2 1 1 49 1 5 39 1 41 1 42 1 50 1 51 16P088625b7cb741885 0 2 0 1 10 1P08d647531bdf1b3f 0 4 0 16 40 16 48 16 49 16P096d79e68ba62db1 1 2 16 2 0 1 50 1 16 2 1 1 49 1 2 51 1 52 1P09ff2704045d58d9 1 2 16 2 0 1 50 1 16 2 1 1 49 1 2 51 1 52 1P0b17a7d826b655bc 0 4 0 16 40 16 48 16 49 16P0c350418b42aa0ae 0 4 0 16 40 16 48 16 49 16P0dd67686d79a755b 1 1 16 2 1 1 49 1 5 39 1 41 1 42 1 50 1 51 16P0eed9160940211f7 0 6 1 16 39 16 41 16 42 16 49 16 50 16P0f04730ac9653a14 0 4 0 16 40 16 48 16 49 16P0f39ab5fcc70b533 1 1 16 2 1 1 45 1 5 37 1 41 1 42 1 46 1 47 16P0fe92bc80b8b53eb 1 1 16 2 1 1 49 1 5 39 1 41 1 42 1 50 1 51 16P1023b7e811c7bcf3 1 2 16 2 0 1 50 1 16 2 1 1 49 1 2 51 1 52 1P11c8a44cecc1e7af 0 4 0 16 40 16 48 16 49 16P12eee8f6a3ce44a1 1 1 16 2 1 1 49 1 5 39 1 41 1 42 1 50 1 51 16P1328e9d31ec6df54 1 2 16 2 0 1 46 1 16 2 1 1 45 1 2 47 1 48 1P13350830f4ad2cfe 1 1 16 2 1 1 49 1 5 39 1 41 1 42 1 50 1 51 16P1398a408ef20181e 0 4 0 16 40 16 48 16 49 16P13a9c74d277f74d1 1 2 16 2 0 1 50 1 16 2 1 1 49 1 2 51 1 52 1P1435e9177ba4db0e 0 4 0 16 40 16 48 16 49 16P144b7302cd8a8342 0 4 0 16 40 16 48 16 49 16P153da66f25acef0f 1 2 16 2 0 1 50 1 16 2 1 1 49 1 2 51 1 52 1P1666fdf3e78d0ce7 0 4 0 16 40 16 48 16 49 16P17001b3402678445 1 1 16 2 1 1 49 1 5 39 1 41 1 42 1 50 1 51 16P17a10c650279c113 0 2 0 1 10 1P17d2172b362c3ed7 1 2 16 2 0 1 50 1 16 2 1 1 49 1 2 51 1 52 1P17d91745ff345886 1 2 16 2 0 1 50 1 16 2 1 1 49 1 2 51 1 52 1P18819ed767bc4080 1 1 16 2 1 1 45 1 5 37 1 41 1 42 1 46 1 47 16P18f648352e573c69 1 2 16 2 0 1 50 1 16 2 1 1 49 1 2 51 1 52 1P1908fdab67dbcbce 0 4 0 16 40 16 48 16 49 16P1a0c9aedbe1f98e2 0 4 0 16 40 16 48 16 49 16P1a1fa226fede3802 1 2 16 2 0 1 46 1 16 2 1 1 45 1 2 47 1 48 1P1a4ca7e185be5c62 1 1 16 2 1 1 49 1 5 39 1 41 1 42 1 50 1 51 16P1c541b4a52da81ce 1 2 16 2 0 1 50 1 16 2 1 1 49 1 2 51 1 52 1P1c862b057eb674c2 0 2 0 1 10 1P1cffb59c13abb31f 0 6 1 16 39 16 41 16 42 16 49 16 50 16P1d01f603592cbea7 1 2 16 2 0 1 50 1 16 2 1 1 49 1 2 51 1 52 1P1e463cf33f3d2cf2 0 4 0 16 40 16 48 16 49 16P1f77ba0d6ca62e4f 0 4 0 1 40 1 44 1 45 1P2118c4654ce55c25 0 2 0 1 10 1P213203c7d95c94e1 1 1 16 2 1 1 49 1 5 39 1 41 1 42 1 50 1 51 16P218c89800df7b04f 0 4 0 1 40 1 44 1 45 1P21a4b2295e04abac 1 2 16 2 0 1 50 1 16 2 1 1 49 1 2 51 1 52 1P21cb66caf60ca718 1 1 16 2 1 1 45 1 5 37 1 41 1 42 1 46 1 47 16P2216efb9df6a1e33 0 4 0 16 40 16 48 16 49 16P2263b8ce220a418b 0 4 0 1 40 1 44 1 45 1P234c4088a8a043ff 1 2 16 2 0 1 46 1 16 2 1 1 45 1 2 47 1 48 1P2418ccc80f88af99 0 4 0 1 40 1 44 1 45 1P25ae7a4e1482cef0 1 1 16 2 1 1 49 1 5 39 1 41 1 42 1 50 1 51 16P263997365295d8de 1 2 16 2 0 1 46 1 16 2 1 1 45 1 2 47 1 48 1P266c327a837b45a2 0 4 0 16 40 16 48 16 49 16P26dff5806fc24bfa 0 4 0 16 40 16 48 16 49 16P2708e3b3b672113f 0 4 0 1 40 1 44 1 45 1P271f0f2b78913d6b 1 1 16 2 1 1 49 1 5 39 1 41 1 42 1 50 1 51 16P2824fcf965ac9b65 1 2 16 2 0 1 50 1 16 2 1 1 49 1 2 51 1 52 1P286c958292a3e1fb 0 4 0 16 40 16 48 16 49 16P28713ca6e40f376c 0 4 0 16 40 16 48 16 49 16P287f1ca1e5786d97 0 2 0 1 10 1P29058f0f5ddfb2c7 1 1 16 2 1 1 49 1 5 39 1 41 1 42 1 50 1 51 16P29345b1d47bca18d 1 2 16 2 0 1 50 1 16 2 1 1 49 1 2 51 1 52 1P2960dc1bb203696d 0 4 0 16 40 16 48 16 49 16P29635a506a768c1e 1 1 16 2 1 1 49 1 5 39 1 41 1 42 1 50 1 51 16P2ab1142fd3241a90 1 1 16 2 1 1 49 1 5 39 1 41 1 42 1 50 1 51 16P2abf9f5b2ac4f88a 1 1 16 2 1 1 45 1 5 37 1 41 1 42 1 46 1 47 16P2b3b23da43f85cfc 0 4 0 1 40 1 44 1 45 1P2b9f6bb35b2a894a 1 2 16 2 0 1 50 1 16 2 1 1 49 1 2 51 1 52 1P2baa722dda18fa46 0 4 0 16 40 16 48 16 49 16P2bccdc02196c285c 1 2 16 2 0 1 46 1 16 2 1 1 45 1 2 47 1 48 1P2ca918bfa1b33451 1 2 16 2 0 1 50 1 16 2 1 1 49 1 2 51 1 52 1P2d9d93b7f4df437f 1 1 16 2 1 1 49 1 5 39 1 41 1 42 1 50 1 51 16P2da7963a7e7056be 1 1 16 2 1 1 45 1 5 37 1 41 1 42 1 46 1 47 16P2e2c108189046c1e 0 2 0 1 10 1P2efbc4cb4433a704 0 6 1 16 39 16 41 16 42 16 49 16 50 16P2f2f15479db6aa54 0 2 0 1 10 1P2fa6229bc7024092 1 1 16 2 1 1 49 1 5 39 1 41 1 42 1 50 1 51 16P2fb4d4e27a7d62e6 1 1 16 2 1 1 49 1 5 39 1 41 1 42 1 50 1 51 16P300eda3f5636ca18 1 1 16 2 1 1 49 1 5 39 1 41 1 42 1 50 1 51 16P305d8f74d5609e70 1 1 16 2 1 1 49 1 5 39 1 41 1 42 1 50 1 51 16P30d9de3109ec3ef4 1 2 16 2 0 1 50 1 16 2 1 1 49 1 2 51 1 52 1P30f67a5fa9d27df9 1 2 16 2 0 1 50 1 16 2 1 1 49 1 2 51 1 52 1P32c57ab013855948 1 1 16 2 1 1 49 1 5 39 1 41 1 42 1 50 1 51 16P32d1d4029697aed5 1 2 16 2 0 1 46 1 16 2 1 1 45 1 2 47 1 48 1P3376d28bd1a065ad 1 1 16 2 1 1 45 1 5 37 1 41 1 42 1 46 1 47 16P36a6d0a7e29ccbfe 1 2 16 2 0 1 46 1 16 2 1 1 45 1 2 47 1 48 1P3741969899573724 1 2 16 2 0 1 50 1 16 2 1 1 49 1 2 51 1 52 1P3809d58f837ac0cc 0 2 0 1 10 1P3825b414164f1012 1 2 16 2 0 1 50 1 16 2 1 1 49 1 2 51 1 52 1P38fce7aa7dd948d9 0 4 0 1 40 1 44 1 45 1P3a37267b27a96dfd 1 1 16 2 1 1 49 1 5 39 1 41 1 42 1 50 1 51 16P3aae6975209cffb6 1 1 16 2 1 1 49 1 5 39 1 41 1 42 1 50 1 51 16P3abd1b0fc00a2fe5 1 1 16 2 1 1 49 1 5 39 1 41 1 42 1 50 1 51 16P3b8bfe4bbbf4cb69 1 1 16 2 1 1 49 1 5 39 1 41 1 42 1 50 1 51 16P3b9cc77bd32fbb0e 1 2 16 2 0 1 50 1 16 2 1 1 49 1 2 51 1 52 1P3bfc0f6fa719b213 0 4 0 16 40 16 48 16 49 16P3c4172c585a2d9f1 1 2 16 2 0 1 46 1 16 2 1 1 45 1 2 47 1 48 1P3f38f7a458daca53 0 4 0 16 40 16 48 16 49 16"%lxh.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import LiaOrc. (* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= orc_lia. (* [comment removed for export] *)
Local Ltac dlia ::= orc_dlia. (* [comment removed for export] *)
Local Ltac plia ::= orc_plia. (* [comment removed for export] *)
Local Ltac clear_disj ::= fc_clear_disj. (* [comment removed for export] *)
Local Ltac prune_disj ::= fc_prune_disj. (* [comment removed for export] *)
Ltac2 gd_tbl_AW_FreeA () : Init.string Init.list := ["stdpp.bitvector.definitions.bv"; "Corelib.Init.Datatypes.option"; "Corelib.Numbers.BinNums.Z"; "RocqVerifyHarness.AgentSubmission.Lib.Step.rw_cells"; "RocqVerifyHarness.AgentSubmission.B.AImg.asegs"; "Corelib.Init.Datatypes.cons"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.cell"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.CB"; "Stdlib.ZArith.BinInt.Z.to_nat"; "Corelib.Lists.ListDef.repeat"; "stdpp.bitvector.definitions.Z_to_bv"; "Corelib.Init.Datatypes.nil"; "Stdlib.ZArith.BinInt.Z.le"; "Stdlib.ZArith.BinInt.Z.add"; "Corelib.Init.Logic.eq"; "Corelib.Init.Datatypes.list"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.ov_read_bytes"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.wa"; "Corelib.Init.Datatypes.Some"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.le8"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.machine_state"; "Corelib.Init.Logic.ex"; "Corelib.Init.Logic.and"; "RocqVerifyHarness.AgentSubmission.Lib.MState.MS"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.mkR"; "ARUN_1.A_FREE_RA1"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.A_PC_FREE"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_Unwind2.A_UNWIND_IMPL"; "Corelib.Init.Datatypes.None"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.seg_rom"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.munch"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_IAInit.ia_W"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.wmono"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.mem_inv"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C8"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C4"; "RocqVerifyHarness.AgentSubmission.Lib.Arr.u64arr"; "Corelib.Init.Datatypes.nat"; "Corelib.Init.Datatypes.length"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.stk"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_IAInit.ia_cells"; "LinuxProcessSemantics.Riscv.Prelude.bvmap"; "Stdlib.ZArith.BinInt.Z.pow"; "RocqVerifyHarness.AgentSubmission.LibA.AEvtA.evtA"; "ARUN_1.A_FREE_RA2"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_Dealloc.A_ASAN_FREE"; "Corelib.Init.Datatypes.prod"; "Stdlib.ZArith.BinInt.Z.of_nat"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.cells_size"; "Stdlib.ZArith.BinInt.Z.sub"; "Corelib.Init.Datatypes.pair"; "RocqVerifyHarness.AgentSubmission.LibA.ALazy.crange"; "RocqVerifyHarness.AgentSubmission.Lib.MState.ret_pc"].

Section ARUN_1. Context {hAR : arun}.
Definition A_FREE : Z := 0x69488.            (* [comment removed for export] *) (* [comment removed for export] *)
(* [comment removed for export] *)
Definition A_FREE_RA1 : Z := 0x6961c.        (* [comment removed for export] *) (* [comment removed for export] *)
Definition A_FREE_RA2 : Z := 0x69630.        (* [comment removed for export] *) (* [comment removed for export] *)

(* [comment removed for export] *)
#[using="Type"] Lemma skipn_repeat : forall {X} (x : X) k n, skipn k (repeat x n) = repeat x (n - k).
Proof.
  intros X x k. induction k as [|k IH]; intros [|n]; cbn; try reflexivity. rewrite IH. reflexivity.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "0020>L30156944664.6L7733768704.7 00000900@S1X1x1k1HS1k1n1H". (* [comment removed for export] *)
#[using="Type"] Lemma firstn_repeat : forall {X} (x : X) k n, (k <= n)%nat -> firstn k (repeat x n) = repeat x k.
Proof.
  intros X x k. induction k as [|k IH]; intros [|n] H; cbn; try reflexivity; [lia|]. rewrite IH by lia. reflexivity.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

(* [comment removed for export] *)
Local Ltac2 Set LiaOrc.tbl := fun () => "0020>L25990927484.8L55419484459.800000;00FS1N1k2Hk2HNS1N1k2Hk2HN". (* [comment removed for export] *)
#[using="Type"] Lemma zeros_read8 : ltac2:(CDefT.buildp (gd_tbl_AW_FreeA ()) "Pm,P,(0.&40.)(1.(0.&8.))PA,$2.PN,$2.Pk,$2.P,(3.$4.R4.R3.(5.$6.(7.(8.R2.)(9.(0.&8.)(:.&8.=)(8.R2.)))(;.$6.)))P,(<.=R2.)P,(<.(=.R3.+8.)R4.)(>.(1.(?.(0.&8.)))(10.$4.R7.(11.(=.R6.R4.))#8.)(12.(?.(0.&8.))(13.(:.&40.=))))")
(* [comment removed for export] *).
Proof.
  intros m A N k [[_ HB] _] Hk HN. cbn [cells_bytes cbytes] in HB. rewrite app_nil_r in HB.
  rewrite (bytes_at_read asegs m A _ k 8 HB Hk) by (rewrite repeat_length; lia).
  rewrite skipn_repeat, firstn_repeat by lia. reflexivity.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

Section FreeA.
  Variable AL : asan_layout.
  Hypothesis IMG : asan_img_ok AL.
  Hypothesis ALWF : al_wf AL.
  Variable CS : Z -> Prop.
  Hypothesis CSOK : cs_ok AL CS.
  Local Instance lxi : LxImg asegs AL := lxA_img AL IMG.   (* [comment removed for export] *)

  Ltac facts :=
    pose proof (cs_ok_sb _ _ CSOK) as SB64;
    pose proof ALWF as ALWF'; unfold al_wf in ALWF';
    pose proof IMG as IMG'; unfold asan_img_ok in IMG'.

  (* [comment removed for export] *)
  Definition fpro_post (SP : Z) (gp tp t0 t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 a7 t3 t4 t5 t6 ra : word) (p lo : Z)
      (F : bvmap 5 word) (fc : bv 32) (m0 : mem) : machine_state -> Prop := ltac2:(CDefT.buildp (gd_tbl_AW_FreeA ()) "Lms',$14.(15.(0.&40.)La6,(0.&40.)(15.P,(0.&40.)(1.(0.&8.))Lm',P,(0.&40.)(1.(0.&8.))(15.(?.(0.&40.))Lws,(?.(0.&40.))(15.(?.(0.&8.))Lfr1,(?.(0.&8.))(15.(?.(0.&8.))Lfr2,(?.(0.&8.))ZSTK,$2.(=.O1=.-850.)(16.(>.$14.R7.(17.(18.(:.&40.$19.)(:.&40.R1.)O1<.O1;.O1:.O19.O18.(:.&40.O1=.)(:.&40.O5.)(:.&40.R1.)(:.&40.$1:.)(:.&40.O1=.)(:.&40.=)(:.&40.+1.)(:.&40.+1>.)R6.O;.(:.&40.$1:.)(:.&40.+1.)(:.&40.R1.)(:.&40.(=.O1=.-51.))O11.O10.O?.O>.O=.O<.O:.O9.O8.O7.)O3.(:.&40.$1;.)O2.(1<.(0.&40.))R5.(1=.$4.)))(16.(1>.(1?.O4.O1=.)O1.R5.)(16.(20.$4.O1.R5.)(16.(21.$4.R5.)(16.(3.$4.R5.(=.O1=.-38.)(5.$6.(22.O12.)(5.$6.(22.O13.)(5.$6.(22.O14.)(5.$6.(22.O15.)(5.$6.(22.O16.)(5.$6.(22.O17.)(5.$6.(22.O6.)(;.$6.)))))))))(16.(3.$4.R5.R1.(5.$6.(22.(:.&40.(=.R1.+10.)))(5.$6.(23.(:.&40.=))(5.$6.(23.(:.&40.=))(;.$6.)))))(16.(24.$4.R5.(=.R1.+10.)R4.)(16.(>.$25.(26.(0.&40.)R4.)#1>.)(16.(3.$4.R5.(=.R1.+100.)(5.$6.(7.#708.R3.)(;.$6.)))(16.(3.$4.R5.(=.R1.+808.)(5.$6.(22.(:.&40.O1=.))(;.$6.)))(16.(3.$4.R5.(=.R1.+810.)(5.$6.(7.#8.R2.)(;.$6.)))(16.(27.$4.R5.O4.R1.)(28.R5.))))))))))))))))))")
(* [comment removed for export] *).

  Local Ltac2 Set LiaOrc.tbl := fun () => "00b0?L10787298087.1 L12169703032.85L13682242252.2 L15332577811.85L16547350677.1 L18928466588.2 L18928876188.83L21670249189.57L21674908290.6 L25859088801.0 L27349425973.2 L28621413992.83L30262258614.85L31164150825.82L31165788864.83L3171562214.2  L31751970783.2 L35078220389.57L35389780230.70L38692635477.0 L38868635973.0 L39188636933.0 L4113131604.2  L42155231742.3 L42433597087.1 L43590398174.83L43718431911.1 L45817977432.85L46993493634.85L47463205488.2 L47495980376.85L49033555447.83L50758311832.1 L51052448024.1 L52968078741.1 L53522260663.83L53703502631.1 L55278381275.3 L55588686165.0 L55594025368.1 L56333148118.2 L56451385240.85L58019137107.3 L63116769125.57L63612251646.1 L65115300033.83L66566366137.92L67789986904.85L8423161990.70 L8806430988.86 00000400E00K00L00P00Q00[01<01M01N01V01`02502B02O02U02[03<03X03Y03Z03[03a03o04304E04I04Z04[04a05205G05K05O05S05c05g06206306706?06P06[07<07?07@07\07m08I08ZS2SPS3hAR2SP2lo5LOIMGS1p2KBFS2SPSS3hAR2SP1pS3hAR2SP2lo3cs23cs43cs53SZ55LOIMGS3hAR2SP2lo5LOIMGSS2SP3SPAS3hAR1p2PBS3hAR2SP2lo5LOIMG3SPLS3hAR2SP1p2PBS3hAR2SP1p2PBS1p2KBS1p2PBS3hAR2SP2lo3cs23cs43cs53SZ45LOIMGS3hAR2SP1p2lo2PB5LOIMG2ws2HLSSSS1p2PBS3hAR2lo5LOIMGS2SPS3hAR2AL1p2PB4IMG'S2SPS3hAR2SP2lo5LOIMGFS1p2PBS3hAR2SP2lo5LOIMGS3hAR2AL1p2PB4IMG'2KBS2SPS2SPS2SPS3hAR2AL1p5ALWF'S2SPS2SP2lo3SPLSS2SPS2SP3SPHS3hAR2SP2lo5LOIMGS2SP2lo3SPLS3hAR2SP2lo3cs23cs43cs53SZ25LOIMGS1pFS3hAR2SP2lo3cs23cs43cs51x2H1S3hAR2SP2lo5LOIMGS3hAR2SP1p2lo2PB5LOIMG2ws2HLS3hAR2SP2lo2x62H1". (* [comment removed for export] *)
  #[using="IMG ALWF CSOK"] Lemma free_pro : forall (ia : bool)
      (ra gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (SP p lo : Z) (F : bvmap 5 word) (fc : bv 32) (m : mem) (cs2 cs4 cs5 : list cell) (p0 p1 : word),
      0 <= p < 2^47 ->
      (* [comment removed for export] *)
      rw_cells asegs m A_IA_INIT [C1 (Z_to_bv 8 (if ia then 1 else 0)); C1 (Z_to_bv 8 0); C2 (Z_to_bv 64 0)] ->
      rw_cells asegs m A_IA [C1 (Z_to_bv 8 0)] ->
      rw_cells asegs m (A_IA + 8) [CB (Z.to_nat 0x40000) (repeat (Z_to_bv 8 0) (Z.to_nat 0x40000))] ->
      rw_cells asegs m (A_IA + 0x40040) cs2 -> Z.of_nat (cells_size cs2) = 0xd80 ->
      rw_cells asegs m (A_IA + 0x40dc0) [C8 p0; C8 p1] ->
      (ia = true -> p0 = Z_to_bv 64 4096 /\ p1 = Z_to_bv 64 (A_IA + 0x40dd0)) ->
      rw_cells asegs m (A_IA + 0x40dd0) cs4 -> Z.of_nat (cells_size cs4) = 0x40248 - 16 ->
      rw_cells asegs m (A_IA + 0x81008) cs5 -> Z.of_nat (cells_size cs5) = 40 ->
      (* [comment removed for export] *)
      ro_cells asegs m A_GOT_PAGESZ [C8 (Z_to_bv 64 A_PAGESZ_CELL)] ->
      ro_cells asegs m A_PAGESZ_CELL [C8 (Z_to_bv 64 4096)] ->
      ro_cells asegs m A_MCS_CELL [C4 (Z_to_bv 64 30)] ->
      ro_cells asegs m A_GOT_CFLAGS [C8 (Z_to_bv 64 A_CFLAGS)] ->
      ro_cells asegs m A_CF_FASTUNW [C1 (Z_to_bv 8 1)] ->
      stk asegs m lo SP -> ACEIL <= lo -> lo <= SP - 4096 -> SP <= 2^62 -> SP mod 16 = 0 ->
      crange CS lo (SP - lo) -> mem_inv asegs m ->
      evtA asegs AL CS (fpro_post SP gp tp t0 t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 a7 t3 t4 t5 t6 ra p lo F fc m)
        (MS (mkR ra (Z_to_bv 64 SP) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 p) a1 a2 a3 a4 a5 a6 a7
                s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 A_FREE) fc None m (seg_rom asegs)).
  Proof.
    intros ia ra gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 SP p lo F fc m cs2 cs4 cs5 p0 p1
      PB IAW IA0 IA1 IA2 SZ2 IA3 HP IA4 SZ4 IA5 SZ5 GOT PGS MCS GOTF FU ST LOIMG SPL SPH SPA SCS MI.
    facts.
    unfold A_FREE, A_MCS_CELL, A_GOT_CFLAGS, A_CFLAGS, A_CF_FASTUNW, A_PC_FREE, A_FREE_RA1, A_UNWIND_IMPL,
      A_IA, A_IA_INIT, A_GOT_PAGESZ, A_PAGESZ_CELL in *.
    change (1676424 + 4) with 1676428 in *. change (1092608 + 1) with 1092609 in *.
    change (1092608 + 8 + 262144) with 1354760 in *. change (1092608 + 8) with 1092616 in *.
    change (1092608 + 262208 + 3456) with 1358272 in *. change (1092608 + 262208) with 1354816 in *.
    change (1092608 + 265664 + 262728) with 1621000 in *. change (1092608 + 265664) with 1358272 in *.
    change (1092608 + 528392 + 40) with 1621040 in *. change (1092608 + 528392) with 1621000 in *.
    change (1092608 + 265680) with 1358288 in *.
    (* [comment removed for export] *)
    pose proof (izeros_i _ _ 262144 IA1) as ZB1. clear IA1.
    pose proof (munch_refl [(lo, SP)] m) as MUp. pose proof (wmono_refl asegs m) as WM.
    lx_aceil.
    lx_run_tac (PLAN [0x74e44] [] 40%N); lx_tree.
    lazymatch goal with MUl : munch _ m ?mx, WMl : wmono _ m _, STl : stk _ _ lo (SP + -56) |- _ =>
      destruct (stk_split _ mx lo (SP + -2128) (SP + -56) STl ltac:(clear -SPL; lia)) as [ST0 SThi]; clear STl;
      pose proof (izeros_e _ _ _ (izeros_transport _ _ _ _ _ ZB1 ltac:(clear; lia) MUl WMl ltac:(cbn [disjoint_from]; clear -LOIMG SPL H; lia))) as IA1;
      assert (IA2' : rw_cells asegs mx 1354816 cs2) by (lx_tr_rw IA2 MUl WMl);
      assert (IA4' : rw_cells asegs mx 1358288 cs4) by (lx_tr_rw IA4 MUl WMl);
      assert (IA5' : rw_cells asegs mx 1621000 cs5) by (lx_tr_rw IA5 MUl WMl);
      assert (MU : munch [(lo, SP); (1676424, 1676428); (1092608, 1092609); (1092616, 1354760);
                            (1354816, 1358272); (1358272, 1621000); (1621000, 1621040)] m mx) by (eapply munch_weaken; [| exact MUl]; lx_subfp);
      clear ZB1 IA2 IA4 IA5 MUl; rename WMl into WM0;
      eapply evtA_cut; [ eapply (ia_init_spec AL IMG ALWF CS CSOK ia) with (lo := lo);
            [eassumption| eassumption| exact IA1| exact IA2'| exact SZ2| eassumption| exact HP| exact IA4'| exact SZ4| exact IA5'| exact SZ5
            | eassumption| eassumption| exact ST0
            | clear -LOIMG; lia| clear -SPL; lia| clear -SPH; lia| clear -SPA; lia
            | unfold crange in *; intros; apply SCS; lia| eassumption] |];
      clear IAW IA0 IA1 IA2' SZ2 IA3 HP IA4' SZ4 IA5' SZ5 GOT PGS
    end.
    (* [comment removed for export] *)
    cbv beta. intros ms1 PO. unfold ia_W, A_IA, A_IA_INIT in PO.
    change (1676424 + 4) with 1676428 in PO. change (1092608 + 1) with 1092609 in PO.
    change (1092608 + 8 + 262144) with 1354760 in PO. change (1092608 + 8) with 1092616 in PO.
    change (1092608 + 262208 + 3456) with 1358272 in PO. change (1092608 + 262208) with 1354816 in PO.
    change (1092608 + 265664 + 262728) with 1621000 in PO. change (1092608 + 265664) with 1358272 in PO.
    change (1092608 + 528392 + 40) with 1621040 in PO. change (1092608 + 528392) with 1621000 in PO.
    change (1092608 + 265680) with 1358288 in PO.
    revert ms1 PO.
    lazymatch goal with MUx : munch _ m ?mx |- forall ms', _ -> evtA ?segs _ _ _ _ => post_callA segs mx end.
    clear ST MCS GOTF FU MI. match goal with H : stk _ _ lo (SP + -2128) |- _ => rename H into ST end.
    match goal with H : ia_cells _ |- _ => rename H into IAC end.
    destruct (ia_cells_open _ IAC) as (cs2' & cs4' & cs5' & _ & _ & IA1' & _). unfold A_IA in *. change (1092608 + 8) with 1092616 in IA1'.
    lazymatch goal with |- evtA _ _ _ _ (MS _ _ _ _ _ ?mx _) => pose proof (munch_refl [(lo, SP)] mx) as MUi; pose proof (wmono_refl asegs mx) as WMi end.
    (* [comment removed for export] *)
    zstep. rewrite (Z.shiftr_div_pow2 p 47) by (clear; lia). rewrite (Z.div_small p (2^47)) by (clear -PB; lia).
    zstep.
    zstep. rewrite (Z.shiftr_div_pow2 p 32) by (clear; lia). change (2^32) with 4294967296.
    assert (KB : 0 <= p / 4294967296 < 32768).
    { clear -PB. split; [apply Z.div_pos; lia| apply Z.div_lt_upper_bound; lia]. }
    zstep. rewrite (Z.shiftl_mul_pow2 (p / 4294967296) 3) by (clear; lia). change (2^3) with 8.
    zstep.
    pose proof (zeros_read8 _ 1092616 262144 (8 * (p / 4294967296)) IA1' ltac:(clear -KB; lia) ltac:(clear -KB; lia)) as RD.
    replace (1092616 + 8 * (p / 4294967296)) with (1092608 + p / 4294967296 * 8 + 8) in RD by (clear; lia).
    zstep. clear RD IA1'. zstep. zstep.
    (* [comment removed for export] *)
    match goal with K : munch _ m ?mx, K' : wmono _ m ?mx' |- _ => lx_hide K; lx_hide K' end.
    lx_run (PLAN [0x71360] [] 80%N). lx_unhide.
    apply evtA_done. unfold fpro_post. cbv zeta. unfold ia_W, A_IA, A_IA_INIT, A_PC_FREE, A_FREE_RA1, A_UNWIND_IMPL.
    change (1676424 + 4) with 1676428. change (1092608 + 1) with 1092609.
    change (1092608 + 8 + 262144) with 1354760. change (1092608 + 8) with 1092616.
    change (1092608 + 262208 + 3456) with 1358272. change (1092608 + 262208) with 1354816.
    change (1092608 + 265664 + 262728) with 1621000. change (1092608 + 265664) with 1358272.
    change (1092608 + 528392 + 40) with 1621040. change (1092608 + 528392) with 1621000.
    change (1092608 + 265680) with 1358288.
    lazymatch goal with |- context [MS _ _ _ _ _ ?mx _] =>
      match goal with ST1 : stk _ mx (SP + -2112) (SP + -72), ST2 : stk _ mx (SP + -64) (SP + -56), STl : stk _ mx lo (SP + -2128),
                      MUl : munch _ ?mi mx, WMl : wmono _ ?mi' mx, MU7 : munch _ m ?mi'', WM7 : wmono _ m _, IACl : ia_cells _ |- _ =>
        destruct (stk_split _ mx (SP + -2112) (SP + -1872) (SP + -72) ST1 ltac:(clear; lia)) as [STa STb];
        destruct (stk_carve _ mx _ _ 240 STa ltac:(clear; lia)) as [_ [tr FTR]];
        destruct (stk_carve _ mx _ _ 1800 STb ltac:(clear; lia)) as [_ [fr1 FR1]];
        destruct (stk_carve _ mx _ _ 8 ST2 ltac:(clear; lia)) as [_ [fr2 FR2]];
        replace (SP + -1872 - Z.of_nat 240) with (SP + -2128 + 16) in FTR by (clear; lia);
        replace (SP + -72 - Z.of_nat 1800) with (SP + -2128 + 256) in FR1 by (clear; lia);
        replace (SP + -56 - Z.of_nat 8) with (SP + -2128 + 2064) in FR2 by (clear; lia);
        clear ST1 ST2 STa STb;
        match goal with FR0 : rw_cells _ mx (SP + -2128) [C8 _; C8 _] |- _ =>
          chunk_split FR0 1%nat FRp FRz;
          apply (rw_cells_reshape asegs _ _ _ [C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0)]) in FRz; [| cbn; tauto| vm_compute; reflexivity] end;
        change 240%nat with (8 * 30)%nat in FTR; destruct (u64arr_of_CB _ _ _ 30 FTR) as (ws & HTR & HL);
        lx_exs; lx_ands;
          [ reflexivity | lx_munch MU7 MUl | lx_wmono WM7 WMl | assumption | assumption
          | apply (proj2 (rw_cells_app asegs _ (SP + -2128) [C8 _] [C4 _; C4 _])); split;
              [replace (SP + -2128 + 16) with (SP + -2112) by (clear; lia); exact FRp| cbn [cells_size csize Nat.add]; exact FRz]
          | exact HTR | exact HL | exact FR1
          | match goal with H0 : rw_cells _ _ (SP + -72) _ |- _ => replace (SP + -2128 + 2056) with (SP + -72) by (clear; lia); exact H0 end
          | exact FR2 | exact STl
          | eapply ia_cells_transport; [exact IACl| exact MUl| exact WMl| unfold A_IA; lx_dj| unfold A_IA_INIT; lx_dj] ]
      end
    end.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0010>L5047823602.43000004S2SP". (* [comment removed for export] *)
  #[using="IMG ALWF CSOK"] Lemma free_mid : ltac2:(CDefT.buildp (gd_tbl_AW_FreeA ()) "Pgp,(0.&40.)Ptp,(0.&40.)Pt0,(0.&40.)Pt1,(0.&40.)Pt2,(0.&40.)Pa0,(0.&40.)Pa1,(0.&40.)Pa2,(0.&40.)Pa3,(0.&40.)Pa4,(0.&40.)Pa5,(0.&40.)Pa6,(0.&40.)Pa7,(0.&40.)Ps2,(0.&40.)Ps3,(0.&40.)Ps4,(0.&40.)Ps5,(0.&40.)Ps6,(0.&40.)Ps7,(0.&40.)Ps8,(0.&40.)Ps9,(0.&40.)Ps10,(0.&40.)Ps11,(0.&40.)Pt3,(0.&40.)Pt4,(0.&40.)Pt5,(0.&40.)Pt6,(0.&40.)PSP,$2.Pp,$2.PF,(29.&5.(0.&40.))Pfc,(0.&20.)Pm,P,(0.&40.)(1.(0.&8.))P,(<.R5.(2:.+2.+3>.))P,(<.+1000.R6.)(2;.$4.VAL,VCS,Lms',$14.(>.$14.R1.(17.(18.(:.&40.$2<.)(:.&40.(=.R8.-850.))R23.R22.R21.R20.R1?.(:.&40.R8.)(:.&40.R7.)(:.&40.R7.)(:.&40.(=.R8.-850.))(:.&40.+1.)R1;.R1:.R19.R18.R17.R16.R15.R14.R13.R12.R11.R10.R?.R>.R=.R<.R;.R:.R9.)R6.(:.&40.$2=.)R5.(1<.(0.&40.))R4.(1=.$4.)))(17.(18.(:.&40.$19.)(:.&40.(=.R7.-850.))R22.R21.R20.R1?.R1>.(:.&40.R7.)(:.&40.R6.)R1=.R1<.R1;.R1:.R19.R18.R17.R16.R15.R14.R13.R12.R11.R10.R?.R>.R=.R<.R;.R:.R9.R8.)R5.(:.&40.$19.)R4.(1<.(0.&40.))R3.(1=.$4.)))")
(* [comment removed for export] *).
  Proof.
    intros gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 SP p F fc m SPH SPL.
    facts. unfold A_FREE_RA1, A_FREE_RA2, A_ASAN_FREE.
    (* [comment removed for export] *)
    zstep. zstep. replace (SP + -2048 + -80) with (SP + -2128) by lia. zstep. zstep. zstep.
    apply evtA_done. reflexivity.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0010>L35132559173.2000009S3csj3SZJ". (* [comment removed for export] *)
  #[using="IMG ALWF CSOK"] Lemma free_epi : ltac2:(CDefT.buildp (gd_tbl_AW_FreeA ()) "Pra,(0.&40.)Pgp,(0.&40.)Ptp,(0.&40.)Pt0,(0.&40.)Pt1,(0.&40.)Pt2,(0.&40.)Ps0,(0.&40.)Ps1,(0.&40.)Ps2,(0.&40.)Ps3,(0.&40.)Ps4,(0.&40.)Ps5,(0.&40.)Px8,(0.&40.)Px9,(0.&40.)Px18,(0.&40.)Px19,(0.&40.)Px20,(0.&40.)Px21,(0.&40.)Pa0,(0.&40.)Pa1,(0.&40.)Pa2,(0.&40.)Pa3,(0.&40.)Pa4,(0.&40.)Pa5,(0.&40.)Pa6,(0.&40.)Pa7,(0.&40.)Ps6,(0.&40.)Ps7,(0.&40.)Ps8,(0.&40.)Ps9,(0.&40.)Ps10,(0.&40.)Ps11,(0.&40.)Pt3,(0.&40.)Pt4,(0.&40.)Pt5,(0.&40.)Pt6,(0.&40.)PSP,$2.Plo,$2.PF,(29.&5.(0.&40.))Pfc,(0.&20.)Pm0,P,(0.&40.)(1.(0.&8.))Pm,P,(0.&40.)(1.(0.&8.))Pcsj,(?.$6.)PW,(?.(2>.$2.$2.))P,(3.$4.R3.(=.R8.-850.)R2.)P,(>.$2.(2?.(30.R3.))+818.)P,(3.$4.R5.(=.R:.-38.)(5.$6.(22.R23.)(5.$6.(22.R24.)(5.$6.(22.R25.)(5.$6.(22.R26.)(5.$6.(22.R27.)(5.$6.(22.R28.)(5.$6.(22.R2>.)(;.$6.)))))))))P,(27.$4.R6.R:.(=.R;.-850.))P,(<.+65?000.R;.)P,(<.R<.(31.R=.+1000.))P,(<.R>.(2:.+2.+3>.))P,(1>.(5.(2>.$2.$2.)(32.$2.$2.R>.R?.)R8.)R;.R:.)P,(20.$4.R<.R;.)P,(21.$4.R<.)P,(33.VCS,R11.(31.R12.R11.))(2;.$4.VAL,VCS,Lms',$14.(15.P,(0.&40.)(1.(0.&8.))Lm',P,(0.&40.)(1.(0.&8.))(16.(>.$14.R2.(17.(18.R39.(:.&40.R15.)R38.R37.R36.R35.R34.R33.R32.R27.R26.R25.R24.R23.R22.R21.R20.R31.R30.R2?.R2>.R1?.R1>.R1=.R1<.R1;.R1:.R19.R18.R17.R16.)R13.(34.R39.)R12.(1<.(0.&40.))R1.(1=.$4.)))(16.(1>.(5.(2>.$2.$2.)(32.$2.$2.R14.R15.)R>.)R11.R1.)(16.(20.$4.R11.R1.)(16.(21.$4.R1.)(27.$4.R1.R14.R15.))))))(17.(18.(:.&40.$2<.)(:.&40.(=.R13.-850.))R36.R35.R34.R33.R32.R2;.R2:.R25.R24.R23.R22.R21.R20.R1?.R1>.R29.R28.R27.R26.R1=.R1<.R1;.R1:.R19.R18.R17.R16.R15.R14.)R11.(:.&40.$2<.)R10.(1<.(0.&40.))R>.(1=.$4.)))")
(* [comment removed for export] *).
  Proof.
    pose proof (I : lx_noaceil) as LXNOACEIL.  (* [comment removed for export] *)
    intros ra gp tp t0 t1 t2 s0 s1 s2 s3 s4 s5 x8 x9 x18 x19 x20 x21 a0 a1 a2 a3 a4 a5 a6 a7 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
      SP lo F fc m0 m csj W FRJ SZJ F6 ST LOIMG SPL SPH MU WM MI SCS.
    unfold A_FREE_RA2.
    (* [comment removed for export] *)
    apply (rw_cells_reshape asegs _ _ _ [CB 2072%nat (cells_bytes csj)]) in FRJ;
      [| cbn; rewrite cells_bytes_length by (exact (proj1 (proj1 FRJ))); split; [clear -SZJ; lia| exact I]
       | cbn; rewrite app_nil_r; reflexivity].
    lx_aceil.
    (* [comment removed for export] *)
    lx_run (PLAN [] [] 20%N).
    lazymatch goal with MUl : munch _ m ?mx, WMl : wmono _ m _ |- _ =>
      lx_post; [lx_munch MU MUl | lx_wmono WM WMl] end.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
End FreeA.

End ARUN_1.
