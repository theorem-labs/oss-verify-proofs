(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Arr Asn1Aux CellsX.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import AModel.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import AW_Unwind AW_MmapFixed.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import AW_ClassId AW_Combined AW_Refill.
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
Import OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.LxhSyntax. #[local] Instance lxh_tab : OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.lx_hints := OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.lxh_parse "P0021b8b25cb1c38d 0 4 0 16 35 16 47 16 48 16P016a65e2e5e98229 0 4 0 1 32 1 36 1 37 1P01870567a5b9eea8 0 6 0 16 33 16 35 16 36 16 47 16 48 16P0188720900f9cb60 0 6 0 16 33 16 35 16 36 16 47 16 48 16P01c2e65385a5d356 0 4 0 16 35 16 47 16 48 16P028487dbd2523b66 0 6 1 16 34 16 36 16 37 16 48 16 49 16P02a38be8e6a0329a 1 1 16 2 1 1 48 1 10 7 128 34 128 36 256 37 256 42 128 43 128 44 128 45 128 49 256 50 4096P040a4ad7429fa285 0 6 0 16 33 16 35 16 36 16 47 16 48 16P04894e0ff05de19c 0 6 1 16 34 16 36 16 37 16 48 16 49 16P0571b423f90984dd 0 4 0 16 35 16 47 16 48 16P062ea9e15ba85b2a 0 4 0 1 32 1 36 1 37 1P0756b649321b78a4 0 4 0 1 32 1 36 1 37 1P07a98e9c9f216802 1 2 16 2 0 1 49 1 16 2 1 1 48 1 2 50 1 51 1P07edaae33aac607e 1 2 16 2 0 1 49 1 16 2 1 1 48 1 2 50 1 51 1P07fdd7e8e419c15d 0 4 0 1 32 1 36 1 37 1P08092d2977aa69e4 0 4 0 16 35 16 47 16 48 16P09290652c54ce594 0 6 0 16 33 16 35 16 36 16 47 16 48 16P09cba0e8baa7b923 0 4 0 1 32 1 36 1 37 1P0a955909abb1fbdf 0 4 0 16 35 16 47 16 48 16P0f09f7636f575f13 1 1 128 1 0 1 2 21 1 36 1P1025446ecd44abbf 1 1 128 1 0 1 2 20 1 36 1P1070ce3d0c0e09c4 0 4 0 1 32 1 36 1 37 1P116fb5a115edffd1 0 6 0 16 33 16 35 16 36 16 47 16 48 16P12c92bd75f5daf1e 0 4 0 16 35 16 47 16 48 16P1330cd5f608fc920 1 2 16 2 0 1 49 1 16 2 1 1 48 1 2 50 1 51 1P137e4e534ecac837 1 1 16 2 1 1 48 1 10 7 128 34 128 36 256 37 256 42 128 43 128 44 128 45 128 49 256 50 4096P139802577541e261 0 4 0 16 35 16 47 16 48 16P15e1c984fdd01abf 0 6 1 16 34 16 36 16 37 16 48 16 49 16P15e52ab2e145bfa7 0 4 0 16 35 16 47 16 48 16P164cab0e8d8b0ed4 0 6 1 16 34 16 36 16 37 16 48 16 49 16P1715f18ddd377dd6 0 4 0 16 35 16 47 16 48 16P185ea84d3651a083 0 4 0 16 35 16 47 16 48 16P187c6c61daa6c7aa 1 2 16 2 0 1 49 1 16 2 1 1 48 1 2 50 1 51 1P1889caba5d2ca761 0 6 0 16 33 16 35 16 36 16 47 16 48 16P1a094c96e3fa1877 0 4 0 16 35 16 47 16 48 16P1a6c2c89e1e33fb3 0 4 0 16 35 16 47 16 48 16P1acb9586ff3cbdd1 0 6 0 16 33 16 35 16 36 16 47 16 48 16P1b0761fcffdc7405 0 4 0 16 35 16 47 16 48 16P1bcf9ec6703ce0e6 0 4 0 16 35 16 47 16 48 16P1cf981f4df591fbf 0 4 0 16 35 16 47 16 48 16P1d883dc7daae100c 0 4 0 16 35 16 47 16 48 16P1dd85879e28dc4ab 0 4 0 16 35 16 47 16 48 16P1e0d7594b59d80f4 1 1 16 2 1 1 48 1 10 7 128 34 128 36 256 37 256 42 128 43 128 44 128 45 128 49 256 50 4096P1e6b3f939bca0d49 0 4 0 16 35 16 47 16 48 16P1eabbc6cd9930a64 0 4 0 16 35 16 47 16 48 16P1ead13ce49c24f60 0 4 0 16 35 16 47 16 48 16P208f1f30fb26607e 0 4 0 16 35 16 47 16 48 16P2191224ab87ef803 0 6 0 16 33 16 35 16 36 16 47 16 48 16P230dc219a29d81ec 0 4 0 16 35 16 47 16 48 16P2326707548bbc6cd 0 6 1 16 34 16 36 16 37 16 48 16 49 16P2332e9f8cabd2953 0 4 0 16 35 16 47 16 48 16P23458f377aa101b7 0 4 0 1 32 1 36 1 37 1P244ea600dbc92115 0 4 0 1 32 1 36 1 37 1P24c901996e145c63 0 6 1 16 34 16 36 16 37 16 48 16 49 16P2576666a4c3a51a7 1 1 16 2 1 1 48 1 10 7 128 34 128 36 256 37 256 42 128 43 128 44 128 45 128 49 256 50 4096P25d3d4a36a5946e9 0 4 0 16 35 16 47 16 48 16P28aaa06f05729f55 1 1 16 2 1 1 48 1 10 7 128 34 128 36 256 37 256 42 128 43 128 44 128 45 128 49 256 50 4096P2aedb9b8371580d1 0 4 0 16 35 16 47 16 48 16P2c4bac1809bdc47f 0 6 1 16 34 16 36 16 37 16 48 16 49 16P2c536fc9e461dec1 0 6 1 16 34 16 36 16 37 16 48 16 49 16P2c7c06332176bbfb 0 4 0 16 35 16 47 16 48 16P2cc934af27d6a65d 0 4 0 16 35 16 47 16 48 16P2ce30f332fda78d4 0 4 0 16 35 16 47 16 48 16P2d03a3b07470901f 0 4 0 16 35 16 47 16 48 16P2d30005b3966f545 0 6 1 16 34 16 36 16 37 16 48 16 49 16P2dda0eb4d2dd7d4b 1 1 16 2 1 1 48 1 10 7 128 34 128 36 256 37 256 42 128 43 128 44 128 45 128 49 256 50 4096P30472f4b19587b7b 0 6 0 16 33 16 35 16 36 16 47 16 48 16P30c4ce3ffdc2f57d 0 6 0 16 33 16 35 16 36 16 47 16 48 16P30f1304196012b7f 0 6 1 16 34 16 36 16 37 16 48 16 49 16P315d50a054e4064d 0 4 0 16 35 16 47 16 48 16P319af54ac5078596 0 4 0 1 32 1 36 1 37 1P319ec82c11325a96 0 4 0 1 32 1 36 1 37 1P32a3b51aa82dd251 1 2 16 2 0 1 49 1 16 2 1 1 48 1 2 50 1 51 1P333264a6620ce6f6 0 6 0 16 33 16 35 16 36 16 47 16 48 16P333309504f507c76 0 4 0 1 32 1 36 1 37 1P337297502bac6040 0 4 0 1 32 1 36 1 37 1P33ee2998fa315074 0 6 1 16 34 16 36 16 37 16 48 16 49 16P3577bcd736510eb2 0 6 0 16 33 16 35 16 36 16 47 16 48 16P36131f987512313a 0 4 0 16 35 16 47 16 48 16P368b674e531345dd 1 2 16 2 0 1 49 1 16 2 1 1 48 1 2 50 1 51 1P370be9d6ef45ad7c 1 1 16 2 1 1 48 1 10 7 128 34 128 36 256 37 256 42 128 43 128 44 128 45 128 49 256 50 4096P371c752a85df7194 1 2 16 2 0 1 49 1 16 2 1 1 48 1 2 50 1 51 1P371f179f0770a7f6 0 6 0 16 33 16 35 16 36 16 47 16 48 16P374b1330d75a8269 0 4 0 16 35 16 47 16 48 16P375d3315d3ea61bb 0 4 0 16 35 16 47 16 48 16P3964d15d01ae500d 1 1 16 2 1 1 48 1 10 7 128 34 128 36 256 37 256 42 128 43 128 44 128 45 128 49 256 50 4096P39a30550778b97ac 0 4 0 16 35 16 47 16 48 16P39a885d58d94d946 0 4 0 16 35 16 47 16 48 16P39ff3908479084bb 0 4 0 1 32 1 36 1 37 1P3b1e9f458bf14f22 0 4 0 16 35 16 47 16 48 16P3b1f251e22dd7e0c 0 6 1 16 34 16 36 16 37 16 48 16 49 16P3b5e0cff46c9244f 0 4 0 16 35 16 47 16 48 16P3be1db7e8c15979d 0 6 1 16 34 16 36 16 37 16 48 16 49 16P3d0c58d9eb5b391e 0 4 0 16 35 16 47 16 48 16P3d3f7e192d6c9b9d 0 4 0 16 35 16 47 16 48 16P3fdf0a65f9f36c96 0 4 0 1 32 1 36 1 37 1N060d45c50cba08ddN07a8607ab8d70bc8N0f7f8ccb42dd1748N14aa9533e4aab230N152e15d431fcec23N1b8abf825416287bN1cf613d5abc320a8N209203cfc0f5ef20N27d3704d95cf3c41N2a8559a6439aa91eN2c277cc410538762N313ef305f0d59fffN353fd4c008dd9fa5N37d4697b53aee42d"%lxh.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import LiaOrc. (* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= orc_lia. (* [comment removed for export] *)
Local Ltac dlia ::= orc_dlia. (* [comment removed for export] *)
Local Ltac plia ::= orc_plia. (* [comment removed for export] *)
Local Ltac clear_disj ::= fc_clear_disj. (* [comment removed for export] *)
Local Ltac prune_disj ::= fc_prune_disj. (* [comment removed for export] *)
Ltac2 gd_tbl_AW_GetFrom () : Init.string Init.list := ["Corelib.Init.Datatypes.nat"; "Corelib.Init.Datatypes.list"; "stdpp.bitvector.definitions.bv"; "Corelib.Init.Peano.le"; "Corelib.Init.Datatypes.length"; "Corelib.Init.Logic.eq"; "ARUN_1.cpy"; "Corelib.Init.Peano.lt"; "Corelib.Init.Datatypes.option"; "Stdlib.Lists.List.nth_error"; "Corelib.Init.Datatypes.Some"; "RocqVerifyHarness.AgentSubmission.Lib.Arr.upd"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.sx32"; "Corelib.Init.Datatypes.S"; "RocqVerifyHarness.AgentSubmission.Lib.Step.rw_cells"; "RocqVerifyHarness.AgentSubmission.B.AImg.asegs"; "Stdlib.ZArith.BinInt.Z.add"; "Corelib.Init.Datatypes.cons"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.cell"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.CB"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C8"; "Corelib.Init.Datatypes.nil"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.machine_state"; "Corelib.Init.Logic.ex"; "Corelib.Init.Logic.and"; "RocqVerifyHarness.AgentSubmission.Lib.MState.MS"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.mkR"; "stdpp.bitvector.definitions.Z_to_bv"; "RocqVerifyHarness.AgentSubmission.Lib.MState.ret_pc"; "Corelib.Init.Datatypes.None"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.seg_rom"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.munch"; "Corelib.Init.Datatypes.prod"; "Corelib.Numbers.BinNums.Z"; "Corelib.Init.Datatypes.pair"; "Stdlib.ZArith.BinInt.Z.mul"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.wmono"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.mem_inv"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.stk"; "LinuxProcessSemantics.Riscv.Prelude.bvmap"; "Stdlib.ZArith.BinInt.Z.le"; "Stdlib.ZArith.BinInt.Z.pow"; "Stdlib.ZArith.BinInt.Z.modulo"; "RocqVerifyHarness.AgentSubmission.LibA.ALazy.crange"; "ARUN_1.kWriterLock"; "ARUN_1.GetFrom.gf_frame"; "RocqVerifyHarness.AgentSubmission.AHeap.ACeil.ACEIL"; "Stdlib.ZArith.BinInt.Z.sub"; "Corelib.Init.Logic.or"; "RocqVerifyHarness.AgentSubmission.LibA.AEvtA.evtA"; "ARUN_1.GetFrom.gf_ret_post"; "Stdlib.ZArith.BinInt.Z.of_nat"; "Stdlib.ZArith.BinInt.Z.lt"; "Stdlib.ZArith.BinInt.Z.to_nat"; "RocqVerifyHarness.AgentSubmission.Lib.Arr.u32arr"; "ARUN_1.GetFrom.gf_ok_post"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.A_INSTANCE"; "ARUN_1.GetFrom.gf_locked"; "ARUN_1.GetFrom.gf_miss_regs"; "ARUN_1.A_POPULATE"; "RocqVerifyHarness.AgentSubmission.Lib.Step.ro_cells"; "ARUN_1.GetFrom.gfA_post"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_Refill.A_GETFROM"].

Section ARUN_1. Context {hAR : arun}.
Set Printing Width 250.

Definition A_POPULATE : Z := 0x4cb60.      (* [comment removed for export] *)
Definition kWriterLock : Z := 2^60.

(* [comment removed for export] *)
Definition cpy (i : nat) (ws ds : list word) : list word := map sx32 (firstn i ws) ++ skipn i ds.
Local Ltac2 Set LiaOrc.tbl := fun () => "0010>L12404458709.600000>S1i2ws2ds1H2H0". (* [comment removed for export] *)
Lemma cpy_length : ltac2:(CDefT.buildp (gd_tbl_AW_GetFrom ()) "Pi,$0.Pws,(1.(2.&40.))Pds,(1.(2.&40.))P,(3.R3.(4.(2.&40.)R2.))P,(3.R4.(4.(2.&40.)R2.))(5.$0.(4.(2.&40.)(6.R5.R4.R3.))(4.(2.&40.)R3.))")
(* [comment removed for export] *).
Proof. intros. unfold cpy. rewrite app_length, map_length, firstn_length, skipn_length. lia. Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
Local Ltac2 Set LiaOrc.tbl := fun () => "0090?L35084011696.9 L37401557894.13L43588673777.9 L54952894175.13L60252186448.9 L60256308493.13L63447229712.8 L63810498890.8 L66731872928.9 00000B00]00o01J01\02702F02U02gS1i2ws2ds2Hd2Hw2L1S1i2ws2ds2Hd2Hw2L13pre4HlenS1i2ws2ds2Hd2Hw2L1S1i2ws2ds2Hd2Hw2L13pre4HlenS1i2ws2ds2Hd2Hw2L1S1i2ws2ds2Hd2Hw2L13pre4HlenS1i2ws2ds2Hd2HwS1i2ws2ds2Hd2HwS1i2ws2ds2Hd2Hw2L1". (* [comment removed for export] *)
Lemma cpy_step : ltac2:(CDefT.buildp (gd_tbl_AW_GetFrom ()) "Pi,$0.Pws,(1.(2.&40.))Pds,(1.(2.&40.))Pw,(2.&40.)P,(7.R4.(4.(2.&40.)R2.))P,(7.R5.(4.(2.&40.)R4.))P,(5.(8.(2.&40.))(9.(2.&40.)R5.R6.)(:.(2.&40.)R3.))(5.(1.(2.&40.))(;.(2.&40.)(6.R7.R6.R5.)R7.(<.R4.))(6.(=.R7.)R6.R5.))")
(* [comment removed for export] *).
Proof.
  intros i ws ds w Hd Hw Hnth. unfold cpy.
  rewrite upd_firstn_skipn.
  2:{ rewrite app_length, map_length, firstn_length, skipn_length. lia. }
  assert (L1 : length (map sx32 (firstn i ws)) = i) by (rewrite map_length, firstn_length; lia).
  rewrite firstn_app, L1, Nat.sub_diag, firstn_O, app_nil_r. rewrite firstn_all2 by lia.
  rewrite skipn_app, L1. replace (S i - i)%nat with 1%nat by lia. rewrite (skipn_all2 (map sx32 _)) by lia. rewrite app_nil_l.
  rewrite skipn_skipn. replace (1 + i)%nat with (S i) by lia.
  destruct (nth_error_split _ _ _ Hnth) as (pre & post & E & Hlen).
  rewrite E. rewrite !firstn_app, Hlen, Nat.sub_diag, firstn_O, app_nil_r. replace (S i - i)%nat with 1%nat by lia.
  rewrite (firstn_all2 (n:=i) pre) by lia. rewrite (firstn_all2 (n:=S i) pre) by lia.
  cbn [firstn]. rewrite map_app. cbn [map]. rewrite <- app_assoc. reflexivity.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

Section GetFrom.
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
  Definition gf_frame (m : mem) (SP : Z) (j0 : list byte) (q11 q10 q9 q8 q7 q6 q5 q4 q3 q2 q1 q0 qra : word) : Prop := ltac2:(CDefT.buildp (gd_tbl_AW_GetFrom ()) "(>.$?.O10.(10.O?.-80.)(11.$12.(13.#18.O>.)(11.$12.(14.O=.)(11.$12.(14.O<.)(11.$12.(14.O;.)(11.$12.(14.O:.)(11.$12.(14.O9.)(11.$12.(14.O8.)(11.$12.(14.O7.)(11.$12.(14.O6.)(11.$12.(14.O5.)(11.$12.(14.O4.)(11.$12.(14.O3.)(11.$12.(14.O2.)(11.$12.(14.O1.)(15.$12.))))))))))))))))")
(* [comment removed for export] *).

  (* [comment removed for export] *)
  Definition gf_ret_post (SP : Z) (gp tp s2 t5 t6 q11 q10 q9 q8 q7 q6 q5 q4 q3 q2 q1 q0 qra : word)
      (F : bvmap 5 word) (fc : bv 32) (RI lo c r : Z) (W : list (Z * Z)) (m0 m : mem) : machine_state -> Prop := ltac2:(CDefT.buildp (gd_tbl_AW_GetFrom ()) "Lms',$16.(17.(2.&40.)Lx5,(2.&40.)(17.(2.&40.)Lx6,(2.&40.)(17.(2.&40.)Lx7,(2.&40.)(17.(2.&40.)Lx11,(2.&40.)(17.(2.&40.)Lx12,(2.&40.)(17.(2.&40.)Lx13,(2.&40.)(17.(2.&40.)Lx14,(2.&40.)(17.(2.&40.)Lx15,(2.&40.)(17.(2.&40.)Lx16,(2.&40.)(17.(2.&40.)Lx17,(2.&40.)(17.(2.&40.)Lx28,(2.&40.)(17.(2.&40.)Lx29,(2.&40.)(17.P,(2.&40.)(8.(2.&8.))Lm',P,(2.&40.)(8.(2.&8.))(18.(5.$16.R>.(19.(1:.O:.(1;.&40.O1<.)O1;.O1:.R=.R<.R;.O;.O<.(1;.&40.O4.)R:.R9.R8.R7.R6.R5.R4.O=.O>.O?.O10.O11.O12.O13.O14.O15.O16.R3.R2.O18.O17.)O9.(1<.O:.)O8.(1=.(2.&40.))R1.(1>.$?.)))(18.(1?.(11.(20.$21.$21.)(22.$21.$21.O6.O1<.)(11.(20.$21.$21.)(22.$21.$21.(10.O7.(23.+80.O5.))(10.(10.O7.(23.+80.O5.))+8.))O3.))O2.R1.)(18.(24.$?.O2.R1.)(18.(25.$?.R1.)(18.(>.$?.R1.(10.O7.(23.+80.O5.))(11.$12.(14.(1;.&40.=))(15.$12.)))(18.(26.$?.R1.O6.O1<.)(18.(1?.(11.(20.$21.$21.)(22.$21.$21.O6.O1<.)(11.(20.$21.$21.)(22.$21.$21.(10.O7.(23.+80.O5.))(10.(10.O7.(23.+80.O5.))+8.))(15.(20.$21.$21.))))O1.R1.)(24.$?.O1.R1.)))))))))))))))))))))")
(* [comment removed for export] *).

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00=0?L12623754083.81L14830815217.81L25410475284.85L27559935248.79L42650174943.85L4612597544.79 L49698585326.84L51491909419.73L55716686549.0 L56130240059.81L66004556044.0 L67976691973.83L9255689747.79 00000=00J01901L02H02U02k03@03A03i03j04:04GS3hAR2SP2RI1cS3hAR2SP2RI1cS3hAR2SP2RI2lo1c2R02HC5LOIMG3SPL2HB5Ha_st5Hl_stS3hAR2RI1c2R02R12HCS3hAR2SP2RI2lo1c2R03RAL2HC5LOIMG3SPL3SPA4RSEP2HB5Ha_st5Hl_stS3hAR2RI1c2HCS3hAR2SP2RI1c2HB5Ha_stS3hAR2SP2RI2lo1c1y2HySS3hAR2SP2RI2lo1c2R03RAL2HC5LOIMG3SPL3SPASS3hAR2SP2RI1c2HBS3hAR2RI1c2HC". (* [comment removed for export] *)
  Lemma gf_unlock : ltac2:(CDefT.buildp (gd_tbl_AW_GetFrom ()) "Pra,(2.&40.)Pgp,(2.&40.)Ptp,(2.&40.)Pt0,(2.&40.)Pt1,(2.&40.)Pt2,(2.&40.)Pa0,(2.&40.)Pa1,(2.&40.)Pa2,(2.&40.)Pa3,(2.&40.)Pa4,(2.&40.)Pa5,(2.&40.)Pa6,(2.&40.)Pa7,(2.&40.)Ps2,(2.&40.)Ps4,(2.&40.)Ps5,(2.&40.)Ps6,(2.&40.)Ps7,(2.&40.)Ps8,(2.&40.)Ps9,(2.&40.)Ps10,(2.&40.)Ps11,(2.&40.)Pt3,(2.&40.)Pt4,(2.&40.)Pt5,(2.&40.)Pt6,(2.&40.)Pq11,(2.&40.)Pq10,(2.&40.)Pq9,(2.&40.)Pq8,(2.&40.)Pq7,(2.&40.)Pq6,(2.&40.)Pq5,(2.&40.)Pq4,(2.&40.)Pq3,(2.&40.)Pq2,(2.&40.)Pq1,(2.&40.)Pq0,(2.&40.)Pqra,(2.&40.)Pj0,(1.(2.&8.))PSP,$21.PF,(27.&5.(2.&40.))Pfc,(2.&20.)Pm0,P,(2.&40.)(8.(2.&8.))Pm,P,(2.&40.)(8.(2.&8.))PRI,$21.Plo,$21.Pc,$21.Pr,$21.PW,(1.(20.$21.$21.))P,(28.+65?000.R5.)P,(28.(10.R6.+1000.)(29.+2.+2?.))P,(5.$21.(2:.R7.+1000.)=)P,(2;.VCS,R8.+1000.)P,(18.(28.+1.R7.)(28.R7.+1?.))P,(18.(28.=R7.)(28.R7.+1.))P,(>.$?.R<.(10.R;.(23.+80.R9.))(11.$12.(14.(1;.&40.$2<.))(15.$12.)))P,(2=.R=.R11.R12.R1?.R1>.R1=.R1<.R1;.R1:.R19.R18.R17.R16.R15.R14.R13.)P,(26.$?.R>.R<.(10.R12.-80.))P,(28.(2>.VhAR,)R=.)P,(28.R>.(2?.R14.+80.))P,(28.R15.(29.+2.+3?.))P,(5.$21.(2:.R16.+10.)=)P,(30.(28.(10.R12.+1000.)R11.)(28.R17.R12.))P,(2;.VCS,R12.(2?.R18.R12.))P,(1?.(11.(20.$21.$21.)(22.$21.$21.R13.R19.)(11.(20.$21.$21.)(22.$21.$21.(10.R14.(23.+80.R12.))(10.(10.R14.(23.+80.R12.))+8.))R10.))R16.R15.)P,(24.$?.R17.R16.)P,(25.$?.R17.)(31.$?.VAL,VCS,(32.R1<.R44.R43.R37.R2<.R2;.R2:.R29.R28.R27.R26.R25.R24.R23.R22.R21.R20.R1?.R1>.R1;.R1:.R17.R16.R15.R14.R13.R19.R18.)(19.(1:.R45.(1;.&40.(10.R1<.-80.))R44.R43.R42.R41.R40.(1;.&40.(10.R17.(23.+80.R15.)))(1;.&40.R14.)R3?.R3>.R3=.R3<.R3;.R3:.R39.R38.R37.(1;.&40.(29.+2.+3=.))R36.R35.R34.R33.R32.R31.R30.R2?.R2>.R2=.R2<.R2;.)R1;.(1;.&40.+4<9?0.)R1:.(1=.(2.&40.))R18.(1>.$?.)))")
(* [comment removed for export] *).
  Proof.
    intros ra gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 q11 q10 q9 q8 q7 q6 q5 q4 q3 q2 q1 q0 qra j0
      SP F fc m0 m RI lo c r W R0 R1 RAL RCS HC HR MX FR ST LOIMG SPL SPH SPA RSEP SCS MU WM MI.
    pose proof (cs_ok_sb _ _ CSOK) as SB64. pose proof ALWF as ALWF'; unfold al_wf in ALWF'. pose proof IMG as IMG'; unfold asan_img_ok in IMG'.
    unfold gf_frame, kWriterLock in *. change (2^60) with 1152921504606846976 in *. change (2^61) with 2305843009213693952.
    pose proof (munch_refl [(lo, SP); (RI + 128 * c, RI + 128 * c + 8)] m) as MU2. pose proof (wmono_refl asegs m) as WM2. lx_aceil.
    assert (KMC : ro_cells asegs m 66568 [C8 (Z_to_bv 64 12682135451164737535)])
      by (split; [cbn; repeat split; exact I|]; apply ro_bytes_at; [exact MI| clear; lia| cbn; clear; lia| apply ro_bytes_b_sound; vm_compute; reflexivity]).
    (* [comment removed for export] *)
    lx_run (PLAN [0x4ca2c] [] 40%N). lx_same.
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep. zstep. zstep.
    (* [comment removed for export] *)
    lx_run (PLAN [] [] 20%N). lx_same.
    apply evtA_done. unfold gf_ret_post.
    lx_exs; lx_ands; [ lx_mseq | exact MU | exact WM | assumption | assumption | assumption | lx_munchx | assumption ].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00N0?L10353725385.69L14403128707.8 L14753466635.69L17290936988.70L1871096642.69 L19022916715.70L19526786641.69L19526868180.70L1996927053.71 L1996927053.72 L21998135307.69L22729643158.69L22729823763.70L23464610505.69L26809741618.71L31112299814.70L3447122754.69 L37394217997.70L45815411402.71L45815411660.73L5058781764.73 L51432820307.69L51688566555.69L59996718509.69L63907091987.70L63907533974.69L6461075389.62 L6463217726.68 L8501252080.74 L954663865.69  00000K00Y01H02002K02c03A03_04D04i05E05`06;06Z07;07Z08508T09=09f0:U0;10;M0;N0;f0<>0>G0@V0@W0A2S1k1i1n2ws2ds2Hk2Hi3LWS3LDSS1i3DST1n2Hi1KS1k1i3SRC3DST1n2ws2ds2Hk2Hi3LWS3LDS2S02S12D02D1S1k1i3SRC3DST1n2ws2ds2Hk2Hi3LWS3LDS2S01KS1k1i1n2ws2ds2Hk2Hi3LWS3LDSS1k1i1n2ws2ds2Hk3LWS3LDSS1k1i1n2ws2ds2Hk2Hi2Hn3LWS3LDSS1k1i1n2ws2ds2Hk2Hi2Hn3LWS3LDSS1k1i3DST1n2ws2ds2Hk2Hi3LWS3LDS5HBarrS1k1i3DST1n2ws2ds2Hk2Hi3LWS3LDS5HBarrS1k1i3SRC1n2ws2ds2Hk3LWS3LDSS1k1i1n2ws2ds2Hk2Hn3LWS3LDSS1k1i1n2ws2ds2Hk2Hn3LWS3LDSS1k1i3SRC1n2ws2ds2Hk2Hi3LWS3LDSS1k1i3DST1n2ws2ds1W2Hk2Hi3LWS3LDSS1k1i3DST1n2ws2ds2Hk2Hi3LWS3LDSS1k1i1n2ws2ds2Hk2Hn3LWS3LDSS1k1i3DST1n2ws2ds2Hk2Hn3LWS3LDSS1k1i3SRC3DST1n2ws2ds2Hk3LWS3LDS2S02S12D1S1k1i3SRC3DST1n2ws2ds2Hk3LWS3LDS2S02S12D1S1k1i3SRC3DST1n2ws2ds2Hk2Hi2Hn3LWS3LDS2S03SEP1wS1k1i3DST1n2ws2ds2Hk3LWS3LDSS1k1i3SRC1n2ws2ds2Hk3LWS3LDSFS1k1i1n2ws2ds2Hk3LWS3LDSS1k1i1n2ws2ds2Hk3LWS3LDSS2AL2CS1i2ra2sp2gp2tp2t02t12t22s02s12a02a22a42a52a62a72s22s32s52s62s72s82s93s103s112t32t42t52t61F2fc2m01m3SRC3DST1n2ws2ds1W2Hk2Hi3LWS3LDSS2AL2CS1k1i2ra2sp2gp2tp2t02t12t22s02s12a02a22a42a52a62a72s22s32s52s62s72s82s93s103s112t32t42t52t61F2fc2m01m3SRC3DST1n2ws2ds1W2Hk2Hi3LWS3LDS3NTHFS1k1i1n2ws2ds2Hk2Hi3LWS3LDS". (* [comment removed for export] *)
  Lemma gf_copy : ltac2:(CDefT.buildp (gd_tbl_AW_GetFrom ()) "Pk,$0.Pi,$21.Pra,(2.&40.)Psp,(2.&40.)Pgp,(2.&40.)Ptp,(2.&40.)Pt0,(2.&40.)Pt1,(2.&40.)Pt2,(2.&40.)Ps0,(2.&40.)Ps1,(2.&40.)Pa0,(2.&40.)Pa2,(2.&40.)Pa4,(2.&40.)Pa5,(2.&40.)Pa6,(2.&40.)Pa7,(2.&40.)Ps2,(2.&40.)Ps3,(2.&40.)Ps5,(2.&40.)Ps6,(2.&40.)Ps7,(2.&40.)Ps8,(2.&40.)Ps9,(2.&40.)Ps10,(2.&40.)Ps11,(2.&40.)Pt3,(2.&40.)Pt4,(2.&40.)Pt5,(2.&40.)Pt6,(2.&40.)PF,(27.&5.(2.&40.))Pfc,(2.&20.)Pm0,P,(2.&40.)(8.(2.&8.))Pm,P,(2.&40.)(8.(2.&8.))PSRC,$21.PDST,$21.Pn,$21.Pws,(1.(2.&40.))Pds,(1.(2.&40.))PW,(1.(20.$21.$21.))P,(5.$21.(10.R27.(33.R28.))R4.)P,(18.(28.=R28.)(34.R28.R5.))P,(28.R6.+10.)P,(5.$0.(4.(2.&40.)R6.)(35.R7.))P,(5.$0.(4.(2.&40.)R6.)#10.)P,(28.+65?000.R;.)P,(28.(10.R<.(23.+4.R:.))(29.+2.+2?.))P,(18.(28.+1000.R<.)(30.(28.(10.R<.+40.)+10000.)(28.+65?000.R<.)))P,(28.(10.R=.+40.)(29.+2.+2?.))P,(30.(28.(10.R?.(23.+4.R=.))R>.)(28.(10.R>.+40.)R?.))P,(2;.VCS,R10.(23.+4.R>.))P,(2;.VCS,R10.+40.)P,(36.$?.R13.R12.R?.)P,(36.$?.R14.R12.(6.(35.R34.)R10.R?.))P,(1?.(11.(20.$21.$21.)(22.$21.$21.R13.(10.R13.(23.+4.R12.)))R?.)R16.R15.)P,(24.$?.R17.R16.)P,(25.$?.R17.)(31.$?.VAL,VCS,Lms',$16.(17.(2.&40.)Lx12,(2.&40.)(17.P,(2.&40.)(8.(2.&8.))Lm',P,(2.&40.)(8.(2.&8.))(18.(5.$16.R3.(19.(1:.R3:.R39.R38.R37.R36.R35.R34.R33.R32.R31.(1;.&40.(10.R19.(23.+4.R18.)))R2.(1;.&40.(10.R19.(23.+4.R18.)))R2?.R2>.R2=.R2<.R2;.R2:.(1;.&40.(10.R1:.(23.+4.R18.)))R29.R28.R27.R26.R25.R24.R23.R22.R21.R20.R1?.)R1>.(1;.&40.+4<9>0.)R1=.(1=.(2.&40.))R1.(1>.$?.)))(18.(1?.(11.(20.$21.$21.)(22.$21.$21.R19.(10.R19.(23.+4.R18.)))R15.)R1<.R1.)(18.(24.$?.R1<.R1.)(18.(25.$?.R1.)(18.(36.$?.R1.R1:.R17.)(36.$?.R1.R19.(6.(35.R18.)R17.R16.)))))))))(19.(1:.R37.R36.R35.R34.R33.R32.R31.R30.R2?.R2>.(1;.&40.(10.R16.(23.+4.R15.)))R2=.(1;.&40.(10.R16.(23.+4.R38.)))R2<.R2;.R2:.R29.R28.R27.(1;.&40.(10.R17.(23.+4.R38.)))R26.R25.R24.R23.R22.R21.R20.R1?.R1>.R1=.R1<.)R1;.(1;.&40.+4<9<<.)R1:.(1=.(2.&40.))R18.(1>.$?.)))")
(* [comment removed for export] *).
  Proof.
    induction k as [|k IH]; intros i ra sp gp tp t0 t1 t2 s0 s1 a0 a2 a4 a5 a6 a7 s2 s3 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m0 m SRC DST n ws ds W
      Hk Hi Hn LWS LDS S0 S1 D0 D1 SEP SCS DCS HS HD MU WM MI; [lia|].
    facts.
    destruct (nth_error ws (Z.to_nat i)) as [w|] eqn:NTH; [| apply nth_error_None in NTH; lia].
    pose proof (u32arr_read asegs m SRC ws i w _ HS NTH ltac:(lia) eq_refl) as RD.
    (* [comment removed for export] *)
    zstep. clear RD.
    (* [comment removed for export] *)
    pose proof (u32arr_store_ok asegs m DST _ i _ HD ltac:(rewrite cpy_length by lia; lia) eq_refl) as SOK.
    pose proof (u32arr_write asegs m DST _ i (sx32 w) HD ltac:(rewrite cpy_length by lia; lia)) as HD'.
    zstep.
    store_done. try clear HD.
    rewrite (cpy_step (Z.to_nat i) ws ds w) in HD' by (first [lia | exact NTH]).
    replace (S (Z.to_nat i)) with (Z.to_nat (i + 1)) in HD' by lia.
    (* [comment removed for export] *)
    zstep. zstep. replace (DST + 4 * i + 4) with (DST + 4 * (i + 1)) by lia. replace (SRC + 4 * i + 4) with (SRC + 4 * (i + 1)) by lia.
    zstep. if_cases K; zify_cond K.
    - (* [comment removed for export] *) eapply (IH (i + 1)); try eassumption; try lia.
    - (* [comment removed for export] *)
      assert (EN : i + 1 = n) by (clear - K Hi Hn D0 D1; lia).
      rewrite EN in *. apply evtA_done. do 2 eexists.
      split; [reflexivity|]. split; [eassumption|]. split; [eassumption|]. split; [eassumption|]. split; eassumption.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition gf_ok_post (SP : Z) (gp tp s2 t5 t6 q11 q10 q9 q8 q7 q6 q5 q4 q3 q2 q1 q0 qra : word)
      (F : bvmap 5 word) (fc : bv 32) (RI CH SRC lo c n nf' : Z) (ws ds : list word) (W : list (Z * Z)) (m0 : mem) : machine_state -> Prop := ltac2:(CDefT.buildp (gd_tbl_AW_GetFrom ()) "Lms',$16.(17.(2.&40.)Lx5,(2.&40.)(17.(2.&40.)Lx6,(2.&40.)(17.(2.&40.)Lx7,(2.&40.)(17.(2.&40.)Lx11,(2.&40.)(17.(2.&40.)Lx12,(2.&40.)(17.(2.&40.)Lx13,(2.&40.)(17.(2.&40.)Lx14,(2.&40.)(17.(2.&40.)Lx15,(2.&40.)(17.(2.&40.)Lx16,(2.&40.)(17.(2.&40.)Lx17,(2.&40.)(17.(2.&40.)Lx28,(2.&40.)(17.(2.&40.)Lx29,(2.&40.)(17.P,(2.&40.)(8.(2.&8.))Lm',P,(2.&40.)(8.(2.&8.))(17.(2.&40.)Lstw',(2.&40.)(18.(5.$16.R?.(19.(1:.O>.(1;.&40.O20.)O1?.O1>.R>.R=.R<.O?.O10.(1;.&40.+1.)R;.R:.R9.R8.R7.R6.R5.O11.O12.O13.O14.O15.O16.O17.O18.O19.O1:.R4.R3.O1<.O1;.)O=.(1<.O>.)O<.(1=.(2.&40.))R2.(1>.$?.)))(18.(1?.(11.(20.$21.$21.)(22.$21.$21.O8.O20.)(11.(20.$21.$21.)(22.$21.$21.(10.O;.(23.+80.O7.))(10.(10.O;.(23.+80.O7.))+8.))(11.(20.$21.$21.)(22.$21.$21.(10.(10.O;.(23.+80.O7.))+10.)(10.(10.O;.(23.+80.O7.))+18.))(11.(20.$21.$21.)(22.$21.$21.(10.(10.O;.(23.+80.O7.))+48.)(10.(10.O;.(23.+80.O7.))+50.))(11.(20.$21.$21.)(22.$21.$21.O:.(10.O:.(23.+4.O6.)))O2.)))))O1.R2.)(18.(24.$?.O1.R2.)(18.(25.$?.R2.)(18.(>.$?.R2.(10.O;.(23.+80.O7.))(11.$12.(14.(1;.&40.=))(15.$12.)))(18.(>.$?.R2.(10.(10.O;.(23.+80.O7.))+10.)(11.$12.(14.(1;.&40.O5.))(15.$12.)))(18.(>.$?.R2.(10.(10.O;.(23.+80.O7.))+48.)(11.$12.(14.R1.)(15.$12.)))(18.(36.$?.R2.O9.O4.)(18.(36.$?.R2.O:.(6.(35.O6.)O4.O3.))(26.$?.R2.O8.O20.))))))))))))))))))))))))")
(* [comment removed for export] *).

  Local Ltac2 Set LiaOrc.tbl := fun () => "00V0@L10160110690.96 L11792650643.98 L17628623115.95 L18436190141.96 L19702179407.96 L21005804121.96 L21247076085.96 L22700267513.103L22991783080.102L23031672621.101L23031672621.102L25211720889.96 L26667465834.119L28793754003.98 L31702012591.102L32171753408.96 L35722035376.102L36573214027.94 L37759976017.102L40669779716.94 L41411780311.96 L41707954711.99 L42299247836.100L42398928231.96 L42650174943.102L46992874510.99 L47951737461.102L49698585326.101L49715598868.102L50525304528.119L54625850244.96 L54668169763.96 L59107913074.101L61933964299.95 L68633958563.99 L8543861769.96  L8552563982.99  L9065380756.99  00000T01K02O03003Q04505305`06Y07n09K0:`0<C0=:0=;0>50?M0@00@i0AL0Am0BS0C<0D<0EQ0F50F60Fe0HU0I]0JA0Je0K_0LC0Li0M`0N]0OWS3hAR2SP2RI2FA2CH1n2nf2ws2ds3LWS3LDSS3hAR2SP2RI2FA2CH2lo1n2ws2ds2R02HN3LWS3LDS2F05LOIMG3SPLS3hAR2SP2RI2FA2CH2lo1n2nf2ws2ds2R02R12HN3HNF3LWS3LDS2F02F15LOIMG3SPLS3hAR2SP2RI2FA2CH1n2ws2ds3LWS3LDSS3hAR2SP2RI2FA2CH1n2ws2ds3LWS3LDSS3hAR2SP2RI2FA2CH1n2ws2ds2HN3LWS3LDSS3hAR2SP2RI2FA2CH2lo1n2nf2ws2ds2R02HN3HNF3LWS3LDS2F05LOIMG3SPLS3hAR2SP2RI2FA2CH2lo1c1n2ws2ds1W3LWS3LDS2x11HS3hAR3stw2SP2RI2FA2CH1c1n2ws2ds3LWS3LDS2LC2HB5Ha_st5Hl_stS3hAR2SP2RI2FA2CH2lo1n2nf2ws2ds2R02HN3HNF3LWS3LDS2F02F13FAL2C03CAL4CSEP5LOIMG3SPL3SPAS3hAR2SP2RI2FA2CH2lo1n2ws2ds2R02HN3LWS3LDS2F02C15LOIMG3SPL1c2nf3RAL2HC3HNF2F12C03CAL4CSEP3SPAS3hAR2SP2RI2FA2CH2lo1n2nf2ws2ds2R02HN3HNF3LWS3LDS2F02F13FAL2C03CAL4CSEP5LOIMG3SPL3SPAS3hAR2SP2RI2FA2CH2lo1c1n2nf2ws2ds2R02R13RAL2HC2HN3HNF3LWS3LDS2F02F12C02C13CAL4CSEP5LOIMG3SPL3SPA2LCS3hAR2SP2RI2FA2CH2lo1n2ws2ds2R02HN3LWS3LDS2F05LOIMG3SPLFS3hAR2SP2RI2FA2CH2lo1n2ws2ds2R02HN3LWS3LDS2F02C15LOIMG3SPLS3hAR3stw2SP2RI2FA2CH2lo1c1n2nf2ws2ds2R02HC2HN3LWS3LDS2F02F15LOIMG3SPL2LC2HB5Ha_st5Hl_stS3hAR2RI1c1n2ws2ds2HC2HN3LWS3LDS2LCS3hAR3stw2SP2RI2FA2CH1c1n2ws2ds3LWS3LDS2LC2HB5Ha_st5Hl_stS3hAR2RI1c1n2ws2ds2HC2HN3LWS3LDS2LCS3hAR2SP2RI2FA2CH1n2ws2ds3LWS3LDSS3hAR2SP2RI2FA2CH1c1n2ws2ds3LWS3LDS2LCS3hAR2SP2RI2FA2CH1c1n2ws2ds3LWS3LDS2LC2HBS3hAR2SP2RI2FA2CH2lo1n2nf2ws2ds2R02R12HN3LWS3LDS2F02F15LOIMG3SPLS3hAR3stw2SP2RI2FA2CH2lo1c1n2ws2ds2R02R12HC2HN3LWS3LDS2F05LOIMG3SPL2LC2HB5Ha_st5Hl_stS3hAR2SP2RI2FA2CH1n2ws2ds3LWS3LDS2LCFS3hAR2SP2RI2FA2CH1c1n2ws2ds3LWS3LDS2LC2HB5Ha_stS3hAR3stw2SP2RI2FA2CH2lo1c1n2nf2ws2ds2R03RAL2HC2HN3HNF3LWS3LDS2F02F12C03CAL4CSEP5LOIMG3SPL3SPA2LC2HB5Ha_st5Hl_stS3hAR2SP2RI2FA2CH2lo1c1n2ws2ds2R02R12HC2HN3LWS3LDS2F05LOIMG3SPL2LC2nf2F1S3hAR2SP2RI2FA2CH1n2ws2ds2HN3LWS3LDSS3hAR2SP2RI2FA2CH1n2nf2ws2ds3LWS3LDSS3hAR2SP2RI2FA2CH2lo1n2ws2ds2R02HN3LWS3LDS2F02C15LOIMG3SPLS3hAR2SP2RI2FA2CH1n2ws2ds2HN3LWS3LDSS3hAR2SP2RI2FA2CH1c1n2ws2ds3LWS3LDS2LCS3hAR2SP2RI2FA2CH2lo1n2ws2ds2R02HN3LWS3LDS2F05LOIMG3SPLS3hAR2SP2RI2FA2CH2lo1n2ws2ds2R02R12HN3LWS3LDS2F05LOIMG3SPL2LCS3hAR2SP2RI2FA2CH2lo1n2ws2ds2R12HN3LWS3LDS2F05LOIMG3SPL2LC". (* [comment removed for export] *)
  Lemma gf_tail : ltac2:(CDefT.buildp (gd_tbl_AW_GetFrom ()) "Pra,(2.&40.)Pgp,(2.&40.)Ptp,(2.&40.)Pt0,(2.&40.)Pt1,(2.&40.)Pt2,(2.&40.)Ps1,(2.&40.)Pa0,(2.&40.)Pa1,(2.&40.)Pa2,(2.&40.)Pa6,(2.&40.)Pa7,(2.&40.)Ps2,(2.&40.)Ps5,(2.&40.)Ps6,(2.&40.)Ps7,(2.&40.)Ps8,(2.&40.)Ps9,(2.&40.)Ps10,(2.&40.)Ps11,(2.&40.)Pt3,(2.&40.)Pt4,(2.&40.)Pt5,(2.&40.)Pt6,(2.&40.)Pq11,(2.&40.)Pq10,(2.&40.)Pq9,(2.&40.)Pq8,(2.&40.)Pq7,(2.&40.)Pq6,(2.&40.)Pq5,(2.&40.)Pq4,(2.&40.)Pq3,(2.&40.)Pq2,(2.&40.)Pq1,(2.&40.)Pq0,(2.&40.)Pqra,(2.&40.)Pstw,(2.&40.)Pj0,(1.(2.&8.))PSP,$21.PF,(27.&5.(2.&40.))Pfc,(2.&20.)Pm0,P,(2.&40.)(8.(2.&8.))Pm,P,(2.&40.)(8.(2.&8.))PRI,$21.PFA,$21.PCH,$21.Plo,$21.Pc,$21.Pn,$21.Pnf,$21.Pws,(1.(2.&40.))Pds,(1.(2.&40.))PW,(1.(20.$21.$21.))P,(28.+65?000.R:.)P,(28.(10.R;.+1000.)(2>.VhAR,))P,(5.$21.(2:.R<.+1000.)=)P,(2;.VCS,R=.+1000.)P,(18.(28.+1.R:.)(28.R:.+1?.))P,(18.(28.+1.R:.)(28.R:.+10.))P,(28.=R:.)P,(5.$0.(4.(2.&40.)R:.)(35.R<.))P,(5.$0.(4.(2.&40.)R:.)#10.)P,(28.+65?000.R12.)P,(28.(10.R13.(23.+4.(10.R>.R?.)))R14.)P,(5.$21.(2:.R14.+4.)=)P,(2;.VCS,(10.R15.(23.+4.R10.))(23.+4.R11.))P,(18.(28.+1000.R15.)(30.(28.(10.R15.+40.)+10000.)(28.+65?000.R15.)))P,(28.(10.R16.+40.)(2>.VhAR,))P,(5.$21.(2:.R17.+4.)=)P,(2;.VCS,R18.+40.)P,(30.(28.(10.R19.+40.)R1:.)(28.(10.R1;.+1000.)R19.))P,(>.$?.R1=.(10.R1<.(23.+80.R18.))(11.$12.(14.(1;.&40.$2<.))(15.$12.)))P,(>.$?.R1>.(10.(10.R1=.(23.+80.R19.))+10.)(11.$12.(14.(1;.&40.R17.))(15.$12.)))P,(>.$?.R1?.(10.(10.R1>.(23.+80.R1:.))+48.)(11.$12.(14.R25.)(15.$12.)))P,(36.$?.R20.(10.R1>.(23.+4.R19.))R18.)P,(36.$?.R21.R1>.R18.)P,(2=.R22.R26.R27.R35.R34.R33.R32.R31.R30.R2?.R2>.R2=.R2<.R2;.R2:.R29.)P,(26.$?.R23.R1?.(10.R27.-80.))P,(28.(2>.VhAR,)R20.)P,(28.R21.(2?.R29.+80.))P,(28.R2:.(29.+2.+3?.))P,(5.$21.(2:.R2;.+10.)=)P,(2;.VCS,R24.(2?.R2<.R24.))P,(1?.(11.(20.$21.$21.)(22.$21.$21.R25.R2=.)(11.(20.$21.$21.)(22.$21.$21.(10.R28.(23.+80.R24.))(10.(10.R28.(23.+80.R24.))+8.))(11.(20.$21.$21.)(22.$21.$21.(10.(10.R28.(23.+80.R24.))+10.)(10.(10.R28.(23.+80.R24.))+18.))(11.(20.$21.$21.)(22.$21.$21.(10.(10.R28.(23.+80.R24.))+48.)(10.(10.R28.(23.+80.R24.))+50.))(11.(20.$21.$21.)(22.$21.$21.R26.(10.R26.(23.+4.R23.)))R1?.)))))R2:.R29.)P,(24.$?.R2;.R2:.)P,(25.$?.R2;.)(31.$?.VAL,VCS,(37.R30.R56.R55.R4;.R41.R40.R3?.R3>.R3=.R3<.R3;.R3:.R39.R38.R37.R36.R35.R34.R33.R2?.R2>.R2;.R29.(10.R2:.(23.+4.R25.))R28.R27.R26.R25.R24.R23.R22.R2=.)(19.(1:.R57.(1;.&40.(10.R30.-80.))R56.R55.R54.R53.R52.(1;.&40.(10.R2;.(23.+80.R27.)))R51.R50.R4?.R4>.(1;.&40.R29.)(1;.&40.R26.)(1;.&40.R25.)R4=.R4<.R4;.(1;.&40.(29.+2.+3=.))(1;.&40.R2:.)R4:.R49.R48.R47.R46.R45.R44.R43.R42.R41.R40.)R2?.(1;.&40.+4<9;<.)R2>.(1=.(2.&40.))R2<.(1>.$?.)))")
(* [comment removed for export] *).
  Proof.
    intros ra gp tp t0 t1 t2 s1 a0 a1 a2 a6 a7 s2 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 q11 q10 q9 q8 q7 q6 q5 q4 q3 q2 q1 q0 qra stw j0
      SP F fc m0 m RI FA CH lo c n nf ws ds W R0 R1 RAL RCS HC HN HNF LWS LDS F0 F1 FAL FCS C0 C1 CAL CCS CSEP
      MX NF STC HS HD FR ST LOIMG SPL SPH SPA SCS MU WM MI.
    facts. unfold gf_frame in FR.
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep.
    rewrite (Z.shiftl_mul_pow2 nf 2), (Z.shiftl_mul_pow2 n 2) by lia. change (2^2) with 4.
    replace (FA + nf * 4) with (FA + 4 * nf) by lia. replace (CH + n * 4) with (CH + 4 * n) by lia.
    replace (Z_to_bv 64 CH) with (Z_to_bv 64 (CH + 4 * 0)) by (f_equal; lia).
    replace (Z_to_bv 64 (FA + 4 * nf)) with (Z_to_bv 64 (FA + 4 * nf + 4 * 0)) by (f_equal; lia).
    lazymatch goal with |- evtA _ _ _ _ (MS _ _ _ _ _ ?mc _) =>
      assert (HD0 : u32arr asegs mc CH (cpy (Z.to_nat 0) ws ds)) by (unfold cpy; cbn; exact HD) end.
    clear HD.
    callxA (eapply (gf_copy (Z.to_nat n) 0) with (W := []); try apply munch_refl; try apply wmono_refl; try eassumption; try lia).
    pose proof (cpy_length (Z.to_nat n) ws ds ltac:(lia) ltac:(lia)) as LC. rewrite LDS in LC.
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep.
    change 2305843009213693952 with (2^61).
    eapply evtA_cut. { eapply gf_unlock; try eassumption; try lia. }
    cbv beta. unfold gf_ret_post, gf_ok_post.
    intros ms' (x5 & x6 & x7 & x11 & x12 & x13 & x14 & x15 & x16 & x17 & x28 & x29 & m' & -> & MU' & WM' & MI' & MX' & ST' & MU2 & WM2).
    apply evtA_done. do 14 eexists.
    split; [reflexivity|]. split; [exact MU'|]. split; [exact WM'|]. split; [exact MI'|]. split; [exact MX'|].
    split. { eapply rw_cells_transport; [exact NF| exact MU2| exact WM2| cbn; lia]. }
    split. { eapply rw_cells_transport; [eassumption| exact MU2| exact WM2| cbn; lia]. }
    split. { eapply u32arr_transport; [exact PC| exact MU2| exact WM2| rewrite LWS; cbn; lia]. }
    split. { eapply u32arr_transport; [eassumption| exact MU2| exact WM2| rewrite LC; cbn; lia]. }
    exact ST'.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)


  (* [comment removed for export] *)
  Definition gf_locked (ra : word) (SP : Z) (gp tp : word) (RI T CH FA c n : Z) (s2 s10 s11 t3 t4 t5 t6 : word) : bvmap 5 word := ltac2:(CDefT.buildp (gd_tbl_AW_GetFrom ()) "(1:.O11.(1;.&40.(10.O10.-80.))O?.O>.(1;.&40.=)(1;.&40.$2<.)(1;.&40.=)(1;.&40.(10.O=.(23.+80.O9.)))(1;.&40.$38.)(1;.&40.(10.(10.O=.(23.+80.O9.))+8.))(1;.&40.(10.O<.+:=0.))(1;.&40.O9.)(1;.&40.O;.)(1;.&40.O8.)(1;.&40.=)(1;.&40.-1.)(1;.&40.=)O7.(1;.&40.(29.+2.+3=.))(1;.&40.O:.)(1;.&40.(29.+2.+28.))(1;.&40.+10000000000?????.)(1;.&40.$2<.)(1;.&40.+5=<.)(1;.&40.+=???????????????.)O6.O5.O4.O3.O2.O1.)")
(* [comment removed for export] *).

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00E0?L17618170671.83L17725009036.79L17731333800.78L22014186727.78L22020445891.79L22991783080.87L31475289507.83L31475289507.84L35722035376.87L42650174943.87L45331638039.84L49698585326.86L49715598868.87L51139731036.85L53860290987.85L59308628433.3 L59314923118.5 L61927706159.83L61929812368.84L66782819793.87L67241240092.8500001001P02002P03003e04H04k06<07M08008\0:C0:i0;Q0;Z0;f0<J0<n0=c0>JS3hAR2SP2RI2FA2CH2lo1n2nf2ws2ds2R02HN3HNF3LWS3LDS2F05LOIMG3SPL1KS3hAR2RI1c1n2ws2ds2HC2HN3LWS3LDSS3hAR2RI1c1n2ws2ds2HC2HN3LWS3LDSS3hAR2RI1c1n2ws2ds2HC2HN3LWS3LDSS3hAR2RI1c1n2ws2ds2HC2HN3LWS3LDSS3hAR2SP2RI2FA2CH1c1n2nf2ws2ds3LWS3LDS2HB5Ha_st5Hl_stS3hAR2SP2RI2FA2CH1c1n2ws2ds3LWS3LDSS3hAR2SP2RI2FA2CH1c1n2ws2ds3LWS3LDSS3hAR2SP2RI2FA2CH2lo1c1n2nf2ws2ds2R02HC2HN3LWS3LDS2F02F15LOIMG3SPL2HB5Ha_st5Hl_stS3hAR2SP2RI2FA2CH2lo1c1n2nf2ws2ds2R02R12HC2HN3LWS3LDS2F05LOIMG3SPL2HB5Ha_st5Hl_stS3hAR2SP2RI2FA2CH1c1n2ws2ds3LWS3LDSS3hAR2SP2RI2FA2CH1c1n2ws2ds3LWS3LDS2HB5Ha_stS3hAR2SP2RI2FA2CH2lo1c1n2nf2ws2ds2R03RAL2HC2HN3LWS3LDS2F02F12C03CAL4CSEP5LOIMG3SPL3SPA1K2HB5Ha_st5Hl_stS3hAR2SP2RI2FA2CH1c1n2ws2ds3LWS3LDS2HBS3hAR2SP2RI2FA2CH1n2nf2ws2ds3HNF3LWS3LDSS1n2HN2K2S1n2nf3HNF1KS3hAR2SP2RI2FA2CH1n2ws2ds2HN3LWS3LDSS3hAR2SP2RI2FA2CH1n2ws2ds2HN3LWS3LDSS3hAR2SP2RI2FA2CH1c1n2nf2ws2ds3LWS3LDS2HB5Ha_st5Hl_stS3hAR2SP2RI2FA2CH1n2nf2ws2ds3LWS3LDS2F1". (* [comment removed for export] *)
  Lemma gf_hit : ltac2:(CDefT.buildp (gd_tbl_AW_GetFrom ()) "Pra,(2.&40.)Pgp,(2.&40.)Ptp,(2.&40.)Ps2,(2.&40.)Ps10,(2.&40.)Ps11,(2.&40.)Pt3,(2.&40.)Pt4,(2.&40.)Pt5,(2.&40.)Pt6,(2.&40.)Pq11,(2.&40.)Pq10,(2.&40.)Pq9,(2.&40.)Pq8,(2.&40.)Pq7,(2.&40.)Pq6,(2.&40.)Pq5,(2.&40.)Pq4,(2.&40.)Pq3,(2.&40.)Pq2,(2.&40.)Pq1,(2.&40.)Pq0,(2.&40.)Pqra,(2.&40.)Pstw,(2.&40.)Pj0,(1.(2.&8.))PSP,$21.PF,(27.&5.(2.&40.))Pfc,(2.&20.)Pm0,P,(2.&40.)(8.(2.&8.))Pm,P,(2.&40.)(8.(2.&8.))PRI,$21.PT,$21.PFA,$21.PCH,$21.Plo,$21.Pc,$21.Pn,$21.Pnf,$21.Pws,(1.(2.&40.))Pds,(1.(2.&40.))PW,(1.(20.$21.$21.))P,(28.+65?000.R;.)P,(28.(10.R<.+1000.)(2>.VhAR,))P,(5.$21.(2:.R=.+1000.)=)P,(2;.VCS,R>.+1000.)P,(18.(28.+1.R:.)(28.R:.+1?.))P,(18.(28.+1.R:.)(28.R:.+10.))P,(18.(28.R;.R:.)(34.R:.(29.+2.+3?.)))P,(5.$0.(4.(2.&40.)R:.)(35.R<.))P,(5.$0.(4.(2.&40.)R:.)#10.)P,(28.+65?000.R12.)P,(28.(10.R13.(23.+4.R>.))R15.)P,(5.$21.(2:.R14.+4.)=)P,(2;.VCS,(10.R15.(23.+4.(2?.R10.R11.)))(23.+4.R11.))P,(18.(28.+1000.R15.)(30.(28.(10.R15.+40.)+10000.)(28.+65?000.R15.)))P,(28.(10.R16.+40.)(2>.VhAR,))P,(5.$21.(2:.R17.+4.)=)P,(2;.VCS,R18.+40.)P,(30.(28.(10.R19.+40.)R1:.)(28.(10.R1<.+1000.)R19.))P,(>.$?.R1>.(10.R1=.(23.+80.R18.))(11.$12.(14.(1;.&40.$2<.))(15.$12.)))P,(>.$?.R1?.(10.(10.R1>.(23.+80.R19.))+10.)(11.$12.(14.(1;.&40.R17.))(15.$12.)))P,(>.$?.R20.(10.(10.R1?.(23.+80.R1:.))+48.)(11.$12.(14.R26.)(15.$12.)))P,(36.$?.R21.(10.R1>.(23.+4.(2?.R19.R1:.)))R18.)P,(36.$?.R22.R1>.R18.)P,(2=.R23.R27.R28.R36.R35.R34.R33.R32.R31.R30.R2?.R2>.R2=.R2<.R2;.R2:.)P,(26.$?.R24.R1?.(10.R28.-80.))P,(28.(2>.VhAR,)R20.)P,(28.R21.(2?.R2:.+80.))P,(28.R2;.(29.+2.+3?.))P,(5.$21.(2:.R2<.+10.)=)P,(2;.VCS,R24.(2?.R2=.R24.))P,(1?.(11.(20.$21.$21.)(22.$21.$21.R25.R2>.)(11.(20.$21.$21.)(22.$21.$21.(10.R29.(23.+80.R24.))(10.(10.R29.(23.+80.R24.))+8.))(11.(20.$21.$21.)(22.$21.$21.(10.(10.R29.(23.+80.R24.))+10.)(10.(10.R29.(23.+80.R24.))+18.))(11.(20.$21.$21.)(22.$21.$21.(10.(10.R29.(23.+80.R24.))+48.)(10.(10.R29.(23.+80.R24.))+50.))(11.(20.$21.$21.)(22.$21.$21.R26.(10.R26.(23.+4.R23.)))R1?.)))))R2;.R2:.)P,(24.$?.R2<.R2;.)P,(25.$?.R2<.)(31.$?.VAL,VCS,(37.R31.R49.R48.R47.R42.R41.R40.R3?.R3>.R3=.R3<.R3;.R3:.R39.R38.R37.R36.R35.R34.R30.R2?.R2<.R29.(10.R2:.(23.+4.(2?.R25.R26.)))R28.R27.R26.(2?.R25.R26.)R24.R23.R22.R2>.)(19.(39.R4:.R31.R49.R48.R2<.R2;.R29.R2:.R27.R26.R47.R46.R45.R44.R43.R42.R41.)R30.(1;.&40.+4<9:8.)R2?.(1=.(2.&40.))R2=.(1>.$?.)))")
(* [comment removed for export] *).
  Proof.
    intros ra gp tp s2 s10 s11 t3 t4 t5 t6 q11 q10 q9 q8 q7 q6 q5 q4 q3 q2 q1 q0 qra stw j0
      SP F fc m0 m RI T FA CH lo c n nf ws ds W R0 R1 RAL RCS HC HN HNF LWS LDS F0 F1 FAL FCS C0 C1 CAL CCS CSEP
      MX NF STC HS HD FR ST LOIMG SPL SPH SPA SCS MU WM MI.
    facts. unfold gf_locked, gf_frame, A_INSTANCE in *.
    (* [comment removed for export] *)
    zstep. zstep. if_cases K; zify_cond K. { exfalso. clear - K HNF HN. lia. }
    zstep. zstep. zstep. if_cases K2; zify_cond K2. { exfalso. clear - K2 HN. lia. }
    eapply gf_tail with (nf := nf - n); try eassumption; try lia.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Definition gf_miss_regs (SP : Z) (gp tp : word) (RI T CH FA c n nf : Z) (s10 s11 t3 t4 t5 t6 : word) : bvmap 5 word := ltac2:(CDefT.buildp (gd_tbl_AW_GetFrom ()) "(1:.(1;.&40.+4<;14.)(1;.&40.(10.O10.-80.))O?.O>.(1;.&40.=)(1;.&40.$2<.)(1;.&40.=)(1;.&40.(10.O=.(23.+80.O9.)))(1;.&40.$38.)(1;.&40.$38.)(1;.&40.(10.O<.+:=0.))(1;.&40.O9.)(1;.&40.(10.O=.(23.+80.O9.)))(1;.&40.(2?.O8.O7.))(1;.&40.O7.)(1;.&40.-1.)(1;.&40.=)(1;.&40.(10.(10.O=.(23.+80.O9.))+8.))(1;.&40.(29.+2.+3=.))(1;.&40.O:.)(1;.&40.O;.)(1;.&40.O8.)(1;.&40.$2<.)(1;.&40.+5=<.)(1;.&40.+=???????????????.)O6.O5.O4.O3.O2.O1.)")
(* [comment removed for export] *).

  Local Ltac2 Set LiaOrc.tbl := fun () => "0060?L17618170671.40L17731333800.38L22014186727.38L31475289507.40L59314923118.4 L61927706159.4000000I00V00c00m01901FS3hAR2RI1n2nf2R02HN3HNF1KS3hAR2RI1c2HCS3hAR2RI1c2HCS3hAR2RI1cS1n2nf3HNF1KS3hAR2RI1n2HN". (* [comment removed for export] *)
  Lemma gf_miss : ltac2:(CDefT.buildp (gd_tbl_AW_GetFrom ()) "Pra,(2.&40.)Pgp,(2.&40.)Ptp,(2.&40.)Ps2,(2.&40.)Ps10,(2.&40.)Ps11,(2.&40.)Pt3,(2.&40.)Pt4,(2.&40.)Pt5,(2.&40.)Pt6,(2.&40.)PSP,$21.PF,(27.&5.(2.&40.))Pfc,(2.&20.)Pm,P,(2.&40.)(8.(2.&8.))PRI,$21.PT,$21.PFA,$21.PCH,$21.Pc,$21.Pn,$21.Pnf,$21.P,(28.+65?000.R7.)P,(28.(10.R8.+1000.)(2>.VhAR,))P,(5.$21.(2:.R9.+1000.)=)P,(2;.VCS,R:.+1000.)P,(18.(28.+1.R7.)(28.R7.+1?.))P,(18.(28.+1.R7.)(28.R7.+10.))P,(18.(28.=R7.)(34.R7.R8.))P,(>.$?.R?.(10.(10.R>.(23.+80.R:.))+10.)(11.$12.(14.(1;.&40.R8.))(15.$12.)))P,(25.$?.R10.)(31.$?.VAL,VCS,Lms',$16.(5.$16.R1.(19.(3:.R15.R1>.R1=.R11.R10.R>.R?.R=.R<.R;.R1;.R1:.R19.R18.R17.R16.)R14.(1;.&40.$3;.)R13.(1=.(2.&40.))R12.(1>.$?.)))(19.(39.R1>.R14.R1=.R1<.R10.R?.R=.R>.R<.R;.R1;.R1:.R19.R18.R17.R16.R15.)R13.(1;.&40.+4<9:8.)R12.(1=.(2.&40.))R11.(1>.$?.)))")
(* [comment removed for export] *).
  Proof.
    intros ra gp tp s2 s10 s11 t3 t4 t5 t6 SP F fc m RI T FA CH c n nf R0 R1 RAL RCS HC HN HNF NF MI.
    facts. unfold gf_locked, gf_miss_regs, A_INSTANCE, A_POPULATE in *.
    (* [comment removed for export] *)
    zstep. zstep. if_cases K; zify_cond K. 2:{ exfalso. clear - K HNF. lia. }
    zstep. zstep. zstep. zstep. zstep. zstep. zstep.
    apply evtA_done. reflexivity.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00E0?L17624452240.93L17718711091.89L17725009036.88L22020445891.88L22026742140.89L22991783080.97L29012665503.92L31475289507.93L31475289507.94L35722035376.97L42650174943.97L45331638039.94L49698585326.96L49715598868.97L51139731036.95L53860346783.94L59308628433.4 L59314923118.3 L61929812368.93L66782819793.97L67241155624.9400001101Q02102Q03103f04L04o05R06c08408W09C0;20;X0<@0<M0<U0=90=n0>US3hAR2SP2RI2FA2CH2lo1n2nf2ws2ds2R02HN3HNF3LWS3LDS2F05LOIMG3SPL2K2S3hAR2RI1c1n2ws2ds2HC2HN3LWS3LDSS3hAR2RI1c1n2ws2ds2HC2HN3LWS3LDSS3hAR2RI1c1n2ws2ds2HC2HN3LWS3LDSS3hAR2RI1c1n2ws2ds2HC2HN3LWS3LDSS3hAR2SP2RI2FA2CH1c1n2nf2ws2ds3LWS3LDS2HB5Ha_st5Hl_stS3hAR2SP2RI2FA2CH1n1r2ws2ds2HR3LWS3LDSS3hAR2SP2RI2FA2CH1c1n2ws2ds3LWS3LDSS3hAR2SP2RI2FA2CH1c1n2ws2ds3LWS3LDSS3hAR2SP2RI2FA2CH2lo1c1n2nf2ws2ds2R02HC2HN3LWS3LDS2F02F15LOIMG3SPL2HB5Ha_st5Hl_stS3hAR2SP2RI2FA2CH2lo1c1n2nf2ws2ds2R02R12HC2HN3LWS3LDS2F05LOIMG3SPL2HB5Ha_st5Hl_stS3hAR2SP2RI2FA2CH1c1n2ws2ds3LWS3LDSS3hAR2SP2RI2FA2CH1c1n2ws2ds3LWS3LDS2HB5Ha_stS3hAR2SP2RI2FA2CH2lo1c1n2nf1r2ws2ds2R03RAL2HC2HN2HR3LWS3LDS2F02F12C03CAL4CSEP5LOIMG3SPL3SPA1K2K22HB5Ha_st5Hl_stS3hAR2SP2RI2FA2CH1c1n2ws2ds3LWS3LDS2HBS3hAR2SP2RI2FA2CH1n2nf2ws2ds3HNF3LWS3LDSS1n2nf3HNF2K2S1r2HR1KS3hAR2SP2RI2FA2CH1n2ws2ds2HN3LWS3LDSS3hAR2SP2RI2FA2CH1c1n2nf2ws2ds3LWS3LDS2HB5Ha_st5Hl_stS3hAR2SP2RI2FA2CH1n2nf2ws2ds3LWS3LDS2F1". (* [comment removed for export] *)
  Lemma gf_pop_ok : ltac2:(CDefT.buildp (gd_tbl_AW_GetFrom ()) "Pgp,(2.&40.)Ptp,(2.&40.)Pt0,(2.&40.)Pt1,(2.&40.)Pt2,(2.&40.)Pa1,(2.&40.)Pa2,(2.&40.)Pa3,(2.&40.)Pa4,(2.&40.)Pa5,(2.&40.)Pa6,(2.&40.)Pa7,(2.&40.)Ps10,(2.&40.)Ps11,(2.&40.)Pt3,(2.&40.)Pt4,(2.&40.)Pt5,(2.&40.)Pt6,(2.&40.)Pq11,(2.&40.)Pq10,(2.&40.)Pq9,(2.&40.)Pq8,(2.&40.)Pq7,(2.&40.)Pq6,(2.&40.)Pq5,(2.&40.)Pq4,(2.&40.)Pq3,(2.&40.)Pq2,(2.&40.)Pq1,(2.&40.)Pq0,(2.&40.)Pqra,(2.&40.)Pstw,(2.&40.)Pj0,(1.(2.&8.))PSP,$21.PF,(27.&5.(2.&40.))Pfc,(2.&20.)Pm0,P,(2.&40.)(8.(2.&8.))Pm,P,(2.&40.)(8.(2.&8.))PRI,$21.PFA,$21.PCH,$21.Plo,$21.Pc,$21.Pn,$21.Pnf,$21.Pr,$21.Pws,(1.(2.&40.))Pds,(1.(2.&40.))PW,(1.(20.$21.$21.))P,(28.+65?000.R;.)P,(28.(10.R<.+1000.)(2>.VhAR,))P,(5.$21.(2:.R=.+1000.)=)P,(2;.VCS,R>.+1000.)P,(18.(28.+1.R;.)(28.R;.+1?.))P,(18.(28.+1.R;.)(28.R;.+10.))P,(18.(28.R<.R;.)(34.R;.(29.+2.+3?.)))P,(18.(34.=R;.)(34.R;.(29.+2.+40.)))P,(5.$0.(4.(2.&40.)R;.)(35.R>.))P,(5.$0.(4.(2.&40.)R;.)#10.)P,(28.+65?000.R14.)P,(28.(10.R15.(23.+4.R10.))R16.)P,(5.$21.(2:.R16.+4.)=)P,(2;.VCS,(10.R17.(23.+4.(2?.R12.R13.)))(23.+4.R13.))P,(18.(28.+1000.R17.)(30.(28.(10.R17.+40.)+10000.)(28.+65?000.R17.)))P,(28.(10.R18.+40.)(2>.VhAR,))P,(5.$21.(2:.R19.+4.)=)P,(2;.VCS,R1:.+40.)P,(30.(28.(10.R1;.+40.)R1<.)(28.(10.R1=.+1000.)R1;.))P,(>.$?.R1?.(10.R1>.(23.+80.R1:.))(11.$12.(14.(1;.&40.$2<.))(15.$12.)))P,(>.$?.R20.(10.(10.R1?.(23.+80.R1;.))+10.)(11.$12.(14.(1;.&40.R19.))(15.$12.)))P,(>.$?.R21.(10.(10.R20.(23.+80.R1<.))+48.)(11.$12.(14.R27.)(15.$12.)))P,(36.$?.R22.(10.R20.(23.+4.(2?.R1;.R1<.)))R19.)P,(36.$?.R23.R20.R19.)P,(2=.R24.R28.R29.R37.R36.R35.R34.R33.R32.R31.R30.R2?.R2>.R2=.R2<.R2;.)P,(26.$?.R25.R21.(10.R29.-80.))P,(28.(2>.VhAR,)R22.)P,(28.R23.(2?.R2;.+80.))P,(28.R2<.(29.+2.+3?.))P,(5.$21.(2:.R2=.+10.)=)P,(2;.VCS,R26.(2?.R2>.R26.))P,(1?.(11.(20.$21.$21.)(22.$21.$21.R27.R2?.)(11.(20.$21.$21.)(22.$21.$21.(10.R2:.(23.+80.R26.))(10.(10.R2:.(23.+80.R26.))+8.))(11.(20.$21.$21.)(22.$21.$21.(10.(10.R2:.(23.+80.R26.))+10.)(10.(10.R2:.(23.+80.R26.))+18.))(11.(20.$21.$21.)(22.$21.$21.(10.(10.R2:.(23.+80.R26.))+48.)(10.(10.R2:.(23.+80.R26.))+50.))(11.(20.$21.$21.)(22.$21.$21.R28.(10.R28.(23.+4.R25.)))R20.)))))R2<.R2;.)P,(24.$?.R2=.R2<.)P,(25.$?.R2=.)(31.$?.VAL,VCS,(37.R32.R53.R52.(1;.&40.(10.(10.R2=.(23.+80.R29.))+8.))R43.R42.R41.R40.R3?.R3>.R3=.R3<.R3;.R3:.R39.R38.R37.R36.R35.R31.R30.R2=.R2;.(10.R2<.(23.+4.(2?.R27.R28.)))R2:.R29.R28.(2?.R27.R28.)R25.R24.R23.R2?.)(19.(1:.(1;.&40.+4<;14.)(1;.&40.(10.R32.-80.))R53.R52.R51.R50.R4?.(1;.&40.(10.R2=.(23.+80.R29.)))(1;.&40.$38.)(1;.&40.R26.)R4>.R4=.R4<.R4;.R4:.R49.R48.(1;.&40.(10.(10.R2=.(23.+80.R29.))+8.))(1;.&40.(29.+2.+3=.))(1;.&40.R2<.)(1;.&40.R2;.)(1;.&40.R28.)(1;.&40.$2<.)(1;.&40.+5=<.)(1;.&40.+=???????????????.)R47.R46.R45.R44.R43.R42.)R31.(1;.&40.+4<;14.)R30.(1=.(2.&40.))R2>.(1>.$?.)))")
(* [comment removed for export] *).
  Proof.
    intros gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s10 s11 t3 t4 t5 t6 q11 q10 q9 q8 q7 q6 q5 q4 q3 q2 q1 q0 qra stw j0
      SP F fc m0 m RI FA CH lo c n nf r ws ds W R0 R1 RAL RCS HC HN HNF HR LWS LDS F0 F1 FAL FCS C0 C1 CAL CCS CSEP
      MX NF STC HS HD FR ST LOIMG SPL SPH SPA SCS MU WM MI.
    facts. unfold A_INSTANCE, gf_frame in *.
    (* [comment removed for export] *)
    zstep. if_cases K; zify_cond K. { exfalso. clear - K HR. lia. }
    zstep. zstep. zstep. if_cases K2; zify_cond K2. { exfalso. clear - K2 HNF. lia. }
    zstep. zstep. zstep. zstep. zstep.
    eapply gf_tail with (nf := nf - n); try eassumption; try lia.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0030?L11746208578.72L8541916066.72 L9071244600.72 00000;00Y014S3hAR2SP2RIS3hAR2SP2RI2lo2R02R15LOIMG3SPLS3hAR2SP2RI2lo2R15LOIMG3SPL". (* [comment removed for export] *)
  Lemma gf_pop_no : ltac2:(CDefT.buildp (gd_tbl_AW_GetFrom ()) "Pgp,(2.&40.)Ptp,(2.&40.)Pt0,(2.&40.)Pt1,(2.&40.)Pt2,(2.&40.)Pa1,(2.&40.)Pa2,(2.&40.)Pa3,(2.&40.)Pa4,(2.&40.)Pa5,(2.&40.)Pa6,(2.&40.)Pa7,(2.&40.)Ps4,(2.&40.)Ps5,(2.&40.)Ps6,(2.&40.)Ps7,(2.&40.)Ps8,(2.&40.)Ps9,(2.&40.)Ps10,(2.&40.)Ps11,(2.&40.)Pt3,(2.&40.)Pt4,(2.&40.)Pt5,(2.&40.)Pt6,(2.&40.)Pq11,(2.&40.)Pq10,(2.&40.)Pq9,(2.&40.)Pq8,(2.&40.)Pq7,(2.&40.)Pq6,(2.&40.)Pq5,(2.&40.)Pq4,(2.&40.)Pq3,(2.&40.)Pq2,(2.&40.)Pq1,(2.&40.)Pq0,(2.&40.)Pqra,(2.&40.)Pj0,(1.(2.&8.))PSP,$21.PF,(27.&5.(2.&40.))Pfc,(2.&20.)Pm0,P,(2.&40.)(8.(2.&8.))Pm,P,(2.&40.)(8.(2.&8.))PRI,$21.Plo,$21.Pc,$21.PW,(1.(20.$21.$21.))P,(28.+65?000.R4.)P,(28.(10.R5.+1000.)(2>.VhAR,))P,(5.$21.(2:.R6.+1000.)=)P,(2;.VCS,R7.+1000.)P,(18.(28.+1.R6.)(28.R6.+1?.))P,(>.$?.R:.(10.R9.(23.+80.R7.))(11.$12.(14.(1;.&40.$2<.))(15.$12.)))P,(2=.R;.R?.R10.R1=.R1<.R1;.R1:.R19.R18.R17.R16.R15.R14.R13.R12.R11.)P,(26.$?.R<.R:.(10.R10.-80.))P,(28.(2>.VhAR,)R;.)P,(28.R<.(2?.R12.+80.))P,(28.R13.(29.+2.+3?.))P,(5.$21.(2:.R14.+10.)=)P,(2;.VCS,R?.(2?.R15.R?.))P,(1?.(11.(20.$21.$21.)(22.$21.$21.R10.R16.)(11.(20.$21.$21.)(22.$21.$21.(10.R11.(23.+80.R?.))(10.(10.R11.(23.+80.R?.))+8.))R>.))R13.R12.)P,(24.$?.R14.R13.)P,(25.$?.R14.)(31.$?.VAL,VCS,(32.R19.R3?.R3>.(1;.&40.(10.(10.R14.(23.+80.R12.))+8.))R29.R28.R27.R26.R25.R24.R23.R22.R21.R20.R1?.R1>.R1=.R1<.R1;.R18.R17.R14.R13.R12.=R11.R16.R15.)(19.(1:.(1;.&40.+4<;14.)(1;.&40.(10.R19.-80.))R3?.R3>.R3=.R3<.R3;.(1;.&40.(10.R14.(23.+80.R12.)))(1;.&40.$38.)(1;.&40.=)R3:.R39.R38.R37.R36.R35.R34.(1;.&40.(10.(10.R14.(23.+80.R12.))+8.))(1;.&40.(29.+2.+3=.))R33.R32.R31.R30.R2?.R2>.R2=.R2<.R2;.R2:.R29.R28.)R18.(1;.&40.+4<;14.)R17.(1=.(2.&40.))R15.(1>.$?.)))")
(* [comment removed for export] *).
  Proof.
    intros gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 q11 q10 q9 q8 q7 q6 q5 q4 q3 q2 q1 q0 qra j0
      SP F fc m0 m RI lo c W R0 R1 RAL RCS HC MX FR ST LOIMG SPL SPH SPA SCS MU WM MI.
    facts. unfold A_INSTANCE in *.
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep.
    eapply gf_unlock; try eassumption; try lia.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)


  (* [comment removed for export] *)
  Definition gfA_post (SP : Z) (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (RI T CH FA c n lo : Z) (m0 : mem) : machine_state -> Prop := ltac2:(CDefT.buildp (gd_tbl_AW_GetFrom ()) "Lms',$16.(17.P,(2.&40.)(8.(2.&8.))Lm',P,(2.&40.)(8.(2.&8.))(17.(1.(2.&8.))Lj0,(1.(2.&8.))(18.(5.$16.R3.(19.(39.O1=.O1>.O1<.O1;.O8.O7.O6.O5.O4.O3.O18.O10.O?.O>.O=.O<.O;.)O:.(1;.&40.+4<9:8.)O9.(1=.(2.&40.))R2.(1>.$?.)))(18.(1?.(11.(20.$21.$21.)(22.$21.$21.O2.O1>.)(11.(20.$21.$21.)(22.$21.$21.(10.O8.(23.+80.O4.))(10.(10.O8.(23.+80.O4.))+8.))(15.(20.$21.$21.))))O1.R2.)(18.(24.$?.O1.R2.)(18.(25.$?.R2.)(18.(>.$?.R2.(10.O8.(23.+80.O4.))(11.$12.(14.(1;.&40.$2<.))(15.$12.)))(18.(2=.R2.O1>.R1.O?.O10.O11.O12.O13.O14.O15.O16.O17.O18.O19.O1:.O1=.)(26.$?.R2.O2.(10.O1>.-80.))))))))))")
(* [comment removed for export] *).

  Local Ltac2 Set LiaOrc.tbl := fun () => "00H0?L10068631391.82L15298127905.77L16591383828.82L17080503348.3 L32425370599.60L33589648154.77L35915399150.79L3610213998.1  L4013141321.81 L44286360852.82L46331482901.80L46336247955.2 L48968216031.80L49698585326.81L51491908006.66L57403674488.77L58253762808.79L63954132868.7 L65240530208.80L65938724504.1 L67211343756.79L6876240317.77 L7959120739.80 L9255691938.3  00000d01@02702@02R02S02c02g03203i04904?04R04k05C05M06>06V07;07?07O07Y07i082S3hAR2SP2SB2RI2lo1c3SB05LOIMG3SPL3RB12HB5Ha_st5Hl_stS3hAR2SB2RI1c3SB03HRI2HC3RB1S3hAR2SP2SB2RI2lo1c3SB03HRI2HC5LOIMG3SPL2HB5Ha_st5Hl_stS2RI1c2HCS3hAR2SP2SB2lo3SPLFS3hAR2SP2SB2RI1cS2SPS3hAR2SP2SBS3hAR2SP2SB2RI2lo1c3SB03HRI2HC5LOIMG3SPL2HB5Ha_st5Hl_stS3hAR2SP2SB2RI1cS2RI1cS3hAR2SP2SB2RI1c2HBS3hAR2SP2SB2RI1c2HB5Ha_stS3hAR2SP2SB2RI2lo1c1y2HyS3hAR2RI1cS3hAR2SP2SB2RI2lo1c3SB04SBAL3HRI2HC5LOIMG3SPL3SPAS3hAR2SB2RI1c3SB13HRI2HCS3hAR2SP2SB2FA2lo1c3SB03HFA5LOIMG3SPLS2SPS3hAR2SP2SB2RI1cS3hAR2RI1cS3hAR2SP2SB2RI1cS2RI1c2HC". (* [comment removed for export] *)
  Lemma gf_A : ltac2:(CDefT.buildp (gd_tbl_AW_GetFrom ()) "Pra,(2.&40.)Pgp,(2.&40.)Ptp,(2.&40.)Pt0,(2.&40.)Pt1,(2.&40.)Pt2,(2.&40.)Ps0,(2.&40.)Ps1,(2.&40.)Pa5,(2.&40.)Pa6,(2.&40.)Pa7,(2.&40.)Ps2,(2.&40.)Ps3,(2.&40.)Ps4,(2.&40.)Ps5,(2.&40.)Ps6,(2.&40.)Ps7,(2.&40.)Ps8,(2.&40.)Ps9,(2.&40.)Ps10,(2.&40.)Ps11,(2.&40.)Pt3,(2.&40.)Pt4,(2.&40.)Pt5,(2.&40.)Pt6,(2.&40.)PSP,$21.PF,(27.&5.(2.&40.))Pfc,(2.&20.)Pm,P,(2.&40.)(8.(2.&8.))PT,$21.PSB,$21.PRI,$21.PFA,$21.PCH,$21.Plo,$21.Pc,$21.Pn,$21.P,(28.+65?000.R7.)P,(28.(10.(10.R8.(29.+2.+25.))+1000.)(2>.VhAR,))P,(5.$21.(2:.R9.+1000.)=)P,(5.$21.R9.(10.R:.(29.+2.+25.)))P,(2;.VCS,R:.+1000.)P,(5.$21.R:.(10.(10.R<.(23.R7.(29.+2.+20.)))+>0000000.))P,(28.=R>.)P,(28.(10.R?.+1000.)(29.+2.+2?.))P,(18.(28.=R<.)(34.R<.(29.+2.+40.)))P,(18.(28.+1.R;.)(28.R;.+1?.))P,(18.(28.+1.R;.)(28.R;.+10.))P,(3<.$?.R14.(10.$38.+20.)(11.$12.(14.(1;.&40.R12.))(15.$12.)))P,(3<.$?.R15.(10.$38.+30.)(11.$12.(14.(1;.&40.R12.))(15.$12.)))P,(>.$?.R16.(10.R13.(23.+80.R?.))(11.$12.(14.(1;.&40.=))(15.$12.)))P,(26.$?.R17.R11.R1:.)P,(28.(2>.VhAR,)R12.)P,(28.R13.(2?.R1<.+80.))P,(28.R1=.(29.+2.+3?.))P,(5.$21.(2:.R1>.+10.)=)P,(2;.VCS,R16.(2?.R1?.R16.))P,(25.$?.R1=.)(31.$?.VAL,VCS,(3=.R21.R3:.R39.R38.R34.R33.R2?.R2>.R2=.R2<.R2;.R2:.R29.R28.R27.R26.R25.R24.R23.R22.R20.R1?.R1;.R1=.R19.R1:.R17.R16.R18.R1>.)(19.(1:.R3:.(1;.&40.R21.)R39.R38.R37.R36.R35.R34.R33.(1;.&40.$38.)(1;.&40.(10.R1=.+:=0.))(1;.&40.R17.)(1;.&40.R19.)(1;.&40.R16.)R32.R31.R30.R2?.R2>.R2=.R2<.R2;.R2:.R29.R28.R27.R26.R25.R24.R23.R22.)R20.(1;.&40.$3>.)R1?.(1=.(2.&40.))R1>.(1>.$?.)))")
(* [comment removed for export] *).
  Proof.
    intros ra gp tp t0 t1 t2 s0 s1 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 SP F fc m T SB RI FA CH lo c n
      SB0 SB1 SBAL HRI RICS HFA T0 T1 HCH HC HN SBC RIC MX ST LOIMG SPL SPH SPA SCS MI.
    pose proof (cs_ok_sb _ _ CSOK) as SB64. pose proof ALWF as ALWF'; unfold al_wf in ALWF'. pose proof IMG as IMG'; unfold asan_img_ok in IMG'.
    unfold A_GETFROM, A_INSTANCE, gf_locked, kWriterLock in *. change (1074072 + 32) with 1074104 in *. change (1074072 + 48) with 1074120 in *.
    change (2^60) with 1152921504606846976. change (2^61) with 2305843009213693952. change (2^40) with 1099511627776.
    pose proof (munch_refl [(lo, SP); (RI + 128 * c, RI + 128 * c + 8)] m) as MU. pose proof (wmono_refl asegs m) as WM. lx_aceil.
    assert (RB1 : RI + 128 * c + 8 <= ACEIL) by (clear -SB1 HRI HC; lia).
    assert (RCS : crange CS (RI + 128 * c) 8) by (eapply crange_sub; [exact RICS| clear -HC; lia| clear -HC; lia]).
    (* [comment removed for export] *)
    lx_run (PLAN [0x4c900] [] 60%N).
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep. zstep.
    lx_fold_mkR. lx_junk_under lo (SP + -104) 24%nat j0 FRa.
    apply evtA_done. unfold gfA_post, gf_locked, gf_frame, kWriterLock, A_INSTANCE.
    change (2^60) with 1152921504606846976. change (2^61) with 2305843009213693952. change (2^40) with 1099511627776.
    lx_exs; lx_ands; [ lx_mseq | lx_munchx | assumption .. | | lx_rwx FRa | assumption ];
      match goal with K : rw_cells _ _ _ [C8 (Z_to_bv 64 1152921504606846976)] |- _ => lx_rwx K end.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
End GetFrom.

End ARUN_1.
