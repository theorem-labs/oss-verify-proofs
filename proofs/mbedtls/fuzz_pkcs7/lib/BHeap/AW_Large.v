(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Arr Asn1Aux CellsX.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import AModel.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import AW_Unwind AW_Unwind2 AW_MmapFixed AW_MmapAnon AW_Poison.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import AW_ClassId AW_Combined AW_Refill AW_GetFrom AW_Populate.
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
Import OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.LxhSyntax. #[local] Instance lxh_tab : OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.lx_hints := OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.lxh_parse "P0205c14d1ceed289 0 4 0 16 20 16 22 16 23 16P02a79f37892e03e1 1 1 16 2 1 1 23 1 5 17 1 21 1 22 1 24 1 25 16P030819c356f28cf7 0 4 0 16 20 16 22 16 23 16P0333c552ef29b677 1 1 16 2 1 1 23 1 5 17 1 21 1 22 1 24 1 25 16P034e22c1cb0daeac 0 4 0 16 20 16 22 16 23 16P0390f22c588ab8ff 0 4 0 16 20 16 22 16 23 16P03e484b1e0531191 1 1 16 2 1 1 23 1 5 17 1 21 1 22 1 24 1 25 16P041294e82799bca2 1 1 4096 2 0 1 24 1 6 12 1 16 1 17 1 19 1 23 1 25 4096P057ef65e72a1a3aa 0 4 0 16 20 16 22 16 23 16P05ec26c21131c522 1 1 16 2 1 1 23 1 5 17 1 21 1 22 1 24 1 25 16P05f720bfec3130a9 1 2 16 2 0 1 24 1 16 2 1 1 23 1 2 25 1 26 1P061bf027f1530628 0 8 0 4096 16 4096 17 4096 19 4096 23 4096 24 4096 25 4096 26 4096P063acb5c795d9bd9 1 1 16 2 1 1 23 1 5 17 1 21 1 22 1 24 1 25 16P065532125461a45d 0 4 0 1 10 1 12 1 13 1P07093d468519283f 1 2 16 2 0 1 24 1 16 2 1 1 23 1 2 25 1 26 1P084fe8f2333c830b 1 2 4096 2 0 1 23 1 4096 2 20 1 24 1 2 25 1 26 1P0b61f4fb74477f8f 1 1 4096 2 18 1 20 1 3 0 1 19 1 21 4096P0b63ac7fc3d5f606 0 2 0 1 12 1P0b6ca490f79f1c1b 0 4 0 16 20 16 22 16 23 16P0b87e6d51cd951ef 0 4 0 16 20 16 22 16 23 16P0b8aa75c758a016d 0 4 0 1 10 1 12 1 13 1P0bce34aa6a7b5a57 1 2 16 2 0 1 24 1 16 2 1 1 23 1 2 25 1 26 1P0bd6b73903b79bec 1 1 16 2 1 1 23 1 5 17 1 21 1 22 1 24 1 25 16P0c64eb522eea4ff7 0 4 0 1 10 1 12 1 13 1P0e815e3eab5ac8bb 0 4 0 16 20 16 22 16 23 16P10156f1aab73d535 1 1 16 2 1 1 23 1 5 17 1 21 1 22 1 24 1 25 16P10541dd1d4b52721 1 1 16 2 1 1 23 1 5 17 1 21 1 22 1 24 1 25 16P1115243d6a8ff3c5 0 4 0 16 20 16 22 16 23 16P11200363888ea427 1 1 16 2 1 1 23 1 5 17 1 21 1 22 1 24 1 25 16P12c0f47c42a487a9 1 1 16 2 1 1 23 1 5 17 1 21 1 22 1 24 1 25 16P14104f0abc974bd0 0 4 0 16 20 16 22 16 23 16P14ac0ad9f996a566 0 4 0 16 20 16 22 16 23 16P166302930739a43f 0 4 0 16 20 16 22 16 23 16P17a74bae380a3f11 0 7 0 4096 10 4096 14 4096 15 4096 17 4096 19 4096 20 4096P18a288825e534c9e 0 4 0 16 20 16 22 16 23 16P1a19f32c0b2ffc9b 1 1 16 2 1 1 23 1 5 17 1 21 1 22 1 24 1 25 16P1a280172060ae348 0 4 0 16 20 16 22 16 23 16P1b22f3cd6d0bcc4a 1 2 16 2 0 1 24 1 16 2 1 1 23 1 2 25 1 26 1P1b27fe6991c697a3 0 4 0 16 20 16 22 16 23 16P1b660b6a028ba1cf 1 1 16 2 1 1 23 1 5 17 1 21 1 22 1 24 1 25 16P1be54a05af5ad6cb 1 2 16 2 0 1 24 1 16 2 1 1 23 1 2 25 1 26 1P1e563b16a089e249 1 1 16 2 1 1 23 1 5 17 1 21 1 22 1 24 1 25 16P207275396c516d7f 0 4 0 1 10 1 12 1 13 1P20e47a452894d6f5 0 4 0 1 10 1 12 1 13 1P21f9039e1eb23f86 0 4 0 16 20 16 22 16 23 16P2355078261f46377 0 4 0 1 10 1 12 1 13 1P26d9494b19442f68 0 4 0 16 20 16 22 16 23 16P28888810afa0a284 0 4 0 16 20 16 22 16 23 16P29100c5b29300cee 0 4 0 16 20 16 22 16 23 16P292491931c4eecdb 1 2 16 2 0 1 24 1 16 2 1 1 23 1 2 25 1 26 1P29938422b7ecaad2 0 4 0 16 20 16 22 16 23 16P2a1da3dc03bcdb42 0 4 0 1 10 1 12 1 13 1P2b5b3f418b6f3806 0 2 0 1 19 1P2b9cbf6e92053d32 0 4 0 16 20 16 22 16 23 16P2ba6e54e73a4bb46 0 2 0 1 11 1P2bad26611b79f5b2 1 1 16 2 1 1 23 1 5 17 1 21 1 22 1 24 1 25 16P2cbd7ec891df9bbe 0 4 0 16 20 16 22 16 23 16P2d77adc24ebc2b0a 0 4 0 1 10 1 12 1 13 1P2dbb2be47422dabf 1 2 16 2 0 1 24 1 16 2 1 1 23 1 2 25 1 26 1P2e3923bf916a9978 1 1 16 2 1 1 23 1 5 17 1 21 1 22 1 24 1 25 16P2e7346eb3d98795d 0 4 0 16 20 16 22 16 23 16P2e7c033711ec62f0 0 4 0 16 20 16 22 16 23 16P2f582b0293e39e08 1 2 4096 2 0 1 19 1 4096 2 18 1 20 1 2 21 1 22 1P30a991bf6cc2f26c 1 1 16 2 1 1 23 1 5 17 1 21 1 22 1 24 1 25 16P316ecf99f540d4f8 1 1 16 2 1 1 23 1 5 17 1 21 1 22 1 24 1 25 16P317228feedd5cda5 0 4 0 1 10 1 12 1 13 1P32e6604fb8c5c59b 1 1 16 2 1 1 23 1 5 17 1 21 1 22 1 24 1 25 16P336c2439eed5853d 0 4 0 16 20 16 22 16 23 16P3381d52212f29d87 1 2 16 2 0 1 24 1 16 2 1 1 23 1 2 25 1 26 1P34fc546732ab8a47 0 4 0 16 20 16 22 16 23 16P358d3abd2a82dbb5 1 1 16 2 1 1 23 1 5 17 1 21 1 22 1 24 1 25 16P35c3495e4161c719 0 4 0 16 20 16 22 16 23 16P360c300448d9b881 0 4 0 1 10 1 12 1 13 1P3618eb8762419770 0 4 0 16 20 16 22 16 23 16P36ec009ebf49a31c 0 4 0 1 10 1 12 1 13 1P370ac09b3fc09041 1 2 16 2 0 1 24 1 16 2 1 1 23 1 2 25 1 26 1P380e3dd1e4912fae 1 1 16 2 1 1 23 1 5 17 1 21 1 22 1 24 1 25 16P389eda7fb99a77a1 0 4 0 1 10 1 12 1 13 1P3ac3142b421c7a4f 1 1 16 2 1 1 23 1 5 17 1 21 1 22 1 24 1 25 16P3afc3f01170ee1d1 0 4 0 16 20 16 22 16 23 16P3b94cf3fae86b380 0 4 0 16 20 16 22 16 23 16P3bfd11abfd377658 1 3 4096 2 20 1 24 1 8 3 0 1 23 1 25 1 8 2 12 1 26 1 3 27 512 28 1 29 1P3cae43df09991d93 1 1 16 2 1 1 23 1 5 17 1 21 1 22 1 24 1 25 16P3cf4a478d724109f 1 2 16 2 0 1 24 1 16 2 1 1 23 1 2 25 1 26 1P3dc1a6ef28842136 0 4 0 16 20 16 22 16 23 16P3ec05bd16c4db353 1 1 16 2 1 1 23 1 5 17 1 21 1 22 1 24 1 25 16P3ee1b0a96dddc100 0 4 0 16 20 16 22 16 23 16P3f4817350dfa936d 0 4 0 16 20 16 22 16 23 16N090664e0ff27715dN10d91c6a8cd386f1N1899841294812cc2N1b20662088e6a2eeN24ce45922fd16d06N24fcc93eb75d074dN3565bc0cf527b29aN3756048a76470947N3e206a94c6c1f1e3N3ecbf0d3008faa82"%lxh.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import LiaOrc. (* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= orc_lia. (* [comment removed for export] *)
Local Ltac dlia ::= orc_dlia. (* [comment removed for export] *)
Local Ltac plia ::= orc_plia. (* [comment removed for export] *)
Local Ltac clear_disj ::= fc_clear_disj. (* [comment removed for export] *)
Local Ltac prune_disj ::= fc_prune_disj. (* [comment removed for export] *)
Ltac2 gd_tbl_AW_Large () : Init.string Init.list := ["Corelib.Init.Logic.and"; "RocqVerifyHarness.AgentSubmission.Lib.Step.ro_cells"; "RocqVerifyHarness.AgentSubmission.B.AImg.asegs"; "Stdlib.ZArith.BinInt.Z.add"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.A_INSTANCE"; "Corelib.Init.Datatypes.cons"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.cell"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C8"; "stdpp.bitvector.definitions.Z_to_bv"; "Corelib.Init.Datatypes.nil"; "ARUN_1.A_GOT_LNAME"; "ARUN_1.A_LNAME_CELL"; "ARUN_1.A_LNAME"; "Corelib.Init.Datatypes.list"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.ivl"; "stdpp.bitvector.definitions.bv"; "Corelib.Init.Datatypes.option"; "Corelib.Numbers.BinNums.Z"; "ARUN_1.large_statics"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.munch"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.disjoint_from"; "Stdlib.ZArith.BinInt.Z.le"; "Corelib.Init.Logic.iff"; "Corelib.Init.Logic.eq"; "Corelib.Init.Datatypes.bool"; "Stdlib.ZArith.BinInt.Z.testbit"; "Corelib.Init.Datatypes.true"; "Corelib.Init.Logic.ex"; "Stdlib.ZArith.BinInt.Z.lor"; "Stdlib.ZArith.BinInt.Z.shiftr"; "RocqVerifyHarness.AgentSubmission.Lib.Arr.u64arr"; "Corelib.Init.Datatypes.app"; "Stdlib.ZArith.BinInt.Z.mul"; "Stdlib.ZArith.BinInt.Z.of_nat"; "Corelib.Init.Datatypes.length"; "RocqVerifyHarness.AgentSubmission.Lib.Step.rw_cells"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.CB"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.machine_state"; "RocqVerifyHarness.AgentSubmission.Lib.MState.MS"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.mkR"; "ARUN_1.Large.map_size"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_MmapAnon.A_MMAP_ANON_TOL"; "Corelib.Init.Datatypes.None"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.seg_rom"; "Corelib.Init.Datatypes.prod"; "Corelib.Init.Datatypes.pair"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.wmono"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.mem_inv"; "ARUN_1.Large.large_frame"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.stk"; "LinuxProcessSemantics.Riscv.Prelude.bvmap"; "Stdlib.ZArith.BinInt.Z.lt"; "Stdlib.ZArith.BinInt.Z.pow"; "RocqVerifyHarness.AgentSubmission.AHeap.ACeil.ACEIL"; "Stdlib.ZArith.BinInt.Z.sub"; "Stdlib.ZArith.BinInt.Z.modulo"; "RocqVerifyHarness.AgentSubmission.LibA.ALazy.crange"; "RocqVerifyHarness.AgentSubmission.LibA.AEvtA.evtA"; "ARUN_1.Large.largeA_post"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_Combined.A_LARGE_ALLOC"; "RocqVerifyHarness.AgentSubmission.Lib.MState.ret_pc"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_Poison.A_POISON"; "Stdlib.ZArith.BinInt.Z.log2"; "stdpp.bitvector.definitions.bv_unsigned"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C4"; "Corelib.Init.Logic.or"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_Populate.thr_statics"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_Unwind2.A_TP"; "ARUN_1.Large.largeD_post"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C1"; "Corelib.Lists.ListDef.map"; "Corelib.Init.Datatypes.nat"; "ARUN_1.Large.largeE_post"; "Corelib.Init.Logic.not"; "ARUN_1.A_MAPORDIE"].

Section ARUN_1. Context {hAR : arun}.
Set Printing Width 250.

Definition A_GOT_LNAME : Z := 0x0f5e38.     (* [comment removed for export] *)
Definition A_LNAME_CELL : Z := 0x0f7d08.    (* [comment removed for export] *)
Definition A_LNAME : Z := 0x1b4ab.
Definition A_MAPORDIE : Z := 0x0852f4.      (* [comment removed for export] *)

(* [comment removed for export] *)
Definition large_statics (m : mem) (PA : Z) : Prop := ltac2:(CDefT.buildp (gd_tbl_AW_Large ()) "(0.(1.$2.O2.(3.$4.+40.)(5.$6.(7.(8.&40.+1000.))(5.$6.(7.(8.&40.O1.))(5.$6.(7.(8.&40.O1.))(9.$6.)))))(0.(1.$2.O2.$:.(5.$6.(7.(8.&40.$;.))(9.$6.)))(1.$2.O2.$;.(5.$6.(7.(8.&40.$<.))(9.$6.)))))")
(* [comment removed for export] *).

Lemma large_statics_transport : ltac2:(CDefT.buildp (gd_tbl_AW_Large ()) "PW,(=.$>.)Pm,P,(?.&40.)(10.(?.&8.))Pm',P,(?.&40.)(10.(?.&8.))PPA,$11.P,(12.R3.R1.)P,(13.R5.R4.R3.)P,(14.R6.(3.$4.+40.)+18.)P,(14.R7.$:.+8.)P,(14.R8.$;.+8.)(12.R7.R6.)")
(* [comment removed for export] *).
Proof.
  intros W m m' PA (S1 & S2 & S3) MU D1 D2 D3. unfold large_statics.
  repeat split; (eapply ro_cells_transport; [eassumption| exact MU| cbn; assumption]).
Qed.

(* [comment removed for export] *)
Fixpoint zallP (P : Z -> Prop) (lo : Z) (n : nat) : Prop :=
  match n with O => True | S n' => P lo /\ zallP P (lo + 1) n' end.
Local Ltac2 Set LiaOrc.tbl := fun () => "0020?L12763751414.6 L44836931205.1000000;00IS1P2lo1k2HkS1n2lo1k2Hk2NE". (* [comment removed for export] *)
Lemma zallP_spec : forall P n lo, zallP P lo n -> forall k, lo <= k < lo + Z.of_nat n -> P k.
Proof.
  intros P n. induction n as [|n IH]; intros lo H k Hk; [cbn in Hk; lia|].
  destruct H as [H0 H1]. destruct (Z.eq_dec k lo) as [->|NE]; [exact H0|].
  apply (IH (lo + 1) H1). rewrite Nat2Z.inj_succ in Hk. lia.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

(* [comment removed for export] *)
Definition reach (v s R : Z) : Prop := ltac2:(CDefT.buildp (gd_tbl_AW_Large ()) "Pi,$11.P,(15.=R1.)(16.(17.$18.(19.O2.R2.)$1:.)(1;.$11.Ld,$11.(0.(0.(15.=R1.)(15.R1.O1.))(17.$18.(19.O3.(3.R3.R1.))$1:.))))")
(* [comment removed for export] *).

Local Ltac2 Set LiaOrc.tbl := fun () => "0020>L61841564948.7L7386141759.5 000006007S1d2HdS". (* [comment removed for export] *)
Lemma reach_0 : forall v, reach v v 0.
Proof.
  intros v i Hi. split.
  - intros H. exists 0. rewrite Z.add_0_r. split; [lia| exact H].
  - intros (d & Hd & H). replace d with 0 in H by lia. rewrite Z.add_0_r in H. exact H.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

Local Ltac2 Set LiaOrc.tbl := fun () => "0070?L10351595562.8 L1677967979.12 L1828729658.8  L46674951710.11L48230358721.12L5054383104.12 L57439218878.1100000600=00H00P00Z00d00oS1i2HiS1R1i1dS1R2HR1i2HiS1R1d2HdS1R1d2Hd1lS1R1d2Hd1gS1R2HR1d2Hd". (* [comment removed for export] *)
Lemma reach_step : forall v s R, 0 <= R -> reach v s R -> reach v (Z.lor s (Z.shiftr s (R + 1))) (2 * R + 1).
Proof.
  intros v s R HR H i Hi. rewrite Z.lor_spec, Z.shiftr_spec by lia. rewrite Bool.orb_true_iff.
  rewrite (H i Hi). rewrite (H (i + (R + 1)) ltac:(lia)). split.
  - intros [(d & Hd & Hb)|(d & Hd & Hb)]; [exists d; split; [lia| exact Hb]|].
    exists (R + 1 + d). split; [lia|]. rewrite Z.add_assoc. exact Hb.
  - intros (d & Hd & Hb). destruct (Z_le_gt_dec d R).
    + left. exists d. split; [lia| exact Hb].
    + right. exists (d - (R + 1)). split; [lia|]. replace (i + (R + 1) + (d - (R + 1))) with (i + d) by lia. exact Hb.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

Definition smear (v : Z) : Z := ltac2:(CDefT.buildp (gd_tbl_AW_Large ()) "Zs1,$11.(1<.O1.(1=.O1.+1.))Zs2,$11.(1<.R1.(1=.R1.+2.))Zs4,$11.(1<.R1.(1=.R1.+4.))Zs8,$11.(1<.R1.(1=.R1.+8.))Zs16,$11.(1<.R1.(1=.R1.+10.))(1<.R1.(1=.R1.+20.))")
(* [comment removed for export] *).

Local Ltac2 Set LiaOrc.tbl := fun () => "0060>L15045117442.3L28720315290.7L29784466396.5L52329334427.6L6755919165.4 L7224918809.8 000001002003004005006SSSSSS". (* [comment removed for export] *)
Lemma smear_reach : forall v, reach v (smear v) 63.
Proof.
  intros v. unfold smear.
  pose proof (reach_0 v) as H0.
  pose proof (reach_step v _ 0 ltac:(lia) H0) as H1. cbn [Z.mul Z.add Pos.add Pos.mul] in H1.
  pose proof (reach_step v _ 1 ltac:(lia) H1) as H2. cbn [Z.mul Z.add Pos.add Pos.mul Pos.succ] in H2.
  pose proof (reach_step v _ 3 ltac:(lia) H2) as H3. cbn [Z.mul Z.add Pos.add Pos.mul Pos.succ] in H3.
  pose proof (reach_step v _ 7 ltac:(lia) H3) as H4. cbn [Z.mul Z.add Pos.add Pos.mul Pos.succ] in H4.
  pose proof (reach_step v _ 15 ltac:(lia) H4) as H5. cbn [Z.mul Z.add Pos.add Pos.mul Pos.succ] in H5.
  pose proof (reach_step v _ 31 ltac:(lia) H5) as H6. cbn [Z.mul Z.add Pos.add Pos.mul Pos.succ] in H6.
  exact H6.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

Local Ltac2 Set LiaOrc.tbl := fun () => "0090?L18874421619.9 L41394733440.9 L48479015785.13L51544884264.9 L54240393276.9 L54240430616.5 L54240453450.13L65966469307.5 L803628894.9   00000>00C00P00[00a00g00m01301>S1v2K11n2Hn2LTS1v1nS1v1n2GE1d2HdS1v1n2Hn2LTS1v2HvS1v2HvS1v2HvS1v2HvS1v2K01n2GE". (* [comment removed for export] *)
Lemma smear_spec : forall v, 0 < v < 2^64 -> smear v = 2 ^ (Z.log2 v + 1) - 1.
Proof.
  intros v Hv. pose proof (smear_reach v) as R.
  pose proof (Z.log2_nonneg v) as K0.
  assert (K1 : Z.log2 v < 64). { apply Z.log2_lt_pow2; lia. }
  change (2 ^ (Z.log2 v + 1) - 1) with (Z.pred (2 ^ (Z.log2 v + 1))). rewrite <- Z.ones_equiv.
  apply Z.bits_inj'. intros n Hn.
  destruct (Z_lt_le_dec n (Z.log2 v + 1)) as [LT|GE].
  - rewrite Z.ones_spec_low by lia.
    apply (proj2 (R n Hn)). exists (Z.log2 v - n). split; [lia|]. replace (n + (Z.log2 v - n)) with (Z.log2 v) by lia.
    apply Z.bit_log2. lia.
  - rewrite Z.ones_spec_high by lia.
    destruct (Z.testbit (smear v) n) eqn:E; [| reflexivity]. exfalso.
    destruct (proj1 (R n Hn) E) as (d & Hd & Hb).
    rewrite Z.bits_above_log2 in Hb; [discriminate| lia| lia].
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

Local Ltac2 Set LiaOrc.tbl := fun () => "0030>L31291349257.6L38651714916.6L67504247318.600000700>00DS2l12l2S2l12l2S1A2l1". (* [comment removed for export] *)
Lemma u64arr_app : ltac2:(CDefT.buildp (gd_tbl_AW_Large ()) "Pm,P,(?.&40.)(10.(?.&8.))PA,$11.Pl1,(=.(?.&40.))Pl2,(=.(?.&40.))(16.(1>.$2.R4.R3.(1?.(?.&40.)R2.R1.))(0.(1>.$2.R4.R3.R2.)(1>.$2.R4.(3.R3.(20.+8.(21.(22.(?.&40.)R2.))))R1.)))")
(* [comment removed for export] *).
Proof.
  intros m A l1 l2. unfold u64arr. rewrite u64s_app, app_length.
  pose proof (bytes_at_app asegs m A (u64s l1) (u64s l2)) as BA. rewrite u64s_length in BA.
  replace (A + Z.of_nat (8 * length l1)) with (A + 8 * Z.of_nat (length l1)) in BA by lia.
  replace (8 * Z.of_nat (length l1 + length l2)) with (8 * Z.of_nat (length l1) + 8 * Z.of_nat (length l2)) by lia.
  rewrite (wr_at_app asegs m A (8 * Z.of_nat (length l1)) (8 * Z.of_nat (length l2))) by lia.
  tauto.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

Section Large.
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
  Definition large_frame (m : mem) (SP : Z) (j0 : list byte) (q9 q8 q7 q6 q5 q4 q3 q2 q1 q0 qra : word) : Prop := ltac2:(CDefT.buildp (gd_tbl_AW_Large ()) "(23.$2.O>.(3.O=.-60.)(5.$6.(24.#8.O<.)(5.$6.(7.O;.)(5.$6.(7.O:.)(5.$6.(7.O9.)(5.$6.(7.O8.)(5.$6.(7.O7.)(5.$6.(7.O6.)(5.$6.(7.O5.)(5.$6.(7.O4.)(5.$6.(7.O3.)(5.$6.(7.O2.)(5.$6.(7.O1.)(9.$6.))))))))))))))")
(* [comment removed for export] *).

  Definition map_size (x : Z) : Z := (x + 4095) / 4096 * 4096 + 4096.

  (* [comment removed for export] *)
  Definition largeA_post (SP : Z) (gp tp t0 t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 a4 a5 a6 a7 ra : word)
      (F : bvmap 5 word) (fc : bv 32) (x lo : Z) (j0 : list byte) (m0 : mem) : machine_state -> Prop := ltac2:(CDefT.buildp (gd_tbl_AW_Large ()) "Lms',$25.(1;.P,(?.&40.)(10.(?.&8.))Lm',P,(?.&40.)(10.(?.&8.))(0.(17.$25.R2.(26.(27.(8.&40.+4<39<.)(8.&40.(3.O21.-60.))O20.O1?.O1>.O1=.O1<.(8.&40.(3.$4.+2;0.))(8.&40.(3.$4.+40.))(8.&40.(28.O4.))(8.&40.$<.)(8.&40.=)(8.&40.+8.)O;.O:.O9.O8.(8.&40.(28.O4.))(8.&40.O4.)O17.(8.&40.+8.)O15.O14.(8.&40.+7.)O12.O11.O10.O?.O>.O=.O<.)O6.(8.&40.$29.)O5.(2:.(?.&40.))R1.(2;.$2.)))(0.(13.(5.(2<.$11.$11.)(2=.$11.$11.O3.O21.)(9.(2<.$11.$11.)))O1.R1.)(0.(2>.$2.O1.R1.)(0.(2?.$2.R1.)(0.(30.R1.O21.O2.O12.O13.O14.O15.O16.O17.O18.O19.O1:.O1;.O7.)(31.$2.R1.O3.(3.O21.-60.))))))))")
(* [comment removed for export] *).

  Local Ltac2 Set LiaOrc.tbl := fun () => "0090?L14303310215.4 L16426443713.2 L18926750396.2 L18930958230.3 L53934581604.49L59308579152.50L64586698136.1 L65867461961.66L8335086958.1  00000;00A00B00E00T01:01>01F01JS1x2Hx1H2H0S1x2HxSS1xS3hAR2SP2lo3SPLS3hAR2SP1x2lo2Hx5LOIMG3SPL3SPA3MSZ3LXES2SPS3hAR2SPS2SP". (* [comment removed for export] *)
  Lemma large_A : ltac2:(CDefT.buildp (gd_tbl_AW_Large ()) "Pra,(?.&40.)Pgp,(?.&40.)Ptp,(?.&40.)Pt0,(?.&40.)Pt1,(?.&40.)Pt2,(?.&40.)Ps0,(?.&40.)Ps1,(?.&40.)Pa4,(?.&40.)Pa5,(?.&40.)Pa6,(?.&40.)Pa7,(?.&40.)Ps2,(?.&40.)Ps3,(?.&40.)Ps4,(?.&40.)Ps5,(?.&40.)Ps6,(?.&40.)Ps7,(?.&40.)Ps8,(?.&40.)Ps9,(?.&40.)Ps10,(?.&40.)Ps11,(?.&40.)Pt3,(?.&40.)Pt4,(?.&40.)Pt5,(?.&40.)Pt6,(?.&40.)PSP,$11.PF,(32.&5.(?.&40.))Pfc,(?.&20.)Pm,P,(?.&40.)(10.(?.&8.))Px,$11.PPA,$11.Plo,$11.P,(0.(33.+10000.R3.)(15.R3.(34.+2.+28.)))P,(0.(15.=R3.)(33.R3.(34.+2.+40.)))P,(12.R6.R4.)P,(31.$2.R7.R4.R:.)P,(15.(35.VhAR,)R5.)P,(15.R6.(36.R<.+60.))P,(15.R=.(34.+2.+3?.))P,(17.$11.(37.R>.+10.)=)P,(38.VCS,R9.(36.R?.R9.))P,(2?.$2.R=.)(39.$2.VAL,VCS,Lms',$25.(1;.(=.(?.&8.))Lj0,(=.(?.&8.))(3:.R13.R2<.R2;.R2:.R29.R28.R27.R26.R21.R20.R1?.R1>.R1=.R1<.R1;.R1:.R19.R18.R17.R16.R15.R14.R25.R24.R23.R22.R2=.R12.R11.R?.R=.R1.R10.R2.))(26.(27.R2;.(8.&40.R11.)R2:.R29.R28.R27.R26.R25.R24.(8.&40.(3.$4.+40.))(8.&40.(3.$4.+2;0.))(8.&40.R=.)(8.&40.+8.)R23.R22.R21.R20.R1?.R1>.R1=.R1<.R1;.R1:.R19.R18.R17.R16.R15.R14.R13.R12.)R10.(8.&40.$3;.)R?.(2:.(?.&40.))R>.(2;.$2.)))")
(* [comment removed for export] *).
  Proof.
    intros ra gp tp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 SP F fc m x PA lo
      Hx HPA LS ST LOIMG SPL SPH SPA SCS MI.
    destruct LS as (LS1 & LS2 & LS3).
    unfold A_LARGE_ALLOC, A_INSTANCE, A_GOT_LNAME, A_LNAME_CELL, A_LNAME, A_MMAP_ANON_TOL in *.
    change (1074072 + 64) with 1074136 in *. change (1074072 + 688) with 1074760 in *.
    pose proof (munch_refl [(lo, SP)] m) as MU. pose proof (wmono_refl asegs m) as WM. lx_aceil.
    assert (MSZ : x + 4096 <= map_size x < x + 8192).
    { unfold map_size. clear - Hx. pose proof (Z.div_mod (x + 4095) 4096 ltac:(lia)). pose proof (Z.mod_pos_bound (x + 4095) 4096 ltac:(lia)). lia. }
    (* [comment removed for export] *)
    lx_run (PLAN [A_MMAP_ANON_TOL] [] 60%N).
    all: rewrite ?lxw_land_m4096 in * by (clear -Hx; lia); change ((x + 4095) / 4096 * 4096 + 4096) with (map_size x) in *.
    all: lx_deads.
    lx_junk_under lo (SP + -88) 8%nat j0 FRa.
    apply evtA_done. exists j0. unfold largeA_post, large_frame, A_INSTANCE, A_LNAME, A_MMAP_ANON_TOL.
    change (1074072 + 64) with 1074136. change (1074072 + 688) with 1074760.
    lx_exs; lx_ands; [ lx_mseq | assumption .. | lx_rwx FRa | assumption ].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma large_null : ltac2:(CDefT.buildp (gd_tbl_AW_Large ()) "Pgp,(?.&40.)Ptp,(?.&40.)Pt0,(?.&40.)Pt1,(?.&40.)Pt2,(?.&40.)Ps0,(?.&40.)Ps1,(?.&40.)Pa1,(?.&40.)Pa2,(?.&40.)Pa3,(?.&40.)Pa4,(?.&40.)Pa5,(?.&40.)Pa6,(?.&40.)Pa7,(?.&40.)Ps2,(?.&40.)Ps3,(?.&40.)Ps4,(?.&40.)Ps5,(?.&40.)Ps6,(?.&40.)Ps7,(?.&40.)Ps8,(?.&40.)Ps9,(?.&40.)Ps10,(?.&40.)Ps11,(?.&40.)Pt3,(?.&40.)Pt4,(?.&40.)Pt5,(?.&40.)Pt6,(?.&40.)Pj0,(=.(?.&8.))Pq9,(?.&40.)Pq8,(?.&40.)Pq7,(?.&40.)Pq6,(?.&40.)Pq5,(?.&40.)Pq4,(?.&40.)Pq3,(?.&40.)Pq2,(?.&40.)Pq1,(?.&40.)Pq0,(?.&40.)Pqra,(?.&40.)PSP,$11.PF,(32.&5.(?.&40.))Pfc,(?.&20.)Pm0,P,(?.&40.)(10.(?.&8.))Pm,P,(?.&40.)(10.(?.&8.))Plo,$11.PW,(=.(2<.$11.$11.))P,(30.R3.R7.R13.R12.R11.R10.R?.R>.R=.R<.R;.R:.R9.R8.)P,(31.$2.R4.R3.(3.R8.-60.))P,(15.(35.VhAR,)R4.)P,(15.R5.(36.R:.+60.))P,(15.R;.(34.+2.+3?.))P,(17.$11.(37.R<.+10.)=)P,(38.VCS,R8.(36.R=.R8.))P,(13.(5.(2<.$11.$11.)(2=.$11.$11.R9.R>.)R8.)R;.R:.)P,(2>.$2.R<.R;.)P,(2?.$2.R<.)(39.$2.VAL,VCS,Lms',$25.(1;.P,(?.&40.)(10.(?.&8.))Lm',P,(?.&40.)(10.(?.&8.))(0.(17.$25.R2.(26.(27.R14.(8.&40.R13.)R3;.R3:.R39.R38.R37.R15.R16.(8.&40.=)R34.R33.R32.R31.R30.R2?.R2>.R17.R18.R19.R1:.R1;.R1<.R1=.R1>.R25.R24.R23.R22.R21.R20.)R12.(3<.R14.)R11.(2:.(?.&40.))R1.(2;.$2.)))(0.(13.(5.(2<.$11.$11.)(2=.$11.$11.R>.R13.)R=.)R10.R1.)(0.(2>.$2.R10.R1.)(0.(2?.$2.R1.)(31.$2.R1.R>.R13.))))))(26.(27.(8.&40.+4<39<.)(8.&40.(3.R11.-60.))R39.R38.R37.R36.R35.R34.R33.(8.&40.=)R32.R31.R30.R2?.R2>.R2=.R2<.R2;.R2:.R29.R28.R27.R26.R25.R24.R23.R22.R21.R20.R1?.R1>.)R10.(8.&40.+4<39<.)R?.(2:.(?.&40.))R=.(2;.$2.)))")
(* [comment removed for export] *).
  Proof.
    intros gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 j0 q9 q8 q7 q6 q5 q4 q3 q2 q1 q0 qra SP F fc m0 m lo W
      FR ST LOIMG SPL SPH SPA SCS MU WM MI.
    unfold large_frame in FR. lx_aceil.
    (* [comment removed for export] *)
    lx_run (PLAN [] [] 20%N). lx_same. lx_post.
  Qed.

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0070?L14303310215.4 L17210349934.2 L18926750396.2 L18930958230.3 L3405010124.57 L62507283238.57L66095738813.5200000;00<00=00@00O00^01AS1x2Hx1H2H0SSS1xS3hAR1a1x2H72H3S3hAR1a1x2H72H3S3hAR1a1x2Hx2A03AAL3lxv2H32H42H52H7". (* [comment removed for export] *)
  Lemma large_B : ltac2:(CDefT.buildp (gd_tbl_AW_Large ()) "Pgp,(?.&40.)Ptp,(?.&40.)Pt0,(?.&40.)Pt1,(?.&40.)Pt2,(?.&40.)Pa1,(?.&40.)Pa2,(?.&40.)Pa3,(?.&40.)Pa4,(?.&40.)Pa5,(?.&40.)Pa6,(?.&40.)Pa7,(?.&40.)Ps4,(?.&40.)Ps6,(?.&40.)Ps7,(?.&40.)Ps9,(?.&40.)Ps10,(?.&40.)Ps11,(?.&40.)Pt3,(?.&40.)Pt4,(?.&40.)Pt5,(?.&40.)Pt6,(?.&40.)PSP,$11.PF,(32.&5.(?.&40.))Pfc,(?.&20.)Pm,P,(?.&40.)(10.(?.&8.))Pa,$11.Px,$11.PPA,$11.P,(0.(33.+10000.R2.)(15.R2.(34.+2.+28.)))P,(17.$11.(37.R3.+8.)=)P,(33.=R5.)P,(17.$11.(37.R6.+1000.)=)P,(15.(3.R7.(28.R6.))(35.VhAR,))P,(0.(15.=R6.)(33.R6.(34.+2.+40.)))P,(12.R:.R7.)P,(2?.$2.R;.)(39.$2.VAL,VCS,Lms',$25.(1;.(?.&40.)La3',(?.&40.)(1;.(?.&40.)La4',(?.&40.)(1;.(?.&40.)La5',(?.&40.)(1;.(?.&40.)La6',(?.&40.)(1;.(?.&40.)La7',(?.&40.)(17.$25.R6.(26.(27.(8.&40.+4<3?4.)(8.&40.(3.R15.-60.))R2;.R2:.R29.R28.R27.(8.&40.(3.$4.+2;0.))(8.&40.(3.$4.+40.))(8.&40.R11.)(8.&40.+1000.)(8.&40.+?:.)R5.R4.R3.R2.R1.(8.&40.(28.R10.))(8.&40.R10.)(8.&40.R11.)(8.&40.(3.(3.R11.+1000.)R10.))(8.&40.(3.R11.(28.R10.)))(8.&40.(3.(3.R11.+1000.)R10.))(8.&40.+7.)(8.&40.(3.R11.+1000.))R1;.R1:.R19.R18.R17.R16.)R14.(8.&40.$3=.)R13.(2:.(?.&40.))R12.(2;.$2.))))))))(26.(27.(8.&40.+4<39<.)(8.&40.(3.R?.-60.))R25.R24.R23.R22.R21.(8.&40.(3.$4.+2;0.))(8.&40.(3.$4.+40.))(8.&40.R;.)R20.R1?.R1>.R1=.R1<.R1;.R1:.(8.&40.(28.R:.))(8.&40.R:.)R19.(8.&40.+8.)R18.R17.(8.&40.+7.)R16.R15.R14.R13.R12.R11.R10.)R>.(8.&40.+4<39<.)R=.(2:.(?.&40.))R<.(2;.$2.)))")
(* [comment removed for export] *).
  Proof.
    intros gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s4 s6 s7 s9 s10 s11 t3 t4 t5 t6 SP F fc m a x PA
      Hx XAL A0 AAL ACE HPA LS MI.
    destruct LS as (LS1 & LS2 & LS3).
    unfold A_INSTANCE, A_POISON in *.
    change (1074072 + 64) with 1074136 in *. change (1074072 + 688) with 1074760 in *.
    assert (MSZ : x + 4096 <= map_size x < x + 8192).
    { unfold map_size. clear - Hx. pose proof (Z.div_mod (x + 4095) 4096 ltac:(lia)). pose proof (Z.mod_pos_bound (x + 4095) 4096 ltac:(lia)). lia. }
    pose proof (munch_refl ([] : list ivl) m) as MU. pose proof (wmono_refl asegs m) as WM. lx_aceil.
    (* [comment removed for export] *)
    lx_run (PLAN [0x6a55c] [] 40%N).
    all: try (rewrite (Z.land_comm 4095 a) in LXKT; change 4095 with (Z.ones 12) in LXKT; rewrite Z.land_ones in LXKT by (clear -A0; lia);
              change (2 ^ 12) with 4096 in LXKT; rewrite AAL in LXKT; cbv in LXKT; discriminate LXKT).
    (* [comment removed for export] *)
    match goal with K : ?v mod 2 ^ Z.of_N 3 = 0 |- _ => is_var v;
      assert (EV : v = a + 4096) by (change (2 ^ Z.of_N 3) with 8 in *; lx_arith); subst v end.
    lx_same. apply evtA_done. do 5 eexists. lx_mseq.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0060?L14303310215.4 L18926750396.2 L18930958230.3 L54843905380.39L7806021768.39 L7988171038.39 00000;00<00?00H00_016S1x2Hx1H2H0SS1xS3hAR1a1xS3hAR1a1x2Hx2A03ACE3MSZS3hAR1a1x2Hx2A03ACE3MSZ". (* [comment removed for export] *)
  Lemma large_C : ltac2:(CDefT.buildp (gd_tbl_AW_Large ()) "Pgp,(?.&40.)Ptp,(?.&40.)Pt0,(?.&40.)Pt1,(?.&40.)Pt2,(?.&40.)Pa0,(?.&40.)Pa1,(?.&40.)Pa2,(?.&40.)Pa3,(?.&40.)Pa4,(?.&40.)Pa5,(?.&40.)Pa6,(?.&40.)Pa7,(?.&40.)Ps10,(?.&40.)Ps11,(?.&40.)Pt3,(?.&40.)Pt4,(?.&40.)Pt5,(?.&40.)Pt6,(?.&40.)PSP,$11.PF,(32.&5.(?.&40.))Pfc,(?.&20.)Pm,P,(?.&40.)(10.(?.&8.))Pa,$11.Px,$11.P,(0.(33.+10000.R1.)(15.R1.(34.+2.+28.)))P,(33.=R3.)P,(15.(3.R4.(28.R3.))(35.VhAR,))P,(2?.$2.R6.)(39.$2.VAL,VCS,Lms',$25.(17.$25.R1.(26.(27.(8.&40.+4<404.)(8.&40.(3.R;.-60.))R1>.R1=.R1<.R1;.R1:.(8.&40.(3.$4.+2;0.))(8.&40.(3.$4.+40.))(8.&40.(3.(3.R7.+1000.)R6.))(8.&40.(36.(36.(28.R6.)+1000.)R6.))(8.&40.+?:.)R16.R15.R14.R13.R12.(8.&40.(28.R6.))(8.&40.R6.)(8.&40.R7.)(8.&40.(3.(3.R7.+1000.)R6.))(8.&40.(3.R7.(28.R6.)))(8.&40.(3.(3.R7.+1000.)R6.))(8.&40.+7.)(8.&40.(3.R7.+1000.))R11.R10.R?.R>.R=.R<.)R:.(8.&40.$3=.)R9.(2:.(?.&40.))R8.(2;.$2.)))(26.(27.(8.&40.+4<3?4.)(8.&40.(3.R:.-60.))R1=.R1<.R1;.R1:.R19.(8.&40.(3.$4.+2;0.))(8.&40.(3.$4.+40.))R18.R17.R16.R15.R14.R13.R12.R11.(8.&40.(28.R5.))(8.&40.R5.)(8.&40.R6.)(8.&40.(3.(3.R6.+1000.)R5.))(8.&40.(3.R6.(28.R5.)))(8.&40.(3.(3.R6.+1000.)R5.))(8.&40.+7.)(8.&40.(3.R6.+1000.))R10.R?.R>.R=.R<.R;.)R9.(8.&40.+4<3?4.)R8.(2:.(?.&40.))R7.(2;.$2.)))")
(* [comment removed for export] *).
  Proof.
    intros gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s10 s11 t3 t4 t5 t6 SP F fc m a x Hx A0 ACE MI.
    facts. unfold A_INSTANCE, A_POISON in *.
    assert (MSZ : x + 4096 <= map_size x < x + 8192).
    { unfold map_size. clear - Hx. pose proof (Z.div_mod (x + 4095) 4096 ltac:(lia)). pose proof (Z.mod_pos_bound (x + 4095) 4096 ltac:(lia)). lia. }
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep.
    replace (a + map_size x - (a + 4096 + x)) with (map_size x - 4096 - x) by lia.
    apply evtA_done. reflexivity.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Definition largeD_post (SP : Z) (gp tp s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (a x nres ncks T lo : Z) (j1 j2 : word) (m0 : mem) : machine_state -> Prop := ltac2:(CDefT.buildp (gd_tbl_AW_Large ()) "Lms',$25.(1;.(?.&40.)Lt0,(?.&40.)(1;.(?.&40.)Lt1,(?.&40.)(1;.(?.&40.)Lt2,(?.&40.)(1;.(?.&40.)La1,(?.&40.)(1;.(?.&40.)La7,(?.&40.)(1;.(?.&40.)Lt3,(?.&40.)(1;.(?.&40.)Lt4,(?.&40.)(1;.(?.&40.)Lt5,(?.&40.)(1;.(?.&40.)Lt6,(?.&40.)(1;.P,(?.&40.)(10.(?.&8.))Lm',P,(?.&40.)(10.(?.&8.))(0.(17.$25.R;.(26.(27.(8.&40.+4<408.)(8.&40.(3.O10.-60.))O?.O>.R:.R9.R8.(8.&40.(3.$4.+2;0.))(8.&40.(3.$4.+40.))(8.&40.(3.O9.+1000.))R7.(8.&40.+101010101010101.)(8.&40.O6.)(8.&40.O7.)(8.&40.+?0?0?0?0?0?0?0?.)(8.&40.+1010101.)R6.(8.&40.(28.O8.))(8.&40.(36.+3?.(3>.(28.O8.))))(8.&40.O9.)(8.&40.O9.)(8.&40.(3.O9.(28.O8.)))(8.&40.(3.(3.O9.+1000.)O8.))(8.&40.+7.)(8.&40.(3.O9.+1000.))O=.O<.R5.R4.R3.R2.)O;.(8.&40.+4<540.)O:.(2:.(?.&40.))R1.(2;.$2.)))(0.(13.(5.(2<.$11.$11.)(2=.$11.$11.O4.(3.O10.-60.))(5.(2<.$11.$11.)(2=.$11.$11.(3.O5.+;38.)(3.O5.+;48.))(5.(2<.$11.$11.)(2=.$11.$11.O9.(3.O9.+18.))(5.(2<.$11.$11.)(2=.$11.$11.(3.$4.+2:8.)(3.$4.+2:<.))(9.(2<.$11.$11.))))))O1.R1.)(0.(2>.$2.O1.R1.)(0.(2?.$2.R1.)(0.(23.$2.R1.(3.O5.+;38.)(5.$6.(7.(8.&40.(3.(3?.&40.O3.)+1.)))(5.$6.(7.(8.&40.(3.(3?.&40.O2.)(28.O8.))))(9.$6.))))(0.(23.$2.R1.O9.(5.$6.(7.(8.&40.O9.))(5.$6.(7.(8.&40.(28.O8.)))(5.$6.(7.(8.&40.O8.))(9.$6.)))))(0.(23.$2.R1.(3.$4.+2:8.)(5.$6.(40.(8.&40.+1.))(9.$6.)))(31.$2.R1.O4.(3.O10.-60.)))))))))))))))))))")
(* [comment removed for export] *).

  Local Ltac2 Set LiaOrc.tbl := fun () => "02<0?L10262636629.4 L10726706001.78L11038616511.85L11045386737.84L11079629317.82L11540214394.79L125704307.2   L1267004120.81 L1267023997.79 L1268977369.79 L13414600821.85L13435033240.81L14303310215.4 L16957347323.79L1700742443.79 L17212662893.80L17603982810.85L17742345290.80L17853282396.13L18186806761.13L18926750396.2 L18928703304.3 L18930958230.3 L19922925653.4 L20146728913.78L20198158912.86L22700267513.6 L23216336650.80L23531849289.13L23808467220.83L2441161451.76 L2443666511.76 L25161287469.76L2539877399.88 L25410475284.83L25475975479.82L27572083717.3 L27617782269.76L27846297964.3 L28072265099.85L2876012845.76 L28922880535.88L29086109671.79L29205938796.85L29784510841.80L30980822757.86L31148345108.83L33019474529.79L33249240548.6 L33853063162.76L33855041886.76L33949406581.85L34333372241.83L34647151001.79L34896197127.88L35345699383.82L35825681707.79L36454576245.85L38235734261.1 L38972201970.78L39012636437.0 L39082318472.84L39650388730.2 L40715817527.79L40823230957.82L41015213144.13L41216767996.79L41415987435.88L41418004045.82L41418040264.2 L41546866969.76L41905953644.85L4311123308.85 L43750768486.4 L44017345965.82L45664753464.0 L45738460440.13L45970127356.2 L45991520309.13L46213856772.82L47195207543.3 L47945611132.76L48776353769.80L49698585326.82L4970582047.79 L51969890876.79L52041007307.84L52281482767.80L52514160055.82L52701299285.4 L53051764561.0 L53520051328.79L53520196992.76L53522098726.85L53522110982.79L53605516488.78L54740876907.76L5477387713.85 L552331111.76  L55333597309.79L55903709626.79L5594495469.81 L56620056933.14L56688083117.79L56765693885.80L57229756180.83L57244366902.4 L57465546075.85L58027258900.3 L58046225820.85L58242885380.3 L58543055976.9 L59308628304.8 L59308628433.8 L59308628566.4 L59495965233.82L59576967703.88L59641295688.78L60206496545.0 L60437937530.76L61486875100.13L6164945645.78 L62801799482.76L63370343213.82L63654440446.83L63995892957.13L64037467531.85L64352553239.88L65500282541.82L66164932269.79L67113273793.82L67115350510.3 L67115351879.82L6753767613.82 L6755915291.88 L7808205600.81 L7808205729.80 L7985980086.81 L8929214087.88 L9741927532.82 00000A00H00I00X00m00n01801^02E02l03J03[03f03g04404@04A04O04^04k04l04o05205C05J05h06706E06U07;07B07I07N07\08B08N08X08Y08`09309@09N09[0:^0:j0;J0;\0;i0<?0<F0<M0<k0==0=>0=?0=K0=P0=n0>20>90>:0>O0>V0>[0>g0?80?90?G0?S0?T0?U0@00@K0@S0@_0@`0A00A70AP0A\0Af0Ag0B50BL0BM0BN0Bc0C10C=0CN0CO0C]0Ck0D;0DI0DP0DW0Df0E30E40E50EF0EG0ET0F;0Fa0Fi0Fj0G10G20G<0G\0Gk0H;0HH0HT0Hb0Hi0Hj0I10I>0IE0IF0IR0JY0Je0Jl0K:0KF0KK0L50L?0Li0M50MC0Mj0NQ0O80O90O\S3hAR2SP2lo5LOIMGS3hAR1aFS3hAR2SP1a1x2HBS3hAR2SP1a1x4ncks3HNCFS4ncks3HNCS3hAR2SP1a1x2lo2Hx2A03ACE5LOIMG3SPL2K2S3hAR2SP1a1x2lo2Hx2A03ACE5LOIMG3SPL3MSZS3hAR2SP1a1x2lo2Hx2A03ACE5LOIMG3SPL3MSZS3hAR2SP1a1x2A02HB5Ha_st5Hl_stS3hAR2SP1a1x1T2HBS1x2Hx1H2H0FS3hAR2AL4IMG'S3hAR2SP1a1xFS3hAR2SP1a1x1TS3hAR2SP2lo3SPLS3hAR2SP1T2T0SS1aS1xS3hAR2SP2lo5LOIMGS3hAR1aS3hAR2SP1a1x2A02HB5Ha_st5Hl_stS2SP1a1T2lo1x1HS3hAR2SP1a1x1TS3hAR2SP3CTX3CX0S3hAR2j12SP1a1x1T2T02HB5Ha_st5Hl_st2j2S3hAR1TS3hAR1TS3hARS3hAR2SP1a1x1kS3hAR2j12SP1a1x1T2T02HB5Ha_st5Hl_st2j2S3hAR2SP1a1xS1x2Hx3MSZFS2SP2loS3hAR2AL4IMG'1k3K16S3hAR2AL4IMG'S3hAR2SP1a1x1kS3hAR2AL4IMG'S3hAR2SP1a1x1T2lo2Hx3XAL2A04SEPT5LOIMG3SPL3SPA2K12K22HB5Ha_st5Hl_stS3hAR2SP1a1xS3hAR2SP1a1x1T2T02HB5Ha_st5Hl_stS3hAR2SP1a1x2A02HBS3hAR2AL4IMG'S3hAR2SP1T2lo2T15LOIMGS3hAR1TS3hAR1TS3hAR2SP1a1x2A02HB5Ha_st5Hl_stS3hAR2SP1a1x2A02HBFFS3hAR2SP1a1xS3hARS3hAR2SP1a1x2A02HB5Ha_st5Hl_stS2loS3hAR1aSS3hAR2SP1a1x2HB5Ha_stS1k3K16S3hARS3hAR2SP1a1xS3hAR2SP2lo5LOIMGFS3hAR2SP1a1x1kS3hAR2SP1a1xSFS3hAR2SP1a1x2HB5Ha_st5Hl_stS3hAR2SP1a1x2HB5Ha_st5Hl_stS1a2A01HS3hAR2SP1a1xSS3hAR2SP3CTX3CX1S1k3K16S3hAR2SP2lo5LOIMG3SPL3SPAS3hAR2SP1a1xS1x2Hx3MSZFS3hAR2SP1a1x1TS3hAR2SP1a1x1T2HB5Ha_stFFS3hAR2SP1a1x2HB5Ha_stS3hAR2SP1a1x1TS3hAR2SP1a1xS3hAR2SP2lo5LOIMGSS3hAR2AL5ALWF'S3hAR2AL5ALWF'S3hAR2AL5ALWF'1kS3hAR2AL5ALWF'S3hAR1aS3hAR1TS3hAR2AL4IMG'1kS3hAR2AL4IMG'FFS3hAR2SP1a1x1T2HBFS3hAR2AL4IMG'S3hAR2SP1a1x2lo2Hx2A03ACE5LOIMG3SPL3MSZS3hAR2j12SP1a1x1T2T02HB5Ha_st5Hl_st2j2S1a2A01HFS1k3K16FS1x2Hx3MSZS3hAR2SP1a1x2lo2Hx3ACE5LOIMG3MSZS3hAR1a1x2Hx2K1S3hAR1a1x3MSZ2K2S1x2Hx3MSZ2K3S3hAR2SP1a1xS3hAR2SP1a1x1kS3hAR1aSS3hAR1TS3hAR2SP1T2T1S3hAR1aFS3hAR2SP1a1xS3hAR2j12SP1a1x1T2lo2Hx3XAL2A04SEPT5LOIMG3SPL3SPA3MSZ2HB5Ha_st5Hl_st2j2S3hAR2SP3SPHS3hAR1kS3hAR2SP1a1x1kS3hAR2SP1a1xS3hARS3hAR2SP1a1x2lo2Hx2A03ACE5LOIMG3SPL3MSZ2K2S1x2Hx3MSZS3hAR2SP1a1x2lo2Hx2A03ACE5LOIMG3SPL3MSZ2K2S3hAR2SP1a1xS3hAR2SP1a1x1kS3hAR2SP1a1x2lo2Hx2A03ACE5LOIMG3SPL3MSZS3hAR2SP1a1x2lo2Hx2A03ACE5LOIMG3SPL3MSZS3hAR2SP1a1x2lo2Hx2A03ACE5LOIMG3SPL3MSZFS3hAR2SP1a1x2lo2Hx2A05LOIMG3SPL3SPA". (* [comment removed for export] *)
  Lemma large_D : ltac2:(CDefT.buildp (gd_tbl_AW_Large ()) "Pgp,(?.&40.)Ptp,(?.&40.)Pt0,(?.&40.)Pt1,(?.&40.)Pt2,(?.&40.)Pa0,(?.&40.)Pa1,(?.&40.)Pa2,(?.&40.)Pa3,(?.&40.)Pa4,(?.&40.)Pa5,(?.&40.)Pa6,(?.&40.)Pa7,(?.&40.)Ps10,(?.&40.)Ps11,(?.&40.)Pt3,(?.&40.)Pt4,(?.&40.)Pt5,(?.&40.)Pt6,(?.&40.)Pj1,(?.&40.)Pj2,(?.&40.)Pz0,(?.&40.)Pz1,(?.&40.)Pz2,(?.&40.)PSP,$11.PF,(32.&5.(?.&40.))Pfc,(?.&20.)Pm,P,(?.&40.)(10.(?.&8.))Pa,$11.Px,$11.PPA,$11.PT,$11.PCTX,$11.Pnres,$11.Pncks,$11.Plo,$11.P,(0.(33.+10000.R7.)(15.R7.(34.+2.+28.)))P,(17.$11.(37.R8.+8.)=)P,(15.+65?000.R:.)P,(17.$11.(37.R;.+1000.)=)P,(15.(3.R<.(28.R;.))(35.VhAR,))P,(0.(15.=R;.)(33.R;.(34.+2.+40.)))P,(0.(15.=R8.)(33.R8.(34.+2.+14.)))P,(0.(15.=R:.)(33.R:.(34.+2.+40.)))P,(15.+65?000.R<.)P,(15.(3.R=.+10000.)(35.VhAR,))P,(38.VCS,R>.+10000.)P,(0.(15.+1000.R10.)(41.(15.(3.R10.+1000.)+10000.)(15.+65?000.R10.)))P,(15.(3.R11.+1000.)(35.VhAR,))P,(38.VCS,R12.+1000.)P,(41.(15.(3.R16.(28.R15.))R13.)(15.(3.R13.+1000.)R16.))P,(38.VCS,R17.+18.)P,(12.R19.R16.)P,(42.R1:.R15.R16.)P,(17.(?.&40.)R35.(8.&40.$43.))P,(23.$2.R1<.(3.R18.+;38.)(5.$6.(7.R24.)(5.$6.(7.R23.)(9.$6.))))P,(23.$2.R1=.R1<.(5.$6.(7.R23.)(5.$6.(7.R22.)(5.$6.(7.R21.)(9.$6.)))))P,(23.$2.R1>.(3.$4.+2:8.)(5.$6.(40.(8.&40.=))(9.$6.)))P,(23.$2.R1?.(3.$4.+70.)(5.$6.(7.(8.&40.R19.))(5.$6.(7.(8.&40.R18.))(9.$6.))))P,(31.$2.R20.R18.(3.R23.-60.))P,(15.(35.VhAR,)R19.)P,(15.R1:.(36.R25.+80.))P,(15.R26.(34.+2.+3?.))P,(17.$11.(37.R27.+10.)=)P,(38.VCS,R1=.(36.R28.R1=.))P,(2?.$2.R26.)(39.$2.VAL,VCS,(44.R2:.R42.R41.R35.R34.R29.R28.R26.R25.R21.R20.R23.R1?.R2?.R2>.R27.)(26.(27.(8.&40.+4<404.)(8.&40.(3.R2:.-60.))R42.R41.R40.R3?.R3>.(8.&40.(3.$4.+2;0.))(8.&40.(3.$4.+40.))R3=.R3<.R3;.R3:.R39.R38.R37.R36.(8.&40.(28.R25.))(8.&40.R25.)(8.&40.R26.)(8.&40.(3.(3.R26.+1000.)R25.))(8.&40.(3.R26.(28.R25.)))(8.&40.(3.(3.R26.+1000.)R25.))(8.&40.+7.)(8.&40.(3.R26.+1000.))R35.R34.R33.R32.R31.R30.)R29.(8.&40.+4<404.)R28.(2:.(?.&40.))R27.(2;.$2.)))")
(* [comment removed for export] *).
  Proof.
    intros gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s10 s11 t3 t4 t5 t6 j1 j2 z0 z1 z2 SP F fc m a x PA T CTX nres ncks lo
      Hx XAL A0 AAL ACE HPA HNC HNR CX0 CX1 CSCTX T0 T1 CST SEPT CSA LS TS TP TJ HDR MX NRC ST LOIMG SPL SPH SPA SCS MI.
    facts. destruct LS as (LS1 & LS2 & LS3).
    unfold A_INSTANCE in *.
    change (1074072 + 64) with 1074136 in *. change (1074072 + 688) with 1074760 in *. change (1074072 + 680) with 1074752 in *. change (1074072 + 112) with 1074184 in *.
    change (1074072 + 684) with 1074756.
    assert (MSZ : x + 4096 <= map_size x < x + 8192).
    { unfold map_size. clear - Hx. pose proof (Z.div_mod (x + 4095) 4096 ltac:(lia)). pose proof (Z.mod_pos_bound (x + 4095) 4096 ltac:(lia)). lia. }
    pose proof (munch_refl [(lo, SP + -96); (T + 2872, T + 2888); (a, a + 24); (1074752, 1074756)] m) as MU. pose proof (wmono_refl asegs m) as WM.
    (* [comment removed for export] *)
    zstep.
    eapply evtA_cut.
    { eapply (gcts_spec AL IMG ALWF CS CSOK) with (CTX := CTX) (T := T) (lo := lo) (m0 := m) (W := []); try exact TS; try exact TP; try exact MI; try exact ST; try exact CSCTX;
        try apply munch_refl; try apply wmono_refl; try (clear - CX0 CX1 T0 T1 LOIMG SPL SPH SPA; lia).
      eapply crange_sub; [exact SCS| clear; lia| clear - SPL; lia]. }
    cbv beta. intros ms1 (x11 & m1 & -> & MU1 & WM1 & MI1 & ST1).
    replace (ret_pc (Z_to_bv 64 0x4c408)) with (Z_to_bv 64 0x4c408) by (symmetry; apply ret_pc_even; [clear; lia | reflexivity]).
    (* [comment removed for export] *)
    assert (LO1 : forall A n, A + n <= lo \/ SP + -96 <= A -> disjoint_from [(lo, SP + -96)] A n) by (intros A n H; cbn; split; [exact H| exact I]).
    assert (TJ1 : rw_cells asegs m1 (T + 2872) [C8 j1; C8 j2]) by (eapply rw_cells_transport; [exact TJ| exact MU1| exact WM1| apply LO1; cbn; clear - T1 LOIMG; lia]).
    assert (HDR1 : rw_cells asegs m1 a [C8 z0; C8 z1; C8 z2]) by (eapply rw_cells_transport; [exact HDR| exact MU1| exact WM1| apply LO1; cbn; clear - ACE LOIMG MSZ Hx; lia]).
    assert (MX1 : rw_cells asegs m1 1074752 [C4 (Z_to_bv 64 0)]) by (eapply rw_cells_transport; [exact MX| exact MU1| exact WM1| apply LO1; cbn; clear - LOIMG; lia]).
    assert (NRC1 : rw_cells asegs m1 1074184 [C8 (Z_to_bv 64 nres); C8 (Z_to_bv 64 ncks)]) by (eapply rw_cells_transport; [exact NRC| exact MU1| exact WM1| apply LO1; cbn; clear - LOIMG; lia]).
    assert (LS1' : ro_cells asegs m1 1074136 [C8 (Z_to_bv 64 4096); C8 (Z_to_bv 64 PA); C8 (Z_to_bv 64 PA)]) by (eapply ro_cells_transport; [exact LS1| exact MU1| apply LO1; cbn; clear - LOIMG; lia]).
    assert (MU1' : munch [(lo, SP + -96); (T + 2872, T + 2888); (a, a + 24); (1074752, 1074756)] m m1) by (eapply munch_weaken; [| exact MU1]; unfold sub_fp; cbn [outside]; clear; intros; lia).
    clear MU WM TJ HDR MX NRC LS1 LS2 LS3 TS MI ST MU1. rename MU1' into MU. rename WM1 into WM.
    (* [comment removed for export] *)
    zstep. zstep. zstep.
    replace (Z.land (a + 4096) 7) with 0.
    2:{ change 7 with (Z.ones 3). rewrite Z.land_ones by lia. change (2^3) with 8. symmetry. clear - AAL A0. pose proof (Z.div_mod a 4096 ltac:(lia)). rewrite AAL in *.
        replace (a + 4096) with ((512 * (a / 4096) + 512) * 8) by lia. apply Z_mod_mult. }
    zstep. zstep. zstep. zstep. zstep.
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep.
    replace (Z.land 4095 (a + 4096)) with 0.
    2:{ rewrite Z.land_comm. change 4095 with (Z.ones 12). rewrite Z.land_ones by lia. change (2^12) with 4096. symmetry. clear - AAL A0. pose proof (Z.div_mod a 4096 ltac:(lia)). rewrite AAL in *.
        replace (a + 4096) with ((a / 4096 + 1) * 4096) by lia. apply Z_mod_mult. }
    zstep. zstep. if_cases K1; zify_cond K1. { exfalso. rewrite ?unsigned_lit in K1 by (clear - A0 ACE MSZ Hx; lia). clear - K1 A0 ACE MSZ Hx; lia. }
    zstep. if_cases K2; zify_cond K2. { exfalso. rewrite ?unsigned_lit in K2 by (clear - A0 ACE MSZ Hx; lia). clear - K2 A0 ACE MSZ Hx; lia. }
    (* [comment removed for export] *)
    zstep. replace (a + 4096 - 4096) with a by lia.
    zstep. zstep. zstep. zstep. if_cases K3; zify_cond K3. { exfalso. rewrite ?unsigned_lit in K3 by (clear - MSZ Hx; lia). clear - K3 MSZ Hx; lia. }
    (* [comment removed for export] *)
    zstep. zstep. zstep. change (Z.land (1074136 + 616) 18446744073709551612) with 1074752. zstep.
    zstep. zstep. zstep. zstep. zstep. zstep. rewrite (sx32_small 0) by (clear; lia).
    zstep. zstep. change (Z.land 0 255) with 0. zstep.
    (* [comment removed for export] *)
    zstep. zstep. rewrite (Z.shiftr_div_pow2 ncks 20) by (clear; lia). rewrite (Z.div_small ncks (2^20)) by (clear - HNC; lia).
    zstep.
    (* [comment removed for export] *)
    do 24 zstep.
    all: match goal with |- context [TNode (TNode TEmpty (Some ?s3v) TEmpty) (Some (Z_to_bv 64 ?a1v)) (TNode TEmpty (Some ?s11v) TEmpty)] =>
           change a1v with (smear (map_size x)) end.
    assert (K16 : 16 <= Z.log2 (map_size x) <= 41).
    { split. - apply Z.log2_le_pow2; clear - MSZ Hx; lia.
             - apply Z.lt_succ_r. apply Z.log2_lt_pow2; clear - MSZ Hx; lia. }
    rewrite (smear_spec (map_size x)) by (clear - MSZ Hx; lia).
    remember (Z.log2 (map_size x)) as k eqn:Ek.
    remember (2 ^ (k + 1) - 1) as S eqn:ES.
    assert (HS : 0 <= S < 2^64).
    { subst S. split. - pose proof (Z.pow_pos_nonneg 2 (k + 1)). clear - H K16; lia.
      - apply (Z.le_lt_trans _ (2^42 - 1)); [| clear; lia]. apply Z.sub_le_mono_r. apply Z.pow_le_mono_r; clear - K16; lia. }
    (* [comment removed for export] *)
    do 18 zstep.
    all: match goal with |- context [TNode (TNode TEmpty (Some (Z_to_bv 64 ?s3v)) TEmpty) (Some (Z_to_bv 64 ?a1v)) (TNode TEmpty (Some ?s11v) TEmpty)] =>
           replace s3v with (63 - k) end.
    2:{ subst S. clear - K16. pattern k. refine (zallP_spec _ 26%nat 16 _ k _); [| clear - K16; lia].
        vm_compute. repeat (apply conj; [reflexivity|]). exact I. }
    apply evtA_done. unfold largeD_post. subst k. do 10 eexists.
    split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [assumption|].
    split; [eassumption|]. split; [eassumption|]. split; [eassumption|]. eassumption.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition largeE_post (SP : Z) (gp tp s10 s11 q9 q8 q7 q6 q5 q4 q3 q2 q1 q0 qra : word) (F : bvmap 5 word) (fc : bv 32)
      (a x ncks PA T lo : Z) (ps rest : list word) (m0 : mem) : machine_state -> Prop := ltac2:(CDefT.buildp (gd_tbl_AW_Large ()) "Lms',$25.(1;.(?.&40.)Lt0,(?.&40.)(1;.(?.&40.)Lt1,(?.&40.)(1;.(?.&40.)Lt2,(?.&40.)(1;.(?.&40.)La1,(?.&40.)(1;.(?.&40.)La2,(?.&40.)(1;.(?.&40.)La3,(?.&40.)(1;.(?.&40.)La4,(?.&40.)(1;.(?.&40.)La5,(?.&40.)(1;.(?.&40.)La6,(?.&40.)(1;.(?.&40.)La7,(?.&40.)(1;.(?.&40.)Lt3,(?.&40.)(1;.(?.&40.)Lt4,(?.&40.)(1;.(?.&40.)Lt5,(?.&40.)(1;.(?.&40.)Lt6,(?.&40.)(1;.P,(?.&40.)(10.(?.&8.))Lm',P,(?.&40.)(10.(?.&8.))(1;.(=.(?.&40.))Lst,(=.(?.&40.))(1;.(=.(?.&40.))Lbsl',(=.(?.&40.))(1;.(?.&40.)Lg0',(?.&40.)(1;.(?.&40.)Lg1',(?.&40.)(0.(17.$25.R14.(26.(27.O<.(8.&40.O1;.)O1:.O19.R13.R12.R11.O=.O>.(8.&40.(3.O9.+1000.))R10.R?.R>.R=.R<.R;.R:.O?.O10.O11.O12.O13.O14.O15.O16.O18.O17.R9.R8.R7.R6.)O;.(3<.O<.)O:.(2:.(?.&40.))R5.(2;.$2.)))(0.(13.(5.(2<.$11.$11.)(2=.$11.$11.O4.O1;.)(5.(2<.$11.$11.)(2=.$11.$11.(3.O9.+18.)(3.O9.+20.))(5.(2<.$11.$11.)(2=.$11.$11.(3.O6.(20.+8.O7.))(3.(3.O6.(20.+8.O7.))+8.))(5.(2<.$11.$11.)(2=.$11.$11.(3.$4.+78.)(3.(3.$4.+2:8.)+4.))(5.(2<.$11.$11.)(2=.$11.$11.(3.$4.+2<0.)(3.$4.+2=0.))(9.(2<.$11.$11.)))))))O1.R5.)(0.(2>.$2.O1.R5.)(0.(2?.$2.R5.)(0.(23.$2.R5.(3.O9.+18.)(5.$6.(7.(8.&40.O7.))(9.$6.)))(0.(1>.$2.R5.O6.(1?.(?.&40.)O3.(5.(?.&40.)(8.&40.O9.)(9.(?.&40.)))))(0.(1>.$2.R5.(3.O6.(20.+8.(3.O7.+1.)))O2.)(0.(23.$2.R5.(3.$4.+78.)(5.$6.(7.(8.&40.(3.O7.+1.)))(5.$6.(45.(8.&8.=))(9.$6.))))(0.(23.$2.R5.(3.$4.+88.)(46.(?.&40.)$6.$7.R4.))(0.(17.$47.(22.(?.&40.)R4.)#4.)(0.(1>.$2.R5.(3.$4.+:8.)R3.)(0.(17.$47.(22.(?.&40.)R3.)#40.)(0.(23.$2.R5.(3.$4.+2:8.)(5.$6.(40.(8.&40.=))(9.$6.)))(0.(23.$2.R5.(3.$4.+2<0.)(5.$6.(7.R2.)(5.$6.(7.R1.)(9.$6.))))(31.$2.R5.O4.O1;.))))))))))))))))))))))))))))))))))")
(* [comment removed for export] *).

  Local Ltac2 Set LiaOrc.tbl := fun () => "0400@L10809598604.100L10872907332.106L10872907332.107L11045386737.108L11077471363.103L11288172055.103L11394232849.101L11540267610.103L11686069868.109L11859429489.108L12046229132.106L12193263599.105L12801675944.110L12918235703.103L13008144747.103L13657685094.103L13896228156.103L14053080684.106L14303310215.4  L15681710279.106L1628955942.105 L1628955942.108 L16405844412.107L1641522951.108 L16430711495.103L1663335898.103 L1669725563.100 L16901313515.103L1700558091.103 L17054063259.100L17766994603.108L17766994861.106L17902247856.106L18468462857.104L1859877436.103 L18926750396.2  L18930958230.3  L19517046891.103L19537051742.104L19540984947.105L19664886920.105L19664886920.108L19713770348.106L19738046538.100L19746469990.100L19897014862.107L20086806253.101L21008451579.100L21175008748.107L21175008748.108L21219833934.107L21694447438.107L21865918023.103L21876371174.100L22112626156.109L22315715346.108L22852168481.109L23190759991.100L23200803483.100L23808467220.106L23833383598.110L23948370241.104L23952303468.105L24149279528.107L24149279528.110L24473297670.107L24515364181.109L24524590286.107L24819799165.100L24828288081.100L24941015654.111L25233018347.103L25669394028.106L25879102919.109L25936699452.103L26229323804.103L26945772285.100L26956159580.103L27091453269.109L27187409237.109L27291709969.101L27575244879.105L27728560274.105L28367561248.103L2838620480.101 L29075671421.100L29250551883.109L29493652943.2  L30156700960.100L30163107212.100L30271965611.103L30573031402.2  L30657312832.110L3165464044.109 L31947708092.103L32067690770.110L3258110912.107 L3258110912.110 L33019527745.103L33022365547.103L33323912488.110L3344981969.100 L3351682941.100 L34314969580.109L34557047148.106L34557047148.109L35164208253.103L35440546923.103L35825890571.103L36250394318.107L36809619730.110L36825302804.106L37097180948.108L37279087706.103L37286292558.107L37617331957.104L37975083836.103L38365407468.109L39082318472.108L39084494452.107L39188636933.0  L39276134848.110L39311712071.109L39599303702.103L39609756855.100L39832035604.108L39991661419.103L40482676668.103L4054608424.107 L40591468502.109L41206198630.100L41382298971.101L41592525904.107L41905953644.109L42503058196.108L42552079515.100L42829949548.109L44189107536.107L44189107536.110L4429452059.100 L4437941047.100 L44385038956.109L44640062295.100L44684143387.100L44692431671.100L4476694636.106 L4476694636.109 L45760346574.107L45828467392.107L45972227783.2  L46295603986.110L46493666364.103L46765748731.100L46771892567.100L46787153677.2  L47087347662.107L47140876414.106L47592708340.101L48945969426.110L49470878773.110L49686018027.103L49698585326.107L50646887276.109L50762941269.109L51029731293.101L51794595714.2  L51969960476.103L52519477948.103L52711488721.100L53520100027.103L53520149174.100L53522049574.103L53522194998.100L53522260663.104L53522310972.101L53530487322.100L53534582426.103L53534582426.105L53773760513.103L53780150432.100L53902472021.109L54266065179.107L54268061638.109L54281737159.106L54281737159.109L55011638034.110L55650177872.110L55914245920.100L56681743927.100L56861442286.111L56916165087.104L56920098290.105L57229756180.108L58057862252.106L58057862252.109L58387071310.107L58478778123.103L58529961788.103L59082152945.105L59310648043.5  L59392774343.103L59432451127.103L59587712341.109L59742863724.106L59742863724.109L60008875016.108L60245581385.106L60445881040.110L60481170540.106L60481170540.109L60671360262.101L60722838257.105L61013672555.103L61243012588.109L6129388396.104 L6133321537.105 L61535112187.103L61566527243.103L6221945708.106 L62350224375.104L62354157530.105L62639173925.106L63406899376.106L64551568828.103L64829551818.100L65147510839.100L65158439067.100L6560987371.103 L65821172626.105L65821172626.108L65873870057.108L66154526775.100L66963743590.100L66974606282.100L67176363755.103L67467701189.105L67467701189.108L67467701189.109L67472158696.104L67939919839.108L68251256535.100L68259548923.100L68286525111.100L68292718102.103L6835528564.104 L6837712776.105 L7278891073.103 L7870474428.103 L8354614654.1   L8636603244.106 L8679631884.100 L8688051232.100 L8873454286.107 L8904688464.1   L9380961614.107 L9970522898.110 00000101@02O03D04?04i05[05\06]07R08\09N0;40;f0<V0<W0=K0>Q0>\0@60A30B00Bi0D=0D>0D?0D@0E00Eb0FT0Gg0I:0JD0K;0Ko0L00L30Lc0MZ0NQ0OL0PG0QM0QN0QO0RA0Rm0Rn0Ro0S00Sb0TT0TU0TV0U_0VT0XC0Xm0YW0Z`0[n0[o0\00]P0_00_b0a10ac0bU0cG0dU0eE0fK0g`0hT0hU0iG0j90kH0lW0mA0n30nh0ni0nj0o\0o]0of0og0oh10R10[11h13E14915G16N17U18G1971:U1;G1<91=B1>E1?H1@:1@j1AT1BF1BG1Ca1Dj1Dk1E]1FT1GH1HQ1IL1JA1JB1KG1Ld1MV1NH1OQ1PA1Q51RS1Sh1Si1T[1Ud1Ve1Wn1XX1YY1Z_1[e1\W1]I1^^1^_1_I1`31a61b91bk1d51d;1eI1f=1f>1f?1fE1g71i31i_1jm1l;1lk1mf1ng20620720=20>21221d22W23J24=25025c26V27I28<28o2902912:@2;>2<<2=S2>j2@82A<2A=2Ao2CF2CG2CH2DQ2ET2FW2GI2H;2Ho2Id2J72J82Jb2L12M42N72O22Od2Q02R32S62S72Sl2T\2Ue2Uf2Ug2Uh2VR2WX2XO2YF2Z>2\<2]02]12]c2^U2_E2`:2`o2b>2bh2bi2bj2cZ2dI2eT2f_2gN2i52i62i72ia2jK2k@2l;2lm2ma2md2nj2nk2nl2o^2od30V31dFS3hAR3st03st13st23st32ps4rest3bsl2SP1a2PA4ncks2lo2A03PA03LPS3LST4LBSL5LOIMG3SPLS3hAR3st03st13st23st32ps4rest3bsl2SP1a2PA4ncks2lo2A03PA03LPS3LST4LBSL5LOIMG3SPLS3hAR3st03st13st23st32ps4rest3bsl2SP1a2PA3LST4LBSL2HBS3hAR3st03st13st23st32ps4rest3bsl2SP1a2PA4ncks3HNC3LST4LBSLS3hAR3st03st13st23st32ps4rest3bsl3LST4LBSLS3hAR2AL3st03st13st23st32ps4rest3bsl3LST4LBSL4IMG'FS3hAR3st03st13st23st32ps4rest3bsl2SP1a2PA3LST4LBSL2HB5Ha_st5Hl_stS3hAR3st03st13st23st32ps4rest3bsl2SP1a2PA3LST4LBSL2HBS3hAR3st03st13st23st32ps4rest3bsl2SP1a2PA2lo2A03PA03LST4LBSL5LOIMG3SPL3SPAS3hAR3st03st13st23st32ps4rest3bsl2SP1a2PA3LST4LBSLS3hAR2g03st03st13st23st32ps4rest3bsl2SP1a1x2PA4ncks2lo2A03PA03LPS3LST4LBSL5LOIMG3SPL2HB5Ha_st5Hl_st2g1S3hAR2AL3st03st13st23st32ps4rest3bsl3LST4LBSL4IMG'S3hAR3st03st13st23st32ps4rest3bsl2SP2lo3LST4LBSLFS3hAR3st03st13st23st32ps4rest3bsl2SP2lo3LST4LBSL3SPLS3hAR3st03st13st23st32ps4rest3bsl2SP1a2PA4ncks3LST4LBSL2HB5Ha_st5Hl_stS1x2Hx1H2H0S3hAR3st03st13st23st32ps4rest3bsl2SP1a2PA4ncks2lo2A03PA03LST4LBSL5LOIMG3SPL2HB5Ha_st5Hl_stS3hAR3st03st13st23st32ps4rest3bsl2SP1a2PA4ncks2lo3LST4LBSL2HBS3hAR3st03st13st23st32ps4rest3bsl2SP1a2PA4ncks2lo3LST4LBSL2HBS3hAR3st03st13st23st32ps4rest3bsl2SP1a2PA2lo3LST4LBSL3SPLS3hAR3st03st13st23st32ps4rest3bsl2SP1a2PA4ncks1k2lo2A03PA03LPS2HK3LST4LBSL5LOIMG3SPLFFFS3hAR3st03st13st23st32ps4rest3bsl2SP2lo3LST4LBSLS3hAR2AL3st03st13st23st32ps4rest3bsl3LST4LBSL4IMG'S3hAR2AL3st03st13st23st32ps4rest3bsl3LST4LBSL4IMG'S3hAR3st03st13st23st32ps4rest3bsl2SP1a2PA4ncks2lo2A03PA03PA13HNC3LST4LBSL5LOIMG3SPLS3hAR3st03st13st23st32ps4rest3bsl2SP1a2PA4ncks2lo2A03PA03PA13HNC3LST4LBSL5LOIMG3SPLS3hAR3st03st13st23st32ps4rest3bsl2SP1a2PA2lo2A03PA03LST4LBSL5LOIMG3SPL3SPAS3hAR3st03st13st23st32ps4rest3bsl2SP1a2PA1k2HK3LST4LBSLS3hAR3st03st13st23st32ps4rest3bsl2SP2lo3LST4LBSL3SPLSS1xS3hAR3st03st13st23st32ps4rest3bsl2SP2lo3LST4LBSLS3hAR2AL3st03st13st23st32ps4rest3bsl1k2HK3LST4LBSL4IMG'S3hAR2AL3st03st13st23st32ps4rest3bsl1k2HK3LST4LBSL4IMG'S3hAR3st03st13st23st32ps4rest3bsl2SP1a2PA3LST4LBSL2HB5Ha_stS3hAR3st03st13st23st32ps4rest3bsl2SP1a2PA3LST4LBSL2HB5Ha_stS3hAR3st03st13st23st32ps4rest3bsl2SP1a2PA4ncks3LST4LBSL2HB5Ha_st5Hl_stFFS3hAR3st03st13st23st32ps4rest3bsl2SP1a2PA3LST4LBSLS3hAR3st03st13st23st32ps4rest3bsl1a3LST4LBSLFFFS3hAR3st03st13st23st32ps4rest3bsl2SP1a2PA3LST4LBSLS3hAR3st03st13st23st32ps4rest3bsl2SP1a2PA3LST4LBSLFFS3hAR2g03st03st13st23st32ps4rest3bsl2SP1a1x2PA3LST4LBSL2HB5Ha_st5Hl_st2g1S3hAR3st03st13st23st32ps4rest3bsl2SP1a2PA3LST4LBSL2HBS3hAR3st03st13st23st32ps4rest3bsl2SP1a1x2PA4ncks2lo2Hx2A03AAL3PA03PAL4SEPA3LPS5LREST3LST4LBSL5LOIMG3SPL3SPA3MSZS3hAR3st03st13st23st32ps4rest3bsl3LST4LBSLS3hAR3st03st13st23st32ps4rest3bsl3LST4LBSLS3hAR3st03st13st23st32ps4rest3bsl2SP1a2PA4ncks2A03LST4LBSL2HB5Ha_st5Hl_stS3hAR3st03st13st23st32ps4rest3bsl2SP1a2PA1k2lo2A03PA02HK3LST4LBSL2bw5LOIMG3SPLFFS3hAR3st03st13st23st32ps4rest3bsl2SP1a2PA4ncks2lo2A03PA03LPS3LST4LBSL5LOIMG3SPL2HB5Ha_st5Hl_st1xS3hAR3st03st13st23st32ps4rest3bsl2SP1a2PA4ncks2lo2A03PA03LPS3LST4LBSL5LOIMG3SPL2HB5Ha_st5Hl_st1xS3hAR3st03st13st23st32ps4rest3bsl2SP1a2PA3LST4LBSLS3hAR3st03st13st23st32ps4rest3bsl2SP1a2PA4ncks2lo2A03PA03LPS3LST4LBSL5LOIMG3SPLS3hAR3st03st13st23st32ps4rest3bsl2SP1a2PA3LST4LBSLS3hAR2AL3st03st13st23st32ps4rest3bsl3LST4LBSL4IMG'S3hAR2AL3st03st13st23st32ps4rest3bsl3LST4LBSL4IMG'S3hAR3st03st13st23st32ps4rest3bsl2SP1a2PA1k2lo2A03PA02HK3LST4LBSL5LOIMG3SPL2bwS3hAR3st03st13st23st32ps4rest3bsl2SP2lo3LST4LBSLS3hAR3st03st13st23st32ps4rest3bsl2SP1a2PA4ncks3LST4LBSL2HB5Ha_st5Hl_stS3hAR3st03st13st23st32ps4rest3bsl2SP1a2PA2lo2A03PA03LST4LBSL5LOIMG3SPL2HB5Ha_st5Hl_stS3hAR3st03st13st23st32ps4rest3bsl2SP2lo3LST4LBSL3SPLFS3hAR2AL3st03st13st23st32ps4rest3bsl3LST4LBSL4IMG'S3hAR2AL3st03st13st23st32ps4rest3bsl3LST4LBSL4IMG'S3hAR3st03st13st23st32ps4rest3bsl2SP1a2PA4ncks2lo2A03PA03LPS3LST4LBSL5LOIMG3SPLS3hAR3st03st13st23st32ps4rest3bsl2SP1a2PA4ncks2lo2A03PA03LPS3LST4LBSL5LOIMG3SPLS3hAR3st03st13st23st32ps4rest3bsl3LST4LBSLS3hAR3st03st13st23st32ps4rest3bsl2SP1a2PA3LST4LBSLS3hAR3st03st13st23st32ps4rest3bsl2SP1a2PA3LST4LBSL2HBFFS3hAR2AL3st03st13st23st32ps4rest3bsl3LST4LBSL4IMG'FS2PA4ncksFFS3hAR3st03st13st23st32ps4rest3bsl3LST4LBSLS2PA4ncksS3hAR2g03st03st13st23st32ps4rest3bsl2SP1a1x2PA3PA03LST4LBSL2HB5Ha_st5Hl_st2g1S3hAR2g03st03st13st23st32ps4rest3bsl2SP1a1x2PA2lo2A03PA03LST4LBSL5LOIMG3SPL2HB5Ha_st5Hl_st2g1S3hAR3st03st13st23st32ps4rest3bsl2SP2lo3LST4LBSL3SPLS3hAR3st03st13st23st32ps4rest3bsl2SP1a2PA1k2lo2A03PA02HK3LST4LBSL5LOIMG3SPL2bwS3hAR3st03st13st23st32ps4rest3bsl2SP1a2PA3PA03LST4LBSL2HB5Ha_st5Hl_st1xS3hAR3st03st13st23st32ps4rest3bsl2SP1a2PA3PA03LST4LBSL2HB5Ha_st5Hl_st1xS3hAR2AL3st03st13st23st32ps4rest3bsl3LST4LBSL4IMG'S3hAR3st03st13st23st32ps4rest3bsl2SP2lo3LST4LBSLS3hAR3st03st13st23st32ps4rest3bsl2SP1a2PA4ncks2lo2A03PA03LPS3LST4LBSL5LOIMG3SPL2HB5Ha_st5Hl_stS3hAR2AL3st03st13st23st32ps4rest3bsl3LST4LBSL4IMG'S3hAR2AL3st03st13st23st32ps4rest3bsl3LST4LBSL4IMG'S3hAR2g03st03st13st23st32ps4rest3bsl2SP1a1x2PA3LST4LBSL2HB5Ha_st5Hl_st2g1S3hAR3st03st13st23st32ps4rest3bsl2SP1a2PA3LST4LBSL2HB5Ha_st5Hl_st1xS3hAR3st03st13st23st32ps4rest3bsl2SP1a2PA3LST4LBSL2HB5Ha_st5Hl_st1xS3hAR2AL3st03st13st23st32ps4rest3bsl3LST4LBSL4IMG'S3hAR3st03st13st23st32ps4rest3bsl2SP2lo3LST4LBSLS3hAR3st03st13st23st32ps4rest3bsl3LST4LBSLS3hAR3st03st13st23st32ps4rest3bsl2SP1a2PA3LST4LBSLFS3hAR3st03st13st23st32ps4rest3bsl2SP1a2PA4ncks2lo2A03PA03LST4LBSL5LOIMG3SPL2HB5Ha_st5Hl_stS3hAR3st03st13st23st32ps4rest3bsl2SP1a2PA4ncks2A03LST4LBSL2HB5Ha_st5Hl_stFS3hAR3st03st13st23st32ps4rest3bsl2SP1a2PA3LST4LBSLS3hAR3st03st13st23st32ps4rest3bsl2SP1a2PA1k2HK3LST4LBSLS3hAR3st03st13st23st32ps4rest3bsl2SP2lo3LST4LBSL3SPLS3hAR2g03st03st13st23st32ps4rest3bsl2SP1a1x2PA3LST4LBSL2HB5Ha_st5Hl_st2g1S3hAR3st03st13st23st32ps4rest3bsl2SP1a2PA3LST4LBSL2HB5Ha_stS3hAR3st03st13st23st32ps4rest3bsl2SP1a2PA3LST4LBSL2HBSS3hAR3st03st13st23st32ps4rest3bsl2SP1a2PA3PA03LST4LBSL2HB5Ha_st5Hl_stS3hAR2g03st03st13st23st32ps4rest3bsl2SP1a1x2PA2lo2A03PA03LST4LBSL5LOIMG3SPL2HB5Ha_st5Hl_st2g1S3hAR2AL3st03st13st23st32ps4rest3bsl3LST4LBSL4IMG'S3hAR2AL3st03st13st23st32ps4rest3bsl3LST4LBSL4IMG'S3hAR3st03st13st23st32ps4rest3bsl2SP1a2PA4ncks2A03LST4LBSL2HB5Ha_st5Hl_stS3hAR3st03st13st23st32ps4rest3bsl2SP2lo3LST4LBSLS3hAR3st03st13st23st32ps4rest3bsl2SP2lo3LST4LBSL3SPLS3hAR3st03st13st23st32ps4rest3bsl2SP1a2PA4ncks2lo2A03PA03LPS3LST4LBSL5LOIMG3SPL2HB5Ha_st5Hl_stS3hAR3st03st13st23st32ps4rest3bsl2SP1a2PA4ncks2lo2A03PA03PA15LREST3LST4LBSL5LOIMG3SPLFS3hAR2AL3st03st13st23st32ps4rest3bsl3LST4LBSL4IMG'S3hAR3st03st13st23st32ps4rest3bsl2SP1a2PA4ncks2A03LST4LBSL2HB5Ha_st5Hl_stS3hAR3st03st13st23st32ps4rest3bsl2SP1a2PA3LST4LBSL2HB5Ha_st5Hl_stS3hAR3st03st13st23st32ps4rest3bsl2SP1a2PA4ncks2A03LST4LBSL2HB5Ha_st5Hl_stS3hAR3st03st13st23st32ps4rest3bsl3LST4LBSLS3hAR3st03st13st23st32ps4rest3bsl2SP1a2PA3LST4LBSL2HB5Ha_st5Hl_stS3hAR3st03st13st23st32ps4rest3bsl2SP1a2PA2A03LST4LBSL2HB5Ha_st5Hl_st1xS3hAR3st03st13st23st32ps4rest3bsl2SP1a2PA2A03LST4LBSL2HB5Ha_st5Hl_st1xS3hAR2AL3st03st13st23st32ps4rest3bsl3LST4LBSL4IMG'S3hAR2AL3st03st13st23st32ps4rest3bsl3LST4LBSL4IMG'S3hAR3st03st13st23st32ps4rest3bsl2SP1a2PA2lo2A03PA03LST4LBSL5LOIMG3SPL2HB5Ha_st5Hl_stFS3hAR3st03st13st23st32ps4rest3bsl3LST4LBSLS3hAR3st03st13st23st32ps4rest3bsl3LST4LBSLS3hAR3st03st13st23st32ps4rest3bsl2SP1a2PA3LST4LBSL2HB5Ha_st5Hl_st1xS3hAR3st03st13st23st32ps4rest3bsl2SP1a2PA3LST4LBSL2HB5Ha_st5Hl_st1xS3hAR3st03st13st23st32ps4rest3bsl2SP1a2PA3LST4LBSLS3hAR3st03st13st23st32ps4rest3bsl2SP1a2PA4ncks3PA03LST4LBSL2HB5Ha_st5Hl_stS1k2HKS3hAR3st03st13st23st32ps4rest3bsl2SP1a2PA1k2lo2A03PA02HK3LST4LBSL2bw5LOIMG3SPLS3hAR3st03st13st23st32ps4rest3bsl2SP2lo3LST4LBSL3SPLFFS1k2HKS3hAR3st03st13st23st32ps4rest3bsl2SP1a2PA3LST4LBSLS3hAR3st03st13st23st32ps4rest3bsl2SP1a1x2PA4ncks2lo2Hx2A03AAL3PA03PAL4SEPA3HNC3LPS3LST4LBSL5LOIMG3SPL3SPA3MSZ2HB5Ha_st5Hl_stS3hAR3st03st13st23st32ps4rest3bsl1a3LST4LBSLS3hAR3st03st13st23st32ps4rest3bsl2SP1a2PA1k2lo2A03PA02HK3LST4LBSL2bw5LOIMG3SPLS3hAR3st03st13st23st32ps4rest3bsl2SP1a2PA1k2lo2A03PA02HK3LST4LBSL5LOIMG3SPL2bwS3hAR3st03st13st23st32ps4rest3bsl2SP2lo3LST4LBSLS3hAR3st03st13st23st32ps4rest3bsl2SP1a2PA3LST4LBSL2HB5Ha_stS3hAR3st03st13st23st32ps4rest3bsl2SP1a2PA3LST4LBSL2HB5Ha_st5Hl_stS3hAR3st03st13st23st32ps4rest3bsl2SP1a2PA4ncks2lo2A03PA03LPS3LST4LBSL5LOIMG3SPLFS1k2HKFS3hAR3st03st13st23st32ps4rest3bsl2SP2lo3LST4LBSL3SPLS3hAR2AL3st03st13st23st32ps4rest3bsl3LST4LBSL4IMG'S3hAR2AL3st03st13st23st32ps4rest3bsl3LST4LBSL5ALWF'S3hAR2AL3st03st13st23st32ps4rest3bsl3LST4LBSL5ALWF'S3hAR2AL3st03st13st23st32ps4rest3bsl3LST4LBSL5ALWF'S3hAR2AL3st03st13st23st32ps4rest3bsl3LST4LBSL5ALWF'S3hAR2AL3st03st13st23st32ps4rest3bsl3LST4LBSL5ALWF'S3hAR2AL3st03st13st23st32ps4rest3bsl3LST4LBSL5ALWF'S3hAR2AL3st03st13st23st32ps4rest3bsl3LST4LBSL5ALWF'S3hAR2AL3st03st13st23st32ps4rest3bsl3LST4LBSL5ALWF'S3hAR2AL3st03st13st23st32ps4rest3bsl3LST4LBSL5ALWF'FFS3hAR3st03st13st23st32ps4rest3bsl2SP1a2PA4ncks2lo2A03PA03LPS3LST4LBSL5LOIMG3SPLS3hAR3st03st13st23st32ps4rest3bsl2SP1a2PA1k2A03PA02HK3LST4LBSLS3hAR3st03st13st23st32ps4rest3bsl2SP1a2PA1k2A03PA02HK3LST4LBSLS3hAR3st03st13st23st32ps4rest3bsl2SP1a2PA2lo2A03PA03LST4LBSL5LOIMG3SPL2HB5Ha_st5Hl_st1xS3hAR3st03st13st23st32ps4rest3bsl2SP1a2PA2lo2A03PA03LST4LBSL5LOIMG3SPL2HB5Ha_st5Hl_st1xS3hAR3st03st13st23st32ps4rest3bsl2SP1a2PA1k2lo2A03PA02HK3LST4LBSL2bw5LOIMG3SPLS3hAR3st03st13st23st32ps4rest3bsl2SP1a2PA2A03LST4LBSL2HB5Ha_st5Hl_stFS3hAR2AL3st03st13st23st32ps4rest3bsl3LST4LBSL4IMG'S3hAR3st03st13st23st32ps4rest3bsl2SP1a2PA4ncks1k2lo2A03PA03LPS2HK3LST4LBSL2bw5LOIMG3SPLFFS3hAR3st03st13st23st32ps4rest3bsl2SP1a2PA4ncks2A03LST4LBSL2HB5Ha_st5Hl_stS3hAR3st03st13st23st32ps4rest3bsl2SP1a2PA3LST4LBSL2HB5Ha_st5Hl_st1xS3hAR3st03st13st23st32ps4rest3bsl2SP1a2PA3LST4LBSL2HB5Ha_st5Hl_st1xS3hAR3st03st13st23st32ps4rest3bsl2SP1a2PA3LST4LBSLS3hAR2AL3st03st13st23st32ps4rest3bsl3LST4LBSL4IMG'S3hAR3st03st13st23st32ps4rest3bsl2SP2lo3LST4LBSL3SPLS3hAR3st03st13st23st32ps4rest3bsl2SP1a2PA3LST4LBSL2HBS3bsl1k2HK4LBSL3NTHFS3hAR3st03st13st23st32ps4rest3bsl3LST4LBSLS3hAR3st03st13st23st32ps4rest3bsl2SP1a2PA4ncks2lo2A03PA03LPS3LST4LBSL5LOIMG3SPLS3hAR3st03st13st23st32ps4rest3bsl2SP1a2PA3LST4LBSL2HB5Ha_st5Hl_st1xS3hAR3st03st13st23st32ps4rest3bsl2SP1a2PA3LST4LBSL2HB5Ha_st5Hl_st1xS3hAR3st03st13st23st32ps4rest3bsl2SP1a2PA3LST4LBSL2HB5Ha_stS3hAR3st03st13st23st32ps4rest3bsl2SP1a2PA3LST4LBSLS3hAR2g03st03st13st23st32ps4rest3bsl2SP1a1x2PA2A03LST4LBSL2HB5Ha_st5Hl_st2g1S3hAR3st03st13st23st32ps4rest3bsl2SP1a2PA3LST4LBSL2HB5Ha_st5Hl_st1xS3hAR3st03st13st23st32ps4rest3bsl2SP1a2PA3LST4LBSL2HB5Ha_st5Hl_st1xFS3hAR3st03st13st23st32ps4rest3bsl2SP1a2PA3LST4LBSL2HBS3hAR3st03st13st23st32ps4rest3bsl2SP2lo3LST4LBSLS3hAR2g03st03st13st23st32ps4rest3bsl2SP1a1x2PA3LST4LBSL2HB5Ha_st5Hl_st2g1FFFS3hAR3st03st13st23st32ps4rest3bsl3LST4LBSLS3hAR3st03st13st23st32ps4rest3bsl2SP1a2PA4ncks3LST4LBSL2HB5Ha_st5Hl_stS3hAR2AL3st03st13st23st32ps4rest3bsl1k2HK3LST4LBSL4IMG'S3hAR2AL3st03st13st23st32ps4rest3bsl1k2HK3LST4LBSL4IMG'S3hAR3st03st13st23st32ps4rest3bsl2SP1a2PA2A03LST4LBSL2HBS3hAR3st03st13st23st32ps4rest3bsl2SP1a1x2PA4ncks2lo2Hx2A03AAL3PA03PAL4SEPA3LPS5LREST3LST4LBSL5LOIMG3SPL3SPA3MSZ2HB5Ha_st5Hl_stS3hAR3st03st13st23st32ps4rest3bsl2SP2lo3LST4LBSL3SPLFS3hAR2AL3st03st13st23st32ps4rest3bsl3LST4LBSL4IMG'S3hAR2AL3st03st13st23st32ps4rest3bsl3LST4LBSL4IMG'S3hAR3st03st13st23st32ps4rest3bsl2SP2lo3LST4LBSLS3hAR3st03st13st23st32ps4rest3bsl2SP1a2PA3LST4LBSL2HBS3hAR3st03st13st23st32ps4rest3bsl2SP1a2PA3LST4LBSL2HBS3hAR3st03st13st23st32ps4rest3bsl2SP1a2PA4ncks2lo2A03PA03LPS3LST4LBSL5LOIMG3SPLS3hAR3st03st13st23st32ps4rest3bsl3LST4LBSLFFS3hAR3st03st13st23st32ps4rest3bsl2SP2lo3LST4LBSLS3hAR3st03st13st23st32ps4rest3bsl1k2HK3LST4LBSLS3hAR3st03st13st23st32ps4rest3bsl2SP1a2PA1k2lo2A03PA02HK3LST4LBSL5LOIMG3SPLS3hAR3st03st13st23st32ps4rest3bsl2SP1a2PA1k2lo2A03PA02HK3LST4LBSL5LOIMG3SPLS3hAR3st03st13st23st32ps4rest3bsl1k2HK3LST4LBSLS3hAR3st03st13st23st32ps4rest3bsl2SP1a1x2PA4ncks2lo2Hx2A03ACE3PA03LST4LBSL5LOIMG3SPL3MSZ2HB5Ha_st5Hl_stFFS3hAR3st03st13st23st32ps4rest3bsl3LST4LBSLS3hAR3st03st13st23st32ps4rest3bsl3LST4LBSLS3hAR3st03st13st23st32ps4rest3bsl2SP1a2PA3LST4LBSL2HBS3hAR3st03st13st23st32ps4rest3bsl2SP1a2PA3LST4LBSL2HB5Ha_stS3hAR2AL3st03st13st23st32ps4rest3bsl3LST4LBSL4IMG'S3hAR3st03st13st23st32ps4rest3bsl2SP2lo3LST4LBSL3SPLS1kS3hAR3st03st13st23st32ps4rest3bsl2SP1a2PA4ncks3LST4LBSL2HB5Ha_st5Hl_stFFS3hAR3st03st13st23st32ps4rest3bsl2SP1a2PA3LST4LBSLS4restS3hAR3st03st13st23st32ps4rest3bsl2SP1a2PA3LST4LBSLS3hAR3st03st13st23st32ps4rest3bsl2SP1a2PA1k2lo2A03PA02HK3LST4LBSL5LOIMG3SPL2bw". (* [comment removed for export] *)
  Lemma large_E2 : ltac2:(CDefT.buildp (gd_tbl_AW_Large ()) "Pra,(?.&40.)Pgp,(?.&40.)Ptp,(?.&40.)Pt0,(?.&40.)Pt1,(?.&40.)Pt2,(?.&40.)Pa1,(?.&40.)Pa2,(?.&40.)Pa4,(?.&40.)Pa5,(?.&40.)Pa6,(?.&40.)Pa7,(?.&40.)Ps4,(?.&40.)Ps6,(?.&40.)Ps7,(?.&40.)Ps8,(?.&40.)Ps9,(?.&40.)Ps10,(?.&40.)Ps11,(?.&40.)Pt3,(?.&40.)Pt4,(?.&40.)Pt5,(?.&40.)Pt6,(?.&40.)Pj0,(=.(?.&8.))Pq9,(?.&40.)Pq8,(?.&40.)Pq7,(?.&40.)Pq6,(?.&40.)Pq5,(?.&40.)Pq4,(?.&40.)Pq3,(?.&40.)Pq2,(?.&40.)Pq1,(?.&40.)Pq0,(?.&40.)Pqra,(?.&40.)Ph3,(?.&40.)Pg0,(?.&40.)Pg1,(?.&40.)Psrt,(?.&8.)Pst,(=.(?.&40.))Pps,(=.(?.&40.))Prest,(=.(?.&40.))Pbsl,(=.(?.&40.))Pr0,(?.&40.)PSP,$11.PF,(32.&5.(?.&40.))Pfc,(?.&20.)Pm,P,(?.&40.)(10.(?.&8.))Pa,$11.Px,$11.PPA,$11.PT,$11.Pncks,$11.Pk,$11.Plo,$11.P,(0.(33.+10000.R6.)(15.R6.(34.+2.+28.)))P,(15.+65?000.R8.)P,(17.$11.(37.R9.+1000.)=)P,(15.(3.R:.(28.R9.))(35.VhAR,))P,(15.+65?000.R9.)P,(15.(3.R:.+800000.)(35.VhAR,))P,(17.$11.(37.R;.+1000.)=)P,(41.(15.(3.R>.(28.R=.))R<.)(15.(3.R<.+800000.)R>.))P,(0.(15.=R;.)(33.R;.(34.+2.+14.)))P,(17.$11.(21.(22.(?.&40.)R18.))R<.)P,(15.(20.+8.(3.(3.R=.+1.)(21.(22.(?.&40.)R18.))))+800000.)P,(0.(15.+10.R=.)(15.R=.+29.))P,(17.$47.(22.(?.&40.)R1<.)#4.)P,(17.$47.(22.(?.&40.)R1:.)#40.)P,(38.VCS,R15.+20.)P,(38.VCS,(3.R14.(20.+8.R12.))+8.)P,(12.R18.R15.)P,(23.$2.R19.(3.R18.+18.)(5.$6.(7.R25.)(9.$6.)))P,(1>.$2.R1:.R17.R21.)P,(1>.$2.R1;.(3.R18.(20.+8.R16.))(5.(?.&40.)R1?.R21.))P,(23.$2.R1<.(3.$4.+78.)(5.$6.(7.(8.&40.R17.))(5.$6.(45.R25.)(9.$6.))))P,(23.$2.R1=.(3.$4.+88.)(46.(?.&40.)$6.$7.R25.))P,(1>.$2.R1>.(3.$4.+:8.)R23.)P,(23.$2.R1?.(3.$4.+2:8.)(5.$6.(40.(8.&40.+1.))(9.$6.)))P,(23.$2.R20.(3.$4.+2<0.)(5.$6.(7.R2;.)(5.$6.(7.R2:.)(9.$6.))))P,(30.R21.R24.R39.R38.R37.R36.R35.R34.R33.R32.R31.R30.R2?.R2>.)P,(31.$2.R22.R1;.(3.R25.-60.))P,(15.(35.VhAR,)R1<.)P,(15.R1=.(36.R27.+60.))P,(15.R28.(34.+2.+3?.))P,(17.$11.(37.R29.+10.)=)P,(38.VCS,R20.(36.R2:.R20.))P,(2?.$2.R28.)(39.$2.VAL,VCS,(48.R2<.R57.R56.R47.R46.R40.R3?.R3>.R3=.R3<.R3;.R3:.R39.R38.R37.R36.R2;.R2:.R28.R27.R24.R26.R25.R22.R30.R2?.R29.)(26.(27.R58.(8.&40.(3.R2<.-60.))R57.R56.R55.R54.R53.(8.&40.(3.$4.+2;0.))(8.&40.(3.$4.+40.))(8.&40.(3.R28.+1000.))R52.R51.(8.&40.R24.)R50.R4?.R4>.R4=.(8.&40.(28.R27.))(8.&40.(36.+3?.R23.))R4<.(8.&40.R28.)R4;.R4:.R49.R48.R47.R46.R45.R44.R43.R42.)R2;.(8.&40.+4<544.)R2:.(2:.(?.&40.))R29.(2;.$2.)))")
(* [comment removed for export] *).
  Proof.
    intros ra gp tp t0 t1 t2 a1 a2 a4 a5 a6 a7 s4 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 j0 q9 q8 q7 q6 q5 q4 q3 q2 q1 q0 qra h3 g0 g1 srt st ps rest bsl r0 SP F fc m a x PA T ncks k lo
      Hx A0 AAL ACE PA0 PA1 PAL SEPA HNC LPS LREST HK LST LBSL CSA CSP LS H3 HPS HREST NC STC BSL MX GS FR ST LOIMG SPL SPH SPA SCS MI.
    facts. destruct LS as (LS1 & LS2 & LS3). unfold large_frame in FR.
    unfold A_INSTANCE in *.
    change (1074072 + 64) with 1074136 in *. change (1074072 + 688) with 1074760 in *. change (1074072 + 680) with 1074752 in *. change (1074072 + 120) with 1074192 in *.
    change (1074072 + 136) with 1074208 in *. change (1074072 + 168) with 1074240 in *. change (1074072 + 704) with 1074776 in *.
    change (1074752 + 4) with 1074756. change (1074072 + 720) with 1074792.
    assert (MSZ : x + 4096 <= map_size x < x + 8192).
    { unfold map_size. clear - Hx. pose proof (Z.div_mod (x + 4095) 4096 ltac:(lia)). pose proof (Z.mod_pos_bound (x + 4095) 4096 ltac:(lia)). lia. }
    destruct st as [|st0 [|st1 [|st2 [|st3 [|]]]]]; try discriminate LST. cbn [map] in STC.
    pose proof (munch_refl [(lo, SP); (a + 24, a + 32); (PA + 8 * ncks, PA + 8 * ncks + 8); (1074192, 1074756); (1074776, 1074792)] m) as MU.
    pose proof (wmono_refl asegs m) as WM.
    (* [comment removed for export] *)
    zstep. zstep.
    replace (Z.lxor (63 - k) 63) with k.
    2:{ clear - HK. pattern k. refine (zallP_spec _ 26%nat 16 _ k _); [| clear - HK; lia]. vm_compute. repeat (apply conj; [reflexivity|]). exact I. }
    zstep. zstep. zstep. rewrite (Z.shiftl_mul_pow2 ncks 3) by (clear; lia). change (2^3) with 8. replace (PA + ncks * 8) with (PA + 8 * ncks) by (clear; lia).
    (* [comment removed for export] *)
    pose proof (u64arr_store_ok asegs _ _ _ 0 _ HREST ltac:(cbn; clear; lia) eq_refl) as SOK.
    pose proof (u64arr_write asegs _ _ _ 0 (Z_to_bv 64 a) HREST ltac:(cbn; clear; lia)) as HREST'.
    rewrite Z.mul_0_r, Z.add_0_r in SOK, HREST'. change (upd (r0 :: rest) (Z.to_nat 0) (Z_to_bv 64 a)) with (Z_to_bv 64 a :: rest) in HREST'.
    zstep. store_done. try clear HREST.
    (* [comment removed for export] *)
    do 10 zstep.
    (* [comment removed for export] *)
    zstep. if_cases KM; [| zstep].
    (* [comment removed for export] *)
    all: zstep; zstep; rewrite (Z.shiftl_mul_pow2 k 3) by (clear; lia); change (2^3) with 8.
    all: destruct (nth_error bsl (Z.to_nat k)) as [bw|] eqn:NTH; [| apply nth_error_None in NTH; exfalso; clear - NTH LBSL HK; lia].
    all: pose proof (u64arr_read asegs _ _ _ k bw (wa (1074136 + k * 8 + 104)) BSL NTH ltac:(clear - HK; lia) ltac:(f_equal; clear; lia)) as RD.
    all: zstep; clear RD.
    all: zstep; zstep.
    all: pose proof (u64arr_store_ok asegs _ _ _ k (wa (1074136 + k * 8 + 104)) BSL ltac:(rewrite LBSL; clear - HK; lia) ltac:(f_equal; clear; lia)) as SOK.
    all: lazymatch goal with |- context [TNode (TNode (TNode TEmpty (Some ?a7v) TEmpty) (Some ?s1v) (TNode TEmpty (Some ?s9v) TEmpty)) (Some ?t0v) (TNode (TNode TEmpty (Some ?s5v) TEmpty) (Some ?a3v) (TNode TEmpty (Some ?t4v) TEmpty))] =>
           pose proof (u64arr_write asegs _ _ _ k a3v BSL ltac:(rewrite LBSL; clear - HK; lia)) as BSL' end.
    all: replace (1074240 + 8 * k) with (1074136 + k * 8 + 104) in BSL' by (clear; lia).
    all: zstep; store_done; try clear BSL.
    (* [comment removed for export] *)
    all: do 5 zstep.
    (* [comment removed for export] *)
    all: match goal with H : rw_cells asegs ?mm 1074752 [C4 (Z_to_bv 64 1)] |- _ =>
           apply (rw_cells_reshape asegs mm 1074752 _ [C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)]) in H; [| cbn; tauto | reflexivity] end.
    all: zstep.
    all: match goal with H : rw_cells asegs ?mm 1074752 ?cs |- _ => idtac "MXC" cs;
           apply (rw_cells_reshape asegs mm 1074752 _ [C4 (Z_to_bv 64 0)]) in H; [| cbn; tauto | reflexivity] end.
    (* [comment removed for export] *)
    all: do 12 zstep; replace (SP + -96 + 96) with SP by lia; zstep.
    all: release_frame FR ST SP.
    all: apply evtA_done; unfold largeE_post, A_INSTANCE.
    all: change (1074072 + 64) with 1074136; change (1074072 + 688) with 1074760; change (1074072 + 680) with 1074752; change (1074072 + 120) with 1074192;
         change (1074072 + 136) with 1074208; change (1074072 + 168) with 1074240; change (1074072 + 704) with 1074776; change (1074072 + 720) with 1074792.
    all: match goal with H : u64arr asegs ?mm (?pa + 8 * ?n) (Z_to_bv 64 ?av :: ?rs) |- _ =>
           change (Z_to_bv 64 av :: rs) with ([Z_to_bv 64 av] ++ rs) in H; apply u64arr_app in H as [HNEW HREST2]; cbn [length Z.of_nat Pos.of_succ_nat] in HREST2 end.
    all: do 14 eexists; eexists; eexists [_; _; _; _]; do 3 eexists.
    all: split; [reflexivity|]. all: split; [exact MU|]. all: split; [exact WM|]. all: split; [assumption|].
    all: split; [assumption|].
    all: split; [apply u64arr_app; split; [exact HPS| rewrite LPS; exact HNEW]|].
    all: split; [replace (PA + 8 * (ncks + 1)) with (PA + 8 * ncks + 8 * 1) by (clear; lia); exact HREST2|].
    all: split; [assumption|]. all: split; [cbn [map]; eassumption|]. all: split; [reflexivity|].
    all: split; [exact BSL'|]. all: split; [rewrite upd_length; exact LBSL|].
    all: split; [assumption|]. all: split; [eassumption|]. all: assumption.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0030?L11075334331.46L49082915003.46L59314923118.6 00000:00D00TS4ncks3HNCS4nres3HNRS4ncks4nres2NE1K". (* [comment removed for export] *)
  Lemma large_E0 : ltac2:(CDefT.buildp (gd_tbl_AW_Large ()) "Pra,(?.&40.)Pgp,(?.&40.)Ptp,(?.&40.)Pt0,(?.&40.)Pt1,(?.&40.)Pt2,(?.&40.)Pa0,(?.&40.)Pa1,(?.&40.)Pa2,(?.&40.)Pa5,(?.&40.)Pa6,(?.&40.)Pa7,(?.&40.)Ps2,(?.&40.)Ps3,(?.&40.)Ps4,(?.&40.)Ps5,(?.&40.)Ps6,(?.&40.)Ps7,(?.&40.)Ps8,(?.&40.)Ps9,(?.&40.)Ps10,(?.&40.)Ps11,(?.&40.)Pt3,(?.&40.)Pt4,(?.&40.)Pt5,(?.&40.)Pt6,(?.&40.)PSP,$11.PF,(32.&5.(?.&40.))Pfc,(?.&20.)Pm,P,(?.&40.)(10.(?.&8.))Pncks,$11.Pnres,$11.P,(0.(15.=R2.)(33.R2.(34.+2.+3?.)))P,(0.(15.=R2.)(33.R2.(34.+2.+3?.)))P,(49.(17.$11.R4.R3.))P,(2?.$2.R6.)(39.$2.VAL,VCS,Lms',$25.(17.$25.R1.(26.(27.R25.(8.&40.(3.R;.-60.))R24.R23.R22.R21.R20.(8.&40.(3.$4.+2;0.))(8.&40.(3.$4.+40.))R1?.R1>.R1=.(8.&40.R7.)(8.&40.R6.)R1<.R1;.R1:.R19.R18.R17.R16.R15.R14.R13.R12.R11.R10.R?.R>.R=.R<.)R:.(8.&40.+4<544.)R9.(2:.(?.&40.))R8.(2;.$2.)))(26.(27.R24.(8.&40.(3.R:.-60.))R23.R22.R21.R20.R1?.(8.&40.(3.$4.+2;0.))(8.&40.(3.$4.+40.))R1>.R1=.R1<.(8.&40.R6.)(8.&40.R5.)R1;.R1:.R19.R18.R17.R16.R15.R14.R13.R12.R11.R10.R?.R>.R=.R<.R;.)R9.(8.&40.+4<540.)R8.(2:.(?.&40.))R7.(2;.$2.)))")
(* [comment removed for export] *).
  Proof.
    intros ra gp tp t0 t1 t2 a0 a1 a2 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 SP F fc m ncks nres HNC HNR NE MI.
    facts. unfold A_INSTANCE in *.
    zstep. if_cases K; zify_cond K. { exfalso. rewrite ?unsigned_lit in K by (clear - HNC HNR; lia). clear - K NE HNC HNR; lia. }
    apply evtA_done. reflexivity.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0070?L11081659039.48L3684711863.48 L36978392003.2 L39188636933.0 L53534663706.48L5788382647.48 L65009957373.4800000:00;00D00E00O00X00aS4ncks3HNCSS4ncks2PASS2AL5ALWF'S2AL4IMG'S2AL4IMG'". (* [comment removed for export] *)
  Lemma large_E1 : ltac2:(CDefT.buildp (gd_tbl_AW_Large ()) "Pra,(?.&40.)Pgp,(?.&40.)Ptp,(?.&40.)Pt0,(?.&40.)Pt1,(?.&40.)Pt2,(?.&40.)Pa0,(?.&40.)Pa1,(?.&40.)Pa2,(?.&40.)Pa5,(?.&40.)Pa6,(?.&40.)Pa7,(?.&40.)Ps2,(?.&40.)Ps3,(?.&40.)Ps4,(?.&40.)Ps5,(?.&40.)Ps6,(?.&40.)Ps7,(?.&40.)Ps8,(?.&40.)Ps9,(?.&40.)Ps10,(?.&40.)Ps11,(?.&40.)Pt3,(?.&40.)Pt4,(?.&40.)Pt5,(?.&40.)Pt6,(?.&40.)PSP,$11.PF,(32.&5.(?.&40.))Pfc,(?.&20.)Pm,P,(?.&40.)(10.(?.&8.))Pncks,$11.PPA,$11.P,(0.(15.=R2.)(33.R2.(34.+2.+14.)))P,(15.=R2.)P,(15.(3.R3.+800000.)(34.+2.+3?.))P,(12.R6.R4.)P,(2?.$2.R7.)(39.$2.VAL,VCS,Lms',$25.(17.$25.R1.(26.(27.(8.&40.+4<73<.)(8.&40.(3.R<.-60.))R25.R24.R23.R22.R21.(8.&40.(3.$4.+2;0.))(8.&40.(3.$4.+40.))(8.&40.(3.$4.+50.))(8.&40.(3.R7.(20.+8.R8.)))(8.&40.+20000.)(8.&40.=)(8.&40.(3.$4.+50.))R1=.R1<.R1;.R1:.R19.R20.R17.R16.R15.R14.R13.R12.R11.R10.R?.R>.R=.)R;.(8.&40.$4:.)R:.(2:.(?.&40.))R9.(2;.$2.)))(26.(27.R25.(8.&40.(3.R;.-60.))R24.R23.R22.R21.R20.(8.&40.(3.$4.+2;0.))(8.&40.(3.$4.+40.))R1?.R1>.R1=.(8.&40.R7.)(8.&40.R7.)R1<.R1;.R1:.R19.R18.R17.R16.R15.R14.R13.R12.R11.R10.R?.R>.R=.R<.)R:.(8.&40.+4<540.)R9.(2:.(?.&40.))R8.(2;.$2.)))")
(* [comment removed for export] *).
  Proof.
    intros ra gp tp t0 t1 t2 a0 a1 a2 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 SP F fc m ncks PA HNC PA0 PA1 LS MI.
    facts. destruct LS as (LS1 & LS2 & LS3). unfold A_INSTANCE, A_MAPORDIE in *.
    change (1074072 + 64) with 1074136 in *. change (1074072 + 688) with 1074760 in *. change (1074072 + 80) with 1074152 in *.
    (* [comment removed for export] *)
    zstep. rewrite bv_eqb_refl. zstep. zstep. zstep. rewrite (Z.shiftl_mul_pow2 ncks 3) by (clear; lia). change (2^3) with 8.
    zstep. zstep. zstep. zstep. zstep. zstep.
    replace (ncks * 8 + PA) with (PA + 8 * ncks) by (clear; lia).
    apply evtA_done. reflexivity.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0090?L28084833207.52L29079881597.52L31802703624.54L53534663706.52L5481563133.52 L56677533751.52L60440291185.53L64024902583.52L66158704183.5200000900B00L00V00_00h00l00m00nS2AL4IMG'S2AL4IMG'S2HB5Ha_stS2AL5ALWF'S2AL4IMG'S2AL4IMG'S2HBSS". (* [comment removed for export] *)
  Lemma large_E1b : ltac2:(CDefT.buildp (gd_tbl_AW_Large ()) "Pgp,(?.&40.)Ptp,(?.&40.)Pt0,(?.&40.)Pt1,(?.&40.)Pt2,(?.&40.)Pa0,(?.&40.)Pa1,(?.&40.)Pa2,(?.&40.)Pa3,(?.&40.)Pa4,(?.&40.)Pa5,(?.&40.)Pa6,(?.&40.)Pa7,(?.&40.)Ps2,(?.&40.)Ps3,(?.&40.)Ps4,(?.&40.)Ps5,(?.&40.)Ps6,(?.&40.)Ps7,(?.&40.)Ps8,(?.&40.)Ps9,(?.&40.)Ps10,(?.&40.)Ps11,(?.&40.)Pt3,(?.&40.)Pt4,(?.&40.)Pt5,(?.&40.)Pt6,(?.&40.)PSP,$11.PF,(32.&5.(?.&40.))Pfc,(?.&20.)Pm0,P,(?.&40.)(10.(?.&8.))Pm,P,(?.&40.)(10.(?.&8.))Pncks,$11.Pnres,$11.Psrt,(?.&8.)PW,(=.(2<.$11.$11.))P,(0.(15.=R4.)(33.R4.(34.+2.+14.)))P,(15.=R4.)P,(15.(3.R5.+4000.)(34.+2.+14.))P,(23.$2.R8.(3.$4.+70.)(5.$6.(7.(8.&40.R6.))(5.$6.(7.(8.&40.R7.))(5.$6.(45.R5.)(9.$6.)))))P,(13.(5.(2<.$11.$11.)(2=.$11.$11.(3.$4.+70.)(3.$4.+78.))R5.)R:.R9.)P,(2>.$2.R;.R:.)P,(2?.$2.R;.)(39.$2.VAL,VCS,Lms',$25.(1;.P,(?.&40.)(10.(?.&8.))Lm',P,(?.&40.)(10.(?.&8.))(0.(17.$25.R2.(26.(27.(8.&40.+4<73<.)(8.&40.(3.R12.-60.))R2=.R2<.R2;.R2:.R29.(8.&40.(3.$4.+2;0.))(8.&40.(3.$4.+40.))R1>.(8.&40.(3.R<.+4000.))(8.&40.+4000.)(8.&40.R=.)R24.R23.R22.R21.R20.R1?.R1>.R1=.R1<.R1;.R1:.R19.R18.R17.R16.R15.R14.R13.)R11.(8.&40.+4<544.)R10.(2:.(?.&40.))R1.(2;.$2.)))(0.(13.(5.(2<.$11.$11.)(2=.$11.$11.(3.$4.+70.)(3.$4.+78.))R:.)R?.R1.)(0.(2>.$2.R?.R1.)(0.(2?.$2.R1.)(23.$2.R1.(3.$4.+70.)(5.$6.(7.(8.&40.(3.R<.+4000.)))(5.$6.(7.(8.&40.R=.))(5.$6.(45.R;.)(9.$6.))))))))))(26.(27.(8.&40.+4<73<.)(8.&40.(3.R10.-60.))R2;.R2:.R29.R28.R27.(8.&40.(3.$4.+2;0.))(8.&40.(3.$4.+40.))R26.R25.R24.R23.R22.R21.R20.R1?.R1>.R1=.R1<.R1;.R1:.R19.R18.R17.R16.R15.R14.R13.R12.R11.)R?.(8.&40.+4<73<.)R>.(2:.(?.&40.))R<.(2;.$2.)))")
(* [comment removed for export] *).
  Proof.
    intros gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 SP F fc m0 m ncks nres srt W HNC HNR0 HNR1 NRC MU WM MI.
    facts. unfold A_INSTANCE in *.
    change (1074072 + 64) with 1074136 in *. change (1074072 + 688) with 1074760 in *. change (1074072 + 112) with 1074184 in *. change (1074072 + 120) with 1074192 in *.
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep. zstep. zstep. zstep.
    apply evtA_done. eexists. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [assumption| assumption].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
End Large.


End ARUN_1.
