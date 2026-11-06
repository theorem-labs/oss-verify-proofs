(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import AsanAcct.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import
PropExec CatExec CatSim SeqExec StoreOk ShapeAlg SpinAlg Hoare AsanAcctShape SymExec2 SymExec2Sound SymRun SymDrive SymDriveX
HeapIface HeapIfaceA IcptIfaceA DrvKitA DrvNodesLazyK As0DrvKitA Ja0DrvEntry Ja0Drv_defs Ja0DrvLib.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__Ja0DrvPiece () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.LinuxProcessSem.Run."; "LinuxProcessSemantics.LinuxProcessSem.State."; "LinuxProcessSemantics.Riscv.Prelude."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.AsanAcct."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CatSim."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.HeapIface."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.HeapIfaceA."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Ja0DrvLib."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.ShapeAlg."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.SpinAlg."; "OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Asan.M."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["0A"; "1None"; "1list"; "1option"; "1prod"; "2and"; "2eq"; "2not"; "3Z"; "0HI"; "0K"; "0LB"; "0LK"; "4mkCfg"; "5Model"; "6bvmap"]; ["0M"; "0M0"; "0M1"; "0MV'"; "0R"; "0R'"; "7mrestrict"; "7same_but_materialized"; "8msteps"; "9credit"; ":ahid"; ":fframe"; ";CWA"; ";dinv"; "<FPState"; "<mkst"]; ["<seg_rom"; "=TSet"; ">srealizes"; "?loaded_segments"; "@le"; "@lt"; "@pow"; "0W"; "0a"; "0ar"; "0cr"; "0fx"; "0fx'"; "0model"; "0model1"; "0pc"]; ["0pc'"; "0scfg"; "0sp0"; "AZ_to_bv"; "Abv"]]).
Section Piece.
Variable scfg : SpuriousCfg.
Variable L : asan_layout.
Variable ar : asan_run.
Variable C : asan_statics_cells.
Variable IL : icpt_layout.
Variable HI : asan_iface.
Hypothesis HIok : asan_iface_ok L ar C scfg HI.
Variable sp0 : word.
Hypothesis Hsp : 0x7fff80000000 <= bv_unsigned sp0 <= 2 ^ 47.
Hypothesis DL : drv_layoutA L ar IL sp0.
Variable M0 : word -> option byte.
#[local] Notation dinvA := (dinv ar HI sp0 M0).
#[local] Notation rom := (seg_rom ASEGS).
Theorem drv_piece : ltac2:(TCodec.tc2 tcn__Ja0DrvPiece "TJ'2'4'8%2211%411&K%611&I'QDyR0%211'3y8%511%311p051'>'N&?y5%221:!p0D1&Q1'MvQ9v9vQBvAr?r>r=r<r;r:%;::987654321'H&Q3&Or8r7&F&J%12<:%321<&Q0%119%95=8731r9r6r5r4%>543216%A3@61&7'6%>2KIr1%A32L1(1%11Q?%63Q?31%811r2%H11%:3QC15%<11p051pRBQJ1'5&Q4z%221?&Q5&Q6+2+R0%3221%52E1%:271%J1@&QCr3%22R:1%Q411rBr@%Q=221rA%Q@3216%Q33R<61p0;1p0=1pRBRK1%QF1Q5&LrE%23R61Q2p041pRBS11rFrDrC%R?:R>R=R<R;3721Q8Q>&G%12DQ:%R02:H%R221QH%QE3RM1R<%R?1Q>%QH11%R81LrH%11N%QK3S431p051p0Q51pRBSC1'Q2vQA(=%RC5CQ3RLR8R;%221R8%54RF41RKp071p0A1p0E1p0H1pRNS@1pQ6SB1%RL5S5S3S2Q:RD%;21Q=%>4RO=1RLp041p0Q31p0Q:1p0R41p0RD1p0S71pFSD1pR@SF1pQ8SN1pS2T41pQ<SK1pS0T61pQ:SM1pRJT11pRHT21pRLT41pQ2T61p2TB1pRFT@1pJTB1pHTE1").
Proof.
intros LB LK cr A M model fx fx' R pc R' pc' MV' W K DI MS GR FZ WC KONT.
pose proof (dinv_lzinv scfg L ar C IL HI HIok sp0 DL M0 _ _ _ _ _ _ DI) as (HH & HL & HA & HM & Hh).
set (H := ahid A model) in *.
apply (srz_msteps_restricted_T ASEGS scfg H HH asegs_wx A (@mkst fx R pc M rom) (@mkst fx' R' pc' MV' rom) model K HL HA HM Hh MS).
intros model1 MI1 SBM HC.
change (unrestrict H (ms_mem (@mkst fx R pc M rom)) (@mkst fx' R' pc' MV' rom)) with (@mkst fx' R' pc' (munrestrict H M MV') rom).
set (M1 := munrestrict H M MV').
assert (VIS : mrestrict H M1 = MV') by (apply As0DrvKitA.mrestrict_munrestrict; intros a Ha; exact (HC a Ha)).
assert (FR1 : forall a, 0 <= a < 2 ^ 64 -> ~ W a -> M1 (Z_to_bv 64 a) = M (Z_to_bv 64 a)).
{ intros a Ha Hn. unfold M1, munrestrict. destruct (H (Z_to_bv 64 a)) eqn:E; [reflexivity|]. rewrite (FZ a Ha Hn). unfold mrestrict. rewrite E. reflexivity. }
assert (AH : ahid A model1 = H) by (unfold H; apply (ahid_sbm A model model1 SBM)).
apply (KONT M1 model1).
- apply (dinv_frame scfg L ar C IL HI HIok sp0 Hsp DL M0 LB LK cr A M M1 model model1 DI).
+ intros a Ha Hn. apply FR1; [exact Ha|]. intros Hw. exact (Hn (WC a Hw)).
+ intros a Ha. unfold M1, munrestrict. destruct (H a) eqn:E; [exact Ha|]. apply GR. unfold mrestrict. rewrite E. exact Ha.
+ exact (sbm_vml _ _ SBM).
+ exact MI1.
+ rewrite (sbm_halted_eq _ _ SBM). exact Hh.
- exact SBM.
- rewrite AH. exact VIS.
- exact FR1.
Qed.
End Piece.
