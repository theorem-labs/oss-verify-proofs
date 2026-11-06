(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import AsanAcct.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import
PropExec CatExec CatSim SeqExec StoreOk StreamSim ShapeAlg ShapeLaws SpinAlg Hoare AgentLib Spec AsanAcctShape SymExec2 SymExec2Sound SymRun SymDrive SymDriveX
HeapIface HeapIfaceA IcptIfaceAB0 DrvKitA DrvNodesLazyK As0DrvKitA Jb0DrvEntry Jb0Drv_defs Jb0DrvLib Jb0DrvRead Jb0DrvPiece Jb0DiagLoopK Jb0DrvStdio Jb0DrvPrintfK Jb0DrvPrintf1.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require L5Defs L5KnA L5Core ArtMem JbtFsInv.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import Jb0DrvP_dpX Jb0DrvP_dpX2_pre Jb0DrvP_dpX3_pre Jb0DrvP_dpX4_pre Jb0DrvP_dpXd_2 Jb0DrvP_dpXd_3 Jb0DrvP_dpXd_4 Jb0DrvP_dpXe
Jb0DrvP_dpXB Jb0DrvP_dpX2B_pre Jb0DrvP_dpX3B_pre Jb0DrvP_dpX4B_pre Jb0ExitCells.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLia. Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLiaT.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import SecKit. From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__Jb0DrvExit () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics."; "LinuxProcessSemantics.LinuxProcessSem.Run."; "LinuxProcessSemantics.LinuxProcessSem.State."; "LinuxProcessSemantics.Riscv.Prelude."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.As0DrvKitA."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.AsanAcct."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CatSim."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.HeapIface."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.HeapIfaceA."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Jb0DrvExit."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Jb0DrvExit.FPX_1.Exit."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Jb0DrvLib."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Jb0DrvPrintf1."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Jb0DrvPrintfK."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Jb0DrvStdio."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Jb0ExitCells."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5Defs.L5."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.ShapeAlg."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Spec."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.SpinAlg."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.StreamSim."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.SymDriveX."; "OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.AsanUbsan.M."; "Stdlib.Lists.List."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["0A"; "1S"; "1Some"; "1andb"; "1bool"; "1cons"; "1list"; "1nat"; "1nil"; "1option"; "1orb"; "1pair"; "1prod"; "1true"; "2I"; "2and"]; ["2eq"; "3Z"; "0H"; "0HI"; "0LB"; "0LK"; "4fetch_word"; "4word_to_le_bytes"; "5SpuriousCfg"; "5mkCfg"; "6FdChannel"; "6FdEntry"; "6Model"; "6fd_lookup"; "6m_fds"; "6m_fs"]; ["7bvmap"; "0M"; "0M'"; "0M0"; "0MV"; "0MV'"; "0R"; "0R'"; "8lzinv"; "9MInv"; "9mrestrict"; "9same_but_materialized"; ":msteps"; ";credit"; "<ahid"; "<fframe"]; [">exit_pre"; ">exit_preB"; ">exit_preT"; ">stdoutPA"; "=cells_at"; "?dinv"; "@stdoutXA"; "AstdoutA"; "BEX_CELLS"; "Catexit_cellsA"; "Dwritable"; "EFPState"; "Egetr"; "Emkst"; "Erdn"; "Eseg_rom"]; ["FTSet"; "Ft_emit"; "Ft_exit"; "GW"; "Gzero_lines"; "Hsrealizes"; "Iwseg_ok"; "JECALLW"; "Kloaded_segments"; "0S"; "LIn"; "Lnth_error"; "Madd"; "Mle"; "Mleb"; "Mlt"]; ["Mof_nat"; "Mpow"; "Mto_nat"; "0T"; "0a"; "0ar"; "0ax"; "0b"; "0bs"; "0canz"; "0cr"; "0fx"; "0fx'"; "0i"; "0l"; "0model"]; ["0model'"; "0n"; "0pc"; "0pc'"; "0scfg"; "0sp0"; "0st"; "NBV"; "NZ_to_bv"; "Nbv"; "0tid"; "0v"]]).
Local Ltac lia := L5FastLiaT.plia2.
Open Scope Z_scope.
Definition XC_CELLS : list (Z * Z * Z) :=
[(6884656, 4, 0); (6884691, 1, 0); (6884128, 8, 6884136); (6884120, 4, 1); (6884144, 8, 1136392); (6884400, 8, 618204); (6884116, 4, 0); (6884136, 8, 0); (6886088, 8, 0); (1281648, 8, 1281416); (1281556, 4, 4294967295); (1281456, 8, 0); (1281472, 8, 0); (1281424, 8, 0); (1281432, 8, 0); (1281408, 8, 1281176); (1281168, 8, 1280936); (1281076, 4, 4294967295); (1280976, 8, 0); (1280992, 8, 0); (1280944, 8, 0); (1280952, 8, 0)].
Definition XC_CELLS_T : list (Z * Z * Z) :=
[(6884656, 4, 0); (6884691, 1, 0); (6884128, 8, 6884136); (6884120, 4, 2); (6884144, 8, 1136392); (6884400, 8, 618204); (6884116, 4, 0); (6884136, 8, 0); (6886088, 8, 0); (1281648, 8, 1281416); (1281556, 4, 4294967295); (1281456, 8, 0); (1281472, 8, 0); (1281424, 8, 0); (1281432, 8, 0); (1281408, 8, 1281176); (1281168, 8, 1280936); (1281076, 4, 4294967295); (1280976, 8, 0); (1280992, 8, 0); (1280944, 8, 0); (1280952, 8, 0); (6746260, 1, 0); (6884152, 8, 1136392); (6884408, 8, 686244)].
Definition cells_at (MV : word -> option byte) (l : list (Z * Z * Z)) : Prop :=
Forall (fun c => rdn ASEGS MV (Z_to_bv 64 (fst (fst c))) (Z.to_nat (snd (fst c))) = Some (word_to_le_bytes (Z.to_nat (snd (fst c))) (Z_to_bv 64 (snd c)))) l.
Lemma cells_at_nth : ltac2:(TCodec.tc2 tcn__Jb0DrvExit "QG'S9yR0%211'9y8%511%311p051'6'<'A%2211%3212%511'7&QDr6r5%3221'@%A18&R;%13:65(2(;r4r3%34AA21r2%54BC21%72B1%<3;91%H1K%N11&QN&R8r8&S8%12Q5E&RB%11?%746531&G%62Q:A%2241%F2=1%K3=51p0@1p0N1pVHQ71pV4Q81pU:Q91pULQ61pUNQ81pR:Q?1").
Proof. intros MV l i a n v HC Hn. exact (proj1 (Forall_forall _ _) HC (a, n, v) (nth_error_In _ _ Hn)). Qed.
Definition exitA (tid : Z) (MV : word -> option byte) : Prop :=
cells_at MV XC_CELLS
/\ rdn ASEGS MV (Z_to_bv 64 6752792) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 tid)) /\ 1 <= tid <= 4194303
/\ (forall i, 0x138ea0 <= i < 0x139380 -> MV (Z_to_bv 64 i) = None).
Definition exitT (tid : Z) (MV : word -> option byte) : Prop :=
cells_at MV XC_CELLS_T
/\ rdn ASEGS MV (Z_to_bv 64 6752792) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 tid)) /\ 1 <= tid <= 4194303
/\ (forall i, 0x138ea0 <= i < 0x139380 -> MV (Z_to_bv 64 i) = None).
Definition XC_CELLS_B : list (Z * Z * Z) :=
[(6884656, 4, 0); (6884691, 1, 0); (6884128, 8, 6884136); (6884120, 4, 4); (6884144, 8, 1136392); (6884400, 8, 618204); (6884116, 4, 0); (6884136, 8, 0); (6886088, 8, 0); (1281648, 8, 1281416); (1281556, 4, 4294967295); (1281456, 8, 0); (1281472, 8, 0); (1281424, 8, 0); (1281432, 8, 0); (1281408, 8, 1281176); (1281168, 8, 1280936); (1281076, 4, 4294967295); (1280976, 8, 0); (1280992, 8, 0); (1280944, 8, 0); (1280952, 8, 0); (6884160, 8, 860168); (6884168, 8, 447508); (6884416, 8, 1280728); (6884424, 8, 0); (6746260, 1, 0); (6884152, 8, 1136392); (6884408, 8, 686244)].
Definition exitB (tid : Z) (MV : word -> option byte) : Prop :=
cells_at MV XC_CELLS_B
/\ rdn ASEGS MV (Z_to_bv 64 6752792) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 tid)) /\ 1 <= tid <= 4194303
/\ (forall i, 0x138ea0 <= i < 0x139380 -> MV (Z_to_bv 64 i) = None).
Lemma rdn_cons1 : ltac2:(TCodec.tc2 tcn__Jb0DrvExit "QJ'S9yR0%211'9y8%511%311p051'A'7'6%116&R=zr4%3221'@%>16&QN&R8r6&S8r5%22F1u1%746521(2(5(8%11H%33I@1%52D1%@3?71r7&R<+1%22@1%@2Q41%D4C51Hr3%>2M1%I3H31r8%F2Q::(1%11G%L4K431%D3Q:KQ1%F2Q51%Q13Q031p091p0C1p0Q51pUBQ:1pV4Q=1pU@QB1pU:Q@1pR:QB1").
Proof.
intros MV a b n bs Ha H1 H2. change (Datatypes.S n) with (1 + n)%nat. change (b :: bs) with ([b] ++ bs). apply (SeqExec.rdn_app ASEGS MV 1%nat n _ _ _ H1).
replace (Z_to_bv 64 a + nat_to_word 1)%bv with (Z_to_bv 64 (a + 1)); [exact H2|].
apply bv_eq. unfold nat_to_word. rewrite bv_add_unsigned, !Z_to_bv_unsigned. unfold bv_wrap. rewrite <- Zplus_mod. reflexivity.
Qed.
Ltac img_rd := vm_compute; apply f_equal; repeat (apply f_equal2; [apply bv_eq; reflexivity|]); reflexivity.
Lemma fetch_exitA : ltac2:(TCodec.tc2 tcn__Jb0DrvExit "A'@'9'S9yQ0%211%411&F&R8&S8yR0+QReS<%3221%6251(2&R7%22;1%@3;41").
Proof. vm_compute. reflexivity. Qed.
Lemma msteps_vis_fx : ltac2:(TCodec.tc2 tcn__Jb0DrvExit "RF'H'S9yR0%211'4p021'6'<'A%2211%411'QK&Q0y5%221;'9y8%@11%311p0@1'L&R0&Q8&R8r<r;r2%544321'Q<&QMr9r8&Q:r=r7%3221&QO%11>%95=8731r:r6r5r4%>543216%@3E61'Q9r?r1%3221&Q;%12@H'@rB%E21;%33Q31H'R5rD(Ir@%N51Q3Q2BF%321B%64Q651Np081p0=1p0@1pV2Q=1pR6Q?1%Q65Q2Q:LQ5N%;21K%>4Q>;1Kp041p0K1p0Q=1pU8QD1pV0QF1pR<QH1pV8R91pR@QO1pR4QK1pV6R<1pR>R21pUJR61pUHR71p2R91pQ6R?1pV:RE1").
Proof.
intros scfg H A fx fx' R pc M R' pc' MV' model T (HH & HL & HA & HM & Hh) MS KONT.
apply (srz_msteps_restricted_T ASEGS scfg H HH asegs_wx A (@mkst fx R pc M (seg_rom ASEGS)) (@mkst fx' R' pc' MV' (seg_rom ASEGS)) model T HL HA HM Hh MS).
intros model1 MI1 SBM HC.
change (unrestrict H (ms_mem (@mkst fx R pc M (seg_rom ASEGS))) (@mkst fx' R' pc' MV' (seg_rom ASEGS))) with (@mkst fx' R' pc' (munrestrict H M MV') (seg_rom ASEGS)).
apply (KONT _ model1 MI1 SBM). apply As0DrvKitA.mrestrict_munrestrict. intros a Ha. exact (HC a Ha).
Qed.
Section FPX_1. Context {fx : PropExec.FPState}.
Variable scfg : SpuriousCfg.
Section Exit.
Variable L : asan_layout.
Variable ar : asan_run.
Variable C : asan_statics_cells.
Variable IL : icpt_layout.
Variable HI : asan_iface.
Hypothesis HIok : asan_iface_ok L ar C scfg HI.
Hypothesis ICok : aicpt_ok L ar IL scfg HI.
Hypothesis ILY : as0_icpt_layout IL.
Variable sp0 : word.
Hypothesis Hsp : 0x7fff80000000 <= bv_unsigned sp0 <= 2 ^ 47.
Hypothesis Hal : bv_unsigned sp0 mod 16 = 0.
Hypothesis DL : drv_layoutA L ar IL sp0.
Hypothesis Hex : incl EX_CELLS (asc_cells C).
Variable M0 : word -> option byte.
#[local] Notation dinvA := (dinv ar HI sp0 M0).
#[local] Notation usp := (bv_unsigned sp0).
#[local] Notation rom := (seg_rom ASEGS).
Section SE.
Local Abbreviation SEC_T_ex_cell_vis := (ltac2:(TCodec.tc2 tcn__Jb0DrvExit "R5'6'<'A%2211%411&Q?%611&Q='S9yR0%211'9y8%511%311p051'L'QEvREvCvS5vQ3r9r8r7r6r5r4%;::987654321&R:%M2KL(;r3%24OO61r2%44Q0Q121&QH%83721'@%Q71J%M11&QN&R8&Q:&Q>%12FD%321F&S8%12Q7F&RB%11G%:49531(2&G%72Q=F%2251%42A1%C3A61p0E1p0O1pVHQJ1pV4QK1pU:QL1pV0Q?1pR4QA1p2QM1pUFQK1pQ<QM1pQ:R01")) (only parsing).
Variable LB : ltac:(sec_ty2 constr:(SEC_T_ex_cell_vis) 0%nat 0%nat).
Variable LK : ltac:(sec_ty2 constr:(SEC_T_ex_cell_vis) 1%nat 0%nat).
Variable cr : ltac:(sec_ty2 constr:(SEC_T_ex_cell_vis) 2%nat 0%nat).
Variable A : ltac:(sec_ty2 constr:(SEC_T_ex_cell_vis) 3%nat 0%nat).
Variable M : ltac:(sec_ty2 constr:(SEC_T_ex_cell_vis) 4%nat 0%nat).
Variable model : ltac:(sec_ty2 constr:(SEC_T_ex_cell_vis) 5%nat 0%nat).
Variable a : ltac:(sec_ty2 constr:(SEC_T_ex_cell_vis) 6%nat 0%nat).
Variable n : ltac:(sec_ty2 constr:(SEC_T_ex_cell_vis) 7%nat 0%nat).
Variable v : ltac:(sec_ty2 constr:(SEC_T_ex_cell_vis) 8%nat 0%nat).
Lemma ex_cell_vis : ltac:(sec_stmt2 constr:(SEC_T_ex_cell_vis) 9%nat 0%nat).
Proof using scfg L C IL HIok Hsp DL Hex LB LK cr A M model a n v.
intros D Hin.
pose proof (di_inv _ _ _ _ _ _ _ _ _ _ D) as HH.
destruct (aio_statics _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as (_ & CS). rewrite (dla_segs _ _ _ _ DL) in CS.
pose proof (proj1 (Forall_forall _ _) CS (a, n, v) (Hex _ Hin)) as X. unfold cell_is in X. cbn [fst snd] in X.
rewrite rdn_mrestrict_eq; [exact X|].
intros k Hk. unfold woff.
assert (B : 0 <= a /\ a + Z.of_nat (Z.to_nat n) <= 0x693000).
{ unfold EX_CELLS in Hin. cbn [In] in Hin. repeat (destruct Hin as [Hin|Hin]; [injection Hin as <- <- <-; cbn; lia|]). destruct Hin. }
rewrite (u64_lit a) by lia. apply (vis_low scfg L ar C IL HI HIok sp0 DL M0 _ _ _ _ _ _ _ D). lia.
Qed.
End SE.
#[using="scfg L C IL HIok Hsp DL"] Lemma ax_cells_vis : ltac2:(TCodec.tc2 tcn__Jb0DrvExit "Q>'6'<'A%2211%411&Q?%611&Q='S9yR0%211'9y8%511%311p051'L'4'QEvREvCvS5vQ3r7r6r5r4r3r2%;::987654321&QI%1253&Q:&Q>%12:8%321:%6219p061p091pU>F1pV0H1pR4J1p2Q61pUFQ41pQ<Q61pQ:Q91").
Proof.
intros LB LK cr A M model ax D H. unfold atexit_cellsA in *. rewrite Forall_forall in *. intros c Hc.
pose proof (ax_cells_in ax c Hc) as (B1 & B2 & B3). specialize (H c Hc). unfold ax_cell in *.
rewrite rdn_mrestrict_eq; [exact H|].
intros k Hk. unfold woff. unfold AXLO, AXHI in *.
rewrite (u64_lit (fst (fst c))) by lia. apply (vis_low scfg L ar C IL HI HIok sp0 DL M0 _ _ _ _ _ _ _ D). lia.
Qed.
Section SE.
Local Abbreviation SEC_T_sh_writable := (ltac2:(TCodec.tc2 tcn__Jb0DrvExit "R3'6'<'A%2211%411&Q?%611&Q='S9yR0%211'9y8%511%311p051'L'QEvREvCvS5vQ3r8r7r6r5r4r3%;::987654321'@'4&:&3&R>+Qoooaa<%2218&R<r2%22;1+Qoooai8%7221%9261+RPPSl^D%:21@+RPPSlc@%<271%>231%@261(=%D3C21&QJ&R8&Q:&Q>%12OM%321O%6451NMp081p0N1pV4QI1pU:QJ1pV0Q=1pR4Q?1p2QK1pUFQI1pQ<QK1pQ:QN1")) (only parsing).
Variable LB : ltac:(sec_ty2 constr:(SEC_T_sh_writable) 0%nat 0%nat).
Variable LK : ltac:(sec_ty2 constr:(SEC_T_sh_writable) 1%nat 0%nat).
Variable cr : ltac:(sec_ty2 constr:(SEC_T_sh_writable) 2%nat 0%nat).
Variable A : ltac:(sec_ty2 constr:(SEC_T_sh_writable) 3%nat 0%nat).
Variable M : ltac:(sec_ty2 constr:(SEC_T_sh_writable) 4%nat 0%nat).
Variable model : ltac:(sec_ty2 constr:(SEC_T_sh_writable) 5%nat 0%nat).
Variable a : ltac:(sec_ty2 constr:(SEC_T_sh_writable) 6%nat 0%nat).
Variable n : ltac:(sec_ty2 constr:(SEC_T_sh_writable) 7%nat 0%nat).
Lemma sh_writable : ltac:(sec_stmt2 constr:(SEC_T_sh_writable) 8%nat 0%nat).
Proof using scfg L IL ICok ILY Hsp DL LB LK cr A M model a n.
intros D Hb.
pose proof (di_inv _ _ _ _ _ _ _ _ _ _ D) as HH.
apply L5Core.L5C.writable_of_defined; [|rewrite !orb_true_iff, !andb_true_iff, !Z.leb_le in Hb; lia | rewrite !orb_true_iff, !andb_true_iff, !Z.leb_le in Hb; lia].
intros i Hi. set (x := a + i).
assert (Hx : 2147468844 <= x < 2147469096 \/ 2147611092 <= x < 2147611248) by (unfold x; rewrite !orb_true_iff, !andb_true_iff, !Z.leb_le in Hb; lia).
assert (DEF : M (Z_to_bv 64 x) <> None).
{ apply (aic_shadow_defined _ _ _ _ _ ICok _ _ _ _ _ _ _ HH x). left. unfold LOWSH_LO, LOWSH_HI. lia. }
assert (VIS : ahid A model (Z_to_bv 64 x) = false).
{ unfold ahid, mkH. apply andb_false_intro2. apply negb_false_iff.
pose proof (aic_globals _ _ _ _ _ ICok _ _ _ _ _ _ _ HH) as G. rewrite (aicl_globals IL ILY) in G.
destruct Hx as [Hx|Hx].
- pose proof (proj2 (Forall_inv G)) as SA. cbn [fst snd] in SA.
specialize (SA 2147468844 ltac:(unfold in_shadow_of, S, SB; cbn; lia)).
replace (page_base (Z_to_bv 64 x)) with (page_base (Z_to_bv 64 2147468844)); [exact SA|].
unfold page_base, page_base_of. rewrite !u64_lit by lia. f_equal. unfold page_size.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). lia.
- destruct (aic_img_shadow _ _ _ _ _ ICok _ _ _ _ _ _ _ HH 0x139380 16) as (_ & SA);
[rewrite (dla_img_lo _ _ _ _ DL); lia | rewrite (dla_img_hi _ _ _ _ DL); lia | lia
| rewrite (aicl_poison IL ILY); repeat (apply Forall_cons; [cbn [fst snd]; lia|]); apply Forall_nil |].
specialize (SA 2147611248 ltac:(unfold in_shadow_of, S, SB; cbn; lia)).
replace (page_base (Z_to_bv 64 x)) with (page_base (Z_to_bv 64 2147611248)); [exact SA|].
unfold page_base, page_base_of. rewrite !u64_lit by lia. f_equal. unfold page_size. lia.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false). }
unfold mrestrict. rewrite VIS. exact DEF.
Qed.
End SE.
#[using="sp0 Hsp M0"] Lemma wsg_writable : ltac2:(TCodec.tc2 tcn__Jb0DrvExit "Q>'S9yR0%211'9y8%511%311p051'A'7'@'4&R6&R8&S8r2%22?1r1%63521(=%:3921&R=zr3%3221&R<r4&R@%115%4231&RA+2+QO%3221%=251&QJr6r5%;1<%44J321p061p0A1p0F1pV4Q21pU:Q41pR:Q61").
Proof.
intros MV a n W Ha Hn d k Hd Hk.
apply (store_ok_window ASEGS MV (Z_to_bv 64 a) (Z_to_bv 64 (a + d)) n k a (a + Z.of_nat n)); first [exact W | reflexivity | lia | rewrite u64_lit by lia; lia].
Qed.
Definition exit_pre (LB : list (Z * Z)) (LK : list fframe) (cr : credit) (A : list (Z * Z)) (M : word -> option byte) (model : Model) (S tid : Z) : Prop :=
let MV := mrestrict (ahid A model) M in
dinvA LB LK cr A M model /\ usp - 4096 <= S /\ S <= usp /\ S mod 16 = 0
/\ (forall a n, usp - 8388608 <= a -> a + n <= usp -> forall d (k : nat), 0 <= d -> d + Z.of_nat k <= n -> store_ok ASEGS MV (Z_to_bv 64 (a + d)) k = true)
/\ (forall i, 65536 <= i < 1269760 -> MV (Z_to_bv 64 i) = None)
/\ exitA tid MV.
Definition exit_preT (LB : list (Z * Z)) (LK : list fframe) (cr : credit) (A : list (Z * Z)) (M : word -> option byte) (model : Model) (S tid : Z) : Prop :=
let MV := mrestrict (ahid A model) M in
dinvA LB LK cr A M model /\ usp - 4096 <= S /\ S <= usp /\ S mod 16 = 0
/\ (forall a n, usp - 8388608 <= a -> a + n <= usp -> forall d (k : nat), 0 <= d -> d + Z.of_nat k <= n -> store_ok ASEGS MV (Z_to_bv 64 (a + d)) k = true)
/\ (forall i, 65536 <= i < 1269760 -> MV (Z_to_bv 64 i) = None)
/\ exitT tid MV.
Definition exit_preB (LB : list (Z * Z)) (LK : list fframe) (cr : credit) (A : list (Z * Z)) (M : word -> option byte) (model : Model) (S tid : Z) : Prop :=
let MV := mrestrict (ahid A model) M in
dinvA LB LK cr A M model /\ usp - 4096 <= S /\ S <= usp /\ S mod 16 = 0
/\ (forall a n, usp - 8388608 <= a -> a + n <= usp -> forall d (k : nat), 0 <= d -> d + Z.of_nat k <= n -> store_ok ASEGS MV (Z_to_bv 64 (a + d)) k = true)
/\ (forall i, 65536 <= i < 1269760 -> MV (Z_to_bv 64 i) = None)
/\ exitB tid MV.
Section SE.
Local Abbreviation SEC_T_exit_run_0 := (ltac2:(TCodec.tc2 tcn__Jb0DrvExit "SC'6'<'A%2211%411&Q?%611&Q='S9yR0%211'9y8%511%311p051'L&Q0y5%2219&QBr:r9r8r7r6r5r3r1%9887654321&Q:&Q>%1297%3219'?&R=zr4%3221&R?+X0%2241%8241'@&QL(S7+1(>%33N21%52I1&S8+QRclH%22Q;1%:3Q;41+2%:3Q518%<2Q11%72Q@Q1%?3Q@21+4%?3Q:1=%A2Q71+V^Rf0%=2QF1%E3QF31+:%E3Q@1C%G2Q>1%B2QKQ=%J3QK21&QG%12Q3Q>&QF%11QA'R5&R8vS4(I&QMvRKr=+QRejL%Q02R91r?&QO%11:%8576431r>%;221&R2r;%Q92RB1&O%116%5231%E4DC71p0G1p0J1p0M1p0Q31p0Q:1p0Q@1p0QL1tR:RHR61p0R;1pVFS71pV>S81pTDS91pR>RI1pV0RM1pR4RO1p2S;1pUFS91pQ<S;1pQ:S>1")) (only parsing).
Variable LB : ltac:(sec_ty2 constr:(SEC_T_exit_run_0) 0%nat 0%nat).
Variable LK : ltac:(sec_ty2 constr:(SEC_T_exit_run_0) 1%nat 0%nat).
Variable cr : ltac:(sec_ty2 constr:(SEC_T_exit_run_0) 2%nat 0%nat).
Variable A : ltac:(sec_ty2 constr:(SEC_T_exit_run_0) 3%nat 0%nat).
Variable M : ltac:(sec_ty2 constr:(SEC_T_exit_run_0) 4%nat 0%nat).
Variable model : ltac:(sec_ty2 constr:(SEC_T_exit_run_0) 5%nat 0%nat).
Variable R : ltac:(sec_ty2 constr:(SEC_T_exit_run_0) 6%nat 0%nat).
Variable S : ltac:(sec_ty2 constr:(SEC_T_exit_run_0) 7%nat 0%nat).
Variable st : ltac:(sec_ty2 constr:(SEC_T_exit_run_0) 8%nat 0%nat).
Variable tid : ltac:(sec_ty2 constr:(SEC_T_exit_run_0) 9%nat 0%nat).
Lemma exit_run_0 : ltac:(sec_stmt2 constr:(SEC_T_exit_run_0) 10%nat 0%nat).
Proof using L C IL HIok ICok ILY Hsp DL Hex LB LK cr A M model R S st tid.
intros (D & HS1 & HS2 & HS16 & WIN & IMGc & (XC & TIDC & HTr & DESC)) MV Hst G1 G2 G4 G10 SO SOX.
pose proof Hsp as Hsp'. destruct SO as (_ & _ & _ & SOwpos & SOwbase & SOlock & _). destruct SOX as (_ & _ & _ & SOrpos & SOrend).
set (V := fun n : nat => match n with 2%nat => S | 44%nat => tid | _ => 0 end).
assert (HS64 : 0 <= V 2%nat < 2 ^ 64) by (cbn [V]; clear - Hsp' HS1 HS2; lia).
assert (HT64 : 0 <= V 44%nat < 2 ^ 64) by (cbn [V]; clear - HTr; lia).
assert (HSr : 140735332552704 <= V 2%nat <= 140737488355328) by (cbn [V]; clear - Hsp' HS1 HS2; lia).
assert (HSa : AS0DRVP_dpX.aligned (V 2%nat) 16) by (cbn [V]; exact HS16).
assert (CWR : L5Defs.L5.writable ASEGS MV (V 2%nat - 320) 320).
{ cbn [V]. intros d k Hd Hk. apply (WIN (S - 320) 320); clear - Hsp' HS1 HS2 Hd Hk; lia. }
assert (CDF : L5Defs.L5.defined MV (V 2%nat - 320) 320).
{ cbn [V]. intros i Hi. apply (store_ok_defined sp0); [clear - Hsp' HS1 HS2 Hi; lia|]. apply (WIN (S - 320) 320); clear - Hsp' HS1 HS2 Hi; lia. }
assert (WSG : forall a (n : nat), wseg_ok ASEGS (Z_to_bv 64 a) n = true -> (0 <=? a) && (a + Z.of_nat n <=? 2 ^ 63) = true -> L5Defs.L5.writable ASEGS MV a (Z.of_nat n)).
{ intros a n W Hb. apply andb_prop in Hb as (B1 & B2). apply Z.leb_le in B1, B2. exact (wsg_writable MV a n W B1 B2). }
assert (SHW : forall a n, ((2147468844 <=? a) && (a + n <=? 2147469096) || (2147611092 <=? a) && (a + n <=? 2147611248)) = true -> L5Defs.L5.writable ASEGS MV a n)
by (intros a n Hb; exact (sh_writable _ _ _ _ _ _ a n D Hb)).
assert (STC : forall (i : nat) a n v, nth_error EX_CELLS i = Some (a, n, v) -> rdn ASEGS MV (Z_to_bv 64 a) (Z.to_nat n) = Some (word_to_le_bytes (Z.to_nat n) (Z_to_bv 64 v)))
by (intros i a n v Hn; exact (ex_cell_vis _ _ _ _ _ _ a n v D (nth_error_In _ _ Hn))).
assert (STC1 : forall (i : nat) a v, nth_error EX_CELLS i = Some (a, 1, v) -> (0 <=? v) && (v <? 2 ^ 64) = true -> rdn ASEGS MV (Z_to_bv 64 a) 1 = Some [Z_to_bv 8 v]).
{ intros i a v Hn Hb. apply andb_prop in Hb as (B1 & B2). apply Z.leb_le in B1. apply Z.ltb_lt in B2. rewrite <- (ArtMem.art_bytes1 v (conj B1 B2)). exact (STC i a 1 v Hn). }
assert (XCC : forall (i : nat) a n v, nth_error XC_CELLS_T i = Some (a, n, v) -> rdn ASEGS MV (Z_to_bv 64 a) (Z.to_nat n) = Some (word_to_le_bytes (Z.to_nat n) (Z_to_bv 64 v)))
by (intros i a n v Hn; exact (cells_at_nth MV XC_CELLS_T i a n v XC Hn)).
assert (XCC1 : forall (i : nat) a v, nth_error XC_CELLS_T i = Some (a, 1, v) -> (0 <=? v) && (v <? 2 ^ 64) = true -> rdn ASEGS MV (Z_to_bv 64 a) 1 = Some [Z_to_bv 8 v]).
{ intros i a v Hn Hb. apply andb_prop in Hb as (B1 & B2). apply Z.leb_le in B1. apply Z.ltb_lt in B2. rewrite <- (ArtMem.art_bytes1 v (conj B1 B2)). exact (XCC i a 1 v Hn). }
assert (DSC : forall a (n : nat) bs, rdn ASEGS (fun _ => None) (Z_to_bv 64 a) n = Some bs -> (0x138ea0 <=? a) && (a + Z.of_nat n <=? 0x139380) = true -> rdn ASEGS MV (Z_to_bv 64 a) n = Some bs).
{ intros a n bs Hr Hb. apply andb_prop in Hb as (B1 & B2). apply Z.leb_le in B1, B2. apply (img_cell MV a n bs Hr); [lia | lia|]. intros i Hi. apply DESC. lia. }
destruct (AS0DRVP_dpX.dpX_conc fx R MV V HS64 HT64
G1 G2 G4 HSr HSa CWR
CDF IMGc (WSG 1282944 8%nat ltac:(vm_compute; reflexivity) eq_refl) (WSG 1283024 1%nat ltac:(vm_compute; reflexivity) eq_refl) (WSG 1286896 8%nat ltac:(vm_compute; reflexivity) eq_refl) (WSG 6884112 1%nat ltac:(vm_compute; reflexivity) eq_refl)
(WSG 6884120 4%nat ltac:(vm_compute; reflexivity) eq_refl) (WSG 6884128 8%nat ltac:(vm_compute; reflexivity) eq_refl) (WSG 6884656 4%nat ltac:(vm_compute; reflexivity) eq_refl) (SHW 2147468844 1 eq_refl) (SHW 2147468845 1 eq_refl) (SHW 2147468846 1 eq_refl)
(SHW 2147468847 1 eq_refl) (SHW 2147468856 1 eq_refl) (SHW 2147468857 1 eq_refl) (SHW 2147468858 1 eq_refl) (SHW 2147468859 1 eq_refl) (SHW 2147468860 1 eq_refl)
(SHW 2147468860 4 eq_refl) (SHW 2147468861 1 eq_refl) (SHW 2147468862 1 eq_refl) (SHW 2147468863 1 eq_refl) (SHW 2147468864 4 eq_refl) (SHW 2147468868 1 eq_refl)
(SHW 2147468868 4 eq_refl) (SHW 2147468869 1 eq_refl) (SHW 2147468870 1 eq_refl) (SHW 2147468871 1 eq_refl) (SHW 2147468916 1 eq_refl) (SHW 2147468917 1 eq_refl)
(SHW 2147468918 1 eq_refl) (SHW 2147468919 1 eq_refl) (SHW 2147468920 1 eq_refl) (SHW 2147468921 1 eq_refl) (SHW 2147468922 1 eq_refl) (SHW 2147468923 1 eq_refl)
(SHW 2147468924 1 eq_refl) (SHW 2147468925 1 eq_refl) (SHW 2147468926 1 eq_refl) (SHW 2147468927 1 eq_refl) (SHW 2147468928 1 eq_refl) (SHW 2147468929 1 eq_refl)
(SHW 2147468930 1 eq_refl) (SHW 2147468931 1 eq_refl) (SHW 2147468932 1 eq_refl) (SHW 2147468932 4 eq_refl) (SHW 2147468933 1 eq_refl) (SHW 2147468934 1 eq_refl)
(SHW 2147468935 1 eq_refl) (SHW 2147468936 4 eq_refl) (SHW 2147468940 1 eq_refl) (SHW 2147468940 4 eq_refl) (SHW 2147468941 1 eq_refl) (SHW 2147468942 1 eq_refl)
(SHW 2147468943 1 eq_refl) (SHW 2147468944 1 eq_refl) (SHW 2147468944 4 eq_refl) (SHW 2147468945 1 eq_refl) (SHW 2147468946 1 eq_refl) (SHW 2147468947 1 eq_refl)
(SHW 2147468948 4 eq_refl) (SHW 2147468952 4 eq_refl) (SHW 2147468956 1 eq_refl) (SHW 2147468956 4 eq_refl) (SHW 2147468957 1 eq_refl) (SHW 2147468958 1 eq_refl)
(SHW 2147468959 1 eq_refl) (SHW 2147468960 1 eq_refl) (SHW 2147468960 4 eq_refl) (SHW 2147468961 1 eq_refl) (SHW 2147468962 1 eq_refl) (SHW 2147468963 1 eq_refl)
(SHW 2147468964 4 eq_refl) (SHW 2147468968 4 eq_refl) (SHW 2147468972 1 eq_refl) (SHW 2147468972 4 eq_refl) (SHW 2147468973 1 eq_refl) (SHW 2147468974 1 eq_refl)
(SHW 2147468975 1 eq_refl) (SHW 2147468976 1 eq_refl) (SHW 2147468977 1 eq_refl) (SHW 2147468978 1 eq_refl) (SHW 2147468979 1 eq_refl) (SHW 2147468980 1 eq_refl)
(SHW 2147468980 4 eq_refl) (SHW 2147468981 1 eq_refl) (SHW 2147468982 1 eq_refl) (SHW 2147468983 1 eq_refl) (SHW 2147468984 4 eq_refl) (SHW 2147468988 1 eq_refl)
(SHW 2147468988 4 eq_refl) (SHW 2147468989 1 eq_refl) (SHW 2147468990 1 eq_refl) (SHW 2147468991 1 eq_refl) (SHW 2147468992 1 eq_refl) (SHW 2147468992 4 eq_refl)
(SHW 2147468993 1 eq_refl) (SHW 2147468994 1 eq_refl) (SHW 2147468995 1 eq_refl) (SHW 2147468996 4 eq_refl) (SHW 2147469000 4 eq_refl) (SHW 2147469004 1 eq_refl)
(SHW 2147469004 4 eq_refl) (SHW 2147469005 1 eq_refl) (SHW 2147469006 1 eq_refl) (SHW 2147469007 1 eq_refl) (SHW 2147469008 1 eq_refl) (SHW 2147469008 4 eq_refl)
(SHW 2147469009 1 eq_refl) (SHW 2147469010 1 eq_refl) (SHW 2147469011 1 eq_refl) (SHW 2147469012 4 eq_refl) (SHW 2147469016 4 eq_refl) (SHW 2147469020 1 eq_refl)
(SHW 2147469020 4 eq_refl) (SHW 2147469021 1 eq_refl) (SHW 2147469022 1 eq_refl) (SHW 2147469023 1 eq_refl) (SHW 2147469024 1 eq_refl) (SHW 2147469024 4 eq_refl)
(SHW 2147469025 1 eq_refl) (SHW 2147469026 1 eq_refl) (SHW 2147469027 1 eq_refl) (SHW 2147469028 4 eq_refl) (SHW 2147469032 1 eq_refl) (SHW 2147469032 4 eq_refl)
(SHW 2147469033 1 eq_refl) (SHW 2147469034 1 eq_refl) (SHW 2147469035 1 eq_refl) (SHW 2147469036 1 eq_refl) (SHW 2147469036 4 eq_refl) (SHW 2147469037 1 eq_refl)
(SHW 2147469038 1 eq_refl) (SHW 2147469039 1 eq_refl) (SHW 2147469040 4 eq_refl) (SHW 2147469044 1 eq_refl) (SHW 2147469044 4 eq_refl) (SHW 2147469045 1 eq_refl)
(SHW 2147469046 1 eq_refl) (SHW 2147469047 1 eq_refl) (SHW 2147469048 1 eq_refl) (SHW 2147469048 4 eq_refl) (SHW 2147469049 1 eq_refl) (SHW 2147469050 1 eq_refl)
(SHW 2147469051 1 eq_refl) (SHW 2147469052 4 eq_refl) (SHW 2147469056 1 eq_refl) (SHW 2147469056 4 eq_refl) (SHW 2147469057 1 eq_refl) (SHW 2147469058 1 eq_refl)
(SHW 2147469059 1 eq_refl) (SHW 2147469060 1 eq_refl) (SHW 2147469060 4 eq_refl) (SHW 2147469061 1 eq_refl) (SHW 2147469062 1 eq_refl) (SHW 2147469063 1 eq_refl)
(SHW 2147469064 4 eq_refl) (SHW 2147469068 4 eq_refl) (SHW 2147469072 1 eq_refl) (SHW 2147469072 4 eq_refl) (SHW 2147469073 1 eq_refl) (SHW 2147469074 1 eq_refl)
(SHW 2147469075 1 eq_refl) (SHW 2147469076 1 eq_refl) (SHW 2147469077 1 eq_refl) (SHW 2147469078 1 eq_refl) (SHW 2147469079 1 eq_refl) (SHW 2147469080 1 eq_refl)
(SHW 2147469081 1 eq_refl) (SHW 2147469082 1 eq_refl) (SHW 2147469083 1 eq_refl) (SHW 2147469084 1 eq_refl) (SHW 2147469084 4 eq_refl) (SHW 2147469085 1 eq_refl)
(SHW 2147469086 1 eq_refl) (SHW 2147469087 1 eq_refl) (SHW 2147469088 4 eq_refl) (SHW 2147469092 1 eq_refl) (SHW 2147469092 4 eq_refl) (SHW 2147469093 1 eq_refl)
(SHW 2147469094 1 eq_refl) (SHW 2147469095 1 eq_refl) (SHW 2147611092 1 eq_refl) (SHW 2147611092 4 eq_refl) (SHW 2147611093 1 eq_refl) (SHW 2147611094 1 eq_refl)
(SHW 2147611095 1 eq_refl) (SHW 2147611096 4 eq_refl) (SHW 2147611100 4 eq_refl) (SHW 2147611104 4 eq_refl) (SHW 2147611108 4 eq_refl) (SHW 2147611112 4 eq_refl)
(SHW 2147611116 4 eq_refl) (SHW 2147611120 8 eq_refl) (SHW 2147611128 8 eq_refl) (SHW 2147611136 8 eq_refl) (SHW 2147611144 8 eq_refl) (SHW 2147611152 8 eq_refl)
(SHW 2147611160 8 eq_refl) (SHW 2147611168 8 eq_refl) (SHW 2147611176 8 eq_refl) (SHW 2147611184 8 eq_refl) (SHW 2147611192 8 eq_refl) (SHW 2147611200 8 eq_refl)
(SHW 2147611208 8 eq_refl) (SHW 2147611216 4 eq_refl) (SHW 2147611220 4 eq_refl) (SHW 2147611224 4 eq_refl) (SHW 2147611228 4 eq_refl) (SHW 2147611232 4 eq_refl)
(SHW 2147611236 4 eq_refl) (SHW 2147611240 1 eq_refl) (SHW 2147611240 4 eq_refl) (SHW 2147611241 1 eq_refl) (SHW 2147611242 1 eq_refl) (SHW 2147611243 1 eq_refl)
TIDC HTr (XCC 0%nat 6884656 4 0 eq_refl) (XCC1 1%nat 6884691 0 eq_refl eq_refl) (XCC 2%nat 6884128 8 6884136 eq_refl) (XCC 3%nat 6884120 4 2 eq_refl)
(XCC 23%nat 6884152 8 1136392 eq_refl) (XCC 24%nat 6884408 8 686244 eq_refl) (XCC 6%nat 6884116 4 0 eq_refl) (XCC1 22%nat 6746260 0 eq_refl eq_refl) (XCC 4%nat 6884144 8 1136392 eq_refl) (XCC 5%nat 6884400 8 618204 eq_refl)
(STC1 10%nat 1894624 0 eq_refl eq_refl) (XCC 7%nat 6884136 8 0 eq_refl) (STC1 3%nat 1283024 0 eq_refl eq_refl) (STC 0%nat 1270192 8 1270192 eq_refl) (STC 2%nat 1282944 8 1 eq_refl) (STC 4%nat 1286736 4 1 eq_refl)
(STC 5%nat 1286896 8 0 eq_refl) (STC1 8%nat 1300248 1 eq_refl eq_refl) (STC 7%nat 1296952 8 2147450880 eq_refl) (DSC 1281696 8%nat (word_to_le_bytes 8 (Z_to_bv 64 143712)) ltac:(img_rd) eq_refl) (DSC 1281712 1%nat [Z_to_bv 8 32] ltac:(img_rd) eq_refl) (STC1 6%nat 1295004 1 eq_refl eq_refl)
(DSC 1281712 8%nat (word_to_le_bytes 8 (Z_to_bv 64 32)) ltac:(img_rd) eq_refl) (STC 9%nat 1893856 8 18446744073709551615 eq_refl) (STC 1%nat 1270704 8 1207272 eq_refl) (DSC 1281752 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1281760 8%nat (word_to_le_bytes 8 (Z_to_bv 64 143808)) ltac:(img_rd) eq_refl) (DSC 1281776 1%nat [Z_to_bv 8 32] ltac:(img_rd) eq_refl)
(DSC 1281776 8%nat (word_to_le_bytes 8 (Z_to_bv 64 32)) ltac:(img_rd) eq_refl) (DSC 1281816 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1281824 8%nat (word_to_le_bytes 8 (Z_to_bv 64 143840)) ltac:(img_rd) eq_refl) (DSC 1281840 1%nat [Z_to_bv 8 96] ltac:(img_rd) eq_refl) (DSC 1281840 8%nat (word_to_le_bytes 8 (Z_to_bv 64 96)) ltac:(img_rd) eq_refl) (DSC 1281880 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl)
(DSC 1281888 8%nat (word_to_le_bytes 8 (Z_to_bv 64 144288)) ltac:(img_rd) eq_refl) (DSC 1281904 1%nat [Z_to_bv 8 32] ltac:(img_rd) eq_refl) (DSC 1281904 8%nat (word_to_le_bytes 8 (Z_to_bv 64 32)) ltac:(img_rd) eq_refl) (DSC 1281944 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1281952 8%nat (word_to_le_bytes 8 (Z_to_bv 64 144320)) ltac:(img_rd) eq_refl) (DSC 1281968 1%nat [Z_to_bv 8 64] ltac:(img_rd) eq_refl)
(DSC 1281968 8%nat (word_to_le_bytes 8 (Z_to_bv 64 64)) ltac:(img_rd) eq_refl) (DSC 1282008 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1282016 8%nat (word_to_le_bytes 8 (Z_to_bv 64 144384)) ltac:(img_rd) eq_refl) (DSC 1282032 1%nat [Z_to_bv 8 32] ltac:(img_rd) eq_refl) (DSC 1282032 8%nat (word_to_le_bytes 8 (Z_to_bv 64 32)) ltac:(img_rd) eq_refl) (DSC 1282072 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl)
(DSC 1282080 8%nat (word_to_le_bytes 8 (Z_to_bv 64 144416)) ltac:(img_rd) eq_refl) (DSC 1282096 1%nat [Z_to_bv 8 96] ltac:(img_rd) eq_refl) (DSC 1282096 8%nat (word_to_le_bytes 8 (Z_to_bv 64 96)) ltac:(img_rd) eq_refl) (DSC 1282136 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1282144 8%nat (word_to_le_bytes 8 (Z_to_bv 64 144512)) ltac:(img_rd) eq_refl) (DSC 1282160 1%nat [Z_to_bv 8 128] ltac:(img_rd) eq_refl)
(DSC 1282160 8%nat (word_to_le_bytes 8 (Z_to_bv 64 128)) ltac:(img_rd) eq_refl) (DSC 1282200 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1282208 8%nat (word_to_le_bytes 8 (Z_to_bv 64 144640)) ltac:(img_rd) eq_refl) (DSC 1282224 1%nat [Z_to_bv 8 128] ltac:(img_rd) eq_refl) (DSC 1282224 8%nat (word_to_le_bytes 8 (Z_to_bv 64 128)) ltac:(img_rd) eq_refl) (DSC 1282264 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl)
(DSC 1282272 8%nat (word_to_le_bytes 8 (Z_to_bv 64 144768)) ltac:(img_rd) eq_refl) (DSC 1282288 1%nat [Z_to_bv 8 32] ltac:(img_rd) eq_refl) (DSC 1282288 8%nat (word_to_le_bytes 8 (Z_to_bv 64 32)) ltac:(img_rd) eq_refl) (DSC 1282328 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1282336 8%nat (word_to_le_bytes 8 (Z_to_bv 64 144800)) ltac:(img_rd) eq_refl) (DSC 1282352 1%nat [Z_to_bv 8 96] ltac:(img_rd) eq_refl)
(DSC 1282352 8%nat (word_to_le_bytes 8 (Z_to_bv 64 96)) ltac:(img_rd) eq_refl) (DSC 1282392 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1282400 8%nat (word_to_le_bytes 8 (Z_to_bv 64 144896)) ltac:(img_rd) eq_refl) (DSC 1282416 1%nat [Z_to_bv 8 128] ltac:(img_rd) eq_refl) (DSC 1282416 8%nat (word_to_le_bytes 8 (Z_to_bv 64 128)) ltac:(img_rd) eq_refl) (DSC 1282456 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl)
(DSC 1282464 8%nat (word_to_le_bytes 8 (Z_to_bv 64 145024)) ltac:(img_rd) eq_refl) (DSC 1282480 1%nat [Z_to_bv 8 128] ltac:(img_rd) eq_refl) (DSC 1282480 8%nat (word_to_le_bytes 8 (Z_to_bv 64 128)) ltac:(img_rd) eq_refl) (DSC 1282520 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1282528 8%nat (word_to_le_bytes 8 (Z_to_bv 64 145152)) ltac:(img_rd) eq_refl) (DSC 1282544 1%nat [Z_to_bv 8 96] ltac:(img_rd) eq_refl)
(DSC 1282544 8%nat (word_to_le_bytes 8 (Z_to_bv 64 96)) ltac:(img_rd) eq_refl) (DSC 1282584 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1282592 8%nat (word_to_le_bytes 8 (Z_to_bv 64 145248)) ltac:(img_rd) eq_refl) (DSC 1282608 1%nat [Z_to_bv 8 96] ltac:(img_rd) eq_refl) (DSC 1282608 8%nat (word_to_le_bytes 8 (Z_to_bv 64 96)) ltac:(img_rd) eq_refl) (DSC 1282648 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl)
(DSC 1282656 8%nat (word_to_le_bytes 8 (Z_to_bv 64 145344)) ltac:(img_rd) eq_refl) (DSC 1282672 1%nat [Z_to_bv 8 96] ltac:(img_rd) eq_refl) (DSC 1282672 8%nat (word_to_le_bytes 8 (Z_to_bv 64 96)) ltac:(img_rd) eq_refl) (DSC 1282712 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1282720 8%nat (word_to_le_bytes 8 (Z_to_bv 64 145440)) ltac:(img_rd) eq_refl) (DSC 1282736 1%nat [Z_to_bv 8 128] ltac:(img_rd) eq_refl)
(DSC 1282736 8%nat (word_to_le_bytes 8 (Z_to_bv 64 128)) ltac:(img_rd) eq_refl) (DSC 1282776 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1282784 8%nat (word_to_le_bytes 8 (Z_to_bv 64 145568)) ltac:(img_rd) eq_refl) (DSC 1282800 1%nat [Z_to_bv 8 64] ltac:(img_rd) eq_refl) (DSC 1282800 8%nat (word_to_le_bytes 8 (Z_to_bv 64 64)) ltac:(img_rd) eq_refl) (DSC 1282840 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl)
(DSC 1282848 8%nat (word_to_le_bytes 8 (Z_to_bv 64 145632)) ltac:(img_rd) eq_refl) (DSC 1282864 1%nat [Z_to_bv 8 96] ltac:(img_rd) eq_refl) (DSC 1282864 8%nat (word_to_le_bytes 8 (Z_to_bv 64 96)) ltac:(img_rd) eq_refl) (DSC 1282904 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (XCC 8%nat 6886088 8 0 eq_refl) (XCC 9%nat 1281648 8 1281416 eq_refl)
(XCC 10%nat 1281556 4 4294967295 eq_refl) (XCC 11%nat 1281456 8 0 eq_refl) (XCC 12%nat 1281472 8 0 eq_refl) (XCC 13%nat 1281424 8 0 eq_refl) (XCC 14%nat 1281432 8 0 eq_refl) (XCC 15%nat 1281408 8 1281176 eq_refl)
SOlock SOwpos SOwbase SOrpos SOrend (XCC 16%nat 1281168 8 1280936 eq_refl)
(XCC 17%nat 1281076 4 4294967295 eq_refl) (XCC 18%nat 1280976 8 0 eq_refl) (XCC 19%nat 1280992 8 0 eq_refl) (XCC 20%nat 1280944 8 0 eq_refl) (XCC 21%nat 1280952 8 0 eq_refl)) as
(fx1 & R1 & MV1 & XGR & _ & _ & XMS & XKS & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Xr17 & _).
unfold V in XMS; cbn beta iota in XMS.
pose proof (dinv_lzinv scfg L ar C IL HI HIok sp0 DL M0 _ _ _ _ _ _ D) as LZ. pose proof LZ as (_ & _ & _ & _ & Hh).
apply (msteps_vis_fx scfg (ahid A model) A fx fx1 R (Z_to_bv 64 0x11575c) M R1 (Z_to_bv 64 0x11546c) MV1 model _ LZ XMS).
intros M' model' MI' SBM' _.
rewrite <- (proj2 (sbm_fds model model' SBM')).
apply (rz_exit_at_lit_lz ASEGS scfg R1 (Z_to_bv 64 0x11546c) M' rom model' ECALLW st fetch_exitA is_ecall_ECALLW).
- rewrite (sbm_halted_eq _ _ SBM'). exact Hh.
- left. exact Xr17.
- eapply eq_trans; [exact (XKS 10%nat ltac:(unfold AS0DRVP_dpX.KS_dpX; cbn [In]; repeat first [left; reflexivity | right]))|]. exact G10.
- exact Hst.
Qed.
End SE.
Definition stdoutPA (MV : word -> option byte) : Prop :=
rdn ASEGS MV (Z_to_bv 64 1281316) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 4294967295))
/\ rdn ASEGS MV (Z_to_bv 64 1281216) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0))
/\ rdn ASEGS MV (Z_to_bv 64 1281232) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0))
/\ rdn ASEGS MV (Z_to_bv 64 1281184) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0))
/\ rdn ASEGS MV (Z_to_bv 64 1281192) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0)).
Section SE.
Local Abbreviation SEC_T_exit_run_e := (ltac2:(TCodec.tc2 tcn__Jb0DrvExit "S8'6'<'A%2211%411&Q?%611&Q='S9yR0%211'9y8%511%311p051'L&Q0y5%2219&Q@r:r9r8r7r6r5r3r1%9887654321&Q:&Q>%1297%3219'?&R=zr4%3221&R?+X0%2241%8241'@&QL(S7+2(>%33N21%52I1&S8%12Q:J%93Q:31+4%93Q417%;2Q01+V^Rf0%72Q@1%?3Q@31+:%?3Q:1=%A2Q71%<2QEQ6%D3QE21&QC%11Q7'R5&R8vS4(I&QMvRKr;+QRejL%H2R11r=&QO%11:%8576431r<%;221&R2%Q02R9QL&O%115%4231%D4CB61p0F1p0I1p0O1p0Q61p0QA1tR:R=QK1p0R01pVFRL1pV>RM1pTDRN1pR>R>1pV0RB1pR4RD1p2S01pUFRN1pQ<S01pQ:S31")) (only parsing).
Variable LB : ltac:(sec_ty2 constr:(SEC_T_exit_run_e) 0%nat 0%nat).
Variable LK : ltac:(sec_ty2 constr:(SEC_T_exit_run_e) 1%nat 0%nat).
Variable cr : ltac:(sec_ty2 constr:(SEC_T_exit_run_e) 2%nat 0%nat).
Variable A : ltac:(sec_ty2 constr:(SEC_T_exit_run_e) 3%nat 0%nat).
Variable M : ltac:(sec_ty2 constr:(SEC_T_exit_run_e) 4%nat 0%nat).
Variable model : ltac:(sec_ty2 constr:(SEC_T_exit_run_e) 5%nat 0%nat).
Variable R : ltac:(sec_ty2 constr:(SEC_T_exit_run_e) 6%nat 0%nat).
Variable S : ltac:(sec_ty2 constr:(SEC_T_exit_run_e) 7%nat 0%nat).
Variable st : ltac:(sec_ty2 constr:(SEC_T_exit_run_e) 8%nat 0%nat).
Variable tid : ltac:(sec_ty2 constr:(SEC_T_exit_run_e) 9%nat 0%nat).
Lemma exit_run_e : ltac:(sec_stmt2 constr:(SEC_T_exit_run_e) 10%nat 0%nat).
Proof using L C IL HIok ICok ILY Hsp DL Hex LB LK cr A M model R S st tid.
intros (D & HS1 & HS2 & HS16 & WIN & IMGc & (XC & TIDC & HTr & DESC)) MV Hst G2 G4 G10 SOP.
pose proof Hsp as Hsp'. destruct SOP as (SOlock & SOwpos & SOwbase & SOrpos & SOrend).
set (V := fun n : nat => match n with 2%nat => S | 44%nat => tid | _ => 0 end).
assert (HS64 : 0 <= V 2%nat < 2 ^ 64) by (cbn [V]; clear - Hsp' HS1 HS2; lia).
assert (HT64 : 0 <= V 44%nat < 2 ^ 64) by (cbn [V]; clear - HTr; lia).
assert (HSr : 140735332552704 <= V 2%nat <= 140737488355328) by (cbn [V]; clear - Hsp' HS1 HS2; lia).
assert (HSa : AS0DRVP_dpXe.aligned (V 2%nat) 16) by (cbn [V]; exact HS16).
assert (CWR : L5Defs.L5.writable ASEGS MV (V 2%nat - 320) 320).
{ cbn [V]. intros d k Hd Hk. apply (WIN (S - 320) 320); clear - Hsp' HS1 HS2 Hd Hk; lia. }
assert (CDF : L5Defs.L5.defined MV (V 2%nat - 320) 320).
{ cbn [V]. intros i Hi. apply (store_ok_defined sp0); [clear - Hsp' HS1 HS2 Hi; lia|]. apply (WIN (S - 320) 320); clear - Hsp' HS1 HS2 Hi; lia. }
assert (WSG : forall a (n : nat), wseg_ok ASEGS (Z_to_bv 64 a) n = true -> (0 <=? a) && (a + Z.of_nat n <=? 2 ^ 63) = true -> L5Defs.L5.writable ASEGS MV a (Z.of_nat n)).
{ intros a n W Hb. apply andb_prop in Hb as (B1 & B2). apply Z.leb_le in B1, B2. exact (wsg_writable MV a n W B1 B2). }
assert (SHW : forall a n, ((2147468844 <=? a) && (a + n <=? 2147469096) || (2147611092 <=? a) && (a + n <=? 2147611248)) = true -> L5Defs.L5.writable ASEGS MV a n)
by (intros a n Hb; exact (sh_writable _ _ _ _ _ _ a n D Hb)).
assert (STC : forall (i : nat) a n v, nth_error EX_CELLS i = Some (a, n, v) -> rdn ASEGS MV (Z_to_bv 64 a) (Z.to_nat n) = Some (word_to_le_bytes (Z.to_nat n) (Z_to_bv 64 v)))
by (intros i a n v Hn; exact (ex_cell_vis _ _ _ _ _ _ a n v D (nth_error_In _ _ Hn))).
assert (STC1 : forall (i : nat) a v, nth_error EX_CELLS i = Some (a, 1, v) -> (0 <=? v) && (v <? 2 ^ 64) = true -> rdn ASEGS MV (Z_to_bv 64 a) 1 = Some [Z_to_bv 8 v]).
{ intros i a v Hn Hb. apply andb_prop in Hb as (B1 & B2). apply Z.leb_le in B1. apply Z.ltb_lt in B2. rewrite <- (ArtMem.art_bytes1 v (conj B1 B2)). exact (STC i a 1 v Hn). }
assert (XCC : forall (i : nat) a n v, nth_error XC_CELLS i = Some (a, n, v) -> rdn ASEGS MV (Z_to_bv 64 a) (Z.to_nat n) = Some (word_to_le_bytes (Z.to_nat n) (Z_to_bv 64 v)))
by (intros i a n v Hn; exact (cells_at_nth MV XC_CELLS i a n v XC Hn)).
assert (XCC1 : forall (i : nat) a v, nth_error XC_CELLS i = Some (a, 1, v) -> (0 <=? v) && (v <? 2 ^ 64) = true -> rdn ASEGS MV (Z_to_bv 64 a) 1 = Some [Z_to_bv 8 v]).
{ intros i a v Hn Hb. apply andb_prop in Hb as (B1 & B2). apply Z.leb_le in B1. apply Z.ltb_lt in B2. rewrite <- (ArtMem.art_bytes1 v (conj B1 B2)). exact (XCC i a 1 v Hn). }
assert (DSC : forall a (n : nat) bs, rdn ASEGS (fun _ => None) (Z_to_bv 64 a) n = Some bs -> (0x138ea0 <=? a) && (a + Z.of_nat n <=? 0x139380) = true -> rdn ASEGS MV (Z_to_bv 64 a) n = Some bs).
{ intros a n bs Hr Hb. apply andb_prop in Hb as (B1 & B2). apply Z.leb_le in B1, B2. apply (img_cell MV a n bs Hr); [lia | lia|]. intros i Hi. apply DESC. lia. }
destruct (AS0DRVP_dpXe.dpXe_conc fx R MV V HS64 HT64
G2 G4 HSr HSa CWR CDF
IMGc (WSG 1282944 8%nat ltac:(vm_compute; reflexivity) eq_refl) (WSG 1283024 1%nat ltac:(vm_compute; reflexivity) eq_refl) (WSG 1286896 8%nat ltac:(vm_compute; reflexivity) eq_refl) (WSG 6884112 1%nat ltac:(vm_compute; reflexivity) eq_refl) (WSG 6884120 4%nat ltac:(vm_compute; reflexivity) eq_refl)
(WSG 6884128 8%nat ltac:(vm_compute; reflexivity) eq_refl) (WSG 6884656 4%nat ltac:(vm_compute; reflexivity) eq_refl) (SHW 2147468844 1 eq_refl) (SHW 2147468845 1 eq_refl) (SHW 2147468846 1 eq_refl) (SHW 2147468847 1 eq_refl)
(SHW 2147468856 1 eq_refl) (SHW 2147468857 1 eq_refl) (SHW 2147468858 1 eq_refl) (SHW 2147468859 1 eq_refl) (SHW 2147468860 1 eq_refl) (SHW 2147468860 4 eq_refl)
(SHW 2147468861 1 eq_refl) (SHW 2147468862 1 eq_refl) (SHW 2147468863 1 eq_refl) (SHW 2147468864 4 eq_refl) (SHW 2147468868 1 eq_refl) (SHW 2147468868 4 eq_refl)
(SHW 2147468869 1 eq_refl) (SHW 2147468870 1 eq_refl) (SHW 2147468871 1 eq_refl) (SHW 2147468916 1 eq_refl) (SHW 2147468917 1 eq_refl) (SHW 2147468918 1 eq_refl)
(SHW 2147468919 1 eq_refl) (SHW 2147468920 1 eq_refl) (SHW 2147468921 1 eq_refl) (SHW 2147468922 1 eq_refl) (SHW 2147468923 1 eq_refl) (SHW 2147468924 1 eq_refl)
(SHW 2147468925 1 eq_refl) (SHW 2147468926 1 eq_refl) (SHW 2147468927 1 eq_refl) (SHW 2147468928 1 eq_refl) (SHW 2147468929 1 eq_refl) (SHW 2147468930 1 eq_refl)
(SHW 2147468931 1 eq_refl) (SHW 2147468932 1 eq_refl) (SHW 2147468932 4 eq_refl) (SHW 2147468933 1 eq_refl) (SHW 2147468934 1 eq_refl) (SHW 2147468935 1 eq_refl)
(SHW 2147468936 4 eq_refl) (SHW 2147468940 1 eq_refl) (SHW 2147468940 4 eq_refl) (SHW 2147468941 1 eq_refl) (SHW 2147468942 1 eq_refl) (SHW 2147468943 1 eq_refl)
(SHW 2147468944 1 eq_refl) (SHW 2147468944 4 eq_refl) (SHW 2147468945 1 eq_refl) (SHW 2147468946 1 eq_refl) (SHW 2147468947 1 eq_refl) (SHW 2147468948 4 eq_refl)
(SHW 2147468952 4 eq_refl) (SHW 2147468956 1 eq_refl) (SHW 2147468956 4 eq_refl) (SHW 2147468957 1 eq_refl) (SHW 2147468958 1 eq_refl) (SHW 2147468959 1 eq_refl)
(SHW 2147468960 1 eq_refl) (SHW 2147468960 4 eq_refl) (SHW 2147468961 1 eq_refl) (SHW 2147468962 1 eq_refl) (SHW 2147468963 1 eq_refl) (SHW 2147468964 4 eq_refl)
(SHW 2147468968 4 eq_refl) (SHW 2147468972 1 eq_refl) (SHW 2147468972 4 eq_refl) (SHW 2147468973 1 eq_refl) (SHW 2147468974 1 eq_refl) (SHW 2147468975 1 eq_refl)
(SHW 2147468976 1 eq_refl) (SHW 2147468977 1 eq_refl) (SHW 2147468978 1 eq_refl) (SHW 2147468979 1 eq_refl) (SHW 2147468980 1 eq_refl) (SHW 2147468980 4 eq_refl)
(SHW 2147468981 1 eq_refl) (SHW 2147468982 1 eq_refl) (SHW 2147468983 1 eq_refl) (SHW 2147468984 4 eq_refl) (SHW 2147468988 1 eq_refl) (SHW 2147468988 4 eq_refl)
(SHW 2147468989 1 eq_refl) (SHW 2147468990 1 eq_refl) (SHW 2147468991 1 eq_refl) (SHW 2147468992 1 eq_refl) (SHW 2147468992 4 eq_refl) (SHW 2147468993 1 eq_refl)
(SHW 2147468994 1 eq_refl) (SHW 2147468995 1 eq_refl) (SHW 2147468996 4 eq_refl) (SHW 2147469000 4 eq_refl) (SHW 2147469004 1 eq_refl) (SHW 2147469004 4 eq_refl)
(SHW 2147469005 1 eq_refl) (SHW 2147469006 1 eq_refl) (SHW 2147469007 1 eq_refl) (SHW 2147469008 1 eq_refl) (SHW 2147469008 4 eq_refl) (SHW 2147469009 1 eq_refl)
(SHW 2147469010 1 eq_refl) (SHW 2147469011 1 eq_refl) (SHW 2147469012 4 eq_refl) (SHW 2147469016 4 eq_refl) (SHW 2147469020 1 eq_refl) (SHW 2147469020 4 eq_refl)
(SHW 2147469021 1 eq_refl) (SHW 2147469022 1 eq_refl) (SHW 2147469023 1 eq_refl) (SHW 2147469024 1 eq_refl) (SHW 2147469024 4 eq_refl) (SHW 2147469025 1 eq_refl)
(SHW 2147469026 1 eq_refl) (SHW 2147469027 1 eq_refl) (SHW 2147469028 4 eq_refl) (SHW 2147469032 1 eq_refl) (SHW 2147469032 4 eq_refl) (SHW 2147469033 1 eq_refl)
(SHW 2147469034 1 eq_refl) (SHW 2147469035 1 eq_refl) (SHW 2147469036 1 eq_refl) (SHW 2147469036 4 eq_refl) (SHW 2147469037 1 eq_refl) (SHW 2147469038 1 eq_refl)
(SHW 2147469039 1 eq_refl) (SHW 2147469040 4 eq_refl) (SHW 2147469044 1 eq_refl) (SHW 2147469044 4 eq_refl) (SHW 2147469045 1 eq_refl) (SHW 2147469046 1 eq_refl)
(SHW 2147469047 1 eq_refl) (SHW 2147469048 1 eq_refl) (SHW 2147469048 4 eq_refl) (SHW 2147469049 1 eq_refl) (SHW 2147469050 1 eq_refl) (SHW 2147469051 1 eq_refl)
(SHW 2147469052 4 eq_refl) (SHW 2147469056 1 eq_refl) (SHW 2147469056 4 eq_refl) (SHW 2147469057 1 eq_refl) (SHW 2147469058 1 eq_refl) (SHW 2147469059 1 eq_refl)
(SHW 2147469060 1 eq_refl) (SHW 2147469060 4 eq_refl) (SHW 2147469061 1 eq_refl) (SHW 2147469062 1 eq_refl) (SHW 2147469063 1 eq_refl) (SHW 2147469064 4 eq_refl)
(SHW 2147469068 4 eq_refl) (SHW 2147469072 1 eq_refl) (SHW 2147469072 4 eq_refl) (SHW 2147469073 1 eq_refl) (SHW 2147469074 1 eq_refl) (SHW 2147469075 1 eq_refl)
(SHW 2147469076 1 eq_refl) (SHW 2147469077 1 eq_refl) (SHW 2147469078 1 eq_refl) (SHW 2147469079 1 eq_refl) (SHW 2147469080 1 eq_refl) (SHW 2147469081 1 eq_refl)
(SHW 2147469082 1 eq_refl) (SHW 2147469083 1 eq_refl) (SHW 2147469084 1 eq_refl) (SHW 2147469084 4 eq_refl) (SHW 2147469085 1 eq_refl) (SHW 2147469086 1 eq_refl)
(SHW 2147469087 1 eq_refl) (SHW 2147469088 4 eq_refl) (SHW 2147469092 1 eq_refl) (SHW 2147469092 4 eq_refl) (SHW 2147469093 1 eq_refl) (SHW 2147469094 1 eq_refl)
(SHW 2147469095 1 eq_refl) (SHW 2147611092 1 eq_refl) (SHW 2147611092 4 eq_refl) (SHW 2147611093 1 eq_refl) (SHW 2147611094 1 eq_refl) (SHW 2147611095 1 eq_refl)
(SHW 2147611096 4 eq_refl) (SHW 2147611100 4 eq_refl) (SHW 2147611104 4 eq_refl) (SHW 2147611108 4 eq_refl) (SHW 2147611112 4 eq_refl) (SHW 2147611116 4 eq_refl)
(SHW 2147611120 8 eq_refl) (SHW 2147611128 8 eq_refl) (SHW 2147611136 8 eq_refl) (SHW 2147611144 8 eq_refl) (SHW 2147611152 8 eq_refl) (SHW 2147611160 8 eq_refl)
(SHW 2147611168 8 eq_refl) (SHW 2147611176 8 eq_refl) (SHW 2147611184 8 eq_refl) (SHW 2147611192 8 eq_refl) (SHW 2147611200 8 eq_refl) (SHW 2147611208 8 eq_refl)
(SHW 2147611216 4 eq_refl) (SHW 2147611220 4 eq_refl) (SHW 2147611224 4 eq_refl) (SHW 2147611228 4 eq_refl) (SHW 2147611232 4 eq_refl) (SHW 2147611236 4 eq_refl)
(SHW 2147611240 1 eq_refl) (SHW 2147611240 4 eq_refl) (SHW 2147611241 1 eq_refl) (SHW 2147611242 1 eq_refl) (SHW 2147611243 1 eq_refl) TIDC
HTr (XCC 0%nat 6884656 4 0 eq_refl) (XCC1 1%nat 6884691 0 eq_refl eq_refl) (XCC 2%nat 6884128 8 6884136 eq_refl) (XCC 3%nat 6884120 4 1 eq_refl) (XCC 4%nat 6884144 8 1136392 eq_refl)
(XCC 5%nat 6884400 8 618204 eq_refl) (XCC 6%nat 6884116 4 0 eq_refl) (STC1 10%nat 1894624 0 eq_refl eq_refl) (XCC 7%nat 6884136 8 0 eq_refl) (STC1 3%nat 1283024 0 eq_refl eq_refl) (STC 0%nat 1270192 8 1270192 eq_refl)
(STC 2%nat 1282944 8 1 eq_refl) (STC 4%nat 1286736 4 1 eq_refl) (STC 5%nat 1286896 8 0 eq_refl) (STC1 8%nat 1300248 1 eq_refl eq_refl) (STC 7%nat 1296952 8 2147450880 eq_refl) (DSC 1281696 8%nat (word_to_le_bytes 8 (Z_to_bv 64 143712)) ltac:(img_rd) eq_refl)
(DSC 1281712 1%nat [Z_to_bv 8 32] ltac:(img_rd) eq_refl) (STC1 6%nat 1295004 1 eq_refl eq_refl) (DSC 1281712 8%nat (word_to_le_bytes 8 (Z_to_bv 64 32)) ltac:(img_rd) eq_refl) (STC 9%nat 1893856 8 18446744073709551615 eq_refl) (STC 1%nat 1270704 8 1207272 eq_refl) (DSC 1281752 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl)
(DSC 1281760 8%nat (word_to_le_bytes 8 (Z_to_bv 64 143808)) ltac:(img_rd) eq_refl) (DSC 1281776 1%nat [Z_to_bv 8 32] ltac:(img_rd) eq_refl) (DSC 1281776 8%nat (word_to_le_bytes 8 (Z_to_bv 64 32)) ltac:(img_rd) eq_refl) (DSC 1281816 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1281824 8%nat (word_to_le_bytes 8 (Z_to_bv 64 143840)) ltac:(img_rd) eq_refl) (DSC 1281840 1%nat [Z_to_bv 8 96] ltac:(img_rd) eq_refl)
(DSC 1281840 8%nat (word_to_le_bytes 8 (Z_to_bv 64 96)) ltac:(img_rd) eq_refl) (DSC 1281880 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1281888 8%nat (word_to_le_bytes 8 (Z_to_bv 64 144288)) ltac:(img_rd) eq_refl) (DSC 1281904 1%nat [Z_to_bv 8 32] ltac:(img_rd) eq_refl) (DSC 1281904 8%nat (word_to_le_bytes 8 (Z_to_bv 64 32)) ltac:(img_rd) eq_refl) (DSC 1281944 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl)
(DSC 1281952 8%nat (word_to_le_bytes 8 (Z_to_bv 64 144320)) ltac:(img_rd) eq_refl) (DSC 1281968 1%nat [Z_to_bv 8 64] ltac:(img_rd) eq_refl) (DSC 1281968 8%nat (word_to_le_bytes 8 (Z_to_bv 64 64)) ltac:(img_rd) eq_refl) (DSC 1282008 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1282016 8%nat (word_to_le_bytes 8 (Z_to_bv 64 144384)) ltac:(img_rd) eq_refl) (DSC 1282032 1%nat [Z_to_bv 8 32] ltac:(img_rd) eq_refl)
(DSC 1282032 8%nat (word_to_le_bytes 8 (Z_to_bv 64 32)) ltac:(img_rd) eq_refl) (DSC 1282072 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1282080 8%nat (word_to_le_bytes 8 (Z_to_bv 64 144416)) ltac:(img_rd) eq_refl) (DSC 1282096 1%nat [Z_to_bv 8 96] ltac:(img_rd) eq_refl) (DSC 1282096 8%nat (word_to_le_bytes 8 (Z_to_bv 64 96)) ltac:(img_rd) eq_refl) (DSC 1282136 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl)
(DSC 1282144 8%nat (word_to_le_bytes 8 (Z_to_bv 64 144512)) ltac:(img_rd) eq_refl) (DSC 1282160 1%nat [Z_to_bv 8 128] ltac:(img_rd) eq_refl) (DSC 1282160 8%nat (word_to_le_bytes 8 (Z_to_bv 64 128)) ltac:(img_rd) eq_refl) (DSC 1282200 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1282208 8%nat (word_to_le_bytes 8 (Z_to_bv 64 144640)) ltac:(img_rd) eq_refl) (DSC 1282224 1%nat [Z_to_bv 8 128] ltac:(img_rd) eq_refl)
(DSC 1282224 8%nat (word_to_le_bytes 8 (Z_to_bv 64 128)) ltac:(img_rd) eq_refl) (DSC 1282264 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1282272 8%nat (word_to_le_bytes 8 (Z_to_bv 64 144768)) ltac:(img_rd) eq_refl) (DSC 1282288 1%nat [Z_to_bv 8 32] ltac:(img_rd) eq_refl) (DSC 1282288 8%nat (word_to_le_bytes 8 (Z_to_bv 64 32)) ltac:(img_rd) eq_refl) (DSC 1282328 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl)
(DSC 1282336 8%nat (word_to_le_bytes 8 (Z_to_bv 64 144800)) ltac:(img_rd) eq_refl) (DSC 1282352 1%nat [Z_to_bv 8 96] ltac:(img_rd) eq_refl) (DSC 1282352 8%nat (word_to_le_bytes 8 (Z_to_bv 64 96)) ltac:(img_rd) eq_refl) (DSC 1282392 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1282400 8%nat (word_to_le_bytes 8 (Z_to_bv 64 144896)) ltac:(img_rd) eq_refl) (DSC 1282416 1%nat [Z_to_bv 8 128] ltac:(img_rd) eq_refl)
(DSC 1282416 8%nat (word_to_le_bytes 8 (Z_to_bv 64 128)) ltac:(img_rd) eq_refl) (DSC 1282456 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1282464 8%nat (word_to_le_bytes 8 (Z_to_bv 64 145024)) ltac:(img_rd) eq_refl) (DSC 1282480 1%nat [Z_to_bv 8 128] ltac:(img_rd) eq_refl) (DSC 1282480 8%nat (word_to_le_bytes 8 (Z_to_bv 64 128)) ltac:(img_rd) eq_refl) (DSC 1282520 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl)
(DSC 1282528 8%nat (word_to_le_bytes 8 (Z_to_bv 64 145152)) ltac:(img_rd) eq_refl) (DSC 1282544 1%nat [Z_to_bv 8 96] ltac:(img_rd) eq_refl) (DSC 1282544 8%nat (word_to_le_bytes 8 (Z_to_bv 64 96)) ltac:(img_rd) eq_refl) (DSC 1282584 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1282592 8%nat (word_to_le_bytes 8 (Z_to_bv 64 145248)) ltac:(img_rd) eq_refl) (DSC 1282608 1%nat [Z_to_bv 8 96] ltac:(img_rd) eq_refl)
(DSC 1282608 8%nat (word_to_le_bytes 8 (Z_to_bv 64 96)) ltac:(img_rd) eq_refl) (DSC 1282648 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1282656 8%nat (word_to_le_bytes 8 (Z_to_bv 64 145344)) ltac:(img_rd) eq_refl) (DSC 1282672 1%nat [Z_to_bv 8 96] ltac:(img_rd) eq_refl) (DSC 1282672 8%nat (word_to_le_bytes 8 (Z_to_bv 64 96)) ltac:(img_rd) eq_refl) (DSC 1282712 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl)
(DSC 1282720 8%nat (word_to_le_bytes 8 (Z_to_bv 64 145440)) ltac:(img_rd) eq_refl) (DSC 1282736 1%nat [Z_to_bv 8 128] ltac:(img_rd) eq_refl) (DSC 1282736 8%nat (word_to_le_bytes 8 (Z_to_bv 64 128)) ltac:(img_rd) eq_refl) (DSC 1282776 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1282784 8%nat (word_to_le_bytes 8 (Z_to_bv 64 145568)) ltac:(img_rd) eq_refl) (DSC 1282800 1%nat [Z_to_bv 8 64] ltac:(img_rd) eq_refl)
(DSC 1282800 8%nat (word_to_le_bytes 8 (Z_to_bv 64 64)) ltac:(img_rd) eq_refl) (DSC 1282840 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1282848 8%nat (word_to_le_bytes 8 (Z_to_bv 64 145632)) ltac:(img_rd) eq_refl) (DSC 1282864 1%nat [Z_to_bv 8 96] ltac:(img_rd) eq_refl) (DSC 1282864 8%nat (word_to_le_bytes 8 (Z_to_bv 64 96)) ltac:(img_rd) eq_refl) (DSC 1282904 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl)
(XCC 8%nat 6886088 8 0 eq_refl) (XCC 9%nat 1281648 8 1281416 eq_refl) (XCC 10%nat 1281556 4 4294967295 eq_refl) (XCC 11%nat 1281456 8 0 eq_refl) (XCC 12%nat 1281472 8 0 eq_refl) (XCC 13%nat 1281424 8 0 eq_refl)
(XCC 14%nat 1281432 8 0 eq_refl) (XCC 15%nat 1281408 8 1281176 eq_refl) SOlock SOwpos SOwbase SOrpos
SOrend (XCC 16%nat 1281168 8 1280936 eq_refl) (XCC 17%nat 1281076 4 4294967295 eq_refl) (XCC 18%nat 1280976 8 0 eq_refl) (XCC 19%nat 1280992 8 0 eq_refl) (XCC 20%nat 1280944 8 0 eq_refl)
(XCC 21%nat 1280952 8 0 eq_refl)) as
(fx1 & R1 & MV1 & XGR & _ & _ & XMS & XKS & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Xr17 & _).
unfold V in XMS; cbn beta iota in XMS.
pose proof (dinv_lzinv scfg L ar C IL HI HIok sp0 DL M0 _ _ _ _ _ _ D) as LZ. pose proof LZ as (_ & _ & _ & _ & Hh).
apply (msteps_vis_fx scfg (ahid A model) A fx fx1 R (Z_to_bv 64 0x11575c) M R1 (Z_to_bv 64 0x11546c) MV1 model _ LZ XMS).
intros M' model' MI' SBM' _.
rewrite <- (proj2 (sbm_fds model model' SBM')).
apply (rz_exit_at_lit_lz ASEGS scfg R1 (Z_to_bv 64 0x11546c) M' rom model' ECALLW st fetch_exitA is_ecall_ECALLW).
- rewrite (sbm_halted_eq _ _ SBM'). exact Hh.
- left. exact Xr17.
- eapply eq_trans; [exact (XKS 10%nat ltac:(unfold AS0DRVP_dpXe.KS_dpXe; cbn [In]; repeat first [left; reflexivity | right]))|]. exact G10.
- exact Hst.
Qed.
End SE.
Section SE.
Local Abbreviation SEC_T_exit_run_2 := (ltac2:(TCodec.tc2 tcn__Jb0DrvExit "TL'6'<'A%2211%411&Q?%611&Q='S9yR0%211'9y8%511%311p051'L&Q0y5%2219&QBr;r:r9r8r7r6r4r2%9887654321&Q:&Q>%1297%3219'?&R=zr5%3221&R?+X0%2241%8241%827@&RA+2+R0%3221%92E1%?261'@&QL(S7+1(>%33Q521%52Q11&S8+QRclH%22QB1%:3QB41%93Q;@7%;2Q81%62QFQ8%>3QF21+4%>3Q@1<%@2Q>1+V^Rf0%<2QL1%D3QL31r<+:%E3QG1C%G231%B2R2QE%J3R221%R=1R0%R311&QN&R8+VbRh0%I2R91u8%544QK21(2&G%124H%32;1%Q73;51&QG%12Q6R3&QF%11R6'K%RD11&M&NrA%211%Q;2RKQ?%5221(J%113%C2:1%QG3:41'R5vS4(I&QMvRK+QRejL%QG2S71rC&QO%11Q3%756B431rB%:221&R1&R3&R4u1%211%42R71&R2r?%R62SF1&O%11<%5231%<271%J4QDI>1p0L1p0Q91p0Q<1p0Q?1p0QM1p0R41p0R;1p0R@1p0RL1p0S41tR:T0S>1p0SC1pUDT?1pVFT@1pV>TA1pTDTB1pR>T21pV0T61pR4T81p2TD1pUFTB1pQ<TD1pQ:TG1")) (only parsing).
Variable LB : ltac:(sec_ty2 constr:(SEC_T_exit_run_2) 0%nat 0%nat).
Variable LK : ltac:(sec_ty2 constr:(SEC_T_exit_run_2) 1%nat 0%nat).
Variable cr : ltac:(sec_ty2 constr:(SEC_T_exit_run_2) 2%nat 0%nat).
Variable A : ltac:(sec_ty2 constr:(SEC_T_exit_run_2) 3%nat 0%nat).
Variable M : ltac:(sec_ty2 constr:(SEC_T_exit_run_2) 4%nat 0%nat).
Variable model : ltac:(sec_ty2 constr:(SEC_T_exit_run_2) 5%nat 0%nat).
Variable R : ltac:(sec_ty2 constr:(SEC_T_exit_run_2) 6%nat 0%nat).
Variable S : ltac:(sec_ty2 constr:(SEC_T_exit_run_2) 7%nat 0%nat).
Variable st : ltac:(sec_ty2 constr:(SEC_T_exit_run_2) 8%nat 0%nat).
Variable tid : ltac:(sec_ty2 constr:(SEC_T_exit_run_2) 9%nat 0%nat).
Variable canz : ltac:(sec_ty2 constr:(SEC_T_exit_run_2) 10%nat 0%nat).
Lemma exit_run_2 : ltac:(sec_stmt2 constr:(SEC_T_exit_run_2) 11%nat 0%nat).
Proof using L C IL HIok ICok ILY Hsp DL Hex LB LK cr A M model R S st tid canz.
intros (D & HS1 & HS2 & HS16 & WIN & IMGc & (XC & TIDC & HTr & DESC)) MV Hst Hcan G1 G2 G4 G10 CANc SO SOX FD1.
pose proof Hsp as Hsp'. destruct SO as (_ & SObufsz & _ & SOwpos & SOwbase & SOlock & _ & FW & BW & BC). destruct SOX as (SOwrite & SOfd & SObuf & SOrpos & SOrend).
set (V := fun n : nat => match n with 2%nat => S | 44%nat => tid | 40%nat => canz | _ => 0 end).
assert (HS64 : 0 <= V 2%nat < 2 ^ 64) by (cbn [V]; clear - Hsp' HS1 HS2; lia).
assert (HT64 : 0 <= V 44%nat < 2 ^ 64) by (cbn [V]; clear - HTr; lia).
assert (HSr : 140735332552704 <= V 2%nat <= 140737488355328) by (cbn [V]; clear - Hsp' HS1 HS2; lia).
assert (HSa : AS0DRVP_dpX2_pre.aligned (V 2%nat) 16) by (cbn [V]; exact HS16).
assert (CWR : L5Defs.L5.writable ASEGS MV (V 2%nat - 320) 320).
{ cbn [V]. intros d k Hd Hk. apply (WIN (S - 320) 320); clear - Hsp' HS1 HS2 Hd Hk; lia. }
assert (CDF : L5Defs.L5.defined MV (V 2%nat - 320) 320).
{ cbn [V]. intros i Hi. apply (store_ok_defined sp0); [clear - Hsp' HS1 HS2 Hi; lia|]. apply (WIN (S - 320) 320); clear - Hsp' HS1 HS2 Hi; lia. }
assert (WSG : forall a (n : nat), wseg_ok ASEGS (Z_to_bv 64 a) n = true -> (0 <=? a) && (a + Z.of_nat n <=? 2 ^ 63) = true -> L5Defs.L5.writable ASEGS MV a (Z.of_nat n)).
{ intros a n W Hb. apply andb_prop in Hb as (B1 & B2). apply Z.leb_le in B1, B2. exact (wsg_writable MV a n W B1 B2). }
assert (SHW : forall a n, ((2147468844 <=? a) && (a + n <=? 2147469096) || (2147611092 <=? a) && (a + n <=? 2147611248)) = true -> L5Defs.L5.writable ASEGS MV a n)
by (intros a n Hb; exact (sh_writable _ _ _ _ _ _ a n D Hb)).
assert (STC : forall (i : nat) a n v, nth_error EX_CELLS i = Some (a, n, v) -> rdn ASEGS MV (Z_to_bv 64 a) (Z.to_nat n) = Some (word_to_le_bytes (Z.to_nat n) (Z_to_bv 64 v)))
by (intros i a n v Hn; exact (ex_cell_vis _ _ _ _ _ _ a n v D (nth_error_In _ _ Hn))).
assert (STC1 : forall (i : nat) a v, nth_error EX_CELLS i = Some (a, 1, v) -> (0 <=? v) && (v <? 2 ^ 64) = true -> rdn ASEGS MV (Z_to_bv 64 a) 1 = Some [Z_to_bv 8 v]).
{ intros i a v Hn Hb. apply andb_prop in Hb as (B1 & B2). apply Z.leb_le in B1. apply Z.ltb_lt in B2. rewrite <- (ArtMem.art_bytes1 v (conj B1 B2)). exact (STC i a 1 v Hn). }
assert (XCC : forall (i : nat) a n v, nth_error XC_CELLS_T i = Some (a, n, v) -> rdn ASEGS MV (Z_to_bv 64 a) (Z.to_nat n) = Some (word_to_le_bytes (Z.to_nat n) (Z_to_bv 64 v)))
by (intros i a n v Hn; exact (cells_at_nth MV XC_CELLS_T i a n v XC Hn)).
assert (XCC1 : forall (i : nat) a v, nth_error XC_CELLS_T i = Some (a, 1, v) -> (0 <=? v) && (v <? 2 ^ 64) = true -> rdn ASEGS MV (Z_to_bv 64 a) 1 = Some [Z_to_bv 8 v]).
{ intros i a v Hn Hb. apply andb_prop in Hb as (B1 & B2). apply Z.leb_le in B1. apply Z.ltb_lt in B2. rewrite <- (ArtMem.art_bytes1 v (conj B1 B2)). exact (XCC i a 1 v Hn). }
assert (DSC : forall a (n : nat) bs, rdn ASEGS (fun _ => None) (Z_to_bv 64 a) n = Some bs -> (0x138ea0 <=? a) && (a + Z.of_nat n <=? 0x139380) = true -> rdn ASEGS MV (Z_to_bv 64 a) n = Some bs).
{ intros a n bs Hr Hb. apply andb_prop in Hb as (B1 & B2). apply Z.leb_le in B1, B2. apply (img_cell MV a n bs Hr); [lia | lia|]. intros i Hi. apply DESC. lia. }
destruct (AS0DRVP_dpX2_pre.dpX2_pre_conc fx R MV V HS64 Hcan
HT64 G1 G2 G4 HSr HSa
CWR CDF IMGc (WSG 1282944 8%nat ltac:(vm_compute; reflexivity) eq_refl) (WSG 1283024 1%nat ltac:(vm_compute; reflexivity) eq_refl) (WSG 1286896 8%nat ltac:(vm_compute; reflexivity) eq_refl)
(WSG 6884112 1%nat ltac:(vm_compute; reflexivity) eq_refl) (WSG 6884120 4%nat ltac:(vm_compute; reflexivity) eq_refl) (WSG 6884128 8%nat ltac:(vm_compute; reflexivity) eq_refl) (WSG 6884656 4%nat ltac:(vm_compute; reflexivity) eq_refl) (SHW 2147468844 1 eq_refl) (SHW 2147468845 1 eq_refl)
(SHW 2147468846 1 eq_refl) (SHW 2147468847 1 eq_refl) (SHW 2147468856 1 eq_refl) (SHW 2147468857 1 eq_refl) (SHW 2147468858 1 eq_refl) (SHW 2147468859 1 eq_refl)
(SHW 2147468860 1 eq_refl) (SHW 2147468860 4 eq_refl) (SHW 2147468861 1 eq_refl) (SHW 2147468862 1 eq_refl) (SHW 2147468863 1 eq_refl) (SHW 2147468864 4 eq_refl)
(SHW 2147468868 1 eq_refl) (SHW 2147468868 4 eq_refl) (SHW 2147468869 1 eq_refl) (SHW 2147468870 1 eq_refl) (SHW 2147468871 1 eq_refl) (SHW 2147468916 1 eq_refl)
(SHW 2147468917 1 eq_refl) (SHW 2147468918 1 eq_refl) (SHW 2147468919 1 eq_refl) (SHW 2147468920 1 eq_refl) (SHW 2147468921 1 eq_refl) (SHW 2147468922 1 eq_refl)
(SHW 2147468923 1 eq_refl) (SHW 2147468924 1 eq_refl) (SHW 2147468925 1 eq_refl) (SHW 2147468926 1 eq_refl) (SHW 2147468927 1 eq_refl) (SHW 2147468928 1 eq_refl)
(SHW 2147468929 1 eq_refl) (SHW 2147468930 1 eq_refl) (SHW 2147468931 1 eq_refl) (SHW 2147468932 1 eq_refl) (SHW 2147468932 4 eq_refl) (SHW 2147468933 1 eq_refl)
(SHW 2147468934 1 eq_refl) (SHW 2147468935 1 eq_refl) (SHW 2147468936 4 eq_refl) (SHW 2147468940 1 eq_refl) (SHW 2147468940 4 eq_refl) (SHW 2147468941 1 eq_refl)
(SHW 2147468942 1 eq_refl) (SHW 2147468943 1 eq_refl) (SHW 2147468944 1 eq_refl) (SHW 2147468944 4 eq_refl) (SHW 2147468945 1 eq_refl) (SHW 2147468946 1 eq_refl)
(SHW 2147468947 1 eq_refl) (SHW 2147468948 4 eq_refl) (SHW 2147468952 4 eq_refl) (SHW 2147468956 1 eq_refl) (SHW 2147468956 4 eq_refl) (SHW 2147468957 1 eq_refl)
(SHW 2147468958 1 eq_refl) (SHW 2147468959 1 eq_refl) (SHW 2147468960 1 eq_refl) (SHW 2147468960 4 eq_refl) (SHW 2147468961 1 eq_refl) (SHW 2147468962 1 eq_refl)
(SHW 2147468963 1 eq_refl) (SHW 2147468964 4 eq_refl) (SHW 2147468968 4 eq_refl) (SHW 2147468972 1 eq_refl) (SHW 2147468972 4 eq_refl) (SHW 2147468973 1 eq_refl)
(SHW 2147468974 1 eq_refl) (SHW 2147468975 1 eq_refl) (SHW 2147468976 1 eq_refl) (SHW 2147468977 1 eq_refl) (SHW 2147468978 1 eq_refl) (SHW 2147468979 1 eq_refl)
(SHW 2147468980 1 eq_refl) (SHW 2147468980 4 eq_refl) (SHW 2147468981 1 eq_refl) (SHW 2147468982 1 eq_refl) (SHW 2147468983 1 eq_refl) (SHW 2147468984 4 eq_refl)
(SHW 2147468988 1 eq_refl) (SHW 2147468988 4 eq_refl) (SHW 2147468989 1 eq_refl) (SHW 2147468990 1 eq_refl) (SHW 2147468991 1 eq_refl) (SHW 2147468992 1 eq_refl)
(SHW 2147468992 4 eq_refl) (SHW 2147468993 1 eq_refl) (SHW 2147468994 1 eq_refl) (SHW 2147468995 1 eq_refl) (SHW 2147468996 4 eq_refl) (SHW 2147469000 4 eq_refl)
(SHW 2147469004 1 eq_refl) (SHW 2147469004 4 eq_refl) (SHW 2147469005 1 eq_refl) (SHW 2147469006 1 eq_refl) (SHW 2147469007 1 eq_refl) (SHW 2147469008 1 eq_refl)
(SHW 2147469008 4 eq_refl) (SHW 2147469009 1 eq_refl) (SHW 2147469010 1 eq_refl) (SHW 2147469011 1 eq_refl) (SHW 2147469012 4 eq_refl) (SHW 2147469016 4 eq_refl)
(SHW 2147469020 1 eq_refl) (SHW 2147469020 4 eq_refl) (SHW 2147469021 1 eq_refl) (SHW 2147469022 1 eq_refl) (SHW 2147469023 1 eq_refl) (SHW 2147469024 1 eq_refl)
(SHW 2147469024 4 eq_refl) (SHW 2147469025 1 eq_refl) (SHW 2147469026 1 eq_refl) (SHW 2147469027 1 eq_refl) (SHW 2147469028 4 eq_refl) (SHW 2147469032 1 eq_refl)
(SHW 2147469032 4 eq_refl) (SHW 2147469033 1 eq_refl) (SHW 2147469034 1 eq_refl) (SHW 2147469035 1 eq_refl) (SHW 2147469036 1 eq_refl) (SHW 2147469036 4 eq_refl)
(SHW 2147469037 1 eq_refl) (SHW 2147469038 1 eq_refl) (SHW 2147469039 1 eq_refl) (SHW 2147469040 4 eq_refl) (SHW 2147469044 1 eq_refl) (SHW 2147469044 4 eq_refl)
(SHW 2147469045 1 eq_refl) (SHW 2147469046 1 eq_refl) (SHW 2147469047 1 eq_refl) (SHW 2147469048 1 eq_refl) (SHW 2147469048 4 eq_refl) (SHW 2147469049 1 eq_refl)
(SHW 2147469050 1 eq_refl) (SHW 2147469051 1 eq_refl) (SHW 2147469052 4 eq_refl) (SHW 2147469056 1 eq_refl) (SHW 2147469056 4 eq_refl) (SHW 2147469057 1 eq_refl)
(SHW 2147469058 1 eq_refl) (SHW 2147469059 1 eq_refl) (SHW 2147469060 1 eq_refl) (SHW 2147469060 4 eq_refl) (SHW 2147469061 1 eq_refl) (SHW 2147469062 1 eq_refl)
(SHW 2147469063 1 eq_refl) (SHW 2147469064 4 eq_refl) (SHW 2147469068 4 eq_refl) (SHW 2147469072 1 eq_refl) (SHW 2147469072 4 eq_refl) (SHW 2147469073 1 eq_refl)
(SHW 2147469074 1 eq_refl) (SHW 2147469075 1 eq_refl) (SHW 2147469076 1 eq_refl) (SHW 2147469077 1 eq_refl) (SHW 2147469078 1 eq_refl) (SHW 2147469079 1 eq_refl)
(SHW 2147469080 1 eq_refl) (SHW 2147469081 1 eq_refl) (SHW 2147469082 1 eq_refl) (SHW 2147469083 1 eq_refl) (SHW 2147469084 1 eq_refl) (SHW 2147469084 4 eq_refl)
(SHW 2147469085 1 eq_refl) (SHW 2147469086 1 eq_refl) (SHW 2147469087 1 eq_refl) (SHW 2147469088 4 eq_refl) (SHW 2147469092 1 eq_refl) (SHW 2147469092 4 eq_refl)
(SHW 2147469093 1 eq_refl) (SHW 2147469094 1 eq_refl) (SHW 2147469095 1 eq_refl) (SHW 2147611092 1 eq_refl) (SHW 2147611092 4 eq_refl) (SHW 2147611093 1 eq_refl)
(SHW 2147611094 1 eq_refl) (SHW 2147611095 1 eq_refl) (SHW 2147611096 4 eq_refl) (SHW 2147611100 4 eq_refl) (SHW 2147611104 4 eq_refl) (SHW 2147611108 4 eq_refl)
(SHW 2147611112 4 eq_refl) (SHW 2147611116 4 eq_refl) (SHW 2147611120 8 eq_refl) (SHW 2147611128 8 eq_refl) (SHW 2147611136 8 eq_refl) (SHW 2147611144 8 eq_refl)
(SHW 2147611152 8 eq_refl) (SHW 2147611160 8 eq_refl) (SHW 2147611168 8 eq_refl) (SHW 2147611176 8 eq_refl) (SHW 2147611184 8 eq_refl) (SHW 2147611192 8 eq_refl)
(SHW 2147611200 8 eq_refl) (SHW 2147611208 8 eq_refl) (SHW 2147611216 4 eq_refl) (SHW 2147611220 4 eq_refl) (SHW 2147611224 4 eq_refl) (SHW 2147611228 4 eq_refl)
(SHW 2147611232 4 eq_refl) (SHW 2147611236 4 eq_refl) (SHW 2147611240 1 eq_refl) (SHW 2147611240 4 eq_refl) (SHW 2147611241 1 eq_refl) (SHW 2147611242 1 eq_refl)
(SHW 2147611243 1 eq_refl) TIDC HTr (XCC 0%nat 6884656 4 0 eq_refl) (XCC1 1%nat 6884691 0 eq_refl eq_refl) (XCC 2%nat 6884128 8 6884136 eq_refl)
(XCC 3%nat 6884120 4 2 eq_refl) (XCC 23%nat 6884152 8 1136392 eq_refl) (XCC 24%nat 6884408 8 686244 eq_refl) (XCC 6%nat 6884116 4 0 eq_refl) (XCC1 22%nat 6746260 0 eq_refl eq_refl) (XCC 4%nat 6884144 8 1136392 eq_refl)
(XCC 5%nat 6884400 8 618204 eq_refl) (STC1 10%nat 1894624 0 eq_refl eq_refl) (XCC 7%nat 6884136 8 0 eq_refl) (STC1 3%nat 1283024 0 eq_refl eq_refl) (STC 0%nat 1270192 8 1270192 eq_refl) (STC 2%nat 1282944 8 1 eq_refl)
(STC 4%nat 1286736 4 1 eq_refl) (STC 5%nat 1286896 8 0 eq_refl) (STC1 8%nat 1300248 1 eq_refl eq_refl) (STC 7%nat 1296952 8 2147450880 eq_refl) (DSC 1281696 8%nat (word_to_le_bytes 8 (Z_to_bv 64 143712)) ltac:(img_rd) eq_refl) (DSC 1281712 1%nat [Z_to_bv 8 32] ltac:(img_rd) eq_refl)
(STC1 6%nat 1295004 1 eq_refl eq_refl) (DSC 1281712 8%nat (word_to_le_bytes 8 (Z_to_bv 64 32)) ltac:(img_rd) eq_refl) (STC 9%nat 1893856 8 18446744073709551615 eq_refl) (STC 1%nat 1270704 8 1207272 eq_refl) (DSC 1281752 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1281760 8%nat (word_to_le_bytes 8 (Z_to_bv 64 143808)) ltac:(img_rd) eq_refl)
(DSC 1281776 1%nat [Z_to_bv 8 32] ltac:(img_rd) eq_refl) (DSC 1281776 8%nat (word_to_le_bytes 8 (Z_to_bv 64 32)) ltac:(img_rd) eq_refl) (DSC 1281816 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1281824 8%nat (word_to_le_bytes 8 (Z_to_bv 64 143840)) ltac:(img_rd) eq_refl) (DSC 1281840 1%nat [Z_to_bv 8 96] ltac:(img_rd) eq_refl) (DSC 1281840 8%nat (word_to_le_bytes 8 (Z_to_bv 64 96)) ltac:(img_rd) eq_refl)
(DSC 1281880 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1281888 8%nat (word_to_le_bytes 8 (Z_to_bv 64 144288)) ltac:(img_rd) eq_refl) (DSC 1281904 1%nat [Z_to_bv 8 32] ltac:(img_rd) eq_refl) (DSC 1281904 8%nat (word_to_le_bytes 8 (Z_to_bv 64 32)) ltac:(img_rd) eq_refl) (DSC 1281944 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1281952 8%nat (word_to_le_bytes 8 (Z_to_bv 64 144320)) ltac:(img_rd) eq_refl)
(DSC 1281968 1%nat [Z_to_bv 8 64] ltac:(img_rd) eq_refl) (DSC 1281968 8%nat (word_to_le_bytes 8 (Z_to_bv 64 64)) ltac:(img_rd) eq_refl) (DSC 1282008 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1282016 8%nat (word_to_le_bytes 8 (Z_to_bv 64 144384)) ltac:(img_rd) eq_refl) (DSC 1282032 1%nat [Z_to_bv 8 32] ltac:(img_rd) eq_refl) (DSC 1282032 8%nat (word_to_le_bytes 8 (Z_to_bv 64 32)) ltac:(img_rd) eq_refl)
(DSC 1282072 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1282080 8%nat (word_to_le_bytes 8 (Z_to_bv 64 144416)) ltac:(img_rd) eq_refl) (DSC 1282096 1%nat [Z_to_bv 8 96] ltac:(img_rd) eq_refl) (DSC 1282096 8%nat (word_to_le_bytes 8 (Z_to_bv 64 96)) ltac:(img_rd) eq_refl) (DSC 1282136 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1282144 8%nat (word_to_le_bytes 8 (Z_to_bv 64 144512)) ltac:(img_rd) eq_refl)
(DSC 1282160 1%nat [Z_to_bv 8 128] ltac:(img_rd) eq_refl) (DSC 1282160 8%nat (word_to_le_bytes 8 (Z_to_bv 64 128)) ltac:(img_rd) eq_refl) (DSC 1282200 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1282208 8%nat (word_to_le_bytes 8 (Z_to_bv 64 144640)) ltac:(img_rd) eq_refl) (DSC 1282224 1%nat [Z_to_bv 8 128] ltac:(img_rd) eq_refl) (DSC 1282224 8%nat (word_to_le_bytes 8 (Z_to_bv 64 128)) ltac:(img_rd) eq_refl)
(DSC 1282264 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1282272 8%nat (word_to_le_bytes 8 (Z_to_bv 64 144768)) ltac:(img_rd) eq_refl) (DSC 1282288 1%nat [Z_to_bv 8 32] ltac:(img_rd) eq_refl) (DSC 1282288 8%nat (word_to_le_bytes 8 (Z_to_bv 64 32)) ltac:(img_rd) eq_refl) (DSC 1282328 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1282336 8%nat (word_to_le_bytes 8 (Z_to_bv 64 144800)) ltac:(img_rd) eq_refl)
(DSC 1282352 1%nat [Z_to_bv 8 96] ltac:(img_rd) eq_refl) (DSC 1282352 8%nat (word_to_le_bytes 8 (Z_to_bv 64 96)) ltac:(img_rd) eq_refl) (DSC 1282392 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1282400 8%nat (word_to_le_bytes 8 (Z_to_bv 64 144896)) ltac:(img_rd) eq_refl) (DSC 1282416 1%nat [Z_to_bv 8 128] ltac:(img_rd) eq_refl) (DSC 1282416 8%nat (word_to_le_bytes 8 (Z_to_bv 64 128)) ltac:(img_rd) eq_refl)
(DSC 1282456 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1282464 8%nat (word_to_le_bytes 8 (Z_to_bv 64 145024)) ltac:(img_rd) eq_refl) (DSC 1282480 1%nat [Z_to_bv 8 128] ltac:(img_rd) eq_refl) (DSC 1282480 8%nat (word_to_le_bytes 8 (Z_to_bv 64 128)) ltac:(img_rd) eq_refl) (DSC 1282520 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1282528 8%nat (word_to_le_bytes 8 (Z_to_bv 64 145152)) ltac:(img_rd) eq_refl)
(DSC 1282544 1%nat [Z_to_bv 8 96] ltac:(img_rd) eq_refl) (DSC 1282544 8%nat (word_to_le_bytes 8 (Z_to_bv 64 96)) ltac:(img_rd) eq_refl) (DSC 1282584 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1282592 8%nat (word_to_le_bytes 8 (Z_to_bv 64 145248)) ltac:(img_rd) eq_refl) (DSC 1282608 1%nat [Z_to_bv 8 96] ltac:(img_rd) eq_refl) (DSC 1282608 8%nat (word_to_le_bytes 8 (Z_to_bv 64 96)) ltac:(img_rd) eq_refl)
(DSC 1282648 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1282656 8%nat (word_to_le_bytes 8 (Z_to_bv 64 145344)) ltac:(img_rd) eq_refl) (DSC 1282672 1%nat [Z_to_bv 8 96] ltac:(img_rd) eq_refl) (DSC 1282672 8%nat (word_to_le_bytes 8 (Z_to_bv 64 96)) ltac:(img_rd) eq_refl) (DSC 1282712 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1282720 8%nat (word_to_le_bytes 8 (Z_to_bv 64 145440)) ltac:(img_rd) eq_refl)
(DSC 1282736 1%nat [Z_to_bv 8 128] ltac:(img_rd) eq_refl) (DSC 1282736 8%nat (word_to_le_bytes 8 (Z_to_bv 64 128)) ltac:(img_rd) eq_refl) (DSC 1282776 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1282784 8%nat (word_to_le_bytes 8 (Z_to_bv 64 145568)) ltac:(img_rd) eq_refl) (DSC 1282800 1%nat [Z_to_bv 8 64] ltac:(img_rd) eq_refl) (DSC 1282800 8%nat (word_to_le_bytes 8 (Z_to_bv 64 64)) ltac:(img_rd) eq_refl)
(DSC 1282840 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1282848 8%nat (word_to_le_bytes 8 (Z_to_bv 64 145632)) ltac:(img_rd) eq_refl) (DSC 1282864 1%nat [Z_to_bv 8 96] ltac:(img_rd) eq_refl) (DSC 1282864 8%nat (word_to_le_bytes 8 (Z_to_bv 64 96)) ltac:(img_rd) eq_refl) (DSC 1282904 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (XCC 8%nat 6886088 8 0 eq_refl)
(XCC 9%nat 1281648 8 1281416 eq_refl) (XCC 10%nat 1281556 4 4294967295 eq_refl) (XCC 11%nat 1281456 8 0 eq_refl) (XCC 12%nat 1281472 8 0 eq_refl) (XCC 13%nat 1281424 8 0 eq_refl) (XCC 14%nat 1281432 8 0 eq_refl)
(XCC 15%nat 1281408 8 1281176 eq_refl) SOlock SOwpos SOwbase SOwrite CANc
SOfd) as
(fx1 & R1 & MV1 & XGR & _ & XFRZ & XMS & _ & _ & Xr2 & _ & _ & _ & Xr8 & Xr9 & Xr10 & Xr11 & Xr12 & _ & _ & _ & _ & Xr17 & Xr18 & Xr19 & Xr21 & Xr22 & _ & Xm112 & Xm120 & Xm128 & Xm136 & Xm104 & Xm96 & Xm88 & Xm80 & Xm72 & Xm64 & Xm56 & Xm48 & Xm40 & Xm32 & Xm24 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _).
unfold V in XFRZ, XMS; cbn beta iota in XFRZ, XMS. cbn [V] in *.
pose proof (dinv_lzinv scfg L ar C IL HI HIok sp0 DL M0 _ _ _ _ _ _ D) as LZ. pose proof LZ as (HH & HL & HA & HM & Hh).
set (good := fun i : Z => i < 1282944 \/ 1286904 <= i < 6884112 \/ 6884136 <= i < 6884656 \/ 6884660 <= i < 2147450880).
assert (FRX : forall i, 0 <= i -> good i -> MV1 (Z_to_bv 64 i) = MV (Z_to_bv 64 i)).
{ intros i Hi Hg. apply XFRZ; [unfold good in Hg; clear - Hi Hg; lia | ..]; (intros X; unfold good in Hg; clear - Hsp' HS1 HS2 Hi Hg X; lia). }
apply (msteps_vis_fx scfg (ahid A model) A fx fx1 R (Z_to_bv 64 0x11575c) M R1 (Z_to_bv 64 0x11d13c) MV1 model _ LZ XMS).
intros M1 model1 MI1 SBM1 VIS1.
assert (LITX : forall a (n : nat) bs, rdn ASEGS MV (Z_to_bv 64 a) n = Some bs ->
(0 <=? a) && ((a + Z.of_nat n <=? 1282944) || ((1286904 <=? a) && (a + Z.of_nat n <=? 6884112)) || ((6884660 <=? a) && (a + Z.of_nat n <=? 2147450880))) = true ->
rdn ASEGS MV1 (Z_to_bv 64 a) n = Some bs).
{ intros a n bs Hr Hb. apply andb_prop in Hb as (B1 & B2). apply Z.leb_le in B1. rewrite !orb_true_iff, !andb_true_iff, !Z.leb_le in B2.
apply (rdn_tr MV MV1 a n bs Hr B1); [lia|]. intros i Hi. apply FRX; [lia|]. unfold good. clear - B1 B2 Hi. lia. }
assert (DATA : rdn ASEGS MV1 (Z_to_bv 64 6886112) (Z.to_nat (2 * 1)) = Some (zero_lines 1%nat)).
{ apply (LITX 6886112 (Z.to_nat (2 * 1))); [|reflexivity]. change (Z.to_nat (2 * 1)) with (2 * 1%nat)%nat.
destruct (BC 0 ltac:(lia)) as (B0a & B0b). cbn [zero_lines].
apply rdn_cons1; [lia | exact B0a|]. apply rdn_cons1; [lia | exact B0b|]. reflexivity. }
set (q := S - 136) in *.
assert (Hq : 0 <= q /\ q <= q + 32 /\ q + 32 + 16 <= 2 ^ 47) by (unfold q; clear - Hsp' HS1 HS2; lia).
assert (Hf : 0 <= 1281176 /\ (1281176 + 124 <= q \/ q + 32 + 16 <= 1281176 + 120) /\ 1281176 + 124 < 2 ^ 63) by (unfold q; clear - Hsp' HS1 HS2; lia).
assert (NLq : forall x, q <= x < q + 32 -> page_in_ranges (page_base_of x) (m_vm_lazy model) = false).
{ intros x Hx. apply (nl_pt scfg L ar C IL HI HIok sp0 Hsp DL M0 _ _ _ _ _ _ x D); unfold q in Hx; clear - Hsp' HS1 HS2 Hx; lia. }
assert (WIN1 : forall a n, usp - 8388608 <= a -> a + n <= usp -> forall d (k : nat), 0 <= d -> d + Z.of_nat k <= n -> store_ok ASEGS MV1 (Z_to_bv 64 (a + d)) k = true)
by (intros a n H1 H2 d k Hd Hk; apply (store_ok_mono ASEGS k MV MV1 _ XGR); apply (WIN a n); assumption).
unfold W. rewrite <- (app_nil_r (zero_lines 1%nat)).
apply (wv_loop scfg (ahid A model) A HH (m_vm_lazy model) HL HA 1281176 1 ltac:(lia) q (q + 32) Hq Hf NLq (t_exit (Z_to_bv 64 st) (m_fs model)) (t_exit_has_nil _ _)
(2 * 1%nat)%nat true R1 M1 model1 q 2 6886112 (2 * 1) 0 0 (zero_lines 1%nat) []).
{ cbn. lia. }
{ exact (sbm_lazy_eq _ _ SBM1). }
{ exact MI1. }
{ rewrite (sbm_halted_eq _ _ SBM1). exact Hh. }
{ rewrite (sbm_fds' _ _ SBM1). exact FD1. }
{ unfold wv_regs. repeat split; assumption. }
{ rewrite VIS1. unfold wv_iov. split; [lia|]. split; [lia|]. split; [right; reflexivity|].
split; [exact Xm136|]. split; [replace (q + 8) with (S - 128) by (unfold q; ring); exact Xm128|].
split; [replace (Z_to_bv 64 q) with (Z_to_bv 64 (q + 0)) by (f_equal; lia); apply (WIN1 q 32); [unfold q; clear - Hsp' HS1 HS2; lia | unfold q; clear - Hsp' HS1 HS2; lia | lia | cbn; lia]|].
split; [unfold wv_buf; split; [lia|]; split; [lia|]; split; [lia|]; split; [right; left; unfold q; clear - Hsp' HS1 HS2; lia|]; split; [exact DATA|];
intros x Hx; apply (nl_pt scfg L ar C IL HI HIok sp0 Hsp DL M0 _ _ _ _ _ _ x D); lia|].
split; [intros X; discriminate X|]. intros _.
split; [replace (q + 16) with (S - 120) by (unfold q; ring); exact Xm120|].
split; [replace (q + 24) with (S - 112) by (unfold q; ring); exact Xm112|].
split; [|lia].
unfold wv_buf. split; [lia|]. split; [lia|]. split; [lia|]. split; [left; reflexivity|]. split; [reflexivity|]. intros x Hx. lia. }
{ lia. }
{ rewrite VIS1. exact (LITX _ _ _ SOfd eq_refl). }
intros R3 M3 model3 MI3 SBM3 KR3 _ FRV3 _ GRV3. rewrite VIS1 in FRV3, GRV3.
set (MV3 := mrestrict (ahid A model) M3) in *.
assert (LIT3 : forall a (n : nat) bs, rdn ASEGS MV (Z_to_bv 64 a) n = Some bs ->
(0 <=? a) && ((a + Z.of_nat n <=? 1282944) || ((1286904 <=? a) && (a + Z.of_nat n <=? 6884112)) || ((6884660 <=? a) && (a + Z.of_nat n <=? 2147450880))) = true ->
rdn ASEGS MV3 (Z_to_bv 64 a) n = Some bs).
{ intros a n bs Hr Hb. pose proof (LITX a n bs Hr Hb) as Y. apply andb_prop in Hb as (B1 & B2). apply Z.leb_le in B1. rewrite !orb_true_iff, !andb_true_iff, !Z.leb_le in B2.
apply (rdn_tr MV1 MV3 a n bs Y B1); [lia|]. intros i Hi. apply FRV3; [lia|]. unfold q. clear - Hsp' HS1 HS2 B1 B2 Hi. lia. }
assert (cellS : forall off k (n : nat) bs, rdn ASEGS MV1 (Z_to_bv 64 (S - k)) n = Some bs ->
(off + k =? 144) && (Z.of_nat n <=? k) && (k <=? 104) = true -> rdn ASEGS MV3 (Z_to_bv 64 (S - 144 + off)) n = Some bs).
{ intros off k n bs Hr Hb. apply andb_prop in Hb as (Hb & Hb3). apply andb_prop in Hb as (Hb1 & Hb2).
apply Z.eqb_eq in Hb1. apply Z.leb_le in Hb2, Hb3. replace (S - 144 + off) with (S - k) by lia.
apply (rdn_tr MV1 MV3 _ _ _ Hr); [clear - Hsp' HS1 HS2 Hb3; lia | clear - Hsp' HS1 HS2 Hb2; lia|].
intros i Hi. apply FRV3; unfold q; clear - Hsp' HS1 HS2 Hb2 Hb3 Hi; lia. }
assert (WIN3 : forall a n, usp - 8388608 <= a -> a + n <= usp -> forall d (k : nat), 0 <= d -> d + Z.of_nat k <= n -> store_ok ASEGS MV3 (Z_to_bv 64 (a + d)) k = true)
by (intros a n H1 H2 d k Hd Hk; apply (store_ok_mono ASEGS k MV1 MV3 _ GRV3); apply (WIN1 a n); assumption).
assert (FW3 : forall a n, 1281176 <= a -> a + n <= 1281176 + 232 -> forall d (k : nat), 0 <= d -> d + Z.of_nat k <= n -> store_ok ASEGS MV3 (Z_to_bv 64 (a + d)) k = true)
by (intros a n H1 H2 d k Hd Hk; apply (store_ok_mono ASEGS k MV1 MV3 _ GRV3); apply (store_ok_mono ASEGS k MV MV1 _ XGR); apply (FW a n); assumption).
assert (IMG3 : forall i, 65536 <= i < 1269760 -> MV3 (Z_to_bv 64 i) = None).
{ intros i Hi. rewrite FRV3; [rewrite FRX; [apply IMGc; exact Hi | lia | unfold good; lia] | lia | unfold q; clear - Hsp' HS1 HS2 Hi; lia]. }
set (VD := fun n : nat => match n with
| 2%nat => S - 144 | 40%nat => canz
| 9%nat => bv_unsigned (getr R (Z_to_bv 5 (Z.of_nat 9))) | 10%nat => bv_unsigned (getr R (Z_to_bv 5 (Z.of_nat 10)))
| 18%nat => bv_unsigned (getr R (Z_to_bv 5 (Z.of_nat 18))) | 19%nat => bv_unsigned (getr R (Z_to_bv 5 (Z.of_nat 19)))
| 20%nat => bv_unsigned (getr R (Z_to_bv 5 (Z.of_nat 20))) | 21%nat => bv_unsigned (getr R (Z_to_bv 5 (Z.of_nat 21)))
| 22%nat => bv_unsigned (getr R (Z_to_bv 5 (Z.of_nat 22)))
| 110%nat => bv_unsigned (getr R3 (Z_to_bv 5 (Z.of_nat 10))) | 118%nat => bv_unsigned (getr R3 (Z_to_bv 5 (Z.of_nat 18)))
| 119%nat => bv_unsigned (getr R3 (Z_to_bv 5 (Z.of_nat 19))) | 120%nat => bv_unsigned (getr R3 (Z_to_bv 5 (Z.of_nat 20)))
| 122%nat => bv_unsigned (getr R3 (Z_to_bv 5 (Z.of_nat 22)))
| _ => 0 end).
assert (Dg2 : getr R3 (Z_to_bv 5 (Z.of_nat 2)) = Z_to_bv 64 (VD 2%nat)) by (eapply eq_trans; [exact (KR3 2%bv ltac:(unfold WV_KEEP; cbn [In]; tauto)) | exact Xr2]).
assert (Dg8 : getr R3 (Z_to_bv 5 (Z.of_nat 8)) = Z_to_bv 64 0) by (eapply eq_trans; [exact (KR3 8%bv ltac:(unfold WV_KEEP; cbn [In]; tauto)) | exact Xr8]).
assert (Dg9 : getr R3 (Z_to_bv 5 (Z.of_nat 9)) = Z_to_bv 64 1281176) by (eapply eq_trans; [exact (KR3 9%bv ltac:(unfold WV_KEEP; cbn [In]; tauto)) | exact Xr9]).
assert (Dg21 : getr R3 (Z_to_bv 5 (Z.of_nat 21)) = Z_to_bv 64 6884096) by (eapply eq_trans; [exact (KR3 21%bv ltac:(unfold WV_KEEP; cbn [In]; tauto)) | exact Xr21]).
assert (Dg10 : getr R3 (Z_to_bv 5 (Z.of_nat 10)) = Z_to_bv 64 (VD 110%nat)) by (cbn [VD]; symmetry; apply Z_to_bv_bv_unsigned).
assert (Dg18 : getr R3 (Z_to_bv 5 (Z.of_nat 18)) = Z_to_bv 64 (VD 118%nat)) by (cbn [VD]; symmetry; apply Z_to_bv_bv_unsigned).
assert (Dg19 : getr R3 (Z_to_bv 5 (Z.of_nat 19)) = Z_to_bv 64 (VD 119%nat)) by (cbn [VD]; symmetry; apply Z_to_bv_bv_unsigned).
assert (Dg20 : getr R3 (Z_to_bv 5 (Z.of_nat 20)) = Z_to_bv 64 (VD 120%nat)) by (cbn [VD]; symmetry; apply Z_to_bv_bv_unsigned).
assert (Dg22 : getr R3 (Z_to_bv 5 (Z.of_nat 22)) = Z_to_bv 64 (VD 122%nat)) by (cbn [VD]; symmetry; apply Z_to_bv_bv_unsigned).
assert (HD64 : 0 <= VD 2%nat < 2 ^ 64) by (cbn [VD]; clear - Hsp' HS1 HS2; lia).
assert (HDr : 140735332552704 <= VD 2%nat <= 140737488355328) by (cbn [VD]; clear - Hsp' HS1 HS2; lia).
assert (HDa : AS0DRVP_dpXd_2.aligned (VD 2%nat) 16).
{ cbn [VD]. unfold AS0DRVP_dpXd_2.aligned. clear - HS16. Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). lia.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false). }
assert (DWR : L5Defs.L5.writable ASEGS MV3 (VD 2%nat - 16) 16).
{ cbn [VD]. intros d k Hd Hk. apply (WIN3 (S - 144 - 16) 16); clear - Hsp' HS1 HS2 Hd Hk; lia. }
assert (DDF : L5Defs.L5.defined MV3 (VD 2%nat - 16) 16).
{ cbn [VD]. intros i Hi. apply (store_ok_defined sp0); [clear - Hsp' HS1 HS2 Hi; lia|]. apply (WIN3 (S - 144 - 16) 16); clear - Hsp' HS1 HS2 Hi; lia. }
destruct (AS0DRVP_dpXd_2.dpXd_2_conc fx1 R3 MV3 VD HD64 (u64_range _)
(u64_range _) (u64_range _) (u64_range _) (u64_range _) (u64_range _) (u64_range _)
Hcan (u64_range _) (u64_range _) (u64_range _) (u64_range _) (u64_range _)
Dg2 Dg8 Dg9 Dg10 Dg18 Dg19
Dg20 Dg21 Dg22 HDr HDa DWR
DDF IMG3 (fun d k Hd Hk => FW3 1281208 8 ltac:(lia) ltac:(lia) d k Hd Hk) (fun d k Hd Hk => FW3 1281216 8 ltac:(lia) ltac:(lia) d k Hd Hk) (fun d k Hd Hk => FW3 1281232 8 ltac:(lia) ltac:(lia) d k Hd Hk) (LIT3 1281264 8%nat _ SObuf eq_refl)
(LIT3 1281272 8%nat _ SObufsz eq_refl) (LIT3 6884096 8%nat _ CANc eq_refl) (cellS 40 104 _ _ Xm104 eq_refl) (cellS 104 40 _ _ Xm40 eq_refl) (cellS 96 48 _ _ Xm48 eq_refl) (cellS 88 56 _ _ Xm56 eq_refl)
(cellS 80 64 _ _ Xm64 eq_refl) (cellS 72 72 _ _ Xm72 eq_refl) (cellS 64 80 _ _ Xm80 eq_refl) (cellS 56 88 _ _ Xm88 eq_refl) (cellS 48 96 _ _ Xm96 eq_refl) (LIT3 1281184 8%nat _ SOrpos eq_refl)
(LIT3 1281192 8%nat _ SOrend eq_refl) (LIT3 1281168 8%nat _ (XCC 16%nat 1281168 8 1280936 eq_refl) eq_refl) (LIT3 1281076 4%nat _ (XCC 17%nat 1281076 4 4294967295 eq_refl) eq_refl) (LIT3 1280976 8%nat _ (XCC 18%nat 1280976 8 0 eq_refl) eq_refl) (LIT3 1280992 8%nat _ (XCC 19%nat 1280992 8 0 eq_refl) eq_refl) (LIT3 1280944 8%nat _ (XCC 20%nat 1280944 8 0 eq_refl) eq_refl)
(LIT3 1280952 8%nat _ (XCC 21%nat 1280952 8 0 eq_refl) eq_refl) (cellS 120 24 _ _ Xm24 eq_refl) (cellS 112 32 _ _ Xm32 eq_refl)) as
(fx2 & R4 & MV4 & _ & _ & _ & DMS & _ & _ & _ & _ & _ & Dr10 & _ & _ & Dr17 & _).
unfold VD in DMS; cbn beta iota in DMS.
assert (LZ3 : lzinv ASEGS (ahid A model) A model3).
{ apply (lzinv_sbm ASEGS (ahid A model) A model model3 LZ MI3). exact (same_but_materialized_trans _ _ _ SBM1 SBM3). }
apply (msteps_vis_fx scfg (ahid A model) A fx1 fx2 R3 (Z_to_bv 64 0x11d148) M3 R4 (Z_to_bv 64 0x11546c) MV4 model3 _ LZ3 DMS).
intros M5 model5 MI5 SBM5 _.
pose proof (same_but_materialized_trans _ _ _ (same_but_materialized_trans _ _ _ SBM1 SBM3) SBM5) as SBMT.
rewrite <- (proj2 (sbm_fds model model5 SBMT)).
apply (rz_exit_at_lit_lz ASEGS scfg R4 (Z_to_bv 64 0x11546c) M5 rom model5 ECALLW st fetch_exitA is_ecall_ECALLW).
- rewrite (sbm_halted_eq _ _ SBMT). exact Hh.
- left. exact Dr17.
- eapply eq_trans; [exact Dr10|]. cbn [VD]. rewrite Z_to_bv_bv_unsigned. exact G10.
- exact Hst.
Qed.
End SE.
#[using="L C IL HIok ICok ILY Hsp DL Hex"] Lemma exit_run_3 : ltac2:(TCodec.tc2 tcn__Jb0DrvExit "TL'6'<'A%2211%411&Q?%611&Q='S9yR0%211'9y8%511%311p051'L&Q0y5%2219&QBr;r:r9r8r7r6r4r2%9887654321&Q:&Q>%1297%3219'?&R=zr5%3221&R?+X0%2241%8241%827@&RA+2+R0%3221%92E1%?261'@&QL(S7+1(>%33Q521%52Q11&S8+QRclH%22QB1%:3QB41%93Q;@7%;2Q81%62QFQ8%>3QF21+4%>3Q@1<%@2Q>1+V^Rf0%<2QL1%D3QL31r<+:%E3QG1C%G231%B2R2QE%J3R221%R=1R0%R311&QN&R8+VbRh0%I2R91u8%544QK21(2&G%124H%32;1%Q73;51&QG%12Q>R3&QF%11R6'K%RD11&M&NrA%211%Q;2RKQ?%5221(J%113%C2:1%QG3:41'R5vS4(I&QMvRK+QRejL%QG2S71rC&QO%11Q3%756B431rB%:221&R1&R3&R4u2%211%42R71&R2r?%R62SF1&O%11<%5231%<271%J4QDI>1p0L1p0Q91p0Q<1p0Q?1p0QM1p0R41p0R;1p0R@1p0RL1p0S41tR:T0S>1p0SC1pUDT?1pVFT@1pV>TA1pTDTB1pR>T21pV0T61pR4T81p2TD1pUFTB1pQ<TD1pQ:TG1").
Proof.
intros LB LK cr A M model R S st tid canz (D & HS1 & HS2 & HS16 & WIN & IMGc & (XC & TIDC & HTr & DESC)) MV Hst Hcan G1 G2 G4 G10 CANc SO SOX FD1.
pose proof Hsp as Hsp'. destruct SO as (_ & SObufsz & _ & SOwpos & SOwbase & SOlock & _ & FW & BW & BC). destruct SOX as (SOwrite & SOfd & SObuf & SOrpos & SOrend).
set (V := fun n : nat => match n with 2%nat => S | 44%nat => tid | 40%nat => canz | _ => 0 end).
assert (HS64 : 0 <= V 2%nat < 2 ^ 64) by (cbn [V]; clear - Hsp' HS1 HS2; lia).
assert (HT64 : 0 <= V 44%nat < 2 ^ 64) by (cbn [V]; clear - HTr; lia).
assert (HSr : 140735332552704 <= V 2%nat <= 140737488355328) by (cbn [V]; clear - Hsp' HS1 HS2; lia).
assert (HSa : AS0DRVP_dpX3_pre.aligned (V 2%nat) 16) by (cbn [V]; exact HS16).
assert (CWR : L5Defs.L5.writable ASEGS MV (V 2%nat - 320) 320).
{ cbn [V]. intros d k Hd Hk. apply (WIN (S - 320) 320); clear - Hsp' HS1 HS2 Hd Hk; lia. }
assert (CDF : L5Defs.L5.defined MV (V 2%nat - 320) 320).
{ cbn [V]. intros i Hi. apply (store_ok_defined sp0); [clear - Hsp' HS1 HS2 Hi; lia|]. apply (WIN (S - 320) 320); clear - Hsp' HS1 HS2 Hi; lia. }
assert (WSG : forall a (n : nat), wseg_ok ASEGS (Z_to_bv 64 a) n = true -> (0 <=? a) && (a + Z.of_nat n <=? 2 ^ 63) = true -> L5Defs.L5.writable ASEGS MV a (Z.of_nat n)).
{ intros a n W Hb. apply andb_prop in Hb as (B1 & B2). apply Z.leb_le in B1, B2. exact (wsg_writable MV a n W B1 B2). }
assert (SHW : forall a n, ((2147468844 <=? a) && (a + n <=? 2147469096) || (2147611092 <=? a) && (a + n <=? 2147611248)) = true -> L5Defs.L5.writable ASEGS MV a n)
by (intros a n Hb; exact (sh_writable _ _ _ _ _ _ a n D Hb)).
assert (STC : forall (i : nat) a n v, nth_error EX_CELLS i = Some (a, n, v) -> rdn ASEGS MV (Z_to_bv 64 a) (Z.to_nat n) = Some (word_to_le_bytes (Z.to_nat n) (Z_to_bv 64 v)))
by (intros i a n v Hn; exact (ex_cell_vis _ _ _ _ _ _ a n v D (nth_error_In _ _ Hn))).
assert (STC1 : forall (i : nat) a v, nth_error EX_CELLS i = Some (a, 1, v) -> (0 <=? v) && (v <? 2 ^ 64) = true -> rdn ASEGS MV (Z_to_bv 64 a) 1 = Some [Z_to_bv 8 v]).
{ intros i a v Hn Hb. apply andb_prop in Hb as (B1 & B2). apply Z.leb_le in B1. apply Z.ltb_lt in B2. rewrite <- (ArtMem.art_bytes1 v (conj B1 B2)). exact (STC i a 1 v Hn). }
assert (XCC : forall (i : nat) a n v, nth_error XC_CELLS_T i = Some (a, n, v) -> rdn ASEGS MV (Z_to_bv 64 a) (Z.to_nat n) = Some (word_to_le_bytes (Z.to_nat n) (Z_to_bv 64 v)))
by (intros i a n v Hn; exact (cells_at_nth MV XC_CELLS_T i a n v XC Hn)).
assert (XCC1 : forall (i : nat) a v, nth_error XC_CELLS_T i = Some (a, 1, v) -> (0 <=? v) && (v <? 2 ^ 64) = true -> rdn ASEGS MV (Z_to_bv 64 a) 1 = Some [Z_to_bv 8 v]).
{ intros i a v Hn Hb. apply andb_prop in Hb as (B1 & B2). apply Z.leb_le in B1. apply Z.ltb_lt in B2. rewrite <- (ArtMem.art_bytes1 v (conj B1 B2)). exact (XCC i a 1 v Hn). }
assert (DSC : forall a (n : nat) bs, rdn ASEGS (fun _ => None) (Z_to_bv 64 a) n = Some bs -> (0x138ea0 <=? a) && (a + Z.of_nat n <=? 0x139380) = true -> rdn ASEGS MV (Z_to_bv 64 a) n = Some bs).
{ intros a n bs Hr Hb. apply andb_prop in Hb as (B1 & B2). apply Z.leb_le in B1, B2. apply (img_cell MV a n bs Hr); [lia | lia|]. intros i Hi. apply DESC. lia. }
destruct (AS0DRVP_dpX3_pre.dpX3_pre_conc fx R MV V HS64 Hcan
HT64 G1 G2 G4 HSr HSa
CWR CDF IMGc (WSG 1282944 8%nat ltac:(vm_compute; reflexivity) eq_refl) (WSG 1283024 1%nat ltac:(vm_compute; reflexivity) eq_refl) (WSG 1286896 8%nat ltac:(vm_compute; reflexivity) eq_refl)
(WSG 6884112 1%nat ltac:(vm_compute; reflexivity) eq_refl) (WSG 6884120 4%nat ltac:(vm_compute; reflexivity) eq_refl) (WSG 6884128 8%nat ltac:(vm_compute; reflexivity) eq_refl) (WSG 6884656 4%nat ltac:(vm_compute; reflexivity) eq_refl) (SHW 2147468844 1 eq_refl) (SHW 2147468845 1 eq_refl)
(SHW 2147468846 1 eq_refl) (SHW 2147468847 1 eq_refl) (SHW 2147468856 1 eq_refl) (SHW 2147468857 1 eq_refl) (SHW 2147468858 1 eq_refl) (SHW 2147468859 1 eq_refl)
(SHW 2147468860 1 eq_refl) (SHW 2147468860 4 eq_refl) (SHW 2147468861 1 eq_refl) (SHW 2147468862 1 eq_refl) (SHW 2147468863 1 eq_refl) (SHW 2147468864 4 eq_refl)
(SHW 2147468868 1 eq_refl) (SHW 2147468868 4 eq_refl) (SHW 2147468869 1 eq_refl) (SHW 2147468870 1 eq_refl) (SHW 2147468871 1 eq_refl) (SHW 2147468916 1 eq_refl)
(SHW 2147468917 1 eq_refl) (SHW 2147468918 1 eq_refl) (SHW 2147468919 1 eq_refl) (SHW 2147468920 1 eq_refl) (SHW 2147468921 1 eq_refl) (SHW 2147468922 1 eq_refl)
(SHW 2147468923 1 eq_refl) (SHW 2147468924 1 eq_refl) (SHW 2147468925 1 eq_refl) (SHW 2147468926 1 eq_refl) (SHW 2147468927 1 eq_refl) (SHW 2147468928 1 eq_refl)
(SHW 2147468929 1 eq_refl) (SHW 2147468930 1 eq_refl) (SHW 2147468931 1 eq_refl) (SHW 2147468932 1 eq_refl) (SHW 2147468932 4 eq_refl) (SHW 2147468933 1 eq_refl)
(SHW 2147468934 1 eq_refl) (SHW 2147468935 1 eq_refl) (SHW 2147468936 4 eq_refl) (SHW 2147468940 1 eq_refl) (SHW 2147468940 4 eq_refl) (SHW 2147468941 1 eq_refl)
(SHW 2147468942 1 eq_refl) (SHW 2147468943 1 eq_refl) (SHW 2147468944 1 eq_refl) (SHW 2147468944 4 eq_refl) (SHW 2147468945 1 eq_refl) (SHW 2147468946 1 eq_refl)
(SHW 2147468947 1 eq_refl) (SHW 2147468948 4 eq_refl) (SHW 2147468952 4 eq_refl) (SHW 2147468956 1 eq_refl) (SHW 2147468956 4 eq_refl) (SHW 2147468957 1 eq_refl)
(SHW 2147468958 1 eq_refl) (SHW 2147468959 1 eq_refl) (SHW 2147468960 1 eq_refl) (SHW 2147468960 4 eq_refl) (SHW 2147468961 1 eq_refl) (SHW 2147468962 1 eq_refl)
(SHW 2147468963 1 eq_refl) (SHW 2147468964 4 eq_refl) (SHW 2147468968 4 eq_refl) (SHW 2147468972 1 eq_refl) (SHW 2147468972 4 eq_refl) (SHW 2147468973 1 eq_refl)
(SHW 2147468974 1 eq_refl) (SHW 2147468975 1 eq_refl) (SHW 2147468976 1 eq_refl) (SHW 2147468977 1 eq_refl) (SHW 2147468978 1 eq_refl) (SHW 2147468979 1 eq_refl)
(SHW 2147468980 1 eq_refl) (SHW 2147468980 4 eq_refl) (SHW 2147468981 1 eq_refl) (SHW 2147468982 1 eq_refl) (SHW 2147468983 1 eq_refl) (SHW 2147468984 4 eq_refl)
(SHW 2147468988 1 eq_refl) (SHW 2147468988 4 eq_refl) (SHW 2147468989 1 eq_refl) (SHW 2147468990 1 eq_refl) (SHW 2147468991 1 eq_refl) (SHW 2147468992 1 eq_refl)
(SHW 2147468992 4 eq_refl) (SHW 2147468993 1 eq_refl) (SHW 2147468994 1 eq_refl) (SHW 2147468995 1 eq_refl) (SHW 2147468996 4 eq_refl) (SHW 2147469000 4 eq_refl)
(SHW 2147469004 1 eq_refl) (SHW 2147469004 4 eq_refl) (SHW 2147469005 1 eq_refl) (SHW 2147469006 1 eq_refl) (SHW 2147469007 1 eq_refl) (SHW 2147469008 1 eq_refl)
(SHW 2147469008 4 eq_refl) (SHW 2147469009 1 eq_refl) (SHW 2147469010 1 eq_refl) (SHW 2147469011 1 eq_refl) (SHW 2147469012 4 eq_refl) (SHW 2147469016 4 eq_refl)
(SHW 2147469020 1 eq_refl) (SHW 2147469020 4 eq_refl) (SHW 2147469021 1 eq_refl) (SHW 2147469022 1 eq_refl) (SHW 2147469023 1 eq_refl) (SHW 2147469024 1 eq_refl)
(SHW 2147469024 4 eq_refl) (SHW 2147469025 1 eq_refl) (SHW 2147469026 1 eq_refl) (SHW 2147469027 1 eq_refl) (SHW 2147469028 4 eq_refl) (SHW 2147469032 1 eq_refl)
(SHW 2147469032 4 eq_refl) (SHW 2147469033 1 eq_refl) (SHW 2147469034 1 eq_refl) (SHW 2147469035 1 eq_refl) (SHW 2147469036 1 eq_refl) (SHW 2147469036 4 eq_refl)
(SHW 2147469037 1 eq_refl) (SHW 2147469038 1 eq_refl) (SHW 2147469039 1 eq_refl) (SHW 2147469040 4 eq_refl) (SHW 2147469044 1 eq_refl) (SHW 2147469044 4 eq_refl)
(SHW 2147469045 1 eq_refl) (SHW 2147469046 1 eq_refl) (SHW 2147469047 1 eq_refl) (SHW 2147469048 1 eq_refl) (SHW 2147469048 4 eq_refl) (SHW 2147469049 1 eq_refl)
(SHW 2147469050 1 eq_refl) (SHW 2147469051 1 eq_refl) (SHW 2147469052 4 eq_refl) (SHW 2147469056 1 eq_refl) (SHW 2147469056 4 eq_refl) (SHW 2147469057 1 eq_refl)
(SHW 2147469058 1 eq_refl) (SHW 2147469059 1 eq_refl) (SHW 2147469060 1 eq_refl) (SHW 2147469060 4 eq_refl) (SHW 2147469061 1 eq_refl) (SHW 2147469062 1 eq_refl)
(SHW 2147469063 1 eq_refl) (SHW 2147469064 4 eq_refl) (SHW 2147469068 4 eq_refl) (SHW 2147469072 1 eq_refl) (SHW 2147469072 4 eq_refl) (SHW 2147469073 1 eq_refl)
(SHW 2147469074 1 eq_refl) (SHW 2147469075 1 eq_refl) (SHW 2147469076 1 eq_refl) (SHW 2147469077 1 eq_refl) (SHW 2147469078 1 eq_refl) (SHW 2147469079 1 eq_refl)
(SHW 2147469080 1 eq_refl) (SHW 2147469081 1 eq_refl) (SHW 2147469082 1 eq_refl) (SHW 2147469083 1 eq_refl) (SHW 2147469084 1 eq_refl) (SHW 2147469084 4 eq_refl)
(SHW 2147469085 1 eq_refl) (SHW 2147469086 1 eq_refl) (SHW 2147469087 1 eq_refl) (SHW 2147469088 4 eq_refl) (SHW 2147469092 1 eq_refl) (SHW 2147469092 4 eq_refl)
(SHW 2147469093 1 eq_refl) (SHW 2147469094 1 eq_refl) (SHW 2147469095 1 eq_refl) (SHW 2147611092 1 eq_refl) (SHW 2147611092 4 eq_refl) (SHW 2147611093 1 eq_refl)
(SHW 2147611094 1 eq_refl) (SHW 2147611095 1 eq_refl) (SHW 2147611096 4 eq_refl) (SHW 2147611100 4 eq_refl) (SHW 2147611104 4 eq_refl) (SHW 2147611108 4 eq_refl)
(SHW 2147611112 4 eq_refl) (SHW 2147611116 4 eq_refl) (SHW 2147611120 8 eq_refl) (SHW 2147611128 8 eq_refl) (SHW 2147611136 8 eq_refl) (SHW 2147611144 8 eq_refl)
(SHW 2147611152 8 eq_refl) (SHW 2147611160 8 eq_refl) (SHW 2147611168 8 eq_refl) (SHW 2147611176 8 eq_refl) (SHW 2147611184 8 eq_refl) (SHW 2147611192 8 eq_refl)
(SHW 2147611200 8 eq_refl) (SHW 2147611208 8 eq_refl) (SHW 2147611216 4 eq_refl) (SHW 2147611220 4 eq_refl) (SHW 2147611224 4 eq_refl) (SHW 2147611228 4 eq_refl)
(SHW 2147611232 4 eq_refl) (SHW 2147611236 4 eq_refl) (SHW 2147611240 1 eq_refl) (SHW 2147611240 4 eq_refl) (SHW 2147611241 1 eq_refl) (SHW 2147611242 1 eq_refl)
(SHW 2147611243 1 eq_refl) TIDC HTr (XCC 0%nat 6884656 4 0 eq_refl) (XCC1 1%nat 6884691 0 eq_refl eq_refl) (XCC 2%nat 6884128 8 6884136 eq_refl)
(XCC 3%nat 6884120 4 2 eq_refl) (XCC 23%nat 6884152 8 1136392 eq_refl) (XCC 24%nat 6884408 8 686244 eq_refl) (XCC 6%nat 6884116 4 0 eq_refl) (XCC1 22%nat 6746260 0 eq_refl eq_refl) (XCC 4%nat 6884144 8 1136392 eq_refl)
(XCC 5%nat 6884400 8 618204 eq_refl) (STC1 10%nat 1894624 0 eq_refl eq_refl) (XCC 7%nat 6884136 8 0 eq_refl) (STC1 3%nat 1283024 0 eq_refl eq_refl) (STC 0%nat 1270192 8 1270192 eq_refl) (STC 2%nat 1282944 8 1 eq_refl)
(STC 4%nat 1286736 4 1 eq_refl) (STC 5%nat 1286896 8 0 eq_refl) (STC1 8%nat 1300248 1 eq_refl eq_refl) (STC 7%nat 1296952 8 2147450880 eq_refl) (DSC 1281696 8%nat (word_to_le_bytes 8 (Z_to_bv 64 143712)) ltac:(img_rd) eq_refl) (DSC 1281712 1%nat [Z_to_bv 8 32] ltac:(img_rd) eq_refl)
(STC1 6%nat 1295004 1 eq_refl eq_refl) (DSC 1281712 8%nat (word_to_le_bytes 8 (Z_to_bv 64 32)) ltac:(img_rd) eq_refl) (STC 9%nat 1893856 8 18446744073709551615 eq_refl) (STC 1%nat 1270704 8 1207272 eq_refl) (DSC 1281752 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1281760 8%nat (word_to_le_bytes 8 (Z_to_bv 64 143808)) ltac:(img_rd) eq_refl)
(DSC 1281776 1%nat [Z_to_bv 8 32] ltac:(img_rd) eq_refl) (DSC 1281776 8%nat (word_to_le_bytes 8 (Z_to_bv 64 32)) ltac:(img_rd) eq_refl) (DSC 1281816 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1281824 8%nat (word_to_le_bytes 8 (Z_to_bv 64 143840)) ltac:(img_rd) eq_refl) (DSC 1281840 1%nat [Z_to_bv 8 96] ltac:(img_rd) eq_refl) (DSC 1281840 8%nat (word_to_le_bytes 8 (Z_to_bv 64 96)) ltac:(img_rd) eq_refl)
(DSC 1281880 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1281888 8%nat (word_to_le_bytes 8 (Z_to_bv 64 144288)) ltac:(img_rd) eq_refl) (DSC 1281904 1%nat [Z_to_bv 8 32] ltac:(img_rd) eq_refl) (DSC 1281904 8%nat (word_to_le_bytes 8 (Z_to_bv 64 32)) ltac:(img_rd) eq_refl) (DSC 1281944 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1281952 8%nat (word_to_le_bytes 8 (Z_to_bv 64 144320)) ltac:(img_rd) eq_refl)
(DSC 1281968 1%nat [Z_to_bv 8 64] ltac:(img_rd) eq_refl) (DSC 1281968 8%nat (word_to_le_bytes 8 (Z_to_bv 64 64)) ltac:(img_rd) eq_refl) (DSC 1282008 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1282016 8%nat (word_to_le_bytes 8 (Z_to_bv 64 144384)) ltac:(img_rd) eq_refl) (DSC 1282032 1%nat [Z_to_bv 8 32] ltac:(img_rd) eq_refl) (DSC 1282032 8%nat (word_to_le_bytes 8 (Z_to_bv 64 32)) ltac:(img_rd) eq_refl)
(DSC 1282072 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1282080 8%nat (word_to_le_bytes 8 (Z_to_bv 64 144416)) ltac:(img_rd) eq_refl) (DSC 1282096 1%nat [Z_to_bv 8 96] ltac:(img_rd) eq_refl) (DSC 1282096 8%nat (word_to_le_bytes 8 (Z_to_bv 64 96)) ltac:(img_rd) eq_refl) (DSC 1282136 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1282144 8%nat (word_to_le_bytes 8 (Z_to_bv 64 144512)) ltac:(img_rd) eq_refl)
(DSC 1282160 1%nat [Z_to_bv 8 128] ltac:(img_rd) eq_refl) (DSC 1282160 8%nat (word_to_le_bytes 8 (Z_to_bv 64 128)) ltac:(img_rd) eq_refl) (DSC 1282200 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1282208 8%nat (word_to_le_bytes 8 (Z_to_bv 64 144640)) ltac:(img_rd) eq_refl) (DSC 1282224 1%nat [Z_to_bv 8 128] ltac:(img_rd) eq_refl) (DSC 1282224 8%nat (word_to_le_bytes 8 (Z_to_bv 64 128)) ltac:(img_rd) eq_refl)
(DSC 1282264 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1282272 8%nat (word_to_le_bytes 8 (Z_to_bv 64 144768)) ltac:(img_rd) eq_refl) (DSC 1282288 1%nat [Z_to_bv 8 32] ltac:(img_rd) eq_refl) (DSC 1282288 8%nat (word_to_le_bytes 8 (Z_to_bv 64 32)) ltac:(img_rd) eq_refl) (DSC 1282328 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1282336 8%nat (word_to_le_bytes 8 (Z_to_bv 64 144800)) ltac:(img_rd) eq_refl)
(DSC 1282352 1%nat [Z_to_bv 8 96] ltac:(img_rd) eq_refl) (DSC 1282352 8%nat (word_to_le_bytes 8 (Z_to_bv 64 96)) ltac:(img_rd) eq_refl) (DSC 1282392 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1282400 8%nat (word_to_le_bytes 8 (Z_to_bv 64 144896)) ltac:(img_rd) eq_refl) (DSC 1282416 1%nat [Z_to_bv 8 128] ltac:(img_rd) eq_refl) (DSC 1282416 8%nat (word_to_le_bytes 8 (Z_to_bv 64 128)) ltac:(img_rd) eq_refl)
(DSC 1282456 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1282464 8%nat (word_to_le_bytes 8 (Z_to_bv 64 145024)) ltac:(img_rd) eq_refl) (DSC 1282480 1%nat [Z_to_bv 8 128] ltac:(img_rd) eq_refl) (DSC 1282480 8%nat (word_to_le_bytes 8 (Z_to_bv 64 128)) ltac:(img_rd) eq_refl) (DSC 1282520 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1282528 8%nat (word_to_le_bytes 8 (Z_to_bv 64 145152)) ltac:(img_rd) eq_refl)
(DSC 1282544 1%nat [Z_to_bv 8 96] ltac:(img_rd) eq_refl) (DSC 1282544 8%nat (word_to_le_bytes 8 (Z_to_bv 64 96)) ltac:(img_rd) eq_refl) (DSC 1282584 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1282592 8%nat (word_to_le_bytes 8 (Z_to_bv 64 145248)) ltac:(img_rd) eq_refl) (DSC 1282608 1%nat [Z_to_bv 8 96] ltac:(img_rd) eq_refl) (DSC 1282608 8%nat (word_to_le_bytes 8 (Z_to_bv 64 96)) ltac:(img_rd) eq_refl)
(DSC 1282648 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1282656 8%nat (word_to_le_bytes 8 (Z_to_bv 64 145344)) ltac:(img_rd) eq_refl) (DSC 1282672 1%nat [Z_to_bv 8 96] ltac:(img_rd) eq_refl) (DSC 1282672 8%nat (word_to_le_bytes 8 (Z_to_bv 64 96)) ltac:(img_rd) eq_refl) (DSC 1282712 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1282720 8%nat (word_to_le_bytes 8 (Z_to_bv 64 145440)) ltac:(img_rd) eq_refl)
(DSC 1282736 1%nat [Z_to_bv 8 128] ltac:(img_rd) eq_refl) (DSC 1282736 8%nat (word_to_le_bytes 8 (Z_to_bv 64 128)) ltac:(img_rd) eq_refl) (DSC 1282776 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1282784 8%nat (word_to_le_bytes 8 (Z_to_bv 64 145568)) ltac:(img_rd) eq_refl) (DSC 1282800 1%nat [Z_to_bv 8 64] ltac:(img_rd) eq_refl) (DSC 1282800 8%nat (word_to_le_bytes 8 (Z_to_bv 64 64)) ltac:(img_rd) eq_refl)
(DSC 1282840 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1282848 8%nat (word_to_le_bytes 8 (Z_to_bv 64 145632)) ltac:(img_rd) eq_refl) (DSC 1282864 1%nat [Z_to_bv 8 96] ltac:(img_rd) eq_refl) (DSC 1282864 8%nat (word_to_le_bytes 8 (Z_to_bv 64 96)) ltac:(img_rd) eq_refl) (DSC 1282904 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (XCC 8%nat 6886088 8 0 eq_refl)
(XCC 9%nat 1281648 8 1281416 eq_refl) (XCC 10%nat 1281556 4 4294967295 eq_refl) (XCC 11%nat 1281456 8 0 eq_refl) (XCC 12%nat 1281472 8 0 eq_refl) (XCC 13%nat 1281424 8 0 eq_refl) (XCC 14%nat 1281432 8 0 eq_refl)
(XCC 15%nat 1281408 8 1281176 eq_refl) SOlock SOwpos SOwbase SOwrite CANc
SOfd) as
(fx1 & R1 & MV1 & XGR & _ & XFRZ & XMS & _ & _ & Xr2 & _ & _ & _ & Xr8 & Xr9 & Xr10 & Xr11 & Xr12 & _ & _ & _ & _ & Xr17 & Xr18 & Xr19 & Xr21 & Xr22 & _ & Xm112 & Xm120 & Xm128 & Xm136 & Xm104 & Xm96 & Xm88 & Xm80 & Xm72 & Xm64 & Xm56 & Xm48 & Xm40 & Xm32 & Xm24 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _).
unfold V in XFRZ, XMS; cbn beta iota in XFRZ, XMS. cbn [V] in *.
pose proof (dinv_lzinv scfg L ar C IL HI HIok sp0 DL M0 _ _ _ _ _ _ D) as LZ. pose proof LZ as (HH & HL & HA & HM & Hh).
set (good := fun i : Z => i < 1282944 \/ 1286904 <= i < 6884112 \/ 6884136 <= i < 6884656 \/ 6884660 <= i < 2147450880).
assert (FRX : forall i, 0 <= i -> good i -> MV1 (Z_to_bv 64 i) = MV (Z_to_bv 64 i)).
{ intros i Hi Hg. apply XFRZ; [unfold good in Hg; clear - Hi Hg; lia | ..]; (intros X; unfold good in Hg; clear - Hsp' HS1 HS2 Hi Hg X; lia). }
apply (msteps_vis_fx scfg (ahid A model) A fx fx1 R (Z_to_bv 64 0x11575c) M R1 (Z_to_bv 64 0x11d13c) MV1 model _ LZ XMS).
intros M1 model1 MI1 SBM1 VIS1.
assert (LITX : forall a (n : nat) bs, rdn ASEGS MV (Z_to_bv 64 a) n = Some bs ->
(0 <=? a) && ((a + Z.of_nat n <=? 1282944) || ((1286904 <=? a) && (a + Z.of_nat n <=? 6884112)) || ((6884660 <=? a) && (a + Z.of_nat n <=? 2147450880))) = true ->
rdn ASEGS MV1 (Z_to_bv 64 a) n = Some bs).
{ intros a n bs Hr Hb. apply andb_prop in Hb as (B1 & B2). apply Z.leb_le in B1. rewrite !orb_true_iff, !andb_true_iff, !Z.leb_le in B2.
apply (rdn_tr MV MV1 a n bs Hr B1); [lia|]. intros i Hi. apply FRX; [lia|]. unfold good. clear - B1 B2 Hi. lia. }
assert (DATA : rdn ASEGS MV1 (Z_to_bv 64 6886112) (Z.to_nat (2 * 2)) = Some (zero_lines 2%nat)).
{ apply (LITX 6886112 (Z.to_nat (2 * 2))); [|reflexivity]. change (Z.to_nat (2 * 2)) with (2 * 2%nat)%nat.
destruct (BC 0 ltac:(lia)) as (B0a & B0b). destruct (BC 1 ltac:(lia)) as (B1a & B1b). cbn [zero_lines].
apply rdn_cons1; [lia | exact B0a|]. apply rdn_cons1; [lia | exact B0b|]. apply rdn_cons1; [lia | exact B1a|]. apply rdn_cons1; [lia | exact B1b|]. reflexivity. }
set (q := S - 136) in *.
assert (Hq : 0 <= q /\ q <= q + 32 /\ q + 32 + 16 <= 2 ^ 47) by (unfold q; clear - Hsp' HS1 HS2; lia).
assert (Hf : 0 <= 1281176 /\ (1281176 + 124 <= q \/ q + 32 + 16 <= 1281176 + 120) /\ 1281176 + 124 < 2 ^ 63) by (unfold q; clear - Hsp' HS1 HS2; lia).
assert (NLq : forall x, q <= x < q + 32 -> page_in_ranges (page_base_of x) (m_vm_lazy model) = false).
{ intros x Hx. apply (nl_pt scfg L ar C IL HI HIok sp0 Hsp DL M0 _ _ _ _ _ _ x D); unfold q in Hx; clear - Hsp' HS1 HS2 Hx; lia. }
assert (WIN1 : forall a n, usp - 8388608 <= a -> a + n <= usp -> forall d (k : nat), 0 <= d -> d + Z.of_nat k <= n -> store_ok ASEGS MV1 (Z_to_bv 64 (a + d)) k = true)
by (intros a n H1 H2 d k Hd Hk; apply (store_ok_mono ASEGS k MV MV1 _ XGR); apply (WIN a n); assumption).
unfold W. rewrite <- (app_nil_r (zero_lines 2%nat)).
apply (wv_loop scfg (ahid A model) A HH (m_vm_lazy model) HL HA 1281176 1 ltac:(lia) q (q + 32) Hq Hf NLq (t_exit (Z_to_bv 64 st) (m_fs model)) (t_exit_has_nil _ _)
(2 * 2%nat)%nat true R1 M1 model1 q 2 6886112 (2 * 2) 0 0 (zero_lines 2%nat) []).
{ cbn. lia. }
{ exact (sbm_lazy_eq _ _ SBM1). }
{ exact MI1. }
{ rewrite (sbm_halted_eq _ _ SBM1). exact Hh. }
{ rewrite (sbm_fds' _ _ SBM1). exact FD1. }
{ unfold wv_regs. repeat split; assumption. }
{ rewrite VIS1. unfold wv_iov. split; [lia|]. split; [lia|]. split; [right; reflexivity|].
split; [exact Xm136|]. split; [replace (q + 8) with (S - 128) by (unfold q; ring); exact Xm128|].
split; [replace (Z_to_bv 64 q) with (Z_to_bv 64 (q + 0)) by (f_equal; lia); apply (WIN1 q 32); [unfold q; clear - Hsp' HS1 HS2; lia | unfold q; clear - Hsp' HS1 HS2; lia | lia | cbn; lia]|].
split; [unfold wv_buf; split; [lia|]; split; [lia|]; split; [lia|]; split; [right; left; unfold q; clear - Hsp' HS1 HS2; lia|]; split; [exact DATA|];
intros x Hx; apply (nl_pt scfg L ar C IL HI HIok sp0 Hsp DL M0 _ _ _ _ _ _ x D); lia|].
split; [intros X; discriminate X|]. intros _.
split; [replace (q + 16) with (S - 120) by (unfold q; ring); exact Xm120|].
split; [replace (q + 24) with (S - 112) by (unfold q; ring); exact Xm112|].
split; [|lia].
unfold wv_buf. split; [lia|]. split; [lia|]. split; [lia|]. split; [left; reflexivity|]. split; [reflexivity|]. intros x Hx. lia. }
{ lia. }
{ rewrite VIS1. exact (LITX _ _ _ SOfd eq_refl). }
intros R3 M3 model3 MI3 SBM3 KR3 _ FRV3 _ GRV3. rewrite VIS1 in FRV3, GRV3.
set (MV3 := mrestrict (ahid A model) M3) in *.
assert (LIT3 : forall a (n : nat) bs, rdn ASEGS MV (Z_to_bv 64 a) n = Some bs ->
(0 <=? a) && ((a + Z.of_nat n <=? 1282944) || ((1286904 <=? a) && (a + Z.of_nat n <=? 6884112)) || ((6884660 <=? a) && (a + Z.of_nat n <=? 2147450880))) = true ->
rdn ASEGS MV3 (Z_to_bv 64 a) n = Some bs).
{ intros a n bs Hr Hb. pose proof (LITX a n bs Hr Hb) as Y. apply andb_prop in Hb as (B1 & B2). apply Z.leb_le in B1. rewrite !orb_true_iff, !andb_true_iff, !Z.leb_le in B2.
apply (rdn_tr MV1 MV3 a n bs Y B1); [lia|]. intros i Hi. apply FRV3; [lia|]. unfold q. clear - Hsp' HS1 HS2 B1 B2 Hi. lia. }
assert (cellS : forall off k (n : nat) bs, rdn ASEGS MV1 (Z_to_bv 64 (S - k)) n = Some bs ->
(off + k =? 144) && (Z.of_nat n <=? k) && (k <=? 104) = true -> rdn ASEGS MV3 (Z_to_bv 64 (S - 144 + off)) n = Some bs).
{ intros off k n bs Hr Hb. apply andb_prop in Hb as (Hb & Hb3). apply andb_prop in Hb as (Hb1 & Hb2).
apply Z.eqb_eq in Hb1. apply Z.leb_le in Hb2, Hb3. replace (S - 144 + off) with (S - k) by lia.
apply (rdn_tr MV1 MV3 _ _ _ Hr); [clear - Hsp' HS1 HS2 Hb3; lia | clear - Hsp' HS1 HS2 Hb2; lia|].
intros i Hi. apply FRV3; unfold q; clear - Hsp' HS1 HS2 Hb2 Hb3 Hi; lia. }
assert (WIN3 : forall a n, usp - 8388608 <= a -> a + n <= usp -> forall d (k : nat), 0 <= d -> d + Z.of_nat k <= n -> store_ok ASEGS MV3 (Z_to_bv 64 (a + d)) k = true)
by (intros a n H1 H2 d k Hd Hk; apply (store_ok_mono ASEGS k MV1 MV3 _ GRV3); apply (WIN1 a n); assumption).
assert (FW3 : forall a n, 1281176 <= a -> a + n <= 1281176 + 232 -> forall d (k : nat), 0 <= d -> d + Z.of_nat k <= n -> store_ok ASEGS MV3 (Z_to_bv 64 (a + d)) k = true)
by (intros a n H1 H2 d k Hd Hk; apply (store_ok_mono ASEGS k MV1 MV3 _ GRV3); apply (store_ok_mono ASEGS k MV MV1 _ XGR); apply (FW a n); assumption).
assert (IMG3 : forall i, 65536 <= i < 1269760 -> MV3 (Z_to_bv 64 i) = None).
{ intros i Hi. rewrite FRV3; [rewrite FRX; [apply IMGc; exact Hi | lia | unfold good; lia] | lia | unfold q; clear - Hsp' HS1 HS2 Hi; lia]. }
set (VD := fun n : nat => match n with
| 2%nat => S - 144 | 40%nat => canz
| 9%nat => bv_unsigned (getr R (Z_to_bv 5 (Z.of_nat 9))) | 10%nat => bv_unsigned (getr R (Z_to_bv 5 (Z.of_nat 10)))
| 18%nat => bv_unsigned (getr R (Z_to_bv 5 (Z.of_nat 18))) | 19%nat => bv_unsigned (getr R (Z_to_bv 5 (Z.of_nat 19)))
| 20%nat => bv_unsigned (getr R (Z_to_bv 5 (Z.of_nat 20))) | 21%nat => bv_unsigned (getr R (Z_to_bv 5 (Z.of_nat 21)))
| 22%nat => bv_unsigned (getr R (Z_to_bv 5 (Z.of_nat 22)))
| 110%nat => bv_unsigned (getr R3 (Z_to_bv 5 (Z.of_nat 10))) | 118%nat => bv_unsigned (getr R3 (Z_to_bv 5 (Z.of_nat 18)))
| 119%nat => bv_unsigned (getr R3 (Z_to_bv 5 (Z.of_nat 19))) | 120%nat => bv_unsigned (getr R3 (Z_to_bv 5 (Z.of_nat 20)))
| 122%nat => bv_unsigned (getr R3 (Z_to_bv 5 (Z.of_nat 22)))
| _ => 0 end).
assert (Dg2 : getr R3 (Z_to_bv 5 (Z.of_nat 2)) = Z_to_bv 64 (VD 2%nat)) by (eapply eq_trans; [exact (KR3 2%bv ltac:(unfold WV_KEEP; cbn [In]; tauto)) | exact Xr2]).
assert (Dg8 : getr R3 (Z_to_bv 5 (Z.of_nat 8)) = Z_to_bv 64 0) by (eapply eq_trans; [exact (KR3 8%bv ltac:(unfold WV_KEEP; cbn [In]; tauto)) | exact Xr8]).
assert (Dg9 : getr R3 (Z_to_bv 5 (Z.of_nat 9)) = Z_to_bv 64 1281176) by (eapply eq_trans; [exact (KR3 9%bv ltac:(unfold WV_KEEP; cbn [In]; tauto)) | exact Xr9]).
assert (Dg21 : getr R3 (Z_to_bv 5 (Z.of_nat 21)) = Z_to_bv 64 6884096) by (eapply eq_trans; [exact (KR3 21%bv ltac:(unfold WV_KEEP; cbn [In]; tauto)) | exact Xr21]).
assert (Dg10 : getr R3 (Z_to_bv 5 (Z.of_nat 10)) = Z_to_bv 64 (VD 110%nat)) by (cbn [VD]; symmetry; apply Z_to_bv_bv_unsigned).
assert (Dg18 : getr R3 (Z_to_bv 5 (Z.of_nat 18)) = Z_to_bv 64 (VD 118%nat)) by (cbn [VD]; symmetry; apply Z_to_bv_bv_unsigned).
assert (Dg19 : getr R3 (Z_to_bv 5 (Z.of_nat 19)) = Z_to_bv 64 (VD 119%nat)) by (cbn [VD]; symmetry; apply Z_to_bv_bv_unsigned).
assert (Dg20 : getr R3 (Z_to_bv 5 (Z.of_nat 20)) = Z_to_bv 64 (VD 120%nat)) by (cbn [VD]; symmetry; apply Z_to_bv_bv_unsigned).
assert (Dg22 : getr R3 (Z_to_bv 5 (Z.of_nat 22)) = Z_to_bv 64 (VD 122%nat)) by (cbn [VD]; symmetry; apply Z_to_bv_bv_unsigned).
assert (HD64 : 0 <= VD 2%nat < 2 ^ 64) by (cbn [VD]; clear - Hsp' HS1 HS2; lia).
assert (HDr : 140735332552704 <= VD 2%nat <= 140737488355328) by (cbn [VD]; clear - Hsp' HS1 HS2; lia).
assert (HDa : AS0DRVP_dpXd_3.aligned (VD 2%nat) 16).
{ cbn [VD]. unfold AS0DRVP_dpXd_3.aligned. clear - HS16. Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). lia.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false). }
assert (DWR : L5Defs.L5.writable ASEGS MV3 (VD 2%nat - 16) 16).
{ cbn [VD]. intros d k Hd Hk. apply (WIN3 (S - 144 - 16) 16); clear - Hsp' HS1 HS2 Hd Hk; lia. }
assert (DDF : L5Defs.L5.defined MV3 (VD 2%nat - 16) 16).
{ cbn [VD]. intros i Hi. apply (store_ok_defined sp0); [clear - Hsp' HS1 HS2 Hi; lia|]. apply (WIN3 (S - 144 - 16) 16); clear - Hsp' HS1 HS2 Hi; lia. }
destruct (AS0DRVP_dpXd_3.dpXd_3_conc fx1 R3 MV3 VD HD64 (u64_range _)
(u64_range _) (u64_range _) (u64_range _) (u64_range _) (u64_range _) (u64_range _)
Hcan (u64_range _) (u64_range _) (u64_range _) (u64_range _) (u64_range _)
Dg2 Dg8 Dg9 Dg10 Dg18 Dg19
Dg20 Dg21 Dg22 HDr HDa DWR
DDF IMG3 (fun d k Hd Hk => FW3 1281208 8 ltac:(lia) ltac:(lia) d k Hd Hk) (fun d k Hd Hk => FW3 1281216 8 ltac:(lia) ltac:(lia) d k Hd Hk) (fun d k Hd Hk => FW3 1281232 8 ltac:(lia) ltac:(lia) d k Hd Hk) (LIT3 1281264 8%nat _ SObuf eq_refl)
(LIT3 1281272 8%nat _ SObufsz eq_refl) (LIT3 6884096 8%nat _ CANc eq_refl) (cellS 40 104 _ _ Xm104 eq_refl) (cellS 104 40 _ _ Xm40 eq_refl) (cellS 96 48 _ _ Xm48 eq_refl) (cellS 88 56 _ _ Xm56 eq_refl)
(cellS 80 64 _ _ Xm64 eq_refl) (cellS 72 72 _ _ Xm72 eq_refl) (cellS 64 80 _ _ Xm80 eq_refl) (cellS 56 88 _ _ Xm88 eq_refl) (cellS 48 96 _ _ Xm96 eq_refl) (LIT3 1281184 8%nat _ SOrpos eq_refl)
(LIT3 1281192 8%nat _ SOrend eq_refl) (LIT3 1281168 8%nat _ (XCC 16%nat 1281168 8 1280936 eq_refl) eq_refl) (LIT3 1281076 4%nat _ (XCC 17%nat 1281076 4 4294967295 eq_refl) eq_refl) (LIT3 1280976 8%nat _ (XCC 18%nat 1280976 8 0 eq_refl) eq_refl) (LIT3 1280992 8%nat _ (XCC 19%nat 1280992 8 0 eq_refl) eq_refl) (LIT3 1280944 8%nat _ (XCC 20%nat 1280944 8 0 eq_refl) eq_refl)
(LIT3 1280952 8%nat _ (XCC 21%nat 1280952 8 0 eq_refl) eq_refl) (cellS 120 24 _ _ Xm24 eq_refl) (cellS 112 32 _ _ Xm32 eq_refl)) as
(fx2 & R4 & MV4 & _ & _ & _ & DMS & _ & _ & _ & _ & _ & Dr10 & _ & _ & Dr17 & _).
unfold VD in DMS; cbn beta iota in DMS.
assert (LZ3 : lzinv ASEGS (ahid A model) A model3).
{ apply (lzinv_sbm ASEGS (ahid A model) A model model3 LZ MI3). exact (same_but_materialized_trans _ _ _ SBM1 SBM3). }
apply (msteps_vis_fx scfg (ahid A model) A fx1 fx2 R3 (Z_to_bv 64 0x11d148) M3 R4 (Z_to_bv 64 0x11546c) MV4 model3 _ LZ3 DMS).
intros M5 model5 MI5 SBM5 _.
pose proof (same_but_materialized_trans _ _ _ (same_but_materialized_trans _ _ _ SBM1 SBM3) SBM5) as SBMT.
rewrite <- (proj2 (sbm_fds model model5 SBMT)).
apply (rz_exit_at_lit_lz ASEGS scfg R4 (Z_to_bv 64 0x11546c) M5 rom model5 ECALLW st fetch_exitA is_ecall_ECALLW).
- rewrite (sbm_halted_eq _ _ SBMT). exact Hh.
- left. exact Dr17.
- eapply eq_trans; [exact Dr10|]. cbn [VD]. rewrite Z_to_bv_bv_unsigned. exact G10.
- exact Hst.
Qed.
#[using="L C IL HIok ICok ILY Hsp DL Hex"] Lemma exit_run_4 : ltac2:(TCodec.tc2 tcn__Jb0DrvExit "TM'6'<'A%2211%411&Q?%611&Q='S9yR0%211'9y8%511%311p051'L&Q0y5%2219&QBr;r:r9r8r7r6r4r2%9887654321&Q:&Q>%1297%3219'?&R=zr5%3221&R?+X0%2241%8241%827@&RA+2+R0%3221%92E1%?261'@&QL(S7+1(>%33Q521%52Q11&S8+QRclH%22QB1%:3QB41%93Q;@7%;2Q81%62QFQ8%>3QF21+4%>3Q@1<%@2Q>1+V^Rf0%<2QL1%D3QL31r<+:%E3QG1C%G231%B2R2QE%J3R221%R=1R0%R311&QN&R8+VbRh0%I2R91u8%544QK21(2&G%124H%32;1%Q73;51&QG+3%221R4&QF%11R7'K%RE11&M&NrA%211%Q<2RLQ@%5221(J%113%D2:1%QH3:41'R5vS4(I&QMvRK+QRejL%QH2S81rC&QO%11Q4%756B431rB%:221&R1&R3&R4u3%211%42R81&R2r?%R72SG1&O%11<%5231%<271%J4QEI>1p0L1p0Q91p0Q<1p0Q@1p0QN1p0R51p0R<1p0RA1p0RM1p0S51tR:T1S?1p0SD1pUDT@1pVFTA1pV>TB1pTDTC1pR>T31pV0T71pR4T91p2TE1pUFTC1pQ<TE1pQ:TH1").
Proof.
intros LB LK cr A M model R S st tid canz (D & HS1 & HS2 & HS16 & WIN & IMGc & (XC & TIDC & HTr & DESC)) MV Hst Hcan G1 G2 G4 G10 CANc SO SOX FD1.
pose proof Hsp as Hsp'. destruct SO as (_ & SObufsz & _ & SOwpos & SOwbase & SOlock & _ & FW & BW & BC). destruct SOX as (SOwrite & SOfd & SObuf & SOrpos & SOrend).
set (V := fun n : nat => match n with 2%nat => S | 44%nat => tid | 40%nat => canz | _ => 0 end).
assert (HS64 : 0 <= V 2%nat < 2 ^ 64) by (cbn [V]; clear - Hsp' HS1 HS2; lia).
assert (HT64 : 0 <= V 44%nat < 2 ^ 64) by (cbn [V]; clear - HTr; lia).
assert (HSr : 140735332552704 <= V 2%nat <= 140737488355328) by (cbn [V]; clear - Hsp' HS1 HS2; lia).
assert (HSa : AS0DRVP_dpX4_pre.aligned (V 2%nat) 16) by (cbn [V]; exact HS16).
assert (CWR : L5Defs.L5.writable ASEGS MV (V 2%nat - 320) 320).
{ cbn [V]. intros d k Hd Hk. apply (WIN (S - 320) 320); clear - Hsp' HS1 HS2 Hd Hk; lia. }
assert (CDF : L5Defs.L5.defined MV (V 2%nat - 320) 320).
{ cbn [V]. intros i Hi. apply (store_ok_defined sp0); [clear - Hsp' HS1 HS2 Hi; lia|]. apply (WIN (S - 320) 320); clear - Hsp' HS1 HS2 Hi; lia. }
assert (WSG : forall a (n : nat), wseg_ok ASEGS (Z_to_bv 64 a) n = true -> (0 <=? a) && (a + Z.of_nat n <=? 2 ^ 63) = true -> L5Defs.L5.writable ASEGS MV a (Z.of_nat n)).
{ intros a n W Hb. apply andb_prop in Hb as (B1 & B2). apply Z.leb_le in B1, B2. exact (wsg_writable MV a n W B1 B2). }
assert (SHW : forall a n, ((2147468844 <=? a) && (a + n <=? 2147469096) || (2147611092 <=? a) && (a + n <=? 2147611248)) = true -> L5Defs.L5.writable ASEGS MV a n)
by (intros a n Hb; exact (sh_writable _ _ _ _ _ _ a n D Hb)).
assert (STC : forall (i : nat) a n v, nth_error EX_CELLS i = Some (a, n, v) -> rdn ASEGS MV (Z_to_bv 64 a) (Z.to_nat n) = Some (word_to_le_bytes (Z.to_nat n) (Z_to_bv 64 v)))
by (intros i a n v Hn; exact (ex_cell_vis _ _ _ _ _ _ a n v D (nth_error_In _ _ Hn))).
assert (STC1 : forall (i : nat) a v, nth_error EX_CELLS i = Some (a, 1, v) -> (0 <=? v) && (v <? 2 ^ 64) = true -> rdn ASEGS MV (Z_to_bv 64 a) 1 = Some [Z_to_bv 8 v]).
{ intros i a v Hn Hb. apply andb_prop in Hb as (B1 & B2). apply Z.leb_le in B1. apply Z.ltb_lt in B2. rewrite <- (ArtMem.art_bytes1 v (conj B1 B2)). exact (STC i a 1 v Hn). }
assert (XCC : forall (i : nat) a n v, nth_error XC_CELLS_T i = Some (a, n, v) -> rdn ASEGS MV (Z_to_bv 64 a) (Z.to_nat n) = Some (word_to_le_bytes (Z.to_nat n) (Z_to_bv 64 v)))
by (intros i a n v Hn; exact (cells_at_nth MV XC_CELLS_T i a n v XC Hn)).
assert (XCC1 : forall (i : nat) a v, nth_error XC_CELLS_T i = Some (a, 1, v) -> (0 <=? v) && (v <? 2 ^ 64) = true -> rdn ASEGS MV (Z_to_bv 64 a) 1 = Some [Z_to_bv 8 v]).
{ intros i a v Hn Hb. apply andb_prop in Hb as (B1 & B2). apply Z.leb_le in B1. apply Z.ltb_lt in B2. rewrite <- (ArtMem.art_bytes1 v (conj B1 B2)). exact (XCC i a 1 v Hn). }
assert (DSC : forall a (n : nat) bs, rdn ASEGS (fun _ => None) (Z_to_bv 64 a) n = Some bs -> (0x138ea0 <=? a) && (a + Z.of_nat n <=? 0x139380) = true -> rdn ASEGS MV (Z_to_bv 64 a) n = Some bs).
{ intros a n bs Hr Hb. apply andb_prop in Hb as (B1 & B2). apply Z.leb_le in B1, B2. apply (img_cell MV a n bs Hr); [lia | lia|]. intros i Hi. apply DESC. lia. }
destruct (AS0DRVP_dpX4_pre.dpX4_pre_conc fx R MV V HS64 Hcan
HT64 G1 G2 G4 HSr HSa
CWR CDF IMGc (WSG 1282944 8%nat ltac:(vm_compute; reflexivity) eq_refl) (WSG 1283024 1%nat ltac:(vm_compute; reflexivity) eq_refl) (WSG 1286896 8%nat ltac:(vm_compute; reflexivity) eq_refl)
(WSG 6884112 1%nat ltac:(vm_compute; reflexivity) eq_refl) (WSG 6884120 4%nat ltac:(vm_compute; reflexivity) eq_refl) (WSG 6884128 8%nat ltac:(vm_compute; reflexivity) eq_refl) (WSG 6884656 4%nat ltac:(vm_compute; reflexivity) eq_refl) (SHW 2147468844 1 eq_refl) (SHW 2147468845 1 eq_refl)
(SHW 2147468846 1 eq_refl) (SHW 2147468847 1 eq_refl) (SHW 2147468856 1 eq_refl) (SHW 2147468857 1 eq_refl) (SHW 2147468858 1 eq_refl) (SHW 2147468859 1 eq_refl)
(SHW 2147468860 1 eq_refl) (SHW 2147468860 4 eq_refl) (SHW 2147468861 1 eq_refl) (SHW 2147468862 1 eq_refl) (SHW 2147468863 1 eq_refl) (SHW 2147468864 4 eq_refl)
(SHW 2147468868 1 eq_refl) (SHW 2147468868 4 eq_refl) (SHW 2147468869 1 eq_refl) (SHW 2147468870 1 eq_refl) (SHW 2147468871 1 eq_refl) (SHW 2147468916 1 eq_refl)
(SHW 2147468917 1 eq_refl) (SHW 2147468918 1 eq_refl) (SHW 2147468919 1 eq_refl) (SHW 2147468920 1 eq_refl) (SHW 2147468921 1 eq_refl) (SHW 2147468922 1 eq_refl)
(SHW 2147468923 1 eq_refl) (SHW 2147468924 1 eq_refl) (SHW 2147468925 1 eq_refl) (SHW 2147468926 1 eq_refl) (SHW 2147468927 1 eq_refl) (SHW 2147468928 1 eq_refl)
(SHW 2147468929 1 eq_refl) (SHW 2147468930 1 eq_refl) (SHW 2147468931 1 eq_refl) (SHW 2147468932 1 eq_refl) (SHW 2147468932 4 eq_refl) (SHW 2147468933 1 eq_refl)
(SHW 2147468934 1 eq_refl) (SHW 2147468935 1 eq_refl) (SHW 2147468936 4 eq_refl) (SHW 2147468940 1 eq_refl) (SHW 2147468940 4 eq_refl) (SHW 2147468941 1 eq_refl)
(SHW 2147468942 1 eq_refl) (SHW 2147468943 1 eq_refl) (SHW 2147468944 1 eq_refl) (SHW 2147468944 4 eq_refl) (SHW 2147468945 1 eq_refl) (SHW 2147468946 1 eq_refl)
(SHW 2147468947 1 eq_refl) (SHW 2147468948 4 eq_refl) (SHW 2147468952 4 eq_refl) (SHW 2147468956 1 eq_refl) (SHW 2147468956 4 eq_refl) (SHW 2147468957 1 eq_refl)
(SHW 2147468958 1 eq_refl) (SHW 2147468959 1 eq_refl) (SHW 2147468960 1 eq_refl) (SHW 2147468960 4 eq_refl) (SHW 2147468961 1 eq_refl) (SHW 2147468962 1 eq_refl)
(SHW 2147468963 1 eq_refl) (SHW 2147468964 4 eq_refl) (SHW 2147468968 4 eq_refl) (SHW 2147468972 1 eq_refl) (SHW 2147468972 4 eq_refl) (SHW 2147468973 1 eq_refl)
(SHW 2147468974 1 eq_refl) (SHW 2147468975 1 eq_refl) (SHW 2147468976 1 eq_refl) (SHW 2147468977 1 eq_refl) (SHW 2147468978 1 eq_refl) (SHW 2147468979 1 eq_refl)
(SHW 2147468980 1 eq_refl) (SHW 2147468980 4 eq_refl) (SHW 2147468981 1 eq_refl) (SHW 2147468982 1 eq_refl) (SHW 2147468983 1 eq_refl) (SHW 2147468984 4 eq_refl)
(SHW 2147468988 1 eq_refl) (SHW 2147468988 4 eq_refl) (SHW 2147468989 1 eq_refl) (SHW 2147468990 1 eq_refl) (SHW 2147468991 1 eq_refl) (SHW 2147468992 1 eq_refl)
(SHW 2147468992 4 eq_refl) (SHW 2147468993 1 eq_refl) (SHW 2147468994 1 eq_refl) (SHW 2147468995 1 eq_refl) (SHW 2147468996 4 eq_refl) (SHW 2147469000 4 eq_refl)
(SHW 2147469004 1 eq_refl) (SHW 2147469004 4 eq_refl) (SHW 2147469005 1 eq_refl) (SHW 2147469006 1 eq_refl) (SHW 2147469007 1 eq_refl) (SHW 2147469008 1 eq_refl)
(SHW 2147469008 4 eq_refl) (SHW 2147469009 1 eq_refl) (SHW 2147469010 1 eq_refl) (SHW 2147469011 1 eq_refl) (SHW 2147469012 4 eq_refl) (SHW 2147469016 4 eq_refl)
(SHW 2147469020 1 eq_refl) (SHW 2147469020 4 eq_refl) (SHW 2147469021 1 eq_refl) (SHW 2147469022 1 eq_refl) (SHW 2147469023 1 eq_refl) (SHW 2147469024 1 eq_refl)
(SHW 2147469024 4 eq_refl) (SHW 2147469025 1 eq_refl) (SHW 2147469026 1 eq_refl) (SHW 2147469027 1 eq_refl) (SHW 2147469028 4 eq_refl) (SHW 2147469032 1 eq_refl)
(SHW 2147469032 4 eq_refl) (SHW 2147469033 1 eq_refl) (SHW 2147469034 1 eq_refl) (SHW 2147469035 1 eq_refl) (SHW 2147469036 1 eq_refl) (SHW 2147469036 4 eq_refl)
(SHW 2147469037 1 eq_refl) (SHW 2147469038 1 eq_refl) (SHW 2147469039 1 eq_refl) (SHW 2147469040 4 eq_refl) (SHW 2147469044 1 eq_refl) (SHW 2147469044 4 eq_refl)
(SHW 2147469045 1 eq_refl) (SHW 2147469046 1 eq_refl) (SHW 2147469047 1 eq_refl) (SHW 2147469048 1 eq_refl) (SHW 2147469048 4 eq_refl) (SHW 2147469049 1 eq_refl)
(SHW 2147469050 1 eq_refl) (SHW 2147469051 1 eq_refl) (SHW 2147469052 4 eq_refl) (SHW 2147469056 1 eq_refl) (SHW 2147469056 4 eq_refl) (SHW 2147469057 1 eq_refl)
(SHW 2147469058 1 eq_refl) (SHW 2147469059 1 eq_refl) (SHW 2147469060 1 eq_refl) (SHW 2147469060 4 eq_refl) (SHW 2147469061 1 eq_refl) (SHW 2147469062 1 eq_refl)
(SHW 2147469063 1 eq_refl) (SHW 2147469064 4 eq_refl) (SHW 2147469068 4 eq_refl) (SHW 2147469072 1 eq_refl) (SHW 2147469072 4 eq_refl) (SHW 2147469073 1 eq_refl)
(SHW 2147469074 1 eq_refl) (SHW 2147469075 1 eq_refl) (SHW 2147469076 1 eq_refl) (SHW 2147469077 1 eq_refl) (SHW 2147469078 1 eq_refl) (SHW 2147469079 1 eq_refl)
(SHW 2147469080 1 eq_refl) (SHW 2147469081 1 eq_refl) (SHW 2147469082 1 eq_refl) (SHW 2147469083 1 eq_refl) (SHW 2147469084 1 eq_refl) (SHW 2147469084 4 eq_refl)
(SHW 2147469085 1 eq_refl) (SHW 2147469086 1 eq_refl) (SHW 2147469087 1 eq_refl) (SHW 2147469088 4 eq_refl) (SHW 2147469092 1 eq_refl) (SHW 2147469092 4 eq_refl)
(SHW 2147469093 1 eq_refl) (SHW 2147469094 1 eq_refl) (SHW 2147469095 1 eq_refl) (SHW 2147611092 1 eq_refl) (SHW 2147611092 4 eq_refl) (SHW 2147611093 1 eq_refl)
(SHW 2147611094 1 eq_refl) (SHW 2147611095 1 eq_refl) (SHW 2147611096 4 eq_refl) (SHW 2147611100 4 eq_refl) (SHW 2147611104 4 eq_refl) (SHW 2147611108 4 eq_refl)
(SHW 2147611112 4 eq_refl) (SHW 2147611116 4 eq_refl) (SHW 2147611120 8 eq_refl) (SHW 2147611128 8 eq_refl) (SHW 2147611136 8 eq_refl) (SHW 2147611144 8 eq_refl)
(SHW 2147611152 8 eq_refl) (SHW 2147611160 8 eq_refl) (SHW 2147611168 8 eq_refl) (SHW 2147611176 8 eq_refl) (SHW 2147611184 8 eq_refl) (SHW 2147611192 8 eq_refl)
(SHW 2147611200 8 eq_refl) (SHW 2147611208 8 eq_refl) (SHW 2147611216 4 eq_refl) (SHW 2147611220 4 eq_refl) (SHW 2147611224 4 eq_refl) (SHW 2147611228 4 eq_refl)
(SHW 2147611232 4 eq_refl) (SHW 2147611236 4 eq_refl) (SHW 2147611240 1 eq_refl) (SHW 2147611240 4 eq_refl) (SHW 2147611241 1 eq_refl) (SHW 2147611242 1 eq_refl)
(SHW 2147611243 1 eq_refl) TIDC HTr (XCC 0%nat 6884656 4 0 eq_refl) (XCC1 1%nat 6884691 0 eq_refl eq_refl) (XCC 2%nat 6884128 8 6884136 eq_refl)
(XCC 3%nat 6884120 4 2 eq_refl) (XCC 23%nat 6884152 8 1136392 eq_refl) (XCC 24%nat 6884408 8 686244 eq_refl) (XCC 6%nat 6884116 4 0 eq_refl) (XCC1 22%nat 6746260 0 eq_refl eq_refl) (XCC 4%nat 6884144 8 1136392 eq_refl)
(XCC 5%nat 6884400 8 618204 eq_refl) (STC1 10%nat 1894624 0 eq_refl eq_refl) (XCC 7%nat 6884136 8 0 eq_refl) (STC1 3%nat 1283024 0 eq_refl eq_refl) (STC 0%nat 1270192 8 1270192 eq_refl) (STC 2%nat 1282944 8 1 eq_refl)
(STC 4%nat 1286736 4 1 eq_refl) (STC 5%nat 1286896 8 0 eq_refl) (STC1 8%nat 1300248 1 eq_refl eq_refl) (STC 7%nat 1296952 8 2147450880 eq_refl) (DSC 1281696 8%nat (word_to_le_bytes 8 (Z_to_bv 64 143712)) ltac:(img_rd) eq_refl) (DSC 1281712 1%nat [Z_to_bv 8 32] ltac:(img_rd) eq_refl)
(STC1 6%nat 1295004 1 eq_refl eq_refl) (DSC 1281712 8%nat (word_to_le_bytes 8 (Z_to_bv 64 32)) ltac:(img_rd) eq_refl) (STC 9%nat 1893856 8 18446744073709551615 eq_refl) (STC 1%nat 1270704 8 1207272 eq_refl) (DSC 1281752 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1281760 8%nat (word_to_le_bytes 8 (Z_to_bv 64 143808)) ltac:(img_rd) eq_refl)
(DSC 1281776 1%nat [Z_to_bv 8 32] ltac:(img_rd) eq_refl) (DSC 1281776 8%nat (word_to_le_bytes 8 (Z_to_bv 64 32)) ltac:(img_rd) eq_refl) (DSC 1281816 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1281824 8%nat (word_to_le_bytes 8 (Z_to_bv 64 143840)) ltac:(img_rd) eq_refl) (DSC 1281840 1%nat [Z_to_bv 8 96] ltac:(img_rd) eq_refl) (DSC 1281840 8%nat (word_to_le_bytes 8 (Z_to_bv 64 96)) ltac:(img_rd) eq_refl)
(DSC 1281880 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1281888 8%nat (word_to_le_bytes 8 (Z_to_bv 64 144288)) ltac:(img_rd) eq_refl) (DSC 1281904 1%nat [Z_to_bv 8 32] ltac:(img_rd) eq_refl) (DSC 1281904 8%nat (word_to_le_bytes 8 (Z_to_bv 64 32)) ltac:(img_rd) eq_refl) (DSC 1281944 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1281952 8%nat (word_to_le_bytes 8 (Z_to_bv 64 144320)) ltac:(img_rd) eq_refl)
(DSC 1281968 1%nat [Z_to_bv 8 64] ltac:(img_rd) eq_refl) (DSC 1281968 8%nat (word_to_le_bytes 8 (Z_to_bv 64 64)) ltac:(img_rd) eq_refl) (DSC 1282008 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1282016 8%nat (word_to_le_bytes 8 (Z_to_bv 64 144384)) ltac:(img_rd) eq_refl) (DSC 1282032 1%nat [Z_to_bv 8 32] ltac:(img_rd) eq_refl) (DSC 1282032 8%nat (word_to_le_bytes 8 (Z_to_bv 64 32)) ltac:(img_rd) eq_refl)
(DSC 1282072 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1282080 8%nat (word_to_le_bytes 8 (Z_to_bv 64 144416)) ltac:(img_rd) eq_refl) (DSC 1282096 1%nat [Z_to_bv 8 96] ltac:(img_rd) eq_refl) (DSC 1282096 8%nat (word_to_le_bytes 8 (Z_to_bv 64 96)) ltac:(img_rd) eq_refl) (DSC 1282136 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1282144 8%nat (word_to_le_bytes 8 (Z_to_bv 64 144512)) ltac:(img_rd) eq_refl)
(DSC 1282160 1%nat [Z_to_bv 8 128] ltac:(img_rd) eq_refl) (DSC 1282160 8%nat (word_to_le_bytes 8 (Z_to_bv 64 128)) ltac:(img_rd) eq_refl) (DSC 1282200 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1282208 8%nat (word_to_le_bytes 8 (Z_to_bv 64 144640)) ltac:(img_rd) eq_refl) (DSC 1282224 1%nat [Z_to_bv 8 128] ltac:(img_rd) eq_refl) (DSC 1282224 8%nat (word_to_le_bytes 8 (Z_to_bv 64 128)) ltac:(img_rd) eq_refl)
(DSC 1282264 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1282272 8%nat (word_to_le_bytes 8 (Z_to_bv 64 144768)) ltac:(img_rd) eq_refl) (DSC 1282288 1%nat [Z_to_bv 8 32] ltac:(img_rd) eq_refl) (DSC 1282288 8%nat (word_to_le_bytes 8 (Z_to_bv 64 32)) ltac:(img_rd) eq_refl) (DSC 1282328 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1282336 8%nat (word_to_le_bytes 8 (Z_to_bv 64 144800)) ltac:(img_rd) eq_refl)
(DSC 1282352 1%nat [Z_to_bv 8 96] ltac:(img_rd) eq_refl) (DSC 1282352 8%nat (word_to_le_bytes 8 (Z_to_bv 64 96)) ltac:(img_rd) eq_refl) (DSC 1282392 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1282400 8%nat (word_to_le_bytes 8 (Z_to_bv 64 144896)) ltac:(img_rd) eq_refl) (DSC 1282416 1%nat [Z_to_bv 8 128] ltac:(img_rd) eq_refl) (DSC 1282416 8%nat (word_to_le_bytes 8 (Z_to_bv 64 128)) ltac:(img_rd) eq_refl)
(DSC 1282456 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1282464 8%nat (word_to_le_bytes 8 (Z_to_bv 64 145024)) ltac:(img_rd) eq_refl) (DSC 1282480 1%nat [Z_to_bv 8 128] ltac:(img_rd) eq_refl) (DSC 1282480 8%nat (word_to_le_bytes 8 (Z_to_bv 64 128)) ltac:(img_rd) eq_refl) (DSC 1282520 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1282528 8%nat (word_to_le_bytes 8 (Z_to_bv 64 145152)) ltac:(img_rd) eq_refl)
(DSC 1282544 1%nat [Z_to_bv 8 96] ltac:(img_rd) eq_refl) (DSC 1282544 8%nat (word_to_le_bytes 8 (Z_to_bv 64 96)) ltac:(img_rd) eq_refl) (DSC 1282584 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1282592 8%nat (word_to_le_bytes 8 (Z_to_bv 64 145248)) ltac:(img_rd) eq_refl) (DSC 1282608 1%nat [Z_to_bv 8 96] ltac:(img_rd) eq_refl) (DSC 1282608 8%nat (word_to_le_bytes 8 (Z_to_bv 64 96)) ltac:(img_rd) eq_refl)
(DSC 1282648 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1282656 8%nat (word_to_le_bytes 8 (Z_to_bv 64 145344)) ltac:(img_rd) eq_refl) (DSC 1282672 1%nat [Z_to_bv 8 96] ltac:(img_rd) eq_refl) (DSC 1282672 8%nat (word_to_le_bytes 8 (Z_to_bv 64 96)) ltac:(img_rd) eq_refl) (DSC 1282712 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1282720 8%nat (word_to_le_bytes 8 (Z_to_bv 64 145440)) ltac:(img_rd) eq_refl)
(DSC 1282736 1%nat [Z_to_bv 8 128] ltac:(img_rd) eq_refl) (DSC 1282736 8%nat (word_to_le_bytes 8 (Z_to_bv 64 128)) ltac:(img_rd) eq_refl) (DSC 1282776 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1282784 8%nat (word_to_le_bytes 8 (Z_to_bv 64 145568)) ltac:(img_rd) eq_refl) (DSC 1282800 1%nat [Z_to_bv 8 64] ltac:(img_rd) eq_refl) (DSC 1282800 8%nat (word_to_le_bytes 8 (Z_to_bv 64 64)) ltac:(img_rd) eq_refl)
(DSC 1282840 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1282848 8%nat (word_to_le_bytes 8 (Z_to_bv 64 145632)) ltac:(img_rd) eq_refl) (DSC 1282864 1%nat [Z_to_bv 8 96] ltac:(img_rd) eq_refl) (DSC 1282864 8%nat (word_to_le_bytes 8 (Z_to_bv 64 96)) ltac:(img_rd) eq_refl) (DSC 1282904 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (XCC 8%nat 6886088 8 0 eq_refl)
(XCC 9%nat 1281648 8 1281416 eq_refl) (XCC 10%nat 1281556 4 4294967295 eq_refl) (XCC 11%nat 1281456 8 0 eq_refl) (XCC 12%nat 1281472 8 0 eq_refl) (XCC 13%nat 1281424 8 0 eq_refl) (XCC 14%nat 1281432 8 0 eq_refl)
(XCC 15%nat 1281408 8 1281176 eq_refl) SOlock SOwpos SOwbase SOwrite CANc
SOfd) as
(fx1 & R1 & MV1 & XGR & _ & XFRZ & XMS & _ & _ & Xr2 & _ & _ & _ & Xr8 & Xr9 & Xr10 & Xr11 & Xr12 & _ & _ & _ & _ & Xr17 & Xr18 & Xr19 & Xr21 & Xr22 & _ & Xm112 & Xm120 & Xm128 & Xm136 & Xm104 & Xm96 & Xm88 & Xm80 & Xm72 & Xm64 & Xm56 & Xm48 & Xm40 & Xm32 & Xm24 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _).
unfold V in XFRZ, XMS; cbn beta iota in XFRZ, XMS. cbn [V] in *.
pose proof (dinv_lzinv scfg L ar C IL HI HIok sp0 DL M0 _ _ _ _ _ _ D) as LZ. pose proof LZ as (HH & HL & HA & HM & Hh).
set (good := fun i : Z => i < 1282944 \/ 1286904 <= i < 6884112 \/ 6884136 <= i < 6884656 \/ 6884660 <= i < 2147450880).
assert (FRX : forall i, 0 <= i -> good i -> MV1 (Z_to_bv 64 i) = MV (Z_to_bv 64 i)).
{ intros i Hi Hg. apply XFRZ; [unfold good in Hg; clear - Hi Hg; lia | ..]; (intros X; unfold good in Hg; clear - Hsp' HS1 HS2 Hi Hg X; lia). }
apply (msteps_vis_fx scfg (ahid A model) A fx fx1 R (Z_to_bv 64 0x11575c) M R1 (Z_to_bv 64 0x11d13c) MV1 model _ LZ XMS).
intros M1 model1 MI1 SBM1 VIS1.
assert (LITX : forall a (n : nat) bs, rdn ASEGS MV (Z_to_bv 64 a) n = Some bs ->
(0 <=? a) && ((a + Z.of_nat n <=? 1282944) || ((1286904 <=? a) && (a + Z.of_nat n <=? 6884112)) || ((6884660 <=? a) && (a + Z.of_nat n <=? 2147450880))) = true ->
rdn ASEGS MV1 (Z_to_bv 64 a) n = Some bs).
{ intros a n bs Hr Hb. apply andb_prop in Hb as (B1 & B2). apply Z.leb_le in B1. rewrite !orb_true_iff, !andb_true_iff, !Z.leb_le in B2.
apply (rdn_tr MV MV1 a n bs Hr B1); [lia|]. intros i Hi. apply FRX; [lia|]. unfold good. clear - B1 B2 Hi. lia. }
assert (DATA : rdn ASEGS MV1 (Z_to_bv 64 6886112) (Z.to_nat (2 * 3)) = Some (zero_lines 3%nat)).
{ apply (LITX 6886112 (Z.to_nat (2 * 3))); [|reflexivity]. change (Z.to_nat (2 * 3)) with (2 * 3%nat)%nat.
destruct (BC 0 ltac:(lia)) as (B0a & B0b). destruct (BC 1 ltac:(lia)) as (B1a & B1b). destruct (BC 2 ltac:(lia)) as (B2a & B2b). cbn [zero_lines].
apply rdn_cons1; [lia | exact B0a|]. apply rdn_cons1; [lia | exact B0b|]. apply rdn_cons1; [lia | exact B1a|]. apply rdn_cons1; [lia | exact B1b|]. apply rdn_cons1; [lia | exact B2a|]. apply rdn_cons1; [lia | exact B2b|]. reflexivity. }
set (q := S - 136) in *.
assert (Hq : 0 <= q /\ q <= q + 32 /\ q + 32 + 16 <= 2 ^ 47) by (unfold q; clear - Hsp' HS1 HS2; lia).
assert (Hf : 0 <= 1281176 /\ (1281176 + 124 <= q \/ q + 32 + 16 <= 1281176 + 120) /\ 1281176 + 124 < 2 ^ 63) by (unfold q; clear - Hsp' HS1 HS2; lia).
assert (NLq : forall x, q <= x < q + 32 -> page_in_ranges (page_base_of x) (m_vm_lazy model) = false).
{ intros x Hx. apply (nl_pt scfg L ar C IL HI HIok sp0 Hsp DL M0 _ _ _ _ _ _ x D); unfold q in Hx; clear - Hsp' HS1 HS2 Hx; lia. }
assert (WIN1 : forall a n, usp - 8388608 <= a -> a + n <= usp -> forall d (k : nat), 0 <= d -> d + Z.of_nat k <= n -> store_ok ASEGS MV1 (Z_to_bv 64 (a + d)) k = true)
by (intros a n H1 H2 d k Hd Hk; apply (store_ok_mono ASEGS k MV MV1 _ XGR); apply (WIN a n); assumption).
unfold W. rewrite <- (app_nil_r (zero_lines 3%nat)).
apply (wv_loop scfg (ahid A model) A HH (m_vm_lazy model) HL HA 1281176 1 ltac:(lia) q (q + 32) Hq Hf NLq (t_exit (Z_to_bv 64 st) (m_fs model)) (t_exit_has_nil _ _)
(2 * 3%nat)%nat true R1 M1 model1 q 2 6886112 (2 * 3) 0 0 (zero_lines 3%nat) []).
{ cbn. lia. }
{ exact (sbm_lazy_eq _ _ SBM1). }
{ exact MI1. }
{ rewrite (sbm_halted_eq _ _ SBM1). exact Hh. }
{ rewrite (sbm_fds' _ _ SBM1). exact FD1. }
{ unfold wv_regs. repeat split; assumption. }
{ rewrite VIS1. unfold wv_iov. split; [lia|]. split; [lia|]. split; [right; reflexivity|].
split; [exact Xm136|]. split; [replace (q + 8) with (S - 128) by (unfold q; ring); exact Xm128|].
split; [replace (Z_to_bv 64 q) with (Z_to_bv 64 (q + 0)) by (f_equal; lia); apply (WIN1 q 32); [unfold q; clear - Hsp' HS1 HS2; lia | unfold q; clear - Hsp' HS1 HS2; lia | lia | cbn; lia]|].
split; [unfold wv_buf; split; [lia|]; split; [lia|]; split; [lia|]; split; [right; left; unfold q; clear - Hsp' HS1 HS2; lia|]; split; [exact DATA|];
intros x Hx; apply (nl_pt scfg L ar C IL HI HIok sp0 Hsp DL M0 _ _ _ _ _ _ x D); lia|].
split; [intros X; discriminate X|]. intros _.
split; [replace (q + 16) with (S - 120) by (unfold q; ring); exact Xm120|].
split; [replace (q + 24) with (S - 112) by (unfold q; ring); exact Xm112|].
split; [|lia].
unfold wv_buf. split; [lia|]. split; [lia|]. split; [lia|]. split; [left; reflexivity|]. split; [reflexivity|]. intros x Hx. lia. }
{ lia. }
{ rewrite VIS1. exact (LITX _ _ _ SOfd eq_refl). }
intros R3 M3 model3 MI3 SBM3 KR3 _ FRV3 _ GRV3. rewrite VIS1 in FRV3, GRV3.
set (MV3 := mrestrict (ahid A model) M3) in *.
assert (LIT3 : forall a (n : nat) bs, rdn ASEGS MV (Z_to_bv 64 a) n = Some bs ->
(0 <=? a) && ((a + Z.of_nat n <=? 1282944) || ((1286904 <=? a) && (a + Z.of_nat n <=? 6884112)) || ((6884660 <=? a) && (a + Z.of_nat n <=? 2147450880))) = true ->
rdn ASEGS MV3 (Z_to_bv 64 a) n = Some bs).
{ intros a n bs Hr Hb. pose proof (LITX a n bs Hr Hb) as Y. apply andb_prop in Hb as (B1 & B2). apply Z.leb_le in B1. rewrite !orb_true_iff, !andb_true_iff, !Z.leb_le in B2.
apply (rdn_tr MV1 MV3 a n bs Y B1); [lia|]. intros i Hi. apply FRV3; [lia|]. unfold q. clear - Hsp' HS1 HS2 B1 B2 Hi. lia. }
assert (cellS : forall off k (n : nat) bs, rdn ASEGS MV1 (Z_to_bv 64 (S - k)) n = Some bs ->
(off + k =? 144) && (Z.of_nat n <=? k) && (k <=? 104) = true -> rdn ASEGS MV3 (Z_to_bv 64 (S - 144 + off)) n = Some bs).
{ intros off k n bs Hr Hb. apply andb_prop in Hb as (Hb & Hb3). apply andb_prop in Hb as (Hb1 & Hb2).
apply Z.eqb_eq in Hb1. apply Z.leb_le in Hb2, Hb3. replace (S - 144 + off) with (S - k) by lia.
apply (rdn_tr MV1 MV3 _ _ _ Hr); [clear - Hsp' HS1 HS2 Hb3; lia | clear - Hsp' HS1 HS2 Hb2; lia|].
intros i Hi. apply FRV3; unfold q; clear - Hsp' HS1 HS2 Hb2 Hb3 Hi; lia. }
assert (WIN3 : forall a n, usp - 8388608 <= a -> a + n <= usp -> forall d (k : nat), 0 <= d -> d + Z.of_nat k <= n -> store_ok ASEGS MV3 (Z_to_bv 64 (a + d)) k = true)
by (intros a n H1 H2 d k Hd Hk; apply (store_ok_mono ASEGS k MV1 MV3 _ GRV3); apply (WIN1 a n); assumption).
assert (FW3 : forall a n, 1281176 <= a -> a + n <= 1281176 + 232 -> forall d (k : nat), 0 <= d -> d + Z.of_nat k <= n -> store_ok ASEGS MV3 (Z_to_bv 64 (a + d)) k = true)
by (intros a n H1 H2 d k Hd Hk; apply (store_ok_mono ASEGS k MV1 MV3 _ GRV3); apply (store_ok_mono ASEGS k MV MV1 _ XGR); apply (FW a n); assumption).
assert (IMG3 : forall i, 65536 <= i < 1269760 -> MV3 (Z_to_bv 64 i) = None).
{ intros i Hi. rewrite FRV3; [rewrite FRX; [apply IMGc; exact Hi | lia | unfold good; lia] | lia | unfold q; clear - Hsp' HS1 HS2 Hi; lia]. }
set (VD := fun n : nat => match n with
| 2%nat => S - 144 | 40%nat => canz
| 9%nat => bv_unsigned (getr R (Z_to_bv 5 (Z.of_nat 9))) | 10%nat => bv_unsigned (getr R (Z_to_bv 5 (Z.of_nat 10)))
| 18%nat => bv_unsigned (getr R (Z_to_bv 5 (Z.of_nat 18))) | 19%nat => bv_unsigned (getr R (Z_to_bv 5 (Z.of_nat 19)))
| 20%nat => bv_unsigned (getr R (Z_to_bv 5 (Z.of_nat 20))) | 21%nat => bv_unsigned (getr R (Z_to_bv 5 (Z.of_nat 21)))
| 22%nat => bv_unsigned (getr R (Z_to_bv 5 (Z.of_nat 22)))
| 110%nat => bv_unsigned (getr R3 (Z_to_bv 5 (Z.of_nat 10))) | 118%nat => bv_unsigned (getr R3 (Z_to_bv 5 (Z.of_nat 18)))
| 119%nat => bv_unsigned (getr R3 (Z_to_bv 5 (Z.of_nat 19))) | 120%nat => bv_unsigned (getr R3 (Z_to_bv 5 (Z.of_nat 20)))
| 122%nat => bv_unsigned (getr R3 (Z_to_bv 5 (Z.of_nat 22)))
| _ => 0 end).
assert (Dg2 : getr R3 (Z_to_bv 5 (Z.of_nat 2)) = Z_to_bv 64 (VD 2%nat)) by (eapply eq_trans; [exact (KR3 2%bv ltac:(unfold WV_KEEP; cbn [In]; tauto)) | exact Xr2]).
assert (Dg8 : getr R3 (Z_to_bv 5 (Z.of_nat 8)) = Z_to_bv 64 0) by (eapply eq_trans; [exact (KR3 8%bv ltac:(unfold WV_KEEP; cbn [In]; tauto)) | exact Xr8]).
assert (Dg9 : getr R3 (Z_to_bv 5 (Z.of_nat 9)) = Z_to_bv 64 1281176) by (eapply eq_trans; [exact (KR3 9%bv ltac:(unfold WV_KEEP; cbn [In]; tauto)) | exact Xr9]).
assert (Dg21 : getr R3 (Z_to_bv 5 (Z.of_nat 21)) = Z_to_bv 64 6884096) by (eapply eq_trans; [exact (KR3 21%bv ltac:(unfold WV_KEEP; cbn [In]; tauto)) | exact Xr21]).
assert (Dg10 : getr R3 (Z_to_bv 5 (Z.of_nat 10)) = Z_to_bv 64 (VD 110%nat)) by (cbn [VD]; symmetry; apply Z_to_bv_bv_unsigned).
assert (Dg18 : getr R3 (Z_to_bv 5 (Z.of_nat 18)) = Z_to_bv 64 (VD 118%nat)) by (cbn [VD]; symmetry; apply Z_to_bv_bv_unsigned).
assert (Dg19 : getr R3 (Z_to_bv 5 (Z.of_nat 19)) = Z_to_bv 64 (VD 119%nat)) by (cbn [VD]; symmetry; apply Z_to_bv_bv_unsigned).
assert (Dg20 : getr R3 (Z_to_bv 5 (Z.of_nat 20)) = Z_to_bv 64 (VD 120%nat)) by (cbn [VD]; symmetry; apply Z_to_bv_bv_unsigned).
assert (Dg22 : getr R3 (Z_to_bv 5 (Z.of_nat 22)) = Z_to_bv 64 (VD 122%nat)) by (cbn [VD]; symmetry; apply Z_to_bv_bv_unsigned).
assert (HD64 : 0 <= VD 2%nat < 2 ^ 64) by (cbn [VD]; clear - Hsp' HS1 HS2; lia).
assert (HDr : 140735332552704 <= VD 2%nat <= 140737488355328) by (cbn [VD]; clear - Hsp' HS1 HS2; lia).
assert (HDa : AS0DRVP_dpXd_4.aligned (VD 2%nat) 16).
{ cbn [VD]. unfold AS0DRVP_dpXd_4.aligned. clear - HS16. Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). lia.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false). }
assert (DWR : L5Defs.L5.writable ASEGS MV3 (VD 2%nat - 16) 16).
{ cbn [VD]. intros d k Hd Hk. apply (WIN3 (S - 144 - 16) 16); clear - Hsp' HS1 HS2 Hd Hk; lia. }
assert (DDF : L5Defs.L5.defined MV3 (VD 2%nat - 16) 16).
{ cbn [VD]. intros i Hi. apply (store_ok_defined sp0); [clear - Hsp' HS1 HS2 Hi; lia|]. apply (WIN3 (S - 144 - 16) 16); clear - Hsp' HS1 HS2 Hi; lia. }
destruct (AS0DRVP_dpXd_4.dpXd_4_conc fx1 R3 MV3 VD HD64 (u64_range _)
(u64_range _) (u64_range _) (u64_range _) (u64_range _) (u64_range _) (u64_range _)
Hcan (u64_range _) (u64_range _) (u64_range _) (u64_range _) (u64_range _)
Dg2 Dg8 Dg9 Dg10 Dg18 Dg19
Dg20 Dg21 Dg22 HDr HDa DWR
DDF IMG3 (fun d k Hd Hk => FW3 1281208 8 ltac:(lia) ltac:(lia) d k Hd Hk) (fun d k Hd Hk => FW3 1281216 8 ltac:(lia) ltac:(lia) d k Hd Hk) (fun d k Hd Hk => FW3 1281232 8 ltac:(lia) ltac:(lia) d k Hd Hk) (LIT3 1281264 8%nat _ SObuf eq_refl)
(LIT3 1281272 8%nat _ SObufsz eq_refl) (LIT3 6884096 8%nat _ CANc eq_refl) (cellS 40 104 _ _ Xm104 eq_refl) (cellS 104 40 _ _ Xm40 eq_refl) (cellS 96 48 _ _ Xm48 eq_refl) (cellS 88 56 _ _ Xm56 eq_refl)
(cellS 80 64 _ _ Xm64 eq_refl) (cellS 72 72 _ _ Xm72 eq_refl) (cellS 64 80 _ _ Xm80 eq_refl) (cellS 56 88 _ _ Xm88 eq_refl) (cellS 48 96 _ _ Xm96 eq_refl) (LIT3 1281184 8%nat _ SOrpos eq_refl)
(LIT3 1281192 8%nat _ SOrend eq_refl) (LIT3 1281168 8%nat _ (XCC 16%nat 1281168 8 1280936 eq_refl) eq_refl) (LIT3 1281076 4%nat _ (XCC 17%nat 1281076 4 4294967295 eq_refl) eq_refl) (LIT3 1280976 8%nat _ (XCC 18%nat 1280976 8 0 eq_refl) eq_refl) (LIT3 1280992 8%nat _ (XCC 19%nat 1280992 8 0 eq_refl) eq_refl) (LIT3 1280944 8%nat _ (XCC 20%nat 1280944 8 0 eq_refl) eq_refl)
(LIT3 1280952 8%nat _ (XCC 21%nat 1280952 8 0 eq_refl) eq_refl) (cellS 120 24 _ _ Xm24 eq_refl) (cellS 112 32 _ _ Xm32 eq_refl)) as
(fx2 & R4 & MV4 & _ & _ & _ & DMS & _ & _ & _ & _ & _ & Dr10 & _ & _ & Dr17 & _).
unfold VD in DMS; cbn beta iota in DMS.
assert (LZ3 : lzinv ASEGS (ahid A model) A model3).
{ apply (lzinv_sbm ASEGS (ahid A model) A model model3 LZ MI3). exact (same_but_materialized_trans _ _ _ SBM1 SBM3). }
apply (msteps_vis_fx scfg (ahid A model) A fx1 fx2 R3 (Z_to_bv 64 0x11d148) M3 R4 (Z_to_bv 64 0x11546c) MV4 model3 _ LZ3 DMS).
intros M5 model5 MI5 SBM5 _.
pose proof (same_but_materialized_trans _ _ _ (same_but_materialized_trans _ _ _ SBM1 SBM3) SBM5) as SBMT.
rewrite <- (proj2 (sbm_fds model model5 SBMT)).
apply (rz_exit_at_lit_lz ASEGS scfg R4 (Z_to_bv 64 0x11546c) M5 rom model5 ECALLW st fetch_exitA is_ecall_ECALLW).
- rewrite (sbm_halted_eq _ _ SBMT). exact Hh.
- left. exact Dr17.
- eapply eq_trans; [exact Dr10|]. cbn [VD]. rewrite Z_to_bv_bv_unsigned. exact G10.
- exact Hst.
Qed.
#[using="L C IL HIok ICok ILY Hsp DL Hex"] Lemma exit_run_0B : ltac2:(TCodec.tc2 tcn__Jb0DrvExit "SC'6'<'A%2211%411&Q?%611&Q='S9yR0%211'9y8%511%311p051'L&Q0y5%2219&QAr:r9r8r7r6r5r3r1%9887654321&Q:&Q>%1297%3219'?&R=zr4%3221&R?+X0%2241%8241'@&QL(S7+1(>%33N21%52I1&S8+QRclH%22Q;1%:3Q;41+2%:3Q518%<2Q11%72Q@Q1%?3Q@21+4%?3Q:1=%A2Q71+V^Rf0%=2QF1%E3QF31+:%E3Q@1C%G2Q>1%B2QKQ=%J3QK21&QG%12Q3Q>&QF%11QA'R5&R8vS4(I&QMvRKr=+QRejL%Q02R91r?&QO%11:%8576431r>%;221&R2r;%Q92RB1&O%116%5231%E4DC71p0G1p0J1p0M1p0Q31p0Q:1p0Q@1p0QL1tR:RHR61p0R;1pVFS71pV>S81pTDS91pR>RI1pV0RM1pR4RO1p2S;1pUFS91pQ<S;1pQ:S>1").
Proof.
intros LB LK cr A M model R S st tid (D & HS1 & HS2 & HS16 & WIN & IMGc & (XC & TIDC & HTr & DESC)) MV Hst G1 G2 G4 G10 SO SOX.
pose proof Hsp as Hsp'. destruct SO as (_ & _ & _ & SOwpos & SOwbase & SOlock & _). destruct SOX as (_ & _ & _ & SOrpos & SOrend).
set (V := fun n : nat => match n with 2%nat => S | 44%nat => tid | _ => 0 end).
assert (HS64 : 0 <= V 2%nat < 2 ^ 64) by (cbn [V]; clear - Hsp' HS1 HS2; lia).
assert (HT64 : 0 <= V 44%nat < 2 ^ 64) by (cbn [V]; clear - HTr; lia).
assert (HSr : 140735332552704 <= V 2%nat <= 140737488355328) by (cbn [V]; clear - Hsp' HS1 HS2; lia).
assert (HSa : AS0DRVP_dpXB.aligned (V 2%nat) 16) by (cbn [V]; exact HS16).
assert (CWR : L5Defs.L5.writable ASEGS MV (V 2%nat - 320) 320).
{ cbn [V]. intros d k Hd Hk. apply (WIN (S - 320) 320); clear - Hsp' HS1 HS2 Hd Hk; lia. }
assert (CDF : L5Defs.L5.defined MV (V 2%nat - 320) 320).
{ cbn [V]. intros i Hi. apply (store_ok_defined sp0); [clear - Hsp' HS1 HS2 Hi; lia|]. apply (WIN (S - 320) 320); clear - Hsp' HS1 HS2 Hi; lia. }
assert (WSG : forall a (n : nat), wseg_ok ASEGS (Z_to_bv 64 a) n = true -> (0 <=? a) && (a + Z.of_nat n <=? 2 ^ 63) = true -> L5Defs.L5.writable ASEGS MV a (Z.of_nat n)).
{ intros a n W Hb. apply andb_prop in Hb as (B1 & B2). apply Z.leb_le in B1, B2. exact (wsg_writable MV a n W B1 B2). }
assert (SHW : forall a n, ((2147468844 <=? a) && (a + n <=? 2147469096) || (2147611092 <=? a) && (a + n <=? 2147611248)) = true -> L5Defs.L5.writable ASEGS MV a n)
by (intros a n Hb; exact (sh_writable _ _ _ _ _ _ a n D Hb)).
assert (STC : forall (i : nat) a n v, nth_error EX_CELLS i = Some (a, n, v) -> rdn ASEGS MV (Z_to_bv 64 a) (Z.to_nat n) = Some (word_to_le_bytes (Z.to_nat n) (Z_to_bv 64 v)))
by (intros i a n v Hn; exact (ex_cell_vis _ _ _ _ _ _ a n v D (nth_error_In _ _ Hn))).
assert (STC1 : forall (i : nat) a v, nth_error EX_CELLS i = Some (a, 1, v) -> (0 <=? v) && (v <? 2 ^ 64) = true -> rdn ASEGS MV (Z_to_bv 64 a) 1 = Some [Z_to_bv 8 v]).
{ intros i a v Hn Hb. apply andb_prop in Hb as (B1 & B2). apply Z.leb_le in B1. apply Z.ltb_lt in B2. rewrite <- (ArtMem.art_bytes1 v (conj B1 B2)). exact (STC i a 1 v Hn). }
assert (XCC : forall (i : nat) a n v, nth_error XC_CELLS_B i = Some (a, n, v) -> rdn ASEGS MV (Z_to_bv 64 a) (Z.to_nat n) = Some (word_to_le_bytes (Z.to_nat n) (Z_to_bv 64 v)))
by (intros i a n v Hn; exact (cells_at_nth MV XC_CELLS_B i a n v XC Hn)).
assert (XCC1 : forall (i : nat) a v, nth_error XC_CELLS_B i = Some (a, 1, v) -> (0 <=? v) && (v <? 2 ^ 64) = true -> rdn ASEGS MV (Z_to_bv 64 a) 1 = Some [Z_to_bv 8 v]).
{ intros i a v Hn Hb. apply andb_prop in Hb as (B1 & B2). apply Z.leb_le in B1. apply Z.ltb_lt in B2. rewrite <- (ArtMem.art_bytes1 v (conj B1 B2)). exact (XCC i a 1 v Hn). }
assert (DSC : forall a (n : nat) bs, rdn ASEGS (fun _ => None) (Z_to_bv 64 a) n = Some bs -> (0x138ea0 <=? a) && (a + Z.of_nat n <=? 0x139380) = true -> rdn ASEGS MV (Z_to_bv 64 a) n = Some bs).
{ intros a n bs Hr Hb. apply andb_prop in Hb as (B1 & B2). apply Z.leb_le in B1, B2. apply (img_cell MV a n bs Hr); [lia | lia|]. intros i Hi. apply DESC. lia. }
destruct (AS0DRVP_dpXB.dpXB_conc fx R MV V HS64 HT64
G1 G2 G4 HSr HSa CWR
CDF IMGc (WSG 1282944 8%nat ltac:(vm_compute; reflexivity) eq_refl) (WSG 1283024 1%nat ltac:(vm_compute; reflexivity) eq_refl) (WSG 1286896 8%nat ltac:(vm_compute; reflexivity) eq_refl) (WSG 6884112 1%nat ltac:(vm_compute; reflexivity) eq_refl)
(WSG 6884120 4%nat ltac:(vm_compute; reflexivity) eq_refl) (WSG 6884128 8%nat ltac:(vm_compute; reflexivity) eq_refl) (WSG 6884656 4%nat ltac:(vm_compute; reflexivity) eq_refl) (SHW 2147468844 1 eq_refl) (SHW 2147468845 1 eq_refl) (SHW 2147468846 1 eq_refl)
(SHW 2147468847 1 eq_refl) (SHW 2147468856 1 eq_refl) (SHW 2147468857 1 eq_refl) (SHW 2147468858 1 eq_refl) (SHW 2147468859 1 eq_refl) (SHW 2147468860 1 eq_refl)
(SHW 2147468860 4 eq_refl) (SHW 2147468861 1 eq_refl) (SHW 2147468862 1 eq_refl) (SHW 2147468863 1 eq_refl) (SHW 2147468864 4 eq_refl) (SHW 2147468868 1 eq_refl)
(SHW 2147468868 4 eq_refl) (SHW 2147468869 1 eq_refl) (SHW 2147468870 1 eq_refl) (SHW 2147468871 1 eq_refl) (SHW 2147468916 1 eq_refl) (SHW 2147468917 1 eq_refl)
(SHW 2147468918 1 eq_refl) (SHW 2147468919 1 eq_refl) (SHW 2147468920 1 eq_refl) (SHW 2147468921 1 eq_refl) (SHW 2147468922 1 eq_refl) (SHW 2147468923 1 eq_refl)
(SHW 2147468924 1 eq_refl) (SHW 2147468925 1 eq_refl) (SHW 2147468926 1 eq_refl) (SHW 2147468927 1 eq_refl) (SHW 2147468928 1 eq_refl) (SHW 2147468929 1 eq_refl)
(SHW 2147468930 1 eq_refl) (SHW 2147468931 1 eq_refl) (SHW 2147468932 1 eq_refl) (SHW 2147468932 4 eq_refl) (SHW 2147468933 1 eq_refl) (SHW 2147468934 1 eq_refl)
(SHW 2147468935 1 eq_refl) (SHW 2147468936 4 eq_refl) (SHW 2147468940 1 eq_refl) (SHW 2147468940 4 eq_refl) (SHW 2147468941 1 eq_refl) (SHW 2147468942 1 eq_refl)
(SHW 2147468943 1 eq_refl) (SHW 2147468944 1 eq_refl) (SHW 2147468944 4 eq_refl) (SHW 2147468945 1 eq_refl) (SHW 2147468946 1 eq_refl) (SHW 2147468947 1 eq_refl)
(SHW 2147468948 4 eq_refl) (SHW 2147468952 4 eq_refl) (SHW 2147468956 1 eq_refl) (SHW 2147468956 4 eq_refl) (SHW 2147468957 1 eq_refl) (SHW 2147468958 1 eq_refl)
(SHW 2147468959 1 eq_refl) (SHW 2147468960 1 eq_refl) (SHW 2147468960 4 eq_refl) (SHW 2147468961 1 eq_refl) (SHW 2147468962 1 eq_refl) (SHW 2147468963 1 eq_refl)
(SHW 2147468964 4 eq_refl) (SHW 2147468968 4 eq_refl) (SHW 2147468972 1 eq_refl) (SHW 2147468972 4 eq_refl) (SHW 2147468973 1 eq_refl) (SHW 2147468974 1 eq_refl)
(SHW 2147468975 1 eq_refl) (SHW 2147468976 1 eq_refl) (SHW 2147468977 1 eq_refl) (SHW 2147468978 1 eq_refl) (SHW 2147468979 1 eq_refl) (SHW 2147468980 1 eq_refl)
(SHW 2147468980 4 eq_refl) (SHW 2147468981 1 eq_refl) (SHW 2147468982 1 eq_refl) (SHW 2147468983 1 eq_refl) (SHW 2147468984 4 eq_refl) (SHW 2147468988 1 eq_refl)
(SHW 2147468988 4 eq_refl) (SHW 2147468989 1 eq_refl) (SHW 2147468990 1 eq_refl) (SHW 2147468991 1 eq_refl) (SHW 2147468992 1 eq_refl) (SHW 2147468992 4 eq_refl)
(SHW 2147468993 1 eq_refl) (SHW 2147468994 1 eq_refl) (SHW 2147468995 1 eq_refl) (SHW 2147468996 4 eq_refl) (SHW 2147469000 4 eq_refl) (SHW 2147469004 1 eq_refl)
(SHW 2147469004 4 eq_refl) (SHW 2147469005 1 eq_refl) (SHW 2147469006 1 eq_refl) (SHW 2147469007 1 eq_refl) (SHW 2147469008 1 eq_refl) (SHW 2147469008 4 eq_refl)
(SHW 2147469009 1 eq_refl) (SHW 2147469010 1 eq_refl) (SHW 2147469011 1 eq_refl) (SHW 2147469012 4 eq_refl) (SHW 2147469016 4 eq_refl) (SHW 2147469020 1 eq_refl)
(SHW 2147469020 4 eq_refl) (SHW 2147469021 1 eq_refl) (SHW 2147469022 1 eq_refl) (SHW 2147469023 1 eq_refl) (SHW 2147469024 1 eq_refl) (SHW 2147469024 4 eq_refl)
(SHW 2147469025 1 eq_refl) (SHW 2147469026 1 eq_refl) (SHW 2147469027 1 eq_refl) (SHW 2147469028 4 eq_refl) (SHW 2147469032 1 eq_refl) (SHW 2147469032 4 eq_refl)
(SHW 2147469033 1 eq_refl) (SHW 2147469034 1 eq_refl) (SHW 2147469035 1 eq_refl) (SHW 2147469036 1 eq_refl) (SHW 2147469036 4 eq_refl) (SHW 2147469037 1 eq_refl)
(SHW 2147469038 1 eq_refl) (SHW 2147469039 1 eq_refl) (SHW 2147469040 4 eq_refl) (SHW 2147469044 1 eq_refl) (SHW 2147469044 4 eq_refl) (SHW 2147469045 1 eq_refl)
(SHW 2147469046 1 eq_refl) (SHW 2147469047 1 eq_refl) (SHW 2147469048 1 eq_refl) (SHW 2147469048 4 eq_refl) (SHW 2147469049 1 eq_refl) (SHW 2147469050 1 eq_refl)
(SHW 2147469051 1 eq_refl) (SHW 2147469052 4 eq_refl) (SHW 2147469056 1 eq_refl) (SHW 2147469056 4 eq_refl) (SHW 2147469057 1 eq_refl) (SHW 2147469058 1 eq_refl)
(SHW 2147469059 1 eq_refl) (SHW 2147469060 1 eq_refl) (SHW 2147469060 4 eq_refl) (SHW 2147469061 1 eq_refl) (SHW 2147469062 1 eq_refl) (SHW 2147469063 1 eq_refl)
(SHW 2147469064 4 eq_refl) (SHW 2147469068 4 eq_refl) (SHW 2147469072 1 eq_refl) (SHW 2147469072 4 eq_refl) (SHW 2147469073 1 eq_refl) (SHW 2147469074 1 eq_refl)
(SHW 2147469075 1 eq_refl) (SHW 2147469076 1 eq_refl) (SHW 2147469077 1 eq_refl) (SHW 2147469078 1 eq_refl) (SHW 2147469079 1 eq_refl) (SHW 2147469080 1 eq_refl)
(SHW 2147469081 1 eq_refl) (SHW 2147469082 1 eq_refl) (SHW 2147469083 1 eq_refl) (SHW 2147469084 1 eq_refl) (SHW 2147469084 4 eq_refl) (SHW 2147469085 1 eq_refl)
(SHW 2147469086 1 eq_refl) (SHW 2147469087 1 eq_refl) (SHW 2147469088 4 eq_refl) (SHW 2147469092 1 eq_refl) (SHW 2147469092 4 eq_refl) (SHW 2147469093 1 eq_refl)
(SHW 2147469094 1 eq_refl) (SHW 2147469095 1 eq_refl) (SHW 2147611092 1 eq_refl) (SHW 2147611092 4 eq_refl) (SHW 2147611093 1 eq_refl) (SHW 2147611094 1 eq_refl)
(SHW 2147611095 1 eq_refl) (SHW 2147611096 4 eq_refl) (SHW 2147611100 4 eq_refl) (SHW 2147611104 4 eq_refl) (SHW 2147611108 4 eq_refl) (SHW 2147611112 4 eq_refl)
(SHW 2147611116 4 eq_refl) (SHW 2147611120 8 eq_refl) (SHW 2147611128 8 eq_refl) (SHW 2147611136 8 eq_refl) (SHW 2147611144 8 eq_refl) (SHW 2147611152 8 eq_refl)
(SHW 2147611160 8 eq_refl) (SHW 2147611168 8 eq_refl) (SHW 2147611176 8 eq_refl) (SHW 2147611184 8 eq_refl) (SHW 2147611192 8 eq_refl) (SHW 2147611200 8 eq_refl)
(SHW 2147611208 8 eq_refl) (SHW 2147611216 4 eq_refl) (SHW 2147611220 4 eq_refl) (SHW 2147611224 4 eq_refl) (SHW 2147611228 4 eq_refl) (SHW 2147611232 4 eq_refl)
(SHW 2147611236 4 eq_refl) (SHW 2147611240 1 eq_refl) (SHW 2147611240 4 eq_refl) (SHW 2147611241 1 eq_refl) (SHW 2147611242 1 eq_refl) (SHW 2147611243 1 eq_refl)
TIDC HTr (XCC 0%nat 6884656 4 0 eq_refl) (XCC1 1%nat 6884691 0 eq_refl eq_refl) (XCC 2%nat 6884128 8 6884136 eq_refl) (XCC 3%nat 6884120 4 4 eq_refl)
(XCC 23%nat 6884168 8 447508 eq_refl) (XCC 25%nat 6884424 8 0 eq_refl) (XCC 6%nat 6884116 4 0 eq_refl) (STC1 11%nat 1286740 0 eq_refl eq_refl) (XCC 22%nat 6884160 8 860168 eq_refl) (XCC 24%nat 6884416 8 1280728 eq_refl)
(XCC 27%nat 6884152 8 1136392 eq_refl) (XCC 28%nat 6884408 8 686244 eq_refl) (XCC1 26%nat 6746260 0 eq_refl eq_refl) (XCC 4%nat 6884144 8 1136392 eq_refl) (XCC 5%nat 6884400 8 618204 eq_refl) (STC1 10%nat 1894624 0 eq_refl eq_refl)
(XCC 7%nat 6884136 8 0 eq_refl) (STC1 3%nat 1283024 0 eq_refl eq_refl) (STC 0%nat 1270192 8 1270192 eq_refl) (STC 2%nat 1282944 8 1 eq_refl) (STC 4%nat 1286736 4 1 eq_refl) (STC 5%nat 1286896 8 0 eq_refl)
(STC1 8%nat 1300248 1 eq_refl eq_refl) (STC 7%nat 1296952 8 2147450880 eq_refl) (DSC 1281696 8%nat (word_to_le_bytes 8 (Z_to_bv 64 143712)) ltac:(img_rd) eq_refl) (DSC 1281712 1%nat [Z_to_bv 8 32] ltac:(img_rd) eq_refl) (STC1 6%nat 1295004 1 eq_refl eq_refl) (DSC 1281712 8%nat (word_to_le_bytes 8 (Z_to_bv 64 32)) ltac:(img_rd) eq_refl)
(STC 9%nat 1893856 8 18446744073709551615 eq_refl) (STC 1%nat 1270704 8 1207272 eq_refl) (DSC 1281752 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1281760 8%nat (word_to_le_bytes 8 (Z_to_bv 64 143808)) ltac:(img_rd) eq_refl) (DSC 1281776 1%nat [Z_to_bv 8 32] ltac:(img_rd) eq_refl) (DSC 1281776 8%nat (word_to_le_bytes 8 (Z_to_bv 64 32)) ltac:(img_rd) eq_refl)
(DSC 1281816 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1281824 8%nat (word_to_le_bytes 8 (Z_to_bv 64 143840)) ltac:(img_rd) eq_refl) (DSC 1281840 1%nat [Z_to_bv 8 96] ltac:(img_rd) eq_refl) (DSC 1281840 8%nat (word_to_le_bytes 8 (Z_to_bv 64 96)) ltac:(img_rd) eq_refl) (DSC 1281880 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1281888 8%nat (word_to_le_bytes 8 (Z_to_bv 64 144288)) ltac:(img_rd) eq_refl)
(DSC 1281904 1%nat [Z_to_bv 8 32] ltac:(img_rd) eq_refl) (DSC 1281904 8%nat (word_to_le_bytes 8 (Z_to_bv 64 32)) ltac:(img_rd) eq_refl) (DSC 1281944 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1281952 8%nat (word_to_le_bytes 8 (Z_to_bv 64 144320)) ltac:(img_rd) eq_refl) (DSC 1281968 1%nat [Z_to_bv 8 64] ltac:(img_rd) eq_refl) (DSC 1281968 8%nat (word_to_le_bytes 8 (Z_to_bv 64 64)) ltac:(img_rd) eq_refl)
(DSC 1282008 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1282016 8%nat (word_to_le_bytes 8 (Z_to_bv 64 144384)) ltac:(img_rd) eq_refl) (DSC 1282032 1%nat [Z_to_bv 8 32] ltac:(img_rd) eq_refl) (DSC 1282032 8%nat (word_to_le_bytes 8 (Z_to_bv 64 32)) ltac:(img_rd) eq_refl) (DSC 1282072 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1282080 8%nat (word_to_le_bytes 8 (Z_to_bv 64 144416)) ltac:(img_rd) eq_refl)
(DSC 1282096 1%nat [Z_to_bv 8 96] ltac:(img_rd) eq_refl) (DSC 1282096 8%nat (word_to_le_bytes 8 (Z_to_bv 64 96)) ltac:(img_rd) eq_refl) (DSC 1282136 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1282144 8%nat (word_to_le_bytes 8 (Z_to_bv 64 144512)) ltac:(img_rd) eq_refl) (DSC 1282160 1%nat [Z_to_bv 8 128] ltac:(img_rd) eq_refl) (DSC 1282160 8%nat (word_to_le_bytes 8 (Z_to_bv 64 128)) ltac:(img_rd) eq_refl)
(DSC 1282200 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1282208 8%nat (word_to_le_bytes 8 (Z_to_bv 64 144640)) ltac:(img_rd) eq_refl) (DSC 1282224 1%nat [Z_to_bv 8 128] ltac:(img_rd) eq_refl) (DSC 1282224 8%nat (word_to_le_bytes 8 (Z_to_bv 64 128)) ltac:(img_rd) eq_refl) (DSC 1282264 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1282272 8%nat (word_to_le_bytes 8 (Z_to_bv 64 144768)) ltac:(img_rd) eq_refl)
(DSC 1282288 1%nat [Z_to_bv 8 32] ltac:(img_rd) eq_refl) (DSC 1282288 8%nat (word_to_le_bytes 8 (Z_to_bv 64 32)) ltac:(img_rd) eq_refl) (DSC 1282328 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1282336 8%nat (word_to_le_bytes 8 (Z_to_bv 64 144800)) ltac:(img_rd) eq_refl) (DSC 1282352 1%nat [Z_to_bv 8 96] ltac:(img_rd) eq_refl) (DSC 1282352 8%nat (word_to_le_bytes 8 (Z_to_bv 64 96)) ltac:(img_rd) eq_refl)
(DSC 1282392 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1282400 8%nat (word_to_le_bytes 8 (Z_to_bv 64 144896)) ltac:(img_rd) eq_refl) (DSC 1282416 1%nat [Z_to_bv 8 128] ltac:(img_rd) eq_refl) (DSC 1282416 8%nat (word_to_le_bytes 8 (Z_to_bv 64 128)) ltac:(img_rd) eq_refl) (DSC 1282456 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1282464 8%nat (word_to_le_bytes 8 (Z_to_bv 64 145024)) ltac:(img_rd) eq_refl)
(DSC 1282480 1%nat [Z_to_bv 8 128] ltac:(img_rd) eq_refl) (DSC 1282480 8%nat (word_to_le_bytes 8 (Z_to_bv 64 128)) ltac:(img_rd) eq_refl) (DSC 1282520 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1282528 8%nat (word_to_le_bytes 8 (Z_to_bv 64 145152)) ltac:(img_rd) eq_refl) (DSC 1282544 1%nat [Z_to_bv 8 96] ltac:(img_rd) eq_refl) (DSC 1282544 8%nat (word_to_le_bytes 8 (Z_to_bv 64 96)) ltac:(img_rd) eq_refl)
(DSC 1282584 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1282592 8%nat (word_to_le_bytes 8 (Z_to_bv 64 145248)) ltac:(img_rd) eq_refl) (DSC 1282608 1%nat [Z_to_bv 8 96] ltac:(img_rd) eq_refl) (DSC 1282608 8%nat (word_to_le_bytes 8 (Z_to_bv 64 96)) ltac:(img_rd) eq_refl) (DSC 1282648 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1282656 8%nat (word_to_le_bytes 8 (Z_to_bv 64 145344)) ltac:(img_rd) eq_refl)
(DSC 1282672 1%nat [Z_to_bv 8 96] ltac:(img_rd) eq_refl) (DSC 1282672 8%nat (word_to_le_bytes 8 (Z_to_bv 64 96)) ltac:(img_rd) eq_refl) (DSC 1282712 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1282720 8%nat (word_to_le_bytes 8 (Z_to_bv 64 145440)) ltac:(img_rd) eq_refl) (DSC 1282736 1%nat [Z_to_bv 8 128] ltac:(img_rd) eq_refl) (DSC 1282736 8%nat (word_to_le_bytes 8 (Z_to_bv 64 128)) ltac:(img_rd) eq_refl)
(DSC 1282776 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1282784 8%nat (word_to_le_bytes 8 (Z_to_bv 64 145568)) ltac:(img_rd) eq_refl) (DSC 1282800 1%nat [Z_to_bv 8 64] ltac:(img_rd) eq_refl) (DSC 1282800 8%nat (word_to_le_bytes 8 (Z_to_bv 64 64)) ltac:(img_rd) eq_refl) (DSC 1282840 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1282848 8%nat (word_to_le_bytes 8 (Z_to_bv 64 145632)) ltac:(img_rd) eq_refl)
(DSC 1282864 1%nat [Z_to_bv 8 96] ltac:(img_rd) eq_refl) (DSC 1282864 8%nat (word_to_le_bytes 8 (Z_to_bv 64 96)) ltac:(img_rd) eq_refl) (DSC 1282904 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (XCC 8%nat 6886088 8 0 eq_refl) (XCC 9%nat 1281648 8 1281416 eq_refl) (XCC 10%nat 1281556 4 4294967295 eq_refl)
(XCC 11%nat 1281456 8 0 eq_refl) (XCC 12%nat 1281472 8 0 eq_refl) (XCC 13%nat 1281424 8 0 eq_refl) (XCC 14%nat 1281432 8 0 eq_refl) (XCC 15%nat 1281408 8 1281176 eq_refl) SOlock
SOwpos SOwbase SOrpos SOrend (XCC 16%nat 1281168 8 1280936 eq_refl) (XCC 17%nat 1281076 4 4294967295 eq_refl)
(XCC 18%nat 1280976 8 0 eq_refl) (XCC 19%nat 1280992 8 0 eq_refl) (XCC 20%nat 1280944 8 0 eq_refl) (XCC 21%nat 1280952 8 0 eq_refl)) as
(fx1 & R1 & MV1 & XGR & _ & _ & XMS & XKS & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Xr17 & _).
unfold V in XMS; cbn beta iota in XMS.
pose proof (dinv_lzinv scfg L ar C IL HI HIok sp0 DL M0 _ _ _ _ _ _ D) as LZ. pose proof LZ as (_ & _ & _ & _ & Hh).
apply (msteps_vis_fx scfg (ahid A model) A fx fx1 R (Z_to_bv 64 0x11575c) M R1 (Z_to_bv 64 0x11546c) MV1 model _ LZ XMS).
intros M' model' MI' SBM' _.
rewrite <- (proj2 (sbm_fds model model' SBM')).
apply (rz_exit_at_lit_lz ASEGS scfg R1 (Z_to_bv 64 0x11546c) M' rom model' ECALLW st fetch_exitA is_ecall_ECALLW).
- rewrite (sbm_halted_eq _ _ SBM'). exact Hh.
- left. exact Xr17.
- eapply eq_trans; [exact (XKS 10%nat ltac:(unfold AS0DRVP_dpXB.KS_dpXB; cbn [In]; repeat first [left; reflexivity | right]))|]. exact G10.
- exact Hst.
Qed.
#[using="L C IL HIok ICok ILY Hsp DL Hex"] Lemma exit_run_2B : ltac2:(TCodec.tc2 tcn__Jb0DrvExit "TL'6'<'A%2211%411&Q?%611&Q='S9yR0%211'9y8%511%311p051'L&Q0y5%2219&QAr;r:r9r8r7r6r4r2%9887654321&Q:&Q>%1297%3219'?&R=zr5%3221&R?+X0%2241%8241%827@&RA+2+R0%3221%92E1%?261'@&QL(S7+1(>%33Q521%52Q11&S8+QRclH%22QB1%:3QB41%93Q;@7%;2Q81%62QFQ8%>3QF21+4%>3Q@1<%@2Q>1+V^Rf0%<2QL1%D3QL31r<+:%E3QG1C%G231%B2R2QE%J3R221%R=1R0%R311&QN&R8+VbRh0%I2R91u8%544QK21(2&G%124H%32;1%Q73;51&QG%12Q6R3&QF%11R6'K%RD11&M&NrA%211%Q;2RKQ?%5221(J%113%C2:1%QG3:41'R5vS4(I&QMvRK+QRejL%QG2S71rC&QO%11Q3%756B431rB%:221&R1&R3&R4u1%211%42R71&R2r?%R62SF1&O%11<%5231%<271%J4QDI>1p0L1p0Q91p0Q<1p0Q?1p0QM1p0R41p0R;1p0R@1p0RL1p0S41tR:T0S>1p0SC1pUDT?1pVFT@1pV>TA1pTDTB1pR>T21pV0T61pR4T81p2TD1pUFTB1pQ<TD1pQ:TG1").
Proof.
intros LB LK cr A M model R S st tid canz (D & HS1 & HS2 & HS16 & WIN & IMGc & (XC & TIDC & HTr & DESC)) MV Hst Hcan G1 G2 G4 G10 CANc SO SOX FD1.
pose proof Hsp as Hsp'. destruct SO as (_ & SObufsz & _ & SOwpos & SOwbase & SOlock & _ & FW & BW & BC). destruct SOX as (SOwrite & SOfd & SObuf & SOrpos & SOrend).
set (V := fun n : nat => match n with 2%nat => S | 44%nat => tid | 40%nat => canz | _ => 0 end).
assert (HS64 : 0 <= V 2%nat < 2 ^ 64) by (cbn [V]; clear - Hsp' HS1 HS2; lia).
assert (HT64 : 0 <= V 44%nat < 2 ^ 64) by (cbn [V]; clear - HTr; lia).
assert (HSr : 140735332552704 <= V 2%nat <= 140737488355328) by (cbn [V]; clear - Hsp' HS1 HS2; lia).
assert (HSa : AS0DRVP_dpX2B_pre.aligned (V 2%nat) 16) by (cbn [V]; exact HS16).
assert (CWR : L5Defs.L5.writable ASEGS MV (V 2%nat - 320) 320).
{ cbn [V]. intros d k Hd Hk. apply (WIN (S - 320) 320); clear - Hsp' HS1 HS2 Hd Hk; lia. }
assert (CDF : L5Defs.L5.defined MV (V 2%nat - 320) 320).
{ cbn [V]. intros i Hi. apply (store_ok_defined sp0); [clear - Hsp' HS1 HS2 Hi; lia|]. apply (WIN (S - 320) 320); clear - Hsp' HS1 HS2 Hi; lia. }
assert (WSG : forall a (n : nat), wseg_ok ASEGS (Z_to_bv 64 a) n = true -> (0 <=? a) && (a + Z.of_nat n <=? 2 ^ 63) = true -> L5Defs.L5.writable ASEGS MV a (Z.of_nat n)).
{ intros a n W Hb. apply andb_prop in Hb as (B1 & B2). apply Z.leb_le in B1, B2. exact (wsg_writable MV a n W B1 B2). }
assert (SHW : forall a n, ((2147468844 <=? a) && (a + n <=? 2147469096) || (2147611092 <=? a) && (a + n <=? 2147611248)) = true -> L5Defs.L5.writable ASEGS MV a n)
by (intros a n Hb; exact (sh_writable _ _ _ _ _ _ a n D Hb)).
assert (STC : forall (i : nat) a n v, nth_error EX_CELLS i = Some (a, n, v) -> rdn ASEGS MV (Z_to_bv 64 a) (Z.to_nat n) = Some (word_to_le_bytes (Z.to_nat n) (Z_to_bv 64 v)))
by (intros i a n v Hn; exact (ex_cell_vis _ _ _ _ _ _ a n v D (nth_error_In _ _ Hn))).
assert (STC1 : forall (i : nat) a v, nth_error EX_CELLS i = Some (a, 1, v) -> (0 <=? v) && (v <? 2 ^ 64) = true -> rdn ASEGS MV (Z_to_bv 64 a) 1 = Some [Z_to_bv 8 v]).
{ intros i a v Hn Hb. apply andb_prop in Hb as (B1 & B2). apply Z.leb_le in B1. apply Z.ltb_lt in B2. rewrite <- (ArtMem.art_bytes1 v (conj B1 B2)). exact (STC i a 1 v Hn). }
assert (XCC : forall (i : nat) a n v, nth_error XC_CELLS_B i = Some (a, n, v) -> rdn ASEGS MV (Z_to_bv 64 a) (Z.to_nat n) = Some (word_to_le_bytes (Z.to_nat n) (Z_to_bv 64 v)))
by (intros i a n v Hn; exact (cells_at_nth MV XC_CELLS_B i a n v XC Hn)).
assert (XCC1 : forall (i : nat) a v, nth_error XC_CELLS_B i = Some (a, 1, v) -> (0 <=? v) && (v <? 2 ^ 64) = true -> rdn ASEGS MV (Z_to_bv 64 a) 1 = Some [Z_to_bv 8 v]).
{ intros i a v Hn Hb. apply andb_prop in Hb as (B1 & B2). apply Z.leb_le in B1. apply Z.ltb_lt in B2. rewrite <- (ArtMem.art_bytes1 v (conj B1 B2)). exact (XCC i a 1 v Hn). }
assert (DSC : forall a (n : nat) bs, rdn ASEGS (fun _ => None) (Z_to_bv 64 a) n = Some bs -> (0x138ea0 <=? a) && (a + Z.of_nat n <=? 0x139380) = true -> rdn ASEGS MV (Z_to_bv 64 a) n = Some bs).
{ intros a n bs Hr Hb. apply andb_prop in Hb as (B1 & B2). apply Z.leb_le in B1, B2. apply (img_cell MV a n bs Hr); [lia | lia|]. intros i Hi. apply DESC. lia. }
destruct (AS0DRVP_dpX2B_pre.dpX2B_pre_conc fx R MV V HS64 Hcan
HT64 G1 G2 G4 HSr HSa
CWR CDF IMGc (WSG 1282944 8%nat ltac:(vm_compute; reflexivity) eq_refl) (WSG 1283024 1%nat ltac:(vm_compute; reflexivity) eq_refl) (WSG 1286896 8%nat ltac:(vm_compute; reflexivity) eq_refl)
(WSG 6884112 1%nat ltac:(vm_compute; reflexivity) eq_refl) (WSG 6884120 4%nat ltac:(vm_compute; reflexivity) eq_refl) (WSG 6884128 8%nat ltac:(vm_compute; reflexivity) eq_refl) (WSG 6884656 4%nat ltac:(vm_compute; reflexivity) eq_refl) (SHW 2147468844 1 eq_refl) (SHW 2147468845 1 eq_refl)
(SHW 2147468846 1 eq_refl) (SHW 2147468847 1 eq_refl) (SHW 2147468856 1 eq_refl) (SHW 2147468857 1 eq_refl) (SHW 2147468858 1 eq_refl) (SHW 2147468859 1 eq_refl)
(SHW 2147468860 1 eq_refl) (SHW 2147468860 4 eq_refl) (SHW 2147468861 1 eq_refl) (SHW 2147468862 1 eq_refl) (SHW 2147468863 1 eq_refl) (SHW 2147468864 4 eq_refl)
(SHW 2147468868 1 eq_refl) (SHW 2147468868 4 eq_refl) (SHW 2147468869 1 eq_refl) (SHW 2147468870 1 eq_refl) (SHW 2147468871 1 eq_refl) (SHW 2147468916 1 eq_refl)
(SHW 2147468917 1 eq_refl) (SHW 2147468918 1 eq_refl) (SHW 2147468919 1 eq_refl) (SHW 2147468920 1 eq_refl) (SHW 2147468921 1 eq_refl) (SHW 2147468922 1 eq_refl)
(SHW 2147468923 1 eq_refl) (SHW 2147468924 1 eq_refl) (SHW 2147468925 1 eq_refl) (SHW 2147468926 1 eq_refl) (SHW 2147468927 1 eq_refl) (SHW 2147468928 1 eq_refl)
(SHW 2147468929 1 eq_refl) (SHW 2147468930 1 eq_refl) (SHW 2147468931 1 eq_refl) (SHW 2147468932 1 eq_refl) (SHW 2147468932 4 eq_refl) (SHW 2147468933 1 eq_refl)
(SHW 2147468934 1 eq_refl) (SHW 2147468935 1 eq_refl) (SHW 2147468936 4 eq_refl) (SHW 2147468940 1 eq_refl) (SHW 2147468940 4 eq_refl) (SHW 2147468941 1 eq_refl)
(SHW 2147468942 1 eq_refl) (SHW 2147468943 1 eq_refl) (SHW 2147468944 1 eq_refl) (SHW 2147468944 4 eq_refl) (SHW 2147468945 1 eq_refl) (SHW 2147468946 1 eq_refl)
(SHW 2147468947 1 eq_refl) (SHW 2147468948 4 eq_refl) (SHW 2147468952 4 eq_refl) (SHW 2147468956 1 eq_refl) (SHW 2147468956 4 eq_refl) (SHW 2147468957 1 eq_refl)
(SHW 2147468958 1 eq_refl) (SHW 2147468959 1 eq_refl) (SHW 2147468960 1 eq_refl) (SHW 2147468960 4 eq_refl) (SHW 2147468961 1 eq_refl) (SHW 2147468962 1 eq_refl)
(SHW 2147468963 1 eq_refl) (SHW 2147468964 4 eq_refl) (SHW 2147468968 4 eq_refl) (SHW 2147468972 1 eq_refl) (SHW 2147468972 4 eq_refl) (SHW 2147468973 1 eq_refl)
(SHW 2147468974 1 eq_refl) (SHW 2147468975 1 eq_refl) (SHW 2147468976 1 eq_refl) (SHW 2147468977 1 eq_refl) (SHW 2147468978 1 eq_refl) (SHW 2147468979 1 eq_refl)
(SHW 2147468980 1 eq_refl) (SHW 2147468980 4 eq_refl) (SHW 2147468981 1 eq_refl) (SHW 2147468982 1 eq_refl) (SHW 2147468983 1 eq_refl) (SHW 2147468984 4 eq_refl)
(SHW 2147468988 1 eq_refl) (SHW 2147468988 4 eq_refl) (SHW 2147468989 1 eq_refl) (SHW 2147468990 1 eq_refl) (SHW 2147468991 1 eq_refl) (SHW 2147468992 1 eq_refl)
(SHW 2147468992 4 eq_refl) (SHW 2147468993 1 eq_refl) (SHW 2147468994 1 eq_refl) (SHW 2147468995 1 eq_refl) (SHW 2147468996 4 eq_refl) (SHW 2147469000 4 eq_refl)
(SHW 2147469004 1 eq_refl) (SHW 2147469004 4 eq_refl) (SHW 2147469005 1 eq_refl) (SHW 2147469006 1 eq_refl) (SHW 2147469007 1 eq_refl) (SHW 2147469008 1 eq_refl)
(SHW 2147469008 4 eq_refl) (SHW 2147469009 1 eq_refl) (SHW 2147469010 1 eq_refl) (SHW 2147469011 1 eq_refl) (SHW 2147469012 4 eq_refl) (SHW 2147469016 4 eq_refl)
(SHW 2147469020 1 eq_refl) (SHW 2147469020 4 eq_refl) (SHW 2147469021 1 eq_refl) (SHW 2147469022 1 eq_refl) (SHW 2147469023 1 eq_refl) (SHW 2147469024 1 eq_refl)
(SHW 2147469024 4 eq_refl) (SHW 2147469025 1 eq_refl) (SHW 2147469026 1 eq_refl) (SHW 2147469027 1 eq_refl) (SHW 2147469028 4 eq_refl) (SHW 2147469032 1 eq_refl)
(SHW 2147469032 4 eq_refl) (SHW 2147469033 1 eq_refl) (SHW 2147469034 1 eq_refl) (SHW 2147469035 1 eq_refl) (SHW 2147469036 1 eq_refl) (SHW 2147469036 4 eq_refl)
(SHW 2147469037 1 eq_refl) (SHW 2147469038 1 eq_refl) (SHW 2147469039 1 eq_refl) (SHW 2147469040 4 eq_refl) (SHW 2147469044 1 eq_refl) (SHW 2147469044 4 eq_refl)
(SHW 2147469045 1 eq_refl) (SHW 2147469046 1 eq_refl) (SHW 2147469047 1 eq_refl) (SHW 2147469048 1 eq_refl) (SHW 2147469048 4 eq_refl) (SHW 2147469049 1 eq_refl)
(SHW 2147469050 1 eq_refl) (SHW 2147469051 1 eq_refl) (SHW 2147469052 4 eq_refl) (SHW 2147469056 1 eq_refl) (SHW 2147469056 4 eq_refl) (SHW 2147469057 1 eq_refl)
(SHW 2147469058 1 eq_refl) (SHW 2147469059 1 eq_refl) (SHW 2147469060 1 eq_refl) (SHW 2147469060 4 eq_refl) (SHW 2147469061 1 eq_refl) (SHW 2147469062 1 eq_refl)
(SHW 2147469063 1 eq_refl) (SHW 2147469064 4 eq_refl) (SHW 2147469068 4 eq_refl) (SHW 2147469072 1 eq_refl) (SHW 2147469072 4 eq_refl) (SHW 2147469073 1 eq_refl)
(SHW 2147469074 1 eq_refl) (SHW 2147469075 1 eq_refl) (SHW 2147469076 1 eq_refl) (SHW 2147469077 1 eq_refl) (SHW 2147469078 1 eq_refl) (SHW 2147469079 1 eq_refl)
(SHW 2147469080 1 eq_refl) (SHW 2147469081 1 eq_refl) (SHW 2147469082 1 eq_refl) (SHW 2147469083 1 eq_refl) (SHW 2147469084 1 eq_refl) (SHW 2147469084 4 eq_refl)
(SHW 2147469085 1 eq_refl) (SHW 2147469086 1 eq_refl) (SHW 2147469087 1 eq_refl) (SHW 2147469088 4 eq_refl) (SHW 2147469092 1 eq_refl) (SHW 2147469092 4 eq_refl)
(SHW 2147469093 1 eq_refl) (SHW 2147469094 1 eq_refl) (SHW 2147469095 1 eq_refl) (SHW 2147611092 1 eq_refl) (SHW 2147611092 4 eq_refl) (SHW 2147611093 1 eq_refl)
(SHW 2147611094 1 eq_refl) (SHW 2147611095 1 eq_refl) (SHW 2147611096 4 eq_refl) (SHW 2147611100 4 eq_refl) (SHW 2147611104 4 eq_refl) (SHW 2147611108 4 eq_refl)
(SHW 2147611112 4 eq_refl) (SHW 2147611116 4 eq_refl) (SHW 2147611120 8 eq_refl) (SHW 2147611128 8 eq_refl) (SHW 2147611136 8 eq_refl) (SHW 2147611144 8 eq_refl)
(SHW 2147611152 8 eq_refl) (SHW 2147611160 8 eq_refl) (SHW 2147611168 8 eq_refl) (SHW 2147611176 8 eq_refl) (SHW 2147611184 8 eq_refl) (SHW 2147611192 8 eq_refl)
(SHW 2147611200 8 eq_refl) (SHW 2147611208 8 eq_refl) (SHW 2147611216 4 eq_refl) (SHW 2147611220 4 eq_refl) (SHW 2147611224 4 eq_refl) (SHW 2147611228 4 eq_refl)
(SHW 2147611232 4 eq_refl) (SHW 2147611236 4 eq_refl) (SHW 2147611240 1 eq_refl) (SHW 2147611240 4 eq_refl) (SHW 2147611241 1 eq_refl) (SHW 2147611242 1 eq_refl)
(SHW 2147611243 1 eq_refl) TIDC HTr (XCC 0%nat 6884656 4 0 eq_refl) (XCC1 1%nat 6884691 0 eq_refl eq_refl) (XCC 2%nat 6884128 8 6884136 eq_refl)
(XCC 3%nat 6884120 4 4 eq_refl) (XCC 23%nat 6884168 8 447508 eq_refl) (XCC 25%nat 6884424 8 0 eq_refl) (XCC 6%nat 6884116 4 0 eq_refl) (STC1 11%nat 1286740 0 eq_refl eq_refl) (XCC 22%nat 6884160 8 860168 eq_refl)
(XCC 24%nat 6884416 8 1280728 eq_refl) (XCC 27%nat 6884152 8 1136392 eq_refl) (XCC 28%nat 6884408 8 686244 eq_refl) (XCC1 26%nat 6746260 0 eq_refl eq_refl) (XCC 4%nat 6884144 8 1136392 eq_refl) (XCC 5%nat 6884400 8 618204 eq_refl)
(STC1 10%nat 1894624 0 eq_refl eq_refl) (XCC 7%nat 6884136 8 0 eq_refl) (STC1 3%nat 1283024 0 eq_refl eq_refl) (STC 0%nat 1270192 8 1270192 eq_refl) (STC 2%nat 1282944 8 1 eq_refl) (STC 4%nat 1286736 4 1 eq_refl)
(STC 5%nat 1286896 8 0 eq_refl) (STC1 8%nat 1300248 1 eq_refl eq_refl) (STC 7%nat 1296952 8 2147450880 eq_refl) (DSC 1281696 8%nat (word_to_le_bytes 8 (Z_to_bv 64 143712)) ltac:(img_rd) eq_refl) (DSC 1281712 1%nat [Z_to_bv 8 32] ltac:(img_rd) eq_refl) (STC1 6%nat 1295004 1 eq_refl eq_refl)
(DSC 1281712 8%nat (word_to_le_bytes 8 (Z_to_bv 64 32)) ltac:(img_rd) eq_refl) (STC 9%nat 1893856 8 18446744073709551615 eq_refl) (STC 1%nat 1270704 8 1207272 eq_refl) (DSC 1281752 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1281760 8%nat (word_to_le_bytes 8 (Z_to_bv 64 143808)) ltac:(img_rd) eq_refl) (DSC 1281776 1%nat [Z_to_bv 8 32] ltac:(img_rd) eq_refl)
(DSC 1281776 8%nat (word_to_le_bytes 8 (Z_to_bv 64 32)) ltac:(img_rd) eq_refl) (DSC 1281816 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1281824 8%nat (word_to_le_bytes 8 (Z_to_bv 64 143840)) ltac:(img_rd) eq_refl) (DSC 1281840 1%nat [Z_to_bv 8 96] ltac:(img_rd) eq_refl) (DSC 1281840 8%nat (word_to_le_bytes 8 (Z_to_bv 64 96)) ltac:(img_rd) eq_refl) (DSC 1281880 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl)
(DSC 1281888 8%nat (word_to_le_bytes 8 (Z_to_bv 64 144288)) ltac:(img_rd) eq_refl) (DSC 1281904 1%nat [Z_to_bv 8 32] ltac:(img_rd) eq_refl) (DSC 1281904 8%nat (word_to_le_bytes 8 (Z_to_bv 64 32)) ltac:(img_rd) eq_refl) (DSC 1281944 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1281952 8%nat (word_to_le_bytes 8 (Z_to_bv 64 144320)) ltac:(img_rd) eq_refl) (DSC 1281968 1%nat [Z_to_bv 8 64] ltac:(img_rd) eq_refl)
(DSC 1281968 8%nat (word_to_le_bytes 8 (Z_to_bv 64 64)) ltac:(img_rd) eq_refl) (DSC 1282008 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1282016 8%nat (word_to_le_bytes 8 (Z_to_bv 64 144384)) ltac:(img_rd) eq_refl) (DSC 1282032 1%nat [Z_to_bv 8 32] ltac:(img_rd) eq_refl) (DSC 1282032 8%nat (word_to_le_bytes 8 (Z_to_bv 64 32)) ltac:(img_rd) eq_refl) (DSC 1282072 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl)
(DSC 1282080 8%nat (word_to_le_bytes 8 (Z_to_bv 64 144416)) ltac:(img_rd) eq_refl) (DSC 1282096 1%nat [Z_to_bv 8 96] ltac:(img_rd) eq_refl) (DSC 1282096 8%nat (word_to_le_bytes 8 (Z_to_bv 64 96)) ltac:(img_rd) eq_refl) (DSC 1282136 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1282144 8%nat (word_to_le_bytes 8 (Z_to_bv 64 144512)) ltac:(img_rd) eq_refl) (DSC 1282160 1%nat [Z_to_bv 8 128] ltac:(img_rd) eq_refl)
(DSC 1282160 8%nat (word_to_le_bytes 8 (Z_to_bv 64 128)) ltac:(img_rd) eq_refl) (DSC 1282200 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1282208 8%nat (word_to_le_bytes 8 (Z_to_bv 64 144640)) ltac:(img_rd) eq_refl) (DSC 1282224 1%nat [Z_to_bv 8 128] ltac:(img_rd) eq_refl) (DSC 1282224 8%nat (word_to_le_bytes 8 (Z_to_bv 64 128)) ltac:(img_rd) eq_refl) (DSC 1282264 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl)
(DSC 1282272 8%nat (word_to_le_bytes 8 (Z_to_bv 64 144768)) ltac:(img_rd) eq_refl) (DSC 1282288 1%nat [Z_to_bv 8 32] ltac:(img_rd) eq_refl) (DSC 1282288 8%nat (word_to_le_bytes 8 (Z_to_bv 64 32)) ltac:(img_rd) eq_refl) (DSC 1282328 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1282336 8%nat (word_to_le_bytes 8 (Z_to_bv 64 144800)) ltac:(img_rd) eq_refl) (DSC 1282352 1%nat [Z_to_bv 8 96] ltac:(img_rd) eq_refl)
(DSC 1282352 8%nat (word_to_le_bytes 8 (Z_to_bv 64 96)) ltac:(img_rd) eq_refl) (DSC 1282392 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1282400 8%nat (word_to_le_bytes 8 (Z_to_bv 64 144896)) ltac:(img_rd) eq_refl) (DSC 1282416 1%nat [Z_to_bv 8 128] ltac:(img_rd) eq_refl) (DSC 1282416 8%nat (word_to_le_bytes 8 (Z_to_bv 64 128)) ltac:(img_rd) eq_refl) (DSC 1282456 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl)
(DSC 1282464 8%nat (word_to_le_bytes 8 (Z_to_bv 64 145024)) ltac:(img_rd) eq_refl) (DSC 1282480 1%nat [Z_to_bv 8 128] ltac:(img_rd) eq_refl) (DSC 1282480 8%nat (word_to_le_bytes 8 (Z_to_bv 64 128)) ltac:(img_rd) eq_refl) (DSC 1282520 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1282528 8%nat (word_to_le_bytes 8 (Z_to_bv 64 145152)) ltac:(img_rd) eq_refl) (DSC 1282544 1%nat [Z_to_bv 8 96] ltac:(img_rd) eq_refl)
(DSC 1282544 8%nat (word_to_le_bytes 8 (Z_to_bv 64 96)) ltac:(img_rd) eq_refl) (DSC 1282584 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1282592 8%nat (word_to_le_bytes 8 (Z_to_bv 64 145248)) ltac:(img_rd) eq_refl) (DSC 1282608 1%nat [Z_to_bv 8 96] ltac:(img_rd) eq_refl) (DSC 1282608 8%nat (word_to_le_bytes 8 (Z_to_bv 64 96)) ltac:(img_rd) eq_refl) (DSC 1282648 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl)
(DSC 1282656 8%nat (word_to_le_bytes 8 (Z_to_bv 64 145344)) ltac:(img_rd) eq_refl) (DSC 1282672 1%nat [Z_to_bv 8 96] ltac:(img_rd) eq_refl) (DSC 1282672 8%nat (word_to_le_bytes 8 (Z_to_bv 64 96)) ltac:(img_rd) eq_refl) (DSC 1282712 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1282720 8%nat (word_to_le_bytes 8 (Z_to_bv 64 145440)) ltac:(img_rd) eq_refl) (DSC 1282736 1%nat [Z_to_bv 8 128] ltac:(img_rd) eq_refl)
(DSC 1282736 8%nat (word_to_le_bytes 8 (Z_to_bv 64 128)) ltac:(img_rd) eq_refl) (DSC 1282776 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1282784 8%nat (word_to_le_bytes 8 (Z_to_bv 64 145568)) ltac:(img_rd) eq_refl) (DSC 1282800 1%nat [Z_to_bv 8 64] ltac:(img_rd) eq_refl) (DSC 1282800 8%nat (word_to_le_bytes 8 (Z_to_bv 64 64)) ltac:(img_rd) eq_refl) (DSC 1282840 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl)
(DSC 1282848 8%nat (word_to_le_bytes 8 (Z_to_bv 64 145632)) ltac:(img_rd) eq_refl) (DSC 1282864 1%nat [Z_to_bv 8 96] ltac:(img_rd) eq_refl) (DSC 1282864 8%nat (word_to_le_bytes 8 (Z_to_bv 64 96)) ltac:(img_rd) eq_refl) (DSC 1282904 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (XCC 8%nat 6886088 8 0 eq_refl) (XCC 9%nat 1281648 8 1281416 eq_refl)
(XCC 10%nat 1281556 4 4294967295 eq_refl) (XCC 11%nat 1281456 8 0 eq_refl) (XCC 12%nat 1281472 8 0 eq_refl) (XCC 13%nat 1281424 8 0 eq_refl) (XCC 14%nat 1281432 8 0 eq_refl) (XCC 15%nat 1281408 8 1281176 eq_refl)
SOlock SOwpos SOwbase SOwrite CANc SOfd) as
(fx1 & R1 & MV1 & XGR & _ & XFRZ & XMS & _ & _ & Xr2 & _ & _ & _ & Xr8 & Xr9 & Xr10 & Xr11 & Xr12 & _ & _ & _ & _ & Xr17 & Xr18 & Xr19 & Xr21 & Xr22 & _ & Xm112 & Xm120 & Xm128 & Xm136 & Xm104 & Xm96 & Xm88 & Xm80 & Xm72 & Xm64 & Xm56 & Xm48 & Xm40 & Xm32 & Xm24 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _).
unfold V in XFRZ, XMS; cbn beta iota in XFRZ, XMS. cbn [V] in *.
pose proof (dinv_lzinv scfg L ar C IL HI HIok sp0 DL M0 _ _ _ _ _ _ D) as LZ. pose proof LZ as (HH & HL & HA & HM & Hh).
set (good := fun i : Z => i < 1282944 \/ 1286904 <= i < 6884112 \/ 6884136 <= i < 6884656 \/ 6884660 <= i < 2147450880).
assert (FRX : forall i, 0 <= i -> good i -> MV1 (Z_to_bv 64 i) = MV (Z_to_bv 64 i)).
{ intros i Hi Hg. apply XFRZ; [unfold good in Hg; clear - Hi Hg; lia | ..]; (intros X; unfold good in Hg; clear - Hsp' HS1 HS2 Hi Hg X; lia). }
apply (msteps_vis_fx scfg (ahid A model) A fx fx1 R (Z_to_bv 64 0x11575c) M R1 (Z_to_bv 64 0x11d13c) MV1 model _ LZ XMS).
intros M1 model1 MI1 SBM1 VIS1.
assert (LITX : forall a (n : nat) bs, rdn ASEGS MV (Z_to_bv 64 a) n = Some bs ->
(0 <=? a) && ((a + Z.of_nat n <=? 1282944) || ((1286904 <=? a) && (a + Z.of_nat n <=? 6884112)) || ((6884660 <=? a) && (a + Z.of_nat n <=? 2147450880))) = true ->
rdn ASEGS MV1 (Z_to_bv 64 a) n = Some bs).
{ intros a n bs Hr Hb. apply andb_prop in Hb as (B1 & B2). apply Z.leb_le in B1. rewrite !orb_true_iff, !andb_true_iff, !Z.leb_le in B2.
apply (rdn_tr MV MV1 a n bs Hr B1); [lia|]. intros i Hi. apply FRX; [lia|]. unfold good. clear - B1 B2 Hi. lia. }
assert (DATA : rdn ASEGS MV1 (Z_to_bv 64 6886112) (Z.to_nat (2 * 1)) = Some (zero_lines 1%nat)).
{ apply (LITX 6886112 (Z.to_nat (2 * 1))); [|reflexivity]. change (Z.to_nat (2 * 1)) with (2 * 1%nat)%nat.
destruct (BC 0 ltac:(lia)) as (B0a & B0b). cbn [zero_lines].
apply rdn_cons1; [lia | exact B0a|]. apply rdn_cons1; [lia | exact B0b|]. reflexivity. }
set (q := S - 136) in *.
assert (Hq : 0 <= q /\ q <= q + 32 /\ q + 32 + 16 <= 2 ^ 47) by (unfold q; clear - Hsp' HS1 HS2; lia).
assert (Hf : 0 <= 1281176 /\ (1281176 + 124 <= q \/ q + 32 + 16 <= 1281176 + 120) /\ 1281176 + 124 < 2 ^ 63) by (unfold q; clear - Hsp' HS1 HS2; lia).
assert (NLq : forall x, q <= x < q + 32 -> page_in_ranges (page_base_of x) (m_vm_lazy model) = false).
{ intros x Hx. apply (nl_pt scfg L ar C IL HI HIok sp0 Hsp DL M0 _ _ _ _ _ _ x D); unfold q in Hx; clear - Hsp' HS1 HS2 Hx; lia. }
assert (WIN1 : forall a n, usp - 8388608 <= a -> a + n <= usp -> forall d (k : nat), 0 <= d -> d + Z.of_nat k <= n -> store_ok ASEGS MV1 (Z_to_bv 64 (a + d)) k = true)
by (intros a n H1 H2 d k Hd Hk; apply (store_ok_mono ASEGS k MV MV1 _ XGR); apply (WIN a n); assumption).
unfold W. rewrite <- (app_nil_r (zero_lines 1%nat)).
apply (wv_loop scfg (ahid A model) A HH (m_vm_lazy model) HL HA 1281176 1 ltac:(lia) q (q + 32) Hq Hf NLq (t_exit (Z_to_bv 64 st) (m_fs model)) (t_exit_has_nil _ _)
(2 * 1%nat)%nat true R1 M1 model1 q 2 6886112 (2 * 1) 0 0 (zero_lines 1%nat) []).
{ cbn. lia. }
{ exact (sbm_lazy_eq _ _ SBM1). }
{ exact MI1. }
{ rewrite (sbm_halted_eq _ _ SBM1). exact Hh. }
{ rewrite (sbm_fds' _ _ SBM1). exact FD1. }
{ unfold wv_regs. repeat split; assumption. }
{ rewrite VIS1. unfold wv_iov. split; [lia|]. split; [lia|]. split; [right; reflexivity|].
split; [exact Xm136|]. split; [replace (q + 8) with (S - 128) by (unfold q; ring); exact Xm128|].
split; [replace (Z_to_bv 64 q) with (Z_to_bv 64 (q + 0)) by (f_equal; lia); apply (WIN1 q 32); [unfold q; clear - Hsp' HS1 HS2; lia | unfold q; clear - Hsp' HS1 HS2; lia | lia | cbn; lia]|].
split; [unfold wv_buf; split; [lia|]; split; [lia|]; split; [lia|]; split; [right; left; unfold q; clear - Hsp' HS1 HS2; lia|]; split; [exact DATA|];
intros x Hx; apply (nl_pt scfg L ar C IL HI HIok sp0 Hsp DL M0 _ _ _ _ _ _ x D); lia|].
split; [intros X; discriminate X|]. intros _.
split; [replace (q + 16) with (S - 120) by (unfold q; ring); exact Xm120|].
split; [replace (q + 24) with (S - 112) by (unfold q; ring); exact Xm112|].
split; [|lia].
unfold wv_buf. split; [lia|]. split; [lia|]. split; [lia|]. split; [left; reflexivity|]. split; [reflexivity|]. intros x Hx. lia. }
{ lia. }
{ rewrite VIS1. exact (LITX _ _ _ SOfd eq_refl). }
intros R3 M3 model3 MI3 SBM3 KR3 _ FRV3 _ GRV3. rewrite VIS1 in FRV3, GRV3.
set (MV3 := mrestrict (ahid A model) M3) in *.
assert (LIT3 : forall a (n : nat) bs, rdn ASEGS MV (Z_to_bv 64 a) n = Some bs ->
(0 <=? a) && ((a + Z.of_nat n <=? 1282944) || ((1286904 <=? a) && (a + Z.of_nat n <=? 6884112)) || ((6884660 <=? a) && (a + Z.of_nat n <=? 2147450880))) = true ->
rdn ASEGS MV3 (Z_to_bv 64 a) n = Some bs).
{ intros a n bs Hr Hb. pose proof (LITX a n bs Hr Hb) as Y. apply andb_prop in Hb as (B1 & B2). apply Z.leb_le in B1. rewrite !orb_true_iff, !andb_true_iff, !Z.leb_le in B2.
apply (rdn_tr MV1 MV3 a n bs Y B1); [lia|]. intros i Hi. apply FRV3; [lia|]. unfold q. clear - Hsp' HS1 HS2 B1 B2 Hi. lia. }
assert (cellS : forall off k (n : nat) bs, rdn ASEGS MV1 (Z_to_bv 64 (S - k)) n = Some bs ->
(off + k =? 144) && (Z.of_nat n <=? k) && (k <=? 104) = true -> rdn ASEGS MV3 (Z_to_bv 64 (S - 144 + off)) n = Some bs).
{ intros off k n bs Hr Hb. apply andb_prop in Hb as (Hb & Hb3). apply andb_prop in Hb as (Hb1 & Hb2).
apply Z.eqb_eq in Hb1. apply Z.leb_le in Hb2, Hb3. replace (S - 144 + off) with (S - k) by lia.
apply (rdn_tr MV1 MV3 _ _ _ Hr); [clear - Hsp' HS1 HS2 Hb3; lia | clear - Hsp' HS1 HS2 Hb2; lia|].
intros i Hi. apply FRV3; unfold q; clear - Hsp' HS1 HS2 Hb2 Hb3 Hi; lia. }
assert (WIN3 : forall a n, usp - 8388608 <= a -> a + n <= usp -> forall d (k : nat), 0 <= d -> d + Z.of_nat k <= n -> store_ok ASEGS MV3 (Z_to_bv 64 (a + d)) k = true)
by (intros a n H1 H2 d k Hd Hk; apply (store_ok_mono ASEGS k MV1 MV3 _ GRV3); apply (WIN1 a n); assumption).
assert (FW3 : forall a n, 1281176 <= a -> a + n <= 1281176 + 232 -> forall d (k : nat), 0 <= d -> d + Z.of_nat k <= n -> store_ok ASEGS MV3 (Z_to_bv 64 (a + d)) k = true)
by (intros a n H1 H2 d k Hd Hk; apply (store_ok_mono ASEGS k MV1 MV3 _ GRV3); apply (store_ok_mono ASEGS k MV MV1 _ XGR); apply (FW a n); assumption).
assert (IMG3 : forall i, 65536 <= i < 1269760 -> MV3 (Z_to_bv 64 i) = None).
{ intros i Hi. rewrite FRV3; [rewrite FRX; [apply IMGc; exact Hi | lia | unfold good; lia] | lia | unfold q; clear - Hsp' HS1 HS2 Hi; lia]. }
set (VD := fun n : nat => match n with
| 2%nat => S - 144 | 40%nat => canz
| 9%nat => bv_unsigned (getr R (Z_to_bv 5 (Z.of_nat 9))) | 10%nat => bv_unsigned (getr R (Z_to_bv 5 (Z.of_nat 10)))
| 18%nat => bv_unsigned (getr R (Z_to_bv 5 (Z.of_nat 18))) | 19%nat => bv_unsigned (getr R (Z_to_bv 5 (Z.of_nat 19)))
| 20%nat => bv_unsigned (getr R (Z_to_bv 5 (Z.of_nat 20))) | 21%nat => bv_unsigned (getr R (Z_to_bv 5 (Z.of_nat 21)))
| 22%nat => bv_unsigned (getr R (Z_to_bv 5 (Z.of_nat 22)))
| 110%nat => bv_unsigned (getr R3 (Z_to_bv 5 (Z.of_nat 10))) | 118%nat => bv_unsigned (getr R3 (Z_to_bv 5 (Z.of_nat 18)))
| 119%nat => bv_unsigned (getr R3 (Z_to_bv 5 (Z.of_nat 19))) | 120%nat => bv_unsigned (getr R3 (Z_to_bv 5 (Z.of_nat 20)))
| 122%nat => bv_unsigned (getr R3 (Z_to_bv 5 (Z.of_nat 22)))
| _ => 0 end).
assert (Dg2 : getr R3 (Z_to_bv 5 (Z.of_nat 2)) = Z_to_bv 64 (VD 2%nat)) by (eapply eq_trans; [exact (KR3 2%bv ltac:(unfold WV_KEEP; cbn [In]; tauto)) | exact Xr2]).
assert (Dg8 : getr R3 (Z_to_bv 5 (Z.of_nat 8)) = Z_to_bv 64 0) by (eapply eq_trans; [exact (KR3 8%bv ltac:(unfold WV_KEEP; cbn [In]; tauto)) | exact Xr8]).
assert (Dg9 : getr R3 (Z_to_bv 5 (Z.of_nat 9)) = Z_to_bv 64 1281176) by (eapply eq_trans; [exact (KR3 9%bv ltac:(unfold WV_KEEP; cbn [In]; tauto)) | exact Xr9]).
assert (Dg21 : getr R3 (Z_to_bv 5 (Z.of_nat 21)) = Z_to_bv 64 6884096) by (eapply eq_trans; [exact (KR3 21%bv ltac:(unfold WV_KEEP; cbn [In]; tauto)) | exact Xr21]).
assert (Dg10 : getr R3 (Z_to_bv 5 (Z.of_nat 10)) = Z_to_bv 64 (VD 110%nat)) by (cbn [VD]; symmetry; apply Z_to_bv_bv_unsigned).
assert (Dg18 : getr R3 (Z_to_bv 5 (Z.of_nat 18)) = Z_to_bv 64 (VD 118%nat)) by (cbn [VD]; symmetry; apply Z_to_bv_bv_unsigned).
assert (Dg19 : getr R3 (Z_to_bv 5 (Z.of_nat 19)) = Z_to_bv 64 (VD 119%nat)) by (cbn [VD]; symmetry; apply Z_to_bv_bv_unsigned).
assert (Dg20 : getr R3 (Z_to_bv 5 (Z.of_nat 20)) = Z_to_bv 64 (VD 120%nat)) by (cbn [VD]; symmetry; apply Z_to_bv_bv_unsigned).
assert (Dg22 : getr R3 (Z_to_bv 5 (Z.of_nat 22)) = Z_to_bv 64 (VD 122%nat)) by (cbn [VD]; symmetry; apply Z_to_bv_bv_unsigned).
assert (HD64 : 0 <= VD 2%nat < 2 ^ 64) by (cbn [VD]; clear - Hsp' HS1 HS2; lia).
assert (HDr : 140735332552704 <= VD 2%nat <= 140737488355328) by (cbn [VD]; clear - Hsp' HS1 HS2; lia).
assert (HDa : AS0DRVP_dpXd_2.aligned (VD 2%nat) 16).
{ cbn [VD]. unfold AS0DRVP_dpXd_2.aligned. clear - HS16. Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). lia.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false). }
assert (DWR : L5Defs.L5.writable ASEGS MV3 (VD 2%nat - 16) 16).
{ cbn [VD]. intros d k Hd Hk. apply (WIN3 (S - 144 - 16) 16); clear - Hsp' HS1 HS2 Hd Hk; lia. }
assert (DDF : L5Defs.L5.defined MV3 (VD 2%nat - 16) 16).
{ cbn [VD]. intros i Hi. apply (store_ok_defined sp0); [clear - Hsp' HS1 HS2 Hi; lia|]. apply (WIN3 (S - 144 - 16) 16); clear - Hsp' HS1 HS2 Hi; lia. }
destruct (AS0DRVP_dpXd_2.dpXd_2_conc fx1 R3 MV3 VD HD64 (u64_range _)
(u64_range _) (u64_range _) (u64_range _) (u64_range _) (u64_range _) (u64_range _)
Hcan (u64_range _) (u64_range _) (u64_range _) (u64_range _) (u64_range _)
Dg2 Dg8 Dg9 Dg10 Dg18 Dg19
Dg20 Dg21 Dg22 HDr HDa DWR
DDF IMG3 (fun d k Hd Hk => FW3 1281208 8 ltac:(lia) ltac:(lia) d k Hd Hk) (fun d k Hd Hk => FW3 1281216 8 ltac:(lia) ltac:(lia) d k Hd Hk) (fun d k Hd Hk => FW3 1281232 8 ltac:(lia) ltac:(lia) d k Hd Hk) (LIT3 1281264 8%nat _ SObuf eq_refl)
(LIT3 1281272 8%nat _ SObufsz eq_refl) (LIT3 6884096 8%nat _ CANc eq_refl) (cellS 40 104 _ _ Xm104 eq_refl) (cellS 104 40 _ _ Xm40 eq_refl) (cellS 96 48 _ _ Xm48 eq_refl) (cellS 88 56 _ _ Xm56 eq_refl)
(cellS 80 64 _ _ Xm64 eq_refl) (cellS 72 72 _ _ Xm72 eq_refl) (cellS 64 80 _ _ Xm80 eq_refl) (cellS 56 88 _ _ Xm88 eq_refl) (cellS 48 96 _ _ Xm96 eq_refl) (LIT3 1281184 8%nat _ SOrpos eq_refl)
(LIT3 1281192 8%nat _ SOrend eq_refl) (LIT3 1281168 8%nat _ (XCC 16%nat 1281168 8 1280936 eq_refl) eq_refl) (LIT3 1281076 4%nat _ (XCC 17%nat 1281076 4 4294967295 eq_refl) eq_refl) (LIT3 1280976 8%nat _ (XCC 18%nat 1280976 8 0 eq_refl) eq_refl) (LIT3 1280992 8%nat _ (XCC 19%nat 1280992 8 0 eq_refl) eq_refl) (LIT3 1280944 8%nat _ (XCC 20%nat 1280944 8 0 eq_refl) eq_refl)
(LIT3 1280952 8%nat _ (XCC 21%nat 1280952 8 0 eq_refl) eq_refl) (cellS 120 24 _ _ Xm24 eq_refl) (cellS 112 32 _ _ Xm32 eq_refl)) as
(fx2 & R4 & MV4 & _ & _ & _ & DMS & _ & _ & _ & _ & _ & Dr10 & _ & _ & Dr17 & _).
unfold VD in DMS; cbn beta iota in DMS.
assert (LZ3 : lzinv ASEGS (ahid A model) A model3).
{ apply (lzinv_sbm ASEGS (ahid A model) A model model3 LZ MI3). exact (same_but_materialized_trans _ _ _ SBM1 SBM3). }
apply (msteps_vis_fx scfg (ahid A model) A fx1 fx2 R3 (Z_to_bv 64 0x11d148) M3 R4 (Z_to_bv 64 0x11546c) MV4 model3 _ LZ3 DMS).
intros M5 model5 MI5 SBM5 _.
pose proof (same_but_materialized_trans _ _ _ (same_but_materialized_trans _ _ _ SBM1 SBM3) SBM5) as SBMT.
rewrite <- (proj2 (sbm_fds model model5 SBMT)).
apply (rz_exit_at_lit_lz ASEGS scfg R4 (Z_to_bv 64 0x11546c) M5 rom model5 ECALLW st fetch_exitA is_ecall_ECALLW).
- rewrite (sbm_halted_eq _ _ SBMT). exact Hh.
- left. exact Dr17.
- eapply eq_trans; [exact Dr10|]. cbn [VD]. rewrite Z_to_bv_bv_unsigned. exact G10.
- exact Hst.
Qed.
#[using="L C IL HIok ICok ILY Hsp DL Hex"] Lemma exit_run_3B : ltac2:(TCodec.tc2 tcn__Jb0DrvExit "TL'6'<'A%2211%411&Q?%611&Q='S9yR0%211'9y8%511%311p051'L&Q0y5%2219&QAr;r:r9r8r7r6r4r2%9887654321&Q:&Q>%1297%3219'?&R=zr5%3221&R?+X0%2241%8241%827@&RA+2+R0%3221%92E1%?261'@&QL(S7+1(>%33Q521%52Q11&S8+QRclH%22QB1%:3QB41%93Q;@7%;2Q81%62QFQ8%>3QF21+4%>3Q@1<%@2Q>1+V^Rf0%<2QL1%D3QL31r<+:%E3QG1C%G231%B2R2QE%J3R221%R=1R0%R311&QN&R8+VbRh0%I2R91u8%544QK21(2&G%124H%32;1%Q73;51&QG%12Q>R3&QF%11R6'K%RD11&M&NrA%211%Q;2RKQ?%5221(J%113%C2:1%QG3:41'R5vS4(I&QMvRK+QRejL%QG2S71rC&QO%11Q3%756B431rB%:221&R1&R3&R4u2%211%42R71&R2r?%R62SF1&O%11<%5231%<271%J4QDI>1p0L1p0Q91p0Q<1p0Q?1p0QM1p0R41p0R;1p0R@1p0RL1p0S41tR:T0S>1p0SC1pUDT?1pVFT@1pV>TA1pTDTB1pR>T21pV0T61pR4T81p2TD1pUFTB1pQ<TD1pQ:TG1").
Proof.
intros LB LK cr A M model R S st tid canz (D & HS1 & HS2 & HS16 & WIN & IMGc & (XC & TIDC & HTr & DESC)) MV Hst Hcan G1 G2 G4 G10 CANc SO SOX FD1.
pose proof Hsp as Hsp'. destruct SO as (_ & SObufsz & _ & SOwpos & SOwbase & SOlock & _ & FW & BW & BC). destruct SOX as (SOwrite & SOfd & SObuf & SOrpos & SOrend).
set (V := fun n : nat => match n with 2%nat => S | 44%nat => tid | 40%nat => canz | _ => 0 end).
assert (HS64 : 0 <= V 2%nat < 2 ^ 64) by (cbn [V]; clear - Hsp' HS1 HS2; lia).
assert (HT64 : 0 <= V 44%nat < 2 ^ 64) by (cbn [V]; clear - HTr; lia).
assert (HSr : 140735332552704 <= V 2%nat <= 140737488355328) by (cbn [V]; clear - Hsp' HS1 HS2; lia).
assert (HSa : AS0DRVP_dpX3B_pre.aligned (V 2%nat) 16) by (cbn [V]; exact HS16).
assert (CWR : L5Defs.L5.writable ASEGS MV (V 2%nat - 320) 320).
{ cbn [V]. intros d k Hd Hk. apply (WIN (S - 320) 320); clear - Hsp' HS1 HS2 Hd Hk; lia. }
assert (CDF : L5Defs.L5.defined MV (V 2%nat - 320) 320).
{ cbn [V]. intros i Hi. apply (store_ok_defined sp0); [clear - Hsp' HS1 HS2 Hi; lia|]. apply (WIN (S - 320) 320); clear - Hsp' HS1 HS2 Hi; lia. }
assert (WSG : forall a (n : nat), wseg_ok ASEGS (Z_to_bv 64 a) n = true -> (0 <=? a) && (a + Z.of_nat n <=? 2 ^ 63) = true -> L5Defs.L5.writable ASEGS MV a (Z.of_nat n)).
{ intros a n W Hb. apply andb_prop in Hb as (B1 & B2). apply Z.leb_le in B1, B2. exact (wsg_writable MV a n W B1 B2). }
assert (SHW : forall a n, ((2147468844 <=? a) && (a + n <=? 2147469096) || (2147611092 <=? a) && (a + n <=? 2147611248)) = true -> L5Defs.L5.writable ASEGS MV a n)
by (intros a n Hb; exact (sh_writable _ _ _ _ _ _ a n D Hb)).
assert (STC : forall (i : nat) a n v, nth_error EX_CELLS i = Some (a, n, v) -> rdn ASEGS MV (Z_to_bv 64 a) (Z.to_nat n) = Some (word_to_le_bytes (Z.to_nat n) (Z_to_bv 64 v)))
by (intros i a n v Hn; exact (ex_cell_vis _ _ _ _ _ _ a n v D (nth_error_In _ _ Hn))).
assert (STC1 : forall (i : nat) a v, nth_error EX_CELLS i = Some (a, 1, v) -> (0 <=? v) && (v <? 2 ^ 64) = true -> rdn ASEGS MV (Z_to_bv 64 a) 1 = Some [Z_to_bv 8 v]).
{ intros i a v Hn Hb. apply andb_prop in Hb as (B1 & B2). apply Z.leb_le in B1. apply Z.ltb_lt in B2. rewrite <- (ArtMem.art_bytes1 v (conj B1 B2)). exact (STC i a 1 v Hn). }
assert (XCC : forall (i : nat) a n v, nth_error XC_CELLS_B i = Some (a, n, v) -> rdn ASEGS MV (Z_to_bv 64 a) (Z.to_nat n) = Some (word_to_le_bytes (Z.to_nat n) (Z_to_bv 64 v)))
by (intros i a n v Hn; exact (cells_at_nth MV XC_CELLS_B i a n v XC Hn)).
assert (XCC1 : forall (i : nat) a v, nth_error XC_CELLS_B i = Some (a, 1, v) -> (0 <=? v) && (v <? 2 ^ 64) = true -> rdn ASEGS MV (Z_to_bv 64 a) 1 = Some [Z_to_bv 8 v]).
{ intros i a v Hn Hb. apply andb_prop in Hb as (B1 & B2). apply Z.leb_le in B1. apply Z.ltb_lt in B2. rewrite <- (ArtMem.art_bytes1 v (conj B1 B2)). exact (XCC i a 1 v Hn). }
assert (DSC : forall a (n : nat) bs, rdn ASEGS (fun _ => None) (Z_to_bv 64 a) n = Some bs -> (0x138ea0 <=? a) && (a + Z.of_nat n <=? 0x139380) = true -> rdn ASEGS MV (Z_to_bv 64 a) n = Some bs).
{ intros a n bs Hr Hb. apply andb_prop in Hb as (B1 & B2). apply Z.leb_le in B1, B2. apply (img_cell MV a n bs Hr); [lia | lia|]. intros i Hi. apply DESC. lia. }
destruct (AS0DRVP_dpX3B_pre.dpX3B_pre_conc fx R MV V HS64 Hcan
HT64 G1 G2 G4 HSr HSa
CWR CDF IMGc (WSG 1282944 8%nat ltac:(vm_compute; reflexivity) eq_refl) (WSG 1283024 1%nat ltac:(vm_compute; reflexivity) eq_refl) (WSG 1286896 8%nat ltac:(vm_compute; reflexivity) eq_refl)
(WSG 6884112 1%nat ltac:(vm_compute; reflexivity) eq_refl) (WSG 6884120 4%nat ltac:(vm_compute; reflexivity) eq_refl) (WSG 6884128 8%nat ltac:(vm_compute; reflexivity) eq_refl) (WSG 6884656 4%nat ltac:(vm_compute; reflexivity) eq_refl) (SHW 2147468844 1 eq_refl) (SHW 2147468845 1 eq_refl)
(SHW 2147468846 1 eq_refl) (SHW 2147468847 1 eq_refl) (SHW 2147468856 1 eq_refl) (SHW 2147468857 1 eq_refl) (SHW 2147468858 1 eq_refl) (SHW 2147468859 1 eq_refl)
(SHW 2147468860 1 eq_refl) (SHW 2147468860 4 eq_refl) (SHW 2147468861 1 eq_refl) (SHW 2147468862 1 eq_refl) (SHW 2147468863 1 eq_refl) (SHW 2147468864 4 eq_refl)
(SHW 2147468868 1 eq_refl) (SHW 2147468868 4 eq_refl) (SHW 2147468869 1 eq_refl) (SHW 2147468870 1 eq_refl) (SHW 2147468871 1 eq_refl) (SHW 2147468916 1 eq_refl)
(SHW 2147468917 1 eq_refl) (SHW 2147468918 1 eq_refl) (SHW 2147468919 1 eq_refl) (SHW 2147468920 1 eq_refl) (SHW 2147468921 1 eq_refl) (SHW 2147468922 1 eq_refl)
(SHW 2147468923 1 eq_refl) (SHW 2147468924 1 eq_refl) (SHW 2147468925 1 eq_refl) (SHW 2147468926 1 eq_refl) (SHW 2147468927 1 eq_refl) (SHW 2147468928 1 eq_refl)
(SHW 2147468929 1 eq_refl) (SHW 2147468930 1 eq_refl) (SHW 2147468931 1 eq_refl) (SHW 2147468932 1 eq_refl) (SHW 2147468932 4 eq_refl) (SHW 2147468933 1 eq_refl)
(SHW 2147468934 1 eq_refl) (SHW 2147468935 1 eq_refl) (SHW 2147468936 4 eq_refl) (SHW 2147468940 1 eq_refl) (SHW 2147468940 4 eq_refl) (SHW 2147468941 1 eq_refl)
(SHW 2147468942 1 eq_refl) (SHW 2147468943 1 eq_refl) (SHW 2147468944 1 eq_refl) (SHW 2147468944 4 eq_refl) (SHW 2147468945 1 eq_refl) (SHW 2147468946 1 eq_refl)
(SHW 2147468947 1 eq_refl) (SHW 2147468948 4 eq_refl) (SHW 2147468952 4 eq_refl) (SHW 2147468956 1 eq_refl) (SHW 2147468956 4 eq_refl) (SHW 2147468957 1 eq_refl)
(SHW 2147468958 1 eq_refl) (SHW 2147468959 1 eq_refl) (SHW 2147468960 1 eq_refl) (SHW 2147468960 4 eq_refl) (SHW 2147468961 1 eq_refl) (SHW 2147468962 1 eq_refl)
(SHW 2147468963 1 eq_refl) (SHW 2147468964 4 eq_refl) (SHW 2147468968 4 eq_refl) (SHW 2147468972 1 eq_refl) (SHW 2147468972 4 eq_refl) (SHW 2147468973 1 eq_refl)
(SHW 2147468974 1 eq_refl) (SHW 2147468975 1 eq_refl) (SHW 2147468976 1 eq_refl) (SHW 2147468977 1 eq_refl) (SHW 2147468978 1 eq_refl) (SHW 2147468979 1 eq_refl)
(SHW 2147468980 1 eq_refl) (SHW 2147468980 4 eq_refl) (SHW 2147468981 1 eq_refl) (SHW 2147468982 1 eq_refl) (SHW 2147468983 1 eq_refl) (SHW 2147468984 4 eq_refl)
(SHW 2147468988 1 eq_refl) (SHW 2147468988 4 eq_refl) (SHW 2147468989 1 eq_refl) (SHW 2147468990 1 eq_refl) (SHW 2147468991 1 eq_refl) (SHW 2147468992 1 eq_refl)
(SHW 2147468992 4 eq_refl) (SHW 2147468993 1 eq_refl) (SHW 2147468994 1 eq_refl) (SHW 2147468995 1 eq_refl) (SHW 2147468996 4 eq_refl) (SHW 2147469000 4 eq_refl)
(SHW 2147469004 1 eq_refl) (SHW 2147469004 4 eq_refl) (SHW 2147469005 1 eq_refl) (SHW 2147469006 1 eq_refl) (SHW 2147469007 1 eq_refl) (SHW 2147469008 1 eq_refl)
(SHW 2147469008 4 eq_refl) (SHW 2147469009 1 eq_refl) (SHW 2147469010 1 eq_refl) (SHW 2147469011 1 eq_refl) (SHW 2147469012 4 eq_refl) (SHW 2147469016 4 eq_refl)
(SHW 2147469020 1 eq_refl) (SHW 2147469020 4 eq_refl) (SHW 2147469021 1 eq_refl) (SHW 2147469022 1 eq_refl) (SHW 2147469023 1 eq_refl) (SHW 2147469024 1 eq_refl)
(SHW 2147469024 4 eq_refl) (SHW 2147469025 1 eq_refl) (SHW 2147469026 1 eq_refl) (SHW 2147469027 1 eq_refl) (SHW 2147469028 4 eq_refl) (SHW 2147469032 1 eq_refl)
(SHW 2147469032 4 eq_refl) (SHW 2147469033 1 eq_refl) (SHW 2147469034 1 eq_refl) (SHW 2147469035 1 eq_refl) (SHW 2147469036 1 eq_refl) (SHW 2147469036 4 eq_refl)
(SHW 2147469037 1 eq_refl) (SHW 2147469038 1 eq_refl) (SHW 2147469039 1 eq_refl) (SHW 2147469040 4 eq_refl) (SHW 2147469044 1 eq_refl) (SHW 2147469044 4 eq_refl)
(SHW 2147469045 1 eq_refl) (SHW 2147469046 1 eq_refl) (SHW 2147469047 1 eq_refl) (SHW 2147469048 1 eq_refl) (SHW 2147469048 4 eq_refl) (SHW 2147469049 1 eq_refl)
(SHW 2147469050 1 eq_refl) (SHW 2147469051 1 eq_refl) (SHW 2147469052 4 eq_refl) (SHW 2147469056 1 eq_refl) (SHW 2147469056 4 eq_refl) (SHW 2147469057 1 eq_refl)
(SHW 2147469058 1 eq_refl) (SHW 2147469059 1 eq_refl) (SHW 2147469060 1 eq_refl) (SHW 2147469060 4 eq_refl) (SHW 2147469061 1 eq_refl) (SHW 2147469062 1 eq_refl)
(SHW 2147469063 1 eq_refl) (SHW 2147469064 4 eq_refl) (SHW 2147469068 4 eq_refl) (SHW 2147469072 1 eq_refl) (SHW 2147469072 4 eq_refl) (SHW 2147469073 1 eq_refl)
(SHW 2147469074 1 eq_refl) (SHW 2147469075 1 eq_refl) (SHW 2147469076 1 eq_refl) (SHW 2147469077 1 eq_refl) (SHW 2147469078 1 eq_refl) (SHW 2147469079 1 eq_refl)
(SHW 2147469080 1 eq_refl) (SHW 2147469081 1 eq_refl) (SHW 2147469082 1 eq_refl) (SHW 2147469083 1 eq_refl) (SHW 2147469084 1 eq_refl) (SHW 2147469084 4 eq_refl)
(SHW 2147469085 1 eq_refl) (SHW 2147469086 1 eq_refl) (SHW 2147469087 1 eq_refl) (SHW 2147469088 4 eq_refl) (SHW 2147469092 1 eq_refl) (SHW 2147469092 4 eq_refl)
(SHW 2147469093 1 eq_refl) (SHW 2147469094 1 eq_refl) (SHW 2147469095 1 eq_refl) (SHW 2147611092 1 eq_refl) (SHW 2147611092 4 eq_refl) (SHW 2147611093 1 eq_refl)
(SHW 2147611094 1 eq_refl) (SHW 2147611095 1 eq_refl) (SHW 2147611096 4 eq_refl) (SHW 2147611100 4 eq_refl) (SHW 2147611104 4 eq_refl) (SHW 2147611108 4 eq_refl)
(SHW 2147611112 4 eq_refl) (SHW 2147611116 4 eq_refl) (SHW 2147611120 8 eq_refl) (SHW 2147611128 8 eq_refl) (SHW 2147611136 8 eq_refl) (SHW 2147611144 8 eq_refl)
(SHW 2147611152 8 eq_refl) (SHW 2147611160 8 eq_refl) (SHW 2147611168 8 eq_refl) (SHW 2147611176 8 eq_refl) (SHW 2147611184 8 eq_refl) (SHW 2147611192 8 eq_refl)
(SHW 2147611200 8 eq_refl) (SHW 2147611208 8 eq_refl) (SHW 2147611216 4 eq_refl) (SHW 2147611220 4 eq_refl) (SHW 2147611224 4 eq_refl) (SHW 2147611228 4 eq_refl)
(SHW 2147611232 4 eq_refl) (SHW 2147611236 4 eq_refl) (SHW 2147611240 1 eq_refl) (SHW 2147611240 4 eq_refl) (SHW 2147611241 1 eq_refl) (SHW 2147611242 1 eq_refl)
(SHW 2147611243 1 eq_refl) TIDC HTr (XCC 0%nat 6884656 4 0 eq_refl) (XCC1 1%nat 6884691 0 eq_refl eq_refl) (XCC 2%nat 6884128 8 6884136 eq_refl)
(XCC 3%nat 6884120 4 4 eq_refl) (XCC 23%nat 6884168 8 447508 eq_refl) (XCC 25%nat 6884424 8 0 eq_refl) (XCC 6%nat 6884116 4 0 eq_refl) (STC1 11%nat 1286740 0 eq_refl eq_refl) (XCC 22%nat 6884160 8 860168 eq_refl)
(XCC 24%nat 6884416 8 1280728 eq_refl) (XCC 27%nat 6884152 8 1136392 eq_refl) (XCC 28%nat 6884408 8 686244 eq_refl) (XCC1 26%nat 6746260 0 eq_refl eq_refl) (XCC 4%nat 6884144 8 1136392 eq_refl) (XCC 5%nat 6884400 8 618204 eq_refl)
(STC1 10%nat 1894624 0 eq_refl eq_refl) (XCC 7%nat 6884136 8 0 eq_refl) (STC1 3%nat 1283024 0 eq_refl eq_refl) (STC 0%nat 1270192 8 1270192 eq_refl) (STC 2%nat 1282944 8 1 eq_refl) (STC 4%nat 1286736 4 1 eq_refl)
(STC 5%nat 1286896 8 0 eq_refl) (STC1 8%nat 1300248 1 eq_refl eq_refl) (STC 7%nat 1296952 8 2147450880 eq_refl) (DSC 1281696 8%nat (word_to_le_bytes 8 (Z_to_bv 64 143712)) ltac:(img_rd) eq_refl) (DSC 1281712 1%nat [Z_to_bv 8 32] ltac:(img_rd) eq_refl) (STC1 6%nat 1295004 1 eq_refl eq_refl)
(DSC 1281712 8%nat (word_to_le_bytes 8 (Z_to_bv 64 32)) ltac:(img_rd) eq_refl) (STC 9%nat 1893856 8 18446744073709551615 eq_refl) (STC 1%nat 1270704 8 1207272 eq_refl) (DSC 1281752 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1281760 8%nat (word_to_le_bytes 8 (Z_to_bv 64 143808)) ltac:(img_rd) eq_refl) (DSC 1281776 1%nat [Z_to_bv 8 32] ltac:(img_rd) eq_refl)
(DSC 1281776 8%nat (word_to_le_bytes 8 (Z_to_bv 64 32)) ltac:(img_rd) eq_refl) (DSC 1281816 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1281824 8%nat (word_to_le_bytes 8 (Z_to_bv 64 143840)) ltac:(img_rd) eq_refl) (DSC 1281840 1%nat [Z_to_bv 8 96] ltac:(img_rd) eq_refl) (DSC 1281840 8%nat (word_to_le_bytes 8 (Z_to_bv 64 96)) ltac:(img_rd) eq_refl) (DSC 1281880 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl)
(DSC 1281888 8%nat (word_to_le_bytes 8 (Z_to_bv 64 144288)) ltac:(img_rd) eq_refl) (DSC 1281904 1%nat [Z_to_bv 8 32] ltac:(img_rd) eq_refl) (DSC 1281904 8%nat (word_to_le_bytes 8 (Z_to_bv 64 32)) ltac:(img_rd) eq_refl) (DSC 1281944 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1281952 8%nat (word_to_le_bytes 8 (Z_to_bv 64 144320)) ltac:(img_rd) eq_refl) (DSC 1281968 1%nat [Z_to_bv 8 64] ltac:(img_rd) eq_refl)
(DSC 1281968 8%nat (word_to_le_bytes 8 (Z_to_bv 64 64)) ltac:(img_rd) eq_refl) (DSC 1282008 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1282016 8%nat (word_to_le_bytes 8 (Z_to_bv 64 144384)) ltac:(img_rd) eq_refl) (DSC 1282032 1%nat [Z_to_bv 8 32] ltac:(img_rd) eq_refl) (DSC 1282032 8%nat (word_to_le_bytes 8 (Z_to_bv 64 32)) ltac:(img_rd) eq_refl) (DSC 1282072 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl)
(DSC 1282080 8%nat (word_to_le_bytes 8 (Z_to_bv 64 144416)) ltac:(img_rd) eq_refl) (DSC 1282096 1%nat [Z_to_bv 8 96] ltac:(img_rd) eq_refl) (DSC 1282096 8%nat (word_to_le_bytes 8 (Z_to_bv 64 96)) ltac:(img_rd) eq_refl) (DSC 1282136 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1282144 8%nat (word_to_le_bytes 8 (Z_to_bv 64 144512)) ltac:(img_rd) eq_refl) (DSC 1282160 1%nat [Z_to_bv 8 128] ltac:(img_rd) eq_refl)
(DSC 1282160 8%nat (word_to_le_bytes 8 (Z_to_bv 64 128)) ltac:(img_rd) eq_refl) (DSC 1282200 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1282208 8%nat (word_to_le_bytes 8 (Z_to_bv 64 144640)) ltac:(img_rd) eq_refl) (DSC 1282224 1%nat [Z_to_bv 8 128] ltac:(img_rd) eq_refl) (DSC 1282224 8%nat (word_to_le_bytes 8 (Z_to_bv 64 128)) ltac:(img_rd) eq_refl) (DSC 1282264 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl)
(DSC 1282272 8%nat (word_to_le_bytes 8 (Z_to_bv 64 144768)) ltac:(img_rd) eq_refl) (DSC 1282288 1%nat [Z_to_bv 8 32] ltac:(img_rd) eq_refl) (DSC 1282288 8%nat (word_to_le_bytes 8 (Z_to_bv 64 32)) ltac:(img_rd) eq_refl) (DSC 1282328 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1282336 8%nat (word_to_le_bytes 8 (Z_to_bv 64 144800)) ltac:(img_rd) eq_refl) (DSC 1282352 1%nat [Z_to_bv 8 96] ltac:(img_rd) eq_refl)
(DSC 1282352 8%nat (word_to_le_bytes 8 (Z_to_bv 64 96)) ltac:(img_rd) eq_refl) (DSC 1282392 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1282400 8%nat (word_to_le_bytes 8 (Z_to_bv 64 144896)) ltac:(img_rd) eq_refl) (DSC 1282416 1%nat [Z_to_bv 8 128] ltac:(img_rd) eq_refl) (DSC 1282416 8%nat (word_to_le_bytes 8 (Z_to_bv 64 128)) ltac:(img_rd) eq_refl) (DSC 1282456 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl)
(DSC 1282464 8%nat (word_to_le_bytes 8 (Z_to_bv 64 145024)) ltac:(img_rd) eq_refl) (DSC 1282480 1%nat [Z_to_bv 8 128] ltac:(img_rd) eq_refl) (DSC 1282480 8%nat (word_to_le_bytes 8 (Z_to_bv 64 128)) ltac:(img_rd) eq_refl) (DSC 1282520 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1282528 8%nat (word_to_le_bytes 8 (Z_to_bv 64 145152)) ltac:(img_rd) eq_refl) (DSC 1282544 1%nat [Z_to_bv 8 96] ltac:(img_rd) eq_refl)
(DSC 1282544 8%nat (word_to_le_bytes 8 (Z_to_bv 64 96)) ltac:(img_rd) eq_refl) (DSC 1282584 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1282592 8%nat (word_to_le_bytes 8 (Z_to_bv 64 145248)) ltac:(img_rd) eq_refl) (DSC 1282608 1%nat [Z_to_bv 8 96] ltac:(img_rd) eq_refl) (DSC 1282608 8%nat (word_to_le_bytes 8 (Z_to_bv 64 96)) ltac:(img_rd) eq_refl) (DSC 1282648 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl)
(DSC 1282656 8%nat (word_to_le_bytes 8 (Z_to_bv 64 145344)) ltac:(img_rd) eq_refl) (DSC 1282672 1%nat [Z_to_bv 8 96] ltac:(img_rd) eq_refl) (DSC 1282672 8%nat (word_to_le_bytes 8 (Z_to_bv 64 96)) ltac:(img_rd) eq_refl) (DSC 1282712 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1282720 8%nat (word_to_le_bytes 8 (Z_to_bv 64 145440)) ltac:(img_rd) eq_refl) (DSC 1282736 1%nat [Z_to_bv 8 128] ltac:(img_rd) eq_refl)
(DSC 1282736 8%nat (word_to_le_bytes 8 (Z_to_bv 64 128)) ltac:(img_rd) eq_refl) (DSC 1282776 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1282784 8%nat (word_to_le_bytes 8 (Z_to_bv 64 145568)) ltac:(img_rd) eq_refl) (DSC 1282800 1%nat [Z_to_bv 8 64] ltac:(img_rd) eq_refl) (DSC 1282800 8%nat (word_to_le_bytes 8 (Z_to_bv 64 64)) ltac:(img_rd) eq_refl) (DSC 1282840 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl)
(DSC 1282848 8%nat (word_to_le_bytes 8 (Z_to_bv 64 145632)) ltac:(img_rd) eq_refl) (DSC 1282864 1%nat [Z_to_bv 8 96] ltac:(img_rd) eq_refl) (DSC 1282864 8%nat (word_to_le_bytes 8 (Z_to_bv 64 96)) ltac:(img_rd) eq_refl) (DSC 1282904 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (XCC 8%nat 6886088 8 0 eq_refl) (XCC 9%nat 1281648 8 1281416 eq_refl)
(XCC 10%nat 1281556 4 4294967295 eq_refl) (XCC 11%nat 1281456 8 0 eq_refl) (XCC 12%nat 1281472 8 0 eq_refl) (XCC 13%nat 1281424 8 0 eq_refl) (XCC 14%nat 1281432 8 0 eq_refl) (XCC 15%nat 1281408 8 1281176 eq_refl)
SOlock SOwpos SOwbase SOwrite CANc SOfd) as
(fx1 & R1 & MV1 & XGR & _ & XFRZ & XMS & _ & _ & Xr2 & _ & _ & _ & Xr8 & Xr9 & Xr10 & Xr11 & Xr12 & _ & _ & _ & _ & Xr17 & Xr18 & Xr19 & Xr21 & Xr22 & _ & Xm112 & Xm120 & Xm128 & Xm136 & Xm104 & Xm96 & Xm88 & Xm80 & Xm72 & Xm64 & Xm56 & Xm48 & Xm40 & Xm32 & Xm24 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _).
unfold V in XFRZ, XMS; cbn beta iota in XFRZ, XMS. cbn [V] in *.
pose proof (dinv_lzinv scfg L ar C IL HI HIok sp0 DL M0 _ _ _ _ _ _ D) as LZ. pose proof LZ as (HH & HL & HA & HM & Hh).
set (good := fun i : Z => i < 1282944 \/ 1286904 <= i < 6884112 \/ 6884136 <= i < 6884656 \/ 6884660 <= i < 2147450880).
assert (FRX : forall i, 0 <= i -> good i -> MV1 (Z_to_bv 64 i) = MV (Z_to_bv 64 i)).
{ intros i Hi Hg. apply XFRZ; [unfold good in Hg; clear - Hi Hg; lia | ..]; (intros X; unfold good in Hg; clear - Hsp' HS1 HS2 Hi Hg X; lia). }
apply (msteps_vis_fx scfg (ahid A model) A fx fx1 R (Z_to_bv 64 0x11575c) M R1 (Z_to_bv 64 0x11d13c) MV1 model _ LZ XMS).
intros M1 model1 MI1 SBM1 VIS1.
assert (LITX : forall a (n : nat) bs, rdn ASEGS MV (Z_to_bv 64 a) n = Some bs ->
(0 <=? a) && ((a + Z.of_nat n <=? 1282944) || ((1286904 <=? a) && (a + Z.of_nat n <=? 6884112)) || ((6884660 <=? a) && (a + Z.of_nat n <=? 2147450880))) = true ->
rdn ASEGS MV1 (Z_to_bv 64 a) n = Some bs).
{ intros a n bs Hr Hb. apply andb_prop in Hb as (B1 & B2). apply Z.leb_le in B1. rewrite !orb_true_iff, !andb_true_iff, !Z.leb_le in B2.
apply (rdn_tr MV MV1 a n bs Hr B1); [lia|]. intros i Hi. apply FRX; [lia|]. unfold good. clear - B1 B2 Hi. lia. }
assert (DATA : rdn ASEGS MV1 (Z_to_bv 64 6886112) (Z.to_nat (2 * 2)) = Some (zero_lines 2%nat)).
{ apply (LITX 6886112 (Z.to_nat (2 * 2))); [|reflexivity]. change (Z.to_nat (2 * 2)) with (2 * 2%nat)%nat.
destruct (BC 0 ltac:(lia)) as (B0a & B0b). destruct (BC 1 ltac:(lia)) as (B1a & B1b). cbn [zero_lines].
apply rdn_cons1; [lia | exact B0a|]. apply rdn_cons1; [lia | exact B0b|]. apply rdn_cons1; [lia | exact B1a|]. apply rdn_cons1; [lia | exact B1b|]. reflexivity. }
set (q := S - 136) in *.
assert (Hq : 0 <= q /\ q <= q + 32 /\ q + 32 + 16 <= 2 ^ 47) by (unfold q; clear - Hsp' HS1 HS2; lia).
assert (Hf : 0 <= 1281176 /\ (1281176 + 124 <= q \/ q + 32 + 16 <= 1281176 + 120) /\ 1281176 + 124 < 2 ^ 63) by (unfold q; clear - Hsp' HS1 HS2; lia).
assert (NLq : forall x, q <= x < q + 32 -> page_in_ranges (page_base_of x) (m_vm_lazy model) = false).
{ intros x Hx. apply (nl_pt scfg L ar C IL HI HIok sp0 Hsp DL M0 _ _ _ _ _ _ x D); unfold q in Hx; clear - Hsp' HS1 HS2 Hx; lia. }
assert (WIN1 : forall a n, usp - 8388608 <= a -> a + n <= usp -> forall d (k : nat), 0 <= d -> d + Z.of_nat k <= n -> store_ok ASEGS MV1 (Z_to_bv 64 (a + d)) k = true)
by (intros a n H1 H2 d k Hd Hk; apply (store_ok_mono ASEGS k MV MV1 _ XGR); apply (WIN a n); assumption).
unfold W. rewrite <- (app_nil_r (zero_lines 2%nat)).
apply (wv_loop scfg (ahid A model) A HH (m_vm_lazy model) HL HA 1281176 1 ltac:(lia) q (q + 32) Hq Hf NLq (t_exit (Z_to_bv 64 st) (m_fs model)) (t_exit_has_nil _ _)
(2 * 2%nat)%nat true R1 M1 model1 q 2 6886112 (2 * 2) 0 0 (zero_lines 2%nat) []).
{ cbn. lia. }
{ exact (sbm_lazy_eq _ _ SBM1). }
{ exact MI1. }
{ rewrite (sbm_halted_eq _ _ SBM1). exact Hh. }
{ rewrite (sbm_fds' _ _ SBM1). exact FD1. }
{ unfold wv_regs. repeat split; assumption. }
{ rewrite VIS1. unfold wv_iov. split; [lia|]. split; [lia|]. split; [right; reflexivity|].
split; [exact Xm136|]. split; [replace (q + 8) with (S - 128) by (unfold q; ring); exact Xm128|].
split; [replace (Z_to_bv 64 q) with (Z_to_bv 64 (q + 0)) by (f_equal; lia); apply (WIN1 q 32); [unfold q; clear - Hsp' HS1 HS2; lia | unfold q; clear - Hsp' HS1 HS2; lia | lia | cbn; lia]|].
split; [unfold wv_buf; split; [lia|]; split; [lia|]; split; [lia|]; split; [right; left; unfold q; clear - Hsp' HS1 HS2; lia|]; split; [exact DATA|];
intros x Hx; apply (nl_pt scfg L ar C IL HI HIok sp0 Hsp DL M0 _ _ _ _ _ _ x D); lia|].
split; [intros X; discriminate X|]. intros _.
split; [replace (q + 16) with (S - 120) by (unfold q; ring); exact Xm120|].
split; [replace (q + 24) with (S - 112) by (unfold q; ring); exact Xm112|].
split; [|lia].
unfold wv_buf. split; [lia|]. split; [lia|]. split; [lia|]. split; [left; reflexivity|]. split; [reflexivity|]. intros x Hx. lia. }
{ lia. }
{ rewrite VIS1. exact (LITX _ _ _ SOfd eq_refl). }
intros R3 M3 model3 MI3 SBM3 KR3 _ FRV3 _ GRV3. rewrite VIS1 in FRV3, GRV3.
set (MV3 := mrestrict (ahid A model) M3) in *.
assert (LIT3 : forall a (n : nat) bs, rdn ASEGS MV (Z_to_bv 64 a) n = Some bs ->
(0 <=? a) && ((a + Z.of_nat n <=? 1282944) || ((1286904 <=? a) && (a + Z.of_nat n <=? 6884112)) || ((6884660 <=? a) && (a + Z.of_nat n <=? 2147450880))) = true ->
rdn ASEGS MV3 (Z_to_bv 64 a) n = Some bs).
{ intros a n bs Hr Hb. pose proof (LITX a n bs Hr Hb) as Y. apply andb_prop in Hb as (B1 & B2). apply Z.leb_le in B1. rewrite !orb_true_iff, !andb_true_iff, !Z.leb_le in B2.
apply (rdn_tr MV1 MV3 a n bs Y B1); [lia|]. intros i Hi. apply FRV3; [lia|]. unfold q. clear - Hsp' HS1 HS2 B1 B2 Hi. lia. }
assert (cellS : forall off k (n : nat) bs, rdn ASEGS MV1 (Z_to_bv 64 (S - k)) n = Some bs ->
(off + k =? 144) && (Z.of_nat n <=? k) && (k <=? 104) = true -> rdn ASEGS MV3 (Z_to_bv 64 (S - 144 + off)) n = Some bs).
{ intros off k n bs Hr Hb. apply andb_prop in Hb as (Hb & Hb3). apply andb_prop in Hb as (Hb1 & Hb2).
apply Z.eqb_eq in Hb1. apply Z.leb_le in Hb2, Hb3. replace (S - 144 + off) with (S - k) by lia.
apply (rdn_tr MV1 MV3 _ _ _ Hr); [clear - Hsp' HS1 HS2 Hb3; lia | clear - Hsp' HS1 HS2 Hb2; lia|].
intros i Hi. apply FRV3; unfold q; clear - Hsp' HS1 HS2 Hb2 Hb3 Hi; lia. }
assert (WIN3 : forall a n, usp - 8388608 <= a -> a + n <= usp -> forall d (k : nat), 0 <= d -> d + Z.of_nat k <= n -> store_ok ASEGS MV3 (Z_to_bv 64 (a + d)) k = true)
by (intros a n H1 H2 d k Hd Hk; apply (store_ok_mono ASEGS k MV1 MV3 _ GRV3); apply (WIN1 a n); assumption).
assert (FW3 : forall a n, 1281176 <= a -> a + n <= 1281176 + 232 -> forall d (k : nat), 0 <= d -> d + Z.of_nat k <= n -> store_ok ASEGS MV3 (Z_to_bv 64 (a + d)) k = true)
by (intros a n H1 H2 d k Hd Hk; apply (store_ok_mono ASEGS k MV1 MV3 _ GRV3); apply (store_ok_mono ASEGS k MV MV1 _ XGR); apply (FW a n); assumption).
assert (IMG3 : forall i, 65536 <= i < 1269760 -> MV3 (Z_to_bv 64 i) = None).
{ intros i Hi. rewrite FRV3; [rewrite FRX; [apply IMGc; exact Hi | lia | unfold good; lia] | lia | unfold q; clear - Hsp' HS1 HS2 Hi; lia]. }
set (VD := fun n : nat => match n with
| 2%nat => S - 144 | 40%nat => canz
| 9%nat => bv_unsigned (getr R (Z_to_bv 5 (Z.of_nat 9))) | 10%nat => bv_unsigned (getr R (Z_to_bv 5 (Z.of_nat 10)))
| 18%nat => bv_unsigned (getr R (Z_to_bv 5 (Z.of_nat 18))) | 19%nat => bv_unsigned (getr R (Z_to_bv 5 (Z.of_nat 19)))
| 20%nat => bv_unsigned (getr R (Z_to_bv 5 (Z.of_nat 20))) | 21%nat => bv_unsigned (getr R (Z_to_bv 5 (Z.of_nat 21)))
| 22%nat => bv_unsigned (getr R (Z_to_bv 5 (Z.of_nat 22)))
| 110%nat => bv_unsigned (getr R3 (Z_to_bv 5 (Z.of_nat 10))) | 118%nat => bv_unsigned (getr R3 (Z_to_bv 5 (Z.of_nat 18)))
| 119%nat => bv_unsigned (getr R3 (Z_to_bv 5 (Z.of_nat 19))) | 120%nat => bv_unsigned (getr R3 (Z_to_bv 5 (Z.of_nat 20)))
| 122%nat => bv_unsigned (getr R3 (Z_to_bv 5 (Z.of_nat 22)))
| _ => 0 end).
assert (Dg2 : getr R3 (Z_to_bv 5 (Z.of_nat 2)) = Z_to_bv 64 (VD 2%nat)) by (eapply eq_trans; [exact (KR3 2%bv ltac:(unfold WV_KEEP; cbn [In]; tauto)) | exact Xr2]).
assert (Dg8 : getr R3 (Z_to_bv 5 (Z.of_nat 8)) = Z_to_bv 64 0) by (eapply eq_trans; [exact (KR3 8%bv ltac:(unfold WV_KEEP; cbn [In]; tauto)) | exact Xr8]).
assert (Dg9 : getr R3 (Z_to_bv 5 (Z.of_nat 9)) = Z_to_bv 64 1281176) by (eapply eq_trans; [exact (KR3 9%bv ltac:(unfold WV_KEEP; cbn [In]; tauto)) | exact Xr9]).
assert (Dg21 : getr R3 (Z_to_bv 5 (Z.of_nat 21)) = Z_to_bv 64 6884096) by (eapply eq_trans; [exact (KR3 21%bv ltac:(unfold WV_KEEP; cbn [In]; tauto)) | exact Xr21]).
assert (Dg10 : getr R3 (Z_to_bv 5 (Z.of_nat 10)) = Z_to_bv 64 (VD 110%nat)) by (cbn [VD]; symmetry; apply Z_to_bv_bv_unsigned).
assert (Dg18 : getr R3 (Z_to_bv 5 (Z.of_nat 18)) = Z_to_bv 64 (VD 118%nat)) by (cbn [VD]; symmetry; apply Z_to_bv_bv_unsigned).
assert (Dg19 : getr R3 (Z_to_bv 5 (Z.of_nat 19)) = Z_to_bv 64 (VD 119%nat)) by (cbn [VD]; symmetry; apply Z_to_bv_bv_unsigned).
assert (Dg20 : getr R3 (Z_to_bv 5 (Z.of_nat 20)) = Z_to_bv 64 (VD 120%nat)) by (cbn [VD]; symmetry; apply Z_to_bv_bv_unsigned).
assert (Dg22 : getr R3 (Z_to_bv 5 (Z.of_nat 22)) = Z_to_bv 64 (VD 122%nat)) by (cbn [VD]; symmetry; apply Z_to_bv_bv_unsigned).
assert (HD64 : 0 <= VD 2%nat < 2 ^ 64) by (cbn [VD]; clear - Hsp' HS1 HS2; lia).
assert (HDr : 140735332552704 <= VD 2%nat <= 140737488355328) by (cbn [VD]; clear - Hsp' HS1 HS2; lia).
assert (HDa : AS0DRVP_dpXd_3.aligned (VD 2%nat) 16).
{ cbn [VD]. unfold AS0DRVP_dpXd_3.aligned. clear - HS16. Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). lia.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false). }
assert (DWR : L5Defs.L5.writable ASEGS MV3 (VD 2%nat - 16) 16).
{ cbn [VD]. intros d k Hd Hk. apply (WIN3 (S - 144 - 16) 16); clear - Hsp' HS1 HS2 Hd Hk; lia. }
assert (DDF : L5Defs.L5.defined MV3 (VD 2%nat - 16) 16).
{ cbn [VD]. intros i Hi. apply (store_ok_defined sp0); [clear - Hsp' HS1 HS2 Hi; lia|]. apply (WIN3 (S - 144 - 16) 16); clear - Hsp' HS1 HS2 Hi; lia. }
destruct (AS0DRVP_dpXd_3.dpXd_3_conc fx1 R3 MV3 VD HD64 (u64_range _)
(u64_range _) (u64_range _) (u64_range _) (u64_range _) (u64_range _) (u64_range _)
Hcan (u64_range _) (u64_range _) (u64_range _) (u64_range _) (u64_range _)
Dg2 Dg8 Dg9 Dg10 Dg18 Dg19
Dg20 Dg21 Dg22 HDr HDa DWR
DDF IMG3 (fun d k Hd Hk => FW3 1281208 8 ltac:(lia) ltac:(lia) d k Hd Hk) (fun d k Hd Hk => FW3 1281216 8 ltac:(lia) ltac:(lia) d k Hd Hk) (fun d k Hd Hk => FW3 1281232 8 ltac:(lia) ltac:(lia) d k Hd Hk) (LIT3 1281264 8%nat _ SObuf eq_refl)
(LIT3 1281272 8%nat _ SObufsz eq_refl) (LIT3 6884096 8%nat _ CANc eq_refl) (cellS 40 104 _ _ Xm104 eq_refl) (cellS 104 40 _ _ Xm40 eq_refl) (cellS 96 48 _ _ Xm48 eq_refl) (cellS 88 56 _ _ Xm56 eq_refl)
(cellS 80 64 _ _ Xm64 eq_refl) (cellS 72 72 _ _ Xm72 eq_refl) (cellS 64 80 _ _ Xm80 eq_refl) (cellS 56 88 _ _ Xm88 eq_refl) (cellS 48 96 _ _ Xm96 eq_refl) (LIT3 1281184 8%nat _ SOrpos eq_refl)
(LIT3 1281192 8%nat _ SOrend eq_refl) (LIT3 1281168 8%nat _ (XCC 16%nat 1281168 8 1280936 eq_refl) eq_refl) (LIT3 1281076 4%nat _ (XCC 17%nat 1281076 4 4294967295 eq_refl) eq_refl) (LIT3 1280976 8%nat _ (XCC 18%nat 1280976 8 0 eq_refl) eq_refl) (LIT3 1280992 8%nat _ (XCC 19%nat 1280992 8 0 eq_refl) eq_refl) (LIT3 1280944 8%nat _ (XCC 20%nat 1280944 8 0 eq_refl) eq_refl)
(LIT3 1280952 8%nat _ (XCC 21%nat 1280952 8 0 eq_refl) eq_refl) (cellS 120 24 _ _ Xm24 eq_refl) (cellS 112 32 _ _ Xm32 eq_refl)) as
(fx2 & R4 & MV4 & _ & _ & _ & DMS & _ & _ & _ & _ & _ & Dr10 & _ & _ & Dr17 & _).
unfold VD in DMS; cbn beta iota in DMS.
assert (LZ3 : lzinv ASEGS (ahid A model) A model3).
{ apply (lzinv_sbm ASEGS (ahid A model) A model model3 LZ MI3). exact (same_but_materialized_trans _ _ _ SBM1 SBM3). }
apply (msteps_vis_fx scfg (ahid A model) A fx1 fx2 R3 (Z_to_bv 64 0x11d148) M3 R4 (Z_to_bv 64 0x11546c) MV4 model3 _ LZ3 DMS).
intros M5 model5 MI5 SBM5 _.
pose proof (same_but_materialized_trans _ _ _ (same_but_materialized_trans _ _ _ SBM1 SBM3) SBM5) as SBMT.
rewrite <- (proj2 (sbm_fds model model5 SBMT)).
apply (rz_exit_at_lit_lz ASEGS scfg R4 (Z_to_bv 64 0x11546c) M5 rom model5 ECALLW st fetch_exitA is_ecall_ECALLW).
- rewrite (sbm_halted_eq _ _ SBMT). exact Hh.
- left. exact Dr17.
- eapply eq_trans; [exact Dr10|]. cbn [VD]. rewrite Z_to_bv_bv_unsigned. exact G10.
- exact Hst.
Qed.
#[using="L C IL HIok ICok ILY Hsp DL Hex"] Lemma exit_run_4B : ltac2:(TCodec.tc2 tcn__Jb0DrvExit "TM'6'<'A%2211%411&Q?%611&Q='S9yR0%211'9y8%511%311p051'L&Q0y5%2219&QAr;r:r9r8r7r6r4r2%9887654321&Q:&Q>%1297%3219'?&R=zr5%3221&R?+X0%2241%8241%827@&RA+2+R0%3221%92E1%?261'@&QL(S7+1(>%33Q521%52Q11&S8+QRclH%22QB1%:3QB41%93Q;@7%;2Q81%62QFQ8%>3QF21+4%>3Q@1<%@2Q>1+V^Rf0%<2QL1%D3QL31r<+:%E3QG1C%G231%B2R2QE%J3R221%R=1R0%R311&QN&R8+VbRh0%I2R91u8%544QK21(2&G%124H%32;1%Q73;51&QG+3%221R4&QF%11R7'K%RE11&M&NrA%211%Q<2RLQ@%5221(J%113%D2:1%QH3:41'R5vS4(I&QMvRK+QRejL%QH2S81rC&QO%11Q4%756B431rB%:221&R1&R3&R4u3%211%42R81&R2r?%R72SG1&O%11<%5231%<271%J4QEI>1p0L1p0Q91p0Q<1p0Q@1p0QN1p0R51p0R<1p0RA1p0RM1p0S51tR:T1S?1p0SD1pUDT@1pVFTA1pV>TB1pTDTC1pR>T31pV0T71pR4T91p2TE1pUFTC1pQ<TE1pQ:TH1").
Proof.
intros LB LK cr A M model R S st tid canz (D & HS1 & HS2 & HS16 & WIN & IMGc & (XC & TIDC & HTr & DESC)) MV Hst Hcan G1 G2 G4 G10 CANc SO SOX FD1.
pose proof Hsp as Hsp'. destruct SO as (_ & SObufsz & _ & SOwpos & SOwbase & SOlock & _ & FW & BW & BC). destruct SOX as (SOwrite & SOfd & SObuf & SOrpos & SOrend).
set (V := fun n : nat => match n with 2%nat => S | 44%nat => tid | 40%nat => canz | _ => 0 end).
assert (HS64 : 0 <= V 2%nat < 2 ^ 64) by (cbn [V]; clear - Hsp' HS1 HS2; lia).
assert (HT64 : 0 <= V 44%nat < 2 ^ 64) by (cbn [V]; clear - HTr; lia).
assert (HSr : 140735332552704 <= V 2%nat <= 140737488355328) by (cbn [V]; clear - Hsp' HS1 HS2; lia).
assert (HSa : AS0DRVP_dpX4B_pre.aligned (V 2%nat) 16) by (cbn [V]; exact HS16).
assert (CWR : L5Defs.L5.writable ASEGS MV (V 2%nat - 320) 320).
{ cbn [V]. intros d k Hd Hk. apply (WIN (S - 320) 320); clear - Hsp' HS1 HS2 Hd Hk; lia. }
assert (CDF : L5Defs.L5.defined MV (V 2%nat - 320) 320).
{ cbn [V]. intros i Hi. apply (store_ok_defined sp0); [clear - Hsp' HS1 HS2 Hi; lia|]. apply (WIN (S - 320) 320); clear - Hsp' HS1 HS2 Hi; lia. }
assert (WSG : forall a (n : nat), wseg_ok ASEGS (Z_to_bv 64 a) n = true -> (0 <=? a) && (a + Z.of_nat n <=? 2 ^ 63) = true -> L5Defs.L5.writable ASEGS MV a (Z.of_nat n)).
{ intros a n W Hb. apply andb_prop in Hb as (B1 & B2). apply Z.leb_le in B1, B2. exact (wsg_writable MV a n W B1 B2). }
assert (SHW : forall a n, ((2147468844 <=? a) && (a + n <=? 2147469096) || (2147611092 <=? a) && (a + n <=? 2147611248)) = true -> L5Defs.L5.writable ASEGS MV a n)
by (intros a n Hb; exact (sh_writable _ _ _ _ _ _ a n D Hb)).
assert (STC : forall (i : nat) a n v, nth_error EX_CELLS i = Some (a, n, v) -> rdn ASEGS MV (Z_to_bv 64 a) (Z.to_nat n) = Some (word_to_le_bytes (Z.to_nat n) (Z_to_bv 64 v)))
by (intros i a n v Hn; exact (ex_cell_vis _ _ _ _ _ _ a n v D (nth_error_In _ _ Hn))).
assert (STC1 : forall (i : nat) a v, nth_error EX_CELLS i = Some (a, 1, v) -> (0 <=? v) && (v <? 2 ^ 64) = true -> rdn ASEGS MV (Z_to_bv 64 a) 1 = Some [Z_to_bv 8 v]).
{ intros i a v Hn Hb. apply andb_prop in Hb as (B1 & B2). apply Z.leb_le in B1. apply Z.ltb_lt in B2. rewrite <- (ArtMem.art_bytes1 v (conj B1 B2)). exact (STC i a 1 v Hn). }
assert (XCC : forall (i : nat) a n v, nth_error XC_CELLS_B i = Some (a, n, v) -> rdn ASEGS MV (Z_to_bv 64 a) (Z.to_nat n) = Some (word_to_le_bytes (Z.to_nat n) (Z_to_bv 64 v)))
by (intros i a n v Hn; exact (cells_at_nth MV XC_CELLS_B i a n v XC Hn)).
assert (XCC1 : forall (i : nat) a v, nth_error XC_CELLS_B i = Some (a, 1, v) -> (0 <=? v) && (v <? 2 ^ 64) = true -> rdn ASEGS MV (Z_to_bv 64 a) 1 = Some [Z_to_bv 8 v]).
{ intros i a v Hn Hb. apply andb_prop in Hb as (B1 & B2). apply Z.leb_le in B1. apply Z.ltb_lt in B2. rewrite <- (ArtMem.art_bytes1 v (conj B1 B2)). exact (XCC i a 1 v Hn). }
assert (DSC : forall a (n : nat) bs, rdn ASEGS (fun _ => None) (Z_to_bv 64 a) n = Some bs -> (0x138ea0 <=? a) && (a + Z.of_nat n <=? 0x139380) = true -> rdn ASEGS MV (Z_to_bv 64 a) n = Some bs).
{ intros a n bs Hr Hb. apply andb_prop in Hb as (B1 & B2). apply Z.leb_le in B1, B2. apply (img_cell MV a n bs Hr); [lia | lia|]. intros i Hi. apply DESC. lia. }
destruct (AS0DRVP_dpX4B_pre.dpX4B_pre_conc fx R MV V HS64 Hcan
HT64 G1 G2 G4 HSr HSa
CWR CDF IMGc (WSG 1282944 8%nat ltac:(vm_compute; reflexivity) eq_refl) (WSG 1283024 1%nat ltac:(vm_compute; reflexivity) eq_refl) (WSG 1286896 8%nat ltac:(vm_compute; reflexivity) eq_refl)
(WSG 6884112 1%nat ltac:(vm_compute; reflexivity) eq_refl) (WSG 6884120 4%nat ltac:(vm_compute; reflexivity) eq_refl) (WSG 6884128 8%nat ltac:(vm_compute; reflexivity) eq_refl) (WSG 6884656 4%nat ltac:(vm_compute; reflexivity) eq_refl) (SHW 2147468844 1 eq_refl) (SHW 2147468845 1 eq_refl)
(SHW 2147468846 1 eq_refl) (SHW 2147468847 1 eq_refl) (SHW 2147468856 1 eq_refl) (SHW 2147468857 1 eq_refl) (SHW 2147468858 1 eq_refl) (SHW 2147468859 1 eq_refl)
(SHW 2147468860 1 eq_refl) (SHW 2147468860 4 eq_refl) (SHW 2147468861 1 eq_refl) (SHW 2147468862 1 eq_refl) (SHW 2147468863 1 eq_refl) (SHW 2147468864 4 eq_refl)
(SHW 2147468868 1 eq_refl) (SHW 2147468868 4 eq_refl) (SHW 2147468869 1 eq_refl) (SHW 2147468870 1 eq_refl) (SHW 2147468871 1 eq_refl) (SHW 2147468916 1 eq_refl)
(SHW 2147468917 1 eq_refl) (SHW 2147468918 1 eq_refl) (SHW 2147468919 1 eq_refl) (SHW 2147468920 1 eq_refl) (SHW 2147468921 1 eq_refl) (SHW 2147468922 1 eq_refl)
(SHW 2147468923 1 eq_refl) (SHW 2147468924 1 eq_refl) (SHW 2147468925 1 eq_refl) (SHW 2147468926 1 eq_refl) (SHW 2147468927 1 eq_refl) (SHW 2147468928 1 eq_refl)
(SHW 2147468929 1 eq_refl) (SHW 2147468930 1 eq_refl) (SHW 2147468931 1 eq_refl) (SHW 2147468932 1 eq_refl) (SHW 2147468932 4 eq_refl) (SHW 2147468933 1 eq_refl)
(SHW 2147468934 1 eq_refl) (SHW 2147468935 1 eq_refl) (SHW 2147468936 4 eq_refl) (SHW 2147468940 1 eq_refl) (SHW 2147468940 4 eq_refl) (SHW 2147468941 1 eq_refl)
(SHW 2147468942 1 eq_refl) (SHW 2147468943 1 eq_refl) (SHW 2147468944 1 eq_refl) (SHW 2147468944 4 eq_refl) (SHW 2147468945 1 eq_refl) (SHW 2147468946 1 eq_refl)
(SHW 2147468947 1 eq_refl) (SHW 2147468948 4 eq_refl) (SHW 2147468952 4 eq_refl) (SHW 2147468956 1 eq_refl) (SHW 2147468956 4 eq_refl) (SHW 2147468957 1 eq_refl)
(SHW 2147468958 1 eq_refl) (SHW 2147468959 1 eq_refl) (SHW 2147468960 1 eq_refl) (SHW 2147468960 4 eq_refl) (SHW 2147468961 1 eq_refl) (SHW 2147468962 1 eq_refl)
(SHW 2147468963 1 eq_refl) (SHW 2147468964 4 eq_refl) (SHW 2147468968 4 eq_refl) (SHW 2147468972 1 eq_refl) (SHW 2147468972 4 eq_refl) (SHW 2147468973 1 eq_refl)
(SHW 2147468974 1 eq_refl) (SHW 2147468975 1 eq_refl) (SHW 2147468976 1 eq_refl) (SHW 2147468977 1 eq_refl) (SHW 2147468978 1 eq_refl) (SHW 2147468979 1 eq_refl)
(SHW 2147468980 1 eq_refl) (SHW 2147468980 4 eq_refl) (SHW 2147468981 1 eq_refl) (SHW 2147468982 1 eq_refl) (SHW 2147468983 1 eq_refl) (SHW 2147468984 4 eq_refl)
(SHW 2147468988 1 eq_refl) (SHW 2147468988 4 eq_refl) (SHW 2147468989 1 eq_refl) (SHW 2147468990 1 eq_refl) (SHW 2147468991 1 eq_refl) (SHW 2147468992 1 eq_refl)
(SHW 2147468992 4 eq_refl) (SHW 2147468993 1 eq_refl) (SHW 2147468994 1 eq_refl) (SHW 2147468995 1 eq_refl) (SHW 2147468996 4 eq_refl) (SHW 2147469000 4 eq_refl)
(SHW 2147469004 1 eq_refl) (SHW 2147469004 4 eq_refl) (SHW 2147469005 1 eq_refl) (SHW 2147469006 1 eq_refl) (SHW 2147469007 1 eq_refl) (SHW 2147469008 1 eq_refl)
(SHW 2147469008 4 eq_refl) (SHW 2147469009 1 eq_refl) (SHW 2147469010 1 eq_refl) (SHW 2147469011 1 eq_refl) (SHW 2147469012 4 eq_refl) (SHW 2147469016 4 eq_refl)
(SHW 2147469020 1 eq_refl) (SHW 2147469020 4 eq_refl) (SHW 2147469021 1 eq_refl) (SHW 2147469022 1 eq_refl) (SHW 2147469023 1 eq_refl) (SHW 2147469024 1 eq_refl)
(SHW 2147469024 4 eq_refl) (SHW 2147469025 1 eq_refl) (SHW 2147469026 1 eq_refl) (SHW 2147469027 1 eq_refl) (SHW 2147469028 4 eq_refl) (SHW 2147469032 1 eq_refl)
(SHW 2147469032 4 eq_refl) (SHW 2147469033 1 eq_refl) (SHW 2147469034 1 eq_refl) (SHW 2147469035 1 eq_refl) (SHW 2147469036 1 eq_refl) (SHW 2147469036 4 eq_refl)
(SHW 2147469037 1 eq_refl) (SHW 2147469038 1 eq_refl) (SHW 2147469039 1 eq_refl) (SHW 2147469040 4 eq_refl) (SHW 2147469044 1 eq_refl) (SHW 2147469044 4 eq_refl)
(SHW 2147469045 1 eq_refl) (SHW 2147469046 1 eq_refl) (SHW 2147469047 1 eq_refl) (SHW 2147469048 1 eq_refl) (SHW 2147469048 4 eq_refl) (SHW 2147469049 1 eq_refl)
(SHW 2147469050 1 eq_refl) (SHW 2147469051 1 eq_refl) (SHW 2147469052 4 eq_refl) (SHW 2147469056 1 eq_refl) (SHW 2147469056 4 eq_refl) (SHW 2147469057 1 eq_refl)
(SHW 2147469058 1 eq_refl) (SHW 2147469059 1 eq_refl) (SHW 2147469060 1 eq_refl) (SHW 2147469060 4 eq_refl) (SHW 2147469061 1 eq_refl) (SHW 2147469062 1 eq_refl)
(SHW 2147469063 1 eq_refl) (SHW 2147469064 4 eq_refl) (SHW 2147469068 4 eq_refl) (SHW 2147469072 1 eq_refl) (SHW 2147469072 4 eq_refl) (SHW 2147469073 1 eq_refl)
(SHW 2147469074 1 eq_refl) (SHW 2147469075 1 eq_refl) (SHW 2147469076 1 eq_refl) (SHW 2147469077 1 eq_refl) (SHW 2147469078 1 eq_refl) (SHW 2147469079 1 eq_refl)
(SHW 2147469080 1 eq_refl) (SHW 2147469081 1 eq_refl) (SHW 2147469082 1 eq_refl) (SHW 2147469083 1 eq_refl) (SHW 2147469084 1 eq_refl) (SHW 2147469084 4 eq_refl)
(SHW 2147469085 1 eq_refl) (SHW 2147469086 1 eq_refl) (SHW 2147469087 1 eq_refl) (SHW 2147469088 4 eq_refl) (SHW 2147469092 1 eq_refl) (SHW 2147469092 4 eq_refl)
(SHW 2147469093 1 eq_refl) (SHW 2147469094 1 eq_refl) (SHW 2147469095 1 eq_refl) (SHW 2147611092 1 eq_refl) (SHW 2147611092 4 eq_refl) (SHW 2147611093 1 eq_refl)
(SHW 2147611094 1 eq_refl) (SHW 2147611095 1 eq_refl) (SHW 2147611096 4 eq_refl) (SHW 2147611100 4 eq_refl) (SHW 2147611104 4 eq_refl) (SHW 2147611108 4 eq_refl)
(SHW 2147611112 4 eq_refl) (SHW 2147611116 4 eq_refl) (SHW 2147611120 8 eq_refl) (SHW 2147611128 8 eq_refl) (SHW 2147611136 8 eq_refl) (SHW 2147611144 8 eq_refl)
(SHW 2147611152 8 eq_refl) (SHW 2147611160 8 eq_refl) (SHW 2147611168 8 eq_refl) (SHW 2147611176 8 eq_refl) (SHW 2147611184 8 eq_refl) (SHW 2147611192 8 eq_refl)
(SHW 2147611200 8 eq_refl) (SHW 2147611208 8 eq_refl) (SHW 2147611216 4 eq_refl) (SHW 2147611220 4 eq_refl) (SHW 2147611224 4 eq_refl) (SHW 2147611228 4 eq_refl)
(SHW 2147611232 4 eq_refl) (SHW 2147611236 4 eq_refl) (SHW 2147611240 1 eq_refl) (SHW 2147611240 4 eq_refl) (SHW 2147611241 1 eq_refl) (SHW 2147611242 1 eq_refl)
(SHW 2147611243 1 eq_refl) TIDC HTr (XCC 0%nat 6884656 4 0 eq_refl) (XCC1 1%nat 6884691 0 eq_refl eq_refl) (XCC 2%nat 6884128 8 6884136 eq_refl)
(XCC 3%nat 6884120 4 4 eq_refl) (XCC 23%nat 6884168 8 447508 eq_refl) (XCC 25%nat 6884424 8 0 eq_refl) (XCC 6%nat 6884116 4 0 eq_refl) (STC1 11%nat 1286740 0 eq_refl eq_refl) (XCC 22%nat 6884160 8 860168 eq_refl)
(XCC 24%nat 6884416 8 1280728 eq_refl) (XCC 27%nat 6884152 8 1136392 eq_refl) (XCC 28%nat 6884408 8 686244 eq_refl) (XCC1 26%nat 6746260 0 eq_refl eq_refl) (XCC 4%nat 6884144 8 1136392 eq_refl) (XCC 5%nat 6884400 8 618204 eq_refl)
(STC1 10%nat 1894624 0 eq_refl eq_refl) (XCC 7%nat 6884136 8 0 eq_refl) (STC1 3%nat 1283024 0 eq_refl eq_refl) (STC 0%nat 1270192 8 1270192 eq_refl) (STC 2%nat 1282944 8 1 eq_refl) (STC 4%nat 1286736 4 1 eq_refl)
(STC 5%nat 1286896 8 0 eq_refl) (STC1 8%nat 1300248 1 eq_refl eq_refl) (STC 7%nat 1296952 8 2147450880 eq_refl) (DSC 1281696 8%nat (word_to_le_bytes 8 (Z_to_bv 64 143712)) ltac:(img_rd) eq_refl) (DSC 1281712 1%nat [Z_to_bv 8 32] ltac:(img_rd) eq_refl) (STC1 6%nat 1295004 1 eq_refl eq_refl)
(DSC 1281712 8%nat (word_to_le_bytes 8 (Z_to_bv 64 32)) ltac:(img_rd) eq_refl) (STC 9%nat 1893856 8 18446744073709551615 eq_refl) (STC 1%nat 1270704 8 1207272 eq_refl) (DSC 1281752 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1281760 8%nat (word_to_le_bytes 8 (Z_to_bv 64 143808)) ltac:(img_rd) eq_refl) (DSC 1281776 1%nat [Z_to_bv 8 32] ltac:(img_rd) eq_refl)
(DSC 1281776 8%nat (word_to_le_bytes 8 (Z_to_bv 64 32)) ltac:(img_rd) eq_refl) (DSC 1281816 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1281824 8%nat (word_to_le_bytes 8 (Z_to_bv 64 143840)) ltac:(img_rd) eq_refl) (DSC 1281840 1%nat [Z_to_bv 8 96] ltac:(img_rd) eq_refl) (DSC 1281840 8%nat (word_to_le_bytes 8 (Z_to_bv 64 96)) ltac:(img_rd) eq_refl) (DSC 1281880 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl)
(DSC 1281888 8%nat (word_to_le_bytes 8 (Z_to_bv 64 144288)) ltac:(img_rd) eq_refl) (DSC 1281904 1%nat [Z_to_bv 8 32] ltac:(img_rd) eq_refl) (DSC 1281904 8%nat (word_to_le_bytes 8 (Z_to_bv 64 32)) ltac:(img_rd) eq_refl) (DSC 1281944 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1281952 8%nat (word_to_le_bytes 8 (Z_to_bv 64 144320)) ltac:(img_rd) eq_refl) (DSC 1281968 1%nat [Z_to_bv 8 64] ltac:(img_rd) eq_refl)
(DSC 1281968 8%nat (word_to_le_bytes 8 (Z_to_bv 64 64)) ltac:(img_rd) eq_refl) (DSC 1282008 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1282016 8%nat (word_to_le_bytes 8 (Z_to_bv 64 144384)) ltac:(img_rd) eq_refl) (DSC 1282032 1%nat [Z_to_bv 8 32] ltac:(img_rd) eq_refl) (DSC 1282032 8%nat (word_to_le_bytes 8 (Z_to_bv 64 32)) ltac:(img_rd) eq_refl) (DSC 1282072 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl)
(DSC 1282080 8%nat (word_to_le_bytes 8 (Z_to_bv 64 144416)) ltac:(img_rd) eq_refl) (DSC 1282096 1%nat [Z_to_bv 8 96] ltac:(img_rd) eq_refl) (DSC 1282096 8%nat (word_to_le_bytes 8 (Z_to_bv 64 96)) ltac:(img_rd) eq_refl) (DSC 1282136 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1282144 8%nat (word_to_le_bytes 8 (Z_to_bv 64 144512)) ltac:(img_rd) eq_refl) (DSC 1282160 1%nat [Z_to_bv 8 128] ltac:(img_rd) eq_refl)
(DSC 1282160 8%nat (word_to_le_bytes 8 (Z_to_bv 64 128)) ltac:(img_rd) eq_refl) (DSC 1282200 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1282208 8%nat (word_to_le_bytes 8 (Z_to_bv 64 144640)) ltac:(img_rd) eq_refl) (DSC 1282224 1%nat [Z_to_bv 8 128] ltac:(img_rd) eq_refl) (DSC 1282224 8%nat (word_to_le_bytes 8 (Z_to_bv 64 128)) ltac:(img_rd) eq_refl) (DSC 1282264 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl)
(DSC 1282272 8%nat (word_to_le_bytes 8 (Z_to_bv 64 144768)) ltac:(img_rd) eq_refl) (DSC 1282288 1%nat [Z_to_bv 8 32] ltac:(img_rd) eq_refl) (DSC 1282288 8%nat (word_to_le_bytes 8 (Z_to_bv 64 32)) ltac:(img_rd) eq_refl) (DSC 1282328 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1282336 8%nat (word_to_le_bytes 8 (Z_to_bv 64 144800)) ltac:(img_rd) eq_refl) (DSC 1282352 1%nat [Z_to_bv 8 96] ltac:(img_rd) eq_refl)
(DSC 1282352 8%nat (word_to_le_bytes 8 (Z_to_bv 64 96)) ltac:(img_rd) eq_refl) (DSC 1282392 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1282400 8%nat (word_to_le_bytes 8 (Z_to_bv 64 144896)) ltac:(img_rd) eq_refl) (DSC 1282416 1%nat [Z_to_bv 8 128] ltac:(img_rd) eq_refl) (DSC 1282416 8%nat (word_to_le_bytes 8 (Z_to_bv 64 128)) ltac:(img_rd) eq_refl) (DSC 1282456 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl)
(DSC 1282464 8%nat (word_to_le_bytes 8 (Z_to_bv 64 145024)) ltac:(img_rd) eq_refl) (DSC 1282480 1%nat [Z_to_bv 8 128] ltac:(img_rd) eq_refl) (DSC 1282480 8%nat (word_to_le_bytes 8 (Z_to_bv 64 128)) ltac:(img_rd) eq_refl) (DSC 1282520 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1282528 8%nat (word_to_le_bytes 8 (Z_to_bv 64 145152)) ltac:(img_rd) eq_refl) (DSC 1282544 1%nat [Z_to_bv 8 96] ltac:(img_rd) eq_refl)
(DSC 1282544 8%nat (word_to_le_bytes 8 (Z_to_bv 64 96)) ltac:(img_rd) eq_refl) (DSC 1282584 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1282592 8%nat (word_to_le_bytes 8 (Z_to_bv 64 145248)) ltac:(img_rd) eq_refl) (DSC 1282608 1%nat [Z_to_bv 8 96] ltac:(img_rd) eq_refl) (DSC 1282608 8%nat (word_to_le_bytes 8 (Z_to_bv 64 96)) ltac:(img_rd) eq_refl) (DSC 1282648 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl)
(DSC 1282656 8%nat (word_to_le_bytes 8 (Z_to_bv 64 145344)) ltac:(img_rd) eq_refl) (DSC 1282672 1%nat [Z_to_bv 8 96] ltac:(img_rd) eq_refl) (DSC 1282672 8%nat (word_to_le_bytes 8 (Z_to_bv 64 96)) ltac:(img_rd) eq_refl) (DSC 1282712 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1282720 8%nat (word_to_le_bytes 8 (Z_to_bv 64 145440)) ltac:(img_rd) eq_refl) (DSC 1282736 1%nat [Z_to_bv 8 128] ltac:(img_rd) eq_refl)
(DSC 1282736 8%nat (word_to_le_bytes 8 (Z_to_bv 64 128)) ltac:(img_rd) eq_refl) (DSC 1282776 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1282784 8%nat (word_to_le_bytes 8 (Z_to_bv 64 145568)) ltac:(img_rd) eq_refl) (DSC 1282800 1%nat [Z_to_bv 8 64] ltac:(img_rd) eq_refl) (DSC 1282800 8%nat (word_to_le_bytes 8 (Z_to_bv 64 64)) ltac:(img_rd) eq_refl) (DSC 1282840 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl)
(DSC 1282848 8%nat (word_to_le_bytes 8 (Z_to_bv 64 145632)) ltac:(img_rd) eq_refl) (DSC 1282864 1%nat [Z_to_bv 8 96] ltac:(img_rd) eq_refl) (DSC 1282864 8%nat (word_to_le_bytes 8 (Z_to_bv 64 96)) ltac:(img_rd) eq_refl) (DSC 1282904 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (XCC 8%nat 6886088 8 0 eq_refl) (XCC 9%nat 1281648 8 1281416 eq_refl)
(XCC 10%nat 1281556 4 4294967295 eq_refl) (XCC 11%nat 1281456 8 0 eq_refl) (XCC 12%nat 1281472 8 0 eq_refl) (XCC 13%nat 1281424 8 0 eq_refl) (XCC 14%nat 1281432 8 0 eq_refl) (XCC 15%nat 1281408 8 1281176 eq_refl)
SOlock SOwpos SOwbase SOwrite CANc SOfd) as
(fx1 & R1 & MV1 & XGR & _ & XFRZ & XMS & _ & _ & Xr2 & _ & _ & _ & Xr8 & Xr9 & Xr10 & Xr11 & Xr12 & _ & _ & _ & _ & Xr17 & Xr18 & Xr19 & Xr21 & Xr22 & _ & Xm112 & Xm120 & Xm128 & Xm136 & Xm104 & Xm96 & Xm88 & Xm80 & Xm72 & Xm64 & Xm56 & Xm48 & Xm40 & Xm32 & Xm24 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _).
unfold V in XFRZ, XMS; cbn beta iota in XFRZ, XMS. cbn [V] in *.
pose proof (dinv_lzinv scfg L ar C IL HI HIok sp0 DL M0 _ _ _ _ _ _ D) as LZ. pose proof LZ as (HH & HL & HA & HM & Hh).
set (good := fun i : Z => i < 1282944 \/ 1286904 <= i < 6884112 \/ 6884136 <= i < 6884656 \/ 6884660 <= i < 2147450880).
assert (FRX : forall i, 0 <= i -> good i -> MV1 (Z_to_bv 64 i) = MV (Z_to_bv 64 i)).
{ intros i Hi Hg. apply XFRZ; [unfold good in Hg; clear - Hi Hg; lia | ..]; (intros X; unfold good in Hg; clear - Hsp' HS1 HS2 Hi Hg X; lia). }
apply (msteps_vis_fx scfg (ahid A model) A fx fx1 R (Z_to_bv 64 0x11575c) M R1 (Z_to_bv 64 0x11d13c) MV1 model _ LZ XMS).
intros M1 model1 MI1 SBM1 VIS1.
assert (LITX : forall a (n : nat) bs, rdn ASEGS MV (Z_to_bv 64 a) n = Some bs ->
(0 <=? a) && ((a + Z.of_nat n <=? 1282944) || ((1286904 <=? a) && (a + Z.of_nat n <=? 6884112)) || ((6884660 <=? a) && (a + Z.of_nat n <=? 2147450880))) = true ->
rdn ASEGS MV1 (Z_to_bv 64 a) n = Some bs).
{ intros a n bs Hr Hb. apply andb_prop in Hb as (B1 & B2). apply Z.leb_le in B1. rewrite !orb_true_iff, !andb_true_iff, !Z.leb_le in B2.
apply (rdn_tr MV MV1 a n bs Hr B1); [lia|]. intros i Hi. apply FRX; [lia|]. unfold good. clear - B1 B2 Hi. lia. }
assert (DATA : rdn ASEGS MV1 (Z_to_bv 64 6886112) (Z.to_nat (2 * 3)) = Some (zero_lines 3%nat)).
{ apply (LITX 6886112 (Z.to_nat (2 * 3))); [|reflexivity]. change (Z.to_nat (2 * 3)) with (2 * 3%nat)%nat.
destruct (BC 0 ltac:(lia)) as (B0a & B0b). destruct (BC 1 ltac:(lia)) as (B1a & B1b). destruct (BC 2 ltac:(lia)) as (B2a & B2b). cbn [zero_lines].
apply rdn_cons1; [lia | exact B0a|]. apply rdn_cons1; [lia | exact B0b|]. apply rdn_cons1; [lia | exact B1a|]. apply rdn_cons1; [lia | exact B1b|]. apply rdn_cons1; [lia | exact B2a|]. apply rdn_cons1; [lia | exact B2b|]. reflexivity. }
set (q := S - 136) in *.
assert (Hq : 0 <= q /\ q <= q + 32 /\ q + 32 + 16 <= 2 ^ 47) by (unfold q; clear - Hsp' HS1 HS2; lia).
assert (Hf : 0 <= 1281176 /\ (1281176 + 124 <= q \/ q + 32 + 16 <= 1281176 + 120) /\ 1281176 + 124 < 2 ^ 63) by (unfold q; clear - Hsp' HS1 HS2; lia).
assert (NLq : forall x, q <= x < q + 32 -> page_in_ranges (page_base_of x) (m_vm_lazy model) = false).
{ intros x Hx. apply (nl_pt scfg L ar C IL HI HIok sp0 Hsp DL M0 _ _ _ _ _ _ x D); unfold q in Hx; clear - Hsp' HS1 HS2 Hx; lia. }
assert (WIN1 : forall a n, usp - 8388608 <= a -> a + n <= usp -> forall d (k : nat), 0 <= d -> d + Z.of_nat k <= n -> store_ok ASEGS MV1 (Z_to_bv 64 (a + d)) k = true)
by (intros a n H1 H2 d k Hd Hk; apply (store_ok_mono ASEGS k MV MV1 _ XGR); apply (WIN a n); assumption).
unfold W. rewrite <- (app_nil_r (zero_lines 3%nat)).
apply (wv_loop scfg (ahid A model) A HH (m_vm_lazy model) HL HA 1281176 1 ltac:(lia) q (q + 32) Hq Hf NLq (t_exit (Z_to_bv 64 st) (m_fs model)) (t_exit_has_nil _ _)
(2 * 3%nat)%nat true R1 M1 model1 q 2 6886112 (2 * 3) 0 0 (zero_lines 3%nat) []).
{ cbn. lia. }
{ exact (sbm_lazy_eq _ _ SBM1). }
{ exact MI1. }
{ rewrite (sbm_halted_eq _ _ SBM1). exact Hh. }
{ rewrite (sbm_fds' _ _ SBM1). exact FD1. }
{ unfold wv_regs. repeat split; assumption. }
{ rewrite VIS1. unfold wv_iov. split; [lia|]. split; [lia|]. split; [right; reflexivity|].
split; [exact Xm136|]. split; [replace (q + 8) with (S - 128) by (unfold q; ring); exact Xm128|].
split; [replace (Z_to_bv 64 q) with (Z_to_bv 64 (q + 0)) by (f_equal; lia); apply (WIN1 q 32); [unfold q; clear - Hsp' HS1 HS2; lia | unfold q; clear - Hsp' HS1 HS2; lia | lia | cbn; lia]|].
split; [unfold wv_buf; split; [lia|]; split; [lia|]; split; [lia|]; split; [right; left; unfold q; clear - Hsp' HS1 HS2; lia|]; split; [exact DATA|];
intros x Hx; apply (nl_pt scfg L ar C IL HI HIok sp0 Hsp DL M0 _ _ _ _ _ _ x D); lia|].
split; [intros X; discriminate X|]. intros _.
split; [replace (q + 16) with (S - 120) by (unfold q; ring); exact Xm120|].
split; [replace (q + 24) with (S - 112) by (unfold q; ring); exact Xm112|].
split; [|lia].
unfold wv_buf. split; [lia|]. split; [lia|]. split; [lia|]. split; [left; reflexivity|]. split; [reflexivity|]. intros x Hx. lia. }
{ lia. }
{ rewrite VIS1. exact (LITX _ _ _ SOfd eq_refl). }
intros R3 M3 model3 MI3 SBM3 KR3 _ FRV3 _ GRV3. rewrite VIS1 in FRV3, GRV3.
set (MV3 := mrestrict (ahid A model) M3) in *.
assert (LIT3 : forall a (n : nat) bs, rdn ASEGS MV (Z_to_bv 64 a) n = Some bs ->
(0 <=? a) && ((a + Z.of_nat n <=? 1282944) || ((1286904 <=? a) && (a + Z.of_nat n <=? 6884112)) || ((6884660 <=? a) && (a + Z.of_nat n <=? 2147450880))) = true ->
rdn ASEGS MV3 (Z_to_bv 64 a) n = Some bs).
{ intros a n bs Hr Hb. pose proof (LITX a n bs Hr Hb) as Y. apply andb_prop in Hb as (B1 & B2). apply Z.leb_le in B1. rewrite !orb_true_iff, !andb_true_iff, !Z.leb_le in B2.
apply (rdn_tr MV1 MV3 a n bs Y B1); [lia|]. intros i Hi. apply FRV3; [lia|]. unfold q. clear - Hsp' HS1 HS2 B1 B2 Hi. lia. }
assert (cellS : forall off k (n : nat) bs, rdn ASEGS MV1 (Z_to_bv 64 (S - k)) n = Some bs ->
(off + k =? 144) && (Z.of_nat n <=? k) && (k <=? 104) = true -> rdn ASEGS MV3 (Z_to_bv 64 (S - 144 + off)) n = Some bs).
{ intros off k n bs Hr Hb. apply andb_prop in Hb as (Hb & Hb3). apply andb_prop in Hb as (Hb1 & Hb2).
apply Z.eqb_eq in Hb1. apply Z.leb_le in Hb2, Hb3. replace (S - 144 + off) with (S - k) by lia.
apply (rdn_tr MV1 MV3 _ _ _ Hr); [clear - Hsp' HS1 HS2 Hb3; lia | clear - Hsp' HS1 HS2 Hb2; lia|].
intros i Hi. apply FRV3; unfold q; clear - Hsp' HS1 HS2 Hb2 Hb3 Hi; lia. }
assert (WIN3 : forall a n, usp - 8388608 <= a -> a + n <= usp -> forall d (k : nat), 0 <= d -> d + Z.of_nat k <= n -> store_ok ASEGS MV3 (Z_to_bv 64 (a + d)) k = true)
by (intros a n H1 H2 d k Hd Hk; apply (store_ok_mono ASEGS k MV1 MV3 _ GRV3); apply (WIN1 a n); assumption).
assert (FW3 : forall a n, 1281176 <= a -> a + n <= 1281176 + 232 -> forall d (k : nat), 0 <= d -> d + Z.of_nat k <= n -> store_ok ASEGS MV3 (Z_to_bv 64 (a + d)) k = true)
by (intros a n H1 H2 d k Hd Hk; apply (store_ok_mono ASEGS k MV1 MV3 _ GRV3); apply (store_ok_mono ASEGS k MV MV1 _ XGR); apply (FW a n); assumption).
assert (IMG3 : forall i, 65536 <= i < 1269760 -> MV3 (Z_to_bv 64 i) = None).
{ intros i Hi. rewrite FRV3; [rewrite FRX; [apply IMGc; exact Hi | lia | unfold good; lia] | lia | unfold q; clear - Hsp' HS1 HS2 Hi; lia]. }
set (VD := fun n : nat => match n with
| 2%nat => S - 144 | 40%nat => canz
| 9%nat => bv_unsigned (getr R (Z_to_bv 5 (Z.of_nat 9))) | 10%nat => bv_unsigned (getr R (Z_to_bv 5 (Z.of_nat 10)))
| 18%nat => bv_unsigned (getr R (Z_to_bv 5 (Z.of_nat 18))) | 19%nat => bv_unsigned (getr R (Z_to_bv 5 (Z.of_nat 19)))
| 20%nat => bv_unsigned (getr R (Z_to_bv 5 (Z.of_nat 20))) | 21%nat => bv_unsigned (getr R (Z_to_bv 5 (Z.of_nat 21)))
| 22%nat => bv_unsigned (getr R (Z_to_bv 5 (Z.of_nat 22)))
| 110%nat => bv_unsigned (getr R3 (Z_to_bv 5 (Z.of_nat 10))) | 118%nat => bv_unsigned (getr R3 (Z_to_bv 5 (Z.of_nat 18)))
| 119%nat => bv_unsigned (getr R3 (Z_to_bv 5 (Z.of_nat 19))) | 120%nat => bv_unsigned (getr R3 (Z_to_bv 5 (Z.of_nat 20)))
| 122%nat => bv_unsigned (getr R3 (Z_to_bv 5 (Z.of_nat 22)))
| _ => 0 end).
assert (Dg2 : getr R3 (Z_to_bv 5 (Z.of_nat 2)) = Z_to_bv 64 (VD 2%nat)) by (eapply eq_trans; [exact (KR3 2%bv ltac:(unfold WV_KEEP; cbn [In]; tauto)) | exact Xr2]).
assert (Dg8 : getr R3 (Z_to_bv 5 (Z.of_nat 8)) = Z_to_bv 64 0) by (eapply eq_trans; [exact (KR3 8%bv ltac:(unfold WV_KEEP; cbn [In]; tauto)) | exact Xr8]).
assert (Dg9 : getr R3 (Z_to_bv 5 (Z.of_nat 9)) = Z_to_bv 64 1281176) by (eapply eq_trans; [exact (KR3 9%bv ltac:(unfold WV_KEEP; cbn [In]; tauto)) | exact Xr9]).
assert (Dg21 : getr R3 (Z_to_bv 5 (Z.of_nat 21)) = Z_to_bv 64 6884096) by (eapply eq_trans; [exact (KR3 21%bv ltac:(unfold WV_KEEP; cbn [In]; tauto)) | exact Xr21]).
assert (Dg10 : getr R3 (Z_to_bv 5 (Z.of_nat 10)) = Z_to_bv 64 (VD 110%nat)) by (cbn [VD]; symmetry; apply Z_to_bv_bv_unsigned).
assert (Dg18 : getr R3 (Z_to_bv 5 (Z.of_nat 18)) = Z_to_bv 64 (VD 118%nat)) by (cbn [VD]; symmetry; apply Z_to_bv_bv_unsigned).
assert (Dg19 : getr R3 (Z_to_bv 5 (Z.of_nat 19)) = Z_to_bv 64 (VD 119%nat)) by (cbn [VD]; symmetry; apply Z_to_bv_bv_unsigned).
assert (Dg20 : getr R3 (Z_to_bv 5 (Z.of_nat 20)) = Z_to_bv 64 (VD 120%nat)) by (cbn [VD]; symmetry; apply Z_to_bv_bv_unsigned).
assert (Dg22 : getr R3 (Z_to_bv 5 (Z.of_nat 22)) = Z_to_bv 64 (VD 122%nat)) by (cbn [VD]; symmetry; apply Z_to_bv_bv_unsigned).
assert (HD64 : 0 <= VD 2%nat < 2 ^ 64) by (cbn [VD]; clear - Hsp' HS1 HS2; lia).
assert (HDr : 140735332552704 <= VD 2%nat <= 140737488355328) by (cbn [VD]; clear - Hsp' HS1 HS2; lia).
assert (HDa : AS0DRVP_dpXd_4.aligned (VD 2%nat) 16).
{ cbn [VD]. unfold AS0DRVP_dpXd_4.aligned. clear - HS16. Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). lia.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false). }
assert (DWR : L5Defs.L5.writable ASEGS MV3 (VD 2%nat - 16) 16).
{ cbn [VD]. intros d k Hd Hk. apply (WIN3 (S - 144 - 16) 16); clear - Hsp' HS1 HS2 Hd Hk; lia. }
assert (DDF : L5Defs.L5.defined MV3 (VD 2%nat - 16) 16).
{ cbn [VD]. intros i Hi. apply (store_ok_defined sp0); [clear - Hsp' HS1 HS2 Hi; lia|]. apply (WIN3 (S - 144 - 16) 16); clear - Hsp' HS1 HS2 Hi; lia. }
destruct (AS0DRVP_dpXd_4.dpXd_4_conc fx1 R3 MV3 VD HD64 (u64_range _)
(u64_range _) (u64_range _) (u64_range _) (u64_range _) (u64_range _) (u64_range _)
Hcan (u64_range _) (u64_range _) (u64_range _) (u64_range _) (u64_range _)
Dg2 Dg8 Dg9 Dg10 Dg18 Dg19
Dg20 Dg21 Dg22 HDr HDa DWR
DDF IMG3 (fun d k Hd Hk => FW3 1281208 8 ltac:(lia) ltac:(lia) d k Hd Hk) (fun d k Hd Hk => FW3 1281216 8 ltac:(lia) ltac:(lia) d k Hd Hk) (fun d k Hd Hk => FW3 1281232 8 ltac:(lia) ltac:(lia) d k Hd Hk) (LIT3 1281264 8%nat _ SObuf eq_refl)
(LIT3 1281272 8%nat _ SObufsz eq_refl) (LIT3 6884096 8%nat _ CANc eq_refl) (cellS 40 104 _ _ Xm104 eq_refl) (cellS 104 40 _ _ Xm40 eq_refl) (cellS 96 48 _ _ Xm48 eq_refl) (cellS 88 56 _ _ Xm56 eq_refl)
(cellS 80 64 _ _ Xm64 eq_refl) (cellS 72 72 _ _ Xm72 eq_refl) (cellS 64 80 _ _ Xm80 eq_refl) (cellS 56 88 _ _ Xm88 eq_refl) (cellS 48 96 _ _ Xm96 eq_refl) (LIT3 1281184 8%nat _ SOrpos eq_refl)
(LIT3 1281192 8%nat _ SOrend eq_refl) (LIT3 1281168 8%nat _ (XCC 16%nat 1281168 8 1280936 eq_refl) eq_refl) (LIT3 1281076 4%nat _ (XCC 17%nat 1281076 4 4294967295 eq_refl) eq_refl) (LIT3 1280976 8%nat _ (XCC 18%nat 1280976 8 0 eq_refl) eq_refl) (LIT3 1280992 8%nat _ (XCC 19%nat 1280992 8 0 eq_refl) eq_refl) (LIT3 1280944 8%nat _ (XCC 20%nat 1280944 8 0 eq_refl) eq_refl)
(LIT3 1280952 8%nat _ (XCC 21%nat 1280952 8 0 eq_refl) eq_refl) (cellS 120 24 _ _ Xm24 eq_refl) (cellS 112 32 _ _ Xm32 eq_refl)) as
(fx2 & R4 & MV4 & _ & _ & _ & DMS & _ & _ & _ & _ & _ & Dr10 & _ & _ & Dr17 & _).
unfold VD in DMS; cbn beta iota in DMS.
assert (LZ3 : lzinv ASEGS (ahid A model) A model3).
{ apply (lzinv_sbm ASEGS (ahid A model) A model model3 LZ MI3). exact (same_but_materialized_trans _ _ _ SBM1 SBM3). }
apply (msteps_vis_fx scfg (ahid A model) A fx1 fx2 R3 (Z_to_bv 64 0x11d148) M3 R4 (Z_to_bv 64 0x11546c) MV4 model3 _ LZ3 DMS).
intros M5 model5 MI5 SBM5 _.
pose proof (same_but_materialized_trans _ _ _ (same_but_materialized_trans _ _ _ SBM1 SBM3) SBM5) as SBMT.
rewrite <- (proj2 (sbm_fds model model5 SBMT)).
apply (rz_exit_at_lit_lz ASEGS scfg R4 (Z_to_bv 64 0x11546c) M5 rom model5 ECALLW st fetch_exitA is_ecall_ECALLW).
- rewrite (sbm_halted_eq _ _ SBMT). exact Hh.
- left. exact Dr17.
- eapply eq_trans; [exact Dr10|]. cbn [VD]. rewrite Z_to_bv_bv_unsigned. exact G10.
- exact Hst.
Qed.
End Exit.
End FPX_1.
