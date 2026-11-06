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
PropExec CatExec CatSim SeqExec StoreOk StreamSim ShapeAlg ShapeLaws SpinAlg Hoare AgentLib Spec AsanAcctShape SymExec2 SymExec2Sound SymRun SymDrive SymDriveX
HeapIface HeapIfaceA IcptIfaceA DrvKitA DrvNodesLazyK As0DrvKitA Ja0DrvEntry Ja0Drv_defs Ja0DrvLib Ja0DrvRead Ja0DrvPiece Ja0DiagLoopK Ja0DrvStdio Ja0DrvPrintfK Ja0DrvPrintf1 Ja0DrvExit.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require L5Defs L5KnA ArtMem JatFsInv JatWrapMallocX Ja0RegionPoisoned Ja0AsanMemcpy Ja0DiagStrnlen Ja0DiagKit Ja0DiagGlue.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLia. Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLiaT.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import SecKit. From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__Ja0DiagStrK () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Init.Nat."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics."; "LinuxProcessSemantics.LinuxProcessSem.State."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.AsanAcct."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.HeapIface."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.HeapIfaceA."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Ja0AsanMemcpy."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Ja0DiagStrnlen.DSN."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Ja0DrvLib."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Ja0DrvStdio."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Ja0RegionPoisoned."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec."; "OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Asan.M."; "Stdlib.Lists.List."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["0A"; "1None"; "1Some"; "1app"; "1cons"; "1length"; "1list"; "1nat"; "1nil"; "1option"; "1pair"; "1prod"; "2and"; "2eq"; "2ex"; "2not"]; ["3add"; "4Z"; "0HI"; "0LB"; "0LK"; "5word_to_le_bytes"; "6Model"; "0M"; "0M0"; "0Mx"; "7mrestrict"; "8credit"; "8defined"; "9ahid"; "9ar_sptop"; "9fframe"]; ["9shadow_allowed"; ":mc_icpt_globs"; ";cstr"; ";sn_cells"; "<dinv"; "=DGS_CELLS"; "=DG_CELLS"; ">SB"; "?rdn"; "@loaded_segments"; "AIn"; "Badd"; "Bdiv"; "Ble"; "Blt"; "Bmin"]; ["Bof_nat"; "Bpow"; "Bsub"; "Bto_nat"; "0a"; "0ar"; "0bs"; "0cr"; "0i"; "0model"; "0n"; "0p"; "0path"; "0pz"; "0sp0"; "CZ_to_bv"]; ["Cbv"; "Cbv_unsigned"; "0t8"; "0v"; "0x"]]).
Local Ltac lia := L5FastLiaT.plia2.
Open Scope Z_scope.
Import SX2. Import SX2S.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Lemma rdn_of_defined : ltac2:(TCodec.tc2 tcn__Ja0DiagStrK "R4'R0yR0%211'9y8%511%311p051'7'A&Q=zr1%3221&Q;r2&Q@r3%211%5241&QA+2+QO%3221%>251'<&Q>r5%<11%32A1%52A1&?'=r7&QO%E28D%22Q31%411(1%11Q2%83Q231%:11p0<1pSBQ21'>'6%11Q9%Q<11&Q8&Q9%@2QAGr6%443C21(2%128Q:%G3831&5%12QDQ=%J3QB17%Q2241qS>>1%A2?1p0C1p0Q71p0QC1pS:QH1pSFQJ1pQDQL1").
Proof.
intros Mx n. induction n as [|n IH]; intros a Ha Hn Hd.
- exists []. split; reflexivity.
- destruct (Mx (Z_to_bv 64 a)) as [b|] eqn:Eb; [|exfalso; apply (Hd 0 ltac:(lia)); rewrite Z.add_0_r; exact Eb].
destruct (IH (a + 1) ltac:(lia) ltac:(lia)) as (bs & Hr & Hl).
{ intros i Hi. replace (a + 1 + i) with (a + (1 + i)) by lia. apply Hd. lia. }
exists (b :: bs). split; [|cbn [length]; lia].
apply (rdn_cons1 Mx a b n bs Ha); [cbn [rdn]; rewrite Eb; reflexivity | exact Hr].
Qed.
Section FPX_1. Context {fx : PropExec.FPState}.
Variable scfg : SpuriousCfg.
Section StrK.
Variable L : asan_layout.
Variable ar : asan_run.
Variable C : asan_statics_cells.
Variable IL : icpt_layout.
Variable HI : asan_iface.
Hypothesis HIok : asan_iface_ok L ar C scfg HI.
Variable sp0 : word.
Hypothesis Hsp : 0x7fff80000000 <= bv_unsigned sp0 <= 2 ^ 47.
Hypothesis DL : drv_layoutA L ar IL sp0.
Hypothesis Hdg : incl DG_CELLS (asc_cells C).
Hypothesis Hdgs : incl DGS_CELLS (asc_cells C).
Variable M0 : word -> option byte.
#[local] Notation dinvA := (dinv ar HI sp0 M0).
#[local] Notation usp := (bv_unsigned sp0).
#[using="scfg L C IL HIok Hsp DL"] Lemma str_cstr : ltac2:(TCodec.tc2 tcn__Ja0DiagStrK "S@'6';'A%2211%411&O%611&K'R0yR0%211'9y8%511%311p051'F%A14'Q4vQEvBvQNvHr8r7r6r5r4r3%;::987654321&Q=&R1%12G;%22H5%4221&Q;%52K9&Q@&5%12J;%311%6251+1%8221+@%:221&QA+2+Q?%3221%D251'=%Q91Q3&Q8&Q9&@%B2Q;Mu1%3221%645Q5Q11(2&3(4&QOz%22QE1(8%11QF%63QG31%83QHQ:1%:2QE1%D3C<1&?&Q:%13QM9Q@%311&L%Q>2R4QE%Q82R1QE%Q:11%Q=21Q6%Q>21Q5%63QL51'>'Q2&J&Mr<r:%3221r;%6221r9%QN2RD1r1%;442R81qT6R?1%>2R@1p0@1p0H1p0M1p0QC1p0R41p0R:1pSJRG1pSHRO1pSDRJ1pQ@RL1p2S81pS@S61pQ:S81pQ8S;1").
Proof.
intros LB LK cr A M model p path D Hlo Hhi STR NONUL PDEF. pose proof Hsp as Hsp'.
set (pz := bv_unsigned p) in *. set (n := length path) in *.
destruct (rdn_of_defined M0 8 (pz + Z.of_nat n + 1) ltac:(lia) ltac:(lia)) as (t8 & R8 & L8).
{ intros i Hi. replace (pz + Z.of_nat n + 1 + i) with (pz + (Z.of_nat n + 1 + i)) by lia. apply PDEF. lia. }
assert (RD0 : rdn ASEGS M0 (Z_to_bv 64 pz) (n + 9) = Some (path ++ Z_to_bv 8 0 :: t8)).
{ replace (n + 9)%nat with ((n + 1) + 8)%nat by lia. replace (path ++ Z_to_bv 8 0 :: t8) with ((path ++ [Z_to_bv 8 0]) ++ t8) by (rewrite <- app_assoc; reflexivity).
unfold pz at 1. rewrite Z_to_bv_bv_unsigned. apply (SeqExec.rdn_app ASEGS M0 (n + 1) 8 p _ _ STR).
replace (p + nat_to_word (n + 1))%bv with (Z_to_bv 64 (pz + Z.of_nat n + 1)); [exact R8|].
apply bv_eq. unfold nat_to_word, pz. rewrite bv_add_unsigned, !Z_to_bv_unsigned. unfold bv_wrap. rewrite Zplus_mod_idemp_r. f_equal. lia. }
exists t8. constructor.
- apply (rdn_tr M0 _ pz (n + 9) _ RD0); [lia | lia|].
intros i Hi. unfold mrestrict.
rewrite (vis_stk scfg L ar C IL HI HIok sp0 Hsp DL M0 _ _ _ _ _ _ i D) by lia.
apply (di_above _ _ _ _ _ _ _ _ _ _ D). lia.
- exact L8.
- intros j Hj Hz. apply NONUL.
replace (Z_to_bv 8 0) with (nth j path (Z_to_bv 8 0)); [apply nth_In; exact Hj|].
apply bv_eq. rewrite Hz. reflexivity.
Qed.
#[using="L IL Hsp DL"] Lemma str_hull : ltac2:(TCodec.tc2 tcn__Ja0DiagStrK "S3'6';'A%2211%411&O%611&K'R0yR0%211'9y8%511%311p051'F'Q4vQEvBvQNvHr8r7r6r5r4r3%;::987654321&Q0&QB&N%11>+XPPP0%4221&QA+2+Q?%3221%9215%;3@61&Q=&R1%12Q2G%321Bz%521D'<&Q;&Q7&Q<+8%22M1%5241+7%I221r1%?2Q@1%A231&Q>&Q?%=2Q6Q5%<21;%?2>1%@21=+Q<%O2N1%C2B1%8241%:2<1%G2<1'=&J&Mr;r9%3221r:r2%73321(2&QO%12R6Q5%32R61%=3R651p0?1pT:R<1p0Q91p0Q<1p0QA1p0QN1pSFRI1pSLRJ1pSDR=1pQ@R?1p2RK1pS@RI1pQ:RK1pQ8RN1").
Proof.
intros LB LK cr A M model pz n D SAH Hlo Hn x Hx. pose proof Hsp as Hsp'.
rewrite <- (Z_to_bv_bv_unsigned 64 x).
apply (hi_sh0 L ar IL HI sp0 Hsp DL M0 _ _ _ _ _ _ (bv_unsigned x) D SAH).
unfold Ja0RegionPoisoned.SB in Hx.
assert (Q1 : (usp - 8388608) / 8 + 1048576 <= pz / 8).
{ replace (usp - 8388608) with (usp + (-1048576) * 8) by lia. rewrite Z.div_add by lia. pose proof (Z.div_le_mono usp pz 8 ltac:(lia) Hlo). lia. }
change ((2 ^ 47 - 1) / 8) with (2 ^ 44 - 1). lia.
Qed.
Section SE.
Local Abbreviation SEC_T_dgs_cell_vis := (ltac2:(TCodec.tc2 tcn__Ja0DiagStrK "R8'6';'A%2211%411&O%611&K'R0yR0%211'9y8%511%311p051'F'Q4vQEvBvQNvHr9r8r7r6r5r4%;::987654321&Q:%M2KL(:r3%24OO61r2%44Q0Q121&3&Q6&Q5%33921%;3:51'=%Q:1M%Q011&Q8&Q9&J&M%12IG%321I&QO%12Q:I&QC%11J%:49531(2&E%72Q@I%2251%42A1%C3A61p0E1p0Q21pT8QM1pSFQN1pS:QO1pSDQB1pQ@QD1p2R01pS@QN1pQ:R01pQ8R31")) (only parsing).
Variable LB : ltac:(sec_ty2 constr:(SEC_T_dgs_cell_vis) 0%nat 0%nat).
Variable LK : ltac:(sec_ty2 constr:(SEC_T_dgs_cell_vis) 1%nat 0%nat).
Variable cr : ltac:(sec_ty2 constr:(SEC_T_dgs_cell_vis) 2%nat 0%nat).
Variable A : ltac:(sec_ty2 constr:(SEC_T_dgs_cell_vis) 3%nat 0%nat).
Variable M : ltac:(sec_ty2 constr:(SEC_T_dgs_cell_vis) 4%nat 0%nat).
Variable model : ltac:(sec_ty2 constr:(SEC_T_dgs_cell_vis) 5%nat 0%nat).
Variable a : ltac:(sec_ty2 constr:(SEC_T_dgs_cell_vis) 6%nat 0%nat).
Variable n : ltac:(sec_ty2 constr:(SEC_T_dgs_cell_vis) 7%nat 0%nat).
Variable v : ltac:(sec_ty2 constr:(SEC_T_dgs_cell_vis) 8%nat 0%nat).
Lemma dgs_cell_vis : ltac:(sec_stmt2 constr:(SEC_T_dgs_cell_vis) 9%nat 0%nat).
Proof using scfg L C IL HIok DL Hdg Hdgs LB LK cr A M model a n v.
intros D Hin.
pose proof (di_inv _ _ _ _ _ _ _ _ _ _ D) as HH.
destruct (aio_statics _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as (_ & CS). rewrite (dla_segs _ _ _ _ DL) in CS.
assert (Hin' : In (a, n, v) (asc_cells C)) by (apply in_app_or in Hin as [X|X]; [exact (Hdg _ X) | exact (Hdgs _ X)]).
pose proof (proj1 (Forall_forall _ _) CS (a, n, v) Hin') as X. unfold cell_is in X. cbn [fst snd] in X.
rewrite rdn_mrestrict_eq; [exact X|].
intros k Hk. unfold woff.
assert (B : 0 <= a /\ a + Z.of_nat (Z.to_nat n) <= 0x691000).
{ unfold DG_CELLS, DGS_CELLS in Hin. cbn [In app] in Hin. repeat (destruct Hin as [Hin|Hin]; [injection Hin as <- <- <-; cbn; lia|]). destruct Hin. }
rewrite (u64_lit a) by lia. apply (vis_low scfg L ar C IL HI HIok sp0 DL M0 _ _ _ _ _ _ _ D). lia.
Qed.
End SE.
Section SE.
Local Abbreviation SEC_T_str_statics := (ltac2:(TCodec.tc2 tcn__Ja0DiagStrK "R0'6';'A%2211%411&O%611&K'R0yR0%211'9y8%511%311p051'F'Q4vQEvBvQNvHr6r5r4r3r2r1%;::987654321'<&Q=+RPP0%2215&Q>+QV`P0%2281%7241'=&J&M%12B@&QO%12Q1@%533D1(1%11Q0%93Q031p0;1pSBQ>1&Q3%;2KI%=21K%311&Q1%113%J231p081p0M1pSDQ:1pQ@Q<1p2QH1pS@QF1pQ:QH1pQ8QK1")) (only parsing).
Variable LB : ltac:(sec_ty2 constr:(SEC_T_str_statics) 0%nat 0%nat).
Variable LK : ltac:(sec_ty2 constr:(SEC_T_str_statics) 1%nat 0%nat).
Variable cr : ltac:(sec_ty2 constr:(SEC_T_str_statics) 2%nat 0%nat).
Variable A : ltac:(sec_ty2 constr:(SEC_T_str_statics) 3%nat 0%nat).
Variable M : ltac:(sec_ty2 constr:(SEC_T_str_statics) 4%nat 0%nat).
Variable model : ltac:(sec_ty2 constr:(SEC_T_str_statics) 5%nat 0%nat).
Lemma str_statics : ltac:(sec_stmt2 constr:(SEC_T_str_statics) 6%nat 0%nat).
Proof using scfg L C IL HIok Hsp DL Hdg Hdgs LB LK cr A M model.
intros D IMG.
set (MV := mrestrict (ahid A model) M) in *.
assert (STC : forall a n v, In (a, n, v) (DG_CELLS ++ DGS_CELLS) -> rdn ASEGS MV (Z_to_bv 64 a) (Z.to_nat n) = Some (word_to_le_bytes (Z.to_nat n) (Z_to_bv 64 v)))
by (intros a n v Hin; exact (dgs_cell_vis _ _ _ _ _ _ a n v D Hin)).
assert (STC1 : forall a v, In (a, 1, v) (DG_CELLS ++ DGS_CELLS) -> (0 <=? v) && (v <? 2 ^ 64) = true -> rdn ASEGS MV (Z_to_bv 64 a) 1 = Some [Z_to_bv 8 v]).
{ intros a v Hin Hb. apply andb_prop in Hb as (B1 & B2). apply Z.leb_le in B1. apply Z.ltb_lt in B2. rewrite <- (ArtMem.art_bytes1 v (conj B1 B2)). exact (STC a 1 v Hin). }
assert (IC : forall a (n : nat) bs, rdn ASEGS (fun _ => None) (Z_to_bv 64 a) n = Some bs -> (65536 <=? a) && (a + Z.of_nat n <=? 1261568) = true -> rdn ASEGS MV (Z_to_bv 64 a) n = Some bs).
{ intros a n bs Hr Hc. apply andb_prop in Hc as (B1 & B2). apply Z.leb_le in B1, B2. apply (img_cell MV a n bs Hr); [lia | lia|]. intros i Hi. apply IMG. lia. }
assert (RT : Ja0RegionPoisoned.rt_layout_globs MV).
{ unfold Ja0RegionPoisoned.rt_layout_globs.
rewrite <- (w_lit 0x132638 (0x132638%bv : word) eq_refl), <- (w_lit 0x13acf8 (0x13acf8%bv : word) eq_refl), <- (w_lit 0x132640 (0x132640%bv : word) eq_refl), <- (w_lit 0x13b9e8 (0x13b9e8%bv : word) eq_refl),
<- (w_lit 0x132648 (0x132648%bv : word) eq_refl), <- (w_lit 0x13b9f0 (0x13b9f0%bv : word) eq_refl), <- (w_lit 0x132650 (0x132650%bv : word) eq_refl), <- (w_lit 0x13b9e0 (0x13b9e0%bv : word) eq_refl).
split; [exact (IC 0x132638 8%nat (word_to_le_bytes 8 (Z_to_bv 64 0x13acf8)) ltac:(img_rd) eq_refl)|].
split; [exact (STC 0x13acf8 8 0x7fff8000 ltac:(unfold DG_CELLS, DGS_CELLS; cbn [In app]; tauto))|].
split; [exact (IC 0x132640 8%nat (word_to_le_bytes 8 (Z_to_bv 64 0x13b9e8)) ltac:(img_rd) eq_refl)|].
split; [exact (STC 0x13b9e8 8 0 ltac:(unfold DG_CELLS, DGS_CELLS; cbn [In app]; tauto))|].
split; [exact (IC 0x132648 8%nat (word_to_le_bytes 8 (Z_to_bv 64 0x13b9f0)) ltac:(img_rd) eq_refl)|].
split; [exact (STC 0x13b9f0 8 0 ltac:(unfold DG_CELLS, DGS_CELLS; cbn [In app]; tauto))|].
split; [exact (IC 0x132650 8%nat (word_to_le_bytes 8 (Z_to_bv 64 0x13b9e0)) ltac:(img_rd) eq_refl)|].
exact (STC 0x13b9e0 8 (2 ^ 47 - 1) ltac:(unfold DG_CELLS, DGS_CELLS; cbn [In app]; tauto)). }
split.
- unfold Ja0DiagStrnlen.DSN.sn_cells, L5Defs.L5.u8_at, L5Defs.L5.u64_at.
split; [exact (STC1 1292760 1 ltac:(unfold DG_CELLS, DGS_CELLS; cbn [In app]; tauto) eq_refl)|].
split; [exact (STC 1263088 8 1201360 ltac:(unfold DG_CELLS, DGS_CELLS; cbn [In app]; tauto))|].
split; [exact (STC 1262720 8 1198256 ltac:(unfold DG_CELLS, DGS_CELLS; cbn [In app]; tauto))|].
split; [exact RT|].
rewrite <- (w_lit 0x132628 (0x132628%bv : word) eq_refl), <- (w_lit 0x1cc923 (0x1cc923%bv : word) eq_refl).
split; [exact (IC 0x132628 8%nat (word_to_le_bytes 8 (Z_to_bv 64 0x1cc828)) ltac:(img_rd) eq_refl)|].
exact (STC1 0x1cc923 1 ltac:(unfold DG_CELLS, DGS_CELLS; cbn [In app]; tauto) eq_refl).
- unfold Ja0AsanMemcpy.mc_icpt_globs.
rewrite <- (w_lit 0x1331a0 (0x1331a0%bv : word) eq_refl), <- (w_lit 0x13b9d9 (0x13b9d9%bv : word) eq_refl), <- (w_lit 0x134640 (0x134640%bv : word) eq_refl).
split; [exact (IC 0x1331a0 8%nat (word_to_le_bytes 8 (Z_to_bv 64 0x13b9d9)) ltac:(img_rd) eq_refl)|].
split; [exact (STC1 0x13b9d9 1 ltac:(unfold DG_CELLS, DGS_CELLS; cbn [In app]; tauto) eq_refl)|].
exact (STC 0x134640 8 0x1249ac ltac:(unfold DG_CELLS, DGS_CELLS; cbn [In app]; tauto)).
Qed.
End SE.
End StrK.
End FPX_1.
