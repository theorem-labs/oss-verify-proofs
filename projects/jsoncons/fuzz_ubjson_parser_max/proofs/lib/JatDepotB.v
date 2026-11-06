(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import PropExec CatExec CatSim SeqExec StepTac StoreOk Hoare WalkTac MmapSim As0StepLib RefMemcpyLib
MemSplit ArtMem ArtRegs ArtAtomics ArtAtomics2 ArtTac JatDepotA.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import muslA.Ja0MemcpyBase Ja0IntMemcpy.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLia. Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLiaT.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import SecKit.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import OtfKit.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Asan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__JatDepotB () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Init.Nat."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.LinuxProcessSem.BvBase."; "LinuxProcessSemantics.Riscv.Prelude."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.ArtMem."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CatExec."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CatSim."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.JatDepotA."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.JatDepotB.FPX.STORE."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.StoreOk."; "OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Asan.M."; "Stdlib.Lists.List."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["1Some"; "1cons"; "1length"; "1list"; "1nat"; "1nil"; "1option"; "2I"; "2and"; "2eq"; "2ex"; "3mul"; "4Z"; "5nat_to_word"; "6bvmap"; "0M"]; ["0M'"; "7apart"; "7cell"; "7wok"; "8wbytes"; "9msteps"; ":STO"; ":rcell"; ";dp_store_out"; "<getr"; "<mkst"; "<rdn"; "=mem_grows"; ">loaded_segments"; "0ST"; "?In"]; ["@add"; "@div"; "@land"; "@le"; "@lt"; "@lxor"; "@mul"; "@of_nat"; "@pow"; "@sub"; "0TF"; "0a"; "0b"; "0blk"; "0bs"; "0fx"]; ["0h"; "0i"; "0k"; "0m"; "0nd"; "0r"; "0regs"; "0regs'"; "0rom"; "0s"; "0size"; "ABV"; "AZ_to_bv"; "Abv"; "Abv_add"; "0u"]; ["0v"; "0x"]]).
Local Ltac oF' pc := oF constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Asan.M.loaded_segments) pc.
Local Ltac oD' pc := oD constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Asan.M.loaded_segments) pc.
Local Ltac oE' pc := oE constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Asan.M.loaded_segments) pc.
Local Ltac oW' pc := oW constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Asan.M.loaded_segments) pc. Local Ltac lia := L5FastLiaT.plia2.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
#[local] Abbreviation ASEGS := Asan.M.loaded_segments.
#[local] Abbreviation cellA := (cell Asan.M.loaded_segments).
#[local] Abbreviation wrA := (wr Asan.M.loaded_segments).
#[local] Abbreviation wokA := (wok Asan.M.loaded_segments).
#[local] Notation "'U' r" := (bv_unsigned r) (at level 10, r at level 9).
Lemma cell8_lo : ltac2:(TCodec.tc2 tcn__JatDepotB "G'QMyR0%211'6y8%511%311p051'<&B&Mr3r2u8r1%6554321r4u4%9582716p041pT2<1pRH=1pQ0?1").
Proof.
intros M a v C. unfold cell in *. pose proof (SeqExec.rdn_firstn _ _ _ _ _ 4 C ltac:(lia)) as F. rewrite F. reflexivity.
Qed.
Lemma zb_add_lit : ltac2:(TCodec.tc2 tcn__JatDepotB "Q4'<'4&Q3zr2%3221&Q4&Q0r3&Q7%116%4231&Q8+2+R0%3221%:251'9'QMyR0%211&QN&QLr4%2251&=%11B%63831%C1D%F261%82;1%>3;41p0@1p0L1pS6Q11pRHQ31").
Proof.
intros a k Ha Hak. unfold nat_to_word. apply bv_eq.
rewrite bv_add_unsigned, !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
rewrite <- Zplus_mod. rewrite !Z.mod_small by lia. reflexivity.
Qed.
Lemma cell8_hi : ltac2:(TCodec.tc2 tcn__JatDepotB "QB'QMyR0%211'6y8%511%311p051'<&Q3zr2%3221&Q4&Q0r3+8%3221&Q8+2+R0%3221%9251'8%?2>9%<2:4%3221&B&Mr6r5u8r4%6554321r7+4%F271u4&Q1+Q0%F2E1%32;1%?5>8651p0:1p0B1p0G1p0Q21pT2Q71pRHQ81pQ0Q:1").
Proof.
intros M a v Ha Ha8 Hv C. unfold cell in *. pose proof (SeqExec.rdn_skipn _ _ _ _ _ 4 C ltac:(lia)) as S.
rewrite (zb_add_lit a 4%nat) in S by lia. change (8 - 4)%nat with 4%nat in S. change (Z.of_nat 4) with 4 in S. rewrite S. f_equal.
pose proof (Z.div_pos v (2 ^ 32) ltac:(lia) ltac:(lia)). pose proof (Z.div_lt_upper_bound v (2 ^ 32) (2 ^ 32) ltac:(lia) ltac:(lia)).
unfold word_to_le_bytes. rewrite !art_u_lit by lia.
cbn [Z_to_le_bytes skipn]. rewrite !Z.shiftr_shiftr by lia. rewrite !Z.shiftr_div_pow2 by lia.
rewrite !Z.div_div by lia. rewrite <- !Z.pow_add_r by lia.
repeat (f_equal; [f_equal; f_equal; lia|]). reflexivity.
Qed.
Lemma rdn_words : ltac2:(TCodec.tc2 tcn__JatDepotB "R2'4'QMyR0%211'6y8%511%311p051'<&Q3zr1%3221&Q4&Q0r2&Q6+8&Q7r4%211%5241%8271&Q8+2+R0%3221%>251'8r6%<11%B2D1%42D1&Gr5%C2BD%F221%4281p061pS4O1':'3%11Q5'9%Q912&K&M&QL%12Q?>&;u8r7%3221%847H51(0%12=Q<%=3<31qRN?1%B2@1p0D1p0Q11p0QA1pRHQF1pQ0QH1pS6R11").
Proof.
induction k as [|k IH]; intros M a Ha Hak RC; [exists []%list; reflexivity|].
destruct (RC 0 ltac:(lia)) as (bs0 & R0). replace (a + 8 * 0) with a in R0 by lia.
destruct (IH M (a + 8) ltac:(lia) ltac:(lia) ltac:(intros i Hi; replace (a + 8 + 8 * i) with (a + 8 * (i + 1)) by lia; apply RC; lia)) as (bs1 & R1).
exists (bs0 ++ bs1)%list. replace (8 * S k)%nat with (8 + 8 * k)%nat by lia.
apply SeqExec.rdn_app; [exact R0|]. rewrite (zb_add_lit a 8%nat) by lia. change (Z.of_nat 8) with 8. exact R1.
Qed.
Lemma land_high_mask_0 : ltac2:(TCodec.tc2 tcn__JatDepotB "B'<'8&Q3zr1%3221&Q4+@%2241%8241'9&Q2r2+_ooooooooooo@%3221%53?1<p071pT4A1").
Proof.
intros x Hx. apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec, Z.bits_0.
destruct (Z_lt_le_dec i 4) as [L|G].
- replace (Z.testbit 18446744073709551600 i) with false; [apply Bool.andb_false_r|].
assert (E : i = 0 \/ i = 1 \/ i = 2 \/ i = 3) by lia. destruct E as [->|[->|[->| ->]]]; reflexivity.
- rewrite (Z.bits_above_log2 x i); [reflexivity | lia |].
destruct (Z.eq_dec x 0) as [->|NZ]; [cbn; lia|]. apply Z.log2_lt_pow2; [lia|]. eapply Z.lt_le_trans; [apply (proj2 Hx)|].
change 16 with (2 ^ 4). apply Z.pow_le_mono_r; lia.
Qed.
Lemma lxor_pow20_nz : ltac2:(TCodec.tc2 tcn__JatDepotB "H'<'8&Q3zr1%3221&Q4&Q8+2+D%3221%5271%;271+1&Q5r2%2216%?241+R0%<2;1%>241%D241p0:1pRHG1").
Proof.
intros a Ha. pose proof (lxor_range64 a (2 ^ 20) ltac:(lia) ltac:(lia)).
destruct (Z.eq_dec (Z.lxor a (2 ^ 20)) 0) as [E|NE]; [|lia].
apply Z.lxor_eq in E. lia.
Qed.
Lemma cell_wb_other : ltac2:(TCodec.tc2 tcn__JatDepotB "QO'QMyR0%211'6y8%511%311p051'<'3%115'4&Q3zr5%3221&Q4&Q0r6&Q7&2%12@7%311%6251&Q8+2+R0%3221%<251%:1?%=2<1%?214&Ar9r8%?2N1%A11r7%C1D%746321&B&Mr;%352196I&Dr<&QL%12Q>5r:%53421%:591A@=p081p0=1p0F1p0Q71p0K1p0Q91pT0QA1pS8Q?1pRJQC1pRNQB1pRHQE1pQ0QG1").
Proof.
intros M a bs b m u Ha Hal Hb Hbm AP C. unfold cell in *. rewrite <- C. apply rdn_wbytes_out; rewrite ?art_u_lit by lia; unfold apart in AP; lia.
Qed.
Lemma wok_wb : ltac2:(TCodec.tc2 tcn__JatDepotB "N'QMyR0%211'6y8%511%311p051'3%114'<'4&C&Mr5r2r1%544321&Dr6r4%33271r3%;4:218p071pS8>1pRJ@1pRNB1pRHJ1pQ0F1").
Proof. intros M a bs b m W. unfold wok in *. eapply store_ok_mono; [apply wbytes_grows | exact W]. Qed.
Section FPX. Context {fx : PropExec.FPState}.
#[local] Ltac wpc := lazymatch goal with |- msteps _ (mkstr _ ?p _ _ _) _ => wlit p | |- msteps _ (mkst _ ?p _ _) _ => wlit p end.
Section STORE.
Variables (M rom : word -> option byte) (s nd h trp size TF ST blk l2 : Z).
Hypothesis Hs : 0x691000 <= s - 224 /\ s < 2 ^ 64.
Hypothesis Hl2 : 0x691000 <= l2 /\ l2 + 2 ^ 20 < 2 ^ 64.
Hypothesis Hnd : l2 + 16 <= nd /\ nd + 16 <= l2 + 2 ^ 20 /\ nd mod 16 = 0.
Hypothesis Hblk : 0x691000 <= blk /\ blk + 2 ^ 23 < 2 ^ 64 /\ blk mod 8 = 0.
Hypothesis HTF : 0 <= TF /\ TF + size + 1 <= 2 ^ 20 - 64.
Hypothesis HST : 0 <= ST /\ ST + size + 1 < 2 ^ 20.
Hypothesis Hsz : 1 <= size <= 30.
Hypothesis Htrp : 4096 <= trp /\ trp + 8 * size < 2 ^ 64 /\ trp mod 8 = 0.
Hypothesis Hh : 0 <= h < 2 ^ 64.
Hypothesis A1 : apart (s - 224) 224 l2 (2 ^ 20).
Hypothesis A2 : apart (s - 224) 224 blk (2 ^ 23).
Hypothesis A3 : apart l2 (2 ^ 20) blk (2 ^ 23).
Hypothesis A4 : apart trp (8 * size) blk (2 ^ 23).
Hypothesis Ctrp : cellA M (s - 104) 8 trp.
Hypothesis Cszt : cellA M (s - 96) 8 size.
Hypothesis CTF : cellA M STO 8 TF.
Hypothesis Cblk : cellA M (STO + 16) 8 blk.
Hypothesis CST : cellA M (STO + 24) 4 ST.
Hypothesis RC : forall i, 0 <= i < size -> rcell M (trp + 8 * i).
Hypothesis Wf : wrA M (s - 224) 112.
Hypothesis Wnd : wrA M nd 16.
Hypothesis Wblk : wrA M blk (2 ^ 23).
Hypothesis Wsto : wrA M STO 32.
Definition p0 : Z := blk + 8 * TF.
Definition dp_store_out (x : word) : Prop :=
~ (s - 224 <= U x < s - 112) /\ ~ (nd <= U x < nd + 8) /\ ~ (nd + 12 <= U x < nd + 16)
/\ ~ (STO <= U x < STO + 8) /\ ~ (STO + 24 <= U x < STO + 28) /\ ~ (blk + 8 * TF <= U x < blk + 8 * TF + 8 * (size + 1)).
Section SE.
Local Abbreviation SEC_T_dp_store_run := (ltac2:(TCodec.tc2 tcn__JatDepotB "UJ&>y5'QMyR0%211%5241'9&Ir1(QK+:(7%33;21%6251&QLvQD%22=1%;3=41r2+;%;3C19%>231z%92D1%B3D31r3+<%B3J1@%E231&Q9vQI+S8%3221%C2N1%L3N61r4+=%L3Q41J%O231vQ@%J2Q51%Q33Q531r5+1%Q33Q;1Q1%Q6231+cVTD%Q63Q<1Q4/01Q<%Q;3Q=41r6+2%Q;3QC1Q9%Q>231+S@%J2I1%Q:2QE1%QC3QE41':'6y8%QK11%311p0QK1'8'E&M&JvQ?r9+cTl4%QN3R41QL/01R4v?vQH%8576321%958QJLR42%<3;21%R72QLJ%R93R;1G%R>1R?&O(1+3%R;3RC1R9+4%R=3RE1R;+8%R?3RG1R=+9%RA3RI1R?+B%RC3RK1RA+C%RE3RM1RC+D%RG3RO1RE+E%RI3S11RG+F%RK3S31RI+G%RM3S51RK+H%RO3S71RM+I%S13S91RO+J%S33S;1S1+K%S53S=1S3(5%11Q0%O3Q131%Q03Q261%Q13Q391%Q23Q4<1%Q33Q5?1%Q43Q6B1%Q53Q7E1%Q63Q8H1%Q73Q9K1%Q83Q:N1%Q93Q;Q11%Q:3Q<Q41%Q;3Q=Q71%Q<3Q>Q:1%Q>3Q?SG1%SI2RMS>r;%SK21S@%SM3SO31p051pS<QE1&L%12QNSO&H%11T1%SA1SH%R21SI%T63R>21p041pT4T:1&B&Fu8&Q0vQ:vQJ%3221%421S;%85RET?761%628QAu4vN%9217%:21SA%>5RKTE541+@%=2?1vQ=%B5ROTI2@1%C5S0TJTCASK%A2TDT9%B2ASI%F5S3TM2<1%S6241%S7261%S82;1%S92B1%S:2L1%S;2Q41%S<2Q71%S=2RN1%S>2S11qQ2S@1%SF2SA1qS@U<1%SH2U=1p0SJ1p0T31p0T<1p0TD1p0TO1p0U71pS>UD1")) (only parsing).
Variable regs : ltac:(sec_ty2 constr:(SEC_T_dp_store_run) 0%nat 0%nat).
Lemma dp_store_run : ltac:(sec_stmt2 constr:(SEC_T_dp_store_run) 1%nat 0%nat).
Proof using trp l2 Hs Hl2 Hnd Hblk HTF HST Hsz Htrp Hh A1 A2 A3 A4 Ctrp Cszt CTF Cblk CST RC Wf Wnd Wblk Wsto regs.
intros H10 H11 H12 H13 H1 H2.
destruct Hs as [S1' S2']. destruct Hl2 as [L1' L2']. destruct Hnd as (N1' & N2' & N3'). destruct Hblk as (B1' & B2' & B3').
destruct HTF as [T1' T2']. destruct HST as [U1' U2']. destruct Htrp as (P1' & P2' & P3'). unfold STO in *.
pose proof (cell8_lo _ _ _ Cszt) as Csz4. pose proof (cell8_hi M (s - 96) size ltac:(lia) ltac:(lia) ltac:(lia) Cszt) as Ctg4.
rewrite (Z.div_small size (2 ^ 32)) in Ctg4 by lia. replace (s - 96 + 4) with (s - 92) in Ctg4 by lia.
assert (S1 : exists r1 X1,
msteps ASEGS (mkst regs (0x99384 : word) M rom) (mkst r1 (0x97194 : word) X1 rom)
/\ X1 = Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 M
(s - 120) (U (0x99894 : word)%bv)) (s - 128) (U (getr regs 8))) nd h) (s - 136) 0)
(s - 152) (U (0x993b0 : word)%bv)) (s - 160) nd) (s - 168) (U (getr regs 9))) (s - 176) (U (getr regs 18))) (s - 184) (U (getr regs 19)))
(s - 192) (U (getr regs 20))) (s - 200) (U (getr regs 21))) (s - 208) 0) (s - 136) 0
/\ getr r1 10 = Z_to_bv 64 2149320 /\ getr r1 11 = Z_to_bv 64 (size + 1) /\ getr r1 12 = Z_to_bv 64 (s - 208) /\ getr r1 13 = Z_to_bv 64 (s - 136)
/\ getr r1 1 = Z_to_bv 64 0x970e8 /\ getr r1 2 = Z_to_bv 64 (s - 208)
/\ getr r1 8 = Z_to_bv 64 (s - 136) /\ getr r1 9 = Z_to_bv 64 2149320 /\ getr r1 18 = Z_to_bv 64 (size + 1) /\ getr r1 19 = Z_to_bv 64 (s - 104)
/\ getr r1 20 = Z_to_bv 64 size /\ getr r1 21 = Z_to_bv 64 0
/\ (forall r : reg, In r [3; 4; 22; 23; 24; 25; 26; 27]%bv -> getr r1 r = getr regs r)).
{ eexists _, _. split; [|split; [reflexivity|]].
- zstep (ltac:(oF' 0x99384%Z)) (ltac:(oD' 0x99384%Z)).
zsd (ltac:(oF' 0x99388%Z)) (ltac:(oD' 0x99388%Z)) (s - 120) (U (0x99894 : word)%bv) ltac:(rewok Wf).
zsd (ltac:(oF' 0x9938c%Z)) (ltac:(oD' 0x9938c%Z)) (s - 128) (U (getr regs 8)) ltac:(rewok Wf).
zstep (ltac:(oF' 0x99390%Z)) (ltac:(oD' 0x99390%Z)).
zstep (ltac:(oF' 0x99394%Z)) (ltac:(oD' 0x99394%Z)).
zsd (ltac:(oF' 0x99398%Z)) (ltac:(oD' 0x99398%Z)) nd h ltac:(rewok Wnd).
zsd (ltac:(oF' 0x9939c%Z)) (ltac:(oD' 0x9939c%Z)) (s - 136) 0 ltac:(rewok Wf).
stepn (ltac:(oF' 0x993a0%Z)) (ltac:(oD' 0x993a0%Z)).
stepn (ltac:(oF' 0x993a4%Z)) (ltac:(oD' 0x993a4%Z)).
zstep (ltac:(oF' 0x993a8%Z)) (ltac:(oD' 0x993a8%Z)).
stepn (ltac:(oF' 0x993ac%Z)) (ltac:(oD' 0x993ac%Z)).
zstep (ltac:(oF' 0x97070%Z)) (ltac:(oD' 0x97070%Z)).
zsd (ltac:(oF' 0x97074%Z)) (ltac:(oD' 0x97074%Z)) (s - 152) (U (0x993b0 : word)%bv) ltac:(rewok Wf).
zsd (ltac:(oF' 0x97078%Z)) (ltac:(oD' 0x97078%Z)) (s - 160) nd ltac:(rewok Wf).
zsd (ltac:(oF' 0x9707c%Z)) (ltac:(oD' 0x9707c%Z)) (s - 168) (U (getr regs 9)) ltac:(rewok Wf).
zsd (ltac:(oF' 0x97080%Z)) (ltac:(oD' 0x97080%Z)) (s - 176) (U (getr regs 18)) ltac:(rewok Wf).
zsd (ltac:(oF' 0x97084%Z)) (ltac:(oD' 0x97084%Z)) (s - 184) (U (getr regs 19)) ltac:(rewok Wf).
zsd (ltac:(oF' 0x97088%Z)) (ltac:(oD' 0x97088%Z)) (s - 192) (U (getr regs 20)) ltac:(rewok Wf).
zsd (ltac:(oF' 0x9708c%Z)) (ltac:(oD' 0x9708c%Z)) (s - 200) (U (getr regs 21)) ltac:(rewok Wf).
zstep (ltac:(oF' 0x97090%Z)) (ltac:(oD' 0x97090%Z)).
match goal with |- msteps _ (mkst _ _ ?X _) _ =>
assert (Q1 : cellA X (s - 96) 4 size) by zcell; assert (Q2 : cellA X (s - 92) 4 0) by zcell end.
zlw (ltac:(oF' 0x97094%Z)) (ltac:(oD' 0x97094%Z)) (s - 96) Q1.
zlw (ltac:(oF' 0x97098%Z)) (ltac:(oD' 0x97098%Z)) (s - 92) Q2.
stepn (ltac:(oF' 0x9709c%Z)) (ltac:(oD' 0x9709c%Z)). rwH. rewrite art_zb_or by lia. rewrite Z.lor_0_r.
zbtk (ltac:(oF' 0x970a0%Z)) (ltac:(oD' 0x970a0%Z)).
zstep (ltac:(oF' 0x970ac%Z)) (ltac:(oD' 0x970ac%Z)).
zstep (ltac:(oF' 0x970b0%Z)) (ltac:(oD' 0x970b0%Z)).
zbft (ltac:(oF' 0x970b4%Z)) (ltac:(oD' 0x970b4%Z)).
zstep (ltac:(oF' 0x970b8%Z)) (ltac:(oD' 0x970b8%Z)).
zstep (ltac:(oF' 0x970bc%Z)) (ltac:(oD' 0x970bc%Z)).
zbtk (ltac:(oF' 0x970c0%Z)) (ltac:(oD' 0x970c0%Z)).
zsd (ltac:(oF' 0x970c8%Z)) (ltac:(oD' 0x970c8%Z)) (s - 208) 0 ltac:(rewok Wf).
zsd (ltac:(oF' 0x970cc%Z)) (ltac:(oD' 0x970cc%Z)) (s - 136) 0 ltac:(rewok Wf).
zstep (ltac:(oF' 0x970d0%Z)) (ltac:(oD' 0x970d0%Z)).
zstep (ltac:(oF' 0x970d4%Z)) (ltac:(oD' 0x970d4%Z)).
zstep (ltac:(oF' 0x970d8%Z)) (ltac:(oD' 0x970d8%Z)).
zstep (ltac:(oF' 0x970dc%Z)) (ltac:(oD' 0x970dc%Z)).
zstep (ltac:(oF' 0x970e0%Z)) (ltac:(oD' 0x970e0%Z)).
stepn (ltac:(oF' 0x970e4%Z)) (ltac:(oD' 0x970e4%Z)).
replace (s - 112 - 32 - 64) with (s - 208) by lia. replace (s - 112 - 32 + 8) with (s - 136) by lia.
apply mst_refl.
- do 12 (split; [kept_solve|]). intros r Hr. cbv in Hr.
destruct Hr as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]; kept_solve. }
destruct S1 as (r1 & X1 & RUN1 & EX1 & Q10 & Q11 & Q12 & Q13 & Q1 & Q2 & Q8 & Q9 & Q18 & Q19 & Q20 & Q21 & K1).
assert (S2 : exists r2 X2,
msteps ASEGS (mkst r1 (0x97194 : word) X1 rom) (mkst r2 (0x970e8 : word) X2 rom)
/\ X2 = Wn 8 (Wn 8 (Wn 8 (Wn 8 X1 (s - 216) 0x970e8) (s - 224) (s - 136)) 2149320 (TF + (size + 1))) (s - 208) TF
/\ getr r2 10 = Z_to_bv 64 (blk + 8 * TF) /\ getr r2 2 = Z_to_bv 64 (s - 208) /\ getr r2 8 = Z_to_bv 64 (s - 136)
/\ getr r2 9 = Z_to_bv 64 2149320 /\ getr r2 18 = Z_to_bv 64 (size + 1) /\ getr r2 19 = Z_to_bv 64 (s - 104) /\ getr r2 20 = Z_to_bv 64 size /\ getr r2 21 = Z_to_bv 64 0
/\ (forall r : reg, In r [3; 4; 22; 23; 24; 25; 26; 27]%bv -> getr r2 r = getr regs r)).
{ subst X1.
match goal with |- exists r2 X2, msteps _ (mkst _ _ ?X _) _ /\ _ =>
assert (CTF1 : cellA X 2149320 8 TF) by zcell; assert (Cblk1 : cellA X (2149320 + 16) 8 blk) by zcell end.
pose proof (Z.div_small TF (2 ^ 20) ltac:(lia)) as DT0. pose proof (Z.div_small (size + TF) (2 ^ 20) ltac:(lia)) as DT1.
pose proof (Z.div_small TF (2 ^ 32) ltac:(lia)) as DT2.
eexists _, _. split; [|split; [reflexivity|]].
- zstep (ltac:(oF' 0x97194%Z)) (ltac:(oD' 0x97194%Z)).
zsd (ltac:(oF' 0x97198%Z)) (ltac:(oD' 0x97198%Z)) (s - 216) 0x970e8 ltac:(rewok Wf).
zsd (ltac:(oF' 0x9719c%Z)) (ltac:(oD' 0x9719c%Z)) (s - 224) (s - 136) ltac:(rewok Wf).
zstep (ltac:(oF' 0x971a0%Z)) (ltac:(oD' 0x971a0%Z)).
zstep (ltac:(oF' 0x971a4%Z)) (ltac:(oD' 0x971a4%Z)).
match goal with |- msteps _ (mkst _ _ ?X _) _ =>
assert (CTF2 : cellA X 2149320 8 TF) by zcell; assert (WTF2 : wokA X 2149320 8) by (rewok Wsto) end.
chain_step; [reflexivity
| eapply (art_step_amoadd_d_rd _ _ _ _ _ _ _ _ _ _ _ (Z_to_bv 64 2149320) (Z_to_bv 64 (size + 1)) (Z_to_bv 64 TF));
[ exact (ltac:(oF' 0x971a8%Z)) | reflexivity | exact (ltac:(oD' 0x971a8%Z)) | reflexivity | gres; rwH; reflexivity | rewrite art_u_lit by lia; reflexivity
| exact CTF2 | apply bytes_le_to_Z_8 | gres; rwH; reflexivity | exact WTF2 ]
| ]. wpc. rewrite art_zb_add.
change (wbytes ?M0 (Z_to_bv 64 2149320) (word_to_le_bytes 8 (Z_to_bv 64 (TF + (size + 1))))) with (Wn 8 M0 2149320 (TF + (size + 1))).
zstep (ltac:(oF' 0x971ac%Z)) (ltac:(oD' 0x971ac%Z)).
stepn (ltac:(oF' 0x971b0%Z)) (ltac:(oD' 0x971b0%Z)). rwH. rewrite art_zb_srli by lia. rewrite DT0.
zstep (ltac:(oF' 0x971b4%Z)) (ltac:(oD' 0x971b4%Z)).
replace (size + 1 + -1 + TF) with (size + TF) by lia.
stepn (ltac:(oF' 0x971b8%Z)) (ltac:(oD' 0x971b8%Z)). rwH. rewrite art_zb_srli by lia. rewrite DT1.
zbft (ltac:(oF' 0x971bc%Z)) (ltac:(oD' 0x971bc%Z)).
stepn (ltac:(oF' 0x971c0%Z)) (ltac:(oD' 0x971c0%Z)). rwH. rewrite art_zb_srli by lia. rewrite DT2.
zbtk (ltac:(oF' 0x971c4%Z)) (ltac:(oD' 0x971c4%Z)).
zsd (ltac:(oF' 0x971dc%Z)) (ltac:(oD' 0x971dc%Z)) (s - 208) TF ltac:(rewok Wf).
zstep (ltac:(oF' 0x971e0%Z)) (ltac:(oD' 0x971e0%Z)).
zstep (ltac:(oF' 0x971e4%Z)) (ltac:(oD' 0x971e4%Z)).
match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (Cblk3 : cellA X (2149320 + 16) 8 blk) by zcell end.
zld (ltac:(oF' 0x971e8%Z)) (ltac:(oD' 0x971e8%Z)) (2149320 + 16) Cblk3.
zbft (ltac:(oF' 0x971ec%Z)) (ltac:(oD' 0x971ec%Z)).
zstep (ltac:(oF' 0x971f0%Z)) (ltac:(oD' 0x971f0%Z)).
stepn (ltac:(oF' 0x971f4%Z)) (ltac:(oD' 0x971f4%Z)). rwH. rewrite (art_zb_srli_exact (TF * 2 ^ 44) 41 (8 * TF)) by lia.
zstep (ltac:(oF' 0x971f8%Z)) (ltac:(oD' 0x971f8%Z)).
match goal with |- msteps _ (mkst _ _ ?X _) _ =>
assert (Lra : cellA X (s - 216) 8 0x970e8) by zcell; assert (Ls0 : cellA X (s - 224) 8 (s - 136)) by zcell end.
zld (ltac:(oF' 0x971fc%Z)) (ltac:(oD' 0x971fc%Z)) (s - 216) Lra.
zld (ltac:(oF' 0x97200%Z)) (ltac:(oD' 0x97200%Z)) (s - 224) Ls0.
zstep (ltac:(oF' 0x97204%Z)) (ltac:(oD' 0x97204%Z)).
stepret (ltac:(oF' 0x97208%Z)) (ltac:(oD' 0x97208%Z)) (Z_to_bv 64 0x970e8 : word) ltac:(rwH; reflexivity).
first [apply mst_refl | replace (s - 224 + 16) with (s - 208) by lia; apply mst_refl | replace (s - 208 + -16 + 16) with (s - 208) by lia; apply mst_refl].
- do 8 (split; [kept_solve|]). intros r Hr. rewrite <- (K1 r Hr). cbv in Hr.
destruct Hr as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]; kept_solve. }
destruct S2 as (r2 & X2 & RUN2 & EX2 & P10 & P2 & P8 & P9 & P18 & P19 & P20 & P21 & K2).
assert (S3 : exists r3 X3,
msteps ASEGS (mkst r2 (0x970e8 : word) X2 rom) (mkst r3 (0x8aa8c : word) X3 rom)
/\ X3 = Wn 8 X2 (blk + 8 * TF) size
/\ getr r3 10 = Z_to_bv 64 (blk + 8 * TF + 8) /\ getr r3 11 = Z_to_bv 64 trp /\ getr r3 12 = Z_to_bv 64 (8 * size) /\ getr r3 1 = Z_to_bv 64 0x97108
/\ getr r3 2 = Z_to_bv 64 (s - 208) /\ getr r3 8 = Z_to_bv 64 (s - 136) /\ getr r3 9 = Z_to_bv 64 2149320 /\ getr r3 18 = Z_to_bv 64 (size + 1)
/\ (forall r : reg, In r [3; 4; 22; 23; 24; 25; 26; 27]%bv -> getr r3 r = getr regs r)).
{ subst X2 X1.
match goal with |- exists r3 X3, msteps _ (mkst _ _ ?X _) _ /\ _ => assert (Ctrp2 : cellA X (s - 104) 8 trp) by zcell end.
eexists _, _. split; [|split; [reflexivity|]].
- zbft (ltac:(oF' 0x970e8%Z)) (ltac:(oD' 0x970e8%Z)).
stepn (ltac:(oF' 0x970ec%Z)) (ltac:(oD' 0x970ec%Z)). rwH.
match goal with |- context [v_slliw (Z_to_bv 64 0) ?k] => replace (v_slliw (Z_to_bv 64 0) k) with (Z_to_bv 64 0 : word) by (apply bv_eq; vm_compute; reflexivity) end.
zld (ltac:(oF' 0x970f0%Z)) (ltac:(oD' 0x970f0%Z)) (s - 104) Ctrp2.
stepn (ltac:(oF' 0x970f4%Z)) (ltac:(oD' 0x970f4%Z)). rwH. rewrite art_zb_or by lia. rewrite Z.lor_0_l.
zsd (ltac:(oF' 0x970f8%Z)) (ltac:(oD' 0x970f8%Z)) (blk + 8 * TF) size ltac:(rewok Wblk).
zstep (ltac:(oF' 0x970fc%Z)) (ltac:(oD' 0x970fc%Z)).
zstep (ltac:(oF' 0x97100%Z)) (ltac:(oD' 0x97100%Z)).
stepn (ltac:(oF' 0x97104%Z)) (ltac:(oD' 0x97104%Z)).
replace (size * 2 ^ 3) with (8 * size) by lia. apply mst_refl.
- do 8 (split; [kept_solve|]). intros r Hr. rewrite <- (K2 r Hr). cbv in Hr.
destruct Hr as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]; kept_solve. }
destruct S3 as (r3 & X3 & RUN3 & EX3 & Q10' & Q11' & Q12' & Q1' & Q2' & Q8' & Q9' & Q18' & K3).
assert (G3 : mem_grows M X3).
{ subst X3 X2 X1. repeat (eapply mem_grows_trans; [|apply Wn_grows]). apply mem_grows_refl. }
destruct (rdn_words (Z.to_nat size) X3 trp ltac:(lia) ltac:(rewrite Z2Nat.id by lia; lia)
ltac:(intros i Hi; apply (rcell_grows M X3 _ G3); apply RC; rewrite Z2Nat.id in Hi by lia; lia)) as (bs & Rbs).
pose proof (rdn_length _ _ _ _ _ Rbs) as Lbs.
assert (MCH : mcH X3 (Z_to_bv 64 (blk + 8 * TF + 8)) (Z_to_bv 64 trp) (8 * size) bs).
{ constructor.
- lia.
- rewrite Lbs. lia.
- rewrite Lbs. exact Rbs.
- rewrite Lbs. subst X3 X2 X1.
match goal with |- store_ok _ ?X ?a ?n = true => change (wokA X (blk + 8 * TF + 8) n) end. rewok Wblk.
- rewrite !art_u_lit by lia. unfold apart in A4. lia.
- rewrite art_u_lit by lia. lia.
- rewrite art_u_lit by lia. lia. }
destruct (int_memcpy_run X3 (Z_to_bv 64 (blk + 8 * TF + 8)) (Z_to_bv 64 trp) (8 * size) bs rom MCH r3 (Z_to_bv 64 0x97108 : word)
ltac:(unfold ret_ok; apply bv_eq; vm_compute; reflexivity) Q1' Q10' Q11' Q12') as (r4 & RUN4 & K4).
set (X4 := wbytes X3 (Z_to_bv 64 (blk + 8 * TF + 8)) bs) in RUN4.
assert (V2 : getr r4 2 = Z_to_bv 64 (s - 208)) by (rewrite (K4 2%bv) by (cbv; tauto); exact Q2').
assert (V8 : getr r4 8 = Z_to_bv 64 (s - 136)) by (rewrite (K4 8%bv) by (cbv; tauto); exact Q8').
assert (V9 : getr r4 9 = Z_to_bv 64 2149320) by (rewrite (K4 9%bv) by (cbv; tauto); exact Q9').
assert (V18 : getr r4 18 = Z_to_bv 64 (size + 1)) by (rewrite (K4 18%bv) by (cbv; tauto); exact Q18').
assert (V1 : getr r4 1 = Z_to_bv 64 0x97108) by (rewrite (K4 1%bv) by (cbv; tauto); exact Q1').
subst X3 X2 X1.
assert (C208 : cellA X4 (s - 208) 8 TF) by (unfold X4; apply cell_wb_other; [lia | rewrite Lbs; lia | lia | cbn; lia | rewrite Lbs; unfold apart in A2 |- *; cbn; lia | zcell]).
pose proof (cell8_lo _ _ _ C208) as C208w.
assert (CSTw : cellA X4 (2149320 + 24) 4 ST) by (unfold X4; apply cell_wb_other; [lia | rewrite Lbs; lia | lia | cbn; lia | rewrite Lbs; unfold apart in A2 |- *; cbn; lia | zcell]).
assert (C136 : cellA X4 (s - 136) 8 0) by (unfold X4; apply cell_wb_other; [lia | rewrite Lbs; lia | lia | cbn; lia | rewrite Lbs; unfold apart in A2 |- *; cbn; lia | zcell]).
assert (C152 : cellA X4 (s - 152) 8 0x993b0) by (unfold X4; apply cell_wb_other; [lia | rewrite Lbs; lia | lia | cbn; lia | rewrite Lbs; unfold apart in A2 |- *; cbn; lia | zcell]).
assert (C160 : cellA X4 (s - 160) 8 nd) by (unfold X4; apply cell_wb_other; [lia | rewrite Lbs; lia | lia | cbn; lia | rewrite Lbs; unfold apart in A2 |- *; cbn; lia | zcell]).
assert (C168 : cellA X4 (s - 168) 8 (U (getr regs 9))) by (unfold X4; apply cell_wb_other; [lia | rewrite Lbs; lia | lia | cbn; lia | rewrite Lbs; unfold apart in A2 |- *; cbn; lia | zcell]).
assert (C176 : cellA X4 (s - 176) 8 (U (getr regs 18))) by (unfold X4; apply cell_wb_other; [lia | rewrite Lbs; lia | lia | cbn; lia | rewrite Lbs; unfold apart in A2 |- *; cbn; lia | zcell]).
assert (C184 : cellA X4 (s - 184) 8 (U (getr regs 19))) by (unfold X4; apply cell_wb_other; [lia | rewrite Lbs; lia | lia | cbn; lia | rewrite Lbs; unfold apart in A2 |- *; cbn; lia | zcell]).
assert (C192 : cellA X4 (s - 192) 8 (U (getr regs 20))) by (unfold X4; apply cell_wb_other; [lia | rewrite Lbs; lia | lia | cbn; lia | rewrite Lbs; unfold apart in A2 |- *; cbn; lia | zcell]).
assert (C200 : cellA X4 (s - 200) 8 (U (getr regs 21))) by (unfold X4; apply cell_wb_other; [lia | rewrite Lbs; lia | lia | cbn; lia | rewrite Lbs; unfold apart in A2 |- *; cbn; lia | zcell]).
assert (C120 : cellA X4 (s - 120) 8 0x99894) by (unfold X4; apply cell_wb_other; [lia | rewrite Lbs; lia | lia | cbn; lia | rewrite Lbs; unfold apart in A2 |- *; cbn; lia | zcell]).
assert (C128 : cellA X4 (s - 128) 8 (U (getr regs 8))) by (unfold X4; apply cell_wb_other; [lia | rewrite Lbs; lia | lia | cbn; lia | rewrite Lbs; unfold apart in A2 |- *; cbn; lia | zcell]).
assert (WST4 : wokA X4 (2149320 + 24) 4) by (unfold X4; apply wok_wb; rewok Wsto).
assert (WND4 : wokA X4 (nd + 12) 4) by (unfold X4; apply wok_wb; rewok Wnd).
assert (W136 : wokA X4 (s - 136) 8) by (unfold X4; apply wok_wb; rewok Wf).
pose proof (Z.div_pos TF (2 ^ 16) ltac:(lia) ltac:(lia)) as D16. pose proof (Z.div_lt_upper_bound TF (2 ^ 16) 16 ltac:(lia) ltac:(lia)) as D16'.
pose proof (lxor_pow20_nz (size + 1 + ST) ltac:(lia)) as LX.
eexists _, (Wn 4 (Wn 8 (Wn 4 X4 (2149320 + 24) (ST + (size + 1))) (s - 136) 0) (nd + 12) (TF + 1)).
split; [|split; [|split; [|split; [|split; [|split; [|split; [|split; [|split]]]]]]]].
- eapply msteps_trans; [exact RUN1|]. eapply msteps_trans; [exact RUN2|]. eapply msteps_trans; [exact RUN3|]. eapply msteps_trans; [exact RUN4|].
zld (ltac:(oF' 0x97108%Z)) (ltac:(oD' 0x97108%Z)) (s - 208) C208.
stepn (ltac:(oF' 0x9710c%Z)) (ltac:(oD' 0x9710c%Z)). rwH. rewrite art_zb_srli by lia.
stepn (ltac:(oF' 0x97110%Z)) (ltac:(oD' 0x97110%Z)). rwH. unfold v_andi. rewrite art_u_lit by lia. change (bv_wrap 64 (-16)) with 18446744073709551600.
rewrite land_high_mask_0 by lia.
zstep (ltac:(oF' 0x97114%Z)) (ltac:(oD' 0x97114%Z)).
zstep (ltac:(oF' 0x97118%Z)) (ltac:(oD' 0x97118%Z)).
replace (2149320 + 0 + 24) with (2149320 + 24) by lia.
chain_step; [reflexivity
| eapply (art_step_amoadd_w_rd _ _ _ _ _ _ _ _ _ _ _ (Z_to_bv 64 (2149320 + 24)) (Z_to_bv 64 (size + 1)) (Z_to_bv 64 ST));
[ exact (ltac:(oF' 0x9711c%Z)) | reflexivity | exact (ltac:(oD' 0x9711c%Z)) | reflexivity | gres; rwH; reflexivity | rewrite art_u_lit by lia; reflexivity
| exact CSTw | apply art_bytes4; lia | rewrite art_u_lit by lia; lia | gres; rwH; reflexivity | exact WST4 ]
| ]. wpc. rewrite art_zb_add. rewrite art_v_lw_small by lia.
change (wbytes ?M0 (Z_to_bv 64 (2149320 + 24)) (word_to_le_bytes 4 (Z_to_bv 64 (ST + (size + 1))))) with (Wn 4 M0 (2149320 + 24) (ST + (size + 1))).
stepn (ltac:(oF' 0x97120%Z)) (ltac:(oD' 0x97120%Z)).
zstep (ltac:(oF' 0x97124%Z)) (ltac:(oD' 0x97124%Z)).
stepn (ltac:(oF' 0x97128%Z)) (ltac:(oD' 0x97128%Z)). rwH. rewrite (art_zb_srli_exact (ST * 2 ^ 32) 32 ST) by lia.
zstep (ltac:(oF' 0x9712c%Z)) (ltac:(oD' 0x9712c%Z)).
match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (C136a : cellA X (s - 136) 8 0) by zcell end.
zld (ltac:(oF' 0x97130%Z)) (ltac:(oD' 0x97130%Z)) (s - 136) C136a.
stepn (ltac:(oF' 0x97134%Z)) (ltac:(oD' 0x97134%Z)). rwH.
match goal with |- context [v_xor (Z_to_bv 64 (size + 1 + ST)) ?L] =>
replace (v_xor (Z_to_bv 64 (size + 1 + ST)) L) with (Z_to_bv 64 (Z.lxor (size + 1 + ST) (2 ^ 20)) : word)
by (symmetry; replace L with (Z_to_bv 64 (2 ^ 20) : word) by (apply bv_eq; vm_compute; reflexivity); apply art_zb_xor; lia) end.
match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (C208a : cellA X (s - 208) 4 TF) by zcell end.
zlw (ltac:(oF' 0x97138%Z)) (ltac:(oD' 0x97138%Z)) (s - 208) C208a.
stepn (ltac:(oF' 0x9713c%Z)) (ltac:(oD' 0x9713c%Z)). rwH. rewrite art_zb_sltiu by lia.
replace (if Z.lxor (size + 1 + ST) (2 ^ 20) <? 1 then 1 else 0) with 0 by (destruct (Z.ltb_spec (Z.lxor (size + 1 + ST) (2 ^ 20)) 1); lia).
zstep (ltac:(oF' 0x97140%Z)) (ltac:(oD' 0x97140%Z)).
zsd (ltac:(oF' 0x97144%Z)) (ltac:(oD' 0x97144%Z)) (s - 136) 0 ltac:(apply wok_Wn; exact W136).
stepn (ltac:(oF' 0x97148%Z)) (ltac:(oD' 0x97148%Z)). rwH. unfold v_addiw. rewrite art_u_lit by lia.
replace (bv_swrap 32 (TF + 1)) with (TF + 1) by (unfold bv_swrap, bv_wrap; change (bv_half_modulus 32) with (2 ^ 31); change (bv_modulus 32) with (2 ^ 32); rewrite Z.mod_small; lia).
match goal with |- msteps _ (mkst _ _ ?X _) _ =>
assert (E152 : cellA X (s - 152) 8 0x993b0) by zcell; assert (E160 : cellA X (s - 160) 8 nd) by zcell;
assert (E168 : cellA X (s - 168) 8 (U (getr regs 9))) by zcell; assert (E176 : cellA X (s - 176) 8 (U (getr regs 18))) by zcell;
assert (E184 : cellA X (s - 184) 8 (U (getr regs 19))) by zcell; assert (E192 : cellA X (s - 192) 8 (U (getr regs 20))) by zcell;
assert (E200 : cellA X (s - 200) 8 (U (getr regs 21))) by zcell end.
zld (ltac:(oF' 0x9714c%Z)) (ltac:(oD' 0x9714c%Z)) (s - 152) E152.
zld (ltac:(oF' 0x97150%Z)) (ltac:(oD' 0x97150%Z)) (s - 160) E160.
zld (ltac:(oF' 0x97154%Z)) (ltac:(oD' 0x97154%Z)) (s - 168) E168. rewrite Z_to_bv_bv_unsigned.
zld (ltac:(oF' 0x97158%Z)) (ltac:(oD' 0x97158%Z)) (s - 176) E176. rewrite Z_to_bv_bv_unsigned.
zld (ltac:(oF' 0x9715c%Z)) (ltac:(oD' 0x9715c%Z)) (s - 184) E184. rewrite Z_to_bv_bv_unsigned.
zld (ltac:(oF' 0x97160%Z)) (ltac:(oD' 0x97160%Z)) (s - 192) E192. rewrite Z_to_bv_bv_unsigned.
zld (ltac:(oF' 0x97164%Z)) (ltac:(oD' 0x97164%Z)) (s - 200) E200. rewrite Z_to_bv_bv_unsigned.
zstep (ltac:(oF' 0x97168%Z)) (ltac:(oD' 0x97168%Z)).
stepret (ltac:(oF' 0x9716c%Z)) (ltac:(oD' 0x9716c%Z)) (Z_to_bv 64 0x993b0 : word) ltac:(rwH; reflexivity).
replace (s - 208 + 64) with (s - 144) by lia.
match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (E136 : cellA X (s - 136) 8 0) by zcell end.
zld (ltac:(oF' 0x993b0%Z)) (ltac:(oD' 0x993b0%Z)) (s - 136) E136.
zsw (ltac:(oF' 0x993b4%Z)) (ltac:(oD' 0x993b4%Z)) (nd + 12) (TF + 1) ltac:(apply wok_Wn; apply wok_Wn; exact WND4).
zbft (ltac:(oF' 0x993b8%Z)) (ltac:(oD' 0x993b8%Z)).
match goal with |- msteps _ (mkst _ _ ?X _) _ =>
assert (E120 : cellA X (s - 120) 8 0x99894) by zcell; assert (E128 : cellA X (s - 128) 8 (U (getr regs 8))) by zcell end.
zld (ltac:(oF' 0x993bc%Z)) (ltac:(oD' 0x993bc%Z)) (s - 120) E120.
zld (ltac:(oF' 0x993c0%Z)) (ltac:(oD' 0x993c0%Z)) (s - 128) E128. rewrite Z_to_bv_bv_unsigned.
zstep (ltac:(oF' 0x993c4%Z)) (ltac:(oD' 0x993c4%Z)).
stepret (ltac:(oF' 0x993c8%Z)) (ltac:(oD' 0x993c8%Z)) (Z_to_bv 64 0x99894 : word) ltac:(rwH; reflexivity).
replace (s - 144 + 32) with (s - 112) by lia. apply mst_refl.
- kept_solve.
- intros r Hr.
assert (KK : In r [3; 4; 22; 23; 24; 25; 26; 27]%bv -> getr r4 r = getr regs r).
{ intros Hr'. rewrite (K4 r) by (clear -Hr'; cbv in Hr' |- *; intuition). apply K3. exact Hr'. }
cbv in Hr. destruct Hr as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]]]]]]];
gres; first [ reflexivity | apply KK; cbv; tauto ].
- unfold X4. do 3 (eapply mem_grows_trans; [|apply Wn_grows]). eapply mem_grows_trans; [exact G3 | apply wbytes_grows].
- intros x (O1 & O2 & O3 & O4 & O5 & O6). unfold STO in O4, O5. pose proof (u64_range x). unfold X4.
rewrite !Wn_outside by (first [lia | cbn; lia]).
rewrite MemSplit.wbytes_outside by (rewrite ?Lbs, ?art_u_lit by lia; lia).
rewrite !Wn_outside by (first [lia | cbn; lia]). reflexivity.
- apply cell_Wn_other; [lia|cbn; lia|lia|cbn; lia|unfold apart in A3 |- *; cbn; lia|].
apply cell_Wn_other; [lia|cbn; lia|lia|cbn; lia|unfold apart; cbn; lia|].
apply cell_Wn_other; [lia|cbn; lia|lia|cbn; lia|unfold apart; cbn; lia|].
replace (TF + size + 1) with (TF + (size + 1)) by lia. unfold X4; apply cell_wb_other; [lia | rewrite Lbs; lia | lia | cbn; lia | rewrite Lbs; unfold apart in A2 |- *; cbn; lia | zcell].
- apply cell_Wn_other; [lia|cbn; lia|lia|cbn; lia|unfold apart in A3 |- *; cbn; lia|].
apply cell_Wn_other; [lia|cbn; lia|lia|cbn; lia|unfold apart; cbn; lia|].
replace (ST + size + 1) with (ST + (size + 1)) by lia. apply cell_Wn_hit; cbn; lia.
- apply cell_Wn_other; [lia|cbn; lia|lia|cbn; lia|unfold apart in A3 |- *; cbn; lia|].
apply cell_Wn_other; [lia|cbn; lia|lia|cbn; lia|unfold apart; cbn; lia|].
apply cell_Wn_other; [lia|cbn; lia|lia|cbn; lia|unfold apart; cbn; lia|]. unfold X4; apply cell_wb_other; [lia | rewrite Lbs; lia | lia | cbn; lia | rewrite Lbs; unfold apart in A2 |- *; cbn; lia | zcell].
- apply cell_Wn_other; [lia|cbn; lia|lia|cbn; lia|unfold apart; cbn; lia|].
apply cell_Wn_other; [lia|cbn; lia|lia|cbn; lia|unfold apart in A1 |- *; cbn; lia|].
apply cell_Wn_other; [lia|cbn; lia|lia|cbn; lia|unfold apart in A3 |- *; cbn; lia|].
unfold X4; apply cell_wb_other; [lia | rewrite Lbs; lia | lia | cbn; lia | rewrite Lbs; unfold apart in A3 |- *; cbn; lia | zcell].
- apply cell_Wn_hit; cbn; lia.
Qed.
End SE.
End STORE.
End FPX.
