(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import PropExec CatExec CatSim SeqExec StepTac StoreOk Hoare WalkTac MmapSim As0StepLib As0Tables
ArtMem ArtRegs ArtAtomics ArtAtomics2 ArtTac ArtFxTac JbtLeaf JbtAllocG JbtPoison ArtRuns ArtRunsMem JbtFp JbtFxQ JbtRecycle5R.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLia. Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLiaT.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import SecKit. From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__JbtRecycle5E () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Init.Peano."; "Corelib.Lists.ListDef."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.Riscv.Prelude."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.ArtMem."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CatSim."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.JbtFp."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.JbtFxQ."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.JbtRecycle5E."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.StoreOk."; "OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.AsanUbsan.M."; "Stdlib.Lists.List."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["1app"; "1cons"; "1length"; "1list"; "1nil"; "1option"; "1pair"; "1prod"; "2I"; "2and"; "2eq"; "2ex"; "2not"; "3le"; "4Forall"; "4firstn"]; ["4map"; "4skipn"; "5Z"; "0GL"; "0HI"; "6bvmap"; "0M"; "0M'"; "7apart"; "7cell"; "7wr"; "8msteps"; "9art_agree"; "9art_out"; ":art_qbatch"; ":art_qbytes"]; [":art_qhead"; ":art_qlist"; ":art_qsep"; ":qb_addr"; ":qb_size"; ";art_qin"; ";art_qlast"; ";art_rcy_npop"; "<getr"; "<mkst"; "=mem_grows"; ">loaded_segments"; "?In"; "@add"; "@le"; "@lt"]; ["@of_nat"; "@pow"; "0b"; "0fx"; "0l"; "0l1"; "0l2"; "0mn"; "0p"; "0pp"; "0r"; "0regs"; "0regs'"; "0rom"; "0rr"; "ABV"]; ["AZ_to_bv"; "Abv"; "0tf"; "0tmp"; "0x"; "0z"]]).
Local Ltac lia := L5FastLiaT.plia1.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
#[local] Abbreviation ASEGS := AsanUbsan.M.loaded_segments.
#[local] Abbreviation cellA := (cell AsanUbsan.M.loaded_segments).
#[local] Abbreviation wrA := (wr AsanUbsan.M.loaded_segments).
#[local] Notation "'U' r" := (bv_unsigned r) (at level 10, r at level 9).
Fixpoint art_rcy_npop (mn : Z) (bs : list art_qbatch) : nat :=
match bs with [] => O | b :: r => if mn <? art_qbytes (b :: r) then S (art_rcy_npop mn r) else O end.
Definition art_qlast (bs : list art_qbatch) : Z := match bs with [] => 0 | _ => qb_addr (last bs (0, [], 0)) end.
Definition art_qin (HI : Z) (b : art_qbatch) : Prop := 0x693000 <= qb_addr b /\ qb_addr b + 8192 <= HI /\ 0 <= qb_size b < 2 ^ 64.
Lemma art_qlast_snoc : ltac2:(TCodec.tc2 tcn__JbtRecycle5E "D'3&N%211':'B&Q6&0r2(1r1(4%11:%43;31%73<61%911&Q3%117%>3=31pS6A1pSDA1").
Proof. intros pp b. unfold art_qlast. destruct (pp ++ [b]) eqn:E; [destruct pp; discriminate|]. rewrite <- E. rewrite last_last. reflexivity. Qed.
Lemma art_qhead_app : ltac2:(TCodec.tc2 tcn__JbtRecycle5E "E'3&N%211&<':r2(4%116%43631%611'B&Q0&0r3%23=19%411%513%=3721p091pSFA1pSDB1").
Proof. intros [|p pp] r H; [contradiction|reflexivity]. Qed.
Lemma art_qbytes_cons : ltac2:(TCodec.tc2 tcn__JbtRecycle5E "C&N'3%112':'B&O(1r2r1%33921%511&Q=&Q4%116%916%4221%=3<61pSF?1pS6B1").
Proof. reflexivity. Qed.
Section SE.
Local Abbreviation SEC_T_art_qlist_snoc_pop := (forall (M M' : word -> option byte) HI tmp pp b, art_agree [(0x1396b0 + 160, 32); (qb_addr b, 8); (tmp, 32); (art_qlast pp, if Z.of_nat (length pp) =? 0 then 0 else 8)] M M' ->
art_qsep (pp ++ [b]) -> Forall (art_qin HI) (pp ++ [b]) -> 0x693000 <= HI -> HI <= tmp -> tmp + 32 < 2 ^ 64 ->
art_qlist M pp (art_qhead pp) (art_qlast pp) -> art_qrec M b ->
(pp <> [] -> cellA M' (art_qlast pp) 8 (qb_addr b)) -> cellA M' (qb_addr b) 8 0 ->
art_qlist M' (pp ++ [b]) (art_qhead (pp ++ [b])) (qb_addr b)) (only parsing).
Variable M : ltac:(sec_ty2 constr:(SEC_T_art_qlist_snoc_pop) 0%nat 0%nat).
Variable M' : ltac:(sec_ty2 constr:(SEC_T_art_qlist_snoc_pop) 1%nat 0%nat).
Variable HI : ltac:(sec_ty2 constr:(SEC_T_art_qlist_snoc_pop) 2%nat 0%nat).
Variable tmp : ltac:(sec_ty2 constr:(SEC_T_art_qlist_snoc_pop) 3%nat 0%nat).
Lemma art_qlist_snoc_pop : ltac:(sec_stmt2 constr:(SEC_T_art_qlist_snoc_pop) 4%nat 0%nat).
Proof.
intros pp b AG SEP IN HHI Htmp Htmp' QL QR Cl Cb.
assert (Hb : art_qin HI b) by (apply Forall_app in IN; destruct IN as [_ X]; exact (Forall_inv X)).
destruct Hb as (Hb0 & Hb1 & _).
assert (TR : forall p, art_qin HI p -> (p = b \/ apart (qb_addr p) 8192 (qb_addr b) 8192) -> (qb_addr p = art_qlast pp \/ apart (qb_addr p) 8192 (art_qlast pp) 8 \/ pp = []) -> art_qrec M p -> art_qrec M' p).
{ intros p (P0 & P1 & _) Hpb Hpl (L & C1 & C2 & CI). unfold art_qrec.
assert (T : forall a (k : nat) v, qb_addr p + 8 <= a -> a + Z.of_nat k <= qb_addr p + 8192 -> cellA M a k v -> cellA M' a k v).
{ intros a k v Ha Hk C. apply (art_cell_tr _ M M' a k v AG); [|lia|lia|exact C]. cbn [art_gap fst snd]. unfold apart in *.
split; [lia|]. split; [destruct Hpb as [->|X]; lia|]. split; [lia|]. split; [|exact I].
destruct pp as [|p0 pp0]; [right; unfold art_qlast; change (Z.of_nat (length (@nil art_qbatch)) =? 0) with true; cbv iota; lia|]. replace (Z.of_nat (length (p0 :: pp0)) =? 0) with false by (symmetry; apply Z.eqb_neq; cbn [length]; lia).
destruct Hpl as [X|[X|X]]; [lia|lia|discriminate X]. }
split; [exact L|]. split; [apply T; [lia|cbn; lia|exact C1]|]. split; [apply T; [lia|cbn; lia|exact C2]|].
intros j it Hj. assert (Hjl : (j < length (qb_items p))%nat) by (apply nth_error_Some; congruence). apply T; [lia|cbn; lia|exact (CI j it Hj)]. }
assert (TL : forall p v, art_qin HI p -> apart (qb_addr p) 8192 (qb_addr b) 8192 -> apart (qb_addr p) 8192 (art_qlast pp) 8 -> pp <> [] -> cellA M (qb_addr p) 8 v -> cellA M' (qb_addr p) 8 v).
{ intros p v (P0 & P1 & _) Apb Apl Hne C. apply (art_cell_tr _ M M' _ _ _ AG); [|lia|cbn; lia|exact C]. cbn [art_gap fst snd]. unfold apart in *.
destruct pp as [|p0 pp0]; [contradiction|]. replace (Z.of_nat (length (p0 :: pp0)) =? 0) with false by (symmetry; apply Z.eqb_neq; cbn [length]; lia).
change (Z.of_nat 8) with 8. repeat split; try exact I; lia. }
destruct pp as [|p0 pp0].
- cbn [app art_qhead art_qlist]. split; [reflexivity|]. split; [apply TR; [apply (Forall_inv IN)|left; reflexivity|right; right; reflexivity|exact QR]|]. split; [reflexivity|]. split; [exact Cb|reflexivity].
- set (pp := p0 :: pp0) in *. assert (Hpp : pp <> []) by discriminate.
assert (INNER : forall s, s <> [] -> (forall p, In p s -> In p pp) -> qb_addr (last s (0, [], 0)) = art_qlast pp -> art_qsep (s ++ [b]) ->
art_qlist M s (art_qhead s) (art_qlast pp) -> art_qlist M' (s ++ [b]) (art_qhead s) (qb_addr b)).
{ induction s as [|p r IHs]; [contradiction|]. intros _ Hsub Hlast SEPs QLs.
assert (Hpin : art_qin HI p). { apply Forall_app in IN. destruct IN as [X _]. exact (proj1 (Forall_forall _ _) X p (Hsub p (or_introl eq_refl))). }
destruct QLs as (_ & QRp & _ & Cn & QLr). cbn [app art_qsep] in SEPs. destruct SEPs as (_ & _ & Fp & SEPr).
assert (Apb : apart (qb_addr p) 8192 (qb_addr b) 8192). { apply (proj1 (Forall_forall _ _) Fp b). apply in_or_app. right. left. reflexivity. }
destruct r as [|p2 r2].
- cbn [last] in Hlast. cbn [app art_qlist art_qhead]. split; [reflexivity|]. split; [apply TR; [exact Hpin|right; exact Apb|left; exact Hlast|exact QRp]|]. split; [exact I|].
split; [rewrite Hlast; apply Cl; exact Hpp|]. split; [reflexivity|].
split; [apply TR; [apply Forall_app in IN; destruct IN as [_ X]; exact (Forall_inv X)|left; reflexivity|right; left|exact QR]|].
{ destruct Hpin as (Q0 & Q1 & _). rewrite <- Hlast. unfold apart in *. lia. }
split; [reflexivity|]. split; [exact Cb|reflexivity].
- assert (Hl2 : In (last (p2 :: r2) (0, [], 0)) (p2 :: r2)) by (apply exists_last in Hpp; destruct (exists_last (l := p2 :: r2) ltac:(discriminate)) as (l' & a' & E); rewrite E, last_last; apply in_or_app; right; left; reflexivity).
assert (Apl : apart (qb_addr p) 8192 (art_qlast pp) 8).
{ rewrite <- Hlast. change (last (p :: p2 :: r2) (0, [], 0)) with (last (p2 :: r2) (0, [], 0)).
pose proof (proj1 (Forall_forall _ _) Fp _ (in_or_app _ _ _ (or_introl Hl2))) as X. unfold apart in *. lia. }
change ((p :: p2 :: r2) ++ [b]) with (p :: (p2 :: r2) ++ [b]). cbn [art_qlist art_qhead]. split; [reflexivity|].
split; [apply TR; [exact Hpin|right; exact Apb|right; left; exact Apl|exact QRp]|]. split; [exact I|].
split; [change (art_qhead ((p2 :: r2) ++ [b])) with (qb_addr p2); apply TL; [exact Hpin|exact Apb|exact Apl|exact Hpp|exact Cn]|].
apply IHs; [discriminate|intros q Hq; apply Hsub; right; exact Hq|exact Hlast|exact SEPr|exact QLr]. }
rewrite (art_qhead_app pp [b] Hpp). apply INNER; [exact Hpp|tauto|reflexivity|exact SEP|exact QL].
Qed.
End SE.
Lemma art_qsep_mid : ltac2:(TCodec.tc2 tcn__JbtRecycle5E "Q<'3&N%211&Q2&0r3(1r2r1%33821%63951%811'9r4(4%11>%:3?;1%=3@41%?11'>&H&Q3%11>+XP0%31;%543212qSBI1%83J1>%844565qSFL1%;3M1G%:1H%<419:9qSFQ01%?3Q11MqSBQ21%A3Q31G%I271%J2;1%K2E1p0M1pS>Q71pT:Q91pS<Q91").
Proof.
induction l1 as [|p l1 IH]; intros x l2 S; cbn [app art_qsep] in *.
- destruct S as (S0 & S1 & SF & SR). repeat split; try assumption; constructor.
- destruct S as (S0 & S1 & SF & SR). destruct (IH x l2 SR) as (A & B & C & D). apply Forall_app in SF. destruct SF as [SF1 SF2].
pose proof (Forall_inv SF2) as Fx. pose proof (Forall_inv_tail SF2) as Fl2.
split; [split; [exact S0|split; [exact S1|split; [apply Forall_app; split; [exact SF1|constructor; [exact Fx|constructor]]|exact A]]]|].
split; [constructor; assumption|]. split; [exact C|constructor; assumption].
Qed.
Lemma art_qbytes_nonneg : ltac2:(TCodec.tc2 tcn__JbtRecycle5E "B'B'3&N%211'>&Q5r2%211r1%53721&Q>z&O%117%4231p061pS:=1pQ:A1").
Proof. induction l as [|b r IH]; intros F; [cbn; lia|]. rewrite art_qbytes_cons. pose proof (Forall_inv F) as (_ & _ & Hs). pose proof (IH (Forall_inv_tail F)). lia. Qed.
Lemma art_out_links : ltac2:(TCodec.tc2 tcn__JbtRecycle5E "Q5'3&N%211'B&M&@'7%1244(6&Q3r1%211+8%54::21qS6=1r3%;4?921%=217&Q<r4%23C51&<'9&Q>%?15%221:&Q?&Q=%124@%32>1%8251%:11p0<1p0@1pT<O1pT:Q21pS:Q21").
Proof.
induction l as [|b r IH]; intros x z O Hin; [destruct Hin|]. cbn [map art_out fst snd] in O. destruct O as [O1 O2].
destruct Hin as [->|Hin]; [exact O1|exact (IH x z O2 Hin)].
Qed.
Lemma art_qlast_in : ltac2:(TCodec.tc2 tcn__JbtRecycle5E "J'3&N%211&<':r1(4%116%43631%611';'9&Q<r3%23=91'B&Q6%114&Q3%11>%@3531%:271qSBE1%=2F1p0?1pSDG1").
Proof.
intros pp H. destruct (exists_last H) as (l' & a & E). exists a. split; [rewrite E; apply in_or_app; right; left; reflexivity|].
unfold art_qlast. destruct pp; [contradiction|]. rewrite E, last_last. reflexivity.
Qed.
Section FPX. Context {fx : PropExec.FPState}.
#[using="Type"] Lemma art_rcy_deq_run : ltac2:(TCodec.tc2 tcn__JbtRecycle5E "[D'3&N%211&Ey5'R1yR0%211%5241'5y8%611%311p061'B':&Q8r8(QO+2(8%33A21%6251&R0r4%22C1%;3C41r9+:%;3I19%>231+QWUe@%92J1%B3J31r:+;%B3Q01@%E231r5%@2Q11%I3Q131r;+>%I3Q71G%L231&Q@&2r<%22Q?1%411%K2Q<1%Q43Q<71+?%Q33QA1Q1%Q6271&Q6r=%211%Q32QD1%Q<3QD51+@%Q;3QI1Q9%Q>261r?%B2QO1%D11%Q;2QL1%QD3QL51r>+5%QD3R21QB%QG231&Q0r@%211%QD2R51%QM3R551'9&Q>z%221Q>&Q?&OrA%211%42QC1%9261&Q2&0rB%23RI71%411'>&Q5%11JrC%83RO71%53S031+Vb\P0%E21Q4%F2KQ5&Q=+Q0%22N1&QA+R0%22RG1%J241rFrG%F3S=21%R12S>1%R311+Q8%:2RO1%Q2231rH%M3SD81%Q411+QO%@2S51%Q8231&J&Q;%241@MF+U0%I2RO1%544B1IrI&Q3r1%211+8%;4:521qS6T51rJrK%QA3T821%Q>3T941&I+UH%Q82S>1u8rL%QN11%65FA431+U@%Q>2SD1rE%:5J>271+H%QB2Q31rM%R711%?5OB3<1%QF2KG%A5Q1=1>Q@&<rO(4%11TO%TB3TO31%511rQ0%RL11%TF3TGQA1p041&Q1rN%SB16%342761rQ2%S411%64?21Q6';'K&Q9vQCrQ3+Z_a0%U23U>1U0/01U>rQ1%75652<1r2+Z_cD%U83UD1U6/01UD%<5;41QJ6%>3R261%U>26TCrQ4&?&Q7rQ5%22K1%43V312%S=3V461%TH2V51%TJ11%UA2V21%UJ3V2;1+6%UI3V71UG%UL2D1%TF18%UG2V81%V03V831%V;1V<&Q<(1+1%V23V@1V0+3%V43VB1V2+4%V63VD1V4%V73VEREV5+9%V93VG1V7+<%V;3VI1V9+=%V=3VK1V;+B%V?3VM1V=+C%VA3VO1V?+D%VC3W11VA+E%VE3W31VC+F%VG3W51VE+G%VI3W71VG%VJ3W8RFVH+I%VL3W:1VJ+J%VN3W<1VL+K%W03W>1VN%RD1Q3%Q23Q421%Q33Q551%Q43Q681%Q53Q7;1%Q63Q8=1%Q73Q9@1%Q83Q:C1%Q93Q;F1%Q:3Q<I1%Q;3Q=L1%Q<3Q>O1%Q=3Q?Q21%Q>3Q@VL1%Q?3QAW41%Q@3QBQ71%QA3QCQ:1%QB3QDQ<1%QC3QEQ?1%QD3QFWA1%QE3QGQC1%QG3QHT61%WI2WARA%WJ2R8RB%WL3X421p041pSFQM1&Q:%12S4T=&L'7%12X4X4(6%14X6X6TFU>%24X7X7SGU?%SG14%R53521%R63641&@%74X<X<TGTFqS6XJ1%V43XKRMRJ%44XL;21%V63<61%?31SDTM&A%13Y0RNRO%WD2Y11%WF11%TI5U9U2U6TF1+U8%V12X71%VO16%TM5U=U62TJ1%VG18%TO5U?U8TMTL1%XL3Y9:T;%U15UASDTITNVMp021%TA13%U45UDSGTLU1T7p021%V<2TCU=%W:1S=%U85UHUA2U51%V?2TFTN%W31S@%U;5UKUD2U81%T@4UESB5S:%TA4UFGAU0%W;2@TA'=u1%221SI%W@241%WA261%WB281%WC2:1%WD2>1%WE2B1%WF2F1%WG2J1%WH2M1%WI2Q21%WJ2Q81%WK2QI1%WL2QL1%WM2SK1%WN2T21%WO2T?1qQ@Z01%U02Z11qSJZ71%U22Z81p0U41p0U81p0U=1p0UH1p0UK1p0V11p0V61p0V>1p0VJ1p0VN1p0W21p0W91p0WB1p0WJ1p0WL1p0WO1p0X61p0X<1p0XG1p0Y11p0Y:1p0YC1p0YO1p0Z71p0Z?1pT6ZL1pQ8ZM1pS@ZN1pT8ZO1pQ:[01pSL[21pQ>[31pSH[91pSD[@1pSN[A1").
Proof.
induction rr as [|b rr' IH]; intros pp regs M rom HI tmp mn GL tf H2 H10 H11 H14 H15 H16 H5 Hmn SEP IN HHI Htmp Htmp' Hlen Hqb Wt Wq Wl Cgb Cgl Ctb Ctf Etf QLp QLr;
[cbn in Hmn; lia|].
destruct (art_qsep_mid pp b rr' SEP) as (SEPb & Fpb & Fbr & Fpr).
pose proof (proj1 (Forall_app _ _ _) IN) as [INp INr]. pose proof (Forall_inv INr) as (Hb0 & Hb1 & Hbs). pose proof (Forall_inv_tail INr) as INr'.
pose proof (art_qbytes_nonneg HI _ INp) as Hqp. pose proof (art_qbytes_nonneg HI _ INr') as Hqr'.
rewrite art_qbytes_app, art_qbytes_cons in Hqb. rewrite art_qbytes_cons in Hmn, Cgb. rewrite length_app in Hlen. cbn [length] in Hlen, H16.
destruct QLr as (_ & QRb & _ & Cnx & QLr'). pose proof QRb as (_ & _ & Csz & _).
assert (Hnext : 0 <= art_qhead rr' < 2 ^ 64). { destruct rr' as [|b2 rr2]; cbn [art_qhead]; [lia|]. pose proof (Forall_inv INr') as (X0 & X1 & _). lia. }
assert (Hpl : Z.of_nat (length pp) <> 0 -> 0x693000 <= art_qlast pp /\ art_qlast pp + 8 < 2 ^ 64 /\ apart (art_qlast pp) 8 (qb_addr b) 8192 /\ apart (art_qlast pp) 8 tmp 32 /\ wrA M (art_qlast pp) 8).
{ intros Hn0. assert (Hpp : pp <> []) by (intros ->; cbn in Hn0; lia). destruct (art_qlast_in pp Hpp) as (p & Hp & ->).
pose proof (proj1 (Forall_forall _ _) INp p Hp) as (P0 & P1 & _). pose proof (proj1 (Forall_forall _ _) Fpb p Hp) as Ap.
pose proof (proj1 (Forall_forall _ _) Wl p (in_or_app _ _ _ (or_introl Hp))) as Wp. unfold apart in *. repeat split; try lia; exact Wp. }
destruct (art_rcy_pop regs M rom tmp (Z.of_nat (length pp)) (art_qlast pp) (Z.of_nat (S (length rr'))) (qb_addr b) (art_qhead rr') (qb_size b) (qb_size b + art_qbytes rr') GL (art_qbytes pp) tf
H10 H14 H15 H16 H5 H2 ltac:(lia) Htmp' Hb0 ltac:(lia) ltac:(unfold apart; lia) ltac:(lia) ltac:(lia) Hnext Hbs ltac:(lia) ltac:(lia) Hpl Wt Wq
(proj1 (Forall_forall _ _) Wl b (in_or_app pp (b :: rr') b (or_intror (or_introl eq_refl)))) Cnx Csz Cgb Cgl Ctb Ctf)
as (r1 & M1 & RUN1 & A14 & A15 & A5 & A7 & A16 & A6 & AK & GW1 & AG1 & Cf1 & Cc1 & Cb1 & Cbz1 & Cl0 & Cl1 & Ct0 & Ct1 & Ctb1).
replace (qb_size b + art_qbytes rr' - qb_size b) with (art_qbytes rr') in A7, Cb1 by lia.
replace (Z.of_nat (S (length rr')) - 1) with (Z.of_nat (length rr')) in A16, Cc1 by lia.
assert (QLp1 : art_qlist M1 (pp ++ [b]) (art_qhead (pp ++ [b])) (qb_addr b)).
{ apply (art_qlist_snoc_pop M M1 HI tmp pp b AG1 SEPb ltac:(apply Forall_app; split; [exact INp|constructor; [exact (Forall_inv INr)|constructor]]) HHI Htmp Htmp' QLp QRb); [|exact Cbz1].
intros Hpp. apply Ct1. intros X. destruct pp; [contradiction|cbn in X; lia]. }
assert (QLr1 : art_qlist M1 rr' (art_qhead rr') GL).
{ apply (art_qlist_tr _ M M1 rr' _ _ AG1); [|exact QLr']. apply Forall_forall. intros r Hr. pose proof (proj1 (Forall_forall _ _) INr' r Hr) as (R0 & R1 & _).
pose proof (proj1 (Forall_forall _ _) Fbr r Hr) as Abr. split; [lia|]. split; [lia|]. cbn [art_gap fst snd]. unfold apart in *. repeat split; try exact I; try lia.
destruct pp as [|p0 pp0]; [right; unfold art_qlast; change (Z.of_nat (length (@nil art_qbatch)) =? 0) with true; cbv iota; lia|]. replace (Z.of_nat (length (p0 :: pp0)) =? 0) with false by (symmetry; apply Z.eqb_neq; cbn [length]; lia).
destruct (art_qlast_in (p0 :: pp0) ltac:(discriminate)) as (p & Hp & ->). pose proof (proj1 (Forall_forall _ _) (proj1 (Forall_forall _ _) Fpr p Hp) r Hr) as Apr.
pose proof (proj1 (Forall_forall _ _) INp p Hp) as (P0 & P1 & _). unfold apart in Apr. lia. }
assert (Ctf1 : cellA M1 (tmp + 8) 8 (art_qhead (pp ++ [b]))).
{ destruct pp as [|p0 pp0]; [apply Ct0; reflexivity|]. rewrite art_qhead_app by discriminate. rewrite <- (Etf ltac:(discriminate)). apply Ct1. cbn [length]. lia. }
assert (AG1' : art_agree ([(0x1396b0 + 160, 32); (tmp, 32)] ++ map (fun b0 => (qb_addr b0, 8)) (pp ++ b :: rr')) M M1).
{ eapply art_agree_sub; [exact AG1|]. intros z Hz H. apply art_out_app in H. destruct H as [H1 H2'].
cbn [art_out fst snd] in H1 |- *. split; [tauto|]. split; [exact (art_out_links _ b z H2' (in_or_app pp (b :: rr') b (or_intror (or_introl eq_refl))))|]. split; [tauto|]. split; [|exact I].
destruct pp as [|p0 pp0]; [unfold art_qlast; change (Z.of_nat (length (@nil art_qbatch)) =? 0) with true; cbv iota; lia|]. replace (Z.of_nat (length (p0 :: pp0)) =? 0) with false by (symmetry; apply Z.eqb_neq; cbn [length]; lia).
destruct (art_qlast_in (p0 :: pp0) ltac:(discriminate)) as (p & Hp & ->). exact (art_out_links _ p z H2' (in_or_app _ _ _ (or_introl Hp))). }
cbn [art_rcy_npop]. rewrite art_qbytes_cons. replace (mn <? qb_size b + art_qbytes rr') with true by (symmetry; apply Z.ltb_lt; lia).
destruct (Z_lt_le_dec mn (art_qbytes rr')) as [More|Done].
-
destruct (art_rcy_more r1 M1 rom mn (art_qbytes rr') ltac:(rewrite AK by inl; exact H11) A7 ltac:(lia) ltac:(lia)) as (r2 & RUN2 & BK).
destruct (IH (pp ++ [b]) r2 M1 rom HI tmp mn GL (art_qhead (pp ++ [b]))
ltac:(rewrite BK; rewrite AK by inl; exact H2) ltac:(rewrite BK; rewrite AK by inl; exact H10) ltac:(rewrite BK; rewrite AK by inl; exact H11)
ltac:(rewrite BK; rewrite A14; f_equal; rewrite length_app; cbn [length]; lia) ltac:(rewrite BK; rewrite art_qlast_snoc; exact A15)
ltac:(rewrite BK; exact A16) ltac:(rewrite BK; exact A5) ltac:(lia) ltac:(rewrite <- app_assoc; exact SEP) ltac:(rewrite <- app_assoc; exact IN) HHI Htmp Htmp'
ltac:(rewrite !length_app; cbn [length]; lia) ltac:(rewrite !art_qbytes_app; cbn [art_qbytes fold_right]; lia)
ltac:(eapply wr_grows; [exact GW1|exact Wt]) ltac:(eapply wr_grows; [exact GW1|exact Wq])
ltac:(rewrite <- app_assoc; eapply Forall_impl; [|exact Wl]; intros a Wa; eapply wr_grows; [exact GW1|exact Wa])
Cb1 ltac:(apply Cl1; destruct rr'; [cbn in More; lia|cbn [art_qhead]; pose proof (Forall_inv INr') as (X0 & _); lia])
ltac:(rewrite art_qbytes_app; cbn [art_qbytes fold_right]; replace (art_qbytes pp + (qb_size b + 0)) with (art_qbytes pp + qb_size b) by lia; exact Ctb1)
Ctf1 ltac:(intros _; reflexivity) ltac:(rewrite art_qlast_snoc; exact QLp1) QLr1)
as (r3 & M3 & RUN3 & C14 & C6 & CK & GW3 & AG3 & D1 & D2 & D3 & D4 & D5 & D6 & D7 & D8 & D9 & D10 & D11).
set (k' := art_rcy_npop mn rr') in *. cbn [firstn skipn].
replace (pp ++ b :: firstn k' rr') with ((pp ++ [b]) ++ firstn k' rr') by (rewrite <- app_assoc; reflexivity).
exists r3, M3. split; [eapply msteps_trans; [exact RUN1|]; eapply msteps_trans; [exact RUN2|exact RUN3]|].
split; [exact C14|]. split; [exact C6|].
split; [intros r Hr; rewrite (CK r Hr); rewrite BK; apply AK; exact Hr|].
split; [eapply mem_grows_trans; [exact GW1|exact GW3]|].
split. { replace ((pp ++ [b]) ++ rr') with (pp ++ b :: rr') in AG3 by (rewrite <- app_assoc; reflexivity). eapply art_agree_sub; [eapply art_agree_trans; [exact AG1'|exact AG3]|]. intros z Hz H. rewrite !art_out_app in H. rewrite !art_out_app. tauto. }
repeat (split; [assumption|]). lia.
-
destruct (art_rcy_exit r1 M1 rom mn (art_qbytes rr') ltac:(rewrite AK by inl; exact H11) A7 ltac:(lia) ltac:(lia)) as (r2 & RUN2 & BK).
assert (E0 : art_rcy_npop mn rr' = O). { destruct rr' as [|b2 rr2]; [reflexivity|]. cbn [art_rcy_npop]. replace (mn <? art_qbytes (b2 :: rr2)) with false by (symmetry; apply Z.ltb_ge; lia). reflexivity. }
rewrite E0. cbn [firstn skipn]. rewrite ?firstn_O, ?skipn_O.
exists r2, M1. split; [eapply msteps_trans; [exact RUN1|exact RUN2]|].
split; [rewrite BK; rewrite A14; f_equal; rewrite length_app; cbn [length]; lia|]. split; [rewrite BK; rewrite art_qlast_snoc; exact A6|].
split; [intros r Hr; rewrite BK; apply AK; exact Hr|]. split; [exact GW1|]. split; [exact AG1'|].
split; [exact Cc1|]. split; [exact Cf1|]. split; [exact Cb1|].
split; [intros ->; apply Cl0; reflexivity|]. split; [intros Hne; apply Cl1; destruct rr'; [contradiction|cbn [art_qhead]; pose proof (Forall_inv INr') as (X0 & _); lia]|].
split; [exact Ctf1|]. split; [rewrite art_qbytes_app; cbn [art_qbytes fold_right]; replace (art_qbytes pp + (qb_size b + 0)) with (art_qbytes pp + qb_size b) by lia; exact Ctb1|].
split; [rewrite art_qlast_snoc; exact QLp1|]. split; [exact QLr1|]. split; [lia|lia].
Qed.
End FPX.
