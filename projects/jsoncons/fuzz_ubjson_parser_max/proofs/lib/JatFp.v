(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import PropExec CatExec CatSim SeqExec StepTac StoreOk Hoare WalkTac MmapSim As0StepLib As0Tables
ArtMem ArtRegs ArtAtomics ArtTac JatLeaf JatAllocG JatPoison ArtRuns ArtRunsMem.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__JatFp () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Numbers.BinNums."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.ArtMem."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.ArtRuns."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.JatFp."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.JatLeaf."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.JatPoison."; "OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Asan.M."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["1Some"; "1app"; "1cons"; "1list"; "1nat"; "1nil"; "1option"; "1pair"; "1prod"; "2and"; "2eq"; "2iff"; "3Z"; "0M"; "0M'"; "0M0"]; ["0M1"; "0M2"; "4Wf"; "4Wn"; "4cell"; "5art_reveal"; "5art_unmap"; "5art_zfill"; "6art_agree"; "6art_gap"; "6art_out"; "7art_tsd"; "8art_layout"; "9loaded_segments"; ":add"; ":le"]; [":lt"; ":modulo"; ":of_nat"; ":pow"; ":sub"; "0W"; "0W'"; "0W1"; "0W2"; "0a"; "0a'"; "0b"; "0ctx"; "0hi"; "0i"; "0k"]; ["0key"; "0len"; "0lo"; "0n"; "0n'"; "0r"; ";Z_to_bv"; ";bv"; ";bv_unsigned"; "0t"; "0tp"; "0tsd"; "0v"; "0x"; "0y"; "0z"]]).
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
#[local] Abbreviation cellA := (cell Asan.M.loaded_segments).
#[local] Abbreviation wrA := (wr Asan.M.loaded_segments).
#[local] Notation "'U' r" := (bv_unsigned r) (at level 10, r at level 9).
Fixpoint art_out (W : list (Z * Z)) (z : Z) : Prop :=
match W with [] => True | p :: r => ~ (fst p <= z < fst p + snd p) /\ art_out r z end.
Fixpoint art_gap (W : list (Z * Z)) (a n : Z) : Prop :=
match W with [] => True | p :: r => apart a n (fst p) (snd p) /\ art_gap r a n end.
Definition art_agree (W : list (Z * Z)) (M M' : word -> option byte) : Prop :=
forall x : word, art_out W (U x) -> M' x = M x.
Lemma art_out_app : ltac2:(TCodec.tc2 tcn__JatFp "E'3'8'<%2211%411&;&J&1r3r2%33721r1%6221'9%8263%9264%3221%<251pT0@1pRB?1pR@@1").
Proof. induction W1 as [|p r IH]; intros W2 z; cbn; [tauto|]. rewrite IH. tauto. Qed.
Lemma art_gap_out : ltac2:(TCodec.tc2 tcn__JatFp "K'3'8'<%2211%411&Ir4r3r2%43321'9&O%1264&Q0&N%1298%3281%7251&Jr6%221=p041p0=1pT0E1pS8F1pRDG1pR<F1").
Proof.
induction W as [|p r IH]; intros a n z G Hz; cbn in *; [exact I|]. destruct G as [G1 G2]. split; [|eapply IH; eassumption].
unfold apart in G1. lia.
Qed.
Lemma art_gap_sub : ltac2:(TCodec.tc2 tcn__JatFp "K'3'8'<%2211%411&Ir5r4r3%43321&O%1253&N%1265r6%3219%6231r8%=31<;p031p091p0<1pS:D1pRFE1pS8F1pRDG1pR<F1").
Proof.
induction W as [|p r IH]; intros a n a' n' G H1 H2; cbn in *; [exact I|]. destruct G as [G1 G2]. split; [|eapply IH; eassumption].
unfold apart in *. lia.
Qed.
Lemma art_gap_app : ltac2:(TCodec.tc2 tcn__JatFp "G'3'8'<%2211%411&;&I&1r4r3%33721r2r1%73321'9%93743%:3754%3221%=251pS8A1pRDB1pRBA1pR@B1").
Proof. induction W1 as [|p r IH]; intros W2 a n; cbn; [tauto|]. rewrite IH. tauto. Qed.
Lemma art_agree_refl : ltac2:(TCodec.tc2 tcn__JatFp "C'3'8'<%2211%411'QGyR0%211'6y8%511%311p051&Hr2r1%33211pL51pR<>1").
Proof. intros W M x _. reflexivity. Qed.
Lemma art_agree_trans : ltac2:(TCodec.tc2 tcn__JatFp "N'3'8'<%2211%411'QGyR0%211'6y8%511%311p051&Hr5r3r2%43321&1r7r6%33B21%93187p061p071pQ4=1pQ2>1pQ0?1pRBH1pR@I1").
Proof. intros W1 W2 M0 M1 M2 A1 A2 x Hx. apply art_out_app in Hx. destruct Hx as [H1 H2]. rewrite A2 by exact H2. apply A1. exact H1. Qed.
Lemma art_agree_sub : ltac2:(TCodec.tc2 tcn__JatFp "Q>'3'8'<%2211%411'QGyR0%211'6y8%511%311p051&Hr4r2r1%43321'9&Oz%2215&Q0&Q3+2+R0%3221%52;1%:271&Jr6%221@r8r3%5221p041p081pT0Q31r5%J31I6p031p0H1pNN1pLO1pR>Q81pR<Q91").
Proof. intros W W' M M' A S x Hx. apply A. apply S; [|exact Hx]. pose proof (bv_unsigned_in_range 64 x) as R. change (bv_modulus 64) with (2 ^ 64) in R. lia. Qed.
Lemma art_agree_pt : ltac2:(TCodec.tc2 tcn__JatFp "Q1'3'8'<%2211%411'QGyR0%211'6y8%511%311p051&Hr4r3r2%43321&Jr5&QH%12?5%4231':%:19%61:%33?21p051p0;1pSLF1pNB1pLC1pR<L1").
Proof. intros W M M' x A H. apply A. exact H. Qed.
Lemma art_agree_Wn : ltac2:(TCodec.tc2 tcn__JatFp "Q?'4'QGyR0%211'6y8%511%311p051'<&Ozr2%3221&Q0&Nr3&Q2r5%211%5241&Q3+2+R0%3221%;251&H(2'8%12DD(7r4r6%@11%44II31(5%117%:3831&C%147E8G%>33F1p0@1p0M1pSJQ21pRDQ31pLQ51pS8Q>1").
Proof. intros n M a v Ha Hn x Hx. cbn in Hx. destruct Hx as [Hx _]. apply Wn_outside; assumption. Qed.
Lemma art_agree_Wf : ltac2:(TCodec.tc2 tcn__JatFp "Q>'QGyR0%211'6y8%511%311p051'<'4&Ozr3%3221&Q0&Nr4&Q2%116%4231&Q3+2+R0%3221%:251&H(2'8%12DD(7r5%>1?%34HH21(5%116%93731r6&B%1428FJ%>3431p0@1p0L1pRHQ21pS0Q21pRDQ41pLQ61").
Proof. intros M a k b Ha Hk x Hx. cbn in Hx. destruct Hx as [Hx _]. apply Wf_outside; assumption. Qed.
Lemma art_agree_zfill : ltac2:(TCodec.tc2 tcn__JatFp "K'QGyR0%211'6y8%511%311p051'<&H(2'8%1244(7r2r1%348821(5%116%93731r3&G%13287%>3431pS4@1pS<A1pLC1").
Proof. intros M r len x Hx. cbn in Hx. destruct Hx as [Hx _]. apply art_zfill_out. exact Hx. Qed.
Lemma art_agree_unmap : ltac2:(TCodec.tc2 tcn__JatFp "K'QGyR0%211'6y8%511%311p051'<&H(2'8%1244(7r2r1%348821(5%116%93731r3&F%13287%>3431pS4@1pS<A1pLC1").
Proof. intros M r len x Hx. cbn in Hx. destruct Hx as [Hx _]. apply art_unmap_out. exact Hx. Qed.
Lemma art_agree_reveal : ltac2:(TCodec.tc2 tcn__JatFp "M'QGyR0%211'6y8%511%311p051'<&H(2'8%1244(7r2&Q4r1%2213%54::41(5%118%;3931r3&E%132:8%@3431pRLB1pS6C1pLE1").
Proof. intros M lo hi x Hx. cbn in Hx. destruct Hx as [Hx _]. apply art_reveal_out. lia. Qed.
Lemma art_cell_tr : ltac2:(TCodec.tc2 tcn__JatFp "QF'3'8'<%2211%411'QGyR0%211'6y8%511%311p051'4&Hr6r5r4%43321&Ir7&Q2r3%211%53471&Oz%221;&Q0&N%91>%22@1&Q3+2+R0%3221%8251&D&Mr9%3521DIHr8%55431FKp031p081p0B1p0F1p0M1pSJQ>1pS8Q41pRDQ@1pNQ71pLQ81pR<QA1").
Proof.
intros W M M' a n v A G Ha Hn C. apply (art_cell_agree _ M M'); [|exact Ha|exact Hn|exact C].
intros x Hx. apply A. eapply art_gap_out; eassumption.
Qed.
Lemma art_byte_tr : ltac2:(TCodec.tc2 tcn__JatFp "Q7'3'8'<%2211%411'QGyR0%211'6y8%511%311p051&Hr5r4r3%43321&Jr6&QH%12?5%4231':%519(0%12@:%43@31%91>%42C>%73C21p041p0:1p0@1pRHH1pSLL1pNH1pLI1pR<Q21").
Proof. intros W M M' x b A O H. rewrite (A x O). exact H. Qed.
Lemma art_cell1_of_byte : ltac2:(TCodec.tc2 tcn__JatFp "Q7'QGyR0%211'6y8%511%311p051'<'9&Ozr1%3221&Q0+X0%2241%8241':r4&QFr3%22E1%411(0r2%62F1%32F1%:3F51&D&Mr5u1%4532>1<p061p0B1pSJL1pRDM1pLO1").
Proof. intros M a v Hv H. unfold cell. cbn [rdn]. rewrite H. rewrite art_bytes1 by lia. reflexivity. Qed.
Lemma cell_Wf_in : ltac2:(TCodec.tc2 tcn__JatFp "QG'QGyR0%211'6y8%511%311p051'<'4&Ozr4%3221&Q0&Nr5&Q2%116%4231&Q3+2+R0%3221%:251'9r3%A2@1%;1<%?231%5231%E2D?+X0%C2A1%9231&D&M&Br9r8r7r6%544321%L24Ku1%:593214p0<1p0A1p0H1p0Q41pRNQ:1pRHQ;1pS0Q;1pRDQ=1pLQ?1").
Proof. intros M a k b i Ha Hk Hi Hb. apply art_cell1_of_byte; [exact Hb|]. apply Wf_inside; assumption. Qed.
Lemma art_zb_mod64 : ltac2:(TCodec.tc2 tcn__JatFp "A'<':'QGyR0%211&QF&Q1r1&Q3+2+R0%3221%6251%82:1%92;7%>3;21pT0@1").
Proof.
intros z. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64). apply Z.mod_mod. lia.
Qed.
Lemma art_cell_norm : ltac2:(TCodec.tc2 tcn__JatFp "N'QGyR0%211'6y8%511%311p051'<'4&D&Mr4r3r2r1%6554321r5&Q1&Q3+2+R0%3221%5291%>5=7<;1p091pSJB1pS8B1pRDD1pLF1").
Proof. intros M a n v C. unfold cell in *. rewrite art_zb_mod64. exact C. Qed.
Lemma art_cell_mod_add : ltac2:(TCodec.tc2 tcn__JatFp "Q3'QGyR0%211'6y8%511%311p051'<'4&D&Mr5r4r3&N&Q1r2&Q3+2+R0%3221%6251r1%9221%?5>=<;1r6%<2=:%B5A2@?1p041pSNF1pSLG1pS8G1pRDI1pLK1").
Proof.
intros M a n x y C. unfold cell in *. replace (Z_to_bv 64 (x + y)) with (Z_to_bv 64 (x mod 2 ^ 64 + y)); [exact C|].
apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64). apply Zplus_mod_idemp_l.
Qed.
Lemma art_mod64_range : ltac2:(TCodec.tc2 tcn__JatFp "@'<'9&Oz&Q1r1&Q3+2+R0%3221%6251%9281&Q0%1234%=231pSJ?1").
Proof. intros v. apply Z.mod_pos_bound. lia. Qed.
Ltac zagree :=
lazymatch goal with
| |- art_agree _ ?M ?M => apply (art_agree_refl [])
| |- art_agree _ ?M (Wn ?n ?M1 ?a ?v) => eapply (art_agree_trans _ _ M M1 _); [ zagree | apply art_agree_Wn; [lia | cbn; lia] ]
| |- art_agree _ ?M (Wf ?M1 ?a ?k ?b) => eapply (art_agree_trans _ _ M M1 _); [ zagree | apply art_agree_Wf; [lia | rewrite ?Z2Nat.id by lia; lia] ]
| |- art_agree _ ?M (art_zfill ?M1 ?r ?len) => eapply (art_agree_trans _ _ M M1 _); [ zagree | apply art_agree_zfill ]
| |- art_agree _ ?M (art_unmap ?M1 ?r ?len) => eapply (art_agree_trans _ _ M M1 _); [ zagree | apply art_agree_unmap ]
| |- art_agree _ ?M (art_reveal ?M1 ?lo ?hi) => eapply (art_agree_trans _ _ M M1 _); [ zagree | apply art_agree_reveal ]
end.
Ltac zgrows :=
lazymatch goal with
| |- mem_grows ?M ?M => apply mem_grows_refl
| |- mem_grows ?M (Wn _ ?M1 _ _) => apply (mem_grows_trans M M1 _); [ zgrows | apply Wn_grows ]
| |- mem_grows ?M (Wf ?M1 _ _ _) => apply (mem_grows_trans M M1 _); [ zgrows | apply Wf_grows ]
| |- mem_grows ?M (art_zfill ?M1 _ _) => apply (mem_grows_trans M M1 _); [ zgrows | apply art_zfill_grows ]
| |- mem_grows ?M (art_reveal ?M1 _ _) => apply (mem_grows_trans M M1 _); [ zgrows | apply art_reveal_grows ]
end.
Ltac zsub := let z := fresh "z" in let Hz := fresh "Hz" in let H := fresh "H" in
intros z Hz H; cbn [art_out app fst snd] in H |- *; repeat split; lia.
Ltac zgap := cbn [art_gap fst snd app]; repeat split; first [ exact I | zapart | unfold apart; cbn; lia ].
Ltac ztr :=
lazymatch goal with
| |- cell _ ?M ?a ?n ?v =>
first [ match goal with H : cell _ M a n v |- _ => exact H end
| match goal with H : cell _ M ?a' n v |- _ => replace a with a' by lia; exact H end
| match goal with A : art_agree ?W ?M0 M |- _ => apply (art_cell_tr W M0 M a n v A); [ zgap | lia | cbn; lia | ztr ] end ]
end.
Lemma art_cell_tr1 : ltac2:(TCodec.tc2 tcn__JatFp "QD'3'8'<%2211%411'QGyR0%211'6y8%511%311p051'4&Hr6r5r4%43321'9&Ir7&Q2r3%211%53481&Oz%221;&Q0&N%12>7&Q3+2+R0%3221%7251%B291%C2=1&D&M%251DIHB%352EKJIp021p061p0K1pSJQ<1pS8Q21pRDQ>1pNQ51pLQ61pR<Q?1").
Proof. intros W M M' a n v A (G & Ha & Hn) C. eapply art_cell_tr; eassumption. Qed.
Ltac zapart_t :=
lazymatch goal with |- apart _ _ _ _ => idtac | _ => fail end;
first [ assumption
| apply apart_sym; assumption
| unfold apart at 1; lia
| match goal with H : apart _ _ _ _ |- _ => unfold apart at 1; unfold apart in H; destruct H; lia end ].
Ltac zarith_t := cbn [art_gap fst snd app]; repeat split; first [ exact I | zapart_t | lia | cbn; lia ].
Ltac zgap_c clr := clr; zarith_t.
Ltac zsub_c clr := let z := fresh "z" in let Hz := fresh "Hz" in let H := fresh "H" in
intros z; clr; intros Hz H; cbn [art_out app fst snd] in H |- *; repeat split; lia.
Ltac ztr_c clr :=
lazymatch goal with
| |- cell _ ?M ?a ?n ?v =>
first [ match goal with H : cell _ M a n v |- _ => exact H end
| match goal with A : art_agree ?W ?M0 M |- _ => apply (art_cell_tr1 W M0 M a n v A); [ clr; zarith_t | ztr_c clr ] end ]
end.
Ltac inl := cbn [In]; repeat first [left; reflexivity | right].
Lemma art_layout_fp : ltac2:(TCodec.tc2 tcn__JatFp "Q8'3'8'<%2211%411'QGyR0%211'6y8%511%311p051&Hr3r2r1%43321'9&O+RPP0%2215&Q0+RQbn8%2281%7241&Jr6%221=p041pT0L1&Lr4%211p011p051p0C1pNI1pLJ1pR<Q31").
Proof. intros W M M' A O L. apply (art_layout_agree3 M M'); [|exact L]. intros x Hx. apply A. apply O. exact Hx. Qed.
Lemma art_tsd_fp : ltac2:(TCodec.tc2 tcn__JatFp "R>'3'8'<%2211%411'QGyR0%211'6y8%511%311p051&Hr8r7r6%43321'9&O+RPP0r1%3221&Q0+VbTP0%2241%8241&Jr;r2%3221p051pT0N1&Nr5+TH%3221%B21@+U0%6251%A2C1%G241r<%@21>p031pT0Q;1+RPX0%L21Q1r9+8%A221%Q021K%Q12Q0Q6+QP0%E261%Q421O&Kr>r:%362AO1;Q=r=%5641CQ13=p031p081p0<1p0>1p0C1p0F1p0Q41p0QD1pSDR41pRJR51pSHR61pS2R71pSFR81pNQO1pLR01pR<R91").
Proof.
intros W M M' tp key tsd ctx t A OI OC Htp Htp' Htsd Htsd' T.
destruct T as (C1 & C2 & C3 & C4 & C5 & R). unfold art_tsd.
assert (TI : forall a (n : nat) v, 0x10000 <= a -> a + Z.of_nat n <= 0x691000 -> cellA M a n v -> cellA M' a n v).
{ intros a n v Ha Hn C. apply (art_cell_agree _ M M'); [|lia|lia|exact C]. intros x Hx. apply A. apply OI. lia. }
assert (Rk : 0 <= key < 128) by (destruct R as (_ & _ & R3 & _); exact R3).
split; [apply TI; [lia|cbn; lia|exact C1]|]. split; [apply TI; [lia|cbn; lia|exact C2]|].
split; [apply TI; [lia|cbn; lia|exact C3]|]. split; [apply TI; [lia|cbn; lia|exact C4]|].
split; [|exact R].
apply (art_cell_agree _ M M'); [|lia|cbn; lia|exact C5]. intros x Hx. apply A. apply OC. cbn in Hx. lia.
Qed.
