(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import PropExec CatSim StoreOk AsanAcct HeapIface HeapIfaceA ArtMem ArtRuns ArtRunsMem JbtCellEx JbtAllocG JbtInv.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import JbtFsInv.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLia. Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLiaT.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import SecKit. From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__JbtFsInvLaws () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Lists.ListDef."; "Corelib.Numbers.BinNums."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.ArtMem."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.HeapIface."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.HeapIfaceA."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.JbtFsInv."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.JbtFsInvLaws."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.JbtFsInvLaws.Facts."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.JbtInv."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.StoreOk."; "OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.AsanUbsan.M."; "Stdlib.Bool.Bool."; "Stdlib.Lists.List."; "Stdlib.ZArith.BinInt.Z."; "stdpp.base."; "stdpp.bitvector.definitions."; "stdpp.decidable."; "stdpp.list_basics.list."], [["1app"; "1list"; "1negb"; "1option"; "1pair"; "1prod"; "2and"; "2eq"; "2ex"; "2iff"; "2not"; "2or"; "3map"; "4Z"; "0F"; "0FF"]; ["0FF'"; "0FF2"; "0FX"; "0LK"; "0LK2"; "0M"; "0M'"; "5apart"; "5cell"; "6defined"; "7FS_BYTES"; "7ar_fs"; "7ff_addr"; "7ff_bytes"; "7ff_class"; "7ff_remove"]; ["7fframe"; "7in_fframe"; "8art_c_statics"; "8art_fs_geo"; "8art_fsg"; "8art_fsinv"; "8art_fsinv_client_law"; "8art_fsinv_frame_law_goal"; "8art_fsinv_release_law"; "8art_fsinv_wf_law"; "8cs_zone"; "8fs_flag"; "8fs_frame"; "8fs_nfr"; ":fs_rt_byte"; "9fs_slot_taken"]; ["9fs_zone3"; ";art_run"; ";rn_ar"; "<mem_grows"; "=loaded_segments"; ">Is_true"; "?In"; "?NoDup"; "?existsb"; "?incl"; "@add"; "@eqb"; "@le"; "@lt"; "@modulo"; "@mul"]; ["@pow"; "@sub"; "0a"; "0b"; "0c"; "0c'"; "0f"; "0f'"; "0fl"; "0fs"; "0g"; "0gfs"; "0h"; "0i"; "0i'"; "0k"]; ["0q"; "0rn"; "0rs"; "ANoDup"; "Afilter"; "Bbv"; "Bbv_unsigned"; "CIs_true_dec"; "Dlist_filter"; "0v"; "0w"; "0x"]]).
Local Ltac lia := L5FastLiaT.plia1.
Open Scope Z_scope.
#[local] Abbreviation cellA := (cell AsanUbsan.M.loaded_segments).
#[local] Abbreviation wrA := (wr AsanUbsan.M.loaded_segments).
#[local] Notation "'U' r" := (bv_unsigned r) (at level 10, r at level 9).
Lemma nodup_map_inj : forall (A B : Type) (g : A -> B) (l : list A) x y, List.NoDup (map g l) -> In x l -> In y l -> g x = g y -> x = y.
Proof.
induction l as [|a l IH]; intros x y ND Hx Hy E; [contradiction|].
cbn in ND. inversion ND as [|? ? Hn ND']; subst.
destruct Hx as [-> | Hx], Hy as [-> | Hy].
- reflexivity.
- exfalso. apply Hn. rewrite E. apply in_map. exact Hy.
- exfalso. apply Hn. rewrite <- E. apply in_map. exact Hx.
- apply IH; assumption.
Qed.
Lemma sfilter_In : forall (A : Type) (P : A -> Prop) (D : forall x, Decision (P x)) (l : list A) x, In x (filter P l) <-> P x /\ In x l.
Proof.
induction l as [|a l IH]; intros x; [cbn; tauto|]. rewrite list_basics.list.filter_cons. destruct (decide (P a)) as [Y | N]; cbn [In]; rewrite IH.
- split; [intros [<- | H]; tauto | intros (Hp & [-> | H]); tauto].
- split; [tauto | intros (Hp & [-> | H]); tauto].
Qed.
Lemma nodup_map_sfilter : forall (A B : Type) (g : A -> B) (P : A -> Prop) (D : forall x, Decision (P x)) (l : list A),
List.NoDup (map g l) -> List.NoDup (map g (filter P l)).
Proof.
induction l as [|a l IH]; intros ND; [exact ND|]. rewrite list_basics.list.filter_cons. cbn in ND. inversion ND as [|? ? Hn ND']; subst.
destruct (decide (P a)); [|apply IH; exact ND']. cbn. constructor; [|apply IH; exact ND'].
intros X. apply in_map_iff in X. destruct X as (y & E & Hy). apply sfilter_In in Hy. apply Hn. rewrite <- E. apply in_map. tauto.
Qed.
Lemma ff_remove_in : ltac2:(TCodec.tc2 tcn__JbtFsInvLaws "@'='1&Q0%211&QFr1&Or3r2%3221%63851%73934p021pT>;1pQ0;1pN?1").
Proof.
induction FF as [|a FF IH]; cbn; intros f H; [contradiction|].
destruct (ff_addr a =? F); [right; exact H|]. destruct H as [H | H]; [left; exact H | right; apply IH; exact H].
Qed.
Lemma ff_remove_keep : ltac2:(TCodec.tc2 tcn__JbtFsInvLaws "I'='1&Q0%211&QFr1r2%33521&:'7&L%115r4%43=21%611r3&Or5%2216%?3A41p061p0>1pT>D1pQ0D1pNH1").
Proof.
induction FF as [|a FF IH]; cbn; intros f H N; [contradiction|].
destruct (Z.eqb_spec (ff_addr a) F) as [E | E].
- destruct H as [-> | H]; [contradiction | exact H].
- destruct H as [H | H]; [left; exact H | right; apply IH; assumption].
Qed.
Lemma ff_remove_gone : ltac2:(TCodec.tc2 tcn__JbtFsInvLaws "K'='1&Q0%211'QG&<&Lr2%346821%5291&QF&Or4r3%3221%53=81&:'7%<15r5%33D21%511p071p0>1pT>F1pQ0F1pNJ1").
Proof.
induction FF as [|a FF IH]; cbn; intros f ND H; [contradiction|]. inversion ND as [|? ? Hn ND']; subst.
destruct (Z.eqb_spec (ff_addr a) F) as [E | E].
- intros X. apply Hn. rewrite E, <- X. apply in_map. exact H.
- destruct H as [<- | H]; [exact E | apply IH; assumption].
Qed.
Lemma ff_remove_nodup : ltac2:(TCodec.tc2 tcn__JbtFsInvLaws "C'='1&Q0%211'QG&<&Lr1%346821%5291&Or3r2%3221%94<>81%;2?1p071pQ0>1pNB1").
Proof.
induction FF as [|a FF IH]; cbn; intros ND; [exact ND|]. inversion ND as [|? ? Hn ND']; subst.
destruct (ff_addr a =? F); [exact ND'|]. cbn. constructor; [|apply IH; exact ND'].
intros X. apply Hn. apply in_map_iff in X. destruct X as (y & E & Hy). rewrite <- E. apply in_map. eapply ff_remove_in; exact Hy.
Qed.
Lemma ff_bytes_pos : ltac2:(TCodec.tc2 tcn__JbtFsInvLaws "<'=&QLzr1%3221&QM&Mr2%211%4271p061pT:;1").
Proof. intros c Hc. unfold ff_bytes. assert (0 < 2 ^ c) by (apply Z.pow_pos_nonneg; lia). lia. Qed.
Lemma ff_bytes_ge64 : ltac2:(TCodec.tc2 tcn__JbtFsInvLaws "<'=&QLzr1%3221+R0&Mr2%211%8241p061pT:;1").
Proof. intros c Hc. unfold ff_bytes. assert (0 < 2 ^ c) by (apply Z.pow_pos_nonneg; lia). lia. Qed.
Lemma fs_nfr_pos : ltac2:(TCodec.tc2 tcn__JbtFsInvLaws "='=&QLr1+>%3221&QMz&Q=r2%211%5241p071pT:<1").
Proof. intros c Hc. unfold fs_nfr. apply Z.pow_pos_nonneg; lia. Qed.
Lemma fs_nfr_bytes : ltac2:(TCodec.tc2 tcn__JbtFsInvLaws "H'='6&QLzr1%3221+>%5231%7231'7&QO&Q=r2%211&M%113%6231&R0+2+D%3221%<3E51p0>1pT:G1").
Proof.
intros c Hc. unfold fs_nfr, ff_bytes. replace (2 ^ (14 - c) * (64 * 2 ^ c)) with (64 * (2 ^ (14 - c) * 2 ^ c)) by ring.
rewrite <- Z.pow_add_r by lia. replace (14 - c + c) with 14 by lia. reflexivity.
Qed.
Lemma fs_frame_range : ltac2:(TCodec.tc2 tcn__JbtFsInvLaws "Q9'='6&QLzr2%3221+:%5231%7231&QM&Q=r3%211%4291%=291&QJr5+QTP0%3221&QOr4+QPPP0%3221%8251&Q<%1395>%H231&M%118%>241+1%@2;1%=21;%B2?1%Q0251%Q2291p0F1p0M1pTLQ61pT:Q71pTDQ81").
Proof.
intros fs c i Hc Hi. unfold fs_frame. pose proof (fs_nfr_bytes c ltac:(lia)) as NB. pose proof (ff_bytes_pos c ltac:(lia)) as BP.
change (2 ^ 20) with 1048576 in *.
assert (P : 0 <= i * ff_bytes c) by (apply Z.mul_nonneg_nonneg; lia).
assert (Q : (i + 1) * ff_bytes c <= fs_nfr c * ff_bytes c) by (apply Z.mul_le_mono_nonneg_r; lia).
lia.
Qed.
Lemma fs_frames_apart_or_eq : ltac2:(TCodec.tc2 tcn__JbtFsInvLaws "QB'='6&QLzr4%3221+:%5231%7231r3%8271%9225%;221r5%<2;1&QM&Q=r6%211%4261%C261%518%72B1%F2B1';'7r8%23K1:r7%43M1@%M231&G&Q<r9%23186&M%11:%534DH%31E%845321%@2:1p0B1p0F1p0O1p0Q41pTNQ=1pT<Q>1pTLQ?1pT:Q@1pTDQA1").
Proof.
intros fs c i c' i' Hc Hc' Hi Hi'. pose proof (fs_frame_range fs c i Hc Hi) as R. pose proof (fs_frame_range fs c' i' Hc' Hi') as R'.
unfold apart. destruct (Z.lt_trichotomy c c') as [L | [E | L]]; [right; lia | | right; lia]. subst c'.
destruct (Z.lt_trichotomy i i') as [L | [E | L]]; [right | left; lia | right]; unfold fs_frame; pose proof (ff_bytes_pos c ltac:(lia)) as BP.
- assert (Q : (i + 1) * ff_bytes c <= i' * ff_bytes c) by (apply Z.mul_le_mono_nonneg_r; lia). lia.
- assert (Q : (i' + 1) * ff_bytes c <= i * ff_bytes c) by (apply Z.mul_le_mono_nonneg_r; lia). lia.
Qed.
Lemma fs_flag_range : ltac2:(TCodec.tc2 tcn__JbtFsInvLaws "Q5'='6&QLzr2%3221+:%5231%7231&QM&Q=r3%211%4291%=291&R1&QJr5+QTP0%3221&QO+2r4%=11%4231%:261&Q;%13:5@%J231%>2:6%E231%N231p0B1p0I1pTLQ21pT:Q31pTDQ41").
Proof. intros fs c i Hc Hi. unfold fs_flag. lia. Qed.
Lemma fs_nfr_double : ltac2:(TCodec.tc2 tcn__JbtFsInvLaws "I'='6&QLzr2%3221&QMr1%2241%8241+>%9271&QO+2&Q=r3%211%5241r4%511%B231p0:1p0=1pT<G1pT:H1").
Proof.
intros c c' H H'. unfold fs_nfr. replace (2 * 2 ^ (14 - c')) with (2 ^ (14 - c' + 1)) by (rewrite Z.pow_add_r by lia; lia).
apply Z.pow_le_mono_r; lia.
Qed.
Lemma fs_flag_inj : ltac2:(TCodec.tc2 tcn__JbtFsInvLaws "Q='='6&QLzr4%3221+:%5231%7231r3%8271%9225%;221r5%<2;1&QM&Q=r6%211%4261%C261%518%72B1%F2B1'7&Q;r9r8r7%43321%534=A%73O21%83Q064%93Q16@%Q1221p041p0=1p0A1p0J1p0O1pTNQ81pT<Q91pTLQ:1pT:Q;1pTDQ<1").
Proof.
intros fs c i c' i' Hc Hc' Hi Hi' E. pose proof (fs_flag_range fs c i Hc Hi) as R. pose proof (fs_flag_range fs c' i' Hc' Hi') as R'.
destruct (Z.lt_trichotomy c c') as [L | [E' | L]].
- pose proof (fs_nfr_double c c' ltac:(lia) ltac:(lia)). lia.
- subst c'. unfold fs_flag in E. lia.
- pose proof (fs_nfr_double c' c ltac:(lia) ltac:(lia)). lia.
Qed.
Section Facts.
Variables (rn : art_run) (g : art_fsg) (FF LK : list fframe) (M : word -> option byte).
Hypothesis I : art_fsinv rn g FF LK M.
Let fs := ar_fs (rn_ar rn).
#[using="g FF LK M I"] Lemma fsinv_geo : ltac2:(TCodec.tc2 tcn__JbtFsInvLaws "3&Q3vRA%211").
Proof. exact (proj1 I). Qed.
#[using="rn g M I"] Lemma fsinv_nodup : ltac2:(TCodec.tc2 tcn__JbtFsInvLaws ";'QG'=&<&Q0&L&0v?vC%33521%746851%:291").
Proof. destruct I as (_ & _ & _ & _ & _ & _ & _ & ND & _). exact ND. Qed.
#[using="g M I"] Lemma fsinv_slot : ltac2:(TCodec.tc2 tcn__JbtFsInvLaws "Q9&Q0&QFr1&0v?vC%33621%63751'6&QLz&Nr2%211%5241+4%7231%9231'8'=%;2:B&QM&Q=r3%=11%311%52H1%C271'7&L%117&Q<vR9%2319O%63?41%K281qTLA1%C2B1%N2E1p0Q01pT>Q81").
Proof.
intros f Hf. destruct I as (_ & _ & _ & _ & _ & _ & _ & _ & FR & _). destruct (FR f Hf) as (K & (i & (Hi & A) & _) & _).
split; [exact K|]. exists i. split; assumption.
Qed.
#[using="g M I"] Lemma fsinv_frame_in : ltac2:(TCodec.tc2 tcn__JbtFsInvLaws "Q1&Q0&QFr1&0v?vC%33621%63751'6&QL&QJvR9+QTP0%3221&Lr2%211%8241&M&N%115%311%<261&J%>2=1%@231&QMz%2217%E241%F2=1p0H1pT>Q01").
Proof.
intros f Hf. destruct (fsinv_slot f Hf) as (K & i & Hi & A). pose proof (fs_frame_range fs (ff_class f) i ltac:(lia) Hi) as R.
pose proof (ff_bytes_pos (ff_class f) ltac:(lia)). unfold FS_BYTES. rewrite A. lia.
Qed.
#[using="rn g M I fs"] Lemma fsinv_frames_apart : ltac2:(TCodec.tc2 tcn__JbtFsInvLaws "M&Q0&QFr2&0v?vC%33621%63751';'7r4r3%33<21&G&L%115&M&N%118%311%619%41:%611%:48431%@2<1p0B1p0C1pT@K1pT>L1").
Proof.
intros f f' Hf Hf'. destruct (fsinv_slot f Hf) as (K & i & Hi & A). destruct (fsinv_slot f' Hf') as (K' & i' & Hi' & A').
destruct (fs_frames_apart_or_eq fs (ff_class f) i (ff_class f') i' ltac:(lia) ltac:(lia) Hi Hi') as [(E1 & E2) | AP].
- left. apply (nodup_map_inj _ _ ff_addr (FF ++ LK)); [exact fsinv_nodup | exact Hf | exact Hf' |]. rewrite A, A', E1, E2. reflexivity.
- right. rewrite A, A'. exact AP.
Qed.
Definition fs_rt_byte (a : Z) : Prop :=
a < fs + 36864 \/ fs + FS_BYTES <= a
\/ exists f, In f (FF ++ LK) /\ (ff_addr f + 24 <= a < ff_addr f + 32 \/ ff_addr f + ff_bytes (ff_class f) - 8 <= a < ff_addr f + ff_bytes (ff_class f)).
#[using="g M I"] Lemma fsinv_rt_not_client : ltac2:(TCodec.tc2 tcn__JbtFsInvLaws "<'=&Q>r1%211&:&Q1v?r2%3221%511p071pT6;1").
Proof.
intros a H (f' & Hf' & R' & N').
assert (Hf'' : In f' (FF ++ LK)) by (apply in_or_app; left; exact Hf'). pose proof (fsinv_frame_in f' Hf'') as IN'.
destruct H as [H | [H | (f & Hf & H)]]; [lia | lia |].
destruct (fsinv_frames_apart f f' Hf Hf'') as [-> | AP]; [lia|]. unfold apart in AP. pose proof (fsinv_frame_in f Hf) as IN.
pose proof (ff_bytes_ge64 (ff_class f) ltac:(destruct (fsinv_slot f Hf); lia)). lia.
Qed.
End Facts.
Theorem art_fsinv_in_proved : ltac2:(TCodec.tc2 tcn__JbtFsInvLaws "QH'QA'Q4'1&Q0%211'REyR0%211'3y8%511%311p051&Q5r5r4r3r2r1%6554321&QF&0%13C87%33D51'6&QL&K&QBr8%211%411&L%11?%8231&QJ&M&N%11D%311%5271&J%72;1%A231&QMz%2217%F241%G2>1p0I1pT>Q>1p0O1pQ<Q71pQ8Q@1pQ0QA1pTHQE1pU4QG1").
Proof. intros rn gfs FF LK M I f Hf. pose proof (fsinv_frame_in rn gfs FF LK M I f Hf). lia. Qed.
Definition fs_zone3 (rn : art_run) (a : Z) : Prop :=
ar_fs (rn_ar rn) <= a < ar_fs (rn_ar rn) + FS_BYTES \/ rn_t rn + 72 <= a < rn_t rn + 80 \/ rn_tp rn <= a < rn_tp rn + 8.
Definition fs_slot_taken (fs : Z) (L : list fframe) (c i : Z) : Prop := exists f, In f L /\ ff_class f = c /\ ff_addr f = fs_frame fs c i.
Section SE.
Local Abbreviation SEC_T_fsinv_cs := (ltac2:(TCodec.tc2 tcn__JbtFsInvLaws "M'QA'Q4'1&Q0%211'REyR0%211'3y8%511%311p051&Q5r5r4r3r2r1%6554321&Q2r6%2215p041pQ<<1pQ8E1pQ0F1pTFJ1pU4L1")) (only parsing).
Variable rn : ltac:(sec_ty2 constr:(SEC_T_fsinv_cs) 0%nat 0%nat).
Variable g : ltac:(sec_ty2 constr:(SEC_T_fsinv_cs) 1%nat 0%nat).
Variable FF : ltac:(sec_ty2 constr:(SEC_T_fsinv_cs) 2%nat 0%nat).
Variable LK : ltac:(sec_ty2 constr:(SEC_T_fsinv_cs) 3%nat 0%nat).
Variable M : ltac:(sec_ty2 constr:(SEC_T_fsinv_cs) 4%nat 0%nat).
Lemma fsinv_cs : ltac:(sec_stmt2 constr:(SEC_T_fsinv_cs) 5%nat 0%nat).
Proof.
intros (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & CS).
exact CS. Qed.
End SE.
Section SE.
Local Abbreviation SEC_T_art_c_statics_keep := (ltac2:(TCodec.tc2 tcn__JbtFsInvLaws "Q8'QA'REyR0%211'3y8%511%311p051&Q3r3%211&Q2r4%2214&QC%1236&Q:r7&RFr1%22C1%5241'7r6r2%211%912%53E21p071pUHK1r5%D2>1p031p0B1p0E1p0I1pQ>M1pQ<N1pU4Q71")) (only parsing).
Variable rn : ltac:(sec_ty2 constr:(SEC_T_art_c_statics_keep) 0%nat 0%nat).
Variable M : ltac:(sec_ty2 constr:(SEC_T_art_c_statics_keep) 1%nat 0%nat).
Variable M' : ltac:(sec_ty2 constr:(SEC_T_art_c_statics_keep) 2%nat 0%nat).
Lemma art_c_statics_keep : ltac:(sec_stmt2 constr:(SEC_T_art_c_statics_keep) 3%nat 0%nat).
Proof.
intros GEO ((Q1 & Q2 & Q3) & C1 & C2 & C3 & C4 & C5 & SH & GL & SD) GR AG.
pose proof GEO as (_ & _ & _ & _ & _ & _ & _ & _ & G11 & G12).
assert (KEEP : forall a (n : nat) v, 0 <= a -> a + Z.of_nat n < 2 ^ 64 -> (forall z, a <= z < a + Z.of_nat n -> cs_zone rn z) -> cellA M a n v -> cellA M' a n v).
{ intros a n v Ha Hn Hz C. apply (cell_agree M M'); [|exact Ha|exact Hn|exact C]. intros x Hx. apply AG. apply Hz. exact Hx. }
assert (ES1 : HeapIfaceA.S 0x10000 = 2147459072) by reflexivity. assert (ES2 : HeapIfaceA.S 0x693000 = 2148312576) by reflexivity.
assert (ES3 : HeapIfaceA.S 0x23160 = 2147468844) by reflexivity. assert (ES4 : HeapIfaceA.S 0x23940 = 2147469096) by reflexivity.
assert (ES5 : HeapIfaceA.S 0x138ea0 = 2147611092) by reflexivity. assert (ES6 : HeapIfaceA.S 0x139360 = 2147611244) by reflexivity.
assert (ES7 : HeapIfaceA.S 0x23180 = 2147468848) by reflexivity. assert (ES8 : HeapIfaceA.S 0x231c0 = 2147468856) by reflexivity.
assert (ES9 : HeapIfaceA.S 0x23240 = 2147468872) by reflexivity. assert (ES10 : HeapIfaceA.S 0x233a0 = 2147468916) by reflexivity.
assert (BYTE : forall x v, 2147459072 <= x < 2148312576 -> byte_at M x v -> byte_at M' x v).
{ intros x v Hx B. unfold byte_at in *. rewrite (AG (Z_to_bv 64 x)); [exact B|].
rewrite art_u_lit by lia. unfold cs_zone. rewrite ES1, ES2. do 4 right. exact Hx. }
split; [repeat split; assumption|].
split. { refine (KEEP _ _ _ _ _ _ C1); [lia | cbn; lia |]. intros z Hz. cbn in Hz. unfold cs_zone. lia. }
split. { refine (KEEP _ _ _ _ _ _ C2); [lia | cbn; lia |]. intros z Hz. cbn in Hz. unfold cs_zone. lia. }
split. { refine (KEEP _ _ _ _ _ _ C3); [lia | cbn; lia |]. intros z Hz. cbn in Hz. unfold cs_zone. lia. }
split. { refine (KEEP _ _ _ _ _ _ C4); [lia | cbn; lia |]. intros z Hz. cbn in Hz. unfold cs_zone. lia. }
split. { refine (KEEP _ _ _ _ _ _ C5); [lia | cbn; lia |]. intros z Hz. cbn in Hz. unfold cs_zone. lia. }
split. { intros x Hx. apply BYTE; [|exact (SH x Hx)]. rewrite ES1, ES2, ES3, ES4, ES5, ES6, ES7, ES8, ES9, ES10 in Hx. lia. }
split. { unfold ART_GLOBALS in *. rewrite !Forall_cons_iff in *. cbn [fst snd] in *.
assert (SB1 : forall u n, 0x10000 <= u -> u + n <= 0x139360 -> 0 < n -> shadow_blk M u n -> shadow_blk M' u n).
{ intros u n Hu Hn Hp (Z0 & PT).
assert (D1 : 8192 <= u / 8) by (change 8192 with (0x10000 / 8); apply Z.div_le_mono; lia).
assert (D2 : (u + n) / 8 <= 160364) by (change 160364 with (0x139360 / 8); apply Z.div_le_mono; lia).
assert (D3 : u / 8 + n / 8 <= (u + n) / 8).
{ pose proof (Z.div_mod u 8 ltac:(lia)) as Du. pose proof (Z.mod_pos_bound u 8 ltac:(lia)). pose proof (Z.div_mod n 8 ltac:(lia)) as Dn. pose proof (Z.mod_pos_bound n 8 ltac:(lia)).
apply Z.div_le_lower_bound; lia. }
split.
- intros j Hj. apply BYTE; [|exact (Z0 j Hj)]. unfold HeapIfaceA.S, HeapIfaceA.SB. lia.
- intros NZ. apply BYTE; [|exact (PT NZ)]. unfold HeapIfaceA.S, HeapIfaceA.SB. lia. }
destruct GL as (g1 & g2 & g3 & g4 & g5 & g6 & g7 & g8 & g9 & g10 & g11 & g12 & g13 & g14 & g15 & g16 & g17 & g18 & g19 & _).
repeat split; first [apply SB1; [lia | lia | lia | assumption] | apply Forall_nil]. }
intros a Ha. apply GR. exact (SD a Ha).
Qed.
End SE.
Section SE.
Local Abbreviation SEC_T_art_fsinv_core := (ltac2:(TCodec.tc2 tcn__JbtFsInvLaws "TM'QA'Q4'1&Q0%211'REyR0%211'3y8%511%311p051'=&Q5r8r7r6r5r4%6554321&QC%1243';'6&QL&QJ&K&QBr:%211%411+TP0%7221r3%:221&QM+QTP0%<271%3251%@251z%6281%D231&Q@r<&RFr1%22Q:1%5241&:&Q1r;r2%82Q@1%4231%611'7%<2QDH%23Q>1Q;%:11%Q01Q:%:1Q;%63QD21p041p091p0A1pUHQL1&Q:r=%221Fr9%11C%Q<1D%A3QO21p051pUHR51&QI%13R;QNJ'QG&<&L&0%13R@R4O%44RAR731%62R81%QM2Q=Q1+:%QO2Q31%R1231&Q=%11QI%QH2Q71%R5271&Q;rC%R411%R611%431R?R0%Q:3RF1QF%QB11&9&Q?rD%R<11%R>11r>rA%J3S921%7441RKRJrB%M3S<14%:471RNRM%<241p0>1p0F1p0K1pTLS81pT:S91%I3>S4RE%QO3S;1QC&H&QDr@u1%4532C1RDrE%S311%S511r?%Q@3SO1D%M431SAS@%RB11%S=281p0>1p0Q:1p0Q?1pTLSL1pT:SM1%SM5Q0@RGQ1RNp021p0G1p0QI1p0R11p0R41p0R>1p0S71p0SM1p0T01pTBT81pQ2TB1pQ>T;1pQ<T<1pQ8TE1pQ0TF1pTFTJ1pU4TL1")) (only parsing).
Variable rn : ltac:(sec_ty2 constr:(SEC_T_art_fsinv_core) 0%nat 0%nat).
Variable g : ltac:(sec_ty2 constr:(SEC_T_art_fsinv_core) 1%nat 0%nat).
Variable FF : ltac:(sec_ty2 constr:(SEC_T_art_fsinv_core) 2%nat 0%nat).
Variable LK : ltac:(sec_ty2 constr:(SEC_T_art_fsinv_core) 3%nat 0%nat).
Variable M : ltac:(sec_ty2 constr:(SEC_T_art_fsinv_core) 4%nat 0%nat).
Variable M' : ltac:(sec_ty2 constr:(SEC_T_art_fsinv_core) 5%nat 0%nat).
Variable FF' : ltac:(sec_ty2 constr:(SEC_T_art_fsinv_core) 6%nat 0%nat).
Variable fl : ltac:(sec_ty2 constr:(SEC_T_art_fsinv_core) 7%nat 0%nat).
Lemma art_fsinv_core : ltac:(sec_stmt2 constr:(SEC_T_art_fsinv_core) 8%nat 0%nat).
Proof.
intros I GR Hfl AG AGCS INC ND' TK0 TK1.
pose proof (art_c_statics_keep rn M M' (fsinv_geo _ _ _ _ _ I) (fsinv_cs _ _ _ _ _ I) GR AGCS) as CS'.
pose proof (fsinv_geo _ _ _ _ _ I) as GEO. pose proof (fsinv_rt_not_client _ _ _ _ _ I) as NC. pose proof (fsinv_frame_in _ _ _ _ _ I) as FIN.
unfold fs_rt_byte in NC.
destruct I as (_ & W & CTP & CT & C88 & C96 & HINT & ND & FR & FL & _). cbn zeta in *.
pose proof GEO as (G1 & G2 & G3 & G4 & (G5 & G6 & G7) & G8 & G9 & G10 & G11 & G12). unfold FS_BYTES in *.
set (fs := ar_fs (rn_ar rn)) in *.
assert (INC' : forall f, In f (FF' ++ LK) -> In f (FF ++ LK)).
{ intros f Hf. apply in_app_or in Hf. apply in_or_app. destruct Hf as [Hf | Hf]; [left; apply INC; exact Hf | right; exact Hf]. }
assert (KEEP : forall a (n : nat) v, 0 <= a -> a + Z.of_nat n < 2 ^ 64 ->
(forall b, a <= b < a + Z.of_nat n -> fs_zone3 rn b /\ b <> fl
/\ (b < fs + 36864 \/ fs + 11571200 <= b
\/ exists f, In f (FF ++ LK) /\ (ff_addr f + 24 <= b < ff_addr f + 32 \/ ff_addr f + ff_bytes (ff_class f) - 8 <= b < ff_addr f + ff_bytes (ff_class f)))) ->
cellA M a n v -> cellA M' a n v).
{ intros a n v Ha Hn Hb C. apply (cell_agree M M'); [|exact Ha|exact Hn|exact C].
intros x Hx. destruct (Hb (U x) Hx) as (Z3 & NF & RT). apply AG; [exact Z3 | apply NC; exact RT | exact NF]. }
unfold art_fsinv. cbn zeta. fold fs. unfold FS_BYTES.
split; [exact GEO|]. split; [eapply wr_grows; [exact GR | exact W]|].
split. { refine (KEEP _ _ _ _ _ _ CTP); [lia | cbn; lia |]. intros b Hb. cbn in Hb. unfold fs_zone3, FS_BYTES. fold fs. lia. }
split. { refine (KEEP _ _ _ _ _ _ CT); [lia | cbn; lia |]. intros b Hb. cbn in Hb. unfold fs_zone3, FS_BYTES. fold fs. lia. }
split. { refine (KEEP _ _ _ _ _ _ C88); [lia | cbn; lia |]. intros b Hb. cbn in Hb. unfold fs_zone3, FS_BYTES. fold fs. lia. }
split. { refine (KEEP _ _ _ _ _ _ C96); [lia | cbn; lia |]. intros b Hb. cbn in Hb. unfold fs_zone3, FS_BYTES. fold fs. lia. }
split. { intros c Hc. destruct (HINT c Hc) as (C & R). split; [|exact R].
refine (KEEP _ _ _ _ _ _ C); [lia | cbn; lia |]. intros b Hb. cbn in Hb. unfold fs_zone3, FS_BYTES. fold fs. lia. }
split; [exact ND'|].
split.
{ intros f Hf. pose proof (INC' f Hf) as Hf0. destruct (FR f Hf0) as (K & (i & SL & CS) & CR & RS). pose proof (FIN f Hf0) as (IN1 & IN2 & IN3).
pose proof (ff_bytes_ge64 (ff_class f) ltac:(lia)) as B64.
split; [exact K|]. split; [|split; [|exact RS]].
- exists i. split; [exact SL|]. refine (KEEP _ _ _ _ _ _ CS); [lia | cbn; lia |].
intros b Hb. cbn in Hb. unfold fs_zone3, FS_BYTES. fold fs. split; [lia|]. split; [lia|]. right; right. exists f. split; [exact Hf0 | lia].
- refine (KEEP _ _ _ _ _ _ CR); [lia | cbn; lia |].
intros b Hb. cbn in Hb. unfold fs_zone3, FS_BYTES. fold fs. split; [lia|]. split; [lia|]. right; right. exists f. split; [exact Hf0 | lia]. }
split; [|exact CS'].
intros c i Hc Hi. pose proof (fs_flag_below_frames fs c i Hc Hi) as FB. destruct (Z.eq_dec (fs_flag fs c i) fl) as [E | NE].
- destruct (TK1 c i Hc Hi E) as (C0 & NT). exists 0. rewrite E. split; [exact C0|]. split; [left; reflexivity|].
split; [intros X; discriminate X | intros X; exfalso; apply NT; exact X].
- destruct (FL c i Hc Hi) as (b & C & B01 & IFF). exists b. split; [|split; [exact B01|]].
+ refine (KEEP _ _ _ _ _ _ C); [lia | cbn; lia |]. intros b' Hb. cbn in Hb. unfold fs_zone3, FS_BYTES. fold fs. lia.
+ rewrite IFF. symmetry. apply (TK0 c i Hc Hi NE).
Qed.
End SE.
Theorem art_fsinv_client_proved : ltac2:(TCodec.tc2 tcn__JbtFsInvLaws "1&Q6").
Proof.
intros rn g FF LK M M' I GR AG AGCS.
apply (art_fsinv_core rn g FF LK M M' FF (-1) I GR); [right; lia | | exact AGCS | apply incl_refl | exact (fsinv_nodup _ _ _ _ _ I) | tauto |].
- intros x Z3 NF _. apply AG; [exact Z3 | exact NF].
- intros c i Hc Hi E. exfalso. pose proof (fs_flag_below_frames (ar_fs (rn_ar rn)) c i Hc Hi). destruct (fsinv_geo _ _ _ _ _ I) as (_ & G2 & _). lia.
Qed.
Theorem art_fsinv_frame_law_proved : ltac2:(TCodec.tc2 tcn__JbtFsInvLaws "1&Q7").
Proof.
intros rn g FF LK M M' I GR AG. apply (art_fsinv_client_proved rn g FF LK M M' I GR).
2:{ intros x Z. apply AG. unfold art_fs_zone. destruct (fsinv_geo _ _ _ _ _ I) as (_ & _ & _ & _ & _ & _ & _ & _ & G11 & G12).
destruct (fsinv_cs _ _ _ _ _ I) as ((Q1 & Q2 & Q3) & _).
destruct Z as [Z | [Z | [Z | [Z | Z]]]].
- right; right; right; left. unfold art_zone_statics. lia.
- right; right; right; left. unfold art_zone_statics. lia.
- right; right; right; left. unfold art_zone_statics. lia.
- do 5 right. lia.
- do 4 right. left. exact Z. }
intros x a Z3 _. apply AG. unfold art_fs_zone. subst a.
destruct (fsinv_geo _ _ _ _ _ I) as (_ & _ & _ & _ & _ & _ & _ & _ & G11 & G12).
destruct Z3 as [Z | [Z | Z]]; [left; exact Z | right; left; exact Z |].
right; right; right. left. unfold art_zone_statics. lia.
Qed.
Theorem art_fsinv_release_proved : ltac2:(TCodec.tc2 tcn__JbtFsInvLaws "1&Q8").
Proof.
intros rn g FF LK M M' F k rs I HF GR (i & Hi & EF & C0 & AG) AGCS.
set (fs := ar_fs (rn_ar rn)) in *.
assert (HF' : In (F, k, rs) (FF ++ LK)) by (apply in_or_app; left; exact HF).
destruct (fsinv_slot _ _ _ _ _ I _ HF') as (K & _). unfold ff_class in K. cbn [fst snd] in K.
pose proof (fsinv_nodup _ _ _ _ _ I) as ND. pose proof ND as ND2. rewrite map_app in ND2.
pose proof (fs_flag_below_frames fs k i ltac:(lia) Hi) as FB.
assert (NDF : List.NoDup (map ff_addr FF)) by (eapply NoDup_app_remove_r; exact ND2).
apply (art_fsinv_core rn g FF LK M M' (ff_remove F FF) (fs_flag fs k i) I GR); fold fs.
- left. lia.
- intros x Z3 NF NE. apply AG; [exact NE | exact Z3 | exact NF].
- exact AGCS.
- intros f Hf. eapply ff_remove_in; exact Hf.
- rewrite map_app. apply NoDup_app_remove_l in ND2 as NDL.
assert (X : forall a, In a (map ff_addr (ff_remove F FF)) -> ~ In a (map ff_addr LK)).
{ intros a Ha Hb. apply in_map_iff in Ha. destruct Ha as (f & <- & Hf). apply ff_remove_in in Hf.
apply in_map_iff in Hb. destruct Hb as (h & E & Hh).
assert (f = h) by (apply (nodup_map_inj _ _ ff_addr (FF ++ LK)); [exact ND | apply in_or_app; left; exact Hf | apply in_or_app; right; exact Hh | symmetry; exact E]).
subst h. clear - ND2 Hf Hh. induction FF as [|a l IH]; [contradiction|]. cbn in ND2. inversion ND2 as [|? ? Hn ND']; subst.
destruct Hf as [-> | Hf]; [apply Hn; apply in_or_app; right; apply in_map; exact Hh | apply IH; assumption]. }
clear - X NDL NDF. pose proof (ff_remove_nodup F FF NDF) as N1. revert N1 X. generalize (map ff_addr (ff_remove F FF)) as l1.
induction l1 as [|a l1 IH]; intros N1 X; [exact NDL|]. cbn. inversion N1 as [|? ? Hn N1']; subst. constructor.
+ intros Y. apply in_app_or in Y. destruct Y as [Y | Y]; [exact (Hn Y) | exact (X a (or_introl eq_refl) Y)].
+ apply IH; [exact N1' | intros b Hb; apply X; right; exact Hb].
-
intros c j Hc Hj NE. unfold fs_slot_taken. split; intros (f & Hf & Ec & Ea); exists f; (split; [|split; assumption]).
+ apply in_app_or in Hf. apply in_or_app. destruct Hf as [Hf | Hf]; [left; eapply ff_remove_in; exact Hf | right; exact Hf].
+ apply in_app_or in Hf. apply in_or_app. destruct Hf as [Hf | Hf]; [left | right; exact Hf].
apply ff_remove_keep; [exact Hf|]. intros X. rewrite Ea, EF in X.
destruct (fs_frames_apart_or_eq fs c j k i Hc ltac:(lia) Hj Hi) as [(E1 & E2) | AP]; [subst; apply NE; reflexivity|].
unfold apart in AP. pose proof (ff_bytes_pos c ltac:(lia)). pose proof (ff_bytes_pos k ltac:(lia)). lia.
-
intros c j Hc Hj E. destruct (fs_flag_inj fs c j k i Hc ltac:(lia) Hj Hi E) as (-> & ->). split; [exact C0|].
intros (f & Hf & Ec & Ea). rewrite <- EF in Ea. apply in_app_or in Hf. destruct Hf as [Hf | Hf].
+ exact (ff_remove_gone F FF f NDF Hf Ea).
+ assert (f = (F, k, rs)) by (apply (nodup_map_inj _ _ ff_addr (FF ++ LK)); [exact ND | apply in_or_app; right; exact Hf | exact HF' | exact Ea]).
subst f. clear - ND2 HF Hf. induction FF as [|a l IH]; [contradiction|]. cbn in ND2. inversion ND2 as [|? ? Hn ND']; subst.
destruct HF as [-> | HF]; [apply Hn; apply in_or_app; right; apply (in_map ff_addr) in Hf; exact Hf | apply IH; assumption].
Qed.
Lemma art_fsinv_relist : ltac2:(TCodec.tc2 tcn__JbtFsInvLaws "Q@'QA'Q4'1&Q0%211'REyR0%211'3y8%511%311p051&Q5r7r6r5r4r1%6554321&9&QF&0%13D76%33E61%33F;:%53G81%7231pT>I1'QG'=&<&L%24N31:%5241r:r9%H521FEDp041p0;1p0E1pQ<M1pQ:Q61pQ4Q71pQ8Q81pQ0Q91pTFQ=1pU4Q?1").
Proof.
intros rn g FF LK FF2 LK2 M I EQ ND2. destruct I as (GEO & W & CTP & CT & C88 & C96 & HINT & ND & FR & FL & CS). cbn zeta in *.
unfold art_fsinv. cbn zeta.
split; [exact GEO|]. split; [exact W|]. split; [exact CTP|]. split; [exact CT|]. split; [exact C88|]. split; [exact C96|]. split; [exact HINT|].
split; [exact ND2|]. split; [intros f Hf; apply FR; apply EQ; exact Hf|]. split; [|exact CS].
intros c i Hc Hi. destruct (FL c i Hc Hi) as (b & C & B01 & IFF). exists b. split; [exact C|]. split; [exact B01|]. rewrite IFF.
split; intros (f & Hf & X); exists f; (split; [apply EQ; exact Hf | exact X]).
Qed.
Section SE.
Local Abbreviation SEC_T_art_fsinv_leak_proved := (ltac2:(TCodec.tc2 tcn__JbtFsInvLaws "QO'QA'Q4'1&Q0%211'REyR0%211'3y8%511%311p051&Q5r6r5r4r3r2%6554321&QI%13B36'QG'=&<&L%24G319%5241r9r8&RD&RH%11M&QE&2&QH&QKr1%=11%>1E%4221qTJQ61%73Q71K%911%;11qT>Q:1&RG%114qUHQ=1r7%D6Q?Q>B521&0%13QAQ4Q6%Q85IH31Q6p0K1p0Q21p0Q51pQ6QE1pQ<Q>1pQ8QG1pQ0QH1pTFQL1pU4QN1")) (only parsing).
Variable rn : ltac:(sec_ty2 constr:(SEC_T_art_fsinv_leak_proved) 0%nat 0%nat).
Variable g : ltac:(sec_ty2 constr:(SEC_T_art_fsinv_leak_proved) 1%nat 0%nat).
Theorem art_fsinv_leak_proved : ltac:(sec_stmt2 constr:(SEC_T_art_fsinv_leak_proved) 2%nat 0%nat).
Proof.
intros FF LK M FX I INC NDX.
pose proof (fsinv_nodup _ _ _ _ _ I) as ND.
set (P := fun f : fframe => Is_true (negb (existsb (fun h => Z.eqb (ff_addr h) (ff_addr f)) FX))).
assert (PX : forall f, P f <-> ~ In (ff_addr f) (map ff_addr FX)).
{ intros f. unfold P. rewrite Is_true_true, negb_true_iff. rewrite <- not_true_iff_false, existsb_exists. split; intros N X; apply N.
- apply in_map_iff in X. destruct X as (h & E & Hh). exists h. split; [exact Hh | apply Z.eqb_eq; exact E].
- destruct X as (h & Hh & E). apply Z.eqb_eq in E. rewrite <- E. apply in_map. exact Hh. }
assert (DISJ : forall f h, In f FF -> In h LK -> ff_addr f <> ff_addr h).
{ intros f h Hf Hh E. assert (f = h) by (apply (nodup_map_inj _ _ ff_addr (FF ++ LK)); [exact ND | apply in_or_app; left; exact Hf | apply in_or_app; right; exact Hh | exact E]).
subst h. rewrite map_app in ND. clear - ND Hf Hh. induction FF as [|a l IH]; [contradiction|]. cbn in ND. inversion ND as [|? ? Hn ND']; subst.
destruct Hf as [-> | Hf]; [apply Hn; apply in_or_app; right; apply in_map; exact Hh | apply IH; assumption]. }
apply (art_fsinv_relist rn g FF LK _ _ M I).
- intros f. rewrite !in_app_iff, sfilter_In. fold P. rewrite PX. split.
+ intros [(_ & H) | [H | H]]; [left; exact H | left; apply INC; exact H | right; exact H].
+ intros [H | H]; [|right; right; exact H].
destruct (in_dec Z.eq_dec (ff_addr f) (map ff_addr FX)) as [Y | N]; [|left; split; assumption].
right; left. apply in_map_iff in Y. destruct Y as (h & E & Hh).
assert (h = f) by (apply (nodup_map_inj _ _ ff_addr (FF ++ LK)); [exact ND | apply in_or_app; left; apply INC; exact Hh | apply in_or_app; left; exact H | exact E]).
subst h. exact Hh.
- rewrite !map_app. rewrite map_app in ND. pose proof (NoDup_app_remove_l _ _ ND) as NDL. pose proof (NoDup_app_remove_r _ _ ND) as NDF.
assert (N2 : List.NoDup (map ff_addr FX ++ map ff_addr LK)).
{ clear - NDX NDL DISJ INC. induction FX as [|a l IH]; [exact NDL|]. cbn in *. inversion NDX as [|? ? Hn NDX']; subst. constructor.
- intros Y. apply in_app_or in Y. destruct Y as [Y | Y]; [exact (Hn Y)|]. apply in_map_iff in Y. destruct Y as (h & E & Hh).
apply (DISJ a h); [apply INC; left; reflexivity | exact Hh | symmetry; exact E].
- apply IH; [intros x Hx; apply INC; right; exact Hx | exact NDX']. }
pose proof (nodup_map_sfilter _ _ ff_addr P _ FF NDF) as N1.
assert (X : forall a, In a (map ff_addr (filter P FF)) -> ~ In a (map ff_addr FX ++ map ff_addr LK)).
{ intros a Ha Hb. apply in_map_iff in Ha. destruct Ha as (f & <- & Hf). apply sfilter_In in Hf. destruct Hf as (Pf & Hf). apply PX in Pf.
apply in_app_or in Hb. destruct Hb as [Hb | Hb]; [exact (Pf Hb)|]. apply in_map_iff in Hb. destruct Hb as (h & E & Hh). apply (DISJ f h Hf Hh). symmetry; exact E. }
clear - N1 N2 X. revert N1 X. generalize (map ff_addr (filter P FF)) as l1.
induction l1 as [|a l1 IH]; intros N1 X; [exact N2|]. cbn. inversion N1 as [|? ? Hn N1']; subst. constructor.
+ intros Y. apply in_app_or in Y. destruct Y as [Y | Y]; [exact (Hn Y) | exact (X a (or_introl eq_refl) Y)].
+ apply IH; [exact N1' | intros b Hb; apply X; right; exact Hb].
Qed.
End SE.
Lemma nodup_app_disj : forall (A B : Type) (g : A -> B) (l1 l2 : list A) x y, List.NoDup (map g (l1 ++ l2)) -> In x l1 -> In y l2 -> g x <> g y.
Proof.
intros A B g l1 l2 x y ND Hx Hy E. rewrite map_app in ND. induction l1 as [|a l IH]; [contradiction|]. cbn in ND. inversion ND as [|? ? Hn ND']; subst.
destruct Hx as [-> | Hx]; [apply Hn; apply in_or_app; right; rewrite E; apply in_map; exact Hy | apply IH; assumption].
Qed.
Lemma art_fsinv_defined : ltac2:(TCodec.tc2 tcn__JbtFsInvLaws "Q2'QA'Q4'1&Q0%211'REyR0%211'3y8%511%311p051&Q5r5r4r3r2r1%6554321&I&K&QBr6%211%411&J%73:21p091pQ<A1pQ8J1pQ0K1pTFO1pU4Q11").
Proof.
intros rn g FF LK M I. pose proof (fsinv_geo _ _ _ _ _ I) as (G1 & G2 & G3 & G4 & (G5 & G6 & G7) & _). destruct I as (_ & W & _).
cbn zeta in W. unfold FS_BYTES in *. intros j Hj.
assert (UA : bv_unsigned (Z_to_bv 64 (ar_fs (rn_ar rn) + j)) = ar_fs (rn_ar rn) + j) by (apply art_u_lit; lia).
assert (D : wview AsanUbsan.M.loaded_segments M (Z_to_bv 64 (ar_fs (rn_ar rn) + j)) <> None)
by (apply (art_wr_wview _ M (ar_fs (rn_ar rn)) 11571200); [lia | lia | exact W | rewrite UA; lia]).
rewrite art_wview_off in D by (rewrite UA; lia). exact D.
Qed.
Lemma mod_of_mul : ltac2:(TCodec.tc2 tcn__JbtFsInvLaws "D'=&QMzr2%3221'7r4&QOr3%2261%53:41&QNr5%2217%93>1<p051p0<1pU2A1pT8B1pUHC1").
Proof. intros x b q Hb ->. apply Z.mod_mul. lia. Qed.
Theorem art_fsinv_wf_proved : ltac2:(TCodec.tc2 tcn__JbtFsInvLaws "1&Q9").
Proof.
intros rn g FF LK M I. pose proof (fsinv_geo _ _ _ _ _ I) as (G1 & G2 & G3 & G4 & G5 & _). pose proof (art_fsinv_defined _ _ _ _ _ I) as DEF.
pose proof (fsinv_nodup _ _ _ _ _ I) as ND.
split; [|split; [exact G5 | split; [exact G3 | split; [exact G4 | split; [exact ND | exact DEF]]]]].
intros f Hf. assert (Hf' : In f (FF ++ LK)) by (apply in_or_app; left; exact Hf).
destruct (fsinv_slot _ _ _ _ _ I f Hf') as (K & i & Hi & A). pose proof (fsinv_frame_in _ _ _ _ _ I f Hf') as (IN1 & IN2 & IN3).
split; [lia|]. split; [exact IN2|]. split; [|split; [|split]].
- rewrite A. unfold fs_frame. pose proof (Z.div_mod (ar_fs (rn_ar rn)) 4096 ltac:(lia)) as DM. rewrite G1, Z.add_0_r in DM.
set (q := ar_fs (rn_ar rn) / 4096) in *. rewrite DM.
assert (C : ff_class f = 0 \/ ff_class f = 1 \/ ff_class f = 2 \/ ff_class f = 3 \/ ff_class f = 4) by lia. destruct C as [-> | [-> | [-> | [-> | ->]]]].
+ change (ff_bytes 0) with 64. apply (mod_of_mul _ 64 (64 * q + 576 + i)); [lia | change (2 ^ 20) with 1048576; ring].
+ change (ff_bytes 1) with 128. apply (mod_of_mul _ 128 (32 * q + 288 + 8192 + i)); [lia | change (2 ^ 20) with 1048576; ring].
+ change (ff_bytes 2) with 256. apply (mod_of_mul _ 256 (16 * q + 144 + 8192 + i)); [lia | change (2 ^ 20) with 1048576; ring].
+ change (ff_bytes 3) with 512. apply (mod_of_mul _ 512 (8 * q + 72 + 6144 + i)); [lia | change (2 ^ 20) with 1048576; ring].
+ change (ff_bytes 4) with 1024. apply (mod_of_mul _ 1024 (4 * q + 36 + 4096 + i)); [lia | change (2 ^ 20) with 1048576; ring].
- cbn [In]. lia.
- intros j Hj. replace (ff_addr f + j) with (ar_fs (rn_ar rn) + (ff_addr f - ar_fs (rn_ar rn) + j)) by ring. apply DEF. lia.
- intros f' Hf2. assert (NDF : List.NoDup (map ff_addr FF)) by (rewrite map_app in ND; eapply NoDup_app_remove_r; exact ND).
assert (Hf2' : In f' (FF ++ LK)) by (apply in_app_or in Hf2; apply in_or_app; destruct Hf2 as [X | X]; [left; eapply ff_remove_in; exact X | right; exact X]).
destruct (fsinv_frames_apart _ _ _ _ _ I f f' Hf' Hf2') as [<- | AP]; [exfalso | exact AP].
apply in_app_or in Hf2. destruct Hf2 as [X | X]; [exact (ff_remove_gone _ _ _ NDF X eq_refl) | exact (nodup_app_disj _ _ ff_addr FF LK f f ND Hf X eq_refl)].
Qed.
Lemma art_fsinv_nodup_stdpp : ltac2:(TCodec.tc2 tcn__JbtFsInvLaws "Q2'QA'Q4'1&Q0%211'REyR0%211'3y8%511%311p051&Q5r5r4r3r2r1%6554321'RC'=&<&L&0%13F:9%44G531%7261p091pQ<A1pQ8J1pQ0K1pTFO1pU4Q11").
Proof. intros rn g FF LK M I. apply NoDup_ListNoDup. exact (fsinv_nodup _ _ _ _ _ I). Qed.
Lemma cell8_inj : ltac2:(TCodec.tc2 tcn__JbtFsInvLaws "Q8'REyR0%211'3y8%511%311p051'=&H&QDr4r3u8r2%6554321r5%8571643'6&QLz%221:&QM&R0+2+R0%3221%52@1%:271'7r6%23G1?p041p051p0A1p0D1pUFL1pUDM1pT6N1pQ<Q01").
Proof.
intros M a v w C1 C2 Hv Hw. unfold cell in *. rewrite C1 in C2.
apply (f_equal (fun o : option (list byte) => match o with Some l => bytes_le_to_Z l | None => 0 end)) in C2.
rewrite !SeqExec.bytes_le_to_Z_8 in C2. rewrite !art_u_lit in C2 by lia. exact C2.
Qed.
Theorem art_fsinv_release_fl : ltac2:(TCodec.tc2 tcn__JbtFsInvLaws "SC'QA'Q4'1&Q0%211'REyR0%211'3y8%511%311p051'=&Q5r:r9r8r7r6%6554321&QF'5%12::%221;(4r5r4%34??21r3%547A21%:371?&H&QD&R1&QJ&M%11;%32C1+8%6221u8%:59I21='6&QLz%221C&QM&R0+2+R0%3221%52I1%:271&QC%12Q8Q7u1%I5HQ:Q61<&:'7&RFr1%22QH1%43QB1Q>%611&Q@rBr2%82QN1%4231&Q1rA%<2R2Q;%3221%@11r?%11QAr@%11QC%D3R431p061p0<1p0B1pUHR<1&Q:%12CGr>%11D%=1E%N3R>21p051pUHRD1&Or<%221Ar=%RB5NI2E1p061p0?1p0Q:1p0Q=1p0Q@1p0QL1p0R81p0RD1pTBRL1pU6RM1pU0RN1pNRO1pQ>S11pQ<S21pQ8S;1pQ0S<1pTFS@1pU4SB1").
Proof.
intros rn g FF LK M M' F k rs fl I HF CF Rfl GR C0 AG AGCS.
assert (HF' : In (F, k, rs) (FF ++ LK)) by (apply in_or_app; left; exact HF).
pose proof (fsinv_geo _ _ _ _ _ I) as (G1 & G2 & G3 & G4 & (G5 & G6 & G7) & _).
pose proof I as (_ & _ & _ & _ & _ & _ & _ & _ & FR & _). cbn zeta in FR. destruct (FR _ HF') as (K & (i & (Hi & A) & CS) & _).
unfold ff_class, ff_addr in K, Hi, A, CS. cbn [fst snd] in K, Hi, A, CS.
pose proof (fs_flag_below_frames (ar_fs (rn_ar rn)) k i ltac:(lia) Hi) as FB. unfold FS_BYTES in *.
assert (E : fl = fs_flag (ar_fs (rn_ar rn)) k i) by (apply (cell8_inj M _ _ _ CF CS); lia).
apply (art_fsinv_release_proved rn g FF LK M M' F k rs I HF GR); [|exact AGCS]. exists i. rewrite <- E.
split; [exact Hi|]. split; [exact A|]. split; [exact C0|]. intros x NE Z3 NF. apply AG; assumption.
Qed.
