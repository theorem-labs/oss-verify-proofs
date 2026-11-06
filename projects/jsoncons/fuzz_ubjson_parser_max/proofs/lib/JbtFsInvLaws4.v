(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import PropExec CatSim StoreOk AsanAcct HeapIface HeapIfaceA ArtMem ArtRuns ArtRunsMem JbtCellEx JbtAllocG JbtDepot ArtBridge JbtInv.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import JbtFsInv JbtFsInvLaws.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLia. Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLiaT.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import SecKit. From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__JbtFsInvLaws4 () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Lists.ListDef."; "Corelib.Numbers.BinNums."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.ArtBridge."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.ArtMem."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.HeapIfaceA."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.JbtFsInv."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.JbtFsInvLaws."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.JbtInv."; "OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.AsanUbsan.M."; "Stdlib.Lists.List."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["1None"; "1app"; "1list"; "1option"; "2and"; "2eq"; "2iff"; "2not"; "2or"; "3map"; "4Z"; "0FF"; "0FF'"; "0LK"; "0M"; "0M'"]; ["5in_shadow_rw"; "6cell"; "7FS_BYTES"; "7ar_fs"; "7ff_addr"; "7fframe"; "7in_fframe"; "8art_c_statics"; "8art_fs_geo"; "8art_fsg"; "8art_fsinv"; "8cs_zone"; "8fs_flag"; "8fs_nfr"; "9fs_slot_taken"; "9fs_zone3"]; [":art_fs_zone"; ":art_run"; ":rn_ar"; ";loaded_segments"; "<NoDup"; "<incl"; "=add"; "=le"; "=lt"; "0a"; "0c"; "0fl"; "0g"; "0i"; "0rn"; ">bv"]; [">bv_unsigned"; "0x"]]).
Local Ltac lia := L5FastLiaT.plia1.
Open Scope Z_scope.
#[local] Abbreviation cellA := (cell AsanUbsan.M.loaded_segments).
#[local] Abbreviation wrA := (wr AsanUbsan.M.loaded_segments).
#[local] Notation "'U' r" := (bv_unsigned r) (at level 10, r at level 9).
Section SE.
Local Abbreviation SEC_T_art_c_statics_keep2 := (ltac2:(TCodec.tc2 tcn__JbtFsInvLaws4 "Q@'Q1'Q?yR0%211'3y8%511%311p051&Hr3%211&Gr4%2214&@&Q@r1%22@1%411&7'5r5r2%211(0%11D%63D31%811p0:1pRDK1&Kr7%221?r6%11<%41=%@3N21p051pS4Q41%L28Bp021p0<1p0M1p0Q11pQ0Q51pNQ61pRNQ?1")) (only parsing).
Variable rn : ltac:(sec_ty2 constr:(SEC_T_art_c_statics_keep2) 0%nat 0%nat).
Variable M : ltac:(sec_ty2 constr:(SEC_T_art_c_statics_keep2) 1%nat 0%nat).
Variable M' : ltac:(sec_ty2 constr:(SEC_T_art_c_statics_keep2) 2%nat 0%nat).
Lemma art_c_statics_keep2 : ltac:(sec_stmt2 constr:(SEC_T_art_c_statics_keep2) 3%nat 0%nat).
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
exact GR.
Qed.
End SE.
Section SE.
Local Abbreviation SEC_T_art_fsinv_core2 := (ltac2:(TCodec.tc2 tcn__JbtFsInvLaws4 "UA'Q1'I'2&E%211'Q?yR0%211'3y8%511%311p051pS462':&Jr8r7r6r5r4%6554321&@&Q@r1%22C1%411&7'5r2%<11(0%11F%53F31%711p091pRDM1'4&Q7&C&Q2r;%211%411%621C&Q8&Q6&B%2251%42H1%=261%Q21F%Q41G%I3Q:21p041pS4Q@1'8+TP0%<2?1%E21Q7+QTP0%?2B1%A2Q:1%J241z%D2Q=1%:231&Or=%221Q<&Fr<%QA2R2Q;%3221%Q?11r3%QE2R61%QA3QO1QM%QC11%Q61QK%91QL%QE3R621p041p091p0?1pS4R>1&Kr>%221QOr:%11QM%QB1QN%R03RA21p051pS4RG1&Q5%13RMR@I'Q4&9&D&1r9%23S31O%54S4RI41%72RJ1%R32Q9R<+:%R52R>1%R7231&M%11Q3%R22RB1%R;271&LrD%R;11%R=11%431S1Q:%RJ3S81QB%RL11&6&NrE%RC11%RE11r?rB%K3SL21%7441S=S<rC%N3SO14%:471S@S?%<241p0>1p0F1p0K1pRLSJ1pRFSK1%I3>SFQO%S?3SM1QD&A&Q3rAu1%4532C1R@rF%S:11%S<11r@%QA3TB1D%M431T3T2%SL11%SC281p0>1p0Q:1p0Q?1pRLT>1pRFT?1%T?5Q0@RGQ1RJp021p0G1p0QI1p0R21p0R51p0R?1p0S31p0S?1p0T31p0TC1pRHTK1pJU61pQ0TN1pNU01pLU91pHU:1pRJU>1pRNU@1")) (only parsing).
Variable rn : ltac:(sec_ty2 constr:(SEC_T_art_fsinv_core2) 0%nat 0%nat).
Variable g : ltac:(sec_ty2 constr:(SEC_T_art_fsinv_core2) 1%nat 0%nat).
Variable FF : ltac:(sec_ty2 constr:(SEC_T_art_fsinv_core2) 2%nat 0%nat).
Variable LK : ltac:(sec_ty2 constr:(SEC_T_art_fsinv_core2) 3%nat 0%nat).
Variable M : ltac:(sec_ty2 constr:(SEC_T_art_fsinv_core2) 4%nat 0%nat).
Variable M' : ltac:(sec_ty2 constr:(SEC_T_art_fsinv_core2) 5%nat 0%nat).
Variable FF' : ltac:(sec_ty2 constr:(SEC_T_art_fsinv_core2) 6%nat 0%nat).
Variable fl : ltac:(sec_ty2 constr:(SEC_T_art_fsinv_core2) 7%nat 0%nat).
Lemma art_fsinv_core2 : ltac:(sec_stmt2 constr:(SEC_T_art_fsinv_core2) 8%nat 0%nat).
Proof.
intros I GR AGW Hfl AG AGCS INC ND' TK0 TK1.
pose proof (art_c_statics_keep2 rn M M' (fsinv_geo _ _ _ _ _ I) (fsinv_cs _ _ _ _ _ I) GR AGCS) as CS'.
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
split; [exact GEO|]. split; [apply (wr_agree M M' fs 11571200 ltac:(lia) ltac:(lia)); [intros x Hx; apply AGW; exact Hx | exact W]|].
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
Section SE.
Local Abbreviation SEC_T_art_fsinv_frame_law2_proved := (ltac2:(TCodec.tc2 tcn__JbtFsInvLaws4 "QE'Q1'I'2&E%211'Q?yR0%211'3y8%511%311p051&Jr6r5r4r3r2%6554321&Q0r8&Q@r1%22B1%5241'5%;19%=1:%33B21p051pS4H1&@%119&7(0%11J%;3J91%411p061pRDQ11r9r7%N52F1MKp041p0>1p0K1pQ0Q31pNQ41pLQ=1pHQ>1pRJQB1pRNQD1")) (only parsing).
Variable rn : ltac:(sec_ty2 constr:(SEC_T_art_fsinv_frame_law2_proved) 0%nat 0%nat).
Variable g : ltac:(sec_ty2 constr:(SEC_T_art_fsinv_frame_law2_proved) 1%nat 0%nat).
Variable FF : ltac:(sec_ty2 constr:(SEC_T_art_fsinv_frame_law2_proved) 2%nat 0%nat).
Variable LK : ltac:(sec_ty2 constr:(SEC_T_art_fsinv_frame_law2_proved) 3%nat 0%nat).
Variable M : ltac:(sec_ty2 constr:(SEC_T_art_fsinv_frame_law2_proved) 4%nat 0%nat).
Variable M' : ltac:(sec_ty2 constr:(SEC_T_art_fsinv_frame_law2_proved) 5%nat 0%nat).
Theorem art_fsinv_frame_law2_proved : ltac:(sec_stmt2 constr:(SEC_T_art_fsinv_frame_law2_proved) 6%nat 0%nat).
Proof.
intros I AG SD.
destruct (fsinv_geo _ _ _ _ _ I) as (_ & G2 & _ & _ & _ & _ & _ & _ & G11 & G12). destruct (fsinv_cs _ _ _ _ _ I) as ((Q1 & Q2 & Q3) & _).
apply (art_fsinv_core2 rn g FF LK M M' FF (-1) I SD); [ | right; lia | | | apply incl_refl | exact (fsinv_nodup _ _ _ _ _ I) | tauto | ].
- intros x Hx. apply AG. left. exact Hx.
- intros x Z3 _ _. apply AG. unfold art_fs_zone. destruct Z3 as [Z | [Z | Z]]; [left; exact Z | right; left; exact Z |].
right; right; right. left. unfold art_zone_statics. lia.
- intros x Z. apply AG. unfold art_fs_zone. destruct Z as [Z | [Z | [Z | [Z | Z]]]].
+ right; right; right; left. unfold art_zone_statics. lia.
+ right; right; right; left. unfold art_zone_statics. lia.
+ right; right; right; left. unfold art_zone_statics. lia.
+ do 5 right. lia.
+ do 4 right. left. exact Z.
- intros c i Hc Hi E. exfalso. pose proof (fs_flag_below_frames (ar_fs (rn_ar rn)) c i Hc Hi). lia.
Qed.
End SE.
