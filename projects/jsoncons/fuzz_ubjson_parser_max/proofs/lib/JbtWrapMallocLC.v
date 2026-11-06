(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import PropExec CatSim StoreOk Hoare AsanAcct HeapIface HeapIfaceA As0Tables
ArtMem JbtPoison ArtRuns ArtRunsMem JbtCls JbtFp JbtCellEx JbtByteCell ArtBridge JbtSecAllocPost JbtSecRSpec JbtAllocate3L JbtMallocTop3L
JbtInv JbtInvMallocPure JbtInvMallocFp JbtInvMalloc JbtInvMallocL JbtLift JbtWrapPure JbtWrapKit JbtWrapMallocX JbtWrapMallocLX.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import HeapIfaceAJx ShadowRLaws.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLia. Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLiaT.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import SecKit. From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__JbtWrapMallocLC () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.LinuxProcessSem.State."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.ArtBridge."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.ArtMem."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.ArtRuns."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.AsanAcct."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.HeapIface."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.HeapIfaceA."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.JbtAllocate3L."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.JbtFp."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.JbtInv."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.JbtMallocTop3L."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.JbtPoison."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.JbtSecRSpec."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.StoreOk."; "OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.AsanUbsan.M."; "Stdlib.Lists.List."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["0A"; "0A'"; "1None"; "1Some"; "1app"; "1bool"; "1cons"; "1false"; "1fst"; "1list"; "1option"; "1pair"; "1prod"; "1snd"; "1true"; "2and"]; ["2eq"; "2not"; "2or"; "3Z"; "0FF"; "0L"; "0LB"; "0LK"; "4Model"; "4page_base"; "0M"; "0M1"; "5HSH_HI"; "5HSH_LO"; "5LSH_HI"; "5LSH_LO"]; ["5bhid"; "5bhist"; "5in_ev_ranges"; "5in_shadow_rw"; "6apart"; "6wr"; "7aev"; "7art_shhi"; "7art_shlo"; "8mkH"; "8mrestrict"; "8page_allowedb"; "9blocks_apart"; "9defined"; ":FS_BYTES"; ":ablock_range"]; [":aheap_pres"; ":ar_fs"; ":ff_addr"; ":ff_bytes"; ":ff_class"; ":fframe"; ":fframes_apart"; ":in_shadow_of"; ":shadow_allowed"; ":shadow_blk"; ";art_sec_grant3"; "<art_agree"; "<art_out"; "=art_client_ok"; "=art_run"; "=art_run_ok"]; ["=rn_HI"; "=rn_ar"; "=rn_blk"; "=rn_ctx"; "=rn_l2"; "=rn_parr"; "=rn_spb"; "=rn_t"; ">art_malloc3L_fp"; "?SB"; "@art_sec_events"; "Amem_grows"; "Bloaded_segments"; "0Sp"; "CIn"; "Cincl"]; ["Dadd"; "Ddiv"; "Dle"; "Dlt"; "Dmodulo"; "Dmul"; "Dpow"; "Dsub"; "0WL"; "0a"; "0b"; "0blk"; "0cm"; "0f"; "0l2"; "0lazy"]; ["0len"; "0lo"; "0log"; "0log'"; "0model"; "0model'"; "0msz"; "0n"; "0nch"; "0parr"; "0r"; "0rn"; "EZ_to_bv"; "Ebv"; "Ebv_unsigned"; "0t"]; ["0u"; "0x"; "0z"]]).
Local Ltac lia := L5FastLiaT.plia1.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
#[local] Abbreviation ASEGS := AsanUbsan.M.loaded_segments.
#[local] Abbreviation cellA := (cell AsanUbsan.M.loaded_segments).
#[local] Abbreviation wrA := (wr AsanUbsan.M.loaded_segments).
#[local] Notation "'U' r" := (bv_unsigned r) (at level 10, r at level 9).
Lemma art_allowed_vis : ltac2:(TCodec.tc2 tcn__JbtWrapMallocLC "N'9'<'S=yR0%211%4211%611'C%7211%911'@'5&Q;r2&Ir1%211%5241(>%93821&Q9r4r3%3321:(7%?3>21p071pW4G1p2C1pV0G1").
Proof. intros lazy A x H. unfold mkH. rewrite H. cbn. apply andb_false_r. Qed.
Lemma art_in_sec_events : ltac2:(TCodec.tc2 tcn__JbtWrapMallocLC "Q>'C'5&Q2&R:r6r5r4r3r2%6554321r1%9221'B'?&RB&Q8%11<%3219&RC&Q7r7%22A1%42>1%:261'@(7%23IC1&R@&RE+8%221H%42J1%B21H+TPP0%7231%A2K1%G241%H2;1%J2?1p0L1pW6Q81pUJQ81pVBQ:1pVDQ;1pVFQ<1pV>Q=1").
Proof.
intros msz r parr nch cm z (ev & Hev & Hz). unfold art_sec_events in Hev. destruct Hev as [<-|Hev]; [left; exact Hz|].
destruct cm; [destruct Hev|]. destruct Hev as [<-|[]]. right. split; [reflexivity|exact Hz].
Qed.
Section ExitMem.
Context {fx : PropExec.FPState}.
#[using="fx"] Lemma art_wmlc_mem : ltac2:(TCodec.tc2 tcn__JbtWrapMallocLC "W:'9'<'C%2211%411'S=yR0%211':y8%511%311p051'H'Q6%?11'5&R8r9r8r7r6r5r4r3r2r1%:9987654321'@r;&4r<&R:%15;<>=8%43D31%73D61&Q1rCrAr?r=rBr@r>%887654=321&Q3&S>%12Q9E%311&A%=1I(2%11Q:%I3Q:31%511p071pUDQA1'B'?&RB&O&Q8%11Q<%4231&Q7%12Q?Q>&N%8221%:251&M%;218&L%=271%?231%A261+Vb\P0%A21Q=&RC&R@&RF+2+G%3221%52Q;1+QO%6251%9231z%M21Q@+`P0%O2QB1%Q1231(7%R13R=R;1%R23RLQG7p021&R;&Q:&Q0rJrF%3221rH%6221rIrE%8221rG%;221%=261&QKr:rK%?216%A21:%5341<%QG1R;%R72S?RL%QK221%QG2R>RA%Q;231%QO231&R9&RA+8%22RH1%Q@241%RA2SIS7%R5221%62RH5%QD241%QF241%R:241%RD11rQ0rL%Q6221rN%Q9321SC(3%12T2SD%SA3T231%Q=365SH%42T5SH%SD3T521p041p0=1p0J1pUFT:1pW4T>1&Q5&R<%QF2AQB%QH21QF+TPP0%5442SF1&QL%12SBS>rM%11T6%G1T7%T53TF21p051pW4TL1%S71SO%S:21SF%S62T1SM%RJ2SH1%S>231rD%Q?21Q>%RM2QA1%SA21QG%RO22Q@%S12QI1%SE231%SO11rQ1%R@31DTJ%TG3U31RG%Q>1TM%TI3U:1T1%T511%QA1U1%71U2%TM3U>21p041p081p0<1p0E1pW4UG1%RO2QHR?%T52RGTA%SC2RHQ7%SE2TC1%T9231rO%S331REU<%U:3UF1S:p041pW4V11%T?2:1%T@2<1%TA2Q81p0QA1p0QH1p0RK1p0S21p0SA1p0SF1p0SL1p0T71p0T:1p0TM1p0U:1p0UD1tUBVDUM1pUJV91pUHVH1pUNVI1pV>VJ1pVFVK1pVBVL1pVDVM1pW0VN1pTLVO1pV8VC1pV6VD1pV<VG1pV:VH1pQHVJ1pQFVK1p4W41p2W51").
Proof.
intros A A' M M1 model model' log log' Sp t parr nch r msz l2 blk cm WL Elog BH SHD WOK Hparr Hparr' Hnch Hnch0 GRW AG WIN WP.
assert (VISP : forall x : word, parr <= U x < parr + 131072 -> bhid A' model' x = false).
{ apply (art_vis_of_wr (bhid A' model') M1 parr 131072); [lia|lia|right; lia|exact WP]. }
split; [|split; [|split; [|exact VISP]]].
-
intros x Ox. apply (art_lift_frame A A' M M1 model model' log log' BH (fun z => ~ art_out WL z)).
+ intros y NN. apply AG. unfold WL, art_malloc3L_fp in *. cbn [art_out fst snd] in *. repeat split; try exact I; intros IN; apply NN; intros O; tauto.
+ intros sfx Esfx z Hz. rewrite Elog in Esfx. apply app_inv_head in Esfx. subst sfx. intros O.
destruct (art_in_sec_events _ _ _ _ _ _ Hz) as [Zw|(Ecm & Zp)]; unfold WL, art_malloc3L_fp in O; cbn [art_out fst snd] in O.
* lia.
* rewrite Ecm in O. lia.
+ intros NN. exact (NN Ox).
-
intros x Hx Nx Vx Dx. destruct (M x) as [b|] eqn:Eb; [|contradiction].
assert (R0 : mrestrict (bhid A model) M x = Some b) by (unfold mrestrict; rewrite Vx; exact Eb).
pose proof (WIN x b Hx Nx R0) as R1. unfold mrestrict in R1. destruct (bhid A' model' x); [discriminate R1|exact R1].
-
apply (art_lift_grows A A' M M1 model model' log log' BH GRW).
intros sfx Esfx x Hz Vx. rewrite Elog in Esfx. apply app_inv_head in Esfx. subst sfx.
unfold mrestrict. rewrite Vx.
destruct (art_in_sec_events _ _ _ _ _ _ Hz) as [Zw|(Ecm & Zp)].
+ apply SHD. unfold in_shadow_rw. lia.
+ pose proof (art_wr_wview ASEGS (mrestrict (bhid A' model') M1) parr 131072 ltac:(lia) ltac:(lia) WP x) as V.
rewrite (Hnch0 Ecm) in Zp. specialize (V ltac:(lia)). rewrite art_wview_off in V by (right; lia). unfold mrestrict in V. rewrite Vx in V. exact V.
Qed.
End ExitMem.
Lemma art_sh_apart : ltac2:(TCodec.tc2 tcn__JbtWrapMallocLC "Q?'C'@&RE+8&RAr5%2213%5241%73813&RBz%2216&RC%1238&Q4r9r8r7r6%544321&QG%13543&A'?&R@&R9r;%G21H%4231%D21<r:%K21L%8241%E2@1%;251%=11p0?1p0B1p0I1p0L1p0Q01p0Q11pUDQ:1pV2Q;1pV4Q<1pV>Q=1pVFQ>1").
Proof.
intros r msz lo len a E1 E2 Hlo Hlen AP (H1 & H2). unfold HeapIfaceA.S, HeapIfaceA.SB in *. unfold JbtPoison.SB.
pose proof (Z.mul_div_le lo 8 ltac:(lia)) as D1. pose proof (Z.mul_succ_div_gt lo 8 ltac:(lia)) as D2.
pose proof (Z.mul_div_le (lo + len - 1) 8 ltac:(lia)) as D3. pose proof (Z.mul_succ_div_gt (lo + len - 1) 8 ltac:(lia)) as D4.
unfold apart in AP. lia.
Qed.
Section ExitClient.
Variable L : asan_layout.
Hypothesis HLlo : hl_img_lo L = 0x10000.
Hypothesis HLhi : hl_img_hi L = 0x693000.
Hypothesis HLst : forall a, art_zone_statics a -> hl_rt_static L a.
Section SE.
Local Abbreviation SEC_T_art_wmlc_client := (ltac2:(TCodec.tc2 tcn__JbtWrapMallocLC "Z0'QN'9'<'C%2211%411&QE%611'S=yR0%211%9211%;11':y8%711%311p071'5&R8r7&R7r@%211&R5%113r6r5r4&R4%118&R2%11:r1%?9>;9876421&QOrA%211&QMrBr?r>r;%5647E321&R?%13Q954&R;r=r<%3221&QL&S>%12Q;C%32K1'@r2%@11%Q312%43Q:21p061pW4QB1'?&RB&Q8%11@%321=&RC&Q7%12DJ%32A1%9251&A&R@&R9&RA+8%22M1%5241%K2R5G%A221%62Q05%9241%@241%F241%=11&Q9rCrEr3%43321(7%Q53R921%61R0(2%11R?%Q93R?31%I11%;1R6rD%11R8%Q>3RD31p051p0;1p0C1p0Q21pW4RO1&Q3%11QG%R51QE%QG3RM1?%Q711p041pUDS61&R0rH%211+TP0%Q=221&RG%12R?3%QJ231&RF+2+Q?%3221%QO2S71z%R121S9+`P0%R32S;1%R5231&QJrK%D11%SA12&R3%114%SA15&R6%117%S?18%S>19%;99865321S6SH&Q4&QA&R1rL%211%411&Q>%74SBT021&RE%R>2SAR=%22R>1%S43TG1SC%RI2MR5'B&O%RO1R7%S1221%RM2R9QN&N%S4221%S6241&M%S7217&L%S9271%S;231%=261&R>rQ1%23U8T;1rG&8%13U<U<SH&=%13U>U>SJ%Q34R0531p071pUFU@1rQ3%<3UBSO1%93UDUDRO%SJ21T1%93UFUFS1%SB231%SI2T41%SO241rF%T<21S6p031p0:1pUDUN1pUFUN1&4rQ2%23UO1J%L3V0U51rQ5%QG11%QI11&QB%11TD%T>231&QC&QD%11TH%311%T9261%T:29QM%TE221%TB2RF4%TH221%TI2:1p0A1pULVB1%S32R7S5%TL21UI%TI2UJR9%TO221rO&S<%12VFU8%311%U;3VA1T3%TK11p071pUDW11rJ%TN21SB%U921SErI%U121SG%U22S65%U=221&RD+@%2291%UI3W<1SA%U>2SL;&Q=%13R7S0S>&QIrM%23QA1S3&QHrQ6rN%33215rQ<(6(;%14WJWJQ05rQ;%43WK21rQ:rQ9rQ7rQ4%VN6:54321&Q?vE%SF1=%3421Q;@&Q<%13Q=B<&QF%R93X6<;%23Q@E1&Q@%1898A?RJTKR8<%VC231%VD271%VE2:1%VF2?1p0K1p0Q01p0Q41p0Q71p0Q91p0Q>1p0QC1p0QG1p0R41p0RK1p0S:1p0SF1p0T51p0T71p0T81p0T=1p0TF1p0U31p0U91p0U?1p0UH1p0V01p0W>1p0WJ1p0WO1p0X21p0X91tUBY:X=1pUJXN1pV@Y>1pW2Y?1pV>Y@1pVFYA1pVBYB1pTLYC1pQHY61pQFY71pV0Y=1p4YE1p2YF1pQ@YE1pQ:YF1pQ>YI1pVHYO1")) (only parsing).
Variable rn : ltac:(sec_ty2 constr:(SEC_T_art_wmlc_client) 0%nat 0%nat).
Variable LB : ltac:(sec_ty2 constr:(SEC_T_art_wmlc_client) 1%nat 0%nat).
Variable FF : ltac:(sec_ty2 constr:(SEC_T_art_wmlc_client) 2%nat 0%nat).
Variable LK : ltac:(sec_ty2 constr:(SEC_T_art_wmlc_client) 3%nat 0%nat).
Variable A : ltac:(sec_ty2 constr:(SEC_T_art_wmlc_client) 4%nat 0%nat).
Variable A' : ltac:(sec_ty2 constr:(SEC_T_art_wmlc_client) 5%nat 0%nat).
Variable lazy : ltac:(sec_ty2 constr:(SEC_T_art_wmlc_client) 6%nat 0%nat).
Variable M : ltac:(sec_ty2 constr:(SEC_T_art_wmlc_client) 7%nat 0%nat).
Variable M1 : ltac:(sec_ty2 constr:(SEC_T_art_wmlc_client) 8%nat 0%nat).
Variable Sp : ltac:(sec_ty2 constr:(SEC_T_art_wmlc_client) 9%nat 0%nat).
Variable nch : ltac:(sec_ty2 constr:(SEC_T_art_wmlc_client) 10%nat 0%nat).
Variable r : ltac:(sec_ty2 constr:(SEC_T_art_wmlc_client) 11%nat 0%nat).
Variable msz : ltac:(sec_ty2 constr:(SEC_T_art_wmlc_client) 12%nat 0%nat).
Variable u : ltac:(sec_ty2 constr:(SEC_T_art_wmlc_client) 13%nat 0%nat).
Variable n : ltac:(sec_ty2 constr:(SEC_T_art_wmlc_client) 14%nat 0%nat).
Lemma art_wmlc_client : ltac:(sec_stmt2 constr:(SEC_T_art_wmlc_client) 15%nat 0%nat).
Proof using HLlo HLhi HLst rn LB FF LK A A' lazy M M1 Sp nch r msz u n.
intros cm WL ROK CLI INC GRW FRF FRW SHD HS HS47 Hnch GRANT Arf E1 E2 Hmsz WOK BLK NFPB FSIN SCR Hu1 Hu2 Hu16 Hbig DEFu SHu SAu.
assert (Hn : 0 < n) by lia.
pose proof (art_run_ok_tail rn ROK) as (Il2 & Iblk & _).
pose proof ROK as ROK'. rok_open ROK'. geo_open GEO.
destruct GRANT as ((Hr4 & Hr & Hri & Hrm & APr & Art & Arc & Arp) & Ark & Arl2 & Arblk).
destruct CLI as (CB & CND & CSA1 & CSA2 & CS1 & CS2 & CS3 & CS4 & CS5 & CS6 & CSI & CSP & CS16).
assert (HIeq : ahl_ceil (rn_ar rn) = rn_HI rn) by reflexivity.
unfold appmem, JbtPoison.SB, JbtPoison.kHighMemBeg in APr. unfold LSH_LO, LSH_HI, HSH_LO, HSH_HI in WOK.
assert (SHEQ : forall lo len a, 0 <= lo -> 0 < len -> lo + len <= 2 ^ 47 -> apart r msz lo len -> in_shadow_of lo len a -> 0 <= a < 2 ^ 64 ->
page_allowedb A (page_base (Z_to_bv 64 a)) = true -> M1 (Z_to_bv 64 a) = M (Z_to_bv 64 a)).
{ intros lo len a Hlo Hlen Hhi AP SH Ha AL.
assert (Ua : U (Z_to_bv 64 a : word) = a) by (apply art_u_lit; lia).
pose proof (art_sh_apart r msz lo len a E1 E2 Hlo Hlen AP SH) as NE.
destruct SH as (SH1 & SH2). pose proof (art_S_ge lo 0 ltac:(lia)) as B0. pose proof (art_S_lt (lo + len - 1) (2 ^ 44) ltac:(lia)) as B2.
destruct (Z_le_dec (art_shlo r) a) as [L1|L1]; [destruct (Z_lt_dec a (art_shhi r msz)) as [L2|L2]|].
- apply FRW; [rewrite Ua; clear - L1 L2; lia|rewrite Ua; exact NE|apply art_allowed_vis; exact AL|apply SHD; rewrite Ua; unfold in_shadow_rw, LSH_LO, LSH_HI, HSH_LO, HSH_HI; clear - CS1 CS6 Hr Hri Hmsz WOK Hu1 Plo Flo SH1 SH2 B0 B2 L1 L2; lia].
- apply FRF. rewrite Ua. unfold WL, art_malloc3L_fp. destruct Papp as (_ & Pap & _). unfold BIGSHADOW_LO, BIGSHADOW_HI in Pap.
set (wlo := art_shlo r) in *. set (whi := art_shhi r msz) in *.
clear - B0 B2 SH1 SH2 L2 HS G1 G10 APr Pap Al2s Abs Hnch. unfold apart in *. cbn [art_out fst snd]. destruct cm; repeat split; try exact I; lia.
- apply FRF. rewrite Ua. unfold WL, art_malloc3L_fp. destruct Papp as (_ & Pap & _). unfold BIGSHADOW_LO, BIGSHADOW_HI in Pap.
set (wlo := art_shlo r) in *. set (whi := art_shhi r msz) in *.
clear - B0 B2 SH1 SH2 L1 HS G1 G10 APr Pap Al2s Abs Hnch. unfold apart in *. cbn [art_out fst snd]. destruct cm; repeat split; try exact I; lia. }
assert (EQ : forall a, 0 <= a < 2 ^ 64 -> art_out WL a -> M1 (Z_to_bv 64 a) = M (Z_to_bv 64 a)).
{ intros a Ha O. apply FRF. rewrite art_u_lit by lia. exact O. }
assert (BA : blocks_apart u n LB).
{ intros b Hb. pose proof (BLK b Hb) as AP. destruct (CB b Hb) as (_ & _ & _ & B4 & _). unfold apart in AP. clear - AP Hu1 Hu2 B4 Hn. lia. }
assert (FFA : fframes_apart u n (FF ++ LK)).
{ intros f Hf. destruct (FSIN f Hf) as (F1 & F2 & _). unfold apart, FS_BYTES in *. clear - F1 F2 Arf Hu1 Hu2. lia. }
assert (SHA : forall a0 n0, shadow_allowed A a0 n0 -> shadow_allowed A' a0 n0).
{ intros a0 n0 SA x Hx. apply (art_page_allowedb_incl A A' _ INC). exact (SA x Hx). }
assert (SHB : forall b, In b LB -> HAJ.shadow_blkR M (fst b) (snd b) -> HAJ.shadow_blkR M1 (fst b) (snd b)).
{ intros b Hb SB0. destruct (CB b Hb) as (B1 & _ & _ & B4 & B5 & _ & _ & _ & B9 & _). rewrite HIeq in B5.
assert (T : forall j, 0 <= j -> (j < snd b / 8 \/ (j = snd b / 8 /\ snd b mod 8 <> 0)) -> forall v, byte_at M (HeapIfaceA.S (fst b) + j) v -> byte_at M1 (HeapIfaceA.S (fst b) + j) v).
{ intros j Hj0 Hj v B. pose proof (art_S_blk_hi (fst b) (snd b) j B4 Hj) as H1. pose proof (art_S_ge (fst b) 0 ltac:(lia)) as H0. pose proof (art_S_lt (fst b + snd b - 1) (2 ^ 44) ltac:(lia)) as H2.
apply (art_byte_at_eq M M1); [|exact B].
apply (SHEQ (fst b) (snd b)); [lia|exact B4|lia|exact (BLK b Hb)|unfold in_shadow_of; lia|lia|apply B9; unfold in_shadow_of; lia]. }
exact (shadow_blkR_tby M M1 (fst b) (snd b) B4 T SB0). }
split; [|split; [|split; [exact BA|split; [exact FFA|]]]].
-
unfold art_client_ok. split; [|split; [|split; [exact (SHA _ _ CSA1)|split; [exact (SHA _ _ CSA2)|repeat split; first [assumption|exact (SHA _ _ CSI)|lia]]]]].
+ intros b [Eb|Hb].
* subst b. cbn [fst snd]. split; [lia|]. split; [right; lia|]. split; [exact Hu16|]. split; [exact Hn|]. split; [rewrite HIeq; lia|].
split; [unfold app_mem, BIGSHADOW_LO, BIGSHADOW_HI; clear - APr Hu1 Hu2 Hn Hr Hrm G2; lia|]. split; [exact DEFu|]. split; [left; exact SHu|]. split; [exact SAu|].
split. { cbn [lb_remove fst]. rewrite Z.eqb_refl. exact BA. }
split; [exact FFA|]. split; [unfold apart, FS_BYTES in *; clear - Arf Hu1 Hu2; lia|]. intros Hsmall. exfalso. clear - Hsmall Hbig. lia.
* destruct (CB b Hb) as (B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8 & B9 & B10 & B11 & B12).
split; [exact B1|]. split; [exact B2|]. split; [exact B3|]. split; [exact B4|]. split; [exact B5|]. split; [exact B6|].
split. { intros i Hi. apply GRW. exact (B7 i Hi). }
split; [exact (SHB b Hb B8)|]. split; [exact (SHA _ _ B9)|].
split. { cbn [lb_remove fst]. pose proof (BA b Hb) as AP. destruct (Z.eqb_spec u (fst b)) as [E|NE]; [exfalso; clear - E AP B1 B2 B3 B4 B5 B6 Hn Hu1 Hu2 Hu16; lia|].
intros b' [Eb'|Hb']; [subst b'; cbn [fst snd]; lia|exact (B10 b' Hb')]. }
split; [exact B11|exact B12].
+ cbn [map fst]. apply NoDup_ListNoDup. constructor; [|apply NoDup_ListNoDup; exact CND]. intros Hin. apply in_map_iff in Hin. destruct Hin as (b & Eb & Hb).
destruct (CB b Hb) as (_ & _ & _ & B4 & _). pose proof (BA b Hb) as AP. clear - CS1 CS6 Hr Hri Hmsz Hu1 Hbig Plo Flo Eb B4 AP; lia.
-
unfold ablock_range. rewrite HLlo, HLhi. split; [lia|]. split; [right; lia|]. split; [exact Hu16|]. split; [exact Hn|]. split; [rewrite HIeq; lia|].
unfold app_mem, BIGSHADOW_LO, BIGSHADOW_HI. clear - APr Hu1 Hu2 Hn Hr Hrm G2. lia.
-
split.
+ intros a Ha CLa. unfold aclient, aclient_g in CLa.
destruct CLa as [(b & Hb & Hr')|[((C1 & C2) & C3)|[((C1 & C2) & C3)|[(f & Hf & R1 & R2)|[SH|[(f & Hf & SH)|(b & Hb & SH)]]]]]].
* apply EQ; [exact Ha|]. exact (NFPB b a Hb Hr').
* apply EQ; [exact Ha|]. rewrite HIeq in C1. unfold WL, art_malloc3L_fp. destruct Papp as (_ & Pap & _).
set (wlo := art_shlo r) in *. set (whi := art_shhi r msz) in *.
clear - C1 C2 C3 HS G1 G8 Hrm WOK Phi Dl2 Dblk Hnch. unfold apart in *. cbn [art_out fst snd]. destruct cm; repeat split; try exact I; lia.
* apply EQ; [exact Ha|]. rewrite HLlo in C1. rewrite HLhi in C2.
assert (NS : ~ art_zone_statics a) by (intros Z; apply C3; apply HLst; exact Z). unfold art_zone_statics in NS.
unfold WL, art_malloc3L_fp. set (wlo := art_shlo r) in *. set (whi := art_shhi r msz) in *.
clear - C1 C2 NS HS G1 G9 Hri WOK Plo Il2 Iblk Hnch. unfold apart in *. cbn [art_out fst snd]. destruct cm; repeat split; try exact I; lia.
* apply EQ; [exact Ha|]. destruct (FSIN f (in_or_app _ _ _ (or_introl Hf))) as (F1 & F2 & _).
unfold WL, art_malloc3L_fp. destruct Fapp as (_ & Fap & _). unfold BIGSHADOW_LO, BIGSHADOW_HI in Fap. set (wlo := art_shlo r) in *. set (whi := art_shhi r msz) in *.
clear - R1 F1 F2 HS G1 Fhi Fimg Aft Arf Fap WOK Afp Afl Afb Hnch. unfold apart, FS_BYTES in *. cbn [art_out fst snd]. destruct cm; repeat split; try exact I; lia.
* apply (SHEQ (ahl_ceil (rn_ar rn)) (2 ^ 47 - ahl_ceil (rn_ar rn))); [rewrite HIeq; lia|rewrite HIeq; lia|lia|rewrite HIeq; unfold apart; lia|exact SH|exact Ha|apply CSA1; exact SH].
* destruct (FSIN f (in_or_app _ _ _ (or_introl Hf))) as (F1 & F2 & F3).
apply (SHEQ (ff_addr f) (ff_bytes (ff_class f))); [lia|exact F3|unfold FS_BYTES in *; lia|unfold apart, FS_BYTES in *; clear - F1 F2 Arf; lia|exact SH|exact Ha|].
apply CSA2. destruct SH as (S1 & S2). unfold in_shadow_of. split.
-- eapply Z.le_trans; [apply (art_S_mono (ar_fs (rn_ar rn)) (ff_addr f)); lia|exact S1].
-- eapply Z.le_trans; [exact S2|apply art_S_mono; lia].
* destruct (CB b Hb) as (B1 & _ & _ & B4 & B5 & _ & _ & _ & B9 & _). rewrite HIeq in B5.
apply (SHEQ (fst b) (snd b)); [lia|exact B4|lia|exact (BLK b Hb)|exact SH|exact Ha|apply B9; exact SH].
+ intros a Ha. apply GRW. exact (SCR a Ha).
Qed.
End SE.
End ExitClient.
