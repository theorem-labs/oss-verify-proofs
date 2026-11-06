(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import PropExec CatExec CatSim SeqExec StepTac StoreOk Hoare WalkTac ShapeAlg SpinAlg AsanAcct HeapIface HeapIfaceA As0StepLib As0Tables
ArtMem ArtTac JatPoison JatInitCache JatPopulate1 ArtRuns ArtRunsMem JatCls JatFp JatClsRep JatClsGfa2 JatClsRefill JatCellEx JatByteCell JatCARSpec JatAlloc3Pure JatDepot JatUnwind
ArtBridge JatAllocate3 JatSecAllocPost JatSecRSpec JatAllocate3L JatMallocTop3L JatInv JatInvMallocPure JatInvMallocFp JatInvMalloc JatInvMallocL JatInvMallocLB JatLift JatWrapPure JatWrapKit
JatWrapMallocX JatWrapMallocH JatWrapMallocLA JatWrapMallocLX JatWrapMallocLC.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLia. Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLiaT.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import SecKit. From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__JatWrapMallocL () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Numbers.BinNums."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.ArtBridge."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.ArtMem."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.ArtRuns."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.AsanAcct."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.HeapIfaceA."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.JatAllocate3L."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.JatFp."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.JatInv."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.JatMallocTop3L."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.JatPoison."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.JatSecRSpec."; "Stdlib.Lists.List."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["0A"; "0A'"; "0BUDGET"; "1None"; "1app"; "1bool"; "1cons"; "1false"; "1length"; "1list"; "1nil"; "1option"; "1pair"; "1prod"; "2and"; "2eq"]; ["2not"; "2or"; "3Z"; "0FF"; "0LB"; "0LK"; "0M"; "0M1"; "0RES"; "4HSH_HI"; "4HSH_LO"; "4LSH_HI"; "4LSH_LO"; "4art_EVOK"; "4art_cost_sum"; "4art_live"]; ["4art_windows"; "4in_shadow_rw"; "5apart"; "6AMmapFixed"; "6AMmapFixedNR"; "6AMmapNull"; "6aev"; "6art_shhi"; "6art_shlo"; "7mkH"; "8FS_BYTES"; "8ar_fs"; "8fframe"; "8shadow_allowed"; "9art_sec_grant3"; ":art_out"]; [";KMAX"; ";LENMAX"; ";art_client_ok"; ";art_fs_zone"; ";art_run"; ";art_run_ok"; ";rn_HI"; ";rn_ar"; ";rn_blk"; ";rn_ctx"; ";rn_dtls"; ";rn_l2"; ";rn_parr"; ";rn_spb"; ";rn_t"; "<art_malloc3L_fp"]; ["=SB"; ">art_sec_events"; "0Sp"; "?In"; "@add"; "@div"; "@le"; "@lt"; "@modulo"; "@mul"; "@of_nat"; "@pow"; "@sub"; "0WL"; "0a"; "0cm"]; ["0l"; "0lazy"; "0len"; "0lin"; "0log"; "0msz"; "0n"; "0nch"; "0nd"; "0ov"; "0parr"; "0q"; "0qr"; "0qz"; "0r"; "0r'"]; ["0r0"; "0rn"; "0rs"; "0rz"; "Abv"; "Abv_unsigned"; "0u"; "0x"]]).
Local Ltac lia := L5FastLiaT.plia1.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
#[local] Abbreviation ASEGS := Asan.M.loaded_segments.
#[local] Abbreviation cellA := (cell Asan.M.loaded_segments).
#[local] Abbreviation wrA := (wr Asan.M.loaded_segments).
#[local] Notation "'U' r" := (bv_unsigned r) (at level 10, r at level 9).
Lemma art_sec_events_null : ltac2:(TCodec.tc2 tcn__JatWrapMallocL "N'B'5&R3'Q6(Q5r2r1%3221&R1r7r6r5r4r3%6554321%=3<81'>'?r8%23C61%33D?;%5221p071pV0G1pU6H1pU0H1pU@J1pUFK1pUNL1pU<M1").
Proof.
intros msz r parr nch cm len r' H. unfold art_sec_events in H. destruct H as [E|H]; [injection E as <- <-; split; reflexivity|].
destruct cm; [destruct H|]. destruct H as [E|[]]. discriminate E.
Qed.
Lemma art_sec_events_no_nr : ltac2:(TCodec.tc2 tcn__JatWrapMallocL "I'B'5&@&R3'Q6(Q4r2r1%3221&R1r7r6r5r4r3%6554321%=3<81%?11pU2B1pTNC1pU0C1pU@E1pUFF1pUNG1pU<H1").
Proof.
intros msz r parr nch cm a l H. unfold art_sec_events in H. destruct H as [E|H]; [discriminate E|].
destruct cm; [destruct H|]. destruct H as [E|[]]. discriminate E.
Qed.
Lemma art_sec_events_window : ltac2:(TCodec.tc2 tcn__JatWrapMallocL "Q1'9'Q6%211'B'5&R3'=%1244(<&Q8r4%211&Q7r5%2241%74<<41&Q0&4r6&R1r3r2r1%45:=321%73G61%911%E3C;1pU0G1pU@I1pUFJ1pUNK1pU<L1pU:N1").
Proof.
intros log msz r parr nch cm. unfold art_windows. rewrite flat_map_app. apply in_or_app. right. unfold art_sec_events. cbn [flat_map]. left. reflexivity.
Qed.
Lemma art_window_allowed : ltac2:(TCodec.tc2 tcn__JatWrapMallocL "QL'9'='B%2211%411&R3(<&Q8r4%211&Q7r3%2241%74;;41r5%:3<21&R6z%2214r6%421<&R7%125>&R4%125:r8r7%4221%<241r9%7215&R;+2+Q?%3221%C251'?&R9+8&R5r:%2213%5241%73Q913&Q=r=%2316Ap041p051p0>1p0F1p0M1p0Q01p0Q31p0Q71pU>QE1pV>QF1pU<QG1pUNQH1p4QG1").
Proof.
intros A' r msz u n Hin Hr Hu Hn Hun Hhi E1 E2 x (X1 & X2). unfold HeapIfaceA.S, HeapIfaceA.SB in X1, X2.
assert (D1 : r / 8 <= u / 8) by (apply Z.div_le_mono; lia).
assert (E3 : (r + msz) / 8 = r / 8 + msz / 8). { rewrite <- E1 at 1. rewrite <- E2 at 1. replace (8 * (r / 8) + 8 * (msz / 8)) with ((r / 8 + msz / 8) * 8) by lia. apply Z.div_mul. lia. }
assert (D2 : (u + n - 1) / 8 < (r + msz) / 8) by (apply Z.div_lt_upper_bound; lia).
assert (D0 : 0 <= r / 8) by (apply Z.div_pos; lia).
assert (D3 : (r + msz) / 8 <= 2 ^ 44) by (apply Z.div_le_upper_bound; lia).
set (lo := art_shlo r) in *. set (hi := art_shhi r msz) in *.
assert (Elo : exists a', lo = 4096 * a' /\ 4096 * a' <= r / 8 + 0x7fff8000).
{ exists ((r / 8 + 0x7fff8000) / 4096). unfold lo, art_shlo. split; [lia|]. apply Z.mul_div_le. lia. }
assert (Ehi : exists b', hi = 4096 * b' /\ (r + msz) / 8 + 0x7fff8000 <= 4096 * b').
{ exists (((r + msz) / 8 + 0x7fff8000 + 4095) / 4096). unfold hi, art_shhi. split; [lia|].
pose proof (Z.mul_succ_div_gt ((r + msz) / 8 + 0x7fff8000 + 4095) 4096 ltac:(lia)). lia. }
destruct Elo as (a' & Elo & La). destruct Ehi as (b' & Ehi & Lb).
assert (Rx : 0 <= x < 2 ^ 64) by lia.
assert (Ux : U (Z_to_bv 64 x : word) = x) by (apply art_u_lit; lia).
assert (PB : U (page_base (Z_to_bv 64 x)) = x / 4096 * 4096).
{ unfold page_base, page_base_of, page_size. rewrite Ux. apply art_u_lit. pose proof (Z.mul_div_le x 4096 ltac:(lia)). pose proof (Z.div_pos x 4096 ltac:(lia) ltac:(lia)). lia. }
unfold page_allowedb. apply existsb_exists. exists (lo, hi). split; [exact Hin|]. cbn [fst snd]. rewrite PB. unfold page_size.
pose proof (Z.mul_div_le x 4096 ltac:(lia)) as K1. pose proof (Z.mul_succ_div_gt x 4096 ltac:(lia)) as K2. set (k := x / 4096) in *.
apply andb_true_intro. split; apply Z.leb_le; lia.
Qed.
Lemma art_sec_evok1 : ltac2:(TCodec.tc2 tcn__JatWrapMallocL "QK'9'='B%2211%411'Q6%611&R7zr2%3221'?&R8r3+TP0%3221%53>18&R6r4&QA%3221&R:&8&Or6%211%42G1%611&Q@%F221&R4&Nr7%211&R5+8%22<1%72=1+XP0%9221%:271r8%I221&Mr:r9(Q5%12?G%5643MD71p071p0E1p0O1p0Q41p0Q;1pV2QD1pU<QE1pU:QB1p6QG1pQBQF1").
Proof.
intros RES BUDGET log msz r0 H1 H2 H3 H4 H5. unfold art_EVOK. split; [exact H1|]. split; [exact H2|]. split; [exact H3|]. split; [exact H4|].
rewrite art_cost_sum_snoc. cbn [art_cost]. lia.
Qed.
Lemma art_sec_evok2 : ltac2:(TCodec.tc2 tcn__JatWrapMallocL "R7'9'='B%2211%411'Q6%611&R3(<r1&R;+2+G%3221%64<<51r6%93=21'?&R8r2+TP0%3221z%63E21&R6r5%2241&R4&Nr7%211&R5+8%22B1%72C1+XP0%9221%:271+TPP0%<221r8%A221&Mr:r9&QA&Q@&4(6(Q5%12EQ3(:%11Q?%53Q@31%73QA>1(Q3&R9%12IQ3%O2Q11%421E%B6A@?>61p0D1p0Q41p0Q81p0Q@1pUFQO1pUNR01pU<R11pU:QN1p6R31pQBR21").
Proof.
intros RES BUDGET log msz r parr HR Hp Hm HB. unfold art_EVOK. rewrite Z.mul_0_r, Z.add_0_r. split; [exact Hp|]. split; [reflexivity|]. split; [lia|].
split. { exists (parr, 2 ^ 23). split; [exact HR|]. cbn [fst snd]. lia. }
rewrite !art_cost_sum_snoc. cbn [art_cost]. lia.
Qed.
Section ExitFs.
Section SE.
Local Abbreviation SEC_T_art_wmlc_fs := (ltac2:(TCodec.tc2 tcn__JatWrapMallocL "V>'QD'9'='B%2211%411&Q<%611'S4yR0%211%9211%;11';y8%711%311p071'5&QOr5&QNr=%211&QL%113r4r3r2&QK%118&QH%11:r1%?9>;9876421&QEr>%211&QBr?r<r;r9%5647E321&Q?&S5%12Q5=%32E1'?%81E%:1F%33Q321p051pV@Q;1'>&R6&Q8r8%211%421=&R7&Q7r7%2261%42B1%;261&@&R4&R0&R5+8%22M1%5241%L2R0Q=%C221%62B5%9241%A241%H241%=11&Q9r@%23Q;1QG(7%Q43R221%Q>1QK(3%11R8%Q83R831%G11%QC1R6%:1R7%Q<3R<21p041p0:1p0@1p0O1pV@RG1&Q1%11QE%R01R8%QE3RE1>%Q411p041pTNRN1&QFrC%211+TP0%Q:221&R<%12R63%QI231&R;+2+Q?%3221%QN2R=1z%R021R?+`P0%R22RA1%R4231&Q>rF%D11%S912&QI%114%S915&QM%117%S718%S619%;99865321RMRN&Q2&Q;&QGrG%211%411&Q:%74SHS621&QJrH%211%;4S>SL1Q6&R9%R?2S=R>%22R?1%S63TC1S?%RK2Q1R6'A&LrB%S311%S5231rA%S1241&K%S9221%S;251&J%S<218&I%S>271%S@231%?261&QCrN%221SL%K1T?rI%11TA%SN3TN31p051pV@U61p0:1p0K1p0M1p0N1p0Q31p0Q81p0QA1p0QN1p0R41p0R:1p0RC1p0RK1p0T81p0TC1p0TJ1tTLUKTN1pU0U?1pU<UO1pUNV01pU@V11pT6V21pQ@UE1pQ>UF1pU4UL1p2V41pQ<V31pQ8V41pQ:V71pV4V=1")) (only parsing).
Variable rn : ltac:(sec_ty2 constr:(SEC_T_art_wmlc_fs) 0%nat 0%nat).
Variable LB : ltac:(sec_ty2 constr:(SEC_T_art_wmlc_fs) 1%nat 0%nat).
Variable FF : ltac:(sec_ty2 constr:(SEC_T_art_wmlc_fs) 2%nat 0%nat).
Variable LK : ltac:(sec_ty2 constr:(SEC_T_art_wmlc_fs) 3%nat 0%nat).
Variable A : ltac:(sec_ty2 constr:(SEC_T_art_wmlc_fs) 4%nat 0%nat).
Variable lazy : ltac:(sec_ty2 constr:(SEC_T_art_wmlc_fs) 5%nat 0%nat).
Variable M : ltac:(sec_ty2 constr:(SEC_T_art_wmlc_fs) 6%nat 0%nat).
Variable M1 : ltac:(sec_ty2 constr:(SEC_T_art_wmlc_fs) 7%nat 0%nat).
Variable Sp : ltac:(sec_ty2 constr:(SEC_T_art_wmlc_fs) 8%nat 0%nat).
Variable nch : ltac:(sec_ty2 constr:(SEC_T_art_wmlc_fs) 9%nat 0%nat).
Variable r : ltac:(sec_ty2 constr:(SEC_T_art_wmlc_fs) 10%nat 0%nat).
Variable msz : ltac:(sec_ty2 constr:(SEC_T_art_wmlc_fs) 11%nat 0%nat).
Lemma art_wmlc_fs : ltac:(sec_stmt2 constr:(SEC_T_art_wmlc_fs) 12%nat 0%nat).
Proof using Type rn LB FF LK A lazy M M1 Sp nch r msz.
intros cm WL ROK CLI FRF FRW SHD HS HS47 Hnch GRANT Arf Ard E1 E2 Hmsz WOK x Z.
pose proof (art_run_ok_tail rn ROK) as (Il2 & Iblk & _ & D0 & D1 & D2 & D3 & _).
pose proof ROK as ROK'. rok_open ROK'. geo_open GEO.
destruct GRANT as ((Hr4 & Hr & Hri & Hrm & APr & Art & Arc & Arp) & Ark & Arl2 & Arblk).
destruct CLI as (CB & CND & CSA1 & CSA2 & CS1 & CS2 & CS3 & CS4 & CS5 & CS6 & CSI & CSP & CS16).
unfold appmem, JatPoison.SB, JatPoison.kHighMemBeg in APr. unfold LSH_LO, LSH_HI, HSH_LO, HSH_HI in WOK.
pose proof (u64_range x) as Rx.
assert (SHEQ : forall lo len, 0 <= lo -> 0 < len -> lo + len <= 2 ^ 47 -> apart r msz lo len -> in_shadow_of lo len (U x) ->
page_allowedb A (page_base x) = true -> M1 x = M x).
{ intros lo len Hlo Hlen Hhi AP SH AL.
pose proof (art_sh_apart r msz lo len (U x) E1 E2 Hlo Hlen AP SH) as NE.
destruct SH as (SH1 & SH2). pose proof (art_S_ge lo 0 ltac:(lia)) as B0. pose proof (art_S_lt (lo + len - 1) (2 ^ 44) ltac:(lia)) as B2.
destruct (Z_le_dec (art_shlo r) (U x)) as [L1|L1]; [destruct (Z_lt_dec (U x) (art_shhi r msz)) as [L2|L2]|].
- apply FRW; [(clear - L1 L2 msz r x; lia)|exact NE|apply art_allowed_vis; exact AL|apply SHD; unfold in_shadow_rw, LSH_LO, LSH_HI, HSH_LO, HSH_HI; (clear - B0 B2 CS1 CS6 D2 Flo Hmsz Hr L1 L2 Plo SH1 SH2 WOK len lo msz r rn x; lia)].
- apply FRF. unfold WL, art_malloc3L_fp. destruct Papp as (_ & Pap & _). unfold BIGSHADOW_LO, BIGSHADOW_HI in Pap.
set (wlo := art_shlo r) in *. set (whi := art_shhi r msz) in *.
clear - B0 B2 SH1 SH2 L2 HS G1 G10 APr Pap Al2s Abs Hnch. unfold apart in *. cbn [art_out fst snd]. destruct cm; repeat split; try exact I; lia.
- apply FRF. unfold WL, art_malloc3L_fp. destruct Papp as (_ & Pap & _). unfold BIGSHADOW_LO, BIGSHADOW_HI in Pap.
set (wlo := art_shlo r) in *. set (whi := art_shhi r msz) in *.
clear - B0 B2 SH1 SH2 L1 HS G1 G10 APr Pap Al2s Abs Hnch. unfold apart in *. cbn [art_out fst snd]. destruct cm; repeat split; try exact I; lia. }
assert (PBx : page_base x = page_base (Z_to_bv 64 (U x))) by (rewrite Z_to_bv_bv_unsigned; reflexivity).
destruct Z as [Z|[Z|[Z|[(Z & NS)|[Z|Z]]]]].
-
apply FRF. unfold WL, art_malloc3L_fp. destruct Fapp as (_ & Fap & _). unfold BIGSHADOW_LO, BIGSHADOW_HI in Fap. set (wlo := art_shlo r) in *. set (whi := art_shhi r msz) in *.
clear - Z HS G1 Fhi Fimg Aft Arf Fap WOK Afp Afl Afb Hnch. unfold apart, FS_BYTES in *. cbn [art_out fst snd]. destruct cm; repeat split; try exact I; lia.
-
apply FRF. apply (art_gap_out WL (U x) 1 (U x)); [|lia].
unfold WL, art_malloc3L_fp. destruct Papp as (_ & Pap & _). unfold BIGSHADOW_LO, BIGSHADOW_HI in Pap. set (wlo := art_shlo r) in *. set (whi := art_shhi r msz) in *.
clear - Z HS G1 G2 G4 G6 G7 G8 G9 G10 G11 Art WOK Apt Al2t Abt Hnch. unfold apart in *. cbn [art_gap fst snd]. unfold apart. destruct cm; repeat split; try exact I; lia.
-
apply (SHEQ (ar_fs (rn_ar rn)) FS_BYTES); [lia|unfold FS_BYTES; lia|unfold FS_BYTES in *; lia|exact Arf| |].
+ unfold in_shadow_of. pose proof (art_S_pred (ar_fs (rn_ar rn) + FS_BYTES)). lia.
+ rewrite PBx. apply CSA2. unfold in_shadow_of. pose proof (art_S_pred (ar_fs (rn_ar rn) + FS_BYTES)). lia.
-
apply FRF. unfold art_zone_statics in NS. unfold WL, art_malloc3L_fp. set (wlo := art_shlo r) in *. set (whi := art_shhi r msz) in *.
clear - Z NS HS G1 G9 Hri WOK Plo Il2 Iblk Hnch. unfold apart in *. cbn [art_out fst snd]. destruct cm; repeat split; try exact I; lia.
-
apply (SHEQ 0x10000 (0x691000 - 0x10000)); [lia|lia|lia|unfold apart; lia| |].
+ unfold in_shadow_of. pose proof (art_S_pred 0x691000). replace (0x10000 + (0x691000 - 0x10000) - 1) with (0x691000 - 1) by lia. lia.
+ rewrite PBx. apply CSI. unfold in_shadow_of. pose proof (art_S_pred 0x691000). replace (0x10000 + (0x691000 - 0x10000) - 1) with (0x691000 - 1) by lia. lia.
-
apply FRF. unfold WL, art_malloc3L_fp. destruct D3 as (_ & Dap & _). unfold BIGSHADOW_LO, BIGSHADOW_HI in Dap. set (wlo := art_shlo r) in *. set (whi := art_shhi r msz) in *.
pose proof (art_run_ok_tail rn ROK) as (_ & _ & _ & _ & _ & _ & _ & Adt & _ & _ & Adp & Adl & Adb & _).
clear - Z HS G1 D0 D1 D2 Dap Ard Adt Adp Adl Adb WOK Hnch. unfold apart in *. cbn [art_out fst snd]. destruct cm; repeat split; try exact I; lia.
Qed.
End SE.
End ExitFs.
Lemma art_mod4096_8 : ltac2:(TCodec.tc2 tcn__JatWrapMallocL "A'B'?&R8r1+TP0%3221z%63721&R9+8&R5r2%2213%5241%=3>13p081pUN@1").
Proof. intros r H. pose proof (Z.div_mod r 4096 ltac:(lia)) as D. rewrite H, Z.add_0_r in D. rewrite D at 1. replace (4096 * (r / 4096)) with ((512 * (r / 4096)) * 8) by lia. rewrite Z.div_mul by lia. lia. Qed.
Section SE.
Local Abbreviation SEC_T_art_rok_parr := (ltac2:(TCodec.tc2 tcn__JatWrapMallocL "Q5'QD&QEr1%211'>'?'B&R8&QLr2%211+TP0%5221z%93821&R6+VbTP0%2217&R4&R;+2+G%3221%52=1&QF%11@%;231+XPPP0%:231+Q?%;2:1%@231%L261%M2@1%N2D1p0Q01pV4Q41")) (only parsing).
Variable rn : ltac:(sec_ty2 constr:(SEC_T_art_rok_parr) 0%nat 0%nat).
Lemma art_rok_parr : ltac:(sec_stmt2 constr:(SEC_T_art_rok_parr) 1%nat 0%nat).
Proof.
intros ROK.
rok_open ROK. geo_open GEO. split; [exact Pal|]. split; [exact Plo|]. split; [exact Phi|exact G2]. Qed.
End SE.
Lemma art_sec_sizes : ltac2:(TCodec.tc2 tcn__JatWrapMallocL "SI'B'>&R6+8r:%3221&R;+2+K%3221%8261%:261'?&R9+@r9%3221%53A=1%@2;>+T0%B2@1%D231%92C7%;3GC1r>r;%H221&R4+7%2251%L251%N251&R7+RPP0r<%821;%4231r=r?%<221%=212%M3Q9@1+TP0&R<+1%22D1%Q1241%?21=%Q326G%Q?2?1%QA231%Q629A%I21:%Q93QEL1%QD2Q?M+D%QB2QA1%QG21Q0+RXP0%QI21Q3+`P0%Q22QD1%QL2Q61%QN241&R8%12Q9Gz%QG3R321&R5%12Q=R2%QI2R31%QK3R71Q?%Q=2Q@3+XP0%Q?221+TPP0%QA221+C%R82R71%QD231rE%R42Q<1%QG21Q@%RA241%QD2Q:4rD%QK2Q<1%QL217%RF21R0+Q0%RH215+RP0%RJ271%RL231%RM261%RN2;1%RO2=1%S02J1%S12O1%S22Q41p0Q;1p0Q?1p0QA1p0QE1p0QO1p0R51p0R;1p0RD1p0RG1p0RL1p0S31pUDS?1pU8S@1pU<SA1pUHSB1pUBSC1pUJSD1pV6SE1pULSF1pV8SG1pU>SH1").
Proof.
intros n rz qz rs qr nd q msz lin ov Hn Erz Hqz Ers Hrs Hsec End Hq Emsz Hlin Hov.
assert (Hm4 : msz mod 4096 = 0). { rewrite Emsz. replace (4096 * q + 4096) with ((q + 1) * 4096) by lia. apply Z_mod_mult. }
assert (Hm8 : msz / 8 = 512 * q + 512). { rewrite Emsz. replace (4096 * q + 4096) with ((512 * q + 512) * 8) by lia. apply Z.div_mul. lia. }
assert (Hl : 2 * n <= lin * n) by (apply Z.mul_le_mono_nonneg_r; lia).
split; [lia|]. split; [exact Hm4|]. split; [lia|]. split; [lia|]. split; [lia|]. split; lia.
Qed.
Section Wrap.
Variable FSG : Type.
Variable FSINV : art_run -> FSG -> list fframe -> list fframe -> (word -> option byte) -> Prop.
Variables MAPS0 RESV0 NOACC0 : list (word * word).
Variables BASE BUDGET : Z.
Variable rn : art_run.
Variable scfg : SpuriousCfg.
Variable L : asan_layout.
Hypothesis Halloc : sc_alloc scfg = false.
Hypothesis Hwx : wx_segs_nowrap ASEGS.
Hypothesis STATIC : bridge_static ASEGS MAPS0 RESV0 NOACC0 (art_RES rn) (rn_HI rn) BUDGET LENMAX KMAX.
Hypothesis HLsegs : hl_segs L = ASEGS.
Hypothesis HLmalloc : hl_malloc L = 0x78ec0.
Hypothesis HLscr : hl_scr_malloc L = 4096.
Hypothesis HLtp : hl_tp L = rn_tp rn.
Hypothesis HLlo : hl_img_lo L = 0x10000.
Hypothesis HLhi : hl_img_hi L = 0x691000.
Hypothesis HLst : forall a, art_zone_statics a -> hl_rt_static L a.
Hypothesis HLk : 3 <= hl_k_per_malloc L.
Hypothesis HLlin : 2 <= hl_b_lin L.
Hypothesis HLov : 2 ^ 20 <= hl_b_overhead L.
Hypothesis FSLAW : art_fsinv_frame_law FSG FSINV.
Hypothesis FS_IN : forall gfs FF LK M, FSINV rn gfs FF LK M ->
forall f, In f (FF ++ LK) -> ar_fs (rn_ar rn) <= ff_addr f /\ ff_addr f + ff_bytes (ff_class f) <= ar_fs (rn_ar rn) + FS_BYTES /\ 0 < ff_bytes (ff_class f).
Context {fx : PropExec.FPState}.
Section SE.
Variables (R : bvmap 5 word).
Variables (M : word -> option byte).
Variables (model : Model).
Variables (LB : list (Z * Z)).
Variables (FF LK : list fframe).
Variables (cr : credit).
Variables (A : list (Z * Z)).
Variables (n rl rz qz rs qr qn m8 nd q msz : Z).
Variables (K : ShapeAlg.TSet).
Theorem art_wrap_malloc_sec : art_ri_inv FSG MAPS0 RESV0 NOACC0 BASE BUDGET FSINV rn LB FF LK cr A M (vml_of model) -> m_halted model = None -> MInv A model ->
getr R 10 = Z_to_bv 64 n -> 8 <= n <= 2 ^ 27 ->
rl = AsanTab.rz_log n -> rz = 16 * 2 ^ rl -> rz = 16 * qz -> 2 <= qz <= 128 -> n = 8 * qn + m8 -> 0 <= m8 <= 7 -> rs = 8 * qr -> n <= rs <= n + 7 ->
65536 < rs + rz ->
nd = rs + rz + rz -> 4096 * (q - 1) < nd <= 4096 * q -> msz = 4096 * q + 4096 ->
acredit_ok L cr n -> getr R 4 = Z_to_bv 64 (hl_tp L) -> Hoare.ret_ok (getr R 1) ->
astack_ok L (rn_ar rn) M (hl_scr_malloc L) (U (getr R 2)) ->
amalloc_post L (rn_ar rn) scfg (art_iface FSG MAPS0 RESV0 NOACC0 BASE BUDGET FSINV rn) fx R M model LB FF LK cr A n K ->
srealizes ASEGS scfg (mkCfg (mkst R (0x78ec0 : word) M (seg_rom ASEGS)) model) K.
Proof using Halloc Hwx STATIC HLsegs HLscr HLtp HLlo HLhi HLst HLk HLlin HLov FSLAW FS_IN R M model LB FF LK cr A n rl rz qz rs qr qn m8 nd q msz K.
intros RI Hhalt HMI H10 Hn Erl Erz Erz16 Hqz En Hm8 Ers Hrs Hsec End Hq Emsz ACR H4 Hret AST POST.
destruct RI as (G & REPr & FS & BV & CRED & CLI & KN & LZ & EG). cbn [vml_of fst snd] in REPr, BV, LZ, EG.
pose proof (BINV_elim _ _ _ _ _ _ _ _ _ _ _ BV Hhalt HMI) as B0.
pose proof REPr as (ROK & _ & _ & _ & _ & SEC0 & _). destruct (art_rok_parr rn ROK) as (Pal & Plo & Phi & G2).
set (Sp := U (getr R 2)) in *. assert (H2 : getr R 2 = Z_to_bv 64 Sp) by (unfold Sp; symmetry; apply Z_to_bv_bv_unsigned).
rewrite HLscr in AST. destruct AST as (S16 & SHI & SLE & STOP & SWR & SDEF).
assert (HIeq : ahl_ceil (rn_ar rn) = rn_HI rn) by reflexivity. rewrite HIeq in SHI.
pose proof CLI as (_ & _ & _ & _ & CS1 & CS2 & CS3 & CS4 & CS5 & CS6 & _). rewrite HIeq in CS1, CS2.
pose proof CRED as (CR1 & CR2 & CR3 & CR4 & CR5 & CR6 & CR7 & CR8). destruct ACR as (AC1 & AC2).
destruct (g_depot FSG G) as [|kb] eqn:Edep; [exfalso; cbn in CR6; clear - CR6 AC1 HLk; lia|].
set (nch := Z.of_nat (length (g_sec FSG G))) in *. set (cm := g_sec_committed FSG G) in *.
destruct SEC0 as (_ & _ & _ & _ & _ & _ & CMT & _).
assert (Hnch0 : cm = false -> nch = 0).
{ intros E. unfold nch. destruct (g_sec FSG G) as [|s0 l0] eqn:Eg; [reflexivity|]. exfalso. unfold cm in E. rewrite CMT in E by discriminate. discriminate E. }
assert (Hnch : 0 <= nch /\ nch + 1 <= 16384) by (unfold nch; clear - CR5 AC1 HLk; lia).
destruct (art_sec_sizes n rz qz rs qr nd q msz (hl_b_lin L) (hl_b_overhead L) Hn Erz16 Hqz Ers Hrs Hsec End Hq Emsz HLlin HLov) as (Hmsz & Hm4 & E2 & Hcost & Hbig & Hfitm & Hrz).
assert (HS1 : rn_HI rn + 4096 <= Sp - 4096) by (clear - SHI; lia).
assert (HS2 : Sp <= 2 ^ 47) by (clear - SLE STOP; lia).
assert (HS3 : 0 <= ar_stack_bottom (rn_ar rn) /\ ar_stack_bottom (rn_ar rn) < ar_stack_top (rn_ar rn) /\ 4096 <= ar_stack_top (rn_ar rn) /\ ar_stack_top (rn_ar rn) < 2 ^ 63).
{ clear - CS1 CS2 CS3 CS4 CS5 G2 Phi Plo. lia. }
destruct HS3 as (Hbot0 & Hbt & Htop4 & Htop63).
pose proof (art_live_of_binv MAPS0 RESV0 NOACC0 BASE BUDGET rn _ _ _ _ B0 KN) as LIVE.
set (Mr0 := mrestrict (mkH (m_vm_lazy model) A) M) in *.
assert (W0 : wrA Mr0 (Sp - 4096) 4096). { apply (art_stack_wr FSG rn G A (m_vm_lazy model) M Sp 4096 ROK LZ ltac:(clear - HS1; lia) ltac:(clear; lia) ltac:(clear - HS2; lia)). rewrite <- HLsegs. exact SWR. }
assert (RD0 : readable8 Mr0 Sp (ar_stack_top (rn_ar rn))). { apply (art_stack_readable FSG rn G A (m_vm_lazy model) M Sp (ar_stack_top (rn_ar rn)) ROK LZ ltac:(clear - HS1; lia) ltac:(clear - Htop63 CS4; lia) SDEF). }
set (raw0 := getr R 1) in *.
assert (H4' : getr R 4 = Z_to_bv 64 (rn_tp rn)) by (rewrite <- HLtp; exact H4).
set (P := fun r : Z => art_GR (KN0 MAPS0 RESV0) (rn_HI rn) (g_log FSG G) Mr0 msz r).
assert (HP : forall r, P r -> art_sec_grant3 (rn_HI rn) (rn_t rn) (rn_ctx rn) (rn_parr rn) (rn_spb rn) (rn_l2 rn) (rn_blk rn) msz r
/\ (forall p, In p (art_live (g_log FSG G)) -> apart r msz (fst p) (snd p))
/\ apart r msz (ar_fs (rn_ar rn)) FS_BYTES /\ apart r msz (rn_dtls rn) 4096 /\ apart r msz (rn_kbase rn) 0x2000011000).
{ intros r Pr. exact (art_gr_grant MAPS0 RESV0 rn (g_log FSG G) Mr0 msz r ROK KN (proj1 Hmsz) Pr). }
set (Qm := fun (log' : list aev) (st : machine_state) =>
exists r regs' (Mr' : word -> option byte) b1, P r /\ st = mkst regs' raw0 Mr' (seg_rom ASEGS) /\ log' = g_log FSG G ++ art_sec_events msz r (rn_parr rn) nch cm
/\ getr regs' 10 = Z_to_bv 64 (4096 + r + rz) /\ getr regs' 2 = Z_to_bv 64 Sp
/\ (forall x : reg, In x [3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv -> getr regs' x = getr R x)
/\ art_malloc_out_sec rn Mr0 Mr' Sp n rz qz qn m8 nd msz r nch cm kb b1).
apply (aruns_srealizes_h ASEGS scfg Halloc Hwx MAPS0 RESV0 NOACC0 (art_RES rn) (rn_HI rn) BASE BUDGET LENMAX KMAX STATIC Qm K model A M model (g_log FSG G))
with (log := g_log FSG G) (s := restrict (bhid A model) (mkst R (0x78ec0 : word) M (seg_rom ASEGS))) (A := A) (model := model);
[ | | reflexivity | exact B0 | apply bmodel_rt_refl | apply bhist_refl ].
2: {
rewrite restrict_mkst. change (mrestrict (bhid A model) M) with Mr0.
eapply ar_steps; [apply art_malloc_thunk|].
apply (art_wm_entry_sec FSG _ _ Qm P (g_log FSG G) R Mr0 (seg_rom ASEGS) raw0 rn G LB Sp n rl rz qz rs qr qn m8 nd q msz (ar_stack_top (rn_ar rn)) (ar_stack_bottom (rn_ar rn)) kb
REPr eq_refl Hret H2 H4' H10 ltac:(clear - Hn; lia) Erl Erz Erz16 Hqz En Hm8 Ers Hrs Hsec End Hq Emsz HS1 HS2 S16 eq_refl eq_refl Hbot0 Hbt Htop4 Htop63
W0 RD0 Edep (proj2 Hnch)).
- intros Mx r GRr. exact GRr.
- intros r Pr. exact (proj1 (HP r Pr)).
- apply art_sec_evok1; [clear - Hmsz; lia|exact Hm4|unfold LENMAX; clear - Hmsz; lia|unfold KMAX in *; clear - CR4 AC1 HLk; lia|clear - CR3 AC2 Hcost; lia].
- intros Ecm r Pr. fold nch. rewrite (Hnch0 Ecm). apply art_sec_evok2; [right; left; reflexivity|exact Pal|clear - Hmsz; lia|clear - CR3 AC2 Hcost; lia].
- intros r regs' Mr' b1 Pr P10 P2 P1 PK OUT. exists r, regs', Mr', b1. split; [exact Pr|]. split; [reflexivity|]. split; [reflexivity|]. split; [exact P10|]. split; [exact P2|]. split; [exact PK|exact OUT]. }
intros log' A' ms' model' B1 RT BH (r & regs' & Mr' & b1 & Pr & Est & Elog & P10 & P2 & PK & OUT).
destruct (restrict_eq_mkst _ _ _ _ _ _ Est) as (Ems & EMr). set (M1 := ms_mem ms') in *. rewrite Ems. subst Mr'.
destruct (HP r Pr) as (GRANT & GLIVE & Arf & Ard & Arkb).
pose proof GRANT as ((Hr4 & Hr & Hri & Hrm & APr & _) & _).
assert (Hn28 : 8 <= n < 2 ^ 28) by (clear - Hn; lia).
pose proof (art_alloc_rep_malloc_sec FSG rn G LB Mr0 (mrestrict (bhid A' model') M1) Sp n rz qz rs qr qn m8 nd q msz r kb b1
REPr Hn28 Erz16 Hqz En Hm8 Ers Hrs Hsec End Hq Emsz HS1 Edep GRANT GLIVE OUT LIVE (proj2 Hnch)) as REP'.
pose proof (art_lrep_new_shadow FSG rn G LB Mr0 (mrestrict (bhid A' model') M1) Sp n rz qz rs qr qn m8 nd q msz r kb b1
REPr Hn28 Erz16 Hqz En Hm8 Ers Hrs Hsec End Hq Emsz HS1 Edep GRANT GLIVE OUT LIVE (proj2 Hnch)) as NSH.
pose proof (art_lrep_blocks_apart_r FSG rn G LB Mr0 rz msz r kb REPr Edep GRANT GLIVE) as BLK.
pose proof (art_lrep_nfp_block FSG rn G LB Mr0 Sp rz qz rs qr nd q msz r kb REPr Erz16 Hqz Ers Hsec End Hq Emsz HS1 Edep GRANT GLIVE LIVE) as NFPB.
fold nch in NFPB. fold cm in NFPB.
set (u := 4096 + r + rz) in *.
pose proof OUT as (GRW & AG & WIN & _ & WSr & _).
assert (OUTL : art_malloc_out_sec rn Mr0 (mrestrict (bhid A' model') M1) Sp n rz qz qn m8 nd msz r nch cm kb b1) by exact OUT.
destruct OUTL as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & WSp).
assert (WINA : In (art_shlo r, art_shhi r msz) A' /\ window_ok (art_shlo r, art_shhi r msz)).
{ apply (bi_windows _ _ _ _ _ _ _ _ _ _ _ B1). rewrite Elog. apply art_sec_events_window. }
destruct WINA as (WinA & (_ & _ & _ & WOK)). cbn [fst snd] in WOK.
assert (E1 : 8 * (r / 8) = r) by exact (art_mod4096_8 r Hr4).
destruct (art_wmlc_mem A A' M M1 model model' (g_log FSG G) log' Sp (rn_t rn) (rn_parr rn) nch r msz (rn_l2 rn) (rn_blk rn) cm Elog BH
(bi_shdef _ _ _ _ _ _ _ _ _ _ _ B1) WOK Plo ltac:(clear - Phi G2; lia) ltac:(clear - Hnch; lia) Hnch0 GRW AG WIN WSp) as (FRF & FRW & GRF & VISP).
pose proof BH as (sfx & Esfx & INC & BH2 & _ & BH4 & BH5).
assert (Esfx' : sfx = art_sec_events msz r (rn_parr rn) nch cm). { rewrite Elog in Esfx. apply app_inv_head in Esfx. symmetry. exact Esfx. }
assert (LZ' : art_lazy_ok FSG rn (art_gs_malloc_sec G (rn_parr rn) msz r u n kb) A' (m_vm_lazy model')).
{ apply (art_wmlx_lazy FSG rn G A (m_vm_lazy model) A' (m_vm_lazy model') msz r u n kb LZ INC).
- intros x Hx. exact (proj1 (BH2 x Hx)).
- intros wd Hwd. destruct (BH4 wd Hwd) as [Hin|(len & r' & Hev & Ew)]; [left; exact Hin|]. right. rewrite Esfx' in Hev.
destruct (art_sec_events_null _ _ _ _ _ _ _ Hev) as (-> & ->). exact Ew.
- unfold LSH_LO, LSH_HI, HSH_LO, HSH_HI in WOK. clear - WOK. lia.
- unfold LSH_LO, LSH_HI, HSH_LO, HSH_HI in WOK. clear - WOK. lia.
- intros x Hx. destruct (BH5 x Hx) as [Hl|(a & l & Hev & _)]; [exact Hl|]. exfalso. rewrite Esfx' in Hev. exact (art_sec_events_no_nr _ _ _ _ _ _ _ Hev).
- exact VISP. }
assert (Hu1 : r + 4096 <= u) by (unfold u; clear - Hrz; lia).
assert (Hu2 : u + n <= r + msz) by (unfold u; clear - Hfitm; lia).
assert (Hr64 : 0 <= r /\ r + msz < 2 ^ 63) by (clear - Hr Hrm G2; lia).
assert (Hu16 : u mod 16 = 0).
{ unfold u. pose proof (Z.div_mod r 4096 ltac:(clear; lia)) as D. rewrite Hr4, Z.add_0_r in D. rewrite D, Erz16.
replace (4096 + 4096 * (r / 4096) + 16 * qz) with ((256 + 256 * (r / 4096) + qz) * 16) by (clear; lia). apply Z_mod_mult. }
assert (DEFu : defined M1 u n).
{ intros i Hi. pose proof (art_wr_wview ASEGS (mrestrict (bhid A' model') M1) r msz ltac:(clear - Hr64; lia) ltac:(clear - Hr64; lia) WSr (Z_to_bv 64 (u + i))) as V.
rewrite art_u_lit in V by (clear - Hi Hu1 Hu2 Hr64; lia). specialize (V ltac:(clear - Hi Hu1 Hu2; lia)).
rewrite art_wview_off in V by (rewrite art_u_lit by (clear - Hi Hu1 Hu2 Hr64; lia); right; clear - Hi Hu1 Hri; lia). unfold mrestrict in V. destruct (bhid A' model' (Z_to_bv 64 (u + i))); [exfalso; apply V; reflexivity|exact V]. }
assert (SHu : shadow_blk M1 u n).
{ destruct NSH as (SHz & SHp).
split; [intros j Hj; exact (art_byte_unrestrict _ _ _ _ (SHz j Hj))|intros Hm; exact (art_byte_unrestrict _ _ _ _ (SHp Hm))]. }
assert (SAu : shadow_allowed A' u n) by (apply (art_window_allowed A' r msz u n WinA); first [exact E1|exact E2|exact Hu2|(clear - Hr64 Hu1 Hbig Hrm G2; lia)]).
assert (EG' : art_eager_ok ((u, n) :: LB) A' (m_vm_lazy model')).
{ pose proof GRANT as ((_ & _ & _ & _ & APr' & _ & _ & Arp') & _ & _ & Arblk').
apply (art_wmlx_eager FSG rn (art_gs_malloc_sec G (rn_parr rn) msz r u n kb) LB A (m_vm_lazy model) A' (m_vm_lazy model') msz r u n EG (bi_awf _ _ _ _ _ _ _ _ _ _ _ B1) LZ').
- intros x Hx. destruct (BH5 x Hx) as [Hl|(a & l & Hev & _)]; [exact Hl|]. exfalso. rewrite Esfx' in Hev. exact (art_sec_events_no_nr _ _ _ _ _ _ _ Hev).
- unfold appmem, JatPoison.SB, JatPoison.kHighMemBeg in APr'. clear - APr'. lia.
- exact Arblk'.
- exact Arkb.
- exact Arp'.
- clear - Hu1. lia.
- exact Hu2. }
assert (SCR : forall a, Sp - 4096 <= a < Sp -> M (Z_to_bv 64 a) <> None).
{ intros a Ha. assert (WM : wrA M (Sp - 4096) 4096) by (intros d k Hd Hk; rewrite <- HLsegs; apply SWR; assumption).
assert (Rs : 0x691000 <= Sp - 4096 /\ Sp < 2 ^ 63) by (clear - HS1 HS2 Phi Plo; lia).
pose proof (art_wr_wview ASEGS M (Sp - 4096) 4096 ltac:(clear - Rs; lia) ltac:(clear - Rs; lia) WM (Z_to_bv 64 a)) as V. rewrite art_u_lit in V by (clear - Rs Ha; lia). specialize (V ltac:(clear - Ha; lia)).
rewrite art_wview_off in V by (rewrite art_u_lit by (clear - Rs Ha; lia); right; clear - Rs Ha; lia). exact V. }
destruct (art_wmlc_client L HLlo HLhi HLst rn LB FF LK A A' (m_vm_lazy model) M M1 Sp nch r msz u n cm ROK CLI INC GRF FRF FRW
(bi_shdef _ _ _ _ _ _ _ _ _ _ _ B0) HS1 HS2 ltac:(clear - Hnch; lia) GRANT Arf E1 E2 ltac:(clear - Hmsz; lia) WOK BLK NFPB (FS_IN _ _ _ _ FS) SCR Hu1 Hu2 Hu16 Hbig DEFu SHu SAu)
as (CLI' & ABR & BA & FFA & AHP).
assert (RI' : art_ri_inv FSG MAPS0 RESV0 NOACC0 BASE BUDGET FSINV rn ((u, n) :: LB) FF LK (adebit L cr n) A' M1 (vml_of model')).
{ exists (art_gs_malloc_sec G (rn_parr rn) msz r u n kb). cbn [vml_of fst snd].
split; [exact REP'|]. split.
{ cbn [art_gs_malloc_sec g_fs]. apply (FSLAW rn (g_fs FSG G) FF LK M M1 FS GRF).
exact (art_wmlc_fs rn LB FF LK A (m_vm_lazy model) M M1 Sp nch r msz cm ROK CLI FRF FRW (bi_shdef _ _ _ _ _ _ _ _ _ _ _ B0) HS1 HS2 ltac:(clear - Hnch; lia)
GRANT Arf Ard E1 E2 ltac:(clear - Hmsz; lia) WOK). }
split. { cbn [art_gs_malloc_sec g_log]. fold nch. fold cm. pose proof B1 as B1'. rewrite Elog in B1'. exact (BINV_intro _ _ _ _ _ _ _ _ _ _ _ B1'). }
split. { unfold adebit. apply (art_wmlx_credit FSG BUDGET rn G LB cr msz r u n kb _ _ CRED Edep); [clear - Hmsz; lia|clear - AC1 HLk; lia|exact Hcost|exact AC2]. }
split; [exact CLI'|]. split; [exact KN|]. split; [exact LZ'|exact EG']. }
unfold amalloc_post in POST. rewrite <- HLsegs.
apply (POST regs' M1 model' A' u P10).
- apply art_kept_preserved; [rewrite P2, H2; reflexivity|exact PK].
- exact ABR.
- exact BA.
- exact FFA.
- exact DEFu.
- exact SHu.
- rewrite HLscr. exact AHP.
- exact RT.
- exact INC.
- exact (bi_minv _ _ _ _ _ _ _ _ _ _ _ B1).
- exact RI'.
Qed.
End SE.
End Wrap.
