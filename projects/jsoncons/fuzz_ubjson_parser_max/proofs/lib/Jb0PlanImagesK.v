(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import PropExec StoreOk AgentLib AsanAcct AxSymExec3K AsanPlanCoreK AsanPlanK AsanPlanSoundK AsanPlanSoundSumsK AsanHexScan AsanInitK.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Export Jb0DefsK.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require FxHexScan.
Import ListNotations.
Import AX2K. Import APCK. Import APK.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__Jb0PlanImagesK () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Lists.ListDef."; "Corelib.Numbers.BinNums."; "Corelib.Numbers.Cyclic.Int63.Uint63Axioms."; "Corelib.Strings.PrimString."; "LinuxProcessSemantics.LinuxProcessSem.MemImageType."; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics."; "LinuxProcessSemantics.LinuxProcessSem.Run."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.AsanAcct."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.AsanHexScan."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.AsanInitK."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.AsanPlanK.APK."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.AsanPlanSoundK.APSK."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.AsanPlanSoundSumsK.APSXK."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Jb0DefsK."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Jb0PlanImagesK."; "OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.AsanUbsan."; "Stdlib.Lists.List."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["0A"; "1None"; "1bool"; "1cons"; "1false"; "1fst"; "1list"; "1negb"; "1nil"; "1option"; "1orb"; "1pair"; "1prod"; "1snd"; "1true"; "2and"]; ["2eq"; "2not"; "2or"; "3Forall"; "4N"; "4Z"; "5to_Z"; "6length"; "0H"; "0L"; "7Segment"; "7seg_readable"; "7seg_writable"; "8find_segment"; "8wview"; "9segments_reserved"]; [":H_off_segments"; ":mkH"; ":ranges_from_b"; ":segs_below_b"; ":wx_segs_nowrap"; ";scanN"; "<img_facts"; "=img_hi"; "=img_lo"; ">hull_ok"; ">in_hull"; ">in_ivs"; ">res_len_ok"; ">shadow_ok"; ">sum_sizes"; "?segs_wr_ok"]; ["@APH0"; "@ASAN0"; "@ASEGS0"; "AAsan0_top"; "Asegs_in_hull_b"; "BAsanUbsan_seg_bytes_002"; "BAsanUbsan_seg_bytes_003"; "BAsanUbsan_segment_000"; "BAsanUbsan_segment_001"; "BAsanUbsan_segment_002"; "BAsanUbsan_segment_003"; "Cforallb"; "Dadd"; "Ddiv"; "Dle"; "Dlt"]; ["Dto_N"; "0a"; "0hi"; "0iv"; "0lo"; "0m"; "0seg"; "0segs"; "EZ_to_bv"; "Ebv"; "Ebv_unsigned"; "0x"; "0z"]]).
Definition Asan0_top : Z := 0x693000.
Lemma Asan0_wx_nowrap : ltac2:(TCodec.tc2 tcn__Jb0PlanImagesK "3&Q4&QB%211").
Proof. apply wx_segs_nowrap_of_b. vm_compute. reflexivity. Qed.
Lemma Asan0_segs_below : ltac2:(TCodec.tc2 tcn__Jb0PlanImagesK "8'@'2&Q3&QB&QC%3221(>%73621").
Proof. vm_compute. reflexivity. Qed.
Lemma Asan0_H_off_above : ltac2:(TCodec.tc2 tcn__Jb0PlanImagesK "G'R9yR0%211'2p021'@r2r1%211(>%53721&QN&QC&R:%12=8%4231p061pT4?1&Q0&QB%221>p041pQBB1").
Proof. intros H Ha. exact (H_off_segments_above _ H _ Asan0_segs_below Ha). Qed.
Lemma Asan0_H_off_mkH : ltac2:(TCodec.tc2 tcn__Jb0PlanImagesK "K'6'<'R9yR0%211%4211%611'E%7211%911'@'2&Q2r2&QC%3221(>%73621&Q0&QB&Q1r3%2219%5241p071p2@1pQDD1").
Proof. intros L A HL. exact (H_off_segments_mkH _ L A _ Asan0_segs_below HL). Qed.
Definition segs_in_hull_b (segs : list Segment) (lo hi : Z) : bool :=
forallb (fun seg => (lo <=? Z.of_N (seg_base seg)) && (Z.of_N (seg_base seg) + Z.of_N (seg_size seg) <=? hi))%bool segs.
Lemma find_segment1_none_outside : ltac2:(TCodec.tc2 tcn__Jb0PlanImagesK "Q2'6'J%211'E'@'2&QDr4r3r2%43321(>%83721'B&QO%1268&QN%1298%5231'9%11C&Mr6+1%332@1(1%11I%G3731p0:1p0A1pTHK1pT6L1pT:M1pT@O1").
Proof.
induction segs as [|s l IH]; intros lo hi x Hb Hx; [reflexivity|].
cbn [segs_in_hull_b forallb] in Hb. apply andb_true_iff in Hb as [Hs Hl].
apply andb_true_iff in Hs as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2.
cbn [find_segment].
replace (Z.leb (Z.of_N (seg_base s)) x && Z.leb (x + 1) (Z.of_N (seg_base s) + Z.of_N (seg_size s)))%bool with false.
- exact (IH lo hi x Hl Hx).
- symmetry. apply andb_false_iff. destruct Hx as [Hx|Hx]; [left | right]; apply Z.leb_gt; lia.
Qed.
Lemma asan0_segs_in_hull : ltac2:(TCodec.tc2 tcn__Jb0PlanImagesK "<'@'2&QD&QB&Q8&QA%211&Q7%113%73631(>%;3:21").
Proof. vm_compute. reflexivity. Qed.
Lemma asan0_in_hull : ltac2:(TCodec.tc2 tcn__Jb0PlanImagesK "K'R9yR0%211'@'2&Q:&QA&R:r1%2281%5241(4%93821'9'J%211&M&QBr2%<2B1+1%53421(1%119%E3931p0=1pT4H1").
Proof.
intros a H. apply (find_segment1_none_outside ASEGS0 (img_lo ASAN0) (img_hi ASAN0)); [exact asan0_segs_in_hull|].
unfold APSK.in_hull in H. apply andb_false_iff in H as [H|H]; [apply Z.leb_gt in H; left | apply Z.ltb_ge in H; right]; lia.
Qed.
Lemma asan0_res_len : ltac2:(TCodec.tc2 tcn__Jb0PlanImagesK "4&Q<&QB&QA%3221").
Proof. vm_compute. reflexivity. Qed.
Lemma asan0_res_eq : ltac2:(TCodec.tc2 tcn__Jb0PlanImagesK "Q9'@'6'<'R9yR0%211%4211%611&O&QB%211(3(;&R8+RPP0%22;1+XPP0%42=1%64==31+ZPP0%72@1+khP0%92B1%;4BB31+QUhP0%<2E1+QPP0%>2G1%@4GG31+QVhP0%A2J1+U[dP0%C2L1%E4LL31(8%11M%I3N31%J3O91%K3Q0?1%L3Q1E1%Q83Q1N1").
Proof. vm_compute. reflexivity. Qed.
Lemma asan0_res_hull : ltac2:(TCodec.tc2 tcn__Jb0PlanImagesK "O'C'<'R9yR0%211%4211'?&QN&Q8&QA%211&R:&5r1%23::1%42<1%9261&QL&=%13??6%92A1%4261&Q7%11>%A231%C291qT8E1&O&QB%211%N3I41").
Proof.
rewrite asan0_res_eq. cbn [img_lo img_hi ASAN0].
repeat constructor; cbn [fst snd]; rewrite ?u64_lit by lia; lia.
Qed.
Lemma asan0_hull_ok : ltac2:(TCodec.tc2 tcn__Jb0PlanImagesK "3&Q9&QA%211").
Proof. unfold APSK.hull_ok. cbn [img_lo img_hi ASAN0]. unfold KHI. repeat split; reflexivity || lia. Qed.
Lemma asan0_shadow_ok : ltac2:(TCodec.tc2 tcn__Jb0PlanImagesK "3&Q=&QA%211").
Proof. unfold APSK.shadow_ok. cbn [shadow_off ASAN0]. lia. Qed.
Lemma asan0_res_sizes : ltac2:(TCodec.tc2 tcn__Jb0PlanImagesK "9'@'E&Q>&O&QB%211%411+V`\P0%83721").
Proof. vm_compute. reflexivity. Qed.
Lemma asan0_hex2 : ltac2:(TCodec.tc2 tcn__Jb0PlanImagesK ":'@'2&Q5&QEuR0wyQPP0%544321(>%93821").
Proof. apply FxHexScan.FXH.scan_ok; [vm_cast_no_check (@eq_refl bool true)|vm_compute; discriminate]. Qed.
Lemma asan0_hex3 : ltac2:(TCodec.tc2 tcn__Jb0PlanImagesK ":'@'2&Q5&QFuR0wyU[dP0%544321(>%93821").
Proof. apply FxHexScan.FXH.scan_ok; [vm_cast_no_check (@eq_refl bool true)|vm_compute; discriminate]. Qed.
Lemma asan0_len2 : ltac2:(TCodec.tc2 tcn__Jb0PlanImagesK ">'@'D&R0&QM&F&G&QE%211%411+2%7221%911yQPP0%=3<21").
Proof. vm_compute. reflexivity. Qed.
Lemma asan0_len3 : ltac2:(TCodec.tc2 tcn__Jb0PlanImagesK ">'@'D&R0&QM&F&G&QF%211%411+2%7221%911yU[dP0%=3<21").
Proof. vm_compute. reflexivity. Qed.
Lemma asan0_segs_eq : ltac2:(TCodec.tc2 tcn__Jb0PlanImagesK "A'@'6'J%211&QB(3&QG&QH&QI&QJ(8%119%73:31%83;51%93<71%:3=91%@3=<1").
Proof. reflexivity. Qed.
Lemma asan0_rw_window : ltac2:(TCodec.tc2 tcn__Jb0PlanImagesK "Q1'R9yR0%211'9y8%511%311p051'?&QN+QUhP0&R:r1%22<1%5241&QO+Vb\P0%2241%:241&A'@&N&QBr3r2%43321(1%11F%83F31%:11p0<1pTHM1pT<I1").
Proof.
intros m x Hx. unfold wview. destruct (m x); [discriminate|].
destruct (find_segment ASEGS0 (bv_unsigned x) 1) as [seg|] eqn:Hf.
- apply find_segment_some_spec in Hf as (Hin & Hb & Ht).
rewrite asan0_segs_eq in Hin.
destruct Hin as [<-|[<-|[<-|[<-|[]]]]];
cbn [seg_base seg_size seg_writable seg_perms seg_bytes string_has Ascii.eqb
AsanUbsan_segment_000 AsanUbsan_segment_001
AsanUbsan_segment_002 AsanUbsan_segment_003] in Hb, Ht |- *.
+ exfalso. lia.
+ exfalso. lia.
+ cbn -[segment_byte_at]. apply (segment_byte_at_some1 _ 32768); [exact asan0_hex2 | rewrite asan0_len2; lia | rewrite Z2N.id by lia; cbn in Hb, Ht; lia].
+ cbn -[segment_byte_at]. apply (segment_byte_at_some1 _ 5623808); [exact asan0_hex3 | rewrite asan0_len3; lia | rewrite Z2N.id by lia; cbn in Hb, Ht; lia].
- exfalso. destruct (Z.lt_ge_cases (bv_unsigned x) 0x136000) as [Hl|Hl].
+ apply (find_segment_none_spec _ _ _ Hf AsanUbsan_segment_002);
[rewrite asan0_segs_eq; cbn; tauto | cbn; lia].
+ apply (find_segment_none_spec _ _ _ Hf AsanUbsan_segment_003);
[rewrite asan0_segs_eq; cbn; tauto | cbn; lia].
Qed.
Lemma asan0_hull_tiled : ltac2:(TCodec.tc2 tcn__Jb0PlanImagesK "I'E'?&QN&Q8&QA%211r1%5221&QO&Q7%116%3251%;251'@'2&Q;r2&O&QB%211%5241(>%93821p0;1pTJH1").
Proof.
intros z Hz. cbn [img_lo img_hi ASAN0] in Hz. rewrite asan0_res_eq. unfold APSK.in_ivs. cbn [existsb fst snd].
rewrite !u64_lit by lia.
destruct (Z.lt_ge_cases z 0x50000) as [H1|H1].
{ apply orb_true_iff. left. apply andb_true_iff. split; [apply Z.leb_le | apply Z.ltb_lt]; lia. }
apply orb_true_iff. right.
destruct (Z.lt_ge_cases z 0x12e000) as [H2|H2].
{ apply orb_true_iff. left. apply andb_true_iff. split; [apply Z.leb_le | apply Z.ltb_lt]; lia. }
apply orb_true_iff. right.
destruct (Z.lt_ge_cases z 0x136000) as [H3|H3].
{ apply orb_true_iff. left. apply andb_true_iff. split; [apply Z.leb_le | apply Z.ltb_lt]; lia. }
apply orb_true_iff. right.
apply orb_true_iff. left. apply andb_true_iff. split; [apply Z.leb_le | apply Z.ltb_lt]; lia.
Qed.
Lemma asan0_hull_lt : ltac2:(TCodec.tc2 tcn__Jb0PlanImagesK "7&QO&Q8&QA%211&Q7%113%6231").
Proof. cbn [img_lo img_hi ASAN0]. lia. Qed.
Lemma segs_wr_of_forallb : ltac2:(TCodec.tc2 tcn__Jb0PlanImagesK "H'6'J%211'@'2&QK&:&7&Lr1%211%411&K%114%8231qT>>1%;3?17(>%?3>21&Q?r2%211p041pT@E1").
Proof.
intros segs H seg Hin Hw. pose proof (proj1 (forallb_forall _ _) H seg Hin) as Hs. cbn beta in Hs.
rewrite Hw in Hs. exact Hs.
Qed.
Lemma asan0_segs_wr : ltac2:(TCodec.tc2 tcn__Jb0PlanImagesK "3&Q?&QB%211").
Proof. apply segs_wr_of_forallb. vm_compute. reflexivity. Qed.
Lemma asan0_img_facts : ltac2:(TCodec.tc2 tcn__Jb0PlanImagesK "5'Q6&QB&QA&Q@%43321").
Proof.
constructor.
- repeat split; reflexivity.
- cbn [img_lo img_hi ASAN0]. lia.
- vm_compute. reflexivity.
- exact asan0_res_hull.
- rewrite asan0_res_sizes. reflexivity.
- cbn [rw_lo rw_len ASAN0]. split; [lia|]. intros m x Hx. apply asan0_rw_window. lia.
- exact asan0_shadow_ok.
Qed.
