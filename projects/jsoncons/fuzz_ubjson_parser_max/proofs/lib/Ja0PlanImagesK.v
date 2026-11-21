(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: decoded the 17 encoded lemma statements (Asan0_wx_nowrap, asan0_res_hull, segs_wr_of_forallb, etc.) into plain Rocq statements and added an n_resx/p_resx bound case to the asan0_img_facts proof; taken in part from projects/jsoncons/fuzz_bigint/proofs/lib/As0PlanImagesK.v, 23 lines within its lines 19-157. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import PropExec StoreOk AgentLib AsanAcct AxSymExec3K AsanPlanCoreK AsanPlanK AsanPlanSoundK AsanPlanSoundSumsK AsanHexScan AsanInitK.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Export Ja0DefsK.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require FxHexScan.
Import ListNotations.
Import AX2K. Import APCK. Import APK.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__Ja0PlanImagesK () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Lists.ListDef."; "Corelib.Numbers.BinNums."; "Corelib.Numbers.Cyclic.Int63.Uint63Axioms."; "Corelib.Strings.PrimString."; "LinuxProcessSemantics.LinuxProcessSem.MemImageType."; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics."; "LinuxProcessSemantics.LinuxProcessSem.Run."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.AsanAcct."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.AsanHexScan."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.AsanInitK."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.AsanPlanK.APK."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.AsanPlanSoundK.APSK."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.AsanPlanSoundSumsK.APSXK."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Ja0DefsK."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Ja0PlanImagesK."; "OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Asan."; "Stdlib.Lists.List."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["0A"; "1None"; "1bool"; "1cons"; "1false"; "1fst"; "1list"; "1negb"; "1nil"; "1option"; "1orb"; "1pair"; "1prod"; "1snd"; "1true"; "2and"]; ["2eq"; "2not"; "2or"; "3Forall"; "4N"; "4Z"; "5to_Z"; "6length"; "0H"; "0L"; "7Segment"; "7seg_readable"; "7seg_writable"; "8find_segment"; "8wview"; "9segments_reserved"]; [":H_off_segments"; ":mkH"; ":ranges_from_b"; ":segs_below_b"; ":wx_segs_nowrap"; ";scanN"; "<img_facts"; "=img_hi"; "=img_lo"; ">hull_ok"; ">in_hull"; ">in_ivs"; ">res_len_ok"; ">shadow_ok"; ">sum_sizes"; "?segs_wr_ok"]; ["@APH0"; "@ASAN0"; "@ASEGS0"; "AAsan0_top"; "Asegs_in_hull_b"; "BAsan_seg_bytes_002"; "BAsan_seg_bytes_003"; "BAsan_segment_000"; "BAsan_segment_001"; "BAsan_segment_002"; "BAsan_segment_003"; "Cforallb"; "Dadd"; "Ddiv"; "Dle"; "Dlt"]; ["Dto_N"; "0a"; "0hi"; "0iv"; "0lo"; "0m"; "0seg"; "0segs"; "EZ_to_bv"; "Ebv"; "Ebv_unsigned"; "0x"; "0z"]]).
Definition Asan0_top : Z := 0x691000.
Lemma Asan0_wx_nowrap : wx_segs_nowrap ASEGS0.
Proof. apply wx_segs_nowrap_of_b. vm_compute. reflexivity. Qed.
Lemma Asan0_segs_below : segs_below_b ASEGS0 Asan0_top = true.
Proof. vm_compute. reflexivity. Qed.
Lemma Asan0_H_off_above : forall H : word -> bool,
(forall a, H a = true -> (Asan0_top <= bv_unsigned a)%Z) -> H_off_segments ASEGS0 H.
Proof. intros H Ha. exact (H_off_segments_above _ H _ Asan0_segs_below Ha). Qed.
Lemma Asan0_H_off_mkH : forall L A, ranges_from_b L Asan0_top = true -> H_off_segments ASEGS0 (mkH L A).
Proof. intros L A HL. exact (H_off_segments_mkH _ L A _ Asan0_segs_below HL). Qed.
Definition segs_in_hull_b (segs : list Segment) (lo hi : Z) : bool :=
forallb (fun seg => (lo <=? Z.of_N (seg_base seg)) && (Z.of_N (seg_base seg) + Z.of_N (seg_size seg) <=? hi))%bool segs.
Lemma find_segment1_none_outside : forall segs lo hi x,
segs_in_hull_b segs lo hi = true -> (x < lo \/ hi <= x) -> find_segment segs x 1 = None.
Proof.
induction segs as [|s l IH]; intros lo hi x Hb Hx; [reflexivity|].
cbn [segs_in_hull_b forallb] in Hb. apply andb_true_iff in Hb as [Hs Hl].
apply andb_true_iff in Hs as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2.
cbn [find_segment].
replace (Z.leb (Z.of_N (seg_base s)) x && Z.leb (x + 1) (Z.of_N (seg_base s) + Z.of_N (seg_size s)))%bool with false.
- exact (IH lo hi x Hl Hx).
- symmetry. apply andb_false_iff. destruct Hx as [Hx|Hx]; [left | right]; apply Z.leb_gt; lia.
Qed.
Lemma asan0_segs_in_hull : segs_in_hull_b ASEGS0 (img_lo ASAN0) (img_hi ASAN0) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma asan0_in_hull : forall a : word,
APSK.in_hull ASAN0 (bv_unsigned a) = false -> find_segment ASEGS0 (bv_unsigned a) 1 = None.
Proof.
intros a H. apply (find_segment1_none_outside ASEGS0 (img_lo ASAN0) (img_hi ASAN0)); [exact asan0_segs_in_hull|].
unfold APSK.in_hull in H. apply andb_false_iff in H as [H|H]; [apply Z.leb_gt in H; left | apply Z.ltb_ge in H; right]; lia.
Qed.
Lemma asan0_res_len : APSK.res_len_ok ASEGS0 ASAN0.
Proof. vm_compute. reflexivity. Qed.
Lemma asan0_res_eq : ltac2:(TCodec.tc2 tcn__Ja0PlanImagesK "Q9'@'6'<'R9yR0%211%4211%611&O&QB%211(3(;&R8+RPP0%22;1+XPP0%42=1%64==31+ZPP0%72@1+k`P0%92B1%;4BB31+QU`P0%<2E1+QPP0%>2G1%@4GG31+QV`P0%A2J1+U[dP0%C2L1%E4LL31(8%11M%I3N31%J3O91%K3Q0?1%L3Q1E1%Q83Q1N1").
Proof. vm_compute. reflexivity. Qed.
Lemma asan0_res_hull : Forall (fun iv => img_lo ASAN0 <= bv_unsigned (fst iv) /\ bv_unsigned (fst iv) + bv_unsigned (snd iv) <= img_hi ASAN0) (segments_reserved ASEGS0).
Proof.
rewrite asan0_res_eq. cbn [img_lo img_hi ASAN0].
repeat constructor; cbn [fst snd]; rewrite ?u64_lit by lia; lia.
Qed.
Lemma asan0_hull_ok : APSK.hull_ok ASAN0.
Proof. unfold APSK.hull_ok. cbn [img_lo img_hi ASAN0]. unfold KHI. repeat split; reflexivity || lia. Qed.
Lemma asan0_shadow_ok : APSK.shadow_ok ASAN0.
Proof. unfold APSK.shadow_ok. cbn [shadow_off ASAN0]. lia. Qed.
Lemma asan0_res_sizes : ltac2:(TCodec.tc2 tcn__Ja0PlanImagesK "9'@'E&Q>&O&QB%211%411+V`TP0%83721").
Proof. vm_compute. reflexivity. Qed.
Lemma asan0_hex2 : ltac2:(TCodec.tc2 tcn__Ja0PlanImagesK ":'@'2&Q5&QEuR0wyQPP0%544321(>%93821").
Proof. apply FxHexScan.FXH.scan_ok; [vm_cast_no_check (@eq_refl bool true)|vm_compute; discriminate]. Qed.
Lemma asan0_hex3 : ltac2:(TCodec.tc2 tcn__Ja0PlanImagesK ":'@'2&Q5&QFuR0wyU[dP0%544321(>%93821").
Proof. apply FxHexScan.FXH.scan_ok; [vm_cast_no_check (@eq_refl bool true)|vm_compute; discriminate]. Qed.
Lemma asan0_len2 : ltac2:(TCodec.tc2 tcn__Ja0PlanImagesK ">'@'D&R0&QM&F&G&QE%211%411+2%7221%911yQPP0%=3<21").
Proof. vm_compute. reflexivity. Qed.
Lemma asan0_len3 : ltac2:(TCodec.tc2 tcn__Ja0PlanImagesK ">'@'D&R0&QM&F&G&QF%211%411+2%7221%911yU[dP0%=3<21").
Proof. vm_compute. reflexivity. Qed.
Lemma asan0_segs_eq : ASEGS0 = [Asan_segment_000; Asan_segment_001;
Asan_segment_002; Asan_segment_003].
Proof. reflexivity. Qed.
Lemma asan0_rw_window : ltac2:(TCodec.tc2 tcn__Ja0PlanImagesK "Q1'R9yR0%211'9y8%511%311p051'?&QN+QU`P0&R:r1%22<1%5241&QO+VbTP0%2241%:241&A'@&N&QBr3r2%43321(1%11F%83F31%:11p0<1pTHM1pT<I1").
Proof.
intros m x Hx. unfold wview. destruct (m x); [discriminate|].
destruct (find_segment ASEGS0 (bv_unsigned x) 1) as [seg|] eqn:Hf.
- apply find_segment_some_spec in Hf as (Hin & Hb & Ht).
rewrite asan0_segs_eq in Hin.
destruct Hin as [<-|[<-|[<-|[<-|[]]]]];
cbn [seg_base seg_size seg_writable seg_perms seg_bytes string_has Ascii.eqb
Asan_segment_000 Asan_segment_001
Asan_segment_002 Asan_segment_003] in Hb, Ht |- *.
+ exfalso. lia.
+ exfalso. lia.
+ cbn -[segment_byte_at]. apply (segment_byte_at_some1 _ 32768); [exact asan0_hex2 | rewrite asan0_len2; lia | rewrite Z2N.id by lia; cbn in Hb, Ht; lia].
+ cbn -[segment_byte_at]. apply (segment_byte_at_some1 _ 5623808); [exact asan0_hex3 | rewrite asan0_len3; lia | rewrite Z2N.id by lia; cbn in Hb, Ht; lia].
- exfalso. destruct (Z.lt_ge_cases (bv_unsigned x) 0x134000) as [Hl|Hl].
+ apply (find_segment_none_spec _ _ _ Hf Asan_segment_002);
[rewrite asan0_segs_eq; cbn; tauto | cbn; lia].
+ apply (find_segment_none_spec _ _ _ Hf Asan_segment_003);
[rewrite asan0_segs_eq; cbn; tauto | cbn; lia].
Qed.
Lemma asan0_hull_tiled : forall z, img_lo ASAN0 <= z < img_hi ASAN0 -> APSK.in_ivs z (segments_reserved ASEGS0) = true.
Proof.
intros z Hz. cbn [img_lo img_hi ASAN0] in Hz. rewrite asan0_res_eq. unfold APSK.in_ivs. cbn [existsb fst snd].
rewrite !u64_lit by lia.
destruct (Z.lt_ge_cases z 0x50000) as [H1|H1].
{ apply orb_true_iff. left. apply andb_true_iff. split; [apply Z.leb_le | apply Z.ltb_lt]; lia. }
apply orb_true_iff. right.
destruct (Z.lt_ge_cases z 0x12c000) as [H2|H2].
{ apply orb_true_iff. left. apply andb_true_iff. split; [apply Z.leb_le | apply Z.ltb_lt]; lia. }
apply orb_true_iff. right.
destruct (Z.lt_ge_cases z 0x134000) as [H3|H3].
{ apply orb_true_iff. left. apply andb_true_iff. split; [apply Z.leb_le | apply Z.ltb_lt]; lia. }
apply orb_true_iff. right.
apply orb_true_iff. left. apply andb_true_iff. split; [apply Z.leb_le | apply Z.ltb_lt]; lia.
Qed.
Lemma asan0_hull_lt : img_lo ASAN0 < img_hi ASAN0.
Proof. cbn [img_lo img_hi ASAN0]. lia. Qed.
Lemma segs_wr_of_forallb : forall segs,
forallb (fun seg => negb (seg_writable seg) || seg_readable seg)%bool segs = true -> APSXK.segs_wr_ok segs.
Proof.
intros segs H seg Hin Hw. pose proof (proj1 (forallb_forall _ _) H seg Hin) as Hs. cbn beta in Hs.
rewrite Hw in Hs. exact Hs.
Qed.
Lemma asan0_segs_wr : APSXK.segs_wr_ok ASEGS0.
Proof. apply segs_wr_of_forallb. vm_compute. reflexivity. Qed.
Lemma asan0_img_facts : img_facts ASEGS0 ASAN0 APH0.
Proof.
constructor.
- repeat split; reflexivity.
- cbn [img_lo img_hi ASAN0]. lia.
- vm_compute. reflexivity.
- exact asan0_res_hull.
- rewrite asan0_res_sizes. reflexivity.
- cbn [rw_lo rw_len ASAN0]. split; [lia|]. intros m x Hx. apply asan0_rw_window. lia.
- exact asan0_shadow_ok.
- cbn [n_resx p_resx ASAN0]. split; lia.
Qed.
