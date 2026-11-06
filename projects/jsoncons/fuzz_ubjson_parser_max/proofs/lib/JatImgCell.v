(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import PropExec CatSim StoreOk StreamSim AsanPlanSoundSums ArtMem ArtRuns ArtRunsMem JatCellEx.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__JatImgCell () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Init.Peano."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.LinuxProcessSem.MemImageType."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.ArtMem."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.JatImgCell."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.StreamSim."; "OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Asan.M."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["1None"; "1Some"; "1bool"; "1length"; "1list"; "1nat"; "1option"; "1true"; "2I"; "2and"; "2eq"; "2ex"; "2not"; "2or"; "3le"; "4Z"]; ["5Segment"; "0M"; "6cell"; "6wr"; "7art_rseg_ok"; "8rdn"; "8seg_rom"; "9wseg_ok"; ":loaded_segments"; ";add"; ";le"; ";lt"; ";mul"; ";of_nat"; ";pow"; "0a"]; ["0bs"; "0n"; "0segs"; "<BV"; "<Z_to_bv"; "<bv"; "<bv_add"; "<bv_unsigned"; "0v"; "0x"]]).
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
#[local] Abbreviation ASEGS := Asan.M.loaded_segments.
#[local] Abbreviation cellA := (cell Asan.M.loaded_segments).
#[local] Abbreviation wrA := (wr Asan.M.loaded_segments).
#[local] Notation "'U' r" := (bv_unsigned r) (at level 10, r at level 9).
Fixpoint art_rseg_ok (segs : list Segment) (a : word) (n : nat) : bool :=
match n with
| O => true
| S n' => match seg_rom segs a with Some _ => art_rseg_ok segs (a + 1)%bv n' | None => false end
end.
Lemma art_bv_succ : ltac2:(TCodec.tc2 tcn__JatImgCell "M'Q5yR0%211&K&I&Q7r1%2261+1%5221&N+2+R0%3221%;251':'?&Q6r2(Q3(8%23D=1%53E41%B2F1%C2G6%E21A%;3:31p0=1pR0J1").
Proof.
intros a H. rewrite bv_add_unsigned. change (bv_unsigned (1 : bv 64)%bv) with 1. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
pose proof (bv_unsigned_in_range 64 a) as R. change (bv_modulus 64) with (2 ^ 64) in R. rewrite Z.mod_small by lia. reflexivity.
Qed.
Lemma art_rseg_pt : ltac2:(TCodec.tc2 tcn__JatImgCell "QI'4'@%211'5'Q5yR0%211&K&I&Q7r1%2261&Mr2%211%7241&N+2+R0%3221%=251':'2&Dr4r3%332=1(7%73621'9&J%F2J7%221Er5%F11%K241%M2I1%8251&<'6y8%Q511%311&Fr7%221Q0(0%116%K3631%;11p0=1pRDQ=1p0H1p0Q11pR0Q@1pR4QD1pR6QF1").
Proof.
induction n as [|n IH]; intros a Hn OK x Hx; [lia|].
cbn [art_rseg_ok] in OK. destruct (seg_rom segs a) as [b|] eqn:E; [|discriminate].
destruct (Z.eq_dec (U x) (U a)) as [Ex|Nx].
- apply bv_eq in Ex. subst x. rewrite E. discriminate.
- apply (IH (a + 1)%bv); [rewrite art_bv_succ by lia; lia | exact OK | rewrite art_bv_succ by lia; lia].
Qed.
Lemma art_rdn_defined_v : ltac2:(TCodec.tc2 tcn__JatImgCell "R<'5'Q5yR0%211'6y8%511%311p051'?&Jzr1%3221&K&Ir2&Mr4%211%5241&N+2+R0%3221%;251'9&Q7%12J@%C2;1r6%>11%A2>1%C251%8251'=&<':%81F(0%11Q2%43Q231%611&F&H%221M%93Q716%;11%=261p0?1pRDQ?1';'4%11Q?%QB11&E&Q4r5%22QH1r7%54@N21(1%129QB%J3931&3%12QKQE%M3R217%Q9241qR2?1%B2@1p0D1p0Q>1p0QK1pR0R01pQ4R21pR4R;1").
Proof.
induction n as [|n IH]; intros M a Ha Hn D; [exists []; split; reflexivity|].
cbn [rdn]. assert (Ua : U (Z_to_bv 64 a : word) = a) by (apply art_u_lit; lia).
assert (exists b, match M (Z_to_bv 64 a) with Some b => Some b | None => seg_rom ASEGS (Z_to_bv 64 a) end = Some b) as (b & Eb).
{ destruct (D (Z_to_bv 64 a) ltac:(rewrite Ua; lia)) as [N|N].
- destruct (M (Z_to_bv 64 a)) as [b|]; [exists b; reflexivity|congruence].
- destruct (M (Z_to_bv 64 a)) as [b|]; [exists b; reflexivity|]. destruct (seg_rom ASEGS (Z_to_bv 64 a)) as [b|]; [exists b; reflexivity|congruence]. }
rewrite Eb.
replace ((Z_to_bv 64 a + 1)%bv : word) with (Z_to_bv 64 (a + 1) : word).
2:{ apply bv_eq. rewrite bv_add_unsigned, Ua. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
change (bv_unsigned (1 : bv 64)%bv) with 1. rewrite !Z.mod_small by lia. reflexivity. }
destruct (IH M (a + 1) ltac:(lia) ltac:(lia) ltac:(intros x Hx; apply D; lia)) as (bs & R & Lb).
rewrite R. exists (b :: bs). split; [reflexivity|cbn; lia].
Qed.
Lemma art_rseg_secwin : ltac2:(TCodec.tc2 tcn__JatImgCell "<':'2&D&H&Q4yR0+QVmfH%3221uQP0%73621(7%;3:21").
Proof. vm_compute. reflexivity. Qed.
Lemma art_wseg_secwin : ltac2:(TCodec.tc2 tcn__JatImgCell "<':'2&G&H&Q4yR0+QVmfH%3221uQP0%73621(7%;3:21").
Proof. vm_compute. reflexivity. Qed.
Lemma art_img_cell_exists : ltac2:(TCodec.tc2 tcn__JatImgCell "QG'Q5yR0%211'6y8%511%311p051'?'5'>r1u8%3221&J+QVmfHr3%3221&Ir4&M%115%4231+QP0%6291%;231';'9z%?21B&K&N+2&L+8r5%@11%4231%7261%92L1%=2;1&B&Hr7r6%45321:Q2%C261qRBQ71%F2Q81p0H1p0Q11p0Q61pR4Q;1pR0Q=1pQ4Q?1").
Proof.
intros M a n Hn8 Ha Hn.
destruct (art_rdn_defined_v n M a ltac:(lia) ltac:(lia)) as (bs & R & Lb).
{ intros x Hx. right. apply (art_rseg_pt ASEGS 1024 (Z_to_bv 64 0x1376d8)); [rewrite art_u_lit by lia; lia | exact art_rseg_secwin | rewrite art_u_lit by lia; lia]. }
exists (bytes_le_to_Z bs). split.
- pose proof (PropExec.bytes_le_to_Z_bound bs) as B. pose proof (PropExec.bytes_le_to_Z_nonneg bs) as B0. rewrite Lb in B. split; [exact B0|exact B].
- unfold cell. rewrite R. f_equal. symmetry. apply APSX.word_to_le_bytes_of_bytes_n; [exact Lb|exact Hn8].
Qed.
Lemma art_img_wr : ltac2:(TCodec.tc2 tcn__JatImgCell "Q1'Q5yR0%211'6y8%511%311p051'?&J+QVmfHr2%3221z%5213&Ir4r3%3221+QP0%52:1%<231&C&Hr6r5%44321:p061p0>1p0A1pR4F1pR0G1pQ4I1").
Proof.
intros M a n Ha Hn0 Hn d k Hd Hk.
apply (store_ok_window ASEGS M (Z_to_bv 64 0x1376d8) (Z_to_bv 64 (a + d)) 1024%nat k 0x1376d8 (0x1376d8 + 1024));
first [exact art_wseg_secwin | reflexivity | lia | (rewrite art_u_lit by lia; lia)].
Qed.
