(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import PropExec CatSim StoreOk AsanPlanSoundSums ArtMem ArtRuns ArtRunsMem.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__JbtCellEx () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Init.Peano."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.LinuxProcessSem.MemImageType."; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.ArtMem."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.JbtCellEx."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec."; "OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.AsanUbsan.M."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["1None"; "1Some"; "1bool"; "1length"; "1list"; "1nat"; "1option"; "1true"; "2and"; "2eq"; "2ex"; "2not"; "2or"; "3le"; "4Z"; "5Segment"]; ["6find_segment"; "6wview"; "0M"; "7cell"; "7wr"; "8art_segs_in"; "9rdn"; ":loaded_segments"; ";add"; ";le"; ";lt"; ";mul"; ";of_nat"; ";pow"; "0a"; "0bs"]; ["0hi"; "0lo"; "0n"; "0segs"; "<Z_to_bv"; "<bv"; "<bv_unsigned"; "0v"; "0x"]]).
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
#[local] Abbreviation ASEGS := AsanUbsan.M.loaded_segments.
#[local] Abbreviation cellA := (cell AsanUbsan.M.loaded_segments).
#[local] Abbreviation wrA := (wr AsanUbsan.M.loaded_segments).
#[local] Notation "'U' r" := (bv_unsigned r) (at level 10, r at level 9).
Fixpoint art_segs_in (segs : list Segment) (lo hi : Z) : bool :=
match segs with
| [] => true
| s :: r => (lo <=? Z.of_N (seg_base s)) && (Z.of_N (seg_base s) + Z.of_N (seg_size s) <=? hi) && art_segs_in r lo hi
end.
Lemma art_find_segment_none : ltac2:(TCodec.tc2 tcn__JbtCellEx "Q2'4'?%211'>'9'2&Er4r3r2%43321(7%83721'<&J%1268&I%1298%5231'6%11C&@r6+1%332@1(0%11I%G3731p0:1p0A1pRBK1pR2L1pR4M1pR8O1").
Proof.
induction segs as [|s r IH]; intros lo hi x H Hx; [reflexivity|]. cbn [art_segs_in] in H.
apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2.
cbn [find_segment].
replace (Z.leb (Z.of_N (seg_base s)) x && Z.leb (x + 1) (Z.of_N (seg_base s) + Z.of_N (seg_size s)))%bool with false.
- exact (IH lo hi x H3 Hx).
- symmetry. apply andb_false_iff. destruct Hx as [Hx|Hx]; [left | right]; apply Z.leb_gt; lia.
Qed.
Lemma art_asegs_in : ltac2:(TCodec.tc2 tcn__JbtCellEx "9'9'2&E&G+RPP0+Vb\P0%43321(7%83721").
Proof. vm_compute. reflexivity. Qed.
Lemma art_wview_off : ltac2:(TCodec.tc2 tcn__JbtCellEx "N'Q5yR0%211'6y8%511%311p051'<&J&Q6r1%22;1+RPP0%5221&I+Vb\P0%2215%:241'9&A&Gr3r2%43321%312%73D21p091pRBJ1pQ6F1").
Proof.
intros M x Hx. unfold wview. destruct (M x) as [b|]; [reflexivity|].
rewrite (art_find_segment_none ASEGS 0x10000 0x693000 (U x) art_asegs_in Hx). reflexivity.
Qed.
Lemma art_rdn_defined : ltac2:(TCodec.tc2 tcn__JbtCellEx "R6'5'Q5yR0%211'6y8%511%311p051'>&Izr1%3221&J&Hr2&Lr4%211%5241&M+2+R0%3221%;251'8&Q6%12J@%C2;1r6%>11%A2>1%C251%8251&;'9%71E(0%11Q1%43Q131%611p081pRBQ81':'4%11Q8%Q;11&F&G&Q4r5%22QB1r7%645H21(1%12:Q<%E3:31&3%12QEQ?%H3QL17%Q3241qR0@1%C2A1p0E1p0Q81p0QE1pQNQJ1pQ6QL1pR6R51").
Proof.
induction n as [|n IH]; intros M a Ha Hn D; [exists []; split; reflexivity|].
cbn [rdn]. assert (Ua : U (Z_to_bv 64 a : word) = a) by (apply art_u_lit; lia).
destruct (M (Z_to_bv 64 a)) as [b|] eqn:E; [|exfalso; apply (D (Z_to_bv 64 a)); [rewrite Ua; lia|exact E]].
replace ((Z_to_bv 64 a + 1)%bv : word) with (Z_to_bv 64 (a + 1) : word).
2:{ apply bv_eq. rewrite bv_add_unsigned, Ua. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
change (bv_unsigned (1 : bv 64)%bv) with 1. rewrite !Z.mod_small by lia. reflexivity. }
destruct (IH M (a + 1) ltac:(lia) ltac:(lia) ltac:(intros x Hx; apply D; lia)) as (bs & R & Lb).
rewrite R. exists (b :: bs). split; [reflexivity|cbn; lia].
Qed.
Lemma art_cell_exists : ltac2:(TCodec.tc2 tcn__JbtCellEx "R1'Q5yR0%211'6y8%511%311p051'>'5'=r1u8%3221'<&I&Hr3&Lr2%211%5241+RPP0%8221+Vb\P0%:218%<231zr4%>221&Jr5%>14%A221&M+2+R0%3221%8251&D&Gr7r6%I1<%544321':'8%Q02DQ4%B2Q5;%3221&Cr9r8%35=21<Q:%8251qR@Q?1%;2Q@1p0=1p0D1p0N1p0Q21p0Q@1pR6QE1pQNQG1pQ6QI1").
Proof.
intros M a n Hn8 Hoff Ha Hn W.
destruct (art_rdn_defined n M a Ha Hn) as (bs & R & Lb).
{ intros x Hx. pose proof (art_wr_wview ASEGS M a (Z.of_nat n) Ha Hn W x Hx) as V. rewrite art_wview_off in V by lia. exact V. }
exists (bytes_le_to_Z bs). split.
- pose proof (PropExec.bytes_le_to_Z_bound bs) as B. pose proof (PropExec.bytes_le_to_Z_nonneg bs) as B0. split; [exact B0|]. eapply Z.lt_le_trans; [exact B|]. apply Z.pow_le_mono_r; lia.
- unfold cell. rewrite R. f_equal. symmetry. apply APSX.word_to_le_bytes_of_bytes_n; [exact Lb|exact Hn8].
Qed.
Lemma art_cell_exists_b : ltac2:(TCodec.tc2 tcn__JbtCellEx "R6'Q5yR0%211'6y8%511%311p051'>'5'=r1u8%3221'<&I&Hr3&Lr2%211%5241+RPP0%8221+Vb\P0%:218%<231zr4%>221&Jr5%>14%A221&M+2+R0%3221%8251&D&Gr7r6%I1<%544321':'8%Q02DQ4&K+8%Q019%3221%B2A1%G2Q:1%8271&Cr9r8%35B21AQ?%=251qR@QD1%@2QE1p0B1p0I1p0Q31p0Q71p0QE1pR6QJ1pQNQL1pQ6QN1").
Proof.
intros M a n Hn8 Hoff Ha Hn W.
destruct (art_rdn_defined n M a Ha Hn) as (bs & R & Lb).
{ intros x Hx. pose proof (art_wr_wview ASEGS M a (Z.of_nat n) Ha Hn W x Hx) as V. rewrite art_wview_off in V by lia. exact V. }
exists (bytes_le_to_Z bs). split.
- pose proof (PropExec.bytes_le_to_Z_bound bs) as B. pose proof (PropExec.bytes_le_to_Z_nonneg bs) as B0. rewrite Lb in B. split; [exact B0|exact B].
- unfold cell. rewrite R. f_equal. symmetry. apply APSX.word_to_le_bytes_of_bytes_n; [exact Lb|exact Hn8].
Qed.
