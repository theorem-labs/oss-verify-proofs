(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith List Lia Bool.
From Stdlib Require Import FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import PropExec CatExec SeqExec StepTac MemSplit.
Import ListNotations.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__ZStores () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Lists.ListDef."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.LinuxProcessSem.BvBase."; "LinuxProcessSemantics.LinuxProcessSem.MemImageType."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CatExec."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.ZStores.FPX_1."; "Stdlib.Lists.List."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["1Some"; "1bool"; "1false"; "1length"; "1list"; "1nat"; "1option"; "1prod"; "1true"; "2and"; "2eq"; "2ex"; "3nth"; "4Z"; "5bytes_le_to_Z"; "6Segment"]; ["0N"; "7wbytes"; "8rdn"; "9covers_off"; "9iota_Z"; "9ws_cover"; "9ws_inb"; "9zeros"; "9zstores"; ":In"; ";add"; ";le"; ";lt"; ";of_nat"; ";pow"; ";sub"]; ["0a"; "0d"; "0i"; "0k"; "0m"; "0n"; "0on"; "0segs"; "<Z_to_bv"; "<bv"; "<bv_unsigned"; "0ws"; "0x"; "0z"]]).
Section FPX_1. Context {fx : PropExec.FPState}.
Definition zeros (n : nat) : list byte := repeat (Z_to_bv 8 0) n.
Fixpoint zstores (m : word -> option byte) (d : word) (ws : list (Z * nat)) : word -> option byte :=
match ws with
| [] => m
| (o, n) :: ws' => zstores (wbytes m (Z_to_bv 64 (bv_unsigned d + o)) (zeros n)) d ws'
end.
Definition covers_off (i : Z) (on : Z * nat) : bool :=
(fst on <=? i) && (i <? fst on + Z.of_nat (snd on)).
Definition ws_inb (ws : list (Z * nat)) (N : Z) : bool :=
forallb (fun on => (0 <=? fst on) && (fst on + Z.of_nat (snd on) <=? N)) ws.
Fixpoint iota_Z (i : Z) (k : nat) : list Z :=
match k with O => [] | S k' => i :: iota_Z (i + 1) k' end.
Definition ws_cover (ws : list (Z * nat)) (N : nat) : bool :=
forallb (fun i => existsb (covers_off i) ws) (iota_Z 0 N).
Lemma forallb_In : forall {A} (f : A -> bool) l x, forallb f l = true -> In x l -> f x = true.
Proof.
induction l as [|y l IH]; intros x H Hin; [contradiction|].
cbn in H. apply andb_true_iff in H as [Hy Hl].
destruct Hin as [<-|Hin]; [exact Hy | apply IH; assumption].
Qed.
Lemma iota_Z_In : ltac2:(TCodec.tc2 tcn__ZStores "H'5'='9&Kr2r1%3221&L&J&Mr3%211%4281%6281%<281&I&Dr4%2281%43B?1p061pRLD1pR6E1pR8G1").
Proof.
induction k as [|k IH]; intros i z Hz; [lia|].
cbn. destruct (Z.eq_dec i z); [left; assumption | right]. apply IH. lia.
Qed.
Lemma existsb_false_forall : forall {A} (f : A -> bool) l,
existsb f l = false -> forall x, In x l -> f x = false.
Proof.
induction l as [|y l IH]; intros H x Hin; [contradiction|].
cbn in H. apply orb_false_iff in H as [Hy Hl].
destruct Hin as [<-|Hin]; [exact Hy | apply IH; assumption].
Qed.
Lemma existsb_true_exists : forall {A} (f : A -> bool) l,
existsb f l = true -> exists x, In x l /\ f x = true.
Proof.
induction l as [|y l IH]; intros H; [discriminate|].
cbn in H. apply orb_true_iff in H as [Hy|Hl].
- exists y. split; [left; reflexivity | exact Hy].
- destruct (IH Hl) as [x [Hin Hx]]. exists x. split; [right; exact Hin | exact Hx].
Qed.
Lemma length_zeros : ltac2:(TCodec.tc2 tcn__ZStores "<'5':&3'Q9y8%211&Gr1%211%7241%93:13pR<;1").
Proof. intro n. apply repeat_length. Qed.
Lemma nth_zeros : ltac2:(TCodec.tc2 tcn__ZStores "A'5':'Q9y8%211&<r1&Gr2%211&Q8z%2291%849741%=3:12pR8?1pR<@1").
Proof. intros n k. unfold zeros. apply nth_repeat. Qed.
Lemma rdn_wbytes_zeros_in : ltac2:(TCodec.tc2 tcn__ZStores "QO'4'?%211'Q9yR0%211'6y8%511%311p051'5&L&J&Q:r4%22<1&Mr2%211%7241&N+2+R0%3221%=251&Kr5%>2H1%321=r3%>11%C241r6%D2N1%B1D%G221%;251':%Q71O%Q211&Br9&Ar8r7&G%11D%53431%8471@Q2(0%51Q4%22=1%?3=41p0A1p0J1p0O1pR<Q>1pQ2Q?1pR2QF1pR4QG1pR:QC1pR@QL1").
Proof.
intros segs m d a N n Hnw Hlo Hhi. unfold zeros at 2. apply rdn_const; [lia|].
intros x Hx. rewrite wbytes_inside by (rewrite length_zeros; lia).
f_equal. apply nth_zeros.
Qed.
Lemma bytes_le_to_Z_zeros : ltac2:(TCodec.tc2 tcn__ZStores ";'5':'=&>&Gr1%211%411z%83721pR<:1").
Proof.
induction n as [|n IH]; [reflexivity|]. cbn [zeros repeat bytes_le_to_Z].
fold (zeros n). rewrite IH. reflexivity.
Qed.
Section Cover.
Variable d : word.
Variable N : Z.
Hypothesis Hnw : bv_unsigned d + N < 2^64.
Lemma zstores_miss : ltac2:(TCodec.tc2 tcn__ZStores "QA'4'7'='5%3221%511'Q9yR0%211'6y8%511%311p051':'1&Fr3v@%3221(8%73621&Ir1r5%33E21&C&O&Q:r4%22G1vQ1%42I1%6231r2%9221(2%G3F21p0=1pR>Q31&H%14<:AH%=1I%M3O21p051p0H1pRJQ61pR:Q21pRHQ;1").
Proof.
induction ws as [|[o n] ws IH]; intros m x Hinb Hno; [reflexivity|].
cbn [zstores]. cbn [ws_inb forallb fst snd] in Hinb.
apply andb_true_iff in Hinb as [Hon Hinb]. apply andb_true_iff in Hon as [Ho Hn].
apply Z.leb_le in Ho. apply Z.leb_le in Hn.
rewrite IH; [| exact Hinb | intros on Hin; apply Hno; right; exact Hin].
pose proof (Hno (o, n) (or_introl eq_refl)) as Hc. cbn [covers_off fst snd] in Hc.
pose proof (u64_range x). pose proof (u64_range d).
apply wbytes_outside.
- rewrite length_zeros. rewrite u_Z2bv by lia. lia.
- rewrite length_zeros. rewrite u_Z2bv by lia.
apply andb_false_iff in Hc as [Hc|Hc]; [apply Z.leb_gt in Hc | apply Z.ltb_ge in Hc];
cbn [fst snd] in Hc; lia.
Qed.
Lemma zstores_hit : ltac2:(TCodec.tc2 tcn__ZStores "QF'4'7'='5%3221%511'Q9yR0%211'6y8%511%311p051':'1&Fr3v@%3221(8%73621';'9&Ir1r5%33G21&C&O&Q:%12H>vQ1%32J1%5231%721:%F3E1@%>2:1qR>Q21%A2Q31&Hr4%241:@I(0&Q8z%22Q41%42Q41%Q23Q461p0:1p0M1pRJQ;1pR:Q71pRHQ@1").
Proof.
induction ws as [|[o n] ws IH]; intros m x Hinb Hex.
{ destruct Hex as [on [[] _]]. }
cbn [zstores]. cbn [ws_inb forallb fst snd] in Hinb.
apply andb_true_iff in Hinb as [Hon Hinb]. apply andb_true_iff in Hon as [Ho Hn].
apply Z.leb_le in Ho. apply Z.leb_le in Hn.
destruct (existsb (covers_off (bv_unsigned x - bv_unsigned d)) ws) eqn:E.
- apply IH; [exact Hinb|]. apply existsb_true_exists. exact E.
- rewrite zstores_miss; [| exact Hinb | apply existsb_false_forall; exact E].
destruct Hex as [on [[<-|Hin] Hc]].
2:{ rewrite (existsb_false_forall _ _ E on Hin) in Hc. discriminate. }
cbn [covers_off fst snd] in Hc. apply andb_true_iff in Hc as [Hc1 Hc2].
apply Z.leb_le in Hc1. apply Z.ltb_lt in Hc2. cbn [fst snd] in Hc1, Hc2.
pose proof (u64_range x). pose proof (u64_range d).
rewrite wbytes_inside by (rewrite length_zeros, u_Z2bv by lia; lia).
f_equal. apply nth_zeros.
Qed.
Lemma zstores_cover : ltac2:(TCodec.tc2 tcn__ZStores "Q>'4'7'='5%3221%511'Q9yR0%211'6y8%511%311p051':&Mr1%211v@%53A21'1&Fr4%2215(8%;3521&Er5r3%3221%@3:16&HvQ1r6%33721&A&G%11?%33;61%I3J51p0:1p0@1p0G1pR<Q81pR:O1pRHQ81").
Proof.
intros ws m n HnN Hinb Hcov. apply functional_extensionality. intro x.
pose proof (u64_range x). pose proof (u64_range d).
destruct (Z_lt_le_dec (bv_unsigned x) (bv_unsigned d)) as [Hlt|Hge].
{ rewrite wbytes_outside by (rewrite length_zeros; lia).
apply zstores_miss; [exact Hinb|]. intros [o k] Hin.
pose proof (forallb_In _ _ _ Hinb Hin) as Hb. cbn [fst snd] in Hb.
apply andb_true_iff in Hb as [Hb1 Hb2]. apply Z.leb_le in Hb1.
cbn [covers_off fst snd]. apply andb_false_iff. left. apply Z.leb_gt. cbn [fst snd]. lia. }
destruct (Z_lt_le_dec (bv_unsigned x) (bv_unsigned d + N)) as [Hin|Hout].
- rewrite wbytes_inside by (rewrite length_zeros; lia). rewrite nth_zeros.
apply zstores_hit; [exact Hinb|].
pose proof (forallb_In _ _ _ Hcov (iota_Z_In n 0 (bv_unsigned x - bv_unsigned d) ltac:(lia))) as He.
apply existsb_true_exists in He. exact He.
- rewrite wbytes_outside by (rewrite length_zeros; lia).
apply zstores_miss; [exact Hinb|]. intros [o k] Hin'.
pose proof (forallb_In _ _ _ Hinb Hin') as Hb. cbn [fst snd] in Hb.
apply andb_true_iff in Hb as [Hb1 Hb2]. apply Z.leb_le in Hb2.
cbn [covers_off fst snd]. apply andb_false_iff. right. apply Z.ltb_ge. cbn [fst snd]. lia.
Qed.
End Cover.
End FPX_1.
