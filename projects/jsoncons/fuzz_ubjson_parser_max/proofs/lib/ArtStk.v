(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import PropExec ArtMem.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__ArtStk () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Init.Peano."; "Corelib.Lists.ListDef."; "Corelib.Numbers.BinNums."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.ArtMem."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.ArtStk."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["0B"; "1O"; "1bool"; "1cons"; "1length"; "1list"; "1nat"; "1nil"; "1option"; "1true"; "2and"; "2eq"; "2or"; "3lt"; "4nth"; "5Z"]; ["0M0"; "6cell"; "6wok"; "6wr"; "7aoff"; "7ashape"; "7aval"; "7env_ok"; "7env_oth"; "7hB"; "7hbase"; "7hhi"; "7hlo"; "7hull"; "7hull0"; "7hull_rng"]; ["7mkhull"; "7slayer"; "7sstk"; "7stk_chk"; "7wlayer"; "7wstk"; "8add"; "8le"; "8lt"; "8pow"; "0b"; "0env"; "0hi"; "0j"; "0l"; "0lo"]; ["0m"; "0mz"; "0s"; "0sb"; "0segs"; "9bv"; "0u"]]).
Inductive ashape : Set := Sh_bare | Sh_off (o : Z) | Sh_off2 (o1 o2 : Z).
Definition aval (B : Z) (s : ashape) : Z := match s with Sh_bare => B | Sh_off o => B + o | Sh_off2 o1 o2 => B + o1 + o2 end.
Definition aoff (s : ashape) : Z := match s with Sh_bare => 0 | Sh_off o => o | Sh_off2 o1 o2 => o1 + o2 end.
Lemma aval_off : ltac2:(TCodec.tc2 tcn__ArtStk ">'?'E';&Fr2r1%3221&Q6&D%114%3261%93;51pS6;1p2=1").
Proof. intros B [|o|o1 o2]; cbn [aval aoff]; lia. Qed.
Record hull : Set := mkhull { hB : Z; hlo : Z; hhi : Z }.
Definition hull0 : hull := mkhull 0 0 0.
Definition hbase (env : list hull) (j : nat) : Z := hB (nth j env hull0).
Inductive wkind : Set := WKn (n : nat) (v : Z) | WKf (k : nat) (b : Z).
Definition wsize (k : wkind) : nat := match k with WKn n _ => n | WKf k _ => k end.
Record wlayer : Set := mkwl { wlj : nat; wls : ashape; wlk : wkind }.
Fixpoint wstk (env : list hull) (M0 : word -> option byte) (l : list wlayer) : word -> option byte :=
match l with
| [] => M0
| ly :: l' =>
match wlk ly with
| WKn n v => Wn n (wstk env M0 l') (aval (hbase env (wlj ly)) (wls ly)) v
| WKf k b => Wf (wstk env M0 l') (aval (hbase env (wlj ly)) (wls ly)) k b
end
end.
Definition lay_ok (env : list hull) (ob mz : Z) (ly : wlayer) : bool :=
let h := nth (wlj ly) env hull0 in let o := aoff (wls ly) in let n := Z.of_nat (wsize (wlk ly)) in
(wlj ly <? length env)%nat && (hlo h <=? o) && (o + n <=? hhi h)
&& (match wlj ly with O => (o + n <=? ob) || (ob + mz <=? o) | S _ => true end).
Definition stk_chk (env : list hull) (sb : ashape) (m : nat) (mz : Z) (l : list wlayer) : bool :=
(mz =? Z.of_nat m) && (hlo (nth 0 env hull0) <=? aoff sb) && (aoff sb + mz <=? hhi (nth 0 env hull0)) && forallb (lay_ok env (aoff sb) mz) l.
Definition hull_rng (h : hull) : Prop := 0 <= hB h + hlo h /\ hB h + hhi h < 2 ^ 64.
Fixpoint env_oth (env : list hull) (b mz : Z) : Prop :=
match env with
| [] => True
| h :: env' => (hull_rng h /\ (b + mz <= hB h + hlo h \/ hB h + hhi h <= b)) /\ env_oth env' b mz
end.
Definition env_ok (env : list hull) (b mz : Z) : Prop :=
match env with [] => False | h :: env' => hull_rng h /\ env_oth env' b mz end.
Lemma env_ok_intro : ltac2:(TCodec.tc2 tcn__ArtStk "Q8'?'5'M%211&Q7z&Q6r6r5%3221%6251&Q8r7%7215&Q9+2+R0%3221%7251&Hr4r3%33>21&G(3(Q0r9r8%3321@%53K1F%731F:p091p0>1p0G1pS4Q21pRFQ31pRHQ11pRJQ51pS0Q61p2Q71").
Proof. intros. split; [split; assumption | assumption]. Qed.
Lemma env_oth_nil : ltac2:(TCodec.tc2 tcn__ArtStk ":'?&H(7'M%211r2r1%63321pS481pRF91").
Proof. intros. exact I. Qed.
Lemma env_oth_cons : ltac2:(TCodec.tc2 tcn__ArtStk "Q@'?'5'M%211&Q7z&Q6r6r5%3221%6251&Q8r7%7215&Q9+2+R0%3221%7251'<r4r3%@221r8%B21<%E231%D23C%G217%9231&H%13GF:(3(Q0r:r9%3321<%53Q21H%831NMp081p0;1p0F1p0O1pS4Q:1pRFQ;1pRHQ91pRJQ=1pS0Q>1p2Q?1").
Proof. intros. split; [split; [split; assumption | assumption] | assumption]. Qed.
Lemma env_oth_nth : ltac2:(TCodec.tc2 tcn__ArtStk "Q<'5'M%211'?'6&Hr4r3r2%43321&=&4r5%22<1%4261':&O&>r6&N%34C=21%511'<&Q7&Q6%12=C&I%117&L%119%6231%8261&K%11=%:271%<21G%>251%F2@1p0H1p0N1pRLQ41pS4Q61pRFQ71pRHQ91").
Proof.
induction env as [|h env IH]; intros b mz j H Hj; [cbn in Hj; lia|].
destruct H as [H1 H2]. destruct j as [|j]; [exact H1 | apply IH; [exact H2 | cbn in Hj; lia]].
Qed.
Inductive slayer : Set := SLn (n : nat) (a v : Z) | SLf (a : Z) (k : nat) (b : Z).
Fixpoint sstk (M0 : word -> option byte) (l : list slayer) : word -> option byte :=
match l with
| [] => M0
| SLn n a v :: l' => Wn n (sstk M0 l') a v
| SLf a k b :: l' => Wf (sstk M0 l') a k b
end.
Section WithSegs.
Variable segs : list Segment.
Lemma wok_sstk : ltac2:(TCodec.tc2 tcn__ArtStk "M'QEyR0%211'8y8%511%311p051'5'Q1%211'?'6&BvQDr4r2r1%544321&Q2r5%2216r3%:49217p061pS2=1pRF?1pRNA1pQ2E1").
Proof.
intros M0 l b m H. induction l as [|[n a v|a k bb] l IH]; [exact H | |]; cbn [sstk]; [apply wok_Wn | apply wok_Wf]; exact IH.
Qed.
Lemma wr_sstk : ltac2:(TCodec.tc2 tcn__ArtStk "L'QEyR0%211'8y8%511%311p051'5'Q1%211'?&CvQDr4r2r1%544321&Q2r5%2216r3%:49217p061pS2=1pRF>1pRN@1pQ2D1").
Proof.
intros M0 l b m H. induction l as [|[n a v|a k bb] l IH]; [exact H | |]; cbn [sstk]; [apply wr_Wn | apply wr_Wf]; exact IH.
Qed.
Lemma cell_wstk_other : ltac2:(TCodec.tc2 tcn__ArtStk "QJ'5'M%211'QEyR0%211'8y8%511%311p051'Q4%<11'?'E'6';r5&F&Jr8(1%3221r4%6221%93<81&Gr9r6r3%43321'2&Q3r:%2516A;>(9%D3521&AvQD%2516C;@&Q5r<r;%3321:r7%8572B1Lp071p0;1p0B1p0H1pS>Q51pS4Q61pS2Q51pS8Q71pRFQ91pRNQ;1pQ2Q>1pRHQG1").
Proof.
intros env M0 l b sb m mz u Eb0 HE HC H.
unfold stk_chk in HC.
apply andb_prop in HC. destruct HC as [HC HL]. apply andb_prop in HC. destruct HC as [HC Hb2]. apply andb_prop in HC. destruct HC as [Hmz Hb1].
apply Z.eqb_eq in Hmz. apply Z.leb_le in Hb1. apply Z.leb_le in Hb2.
destruct env as [|h0 env']; [destruct HE|]. destruct HE as [[Rb1 Rb2] HO].
assert (Eb : b = hB h0 + aoff sb) by (rewrite Eb0; unfold hbase; cbn [nth]; apply aval_off).
cbn [nth] in Hb1, Hb2.
induction l as [|ly l IH]; [exact H|].
cbn [forallb] in HL. apply andb_prop in HL. destruct HL as [Hly HL]. specialize (IH HL).
unfold lay_ok in Hly. cbn zeta in Hly.
apply andb_prop in Hly. destruct Hly as [Hly Hsb]. apply andb_prop in Hly. destruct Hly as [Hly Ho2]. apply andb_prop in Hly. destruct Hly as [Hj Ho1].
apply Nat.ltb_lt in Hj. apply Z.leb_le in Ho1. apply Z.leb_le in Ho2.
assert (Ea : aval (hbase (h0 :: env') (wlj ly)) (wls ly) = hB (nth (wlj ly) (h0 :: env') hull0) + aoff (wls ly)) by (unfold hbase; apply aval_off).
assert (RA : 0 <= hB (nth (wlj ly) (h0 :: env') hull0) + hlo (nth (wlj ly) (h0 :: env') hull0)
/\ hB (nth (wlj ly) (h0 :: env') hull0) + hhi (nth (wlj ly) (h0 :: env') hull0) < 2 ^ 64
/\ apart (aval (hbase (h0 :: env') (wlj ly)) (wls ly)) (Z.of_nat (wsize (wlk ly))) b (Z.of_nat m)).
{ unfold apart. rewrite Ea. destruct (wlj ly) as [|j] eqn:Ej.
- cbn [nth] in *. split; [exact Rb1|]. split; [exact Rb2|]. rewrite Eb. apply orb_prop in Hsb. destruct Hsb as [Hs|Hs]; apply Z.leb_le in Hs; lia.
- cbn [nth] in *. cbn [length] in Hj. destruct (env_oth_nth env' b mz j HO ltac:(lia)) as [[R1 R2] R3]. split; [exact R1|]. split; [exact R2|]. lia. }
destruct RA as (R1 & R2 & AP).
cbn [wstk]. destruct (wlk ly) as [n v|k bb]; cbn [wsize] in *.
- apply cell_Wn_other; [lia | lia | lia | lia | exact AP | exact IH].
- apply cell_Wf_other; [lia | lia | lia | lia | exact AP | exact IH].
Qed.
End WithSegs.
