(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import PropExec CatExec CatSim SeqExec StepTac StoreOk Hoare WalkTac MmapSim As0StepLib As0Tables
ArtMem ArtRegs ArtAtomics ArtTac JbtLeaf JbtAllocG JbtPoison ArtRuns ArtRunsMem JbtFp.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLia. Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLiaT.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import SecKit. From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__JbtFxQ () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Lists.ListDef."; "Corelib.Numbers.BinNums."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.ArtMem."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.JbtFp."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.JbtFxQ."; "OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.AsanUbsan.M."; "Stdlib.Lists.List."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["1app"; "1list"; "1nil"; "1option"; "1pair"; "1prod"; "2and"; "2eq"; "2not"; "3Forall"; "4Z"; "0M"; "0M'"; "5cell"; "6art_agree"; "7art_qbatch"]; ["7art_qbytes"; "7art_qgeo"; "7art_qhead"; "7art_qlist"; "7art_qrec"; "7art_qsep"; "7qb_addr"; "8loaded_segments"; "9In"; "9last"; ":add"; ":le"; ":lt"; ":pow"; "0W"; "0a"]; ["0b"; "0bs"; "0f"; "0l"; ";bv"]]).
Local Ltac lia := L5FastLiaT.plia1.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
#[local] Abbreviation cellA := (cell AsanUbsan.M.loaded_segments).
#[local] Notation "'U' r" := (bv_unsigned r) (at level 10, r at level 9).
Definition art_qbatch : Type := (Z * list Z * Z)%type.
Definition qb_addr (b : art_qbatch) : Z := fst (fst b).
Definition qb_items (b : art_qbatch) : list Z := snd (fst b).
Definition qb_size (b : art_qbatch) : Z := snd b.
Definition art_qhead (bs : list art_qbatch) : Z := match bs with [] => 0 | b :: _ => qb_addr b end.
Definition art_qrec (M : word -> option byte) (b : art_qbatch) : Prop :=
(length (qb_items b) <= 1021)%nat
/\ cellA M (qb_addr b + 16) 8 (Z.of_nat (length (qb_items b)))
/\ cellA M (qb_addr b + 8) 8 (qb_size b)
/\ (forall j it, nth_error (qb_items b) j = Some it -> cellA M (qb_addr b + 24 + 8 * Z.of_nat j) 8 it).
Fixpoint art_qlist (M : word -> option byte) (bs : list art_qbatch) (first last : Z) : Prop :=
match bs with
| [] => first = 0
| b :: r =>
first = qb_addr b /\ art_qrec M b
/\ (match r with [] => last = qb_addr b | _ => True end)
/\ cellA M (qb_addr b) 8 (art_qhead r)
/\ art_qlist M r (art_qhead r) last
end.
Definition art_qbytes (bs : list art_qbatch) : Z := fold_right (fun b z => qb_size b + z) 0 bs.
Lemma art_qbytes_app : ltac2:(TCodec.tc2 tcn__JbtFxQ "B'1&?%211'7':&@&0r2r1%33821%511&J%715%815%3221%<3;51pR2>1pR0?1").
Proof. intros a b. unfold art_qbytes. induction a as [|x a IH]; cbn [app fold_right]; lia. Qed.
Lemma art_qlist_first : ltac2:(TCodec.tc2 tcn__JbtFxQ "K'Q4yR0%211'3y8%511%311p051'1&?%211':&Cr4r3r2r1%544321'7&B%117%33:71p051pR8<1pR6=1pR4?1pHC1").
Proof. intros M [|b r] f l H; cbn in *; [exact H | tauto]. Qed.
Definition art_qgeo (W : list (Z * Z)) (b : art_qbatch) : Prop := 0 <= qb_addr b /\ qb_addr b + 8192 < 2 ^ 64 /\ art_gap W (qb_addr b) 8192.
Section SE.
Local Abbreviation SEC_T_art_qrec_tr := (ltac2:(TCodec.tc2 tcn__JbtFxQ "Q0'1'5':%2211%411'Q4yR0%211'3y8%511%311p051&?&>r4r3r2%43321&Ar5%2214&D%1237%2249p021p051p091pR2?1pJA1pHB1pQNK1")) (only parsing).
Variable W : ltac:(sec_ty2 constr:(SEC_T_art_qrec_tr) 0%nat 0%nat).
Variable M : ltac:(sec_ty2 constr:(SEC_T_art_qrec_tr) 1%nat 0%nat).
Variable M' : ltac:(sec_ty2 constr:(SEC_T_art_qrec_tr) 2%nat 0%nat).
Variable b : ltac:(sec_ty2 constr:(SEC_T_art_qrec_tr) 3%nat 0%nat).
Lemma art_qrec_tr : ltac:(sec_stmt2 constr:(SEC_T_art_qrec_tr) 4%nat 0%nat).
Proof.
intros A (G0 & G1 & G) (L & C1 & C2 & CI).
unfold art_qrec.
split; [exact L|].
split; [apply (art_cell_tr W M M' _ _ _ A); [eapply art_gap_sub; [exact G|lia|cbn; lia]|lia|cbn; lia|exact C1]|].
split; [apply (art_cell_tr W M M' _ _ _ A); [eapply art_gap_sub; [exact G|lia|cbn; lia]|lia|cbn; lia|exact C2]|].
intros j it Hj. assert (Hjl : (j < length (qb_items b))%nat) by (apply nth_error_Some; congruence).
apply (art_cell_tr W M M' _ _ _ A); [eapply art_gap_sub; [exact G|lia|cbn; lia]|lia|cbn; lia|exact (CI j it Hj)].
Qed.
End SE.
Lemma art_qlist_tr : ltac2:(TCodec.tc2 tcn__JbtFxQ "Q6'1'5':%2211%411'Q4yR0%211'3y8%511%311p051&?%>11&>r6r5r4%43321'9&Ar7%211%43;16&Cr3%245:91%346<;:p021p061p0<1pR8N1pR6O1pR4D1pJG1pHH1pQNQ11").
Proof.
intros W M M' bs. induction bs as [|b r IH]; intros f l A F H; cbn [art_qlist] in *; [exact H|].
inversion F as [|? ? Fb Fr]; subst. destruct H as (Ef & R & El & Cn & Hr).
split; [exact Ef|]. split; [exact (art_qrec_tr W M M' b A Fb R)|]. split; [exact El|].
split; [destruct Fb as (G0 & G1 & G); apply (art_cell_tr W M M' _ _ _ A); [eapply art_gap_sub; [exact G|lia|cbn; lia]|lia|cbn; lia|exact Cn]|].
exact (IH _ _ A Fr Hr).
Qed.
Lemma art_qlist_last : ltac2:(TCodec.tc2 tcn__JbtFxQ "QB'Q4yR0%211'3y8%511%311p051'1&?%211':&8'7r3(2%117%43731%611&Cr5r4r2%443291'6&F&I(4'5%E1B%22C1z%A1E%64F421%744G13%93J?1%;11%H3J1G&=&Gr6u8%4532L1;%C261p0E1p0K1pR8Q31pR6Q41pR4Q61pHQ:1").
Proof.
intros M bs. induction bs as [|b r IH]; intros f l NE H; [congruence|].
cbn [art_qlist] in H. destruct H as (Ef & R & El & Cn & Hr).
destruct r as [|b' r'].
- cbn [last]. split; [symmetry; exact El | rewrite El; exact Cn].
- change (last (b :: b' :: r') (0, [], 0)) with (last (b' :: r') (0, [], 0)). apply (IH _ _ ltac:(discriminate) Hr).
Qed.
Fixpoint art_qsep (bs : list art_qbatch) : Prop :=
match bs with
| [] => True
| b :: r => 0 <= qb_addr b /\ qb_addr b + 8192 < 2 ^ 64 /\ Forall (fun b' => apart (qb_addr b) 8192 (qb_addr b') 8192) r /\ art_qsep r
end.
Lemma art_qsep_rng : ltac2:(TCodec.tc2 tcn__JbtFxQ "M'1&?%211&Er2%211&Hr3%23741'6&Kz&F%116%4231&L&J+XP0%2251&M+2+R0%3221%8251%?2:1p0A1p0E1pR2J1pR4J1").
Proof. induction bs as [|x r IH]; intros b S Hin; cbn in *; [contradiction|]. destruct S as (S0 & S1 & S2 & S3). destruct Hin as [<-|Hin]; [lia|exact (IH b S3 Hin)]. Qed.
Lemma art_qsep_app_r : ltac2:(TCodec.tc2 tcn__JbtFxQ "='1&?%211&E&0r2r1%33621%511%614p021pR291pR0:1").
Proof. induction a as [|x a IH]; intros b S; cbn [app art_qsep] in *; [exact S|]. apply IH. tauto. Qed.
Lemma art_last_in : forall (A : Type) (l : list A) d, l <> [] -> In (last l d) l.
Proof. intros A l d NE. destruct (exists_last NE) as (l' & x & ->). rewrite last_last. apply in_or_app. right. left. reflexivity. Qed.
Section SE.
Local Abbreviation SEC_T_art_qlist_splice := (forall M M' gbs tbs gf gl tf tl, gbs <> [] -> art_qlist M gbs gf gl -> art_qlist M tbs tf tl ->
art_agree [(gl, 8)] M M' -> cellA M' gl 8 tf -> art_qsep (gbs ++ tbs) ->
art_qlist M' (gbs ++ tbs) gf (match tbs with [] => gl | _ => tl end)) (only parsing).
Variable M : ltac:(sec_ty2 constr:(SEC_T_art_qlist_splice) 0%nat 0%nat).
Variable M' : ltac:(sec_ty2 constr:(SEC_T_art_qlist_splice) 1%nat 0%nat).
Lemma art_qlist_splice : ltac:(sec_stmt2 constr:(SEC_T_art_qlist_splice) 2%nat 0%nat).
Proof.
intros gbs tbs gf gl tf tl NEg Hg Ht A Cgl S.
revert gf Hg S. induction gbs as [|b r IH]; intros gf Hg S; [congruence|].
cbn [app art_qsep] in S. destruct S as (S0 & S1 & S2 & S3).
cbn [art_qlist] in Hg. destruct Hg as (Ef & R & El & Cn & Hr).
destruct r as [|b' r'].
-
cbn [app] in *. subst gl. cbn [art_qlist]. split; [exact Ef|].
split.
{ destruct R as (L & C1 & C2 & CI). unfold art_qrec. split; [exact L|].
assert (T : forall a (n : nat) v, qb_addr b + 8 <= a -> a + Z.of_nat n <= qb_addr b + 8192 -> cellA M a n v -> cellA M' a n v).
{ intros a n v Ha Hn C. apply (art_cell_tr _ M M' _ _ _ A); [|lia|lia|exact C]. cbn [art_gap fst snd]. split; [unfold apart; lia|exact I]. }
split; [apply T; [lia|cbn; lia|exact C1]|]. split; [apply T; [lia|cbn; lia|exact C2]|].
intros j it Hj. assert (Hjl : (j < length (qb_items b))%nat) by (apply nth_error_Some; congruence). apply T; [lia|cbn; lia|exact (CI j it Hj)]. }
split; [destruct tbs; [reflexivity|exact I]|].
rewrite (art_qlist_first M tbs tf tl Ht) in Cgl. split; [exact Cgl|].
rewrite <- (art_qlist_first M tbs tf tl Ht).
assert (Ht' : art_qlist M' tbs tf tl).
{ apply (art_qlist_tr [(qb_addr b, 8)] M M' tbs tf tl A); [|exact Ht].
apply Forall_forall. intros x Hx. destruct (art_qsep_rng tbs x S3 Hx) as (X0 & X1). split; [exact X0|]. split; [exact X1|].
cbn [art_gap fst snd]. split; [|exact I]. pose proof (proj1 (Forall_forall _ _) S2 x Hx) as AP. unfold apart in *. lia. }
destruct tbs; [cbn [art_qlist] in *; exact Ht'|exact Ht'].
- assert (Egl : qb_addr (last (b' :: r') (0, [], 0)) = gl) by (apply (art_qlist_last M (b' :: r') _ gl ltac:(discriminate) Hr)).
assert (APb : apart (qb_addr b) 8192 gl 8).
{ rewrite <- Egl. pose proof (proj1 (Forall_forall _ _) S2 (last (b' :: r') (0, [], 0)) ltac:(apply in_or_app; left; apply art_last_in; discriminate)) as AP. unfold apart in *. lia. }
change ((b :: b' :: r') ++ tbs) with (b :: ((b' :: r') ++ tbs)). cbn [art_qlist].
split; [exact Ef|].
split; [apply (art_qrec_tr [(gl, 8)] M M' b A); [split; [exact S0|]; split; [exact S1|]; cbn [art_gap fst snd]; split; [exact APb|exact I]|exact R]|].
split; [exact I|].
split; [apply (art_cell_tr _ M M' _ _ _ A); [cbn [art_gap fst snd]; split; [unfold apart in *; cbn; lia|exact I]|lia|cbn; lia|exact Cn]|].
exact (IH ltac:(discriminate) _ Hr S3).
Qed.
End SE.
