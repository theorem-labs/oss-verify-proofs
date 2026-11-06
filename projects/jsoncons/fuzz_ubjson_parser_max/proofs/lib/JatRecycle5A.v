(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import PropExec CatSim StoreOk As0Tables ArtMem JatInitCache JatPopulate1 ArtRuns JatCls JatFp JatClsRep JatSecAllocPost JatRecycle2C JatRecycle3L.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLia. Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLiaT.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import SecKit. From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__JatRecycle5A () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Numbers.BinNums."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.JatCls."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.JatInitCache."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.JatRecycle2C."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.JatRecycle3L."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.JatRecycle5A."; "Stdlib.Lists.List."; "Stdlib.Sorting.Permutation."; "Stdlib.ZArith.BinInt.Z."], [["1Some"; "1app"; "1cons"; "1fst"; "1length"; "1list"; "1nat"; "1option"; "1pair"; "1prod"; "2and"; "2eq"; "2iff"; "2not"; "2or"; "3Z"]; ["0HI"; "4art_cls"; "4cl_au"; "4cl_cache"; "4cl_free"; "4cl_mfa"; "4cl_mu"; "5art_ic_mc"; "6art_sec_geo"; "6art_swap_remove"; "7art_cls_dealloc"; "8art_bl_idx"; "8art_cls_upd"; "9In"; "9nth_error"; ":Permutation"]; [";add"; ";le"; ";of_nat"; "0b"; "0b'"; "0bl"; "0c"; "0c'"; "0cl"; "0ctx"; "0f"; "0i"; "0mb"; "0ms"; "0parr"; "0t"]; ["0w"; "0x"]]).
Local Ltac lia := L5FastLiaT.plia1.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Inductive art_rel : Type :=
| REP (c w d b1 n : Z)
| RES (mb ms m b1 n : Z)
| REB (wb : Z).
Definition art_rel_addr (spb : Z) (e : art_rel) : Z :=
match e with REP c w d _ _ => spb + c * 2 ^ 32 + 16 * w + d | RES _ _ m _ _ => m | REB wb => spb + 24 * 2 ^ 32 + 16 * wb end.
Definition art_rel_zone (spb : Z) (e : art_rel) : Z * Z :=
match e with REP c w _ _ _ => (spb + c * 2 ^ 32 + 16 * w, AsanTab.class_size c) | RES mb ms _ _ _ => (mb, ms) | REB wb => (spb + 24 * 2 ^ 32 + 16 * wb, 8192) end.
Record art_rg : Type := RG { rg_cls : Z -> art_cls; rg_bl : list (Z * Z) }.
Definition art_cls_upd (f : Z -> art_cls) (c : Z) (cl : art_cls) : Z -> art_cls := fun c' => if c' =? c then cl else f c'.
Fixpoint art_bl_idx (mb : Z) (bl : list (Z * Z)) : nat :=
match bl with [] => O | b :: r => if fst b =? mb then O else S (art_bl_idx mb r) end.
Definition art_rel_step (e : art_rel) (G : art_rg) : art_rg :=
match e with
| REP c w _ _ _ => RG (art_cls_upd (rg_cls G) c (art_cls_dealloc c w (rg_cls G c))) (rg_bl G)
| RES mb _ _ _ _ => RG (rg_cls G) (art_swap_remove (0, 0) (art_bl_idx mb (rg_bl G)) (rg_bl G))
| REB wb => RG (art_cls_upd (rg_cls G) 24 (art_cls_dealloc 24 wb (rg_cls G 24))) (rg_bl G)
end.
Definition art_rel_steps (es : list art_rel) (G : art_rg) : art_rg := fold_left (fun g e => art_rel_step e g) es G.
Lemma art_cls_upd_same : ltac2:(TCodec.tc2 tcn__JatRecycle5A "='?'Ap021';&Lr3r2r1%443212%63812pRB91pR>;1pRF:1").
Proof. intros. unfold art_cls_upd. rewrite Z.eqb_refl. reflexivity. Qed.
Lemma art_cls_upd_other : ltac2:(TCodec.tc2 tcn__JatRecycle5A "E'?'Ap021&=';r1r3%33721%511&Lr5r4r2%443271%412%;3>21p081pR@A1pRBA1pR>C1pRFB1").
Proof. intros f c cl c' H. unfold art_cls_upd. destruct (c' =? c) eqn:E; [apply Z.eqb_eq in E; lia|reflexivity]. Qed.
Lemma art_bl_idx_nth : ltac2:(TCodec.tc2 tcn__JatRecycle5A "Q<'5'9'?%2211%411&M(8r2r1%347721r3%63821r6%83:61r7%:3<81';&3r4%23AA1%33BB:%53C21r5%73D15p031p0:1p0=1pR:H1pR8I1'7%11K&N&K%12?;%33O<1(0%N4Q2Q2BJ%22Q21%F3841p0;1p0M1pRLQ71pRJQ81pR<Q71").
Proof.
induction bl as [|b r IH]; intros mb ms Hin Hinj; [destruct Hin|]. cbn [art_bl_idx].
destruct (Z.eqb_spec (fst b) mb) as [E|NE].
- cbn. f_equal. apply Hinj; [left; reflexivity|exact Hin|exact E].
- cbn. apply IH.
+ destruct Hin as [Eb|Hin]; [exfalso; apply NE; rewrite Eb; reflexivity|exact Hin].
+ intros x y Hx Hy. apply Hinj; right; assumption.
Qed.
Lemma art_swap_remove_keeps : forall A (d : A) i l x, (i < length l)%nat -> In x l -> x <> nth i l d -> In x (art_swap_remove d i l).
Proof.
intros A d i l x Hi Hx Hne. destruct (In_nth _ _ d Hx) as (j & Hj & Ej).
assert (Hji : j <> i) by (intros ->; apply Hne; symmetry; exact Ej).
destruct (Nat.eq_dec j (length l - 1)) as [Elast|Nlast].
-
assert (Hil : (i < length l - 1)%nat) by lia.
apply (nth_error_In _ i). rewrite art_swap_remove_nth by exact Hil. rewrite Nat.eqb_refl. rewrite <- Elast. rewrite (nth_error_nth' l d Hj). f_equal. exact Ej.
- assert (Hjl : (j < length l - 1)%nat) by lia.
apply (nth_error_In _ j). rewrite art_swap_remove_nth by exact Hjl. replace (j =? i)%nat with false by (symmetry; apply Nat.eqb_neq; exact Hji).
rewrite (nth_error_nth' l d Hj). f_equal. exact Ej.
Qed.
Section SE.
Local Abbreviation SEC_T_art_sec_geo_remove := (ltac2:(TCodec.tc2 tcn__JatRecycle5A "K'?'5'9%1233%311'6&Hr6r5r4r3r2%6554321r7&I(8z%24AA11%44?178%=56<;:1p081pRH@1pR<B1pRNG1pRDH1pS0I1pQ2J1")) (only parsing).
Variable HI : ltac:(sec_ty2 constr:(SEC_T_art_sec_geo_remove) 0%nat 0%nat).
Variable t : ltac:(sec_ty2 constr:(SEC_T_art_sec_geo_remove) 1%nat 0%nat).
Variable ctx : ltac:(sec_ty2 constr:(SEC_T_art_sec_geo_remove) 2%nat 0%nat).
Variable parr : ltac:(sec_ty2 constr:(SEC_T_art_sec_geo_remove) 3%nat 0%nat).
Variable bl : ltac:(sec_ty2 constr:(SEC_T_art_sec_geo_remove) 4%nat 0%nat).
Variable i : ltac:(sec_ty2 constr:(SEC_T_art_sec_geo_remove) 5%nat 0%nat).
Lemma art_sec_geo_remove : ltac:(sec_stmt2 constr:(SEC_T_art_sec_geo_remove) 6%nat 0%nat).
Proof.
intros (G1 & G2 & G3 & G4 & G5 & G6 & GB & GD).
assert (L : Z.of_nat (length (art_swap_remove (0, 0) i bl)) <= Z.of_nat (length bl)) by (rewrite art_swap_remove_length; lia).
pose proof (Nat2Z.is_nonneg (length (art_swap_remove (0, 0) i bl))) as L0.
unfold art_sec_geo. split; [exact G1|]. split; [lia|]. split; [lia|].
split. { unfold appmem in *. lia. }
split. { unfold apart in *. lia. }
split. { unfold apart in *. lia. }
split.
- intros b Hb. apply art_swap_remove_in in Hb. destruct (GB b Hb) as (B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8 & B9).
repeat (split; [assumption|]). split; [|split; assumption]. unfold apart in *. lia.
- intros j1 j2 b b' H1 H2 Hne.
assert (Hj1 : (j1 < length bl - 1)%nat) by (rewrite <- (art_swap_remove_length _ (0, 0) i bl); apply nth_error_Some; congruence).
assert (Hj2 : (j2 < length bl - 1)%nat) by (rewrite <- (art_swap_remove_length _ (0, 0) i bl); apply nth_error_Some; congruence).
rewrite art_swap_remove_nth in H1 by exact Hj1. rewrite art_swap_remove_nth in H2 by exact Hj2.
apply (GD _ _ b b' H1 H2). destruct (j1 =? i)%nat eqn:E1; destruct (j2 =? i)%nat eqn:E2; try lia.
apply Nat.eqb_eq in E1. apply Nat.eqb_eq in E2. lia.
Qed.
End SE.
Lemma art_sec_geo_inj : ltac2:(TCodec.tc2 tcn__JatRecycle5A "Q0'?'5'9%1233%311&Hr5r4r3r2r1%6554321&M%13:46%23;58';&3%13AA:%23BB:%43C21%53A>=p021p081p0:1pR:E1pR8F1p0?1pR<G1pRNL1pRDM1pS0N1pQ2O1").
Proof.
intros HI t ctx parr bl (_ & _ & _ & _ & _ & _ & GB & GD) b b' Hb Hb' E.
destruct (In_nth_error _ _ Hb) as (j & Hj). destruct (In_nth_error _ _ Hb') as (j' & Hj').
destruct (Nat.eq_dec j j') as [->|NE]; [congruence|].
pose proof (GD j j' b b' Hj Hj' NE) as Ap. destruct (GB b Hb) as (_ & _ & S1 & _). destruct (GB b' Hb') as (_ & _ & S2 & _). unfold apart in Ap. lia.
Qed.
Lemma art_cls_dealloc_au : ltac2:(TCodec.tc2 tcn__JatRecycle5A "J'?'A':';&B&Jr3r2r1%43321%611%713%93<21&F%115%217%=3@21&E%119%21;%A3D21%C251%D2:1pRBF1pS2H1pR>I1").
Proof. intros c w cl. unfold art_cls_dealloc. destruct (art_cls_full c cl); cbn; auto. Qed.
Lemma art_cls_dealloc_perm : ltac2:(TCodec.tc2 tcn__JatRecycle5A "Q9'?'A&Q1&Q2&4&Cr1%211%4281%611&Gr3%211%;241':+1r4%?221+O%A231%6231'O(2&1%C1=&D%11?%43K31%63L<1&Jr5%231?D%K11%812%;3Q221%>3Q371p0@1p0H1pRBQ51pS2Q71pR>Q81").
Proof.
intros c w cl Hlen Hc. unfold art_cls_dealloc. destruct (art_cls_full c cl) eqn:EF.
- unfold art_cls_push, art_cls_return. cbn [cl_cache cl_free].
set (k := (length (cl_cache cl) - Z.to_nat (art_ic_mc c / 2))%nat).
rewrite <- (firstn_skipn k (cl_cache cl)) at 1. rewrite <- !app_assoc. cbn [app].
eapply Permutation_trans; [apply Permutation_middle|]. apply Permutation_app_head. apply perm_skip. apply Permutation_app_comm.
- unfold art_cls_push. cbn [cl_cache cl_free]. rewrite <- app_assoc. cbn [app]. apply Permutation_middle.
Qed.
Lemma art_cls_dealloc_in : ltac2:(TCodec.tc2 tcn__JatRecycle5A "Q@'?'A&Q1&Q2&4&Cr2%211%4281%611&Gr4%211%;241':+1r5%?221+O%A231%6231&<&Mr3&1&Jr6%231;@%G11&D%113%73O31%:3Q091'>';%13Q3<C%O1I%81J%>3Q621%A3Q7@1%7251%D291p0F1p0N1pS4Q<1pRBQ<1pS2Q>1pR>Q?1").
Proof.
intros c w cl x Hlen Hc. pose proof (art_cls_dealloc_perm c w cl Hlen Hc) as P. split.
- intros H. apply (Permutation_in _ (Permutation_sym P)) in H. destruct H as [<-|H]; [left; reflexivity|right; exact H].
- intros H. apply (Permutation_in _ P). destruct H as [->|H]; [left; reflexivity|right; exact H].
Qed.
Lemma art_cls_dealloc_total : ltac2:(TCodec.tc2 tcn__JatRecycle5A "Q@'?'A&Q1&Q2&4&Cr1%211%4281%611&Gr3%211%;241':+1r4%?221+O%A231%6231';&Q0&Jr5%2319>%E11%G2K1%I11&D%115%K2O1%M11%;251%M1G%O2Q31%Q111%81J%Q22Q61%Q411%B241%C21J%E3Q:91p0G1p0O1pRBQ<1pS2Q>1pR>Q?1").
Proof.
intros c w cl Hlen Hc. pose proof (Permutation_length (art_cls_dealloc_perm c w cl Hlen Hc)) as L. cbn [length] in L. rewrite !length_app in L. lia.
Qed.
Lemma art_cls_dealloc_cache_le : ltac2:(TCodec.tc2 tcn__JatRecycle5A "Q2'?'A&Q1&Q2&4&Cr1%211%4281%611&Gr3%211%;241':+1r4%?221+O%A231%6231&Jr5%2317<%C11%E2I1%G11%A15%J221p091p0A1pRBN1pS2Q01pR>Q11").
Proof.
intros c w cl Hlen Hc. destruct (art_ic_mc_half c Hc) as (Emc & Hh). unfold art_cls_dealloc. destruct (art_cls_full c cl) eqn:EF; unfold art_cls_full in EF.
- apply Z.eqb_eq in EF. unfold art_cls_push, art_cls_return. cbn [cl_cache]. rewrite length_app, length_firstn. cbn [length]. lia.
- apply Z.eqb_neq in EF. unfold art_cls_push. cbn [cl_cache]. rewrite length_app. cbn [length]. lia.
Qed.
