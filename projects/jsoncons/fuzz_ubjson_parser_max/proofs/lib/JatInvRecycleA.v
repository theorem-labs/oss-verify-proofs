(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import PropExec CatSim StoreOk As0Tables ArtMem JatInitCache JatPopulate1 ArtRuns JatCls JatFp JatClsRep JatSecAllocPost JatFxQ
JatRecycle2C JatRecycle3L JatRecycle5A JatRecycle5I JatRecycle5T JatInv.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLia. Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLiaT. From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__JatInvRecycleA () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Lists.ListDef."; "Corelib.Numbers.BinNums."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.ArtMem."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.As0Tables.AsanTab."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.JatCls."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.JatInvRecycleA."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.JatRecycle3L."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.JatRecycle5A."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.JatRecycle5I."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.JatRecycle5T."; "Stdlib.Lists.List."; "Stdlib.ZArith.BinInt.Z."], [["1app"; "1fst"; "1list"; "1pair"; "1prod"; "1snd"; "2and"; "2eq"; "2ex"; "2not"; "3map"; "4Z"; "0G"; "5apart"; "6class_size"; "7art_cptr_ok"]; ["7cl_au"; "7cl_cache"; "7cl_free"; "8art_rel_key"; "8art_rg_ok"; "9art_cls_dealloc"; ":art_cls_upd"; ":art_rel"; ":art_rel_step"; ":art_rel_zone"; ":art_rg"; ":rg_cls"; ";art_rel_pre"; "<art_rels_pre"; "<art_rels_sep"; "<art_zapart"]; ["=In"; "=NoDup"; ">add"; ">le"; ">mul"; ">pow"; "0c"; "0c'"; "0c0"; "0e"; "0e'"; "0e0"; "0es"; "0i"; "0spb"; "0sz"]; ["0w"; "0w'"; "0w0"]]).
Local Ltac lia := L5FastLiaT.plia1.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Definition art_sec_b (s : art_sec) : Z * Z := (sc_map s, sc_msize s).
Definition art_rel_key (e : art_rel) : Z * Z := match e with REP c w _ _ _ => (c, w) | RES mb _ _ _ _ => (0, mb) | REB wb => (24, wb) end.
Definition art_rg_ok (G : art_rg) : Prop :=
(forall c, 1 <= c <= 30 -> Z.of_nat (length (cl_cache (rg_cls G c))) <= art_ic_mc c)
/\ (forall b b', In b (rg_bl G) -> In b' (rg_bl G) -> fst b = fst b' -> b = b').
Lemma art_rg_ok_step : ltac2:(TCodec.tc2 tcn__JatInvRecycleA "A'G'J&Dr1%211&Lr2r3%3221&Hr4%2214%:11p051p0:1pJ>1pRD@1").
Proof.
intros e G (CK & INJ) PRE. destruct e as [c w d b1 n|mb ms m b1 n|wb]; cbn [art_rel_step art_rel_pre] in *.
- split; [|exact INJ]. cbn [rg_cls]. intros c' Hc'. destruct (Z.eq_dec c' c) as [->|NE].
+ rewrite art_cls_upd_same. apply art_cls_dealloc_cache_le; [apply CK; exact Hc'|lia].
+ rewrite art_cls_upd_other by exact NE. apply CK. exact Hc'.
- split; [exact CK|]. cbn [rg_bl]. intros b b' Hb Hb'. apply INJ; eapply art_swap_remove_in; eassumption.
- split; [|exact INJ]. cbn [rg_cls]. intros c' Hc'. destruct (Z.eq_dec c' 24) as [->|NE].
+ rewrite art_cls_upd_same. apply art_cls_dealloc_cache_le; [apply CK; exact Hc'|lia].
+ rewrite art_cls_upd_other by exact NE. apply CK. exact Hc'.
Qed.
Lemma art_pre_cls_other : ltac2:(TCodec.tc2 tcn__JatInvRecycleA "R5'J';&Dr6%211'6&Q3+1%2215+N%4271%6231&9'7'4%12>>(3r7%24AA1?r5r4%54DD21%93741%;11&?&@&Kr9%221I%411%63:1;&Q0&0&Ar:%921B%311&B%113%73Q631%93Q7Q51%M11&Fr;%B11&E%D23<%23=D1r8%745?21%I11%K3Q@1Q2%C13%@14%F3QE21%H3QFQ61%Q<11%QD261p0A1p0M1p0Q51p0QB1p0QJ1pS0QN1pS2QO1pR>R01pS6R11pRBR21pJR41").
Proof.
intros G c0 w0 c w sz (CK & _) Hc0 NE OKw NIN. destruct (Z.eq_dec c c0) as [->|NEc].
- rewrite art_cls_upd_same. destruct (art_cls_dealloc_au c0 w0 (rg_cls G c0)) as (Ea & _). rewrite Ea. split; [exact OKw|].
intros Hin. apply (art_cls_dealloc_in c0 w0 (rg_cls G c0) w (CK c0 Hc0) ltac:(lia)) in Hin. destruct Hin as [E|Hin]; [apply NE; rewrite E; reflexivity|exact (NIN Hin)].
- rewrite art_cls_upd_other by exact NEc. split; assumption.
Qed.
Lemma art_rel_pre_other : ltac2:(TCodec.tc2 tcn__JatInvRecycleA "Q2'G'J&Dr1%211&Lr2r4%3221r3%5213&9'7'4';%2211&Cr6%211r5%411%93631%;11&Hr7%2216%E219p051p0B1p0E1p0J1pJN1pRDQ01pRHQ11").
Proof.
intros e0 e G OK P0 P NE. pose proof OK as (CK & INJ).
destruct e as [c w d b1 n|mb ms m b1 n|wb]; cbn [art_rel_pre art_rel_key] in P, NE |- *.
- destruct P as (Hc & OKw & NIN & REST).
destruct e0 as [c0 w0 d0 b10 n0|mb0 ms0 m0 b10 n0|wb0]; cbn [art_rel_step art_rel_pre art_rel_key rg_cls] in P0, NE |- *.
+ destruct P0 as (Hc0 & _). destruct (art_pre_cls_other G c0 w0 c w _ OK Hc0 NE OKw NIN) as (X1 & X2). split; [exact Hc|]. split; [exact X1|]. split; [exact X2|exact REST].
+ split; [exact Hc|]. split; [exact OKw|]. split; [exact NIN|exact REST].
+ destruct (art_pre_cls_other G 24 wb0 c w _ OK ltac:(lia) NE OKw NIN) as (X1 & X2). split; [exact Hc|]. split; [exact X1|]. split; [exact X2|exact REST].
- destruct P as (Hin & REST).
destruct e0 as [c0 w0 d0 b10 n0|mb0 ms0 m0 b10 n0|wb0]; cbn [art_rel_step art_rel_pre art_rel_key rg_bl] in P0, NE |- *; try (split; [exact Hin|exact REST]).
destruct P0 as (Hin0 & _). split; [|exact REST].
pose proof (art_bl_idx_nth (rg_bl G) mb0 ms0 Hin0 INJ) as Hn.
apply art_swap_remove_keeps; [apply nth_error_Some; rewrite Hn; discriminate|exact Hin|].
rewrite (nth_error_nth _ _ (0, 0) Hn). intros E. apply NE. injection E as E1 _. rewrite E1. reflexivity.
- destruct P as (OKw & NIN).
destruct e0 as [c0 w0 d0 b10 n0|mb0 ms0 m0 b10 n0|wb0]; cbn [art_rel_step art_rel_pre art_rel_key rg_cls] in P0, NE |- *.
+ destruct P0 as (Hc0 & _). exact (art_pre_cls_other G c0 w0 24 wb _ OK Hc0 NE OKw NIN).
+ split; assumption.
+ exact (art_pre_cls_other G 24 wb0 24 wb _ OK ltac:(lia) NE OKw NIN).
Qed.
Lemma art_rels_pre_intro : ltac2:(TCodec.tc2 tcn__JatInvRecycleA "O'2'G%211'J&Dr1%211&Q0r4%23841&Lr2%2241p041pRD=1'Q1'4';%2211&:&C%24D31=%7241&Mr5%22A1p041p0=1p0F1pJJ1pRJL1").
Proof.
induction es as [|e0 r IH]; intros G OK PRE ND; cbn [art_rels_pre]; [exact I|].
cbn [map] in ND. inversion ND as [|? ? Hnin NDr]; subst.
split; [apply PRE; left; reflexivity|].
apply IH; [apply art_rg_ok_step; [exact OK|apply PRE; left; reflexivity]| |exact NDr].
intros e He. apply art_rel_pre_other; [exact OK|apply PRE; left; reflexivity|apply PRE; right; exact He|].
intros E. apply Hnin. rewrite E. apply in_map. exact He.
Qed.
Lemma art_nodup_map_of : forall (A B C : Type) (f : A -> B) (g : A -> C) (l : list A),
(forall x y, In x l -> In y l -> g x = g y -> f x = f y) -> List.NoDup (map f l) -> List.NoDup (map g l).
Proof.
intros A B C f g l. induction l as [|a r IH]; intros INJ ND; cbn [map] in *; [constructor|].
inversion ND as [|? ? Hnin NDr]; subst. constructor.
- intros Hin. apply in_map_iff in Hin. destruct Hin as (y & Ey & Hy). apply Hnin. rewrite <- (INJ y a (or_intror Hy) (or_introl eq_refl) Ey). apply in_map. exact Hy.
- apply IH; [|exact NDr]. intros x y Hx Hy. apply INJ; right; assumption.
Qed.
Lemma art_nodup_flat_snoc : forall (A B : Type) (f : A -> list B) (g : A -> B) (l : list A),
List.NoDup (flat_map f l) -> List.NoDup (map g l) -> (forall b b', In b l -> In b' l -> ~ In (g b) (f b')) ->
List.NoDup (flat_map (fun b => f b ++ [g b]) l).
Proof.
intros A B f g l. induction l as [|a r IH]; intros NDf NDg NX; cbn [flat_map map] in *; [constructor|].
inversion NDg as [|? ? Hnin NDr]; subst.
apply NoDup_app_remove_l in NDf as NDfr. pose proof NDf as NDf0.
assert (IHr : List.NoDup (flat_map (fun b => f b ++ [g b]) r)) by (apply IH; [exact NDfr|exact NDr|intros b b' Hb Hb'; apply NX; right; assumption]).
rewrite <- app_assoc. cbn [app].
assert (INr : forall x, In x (flat_map (fun b => f b ++ [g b]) r) -> In x (flat_map f r) \/ In x (map g r)).
{ intros x Hx. apply in_flat_map in Hx. destruct Hx as (b & Hb & Hx). apply in_app_or in Hx. destruct Hx as [Hx|[<-|[]]].
- left. apply in_flat_map. exists b. split; assumption.
- right. apply in_map. exact Hb. }
apply List.NoDup_app; [exact (NoDup_app_remove_r _ _ NDf0)| |].
- constructor; [|exact IHr]. intros Hx. destruct (INr _ Hx) as [Hx'|Hx']; [|exact (Hnin Hx')].
apply in_flat_map in Hx'. destruct Hx' as (b' & Hb' & Hx'). exact (NX a b' (or_introl eq_refl) (or_intror Hb') Hx').
- intros x Hx [<-|Hx2]; [exact (NX a a (or_introl eq_refl) (or_introl eq_refl) Hx)|].
destruct (INr _ Hx2) as [Hx'|Hx'].
+ revert Hx Hx'. clear - NDf0. intros Hx Hx'. induction (f a) as [|y s IHs]; [destruct Hx|]. cbn [app] in NDf0. inversion NDf0 as [|? ? Hn Nd]; subst.
destruct Hx as [<-|Hx]; [apply Hn; apply in_or_app; right; exact Hx'|exact (IHs Nd Hx)].
+ apply in_map_iff in Hx'. destruct Hx' as (b' & Eb' & Hb'). rewrite <- Eb' in Hx. exact (NX b' a (or_intror Hb') (or_introl eq_refl) Hx).
Qed.
Lemma art_swap_remove_map : forall (A B : Type) (f : A -> B) (d : A) i l, map f (art_swap_remove d i l) = art_swap_remove (f d) i (map f l).
Proof.
intros A B f d i l. unfold art_swap_remove. rewrite map_map, length_map. apply map_ext. intros j. symmetry. apply map_nth.
Qed.
Lemma art_chunk_apart : ltac2:(TCodec.tc2 tcn__JatInvRecycleA "RL';'6&Q3+1r4%3221+N%5231%7231r3%8271%9225%;221zr5%=221&Q2&Q4+@r6%3221&>r7%211%8241+S`PPPP0%H221'8'7r8%=2<1r9%;11r1%A221%73Q351qRLQ41%:2Q51%Q42IC%F2EA%C1;%I221%Q821A%J2I<r:%H11%M21=%C3Q?41qRLQ@1%F2QA1&9'4%12QDQD(3r<r;%34QHQH21%44QIQI=J%N3621%911&=r>r=&Q5+2+Q0%3221%QB251%QD271%QD2QC?%QF221%QB19%QG2A6%QI2<1%QI2QHN%QK221%QG1E%A47621p0C1p0N1p0Q61p0Q;1p0Q=1p0QI1p0R51p0R91p0R>1pS4RG1pR@RH1pS2RI1pR>RJ1pRNRK1").
Proof.
intros spb c w c' w' Hc Hc' Hw Hwu (i & Ei) Hw' Hwu' (i' & Ei') NE. unfold apart.
destruct (art_class_size_facts c Hc) as (S1 & _). destruct (art_class_size_facts c' Hc') as (S1' & _).
destruct (Z.eq_dec c c') as [->|NEc]; [|lia].
assert (NEw : w <> w') by (intros ->; apply NE; reflexivity).
assert (NEi : i <> i') by (intros ->; apply NEw; lia).
set (sz := AsanTab.class_size c') in *. rewrite Ei, Ei'. nia.
Qed.
Lemma art_rels_sep_intro : ltac2:(TCodec.tc2 tcn__JatInvRecycleA "Q<';'2'G%211&Q0r2r3%33521r4%53741&9'7'4%12==&C%117%21:%63421%811&Or7r5&1&I%124@%33II1&5%13KK3%948731p0;1p0E1p0H1pRFN1pRDO1'Q1&:%14Q2GFO%32H1&N%12OQ1p031p081pRJQ71pRNQ;1").
Proof.
intros spb es. induction es as [|e0 r IH]; intros Z ND; cbn [art_rels_sep]; [exact I|].
cbn [map] in ND. inversion ND as [|? ? Hn Nd]; subst. split.
- apply Forall_forall. intros e' He'. apply Z; [left; reflexivity|right; exact He'|]. intros E. apply Hn. rewrite E. apply in_map. exact He'.
- apply IH; [|exact Nd]. intros e e' He He'. apply Z; right; assumption.
Qed.
