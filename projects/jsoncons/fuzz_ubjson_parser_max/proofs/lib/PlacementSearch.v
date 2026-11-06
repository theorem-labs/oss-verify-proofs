(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase State.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__PlacementSearch () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.LinuxProcessSem.State."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PlacementSearch."; "Stdlib.Lists.List."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["1Some"; "1app"; "1bool"; "1false"; "1list"; "1option"; "1prod"; "1true"; "2and"; "2eq"; "2ex"; "2iff"; "2or"; "3Z"; "4VmMaps"; "4alloc_top"]; ["4page_round_up_Z"; "4page_size"; "4region_free"; "4two_pow_64"; "4vm_maps"; "4vm_reserved"; "5higher_fit_b"; "5no_higher_fit"; "5place"; "5place_fits"; "5place_in_model"; "5search_candidates"; "6In"; "6existsb"; "6fold_left"; "7add"]; ["7le"; "7lt"; "7max"; "7modulo"; "7sub"; "0a"; "0aZ"; "0b"; "0baseZ"; "0g"; "0h"; "0hiZ"; "0l"; "0loZ"; "0maps"; "0nZ"]; ["0s"; "8Z_to_bv"; "8bv"; "8bv_unsigned"; "0x"; "0z"]]).
Definition no_higher_fit (maps : list (word * word)) (aZ nZ baseZ : Z)
: Prop :=
forall g : Z,
(g mod page_size = 0)%Z ->
(aZ + nZ <= g)%Z ->
(g + nZ <= baseZ)%Z ->
region_free maps (Z_to_bv 64 g) (Z_to_bv 64 nZ) = false.
Definition fit_candidates (maps : list (word * word)) (aZ nZ : Z)
: list Z :=
(aZ + nZ)%Z
:: map (fun p => page_round_up_Z (bv_unsigned (fst p)
+ bv_unsigned (snd p))%Z)
maps.
Definition higher_fit_b (maps : list (word * word)) (aZ nZ baseZ : Z)
: bool :=
existsb (fun g => (g mod page_size =? 0)%Z
&& (aZ + nZ <=? g)%Z && (g + nZ <=? baseZ)%Z
&& region_free maps (Z_to_bv 64 g) (Z_to_bv 64 nZ))
(fit_candidates maps aZ nZ).
Lemma page_round_up_Z_aligned : ltac2:(TCodec.tc2 tcn__PlacementSearch ";'='9&Q3&@r1%211&A%5221z%83921pS<:1").
Proof. intro z. unfold page_round_up_Z. apply Z_mod_mult. Qed.
Lemma page_round_up_Z_ge : ltac2:(TCodec.tc2 tcn__PlacementSearch "7'=&Q0r1&@%112%4231pS<61").
Proof.
intro z. unfold page_round_up_Z, page_size.
pose proof (Z.div_mod (z + 4096 - 1) 4096 ltac:(lia)) as H.
pose proof (Z.mod_pos_bound (z + 4096 - 1) 4096 ltac:(lia)).
lia.
Qed.
Lemma page_round_up_Z_le : ltac2:(TCodec.tc2 tcn__PlacementSearch "D'=&Q0r2r1%3221'9&Q3&A%2261z%53:21&@r4%211r3%>221p061p0=1pR@B1pS<C1").
Proof.
intros z b Hzb Hb. unfold page_round_up_Z, page_size in *.
pose proof (Z.div_mod b 4096 ltac:(lia)) as Hbm.
assert (Hq : ((z + 4096 - 1) / 4096 < b / 4096 + 1)%Z)
by (apply Z.div_lt_upper_bound; lia).
apply Z.le_trans with (m := (b / 4096 * 4096)%Z); [|lia].
apply Z.mul_le_mono_nonneg_r; lia.
Qed.
Lemma fold_max_ge_seed : ltac2:(TCodec.tc2 tcn__PlacementSearch "<'4'=%211&Q0r1&N&Q2r2%3577214%6251pS291pRJ91").
Proof.
induction l as [|x l IH]; intro s; cbn; [lia|].
pose proof (IH (Z.max s x)). lia.
Qed.
Lemma fold_max_ge_in : ltac2:(TCodec.tc2 tcn__PlacementSearch "B'4'=%211&Lr1r3%33521&Q0r2&N&Q2r4%35;;217%6251p081pS:>1pS2?1pRJ?1").
Proof.
induction l as [|y l IH]; intros s x Hin; [contradiction|].
destruct Hin as [->|Hin]; cbn.
- pose proof (fold_max_ge_seed l (Z.max s x)). lia.
- apply IH; assumption.
Qed.
Lemma fold_max_le : ltac2:(TCodec.tc2 tcn__PlacementSearch "H'4'=%211&Q0r2r1%3221&Lr5%23841r4%8271p031pS:<1&N&Q2%25??186r3%?221p061p0>1pR@D1pS2E1pRJE1").
Proof.
induction l as [|y l IH]; intros s b Hs Hl; cbn; [exact Hs|].
apply IH.
- pose proof (Hl y ltac:(now left)). lia.
- intros x Hx. apply Hl. now right.
Qed.
Lemma fold_max_in_or_seed : ltac2:(TCodec.tc2 tcn__PlacementSearch "@'4'=%211'<'9&N&Q2r2r1%4588321%63912&L%13;35%:231pS2=1pRJ=1").
Proof.
induction l as [|y l IH]; intro s; cbn; [now left|].
destruct (IH (Z.max s y)) as [Heq|Hin].
- rewrite Heq. destruct (Z.max_spec s y) as [[_ ->]|[_ ->]];
[right; now left | now left].
- right. now right.
Qed.
Lemma higher_fit_b_complete : ltac2:(TCodec.tc2 tcn__PlacementSearch "QN'4'6'QByR0%211%4211%611'=&Q0z&Or4r3%3221%6251&Q1%1275'9&Q3r6&A%3221%53?1=&C%9251r:r9%A221r7%E221r8%E216%H216'2&Br=&QA%12Q2;r;%32Q41%63531(7%I3921&Fr>r<%342;18%N3>16p061p0A1p0E1p0M1p0L1p0O1p0Q01p0Q71p0Q:1pRDQB1pRBQC1pS0QD1pR>QE1pRNQG1").
Proof.
intros maps aZ nZ baseZ g HaPos HnPos HaAl HnAl Hbase HgAl Hglo Hghi
Hgfree.
assert (Hmod : two_pow_64 = bv_modulus 64) by reflexivity.
assert (HgW : bv_unsigned (Z_to_bv 64 g) = g)
by (clear HaAl HnAl HgAl Hgfree; rewrite Z_to_bv_unsigned; apply bv_wrap_small; lia).
assert (HnW : bv_unsigned (Z_to_bv 64 nZ) = nZ)
by (clear HaAl HnAl HgAl Hgfree; rewrite Z_to_bv_unsigned; apply bv_wrap_small; lia).
set (cs := List.filter (fun c => (c <=? g)%Z) (fit_candidates maps aZ nZ)).
set (g' := fold_left Z.max cs (aZ + nZ)%Z).
assert (Hcs : forall x, In x cs <->
In x (fit_candidates maps aZ nZ) /\ (x <=? g)%Z = true)
by (intro x0; unfold cs; exact (filter_In _ x0 _)).
assert (Hlo : (aZ + nZ <= g')%Z) by (unfold g'; apply fold_max_ge_seed).
assert (Hhi : (g' <= g)%Z).
{ unfold g'. apply fold_max_le; [lia|]. intros x Hx.
apply Hcs in Hx. destruct Hx as [_ Hx]. now apply Z.leb_le. }
assert (Hcand : In g' (fit_candidates maps aZ nZ)).
{ destruct (fold_max_in_or_seed cs (aZ + nZ)%Z) as [Heq|Hin].
- assert (Heq' : g' = (aZ + nZ)%Z) by exact Heq.
rewrite Heq'. now left.
- apply Hcs in Hin. exact (proj1 Hin). }
assert (Hg'W : bv_unsigned (Z_to_bv 64 g') = g')
by (clear HaAl HnAl HgAl; rewrite Z_to_bv_unsigned; apply bv_wrap_small; lia).
assert (Hg'Al : (g' mod page_size = 0)%Z).
{ destruct Hcand as [Heq|Hin].
- rewrite <- Heq.
rewrite Z.add_mod, HaAl, HnAl by (unfold page_size; lia).
reflexivity.
- apply in_map_iff in Hin. destruct Hin as (p & Heq & _).
rewrite <- Heq. apply page_round_up_Z_aligned. }
assert (Hg'free : region_free maps (Z_to_bv 64 g') (Z_to_bv 64 nZ)
= true).
{ apply region_free_intro. intros b s Hin.
pose proof (region_free_In _ _ _ _ _ Hgfree Hin) as Hno.
unfold iv_overlap in *. rewrite HgW, HnW in Hno.
rewrite Hg'W, HnW.
apply andb_false_iff in Hno.
set (B := bv_unsigned b) in *. set (S := bv_unsigned s) in *.
destruct (Z.le_gt_cases (B + S) g) as [Hend|Hend].
-
assert (Hc : In (page_round_up_Z (B + S)) (fit_candidates maps aZ nZ)).
{ right. apply in_map_iff. exists (b, s).
split; [reflexivity|assumption]. }
assert (Hcle : (page_round_up_Z (B + S) <= g)%Z)
by (apply page_round_up_Z_le; assumption).
assert (Hcg' : (page_round_up_Z (B + S) <= g')%Z).
{ unfold g'. apply fold_max_ge_in. apply Hcs. split; [assumption|].
now apply Z.leb_le. }
pose proof (page_round_up_Z_ge (B + S)) as Hround.
apply andb_false_iff. left. apply Z.ltb_ge.
exact (Z.le_trans _ _ _ Hround Hcg').
-
destruct Hno as [Hno|Hno].
+ apply Z.ltb_ge in Hno. lia.
+ apply Z.ltb_ge in Hno.
apply andb_false_iff. right. apply Z.ltb_ge.
exact (Z.le_trans _ _ _
(Z.add_le_mono _ _ _ _ Hhi (Z.le_refl nZ)) Hno). }
unfold higher_fit_b. apply existsb_exists. exists g'.
split; [exact Hcand|].
assert (Hg'base : (g' + nZ <= baseZ)%Z)
by exact (Z.le_trans _ _ _
(Z.add_le_mono _ _ _ _ Hhi (Z.le_refl nZ)) Hghi).
rewrite Hg'free.
rewrite (proj2 (Z.eqb_eq _ _) Hg'Al).
rewrite (proj2 (Z.leb_le _ _) Hlo).
rewrite (proj2 (Z.leb_le _ _) Hg'base).
reflexivity.
Qed.
Lemma higher_fit_b_sound : ltac2:(TCodec.tc2 tcn__PlacementSearch "QA'4'6'QByR0%211%4211%611'='9'2&Fr4r3r2r1%544321(7%93821':'8&Q3&A%2281z%@3A21&Q0&Or5%221A%421?%42@C%621C&Br6&QA%12Q0E%22Q1I%53421%N3M1F%D281%E2;1%F2A1qRDQ31%I2Q41p0K1pRBQ61pS0Q71pR>Q81pRNQ:1").
Proof.
intros maps aZ nZ baseZ H.
unfold higher_fit_b in H. apply existsb_exists in H as (g & _ & Hg).
apply andb_true_iff in Hg as [Hg Hfree].
apply andb_true_iff in Hg as [Hg Hhi].
apply andb_true_iff in Hg as [Hal Hlo].
exists g. repeat split.
- now apply Z.eqb_eq.
- now apply Z.leb_le.
- now apply Z.leb_le.
- exact Hfree.
Qed.
Lemma no_higher_fit_iff : ltac2:(TCodec.tc2 tcn__PlacementSearch "Q<'4'6'QByR0%211%4211%611'=&Q0zr3%3221&Q1%1243'9&Q3r5&A%3221%53<1:&C%9251&;'2&Fr9r8r7r6%544321(3%A3821&G%148765%<231p0>1p0A1p0B1p0I1p0L1pRBQ11pS0Q21pR>Q31pRNQ51").
Proof.
intros maps aZ nZ baseZ HaPos HnPos HaAl HnAl Hbase. split.
- intros Hf g HgAl Hglo Hghi.
destruct (region_free maps (Z_to_bv 64 g) (Z_to_bv 64 nZ)) eqn:Hfree;
[|reflexivity].
exfalso.
rewrite (higher_fit_b_complete maps aZ nZ baseZ g
ltac:(lia) HnPos HaAl HnAl Hbase HgAl Hglo Hghi Hfree)
in Hf.
discriminate.
- intro H. destruct (higher_fit_b maps aZ nZ baseZ) eqn:Hf;
[|reflexivity].
exfalso. apply higher_fit_b_sound in Hf as (g & HgAl & Hglo & Hghi & Hfree).
rewrite (H g HgAl Hglo Hghi) in Hfree. discriminate.
Qed.
Definition search_candidates (maps : list (word * word)) (loZ : Z)
: list Z :=
loZ :: map (fun p => page_round_up_Z (bv_unsigned (fst p)
+ bv_unsigned (snd p))%Z)
maps.
Definition place_fits (maps : list (word * word)) (loZ hiZ nZ : Z) (g : Z)
: bool :=
(g mod page_size =? 0)%Z && (loZ <=? g)%Z && (g + nZ <=? hiZ)%Z
&& region_free maps (Z_to_bv 64 g) (Z_to_bv 64 nZ).
Definition place (maps : list (word * word)) (loZ hiZ nZ : Z)
: option Z :=
find (place_fits maps loZ hiZ nZ) (search_candidates maps loZ).
Lemma place_sound : ltac2:(TCodec.tc2 tcn__PlacementSearch "QB'4'6'QByR0%211%4211%611'='9'5%113&Hr5r4r3r2%544321(0r1%22<1%<3:41'8&Q3&A%2291z%B3C21&Q0%12@=&O%12?@%421B'2&Br6&QA%12Q1E%22Q2G%53421(7%Q03821%D2:1%E2>1%F2A1p0H1pR<Q61pS0Q71pRHQ81pRLQ91pRNQ;1").
Proof.
intros maps loZ hiZ nZ a H.
unfold place in H. apply find_some in H as [_ Hf].
unfold place_fits in Hf.
apply andb_true_iff in Hf as [Hf Hfree].
apply andb_true_iff in Hf as [Hf Hhi].
apply andb_true_iff in Hf as [Hal Hlo].
repeat split.
- now apply Z.eqb_eq.
- now apply Z.leb_le.
- now apply Z.leb_le.
- exact Hfree.
Qed.
Lemma existsb_find : forall {A} (f : A -> bool) l,
existsb f l = true -> exists x, find f l = Some x.
Proof.
intros A f l. induction l as [|y l IH]; cbn; [discriminate|].
destruct (f y) eqn:Hy; [intros _; now exists y|].
cbn. exact IH.
Qed.
Lemma higher_fit_b_as_place : ltac2:(TCodec.tc2 tcn__PlacementSearch "M'4'6'QByR0%211%4211%611'='9'2&Fr4&Q4r3r1%3221r2%746231&M&I%149746&K%12;9%53@31%@3?71pS0B1pRHC1pRLD1pRNF1").
Proof.
intros maps loZ hiZ nZ.
unfold higher_fit_b, place_fits, search_candidates, fit_candidates.
replace (loZ - nZ + nZ)%Z with loZ by lia.
reflexivity.
Qed.
Lemma place_complete : ltac2:(TCodec.tc2 tcn__PlacementSearch "R7'4'6'QByR0%211%4211%611'=&Q0zr4%3221&Q1r3%2251'9&Q3r6&A%3221%53=1;r5%6214%83@1>r7&C%>221r:%D214&Or8r9%3221%I216'2&Br=&QA%12Q37%22Q4<%53421(7%K3821':'5%11Q6&Hr?r>r<%4432>1(0r1%22Q>1%Q73941qR<Q@1%=2QA1p0?1p0I1p0O1p0Q81p0Q31p0Q71p0Q;1p0QB1p0QF1pRDQK1pS0QL1pRHQM1pRLQN1pRNR01").
Proof.
intros maps loZ hiZ nZ g Hlo0 Hn Hloal Hnal Hhi HgAl Hglo Hghi Hfree.
apply existsb_find. rewrite <- higher_fit_b_as_place.
apply (higher_fit_b_complete maps (loZ - nZ) nZ hiZ g).
- lia.
- exact Hn.
- rewrite Zminus_mod, Hloal, Hnal. reflexivity.
- exact Hnal.
- exact Hhi.
- exact HgAl.
- lia.
- exact Hghi.
- exact Hfree.
Qed.
Definition place_in_model (h : VmMaps) (nZ : Z) : option Z :=
place (vm_reserved h ++ vm_maps h) page_size (alloc_top h) nZ.
Lemma place_in_model_admissible : ltac2:(TCodec.tc2 tcn__PlacementSearch "QL'>'=&Q0zr2%3221'9'5%117&Jr4r3%3221(0%12=:%93731'8&QCyR0&QA%1229%4231%@3E1;&Q3&A%2241%D3I1G&Q1%12I7&O%129D&?r5%211%Q0241'2&B&1'6'QB%11F%3211&E%11;&D%11=%93531%L2MQ5%<32L1(7%Q<3?21%Q32A1%Q42H1%Q52K1%Q62Q01p0Q81p0QC1pR<QH1pS0QI1pRFQK1").
Proof.
intros h nZ a Hn H. unfold place_in_model in H.
destruct (place_sound _ _ _ _ _ H) as (Hal & Hlo & Hhi & Hfree).
pose proof (alloc_top_lt h) as Htop. unfold two_pow_64 in Htop.
assert (Hrt : bv_unsigned (Z_to_bv 64 a) = a).
{ rewrite Z_to_bv_unsigned. apply bv_wrap_small.
unfold bv_modulus. unfold page_size in Hlo. cbn. lia. }
rewrite Hrt. repeat split; try assumption.
unfold page_size in Hlo. lia.
Qed.
Example place_accepts_a_negative_length :
place_in_model (mkVmMaps [] [] 0 0 0) (-4096) = Some 4096%Z.
Proof. vm_compute. reflexivity. Qed.
Lemma place_in_model_complete : ltac2:(TCodec.tc2 tcn__PlacementSearch "R1'>'=&Q1zr2%3221'9&Q3r3&A%3221%53:18&Q0r4%2251&Or5r6%3221&?r7%211%:241'2&B&1'6'QByR0%211%4211&Er8%211&D%113%;3631&QA%12:E%22;C%@3421(7%Q43C21':'5%11Q<&Jr:r9%3221(0r1%22QC1%Q?3841qR<QE1%<2QF1p0>1p0Q31p0Q<1p0Q@1p0QA1p0QH1pRDQM1pS0QN1pRFR01").
Proof.
intros h nZ g Hn Hnal HgAl Hglo Hghi Hfree.
unfold place_in_model.
apply (place_complete _ _ _ _ g); try assumption.
- unfold page_size. lia.
- unfold page_size. reflexivity.
- exact (alloc_top_lt h).
Qed.
Definition witness_ledger : list (word * word) :=
[(Z_to_bv 64 4096, Z_to_bv 64 8192)].
Definition demo_top : Z := alloc_top (mkVmMaps [] [] 0 0 0).
Example place_skips_the_occupied_floor :
place witness_ledger page_size demo_top 4096 = Some 12288%Z.
Proof. vm_compute. reflexivity. Qed.
Example place_complete_premises_are_satisfiable :
(0 <= page_size)%Z /\ (0 < 4096)%Z
/\ (page_size mod page_size = 0)%Z /\ (4096 mod page_size = 0)%Z
/\ (demo_top < two_pow_64)%Z
/\ (12288 mod page_size = 0)%Z /\ (page_size <= 12288)%Z
/\ (12288 + 4096 <= demo_top)%Z
/\ region_free witness_ledger (Z_to_bv 64 12288) (Z_to_bv 64 4096) = true.
Proof.
unfold page_size, demo_top, two_pow_64. rewrite alloc_top_mkVmMaps.
repeat split; try (vm_compute; reflexivity); try lia.
Qed.
Definition full_ledger : list (word * word) :=
[(Z_to_bv 64 4096, Z_to_bv 64 (demo_top - 4096))].
Example place_finds_nothing_when_full :
place full_ledger page_size demo_top 4096 = None.
Proof. vm_compute. reflexivity. Qed.
