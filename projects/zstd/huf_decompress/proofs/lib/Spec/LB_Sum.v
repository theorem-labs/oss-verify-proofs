(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (35 recorded proofs replaced by written proofs (zsum_app, zsum_perm, zsum_map_perm and 32 more)). *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool Lia Permutation.
From stdpp Require Import gmap.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Spec Require Import STree Malloc MI_Inv LB_Inv.
From OSSVerify.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_LB_Sum () := "K47Corelib4Init5Logic2eq01I47Corelib7Numbers7BinNums1Z00K47Corelib7Numbers7BinNums1Z01C47Corelib7Classes9Morphisms6ProperC47Corelib7Classes?RelationClasses9ReflexiveC47Corelib7Program6Basics4flipC47Corelib7Classes9MorphismsGrewrite_relation_eq_domC47Corelib7Classes9MorphismsKrespectful_per_obligation_1C35stdpp8fin_maps8map_foldI35stdpp9countable9Countable00C35stdpp4base;RelDecisionC35stdpp8fin_maps7MapFoldI35stdpp8fin_maps6FinMap00C35stdpp8fin_maps:map_insertC35stdpp4base5EmptyC35stdpp4base4FMapC35stdpp4base4OMapC35stdpp4base6LookupC35stdpp4base6InsertC35stdpp4base<PartialAlterC35stdpp4base5MergeI35stdpp4gmap4gmap00C35stdpp4base4fmapC35stdpp8fin_maps:map_eq_iffC47Corelib4Init5Logic8eq_ind_rC46Stdlib5Lists4List8map_consC35stdpp8fin_mapsAmap_to_list_emptyC35stdpp4gmap;gmap_lookupC35stdpp4gmap:gmap_emptyC35stdpp4gmapBgmap_partial_alterC35stdpp4gmap9gmap_foldI47Corelib4Init9Datatypes4list00C59OSSVerify5KrLib4Spec6MI_Inv4zsumC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3addK47Corelib4Init9Datatypes4list01K46Stdlib9micromega6VarMap1t02I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr03K46Stdlib9micromega=RingMicromega7Formula01C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerI47Corelib4Init5Logic2eq00C46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundK47Corelib4Init9Datatypes4list02K46Stdlib9micromega6VarMap1t03K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums8positive01c59OSSVerify5KrLib4Spec6LB_Sum9zsum_consC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes8list_indC47Corelib4Init9Datatypes3appK46Stdlib9micromega5Tauto8GFormula04C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01I46Stdlib9micromega:ZMicromega;ZArithProof00K47Corelib7Numbers7BinNums8positive03K46Stdlib9micromega=RingMicromega3Op201I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01c59OSSVerify5KrLib4Spec6LB_Sum8zsum_nilC1?~~~~~~~~~~~~~~~I46Stdlib7Sorting;Permutation;Permutation00K47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01K47Corelib4Init9Datatypes3nat02K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz04K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K47Corelib4Init9Datatypes6option02C46Stdlib7Sorting;Permutation?Permutation_indK46Stdlib9micromega5Tauto8GFormula08K47Corelib4Init9Datatypes3nat01K46Stdlib9micromega:ZMicromega;ZArithProof01C47Corelib5Lists7ListDef3mapC46Stdlib7Sorting;Permutation?Permutation_mapc59OSSVerify5KrLib4Spec6LB_Sum9zsum_permC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List2InC46Stdlib5Lists4List:map_ext_inC35stdpp7tactics<f_equal_helpC56Stdlib6ZArith6BinInt1Z2leK46Stdlib9micromega6VarMap1t01I47Corelib4Init5Logic2or00K47Corelib4Init5Logic2or01K47Corelib4Init5Logic2or02K46Stdlib9micromega=RingMicromega3Op203I47Corelib4Init5Logic5False00C56Stdlib6ZArith6BinInt1Z3mulK46Stdlib9micromega7EnvRing5PExpr05C59OSSVerify5KrLib4Spec6LB_Inv4zlenC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes6lengthC56Stdlib6ZArith6BinInt1Z6of_natK47Corelib7Numbers7BinNums1Z02C47Corelib4Init5Logic8iff_reflC46Stdlib9micromega;ZifyClasses3injC46Stdlib9micromega;ZifyClasses5mkrelC56Stdlib6ZArith4Znat5Nat2Z9is_nonnegC46Stdlib9micromega;ZifyClasses;rew_iff_revC46Stdlib9micromega;ZifyClasses5mkappC46Stdlib9micromega;ZifyClasses6mkapp2I47Corelib4Init9Datatypes3nat00C56Stdlib6ZArith4Znat5Nat2Z8inj_succC46Stdlib9micromega8ZifyInst7Inj_Z_ZC46Stdlib5Lists4List6filterC46Stdlib5Lists4List8flat_mapC46Stdlib5Lists4List7map_appc59OSSVerify5KrLib4Spec6LB_Sum8zsum_appC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List8in_splitC46Stdlib7Sorting;PermutationBPermutation_middleC47Corelib4Init5Logic3notI47Corelib4Init6Specif7sumbool00I47Corelib4Init5Logic2ex00I47Corelib4Init5Logic3and00C46Stdlib7Sorting;Permutation?Permutation_symK47Corelib4Init5Logic3and01K47Corelib4Init5Logic2ex01c59OSSVerify5KrLib4Spec6LB_Sum?zsum_map_nonnegC1?~~~~~~~~~~~~~~~C46Stdlib7Sorting;Permutation>Permutation_inc59OSSVerify5KrLib4Spec6LB_Sum?zsum_map_removeC1?~~~~~~~~~~~~~~~I46Stdlib5Lists4List5NoDup00C46Stdlib5Lists4List>NoDup_cons_iffC47Corelib4Init5Logic9False_indC46Stdlib5Lists4List:length_appC47Corelib4Init3Nat3addC56Stdlib5Arith8PeanoNat3Nat3addC56Stdlib6ZArith4Znat5Nat2Z7inj_addC46Stdlib7Sorting;PermutationBPermutation_lengthC46Stdlib5Lists4List:length_mapC59OSSVerify5KrLib4Spec6LB_Inv6zcountC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic6eq_indc59OSSVerify5KrLib4Spec6LB_Sum>zcount_eq_zsumC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec6LB_Sum;zlen_nonnegC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec6LB_Sum9zlen_consC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec6LB_Sum;zcount_consC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes:comparison00K47Corelib4Init9Datatypes:comparison01K47Corelib4Init9Datatypes:comparison03I47Corelib4Init5Logic4True00K47Corelib4Init5Logic4True01c59OSSVerify5KrLib4Spec6LB_Sum=zsum_map_permC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec6LB_Sum<zsum_map_extC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec6LB_Sum;zsum_map_leC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4bool02c59OSSVerify5KrLib4Spec6LB_Sum:zcount_appC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec6LB_Sum=zcount_nonnegC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec6LB_Sum;zsum_inj_leC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec6LB_Sum>zsum_map_constC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List7existsbC47Corelib7Classes?RelationClassesCPreOrder_TransitiveC46Stdlib5Lists4List<NoDup_filterC46Stdlib5Lists4List9filter_InC56Stdlib6ZArith6BinInt1Z7le_reflC47Corelib7Classes?RelationClasses<transitivityC56Stdlib6ZArith6BinInt1Z;le_preorderC46Stdlib5Lists4List2hdC47Corelib7Classes9MorphismsCeq_rewrite_relationC47Corelib4Init9Datatypes3fstC35stdpp8fin_maps:map_deleteC35stdpp8fin_maps;map_to_listC35stdpp4gmap9gmap_fmapC35stdpp4gmap9gmap_omapC35stdpp4gmap:gmap_mergeC35stdpp8fin_mapsANoDup_map_to_listC35stdpp4base6ElemOfC35stdpp4gmap;gmap_finmapC35stdpp4base6DeleteI35stdpp4base<list_elem_of00C35stdpp4base?list_elem_of_InC35stdpp4base?NoDup_ListNoDupC35stdpp8fin_mapsCelem_of_map_to_listC35stdpp8fin_maps@lookup_delete_eqC35stdpp8fin_maps@insert_delete_eqC35stdpp8fin_maps@insert_delete_idC35stdpp8fin_mapsENoDup_fst_map_to_listC35stdpp8fin_mapsBmap_to_list_insertI47Corelib4Init9Datatypes4prod00I35stdpp4base5NoDup00K47Corelib4Init9Datatypes4prod01C35stdpp4base7elem_ofC47Corelib4Init5Logic3iffC47Corelib7Classes?RelationClasses8symmetryI47Corelib4Init9Datatypes6option00C35stdpp4base6lookupK47Corelib4Init9Datatypes6option01C47Corelib7Classes9Morphisms?eq_proper_proxyC47Corelib7Classes9MorphismsMtrans_co_eq_inv_impl_morphismC47Corelib7Classes?RelationClasses>iff_TransitiveC47Corelib7Classes?RelationClasses=iff_SymmetricC35stdpp4base6deleteC35stdpp4base6insertC47Corelib7Classes9Morphisms:respectfulC47Corelib7Classes?RelationClasses>flip_ReflexiveC47Corelib7Classes9MorphismsJreflexive_eq_dom_reflexiveC47Corelib7Classes9MorphismsIreflexive_reflexive_proxyC47Corelib7Classes?RelationClasses<eq_ReflexiveC47Corelib7Classes9Morphisms@reflexive_properC47Corelib7Classes?RelationClasses<eq_SymmetricC47Corelib7Classes9MorphismsNReflexive_partial_app_morphismC47Corelib7Program6Basics4implC47Corelib7Classes?RelationClasses>impl_Reflexivec59OSSVerify5KrLib4Spec6LB_Sum:mtl_insertC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec6LB_Sum4msumC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec6LB_Sum:mtl_deleteC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3subc59OSSVerify5KrLib4Spec6LB_Sum;msum_deleteC1?~~~~~~~~~~~~~~~K46Stdlib9micromega7EnvRing5PExpr04c59OSSVerify5KrLib4Spec6LB_Sum>mtl_insert_oldC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec6LB_Sum6mtl_inC1?~~~~~~~~~~~~~~~C35stdpp4base5empty".
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma zsum_nil : zsum [] = 0.
Proof.
ltac2:(KReplay.run1 (kr_t_LB_Sum ()) [] "p;2g0000j20Tg000Jg000h'0o"). Qed.
Lemma zsum_cons x l : zsum (x :: l) = x + zsum l.
Proof.
ltac2:(KReplay.run1 (kr_t_LB_Sum ()) [] "h01lh11xp;1p;2p-1R0p1001Fp4p710R1p9P0p1001ip4p710R2p9P0p1002UR3p4p710p9P0P3p4p7210p9P0P3p4p73110p9P0p10033R3p4p7210p9P0p1003gp4p710R0p9p1004_p4p7511110R4P1p9P4P2p9P4P3p4p710R3p9P4P0p9p10059p4p710R4p1005WR5p4p710R6p8P4P5p4p7210R5p8p10060R7p4p710R8P1p8P8P2p8P8P3p8P8P0p8P7p4p7210R9P1p8P9P2p8P9P3p8P9P0p8P7p4p73110R7P1p8P7P2p8P7P3p8P7P0p8p1006IR0p4p73101R3P7p8P3p1006cR7p4p73110p8P3p1007?p4p710p8P3p1007RR2p4p7201p8P3p1007dp4p7201p8P3p10086R1p4p73110p8P3p1008JR9p4p73110p8P3p1008^R:p4p73110p8P3p10098p4p7201p8P0p4p710R3P8p8P3P7p4p710p8P3P6p8P3P5p8P3P1p4p710p8P3P9p4p710p8P3P:p4p710p8p1009KR:p4p710R3P4p8P3P6p8P3P5p8P3p1009_p4p73110p8P:p4p741110R:p100:1R3p4p73101p8P3p4p710p100:Mp4p710R3p8p100:kp4p7210P3p8p100;Hp4p7<111111111110P3p8p100;kp4p741110R3P0p4p7511100R5p8P5P3p8p100<Dp4p741110R3P0p4p76111100R5p8P5P3p8p100<\p4p741110R3P0p4p771111100R5p8P5P3p8p100=<p4p741110R3P0p4p7:1111111100R0p8P0P3p8P2p4p7200R2P:p8P:P2p8g00=Sj13Tg00>3j12Tg00>hj20Tg0000j21Tg000JR2%32R:f1R3f0R0#2'0,12X0:X12P3P0O2W0W1o"). Qed.
Lemma zsum_app l1 l2 : zsum (l1 ++ l2) = zsum l1 + zsum l2.
Proof. induction l1 as [|x l1 IH]; [cbn [app]; rewrite zsum_nil; lia|]. cbn [app]. rewrite !zsum_cons, IH. lia. Qed.

Lemma zsum_perm l l' : Permutation l l' -> zsum l = zsum l'.
Proof. induction 1; rewrite ?zsum_cons; lia. Qed.

Lemma zsum_map_perm {A} (f : A -> Z) l l' : Permutation l l' -> zsum (map f l) = zsum (map f l').
Proof. intros P. apply zsum_perm. apply Permutation_map. exact P. Qed.

Lemma zsum_map_ext {A} (f g : A -> Z) l : (forall x, In x l -> f x = g x) -> zsum (map f l) = zsum (map g l).
Proof. intros H. f_equal. apply map_ext_in. exact H. Qed.

Lemma zsum_map_le {A} (f g : A -> Z) l : (forall x, In x l -> f x <= g x) -> zsum (map f l) <= zsum (map g l).
Proof.
  induction l as [|x l IH]; intros H; cbn [map]; [rewrite zsum_nil; lia|]. rewrite !zsum_cons.
  pose proof (H x (or_introl eq_refl)). assert (zsum (map f l) <= zsum (map g l)) by (apply IH; intros y Hy; apply H; right; exact Hy). lia.
Qed.

Lemma zsum_map_nonneg {A} (f : A -> Z) l : (forall x, In x l -> 0 <= f x) -> 0 <= zsum (map f l).
Proof. intros H. induction l as [|x l IH]; cbn [map]; [rewrite zsum_nil; lia|]. rewrite zsum_cons. pose proof (H x (or_introl eq_refl)). assert (0 <= zsum (map f l)) by (apply IH; intros y Hy; apply H; right; exact Hy). lia. Qed.

Lemma zsum_map_add {A} (f g : A -> Z) l : zsum (map (fun x => f x + g x) l) = zsum (map f l) + zsum (map g l).
Proof. induction l as [|x l IH]; cbn [map]; [rewrite !zsum_nil; reflexivity|]. rewrite !zsum_cons, IH. lia. Qed.

Lemma zsum_map_mul {A} (k : Z) (f : A -> Z) l : zsum (map (fun x => k * f x) l) = k * zsum (map f l).
Proof. induction l as [|x l IH]; cbn [map]; [rewrite !zsum_nil; lia|]. rewrite !zsum_cons, IH. lia. Qed.

Lemma zsum_map_const {A} (k : Z) (l : list A) : zsum (map (fun _ => k) l) = k * zlen l.
Proof. unfold zlen. induction l as [|x l IH]; cbn [map length]; [rewrite zsum_nil; lia|]. rewrite zsum_cons, IH. lia. Qed.

Lemma zsum_map_filter {A} (p : A -> bool) (f : A -> Z) l :
  zsum (map f (List.filter p l)) = zsum (map (fun x => if p x then f x else 0) l).
Proof. induction l as [|x l IH]; cbn [map List.filter]; [reflexivity|]. destruct (p x); cbn [map]; rewrite ?zsum_cons, IH; lia. Qed.

Lemma zsum_flat_map {A B} (g : A -> list B) (f : B -> Z) l :
  zsum (map f (flat_map g l)) = zsum (map (fun a => zsum (map f (g a))) l).
Proof. induction l as [|x l IH]; cbn [map flat_map]; [reflexivity|]. rewrite map_app, zsum_app, zsum_cons, IH. reflexivity. Qed.

(* [comment removed for export] *)
Lemma zsum_map_remove {A} (eq_dec : forall x y : A, {x = y} + {x <> y}) (g : A -> Z) y l :
  In y l -> (forall x, In x l -> 0 <= g x) -> exists l', Permutation l (y :: l') /\ zsum (map g l) = g y + zsum (map g l').
Proof.
  intros Hin Hg. apply in_split in Hin as (l1 & l2 & ->). exists (l1 ++ l2). split; [apply Permutation_sym; apply Permutation_middle|].
  rewrite !map_app, !zsum_app. cbn [map]. rewrite zsum_cons. lia.
Qed.

Lemma zsum_inj_le {A B} (eqB : forall x y : B, {x = y} + {x <> y}) (f : A -> Z) (g : B -> Z) (h : A -> B) :
  forall (l1 : list A) (l2 : list B),
  List.NoDup l1 -> (forall x, In x l1 -> In (h x) l2 /\ f x <= g (h x)) ->
  (forall x y, In x l1 -> In y l1 -> h x = h y -> x = y) ->
  (forall y, In y l2 -> 0 <= g y) ->
  zsum (map f l1) <= zsum (map g l2).
Proof.
  induction l1 as [|a l1 IH]; intros l2 ND H INJ POS; cbn [map].
  - rewrite zsum_nil. apply zsum_map_nonneg. exact POS.
  - rewrite zsum_cons. apply List.NoDup_cons_iff in ND as [NI ND].
    destruct (H a (or_introl eq_refl)) as [Hin Hle].
    destruct (zsum_map_remove eqB g (h a) l2 Hin POS) as (l2' & P & E). rewrite E.
    assert (IH' : zsum (map f l1) <= zsum (map g l2')).
    { apply IH; [exact ND| | intros x y Hx Hy; apply INJ; right; assumption| intros y Hy; apply POS; eapply Permutation_in; [apply Permutation_sym; exact P| right; exact Hy]].
      intros x Hx. destruct (H x (or_intror Hx)) as [Hin2 Hle2]. split; [| exact Hle2].
      pose proof (Permutation_in _ P Hin2) as [E2|Hin3]; [| exact Hin3].
      exfalso. apply NI. rewrite (INJ a x (or_introl eq_refl) (or_intror Hx) E2). exact Hx. }
    lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma zlen_nil {A} : zlen (@nil A) = 0.
Proof.
ltac2:(KReplay.run1 (kr_t_LB_Sum ()) [] "h01Ap;2p200R0p100`>p4p710p8g0000j20Tg000Jg000h'0X00f0O1X00o"). Qed.
Lemma zlen_cons {A} (x : A) l : zlen (x :: l) = 1 + zlen l.
Proof.
ltac2:(KReplay.run1 (kr_t_LB_Sum ()) [] "h01xh11Ah24__x1h31lh47__arithh54__ffh68__varmaph75__with84cstrh91yp;1p;2p;<p;3p;4p;7p200R0g00`>R1p4p710p8P0g00a3R2p4p710p8g00=Sj19TP2j24Tg00RXR2j1@Tg00aSR3j11Tg00b3j1PTg00>hj22Tg00Dnj1?j37Tg00bQj1>Tg0000j23Tg00cRl<:Tg00d7j1OTg00\2j2NTg00?Ej1MTg00?ej2LTg00@Cj1KTg00@aj1HTg00ALj2BTg00Aoj2ATg00BRj36Tg00C5j4CTg00JZj7DTg00C`j2ETg00DBj2FTg00EHj3GTg00Egj4=Tg00d\j4ITg00FYj3JTP1j25Tg00eGl<8Tg000JR1f1R4f0R537p=0g00fRR6P6P1P1P2P3P3f3R2g00g1f2R7P4P5M<8p=<P6P1P1P1P3P3f5f4R3P2P7P4P5M<8p=;%94R21475R8#@R9#1R:g00MiR;#PR<%18R='2R>'012=<R?/0>P1P1%?1R@P5X01RAP@1045#>X91X01P:P?PAPA%15,31X06P9P?125<R?X01P8P=131=C<E;P>P>131>M<:%O8g000hR8/N=g00M=R=#M%9=1L14%K1%H1R=g00K>g00K]R9P9g00L=R9P11B1;R;1A1<R6561g00NNA616;CCg00L]FD1E=9P5P7g00O5R9g00OUR='31F57=79=dAG184C=b5b6b7X2112<5,0?^21P51437#1O1b4b8CIAJ745R3,47#1/0>e15731575,2<'0eX32X05X10P7P4P5O3W3X05X10o"). Qed.
Lemma zlen_app {A} (l1 l2 : list A) : zlen (l1 ++ l2) = zlen l1 + zlen l2.
Proof.
ltac2:(KReplay.run1 (kr_t_LB_Sum ()) [] "h01xh11Ah24__x1h34__x2h42l1h52l2h67__arithh74__ffh88__varmaph95__with:4cstrh;5cstr0h<1nh=1yp;1p;2p;<p;4p;3p;7p;6p;Bp200R0g00`>R1p4p710p8P0g012mR2p4p710p8P0g00a3R3p4p710p8P0g00J=R4p4p710p8g00=Sj16TP3j21Tg013Lj2ATg00aSR3j10Tg00>hR5j24Tg00Dnj1Hj39Tg00bQj1@Tg0000j23Tg00cRl<;Tg00d7j17Tg00\2j2:Tg00?Ej1TTg00?ej2STg00\Nj1RTg00G9j4QTg00@Cj1NTg00@aj1GTg00ALj28Tg00GWj1ETg00BRj3BTg00C5j4CTg00JZj7DTg00C`j2?Tg00DBj2FTg00EHj3ITg00Egj4JTg00d\j4KTP4j3<TP2j3LTg00:Mj6MTP1j25Tg00ellBOTg00eGl<PTg000JR1f1R2f0R439p=2g00fRR6P6P6P1P1P1g013cP3P3P3P5g014Cf5R5f4R7f3R8f2R9P2P4MBOp=>P6P1P1P1P3P3P5P7P8P9P2P4M<Pp==%64R3%62R:P61192R;1194R<'AR=%04R>1189R?#0R@1182#0'4'2X<6%0=RA%0;RB%0<RC'4RD'212DDP1P1%H1REP4X01RFPE1224#@X=1X01PAPDPFPF131>X06P=PDP;PB131BP<PC131CE>E=PDPD131DM<;%7<g000hR</:C%7?1:<@g00M=R@#T%6@P11S19P2%R1CQ%N1%G1R@g00K>g00K]R?P?g00L=R?P1g00MiRC,81%EC,815B1RCg00NNPCCCg00L]FD1?@?P4P9g00O5R?g00OUR@'31F49=9?@dAI1<2CJb7b8b9X21X311442R</2<^21^31P41158#01157#0O2b6b;b:CKA<924R7,19AL924EM159715921594'4'2eX5:X43X10P9P2P4O3W5W4X10o"). Qed.
Lemma zlen_nonneg {A} (l : list A) : 0 <= zlen l.
Proof.
ltac2:(KReplay.run1 (kr_t_LB_Sum ()) [] "h01Ah14__x1h21lh37__arithh44__ffh58__varmaph65__with74cstrp;1p;2p;4p;7p;8p;3p200R0g00`>R1p4p710p8P0g00a3R2p4p710p8g00=Sj11TP2j23Tg00d7j18Tg00aSj12Tg00\2j20Tg00?Ej1<Tg00?ej2;Tg00@Cj17Tg00@aj15Tg00Aoj26Tg00ALj24Tg00C5j49Tg00JZj7:Tg00U^j1ETg00Vmj8DTg00C`j2CTg0000j2=Tg00DBj2>Tg00Dnj3?Tg00EHj3@Tg00Egj4ATP1j2BTf0R1#1R2f1R3/31R4#8g000hR5%24'0g000JR4g00M=R6#<%161;43%74%54R6g00K>R7g00K]R8P8g00L=R9P6P7P8P8P9P41645g00^:g00Mi,44C9g00L]F:R7%E8P7GD1C69P1f2R9g00O5R6g00OUR7'=1>19=?67dA@453CAb4b5b6W110511053[^14P1f3/39#2P3O2b3b71B31,05eX22X00P3P1O2W2X00o"). Qed.
Lemma zlen_perm {A} (l l' : list A) : Permutation l l' -> zlen l = zlen l'.
Proof.
ltac2:(KReplay.run1 (kr_t_LB_Sum ()) [] "h01Ah11lh22l'h31Ph41np;1p;3p;2p;4p;6p200R0g00PnR1p4p710p8P0g00`>R2p4p710p8P0g014fR3p4p710p8g00=Sj13TP1j38Tg00a3j21Tg00aSj10Tg00Dnj34Tg0000j27TP3j46Tg00:Mj65TP2j22Tf0R2#3R3f1R1#3R4f2R5?812g00fRR6f3R7/11R8g000JR9%02f4/15#034X46%08,791175P7P5P1P2C6E512751271549eW3X24X13X00P5P1P2O3W2W1X00o"). Qed.
Lemma zlen_map {A B} (f : A -> B) l : zlen (map f l) = zlen l.
Proof.
ltac2:(KReplay.run1 (kr_t_LB_Sum ()) [] "h01Ah11Bh21fh31lh41np;1p;2p;3p;4p;6p200R0g00X\R1p4p710p8P0g00`>R2p4p710R3p8P0g015VR4p4p710p8p201R5P1p4p7210p8P5P3p8P5P4p4p7210p8g00=Sj18Tg00a3j21Tg00aSj10Tg00Dnj32Tg0000j27TP1j46TP4j45Tg00:Mj64TP2j23Tf1R2P2[R4f2R1#8R3g00fRR6f3R7f0R8'1R9g000JR:%08f4/12#032X46%09,7:P7P1P2P8C6R9,11P7P1P2P8C5E41319137852:eX33X24X15X00P7P1P2P8O4W3W2X15X00o"). Qed.

Lemma zcount_eq_zsum {A} (p : A -> bool) l : zcount p l = zsum (map (fun x => if p x then 1 else 0) l).
Proof. unfold zcount, zlen. induction l as [|x l IH]; cbn [map List.filter length]; [rewrite zsum_nil; reflexivity|]. destruct (p x); cbn [length]; rewrite ?zsum_cons, <- IH; lia. Qed.
Lemma zcount_nil {A} (p : A -> bool) : zcount p [] = 0.
Proof.
ltac2:(KReplay.run1 (kr_t_LB_Sum ()) [] "h01Ah11pp;2p200R0p10165p4p710p8g0000j20Tf0R1g00O5[R2g000Jg000h'0X12X00f1P1O2W1X00o"). Qed.
Lemma zcount_cons {A} (p : A -> bool) x l : zcount p (x :: l) = (if p x then 1 else 0) + zcount p l.
Proof. rewrite !zcount_eq_zsum. cbn [map]. rewrite zsum_cons. reflexivity. Qed.
Lemma zcount_app {A} (p : A -> bool) l1 l2 : zcount p (l1 ++ l2) = zcount p l1 + zcount p l2.
Proof. rewrite !zcount_eq_zsum, map_app, zsum_app. reflexivity. Qed.
Lemma zcount_nonneg {A} (p : A -> bool) l : 0 <= zcount p l.
Proof.
ltac2:(KReplay.run1 (kr_t_LB_Sum ()) [] "h01Ah11lh21pp;1p;3p;2p200R0g0165R1p4p710p8P0g018GR2p4p710p8g00=Sj14Tg00h9j33TP2j20TP1j31Tg00\2j22Tf0R1g00O5[R2f1R3#4R4f2R5A3531'0g000hA1531'2eX14X22X00P5P3P1O3W1W2X00o"). Qed.
Lemma zcount_le_len {A} (p : A -> bool) l : zcount p l <= zlen l.
Proof. induction l as [|x l IH]; [cbv; discriminate|]. rewrite zcount_cons, zlen_cons. destruct (p x); lia. Qed.
Lemma zcount_perm {A} (p : A -> bool) l l' : Permutation l l' -> zcount p l = zcount p l'.
Proof. intros P. rewrite !zcount_eq_zsum. apply zsum_map_perm. exact P. Qed.
Lemma zcount_ext {A} (p q : A -> bool) l : (forall x, In x l -> p x = q x) -> zcount p l = zcount q l.
Proof. intros H. rewrite !zcount_eq_zsum. apply zsum_map_ext. intros x Hx. rewrite (H x Hx). reflexivity. Qed.
Lemma zcount_mono {A} (p q : A -> bool) l : (forall x, In x l -> p x = true -> q x = true) -> zcount p l <= zcount q l.
Proof.
  intros H. rewrite !zcount_eq_zsum. apply zsum_map_le. intros x Hx. specialize (H x Hx). destruct (p x); [rewrite H by reflexivity; lia| destruct (q x); lia].
Qed.
Lemma zcount_false {A} (p : A -> bool) l : (forall x, In x l -> p x = false) -> zcount p l = 0.
Proof. intros H. rewrite zcount_eq_zsum. induction l as [|x l IH]; cbn [map]; [apply zsum_nil|]. rewrite zsum_cons, (H x (or_introl eq_refl)), IH; [lia|]. intros y Hy; apply H; right; exact Hy. Qed.
Lemma zcount_In_pos {A} (p : A -> bool) l x : In x l -> p x = true -> 1 <= zcount p l.
Proof.
  intros Hin Hp. apply in_split in Hin as (l1 & l2 & ->). rewrite zcount_app, zcount_cons, Hp. pose proof (zcount_nonneg p l1). pose proof (zcount_nonneg p l2). lia.
Qed.
(* [comment removed for export] *)
Lemma zcount_inj_le {A B} (eqB : forall x y : B, {x = y} + {x <> y}) (p : A -> bool) (q : B -> bool) (h : A -> B) l1 l2 :
  List.NoDup l1 -> (forall x, In x l1 -> p x = true -> In (h x) l2 /\ q (h x) = true) ->
  (forall x y, In x l1 -> In y l1 -> p x = true -> p y = true -> h x = h y -> x = y) ->
  zcount p l1 <= zcount q l2.
Proof.
  intros ND H INJ. unfold zcount at 1. unfold zlen.
  transitivity (zsum (map (fun _ => 1) (List.filter p l1))); [rewrite zsum_map_const; unfold zlen; lia|].
  rewrite zcount_eq_zsum. apply (zsum_inj_le eqB (fun _ => 1) _ h).
  - apply List.NoDup_filter. exact ND.
  - intros x Hx. apply filter_In in Hx as [Hx Hp]. destruct (H x Hx Hp) as [Hin Hq]. rewrite Hq. auto with zarith.
  - intros x y Hx Hy. apply filter_In in Hx as [Hx Hp]. apply filter_In in Hy as [Hy Hq]. apply INJ; assumption.
  - intros y _. destruct (q y); lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section MTL.
Context `{Countable K} `{EqDecision K} {V : Type}.
Implicit Types m : gmap K V.

Lemma mtl_nodup m : List.NoDup (map_to_list m).
Proof. apply NoDup_ListNoDup. apply NoDup_map_to_list. Qed.
Lemma mtl_nodup_keys m : List.NoDup (map fst (map_to_list m)).
Proof. apply NoDup_ListNoDup. apply NoDup_fst_map_to_list. Qed.
Lemma mtl_in m k v : In (k, v) (map_to_list m) <-> m !! k = Some v.
Proof. rewrite <- list_elem_of_In. apply elem_of_map_to_list. Qed.
Lemma mtl_insert m k v : m !! k = None -> Permutation (map_to_list (<[k := v]> m)) ((k, v) :: map_to_list m).
Proof. intros Hk. apply map_to_list_insert. exact Hk. Qed.
Lemma mtl_delete m k v : m !! k = Some v -> Permutation (map_to_list m) ((k, v) :: map_to_list (delete k m)).
Proof. intros Hk. rewrite <- (insert_delete_id m k v Hk) at 1. apply map_to_list_insert. apply lookup_delete_eq. Qed.
Lemma mtl_insert_old m k v v0 : m !! k = Some v0 ->
  Permutation (map_to_list (<[k := v]> m)) ((k, v) :: map_to_list (delete k m)).
Proof. intros Hk. rewrite <- (insert_delete_eq m k v). apply map_to_list_insert. apply lookup_delete_eq. Qed.

(* [comment removed for export] *)
Definition msum (f : K * V -> Z) m : Z := zsum (map f (map_to_list m)).
Lemma msum_insert f m k v : m !! k = None -> msum f (<[k := v]> m) = f (k, v) + msum f m.
Proof. intros Hk. unfold msum. rewrite (zsum_map_perm f _ _ (mtl_insert m k v Hk)). cbn [map]. apply zsum_cons. Qed.
Lemma msum_delete f m k v : m !! k = Some v -> msum f m = f (k, v) + msum f (delete k m).
Proof. intros Hk. unfold msum. rewrite (zsum_map_perm f _ _ (mtl_delete m k v Hk)). cbn [map]. apply zsum_cons. Qed.
Lemma msum_insert_old f m k v v0 : m !! k = Some v0 -> msum f (<[k := v]> m) = f (k, v) + msum f m - f (k, v0).
Proof. intros Hk. unfold msum. rewrite (zsum_map_perm f _ _ (mtl_insert_old m k v v0 Hk)). cbn [map]. rewrite zsum_cons. pose proof (msum_delete f m k v0 Hk) as E. unfold msum in E. lia. Qed.
Lemma msum_ext f g m : (forall k v, m !! k = Some v -> f (k, v) = g (k, v)) -> msum f m = msum g m.
Proof. intros Hfg. unfold msum. apply zsum_map_ext. intros [k v] Hin. apply Hfg. apply mtl_in. exact Hin. Qed.
Lemma msum_nonneg f m : (forall k v, m !! k = Some v -> 0 <= f (k, v)) -> 0 <= msum f m.
Proof. intros Hf. unfold msum. apply zsum_map_nonneg. intros [k v] Hin. apply Hf. apply mtl_in. exact Hin. Qed.
Lemma msum_empty f : msum f (∅ : gmap K V) = 0.
Proof. unfold msum. rewrite map_to_list_empty. reflexivity. Qed.
End MTL.
