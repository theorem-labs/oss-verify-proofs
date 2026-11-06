(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase State.
Import ListNotations.
Open Scope bv_scope.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Ltac2 gd_tbl_PlacementSearch () : Init.string Init.list := ["Corelib.Numbers.BinNums.Z"; "Corelib.Init.Logic.eq"; "Stdlib.ZArith.BinInt.Z.modulo"; "LinuxProcessSemantics.LinuxProcessSem.State.page_size"; "Stdlib.ZArith.BinInt.Z.le"; "Stdlib.ZArith.BinInt.Z.add"; "Corelib.Init.Datatypes.bool"; "LinuxProcessSemantics.LinuxProcessSem.State.region_free"; "stdpp.bitvector.definitions.Z_to_bv"; "Corelib.Init.Datatypes.false"; "Corelib.Init.Datatypes.cons"; "Corelib.Lists.ListDef.map"; "Corelib.Init.Datatypes.prod"; "stdpp.bitvector.definitions.bv"; "LinuxProcessSemantics.LinuxProcessSem.State.page_round_up_Z"; "stdpp.bitvector.definitions.bv_unsigned"; "Corelib.Init.Datatypes.fst"; "Corelib.Init.Datatypes.snd"; "Stdlib.Lists.List.existsb"; "Corelib.Init.Datatypes.andb"; "Stdlib.ZArith.BinInt.Z.eqb"; "Stdlib.ZArith.BinInt.Z.leb"; "fit_candidates"; "Corelib.Init.Datatypes.list"; "Stdlib.ZArith.BinInt.Z.lt"; "LinuxProcessSemantics.LinuxProcessSem.State.two_pow_64"; "Corelib.Init.Datatypes.true"; "higher_fit_b"; "Corelib.Init.Logic.ex"; "Corelib.Init.Logic.and"; "Corelib.Init.Logic.iff"; "no_higher_fit"; "Corelib.Init.Datatypes.option"; "place"; "Corelib.Init.Datatypes.Some"; "Stdlib.ZArith.BinInt.Z.sub"; "place_fits"; "search_candidates"; "LinuxProcessSemantics.LinuxProcessSem.State.VmMaps"; "place_in_model"; "LinuxProcessSemantics.LinuxProcessSem.State.alloc_top"; "Corelib.Init.Datatypes.app"; "LinuxProcessSemantics.LinuxProcessSem.State.vm_reserved"; "LinuxProcessSemantics.LinuxProcessSem.State.vm_maps"].


(* [comment removed for export] *)
Definition no_higher_fit (maps : list (word * word)) (aZ nZ baseZ : Z)
    : Prop := ltac2:(CDefT.buildp (gd_tbl_PlacementSearch ()) "Pg,$0.P,(1.$0.(2.R1.$3.)=)P,(4.(5.O3.O2.)R2.)P,(4.(5.R3.O2.)O1.)(1.$6.(7.O4.(8.&40.R4.)(8.&40.O2.))$9.)")
(* [comment removed for export] *).

(* [comment removed for export] *)
Definition fit_candidates (maps : list (word * word)) (aZ nZ : Z)
    : list Z := ltac2:(CDefT.buildp (gd_tbl_PlacementSearch ()) "(:.$0.(5.O2.O1.)(;.(<.(=.&40.)(=.&40.))$0.Lp,(<.(=.&40.)(=.&40.))(>.(5.(?.&40.(10.(=.&40.)(=.&40.)R1.))(?.&40.(11.(=.&40.)(=.&40.)R1.))))O3.))")
(* [comment removed for export] *).

Definition higher_fit_b (maps : list (word * word)) (aZ nZ baseZ : Z)
    : bool := ltac2:(CDefT.buildp (gd_tbl_PlacementSearch ()) "(12.$0.Lg,$0.(13.(13.(13.(14.(2.R1.$3.)=)(15.(5.O3.O2.)R1.))(15.(5.R1.O2.)O1.))(7.O4.(8.&40.R1.)(8.&40.O2.)))(16.O4.O3.O2.))")
(* [comment removed for export] *).

Lemma page_round_up_Z_aligned : forall z,
  (page_round_up_Z z mod page_size = 0)%Z.
Proof. intro z. unfold page_round_up_Z. apply Z_mod_mult. Qed.

Lemma page_round_up_Z_ge : forall z, (z <= page_round_up_Z z)%Z.
Proof.
  intro z. unfold page_round_up_Z, page_size.
  pose proof (Z.div_mod (z + 4096 - 1) 4096 ltac:(lia)) as H.
  pose proof (Z.mod_pos_bound (z + 4096 - 1) 4096 ltac:(lia)).
  lia.
Qed.

(* [comment removed for export] *)
Lemma page_round_up_Z_le : forall z b,
  (z <= b)%Z -> (b mod page_size = 0)%Z -> (page_round_up_Z z <= b)%Z.
Proof.
  intros z b Hzb Hb. unfold page_round_up_Z, page_size in *.
  pose proof (Z.div_mod b 4096 ltac:(lia)) as Hbm.
  assert (Hq : ((z + 4096 - 1) / 4096 < b / 4096 + 1)%Z)
    by (apply Z.div_lt_upper_bound; lia).
  apply Z.le_trans with (m := (b / 4096 * 4096)%Z); [|lia].
  apply Z.mul_le_mono_nonneg_r; lia.
Qed.

Lemma fold_max_ge_seed : forall l s, (s <= fold_left Z.max l s)%Z.
Proof.
  induction l as [|x l IH]; intro s; cbn; [lia|].
  pose proof (IH (Z.max s x)). lia.
Qed.

Lemma fold_max_ge_in : forall l s x,
  In x l -> (x <= fold_left Z.max l s)%Z.
Proof.
  induction l as [|y l IH]; intros s x Hin; [contradiction|].
  destruct Hin as [->|Hin]; cbn.
  - pose proof (fold_max_ge_seed l (Z.max s x)). lia.
  - apply IH; assumption.
Qed.

Lemma fold_max_le : forall l s b,
  (s <= b)%Z -> (forall x, In x l -> (x <= b)%Z) ->
  (fold_left Z.max l s <= b)%Z.
Proof.
  induction l as [|y l IH]; intros s b Hs Hl; cbn; [exact Hs|].
  apply IH.
  - pose proof (Hl y ltac:(now left)). lia.
  - intros x Hx. apply Hl. now right.
Qed.

Lemma fold_max_in_or_seed : forall l s,
  fold_left Z.max l s = s \/ In (fold_left Z.max l s) l.
Proof.
  induction l as [|y l IH]; intro s; cbn; [now left|].
  destruct (IH (Z.max s y)) as [Heq|Hin].
  - rewrite Heq. destruct (Z.max_spec s y) as [[_ ->]|[_ ->]];
      [right; now left | now left].
  - right. now right.
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma higher_fit_b_complete : ltac2:(CDefT.buildp (gd_tbl_PlacementSearch ()) "Pmaps,(17.(<.(=.&40.)(=.&40.)))PaZ,$0.PnZ,$0.PbaseZ,$0.Pg,$0.P,(4.=(5.R4.R3.))P,(18.=R4.)P,(1.$0.(2.R6.$3.)=)P,(1.$0.(2.R6.$3.)=)P,(18.R6.$19.)P,(1.$0.(2.R6.$3.)=)P,(4.(5.R:.R9.)R7.)P,(4.(5.R8.R:.)R9.)P,(1.$6.(7.R=.(8.&40.R9.)(8.&40.R;.))$1:.)(1.$6.(1;.R>.R=.R<.R;.)$1:.)")
(* [comment removed for export] *).
Proof.
  (* [comment removed for export] *)
  intros maps aZ nZ baseZ g HaPos HnPos HaAl HnAl Hbase HgAl Hglo Hghi
    Hgfree.
  assert (Hmod : two_pow_64 = bv_modulus 64) by reflexivity.
  assert (HgW : bv_unsigned (Z_to_bv 64 g) = g)
    by (rewrite Z_to_bv_unsigned; apply bv_wrap_small; clear HaAl HnAl HgAl Hgfree; lia).   (* [comment removed for export] *)
  assert (HnW : bv_unsigned (Z_to_bv 64 nZ) = nZ)
    by (rewrite Z_to_bv_unsigned; apply bv_wrap_small; clear HaAl HnAl HgAl Hgfree; lia).
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
    by (rewrite Z_to_bv_unsigned; apply bv_wrap_small; clear HaAl HnAl HgAl Hgfree Hcs Hcand; lia).   (* [comment removed for export] *)
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
    - (* [comment removed for export] *)
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
    - (* [comment removed for export] *)
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

(* [comment removed for export] *)
Lemma higher_fit_b_sound : ltac2:(CDefT.buildp (gd_tbl_PlacementSearch ()) "Pmaps,(17.(<.(=.&40.)(=.&40.)))PaZ,$0.PnZ,$0.PbaseZ,$0.P,(1.$6.(1;.R4.R3.R2.R1.)$1:.)(1<.$0.Lg,$0.(1=.(1.$0.(2.R1.$3.)=)(1=.(4.(5.R5.R4.)R1.)(1=.(4.(5.R1.R4.)R3.)(1.$6.(7.R6.(8.&40.R1.)(8.&40.R4.))$1:.)))))")
(* [comment removed for export] *).
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

(* [comment removed for export] *)
Lemma no_higher_fit_iff : ltac2:(CDefT.buildp (gd_tbl_PlacementSearch ()) "Pmaps,(17.(<.(=.&40.)(=.&40.)))PaZ,$0.PnZ,$0.PbaseZ,$0.P,(4.=R3.)P,(18.=R3.)P,(1.$0.(2.R5.$3.)=)P,(1.$0.(2.R5.$3.)=)P,(18.R5.$19.)(1>.(1.$6.(1;.R9.R8.R7.R6.)$9.)(1?.R9.R8.R7.R6.))")
(* [comment removed for export] *).
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

(* [comment removed for export] *)

(* [comment removed for export] *)
Definition search_candidates (maps : list (word * word)) (loZ : Z)
    : list Z := ltac2:(CDefT.buildp (gd_tbl_PlacementSearch ()) "(:.$0.O1.(;.(<.(=.&40.)(=.&40.))$0.Lp,(<.(=.&40.)(=.&40.))(>.(5.(?.&40.(10.(=.&40.)(=.&40.)R1.))(?.&40.(11.(=.&40.)(=.&40.)R1.))))O2.))")
(* [comment removed for export] *).

(* [comment removed for export] *)
Definition place_fits (maps : list (word * word)) (loZ hiZ nZ : Z) (g : Z)
    : bool := ltac2:(CDefT.buildp (gd_tbl_PlacementSearch ()) "(13.(13.(13.(14.(2.O1.$3.)=)(15.O4.O1.))(15.(5.O1.O2.)O3.))(7.O5.(8.&40.O1.)(8.&40.O2.)))")
(* [comment removed for export] *).

Definition place (maps : list (word * word)) (loZ hiZ nZ : Z)
    : option Z :=
  find (place_fits maps loZ hiZ nZ) (search_candidates maps loZ).

(* [comment removed for export] *)

Lemma place_sound : ltac2:(CDefT.buildp (gd_tbl_PlacementSearch ()) "Pmaps,(17.(<.(=.&40.)(=.&40.)))PloZ,$0.PhiZ,$0.PnZ,$0.Pa,$0.P,(1.(20.$0.)(21.R5.R4.R3.R2.)(22.$0.R1.))(1=.(1.$0.(2.R2.$3.)=)(1=.(4.R5.R2.)(1=.(4.(5.R2.R3.)R4.)(1.$6.(7.R6.(8.&40.R2.)(8.&40.R3.))$1:.))))")
(* [comment removed for export] *).
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

(* [comment removed for export] *)

Lemma existsb_find : forall {A} (f : A -> bool) l,
  existsb f l = true -> exists x, find f l = Some x.
Proof.
  intros A f l. induction l as [|y l IH]; cbn; [discriminate|].
  destruct (f y) eqn:Hy; [intros _; now exists y|].
  cbn. exact IH.
Qed.

(* [comment removed for export] *)
Lemma higher_fit_b_as_place : ltac2:(CDefT.buildp (gd_tbl_PlacementSearch ()) "Pmaps,(17.(<.(=.&40.)(=.&40.)))PloZ,$0.PhiZ,$0.PnZ,$0.(1.$6.(1;.R4.(23.R3.R1.)R1.R2.)(12.$0.(24.R4.R3.R2.R1.)(25.R4.R3.)))")
(* [comment removed for export] *).
Proof.
  intros maps loZ hiZ nZ.
  unfold higher_fit_b, place_fits, search_candidates, fit_candidates.
  replace (loZ - nZ + nZ)%Z with loZ by lia.
  reflexivity.
Qed.

(* [comment removed for export] *)
Lemma place_complete : ltac2:(CDefT.buildp (gd_tbl_PlacementSearch ()) "Pmaps,(17.(<.(=.&40.)(=.&40.)))PloZ,$0.PhiZ,$0.PnZ,$0.Pg,$0.P,(4.=R4.)P,(18.=R3.)P,(1.$0.(2.R6.$3.)=)P,(1.$0.(2.R5.$3.)=)P,(18.R7.$19.)P,(1.$0.(2.R6.$3.)=)P,(4.R:.R7.)P,(4.(5.R8.R9.)R:.)P,(1.$6.(7.R=.(8.&40.R9.)(8.&40.R:.))$1:.)(1<.$0.La,$0.(1.(20.$0.)(21.R?.R>.R=.R<.)(22.$0.R1.)))")
(* [comment removed for export] *).
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

(* [comment removed for export] *)

(* [comment removed for export] *)
Definition place_in_model (h : VmMaps) (nZ : Z) : option Z :=
  place (vm_reserved h ++ vm_maps h) page_size (alloc_top h) nZ.

(* [comment removed for export] *)
Lemma place_in_model_admissible : ltac2:(CDefT.buildp (gd_tbl_PlacementSearch ()) "Ph,$26.PnZ,$0.Pa,$0.P,(4.=R2.)P,(1.(20.$0.)(27.R4.R3.)(22.$0.R2.))(1=.(1.$0.(?.&40.(8.&40.R3.))R3.)(1=.(1.$0.(2.(?.&40.(8.&40.R3.))$3.)=)(1=.(18.=(?.&40.(8.&40.R3.)))(1=.(4.(5.(?.&40.(8.&40.R3.))R4.)(28.R5.))(1.$6.(7.(29.(<.(=.&40.)(=.&40.))(2:.R5.)(2;.R5.))(8.&40.R3.)(8.&40.R4.))$1:.)))))")
(* [comment removed for export] *).
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

(* [comment removed for export] *)
Example place_accepts_a_negative_length :
  place_in_model (mkVmMaps [] [] 0 0 0) (-4096) = Some 4096%Z.
Proof. vm_compute. reflexivity. Qed.

Lemma place_in_model_complete : ltac2:(CDefT.buildp (gd_tbl_PlacementSearch ()) "Ph,$26.PnZ,$0.Pg,$0.P,(18.=R2.)P,(1.$0.(2.R3.$3.)=)P,(1.$0.(2.R3.$3.)=)P,(4.$3.R4.)P,(4.(5.R5.R6.)(28.R7.))P,(1.$6.(7.(29.(<.(=.&40.)(=.&40.))(2:.R8.)(2;.R8.))(8.&40.R6.)(8.&40.R7.))$1:.)(1<.$0.La,$0.(1.(20.$0.)(27.R:.R9.)(22.$0.R1.)))")
(* [comment removed for export] *).
Proof.
  intros h nZ g Hn Hnal HgAl Hglo Hghi Hfree.
  unfold place_in_model.
  apply (place_complete _ _ _ _ g); try assumption.
  - unfold page_size. lia.
  - unfold page_size. reflexivity.
  - exact (alloc_top_lt h).
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)

Definition witness_ledger : list (word * word) :=
  [(Z_to_bv 64 4096, Z_to_bv 64 8192)].

(* [comment removed for export] *)
Definition demo_top : Z := alloc_top (mkVmMaps [] [] 0 0 0).

(* [comment removed for export] *)
Example place_skips_the_occupied_floor :
  place witness_ledger page_size demo_top 4096 = Some 12288%Z.
Proof. vm_compute. reflexivity. Qed.

(* [comment removed for export] *)
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

(* [comment removed for export] *)
Definition full_ledger : list (word * word) :=
  [(Z_to_bv 64 4096, Z_to_bv 64 (demo_top - 4096))].

Example place_finds_nothing_when_full :
  place full_ledger page_size demo_top 4096 = None.
Proof. vm_compute. reflexivity. Qed.
