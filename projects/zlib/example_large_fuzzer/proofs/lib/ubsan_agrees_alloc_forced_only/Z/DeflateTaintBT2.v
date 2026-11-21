(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith.
From Stdlib Require Import List.
From Stdlib Require Import Bool.
From Stdlib Require Import Lia.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import ZProg.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import DeflateState.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import Trees.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import FillWinModel.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import TreeModel.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import BuildTreeModel.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import GenBitlenModel.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import GenCodesModel.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import RefDeflSafeZ.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import RefDeflSafeB1.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import RefDeflSafeB2.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import RefDeflSafeB3.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import RefDeflSafeB4.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import DeflateTaintRel.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import DeflateTaintBT.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
Lemma AG_set2 P a b i v1 v2 : AG P a b -> (0 <= i < arr_len a -> v1 = v2) -> AG P (arr_set a i v1) (arr_set b i v2).
Proof.
  intros [L H] Hv. split; [rewrite !arr_len_set; exact L|].
  intros j Pj. rewrite !arr_get_set. unfold arr_inb. rewrite <- L.
  destruct (Z.eqb_spec i j) as [<-|NE]; cbn [andb]; [| apply H; exact Pj].
  destruct (Z.leb_spec 0 i); destruct (Z.ltb_spec i (arr_len a)); cbn [andb]; try (apply H; exact Pj).
  apply Hv. lia.
Qed.

Section GB.
Variable t : tree_id.
Local Notation E := (sd_elems t).
Local Notation TS := (tsize t).
Local Notation ML := (sd_max_length t).
Variable s1 : deflate_state.
Variable s2 : deflate_state.
Hypothesis TL1 : tree_lens s1.
Hypothesis TL2 : tree_lens s2.
Local Notation U1 := (bt_upd s1 t).
Local Notation U2 := (bt_upd s2 t).
(* [comment removed for export] *)
Variable FC2r : arr.
Variable DL2r : arr.
Variable L : Z.
Variable mc : Z.
Variable FCf : arr.
Variable DLf : arr.
Variable HPf : arr.
Variable DPf : arr.
Hypothesis HR : heap_result t FC2r DL2r L mc FCf DLf HPf DPf.
Local Notation HM := (RefDeflSafeB3.HM L).

Lemma GB_ranges : 2 <= HM <= 570 /\ 2 <= L <= E /\ 0 <= mc < E /\ 7 <= ML <= 15 /\ 19 <= E <= 286 /\ TS = 2 * E + 1.
Proof.
  pose proof (HM_range t _ _ _ _ _ _ _ _ HR). pose proof (hr_L _ _ _ _ _ _ _ _ _ HR). pose proof (hr_mc _ _ _ _ _ _ _ _ _ HR).
  pose proof (ML_range t _ _ _ _ _ _ _ _ HR). pose proof (E_TS t). lia.
Qed.

(* [comment removed for export] *)
Lemma tail_pos : forall u, (E <= u < E + L - 1 \/ (exists p, HM <= p < 573 /\ arr_get HPf p = u)) ->
  exists p, HM <= p < 573 /\ arr_get HPf p = u.
Proof.
  intros u [Hu|Hu]; [| exact Hu].
  destruct (hr_cov _ _ _ _ _ _ _ _ _ HR u ltac:(unfold Vj; right; lia)) as (p & Hp & Ep).
  exists p. unfold RefDeflSafeB3.HM. split; [lia | exact Ep].
Qed.

(* [comment removed for export] *)
Variable FCg : arr.
Variable HPg : arr.
Variable DPg : arr.

(* [comment removed for export] *)
Lemma HR2_U_repl V D DL1 BC1 DL2 BC2 OL SL DL1' BC1' DL2' BC2' OL' SL' :
  HR2 t V D (U1 FCf DL1 HPf 1 HM DPf BC1 OL SL mc) (U2 FCg DL2 HPg 1 HM DPg BC2 OL SL mc) ->
  AG D DL1' DL2' -> arr_len DL1' = TS -> arr_len BC1' = 16 -> arr_len BC2' = 16 ->
  HR2 t V D (U1 FCf DL1' HPf 1 HM DPf BC1' OL' SL' mc) (U2 FCg DL2' HPg 1 HM DPg BC2' OL' SL' mc).
Proof.
  intros R ADL LDL LBC1 LBC2.
  pose proof (hu_lens t s1 s2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ R) as (LFC1 & LFC2 & _ & _ & LHP1 & LHP2 & LDP1 & LDP2 & _ & _).
  apply (HR2_U t s1 s2 TL1 TL2); try assumption.
  - exact (hu_fc t s1 s2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ R).
  - exact (hu_dp t s1 s2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ R).
  - exact (hu_hp t s1 s2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ R).
  - exact (hu_V t s1 s2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ R).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section Passes.
  Variable V : Z -> Prop.
Variable D : Z -> Prop.
  (* [comment removed for export] *)
  Hypothesis TD : forall p, HM <= p < 573 -> D (arr_get HPf p).
  Hypothesis DI : forall u, E <= u < E + L - 1 -> D u.

  Lemma tail_live : forall p, HM <= p < 573 -> live 1 HM p.
  Proof. intros p Hp. unfold live. right. exact Hp. Qed.

  Lemma loop1_gb_rel : forall f h ovf DL1 BC1 OL SL DL2 BC2 BC0 OL0 SL0,
    HR2 t V D (U1 FCf DL1 HPf 1 HM DPf BC1 OL SL mc) (U2 FCg DL2 HPg 1 HM DPg BC2 OL SL mc) ->
    AG (fun i => 0 <= i < 16) BC1 BC2 ->
    L1I t FC2r L mc FCf DLf HPf DPf s1 BC0 OL0 SL0 h (U1 FCf DL1 HPf 1 HM DPf BC1 OL SL mc) ovf ->
    (Z.of_nat f >= 573 - h) ->
    exists DL1' BC1' OL' SL' DL2' BC2' ovf',
      gen_bitlen_loop1 f (U1 FCf DL1 HPf 1 HM DPf BC1 OL SL mc) t mc (sd_extra_base t) ML h ovf = (U1 FCf DL1' HPf 1 HM DPf BC1' OL' SL' mc, ovf')
      /\ gen_bitlen_loop1 f (U2 FCg DL2 HPg 1 HM DPg BC2 OL SL mc) t mc (sd_extra_base t) ML h ovf = (U2 FCg DL2' HPg 1 HM DPg BC2' OL' SL' mc, ovf')
      /\ HR2 t V D (U1 FCf DL1' HPf 1 HM DPf BC1' OL' SL' mc) (U2 FCg DL2' HPg 1 HM DPg BC2' OL' SL' mc)
      /\ AG (fun i => 0 <= i < 16) BC1' BC2'
      /\ L1I t FC2r L mc FCf DLf HPf DPf s1 BC0 OL0 SL0 573 (U1 FCf DL1' HPf 1 HM DPf BC1' OL' SL' mc) ovf'.
  Proof.
    induction f as [|f IH]; intros h ovf DL1 BC1 OL SL DL2 BC2 BC0 OL0 SL0 R ABC HI Hf.
    - pose proof (l1_h _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HI) as Hh.
      exists DL1, BC1, OL, SL, DL2, BC2, ovf. cbn [gen_bitlen_loop1].
      split; [reflexivity|]. split; [reflexivity|]. split; [exact R|]. split; [exact ABC|].
      replace 573 with h by lia. exact HI.
    - pose proof (l1_h _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HI) as Hh. pose proof GB_ranges as RG.
      rewrite !(GL1_step t mc). unfold HEAP_SIZE.
      destruct (Z.ltb_spec h 573) as [Ch|Ch].
      2:{ exists DL1, BC1, OL, SL, DL2, BC2, ovf. split; [reflexivity|]. split; [reflexivity|]. split; [exact R|]. split; [exact ABC|].
          replace 573 with h by lia. exact HI. }
      pose proof (hu_lens t s1 s2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ R) as (LFC1 & LFC2 & LDL1 & LDL2 & LHP1 & LHP2 & LDP1 & LDP2 & LBC1 & LBC2).
      pose proof (hu_fc t s1 s2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ R) as AFC. pose proof (hu_dl t s1 s2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ R) as ADL.
      pose proof (hu_hp t s1 s2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ R) as AHP.
      (* [comment removed for export] *)
      set (n := arr_get HPf h).
      destruct (AHP h ltac:(apply tail_live; lia)) as [En Vn]. fold n in En.
      (* [comment removed for export] *)
      destruct (l1_X _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HI) as (DLx & BCx & OLx & SLx & EX & HDL & _).
      pose proof (f_equal (fun x => tree_dl x t) EX) as EDL. cbv beta in EDL. autorewrite with btupd in EDL. subst DLx.
      assert (Edad1 : arr_get DL1 n = E + (572 - h) / 2).
      { rewrite HDL. unfold dl_at. destruct (tid_nd t _ _ _ _ _ _ _ _ HR h ltac:(unfold tail; lia)) as [T P].
        unfold RefDeflSafeB3.nd in T, P. fold n in T, P. rewrite T, P.
        replace (h <? h) with false by (symmetry; apply Z.ltb_irrefl). cbn [andb].
        exact (hr_dad _ _ _ _ _ _ _ _ _ HR h ltac:(unfold RefDeflSafeB3.HM in *; lia)). }
      assert (Hdad : E <= E + (572 - h) / 2 < E + L - 1).
      { split; [pose proof (Z.div_pos (572 - h) 2); lia|].
        assert ((572 - h) / 2 < L - 1) by (apply Z.div_lt_upper_bound; unfold RefDeflSafeB3.HM in *; lia). lia. }
      assert (Edad2 : arr_get DL2 n = arr_get DL1 n) by (symmetry; apply (AG_get _ _ _ _ ADL); apply TD; lia).
      assert (Elen2 : arr_get DL2 (arr_get DL1 n) = arr_get DL1 (arr_get DL1 n)).
      { symmetry. apply (AG_get _ _ _ _ ADL). rewrite Edad1. apply DI. exact Hdad. }
      assert (Efc2 : arr_get FCg n = arr_get FCf n) by (symmetry; apply (AG_get _ _ _ _ AFC); right; exact Vn).
      (* [comment removed for export] *)
      pose proof (L1_step t _ _ _ _ _ _ _ _ HR s1 BC0 OL0 SL0 h _ ovf HI Ch) as [HI' _].
      rewrite (GB1_flat t mc s1) in HI'. cbv zeta in HI'. rewrite (GB1_flat t mc s1), (GB1_flat t mc s2). cbv zeta.
      rewrite En, Edad2, Elen2, Efc2. fold n in HI' |- *.
      set (bits0 := arr_get DL1 (arr_get DL1 n) + 1) in *.
      set (bits := if ML <? bits0 then ML else bits0) in *.
      set (ovf' := if ML <? bits0 then ovf + 1 else ovf) in *.
      set (DL1' := arr_set DL1 n (wrap16 bits)) in *. set (DL2' := arr_set DL2 n (wrap16 bits)).
      assert (ADL' : AG D DL1' DL2') by (subst DL1' DL2'; apply AG_set; exact ADL).
      assert (LDL1' : arr_len DL1' = TS) by (subst DL1'; rewrite arr_len_set; exact LDL1).
      destruct (Z.ltb_spec mc n) as [Cn|Cn].
      + cbn [fst snd] in HI'.
        assert (R1 : HR2 t V D (U1 FCf DL1' HPf 1 HM DPf BC1 OL SL mc) (U2 FCg DL2' HPg 1 HM DPg BC2 OL SL mc))
          by (apply (HR2_U_repl V D DL1 BC1 DL2 BC2 OL SL); assumption).
        destruct (IH (h + 1) ovf' DL1' BC1 OL SL DL2' BC2 BC0 OL0 SL0 R1 ABC HI' ltac:(lia))
          as (DL1f & BC1f & OLf & SLf & DL2f & BC2f & ovff & E1 & E2 & Rf & Af & If).
        exists DL1f, BC1f, OLf, SLf, DL2f, BC2f, ovff. split; [exact E1|]. split; [exact E2|]. split; [exact Rf|]. split; [exact Af | exact If].
      + cbn [fst snd] in HI'.
        set (BC1' := arr_set BC1 bits (wrap16 (arr_get BC1 bits + 1))) in *.
        set (BC2' := arr_set BC2 bits (wrap16 (arr_get BC2 bits + 1))).
        assert (ABC' : AG (fun i => 0 <= i < 16) BC1' BC2').
        { subst BC1' BC2'. apply AG_set2; [exact ABC|]. intros Hb. rewrite (AG_get _ _ _ bits ABC); [reflexivity | rewrite <- LBC1; exact Hb]. }
        set (OL' := wrap64 (OL + arr_get FCf n * (bits + xbits t n))) in *.
        set (SL' := if stree_has t then wrap64 (SL + arr_get FCf n * (stree_Len t n + xbits t n)) else SL) in *.
        assert (R1 : HR2 t V D (U1 FCf DL1' HPf 1 HM DPf BC1' OL' SL' mc) (U2 FCg DL2' HPg 1 HM DPg BC2' OL' SL' mc)).
        { apply (HR2_U_repl V D DL1 BC1 DL2 BC2 OL SL); try assumption; subst BC1' BC2'; rewrite arr_len_set; assumption. }
        destruct (IH (h + 1) ovf' DL1' BC1' OL' SL' DL2' BC2' BC0 OL0 SL0 R1 ABC' HI' ltac:(lia))
          as (DL1f & BC1f & OLf & SLf & DL2f & BC2f & ovff & E1 & E2 & Rf & Af & If).
        exists DL1f, BC1f, OLf, SLf, DL2f, BC2f, ovff. split; [exact E1|]. split; [exact E2|]. split; [exact Rf|]. split; [exact Af | exact If].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  Lemma find_rel : forall f BC1 BC2 DL1 DL2 OL SL b,
    AG (fun i => 0 <= i < 16) BC1 BC2 -> arr_len BC1 = 16 -> b < 16 -> Z.of_nat f <= b + 1 ->
    gen_bitlen_find f (U2 FCg DL2 HPg 1 HM DPg BC2 OL SL mc) b = gen_bitlen_find f (U1 FCf DL1 HPf 1 HM DPf BC1 OL SL mc) b.
  Proof.
    induction f as [|f IH]; intros BC1 BC2 DL1 DL2 OL SL b ABC LBC Hb Hf; [reflexivity|].
    cbn [gen_bitlen_find]. rewrite !bt_bl_count_get.
    rewrite <- (AG_get _ _ _ b ABC) by lia.
    destruct (arr_get BC1 b =? 0); [| reflexivity]. apply IH; try assumption; lia.
  Qed.

  Lemma loop2_gb_rel : forall f ovf DL1 BC1 DL2 BC2 OL SL,
    HR2 t V D (U1 FCf DL1 HPf 1 HM DPf BC1 OL SL mc) (U2 FCg DL2 HPg 1 HM DPg BC2 OL SL mc) ->
    AG (fun i => 0 <= i < 16) BC1 BC2 ->
    exists BC1' BC2',
      gen_bitlen_loop2 f (U1 FCf DL1 HPf 1 HM DPf BC1 OL SL mc) ML ovf = U1 FCf DL1 HPf 1 HM DPf BC1' OL SL mc
      /\ gen_bitlen_loop2 f (U2 FCg DL2 HPg 1 HM DPg BC2 OL SL mc) ML ovf = U2 FCg DL2 HPg 1 HM DPg BC2' OL SL mc
      /\ HR2 t V D (U1 FCf DL1 HPf 1 HM DPf BC1' OL SL mc) (U2 FCg DL2 HPg 1 HM DPg BC2' OL SL mc)
      /\ AG (fun i => 0 <= i < 16) BC1' BC2'.
  Proof.
    induction f as [|f IH]; intros ovf DL1 BC1 DL2 BC2 OL SL R ABC.
    - exists BC1, BC2. cbn [gen_bitlen_loop2]. split; [reflexivity|]. split; [reflexivity|]. split; [exact R | exact ABC].
    - pose proof GB_ranges as RG.
      pose proof (hu_lens t s1 s2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ R) as (_ & _ & LDL1 & _ & _ & _ & _ & _ & LBC1 & LBC2).
      rewrite (GL2_step t ML f s1), (GL2_step t ML f s2). cbv zeta.
      rewrite (find_rel (Z.to_nat ML) BC1 BC2 DL1 DL2 OL SL (ML - 1) ABC LBC1) by lia.
      set (r := gen_bitlen_find (Z.to_nat ML) (U1 FCf DL1 HPf 1 HM DPf BC1 OL SL mc) (ML - 1)). clearbody r.
      assert (ABC' : AG (fun i => 0 <= i < 16) (bl_adj ML BC1 r) (bl_adj ML BC2 r)).
      { unfold bl_adj.
        assert (A1 : AG (fun i => 0 <= i < 16) (arr_set BC1 r (wrap16 (arr_get BC1 r - 1))) (arr_set BC2 r (wrap16 (arr_get BC2 r - 1)))).
        { apply AG_set2; [exact ABC|]. intros Hr. rewrite (AG_get _ _ _ r ABC) by lia. reflexivity. }
        match goal with |- AG _ (arr_set (arr_set ?a1 _ _) _ _) (arr_set (arr_set ?a2 _ _) _ _) =>
          assert (A2 : AG (fun i => 0 <= i < 16) (arr_set a1 (r + 1) (wrap16 (arr_get a1 (r + 1) + 2))) (arr_set a2 (r + 1) (wrap16 (arr_get a2 (r + 1) + 2))));
          [ apply AG_set2; [exact A1|]; intros Hr; rewrite (AG_get _ _ _ (r + 1) A1) by (rewrite arr_len_set in Hr; lia); reflexivity |] end.
        apply AG_set2; [exact A2|]. intros Hr. rewrite (AG_get _ _ _ ML A2) by (rewrite !arr_len_set in Hr; lia). reflexivity. }
      assert (R' : HR2 t V D (U1 FCf DL1 HPf 1 HM DPf (bl_adj ML BC1 r) OL SL mc) (U2 FCg DL2 HPg 1 HM DPg (bl_adj ML BC2 r) OL SL mc)).
      { apply (HR2_U_repl V D DL1 BC1 DL2 BC2 OL SL); try assumption.
        - exact (hu_dl t s1 s2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ R).
        - unfold bl_adj. rewrite !arr_len_set. exact LBC1.
        - unfold bl_adj. rewrite !arr_len_set. exact LBC2. }
      destruct (0 <? ovf - 2).
      + exact (IH (ovf - 2) DL1 _ DL2 _ OL SL R' ABC').
      + exists (bl_adj ML BC1 r), (bl_adj ML BC2 r). split; [reflexivity|]. split; [reflexivity|]. split; [exact R' | exact ABC'].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  Local Notation nleaf := (nleaf t L HPf).

  Lemma loop3i_gb_rel : forall f bits n h DL1 BC1 DL2 BC2 OL SL,
    HR2 t V D (U1 FCf DL1 HPf 1 HM DPf BC1 OL SL mc) (U2 FCg DL2 HPg 1 HM DPg BC2 OL SL mc) ->
    (Z.of_nat f >= h - HM) -> HM + 1 <= h <= 573 -> 0 <= n <= nleaf h ->
    exists DL1' OL' DL2' h',
      gen_bitlen_loop3i f (U1 FCf DL1 HPf 1 HM DPf BC1 OL SL mc) t mc bits n h = (U1 FCf DL1' HPf 1 HM DPf BC1 OL' SL mc, h')
      /\ gen_bitlen_loop3i f (U2 FCg DL2 HPg 1 HM DPg BC2 OL SL mc) t mc bits n h = (U2 FCg DL2' HPg 1 HM DPg BC2 OL' SL mc, h')
      /\ HR2 t V D (U1 FCf DL1' HPf 1 HM DPf BC1 OL' SL mc) (U2 FCg DL2' HPg 1 HM DPg BC2 OL' SL mc)
      /\ HM + 1 <= h' <= h /\ nleaf h' = nleaf h - n.
  Proof.
    induction f as [|f IH]; intros bits n h DL1 BC1 DL2 BC2 OL SL R Hf Hh Hn.
    - exists DL1, OL, DL2, h. cbn [gen_bitlen_loop3i].
      assert (n = 0 \/ h = HM) by lia. pose proof (nleaf_base t L HPf) as NB.
      destruct H as [-> | ->]; [| exfalso; lia].
      split; [reflexivity|]. split; [reflexivity|]. split; [exact R|]. lia.
    - pose proof GB_ranges as RG.
      rewrite !(GL3i_step t mc). destruct (Z.eqb_spec n 0) as [N0|N0]; cbn [negb].
      { exists DL1, OL, DL2, h. split; [reflexivity|]. split; [reflexivity|]. split; [exact R|]. lia. }
      (* [comment removed for export] *)
      assert (Hh1 : HM + 1 <= h - 1).
      { destruct (Z_lt_le_dec (HM + 1) h) as [|C0]; [lia|]. exfalso. replace h with (HM + 1) in Hn by lia. rewrite (nleaf_base t L HPf) in Hn. lia. }
      pose proof (hu_lens t s1 s2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ R) as (LFC1 & LFC2 & LDL1 & LDL2 & LHP1 & LHP2 & LDP1 & LDP2 & LBC1 & LBC2).
      pose proof (hu_fc t s1 s2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ R) as AFC. pose proof (hu_dl t s1 s2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ R) as ADL.
      pose proof (hu_hp t s1 s2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ R) as AHP.
      set (m := arr_get HPf (h - 1)).
      destruct (AHP (h - 1) ltac:(apply tail_live; lia)) as [Em Vm]. fold m in Em.
      assert (Edl : arr_get DL2 m = arr_get DL1 m) by (symmetry; apply (AG_get _ _ _ _ ADL); apply TD; lia).
      assert (Efc : arr_get FCg m = arr_get FCf m) by (symmetry; apply (AG_get _ _ _ _ AFC); right; exact Vm).
      pose proof (nleaf_step t L HPf (h - 1) ltac:(lia)) as NS. replace (h - 1 + 1) with h in NS by lia.
      pose proof (nd_cases t _ _ _ _ _ _ _ _ HR (h - 1) ltac:(unfold tail; lia)) as NC.
      pose proof (leaf_mc t _ _ _ _ _ _ _ _ HR (h - 1) ltac:(unfold tail; lia)) as LM.
      unfold RefDeflSafeB3.nd in NC, LM. fold m in NC, LM.
      rewrite (GB3i_flat t mc s1), (GB3i_flat t mc s2). cbv zeta. rewrite Em, Edl, Efc. fold m.
      destruct (Z.ltb_spec mc m) as [Ci|Cl].
      + (* [comment removed for export] *)
        unfold RefDeflSafeB3.leafb, RefDeflSafeB3.nd in NS. fold m in NS.
        replace (m <? E) with false in NS by (symmetry; apply Z.ltb_ge; lia). cbn [zind] in NS.
        destruct (IH bits n (h - 1) DL1 BC1 DL2 BC2 OL SL R ltac:(lia) ltac:(lia) ltac:(lia)) as (DL1' & OL' & DL2' & h' & E1 & E2 & R' & B1 & B2).
        exists DL1', OL', DL2', h'. split; [exact E1|]. split; [exact E2|]. split; [exact R'|]. lia.
      + assert (Lf : RefDeflSafeB3.leafb t HPf (h - 1) = true) by (unfold RefDeflSafeB3.leafb, RefDeflSafeB3.nd; apply Z.ltb_lt; lia).
        rewrite Lf in NS. cbn [zind] in NS.
        destruct (Z.eqb_spec (arr_get DL1 m) bits) as [Eb|Nb].
        * destruct (IH bits (n - 1) (h - 1) DL1 BC1 DL2 BC2 OL SL R ltac:(lia) ltac:(lia) ltac:(lia)) as (DL1' & OL' & DL2' & h' & E1 & E2 & R' & B1 & B2).
          exists DL1', OL', DL2', h'. split; [exact E1|]. split; [exact E2|]. split; [exact R'|]. lia.
        * set (DL1' := arr_set DL1 m (wrap16 bits)). set (DL2' := arr_set DL2 m (wrap16 bits)).
          set (OL' := wrap64 (OL + (bits - arr_get DL1 m) * arr_get FCf m)).
          assert (R1 : HR2 t V D (U1 FCf DL1' HPf 1 HM DPf BC1 OL' SL mc) (U2 FCg DL2' HPg 1 HM DPg BC2 OL' SL mc)).
          { apply (HR2_U_repl V D DL1 BC1 DL2 BC2 OL SL); try assumption.
            - subst DL1' DL2'. apply AG_set. exact ADL.
            - subst DL1'. rewrite arr_len_set. exact LDL1. }
          destruct (IH bits (n - 1) (h - 1) DL1' BC1 DL2' BC2 OL' SL R1 ltac:(lia) ltac:(lia) ltac:(lia)) as (DL1f & OLf & DL2f & h' & E1 & E2 & R' & B1 & B2).
          exists DL1f, OLf, DL2f, h'. split; [exact E1|]. split; [exact E2|]. split; [exact R'|]. lia.
  Qed.

  Lemma loop3_gb_rel : forall f bits h DL1 BC1 DL2 BC2 OL SL,
    HR2 t V D (U1 FCf DL1 HPf 1 HM DPf BC1 OL SL mc) (U2 FCg DL2 HPg 1 HM DPg BC2 OL SL mc) ->
    AG (fun i => 0 <= i < 16) BC1 BC2 ->
    0 <= bits <= ML -> HM + 1 <= h <= 573 ->
    zsum (arr_get BC1) 1 (Z.to_nat bits) <= nleaf h -> (forall b, 1 <= b <= ML -> 0 <= arr_get BC1 b) ->
    exists DL1' OL' DL2',
      gen_bitlen_loop3 f (U1 FCf DL1 HPf 1 HM DPf BC1 OL SL mc) t mc bits h = U1 FCf DL1' HPf 1 HM DPf BC1 OL' SL mc
      /\ gen_bitlen_loop3 f (U2 FCg DL2 HPg 1 HM DPg BC2 OL SL mc) t mc bits h = U2 FCg DL2' HPg 1 HM DPg BC2 OL' SL mc
      /\ HR2 t V D (U1 FCf DL1' HPf 1 HM DPf BC1 OL' SL mc) (U2 FCg DL2' HPg 1 HM DPg BC2 OL' SL mc).
  Proof.
    induction f as [|f IH]; intros bits h DL1 BC1 DL2 BC2 OL SL R ABC Hbits Hh Hdem Hnn.
    - exists DL1, OL, DL2. cbn [gen_bitlen_loop3]. split; [reflexivity|]. split; [reflexivity | exact R].
    - pose proof GB_ranges as RG.
      pose proof (hu_lens t s1 s2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ R) as (_ & _ & _ & _ & _ & _ & _ & _ & LBC1 & LBC2).
      rewrite !(GL3_step t mc). rewrite !bt_bl_count_get.
      destruct (Z.eqb_spec bits 0) as [B0|B0]; cbn [negb].
      { exists DL1, OL, DL2. split; [reflexivity|]. split; [reflexivity | exact R]. }
      rewrite <- (AG_get _ _ _ bits ABC) by lia.
      assert (Hc : 0 <= arr_get BC1 bits <= nleaf h).
      { pose proof (Hnn bits ltac:(lia)). split; [lia|].
        pose proof (zsum_ge_point (arr_get BC1) 1 (Z.to_nat bits) bits ltac:(intros; apply Hnn; lia) ltac:(lia)). lia. }
      destruct (loop3i_gb_rel 574 bits (arr_get BC1 bits) h DL1 BC1 DL2 BC2 OL SL R ltac:(lia) Hh Hc) as (DL1a & OLa & DL2a & h1 & E1 & E2 & Ra & B1 & B2).
      rewrite E1, E2.
      destruct (IH (bits - 1) h1 DL1a BC1 DL2a BC2 OLa SL Ra ABC ltac:(lia) ltac:(lia)) as (DL1' & OL' & DL2' & E1' & E2' & R'); try assumption.
      { replace (Z.to_nat bits) with (S (Z.to_nat (bits - 1))) in Hdem by lia. rewrite zsum_snoc in Hdem.
        replace (1 + Z.of_nat (Z.to_nat (bits - 1))) with bits in Hdem by lia. lia. }
      exists DL1', OL', DL2'. split; [exact E1'|]. split; [exact E2' | exact R'].
  Qed.
End Passes.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma AG_fill0 : forall (a b : arr) n, arr_len a = n -> arr_len b = n ->
  AG (fun i => 0 <= i < n) (arr_fill a 0 n 0) (arr_fill b 0 n 0).
Proof.
  intros a b n La Lb. split; [rewrite !arr_len_fill; congruence|].
  intros i Hi. rewrite !arr_get_fill. unfold arr_inb. rewrite La, Lb.
  replace ((0 <=? i) && (i <? 0 + Z.max 0 n) && ((0 <=? i) && (i <? n))) with true; [reflexivity|].
  symmetry. rewrite !andb_true_iff, !Z.leb_le, !Z.ltb_lt. lia.
Qed.

Theorem gen_bitlen_relU : forall V D BC1 BC2 DLg OL SL,
  HR2 t V D (U1 FCf DLf HPf 1 HM DPf BC1 OL SL mc) (U2 FCg DLg HPg 1 HM DPg BC2 OL SL mc) ->
  (forall p, HM < p < 573 -> D (arr_get HPf p)) ->
  0 <= OL < 2 ^ 64 -> 0 <= SL < 2 ^ 64 ->
  exists DL1' BC1' OL' SL' DL2' BC2',
    gen_bitlen (U1 FCf DLf HPf 1 HM DPf BC1 OL SL mc) t = U1 FCf DL1' HPf 1 HM DPf BC1' OL' SL' mc
    /\ gen_bitlen (U2 FCg DLg HPg 1 HM DPg BC2 OL SL mc) t = U2 FCg DL2' HPg 1 HM DPg BC2' OL' SL' mc
    /\ HR2 t V (fun u => D u \/ u = arr_get HPf HM) (U1 FCf DL1' HPf 1 HM DPf BC1' OL' SL' mc) (U2 FCg DL2' HPg 1 HM DPg BC2' OL' SL' mc)
    /\ AG (fun i => 0 <= i < 16) BC1' BC2'.
Proof.
  intros V D BC1 BC2 DLg OL SL R TD HOL HSL. pose proof GB_ranges as RG.
  pose proof (hu_lens t s1 s2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ R) as (LFC1 & LFC2 & LDL1 & LDL2 & LHP1 & LHP2 & LDP1 & LDP2 & LBC1 & LBC2).
  pose proof (hu_fc t s1 s2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ R) as AFC. pose proof (hu_dl t s1 s2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ R) as ADL.
  pose proof (hu_dp t s1 s2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ R) as ADP. pose proof (hu_hp t s1 s2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ R) as AHP.
  pose proof (hu_V t s1 s2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ R) as HV.
  set (root := arr_get HPf HM).
  destruct (AHP HM ltac:(unfold live; lia)) as [Er Vr]. fold root in Er, Vr.
  set (D' := fun u => D u \/ u = root).
  assert (TD9 : forall p, HM <= p < 573 -> D' (arr_get HPf p)).
  { intros p Hp. destruct (Z.eq_dec p HM) as [->|N]; [right; reflexivity | left; apply TD; lia]. }
  assert (DI9 : forall u, E <= u < E + L - 1 -> D' u).
  { intros u Hu. destruct (tail_pos u (or_introl Hu)) as (p & Hp & <-). apply TD9. exact Hp. }
  unfold gen_bitlen. autorewrite with btupd. unfold heap_get. autorewrite with btupd. rewrite Er. fold root.
  set (BC1a := arr_fill BC1 0 (MAX_BITS + 1) 0). set (BC2a := arr_fill BC2 0 (MAX_BITS + 1) 0).
  set (DL1a := arr_set DLf root (wrap16 0)). set (DL2a := arr_set DLg root (wrap16 0)).
  assert (ABCa : AG (fun i => 0 <= i < 16) BC1a BC2a) by (subst BC1a BC2a; unfold MAX_BITS; apply (AG_fill0 BC1 BC2 16 LBC1 LBC2)).
  assert (LBC1a : arr_len BC1a = 16) by (subst BC1a; rewrite arr_len_fill; exact LBC1).
  assert (LBC2a : arr_len BC2a = 16) by (subst BC2a; rewrite arr_len_fill; exact LBC2).
  assert (R9 : HR2 t V D' (U1 FCf DL1a HPf 1 HM DPf BC1a OL SL mc) (U2 FCg DL2a HPg 1 HM DPg BC2a OL SL mc)).
  { apply (HR2_U t s1 s2 TL1 TL2); try assumption.
    - subst DL1a DL2a. apply AG_set_ext; [exact ADL | pose proof (HV root Vr); lia].
    - subst DL1a. rewrite arr_len_set. exact LDL1. }
  pose proof (L1_init t _ _ _ _ _ _ _ _ HR s1 BC1 OL SL LBC1 HOL HSL) as I9. fold root in I9. fold BC1a DL1a in I9.
  destruct (loop1_gb_rel V D' TD9 DI9 573 (HM + 1) 0 DL1a BC1a OL SL DL2a BC2a BC1 OL SL R9 ABCa I9 ltac:(lia))
    as (DL1b & BC1b & OLb & SLb & DL2b & BC2b & ovf & E1 & E2 & Rb & ABCb & I10).
  rewrite E1, E2.
  destruct (Z.eqb_spec ovf 0) as [Z0|NZ].
  { exists DL1b, BC1b, OLb, SLb, DL2b, BC2b. split; [reflexivity|]. split; [reflexivity|]. split; [exact Rb | exact ABCb]. }
  (* [comment removed for export] *)
  destruct (l1_X _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ I10) as (DLx & BCx & OLx & SLx & EX & HDL10 & LDL10 & HBC10 & LBC10 & _).
  pose proof (f_equal (fun x => ds_bl_count x) EX) as EBC. cbv beta in EBC. autorewrite with btupd in EBC. subst BCx.
  pose proof (l1_ovf _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ I10) as Hovf.
  replace (Z.to_nat (573 - HM - 1)) with (Z.to_nat (572 - HM)) in HBC10, Hovf by lia.
  rewrite (ovf_identity t _ _ _ _ _ _ _ _ HR) in Hovf.
  assert (HI : L2I t L HPf (arr_get BC1b) (2 * NI t L HPf 573)).
  { apply (L2I_ext t _ _ _ _ _ _ _ _ HR (cntL t L HPf)); [exact (L2_init t _ _ _ _ _ _ _ _ HR)|]. intros b Hb. rewrite HBC10 by exact Hb. reflexivity. }
  pose proof (NI_bound t _ _ _ _ _ _ _ _ HR) as NIB.
  pose proof (hu_lens t s1 s2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Rb) as (_ & _ & LDL1b & _ & _ & _ & _ & _ & LBC1b & LBC2b).
  destruct (loop2_run t _ _ _ _ _ _ _ _ HR 573 (NI t L HPf 573) s1 FCf DL1b HPf 1 HM DPf BC1b OLb SLb mc ltac:(lia) ltac:(lia) HI LBC1b)
    as (BCr & EQ2 & HI2 & LBCr & _).
  destruct (loop2_gb_rel V D' 573 ovf DL1b BC1b DL2b BC2b OLb SLb Rb ABCb) as (BC1c & BC2c & E1c & E2c & Rc & ABCc).
  rewrite Hovf in E1c. rewrite EQ2 in E1c.
  pose proof (f_equal (fun x => ds_bl_count x) E1c) as EBC. cbv beta in EBC. autorewrite with btupd in EBC. subst BCr.
  rewrite <- Hovf in EQ2. rewrite EQ2, E2c. unfold HEAP_SIZE.
  destruct (loop3_gb_rel V D' TD9 (Z.to_nat ML) ML 573 DL1b BC1c DL2b BC2c OLb SLb Rc ABCc ltac:(lia) ltac:(lia)) as (DL1' & OL' & DL2' & E1' & E2' & R').
  { destruct HI2 as [NN Z0 HI0 _ TOT _ _]. rewrite <- TOT.
    replace 16%nat with (S (Z.to_nat ML + (15 - Z.to_nat ML)))%nat by lia.
    rewrite zsum_shift, Z0, zsum_split. replace (0 + 1) with 1 by lia.
    pose proof (zsum_nonneg (arr_get BC1c) (1 + Z.of_nat (Z.to_nat ML)) (15 - Z.to_nat ML) ltac:(intros; apply NN; lia)). lia. }
  { intros b Hb. apply (l2_nn _ _ _ _ _ HI2). lia. }
  exists DL1', BC1c, OL', SLb, DL2', BC2c. split; [exact E1'|]. split; [exact E2'|]. split; [exact R' | exact ABCc].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma NC_rel : forall f (b1 b2 nc : arr) code bits,
  (forall i, 0 <= i < 16 -> arr_get b2 i = arr_get b1 i) -> 1 <= bits ->
  gen_codes_loop1 f b2 nc code bits = gen_codes_loop1 f b1 nc code bits.
Proof.
  induction f as [|f IH]; intros b1 b2 nc code bits Hb Hbits; [reflexivity|].
  cbn [gen_codes_loop1]. destruct (Z.leb_spec bits MAX_BITS) as [C|C]; [|reflexivity].
  unfold MAX_BITS in C. rewrite Hb by lia. apply IH; [exact Hb | lia].
Qed.

Lemma gen_codes_loop2_rel : forall V D f nc a1 DL1 HP1 DP1 BC1 a2 DL2 HP2 DP2 BC2 HL HMx OL SL n,
  HR2 t V D (U1 a1 DL1 HP1 HL HMx DP1 BC1 OL SL mc) (U2 a2 DL2 HP2 HL HMx DP2 BC2 OL SL mc) ->
  (forall u, 0 <= u < E -> D u) -> 0 <= n ->
  exists a1' a2',
    gen_codes_loop2 f (set_tree_fc (U1 a1 DL1 HP1 HL HMx DP1 BC1 OL SL mc) t a1) t nc mc n = U1 a1' DL1 HP1 HL HMx DP1 BC1 OL SL mc
    /\ gen_codes_loop2 f (set_tree_fc (U2 a2 DL2 HP2 HL HMx DP2 BC2 OL SL mc) t a2) t nc mc n = U2 a2' DL2 HP2 HL HMx DP2 BC2 OL SL mc
    /\ HR2 t V D (U1 a1' DL1 HP1 HL HMx DP1 BC1 OL SL mc) (U2 a2' DL2 HP2 HL HMx DP2 BC2 OL SL mc).
Proof.
  intros V D f. induction f as [|f IH]; intros nc a1 DL1 HP1 DP1 BC1 a2 DL2 HP2 DP2 BC2 HL HMx OL SL n R DE Hn.
  - exists a1, a2. cbn [gen_codes_loop2]. rewrite !bt_set_tree_fc. split; [reflexivity|]. split; [reflexivity | exact R].
  - pose proof GB_ranges as RG.
    rewrite !loop2_S. destruct (Z.leb_spec n mc) as [C|C].
    2:{ exists a1, a2. rewrite !bt_set_tree_fc. split; [reflexivity|]. split; [reflexivity | exact R]. }
    cbv zeta. rewrite !bt_Len.
    pose proof (hu_dl t s1 s2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ R) as ADL. pose proof (hu_fc t s1 s2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ R) as AFC.
    rewrite <- (AG_get _ _ _ n ADL) by (apply DE; lia).
    destruct (Z.eqb_spec (arr_get DL1 n) 0) as [L0|L0].
    + exact (IH nc a1 DL1 HP1 DP1 BC1 a2 DL2 HP2 DP2 BC2 HL HMx OL SL (n + 1) R DE ltac:(lia)).
    + set (v := wrap16 (bi_reverse (arr_get nc (arr_get DL1 n)) (arr_get DL1 n))).
      assert (R1 : HR2 t V D (U1 (arr_set a1 n v) DL1 HP1 HL HMx DP1 BC1 OL SL mc) (U2 (arr_set a2 n v) DL2 HP2 HL HMx DP2 BC2 OL SL mc)).
      { pose proof (hu_lens t s1 s2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ R) as (LFC1 & LFC2 & LDL1 & LDL2 & LHP1 & LHP2 & LDP1 & LDP2 & LBC1 & LBC2).
        apply (HR2_U t s1 s2 TL1 TL2); try assumption; try (rewrite arr_len_set; assumption).
        - apply AG_set. exact AFC.
        - exact (hu_dp t s1 s2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ R).
        - exact (hu_hp t s1 s2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ R).
        - exact (hu_V t s1 s2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ R). }
      rewrite (bt_set_tree_fc s1 t a1 DL1 HP1 HL HMx DP1 BC1 OL SL mc (arr_set a1 n v)).
      rewrite (bt_set_tree_fc s2 t a2 DL2 HP2 HL HMx DP2 BC2 OL SL mc (arr_set a2 n v)).
      rewrite <- (bt_set_tree_fc s1 t (arr_set a1 n v) DL1 HP1 HL HMx DP1 BC1 OL SL mc (arr_set a1 n v)).
      rewrite <- (bt_set_tree_fc s2 t (arr_set a2 n v) DL2 HP2 HL HMx DP2 BC2 OL SL mc (arr_set a2 n v)).
      exact (IH (arr_set nc (arr_get DL1 n) (wrap16 (arr_get nc (arr_get DL1 n) + 1))) _ DL1 HP1 DP1 BC1 _ DL2 HP2 DP2 BC2 HL HMx OL SL (n + 1) R1 DE ltac:(lia)).
Qed.

Theorem gen_codes_relU : forall V D FC1 DL1 HP1 DP1 BC1 FC2 DL2 HP2 DP2 BC2 HL HMx OL SL,
  HR2 t V D (U1 FC1 DL1 HP1 HL HMx DP1 BC1 OL SL mc) (U2 FC2 DL2 HP2 HL HMx DP2 BC2 OL SL mc) ->
  (forall u, 0 <= u < E -> D u) -> AG (fun i => 0 <= i < 16) BC1 BC2 ->
  exists FC1' FC2',
    gen_codes (U1 FC1 DL1 HP1 HL HMx DP1 BC1 OL SL mc) t mc = U1 FC1' DL1 HP1 HL HMx DP1 BC1 OL SL mc
    /\ gen_codes (U2 FC2 DL2 HP2 HL HMx DP2 BC2 OL SL mc) t mc = U2 FC2' DL2 HP2 HL HMx DP2 BC2 OL SL mc
    /\ HR2 t V D (U1 FC1' DL1 HP1 HL HMx DP1 BC1 OL SL mc) (U2 FC2' DL2 HP2 HL HMx DP2 BC2 OL SL mc).
Proof.
  intros V D FC1 DL1 HP1 DP1 BC1 FC2 DL2 HP2 DP2 BC2 HL HMx OL SL R DE ABC. pose proof GB_ranges as RG.
  unfold gen_codes. autorewrite with btupd.
  rewrite (NC_rel 16 BC1 BC2) by (first [lia | intros i Hi; symmetry; apply (AG_get _ _ _ i ABC); exact Hi]).
  rewrite <- (bt_set_tree_fc s1 t FC1 DL1 HP1 HL HMx DP1 BC1 OL SL mc FC1).
  rewrite <- (bt_set_tree_fc s2 t FC2 DL2 HP2 HL HMx DP2 BC2 OL SL mc FC2).
  apply (gen_codes_loop2_rel V D); [exact R | exact DE | lia].
Qed.
End GB.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section Assemble.
Variable t : tree_id.
Local Notation E := (sd_elems t).
Local Notation TS := (tsize t).
Variable s1 : deflate_state.
Variable s2 : deflate_state.
Hypothesis TL1 : tree_lens s1.
Hypothesis TL2 : tree_lens s2.
Local Notation U1 := (bt_upd s1 t).
Local Notation U2 := (bt_upd s2 t).

(* [comment removed for export] *)
Lemma U_inj : forall FC DL HP HL HM DP BC OL SL MC FC' DL' HP' HL' HM' DP' BC' OL' SL' MC',
  U1 FC DL HP HL HM DP BC OL SL MC = U1 FC' DL' HP' HL' HM' DP' BC' OL' SL' MC' ->
  FC = FC' /\ DL = DL' /\ HP = HP' /\ HL = HL' /\ HM = HM' /\ DP = DP' /\ BC = BC' /\ OL = OL' /\ SL = SL' /\ MC = MC'.
Proof.
  intros * EQ.
  pose proof (f_equal (fun x => tree_fc x t) EQ) as E1. pose proof (f_equal (fun x => tree_dl x t) EQ) as E2.
  pose proof (f_equal ds_heap EQ) as E3. pose proof (f_equal ds_heap_len EQ) as E4. pose proof (f_equal ds_heap_max EQ) as E5.
  pose proof (f_equal ds_depth EQ) as E6. pose proof (f_equal ds_bl_count EQ) as E7. pose proof (f_equal ds_opt_len EQ) as E8.
  pose proof (f_equal ds_static_len EQ) as E9. pose proof (f_equal (fun x => max_code x t) EQ) as E10.
  cbv beta in E1, E2, E10. autorewrite with btupd in E1. autorewrite with btupd in E2. autorewrite with btupd in E3.
  autorewrite with btupd in E4. autorewrite with btupd in E5. autorewrite with btupd in E6. autorewrite with btupd in E7.
  autorewrite with btupd in E8. autorewrite with btupd in E9. autorewrite with btupd in E10.
  repeat split; assumption.
Qed.

Theorem build_tree_relU : forall FC1 DL1 HP1 DP1 BC1 HL01 HM01 MC1 FC2 DL2 HP2 DP2 BC2 HL02 HM02 MC2 OL SL,
  arr_len FC1 = TS -> arr_len DL1 = TS -> arr_len HP1 = 573 -> arr_len DP1 = 573 -> arr_len BC1 = 16 ->
  arr_len FC2 = TS -> arr_len DL2 = TS -> arr_len HP2 = 573 -> arr_len DP2 = 573 -> arr_len BC2 = 16 ->
  (forall i, 0 <= arr_get FC1 i < 65536) -> (forall i, 0 <= arr_get DL1 i < 65536) -> (forall i, 0 <= arr_get DP1 i < 256) ->
  0 <= OL < 2 ^ 64 -> 0 <= SL < 2 ^ 64 ->
  AG (fun i => 0 <= i < E) FC1 FC2 ->
  exists FC1' DL1' HP1' DP1' BC1' FC2' DL2' HP2' DP2' BC2' HMf OLf SLf mc,
    build_tree (U1 FC1 DL1 HP1 HL01 HM01 DP1 BC1 OL SL MC1) t = U1 FC1' DL1' HP1' 1 HMf DP1' BC1' OLf SLf mc
    /\ build_tree (U2 FC2 DL2 HP2 HL02 HM02 DP2 BC2 OL SL MC2) t = U2 FC2' DL2' HP2' 1 HMf DP2' BC2' OLf SLf mc
    /\ AG (fun i => 0 <= i < E) FC1' FC2' /\ AG (fun i => 0 <= i < E) DL1' DL2' /\ AG (fun i => 0 <= i < 16) BC1' BC2'
    /\ 0 <= mc < E
    /\ arr_len FC1' = TS /\ arr_len FC2' = TS /\ arr_len DL1' = TS /\ arr_len DL2' = TS /\ arr_len BC1' = 16 /\ arr_len BC2' = 16
    /\ arr_len HP1' = 573 /\ arr_len HP2' = 573 /\ arr_len DP1' = 573 /\ arr_len DP2' = 573.
Proof.
  intros FC1 DL1 HP1 DP1 BC1 HL01 HM01 MC1 FC2 DL2 HP2 DP2 BC2 HL02 HM02 MC2 OL SL
         LFC1 LDL1 LHP1 LDP1 LBC1 LFC2 LDL2 LHP2 LDP2 LBC2 RFC1 RDL1 RDP1 HOL HSL AFC.
  pose proof (E_TS t) as HE. pose proof (AG_len _ _ _ AFC) as LFC12.
  (* [comment removed for export] *)
  pose proof (heap_phase s1 t FC1 DL1 HP1 HL01 HM01 DP1 BC1 OL SL MC1 LFC1 LDL1 LHP1 LDP1 RFC1 RDL1 RDP1) as H.
  cbv zeta in H. autorewrite with btupd in H. unfold HEAP_SIZE in H.
  unfold build_tree. autorewrite with btupd. unfold HEAP_SIZE.
  (* [comment removed for export] *)
  assert (R0 : HR2 t (fun _ => False) (fun _ => False) (U1 FC1 DL1 HP1 0 573 DP1 BC1 OL SL MC1) (U2 FC2 DL2 HP2 0 573 DP2 BC2 OL SL MC2)).
  { apply (HR2_U t s1 s2 TL1 TL2); try assumption.
    - eapply AG_mono; [exact AFC|]. intros i [Hi|Hi]; [exact Hi | destruct Hi].
    - split; [congruence | intros i Hi; destruct Hi].
    - split; [congruence | intros i Hi; destruct Hi].
    - intros j Hj. exfalso. unfold live in Hj. lia.
    - intros u Hu. destruct Hu. }
  destruct (loop1_relU t s1 s2 TL1 TL2 (Z.to_nat E) 0 (-1) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ R0 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia))
    as (DL1a & HP1a & DP1a & DL2a & HP2a & DP2a & HLa & mca & E1a & E2a & Ra & Ba & Bmc).
  rewrite E1a, E2a. rewrite E1a in H.
  (* [comment removed for export] *)
  destruct (loop2_relU t s1 s2 TL1 TL2 2 mca _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Ra ltac:(lia) Bmc)
    as (FC1b & HP1b & DP1b & FC2b & HP2b & DP2b & HLb & OLb & SLb & mcb & Vb & E1b & E2b & Rb & Vb1 & Vb2 & Bb & FEb).
  rewrite E1b, E2b. rewrite E1b in H. cbv beta iota in H. autorewrite with btupd in H. autorewrite with btupd.
  destruct H as (Fl & DLx & HPx & DPx & L & FCf & DLf & HPf & DPf & EQ3 & EQ7 & HR & _ & _ & _ & _ & _ & _ & _ & LF & _ & _ & FCE2 & DLE1).
  destruct (U_inj _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ EQ3) as (-> & -> & -> & -> & _ & -> & _ & -> & -> & _).
  pose proof (hr_L _ _ _ _ _ _ _ _ _ HR) as RL. pose proof (hr_mc _ _ _ _ _ _ _ _ _ HR) as Rmc.
  (* [comment removed for export] *)
  pose proof (HR2_U_mc t s1 s2 TL1 TL2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ mcb mcb Rb) as Rb'. clear Rb.
  assert (HL2h : 0 <= L / 2 <= L) by (split; [apply Z.div_pos; lia | apply Z.div_le_upper_bound; lia]).
  destruct (loop3_relU t s1 s2 (Z.to_nat (L / 2)) (L / 2) _ _ _ _ _ _ _ _ _ _ _ _ L 573 _ _ _ _ Rb' HL2h ltac:(lia))
    as (HP1c & HP2c & E1c & E2c & Rc & Oc).
  rewrite E1c, E2c. rewrite E1c in EQ7.
  (* [comment removed for export] *)
  assert (Rc' : HR2 t Vb (fun u => False \/ 0 <= u < E /\ arr_get FC1 u = 0)
                  (U1 (fc_forced Fl FC1) DLx HP1c (L - 0) (573 - 2 * 0) DPx BC1 (ol_forced Fl OL) (sl_forced t Fl SL) mcb)
                  (U2 FC2b DL2a HP2c (L - 0) (573 - 2 * 0) DP2b BC2 (ol_forced Fl OL) (sl_forced t Fl SL) mcb)).
  { replace (L - 0) with L by lia. replace (573 - 2 * 0) with 573 by lia. exact Rc. }
  destruct (loop4_relU t s1 s2 TL1 TL2 573 0 L _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Rc' ltac:(lia) ltac:(lia) ltac:(lia) ltac:(intros; lia))
    as (FC1d & DL1d & HP1d & DP1d & FC2d & DL2d & HP2d & DP2d & Vd & Dd & E1d & E2d & Rd & TDd & HV1 & HD1 & HV2 & FEd).
  replace (L - 0) with L in E1d, E2d by lia. replace (573 - 2 * 0) with 573 in E1d, E2d by lia. replace (E + 0) with E in E1d, E2d by lia.
  rewrite E1d, E2d. rewrite E1d in EQ7. autorewrite with btupd in EQ7. autorewrite with btupd.
  unfold SMALLEST in EQ7 |- *.
  replace (573 - 2 * (L - 1) - 1) with (RefDeflSafeB3.HM L) in EQ7 |- * by (unfold RefDeflSafeB3.HM; lia).
  replace (574 - 2 * L) with (RefDeflSafeB3.HM L) in EQ7 by reflexivity.
  pose proof (HM_range t _ _ _ _ _ _ _ _ HR) as RHM.
  pose proof (hu_hp t s1 s2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Rd 1 ltac:(unfold live; lia)) as [E21 V1]. rewrite E21.
  destruct (U_inj _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ EQ7) as (-> & -> & EHP & _ & _ & -> & _ & _ & _ & _). rewrite EHP.
  pose proof (hu_lens t s1 s2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Rd) as (LFCd1 & LFCd2 & LDLd1 & LDLd2 & LHPd1 & LHPd2 & LDPd1 & LDPd2 & _ & _).
  set (HPg := arr_set HP2d (RefDeflSafeB3.HM L) (arr_get HP1d 1)).
  assert (R7 : HR2 t Vd Dd (U1 FCf DLf HPf 1 (RefDeflSafeB3.HM L) DPf BC1 (ol_forced Fl OL) (sl_forced t Fl SL) mcb)
                         (U2 FC2d DL2d HPg 1 (RefDeflSafeB3.HM L) DP2d BC2 (ol_forced Fl OL) (sl_forced t Fl SL) mcb)).
  { rewrite <- EHP. subst HPg. apply (HR2_U t s1 s2 TL1 TL2); try assumption; try (rewrite arr_len_set; assumption).
    - exact (hu_fc t s1 s2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Rd).
    - exact (hu_dl t s1 s2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Rd).
    - exact (hu_dp t s1 s2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Rd).
    - intros j Hj. rewrite !arr_get_set. unfold arr_inb. rewrite LHPd1, LHPd2.
      destruct (Z.eqb_spec (RefDeflSafeB3.HM L) j) as [<-|N]; cbn [andb].
      + replace ((0 <=? RefDeflSafeB3.HM L) && (RefDeflSafeB3.HM L <? 573)) with true by (symmetry; apply andb_true_intro; split; [apply Z.leb_le | apply Z.ltb_lt]; lia).
        split; [reflexivity | exact V1].
      + apply (hu_hp t s1 s2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Rd). unfold live in *. unfold RefDeflSafeB3.HM in *. lia.
    - exact (hu_V t s1 s2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Rd). }
  assert (TD7 : forall p, RefDeflSafeB3.HM L < p < 573 -> Dd (arr_get HPf p)).
  { intros p Hp. rewrite <- EHP. rewrite arr_get_set. destruct (Z.eqb_spec (RefDeflSafeB3.HM L) p); [lia|]. cbn [andb]. apply TDd. unfold RefDeflSafeB3.HM in *. lia. }
  assert (ROL : 0 <= ol_forced Fl OL < 2 ^ 64).
  { unfold ol_forced. destruct Fl as [|a [|b [|c l]]]; cbn [fold_left]; [exact HOL | apply wrap64_range | apply wrap64_range | cbn in LF; lia]. }
  assert (RSL : 0 <= sl_forced t Fl SL < 2 ^ 64).
  { unfold sl_forced. destruct (stree_has t); [| exact HSL].
    destruct Fl as [|a [|b [|c l]]]; cbn [fold_left]; [exact HSL | apply wrap64_range | apply wrap64_range | cbn in LF; lia]. }
  destruct (gen_bitlen_relU t s1 s2 TL1 TL2 _ _ _ _ _ _ _ _ HR FC2d HPg DP2d Vd Dd BC1 BC2 DL2d _ _ R7 TD7 ROL RSL)
    as (DL1e & BC1e & OLe & SLe & DL2e & BC2e & EG1 & EG2 & Re & ABCe).
  rewrite EG1, EG2.
  (* [comment removed for export] *)
  assert (DE : forall u, 0 <= u < E -> Dd u \/ u = arr_get HPf (RefDeflSafeB3.HM L)).
  { intros u Hu. destruct (Z.eq_dec (arr_get FC1 u) 0) as [Z0|NZ].
    - left. apply HD1. right. split; [exact Hu | exact Z0].
    - assert (Vu : Vj t (fc_forced Fl FC1) (L - 1) u).
      { unfold Vj, V0, Vscan. left. split; [exact Hu|]. rewrite FCE2. destruct (existsb _ _); [lia | exact NZ]. }
      destruct (hr_cov _ _ _ _ _ _ _ _ _ HR u Vu) as (p & Hp & Ep).
      destruct (Z.eq_dec p (RefDeflSafeB3.HM L)) as [->|Np]; [right; symmetry; exact Ep|].
      left. rewrite <- Ep. apply TD7. unfold RefDeflSafeB3.HM in *. lia. }
  destruct (gen_codes_relU t s1 s2 TL1 TL2 _ _ _ _ _ _ _ _ HR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Re DE ABCe) as (FC1g & FC2g & EC1 & EC2 & Rg).
  rewrite EC1, EC2.
  pose proof (hu_lens t s1 s2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Rg) as (L1 & L2 & L3 & L4 & L5 & L6 & L7 & L8 & L9 & L10).
  exists FC1g, DL1e, HPf, DPf, BC1e, FC2g, DL2e, HPg, DP2d, BC2e, (RefDeflSafeB3.HM L), OLe, SLe, mcb.
  split; [reflexivity|]. split; [reflexivity|].
  split; [eapply AG_mono; [exact (hu_fc t s1 s2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Rg) | intros i Hi; left; exact Hi]|].
  split; [eapply AG_mono; [exact (hu_dl t s1 s2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Rg) | intros i Hi; exact (DE i Hi)]|].
  split; [exact ABCe|]. split; [exact Rmc|].
  repeat split; assumption.
Qed.
End Assemble.
