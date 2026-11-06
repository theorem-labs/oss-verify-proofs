(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

(* [comment removed for export] *)
From Stdlib Require ZArith.
From Stdlib Require NArith.
From Stdlib Require List.
From Stdlib Require Bool.
From Stdlib Require Lia.
From Stdlib Require Permutation.
From stdpp Require gmap.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require STree.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require Malloc.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require MallocCtrl.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require KInv.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require KStep.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require MEX_defs.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require MI_Inv.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require MI_Kit.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require MI_Cnt.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require MI_Ext.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require MI_Pres1.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require MI_Pres4.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require MI_WFree2.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require MI_WEnframe2.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require MI_Contracts.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require Realloc.
Module MI_WRealloc.
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.micromega.Lia Stdlib.Sorting.Permutation.
Import stdpp.gmap.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.STree OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Malloc OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MallocCtrl OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.KInv OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.KStep OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MEX_defs.MI_Tree OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MI_Inv OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MI_Kit OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MI_Cnt.MI_Arith OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MI_Ext.MI_List OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MI_Pres1.MI_Geom OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MI_Ext OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MI_Pres4.MI_Ext2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MI_Pres4.MI_Shadow OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MI_Pres1 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MI_Pres4.MI_Pres2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MI_WFree2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MI_WEnframe2.MI_WGroup OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MI_WEnframe2.MI_TF2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MI_Contracts.MI_WMalloc OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MI_WEnframe2.MI_WEnframe OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MI_WEnframe2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MI_Contracts.

Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Local Open Scope Z_scope.
Import Realloc.

(* [comment removed for export] *)
Section CeilWrap.
Context {ACEIL : Ceil}.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Ltac splits := repeat (lazymatch goal with |- _ /\ _ => split | |- _ => fail end).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition ss_list (p e : aptr) (n idx : Z) : list (aptr * Z) :=
  let res := snd e - snd p - n in
  (if negb (res =? 0) then [(aadd e (- res), 0)] else [])
  ++ (if 5 <=? res then [(aadd e (-4), res); (aadd (aadd e (-4)) 1, Z.shiftr res 8); (aadd (aadd e (-4)) 2, Z.shiftr res 16);
                         (aadd (aadd e (-4)) 3, Z.shiftr res 24); (aadd e (-5), 0)] else [])
  ++ [(aadd p (-3), idx + Z.shiftl (if 5 <=? res then 5 else res) 5)].

Lemma set_size_i_eq p e n idx st : set_size_i p e n idx st = wrs (ss_list p e n idx) st.
Proof.
  unfold set_size_i, ss_list. cbv zeta.
  destruct (snd e - snd p - n =? 0); destruct (5 <=? snd e - snd p - n); cbn beta iota delta [wr32 wrs app negb]; reflexivity.
Qed.

Lemma ss_list_addrs p e n idx a : fst e = fst p -> 0 <= snd e - snd p - n -> In a (map fst (ss_list p e n idx)) ->
  fst a = fst p /\ (snd a = snd p - 3 \/ (snd p + n <= snd a < snd e /\ snd e - snd p - n <> 0)).
Proof.
  intros Ef Hr Hin. unfold ss_list in Hin.
  destruct (Z.eqb_spec (snd e - snd p - n) 0) as [R0|R0]; destruct (Z.leb_spec 5 (snd e - snd p - n)) as [R5|R5];
    cbn [negb app map fst In] in Hin; unfold aadd in *; cbn [fst snd] in *.
  all: repeat match type of Hin with _ \/ _ => destruct Hin as [<-|Hin] | False => destruct Hin end; cbn [fst snd].
  all: split; [first [exact Ef| reflexivity]|].
  all: first [left; lia| right; lia].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Section SETSIZE.
Variables (s : mstate) (LA : mled) (BL1 : list blk) (LS : lhead -> list aptr).
Variables (c : cptr) (off n : Z) (m bm : aptr) (i ai : Z).
Let X1 := mkX [] [] (Some c) None None.
Hypothesis INV1 : INVL X1 s LA BL1 LS.
Hypothesis Hs : s_slots s !! c = Some (m, i).
Hypothesis Hg : s_groups s !! bm = Some (mkGhdr (Some m) ai).
Hypothesis Hi : 0 <= i <= m_last_idx (MR s m).
Hypothesis Ec : c = (fst bm, sstart (MR s m) i).
Hypothesis Ho : 0 <= off <= 255.
Hypothesis Hn : 0 <= n.
Let stride := get_stride (MR s m).
Let up : aptr := aadd c (UNIT * off).
Let e : aptr := aadd c (stride - IB).
Let res := stride - IB - UNIT * off - n.
Hypothesis Hfit : UNIT * off + n <= stride - IB.
Hypothesis S16 : 16 <= stride.
Hypothesis SM : stride mod 16 = 0.
Hypothesis RS : stride - IB - UNIT * off - n < 2^32.
Hypothesis OLD : forall o v t, r_cells (get_shadow s (fst c)) !! o = Some (v, t) -> snd up <= o < snd up + n -> (t < s_tick s)%N.
Let q := (snd c + UNIT * off - snd (gbase (MR s m)) - UNIT) / UNIT.
Hypothesis K4 : known s (fst c, snd c + UNIT * off - 4) 0.
Hypothesis K2 : known s (fst c, snd c + UNIT * off - 2) (byte_of q 0).
Hypothesis K1 : known s (fst c, snd c + UNIT * off - 1) (byte_of q 1).
Hypothesis HQ : 0 <= q < 2^16.

Let SL := ss_list up e n i.
Let stw := wrs SL s.
Definition ss_final : mstate := havoc up n stw.
Let stf := ss_final.

Let IM := proj1 (proj2 (proj2 INV1)).
Let IG := proj1 (proj2 (proj2 (proj2 (proj2 INV1)))).
Let IS := proj1 (proj2 (proj2 (proj2 (proj2 (proj2 INV1))))).
Let ISH := proj2 (proj2 (proj2 (proj2 (proj2 (proj2 INV1))))).

Lemma Hm : hosts s bm m. Proof. exists ai. exact Hg. Qed.
Lemma res_eq : snd e - snd up - n = res. Proof. unfold e, up, res, aadd. cbn [snd]. lia. Qed.
Lemma res_nonneg : 0 <= res. Proof. pose proof Hfit. unfold res. lia. Qed.

Lemma c16 : snd c mod 16 = 0.
Proof.
  rewrite Ec. cbn [snd]. pose proof (sstart_res _ _ _ _ _ INV1 bm m i Hm) as R.
  pose proof (Z_div_mod_eq_full (sstart (MR s m) i - IB) 16). pose proof (Z_div_mod_eq_full (sstart (MR s m) i) 16).
  pose proof (Z.mod_pos_bound (sstart (MR s m) i) 16 ltac:(lia)). unfold IB in *. lia.
Qed.
Lemma up16 : snd up mod 16 = 0.
Proof. unfold up, aadd. cbn [snd]. unfold UNIT. rewrite Z.add_mod, c16, Z.mul_comm, Z_mod_mult by lia. reflexivity. Qed.

Lemma stw_ctrl : ctrl_eq s stw /\ s_tick stw = s_tick s.
Proof. exact (wrs_ctrl SL s). Qed.
Lemma stf_ctrl : ctrl_eq s stf /\ s_tick stf = s_tick s.
Proof.
  destruct stw_ctrl as [C T]. destruct (havoc_ctrl up n stw) as [C2 T2]. split; [exact (ctrl_eq_trans _ _ _ C C2)| unfold stf, ss_final; rewrite T2; exact T].
Qed.
Lemma stw_TKS : TKS stw (s_tick s).
Proof. apply wrs_TKS; [lia|]. exact (TKS_of _ _ _ _ _ INV1). Qed.
Lemma stw_hav u hl : r_hav (get_shadow stw (fst up)) !! u = Some hl -> hl_ticks hl (s_tick stw).
Proof.
  intros Hu ch Hch. pose proof stw_TKS as TK. rewrite <- (proj2 stw_ctrl) in TK.
  exact (proj1 (sh_ticks_of _ _ TK) u hl ch Hu Hch).
Qed.

Lemma stf_read_out r : ~ (fst r = fst up /\ snd up <= snd r < snd up + n) ->
  cell_read (get_shadow stf (fst r)) (snd r) = cell_read (get_shadow stw (fst r)) (snd r).
Proof.
  intros Hr. unfold stf, ss_final. destruct (Z.eq_dec n 0) as [N0|NZ]; [rewrite havoc_le0 by lia; reflexivity|].
  apply (cell_read_havoc_out up n stw up16 ltac:(lia) stw_hav). exact Hr.
Qed.

Lemma SL_addrs a : In a (map fst SL) -> fst a = fst c /\ (snd a = snd up - 3 \/ snd up + n <= snd a < snd e) .
Proof.
  intros Hin. destruct (ss_list_addrs up e n i a eq_refl ltac:(rewrite res_eq; apply res_nonneg) Hin) as [F R].
  split; [exact F|]. destruct R as [R|[R _]]; [left; exact R| right; exact R].
Qed.

(* [comment removed for export] *)
Lemma stf_known_w x w : ~ (snd up <= x < snd up + n) ->
  lastw SL (fst c, x) None = Some w -> known stf (fst c, x) (Z.land w 255).
Proof.
  intros Hx HL. unfold known, SHd. cbn [fst snd].
  rewrite (stf_read_out (fst c, x)) by (cbn [fst snd]; tauto).
  unfold stw. rewrite (wrs_lastw SL s (fst c, x) (TKS_of _ _ _ _ _ INV1)). rewrite HL. reflexivity.
Qed.
Lemma stf_known_old x v : ~ (snd up <= x < snd up + n) ->
  lastw SL (fst c, x) None = None -> known s (fst c, x) v -> known stf (fst c, x) v.
Proof.
  intros Hx HL K. unfold known, SHd in *. cbn [fst snd] in *.
  rewrite (stf_read_out (fst c, x)) by (cbn [fst snd]; tauto).
  unfold stw. rewrite (wrs_lastw SL s (fst c, x) (TKS_of _ _ _ _ _ INV1)). rewrite HL. exact K.
Qed.
Lemma stf_unknown a : snd up <= a < snd up + n -> unknown stf (fst c, a).
Proof.
  intros Ha. unfold unknown, SHd, stf, ss_final. cbn [fst snd].
  destruct (cell_read_havoc_in up n stw up16 ltac:(lia) stw_hav (fst c, a) eq_refl Ha) as [h Hh]; [| exists h; exact Hh].
  cbn [snd]. intros v tk Hc. unfold stw in Hc.
  rewrite wrs_cells_other in Hc.
  2:{ intros Hin. destruct (SL_addrs _ Hin) as [_ [R|R]]; cbn [snd] in R; lia. }
  rewrite (proj2 (wrs_ctrl SL s)). exact (OLD a v tk Hc Ha).
Qed.

Ltac aeq :=
  match goal with
  | |- context [aptr_eqb ?a ?b] =>
      first [ rewrite (aptr_eqb_neq a b) by (unfold e, up, aadd; cbn [fst snd]; intros E; apply (f_equal snd) in E; cbn [snd] in E; unfold IB, UNIT in *; lia)
            | rewrite (proj2 (aptr_eqb_eq a b)) by (unfold e, up, aadd; cbn [fst snd]; unfold IB, UNIT in *; f_equal; lia) ]
  end.

(* [comment removed for export] *)
Lemma ss_blk_ok : blk_shadow_ok stf ((c, off), n) m i.
Proof.
  destruct stf_ctrl as [CE TK].
  assert (MRE : MR stf m = MR s m) by (apply MR_ext; exact (ce_metas _ _ CE)).
  pose proof Hfit as Hf. pose proof res_nonneg as R0.
  unfold blk_shadow_ok. cbn [bslot boff bsize fst snd]. rewrite MRE. fold stride. fold q.
  replace (snd c + stride - IB - (snd c + UNIT * off) - n) with res by (unfold res; lia).
  assert (NP : forall x, x < snd up \/ snd up + n <= x -> ~ (snd up <= x < snd up + n)) by (intros; lia).
  assert (PP : snd up = snd c + UNIT * off) by reflexivity.
  assert (EE : snd e = snd c + stride - IB) by (unfold e, aadd; cbn [snd]; lia).
  assert (RE : snd e - snd up - n = res) by exact res_eq.
  split; [| split; [| split; [| split; [| split; [exact HQ| split; [| split]]]]]].
  - (* [comment removed for export] *) apply stf_known_old; [apply NP; lia| | exact K4].
    unfold SL, ss_list. rewrite RE. destruct (negb (res =? 0)); destruct (5 <=? res); cbn [lastw app]; repeat aeq; reflexivity.
  - (* [comment removed for export] *)
    replace (i + 32 * Z.min res 5) with (Z.land (i + Z.shiftl (if 5 <=? res then 5 else res) 5) 255).
    2:{ rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 5) with 32.
        pose proof (g_li _ _ _ _ _ _ (ig_ok _ _ _ IG _ _ _ Hg)) as LI.
        destruct (Z.leb_spec 5 res).
        - rewrite Z.min_r by lia. change 255 with (Z.ones 8). rewrite Z.land_ones by lia. rewrite Z.mod_small; lia.
        - rewrite Z.min_l by lia. change 255 with (Z.ones 8). rewrite Z.land_ones by lia. rewrite Z.mod_small; lia. }
    apply stf_known_w; [apply NP; lia|].
    unfold SL, ss_list. rewrite RE. destruct (negb (res =? 0)); destruct (5 <=? res); cbn [lastw app]; repeat aeq; reflexivity.
  - (* [comment removed for export] *) apply stf_known_old; [apply NP; lia| | exact K2].
    unfold SL, ss_list. rewrite RE. destruct (Z.eqb_spec res 0); destruct (Z.leb_spec 5 res); cbn [negb lastw app]; repeat aeq; reflexivity.
  - (* [comment removed for export] *) apply stf_known_old; [apply NP; lia| | exact K1].
    unfold SL, ss_list. rewrite RE. destruct (Z.eqb_spec res 0); destruct (Z.leb_spec 5 res); cbn [negb lastw app]; repeat aeq; reflexivity.
  - (* [comment removed for export] *) intros R5. unfold byte_of. rewrite Z.mul_0_r, Z.shiftr_0_r, Z.mul_1_r.
    assert (RS' : res < 2 ^ 32) by (unfold res; exact RS).
    assert (E5 : (5 <=? res) = true) by (apply Z.leb_le; exact R5).
    assert (EZ : (res =? 0) = false) by (apply Z.eqb_neq; lia).
    split; [| split; [| split; [| split; [| split; [| exact RS']]]]].
    1-4: apply stf_known_w; [apply NP; unfold res in *; unfold IB, UNIT in *; lia|];
         unfold SL, ss_list; rewrite RE, E5, EZ; cbn [negb lastw app]; repeat aeq; try reflexivity.
    all: try (change (8 * 2) with 16; reflexivity). all: try (change (8 * 3) with 24; reflexivity).
    apply (stf_known_w _ 0); [apply NP; unfold res in *; unfold IB, UNIT in *; lia|].
    unfold SL, ss_list; rewrite RE, E5, EZ; cbn [negb lastw app]; repeat aeq; reflexivity.
  - (* [comment removed for export] *) intros RP.
    replace (snd c + stride - IB - res) with (snd up + n) by (unfold res; rewrite PP; lia).
    apply (stf_known_w _ 0); [apply NP; lia|].
    assert (EZ : (res =? 0) = false) by (apply Z.eqb_neq; lia).
    unfold SL, ss_list; rewrite RE, EZ. destruct (Z.leb_spec 5 res); cbn [negb lastw app];
      try (destruct (Z.eq_dec res 5)); try (exfalso; lia); repeat aeq; reflexivity.
  - (* [comment removed for export] *) intros a Ha. apply stf_unknown. rewrite PP. exact Ha.
Qed.

Theorem ss_INVL : INVL x0 stf LA (((c, off), n) :: BL1) LS.
Proof.
  destruct stf_ctrl as [CE TK].
  assert (REG : exists r, s_regions s !! fst c = Some r /\ r_kind r = RKGroup).
  { rewrite Ec. cbn [fst]. exact (ig_region _ _ _ IG _ _ Hg). }
  apply (INVL_add_block X1 s stf LA BL1 LS c off n INV1 eq_refl CE TK).
  - (* [comment removed for export] *)
    intros m' i' Hs' r Hr. rewrite Hs in Hs'. injection Hs' as <- <-.
    assert (NQ : ~ (fst r = fst up /\ snd up <= snd r < snd up + n)).
    { intros [F R]. apply Hr. unfold inT. split; [exact F|]. rewrite sstart_succ. fold stride.
      unfold up, aadd in R. rewrite Ec in R. cbn [snd] in R. pose proof Hfit. unfold IB, UNIT in *. lia. }
    rewrite (stf_read_out r NQ). unfold stw. apply wrs_read_other.
    intros Hin. destruct (SL_addrs r Hin) as [F R]. apply Hr. unfold inT. split; [exact F|].
    rewrite sstart_succ. fold stride. unfold up, e, aadd in R. rewrite Ec in R. cbn [snd] in R.
    pose proof Hfit. unfold IB, UNIT in *. lia.
  - (* [comment removed for export] *)
    change (DOMS s stf). unfold stf, ss_final. destruct (Z.eq_dec n 0) as [N0|NZ].
    + rewrite havoc_le0 by lia. apply wrs_DOMS; [exact (DOMS_of _ _ _ _ _ INV1)|]. intros r Hin. destruct (SL_addrs r Hin) as [F _]. rewrite F. exact REG.
    + apply DOMS_havoc; [lia| | exact REG]. apply wrs_DOMS; [exact (DOMS_of _ _ _ _ _ INV1)|]. intros r Hin. destruct (SL_addrs r Hin) as [F _]. rewrite F. exact REG.
  - (* [comment removed for export] *)
    change (TKS stf (s_tick s)). unfold stf, ss_final. destruct (Z.eq_dec n 0) as [N0|NZ].
    + rewrite havoc_le0 by lia. apply stw_TKS.
    + rewrite <- (proj2 stw_ctrl). apply TKS_havoc; [apply up16| lia| rewrite (proj2 stw_ctrl); apply stw_TKS].
  - intros m' i' Hs'. rewrite Hs in Hs'. injection Hs' as <- <-.
    split; [exact Ho|]. split; [exact Hn|]. split; [exact Hfit|]. exact ss_blk_ok.
Qed.

Lemma ss_ctrl : ctrl_eq s stf /\ s_tick stf = s_tick s.
Proof. exact stf_ctrl. Qed.
End SETSIZE.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section INPLACE.
Variables (st : mstate) (L : mled) (BL : list blk) (LS : lhead -> list aptr).
Variables (c : cptr) (off sz n : Z).
Hypothesis INV : INVL x0 st L BL LS.
Hypothesis Hk : In ((c, off), sz) BL.
Hypothesis Hn : 0 <= n.
Let up : aptr := aadd c (UNIT * off).
(* [comment removed for export] *)
Hypothesis Hfit : forall m i, s_slots st !! c = Some (m, i) -> UNIT * off + n <= get_stride (MR st m) - IB.
(* [comment removed for export] *)
Hypothesis HRS : forall m i, s_slots st !! c = Some (m, i) -> get_stride (MR st m) - IB - UNIT * off - n < 2^32.

Let IM := proj1 (proj2 (proj2 INV)).
Let IG := proj1 (proj2 (proj2 (proj2 (proj2 INV)))).
Let IS := proj1 (proj2 (proj2 (proj2 (proj2 (proj2 INV))))).
Let ISH := proj2 (proj2 (proj2 (proj2 (proj2 (proj2 INV))))).

Let st1 := set_tick (N.succ (s_tick st)) st.
Let X1 := mkX [] [] (Some c) None None.
Let BL1 := bl_remove c BL.

Lemma ip_INV1 : INVL x0 st1 L BL LS.
Proof. apply INVL_set_tick; [cbn; lia| exact INV]. Qed.

Lemma ip_INV_removed : INVL X1 st1 L BL1 LS.
Proof.
  apply (INVL_remove_block x0 st1 st1 L BL LS ((c, off), sz) ip_INV1 Hk eq_refl (ctrl_eq_refl _) eq_refl).
  - intros; reflexivity.
  - exact (DOMS_of _ _ _ _ _ ip_INV1).
  - exact (TKS_of _ _ _ _ _ ip_INV1).
Qed.

Theorem rr_inplace_INVL :
  INVL x0 (rr_inplace_full st c up n) (set_live (map bslot (((c, off), n) :: bl_remove c BL)) L) (((c, off), n) :: bl_remove c BL) LS
  /\ ctrl_eq st (rr_inplace_full st c up n).
Proof.
  destruct (is_blocks _ _ _ IS _ Hk) as (m & i & Hs & Ho & Hsz & Hf). cbn [bslot boff bsize fst snd] in Hs, Ho, Hsz, Hf.
  destruct (is_valid _ _ _ IS _ _ _ Hs) as ((bm & ai & Hg) & Hi & Es).
  rewrite (slot_start'_eq _ _ _ IM _ _ _ (ex_intro _ ai Hg)) in Es.
  pose proof (stride_ge _ _ _ IG _ _ (ex_intro _ ai Hg)) as [S16 SM].
  pose proof (ig_ok _ _ _ IG m bm ai Hg) as GOK.
  specialize (HRS m i Hs). specialize (Hfit m i Hs).
  destruct (ish_blk _ _ ISH ((c, off), sz) m i Hk Hs) as (A1 & A2 & A3 & A4 & A5 & _). cbn [bslot boff bsize fst snd] in A1, A2, A3, A4, A5.
  assert (E : rr_inplace_full st c up n = ss_final st1 c off n m i).
  { unfold rr_inplace_full. rewrite Hs. unfold ss_final. rewrite set_size_i_eq. reflexivity. }
  rewrite E.
  pose proof (ss_ctrl st1 c off n m i) as CT.
  split.
  - apply (INVL_set_live x0 (ss_final st1 c off n m i) L (((c, off), n) :: bl_remove c BL) LS).
    refine (ss_INVL st1 L BL1 LS c off n m bm i ai ip_INV_removed Hs Hg Hi Es Ho Hn Hfit S16 SM _ _ _ _ _ _).
    + change (MR st1 m) with (MR st m). exact HRS.
    + intros o v t Hc Ho'. change (s_tick st1) with (N.succ (s_tick st)).
      change (get_shadow st1 (fst c)) with (get_shadow st (fst c)) in Hc.
      destruct (get_shadow_cells_some st (fst c) o (v, t) Hc) as (sh & Hsh & Hc').
      destruct (TKS_of _ _ _ _ _ INV (fst c) sh Hsh) as (C & _ & _). destruct (C o v t Hc') as [_ Hle]. lia.
    + exact A1.
    + exact A3.
    + exact A4.
    + exact A5.
  - eapply ctrl_eq_trans; [apply ctrl_eq_set_tick| exact (proj1 CT)].
Qed.
End INPLACE.


End CeilWrap.
(* [comment removed for export] *)
Ltac splits := repeat (lazymatch goal with |- _ /\ _ => split | |- _ => fail end).
End MI_WRealloc.

(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool Lia Permutation.
From stdpp Require Import gmap.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require Import STree Malloc MallocCtrl KInv KStep.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require MEX_defs.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MEX_defs.MI_Tree.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require Import MI_Inv MI_Kit.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require MI_Cnt.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MI_Cnt.MI_Arith.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require MI_Ext.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MI_Ext.MI_List.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require MI_Pres1.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MI_Pres1.MI_Geom.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require Import MI_Ext.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require MI_Pres4.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MI_Pres4.MI_Ext2.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require MI_Pres4.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MI_Pres4.MI_Shadow.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require Import MI_Pres1.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require MI_Pres4.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MI_Pres4.MI_Pres2.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require Import MI_WFree2.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require MI_WEnframe2.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MI_WEnframe2.MI_WGroup.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require MI_WEnframe2.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MI_WEnframe2.MI_TF2.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require MI_Contracts.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MI_Contracts.MI_WMalloc.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require MI_WEnframe2.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MI_WEnframe2.MI_WEnframe.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require Import MI_WEnframe2.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require MI_WSlot2.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MI_WSlot2.MI_Ledger.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require Import MI_Contracts.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require Realloc.
Import MI_WRealloc.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Local Open Scope Z_scope.
Import Realloc.

(* [comment removed for export] *)
Section CeilWrap.
Context {ACEIL : Ceil}.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Ltac splits := repeat (lazymatch goal with |- _ /\ _ => split | |- _ => fail end).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition pruneF (len : Z) (sh : shadow) : shadow :=
  mkShadow (filter (fun kv => fst kv <? len) (r_cells sh))
           (filter (fun kv => 16 * fst kv <? len) (r_hav sh))
           (filter (fun kv => 4096 * fst kv <? len) (r_havp sh)).

Lemma prune_shadow_eq rid len st : prune_shadow rid len st = upd_shadow rid (pruneF len) st.
Proof. reflexivity. Qed.

Lemma pruneF_cells len sh o : r_cells (pruneF len sh) !! o = if o <? len then r_cells sh !! o else None.
Proof.
  cbn [pruneF r_cells]. destruct (Z.ltb_spec o len).
  - destruct (r_cells sh !! o) as [x|] eqn:E.
    + apply map_lookup_filter_Some_2; [exact E|]. cbn. apply Is_true_eq_left. apply Z.ltb_lt. assumption.
    + apply map_lookup_filter_None_2. left. exact E.
  - apply map_lookup_filter_None_2. right. intros x _ Hp. cbn in Hp. apply Is_true_eq_true in Hp. apply Z.ltb_lt in Hp. lia.
Qed.
Lemma pruneF_hav len sh u : r_hav (pruneF len sh) !! u = if 16 * u <? len then r_hav sh !! u else None.
Proof.
  cbn [pruneF r_hav]. destruct (Z.ltb_spec (16 * u) len).
  - destruct (r_hav sh !! u) as [x|] eqn:E.
    + apply map_lookup_filter_Some_2; [exact E|]. cbn. apply Is_true_eq_left. apply Z.ltb_lt. assumption.
    + apply map_lookup_filter_None_2. left. exact E.
  - apply map_lookup_filter_None_2. right. intros x _ Hp. cbn in Hp. apply Is_true_eq_true in Hp. apply Z.ltb_lt in Hp. lia.
Qed.
Lemma pruneF_havp len sh pg : r_havp (pruneF len sh) !! pg = if 4096 * pg <? len then r_havp sh !! pg else None.
Proof.
  cbn [pruneF r_havp]. destruct (Z.ltb_spec (4096 * pg) len).
  - destruct (r_havp sh !! pg) as [x|] eqn:E.
    + apply map_lookup_filter_Some_2; [exact E|]. cbn. apply Is_true_eq_left. apply Z.ltb_lt. assumption.
    + apply map_lookup_filter_None_2. left. exact E.
  - apply map_lookup_filter_None_2. right. intros x _ Hp. cbn in Hp. apply Is_true_eq_true in Hp. apply Z.ltb_lt in Hp. lia.
Qed.

(* [comment removed for export] *)
Lemma pruneF_read len sh o : 0 <= o < len -> cell_read (pruneF len sh) o = cell_read sh o.
Proof.
  intros Ho. unfold cell_read. rewrite pruneF_cells, pruneF_hav, pruneF_havp.
  pose proof (Z_div_mod_eq_full o 16). pose proof (Z.mod_pos_bound o 16 ltac:(lia)).
  pose proof (Z_div_mod_eq_full o 4096). pose proof (Z.mod_pos_bound o 4096 ltac:(lia)).
  replace (o <? len) with true by (symmetry; apply Z.ltb_lt; lia).
  replace (16 * (o / 16) <? len) with true by (symmetry; apply Z.ltb_lt; lia).
  replace (4096 * (o / 4096) <? len) with true by (symmetry; apply Z.ltb_lt; lia).
  reflexivity.
Qed.

Lemma pruneF_sh_ticks len sh t : sh_ticks sh t -> sh_ticks (pruneF len sh) t.
Proof.
  intros [T1 T2]. split.
  - intros u hl ch Hu Hin. rewrite pruneF_hav in Hu. destruct (16 * u <? len); [| discriminate]. exact (T1 u hl ch Hu Hin).
  - intros pg t' Hp. rewrite pruneF_havp in Hp. destruct (4096 * pg <? len); [| discriminate]. exact (T2 pg t' Hp).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section ALONE.
Variables (X : extras) (st : mstate) (L : mled) (BL : list blk) (LS : lhead -> list aptr).
Hypothesis INV : INVL X st L BL LS.
Variables (g b : aptr).
Hypothesis Hg : hosts st b g.
Hypothesis Hsc : 48 <= m_sizeclass (MR st g).
Let IM := proj1 (proj2 (proj2 INV)).
Let IG := proj1 (proj2 (proj2 (proj2 (proj2 INV)))).
Let IS := proj1 (proj2 (proj2 (proj2 (proj2 (proj2 INV))))).

Lemma g63 : m_sizeclass (MR st g) = 63 /\ m_last_idx (MR st g) = 0 /\ m_maplen (MR st g) <> 0 /\ ~ in_list LS g.
Proof.
  destruct (hosts_ok _ _ _ IG _ _ Hg) as (ai & Hb & GO).
  destruct (g_sc _ _ _ _ _ _ GO) as [[Hlt _]|H]; [lia| exact H].
Qed.

Lemma alone b' m' : hosts st b' m' -> fst b' = fst b -> m' = g /\ b' = b.
Proof.
  intros Hm' Ef. destruct g63 as (E63 & L0 & ML & _).
  assert (Em : m' = g).
  { destruct (Z.eq_dec (m_maplen (MR st m')) 0) as [Z0|NZ].
    - destruct (top_chain _ _ _ _ IM IG IS m' b' Hm' Z0) as (t & i & c & bt & Ha & Ht & Htop & Hft).
      pose proof (top_unique _ _ _ IG t g bt b Ht Hg Htop ML ltac:(congruence)) as ->.
      destruct (anc_facts _ _ _ _ IM IG IS _ _ _ _ Ha) as (? & ? & _ & _ & _ & _ & _ & _ & _ & _ & Hsc'). lia.
    - exact (top_unique _ _ _ IG m' g b' b Hm' Hg NZ ML Ef). }
  subst m'. split; [reflexivity|]. exact (hosts_inj _ _ _ IM _ _ _ Hm' Hg).
Qed.

(* [comment removed for export] *)
Lemma alone_slot q m' i' : s_slots st !! q = Some (m', i') -> fst q = fst b -> m' = g /\ i' = 0 /\ q = slot_start' (MR st g) 0.
Proof.
  intros Hq Ef. destruct g63 as (E63 & L0 & ML & _).
  destruct (is_valid _ _ _ IS _ _ _ Hq) as ([b' Hb'] & Hi & Eq).
  rewrite (slot_start'_eq _ _ _ IM _ _ _ Hb') in Eq.
  assert (Ef' : fst b' = fst b) by (rewrite Eq in Ef; exact Ef).
  destruct (alone b' m' Hb' Ef') as [-> ->].
  assert (i' = 0) by lia. subst i'. rewrite (slot_start'_eq _ _ _ IM _ _ _ Hg). auto.
Qed.
End ALONE.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma land_ones52 v : 0 <= v < 2^52 -> Z.land v (2^52 - 1) = v.
Proof. intros Hv. change (2^52 - 1) with (Z.ones 52). rewrite Z.land_ones by lia. apply Z.mod_small. lia. Qed.

Lemma regions_overwrite_perm (st : mstate) rid r r' (F : N * region -> bool) :
  s_regions st !! rid = Some r ->
  Permutation (List.filter F (map_to_list (<[rid := r']> (s_regions st)))) (List.filter F ((rid, r') :: map_to_list (delete rid (s_regions st)))).
Proof.
  intros H. apply perm_filter. rewrite <- (insert_delete_id (s_regions st) rid r H) at 1. rewrite insert_insert_eq.
  apply map_to_list_insert. apply lookup_delete_eq.
Qed.

Section PHASEA.
Variables (s : mstate) (L : mled) (BL1 : list blk) (LS : lhead -> list aptr).
Variables (c : cptr) (g : aptr) (ai : Z) (r : region) (d nn : Z).
Let X1 := mkX [] [] (Some c) None None.
Let rid := fst c.
Let b : aptr := (rid, 0).
Hypothesis INV1 : INVL X1 s L BL1 LS.
Hypothesis TF : TF0 s.
Hypothesis Hgb : s_groups s !! b = Some (mkGhdr (Some g) ai).
Hypothesis Hs : s_slots s !! c = Some (g, 0).
Hypothesis Hsc : 48 <= m_sizeclass (MR s g).
Hypothesis Hr : s_regions s !! rid = Some r.
Hypothesis Hd : 0 < d.
Hypothesis Hda : d mod PGSZ = 0.
Hypothesis Hnn : PGSZ <= nn.
Hypothesis Hnn2 : 2 * PGSZ <= nn.
Hypothesis Hnna : nn mod PGSZ = 0.
Hypothesis HnnM : nn < LEN_MAX.
Hypothesis Hce : d + nn <= alloc_ceiling.
Hypothesis Hfree : forall q rq, s_regions s !! q = Some rq -> q <> rid ->
  d + nn <= fst (region_live_range rq) \/ fst (region_live_range rq) + snd (region_live_range rq) <= d.

Let IR := proj1 INV1.
Let IA := proj1 (proj2 INV1).
Let IM := proj1 (proj2 (proj2 INV1)).
Let IL := proj1 (proj2 (proj2 (proj2 INV1))).
Let IG := proj1 (proj2 (proj2 (proj2 (proj2 INV1)))).
Let IS := proj1 (proj2 (proj2 (proj2 (proj2 (proj2 INV1))))).
Let ISH := proj2 (proj2 (proj2 (proj2 (proj2 (proj2 INV1))))).

Definition pa_r' : region := mkRegion (r_kind r) d nn.
Definition pa_len : Z := Z.min (m_maplen (MR s g) * 4096) nn.
Definition pa_R' : meta := m_set_maplen (nn / 4096) (MR s g).
Definition pa_s2 : mstate := upd_region rid (fun r0 => mkRegion (r_kind r0) d nn) s.
Definition pa_s3 : mstate := prune_shadow rid pa_len pa_s2.
Definition pa_s4 : mstate := upd_meta g (m_set_maplen (nn / 4096)) pa_s3.
Definition pa_s5 : mstate := wr8 (aadd b (nn - IB)) 0 pa_s4.
Definition pa_L : mled := set_groups ((d, nn) :: g_remove (r_base r) (ld_groups L)) L.
Let sh3 : shadow := pruneF pa_len (get_shadow s rid).
Let sh5 : shadow := mkShadow (<[nn - IB := (Z.land 0 255, s_tick s)]> (r_cells sh3)) (r_hav sh3) (r_havp sh3).

(* [comment removed for export] *)
Lemma pa_Hg : hosts s b g. Proof. exists ai. exact Hgb. Qed.
Lemma pa_g63 : m_sizeclass (MR s g) = 63 /\ m_last_idx (MR s g) = 0 /\ m_maplen (MR s g) <> 0 /\ ~ in_list LS g.
Proof. exact (g63 X1 s L BL1 LS INV1 g b pa_Hg Hsc). Qed.
Lemma pa_Kr : r_kind r = RKGroup.
Proof. destruct (ig_region _ _ _ IG _ _ Hgb) as (r0 & Hr0 & K). cbn [fst b] in Hr0. unfold b in Hr0. cbn [fst] in Hr0. rewrite Hr in Hr0. injection Hr0 as ->. exact K. Qed.
Lemma pa_GOK : group_ok X1 s LS g b ai. Proof. exact (ig_ok _ _ _ IG _ _ _ Hgb). Qed.
Lemma pa_top : m_maplen (MR s g) * 4096 = round_up_pg (r_len r) /\ gend (MR s g) <= m_maplen (MR s g) * 4096.
Proof.
  destruct pa_g63 as (_ & _ & ML & _). destruct (g_top _ _ _ _ _ _ pa_GOK ML) as (_ & r0 & Hr0 & _ & E1 & E2).
  unfold b in Hr0. cbn [fst] in Hr0. fold rid in Hr0. rewrite Hr in Hr0. injection Hr0 as ->. auto.
Qed.
Lemma pa_mem : m_mem (MR s g) = Some b.
Proof. exact (hosts_mem _ _ _ IM _ _ pa_Hg). Qed.
Lemma pa_gbase : gbase (MR s g) = b.
Proof. exact (hosts_gbase _ _ _ IM _ _ pa_Hg). Qed.
Lemma pa_c : c = (rid, UNIT).
Proof.
  destruct (is_valid _ _ _ IS _ _ _ Hs) as (_ & _ & E). rewrite (slot_start'_eq _ _ _ IM _ _ _ pa_Hg) in E.
  rewrite (sstart0 _ _ _ IM _ _ pa_Hg) in E. exact E.
Qed.
Lemma pa_maplen_pos : 0 < m_maplen (MR s g).
Proof. destruct pa_g63 as (_ & _ & ML & _). pose proof (g_maplen _ _ _ _ _ _ pa_GOK). lia. Qed.
Lemma pa_len_ge : PGSZ <= pa_len.
Proof. unfold pa_len. pose proof pa_maplen_pos. unfold PGSZ in *. lia. Qed.
Lemma pa_stride : get_stride (MR s g) = m_maplen (MR s g) * 4096 - UNIT.
Proof.
  destruct pa_g63 as (_ & L0 & ML & _). unfold get_stride. rewrite L0, Z.eqb_refl.
  destruct (Z.eqb_spec (m_maplen (MR s g)) 0); [contradiction| reflexivity].
Qed.

(* [comment removed for export] *)
Lemma pa_R'_maplen : m_maplen pa_R' = nn / 4096.
Proof.
  unfold pa_R', m_set_maplen. cbn. apply land_ones52. unfold LEN_MAX in HnnM. unfold PGSZ in *.
  split; [apply Z.div_pos; lia|]. apply Z.div_lt_upper_bound; lia.
Qed.
Lemma pa_R'_fields : m_prev pa_R' = m_prev (MR s g) /\ m_next pa_R' = m_next (MR s g) /\ m_mem pa_R' = m_mem (MR s g)
  /\ m_avail pa_R' = m_avail (MR s g) /\ m_freed pa_R' = m_freed (MR s g) /\ m_last_idx pa_R' = m_last_idx (MR s g)
  /\ m_freeable pa_R' = m_freeable (MR s g) /\ m_sizeclass pa_R' = m_sizeclass (MR s g).
Proof. unfold pa_R', m_set_maplen. cbn. repeat split; reflexivity. Qed.
Lemma pa_nn_div : nn / 4096 * 4096 = nn /\ 0 < nn / 4096.
Proof. unfold PGSZ in *. pose proof (Z_div_mod_eq_full nn 4096). split; [lia|]. apply Z.div_str_pos. lia. Qed.
Lemma pa_R'_stride : get_stride pa_R' = nn - UNIT.
Proof.
  destruct pa_g63 as (_ & L0 & _ & _). destruct pa_nn_div as [E P].
  unfold get_stride. rewrite (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 pa_R'_fields)))))), L0, Z.eqb_refl, pa_R'_maplen.
  destruct (Z.eqb_spec (nn / 4096) 0); [lia|]. cbn [andb negb]. lia.
Qed.
Lemma pa_R'_gbase : gbase pa_R' = b.
Proof. unfold gbase. rewrite (proj1 (proj2 (proj2 pa_R'_fields))). fold (gbase (MR s g)). exact pa_gbase. Qed.
Lemma pa_R'_sstart i : sstart pa_R' i = UNIT + (nn - UNIT) * i.
Proof. unfold sstart. rewrite pa_R'_gbase, pa_R'_stride. cbn [snd b]. unfold b. cbn [snd]. lia. Qed.
Lemma pa_R'_cnt : cnt_of pa_R' = 1.
Proof. unfold cnt_of. rewrite (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 pa_R'_fields)))))). destruct pa_g63 as (_ & -> & _). reflexivity. Qed.

(* [comment removed for export] *)
Lemma pa_s2_eq : pa_s2 = set_regions (<[rid := pa_r']> (s_regions s)) s.
Proof. unfold pa_s2, upd_region, get_region. rewrite Hr. reflexivity. Qed.

Lemma pa_regions : s_regions pa_s5 = <[rid := pa_r']> (s_regions s).
Proof. unfold pa_s5, pa_s4, pa_s3. rewrite prune_shadow_eq. cbn -[pa_s2 insert]. rewrite pa_s2_eq. reflexivity. Qed.
Lemma pa_lookup q : s_regions pa_s5 !! q = if (q =? rid)%N then Some pa_r' else s_regions s !! q.
Proof.
  rewrite pa_regions. destruct (N.eqb_spec q rid) as [->|NE]; [apply lookup_insert_eq| rewrite lookup_insert_ne by congruence; reflexivity].
Qed.
Lemma pa_keep q rq : s_regions s !! q = Some rq -> q <> rid -> s_regions pa_s5 !! q = Some rq.
Proof. intros H NE. rewrite pa_lookup. destruct (N.eqb_spec q rid); [congruence| exact H]. Qed.
Lemma pa_some q rq : s_regions pa_s5 !! q = Some rq -> (q = rid /\ rq = pa_r') \/ (q <> rid /\ s_regions s !! q = Some rq).
Proof. rewrite pa_lookup. destruct (N.eqb_spec q rid) as [->|NE]; [intros H; injection H as <-; auto| auto]. Qed.

Lemma pa_metas : s_metas pa_s5 = <[g := pa_R']> (s_metas s).
Proof.
  assert (E3 : s_metas pa_s3 = s_metas s).
  { unfold pa_s3, pa_s2. rewrite prune_shadow_eq, s_metas_upd_shadow, s_metas_upd_region. reflexivity. }
  unfold pa_s5, pa_s4. cbn -[pa_s3 insert upd_meta pa_R']. rewrite s_metas_upd_meta. rewrite E3. f_equal.
  unfold pa_R'. f_equal. unfold MR. apply get_meta_rec_ext. exact E3.
Qed.
Lemma pa_MR x : MR pa_s5 x = if aptr_eqb x g then pa_R' else MR s x.
Proof.
  unfold MR, get_meta_rec. rewrite pa_metas. destruct (aptr_eqb_spec x g) as [->|NE]; [rewrite lookup_insert_eq; reflexivity| rewrite lookup_insert_ne by congruence; reflexivity].
Qed.
Lemma pa_MRg : MR pa_s5 g = pa_R'. Proof. rewrite pa_MR, aptr_eqb_refl. reflexivity. Qed.
Lemma pa_MRo x : x <> g -> MR pa_s5 x = MR s x. Proof. intros NE. rewrite pa_MR, (aptr_eqb_neq _ _ NE). reflexivity. Qed.

Lemma pa_ctx : s_ctx pa_s5 = s_ctx s.
Proof. unfold pa_s5, pa_s4, pa_s3, pa_s2. rewrite prune_shadow_eq. cbn -[upd_region]. rewrite s_ctx_upd_region. reflexivity. Qed.
Lemma pa_groups : s_groups pa_s5 = s_groups s.
Proof. unfold pa_s5, pa_s4, pa_s3, pa_s2. rewrite prune_shadow_eq. cbn -[upd_region]. rewrite s_groups_upd_region. reflexivity. Qed.
Lemma pa_slots : s_slots pa_s5 = s_slots s.
Proof. unfold pa_s5, pa_s4, pa_s3, pa_s2. rewrite prune_shadow_eq. cbn -[upd_region]. rewrite s_slots_upd_region. reflexivity. Qed.
Lemma pa_areas : s_areas pa_s5 = s_areas s.
Proof. unfold pa_s5, pa_s4, pa_s3, pa_s2. rewrite prune_shadow_eq. cbn -[upd_region]. rewrite s_areas_upd_region. reflexivity. Qed.
Lemma pa_next_rid : s_next_rid pa_s5 = s_next_rid s.
Proof. unfold pa_s5, pa_s4, pa_s3, pa_s2. rewrite prune_shadow_eq. cbn -[upd_region]. rewrite s_next_rid_upd_region. reflexivity. Qed.
Lemma pa_secret : s_secret pa_s5 = s_secret s.
Proof. unfold pa_s5, pa_s4, pa_s3, pa_s2. rewrite prune_shadow_eq. cbn -[upd_region]. rewrite s_secret_upd_region. reflexivity. Qed.
Lemma pa_reserved : s_reserved pa_s5 = s_reserved s.
Proof. unfold pa_s5, pa_s4, pa_s3, pa_s2. rewrite prune_shadow_eq. cbn -[upd_region]. rewrite s_reserved_upd_region. reflexivity. Qed.
Lemma pa_tick : s_tick pa_s5 = s_tick s.
Proof. unfold pa_s5, pa_s4, pa_s3, pa_s2. rewrite prune_shadow_eq. cbn -[upd_region]. rewrite s_tick_upd_region. reflexivity. Qed.

Lemma pa_shadow : s_shadow pa_s5 = <[rid := sh5]> (s_shadow s).
Proof.
  unfold pa_s5.
  unfold wr8, upd_shadow. cbn -[pa_s4 insert get_shadow Z.land Z.sub].
  assert (E4 : s_shadow pa_s4 = <[rid := sh3]> (s_shadow s)).
  { unfold pa_s4. rewrite s_shadow_upd_meta. unfold pa_s3. rewrite prune_shadow_eq. unfold upd_shadow. cbn -[pa_s2 insert get_shadow pruneF pa_len].
    unfold pa_s2. rewrite s_shadow_upd_region. f_equal. unfold sh3. f_equal. apply get_shadow_ext. apply s_shadow_upd_region. }
  assert (T4 : s_tick pa_s4 = s_tick s).
  { unfold pa_s4, pa_s3, pa_s2. rewrite prune_shadow_eq. cbn -[upd_region]. rewrite s_tick_upd_region. reflexivity. }
  assert (G4 : get_shadow pa_s4 rid = sh3).
  { unfold get_shadow. rewrite E4, lookup_insert_eq. reflexivity. }
  unfold b, aadd. cbn [fst snd]. fold rid. rewrite E4, T4, G4, insert_insert_eq. unfold sh5. f_equal.
Qed.
Lemma pa_get_shadow q : get_shadow pa_s5 q = if (q =? rid)%N then sh5 else get_shadow s q.
Proof.
  unfold get_shadow at 1. rewrite pa_shadow. destruct (N.eqb_spec q rid) as [->|NE]; [rewrite lookup_insert_eq; reflexivity|].
  rewrite lookup_insert_ne by congruence. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma pa_read_other q o : q <> rid -> cell_read (get_shadow pa_s5 q) o = cell_read (get_shadow s q) o.
Proof. intros NE. rewrite pa_get_shadow. destruct (N.eqb_spec q rid); [contradiction| reflexivity]. Qed.

Lemma pa_sh3_ticks : sh_ticks sh3 (s_tick s).
Proof. unfold sh3. apply pruneF_sh_ticks. apply sh_ticks_of. exact (TKS_of _ _ _ _ _ INV1). Qed.

Lemma pa_read_end : cell_read (get_shadow pa_s5 rid) (nn - IB) = Known 0.
Proof.
  rewrite pa_get_shadow, N.eqb_refl. unfold cell_read. cbn [sh5 r_cells r_hav r_havp]. rewrite lookup_insert_eq.
  rewrite (not_stale_cur _ _ _ pa_sh3_ticks). reflexivity.
Qed.

Lemma pa_read_low o : 0 <= o < pa_len -> o <> nn - IB -> cell_read (get_shadow pa_s5 rid) o = cell_read (get_shadow s rid) o.
Proof.
  intros Ho NE. rewrite pa_get_shadow, N.eqb_refl.
  transitivity (cell_read sh3 o); [| unfold sh3; apply pruneF_read; exact Ho].
  unfold cell_read. cbn [sh5 r_cells r_hav r_havp]. rewrite lookup_insert_ne by congruence. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma pa_read_high o : pa_len <= o -> o <> nn - IB -> cell_read (get_shadow pa_s5 rid) o = Known 0.
Proof.
  intros Ho NE. pose proof pa_len_ge as PL. destruct pa_nn_div as [ND NP]. pose proof pa_maplen_pos as MP.
  assert (PL16 : pa_len mod 16 = 0 /\ pa_len mod 4096 = 0).
  { unfold pa_len. destruct (Z.le_gt_cases (m_maplen (MR s g) * 4096) nn).
    - rewrite Z.min_l by lia. split; [replace (m_maplen (MR s g) * 4096) with (m_maplen (MR s g) * 256 * 16) by lia|]; apply Z_mod_mult.
    - rewrite Z.min_r by lia. split; [| unfold PGSZ in Hnna; exact Hnna].
      replace nn with (nn / 4096 * 256 * 16) by lia. apply Z_mod_mult. }
  destruct PL16 as [M16 M4096].
  rewrite pa_get_shadow, N.eqb_refl. unfold cell_read. cbn [sh5 r_cells r_hav r_havp]. rewrite lookup_insert_ne by congruence.
  unfold sh3. rewrite pruneF_cells, pruneF_hav, pruneF_havp.
  replace (o <? pa_len) with false by (symmetry; apply Z.ltb_ge; lia).
  replace (16 * (o / 16) <? pa_len) with false by (symmetry; apply Z.ltb_ge; Z.div_mod_to_equations; lia).
  replace (4096 * (o / 4096) <? pa_len) with false by (symmetry; apply Z.ltb_ge; Z.div_mod_to_equations; lia).
  reflexivity.
Qed.

Lemma pa_known_low o v : 0 <= o < pa_len -> o <> nn - IB -> known s (rid, o) v -> known pa_s5 (rid, o) v.
Proof. intros Ho NE K. unfold known, SHd in *. cbn [fst snd] in *. rewrite pa_read_low; assumption. Qed.
Lemma pa_unknown_low o : 0 <= o < pa_len -> o <> nn - IB -> unknown s (rid, o) -> unknown pa_s5 (rid, o).
Proof. intros Ho NE K. unfold unknown, SHd in *. cbn [fst snd] in *. rewrite pa_read_low; assumption. Qed.
Lemma pa_known_other q o v : q <> rid -> known s (q, o) v -> known pa_s5 (q, o) v.
Proof. intros NE K. unfold known, SHd in *. cbn [fst snd] in *. rewrite pa_read_other; assumption. Qed.
Lemma pa_unknown_other q o : q <> rid -> unknown s (q, o) -> unknown pa_s5 (q, o).
Proof. intros NE K. unfold unknown, SHd in *. cbn [fst snd] in *. rewrite pa_read_other; assumption. Qed.

(* [comment removed for export] *)
Lemma pa_cells_old o v t : r_cells (get_shadow pa_s5 rid) !! o = Some (v, t) -> o <> nn - IB -> (t < s_tick s)%N.
Proof.
  rewrite pa_get_shadow, N.eqb_refl. cbn [sh5 r_cells]. intros Hc NE. rewrite lookup_insert_ne in Hc by congruence.
  unfold sh3 in Hc. rewrite pruneF_cells in Hc. destruct (o <? pa_len); [| discriminate].
  destruct (get_shadow_cells_some s rid o (v, t) Hc) as (sh & Hsh & Hc'). exact (TF _ _ _ _ _ Hsh Hc').
Qed.

(* [comment removed for export] *)
Lemma pa_frontier q rq : frontier pa_s5 q rq = frontier s q rq.
Proof. apply frontier_ext. rewrite pa_ctx. reflexivity. Qed.

Lemma pa_r'_live : region_live_range pa_r' = (d, nn).
Proof. unfold region_live_range, pa_r'. cbn. rewrite pa_Kr. f_equal. apply round_up_pg_aligned. unfold PGSZ in Hnna. exact Hnna. Qed.

Lemma pa_other_groups_base q rq : s_regions s !! q = Some rq -> q <> rid -> r_kind rq = RKGroup -> r_base rq <> r_base r.
Proof using Hd Hda Hgb Hnn2 Hnna Hr IG IR.
  intros Hq NE K E. pose proof (ir_disj _ _ _ IR q rid rq r Hq Hr NE) as D. unfold region_live_range in D. rewrite K, pa_Kr in D.
  pose proof (ir_shape _ _ _ IR _ _ Hq) as (S1 & _ & S3 & _). pose proof (ir_shape _ _ _ IR _ _ Hr) as (T1 & _ & T3 & _).
  pose proof (round_up_ge (r_len rq)). pose proof (round_up_ge (r_len r)). clear - D E S3 T3 H H0. lia.  (* [comment removed for export] *)
Qed.

Lemma pa_inv_R : inv_R X1 pa_s5 pa_L.
Proof.
  pose proof pa_Kr as Kr. destruct pa_nn_div as [ND NP].
  destruct IR; constructor; rewrite ?pa_next_rid, ?pa_reserved, ?pa_ctx.
  - intros q rq Hq. apply pa_some in Hq as [[-> _]|[_ Hq]]; [exact (ir_ids _ _ Hr)| exact (ir_ids q rq Hq)].
  - intros q rq Hq. apply pa_some in Hq as [[-> ->]|[_ Hq]]; [| exact (ir_shape q rq Hq)]. unfold pa_r'. cbn. rewrite Kr.
    rewrite round_up_pg_aligned by (unfold PGSZ in Hnna; exact Hnna). unfold PGSZ in *.
    split; [lia|]. split; [exact Hda|]. split; [lia|]. split; [exact HnnM|]. split; [lia|]. intros [K|K]; discriminate.
  - intros q1 q2 r1 r2 H1 H2 NE.
    apply pa_some in H1 as [[-> ->]|[N1 H1]]; apply pa_some in H2 as [[-> ->]|[N2 H2]]; [congruence| | | exact (ir_disj q1 q2 r1 r2 H1 H2 NE)].
    + rewrite pa_r'_live. pose proof (Hfree q2 r2 H2 N2) as D. destruct (region_live_range r2) as [b2 l2]. cbn in D |- *. lia.
    + rewrite pa_r'_live. pose proof (Hfree q1 r1 H1 N1) as D. destruct (region_live_range r1) as [b1 l1]. cbn in D |- *. lia.
  - exact ir_resv.
  - (* [comment removed for export] *)
    unfold pa_L. cbn [ld_groups set_groups]. rewrite pa_regions.
    eapply Permutation_trans; [| apply Permutation_map; apply Permutation_sym; apply (regions_overwrite_perm s rid r pa_r' _ Hr)].
    cbn [List.filter map]. unfold pa_r' at 1 2. cbn [r_kind r_base r_len snd]. rewrite Kr. cbn [map]. apply perm_skip.
    apply g_remove_perm with (l := r_len r).
    + eapply Permutation_trans; [exact ir_groups|].
      eapply Permutation_trans; [apply Permutation_map; apply (regions_delete_perm s rid r _ Hr)|].
      cbn. rewrite Kr. cbn. apply Permutation_refl.
    + intros y Hy. apply in_map_iff in Hy as ([q rq] & <- & Hq). apply filter_In in Hq as [Hq Hkq]. cbn in Hkq |- *.
      apply list_elem_of_In in Hq. apply elem_of_map_to_list in Hq. apply lookup_delete_Some in Hq as [NE Hq].
      destruct (r_kind rq) eqn:Ek; try discriminate. exact (pa_other_groups_base q rq Hq ltac:(congruence) Ek).
  - (* [comment removed for export] *)
    unfold pa_L. cbn [ld_metas set_groups]. rewrite pa_regions.
    assert (EF : forall kr : N * region, (r_base (snd kr), r_len (snd kr), frontier pa_s5 (fst kr) (snd kr) / PGSZ - 1)
                                       = (r_base (snd kr), r_len (snd kr), frontier s (fst kr) (snd kr) / PGSZ - 1)).
    { intros [q rq]. cbn [fst snd]. rewrite pa_frontier. reflexivity. }
    rewrite (map_ext _ _ EF).
    eapply Permutation_trans; [exact ir_metas|].
    eapply Permutation_trans; [apply Permutation_map; apply (regions_delete_perm s rid r _ Hr)|].
    eapply Permutation_trans; [| apply Permutation_map; apply Permutation_sym; apply (regions_overwrite_perm s rid r pa_r' _ Hr)].
    cbn [List.filter map snd fst r_kind pa_r']. rewrite Kr. apply Permutation_refl.
  - intros q rq Hq K. rewrite pa_frontier. apply pa_some in Hq as [[-> ->]|[_ Hq]]; [cbn in K; rewrite Kr in K; discriminate| exact (ir_metalen q rq Hq K)].
  - intros q rq Hq K. rewrite pa_frontier. apply pa_some in Hq as [[-> ->]|[_ Hq]]; [cbn in K; rewrite Kr in K; discriminate| exact (ir_brkfront q rq Hq K)].
  - destruct ir_shift as [S1 [S2|(q & rq & Hq & K & E)]]; split; [exact S1| left; exact S2| exact S1|].
    right. exists q, rq. split; [apply pa_keep; [exact Hq| intros ->; rewrite Hr in Hq; injection Hq as ->; rewrite Kr in K; discriminate]| auto].
  - intros b0 l0. unfold pa_L. cbn [ld_brkreg set_groups]. rewrite ir_brkreg. split; intros (q & rq & Hq & K & E1 & E2); exists q, rq.
    + split; [apply pa_keep; [exact Hq| intros ->; rewrite Hr in Hq; injection Hq as ->; rewrite Kr in K; discriminate]| auto].
    + apply pa_some in Hq as [[-> ->]|[_ Hq]]; [cbn in K; rewrite Kr in K; discriminate| auto].
  - intros q1 q2 r1 r2 H1 H2 K1 K2.
    apply pa_some in H1 as [[-> ->]|[_ H1]]; [cbn in K1; rewrite Kr in K1; discriminate|].
    apply pa_some in H2 as [[-> ->]|[_ H2]]; [cbn in K2; rewrite Kr in K2; discriminate|].
    exact (ir_brk1 q1 q2 r1 r2 H1 H2 K1 K2).
  - unfold pa_L. cbn [ld_brk set_groups]. revert ir_brk. destruct (c_brk (s_ctx s)) as [| |brid boff]; intros IBK.
    + destruct IBK as [B NB]. split; [exact B|]. intros q rq Hq. apply pa_some in Hq as [[-> ->]|[_ Hq]]; [cbn; rewrite Kr; discriminate| exact (NB q rq Hq)].
    + exact IBK.
    + destruct IBK as [B (rq & Hq & K & E)]. split; [exact B|]. exists rq.
      split; [apply pa_keep; [exact Hq| intros ->; rewrite Hr in Hq; injection Hq as ->; rewrite Kr in K; discriminate]| auto].
  - destruct ir_cursor as (C1 & C2 & C3). split; [exact C1|]. split; [exact C2|].
    intros q off E. destruct (C3 q off E) as (rq & Hq & K & B). exists rq.
    split; [apply pa_keep; [exact Hq| intros ->; rewrite Hr in Hq; injection Hq as ->; destruct K as [K|K]; rewrite Kr in K; discriminate]| auto].
  - intros q Hq. cbn in Hq. discriminate.
Qed.

Lemma pa_gcnt sc : gcnt pa_s5 sc = gcnt s sc.
Proof.
  unfold gcnt. rewrite pa_groups. f_equal. apply map_ext. intros [b0 h]. cbn. destruct (g_meta h) as [m|]; [| reflexivity].
  rewrite pa_MR. destruct (aptr_eqb_spec m g) as [->|NE]; [| reflexivity].
  unfold cnt_of. rewrite (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 pa_R'_fields)))))), (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 pa_R'_fields))))))). reflexivity.
Qed.

Lemma pa_inv_A : inv_A pa_s5.
Proof.
  pose proof pa_Kr as Kr.
  pose proof (usage_ext s pa_s5 ltac:(rewrite pa_ctx; reflexivity)) as US.
  destruct IA; constructor; rewrite ?pa_ctx, ?pa_areas, ?pa_secret, ?pa_metas; try assumption.
  - intros a ar Ha. destruct (ia_areas a ar Ha) as ((rq & Hq & K & M & P & F) & rest). split; [| exact rest].
    exists rq. rewrite pa_frontier. split; [| auto]. apply pa_keep; [exact Hq|].
    intros E. rewrite E, Hr in Hq. injection Hq as ->. destruct K as [K|K]; rewrite Kr in K; discriminate.
  - intros m mr Hm. destruct (aptr_eqb_spec m g) as [->|NE].
    + destruct (s_metas s !! g) as [mr0|] eqn:E; [exact (ia_metas g mr0 E)|]. exfalso. exact (g_present _ _ _ _ _ _ pa_GOK E).
    + rewrite lookup_insert_ne in Hm by congruence. exact (ia_metas m mr Hm).
  - destruct ia_avail as [A1 A2]. split; [exact A1|]. intros Hc. destruct (A2 Hc) as (a & T1 & T2 & T3). exists a. split; [exact T1|]. split; [exact T2|].
    intros k Hk. rewrite lookup_insert_ne; [exact (T3 k Hk)|].
    intros E. pose proof (T3 k Hk) as N0. rewrite <- E in N0. exact (g_present _ _ _ _ _ _ pa_GOK N0).
  - intros q Hq. destruct (ia_availptr q Hq) as (rq & Hrq & K). exists rq. split; [| exact K]. apply pa_keep; [exact Hrq|].
    intros E. rewrite E, Hr in Hrq. injection Hrq as ->. destruct K as [K|K]; rewrite Kr in K; discriminate.
  - intros sc Hsc'. rewrite US, pa_gcnt. exact (ia_usage sc Hsc').
Qed.

Lemma pa_hosts b0 m0 : hosts pa_s5 b0 m0 <-> hosts s b0 m0.
Proof. apply hosts_ext. apply pa_groups. Qed.

Lemma pa_inv_M : inv_M X1 pa_s5 LS.
Proof.
  destruct pa_R'_fields as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8).
  destruct IM as [M1 M2 M3 M4 M5]; constructor.
  - intros m Hm. rewrite pa_MR in Hm |- *. destruct (aptr_eqb_spec m g) as [E|NE]; [| exact (M1 m Hm)].
    exfalso. rewrite F3 in Hm. subst m. rewrite pa_mem in Hm. discriminate.
  - intros m b0 Hm. rewrite pa_MR in Hm. destruct (aptr_eqb_spec m g) as [E|NE].
    + subst m. rewrite F3 in Hm. destruct (M2 g b0 Hm) as [H|H]; [left; apply pa_hosts; exact H| right; exact H].
    + destruct (M2 m b0 Hm) as [H|H]; [left; apply pa_hosts; exact H| right; exact H].
  - intros b0 h Hb0. rewrite pa_groups in Hb0. destruct (M3 b0 h Hb0) as (m & H1 & H2 & H3). exists m. rewrite pa_MR.
    destruct (aptr_eqb_spec m g) as [E|NE]; [subst m; rewrite F3, F6|]; auto.
  - intros m Hm. destruct Hm.
  - intros z Hz. destruct Hz.
Qed.

Lemma pa_inv_L : inv_L pa_s5 LS.
Proof.
  destruct pa_R'_fields as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8).
  assert (NX : forall x, m_next (MR pa_s5 x) = m_next (MR s x)) by (intros x; rewrite pa_MR; destruct (aptr_eqb_spec x g) as [->|]; [exact F2| reflexivity]).
  assert (PX : forall x, m_prev (MR pa_s5 x) = m_prev (MR s x)) by (intros x; rewrite pa_MR; destruct (aptr_eqb_spec x g) as [->|]; [exact F1| reflexivity]).
  pose proof (get_head_ext s pa_s5 pa_ctx) as HE.
  destruct IL as [L1 L2 L3 L4 L5 L6 L7 L9]; constructor.
  - intros h. rewrite HE. apply L1.
  - intros h. specialize (L2 h). destruct (LS h) as [|a l] eqn:E; [exact I|]. cbn [dll] in L2 |- *.
    eapply linked_ext; [| | exact L2]; intros; auto.
  - exact L3.
  - exact L4.
  - intros m. rewrite NX, PX. apply L5.
  - intros m Hm. pose proof (L6 m Hm) as Z0. rewrite pa_MR. destruct (aptr_eqb_spec m g) as [E|NE]; [| exact Z0].
    exfalso. subst m. pose proof pa_mem as MM. rewrite Z0 in MM. discriminate.
  - intros sc m Hm. destruct (L7 sc m Hm) as (H1 & H2 & H3). split; [exact H1|]. split; [apply (live_group_ext s pa_s5 pa_groups); exact H2|].
    rewrite pa_MR. destruct (aptr_eqb_spec m g) as [E|NE]; [subst m; rewrite F8|]; exact H3.
  - exact L9.
Qed.

Lemma pa_group_other m0 b0 ai0 : s_groups s !! b0 = Some (mkGhdr (Some m0) ai0) -> m0 <> g -> fst b0 <> rid /\ MR pa_s5 m0 = MR s m0.
Proof.
  intros Hb0 NE. split; [| exact (pa_MRo m0 NE)].
  intros Ef. apply NE. exact (proj1 (alone X1 s L BL1 LS INV1 g b pa_Hg Hsc b0 m0 (ex_intro _ ai0 Hb0) Ef)).
Qed.

Lemma pa_inv_G : inv_G X1 pa_s5 LS.
Proof.
  pose proof pa_Kr as Kr. destruct pa_nn_div as [ND NP].
  destruct pa_R'_fields as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8).
  destruct pa_g63 as (E63 & L0 & ML & NL).
  destruct IG as [G1 G2 G3 G4 G5]; constructor; rewrite ?pa_groups.
  - intros m0 b0 ai0 Hb0. destruct (aptr_eqb_spec m0 g) as [->|NE].
    + pose proof (hosts_inj _ _ _ IM b0 b g (ex_intro _ ai0 Hb0) pa_Hg) as ->.
      rewrite Hgb in Hb0. injection Hb0 as <-.
      pose proof pa_GOK as GO. destruct GO as [Q1 Q2 Q3 Q4 Q5 Q6 Q7 Q8 Q9 Q10 Q11 Q12 Q13 Q14 Q15 Q16].
      constructor; rewrite ?pa_MRg, ?F1, ?F2, ?F3, ?F4, ?F5, ?F6, ?F7, ?F8, ?pa_R'_maplen.
      * rewrite pa_metas, lookup_insert_eq. discriminate.
      * exact Q2.
      * exact Q3.
      * right. split; [exact E63|]. split; [exact L0|]. split; [lia| exact NL].
      * exact Q5.
      * lia.
      * exact Q7.
      * intros _ Hai. lia.
      * intros _ Hlt. lia.
      * intros _ sc Hin. exfalso. apply NL. exists (LActive sc). exact Hin.
      * intros Hlt. lia.
      * intros _ Hlt. lia.
      * exact Q13.
      * intros _. split; [reflexivity|]. exists pa_r'. rewrite pa_lookup. unfold b. cbn [fst]. rewrite N.eqb_refl.
        split; [reflexivity|]. split; [exact Kr|]. unfold pa_r'. cbn [r_len].
        rewrite round_up_pg_aligned by (unfold PGSZ in Hnna; exact Hnna). split; [lia|].
        unfold gend. rewrite pa_R'_cnt, pa_R'_sstart. lia.
      * intros Z0. exfalso. lia.
      * intros E0. exfalso. lia.
    + destruct (pa_group_other m0 b0 ai0 Hb0 NE) as [NR ME].
      pose proof (G1 m0 b0 ai0 Hb0) as GO. destruct GO as [Q1 Q2 Q3 Q4 Q5 Q6 Q7 Q8 Q9 Q10 Q11 Q12 Q13 Q14 Q15 Q16].
      constructor; rewrite ?ME; try assumption.
      * rewrite pa_metas, lookup_insert_ne by congruence. exact Q1.
      * intros Hml. destruct (Q14 Hml) as (H0 & r0 & Hr0 & K0 & E1 & E2). split; [exact H0|]. exists r0.
        split; [apply pa_keep; [exact Hr0| exact NR]|]. auto.
      * intros Hml. destruct (Q15 Hml) as (p & i & Hsl & Hfb & Hge & Hscp & Hstp). exists p, i. rewrite pa_slots.
        assert (NEp : p <> g) by (intros ->; lia).
        rewrite (pa_MRo p NEp). split; [exact Hsl|]. auto.
  - intros b0 ai0 Hb0. exact (G2 b0 ai0 Hb0).
  - intros m1 m2 b1 b2 ai1 ai2 H1 H2 A1 A2 E.
    destruct (aptr_eqb_spec m1 g) as [->|N1].
    { rewrite pa_MRg, F6 in A1. pose proof (g_ai _ _ _ _ _ _ (G1 g b1 ai1 H1)). exfalso. lia. }
    destruct (aptr_eqb_spec m2 g) as [->|N2].
    { rewrite pa_MRg, F6 in A2. pose proof (g_ai _ _ _ _ _ _ (G1 g b2 ai2 H2)). exfalso. lia. }
    rewrite (pa_MRo m1 N1) in A1, E. rewrite (pa_MRo m2 N2) in A2, E.
    exact (G3 m1 m2 b1 b2 ai1 ai2 H1 H2 A1 A2 E).
  - intros q rq Hq K NO. apply pa_some in Hq as [[-> ->]|[NE Hq]].
    + exists g. split; [apply pa_hosts; exact pa_Hg|]. rewrite pa_MRg, pa_R'_maplen. lia.
    + destruct (G4 q rq Hq K NO) as (m0 & Hm0 & Hml). exists m0. split; [apply pa_hosts; exact Hm0|].
      rewrite pa_MR. destruct (aptr_eqb_spec m0 g) as [->|NEm]; [rewrite pa_R'_maplen; lia| exact Hml].
  - intros b0 h Hb0. destruct (G5 b0 h Hb0) as (r0 & Hr0 & K0). destruct (N.eq_dec (fst b0) rid) as [E|NE].
    + exists pa_r'. rewrite pa_lookup, E, N.eqb_refl. split; [reflexivity| exact Kr].
    + exists r0. split; [apply pa_keep; assumption| exact K0].
Qed.

(* [comment removed for export] *)
Lemma pa_c_not_block k : In k BL1 -> bslot k <> c.
Proof.
  intros Hk E. destruct pa_g63 as (E63 & L0 & ML & NL).
  pose proof (is_part _ _ _ IS b g ai 0 Hgb ltac:(lia)) as P5. cbv zeta in P5.
  rewrite (slot_start'_eq _ _ _ IM _ _ _ pa_Hg), (sstart0 _ _ _ IM _ _ pa_Hg) in P5.
  assert (Ec : slot_start' (MR s g) 0 = c) by (rewrite (slot_start'_eq _ _ _ IM _ _ _ pa_Hg), (sstart0 _ _ _ IM _ _ pa_Hg), pa_c; reflexivity).
  destruct P5 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & CE & _).
  apply CE. split; [| cbn [x_pend X1]; rewrite pa_c; reflexivity].
  rewrite <- pa_c, <- E. apply in_map. exact Hk.
Qed.

Lemma pa_slot_g q i' : s_slots s !! q = Some (g, i') -> i' = 0 /\ q = c.
Proof.
  intros Hq. destruct (is_valid _ _ _ IS _ _ _ Hq) as (_ & Hi & Eq). destruct pa_g63 as (_ & L0 & _ & _).
  assert (i' = 0) by lia. subst i'. split; [reflexivity|].
  rewrite Eq, (slot_start'_eq _ _ _ IM _ _ _ pa_Hg), (sstart0 _ _ _ IM _ _ pa_Hg), pa_c. reflexivity.
Qed.

Lemma pa_slot_start'_g : slot_start' pa_R' 0 = slot_start' (MR s g) 0.
Proof.
  rewrite !slot_start'_sstart, pa_R'_gbase, pa_gbase, pa_R'_sstart, (sstart0 _ _ _ IM _ _ pa_Hg). unfold b. cbn [snd]. f_equal. lia.
Qed.

Lemma pa_inv_S : inv_S X1 pa_s5 BL1.
Proof.
  destruct pa_R'_fields as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8). destruct pa_g63 as (E63 & L0 & ML & NL).
  destruct IS as [S1 S2 S3 S4 S5 S6]; constructor; rewrite ?pa_slots, ?pa_groups.
  - intros q m0 i0 Hq. destruct (S1 q m0 i0 Hq) as (LG & Hi & Eq). split; [apply (live_group_ext s pa_s5 pa_groups); exact LG|].
    rewrite pa_MR. destruct (aptr_eqb_spec m0 g) as [->|NE]; [| auto].
    rewrite F6. split; [exact Hi|]. destruct (pa_slot_g q i0 Hq) as [-> ->]. rewrite pa_slot_start'_g. exact Eq.
  - intros b0 m0 i0 Hb0 Hi. apply pa_hosts in Hb0. rewrite pa_MR in Hi |- *. destruct (aptr_eqb_spec m0 g) as [->|NE]; [| exact (S2 b0 m0 i0 Hb0 Hi)].
    rewrite F6, L0 in Hi. assert (i0 = 0) by lia. subst i0. rewrite pa_slot_start'_g. apply (S2 b0); [exact Hb0| lia].
  - intros b0 m0 ai0 i0 Hb0 Hi. rewrite pa_MR in Hi |- *. destruct (aptr_eqb_spec m0 g) as [->|NE]; [| exact (S3 b0 m0 ai0 i0 Hb0 Hi)].
    rewrite F4, F5. rewrite F6, L0 in Hi. assert (i0 = 0) by lia. subst i0. rewrite pa_slot_start'_g. apply (S3 b0 g ai0 0 Hb0). lia.
  - exact S4.
  - exact S5.
  - intros k Hk. destruct (S6 k Hk) as (m0 & i0 & Hs0 & Ho & Hsz & Hf). exists m0, i0. split; [exact Hs0|]. split; [exact Ho|]. split; [exact Hsz|].
    rewrite pa_MR. destruct (aptr_eqb_spec m0 g) as [->|NE]; [| exact Hf].
    exfalso. destruct (pa_slot_g _ _ Hs0) as [_ E]. exact (pa_c_not_block k Hk E).
Qed.

Lemma pa_get_shadow_s_cells o v t : r_cells (get_shadow s rid) !! o = Some (v, t) -> 0 <= v < 256 /\ (t <= s_tick s)%N.
Proof.
  intros Hc. destruct (get_shadow_cells_some s rid o (v, t) Hc) as (sh & Hsh & Hc').
  exact (proj1 (TKS_of _ _ _ _ _ INV1 rid sh Hsh) o v t Hc').
Qed.

Lemma pa_hosts_rid b0 m0 : hosts s b0 m0 -> fst b0 = rid -> m0 = g /\ b0 = b.
Proof. intros H E. exact (alone X1 s L BL1 LS INV1 g b pa_Hg Hsc b0 m0 H E). Qed.

Lemma pa_inv_SH : inv_SH pa_s5 BL1.
Proof.
  pose proof pa_Kr as Kr. destruct pa_R'_fields as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8). destruct pa_g63 as (E63 & L0 & ML & NL).
  pose proof pa_len_ge as PL. pose proof pa_sh3_ticks as [T31 T32]. destruct pa_nn_div as [ND NP].
  destruct ISH as [H1 H2 H3 H4 H5 H6]; constructor.
  - intros q sh Hq. rewrite pa_shadow in Hq. destruct (N.eq_dec q rid) as [->|NE].
    + exists pa_r'. rewrite pa_lookup, N.eqb_refl. split; [reflexivity| exact Kr].
    + rewrite lookup_insert_ne in Hq by congruence. destruct (H1 q sh Hq) as (r0 & Hr0 & K0). exists r0. split; [apply pa_keep; assumption| exact K0].
  - intros q sh Hq. rewrite pa_tick. rewrite pa_shadow in Hq. destruct (N.eq_dec q rid) as [->|NE].
    + rewrite lookup_insert_eq in Hq. injection Hq as <-. cbn [sh5 r_cells r_hav r_havp]. split; [| split].
      * intros o v t Hc. destruct (Z.eq_dec o (nn - IB)) as [->|NEo].
        -- rewrite lookup_insert_eq in Hc. injection Hc as <- <-. change (Z.land 0 255) with 0. split; [lia| apply N.le_refl].
        -- rewrite lookup_insert_ne in Hc by congruence. unfold sh3 in Hc. rewrite pruneF_cells in Hc.
           destruct (o <? pa_len); [| discriminate]. exact (pa_get_shadow_s_cells o v t Hc).
      * intros u hl ch Hu Hin. exact (T31 u hl ch Hu Hin).
      * intros pg t Hp. exact (T32 pg t Hp).
    + rewrite lookup_insert_ne in Hq by congruence. exact (H2 q sh Hq).
  - intros b0 m0 i Hb0 Hi. apply pa_hosts in Hb0. destruct (aptr_eqb_spec m0 g) as [->|NE].
    + pose proof (hosts_inj _ _ _ IM b0 b g Hb0 pa_Hg) as ->. rewrite pa_MRg in Hi |- *. rewrite pa_R'_cnt in Hi. unfold b. cbn [fst]. rewrite pa_R'_sstart.
      assert (i = 0 \/ i = 1) as [E0|E0] by lia; rewrite E0.
      * replace (UNIT + (nn - UNIT) * 0 - IB) with 12 by (unfold UNIT, IB; lia).
        apply pa_known_low; [unfold PGSZ in PL; lia| unfold PGSZ, IB in *; lia|].
        pose proof (H3 b g 0 pa_Hg ltac:(unfold cnt_of; lia)) as K. rewrite (sstart0 _ _ _ IM _ _ pa_Hg) in K. unfold b in K. cbn [fst snd] in K.
        replace (0 + UNIT - IB) with 12 in K by (unfold UNIT, IB; lia). exact K.
      * replace (UNIT + (nn - UNIT) * 1 - IB) with (nn - IB) by lia. unfold known, SHd. cbn [fst snd]. exact pa_read_end.
    + rewrite (pa_MRo m0 NE) in Hi |- *. destruct (N.eq_dec (fst b0) rid) as [E|NEr]; [exfalso; exact (NE (proj1 (pa_hosts_rid b0 m0 Hb0 E)))|].
      destruct b0 as [q o]. cbn [fst] in *. apply pa_known_other; [exact NEr|]. exact (H3 (q, o) m0 i Hb0 Hi).
  - intros b0 m0 o Hb0 Ho. apply pa_hosts in Hb0. destruct (N.eq_dec (fst b0) rid) as [E|NEr].
    + destruct (pa_hosts_rid b0 m0 Hb0 E) as [-> ->]. unfold b. cbn [fst snd]. rewrite Z.add_0_l.
      apply pa_unknown_low; [unfold PGSZ in PL; lia| unfold PGSZ, IB in *; lia|].
      pose proof (H4 b g o pa_Hg Ho) as K. unfold b in K. cbn [fst snd] in K. rewrite Z.add_0_l in K. exact K.
    + destruct b0 as [q o0]. cbn [fst snd] in *. apply pa_unknown_other; [exact NEr|]. exact (H4 (q, o0) m0 o Hb0 Ho).
  - intros b0 m0 p i Hb0 Hml Hsl. apply pa_hosts in Hb0. rewrite pa_slots in Hsl.
    destruct (aptr_eqb_spec m0 g) as [->|NE]; [rewrite pa_MRg, pa_R'_maplen in Hml; exfalso; lia|]. rewrite (pa_MRo m0 NE) in Hml.
    destruct (N.eq_dec (fst b0) rid) as [E|NEr]; [exfalso; exact (NE (proj1 (pa_hosts_rid b0 m0 Hb0 E)))|].
    assert (NEp : p <> g).
    { intros ->. destruct (pa_slot_g _ _ Hsl) as [_ Eb]. apply NEr. rewrite Eb, pa_c. reflexivity. }
    rewrite (pa_MRo p NEp). destruct b0 as [q o0]. cbn [fst snd] in *.
    destruct (H5 (q, o0) m0 p i Hb0 Hml Hsl) as ((v3 & K3 & E3 & R3) & K2 & K1 & Q). cbn [fst snd] in K3, K2, K1, Q.
    split; [exists v3; split; [apply pa_known_other; [exact NEr| exact K3]| auto]|].
    split; [apply pa_known_other; [exact NEr| exact K2]|]. split; [apply pa_known_other; [exact NEr| exact K1]| exact Q].
  - intros k m0 i Hk Hsl. rewrite pa_slots in Hsl.
    assert (NE : m0 <> g).
    { intros ->. destruct (pa_slot_g _ _ Hsl) as [_ E]. exact (pa_c_not_block k Hk E). }
    assert (NEr : fst (bslot k) <> rid).
    { intros E. destruct (is_valid _ _ _ IS _ _ _ Hsl) as ([b0 Hb0] & _ & Eq).
      rewrite (slot_start'_eq _ _ _ IM _ _ _ Hb0) in Eq. apply NE. rewrite Eq in E. cbn [fst] in E.
      exact (proj1 (pa_hosts_rid b0 m0 Hb0 E)). }
    rewrite (pa_MRo m0 NE). cbv zeta.
    pose proof (H6 k m0 i Hk Hsl) as (B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8). cbv zeta in *.
    split; [apply pa_known_other; [exact NEr| exact B1]|].
    split; [apply pa_known_other; [exact NEr| exact B2]|].
    split; [apply pa_known_other; [exact NEr| exact B3]|].
    split; [apply pa_known_other; [exact NEr| exact B4]|].
    split; [exact B5|].
    split. { intros R5. destruct (B6 R5) as (C1 & C2 & C3 & C4 & C5 & C6). repeat split; try (apply pa_known_other; [exact NEr|]); assumption. }
    split. { intros R0. apply pa_known_other; [exact NEr|]. exact (B7 R0). }
    intros a Ha. apply pa_unknown_other; [exact NEr|]. exact (B8 a Ha).
Qed.

Theorem pa_INVL : INVL X1 pa_s5 pa_L BL1 LS.
Proof.
  split; [exact pa_inv_R|]. split; [exact pa_inv_A|]. split; [exact pa_inv_M|]. split; [exact pa_inv_L|].
  split; [exact pa_inv_G|]. split; [exact pa_inv_S| exact pa_inv_SH].
Qed.

(* [comment removed for export] *)
Theorem pa_facts :
  INVL X1 pa_s5 pa_L BL1 LS
  /\ MR pa_s5 g = pa_R' /\ get_stride pa_R' = nn - UNIT /\ (forall i, sstart pa_R' i = UNIT + (nn - UNIT) * i)
  /\ gbase pa_R' = b /\ m_last_idx pa_R' = m_last_idx (MR s g) /\ c = (rid, UNIT) /\ PGSZ <= pa_len
  /\ s_slots pa_s5 = s_slots s /\ s_groups pa_s5 = s_groups s /\ s_tick pa_s5 = s_tick s
  /\ (forall o v, 0 <= o < pa_len -> o <> nn - IB -> known s (rid, o) v -> known pa_s5 (rid, o) v)
  /\ (forall o v t, r_cells (get_shadow pa_s5 rid) !! o = Some (v, t) -> o <> nn - IB -> (t < s_tick s)%N)
  /\ m_sizeclass (MR s g) = 63 /\ m_last_idx (MR s g) = 0.
Proof.
  destruct pa_g63 as (E63 & L0 & _ & _). destruct pa_R'_fields as (_ & _ & _ & _ & _ & F6 & _ & _).
  split; [exact pa_INVL|]. split; [exact pa_MRg|]. split; [exact pa_R'_stride|]. split; [exact pa_R'_sstart|].
  split; [exact pa_R'_gbase|]. split; [exact F6|]. split; [exact pa_c|]. split; [exact pa_len_ge|].
  split; [exact pa_slots|]. split; [exact pa_groups|]. split; [exact pa_tick|].
  split; [exact pa_known_low|]. split; [exact pa_cells_old|]. split; [exact E63| exact L0].
Qed.

(* [comment removed for export] *)
Theorem pa_facts2 :
  MR pa_s5 g = pa_R' /\ m_last_idx pa_R' = m_last_idx (MR s g)
  /\ s_slots pa_s5 = s_slots s /\ s_groups pa_s5 = s_groups s /\ s_tick pa_s5 = s_tick s
  /\ (forall o, 0 <= o < pa_len -> o <> nn - IB -> cell_read (get_shadow pa_s5 rid) o = cell_read (get_shadow s rid) o)
  /\ cell_read (get_shadow pa_s5 rid) (nn - IB) = Known 0
  /\ (forall o, pa_len <= o -> o <> nn - IB -> cell_read (get_shadow pa_s5 rid) o = Known 0)
  /\ PGSZ <= pa_len.
Proof.
  destruct pa_R'_fields as (_ & _ & _ & _ & _ & F6 & _ & _).
  split; [exact pa_MRg|]. split; [exact F6|]. split; [exact pa_slots|]. split; [exact pa_groups|]. split; [exact pa_tick|].
  split; [exact pa_read_low|]. split; [exact pa_read_end|]. split; [exact pa_read_high| exact pa_len_ge].
Qed.
End PHASEA.


End CeilWrap.
(* [comment removed for export] *)
Ltac splits := repeat (lazymatch goal with |- _ /\ _ => split | |- _ => fail end).
