(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool Lia Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase State Specs.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Decode.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require STree Malloc Mall7vg KInv KLink.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require MI_List.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require MI_Inv MI_Kit MI_Arith MI_List MI_Geom MI_Ext.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require MI_Pres2.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require MI_S421.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require MI_Pres2.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require MI_Pres2.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require MI_Pres4.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require MI_Pres4 MI_Ws22.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require MI_W2ig.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require MI_W2ig MI_W3do.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require MI_WTry2.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require MI_WTry2 MI_Wp9i MI_Cnt.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require MI_Ccma.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require MI_Ccma.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require MI_Ccma.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require MI_Ccma.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require MI_Ccma.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require MI_Ccma.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require MI_Bits LB_T80p LB_Inv LB_Sum LB_Bound LB_WNtf LB_XferF LB_Tree LB_QM.

Module LB_KCnt.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool Lia Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase State Specs.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Decode.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require STree Malloc KInv KLink MI_Inv MI_Cnt MI_Ws22 LB_T80p LB_Inv LB_Sum.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require LB_AG.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require LB_Bound LB_QM LB_Ljn7.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require MI_WFree.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.STree OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.Malloc OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.KInv OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.KLink OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_Inv OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_Cnt OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_Ws22 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.LB_T80p OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.LB_Inv OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.LB_Sum OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.LB_AG.LB_Cnt OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.LB_Bound OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.LB_QM OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.LB_Ljn7 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_WFree.LB_Dead.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Ceiling.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
(* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac Stdlib.micromega.Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_noeuclid ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_post_hook.
(* [comment removed for export] *)
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Section LBCEIL.
Context {Clg : Ceiling}.  (* [comment removed for export] *)

(* [comment removed for export] *)
Lemma nodup_incl_length {A} (l l' : list A) : List.NoDup l -> incl l l' -> (length l <= length l')%nat.
Proof. intros ND INC. apply (List.NoDup_incl_length ND INC). Qed.

(* [comment removed for export] *)
Lemma len_filter_key_eq (l : list (N * region)) (o : N) :
  List.NoDup (map fst l) -> (length (List.filter (fun kr => N.eqb (fst kr) o) l) <= 1)%nat.
Proof.
  induction l as [|[k r] l IH]; intros ND; cbn; [lia|].
  inversion ND as [|? ? Hni ND']; subst. specialize (IH ND').
  destruct (N.eqb_spec k o) as [->|NE]; cbn; [| exact IH].
  (* [comment removed for export] *)
  assert (E : forall l', ~ In o (map fst l') -> List.filter (fun kr : N * region => N.eqb (fst kr) o) l' = []).
  { clear. induction l' as [|[k' r'] l' IH]; intros Hni; [reflexivity|]. cbn in Hni |- *.
    destruct (N.eqb_spec k' o) as [->|NE']; cbn; [exfalso; apply Hni; left; reflexivity|].
    apply IH. intros H. apply Hni. right. exact H. }
  rewrite (E l Hni). cbn. lia.
Qed.

Lemma len_filter_key_ne (l : list (N * region)) (o : N) :
  List.NoDup (map fst l) ->
  (length l <= length (List.filter (fun kr => negb (N.eqb (fst kr) o)) l) + 1)%nat.
Proof.
  intros ND. pose proof (len_filter_key_eq l o ND) as H1.
  pose proof (List.filter_length (fun kr : N * region => N.eqb (fst kr) o) l) as H2. cbn beta in H2. lia.
Qed.

Section KCNT.
Variables (X : extras) (st : mstate) (L : mled) (BL : list blk) (LS : lhead -> list aptr) (P : Z -> Z) (d : Z).
Hypothesis INV : INVL X st L BL LS.
Hypothesis SGH : SG st BL.
Hypothesis HAQ : AQ st BL P.
Hypothesis Q : QM X st d.
Let IR : inv_R X st L := proj1 INV.
Let IG : inv_G X st LS := proj1 (proj2 (proj2 (proj2 (proj2 INV)))).

Definition isGb (kr : N * region) : bool := match r_kind (snd kr) with RKGroup => true | _ => false end.

(* [comment removed for export] *)
Lemma ld_groups_len : Z.of_nat (length (ld_groups L)) <= ngroups st + 1.
Proof.
  pose proof (Permutation_length (ir_groups _ _ _ IR)) as EL. rewrite length_map in EL. rewrite EL.
  set (GR := List.filter (fun kr : N * region => match r_kind (snd kr) with RKGroup => true | _ => false end) (map_to_list (s_regions st))).
  assert (NDk : List.NoDup (map fst GR)).
  { subst GR. pose proof (mtl_nodup_keys (s_regions st)) as ND. revert ND. generalize (map_to_list (s_regions st)) as l. clear.
    induction l as [|[k r] l IH]; intros ND; cbn; [constructor|]. cbn in ND. inversion ND as [|? ? Hni ND']; subst.
    destruct (r_kind r); cbn; try (apply IH; exact ND').
    constructor; [| apply IH; exact ND']. intros Hin. apply Hni. apply in_map_iff in Hin as ([k' r'] & E & Hin').
    apply filter_In in Hin' as [Hin' _]. apply in_map_iff. exists (k', r'). auto. }
  (* [comment removed for export] *)
  set (o := match x_orph X with Some rid => rid | None => s_next_rid st end).
  set (GR' := List.filter (fun kr : N * region => negb (N.eqb (fst kr) o)) GR).
  pose proof (len_filter_key_ne GR o NDk) as L1. fold GR' in L1.
  (* [comment removed for export] *)
  assert (INC : incl (map fst GR') (map (fun mb : aptr * aptr => fst (snd mb)) (gmetas st))).
  { intros rid Hin. apply in_map_iff in Hin as ([rid' r] & E & Hin). cbn in E. subst rid'.
    apply filter_In in Hin as [Hin NEo]. apply filter_In in Hin as [Hin K]. apply mtl_in in Hin. cbn in K, NEo.
    assert (KG : r_kind r = RKGroup) by (destruct (r_kind r); try discriminate; reflexivity).
    assert (NO : x_orph X <> Some rid).
    { intros E. subst o. rewrite E in NEo. rewrite N.eqb_refl in NEo. discriminate. }
    destruct (ig_top _ _ _ IG rid r Hin KG NO) as (m & [ai Hb] & _).
    apply in_map_iff. exists (m, (rid, 0%Z)). split; [reflexivity|]. apply gmetas_in. exists ai. exact Hb. }
  assert (ND' : List.NoDup (map fst GR')).
  { subst GR'. revert NDk. generalize GR as l. clear. induction l as [|[k r] l IH]; intros ND; cbn; [constructor|].
    cbn in ND. inversion ND as [|? ? Hni ND']; subst. destruct (negb (N.eqb k o)); cbn; [| apply IH; exact ND'].
    constructor; [| apply IH; exact ND']. intros Hin. apply Hni. apply in_map_iff in Hin as ([k' r'] & E & Hin').
    apply filter_In in Hin' as [Hin' _]. apply in_map_iff. exists (k', r'). auto. }
  pose proof (nodup_incl_length _ _ ND' INC) as L2. rewrite !length_map in L2.
  unfold ngroups, zlen. subst GR' GR. lia.
Qed.

(* [comment removed for export] *)
Lemma ld_metas_len : 2 * PGSZ * Z.of_nat (length (ld_metas L)) <= meta_bytes st.
Proof.
  pose proof (Permutation_length (ir_metas _ _ _ IR)) as EL. rewrite length_map in EL. rewrite EL.
  unfold meta_bytes, regions_l.
  (* [comment removed for export] *)
  assert (G : forall l, incl l (map_to_list (s_regions st)) ->
    2 * PGSZ * Z.of_nat (length (List.filter (fun kr : N * region => match r_kind (snd kr) with RKMeta => true | _ => false end) l))
    <= zsum (map (fun kr : N * region => match r_kind (snd kr) with RKMeta => r_len (snd kr) | _ => 0 end) l)).
  { induction l as [|[rid r] l IH]; intros INC; [cbn; lia|].
    cbn [map List.filter fst snd]. rewrite zsum_cons. specialize (IH ltac:(intros x Hx; apply INC; right; exact Hx)).
    assert (Hr : s_regions st !! rid = Some r) by (apply mtl_in; apply INC; left; reflexivity).
    pose proof (ir_shape _ _ _ IR rid r Hr) as (_ & _ & Lpos & _ & _ & MK).
    destruct (r_kind r) eqn:K; cbn [length]; try lia.
    specialize (MK ltac:(unfold is_metakind; rewrite K; auto)). rewrite Nat2Z.inj_succ. lia. }
  apply G. intros x Hx. exact Hx.
Qed.

(* [comment removed for export] *)
Lemma BB_le_brk_pages : brk_quiet L -> 0 <= BB L <= PGSZ * brk_pages st.
Proof.
  intros Hq. pose proof (brk_pages_nonneg X st L BL LS INV) as NN.
  unfold BB. unfold brk_quiet in Hq. destruct (ld_brk L) eqn:EP; try (destruct Hq; fail).
  all: destruct (ld_brkreg L) as [[b l]|] eqn:ER; [| unfold PGSZ; lia].
  all: destruct (proj1 (ir_brkreg _ _ _ IR b l) ER) as (rid & r & Hr & K & Eb & El).
  all: pose proof (ir_shape _ _ _ IR rid r Hr) as (_ & _ & LPOS & _ & _ & MK);
       specialize (MK ltac:(unfold is_metakind; rewrite K; auto)); destruct MK as [MOD M2].
  all: unfold brk_pages, regions_l; rewrite <- El;
       change (zsum (map (fun kr : N * region => match r_kind (snd kr) with RKBrk => r_len (snd kr) / PGSZ | _ => 0 end) (map_to_list (s_regions st))))
         with (msum (fun kr : N * region => match r_kind (snd kr) with RKBrk => r_len (snd kr) / PGSZ | _ => 0 end) (s_regions st));
       rewrite (msum_delete _ (s_regions st) rid r Hr); cbn [snd]; rewrite K.
  all: assert (NN2 : 0 <= msum (fun kr : N * region => match r_kind (snd kr) with RKBrk => r_len (snd kr) / PGSZ | _ => 0 end) (delete rid (s_regions st)))
         by (unfold msum; apply zsum_map_nonneg; intros [q rq] Hin; cbn; destruct (r_kind rq); try lia;
             apply mtl_in in Hin; rewrite lookup_delete_Some in Hin; destruct Hin as [_ Hin];
             pose proof (ir_shape _ _ _ IR q rq Hin) as (_ & _ & LP & _); apply Z.div_pos; unfold PGSZ; lia).
  all: pose proof (Z.div_mod (r_len r) PGSZ ltac:(unfold PGSZ; lia)) as DM; rewrite MOD, Z.add_0_r in DM; unfold PGSZ in *; nia.
Qed.

(* [comment removed for export] *)
Lemma gm_BB_nonneg : 0 <= gm L + BB L.
Proof.
  pose proof (BB_le_brk_pages (brk_quiet_of _ _ _ IR)) as [B0 _].
  assert (G : forall l : list (Z * Z), (forall g, In g l -> 0 < snd g) -> 0 <= fold_right Z.add 0 (map (fun g : Z * Z => mmap_len (snd g)) l)).
  { induction l as [|[b len] l IHl]; intros Hl; cbn; [lia|]. pose proof (Hl _ (or_introl eq_refl)) as P0. cbn in P0.
    pose proof (mmap_len_ge len P0). specialize (IHl ltac:(intros g Hg; apply Hl; right; exact Hg)). lia. }
  assert (M : forall l : list (Z * Z * Z), (forall m, In m l -> 0 < snd (fst m)) -> 0 <= fold_right Z.add 0 (map (fun m : Z * Z * Z => mmap_len (snd (fst m))) l)).
  { induction l as [|[[b len] k] l IHl]; intros Hl; cbn; [lia|]. pose proof (Hl _ (or_introl eq_refl)) as P0. cbn in P0.
    pose proof (mmap_len_ge len P0). specialize (IHl ltac:(intros g Hg; apply Hl; right; exact Hg)). lia. }
  unfold gm.
  specialize (G (ld_groups L) ltac:(intros [b len] Hg; apply (Permutation_in _ (ir_groups _ _ _ IR)) in Hg; apply in_map_iff in Hg as ([q rq] & E & Hin);
    apply filter_In in Hin as [Hin _]; apply mtl_in in Hin; pose proof (ir_shape _ _ _ IR _ _ Hin) as (_ & _ & LP & _); cbn; inversion E; subst; exact LP)).
  specialize (M (ld_metas L) ltac:(intros [[b len] k] Hg; apply (Permutation_in _ (ir_metas _ _ _ IR)) in Hg; apply in_map_iff in Hg as ([q rq] & E & Hin);
    apply filter_In in Hin as [Hin _]; apply mtl_in in Hin; pose proof (ir_shape _ _ _ IR _ _ Hin) as (_ & _ & LP & _); cbn; inversion E; subst; exact LP)).
  lia.
Qed.

Theorem kcnt_bound : brk_quiet L -> kcnt L <= NG P + 3 * (NCAP P / 101) + 5.
Proof.
  intros Hq. unfold kcnt.
  pose proof ld_groups_len as G1. pose proof (ngroups_le X st L BL LS P INV SGH HAQ) as G2.
  pose proof ld_metas_len as M1.
  pose proof (meta_bytes_bound4 st (qmm_len _ _ _ Q) (qmm_dist _ _ _ Q) (qmm_shift _ _ _ Q)) as M2.
  pose proof (BB_le_brk_pages Hq) as [B0 B1]. pose proof (brk_pages_boundQ X st L IR (qmm_brk _ _ _ Q)) as B2.
  pose proof (aq_carved _ _ _ HAQ) as NC. assert (NC0 : 0 <= ncarved st) by (unfold ncarved; apply zlen_nonneg).
  assert (DM : ncarved st / 101 <= NCAP P / 101) by (apply Z.div_le_mono; lia).
  assert (D0 : 0 <= ncarved st / 101) by (apply Z.div_pos; lia).
  assert (MB : Z.of_nat (length (ld_metas L)) <= 2 * (ncarved st / 101) + 2) by (unfold PGSZ in *; nia).
  assert (BQ : BB L / PGSZ <= ncarved st / 101 + 2).
  { apply Z.div_le_upper_bound; [unfold PGSZ; lia|]. unfold PGSZ in *. nia. }
  lia.
Qed.
End KCNT.

(* [comment removed for export] *)
Lemma kcnt_KCAP X st L BL LS P d : INVL X st L BL LS -> SG st BL -> AQ st BL P -> QM X st d -> kcnt L + 3 <= KCAP.
Proof.
  intros INV SGH HAQ Q. pose proof (kcnt_bound X st L BL LS P d INV SGH HAQ Q (brk_quiet_of _ _ _ (proj1 INV))) as K.
  pose proof (aq_kcap _ _ _ HAQ). unfold KCAP. lia.
Qed.

Lemma kcnt_KCAP_S X st L BL LS P : INVL X st L BL LS -> SINV X st BL -> AQ st BL P -> kcnt L + 3 <= KCAP.
Proof. intros INV SI HAQ. apply SINV_split in SI as [SGH Q]. exact (kcnt_KCAP X st L BL LS P 0 INV SGH HAQ Q). Qed.

(* [comment removed for export] *)
Lemma CAP_lower' P c : (forall c, 0 <= P c) -> 0 <= c -> 14 <= CAP P c.   (* [comment removed for export] *)
Proof.
  intros HP Hc.
  assert (0 <= HOSTSTD P c).
  { unfold HOSTSTD. apply zsum_map_nonneg. intros c' Hc'.
    assert (G : 0 <= c' < 48) by (unfold guests in Hc'; cbn in Hc'; lia). cbn beta.
    destruct (bighost c' =? c); [| apply Z.le_refl]. pose proof (tab_basic_ok c' G) as (_ & CM & _).
    apply Z.div_pos; [| lia]. unfold CAP0. pose proof NBCAP_ge13. pose proof (HP c'). destruct (c' <=? 23); lia. }
  unfold CAP, CAP0. pose proof NBCAP_ge13. pose proof (HP c). destruct (c <=? 23); lia.
Qed.

Lemma NCAP_lower' P : (forall c, 0 <= P c) -> 4 <= NCAP P.   (* [comment removed for export] *)
Proof.
  intros HP. unfold NCAP, NG.
  assert (0 <= zsum (map (fun c => (CAP P c + 32) / cmax c + 160) classes)).
  { apply zsum_map_nonneg. intros c Hc. apply In_classes in Hc. cbn beta.
    pose proof (tab_basic_ok c Hc) as (_ & CM & _). pose proof (CAP_lower' P c HP ltac:(lia)).
    assert (0 <= (CAP P c + 32) / cmax c) by (apply Z.div_pos; lia). lia. }
  pose proof (HP 63). lia.
Qed.

Lemma PHI_lower P : (forall c, 0 <= P c) -> 2 ^ 24 <= PHI P.
Proof.
  intros HP. unfold PHI.
  assert (S1 : 0 <= zsum (map (fun c => if std_nested c then 0 else std_len c * ((CAP P c + 32) / cmax c)) classes)).
  { apply zsum_map_nonneg. intros c Hc. apply In_classes in Hc. destruct (std_nested c); [lia|].
    pose proof (tab_basic_ok c Hc) as (SS & CM & SL & _). pose proof (CAP_lower' P c HP ltac:(lia)).
    assert (0 <= std_span c) by (unfold std_span, UNIT; nia).
    apply Z.mul_nonneg_nonneg; [lia| apply Z.div_pos; lia]. }
  assert (S2 : zsum (map (fun c => 160 * (S_ c + 4111)) classes) = ltac:(let v := eval vm_compute in (zsum (map (fun c => 160 * (S_ c + 4111)) classes)) in exact v)).
  { vm_compute. reflexivity. }
  rewrite S2. pose proof (NCAP_lower' P HP). assert (0 <= 5 * NCAP P / 101) by (apply Z.div_pos; lia). unfold PGSZ. lia.
Qed.

End LBCEIL.
End LB_KCnt.

Module LB_Wjp3.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool Lia Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase State Specs.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Decode.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require STree Malloc Mall7vg KInv KLink.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require MI_List.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require MI_Inv MI_Kit MI_Arith MI_List MI_Geom MI_Ext.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require MI_Pres2.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require MI_Pres2.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require MI_Pres2.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require MI_Pres4.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require MI_Pres4 MI_Ws22.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require MI_W2ig.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require MI_W2ig MI_W3do MI_Cnt LB_T80p LB_Inv LB_Sum LB_Bound LB_WNtf LB_XferF LB_Tree LB_QM.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require LB_Ljn7.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require MI_WFree.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.STree OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.Malloc OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.Mall7vg OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.KInv OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.KLink OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_List.MI_Tree OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_Inv OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_Kit OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_Arith OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_List OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_Geom OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_Ext OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_Pres2.MI_Ext2 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_Pres2.MI_Pres1 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_Pres2 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_Pres4.MI_Pres3 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_Pres4 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_Ws22 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_W2ig.MI_Lsjc OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_W2ig OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_W3do OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_Cnt OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.LB_T80p OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.LB_Inv OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.LB_Sum OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.LB_Bound OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.LB_WNtf OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.LB_XferF OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.LB_Tree OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.LB_QM OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.LB_Wazc.LB_KCnt OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.LB_Ljn7 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_WFree.LB_Dead.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Ceiling.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require AndN.   (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
(* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac Stdlib.micromega.Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_noeuclid ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_post_hook.
(* [comment removed for export] *)
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Section LBCEIL.
Context {Clg : Ceiling}.  (* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma gmetas_ext st st1 : s_groups st1 = s_groups st -> gmetas st1 = gmetas st.
Proof. intros E. unfold gmetas, groups_l. rewrite E. reflexivity. Qed.

Lemma gcnt_frame st st1 c : s_groups st1 = s_groups st ->
  (forall m, (exists b, hosts st b m) -> geom (MR st1 m) = geom (MR st m)) -> gcnt st1 c = gcnt st c.
Proof.
  intros EG GEO. rewrite !gcnt_gmetas, (gmetas_ext st st1 EG). apply zsum_map_ext. intros [m b] Hin. cbn.
  apply gmetas_in in Hin as [ai Hb]. pose proof (GEO m (ex_intro _ b (ex_intro _ ai Hb))) as G. unfold geom in G. inversion G.
  unfold cnt_of. rewrite H1, H2. reflexivity.
Qed.

Lemma AQ_frame st st1 BL P : s_groups st1 = s_groups st ->
  (forall m, (exists b, hosts st b m) -> geom (MR st1 m) = geom (MR st m)) -> ncarved st1 <= NCAP P ->
  AQ st BL P -> AQ st1 BL P.
Proof.
  intros EG GEO NC A. destruct A as [A1 A2 A3 A4 A5]. constructor; auto.
  intros c Hc. rewrite (gcnt_frame st st1 c EG GEO). exact (A2 c Hc).
Qed.

(* [comment removed for export] *)
Lemma am_bytes X st L BL LS d : INVL X st L BL LS -> QM X st d ->
  gm L + BB L <= group_bytes st + PGSZ * (5 * (ncarved st / 101) + 6)
  /\ meta_bytes st <= PGSZ * (if c_meta_alloc_shift (s_ctx st) <? 1 then 0 else 2 ^ (c_meta_alloc_shift (s_ctx st) + 1) - 2)
  /\ PGSZ * brk_pages st <= PGSZ * (ncarved st / 101 + 2)
  /\ gm L + BB L <= group_bytes st + meta_bytes st + PGSZ * brk_pages st.
Proof.
  intros INV Q. pose proof (proj1 INV) as IR. destruct Q as [Q1 Q2 Q3 Q4 Q5 Q6].
  pose proof (ledger_bound X st L BL LS INV) as LB.
  pose proof (meta_bytes_bound4 st Q4 Q5 Q6) as M4. pose proof (meta_bytes_pow st Q4 Q5) as MP.
  pose proof (brk_pages_boundQ X st L IR Q3) as BP. unfold PGSZ in *. lia.
Qed.

Lemma div101_mono n N : 0 <= n <= N -> 5 * (n / 101) <= 5 * N / 101.
Proof. intros H. apply Z.div_le_lower_bound; [lia|]. pose proof (Z.div_mod n 101 ltac:(lia)). pose proof (Z.mod_pos_bound n 101 ltac:(lia)). pose proof (Z.div_le_mono n N 101 ltac:(lia) ltac:(lia)). nia. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section AMQ.
Variables (T : Type) (BL : list blk) (P : Z -> Z) (B : Z) (Post : mled -> T -> Prop) (k : mstate -> optr -> M T) (bail : M T).
Variables (X : extras) (st0 : mstate) (L0 : mled) (LS0 : lhead -> list aptr).
Hypothesis INV0 : INVL X st0 L0 BL LS0.
Hypothesis SG0 : SG st0 BL.
Hypothesis HAQ0 : AQ st0 BL P.
Hypothesis ROOM0 : c_free_meta_head (s_ctx st0) = None -> ncarved st0 + 1 <= NCAP P.
Hypothesis HB : group_bytes st0 + PGSZ * (5 * NCAP P / 101 + 8) <= B.
Hypothesis KN : forall st1 L1 LS1, INVL X st1 L1 BL LS1 -> AM_frame st0 st1 -> L_frame L0 L1 ->
  SINV X st1 BL -> AQ st1 BL P -> (forall c, gcnt st1 c = gcnt st0 c) ->
  (forall m, (exists b, hosts st0 b m) -> geom (MR st1 m) = geom (MR st0 m)) -> fqtree B L1 (k st1 None) Post.
Hypothesis KS : forall st1 L1 LS1 m, INVL (xidle X (m :: x_idle X)) st1 L1 BL LS1 -> ~ In m (x_idle X) -> AM_frame st0 st1 -> L_frame L0 L1 ->
  SINV (xidle X (m :: x_idle X)) st1 BL -> AQ st1 BL P -> ncarved st1 <= ncarved st0 + 1 -> (forall c, gcnt st1 c = gcnt st0 c) ->
  (forall x, (exists b, hosts st0 b x) -> geom (MR st1 x) = geom (MR st0 x)) ->
  fqtree B L1 (k st1 (Some m)) Post.

(* [comment removed for export] *)
Definition QT (Y : extras) (st : mstate) (d : Z) : Prop :=
  QM Y st d /\ ncarved st = ncarved st0 /\ group_bytes st = group_bytes st0
  /\ (forall m, (exists b, hosts st0 b m) -> geom (MR st m) = geom (MR st0 m)).

Lemma SV0 : forall s m i, s_slots st0 !! s = Some (m, i) -> exists b, hosts st0 b m.
Proof. intros s m i H. exact (proj1 (is_valid _ _ _ (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 INV0)))))) _ _ _ H)). Qed.

Lemma SG_of st : AM_frame st0 st -> (forall m, (exists b, hosts st0 b m) -> geom (MR st m) = geom (MR st0 m)) -> SG st BL.
Proof. intros AF GEO. apply (SG_frame st0 st BL (amf_groups _ _ AF) (amf_slots _ _ AF) GEO SV0 SG0). Qed.

(* [comment removed for export] *)
Lemma exit_none st L LS : INVL X st L BL LS -> AM_frame st0 st -> L_frame L0 L -> QT X st 0 -> fqtree B L (k st None) Post.
Proof.
  intros INV AF LF (Q & NC & GB & GEO). apply (KN st L LS INV AF LF).
  - apply SINV_split. split; [exact (SG_of st AF GEO)| exact Q].
  - apply (AQ_frame st0 st BL P (amf_groups _ _ AF) GEO); [rewrite NC; exact (aq_carved _ _ _ HAQ0)| exact HAQ0].
  - intros c. exact (gcnt_frame st0 st c (amf_groups _ _ AF) GEO).
  - exact GEO.
Qed.

Lemma bound_of st L LS d extra : INVL X st L BL LS -> QT X st d -> 0 <= extra <= 2 * PGSZ ->
  gm L + BB L + extra <= B.
Proof.
  intros INV (Q & NC & GB & GEO) HE. destruct (am_bytes X st L BL LS d INV Q) as (A & _).
  rewrite NC, GB in A. pose proof (div101_mono (ncarved st0) (NCAP P) ltac:(pose proof (ncarved_nonneg st0); pose proof (aq_carved _ _ _ HAQ0); lia)). unfold PGSZ in *. lia.
Qed.

(* [comment removed for export] *)
Lemma am_take_fq st L LS : ncarved st0 + 1 <= NCAP P -> INVL X st L BL LS -> AM_frame st0 st -> L_frame L0 L ->
  0 < c_avail_meta_count (s_ctx st) -> QT X st 0 -> fqtree B L (am_take st k bail) Post.
Proof.
  intros ROOM INV AF LF HC (Q & NC & GB & GEO).
  destruct (ia_avail _ (proj1 (proj2 INV))) as [A1 A2]. destruct (A2 HC) as (a & Ht & Ea & FREE).
  set (m := mslot a (NSLOTS - c_avail_meta_count (s_ctx st))) in *.
  pose proof (take_fresh X st L BL LS m INV HC Ea) as FRm.
  rewrite (am_take_unfold st m k bail Ea).
  (* [comment removed for export] *)
  destruct (am_take_ok X st L BL LS INV HC (fun s o => ret (s, o)) (ret (st, @None aptr))) as (m' & st2 & E2 & INV2 & AF2 & NI).
  rewrite (am_take_unfold st m _ _ Ea) in E2. assert (Em : m' = m) by (inversion E2; reflexivity). assert (Es : st2 = take_st st m) by (inversion E2; reflexivity). subst m' st2.
  destruct (QM_take X st m 0 FRm Q) as (Q2 & NC2 & RG2 & AP2 & MR2).
  assert (GEO2 : forall x, (exists b, hosts st0 b x) -> geom (MR (take_st st m) x) = geom (MR st0 x)).
  { intros x Hx. rewrite MR2; [exact (GEO x Hx)|]. intros ->.
    destruct Hx as [b [ai Hb]]. pose proof (im_hdr _ _ _ (proj1 (proj2 (proj2 INV0))) _ _ Hb) as (m1 & Em1 & MEM & _). cbn in Em1. assert (m1 = m) by congruence. subst m1.
    pose proof (GEO m (ex_intro _ b (ex_intro _ ai Hb))) as G. assert (Z0 : m_mem (MR st m) = None) by (unfold MR, get_meta_rec; rewrite FRm; reflexivity). unfold geom in G. rewrite Z0, MEM in G. congruence. }
  apply (KS (take_st st m) L LS m INV2 NI (amf_trans _ _ _ AF AF2) LF).
  - apply SINV_split. split; [| exact Q2]. exact (SG_of (take_st st m) (amf_trans _ _ _ AF AF2) GEO2).
  - apply (AQ_frame st0 (take_st st m) BL P (amf_groups _ _ (amf_trans _ _ _ AF AF2)) GEO2); [| exact HAQ0].
    rewrite NC2, NC. exact ROOM.
  - rewrite NC2, NC. lia.
  - intros c. exact (gcnt_frame st0 (take_st st m) c (amf_groups _ _ (amf_trans _ _ _ AF AF2)) GEO2).
  - exact GEO2.
Qed.

(* [comment removed for export] *)
Lemma am_carve_fq s p L LS : ncarved st0 + 1 <= NCAP P -> INVL X s L BL LS ->
  c_avail_meta_areas (s_ctx s) = Some (aadd p 4096) -> s_areas s !! p = None -> (forall k, 0 <= k < NSLOTS -> s_metas s !! mslot p k = None) ->
  PGSZ <= snd p -> snd p mod PGSZ = 0 -> c_init_done (s_ctx s) = 1 ->
  AM_frame st0 s -> L_frame L0 L -> QT X s 101 -> c_avail_meta_count (s_ctx s) = 0 ->
  fqtree B L (am_take (carve_rest s p) k bail) Post.
Proof.
  intros ROOM INV H1 H2 H3 H4 H5 H6 AF LF (Q & NC & GB & GEO) HK.
  destruct (INVL_carve X s L BL LS p INV H1 H2 H3 H4 H5 H6) as (INV' & AF' & HC).
  destruct (carve_rest_q s p) as (R1 & R2 & R3 & R4 & R5 & R6).
  eapply am_take_fq; [exact ROOM| exact INV'| exact (amf_trans _ _ _ AF AF')| exact LF| exact HC|].
  split; [exact (QM_carve_rest X s p 101 Q HK ltac:(lia))|]. split; [rewrite (ncarved_ext s _ R2); exact NC|].
  split; [rewrite (group_bytes_ext s _ R1); exact GB|]. intros m Hm. rewrite <- (GEO m Hm). unfold MR, get_meta_rec. rewrite R2. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma am_finish_fq st L LS : ncarved st0 + 1 <= NCAP P -> INVL X st L BL LS -> AM_frame st0 st -> L_frame L0 L ->
  0 < c_avail_meta_area_count (s_ctx st) -> c_init_done (s_ctx st) = 1 -> QT X st 0 -> c_avail_meta_count (s_ctx st) = 0 ->
  fqtree B L (am_finish st true k bail) Post.
Proof.
  intros ROOM INV AF LF HC HI QT0 HK. pose proof QT0 as (Q & NC & GB & GEO).
  destruct (ir_cursor _ _ _ (proj1 INV)) as (C1 & C2 & C3).
  destruct (c_avail_meta_areas (ctx st)) as [[rid off]|] eqn:EC; [| exfalso; exact (C2 HC EC)].
  destruct (C3 _ _ EC) as (r & Hr & K & P1 & P2 & P3 & P4).
  unfold am_finish. rewrite EC. cbn [snd]. rewrite (proj2 (Z.eqb_eq _ _) P2). cbn [negb].
  apply fqtree_vis; [reflexivity| reflexivity| exact (ma_event_pre X st L BL LS rid off INV EC HC)| | exact I| |].
  - intros z Hz. unfold event_post. pose proof (bound_of st L LS 0 0 INV QT0 ltac:(unfold PGSZ; lia)) as B0.
    destruct ((z =? 0) || (z =? TWO64 - ENOSYS)); [rewrite gm_bump, BB_set_metas|]; lia.
  - intros a Ha. cbn in Ha. rewrite Ha. cbn [negb].
    change (if (a =? 0) || (a =? TWO64 - ENOSYS) then am_carve st (rid, off) k bail else k st None)
      with (if (a =? 0) || (a =? TWO64 - ENOSYS) then am_carve st (rid, off) k bail else k st None).
    cbn [event_post]. destruct ((a =? 0) || (a =? TWO64 - ENOSYS)).
    + rewrite am_carve_eq.
      destruct (INVL_meta_adv X st L BL LS rid off INV EC HC) as (INV' & F1 & F2 & F3 & F4 & F5 & F6 & AF').
      eapply am_carve_fq; [exact ROOM| exact INV'| exact F1| exact F2| exact F3| exact F4| exact F5| rewrite F6; exact HI| exact (amf_trans _ _ _ AF AF')| | |].
      * destruct LF; constructor; assumption.
      * split; [| split; [exact NC| split; [exact GB| exact GEO]]].
        replace 101 with (0 + 101) by reflexivity. apply (QM_adv X st L rid off r 0 (proj1 INV) EC Hr K P2 Q).
      * exact HK.
    + eapply exit_none; [exact INV| exact AF| exact LF| exact QT0].
  - intros a Ha. cbn in Ha. rewrite Ha. exact I.
Qed.

(* [comment removed for export] *)
Lemma am_after_brk_fq st L LS : ncarved st0 + 1 <= NCAP P -> INVL X st L BL LS -> AM_frame st0 st -> L_frame L0 L ->
  c_init_done (s_ctx st) = 1 -> QT X st 0 -> c_avail_meta_count (s_ctx st) = 0 ->
  fqtree B L (am_after_brk st true k bail) Post.
Proof.
  intros ROOM INV AF LF HI QT0 HK. pose proof QT0 as (Q & NC & GB & GEO). unfold am_after_brk.
  destruct (Z.eqb_spec (c_avail_meta_area_count (ctx st)) 0) as [HC|HC].
  - (* [comment removed for export] *)
    destruct (am_bytes X st L BL LS 0 INV Q) as (A1 & A2 & A3 & A4).
    destruct (nm_n X st L BL LS INV) as [En N2].
    pose proof (div101_mono (ncarved st0) (NCAP P) ltac:(pose proof (ncarved_nonneg st0); pose proof (aq_carved _ _ _ HAQ0); lia)) as DM.
    assert (LEN : mmap_len (Z.shiftl 2 (c_meta_alloc_shift (s_ctx st)) * PGSZ) = Z.shiftl 2 (c_meta_alloc_shift (s_ctx st)) * PGSZ).
    { apply mmap_len_of_aligned; [unfold PGSZ; lia| unfold PGSZ; apply Z_mod_mult]. }
    assert (MAIN : gm L + BB L + Z.shiftl 2 (c_meta_alloc_shift (s_ctx st)) * PGSZ <= B).
    { rewrite En in *. rewrite Z.pow_add_r in * by (try lia; pose proof (proj1 (ir_shift _ _ _ (proj1 INV))); lia). change (2 ^ 1) with 2 in *.
      rewrite NC, GB in *.
      destruct (Z.ltb_spec (c_meta_alloc_shift (s_ctx st)) 1) as [S0|S1].
      - assert (E0 : c_meta_alloc_shift (s_ctx st) = 0) by (pose proof (proj1 (ir_shift _ _ _ (proj1 INV))); lia). rewrite E0 in *. cbn in *. unfold PGSZ in *. lia.
      - pose proof (exhausted_shift X st L 0 (proj1 INV) Q (ltac:(unfold ctx in HC; exact HC)) HK ltac:(lia) S1) as EX. rewrite NC in EX.
        set (t := 2 ^ c_meta_alloc_shift (s_ctx st)) in *.
        assert (TQ : t - 1 <= ncarved st0 / 101) by (apply Z.div_le_lower_bound; lia).
        unfold PGSZ in *. lia. }
    pose proof (proj2 (nm_n X st L BL LS INV)) as N2'.
    pose proof (gm_BB_nonneg X st L BL LS INV) as GB0.
    apply fqtree_vis; [reflexivity| reflexivity| exact (nm_event_pre X st L BL LS INV)| | | |].
    + (* [comment removed for export] *)
      intros z Hz. unfold event_post. change (Z.land (MAP_PRIVATE + MAP_ANON) MAP_FIXED =? 0) with true. change (PROT_NONE =? PROT_NONE) with true. cbn iota.
      destruct (is_err z); [unfold PGSZ in *; lia|]. rewrite gm_add_meta, BB_set_metas. unfold ctx. rewrite LEN. lia.
    + (* [comment removed for export] *)
      cbn [XB]. change (Z.land (MAP_PRIVATE + MAP_ANON) MAP_FIXED =? 0) with true. cbn iota. split.
      * unfold ctx. rewrite LEN. unfold PGSZ in *. lia.
      * apply (kcnt_KCAP X st L BL LS P 0 INV (SG_of _ AF GEO) (AQ_frame st0 st BL P (amf_groups _ _ AF) GEO ltac:(rewrite NC; lia) HAQ0) Q).
    + intros a Ha. unfold answer_ok in Ha. change (Z.land (MAP_PRIVATE + MAP_ANON) MAP_FIXED =? 0) with true in Ha. cbn [andb] in Ha.
      rewrite (mmap_answer_ok_eq X st L (proj1 INV)) in Ha. unfold ctx. rewrite Ha. cbn [negb].
      unfold event_post. change (Z.land (MAP_PRIVATE + MAP_ANON) MAP_FIXED =? 0) with true. change (PROT_NONE =? PROT_NONE) with true. cbn [andb].
      destruct (is_err a) eqn:NE.
      * eapply exit_none; [exact INV| exact AF| exact LF| exact QT0].
      * destruct (INVL_new_meta X st L BL LS a INV HC Ha NE) as (INV' & HC' & HI' & AF').
        destruct (QM_new_meta X st L BL LS a 0 INV HC HK Q ltac:(lia)) as (Q2 & NC2 & AP2 & GB2 & MB2 & BP2 & MR2 & SH2 & EX2).
        eapply am_finish_fq; [exact ROOM| exact INV'| exact (amf_trans _ _ _ AF AF')| destruct LF; constructor; assumption| exact HC'| rewrite HI'; exact HI| | reflexivity || exact HK].
        split; [exact Q2|]. split; [rewrite NC2; exact NC|]. split; [rewrite GB2; exact GB|]. intros m Hm. rewrite MR2. exact (GEO m Hm).
    + intros a Ha. unfold answer_ok in Ha. change (Z.land (MAP_PRIVATE + MAP_ANON) MAP_FIXED =? 0) with true in Ha. cbn [andb] in Ha.
      rewrite (mmap_answer_ok_eq X st L (proj1 INV)) in Ha. unfold ctx. rewrite Ha. exact I.
  - eapply am_finish_fq; [exact ROOM| exact INV| exact AF| exact LF| pose proof (proj1 (ir_cursor _ _ _ (proj1 INV))); unfold ctx in HC; lia| exact HI| exact QT0| exact HK].
Qed.

Lemma QT_am_init Y st d : QT Y st d -> QT Y (am_init st) d.
Proof.
  intros (Q & NC & GB & GEO). unfold am_init. destruct (c_init_done (ctx st) =? 0); [| split; auto].
  split; [| split; [exact NC| split; [exact GB| exact GEO]]].
  destruct Q as [Q1 Q2 Q3 Q4 Q5 Q6]; constructor; cbn -[apages ncarved]; auto.
  all: replace (apages (upd_ctx (fun c => set_init_done 1 (set_secret (s_secret st) c)) st)) with (apages st) by (apply apages_ext; reflexivity); exact Q2.
Qed.

Lemma QT_brk_dead Y st d : QT Y st d -> QT Y (upd_ctx (set_brk BrkDead) st) d.
Proof.
  intros (Q & NC & GB & GEO). split; [| split; [exact NC| split; [exact GB| exact GEO]]].
  destruct Q as [Q1 Q2 Q3 Q4 Q5 Q6]; constructor; cbn -[apages ncarved]; auto.
  all: replace (apages (upd_ctx (set_brk BrkDead) st)) with (apages st) by (apply apages_ext; reflexivity); exact Q2.
Qed.

Theorem alloc_meta_fq st L LS : INVL X st L BL LS -> AM_frame st0 st -> L_frame L0 L -> QT X st 0 ->
  c_free_meta_head (s_ctx st) = c_free_meta_head (s_ctx st0) ->
  fqtree B L (alloc_meta st k bail) Post.
Proof.
  intros INV1 AF0 LF QT1 EFH0.
  assert (EFH1 : c_free_meta_head (s_ctx (am_init st)) = c_free_meta_head (s_ctx st0)) by (unfold am_init; destruct (c_init_done (ctx st) =? 0); exact EFH0).
  destruct (INVL_am_init X st L BL LS INV1) as (INV & HI & AFi).
  pose proof (amf_trans _ _ _ AF0 AFi) as AF. pose proof (QT_am_init X st 0 QT1) as QT0. clear AF0 AFi INV1 QT1.
  unfold alloc_meta. fold (am_init st). set (s := am_init st) in *. clearbody s.
  pose proof INV as (IR & IA & IM & IL & IG & IS & ISH). pose proof QT0 as (Q & NC & GB & GEO).
  (* [comment removed for export] *)
  destruct (c_free_meta_head (ctx s)) as [m|] eqn:EFH.
  { pose proof (il_head _ _ IL LFree) as HH. cbn in HH. unfold ctx in EFH. rewrite EFH in HH.
    destruct (LS LFree) as [|m' rest] eqn:ELS; [discriminate|]. cbn in HH. inversion HH. subst m'.
    pose proof (INVL_dequeue X (xidle X (m :: x_idle X)) s L BL LS m LFree [] rest INV ltac:(rewrite ELS; reflexivity) ltac:(right; split; reflexivity)) as INV2.
    destruct (dequeue_frame LFree m s) as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & FC).
    destruct (am_reuse_q X s L BL LS m rest 0 INV ELS Q) as (Q2 & NC2 & RG2 & AP2 & DD).
    assert (AF2 : AM_frame st0 (dequeue LFree m s)).
    { eapply amf_trans; [exact AF|]. destruct FC. constructor; auto; try congruence.
      all: try (intros sc; change (active (dequeue LFree m s) sc) with (get_head (dequeue LFree m s) (LActive sc)); rewrite dequeue_head;
                destruct (decide (LActive sc = LFree)); [discriminate| reflexivity]).
      all: try (intros sc; unfold usage, ctx; rewrite cb_usage; reflexivity).
      all: try (intros rid r H _; rewrite F1; exact H).
      all: rewrite ?F3; lia. }
    assert (GEO2 : forall x, (exists b, hosts st0 b x) -> geom (MR (dequeue LFree m s) x) = geom (MR st0 x)).
    { intros x Hx. rewrite <- (GEO x Hx). apply geom_data. apply DD. }
    eapply KS; [exact INV2| | exact AF2| exact LF| | | | | exact GEO2].
    - intros Hin. apply (proj2 (im_idle _ _ _ IM m Hin)). exists LFree. rewrite ELS. left. reflexivity.
    - apply SINV_split. split; [exact (SG_of _ AF2 GEO2)| exact Q2].
    - apply (AQ_frame st0 _ BL P (amf_groups _ _ AF2) GEO2); [rewrite NC2, NC; exact (aq_carved _ _ _ HAQ0)| exact HAQ0].
    - rewrite NC2, NC. lia.
    - intros c. exact (gcnt_frame st0 _ c (amf_groups _ _ AF2) GEO2). }
  (* [comment removed for export] *)
  assert (ROOM : ncarved st0 + 1 <= NCAP P) by (apply ROOM0; rewrite <- EFH1; unfold ctx in EFH; exact EFH).
  destruct (Z.eqb_spec (c_avail_meta_count (ctx s)) 0) as [HAC|HAC]; cbn [negb].
  2:{ eapply am_take_fq; [exact ROOM| exact INV| exact AF| exact LF| pose proof (proj1 (ia_avail _ IA)); unfold ctx in HAC; lia| exact QT0]. }
  (* [comment removed for export] *)
  destruct (Z.eqb_spec (c_avail_meta_area_count (ctx s)) 0) as [HC|HC]; cbn [andb].
  2:{ eapply am_after_brk_fq; [exact ROOM| exact INV| exact AF| exact LF| exact HI| exact QT0| unfold ctx in HAC; exact HAC]. }
  pose proof (ir_brk _ _ _ IR) as IBK. unfold ctx. destruct (c_brk (s_ctx s)) as [| |rid off] eqn:EBRK; cbn [negb].
  - (* [comment removed for export] *)
    destruct IBK as [BP NB].
    assert (BR0 : ld_brkreg L = None).
    { destruct (ld_brkreg L) as [[b l]|] eqn:E; [| reflexivity]. exfalso.
      destruct (proj1 (ir_brkreg _ _ _ IR b l) E) as (q & rq & Hq & Kq & _). exact (NB q rq Hq Kq). }
    assert (BB0 : BB L = 0) by (unfold BB; rewrite BP, BR0; reflexivity).
    pose proof (bound_of s L LS 0 (2 * PGSZ) INV QT0 ltac:(unfold PGSZ; lia)) as BND. rewrite BB0 in BND. unfold PGSZ in BND.
    apply fqtree_vis; [reflexivity| reflexivity| left; auto| | exact I| |].
    { intros cur Hc. cbn [event_post Z.eqb]. rewrite gm_set_brkph. unfold BB. cbn. rewrite BR0. lia. }
    2:{ intros cur Hc. cbn in Hc. rewrite Hc. exact I. }
    intros cur Hc. cbn in Hc. rewrite Hc. cbn [negb]. cbn [event_post Z.eqb].
    set (L1 := KInv.set_brkph (BPQueried cur) L).
    set (base := round_up_pg cur). set (new := base + 2 * PGSZ).
    assert (NZ : (new =? 0) = false).
    { apply Z.eqb_neq. unfold new, base. pose proof (round_up_ge cur). unfold brk0_answer_ok in Hc.
      apply Bool.andb_true_iff in Hc as [Hc _]. apply Bool.andb_true_iff in Hc as [Hc _]. apply Z.ltb_lt in Hc. unfold PGSZ. lia. }
    apply fqtree_vis; [reflexivity| reflexivity| right; left; exists cur; split; reflexivity| | exact I| |].
    { intros z Hz. unfold event_post. rewrite NZ. unfold L1. cbn [KInv.ld_brk KInv.set_brkph].
      destruct (z =? new); unfold BB; cbn; rewrite ?BR0; unfold gm in BND |- *; cbn in BND |- *; unfold PGSZ in *; lia. }
    + intros r Hr. unfold answer_ok in Hr. rewrite NZ in Hr. unfold L1 in Hr. cbn [KInv.ld_brk KInv.set_brkph] in Hr.
      apply Bool.andb_true_iff in Hr as [Hb Hp]. rewrite Hb. cbn [negb].
      unfold event_post. rewrite NZ. unfold L1. cbn [KInv.ld_brk KInv.set_brkph].
      destruct (Z.eqb_spec r new) as [->|NE]; cbn [negb].
      * cbn [negb orb] in Hp.
        rewrite (lbrk_pages_ok_ext (KInv.set_brkph (BPQueried cur) L) L) in Hp by reflexivity.
        rewrite (brk_pages_ok_eq X s L IR) in Hp. fold base in Hp. rewrite Hp. cbn [negb].
        apply fqtree_vis; [reflexivity| reflexivity| right; exists cur; cbn; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; reflexivity| | exact I| |].
        { intros z Hz. unfold event_post. change (Z.land (MAP_PRIVATE + MAP_ANON + MAP_FIXED) MAP_FIXED =? 0) with false. cbn [andb].
          unfold BB, gm in BND |- *. cbn in BND |- *. unfold PGSZ in *. lia. }
        -- intros rg Hg. unfold answer_ok in Hg. change (Z.land (MAP_PRIVATE + MAP_ANON + MAP_FIXED) MAP_FIXED =? 0) with false in Hg. cbn [andb] in Hg.
           fold base in Hg. rewrite Hg. cbn [negb]. unfold event_post. change (Z.land (MAP_PRIVATE + MAP_ANON + MAP_FIXED) MAP_FIXED =? 0) with false. cbn [andb].
           set (st1 := new_region RKBrk base (2 * PGSZ) s). destruct st1 as [s1 rid] eqn:ES1.
           assert (Erid : rid = s_next_rid s) by (unfold st1, new_region in ES1; inversion ES1; reflexivity).
           assert (Es1 : s1 = fst (new_region RKBrk base (2 * PGSZ) s)) by (unfold st1 in ES1; rewrite <- ES1 || idtac; unfold new_region in *; inversion ES1; reflexivity).
           subst rid s1.
           unfold am_after_brk, ctx. cbn [c_avail_meta_area_count s_ctx upd_ctx set_avail_meta_area_count set_avail_meta_areas set_brk Z.eqb].
           unfold am_finish, ctx. cbn [c_avail_meta_areas s_ctx upd_ctx set_avail_meta_area_count set_avail_meta_areas set_brk snd].
           change (PGSZ mod PGSZ =? 0) with true. cbn [negb].
           rewrite am_carve_eq.
           destruct (INVL_brk_first X s L BL LS cur INV EBRK HC ltac:(exact Hp) (KInv.set_brkph (BPGuard cur) (KInv.set_brkph (BPQueried cur) L)) ltac:(OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; reflexivity))
             as (INV' & G1 & G2 & G3 & G4 & G5 & G6 & AF').
           destruct (QM_brk_first X s L BL LS cur 0 INV EBRK HC HAC Q ltac:(lia)) as (Q3 & NC3 & AP3 & GB3 & MB3 & BP3 & MR3 & CK3 & _).
           eapply am_carve_fq; [exact ROOM| exact INV'| exact G1| exact G2| exact G3| exact G4| exact G5| rewrite G6; exact HI| exact (amf_trans _ _ _ AF AF')| | | exact CK3].
           ++ destruct LF; constructor; assumption.
           ++ split; [exact Q3|]. split; [rewrite NC3; exact NC|]. split; [rewrite GB3; exact GB|]. intros x Hx. rewrite MR3. exact (GEO x Hx).
        -- intros rg Hg. unfold answer_ok in Hg. change (Z.land (MAP_PRIVATE + MAP_ANON + MAP_FIXED) MAP_FIXED =? 0) with false in Hg. cbn [andb] in Hg.
           fold base in Hg. rewrite Hg. exact I.
      * destruct (INVL_brk_dead X s L (KInv.set_brkph BPDead (KInv.set_brkph (BPQueried cur) L)) BL LS INV eq_refl eq_refl eq_refl eq_refl eq_refl) as [INV' AF'].
        eapply am_after_brk_fq; [exact ROOM| exact INV'| exact (amf_trans _ _ _ AF AF')| destruct LF; constructor; assumption| cbn; exact HI| apply QT_brk_dead; exact QT0| cbn; exact HAC].
    + intros r Hr. unfold answer_ok in Hr. rewrite NZ in Hr. unfold L1 in Hr. cbn [KInv.ld_brk KInv.set_brkph] in Hr.
      apply Bool.andb_false_iff in Hr. destruct Hr as [Hb|Hp].
      * rewrite Hb. exact I.
      * destruct (brk_answer_ok cur new r); [| exact I]. cbn [negb].
        apply Bool.orb_false_iff in Hp as [Hn Hp]. apply Bool.negb_false_iff in Hn. rewrite Hn. cbn [negb].
        rewrite (lbrk_pages_ok_ext (KInv.set_brkph (BPQueried cur) L) L) in Hp by reflexivity.
        rewrite (brk_pages_ok_eq X s L IR) in Hp. fold base in Hp. rewrite Hp. exact I.
  - (* [comment removed for export] *) eapply am_after_brk_fq; [exact ROOM| exact INV| exact AF| exact LF| exact HI| exact QT0| exact HAC].
  - (* [comment removed for export] *)
    destruct IBK as [BP (r & Hr & K & Elen)].
    pose proof (bg_event_pre X s L BL LS rid off INV EBRK) as PRE.
    set (old := conc s (rid, off)) in *. set (new := old + PGSZ) in *.
    assert (NZ : (new =? 0) = false).
    { apply Z.eqb_neq. unfold new, old, conc, get_region. rewrite Hr. cbn [fst snd]. pose proof (ir_shape _ _ _ IR _ _ Hr) as (S1 & _ & S3 & _). unfold PGSZ. lia. }
    assert (BR : ld_brkreg L = Some (r_base r, off)).
    { apply (proj2 (ir_brkreg _ _ _ IR (r_base r) off)). exists rid, r. auto. }
    assert (Eold : old = r_base r + off) by (unfold old, conc, get_region; rewrite Hr; cbn [fst snd]; reflexivity).
    pose proof (bound_of s L LS 0 PGSZ INV QT0 ltac:(unfold PGSZ; lia)) as BND.
    apply fqtree_vis; [reflexivity| reflexivity| exact PRE| | exact I| |].
    { intros z Hz. unfold event_post. rewrite NZ, BP, BR.
      assert (BBL : BB L = off) by (unfold BB; rewrite BP, BR; reflexivity). rewrite BBL in BND.
      destruct (z =? new).
      - rewrite gm_set_brkreg. unfold BB. cbn [ld_brk ld_brkreg set_brkreg]. rewrite BP. unfold PGSZ in *. lia.
      - rewrite gm_set_brkph. unfold BB. cbn [ld_brk ld_brkreg set_brkph]. rewrite BR. unfold PGSZ in *. lia. }
    + intros z Hz. unfold answer_ok in Hz. rewrite NZ, BP, BR in Hz. rewrite <- Eold in Hz.
      apply Bool.andb_true_iff in Hz as [Hb Hp]. rewrite Hb. cbn [negb].
      unfold event_post. rewrite NZ, BP, BR.
      destruct (Z.eqb_spec z new) as [->|NE]; cbn [negb].
      * cbn [negb orb] in Hp. rewrite (brk_pages_ok_eq X s L IR) in Hp. rewrite Hp. cbn [negb].
        unfold am_after_brk, ctx. cbn [c_avail_meta_area_count s_ctx upd_ctx set_avail_meta_area_count set_avail_meta_areas set_brk Z.eqb].
        unfold am_finish, ctx. cbn [c_avail_meta_areas s_ctx upd_ctx set_avail_meta_area_count set_avail_meta_areas set_brk snd].
        destruct (bg_region X s L BL LS rid off INV EBRK) as (r' & _ & _ & _ & _ & _ & _ & _ & OM & _).
        rewrite (proj2 (Z.eqb_eq _ _) OM). cbn [negb].
        rewrite am_carve_eq.
        destruct (INVL_brk_grow X s L BL LS rid off INV EBRK HC ltac:(exact Hp)) as (INV' & G1 & G2 & G3 & G4 & G5 & G6 & AF').
        replace (conc s (rid, off) - off) with (r_base r) in INV' by (unfold conc, get_region; rewrite Hr; cbn [fst snd]; lia).
        destruct (QM_brk_grow X s L BL LS rid off 0 INV EBRK HC HAC Q ltac:(lia)) as (Q3 & NC3 & AP3 & GB3 & MB3 & BP3 & MR3 & CK3 & _).
        eapply am_carve_fq; [exact ROOM| exact INV'| exact G1| exact G2| exact G3| exact G4| exact G5| rewrite G6; exact HI| exact (amf_trans _ _ _ AF AF')| | | exact CK3].
        -- destruct LF; constructor; assumption.
        -- split; [exact Q3|]. split; [rewrite NC3; exact NC|]. split; [rewrite GB3; exact GB|]. intros x Hx. rewrite MR3. exact (GEO x Hx).
      * destruct (INVL_brk_dead X s L (KInv.set_brkph BPDead L) BL LS INV eq_refl eq_refl eq_refl eq_refl eq_refl) as [INV' AF'].
        eapply am_after_brk_fq; [exact ROOM| exact INV'| exact (amf_trans _ _ _ AF AF')| destruct LF; constructor; assumption| cbn; exact HI| apply QT_brk_dead; exact QT0| cbn; exact HAC].
    + intros z Hz. unfold answer_ok in Hz. rewrite NZ, BP, BR in Hz. rewrite <- Eold in Hz.
      apply Bool.andb_false_iff in Hz. destruct Hz as [Hb|Hp].
      * rewrite Hb. exact I.
      * destruct (brk_answer_ok old new z); [| exact I]. cbn [negb].
        apply Bool.orb_false_iff in Hp as [Hn Hp]. apply Bool.negb_false_iff in Hn. rewrite Hn. cbn [negb].
        rewrite (brk_pages_ok_eq X s L IR) in Hp. rewrite Hp. exact I.
Qed.
End AMQ.

End LBCEIL.
End LB_Wjp3.

From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require LB_XferF.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require LB_AG.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require LB_AG LB_StmtA LB_WFree.

Module LB_WSlot.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool Lia Permutation FinFun.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase State Specs.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Decode.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require STree Malloc Mall7vg KInv KLink.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require MI_List.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require MI_Inv MI_Kit MI_Arith MI_List MI_Geom MI_Ext.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require MI_Pres2.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require MI_S421.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require MI_Pres2.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require MI_Pres2.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require MI_Pres4.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require MI_Pres4 MI_Ws22.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require MI_W2ig.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require MI_W2ig MI_W3do.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require MI_WTry2.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require MI_WTry2 MI_Wp9i MI_Cnt.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require MI_Ccma.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require MI_Ccma.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require MI_Ccma.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require MI_Ccma.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require MI_Ccma.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require LB_T80p LB_Inv LB_Sum LB_Bound LB_WNtf LB_XferF LB_Tree LB_QM.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require LB_XferF.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require LB_AG.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require LB_AG LB_WFree.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require LB_Ljn7.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require MI_WFree.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.STree OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.Malloc OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.Mall7vg OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.KInv OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.KLink OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_List.MI_Tree OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_Inv OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_Kit OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_Arith OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_List OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_Geom OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_Ext OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_Pres2.MI_Ext2 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_S421 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_Pres2.MI_Pres1 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_Pres2 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_Pres4.MI_Pres3 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_Pres4 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_Ws22 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_W2ig.MI_Lsjc OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_W2ig OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_W3do OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_WTry2.MI_WTry OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_WTry2 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_Wp9i OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_Cnt OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_Ccma.MI_TF2 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_Ccma.MI_Wm9j OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_Ccma.MI_WSlot OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_Ccma.MI_Wvdb OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_Ccma.MI_Wdy2 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.LB_T80p OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.LB_Inv OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.LB_Sum OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.LB_Bound OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.LB_WNtf OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.LB_XferF OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.LB_Tree OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.LB_QM OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.LB_Wazc.LB_Wjp3 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.LB_XferF.LB_WTry OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.LB_AG.LB_Cnt OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.LB_AG OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.LB_WFree OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.LB_Wazc.LB_KCnt OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.LB_Ljn7 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_WFree.LB_Dead.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Ceiling.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require AndN.   (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
(* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac Stdlib.micromega.Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_noeuclid ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_post_hook.
(* [comment removed for export] *)
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Section LBCEIL.
Context {Clg : Ceiling}.  (* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition QPOST (P : Z -> Z) (idle : list aptr) (BL : list blk) (st : mstate) : Prop :=
  SG st BL /\ QM (X_as idle) st 0 /\ AQ st BL P.

Lemma QPOST_SINV P idle BL st X : x_idle X = idle -> QPOST P idle BL st -> SINV X st BL /\ AQ st BL P.
Proof. intros E (S & Q & A). split; [| exact A]. apply SINV_split. split; [exact S|]. apply (QM_X (X_as idle)); [rewrite E; reflexivity| exact Q]. Qed.

Lemma SINV_QPOST P idle BL st X : x_idle X = idle -> SINV X st BL -> AQ st BL P -> QPOST P idle BL st.
Proof. intros E S A. apply SINV_split in S as [S Q]. split; [exact S|]. split; [| exact A]. apply (QM_X X); [cbn; symmetry; exact E| exact Q]. Qed.

(* [comment removed for export] *)
Record qsame (st st1 : mstate) : Prop := mkQS {
  qs_groups : s_groups st1 = s_groups st;
  qs_slots : s_slots st1 = s_slots st;
  qs_metas : s_metas st1 = s_metas st;
  qs_regions : s_regions st1 = s_regions st;
  qs_amc : c_avail_meta_count (s_ctx st1) = c_avail_meta_count (s_ctx st);
  qs_amas : c_avail_meta_areas (s_ctx st1) = c_avail_meta_areas (s_ctx st);
  qs_shift : c_meta_alloc_shift (s_ctx st1) = c_meta_alloc_shift (s_ctx st) }.

Lemma QPOST_qsame P idle BL st st1 X L LS : INVL X st L BL LS -> qsame st st1 -> QPOST P idle BL st -> QPOST P idle BL st1.
Proof.
  intros INV [EG ES EM ER EC EA EH] (S & Q & A).
  assert (MRx : forall x, MR st1 x = MR st x) by (intros x; unfold MR, get_meta_rec; rewrite EM; reflexivity).
  assert (GEO : forall x, (exists b, hosts st b x) -> geom (MR st1 x) = geom (MR st x)) by (intros x _; rewrite MRx; reflexivity).
  split; [| split].
  - apply (SG_frame st st1 BL EG ES GEO); [| exact S]. intros s x i Hs. exact (proj1 (is_valid _ _ _ (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 INV)))))) _ _ _ Hs)).
  - destruct Q as [Q1 Q2 Q3 Q4 Q5 Q6]. constructor; rewrite ?EM, ?ER, ?EC, ?EH, ?(ncarved_ext st st1 EM), ?(apages_ext st st1 ER EA); auto.
  - apply (AQ_frame st st1 BL P EG GEO); [rewrite (ncarved_ext st st1 EM); exact (aq_carved _ _ _ A)| exact A].
Qed.

Lemma qsame_step_seq st : qsame st (step_seq st).
Proof. unfold step_seq. destruct (c_seq (ctx st) =? 255); constructor; reflexivity. Qed.
Lemma qsame_account_bounce sc st : qsame st (account_bounce sc st).
Proof. unfold account_bounce. destruct (sc_in_seq_range sc); [destruct (negb _ && _); [destruct (_ <? 100)|]|]; constructor; reflexivity. Qed.
Lemma qsame_trans a b c : qsame a b -> qsame b c -> qsame a c.
Proof. intros [A1 A2 A3 A4 A5 A6 A7] [B1 B2 B3 B4 B5 B6 B7]; constructor; congruence. Qed.

(* [comment removed for export] *)
Definition BLF (st0 st1 : mstate) (BL : list blk) : Prop :=
  forall k, In k BL -> slotcls st1 (bslot k) = slotcls st0 (bslot k).
(* [comment removed for export] *)
Lemma BLF_trans a b c BL : BLF a b BL -> BLF b c BL -> BLF a c BL.
Proof. intros H1 H2 k Hk. rewrite (H2 k Hk). exact (H1 k Hk). Qed.
Lemma scl_geo X st st1 L BL LS : INVL X st L BL LS -> s_slots st1 = s_slots st ->
  (forall m, (exists b, hosts st b m) -> geom (MR st1 m) = geom (MR st m)) -> forall s, slotcls st1 s = slotcls st s.
Proof.
  intros INV ES GEO s. unfold slotcls, cls. rewrite ES. destruct (s_slots st !! s) as [[m i]|] eqn:E; [| reflexivity].
  pose proof (GEO m (proj1 (is_valid _ _ _ (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 INV)))))) _ _ _ E))) as G.
  unfold geom in G. inversion G. reflexivity.
Qed.
Lemma BLF_geo X st st1 L BL LS : INVL X st L BL LS -> s_slots st1 = s_slots st ->
  (forall m, (exists b, hosts st b m) -> geom (MR st1 m) = geom (MR st m)) -> BLF st st1 BL.
Proof. intros INV ES GEO k _. exact (scl_geo X st st1 L BL LS INV ES GEO (bslot k)). Qed.
Lemma BLF_qsame st st1 BL : qsame st st1 -> BLF st st1 BL.
Proof. intros [_ ES EM _ _ _ _] k _. unfold slotcls, cls, MR, get_meta_rec. rewrite ES, EM. reflexivity. Qed.
Lemma BLF_ffr X2 st1 st2 L2 BL LS2 : INVL X2 st2 L2 BL LS2 -> FFR st1 st2 -> BLF st1 st2 BL.
Proof. intros INV F k Hk. exact (x_slotcls X2 st1 st2 L2 BL LS2 INV F k Hk). Qed.
Lemma BLF_old X st0 st1 L BL LS : INVL X st0 L BL LS -> (forall s, s_slots st0 !! s <> None -> slotcls st1 s = slotcls st0 s) -> BLF st0 st1 BL.
Proof.
  intros INV H k Hk. apply H. destruct (is_blocks _ _ _ (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 INV)))))) k Hk) as (x & i & Hs & _). rewrite Hs. discriminate.
Qed.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma free_idle_q idle m st L BL LS P : INVL (X_as (m :: idle)) st L BL LS -> ~ In m idle ->
  QPOST P (m :: idle) BL st -> QPOST P idle BL (fm_st st m).
Proof.
  intros INV NIm (S & Q & A).
  pose proof INV as (IR & IA & IM & IL & IG & IS & ISH).
  pose proof (fi_metas idle m st L BL LS INV) as Hm.
  assert (PUT : put_meta m meta0 st = st) by (apply (fi_put idle m st L BL LS INV)).
  unfold fm_st. rewrite PUT.
  destruct (queue_frame LFree m st) as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & FC).
  pose proof (queue_data LFree m st) as DD.
  assert (GEO : forall x, (exists b, hosts st b x) -> geom (MR (queue_st LFree m st) x) = geom (MR st x)) by (intros x _; apply geom_data; apply DD).
  (* [comment removed for export] *)
  assert (DOM : forall x, s_metas (queue_st LFree m st) !! x <> None <-> s_metas st !! x <> None).
  { intros x. split; [| apply queue_keys_mono]. intros Hx. destruct (queue_keys LFree m st x Hx) as [H'|[->|[Hh|(a & Hh & Hpv)]]]; [exact H'| rewrite Hm; discriminate| |].
    - apply (listed_present _ _ _ _ _ INV x LFree). exact (head_listed _ _ _ _ _ INV LFree x Hh).
    - apply (listed_present _ _ _ _ _ INV x LFree). exact (prev_listed _ _ _ _ _ INV LFree a x (head_listed _ _ _ _ _ INV LFree a Hh) Hpv). }
  pose proof (ncarved_dom st (queue_st LFree m st) DOM) as NC.
  split; [| split].
  - apply (SG_frame st _ BL F5 F6 GEO); [| exact S]. intros s x i Hs. exact (proj1 (is_valid _ _ _ IS _ _ _ Hs)).
  - destruct Q as [Q1 Q2 Q3 Q4 Q5 Q6]. destruct FC. constructor; rewrite ?F1, ?NC; auto.
    + intros x mr Hx Z0.
      assert (Px : s_metas st !! x <> None) by (apply DOM; rewrite Hx; discriminate).
      destruct (s_metas st !! x) as [mr0|] eqn:E0; [| congruence].
      pose proof (DD x) as Dx. rewrite (MR_of_lookup _ _ _ Hx), (MR_of_lookup _ _ _ E0) in Dx. apply data_of_eq in Dx as (Em & _).
      pose proof (queue_next LFree m st x) as QN. rewrite (MR_of_lookup _ _ _ Hx) in QN.
      destruct (aptr_eq_dec x m) as [->|NE].
      * left. rewrite QN. cbn [get_head]. destruct (c_free_meta_head (ctx st)) as [a|] eqn:HH.
        -- destruct (aptr_eqb_spec m a) as [->|NEa].
           { exfalso. apply (proj2 (im_idle _ _ _ IM a ltac:(left; reflexivity))). exists LFree. exact (head_listed _ _ _ _ _ INV LFree a HH). }
           destruct (optr_eqb _ _); [discriminate|]. rewrite aptr_eqb_refl. discriminate.
        -- rewrite aptr_eqb_refl. discriminate.
      * destruct (Q1 x mr0 E0 ltac:(congruence)) as [N0|I0].
        -- left. rewrite QN. cbn [get_head]. destruct (c_free_meta_head (ctx st)) as [a|].
           ++ destruct (aptr_eqb_spec x a) as [->|NEa].
              ** destruct (optr_eqb _ _); [discriminate|]. destruct (aptr_eqb_spec a m); [congruence|]. rewrite (MR_of_lookup _ _ _ E0). exact N0.
              ** destruct (optr_eqb _ _); [discriminate|]. destruct (aptr_eqb_spec x m); [congruence|]. rewrite (MR_of_lookup _ _ _ E0). exact N0.
           ++ destruct (aptr_eqb_spec x m); [congruence|]. rewrite (MR_of_lookup _ _ _ E0). exact N0.
        -- destruct I0 as [->|I1]; [congruence| right; exact I1].
    + rewrite (apages_ext st (queue_st LFree m st) F1 cb_amas), cb_amc. exact Q2.
    + rewrite cb_shift. exact Q4.
    + rewrite cb_shift. exact Q6.
  - apply (AQ_frame st _ BL P F5 GEO); [rewrite NC; exact (aq_carved _ _ _ A)| exact A].
Qed.

Lemma BLF_free_idle idle m st L BL LS : INVL (X_as (m :: idle)) st L BL LS -> BLF st (fm_st st m) BL.
Proof.
  intros INV. apply (BLF_geo _ st _ L BL LS INV).
  - unfold fm_st. rewrite (fi_put idle m st L BL LS INV). destruct (queue_frame LFree m st) as (_ & _ & _ & _ & _ & F6 & _). exact F6.
  - intros x _. apply geom_data. unfold fm_st. rewrite (fi_put idle m st L BL LS INV). apply queue_data.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma state_bytes_B X st L BL LS P B : INVL X st L BL LS -> x_pend X = None -> x_orph X = None ->
  SINV X st BL -> AQ st BL P -> PHI P + R63 BL <= B + 3 * PGSZ -> gm L + BB L <= B.
Proof.
  intros INV HP HO SI HAQ HB. pose proof (ledger_bound X st L BL LS INV) as L1. pose proof (regions_bound X st L BL LS P INV SI HAQ HP) as R1.
  unfold ORPH in R1. rewrite HO in R1. unfold PGSZ in *. lia.
Qed.

Lemma group_bytes_B X st L BL LS P B : INVL X st L BL LS -> x_pend X = None -> x_orph X = None ->
  SINV X st BL -> AQ st BL P -> PHI P + R63 BL <= B + 3 * PGSZ -> group_bytes st + PGSZ * (5 * NCAP P / 101 + 8) <= B.
Proof.
  intros INV HP HO SI HAQ HB. pose proof (group_bytes_bound X st L BL LS P INV SI HAQ HP) as R1.
  unfold ORPH in R1. rewrite HO in R1. unfold PGSZ in *. lia.
Qed.

(* [comment removed for export] *)
Definition AGK (T : Type) (P : Z -> Z) (B : Z) (Post : mled -> T -> Prop) (idle : list aptr) (sc req : Z) (st0 : mstate) (L0 : mled) (BL : list blk)
  (k : mstate -> optr -> M T) : Prop :=
  forall st2 go L2 LS2, AG_POST idle sc req st0 L0 BL st2 go L2 LS2 -> QPOST P idle BL st2 ->
  (forall c, 0 <= c < sc -> gcnt st2 c <= gcnt st0 c) -> BLF st0 st2 BL -> fqtree B L2 (k st2 go) Post.

(* [comment removed for export] *)
Lemma QPOST_new_group_region P idle BL st X L LS a len :
  INVL X st L BL LS -> QPOST P idle BL st -> QPOST P idle BL (fst (new_region RKGroup a len st)).
Proof.
  intros INV (S & Q & A). pose proof (nm_fresh _ _ _ _ _ INV) as FR.
  set (st2 := fst (new_region RKGroup a len st)).
  assert (MRx : forall x, MR st2 x = MR st x) by (intros; reflexivity).
  assert (GEO : forall x, (exists b, hosts st b x) -> geom (MR st2 x) = geom (MR st x)) by (intros; reflexivity).
  assert (RG : s_regions st2 = <[s_next_rid st := mkRegion RKGroup a len]> (s_regions st)) by reflexivity.
  assert (AP : apages st2 = apages st).
  { rewrite !apages_msum, RG, (msum_insert _ _ _ _ FR). unfold apF at 1. cbn [fst snd is_metakind_b r_kind]. rewrite Z.add_0_l.
    apply msum_ext. intros q rq Hq. unfold apF, frontier. cbn. reflexivity. }
  split; [| split].
  - apply (SG_frame st st2 BL eq_refl eq_refl GEO); [| exact S]. intros s x i Hs. exact (proj1 (is_valid _ _ _ (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 INV)))))) _ _ _ Hs)).
  - destruct Q as [Q1 Q2 Q3 Q4 Q5 Q6]. constructor; try exact Q1; rewrite ?RG, ?AP; change (ncarved st2) with (ncarved st); change (s_ctx st2) with (s_ctx st); auto.
    + intros q rq Hq K. destruct (N.eq_dec q (s_next_rid st)) as [->|NE]; [rewrite lookup_insert_eq in Hq; inversion Hq; subst; cbn in K; discriminate|].
      rewrite lookup_insert_ne in Hq by congruence. exact (Q3 q rq Hq K).
    + intros q rq Hq K. destruct (N.eq_dec q (s_next_rid st)) as [->|NE]; [rewrite lookup_insert_eq in Hq; inversion Hq; subst; cbn in K; discriminate|].
      rewrite lookup_insert_ne in Hq by congruence. exact (Q4 q rq Hq K).
    + intros q1 q2 r1 r2 H1 H2 K1 K2 NE.
      destruct (N.eq_dec q1 (s_next_rid st)) as [->|NE1]; [rewrite lookup_insert_eq in H1; inversion H1; subst; cbn in K1; discriminate|].
      destruct (N.eq_dec q2 (s_next_rid st)) as [->|NE2]; [rewrite lookup_insert_eq in H2; inversion H2; subst; cbn in K2; discriminate|].
      rewrite lookup_insert_ne in H1 by congruence. rewrite lookup_insert_ne in H2 by congruence. exact (Q5 _ _ _ _ H1 H2 K1 K2 NE).
  - apply (AQ_frame st st2 BL P eq_refl GEO); [change (ncarved st2) with (ncarved st); exact (aq_carved _ _ _ A)| exact A].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section MMAP_BRANCHQ.
Variables (T : Type) (idle : list aptr) (st0 st1 : mstate) (L0 L1 : mled) (BL : list blk) (LS1 : lhead -> list aptr) (P : Z -> Z) (B : Z).
Variables (m : aptr) (sc req cnt needed : Z) (k : mstate -> optr -> M T) (bail : M T) (Post : mled -> T -> Prop).
Hypothesis INV1 : INVL (X_as (m :: idle)) st1 L1 BL LS1.
Hypothesis NIm : ~ In m idle.
Hypothesis TF1 : TF0 st1.
Hypothesis Hsc : 0 <= sc < 48.
Hypothesis Hreq : 0 <= req.
Hypothesis Hfit : req + IB <= UNIT * size_class sc.
Hypothesis HA1 : forall sc', active st1 sc' = active st0 sc'.
Hypothesis HA0 : active st0 sc = None.
Hypothesis HL1 : ld_live L1 = ld_live L0.
Hypothesis HG1 : GP st0 st1.
Hypothesis GRP : grp_ok sc cnt needed = true.
Hypothesis RED : (cnt = 1 /\ needed = round_up_pg (req + IB + UNIT) /\ 28 <= sc) \/ (UNIT * size_class sc * cnt + UNIT <= needed).
Hypothesis QP1 : QPOST P (m :: idle) BL st1.
Hypothesis STD : cnt = cmax sc -> needed = std_len sc /\ std_nested sc = false.
Hypothesis NSTD : cnt <> cmax sc -> gcnt st1 sc < 128.
Hypothesis NUB : needed <= UNIT * size_class sc * cnt + 4111.
Hypothesis GLE1 : forall c, gcnt st1 c = gcnt st0 c.
Hypothesis BF1 : BLF st0 st1 BL.
Hypothesis HBP : PHI P + R63 BL <= B + 3 * PGSZ.
Hypothesis HK : AGK T P B Post idle sc req st0 L0 BL k.
Let st1' := step_seq (account_bounce sc st1).
Let MC := fun c => set_mmap_counter (u32 (c_mmap_counter c + 1)) c.
Let AI := let ai := (4096 - UNIT) / (UNIT * size_class sc) - 1 in let ai := if cnt - 1 <? ai then cnt - 1 else ai in if ai <? 0 then 0 else ai.

Lemma QP1' : QPOST P (m :: idle) BL st1'.
Proof. apply (QPOST_qsame P (m :: idle) BL st1 st1' _ L1 LS1 INV1); [| exact QP1]. eapply qsame_trans; [apply qsame_account_bounce| apply qsame_step_seq]. Qed.

(* [comment removed for export] *)
Lemma mmap_final a :
  let st1f := step_seq (account_bounce sc st1) in
  mmap_answer_ok (live_ranges st1f) needed a = true -> is_err a = false ->
  let st2 := fst (new_region RKGroup a needed st1f) in let rid := s_next_rid st1f in
  let stf := agt (upd_meta m (m_set_maplen (Z.shiftr needed 12)) (upd_ctx MC st2)) sc m (rid, 0) cnt AI in
  let mr' := agG sc (rid, 0) cnt AI (m_set_maplen (Z.shiftr needed 12) meta0) in
  INVL (mkX idle [] None None (Some m)) stf (KInv.set_groups ((a, needed) :: ld_groups L1) L1) BL LS1
  /\ TF0 stf /\ MR stf m = mr' /\ s_groups stf !! (rid, 0) = Some (mkGhdr (Some m) AI)
  /\ (forall sc0, active stf sc0 = active st0 sc0) /\ QPOST P idle BL stf
  /\ s_regions stf = s_regions st2 /\ s_secret st2 = s_secret st1 /\ (forall c, gcnt stf c = (if sc =? c then cnt else 0) + gcnt st1 c)
  /\ BLF st0 stf BL.
Proof.
  cbn zeta. intros Ha ER.
  destruct (st1'_facts idle st1 L1 BL LS1 m sc INV1 TF1) as (INV1' & SH1 & TK1 & ACT1 & TF1' & RG1 & SS1'). fold st1' in INV1', SH1, TK1, ACT1, TF1', RG1, SS1' |- *.
  pose proof (grp_ok_sound sc cnt needed GRP) as G. cbn zeta in G. destruct G as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11).
  set (st2 := fst (new_region RKGroup a needed st1')). set (rid := s_next_rid st1').
  pose proof (INVL_new_group_region (X_as (m :: idle)) st1' L1 BL LS1 a needed INV1' eq_refl Ha ER ltac:(unfold LEN_MAX; lia)) as INV2.
  fold rid st2 in INV2. cbn [xorph X_as x_idle x_zomb x_pend x_fresh] in INV2.
  assert (Hr : s_regions st2 !! rid = Some (mkRegion RKGroup a needed)) by (unfold st2; rewrite ng_lookup; fold rid; rewrite N.eqb_refl; reflexivity).
  assert (NS : s_shadow st2 !! rid = None) by (unfold st2, rid; change (s_shadow (fst (new_region RKGroup a needed st1'))) with (s_shadow st1'); exact (shadow_next_rid_none _ _ _ _ _ INV1')).
  assert (ACT2 : forall sc', active st2 sc' = active st0 sc') by (intros sc'; unfold st2; change (active (fst (new_region RKGroup a needed st1')) sc') with (active st1' sc'); rewrite ACT1; apply HA1).
  assert (EMP : LS1 (LActive sc) = []) by (apply (LS_empty_of _ _ _ _ _ _ INV2); rewrite ACT2; exact HA0).
  assert (TF2' : TF0 st2) by (apply (TF0_ctrl st1'); [reflexivity| reflexivity| exact TF1']).
  pose proof (clamp_ai (UNIT * size_class sc) cnt ltac:(lia)) as HAI. cbn zeta in HAI. fold AI in HAI.
  assert (HAI0 : sc = 0 -> AI = cnt - 1).
  { intros Hsc0. unfold AI. rewrite Hsc0. change (UNIT * size_class 0) with 16. change ((4096 - UNIT) / 16 - 1) with 254.
    replace (cnt - 1 <? 254) with true by (symmetry; apply Z.ltb_lt; lia). replace (cnt - 1 <? 0) with false by (symmetry; apply Z.ltb_ge; lia). reflexivity. }
  destruct (ag_top_ok idle st2 (KInv.set_groups ((a, needed) :: ld_groups L1) L1) BL LS1 m rid (mkRegion RKGroup a needed) sc cnt needed AI
              INV2 Hr eq_refl eq_refl NS GRP Hsc HAI HAI0 EMP TF2' NIm) as (INV' & TF' & MR' & GR' & ACT' & HD' & TK').
  change (upd_meta m (m_set_maplen (Z.shiftr needed 12)) (upd_ctx MC st2)) with (upd_meta m (m_set_maplen (Z.shiftr needed 12)) (upd_ctx MC st2)) in *.
  split; [exact INV'|]. split; [exact TF'|]. split; [exact MR'|]. split; [exact GR'|]. split; [intros sc0; rewrite ACT'; apply ACT2|].
  enough (QG : QPOST P idle BL (agt (upd_meta m (m_set_maplen (Z.shiftr needed 12)) (upd_ctx MC st2)) sc m (rid, 0) cnt AI)
              /\ (forall c, gcnt (agt (upd_meta m (m_set_maplen (Z.shiftr needed 12)) (upd_ctx MC st2)) sc m (rid, 0) cnt AI) c = (if sc =? c then cnt else 0) + gcnt st1 c)
              /\ BLF st0 (agt (upd_meta m (m_set_maplen (Z.shiftr needed 12)) (upd_ctx MC st2)) sc m (rid, 0) cnt AI) BL).
  { destruct QG as (QG1 & QG2 & QG3). split; [exact QG1|]. split; [rewrite agt_regions; reflexivity|]. split; [exact SS1'|]. split; [exact QG2| exact QG3]. }
  (* [comment removed for export] *)
  pose proof (top_facts rid sc cnt needed AI GRP Hsc) as TFX. cbn zeta in TFX.
  destruct TFX as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10 & F11 & Emr).
  destruct (QPOST_new_group_region P (m :: idle) BL st1' _ L1 LS1 a needed INV1' QP1') as (SG2 & Q2 & A2). fold st2 in SG2, Q2, A2.
  pose proof INV2 as (IR2 & IA2 & IM2 & IL2 & IG2 & IS2 & ISH2).
  assert (FR : s_regions st1' !! rid = None) by (unfold rid; exact (nm_fresh _ _ _ _ _ INV1')).
  assert (HpN : s_groups st2 !! (rid, 0) = None).
  { destruct (s_groups st2 !! (rid, 0)) as [h|] eqn:E; [| reflexivity]. exfalso.
    change (s_groups st2) with (s_groups st1') in E. destruct (ig_region _ _ _ (proj1 (proj2 (proj2 (proj2 (proj2 INV1'))))) _ _ E) as (r & Hr' & _). cbn in Hr'. rewrite FR in Hr'. discriminate. }
  assert (HsN : s_slots st2 !! (rid, 0) = None).
  { destruct (s_slots st2 !! (rid, 0)) as [[x i]|] eqn:E; [| reflexivity]. exfalso.
    change (s_slots st2) with (s_slots st1') in E. destruct (is_valid _ _ _ (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 INV1')))))) _ _ _ E) as ([b [aix Hb]] & _ & Es).
    destruct (ig_region _ _ _ (proj1 (proj2 (proj2 (proj2 (proj2 INV1'))))) _ _ Hb) as (r & Hr' & _).
    pose proof (hosts_mem _ _ _ (proj1 (proj2 (proj2 INV1'))) _ _ (ex_intro _ aix Hb)) as MM.
    unfold slot_start', gbase in Es. rewrite MM in Es. cbn in Es. assert (E1 : fst b = rid) by (inversion Es; reflexivity). rewrite E1, FR in Hr'. discriminate. }
  assert (NEEDED : Z.shiftr needed 12 * 4096 = needed) by (rewrite F10; apply round_up_pg_id; exact G2).
  assert (STRIDE : get_stride (agG sc (rid, 0) cnt AI (m_set_maplen (Z.shiftr needed 12) meta0)) = if (cnt - 1 =? 0) then Z.shiftr needed 12 * 4096 - UNIT else UNIT * size_class sc).
  { rewrite Emr. unfold get_stride. cbn -[Z.shiftr Z.mul Z.sub Z.eqb size_class]. replace (Z.shiftr needed 12 =? 0) with false by (symmetry; apply Z.eqb_neq; lia). rewrite andb_true_r. reflexivity. }
  pose proof (tab_basic_ok sc Hsc) as (_ & CM & _).
  set (stA := upd_meta m (m_set_maplen (Z.shiftr needed 12)) (upd_ctx MC st2)) in *.
  assert (LKm : forall x, x <> m -> s_metas stA !! x = s_metas st2 !! x) by (intros x NE; unfold stA; rewrite s_metas_upd_meta, lookup_insert_ne by congruence; reflexivity).
  assert (LKc : c_avail_meta_count (s_ctx stA) = c_avail_meta_count (s_ctx st2) /\ c_avail_meta_areas (s_ctx stA) = c_avail_meta_areas (s_ctx st2)
                /\ c_meta_alloc_shift (s_ctx stA) = c_meta_alloc_shift (s_ctx st2)) by (OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; reflexivity).
  assert (HmA : s_metas stA !! m <> None) by (unfold stA; rewrite s_metas_upd_meta, lookup_insert_eq; discriminate).
  assert (HmI : s_metas st2 !! m = Some meta0) by exact (proj1 (im_idle _ _ _ IM2 m ltac:(left; reflexivity))).
  assert (ROOM : gcnt st2 sc <= CAP P sc) by (apply (creation_room _ st2 _ BL LS1 P INV2 SG2 A2 sc Hsc eq_refl); rewrite ACT2; exact HA0).
  assert (NEWG : m_sizeclass (MR (agt stA sc m (rid, 0) cnt AI) m) = sc /\ m_last_idx (MR (agt stA sc m (rid, 0) cnt AI) m) = cnt - 1) by (rewrite MR', Emr; split; reflexivity).
  assert (QGm : m_maplen (MR (agt stA sc m (rid, 0) cnt AI) m) <> 0 -> m_maplen (MR (agt stA sc m (rid, 0) cnt AI) m) * 4096 <= cnt * S_ sc + 4111 /\ s_slots st2 !! (rid, 0) = None).
  { rewrite MR', Emr. cbn [m_maplen]. intros _. split; [| exact HsN]. unfold S_. rewrite NEEDED. lia. }
  assert (QGn : m_maplen (MR (agt stA sc m (rid, 0) cnt AI) m) = 0 -> exists g i, s_slots st2 !! (rid, 0) = Some (g, i) /\ m_sizeclass (MR st2 g) <= 23
                /\ (stdg (agt stA sc m (rid, 0) cnt AI) m = true -> m_sizeclass (MR st2 g) = bighost sc)).
  { rewrite MR', Emr. cbn [m_maplen]. intros Z0. exfalso. lia. }
  assert (SDc : stdg (agt stA sc m (rid, 0) cnt AI) m = true -> cnt = cmax sc).
  { unfold stdg, cls, cnt_of. rewrite MR', Emr. cbn -[Z.eqb Z.shiftr Z.mul Z.sub Z.add get_stride cmax S_ size_class agG m_set_maplen meta0].
    intros SD. apply andb_prop in SD as [SD1 _]. apply Z.eqb_eq in SD1. cbn in SD1. clear -SD1. lia. }
  assert (QGs : stdg (agt stA sc m (rid, 0) cnt AI) m = true -> (m_maplen (MR (agt stA sc m (rid, 0) cnt AI) m) = 0 <-> std_nested sc = true)
                /\ (m_maplen (MR (agt stA sc m (rid, 0) cnt AI) m) <> 0 -> m_maplen (MR (agt stA sc m (rid, 0) cnt AI) m) * 4096 = std_len sc)).
  { intros SD. destruct (STD (SDc SD)) as [EN SNF]. rewrite MR', Emr. cbn [m_maplen].
    split; [rewrite SNF; split; [intros; exfalso; lia| discriminate]| intros _; rewrite NEEDED; exact EN]. }
  assert (MS1 : s_metas st1' = s_metas st1 /\ s_groups st1' = s_groups st1).
  { unfold st1', step_seq, account_bounce. destruct (sc_in_seq_range sc); [destruct (negb _ && _); [destruct (_ <? 100)|]|]; destruct (c_seq _ =? 255); split; reflexivity. }
  assert (MS12 : s_metas st2 = s_metas st1 /\ s_groups st2 = s_groups st1) by exact MS1.
  assert (G12c : forall c, gcnt st2 c = gcnt st1 c).
  { intros c. destruct MS12 as [MS GS]. apply gcnt_frame; [exact GS|]. intros x _. unfold MR, get_meta_rec. rewrite MS. reflexivity. }
  pose proof (G12c sc) as G12.
  assert (QGsm : stdg (agt stA sc m (rid, 0) cnt AI) m = false -> gcnt st2 sc < 128).
  { intros SD. rewrite G12. apply NSTD. intros EC.
    unfold stdg, cls, cnt_of in SD. rewrite MR', Emr in SD. cbn -[Z.eqb Z.shiftr Z.mul Z.sub Z.add get_stride cmax S_ size_class agG m_set_maplen meta0] in SD.
    rewrite <- Emr, STRIDE in SD. replace (cnt - 1 =? 0) with false in SD by (symmetry; apply Z.eqb_neq; clear -EC CM; lia).
    replace (cnt - 1 + 1 =? cmax sc) with true in SD by (symmetry; apply Z.eqb_eq; clear -EC; lia). unfold S_ in SD. rewrite Z.eqb_refl in SD. discriminate. }
  destruct (agt_quant (xorph (X_as (m :: idle)) (Some rid)) (mkX idle [] None None (Some m)) st2 stA _ _ BL LS1 LS1 P sc m (rid, 0) cnt AI
              INV2 INV' eq_refl eq_refl LKm LKc HmA HmI HpN SG2 (QM_X (X_as (m :: idle)) (xorph (X_as (m :: idle)) (Some rid)) st2 0 eq_refl Q2) ltac:(intros x Hx; cbn in Hx |- *; destruct Hx as [Hx|Hx]; [left; symmetry; exact Hx| right; exact Hx]) A2 Hsc ROOM ltac:(lia) NEWG QGm QGn QGs QGsm)
    as (Qa & Qb & Qc).
  split; [split; [exact Qa|]; split; [exact (QM_X (mkX idle [] None None (Some m)) (X_as idle) _ 0 eq_refl Qb)| exact Qc]|].
  split.
  { intros c. rewrite (aq_gcnt (xorph (X_as (m :: idle)) (Some rid)) st2 stA _ BL LS1 sc m (rid, 0) cnt AI INV2 eq_refl LKm HmI HpN NEWG c).
    rewrite <- (G12c c). reflexivity. }
  (* [comment removed for export] *)
  eapply BLF_trans; [exact BF1|].
  assert (B12 : BLF st1 st2 BL).
  { intros kk _. unfold slotcls, cls, MR, get_meta_rec. rewrite (proj1 MS12). replace (s_slots st2) with (s_slots st1); [reflexivity|].
    unfold st2. change (s_slots (fst (new_region RKGroup a needed st1'))) with (s_slots st1').
    unfold st1', step_seq, account_bounce. destruct (sc_in_seq_range sc); [destruct (negb _ && _); [destruct (_ <? 100)|]|]; destruct (c_seq _ =? 255); reflexivity. }
  eapply BLF_trans; [exact B12|].
  apply (BLF_old _ st2 _ _ BL LS1 INV2).
  exact (aq_slotcls_old (xorph (X_as (m :: idle)) (Some rid)) (mkX idle [] None None (Some m)) st2 stA _ _ BL LS1 LS1 sc m (rid, 0) cnt AI
           INV2 INV' eq_refl LKm HmI HpN NEWG QGm QGn QGs QGsm).
Qed.

Theorem ag_mmap_fq :
  fqtree B L1 (SVis (EMmap 0 needed PROT_RW (MAP_PRIVATE + MAP_ANON)) (fun r =>
    if negb (mmap_answer_ok (live_ranges st1') needed r) then bad_answer bail
    else if is_err r then free_meta m st1' (fun st2 => k st2 None) bail
    else let '(st2, rid) := new_region RKGroup r needed st1' in
         ag_tail full_lay (upd_ctx MC (upd_meta m (m_set_maplen (Z.shiftr needed 12)) st2)) sc m (rid, 0) cnt AI k)) Post.
Proof.
  destruct (st1'_facts idle st1 L1 BL LS1 m sc INV1 TF1) as (INV1' & SH1 & TK1 & ACT1 & TF1' & RG1 & SS1'). fold st1' in INV1', SH1, TK1, ACT1, TF1', RG1, SS1'.
  pose proof (grp_ok_sound sc cnt needed GRP) as G. cbn zeta in G. destruct G as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11).
  pose proof QP1' as QP. destruct (QPOST_SINV P (m :: idle) BL st1' (X_as (m :: idle)) eq_refl QP) as [SI1' A1'].
  assert (MS1 : s_metas st1' = s_metas st1 /\ s_groups st1' = s_groups st1).
  { unfold st1', step_seq, account_bounce. destruct (sc_in_seq_range sc); [destruct (negb _ && _); [destruct (_ <? 100)|]|]; destruct (c_seq _ =? 255); split; reflexivity. }
  apply fqtree_vis; [reflexivity| reflexivity| | | |  |].
  - (* [comment removed for export] *) cbn. left. split; [exact (brk_quiet_of _ _ _ (proj1 INV1'))|]. split; [reflexivity|]. split; [reflexivity|].
    split; [right; reflexivity|]. unfold LEN_MAX. lia.
  - (* [comment removed for export] *)
    intros a Ha. cbn [answer_ok] in Ha. change (Z.land (MAP_PRIVATE + MAP_ANON) MAP_FIXED =? 0) with true in Ha. cbn [negb] in Ha.
    change (event_post L1 (EMmap 0 needed PROT_RW (MAP_PRIVATE + MAP_ANON)) a)
      with (if Z.land (MAP_PRIVATE + MAP_ANON) MAP_FIXED =? 0 then if is_err a then L1 else if PROT_RW =? PROT_NONE then KInv.set_metas ((a, needed, 0) :: ld_metas L1) L1 else KInv.set_groups ((a, needed) :: ld_groups L1) L1 else set_brkph BPLive (set_brkreg (Some (0, 2 * PGSZ)) L1)).
    change (Z.land (MAP_PRIVATE + MAP_ANON) MAP_FIXED =? 0) with true. change (PROT_RW =? PROT_NONE) with false. cbn iota.
    rewrite (mmap_answer_ok_eq _ _ _ (proj1 INV1')) in Ha.
    destruct (is_err a) eqn:ER.
    + exact (state_bytes_B (X_as (m :: idle)) st1' L1 BL LS1 P B INV1' eq_refl eq_refl SI1' A1' HBP).
    + destruct (mmap_final a Ha ER) as (INVf & _ & _ & _ & _ & QPf & _ & _ & _).
      destruct (QPOST_SINV P idle BL _ (mkX idle [] None None (Some m)) eq_refl QPf) as [SIf Af].
      exact (state_bytes_B _ _ _ BL LS1 P B INVf eq_refl eq_refl SIf Af HBP).
  - (* [comment removed for export] *)
    cbn [XB]. change (Z.land (MAP_PRIVATE + MAP_ANON) MAP_FIXED =? 0) with true. cbn iota.
    destruct QP as (SGq & Qq & Aq). split.
    + rewrite (mmap_len_of_aligned needed ltac:(lia) G2). pose proof (PHI_lower P (aq_P _ _ _ Aq)).
      pose proof (R63_nonneg BL) as R0.   (* [comment removed for export] *)
      unfold PGSZ in *. lia.
    + exact (kcnt_KCAP (X_as (m :: idle)) st1' L1 BL LS1 P 0 INV1' SGq Aq Qq).
  - intros a Ha. cbn [answer_ok] in Ha. change (Z.land (MAP_PRIVATE + MAP_ANON) MAP_FIXED =? 0) with true in Ha. cbn [negb] in Ha |- *.
    change (event_post L1 (EMmap 0 needed PROT_RW (MAP_PRIVATE + MAP_ANON)) a)
      with (if Z.land (MAP_PRIVATE + MAP_ANON) MAP_FIXED =? 0 then if is_err a then L1 else if PROT_RW =? PROT_NONE then KInv.set_metas ((a, needed, 0) :: ld_metas L1) L1 else KInv.set_groups ((a, needed) :: ld_groups L1) L1 else set_brkph BPLive (set_brkreg (Some (0, 2 * PGSZ)) L1)).
    change (Z.land (MAP_PRIVATE + MAP_ANON) MAP_FIXED =? 0) with true. change (PROT_RW =? PROT_NONE) with false. cbn iota.
    rewrite (mmap_answer_ok_eq _ _ _ (proj1 INV1')) in Ha. rewrite Ha. cbn [negb].
    destruct (is_err a) eqn:ER.
    + (* [comment removed for export] *)
      rewrite free_meta_eq.
      destruct (free_idle_ok idle m st1' L1 BL LS1 INV1' NIm) as (INV2 & F1 & F2 & F3 & F4 & F5 & F6 & F7 & _).
      eapply HK.
      * split; [intros sc' _; rewrite F7, ACT1; apply HA1|]. split; [exact HL1|].
        split.
        { eapply GP_trans; [exact HG1| apply GP_eq; [rewrite F5, RG1; reflexivity|]].
          unfold fm_st. destruct (queue_frame LFree m (put_meta m meta0 st1')) as (_ & _ & _ & _ & _ & _ & _ & Q8 & _). rewrite Q8. cbn. exact SS1'. }
        split; [exact INV2|]. exact (TF0_ctrl st1' _ F1 F2 TF1').
      * exact (free_idle_q idle m st1' L1 BL LS1 P INV1' NIm QP).
      * intros c Hc. rewrite <- GLE1. apply Z.eq_le_incl. apply gcnt_frame; [rewrite F3; exact (proj2 MS1)|].
        intros x _. transitivity (geom (MR st1' x)); [| unfold MR, get_meta_rec; rewrite (proj1 MS1); reflexivity].
        apply geom_data. unfold fm_st. rewrite (fi_put idle m st1' L1 BL LS1 INV1'). apply queue_data.
      * eapply BLF_trans; [exact BF1|]. eapply BLF_trans; [| exact (BLF_free_idle idle m st1' L1 BL LS1 INV1')].
        apply BLF_qsame. eapply qsame_trans; [apply qsame_account_bounce| apply qsame_step_seq].
    + (* [comment removed for export] *)
      destruct (new_region RKGroup a needed st1') as [st2 rid] eqn:EN.
      assert (Erid : rid = s_next_rid st1') by (unfold new_region in EN; inversion EN; reflexivity).
      assert (Est2 : st2 = fst (new_region RKGroup a needed st1')) by (rewrite EN; reflexivity).
      destruct (mmap_final a Ha ER) as (INV' & TF' & MR' & GR' & ACT' & QPf & RGf & SSf & GCf & BFf). rewrite <- Est2, <- Erid in *.
      rewrite ag_tail_eq.
      change (upd_ctx MC (upd_meta m (m_set_maplen (Z.shiftr needed 12)) st2)) with (upd_meta m (m_set_maplen (Z.shiftr needed 12)) (upd_ctx MC st2)).
      pose proof (top_facts rid sc cnt needed AI GRP Hsc) as TFX. cbn zeta in TFX.
      destruct TFX as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10 & F11 & Emr).
      rewrite Emr in MR', F4, F5, F7, F8, F9. rewrite <- MR' in F4, F5, F7, F8, F9.
      eapply HK; [| exact QPf| intros c Hc; rewrite GCf, <- GLE1; destruct (Z.eqb_spec sc c); lia| exact BFf].
      split; [intros sc' _; apply ACT'|]. split; [cbn; exact HL1|].
      split.
      { eapply GP_trans; [exact HG1|]. split.
        - intros q rq Hq Kq. rewrite RGf, Est2. apply (ng_keep _ _ _ _ _ _ _ INV1'). rewrite RG1. exact Hq.
        - transitivity (s_secret st2); [rewrite agt_secret; reflexivity|]. rewrite SSf. reflexivity. }
      exists (rid, 0), AI, (cnt - 1), (Z.shiftr needed 12).
      pose proof (clamp_ai (UNIT * size_class sc) cnt ltac:(lia)) as HAI. cbn zeta in HAI. fold AI in HAI.
      split; [exact GR'|]. split; [exact MR'|]. split; [exact HAI|]. split; [lia|].
      assert (STR : get_stride (MR (agt (upd_meta m (m_set_maplen (Z.shiftr needed 12)) (upd_ctx MC st2)) sc m (rid, 0) cnt AI) m)
                    = if (cnt - 1 =? 0) && negb (Z.shiftr needed 12 =? 0) then Z.shiftr needed 12 * 4096 - UNIT else UNIT * size_class sc).
      { rewrite MR'. unfold get_stride. cbn. reflexivity. }
      assert (NZ : (Z.shiftr needed 12 =? 0) = false) by (apply Z.eqb_neq; lia).
      rewrite NZ in STR. cbn [negb] in STR. rewrite andb_true_r in STR.
      assert (E12 : Z.shiftr needed 12 * 4096 = needed) by (rewrite F10; apply round_up_pg_id; exact G2).
      split; [| split; [| split; [| split; [exact INV'| apply TF0_TF2; exact TF']]]].
      * destruct RED as [(C1 & Nd & S28)|NR].
        -- rewrite STR. replace (cnt - 1 =? 0) with true by (symmetry; apply Z.eqb_eq; lia). rewrite E12, Nd.
           pose proof (proj1 (round_up_pg_spec (req + IB + UNIT))). unfold UNIT, IB in *. lia.
        -- rewrite STR. destruct (Z.eqb_spec (cnt - 1) 0) as [C1|C1]; [| lia]. rewrite E12. assert (C1' : cnt = 1) by lia. rewrite C1', Z.mul_1_r in NR. unfold UNIT, IB in *. lia.
      * intros S28. destruct RED as [(C1 & Nd & S28')|NR]; [lia|].
        rewrite STR in F5 |- *. destruct (Z.eqb_spec (cnt - 1) 0) as [C1|]; [| reflexivity].
        destruct F5 as [F5|]; [| lia]. rewrite E12 in F5 |- *. assert (cnt = 1) by lia. subst cnt. lia.
      * intros UNDER. rewrite STR in UNDER. destruct RED as [(C1 & Nd & S28)|NR].
        -- clear - HAI C1. lia.
        -- exfalso. destruct (Z.eqb_spec (cnt - 1) 0) as [C1|]; [| lia]. rewrite E12 in UNDER. assert (cnt = 1) by lia. subst cnt. lia.
  - intros a Ha. cbn [answer_ok] in Ha. change (Z.land (MAP_PRIVATE + MAP_ANON) MAP_FIXED =? 0) with true in Ha. cbn iota in Ha.
    rewrite (mmap_answer_ok_eq _ _ _ (proj1 INV1')) in Ha. rewrite Ha. exact I.
Qed.
End MMAP_BRANCHQ.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition REC_OKQ (T : Type) (rec : mstate -> Z -> Z -> (mstate -> Z -> M T) -> M T -> M T) (sc : Z) (P : Z -> Z) (B : Z) (Post : mled -> T -> Prop) : Prop :=
  forall j idle st L BL LS req (k : mstate -> Z -> M T) bail,
  sc < j < 48 ->
  INVL (X_as idle) st L BL LS -> TF0 st -> NoDup idle -> 0 <= req -> req + IB <= UNIT * size_class j ->
  QPOST P idle BL st -> zlen idle <= rank j -> PHI P + R63 BL <= B + 3 * PGSZ ->
  (forall st1 idx L1 LS1, SLOT_POST idle j req st L BL st1 idx L1 LS1 -> QPOST P idle BL st1 ->
     (forall c, 0 <= c < j -> gcnt st1 c <= gcnt st c) -> BLF st st1 BL -> fqtree B L1 (k st1 idx) Post) ->
  fqtree B L (rec st j req k bail) Post.

Section NEST_BRANCHQ.
Variables (T : Type) (rec : mstate -> Z -> Z -> (mstate -> Z -> M T) -> M T -> M T).
Variables (idle : list aptr) (st0 st1 : mstate) (L0 L1 : mled) (BL : list blk) (LS1 : lhead -> list aptr) (P : Z -> Z) (B : Z).
Variables (m : aptr) (sc req cnt : Z) (k : mstate -> optr -> M T) (bail : M T) (Post : mled -> T -> Prop).
Hypothesis REC : REC_OKQ T rec sc P B Post.
Hypothesis INV1 : INVL (X_as (m :: idle)) st1 L1 BL LS1.
Hypothesis NIm : ~ In m idle.
Hypothesis ND : NoDup idle.
Hypothesis TF1 : TF0 st1.
Hypothesis Hsc : 0 <= sc < 48.
Hypothesis Hreq : 0 <= req.
Hypothesis Hfit : req + IB <= UNIT * size_class sc.
Hypothesis HA1 : forall sc', active st1 sc' = active st0 sc'.
Hypothesis HA0 : active st0 sc = None.
Hypothesis HL1 : ld_live L1 = ld_live L0.
Hypothesis HG1 : GP st0 st1.
Hypothesis NEST : nest_ok sc cnt = true.
Hypothesis QP1 : QPOST P (m :: idle) BL st1.
Hypothesis NSTD : cnt <> cmax sc -> gcnt st1 sc < 128.
Hypothesis GLE1 : forall c, gcnt st1 c = gcnt st0 c.
Hypothesis BF1 : BLF st0 st1 BL.
Hypothesis RK : zlen idle + 1 <= rank (size_to_class (UNIT + cnt * (UNIT * size_class sc) - IB)).
Hypothesis HBP : PHI P + R63 BL <= B + 3 * PGSZ.
Hypothesis HK : AGK T P B Post idle sc req st0 L0 BL k.
Let size := UNIT * size_class sc.
Let j := size_to_class (UNIT + cnt * size - IB).

Theorem ag_nest_fq :
  fqtree B L1 (rec st1 j (UNIT + cnt * size - IB) (fun st2 idx =>
     if idx <? 0 then free_meta m st2 (fun st3 => k st3 None) bail
     else match active st2 j with
          | None => SVis (EUndef UBadPtr) (fun _ => bail)
          | Some g => ag_tail full_lay (upd_meta m (m_set_maplen 0) (nest_layout st2 g idx j size cnt)) sc m (slot_of st2 g idx) cnt (cnt - 1) k
          end) bail) Post.
Proof.
  pose proof (nest_ok_sound sc cnt NEST) as N0. cbn zeta in N0. fold size in N0. fold j in N0. destruct N0 as (N1 & N2 & N3 & N4 & N5 & N6).
  apply (REC j (m :: idle) st1 L1 BL LS1 (UNIT + cnt * size - IB) _ bail ltac:(lia) INV1 TF1).
  - apply NoDup_cons_2; [intros Hin; apply NIm; apply (proj1 (list_elem_of_In _ _)); exact Hin| exact ND].
  - exact N5.
  - lia.
  - exact QP1.
  - rewrite zlen_cons. fold size in RK. fold j in RK. lia.
  - exact HBP.
  - intros st2 idx L2 LS2 (ACT & LIVE & GP2 & RES) QP2 GLE2 BF2.
    destruct RES as [(-> & INV2 & TF2')|(g & bg & aig & Hidx & HAj & Hg & SCg & FIT & STR & INV2 & TF2')].
    + (* [comment removed for export] *)
      change (-1 <? 0) with true. cbn iota. rewrite free_meta_eq.
      destruct (free_idle_ok idle m st2 L2 BL LS2 INV2 NIm) as (INV3 & F1 & F2 & F3 & F4 & F5 & F6 & F7 & _).
      eapply HK.
      * split; [intros sc' Hs; rewrite F7, ACT by lia; apply HA1|]. split; [rewrite LIVE; exact HL1|].
        split.
        { eapply GP_trans; [exact HG1| eapply GP_trans; [exact GP2| apply GP_eq; [exact F5|]]].
          unfold fm_st. destruct (queue_frame LFree m (put_meta m meta0 st2)) as (_ & _ & _ & _ & _ & _ & _ & Q8 & _). rewrite Q8. reflexivity. }
        split; [exact INV3|]. exact (TF0_ctrl st2 _ F1 F2 TF2').
      * exact (free_idle_q idle m st2 L2 BL LS2 P INV2 NIm QP2).
      * intros c Hc. rewrite <- GLE1. etransitivity; [| apply (GLE2 c); lia]. apply Z.eq_le_incl. apply gcnt_frame; [exact F3|].
        intros x _. apply geom_data. unfold fm_st. rewrite (fi_put idle m st2 L2 BL LS2 INV2). apply queue_data.
      * eapply BLF_trans; [exact BF1|]. eapply BLF_trans; [exact BF2| exact (BLF_free_idle idle m st2 L2 BL LS2 INV2)].
    + replace (idx <? 0) with false by (symmetry; apply Z.ltb_ge; lia). rewrite HAj.
      assert (Hgh : hosts st2 bg g) by (exists aig; exact Hg).
      assert (Ep : slot_of st2 g idx = (fst bg, sstart (MR st2 g) idx)).
      { unfold slot_of. fold (MR st2 g). exact (slot_start'_eq _ _ _ (proj1 (proj2 (proj2 INV2))) _ _ idx Hgh). }
      rewrite Ep. rewrite ag_tail_eq.
      specialize (STR ltac:(lia)).
      assert (EMP : LS2 (LActive sc) = []) by (apply (LS_empty_of _ _ _ _ _ _ INV2); rewrite ACT by lia; rewrite HA1; exact HA0).
      destruct (ag_nested_ok idle st2 L2 BL LS2 m g bg aig idx sc cnt INV2 Hg Hidx SCg STR NEST Hsc EMP TF2' NIm)
        as (INV' & TF' & MR' & GR' & ACT' & HD' & TK').
      pose proof (nst_facts st2 g bg idx sc cnt NEST Hsc) as NF. cbn zeta in NF.
      destruct NF as (_ & _ & _ & _ & _ & _ & _ & Emr & Es).
      fold size in MR', GR', ACT', INV', TF', Emr, Es |- *. fold j in MR', GR', ACT', INV', TF' |- *.
      rewrite Emr in MR'. rewrite Emr in Es.
      (* [comment removed for export] *)
      set (p := (fst bg, sstart (MR st2 g) idx)) in *.
      set (stA := upd_meta m (m_set_maplen 0) (nest_layout st2 g idx j size cnt)) in *.
      pose proof (strip_nest_layout st2 g idx j size cnt) as SN.
      assert (LKg : s_groups stA = s_groups st2) by (unfold stA; rewrite s_groups_upd_meta || cbn; transitivity (s_groups (strip (nest_layout st2 g idx j size cnt))); [reflexivity|]; rewrite SN; reflexivity).
      assert (LKr : s_regions stA = s_regions st2) by (unfold stA; transitivity (s_regions (strip (nest_layout st2 g idx j size cnt))); [reflexivity|]; rewrite SN; reflexivity).
      assert (MSn : s_metas (nest_layout st2 g idx j size cnt) = s_metas st2) by (transitivity (s_metas (strip (nest_layout st2 g idx j size cnt))); [reflexivity|]; rewrite SN; reflexivity).
      assert (CXn : s_ctx (nest_layout st2 g idx j size cnt) = s_ctx st2) by (transitivity (s_ctx (strip (nest_layout st2 g idx j size cnt))); [reflexivity|]; rewrite SN; reflexivity).
      assert (LKm : forall x, x <> m -> s_metas stA !! x = s_metas st2 !! x) by (intros x NE; unfold stA; rewrite s_metas_upd_meta, lookup_insert_ne by congruence; exact (f_equal (fun t => t !! x) MSn) || (rewrite MSn; reflexivity)).
      assert (LKc : c_avail_meta_count (s_ctx stA) = c_avail_meta_count (s_ctx st2) /\ c_avail_meta_areas (s_ctx stA) = c_avail_meta_areas (s_ctx st2)
                    /\ c_meta_alloc_shift (s_ctx stA) = c_meta_alloc_shift (s_ctx st2)) by (unfold stA; rewrite s_ctx_upd_meta || cbn -[nest_layout]; rewrite CXn; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; reflexivity).
      assert (HmA : s_metas stA !! m <> None) by (unfold stA; rewrite s_metas_upd_meta, lookup_insert_eq; discriminate).
      pose proof INV2 as (IR2 & IA2 & IM2 & IL2 & IG2 & IS2 & ISH2).
      assert (HmI : s_metas st2 !! m = Some meta0) by exact (proj1 (im_idle _ _ _ IM2 m ltac:(left; reflexivity))).
      assert (Ep' : p = slot_start' (MR st2 g) idx) by (unfold p; symmetry; exact (slot_start'_eq _ _ _ IM2 _ _ idx Hgh)).
      assert (HpN : s_groups st2 !! p = None).
      { pose proof (is_part _ _ _ IS2 bg g aig idx Hg Hidx) as P5. cbn zeta in P5. rewrite <- Ep' in P5.
        destruct P5 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & NDE).
        destruct (s_groups st2 !! p) as [h|] eqn:E; [| reflexivity]. exfalso. apply NDE. split; [rewrite E; discriminate| reflexivity]. }
      assert (HsP : s_slots st2 !! p = Some (g, idx)) by (rewrite Ep'; exact (is_total _ _ _ IS2 bg g idx Hgh Hidx)).
      destruct QP2 as (SG2 & Q2 & A2).
      assert (ROOM : gcnt st2 sc <= CAP P sc) by (apply (creation_room _ st2 _ BL LS2 P INV2 SG2 A2 sc Hsc eq_refl); rewrite ACT by lia; rewrite HA1; exact HA0).
      assert (NEWG : m_sizeclass (MR (agt stA sc m p cnt (cnt - 1)) m) = sc /\ m_last_idx (MR (agt stA sc m p cnt (cnt - 1)) m) = cnt - 1) by (rewrite MR'; split; reflexivity).
      assert (SDc : stdg (agt stA sc m p cnt (cnt - 1)) m = (cnt =? cmax sc)).
      { unfold stdg, cls, cnt_of. rewrite MR'. cbn -[Z.eqb Z.mul Z.sub Z.add get_stride cmax S_ size_class]. rewrite Es. unfold size, S_. rewrite Z.eqb_refl, andb_true_r.
        replace (cnt - 1 + 1) with cnt by lia. reflexivity. }
      assert (BH : cnt = cmax sc -> std_nested sc = true /\ bighost sc = j).
      { intros EC. assert (SN2 : std_nested sc = true).
        { unfold std_nested, std_span, S_. apply Z.leb_le. rewrite <- EC. fold size.
          unfold UNIT, IB, PGSZ in N6 |- *. clear -N6. lia. }
        split; [exact SN2|]. unfold bighost. rewrite SN2. unfold std_span, S_, j. rewrite <- EC. fold size. f_equal. unfold UNIT. lia. }
      assert (QGm : m_maplen (MR (agt stA sc m p cnt (cnt - 1)) m) <> 0 -> m_maplen (MR (agt stA sc m p cnt (cnt - 1)) m) * 4096 <= cnt * S_ sc + 4111 /\ s_slots st2 !! p = None).
      { rewrite MR'. cbn [m_maplen]. intros Z0. exfalso. exact (Z0 eq_refl). }
      assert (QGn : m_maplen (MR (agt stA sc m p cnt (cnt - 1)) m) = 0 -> exists g0 i0, s_slots st2 !! p = Some (g0, i0) /\ m_sizeclass (MR st2 g0) <= 23
                    /\ (stdg (agt stA sc m p cnt (cnt - 1)) m = true -> m_sizeclass (MR st2 g0) = bighost sc)).
      { intros _. exists g, idx. split; [exact HsP|]. rewrite SCg. split; [lia|]. rewrite SDc. intros EC. apply Z.eqb_eq in EC. destruct (BH EC) as [_ E]. symmetry. exact E. }
      assert (QGs : stdg (agt stA sc m p cnt (cnt - 1)) m = true -> (m_maplen (MR (agt stA sc m p cnt (cnt - 1)) m) = 0 <-> std_nested sc = true)
                    /\ (m_maplen (MR (agt stA sc m p cnt (cnt - 1)) m) <> 0 -> m_maplen (MR (agt stA sc m p cnt (cnt - 1)) m) * 4096 = std_len sc)).
      { rewrite SDc. intros EC. apply Z.eqb_eq in EC. destruct (BH EC) as [SN2 _]. rewrite MR'. cbn [m_maplen]. rewrite SN2. split; [split; intros; reflexivity| intros Z0; exfalso; exact (Z0 eq_refl)]. }
      assert (QGsm : stdg (agt stA sc m p cnt (cnt - 1)) m = false -> gcnt st2 sc < 128).
      { rewrite SDc. intros EC. apply Z.eqb_neq in EC. pose proof (GLE2 sc ltac:(lia)). pose proof (NSTD EC). lia. }
      destruct (agt_quant (xpend (X_as (m :: idle)) (Some p)) (mkX idle [] None None (Some m)) st2 stA _ _ BL LS2 LS2 P sc m p cnt (cnt - 1)
                  INV2 INV' LKg LKr LKm LKc HmA HmI HpN SG2 (QM_X (X_as (m :: idle)) (xpend (X_as (m :: idle)) (Some p)) st2 0 eq_refl Q2)
                  ltac:(intros x Hx; cbn in Hx |- *; destruct Hx as [Hx|Hx]; [left; symmetry; exact Hx| right; exact Hx]) A2 Hsc ROOM ltac:(lia) NEWG QGm QGn QGs QGsm)
        as (Qa & Qb & Qc).
      eapply HK.
      * split; [intros sc' Hs; rewrite ACT', ACT by lia; apply HA1|]. split; [rewrite LIVE; exact HL1|].
        split.
        { eapply GP_trans; [exact HG1| eapply GP_trans; [exact GP2| apply GP_eq]].
          - rewrite agt_regions. exact LKr.
          - rewrite agt_secret. change (s_secret (nest_layout st2 g idx j size cnt) = s_secret st2).
            rewrite <- (s_secret_strip (nest_layout st2 g idx j size cnt)), SN. reflexivity. }
        exists p, (cnt - 1), (cnt - 1), 0.
        rewrite Z.sub_diag. split; [exact GR'|]. split; [exact MR'|]. split; [lia|]. split; [lia|].
        rewrite MR', Es. split; [unfold size; lia|]. split; [intros _; reflexivity|]. split; [unfold size; intros; lia|].
        split; [exact INV'| exact TF'].
      * split; [exact Qa|]. split; [exact (QM_X (mkX idle [] None None (Some m)) (X_as idle) _ 0 eq_refl Qb)| exact Qc].
      * intros c Hc. rewrite (aq_gcnt (xpend (X_as (m :: idle)) (Some p)) st2 stA _ BL LS2 sc m p cnt (cnt - 1) INV2 LKg LKm HmI HpN NEWG c).
        replace (sc =? c) with false by (symmetry; apply Z.eqb_neq; lia). rewrite <- GLE1. pose proof (GLE2 c ltac:(lia)). lia.
      * eapply BLF_trans; [exact BF1|]. eapply BLF_trans; [exact BF2|].
        apply (BLF_old _ st2 _ _ BL LS2 INV2).
        exact (aq_slotcls_old (xpend (X_as (m :: idle)) (Some p)) (mkX idle [] None None (Some m)) st2 stA _ _ BL LS2 LS2 sc m p cnt (cnt - 1)
                 INV2 INV' LKg LKm HmI HpN NEWG QGm QGn QGs QGsm).
Qed.
End NEST_BRANCHQ.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma ag_cnt1_ge128 sc u0 : 0 <= sc < 48 -> 128 <= u0 -> ag_cnt1 sc u0 = cmax sc.
Proof.
  intros Hsc Hu. unfold ag_cnt1. rewrite (cnt0_of_ge128 sc u0 Hsc Hu). pose proof (tab_basic_ok sc Hsc) as (_ & CM & _).
  replace (cmax sc =? 1) with false by (symmetry; apply Z.eqb_neq; lia). reflexivity.
Qed.

Lemma ag_cnt1_nstd sc u0 : 0 <= sc < 48 -> ag_cnt1 sc u0 <> cmax sc -> u0 < 128.
Proof. intros Hsc H. destruct (Z.lt_ge_cases u0 128) as [L|G]; [exact L|]. exfalso. apply H. apply ag_cnt1_ge128; assumption. Qed.

Definition cnt0_range_f (sc : Z) : bool := forallb (fun c => (1 <=? c) && (c <=? 32)) (cnt0_list sc).
Lemma cnt0_range_all : forallb cnt0_range_f classes = true.
Proof. vm_compute. reflexivity. Qed.
Lemma cnt0_range sc c : 0 <= sc < 48 -> In c (cnt0_list sc) -> 1 <= c <= 32.
Proof.
  intros Hsc Hc. pose proof (forallb_classes _ cnt0_range_all sc Hsc) as T. unfold cnt0_range_f in T. rewrite forallb_forall in T.
  specialize (T c Hc). apply andb_prop in T as [A B]. apply Z.leb_le in A. apply Z.leb_le in B. lia.
Qed.
Lemma ag_cnt1_range sc u0 : 0 <= sc < 48 -> 1 <= ag_cnt1 sc u0 <= 32.
Proof.
  intros Hsc. unfold ag_cnt1. pose proof (cnt0_range sc _ Hsc (cnt0_in sc u0)) as R.
  destruct (_ && _) eqn:E; [apply andb_prop in E as [E _]; apply Z.eqb_eq in E; lia| exact R].
Qed.

Lemma ag_cnt_facts sc req u0 u1 ns c3 n3 :
  0 <= sc < 48 -> 0 <= req -> req + IB <= UNIT * size_class sc -> u0 <= u1 ->
  PGSZ / 2 < UNIT * size_class sc * ag_cnt1 sc u0 + UNIT ->
  ag_cn3 sc req (ag_cnt2 sc (ag_cnt1 sc u0) u1 ns) u1 ns = (c3, n3) ->
  (c3 = cmax sc -> n3 = std_len sc /\ std_nested sc = false) /\ (c3 <> cmax sc -> u0 < 128) /\ n3 <= UNIT * size_class sc * c3 + 4111.
Proof.
  intros Hsc Hreq Hfit HU HB E. pose proof (tab_basic_ok sc Hsc) as (S16 & CM & _).
  set (c1 := ag_cnt1 sc u0) in *.
  assert (C2 : ag_cnt2 sc c1 u1 ns = c1 \/ (ag_cnt2 sc c1 u1 ns <= 5 /\ u1 < 4 * c1)).
  { unfold ag_cnt2. destruct (Z.ltb_spec u1 (4 * c1)); cbn [andb]; [| left; reflexivity]. destruct ns; cbn; [left; reflexivity|].
    destruct (adj_small sc (UNIT * size_class sc) c1) as [E1|LE]; [left; exact E1| right; split; [exact LE| assumption]]. }
  set (c2 := ag_cnt2 sc c1 u1 ns) in *.
  assert (C1R : c1 = cmax sc \/ u0 < 128) by (destruct (Z.eq_dec c1 (cmax sc)); [left; assumption| right; apply (ag_cnt1_nstd sc u0 Hsc); assumption]).
  assert (C1B : 1 <= c1 <= 32) by (unfold c1; apply ag_cnt1_range; exact Hsc).
  unfold ag_cn3 in E. cbn zeta in E.
  assert (RU : forall x, x <= round_up_pg x <= x + 4095) by (intros x; pose proof (round_up_pg_spec x); lia).
  destruct (negb ns && (c2 <=? 7)) eqn:E7.
  - destruct ((round_up_pg (req + IB + UNIT) <? UNIT * size_class sc + UNIT) || ((4 * PGSZ <=? round_up_pg (req + IB + UNIT)) && (u1 <? 2 * c2))).
    + inversion E; subst c3 n3. split; [intros E1; exfalso; lia|]. split.
      * intros _. apply andb_prop in E7 as [_ E7]. apply Z.leb_le in E7. destruct C2 as [E2|[LE LT]]; [| lia]. destruct C1R as [E1|L]; [| exact L]. exfalso. unfold c2 in E7. lia.
      * pose proof (RU (req + IB + UNIT)). unfold IB, UNIT in *. lia.
    + inversion E; subst c3 n3. apply andb_prop in E7 as [_ E7]. apply Z.leb_le in E7. split; [intros E1; exfalso; lia|]. split.
      * intros _. destruct C2 as [E2|[LE LT]]; [| lia]. destruct C1R as [E1|L]; [| exact L]. exfalso. unfold c2 in E7. lia.
      * pose proof (RU (UNIT * size_class sc * c2 + UNIT)). unfold UNIT in *. lia.
  - inversion E; subst c3 n3. split; [| split].
    + intros E2. assert (E1 : c1 = cmax sc) by (destruct C2 as [E0|[LE LT]]; lia).
      split; [unfold std_len, std_span, S_; rewrite E2; f_equal; lia|].
      unfold std_nested, std_span, S_. apply Z.leb_gt. rewrite <- E1. unfold c1 in HB |- *. lia.
    + intros NE. destruct C2 as [E0|[LE LT]]; [destruct C1R as [E1|L]; [exfalso; apply NE; lia| exact L]| lia].
    + pose proof (RU (UNIT * size_class sc * c2 + UNIT)). unfold UNIT in *. lia.
Qed.

Lemma gcnt_nonneg X st L BL LS c : INVL X st L BL LS -> 0 <= gcnt st c.
Proof.
  intros INV. rewrite gcnt_gmetas. apply zsum_map_nonneg. intros [m b] Hin. cbn. destruct (gfacts X st L BL LS INV m b Hin) as ([? ?] & _).
  destruct (_ =? _); lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section AGQ.
Variables (T : Type) (rec : mstate -> Z -> Z -> (mstate -> Z -> M T) -> M T -> M T) (sc : Z) (P : Z -> Z) (B : Z) (Post : mled -> T -> Prop).
Hypothesis REC : REC_OKQ T rec sc P B Post.

Theorem alloc_group_fq idle st L BL LS req (k : mstate -> optr -> M T) bail :
  INVL (X_as idle) st L BL LS -> TF0 st -> NoDup idle -> 0 <= sc < 48 -> 0 <= req -> req + IB <= UNIT * size_class sc ->
  active st sc = None -> QPOST P idle BL st -> zlen idle <= rank sc -> PHI P + R63 BL <= B + 3 * PGSZ ->
  AGK T P B Post idle sc req st L BL k ->
  fqtree B L (alloc_group T full_lay rec st sc req k bail) Post.
Proof.
  intros INV TF ND Hsc Hreq Hfit HA QP RK HBP HK. pose proof QP as (SGst & Qst & Ast). unfold alloc_group.
  destruct (QPOST_SINV P idle BL st (X_as idle) eq_refl QP) as [SIst _].
  pose proof (rank_range sc) as RR.
  eapply (alloc_meta_fq T BL P B Post _ bail (X_as idle) st L LS INV SGst Ast); [ | | | | exact INV| apply amf_refl| apply lf_refl| | reflexivity].
  - (* [comment removed for export] *)
    intros HFH. pose proof (ncarved_le_groups (X_as idle) st L BL LS INV 0 Qst HFH eq_refl) as NC.
    pose proof (ngroups_le (X_as idle) st L BL LS P INV SGst Ast) as NG0. cbn [x_idle X_as] in NC. unfold NCAP. lia.
  - (* [comment removed for export] *)
    exact (group_bytes_B (X_as idle) st L BL LS P B INV eq_refl eq_refl SIst Ast HBP).
  - (* [comment removed for export] *)
    intros st1 L1 LS1 INV1 AF LF SI1 A1 GC1 GEO1. cbn beta iota. eapply HK.
    + split; [intros sc' _; apply (amf_active _ _ AF)|]. split; [exact (lf_live _ _ LF)|]. split; [exact (GP_amf _ _ AF)|]. split; [exact INV1|].
      exact (TF0_ctrl st st1 (amf_shadow _ _ AF) (amf_tick _ _ AF) TF).
    + exact (SINV_QPOST P idle BL st1 (X_as idle) eq_refl SI1 A1).
    + intros c Hc. rewrite GC1. lia.
    + exact (BLF_geo _ st st1 L BL LS INV (amf_slots _ _ AF) GEO1).
  - (* [comment removed for export] *)
    intros st1 L1 LS1 m INV1 NIm AF LF SI1 A1 NC1 GC1 GEO1. cbn beta iota zeta.
    pose proof (BLF_geo _ st st1 L BL LS INV (amf_slots _ _ AF) GEO1) as BF1. cbn [xidle X_as x_idle x_zomb x_pend x_orph x_fresh] in INV1, NIm, SI1. change (mkX (m :: idle) [] None None None) with (X_as (m :: idle)) in INV1, SI1.
    change (if sc <? 9 then small_cnt_pick sc (usage st1 sc) else halve_big 8 (halve_even 8 (med_cnt (Z.land sc 3)) (usage st1 sc)) (UNIT * size_class sc))
      with (cnt0_of sc (usage st1 sc)).
    change (if (cnt0_of sc (usage st1 sc) =? 1) && (UNIT * size_class sc * cnt0_of sc (usage st1 sc) + UNIT <=? PGSZ / 2) then 2 else cnt0_of sc (usage st1 sc))
      with (ag_cnt1 sc (usage st1 sc)).
    change (lh_nest full_lay) with nest_layout.
    assert (HA1 : forall sc', active st1 sc' = active st sc') by (intros; apply (amf_active _ _ AF)).
    assert (TF1 : TF0 st1) by exact (TF0_ctrl st st1 (amf_shadow _ _ AF) (amf_tick _ _ AF) TF).
    pose proof (SINV_QPOST P (m :: idle) BL st1 (X_as (m :: idle)) eq_refl SI1 A1) as QP1.
    assert (U0 : usage st1 sc = gcnt st1 sc) by exact (ia_usage _ (proj1 (proj2 INV1)) sc Hsc).
    pose proof (ag_arith sc req (usage st1 sc)) as AR.
    set (c1 := ag_cnt1 sc (usage st1 sc)) in *.
    destruct (Z.ltb_spec (PGSZ / 2) (UNIT * size_class sc * c1 + UNIT)) as [HB|HB].
    + (* [comment removed for export] *)
      set (ns := is_bouncing sc st1).
      set (st1' := step_seq (account_bounce sc st1)).
      set (u1 := if Z.even sc && (sc <? 32) then usage st1 sc + usage st1' (sc + 1) else usage st1 sc).
      change (if (u1 <? 4 * c1) && negb ns
              then if (Z.land sc 3 =? 1) && (8 * PGSZ <? UNIT * size_class sc * c1) then 2
                   else if (Z.land sc 3 =? 2) && (4 * PGSZ <? UNIT * size_class sc * c1) then 3
                   else if (Z.land sc 3 =? 0) && (8 * PGSZ <? UNIT * size_class sc * c1) then 3
                   else if (Z.land sc 3 =? 0) && (2 * PGSZ <? UNIT * size_class sc * c1) then 5
                   else c1
              else c1) with (ag_cnt2 sc c1 u1 ns).
      set (c2 := ag_cnt2 sc c1 u1 ns).
      specialize (AR u1 ns).
      assert (HU : usage st1 sc <= u1).
      { unfold u1. destruct (Z.even sc && (sc <? 32)) eqn:E; [| lia].
        apply andb_prop in E as [_ E]. apply Z.ltb_lt in E.
        destruct (st1'_facts idle st1 L1 BL LS1 m sc INV1 TF1) as (INV1' & _). fold st1' in INV1'.
        rewrite (ia_usage _ (proj1 (proj2 INV1')) (sc + 1) ltac:(lia)). pose proof (gcnt_nonneg _ _ _ _ _ (sc + 1) INV1'). lia. }
      assert (GO : forall c3 n3, ag_cn3 sc req c2 u1 ns = (c3, n3) ->
        fqtree B L1 (SVis (EMmap 0 n3 PROT_RW (MAP_PRIVATE + MAP_ANON)) (fun r =>
          if negb (mmap_answer_ok (live_ranges st1') n3 r) then bad_answer bail
          else if is_err r then free_meta m st1' (fun st2 => k st2 None) bail
          else let '(st2, rid) := new_region RKGroup r n3 st1' in
               ag_tail full_lay (upd_ctx (fun c => set_mmap_counter (u32 (c_mmap_counter c + 1)) c) (upd_meta m (m_set_maplen (Z.shiftr n3 12)) st2)) sc m (rid, 0) c3
                 (let ai := (4096 - UNIT) / (UNIT * size_class sc) - 1 in let ai := if c3 - 1 <? ai then c3 - 1 else ai in if ai <? 0 then 0 else ai) k)) Post).
      { intros c3 n3 E3. destruct (proj1 (AR c3 n3 Hsc Hreq Hfit) HB E3) as [GRP RED].
        destruct (ag_cnt_facts sc req (usage st1 sc) u1 ns c3 n3 Hsc Hreq Hfit HU HB E3) as (STD & NSTD & NUB).
        apply (ag_mmap_fq T idle st st1 L L1 BL LS1 P B m sc req c3 n3 k bail Post INV1 NIm TF1 Hsc Hfit HA1 HA (lf_live _ _ LF) (GP_amf _ _ AF) GRP RED QP1 STD); [| exact NUB| exact GC1| exact BF1| exact HBP| exact HK].
        intros NE. rewrite <- U0. exact (NSTD NE). }
      unfold ag_cn3 in GO. cbn zeta in GO.
      destruct (negb ns && (c2 <=? 7)).
      * destruct ((round_up_pg (req + IB + UNIT) <? UNIT * size_class sc + UNIT) || ((4 * PGSZ <=? round_up_pg (req + IB + UNIT)) && (u1 <? 2 * c2))).
        -- cbn beta iota. exact (GO _ _ eq_refl).
        -- cbn beta iota. exact (GO _ _ eq_refl).
      * cbn beta iota. exact (GO _ _ eq_refl).
    + (* [comment removed for export] *)
      pose proof (proj2 (AR 0 false 0 0 Hsc Hreq Hfit) HB) as NEST.
      apply (ag_nest_fq T rec idle st st1 L L1 BL LS1 P B m sc req c1 k bail Post REC INV1 NIm ND TF1 Hsc Hfit HA1 HA (lf_live _ _ LF) (GP_amf _ _ AF) NEST QP1); [| exact GC1| exact BF1| | exact HBP| exact HK].
      * intros NE. rewrite <- U0. apply (ag_cnt1_nstd sc); [exact Hsc| exact NE].
      * pose proof (nest_host sc (usage st1 sc) Hsc) as NH. cbn zeta in NH.
        change (bump (UNIT * size_class sc) (cnt0_of sc (usage st1 sc))) with c1 in NH.
        specialize (NH HB).
        pose proof (nest_ok_sound sc c1 NEST) as N0. cbn zeta in N0. destruct N0 as (_ & N2 & _).
        pose proof (rank_host sc (size_to_class (UNIT + c1 * (UNIT * size_class sc) - IB)) ltac:(lia) NH). lia.
  - (* [comment removed for export] *) split; [exact Qst|]. split; [reflexivity|]. split; [reflexivity|]. intros x _. reflexivity.
Qed.
End AGQ.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section SLOTQ.
Variables (T : Type) (P : Z -> Z) (B : Z) (Post : mled -> T -> Prop).

Theorem alloc_slot_fq (f : nat) : forall sc idle st L BL LS req (k : mstate -> Z -> M T) bail,
  49 - sc <= Z.of_nat f ->
  INVL (X_as idle) st L BL LS -> TF0 st -> NoDup idle -> 0 <= sc < 48 -> 0 <= req -> req + IB <= UNIT * size_class sc ->
  QPOST P idle BL st -> zlen idle <= rank sc -> PHI P + R63 BL <= B + 3 * PGSZ ->
  (forall st1 idx L1 LS1, SLOT_POST idle sc req st L BL st1 idx L1 LS1 -> QPOST P idle BL st1 ->
     (forall c, 0 <= c < sc -> gcnt st1 c <= gcnt st c) -> BLF st st1 BL -> fqtree B L1 (k st1 idx) Post) ->
  fqtree B L (alloc_slot full_lay f st sc req k bail) Post.
Proof.
  induction f as [|f IH]; intros sc idle st L BL LS req k bail Hf INV TF ND Hsc Hreq Hfit QP RK HBP HK.
  { exfalso. cbn in Hf. lia. }
  change (alloc_slot full_lay (S f) st sc req k bail) with
    (try_avail sc st (fun st1 first =>
       if negb (first =? 0) then k st1 (ctz32 first)
       else alloc_group T full_lay (alloc_slot full_lay f) st1 sc req (fun st2 go =>
              match go with
              | None => k st2 (-1)
              | Some g => let st3 := upd_meta g (fun r => m_set_avail (m_avail r - 1) r) st2 in
                          queue (LActive sc) g st3 (fun st4 => k st4 0) bail
              end) bail) bail).
  destruct (try_avail_okQ T (X_as idle) L BL sc
              (fun st1 first =>
                 if negb (first =? 0) then k st1 (ctz32 first)
                 else alloc_group T full_lay (alloc_slot full_lay f) st1 sc req (fun st2 go =>
                        match go with
                        | None => k st2 (-1)
                        | Some g => let st3 := upd_meta g (fun r => m_set_avail (m_avail r - 1) r) st2 in
                                    queue (LActive sc) g st3 (fun st4 => k st4 0) bail
                        end) bail) bail eq_refl eq_refl Hsc st LS INV) as (st1 & first & LS1 & E & [TAF RES] & FF).
  rewrite E. cbn beta.
  assert (ACT1 : forall sc', sc' < sc -> active st1 sc' = active st sc').
  { intros sc' Hs. change (active st1 sc') with (get_head st1 (LActive sc')). rewrite (taf_heads _ _ _ TAF) by (intros EQ; inversion EQ; lia). reflexivity. }
  assert (TF1 : TF0 st1) by exact (TF0_ctrl st st1 (taf_shadow _ _ _ TAF) (taf_tick _ _ _ TAF) TF).
  (* [comment removed for export] *)
  pose proof QP as (SGst & Qst & Ast). destruct (QPOST_SINV P idle BL st (X_as idle) eq_refl QP) as [SIst _].
  assert (XFER : forall X1, x_idle X1 = idle -> INVL X1 st1 L BL LS1 -> QPOST P idle BL st1 /\ (forall c, 0 <= c < 48 -> gcnt st1 c <= gcnt st c) /\ BLF st st1 BL).
  { intros X1 HX INV1.
    destruct (SINVx_xfer (X_as idle) X1 st st1 L L BL LS LS1 P None INV INV1 ltac:(rewrite HX; reflexivity) FF Ast (SINV_SINVx _ _ _ SIst) ltac:(intros; discriminate)) as (SI1 & A1 & GC & _).
    split; [exact (SINV_QPOST P idle BL st1 X1 HX SI1 A1)|]. split; [exact GC| exact (BLF_ffr X1 st st1 L BL LS1 INV1 FF)]. }
  destruct RES as [(-> & HA & INV1)|(g & bg & ai & idx & NZ & POS & Eidx & HA & Hg & Hidx & SC & STR & INV1)].
  - (* [comment removed for export] *)
    change (negb (0 =? 0)) with false. cbn iota.
    destruct (XFER (X_as idle) eq_refl INV1) as (QP1 & GC1 & BF1).
    assert (RECQ : REC_OKQ T (alloc_slot full_lay f) sc P B Post).
    { intros j idle' st' L' BL' LS' req' k' bail' Hj INV' TF' ND' Hreq' Hfit' QP' RK' HBP' HK'.
      apply (IH j idle' st' L' BL' LS' req' k' bail'); try assumption; lia. }
    apply (alloc_group_fq T (alloc_slot full_lay f) sc P B Post RECQ idle st1 L BL LS1 req _ bail INV1 TF1 ND Hsc Hreq Hfit HA QP1 RK HBP).
    intros st2 go L2 LS2 (ACT2 & LIVE2 & GP2 & RES2) QP2 GLE2 BF2. destruct go as [g|].
    + destruct RES2 as (b & ai & last & ml & Hb & Em & Hai & Hl & FIT & STR & UND & INV2 & TF2').
      cbn zeta.
      destruct (slot_finish_ok T idle st2 L2 BL LS2 g b ai last sc ml (fun st4 => k st4 0) bail INV2 Hb Em Hai Hl Hsc
                  ltac:(rewrite ACT2 by lia; exact HA) UND TF2')
        as (LS4 & EQ & INV4 & TF4 & HA4 & ACT4 & G4 & TK4 & SH4 & L4 & SC4 & STR4 & SS4 & RG4 & SE4).
      rewrite EQ.
      (* [comment removed for export] *)
      set (st3 := upd_meta g (fun r => m_set_avail (m_avail r - 1) r) st2) in *.
      set (st4 := queue_st (LActive sc) g st3) in *.
      assert (F24 : FFR st2 st4).
      { apply (FFR_trans st2 st3 st4).
        - unfold st3. apply FFR_upd_meta; [exact (g_present _ _ _ _ _ _ (ig_ok _ _ _ (proj1 (proj2 (proj2 (proj2 (proj2 INV2))))) _ _ _ Hb))| intros r; destruct r; reflexivity| intros r Hr; destruct r; exact Hr].
        - unfold st4. apply FFR_queue_st.
          + unfold st3. rewrite s_metas_upd_meta, lookup_insert_eq. discriminate.
          + unfold st3, MR. rewrite get_meta_rec_upd_same. fold (MR st2 g). rewrite Em. cbn. discriminate.
          + intros a Ha. exfalso. unfold st3 in Ha. rewrite get_head_upd_meta in Ha. cbn in Ha. rewrite ACT2 in Ha by lia. rewrite HA in Ha. discriminate.
          + intros a z Ha. exfalso. unfold st3 in Ha. rewrite get_head_upd_meta in Ha. cbn in Ha. rewrite ACT2 in Ha by lia. rewrite HA in Ha. discriminate. }
      destruct QP2 as (SG2 & Q2 & A2). destruct (QPOST_SINV P idle BL st2 (mkX idle [] None None (Some g)) eq_refl (conj SG2 (conj Q2 A2))) as [SI2 _].
      destruct (SINVx_xfer (mkX idle [] None None (Some g)) _ st2 st4 L2 L2 BL LS2 LS4 P None INV2 INV4 eq_refl F24 A2 (SINV_SINVx _ _ _ SI2) ltac:(intros; discriminate)) as (SI4 & A4 & GC4 & _).
      eapply HK.
      * split; [intros sc' Hs; rewrite ACT4, ACT2 by lia; apply ACT1; exact Hs|]. split; [exact LIVE2|].
        split; [eapply GP_trans; [exact (GP_taf _ _ _ TAF)| eapply GP_trans; [exact GP2| apply GP_eq; [exact RG4| exact SE4]]]|].
        right. exists g, b, ai. rewrite L4, SC4, STR4, G4, SS4.
        split; [lia|]. split; [exact HA4|]. split; [exact Hb|]. split; [reflexivity|]. split; [exact FIT|]. split; [exact STR|].
        split; [exact INV4| exact TF4].
      * exact (SINV_QPOST P idle BL st4 (xpend (X_as idle) (Some (fst b, sstart (MR st2 g) 0))) eq_refl SI4 A4).
      * intros c Hc. pose proof (GC4 c ltac:(lia)). pose proof (GLE2 c Hc). pose proof (GC1 c ltac:(lia)). lia.
      * eapply BLF_trans; [exact BF1|]. eapply BLF_trans; [exact BF2|]. exact (BLF_ffr _ st2 st4 L2 BL LS4 INV4 F24).
    + destruct RES2 as [INV2 TF2']. eapply HK.
      * split; [intros sc' Hs; rewrite ACT2 by lia; apply ACT1; exact Hs|]. split; [exact LIVE2|].
        split; [eapply GP_trans; [exact (GP_taf _ _ _ TAF)| exact GP2]|].
        left. split; [reflexivity|]. split; [exact INV2| exact TF2'].
      * exact QP2.
      * intros c Hc. pose proof (GLE2 c Hc). pose proof (GC1 c ltac:(lia)). lia.
      * eapply BLF_trans; [exact BF1| exact BF2].
  - (* [comment removed for export] *)
    replace (negb (first =? 0)) with true by (symmetry; apply negb_true_iff; apply Z.eqb_neq; exact NZ).
    cbn iota. rewrite Eidx.
    destruct (XFER (xpend (X_as idle) (Some (fst bg, sstart (MR st1 g) idx))) eq_refl INV1) as (QP1 & GC1 & BF1).
    eapply HK.
    + split; [exact ACT1|]. split; [reflexivity|]. split; [exact (GP_taf _ _ _ TAF)|]. right.
      pose proof (ig_ok _ _ _ (proj1 (proj2 (proj2 (proj2 (proj2 INV1))))) _ _ _ Hg) as GO.
      pose proof (g_stride _ _ _ _ _ _ GO ltac:(rewrite SC; lia)) as (GS & _ & _). rewrite SC in GS.
      exists g, bg, ai. split; [exact Hidx|]. split; [exact HA|]. split; [exact Hg|]. split; [exact SC|].
      split; [lia|]. split; [intros Hs28; destruct GS; lia|]. split; [exact INV1|]. apply TF0_TF2. exact TF1.
    + exact QP1.
    + intros c Hc. apply GC1. lia.
    + exact BF1.
Qed.
End SLOTQ.

End LBCEIL.
End LB_WSlot.

From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require LB_Ljn7.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require MI_WFree.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.STree OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.Malloc OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.Mall7vg OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.KInv OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.KLink OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_List.MI_Tree OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_Inv OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_Kit OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_Arith OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_List OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_Geom OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_Ext OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_Pres2.MI_Ext2 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_S421 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_Pres2.MI_Pres1 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_Pres2 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_Pres4.MI_Pres3 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_Pres4 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_Ws22 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_W2ig.MI_Lsjc OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_W2ig OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_W3do OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_WTry2.MI_WTry OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_WTry2 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_Wp9i OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_Cnt OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_Ccma.MI_TF2 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_Ccma.MI_Wm9j OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_Ccma.MI_WSlot OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_Ccma.MI_Wvdb OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_Ccma.MI_Wdy2 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_Ccma.MI_Wkfj OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_Bits OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.LB_T80p OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.LB_Inv OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.LB_Sum OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.LB_Bound OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.LB_WNtf OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.LB_XferF OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.LB_Tree OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.LB_QM OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.LB_Wazc.LB_Wjp3 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.LB_XferF.LB_WTry OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.LB_AG.LB_Cnt OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.LB_AG OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.LB_StmtA OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.LB_WFree OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.LB_Wazc.LB_WSlot OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.LB_Wazc.LB_KCnt OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.LB_Ljn7 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_WFree.LB_Dead.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Ceiling.

Module LB_Rekey.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Nodes.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Nodes Decode Ceiling.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Nodes.ITree OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Nodes OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Decode OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Ceiling.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require Import STree Malloc Mall7vg Monad MProg KInv MI_Inv KNodes RzImpl KLink.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
(* [comment removed for export] *)
Local Ltac Stdlib.micromega.Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope Z_scope.

Section CEIL.
Context {Clg : Ceiling}.

(* [comment removed for export] *)
Lemma INVL_led_equiv X X' st st2 L L2 BL BL2 LS LS2 :
  INVL X st L BL LS -> INVL X' st2 L2 BL2 LS2 -> strip st2 = strip st ->
  ld_resv L2 = ld_resv L /\ Permutation (ld_groups L2) (ld_groups L) /\ Permutation (ld_metas L2) (ld_metas L)
  /\ ld_brkreg L2 = ld_brkreg L /\ ld_brk L2 = ld_brk L.
Proof.
  intros I1 I2 ES. pose proof (proj1 I1) as R1. pose proof (proj1 I2) as R2.
  assert (ER : s_regions st2 = s_regions st) by (apply (f_equal s_regions) in ES; exact ES).
  assert (EC : s_ctx st2 = s_ctx st) by (apply (f_equal s_ctx) in ES; exact ES).
  assert (EV : s_reserved st2 = s_reserved st) by (apply (f_equal s_reserved) in ES; exact ES).
  assert (EF : forall q rq, frontier st2 q rq = frontier st q rq) by (intros; unfold frontier; rewrite EC; reflexivity).
  split; [rewrite (ir_resv _ _ _ R1), (ir_resv _ _ _ R2); exact EV|].
  split. { eapply Permutation_trans; [exact (ir_groups _ _ _ R2)|]. rewrite ER. apply Permutation_sym. exact (ir_groups _ _ _ R1). }
  split. { eapply Permutation_trans; [exact (ir_metas _ _ _ R2)|]. rewrite ER.
           erewrite map_ext; [apply Permutation_sym; exact (ir_metas _ _ _ R1)|]. intros [q rq]. cbn [fst snd]. rewrite EF. reflexivity. }
  split.
  { pose proof (ir_brkreg _ _ _ R1) as B1. pose proof (ir_brkreg _ _ _ R2) as B2. rewrite ER in B2.
    destruct (ld_brkreg L) as [[b l]|] eqn:E1; destruct (ld_brkreg L2) as [[b2 l2]|] eqn:E2.
    - destruct (proj1 (B1 b l) eq_refl) as (q & rq & Hq & Kq & Hb & Hl). destruct (proj1 (B2 b2 l2) eq_refl) as (q2 & rq2 & Hq2 & Kq2 & Hb2 & Hl2).
      pose proof (ir_brk1 _ _ _ R1 q q2 rq rq2 Hq Hq2 Kq Kq2) as ->. rewrite Hq in Hq2. inversion Hq2. subst. reflexivity.
    - destruct (proj1 (B1 b l) eq_refl) as (q & rq & Hq & Kq & Hb & Hl). pose proof (proj2 (B2 b l) ltac:(exists q, rq; auto)). congruence.
    - destruct (proj1 (B2 b2 l2) eq_refl) as (q & rq & Hq & Kq & Hb & Hl). pose proof (proj2 (B1 b2 l2) ltac:(exists q, rq; auto)). congruence.
    - reflexivity. }
  pose proof (ir_brk _ _ _ R1) as P1. pose proof (ir_brk _ _ _ R2) as P2. rewrite EC in P2.
  destruct (c_brk (s_ctx st)); [destruct P1 as [E1 _]; destruct P2 as [E2 _] | pose proof P1 as E1; pose proof P2 as E2 | destruct P1 as [E1 _]; destruct P2 as [E2 _]];
    rewrite E1, E2; reflexivity.
Qed.

Lemma KL_led_equiv L L2 pbrk mo :
  ld_resv L2 = ld_resv L -> Permutation (ld_groups L2) (ld_groups L) -> Permutation (ld_metas L2) (ld_metas L) ->
  ld_brkreg L2 = ld_brkreg L -> ld_brk L2 = ld_brk L ->
  KL L2 pbrk mo -> KL L pbrk mo.
Proof.
  intros ER PG PM EB EP HK.
  assert (IG : forall x, In x (ld_groups L) <-> In x (ld_groups L2)).
  { intros x; split; intros H; [eapply Permutation_in; [apply Permutation_sym; exact PG| exact H]| eapply Permutation_in; [exact PG| exact H]]. }
  assert (IM : forall x, In x (ld_metas L) <-> In x (ld_metas L2)).
  { intros x; split; intros H; [eapply Permutation_in; [apply Permutation_sym; exact PM| exact H]| eapply Permutation_in; [exact PM| exact H]]. }
  assert (BD : forall b n, brk_disj L2 b n -> brk_disj L b n) by (intros b n H b0 l0 Hb; apply H; rewrite EB; exact Hb).
  destruct HK. constructor; auto.
  - rewrite <- ER. assumption.
  - intros b l H. apply IG in H. destruct (kl_groups b l H) as (A1 & A2 & A3 & A4 & A5 & A6). splits; auto; lia.
  - intros b l k H. apply IM in H. destruct (kl_metas b l k H) as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9). splits; auto; lia.
  - eapply Permutation_NoDup; [| exact kl_distinct]. apply Permutation_app; apply Permutation_map; assumption.
  - intros b l Hb. rewrite <- EB in Hb. exact (kl_brkreg b l Hb).
  - rewrite <- EP, <- EB. destruct (ld_brk L2); try exact kl_phase.
    destruct kl_phase as (P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8).
    split; [exact P1|]. split; [exact P2|]. split; [exact P3|]. split; [exact P4|]. split; [exact P5|]. split; [exact P6|].
    split; [intros b l H; apply P7; apply IG; exact H| intros b l k H; apply (P8 b l k); apply IM; exact H].
  - intros b l H. apply kl_groups_na. apply IG. exact H.
  - intros e He. destruct (kl_complete e He) as [(b & l & H & E)|[(b & l & k & H & E)|X]];
      [left; exists b, l; split; [apply IG; exact H| exact E]| right; left; exists b, l, k; split; [apply IM; exact H| exact E]| right; right; exact X].
  - unfold brk_extent in *. rewrite <- EB. exact kl_brkb.
Qed.


End CEIL.
End LB_Rekey.


Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
(* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac Stdlib.micromega.Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_noeuclid ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_post_hook.
(* [comment removed for export] *)
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Section LBCEIL.
Context {Clg : Ceiling}.  (* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

Lemma SG_add_block st BL c off n m i :
  SG st BL -> s_slots st !! c = Some (m, i) -> m_sizeclass (MR st m) < 48 -> 0 <= n < MMAP_THRESHOLD ->
  zlen BL + 1 <= NBCAP ->   (* [comment removed for export] *)
  SG st (((c, off), n) :: BL).
Proof.
  intros S Hs Hsc Hn CNT. destruct S as [S1 S2 S3 S4 S5 S6 S7]. constructor; auto.
  - intros k [<-|Hk]; [| exact (S1 k Hk)]. exists m, i. cbn [bslot bsize fst snd]. split; [exact Hs|].
    split; [intros _; lia| intros E63; exfalso; lia].
  - rewrite zlen_cons. lia.
  - intros b x ai Hb H63. right. exact (S6 b x ai Hb H63).
Qed.

Lemma AQ_add_block st BL P c off n :
  AQ st BL P -> 0 <= n -> ROOM BL P n -> AQ st (((c, off), n) :: BL) P.
Proof.
  intros A Hn (R1 & R2 & _). destruct A as [A1 A2 A3 A4 A5]. constructor; auto.
  - intros c' Hc'. unfold LR. rewrite zcount_cons. fold (LR BL c'). cbn [bsize snd]. unfold isbig. cbn [bsize snd].
    destruct (Z.leb_spec MMAP_THRESHOLD n) as [GE|LT]; cbn [negb andb]; [exact (A1 c' Hc')|].
    destruct (Z.eqb_spec (size_to_class n) c') as [<-|NE]; [specialize (R1 LT); lia| exact (A1 c' Hc')].
  - unfold n63. rewrite zcount_cons. fold (n63 BL). unfold isbig. cbn [bsize snd].
    destruct (Z.leb_spec MMAP_THRESHOLD n) as [GE|LT]; [specialize (R2 GE); lia| exact A3].
Qed.

(* [comment removed for export] *)

Lemma bigb_small n : n < MMAP_THRESHOLD -> bigb n = 0.
Proof. intros H. unfold bigb. replace (MMAP_THRESHOLD <=? n) with false by (symmetry; apply Z.leb_gt; exact H). reflexivity. Qed.

Lemma bigb_big n : MMAP_THRESHOLD <= n -> bigb n = bigmap n.
Proof. intros H. unfold bigb. replace (MMAP_THRESHOLD <=? n) with true by (symmetry; apply Z.leb_le; exact H). reflexivity. Qed.

Lemma mmap_len_rup l : mmap_len l = round_up_pg l.
Proof. unfold mmap_len. symmetry. apply round_up_pg_eq. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma small_class X st L BL LS n : INVL X st L BL LS -> 0 <= n < MMAP_THRESHOLD ->
  let sc0 := size_to_class n in
  let sc := match active st sc0 with
            | Some _ => sc0
            | None =>
              if (4 <=? sc0) && (sc0 <? 32) && negb (sc0 =? 6) && Z.even sc0 && (usage st sc0 =? 0) then
                let usage1 := usage st (Z.lor sc0 1) in
                let usage1 := match active st (Z.lor sc0 1) with
                              | None => usage1 + 3
                              | Some _ => let ar := get_meta_rec st (default (0%N,-1) (active st (Z.lor sc0 1))) in
                                          if (m_avail ar =? 0) && (m_freed ar =? 0) then usage1 + 3 else usage1
                              end in
                if usage1 <=? 12 then Z.lor sc0 1 else sc0
              else sc0
            end in
  0 <= sc < 48 /\ n + IB <= UNIT * size_class sc /\ (size_to_class n = sc \/ (size_to_class n = sc - 1 /\ gcnt st sc <= 12)).
Proof.
  intros INV Hn. pose proof (size_to_class_ok n ltac:(lia)) as [SC FIT]. cbn zeta.
  set (sc0 := size_to_class n) in *.
  destruct (active st sc0); [auto|].
  destruct ((4 <=? sc0) && (sc0 <? 32) && negb (sc0 =? 6) && Z.even sc0 && (usage st sc0 =? 0)) eqn:E; [| auto].
  apply andb_true_iff in E as [E _]. apply andb_true_iff in E as [E EV]. apply andb_true_iff in E as [E _]. apply andb_true_iff in E as [E1 E2].
  apply Z.leb_le in E1. apply Z.ltb_lt in E2.
  rewrite (lor1_even sc0 ltac:(lia) EV).
  assert (U : usage st (sc0 + 1) = gcnt st (sc0 + 1)) by exact (ia_usage _ (proj1 (proj2 INV)) (sc0 + 1) ltac:(lia)).
  match goal with |- context [if ?c then sc0 + 1 else sc0] => destruct c eqn:LE end; [| auto].
  apply Z.leb_le in LE.
  pose proof (size_class_lt sc0 (sc0 + 1) ltac:(lia) ltac:(lia) ltac:(lia)).
  split; [lia|]. split; [unfold UNIT in *; lia|]. right. split; [lia|].
  rewrite <- U. destruct (active st (sc0 + 1)); [| lia]. destruct (_ && _); lia.
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section C63Q.
Variables (st3 : mstate) (L : mled) (BL : list blk) (LS : lhead -> list aptr) (P : Z -> Z).
Variables (g : aptr) (rid : N) (r : region) (needed n off : Z).
Let X := mkX [g] [] None (Some rid) None.
Let p : aptr := (rid, 0).
Let X' := mkX [] [] (Some (rid, 16)) None None.
Hypothesis INV : INVL X st3 L BL LS.
Hypothesis Hr : s_regions st3 !! rid = Some r.
Hypothesis Kr : r_kind r = RKGroup.
Hypothesis Lr : r_len r = needed.
Hypothesis NS : s_shadow st3 !! rid = None.
Hypothesis Hn : 0 < needed < 2 ^ 63.
Hypothesis TF : TF0 st3.
Hypothesis En : needed = n + IB + UNIT.
Hypothesis Hbig : MMAP_THRESHOLD <= n.
Hypothesis SG3 : SG st3 BL.
Hypothesis Q3 : QM X st3 0.
Hypothesis A3 : AQ st3 BL P.
Hypothesis R63room : n63 BL + 1 <= P 63.
Hypothesis CNTroom : zlen BL + 1 <= NBCAP.   (* [comment removed for export] *)
Let ml := (needed + 4095) / 4096.
Let st4 := upd_meta g (F63 rid ml) st3.
Let st5 := put_group p (Some g) (group_active_idx st4 p) (hdr_havoc p st4).
Let st6 := add_slots g p (get_stride (get_meta_rec st5 g)) 1 st5.
Let mr' := mkMeta None None (Some p) 0 0 0 1 63 ml.
Let k0 : blk := (((rid, 16), off), n).

Let IM := proj1 (proj2 (proj2 INV)).
Let IG := proj1 (proj2 (proj2 (proj2 (proj2 INV)))).
Let IS := proj1 (proj2 (proj2 (proj2 (proj2 (proj2 INV))))).

Lemma q63_metas : s_metas st6 = <[g := mr']> (s_metas st3).
Proof.
  change (s_metas st6) with (s_metas st4). unfold st4. rewrite s_metas_upd_meta. fold (MR st3 g).
  rewrite (c63_MRg st3 L BL LS g rid INV). unfold ml, mr', p. rewrite (c63_F rid needed Hn). reflexivity.
Qed.

Lemma q63_groups : s_groups st6 = <[p := mkGhdr (Some g) 0]> (s_groups st3).
Proof.
  change (s_groups st6) with (s_groups st5). unfold st5, put_group. cbn [s_groups Malloc.set_groups].
  unfold group_active_idx, get_group. change (s_groups st4) with (s_groups st3). rewrite (c63_nogroup st3 L BL LS g rid INV). reflexivity.
Qed.

Lemma q63_rec5 : get_meta_rec st5 g = mr'.
Proof. unfold get_meta_rec. change (s_metas st5) with (s_metas st6). rewrite q63_metas, lookup_insert_eq. reflexivity. Qed.

Lemma q63_slots : s_slots st6 = <[(rid, 16) := (g, 0)]> (s_slots st3).
Proof.
  unfold st6, add_slots. rewrite q63_rec5. cbn [Z.iter Pos.iter snd s_slots set_slots].
  replace (aadd p (UNIT + get_stride mr' * 0)) with (rid, 16); [reflexivity|].
  unfold aadd, p. cbn [fst snd]. f_equal. unfold UNIT. lia.
Qed.

Lemma q63_MR x : x <> g -> MR st6 x = MR st3 x.
Proof. intros NE. unfold MR, get_meta_rec. rewrite q63_metas, lookup_insert_ne by congruence. reflexivity. Qed.

Lemma q63_MRg : MR st6 g = mr'.
Proof. unfold MR, get_meta_rec. rewrite q63_metas, lookup_insert_eq. reflexivity. Qed.

Lemma q63_old x : (exists b, hosts st3 b x) -> x <> g /\ MR st6 x = MR st3 x.
Proof.
  intros [b Hb]. assert (NE : x <> g).
  { intros ->. pose proof (hosts_mem _ _ _ IM _ _ Hb) as MM. rewrite (c63_MRg st3 L BL LS g rid INV) in MM. cbn in MM. discriminate. }
  split; [exact NE| exact (q63_MR x NE)].
Qed.

Lemma q63_nogroup_rid b : fst b = rid -> s_groups st3 !! b = None.
Proof. intros Hb. destruct (ir_orph _ _ _ (proj1 INV) rid eq_refl) as (r0 & _ & _ & NG). exact (NG b Hb). Qed.

Lemma q63_noslot : s_slots st3 !! (rid, 16) = None.
Proof.
  destruct (s_slots st3 !! (rid, 16)) as [[x i]|] eqn:E; [| reflexivity]. exfalso.
  destruct (is_valid _ _ _ IS _ _ _ E) as ([b Hb] & Hi & Es).
  rewrite (slot_start'_eq _ _ _ IM x b i Hb) in Es. assert (Eb : fst b = rid) by (inversion Es; reflexivity).
  destruct Hb as [ai Hb]. rewrite (q63_nogroup_rid b Eb) in Hb. discriminate.
Qed.

Lemma q63_slots_old s v : s_slots st3 !! s = Some v -> s_slots st6 !! s = Some v.
Proof. intros Hs. rewrite q63_slots, lookup_insert_ne; [exact Hs|]. intros <-. rewrite q63_noslot in Hs. discriminate. Qed.

Lemma q63_slotcls_old s : s_slots st3 !! s <> None -> slotcls st6 s = slotcls st3 s.
Proof.
  intros Hs. destruct (s_slots st3 !! s) as [[x i]|] eqn:E; [| congruence]. unfold slotcls. rewrite (q63_slots_old _ _ E), E.
  destruct (is_valid _ _ _ IS _ _ _ E) as ([b Hb] & _). destruct (q63_old x (ex_intro _ b Hb)) as [_ MRx]. unfold cls. rewrite MRx. reflexivity.
Qed.

Lemma q63_gmetas : Permutation (gmetas st6) ((g, p) :: gmetas st3).
Proof.
  unfold gmetas, groups_l. rewrite q63_groups.
  etransitivity; [apply Permutation_flat_map; apply mtl_insert; exact (q63_nogroup_rid p eq_refl)|]. cbn. apply Permutation_refl.
Qed.

Lemma q63_gmetas_hosts x b : In (x, b) (gmetas st3) -> exists b', hosts st3 b' x.
Proof. intros H. apply gmetas_in in H as [aix Hb]. exists b, aix. exact Hb. Qed.

Lemma q63_sum (F F' : aptr * aptr -> Z) :
  (forall x b, In (x, b) (gmetas st3) -> F' (x, b) = F (x, b)) ->
  zsum (map F' (gmetas st6)) = F' (g, p) + zsum (map F (gmetas st3)).
Proof.
  intros HF. rewrite (zsum_map_perm _ _ _ q63_gmetas). cbn [map]. rewrite zsum_cons. f_equal. apply zsum_map_ext. intros [x b] Hin. apply HF. exact Hin.
Qed.

Lemma q63_gcnt c : c <> 63 -> gcnt st6 c = gcnt st3 c.
Proof.
  intros NE. rewrite !gcnt_gmetas. rewrite (q63_sum (fun mb => if m_sizeclass (MR st3 (fst mb)) =? c then cnt_of (MR st3 (fst mb)) else 0)).
  - cbn [fst]. rewrite q63_MRg. unfold mr'. cbn [m_sizeclass]. replace (63 =? c) with false by (symmetry; apply Z.eqb_neq; lia). lia.
  - intros x b Hin. cbn [fst]. destruct (q63_old x (q63_gmetas_hosts x b Hin)) as [_ E]. rewrite E. reflexivity.
Qed.

Lemma q63_stdg_g : stdg st6 g = false.
Proof.
  unfold stdg, cls. rewrite q63_MRg. cbn [m_sizeclass]. unfold mr', ml, p. rewrite (c63_stride rid needed Hn).
  pose proof (c63_ml needed Hn) as [M _]. replace (_ =? S_ 63) with false; [apply andb_false_r|].
  symmetry. apply Z.eqb_neq. unfold S_. change (size_class 63) with 0. unfold UNIT. lia.
Qed.

Lemma q63_stdg_old x : (exists b, hosts st3 b x) -> stdg st6 x = stdg st3 x.
Proof. intros Hx. destruct (q63_old x Hx) as [_ E]. unfold stdg, cls. rewrite E. reflexivity. Qed.

Lemma q63_nsc c : 0 <= c < 48 -> nsc st6 c = nsc st3 c.
Proof.
  intros Hc. unfold nsc. rewrite (q63_sum (fun mb => if (cls st3 (fst mb) =? c) && negb (stdg st3 (fst mb)) then cnt_of (MR st3 (fst mb)) else 0)).
  - cbn [fst]. unfold cls at 1. rewrite q63_MRg. unfold mr'. cbn [m_sizeclass]. replace (63 =? c) with false by (symmetry; apply Z.eqb_neq; lia). cbn. reflexivity.
  - intros x b Hin. cbn [fst]. pose proof (q63_gmetas_hosts x b Hin) as Hx. rewrite (q63_stdg_old x Hx). destruct (q63_old x Hx) as [_ E]. unfold cls. rewrite E. reflexivity.
Qed.

Lemma q63_ncarved : ncarved st6 = ncarved st3.
Proof.
  unfold ncarved. rewrite q63_metas.
  pose proof (proj1 (im_idle _ _ _ IM g ltac:(left; reflexivity))) as Hg.
  change (zlen (map_to_list (<[g:=mr']> (s_metas st3))) = zlen (map_to_list (s_metas st3))).
  unfold zlen. rewrite (Permutation_length (mtl_insert_old (s_metas st3) g mr' _ Hg)), (Permutation_length (mtl_delete (s_metas st3) g _ Hg)). reflexivity.
Qed.

(* [comment removed for export] *)

Theorem c63_quant : SG st6 (k0 :: BL) /\ QM x0 st6 0 /\ AQ st6 (k0 :: BL) P /\ BLF st3 st6 BL.
Proof.
  pose proof (c63_ml needed Hn) as [M RU].
  assert (GRP' : forall b x aix, s_groups st6 !! b = Some (mkGhdr (Some x) aix) -> (x = g /\ b = p) \/ (x <> g /\ s_groups st3 !! b = Some (mkGhdr (Some x) aix) /\ MR st6 x = MR st3 x)).
  { intros b x aix Hb. rewrite q63_groups in Hb. destruct (aptr_eq_dec b p) as [->|NE].
    - rewrite lookup_insert_eq in Hb. inversion Hb. left. auto.
    - rewrite lookup_insert_ne in Hb by congruence. right. destruct (q63_old x (ex_intro _ b (ex_intro _ aix Hb))) as [NEx MRx]. auto. }
  assert (BF : BLF st3 st6 BL).
  { intros k Hk. destruct (is_blocks _ _ _ IS k Hk) as (x & i & Hs & _). apply q63_slotcls_old. rewrite Hs. discriminate. }
  split; [| split; [| split; [| exact BF]]].
  - (* [comment removed for export] *) destruct SG3 as [S1 S2 S3 S4 S5 S6 S7]. constructor.
    + intros k [<-|Hk].
      * exists g, 0. unfold k0. cbn [bslot bsize fst snd]. rewrite q63_slots, lookup_insert_eq, q63_MRg. unfold mr'. cbn [m_sizeclass m_maplen].
        split; [reflexivity|]. split; [intros; exfalso; lia|]. intros _. split; [exact Hbig|]. unfold ml in *. rewrite RU, En. apply bigmap_lower.   (* [comment removed for export] *)
      * destruct (S1 k Hk) as (x & i & Hs & C1 & C2). exists x, i. split; [exact (q63_slots_old _ _ Hs)|].
        destruct (is_valid _ _ _ IS _ _ _ Hs) as ([b Hb] & _). destruct (q63_old x (ex_intro _ b Hb)) as [_ MRx]. rewrite MRx. auto.
    + rewrite zlen_cons. lia.   (* [comment removed for export] *)
    + intros b x aix Hb Hc Hml. destruct (GRP' _ _ _ Hb) as [[-> ->]|(NE & Hb0 & MRx)]; [rewrite q63_MRg in Hc; unfold mr' in Hc; cbn in Hc; lia|].
      rewrite MRx in *. exact (S3 _ _ _ Hb0 Hc Hml).
    + intros b x aix Hb SD. destruct (GRP' _ _ _ Hb) as [[-> ->]|(NE & Hb0 & MRx)]; [rewrite q63_stdg_g in SD; discriminate|].
      rewrite (q63_stdg_old x (ex_intro _ b (ex_intro _ aix Hb0))) in SD. rewrite MRx. destruct (S4 _ _ _ Hb0 SD) as (Q1 & Q2 & Q3').
      split; [exact Q1|]. split; [| exact Q3']. intros Z0. destruct (Q2 Z0) as (g0 & i0 & Hs & Eg). exists g0, i0. split; [exact (q63_slots_old _ _ Hs)|].
      destruct (is_valid _ _ _ IS _ _ _ Hs) as ([bg Hbg] & _). destruct (q63_old g0 (ex_intro _ bg Hbg)) as [_ MRg0]. rewrite MRg0. exact Eg.
    + intros c Hc. rewrite (q63_nsc c Hc). exact (S5 c Hc).
    + intros b x aix Hb H63. destruct (GRP' _ _ _ Hb) as [[-> ->]|(NE & Hb0 & MRx)].
      * left. rewrite q63_MRg. unfold k0, slot_start', mr'. cbn -[Z.add Z.mul]. unfold p. cbn [fst snd]. f_equal. rewrite (c63_stride rid needed Hn) || idtac. unfold UNIT. lia.
      * right. rewrite MRx in *. exact (S6 _ _ _ Hb0 H63).
    + intros b x aix g0 i Hb Z0 Hs'. destruct (GRP' _ _ _ Hb) as [[-> ->]|(NE & Hb0 & MRx)]; [rewrite q63_MRg in Z0; unfold mr' in Z0; cbn in Z0; unfold ml in Z0; lia|].
      rewrite MRx in Z0. destruct (g_nest _ _ _ _ _ _ (ig_ok _ _ _ IG _ _ _ Hb0) Z0) as (g1 & i1 & Hs & _).
      rewrite (q63_slots_old _ _ Hs) in Hs'. assert (g1 = g0 /\ i1 = i) as [-> ->] by (split; congruence).
      destruct (is_valid _ _ _ IS _ _ _ Hs) as ([bg Hbg] & _). destruct (q63_old g0 (ex_intro _ bg Hbg)) as [_ MRg0]. rewrite MRg0. exact (S7 _ _ _ _ _ Hb0 Z0 Hs).
  - (* [comment removed for export] *)
    assert (RG' : s_regions st6 = s_regions st3) by reflexivity.
    assert (CX' : s_ctx st6 = s_ctx st3) by reflexivity.
    assert (AP' : apages st6 = apages st3) by (apply apages_ext; [exact RG'| rewrite CX'; reflexivity]).
    destruct Q3 as [Q1 Q2 Q3' Q4 Q5 Q6]. constructor; rewrite ?RG', ?q63_ncarved, ?AP', ?CX'; auto.
    intros x mr Hx Z0. rewrite q63_metas in Hx. destruct (aptr_eq_dec x g) as [->|NE].
    + rewrite lookup_insert_eq in Hx. inversion Hx. subst mr. cbn in Z0. discriminate.
    + rewrite lookup_insert_ne in Hx by congruence. destruct (Q1 x mr Hx Z0) as [N0|I0]; [left; exact N0|]. cbn in I0. destruct I0 as [I0|[]]. congruence.
  - (* [comment removed for export] *) destruct A3 as [A1 A2 A3' A4 A5]. constructor; auto.
    + intros c Hc. unfold LR. rewrite zcount_cons. fold (LR BL c). unfold isbig, k0. cbn [bsize snd]. replace (MMAP_THRESHOLD <=? n) with true by (symmetry; apply Z.leb_le; exact Hbig). cbn. exact (A1 c Hc).
    + intros c Hc. rewrite (q63_gcnt c ltac:(lia)). exact (A2 c Hc).
    + unfold n63. rewrite zcount_cons. fold (n63 BL). unfold isbig, k0. cbn [bsize snd]. replace (MMAP_THRESHOLD <=? n) with true by (symmetry; apply Z.leb_le; exact Hbig). lia.
    + rewrite q63_ncarved. exact A4.
Qed.
End C63Q.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section COREQ.
Variables (st : mstate) (L : mled) (BL : list blk) (LS : lhead -> list aptr) (P : Z -> Z) (n B : Z).
Hypothesis INV : INVL x0 st L BL LS.
Hypothesis TF : TF0 st.
Hypothesis SI : SINV x0 st BL.
Hypothesis HAQ : AQ st BL P.
Hypothesis Hn : 0 <= n.
Hypothesis HR : ROOM BL P n.
Hypothesis HB : PHI P + R63 BL + bigb n <= B + 3 * PGSZ.

(* [comment removed for export] *)
Lemma small_leaf st1 L1 LS1 g bg idx sc X1 :
  INVL X1 st1 L1 BL LS1 -> x_idle X1 = [] -> hosts st1 bg g -> 0 <= idx <= m_last_idx (MR st1 g) ->
  m_sizeclass (MR st1 g) = sc -> 0 <= sc < 48 ->
  (size_to_class n = sc \/ (size_to_class n = sc - 1 /\ gcnt st sc <= 12)) ->
  SINV X1 st1 BL -> AQ st1 BL P -> BLF st st1 BL -> n < MMAP_THRESHOLD ->
  CORE_POSTQ n BL P L1 (st1, Some (g, idx)).
Proof.
  intros INV1 HX Hh Hidx SCg Hsc CLS SI1 A1 BF Hlt. unfold CORE_POSTQ. cbn [fst snd]. intros bg' off Hh'.
  pose proof (hosts_inj _ _ _ (proj1 (proj2 (proj2 INV1))) _ _ _ Hh' Hh) as ->.
  pose proof (is_total _ _ _ (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 INV1)))))) bg g idx Hh Hidx) as T.
  rewrite (slot_start'_eq _ _ _ (proj1 (proj2 (proj2 INV1))) g bg idx Hh) in T.
  split.
  - apply (SINV_X X1 x0); [rewrite HX; reflexivity|]. apply SINV_split in SI1 as [G1 Q1]. apply SINV_split. split; [| exact Q1].
    exact (SG_add_block st1 BL _ off n g idx G1 T ltac:(lia) ltac:(lia) (proj2 (proj2 HR))).
  - exact (AQ_add_block st1 BL P _ off n A1 Hn HR).
Qed.


Lemma malloc_small_fq : n < MMAP_THRESHOLD ->
  fqtree B L (malloc_small_ctrl full_lay st n (fun st1 r => ret (st1, r)) (ret (st, @None (aptr * Z)))) (CORE_POSTQ n BL P).
Proof.
  intros Hlt. pose proof (small_class x0 st L BL LS n INV ltac:(lia)) as SCF. cbn zeta in SCF.
  pose proof HB as HB0. rewrite (bigb_small n Hlt), Z.add_0_r in HB0.
  pose proof (SINV_QPOST P [] BL st x0 eq_refl SI HAQ) as QP.
  unfold malloc_small_ctrl.
  set (sc0 := size_to_class n) in *.
  set (sc := match active st sc0 with Some _ => sc0 | None => _ end) in *.
  clearbody sc. destruct SCF as (SC' & FIT' & CLS).
  assert (SLOT : fqtree B L (alloc_slot full_lay FUEL st sc n (fun st1 idx =>
             if idx <? 0 then ret (st1, None)
             else match active st1 sc with
                  | Some gp => ret (st1, Some (gp, idx))
                  | None => SVis (EUndef UBadPtr) (fun _ => ret (st, @None (aptr * Z)))
                  end) (ret (st, None))) (CORE_POSTQ n BL P)).
  { apply (alloc_slot_fq (mstate * option (aptr * Z)) P B (CORE_POSTQ n BL P) FUEL sc [] st L BL LS n); try assumption.
    - unfold FUEL. cbn. lia.
    - apply NoDup_nil_2.
    - pose proof (rank_range sc). unfold zlen. cbn. lia.
    - intros st1 idx L1 LS1 (ACT & LIVE & GP1 & RES) QP1 GC1 BF1.
      destruct RES as [(-> & INV1 & TF1)|(g & bg & ai & Hidx & HA1 & Hg & SCg & FIT1 & STR1 & INV1 & TF1)].
      + change (-1 <? 0) with true. cbn iota. apply fqtree_ret. unfold CORE_POSTQ. cbn [fst snd].
        exact (QPOST_SINV P [] BL st1 x0 eq_refl QP1).
      + replace (idx <? 0) with false by (symmetry; apply Z.ltb_ge; lia). rewrite HA1. apply fqtree_ret.
        destruct (QPOST_SINV P [] BL st1 (xpend (X_as []) (Some (fst bg, sstart (MR st1 g) idx))) eq_refl QP1) as [SI1 A1].
        apply (small_leaf st1 L1 LS1 g bg idx sc _ INV1 eq_refl (ex_intro _ ai Hg) Hidx SCg SC' CLS SI1 A1 BF1 Hlt). }
  destruct (active st sc) as [gp|] eqn:HA; [| exact SLOT].
  destruct (Z.eqb_spec (m_avail (get_meta_rec st gp)) 0) as [AZ|ANZ].
  { rewrite AZ. change (lowbit 0) with 0. cbn [negb Z.eqb]. exact SLOT. }
  (* [comment removed for export] *)
  destruct (hd_facts x0 st L BL LS sc gp INV HA) as (_ & Esc & bm & ai & Hbm).
  pose proof (ig_ok _ _ _ (proj1 (proj2 (proj2 (proj2 (proj2 INV))))) _ _ _ Hbm) as GO.
  pose proof (proj1 (g_masks _ _ _ _ _ _ GO)) as A0. fold (MR st gp) in ANZ |- *.
  destruct (lowbit_idiom (m_avail (MR st gp)) ltac:(lia)) as (k & Hk & LB & CTZ & TB & _).
  assert (LNZ : (lowbit (m_avail (MR st gp)) =? 0) = false) by (apply Z.eqb_neq; rewrite LB; pose proof (Z.pow_pos_nonneg 2 k ltac:(lia) Hk); lia).
  rewrite LNZ. cbn [negb]. apply fqtree_ret.
  pose proof (ta_fin_ok x0 st L BL LS gp bm ai INV eq_refl eq_refl Hbm ltac:(rewrite Esc; exact (hd_head x0 st L BL LS sc gp INV HA)) ANZ) as (INV1 & Hidx & _ & _ & STR).
  set (st1 := upd_meta gp (m_set_avail (m_avail (MR st gp) - lowbit (m_avail (MR st gp)))) st) in *.
  assert (MRg : m_last_idx (MR st1 gp) = m_last_idx (MR st gp) /\ m_sizeclass (MR st1 gp) = m_sizeclass (MR st gp)).
  { unfold st1, MR. rewrite get_meta_rec_upd_same. destruct (get_meta_rec st gp); cbn; split; reflexivity. }
  destruct MRg as [ML MSC].
  assert (F01 : FFR st st1).
  { unfold st1. apply FFR_upd_meta; [exact (g_present _ _ _ _ _ _ GO)| intros r; destruct r; reflexivity| intros r Hr; destruct r; exact Hr]. }
  destruct (SINVx_xfer x0 (xpend x0 (Some (fst bm, sstart (MR st gp) (ctz32 (lowbit (m_avail (MR st gp))))))) st st1 L L BL LS LS P None INV INV1 eq_refl F01 HAQ (SINV_SINVx _ _ _ SI) ltac:(intros; discriminate)) as (SI1 & A1 & _).
  apply (small_leaf st1 L LS gp bm _ sc _ INV1 eq_refl); try assumption.
  - apply (proj2 (hosts_ext st st1 eq_refl bm gp)). exists ai. exact Hbm.
  - rewrite ML. exact Hidx.
  - rewrite MSC. exact Esc.
  - exact (BLF_ffr _ st st1 L BL LS INV1 F01).
Qed.

(* [comment removed for export] *)
Lemma malloc_big_fq : MMAP_THRESHOLD <= n -> size_overflows n = false ->
  fqtree B L
    (SVis (EMmap 0 (n + IB + UNIT) PROT_RW (MAP_PRIVATE + MAP_ANON)) (fun r =>
      if negb (mmap_answer_ok (live_ranges st) (n + IB + UNIT) r) then bad_answer (ret (st, @None (aptr * Z))) else
      if is_err r then ret (st, None) else
      let '(st1, rid) := new_region RKGroup r (n + IB + UNIT) st in
      let st2 := step_seq st1 in
      alloc_meta st2 (fun st3 go =>
        match go with
        | None => SVis (EMunmap r (n + IB + UNIT)) (fun ru => if munmap_answer_ok ru then ret (drop_region rid st3, @None (aptr * Z)) else bad_answer (ret (st, @None (aptr * Z))))
        | Some g =>
          let st4 := upd_meta g (fun mr => m_set_freed 0 (m_set_avail 0 (m_set_maplen ((n + IB + UNIT + 4095) / 4096)
                       (m_set_sizeclass 63 (m_set_freeable 1 (m_set_last_idx 0 (m_set_mem (Some (rid, 0)) mr))))))) st3 in
          let st5 := put_group (rid, 0) (Some g) (group_active_idx st4 (rid, 0)) (lh_hdr full_lay st4 (rid, 0)) in
          let st6 := add_slots g (rid, 0) (get_stride (get_meta_rec st5 g)) 1 st5 in
          let st7 := upd_ctx (fun c => set_mmap_counter (u32 (c_mmap_counter c + 1)) c) st6 in
          ret (st7, Some (g, 0))
        end) (ret (st, @None (aptr * Z)))))
    (CORE_POSTQ n BL P).
Proof.
  intros Hbig Hov. unfold size_overflows in Hov. apply Z.leb_gt in Hov.
  set (needed := n + IB + UNIT).
  assert (HN : 131072 <= needed < 2 ^ 63 - 4000) by (unfold needed, IB, UNIT, MMAP_THRESHOLD in *; lia).
  pose proof HB as HB0. rewrite (bigb_big n Hbig) in HB0. unfold bigmap in HB0. fold needed in HB0. assert (PG0 : 0 < PGSZ) by (unfold PGSZ; lia).   (* [comment removed for export] *)
  pose proof (round_up_pg_spec needed) as [[RU1 RU2] _].
  pose proof INV as (IR & IA & IM & IL & IG & IS & ISH).
  pose proof (SINV_QPOST P [] BL st x0 eq_refl SI HAQ) as QP. destruct QP as (SGst & Qst & Ast).
  pose proof (state_bytes_B x0 st L BL LS P (B - round_up_pg needed) INV eq_refl eq_refl SI HAQ ltac:(lia)) as SB.
  apply fqtree_vis; [reflexivity| reflexivity| | | | |].
  - cbn. left. split; [exact (brk_quiet_of _ _ _ IR)|]. split; [reflexivity|]. split; [reflexivity|]. split; [right; reflexivity|].
    unfold LEN_MAX. clear -HN. lia.
  - (* [comment removed for export] *)
    intros a Ha. cbn [answer_ok] in Ha. change (Z.land (MAP_PRIVATE + MAP_ANON) MAP_FIXED =? 0) with true in Ha. cbn [negb] in Ha.
    change (event_post L (EMmap 0 needed PROT_RW (MAP_PRIVATE + MAP_ANON)) a)
      with (if Z.land (MAP_PRIVATE + MAP_ANON) MAP_FIXED =? 0 then if is_err a then L else if PROT_RW =? PROT_NONE then KInv.set_metas ((a, needed, 0) :: ld_metas L) L else KInv.set_groups ((a, needed) :: ld_groups L) L else set_brkph BPLive (set_brkreg (Some (0, 2 * PGSZ)) L)).
    change (Z.land (MAP_PRIVATE + MAP_ANON) MAP_FIXED =? 0) with true. change (PROT_RW =? PROT_NONE) with false. cbn iota.
    destruct (is_err a); [lia|]. rewrite gm_add_group, BB_set_groups, mmap_len_rup. lia.
  - (* [comment removed for export] *)
    cbn [XB]. change (Z.land (MAP_PRIVATE + MAP_ANON) MAP_FIXED =? 0) with true. cbn iota.
    pose proof (gm_BB_nonneg x0 st L BL LS INV) as GB0. split.
    + rewrite mmap_len_rup. clear -SB GB0 RU1. unfold PGSZ in *. lia.
    + exact (kcnt_KCAP_S x0 st L BL LS P INV SI HAQ).
  - intros a Ha. cbn [answer_ok] in Ha. change (Z.land (MAP_PRIVATE + MAP_ANON) MAP_FIXED =? 0) with true in Ha. cbn iota in Ha.
    change (event_post L (EMmap 0 needed PROT_RW (MAP_PRIVATE + MAP_ANON)) a)
      with (if Z.land (MAP_PRIVATE + MAP_ANON) MAP_FIXED =? 0 then if is_err a then L else if PROT_RW =? PROT_NONE then KInv.set_metas ((a, needed, 0) :: ld_metas L) L else KInv.set_groups ((a, needed) :: ld_groups L) L else set_brkph BPLive (set_brkreg (Some (0, 2 * PGSZ)) L)).
    change (Z.land (MAP_PRIVATE + MAP_ANON) MAP_FIXED =? 0) with true. change (PROT_RW =? PROT_NONE) with false. cbn iota.
    rewrite (mmap_answer_ok_eq _ _ _ IR) in Ha. rewrite Ha. cbn [negb].
    destruct (is_err a) eqn:ER.
    + apply fqtree_ret. unfold CORE_POSTQ. cbn [fst snd]. split; [exact SI| exact HAQ].
    + destruct (new_region RKGroup a needed st) as [st1 rid] eqn:EN.
      assert (Erid : rid = s_next_rid st) by (unfold new_region in EN; inversion EN; reflexivity).
      assert (Est1 : st1 = fst (new_region RKGroup a needed st)) by (rewrite EN; reflexivity).
      pose proof (INVL_new_group_region x0 st L BL LS a needed INV eq_refl Ha ER ltac:(unfold LEN_MAX; clear -HN; lia)) as INV1.
      rewrite <- Est1, <- Erid in INV1.
      set (L1 := KInv.set_groups ((a, needed) :: ld_groups L) L) in *.
      assert (Hr1 : s_regions st1 !! rid = Some (mkRegion RKGroup a needed)) by (rewrite Est1, ng_lookup, Erid, N.eqb_refl; reflexivity).
      assert (FR : s_regions st !! rid = None) by (rewrite Erid; exact (nm_fresh _ _ _ _ _ INV)).
      assert (NS1 : s_shadow st1 !! rid = None).
      { rewrite Est1, Erid. change (s_shadow (fst (new_region RKGroup a needed st))) with (s_shadow st). exact (shadow_next_rid_none _ _ _ _ _ INV). }
      assert (TF1 : TF0 (step_seq st1)).
      { destruct (step_seq_fields st1) as (A' & B' & _). apply (TF0_ctrl st1); [exact A'| exact B'|]. apply (TF0_ctrl st); [rewrite Est1; reflexivity| rewrite Est1; reflexivity| exact TF]. }
      pose proof (INVL_step_seq _ _ _ _ _ INV1) as INV2.
      destruct (step_seq_fields st1) as (SS1 & SS2 & SS3 & SS4 & SS5 & _).
      (* [comment removed for export] *)
      pose proof (QPOST_new_group_region P [] BL st x0 L LS a needed INV (conj SGst (conj Qst Ast))) as QP1. rewrite <- Est1 in QP1.
      pose proof (QPOST_qsame P [] BL st1 (step_seq st1) _ L1 LS INV1 (qsame_step_seq st1) QP1) as (SG2 & Q2 & A2).
      set (st2 := step_seq st1) in *.
      assert (GB2 : group_bytes st2 = group_bytes st + round_up_pg needed).
      { rewrite (group_bytes_ext st1 st2 SS4). rewrite !group_bytes_msum, Est1. unfold new_region. cbn [fst s_regions set_next_rid set_regions].
        rewrite <- Erid. rewrite (msum_regions_insert_fresh gbF st rid _ FR). unfold gbF at 1. cbn. lia. }
      eapply (alloc_meta_fq (mstate * option (aptr * Z)) BL P B (CORE_POSTQ n BL P) _ _ (xorph x0 (Some rid)) st2 L1 LS INV2 SG2 A2);
        [ | | | | exact INV2| apply amf_refl| apply lf_refl| | reflexivity].
      * (* [comment removed for export] *)
        intros HFH. pose proof (ncarved_le_groups (xorph x0 (Some rid)) st2 L1 BL LS INV2 0 (QM_X (X_as []) (xorph x0 (Some rid)) st2 0 eq_refl Q2) HFH eq_refl) as NC.
        pose proof (ngroups_le (xorph x0 (Some rid)) st2 L1 BL LS P INV2 SG2 A2) as NG0. cbn [x_idle xorph x0] in NC. unfold zlen in NC. cbn [length] in NC. change (Z.of_nat 0) with 0 in NC. unfold NCAP. lia.
      * (* [comment removed for export] *)
        rewrite GB2. pose proof (group_bytes_B x0 st L BL LS P (B - round_up_pg needed) INV eq_refl eq_refl SI HAQ ltac:(lia)). lia.
      * (* [comment removed for export] *)
        intros st3 L3 LS3 INV3 AF LF SI3 A3' GC3 GEO3. cbn beta iota.
        assert (Hr3 : s_regions st3 !! rid = Some (mkRegion RKGroup a needed)) by (apply (amf_regions _ _ AF); [rewrite SS4; exact Hr1| reflexivity]).
        pose proof (proj1 INV3) as IR3.
        assert (GPOS : forall g, In g (ld_groups L3) -> 0 <= snd g).
        { intros g Hg. apply (Permutation_in _ (ir_groups _ _ _ IR3)) in Hg. apply in_map_iff in Hg as ([q rq] & <- & Hin). cbn.
          apply filter_In in Hin as [Hin _]. apply mtl_in in Hin. pose proof (ir_shape _ _ _ IR3 _ _ Hin) as (_ & _ & L0 & _). lia. }
        apply fqtree_vis; [reflexivity| reflexivity| | | exact I| |].
        -- cbn. split; [exact (brk_quiet_of _ _ _ IR3)|]. exists needed. rewrite (lf_groups _ _ LF). split; [left; reflexivity| left; reflexivity].
        -- intros z Hz. etransitivity; [apply lbytes_event_post_munmap; exact GPOS|].
           pose proof (ledger_bound _ st3 L3 BL LS3 INV3) as LB3. pose proof (regions_bound _ st3 L3 BL LS3 P INV3 SI3 A3' eq_refl) as RB3.
           unfold ORPH in RB3. cbn [x_orph xorph x0] in RB3. rewrite Hr3 in RB3. cbn [r_len] in RB3. lia.
        -- intros ru Hru. cbn [answer_ok] in Hru. rewrite Hru. apply fqtree_ret. unfold CORE_POSTQ. cbn [fst snd].
           destruct (SINV_drop_orph _ st3 L3 BL LS3 P rid _ INV3 Hr3 eq_refl SI3 A3') as [S'' A'']. split; [exact (SINV_X (xorph x0 (Some rid)) x0 _ _ eq_refl S'')| exact A''].
        -- intros ru Hru. cbn [answer_ok] in Hru. rewrite Hru. exact I.
      * (* [comment removed for export] *)
        intros st3 L3 LS3 g INV3 NIg AF LF SI3 A3' NC3 GC3 GEO3. cbn beta iota zeta.
        change (lh_hdr full_lay) with (fun s b => hdr_havoc b s). cbn beta.
        assert (Hr3 : s_regions st3 !! rid = Some (mkRegion RKGroup a needed)) by (apply (amf_regions _ _ AF); [rewrite SS4; exact Hr1| reflexivity]).
        assert (NS3 : s_shadow st3 !! rid = None) by (rewrite (amf_shadow _ _ AF), SS1; exact NS1).
        assert (TF3 : TF0 st3) by (apply (TF0_ctrl st2); [exact (amf_shadow _ _ AF)| exact (amf_tick _ _ AF)| exact TF1]).
        cbn [xidle xorph x_idle x_zomb x_pend x_orph x_fresh x0] in INV3, SI3.
        destruct (create63_ok st3 L3 BL LS3 g rid (mkRegion RKGroup a needed) needed INV3 Hr3 eq_refl eq_refl NS3 ltac:(lia) TF3)
          as (INV6 & TF6 & MR6 & GR6 & CTX6 & TK6 & RG6 & STR6 & RU6).
        match goal with |- fqtree _ _ (ret (upd_ctx ?f ?s6, _)) _ => set (st6 := s6) in * end.
        apply fqtree_ret. unfold CORE_POSTQ. cbn [fst snd]. intros bg off Hh.
        pose proof (INVL_mmap_counter _ _ _ _ _ INV6) as INV7.
        set (st7 := upd_ctx _ st6) in *.
        assert (Hh6 : hosts st6 bg g) by exact Hh.
        pose proof (hosts_inj _ _ _ (proj1 (proj2 (proj2 INV6))) _ _ _ Hh6 (ex_intro _ 0 GR6)) as ->.
        assert (MR7 : MR st7 g = MR st6 g) by reflexivity. rewrite MR7, MR6.
        replace (sstart (mkMeta None None (Some (rid, 0)) 0 0 0 1 63 ((needed + 4095) / 4096)) 0) with 16 by (unfold sstart, gbase; cbn -[Z.mul Z.add get_stride]; unfold UNIT; lia).
        change (fst (rid, 0)) with rid.
        apply SINV_split in SI3 as [SG3 Q3].
        destruct (c63_quant st3 L3 BL LS3 P g rid needed n off INV3 ltac:(lia) eq_refl Hbig SG3 Q3 A3' ltac:(exact (proj1 (proj2 HR) Hbig)) (proj2 (proj2 HR)))
          as (SG6 & Q6 & A6 & _).
        fold st6 in SG6, Q6, A6.
        assert (SV6 : forall s x i, s_slots st6 !! s = Some (x, i) -> exists b, hosts st6 b x).
        { intros s x i Hs. exact (proj1 (is_valid _ _ _ (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 INV6)))))) _ _ _ Hs)). }
        split.
        -- apply SINV_split. split.
           ++ apply (SG_frame st6 st7 _ eq_refl eq_refl ltac:(intros; reflexivity) SV6 SG6).
           ++ destruct Q6 as [Q1' Q2' Q3' Q4' Q5' Q6']. constructor; auto.
        -- apply (AQ_frame st6 st7 _ P eq_refl ltac:(intros; reflexivity)); [| exact A6]. exact (aq_carved _ _ _ A6).
      * (* [comment removed for export] *)
        split; [exact (QM_X (X_as []) (xorph x0 (Some rid)) st2 0 eq_refl Q2)|]. split; [reflexivity|]. split; [reflexivity|]. intros; reflexivity.
  - intros a Ha. cbn [answer_ok] in Ha. change (Z.land (MAP_PRIVATE + MAP_ANON) MAP_FIXED =? 0) with true in Ha. cbn iota in Ha.
    rewrite (mmap_answer_ok_eq _ _ _ IR) in Ha. rewrite Ha. exact I.
Qed.

Theorem malloc_core_fq : fqtree B L (malloc_core full_lay st n) (CORE_POSTQ n BL P).
Proof.
  unfold malloc_core.
  destruct (size_overflows n) eqn:Hov.
  - apply fqtree_ret. unfold CORE_POSTQ. cbn [fst snd]. split; [exact SI| exact HAQ].
  - destruct (Z.leb_spec MMAP_THRESHOLD n) as [Hbig|Hsmall].
    + exact (malloc_big_fq Hbig Hov).
    + exact (malloc_small_fq Hsmall).
Qed.
End COREQ.

Theorem malloc_core_fq_proof : malloc_core_fq_stmt.
Proof. intros st L BL LS P n B INV TF SI HAQ Hn HR HB. exact (malloc_core_fq st L BL LS P n B INV TF SI HAQ Hn HR HB). Qed.

Check (malloc_core_fq_proof : malloc_core_fq_stmt).

End LBCEIL.
