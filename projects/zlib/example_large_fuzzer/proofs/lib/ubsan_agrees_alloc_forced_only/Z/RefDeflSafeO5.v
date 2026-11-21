(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith.
From Stdlib Require Import List.
From Stdlib Require Import Lia.
From Stdlib Require Import Bool.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import DeflateState.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import Trees.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import OverlayIface.
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
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import RefDeflSafeB5.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import RefDeflSafeB6.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import RefDeflSafeO1.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import RefDeflSafeO2.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import RefDeflSafeO3.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import RefDeflSafeO4.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
Lemma rep_find_ext : forall f (h h' : hist) b, (forall x, h x = h' x) -> rep_find f h b = rep_find f h' b.
Proof. induction f as [|f IH]; intros h h' b E; cbn [rep_find]; [reflexivity|]. rewrite E. destruct (h' b =? 0); [apply IH; exact E | reflexivity]. Qed.

Lemma rep_step_ext : forall ML (h h' : hist) r x, (forall x, h x = h' x) -> rep_step ML h r x = rep_step ML h' r x.
Proof. intros ML h h' r x E. unfold rep_step. rewrite !E. reflexivity. Qed.

Lemma rep_iter_ext : forall n ML (h h' : hist), (forall x, h x = h' x) -> forall x, rep_iter n ML h x = rep_iter n ML h' x.
Proof.
  induction n as [|n IH]; intros ML h h' E x; cbn [rep_iter]; [apply E|].
  apply IH. intros y. rewrite (rep_find_ext _ h h') by exact E. apply rep_step_ext. exact E.
Qed.

Lemma repair_ext : forall ML (h h' : hist), (forall x, h x = h' x) -> forall x, repair ML h x = repair ML h' x.
Proof.
  intros ML h h' E x. unfold repair, kraftZ. rewrite (zsum_ext (fun b => h b * 2 ^ (ML - b)) (fun b => h' b * 2 ^ (ML - b))) by (intros; rewrite E; reflexivity).
  apply rep_iter_ext. exact E.
Qed.

Section ZTree.
Variable t : tree_id.
Variable FC2 : arr.
Variable DL2 : arr.
Variable L : Z.
Variable mc : Z.
Variable FCf : arr.
Variable DLf : arr.
Variable HPf : arr.
Variable DPf : arr.
Variable Wg : Z -> Z.
Variable DLq : arr.
Local Notation E := (sd_elems t).
Local Notation ML := (sd_max_length t).
Local Notation HM := (HM L).
Local Notation C := (C t L HPf).
Local Notation D := (D t L HPf).
Local Notation leafb := (leafb t HPf).
Local Notation nd := (nd HPf).
Local Notation par := (par t L HPf).
Local Notation tail := (tail L).
Local Notation cntL := (cntL t L HPf).
Local Notation NI := (NI t L HPf 573).
Local Notation lcnt := (lcnt t HPf).
Hypothesis HR : heap_result t FC2 DL2 L mc FCf DLf HPf DPf.
Hypothesis GF : greedy_facts t FC2 L FCf HPf Wg.
(* [comment removed for export] *)
Hypothesis HDLI : DLI t FC2 L HPf DLq.
Hypothesis Hnoovf : NI = 0 -> forall i, HM < i < 573 -> arr_get DLq (nd i) = D i.
Hypothesis Hhist : forall b, 1 <= b <= ML -> lcnt DLq (HM + 1) b = repair ML cntL b.
Hypothesis Hrank : NI <> 0 -> forall p q, HM < q -> q < p -> p < 573 -> leafb p = true -> leafb q = true -> arr_get DLq (nd q) <= arr_get DLq (nd p).
Hypothesis Hkraft : kraftZ ML (fun b => lcnt DLq (HM + 1) b) = 2 ^ ML.

Let RHM : 2 <= HM <= 570 := HM_range t FC2 DL2 L mc FCf DLf HPf DPf HR.
Let RML : 7 <= ML <= 15 /\ E <= 2 ^ ML := ML_range t FC2 DL2 L mc FCf DLf HPf DPf HR.
Let RL : 2 <= L <= E := hr_L _ _ _ _ _ _ _ _ _ HR.

Definition ztree_of : ztree := {| zt_E := E; zt_ML := ML; zt_g := gtree_of t L HPf Wg; zt_len := fun c => arr_get DLq c |}.

(* [comment removed for export] *)
Lemma g_depth_fuel_D : forall f g i, tail i -> (Z.to_nat (i - HM) < f)%nat -> (Z.to_nat (i - HM) < g)%nat ->
  g_depth_fuel (gtree_of t L HPf Wg) f i = Df t L HPf g i.
Proof.
  induction f as [|f IH]; intros g i Hi Hf Hg; [lia|]. destruct g as [|g]; [lia|].
  cbn [g_depth_fuel Df g_lo g_par gtree_of].
  destruct (Z.leb_spec i HM) as [Le|Gt]; [reflexivity|].
  destruct (par_spec _ _ _ _ _ _ _ _ _ HR i ltac:(unfold RefDeflSafeB3.tail in Hi; lia)) as (A & B & _).
  rewrite (IH g (par i) A); [lia | unfold RefDeflSafeB3.tail in *; lia | unfold RefDeflSafeB3.tail in *; lia].
Qed.

Lemma g_depth_D : forall i, tail i -> g_depth (gtree_of t L HPf Wg) i = D i.
Proof.
  intros i Hi. unfold g_depth, RefDeflSafeO4.D. cbn [g_hi g_lo gtree_of].
  apply g_depth_fuel_D; [exact Hi | unfold RefDeflSafeB3.tail in Hi; lia | unfold RefDeflSafeB3.tail in Hi; lia].
Qed.

(* [comment removed for export] *)
Lemma leaf_pos : forall i, HM <= i <= 572 -> leafb i = true -> HM < i < 573.
Proof.
  intros i Hi Li. destruct (Z.eq_dec i HM) as [->|N]; [|lia].
  rewrite (root_internal _ _ _ _ _ _ _ _ _ HR) in Li. discriminate.
Qed.

(* [comment removed for export] *)
Lemma used_iff : forall c, 0 <= c < E -> (zt_used ztree_of c <-> arr_get FC2 c <> 0).
Proof.
  intros c Hc. unfold zt_used, zt_is_leaf_of, g_pos. cbn [zt_g ztree_of g_lo g_hi g_leaf g_code gtree_of]. split.
  - intros (i & Hi & Li & Ci). pose proof (leaf_pos i Hi Li).
    destruct (nd_cases _ _ _ _ _ _ _ _ _ HR i ltac:(unfold RefDeflSafeB3.tail; lia)) as [[A B]|A]; [rewrite <- Ci; exact B|].
    unfold RefDeflSafeB3.leafb in Li. apply Z.ltb_lt in Li. lia.
  - intros Fc. destruct (hr_cov _ _ _ _ _ _ _ _ _ HR c ltac:(unfold Vj, V0, Vscan; left; split; [lia | exact Fc])) as (i & Hi & Ei).
    exists i. unfold RefDeflSafeB3.leafb, RefDeflSafeB3.nd. rewrite Ei. unfold RefDeflSafeB3.HM in *.
    split; [| split; [apply Z.ltb_lt; lia | reflexivity]].
    destruct (Z.eq_dec i (574 - 2 * L)) as [->|N]; [| lia]. rewrite (hr_root _ _ _ _ _ _ _ _ _ HR) in Ei. lia.
Qed.

(* [comment removed for export] *)
Lemma leaf_wt : forall i, HM <= i <= 572 -> leafb i = true -> g_wt (gtree_of t L HPf Wg) i = arr_get FC2 (nd i) /\ 0 <= nd i < E.
Proof.
  intros i Hi Li. cbn [g_wt gtree_of]. pose proof (leaf_pos i Hi Li) as P.
  unfold RefDeflSafeB3.leafb in Li. apply Z.ltb_lt in Li.
  destruct (nd_cases _ _ _ _ _ _ _ _ _ HR i ltac:(unfold RefDeflSafeB3.tail; lia)) as [[A B]|A]; [|lia].
  split; [| lia]. apply (gf_wleaf _ _ _ _ _ _ GF). lia.
Qed.

(* [comment removed for export] *)
Lemma pos_wt_mono : forall i j, HM < i < 573 -> HM < j < 573 -> i < j -> leafb i = true -> Wg (nd j) <= Wg (nd i).
Proof.
  intros i j Hi Hj Hij Li. pose proof GF as [WL WF WN ND NM MIN].
  pose proof (round_of t L j Hj) as (Kj & Cj & Dj). cbv zeta in Kj, Cj, Dj. set (k := (572 - j) / 2 + 1) in *. clearbody k.
  unfold RefDeflSafeB3.leafb in Li. apply Z.ltb_lt in Li.
  destruct Cj as [-> | ->].
  - destruct (Z.eq_dec i (573 - 2 * k)) as [->|Ni]; [apply NM; exact Kj|].
    exact (proj1 (MIN k i Kj ltac:(unfold RefDeflSafeB3.HM in *; lia) ltac:(unfold RefDeflSafeB3.nd in Li; lia))).
  - exact (proj2 (MIN k i Kj ltac:(unfold RefDeflSafeB3.HM in *; lia) ltac:(unfold RefDeflSafeB3.nd in Li; lia))).
Qed.

(* [comment removed for export] *)
Lemma g_hist_len : forall b, g_hist (gtree_of t L HPf Wg) (fun i => arr_get DLq (nd i)) b = lcnt DLq (HM + 1) b.
Proof.
  intros b. unfold g_hist, RefDeflSafeO4.lcnt. cbn [g_lo g_hi g_leaf gtree_of].
  replace (Z.to_nat (572 - HM + 1)) with (S (Z.to_nat (573 - (HM + 1)))) by lia.
  rewrite zsum_shift, (root_internal _ _ _ _ _ _ _ _ _ HR). cbn [andb zind]. lia.
Qed.

Lemma g_hist_capped : forall b, g_hist (gtree_of t L HPf Wg) (fun i => Z.min (g_depth (gtree_of t L HPf Wg) i) ML) b = cntL b.
Proof.
  intros b. unfold g_hist, RefDeflSafeB3.cntL. cbn [g_lo g_hi g_leaf gtree_of].
  replace (Z.to_nat (572 - HM + 1)) with (S (Z.to_nat (572 - HM))) by lia.
  rewrite zsum_shift, (root_internal _ _ _ _ _ _ _ _ _ HR). cbn [andb zind]. rewrite Z.add_0_l.
  apply zsum_ext. intros i Hi. unfold w_cnt. rewrite g_depth_D, <- (C_min' _ _ _ _ _ _ _ _ _ HR) by (unfold RefDeflSafeB3.tail; lia). reflexivity.
Qed.

(* [comment removed for export] *)
Lemma ztree_of_kraft : kraftZ ML (g_hist (gtree_of t L HPf Wg) (fun i => arr_get DLq (nd i))) = 2 ^ ML.
Proof.
  rewrite <- Hkraft. unfold kraftZ. apply zsum_ext. intros b Hb. rewrite g_hist_len. reflexivity.
Qed.

Theorem ztree_of_ok : ztree_ok ztree_of.
Proof.
  pose proof GF as [WL WF WN ND NM MIN].
  constructor; cbn [zt_E zt_ML zt_g zt_len ztree_of].
  - exact (gtree_of_ok t FC2 DL2 L mc FCf DLf HPf DPf Wg HR GF).
  - intros i Hi Li. exact (proj2 (leaf_wt i Hi Li)).
  - lia.
  - intros c i (Hi & Li & Ci). cbn [zt_g ztree_of g_leaf g_code gtree_of] in Li, Ci. unfold g_pos in Hi. cbn [zt_g ztree_of g_lo g_hi gtree_of] in Hi.
    rewrite <- Ci. apply (dli_leaf _ _ _ _ _ HDLI); [exact (leaf_pos i Hi Li) | exact Li].
  - intros c Hc NU. apply (dli_zero _ _ _ _ _ HDLI c Hc). destruct (Z.eq_dec (arr_get FC2 c) 0) as [Z0|NZ]; [exact Z0|].
    exfalso. apply NU. apply (proj2 (used_iff c Hc)). exact NZ.
  - intros NOV c i (Hi & Li & Ci). cbn [zt_g ztree_of g_leaf g_code gtree_of] in Li, Ci, NOV. unfold g_pos in Hi, NOV. cbn [zt_g ztree_of g_lo g_hi gtree_of] in Hi, NOV.
    pose proof (leaf_pos i Hi Li) as P. rewrite <- Ci, g_depth_D by (unfold RefDeflSafeB3.tail; lia).
    apply Hnoovf; [| exact P]. apply (noovf_NI _ _ _ _ _ _ _ _ _ HR).
    intros j Hj Lj. rewrite <- g_depth_D by (unfold RefDeflSafeB3.tail; lia). apply NOV; [lia | exact Lj].
  - intros b Hb. cbn [zt_g ztree_of].
    rewrite (repair_ext ML _ cntL g_hist_capped).
    change (fun i : Z => arr_get DLq (g_code (gtree_of t L HPf Wg) i)) with (fun i : Z => arr_get DLq (nd i)).
    rewrite g_hist_len. apply Hhist. exact Hb.
  - intros (i0 & Hi0 & Li0 & Di0) i j Hi Hj Li Lj Wij. unfold g_pos in *. cbn [zt_g ztree_of g_lo g_hi g_leaf g_code g_wt gtree_of] in *.
    pose proof (leaf_pos i0 Hi0 Li0) as P0. pose proof (leaf_pos i Hi Li) as Pi. pose proof (leaf_pos j Hj Lj) as Pj.
    rewrite g_depth_D in Di0 by (unfold RefDeflSafeB3.tail; lia).
    assert (NZ : NI <> 0).
    { intros Z0. pose proof (NI0_depth _ _ _ _ _ _ _ _ _ HR Z0 i0 ltac:(unfold RefDeflSafeB3.tail; lia)). lia. }
    destruct (Z_lt_le_dec j i) as [LT|GE].
    + apply (Hrank NZ i j); try assumption; lia.
    + exfalso. destruct (Z.eq_dec i j) as [->|N]; [lia|].
      pose proof (pos_wt_mono i j Pi Pj ltac:(lia) Li). lia.
Qed.
End ZTree.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma loop2_id : forall X t mc, 2 <= ds_heap_len X -> build_tree_loop2 2%nat X t mc = (X, mc).
Proof.
  intros X t mc H. cbn [build_tree_loop2].
  replace (ds_heap_len X <? 2) with false by (symmetry; apply Z.ltb_ge; lia). reflexivity.
Qed.

(* [comment removed for export] *)
Lemma zone_two : forall HP hl (V : Z -> Prop) a b, zone_ok HP hl 573 V -> V a -> V b -> a <> b -> 2 <= hl.
Proof.
  intros HP hl V a b [pos [A B]] Va Vb Nab.
  destruct (B a Va) as [La Ea]. destruct (B b Vb) as [Lb Eb]. unfold live in La, Lb.
  destruct (Z.eq_dec (pos a) (pos b)) as [Ep|Np]; [rewrite Ep in Ea; congruence | lia].
Qed.

Section BuildTree.
Variable s : deflate_state.
Variable t : tree_id.
Local Notation E := (sd_elems t).
Local Notation ML := (sd_max_length t).
Hypothesis HP : bt_pre s t.
(* [comment removed for export] *)
Hypothesis WB : zsum (fun u => arr_get (tree_fc s t) u) 0 (Z.to_nat E) + 2 < 2 ^ 16.

Theorem build_tree_ztree :
  exists Fl L mc FCf DLf HPf DPf DL2 Wg DLq FCg BCq OLq SLq,
    let FC2 := fc_forced Fl (tree_fc s t) in
    (* [comment removed for export] *)
    build_tree s t = bt_upd s t FCg DLq HPf 1 (574 - 2 * L) DPf BCq OLq SLq mc
    /\ tree_dl (build_tree s t) t = DLq /\ max_code (build_tree s t) t = mc
    (* [comment removed for export] *)
    /\ (length Fl <= 2)%nat /\ NoDup Fl /\ (forall f, In f Fl -> 0 <= f < E /\ arr_get (tree_fc s t) f = 0 /\ f <= 2)
    /\ (forall i, arr_get FC2 i = if existsb (Z.eqb i) Fl then 1 else arr_get (tree_fc s t) i)
    /\ (forall a b, 0 <= a < E -> 0 <= b < E -> a <> b -> arr_get (tree_fc s t) a <> 0 -> arr_get (tree_fc s t) b <> 0 -> Fl = [])
    /\ (exists a b, 0 <= a < E /\ 0 <= b < E /\ a <> b /\ arr_get FC2 a <> 0 /\ arr_get FC2 b <> 0)
    (* [comment removed for export] *)
    /\ heap_result t FC2 DL2 L mc FCf DLf HPf DPf
    /\ greedy_facts t FC2 L FCf HPf Wg
    /\ DLI t FC2 L HPf DLq
    (* [comment removed for export] *)
    /\ ztree_ok (ztree_of t L HPf Wg DLq)
    /\ kraftZ ML (g_hist (gtree_of t L HPf Wg) (fun i => arr_get DLq (nd HPf i))) = 2 ^ ML
    /\ (forall c, 0 <= c < E -> (zt_used (ztree_of t L HPf Wg DLq) c <-> arr_get FC2 c <> 0))
    /\ (forall i, 574 - 2 * L <= i <= 572 -> leafb t HPf i = true ->
          g_wt (gtree_of t L HPf Wg) i = arr_get FC2 (nd HPf i) /\ 0 <= nd HPf i < E).
Proof.
  pose proof (elems_range t) as RE.
  pose proof (heap_phase_s s t HP) as H. cbv zeta in H.
  apply let_pair_elim in H. apply let_pair_elim in H.
  destruct H as (Fl & DL2 & HP2 & DP2 & L & FCf & DLf & HPf & DPf & E3 & E7 & HR & Z2 & LHP2 & LDP2 & LDL2 & RDP2 & RFC2 & RDL2 & LF & ND & FF & FCE & DLE).
  pose proof (hr_L _ _ _ _ _ _ _ _ _ HR) as RL. pose proof (ML_range t _ _ _ _ _ _ _ _ HR) as RML. pose proof (hr_mc _ _ _ _ _ _ _ _ _ HR) as Rmc.
  pose proof (HM_range _ _ _ _ _ _ _ _ _ HR) as RHM.
  pose proof E7 as E7'. rewrite E3 in E7'.
  destruct (heap_phase_o s t (tree_fc s t) (ds_bl_count s) (ds_opt_len s) (ds_static_len s) _ Fl DL2 HP2 DP2 L FCf DLf HPf DPf E7' RL Z2 LHP2 LDP2 LDL2
              (tree_lens_fc _ _ (bp_tl _ _ HP)) RDP2 RFC2 RDL2 LF FCE ltac:(intros i; pose proof (bp_fc _ _ HP i); lia) WB) as [Wg GF].
  (* [comment removed for export] *)
  assert (NOF : forall a b, 0 <= a < E -> 0 <= b < E -> a <> b -> arr_get (tree_fc s t) a <> 0 -> arr_get (tree_fc s t) b <> 0 -> Fl = []).
  { intros a b Ha Hb Nab Fa Fb.
    pose proof (LHP s t HP) as LHP0. pose proof (tree_lens_dl s t (bp_tl _ _ HP)) as LDL0.
    destruct (loop1_spec s t (Z.to_nat E) 0 (-1) (tree_fc s t) (tree_dl s t) (ds_heap s) 0 (ds_depth s) (ds_bl_count s) (ds_opt_len s) (ds_static_len s) (max_code s t)
                ltac:(lia) ltac:(lia) ltac:(lia) LHP0 LDL0)
      as (HP1 & HL1 & DL1 & DP1 & mc1 & E1 & B1 & B1' & LHP1 & LDL1 & Z1 & _).
    { apply (zone_ok_ext _ _ _ (fun _ => False)); [| apply zone_ok_empty]. unfold Vscan. intros u. lia. }
    { lia. } { intros; lia. } { intros; lia. } { lia. }
    pose proof (zone_two HP1 HL1 (Vscan (tree_fc s t) E) a b Z1 ltac:(unfold Vscan; split; [lia | exact Fa]) ltac:(unfold Vscan; split; [lia | exact Fb]) Nab) as HL2.
    assert (S0 : set_heap_max (set_heap_len s 0) HEAP_SIZE = bt_upd s t (tree_fc s t) (tree_dl s t) (ds_heap s) 0 573 (ds_depth s) (ds_bl_count s) (ds_opt_len s) (ds_static_len s) (max_code s t)).
    { rewrite <- (bt_upd_self s t) at 1. autorewrite with btupd. reflexivity. }
    pose proof E3 as E3'. rewrite S0, E1 in E3'. cbn [fst snd] in E3'. rewrite loop2_id in E3' by (rewrite bt_heap_len; exact HL2). cbn [fst snd] in E3'.
    rewrite bt_set_max_code in E3'.
    pose proof (f_equal (fun x => tree_fc x t) E3') as EF. cbv beta in EF. rewrite !bt_tree_fc in EF.
    destruct Fl as [|f l]; [reflexivity|]. exfalso.
    destruct (FF f (or_introl eq_refl)) as (Rf & Zf & _). pose proof (FCE f) as X. rewrite <- EF, Zf in X. cbn [existsb] in X. rewrite Z.eqb_refl in X. cbn in X. lia. }
  (* [comment removed for export] *)
  assert (TWO : exists a b, 0 <= a < E /\ 0 <= b < E /\ a <> b /\ arr_get (fc_forced Fl (tree_fc s t)) a <> 0 /\ arr_get (fc_forced Fl (tree_fc s t)) b <> 0).
  { pose proof (zone_ok_mem _ _ _ _ 1 Z2 ltac:(unfold live; left; lia)) as M1. pose proof (zone_ok_mem _ _ _ _ 2 Z2 ltac:(unfold live; left; lia)) as M2.
    unfold Vscan in M1, M2. exists (arr_get HP2 1), (arr_get HP2 2).
    split; [lia|]. split; [lia|]. split; [| split; [exact (proj2 M1) | exact (proj2 M2)]].
    intros EQ. pose proof (zone_ok_inj _ _ _ _ 1 2 Z2 ltac:(unfold live; left; lia) ltac:(unfold live; left; lia) EQ). lia. }
  rewrite build_tree_unfold. cbv zeta. rewrite E7.
  set (p1 := build_tree_loop1 (Z.to_nat E) (set_heap_max (set_heap_len s 0) HEAP_SIZE) t E 0 (-1)) in *.
  set (p2 := build_tree_loop2 2 (fst p1) t (snd p1)) in *.
  set (mc := snd p2) in *.
  set (FC := tree_fc s t) in *. set (FC2 := fc_forced Fl FC) in *.
  pose proof (LBC s t HP) as LB.
  assert (ROL : 0 <= ol_forced Fl (ds_opt_len s) < 2 ^ 64).
  { unfold ol_forced. destruct Fl as [|a [|b [|c l]]]; cbn [fold_left]; [apply (bp_ol _ _ HP) | apply wrap64_range | apply wrap64_range | cbn in LF; lia]. }
  assert (RSL : 0 <= sl_forced t Fl (ds_static_len s) < 2 ^ 64).
  { unfold sl_forced. destruct (stree_has t); [| apply (bp_sl _ _ HP)].
    destruct Fl as [|a [|b [|c l]]]; cbn [fold_left]; [apply (bp_sl _ _ HP) | apply wrap64_range | apply wrap64_range | cbn in LF; lia]. }
  destruct (gen_bitlen_exact t _ _ _ _ _ _ _ _ HR s (ds_bl_count s) (ol_forced Fl (ds_opt_len s)) (sl_forced t Fl (ds_static_len s)) LB ROL RSL)
    as (DL' & BC' & OL' & SL' & EG & HD & RO & RS & LB' & RBC & NOOVF & HIST & KRF & RANK).
  change (RefDeflSafeB3.HM L) with (574 - 2 * L) in EG. rewrite EG.
  (* [comment removed for export] *)
  set (X := bt_upd s t FCf DL' HPf 1 (574 - 2 * L) DPf BC' OL' SL' mc).
  assert (TLX : tree_lens X) by (subst X; apply bt_tree_lens; try assumption; [apply (bp_tl _ _ HP) | apply (hr_lfc _ _ _ _ _ _ _ _ _ HR) | apply (dli_len _ _ _ _ _ HD) | apply (hr_lhp _ _ _ _ _ _ _ _ _ HR) | apply (hr_ldp _ _ _ _ _ _ _ _ _ HR)]).
  unfold gen_codes. rewrite <- (stf_self X t).
  destruct (gen_codes_typed (Z.to_nat (mc + 1)) X t (tree_fc X t) (gen_codes_loop1 16 (ds_bl_count (set_tree_fc X t (tree_fc X t))) (arr_make (MAX_BITS + 1) 0) 0 1) mc 0)
    as (FCg & EC & LFCg & RFCg).
  { subst X. rewrite bt_tree_fc. apply (hr_lfc _ _ _ _ _ _ _ _ _ HR). }
  { subst X. rewrite bt_tree_fc. apply (hr_fcr _ _ _ _ _ _ _ _ _ HR). }
  rewrite EC. subst X. rewrite bt_set_tree_fc.
  exists Fl, L, mc, FCf, DLf, HPf, DPf, DL2, Wg, DL', FCg, BC', OL', SL'.
  cbv zeta. fold FC2.
  split; [reflexivity|]. split; [apply bt_tree_dl|]. split; [apply bt_max_code|].
  split; [exact LF|]. split; [exact ND|]. split; [exact FF|]. split; [exact FCE|]. split; [exact NOF|]. split; [exact TWO|].
  split; [exact HR|]. split; [exact GF|]. split; [exact HD|].
  split; [exact (ztree_of_ok t FC2 DL2 L mc FCf DLf HPf DPf Wg DL' HR GF HD NOOVF HIST RANK)|].
  split; [exact (ztree_of_kraft t FC2 DL2 L mc FCf DLf HPf DPf Wg DL' HR KRF)|].
  split; [intros c Hc; exact (used_iff t FC2 DL2 L mc FCf DLf HPf DPf Wg DL' HR c Hc)|].
  intros i Hi Li. exact (leaf_wt t FC2 DL2 L mc FCf DLf HPf DPf Wg HR GF i Hi Li).
Qed.
End BuildTree.
