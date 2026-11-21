(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (munmap's maps_subtract cut; the reserved ledger). *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.Lib Require Import PropExec MState Mem Exec ITree Nodes RzCPS NodesA NodesA_mm.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.A15 Require Import ImageA.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.AS Require Import AsanAcct BackingAlgebra.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.A15 Require Import Layout RT_iface D_defs RT_state RT_rep RT_init RT_sys_stmt RT_sys_fixed.
(* [comment removed for export] *)
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma Permutation_map_remove : forall l l' a, Permutation l l' -> Permutation (map_remove l a) (map_remove l' a).
Proof.
  intros l l' a H. unfold map_remove. induction H as [|x l l' _ IH|x y l|l l' l'' _ IH1 _ IH2]; cbn [List.filter].
  - constructor.
  - destruct (negb (bv_eqb (fst x) a)); [constructor|]; exact IH.
  - destruct (negb (bv_eqb (fst x) a)), (negb (bv_eqb (fst y) a)); try constructor; apply Permutation_refl.
  - exact (Permutation_trans IH1 IH2).
Qed.

Lemma FOP_filter : forall {X} (R : X -> X -> Prop) f l, ForallOrdPairs R l -> ForallOrdPairs R (List.filter f l).
Proof.
  intros X R f l H. induction H as [|x l Hx Hl IH]; cbn [List.filter]; [constructor|].
  destruct (f x); [|exact IH]. constructor; [|exact IH].
  apply Forall_forall. intros y Hy. apply filter_In in Hy as [Hy _]. exact (proj1 (Forall_forall _ _) Hx y Hy).
Qed.

(* [comment removed for export] *)

Lemma FOP_perm : forall {X} (R : X -> X -> Prop), (forall x y, R x y -> R y x) ->
  forall l l', Permutation l l' -> ForallOrdPairs R l -> ForallOrdPairs R l'.
Proof.
  intros X R Hs l l' H. induction H as [|x l l' Hp IH|x y l|l l' l'' _ IH1 _ IH2]; intros HF.
  - constructor.
  - inversion HF as [|? ? Hx Hl]; subst. constructor; [|exact (IH Hl)].
    apply Forall_forall. intros z Hz. apply (proj1 (Forall_forall _ _) Hx). exact (Permutation_in _ (Permutation_sym Hp) Hz).
  - inversion HF as [|? ? Hy Hl]; subst. inversion Hl as [|? ? Hx Hl']; subst.
    inversion Hy as [|? ? Hyx Hyl]; subst.
    constructor; [constructor; [exact (Hs _ _ Hyx)| exact Hx]|]. constructor; [exact Hyl| exact Hl'].
  - exact (IH2 (IH1 HF)).
Qed.


Lemma FOP_In_apart : forall {X} (R : X -> X -> Prop) l x y, ForallOrdPairs R l -> In x l -> In y l -> x <> y -> R x y \/ R y x.
Proof.
  intros X R l x y H. induction H as [|p l Hp Hl IH]; intros Hx Hy Hne; [destruct Hx|].
  destruct Hx as [<-|Hx], Hy as [<-|Hy].
  - exfalso. exact (Hne eq_refl).
  - left. exact (proj1 (Forall_forall _ _) Hp y Hy).
  - right. exact (proj1 (Forall_forall _ _) Hp x Hx).
  - exact (IH Hx Hy Hne).
Qed.

Lemma FOP_app_cross : forall {X} (R : X -> X -> Prop) l1 l2, ForallOrdPairs R (l1 ++ l2) ->
  forall x y, In x l1 -> In y l2 -> R x y.
Proof.
  intros X R l1. induction l1 as [|p l1 IH]; intros l2 H x y Hx Hy; [destruct Hx|].
  cbn [app] in H. inversion H as [|? ? Hp Hl]; subst. destruct Hx as [<-|Hx].
  - apply (proj1 (Forall_forall _ _) Hp). apply in_or_app. right. exact Hy.
  - exact (IH l2 Hl x y Hx Hy).
Qed.

Lemma iv_apart_sym : forall p q, iv_apart p q -> iv_apart q p.
Proof. intros p q H. unfold iv_apart in *. lia. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma sum_count_ext_on : forall P Q l,
  (forall p, In p l -> forall x, B p <= x < B p + S p -> P x = Q x) -> sum_count P l = sum_count Q l.
Proof.
  intros P Q l H. induction l as [|p l IH]; cbn [sum_count]; [reflexivity|].
  rewrite IH by (intros q Hq; apply H; now right). f_equal. unfold iv_count. apply zcount_ext.
  intros x Hx. pose proof (S_range p). rewrite Z2Nat.id in Hx by lia. exact (H p (or_introl eq_refl) x Hx).
Qed.

Lemma sum_count_partition : forall P f l,
  sum_count P l = sum_count P (List.filter f l) + sum_count P (List.filter (fun p => negb (f p)) l).
Proof.
  intros P f l. induction l as [|p l IH]; cbn [List.filter sum_count]; [reflexivity|].
  destruct (f p); cbn [negb sum_count]; rewrite IH; lia.
Qed.

Lemma sum_count_In_ge : forall P l p, In p l -> iv_count P p <= sum_count P l.
Proof.
  intros P l. induction l as [|q l IH]; intros p Hp; [destruct Hp|]. cbn [sum_count].
  pose proof (zcount_nonneg P (B q) (Z.to_nat (S q))). pose proof (sum_count_nonneg P l). unfold iv_count in *.
  destruct Hp as [<-|Hp]; [lia|]. specialize (IH p Hp). unfold iv_count in IH. lia.
Qed.

(* [comment removed for export] *)
(* At LPS 08b1429 munmap rebuilds [vm_maps] with [maps_subtract] (Mmap.v, mmap_fixed_destroyed_next),
   not [map_remove]; these facts carry the ledger invariants across that cut. *)
Lemma FOP_app_intro : forall {X} (R : X -> X -> Prop) l1 l2,
  ForallOrdPairs R l1 -> ForallOrdPairs R l2 -> (forall x y, In x l1 -> In y l2 -> R x y) -> ForallOrdPairs R (l1 ++ l2).
Proof.
  intros X R l1. induction l1 as [|p l1 IH]; intros l2 H1 H2 H12; [exact H2|].
  inversion H1 as [|? ? Hf Hl]; subst. cbn [app]. constructor.
  - apply Forall_app. split; [exact Hf|]. apply Forall_forall. intros q Hq. apply H12; [left; reflexivity | exact Hq].
  - apply IH; [exact Hl | exact H2 |]. intros x y Hx Hy. apply H12; [right; exact Hx | exact Hy].
Qed.

Lemma FOP_iv_subtract : forall (a sz : word) lo hi, iv_wf (a, sz) -> lo <= hi ->
  ForallOrdPairs iv_apart (iv_subtract a sz lo hi).
Proof.
  intros a sz lo hi Hwf Hlh. unfold iv_wf, B, S in Hwf. cbn [fst snd] in Hwf.
  pose proof (u64_range a) as Ra. pose proof (u64_range sz) as Rs. unfold iv_subtract. cbv zeta.
  destruct (Z.ltb_spec (bv_unsigned a) lo); destruct (Z.ltb_spec hi (bv_unsigned a + bv_unsigned sz)); cbn [app].
  all: repeat first [apply FOP_nil | apply FOP_cons | apply Forall_nil | apply Forall_cons].
  all: unfold iv_apart; cbn [fst snd]; rewrite !unsigned_lit by lia; lia.
Qed.

Lemma FOP_maps_subtract : forall l lo hi, ForallOrdPairs iv_apart l -> ivs_wf l -> lo <= hi ->
  ForallOrdPairs iv_apart (maps_subtract l lo hi).
Proof.
  induction l as [|[a sz] l IH]; intros lo hi Hs Hwf Hlh; [constructor|].
  apply ivs_wf_cons_inv in Hwf as [Ha Hl]. inversion Hs as [|p' l' Hf Htl]; subst.
  cbn [maps_subtract]. apply FOP_app_intro; [apply FOP_iv_subtract; assumption | apply IH; assumption |].
  intros p q Hp Hq.
  destruct (iv_subtract_pieces' a sz lo hi p Ha Hp) as (P1 & P2 & _).
  destruct (maps_subtract_pieces' l lo hi q Hl Hq) as (r & Hr & Q1 & Q2 & _).
  pose proof (proj1 (Forall_forall _ _) Hf r Hr) as D. unfold iv_apart in *. cbn [fst snd] in *. lia.
Qed.

(* Cutting out an exact mapping [(a, n)] removes it and keeps every positive interval apart from it. *)
Lemma filter_vpos_munmap_cut : forall l (a n : word), ivs_wf l -> 0 < bv_unsigned n ->
  (forall e, In e l -> vpos e = true -> e = (a, n) \/ iv_apart e (a, n)) ->
  List.filter vpos (maps_subtract l (bv_unsigned a) (bv_unsigned a + bv_unsigned n)) = map_remove (List.filter vpos l) a.
Proof.
  intros l. induction l as [|[b s] l IH]; intros a n Wl Hn Hcond; [reflexivity|].
  apply ivs_wf_cons_inv in Wl as [Wb Wl'].
  cbn [maps_subtract]. rewrite filter_app. rewrite (IH a n Wl' Hn (fun e He => Hcond e (or_intror He))).
  pose proof (u64_range a) as Ra. pose proof (u64_range b) as Rb. pose proof (u64_range s) as Rs.
  cbn [List.filter]. destruct (vpos (b, s)) eqn:Ev.
  - assert (Hs : 0 < bv_unsigned s) by (unfold vpos in Ev; cbn [snd] in Ev; apply Z.ltb_lt; exact Ev).
    destruct (Hcond (b, s) (or_introl eq_refl) Ev) as [E|D].
    + injection E as Eb Es. subst b s.
      unfold iv_subtract. cbv zeta.
      rewrite (proj2 (Z.ltb_ge (bv_unsigned a) (bv_unsigned a))) by lia.
      rewrite (proj2 (Z.ltb_ge (bv_unsigned a + bv_unsigned n) (bv_unsigned a + bv_unsigned n))) by lia.
      cbn [app List.filter]. unfold map_remove. cbn [List.filter fst]. rewrite bv_eqb_refl. reflexivity.
    + unfold iv_apart in D. cbn [fst snd] in D.
      assert (Hsub : iv_subtract b s (bv_unsigned a) (bv_unsigned a + bv_unsigned n) = [(b, s)]).
      { unfold iv_subtract. cbv zeta. destruct D as [D|D].
        - rewrite (proj2 (Z.ltb_lt (bv_unsigned b) (bv_unsigned a))) by lia.
          rewrite (proj2 (Z.ltb_ge (bv_unsigned a + bv_unsigned n) (bv_unsigned b + bv_unsigned s))) by lia.
          rewrite Z.min_l by lia. rewrite Z_to_bv_bv_unsigned. reflexivity.
        - rewrite (proj2 (Z.ltb_ge (bv_unsigned b) (bv_unsigned a))) by lia.
          rewrite (proj2 (Z.ltb_lt (bv_unsigned a + bv_unsigned n) (bv_unsigned b + bv_unsigned s))) by lia.
          rewrite Z.max_l by lia.
          replace (bv_unsigned b + bv_unsigned s - bv_unsigned b) with (bv_unsigned s) by lia.
          rewrite !Z_to_bv_bv_unsigned. reflexivity. }
      assert (Hne : bv_eqb b a = false).
      { destruct (bv_eqb b a) eqn:Eb; [|reflexivity]. exfalso. apply bv_eqb_eq in Eb. subst b. lia. }
      rewrite Hsub. cbn [List.filter]. rewrite Ev. cbn [app].
      unfold map_remove. cbn [List.filter fst]. rewrite Hne. reflexivity.
  - assert (HL : forall q, In q (iv_subtract b s (bv_unsigned a) (bv_unsigned a + bv_unsigned n)) -> vpos q = false).
    { intros q Hq. destruct (iv_subtract_pieces' b s _ _ q Wb Hq) as (Q1 & Q2 & _).
      unfold vpos in Ev |- *. cbn [snd] in Ev. apply Z.ltb_ge in Ev. apply Z.ltb_ge. lia. }
    assert (Hnil : forall L : list (word * word), (forall q, In q L -> vpos q = false) -> List.filter vpos L = []).
    { intros L. induction L as [|q L IHL]; intros HL0; [reflexivity|]. cbn [List.filter].
      rewrite (HL0 q (or_introl eq_refl)). apply IHL. intros q' Hq'. apply HL0. right. exact Hq'. }
    rewrite (Hnil _ HL). reflexivity.
Qed.

(* No cut makes a zero-size piece out of a positive interval. *)
Lemma zcount_iv_subtract : forall (a sz : word) lo hi, lo <= hi ->
  (length (iv_subtract a sz lo hi) + (if vpos (a, sz) then 1 else 0) <= 1 + length (List.filter vpos (iv_subtract a sz lo hi)))%nat.
Proof.
  intros a sz lo hi Hlh. pose proof (u64_range a) as Ra. pose proof (u64_range sz) as Rs.
  assert (Hv : forall (b : word) z, 0 < z < 2^64 -> vpos (b, Z_to_bv 64 z) = true)
    by (intros b z Hz; unfold vpos; cbn [snd]; rewrite unsigned_lit by lia; apply Z.ltb_lt; lia).
  unfold iv_subtract. cbv zeta. destruct (vpos (a, sz)) eqn:Ev.
  - assert (Hs : 0 < bv_unsigned sz) by (unfold vpos in Ev; cbn [snd] in Ev; apply Z.ltb_lt; exact Ev).
    destruct (Z.ltb_spec (bv_unsigned a) lo); destruct (Z.ltb_spec hi (bv_unsigned a + bv_unsigned sz)); cbn [app List.filter];
      rewrite ?(Hv a (Z.min (bv_unsigned sz) (lo - bv_unsigned a))) by lia;
      rewrite ?(Hv (Z_to_bv 64 (Z.max (bv_unsigned a) hi)) (bv_unsigned a + bv_unsigned sz - Z.max (bv_unsigned a) hi)) by lia;
      cbn [length]; lia.
  - assert (Hs : bv_unsigned sz <= 0) by (unfold vpos in Ev; cbn [snd] in Ev; apply Z.ltb_ge; exact Ev).
    destruct (Z.ltb_spec (bv_unsigned a) lo); destruct (Z.ltb_spec hi (bv_unsigned a + bv_unsigned sz)); cbn [app List.filter];
      repeat match goal with |- context [vpos ?q] => destruct (vpos q) end; cbn [length]; lia.
Qed.

Lemma zcount_maps_subtract : forall l lo hi, lo <= hi ->
  (length (maps_subtract l lo hi) + length (List.filter vpos l) <= length l + length (List.filter vpos (maps_subtract l lo hi)))%nat.
Proof.
  induction l as [|[a sz] l IH]; intros lo hi Hlh; [cbn; lia|].
  cbn [maps_subtract List.filter length].
  pose proof (IH lo hi Hlh) as H2. pose proof (zcount_iv_subtract a sz lo hi Hlh) as H1.
  (* the cut of the head interval is kept opaque: [iv_subtract] is itself an append, and
     [rewrite !length_app] would otherwise split its length in the goal, away from [H1] *)
  set (IC := iv_subtract a sz lo hi) in *. clearbody IC.
  rewrite filter_app, !length_app.
  destruct (vpos (a, sz)) eqn:Ev; rewrite ?Ev in H1; cbn [length] in *; lia.
Qed.

Lemma zbound_maps_subtract : forall l lo hi, lo <= hi ->
  Z.of_nat (length l) <= Z.of_nat (length (List.filter vpos l)) + 1 ->
  Z.of_nat (length (maps_subtract l lo hi)) <= Z.of_nat (length (List.filter vpos (maps_subtract l lo hi))) + 1.
Proof. intros l lo hi Hlh H. pose proof (zcount_maps_subtract l lo hi Hlh) as C. lia. Qed.

Lemma eager_munmap_exact : forall mo (a n : word), model_ivs_wf mo ->
  ForallOrdPairs iv_apart (vm_maps (m_vmmaps mo)) -> In (a, n) (vm_maps (m_vmmaps mo)) -> 0 < bv_unsigned n ->
  (forall x, bv_unsigned a <= x < bv_unsigned a + bv_unsigned n ->
     covered (vm_noaccess (m_vmmaps mo) ++ m_vm_lazy mo) x = false) ->
  eager_used (mdl_munmap mo a n) + bv_unsigned n <= eager_used mo.
Proof.
  intros mo a n Hwf Hsep Hin Hpos Hnc. pose proof Hwf as (Wm & Wn & Wl & _). pose proof (u64_range n) as Rn.
  remember (bv_unsigned a) as lo eqn:Elo. remember (lo + bv_unsigned n) as hi eqn:Ehi.
  assert (Hlh : lo <= hi) by lia.
  destruct (maps_subtract_sem (vm_maps (m_vmmaps mo)) lo hi Wm Hlh) as (Wr & Sm & _).
  assert (Wm' : ivs_wf (vm_maps (m_vmmaps (mdl_munmap mo a n)))).
  { rewrite mdl_munmap_vmmaps. cbn [vm_maps]. rewrite <- Elo, <- Ehi. exact Wr. }
  rewrite (eager_used_sem' _ Wm'), (eager_used_sem' _ Wm). rewrite mdl_munmap_vmmaps, mdl_munmap_lazy.
  cbn [vm_maps vm_noaccess]. rewrite <- Elo, <- Ehi. rewrite Sm. cbv beta.
  set (l := vm_maps (m_vmmaps mo)) in *.
  set (Q := fun x => negb (covered (vm_noaccess (m_vmmaps mo) ++ m_vm_lazy mo) x)).
  (* [comment removed for export] *)
  match goal with |- sum_count ?P l + _ <= _ =>
    assert (E1 : sum_count P l = sum_count (fun x => Q x && negb (in_rng lo hi x)) l) end.
  { apply sum_count_ext. intros x. unfold Q. cbv beta.
    rewrite !covered_app, (covered_subtract _ lo hi x Wn Hlh), (covered_subtract _ lo hi x Wl Hlh).
    destruct (covered (vm_noaccess (m_vmmaps mo)) x), (covered (m_vm_lazy mo) x), (in_rng lo hi x); reflexivity. }
  rewrite E1.
  assert (Hsplit : forall (P R : Z -> bool) l0,
             sum_count P l0 = sum_count (fun x => P x && R x) l0 + sum_count (fun x => P x && negb (R x)) l0).
  { intros P R l0. induction l0 as [|q l0 IH]; cbn [sum_count]; [reflexivity|]. unfold iv_count in *.
    rewrite (zcount_and_split P R). lia. }
  rewrite (Hsplit Q (in_rng lo hi) l).
  (* [comment removed for export] *)
  assert (Hn : iv_count (fun x => Q x && in_rng lo hi x) (a, n) = bv_unsigned n).
  { unfold iv_count, B, S. cbn [fst snd].
    rewrite zcount_true by (intros x Hx; rewrite Z2Nat.id in Hx by lia; cbv beta; unfold Q; cbv beta;
      rewrite (Hnc x ltac:(lia)); cbn [negb andb]; unfold in_rng;
      rewrite (proj2 (Z.leb_le lo x)) by lia; rewrite (proj2 (Z.ltb_lt x hi)) by lia; reflexivity).
    apply Z2Nat.id. lia. }
  pose proof (sum_count_In_ge (fun x => Q x && in_rng lo hi x) l (a, n) Hin) as Hge.
  lia.
Qed.

(* [comment removed for export] *)
Lemma lazy_in_maps_munmap' : forall mo (a n : word), model_ivs_wf mo -> lazy_in_maps mo ->
  ForallOrdPairs iv_apart (vm_maps (m_vmmaps mo)) -> In (a, n) (vm_maps (m_vmmaps mo)) -> 0 < bv_unsigned n ->
  lazy_in_maps (mdl_munmap mo a n).
Proof.
  intros mo a n (Wm & _ & Wl & _) H Hsep Hin Hpos iv Hiv Hsz. rewrite mdl_munmap_lazy in Hiv. rewrite mdl_munmap_vmmaps. cbn [vm_maps].
  destruct (maps_subtract_pieces' _ _ _ iv Wl Hiv) as (r & Hr & P1 & P2 & P3).
  destruct (H r Hr ltac:(lia)) as (e & He & E1 & E2).
  destruct (maps_subtract_contains' _ (bv_unsigned a) (bv_unsigned a + bv_unsigned n) e
              (bv_unsigned (fst iv)) (bv_unsigned (fst iv) + bv_unsigned (snd iv)) Wm He
              ltac:(lia) ltac:(lia) ltac:(lia) P3) as (e' & He' & F1 & F2).
  exists e'. split; [exact He'| lia].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Theorem munmap_ok : munmap_node.
Proof.
  intros Σ Σ' PMc Pm K mb len HPMc _ EL Eaw Hsm Hperm' Heg HL Haw Heg38 Hlen Hlal Hmb0 Hal Hend Hm.
  assert (EA : rtA_allow Σ' = rtA_allow Σ) by (unfold rtA_allow; rewrite Eaw, EL; reflexivity).
  unfold ASTA. cbn [rt_allow ARTM RTA]. rewrite EA.
  pose proof HL as HL'. unfold layout_ok in HL'. destruct HL' as ((Hsp1 & Hsp2) & _).
  unfold l_ACEIL, STACK_WIN, sp_window_lo, sp_window_hi in *.
  assert (Hrd : page_round_up_Z len = len) by (apply AllocSim.page_round_up_Z_aligned; [lia| unfold page_size; exact Hlal]).
  pose proof (A_bytes_rtA_allow Σ HL Haw) as HAB. unfold CREDIT0 in HAB.
  apply (ast_munmap asegs SEGTOP_A asegs_wx asegs_below (rtA_allow Σ) Pm (fun mo => ARTM_A Σ mo /\ PMc mo)
           K (fun mo => ARTM_A Σ' mo /\ PMc mo) mb len).
  - lia.
  - exact Hmb0.
  - unfold page_size. exact Hal.
  - rewrite Hrd. unfold TASK_SIZE. lia.
  - intros ms HPm. destruct (Hm ms HPm) as (S1 & S2 & S3 & S4). rewrite Hrd. repeat (split; [assumption|]). exact S4.
  - intros mo (HA & HPc). pose proof HA as (Hperm & Eres & Elim & Heu & (Hwf & Hlz & Hsep & Hisp & Hcf & Hsl & Hzb & Hnp)).
    rewrite Hrd.
    assert (Eua : bv_unsigned (Z_to_bv 64 mb) = mb) by (apply unsigned_lit; lia).
    assert (Eul : bv_unsigned (Z_to_bv 64 len) = len) by (apply unsigned_lit; lia).
    assert (HinR : In (Z_to_bv 64 mb, Z_to_bv 64 len) (rt_maps Σ)) by (unfold rt_maps; apply in_or_app; left; exact Hsm).
    assert (Hin : In (Z_to_bv 64 mb, Z_to_bv 64 len) (vm_maps (m_vmmaps mo))) by exact (artm_in_maps Σ mo _ HA HinR).
    assert (HsepR : ForallOrdPairs iv_apart (rt_maps Σ)) by exact (FOP_perm _ iv_apart_sym _ _ Hperm (FOP_filter _ vpos _ Hsep)).
    (* [comment removed for export] *)
    assert (Hnc : forall x, bv_unsigned (Z_to_bv 64 mb) <= x < bv_unsigned (Z_to_bv 64 mb) + bv_unsigned (Z_to_bv 64 len) ->
                  covered (vm_noaccess (m_vmmaps mo) ++ m_vm_lazy mo) x = false).
    { intros x Hx. destruct (covered (vm_noaccess (m_vmmaps mo) ++ m_vm_lazy mo) x) eqn:Hc; [|reflexivity].
      exfalso. pose proof (Hcf x Hc) as H0. unfold covered in H0. apply existsb_exists in H0 as (q & Hq & Hqx).
      unfold rt_maps in HsepR. pose proof (FOP_app_cross _ _ _ HsepR _ q Hsm Hq) as D.
      unfold in_iv, in_rng, B, S in Hqx. apply andb_prop in Hqx as [Q1 Q2]. apply Z.leb_le in Q1. apply Z.ltb_lt in Q2.
      unfold iv_apart in D. cbn [fst snd] in D. lia. }
    assert (Hcut : forall e, In e (vm_maps (m_vmmaps mo)) -> vpos e = true ->
                   e = (Z_to_bv 64 mb, Z_to_bv 64 len) \/ iv_apart e (Z_to_bv 64 mb, Z_to_bv 64 len)).
    { intros [b s] He _. destruct (bv_eqb b (Z_to_bv 64 mb) && bv_eqb s (Z_to_bv 64 len)) eqn:E.
      - apply andb_true_iff in E as [E1 E2]. apply bv_eqb_eq in E1. apply bv_eqb_eq in E2. subst b s. left. reflexivity.
      - right. assert (Hne : (b, s) <> (Z_to_bv 64 mb, Z_to_bv 64 len))
          by (intros Eq; injection Eq as -> ->; rewrite !bv_eqb_refl in E; cbn in E; discriminate E).
        destruct (FOP_In_apart _ _ _ _ Hsep He Hin Hne) as [D|D]; [exact D| exact (iv_apart_sym _ _ D)]. }
    split; [exact Hwf|].
    split.
    { unfold map_has. apply existsb_exists. exists (Z_to_bv 64 mb, Z_to_bv 64 len). split; [exact Hin|].
      cbn [fst snd]. rewrite !bv_eqb_refl. reflexivity. }
    split.
    { rewrite overlap_sum_zero; [rewrite Elim; unfold E0_MAX, VMLIMIT in *; lia|].
      apply Forall_forall. intros q Hq. apply filter_In in Hq as [Hq Hb]. apply negb_true_iff in Hb.
      assert (Hne : q <> (Z_to_bv 64 mb, Z_to_bv 64 len)) by (intros ->; cbn [fst] in Hb; rewrite bv_eqb_refl in Hb; discriminate).
      destruct (FOP_In_apart _ _ _ _ Hsep Hq Hin Hne) as [D|D]; unfold iv_apart in D; cbn [fst snd] in D; rewrite Eua, Eul in D;
        unfold B, S; lia. }
    split.
    + (* [comment removed for export] *)
      split.
      { rewrite mdl_munmap_vmmaps. cbn [vm_maps].
        rewrite (filter_vpos_munmap_cut _ (Z_to_bv 64 mb) (Z_to_bv 64 len) (proj1 Hwf) ltac:(rewrite Eul; lia) Hcut).
        exact (Permutation_trans (Permutation_map_remove _ _ _ Hperm) (Permutation_sym Hperm')). }
      split.
      { apply (artm_res_step mo _ Eres); [rewrite mdl_munmap_vmmaps; reflexivity|].
        intros e He. left. rewrite mdl_munmap_vmmaps in He. cbn [vm_maps] in He.
        rewrite (filter_vpos_munmap_cut _ (Z_to_bv 64 mb) (Z_to_bv 64 len) (proj1 Hwf) ltac:(rewrite Eul; lia) Hcut) in He.
        unfold map_remove in He. apply List.filter_In in He as [He _]. exact He. }
      split; [rewrite mdl_munmap_vmmaps; cbn [vm_limit]; exact Elim|].
      split.
      { pose proof (eager_munmap_exact mo _ _ Hwf Hsep Hin ltac:(rewrite Eul; lia) Hnc) as Hle. rewrite Eul in Hle. lia. }
      pose proof Hwf as (Wm & Wn & Wl & _).
      split; [apply model_ivs_wf_munmap; exact Hwf|].
      split; [exact (lazy_in_maps_munmap' mo _ _ Hwf Hlz Hsep Hin ltac:(rewrite Eul; lia))|].
      split; [rewrite mdl_munmap_vmmaps; cbn [vm_maps]; apply FOP_maps_subtract; [exact Hsep| exact Wm| rewrite Eua, Eul; lia]|].
      split; [rewrite mdl_munmap_vmmaps; cbn [vm_init_sp]; rewrite EL; exact Hisp|].
      split.
      { intros z Hz. rewrite EL. apply Hcf. rewrite mdl_munmap_vmmaps, mdl_munmap_lazy in Hz.
        cbn [vm_noaccess] in Hz. rewrite covered_app in Hz |- *. rewrite Eua, Eul in Hz.
        apply orb_true_iff in Hz as [Hz|Hz]; apply orb_true_iff;
          [left; refine (covered_subtract_le _ _ _ _ Wn _ Hz); lia | right; refine (covered_subtract_le _ _ _ _ Wl _ Hz); lia]. }
      split.
      { apply (shadow_lazy_cut_nc mo _ mb (mb + len) Hwf ltac:(lia) Hal ltac:(rewrite Z.add_mod, Hal, Hlal by lia; reflexivity) Hsl).
        - rewrite mdl_munmap_lazy, Eua, Eul. reflexivity.
        - rewrite mdl_munmap_vmmaps. cbn [vm_noaccess]. rewrite Eua, Eul. reflexivity.
        - intros x Hx. pose proof (Hnc x ltac:(rewrite Eua, Eul; lia)) as C. rewrite covered_app in C.
          apply orb_false_iff in C as [_ C]. exact C. }
      (* [comment removed for export] *)
      split; [unfold maps_zbound; rewrite mdl_munmap_vmmaps; cbn [vm_maps]; apply zbound_maps_subtract; [rewrite Eua, Eul; lia| exact Hzb]|].
      (* [comment removed for export] *)
      apply NodesA_madv.noaccess_pos_munmap; [exact Hwf| exact Hnp].
    + apply (HPMc mo); [apply mdl_munmap_fds| apply mdl_munmap_fs| apply mdl_munmap_reader| exact HPc].
Qed.
