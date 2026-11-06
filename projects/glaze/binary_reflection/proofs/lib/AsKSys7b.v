(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.glaze.binary_reflection.lib Require BvWfKernel.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require WdZS.
#[local] Ltac Zify.zify ::= WdZS.wd_zs_stock.   (* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap Mprotect.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32 OSSVerify.Proofs.glaze.binary_reflection.lib.Spec4 OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.Common.BackingAlgebra OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys6 OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsArith3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrameE3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvZone3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvHoleP3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvRoom3. Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Spec4.AgentLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.Common.BackingAlgebra OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys6.AsanNodesMmLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys6.AsanNodesLibE OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst.RunCeil OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.RunLim OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsCells OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsArith3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3.AsAinv3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3.AsAinvGeom3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrameE3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvZone3b.AsAinvFacts3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3.AsAinvLedger OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvHoleP3.AsAinvLedger2 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3.AsAinvOps3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3.AsAinvOpsPf3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3.AsAinvHole3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvHoleP3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvRoom3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys6 OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys6.AsKSys7.
Import ListNotations.
Open Scope Z_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
#[local] Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Notation u := bv_unsigned.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma wsum_map : forall {A B} (f : A -> B) (w : B -> Z) l, wsum w (map f l) = wsum (fun x => w (f x)) l.
Proof. induction l as [|x t IH]; [reflexivity|]. (lazymatch goal with |- ?G => let G' := eval cbn [map wsum fold_right] in G in change_no_check G' end). fold (wsum w (map f t)). fold (wsum (fun x => w (f x)) t). lia. Qed.
Lemma wsum_nonneg : forall {A} (w : A -> Z) l, (forall x, 0 <= w x) -> 0 <= wsum w l.
Proof. induction l as [|x t IH]; intros H; [(lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia|]. (lazymatch goal with |- ?G => let G' := eval cbn [wsum fold_right] in G in change_no_check G' end). fold (wsum w t). pose proof (H x). pose proof (IH H). lia. Qed.
Lemma wsum_incl_le : forall {A} (w : A -> Z) l l', List.NoDup l -> incl l l' -> (forall y, 0 <= w y) -> wsum w l <= wsum w l'.
Proof.
  induction l as [|a t IH]; intros l' ND INC W0; [apply wsum_nonneg; exact W0|].
  inversion ND as [|? ? Hna NDt]; subst.
  destruct (in_split a l' (INC a (or_introl eq_refl))) as (l1 & l2 & ->).
  assert (INC' : incl t (l1 ++ l2)).
  { intros y Hy. pose proof (INC y (or_intror Hy)) as Hy'. apply in_app_iff in Hy'. apply in_app_iff.
    destruct Hy' as [Hy'|[Hy'|Hy']]; [left; exact Hy' | subst y; contradiction | right; exact Hy']. }
  pose proof (IH (l1 ++ l2) NDt INC' W0) as IHt. rewrite wsum_app in *. cbn [wsum fold_right] in *. fold (wsum w t). fold (wsum w l2). fold (wsum w l2) in IHt. lia.
Qed.
Lemma NoDup_map_of : forall {A B C} (f : A -> B) (g : A -> C) l,
  List.NoDup (map g l) -> (forall x y, In x l -> In y l -> f x = f y -> g x = g y) -> List.NoDup (map f l).
Proof.
  induction l as [|a t IH]; intros ND INJ; [constructor|]. cbn [map] in *. inversion ND as [|? ? Hna NDt]; subst. constructor.
  - intros Hin. apply in_map_iff in Hin as (y & Ey & Hy). apply Hna. apply in_map_iff. exists y. split; [| exact Hy].
    apply INJ; [right; exact Hy | left; reflexivity | exact Ey].
  - apply IH; [exact NDt|]. intros x y Hx Hy. apply INJ; right; assumption.
Qed.

Lemma q_bytes_app : forall q1 q2, q_bytes (q1 ++ q2) = q_bytes q1 + q_bytes q2.
Proof. induction q1 as [|b t IH]; intros q2; [reflexivity|]. (lazymatch goal with |- ?G => let G' := eval cbn [app q_bytes fold_right] in G in change_no_check G' end). fold (q_bytes (t ++ q2)). fold (q_bytes t). rewrite IH. lia. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma sum_classes_add : forall (f g : Z -> Z) (k : nat), sum_classes (fun c => f c + g c) k = sum_classes f k + sum_classes g k.
Proof. induction k as [|k IH]; [reflexivity|]. (lazymatch goal with |- ?G => let G' := eval cbn [sum_classes] in G in change_no_check G' end). rewrite IH. lia. Qed.
Lemma sum_classes_mono : forall (f g : Z -> Z) (k : nat), (forall c, 1 <= c <= Z.of_nat k -> f c <= g c) -> sum_classes f k <= sum_classes g k.
Proof.
  induction k as [|k IH]; intros H; [(lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia|]. (lazymatch goal with |- ?G => let G' := eval cbn [sum_classes] in G in change_no_check G' end).
  pose proof (H (Z.of_nat (Datatypes.S k)) ltac:(lia)). assert (sum_classes f k <= sum_classes g k) by (apply IH; intros c Hc; apply H; lia). lia.
Qed.
Lemma sum_classes_div8 : forall (f : Z -> Z) (k : nat), sum_classes (fun c => f c / 8) k <= sum_classes f k / 8.
Proof.
  induction k as [|k IH]; [(lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia|]. (lazymatch goal with |- ?G => let G' := eval cbn [sum_classes] in G in change_no_check G' end).
  set (a := f (Z.of_nat (Datatypes.S k))) in *. set (b := sum_classes f k) in *. set (b8 := sum_classes (fun c => f c / 8) k) in *.
  clearbody a b b8. Z.div_mod_to_equations. lia.
Qed.
Lemma sum_classes_const : forall (x : Z) (k : nat), sum_classes (fun _ => x) k = Z.of_nat k * x.
Proof. induction k as [|k IH]; [reflexivity|]. (lazymatch goal with |- ?G => let G' := eval cbn [sum_classes] in G in change_no_check G' end). rewrite IH. lia. Qed.
(* [comment removed for export] *)
Lemma sec_hull_le : forall mp n, 0 <= mp -> 0 <= sec_map_size n -> 0 <= sec_hull mp n <= sec_map_size n / 8 + 2 * PG.
Proof. intros mp n Hmp Hsz. (lazymatch goal with |- ?G => let G' := eval unfold sec_hull, sec_hull_lo, sec_hull_hi, pgup, pgdn, sh_lo, sh_hi, SB, PG in G in change_no_check G' end). Z.div_mod_to_equations. lia. Qed.

Section Budget.
  Context {RUN : run_ceil}.
  Variable bt : as_boot.
  Variables (st : ast) (Lc FF : list (Z * Z)) (qt qg : Z).
  Hypothesis W : WFq bt st Lc FF qt qg.
  Hypothesis HQ : qt + qg <= 2 ^ 28 + 2 ^ 21.

  (* [comment removed for export] *)
  Lemma prim_charge_le : a_kact st <= KCAP -> prim_charge st <= PRIMMAX.
  Proof.
    clear HQ. intros KC.
    pose proof W as ((WR1 & _) & _ & _ & _ & _ & _ & _ & (M1 & M2 & M3 & M4 & M5) & _).
    assert (EVD : a_kact st / EVT <= NEV) by ((lazymatch goal with |- ?G => let G' := eval unfold NEV in G in change_no_check G' end); apply Z.div_le_mono; [(lazymatch goal with |- ?G => let G' := eval unfold EVT in G in change_no_check G' end); lia | exact KC]).
    assert (MU : sum_mu st <= MUMAX).
    { (lazymatch goal with |- ?G => let G' := eval unfold MUMAX in G in change_no_check G' end). eapply Z.le_trans; [exact M4|]. apply Z.mul_le_mono_nonneg_l; [(lazymatch goal with |- ?G => let G' := eval unfold KUSERMAP in G in change_no_check G' end); lia | exact EVD]. }
    set (mu := fun c => r_mapped_user (a_reg st c)). set (fa := fun c => r_mapped_fa (a_reg st c)).
    assert (FAc : forall c, 1 <= c <= 30 -> fa c <= mu c / 8 + KFAMAP).
    { intros c Hc. pose proof (M5 c Hc) as F5. pose proof (csize_pos c Hc) as [S1 _].
      destruct (WR1 c Hc) as ((Y1 & _) & _).
      assert (D32 : r_mapped_user (a_reg st c) / csize c <= r_mapped_user (a_reg st c) / 32) by (apply Z.div_le_compat_l; lia).
      (lazymatch goal with |- ?G => let G' := eval unfold fa, mu in G in change_no_check G' end). clear -F5 D32 Y1. Z.div_mod_to_equations. lia. }
    (lazymatch goal with |- ?G => let G' := eval unfold prim_charge in G in change_no_check G' end).
    change (sum_classes (fun c : Z => r_mapped_user (a_reg st c) + r_mapped_user (a_reg st c) / 8 + r_mapped_fa (a_reg st c) + r_mapped_fa (a_reg st c) / 8) 30)
      with (sum_classes (fun c : Z => ((mu c + mu c / 8) + fa c) + fa c / 8) 30).
    rewrite !sum_classes_add. change (sum_classes (fun c : Z => mu c) 30) with (sum_mu st). change (sum_classes mu 30) with (sum_mu st).
    pose proof (sum_classes_div8 mu 30) as D1. change (sum_classes mu 30) with (sum_mu st) in D1.
    pose proof (sum_classes_div8 fa 30) as D2.
    assert (SF : sum_classes fa 30 <= MUMAX / 8 + 30 * KFAMAP).
    { eapply Z.le_trans; [apply (sum_classes_mono fa (fun c => mu c / 8 + KFAMAP)); exact FAc|].
      rewrite sum_classes_add, sum_classes_const. (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end).
      assert (MUMAX8 : sum_mu st / 8 <= MUMAX / 8) by (apply Z.div_le_mono; lia). clear -D1 MUMAX8. lia. }
    assert (SF8 : sum_classes fa 30 / 8 <= (MUMAX / 8 + 30 * KFAMAP) / 8) by (apply Z.div_le_mono; lia).
    assert (MU8 : sum_mu st / 8 <= MUMAX / 8) by (apply Z.div_le_mono; lia).
    change (sum_classes (fun c : Z => fa c) 30) with (sum_classes fa 30).
    (lazymatch goal with |- ?G => let G' := eval unfold PRIMMAX in G in change_no_check G' end). clear -MU MU8 D1 D2 SF SF8. lia.
  Qed.

  (* [comment removed for export] *)
  Definition sec_maps : Z := wsum sc_mapsz (a_sec st).
  Definition sec_hulls : Z := wsum (fun s => sec_hull (sc_map s) (sc_n s)) (a_sec st).
  Lemma sec_charge_split : sec_charge st = sec_maps + sec_hulls.
  Proof.
    clear W HQ. (lazymatch goal with |- ?G => let G' := eval unfold sec_charge, sec_maps, sec_hulls, wsum in G in change_no_check G' end). induction (a_sec st) as [|x t IH]; [reflexivity|]. (lazymatch goal with |- ?G => let G' := eval cbn [fold_right] in G in change_no_check G' end). rewrite IH. lia.
  Qed.

  (* [comment removed for export] *)
  Definition secw (pn : Z * Z) : Z := if is_primary (snd pn) then 0 else snd pn + 12296.


  Lemma not_primary_big : forall n, 64513 <= n -> is_primary n = false.
  Proof.
    intros n Hn. (lazymatch goal with |- ?G => let G' := eval unfold is_primary, needed in G in change_no_check G' end). apply Z.leb_gt. pose proof (rz_big n ltac:(lia)) as RZ. rewrite RZ.
    (lazymatch goal with |- ?G => let G' := eval unfold rounded in G in change_no_check G' end). pose proof (RoundUp_ge (Z.max n 8) 8 ltac:(lia)). lia.
  Qed.
  Lemma sec_map_size_le : forall n, 64513 <= n -> sec_map_size n <= n + 12296.
  Proof.
    intros n Hn. (lazymatch goal with |- ?G => let G' := eval unfold sec_map_size, sec_needed in G in change_no_check G' end). rewrite (rz_big n ltac:(lia)). (lazymatch goal with |- ?G => let G' := eval unfold rounded, PG in G in change_no_check G' end).
    pose proof (RoundUp_lt (Z.max n 8) 8 ltac:(lia)). pose proof (RoundUp_lt (RoundUp (Z.max n 8) 8 + 2 * 2048) 4096 ltac:(lia)). lia.
  Qed.
  Lemma sec_map_size_ge0 : forall n, 64513 <= n -> 0 <= sec_map_size n.
  Proof.
    intros n Hn. (lazymatch goal with |- ?G => let G' := eval unfold sec_map_size, sec_needed in G in change_no_check G' end). rewrite (rz_big n ltac:(lia)). (lazymatch goal with |- ?G => let G' := eval unfold rounded, PG in G in change_no_check G' end).
    pose proof (RoundUp_ge (Z.max n 8) 8 ltac:(lia)). pose proof (RoundUp_ge (RoundUp (Z.max n 8) 8 + 2 * 2048) 4096 ltac:(lia)). lia.
  Qed.
  Lemma PHI_wsum : forall L, PHI L = wsum (fun b : Z * Z => snd b + MBLK) L.
  Proof. induction L as [|b t IH]; [reflexivity|]. (lazymatch goal with |- ?G => let G' := eval cbn [PHI wsum fold_right] in G in change_no_check G' end). fold (wsum (fun b : Z * Z => snd b + MBLK) t). rewrite IH. lia. Qed.
  Lemma wsum_scale : forall {A} (k : Z) (w : A -> Z) l, k * wsum w l = wsum (fun x => k * w x) l.
  Proof. induction l as [|x t IH]; [(lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia|]. (lazymatch goal with |- ?G => let G' := eval cbn [wsum fold_right] in G in change_no_check G' end). fold (wsum w t). fold (wsum (fun x => k * w x) t). lia. Qed.
  Lemma wsum_add : forall {A} (w1 w2 : A -> Z) l, wsum (fun x => w1 x + w2 x) l = wsum w1 l + wsum w2 l.
  Proof. induction l as [|x t IH]; [(lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia|]. (lazymatch goal with |- ?G => let G' := eval cbn [wsum fold_right] in G in change_no_check G' end). fold (wsum w1 t). fold (wsum w2 t). fold (wsum (fun x => w1 x + w2 x) t). lia. Qed.
  Definition ZZ_eq_dec : forall x y : Z * Z, {x = y} + {x <> y}.
  Proof. decide equality; apply Z.eq_dec. Defined.

  (* [comment removed for export] *)
  Lemma sec_maps_inj : forall w : Z * Z -> Z, (forall pn, 0 <= w pn) ->
    wsum (fun s => w (sc_user s, sc_n s)) (a_sec st) <= wsum w Lc + wsum w (map (fun mn : Z * Z => (fst mn + 16, snd mn)) (quar st)).
  Proof.
    clear HQ. intros w W0.
    pose proof W as (_ & _ & (WB1 & WB2 & QT & QG & _ & _) & (_ & _ & _ & SR & SND & SLQ & _ & _) & (WL & _) & _).
    set (f := fun s : schunk => (sc_user s, sc_n s)).
    set (g := fun mn : Z * Z => (fst mn + 16, snd mn)).
    assert (ND : List.NoDup (map f (a_sec st))).
    { apply (NoDup_map_of f sc_map _ SND). intros x y Hx Hy E. unfold f, sc_user in E. injection E as E1 E2. rewrite E2 in E1. lia. }
    assert (INC : incl (map f (a_sec st)) (Lc ++ map g (quar st))).
    { intros y Hy. apply in_map_iff in Hy as (s & <- & Hs). apply in_app_iff.
      destruct (in_dec ZZ_eq_dec (f s) Lc) as [L|NL]; [left; exact L | right].
      destruct (in_dec ZZ_eq_dec (sc_user s - 16, sc_n s) (quar st)) as [Q|NQ].
      - apply in_map_iff. exists (sc_user s - 16, sc_n s). (lazymatch goal with |- ?G => let G' := eval unfold g, f in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval cbn [fst snd] in G in change_no_check G' end). split; [f_equal; lia | exact Q].
      - exfalso. apply NL. apply (proj2 (SLQ s Hs)). exact NQ. }
    change (wsum (fun s : schunk => w (sc_user s, sc_n s)) (a_sec st)) with (wsum (fun s => w (f s)) (a_sec st)).
    rewrite <- (wsum_map f w). rewrite <- wsum_app. apply wsum_incl_le; [exact ND | exact INC | intros y; apply W0].
  Qed.

  (* [comment removed for export] *)
  Lemma sec_maps_le5 : 5 * sec_maps <= 5 * PHI Lc + 6 * (qt + qg).
  Proof.
    clear HQ.
    pose proof W as (_ & _ & (WB1 & WB2 & QT & QG & _ & _) & (_ & _ & _ & SR & SND & SLQ & _ & _) & (WL & _) & _).
    set (secw0 := fun pn : Z * Z => Z.max 0 (secw pn)).
    assert (S1 : sec_maps <= wsum (fun s => secw0 (sc_user s, sc_n s)) (a_sec st)).
    { (lazymatch goal with |- ?G => let G' := eval unfold sec_maps in G in change_no_check G' end). apply wsum_le. intros s Hs. destruct (SR s Hs) as [Hn _]. (lazymatch goal with |- ?G => let G' := eval unfold secw0, secw in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval cbn [snd] in G in change_no_check G' end).
      rewrite (not_primary_big (sc_n s) ltac:(lia)). (lazymatch goal with |- ?G => let G' := eval unfold sc_mapsz in G in change_no_check G' end). pose proof (sec_map_size_le (sc_n s) ltac:(lia)). lia. }
    pose proof (sec_maps_inj secw0 ltac:(intros pn; (lazymatch goal with |- ?G => let G' := eval unfold secw0 in G in change_no_check G' end); lia)) as S2.
    assert (S3 : wsum secw0 Lc <= PHI Lc).
    { rewrite PHI_wsum. apply wsum_le. intros [p n] Hy. destruct (WL p n Hy) as (N1 & _). (lazymatch goal with |- ?G => let G' := eval unfold secw0, secw, MBLK in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval cbn [snd] in G in change_no_check G' end).
      destruct (is_primary n); lia. }
    assert (S4 : 5 * wsum secw0 (map (fun mn : Z * Z => (fst mn + 16, snd mn)) (quar st)) <= 6 * wsum (fun it : Z * Z => snd it) (quar st)).
    { rewrite wsum_map, !wsum_scale. apply wsum_le. intros [m n] Hq. (lazymatch goal with |- ?G => let G' := eval unfold secw0, secw in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval cbn [fst snd] in G in change_no_check G' end).
      destruct (quar_item bt st Lc FF W m n Hq) as (N1 & _).
      destruct (is_primary n) eqn:HP; [lia|].
      destruct (quar_sec bt st Lc FF W m n Hq HP) as (sc & Hsc & _ & En). destruct (SR sc Hsc) as [Hn _]. lia. }
    assert (S5 : wsum (fun it : Z * Z => snd it) (quar st) <= qt + qg).
    { (lazymatch goal with |- ?G => let G' := eval unfold quar in G in change_no_check G' end). pose proof (items_sum_q (a_tq st ++ a_gq st)) as IQ. rewrite q_bytes_app in IQ. unfold BATCHSZ in IQ. lia. }
    lia.
  Qed.

  (* [comment removed for export] *)
  Lemma sec_maps_le_cnt : sec_maps <= PHI Lc + (qt + qg) + 12296 * Z.of_nat (length (a_sec st)).
  Proof.
    clear HQ.
    pose proof W as (_ & _ & (WB1 & WB2 & QT & QG & _ & _) & (_ & _ & _ & SR & SND & SLQ & _ & _) & (WL & _) & _).
    set (w0 := fun pn : Z * Z => Z.max 0 (snd pn)).
    assert (S1 : sec_maps <= wsum (fun s => w0 (sc_user s, sc_n s)) (a_sec st) + 12296 * Z.of_nat (length (a_sec st))).
    { (lazymatch goal with |- ?G => let G' := eval unfold sec_maps in G in change_no_check G' end). rewrite <- (wsum_const 12296 (a_sec st)), <- wsum_add. apply wsum_le. intros s Hs. destruct (SR s Hs) as [Hn _].
      (lazymatch goal with |- ?G => let G' := eval unfold w0 in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval cbn [snd] in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval unfold sc_mapsz in G in change_no_check G' end). pose proof (sec_map_size_le (sc_n s) ltac:(lia)). lia. }
    pose proof (sec_maps_inj w0 ltac:(intros pn; (lazymatch goal with |- ?G => let G' := eval unfold w0 in G in change_no_check G' end); lia)) as S2.
    assert (S3 : wsum w0 Lc <= PHI Lc).
    { rewrite PHI_wsum. apply wsum_le. intros [p n] Hy. destruct (WL p n Hy) as (N1 & _). (lazymatch goal with |- ?G => let G' := eval unfold w0, MBLK in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval cbn [snd] in G in change_no_check G' end). lia. }
    assert (S4 : wsum w0 (map (fun mn : Z * Z => (fst mn + 16, snd mn)) (quar st)) <= wsum (fun it : Z * Z => snd it) (quar st)).
    { rewrite wsum_map. apply wsum_le. intros [m n] Hq. (lazymatch goal with |- ?G => let G' := eval unfold w0 in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval cbn [fst snd] in G in change_no_check G' end). destruct (quar_item bt st Lc FF W m n Hq) as (N1 & _). lia. }
    assert (S5 : wsum (fun it : Z * Z => snd it) (quar st) <= qt + qg).
    { (lazymatch goal with |- ?G => let G' := eval unfold quar in G in change_no_check G' end). pose proof (items_sum_q (a_tq st ++ a_gq st)) as IQ. rewrite q_bytes_app in IQ. unfold BATCHSZ in IQ. lia. }
    lia.
  Qed.
  Lemma sec_hulls_le : sec_hulls <= sec_maps / 8 + 2 * PG * Z.of_nat (length (a_sec st)).
  Proof.
    clear HQ.
    assert (SR : forall s, In s (a_sec st) -> 64513 <= sc_n s /\ 0 < sc_map s).
    { intros s Hs. destruct (sec_facts bt st Lc FF W s Hs) as (A1 & _ & _ & _ & _ & _ & A7 & _). split; [| exact A1]. clear -A7. lia. }
    (lazymatch goal with |- ?G => let G' := eval unfold sec_hulls, sec_maps in G in change_no_check G' end). revert SR. generalize (a_sec st) as l. intros l SR. induction l as [|s t IH]; [(lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia|].
    (lazymatch goal with |- ?G => let G' := eval cbn [wsum fold_right length] in G in change_no_check G' end). fold (wsum sc_mapsz t). fold (wsum (fun s0 : schunk => sec_hull (sc_map s0) (sc_n s0)) t).
    assert (IH' : wsum (fun s0 : schunk => sec_hull (sc_map s0) (sc_n s0)) t <= wsum sc_mapsz t / 8 + 2 * PG * Z.of_nat (length t)) by (apply IH; intros s1 Hs1; apply SR; right; exact Hs1).
    destruct (SR s (or_introl eq_refl)) as [Hn Hm].
    pose proof (sec_hull_le (sc_map s) (sc_n s) ltac:(clear -Hm; lia) (sec_map_size_ge0 (sc_n s) Hn)) as HL.
    unfold sc_mapsz at 1. rewrite Nat2Z.inj_succ.
    set (a := sec_map_size (sc_n s)) in *. set (b := wsum sc_mapsz t) in *. clearbody a b. clear -IH' HL. unfold PG in *. Z.div_mod_to_equations. lia.
  Qed.


  (* [comment removed for export] *)
  Lemma depot_charge_le : a_kact st <= KCAP -> depot_charge st <= DEPOTMAX.
  Proof.
    clear HQ. intros KC.
    pose proof W as (_ & _ & _ & _ & _ & _ & (D1 & D2 & D3 & D4 & D5 & D6 & D7 & D8 & D9 & D10 & _) & _ & _ & _ & _ & (N0 & F0)).
    assert (EVD : a_kact st / EVT <= NEV) by ((lazymatch goal with |- ?G => let G' := eval unfold NEV in G in change_no_check G' end); apply Z.div_le_mono; [(lazymatch goal with |- ?G => let G' := eval unfold EVT in G in change_no_check G' end); lia | exact KC]).
    assert (E0 : 0 <= a_kact st / EVT) by (apply Z.div_pos; [| (lazymatch goal with |- ?G => let G' := eval unfold EVT in G in change_no_check G' end); lia]; pose proof W as (_ & _ & _ & _ & _ & _ & _ & (M1 & _) & _); exact M1).
    (lazymatch goal with |- ?G => let G' := eval unfold depot_charge in G in change_no_check G' end). rewrite D6.
    assert (NEVv : NEV = 2048) by reflexivity. rewrite NEVv in EVD.
    assert (NB : dp_nids (a_dep st) / 2 ^ 16 < 17).
    { apply Z.div_lt_upper_bound; [lia|]. clear -D2 N0 EVD E0. lia. }
    assert (SB : Z.of_nat (length (dp_storeblocks (a_dep st))) <= 1).
    { set (L := Z.of_nat (length (dp_storeblocks (a_dep st)))) in *.
      assert (L0 : 0 <= L) by ((lazymatch goal with |- ?G => let G' := eval unfold L in G in change_no_check G' end); lia).
      destruct (Z_le_gt_dec L 1) as [LE|GT]; [exact LE|]. exfalso.
      assert (HL : L <= (dp_frames (a_dep st) - 1) / 2 ^ 20) by (clear -D10 GT L0; lia).
      assert (HF : dp_frames (a_dep st) <= 2 ^ 20 + FRW * 2048 + FRW * L) by (clear -D9 F0 EVD E0 L0; unfold FRW in *; nia).
      unfold FRW in HF. clear -HL HF GT. Z.div_mod_to_equations. lia. }
    (lazymatch goal with |- ?G => let G' := eval unfold DEPOTMAX, DEPOT0 in G in change_no_check G' end). rewrite NEVv. clear -NB SB. lia.
  Qed.

  (* [comment removed for export] *)
  Theorem budget_core : forall X k, 0 <= X -> 0 <= k ->
    PHI Lc + X + (qt + qg) <= GBUDGET + QCAP -> a_kact st + k * EVT <= KCAP ->
    KBASE + prim_charge st + (sec_charge st + X + X / 8 + 2 * PG * k) + depot_charge st + a_shsec st + 8 * a_nres st + ROOMSLACK <= LMIN.
  Proof.
    clear HQ. intros X k X0 K0 HX HKC.
    pose proof W as (_ & _ & _ & (_ & _ & NR & _) & (WL & _) & _ & _ & (M1 & M2 & M3 & _) & _).
    assert (KC : a_kact st <= KCAP) by (clear -HKC K0; unfold EVT in *; nia).
    assert (HK : a_kact st / EVT + k <= NEV).
    { (lazymatch goal with |- ?G => let G' := eval unfold NEV in G in change_no_check G' end). replace (a_kact st / EVT + k) with ((a_kact st + k * EVT) / EVT) by (apply Z.div_add; (lazymatch goal with |- ?G => let G' := eval unfold EVT in G in change_no_check G' end); lia).
      apply Z.div_le_mono; [(lazymatch goal with |- ?G => let G' := eval unfold EVT in G in change_no_check G' end); lia | exact HKC]. }
    pose proof (prim_charge_le KC) as PC. pose proof (depot_charge_le KC) as DC.
    pose proof sec_maps_le_cnt as SM. pose proof sec_hulls_le as SH. rewrite sec_charge_split.
    pose proof budget_closed as CL. unfold BUDGET_TOTAL in CL.
    assert (P0 : 0 <= PHI Lc) by (apply PHI_nonneg; intros b n Hin; destruct (WL b n Hin) as (N1 & _); lia).
    set (N := Z.of_nat (length (a_sec st))) in *. assert (N0 : 0 <= N) by ((lazymatch goal with |- ?G => let G' := eval unfold N in G in change_no_check G' end); lia).
    set (E := a_kact st / EVT) in *.
    assert (NN : N <= E) by (clear -M2 M3 N0; unfold PG in *; lia).
    set (m := sec_maps) in *. set (h := sec_hulls) in *.
    assert (SMX : m + X <= SECMAPS) by ((lazymatch goal with |- ?G => let G' := eval unfold SECMAPS in G in change_no_check G' end); clear -SM HX HK NN K0 N0 X0 P0; lia).
    assert (A2 : m / 8 + X / 8 <= SECMAPS / 8).
    { assert (D : (m + X) / 8 <= SECMAPS / 8) by (apply Z.div_le_mono; [lia | exact SMX]).
      generalize D. clear. generalize (SECMAPS / 8). intros z D. Z.div_mod_to_equations. lia. }
    assert (A3 : a_shsec st + 2 * PG * N + 2 * PG * k <= 2 * PG * NEV) by (clear -M3 HK M2 N0 K0; unfold PG in *; lia).
    unfold SECMAX, RESMAX in CL. clearbody m h N E. clear W WL M1 SM HX HKC HK NN.
    unfold PG in *. lia.
  Qed.

  Hypothesis KC : a_kact st <= KCAP.
  (* [comment removed for export] *)
  Theorem budget_room :
    KBASE + prim_charge st + sec_charge st + depot_charge st + a_shsec st + 8 * a_nres st + ROOMSLACK <= LMIN.
  Proof.
    pose proof W as (_ & _ & _ & _ & _ & _ & _ & _ & _ & (_ & _ & PH) & _).
    pose proof (budget_core 0 0 ltac:(lia) ltac:(lia) ltac:((lazymatch goal with |- ?G => let G' := eval unfold QCAP in G in change_no_check G' end); clear -HQ PH; lia) ltac:(clear -KC; lia)). clear -H. unfold PG in *. lia.
  Qed.
  (* [comment removed for export] *)
  Theorem budget_room_q : PHI Lc + qt + qg <= GBUDGET + 2 ^ 28 + 2 ^ 21 ->
    KBASE + prim_charge st + sec_charge st + depot_charge st + a_shsec st + 8 * a_nres st + ROOMSLACK <= LMIN.
  Proof.
    clear HQ. intros HQ'.
    pose proof (budget_core 0 0 ltac:(lia) ltac:(lia) ltac:((lazymatch goal with |- ?G => let G' := eval unfold QCAP in G in change_no_check G' end); clear -HQ'; lia) ltac:(clear -KC; lia)). clear -H. unfold PG in *. lia.
  Qed.

End Budget.
Definition qroom (Lc : list (Z * Z)) (qt qg : Z) : Prop := PHI Lc + qt + qg <= GBUDGET + 2 ^ 28 + 2 ^ 21.
Lemma qroom_WF : forall {RUN : run_ceil} bt st Lc FF, WF bt st Lc FF -> qroom Lc (2 ^ 20) (2 ^ 28).
Proof. intros RUN bt st Lc FF W. destruct W as (_ & _ & _ & _ & _ & _ & _ & _ & _ & (_ & _ & PH) & _). (lazymatch goal with |- ?G => let G' := eval unfold qroom in G in change_no_check G' end). lia. Qed.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma mod0_sub : forall a b m, 0 < m -> a mod m = 0 -> b mod m = 0 -> (b - a) mod m = 0.
Proof. intros a b m Hm Ha Hb. rewrite Zminus_mod, Ha, Hb. reflexivity. Qed.
Lemma mod0_add : forall a b m, 0 < m -> a mod m = 0 -> b mod m = 0 -> (a + b) mod m = 0.
Proof. intros a b m Hm Ha Hb. rewrite Zplus_mod, Ha, Hb. reflexivity. Qed.

Lemma pg_in_ivz_subtract : forall l lo hi a, ivs_wf l -> lo mod 4096 = 0 -> hi mod 4096 = 0 -> lo <= hi ->
  (pg_in_ivz (maps_subtract l lo hi) a <-> pg_in_ivz l a /\ ~ (lo <= a < hi)).
Proof.
  intros l lo hi a Hwf Hlo Hhi Hlh. (lazymatch goal with |- ?G => let G' := eval unfold pg_in_ivz in G in change_no_check G' end). split.
  - intros [Ra H]. split; [split; [exact Ra | exact (page_in_ranges_subtract_sub _ _ _ _ Hwf H)]|]. intros Hin.
    pose proof (page_of_byte_in_aligned (Z_to_bv 64 a) lo hi Hlo Hhi ltac:(rewrite u64_lit by lia; exact Hin)) as [P1 P2].
    rewrite (page_in_ranges_subtract_in (page_base (Z_to_bv 64 a)) l lo hi Hwf ltac:(lia)) in H. discriminate H.
  - intros [[Ra H] Nin]. split; [exact Ra|].
    rewrite page_in_ranges_subtract_out; [exact H | exact Hwf | exact Hlh |].
    apply (page_of_byte_out_aligned (Z_to_bv 64 a) lo hi Hlo Hhi). rewrite u64_lit by lia. lia.
Qed.

Section LazyOk.
  Variables (CE ILO IHI : Z).
  Definition lazy_ok (iv : word * word) : Prop :=
    u (fst iv) mod PG = 0 /\ u (snd iv) mod PG = 0 /\ 0 < u (fst iv) /\ u (fst iv) + u (snd iv) <= CE
    /\ (u (fst iv) + u (snd iv) <= ILO \/ IHI <= u (fst iv)).
  Lemma lazy_ok_subtract : forall l lo hi, ivs_wf l -> lo mod 4096 = 0 -> hi mod 4096 = 0 -> 0 <= lo -> lo <= hi -> hi <= 2 ^ 64 ->
    Forall lazy_ok l -> Forall lazy_ok (maps_subtract l lo hi).
  Proof.
    intros l lo hi Hwf Hlo Hhi H0 Hlh H64 HF. induction HF as [|[a sz] t Ha Ht IH]; [constructor|].
    apply ivs_wf_cons_inv in Hwf as [Wa Wt]. (lazymatch goal with |- ?G => let G' := eval cbn [maps_subtract] in G in change_no_check G' end). apply Forall_app. split; [| exact (IH Wt)].
    apply Forall_forall. intros q Hq. destruct Ha as (A1 & A2 & A3 & A4 & A5). cbn [fst snd] in *. unfold PG in *.
    pose proof (mod0_add _ _ 4096 ltac:(lia) A1 A2) as AE.
    destruct (iv_subtract_ends a sz lo hi q Wa H0 Hlh H64 Hq) as [(E1 & E2 & E3) | (E1 & E2 & E3)]; (lazymatch goal with |- ?G => let G' := eval unfold lazy_ok, PG in G in change_no_check G' end); rewrite E1.
    - assert (ES : u (snd q) = Z.min (u a + u sz) lo - u a) by lia. rewrite ES.
      split; [exact A1|]. split; [apply mod0_sub; [lia | exact A1 | destruct (Z.min_spec (u a + u sz) lo) as [[_ ->]|[_ ->]]; assumption]|].
      split; [exact A3|]. split; [lia|]. destruct A5 as [A5|A5]; [left; lia | right; lia].
    - assert (ES : u (snd q) = u a + u sz - Z.max (u a) hi) by lia. rewrite ES.
      assert (MX : Z.max (u a) hi mod 4096 = 0) by (destruct (Z.max_spec (u a) hi) as [[_ ->]|[_ ->]]; assumption).
      split; [exact MX|]. split; [apply mod0_sub; [lia | exact MX | exact AE]|].
      split; [lia|]. split; [lia|]. destruct A5 as [A5|A5]; [left; lia | right; lia].
  Qed.
End LazyOk.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section Vis.
  Context {RUN : run_ceil}.
  Variable bt : as_boot.
  #[local] Abbreviation IA := (bt_ia bt).
  Variables (st : ast) (Lc FF : list (Z * Z)) (qt qg : Z).
  Hypothesis W : WFq bt st Lc FF qt qg.                                       (* [comment removed for export] *)
  Ltac ulia := try ceil; unfold AS_HEAPLO, AS_LO, PTRLO, SB, PG, FAKE_SIZE, IASZ, KSPACE, BATCHSZ, BATCHCAP in *; lia.

  Lemma app_visible_cases : forall a, app_visible IA Lc FF a ->
    (0 <= a < 2 ^ 64) /\ (rep_wr bt st Lc FF a \/ in_band a).
  Proof.
    intros a Ha. pose proof W as (_ & _ & _ & _ & (WL & _) & _).
    pose proof (fixed_facts bt st Lc FF W) as (X1 & X2 & X3 & X4 & X5 & X6 & X7 & _).
    pose proof (img_lits bt st Lc FF W) as [I1 I2]. pose proof ceil_rng as CR.
    destruct Ha as [(b & n & Hin & Hr) | [(f & k & Hin & Hr) | [(b & n & Hin & Hr) | [(f & k & Hin & Hr) | [Hr | Hr]]]]].
    - destruct (WL b n Hin) as (N1 & _ & (B1 & B2 & _) & _). split; [ulia|]. left. do 5 right. left. exists b, n. split; [exact Hin | left; lia].
    - destruct (fake_frame_facts bt st Lc FF W f k Hin) as (F1 & F2 & _). split; [ulia|]. left. do 9 right. left. lia.
    - destruct (WL b n Hin) as (N1 & _ & (B1 & B2 & _) & _). split.
      + unfold sh_lo, sh_hi in Hr. assert (0 <= b / 8) by (apply Z.div_pos; ulia). assert ((b + n + 7) / 8 <= 2 ^ 47) by (apply Z.div_le_upper_bound; ulia). ulia.
      + left. do 5 right. left. exists b, n. split; [exact Hin | right; exact Hr].
    - destruct (fake_frame_facts bt st Lc FF W f k Hin) as (F1 & F2 & _ & F4 & _). split.
      + unfold sh_lo, sh_hi in Hr. assert (0 <= f / 8) by (apply Z.div_pos; ulia). assert ((f + FS k + 7) / 8 <= 2 ^ 47) by (apply Z.div_le_upper_bound; ulia). ulia.
      + left. do 10 right. left. exists f, k. split; [exact Hin | exact Hr].
    - unfold in_stack_shadow, sh_lo in Hr. assert (0 <= CEIL / 8) by (apply Z.div_pos; lia). split; [ulia|]. right. (lazymatch goal with |- ?G => let G' := eval unfold in_band in G in change_no_check G' end). ulia.
    - unfold in_image_shadow, sh_lo, sh_hi in Hr. assert (0 <= ia_img_lo IA / 8) by (apply Z.div_pos; lia).
      assert ((ia_img_lo IA + (ia_img_hi IA - ia_img_lo IA) + 7) / 8 <= 2 ^ 44) by (apply Z.div_le_upper_bound; ulia).
      split; [ulia|]. right. (lazymatch goal with |- ?G => let G' := eval unfold in_band in G in change_no_check G' end). ulia.
  Qed.

  Lemma uslot_not_visible : forall c a, 1 <= c <= 30 -> uslot bt st c a -> ~ app_visible IA Lc FF a.
  Proof.
    intros c a Hc Hs Hv. destruct (app_visible_cases a Hv) as [_ [Hw|Hb]].
    - exact (uslot_not_supp bt st Lc FF c _ _ W Hc a (or_intror Hw) Hs).
    - destruct (uslot_in_space bt st Lc FF c _ _ W Hc a Hs) as (_ & _ & _ & NB & _). exact (NB Hb).
  Qed.
  Lemma fslot_not_visible : forall c a, 1 <= c <= 30 -> r_mapped_fa (a_reg st c) + KFAMAP <= 2 ^ 29 -> fslot bt st c a -> ~ app_visible IA Lc FF a.
  Proof.
    intros c a Hc FR Hs Hv. destruct (app_visible_cases a Hv) as [_ [Hw|Hb]].
    - exact (fslot_not_supp bt st Lc FF c _ _ W Hc FR a (or_intror Hw) Hs).
    - destruct (fslot_in_space bt st Lc FF c _ _ W Hc FR a Hs) as (_ & _ & _ & NB & _). exact (NB Hb).
  Qed.
End Vis.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition res_low (bt : as_boot) : Prop := forall iv, In iv (bt_reserved bt) -> u (fst iv) + u (snd iv) <= AS_LO.

Section Slot.
  Context {RUN : run_ceil}.
  Variable bt : as_boot.
  #[local] Abbreviation SBEG := (bt_spacebeg bt).
  #[local] Abbreviation IA := (bt_ia bt).
  Variables (st : ast) (Lc FF : list (Z * Z)) (M0 : mem) (mdl : Model) (lo : Z) (qt qg : Z).
  Hypothesis W : WFq bt st Lc FF qt qg.                                       (* [comment removed for export] *)
  Hypothesis HQ : qroom Lc qt qg.
  Hypothesis R : Rep bt st Lc FF M0 mdl.
  Hypothesis MW : model_ivs_wf mdl.
  Hypothesis HH : m_halted mdl = None.
  Hypothesis KC : a_kact st <= KCAP.
  Hypothesis RL : res_low bt.
  Hypotheses (SL1 : (lo - SBEG) mod KUSERMAP = 0) (SL2 : SBEG <= lo) (SL3 : lo + KUSERMAP <= SBEG + KSPACE).
  Hypothesis NH : forall a, lo <= a < lo + KUSERMAP -> ~ holes bt st a.
  Hypothesis NV : forall a, lo <= a < lo + KUSERMAP -> ~ app_visible IA Lc FF a.
  #[local] Notation addr := (Z_to_bv 64 lo).
  #[local] Notation size := (Z_to_bv 64 KUSERMAP).
  #[local] Notation K := KUSERMAP.
  #[local] Notation A2 := (a_aa st ++ [(sh_lo lo, sh_lo lo + KUSERMAP / 8)]).
  #[local] Notation E6 := (bt_resv6 bt + bt_resv6_len bt).

  Lemma slot_lits : 0 < lo /\ bt_resv6 bt <= lo /\ lo + K <= E6 /\ E6 <= CEIL /\ lo + K < 2 ^ 64 /\ u addr = lo /\ u size = K
                    /\ AS_HEAPLO <= lo /\ ia_img_hi IA <= lo.
  Proof.
    destruct (space_facts bt st Lc FF W) as ((D1 & D2 & D3 & D4 & D5) & MR & S1 & S2 & S3).
    pose proof (img_lits bt st Lc FF W) as [I1 I2].
    pose proof ceil_rng as CR. unfold KUSERMAP, KSPACE, PG, AS_HEAPLO, AS_LO in *.
    assert (X : 0 < lo /\ lo + 2 ^ 18 < 2 ^ 64) by lia.
    repeat split; try lia; rewrite u64_lit; lia.
  Qed.

  Lemma slot_aligned : lo mod 2 ^ 15 = 0.
  Proof.
    pose proof (fixed_facts bt st Lc FF W) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & SB16).
    unfold KUSERMAP in SL1.
    pose proof (Z.div_mod (lo - SBEG) (2 ^ 18) ltac:(lia)) as D1. rewrite SL1 in D1.
    pose proof (Z.div_mod SBEG (2 ^ 16) ltac:(lia)) as D2. rewrite SB16 in D2.
    replace lo with ((8 * ((lo - SBEG) / 2 ^ 18) + 2 * (SBEG / 2 ^ 16)) * 2 ^ 15) by lia. apply Z_mod_mult.
  Qed.
  Lemma slot_pg : lo mod page_size = 0 /\ (lo + K) mod page_size = 0.
  Proof.
    pose proof slot_aligned as A. pose proof (Z.div_mod lo (2 ^ 15) ltac:(lia)) as D. rewrite A in D. (lazymatch goal with |- ?G => let G' := eval unfold page_size, KUSERMAP in G in change_no_check G' end).
    split.
    - replace lo with ((8 * (lo / 2 ^ 15)) * 4096) by lia. apply Z_mod_mult.
    - replace (lo + 2 ^ 18) with ((8 * (lo / 2 ^ 15) + 64) * 4096) by lia. apply Z_mod_mult.
  Qed.
  Lemma A2_wf : A_wf A2.
  Proof.
    destruct R as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (AW & _) & _).
    unfold A_wf in *. apply Forall_app. split; [exact AW|]. constructor; [|constructor]. (lazymatch goal with |- ?G => let G' := eval cbn [fst snd] in G in change_no_check G' end).
    pose proof slot_aligned as A. pose proof (Z.div_mod lo (2 ^ 15) ltac:(lia)) as D. rewrite A in D.
    (lazymatch goal with |- ?G => let G' := eval unfold sh_lo, SB, KUSERMAP, page_size in G in change_no_check G' end).
    assert (E : lo / 8 = 4096 * (lo / 2 ^ 15)). { rewrite D at 1. replace (2 ^ 15 * (lo / 2 ^ 15) + 0) with ((4096 * (lo / 2 ^ 15)) * 8) by lia. apply Z_div_mult. lia. }
    rewrite E. change (2 ^ 18 / 8) with 32768.
    split; [lia|]. split.
    - replace (2147450880 + 4096 * (lo / 2 ^ 15)) with ((524280 + lo / 2 ^ 15) * 4096) by lia. apply Z_mod_mult.
    - replace (2147450880 + 4096 * (lo / 2 ^ 15) + 32768) with ((524288 + lo / 2 ^ 15) * 4096) by lia. apply Z_mod_mult.
  Qed.

  (* [comment removed for export] *)
  Lemma ledger_R : rep_ledger bt st mdl.
  Proof. destruct R as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & R13 & _). exact R13. Qed.

  (* [comment removed for export] *)
  Lemma slot_overlap : overlap_sum (vm_maps (m_vmmaps mdl)) lo (lo + K) <= K.
  Proof.
    destruct slot_lits as (L0 & L1 & L2 & L3 & L4 & L5 & L6 & L7 & L8).
    destruct ledger_R as ((F6 & PM & FOK & FSEP & FCOV) & _).
    pose proof W as (_ & _ & _ & _ & _ & _ & _ & _ & WM & _).
    destruct WM as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & M0R6 & M0POS & _).
    rewrite (overlap_sum_perm _ _ lo (lo + K) PM), !overlap_sum_app.
    (* [comment removed for export] *)
    destruct (slot_in_one_fragment bt st F6 lo FOK FCOV SL1 L1 L2 SL3 NH) as (iv & Hiv & I1 & I2).
    destruct (in_split iv F6 Hiv) as (l1 & l2 & EF).
    assert (OF6 : overlap_sum F6 lo (lo + K) <= K).
    { rewrite EF, overlap_sum_app, overlap_sum_cons.
      pose proof (iv_count_in_rng_le iv lo (lo + K) ltac:((lazymatch goal with |- ?G => let G' := eval unfold KUSERMAP in G in change_no_check G' end); lia)).
      assert (Z1 : forall y, In y (l1 ++ l2) -> u (fst y) + u (snd y) <= lo \/ lo + K <= u (fst y)).
      { intros y Hy. destruct (FSEP l1 iv l2 y EF Hy) as [D|D]; [right; lia | left; lia]. }
      rewrite (overlap_sum_off l1), (overlap_sum_off l2); [lia | |]; apply Forall_forall; intros y Hy; apply Z1; apply in_app_iff; [right | left]; exact Hy. }
    (* [comment removed for export] *)
    assert (OM0 : overlap_sum (bt_maps0 bt) lo (lo + K) = 0).
    { apply overlap_sum_off. apply Forall_forall. intros [b n] Hbn. (lazymatch goal with |- ?G => let G' := eval cbn [fst snd] in G in change_no_check G' end).
      rewrite Forall_forall in M0POS. pose proof (M0POS (b, n) Hbn) as Pn. cbn [snd] in Pn.
      destruct (Z_le_gt_dec (u b + u n) lo) as [LE|GT]; [left; exact LE|]. destruct (Z_le_gt_dec (lo + K) (u b)) as [LE2|GT2]; [right; exact LE2|]. exfalso.
      apply (M0R6 b n (Z.max (u b) lo) Hbn); unfold KUSERMAP in *; lia. }
    (* [comment removed for export] *)
    assert (ODY : overlap_sum (dyn_maps st) lo (lo + K) = 0).
    { apply overlap_sum_off. apply Forall_forall. intros [b n] Hbn. (lazymatch goal with |- ?G => let G' := eval cbn [fst snd] in G in change_no_check G' end).
      assert (DR : exists dl dh, In (dl, dh) (dyn_ranges st) /\ b = Z_to_bv 64 dl /\ n = Z_to_bv 64 (dh - dl)).
      { unfold dyn_maps in Hbn. (lazymatch goal with |- ?G => let G' := eval unfold dyn_ranges in G in change_no_check G' end). apply in_app_iff in Hbn as [Hbn|Hbn]; [|apply in_app_iff in Hbn as [Hbn|Hbn]];
          apply in_map_iff in Hbn as (x & E & Hx); injection E as <- <-.
        - exists (sc_map x), (sc_map x + sc_mapsz x). split; [apply in_app_iff; left; apply in_map_iff; exists x; split; [reflexivity | exact Hx] | split; [reflexivity | f_equal; lia]].
        - exists x, (x + 2 ^ 20). split; [apply in_app_iff; right; apply in_app_iff; left; apply in_map_iff; exists x; split; [reflexivity | exact Hx] | split; [reflexivity | f_equal; lia]].
        - exists x, (x + 2 ^ 23). split; [apply in_app_iff; right; apply in_app_iff; right; apply in_map_iff; exists x; split; [reflexivity | exact Hx] | split; [reflexivity | f_equal; lia]]. }
      destruct DR as (dl & dh & Hd & -> & ->).
      pose proof W as (_ & _ & _ & _ & _ & _ & _ & _ & (RNG & _) & _).
      destruct (RNG dl dh (all_ranges_dyn bt st _ Hd)) as ((D1 & D2 & D3 & _) & D6 & _).
      pose proof ceil_rng as CR. rewrite !u64_lit by lia.
      destruct (space_vs_dyn bt st Lc FF W dl dh Hd) as [S|S]; unfold KSPACE, PG, KUSERMAP in *; lia. }
    lia.
  Qed.

  Lemma budget_slack : eager_used mdl + A_bytes (a_aa st) + ROOMSLACK <= vm_limit (m_vmmaps mdl).
  Proof.
    destruct ledger_R as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & LIM & _).
    destruct R as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (_ & _ & _ & _ & _ & _ & _ & BUD) & _).
    pose proof (budget_room_q bt st Lc FF qt qg W KC HQ). lia.   (* [comment removed for export] *)
  Qed.

  Section Mat.
    Variable mdlm : Model.
    Hypothesis SBM : same_but_materialized mdl mdlm.
    Hypothesis MI : MInv (a_aa st) mdlm.

    Lemma mat_eqs : m_vmmaps mdlm = m_vmmaps mdl /\ m_vm_lazy mdlm = m_vm_lazy mdl /\ eager_used mdlm = eager_used mdl /\ m_halted mdlm = None /\ model_ivs_wf mdlm.
    Proof.
      destruct (sbm_vmmaps mdl mdlm SBM) as [E1 E2]. split; [exact E1|]. split; [exact E2|]. split; [apply eager_used_ext; assumption|].
      split; [| exact (model_ivs_wf_sbm7 mdl mdlm SBM MW)].
      pose proof (same_but_materialized_frame mdl mdlm SBM) as F. destruct F as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HL & _). rewrite HL. exact HH.
    Qed.

    Lemma node_top : u addr + u size <= alloc_top (m_vmmaps mdlm) /\ alloc_top (m_vmmaps mdlm) < two_pow_64.
    Proof.
      destruct slot_lits as (L0 & L1 & L2 & L3 & L4 & L5 & L6 & L7 & L8). destruct mat_eqs as (E1 & _). rewrite E1.
      destruct ledger_R as (_ & _ & _ & _ & _ & _ & _ & _ & _ & TOP & _).
      pose proof (page_floor_le (alloc_top (m_vmmaps mdl))). split; [rewrite L5, L6; lia | apply alloc_top_lt].
    Qed.

    Lemma node_region_free : region_free (vm_reserved (m_vmmaps mdlm)) addr size = true.
    Proof.
      destruct slot_lits as (L0 & L1 & L2 & L3 & L4 & L5 & L6 & L7 & L8). destruct mat_eqs as (E1 & _). rewrite E1.
      destruct ledger_R as (_ & _ & _ & _ & RES & _). rewrite RES.
      apply RefNodes.region_free_intro. intros b s Hbs. right. pose proof (RL (b, s) Hbs) as H. cbn [fst snd] in H. rewrite L5.
      unfold AS_HEAPLO, AS_LO in *. lia.
    Qed.

    Lemma node_map_contains : map_contains (vm_maps (m_vmmaps mdlm)) addr size = true.
    Proof.
      destruct slot_lits as (L0 & L1 & L2 & L3 & L4 & L5 & L6 & L7 & L8). destruct mat_eqs as (E1 & _). rewrite E1.
      destruct ledger_R as ((F6 & PM & FOK & FSEP & FCOV) & _).
      exact (map_contains_of_frag bt st F6 _ _ lo PM FOK FCOV SL1 L1 L2 SL3 NH ltac:(lia) L4).
    Qed.

    Lemma node_budget : mmap_fixed_rw_budget_ok (Z_to_bv 64 50) mdlm addr size = true.
    Proof.
      destruct slot_lits as (L0 & L1 & L2 & L3 & L4 & L5 & L6 & L7 & L8). destruct mat_eqs as (E1 & E2 & E3 & E4 & E5).
      destruct R as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (AW & _) & _).
      apply (budget_ok_commit (a_aa st)); [exact MI | exact AW | exact E5 |].
      rewrite E1, E3, L5, L6. pose proof slot_overlap. pose proof budget_slack. unfold ROOMSLACK, KUSERMAP in *. lia.
    Qed.

    Lemma node_OK : m_halted (OKm addr size mdlm) = None /\ MInv (a_aa st) (OKm addr size mdlm)
      /\ (forall p, page_in_ranges p (m_vm_lazy (OKm addr size mdlm)) = true -> page_in_ranges p (m_vm_lazy mdl) = true).
    Proof.
      destruct slot_lits as (L0 & L1 & L2 & L3 & L4 & L5 & L6 & L7 & L8). destruct mat_eqs as (E1 & E2 & E3 & E4 & E5). destruct slot_pg as [P1 P2].
      split; [rewrite OKm_halted; exact E4|]. split.
      - apply MInv_OKm; [exact MI | exact E5 | rewrite L5; exact P1 |].
        rewrite E1, E3, L5, L6. pose proof slot_overlap. pose proof budget_slack. unfold ROOMSLACK, KUSERMAP in *. lia.
      - intros p Hp. rewrite OKm_lazy, E2 in Hp. destruct MW as (_ & _ & Wl & _). exact (page_in_ranges_subtract_sub p _ _ _ Wl Hp).
    Qed.

    Lemma node_DS : m_halted (DSm addr size mdlm) = None /\ MInv (a_aa st) (DSm addr size mdlm)
      /\ (forall p, page_in_ranges p (m_vm_lazy (DSm addr size mdlm)) = true -> page_in_ranges p (m_vm_lazy mdl) = true).
    Proof.
      destruct slot_lits as (L0 & L1 & L2 & L3 & L4 & L5 & L6 & L7 & L8). destruct mat_eqs as (E1 & E2 & E3 & E4 & E5). destruct slot_pg as [P1 P2].
      split; [rewrite DSm_halted; exact E4|]. split.
      - apply MInv_DSm; [exact MI | exact E5 | rewrite L5; exact P1].
      - intros p Hp. rewrite DSm_lazy, E2 in Hp. destruct MW as (_ & _ & Wl & _). exact (page_in_ranges_subtract_sub p _ _ _ Wl Hp).
    Qed.
  End Mat.

  (* [comment removed for export] *)
  Lemma slot_cut_lz : forall l a, ivs_wf l ->
    (app_visible IA Lc FF a \/ CEIL <= a < 2 ^ 64 \/ (ia_img_lo IA <= a < ia_img_hi IA)) ->
    page_in_ranges (page_base (Z_to_bv 64 a)) (maps_subtract l lo (lo + K)) = page_in_ranges (page_base (Z_to_bv 64 a)) l.
  Proof.
    intros l a Wl Ha. destruct slot_lits as (L0 & L1 & L2 & L3 & L4 & L5 & L6 & L7 & L8). destruct slot_pg as [P1 P2]. unfold page_size in *.
    pose proof (img_lits bt st Lc FF W) as [I1 I2]. pose proof ceil_rng as CR.
    assert (RA : 0 <= a < 2 ^ 64).
    { destruct Ha as [Ha | [Ha | Ha]]; [exact (proj1 (app_visible_cases bt st Lc FF qt qg W a Ha)) | lia | unfold AS_LO in *; lia]. }
    assert (NS : ~ (lo <= a < lo + K)).
    { intros Hs. destruct Ha as [Ha | [Ha | Ha]]; [exact (NV a Hs Ha) | lia | lia]. }
    apply page_in_ranges_subtract_out; [exact Wl | (lazymatch goal with |- ?G => let G' := eval unfold KUSERMAP in G in change_no_check G' end); lia |].
    apply (page_of_byte_out_aligned (Z_to_bv 64 a) lo (lo + K) P1 P2). rewrite u64_lit by lia. lia.
  Qed.

  (* [comment removed for export] *)
  Section PostOK.
    Variables mdlm mdl' : Model.
    Hypothesis SBM : same_but_materialized mdl mdlm.
    Hypothesis SBM' : same_but_materialized (OKm addr size mdlm) mdl'.

    Lemma postOK_eqs : m_vmmaps mdl' = mmap_fixed_rw_next (m_vmmaps mdl) addr size
      /\ m_vm_lazy mdl' = maps_subtract (m_vm_lazy mdl) lo (lo + K).
    Proof.
      destruct slot_lits as (L0 & L1 & L2 & L3 & L4 & L5 & L6 & L7 & L8).
      destruct (sbm_vmmaps mdl mdlm SBM) as [E1 E2]. destruct (sbm_vmmaps _ mdl' SBM') as [E3 E4].
      rewrite E3, E4, OKm_vmmaps, OKm_lazy, E1, E2, L5, L6. split; reflexivity.
    Qed.

    Lemma postOK_eager : eager_used mdl' <= eager_used mdl + K.
    Proof.
      destruct slot_lits as (L0 & L1 & L2 & L3 & L4 & L5 & L6 & L7 & L8).
      destruct (sbm_vmmaps mdl mdlm SBM) as [E1 E2]. destruct (sbm_vmmaps _ mdl' SBM') as [E3 E4].
      rewrite (eager_used_ext mdl' (OKm addr size mdl)); [| rewrite E3, !OKm_vmmaps, E1; reflexivity | rewrite E4, !OKm_lazy, E2; reflexivity].
      pose proof (eager_OKm_le addr size mdl MW) as H. rewrite L5, L6 in H. pose proof slot_overlap. lia.
    Qed.

    Lemma postOK_widen : MInv (a_aa st) mdl' -> MInv A2 mdl'.
    Proof.
      intros MI. apply MInv_widen; [exact MI|]. destruct postOK_eqs as [E1 _]. rewrite E1. (lazymatch goal with |- ?G => let G' := eval unfold mmap_fixed_rw_next in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval cbn [vm_limit] in G in change_no_check G' end).
      pose proof postOK_eager. pose proof budget_slack. unfold ROOMSLACK, KUSERMAP in *. change (2 ^ 18 / 8) with 32768. lia.
    Qed.

    Lemma postOK_ledger :
      vm_maps (m_vmmaps mdl') = vm_maps (m_vmmaps mdl)
      /\ (forall a, in_ivz (vm_noaccess (m_vmmaps mdl')) a <-> in_ivz (vm_noaccess (m_vmmaps mdl)) a /\ ~ (lo <= a < lo + K))
      /\ Forall (fun e : word * word => 0 < bv_unsigned (snd e)) (vm_noaccess (m_vmmaps mdl'))
      /\ (forall a, pg_in_ivz (m_vm_lazy mdl') a <-> pg_in_ivz (m_vm_lazy mdl) a /\ ~ (lo <= a < lo + K))
      /\ Forall (fun iv : word * word => bv_unsigned (fst iv) mod PG = 0 /\ bv_unsigned (snd iv) mod PG = 0 /\ 0 < bv_unsigned (fst iv)
                                     /\ bv_unsigned (fst iv) + bv_unsigned (snd iv) <= CEIL
                                     /\ (bv_unsigned (fst iv) + bv_unsigned (snd iv) <= ia_img_lo IA \/ ia_img_hi IA <= bv_unsigned (fst iv)))
                (m_vm_lazy mdl')
      /\ vm_reserved (m_vmmaps mdl') = vm_reserved (m_vmmaps mdl) /\ vm_brk (m_vmmaps mdl') = vm_brk (m_vmmaps mdl)
      /\ vm_start_brk (m_vmmaps mdl') = vm_start_brk (m_vmmaps mdl) /\ vm_mmap_base (m_vmmaps mdl') = vm_mmap_base (m_vmmaps mdl)
      /\ vm_init_sp (m_vmmaps mdl') = vm_init_sp (m_vmmaps mdl) /\ vm_limit (m_vmmaps mdl') = vm_limit (m_vmmaps mdl).
    Proof.
      destruct slot_lits as (L0 & L1 & L2 & L3 & L4 & L5 & L6 & L7 & L8). destruct slot_pg as [P1 P2]. unfold page_size in *.
      destruct postOK_eqs as [E1 E2]. rewrite E1, E2. (lazymatch goal with |- ?G => let G' := eval unfold mmap_fixed_rw_next in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval cbn [vm_maps vm_noaccess vm_reserved vm_brk vm_start_brk vm_mmap_base vm_init_sp vm_limit] in G in change_no_check G' end).
      rewrite L5, L6. destruct MW as (Wm & Wn & Wl & _).
      destruct ledger_R as (_ & _ & _ & LOK & _ & _ & _ & _ & _ & _ & _ & NPOS).
      split; [reflexivity|]. split; [intros a; apply in_ivz_maps_subtract; unfold KUSERMAP in *; lia|].
      split; [apply ivs_pos_subtract; exact NPOS|].
      split; [intros a; apply pg_in_ivz_subtract; [exact Wl | exact P1 | exact P2 | (lazymatch goal with |- ?G => let G' := eval unfold KUSERMAP in G in change_no_check G' end); lia]|].
      split; [apply (lazy_ok_subtract CEIL (ia_img_lo IA) (ia_img_hi IA)); [exact Wl | exact P1 | exact P2 | lia | (lazymatch goal with |- ?G => let G' := eval unfold KUSERMAP in G in change_no_check G' end); lia | lia | exact LOK]|].
      repeat split; reflexivity.
    Qed.

    Lemma postOK_rest : same_except_vm mdl mdl' /\ lazy_kept IA Lc FF mdl mdl' /\ model_ivs_wf mdl' /\ m_halted mdl' = None.
    Proof.
      destruct slot_lits as (L0 & L1 & L2 & L3 & L4 & L5 & L6 & L7 & L8). destruct postOK_eqs as [E1 E2].
      split.
      { (lazymatch goal with |- ?G => let G' := eval unfold same_except_vm in G in change_no_check G' end). rewrite (sbm_frame_vm _ _ SBM'). rewrite (OKm_frame addr size mdlm). rewrite (sbm_frame_vm _ _ SBM). reflexivity. }
      split.
      { intros a Ha. (lazymatch goal with |- ?G => let G' := eval unfold lzb in G in change_no_check G' end). rewrite E2. destruct MW as (_ & _ & Wl & _). exact (slot_cut_lz _ a Wl Ha). }
      split.
      { apply (model_ivs_wf_sbm7 _ _ SBM'). apply model_ivs_wf_OKm. exact (model_ivs_wf_sbm7 _ _ SBM MW). }
      pose proof (same_but_materialized_frame _ _ SBM') as F. destruct F as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HL & _).
      rewrite HL, OKm_halted.
      pose proof (same_but_materialized_frame _ _ SBM) as F. destruct F as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HL2 & _). rewrite HL2. exact HH.
    Qed.
  End PostOK.

  (* [comment removed for export] *)
  Section PostDS.
    Variables mdlm mdl' : Model.
    Hypothesis SBM : same_but_materialized mdl mdlm.
    Hypothesis SBM' : same_but_materialized (DSm addr size mdlm) mdl'.

    Lemma postDS_eqs : m_vmmaps mdl' = mmap_fixed_destroyed_next (m_vmmaps mdl) addr size
      /\ m_vm_lazy mdl' = maps_subtract (m_vm_lazy mdl) lo (lo + K).
    Proof.
      destruct slot_lits as (L0 & L1 & L2 & L3 & L4 & L5 & L6 & L7 & L8).
      destruct (sbm_vmmaps mdl mdlm SBM) as [E1 E2]. destruct (sbm_vmmaps _ mdl' SBM') as [E3 E4].
      rewrite E3, E4, DSm_vmmaps, DSm_lazy, E1, E2, L5, L6. split; reflexivity.
    Qed.

    Lemma postDS_eager : eager_used mdl' <= eager_used mdl.
    Proof.
      destruct (sbm_vmmaps mdl mdlm SBM) as [E1 E2]. destruct (sbm_vmmaps _ mdl' SBM') as [E3 E4].
      rewrite (eager_used_ext mdl' (DSm addr size mdl)); [| rewrite E3, !DSm_vmmaps, E1; reflexivity | rewrite E4, !DSm_lazy, E2; reflexivity].
      exact (eager_DSm_le addr size mdl MW).
    Qed.

    Lemma postDS_ledger : ledger_destroyed bt mdl mdl' lo K.
    Proof.
      destruct slot_lits as (L0 & L1 & L2 & L3 & L4 & L5 & L6 & L7 & L8). destruct slot_pg as [P1 P2]. unfold page_size in *.
      destruct postDS_eqs as [E1 E2]. (lazymatch goal with |- ?G => let G' := eval unfold ledger_destroyed in G in change_no_check G' end). cbn zeta. rewrite E1, E2. (lazymatch goal with |- ?G => let G' := eval unfold mmap_fixed_destroyed_next in G in change_no_check G' end).
      (lazymatch goal with |- ?G => let G' := eval cbn [vm_maps vm_noaccess vm_reserved vm_brk vm_start_brk vm_mmap_base vm_init_sp vm_limit] in G in change_no_check G' end).
      rewrite L5, L6. destruct MW as (Wm & Wn & Wl & _).
      destruct ledger_R as (_ & _ & _ & LOK & _).
      split; [reflexivity|]. split; [reflexivity|].
      split; [intros a; apply pg_in_ivz_subtract; [exact Wl | exact P1 | exact P2 | (lazymatch goal with |- ?G => let G' := eval unfold KUSERMAP in G in change_no_check G' end); lia]|].
      split; [apply (lazy_ok_subtract CEIL (ia_img_lo IA) (ia_img_hi IA)); [exact Wl | exact P1 | exact P2 | lia | (lazymatch goal with |- ?G => let G' := eval unfold KUSERMAP in G in change_no_check G' end); lia | lia | exact LOK]|].
      repeat split; reflexivity.
    Qed.

    Lemma postDS_rest : same_except_vm mdl mdl' /\ lazy_kept IA Lc FF mdl mdl' /\ model_ivs_wf mdl' /\ m_halted mdl' = None.
    Proof.
      destruct slot_lits as (L0 & L1 & L2 & L3 & L4 & L5 & L6 & L7 & L8). destruct postDS_eqs as [E1 E2].
      split.
      { (lazymatch goal with |- ?G => let G' := eval unfold same_except_vm in G in change_no_check G' end). rewrite (sbm_frame_vm _ _ SBM'). rewrite (DSm_frame addr size mdlm). rewrite (sbm_frame_vm _ _ SBM). reflexivity. }
      split.
      { intros a Ha. (lazymatch goal with |- ?G => let G' := eval unfold lzb in G in change_no_check G' end). rewrite E2. destruct MW as (_ & _ & Wl & _). exact (slot_cut_lz _ a Wl Ha). }
      split.
      { apply (model_ivs_wf_sbm7 _ _ SBM'). apply model_ivs_wf_DSm. exact (model_ivs_wf_sbm7 _ _ SBM MW). }
      pose proof (same_but_materialized_frame _ _ SBM') as F. destruct F as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HL & _).
      rewrite HL, DSm_halted.
      pose proof (same_but_materialized_frame _ _ SBM) as F. destruct F as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HL2 & _). rewrite HL2. exact HH.
    Qed.
  End PostDS.
End Slot.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section N3.
  Context {RC : run_ceil}.
  Variable bt : as_boot.
  #[local] Abbreviation SBEG := (bt_spacebeg bt).
  #[local] Abbreviation IA := (bt_ia bt).
  #[local] Abbreviation U := bv_unsigned.

  Definition famap_ledger (st : ast) (c : Z) (mdl mdl' : Model) : Prop :=
    let lo := fa_beg SBEG c + r_mapped_fa (a_reg st c) in
    (r_fhole (a_reg st c) = false -> vm_maps (m_vmmaps mdl') = vm_maps (m_vmmaps mdl))
    /\ (r_fhole (a_reg st c) = true -> Permutation (vm_maps (m_vmmaps mdl')) ((Z_to_bv 64 lo, Z_to_bv 64 KFAMAP) :: vm_maps (m_vmmaps mdl)))
    /\ (forall a, in_ivz (vm_noaccess (m_vmmaps mdl')) a <-> in_ivz (vm_noaccess (m_vmmaps mdl)) a /\ ~ (lo <= a < lo + KFAMAP))
    /\ Forall (fun e : word * word => 0 < bv_unsigned (snd e)) (vm_noaccess (m_vmmaps mdl'))
    /\ (forall a, pg_in_ivz (m_vm_lazy mdl') a <-> pg_in_ivz (m_vm_lazy mdl) a /\ ~ (lo <= a < lo + KFAMAP))
    /\ Forall (fun iv : word * word => bv_unsigned (fst iv) mod PG = 0 /\ bv_unsigned (snd iv) mod PG = 0 /\ 0 < bv_unsigned (fst iv)
                                   /\ bv_unsigned (fst iv) + bv_unsigned (snd iv) <= CEIL
                                   /\ (bv_unsigned (fst iv) + bv_unsigned (snd iv) <= ia_img_lo IA \/ ia_img_hi IA <= bv_unsigned (fst iv)))
              (m_vm_lazy mdl')
    /\ vm_reserved (m_vmmaps mdl') = vm_reserved (m_vmmaps mdl) /\ vm_brk (m_vmmaps mdl') = vm_brk (m_vmmaps mdl)
    /\ vm_start_brk (m_vmmaps mdl') = vm_start_brk (m_vmmaps mdl) /\ vm_mmap_base (m_vmmaps mdl') = vm_mmap_base (m_vmmaps mdl)
    /\ vm_init_sp (m_vmmaps mdl') = vm_init_sp (m_vmmaps mdl) /\ vm_limit (m_vmmaps mdl') = vm_limit (m_vmmaps mdl)
    /\ eager_used mdl' <= eager_used mdl + KFAMAP.

  Definition N3F_stmt : Prop := forall st Lc FF M0 mdl c,
    WF bt st Lc FF -> Rep bt st Lc FF M0 mdl -> 1 <= c <= 30 -> r_fhole (a_reg st c) = false ->
    r_mapped_fa (a_reg st c) + KFAMAP <= 2 ^ 29 -> BackingAlgebra.model_ivs_wf mdl -> m_halted mdl = None -> a_kact st <= KCAP ->
    let lo := fa_beg SBEG c + r_mapped_fa (a_reg st c) in
    let addr : word := Z_to_bv 64 lo in let size : word := Z_to_bv 64 KFAMAP in
    let A2 := a_aa st ++ [(sh_lo lo, sh_lo lo + KFAMAP / 8)] in
    let OK := fixedin_ok_model 3 (Z_to_bv 64 50) addr size in let DS := fixedin_destroyed_model addr size in
    A_wf A2
    /\ (forall mdlm, same_but_materialized mdl mdlm -> MInv (a_aa st) mdlm ->
          U addr + U size <= alloc_top (m_vmmaps mdlm) /\ alloc_top (m_vmmaps mdlm) < two_pow_64
          /\ region_free (vm_reserved (m_vmmaps mdlm)) addr size = true /\ map_contains (vm_maps (m_vmmaps mdlm)) addr size = true
          /\ mmap_fixed_rw_budget_ok (Z_to_bv 64 50) mdlm addr size = true
          /\ m_halted (OK mdlm) = None /\ MInv (a_aa st) (OK mdlm)
          /\ (forall p, page_in_ranges p (m_vm_lazy (OK mdlm)) = true -> page_in_ranges p (m_vm_lazy mdl) = true)
          /\ m_halted (DS mdlm) = None /\ MInv (a_aa st) (DS mdlm)
          /\ (forall p, page_in_ranges p (m_vm_lazy (DS mdlm)) = true -> page_in_ranges p (m_vm_lazy mdl) = true))
    /\ (forall mdlm mdl4, same_but_materialized mdl mdlm -> same_but_materialized (OK mdlm) mdl4 -> MInv (a_aa st) mdl4 -> MInv A2 mdl4)
    /\ (forall mdlm mdl', same_but_materialized mdl mdlm -> same_but_materialized (OK mdlm) mdl' ->
          famap_ledger st c mdl mdl' /\ same_except_vm mdl mdl' /\ lazy_kept IA Lc FF mdl mdl' /\ BackingAlgebra.model_ivs_wf mdl' /\ m_halted mdl' = None)
    /\ (forall mdlm mdl', same_but_materialized mdl mdlm -> same_but_materialized (DS mdlm) mdl' ->
          ledger_destroyed bt mdl mdl' lo KFAMAP /\ eager_used mdl' <= eager_used mdl
          /\ same_except_vm mdl mdl' /\ lazy_kept IA Lc FF mdl mdl' /\ BackingAlgebra.model_ivs_wf mdl' /\ m_halted mdl' = None).
  (* [comment removed for export] *)
  Definition N3Fq_stmt : Prop := forall st Lc FF M0 mdl c qt qg,
    WFq bt st Lc FF qt qg -> qroom Lc qt qg -> Rep bt st Lc FF M0 mdl -> 1 <= c <= 30 -> r_fhole (a_reg st c) = false ->
    r_mapped_fa (a_reg st c) + KFAMAP <= 2 ^ 29 -> BackingAlgebra.model_ivs_wf mdl -> m_halted mdl = None -> a_kact st <= KCAP ->
    let lo := fa_beg SBEG c + r_mapped_fa (a_reg st c) in
    let addr : word := Z_to_bv 64 lo in let size : word := Z_to_bv 64 KFAMAP in
    let A2 := a_aa st ++ [(sh_lo lo, sh_lo lo + KFAMAP / 8)] in
    let OK := fixedin_ok_model 3 (Z_to_bv 64 50) addr size in let DS := fixedin_destroyed_model addr size in
    A_wf A2
    /\ (forall mdlm, same_but_materialized mdl mdlm -> MInv (a_aa st) mdlm ->
          U addr + U size <= alloc_top (m_vmmaps mdlm) /\ alloc_top (m_vmmaps mdlm) < two_pow_64
          /\ region_free (vm_reserved (m_vmmaps mdlm)) addr size = true /\ map_contains (vm_maps (m_vmmaps mdlm)) addr size = true
          /\ mmap_fixed_rw_budget_ok (Z_to_bv 64 50) mdlm addr size = true
          /\ m_halted (OK mdlm) = None /\ MInv (a_aa st) (OK mdlm)
          /\ (forall p, page_in_ranges p (m_vm_lazy (OK mdlm)) = true -> page_in_ranges p (m_vm_lazy mdl) = true)
          /\ m_halted (DS mdlm) = None /\ MInv (a_aa st) (DS mdlm)
          /\ (forall p, page_in_ranges p (m_vm_lazy (DS mdlm)) = true -> page_in_ranges p (m_vm_lazy mdl) = true))
    /\ (forall mdlm mdl4, same_but_materialized mdl mdlm -> same_but_materialized (OK mdlm) mdl4 -> MInv (a_aa st) mdl4 -> MInv A2 mdl4)
    /\ (forall mdlm mdl', same_but_materialized mdl mdlm -> same_but_materialized (OK mdlm) mdl' ->
          famap_ledger st c mdl mdl' /\ same_except_vm mdl mdl' /\ lazy_kept IA Lc FF mdl mdl' /\ BackingAlgebra.model_ivs_wf mdl' /\ m_halted mdl' = None)
    /\ (forall mdlm mdl', same_but_materialized mdl mdlm -> same_but_materialized (DS mdlm) mdl' ->
          ledger_destroyed bt mdl mdl' lo KFAMAP /\ eager_used mdl' <= eager_used mdl
          /\ same_except_vm mdl mdl' /\ lazy_kept IA Lc FF mdl mdl' /\ BackingAlgebra.model_ivs_wf mdl' /\ m_halted mdl' = None).

  Definition usermap_ledger (st : ast) (c : Z) (mdl mdl' : Model) : Prop :=
    let lo := region_beg SBEG c + r_mapped_user (a_reg st c) in
    (r_uhole (a_reg st c) = false -> vm_maps (m_vmmaps mdl') = vm_maps (m_vmmaps mdl))
    /\ (r_uhole (a_reg st c) = true -> Permutation (vm_maps (m_vmmaps mdl')) ((Z_to_bv 64 lo, Z_to_bv 64 KUSERMAP) :: vm_maps (m_vmmaps mdl)))
    /\ (forall a, in_ivz (vm_noaccess (m_vmmaps mdl')) a <-> in_ivz (vm_noaccess (m_vmmaps mdl)) a /\ ~ (lo <= a < lo + KUSERMAP))
    /\ Forall (fun e : word * word => 0 < bv_unsigned (snd e)) (vm_noaccess (m_vmmaps mdl'))
    /\ (forall a, pg_in_ivz (m_vm_lazy mdl') a <-> pg_in_ivz (m_vm_lazy mdl) a /\ ~ (lo <= a < lo + KUSERMAP))
    /\ Forall (fun iv : word * word => bv_unsigned (fst iv) mod PG = 0 /\ bv_unsigned (snd iv) mod PG = 0 /\ 0 < bv_unsigned (fst iv)
                                   /\ bv_unsigned (fst iv) + bv_unsigned (snd iv) <= CEIL
                                   /\ (bv_unsigned (fst iv) + bv_unsigned (snd iv) <= ia_img_lo IA \/ ia_img_hi IA <= bv_unsigned (fst iv)))
              (m_vm_lazy mdl')
    /\ vm_reserved (m_vmmaps mdl') = vm_reserved (m_vmmaps mdl) /\ vm_brk (m_vmmaps mdl') = vm_brk (m_vmmaps mdl)
    /\ vm_start_brk (m_vmmaps mdl') = vm_start_brk (m_vmmaps mdl) /\ vm_mmap_base (m_vmmaps mdl') = vm_mmap_base (m_vmmaps mdl)
    /\ vm_init_sp (m_vmmaps mdl') = vm_init_sp (m_vmmaps mdl) /\ vm_limit (m_vmmaps mdl') = vm_limit (m_vmmaps mdl)
    /\ eager_used mdl' <= eager_used mdl + KUSERMAP.

  Definition N3U_stmt : Prop := forall st Lc FF M0 mdl c,
    WF bt st Lc FF -> Rep bt st Lc FF M0 mdl -> 1 <= c <= 30 -> r_uhole (a_reg st c) = false ->
    r_mapped_user (a_reg st c) + KUSERMAP + KUSERMAP <= KREGION_EXHAUST -> BackingAlgebra.model_ivs_wf mdl -> m_halted mdl = None -> a_kact st <= KCAP ->
    let lo := region_beg SBEG c + r_mapped_user (a_reg st c) in
    let addr : word := Z_to_bv 64 lo in let size : word := Z_to_bv 64 KUSERMAP in
    let A2 := a_aa st ++ [(sh_lo lo, sh_lo lo + KUSERMAP / 8)] in
    let OK := fixedin_ok_model 3 (Z_to_bv 64 50) addr size in let DS := fixedin_destroyed_model addr size in
    A_wf A2
    /\ (forall mdlm, same_but_materialized mdl mdlm -> MInv (a_aa st) mdlm ->
          U addr + U size <= alloc_top (m_vmmaps mdlm) /\ alloc_top (m_vmmaps mdlm) < two_pow_64
          /\ region_free (vm_reserved (m_vmmaps mdlm)) addr size = true /\ map_contains (vm_maps (m_vmmaps mdlm)) addr size = true
          /\ mmap_fixed_rw_budget_ok (Z_to_bv 64 50) mdlm addr size = true
          /\ m_halted (OK mdlm) = None /\ MInv (a_aa st) (OK mdlm)
          /\ (forall p, page_in_ranges p (m_vm_lazy (OK mdlm)) = true -> page_in_ranges p (m_vm_lazy mdl) = true)
          /\ m_halted (DS mdlm) = None /\ MInv (a_aa st) (DS mdlm)
          /\ (forall p, page_in_ranges p (m_vm_lazy (DS mdlm)) = true -> page_in_ranges p (m_vm_lazy mdl) = true))
    /\ (forall mdlm mdl4, same_but_materialized mdl mdlm -> same_but_materialized (OK mdlm) mdl4 -> MInv (a_aa st) mdl4 -> MInv A2 mdl4)
    /\ (forall mdlm mdl', same_but_materialized mdl mdlm -> same_but_materialized (OK mdlm) mdl' ->
          usermap_ledger st c mdl mdl' /\ same_except_vm mdl mdl' /\ lazy_kept IA Lc FF mdl mdl' /\ BackingAlgebra.model_ivs_wf mdl' /\ m_halted mdl' = None)
    /\ (forall mdlm mdl', same_but_materialized mdl mdlm -> same_but_materialized (DS mdlm) mdl' ->
          ledger_destroyed bt mdl mdl' lo KUSERMAP /\ eager_used mdl' <= eager_used mdl
          /\ same_except_vm mdl mdl' /\ lazy_kept IA Lc FF mdl mdl' /\ BackingAlgebra.model_ivs_wf mdl' /\ m_halted mdl' = None).
  (* [comment removed for export] *)
  Definition N3Uq_stmt : Prop := forall st Lc FF M0 mdl c qt qg,
    WFq bt st Lc FF qt qg -> qroom Lc qt qg -> Rep bt st Lc FF M0 mdl -> 1 <= c <= 30 -> r_uhole (a_reg st c) = false ->
    r_mapped_user (a_reg st c) + KUSERMAP + KUSERMAP <= KREGION_EXHAUST -> BackingAlgebra.model_ivs_wf mdl -> m_halted mdl = None -> a_kact st <= KCAP ->
    let lo := region_beg SBEG c + r_mapped_user (a_reg st c) in
    let addr : word := Z_to_bv 64 lo in let size : word := Z_to_bv 64 KUSERMAP in
    let A2 := a_aa st ++ [(sh_lo lo, sh_lo lo + KUSERMAP / 8)] in
    let OK := fixedin_ok_model 3 (Z_to_bv 64 50) addr size in let DS := fixedin_destroyed_model addr size in
    A_wf A2
    /\ (forall mdlm, same_but_materialized mdl mdlm -> MInv (a_aa st) mdlm ->
          U addr + U size <= alloc_top (m_vmmaps mdlm) /\ alloc_top (m_vmmaps mdlm) < two_pow_64
          /\ region_free (vm_reserved (m_vmmaps mdlm)) addr size = true /\ map_contains (vm_maps (m_vmmaps mdlm)) addr size = true
          /\ mmap_fixed_rw_budget_ok (Z_to_bv 64 50) mdlm addr size = true
          /\ m_halted (OK mdlm) = None /\ MInv (a_aa st) (OK mdlm)
          /\ (forall p, page_in_ranges p (m_vm_lazy (OK mdlm)) = true -> page_in_ranges p (m_vm_lazy mdl) = true)
          /\ m_halted (DS mdlm) = None /\ MInv (a_aa st) (DS mdlm)
          /\ (forall p, page_in_ranges p (m_vm_lazy (DS mdlm)) = true -> page_in_ranges p (m_vm_lazy mdl) = true))
    /\ (forall mdlm mdl4, same_but_materialized mdl mdlm -> same_but_materialized (OK mdlm) mdl4 -> MInv (a_aa st) mdl4 -> MInv A2 mdl4)
    /\ (forall mdlm mdl', same_but_materialized mdl mdlm -> same_but_materialized (OK mdlm) mdl' ->
          usermap_ledger st c mdl mdl' /\ same_except_vm mdl mdl' /\ lazy_kept IA Lc FF mdl mdl' /\ BackingAlgebra.model_ivs_wf mdl' /\ m_halted mdl' = None)
    /\ (forall mdlm mdl', same_but_materialized mdl mdlm -> same_but_materialized (DS mdlm) mdl' ->
          ledger_destroyed bt mdl mdl' lo KUSERMAP /\ eager_used mdl' <= eager_used mdl
          /\ same_except_vm mdl mdl' /\ lazy_kept IA Lc FF mdl mdl' /\ BackingAlgebra.model_ivs_wf mdl' /\ m_halted mdl' = None).

  Hypothesis RL : res_low bt.

  (* [comment removed for export] *)
  Lemma slot_pack : forall st Lc FF M0 mdl lo qt qg,
    WFq bt st Lc FF qt qg -> qroom Lc qt qg -> Rep bt st Lc FF M0 mdl -> model_ivs_wf mdl -> m_halted mdl = None -> a_kact st <= KCAP ->
    (lo - SBEG) mod KUSERMAP = 0 -> SBEG <= lo -> lo + KUSERMAP <= SBEG + KSPACE ->
    (forall a, lo <= a < lo + KUSERMAP -> ~ holes bt st a) -> (forall a, lo <= a < lo + KUSERMAP -> ~ app_visible IA Lc FF a) ->
    let addr : word := Z_to_bv 64 lo in let size : word := Z_to_bv 64 KUSERMAP in
    let A2 := a_aa st ++ [(sh_lo lo, sh_lo lo + KUSERMAP / 8)] in
    let OK := fixedin_ok_model 3 (Z_to_bv 64 50) addr size in let DS := fixedin_destroyed_model addr size in
    A_wf A2
    /\ (forall mdlm, same_but_materialized mdl mdlm -> MInv (a_aa st) mdlm ->
          U addr + U size <= alloc_top (m_vmmaps mdlm) /\ alloc_top (m_vmmaps mdlm) < two_pow_64
          /\ region_free (vm_reserved (m_vmmaps mdlm)) addr size = true /\ map_contains (vm_maps (m_vmmaps mdlm)) addr size = true
          /\ mmap_fixed_rw_budget_ok (Z_to_bv 64 50) mdlm addr size = true
          /\ m_halted (OK mdlm) = None /\ MInv (a_aa st) (OK mdlm)
          /\ (forall p, page_in_ranges p (m_vm_lazy (OK mdlm)) = true -> page_in_ranges p (m_vm_lazy mdl) = true)
          /\ m_halted (DS mdlm) = None /\ MInv (a_aa st) (DS mdlm)
          /\ (forall p, page_in_ranges p (m_vm_lazy (DS mdlm)) = true -> page_in_ranges p (m_vm_lazy mdl) = true))
    /\ (forall mdlm mdl4, same_but_materialized mdl mdlm -> same_but_materialized (OK mdlm) mdl4 -> MInv (a_aa st) mdl4 -> MInv A2 mdl4).
  Proof.
    intros st Lc FF M0 mdl lo qt qg W HQ R MW HH KC SL1 SL2 SL3 NH NV. cbn zeta.
    split; [eapply A2_wf; eassumption|]. split.
    - intros mdlm SBM MI.
      edestruct (node_top bt st Lc FF M0 mdl lo) as [T1 T2]; try eassumption.
      edestruct (node_OK bt st Lc FF M0 mdl lo) as (O1 & O2 & O3); try eassumption.
      edestruct (node_DS bt st Lc FF mdl lo) as (D1 & D2 & D3); try eassumption.
      split; [exact T1|]. split; [exact T2|].
      split; [eapply node_region_free; eassumption|].
      split; [eapply node_map_contains; eassumption|].
      split; [eapply node_budget; eassumption|].
      split; [exact O1|]. split; [exact O2|]. split; [exact O3|]. split; [exact D1|]. split; [exact D2 | exact D3].
    - intros mdlm mdl4 SBM SBM4 MI. eapply (postOK_widen bt st Lc FF M0 mdl lo); eassumption.
  Qed.

  (* [comment removed for export] *)
  Theorem N3Fq_pf : N3Fq_stmt.
  Proof.
    intros st Lc FF M0 mdl c qt qg W HQ R Hc FH FR MW HH KC. cbn zeta.
    pose proof W as ((WR1 & _) & _). pose proof (WR1 c Hc) as (_ & MUK & MUX & _ & MF0 & MFK & _).
    set (lo := fa_beg SBEG c + r_mapped_fa (a_reg st c)).
    assert (SL1 : (lo - SBEG) mod KUSERMAP = 0) by (exact (fa_slot_aligned bt c _ MFK)).
    assert (SL2 : SBEG <= lo) by ((lazymatch goal with |- ?G => let G' := eval unfold lo, fa_beg, region_beg, KREGION, KFAOFF in G in change_no_check G' end); lia).
    assert (SL3 : lo + KUSERMAP <= SBEG + KSPACE) by (unfold lo, fa_beg, region_beg, KREGION, KFAOFF, KFAMAP, KUSERMAP, KSPACE in *; lia).
    assert (NH : forall a, lo <= a < lo + KUSERMAP -> ~ holes bt st a).
    { intros a Ha (c' & Hc' & [[UH Hr] | [FH' Hr]]).
      - destruct (WR1 c' Hc') as (((A0 & A1) & _) & _ & MUX' & _).
        unfold lo, fa_beg, region_beg, KREGION, KFAOFF, KFAMAP, KUSERMAP, KREGION_EXHAUST in *.
        assert (c' = c \/ c' + 1 <= c \/ c + 1 <= c') as [E | [E | E]] by lia; [subst c' |  |]; lia.
      - destruct (WR1 c' Hc') as (_ & _ & _ & _ & MF0' & _ & _ & _ & _ & _ & FHR). pose proof (FHR FH') as FR'.
        unfold lo, fa_beg, region_beg, KREGION, KFAOFF, KFAMAP, KUSERMAP, KREGION_EXHAUST in *.
        assert (c' = c \/ c' + 1 <= c \/ c + 1 <= c') as [E | [E | E]] by lia; [subst c'; rewrite FH in FH'; discriminate FH' | |]; lia. }
    assert (NV : forall a, lo <= a < lo + KUSERMAP -> ~ app_visible IA Lc FF a).
    { intros a Ha. exact (fslot_not_visible bt st Lc FF qt qg W c a Hc FR Ha). }
    destruct (slot_pack st Lc FF M0 mdl lo qt qg W HQ R MW HH KC SL1 SL2 SL3 NH NV) as (P1 & P2 & P3).
    split; [exact P1|]. split; [exact P2|]. split; [exact P3|]. split.
    - intros mdlm mdl' SBM SBM'. change (same_but_materialized (OKm (Z_to_bv 64 lo) (Z_to_bv 64 KUSERMAP) mdlm) mdl') in SBM'.
      destruct (postOK_ledger bt st Lc FF M0 mdl lo qt qg W R MW SL1 SL2 SL3 mdlm mdl' SBM SBM') as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11).
      destruct (postOK_rest bt st Lc FF mdl lo qt qg W MW HH SL1 SL2 SL3 NV mdlm mdl' SBM SBM') as (Q1 & Q2 & Q3 & Q4).
      split; [| split; [exact Q1|]; split; [exact Q2|]; split; [exact Q3 | exact Q4]].
      (lazymatch goal with |- ?G => let G' := eval unfold famap_ledger in G in change_no_check G' end). cbn zeta. fold lo.
      split; [intros _; exact G1|]. split; [intros E; rewrite FH in E; discriminate E|].
      split; [exact G2|]. split; [exact G3|]. split; [exact G4|]. split; [exact G5|].
      repeat (split; [assumption|]). exact (postOK_eager bt st Lc FF M0 mdl lo qt qg W R MW SL1 SL2 SL3 NH mdlm mdl' SBM SBM').
    - intros mdlm mdl' SBM SBM'. change (same_but_materialized (DSm (Z_to_bv 64 lo) (Z_to_bv 64 KUSERMAP) mdlm) mdl') in SBM'.
      destruct (postDS_rest bt st Lc FF mdl lo qt qg W MW HH SL1 SL2 SL3 NV mdlm mdl' SBM SBM') as (Q1 & Q2 & Q3 & Q4).
      split; [exact (postDS_ledger bt st Lc FF M0 mdl lo qt qg W R MW SL1 SL2 SL3 mdlm mdl' SBM SBM')|].
      split; [exact (postDS_eager mdl lo MW mdlm mdl' SBM SBM')|]. split; [exact Q1|]. split; [exact Q2|]. split; [exact Q3 | exact Q4].
  Qed.

  Theorem N3F_pf : N3F_stmt.
  Proof. intros st Lc FF M0 mdl c W. exact (N3Fq_pf st Lc FF M0 mdl c (2 ^ 20) (2 ^ 28) W (qroom_WF bt st Lc FF W)). Qed.

  (* [comment removed for export] *)
  Theorem N3Uq_pf : N3Uq_stmt.
  Proof.
    intros st Lc FF M0 mdl c qt qg W HQ R Hc UH UR MW HH KC. cbn zeta.
    pose proof W as ((WR1 & _) & _). pose proof (WR1 c Hc) as (_ & MUK & MUX & _ & MF0 & MFK & _).
    set (lo := region_beg SBEG c + r_mapped_user (a_reg st c)).
    assert (MU0 : 0 <= r_mapped_user (a_reg st c)) by (destruct (WR1 c Hc) as (((A0 & A1) & _) & _); lia).
    assert (SL1 : (lo - SBEG) mod KUSERMAP = 0) by (exact (user_slot_aligned bt c _ MUK)).
    assert (SL2 : SBEG <= lo) by ((lazymatch goal with |- ?G => let G' := eval unfold lo, region_beg, KREGION in G in change_no_check G' end); lia).
    assert (SL3 : lo + KUSERMAP <= SBEG + KSPACE) by (unfold lo, region_beg, KREGION, KUSERMAP, KSPACE, KREGION_EXHAUST in *; lia).
    assert (NH : forall a, lo <= a < lo + KUSERMAP -> ~ holes bt st a).
    { intros a Ha (c' & Hc' & [[UH' Hr] | [FH' Hr]]).
      - destruct (WR1 c' Hc') as (((A0 & A1) & _) & _ & MUX' & _).
        unfold lo, fa_beg, region_beg, KREGION, KFAOFF, KFAMAP, KUSERMAP, KREGION_EXHAUST in *.
        assert (c' = c \/ c' + 1 <= c \/ c + 1 <= c') as [E | [E | E]] by lia; [subst c'; rewrite UH in UH'; discriminate UH' | |]; lia.
      - destruct (WR1 c' Hc') as (_ & _ & _ & _ & MF0' & _ & _ & _ & _ & _ & FHR). pose proof (FHR FH') as FR'.
        unfold lo, fa_beg, region_beg, KREGION, KFAOFF, KFAMAP, KUSERMAP, KREGION_EXHAUST in *.
        assert (c' = c \/ c' + 1 <= c \/ c + 1 <= c') as [E | [E | E]] by lia; [subst c' | |]; lia. }
    assert (NV : forall a, lo <= a < lo + KUSERMAP -> ~ app_visible IA Lc FF a).
    { intros a Ha. exact (uslot_not_visible bt st Lc FF qt qg W c a Hc Ha). }
    destruct (slot_pack st Lc FF M0 mdl lo qt qg W HQ R MW HH KC SL1 SL2 SL3 NH NV) as (P1 & P2 & P3).
    split; [exact P1|]. split; [exact P2|]. split; [exact P3|]. split.
    - intros mdlm mdl' SBM SBM'. change (same_but_materialized (OKm (Z_to_bv 64 lo) (Z_to_bv 64 KUSERMAP) mdlm) mdl') in SBM'.
      destruct (postOK_ledger bt st Lc FF M0 mdl lo qt qg W R MW SL1 SL2 SL3 mdlm mdl' SBM SBM') as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11).
      destruct (postOK_rest bt st Lc FF mdl lo qt qg W MW HH SL1 SL2 SL3 NV mdlm mdl' SBM SBM') as (Q1 & Q2 & Q3 & Q4).
      split; [| split; [exact Q1|]; split; [exact Q2|]; split; [exact Q3 | exact Q4]].
      (lazymatch goal with |- ?G => let G' := eval unfold usermap_ledger in G in change_no_check G' end). cbn zeta. fold lo.
      split; [intros _; exact G1|]. split; [intros E; rewrite UH in E; discriminate E|].
      split; [exact G2|]. split; [exact G3|]. split; [exact G4|]. split; [exact G5|].
      repeat (split; [assumption|]). exact (postOK_eager bt st Lc FF M0 mdl lo qt qg W R MW SL1 SL2 SL3 NH mdlm mdl' SBM SBM').
    - intros mdlm mdl' SBM SBM'. change (same_but_materialized (DSm (Z_to_bv 64 lo) (Z_to_bv 64 KUSERMAP) mdlm) mdl') in SBM'.
      destruct (postDS_rest bt st Lc FF mdl lo qt qg W MW HH SL1 SL2 SL3 NV mdlm mdl' SBM SBM') as (Q1 & Q2 & Q3 & Q4).
      split; [exact (postDS_ledger bt st Lc FF M0 mdl lo qt qg W R MW SL1 SL2 SL3 mdlm mdl' SBM SBM')|].
      split; [exact (postDS_eager mdl lo MW mdlm mdl' SBM SBM')|]. split; [exact Q1|]. split; [exact Q2|]. split; [exact Q3 | exact Q4].
  Qed.
  Theorem N3U_pf : N3U_stmt.
  Proof. intros st Lc FF M0 mdl c W. exact (N3Uq_pf st Lc FF M0 mdl c (2 ^ 20) (2 ^ 28) W (qroom_WF bt st Lc FF W)). Qed.
End N3.
