(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import Uint63 Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run Fs.
From OSSVerify.Proofs.openssl.bignum.lib.AS Require Import AsanAcct.
From OSSVerify.Proofs.openssl.bignum.lib.VCommon Require Import FastWord.
From OSSVerify.Proofs.openssl.bignum.lib.VCommon.Ax Require Import AxLazy AxLin AxVal AxMem AxState AxSys AxAcct AxMeasure AxLz AxFd AxModelRel.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Section ExportM.
Variable segs : list Segment.
Variable fs0 : Fs.Fs.
Variable LIM : Z.
Variable ρ : valuation.
Variable B : AST.
Variable ms : machine_state.
Variable model : Model.
Hypothesis HR : R segs amodel (MR segs fs0 ρ) LIM ρ B (mkCfg ms model).

Let HM : MR segs fs0 ρ (a_model B) model := r_model _ _ _ _ _ _ _ HR.
Let Hsat : sat ρ (a_facts B) := r_sat _ _ _ _ _ _ _ HR.
Let HLZ := mr_lz segs fs0 ρ (a_model B) model HM.

Definition big_top_ok (top : Z) : bool :=
  forallb (fun e => (ae_size e <? BIGMIN) || match lrange (a_facts B) (ae_base e) with Some (lo, _) => top <=? lo | None => false end)
          (am_maps (a_model B)).

Lemma ex_big_top (top : Z) : big_top_ok top = true -> forall e, In e (am_maps (a_model B)) -> BIGMIN <= ae_size e -> top <= leval ρ (ae_base e).
Proof.
  intros H e He Hb. unfold big_top_ok in H. rewrite forallb_forall in H. specialize (H e He). apply orb_prop in H as [H|H].
  - apply Z.ltb_lt in H. lia.
  - destruct (lrange (a_facts B) (ae_base e)) as [[lo hi]|] eqn:El; [|discriminate H]. apply Z.leb_le in H.
    pose proof (lrange_sound ρ _ _ Hsat _ El) as X. cbn [fst snd] in X. lia.
Qed.

Lemma ex_noaccess_pos : Forall (fun q : word * word => 0 < bv_unsigned (snd q)) (vm_noaccess (m_vmmaps model)).
Proof. destruct HLZ as (_ & _ & Z4 & _). apply Forall_forall. intros q Hq. exact (proj1 (proj1 (Forall_forall _ _) Z4 q Hq)). Qed.

Theorem ex_ranges_from (top : Z) : big_top_ok top = true -> ranges_from_b (m_vm_lazy model) top = true.
Proof.
  intros H. unfold ranges_from_b. apply forallb_forall. intros r Hr. apply Z.leb_le.
  destruct HLZ as (Z1 & _ & _ & Z6). pose proof (proj1 (proj1 (Forall_forall _ _) Z6 r Hr)) as Hpos.
  destruct (Z1 r Hr Hpos) as (e & He & Hb & E1 & _). pose proof (ex_big_top top H e He Hb) as X. unfold ent_lo, bas in *. lia.
Qed.

Theorem ex_lazy_in_maps : forall iv, In iv (m_vm_lazy model) -> 0 < bv_unsigned (snd iv) ->
  exists e, In e (vm_maps (m_vmmaps model)) /\ bv_unsigned (fst e) <= bv_unsigned (fst iv)
            /\ bv_unsigned (fst iv) + bv_unsigned (snd iv) <= bv_unsigned (fst e) + bv_unsigned (snd e).
Proof.
  intros iv Hiv Hpos. destruct HLZ as (Z1 & _). destruct (Z1 iv Hiv Hpos) as (e & He & _ & E1 & E2).
  exists (ent_val ρ e). split; [exact (MR_ent_in segs fs0 ρ _ model e HM He)|].
  pose proof (MR_ent segs fs0 ρ _ model e HM He) as Hok. fold (bas (ent_val ρ e)). fold (bsz (ent_val ρ e)).
  rewrite (ent_val_bas ρ e Hok), (ent_val_bsz ρ e Hok). unfold ent_lo, ent_hi, bas, bsz in *. lia.
Qed.

Theorem ex_shadow_lazy : am_shadow (a_model B) = true -> forall a : word,
  (2147446784 <= bv_unsigned a < 2415882240) \/ (2201439137792 <= bv_unsigned a < 17594333495296) ->
  page_in_ranges (page_base a) (m_vm_lazy model) = true /\ ~ inl (vm_noaccess (m_vmmaps model)) (bv_unsigned a).
Proof.
  intros Hsh a Ha. destruct (mr_shadow segs fs0 ρ _ model HM Hsh) as (S1 & _ & S3). destruct HLZ as (_ & Z2 & _).
  destruct Ha as [Ha|Ha].
  - apply (Z2 ls_ent S1 eq_refl a). unfold ent_lo, ent_hi, leval, ls_ent. cbn [ae_base ae_size fst snd teval]. lia.
  - apply (Z2 hs_ent S3 eq_refl a). unfold ent_lo, ent_hi, leval, hs_ent. cbn [ae_base ae_size fst snd teval]. lia.
Qed.

Theorem ex_minv (J : Z) (W : list (Z * Z)) :
  0 <= J -> J mod 4096 = 0 -> Forall (fun iv => 0 < snd iv) W ->
  a_budget B <= J -> a_budget B + (J + A_bytes W) <= LIM ->
  MInv ((- J, 0) :: W) model.
Proof.
  intros HJ0 HJa HW Hb1 Hb2. destruct (r_budget _ _ _ _ _ _ _ HR) as [Hu Hl]. cbn [cfg_model] in Hu, Hl.
  rewrite vm_backing_used_split in Hu. unfold page_size in Hu.
  assert (He0 : 0 <= eager_used model) by (unfold eager_used; apply AxAcct.live_bytes_nonneg).
  assert (EA : A_bytes ((- J, 0) :: W) = J + A_bytes W) by (cbn [A_bytes fst snd]; lia).
  assert (EW : List.filter (fun iv : Z * Z => snd iv <=? 0) W = []).
  { clear - HW. induction HW as [|iv r Hp Hr IH]; [reflexivity|]. cbn [List.filter].
    destruct (snd iv <=? 0) eqn:E; [apply Z.leb_le in E; lia | exact IH]. }
  assert (EN : A_neg ((- J, 0) :: W) = [(- J, 0)]).
  { unfold A_neg. cbn [List.filter snd]. change (0 <=? 0) with true. cbv iota. rewrite EW. reflexivity. }
  constructor.
  - exists [], (m_vm_materialized model). cbn [app]. split; [apply Permutation_refl|]. split; [constructor|].
    split; [intros p []|]. split; [intros p []|]. split; [intros p []|].
    rewrite EN. cbn [A_bytes fst snd]. unfold page_size. lia.
  - rewrite EA, Hl. lia.
Qed.

End ExportM.

Section ExportM2.
Variable segs : list Segment.
Variable fs0 : Fs.Fs.
Variable LIM : Z.
Variable ρ : valuation.
Variable B : AST.
Variable ms : machine_state.
Variable model : Model.
Hypothesis HR : R segs amodel (MR segs fs0 ρ) LIM ρ B (mkCfg ms model).

Let HM : MR segs fs0 ρ (a_model B) model := r_model _ _ _ _ _ _ _ HR.
Let Hsat : sat ρ (a_facts B) := r_sat _ _ _ _ _ _ _ HR.

Theorem ex_maps_apart : ForallOrdPairs (fun p q : word * word =>
    bv_unsigned (fst p) + bv_unsigned (snd p) <= bv_unsigned (fst q) \/ bv_unsigned (fst q) + bv_unsigned (snd q) <= bv_unsigned (fst p))
  (vm_maps (m_vmmaps model)).
Proof.
  pose proof (mr_pw segs fs0 ρ _ model HM) as Hpw. induction (vm_maps (m_vmmaps model)) as [|p l IH]; [constructor|].
  destruct (pw_disj_inv p l Hpw) as [H1 H2]. constructor; [|exact (IH H2)].
  apply Forall_forall. intros q Hq. specialize (H1 q Hq). unfold iv_disj, bas, bsz in H1. lia.
Qed.

Theorem ex_maps_pos : Forall (fun e : word * word => 0 < bv_unsigned (snd e)) (vm_maps (m_vmmaps model)).
Proof. apply Forall_forall. intros q Hq. exact (MR_maps_pos segs fs0 ρ _ model HM q Hq). Qed.

Theorem ex_nowrap : (forall q, In q (vm_maps (m_vmmaps model)) -> bv_unsigned (fst q) + bv_unsigned (snd q) <= 2 ^ 64)
  /\ (forall q, In q (vm_noaccess (m_vmmaps model)) -> bv_unsigned (fst q) + bv_unsigned (snd q) <= 2 ^ 64)
  /\ (forall q, In q (m_vm_lazy model) -> bv_unsigned (fst q) + bv_unsigned (snd q) <= 2 ^ 64).
Proof.
  split; [|split]; intros q Hq.
  - exact (MR_maps_nowrap segs fs0 ρ _ model HM q Hq).
  - exact (mr_na segs fs0 ρ _ model HM q Hq).
  - exact (MR_lazy_nowrap segs fs0 ρ _ model HM q Hq).
Qed.

Theorem ex_confined (z : Z) : inl (vm_noaccess (m_vmmaps model) ++ m_vm_lazy model) z -> inl (vm_maps (m_vmmaps model)) z.
Proof.
  intros [p [Hp Hz]]. apply in_app_or in Hp as [Hp|Hp].
  - apply (mr_na_maps segs fs0 ρ _ model HM z). exists p. split; [exact Hp | exact Hz].
  - destruct (ex_lazy_in_maps segs fs0 LIM ρ B ms model HR p Hp ltac:(unfold bas, bsz in Hz; lia)) as (e & He & E1 & E2).
    exists e. split; [exact He|]. unfold bas, bsz in *. lia.
Qed.

Definition atop_ok (lo : Z) : bool :=
  match lrange (a_facts B) (am_atop (a_model B)) with Some (l, _) => lo <=? l | None => false end.

Theorem ex_eager : eager_used model <= a_budget B.
Proof.
  destruct (r_budget _ _ _ _ _ _ _ HR) as [Hu _]. cbn [cfg_model] in Hu. rewrite vm_backing_used_split in Hu. unfold page_size in Hu. lia.
Qed.

Theorem ex_misc : vm_reserved (m_vmmaps model) = segments_reserved segs /\ vm_limit (m_vmmaps model) = LIM
  /\ m_fs model = fs0 /\ m_halted model = None.
Proof.
  destruct (r_budget _ _ _ _ _ _ _ HR) as [_ Hl]. repeat split.
  - exact (mr_res segs fs0 ρ _ model HM).
  - exact Hl.
  - exact (mr_fs segs fs0 ρ _ model HM).
  - exact (r_halted _ _ _ _ _ _ _ HR).
Qed.

End ExportM2.

Lemma ex_fds (segs : list Segment) (fs0 : Fs.Fs) (LIM : Z) (ρ : valuation) (B : AST) (ms : machine_state) (model : Model) :
  R segs amodel (MR segs fs0 ρ) LIM ρ B (mkCfg ms model) -> am_fd (a_model B) = FDStd ->
  m_fds model = [ (Z_to_bv 64 0, FdChannel (Z_to_bv 64 0)); (Z_to_bv 64 1, FdChannel (Z_to_bv 64 1)); (Z_to_bv 64 2, FdChannel (Z_to_bv 64 2)) ]
  /\ valid_argv (AxFd.dec_argvB ρ).
Proof.
  intros HR Hfd. destruct (mr_fds segs fs0 ρ _ model (r_model _ _ _ _ _ _ _ HR)) as [Hg [Hf _]]. rewrite Hfd in Hf. split; [exact Hf | exact Hg].
Qed.
