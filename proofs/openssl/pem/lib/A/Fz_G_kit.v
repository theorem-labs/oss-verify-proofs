(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Common Require Import ShapeAlg AsanAcct.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import Tac ImageA RzCPS NodesA SysStep.
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Layout RT_iface D_defs D_kit D_agree D_clx R_cache_defs Fz_kit.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Lemma wg_not_outside_cons : forall lo hi (W : list (Z * Z)) x, ~ outside ((lo, hi) :: W) x -> (lo <= x < hi) \/ ~ outside W x.
Proof.
  intros lo hi W x H. cbn [outside] in H. destruct (Z_le_dec lo x) as [A|A]; [destruct (Z_lt_dec x hi) as [B|B]|].
  - left. lia.
  - right. intros O. apply H. split; [lia | exact O].
  - right. intros O. apply H. split; [lia | exact O].
Qed.

Lemma wg_mod16_8 : forall p, p mod 16 = 0 -> p mod 8 = 0.
Proof. intros p H. replace p with (16 * (p / 16)) by (pose proof (Z.div_mod p 16 ltac:(lia)); lia). replace (16 * (p / 16)) with (p / 16 * 2 * 8) by lia. apply Z.mod_mul. lia. Qed.

Lemma wg_mod16_4 : forall p, p mod 16 = 0 -> p mod 4 = 0.
Proof. intros p H. replace p with (16 * (p / 16)) by (pose proof (Z.div_mod p 16 ltac:(lia)); lia). replace (16 * (p / 16)) with (p / 16 * 4 * 4) by lia. apply Z.mod_mul. lia. Qed.
Lemma wg_mod8_4 : forall p, p mod 8 = 0 -> p mod 4 = 0.
Proof. intros p H. replace p with (8 * (p / 8)) by (pose proof (Z.div_mod p 8 ltac:(lia)); lia). replace (8 * (p / 8)) with (p / 8 * 2 * 4) by lia. apply Z.mod_mul. lia. Qed.
Lemma wg_land7 : forall x, 0 <= x -> Z.land x 7 = x mod 8.
Proof. intros x Hx. change 7 with (Z.ones 3). rewrite Z.land_ones by lia. reflexivity. Qed.
Lemma wg_land3 : forall x, 0 <= x -> Z.land x 3 = x mod 4.
Proof. intros x Hx. change 3 with (Z.ones 2). rewrite Z.land_ones by lia. reflexivity. Qed.
Lemma wg_land15 : forall x, 0 <= x -> Z.land x 15 = x mod 16.
Proof. intros x Hx. change 15 with (Z.ones 4). rewrite Z.land_ones by lia. reflexivity. Qed.
(* [comment removed for export] *)
Lemma wg_lxor_ones : forall x, 0 <= x < 2^64 -> Z.lxor x 18446744073709551615 = 18446744073709551615 - x.
Proof.
  intros x Hx. change 18446744073709551615 with (Z.ones 64).
  assert (L : x = 0 \/ Z.log2 x < 64). { destruct (Z.eq_dec x 0) as [->|]; [left; reflexivity| right; apply Z.log2_lt_pow2; lia]. }
  assert (LG : x = 0 -> Z.log2 x < 64) by (intros ->; cbn; lia).
  assert (LL : Z.log2 x < 64) by (destruct L as [E|L']; [apply LG; exact E | exact L']).
  rewrite <- Z.ldiff_ones_l_low; [| lia | exact LL].
  symmetry. apply Z.sub_nocarry_ldiff. apply Z.ldiff_ones_r_low; [lia | exact LL].
Qed.

(* [comment removed for export] *)
Ltac wg_modfacts :=
  repeat match goal with
  | H : ?x mod 16 = 0 |- context [?x mod 8] => rewrite (wg_mod16_8 x H)
  | H : ?x mod 16 = 0 |- context [?x mod 4] => rewrite (wg_mod16_4 x H)
  | H : ?x mod 8 = 0 |- context [?x mod 4] => rewrite (wg_mod8_4 x H)
  | H : ?x mod ?k = 0 |- context [?x mod ?k] => rewrite H
  end.
Ltac wg_cond :=
  rewrite ?wg_land7, ?wg_land3, ?wg_land15, ?wg_lxor_ones by lia; wg_modfacts;
  unfold_cond; fold_lit_ux; rewrite ?unsigned_lit by lia; solve_cond_rec.

Section WgKit.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.

(* [comment removed for export] *)
Lemma wg_seg_ART : forall Σ (m m' : mem) usp d (W : list (Z * Z)), ART RT Σ m -> rt_sp0 RT Σ - STACK_WIN <= usp - d -> usp <= USTACK_TOP ->
  munch (W ++ [(usp - d, usp)]) m m' -> (forall x, ~ outside W x -> client_static x \/ in_live (rt_live RT Σ) x) -> wmono asegs m m' -> ART RT Σ m'.
Proof using AF.
  intros Σ m m' usp d W HA H1 H2 MU HW WM. apply (af_frame RT AF Σ m m' (usp - d) HA H1); [|exact WM].
  intros a Ha. apply MU. apply outside_app_intro.
  - destruct (outside_dec W (bv_unsigned a)) as [O|O]; [exact O|]. exfalso. apply Ha. destruct (HW _ O) as [S|L]; [right; left; exact S | right; right; left; exact L].
  - cbn [outside]. split; [intros Hin; apply Ha; left; lia | exact I].
Qed.

(* [comment removed for export] *)
Lemma wg_seg_pres : forall live frames Σ (m m' : mem) usp d (W WS : list (Z * Z)), ART RT Σ m -> rt_sp0 RT Σ - STACK_WIN <= usp - d -> 0 <= d ->
  munch (W ++ [(usp - d, usp)]) m m' ->
  (forall x, aclient live frames usp x -> aclient (rt_live RT Σ) (rt_frames RT Σ) usp x) ->
  (forall x, aclient live frames usp x -> outside WS x -> outside W x) ->
  rt_pres_fp live frames usp WS m m'.
Proof using AF.
  intros live frames Σ m m' usp d W WS HA H1 H2 MU HM HW a Ha Ho. apply MU. apply outside_app_intro; [exact (HW _ Ha Ho)|].
  cbn [outside]. split; [destruct (cl_split RT AF Σ m usp d _ HA H1 H2 (HM _ Ha)); lia | exact I].
Qed.

End WgKit.

(* [comment removed for export] *)
Lemma wg_mcost_nonneg : forall n, 0 <= mcost n.
Proof. intros n. unfold mcost. destruct (n <=? 64512) eqn:E; [lia|]. apply Z.leb_gt in E. lia. Qed.

(* [comment removed for export] *)
Lemma wg_keep_seg : forall W (m m' : mem) X cs, rw_cells asegs m X cs -> munch W m m' -> wmono asegs m m' ->
  (forall x, X <= x < X + Z.of_nat (cells_size cs) -> outside W x) -> rw_cells asegs m' X cs.
Proof.
  intros W m m' X cs H MU WM HO. apply (rw_cells_agree asegs m m' X cs H); [|exact WM].
  intros a Ha. apply MU. exact (HO _ Ha).
Qed.

Lemma wg_keep_live : forall live frames sp W (m m' : mem) p n X cs, rw_cells asegs m X cs -> rt_pres_fp live frames sp W m m' -> wmono asegs m m' ->
  In (p, n) live -> p <= X -> X + Z.of_nat (cells_size cs) <= p + n ->
  (forall x, X <= x < X + Z.of_nat (cells_size cs) -> outside W x) -> rw_cells asegs m' X cs.
Proof.
  intros live frames sp W m m' p n X cs H PR WM IN H1 H2 HO. apply (rw_cells_agree asegs m m' X cs H); [|exact WM].
  intros a Ha. apply PR; [|exact (HO _ Ha)]. right; right; left. exists p, n. split; [exact IN | lia].
Qed.

Section WgKit2.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.

(* [comment removed for export] *)
Lemma wg_newchunk_apart : forall (Σ Σ1 : rts RT) (m1 : mem) (NEW : list (Z * Z)) p n usp a,
  ART RT Σ1 m1 -> rt_live RT Σ1 = NEW ++ rt_live RT Σ -> In (p, n) NEW -> rt_frames RT Σ1 = rt_frames RT Σ -> rt_sp0 RT Σ1 = rt_sp0 RT Σ ->
  rt_sp0 RT Σ - STACK_WIN <= usp -> 0 <= n -> aclient (rt_live RT Σ) (rt_frames RT Σ) usp a -> ~ (p <= a < p + n).
Proof using AF.
  intros Σ Σ1 m1 NEW p n usp a ART1 LV INN FRS SP0 LU Hn Ha.
  assert (INL : In (p, n) (rt_live RT Σ1)) by (rewrite LV; apply in_or_app; left; exact INN).
  pose proof (af_live_range RT AF Σ1 m1 p n ART1 INL) as (R0 & R1 & R2). rewrite SP0 in R1.
  destruct Ha as [H|[H|[H|[H|H]]]].
  - lia.
  - pose proof (client_static_range a H). unfold SEGTOP_A in *. lia.
  - destruct H as (p2 & n2 & Hin & Hp).
    destruct (in_split _ _ INN) as (l1 & l2 & EN). rewrite EN, <- app_assoc in LV. cbn [app] in LV.
    destruct (af_live_disj RT AF Σ1 m1 p n p2 n2 l1 (l2 ++ rt_live RT Σ) ART1 LV ltac:(apply in_or_app; right; apply in_or_app; right; exact Hin)); lia.
  - destruct H as (f & k & Hin & Hf). rewrite <- FRS in Hin.
    pose proof (af_frames_range RT AF Σ1 m1 f k ART1 Hin) as (_ & _ & _ & R3). destruct (R3 p n INL); lia.
  - destruct H as (f & k & Hin & Hf). rewrite <- FRS in Hin.
    pose proof (af_fshadow_apart RT AF Σ1 m1 f k ART1 Hin) as (SL & _). destruct (SL p n INL); lia.
Qed.

(* [comment removed for export] *)
Lemma wg_live_apart : forall (Σ1 : rts RT) (m1 : mem) l1 p n l2 p2 n2,
  ART RT Σ1 m1 -> rt_live RT Σ1 = l1 ++ (p, n) :: l2 -> In (p2, n2) (l1 ++ l2) -> p + n <= p2 \/ p2 + n2 <= p.
Proof using AF. intros Σ1 m1 l1 p n l2 p2 n2 A LV IN. exact (af_live_disj RT AF Σ1 m1 p n p2 n2 l1 l2 A LV IN). Qed.

End WgKit2.

(* [comment removed for export] *)
Lemma wg_keep_seg_ro : forall W (m m' : mem) X cs, ro_cells asegs m X cs -> munch W m m' ->
  (forall x, X <= x < X + Z.of_nat (cells_size cs) -> outside W x) -> ro_cells asegs m' X cs.
Proof. intros W m m' X cs H MU HO. apply (ro_cells_agree asegs m m' X cs H). intros a Ha. apply MU. exact (HO _ Ha). Qed.

Lemma wg_keep_static : forall live frames sp W (m m' : mem) X cs, rw_cells asegs m X cs -> rt_pres_fp live frames sp W m m' -> wmono asegs m m' ->
  (forall x, X <= x < X + Z.of_nat (cells_size cs) -> client_static x /\ outside W x) -> rw_cells asegs m' X cs.
Proof.
  intros live frames sp W m m' X cs H PR WM HO. apply (rw_cells_agree asegs m m' X cs H); [|exact WM].
  intros a Ha. destruct (HO _ Ha) as [S O]. apply PR; [right; left; exact S | exact O].
Qed.

Lemma wg_keep_static_ro : forall live frames sp W (m m' : mem) X cs, ro_cells asegs m X cs -> rt_pres_fp live frames sp W m m' ->
  (forall x, X <= x < X + Z.of_nat (cells_size cs) -> client_static x /\ outside W x) -> ro_cells asegs m' X cs.
Proof.
  intros live frames sp W m m' X cs H PR HO. apply (ro_cells_agree asegs m m' X cs H).
  intros a Ha. destruct (HO _ Ha) as [S O]. apply PR; [right; left; exact S | exact O].
Qed.

Lemma wg_rw_ro : forall (m : mem) X cs, rw_cells asegs m X cs -> ro_cells asegs m X cs.
Proof. intros m X cs H. exact (proj1 H). Qed.
