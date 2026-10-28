(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import Tac ImageA.
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Layout RT_iface D_defs D_kit D_agree D_clx I_lkit Fz_kit.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Lemma live_remove_cons_ne : forall p q n (l : list (Z * Z)), q <> p -> live_remove p ((q, n) :: l) = (q, n) :: live_remove p l.
Proof. intros p q n l NE. unfold live_remove. cbn. rewrite (proj2 (Z.eqb_neq q p) NE). cbn. reflexivity. Qed.

Lemma bytes_at_inj : forall (m : mem) a (b1 b2 : list byte), bytes_at asegs m a b1 -> bytes_at asegs m a b2 -> length b1 = length b2 -> b1 = b2.
Proof.
  intros m a b1 b2 (_ & _ & H1) (_ & _ & H2) HL. apply nth_error_ext. intros i.
  destruct (Nat.lt_ge_cases i (length b1)) as [Hi|Hi].
  - rewrite <- (H1 i Hi), <- (H2 i ltac:(lia)). reflexivity.
  - rewrite (proj2 (nth_error_None b1 i) Hi), (proj2 (nth_error_None b2 i) ltac:(lia)). reflexivity.
Qed.

(* [comment removed for export] *)
Lemma wr_at_bytes : forall (m : mem) a n, wr_at asegs m a n -> 0 <= n -> exists bs, bytes_at asegs m a bs /\ Z.of_nat (length bs) = n.
Proof.
  intros m a n WR Hn. destruct (I_lkit.wr_at_rw_CB m a n WR Hn) as (junk & ((WF & _) & BY) & _).
  cbn [cells_bytes cbytes] in BY. rewrite app_nil_r in BY. exists junk. split; [exact BY|]. cbn in WF. rewrite WF. lia.
Qed.

(* [comment removed for export] *)
Lemma acc_of_shadow0 : forall (m : mem) g, bytes_at asegs m (shad g) [z8] -> g mod 8 = 0 -> 0 <= g -> acc asegs m g 8.
Proof.
  intros m g HB H8 H0 i Hi. exists z8. split; [| left; reflexivity].
  assert (ES : shad (g + i) = shad g).
  { unfold shad. f_equal. pose proof (Z.div_mod g 8 ltac:(lia)) as D. rewrite H8 in D.
    replace (g + i) with (g / 8 * 8 + i) by lia. rewrite Z.div_add_l by lia. rewrite (Z.div_small i 8) by lia. lia. }
  rewrite ES. exact HB.
Qed.
Lemma rw_C1_bytes : forall (m : mem) a b, rw_cells asegs m a [C1 b] -> bytes_at asegs m a [b].
Proof. intros m a b [[_ HB] _]. cbn [cells_bytes cbytes] in HB. rewrite app_nil_r in HB. exact HB. Qed.

Section MKit.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.

Lemma live_checked_dst : forall (Σ : rts RT) (m : mem) (sp : word) p n d k, ART RT Σ m -> In (p, n) (rt_live RT Σ) ->
  p <= d -> d + k <= p + n -> 0 <= k -> checked_dst RT Σ m sp d k.
Proof using AF.
  intros Σ m sp p n d k HA Hin H1 H2 Hk. pose proof (af_acc_live RT AF Σ m p n HA Hin) as (WR & ACC).
  split; [intros _; split; [exact (acc_sub asegs m p n d k ACC H1 H2) | left; exists p, n; split; [exact Hin | lia]]|].
  split; [intros i Hi; right; right; left; exists p, n; split; [exact Hin | lia]|].
  exact (wr_at_sub m p n d k WR H1 H2 Hk).
Qed.

Lemma live_checked_src : forall (Σ : rts RT) (m : mem) (sp : word) lo p n s k, ART RT Σ m -> In (p, n) (rt_live RT Σ) ->
  p <= s -> s + k <= p + n -> rt_sp0 RT Σ - STACK_WIN <= lo -> checked_src RT Σ m sp lo s k.
Proof using AF.
  intros Σ m sp lo p n s k HA Hin H1 H2 LOW. pose proof (af_acc_live RT AF Σ m p n HA Hin) as (WR & ACC).
  pose proof (af_live_range RT AF Σ m p n HA Hin) as (_ & R1 & _).
  split; [intros _; split; [exact (acc_sub asegs m p n s k ACC H1 H2) | left; exists p, n; split; [exact Hin | lia]]|].
  left. lia.
Qed.

Lemma removed_apart : forall (Σ : rts RT) (m : mem) p n usp a, ART RT Σ m -> In (p, n) (rt_live RT Σ) ->
  rt_sp0 RT Σ - STACK_WIN <= usp -> aclient (live_remove p (rt_live RT Σ)) (rt_frames RT Σ) usp a -> ~ (p <= a < p + n).
Proof using AF.
  intros Σ m p n usp a HA Hin LU Ha. pose proof (af_live_range RT AF Σ m p n HA Hin) as (R0 & R1 & R2).
  destruct Ha as [H|[H|[H|[H|H]]]].
  - lia.
  - pose proof (client_static_range a H). unfold SEGTOP_A in *. lia.
  - destruct H as (p' & n' & Hin' & Hx). pose proof (live_remove_sub _ _ _ Hin') as Hin0.
    assert (NE : p' <> p).
    { unfold live_remove in Hin'. apply stdpp.base.list_elem_of_In in Hin'. apply stdpp.list_basics.list.list_elem_of_filter in Hin'.
      destruct Hin' as (Hf & _). cbn [fst] in Hf. intros E. rewrite E, Z.eqb_refl in Hf. exact Hf. }
    destruct (in_split _ _ Hin0) as (l1 & l2 & EL).
    assert (Hin2 : In (p, n) (l1 ++ l2)).
    { rewrite EL in Hin. apply in_app_or in Hin. apply in_or_app. destruct Hin as [X|[X|X]]; [left; exact X | injection X as X1 _; exfalso; exact (NE X1) | right; exact X]. }
    destruct (af_live_disj RT AF Σ m p' n' p n l1 l2 HA EL Hin2); lia.
  - destruct H as (f & k & Hinf & Hf). pose proof (af_frames_range RT AF Σ m f k HA Hinf) as (_ & _ & _ & R3). destruct (R3 p n Hin); lia.
  - destruct H as (f & k & Hinf & Hf). pose proof (af_fshadow_apart RT AF Σ m f k HA Hinf) as (SL & _). destruct (SL p n Hin); lia.
Qed.

End MKit.
