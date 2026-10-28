(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.Lib Require Import PropExec MState Mem Frame Cells Step Arr ImageA.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.B Require Import RT_iface.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Definition agree_on (P : Z -> Prop) (m m' : mem) : Prop := forall a : word, P (bv_unsigned a) -> m' a = m a.

Lemma agree_refl : forall P m, agree_on P m m.
Proof. intros P m a _. reflexivity. Qed.

Lemma agree_sub : forall (P Q : Z -> Prop) m m', agree_on P m m' -> (forall x, Q x -> P x) -> agree_on Q m m'.
Proof. intros P Q m m' H HQ a Ha. exact (H a (HQ _ Ha)). Qed.

Lemma agree_trans : forall P m1 m2 m3, agree_on P m1 m2 -> agree_on P m2 m3 -> agree_on P m1 m3.
Proof. intros P m1 m2 m3 H1 H2 a Ha. rewrite (H2 a Ha). exact (H1 a Ha). Qed.

Lemma agree_of_munch : forall W m m' (P : Z -> Prop), munch W m m' -> (forall x, P x -> outside W x) -> agree_on P m m'.
Proof. intros W m m' P H HP a Ha. exact (H a (HP _ Ha)). Qed.

Lemma agree_of_pres : forall live frames sp m m' (P : Z -> Prop),
  rt_pres live frames sp m m' -> (forall x, P x -> aclient live frames sp x) -> agree_on P m m'.
Proof. intros live frames sp m m' P H HP a Ha. exact (H a (HP _ Ha)). Qed.

Lemma agree_of_pres_fp : forall live frames sp W m m' (P : Z -> Prop),
  rt_pres_fp live frames sp W m m' -> (forall x, P x -> aclient live frames sp x /\ outside W x) -> agree_on P m m'.
Proof. intros live frames sp W m m' P H HP a Ha. destruct (HP _ Ha) as [H1 H2]. exact (H a H1 H2). Qed.

Lemma agree_of_pres_ex : forall live frames sp d n m m' (P : Z -> Prop),
  rt_pres_ex live frames sp d n m m' -> (forall x, P x -> aclient live frames sp x /\ ~ (d <= x < d + n)) -> agree_on P m m'.
Proof. intros live frames sp d n m m' P H HP a Ha. destruct (HP _ Ha) as [H1 H2]. exact (H a H1 H2). Qed.

Section Transport.
Variable segs : list Segment.

Lemma wa_unsigned_range : forall a x, 0 <= a -> a + x < 2^64 -> 0 <= x -> bv_unsigned (wa (a + x)) = a + x.
Proof. intros a x H1 H2 H3. unfold wa. apply unsigned_lit. lia. Qed.

Lemma bytes_at_agree : forall m m' a bs, bytes_at segs m a bs ->
  agree_on (fun x => a <= x < a + Z.of_nat (length bs)) m m' -> bytes_at segs m' a bs.
Proof.
  intros m m' a bs (H0 & H1 & H) HA. split; [exact H0|]. split; [exact H1|].
  intros i Hi. rewrite <- (H i Hi). unfold mrd. rewrite (HA (wa (a + Z.of_nat i))); [reflexivity|].
  unfold wa. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2^64).
  destruct (Z.eq_dec (a + Z.of_nat i) (2^64)) as [E|E]; [lia|].
  rewrite Z.mod_small by lia. lia.
Qed.

Lemma cells_at_agree : forall m m' a cs, cells_at segs m a cs ->
  agree_on (fun x => a <= x < a + Z.of_nat (cells_size cs)) m m' -> cells_at segs m' a cs.
Proof.
  intros m m' a cs [Hwf Hb] HA. split; [exact Hwf|]. apply (bytes_at_agree m m' a _ Hb).
  rewrite cells_bytes_length by exact Hwf. exact HA.
Qed.

Lemma ro_cells_agree : forall m m' a cs, ro_cells segs m a cs ->
  agree_on (fun x => a <= x < a + Z.of_nat (cells_size cs)) m m' -> ro_cells segs m' a cs.
Proof. intros m m' a cs H HA. exact (cells_at_agree m m' a cs H HA). Qed.

Lemma rw_cells_agree : forall m m' a cs, rw_cells segs m a cs ->
  agree_on (fun x => a <= x < a + Z.of_nat (cells_size cs)) m m' -> wmono segs m m' -> rw_cells segs m' a cs.
Proof.
  intros m m' a cs [Hc Hw] HA WM. split; [exact (cells_at_agree m m' a cs Hc HA)|].
  exact (wr_at_transport segs m m' a _ Hw WM).
Qed.

Lemma u64arr_agree : forall m m' a ws, u64arr segs m a ws ->
  agree_on (fun x => a <= x < a + 8 * Z.of_nat (length ws)) m m' -> wmono segs m m' -> u64arr segs m' a ws.
Proof.
  intros m m' a ws [Hb Hw] HA WM. split; [| exact (wr_at_transport segs m m' a _ Hw WM)].
  apply (bytes_at_agree m m' a _ Hb). rewrite u64s_length. eapply agree_sub; [exact HA|]. intros x Hx. cbv beta in *. lia.
Qed.

Lemma stk_agree : forall m m' lo hi, stk segs m lo hi -> agree_on (fun x => lo <= x < hi) m m' -> wmono segs m m' ->
  stk segs m' lo hi.
Proof.
  intros m m' lo hi (H0 & H1 & H) HA WM. split; [exact H0|]. split; [exact H1|].
  intros a Ha. destruct (H a Ha) as [Hw (b & Hr)]. split; [exact (WM _ Hw)|].
  exists b. unfold mrd in *. rewrite (HA (wa a)); [exact Hr|].
  unfold wa. rewrite unsigned_lit by lia. exact Ha.
Qed.

Lemma wview_agree : forall m m' (a : word), m' a = m a -> wview segs m' a = wview segs m a.
Proof. intros m m' a H. unfold wview. rewrite H. reflexivity. Qed.

Lemma wr_at_agree_nw : forall m m' a n, wr_at segs m a n -> agree_on (fun x => a <= x < a + n) m m' -> wr_at segs m' a n.
Proof.
  intros m m' a n (H0 & H1 & H) HA. split; [exact H0|]. split; [exact H1|].
  intros i Hi. rewrite (wview_agree m m'); [exact (H i Hi)|]. apply HA.
  unfold wa. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2^64).
  destruct (Z.eq_dec (a + i) (2^64)) as [E|E]; [lia|]. rewrite Z.mod_small by lia. lia.
Qed.

Lemma rw_cells_agree_nw : forall m m' a cs, rw_cells segs m a cs ->
  agree_on (fun x => a <= x < a + Z.of_nat (cells_size cs)) m m' -> rw_cells segs m' a cs.
Proof.
  intros m m' a cs [Hc Hw] HA. split; [exact (cells_at_agree m m' a cs Hc HA)|]. exact (wr_at_agree_nw m m' a _ Hw HA).
Qed.

Lemma u64arr_agree_nw : forall m m' a ws, u64arr segs m a ws ->
  agree_on (fun x => a <= x < a + 8 * Z.of_nat (length ws)) m m' -> u64arr segs m' a ws.
Proof.
  intros m m' a ws [Hb Hw] HA. split.
  - apply (bytes_at_agree m m' a _ Hb). rewrite u64s_length. eapply agree_sub; [exact HA|]. intros x Hx. cbv beta in *. lia.
  - apply (wr_at_agree_nw m m' a _ Hw). eapply agree_sub; [exact HA|]. intros x Hx. cbv beta in *. lia.
Qed.

Lemma stk_agree_nw : forall m m' lo hi, stk segs m lo hi -> agree_on (fun x => lo <= x < hi) m m' -> stk segs m' lo hi.
Proof.
  intros m m' lo hi (H0 & H1 & H) HA. split; [exact H0|]. split; [exact H1|].
  intros a Ha. assert (E : m' (wa a) = m (wa a)) by (apply HA; unfold wa; rewrite unsigned_lit by lia; exact Ha).
  destruct (H a Ha) as [Hw (b & Hr)]. split; [rewrite (wview_agree m m' _ E); exact Hw|].
  exists b. unfold mrd in *. rewrite E. exact Hr.
Qed.

End Transport.
