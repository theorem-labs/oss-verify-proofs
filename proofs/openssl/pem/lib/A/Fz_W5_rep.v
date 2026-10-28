(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import ImageA Tac Arr.
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Layout RT_iface D_agree Fz_kit Fz_T_sa Fz_W5_glx Fz_W5_icb Fz_W5_gsi.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Notation zeros n := (repeat (Z_to_bv 8 0) n) (only parsing).

(* [comment removed for export] *)
Definition es_rep (m : mem) (E top bot : Z) (fl mk buf fs ls fn : list word) : Prop :=
  u32arr asegs m E fl /\ length fl = 16%nat
  /\ u32arr asegs m (E + 64) mk /\ length mk = 16%nat
  /\ u64arr asegs m (E + 128) buf /\ length buf = 16%nat
  /\ u8arr asegs m (E + 256) (zeros 128) /\ u8arr asegs m (E + 384) (zeros 128) /\ u8arr asegs m (E + 512) (zeros 64)
  /\ u64arr asegs m (E + 576) fs /\ length fs = 16%nat
  /\ u32arr asegs m (E + 704) ls /\ length ls = 16%nat
  /\ u64arr asegs m (E + 768) fn /\ length fn = 16%nat
  /\ rw_cells asegs m (E + 896) [C4 (Z_to_bv 64 top); C4 (Z_to_bv 64 bot)] /\ 0 <= top < 16 /\ 0 <= bot < 16.

(* [comment removed for export] *)
Definition slot_word (fs fn : list word) (ik : Z * bool) : option word := nth_error (if snd ik then fn else fs) (Z.to_nat (fst ik)).
Definition slots_ok (fs fn : list word) (ks : list (Z * bool)) (owned : list (Z * Z)) : Prop :=
  NoDup ks /\ length ks = length owned /\ (forall ik, In ik ks -> 0 <= fst ik < 16)
  /\ (forall j ik pn, nth_error ks j = Some ik -> nth_error owned j = Some pn -> slot_word fs fn ik = Some (Z_to_bv 64 (fst pn)) /\ 0 < fst pn /\ 0 < snd pn)
  /\ (forall ik w, 0 <= fst ik < 16 -> slot_word fs fn ik = Some w -> ~ In ik ks -> w = Z_to_bv 64 0).

(* [comment removed for export] *)
Definition es_at_rest (m : mem) (E : Z) : Prop :=
  exists fl mk buf ls, es_rep m E 0 0 fl mk buf (repeat (Z_to_bv 64 0) 16) ls (repeat (Z_to_bv 64 0) 16).

(* [comment removed for export] *)
Definition err_env (m : mem) (od e : word) (k MK SA NODES E LV : Z) (pad top ne : word) : Prop :=
  icstat m od /\ rw_cells asegs m ERRNO_A [C4 e] /\ errchain m k MK SA NODES E LV pad top ne.
Definition err_blocks (live : list (Z * Z)) (MK SA NODES E : Z) : Prop :=
  In (MK, 72) live /\ In (SA, 32) live /\ In (NODES, 128) live /\ In (E, 904) live /\ MK mod 8 = 0 /\ SA mod 8 = 0 /\ NODES mod 8 = 0 /\ E mod 8 = 0.

(* [comment removed for export] *)
Lemma u8arr_agree : forall (m m' : mem) A bs, u8arr asegs m A bs -> agree_on (fun x => A <= x < A + Z.of_nat (length bs)) m m' -> wmono asegs m m' -> u8arr asegs m' A bs.
Proof. intros m m' A bs [B W] AG WM. split; [eapply bytes_at_agree; [exact B | exact AG] | eapply wr_at_wm; [exact W | exact WM]]. Qed.
Lemma u32arr_agree : forall (m m' : mem) A ws, u32arr asegs m A ws -> agree_on (fun x => A <= x < A + 4 * Z.of_nat (length ws)) m m' -> wmono asegs m m' -> u32arr asegs m' A ws.
Proof.
  intros m m' A ws [B W] AG WM. split; [| eapply wr_at_wm; [exact W | exact WM]].
  eapply bytes_at_agree; [exact B |]. intros x Hx. apply AG. cbv beta in *. rewrite u32s_length in Hx. lia.
Qed.
Lemma u64arr_agree : forall (m m' : mem) A ws, u64arr asegs m A ws -> agree_on (fun x => A <= x < A + 8 * Z.of_nat (length ws)) m m' -> wmono asegs m m' -> u64arr asegs m' A ws.
Proof.
  intros m m' A ws [B W] AG WM. split; [| eapply wr_at_wm; [exact W | exact WM]].
  eapply bytes_at_agree; [exact B |]. intros x Hx. apply AG. cbv beta in *. rewrite u64s_length in Hx. lia.
Qed.

Lemma es_rep_agree : forall (m m' : mem) E top bot fl mk buf fs ls fn, es_rep m E top bot fl mk buf fs ls fn ->
  agree_on (fun x => E <= x < E + 904) m m' -> wmono asegs m m' -> es_rep m' E top bot fl mk buf fs ls fn.
Proof.
  intros m m' E top bot fl mk buf fs ls fn R AG WM.
  destruct R as (A1 & L1 & A2 & L2 & A3 & L3 & A4 & A5 & A6 & A7 & L7 & A8 & L8 & A9 & L9 & TB & HT & HB).
  assert (AGs : forall (P : Z -> Prop), (forall x, P x -> E <= x < E + 904) -> agree_on P m m') by (intros P HP x Hx; apply AG; apply HP; exact Hx).
  unfold es_rep.
  split; [apply (u32arr_agree m m' _ _ A1); [apply AGs; intros x Hx; cbv beta in Hx; rewrite L1 in Hx; lia | exact WM]|]. split; [exact L1|].
  split; [apply (u32arr_agree m m' _ _ A2); [apply AGs; intros x Hx; cbv beta in Hx; rewrite L2 in Hx; lia | exact WM]|]. split; [exact L2|].
  split; [apply (u64arr_agree m m' _ _ A3); [apply AGs; intros x Hx; cbv beta in Hx; rewrite L3 in Hx; lia | exact WM]|]. split; [exact L3|].
  split; [apply (u8arr_agree m m' _ _ A4); [apply AGs; intros x Hx; cbv beta in Hx; rewrite repeat_length in Hx; lia | exact WM]|].
  split; [apply (u8arr_agree m m' _ _ A5); [apply AGs; intros x Hx; cbv beta in Hx; rewrite repeat_length in Hx; lia | exact WM]|].
  split; [apply (u8arr_agree m m' _ _ A6); [apply AGs; intros x Hx; cbv beta in Hx; rewrite repeat_length in Hx; lia | exact WM]|].
  split; [apply (u64arr_agree m m' _ _ A7); [apply AGs; intros x Hx; cbv beta in Hx; rewrite L7 in Hx; lia | exact WM]|]. split; [exact L7|].
  split; [apply (u32arr_agree m m' _ _ A8); [apply AGs; intros x Hx; cbv beta in Hx; rewrite L8 in Hx; lia | exact WM]|]. split; [exact L8|].
  split; [apply (u64arr_agree m m' _ _ A9); [apply AGs; intros x Hx; cbv beta in Hx; rewrite L9 in Hx; lia | exact WM]|]. split; [exact L9|].
  split; [eapply rw_cells_agree; [exact TB | apply AGs; intros x Hx; cbv beta in Hx; cbn [cells_size csize Nat.add] in Hx; lia | exact WM]|]. lia.
Qed.

Lemma err_env_agree : forall (m m' : mem) od e k MK SA NODES E LV pad top ne, err_env m od e k MK SA NODES E LV pad top ne ->
  (forall a n, (0xb9f200 <= a /\ a + n <= 0xb9f848) \/ (0xbc52a0 <= a /\ a + n <= 0xbc5698) \/ (ERRNO_A <= a /\ a + n <= ERRNO_A + 4)
               \/ (MK <= a /\ a + n <= MK + 72) \/ (SA <= a /\ a + n <= SA + 32) \/ (NODES <= a /\ a + n <= NODES + 128) -> agree_on (fun x => a <= x < a + n) m m') ->
  wmono asegs m m' -> err_env m' od e k MK SA NODES E LV pad top ne.
Proof.
  intros m m' od e k MK SA NODES E LV pad top ne (IC & ER & CH) AG WM. split; [| split].
  - apply (icstat_agree m m' od IC); [| exact WM]. intros a n H1 H2. apply AG. lia.
  - eapply rw_cells_agree; [exact ER | apply AG; cbn [cells_size csize Nat.add]; lia | exact WM].
  - apply (errchain_agree m m' _ _ _ _ _ _ _ _ _ CH); [| exact WM]. intros a n H. apply AG. unfold TSD_MAIN_A in H. destruct CH as (_ & _ & HK & _). lia.
Qed.

(* [comment removed for export] *)
Lemma live_in_disj : forall RT (AF : art_facts RT) (Σ : rts RT) (m : mem) p1 n1 p2 n2,
  ART RT Σ m -> In (p1, n1) (rt_live RT Σ) -> In (p2, n2) (rt_live RT Σ) -> (p1, n1) <> (p2, n2) -> p1 + n1 <= p2 \/ p2 + n2 <= p1.
Proof.
  intros RT AF Σ m p1 n1 p2 n2 HA H1 H2 NE.
  destruct (in_split _ _ H1) as (l1 & l2 & EL).
  assert (H2' : In (p2, n2) (l1 ++ l2)).
  { rewrite EL in H2. apply in_app_or in H2. apply in_or_app. destruct H2 as [X|[X|X]]; [left; exact X | exfalso; exact (NE X) | right; exact X]. }
  exact (af_live_disj RT AF Σ m p1 n1 p2 n2 l1 l2 HA EL H2').
Qed.
