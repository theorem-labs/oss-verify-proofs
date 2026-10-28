(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import Tac ImageA Arr Walk Image SysStep.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import StoreFast.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Malloc Require Import MallocKit_AB.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Start Require Import AsanRehashModel.
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Shadow R_arrkit.
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Layout RT_ibase R_small R_cache_defs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Notation mem := (word -> option byte).
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition EW : word := Z_to_bv 64 RHM.EMPTY.

(* [comment removed for export] *)
Definition keys_rep (n : nat) (ws : list word) (ks : list Z) : Prop :=
  length ws = (4 * n)%nat /\ length ks = n /\
  forall d, (d < n)%nat -> nth_error ws (4 * d) = Some (Z_to_bv 64 (nth d ks 0)).

Lemma rhm_upd_length : forall ks i v, length (RHM.upd ks i v) = length ks.
Proof. induction ks as [|k ks IH]; intros [|i] v; cbn; auto. Qed.

Lemma rhm_upd_nth_same : forall ks i v, (i < length ks)%nat -> nth i (RHM.upd ks i v) 0 = v.
Proof.
  induction ks as [|k ks IH]; intros i v Hi; [cbn in Hi; lia|].
  destruct i as [|i]; cbn in *; [reflexivity| apply IH; lia].
Qed.

Lemma rhm_upd_nth_other : forall ks i j v, i <> j -> nth j (RHM.upd ks i v) 0 = nth j ks 0.
Proof.
  induction ks as [|k ks IH]; intros i j v Hij; [destruct i, j; reflexivity|].
  destruct i as [|i], j as [|j]; cbn; try reflexivity; [lia| apply IH; lia].
Qed.

Lemma keys_rep_set_key : forall n ws ks d k, keys_rep n ws ks -> (d < n)%nat ->
  keys_rep n (upd ws (4 * d) (Z_to_bv 64 k)) (RHM.upd ks d k).
Proof.
  intros n ws ks d k (L1 & L2 & H) Hd. split; [rewrite upd_length; exact L1|]. split; [rewrite rhm_upd_length; exact L2|].
  intros e He. destruct (Nat.eq_dec e d) as [->|Ne].
  - rewrite nth_error_upd_same by lia. rewrite rhm_upd_nth_same by lia. reflexivity.
  - rewrite nth_error_upd_other by lia. rewrite rhm_upd_nth_other by lia. apply H. exact He.
Qed.

Lemma keys_rep_set_val : forall n ws ks i v, keys_rep n ws ks -> (i mod 4 <> 0)%nat -> keys_rep n (upd ws i v) ks.
Proof.
  intros n ws ks i v (L1 & L2 & H) Hi. split; [rewrite upd_length; exact L1|]. split; [exact L2|].
  intros e He. rewrite nth_error_upd_other; [apply H; exact He|].
  intros E. apply Hi. rewrite E. rewrite Nat.mul_comm. apply Nat.Div0.mod_mul.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma rw_cells_c8_zero_split : forall (m : mem) A pre post,
  rw_cells asegs m A (pre ++ C8 (Z_to_bv 64 0) :: post) -> rw_cells asegs m A (pre ++ C4 (Z_to_bv 64 0) :: C4 (Z_to_bv 64 0) :: post).
Proof.
  intros m A pre post [[Hwf Hb] Hw]. apply cells_wf_app in Hwf. destruct Hwf as [W1 W2]. cbn in W2. destruct W2 as [_ W2].
  split; [split|].
  - apply cells_wf_app. split; [exact W1|]. cbn. tauto.
  - rewrite cells_bytes_app in *. cbn [cells_bytes cbytes] in *.
    change (le8 (Z_to_bv 64 0)) with (le4 (Z_to_bv 64 0) ++ le4 (Z_to_bv 64 0)) in Hb. rewrite <- app_assoc in Hb. exact Hb.
  - rewrite cells_size_app in *. cbn [cells_size csize] in *. replace (4 + (4 + cells_size post))%nat with (8 + cells_size post)%nat by lia. exact Hw.
Qed.

Lemma le8_inj : forall a b : word, le8 a = le8 b -> a = b.
Proof. intros a b H. rewrite <- (le_bytes_to_word_le8 a), <- (le_bytes_to_word_le8 b), H. reflexivity. Qed.

Lemma xr_rw_cells_app_l : forall (m : mem) a cs1 cs2, rw_cells asegs m a (cs1 ++ cs2) -> rw_cells asegs m a cs1.
Proof.
  intros m a cs1 cs2 [[Hw Hb] W]. rewrite cells_bytes_app in Hb. apply bytes_at_app in Hb as [Hb1 _].
  apply cells_wf_app in Hw as [Hw1 _]. split; [split; [exact Hw1 | exact Hb1]|].
  rewrite cells_size_app, Nat2Z.inj_add in W. destruct W as (W0 & W1 & W2). split; [lia|]. split; [lia|]. intros j Hj. apply W2. lia.
Qed.

Lemma xr_rw_cells_app_r : forall (m : mem) a cs1 cs2, rw_cells asegs m a (cs1 ++ cs2) -> rw_cells asegs m (a + Z.of_nat (cells_size cs1)) cs2.
Proof.
  intros m a cs1 cs2 [[Hw Hb] W]. rewrite cells_bytes_app in Hb. apply bytes_at_app in Hb as [_ Hb2].
  apply cells_wf_app in Hw as [Hw1 Hw2]. rewrite cells_bytes_length in Hb2 by exact Hw1.
  split; [split; [exact Hw2 | exact Hb2]|].
  rewrite cells_size_app, Nat2Z.inj_add in W. destruct W as (W0 & W1 & W2).
  split; [lia|]. split; [lia|]. intros i Hi. replace (a + Z.of_nat (cells_size cs1) + i) with (a + (Z.of_nat (cells_size cs1) + i)) by lia.
  apply W2. lia.
Qed.

(* [comment removed for export] *)
Lemma u64arr_cell : forall (m : mem) A ws i w, u64arr asegs m A ws -> nth_error ws (Z.to_nat i) = Some w -> 0 <= i ->
  rw_cells asegs m (A + 8 * i) [C8 w].
Proof.
  intros m A ws i w [Hb Hw] Hn Hi.
  destruct (u64s_split _ _ _ Hn) as (pre & post & E & Hlen & Eu & Hlu).
  rewrite Eu in Hb. apply bytes_at_app in Hb as [_ Hb]. apply bytes_at_app in Hb as [Hb _]. rewrite Hlu in Hb.
  replace (A + Z.of_nat (8 * Z.to_nat i)) with (A + 8 * i) in Hb by lia.
  assert (HL : (Z.to_nat i < length ws)%nat) by (apply nth_error_Some; rewrite Hn; discriminate).
  split; [split; [exact (conj I I)| cbn [cells_bytes cbytes]; rewrite app_nil_r; exact Hb]|].
  cbn [cells_size csize]. destruct Hw as (W0 & W1 & W2). split; [lia|]. split; [lia|].
  intros k Hk. replace (A + 8 * i + k) with (A + (8 * i + k)) by lia. apply W2. lia.
Qed.

Lemma some_inj : forall {X} (a b : X), Some a = Some b -> a = b.
Proof. intros X a b H. injection H. auto. Qed.

(* [comment removed for export] *)
Lemma u64arr_key_word : forall (m : mem) A ws i w v, u64arr asegs m A ws -> nth_error ws (Z.to_nat i) = Some w -> 0 <= i ->
  ro_cells asegs m (A + 8 * i) [C8 v] -> w = v.
Proof.
  intros m A ws i w v ARR Hn Hi RC.
  pose proof (u64arr_read asegs m A ws i w (wa (A + 8 * i)) ARR Hn Hi eq_refl) as R1.
  pose proof (cells_at_read asegs m (A + 8 * i) [C8 v] 0 (C8 v) RC eq_refl) as R2.
  cbn [csize cbytes Z.of_nat] in R2. rewrite Z.add_0_r in R2. rewrite R1 in R2. apply le8_inj. exact (some_inj _ _ R2).
Qed.


(* [comment removed for export] *)
Definition keys_empty_upto (i : nat) (ws : list word) : Prop :=
  forall d, (d < i)%nat -> nth_error ws (4 * d) = Some (Z_to_bv 64 (-1)).

Lemma mod4_ne : forall d r, 0 <= d -> 1 <= r <= 3 -> (Z.to_nat (4 * d + r) mod 4 <> 0)%nat.
Proof.
  intros d r Hd Hr. replace (Z.to_nat (4 * d + r)) with (Z.to_nat r + Z.to_nat d * 4)%nat by lia.
  rewrite Nat.Div0.mod_add. rewrite Nat.mod_small by lia. lia.
Qed.

Lemma pow2_of_land : forall n, 0 < n -> Z.land (n - 1) n = 0 -> n = 2 ^ Z.log2 n.
Proof.
  intros n Hn HL. pose proof (Z.log2_spec n Hn) as [L1 L2]. pose proof (Z.log2_nonneg n) as L0.
  destruct (Z.eq_dec n (2 ^ Z.log2 n)) as [E|NE]; [exact E|exfalso].
  assert (H1 : 2 ^ Z.log2 n <= n - 1 < 2 ^ Z.succ (Z.log2 n)) by lia.
  assert (E1 : Z.log2 (n - 1) = Z.log2 n) by (apply Z.log2_unique; lia).
  pose proof (Z.bit_log2 n Hn) as T1. pose proof (Z.bit_log2 (n - 1) ltac:(lia)) as T2. rewrite E1 in T2.
  assert (T : Z.testbit (Z.land (n - 1) n) (Z.log2 n) = true) by (rewrite Z.land_spec, T1, T2; reflexivity).
  rewrite HL, Z.bits_0 in T. discriminate.
Qed.

Lemma land_mask_lt : forall x n, 0 < n -> Z.land (n - 1) n = 0 -> 0 <= x -> 0 <= Z.land x (n - 1) < n.
Proof.
  intros x n Hn HL Hx.
  assert (EX : exists e, 0 <= e /\ n = 2 ^ e) by (exists (Z.log2 n); split; [apply Z.log2_nonneg | apply pow2_of_land; assumption]).
  destruct EX as (e & He & ->).
  replace (2 ^ e - 1) with (Z.ones e) by (rewrite Z.ones_equiv; lia).
  rewrite Z.land_ones by lia. apply Z.mod_pos_bound. lia.
Qed.

Lemma scale32 : forall x, 0 <= x < 2 ^ 32 -> Z.shiftr (Z.land (Z.shiftl x 32) 18446744073709551615) 27 = 32 * x.
Proof.
  intros x Hx. change 18446744073709551615 with (Z.ones 64). rewrite Z.land_ones by lia. rewrite Z.shiftl_mul_pow2 by lia.
  rewrite Z.mod_small by lia. rewrite Z.shiftr_div_pow2 by lia.
  replace (x * 2 ^ 32) with (32 * x * 2 ^ 27) by lia. apply Z.div_mul. lia.
Qed.

Section RH.
Variables (map Bo No B N RA : Z).
Variables (gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t6 sp : word) (F : bvmap 5 word) (fc : bv 32).
Variable Q : machine_state -> Prop.
Hypothesis HN : 64 <= N <= 2 ^ 20.
Hypothesis HP : Z.land (N - 1) N = 0.
Hypothesis HNo : 1 <= No <= 2 ^ 20.
Hypothesis B0 : 0 < B.
Hypothesis BT : B + 32 * N <= 2 ^ 47.
Hypothesis Bo0 : 0 < Bo.
Hypothesis BoT : Bo + 32 * No <= 2 ^ 47.

(* [comment removed for export] *)
Notation RHW := [(map + 8, map + 16); (B, B + 32 * N); (bv_unsigned sp + -16, bv_unsigned sp)] (only parsing).

Lemma init_loop : forall (n : nat) (i : Z) (ws : list word) (m0 m : mem) (ra t0 t1 t2 a6 a7 t3 t4 t5 : word),
  Z.of_nat n = N - i -> 0 <= i < N -> length ws = (4 * Z.to_nat N)%nat ->
  u64arr asegs m B ws -> keys_empty_upto (Z.to_nat i) ws ->
  mem_inv asegs m -> munch [(B, B + 32 * N)] m0 m -> wmono asegs m0 m ->
  (forall m' ws', length ws' = (4 * Z.to_nat N)%nat -> u64arr asegs m' B ws' -> keys_empty_upto (Z.to_nat N) ws' ->
     mem_inv asegs m' -> munch [(B, B + 32 * N)] m0 m' -> wmono asegs m0 m' ->
     evt asegs Q (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -16)) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 map) (Z_to_bv 64 Bo) (Z_to_bv 64 (Bo + 32 * No))
                          (Z_to_bv 64 (B + 32 * N)) (Z_to_bv 64 0) (Z_to_bv 64 (-1)) a6 a7
                          s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                      F (Z_to_bv 64 0x1aba70) fc None m' (seg_rom asegs))) ->
  evt asegs Q (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -16)) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 map) (Z_to_bv 64 Bo) (Z_to_bv 64 (Bo + 32 * No))
                       (Z_to_bv 64 (B + 32 * i)) (Z_to_bv 64 (32 * (N - i))) (Z_to_bv 64 (-1)) a6 a7
                       s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                   F (Z_to_bv 64 0x1aba60) fc None m (seg_rom asegs)).
Proof.
  induction n as [|n IH]; intros i ws m0 m ra t0 t1 t2 a6 a7 t3 t4 t5 Hn Hi HL ARR KE MI MU WM K; [lia|].
  pose proof (u64arr_bound asegs m B _ ARR) as BND. rewrite HL in BND.
  pose proof (u64arr_store_ok asegs m B _ (4 * i) (wa (B + 8 * (4 * i))) ARR ltac:(rewrite HL; lia) eq_refl) as SOK.
  pose proof (u64arr_write asegs m B _ (4 * i) (Z_to_bv 64 (-1)) ARR ltac:(rewrite HL; lia)) as ARR1.
  replace (B + 8 * (4 * i)) with (B + 32 * i) in SOK, ARR1 by lia.
  zstep. change (Z_to_le_bytes 8 18446744073709551615) with (le8 (Z_to_bv 64 (-1))). clear ARR. store_done.
  zstep. zstep.
  assert (KE1 : keys_empty_upto (Z.to_nat (i + 1)) (upd ws (Z.to_nat (4 * i)) (Z_to_bv 64 (-1)))).
  { intros d Hd. destruct (Nat.eq_dec d (Z.to_nat i)) as [->|Nd].
    - replace (4 * Z.to_nat i)%nat with (Z.to_nat (4 * i)) by lia. apply nth_error_upd_same. rewrite HL. lia.
    - rewrite nth_error_upd_other by lia. apply KE. lia. }
  destruct (Z.eq_dec (i + 1) N) as [E|NE].
  - replace (32 * (N - i) + -32) with 0 by lia. zstep. ifF.
    replace (B + 32 * i + 32) with (B + 32 * N) by lia.
    rewrite E in KE1.
    apply (K _ _ ltac:(rewrite upd_length; exact HL) ARR1 KE1); assumption.
  - assert (EU : bv_unsigned (Z_to_bv 64 (32 * (N - i) + -32)) = 32 * (N - i) + -32) by (apply unsigned_lit; lia).
    zstep. ifT.
    replace (B + 32 * i + 32) with (B + 32 * (i + 1)) by lia. replace (32 * (N - i) + -32) with (32 * (N - (i + 1))) by lia.
    apply (IH (i + 1) (upd ws (Z.to_nat (4 * i)) (Z_to_bv 64 (-1))) m0 m1); try assumption; try lia.
    rewrite upd_length; exact HL.
Qed.

(* [comment removed for export] *)
Lemma probe_loop : forall (fuel : nat) (idx t d k : Z) (ks : list Z) (nws : list word) (m : mem) (ra sp' a1 a2 : word),
  RHM.probe_free N ks idx t fuel = Some d ->
  0 <= idx < N -> 1 <= t < 2 ^ 32 - Z.of_nat fuel ->
  u64arr asegs m B nws -> keys_rep (Z.to_nat N) nws ks ->
  (forall e, 0 <= e < N -> 0 <= nth (Z.to_nat e) ks 0 < 2 ^ 64 /\ nth (Z.to_nat e) ks 0 <> k /\ nth (Z.to_nat e) ks 0 <> RHM.TOMB) ->
  0 <= k < 2 ^ 64 ->
  mem_inv asegs m ->
  (forall t2' t4' t5', 0 <= d < N -> nth (Z.to_nat d) ks 0 = RHM.EMPTY ->
     evt asegs Q (MS (mkR ra sp' gp tp (Z_to_bv 64 (B + 32 * d)) (Z_to_bv 64 (N - 1)) t2' s0 s1 (Z_to_bv 64 map) a1 a2
                          (Z_to_bv 64 (-3)) (Z_to_bv 64 37) (Z_to_bv 64 (-1)) (Z_to_bv 64 k) (Z_to_bv 64 B)
                          s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 0) t4' t5' t6)
                      F (Z_to_bv 64 0x1abb00) fc None m (seg_rom asegs))) ->
  evt asegs Q (MS (mkR ra sp' gp tp (Z_to_bv 64 (B + 32 * idx)) (Z_to_bv 64 (N - 1)) (Z_to_bv 64 idx) s0 s1 (Z_to_bv 64 map) a1 a2
                       (Z_to_bv 64 (-3)) (Z_to_bv 64 37) (Z_to_bv 64 (-1)) (Z_to_bv 64 k) (Z_to_bv 64 B)
                       s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 0) (Z_to_bv 64 t) (Z_to_bv 64 (nth (Z.to_nat idx) ks 0)) t6)
                   F (Z_to_bv 64 0x1abac4) fc None m (seg_rom asegs)).
Proof.
  induction fuel as [|fuel IH]; intros idx t d k ks nws m ra sp' a1 a2 PF Hidx Ht ARR KR KD Hk MI K; [cbn in PF; discriminate|].
  cbn [RHM.probe_free] in PF.
  destruct (KD idx Hidx) as (Kr & Kk & Kt).
  remember (nth (Z.to_nat idx) ks 0) as kk eqn:Ekk.
  assert (EUk : bv_unsigned (Z_to_bv 64 kk) = kk) by (apply unsigned_lit; lia).
  assert (EUm1 : bv_unsigned (Z_to_bv 64 (-1)) = 18446744073709551615) by reflexivity.
  zstep. rewrite bv_eqb_Z, EUk, EUm1.
  destruct (Z.eqb_spec kk RHM.EMPTY) as [EE|NE].
  - injection PF as <-. change RHM.EMPTY with 18446744073709551615 in EE. rewrite (proj2 (Z.eqb_eq _ _) EE).
    apply K; [exact Hidx | rewrite <- Ekk; exact EE].
  - change RHM.EMPTY with 18446744073709551615 in NE. rewrite (proj2 (Z.eqb_neq _ _) NE).
    zstep. zstep.
    assert (XR : 0 <= Z.lxor kk 18446744073709551614 < 2 ^ 64) by (apply zr_lxor; unfold inr64; lia).
    assert (XN : Z.lxor kk 18446744073709551614 <> 0) by (intros E; apply (proj1 (zb_lxor_eq0 _ _)) in E; apply Kt; exact E).
    assert (EUx : bv_unsigned (Z_to_bv 64 (Z.lxor kk 18446744073709551614)) = Z.lxor kk 18446744073709551614) by (apply unsigned_lit; lia).
    zstep. ifF.
    zstep. zstep. zstep. zstep.
    set (idx' := Z.land (idx + t) (N - 1)) in *.
    assert (Hidx' : 0 <= idx' < N) by (apply land_mask_lt; lia).
    assert (EUi : bv_unsigned (Z_to_bv 64 idx') = idx') by (apply unsigned_lit; lia).
    zstep. zstep. zstep.
    rewrite (scale32 idx') by lia.
    assert (Hn : nth_error nws (Z.to_nat (4 * idx')) = Some (Z_to_bv 64 (nth (Z.to_nat idx') ks 0))).
    { destruct KR as (_ & _ & KR). replace (Z.to_nat (4 * idx')) with (4 * Z.to_nat idx')%nat by lia. apply KR. lia. }
    pose proof (u64arr_read asegs m B nws (4 * idx') _ (Z_to_bv 64 (B + 32 * idx')) ARR Hn ltac:(lia) ltac:(unfold wa; f_equal; lia)) as RD.
    zstep. clear RD. zstep.
    destruct (KD idx' Hidx') as (Kr' & Kk' & Kt').
    assert (EUk' : bv_unsigned (Z_to_bv 64 (nth (Z.to_nat idx') ks 0)) = nth (Z.to_nat idx') ks 0) by (apply unsigned_lit; lia).
    assert (EUkey : bv_unsigned (Z_to_bv 64 k) = k) by (apply unsigned_lit; lia).
    zstep. rewrite bv_eqb_Z, EUk', EUkey. rewrite (proj2 (Z.eqb_neq _ _) (not_eq_sym Kk')).
    zstep.
    apply (IH idx' (t + 1) d k ks nws m ra sp' a1 a2 PF Hidx' ltac:(lia) ARR KR KD Hk MI K).
Qed.

(* [comment removed for export] *)
Variables (olds : list Z) (ows : list word).
Hypothesis HLo : Z.of_nat (length olds) = No.
Hypothesis HRo : Forall (fun k => 0 <= k < 2 ^ 64) olds.
Hypothesis KRo : keys_rep (Z.to_nat No) ows olds.
Hypothesis BoI : Bo + 32 * No <= 0x10000 \/ 0xbc6000 <= Bo.
Hypothesis BI : B + 32 * N <= 0x10000 \/ 0xbc6000 <= B.
Hypothesis SPlo : 0xbc6000 <= bv_unsigned sp + -16.
Hypothesis SPhi : bv_unsigned sp < 2 ^ 47.
Hypothesis APART : Bo + 32 * No <= B \/ B + 32 * N <= Bo.
Hypothesis SPo : bv_unsigned sp <= Bo \/ Bo + 32 * No <= bv_unsigned sp + -16.
Hypothesis SPn : bv_unsigned sp <= B \/ B + 32 * N <= bv_unsigned sp + -16.
Hypothesis MAP0 : 0x10000 <= map.
Hypothesis MAP1 : map + 20 <= 0xbc6000.

(* [comment removed for export] *)
Definition ks_ok (ks done : list Z) : Prop := Forall (fun x => x = RHM.EMPTY \/ In x done) ks.

Lemma outer_loop : forall (r : list Z) (j : Z) (ks done : list Z) (pl : list (Z * Z)) (ks' : list Z) (plf : list (Z * Z))
    (nws : list word) (junk : list byte) (m0 m : mem) (ra t0 t1 t2 a6 a7 t3 t4 t5 : word),
  RHM.rehash N ks r j pl = Some (ks', plf) ->
  r = skipn (Z.to_nat j) olds -> 0 <= j < No ->
  keys_rep (Z.to_nat N) nws ks -> ks_ok ks done -> List.NoDup (done ++ List.filter RHM.is_live r) ->
  Forall (fun x => 0 <= x < 2 ^ 64 /\ RHM.is_live x = true) done ->
  Z.of_nat (length pl) <= j ->
  rw_cells asegs m map [C8 (Z_to_bv 64 B); C4 (Z_to_bv 64 (Z.of_nat (length pl))); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 N)] ->
  u64arr asegs m Bo ows -> u64arr asegs m B nws ->
  rw_cells asegs m (bv_unsigned sp + -16) [CB 8 junk; C8 (Z_to_bv 64 RA)] ->
  mem_inv asegs m -> munch RHW m0 m -> wmono asegs m0 m ->
  (forall (m' : mem) (nws' : list word) (a3' a4' a5' a6' a7' t0' t1' t2' t3' t4' t5' : word),
     keys_rep (Z.to_nat N) nws' ks' ->
     rw_cells asegs m' map [C8 (Z_to_bv 64 B); C4 (Z_to_bv 64 (Z.of_nat (length plf))); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 N)] ->
     u64arr asegs m' Bo ows -> u64arr asegs m' B nws' ->
     rw_cells asegs m' (bv_unsigned sp + -16) [CB 8 junk; C8 (Z_to_bv 64 RA)] ->
     mem_inv asegs m' -> munch RHW m0 m' -> wmono asegs m0 m' ->
     evt asegs Q (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -16)) gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 map) (Z_to_bv 64 (Bo + 32 * No)) (Z_to_bv 64 (Bo + 32 * No))
                          a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6)
                      F (Z_to_bv 64 0x1abb38) fc None m' (seg_rom asegs))) ->
  evt asegs Q (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -16)) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 map) (Z_to_bv 64 (Bo + 32 * j)) (Z_to_bv 64 (Bo + 32 * No))
                       (Z_to_bv 64 (-3)) (Z_to_bv 64 37) (Z_to_bv 64 (-1)) a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                   F (Z_to_bv 64 0x1aba80) fc None m (seg_rom asegs)).
Proof.
  induction r as [|k r IH]; intros j ks done pl ks' plf nws junk m0 m ra t0 t1 t2 a6 a7 t3 t4 t5
    RH Er Hj KR KO ND FD HPL MAPC OA NA FR MI MU WM K.
  { exfalso. assert (L : length (skipn (Z.to_nat j) olds) = 0%nat) by (rewrite <- Er; reflexivity). rewrite length_skipn in L. lia. }
  assert (Ek : nth (Z.to_nat j) olds 0 = k).
  { rewrite <- (firstn_skipn (Z.to_nat j) olds) at 1. rewrite <- Er. rewrite app_nth2 by (rewrite length_firstn; lia).
    rewrite length_firstn. replace (Z.to_nat j - Nat.min (Z.to_nat j) (length olds))%nat with 0%nat by lia. reflexivity. }
  assert (Hk : 0 <= k < 2 ^ 64).
  { rewrite <- Ek. apply (proj1 (Forall_forall _ _) HRo). apply nth_In. lia. }
  assert (Er' : r = skipn (Z.to_nat (j + 1)) olds).
  { replace (Z.to_nat (j + 1)) with (1 + Z.to_nat j)%nat by lia. rewrite <- skipn_skipn, <- Er. reflexivity. }
  cbn [RHM.rehash] in RH.
  (* [comment removed for export] *)
  assert (Hko : nth_error ows (Z.to_nat (4 * j)) = Some (Z_to_bv 64 k)).
  { destruct KRo as (_ & _ & KRo'). replace (Z.to_nat (4 * j)) with (4 * Z.to_nat j)%nat by lia. rewrite <- Ek. apply KRo'. lia. }
  pose proof (u64arr_read asegs m Bo ows (4 * j) _ (Z_to_bv 64 (Bo + 32 * j)) OA Hko ltac:(lia) ltac:(unfold wa; f_equal; lia)) as RD.
  assert (EUkey : bv_unsigned (Z_to_bv 64 k) = k) by (apply unsigned_lit; lia).
  zstep. clear RD. zstep.
  rewrite bv_ltu_Z, EUkey. change (bv_unsigned (Z_to_bv 64 (-3))) with 18446744073709551613.
  unfold RHM.is_live in RH. change (2 ^ 64 - 3) with 18446744073709551613 in RH.
  destruct (Z.leb_spec k 18446744073709551613) as [LIVE|DEAD].
  2:{ (* [comment removed for export] *)
    rewrite (proj2 (Z.ltb_lt _ _) DEAD). cbn [negb].
    assert (LVk : RHM.is_live k = false) by (unfold RHM.is_live; apply Z.leb_gt; lia).
    cbn [List.filter] in ND. rewrite LVk in ND.
    zstep.
    destruct (Z.eq_dec (j + 1) No) as [EJ|NJ].
    - replace (Bo + 32 * j + 32) with (Bo + 32 * No) by lia.
      zstep. ifF. zstep.
      assert (Er0 : r = []) by (rewrite Er', EJ; apply skipn_all2; lia).
      rewrite Er0 in RH. cbn [RHM.rehash] in RH. injection RH as <- <-.
      eapply K; try eassumption. rewrite length_rev. exact MAPC.
    - replace (Bo + 32 * j + 32) with (Bo + 32 * (j + 1)) by lia.
      assert (EUa : bv_unsigned (Z_to_bv 64 (Bo + 32 * (j + 1))) = Bo + 32 * (j + 1)) by (apply unsigned_lit; lia).
      assert (EUb : bv_unsigned (Z_to_bv 64 (Bo + 32 * No)) = Bo + 32 * No) by (apply unsigned_lit; lia).
      zstep. ifT.
      eapply (IH (j + 1) ks done pl ks' plf); try eassumption; lia. }
  rewrite (proj2 (Z.ltb_ge _ _) LIVE). cbn [negb].
  zstep.
  rewrite (sx32_small_A N) by lia.
  zstep. zstep. zstep. zstep.
  replace (Z.land (N + -1) (Z.land (k * 37) 18446744073709551615)) with (RHM.hash0 N k)
    by (unfold RHM.hash0; change 18446744073709551615 with (Z.ones 64); rewrite Z.land_ones by lia; rewrite Z.land_comm; f_equal; lia).
  set (h := RHM.hash0 N k) in *.
  assert (Hh : 0 <= h < N) by (unfold h, RHM.hash0; apply land_mask_lt; [lia | exact HP | apply Z.mod_pos_bound; lia]).
  assert (EUh : bv_unsigned (Z_to_bv 64 h) = h) by (apply unsigned_lit; lia).
  zstep. zstep. zstep. rewrite (scale32 h) by lia.
  assert (Hn0 : nth_error nws (Z.to_nat (4 * h)) = Some (Z_to_bv 64 (nth (Z.to_nat h) ks 0))).
  { destruct KR as (_ & _ & KR'). replace (Z.to_nat (4 * h)) with (4 * Z.to_nat h)%nat by lia. apply KR'. lia. }
  pose proof (u64arr_read asegs m B nws (4 * h) _ (Z_to_bv 64 (B + 32 * h)) NA Hn0 ltac:(lia) ltac:(unfold wa; f_equal; lia)) as RD.
  zstep. clear RD.
  assert (LVk : RHM.is_live k = true) by (unfold RHM.is_live; apply Z.leb_le; lia).
  cbn [List.filter] in ND. rewrite LVk in ND.
  assert (KD : forall e, 0 <= e < N -> 0 <= nth (Z.to_nat e) ks 0 < 2 ^ 64 /\ nth (Z.to_nat e) ks 0 <> k /\ nth (Z.to_nat e) ks 0 <> RHM.TOMB).
  { intros e He. destruct KR as (_ & Lk & _).
    destruct (proj1 (Forall_forall _ _) KO (nth (Z.to_nat e) ks 0) ltac:(apply nth_In; lia)) as [EE|IN].
    - rewrite EE. unfold RHM.EMPTY, RHM.TOMB. lia.
    - pose proof (proj1 (Forall_forall _ _) FD _ IN) as (R1 & L1). unfold RHM.is_live in L1. apply Z.leb_le in L1.
      split; [lia|]. split; [| unfold RHM.TOMB; lia].
      intros E. rewrite E in IN. apply NoDup_remove_2 in ND. apply ND. apply in_or_app. left. exact IN. }
  destruct (KD h Hh) as (Kr0 & Kk0 & Kt0).
  assert (EUk0 : bv_unsigned (Z_to_bv 64 (nth (Z.to_nat h) ks 0)) = nth (Z.to_nat h) ks 0) by (apply unsigned_lit; lia).
  zstep. rewrite bv_eqb_Z, EUk0, EUkey. rewrite (proj2 (Z.eqb_neq _ _) (not_eq_sym Kk0)).
  zstep. zstep.
  destruct (RHM.probe_free N ks h 1 (Z.to_nat N)) as [d|] eqn:PF; [|discriminate].
  apply (probe_loop (Z.to_nat N) h 1 d k ks nws m _ _ _ _ PF Hh ltac:(lia) NA KR KD Hk MI).
  intros t2' t4' t5' Hd EEd.
  zstep.
  ifT.
  assert (HLn : length nws = (4 * Z.to_nat N)%nat) by (destruct KR as (L & _); exact L).
  assert (HLw : length ows = (4 * Z.to_nat No)%nat) by (destruct KRo as (L & _); exact L).
  destruct (nth_error ows (Z.to_nat (4 * j + 1))) as [v1|] eqn:Hv1; [| apply nth_error_None in Hv1; lia].
  destruct (nth_error ows (Z.to_nat (4 * j + 2))) as [v2|] eqn:Hv2; [| apply nth_error_None in Hv2; lia].
  destruct (nth_error ows (Z.to_nat (4 * j + 3))) as [v3|] eqn:Hv3; [| apply nth_error_None in Hv3; lia].
  pose proof (u64arr_bound asegs m B _ NA) as BND. rewrite HLn in BND.
  (* [comment removed for export] *)
  pose proof (u64arr_store_ok asegs m B _ (4 * d) (wa (B + 8 * (4 * d))) NA ltac:(rewrite HLn; lia) eq_refl) as SOK.
  pose proof (u64arr_write asegs m B _ (4 * d) (Z_to_bv 64 k) NA ltac:(rewrite HLn; lia)) as NA1.
  replace (B + 8 * (4 * d)) with (B + 32 * d) in SOK, NA1 by lia.
  zstep.
  clear NA. store_done.
  (* [comment removed for export] *)
  pose proof (u64arr_read asegs m1 Bo ows (4 * j + 1) _ (Z_to_bv 64 (Bo + 32 * j + 8)) OA Hv1 ltac:(lia) ltac:(unfold wa; f_equal; lia)) as RD.
  zstep. clear RD.
  pose proof (u64arr_store_ok asegs m1 B _ (4 * d + 1) (wa (B + 8 * (4 * d + 1))) NA1 ltac:(rewrite upd_length, HLn; lia) eq_refl) as SOK.
  pose proof (u64arr_write asegs m1 B _ (4 * d + 1) v1 NA1 ltac:(rewrite upd_length, HLn; lia)) as NA2.
  replace (B + 8 * (4 * d + 1)) with (B + 32 * d + 8) in SOK, NA2 by lia.
  zstep. clear NA1. store_done.
  (* [comment removed for export] *)
  lazymatch goal with OAx : u64arr asegs ?mm Bo ows |- _ =>
    pose proof (u64arr_read asegs mm Bo ows (4 * j + 2) _ (Z_to_bv 64 (Bo + 32 * j + 16)) OAx Hv2 ltac:(lia) ltac:(unfold wa; f_equal; lia)) as RD end.
  zstep. clear RD.
  lazymatch goal with NAx : u64arr asegs ?mm B ?xs |- _ =>
    pose proof (u64arr_store_ok asegs mm B _ (4 * d + 2) (wa (B + 8 * (4 * d + 2))) NAx ltac:(rewrite !upd_length, HLn; lia) eq_refl) as SOK;
    pose proof (u64arr_write asegs mm B _ (4 * d + 2) v2 NAx ltac:(rewrite !upd_length, HLn; lia)) as NA3 end.
  replace (B + 8 * (4 * d + 2)) with (B + 32 * d + 16) in SOK, NA3 by lia.
  zstep. clear NA2. store_done.
  (* [comment removed for export] *)
  lazymatch goal with OAx : u64arr asegs ?mm Bo ows |- _ =>
    pose proof (u64arr_read asegs mm Bo ows (4 * j + 3) _ (Z_to_bv 64 (Bo + 32 * j + 24)) OAx Hv3 ltac:(lia) ltac:(unfold wa; f_equal; lia)) as RD end.
  zstep. clear RD.
  lazymatch goal with NAx : u64arr asegs ?mm B ?xs |- _ =>
    pose proof (u64arr_store_ok asegs mm B _ (4 * d + 3) (wa (B + 8 * (4 * d + 3))) NAx ltac:(rewrite !upd_length, HLn; lia) eq_refl) as SOK;
    pose proof (u64arr_write asegs mm B _ (4 * d + 3) v3 NAx ltac:(rewrite !upd_length, HLn; lia)) as NA4 end.
  replace (B + 8 * (4 * d + 3)) with (B + 32 * d + 24) in SOK, NA4 by lia.
  zstep. clear NA3. store_done.
  (* [comment removed for export] *)
  zstep.
  rewrite (sx32_small_A (Z.of_nat (length pl))) by lia.
  zstep. zstep.
  assert (KR4 : keys_rep (Z.to_nat N) (upd (upd (upd (upd nws (Z.to_nat (4 * d)) (Z_to_bv 64 k)) (Z.to_nat (4 * d + 1)) v1)
                                        (Z.to_nat (4 * d + 2)) v2) (Z.to_nat (4 * d + 3)) v3) (RHM.upd ks (Z.to_nat d) k)).
  { do 3 (apply keys_rep_set_val; [| apply mod4_ne; lia]).
    replace (Z.to_nat (4 * d)) with (4 * Z.to_nat d)%nat by lia. apply keys_rep_set_key; [exact KR | lia]. }
  assert (KO' : ks_ok (RHM.upd ks (Z.to_nat d) k) (done ++ [k])).
  { unfold ks_ok in *. apply Forall_forall. intros x Hx. destruct KR as (_ & Lk & _).
    destruct (In_nth _ _ 0 Hx) as (e & He & Ee). rewrite rhm_upd_length in He.
    destruct (Nat.eq_dec e (Z.to_nat d)) as [->|Ne].
    - rewrite rhm_upd_nth_same in Ee by lia. right. apply in_or_app. right. left. exact Ee.
    - rewrite rhm_upd_nth_other in Ee by lia.
      destruct (proj1 (Forall_forall _ _) KO x ltac:(rewrite <- Ee; apply nth_In; lia)) as [EE|IN]; [left; exact EE| right; apply in_or_app; left; exact IN]. }
  assert (ND' : List.NoDup ((done ++ [k]) ++ List.filter RHM.is_live r)) by (rewrite <- app_assoc; exact ND).
  assert (FD' : Forall (fun x => 0 <= x < 2 ^ 64 /\ RHM.is_live x = true) (done ++ [k])).
  { apply Forall_app. split; [exact FD|]. constructor; [split; [exact Hk | exact LVk] | constructor]. }
  zstep.
  destruct (Z.eq_dec (j + 1) No) as [EJ|NJ].
  - (* [comment removed for export] *)
    replace (Bo + 32 * j + 32) with (Bo + 32 * No) by lia.
    zstep. ifF.
    assert (Er0 : r = []) by (rewrite Er', EJ; apply skipn_all2; lia).
    rewrite Er0 in RH. cbn [RHM.rehash] in RH. injection RH as <- <-.
    eapply K; try eassumption.
    rewrite length_app, length_rev. cbn [length]. replace (Z.of_nat (length pl + 1)) with (Z.of_nat (length pl) + 1) by lia. eassumption.
  - replace (Bo + 32 * j + 32) with (Bo + 32 * (j + 1)) by lia.
    assert (EUa : bv_unsigned (Z_to_bv 64 (Bo + 32 * (j + 1))) = Bo + 32 * (j + 1)) by (apply unsigned_lit; lia).
    assert (EUb : bv_unsigned (Z_to_bv 64 (Bo + 32 * No)) = Bo + 32 * No) by (apply unsigned_lit; lia).
    zstep. ifT.
    eapply (IH (j + 1) (RHM.upd ks (Z.to_nat d) k) (done ++ [k]) ((j, d) :: pl) ks' plf); try eassumption; try lia.
    + cbn [length]. lia.
    + cbn [length]. rewrite Nat2Z.inj_succ. replace (Z.succ (Z.of_nat (length pl))) with (Z.of_nat (length pl) + 1) by lia. eassumption.
Qed.

End RH.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Theorem xr_rehash_spec : forall (map Bo No B N : Z) (olds ks' : list Z) (pl : list (Z * Z)) (ne0 tb0 : word) (RA : Z)
    (gp tp t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (sp : word) F fc (m : mem),
  RHM.rehash0 N olds = Some (ks', pl) ->
  Z.of_nat (length olds) = No -> Forall (fun k => 0 <= k < 2 ^ 64) olds -> List.NoDup (List.filter RHM.is_live olds) ->
  64 <= N <= 2 ^ 20 -> Z.land (N - 1) N = 0 ->
  1 <= No <= 2 ^ 20 ->
  rw_cells asegs m map [C8 (Z_to_bv 64 B); C4 ne0; C4 tb0; C4 (Z_to_bv 64 N)] ->
  (forall j, 0 <= j < No -> ro_cells asegs m (Bo + 32 * j) [C8 (Z_to_bv 64 (nth (Z.to_nat j) olds 0))]) ->
  stk asegs m Bo (Bo + 32 * No) ->
  stk asegs m B (B + 32 * N) ->
  stk asegs m (bv_unsigned sp - 16) (bv_unsigned sp) -> bv_unsigned sp mod 16 = 0 ->
  0 < Bo -> Bo + 32 * No <= 2 ^ 47 -> (Bo + 32 * No <= 0x10000 \/ SEGTOP_A <= Bo) -> Bo mod 8 = 0 ->
  0 < B -> B + 32 * N <= 2 ^ 47 -> (B + 32 * N <= 0x10000 \/ SEGTOP_A <= B) -> B mod 8 = 0 ->
  SEGTOP_A <= bv_unsigned sp - 16 -> bv_unsigned sp < 2 ^ 47 ->
  (Bo + 32 * No <= B \/ B + 32 * N <= Bo) ->
  (bv_unsigned sp <= Bo \/ Bo + 32 * No <= bv_unsigned sp - 16) -> (bv_unsigned sp <= B \/ B + 32 * N <= bv_unsigned sp - 16) ->
  0x10000 <= map -> map + 20 <= SEGTOP_A ->
  0 <= RA < 2 ^ 47 -> RA mod 4 = 0 ->
  mem_inv asegs m ->
  evt asegs (fun ms' => exists (a3' a4' a5' a6' a7' t0' t1' t2' t3' t4' t5' : word) (m' : mem),
      ms' = MS (mkR (Z_to_bv 64 RA) sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 map) (Z_to_bv 64 (Bo + 32 * No)) (Z_to_bv 64 (Bo + 32 * No)) a3' a4' a5' a6' a7'
                    s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6)
               F (Z_to_bv 64 RA) fc None m' (seg_rom asegs)
      /\ munch [(map + 8, map + 16); (B, B + 32 * N); (bv_unsigned sp - 16, bv_unsigned sp)] m m'
      /\ wmono asegs m m' /\ mem_inv asegs m'
      /\ rw_cells asegs m' (map + 8) [C4 (Z_to_bv 64 (Z.of_nat (length pl))); C4 (Z_to_bv 64 0)]
      /\ (forall d, 0 <= d < N -> rw_cells asegs m' (B + 32 * d) [C8 (Z_to_bv 64 (nth (Z.to_nat d) ks' 0))]))
    (MS (mkR (Z_to_bv 64 RA) sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 map) (Z_to_bv 64 Bo) (Z_to_bv 64 (Bo + 32 * No)) a3 a4 a5 a6 a7
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x1aba34) fc None m (seg_rom asegs)).
Proof.
  intros until m. intros RH0 HLo HRo ND HN HP HNo MAP KEYS OLD NEW FRS SP16 Bo0 BoT BoI Bo8 B0 BT BI B8 SPlo SPhi APART SPo SPn MAP0 MAP1 HRA HRA4 MI.
  unfold SEGTOP_A in *.
  (* [comment removed for export] *)
  destruct (stk_carve asegs m B (B + 32 * N) (Z.to_nat (32 * N)) NEW ltac:(lia)) as [_ (junkn & NEWC)].
  replace (B + 32 * N - Z.of_nat (Z.to_nat (32 * N))) with B in NEWC by lia.
  destruct (u64arr_of_CB asegs m B (4 * Z.to_nat N) _ _ NEWC ltac:(lia)) as (nws0 & HLn0 & NA0).
  destruct (stk_carve asegs m Bo (Bo + 32 * No) (Z.to_nat (32 * No)) OLD ltac:(lia)) as [_ (junko & OLDC)].
  replace (Bo + 32 * No - Z.of_nat (Z.to_nat (32 * No))) with Bo in OLDC by lia.
  destruct (u64arr_of_CB asegs m Bo (4 * Z.to_nat No) _ _ OLDC ltac:(lia)) as (ows & HLw & OA0).
  assert (KRo : keys_rep (Z.to_nat No) ows olds).
  { split; [exact HLw|]. split; [lia|]. intros d Hd.
    destruct (nth_error ows (4 * d)) as [w|] eqn:Hw; [| apply nth_error_None in Hw; lia].
    f_equal. replace (4 * d)%nat with (Z.to_nat (4 * Z.of_nat d)) in Hw by lia.
    pose proof (KEYS (Z.of_nat d) ltac:(lia)) as RC. rewrite Nat2Z.id in RC.
    replace (Bo + 32 * Z.of_nat d) with (Bo + 8 * (4 * Z.of_nat d)) in RC by lia.
    exact (u64arr_key_word m Bo ows _ w _ OA0 Hw ltac:(lia) RC). }
  clear KEYS OLD NEW OLDC NEWC.
  pose proof (munch_refl [(map + 8, map + 16); (B, B + 32 * N); (bv_unsigned sp + -16, bv_unsigned sp)] m) as MU.
  pose proof (wmono_refl asegs m) as WM.
  carve_frame 16%nat FRS. zstep. zstep.
  apply (rw_cells_merge asegs _ _ [C8 _] [C4 _; C4 _] [C4 _]) in MAP; cbn [app cells_size csize Nat.add] in MAP.
  zstep. rewrite (zx32_small N) by lia.
  zstep. zstep. replace (N + -1) with (N - 1) by lia. rewrite HP.
  zstep. change (Z_to_le_bytes 8 0) with (le8 (Z_to_bv 64 0)). mem_after_store.
  apply (rw_cells_c8_zero_split _ _ [C8 _] [C4 _]) in MAP. cbn [app] in MAP.
  zstep. ifF. zstep. ifF.
  zstep. zstep. zstep.
  clear FRS.
  replace (Z_to_bv 64 B) with (Z_to_bv 64 (B + 32 * 0)) by (f_equal; lia).
  replace (N ≪ 5) with (32 * (N - 0)) by (rewrite Z.shiftl_mul_pow2 by lia; lia).
  pose proof (munch_refl [(B, B + 32 * N)] m1) as MU1. pose proof (wmono_refl asegs m1) as WM1.
  lazymatch goal with |- evt asegs ?QQ _ =>
    apply (init_loop map Bo No B N gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t6 sp F fc QQ HN B0 BT
             (Z.to_nat N) 0 nws0 m1 m1 _ _ _ _ _ _ _ _ _ ltac:(lia) ltac:(lia) HLn0 NA0 ltac:(intros d Hd; cbn in Hd; lia) MI MU1 WM1) end.
  intros m2 ws2 HL2 NA2 KE2 MI2 MU2 WM2.
  clear NA0 MU1 WM1 MI.
  transport_after_call asegs m1 m2 MU2 WM2. clear MU2 WM2.
  (* [comment removed for export] *)
  assert (EUo : bv_unsigned (Z_to_bv 64 Bo) = Bo) by (apply unsigned_lit; lia).
  assert (EUe : bv_unsigned (Z_to_bv 64 (Bo + 32 * No)) = Bo + 32 * No) by (apply unsigned_lit; lia).
  zstep. ifF.
  zstep. zstep. zstep.
  assert (KR0 : keys_rep (Z.to_nat N) ws2 (repeat RHM.EMPTY (Z.to_nat N))).
  { split; [exact HL2|]. split; [apply repeat_length|]. intros d Hd. rewrite (KE2 d Hd). f_equal.
    rewrite nth_repeat_lt by exact Hd. apply bv_eq. reflexivity. }
  assert (KO0 : ks_ok (repeat RHM.EMPTY (Z.to_nat N)) []).
  { apply Forall_forall. intros x Hx. left. apply repeat_spec in Hx. exact Hx. }
  replace (Z_to_bv 64 Bo) with (Z_to_bv 64 (Bo + 32 * 0)) by (f_equal; lia).
  lazymatch goal with |- evt asegs ?QQ _ =>
    eapply (outer_loop map Bo No B N RA gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t6 sp F fc QQ HN HP HNo B0 BT Bo0 BoT
              olds ows HLo HRo KRo BoI BI SPlo SPhi APART SPo SPn MAP0 MAP1
              olds 0 (repeat RHM.EMPTY (Z.to_nat N)) [] [] ks' pl ws2 _ m m2 _ _ _ _ _ _ _ _ _ RH0 eq_refl ltac:(lia) KR0 KO0 ND
              ltac:(constructor) ltac:(cbn; lia) MAP OA0 NA2 FR MI2 MU WM) end.
  intros m3 nws3 a3' a4' a5' a6' a7' t0' t1' t2' t3' t4' t5' KR3 MAP3 OA3 NA3 FR3 MI3 MU3 WM3.
  zstep. zstep. zstep.
  rewrite (ret_pc_even RA) by (try lia; Z.div_mod_to_equations; lia).
  apply evt_done.
  exists a3', a4', a5', a6', a7', t0', t1', t2', t3', t4', t5', m3.
  split; [reflexivity|].
  split; [replace (bv_unsigned sp - 16) with (bv_unsigned sp + -16) by lia; exact MU3|].
  split; [exact WM3|]. split; [exact MI3|]. split.
  - exact (xr_rw_cells_app_l m3 (map + 8) [C4 _; C4 _] [C4 _] (xr_rw_cells_app_r m3 map [C8 _] _ MAP3)).
  - intros d Hd. destruct KR3 as (L3 & _ & K3).
    replace (B + 32 * d) with (B + 8 * (4 * d)) by lia.
    apply (u64arr_cell m3 B nws3 (4 * d) _ NA3); [| lia].
    replace (Z.to_nat (4 * d)) with (4 * Z.to_nat d)%nat by lia. apply K3. lia.
Qed.
