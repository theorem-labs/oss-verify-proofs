(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtLib Require Import ImageCtA.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require Import Tac Mem Frame Cells Step Arr Exec RzCPS. 
From OssFuzzTheorems.Proofs.openssl.ct.lib.AS Require Import AsanAcct.
From OssFuzzTheorems.Proofs.openssl.ct.lib.A Require Import Shadow R_sizeclass.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtA Require Import Layout RT_iface D_defs R_cache_defs R_prim_defs R_glue_defs R_thread R_m2s R_poison R_leaves R_setshadow R_depot_defs R_unwind_defs R_asan_defs R_allocate1 R_allocate2 R_allocate3 R_pmalloc1 R_pmalloc2 R_pmalloc3 R_asan_malloc RT_state RT_rep RT_frame RT_trans RT_facts0 RT_sep RT_facts RT_icfacts RT_malstate.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma shad_add8_pm : forall a x, a mod 8 = 0 -> x mod 8 = 0 -> shad (a + x) = shad a + x / 8.
Proof.
  intros a x Ha Hx. unfold shad. apply Z.mod_divide in Ha, Hx; try (clear; lia). destruct Ha as [qa Ea]. destruct Hx as [qx Ex]. subst a x.
  replace (qa * 8 + qx * 8) with ((qa + qx) * 8) by ring. rewrite !Z.div_mul by lia. lia.
Qed.

Lemma size_rd_facts_pm : forall k, 0 <= k -> size_rd k mod 8 = 0 /\ size_rd k <= k < size_rd k + 8 /\ 0 <= size_rd k.
Proof. intros k Hk. unfold size_rd. split; [rewrite Z.mul_comm; apply Z.mod_mul; lia|]. Z.div_mod_to_equations. lia. Qed.

Lemma hb1_props_pm : forall b1, 0 <= b1 < 256 -> 0 <= hb1_pm b1 < 256 /\ hb1_pm b1 mod 4 = 1.
Proof.
  intros b1 Hb. assert (H : forallb (fun k => (0 <=? hb1_pm k) && (hb1_pm k <? 256) && (hb1_pm k mod 4 =? 1)) (map Z.of_nat (seq 0 256)) = true)
    by (vm_compute; reflexivity).
  rewrite forallb_forall in H. specialize (H b1 ltac:(apply in_map_iff; exists (Z.to_nat b1); split; [lia | apply in_seq; lia])).
  apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2]. apply Z.leb_le in H1. apply Z.ltb_lt in H2. apply Z.eqb_eq in H3. lia.
Qed.

Lemma hdr_b1_range_pm : forall hdr, 0 <= hdr_b1 hdr < 256.
Proof.
  intros hdr. unfold hdr_b1. rewrite zext_small. pose proof (bv_unsigned_in_range 8 (bv_extract 0 8 (le_bytes_to_word (firstn 1 (skipn 1 hdr))))) as R.
  unfold bv_modulus in R. cbn in R. rewrite unsigned_lit by lia. lia.
Qed.

Lemma depot_ok_mono_pm : forall D DNB SSB lo lo', depot_ok D DNB SSB lo -> lo <= lo' -> depot_ok D DNB SSB lo'.
Proof. intros D DNB SSB lo lo' (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8) Hl. repeat split; try assumption; lia. Qed.

Lemma T_MAIN_range_pm : forall tr, In tr T_MAIN -> Forall (fun x => 0 <= x < 2 ^ 64) tr.
Proof.
  intros tr Hin. assert (H : forallb (fun t => forallb (fun x => (0 <=? x) && (x <? 2 ^ 64)) t) T_MAIN = true) by (vm_compute; reflexivity).
  rewrite forallb_forall in H. specialize (H tr Hin). rewrite forallb_forall in H. apply Forall_forall. intros x Hx.
  specialize (H x Hx). apply andb_prop in H as [H1 H2]. apply Z.leb_le in H1. apply Z.ltb_lt in H2. lia.
Qed.

Lemma map_unsigned_lit_pm : forall tr, Forall (fun x => 0 <= x < 2 ^ 64) tr -> map bv_unsigned (map (Z_to_bv 64) tr) = tr.
Proof.
  induction tr as [|x tr IH]; intros H; [reflexivity|]. apply Forall_cons_iff in H as [H1 H2]. cbn [map].
  rewrite unsigned_lit by exact H1. rewrite (IH H2). reflexivity.
Qed.

Lemma rw_cells_app_l_pm : forall (m : mem) a cs1 cs2, rw_cells ctasegs m a (cs1 ++ cs2) -> rw_cells ctasegs m a cs1.
Proof.
  intros m a cs1 cs2 [[Hw Hb] W]. rewrite cells_bytes_app in Hb. apply bytes_at_app in Hb as [Hb1 _].
  apply cells_wf_app in Hw as [Hw1 _]. split; [split; [exact Hw1 | exact Hb1]|].
  rewrite cells_size_app, Nat2Z.inj_add in W. destruct W as (W0 & W1 & W2). split; [lia|]. split; [lia|]. intros j Hj. apply W2. lia.
Qed.

Lemma stk_CB_pm : forall (m : mem) a k, stk ctasegs m a (a + k) -> 0 <= k -> exists bs, rw_cells ctasegs m a [CB (Z.to_nat k) bs].
Proof.
  intros m a k St Hk. destruct (stk_bytes ctasegs m _ _ St ltac:(lia)) as (bs & Hl & Hb). exists bs.
  replace (a + k - a) with k in Hl by lia.
  split; [split; [cbn; split; [exact Hl | exact I] | cbn [cells_bytes cbytes]; rewrite app_nil_r; exact Hb]|].
  destruct St as (S0 & S1 & S). split; [lia|]. split; [cbn [cells_size csize]; rewrite Nat.add_0_r, Z2Nat.id by lia; lia|].
  intros j Hj. cbn [cells_size csize] in Hj. rewrite Nat.add_0_r, Z2Nat.id in Hj by lia. exact (proj1 (S (a + j) ltac:(lia))).
Qed.

Lemma rw_C1_of_pm : forall (m : mem) a, stk ctasegs m a (a + 1) -> exists b, rw_cells ctasegs m a [C1 b].
Proof.
  intros m a St. destruct (stk_CB_pm m a 1 St ltac:(lia)) as (bs & H). destruct H as [[[Hl _] Hb] R].
  destruct bs as [|b [|b' bs]]; cbn in Hl; try discriminate. exists b. split; [split; [exact (conj I I) | exact Hb] | exact R].
Qed.

Lemma land243_mod4_pm : forall b1, 0 <= b1 < 256 -> b1 mod 4 = 1 -> bv_unsigned (Z_to_bv 8 (Z.land b1 243)) mod 4 = 1.
Proof.
  intros b1 Hb H. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. cbn [Z.of_N].
  rewrite Z.mod_mod_divide by (exists 64; reflexivity).
  change 4 with (2 ^ 2). rewrite <- Z.land_ones by lia. rewrite <- Z.land_assoc. change (Z.land 243 (Z.ones 2)) with (Z.ones 2).
  rewrite Z.land_ones by lia. exact H.
Qed.

Lemma sp_off_pm : forall x k, 0 <= x < 2 ^ 64 -> Z_to_bv 64 (bv_unsigned (Z_to_bv 64 x) + k) = Z_to_bv 64 (x + k).
Proof. intros x k Hx. rewrite unsigned_lit by exact Hx. reflexivity. Qed.

Lemma munch_into_pm : forall W W' (m0 m1 m2 : mem), munch W' m0 m1 -> munch W m1 m2 -> sub_fp W W' -> munch W' m0 m2.
Proof. intros W W' m0 m1 m2 H1 H2 Hs. apply (munch_trans W' m0 m1 m2 H1). exact (munch_weaken W W' m1 m2 Hs H2). Qed.

Section Tail.
Variables (Σ : rtsA) (mX : mem) (B : Z) (gp s0A s1A s2A s3A s4A s5A s6A s7A s8A s9A s10A s11A : word) (F : bvmap 5 word) (fc : bv 32)
  (n lo : Z) (tr : list Z).
Hypothesis HA : ART_A Σ mX.
Hypothesis Hn : 1 <= n <= 64512.
Hypothesis En : n = 32768.   (* [comment removed for export] *)
Hypothesis Hca : ca Σ (ClassID (needed2 n)) <> [].
Hypothesis LOW : l_ACEIL (lay Σ) <= lo.
Hypothesis LOR : lo + 0x1000 <= B + -176.
Hypothesis SPT : B + 16 <= USTACK_TOP.
Hypothesis SPA : B mod 16 = 0.
Hypothesis Htr : In tr T_MAIN.
Hypothesis Htrl : (1 <= length tr <= TR_MAX)%nat.

#[local] Notation L := (lay Σ).
#[local] Notation SB := (l_SB (lay Σ)).
#[local] Notation T := (l_T (lay Σ)).
#[local] Notation TCX := (l_TCX (lay Σ)).
#[local] Notation DNB := (l_DNB (lay Σ)).
#[local] Notation SSB := (l_SSB (lay Σ)).
#[local] Notation c := (ClassID (needed2 n)).
#[local] Notation i := (Z.to_nat (last (ca Σ (ClassID (needed2 n))) 0)).
#[local] Notation AB := (p_abeg (l_SB (lay Σ)) (ClassID (needed2 n)) (Z.to_nat (last (ca Σ (ClassID (needed2 n))) 0))).
#[local] Notation S := (ClassSize (ClassID (needed2 n))).
#[local] Notation D := (dep Σ).
#[local] Notation BK := (DEP_BK (hash_of (d_hs (dep Σ)) 1)).

(* [comment removed for export] *)
Definition W_tail_pm : list ivl :=
  [(pc_addr T c, pc_addr T c + 4); (T + 2768, T + 3168); (l_ACEIL L, B + -48); (AB, AB + S); (shad AB, shad (AB + S));
   (d_tab, d_nuniq + 4); (d_map1, d_map1 + 8); (DNB, DNB + 2 ^ 20); (s_total, s_total + 8); (s_data0, s_stored0 + 4);
   (SSB, SSB + 2 ^ 23)].

(* [comment removed for export] *)
Definition tail_facts_pm (m : mem) : Prop :=
  ahdr m (AB + rz_size n - 16) n /\ lch_if m AB (AB + rz_size n - 16) n
  /\ bytes_at ctasegs m (shad (AB + rz_size n)) (ushadow n)
  /\ bytes_at ctasegs m (shad AB) (farun (rz_size n / 8))
  /\ bytes_at ctasegs m (shad (AB + rz_size n + ru8 n)) (farun ((S - rz_size n - ru8 n) / 8))
  /\ depot_rep (fst (depot_put D tr)) BK DNB SSB m
  /\ pc_cells m (pc_addr T c) (Z.of_nat (length (ca Σ c)) - 1) (MaxCount c) (ClassSize c).

Definition tail_post_pm : machine_state -> Prop :=
  fun ms => exists m', ret_st (Z_to_bv 64 0x19c9e4) (Z_to_bv 64 (B + -48)) gp (Z_to_bv 64 tpA) s0A s1A s2A s3A s4A s5A s6A s7A s8A s9A
                         s10A s11A (Z_to_bv 64 (AB + rz_size n)) m' ms
    /\ munch W_tail_pm mX m' /\ wmono ctasegs mX m' /\ mem_inv ctasegs m' /\ stk ctasegs m' lo (B + -48) /\ tail_facts_pm m'.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma tl_cls_pm : 1 <= c <= 30 /\ needed2 n <= S /\ rz_size n + n <= S /\ 32 <= S <= 65536 /\ S mod 32 = 0
  /\ 24 <= needed2 n <= n + 7 + 4096 /\ needed2 n mod 8 = 0 /\ 16 <= rz_size n <= 2048 /\ rz_size n mod 16 = 0.
Proof using Hn En.
  clear - Hn En. pose proof (needed2_range n ltac:(lia)) as (N1 & N2). pose proof (needed2_ge n ltac:(lia)) as NG.
  pose proof (rz_size_range n) as RZ. pose proof (rz_size_mod16 n) as RZ16.
  assert (RZ6 : rz_size n <= 1024).
  { unfold rz_size, rz_log. destruct (n <=? 48); [apply Z.leb_le; reflexivity|]. destruct (n <=? 96); [apply Z.leb_le; reflexivity|].
    destruct (n <=? 448); [apply Z.leb_le; reflexivity|]. destruct (n <=? 3968); [apply Z.leb_le; reflexivity|].
    destruct (n <=? 16128); [apply Z.leb_le; reflexivity|]. destruct (n <=? 32256); [apply Z.leb_le; reflexivity|].
    destruct (n <=? 64512) eqn:E6; [apply Z.leb_le; reflexivity | apply Z.leb_gt in E6; lia]. }
  assert (FP : from_primary n = true).
  { unfold from_primary, needed, rounded. apply Z.leb_le. assert ((Z.max (Z.max n 1) 8 + 7) / 8 < 8065) by (apply Z.div_lt_upper_bound; lia). lia. }
  assert (Hs : 1 <= needed2 n <= 65536) by (split; [lia|]; unfold needed2; rewrite FP; unfold from_primary in FP; apply Z.leb_le in FP; lia).
  pose proof (ClassID_props (needed2 n) Hs) as (CI1 & CI2). pose proof (ClassSize_range c ltac:(lia)) as (S1 & S2).
  repeat split; lia.
Qed.


(* [comment removed for export] *)
Lemma tl_entry_pm : 0 <= last (ca Σ c) 0 < Z.of_nat (length (r_st (pr Σ c))) /\ nth_error (r_st (pr Σ c)) i = Some CkIdle
  /\ ca_init Σ = true.
Proof using HA Hn En Hca.
  clear - HA Hn En Hca. pose proof tl_cls_pm as (K1 & _).
  pose proof (ART_wf Σ mX HA) as (_ & HR & _). destruct HR as (_ & _ & HC & HI & _). destruct (HC c ltac:(lia)) as (_ & _ & Hall).
  assert (Hin : In (last (ca Σ c) 0) (ca Σ c)) by (rewrite (app_removelast_last (ca Σ c) 0 Hca) at 2; apply in_or_app; right; left; reflexivity).
  destruct (proj1 (Forall_forall _ _) Hall _ Hin) as (H1 & H2). split; [exact H1|]. split; [exact H2|].
  destruct (ca_init Σ) eqn:E; [reflexivity|]. exfalso. exact (Hca (HI eq_refl c)).
Qed.

(* [comment removed for export] *)
Lemma tl_geo_pm :
  (* [comment removed for export] *)
  SB + c * 2 ^ 32 <= AB /\ AB + S <= SB + c * 2 ^ 32 + 0xE0000000 /\ AB mod 16 = 0
  /\ l_PRB L <= SB /\ SB + 2 ^ 37 + 4096 <= l_PRB L + 0x2000011000 /\ l_PRB L + 0x2000011000 <= l_ACEIL L
  /\ K_HIGH_SHADOW_hi <= l_PRB L
  (* [comment removed for export] *)
  /\ 0 < T /\ T mod 4096 = 0 /\ T + 4096 <= l_ACEIL L /\ 0 < TCX /\ TCX + 0x10000 <= l_ACEIL L
  /\ 0xbcb000 <= DNB /\ DNB + 2 ^ 20 <= l_ACEIL L /\ 0xbcb000 <= SSB /\ SSB + 2 ^ 23 <= l_ACEIL L
  (* [comment removed for export] *)
  /\ 2 ^ 44 + SHB + 8 <= l_ACEIL L /\ l_ACEIL L <= lo /\ lo + 0x1000 <= B + -176 /\ B + 16 <= 2 ^ 47 /\ B mod 16 = 0.
Proof using HA Hn En Hca LOW LOR SPT SPA.
  clear - HA Hn En Hca LOW LOR SPT SPA. pose proof tl_cls_pm as (K1 & K2 & K3 & K4 & K5 & _).
  pose proof tl_entry_pm as (E1 & E2 & _).
  pose proof (slot_geo Σ mX HA c i CkIdle ltac:(lia) E2) as (S1 & S2 & S3 & _).
  pose proof (geo_prb Σ mX HA) as (P1 & P2 & P3).
  pose proof (geo_grant Σ mX HA (l_PRB L) 0x2000011000 ltac:(unfold startup_grants; left; reflexivity)) as (G1 & G2 & G3 & G4 & G5).
  pose proof (geo_grant Σ mX HA T 4096 ltac:(unfold startup_grants; do 2 right; left; reflexivity)) as (T1 & T2 & T3 & _).
  pose proof (geo_grant Σ mX HA TCX 0x10000 ltac:(unfold startup_grants; do 3 right; left; reflexivity)) as (X1 & _ & X3 & _).
  pose proof (geo_grant Σ mX HA DNB 0x100000 ltac:(unfold startup_grants; do 6 right; left; reflexivity)) as (D1 & _ & D3 & _ & D5).
  pose proof (geo_grant Σ mX HA SSB 0x800000 ltac:(unfold startup_grants; do 7 right; left; reflexivity)) as (B1 & _ & B3 & _ & B5).
  pose proof (rta_sp0_win Σ mX HA) as Hw.
  unfold rb, kUserCap, K_LOW_SHADOW_lo, K_HIGH_SHADOW_hi, SEGTOP_A, l_ACEIL, STACK_WIN, SHB, RT_STACK, USTACK_TOP, rtA_sp0 in *.
  assert (AB16 : AB mod 16 = 0).
  { unfold p_abeg. apply Z.mod_divide; [lia|]. apply Z.divide_add_r; [apply Z.divide_add_r|].
    - apply Z.mod_divide in P3; [|lia]. apply (Z.divide_trans 16 (2 ^ 16)); [exists 4096; reflexivity | exact P3].
    - exists (c * 2 ^ 28). lia.
    - apply Z.divide_mul_r. apply Z.mod_divide in K5; [|lia]. apply (Z.divide_trans 16 32); [exists 2; reflexivity | exact K5]. }
  split; [lia|]. split; [lia|]. split; [exact AB16|]. split; [lia|]. split; [lia|]. split; [lia|].
  split; [destruct G4 as [G4|G4]; lia|].
  split; [lia|]. split; [exact T2|]. split; [lia|]. split; [lia|]. split; [lia|].
  split; [destruct D5 as [D5|D5]; lia|]. split; [lia|]. split; [destruct B5 as [B5|B5]; lia|]. split; [lia|].
  split; [lia|]. split; [lia|]. split; [lia|]. split; [lia | exact SPA].
Qed.

Lemma tl_AB64_pm : AB mod 64 = 0.
Proof using HA Hn En Hca LOW LOR SPT SPA.
  clear - HA Hn En Hca LOW LOR SPT SPA. pose proof tl_cls_pm as (K1 & _).
  pose proof (geo_prb Σ mX HA) as (P1 & P2 & P3).
  unfold p_abeg. apply Z.mod_divide; [lia|]. apply Z.divide_add_r; [apply Z.divide_add_r|].
  - apply Z.mod_divide in P3; [|lia]. apply (Z.divide_trans 64 (2 ^ 16)); [exists 1024; reflexivity | exact P3].
  - exists (c * 2 ^ 26). lia.
  - apply Z.divide_mul_r. replace S with 49152 by (rewrite En; reflexivity). exists 768; reflexivity.
Qed.

(* [comment removed for export] *)
Lemma tl_apart_pm :
  apart (l_PRB L) 0x2000011000 T 4096 /\ apart (l_PRB L) 0x2000011000 TCX 0x10000 /\ apart (l_PRB L) 0x2000011000 DNB 0x100000
  /\ apart (l_PRB L) 0x2000011000 SSB 0x800000 /\ apart T 4096 TCX 0x10000 /\ apart T 4096 DNB 0x100000 /\ apart T 4096 SSB 0x800000
  /\ apart TCX 0x10000 DNB 0x100000 /\ apart TCX 0x10000 SSB 0x800000 /\ apart DNB 0x100000 SSB 0x800000
  /\ (T + 4096 <= K_LOW_SHADOW_lo \/ K_HIGH_SHADOW_hi <= T) /\ (TCX + 0x10000 <= K_LOW_SHADOW_lo \/ K_HIGH_SHADOW_hi <= TCX)
  /\ (T + 4096 <= 0x10000 \/ SEGTOP_A <= T) /\ (TCX + 0x10000 <= 0x10000 \/ SEGTOP_A <= TCX)
  /\ (DNB + 0x100000 <= K_LOW_SHADOW_lo \/ K_HIGH_SHADOW_hi <= DNB) /\ (SSB + 0x800000 <= K_LOW_SHADOW_lo \/ K_HIGH_SHADOW_hi <= SSB).
Proof using HA.
  clear - HA.
  pose proof (geo_apart Σ mX HA 0 2 _ _ ltac:(lia) eq_refl eq_refl) as A02. pose proof (geo_apart Σ mX HA 0 3 _ _ ltac:(lia) eq_refl eq_refl) as A03.
  pose proof (geo_apart Σ mX HA 0 6 _ _ ltac:(lia) eq_refl eq_refl) as A06. pose proof (geo_apart Σ mX HA 0 7 _ _ ltac:(lia) eq_refl eq_refl) as A07.
  pose proof (geo_apart Σ mX HA 2 3 _ _ ltac:(lia) eq_refl eq_refl) as A23. pose proof (geo_apart Σ mX HA 2 6 _ _ ltac:(lia) eq_refl eq_refl) as A26.
  pose proof (geo_apart Σ mX HA 2 7 _ _ ltac:(lia) eq_refl eq_refl) as A27. pose proof (geo_apart Σ mX HA 3 6 _ _ ltac:(lia) eq_refl eq_refl) as A36.
  pose proof (geo_apart Σ mX HA 3 7 _ _ ltac:(lia) eq_refl eq_refl) as A37. pose proof (geo_apart Σ mX HA 6 7 _ _ ltac:(lia) eq_refl eq_refl) as A67.
  pose proof (geo_grant Σ mX HA T 4096 ltac:(unfold startup_grants; do 2 right; left; reflexivity)) as (_ & _ & _ & T4 & T5).
  pose proof (geo_grant Σ mX HA TCX 0x10000 ltac:(unfold startup_grants; do 3 right; left; reflexivity)) as (_ & _ & _ & X4 & X5).
  pose proof (geo_grant Σ mX HA DNB 0x100000 ltac:(unfold startup_grants; do 6 right; left; reflexivity)) as (_ & _ & _ & D4 & _).
  pose proof (geo_grant Σ mX HA SSB 0x800000 ltac:(unfold startup_grants; do 7 right; left; reflexivity)) as (_ & _ & _ & B4 & _).
  cbn [fst snd] in *. repeat split; assumption.
Qed.


(* [comment removed for export] *)
Ltac clear_disj := repeat match goal with X : _ \/ _ |- _ => clear X end.
Ltac sep_one := clear_disj; first
  [ unfold SHB, K_HIGH_SHADOW_hi, K_LOW_SHADOW_lo, SEGTOP_A in *; lia
  | pose proof tl_apart_pm as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & X & _);
    unfold K_LOW_SHADOW_lo, K_HIGH_SHADOW_hi, SHB in *; destruct X; lia
  | pose proof tl_apart_pm as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & X);
    unfold K_LOW_SHADOW_lo, K_HIGH_SHADOW_hi, SHB in *; destruct X; lia
  | pose proof tl_apart_pm as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & X & _); unfold K_LOW_SHADOW_lo, K_HIGH_SHADOW_hi, SHB in *; destruct X; lia
  | pose proof tl_apart_pm as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & X & _); unfold SEGTOP_A in *; destruct X; lia
  | pose proof tl_apart_pm as (_ & _ & _ & _ & _ & X & _); unfold apart in X; destruct X; lia
  | pose proof tl_apart_pm as (_ & _ & _ & _ & _ & _ & X & _); unfold apart in X; destruct X; lia
  | pose proof tl_apart_pm as (X & _); unfold apart in X; destruct X; lia
  | pose proof tl_apart_pm as (_ & _ & X & _); unfold apart in X; destruct X; lia
  | pose proof tl_apart_pm as (_ & _ & _ & X & _); unfold apart in X; destruct X; lia
  | pose proof tl_apart_pm as (_ & X & _); unfold apart in X; destruct X; lia
  | pose proof tl_apart_pm as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & X & _); unfold K_LOW_SHADOW_lo, K_HIGH_SHADOW_hi, SHB in *; destruct X; lia
  | pose proof tl_apart_pm as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & X & _); unfold SEGTOP_A in *; destruct X; lia ].

(* [comment removed for export] *)
Local Ltac sep_s0 := unfold SHB, K_HIGH_SHADOW_hi, K_LOW_SHADOW_lo, SEGTOP_A in *; lia.
Local Ltac sep_s1 := pose proof tl_apart_pm as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & X & _);
    unfold K_LOW_SHADOW_lo, K_HIGH_SHADOW_hi, SHB in *; destruct X; lia.
Local Ltac sep_s2 := pose proof tl_apart_pm as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & X);
    unfold K_LOW_SHADOW_lo, K_HIGH_SHADOW_hi, SHB in *; destruct X; lia.
Local Ltac sep_s3 := pose proof tl_apart_pm as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & X & _); unfold K_LOW_SHADOW_lo, K_HIGH_SHADOW_hi, SHB in *; destruct X; lia.
Local Ltac sep_s4 := pose proof tl_apart_pm as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & X & _); unfold SEGTOP_A in *; destruct X; lia.
Local Ltac sep_s5 := pose proof tl_apart_pm as (_ & _ & _ & _ & _ & X & _); unfold apart in X; destruct X; lia.
Local Ltac sep_s6 := pose proof tl_apart_pm as (_ & _ & _ & _ & _ & _ & X & _); unfold apart in X; destruct X; lia.
Local Ltac sep_s7 := pose proof tl_apart_pm as (X & _); unfold apart in X; destruct X; lia.
Local Ltac sep_s8 := pose proof tl_apart_pm as (_ & _ & X & _); unfold apart in X; destruct X; lia.
Local Ltac sep_s9 := pose proof tl_apart_pm as (_ & _ & _ & X & _); unfold apart in X; destruct X; lia.
Local Ltac sep_s10 := pose proof tl_apart_pm as (_ & X & _); unfold apart in X; destruct X; lia.
Local Ltac sep_s11 := pose proof tl_apart_pm as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & X & _); unfold K_LOW_SHADOW_lo, K_HIGH_SHADOW_hi, SHB in *; destruct X; lia.
Local Ltac sep_s12 := pose proof tl_apart_pm as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & X & _); unfold SEGTOP_A in *; destruct X; lia.
Local Ltac sep_fast := clear_disj; first
  [ lazymatch goal with
    | |- context [l_T _] => lazymatch goal with
         | |- context [l_DNB _] => sep_s5 | |- context [l_SSB _] => sep_s6 | |- context [l_PRB _] => sep_s7
         | |- context [shad _] => sep_s3 | |- context [p_abeg _ _ _] => sep_s7 | |- context [17594333495296%Z] => sep_s3
         | |- _ => first [ sep_s4 | sep_s3 | sep_s0 ] end
    | |- context [l_TCX _] => lazymatch goal with
         | |- context [17594333495296%Z] => sep_s11 | |- context [l_PRB _] => sep_s10 | |- _ => first [ sep_s12 | sep_s0 ] end
    | |- context [shad _] => lazymatch goal with
         | |- context [l_DNB _] => sep_s1 | |- context [l_SSB _] => sep_s2 | |- _ => sep_s0 end
    | |- context [p_abeg _ _ _] => lazymatch goal with
         | |- context [l_DNB _] => sep_s8 | |- context [l_SSB _] => sep_s9 | |- _ => sep_s0 end
    | |- _ => sep_s0
    end
  | sep_one ].

Lemma tl_shad_pm : SHB <= shad AB /\ shad (AB + S) = shad AB + S / 8 /\ shad (AB + S) <= 2 ^ 44 + SHB.
Proof using HA Hn En Hca LOW LOR SPT SPA.
  clear - HA Hn En Hca LOW LOR SPT SPA. pose proof tl_cls_pm as (K1 & K2 & K3 & K4 & K5 & _).
  pose proof tl_geo_pm as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & _ & _ & _ & _ & _ & _ & _ & _ & _ & G17 & G18 & G19 & G20 & _).
  unfold K_HIGH_SHADOW_hi in *.
  assert (E : shad (AB + S) = shad AB + S / 8).
  { unfold shad. assert (M1 : AB = 8 * (AB / 8)) by (apply Z.div_exact; [lia | exact (mod8_of AB 16 ltac:(lia) G3 ltac:(exists 2; reflexivity))]).
    assert (M2 : S = 8 * (S / 8)) by (apply Z.div_exact; [lia | exact (mod8_of S 32 ltac:(lia) K5 ltac:(exists 4; reflexivity))]).
    rewrite M1 at 1. rewrite M2 at 1. replace (8 * (AB / 8) + 8 * (S / 8)) with ((AB / 8 + S / 8) * 8) by ring. rewrite Z.div_mul by lia. lia. }
  split; [unfold shad; pose proof (Z.div_pos AB 8 ltac:(lia) ltac:(lia)); lia|]. split; [exact E|].
  unfold shad. assert ((AB + S) / 8 <= 2 ^ 44) by (apply Z.div_le_upper_bound; unfold SHB in *; lia). lia.
Qed.

(* [comment removed for export] *)
Definition dep_far_pm (a b : Z) : Prop :=
  (d_tab + (d_nuniq + 4 - d_tab) <= a \/ b <= d_tab) /\ (d_map1 + 8 <= a \/ b <= d_map1)
  /\ (DNB + 2 ^ 20 <= a \/ b <= DNB) /\ (s_total + 8 <= a \/ b <= s_total)
  /\ (s_data0 + (s_stored0 + 4 - s_data0) <= a \/ b <= s_data0) /\ (SSB + 2 ^ 23 <= a \/ b <= SSB).

Fixpoint far_all_pm (W : list ivl) : Prop :=
  match W with [] => True | (a, b) :: W' => dep_far_pm a b /\ far_all_pm W' end.

Lemma dep_frame_far_pm : forall D' BK' lo' W (m m' : mem), depot_rep D' BK' DNB SSB m -> depot_ok D' DNB SSB lo' ->
  munch W m m' -> wmono ctasegs m m' -> far_all_pm W -> depot_rep D' BK' DNB SSB m'.
Proof.
  intros D' BK' lo' W m m' DR OK MU WM HF. apply (depot_rep_frame D' BK' DNB SSB lo' W m m' DR OK MU WM); clear - HF;
    induction W as [|[a b] W IH]; cbn [disjoint_from far_all_pm] in *; try exact I; destruct HF as ((F1 & F2 & F3 & F4 & F5 & F6) & HW);
    (split; [assumption | exact (IH HW)]).
Qed.

Lemma dep_far_T_pm : forall a b, T <= a -> b <= T + 4096 -> dep_far_pm a b.
Proof using HA.
  intros a b H1 H2. clear - HA H1 H2.
  pose proof tl_apart_pm as (_ & _ & _ & _ & _ & A26 & A27 & _ & _ & _ & _ & _ & TP & _).
  unfold apart, dep_far_pm, SEGTOP_A in *. destruct TP; destruct A26; destruct A27; repeat split; lia.
Qed.

Lemma dep_far_stk_pm : forall a b, l_ACEIL L <= a -> dep_far_pm a b.
Proof using HA Hn En Hca LOW LOR SPT SPA.
  intros a b H1. clear - HA Hn En Hca LOW LOR SPT SPA H1.
  pose proof tl_geo_pm as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & D2 & _ & B2 & G17 & _).
  unfold dep_far_pm, SHB in *. repeat split; lia.
Qed.

Lemma dep_far_shad_pm : forall a b, shad AB <= a -> b <= shad (AB + S) -> dep_far_pm a b.
Proof using HA Hn En Hca LOW LOR SPT SPA.
  intros a b H1 H2. clear - HA Hn En Hca LOW LOR SPT SPA H1 H2. pose proof tl_shad_pm as (S1 & _ & S3).
  pose proof tl_apart_pm as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & DS & BS).
  unfold dep_far_pm, K_LOW_SHADOW_lo, K_HIGH_SHADOW_hi, SHB in *. destruct DS; destruct BS; repeat split; lia.
Qed.

Lemma dep_far_chunk_pm : forall a b, AB <= a -> b <= AB + S -> dep_far_pm a b.
Proof using HA Hn En Hca LOW LOR SPT SPA.
  intros a b H1 H2. clear - HA Hn En Hca LOW LOR SPT SPA H1 H2.
  pose proof tl_cls_pm as (K1 & _). pose proof tl_geo_pm as (G1 & G2 & _ & G4 & G5 & _ & G7 & _).
  pose proof tl_apart_pm as (_ & _ & A03 & A04 & _).
  unfold dep_far_pm, apart, K_HIGH_SHADOW_hi in *. destruct A03; destruct A04; repeat split; lia.
Qed.

(* [comment removed for export] *)
Lemma tw_img_pm : forall a k, 0x10000 <= a -> a + k <= SEGTOP_A -> (a + k <= 0x743f08 \/ 0xb53f30 <= a) -> disjoint_from W_tail_pm a k.
Proof using HA Hn En Hca LOW LOR SPT SPA.
  intros a k H1 H2 H3. clear - HA Hn En Hca LOW LOR SPT SPA H1 H2 H3.
  pose proof tl_geo_pm as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & _ & _ & G13 & _ & G15 & _ & G17 & _).
  pose proof tl_shad_pm as (S1 & S2 & S3). pose proof tl_cls_pm as (K1 & _).
  pose proof tl_apart_pm as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & TP & _).
  unfold W_tail_pm, pc_addr. cbn [disjoint_from]. unfold SEGTOP_A, SHB, K_HIGH_SHADOW_hi in *.
  destruct TP as [TP|TP]; (split; [lia|]); (split; [lia|]); (split; [lia|]); (split; [lia|]); (split; [lia|]);
    (split; [lia|]); (split; [lia|]); (split; [lia|]); (split; [lia|]); (split; [lia|]); (split; [lia | exact I]).
Qed.

Lemma tw_T_pm : forall a k, T <= a -> a + k <= T + 4096 -> (a + k <= pc_addr T c \/ pc_addr T c + 4 <= a) ->
  (a + k <= T + 2768 \/ T + 3168 <= a) -> disjoint_from W_tail_pm a k.
Proof using HA Hn En Hca LOW LOR SPT SPA.
  intros a k H1 H2 H3 H4. clear - HA Hn En Hca LOW LOR SPT SPA H1 H2 H3 H4.
  pose proof tl_geo_pm as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & _ & _ & G13 & _ & G15 & _ & G17 & _).
  pose proof tl_shad_pm as (S1 & S2 & S3). pose proof tl_cls_pm as (K1 & _).
  pose proof tl_apart_pm as (A02 & _ & _ & _ & _ & A26 & A27 & _ & _ & _ & TS & _ & TP & _).
  unfold W_tail_pm. cbn [disjoint_from]. unfold apart, K_LOW_SHADOW_lo, K_HIGH_SHADOW_hi, SEGTOP_A, SHB in *.
  split; [clear H4 A02 A26 A27 TS TP; lia|]. split; [clear H3 A02 A26 A27 TS TP; lia|]. split; [clear H3 H4 A02 A26 A27 TS TP; lia|].
  split; [clear H3 H4 A26 A27 TS TP; destruct A02; lia|]. split; [clear H3 H4 A02 A26 A27 TP; destruct TS; lia|].
  split; [clear H3 H4 A02 A26 A27 TS; destruct TP; lia|]. split; [clear H3 H4 A02 A26 A27 TS; destruct TP; lia|].
  split; [clear H3 H4 A02 A27 TS TP; destruct A26; lia|]. split; [clear H3 H4 A02 A26 A27 TS; destruct TP; lia|].
  split; [clear H3 H4 A02 A26 A27 TS; destruct TP; lia|].
  split; [clear H3 H4 A02 A26 TS TP; destruct A27; lia | exact I].
Qed.

Lemma tw_TCX_pm : forall a k, TCX <= a -> a + k <= TCX + 0x10000 -> disjoint_from W_tail_pm a k.
Proof using HA Hn En Hca LOW LOR SPT SPA.
  intros a k H1 H2. clear - HA Hn En Hca LOW LOR SPT SPA H1 H2.
  pose proof tl_geo_pm as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12 & G13 & _ & G15 & _ & G17 & _).
  pose proof tl_shad_pm as (S1 & S2 & S3). pose proof tl_cls_pm as (K1 & _).
  pose proof tl_apart_pm as (_ & A03 & _ & _ & A23 & _ & _ & A36 & A37 & _ & _ & XS & _ & XP & _).
  unfold W_tail_pm, pc_addr. cbn [disjoint_from]. unfold apart, K_LOW_SHADOW_lo, K_HIGH_SHADOW_hi, SEGTOP_A, SHB in *.
  split; [clear A03 A36 A37 XS XP; destruct A23; lia|]. split; [clear A03 A36 A37 XS XP; destruct A23; lia|].
  split; [clear A03 A23 A36 A37 XS XP; lia|]. split; [clear A23 A36 A37 XS XP; destruct A03; lia|].
  split; [clear A03 A23 A36 A37 XP; destruct XS; lia|].
  split; [clear A03 A23 A36 A37 XS; destruct XP; lia|]. split; [clear A03 A23 A36 A37 XS; destruct XP; lia|].
  split; [clear A03 A23 A37 XS XP; destruct A36; lia|]. split; [clear A03 A23 A36 A37 XS; destruct XP; lia|].
  split; [clear A03 A23 A36 A37 XS; destruct XP; lia|].
  split; [clear A03 A23 A36 XS XP; destruct A37; lia | exact I].
Qed.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma tl_room_pm : rz_size n + ru8 n <= S /\ rz_size n + 16 <= S /\ Z.of_nat (length (ushadow n)) = ru8 n / 8 /\ n <= ru8 n < n + 8
  /\ ru8 n mod 8 = 0.
Proof using Hn En.
  clear - Hn En. pose proof tl_cls_pm as (K1 & K2 & K3 & K4 & K5 & _).
  pose proof (slot_room c n ltac:(lia) ltac:(lia) K3) as (R1 & R2). pose proof (ushadow_len n ltac:(lia)) as U.
  unfold ru8 in *. split; [exact R1|]. split; [exact R2|]. split; [exact U|]. Z.div_mod_to_equations. lia.
Qed.

(* [comment removed for export] *)
Lemma tl_dep_pm : depot_ok D DNB SSB (l_ACEIL L) /\ dep_inv D /\ depot_ok (fst (depot_put D tr)) DNB SSB (l_ACEIL L)
  /\ d_n D + 2 < 2 ^ 16 /\ d_tot D + Z.of_nat (length tr) + 1 < 2 ^ 20.
Proof using HA Htrl.
  clear - HA Htrl. pose proof (ART_wf Σ mX HA) as (_ & _ & _ & _ & _ & _ & _ & OK & _ & _ & DI & _).
  pose proof (dep_inv_bounds D DI) as (B1 & B2).
  split; [exact OK|]. split; [exact DI|]. split; [apply depot_ok_put_ok; [exact OK | lia | lia]|]. split; lia.
Qed.

(* [comment removed for export] *)
Lemma tl_shadows_pm : shad (AB + rz_size n) = shad AB + rz_size n / 8
  /\ shad (AB + rz_size n + ru8 n) = shad AB + rz_size n / 8 + ru8 n / 8
  /\ shad (AB + rz_size n + size_rd n) = shad AB + rz_size n / 8 + size_rd n / 8
  /\ rz_size n / 8 + ru8 n / 8 <= S / 8 /\ size_rd n / 8 <= ru8 n / 8 /\ 2 <= rz_size n / 8
  /\ (n mod 8 <> 0 -> size_rd n / 8 + 1 = ru8 n / 8) /\ (n mod 8 = 0 -> size_rd n = ru8 n).
Proof using HA Hn En Hca LOW LOR SPT SPA.
  clear - HA Hn En Hca LOW LOR SPT SPA. pose proof tl_geo_pm as (_ & _ & G3 & _). pose proof tl_room_pm as (R1 & R2 & R3 & R4 & R5).
  pose proof tl_cls_pm as (K1 & K2 & K3 & K4 & K5 & K6 & K7 & K8 & K9). pose proof (size_rd_facts_pm n ltac:(lia)) as (D1 & D2 & D3).
  assert (M8 : AB mod 8 = 0) by exact (mod8_of AB 16 ltac:(lia) G3 ltac:(exists 2; reflexivity)).
  assert (RZ8 : rz_size n mod 8 = 0) by exact (mod8_of (rz_size n) 16 ltac:(lia) K9 ltac:(exists 2; reflexivity)).
  rewrite (shad_add8_pm AB (rz_size n) M8 RZ8).
  replace (AB + rz_size n + ru8 n) with (AB + (rz_size n + ru8 n)) by ring.
  rewrite (shad_add8_pm AB (rz_size n + ru8 n) M8 ltac:(rewrite Z.add_mod, RZ8, R5 by lia; reflexivity)).
  replace (AB + rz_size n + size_rd n) with (AB + (rz_size n + size_rd n)) by ring.
  rewrite (shad_add8_pm AB (rz_size n + size_rd n) M8 ltac:(rewrite Z.add_mod, RZ8, D1 by lia; reflexivity)).
  unfold ru8, size_rd in *. Z.div_mod_to_equations. repeat split; intros; lia.
Qed.

Lemma tl_rr_pm : (S - rz_size n - ru8 n) / 8 = S / 8 - rz_size n / 8 - ru8 n / 8 /\ 0 <= (S - rz_size n - ru8 n) / 8.
Proof using Hn En.
  clear - Hn En. pose proof tl_cls_pm as (K1 & K2 & K3 & K4 & K5 & K6 & K7 & K8 & K9). pose proof tl_room_pm as (R1 & R2 & R3 & R4 & R5).
  assert (M1 : S mod 8 = 0) by exact (mod8_of S 32 ltac:(lia) K5 ltac:(exists 4; reflexivity)).
  assert (M2 : rz_size n mod 8 = 0) by exact (mod8_of (rz_size n) 16 ltac:(lia) K9 ltac:(exists 2; reflexivity)).
  set (x := S) in *. set (y := rz_size n) in *. set (z := ru8 n) in *. clearbody x y z. clear - M1 M2 R5 R1.
  split; [|apply Z.div_pos; lia]. Z.div_mod_to_equations. lia.
Qed.

(* [comment removed for export] *)
Lemma tf_stack_pm : forall W (m m' : mem), tail_facts_pm m -> munch W m m' -> wmono ctasegs m m' -> sub_fp W [(l_ACEIL L, USTACK_TOP)] ->
  tail_facts_pm m'.
Proof using HA Hn En Hca LOW LOR SPT SPA Htrl.
  intros W m m' H MU WM SF. assert (MU' : munch [(l_ACEIL L, USTACK_TOP)] m m') by (eapply munch_weaken; [exact SF | exact MU]).
  clear MU SF. pose proof tl_geo_pm as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & _ & _ & G13 & G14 & G15 & G16 & G17 & _).
  pose proof tl_shad_pm as (S1 & S2 & S3). pose proof tl_room_pm as (R1 & R2 & R3 & R4 & R5). pose proof tl_dep_pm as (_ & _ & OK' & _).
  pose proof tl_cls_pm as (K1 & K2 & K3 & K4 & K5 & K6 & K7 & K8 & K9). pose proof tl_shadows_pm as (E1 & E2 & _ & E4 & _).
  assert (DK : forall a k, a + k <= l_ACEIL L -> disjoint_from [(l_ACEIL L, USTACK_TOP)] a k) by (intros a k Hk; cbn; split; [lia | exact I]).
  destruct H as ((b1 & ctx & Hb & Hh) & Hl & U & RZ1 & RZ2 & DR & PC).
  split; [exists b1, ctx; split; [exact Hb|]; apply (rw_cells_transport ctasegs _ m m' _ _ Hh MU' WM); cbn [cells_size csize Nat.add]; apply DK; lia|].
  split; [intros Hr; pose proof (Hl Hr) as X; unfold lch in *; apply (rw_cells_transport ctasegs _ m m' _ _ X MU' WM); cbn [cells_size csize Nat.add]; apply DK; lia|].
  assert (SH : forall a bs, a + Z.of_nat (length bs) <= shad AB + S / 8 -> bytes_at ctasegs m a bs -> bytes_at ctasegs m' a bs).
  { intros a bs Ha Hb'. apply (bytes_at_transport ctasegs _ m m' _ _ Hb' MU'). apply DK. unfold SHB in *. lia. }
  assert (FL : forall k, 0 <= k -> Z.of_nat (length (farun k)) = k) by (intros k Hk; unfold farun; rewrite repeat_length; lia).
  split; [apply SH; [rewrite E1, R3; lia | exact U]|].
  assert (U8 : 0 <= ru8 n / 8) by (apply Z.div_pos; lia).
  split; [apply SH; [rewrite FL by (apply Z.div_pos; lia); lia | exact RZ1]|].
  split; [apply SH; [rewrite E2, FL by (apply Z.div_pos; lia); pose proof tl_rr_pm as (Hrr0 & _); lia | exact RZ2]|].
  split; [apply (depot_rep_frame _ _ _ _ _ _ m m' DR OK' MU' WM); apply DK; unfold SEGTOP_A in *; lia|].
  apply (rw_cells_transport ctasegs _ m m' _ _ PC MU' WM). cbn [cells_size csize Nat.add]. apply DK. unfold pc_addr. lia.
Qed.



(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)


Ltac tw_lit X MU WM := apply (rw_cells_transport ctasegs _ _ _ _ _ X MU WM); cbn [cells_size csize Nat.add];
  apply tw_img_pm; unfold g_tsd_key_inited, g_tsd_key, pth_tsd, g_pthread_tsd_main, g_got_common_flags, g_can_poison,
    g_cf_clear_shadow_mmap_threshold, g_got_real_memset, g_real_memset, SEGTOP_A; lia.

Lemma tl_static_pm : forall (m : mem), munch W_tail_pm mX m -> wmono ctasegs mX m ->
  thread_cells TCX T m /\ m2s_cells m /\ ps_cells m /\ setshadow_cells m
  /\ rw_cells ctasegs m g_GOT_asan_flags [C8 (Z_to_bv 64 g_asan_flags)] /\ rw_cells ctasegs m (g_asan_flags + 44) [C4 (Z_to_bv 64 4096)]
  /\ rw_cells ctasegs m (g_asan_flags + 52) [C4 (Z_to_bv 64 190)] /\ rw_cells ctasegs m (g_asan_flags + 85) [C1 (Z_to_bv 8 1)]
  /\ rw_cells ctasegs m (tpA + 32) [C4 (Z_to_bv 64 0)] /\ rw_cells ctasegs m 0x5a9eb0 [C8 (Z_to_bv 64 32)]
  /\ rw_cells ctasegs m g_MFHooks [C8 (Z_to_bv 64 0)] /\ rw_cells ctasegs m g_can_poison_memory [C1 (Z_to_bv 8 1)]
  /\ rw_cells ctasegs m (TCX + 8) [C4 (Z_to_bv 64 0)] /\ rw_cells ctasegs m T [C8 (Z_to_bv 64 TCX)].
Proof using HA Hn En Hca LOW LOR SPT SPA.
  intros m MU WM. clear - HA Hn En Hca LOW LOR SPT SPA MU WM.
  pose proof (ART_consts Σ mX HA) as (_ & _ & ((T1 & T2 & T3 & T4) & T5) & (M1 & M2 & M3) & (P1 & _ & (S1 & S2) & P3 & P4) & _ & _
    & (X1 & X2 & X3 & X4 & X5 & X6 & X7 & X8 & X9 & X10 & X11 & X12 & X13 & X14 & X15 & X16 & X17 & X18 & X19 & X20 & X21 & X22 & X23 & X24
       & X25 & X26 & X27 & X28 & X29 & X30 & X31 & _ & X33 & _)).
  pose proof tl_geo_pm as (_ & _ & _ & _ & _ & _ & _ & G8 & G9 & G10 & G11 & G12 & _).
  assert (M' : m2s_cells m) by (split; [tw_lit M1 MU WM | split; [tw_lit M2 MU WM | tw_lit M3 MU WM]]).
  assert (SS' : setshadow_cells m) by (split; [tw_lit S1 MU WM | tw_lit S2 MU WM]).
  split.
  { split; [split; [tw_lit T1 MU WM | split; [tw_lit T2 MU WM | split; [tw_lit T3 MU WM | tw_lit T4 MU WM]]]|].
    apply (rw_cells_transport ctasegs _ _ _ _ _ T5 MU WM). cbn [cells_size csize Nat.add]. apply tw_TCX_pm; lia. }
  split; [exact M'|]. split; [split; [tw_lit P1 MU WM | split; [exact M' | split; [exact SS' | split; [tw_lit P3 MU WM | tw_lit P4 MU WM]]]]|].
  split; [exact SS'|].
  split; [tw_lit X23 MU WM|]. split; [tw_lit X24 MU WM|]. split; [tw_lit X25 MU WM|]. split; [tw_lit X26 MU WM|].
  split; [unfold tpA; tw_lit X27 MU WM|]. split; [tw_lit X28 MU WM|]. split; [unfold g_MFHooks; tw_lit X29 MU WM|].
  split; [unfold g_can_poison_memory; tw_lit X30 MU WM|].
  split.
  { apply (rw_cells_transport ctasegs _ _ _ _ _ X31 MU WM). cbn [cells_size csize Nat.add]. apply tw_TCX_pm; lia. }
  apply (rw_cells_transport ctasegs _ _ _ _ _ X33 MU WM). cbn [cells_size csize Nat.add]. apply tw_T_pm; unfold pc_addr; pose proof tl_cls_pm as (K1 & _); lia.
Qed.



(* [comment removed for export] *)
Lemma tl_chunk_stk_pm : forall (m : mem), wmono ctasegs mX m -> stk ctasegs m AB (AB + S).
Proof using HA Hn En Hca.
  intros m WM. clear - HA Hn En Hca WM. pose proof tl_cls_pm as (K1 & _). pose proof tl_entry_pm as (_ & E2 & _).
  pose proof (ART_chunk Σ mX HA) as (P & _). pose proof (P c i CkIdle ltac:(lia) E2) as (St & _). exact (stk_wmono mX m _ _ St WM).
Qed.

(* [comment removed for export] *)
Definition trc_cells_pm (m : mem) (tb : list word) : Prop :=
  rw_cells ctasegs m B [C8 (Z_to_bv 64 (B + 16)); C8 (Z_to_bv 64 (Z.of_nat (length tr)))]
  /\ u64arr ctasegs m (B + 16) (wr_trace tr tb) /\ length tb = 255%nat.
(* [comment removed for export] *)
Definition af_cells_pm (m : mem) (j0 : list byte) : Prop :=
  alloc_frame64 m (B + -176) (Z_to_bv 64 0x19c9e4) s0A s1A s2A s3A s4A s5A s6A s7A s8A s9A s10A s11A
  /\ rw_cells ctasegs m (B + -176) [CB 8 j0].

Lemma af_transport_pm : forall W (m m' : mem) j0, af_cells_pm m j0 -> munch W m m' -> wmono ctasegs m m' ->
  disjoint_from W (B + -176) 128 -> af_cells_pm m' j0.
Proof.
  intros W m m' j0 (A1 & A2) MU WM D. unfold alloc_frame64 in *.
  split; [apply (rw_cells_transport ctasegs _ m m' _ _ A1 MU WM); cbn [cells_size csize Nat.add]; eapply dsj_sub; [exact D | lia | lia]|].
  apply (rw_cells_transport ctasegs _ m m' _ _ A2 MU WM); cbn [cells_size csize Nat.add]; eapply dsj_sub; [exact D | lia | lia].
Qed.





(* [comment removed for export] *)
Lemma tl_shadow_stk_pm : forall (m : mem), wmono ctasegs mX m -> stk ctasegs m (shad AB) (shad AB + S / 8).
Proof using HA Hn En Hca LOW LOR SPT SPA.
  intros m WM. clear - HA Hn En Hca LOW LOR SPT SPA WM. pose proof tl_cls_pm as (K1 & K2 & K3 & K4 & K5 & _).
  pose proof tl_entry_pm as (E1 & E2 & _). pose proof tl_shad_pm as (S1 & S2 & S3).
  pose proof (slot_geo Σ mX HA c i CkIdle ltac:(lia) E2) as (G1 & G2 & G3 & _).
  pose proof (ART_prim Σ mX HA c ltac:(lia)) as (_ & _ & _ & _ & _ & _ & St).
  assert (Hlo : shad (rb SB c) <= shad AB) by (unfold shad; apply Z.add_le_mono_r; apply Z.div_le_mono; lia).
  assert (Hhi : shad (AB + S) <= shad (rb SB c + 2 ^ 32)) by (unfold shad; apply Z.add_le_mono_r; apply Z.div_le_mono; unfold rb, kUserCap in *; lia).
  rewrite S2 in Hhi. pose proof (stk_wmono mX m _ _ St WM) as St'.
  destruct (stk_split ctasegs m _ (shad AB) _ St' ltac:(unfold shad in *; pose proof (Z.div_le_mono (rb SB c) (rb SB c + 2 ^ 32) 8 ltac:(lia) ltac:(lia)); lia)) as [_ X].
  exact (proj1 (stk_split ctasegs m _ (shad AB + S / 8) _ X ltac:(lia))).
Qed.

(* [comment removed for export] *)
Lemma tl_p3stats_pm : forall (m : mem), wmono ctasegs mX m -> p3_stats m T.
Proof using HA.
  intros m WM. clear - HA WM. pose proof (ART_consts Σ mX HA) as (_ & _ & _ & _ & _ & _ & _ & ICR).
  destruct ICR as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & St & _).
  pose proof (stk_wmono mX m _ _ St WM) as St'.
  assert (W8 : forall a, T + 2768 <= a -> a + 8 <= T + 3168 -> exists w, rw_cells ctasegs m a [C8 w]).
  { intros a H1 H2. destruct (stk_split ctasegs m (T + 2768) a (T + 3168) St' ltac:(lia)) as [_ X].
    destruct (stk_split ctasegs m a (a + 8) (T + 3168) X ltac:(lia)) as [X8 _].
    destruct (stk_CB_pm m a 8 X8 ltac:(lia)) as (bs & Hb). destruct (word_of_stk m a (a + 8) a X8 ltac:(lia) ltac:(lia)) as (v & Hv).
    exists v. split; [exact Hv | exact (proj2 Hb)]. }
  assert (CONS : forall a c0 cs, rw_cells ctasegs m a [c0] -> rw_cells ctasegs m (a + Z.of_nat (csize c0)) cs -> rw_cells ctasegs m a (c0 :: cs)).
  { intros a c0 cs [[Hw1 Hb1] W1] [[Hw2 Hb2] W2]. cbn [cells_wf cells_bytes cells_size] in *. rewrite app_nil_r in Hb1.
    rewrite Nat.add_0_r in W1. split; [split; [split; [exact (proj1 Hw1) | exact Hw2]|]|].
    - apply bytes_at_app. split; [exact Hb1|]. rewrite cbytes_length by exact (proj1 Hw1). exact Hb2.
    - destruct W1 as (A0 & A1 & A2). destruct W2 as (B0 & B1 & B2). split; [lia|]. split; [cbn [cells_size]; rewrite Nat2Z.inj_add; lia|].
      intros j Hj. cbn [cells_size] in Hj. rewrite Nat2Z.inj_add in Hj. destruct (Z_lt_le_dec j (Z.of_nat (csize c0))) as [L|L]; [apply A2; lia|].
      replace (a + j) with (a + Z.of_nat (csize c0) + (j - Z.of_nat (csize c0))) by lia. apply B2. lia. }
  destruct (W8 (T + 2800) ltac:(lia) ltac:(lia)) as (x0 & X0). destruct (W8 (T + 2808) ltac:(lia) ltac:(lia)) as (x1 & X1).
  destruct (W8 (T + 2816) ltac:(lia) ltac:(lia)) as (x2 & X2). destruct (W8 (T + 2904) ltac:(lia) ltac:(lia)) as (x13 & X13).
  split; [exists x0, x1, x2; apply CONS; [exact X0|]; cbn [csize]; replace (T + 2800 + Z.of_nat 8) with (T + 2808) by lia;
          apply CONS; [exact X1|]; cbn [csize]; replace (T + 2808 + Z.of_nat 8) with (T + 2816) by lia; exact X2|].
  split; [exists x13; exact X13|].
  destruct (stk_split ctasegs m (T + 2768) (T + 2912) (T + 3168) St' ltac:(lia)) as [_ X].
  destruct (stk_CB_pm m (T + 2912) 256 ltac:(replace (T + 2912 + 256) with (T + 3168) by lia; exact X) ltac:(lia)) as (bs & Hb).
  exists (ma_dec64 32 bs). split; [apply ma_rw_cells_u64arr; exact Hb | apply ma_dec64_length].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)


(* [comment removed for export] *)
Lemma sub_stack_pm : forall a b, l_ACEIL L <= a -> b <= B + -48 -> sub_fp [(a, b)] W_tail_pm.
Proof.
  intros a b H1 H2 x Hx. cbn [outside]. split; [|exact I]. intros Hy.
  exact (not_outside W_tail_pm (l_ACEIL L) (B + -48) x ltac:(unfold W_tail_pm; right; right; left; reflexivity) ltac:(lia) Hx).
Qed.

(* [comment removed for export] *)
Ltac piece k Hx := let Hy := fresh "Hy" in intros Hy;
  eapply (not_outside W_tail_pm _ _ _ (nth_error_In W_tail_pm k eq_refl)); [|exact Hx]; cbn [fst snd]; lia.

Lemma tl_fp_pm : from_primary n = true.
Proof using Hn En.
  clear - Hn En. unfold from_primary, needed, rounded. apply Z.leb_le.
  assert (RZ6 : rz_size n <= 1024).
  { unfold rz_size, rz_log. destruct (n <=? 48); [apply Z.leb_le; reflexivity|]. destruct (n <=? 96); [apply Z.leb_le; reflexivity|].
    destruct (n <=? 448); [apply Z.leb_le; reflexivity|]. destruct (n <=? 3968); [apply Z.leb_le; reflexivity|].
    destruct (n <=? 16128); [apply Z.leb_le; reflexivity|]. destruct (n <=? 32256); [apply Z.leb_le; reflexivity|].
    destruct (n <=? 64512) eqn:E6; [apply Z.leb_le; reflexivity | apply Z.leb_gt in E6; lia]. }
  assert ((Z.max (Z.max n 1) 8 + 7) / 8 < 8065) by (apply Z.div_lt_upper_bound; lia). lia.
Qed.

(* [comment removed for export] *)
Lemma tl_p3b_pm : forall (m6 : mem) (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 ra0 s0v s6v s9v s3v : word)
    (j0 h0 : list byte) (b1 : Z) (ctx : word),
  munch W_tail_pm mX m6 -> wmono ctasegs mX m6 -> mem_inv ctasegs m6 -> stk ctasegs m6 lo (B + -176) ->
  af_cells_pm m6 j0 -> 0 <= b1 < 256 -> b1 mod 4 = 1 ->
  rw_cells ctasegs m6 (AB + rz_size n + -16) [CB 1 h0; C1 (Z_to_bv 8 b1); C2 (Z_to_bv 64 0); C4 (Z_to_bv 64 n); C8 ctx] ->
  bytes_at ctasegs m6 (shad (AB + rz_size n)) (ushadow n) -> bytes_at ctasegs m6 (shad AB) (farun (rz_size n / 8)) ->
  bytes_at ctasegs m6 (shad (AB + rz_size n + ru8 n)) (farun ((S - rz_size n - ru8 n) / 8)) ->
  depot_rep (fst (depot_put D tr)) BK DNB SSB m6 ->
  pc_cells m6 (pc_addr T c) (Z.of_nat (length (ca Σ c)) - 1) (MaxCount c) (ClassSize c) ->
  evt ctasegs tail_post_pm (MS (mkR ra0 (Z_to_bv 64 (B + -176)) gp (Z_to_bv 64 tpA) t0 t1 t2 s0v (Z_to_bv 64 n) a0 a1 a2 a3 a4 a5 a6 a7
                             (Z_to_bv 64 AB) s3v (Z_to_bv 64 (AB + rz_size n)) (Z_to_bv 64 (AB + rz_size n + -16)) s6v
                             (Z_to_bv 64 (B)) (Z_to_bv 64 0) s9v (Z_to_bv 64 T) (Z_to_bv 64 1) t3 t4 t5 t6)
                         F (Z_to_bv 64 0x19c3c8) fc None m6 (seg_rom ctasegs)).
Proof using HA Hn En Hca LOW LOR SPT SPA Htrl.
  intros m6 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 ra0 s0v s6v s9v s3v j0 h0 b1 ctx MU WM MI ST AF Hb1 Hb4 HD US RZ1 RZ2 DR PC.
  pose proof tl_geo_pm as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12 & G13 & G14 & G15 & G16 & G17 & G18 & G19 & G20 & G21).
  pose proof tl_cls_pm as (K1 & K2 & K3 & K4 & K5 & K6 & _ & K8 & _). pose proof tl_room_pm as (R1 & R2 & R3 & R4 & R5).
  pose proof (tl_chunk_stk_pm m6 WM) as CH.
  assert (CH2 : stk ctasegs m6 (AB + rz_size n) (AB + rz_size n + Z.min n 4096)).
  { pose proof (proj2 (stk_split ctasegs m6 AB (AB + rz_size n) (AB + S) CH ltac:(lia))) as X.
    exact (proj1 (stk_split ctasegs m6 (AB + rz_size n) (AB + rz_size n + Z.min n 4096) (AB + S) X ltac:(lia))). }
  destruct (stk_CB_pm m6 (AB + rz_size n) (Z.min n 4096) CH2 ltac:(lia)) as (uj & UJ).
  destruct (stk_CB_pm m6 AB 16 ltac:(apply (proj1 (stk_split ctasegs m6 AB (AB + 16) (AB + S) CH ltac:(lia)))) ltac:(lia)) as (lj & LJ).
  destruct (tl_static_pm m6 MU WM) as (_ & _ & _ & SS & GAF & F44 & F52 & _ & TP16 & G9a & MFH & _).
  destruct AF as (AF & J0).
  assert (RS : 0 <= B + -176 < 2 ^ 64) by (unfold SHB in *; lia).
  eapply evt_mono.
  { apply (allocate_p3b_spec_pm (Z_to_bv 64 (B + -176)) gp ra0 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 s0v s6v s9v s3v
             (Z_to_bv 64 0x19c9e4) s0A s1A s2A s3A s4A s5A s6A s7A s8A s9A s10A s11A F fc m6 n AB (B) T lo b1 h0 uj lj j0 ctx);
      rewrite ?unsigned_lit by exact RS; try assumption; try (intros _; exact LJ);
      unfold kHighShadowEnd, kHighMemEnd, K_HIGH_SHADOW_hi, SHB in *; lia. }
  intros ms (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m7 & -> & MU7 & WM7 & MI7 & HD7 & UJ7 & LCH7 & ST7).
  rewrite unsigned_lit in MU7, ST7 by exact RS. rewrite sp_off_pm by exact RS.
  replace (B + -176 + 128) with (B + -48) in * by lia.
  assert (D7 : forall a k, (a + k <= AB \/ AB + S <= a) -> (a + k <= B + -208 \/ B + -48 <= a) ->
               disjoint_from [(AB, AB + 16); (AB + rz_size n + -16, AB + rz_size n + Z.min n 4096); (B + -176 - 32, B + -48)] a k).
  { intros a k H1 H2. cbn [disjoint_from]. split; [lia|]. split; [lia|]. split; [lia | exact I]. }
  assert (DSH : forall a k, shad AB <= a -> a + k <= shad AB + S / 8 ->
               disjoint_from [(AB, AB + 16); (AB + rz_size n + -16, AB + rz_size n + Z.min n 4096); (B + -176 - 32, B + -48)] a k).
  { intros a k H1 H2. pose proof tl_shad_pm as (S1 & S2 & S3). apply D7; unfold SHB, K_HIGH_SHADOW_hi in *; lia. }
  exists m7. split; [exists t0', t1', t2', a1', a2', a3', a4', a5', a6', a7', t3', t4', t5', t6', F, fc; reflexivity|].
  split.
  { apply (munch_into_pm _ _ mX m6 m7 MU MU7). intros x Hx. cbn [outside]. split; [piece 3%nat Hx|]. split; [piece 3%nat Hx|].
    split; [piece 2%nat Hx | exact I]. }
  split; [exact (wmono_trans ctasegs _ _ _ WM WM7)|]. split; [exact MI7|]. split; [exact ST7|].
  pose proof tl_apart_pm as (A02 & _ & A06 & A07 & _). pose proof tl_dep_pm as (_ & _ & OK' & _).
  unfold apart in *. split; [exists (Z_to_bv 8 (Z.land b1 243)), ctx; split; [exact (land243_mod4_pm b1 Hb1 Hb4) | exact HD7]|].
  split; [intros Hr; exact (LCH7 Hr)|].
  assert (FL : forall k, 0 <= k -> Z.of_nat (length (farun k)) = k) by (intros k Hk; unfold farun; rewrite repeat_length; lia).
  pose proof tl_shadows_pm as (E1 & E2 & _ & E4 & _).
  split; [apply (bytes_at_transport ctasegs _ m6 m7 _ _ US MU7); apply DSH; [rewrite E1; lia | rewrite E1, R3; lia]|].
  split; [apply (bytes_at_transport ctasegs _ m6 m7 _ _ RZ1 MU7); apply DSH; [lia | rewrite FL by lia; lia]|].
  split; [apply (bytes_at_transport ctasegs _ m6 m7 _ _ RZ2 MU7); apply DSH; [rewrite E2; lia|];
          rewrite E2, FL by (apply Z.div_pos; lia); pose proof tl_rr_pm as (Hrr0 & _); lia|].
  split; [apply (dep_frame_far_pm _ _ _ _ m6 m7 DR OK' MU7 WM7); cbn [far_all_pm];
          split; [apply dep_far_chunk_pm; lia|]; split; [apply dep_far_chunk_pm; lia|]; split; [apply dep_far_stk_pm; lia | exact I]|].
  apply (rw_cells_transport ctasegs _ m6 m7 _ _ PC MU7 WM7). cbn [cells_size csize Nat.add]. apply D7; unfold pc_addr; pose proof tl_cls_pm as (K1' & _); sep_fast.
Qed.

(* [comment removed for export] *)
Lemma tl_p3a_pm : forall (m5 : mem) (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 ra0 : word)
    (j0 h0 : list byte) (b1 : Z) (ctx : word),
  munch W_tail_pm mX m5 -> wmono ctasegs mX m5 -> mem_inv ctasegs m5 -> stk ctasegs m5 lo (B + -176) ->
  af_cells_pm m5 j0 -> 0 <= b1 < 256 -> b1 mod 4 = 1 ->
  rw_cells ctasegs m5 (AB + rz_size n + -16) [CB 1 h0; C1 (Z_to_bv 8 b1); C2 (Z_to_bv 64 0); C4 (Z_to_bv 64 n); C8 ctx] ->
  bytes_at ctasegs m5 (shad (AB + rz_size n)) (zrun (size_rd n / 8)) -> bytes_at ctasegs m5 (shad AB) (farun (rz_size n / 8)) ->
  bytes_at ctasegs m5 (shad (AB + rz_size n + ru8 n)) (farun ((S - rz_size n - ru8 n) / 8)) ->
  depot_rep (fst (depot_put D tr)) BK DNB SSB m5 ->
  pc_cells m5 (pc_addr T c) (Z.of_nat (length (ca Σ c)) - 1) (MaxCount c) (ClassSize c) ->
  evt ctasegs tail_post_pm (MS (mkR ra0 (Z_to_bv 64 (B + -176)) gp (Z_to_bv 64 tpA) t0 t1 t2 (Z_to_bv 64 1) (Z_to_bv 64 n) a0 a1 a2 a3 a4 a5 a6 a7
                             (Z_to_bv 64 AB) (Z_to_bv 64 (needed2 n + 64)) (Z_to_bv 64 (AB + rz_size n)) (Z_to_bv 64 (AB + rz_size n + -16))
                             (Z_to_bv 64 (size_rd n)) (Z_to_bv 64 (B)) (Z_to_bv 64 0) (Z_to_bv 64 (AB + rz_size n + n))
                             (Z_to_bv 64 T) (Z_to_bv 64 1) t3 t4 t5 t6)
                         F (Z_to_bv 64 0x19c1d4) fc None m5 (seg_rom ctasegs)).
Proof using HA Hn En Hca LOW LOR SPT SPA Htrl.
  intros m5 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 ra0 j0 h0 b1 ctx MU WM MI ST AF Hb1 Hb4 HD ZR RZ1 RZ2 DR PC.
  pose proof tl_geo_pm as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12 & G13 & G14 & G15 & G16 & G17 & G18 & G19 & G20 & G21).
  pose proof tl_cls_pm as (K1 & K2 & K3 & K4 & K5 & K6 & _ & K8 & _). pose proof tl_room_pm as (R1 & R2 & R3 & R4 & R5).
  pose proof tl_shadows_pm as (E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8). pose proof (size_rd_facts_pm n ltac:(lia)) as (D1 & D2 & D3).
  pose proof tl_shad_pm as (S1 & S2 & S3). pose proof (tl_shadow_stk_pm m5 WM) as SST.
  destruct (tl_static_pm m5 MU WM) as (TC & M2S & _ & _ & GAF & _ & _ & F85 & _ & _ & _ & CP & _ & _).
  assert (S8 : 0 <= size_rd n / 8) by (apply Z.div_pos; lia). assert (U8 : 0 <= ru8 n / 8) by (apply Z.div_pos; lia).
  assert (PBx : exists pb : byte, n mod 8 <> 0 -> rw_cells ctasegs m5 (shad (AB + rz_size n + size_rd n)) [C1 pb]).
  { destruct (Z.eq_dec (n mod 8) 0) as [Hm0|Hm0]; [exists (Z_to_bv 8 0); intros X; contradiction|].
    pose proof (E7 Hm0) as X7.
    assert (SP1 : stk ctasegs m5 (shad AB + rz_size n / 8 + size_rd n / 8) (shad AB + S / 8))
      by exact (proj2 (stk_split ctasegs m5 (shad AB) (shad AB + rz_size n / 8 + size_rd n / 8) (shad AB + S / 8) SST ltac:(lia))).
    destruct (rw_C1_of_pm m5 (shad (AB + rz_size n + size_rd n))
                ltac:(rewrite E3; exact (proj1 (stk_split ctasegs m5 _ (shad AB + rz_size n / 8 + size_rd n / 8 + 1) _ SP1 ltac:(lia)))))
      as (pb & PB).
    exists pb. intros _. exact PB. }
  destruct PBx as (pb & PB).
  destruct AF as (AF & J0).
  assert (RS : 0 <= B + -176 < 2 ^ 64) by (unfold SHB in *; lia).
  eapply evt_cut.
  { apply (allocate_p3a_spec_pm (Z_to_bv 64 (B + -176)) gp ra0 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 (Z_to_bv 64 1) (Z_to_bv 64 (AB + rz_size n + n))
             (Z_to_bv 64 0x19c9e4) s0A s1A s2A s3A s4A s5A s6A s7A s8A s9A s10A s11A F fc m5 n AB (B) TCX T lo pb);
      rewrite ?unsigned_lit by exact RS; try assumption; try exact PB; try exact (tl_p3stats_pm m5 WM);
      unfold kHighShadowEnd, kHighMemEnd in *; sep_fast. }
  intros ms (ra' & t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & s6' & m6 & -> & MU6 & WM6 & MI6 & SC6 & PB6 & ST6).
  rewrite unsigned_lit in MU6, ST6 by exact RS. rewrite E3 in MU6, PB6.
  set (PW := if n mod 8 =? 0 then 0 else 1) in MU6.
  assert (HPW : 0 <= PW <= 1 /\ (n mod 8 = 0 -> PW = 0) /\ (n mod 8 <> 0 -> PW = 1)).
  { unfold PW. destruct (Z.eqb_spec (n mod 8) 0); lia. }
  clearbody PW. destruct HPW as (PW1 & PW2 & PW3).
  assert (D6 : forall a k, 0 <= k -> (a + k <= shad AB + rz_size n / 8 + size_rd n / 8 \/ shad AB + rz_size n / 8 + size_rd n / 8 + PW <= a) ->
               (a + k <= T + 2800 \/ T + 3168 <= a) -> (a + k <= B + -176 - 32 \/ B + -176 <= a) ->
               disjoint_from [(shad AB + rz_size n / 8 + size_rd n / 8, shad AB + rz_size n / 8 + size_rd n / 8 + PW); (T + 2800, T + 2824);
                              (T + 2904, T + 2912 + 256); (B + -176 - 32, B + -176)] a k).
  { intros a k Hk H1 H2 H3. cbn [disjoint_from]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia | exact I]. }
  assert (TSH : forall a k, shad AB <= a -> a + k <= shad AB + S / 8 -> (a + k <= T + 2800 \/ T + 3168 <= a)).
  { intros a k H1 H2. sep_fast. }
  assert (USH : bytes_at ctasegs m6 (shad (AB + rz_size n)) (ushadow n)).
  { pose proof (bytes_at_transport ctasegs _ m5 m6 _ _ ZR MU6) as ZR6.
    assert (Lz : Z.of_nat (length (zrun (size_rd n / 8))) = size_rd n / 8) by (unfold zrun; rewrite repeat_length; lia).
    rewrite Lz in ZR6. specialize (ZR6 ltac:(rewrite E1; apply D6; [lia | lia | apply TSH; lia | lia])).
    assert (E8' : size_rd n / 8 = n / 8) by (unfold size_rd; rewrite Z.mul_comm, Z.div_mul by lia; reflexivity).
    unfold ushadow. unfold zrun in ZR6. rewrite E8' in ZR6. destruct (Z.eqb_spec (n mod 8) 0) as [Hm|Hm].
    - rewrite app_nil_r. exact ZR6.
    - apply bytes_at_app. split; [exact ZR6|]. rewrite repeat_length, Z2Nat.id by (apply Z.div_pos; lia). rewrite E1.
      destruct (PB6 Hm) as [[_ Hb] _]. cbn [cells_bytes cbytes] in Hb. rewrite app_nil_r in Hb. rewrite <- E8'. exact Hb. }
  assert (FL : forall k, 0 <= k -> Z.of_nat (length (farun k)) = k) by (intros k Hk; unfold farun; rewrite repeat_length; lia).
  pose proof tl_rr_pm as (Hrr & _).
  assert (DSH : forall a k, 0 <= k -> shad AB <= a -> a + k <= shad AB + S / 8 ->
               (a + k <= shad AB + rz_size n / 8 + size_rd n / 8 \/ shad AB + rz_size n / 8 + size_rd n / 8 + PW <= a) ->
               disjoint_from [(shad AB + rz_size n / 8 + size_rd n / 8, shad AB + rz_size n / 8 + size_rd n / 8 + PW); (T + 2800, T + 2824);
                              (T + 2904, T + 2912 + 256); (B + -176 - 32, B + -176)] a k).
  { intros a k Hk H1 H2 H3. apply D6; [lia | exact H3 | apply (TSH a k H1 H2) | unfold SHB in *; lia]. }
  assert (DCH : forall a k, 0 <= k -> AB <= a -> a + k <= AB + S ->
               disjoint_from [(shad AB + rz_size n / 8 + size_rd n / 8, shad AB + rz_size n / 8 + size_rd n / 8 + PW); (T + 2800, T + 2824);
                              (T + 2904, T + 2912 + 256); (B + -176 - 32, B + -176)] a k).
  { intros a k Hk H1 H2. pose proof tl_apart_pm as (A02 & _). unfold apart, K_HIGH_SHADOW_hi, SHB in *. apply D6; [lia | lia | lia | lia]. }
  apply (tl_p3b_pm m6 t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' ra' (Z_to_bv 64 1) s6' (Z_to_bv 64 (AB + rz_size n + n))
           (Z_to_bv 64 (needed2 n + 64)) j0 h0 b1 ctx).
  - apply (munch_into_pm _ _ mX m5 m6 MU MU6). intros x Hx. cbn [outside]. split; [piece 4%nat Hx|]. split; [piece 1%nat Hx|].
    split; [piece 1%nat Hx|]. split; [piece 2%nat Hx | exact I].
  - exact (wmono_trans ctasegs _ _ _ WM WM6).
  - exact MI6.
  - exact ST6.
  - apply (af_transport_pm _ m5 m6 _ (conj AF J0) MU6 WM6). apply D6; sep_fast.
  - exact Hb1.
  - exact Hb4.
  - apply (rw_cells_transport ctasegs _ m5 m6 _ _ HD MU6 WM6). cbn [cells_size csize Nat.add]. apply DCH; lia.
  - exact USH.
  - apply (bytes_at_transport ctasegs _ m5 m6 _ _ RZ1 MU6). rewrite FL by (apply Z.div_pos; lia). apply DSH; lia.
  - apply (bytes_at_transport ctasegs _ m5 m6 _ _ RZ2 MU6). rewrite FL by (apply Z.div_pos; lia). rewrite E2. apply DSH; [lia | lia | lia |].
    right. destruct (Z.eqb_spec (n mod 8) 0) as [Hm|Hm]; [rewrite (PW2 Hm), (E8 Hm); lia | rewrite (PW3 Hm), <- (E7 Hm); lia].
  - pose proof tl_dep_pm as (_ & _ & OK' & _).
    apply (dep_frame_far_pm _ _ _ _ m5 m6 DR OK' MU6 WM6). cbn [far_all_pm].
    split; [apply dep_far_shad_pm; lia|]. split; [apply dep_far_T_pm; lia|]. split; [apply dep_far_T_pm; lia|]. split; [apply dep_far_stk_pm; lia | exact I].
  - apply (rw_cells_transport ctasegs _ m5 m6 _ _ PC MU6 WM6). cbn [cells_size csize Nat.add]. unfold pc_addr. pose proof tl_cls_pm as (K1' & _).
    apply D6; sep_fast.
Qed.

(* [comment removed for export] *)
Lemma tl_ps_pm : forall (m4 : mem) (t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word)
    (j0 h0 : list byte) (b1 : Z) (ctx : word),
  8 <= n ->
  munch W_tail_pm mX m4 -> wmono ctasegs mX m4 -> mem_inv ctasegs m4 -> stk ctasegs m4 lo (B + -176) ->
  af_cells_pm m4 j0 -> 0 <= b1 < 256 -> b1 mod 4 = 1 ->
  rw_cells ctasegs m4 (AB + rz_size n + -16) [CB 1 h0; C1 (Z_to_bv 8 b1); C2 (Z_to_bv 64 0); C4 (Z_to_bv 64 n); C8 ctx] ->
  bytes_at ctasegs m4 (shad AB) (farun (rz_size n / 8)) ->
  bytes_at ctasegs m4 (shad (AB + rz_size n + ru8 n)) (farun ((S - rz_size n - ru8 n) / 8)) ->
  depot_rep (fst (depot_put D tr)) BK DNB SSB m4 ->
  pc_cells m4 (pc_addr T c) (Z.of_nat (length (ca Σ c)) - 1) (MaxCount c) (ClassSize c) ->
  evt ctasegs tail_post_pm (MS (mkR (Z_to_bv 64 0x19c1d4) (Z_to_bv 64 (B + -176)) gp (Z_to_bv 64 tpA) t0 t1 t2 (Z_to_bv 64 1) (Z_to_bv 64 n)
                             (Z_to_bv 64 (AB + rz_size n)) (Z_to_bv 64 (size_rd n)) (Z_to_bv 64 0) a3 a4 a5 a6 a7
                             (Z_to_bv 64 AB) (Z_to_bv 64 (needed2 n + 64)) (Z_to_bv 64 (AB + rz_size n)) (Z_to_bv 64 (AB + rz_size n + -16))
                             (Z_to_bv 64 (size_rd n)) (Z_to_bv 64 (B)) (Z_to_bv 64 0) (Z_to_bv 64 (AB + rz_size n + n))
                             (Z_to_bv 64 T) (Z_to_bv 64 1) t3 t4 t5 t6)
                         F (Z_to_bv 64 ps_entry) fc None m4 (seg_rom ctasegs)).
Proof using HA Hn En Hca LOW LOR SPT SPA Htrl.
  intros m4 t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6 j0 h0 b1 ctx H8 MU WM MI ST AF Hb1 Hb4 HD RZ1 RZ2 DR PC.
  pose proof tl_geo_pm as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12 & G13 & G14 & G15 & G16 & G17 & G18 & G19 & G20 & G21).
  pose proof tl_cls_pm as (K1 & K2 & K3 & K4 & K5 & K6 & _ & K8 & _). pose proof tl_room_pm as (R1 & R2 & R3 & R4 & R5).
  pose proof tl_shadows_pm as (E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8). pose proof (size_rd_facts_pm n ltac:(lia)) as (D1 & D2 & D3).
  pose proof tl_shad_pm as (S1 & S2 & S3). pose proof (tl_shadow_stk_pm m4 WM) as SST.
  destruct (tl_static_pm m4 MU WM) as (_ & _ & PSC & _).
  assert (S8 : 1 <= size_rd n / 8) by (unfold size_rd; rewrite Z.mul_comm, Z.div_mul by lia; apply Z.div_le_lower_bound; lia).
  destruct (stk_CB_pm m4 (shad (AB + rz_size n)) (size_rd n / 8)
              ltac:(rewrite E1; apply (proj1 (stk_split ctasegs m4 _ (shad AB + rz_size n / 8 + size_rd n / 8) _
                    (proj2 (stk_split ctasegs m4 (shad AB) (shad AB + rz_size n / 8) _ SST ltac:(lia))) ltac:(lia)))) ltac:(lia))
    as (shj & SHJ).
  assert (RS : 0 <= B + -176 < 2 ^ 64) by (unfold SHB in *; lia).
  assert (PSA : ps_args_ok (AB + rz_size n) (size_rd n)).
  { unfold ps_args_ok. split; [split; [rewrite Z.add_mod, (mod8_of AB 16 ltac:(lia) G3 ltac:(exists 2; reflexivity)),
                                      (mod8_of (rz_size n) 16 ltac:(lia) ltac:(exact (rz_size_mod16 n)) ltac:(exists 2; reflexivity)) by lia; reflexivity|]|].
    - split; [exact D1 | lia].
    - right. unfold kHighShadowEnd, kHighMemEnd, K_HIGH_SHADOW_hi in *. lia. }
  assert (S8u : size_rd n / 8 < 0x10000) by (apply Z.div_lt_upper_bound; lia).
  eapply evt_cut.
  { apply (poison_small_spec (Z_to_bv 64 0x19c1d4) (Z_to_bv 64 (B + -176)) gp (Z_to_bv 64 tpA) t0 t1 t2 (Z_to_bv 64 1) (Z_to_bv 64 n)
             a3 a4 a5 a6 a7 (Z_to_bv 64 AB) (Z_to_bv 64 (needed2 n + 64)) (Z_to_bv 64 (AB + rz_size n)) (Z_to_bv 64 (AB + rz_size n + -16))
             (Z_to_bv 64 (size_rd n)) (Z_to_bv 64 (B)) (Z_to_bv 64 0) (Z_to_bv 64 (AB + rz_size n + n)) (Z_to_bv 64 T) (Z_to_bv 64 1)
             t3 t4 t5 t6 F fc m4 (AB + rz_size n) (size_rd n) 0 lo shj); rewrite ?unsigned_lit by exact RS; try assumption;
      first [ right; exact S8u | unfold kHighShadowEnd, SHB in *; lia ]. }
  intros ms (t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m5 & -> & MU5 & WM5 & MI5 & ZR5 & ST5).
  rewrite unsigned_lit in MU5, ST5 by exact RS. rewrite (ret_pc_even 0x19c1d4) by (lia || reflexivity). rewrite E1 in MU5, ZR5.
  assert (D5 : forall a k, 0 <= k -> (a + k <= shad AB + rz_size n / 8 \/ shad AB + rz_size n / 8 + size_rd n / 8 <= a) ->
               (a + k <= B + -176 - 64 \/ B + -176 <= a) ->
               disjoint_from [(shad AB + rz_size n / 8, shad AB + rz_size n / 8 + size_rd n / 8); (B + -176 - 64, B + -176)] a k).
  { intros a k Hk H1 H2. cbn [disjoint_from]. split; [lia|]. split; [lia | exact I]. }
  assert (FL : forall k, 0 <= k -> Z.of_nat (length (farun k)) = k) by (intros k Hk; unfold farun; rewrite repeat_length; lia).
  pose proof tl_rr_pm as (Hrr & _).
  assert (DFAR : forall a k, 0 <= k -> (a + k <= shad AB + rz_size n / 8 \/ shad AB + rz_size n / 8 + size_rd n / 8 <= a) ->
               a + k <= l_ACEIL L -> disjoint_from [(shad AB + rz_size n / 8, shad AB + rz_size n / 8 + size_rd n / 8); (B + -176 - 64, B + -176)] a k).
  { intros a k Hk H1 H2. apply D5; [lia | lia | left; lia]. }
  apply (tl_p3a_pm m5 t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' (Z_to_bv 64 0x19c1d4) j0 h0 b1 ctx).
  - apply (munch_into_pm _ _ mX m4 m5 MU MU5). intros x Hx. cbn [outside]. split; [piece 4%nat Hx|]. split; [piece 2%nat Hx | exact I].
  - exact (wmono_trans ctasegs _ _ _ WM WM5).
  - exact MI5.
  - exact ST5.
  - apply (af_transport_pm _ m4 m5 _ AF MU5 WM5). apply D5; [lia | unfold SHB in *; lia | lia].
  - exact Hb1.
  - exact Hb4.
  - apply (rw_cells_transport ctasegs _ m4 m5 _ _ HD MU5 WM5). cbn [cells_size csize Nat.add]. apply DFAR; [lia | unfold SHB, K_HIGH_SHADOW_hi in *; lia | lia].
  - rewrite E1. destruct ZR5 as [[_ Hb] _]. cbn [cells_bytes cbytes] in Hb. rewrite app_nil_r in Hb. exact Hb.
  - apply (bytes_at_transport ctasegs _ m4 m5 _ _ RZ1 MU5). rewrite FL by (apply Z.div_pos; lia). apply DFAR; lia.
  - apply (bytes_at_transport ctasegs _ m4 m5 _ _ RZ2 MU5). rewrite FL by (apply Z.div_pos; lia). rewrite E2. apply DFAR; lia.
  - pose proof tl_dep_pm as (_ & _ & OK' & _). pose proof tl_apart_pm as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & DS & BS).
    apply (dep_frame_far_pm _ _ _ _ m4 m5 DR OK' MU5 WM5). cbn [far_all_pm].
    split; [apply dep_far_shad_pm; lia|]. split; [apply dep_far_stk_pm; lia | exact I].
  - apply (rw_cells_transport ctasegs _ m4 m5 _ _ PC MU5 WM5). cbn [cells_size csize Nat.add]. unfold pc_addr. pose proof tl_cls_pm as (K1' & _).
    apply D5; sep_fast.
Qed.

(* [comment removed for export] *)
Lemma tl_p2P_pm : forall (m3 : mem) (ra' t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word)
    (j0 h0 : list byte) (b1 : Z) (ctx : word),
  munch W_tail_pm mX m3 -> wmono ctasegs mX m3 -> mem_inv ctasegs m3 -> stk ctasegs m3 lo (B + -176) ->
  af_cells_pm m3 j0 -> 0 <= b1 < 256 -> b1 mod 4 = 1 ->
  rw_cells ctasegs m3 (AB + rz_size n + -16) [CB 1 h0; C1 (Z_to_bv 8 b1); C2 (Z_to_bv 64 0); C4 (Z_to_bv 64 n); C8 ctx] ->
  bytes_at ctasegs m3 (shad AB) (farun (rz_size n / 8)) ->
  bytes_at ctasegs m3 (shad (AB + rz_size n + ru8 n)) (farun ((S - rz_size n - ru8 n) / 8)) ->
  depot_rep (fst (depot_put D tr)) BK DNB SSB m3 ->
  pc_cells m3 (pc_addr T c) (Z.of_nat (length (ca Σ c)) - 1) (MaxCount c) (ClassSize c) ->
  evt ctasegs tail_post_pm (MS (mkR ra' (Z_to_bv 64 (B + -176)) gp (Z_to_bv 64 tpA) t0 t1 t2 (Z_to_bv 64 1) (Z_to_bv 64 n) a0 a1 a2 a3 a4 a5 a6 a7
                             (Z_to_bv 64 AB) (Z_to_bv 64 (needed2 n + 64)) (Z_to_bv 64 (AB + rz_size n)) (Z_to_bv 64 (AB + rz_size n + -16))
                             (Z_to_bv 64 INST) (Z_to_bv 64 (B)) (Z_to_bv 64 0) (Z_to_bv 64 (AB + rz_size n + n))
                             (Z_to_bv 64 T) (Z_to_bv 64 1) t3 t4 t5 t6)
                         F (Z_to_bv 64 0x19c0d8) fc None m3 (seg_rom ctasegs)).
Proof using HA Hn En Hca LOW LOR SPT SPA Htrl.
  intros m3 ra' t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 j0 h0 b1 ctx MU WM MI ST AF Hb1 Hb4 HD RZ1 RZ2 DR PC.
  pose proof tl_geo_pm as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12 & G13 & G14 & G15 & G16 & G17 & G18 & G19 & G20 & G21).
  pose proof tl_cls_pm as (K1 & K2 & K3 & K4 & K5 & K6 & _ & K8 & _). pose proof tl_shadows_pm as (E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8).
  pose proof (tl_shadow_stk_pm m3 WM) as SST. pose proof tl_shad_pm as (S1 & S2 & S3).
  assert (S8p : 2 <= S / 8) by (apply Z.div_le_lower_bound; lia).
  destruct (tl_static_pm m3 MU WM) as (_ & (M1 & M2 & _) & _).
  assert (M1' : rw_cells ctasegs m3 0x5a9238 [C8 (Z_to_bv 64 0x672038)]) by exact (rw_cells_app_l_pm m3 _ [C8 (Z_to_bv 64 0x672038)] _ M1).
  assert (SB0 : rw_cells ctasegs m3 (shad AB) [C1 (Z_to_bv 8 K_kAsanHeapLeftRedzoneMagic)]).
  { destruct (rw_C1_of_pm m3 (shad AB) ltac:(apply (proj1 (stk_split ctasegs m3 _ (shad AB + 1) _ SST ltac:(lia))))) as (b & Hb).
    destruct Hb as [[Hw Hb] R]. split; [split; [exact Hw|] | exact R].
    unfold farun in RZ1. replace (Z.to_nat (rz_size n / 8)) with (Datatypes.S (Z.to_nat (rz_size n / 8) - 1)) in RZ1 by lia.
    cbn [repeat] in RZ1. cbn [cells_bytes cbytes app]. apply (bytes_at_app ctasegs m3 _ [_] _) in RZ1 as [X _]. exact X. }
  assert (RS : 0 <= B + -176 < 2 ^ 64) by (unfold SHB in *; lia).
  eapply evt_cut.
  { apply (allocate_p2P_spec (Z_to_bv 64 (B + -176)) gp (Z_to_bv 64 tpA) t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 ra' F fc m3 n AB
             (B) T lo (Z_to_bv 8 K_kAsanHeapLeftRedzoneMagic) (Z_to_bv 64 (needed2 n + 64))); rewrite ?unsigned_lit by exact RS; try assumption;
      try (unfold K_kAsanHeapLeftRedzoneMagic; rewrite Z_to_bv_unsigned; cbn; discriminate);
      unfold kHighShadowEnd, K_HIGH_SHADOW_hi in *; lia. }
  intros ms (m4 & HS & MU4 & WM4 & MI4 & _ & ST4).
  assert (MUe : munch W_tail_pm mX m4) by (apply (munch_into_pm _ _ mX m3 m4 MU MU4); intros x _; exact I).
  assert (TR : forall a cs, rw_cells ctasegs m3 a cs -> rw_cells ctasegs m4 a cs) by (intros a cs H; exact (rw_cells_transport ctasegs [] m3 m4 _ _ H MU4 WM4 I)).
  assert (TB' : forall a bs, bytes_at ctasegs m3 a bs -> bytes_at ctasegs m4 a bs) by (intros a bs H; exact (bytes_at_transport ctasegs [] m3 m4 _ _ H MU4 I)).
  assert (AF4 : af_cells_pm m4 j0) by exact (af_transport_pm [] m3 m4 j0 AF MU4 WM4 I).
  assert (DR4 : depot_rep (fst (depot_put D tr)) BK DNB SSB m4).
  { pose proof tl_dep_pm as (_ & _ & OK' & _). exact (depot_rep_frame _ _ _ _ _ [] m3 m4 DR OK' MU4 WM4 I I I I I I). }
  destruct (8 <=? n) eqn:E8n.
  - apply Z.leb_le in E8n. destruct HS as (t0' & t1' & t2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & ->).
    rewrite unsigned_lit in ST4 by lia.
    exact (tl_ps_pm m4 t0' t1' t2' a3' a4' a5' a6' a7' t3' t4' t5' t6' j0 h0 b1 ctx E8n MUe (wmono_trans ctasegs _ _ _ WM WM4) MI4 ST4
             AF4 Hb1 Hb4 (TR _ _ HD) (TB' _ _ RZ1) (TB' _ _ RZ2) DR4 (TR _ _ PC)).
  - apply Z.leb_gt in E8n. destruct HS as (ra'' & t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & ->).
    rewrite unsigned_lit in ST4 by lia.
    assert (Hz0 : size_rd n = 0) by (unfold size_rd; rewrite Z.div_small by lia; reflexivity).
    eapply evt_eq; [| apply (tl_p3a_pm m4 t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' ra'' j0 h0 b1 ctx MUe
                               (wmono_trans ctasegs _ _ _ WM WM4) MI4 ST4 AF4 Hb1 Hb4 (TR _ _ HD) ltac:(rewrite Hz0; apply bytes_at_nil; unfold SHB in *; lia)
                               (TB' _ _ RZ1) (TB' _ _ RZ2) DR4 (TR _ _ PC))].
    rewrite Hz0. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma tl_p2a_pm : forall (m2 : mem) (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (tb : list word) (j0 : list byte),
  munch W_tail_pm mX m2 -> wmono ctasegs mX m2 -> mem_inv ctasegs m2 -> stk ctasegs m2 lo (B + -176) ->
  af_cells_pm m2 j0 -> trc_cells_pm m2 tb ->
  bytes_at ctasegs m2 (shad AB) (farun (S / 8)) -> depot_rep D BK DNB SSB m2 ->
  pc_cells m2 (pc_addr T c) (Z.of_nat (length (ca Σ c)) - 1) (MaxCount c) (ClassSize c) ->
  evt ctasegs tail_post_pm (MS (mkR (Z_to_bv 64 0x19bfbc) (Z_to_bv 64 (B + -176)) gp (Z_to_bv 64 tpA) t0 t1 t2
                             (Z_to_bv 64 (Z.b2z (from_primary n))) (Z_to_bv 64 n) (Z_to_bv 64 AB) a1 a2 a3 a4 a5 a6 a7
                             (Z_to_bv 64 64) (Z_to_bv 64 (needed2 n + 64)) (Z_to_bv 64 (rz_size n)) (Z_to_bv 64 n) (Z_to_bv 64 INST)
                             (Z_to_bv 64 (B)) (Z_to_bv 64 (-64)) (Z_to_bv 64 63) (Z_to_bv 64 T) (Z_to_bv 64 1) t3 t4 t5 t6)
                         F (Z_to_bv 64 0x19bfbc) fc None m2 (seg_rom ctasegs)).
Proof using HA Hn En Hca LOW LOR SPT SPA Htr Htrl.
  intros m2 t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 tb j0 MU WM MI ST AF IC SH DR PC.
  pose proof tl_geo_pm as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12 & G13 & G14 & G15 & G16 & G17 & G18 & G19 & G20 & G21).
  pose proof tl_cls_pm as (K1 & K2 & K3 & K4 & K5 & K6 & K7 & K8 & K9). pose proof tl_room_pm as (R1 & R2 & R3 & R4 & R5).
  pose proof tl_shadows_pm as (E1 & E2 & E3 & E4 & E5 & E6 & _ & _). pose proof tl_shad_pm as (S1 & S2 & S3).
  pose proof tl_dep_pm as (OK & DI & OK' & DN2 & DT).
  destruct (tl_static_pm m2 MU WM) as (TC & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & TX8 & TT0).
  pose proof (tl_chunk_stk_pm m2 WM) as CH.
  destruct (stk_CB_pm m2 (AB + rz_size n - 16) 16 ltac:(apply (proj1 (stk_split ctasegs m2 _ (AB + rz_size n - 16 + 16) _
              (proj2 (stk_split ctasegs m2 AB (AB + rz_size n - 16) _ CH ltac:(lia))) ltac:(lia)))) ltac:(lia)) as (hdr & HD).
  (* [comment removed for export] *)
  assert (FL : forall k, 0 <= k -> Z.of_nat (length (farun k)) = k) by (intros k Hk; unfold farun; rewrite repeat_length; lia).
  pose proof tl_rr_pm as (Hrr & _).
  assert (U8 : 0 <= ru8 n / 8) by (apply Z.div_pos; lia).
  assert (SPL : farun (S / 8) = farun (rz_size n / 8) ++ farun (ru8 n / 8) ++ farun ((S - rz_size n - ru8 n) / 8)).
  { unfold farun. rewrite <- !repeat_app. f_equal. rewrite Hrr. clear - E4 E6 U8. lia. }
  rewrite SPL in SH. apply bytes_at_app in SH as [RZ1 SH]. rewrite FL in SH by (apply Z.div_pos; lia).
  apply bytes_at_app in SH as [_ RZ2]. rewrite FL in RZ2 by lia.
  assert (RZ2' : bytes_at ctasegs m2 (shad (AB + rz_size n + ru8 n)) (farun ((S - rz_size n - ru8 n) / 8))) by (rewrite E2; replace (shad AB + rz_size n / 8 + ru8 n / 8) with (shad AB + rz_size n / 8 + ru8 n / 8) by lia; exact RZ2).
  clear RZ2. rename RZ2' into RZ2.
  destruct IC as (I6 & I4 & HTB).
  assert (I6' : rw_cells ctasegs m2 (B) [C8 (Z_to_bv 64 (B + 16)); C8 (Z_to_bv 64 (Z.of_nat (length (map (Z_to_bv 64) tr))))])
    by (rewrite map_length; exact I6).
  assert (I4' : u64arr ctasegs m2 (B + 16) (map (Z_to_bv 64) tr ++ skipn (length tr) tb))
    by exact I4.
  assert (RS : 0 <= B + -176 < 2 ^ 64) by (unfold SHB in *; lia).
  pose proof (T_MAIN_range_pm tr Htr) as TRR.
  assert (HBK : In (bkt (depot_hash (map bv_unsigned (map (Z_to_bv 64) tr)))) BK).
  { rewrite (map_unsigned_lit_pm tr TRR). unfold DEP_BK. right. apply in_map_iff. exists tr. split; [reflexivity | exact Htr]. }
  eapply evt_cut.
  { apply (allocate_p2a_spec_cf_pm (Z_to_bv 64 (B + -176)) gp (Z_to_bv 64 tpA) t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6
             (Z_to_bv 64 0x19c9e4) s0A s1A s2A s3A s4A s5A s6A s7A s8A s9A s10A s11A F fc m2 n AB (B) TCX T lo hdr D BK DNB SSB
             (map (Z_to_bv 64) tr) (skipn (length tr) tb)); rewrite ?unsigned_lit by exact RS.
    - lia.
    - unfold K_HIGH_SHADOW_hi in *. lia.
    - exact tl_AB64_pm.
    - exact En.
    - lia.
    - exact HD.
    - exact (proj1 AF).
    - exact TT0.
    - exact TX8.
    - exact I6'.
    - exact I4'.
    - rewrite app_length, map_length, skipn_length. lia.
    - rewrite map_length. lia.
    - apply (depot_ok_mono_pm _ _ _ _ _ OK). lia.
    - exact DR.
    - rewrite map_length. exact DT.
    - exact HBK.
    - exact DN2.
    - exact ST.
    - lia.
    - lia.
    - lia.
    - pose proof tl_apart_pm as (A02 & _). unfold apart in A02. destruct A02; lia.
    - pose proof tl_apart_pm as (_ & A03 & _). unfold apart in A03. destruct A03; lia.
    - pose proof tl_apart_pm as (_ & _ & A06 & _). unfold apart in A06. destruct A06; lia.
    - pose proof tl_apart_pm as (_ & _ & _ & A07 & _). unfold apart in A07. destruct A07; lia.
    - lia.
    - lia.
    - pose proof tl_apart_pm as (_ & _ & _ & _ & _ & A26 & _). unfold apart in A26. destruct A26; lia.
    - pose proof tl_apart_pm as (_ & _ & _ & _ & _ & _ & A27 & _). unfold apart in A27. destruct A27; lia.
    - pose proof tl_apart_pm as (_ & _ & _ & _ & _ & _ & _ & A36 & _). unfold apart in A36. destruct A36; lia.
    - pose proof tl_apart_pm as (_ & _ & _ & _ & _ & _ & _ & _ & A37 & _). unfold apart in A37. destruct A37; lia.
    - pose proof tl_apart_pm as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & TP & _). unfold SEGTOP_A in TP. exact TP.
    - pose proof tl_apart_pm as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & XP & _). unfold SEGTOP_A in XP. destruct XP; lia.
    - exact MI. }
  intros ms (ra' & t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m3 & -> & MU3 & WM3 & MI3 & HD3 & DR3 & TB3 & ST3).
  rewrite unsigned_lit in MU3, ST3 by exact RS. rewrite (map_unsigned_lit_pm tr TRR) in HD3, DR3. rewrite tl_fp_pm.
  pose proof (hb1_props_pm (hdr_b1 hdr) (hdr_b1_range_pm hdr)) as (HB1 & HB4).
  assert (D3 : forall a k, 0 <= k -> (a + k <= AB + rz_size n + -16 \/ AB + rz_size n <= a) ->
               (a + k <= 0x743f08 \/ 0xb53f30 <= a) -> (a + k <= DNB \/ DNB + 2 ^ 20 <= a) -> (a + k <= SSB \/ SSB + 2 ^ 23 <= a) ->
               (a + k <= B + -176 - 224 \/ B + -176 <= a) ->
               disjoint_from [(AB + rz_size n + -16, AB + rz_size n); (d_tab, d_nuniq + 4); (d_map1, d_map1 + 8); (DNB, DNB + 2 ^ 20);
                              (s_total, s_total + 8); (s_data0, s_stored0 + 4); (SSB, SSB + 2 ^ 23); (B + -176 - 224, B + -176)] a k).
  { intros a k Hk H1 H2 H3 H4 H5. cbn [disjoint_from]. split; [exact H1|]. split; [clear H1 H3 H4 H5; destruct H2; lia|].
    split; [clear H1 H3 H4 H5; destruct H2; lia|]. split; [exact H3|]. split; [clear H1 H3 H4 H5; destruct H2; lia|].
    split; [clear H1 H3 H4 H5; destruct H2; lia|]. split; [exact H4|]. split; [exact H5 | exact I]. }
  assert (DSH : forall a k, 0 <= k -> shad AB <= a -> a + k <= shad AB + S / 8 ->
               disjoint_from [(AB + rz_size n + -16, AB + rz_size n); (d_tab, d_nuniq + 4); (d_map1, d_map1 + 8); (DNB, DNB + 2 ^ 20);
                              (s_total, s_total + 8); (s_data0, s_stored0 + 4); (SSB, SSB + 2 ^ 23); (B + -176 - 224, B + -176)] a k).
  { intros a k Hk H1 H2. pose proof tl_apart_pm as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & DS & BS).
    apply D3; [lia | unfold K_HIGH_SHADOW_hi, SHB in *; lia | unfold SHB in *; lia | clear BS; unfold K_LOW_SHADOW_lo, K_HIGH_SHADOW_hi, SHB in *; destruct DS; lia
              | clear DS; unfold K_LOW_SHADOW_lo, K_HIGH_SHADOW_hi, SHB in *; destruct BS; lia | unfold SHB in *; lia]. }
  apply (tl_p2P_pm m3 ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' j0
           (firstn 1 hdr) (hb1_pm (hdr_b1 hdr)) (Z_to_bv 64 (snd (depot_put D tr)))).
  - apply (munch_into_pm _ _ mX m2 m3 MU MU3). intros x Hx. cbn [outside]. split; [piece 3%nat Hx|]. split; [piece 5%nat Hx|].
    split; [piece 6%nat Hx|]. split; [piece 7%nat Hx|]. split; [piece 8%nat Hx|]. split; [piece 9%nat Hx|]. split; [piece 10%nat Hx|].
    split; [piece 2%nat Hx | exact I].
  - exact (wmono_trans ctasegs _ _ _ WM WM3).
  - exact MI3.
  - exact ST3.
  - apply (af_transport_pm _ m2 m3 _ AF MU3 WM3). apply D3; unfold apart, K_HIGH_SHADOW_hi, SEGTOP_A in *; try lia.
  - exact HB1.
  - exact HB4.
  - exact HD3.
  - apply (bytes_at_transport ctasegs _ m2 m3 _ _ RZ1 MU3). rewrite FL by lia. apply DSH; lia.
  - apply (bytes_at_transport ctasegs _ m2 m3 _ _ RZ2 MU3). rewrite FL by (apply Z.div_pos; lia). rewrite E2. apply DSH; lia.
  - exact DR3.
  - apply (rw_cells_transport ctasegs _ m2 m3 _ _ PC MU3 WM3). cbn [cells_size csize Nat.add]. unfold pc_addr in *.
    pose proof tl_cls_pm as (K1' & _).
    apply D3; [lia | pose proof tl_apart_pm as (A02 & _); unfold apart in A02; destruct A02; lia
              | pose proof tl_apart_pm as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & TP & _); unfold SEGTOP_A in TP; destruct TP; lia
              | pose proof tl_apart_pm as (_ & _ & _ & _ & _ & A26 & _); unfold apart in A26; destruct A26; lia
              | pose proof tl_apart_pm as (_ & _ & _ & _ & _ & _ & A27 & _); unfold apart in A27; destruct A27; lia | lia].
Qed.

End Tail.
