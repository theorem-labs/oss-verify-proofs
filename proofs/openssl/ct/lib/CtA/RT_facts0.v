(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtLib Require Import ImageCtA.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Monad Specs Run Fs.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require Import MState Mem Frame Cells Step Arr Exec RzCPS. 
From OssFuzzTheorems.Proofs.openssl.ct.lib.AS Require Import AsanAcct.
From OssFuzzTheorems.Proofs.openssl.ct.lib.AS Require BackingAlgebra.
From OssFuzzTheorems.Proofs.openssl.ct.lib.A Require Import Shadow R_sizeclass.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtA Require Import Layout RT_iface R_cache_defs R_prim_defs R_depot_defs R_fs_defs R_glue_defs R_m2s R_poison RT_state RT_rep.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma rta_client_consts : forall Σ m, ART_A Σ m -> client_consts m.
Proof. intros Σ m H. exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (ART_consts Σ m H)))))))). Qed.

Lemma rta_with_fds : forall Σ mo fds, ARTM_A Σ mo -> ARTM_A Σ (with_fds fds mo).
Proof. intros Σ mo fds H. exact H. Qed.

Lemma rta_mat_stable : forall Σ, mat_stable (ARTM_A Σ).
Proof. intros Σ. unfold ARTM_A, artm_sys, lazy_in_maps_A, confined0, shadow_lazy, maps_zbound, BackingAlgebra.model_ivs_wf, NodesA_madv.noaccess_pos. mat_stable_tac. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma rta_sp0 : forall Σ m, ART_A Σ m -> sp_window_lo <= rtA_sp0 Σ <= sp_window_hi /\ rtA_sp0 Σ mod 16 = 0.
Proof.
  intros Σ m H. pose proof (ART_wf Σ m H) as (HL & _). unfold layout_ok in HL. destruct HL as (H1 & H2 & _). unfold rtA_sp0. split; assumption.
Qed.

Lemma rta_sp0_range : forall Σ m, ART_A Σ m -> SEGTOP_A + STACK_WIN <= rtA_sp0 Σ <= USTACK_TOP.
Proof. intros Σ m H. destruct (rta_sp0 Σ m H) as [[H1 H2] _]. unfold sp_window_lo, sp_window_hi, SEGTOP_A, STACK_WIN, USTACK_TOP in *. lia. Qed.

Lemma rta_sp0_win : forall Σ m, ART_A Σ m -> 0x7fff80000000 <= rtA_sp0 Σ.
Proof. intros Σ m H. destruct (rta_sp0 Σ m H) as [[H1 H2] _]. unfold sp_window_lo in *. lia. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma ClassSize_pos : forall c, 1 <= c <= 31 -> 0 < ClassSize c.
Proof.
  intros c Hc. unfold ClassSize. destruct (c =? 31); [lia|]. destruct (c <=? 16) eqn:H16; [lia|].
  assert (T : 512 <= Z.shiftl 512 ((c - 16) / 2)).
  { rewrite Z.shiftl_mul_pow2 by (apply Z.div_pos; lia). pose proof (Z.pow_pos_nonneg 2 ((c - 16) / 2) ltac:(lia) ltac:(apply Z.div_pos; lia)). nia. }
  assert (0 <= c mod 2) by (apply Z.mod_pos_bound; lia). assert (0 <= Z.shiftl 512 ((c - 16) / 2) / 2) by (apply Z.div_pos; lia). nia.
Qed.

Lemma rz_size_big : forall n, 64512 < n -> rz_size n = 2048.
Proof.
  intros n Hn. unfold rz_size, rz_log.
  rewrite (proj2 (Z.leb_gt n 48)), (proj2 (Z.leb_gt n 96)), (proj2 (Z.leb_gt n 448)), (proj2 (Z.leb_gt n 3968)),
          (proj2 (Z.leb_gt n 16128)), (proj2 (Z.leb_gt n 32256)), (proj2 (Z.leb_gt n 64512)) by lia. reflexivity.
Qed.

Lemma smsz_room : forall n, 64512 < n -> 4096 + 2048 + n <= smsz n.
Proof.
  intros n Hn. unfold smsz, needed, pg_up, rounded. rewrite rz_size_big by lia.
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). lia.
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Qed.

Lemma rta_live_range : forall Σ m p n, ART_A Σ m -> In (p, n) (live Σ) ->
  0 < p /\ p + n <= rtA_sp0 Σ - STACK_WIN /\ (p + n <= 0x10000 \/ SEGTOP_A <= p).
Proof.
  intros Σ m p n H Hin. pose proof (ART_wf Σ m H) as (HL & HR & HV & HS & _).
  destruct HV as (_ & _ & HVin & _). unfold rtA_sp0.
  destruct HL as (_ & _ & _ & _ & (P1 & P2 & P3 & P4 & P5) & _ & Hsb & _). unfold l_ACEIL in P3.
  unfold SEGTOP_A, STACK_WIN, K_LOW_SHADOW_lo, K_HIGH_SHADOW_hi in *.
  destruct (HVin p n Hin) as [(c & i & Hc & Hn & ->)|(s & Hs & Hq & <- & ->)].
  - destruct HR as (HR & _). pose proof (HR c Hc) as (W1 & W2 & W3 & W4 & W5 & W6 & W7 & W8 & W9 & W10 & _).
    pose proof (nth_error_In _ _ Hn) as Hi. pose proof (proj1 (Forall_forall _ _) W10 _ Hi) as (Hn0 & Hfit & _). cbv beta iota in Hn0, Hfit.
    pose proof (proj1 (nth_error_Some (r_st (pr Σ c)) i) ltac:(rewrite Hn; discriminate)) as Hlt.
    pose proof (ClassSize_pos c Hc) as Hcs. unfold p_ubeg, p_abeg, kUserCap in *.
    assert (Hm : Z.of_nat i * ClassSize c + ClassSize c <= ClassSize c * Z.of_nat (length (r_st (pr Σ c)))).
    { replace (ClassSize c * Z.of_nat (length (r_st (pr Σ c)))) with (Z.of_nat (length (r_st (pr Σ c))) * ClassSize c) by ring.
      replace (Z.of_nat i * ClassSize c + ClassSize c) with ((Z.of_nat i + 1) * ClassSize c) by ring.
      apply Z.mul_le_mono_nonneg_r; lia. }
    assert (Hx : 0 <= Z.of_nat i * ClassSize c) by (apply Z.mul_nonneg_nonneg; lia).
    assert (Hrz : 0 < rz_size n) by (unfold rz_size; pose proof (Z.pow_pos_nonneg 2 (rz_log n) ltac:(lia) ltac:(unfold rz_log; repeat destruct (_ <=? _); lia)); lia).
    split; [lia|]. split; [lia|]. right. lia.
  - destruct HS as (_ & _ & _ & HSF & _). pose proof (proj1 (Forall_forall _ _) HSF s Hs) as (Hsn & (G1 & G2 & G3 & G4 & G5) & _ & _).
    pose proof (smsz_room (s_n s) ltac:(lia)) as Hroom. unfold s_ubeg. unfold l_ACEIL, STACK_WIN in G3.
    unfold SEGTOP_A in G5. split; [lia|]. split; [lia|]. destruct G5 as [G5|G5]; [left; lia | right; lia].
Qed.

(* [comment removed for export] *)
Lemma rta_credit_nonneg : forall Σ m, ART_A Σ m -> 0 <= credit Σ.
Proof. intros Σ m H. pose proof (ART_wf Σ m H) as (_ & _ & _ & _ & _ & _ & (B1 & _) & _). exact B1. Qed.

(* [comment removed for export] *)
Lemma rta_live_offshadow : forall Σ m p n, ART_A Σ m -> In (p, n) (live Σ) -> p + n <= 0x7fff7000 \/ 0x10007fff8000 <= p.
Proof.
  intros Σ m p n H Hin. pose proof (ART_wf Σ m H) as (HL & HR & HV & HS & _).
  destruct HV as (_ & _ & HVin & _).
  destruct HL as (_ & _ & _ & _ & (P1 & P2 & P3 & P4 & P5) & _ & Hsb & _). unfold l_ACEIL in P3.
  unfold SEGTOP_A, STACK_WIN, K_LOW_SHADOW_lo, K_HIGH_SHADOW_hi in *.
  destruct (HVin p n Hin) as [(c & i & Hc & Hn & ->)|(s & Hs & Hq & <- & ->)].
  - destruct HR as (HR & _). pose proof (HR c Hc) as (W1 & W2 & W3 & W4 & W5 & W6 & W7 & W8 & W9 & W10 & _).
    pose proof (nth_error_In _ _ Hn) as Hi. pose proof (proj1 (Forall_forall _ _) W10 _ Hi) as (Hn0 & Hfit & _). cbv beta iota in Hn0, Hfit.
    pose proof (proj1 (nth_error_Some (r_st (pr Σ c)) i) ltac:(rewrite Hn; discriminate)) as Hlt.
    pose proof (ClassSize_pos c Hc) as Hcs. unfold p_ubeg, p_abeg, kUserCap in *.
    assert (Hm : Z.of_nat i * ClassSize c + ClassSize c <= ClassSize c * Z.of_nat (length (r_st (pr Σ c)))).
    { replace (ClassSize c * Z.of_nat (length (r_st (pr Σ c)))) with (Z.of_nat (length (r_st (pr Σ c))) * ClassSize c) by ring.
      replace (Z.of_nat i * ClassSize c + ClassSize c) with ((Z.of_nat i + 1) * ClassSize c) by ring.
      apply Z.mul_le_mono_nonneg_r; lia. }
    assert (Hx : 0 <= Z.of_nat i * ClassSize c) by (apply Z.mul_nonneg_nonneg; lia).
    assert (Hrz : 0 < rz_size n) by (unfold rz_size; pose proof (Z.pow_pos_nonneg 2 (rz_log n) ltac:(lia) ltac:(unfold rz_log; repeat destruct (_ <=? _); lia)); lia).
    lia.
  - destruct HS as (_ & _ & _ & HSF & _). pose proof (proj1 (Forall_forall _ _) HSF s Hs) as (Hsn & (G1 & G2 & G3 & G4 & G5) & _ & _).
    pose proof (smsz_room (s_n s) ltac:(lia)) as Hroom. unfold s_ubeg. unfold K_LOW_SHADOW_lo, K_HIGH_SHADOW_hi in G4. destruct G4 as [G4|G4]; [left; lia | right; lia].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma ro_of_rw : forall (m : mem) a cs, rw_cells ctasegs m a cs -> ro_cells ctasegs m a cs.
Proof. intros m a cs [H _]. exact H. Qed.

Lemma ro_head : forall (m : mem) a c cs, ro_cells ctasegs m a (c :: cs) -> ro_cells ctasegs m a [c].
Proof.
  intros m a c cs [[Hw1 Hw2] Hb]. split; [split; [exact Hw1 | exact I]|]. cbn [cells_bytes] in *. rewrite app_nil_r.
  apply bytes_at_app in Hb as [Hb _]. exact Hb.
Qed.



(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma rta_frame_in : forall Σ m f k, ART_A Σ m -> In (f, k) (frames Σ) ->
  (k = 0%nat \/ k = 1%nat \/ k = 2%nat \/ k = 3%nat \/ k = 4%nat) /\ l_FSB (lay Σ) + 0x9000 <= f /\ f + fs_size k <= l_FSB (lay Σ) + 0xb09000.
Proof.
  intros Σ m f k H Hin. pose proof (ART_wf Σ m H) as (_ & _ & _ & _ & _ & HF & _). destruct HF as (_ & _ & _ & HF & _).
  pose proof (proj1 (Forall_forall _ _) HF (f, k) Hin) as (Hk & (p & Hp & Hf & _)). cbn [fst snd] in *. split; [exact Hk|].
  unfold frame_addr, fs_size, fsz, NF in *. rewrite Z.shiftl_mul_pow2 by lia. subst f.
  destruct Hk as [Hk | [Hk | [Hk | [Hk | Hk]]]]; subst k.
  - change (Z.of_nat 0) with 0 in *. change (2 ^ (14 - 0)) with 16384 in Hp. change (64 * 2 ^ 0) with 64. lia.
  - change (Z.of_nat 1) with 1 in *. change (2 ^ (14 - 1)) with 8192 in Hp. change (64 * 2 ^ 1) with 128. lia.
  - change (Z.of_nat 2) with 2 in *. change (2 ^ (14 - 2)) with 4096 in Hp. change (64 * 2 ^ 2) with 256. lia.
  - change (Z.of_nat 3) with 3 in *. change (2 ^ (14 - 3)) with 2048 in Hp. change (64 * 2 ^ 3) with 512. lia.
  - change (Z.of_nat 4) with 4 in *. change (2 ^ (14 - 4)) with 1024 in Hp. change (64 * 2 ^ 4) with 1024. lia.
Qed.

Lemma rta_live_fshadow : forall Σ m p n f k, ART_A Σ m -> In (p, n) (live Σ) -> In (f, k) (frames Σ) ->
  p + n <= shad f \/ shad (f + fs_size k) <= p.
Proof.
  intros Σ m p n f k H Hp Hf. pose proof (ART_wf Σ m H) as (HL & _ & HV & HS & _).
  destruct (rta_frame_in Σ m f k H Hf) as (_ & F1 & F2).
  pose proof (rta_live_range Σ m p n H Hp) as (L1 & L2 & L3).
  destruct HL as (_ & _ & _ & _ & (P1 & P2 & P3 & P4 & P5) & _ & Hsb & _ & _ & _ & _ & (Q1 & Q2 & Q3 & Q4 & Q5) & _).
  unfold l_ACEIL, STACK_WIN, K_LOW_SHADOW_lo, K_HIGH_SHADOW_hi, SEGTOP_A in *. unfold rtA_sp0 in L2.
  assert (Hfs : 0 <= f) by lia.
  pose proof (rta_sp0 Σ m H) as ((W1 & W2) & _). unfold rtA_sp0, sp_window_lo, sp_window_hi in W1, W2.
  destruct HV as (_ & _ & HVin & _).
  destruct (HVin p n Hp) as [(c & i & Hc & Hn & ->)|(s & Hs & Hq & <- & ->)].
  - (* [comment removed for export] *)
    right. destruct P4 as [P4|P4]; [lia|]. unfold p_ubeg, p_abeg, shad, SHB.
    assert (0 <= Z.of_nat i * ClassSize c) by (apply Z.mul_nonneg_nonneg; [lia | pose proof (ClassSize_pos c Hc); lia]).
    assert (0 < rz_size n) by (unfold rz_size; pose proof (Z.pow_pos_nonneg 2 (rz_log n) ltac:(lia) ltac:(unfold rz_log; repeat destruct (_ <=? _); lia)); lia).
    assert ((f + fs_size k) / 8 <= 2 ^ 44) by (apply Z.div_le_upper_bound; lia). lia.
  - destruct HS as (_ & _ & _ & HSF & _). pose proof (proj1 (Forall_forall _ _) HSF s Hs) as (Hsn & (G1 & G2 & G3 & G4 & G5) & _ & _).
    pose proof (smsz_room (s_n s) ltac:(lia)) as Hroom. unfold s_ubeg, shad, SHB. unfold K_LOW_SHADOW_lo, K_HIGH_SHADOW_hi in G4.
    assert (0 <= f / 8) by (apply Z.div_pos; lia). assert ((f + fs_size k) / 8 <= 2 ^ 44) by (apply Z.div_le_upper_bound; lia).
    destruct G4 as [G4|G4]; [left; lia | right; lia].
Qed.
