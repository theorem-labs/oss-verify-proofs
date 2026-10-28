(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import Sorting.Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame Arr Tac ITree Nodes Decode InitMem.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.LibA Require Import ExecF ITreeA StepF.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import STree AsanCtrl AsanEmbed.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.AsanT Require Import BImg ABase ADepot_iface ARep ARepQ ARepFrame ARepKit AFreeRep AQConst.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import RunDraw.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Notation Wf sp t UB gq nodes store lst eb gl :=
  ([(sp - 4096, sp); (0xcca08, 0xcca30); (0xd0f00, 0x151f30); (0x15f788, 0x15f78c); (ADEPOT_LO, ADEPOT_HI);
    (t + 80, t + 112); (t + 2128, t + 2132); (t + 2784, t + 2792); (t + 2800, t + 3169);
    (UB - 16, UB + 8); (shad UB, shad UB + gq);
    (nodes, nodes + 1048576); (store, store + 8388608);
    (lst, lst + qsz lst); (eb, eb + 8192); (gl, gl + 8)]%Z) (only parsing).      (* [comment removed for export] *)

(* [comment removed for export] *)
Local Lemma sclr_int : forall a n, sclr a n -> 0 <= a -> a + n <= 18446744073709551616 ->
  exists k, 0 <= k <= 1 /\ a + n <= 2147446784 + k * 18446744073709551616 /\ 17594333495296 * k <= a.
Proof. intros a n H G1 G2. unfold sclr, KLS in H. destruct H; [exists 0 | exists 1]; lia. Qed.
Local Lemma iclr_int : forall a n, iclr a n -> a + n <= 18446744073709551616 ->
  exists k, 0 <= k <= 1 /\ 4096 <= a /\ a + n <= 65536 + k * 18446744073709551616 /\ 6443008 * k <= a.
Proof. intros a n H G2. unfold iclr, AIMG_LO, AIMG_HI in H. destruct H as [? [?|?]]; [exists 0 | exists 1]; lia. Qed.
Local Lemma ablk_int {rc : runConstT} : forall lo hi, ablk lo hi ->
  exists k, 0 <= k <= 1 /\ 6443008 <= lo /\ 17594333495296 * k <= lo /\ hi <= 2147446784 + k * 18446744073709551616 /\ hi <= ATOP.
Proof. intros lo hi H. unfold ablk, KLS, AIMG_HI in H. pose proof atop_range. destruct H as [[? ?]|[? ?]]; [exists 0 | exists 1]; lia. Qed.
Local Ltac band_int H :=
  let k := fresh "k" H in let A := fresh "KA" H in let B := fresh "KB" H in let C := fresh "KC" H in let D := fresh "KD" H in
  let G1 := fresh "G" in let G2 := fresh "G" in
  lazymatch type of H with
  | sclr ?a ?n =>
      assert (G1 : 0 <= a) by (atop_facts; unfold AIMG_HI, AIMG_LO, KLS in *; lia); assert (G2 : a + n <= 18446744073709551616) by (atop_facts; unfold AIMG_HI, AIMG_LO, KLS in *; lia);
      destruct (sclr_int a n H G1 G2) as (k & A & B & C); clear G1 G2
  | iclr ?a ?n =>
      assert (G2 : a + n <= 18446744073709551616) by (atop_facts; unfold AIMG_HI, AIMG_LO, KLS in *; lia);
      destruct (iclr_int a n H G2) as (k & A & B & C & D); clear G2
  | 4096 <= ?a /\ (?a + ?n <= _ \/ _ <= ?a) =>      (* [comment removed for export] *)
      assert (G2 : a + n <= 18446744073709551616) by (atop_facts; unfold AIMG_HI, AIMG_LO, KLS in *; lia);
      destruct (iclr_int a n H G2) as (k & A & B & C & D); clear G2
  | ablk ?lo ?hi => let E := fresh "KE" H in destruct (ablk_int lo hi H) as (k & A & B & E & C & D)
  end.

Section CANSEC1. Context {rc : runConstT}.
Section Kinds.
Variables (sp t AB S UB gq nodes store res ctx lo grz ssz lst eb gl : Z).
Definition kfactsF : Prop :=
     (ATOP <= lo /\ lo <= sp - 4096)
  /\ (sclr t 4096 /\ iclr t 4096 /\ 4096 <= t /\ t + 4096 <= ATOP)      (* [comment removed for export] *)
  /\ (17594333495296 <= res /\ res + 137439023104 <= ATOP)      (* [comment removed for export] *)
  /\ (res + 4096 <= AB /\ AB + S <= res + 137439023104 /\ AB + 16 <= UB /\ UB + 8 <= AB + S)
  /\ (2201439137792 <= shad AB /\ shad UB = shad AB + grz /\ 2 <= grz /\ 1 <= gq /\ shad UB + gq <= shad AB + ssz
      /\ shad AB + ssz <= 17594333495296)
  /\ (sclr nodes 1048576 /\ 6443008 <= nodes /\ nodes + 1048576 <= ATOP /\ sclr store 8388608 /\ 6443008 <= store /\ store + 8388608 <= ATOP)   (* [comment removed for export] *)
  /\ (sclr ctx 65536 /\ 6443008 <= ctx /\ ctx + 65536 <= ATOP)   (* [comment removed for export] *)
  /\ ((lst = 0 /\ qsz lst = 8) \/ (res + 4096 <= lst /\ lst + 8192 <= res + 137439023104 /\ qsz lst = 8192))   (* [comment removed for export] *)
  /\ (res + 4096 <= eb /\ eb + 8192 <= res + 137439023104)      (* [comment removed for export] *)
  /\ (gl = 0 \/ (res + 4096 <= gl /\ gl + 8192 <= res + 137439023104)).
Hypothesis KF : kfactsF.

Ltac kind := pose proof KF as KF'; unfold kfactsF, AIMG_HI in *;
  destruct KF' as (F_lo & (Ft1 & Ft2 & Ft3 & Ft4) & F_res & F_slot & F_sh & (Fn1 & Fn2 & Fn3 & Fs1 & Fs2 & Fs3) & (Fc1 & Fc2 & Fc3) & F_lst & F_eb & F_gl);
  band_int Ft1; band_int Ft2; band_int Fn1; band_int Fs1; band_int Fc1; clear Ft1 Ft2 Fn1 Fs1 Fc1;   (* [comment removed for export] *)
  cbn [disjoint_from]; repeat (split; [lia|]); first [lia | exact I].

Lemma KF_img : forall A k, 0x10000 <= A -> 0 <= k ->
  (A + k <= ADEPOT_LO /\ (A + k <= 0xcca08 \/ 0xcca30 <= A) /\ (A + k <= 0xd0f00 \/ 0x151f30 <= A) /\ (A + k <= 0x15f788 \/ 0x15f78c <= A))
  \/ (ADEPOT_HI <= A /\ A + k <= AIMG_HI) ->
  disjoint_from (Wf sp t UB gq nodes store lst eb gl) A k.
Proof. intros. kind. Qed.

Lemma KF_low : forall A k, 2147450880 <= A -> A + k <= 2148256256 -> 0 <= k ->      (* [comment removed for export] *)
  disjoint_from (Wf sp t UB gq nodes store lst eb gl) A k.
Proof. intros. kind. Qed.

Lemma KF_hi : forall A k, sp <= A -> 0 <= k ->
  disjoint_from (Wf sp t UB gq nodes store lst eb gl) A k.
Proof. intros. kind. Qed.

Lemma KF_shad : forall A k, 2147446784 <= A -> A + k <= 17594333495296 -> 0 <= k ->      (* [comment removed for export] *)
  (A + k <= shad UB \/ shad UB + gq <= A) ->
  disjoint_from (Wf sp t UB gq nodes store lst eb gl) A k.
Proof. intros. kind. Qed.

Lemma KF_ctx :
  (ctx + 65536 <= t \/ t + 4096 <= ctx) -> (ctx + 65536 <= res \/ res + 137439023104 <= ctx) ->
  (ctx + 65536 <= nodes \/ nodes + 1048576 <= ctx) -> (ctx + 65536 <= store \/ store + 8388608 <= ctx) ->
  forall A k, ctx <= A -> A + k <= ctx + 65536 -> 0 <= k ->
  disjoint_from (Wf sp t UB gq nodes store lst eb gl) A k.
Proof. intros. kind. Qed.

Lemma KF_t :
  (t + 4096 <= res \/ res + 137439023104 <= t) -> (t + 4096 <= nodes \/ nodes + 1048576 <= t) -> (t + 4096 <= store \/ store + 8388608 <= t) ->
  forall A k, t <= A -> A + k <= t + 4096 -> 0 <= k ->
  (A + k <= t + 80 \/ t + 112 <= A) -> (A + k <= t + 2128 \/ t + 2132 <= A) -> (A + k <= t + 2784 \/ t + 2792 <= A) -> (A + k <= t + 2800 \/ t + 3169 <= A) ->
  disjoint_from (Wf sp t UB gq nodes store lst eb gl) A k.
Proof. intros. kind. Qed.

Lemma KF_res :
  (t + 4096 <= res \/ res + 137439023104 <= t) -> (nodes + 1048576 <= res \/ res + 137439023104 <= nodes) ->
  (store + 8388608 <= res \/ res + 137439023104 <= store) ->
  forall A k, res <= A -> A + k <= res + 137439023104 -> 0 <= k ->
  (A + k <= UB - 16 \/ UB + 8 <= A) ->
  (A + k <= lst \/ lst + 8192 <= A) -> (A + k <= eb \/ eb + 8192 <= A) -> (A + k <= gl \/ gl + 8 <= A) ->
  disjoint_from (Wf sp t UB gq nodes store lst eb gl) A k.
Proof. intros. kind. Qed.

Lemma KF_obj : forall A k, ((6443008 <= A /\ A + k <= 2147446784) \/ 17594333495296 <= A) -> A + k <= ATOP -> 0 <= k ->      (* [comment removed for export] *)
  (A + k <= t \/ t + 4096 <= A) -> (A + k <= res \/ res + 137439023104 <= A) ->
  (A + k <= nodes \/ nodes + 1048576 <= A) -> (A + k <= store \/ store + 8388608 <= A) ->
  disjoint_from (Wf sp t UB gq nodes store lst eb gl) A k.
Proof. intros. kind. Qed.
End Kinds.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section Frames.
Variables (L : alayout) (W : list (Z * Z)) (m m' : amem).
Hypothesis MU : munch W m m'.
Hypothesis WM : wmono bsegs m m'.

Lemma aslots_update_gen : forall st st' X X' c,
  aslots L st X m c ->
  ndist st' c = ndist st c ->
  c_allocated_user (get_cls st' c) = c_allocated_user (get_cls st c) ->
  c_mapped_user (get_cls st' c) = c_mapped_user (get_cls st c) ->
  (forall k, 0 <= k < ndist st c ->
       (busy_of X' c k = busy_of X c k /\ disjoint_from W (aslot_addr L c k) (size_of_class c)
          /\ (forall b, busy_of X c k = Some b -> xb_class b = c /\ xb_slot b = k /\ xb_fits b))
    \/ match busy_of X' c k with None => junk_at m' (aslot_addr L c k) (size_of_class c) | Some b => aslot_busy L m' b end) ->
  (0 < c_mapped_user (get_cls st c) - c_allocated_user (get_cls st c) ->
   disjoint_from W (aregion L c + c_allocated_user (get_cls st c)) (c_mapped_user (get_cls st c) - c_allocated_user (get_cls st c))) ->
  aslots L st' X' m' c.
Proof.
  intros st st' X X' c [SL UND] E0 E1 E2 OTH DU. unfold aslots. cbv zeta. rewrite E0, E1, E2. split.
  - intros k Hk. destruct (OTH k Hk) as [(EB & D & WFB)|NEW]; [| exact NEW].
    rewrite EB. specialize (SL k Hk). destruct (busy_of X c k) as [b|].
    + destruct (WFB b eq_refl) as (C1' & K1 & FIT1).
      eapply aslot_busy_frame; [exact MU| exact WM| exact SL | exact FIT1 |]. unfold xb_alloc. rewrite C1', K1. exact D.
    + eapply junk_frame; [exact SL | exact MU | exact WM | intros _; exact D].
  - eapply junk_frame; [exact UND | exact MU | exact WM | exact DU].
Qed.

Lemma aslot_shadow_update_gen : forall st st' X X' c,
  aslot_shadow L st X m c ->
  ndist st' c = ndist st c ->
  c_allocated_user (get_cls st' c) = c_allocated_user (get_cls st c) ->
  c_mapped_user (get_cls st' c) = c_mapped_user (get_cls st c) ->
  (forall k, 0 <= k < ndist st c ->
       (slot_shadow_bytes (size_of_class c) (busy_of X' c k) = slot_shadow_bytes (size_of_class c) (busy_of X c k)
          /\ disjoint_from W (shad (aslot_addr L c k)) (shlen (size_of_class c)))
    \/ rw_cells bsegs m' (shad (aslot_addr L c k)) [CB (Z.to_nat (shlen (size_of_class c))) (slot_shadow_bytes (size_of_class c) (busy_of X' c k))]) ->
  (0 < shlen (c_mapped_user (get_cls st c) - c_allocated_user (get_cls st c)) ->
   disjoint_from W (shad (aregion L c + c_allocated_user (get_cls st c))) (shlen (c_mapped_user (get_cls st c) - c_allocated_user (get_cls st c)))) ->
  0 <= shlen (size_of_class c) ->
  aslot_shadow L st' X' m' c.
Proof.
  intros st st' X X' c [SL UND] E0 E1 E2 OTH DU POS. unfold aslot_shadow. cbv zeta. rewrite E0, E1, E2. split.
  - intros k Hk. destruct (OTH k Hk) as [[EB D]|NEW]; [| exact NEW].
    rewrite EB. specialize (SL k Hk).
    eapply cells_frame; [exact SL| exact MU| exact WM |]. cbn [cells_size csize]. rewrite Nat.add_0_r, Z2Nat.id by exact POS. exact D.
  - eapply fill_frame; [exact UND | exact MU | exact WM | exact DU].
Qed.
End Frames.

(* [comment removed for export] *)
Lemma slot_shadow_bbatch : forall S k24,
  2 <= shlen S -> slot_shadow_bytes S (Some (bbatch k24)) = repeat (Z_to_bv 8 0xfa) (Z.to_nat (shlen S)).
Proof.
  intros S k24 H. unfold slot_shadow_bytes, bbatch. cbn [xb_n xb_st].
  replace (rz_size 0) with 16 by reflexivity. replace (shlen 16) with 2 by reflexivity. replace (granules 0) with 0 by reflexivity.
  rewrite <- !repeat_app. f_equal. lia.
Qed.
End CANSEC1.
