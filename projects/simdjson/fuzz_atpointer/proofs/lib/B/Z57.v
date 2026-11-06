(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.AS Require Import Zp7 Z1b.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.Lib Require Import Tac Arr Bytes ImageA RzCPS Z119 FP.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.Sj Require Import Zpf.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.Spec Require Import Prelim Stdio Zpb Z3o.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.P Require Import Zvw Z4d.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.A Require Import Shadow.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.B Require Import Layout Zks Zkt Zi4 D_defs D_kit D_clx Z87 Z82 I_lkit Sj_rtf Zpm Zpl Zq2 Zq3 Sj_new Zpt Zps Zpo Zwn Zsl Z4a Z73 Z5g Z6m Z71 Z5h Z5i Z5j Z6q Z6y Z6p Z4e Z4l Z4m Z4n Z52.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Definition doc_len (bs : list byte) : Z := zlength (atp_doc (chars bs)).
Definition doc_cap (bs : list byte) : Z := Z.max (doc_len bs) 32.

Lemma atp_elsA_shape : forall D d, exists P0 e1 rest,
  atp_elsA D d = (P0, zlength (atp_s0 d)) :: e1 :: rest /\ (P0 = 0 /\ atp_s0 d = [] \/ P0 = D + Z.of_nat 0) /\ atp_s0 d = firstn (length (atp_s0 d)) d.
Proof.
  intros D d. unfold atp_elsA, atp_P, atp_s0.
  pose proof (poffs_length d) as PL. pose proof (poffs_parts d) as PP.
  destruct (poffs d) as [|[o0 n0] tl] eqn:EP.
  - cbn in PP. rewrite <- PP. cbn. exists 0, (0, 0), []. split; [reflexivity|]. split; [left; split; reflexivity| reflexivity].
  - assert (O0 : o0 = 0%nat).
    { rewrite poffs_eq in EP. destruct d as [|c l]; [discriminate|]. rewrite poffs_of_unfold in EP. destruct (find_sep (c :: l)); congruence. }
    subst o0. rewrite <- PP. cbn [map nth fst snd skipn].
    assert (LN0 : (n0 <= length d)%nat) by (pose proof (poffs_bound d (0%nat, n0) ltac:(rewrite EP; left; reflexivity)) as B; cbn in B; lia).
    assert (ZL : zlength (firstn n0 d) = Z.of_nat n0) by (unfold zlength; rewrite length_firstn; lia).
    rewrite ZL. replace (length (firstn n0 d)) with n0 by (rewrite length_firstn; clear - LN0; lia).
    destruct tl as [|e1 tl'].
    + cbn [length Nat.max Nat.sub repeat map app pview fst snd]. do 3 eexists. split; [reflexivity|]. split; [right; reflexivity| reflexivity].
    + cbn [map app]. do 3 eexists. split; [reflexivity|]. split; [right; reflexivity| reflexivity].
Qed.

Lemma firstn_chars : forall k (bs : list byte), firstn k (chars bs) = chars (firstn k bs).
Proof. intros k bs. unfold chars. rewrite firstn_map. reflexivity. Qed.

Lemma atp_s0_bytes : forall bs, exists bs0 : list byte, atp_s0 (chars bs) = chars bs0 /\ bs0 = firstn (length bs0) bs /\ (length bs0 <= length bs)%nat.
Proof.
  intros bs. destruct (atp_elsA_shape 0 (chars bs)) as (P0 & e1 & rest & _ & _ & E).
  exists (firstn (length (atp_s0 (chars bs))) bs). rewrite firstn_chars in E. split; [exact E|].
  rewrite length_firstn. split; [| lia]. f_equal. rewrite E at 1. unfold chars. rewrite length_map, firstn_length. lia.
Qed.

Lemma padded_bytes_chars : forall bs0 : list byte, padded_bytes (map bv_unsigned bs0) = bs0 ++ repeat z8 64.
Proof.
  intros bs0. unfold padded_bytes. f_equal. change (zbytes (map bv_unsigned bs0)) with (to_bytes (chars bs0)). apply to_bytes_chars.
Qed.

Lemma pid_costA_bound : forall len, 0 <= len <= 1048512 -> pid_costA len <= 2^27.
Proof.
  intros len H. unfold pid_costA, pid_cost6, S2A_COST, NUMA_CREDIT.
  set (cap := Z.max len 32). assert (C : 32 <= cap <= 1048512) by lia.
  pose proof (al_sbuf_bounds cap ltac:(lia)) as B1. pose proof (al_tape_bounds cap ltac:(lia)) as B2. pose proof (sc_idx_bounds cap ltac:(lia)) as B3.
  assert (U1 : al_sbuf cap <= 2 * 1048512) by (unfold al_sbuf, roundup64; Z.div_mod_to_equations; lia).
  assert (U2 : al_tape cap <= 9 * 1048512) by (unfold al_tape, roundup64; Z.div_mod_to_equations; lia).
  assert (U3 : sc_idx cap <= 5 * 1048512) by (unfold sc_idx, roundup64; Z.div_mod_to_equations; lia).
  pose proof (mcost_le (al_sbuf cap) ltac:(lia)). pose proof (mcost_le (al_tape cap) ltac:(lia)). pose proof (mcost_le (sc_idx cap) ltac:(lia)).
  pose proof (mcost_le 96 ltac:(lia)). pose proof (mcost_le 8192 ltac:(lia)). pose proof (mcost_le 1024 ltac:(lia)). pose proof (mcost_le (len + 64) ltac:(lia)).
  lia.
Qed.

Lemma pid_costA_nonneg : forall len, 0 <= len -> 0 <= pid_costA len.
Proof.
  intros len H. unfold pid_costA, pid_cost6, S2A_COST, NUMA_CREDIT.
  pose proof (al_sbuf_bounds (Z.max len 32)). pose proof (al_tape_bounds (Z.max len 32)). pose proof (sc_idx_bounds (Z.max len 32)).
  destruct (Z.le_gt_cases (Z.max len 32) (2^26)).
  - repeat match goal with |- context [mcost ?n] => lazymatch goal with H : 0 <= mcost n |- _ => fail | _ => pose proof (mcost_nonneg n ltac:(lia)) end end. lia.
  - unfold mcost, DCOST. repeat match goal with |- context [if ?c then _ else _] => destruct c end; unfold al_sbuf, al_tape, sc_idx, roundup64 in *; Z.div_mod_to_equations; lia.
Qed.

Lemma live_remove_comm : forall p q (l : list (Z * Z)), live_remove p (live_remove q l) = live_remove q (live_remove p l).
Proof.
  intros p q l. induction l as [|e l IH]; [reflexivity|]. rewrite !live_remove_cons'.
  destruct (fst e =? q) eqn:Eq; destruct (fst e =? p) eqn:Ep; rewrite ?live_remove_cons', ?Eq, ?Ep, IH; reflexivity.
Qed.

Section Kit.
Variable RT : rt_sig.
Variable LIB : mem -> Prop.
Hypothesis LIB_loc : fp_local LIB_FP LIB.
Hypothesis AF : art_facts RT.

Local Ltac ul := unfold FUZZ_STACK, ATPA_SPLITINTO_STACK, ATPA_SPLIT_STACK, ATPA_PUSH_STACK, PID_STACK in *; unfold SEGTOP_A, STACK_WIN, USTACK_TOP, RT_STACK in *; lia.

Lemma LIB_agree2 : forall m m', LIB m -> agree_on (in_ranges LIB_FP) m m' -> LIB m'.
Proof using LIB_loc. intros m m' H AG. apply (LIB_loc m m' H). intros a Ha. apply AG. exact Ha. Qed.

Definition lp_inv (Σ Σx : rts RT) (m mx : mem) (usp sp' f lo d : Z) (bs : list byte) (ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
    (h3 t : list byte) (A : Z) : Prop :=
  ART RT Σx mx /\ mem_inv bsegs mx /\ stk bsegs mx lo sp'
  /\ (exists j0 j1 j2 j4 jq je jo jn jr j13, rw_cells bsegs mx sp' (fa_locals2 j0 j1 j2 f j4 jq je jo jn jr (d + Z.of_nat (length bs)) j13))
  /\ stk bsegs mx (sp' + 184) (usp - 104)
  /\ rw_cells bsegs mx (usp - 104) (fa_saved ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11)
  /\ rw_cells bsegs mx f (fz_hdr (C8 (Z_to_bv 64 0x41b58ab3)) (C8 (Z_to_bv 64 0x1e816)) (C8 (Z_to_bv 64 0x96ab0)) h3)
  /\ rw_cells bsegs mx (f / 8 + 2147450880) (fa_shadow2 t)
  /\ vrepA mx (f + 32) A (vcap_iter (atp_P (chars bs)) 0 0) (Z.of_nat (atp_P (chars bs))) (atp_elsA d (chars bs))
  /\ bytes_at bsegs mx d bs /\ LIB mx
  /\ rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) usp LIB_FP m mx
  /\ rt_frames RT Σx = [(f, 2%nat)] /\ rt_sp0 RT Σx = rt_sp0 RT Σ.

Definition lp_rng (usp sp' f A d : Z) (bs : list byte) (x : Z) : Prop :=
  (sp' <= x < usp) \/ (f <= x < f + 56) \/ (f / 8 + 2147450880 <= x < f / 8 + 2147450880 + 32)
  \/ (A <= x < A + 16 * Z.of_nat (atp_P (chars bs))) \/ (d <= x < d + Z.of_nat (length bs)) \/ in_ranges LIB_FP x.

Definition lp_dom (Σ : rts RT) (usp sp' f A d : Z) (bs : list byte) (x : Z) : Prop :=
  lp_rng usp sp' f A d bs x \/ (aclient (rt_live RT Σ) (rt_frames RT Σ) usp x /\ outside LIB_FP x).

Lemma lp_inv_xfer : forall Σ Σx Σy m mx my usp sp' f lo d bs ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 h3 t A,
  lp_inv Σ Σx m mx usp sp' f lo d bs ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 h3 t A ->
  sp' + 288 <= usp ->
  rt_frames RT Σy = rt_frames RT Σx -> rt_sp0 RT Σy = rt_sp0 RT Σx ->
  ART RT Σy my -> mem_inv bsegs my -> stk bsegs my lo sp' ->
  agree_on (lp_rng usp sp' f A d bs) mx my ->
  (forall a : word, aclient (rt_live RT Σ) (rt_frames RT Σ) usp (bv_unsigned a) -> outside LIB_FP (bv_unsigned a) -> my a = mx a) ->
  lp_inv Σ Σy m my usp sp' f lo d bs ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 h3 t A.
Proof using LIB_loc.
  intros until A. intros INV GEO FRS SP ARTy MIy STy AG PR.
  destruct INV as (_ & _ & _ & (j0 & j1 & j2 & j4 & jq & je & jo & jn & jr & j13 & L1) & L2 & L3 & L4 & L5 & VR & BS & LB & PRES & FRSx & SPx).
  unfold lp_inv. split; [exact ARTy|]. split; [exact MIy|]. split; [exact STy|].
  split. { exists j0, j1, j2, j4, jq, je, jo, jn, jr, j13. apply (rw_cells_agree_nw bsegs mx my _ _ L1). eapply agree_sub; [exact AG|].
           intros x Hx. unfold fa_locals2 in Hx. cbn [cells_size csize Nat.add] in Hx. unfold lp_rng. left. lia. }
  split. { apply (stk_agree_nw bsegs mx my _ _ L2). eapply agree_sub; [exact AG|]. intros x Hx. cbv beta in Hx. unfold lp_rng. left. lia. }
  split. { apply (rw_cells_agree_nw bsegs mx my _ _ L3). eapply agree_sub; [exact AG|]. intros x Hx. unfold fa_saved in Hx. cbn [cells_size csize Nat.add] in Hx.
           unfold lp_rng. left. lia. }
  split. { apply (rw_cells_agree_nw bsegs mx my _ _ L4). eapply agree_sub; [exact AG|]. intros x Hx. unfold fz_hdr in Hx. cbn [cells_size csize Nat.add] in Hx.
           unfold lp_rng. right; left. lia. }
  split. { apply (rw_cells_agree_nw bsegs mx my _ _ L5). eapply agree_sub; [exact AG|]. intros x Hx. unfold fa_shadow2 in Hx.
           cbn [map app repeat cells_size csize Nat.add] in Hx. unfold lp_rng. right; right; left. lia. }
  split. { destruct VR as (E & R & C & A0 & AH & SV & BLK). unfold vrepA. split; [exact E|]. split; [exact R|]. split; [exact C|]. split; [exact A0|]. split; [exact AH|].
           split. { apply (rw_cells_agree_nw bsegs mx my _ _ SV). eapply agree_sub; [exact AG|]. intros x Hx. cbn [cells_size csize Nat.add] in Hx. unfold lp_rng. right; left. lia. }
           destruct BLK as [B|(C1 & A16 & ASG & EL)]; [left; exact B| right]. split; [exact C1|]. split; [exact A16|]. split; [exact ASG|].
           apply (rw_cells_agree_nw bsegs mx my _ _ EL). eapply agree_sub; [exact AG|]. intros x Hx. rewrite velts_size, atp_elsA_length in Hx.
           unfold lp_rng. right; right; right; left. lia. }
  split. { apply (bytes_at_agree bsegs mx my _ _ BS). eapply agree_sub; [exact AG|]. intros x Hx. cbv beta in Hx. unfold lp_rng. do 4 right. left. exact Hx. }
  split. { apply (LIB_agree2 mx my LB). eapply agree_sub; [exact AG|]. intros x Hx. unfold lp_rng. do 5 right. exact Hx. }
  split. { intros a Ha Hout. rewrite (PR a Ha Hout). exact (PRES a Ha Hout). }
  split; [rewrite FRS; exact FRSx| rewrite SP; exact SPx].
Qed.

Lemma lp_inv_xfer' : forall Σ Σx Σy m mx my usp sp' f lo d bs ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 h3 t A,
  lp_inv Σ Σx m mx usp sp' f lo d bs ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 h3 t A ->
  sp' + 288 <= usp ->
  rt_frames RT Σy = rt_frames RT Σx -> rt_sp0 RT Σy = rt_sp0 RT Σx ->
  ART RT Σy my -> mem_inv bsegs my -> stk bsegs my lo sp' ->
  (forall a : word, lp_dom Σ usp sp' f A d bs (bv_unsigned a) -> my a = mx a) ->
  lp_inv Σ Σy m my usp sp' f lo d bs ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 h3 t A.
Proof using LIB_loc.
  intros until A. intros INV GEO FRS SP ARTy MIy STy EQ.
  apply (lp_inv_xfer Σ Σx Σy m mx my usp sp' f lo d bs ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 h3 t A INV GEO FRS SP ARTy MIy STy).
  - intros a Ha. apply EQ. left. exact Ha.
  - intros a Ha Hout. apply EQ. right. split; [exact Ha| exact Hout].
Qed.

Lemma lp_client : forall (Σ Σx : rts RT) (mx : mem) (usp sp' f lo d A : Z) (bs : list byte),
  ART RT Σx mx -> rt_frames RT Σx = [(f, 2%nat)] -> rt_frames RT Σ = [] ->
  (forall e, In e (rt_live RT Σ) -> In e (rt_live RT Σx)) -> In (A, 16 * Z.of_nat (atp_P (chars bs))) (rt_live RT Σx) ->
  ((exists p n, In (p, n) (rt_live RT Σ) /\ p <= d /\ d + Z.of_nat (length bs) <= p + n) \/ (bs = [] /\ d < SEGTOP_A)) ->
  0 < f -> f mod 64 = 0 -> sp' <= usp -> usp + 16 <= USTACK_TOP ->
  forall x, lp_dom Σ usp sp' f A d bs x -> aclient (rt_live RT Σx) (rt_frames RT Σx) sp' x.
Proof using AF.
  intros Σ Σx mx usp sp' f lo d A bs ARTx FRSx FRS0 INCL INA INLV FPOS F64 SPLE SPT x [Hx|(Hx & _)].
  - assert (INF : In (f, 2%nat) (rt_frames RT Σx)) by (rewrite FRSx; left; reflexivity).
    destruct Hx as [H|[H|[H|[H|[H|H]]]]].
    + left. ul.
    + right; right; right; left. exists f, 2%nat. change (fs_size 2) with 256. split; [exact INF| lia].
    + right; right; right; right. exists f, 2%nat. change (fs_size 2) with 256. unfold shad, SHB. split; [exact INF| Z.div_mod_to_equations; lia].
    + right; right; left. exists A, (16 * Z.of_nat (atp_P (chars bs))). split; [exact INA| lia].
    + destruct INLV as [(p & k & Hin & Q1 & Q2)|(E & _)]; [| subst bs; cbn [length] in H; lia].
      right; right; left. exists p, k. split; [apply INCL; exact Hin| lia].
    + right; left. exact (proj1 (lib_fp_static x H)).
  - apply (aclient_mono _ _ _ _ _ _ _ Hx); [exact INCL| rewrite FRS0; intros e []| exact SPLE].
Qed.

Lemma lp_apart_frame : forall (Σ Σx : rts RT) (mx : mem) (usp sp' f lo d A lo' hi' : Z) (bs : list byte),
  ART RT Σx mx -> rt_frames RT Σx = [(f, 2%nat)] -> rt_frames RT Σ = [] -> rt_sp0 RT Σx = rt_sp0 RT Σ ->
  (forall e, In e (rt_live RT Σ) -> In e (rt_live RT Σx)) -> In (A, 16 * Z.of_nat (atp_P (chars bs))) (rt_live RT Σx) ->
  ((exists p n, In (p, n) (rt_live RT Σ) /\ p <= d /\ d + Z.of_nat (length bs) <= p + n) \/ (bs = [] /\ d < SEGTOP_A)) ->
  rt_sp0 RT Σ - STACK_WIN <= lo -> lo + FUZZ_STACK <= usp -> usp - 304 <= sp' ->
  (f + 256 <= f / 8 + 2147450880 \/ f / 8 + 2147450880 + 32 <= f) ->
  f + 56 <= lo' -> hi' <= f + 256 ->
  forall x, lp_dom Σ usp sp' f A d bs x -> ~ (lo' <= x < hi').
Proof using AF.
  intros Σ Σx mx usp sp' f lo d A lo' hi' bs ARTx FRSx FRS0 SPx INCL INA INLV LOW LOR SPR FSELF HLO HHI x Hx.
  assert (INF : In (f, 2%nat) (rt_frames RT Σx)) by (rewrite FRSx; left; reflexivity).
  pose proof (af_frames_range RT AF Σx mx f 2%nat ARTx INF) as (_ & FR1 & FSEG & FLV). change (fs_size 2) with 256 in FR1, FSEG, FLV. rewrite SPx in FR1.
  destruct Hx as [Hx|(Hx & _)].
  - destruct Hx as [H|[H|[H|[H|[H|H]]]]].
    + clear - H FR1 LOW LOR SPR HLO HHI. ul.
    + lia.
    + clear - H FSELF HLO HHI. lia.
    + pose proof (FLV A _ INA). lia.
    + destruct INLV as [(p & k & Hin & Q1 & Q2)|(E & _)]; [| subst bs; cbn [length] in H; lia].
      pose proof (FLV p k (INCL _ Hin)). lia.
    + pose proof (proj2 (lib_fp_static x H)). clear - H0 FSEG HLO HHI. unfold SEGTOP_A in *. lia.
  - destruct Hx as [H|[H|[H|[H|H]]]].
    + clear - H FR1 LOW LOR SPR HLO HHI. ul.
    + pose proof (client_static_range x H). clear - H0 FSEG HLO HHI. unfold SEGTOP_A in *. lia.
    + destruct H as (p & k & Hin & Hr). pose proof (FLV p k (INCL _ Hin)). lia.
    + destruct H as (f9 & k9 & Hin & _). rewrite FRS0 in Hin. destruct Hin.
    + destruct H as (f9 & k9 & Hin & _). rewrite FRS0 in Hin. destruct Hin.
Qed.

Lemma lp_apart_chunk : forall (Σ Σx : rts RT) (mx : mem) (usp sp' f lo d A q k : Z) (l1 l2 : list (Z * Z)) (bs : list byte),
  ART RT Σx mx -> rt_frames RT Σx = [(f, 2%nat)] -> rt_frames RT Σ = [] -> rt_sp0 RT Σx = rt_sp0 RT Σ ->
  rt_live RT Σx = l1 ++ (q, k) :: l2 ->
  (forall e, In e (rt_live RT Σ) -> In e (l1 ++ l2)) -> In (A, 16 * Z.of_nat (atp_P (chars bs))) (l1 ++ l2) ->
  ((exists p n, In (p, n) (rt_live RT Σ) /\ p <= d /\ d + Z.of_nat (length bs) <= p + n) \/ (bs = [] /\ d < SEGTOP_A)) ->
  rt_sp0 RT Σ - STACK_WIN <= lo -> lo + FUZZ_STACK <= usp -> usp - 304 <= sp' -> f mod 64 = 0 ->
  forall x, lp_dom Σ usp sp' f A d bs x -> ~ (q <= x < q + k).
Proof using AF.
  intros Σ Σx mx usp sp' f lo d A q k l1 l2 bs ARTx FRSx FRS0 SPx E INCL INA INLV LOW LOR SPR F64 x Hx.
  assert (INF : In (f, 2%nat) (rt_frames RT Σx)) by (rewrite FRSx; left; reflexivity).
  assert (INQ : In (q, k) (rt_live RT Σx)) by (rewrite E; apply in_or_app; right; left; reflexivity).
  pose proof (af_live_range RT AF Σx mx q k ARTx INQ) as (Q0 & Q1 & Q2). rewrite SPx in Q1.
  pose proof (af_frames_range RT AF Σx mx f 2%nat ARTx INF) as (_ & _ & _ & FLV). change (fs_size 2) with 256 in FLV.
  pose proof (proj1 (af_fshadow_apart RT AF Σx mx f 2%nat ARTx INF) q k INQ) as FSQ. change (fs_size 2) with 256 in FSQ.
  unfold shad, SHB in FSQ.
  pose proof (fun p n Hin => af_live_disj RT AF Σx mx q k p n l1 l2 ARTx E Hin) as DJ.
  destruct Hx as [Hx|(Hx & _)].
  - destruct Hx as [H|[H|[H|[H|[H|H]]]]].
    + clear - H Q1 LOW LOR SPR. ul.
    + pose proof (FLV q k INQ). lia.
    + clear - H FSQ F64. Z.div_mod_to_equations. lia.
    + pose proof (DJ A _ INA). lia.
    + destruct INLV as [(p & kk & Hin & P1 & P2)|(E0 & _)]; [| subst bs; cbn [length] in H; lia].
      pose proof (DJ p kk (INCL _ Hin)). lia.
    + pose proof (proj2 (lib_fp_static x H)). clear - H0 Q2. unfold SEGTOP_A in *. lia.
  - destruct Hx as [H|[H|[H|[H|H]]]].
    + clear - H Q1 LOW LOR SPR. ul.
    + pose proof (client_static_range x H). clear - H0 Q2. unfold SEGTOP_A in *. lia.
    + destruct H as (p & kk & Hin & Hr). pose proof (DJ p kk (INCL _ Hin)). lia.
    + destruct H as (f9 & k9 & Hin & _). rewrite FRS0 in Hin. destruct Hin.
    + destruct H as (f9 & k9 & Hin & _). rewrite FRS0 in Hin. destruct Hin.
Qed.

Lemma lp_fobjP : forall Σ Σx m mx usp sp' f lo d bs ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 h3 t A,
  lp_inv Σ Σx m mx usp sp' f lo d bs ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 h3 t A -> 0 < f -> f mod 64 = 0 ->
  fobj RT Σx mx (f + 96) 80.
Proof.
  intros until A. intros INV FPOS F64. destruct INV as (_ & _ & _ & _ & _ & _ & _ & FS & _ & _ & _ & _ & FRS & _).
  split; [Z.div_mod_to_equations; lia|]. split; [lia|]. change ((80 + 7) / 8) with 10.
  split; [exists f, 2%nat; rewrite FRS; change (fs_size 2) with 256; split; [left; reflexivity| lia]|].
  replace (shad (f + 96)) with (f / 8 + 2147450880 + Z.of_nat 12) by (unfold shad, SHB; Z.div_mod_to_equations; lia).
  unfold fa_shadow2 in FS. cbn [map app repeat] in FS.
  lazymatch type of FS with rw_cells _ _ _ (?c0 :: ?c1 :: ?c2 :: ?c3 :: ?c4 :: ?c5 :: ?c6 :: ?c7 :: ?c8 :: ?c9 :: ?c10 :: ?c11 ::
                                        ?d0 :: ?d1 :: ?d2 :: ?d3 :: ?d4 :: ?d5 :: ?d6 :: ?d7 :: ?d8 :: ?d9 :: ?rest) =>
    change (c0 :: c1 :: c2 :: c3 :: c4 :: c5 :: c6 :: c7 :: c8 :: c9 :: c10 :: c11 :: d0 :: d1 :: d2 :: d3 :: d4 :: d5 :: d6 :: d7 :: d8 :: d9 :: rest)
      with ([c0; c1; c2; c3; c4; c5; c6; c7; c8; c9; c10; c11] ++ [d0; d1; d2; d3; d4; d5; d6; d7; d8; d9] ++ rest) in FS end.
  apply Zvw.rw_cells_app in FS. destruct FS as [_ FS]. apply Zvw.rw_cells_app in FS. destruct FS as [FS _].
  cbn [cells_size csize Nat.add] in FS. destruct FS as [[_ HB] _]. exact HB.
Qed.

Lemma lp_fobjV : forall Σ Σx m mx usp sp' f lo d bs ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 h3 t A,
  lp_inv Σ Σx m mx usp sp' f lo d bs ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 h3 t A -> 0 < f -> f mod 64 = 0 ->
  fobj RT Σx mx (f + 32) 24.
Proof.
  intros until A. intros INV FPOS F64. destruct INV as (_ & _ & _ & _ & _ & _ & _ & FS & _ & _ & _ & _ & FRS & _).
  split; [Z.div_mod_to_equations; lia|]. split; [lia|]. change ((24 + 7) / 8) with 3.
  split; [exists f, 2%nat; rewrite FRS; change (fs_size 2) with 256; split; [left; reflexivity| lia]|].
  replace (shad (f + 32)) with (f / 8 + 2147450880 + Z.of_nat 4) by (unfold shad, SHB; Z.div_mod_to_equations; lia).
  unfold fa_shadow2 in FS. cbn [map app repeat] in FS.
  lazymatch type of FS with rw_cells _ _ _ (?c0 :: ?c1 :: ?c2 :: ?c3 :: ?d0 :: ?d1 :: ?d2 :: ?rest) =>
    change (c0 :: c1 :: c2 :: c3 :: d0 :: d1 :: d2 :: rest) with ([c0; c1; c2; c3] ++ [d0; d1; d2] ++ rest) in FS end.
  apply Zvw.rw_cells_app in FS. destruct FS as [_ FS]. apply Zvw.rw_cells_app in FS. destruct FS as [FS _].
  cbn [cells_size csize Nat.add] in FS. destruct FS as [[_ HB] _]. exact HB.
Qed.

Definition gate_postA (Σ : rts RT) (PMc : Model -> Prop) (usp lo d : Z) (bs : list byte)
    (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (m : mem) : config -> Prop :=
  fun c => exists (Σg : rts RT) (sp' f A impl idx oc ia tape sbuf : Z),
    ASTA RT Σg PMc (fun ms => exists (mg : mem) (x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2x s6x s7x s8x t3 t4 t5 t6 : word) F fc
                                    (h3 t j20 : list byte) (r : word),
        ms = sa_regs 0x96dcc x1 sp' gp tp t0 t1 t2 usp a0 a1 a2 a3 a4 a5 a6 a7 f s2x s6x s7x s8x t3 t4 t5 t6 F fc mg
        /\ frm0 fc
        /\ lp_inv Σ Σg m mg usp sp' f lo d bs ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 h3 t A
        /\ rw_cells bsegs mg (sp' + 136) (res_cellsA (f + 120) r j20) /\ bv_unsigned r < 64
        /\ s2a_okres tape sbuf (roundup64 (doc_cap bs + 3)) (al_sbuf (doc_cap bs)) r mg
        /\ pdone RT Σg mg (f + 96) (vblockA A (vcap_iter (atp_P (chars bs)) 0 0) (Z.of_nat (atp_P (chars bs))) ++ rt_live RT Σ)
        /\ pidA_st RT Σg mg (f + 96) impl idx oc ia tape sbuf (doc_cap bs)) c
    /\ usp - 304 <= sp' <= usp - 288 /\ sp' mod 32 = 0 /\ 0 < f /\ f mod 64 = 0 /\ f + 256 <= rt_sp0 RT Σ - STACK_WIN
    /\ (f + 256 <= 0x10000 \/ SEGTOP_A <= f) /\ (f + 256 <= f / 8 + 2147450880 \/ f / 8 + 2147450880 + 32 <= f)
    /\ SHB <= f / 8 + 2147450880 /\ f / 8 + 2147450880 + 32 + 1 <= rt_sp0 RT Σ - STACK_WIN
    /\ rt_live RT Σg = (ia, 1024) :: (oc, 8192) :: (idx, sc_idx (doc_cap bs)) :: (impl, 96) :: (tape, al_tape (doc_cap bs)) :: (sbuf, al_sbuf (doc_cap bs))
                         :: vblockA A (vcap_iter (atp_P (chars bs)) 0 0) (Z.of_nat (atp_P (chars bs))) ++ rt_live RT Σ
    /\ (impl mod 16 = 0 /\ idx mod 16 = 0 /\ oc mod 16 = 0 /\ ia mod 16 = 0 /\ tape mod 16 = 0 /\ sbuf mod 16 = 0)
    /\ rt_credit RT Σ - 2 - vcost_pushes (atp_P (chars bs)) 0 0 - mcost (doc_len bs + 64) - pid_costA (doc_len bs) <= rt_credit RT Σg.

Definition par_postA (Σ : rts RT) (PMc : Model -> Prop) (usp lo d : Z) (bs : list byte)
    (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (m : mem) : config -> Prop :=
  fun c => exists (Σ1 : rts RT) (sp' f A : Z),
    ASTA RT Σ1 PMc (fun ms => exists (m1 : mem) (x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2x s7x s8x t3 t4 t5 t6 : word) F fc (h3 t p1 p17 p57 : list byte),
        ms = MS (mkR x1 (Z_to_bv 64 sp') gp tp t0 t1 t2 (Z_to_bv 64 usp) (Z_to_bv 64 sp') a0 a1 a2 a3 a4 a5 a6 a7
                     s2x (Z_to_bv 64 (f + 32)) (Z_to_bv 64 (f + 96)) (Z_to_bv 64 (f + 120)) (Z_to_bv 64 A) s7x s8x
                     (Z_to_bv 64 (f / 8 + 2147450880)) (Z_to_bv 64 f) (Z_to_bv 64 2147450880) t3 t4 t5 t6)
                F (Z_to_bv 64 0x96d00) fc None m1 (seg_rom bsegs)
        /\ frm0 fc
        /\ lp_inv Σ Σ1 m m1 usp sp' f lo d bs ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 h3 t A
        /\ rw_cells bsegs m1 (f + 96) (parser_init p1 p17 p57)) c
    /\ vliveA (rt_live RT Σ1) A (vcap_iter (atp_P (chars bs)) 0 0) (Z.of_nat (atp_P (chars bs))) (rt_live RT Σ)
    /\ rt_credit RT Σ - 2 - vcost_pushes (atp_P (chars bs)) 0 0 <= rt_credit RT Σ1
    /\ usp - 304 <= sp' <= usp - 288 /\ sp' mod 32 = 0 /\ 0 < f /\ f mod 64 = 0 /\ f + 256 <= rt_sp0 RT Σ - STACK_WIN
    /\ (f + 256 <= 0x10000 \/ SEGTOP_A <= f) /\ (f + 256 <= f / 8 + 2147450880 \/ f / 8 + 2147450880 + 32 <= f)
    /\ SHB <= f / 8 + 2147450880 /\ f / 8 + 2147450880 + 32 + 1 <= rt_sp0 RT Σ - STACK_WIN.

Lemma bytes_at_firstn' : forall m A (bs : list byte) k, bytes_at bsegs m A bs -> bytes_at bsegs m A (firstn k bs).
Proof. intros m A bs k H. rewrite <- (firstn_skipn k bs) in H. apply bytes_at_app in H. destruct H as [H _]. exact H. Qed.

Lemma lp_inv_xfer_pid : forall Σ Σx Σy m mx my usp sp' f lo d bs ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 h3 t A (jr' : list byte),
  lp_inv Σ Σx m mx usp sp' f lo d bs ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 h3 t A ->
  rt_frames RT Σ = [] -> (forall e, In e (rt_live RT Σ) -> In e (rt_live RT Σx)) -> In (A, 16 * Z.of_nat (atp_P (chars bs))) (rt_live RT Σx) ->
  ((exists p n, In (p, n) (rt_live RT Σ) /\ p <= d /\ d + Z.of_nat (length bs) <= p + n) \/ (bs = [] /\ d < SEGTOP_A)) ->
  rt_sp0 RT Σ - STACK_WIN <= lo -> lo + FUZZ_STACK <= usp -> usp - 304 <= sp' <= usp - 288 ->
  (f + 256 <= 0x10000 \/ SEGTOP_A <= f) -> SHB <= f / 8 + 2147450880 ->
  rt_frames RT Σy = rt_frames RT Σx -> rt_sp0 RT Σy = rt_sp0 RT Σx ->
  ART RT Σy my -> mem_inv bsegs my -> stk bsegs my lo sp' ->
  (forall a : word, lp_dom Σ usp sp' f A d bs (bv_unsigned a) -> ~ (sp' + 136 <= bv_unsigned a < sp' + 160) -> ~ in_ranges LIB_FP (bv_unsigned a) -> my a = mx a) ->
  LIB my -> rw_cells bsegs my (sp' + 136) [CB 24 jr'] ->
  lp_inv Σ Σy m my usp sp' f lo d bs ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 h3 t A.
Proof using LIB_loc AF.
  intros until jr'. intros INV FRS0 INCL INA INLV LOW LOR SPR FSEG2 SHB0 FRS SP ARTy MIy STy EQ LBy RCy.
  destruct INV as (ARTx & _ & STx & (j0 & j1 & j2 & j4 & jq & je & jo & jn & jr & j13 & L1) & L2 & L3 & L4 & L5 & VR & BS & LB & PRES & FRSx & SPx).
  pose proof (af_sp0_range RT AF Σx mx ARTx) as SPR0. rewrite SPx in SPR0.
  pose proof (af_live_range RT AF Σx mx A _ ARTx INA) as (AR0 & AR1 & AR2). rewrite SPx in AR1.
  assert (NL : forall x, 0x6530c8 <= x \/ x < 0x11c1e0 -> ~ in_ranges LIB_FP x) by (intros x Hx HL; pose proof (proj2 (lib_fp_static x HL)); lia).
  assert (AG : forall (Q : Z -> Prop), (forall x, Q x -> lp_rng usp sp' f A d bs x /\ ~ (sp' + 136 <= x < sp' + 160) /\ (0x6530c8 <= x \/ x < 0x11c1e0)) -> agree_on Q mx my).
  { intros Q HQ a Ha. destruct (HQ _ Ha) as (H1 & H2 & H3). apply EQ; [left; exact H1| exact H2| exact (NL _ H3)]. }
  assert (STKHI : 0x676000 <= sp') by (clear - SPR0 LOW LOR SPR; ul).
  assert (INF : In (f, 2%nat) (rt_frames RT Σx)) by (rewrite FRSx; left; reflexivity).
  pose proof (fframe_ranges RT AF Σx mx f 2%nat ARTx INF) as (F0 & FR1 & _ & SHB1 & SHT). change (fs_size 2) with 256 in FR1, SHT. rewrite SPx in FR1, SHT.
  pose proof (af_frames_range RT AF Σx mx f 2%nat ARTx INF) as (_ & _ & FSG & _). change (fs_size 2) with 256 in FSG.
  assert (SHF : shad (f + 256) = f / 8 + 2147450880 + 32) by (unfold shad, SHB; Z.div_mod_to_equations; lia). rewrite SHF in SHT.
  assert (FLO : f + 256 <= sp') by (clear - FR1 LOW LOR SPR; ul).
  assert (SLO : f / 8 + 2147450880 + 32 < sp') by (clear - SHT LOW LOR SPR; ul).
  unfold lp_inv. split; [exact ARTy|]. split; [exact MIy|]. split; [exact STy|].
  split. { exists j0, j1, j2, j4, jq, je, jo, jn, jr', j13. unfold fa_locals2 in *.
           lazymatch type of L1 with rw_cells _ _ _ (?c0 :: ?c1 :: ?c2 :: ?c3 :: ?c4 :: ?c5 :: ?c6 :: ?c7 :: ?c8 :: ?c9 :: ?c10 :: ?rest) =>
             change (c0 :: c1 :: c2 :: c3 :: c4 :: c5 :: c6 :: c7 :: c8 :: c9 :: c10 :: rest) with ([c0; c1; c2; c3; c4; c5; c6; c7; c8; c9] ++ [c10] ++ rest) in L1 end.
           apply Zvw.rw_cells_app in L1. destruct L1 as [X1 L1]. apply Zvw.rw_cells_app in L1. destruct L1 as [_ X3].
           cbn [cells_size csize Nat.add] in X1, X3.
           lazymatch goal with |- rw_cells _ _ _ (?c0 :: ?c1 :: ?c2 :: ?c3 :: ?c4 :: ?c5 :: ?c6 :: ?c7 :: ?c8 :: ?c9 :: ?c10 :: ?rest) =>
             change (c0 :: c1 :: c2 :: c3 :: c4 :: c5 :: c6 :: c7 :: c8 :: c9 :: c10 :: rest) with ([c0; c1; c2; c3; c4; c5; c6; c7; c8; c9] ++ [c10] ++ rest) end.
           apply Zvw.rw_cells_app. split.
           { apply (rw_cells_agree_nw bsegs mx my _ _ X1). apply AG. intros x Hx. cbn [cells_size csize Nat.add] in Hx. split; [left; lia| lia]. }
           apply Zvw.rw_cells_app. split.
           { cbn [cells_size csize Nat.add]. replace (sp' + Z.of_nat 136) with (sp' + 136) by lia. exact RCy. }
           cbn [cells_size csize Nat.add]. apply (rw_cells_agree_nw bsegs mx my _ _ X3). apply AG. intros x Hx. cbn [cells_size csize Nat.add] in Hx. split; [left; lia| lia]. }
  split. { apply (stk_agree_nw bsegs mx my _ _ L2). apply AG. intros x Hx. cbv beta in Hx. split; [left; lia| lia]. }
  split. { apply (rw_cells_agree_nw bsegs mx my _ _ L3). apply AG. intros x Hx. unfold fa_saved in Hx. cbn [cells_size csize Nat.add] in Hx. split; [left; lia| lia]. }
  split. { apply (rw_cells_agree_nw bsegs mx my _ _ L4). apply AG. intros x Hx. unfold fz_hdr in Hx. cbn [cells_size csize Nat.add] in Hx.
           split; [right; left; lia|]. clear - Hx FSEG2 FLO. unfold SEGTOP_A in *. lia. }
  split. { apply (rw_cells_agree_nw bsegs mx my _ _ L5). apply AG. intros x Hx. unfold fa_shadow2 in Hx. cbn [map app repeat cells_size csize Nat.add] in Hx.
           split; [right; right; left; lia|]. clear - Hx SHB0 SLO. unfold SHB in *. lia. }
  split. { destruct VR as (E & R & C & A0 & AH & SV & BLK). unfold vrepA. split; [exact E|]. split; [exact R|]. split; [exact C|]. split; [exact A0|]. split; [exact AH|].
           split. { apply (rw_cells_agree_nw bsegs mx my _ _ SV). apply AG. intros x Hx. cbn [cells_size csize Nat.add] in Hx. split; [right; left; lia|].
                    clear - Hx FSEG2 FLO. unfold SEGTOP_A in *. lia. }
           destruct BLK as [B|(C1 & A16 & ASG & EL)]; [left; exact B| right]. split; [exact C1|]. split; [exact A16|]. split; [exact ASG|].
           apply (rw_cells_agree_nw bsegs mx my _ _ EL). apply AG. intros x Hx. rewrite velts_size, atp_elsA_length in Hx.
           split; [right; right; right; left; lia|]. clear - Hx AR1 AR2 LOW LOR SPR. unfold SEGTOP_A in *. ul. }
  split. { apply (bytes_at_agree bsegs mx my _ _ BS). apply AG. intros x Hx. cbv beta in Hx. split; [do 4 right; left; exact Hx|].
           destruct INLV as [(p & k & Hin & Q1 & Q2)|(E & _)]; [| subst bs; cbn [length] in Hx; lia].
           pose proof (af_live_range RT AF Σx mx p k ARTx (INCL _ Hin)) as (_ & R1 & R2). rewrite SPx in R1. clear - Hx Q1 Q2 R1 R2 LOW LOR SPR. unfold SEGTOP_A in *. ul. }
  split; [exact LBy|].
  split. { intros a Ha Hout. rewrite <- (PRES a Ha Hout). apply EQ; [right; split; [exact Ha| exact Hout]| | exact (not_in_ranges_of_outside _ _ Hout)].
           destruct Ha as [H|[H|[H|[H|H]]]]; [lia| pose proof (client_static_range _ H); unfold SEGTOP_A in *; lia| | |].
           - destruct H as (p & k & Hin & Hr). pose proof (af_live_range RT AF Σx mx p k ARTx (INCL _ Hin)) as (_ & R1 & _). rewrite SPx in R1.
             clear - Hr R1 LOW LOR SPR. ul.
           - destruct H as (f9 & k9 & Hin & _). rewrite FRS0 in Hin. destruct Hin.
           - destruct H as (f9 & k9 & Hin & _). rewrite FRS0 in Hin. destruct Hin. }
  split; [rewrite FRS; exact FRSx| rewrite SP; exact SPx].
Qed.

Lemma pidA_st_xfer : forall (Σ Σ' : rts RT) (live' : list (Z * Z)) (m m' : mem) (P sp impl idx oc ia tape sbuf cap : Z),
  pidA_st RT Σ m P impl idx oc ia tape sbuf cap -> ART RT Σ m ->
  rt_frames RT Σ' = rt_frames RT Σ -> In (impl, 96) live' ->
  rt_pres_fp live' (rt_frames RT Σ) sp [] m m' \/ rt_pres live' (rt_frames RT Σ) sp m m' ->
  pidA_st RT Σ' m' P impl idx oc ia tape sbuf cap.
Proof using AF.
  intros Σ Σ' live' m m' P sp impl idx oc ia tape sbuf cap (FOBJ & (p1 & p17 & p57 & PC) & (nsi & p12 & nxt & p28 & p50 & bufv & lenv & docv & IC)) ARTm FRS INM PRES.
  assert (PR : rt_pres live' (rt_frames RT Σ) sp m m').
  { destruct PRES as [H|H]; [| exact H]. intros a Ha. apply H; [exact Ha| exact I]. }
  split; [exact (fobj_pres RT AF Σ Σ' live' sp m m' P 80 ARTm FOBJ PR FRS)|].
  destruct FOBJ as (_ & _ & (f & c & Hf & FL & FH) & _). change ((80 + 7) / 8) with 10 in FH.
  split. { exists p1, p17, p57. apply (rw_cells_agree_nw bsegs m m' _ _ PC). apply (agree_of_pres _ _ _ _ _ _ PR). intros x Hx.
           unfold pid_cells in Hx. cbn [cells_size csize Nat.add] in Hx. right; right; right; left. exists f, c. split; [exact Hf| lia]. }
  exists nsi, p12, nxt, p28, p50, bufv, lenv, docv. apply (rw_cells_agree_nw bsegs m m' _ _ IC). apply (agree_of_pres _ _ _ _ _ _ PR). intros x Hx.
  unfold impl16 in Hx. cbn [cells_size csize Nat.add] in Hx. right; right; left. exists impl, 96. split; [exact INM| lia].
Qed.

Lemma gate_intro : forall (Σ Σg : rts RT) PMc (c : config) (m mg : mem) (usp sp' f A lo d : Z) (bs : list byte)
    (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2x s6x s7x s8x t3 t4 t5 t6 : word) F fc
    (h3 t j20 : list byte) (impl idx oc ia tape sbuf : Z) (r : word),
  ASTA RT Σg PMc (eq (sa_regs 0x96dcc x1 sp' gp tp t0 t1 t2 usp a0 a1 a2 a3 a4 a5 a6 a7 f s2x s6x s7x s8x t3 t4 t5 t6 F fc mg)) c -> frm0 fc ->
  lp_inv Σ Σg m mg usp sp' f lo d bs ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 h3 t A ->
  rw_cells bsegs mg (sp' + 136) (res_cellsA (f + 120) r j20) -> bv_unsigned r < 64 ->
  s2a_okres tape sbuf (roundup64 (doc_cap bs + 3)) (al_sbuf (doc_cap bs)) r mg ->
  pdone RT Σg mg (f + 96) (vblockA A (vcap_iter (atp_P (chars bs)) 0 0) (Z.of_nat (atp_P (chars bs))) ++ rt_live RT Σ) ->
  pidA_st RT Σg mg (f + 96) impl idx oc ia tape sbuf (doc_cap bs) ->
  usp - 304 <= sp' <= usp - 288 -> sp' mod 32 = 0 -> 0 < f -> f mod 64 = 0 -> f + 256 <= rt_sp0 RT Σ - STACK_WIN ->
  (f + 256 <= 0x10000 \/ SEGTOP_A <= f) -> (f + 256 <= f / 8 + 2147450880 \/ f / 8 + 2147450880 + 32 <= f) ->
  SHB <= f / 8 + 2147450880 -> f / 8 + 2147450880 + 32 + 1 <= rt_sp0 RT Σ - STACK_WIN ->
  rt_live RT Σg = (ia, 1024) :: (oc, 8192) :: (idx, sc_idx (doc_cap bs)) :: (impl, 96) :: (tape, al_tape (doc_cap bs)) :: (sbuf, al_sbuf (doc_cap bs))
                    :: vblockA A (vcap_iter (atp_P (chars bs)) 0 0) (Z.of_nat (atp_P (chars bs))) ++ rt_live RT Σ ->
  (impl mod 16 = 0 /\ idx mod 16 = 0 /\ oc mod 16 = 0 /\ ia mod 16 = 0 /\ tape mod 16 = 0 /\ sbuf mod 16 = 0) ->
  rt_credit RT Σ - 2 - vcost_pushes (atp_P (chars bs)) 0 0 - mcost (doc_len bs + 64) - pid_costA (doc_len bs) <= rt_credit RT Σg ->
  gate_postA Σ PMc usp lo d bs ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m c.
Proof.
  intros until r. intros Hc FRM INV RC R64 OKR PD PST SPR SPA FPOS F64 FR1 FSEG FSELF SHB0 SHT LVg MODS CR.
  exists Σg, sp', f, A, impl, idx, oc, ia, tape, sbuf. split.
  - eapply ASTA_conseq; [exact Hc|]. intros ms <-.
    exists mg, x1, t0, t1, t2, a0, a1, a2, a3, a4, a5, a6, a7, s2x, s6x, s7x, s8x, t3, t4, t5, t6, F, fc, h3, t, j20, r.
    split; [reflexivity|]. split; [exact FRM|]. split; [exact INV|]. split; [exact RC|]. split; [exact R64|]. split; [exact OKR|]. split; [exact PD| exact PST].
  - split; [exact SPR|]. split; [exact SPA|]. split; [exact FPOS|]. split; [exact F64|]. split; [exact FR1|]. split; [exact FSEG|]. split; [exact FSELF|].
    split; [exact SHB0|]. split; [exact SHT|]. split; [exact LVg|]. split; [exact MODS| exact CR].
Qed.

Lemma pdone_free : forall (Σp Σd : rts RT) (m m' : mem) (P buf nb sp : Z) (ia oc idx impl tape sbuf nia noc nidx nimpl ntape nsbuf : Z) (Lr : list (Z * Z)),
  pdone RT Σp m P ((buf, nb) :: Lr) -> ART RT Σp m ->
  rt_live RT Σp = (ia, nia) :: (oc, noc) :: (idx, nidx) :: (impl, nimpl) :: (tape, ntape) :: (sbuf, nsbuf) :: (buf, nb) :: Lr ->
  0 < nia -> 0 < noc -> 0 < nidx -> 0 < nimpl -> 0 < ntape -> 0 < nsbuf -> 0 < nb -> lposx Lr ->
  rt_live RT Σd = live_remove buf (rt_live RT Σp) -> rt_frames RT Σd = rt_frames RT Σp ->
  rt_pres (rt_live RT Σd) (rt_frames RT Σp) sp m m' ->
  pdone RT Σd m' P Lr
  /\ rt_live RT Σd = (ia, nia) :: (oc, noc) :: (idx, nidx) :: (impl, nimpl) :: (tape, ntape) :: (sbuf, nsbuf) :: Lr.
Proof using AF.
  intros Σp Σd m m' P buf nb sp ia oc idx impl tape sbuf nia noc nidx nimpl ntape nsbuf Lr PD ARTp LVp P1 P2 P3 P4 P5 P6 PB HL LVd FRSd PRES.

  destruct (pos_prefix_facts RT AF Σp m [(ia, nia); (oc, noc); (idx, nidx); (impl, nimpl); (tape, ntape); (sbuf, nsbuf); (buf, nb)] [] Lr ARTp
              ltac:(rewrite LVp; reflexivity)
              ltac:(intros e He; cbn [In] in He; destruct He as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]; cbn [snd]; assumption) HL) as [ND NI].
  cbn [map fst] in ND.
  assert (NB6 : forall e, In e [(ia, nia); (oc, noc); (idx, nidx); (impl, nimpl); (tape, ntape); (sbuf, nsbuf)] -> fst e <> buf).
  { pose proof (fun i x => @nodup_nth_neq Z _ i 6%nat x buf ND) as NN.
    intros e He. cbn [In] in He.
    destruct He as [<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]; cbn [fst];
      [exact (NN 0%nat _ eq_refl eq_refl ltac:(discriminate))| exact (NN 1%nat _ eq_refl eq_refl ltac:(discriminate))
      | exact (NN 2%nat _ eq_refl eq_refl ltac:(discriminate))| exact (NN 3%nat _ eq_refl eq_refl ltac:(discriminate))
      | exact (NN 4%nat _ eq_refl eq_refl ltac:(discriminate))| exact (NN 5%nat _ eq_refl eq_refl ltac:(discriminate))]. }
  assert (NBL : forall e, In e Lr -> fst e <> buf).
  { intros e He E. apply (NI (buf, nb) e ltac:(cbn [In]; tauto) He). cbn [fst]. rewrite E. reflexivity. }
  assert (LVd' : rt_live RT Σd = (ia, nia) :: (oc, noc) :: (idx, nidx) :: (impl, nimpl) :: (tape, ntape) :: (sbuf, nsbuf) :: Lr).
  { rewrite LVd, LVp. pose proof (live_remove_one buf nb [(ia, nia); (oc, noc); (idx, nidx); (impl, nimpl); (tape, ntape); (sbuf, nsbuf)] [] Lr
                                      NB6 ltac:(intros e []) NBL) as R. cbn [app] in R. exact R. }
  split; [| exact LVd'].
  destruct PD as (impl' & tape' & sbuf' & idx' & oc' & ia' & nt & ns & nidx' & noc' & nia' & dcap & pre8 & mid & mid2 & rest & ipre8 & imid & irest
                  & FOBJ & PC & INM & I8 & IC & INS & INT & INA & INO & INX & NS0 & NT0 & NA0 & NO0 & NX0 & ND6 & EL).

  assert (KEEP : forall p n, In (p, n) (rt_live RT Σp) -> p <> buf -> In (p, n) (rt_live RT Σd)).
  { intros p n Hin NE. rewrite LVd. apply (live_remove_keep _ _ (p, n) Hin). cbn [fst]. exact NE. }
  assert (HB : forall p, In p [impl'; idx'; oc'; ia'; tape'; sbuf'] -> p <> buf).
  { intros p Hp E. subst p.
    assert (X : ~ In (buf, nb) (live_remove impl' (live_remove idx' (live_remove oc' (live_remove ia' (live_remove tape' (live_remove sbuf' (rt_live RT Σp)))))))).
    { cbn [In] in Hp. intros Hin.
      repeat match goal with H : In _ (live_remove ?p ?l) |- _ =>
        let N := fresh "NEQ" in pose proof (live_remove_neq l p _ H) as N; apply live_remove_sub in H; cbn [fst] in N end.
      intuition congruence. }
    apply X. rewrite EL. left. reflexivity. }
  cbn [In] in HB.
  exists impl', tape', sbuf', idx', oc', ia', nt, ns, nidx', noc', nia', dcap, pre8, mid, mid2, rest, ipre8, imid, irest.
  split. { apply (fobj_pres RT AF Σp Σd (rt_live RT Σd) sp m m' P 80 ARTp FOBJ PRES FRSd). }
  split. { apply (rw_cells_agree_nw bsegs m m' _ _ PC). apply (agree_of_pres _ _ _ _ _ _ PRES). destruct FOBJ as (_ & _ & (f & c & Hf & FL & FH) & _).
           intros x Hx. unfold pd_cells in Hx. cbn [cells_size csize Nat.add] in Hx. right; right; right; left. exists f, c. split; [exact Hf|].
           change ((80 + 7) / 8) with 10 in FH. lia. }
  split; [apply KEEP; [exact INM| apply HB; tauto]|]. split; [exact I8|].
  split. { apply (rw_cells_agree_nw bsegs m m' _ _ IC). apply (agree_of_pres _ _ _ _ _ _ PRES). intros x Hx. unfold dl_cells in Hx. cbn [cells_size csize Nat.add] in Hx.
           right; right; left. exists impl', 96. split; [apply KEEP; [exact INM| apply HB; tauto]| lia]. }
  split; [apply KEEP; [exact INS| apply HB; tauto]|]. split; [apply KEEP; [exact INT| apply HB; tauto]|].
  split; [apply KEEP; [exact INA| apply HB; tauto]|]. split; [apply KEEP; [exact INO| apply HB; tauto]|]. split; [apply KEEP; [exact INX| apply HB; tauto]|].
  split; [exact NS0|]. split; [exact NT0|]. split; [exact NA0|]. split; [exact NO0|]. split; [exact NX0|]. split; [exact ND6|].
  rewrite LVd. rewrite (live_remove_comm sbuf' buf), (live_remove_comm tape' buf), (live_remove_comm ia' buf), (live_remove_comm oc' buf),
    (live_remove_comm idx' buf), (live_remove_comm impl' buf), EL.
  rewrite live_remove_cons'. cbn [fst]. rewrite Z.eqb_refl. exact (live_remove_none' buf Lr NBL).
Qed.

End Kit.
