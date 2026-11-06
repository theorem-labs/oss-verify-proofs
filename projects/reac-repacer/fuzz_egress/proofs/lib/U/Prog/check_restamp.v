(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Copyright 2026 Theorem Labs *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-repacer/fuzz_uci/lib/Prog/check_no_overread.v, with its module paths, module names, addresses and numbers changed; 603 of its 729 lines of code are new or changed and 726 lines of the source are left out. *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Sem Fpu.
From OSSVerify.Proofs.reac_repacer.fuzz_egress.lib.Lib Require Import
  PropExec MState Mem Cells Exec Frame Step Tac Bytes ZBridge.
From OSSVerify.Proofs.reac_repacer.fuzz_egress.lib.U Require Import Img0.
From OSSVerify.Proofs.reac_repacer.fuzz_egress.lib.U.Spec Require Import StrFun.
From OSSVerify.Proofs.reac_repacer.fuzz_egress.lib.U.Prog Require Import memcpy_c bcmp_c rp_restamp_c check_restamp_c.
Import ListNotations.
Open Scope Z_scope.

(* Part 1: the machine walk in three segments over rsegs: the short return (n < 18), the prologue up to malloc,
   and the body after malloc up to the tail call to free (memcpy, rp_restamp, the byte checks, two bcmp calls). *)

Definition CS_MALLOC : Z := 0x14240.
Definition CS_FREE : Z := 0x14100.

Ltac cs_regs := unfold mkR;
  repeat match goal with
  | |- TNode _ _ _ = TNode _ _ _ => f_equal
  | |- Some _ = Some _ => f_equal
  end.

Ltac cs_usub := repeat match goal with |- context [bv_unsigned (Z_to_bv 64 ?z)] => rewrite (unsigned_lit z) by nia end.

Ltac cs_w := cs_usub; rewrite ?Z.shiftl_mul_pow2 by lia;
  first [ reflexivity | f_equal; lia | apply Z_to_bv_eqm; f_equal; lia ].

Lemma cs_short :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z),
    stk rsegs m lo (bv_unsigned sp) -> lo + 48 <= bv_unsigned sp -> bv_unsigned a1 < 18 ->
    evt rsegs
      (fun ms' => exists (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word)
                    (m' : word -> option byte),
         ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7'
                       s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                  F (ret_pc ra) fc None m' (seg_rom rsegs) /\
         munch [(bv_unsigned sp - 48, bv_unsigned sp)] m m' /\ wmono rsegs m m')
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 CHECK_RESTAMP) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo
    ST HLO HN.
  unfold CHECK_RESTAMP.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. change (bv_modulus 64) with (2^64) in Rsp.
  assert (Hlo0 : 0 <= lo) by (destruct ST as [H _]; exact H).
  pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  carve_frame 48%nat ST.
  do 9 step.
  if_false.
  do 7 step.
  apply evt_done. do 16 eexists. split; [reflexivity|]. split; [exact MU | exact WM].
Qed.

Lemma cs_seg1 :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z),
    stk rsegs m lo (bv_unsigned sp) -> lo + 48 <= bv_unsigned sp -> 18 <= bv_unsigned a1 ->
    evt rsegs
      (fun ms' => exists (t0' t1' t2' a1' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : word -> option byte)
                    (junk : list byte),
         ms' = MS (mkR (Z_to_bv 64 0x12ea8) (Z_to_bv 64 (bv_unsigned sp - 48)) gp tp t0' t1' t2' a1 s1 a1 a1' a2
                       a3' a4' a5' a6' a7' a0 a2 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                  F (Z_to_bv 64 CS_MALLOC) fc None m' (seg_rom rsegs) /\
         munch [(bv_unsigned sp - 48, bv_unsigned sp)] m m' /\ wmono rsegs m m' /\
         rw_cells rsegs m' (bv_unsigned sp - 48) [CB 8 junk; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra])
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 CHECK_RESTAMP) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo
    ST HLO HN.
  unfold CHECK_RESTAMP, CS_MALLOC.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. change (bv_modulus 64) with (2^64) in Rsp.
  assert (Hlo0 : 0 <= lo) by (destruct ST as [H _]; exact H).
  pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  carve_frame 48%nat ST.
  do 9 step.
  if_true.
  do 4 step.
  apply evt_done. do 15 eexists. split.
  2: { split; [eassumption|]. split; [eassumption|]. replace (bv_unsigned sp - 48) with (bv_unsigned sp + -48) by lia.
       eassumption. }
  reflexivity.
Qed.

Lemma cs_memcmp_self : forall (l : list byte) k, (k <= length l)%nat -> memcmp_model l l k = Some 0.
Proof.
  intros l k. revert l. induction k as [|k IH]; intros [|x l] H; cbn in *; try lia; try reflexivity.
  rewrite Z.eqb_refl. apply IH. lia.
Qed.

Lemma cs_wr_sub : forall segs m a n k j, wr_at segs m a n -> 0 <= k -> k + j <= n -> 0 <= j -> wr_at segs m (a + k) j.
Proof.
  intros segs m a n k j (H0 & H1 & H) Hk Hkj Hj. split; [lia|]. split; [lia|].
  intros i Hi. replace (a + k + i) with (a + (k + i)) by lia. apply H. lia.
Qed.

Lemma cs_seq_nth : forall s k i, (i < k)%nat -> nth_error (seq s k) i = Some (s + i)%nat.
Proof.
  intros s k. revert s. induction k as [|k IH]; intros s i Hi; [lia|].
  destruct i as [|i]; cbn; [f_equal; lia|]. rewrite IH by lia. f_equal. lia.
Qed.

(* KindB's present_rw_cells, with presence spelled out. *)
Lemma cs_cells_of : forall segs m a (k : nat), 0 <= a -> a + Z.of_nat k <= 2 ^ 64 ->
  (forall i, 0 <= i < Z.of_nat k -> exists bb, m (Z_to_bv 64 (a + i)) = Some bb) ->
  exists junk, rw_cells segs m a [CB k junk].
Proof.
  intros segs m a k Ha Hk H.
  exists (map (fun i => match m (wa (a + Z.of_nat i)) with Some b => b | None => Z_to_bv 8 0 end) (seq 0 k)).
  assert (L : length (map (fun i => match m (wa (a + Z.of_nat i)) with Some b => b | None => Z_to_bv 8 0 end)
                         (seq 0 k)) = k) by (rewrite length_map, length_seq; reflexivity).
  split; [split|].
  - cbn. split; [exact L | exact I].
  - cbn [cells_bytes cbytes]. rewrite app_nil_r. split; [exact Ha|]. split; [rewrite L; exact Hk|].
    intros i Hi. rewrite L in Hi.
    destruct (H (Z.of_nat i) ltac:(lia)) as [b E].
    rewrite (map_nth_error _ _ _ (cs_seq_nth 0 k i Hi)). cbn [Nat.add].
    unfold mrd. unfold wa. rewrite E. reflexivity.
  - split; [exact Ha|]. split; [cbn; lia|]. intros i Hi. cbn in Hi.
    destruct (H i ltac:(lia)) as [b E]. unfold wview, wa. rewrite E. discriminate.
Qed.

Definition cs_s2_post (vra sp gp tp v0 v1 v2 v3 s4 s5 s6 s7 s8 s9 s10 s11 cw : word) (F : bvmap 5 word) (fc : bv 32)
    (n : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : word -> option byte),
    ms' = MS (mkR vra (Z_to_bv 64 (bv_unsigned sp + 48)) gp tp t0 t1 t2 v0 v1 cw a1 a2 a3 a4 a5 a6 a7 v2 v3
               s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 CS_FREE) fc None m' (seg_rom rsegs) /\
    munch [(bv_unsigned cw, bv_unsigned cw + n)] m m' /\ wmono rsegs m m'.

Lemma cs_seg2 : memcpy_contract -> rp_restamp_contract -> bcmp_contract ->
  forall (ra sp gp tp t0 t1 t2 s1 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
         (cw nw fw kw v0 v1 v2 v3 vra : word) (fj junk src : list byte),
    18 <= bv_unsigned nw <= 1600 ->
    0 < bv_unsigned cw -> bv_unsigned cw + bv_unsigned nw <= bv_unsigned sp ->
    0 < bv_unsigned fw -> bv_unsigned fw + bv_unsigned nw < 2 ^ 63 ->
    (bv_unsigned cw + bv_unsigned nw <= bv_unsigned fw \/ bv_unsigned fw + bv_unsigned nw <= bv_unsigned cw) ->
    bv_unsigned sp + 48 < 2 ^ 64 ->
    mem_inv rsegs m ->
    rw_cells rsegs m (bv_unsigned sp) [CB 8 fj; C8 v3; C8 v2; C8 v1; C8 v0; C8 vra] ->
    rw_cells rsegs m (bv_unsigned cw) [CB (Z.to_nat (bv_unsigned nw)) junk] ->
    bytes_at rsegs m (bv_unsigned fw) src -> length src = Z.to_nat (bv_unsigned nw) ->
    evt rsegs (cs_s2_post vra sp gp tp v0 v1 v2 v3 s4 s5 s6 s7 s8 s9 s10 s11 cw F fc (bv_unsigned nw) m)
      (MS (mkR ra sp gp tp t0 t1 t2 nw s1 cw a1 a2 a3 a4 a5 a6 a7 fw kw s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x12ea8) fc None m (seg_rom rsegs)).
Proof.
  intros MCPY RST BCMP ra sp gp tp t0 t1 t2 s1 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    cw nw fw kw v0 v1 v2 v3 vra fj junk src HN HC0 HCS HF0 HF1 HD HSP MI FR CJ FB FL.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. change (bv_modulus 64) with (2^64) in Rsp.
  pose proof (bv_unsigned_in_range 64 cw) as Rcw. change (bv_modulus 64) with (2^64) in Rcw.
  pose proof (bv_unsigned_in_range 64 kw) as Rkw. change (bv_modulus 64) with (2^64) in Rkw.
  step. if_false.
  do 4 step.
  eapply evt_cut.
  { eapply MCPY with (src := src) (junk := junk); [exact FB | exact FL | exact CJ | lia | exact MI]. }
  intros ms1 (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m1 & -> & MU1 & WM1 & MI1 & CW1 &
    FB1).
  rewrite ret_pc_even by first [lia | reflexivity].
  do 3 step.
  pose proof CW1 as [[_ CB1] WR1]. cbn [cells_bytes cbytes] in CB1. rewrite app_nil_r in CB1.
  cbn [cells_size csize] in WR1. rewrite Nat.add_0_r, Z2Nat.id in WR1 by lia.
  eapply evt_cut.
  { eapply RST; [lia | apply (cs_wr_sub _ _ _ _ 14 2 WR1); lia | exact MI1]. }
  intros ms2 (c1 & c2 & m2 & -> & MU2 & WM2 & MI2 & RB2).
  rewrite ret_pc_even by first [lia | reflexivity].
  unfold restamp_bytes in RB2.
  assert (R14 : ov_read_bytes rsegs m2 (wa (bv_unsigned cw + 14)) 1 = Some [Z_to_bv 8 (bv_unsigned kw mod 256)]).
  { replace (bv_unsigned cw + 14) with (bv_unsigned cw + 14 + 0) by lia.
    rewrite (bytes_at_read rsegs m2 _ _ 0 1 RB2) by (cbn; lia). reflexivity. }
  assert (R15 : ov_read_bytes rsegs m2 (wa (bv_unsigned cw + 15)) 1 =
                Some [Z_to_bv 8 (bv_unsigned kw / 256 mod 256)]).
  { replace (bv_unsigned cw + 15) with (bv_unsigned cw + 14 + 1) by lia.
    rewrite (bytes_at_read rsegs m2 _ _ 1 1 RB2) by (cbn; lia). reflexivity. }
  assert (E14 : zxb (Z_to_bv 8 (bv_unsigned kw mod 256)) = Z_to_bv 64 (Z.land (bv_unsigned kw) 255)).
  { unfold zxb. f_equal. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256.
    rewrite Z.mod_mod by lia. change 255 with (Z.ones 8). rewrite Z.land_ones by lia. reflexivity. }
  assert (E15 : zxb (Z_to_bv 8 (bv_unsigned kw / 256 mod 256)) =
                Z_to_bv 64 (bv_unsigned (Z_to_bv 64 (bv_unsigned kw ≪ 48)) ≫ 56)).
  { unfold zxb. f_equal. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256.
    rewrite Z.shiftr_div_pow2 by lia. rewrite unsigned_lit_wrap. rewrite Z.shiftl_mul_pow2 by lia.
    change (2 ^ 48) with 281474976710656. change (2 ^ 56) with 72057594037927936.
    change (2 ^ 64) with 18446744073709551616.
    Z.div_mod_to_equations. lia. }
  (* UBSan: c + 14 does not overflow *)
  do 2 step. if_false.
  do 3 step.
  rewrite E14, bv_eqb_refl. cbn [negb].
  (* UBSan: c + 15 does not overflow *)
  do 2 step. if_false.
  do 4 step.
  rewrite E15, bv_eqb_refl. cbn [negb].
  do 4 step.
  pose proof (firstn_skipn 14 src) as S14. pose proof (firstn_skipn 16 src) as S16.
  assert (L14 : length (firstn 14 src) = 14%nat) by (rewrite firstn_length_le; lia).
  assert (L16 : length (firstn 16 src) = 16%nat) by (rewrite firstn_length_le; lia).
  assert (CB14 : bytes_at rsegs m1 (bv_unsigned cw) (firstn 14 src)).
  { rewrite <- S14 in CB1. apply bytes_at_app in CB1. exact (proj1 CB1). }
  assert (FB14 : bytes_at rsegs m1 (bv_unsigned fw) (firstn 14 src)).
  { pose proof FB1 as X. rewrite <- S14 in X. apply bytes_at_app in X. exact (proj1 X). }
  assert (CB16 : bytes_at rsegs m1 (bv_unsigned cw + 16) (skipn 16 src)).
  { pose proof CB1 as X. rewrite <- S16 in X. apply bytes_at_app in X. rewrite L16 in X. exact (proj2 X). }
  assert (FB16 : bytes_at rsegs m1 (bv_unsigned fw + 16) (skipn 16 src)).
  { pose proof FB1 as X. rewrite <- S16 in X. apply bytes_at_app in X. rewrite L16 in X. exact (proj2 X). }
  assert (LS16 : length (skipn 16 src) = Z.to_nat (bv_unsigned nw - 16)) by (rewrite length_skipn; lia).
  eapply (bytes_at_transport rsegs) in CB14; [| exact MU2 | cbn [disjoint_from]; rewrite L14; lia].
  eapply (bytes_at_transport rsegs) in FB14; [| exact MU2 | cbn [disjoint_from]; rewrite L14; lia].
  eapply (bytes_at_transport rsegs) in CB16; [| exact MU2 | cbn [disjoint_from]; rewrite LS16; lia].
  eapply (bytes_at_transport rsegs) in FB16; [| exact MU2 | cbn [disjoint_from]; rewrite LS16; lia].
  eapply evt_cut.
  { eapply BCMP with (ls := firstn 14 src) (rs := firstn 14 src) (v := 0).
    - exact CB14.
    - exact FB14.
    - apply cs_memcmp_self. rewrite unsigned_lit by lia. rewrite L14. lia.
    - exact MI2. }
  intros ms3 (d0 & d1 & d2 & e1 & e2 & e3 & e4 & e5 & e6 & e7 & d3 & d4 & d5 & d6 & m3 & -> & MU3 & WM3 & MI3 & _ & _).
  rewrite ret_pc_even by first [lia | reflexivity].
  step. if_false.
  (* UBSan: f + 16 and c + 16 do not overflow *)
  do 2 step. if_false.
  step. if_false.
  do 4 step.
  eapply (bytes_at_transport rsegs) in CB16; [| exact MU3 | exact I].
  eapply (bytes_at_transport rsegs) in FB16; [| exact MU3 | exact I].
  eapply evt_cut.
  { eapply BCMP with (ls := skipn 16 src) (rs := skipn 16 src) (v := 0).
    - rewrite unsigned_lit by lia. exact CB16.
    - rewrite unsigned_lit by lia. exact FB16.
    - apply cs_memcmp_self. rewrite unsigned_lit by lia. rewrite LS16. lia.
    - exact MI3. }
  intros ms4 (f0 & f1 & f2 & g1 & g2 & g3 & g4 & g5 & g6 & g7 & f3 & f4 & f5 & f6 & m4 & -> & MU4 & WM4 & MI4 & _ & _).
  rewrite ret_pc_even by first [lia | reflexivity].
  step. if_false.
  assert (FR4 : rw_cells rsegs m4 (bv_unsigned sp) [CB 8 fj; C8 v3; C8 v2; C8 v1; C8 v0; C8 vra]).
  { apply (rw_cells_transport rsegs _ m3 m4 _ _ (rw_cells_transport rsegs _ m2 m3 _ _
      (rw_cells_transport rsegs _ m1 m2 _ _ (rw_cells_transport rsegs _ m m1 _ _ FR MU1 WM1 ltac:(cbn; lia))
         MU2 WM2 ltac:(cbn; lia)) MU3 WM3 I) MU4 WM4 I). }
  clear FR CJ CW1 CB1 FB FB1 CB14 FB14 CB16 FB16 RB2.
  do 8 step.
  apply evt_done. unfold cs_s2_post, CS_FREE. do 15 eexists. split; [first [reflexivity | f_equal; cs_regs; cs_w]|].
  split.
  - apply (munch_trans _ m m3 m4); [apply (munch_trans _ m m2 m3); [apply (munch_trans _ m m1 m2) |] |].
    + exact MU1.
    + refine (munch_weaken _ _ m1 m2 _ MU2). intros x Hx. cbn [outside] in *. lia.
    + refine (munch_weaken _ _ m2 m3 _ MU3). intros x Hx. exact I.
    + refine (munch_weaken _ _ m3 m4 _ MU4). intros x Hx. exact I.
  - exact (wmono_trans rsegs m m3 m4 (wmono_trans rsegs m m2 m3 (wmono_trans rsegs m m1 m2 WM1 WM2) WM3) WM4).
Qed.

(* Part 2: the allocator world (SR over call_pre_k / call_post_k), decode's check_round_trip.v route: the segments above
   run on the normalized memory (MemNorm) and their footprints carry kb_mid across; malloc and free by their
   contracts. The glue lemmas are decode's crt_glue.v / check_round_trip.v, copied (cs_ for crt_ / cr_). *)

From OSSVerify.Proofs.reac_repacer.fuzz_egress.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.reac_repacer.fuzz_egress.lib.U.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.reac_repacer.fuzz_egress.lib.U.Reusable Require Import YM05 YL0i YL01 YO10.
From OSSVerify.Proofs.reac_repacer.fuzz_egress.lib.U Require Import Contract KindBGlue Img0.
From OSSVerify.Proofs.reac_repacer.fuzz_egress.lib.U.Prog Require Import check_restamp_c.
From OSSVerify.Proofs.reac_repacer.fuzz_egress.lib.U.Prog Require Import EgressGlue.
Local Open Scope Z_scope.

Lemma cs_pw : forall (l1 l2 : list (Z * Z)) a k c j, pairwise ranges_disjoint (l1 ++ (a, k) :: l2) ->
  In (c, j) (l1 ++ l2) -> a + k <= c \/ c + j <= a.
Proof. intros l1 l2 a k c j H Hi. exact (eg_pw_mid l1 l2 (a, k) (c, j) H Hi). Qed.

Lemma eg_notin : forall (l1 l2 : list (Z * Z)) x, pairwise ranges_disjoint (l1 ++ x :: l2) -> 0 < snd x ->
  ~ In x (l1 ++ l2).
Proof.
  intros l1 l2 x H Hx Hin. pose proof (eg_pw_mid l1 l2 x x H Hin) as D. unfold ranges_disjoint in D. lia.
Qed.

Lemma cs_cells_norm : forall m A cs, ro_agree rsegs m -> Step.rw_cells rsegs m A cs ->
  (forall i, 0 <= i < Z.of_nat (Cells.cells_size cs) -> Mem.ro_addr rsegs (Z_to_bv 64 (A + i)) = false) ->
  Step.rw_cells rsegs (normalize rsegs m) A cs.
Proof.
  intros m A cs RO [[Hwf Hb] Hw] Hro. split; [split; [exact Hwf|]|].
  - exact (bytes_at_normalize rsegs m A _ RO Hb).
  - exact (wr_at_norm rsegs m (normalize rsegs m) A _ (mem_rel_normalize rsegs m RO) Hw Hro).
Qed.

Section CRS.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Hypothesis SEGS : ms_segs B = rsegs.
Hypothesis MALPC : ms_malloc B = 0x14240.
Hypothesis FREEPC : ms_free B = 0x14100.
Hypothesis ERR : errno_addr B + 4 <= alloc_ceiling.
Hypothesis AX : AllocExtra B (aa_MR API).
Hypothesis CT : ctx_owned B API.
Hypothesis MALLOC : malloc_contract B API.
Hypothesis FREE : forall fx' : YK11.FPState, @free_contract fx' rc B API.
Hypothesis MCPY : memcpy_contract.
Hypothesis RST : rp_restamp_contract.
Hypothesis BCMP : bcmp_contract.

Lemma cs_blk : forall Lk Ak mk mdk P k, aa_MR API Lk Ak mk mdk -> In (P, k) (blocks Lk Ak) ->
  4096 <= P /\ P + k <= alloc_ceiling /\ P mod 16 = 0 /\
  forall i, 0 <= i < k -> present mk (P + i) /\ ~ in_img B (P + i) /\ ~ owned B Lk Ak (P + i).
Proof.
  intros Lk Ak mk mdk P k HM Hin.
  destruct (eg_bu Lk Ak P k Hin) as (p & Hp & <-).
  destruct (mr_blocks_range _ _ (aa_laws API) _ _ _ _ p k HM Hp) as [H1 H2].
  split; [exact H1|]. split; [exact H2|].
  split; [exact (mr_blocks_aligned _ _ (aa_laws API) _ _ _ _ p k HM Hp)|].
  intros i Hi. destruct (mr_blocks _ _ (aa_laws API) _ _ _ _ p k i HM Hp Hi) as (Hpr & _ & _ & Hno).
  split; [exact Hpr|]. split; [exact (ax_blocks_img AX Lk Ak mk mdk p k i HM Hp Hi) | exact Hno].
Qed.

Section Body.
Variables (L : layout) (A : astate) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model)
  (f n ctr : Z) (b : sbound).
Hypothesis PRE : call_pre_k B (aa_MR API) CHECK_RESTAMP_STACK L A regs mem md.
Hypothesis R10 : getr regs 10 = Z_to_bv 64 f.
Hypothesis R11 : getr regs 11 = Z_to_bv 64 n.
Hypothesis R12 : getr regs 12 = Z_to_bv 64 ctr.
Hypothesis NB : 0 <= n <= 1600.
Hypothesis IB : in_block L A f n.
Hypothesis RO : ro_agree (ms_segs B) mem.
Hypothesis FRM : frm_zero fp_csr.
Hypothesis RES : res_ok_slots A b.
Hypothesis ROOM : room_slots b n.

Definition cs_inv (L' : layout) (A' : astate) (m' : word -> option byte) (md' : Model) : Prop :=
  kb_mid B API CHECK_RESTAMP_STACK (spZ regs) L A mem md (fun _ => False) L' A' m' md' /\
  (length (st_regions A) <= length (st_regions A'))%nat /\
  (forall p k, In (p, k) (user_blocks A) -> In (p, k) (user_blocks A')) /\
  ro_agree (ms_segs B) m' /\ guard_kept B mem m'.

Definition cs_keep (r : bvmap 5 word) : Prop :=
  getr r 3 = getr regs 3 /\ getr r 4 = getr regs 4 /\ getr r 20 = getr regs 20 /\ getr r 21 = getr regs 21 /\
  getr r 22 = getr regs 22 /\ getr r 23 = getr regs 23 /\ getr r 24 = getr regs 24 /\ getr r 25 = getr regs 25 /\
  getr r 26 = getr regs 26 /\ getr r 27 = getr regs 27.

Definition cs_frame (m' : word -> option byte) : Prop :=
  exists junk, Step.rw_cells rsegs m' (spZ regs - 48) [Cells.CB 8 junk; Cells.C8 (getr regs 19);
    Cells.C8 (getr regs 18); Cells.C8 (getr regs 9); Cells.C8 (getr regs 8); Cells.C8 (getr regs 1)].

Definition cs_final (c' : config) : Prop :=
  exists (fx' : FPState) L' A' regs' mem' md',
    c' = mkCfg (@mkst fx' regs' (getr regs 1) mem' (seg_rom (ms_segs B))) md' /\
    frm_zero (@fp_csr fx') /\
    call_post_k B (aa_MR API) CHECK_RESTAMP_STACK L A regs mem md (fun _ => False) L' A' regs' mem' md' /\
    blocks L' A' = blocks L A /\
    blocks_kept B L A mem mem' (fun _ => False) /\
    guard_kept B mem mem' /\
    ro_agree (ms_segs B) mem' /\
    res_ok_slots A' b /\
    (st_init_done A = true -> st_init_done A' = true).

Lemma cs_pre : forall Lk Ak mk mdk regsk off K1,
  cs_inv Lk Ak mk mdk -> spZ regsk = spZ regs - off -> 0 <= off -> 0 <= K1 -> off + K1 <= CHECK_RESTAMP_STACK ->
  spZ regsk mod 16 = 0 -> getr regsk 4 = getr regs 4 -> YK0s.ret_ok (getr regsk 1) -> st_init_done Ak = true ->
  call_pre_k B (aa_MR API) K1 Lk Ak regsk mk mdk.
Proof.
  intros Lk Ak mk mdk regsk off K1 ((M1 & W1 & B1 & _ & _ & _ & _ & _ & S1) & _) Hsp Hf HK1 HfK H16 H4 Hra Hinit.
  pose proof PRE as (_ & _ & _ & _ & _ & Hlo & Hhi & _ & Htp & _).
  refine (conj M1 (conj W1 (conj B1 (conj Hra (conj H16 (conj _ (conj _ (conj _ (conj _ (conj _ _)))))))))).
  - lia.
  - lia.
  - intros a Ha. apply S1. left. lia.
  - rewrite H4. exact Htp.
  - intros a Ha. apply S1. right. exact Ha.
  - intros E. rewrite Hinit in E. discriminate.
Qed.

Lemma cs_inv_call : forall Lk Ak mk mdk regsk K2 (E2 : Z -> Prop) L2 A2 regs2 m2 md2,
  cs_inv Lk Ak mk mdk ->
  call_post_k B (aa_MR API) K2 Lk Ak regsk mk mdk E2 L2 A2 regs2 m2 md2 ->
  spZ regs - CHECK_RESTAMP_STACK <= spZ regsk - K2 -> spZ regsk <= spZ regs ->
  (forall a, E2 a -> a < alloc_ceiling /\ ~ in_img B a) ->
  (length (st_regions Ak) <= length (st_regions A2))%nat ->
  (forall p k, In (p, k) (user_blocks A) -> In (p, k) (user_blocks A2)) ->
  ro_agree (ms_segs B) m2 -> guard_kept B mk m2 ->
  cs_inv L2 A2 m2 md2.
Proof.
  intros Lk Ak mk mdk regsk K2 E2 L2 A2 regs2 m2 md2 (I1 & I2 & I3 & I4 & I5) Hpost H1 H2 HE HL HU Hro Hg.
  pose proof PRE as (HM & _ & _ & _ & _ & Hlo & Hhi & _).
  pose proof alloc_ceiling_value as Hc.
  destruct (kb_mid_call B API _ _ _ _ _ _ _ _ _ _ _ _ Hpost) as [Hmid _].
  split.
  { apply (eg_drop B API _ _ _ _ _ _ (fun a => False \/ E2 a)).
    - eapply (eg_seq B API AX CT); [exact HM | exact I1 | exact Hmid | lia | lia | lia | lia | | exact I2 | exact I3].
      intros a Ha _ He. destruct (HE a He) as [Ha' _]. lia.
    - intros a [[]|He]. exact (HE a He). }
  split; [lia|]. split; [exact HU|]. split; [exact Hro|].
  intros i Hi. rewrite (Hg i Hi). exact (I5 i Hi).
Qed.

Lemma cs_inv_A : forall Lk Ak mk mdk mk' W,
  cs_inv Lk Ak mk mdk ->
  Frame.munch W mk mk' -> Frame.wmono (ms_segs B) mk mk' -> (forall x, mk x <> None -> mk' x <> None) ->
  (forall x, 0 <= x < 2 ^ 64 -> ~ Frame.outside W x ->
     (spZ regs - CHECK_RESTAMP_STACK <= x < spZ regs) \/
     (x < alloc_ceiling /\ ~ in_img B x /\ ~ owned B Lk Ak x /\
      forall p k i, In (p, k) (user_blocks A) -> 0 <= i < k -> ptr_addr L p + i <> x)) ->
  ro_agree (ms_segs B) mk' ->
  cs_inv Lk Ak mk' mdk.
Proof.
  intros Lk Ak mk mdk mk' W (I1 & I2 & I3 & I4 & I5) Hm Hw Hp HW Hro.
  pose proof PRE as (HM & _ & _ & _ & _ & Hlo & Hhi & _).
  pose proof alloc_ceiling_value as Hc.
  pose proof (eg_img_low B SEGS) as HIL.
  pose proof I1 as (M1 & _).
  split.
  { apply (eg_drop B API _ _ _ _ _ _
      (fun x => False \/ (0 <= x < 2 ^ 64 /\ ~ Frame.outside W x /\ ~ (spZ regs - CHECK_RESTAMP_STACK <= x < spZ regs)))).
    - apply (kb_mid_tail B API HIL _ _ _ _ _ _ _ Lk Ak mk mdk mk' W); [exact I1 | exact Hm | exact Hw | exact Hp | | |].
      + intros x Hx Hs He. destruct (kb_outside_dec W x) as [Ho|Ho]; [exact Ho|]. exfalso. apply He. tauto.
      + intros x Hx Ho. destruct (kb_outside_dec W x) as [Hout|Hout]; [exact Hout|]. exfalso.
        destruct (HW x ltac:(lia) Hout) as [Hs | (_ & _ & H3 & _)]; [lia | exact (H3 Ho)].
      + intros p k i Hin Hin' Hi. destruct (kb_outside_dec W (ptr_addr L p + i)) as [Hout|Hout]; [exact Hout|].
        exfalso. destruct (mr_blocks_range _ _ (aa_laws API) _ _ _ _ p k HM Hin) as [Hr1 Hr2].
        destruct (HW (ptr_addr L p + i) ltac:(lia) Hout) as [Hs | (_ & _ & _ & H4)];
          [lia | exact (H4 p k i Hin Hi eq_refl)].
    - intros x [[]|(Hx & Ho & Hs)].
      destruct (HW x Hx Ho) as [H|(H1 & H2 & _)]; [contradiction | split; assumption]. }
  split; [exact I2|]. split; [exact I3|]. split; [exact Hro|].
  intros i Hi. rewrite <- (I5 i Hi).
  assert (Ho : owned B Lk Ak (ms_got_guard B + i))
    by (right; unfold static_owned; right; right; right; right; left; lia).
  pose proof (mr_owned_low _ _ (aa_laws API) _ _ _ _ _ M1 Ho) as Hr.
  apply (mbyte_munch (ms_segs B) W mk mk'); [exact Hm | lia |].
  destruct (kb_outside_dec W (ms_got_guard B + i)) as [Hout|Hout]; [exact Hout|]. exfalso.
  destruct (HW (ms_got_guard B + i) ltac:(lia) Hout) as [Hs | (_ & _ & H3 & _)]; [lia | exact (H3 Ho)].
Qed.

Lemma cs_free_keep : forall Lk Ak mk mdk p k0,
  cs_inv Lk Ak mk mdk -> In (p, k0) (user_blocks Ak) -> 0 < k0 ->
  (forall y, In y (blocks L A) -> ranges_disjoint (ptr_addr Lk p, k0) y) ->
  forall q k, In (q, k) (user_blocks A) -> q <> p.
Proof.
  intros Lk Ak mk mdk p k0 ((M1 & W1 & _ & _ & P1 & _) & _ & I3 & _) Hp Hn HD q k Hq Eq. subst q.
  pose proof (I3 p k Hq) as Hpk.
  pose proof (user_block_ptrs_NoDup Ak W1) as ND.
  pose proof (eg_fst_unique _ p k k0 ND Hpk Hp) as Ek. subst k.
  pose proof (HD _ (eg_ub L A p k0 Hq)) as D.
  rewrite (P1 p k0 Hq Hpk) in D. unfold ranges_disjoint in D. cbn [fst snd] in D. lia.
Qed.

Lemma cs_frame_call : forall Lk Ak mk mdk regsk K2 (E2 : Z -> Prop) L2 A2 regs2 m2 md2,
  cs_inv Lk Ak mk mdk -> cs_frame mk ->
  call_post_k B (aa_MR API) K2 Lk Ak regsk mk mdk E2 L2 A2 regs2 m2 md2 ->
  spZ regsk <= spZ regs - 48 -> (forall a, E2 a -> a < alloc_ceiling) ->
  cs_frame m2.
Proof.
  intros Lk Ak mk mdk regsk K2 E2 L2 A2 regs2 m2 md2 ((M1 & _) & _) (junk & FR) Hpost Hsp HE.
  pose proof Hpost as (M2 & _ & _ & _ & _ & _ & _ & Hfr & _).
  pose proof PRE as (_ & _ & _ & _ & _ & Hlo & Hhi & _).
  pose proof alloc_ceiling_value as Hc.
  exists junk. rewrite <- SEGS in FR |- *.
  apply (eg_cells_mb B mk m2 _ _ FR). intros i Hi. change (Z.of_nat (Cells.cells_size _)) with 48 in Hi.
  assert (HK0 : CHECK_RESTAMP_STACK = 8240) by reflexivity.
  assert (Hr : alloc_ceiling <= spZ regs - 48 + i < 2 ^ 64) by lia.
  destruct (Hfr (spZ regs - 48 + i)) as [E W].
  - left. exact Hr.
  - intros Ho. pose proof (mr_owned_low _ _ (aa_laws API) _ _ _ _ _ M1 Ho). lia.
  - intros Ho. pose proof (mr_owned_low _ _ (aa_laws API) _ _ _ _ _ M2 Ho). lia.
  - unfold scratch_k. lia.
  - intros He. pose proof (HE _ He). lia.
  - split; [exact E | intros Hw; apply W; exact Hw].
Qed.

Lemma cs_inv_kept : forall Lk Ak mk mdk, cs_inv Lk Ak mk mdk -> blocks_kept B L A mem mk (fun _ => False).
Proof.
  intros Lk Ak mk mdk ((_ & _ & _ & _ & _ & _ & _ & K1 & _) & _ & I3 & _) a k i Hin _ Hi.
  destruct (eg_bu L A a k Hin) as (p & Hp & <-). exact (K1 p k i Hp (I3 p k Hp) Hi).
Qed.

Lemma cs_keep_pres : forall r r', cs_keep r -> regs_preserved r r' -> cs_keep r'.
Proof.
  intros r r' (K3 & K4 & K20 & K21 & K22 & K23 & K24 & K25 & K26 & K27) Hp.
  refine (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ _))))))))).
  - transitivity (getr r 3); [apply (Hp 3); unfold callee_saved; lia | exact K3].
  - transitivity (getr r 4); [apply (Hp 4); unfold callee_saved; lia | exact K4].
  - transitivity (getr r 20); [apply (Hp 20); unfold callee_saved; lia | exact K20].
  - transitivity (getr r 21); [apply (Hp 21); unfold callee_saved; lia | exact K21].
  - transitivity (getr r 22); [apply (Hp 22); unfold callee_saved; lia | exact K22].
  - transitivity (getr r 23); [apply (Hp 23); unfold callee_saved; lia | exact K23].
  - transitivity (getr r 24); [apply (Hp 24); unfold callee_saved; lia | exact K24].
  - transitivity (getr r 25); [apply (Hp 25); unfold callee_saved; lia | exact K25].
  - transitivity (getr r 26); [apply (Hp 26); unfold callee_saved; lia | exact K26].
  - transitivity (getr r 27); [apply (Hp 27); unfold callee_saved; lia | exact K27].
Qed.

Lemma cs_heap_E : forall Lk Ak mk mdk p k, aa_MR API Lk Ak mk mdk -> In (p, k) (user_blocks Ak) ->
  forall a, ptr_addr Lk p <= a < ptr_addr Lk p + k -> a < alloc_ceiling /\ ~ in_img B a.
Proof.
  intros Lk Ak mk mdk p k HMk Hp a Ha.
  destruct (mr_blocks_range _ _ (aa_laws API) _ _ _ _ p _ HMk Hp) as [Hr1 Hr2].
  split; [lia|]. replace a with (ptr_addr Lk p + (a - ptr_addr Lk p)) by lia.
  exact (ax_blocks_img AX Lk Ak mk mdk p k (a - ptr_addr Lk p) HMk Hp ltac:(lia)).
Qed.

(* The tail call: free(c) at the entry sp, returning to the caller's ra. *)
Lemma cs_ph3 : forall (fx7 : FPState) L1 A1 regs7 m7 md1 c d1 d2,
  frm_zero (@fp_csr fx7) ->
  cs_inv L1 A1 m7 md1 -> st_init_done A1 = true ->
  blocks L1 A1 = d1 ++ (c, n) :: d2 -> blocks L A = d1 ++ d2 -> 0 < n ->
  res_ok_slots A1 (sb_malloc b n) ->
  getr regs7 1 = getr regs 1 -> spZ regs7 = spZ regs -> getr regs7 10 = Z_to_bv 64 c ->
  regs_preserved regs regs7 ->
  SR (ms_segs B) (mkCfg (@mkst fx7 regs7 (Z_to_bv 64 CS_FREE) m7 (seg_rom (ms_segs B))) md1) cs_final.
Proof.
  intros fx7 L1 A1 regs7 m7 md1 c d1 d2 Hfrm I Hinit Hb1 Hb0 Hn Hres G1 S7 G10 P7.
  pose proof PRE as (HM & HWF & HB & Hra & H16 & Hlo & Hhi & HW & Htp & Herr & Haux).
  pose proof alloc_ceiling_value as Hc.
  assert (HK0 : CHECK_RESTAMP_STACK = 8240) by reflexivity.
  pose proof I as ((M1 & W1 & B1 & _) & I2 & I3 & I4 & I5).
  destruct (eg_bu L1 A1 c _ ltac:(rewrite Hb1; apply eg_in_mid)) as (p & Hp & Ep).
  assert (Hpre7 : call_pre B (aa_MR API) L1 A1 regs7 m7 md1).
  { apply (proj2 (call_pre_k_alloc B (aa_MR API) L1 A1 regs7 m7 md1)).
    apply (cs_pre L1 A1 m7 md1 regs7 0 ALLOC_STACK I); [lia | lia | unfold ALLOC_STACK; lia
      | rewrite HK0; unfold ALLOC_STACK; lia | rewrite S7; exact H16
      | exact (P7 4 ltac:(unfold callee_saved; lia)) | rewrite G1; exact Hra | exact Hinit]. }
  replace (Z_to_bv 64 CS_FREE) with (Z_to_bv 64 (ms_free B)) by (rewrite FREEPC; reflexivity).
  eapply SR_bind.
  { apply (FREE fx7 L1 A1 regs7 m7 md1 p n (sb_malloc b n) Hpre7 I4 Hp).
    - rewrite G10, Ep. reflexivity.
    - exact Hres. }
  intros c' (L6 & A6 & regs12 & m12 & md6 & -> & Hpost & (e1 & e2 & Hd1 & Hd2) & Hkept & Hro6 & Hgk6 & Hub6 &
    Hinit6 & Hlen6 & Hres6).
  apply call_post_k_alloc in Hpost.
  rewrite Ep in Hd1.
  assert (PW1 : pairwise ranges_disjoint (d1 ++ (c, n) :: d2))
    by (rewrite <- Hb1; exact (mr_blocks_disjoint _ _ (aa_laws API) _ _ _ _ M1)).
  assert (ND1 : ~ In (c, n) (d1 ++ d2)) by (apply (eg_notin d1 d2 _ PW1); cbn; lia).
  assert (Hb6 : blocks L6 A6 = blocks L A).
  { rewrite Hd2, Hb0. symmetry. apply (eg_rm (c, n) d1 d2 e1 e2 ND1). rewrite <- Hb1. exact Hd1. }
  assert (HD1 : forall y, In y (blocks L A) -> ranges_disjoint (ptr_addr L1 p, n) y).
  { intros y Hy. rewrite Ep. apply (eg_pw_mid d1 d2 _ y PW1). rewrite <- Hb0. exact Hy. }
  assert (HU6 : forall q k, In (q, k) (user_blocks A) -> In (q, k) (user_blocks A6)).
  { intros q k Hq. apply Hub6; [exact (I3 q k Hq) | exact (cs_free_keep L1 A1 m7 md1 p _ I Hp ltac:(lia) HD1 q k Hq)]. }
  assert (I6 : cs_inv L6 A6 m12 md6).
  { apply (cs_inv_call L1 A1 m7 md1 regs7 ALLOC_STACK _ L6 A6 regs12 m12 md6 I Hpost);
      [rewrite S7, HK0; unfold ALLOC_STACK; lia | lia | exact (cs_heap_E L1 A1 m7 md1 p _ M1 Hp) | exact Hlen6
      | exact HU6 | exact Hro6 | exact Hgk6]. }
  apply SR_ret. exists fx7, L6, A6, regs12, m12, md6.
  split; [rewrite G1; reflexivity|].
  split; [exact Hfrm|].
  split.
  { destruct I6 as (I6a & _). apply (kb_post B API); [exact I6a|].
    exact (kb_preserved_trans _ _ _ P7 (proj2 (kb_mid_call B API _ _ _ _ _ _ _ _ _ _ _ _ Hpost))). }
  split; [exact Hb6|].
  split; [exact (cs_inv_kept _ _ _ _ I6)|].
  destruct I6 as (_ & _ & _ & Hro' & Hg').
  split; [exact Hg'|]. split; [exact Hro'|].
  split; [rewrite sb_free_malloc in Hres6; exact Hres6 | intros _; exact (Hinit6 Hinit)].
Qed.

(* After malloc: the body on the normalized memory (cs_seg2), then the tail call. *)
Lemma cs_ph2 : forall L1 A1 regs2 m2 md1 c d1 d2,
  cs_inv L1 A1 m2 md1 -> st_init_done A1 = true ->
  blocks L1 A1 = d1 ++ (c, n) :: d2 -> blocks L A = d1 ++ d2 -> 18 <= n ->
  res_ok_slots A1 (sb_malloc b n) ->
  getr regs2 2 = Z_to_bv 64 (spZ regs - 48) -> getr regs2 8 = Z_to_bv 64 n -> getr regs2 10 = Z_to_bv 64 c ->
  getr regs2 18 = Z_to_bv 64 f -> getr regs2 19 = Z_to_bv 64 ctr -> cs_keep regs2 -> cs_frame m2 ->
  SR (ms_segs B) (mkCfg (mkst regs2 (Z_to_bv 64 0x12ea8) m2 (seg_rom (ms_segs B))) md1) cs_final.
Proof.
  intros L1 A1 regs2 m2 md1 c d1 d2 I Hinit Hb1 Hb0 Hn18 Hres G2 G8 G10 G18 G19 GK (junk & FR).
  pose proof PRE as (HM & HWF & HB & Hra & H16 & Hlo & Hhi & HW & Htp & Herr & Haux).
  pose proof alloc_ceiling_value as Hc.
  assert (HK0 : CHECK_RESTAMP_STACK = 8240) by reflexivity.
  pose proof I as ((M1 & W1 & B1 & _) & I2 & I3 & I4 & I5).
  destruct (kb_md B API L1 A1 m2 md1 M1) as [Hh Hlz].
  pose proof (eg_img_low B SEGS) as HIL.
  assert (S2 : spZ regs2 = spZ regs - 48) by (unfold spZ at 1; rewrite G2; apply MState.unsigned_lit; lia).
  assert (Hro' : ro_agree rsegs m2) by (rewrite <- SEGS; exact I4).
  assert (InC : In (c, n) (blocks L1 A1)) by (rewrite Hb1; apply eg_in_mid).
  destruct (cs_blk L1 A1 m2 md1 c n M1 InC) as (HC1 & HC2 & _ & HCi).
  pose proof IB as (q & k & Hq & Hq1 & Hq2).
  destruct (cs_blk L A mem md q k HM Hq) as (HQ1 & HQ2 & _).
  assert (Hq' : In (q, k) (d1 ++ d2)) by (rewrite <- Hb0; exact Hq).
  assert (HqL1 : In (q, k) (blocks L1 A1)) by (rewrite Hb1; apply eg_in_ins; exact Hq').
  destruct (cs_blk L1 A1 m2 md1 q k M1 HqL1) as (_ & _ & _ & HQi).
  assert (PW1 : pairwise ranges_disjoint (d1 ++ (c, n) :: d2))
    by (rewrite <- Hb1; exact (mr_blocks_disjoint _ _ (aa_laws API) _ _ _ _ M1)).
  pose proof (cs_pw _ _ _ _ _ _ PW1 Hq') as DCQ.
  assert (PN : forall a, present m2 a -> ~ in_img B a -> 0 <= a < 2 ^ 64 ->
                 exists bb, normalize rsegs m2 (Z_to_bv 64 a) = Some bb).
  { intros a [bb Hbb] Hni Ha. exists bb. unfold normalize. cbv beta.
    pose proof (eg_ro_false B a Ha (eg_fs_none B SEGS a Hni)) as E. rewrite SEGS in E. unfold Mem.wa in E.
    rewrite E. exact Hbb. }
  assert (CJx : exists cj, Step.rw_cells rsegs (normalize rsegs m2) c [Cells.CB (Z.to_nat n) cj]).
  { apply cs_cells_of; [lia | lia |].
    intros i Hi. destruct (HCi i ltac:(lia)) as (X1 & X2 & _). apply PN; [exact X1 | exact X2 | lia]. }
  destruct CJx as (cj & CJ).
  assert (FJx : exists src, Step.rw_cells rsegs (normalize rsegs m2) f [Cells.CB (Z.to_nat n) src]).
  { apply cs_cells_of; [lia | lia |].
    intros i Hi. destruct (HQi (f - q + i) ltac:(lia)) as (X1 & X2 & _).
    replace (q + (f - q + i)) with (f + i) in X1, X2 by ring. apply PN; [exact X1 | exact X2 | lia]. }
  destruct FJx as (src & FJ).
  destruct FJ as [[FW FB] _]. cbn [Cells.cells_bytes Cells.cbytes] in FB. rewrite app_nil_r in FB.
  cbn in FW. destruct FW as [FL _].
  assert (FRn : Step.rw_cells rsegs (normalize rsegs m2) (spZ regs - 48) [Cells.CB 8 junk; Cells.C8 (getr regs 19);
    Cells.C8 (getr regs 18); Cells.C8 (getr regs 9); Cells.C8 (getr regs 8); Cells.C8 (getr regs 1)]).
  { apply (cs_cells_norm m2 _ _ Hro' FR). intros i Hi. change (Z.of_nat (Cells.cells_size _)) with 48 in Hi.
    pose proof (eg_ro_false B (spZ regs - 48 + i) ltac:(lia) (eg_fs_high B HIL (spZ regs - 48 + i) ltac:(lia))) as E.
    rewrite SEGS in E. exact E. }
  eapply (eg_runN B SEGS regs2 _ m2 md1); [exact Hh | exact Hlz | exact Hro' | | |].
  { unfold rmk. rewrite G8, G10, G18, G19.
    eapply (cs_seg2 MCPY RST BCMP); rewrite ?MState.unsigned_lit by lia;
      try change (bv_unsigned (getr regs2 2)) with (spZ regs2); rewrite ?S2;
      first [ lia | exact (mem_inv_normalize rsegs m2) | exact FRn | exact CJ | exact FB | exact FL ]. }
  { intros ms (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & -> & _).
    repeat split; reflexivity. }
  intros ms s0 regs7 (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & -> &
    MU & WM) Hrel Hsame Hg7.
  destruct Hrel as (_ & _ & _ & _ & _ & _ & _ & HR). cbn [ms_mem MState.MS] in HR.
  rewrite !MState.unsigned_lit in MU by lia.
  set (W := [(c, c + n)]) in MU.
  pose proof (mem_rel_normalize rsegs m2 Hro') as HR6.
  pose proof (munch_rel rsegs _ m2 _ (ms_mem ms) m' HR6 HR Hsame MU) as MU7.
  pose proof (wmono_rel rsegs m2 _ (ms_mem ms) m' HR6 HR Hsame WM) as WM7.
  pose proof (ro_agree_same rsegs m2 (ms_mem ms) Hro' Hsame) as RO7.
  rewrite <- SEGS in WM7, RO7.
  assert (HinW : forall x, ~ Frame.outside W x -> c <= x < c + n)
    by (intros x Hx; unfold W in Hx; cbn [Frame.outside] in Hx; lia).
  assert (PRES : forall x, m2 x <> None -> ms_mem ms x <> None).
  { intros x Hx. destruct (kb_outside_dec W (bv_unsigned x)) as [Hout|Hout]; [rewrite (MU7 x Hout); exact Hx|].
    apply (eg_pres B m2 (ms_mem ms) x); [| exact (WM7 x) | exact Hx].
    pose proof (HinW _ Hout) as Hs.
    apply (eg_fs_none B SEGS). destruct (HCi (bv_unsigned x - c) ltac:(lia)) as (_ & Hni & _).
    replace (c + (bv_unsigned x - c)) with (bv_unsigned x) in Hni by ring. exact Hni. }
  assert (HWW : forall x, 0 <= x < 2 ^ 64 -> ~ Frame.outside W x ->
     (spZ regs - CHECK_RESTAMP_STACK <= x < spZ regs) \/
     (x < alloc_ceiling /\ ~ in_img B x /\ ~ owned B L1 A1 x /\
      forall p k i, In (p, k) (user_blocks A) -> 0 <= i < k -> ptr_addr L p + i <> x)).
  { intros x Hx Hout. pose proof (HinW _ Hout) as Hs. right.
    destruct (HCi (x - c) ltac:(lia)) as (_ & Hn1 & Hn2).
    replace (c + (x - c)) with x in Hn1, Hn2 by ring.
    split; [lia|]. split; [exact Hn1|]. split; [exact Hn2|].
    intros p k0 i Hp Hi E. assert (Y : In (ptr_addr L p, k0) (d1 ++ d2)) by (rewrite <- Hb0; exact (eg_ub L A p k0 Hp)).
    pose proof (cs_pw _ _ _ _ _ _ PW1 Y). lia. }
  pose proof (cs_inv_A L1 A1 m2 md1 (ms_mem ms) W I MU7 WM7 PRES HWW RO7) as I7.
  assert (G7a : getr regs7 1 = getr regs 1) by (rewrite Hg7; reflexivity).
  assert (G7b : getr regs7 2 = Z_to_bv 64 (bv_unsigned (getr regs2 2) + 48)) by (rewrite Hg7; reflexivity).
  change (bv_unsigned (getr regs2 2)) with (spZ regs2) in G7b. rewrite S2 in G7b.
  replace (spZ regs - 48 + 48) with (spZ regs) in G7b by lia.
  assert (S7 : spZ regs7 = spZ regs) by (unfold spZ at 1; rewrite G7b; apply MState.unsigned_lit; lia).
  assert (G7c : getr regs7 10 = Z_to_bv 64 c) by (rewrite Hg7; reflexivity).
  assert (P7 : regs_preserved regs regs7).
  { destruct GK as (K3 & K4 & K20 & K21 & K22 & K23 & K24 & K25 & K26 & K27).
    assert (Hs : getr regs7 2 = getr regs 2) by (rewrite G7b; unfold spZ; apply Z_to_bv_bv_unsigned).
    intros r Hr. unfold callee_saved in Hr.
    assert (C : r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/
                r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia.
    destruct C as [->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->| ->]]]]]]]]]]]]]];
      first [exact Hs | rewrite Hg7; first [reflexivity | exact K3 | exact K4 | exact K20 | exact K21 | exact K22
        | exact K23 | exact K24 | exact K25 | exact K26 | exact K27]]. }
  apply (cs_ph3 (mkFP fp_regs fp_csr) L1 A1 regs7 (ms_mem ms) md1 c d1 d2 FRM I7 Hinit Hb1 Hb0 ltac:(lia) Hres
    G7a S7 G7c P7).
Qed.

Lemma cs_entry :
  SR (ms_segs B) (mkCfg (mkst regs (Z_to_bv 64 CHECK_RESTAMP) mem (seg_rom (ms_segs B))) md) cs_final.
Proof.
  pose proof PRE as (HM & HWF & HB & Hra & H16 & Hlo & Hhi & HW & Htp & Herr & Haux).
  pose proof alloc_ceiling_value as Hc.
  assert (HK0 : CHECK_RESTAMP_STACK = 8240) by reflexivity.
  pose proof (eg_img_low B SEGS) as HIL.
  destruct (kb_md B API L A mem md HM) as [Hh Hlz].
  assert (I0 : cs_inv L A mem md).
  { split.
    { apply (kb_mid_refl B API); [exact HM | exact HWF | exact HB |].
      intros a [Ha|Ha]; [exact (HW a Ha) | exact (Herr a Ha)]. }
    split; [lia|]. split; [intros p k Hp; exact Hp|]. split; [exact RO|]. intros i Hi. reflexivity. }
  assert (ST : Frame.stk rsegs mem (spZ regs - CHECK_RESTAMP_STACK) (spZ regs))
    by (rewrite <- SEGS; exact (kb_stk B API HIL CHECK_RESTAMP_STACK L A regs mem md PRE ltac:(lia))).
  assert (Hout : forall x, ~ Frame.outside [(spZ regs - 48, spZ regs)] x -> spZ regs - 48 <= x < spZ regs)
    by (intros x Hx; cbn [Frame.outside] in Hx; lia).
  assert (FRAME : forall m1, Frame.munch [(spZ regs - 48, spZ regs)] mem m1 -> Frame.wmono rsegs mem m1 ->
    cs_inv L A m1 md /\ ro_agree (ms_segs B) m1 /\ Frame.wmono (ms_segs B) mem m1).
  { intros m1 MU WM.
    assert (WM' : Frame.wmono (ms_segs B) mem m1) by (rewrite SEGS; exact WM).
    assert (Hro1 : ro_agree (ms_segs B) m1).
    { apply (eg_ro_munch B _ mem m1 RO MU). intros a Ha Ho. apply (eg_fs_high B HIL). pose proof (Hout a Ho). lia. }
    split; [|split; [exact Hro1 | exact WM']].
    apply (cs_inv_A L A mem md m1 _ I0 MU WM').
    - intros x Hx. destruct (kb_outside_dec [(spZ regs - 48, spZ regs)] (bv_unsigned x)) as [Ho|Ho];
        [rewrite (MU x Ho); exact Hx|].
      apply (eg_pres B mem m1 x); [| exact (WM' x) | exact Hx].
      apply (eg_fs_high B HIL). pose proof (Hout _ Ho). lia.
    - intros x _ Ho. left. pose proof (Hout x Ho). lia.
    - exact Hro1. }
  destruct (Z_lt_ge_dec n 18) as [Hs|Hs].
  - (* n < 18: it returns at once *)
    eapply (eg_runA B SEGS regs _ mem md); [exact Hh | exact Hlz | | |].
    { unfold rmk. rewrite R10, R11, R12.
      eapply cs_short; [exact ST | unfold spZ; lia | rewrite MState.unsigned_lit by lia; lia]. }
    { intros ms (t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m1 & -> & _).
      repeat split; reflexivity. }
    intros ms regs1 (t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m1 & -> &
      MU & WM) Hg1.
    cbn [MState.MS ms_pc_val ms_mem].
    rewrite (kb_ret_pc _ Hra).
    change (bv_unsigned (getr regs 2)) with (spZ regs) in MU.
    destruct (FRAME m1 MU WM) as (I1 & _ & _).
    apply SR_ret. exists fx, L, A, regs1, m1, md.
    split; [reflexivity|]. split; [exact FRM|].
    split.
    { destruct I1 as (I1a & _). apply (kb_post B API); [exact I1a|].
      intros r Hr. unfold callee_saved in Hr.
      assert (C : r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/
                  r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia.
      destruct C as [->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->| ->]]]]]]]]]]]]]];
        rewrite Hg1; reflexivity. }
    split; [reflexivity|].
    split; [exact (cs_inv_kept _ _ _ _ I1)|].
    destruct I1 as (_ & _ & _ & Hro' & Hg').
    split; [exact Hg'|]. split; [exact Hro'|]. split; [exact RES | intros H; exact H].
  - (* 18 <= n: the copy, the checks, free *)
    eapply (eg_runA B SEGS regs _ mem md); [exact Hh | exact Hlz | | |].
    { unfold rmk. rewrite R10, R11, R12.
      eapply cs_seg1; [exact ST | unfold spZ; lia | rewrite MState.unsigned_lit by lia; lia]. }
    { intros ms (t0' & t1' & t2' & a1' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m1 & junk & -> & _).
      repeat split; reflexivity. }
    intros ms regs1 (t0' & t1' & t2' & a1' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m1 & junk & -> &
      MU & WM & FR1) Hg1.
    cbn [MState.MS ms_pc_val ms_mem].
    change (bv_unsigned (getr regs 2)) with (spZ regs) in MU, FR1.
    assert (G1a : getr regs1 1 = Z_to_bv 64 0x12ea8) by (rewrite Hg1; reflexivity).
    assert (G1b : getr regs1 2 = Z_to_bv 64 (spZ regs - 48)) by (rewrite Hg1; reflexivity).
    assert (G1c : getr regs1 10 = Z_to_bv 64 n) by (rewrite Hg1; reflexivity).
    assert (G1d : getr regs1 8 = Z_to_bv 64 n) by (rewrite Hg1; reflexivity).
    assert (G1e : getr regs1 18 = Z_to_bv 64 f) by (rewrite Hg1; reflexivity).
    assert (G1f : getr regs1 19 = Z_to_bv 64 ctr) by (rewrite Hg1; reflexivity).
    assert (K1 : cs_keep regs1).
    { unfold cs_keep. repeat match goal with |- _ /\ _ => split end; rewrite Hg1; reflexivity. }
    assert (S1 : spZ regs1 = spZ regs - 48) by (unfold spZ at 1; rewrite G1b; apply MState.unsigned_lit; lia).
    destruct (FRAME m1 MU WM) as (I1 & Hro1 & WM').
    assert (FR1' : cs_frame m1) by (exists junk; exact FR1).
    assert (Hpre1 : call_pre B (aa_MR API) L A regs1 m1 md).
    { apply (proj2 (call_pre_k_alloc B (aa_MR API) L A regs1 m1 md)).
      apply (kb_pre_A B API CHECK_RESTAMP_STACK 48 ALLOC_STACK L A regs mem md regs1 m1 [(spZ regs - 48, spZ regs)]
        PRE); [lia | unfold ALLOC_STACK; lia | rewrite HK0; unfold ALLOC_STACK; lia | exact S1
        | rewrite S1; replace (spZ regs - 48) with (spZ regs + (-3) * 16) by lia; rewrite Z_mod_plus_full; exact H16
        | rewrite Hg1; reflexivity | rewrite G1a; unfold YK0s.ret_ok; apply bv_eq; vm_compute; reflexivity
        | exact MU | exact WM' | |].
      - intros x _ Hx. cbn [Frame.outside]. split; [lia | exact I].
      - intros x Hx _. cbn [Frame.outside]. split; [lia | exact I]. }
    replace (Z_to_bv 64 CS_MALLOC) with (Z_to_bv 64 (ms_malloc B)) by (rewrite MALPC; reflexivity).
    eapply SR_bind.
    { exact (MALLOC L A regs1 m1 md n b Hpre1 Hro1 G1c RES ROOM). }
    intros c' (L1 & A1 & regs2 & m2 & md1 & res & -> & Hpost & G2 & _ & _ & _ & (d1 & d2 & Hb1 & Hb0) & _ & Hro2 &
      Hgk2 & HU1 & Hinit1 & Hlen1 & Hres1).
    pose proof Hpost as (_ & _ & _ & _ & _ & Hp2 & _).
    assert (I1' : cs_inv L1 A1 m2 md1).
    { apply (cs_inv_call L A m1 md regs1 ALLOC_STACK _ L1 A1 regs2 m2 md1 I1 Hpost);
        [rewrite S1, HK0; unfold ALLOC_STACK; lia | lia | intros a [] | exact Hlen1 | exact HU1 | exact Hro2
        | exact Hgk2]. }
    assert (FR2 : cs_frame m2).
    { apply (cs_frame_call L A m1 md regs1 ALLOC_STACK _ L1 A1 regs2 m2 md1 I1 FR1' Hpost); [lia | intros a []]. }
    rewrite G1a.
    apply (cs_ph2 L1 A1 regs2 m2 md1 res d1 d2 I1' Hinit1 Hb1 Hb0 ltac:(lia) Hres1).
    + transitivity (getr regs1 2); [apply (Hp2 2); unfold callee_saved; lia | exact G1b].
    + transitivity (getr regs1 8); [apply (Hp2 8); unfold callee_saved; lia | exact G1d].
    + exact G2.
    + transitivity (getr regs1 18); [apply (Hp2 18); unfold callee_saved; lia | exact G1e].
    + transitivity (getr regs1 19); [apply (Hp2 19); unfold callee_saved; lia | exact G1f].
    + exact (cs_keep_pres regs1 regs2 K1 Hp2).
    + exact FR2.
Qed.

End Body.

Theorem check_restamp_holds : check_restamp_contract B API.
Proof.
  intros L A regs mem md f n ctr b _ H1 H2 H3 H4 H5 H6 H7 H8 H9 H10.
  eapply cs_entry; eassumption.
Qed.
End CRS.
