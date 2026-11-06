(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/openssl/ct/lib/CtColB/W_set0A.v, with its module paths and module names changed; 604 of its 627 lines of code are new or changed and 122 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_scene/lib/Prog/check_step.v, with its module names changed; 305 of its 333 lines of code are new or changed and 599 lines of the source are left out. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame Tac Bytes Image Arr ZBridge.
From OSSVerify.Proofs.libreac.fuzz_scene.lib Require Import Img0.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Prog Require Import SceneTac memset_c reac_ctrl_build_scene_step_c check_step_c SegBX.
Import ListNotations.
Open Scope Z_scope.

Lemma lxor_small : forall x, 0 <= x < 2^63 -> Z.lxor x 9223372036854775808 = x + 9223372036854775808.
Proof.
  intros x Hx. rewrite <- Z.add_nocarry_lxor; [reflexivity|].
  apply Z.bits_inj'. intros n Hn. rewrite Z.land_spec, Z.bits_0.
  change 9223372036854775808 with (2^63). rewrite Z.pow2_bits_eqb by lia.
  destruct (Z.eqb_spec 63 n); [|apply andb_false_r].
  subst n. rewrite Z.bits_above_log2; [reflexivity|lia|].
  destruct (Z.eq_dec x 0); [subst; cbn; lia|]. apply Z.log2_lt_pow2; lia.
Qed.

Lemma lxor_flip : forall x, -9223372036854775808 <= x < 9223372036854775808 ->
  Z.lxor (x mod 18446744073709551616) 9223372036854775808 = x + 9223372036854775808.
Proof.
  intros x Hx. destruct (Z.leb_spec 0 x).
  - rewrite Z.mod_small by lia. apply lxor_small. lia.
  - replace (x mod 18446744073709551616) with (Z.lxor (x + 9223372036854775808) 9223372036854775808).
    + rewrite Z.lxor_assoc, Z.lxor_nilpotent, Z.lxor_0_r. reflexivity.
    + rewrite lxor_small by lia. Z.div_mod_to_equations. lia.
Qed.

Lemma sx16_range : forall w, 0 <= w < 65536 -> -32768 <= sx16 w < 32768.
Proof. intros w Hw. unfold sx16. destruct (Z.ltb_spec w 32768); lia. Qed.

Lemma sx_back : forall x, -32768 <= x < 32768 ->
  Z.shiftr (bv_signed (Z_to_bv 64 (Z.shiftl x 48))) 48 = x.
Proof.
  intros x Hx. rewrite zb_signed, unsigned_lit_wrap, Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia.
  match goal with |- context [?a <? ?b] => destruct (Z.ltb_spec a b) end.
  all: Z.div_mod_to_equations; lia.
Qed.

Lemma sx_gen : forall u x, -32768 <= x < 32768 -> u mod 2^64 = x mod 2^64 ->
  Z.shiftr (bv_signed (Z_to_bv 64 (Z.shiftl u 48))) 48 = x.
Proof.
  intros u x Hx Hu.
  replace (Z_to_bv 64 (Z.shiftl u 48)) with (Z_to_bv 64 (Z.shiftl x 48)); [apply sx_back; exact Hx|].
  apply bv_eq. rewrite !unsigned_lit_wrap, !Z.shiftl_mul_pow2 by lia.
  rewrite <- (Z.mul_mod_idemp_l u) by lia. rewrite <- (Z.mul_mod_idemp_l x) by lia. rewrite Hu. reflexivity.
Qed.

Lemma s7_neg : forall v, 0 <= v < 65536 -> (sx16 (256 * (v / 256)) < 0 <-> sx16 v < 0).
Proof.
  intros v Hv. unfold sx16.
  destruct (Z.ltb_spec v 32768); destruct (Z.ltb_spec (256 * (v / 256)) 32768); Z.div_mod_to_equations; lia.
Qed.

Lemma a1_val : forall (b0 : bool) n v u7 u4, 0 <= v < 65536 -> b0 = negb (n =? 8904) ->
  u7 mod 2^64 = sx16 (256 * (v / 256)) mod 2^64 -> u4 mod 2^64 = sx16 v mod 2^64 ->
  Z_to_bv 64 (0 - Z.lor (Z.lor (Z.b2z b0)
      (Z.b2z (Z.lxor (Z.shiftr (bv_signed (Z_to_bv 64 (Z.shiftl u7 48))) 48 mod 18446744073709551616) 9223372036854775808 <? 9223372036854775808)))
      (Z.lxor (Z.b2z (Z.lxor (Z.shiftr (bv_signed (Z_to_bv 64 (Z.shiftl u4 48))) 48 mod 18446744073709551616) 9223372036854775808 <? 9223372036854776151)) 1))
  = Z_to_bv 64 (if (n =? 8904) && (0 <=? sx16 v) && (sx16 v <=? 342) then 0 else -1).
Proof.
  intros b0 n v u7 u4 Hv -> H7 H4.
  pose proof (sx16_range v Hv) as R1.
  assert (Hw : 0 <= 256 * (v / 256) < 65536) by (Z.div_mod_to_equations; lia).
  pose proof (sx16_range _ Hw) as R2. pose proof (s7_neg v Hv) as [SN1 SN2].
  rewrite (sx_gen u7 _ R2 H7). rewrite (sx_gen u4 _ R1 H4).
  rewrite (lxor_flip (sx16 (256 * (v / 256)))) by lia. rewrite (lxor_flip (sx16 v)) by lia.
  destruct (Z.eqb_spec n 8904); destruct (Z.leb_spec 0 (sx16 v)); destruct (Z.leb_spec (sx16 v) 342);
    destruct (Z.ltb_spec (sx16 (256 * (v / 256)) + 9223372036854775808) 9223372036854775808);
    destruct (Z.ltb_spec (sx16 v + 9223372036854775808) 9223372036854776151);
    cbn [negb andb Z.b2z]; try (exfalso; lia); reflexivity.
Qed.

Lemma ok_val : forall (blk bd s8 : word) n v, bv_unsigned blk <> 0 -> bv_unsigned bd <> 0 -> bv_unsigned s8 = n ->
  0 <= v < 65536 ->
  scene_step_ok blk bd s8 (Z_to_bv 64 (sx16 v)) = (n =? 8904) && (0 <=? sx16 v) && (sx16 v <=? 342).
Proof.
  intros blk bd s8 n v H1 H2 H3 Hv. pose proof (sx16_range v Hv) as R.
  unfold scene_step_ok. rewrite (proj2 (Z.eqb_neq _ _) H1), (proj2 (Z.eqb_neq _ _) H2), H3, unsigned_lit_wrap.
  cbn [negb andb].
  destruct (n =? 8904); cbn [andb]; [|reflexivity].
  destruct (Z.leb_spec 0 (sx16 v)).
  - rewrite Z.mod_small by lia. cbn [andb]. reflexivity.
  - cbn [andb]. apply Z.leb_gt. Z.div_mod_to_equations. lia.
Qed.

Lemma nbE_id : forall n, n <> 0 -> nbE n = n.
Proof. intros n H. unfold nbE. destruct (Z.eqb_spec n 0); lia. Qed.

Lemma nbE_range : forall n, 0 <= n < 65536 -> 1 <= nbE n < 65536.
Proof. intros n H. unfold nbE. destruct (Z.eqb_spec n 0); lia. Qed.

Lemma snez_val : forall x n, x = n -> 0 <= n -> (0 <? Z.lxor x 8904) = negb (n =? 8904).
Proof.
  intros x n -> Hn. destruct (Z.eqb_spec n 8904) as [->|NE]; [reflexivity|]. cbn [negb]. apply Z.ltb_lt.
  assert (0 <= Z.lxor n 8904) by (apply Z.lxor_nonneg; split; intros; lia).
  assert (Z.lxor n 8904 <> 0) by (rewrite Z.lxor_eq_0_iff; lia).
  lia.
Qed.

Lemma len8904 : forall (l : list byte), Z.of_nat (length l) = 8904 -> length l = 8904%nat.
Proof. intros l H. apply Nat2Z.inj. rewrite H. reflexivity. Qed.

Lemma nth_rep : forall (x d : byte) k j, (j < k)%nat -> nth j (repeat x k) d = x.
Proof.
  intros x d k. induction k as [|k IH]; intros j Hj; [lia|].
  destruct j as [|j]; cbn; [reflexivity|]. apply IH. lia.
Qed.

Lemma trailer_ro : forall x, TAIL_TRAILER_AT <= x < TAIL_TRAILER_AT + 12 -> ro_addr rsegs (wa x) = true.
Proof.
  intros x Hx.
  assert (Hall : forallb (fun j => ro_addr rsegs (wa (TAIL_TRAILER_AT + Z.of_nat j))) (seq 0 12) = true)
    by (vm_compute; reflexivity).
  rewrite forallb_forall in Hall. specialize (Hall (Z.to_nat (x - TAIL_TRAILER_AT)) ltac:(apply in_seq; lia)).
  rewrite Z2Nat.id in Hall by lia.
  replace (TAIL_TRAILER_AT + (x - TAIL_TRAILER_AT)) with x in Hall by lia. exact Hall.
Qed.

Lemma wr_trailer : forall m A, mem_inv rsegs m -> wr_at rsegs m A 34 ->
  TAIL_TRAILER_AT + 12 <= A \/ A + 34 <= TAIL_TRAILER_AT.
Proof.
  intros m A HMI (HA & HAn & HW).
  destruct (Z_le_gt_dec (TAIL_TRAILER_AT + 12) A) as [L|L]; [left; exact L|].
  destruct (Z_le_gt_dec (A + 34) TAIL_TRAILER_AT) as [L2|L2]; [right; exact L2|].
  exfalso.
  specialize (HW (Z.max A TAIL_TRAILER_AT - A) ltac:(lia)).
  replace (A + (Z.max A TAIL_TRAILER_AT - A)) with (Z.max A TAIL_TRAILER_AT) in HW by lia.
  pose proof (trailer_ro (Z.max A TAIL_TRAILER_AT) ltac:(lia)) as RO.
  destruct (m (wa (Z.max A TAIL_TRAILER_AT))) as [b|] eqn:E.
  - rewrite (HMI _ _ E) in RO. discriminate.
  - rewrite (wview_not_ro rsegs m _ HW E) in RO. discriminate.
Qed.

Lemma evt_or_l : forall (P Q : machine_state -> Prop) ms, evt rsegs P ms -> evt rsegs (fun ms' => P ms' \/ Q ms') ms.
Proof. intros P Q ms H. unfold evt in *. destruct H as (ms' & H1 & H2). exists ms'. split; [exact H1 | left; exact H2]. Qed.

Lemma evt_or_r : forall (P Q : machine_state -> Prop) ms, evt rsegs Q ms -> evt rsegs (fun ms' => P ms' \/ Q ms') ms.
Proof. intros P Q ms H. unfold evt in *. destruct H as (ms' & H1 & H2). exists ms'. split; [exact H1 | right; exact H2]. Qed.

Section S.
Variables (gp tp : word) (F : bvmap 5 word) (fc : bv 32).

Definition QBa (m0 : word -> option byte) (lo Se : Z) (bd : word) (nb n P : Z) (inb sv mb : list byte) (sp : word)
    (ms' : machine_state) : Prop :=
  exists (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27
          x28 x29 x30 x31 : word) (m' : word -> option byte) (bb : list byte),
    ms' = MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26
                  x27 x28 x29 x30 x31) F (Z_to_bv 64 0x16698) fc None m' (seg_rom rsegs) /\
    x1 = Z_to_bv 64 0x15100 /\ x2 = sp /\ x3 = gp /\ x4 = tp /\ x9 = bd /\ x10 = Z_to_bv 64 8904 /\
    n = 8904 /\ nb = 8904 /\
    bytes_at rsegs m' (Se - 9064) (le8 (Z_to_bv 64 nb)) /\ bytes_at rsegs m' (Se - 9056) (le8 (Z_to_bv 64 n)) /\
    munch [(Se - 9296, Se); (bv_unsigned bd, bv_unsigned bd + nb)] m0 m' /\ wmono rsegs m0 m' /\ mem_inv rsegs m' /\
    stk rsegs m' lo Se /\ bytes_at rsegs m' (Se - 104) sv /\ bytes_at rsegs m' (Se - 110) mb /\
    bytes_at rsegs m' P inb /\
    Z.of_nat (length bb) = nb /\ bytes_at rsegs m' (bv_unsigned bd) bb /\ wr_at rsegs m' (bv_unsigned bd) nb.

Definition QBb (m0 : word -> option byte) (lo Se : Z) (bd : word) (nb n P : Z) (inb sv mb : list byte) (sp : word)
    (ms' : machine_state) : Prop :=
  exists (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27
          x28 x29 x30 x31 : word) (m' : word -> option byte) (bb : list byte),
    ms' = MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26
                  x27 x28 x29 x30 x31) F (Z_to_bv 64 0x151dc) fc None m' (seg_rom rsegs) /\
    x2 = sp /\ x3 = gp /\ x4 = tp /\ x9 = bd /\ x18 = Z_to_bv 64 nb /\ x24 = Z_to_bv 64 n /\
    munch [(Se - 9296, Se); (bv_unsigned bd, bv_unsigned bd + nb)] m0 m' /\ wmono rsegs m0 m' /\ mem_inv rsegs m' /\
    stk rsegs m' lo Se /\ bytes_at rsegs m' (Se - 104) sv /\ bytes_at rsegs m' (Se - 110) mb /\
    bytes_at rsegs m' P inb /\
    Z.of_nat (length bb) = nb /\ bytes_at rsegs m' (bv_unsigned bd) bb /\ wr_at rsegs m' (bv_unsigned bd) nb.

Lemma chk_loop : forall (k : nat) (ra sp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 a0 a1 a2 : word)
    (m : word -> option byte) (A i : Z),
  Z.of_nat k = 34 - i -> 0 <= i < 34 -> 0 <= A -> A + 34 < 2 ^ 64 ->
  bytes_at rsegs m A (repeat (Z_to_bv 8 165) 34) ->
  a0 = Z_to_bv 64 0 -> a1 = Z_to_bv 64 (A + i) -> a2 = Z_to_bv 64 (A + 34) ->
  evt rsegs (fun ms' => exists a1' a3' : word,
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) a1' a2 a3' a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                    t3 t4 t5 t6) F (Z_to_bv 64 0x150c0) fc None m (seg_rom rsegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x150a8) fc None m (seg_rom rsegs)).
Proof.
  induction k as [|k IH]; intros ra sp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 a0 a1 a2
    m A i HK Hi HA HA34 HB Ha0 Ha1 Ha2; [lia|].
  subst a0 a1 a2.
  pose proof (bytes_at_byte1 _ _ _ i HB ltac:(rewrite repeat_length; lia)) as HR.
  rewrite nth_rep in HR by lia.
  zstep. zstep. zstep. zstep. zstep. zstep.
  if_cases K; zify_cond K; rewrite ?Z.mod_small in K by lia.
  - eapply IH with (A := A) (i := i + 1); [lia | lia | lia | lia | exact HB | reflexivity | f_equal; lia | reflexivity].
  - finish.
Qed.

Lemma tail_B : forall (ra t0 t1 t2 s0 bd a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 sp : word)
    (m0 m : word -> option byte) (lo n fl P : Z) (bs inb sv mb : list byte),
  0 <= n < 65536 -> bv_unsigned s8 = n -> bv_unsigned s2 = nbE n -> 0 <= fl < 256 ->
  lo + 9296 <= bv_unsigned sp + 9072 -> bv_unsigned sp + 9072 < 2 ^ 64 ->
  Z.of_nat (length bs) = nbE n -> u8arr rsegs m (bv_unsigned bd) bs -> bv_unsigned bd + nbE n <= lo ->
  bytes_at rsegs m P inb -> (P + Z.of_nat (length inb) <= lo \/ bv_unsigned sp + 9072 <= P) ->
  bytes_at rsegs m (bv_unsigned sp + 9072 - 104) sv -> bytes_at rsegs m (bv_unsigned sp + 9072 - 110) mb ->
  stk rsegs m lo (bv_unsigned sp + 9072) -> mem_inv rsegs m ->
  munch [(bv_unsigned sp + 9072 - 9296, bv_unsigned sp + 9072); (bv_unsigned bd, bv_unsigned bd + nbE n)] m0 m ->
  wmono rsegs m0 m ->
  evt rsegs (fun ms' => QBa m0 lo (bv_unsigned sp + 9072) bd (nbE n) n P inb sv mb sp ms' \/
                        QBb m0 lo (bv_unsigned sp + 9072) bd (nbE n) n P inb sv mb sp ms')
    (MS (mkR ra sp gp tp t0 t1 t2 s0 bd a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 (Z_to_bv 64 fl) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x150e0) fc None m (seg_rom rsegs)).
Proof.
  intros ra t0 t1 t2 s0 bd a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 sp m0 m lo n fl P bs inb sv mb
    HN Hs8 Hs2 Hfl LO SPH HL HU HBD HIN DJ HSV HMB STK HMI MU WM.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. pose proof (bv_unsigned_in_range 64 bd) as Rbd.
  unfold bv_modulus in Rsp, Rbd.
  pose proof (nbE_range n HN) as NB.
  assert (Es2 : s2 = Z_to_bv 64 (nbE n)) by (apply bv_eq; rewrite unsigned_lit by lia; exact Hs2). subst s2.
  assert (Es8 : s8 = Z_to_bv 64 n) by (apply bv_eq; rewrite unsigned_lit by lia; exact Hs8). subst s8.
  pose proof (bytes_at_bound _ _ _ _ HIN) as [HP0 HPd].
  destruct HU as [HUb HUw]. rewrite HL in HUw.
  zstep. zstep.
  if_cases K; zify_cond K.
  - apply evt_or_r. finish; try reflexivity; try eassumption.
  - zstep. zstep. zstep.
    if_cases K2; zify_cond K2.
    + apply evt_or_r. finish; try reflexivity; try eassumption.
    + destruct (stk_split rsegs m lo (bv_unsigned sp + 24) (bv_unsigned sp + 9072) STK ltac:(lia)) as [STl STu].
      clear STK.
      carve_frame 16%nat STl.
      zstep. zstep. zstep.
      match goal with FR : rw_cells _ _ (bv_unsigned sp + 8) _ |- _ =>
        pose proof (proj2 (proj1 FR)) as FB; cbn [cells_bytes cbytes] in FB;
        release_frame FR STl (bv_unsigned sp + 24)
      end.
      rewrite app_nil_r in FB. apply bytes_at_app in FB as [FB1 FB2]. rewrite length_le8 in FB2.
      replace (bv_unsigned sp + 8) with (bv_unsigned sp + 9072 - 9064) in FB1 by lia.
      replace (bv_unsigned sp + 8 + Z.of_nat 8) with (bv_unsigned sp + 9072 - 9056) in FB2 by lia.
      pose proof (stk_merge _ _ _ _ _ STl STu ltac:(lia)) as STK. clear STl STu.
      apply evt_or_l. finish; try reflexivity; try eassumption; try (rewrite nbE_id by lia; lia); try lia.
Qed.

Lemma scene_B_x : memset_contract -> reac_ctrl_build_scene_step_contract -> check_step_contract ->
  forall (ra sp t0 t1 t2 s0 s1 bd a1 a2 a3 a4 a5 a6 a7 s2 s3 s6 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (m : word -> option byte) (Se lo n r P fl v : Z) (bs inb sv mb : list byte),
  bv_unsigned sp = Se - 9072 -> Se mod 16 = 0 -> Se < 2 ^ 64 -> stk rsegs m lo Se -> lo + 9296 <= Se ->
  bv_unsigned bd <> 0 -> Z.of_nat (length bs) = nbE n -> u8arr rsegs m (bv_unsigned bd) bs ->
  bv_unsigned bd + nbE n <= lo ->
  bv_unsigned s2 = nbE n -> bv_unsigned s3 = P -> bv_unsigned s6 = r -> bv_unsigned s8 = n ->
  0 <= n < 65536 -> 0 <= fl < 256 -> 0 <= v < 65536 ->
  bytes_at rsegs m P inb -> Z.of_nat (length inb) = r ->
  (P + r <= bv_unsigned bd \/ bv_unsigned bd + nbE n <= P) -> (P + r <= lo \/ Se <= P) ->
  bytes_at rsegs m (Se - 104) sv -> bytes_at rsegs m (Se - 110) mb ->
  bytes_at rsegs m 0x1ef60 (le8 (Z_to_bv 64 TADDR)) -> mem_inv rsegs m ->
  evt rsegs (fun ms' => QBa m lo Se bd (nbE n) n P inb sv mb sp ms' \/ QBb m lo Se bd (nbE n) n P inb sv mb sp ms')
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 bd a1 a2 a3 a4 a5 a6 a7 s2 s3 (Z_to_bv 64 (sx16 v)) (Z_to_bv 64 fl) s6
             (Z_to_bv 64 (sx16 (256 * (v / 256)))) s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x14fa4) fc None m (seg_rom rsegs)).
Proof.
  intros MSET BUILD CHECK ra sp t0 t1 t2 s0 s1 bd a1 a2 a3 a4 a5 a6 a7 s2 s3 s6 s8 s9 s10 s11 t3 t4 t5 t6 m Se lo n r P fl v
    bs inb sv mb HSP S16 SLT STK LO Hbd HL HU HBD Hs2 Hs3 Hs6 Hs8 HN Hfl Hv HIN Hr DJ1 DJ2 HSV HMB HGOT HMI.
  unfold memset_contract, MEMSET in MSET.
  unfold reac_ctrl_build_scene_step_contract, REAC_CTRL_BUILD_SCENE_STEP_FRAME, REAC_CTRL_BUILD_SCENE_STEP in BUILD.
  unfold check_step_contract, CHECK_STEP, CHECK_STEP_K in CHECK.
  assert (ES : Se = bv_unsigned sp + 9072) by lia. subst Se.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. pose proof (bv_unsigned_in_range 64 bd) as Rbd.
  unfold bv_modulus in Rsp, Rbd.
  pose proof (bytes_at_bound _ _ _ _ HIN) as [HP0 HPd].
  pose proof (nbE_range n HN) as NB.
  pose proof (sx16_range v Hv) as RV.
  pose proof STK as [Hlo0 _].
  eapply evt_cut; [eapply (pre_B gp tp F fc) with (n := n) (r := r) (PC := P) (bs := bs) (inb := inb);
    [exact HN | exact Hs8 | exact Hs6 | exact Hs3 | exact Hbd | exact HL | exact HU | lia | exact HIN | exact Hr
    | exact DJ1 | exact HGOT | exact HMI] | ].
  intros ms' (a0' & a1' & a2' & a3' & a4' & s3' & s6' & m1 & bs1 & E & MU1 & WM & MI1 & HU1 & HL1 & HIN1). subst ms'.
  pose proof (stk_transport_disjoint rsegs _ m m1 lo (bv_unsigned sp + 9072) STK MU1 WM
    ltac:(cbn [disjoint_from]; split; [lia | exact I])) as ST1.
  pose proof (bytes_at_transport rsegs _ m m1 _ sv HSV MU1 ltac:(cbn [disjoint_from]; split; [lia | exact I])) as HSV1.
  pose proof (bytes_at_transport rsegs _ m m1 _ mb HMB MU1 ltac:(cbn [disjoint_from]; split; [lia | exact I])) as HMB1.
  assert (MU : munch [(bv_unsigned sp + 9072 - 9296, bv_unsigned sp + 9072); (bv_unsigned bd, bv_unsigned bd + nbE n)] m m1)
    by (eapply munch_weaken; [| exact MU1]; unfold sub_fp; cbn [outside]; tauto).
  clear STK HSV HMB HU HIN HGOT HMI MU1 HL.
  destruct (stk_split rsegs m1 lo (bv_unsigned sp + 8962) (bv_unsigned sp + 9072) ST1 ltac:(lia)) as [STa STt].
  clear ST1.
  carve_frame 34%nat STa. rename FR into FRb.
  destruct (stk_split rsegs m1 lo (bv_unsigned sp) (bv_unsigned sp + 8928) STa ltac:(lia)) as [ST STm].
  clear STa.
  do 10 zstep.
  eapply evt_cut; [eapply MSET; [rewrite !unsigned_lit by lia; exact FRb | exact MI1] | ].
  intros ms' PO. unfold memset_post in PO.
  destruct PO as (y1 & y2 & y3 & y4 & y5 & y6 & y7 & y8 & y9 & y10 & y11 & y12 & y13 & y14 & m2 & E & MU2 & WM2 & MI2 & FB2).
  subst ms'.
  rewrite !unsigned_lit in MU2 by lia. rewrite !unsigned_lit in FB2 by lia.
  change (Z.to_nat 34) with 34%nat in FB2. change (165 mod 256) with 165 in FB2.
  transport_after_call rsegs m1 m2 MU2 WM2. clear MU2 WM2 MI1.
  replace (ret_pc (Z_to_bv 64 86080)) with (Z_to_bv 64 86080) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
  do 7 zstep.
  eapply evt_cut; [eapply BUILD with (lo := lo) (bj := repeat (Z_to_bv 8 165) 34) (b := bs1); [exact MI2 | exact ST | lia | ] | ].
  { intros OKT.
    rewrite (ok_val _ _ _ n v) in OKT by (try rewrite unsigned_lit by lia; lia).
    apply andb_true_iff in OKT as [OKT O3]. apply andb_true_iff in OKT as [O1 O2].
    apply Z.eqb_eq in O1. apply Z.leb_le in O2. apply Z.leb_le in O3.
    pose proof (nbE_id n ltac:(lia)) as NBn.
    pose proof (wr_trailer _ _ MI2 (proj2 FB2)) as TR.
    rewrite !unsigned_lit by lia.
    split; [exact FB2|]. split; [exact (proj1 HU1)|]. split; [apply len8904; lia|].
    repeat split; lia. }
  intros ms' PO.
  destruct PO as (w1 & w2 & w3 & w4 & w5 & w6 & w7 & w8 & w9 & w10 & w11 & w12 & w13 & w14 & w15 & m3 & E & MU3 & WM3 & MI3 & ST3 & PO).
  subst ms'.
  revert PO. rewrite (ok_val _ _ _ n v) by (try rewrite unsigned_lit by lia; lia). intros PO.
  rewrite !unsigned_lit in MU3 by lia.
  replace (ret_pc (Z_to_bv 64 86108)) with (Z_to_bv 64 86108) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
  revert PO. destruct ((n =? 8904) && (0 <=? sx16 v) && (sx16 v <=? 342)) eqn:OK; intros PO.
  - destruct PO as [EA FB3]. subst w4.
    pose proof OK as OK2. apply andb_true_iff in OK2 as [OK2 O3]. apply andb_true_iff in OK2 as [O1 O2].
    apply Z.eqb_eq in O1. apply Z.leb_le in O2. apply Z.leb_le in O3.
    pose proof (nbE_id n ltac:(lia)) as NBn.
    rewrite !unsigned_lit in FB3 by lia.
    transport_after_call rsegs m2 m3 MU3 WM3. clear MU3 WM3 MI2.
    do 10 zstep.
    rewrite (a1_val _ n v); [ | lia | apply snez_val; lia | first [reflexivity | Z.div_mod_to_equations; lia]
                            | first [reflexivity | Z.div_mod_to_equations; lia] ].
    rewrite OK. change (if true then 0 else -1) with 0.
    zr_until 0x153ec.
    eapply evt_cut; [eapply CHECK with (lo := lo) (b := bs1);
      [exact MI3 | exact ST3 | lia | Z.div_mod_to_equations; lia | rewrite unsigned_lit by lia; lia
      | rewrite !unsigned_lit by lia; exact (proj1 (u8arr_of_rw_cells rsegs _ _ _ _ FB3)) | exact (proj1 HU1)
      | apply len8904; lia
      | rewrite unsigned_lit by lia; lia | lia] | ].
    intros ms' PO.
    destruct PO as (z1 & z2 & z3 & z4 & z5 & z6 & z7 & z8 & z9 & z10 & z11 & z12 & z13 & z14 & z15 & m4 & E & MU4 & WM4 & MI4 & ST4).
    subst ms'.
    transport_after_call rsegs m3 m4 MU4 WM4. clear MU4 WM4 MI3.
    replace (ret_pc (Z_to_bv 64 86240)) with (Z_to_bv 64 86240) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
    pose proof (stk_merge _ _ _ _ _ ST4 STm ltac:(lia)) as STb. clear ST4 STm.
    release_frame FB3 STb (bv_unsigned sp + 8962).
    pose proof (stk_merge _ _ _ _ _ STb STt ltac:(lia)) as STK. clear STb STt.
    eapply tail_B with (bs := bs1);
      [exact HN | exact Hs8 | exact Hs2 | exact Hfl | lia | lia | exact HL1 | exact HU1 | exact HBD | exact HIN1 | lia
      | exact HSV1 | exact HMB1 | exact STK | eassumption | exact MU | exact WM].
  - destruct PO as [EA MU3n]. subst w4.
    clear MU3.
    transport_after_call rsegs m2 m3 MU3n WM3. clear MU3n WM3 MI2.
    do 10 zstep.
    rewrite (a1_val _ n v); [ | lia | apply snez_val; lia | first [reflexivity | Z.div_mod_to_equations; lia]
                            | first [reflexivity | Z.div_mod_to_equations; lia] ].
    rewrite OK. change (if false then 0 else -1) with (-1).
    zr_until 0x150a8.
    eapply evt_cut; [eapply (chk_loop 34) with (A := bv_unsigned sp + 8928) (i := 0);
      [lia | lia | lia | lia | exact (proj1 (u8arr_of_rw_cells rsegs _ _ _ _ FB2)) | reflexivity | f_equal; lia
      | f_equal; lia] | ].
    intros ms' (a1x & a3x & E). subst ms'.
    zstep. sres_if.
    pose proof (stk_merge _ _ _ _ _ ST3 STm ltac:(lia)) as STb. clear ST3 STm.
    release_frame FB2 STb (bv_unsigned sp + 8962).
    pose proof (stk_merge _ _ _ _ _ STb STt ltac:(lia)) as STK. clear STb STt.
    eapply tail_B with (bs := bs1);
      [exact HN | exact Hs8 | exact Hs2 | exact Hfl | lia | lia | exact HL1 | exact HU1 | exact HBD | exact HIN1 | lia
      | exact HSV1 | exact HMB1 | exact STK | eassumption | exact MU | exact WM].
Qed.

End S.
