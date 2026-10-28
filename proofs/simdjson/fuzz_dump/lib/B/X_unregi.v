(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.Lib Require Import Tac ImageA SysStep.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.Lib Require Import StoreFast.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.P Require Import Str_tac Startup_glue.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.B Require Import Layout R_small F_memset X_atexit X_xdefs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.

Ltac fold_closed_regs :=
  repeat match goal with
  | |- context [Z_to_bv 64 ?z] => lazymatch z with Z0 => fail | Zpos _ => fail | Zneg _ => fail | _ => idtac end;
       let v := eval vm_compute in z in is_Zlit v; change (Z_to_bv 64 z) with (Z_to_bv 64 v)
  end.
Lemma land_7 : forall x, 0 <= x -> Z.land x 7 = x mod 8.
Proof. intros x Hx. change 7 with (Z.ones 3). rewrite Z.land_ones by lia. reflexivity. Qed.

Lemma C8_first_byte : forall (m : mem) A v pre post, ro_cells bsegs m A (pre ++ C8 v :: post) ->
  ov_read_bytes bsegs m (wa (A + Z.of_nat (cells_size pre))) 1 = Some [Z_to_bv 8 (bv_unsigned v)].
Proof.
  intros m A v pre post [Hwf Hb]. apply cells_wf_app in Hwf. destruct Hwf as [Hw1 _].
  rewrite <- (cells_bytes_length pre Hw1). rewrite (bytes_at_ov_read bsegs m A _ _ 1 Hb).
  - rewrite cells_bytes_app, skipn_app_exact. reflexivity.
  - rewrite cells_bytes_app, length_app. cbn [cells_bytes cbytes]. rewrite length_app, length_le8. lia.
Qed.

Lemma byte_land7 : forall z, z mod 8 = 0 -> Z.land (bv_unsigned (Z_to_bv 8 z)) 7 = 0.
Proof.
  intros z Hz. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 8) with 256.
  rewrite land_7 by (apply Z.mod_pos_bound; lia). Z.div_mod_to_equations. lia.
Qed.

Lemma stk_window : forall (m : mem) lo hi a n, stk bsegs m lo hi -> lo <= a -> a + n <= hi -> 0 <= n ->
  stk bsegs m lo a /\ (exists junk, rw_cells bsegs m a [CB (Z.to_nat n) junk]) /\ stk bsegs m (a + n) hi.
Proof.
  intros m lo hi a n ST H1 H2 H3.
  destruct (stk_split bsegs m lo a hi ST ltac:(lia)) as [S1 S23].
  destruct (stk_split bsegs m a (a + n) hi S23 ltac:(lia)) as [S2 S3].
  split; [exact S1|]. split; [| exact S3].
  destruct (stk_carve bsegs m a (a + n) (Z.to_nat n) S2 ltac:(lia)) as [_ (junk & FR)].
  exists junk. replace (a + n - Z.of_nat (Z.to_nat n)) with a in FR by lia. exact FR.
Qed.

Lemma stk_unwindow : forall (m : mem) lo hi a n cs, stk bsegs m lo a -> rw_cells bsegs m a cs -> Z.of_nat (cells_size cs) = n ->
  stk bsegs m (a + n) hi -> lo <= a -> a + n <= hi -> stk bsegs m lo hi.
Proof.
  intros m lo hi a n cs S1 C En S3 H1 H2. pose proof (stk_of_rw_cells bsegs m a cs C) as S2. rewrite En in S2.
  apply (stk_merge bsegs m lo a hi S1); [| lia]. apply (stk_merge bsegs m a (a + n) hi S2 S3). lia.
Qed.

Definition can_poison_entry := 0x81708%Z.

Lemma can_poison_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem),
  ro_cells bsegs m 0x17699c [C1 (Z_to_bv 8 1)] ->
  mem_inv bsegs m ->
  evt bsegs (leaf_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc 1 m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x81708) fc None m (seg_rom bsegs)).
Proof.
  intros until m. intros CI MI.
  pose proof (munch_refl [] m) as MU. pose proof (wmono_refl bsegs m) as WM.
  do 5 zstep.
  finish.
Qed.

Lemma unreg_iter_head : forall (A K beg srz : Z) (w1 w3 w4 w5 w6 w7 : word)
    (ra gp tp t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (sp : word) F fc (m : mem),
  ro_cells bsegs m A [C8 (Z_to_bv 64 beg); C8 w1; C8 (Z_to_bv 64 srz); C8 w3; C8 w4; C8 w5; C8 w6; C8 w7] ->
  rw_cells bsegs m 0x177e18 [C1 (Z_to_bv 8 1)] ->
  ro_cells bsegs m 0x17699c [C1 (Z_to_bv 8 1)] ->
  ro_cells bsegs m 0x174950 [C4 (Z_to_bv 64 1)] ->
  ro_cells bsegs m 0x177138 [C8 (Z_to_bv 64 0x7fff8000)] ->
  ro_cells bsegs m 0x208ce0 [C8 (Z_to_bv 64 0xffffffffffffffff)] ->
  ro_cells bsegs m 0x1701e0 [C8 (Z_to_bv 64 0x160c88)] ->
  stk bsegs m XS1_LO XS1_HI -> stk bsegs m XS2_LO XS2_HI -> stk bsegs m XS3_LO XS3_HI ->
  ((XS1_LO <= SHB + beg / 8 /\ SHB + beg / 8 + srz / 8 <= XS1_HI)
   \/ (XS2_LO <= SHB + beg / 8 /\ SHB + beg / 8 + srz / 8 <= XS2_HI)
   \/ (XS3_LO <= SHB + beg / 8 /\ SHB + beg / 8 + srz / 8 <= XS3_HI)) ->
  0 <= beg -> beg mod 8 = 0 -> 8 <= srz -> srz mod 8 = 0 -> beg + srz <= 0x6cd000 -> srz / 8 < 0x10000 ->
  0x173090 <= A -> A + 64 <= 0x173a50 -> 1 <= K <= 39 ->
  mem_inv bsegs m ->
  evt bsegs (fun ms' => exists (s0' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : mem),
        ms' = MS (mkR (Z_to_bv 64 0x67a64) sp gp tp t0' t1' t2' s0' (Z_to_bv 64 0x208c68) a0' a1' a2' a3' a4' a5' a6' a7'
                      (Z_to_bv 64 2) (Z_to_bv 64 0x1cae9) (Z_to_bv 64 A) (Z_to_bv 64 (2^61)) (Z_to_bv 64 0x1749b0)
                      (Z_to_bv 64 0x1701e0) (Z_to_bv 64 0x1749f0) (Z_to_bv 64 0x174938) (Z_to_bv 64 0x177138) (Z_to_bv 64 K)
                      t3' t4' t5' t6')
                 F (Z_to_bv 64 0x67a64) fc None m' (seg_rom bsegs)
        /\ munch [(XS1_LO, XS1_HI); (XS2_LO, XS2_HI); (XS3_LO, XS3_HI)] m m' /\ wmono bsegs m m' /\ mem_inv bsegs m'
        /\ stk bsegs m' XS1_LO XS1_HI /\ stk bsegs m' XS2_LO XS2_HI /\ stk bsegs m' XS3_LO XS3_HI)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 0x208c68) a0 a1 a2 a3 a4 a5 a6 a7
             (Z_to_bv 64 2) (Z_to_bv 64 0x1cae9) (Z_to_bv 64 A) (Z_to_bv 64 (2^61)) (Z_to_bv 64 0x1749b0)
             (Z_to_bv 64 0x1701e0) (Z_to_bv 64 0x1749f0) (Z_to_bv 64 0x174938) (Z_to_bv 64 0x177138) (Z_to_bv 64 K)
             t3 t4 t5 t6)
        F (Z_to_bv 64 0x67a7c) fc None m (seg_rom bsegs)).
Proof.
  intros until m. intros REC AI CP RG SHC THR RMS SC1 SC2 SC3 INS B0 B8 S8 S8m BT ST8 A0 A1 HK MI.
  unfold SHB in *.
  pose proof (munch_refl [(0x7fff8000 + beg / 8, 0x7fff8000 + beg / 8 + srz / 8)] m) as MU.
  pose proof (wmono_refl bsegs m) as WM.
  assert (EUb : bv_unsigned (Z_to_bv 64 beg) = beg) by (apply unsigned_lit; lia).
  assert (EUs : bv_unsigned (Z_to_bv 64 srz) = srz) by (apply unsigned_lit; lia).
  assert (EUA : bv_unsigned (Z_to_bv 64 A) = A) by (apply unsigned_lit; lia).
  astep.
  call asan_inited_spec; [exact AI| exact MI|].
  xsteps_to 0x67aa0%Z.
  do 6 xstep. fold_closed_regs.
  xstep.
  lstep. rewrite (land_7 beg B0), B8. xstep.
  lazymatch goal with REC : ro_cells bsegs ?mm A (?c0 :: ?c1 :: C8 ?v :: ?post) |- _ =>
    pose proof (C8_first_byte mm A v [c0; c1] post REC) as HR end.
  cbn [cells_size csize Nat.add] in HR. change (Z.of_nat 16) with 16 in HR.
  lstep. lstep. rewrite (byte_land7 srz S8m). xstep. xstep. clear HR.
  call can_poison_spec; [exact CP| assumption|].
  xstep.
  do 12 lstep.
  assert (E1 : beg ≫ 3 = beg / 8) by (rewrite Z.shiftr_div_pow2 by lia; reflexivity).
  assert (E2 : (beg + srz + -8) ≫ 3 = beg / 8 + srz / 8 - 1).
  { rewrite Z.shiftr_div_pow2 by lia. change (2^3) with 8. Z.div_mod_to_equations. lia. }
  rewrite E1, E2.
  replace (2147450880 + (beg / 8 + srz / 8 - 1) + 1) with (2147450880 + beg / 8 + srz / 8) by lia.
  assert (EUN : bv_unsigned (Z_to_bv 64 (srz / 8)) = srz / 8) by (apply unsigned_lit; Z.div_mod_to_equations; lia).
  lstep.
  rewrite (Z.mod_small (2147450880 + beg / 8 + srz / 8)) by (Z.div_mod_to_equations; lia).
  rewrite (Z.mod_small (2147450880 + beg / 8)) by (Z.div_mod_to_equations; lia).
  replace (2147450880 + beg / 8 + srz / 8 - (2147450880 + beg / 8)) with (srz / 8) by lia.
  if_true.
  lstep. lstep. lstep.
  assert (N0 : 0 <= srz / 8) by (Z.div_mod_to_equations; lia).
  assert (DB : 0 <= 2147450880 + beg / 8 /\ 2147450880 + beg / 8 + srz / 8 <= 2^64) by (Z.div_mod_to_equations; lia).
  destruct INS as [(SL0 & SH0)|[(SL0 & SH0)|(SL0 & SH0)]].
  - destruct (stk_window _ _ _ (2147450880 + beg / 8) (srz / 8) SC1 SL0 SH0 N0) as (SA & (junk & DST) & SB). clear SC1.
    call memset_callZ; [exact DST| assumption| lia| lia| lia| lia|].
    pose proof (stk_unwindow _ _ _ _ (srz / 8) _ SA POST ltac:(cbn [cells_size csize]; rewrite Nat.add_0_r, Z2Nat.id by lia; reflexivity)
                  SB SL0 SH0) as SC1.
    apply evt_done. do 17 eexists. split; [reflexivity|].
    split; [eapply munch_weaken; [| exact MU]; unfold sub_fp; cbn [outside]; intros; lia|]. split; [exact WM|]. split; [assumption|]. split; [exact SC1| split; assumption].
  - destruct (stk_window _ _ _ (2147450880 + beg / 8) (srz / 8) SC2 SL0 SH0 N0) as (SA & (junk & DST) & SB). clear SC2.
    call memset_callZ; [exact DST| assumption| lia| lia| lia| lia|].
    pose proof (stk_unwindow _ _ _ _ (srz / 8) _ SA POST ltac:(cbn [cells_size csize]; rewrite Nat.add_0_r, Z2Nat.id by lia; reflexivity)
                  SB SL0 SH0) as SC2.
    apply evt_done. do 17 eexists. split; [reflexivity|].
    split; [eapply munch_weaken; [| exact MU]; unfold sub_fp; cbn [outside]; intros; lia|]. split; [exact WM|]. split; [assumption|]. split; [assumption| split; assumption].
  - destruct (stk_window _ _ _ (2147450880 + beg / 8) (srz / 8) SC3 SL0 SH0 N0) as (SA & (junk & DST) & SB). clear SC3.
    call memset_callZ; [exact DST| assumption| lia| lia| lia| lia|].
    pose proof (stk_unwindow _ _ _ _ (srz / 8) _ SA POST ltac:(cbn [cells_size csize]; rewrite Nat.add_0_r, Z2Nat.id by lia; reflexivity)
                  SB SL0 SH0) as SC3.
    apply evt_done. do 17 eexists. split; [reflexivity|].
    split; [eapply munch_weaken; [| exact MU]; unfold sub_fp; cbn [outside]; intros; lia|]. split; [exact WM|]. split; [assumption|]. split; [assumption| split; assumption].
Qed.

Lemma unreg_iter_tail : forall (A K odr : Z) (w0 w1 w2 w3 w4 w5 w6 : word)
    (ra gp tp t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (sp : word) F fc (m : mem) (o1 o2 o3 o4 o5 o6 o7 o8 o9 o10 o11 : byte),
  ro_cells bsegs m A [C8 w0; C8 w1; C8 w2; C8 w3; C8 w4; C8 w5; C8 w6; C8 (Z_to_bv 64 odr)] ->
  rw_cells bsegs m 0x6a9960 [C1 o1] -> rw_cells bsegs m 0x6a9961 [C1 o2] -> rw_cells bsegs m 0x6a9962 [C1 o3] -> rw_cells bsegs m 0x6a9963 [C1 o4] -> rw_cells bsegs m 0x6a9964 [C1 o5] -> rw_cells bsegs m 0x6a9965 [C1 o6] -> rw_cells bsegs m 0x6a9966 [C1 o7] -> rw_cells bsegs m 0x6a9967 [C1 o8] -> rw_cells bsegs m 0x6a9968 [C1 o9] -> rw_cells bsegs m 0x6a9969 [C1 o10] -> rw_cells bsegs m 0x6a996a [C1 o11] ->
  (odr = ODR_NONE \/ odr = 0x6a9960 \/ odr = 0x6a9961 \/ odr = 0x6a9962 \/ odr = 0x6a9963 \/ odr = 0x6a9964 \/ odr = 0x6a9965 \/ odr = 0x6a9966 \/ odr = 0x6a9967 \/ odr = 0x6a9968 \/ odr = 0x6a9969 \/ odr = 0x6a996a) ->
  0x173090 <= A -> A + 64 <= 0x173a50 -> 1 <= K <= 39 ->
  mem_inv bsegs m ->
  evt bsegs (fun ms' => exists (ra' s0' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : mem) (o1' o2' o3' o4' o5' o6' o7' o8' o9' o10' o11' : byte),
        ms' = MS (mkR ra' sp gp tp t0' t1' t2' s0' (Z_to_bv 64 0x208c68) a0' a1' a2' a3' a4' a5' a6' a7'
                      (Z_to_bv 64 2) (Z_to_bv 64 0x1cae9) (Z_to_bv 64 (A + 64)) (Z_to_bv 64 (2^61)) (Z_to_bv 64 0x1749b0)
                      (Z_to_bv 64 0x1701e0) (Z_to_bv 64 0x1749f0) (Z_to_bv 64 0x174938) (Z_to_bv 64 0x177138) (Z_to_bv 64 (K - 1))
                      t3' t4' t5' t6')
                 F (Z_to_bv 64 (if K =? 1 then 0x67c80 else 0x67a7c)) fc None m' (seg_rom bsegs)
        /\ munch [(0x6a9960, 0x6a9961); (0x6a9961, 0x6a996b)] m m' /\ wmono bsegs m m' /\ mem_inv bsegs m'
        /\ rw_cells bsegs m' 0x6a9960 [C1 o1'] /\ rw_cells bsegs m' 0x6a9961 [C1 o2'] /\ rw_cells bsegs m' 0x6a9962 [C1 o3'] /\ rw_cells bsegs m' 0x6a9963 [C1 o4'] /\ rw_cells bsegs m' 0x6a9964 [C1 o5'] /\ rw_cells bsegs m' 0x6a9965 [C1 o6'] /\ rw_cells bsegs m' 0x6a9966 [C1 o7'] /\ rw_cells bsegs m' 0x6a9967 [C1 o8'] /\ rw_cells bsegs m' 0x6a9968 [C1 o9'] /\ rw_cells bsegs m' 0x6a9969 [C1 o10'] /\ rw_cells bsegs m' 0x6a996a [C1 o11'])
    (MS (mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 0x208c68) a0 a1 a2 a3 a4 a5 a6 a7
             (Z_to_bv 64 2) (Z_to_bv 64 0x1cae9) (Z_to_bv 64 A) (Z_to_bv 64 (2^61)) (Z_to_bv 64 0x1749b0)
             (Z_to_bv 64 0x1701e0) (Z_to_bv 64 0x1749f0) (Z_to_bv 64 0x174938) (Z_to_bv 64 0x177138) (Z_to_bv 64 K)
             t3 t4 t5 t6)
        F (Z_to_bv 64 0x67a64) fc None m (seg_rom bsegs)).
Proof.
  intros until o11. intros REC O1 O2 O3 O4 O5 O6 O7 O8 O9 O10 O11 ODR A0 A1 HK MI.
  pose proof (munch_refl [(0x6a9960, 0x6a9961); (0x6a9961, 0x6a996b)] m) as MU.
  pose proof (wmono_refl bsegs m) as WM.
  assert (EUA : bv_unsigned (Z_to_bv 64 A) = A) by (apply unsigned_lit; lia).
  assert (EUK : bv_unsigned (Z_to_bv 64 K) = K) by (apply unsigned_lit; lia).
  assert (EUK1 : K <> 1 -> bv_unsigned (Z_to_bv 64 (K + -1)) = K + -1) by (intros; apply unsigned_lit; lia).
  unfold ODR_NONE in ODR.
  destruct ODR as [ -> | ODR ]; [| repeat (destruct ODR as [ -> | ODR ]); [.. | subst odr] ].
  -
    lstep. lstep. xstep. lstep. lstep.
    destruct (Z.eqb_spec K 1) as [EK|NK].
    + subst K. xstep.
      apply evt_done. do 18 eexists. exists o1, o2, o3, o4, o5, o6, o7, o8, o9, o10, o11. split; [reflexivity|].
      split; [exact MU|]. split; [exact WM|]. split; [assumption|]. repeat (split; [assumption|]). assumption.
    + specialize (EUK1 NK). lstep. if_false.
      replace (if K =? 1 then 425088 else 424572) with 424572 by (destruct (Z.eqb_spec K 1); [contradiction| reflexivity]).
      apply evt_done. do 18 eexists. exists o1, o2, o3, o4, o5, o6, o7, o8, o9, o10, o11. split; [reflexivity|].
      split; [exact MU|]. split; [exact WM|]. split; [assumption|]. repeat (split; [assumption|]). assumption.
  -
    lstep. lstep. xstep. lstep. lstep. lstep.
    destruct (Z.eqb_spec K 1) as [EK|NK].
    + subst K. xstep. xstep.
      apply evt_done. do 18 eexists. exists (Z_to_bv 8 0), o2, o3, o4, o5, o6, o7, o8, o9, o10, o11. split; [reflexivity|].
      split; [exact MU|]. split; [exact WM|]. split; [assumption|]. repeat (split; [assumption|]). assumption.
    + specialize (EUK1 NK). lstep. if_true.
      replace (if K =? 1 then 425088 else 424572) with 424572 by (destruct (Z.eqb_spec K 1); [contradiction| reflexivity]).
      apply evt_done. do 18 eexists. exists (Z_to_bv 8 0), o2, o3, o4, o5, o6, o7, o8, o9, o10, o11. split; [reflexivity|].
      split; [exact MU|]. split; [exact WM|]. split; [assumption|]. repeat (split; [assumption|]). assumption.
  -
    lstep. lstep. xstep. lstep. lstep. lstep.
    destruct (Z.eqb_spec K 1) as [EK|NK].
    + subst K. xstep. xstep.
      apply evt_done. do 18 eexists. exists o1, (Z_to_bv 8 0), o3, o4, o5, o6, o7, o8, o9, o10, o11. split; [reflexivity|].
      split; [exact MU|]. split; [exact WM|]. split; [assumption|]. repeat (split; [assumption|]). assumption.
    + specialize (EUK1 NK). lstep. if_true.
      replace (if K =? 1 then 425088 else 424572) with 424572 by (destruct (Z.eqb_spec K 1); [contradiction| reflexivity]).
      apply evt_done. do 18 eexists. exists o1, (Z_to_bv 8 0), o3, o4, o5, o6, o7, o8, o9, o10, o11. split; [reflexivity|].
      split; [exact MU|]. split; [exact WM|]. split; [assumption|]. repeat (split; [assumption|]). assumption.
  -
    lstep. lstep. xstep. lstep. lstep. lstep.
    destruct (Z.eqb_spec K 1) as [EK|NK].
    + subst K. xstep. xstep.
      apply evt_done. do 18 eexists. exists o1, o2, (Z_to_bv 8 0), o4, o5, o6, o7, o8, o9, o10, o11. split; [reflexivity|].
      split; [exact MU|]. split; [exact WM|]. split; [assumption|]. repeat (split; [assumption|]). assumption.
    + specialize (EUK1 NK). lstep. if_true.
      replace (if K =? 1 then 425088 else 424572) with 424572 by (destruct (Z.eqb_spec K 1); [contradiction| reflexivity]).
      apply evt_done. do 18 eexists. exists o1, o2, (Z_to_bv 8 0), o4, o5, o6, o7, o8, o9, o10, o11. split; [reflexivity|].
      split; [exact MU|]. split; [exact WM|]. split; [assumption|]. repeat (split; [assumption|]). assumption.
  -
    lstep. lstep. xstep. lstep. lstep. lstep.
    destruct (Z.eqb_spec K 1) as [EK|NK].
    + subst K. xstep. xstep.
      apply evt_done. do 18 eexists. exists o1, o2, o3, (Z_to_bv 8 0), o5, o6, o7, o8, o9, o10, o11. split; [reflexivity|].
      split; [exact MU|]. split; [exact WM|]. split; [assumption|]. repeat (split; [assumption|]). assumption.
    + specialize (EUK1 NK). lstep. if_true.
      replace (if K =? 1 then 425088 else 424572) with 424572 by (destruct (Z.eqb_spec K 1); [contradiction| reflexivity]).
      apply evt_done. do 18 eexists. exists o1, o2, o3, (Z_to_bv 8 0), o5, o6, o7, o8, o9, o10, o11. split; [reflexivity|].
      split; [exact MU|]. split; [exact WM|]. split; [assumption|]. repeat (split; [assumption|]). assumption.
  -
    lstep. lstep. xstep. lstep. lstep. lstep.
    destruct (Z.eqb_spec K 1) as [EK|NK].
    + subst K. xstep. xstep.
      apply evt_done. do 18 eexists. exists o1, o2, o3, o4, (Z_to_bv 8 0), o6, o7, o8, o9, o10, o11. split; [reflexivity|].
      split; [exact MU|]. split; [exact WM|]. split; [assumption|]. repeat (split; [assumption|]). assumption.
    + specialize (EUK1 NK). lstep. if_true.
      replace (if K =? 1 then 425088 else 424572) with 424572 by (destruct (Z.eqb_spec K 1); [contradiction| reflexivity]).
      apply evt_done. do 18 eexists. exists o1, o2, o3, o4, (Z_to_bv 8 0), o6, o7, o8, o9, o10, o11. split; [reflexivity|].
      split; [exact MU|]. split; [exact WM|]. split; [assumption|]. repeat (split; [assumption|]). assumption.
  -
    lstep. lstep. xstep. lstep. lstep. lstep.
    destruct (Z.eqb_spec K 1) as [EK|NK].
    + subst K. xstep. xstep.
      apply evt_done. do 18 eexists. exists o1, o2, o3, o4, o5, (Z_to_bv 8 0), o7, o8, o9, o10, o11. split; [reflexivity|].
      split; [exact MU|]. split; [exact WM|]. split; [assumption|]. repeat (split; [assumption|]). assumption.
    + specialize (EUK1 NK). lstep. if_true.
      replace (if K =? 1 then 425088 else 424572) with 424572 by (destruct (Z.eqb_spec K 1); [contradiction| reflexivity]).
      apply evt_done. do 18 eexists. exists o1, o2, o3, o4, o5, (Z_to_bv 8 0), o7, o8, o9, o10, o11. split; [reflexivity|].
      split; [exact MU|]. split; [exact WM|]. split; [assumption|]. repeat (split; [assumption|]). assumption.
  -
    lstep. lstep. xstep. lstep. lstep. lstep.
    destruct (Z.eqb_spec K 1) as [EK|NK].
    + subst K. xstep. xstep.
      apply evt_done. do 18 eexists. exists o1, o2, o3, o4, o5, o6, (Z_to_bv 8 0), o8, o9, o10, o11. split; [reflexivity|].
      split; [exact MU|]. split; [exact WM|]. split; [assumption|]. repeat (split; [assumption|]). assumption.
    + specialize (EUK1 NK). lstep. if_true.
      replace (if K =? 1 then 425088 else 424572) with 424572 by (destruct (Z.eqb_spec K 1); [contradiction| reflexivity]).
      apply evt_done. do 18 eexists. exists o1, o2, o3, o4, o5, o6, (Z_to_bv 8 0), o8, o9, o10, o11. split; [reflexivity|].
      split; [exact MU|]. split; [exact WM|]. split; [assumption|]. repeat (split; [assumption|]). assumption.
  -
    lstep. lstep. xstep. lstep. lstep. lstep.
    destruct (Z.eqb_spec K 1) as [EK|NK].
    + subst K. xstep. xstep.
      apply evt_done. do 18 eexists. exists o1, o2, o3, o4, o5, o6, o7, (Z_to_bv 8 0), o9, o10, o11. split; [reflexivity|].
      split; [exact MU|]. split; [exact WM|]. split; [assumption|]. repeat (split; [assumption|]). assumption.
    + specialize (EUK1 NK). lstep. if_true.
      replace (if K =? 1 then 425088 else 424572) with 424572 by (destruct (Z.eqb_spec K 1); [contradiction| reflexivity]).
      apply evt_done. do 18 eexists. exists o1, o2, o3, o4, o5, o6, o7, (Z_to_bv 8 0), o9, o10, o11. split; [reflexivity|].
      split; [exact MU|]. split; [exact WM|]. split; [assumption|]. repeat (split; [assumption|]). assumption.
  -
    lstep. lstep. xstep. lstep. lstep. lstep.
    destruct (Z.eqb_spec K 1) as [EK|NK].
    + subst K. xstep. xstep.
      apply evt_done. do 18 eexists. exists o1, o2, o3, o4, o5, o6, o7, o8, (Z_to_bv 8 0), o10, o11. split; [reflexivity|].
      split; [exact MU|]. split; [exact WM|]. split; [assumption|]. repeat (split; [assumption|]). assumption.
    + specialize (EUK1 NK). lstep. if_true.
      replace (if K =? 1 then 425088 else 424572) with 424572 by (destruct (Z.eqb_spec K 1); [contradiction| reflexivity]).
      apply evt_done. do 18 eexists. exists o1, o2, o3, o4, o5, o6, o7, o8, (Z_to_bv 8 0), o10, o11. split; [reflexivity|].
      split; [exact MU|]. split; [exact WM|]. split; [assumption|]. repeat (split; [assumption|]). assumption.
  -
    lstep. lstep. xstep. lstep. lstep. lstep.
    destruct (Z.eqb_spec K 1) as [EK|NK].
    + subst K. xstep. xstep.
      apply evt_done. do 18 eexists. exists o1, o2, o3, o4, o5, o6, o7, o8, o9, (Z_to_bv 8 0), o11. split; [reflexivity|].
      split; [exact MU|]. split; [exact WM|]. split; [assumption|]. repeat (split; [assumption|]). assumption.
    + specialize (EUK1 NK). lstep. if_true.
      replace (if K =? 1 then 425088 else 424572) with 424572 by (destruct (Z.eqb_spec K 1); [contradiction| reflexivity]).
      apply evt_done. do 18 eexists. exists o1, o2, o3, o4, o5, o6, o7, o8, o9, (Z_to_bv 8 0), o11. split; [reflexivity|].
      split; [exact MU|]. split; [exact WM|]. split; [assumption|]. repeat (split; [assumption|]). assumption.
  -
    lstep. lstep. xstep. lstep. lstep. lstep.
    destruct (Z.eqb_spec K 1) as [EK|NK].
    + subst K. xstep. xstep.
      apply evt_done. do 18 eexists. exists o1, o2, o3, o4, o5, o6, o7, o8, o9, o10, (Z_to_bv 8 0). split; [reflexivity|].
      split; [exact MU|]. split; [exact WM|]. split; [assumption|]. repeat (split; [assumption|]). assumption.
    + specialize (EUK1 NK). lstep. if_true.
      replace (if K =? 1 then 425088 else 424572) with 424572 by (destruct (Z.eqb_spec K 1); [contradiction| reflexivity]).
      apply evt_done. do 18 eexists. exists o1, o2, o3, o4, o5, o6, o7, o8, o9, o10, (Z_to_bv 8 0). split; [reflexivity|].
      split; [exact MU|]. split; [exact WM|]. split; [assumption|]. repeat (split; [assumption|]). assumption.
Qed.
