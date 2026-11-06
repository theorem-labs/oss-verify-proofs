(** rate_csv_holds: the csv segment of fuzz_rate's LLVMFuzzerTestOneInput (UBSan image), [0x14628, 0x14660), against
    rate_csv_contract (U/Prog/LLVMFuzzerTestOneInput_c.v), from the contracts of memset (0x1d618, U/Prog/memset_c.v),
    reac_rate_drivable_csv (0x14dcc, U/Prog/reac_rate_drivable_csv_c.v) and check_csv (0x14864, U/Prog/check_csv_c.v).
    The plain walk (lib/Prog/rate_csv.v) at the UBSan addresses, with mask in s10 and buflen in s0; no trap in the range:
      0x14628 `beqz a0` (not taken: buf <> 0); `mv s4,a0`; `addi a1,zero,0x5a`; `mv a2,s5`;
      0x14638 `jal memset`: memset(buf, 0x5a, bl), bl = buflen + (buflen = 0);
      `mv a0,s10`; `mv a1,s4`; `mv a2,s0`; 0x14648 `jal reac_rate_drivable_csv`: drivable_csv(mask, buf, buflen), run
              with its own stack bottom sp - CSV_STACK, so its post's munch fits the contract's;
      `mv a2,a0`; `mv a0,s4`; `mv a1,s0`; `mv a3,s10`; 0x1465c `jal check_csv`: check_csv(buf, buflen, len, mask),
              whose premises come from drivable_csv's post (buflen > 0) or memset's 0x5a at buf[0] (buflen = 0).
    The guard cells (U snprintf_c GOT_GUARD = RATE_GOT_GUARD = 0x1ee78, GUARD = RATE_GUARD = 0x50460) cross memset by
    its munch: both lie in the image's segments, the buf block outside them.
    rule 24: proves no function (kind: segment lemma of LLVMFuzzerTestOneInput's walk: rate_csv_contract is the evt of
    its range [0x14628, 0x14660)). *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame Tac FP.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.U Require Import Img0.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.U Require MemNorm.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Pod Require Import RateCfg RateCsv.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.U.Prog Require Import memset_c reac_rate_drivable_csv_c check_csv_c
  snprintf_c LLVMFuzzerTestOneInput_c.
Import ListNotations.
Open Scope Z_scope.

(** task_mem across a callee whose footprint was writable before it ran (copied from the released
    libreac/fuzz_disco Prog/tj_lemmas.v:221, origin/ossv/recipes 25e3d17bdb50). *)
Lemma task_mem_munch : forall W m m', MemNorm.task_mem rsegs m -> munch W m m' ->
  (forall a : word, ~ outside W (bv_unsigned a) -> wview rsegs m a <> None) -> MemNorm.task_mem rsegs m'.
Proof.
  intros W m m' TK MU HW a b E. destruct (m a) as [b0|] eqn:E0; [exact (TK a b0 E0)|].
  assert (HI : ~ outside W (bv_unsigned a)) by (intros Ho; rewrite (MU a Ho), E0 in E; discriminate).
  pose proof (HW a HI) as W0. unfold wview in W0. rewrite E0 in W0.
  destruct (find_segment rsegs (bv_unsigned a) 1) eqn:EF; [left; discriminate|].
  exfalso. apply W0. reflexivity.
Qed.

(** The eight bytes of each guard cell lie in the image's segments (seg_rom answers there). *)
Lemma guards_rom : forall i, 0 <= i < 8 ->
  seg_rom rsegs (wa (RATE_GOT_GUARD + i)) <> None /\ seg_rom rsegs (wa (RATE_GUARD + i)) <> None.
Proof.
  intros i Hi. unfold RATE_GOT_GUARD, RATE_GUARD.
  assert (E : i = 0 \/ i = 1 \/ i = 2 \/ i = 3 \/ i = 4 \/ i = 5 \/ i = 6 \/ i = 7) by lia.
  destruct E as [->|[->|[->|[->|[->|[->|[->| ->]]]]]]]; split; vm_compute; intros H; discriminate H.
Qed.

(** A range where seg_rom answers and a range where it does not are apart. *)
Lemma rom_apart : forall A k c n,
  (forall i, 0 <= i < k -> seg_rom rsegs (wa (A + i)) <> None) ->
  (forall a, c <= a < c + n -> seg_rom rsegs (wa a) = None) -> 0 < k -> 0 < n ->
  A + k <= c \/ c + n <= A.
Proof.
  intros A k c n HA HB Hk Hn.
  destruct (Z_le_gt_dec (A + k) c) as [H1|H1]; [left; exact H1|].
  destruct (Z_le_gt_dec (c + n) A) as [H2|H2]; [right; exact H2|].
  exfalso. apply (HA (Z.max A c - A)); [lia|].
  replace (A + (Z.max A c - A)) with (Z.max A c) by lia. apply HB. lia.
Qed.

(** The bytes of a one-block rw_cells. *)
Lemma rw_cb_bytes : forall m A n bs, rw_cells rsegs m A [CB n bs] -> bytes_at rsegs m A bs.
Proof.
  intros m A n bs [[_ HB] _]. cbn [cells_bytes cbytes] in HB. rewrite app_nil_r in HB. exact HB.
Qed.

Ltac ret_even := rewrite ret_pc_even by (first [lia | reflexivity]).
Ltac fp_sub := unfold sub_fp; let x := fresh "x" in let Hx := fresh "Hx" in
  intros x Hx; cbn [outside] in *; repeat split; try exact I; lia.

Theorem rate_csv_holds : memset_contract -> reac_rate_drivable_csv_contract -> check_csv_contract ->
  rate_csv_contract.
Proof.
  intros MEMSET DCSV CHK. unfold rate_csv_contract.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
         F fc m junk mask buflen cb pod lo canary
         -> Hcb0 Hcb16 -> -> -> -> Hmask Hbuflen HRW HROMB HCBLO HSTK HLO HSPA HLOMIN HSP63 HROM HG1 HG2 HF HMI HTM.
  clear Hcb16 HSPA.
  remember (rate_bl buflen) as bl eqn:EBL.
  try rewrite <- EBL in HRW; try rewrite <- EBL in HROMB; try rewrite <- EBL in HCBLO.
  assert (HBL : bl = Z.max buflen 1) by (subst bl; unfold rate_bl; destruct (Z.eqb_spec buflen 0); lia).
  clear EBL.
  unfold CSV_STACK, STACK_LO_MIN, RATE_CSV, RATE_FREE in *.
  pose proof (rw_cells_bound rsegs m cb _ HRW) as [HB1 HB2]. cbn [cells_size csize] in HB2.
  assert (HB3 : cb + bl <= 2^64) by lia.
  (* the guard cells lie apart from the buf block *)
  pose proof (rom_apart RATE_GOT_GUARD 8 cb bl (fun i Hi => proj1 (guards_rom i Hi)) HROMB ltac:(lia) ltac:(lia))
    as DG1.
  pose proof (rom_apart RATE_GUARD 8 cb bl (fun i Hi => proj2 (guards_rom i Hi)) HROMB ltac:(lia) ltac:(lia))
    as DG2.
  assert (HUcb : bv_unsigned (Z_to_bv 64 cb) = cb) by (apply unsigned_lit; lia).
  (* 0x14628 beqz a0: not taken *)
  step.
  first [ if_false
        | let K := fresh "K" in
          if_cases K; [exfalso; zify_cond K; rewrite ?Z.mod_small in K by lia; lia | cbv iota] ].
  (* 0x1462c mv s4,a0; addi a1,zero,0x5a; mv a2,s5; jal memset *)
  step. step. step. step.
  eapply evt_cut.
  { eapply MEMSET with (junk := junk).
    - rewrite (unsigned_lit cb), (unsigned_lit bl) by lia. exact HRW.
    - exact HMI. }
  intros ms' Hpost. unfold memset_post in Hpost.
  destruct Hpost as (t0a & t1a & t2a & a1a & a2a & a3a & a4a & a5a & a6a & a7a & t3a & t4a & t5a & t6a & m1 &
                     -> & MU1 & WM1 & MI1 & RW1).
  ret_even.
  rewrite (unsigned_lit cb), (unsigned_lit bl) in MU1, RW1 by lia.
  match type of RW1 with context [Z_to_bv 8 ?v] =>
    replace (Z_to_bv 8 v) with (Z_to_bv 8 0x5a) in RW1 by (apply bv_eq; vm_compute; reflexivity) end.
  (* the memory after memset *)
  assert (DJ1 : forall A k, (A + k <= cb \/ cb + bl <= A) -> disjoint_from [(cb, cb + bl)] A k)
    by (intros A k H; cbn [disjoint_from]; split; [lia | exact I]).
  assert (HG1a : bytes_at rsegs m1 RATE_GOT_GUARD (le8 (Z_to_bv 64 RATE_GUARD))).
  { apply (bytes_at_transport rsegs _ m m1 _ _ HG1 MU1). rewrite length_le8. apply DJ1. lia. }
  assert (HG2a : bytes_at rsegs m1 RATE_GUARD (le8 canary)).
  { apply (bytes_at_transport rsegs _ m m1 _ _ HG2 MU1). rewrite length_le8. apply DJ1. lia. }
  assert (ST1 : stk rsegs m1 lo (bv_unsigned sp)).
  { apply (stk_transport_disjoint rsegs _ m m1 _ _ HSTK MU1 WM1). apply DJ1. lia. }
  destruct (stk_split rsegs m1 lo (bv_unsigned sp - 8192) (bv_unsigned sp) ST1 ltac:(lia)) as [STa STb].
  assert (TM1 : MemNorm.task_mem rsegs m1).
  { apply (task_mem_munch [(cb, cb + bl)] m m1 HTM MU1). intros x Hx. cbn [outside] in Hx.
    pose proof HRW as [_ (W0 & W1 & W)]. cbn [cells_size csize] in W.
    pose proof (W (bv_unsigned x - cb)) as Wx. replace (cb + (bv_unsigned x - cb)) with (bv_unsigned x) in Wx by lia.
    unfold wa in Wx. rewrite Z_to_bv_lit_self in Wx. apply Wx. lia. }
  (* 0x1463c mv a0,s10; mv a1,s4; mv a2,s0; jal reac_rate_drivable_csv *)
  step. step. step. step.
  pose proof DCSV as HD. unfold reac_rate_drivable_csv_contract in HD. cbv zeta in HD.
  eapply evt_cut.
  { eapply HD with (lo := bv_unsigned sp - 8192) (canary := canary)
                   (junk := repeat (Z_to_bv 8 0x5a) (Z.to_nat bl));
      rewrite ?(unsigned_lit mask), ?(unsigned_lit cb), ?(unsigned_lit buflen) by lia.
    - lia.
    - intros Hn. split; [lia|]. split; [|lia].
      replace (Z.to_nat buflen) with (Z.to_nat bl) by lia. exact RW1.
    - exact STb.
    - unfold DCSV_K, DCSV_F, SNPRINTF_K. lia.
    - unfold IMG_END. lia.
    - exact HSP63.
    - exact HF.
    - exact MI1.
    - exact TM1.
    - exact HG1a.
    - exact HG2a. }
  intros ms' (t0b & t1b & t2b & a1b & a2b & a3b & a4b & a5b & a6b & a7b & t3b & t4b & t5b & t6b & F2 & fc2 & m2 &
              -> & HF2 & HFk & WM2 & MI2 & TM2 & ST2 & H0 & HP).
  ret_even.
  rewrite ?(unsigned_lit buflen) in H0 by lia.
  rewrite ?(unsigned_lit mask), ?(unsigned_lit cb), ?(unsigned_lit buflen) in HP by lia.
  (* the memory after drivable_csv *)
  assert (MU2 : munch [(bv_unsigned sp - 8192, bv_unsigned sp); (cb, cb + bl)] m1 m2).
  { destruct (Z.eq_dec buflen 0) as [E|E].
    - eapply munch_weaken; [|exact (H0 E)]. fp_sub.
    - destruct (HP ltac:(lia)) as [MU _]. replace bl with buflen by lia. exact MU. }
  assert (ST2b : stk rsegs m2 lo (bv_unsigned sp)).
  { apply (stk_merge rsegs m2 lo (bv_unsigned sp - 8192) (bv_unsigned sp)); [| exact ST2 | lia].
    apply (stk_transport_disjoint rsegs _ m1 m2 _ _ STa MU2 WM2). cbn [disjoint_from].
    repeat split; try exact I; lia. }
  assert (B0 : buflen = 0 -> bytes_at rsegs m2 cb [Z_to_bv 8 0x5a]).
  { intros E. pose proof (rw_cb_bytes m1 cb _ _ RW1) as HB.
    replace (Z.to_nat bl) with 1%nat in HB by lia. cbn [repeat] in HB.
    apply (bytes_at_transport rsegs _ m1 m2 _ _ HB (H0 E)). cbn [disjoint_from length]. split; [lia | exact I]. }
  (* 0x1464c mv a2,a0; mv a0,s4; mv a1,s0; mv a3,s10; jal check_csv *)
  step. step. step. step. step.
  pose proof CHK as HC. unfold check_csv_contract in HC. cbv zeta in HC.
  pose proof (csv_list_length mask ltac:(lia)) as HLL.
  eapply evt_cut.
  { eapply HC with (lo := lo);
      rewrite ?(unsigned_lit mask), ?(unsigned_lit cb), ?(unsigned_lit buflen) by lia.
    - apply unsigned_lit. lia.
    - lia.
    - exact B0.
    - intros Hn. exact (proj2 (HP Hn)).
    - left. lia.
    - exact ST2b.
    - unfold CHECK_CSV_FRAME. lia.
    - exact HROM.
    - exact MI2. }
  intros ms' (t0c & t1c & t2c & a0c & a1c & a2c & a3c & a4c & a5c & a6c & a7c & t3c & t4c & t5c & t6c & m3 &
              -> & MU3 & WM3 & MI3 & ST3).
  ret_even.
  (* 0x14660: the contract's postcondition *)
  apply evt_done.
  do 29 eexists. split; [reflexivity|].
  split; [exact HF2|].
  split.
  { apply (munch_trans _ m m1 m3); [eapply munch_weaken; [|exact MU1]; fp_sub|].
    apply (munch_trans _ m1 m2 m3); [eapply munch_weaken; [|exact MU2]; fp_sub|].
    eapply munch_weaken; [|exact MU3]. unfold CHECK_CSV_FRAME. fp_sub. }
  split; [exact (wmono_trans rsegs m m1 m3 WM1 (wmono_trans rsegs m1 m2 m3 WM2 WM3))|].
  split; [exact MI3 | exact ST3].
Qed.
