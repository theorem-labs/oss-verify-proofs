(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Copyright 2026 Theorem Labs *)
(* New for libdiginet/fuzz_decode: the cursor loop of LLVMFuzzerTestOneInput on the UBSan image (fuzz_decode.ubsan,
   fuzz_decode.c:306-321), from the cut 0x12df8 to the cut 0x12e8c (LLVMFuzzerTestOneInput_mid.v), an evt walk over
   the contracts of its callees:
   - 0x12df8-0x12e14: diginet_cursor_init (&c, body, len) at 0x12e04 (c = sp + 0x130); then status a0 = 0, at a2 = 0,
     s3 = 1, a1 = 1;
   - one pass from the loop head 0x12e18 (s4 = the pass number, from 1): spec_msg_step (body, len, at, status & 0xff,
     &m) at 0x12e2c (m = sp + 0x18), memset (&msg, 0, 40) at 0x12e3c (msg = sp + 0xe0), r = diginet_msg_next (&c,
     &msg) at 0x12e48, check_cursor_step (&m, r, &c) at 0x12e58, and when m.code = 1 check_cursor_message (body, &m,
     &msg) at 0x12e70; the loop leaves at 0x12e78 when m.code = 0, else it takes at = m.next (0x12e7c), status =
     m.status_out (0x12e80), a1 = s4 + 1, and runs again while len >=u s4 (0x12e88), else it leaves.
   The loop leaves after at most len + 1 passes (s4 against len). No check aborts: at every pass the step of spec.h
   and the library's step agree (LLVMFuzzerTestOneInput_cursor_m.v), so the model boolean of each check holds, and
   the cursor in memory holds the pair (at, status) the next pass starts from.
   Memory at the loop head: the facts of mid_inv, the 8 bytes at sp, and in the 376 bytes from sp + 0x10 the cursor
   (cursor_cells, 25 bytes at sp + 0x130) and two stack ranges (stk) for the rest; a pass carves m (56 bytes at
   sp + 0x18) and msg (40 bytes at sp + 0xe0) out of the first range and gives them back. *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libdiginet.fuzz_decode.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.libdiginet.fuzz_decode.lib.U.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.libdiginet.fuzz_decode.lib.U.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14.
From OSSVerify.Proofs.libdiginet.fuzz_decode.lib.U.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.libdiginet.fuzz_decode.lib.U Require Import Contract Img0.
From OSSVerify.Proofs.libdiginet.fuzz_decode.lib.Lib Require Import PropExec MState Mem Exec Frame Step Cells Tac.
From OSSVerify.Proofs.libdiginet.fuzz_decode.lib.Spec Require Import DgnSpec DgnLib DgnDecHarness DgnAgreeCursor.
From OSSVerify.Proofs.libdiginet.fuzz_decode.lib.U.Prog Require Import LLVMFuzzerTestOneInput_c
  LLVMFuzzerTestOneInput_fr LLVMFuzzerTestOneInput_mid LLVMFuzzerTestOneInput_cursor_m DgnLayout
  diginet_cursor_init_c diginet_msg_next_c spec_msg_step_c memset_c check_cursor_step_c check_cursor_message_c.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* ---- machine values ---- *)

(* 0x12e1c andi a3, a0, 0xff on a status byte *)
Lemma andi_byte : forall st, 0 <= st < 256 -> Z_to_bv 64 (Z.land (bv_unsigned (Z_to_bv 64 st)) 255) = Z_to_bv 64 st.
Proof.
  intros st H. rewrite unsigned_lit by lia. change 255 with (Z.ones 8).
  rewrite Z.land_ones by lia. rewrite Z.mod_small by (change (2 ^ 8) with 256; lia). reflexivity.
Qed.

(* lw of a C int *)
Lemma sx32_lit : forall c, -2^31 <= c < 2^31 -> sx32 (Z_to_bv 64 c) = Z_to_bv 64 c.
Proof.
  intros c H. unfold sx32. f_equal. rewrite Z_to_bv_unsigned.
  rewrite (bv_swrap_congr 32 (bv_wrap 64 c) c).
  - apply bv_swrap_small. change (bv_half_modulus 32) with (2^31). lia.
  - unfold bv_wrap, bv_modulus. change (Z.of_N 64) with 64. change (Z.of_N 32) with 32.
    apply mod_mod_pow2. lia.
Qed.

(* lbu of a byte *)
Lemma zxb_b8 : forall z, 0 <= z < 256 -> zxb (b8 z) = Z_to_bv 64 z.
Proof.
  intros z H. unfold zxb. change (bv_unsigned (b8 z)) with (bz (b8 z)).
  rewrite bz_b8 by (change (2 ^ 8) with 256; lia). reflexivity.
Qed.

(* beq / bne of two words that hold C values *)
Lemma eqb_lit : forall a b, -2^63 <= a < 2^63 -> -2^63 <= b < 2^63 ->
  bv_eqb (Z_to_bv 64 a) (Z_to_bv 64 b) = (a =? b).
Proof.
  intros a b Ha Hb. unfold bv_eqb. rewrite !unsigned_lit_wrap.
  destruct (Z.eqb_spec a b) as [->|Hne]; [apply Z.eqb_refl|].
  apply Z.eqb_neq. intros E. apply Hne. Z.div_mod_to_equations. lia.
Qed.

(* bgeu of two sizes *)
Lemma ltu_lit : forall a b, 0 <= a < 2^64 -> 0 <= b < 2^64 -> bv_ltu (Z_to_bv 64 a) (Z_to_bv 64 b) = (a <? b).
Proof. intros a b Ha Hb. unfold bv_ltu. rewrite !unsigned_lit by lia. reflexivity. Qed.

(* the alignment of sp, kept from lia *)
Definition al16 (x : Z) : Prop := x mod 16 = 0.

Lemma al16_8 : forall x k, al16 x -> k mod 8 = 0 -> (x + k) mod 8 = 0.
Proof. unfold al16. intros x k H1 H2. Z.div_mod_to_equations. lia. Qed.

(* ---- the 376 bytes from sp + 0x10 ---- *)

Lemma stk_rw_cb : forall m a b n, stk rsegs m a b -> b = a + Z.of_nat n -> exists j, rw_cells rsegs m a [CB n j].
Proof.
  intros m a b n H E. subst b.
  destruct (stk_carve rsegs m a (a + Z.of_nat n) n H ltac:(lia)) as [_ [j Hj]].
  exists j. replace (a + Z.of_nat n - Z.of_nat n) with a in Hj by lia. exact Hj.
Qed.

Lemma msg_cells_size : forall body mj r, cells_size (msg_cells body mj r) = 40%nat.
Proof.
  intros body mj r. unfold msg_cells. destruct (is_end r); [reflexivity|].
  destruct (writes_len (mr_kind r)); reflexivity.
Qed.

(* at 0x12df8: the cursor's 25 bytes, and the two ranges around it *)
Lemma init_region : forall m Sp j1, rw_cells rsegs m (Sp + 16) [CB 376 j1] ->
  stk rsegs m (Sp + 16) (Sp + 304) /\ (exists jc, rw_cells rsegs m (Sp + 304) [CB 25 jc]) /\
  stk rsegs m (Sp + 329) (Sp + 392).
Proof.
  intros m Sp j1 H. pose proof (stk_of_rw_cells rsegs m _ _ H) as S.
  replace (Sp + 16 + Z.of_nat (cells_size [CB 376 j1])) with (Sp + 392) in S
    by (change (Z.of_nat (cells_size [CB 376 j1])) with 376; lia).
  destruct (stk_split rsegs m _ (Sp + 304) _ S ltac:(lia)) as [S1 R1].
  destruct (stk_split rsegs m _ (Sp + 329) _ R1 ltac:(lia)) as [S2 S3].
  split; [exact S1|]. split; [apply (stk_rw_cb m _ _ 25 S2); lia | exact S3].
Qed.

(* at the loop head: m (56 bytes at sp + 0x18) and msg (40 bytes at sp + 0xe0) out of the first range *)
Lemma head_region : forall m Sp, stk rsegs m (Sp + 16) (Sp + 304) ->
  stk rsegs m (Sp + 16) (Sp + 24) /\ (exists jm, rw_cells rsegs m (Sp + 24) [CB 56 jm]) /\
  stk rsegs m (Sp + 80) (Sp + 224) /\ (exists jq, rw_cells rsegs m (Sp + 224) [CB 40 jq]) /\
  stk rsegs m (Sp + 264) (Sp + 304).
Proof.
  intros m Sp H.
  destruct (stk_split rsegs m _ (Sp + 24) _ H ltac:(lia)) as [S1 R1].
  destruct (stk_split rsegs m _ (Sp + 80) _ R1 ltac:(lia)) as [S2 R2].
  destruct (stk_split rsegs m _ (Sp + 224) _ R2 ltac:(lia)) as [S3 R3].
  destruct (stk_split rsegs m _ (Sp + 264) _ R3 ltac:(lia)) as [S4 S5].
  split; [exact S1|]. split; [apply (stk_rw_cb m _ _ 56 S2); lia|].
  split; [exact S3|]. split; [apply (stk_rw_cb m _ _ 40 S4); lia|]. exact S5.
Qed.

(* after a pass: m and msg back into the first range *)
Lemma pass_region : forall m Sp cm cq,
  stk rsegs m (Sp + 16) (Sp + 24) -> rw_cells rsegs m (Sp + 24) cm -> cells_size cm = 56%nat ->
  stk rsegs m (Sp + 80) (Sp + 224) -> rw_cells rsegs m (Sp + 224) cq -> cells_size cq = 40%nat ->
  stk rsegs m (Sp + 264) (Sp + 304) ->
  stk rsegs m (Sp + 16) (Sp + 304).
Proof.
  intros m Sp cm cq S1 M Hm S2 Q Hq S3.
  pose proof (stk_of_rw_cells rsegs m _ _ M) as SM. rewrite Hm in SM.
  pose proof (stk_of_rw_cells rsegs m _ _ Q) as SQ. rewrite Hq in SQ.
  replace (Sp + 24 + Z.of_nat 56) with (Sp + 80) in SM by lia.
  replace (Sp + 224 + Z.of_nat 40) with (Sp + 264) in SQ by lia.
  apply (stk_merge rsegs m (Sp + 16) (Sp + 24) (Sp + 304)); [exact S1| |lia].
  apply (stk_merge rsegs m (Sp + 24) (Sp + 80) (Sp + 304)); [exact SM| |lia].
  apply (stk_merge rsegs m (Sp + 80) (Sp + 224) (Sp + 304)); [exact S2| |lia].
  apply (stk_merge rsegs m (Sp + 224) (Sp + 264) (Sp + 304)); [exact SQ|exact S3|lia].
Qed.

(* at the exit: the 376 bytes as junk *)
Lemma exit_region : forall m Sp cc, stk rsegs m (Sp + 16) (Sp + 304) -> rw_cells rsegs m (Sp + 304) cc ->
  cells_size cc = 25%nat -> stk rsegs m (Sp + 329) (Sp + 392) ->
  exists j1, rw_cells rsegs m (Sp + 16) [CB 376 j1].
Proof.
  intros m Sp cc S1 C Hc S3. pose proof (stk_of_rw_cells rsegs m _ _ C) as SC. rewrite Hc in SC.
  replace (Sp + 304 + Z.of_nat 25) with (Sp + 329) in SC by lia.
  apply (stk_rw_cb m (Sp + 16) (Sp + 392) 376); [|lia].
  apply (stk_merge rsegs m _ (Sp + 304) _); [exact S1| |lia].
  apply (stk_merge rsegs m _ (Sp + 329) _); [exact SC|exact S3|lia].
Qed.

(* the memory at the loop head (after the cursor's set-up or a pass): the cut's facts, the 8 bytes at sp, the
   cursor at sp + 0x130 holding (pos, st), and the rest of the 376 bytes as stack *)
Definition chead_mem (sv : list cell) (Sp lo buf body : Z) (bb : list byte) (m0 m : word -> option byte)
    (j0 : list byte) (pos : nat) (st : Z) : Prop :=
  mid_inv sv Sp lo buf body bb m0 m /\ rw_cells rsegs m Sp [CB 8 j0] /\
  stk rsegs m (Sp + 16) (Sp + 304) /\
  rw_cells rsegs m (Sp + 304) (cursor_cells body (Z.of_nat (length bb)) pos st) /\
  stk rsegs m (Sp + 329) (Sp + 392).

(* ---- tactics of the walk ---- *)

(* a callee's premise *)
Local Ltac side :=
  try unfold SPEC_MSG_STEP_FRAME, CHECK_CURSOR_STEP_FRAME, CHECK_CURSOR_MESSAGE_FRAME, SM_SIZE, DM_SIZE;
  rewrite ?unsigned_lit by lia;
  first [ assumption
        | apply al16_8; [assumption | reflexivity]
        | lia ].

(* the return address after a call *)
Local Ltac fix_ret :=
  lazymatch goal with
  | |- evt _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) =>
      replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [lia | reflexivity])
  end.

(* the cut 0x12e8c from the memory after a pass *)
Local Ltac cexit :=
  lazymatch goal with
  | S1 : stk rsegs ?m (?Sp + 16) (?Sp + 24), HMa : rw_cells rsegs ?m (?Sp + 24) _,
    S2 : stk rsegs ?m (?Sp + 80) (?Sp + 224), HQa : rw_cells rsegs ?m (?Sp + 224) (msg_cells _ _ _),
    S3 : stk rsegs ?m (?Sp + 264) (?Sp + 304), HCa : rw_cells rsegs ?m (?Sp + 304) (cursor_cells _ _ _ _),
    SZ : stk rsegs ?m (?Sp + 329) (?Sp + 392), HJ0 : rw_cells rsegs ?m ?Sp [CB 8 ?j0] |- _ =>
      let j1 := fresh "j1" in let HJ1 := fresh "HJ1" in
      destruct (exit_region m Sp _ (pass_region m Sp _ _ S1 HMa eq_refl S2 HQa (msg_cells_size _ _ _) S3)
                  HCa eq_refl SZ) as [j1 HJ1];
      apply evt_done; unfold mid_at;
      do 26 eexists; exists m, j0, j1;
      split; [reflexivity|];
      split; [unfold mid_inv; repeat (split; [assumption|]); assumption | split; assumption]
  end.

(* the loop head's memory from the memory after a pass *)
Local Ltac cmem :=
  lazymatch goal with
  | S1 : stk rsegs ?m (?Sp + 16) (?Sp + 24), HMa : rw_cells rsegs ?m (?Sp + 24) _,
    S2 : stk rsegs ?m (?Sp + 80) (?Sp + 224), HQa : rw_cells rsegs ?m (?Sp + 224) (msg_cells _ _ _),
    S3 : stk rsegs ?m (?Sp + 264) (?Sp + 304) |- _ =>
      unfold chead_mem;
      split; [unfold mid_inv; repeat (split; [assumption|]); assumption|];
      split; [assumption|];
      split; [exact (pass_region m Sp _ _ S1 HMa eq_refl S2 HQa (msg_cells_size _ _ _) S3)|];
      split; assumption
  end.

(* ---- the loop ---- *)

Lemma cursor_loop :
  diginet_msg_next_contract -> spec_msg_step_contract -> memset_contract ->
  check_cursor_step_contract -> check_cursor_message_contract ->
  forall F fc gp tp sv Sp lo buf nn body bb m0,
  mid_env sv Sp lo buf nn body bb ->
  forall (K : nat) (k : Z) (pos : nat) (st : Z) (j0 : list byte) (m : word -> option byte)
    (x1 x5 x6 x7 x8 x13 x14 x15 x16 x17 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word),
  Z.to_nat (Z.of_nat (length bb) + 1 - k) = K -> 1 <= k <= Z.of_nat (length bb) + 1 ->
  (pos <= length bb)%nat -> st_ok st ->
  chead_mem sv Sp lo buf body bb m0 m j0 pos st ->
  evt rsegs (mid_at F fc gp tp sv Sp lo buf body bb m0 LLVM_PC_CURSOR_OUT)
    (MS (mkR x1 (Z_to_bv 64 Sp) gp tp x5 x6 x7 x8 (Z_to_bv 64 (Z.of_nat (length bb))) (Z_to_bv 64 st)
           (Z_to_bv 64 k) (Z_to_bv 64 (Z.of_nat pos)) x13 x14 x15 x16 x17 (Z_to_bv 64 body) (Z_to_bv 64 1)
           x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
        F (Z_to_bv 64 0x12e18) fc None m (seg_rom rsegs)).
Proof.
  intros CMN CSS CMS CCS CCM F fc gp tp sv Sp lo buf nn body bb m0 ENV.
  pose proof ENV as (Hlo & Hlo2 & HAL & Hsp & Hbuf & Hnn & Hbn & Hbb & Hbe & Hsv).
  replace ALLOC_STACK with 8192 in Hlo2 by reflexivity.
  unfold LLVM_FRAME in Hsp. unfold mid_len in Hbe.
  change (Sp mod 16 = 0) with (al16 Sp) in HAL.
  assert (HLB : Z.of_nat (length bb) < 2 ^ 26) by lia.
  intros K. induction K as [K IH] using lt_wf_ind.
  intros k pos st j0 m x1 x5 x6 x7 x8 x13 x14 x15 x16 x17 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31
    HK Hk Hpos Hst HM.
  destruct HM as ((MI & ST & HSV & HBUF & HB & MU0 & WM0) & HJ0 & SR & HC & SZ).
  unfold LLVM_FRAME in MU0.
  assert (Hst8 : 0 <= st < 256) by (unfold st_ok in Hst; lia).
  destruct (head_region m Sp SR) as (S1 & (jm & HMj) & S2 & (jq & HQj) & S3). clear SR.

  (* 0x12e18-0x12e2c: s4 = a1, a3 = status & 0xff, a4 = &m, a0 = body, a1 = len, jal spec_msg_step *)
  do 6 step.
  rewrite andi_byte by exact Hst8.
  eapply evt_cut.
  { eapply CSS with (b := body) (len := Z.of_nat (length bb)) (pos := Z.of_nat pos) (st := st) (mp := Sp + 24)
      (lo := lo) (bs := bb) (junk := jm).
    all: side. }
  intros ms' (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & m1 & -> & MU & WM & MI1 & ST1 & HM1).
  unfold SPEC_MSG_STEP_FRAME in MU. rewrite ?unsigned_lit in MU, ST1 by lia.
  fix_ret. transport_after_call rsegs m m1 MU WM. clear MU WM MI.
  rewrite spec_msg_step_res_u in HM1. unfold spec_msg_cells, res_spec in HM1.
  cbn [sm_code sm_at sm_len sm_next sm_status sm_running sm_d1 sm_d2 sm_status_out sm_sysex_at sm_sysex_len] in HM1.

  (* 0x12e30-0x12e3c: memset (&msg, 0, 40) *)
  do 4 step.
  eapply evt_cut.
  { eapply CMS with (junk := jq). all: side. }
  intros ms' PO. unfold memset_post in PO.
  destruct PO as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & m2 & -> & MU & WM & MI2 & HQ2).
  rewrite ?unsigned_lit in MU, HQ2 by lia.
  change (Z.to_nat 40) with 40%nat in HQ2. change (0 mod 256) with 0 in HQ2.
  fix_ret. transport_after_call rsegs m1 m2 MU WM. clear MU WM MI1.

  (* 0x12e40-0x12e48: r = diginet_msg_next (&c, &msg) *)
  do 3 step.
  eapply evt_cut.
  { eapply CMN with (c := Sp + 304) (mp := Sp + 224) (body := body) (bb := bb) (mj := repeat (Z_to_bv 8 0) 40)
      (pos := pos) (st := st).
    all: side. }
  intros ms' (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & m3 & -> & MU & WM & MI3 & HC3 & HQ3).
  fix_ret. transport_after_call rsegs m2 m3 MU WM. clear MU WM MI2.

  (* 0x12e4c-0x12e58: check_cursor_step (&m, r, &c) *)
  do 4 step.
  pose proof (mr_code_range (msg_step bb pos st)) as Hcode.
  assert (K1 : check_cursor_step_ok (res_spec (msg_step bb pos st)) (mr_code (msg_step bb pos st))
                 (DgnCursor (Z.of_nat (length bb)) (Z.of_nat (mr_pos (msg_step bb pos st)))
                    (mr_st (msg_step bb pos st))) = true)
    by exact (check_cursor_step_ok_refl (res_spec (msg_step bb pos st)) (Z.of_nat (length bb))).
  assert (K2 : -2^31 <= sm_code (res_spec (msg_step bb pos st)) < 2^31) by (cbn [res_spec sm_code]; lia).
  assert (K3 : -2^31 <= mr_code (msg_step bb pos st) < 2^31) by lia.
  assert (K4 : 0 <= dc_pos (DgnCursor (Z.of_nat (length bb)) (Z.of_nat (mr_pos (msg_step bb pos st)))
                              (mr_st (msg_step bb pos st)))) by (cbn [dc_pos]; lia).
  assert (RM : ro_cells rsegs m3 (Sp + 24) (spec_msg_cells (res_spec (msg_step bb pos st)))) by exact (proj1 HM1).
  assert (RC : ro_cells rsegs m3 (Sp + 304)
      (cursor_cells body (dc_len (DgnCursor (Z.of_nat (length bb)) (Z.of_nat (mr_pos (msg_step bb pos st)))
                                    (mr_st (msg_step bb pos st))))
         (Z.to_nat (dc_pos (DgnCursor (Z.of_nat (length bb)) (Z.of_nat (mr_pos (msg_step bb pos st)))
                              (mr_st (msg_step bb pos st)))))
         (dc_status (DgnCursor (Z.of_nat (length bb)) (Z.of_nat (mr_pos (msg_step bb pos st)))
                       (mr_st (msg_step bb pos st)))))).
  { cbn [dc_len dc_pos dc_status]. rewrite Nat2Z.id. exact (proj1 HC3). }
  eapply evt_cut.
  { eapply CCS with (p := Sp + 24) (c := Sp + 304) (body := body) (r := mr_code (msg_step bb pos st)) (lo := lo)
      (sm := res_spec (msg_step bb pos st))
      (cur := DgnCursor (Z.of_nat (length bb)) (Z.of_nat (mr_pos (msg_step bb pos st))) (mr_st (msg_step bb pos st))).
    all: side. }
  clear K1 K2 K4 RM RC.
  intros ms' (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & m4 & -> & MU & WM & MI4 & ST4).
  unfold CHECK_CURSOR_STEP_FRAME in MU. rewrite ?unsigned_lit in MU, ST4 by lia.
  fix_ret. transport_after_call rsegs m3 m4 MU WM. clear MU WM MI3.

  (* 0x12e5c: lw a0, 0x18(sp) (m.code); 0x12e60: bne a0, s3 *)
  step. rewrite sx32_lit by exact K3.
  step. rewrite eqb_lit by lia.
  destruct (Z.eqb_spec (mr_code (msg_step bb pos st)) 1) as [E1|E1]; cbv beta iota delta [negb].
  - (* a whole message: 0x12e64-0x12e70 check_cursor_message (body, &m, &msg), 0x12e74 lw a0, 0x18(sp) *)
    do 4 step.
    assert (KM1 : check_cursor_message_ok (res_spec (msg_step bb pos st))
                    (msg_of_step (res_spec (msg_step bb pos st))) = true)
      by (unfold check_cursor_message_ok; apply msg_agrees_of_step).
    assert (KM2 : 0 <= sm_status (res_spec (msg_step bb pos st)) < 256)
      by exact (msg_step_status_range bb pos st Hst).
    assert (KM3 : sm_status (res_spec (msg_step bb pos st)) = 240 ->
                  sm_sysex_at (res_spec (msg_step bb pos st)) <> 0).
    { intros H. destruct (msg_step_f0 bb pos st Hst H) as [S1' _].
      change (Z.of_nat (mr_sysex (msg_step bb pos st)) <> 0). rewrite S1'. lia. }
    assert (KM4 : sm_status (res_spec (msg_step bb pos st)) = 240 ->
                  0 < body /\ 0 <= sm_sysex_at (res_spec (msg_step bb pos st)) /\
                  body + sm_sysex_at (res_spec (msg_step bb pos st)) < 2^64).
    { intros H. destruct (msg_step_f0 bb pos st Hst H) as [S1' S2'].
      change (0 < body /\ 0 <= Z.of_nat (mr_sysex (msg_step bb pos st)) /\
              body + Z.of_nat (mr_sysex (msg_step bb pos st)) < 2^64).
      rewrite S1'. lia. }
    assert (RM : ro_cells rsegs m4 (Sp + 24) (spec_msg_cells (res_spec (msg_step bb pos st)))) by exact (proj1 HM1).
    assert (RQ : ro_cells rsegs m4 (Sp + 224)
        (dmsg_cells body (firstn 4 (skipn 4 (repeat (Z_to_bv 8 0) 40))) (msg_of_step (res_spec (msg_step bb pos st))))).
    { rewrite <- (msg_cells_dmsg bb pos st body (repeat (Z_to_bv 8 0) 40) E1). exact (proj1 HQ3). }
    eapply evt_cut.
    { eapply CCM with (b := body) (p := Sp + 24) (q := Sp + 224) (lo := lo) (sm := res_spec (msg_step bb pos st))
        (msg := msg_of_step (res_spec (msg_step bb pos st))) (pad := firstn 4 (skipn 4 (repeat (Z_to_bv 8 0) 40))).
      all: side. }
    clear KM1 KM2 KM3 KM4 RM RQ.
    intros ms' (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & m5 & -> & MU & WM & MI5 & ST5).
    unfold CHECK_CURSOR_MESSAGE_FRAME in MU. rewrite ?unsigned_lit in MU, ST5 by lia.
    fix_ret. transport_after_call rsegs m4 m5 MU WM. clear MU WM MI4.
    step. rewrite sx32_lit by exact K3.
    (* 0x12e78: beqz a0 *)
    step. rewrite eqb_lit by lia.
    destruct (Z.eqb_spec (mr_code (msg_step bb pos st)) 0) as [E0|E0]; cbv beta iota; [exfalso; lia|].
    (* 0x12e7c ld a2, 0x30(sp) (m.next); 0x12e80 lbu a0, 0x3c(sp) (m.status_out); 0x12e84 a1 = s4 + 1 *)
    do 3 step.
    rewrite zxb_b8 by (pose proof (msg_step_st_ok bb pos st Hst) as X; unfold st_ok in X; lia).
    (* 0x12e88: bgeu s1, s4 *)
    step. rewrite ltu_lit by lia.
    destruct (Z.ltb_spec (Z.of_nat (length bb)) k) as [Ek|Ek]; cbv beta iota delta [negb].
    + cexit.
    + eapply (IH (Z.to_nat (Z.of_nat (length bb) + 1 - (k + 1))) ltac:(lia) (k + 1) (mr_pos (msg_step bb pos st))
        (mr_st (msg_step bb pos st)) j0).
      * reflexivity.
      * lia.
      * apply msg_step_pos_le. exact Hpos.
      * apply msg_step_st_ok. exact Hst.
      * cmem.
  - (* no whole message: 0x12e78 beqz a0 *)
    step. rewrite eqb_lit by lia.
    destruct (Z.eqb_spec (mr_code (msg_step bb pos st)) 0) as [E0|E0]; cbv beta iota.
    + cexit.
    + do 3 step.
      rewrite zxb_b8 by (pose proof (msg_step_st_ok bb pos st Hst) as X; unfold st_ok in X; lia).
      step. rewrite ltu_lit by lia.
      destruct (Z.ltb_spec (Z.of_nat (length bb)) k) as [Ek|Ek]; cbv beta iota delta [negb].
      * cexit.
      * eapply (IH (Z.to_nat (Z.of_nat (length bb) + 1 - (k + 1))) ltac:(lia) (k + 1)
          (mr_pos (msg_step bb pos st)) (mr_st (msg_step bb pos st)) j0).
        -- reflexivity.
        -- lia.
        -- apply msg_step_pos_le. exact Hpos.
        -- apply msg_step_st_ok. exact Hst.
        -- cmem.
Qed.

(* ---- the segment ---- *)

Lemma llvm_cursor_evt :
  diginet_cursor_init_contract -> diginet_msg_next_contract -> spec_msg_step_contract -> memset_contract ->
  check_cursor_step_contract -> check_cursor_message_contract ->
  forall F fc gp tp sv Sp lo buf nn body bb m0 ms,
    mid_env sv Sp lo buf nn body bb ->
    mid_at F fc gp tp sv Sp lo buf body bb m0 LLVM_PC_BODY ms ->
    evt rsegs (mid_at F fc gp tp sv Sp lo buf body bb m0 LLVM_PC_CURSOR_OUT) ms.
Proof.
  intros CCI CMN CSS CMS CCS CCM F fc gp tp sv Sp lo buf nn body bb m0 ms ENV AT.
  pose proof ENV as (Hlo & Hlo2 & HAL & Hsp & Hbuf & Hnn & Hbn & Hbb & Hbe & Hsv).
  replace ALLOC_STACK with 8192 in Hlo2 by reflexivity.
  unfold LLVM_FRAME in Hsp. unfold mid_len in Hbe.
  change (Sp mod 16 = 0) with (al16 Sp) in HAL.
  assert (HLB : Z.of_nat (length bb) < 2 ^ 26) by lia.
  destruct AT as (x1 & x5 & x6 & x7 & x8 & x10 & x11 & x12 & x13 & x14 & x15 & x16 & x17 & x19 & x20 & x21 & x22
    & x23 & x24 & x25 & x26 & x27 & x28 & x29 & x30 & x31 & m & j0 & j1 & -> & (MI & ST & HSV & HBUF & HB & MU0 & WM0)
    & HJ0 & HJ1).
  unfold LLVM_PC_BODY, mid_len. unfold LLVM_FRAME in MU0.
  destruct (init_region m Sp j1 HJ1) as (SR & (jc & HCj) & SZ). clear HJ1.

  (* 0x12df8-0x12e04: diginet_cursor_init (&c, body, len) *)
  do 4 step.
  eapply evt_cut.
  { eapply CCI with (c := Sp + 304) (body := body) (len := Z.of_nat (length bb)) (cj := jc). all: side. }
  intros ms' (? & ? & m1 & -> & MU & WM & MI1 & HC1).
  replace (body =? 0) with false in HC1 by (symmetry; apply Z.eqb_neq; lia).
  fix_ret. transport_after_call rsegs m m1 MU WM. clear MU WM MI.

  (* 0x12e08-0x12e14: status a0 = 0, at a2 = 0, s3 = 1, a1 = 1, to the loop head *)
  do 4 step.
  eapply (cursor_loop CMN CSS CMS CCS CCM F fc gp tp sv Sp lo buf nn body bb m0 ENV
            (Z.to_nat (Z.of_nat (length bb) + 1 - 1)) 1 0 0 j0 m1).
  - reflexivity.
  - lia.
  - lia.
  - left. reflexivity.
  - unfold chead_mem.
    split; [unfold mid_inv; repeat (split; [assumption|]); assumption|].
    split; [assumption|]. split; [assumption|]. split; assumption.
Qed.
