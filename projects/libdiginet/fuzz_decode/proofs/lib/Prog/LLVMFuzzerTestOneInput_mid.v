(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Copyright 2026 Theorem Labs *)
(* New for libdiginet/fuzz_decode: the run of LLVMFuzzerTestOneInput (plain image) from malloc's return (0x12d38) to
   check_refusal's return (0x13684), put together from the statements of LLVMFuzzerTestOneInput_seg2.v (set-up,
   cursor loop, decoder set-up, decoder loop) and check_refusal (body, len) at 0x13678-0x13680 through its contract;
   the end state q_x has buf in its frame slot and the saved registers as the prologue left them. *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libdiginet.fuzz_decode.lib.Lib Require Import PropExec MState Mem Exec Frame Step Cells Tac Bytes.
From OSSVerify.Proofs.libdiginet.fuzz_decode.lib Require Import Img0.
From OSSVerify.Proofs.libdiginet.fuzz_decode.lib.Spec Require Import DgnSpec DgnLib DgnDecHarness.
From OSSVerify.Proofs.libdiginet.fuzz_decode.lib.Prog Require Import memset_c memcpy_c DgnLayout
  diginet_cursor_init_c diginet_msg_next_c diginet_personality_of_c diginet_decoder_init_c diginet_decoder_next_c
  check_cursor_step_c check_cursor_message_c check_events_step_c check_events_fields_c check_refusal_c
  LLVMFuzzerTestOneInput_seg LLVMFuzzerTestOneInput_seg2.
Import ListNotations.
Open Scope Z_scope.

(* the state after check_refusal, 0x13684: buf in its slot, the saved registers *)
Definition q_x (F : bvmap 5 word) (fc : bv 32) (gp tp : word) (m0 : word -> option byte)
    (Sp lo buf nb : Z) (saved : list cell) (ms : machine_state) : Prop :=
  exists R m' jx jy, ms = MS R F (Z_to_bv 64 0x13684) fc None m' (seg_rom rsegs) /\
    reg_get R 2 = Z_to_bv 64 Sp /\ reg_get R 3 = gp /\ reg_get R 4 = tp /\
    munch [(lo, Sp + 448); (buf, buf + nb)] m0 m' /\ wmono rsegs m0 m' /\ mem_inv rsegs m' /\
    stk rsegs m' lo Sp /\
    rw_cells rsegs m' Sp (CB 16 jx :: C8 (Z_to_bv 64 buf) :: CB 320 jy :: saved).

Lemma mid_fp_loop : forall lo Sp buf nb, sub_fp (loop_fp lo Sp) [(lo, Sp + 448); (buf, buf + nb)].
Proof. intros lo Sp buf nb x Hx. unfold loop_fp. cbn [outside] in *. lia. Qed.

Lemma mid_fp_ref : forall lo Sp buf nb, lo + 160 <= Sp ->
  sub_fp [(Sp - 160, Sp)] [(lo, Sp + 448); (buf, buf + nb)].
Proof. intros lo Sp buf nb H x Hx. cbn [outside] in *. lia. Qed.

(* check_refusal (body, len) from the decoder loop's exit, 0x13678 .. 0x13684 *)
Lemma mid_refusal : check_refusal_contract ->
  forall (x3 x4 : word) (F : bvmap 5 word) (fc : bv 32) (ms0 m0 : word -> option byte)
    (Sp lo body buf nb : Z) (bb j0 : list byte) (w10 : word) (saved : list cell),
  seg_ok Sp body bb -> lo_ok lo Sp body bb -> cells_size saved = 104%nat ->
  w10 = Z_to_bv 64 buf ->
  munch [(lo, Sp + 448); (buf, buf + nb)] ms0 m0 -> wmono rsegs ms0 m0 ->
  dexit (q_x F fc x3 x4 ms0 Sp lo buf nb saved) x3 x4 F fc m0 Sp lo body bb j0 w10 saved.
Proof.
  intros CR x3 x4 F fc ms0 m0 Sp lo body buf nb bb j0 w10 saved SO LO SV -> MU0 WM0.
  intros r1 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r19 r20 r22 r23 r24 r25 r26 r27 r28 r29 r30 r31 m' jj
    MU WM MI ST BA RW.
  destruct SO as (S0 & S1 & S2 & S3 & S4). destruct LO as (L0 & L1 & L2).
  do 3 step.
  eapply evt_cut.
  { apply (CR (Z_to_bv 64 0x13684) (Z_to_bv 64 Sp) x3 x4 r5 r6 r7 r8 r9 r12 r13 r14 r15 r16 r17
      (Z_to_bv 64 (Z.of_nat (length bb))) r19 r20 (Z_to_bv 64 body) r22 r23 r24 r25 r26 r27 r28 r29 r30 r31
      F fc m' body lo bb).
    - lia.
    - exact BA.
    - lia.
    - rewrite unsigned_lit by lia. exact ST.
    - rewrite unsigned_lit by lia. unfold CHECK_REFUSAL_STACK. lia.
    - rewrite unsigned_lit by lia. unfold CHECK_REFUSAL_STACK. lia.
    - exact MI. }
  intros ms' (t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m'' &
    -> & MU2 & WM2 & MI2 & ST2).
  rewrite unsigned_lit in MU2, ST2 by lia. unfold CHECK_REFUSAL_STACK in MU2.
  replace (ret_pc (Z_to_bv 64 0x13684)) with (Z_to_bv 64 0x13684) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
  apply evt_done. unfold q_x.
  unfold fr_head in RW.
  assert (SZ : cells_size ([CB 8 j0; C8 (Z_to_bv 64 0x103a4); C8 (Z_to_bv 64 buf); C8 (Z_to_bv 64 (body + 1))] ++
    CB 312 jj :: saved) = 448%nat) by (cbn [app cells_size csize]; rewrite SV; reflexivity).
  pose proof (rw_cells_transport rsegs [(Sp - 160, Sp)] m' m'' Sp _ RW MU2 WM2
    ltac:(cbn [disjoint_from]; rewrite SZ; split; [lia | exact I])) as RW2.
  pose proof (rw_cells_merge rsegs m'' Sp [] [CB 8 j0; C8 (Z_to_bv 64 0x103a4)]
     (C8 (Z_to_bv 64 buf) :: C8 (Z_to_bv 64 (body + 1)) :: CB 312 jj :: saved) RW2) as RW3.
  cbn [app] in RW3.
  pose proof (rw_cells_merge rsegs m'' Sp [CB (cells_size [CB 8 j0; C8 (Z_to_bv 64 0x103a4)])
       (cells_bytes [CB 8 j0; C8 (Z_to_bv 64 0x103a4)]); C8 (Z_to_bv 64 buf)]
     [C8 (Z_to_bv 64 (body + 1)); CB 312 jj] saved RW3) as RW4.
  cbn [app cells_size csize Nat.add] in RW4.
  do 4 eexists. split; [reflexivity|].
  split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
  split.
  { apply (munch_trans _ ms0 m0 m'' MU0).
    apply (munch_trans _ m0 m' m'' (munch_weaken _ _ m0 m' (mid_fp_loop lo Sp buf nb) MU)).
    exact (munch_weaken _ _ m' m'' (mid_fp_ref lo Sp buf nb L1) MU2). }
  split; [exact (wmono_trans rsegs ms0 m0 m'' WM0 (wmono_trans rsegs m0 m' m'' WM WM2))|].
  split; [exact MI2|]. split; [exact ST2|].
  exact RW4.
Qed.

Lemma mid_fp_mono : forall lo Sp buf nb, sub_fp [(lo, Sp + 448); (buf, buf + nb)] [(lo, Sp + 448); (buf, buf + nb)].
Proof. intros lo Sp buf nb x Hx. exact Hx. Qed.

(* the run from malloc's return to check_refusal's return: the set-up, the cursor loop, the decoder set-up, the
   decoder loop and check_refusal *)
Lemma mid_evt :
  memset_contract -> memcpy_contract -> diginet_cursor_init_contract -> diginet_msg_next_contract ->
  diginet_personality_of_contract -> diginet_decoder_init_contract -> diginet_decoder_next_contract ->
  check_cursor_step_contract -> check_cursor_message_contract -> check_events_step_contract ->
  check_events_fields_contract -> check_refusal_contract ->
  cstep_stmt -> dstep_stmt -> dsysex_stmt -> dchan_stmt ->
  setup_stmt -> cloop_stmt -> dsetup_stmt -> dloop_stmt ->
  forall (x1 x3 x4 x5 x6 x7 x9 x11 x12 x13 x14 x15 x16 x17 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
    (Sp lo p buf : Z) (pl junk j : list byte) (saved : list cell),
  0 <= Sp -> Sp + 448 <= 2 ^ 63 -> 0 <= lo -> lo + 160 <= Sp ->
  1 <= Z.of_nat (length pl) < 2 ^ 26 -> cells_size saved = 104%nat ->
  4096 <= buf -> buf + dup_size (Z.of_nat (length pl) - 1) <= lo ->
  0 <= p -> p + Z.of_nat (length pl) <= lo ->
  buf + dup_size (Z.of_nat (length pl) - 1) <= p \/ p + Z.of_nat (length pl) <= buf ->
  bytes_at rsegs m p pl ->
  rw_cells rsegs m buf [CB (Z.to_nat (dup_size (Z.of_nat (length pl) - 1))) junk] ->
  rw_cells rsegs m Sp (CB 344 j :: saved) ->
  mem_inv rsegs m -> stk rsegs m lo Sp ->
  evt rsegs (q_x F fc x3 x4 m Sp lo buf (dup_size (Z.of_nat (length pl) - 1)) saved)
    (MS (mkR x1 (Z_to_bv 64 Sp) x3 x4 x5 x6 x7 (Z_to_bv 64 (Z.of_nat (length pl))) x9 (Z_to_bv 64 buf)
           x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 (Z.of_nat (length pl) - 1)) (Z_to_bv 64 p)
           (sxb (nth 0 pl (Z_to_bv 8 0))) x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
        F (Z_to_bv 64 0x12d38) fc None m (seg_rom rsegs)).
Proof.
  intros MSET MCPY CIN MNX POF DIN DNX CCS CCM CES CEF CRF CST DST DSY DCH SET CLP DSE DLP.
  intros x1 x3 x4 x5 x6 x7 x9 x11 x12 x13 x14 x15 x16 x17 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31
    F fc m Sp lo p buf pl junk j saved H0 H1 H2 H3 H4 SV H6 H7 H8 H9 H10 BP RB RF MI ST.
  set (nb := dup_size (Z.of_nat (length pl) - 1)).
  apply (SET MCPY CIN x1 x3 x4 x5 x6 x7 x9 x11 x12 x13 x14 x15 x16 x17 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31
    F fc m Sp lo p buf pl junk j saved (q_x F fc x3 x4 m Sp lo buf nb saved)
    H0 H1 H2 H3 H4 SV H6 H7 H8 H9 H10 BP RB RF MI ST).
  (* the cursor loop's head after 0 passes *)
  intros body bb j0 mj jA cpad r1 r5 r6 r7 r9 r10 r11 r12 r13 r14 r15 r16 r17 r20 r26 r28 r29 r30 r31 m1
    SO LO Hb1 Hb2 MU1 WM1 MI1 ST1 BA1 RW1.
  apply (CLP MSET MNX CCS CCM CST x3 x4 F fc m1 Sp lo body bb j0 (sxb (nth 0 pl (Z_to_bv 8 0))) (Z_to_bv 64 buf)
    saved (q_x F fc x3 x4 m Sp lo buf nb saved) SO LO SV) with (k := 0) (pos := 0) (status := 0)
    (mj := mj) (jA := jA) (cpad := cpad);
    [ | lia | lia | left; reflexivity | apply munch_refl | apply wmono_refl | exact MI1 | exact ST1 | exact BA1
    | exact RW1 ].
  (* the cursor loop's exit *)
  intros q1 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 q16 q17 q19 q20 q22 q23 q24 q25 q26 q27 q28 q29 q30 q31 m2 jj
    MU2 WM2 MI2 ST2 BA2 RW2.
  apply (DSE POF DIN q1 x3 x4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 q16 q17 q19 q20 q22 q23 q24 q25 q26 q27
    q28 q29 q30 q31 F fc m2 Sp lo body bb j0 jj (nth 0 pl (Z_to_bv 8 0)) (Z_to_bv 64 buf) saved
    (q_x F fc x3 x4 m Sp lo buf nb saved) SO LO SV MI2 ST2 BA2 RW2).
  (* the decoder loop's head after 0 passes *)
  intros pp oj jE jM cpad2 jC s1' s5 s6 s7 s9 s10 s11 s12 s13 s14 s15 s16 s17 s20 s25 s28 s29 s30 s31 m3
    MU3 WM3 MI3 ST3 BA3 RW3.
  apply (DLP MSET MCPY DNX CES CEF DST DSY DCH x3 x4 F fc m3 Sp lo body bb j0 (Z_to_bv 64 buf) saved pp
    (q_x F fc x3 x4 m Sp lo buf nb saved) SO LO SV) with (k := 0) (pos := 0) (status := 0)
    (oj := oj) (jE := jE) (jM := jM) (cpad := cpad2) (jC := jC);
    [ | lia | lia | left; reflexivity | apply munch_refl | apply wmono_refl | exact MI3 | exact ST3 | exact BA3
    | exact RW3 ].
  (* the decoder loop's exit: check_refusal *)
  apply (mid_refusal CRF x3 x4 F fc m m3 Sp lo body buf nb bb j0 (Z_to_bv 64 buf) saved SO LO SV eq_refl).
  - apply (munch_trans _ m m1 m3 MU1).
    apply (munch_trans _ m1 m2 m3 (munch_weaken _ _ m1 m2 (mid_fp_loop lo Sp buf nb) MU2)).
    exact (munch_weaken _ _ m2 m3 (mid_fp_loop lo Sp buf nb) MU3).
  - exact (wmono_trans rsegs m m1 m3 WM1 (wmono_trans rsegs m1 m2 m3 WM2 WM3)).
Qed.
