From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame Tac Bytes ZBridge.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.U Require Import Img0.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Spec Require Import DgnSpec DgnLib.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Prog Require Import codec_owe codec_chk check_text_masks_bits.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.U.Prog Require Import codec_cells
  diginet_meter_mask_c diginet_meter_segments_c diginet_ring_dot_c diginet_ring_fill_c check_text_masks_c.
Import ListNotations.
Open Scope Z_scope.

(** check_text_masks of the ubsan image (0x152c8, 52 instructions, frame 0x20). The prologue saves ra and
    s0-s2 and keeps n in s0 and the mask in s1; diginet_meter_mask is called first, then the clamp
    [bltu s0, 14] puts lit = min(n, 14) in a1 (both arms join at 0x152f8). The four comparisons, the
    inlined spec_segments loop (0x15318-0x1532c, the fuel lemma ctm_loop) and the epilogue are as in the
    plain image; ring_fill's comparison is [(-(s0 <u 16)) and not(sllw -1, s0)]. Every comparison holds
    under the contract's four agreement premises (check_text_masks_bits), so the abort call at 0x15390 is
    never reached. The function has no UBSan check: every shift is masked by the [sltiu] selects, and the
    [unimp] at 0x15394 follows the abort call. *)

(** The spec_segments loop: at 0x15318 with a1 = j, a2 = 15, s1 = mask, s2 = -1 and S k iterations left,
    it reaches 0x15330 with a1 = spec_seg_go mask j (S k). *)
Lemma ctm_loop : forall (k j : nat) (ra sp gp tp t0 t1 t2 s0 a0 a3 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11
                        t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (mask : Z),
  (j + S k = 15)%nat -> 0 <= mask < 2 ^ 16 ->
  evt rsegs
    (fun ms' => exists a3' : word,
       ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 mask) a0 (Z_to_bv 64 (spec_seg_go mask j (S k)))
                     (Z_to_bv 64 15) a3' a4 a5 a6 a7 (Z_to_bv 64 (-1)) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                F (Z_to_bv 64 0x15330) fc None m (seg_rom rsegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 mask) a0 (Z_to_bv 64 (Z.of_nat j))
             (Z_to_bv 64 15) a3 a4 a5 a6 a7 (Z_to_bv 64 (-1)) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x15318) fc None m (seg_rom rsegs)).
Proof.
  induction k as [|k IH]; intros j ra sp gp tp t0 t1 t2 s0 a0 a3 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11
    t3 t4 t5 t6 F fc m mask Hj Hm.
  - (* j = 14: the last test, then a1 = -1 *)
    assert (Rj : Z.of_nat j = 14) by lia.
    change (spec_seg_go mask j 1) with (if mask =? 2 ^ Z.of_nat j - 1 then Z.of_nat j else spec_seg_go mask (S j) 0).
    zstep. zstep. zstep.
    rewrite (ctm_seg_test (Z.of_nat j) mask) by lia.
    if_cases K.
    + apply evt_done. eexists. reflexivity.
    + zstep. zstep.
      rewrite (ctm_cnt (Z.of_nat j)) by lia. rewrite chk_s64_eqb by lia.
      if_cases K2.
      * exfalso. apply Bool.negb_true_iff, Z.eqb_neq in K2. lia.
      * zstep. apply evt_done. eexists. reflexivity.
  - (* j < 14: the test at j, then the next index *)
    assert (Rj : Z.of_nat j < 14) by lia.
    change (spec_seg_go mask j (S (S k)))
      with (if mask =? 2 ^ Z.of_nat j - 1 then Z.of_nat j else spec_seg_go mask (S j) (S k)).
    zstep. zstep. zstep.
    rewrite (ctm_seg_test (Z.of_nat j) mask) by lia.
    if_cases K.
    + apply evt_done. eexists. reflexivity.
    + zstep. zstep.
      rewrite (ctm_cnt (Z.of_nat j)) by lia. rewrite chk_s64_eqb by lia.
      if_cases K2.
      * replace (Z.of_nat j + 1) with (Z.of_nat (S j)) by lia.
        eapply evt_mono; [ apply (IH (S j)); [ lia | exact Hm ] | ].
        intros ms' [a3' ->]. exists a3'. reflexivity.
      * exfalso. apply Bool.negb_false_iff, Z.eqb_eq in K2. lia.
Qed.

Section CheckTextMasks.
Variables (ra sp gp tp t0 t1 t2 s0 s1 a0 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
          (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo n mask : Z).
Hypothesis HA0 : arg_u32 a0 n.
Hypothesis HM : 0 <= mask < 2 ^ 16.
Hypothesis E1 : meter_mask_spec n = owed_meter_mask n.
Hypothesis E2 : meter_segments_spec mask = spec_segments_spec mask.
Hypothesis E3 : ring_dot_spec n = owed_ring_dot n.
Hypothesis E4 : ring_fill_spec n = owed_ring_fill n.
Hypothesis MM : diginet_meter_mask_contract.
Hypothesis MSG : diginet_meter_segments_contract.
Hypothesis RD : diginet_ring_dot_contract.
Hypothesis RF : diginet_ring_fill_contract.
Hypothesis LO : lo + 32 <= bv_unsigned sp.

(** The contract's post with the frame interval written as the walk carries it. *)
Definition Qm (ms' : machine_state) : Prop :=
  exists (a0' a1' a2' a3' : word) (m' : word -> option byte),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0' a1' a2' a3' a4 a5 a6 a7
                  s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom rsegs) /\
    munch [(bv_unsigned sp + -32, bv_unsigned sp)] m m' /\
    wmono rsegs m m' /\
    mem_inv rsegs m' /\
    stk rsegs m' lo (bv_unsigned sp).

(** From the join of the clamp (0x152f8, a1 = min(n, 14)) to the return. *)
Lemma ctm_tail : forall (a1x : word) (m0 : word -> option byte),
  bv_unsigned a1x = Z.min n 14 ->
  rw_cells rsegs m0 (bv_unsigned sp + -32) [C8 s2; C8 s1; C8 s0; C8 ra] ->
  stk rsegs m0 lo (bv_unsigned sp + -32) ->
  munch [(bv_unsigned sp + -32, bv_unsigned sp)] m m0 -> wmono rsegs m m0 -> mem_inv rsegs m0 ->
  evt rsegs Qm
    (MS (mkR (Z_to_bv 64 86760) (Z_to_bv 64 (bv_unsigned sp + -32)) gp tp t0 t1 t2 a0 (Z_to_bv 64 mask)
             (Z_to_bv 64 (meter_mask_spec n)) a1x (Z_to_bv 64 14) a3
             a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x152f8) fc None m0 (seg_rom rsegs)).
Proof.
  intros a1x m0 Ha1 FR ST MU WM HMI.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. unfold bv_modulus in Rsp.
  pose proof (proj1 HA0) as Hn.
  unfold diginet_meter_segments_contract, DIGINET_METER_SEGMENTS, diginet_meter_segments_pre in MSG.
  unfold diginet_ring_dot_contract, DIGINET_RING_DOT, diginet_ring_dot_pre in RD.
  unfold diginet_ring_fill_contract, DIGINET_RING_FILL, diginet_ring_fill_pre in RF.
  (* addi s2, zero, -1; sllw a1, s2, a1; xor a0, a1, a0; bne a0, s2 *)
  zstep. zstep. zstep. zstep.
  if_cases K1.
  { exfalso. rewrite E1, (ctm_mm_ok n a1x) in K1 by lia. discriminate K1. }
  (* mv a0, s1; jal diginet_meter_segments *)
  zstep. zstep.
  eapply evt_cut; [ eapply MSG with (mask := mask); split; [ exact HM | reflexivity ] | ].
  intros ms' [a1z [a2z ->]].
  replace (ret_pc (Z_to_bv 64 86800)) with (Z_to_bv 64 86800) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]).
  (* mv a1, zero; addi a2, zero, 15; the spec_segments loop; bne a0, a1 *)
  zstep. zstep.
  eapply evt_cut; [ apply (ctm_loop 14 0); [ lia | exact HM ] | ].
  intros ms' [a3z ->].
  zstep.
  if_cases K2.
  { exfalso. rewrite E2 in K2. change (spec_seg_go mask 0 15) with (spec_segments_spec mask) in K2.
    rewrite bv_eqb_refl in K2. discriminate K2. }
  (* mv a0, s0; jal diginet_ring_dot *)
  zstep. zstep.
  eapply evt_cut; [ eapply RD with (n := n); exact HA0 | ].
  intros ms' [a1w [a2w ->]].
  replace (ret_pc (Z_to_bv 64 86844)) with (Z_to_bv 64 86844) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]).
  (* sltiu a1, s0, 15; addi a2, zero, 1; sllw a2, a2, s0; neg a1, a1; and a1, a1, a2; bne a1, a0 *)
  zstep. zstep. zstep. zstep. zstep. zstep.
  if_cases K3.
  { exfalso. rewrite E3, (ctm_rd_ok n a0 Hn (proj2 HA0)) in K3. discriminate K3. }
  (* mv a0, s0; jal diginet_ring_fill *)
  zstep. zstep.
  eapply evt_cut; [ eapply RF with (n := n); exact HA0 | ].
  intros ms' [a1v [a2v ->]].
  replace (ret_pc (Z_to_bv 64 86876)) with (Z_to_bv 64 86876) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]).
  (* sltiu a1, s0, 16; addi a2, zero, -1; sllw a2, a2, s0; not a2, a2; neg a1, a1; and a1, a1, a2; bne a1, a0 *)
  zstep. zstep. zstep. zstep. zstep. zstep. zstep.
  if_cases K4.
  { exfalso. rewrite E4, (ctm_rf_ok_u n a0 Hn (proj2 HA0)) in K4. discriminate K4. }
  (* the epilogue: ld ra, s0-s2; addi sp, sp, 0x20; ret *)
  zstep. zstep. zstep. zstep. zstep.
  eapply stk_release in FR; [ | exact ST | lia ].
  cbn [cells_size csize Nat.add] in FR.
  replace (bv_unsigned sp + -32 + Z.of_nat 32) with (bv_unsigned sp) in FR by lia.
  clear ST.
  zstep.
  finish.
Qed.

(** From the entry: carve the frame, store ra and s0-s2, call diginet_meter_mask, take either arm of the
    clamp. *)
Lemma ctm_entry : mem_inv rsegs m -> stk rsegs m lo (bv_unsigned sp) ->
  evt rsegs Qm
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 (Z_to_bv 64 mask) a2 a3 a4 a5 a6 a7
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x152c8) fc None m (seg_rom rsegs)).
Proof.
  intros HMI ST.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. unfold bv_modulus in Rsp.
  unfold diginet_meter_mask_contract, DIGINET_METER_MASK, diginet_meter_mask_pre in MM.
  carve_frame 32%nat ST.
  assert (MU : munch [(bv_unsigned sp + -32, bv_unsigned sp)] m m) by apply munch_refl.
  assert (WM : wmono rsegs m m) by apply wmono_refl.
  (* addi sp; sd ra, s0-s2; mv s1, a1; mv s0, a0; jal diginet_meter_mask *)
  do 8 zstep.
  eapply evt_cut; [ eapply MM with (n := n); exact HA0 | ].
  intros ms' [a1y ->].
  replace (ret_pc (Z_to_bv 64 86760)) with (Z_to_bv 64 86760) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]).
  (* addi a2, zero, 14; mv a1, s0; bltu s0, a2 *)
  zstep. zstep. zstep.
  if_cases K1.
  - eapply ctm_tail; [ apply (ctm_lit_lt n a0 (proj1 HA0) (proj2 HA0) K1) | eassumption .. ].
  - pose proof (ctm_lit_ge n a0 (proj1 HA0) (proj2 HA0) K1) as H14.
    zstep.
    eapply ctm_tail; [ rewrite unsigned_lit by lia; lia | eassumption .. ].
Qed.

End CheckTextMasks.

Theorem check_text_masks_holds :
  diginet_meter_mask_contract -> diginet_meter_segments_contract ->
  diginet_ring_dot_contract -> diginet_ring_fill_contract ->
  check_text_masks_contract.
Proof.
  intros MM MSG RD RF. unfold check_text_masks_contract, CHECK_TEXT_MASKS.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
         F fc m lo n mask [HA0 [[HM HA1] [HMI [ST [LO [E1 [E2 [E3 E4]]]]]]]].
  subst a1. unfold CHECK_TEXT_MASKS_DEPTH in LO |- *.
  eapply evt_mono; [ eapply ctm_entry; eassumption | ].
  intros ms' (a0' & a1' & a2' & a3' & m' & Heq & MU & WM & MI & STs).
  exists a0', a1', a2', a3', m'.
  replace (bv_unsigned sp - 32) with (bv_unsigned sp + -32) by lia.
  exact (conj Heq (conj MU (conj WM (conj MI STs)))).
Qed.
