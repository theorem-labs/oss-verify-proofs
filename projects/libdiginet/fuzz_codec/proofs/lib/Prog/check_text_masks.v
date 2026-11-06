From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame Tac Bytes ZBridge.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib Require Import Img0.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Spec Require Import DgnSpec DgnLib.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Prog Require Import codec_owe codec_cells codec_chk
  check_text_masks_bits diginet_meter_mask_c diginet_meter_segments_c diginet_ring_dot_c diginet_ring_fill_c
  check_text_masks_c.
Import ListNotations.
Open Scope Z_scope.

(** check_text_masks of the plain image (0x15000, 52 instructions, frame 0x30). The prologue saves ra and
    s0-s3, keeps n in s0, the mask in s1 and lit = min(n, 14) in s3 (the [bltu a0, 14] clamp, both arms
    join at 0x15030), then calls diginet_meter_mask, diginet_meter_segments, diginet_ring_dot and
    diginet_ring_fill in turn, each followed by a comparison whose failing arm jumps to the abort call at
    0x150cc. The inlined spec_segments loop (0x15058-0x1506c) is the fuel lemma ctm_loop. Every
    comparison holds under the contract's four agreement premises (check_text_masks_bits), so 0x150cc is
    never reached; the epilogue restores the saved registers from the frame. *)

(** The spec_segments loop: at 0x15058 with a1 = j, a2 = 15, s1 = mask, s2 = -1 and S k iterations left,
    it reaches 0x15070 with a1 = spec_seg_go mask j (S k). *)
Lemma ctm_loop : forall (k j : nat) (ra sp gp tp t0 t1 t2 s0 a0 a3 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11
                        t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (mask : Z),
  (j + S k = 15)%nat -> 0 <= mask < 2 ^ 16 ->
  evt rsegs
    (fun ms' => exists a3' : word,
       ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 mask) a0 (Z_to_bv 64 (spec_seg_go mask j (S k)))
                     (Z_to_bv 64 15) a3' a4 a5 a6 a7 (Z_to_bv 64 (-1)) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                F (Z_to_bv 64 0x15070) fc None m (seg_rom rsegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 mask) a0 (Z_to_bv 64 (Z.of_nat j))
             (Z_to_bv 64 15) a3 a4 a5 a6 a7 (Z_to_bv 64 (-1)) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x15058) fc None m (seg_rom rsegs)).
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
Hypothesis LO : lo + 48 <= bv_unsigned sp.

(** The contract's post with the frame interval written as the walk carries it. *)
Definition Qm (ms' : machine_state) : Prop :=
  exists (a0' a1' a2' a3' : word) (m' : word -> option byte),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0' a1' a2' a3' a4 a5 a6 a7
                  s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom rsegs) /\
    munch [(bv_unsigned sp + -48, bv_unsigned sp)] m m' /\
    wmono rsegs m m' /\
    mem_inv rsegs m' /\
    stk rsegs m' lo (bv_unsigned sp).

(** From the join of the clamp (0x15030, s3 = min(n, 14)) to the return. *)
Lemma ctm_tail : forall (s3x : word) (jk : list byte) (m0 : word -> option byte),
  bv_unsigned s3x = Z.min n 14 ->
  rw_cells rsegs m0 (bv_unsigned sp + -48) [CB 8 jk; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
  stk rsegs m0 lo (bv_unsigned sp + -48) ->
  munch [(bv_unsigned sp + -48, bv_unsigned sp)] m m0 -> wmono rsegs m m0 -> mem_inv rsegs m0 ->
  evt rsegs Qm
    (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 a0 (Z_to_bv 64 mask) a0 (Z_to_bv 64 14) a2 a3
             a4 a5 a6 a7 s2 s3x s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x15030) fc None m0 (seg_rom rsegs)).
Proof.
  intros s3x jk m0 Hs3 FR ST MU WM HMI.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. unfold bv_modulus in Rsp.
  pose proof (proj1 HA0) as Hn.
  unfold diginet_meter_mask_contract, DIGINET_METER_MASK, diginet_meter_mask_pre in MM.
  unfold diginet_meter_segments_contract, DIGINET_METER_SEGMENTS, diginet_meter_segments_pre in MSG.
  unfold diginet_ring_dot_contract, DIGINET_RING_DOT, diginet_ring_dot_pre in RD.
  unfold diginet_ring_fill_contract, DIGINET_RING_FILL, diginet_ring_fill_pre in RF.
  (* mv a0, s0; jal diginet_meter_mask *)
  zstep. zstep.
  eapply evt_cut; [ eapply MM with (n := n); exact HA0 | ].
  intros ms' [a1y ->].
  replace (ret_pc (Z_to_bv 64 86072)) with (Z_to_bv 64 86072) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]).
  (* addi s2, zero, -1; sllw a1, s2, s3; xor a0, a1, a0; bne a0, s2 *)
  zstep. zstep. zstep. zstep.
  if_cases K1.
  { exfalso. rewrite E1, (ctm_mm_ok n s3x) in K1 by lia. discriminate K1. }
  (* mv a0, s1; jal diginet_meter_segments *)
  zstep. zstep.
  eapply evt_cut; [ eapply MSG with (mask := mask); split; [ exact HM | reflexivity ] | ].
  intros ms' [a1z [a2z ->]].
  replace (ret_pc (Z_to_bv 64 86096)) with (Z_to_bv 64 86096) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]).
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
  replace (ret_pc (Z_to_bv 64 86140)) with (Z_to_bv 64 86140) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]).
  (* sltiu a1, s0, 15; addi a2, zero, 1; sllw s1, a2, s0; neg a1, a1; and a1, a1, s1; bne a1, a0 *)
  zstep. zstep. zstep. zstep. zstep. zstep.
  if_cases K3.
  { exfalso. rewrite E3, (ctm_rd_ok n a0 Hn (proj2 HA0)) in K3. discriminate K3. }
  (* mv a0, s0; jal diginet_ring_fill *)
  zstep. zstep.
  eapply evt_cut; [ eapply RF with (n := n); exact HA0 | ].
  intros ms' [a1v [a2v ->]].
  replace (ret_pc (Z_to_bv 64 86172)) with (Z_to_bv 64 86172) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]).
  (* sltiu a1, s0, 16; addiw s1, s1, -1; neg a1, a1; and a1, a1, s1; bne a1, a0 *)
  zstep. zstep. zstep. zstep. zstep.
  if_cases K4.
  { exfalso. rewrite E4, (ctm_rf_ok_p n a0 Hn (proj2 HA0)) in K4. discriminate K4. }
  (* the epilogue: ld ra, s0-s3; addi sp, sp, 0x30; ret *)
  zstep. zstep. zstep. zstep. zstep. zstep.
  eapply stk_release in FR; [ | exact ST | lia ].
  cbn [cells_size csize Nat.add] in FR.
  replace (bv_unsigned sp + -48 + Z.of_nat 48) with (bv_unsigned sp) in FR by lia.
  clear ST.
  zstep.
  finish.
Qed.

(** From the entry: carve the frame, store ra and s0-s3, take either arm of the clamp. *)
Lemma ctm_entry : mem_inv rsegs m -> stk rsegs m lo (bv_unsigned sp) ->
  evt rsegs Qm
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 (Z_to_bv 64 mask) a2 a3 a4 a5 a6 a7
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x15000) fc None m (seg_rom rsegs)).
Proof.
  intros HMI ST.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. unfold bv_modulus in Rsp.
  carve_frame 48%nat ST.
  assert (MU : munch [(bv_unsigned sp + -48, bv_unsigned sp)] m m) by apply munch_refl.
  assert (WM : wmono rsegs m m) by apply wmono_refl.
  (* addi sp; sd ra, s0-s3; mv s1, a1; addi a1, zero, 14; mv s0, a0; mv s3, a0; bltu a0, a1 *)
  do 11 zstep.
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
  replace (bv_unsigned sp - 48) with (bv_unsigned sp + -48) by lia.
  exact (conj Heq (conj MU (conj WM (conj MI STs)))).
Qed.
