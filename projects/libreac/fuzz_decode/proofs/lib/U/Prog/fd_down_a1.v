From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Lib Require Import Tac Bytes ZBridge.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.U Require Import Img0.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.U.Prog Require Import ReacDecodeLib reac_frame_inspect_c
  reac_frame_counter_c fd_down_q.
Import ListNotations.
Open Scope Z_scope.

Lemma ud_nth_repeat : forall (b d : byte) n i, (i < n)%nat -> nth i (repeat b n) d = b.
Proof. intros b d n. induction n as [|n IH]; intros i H; [lia|]. destruct i; [reflexivity|]. cbn. apply IH. lia. Qed.

Lemma ud_rd_fill : forall m out n i, bytes_at rsegs m out (repeat FILL (Z.to_nat n)) -> 0 <= i < n ->
  ov_read_bytes rsegs m (Z_to_bv 64 (out + i)) 1 = Some [FILL].
Proof.
  intros m out n i H Hi. rewrite (rd1 _ _ _ i H) by (rewrite repeat_length; lia).
  rewrite ud_nth_repeat by lia. reflexivity.
Qed.

Section Fill.
Variables (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x24 x25 x26 x27 x28
  x29 x30 x31 : word) (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (Q : machine_state -> Prop)
  (out n : Z).
Hypothesis HF : bytes_at rsegs m out (repeat FILL (Z.to_nat n)).
Hypothesis Hn : 1 <= n.
Hypothesis Hout : 0 <= out.
Hypothesis HoutN : out + n < 2^64.

Lemma ud_fill :
  (forall y11 y12 y13 y14 : word, evt rsegs Q (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 y11 y12 y13 y14 x15 x16 x17
     x18 x19 x20 x21 (Z_to_bv 64 out) (Z_to_bv 64 n) x24 x25 x26 x27 x28 x29 x30 x31)
     F (Z_to_bv 64 0x130ec) fc None m (seg_rom rsegs))) ->
  evt rsegs Q (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21
     (Z_to_bv 64 out) (Z_to_bv 64 n) x24 x25 x26 x27 x28 x29 x30 x31) F (Z_to_bv 64 0x130bc) fc None m (seg_rom rsegs)).
Proof.
  intros CONT.
  assert (L : forall (K : nat) (i : Z) (y12 y14 : word), Z.to_nat (n - i) = K -> 0 <= i < n ->
    bv_unsigned y12 = i ->
    evt rsegs Q (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 (Z_to_bv 64 0) y12 (Z_to_bv 64 (18446744073709551615 - out))
      y14 x15 x16 x17 x18 x19 x20 x21 (Z_to_bv 64 out) (Z_to_bv 64 n) x24 x25 x26 x27 x28 x29 x30 x31)
      F (Z_to_bv 64 0x130c8) fc None m (seg_rom rsegs))).
  { induction K as [K IH] using lt_wf_ind. intros i y12 y14 HK Hi H12. apply wv in H12. subst y12.
    pose proof (ud_rd_fill m out n i HF Hi) as HR. unfold FILL in HR.
    st. cnd false.
    st. st. st. st. st. st.
    replace (v_sltu (Z_to_bv 64 0) (Z_to_bv 64 (bv_unsigned (zxb (Z_to_bv 8 165)) + -165))) with (Z_to_bv 64 0)
      by (apply bv_eq; reflexivity).
    st. brq BR.
    - st. cnd false. apply CONT.
    - eapply (IH (Z.to_nat (n - (i + 1))) ltac:(lia) (i + 1)); [reflexivity | lia | rewrite unsigned_lit by lia; lia]. }
  st. st. st. rewrite zb_lxor_ones by lia.
  eapply (L (Z.to_nat (n - 0)) 0); [reflexivity | lia | rewrite ?unsigned_lit by lia; lia].
Qed.

End Fill.

Definition ud_wfz (len : Z) (bs : list byte) : Z := if inspect_wf len bs then 1 else 0.

Lemma ud_byte_range : forall b : byte, 0 <= bv_unsigned b < 256.
Proof. intros b. pose proof (bv_unsigned_in_range 8 b) as H. unfold bv_modulus in H. exact H. Qed.

Lemma ud_eqb_zxb : forall (b : byte) c, 0 <= c < 2^64 -> bv_eqb (zxb b) (Z_to_bv 64 c) = (bv_unsigned b =? c).
Proof.
  intros b c Hc. pose proof (ud_byte_range b) as Hb.
  unfold zxb, bv_eqb. rewrite !unsigned_lit by lia. reflexivity.
Qed.

Lemma ud_inspect_wf_spec : forall len bs, inspect_wf len bs = true <->
  len = 1492 /\ inspect_byte bs 12 = 0x88 /\ inspect_byte bs 13 = 0x19 /\
  inspect_byte bs 1490 = 0xC2 /\ inspect_byte bs 1491 = 0xEA.
Proof. intros. unfold inspect_wf. rewrite !andb_true_iff, !Z.eqb_eq. tauto. Qed.

Lemma ud_cnt_hi : forall c, 0 <= c < 2^16 ->
  Z_to_bv 64 (Z.shiftr (bv_unsigned (Z_to_bv 64 (bv_unsigned (Z_to_bv 64 (2^32 + c)) * 281474976710656))) 48) =
  Z_to_bv 64 c.
Proof.
  intros c Hc. rewrite (unsigned_lit (2^32 + c)) by lia.
  rewrite unsigned_lit_wrap. rewrite Z.shiftr_div_pow2 by lia. f_equal.
  replace ((2 ^ 32 + c) * 281474976710656) with (c * 2^48 + 2^16 * 2^64) by ring.
  rewrite Z.mod_add by lia. rewrite Z.mod_small by lia. apply Z.div_mul. lia.
Qed.

Lemma ud_cnt_lo : forall b14 b15 : byte,
  Z_to_bv 64 (Z.lor (bv_unsigned (Z_to_bv 64 (bv_unsigned (zxb b15) * 256))) (bv_unsigned (zxb b14))) =
  Z_to_bv 64 (bv_unsigned b14 + 256 * bv_unsigned b15).
Proof.
  intros b14 b15. pose proof (ud_byte_range b14). pose proof (ud_byte_range b15).
  unfold zxb. rewrite !(unsigned_lit (bv_unsigned _)) by lia.
  rewrite unsigned_lit by lia. f_equal. rewrite Z.lor_comm.
  rewrite <- (lor_shiftl8_add (bv_unsigned b14) (bv_unsigned b15)) by lia.
  rewrite Z.shiftl_mul_pow2 by lia. reflexivity.
Qed.

Section DA.
Context (IHC : reac_frame_counter_contract).
Variables (x3 x4 x20 x21 x26 x27 : word) (F : bvmap 5 word) (fc : bv 32) (Q : machine_state -> Prop)
  (Sp mode nch ns out frame len lo : Z) (fr : list byte).
Hypothesis HSp : 0 <= Sp < 2 ^ 63.
Hypothesis Hnch : -128 <= nch <= 127.
Hypothesis Hns : -128 <= ns <= 127.
Hypothesis HLEN : Z.of_nat (length fr) = len.
Hypothesis HLB : 0 <= len < 2 ^ 26.
Hypothesis HOP : 4096 <= out < 2 ^ 60.
Hypothesis HFP : 4096 <= frame < 2 ^ 60.
Hypothesis HMP : 0 <= mode < 2 ^ 60.
Hypothesis HMA : mode <> 0 /\ mode mod 4 = 0.
Hypothesis LO : lo + 4096 <= Sp.
Hypothesis DOF : out + fd_olen nch ns <= frame \/ frame + len <= out.
Hypothesis DOS : out + fd_olen nch ns <= lo.
Hypothesis DOM : out + fd_olen nch ns <= mode + 4 \/ mode + 12 <= out.
Hypothesis DFS : frame + len + 1500 <= lo.
Hypothesis DMS : mode + 12 <= lo \/ Sp + 56 <= mode + 4.

Local Abbreviation SU pc mm r1 r5 r6 r7 r8 r10 r11 r12 r13 r14 r15 r16 r17 r24 r28 r29 r30 r31 :=
  (MS (mkR r1 (Z_to_bv 64 Sp) x3 x4 r5 r6 r7 r8 (Z_to_bv 64 len) r10 r11 r12 r13 r14 r15 r16 r17
     (Z_to_bv 64 (fd_fits nch ns)) (Z_to_bv 64 mode) x20 x21 (Z_to_bv 64 out) (Z_to_bv 64 (fd_olen nch ns)) r24
     (Z_to_bv 64 frame) x26 x27 r28 r29 r30 r31) F (Z_to_bv 64 pc) fc None mm (seg_rom rsegs)).

Lemma ud_segW : forall (m : word -> option byte) (j : list byte)
    (r1 r5 r6 r7 r8 r12 r13 r14 r15 r16 r17 r24 r28 r29 r30 r31 : word),
  rw_cells rsegs m (Sp + 8) [C8 (Z_to_bv 64 len); C8 (Z_to_bv 64 frame); CB 16 j] -> bytes_at rsegs m frame fr ->
  (forall y11 y12 : word, evt rsegs Q (SU 0x13018 m r1 r5 r6 r7 r8 (Z_to_bv 64 (inspect_result len fr)) y11 y12
     r13 r14 r15 r16 r17 (Z_to_bv 64 (ud_wfz len fr)) r28 r29 r30 r31)) ->
  evt rsegs Q (SU 0x12f98 m r1 r5 r6 r7 r8 (Z_to_bv 64 (inspect_result len fr)) (Z_to_bv 64 1492) r12
     r13 r14 r15 r16 r17 r24 r28 r29 r30 r31).
Proof.
  intros m j r1 r5 r6 r7 r8 r12 r13 r14 r15 r16 r17 r24 r28 r29 r30 r31 HS HFR CONT. unfold ud_wfz in CONT.
  pose proof (bytes_at_bound _ _ _ _ HFR) as HFB. rewrite HLEN in HFB.
  st. brq B1.
  2:{ assert (WF : inspect_wf len fr = false) by (apply not_true_iff_false; rewrite ud_inspect_wf_spec; lia).
      rewrite WF in CONT. st. st. apply CONT. }
  st. cnd false. st. st. st. cnd false.
  pose proof (rd1 _ _ _ 12 HFR ltac:(lia)) as HR. change (Z.to_nat 12) with 12%nat in HR.
  st. st. st. st. rewrite ud_eqb_zxb by lia. brq B2.
  2:{ assert (WF : inspect_wf len fr = false)
        by (apply not_true_iff_false; rewrite ud_inspect_wf_spec; unfold inspect_byte; lia).
      rewrite WF in CONT. st. st. apply CONT. }
  clear HR. st. st. cnd false.
  pose proof (rd1 _ _ _ 13 HFR ltac:(lia)) as HR. change (Z.to_nat 13) with 13%nat in HR.
  st. st. st. st. rewrite ud_eqb_zxb by lia. brq B3.
  2:{ assert (WF : inspect_wf len fr = false)
        by (apply not_true_iff_false; rewrite ud_inspect_wf_spec; unfold inspect_byte; lia).
      rewrite WF in CONT. st. st. apply CONT. }
  clear HR. st. st. cnd false.
  pose proof (rd1 _ _ _ 1490 HFR ltac:(lia)) as HR. change (Z.to_nat 1490) with 1490%nat in HR.
  st. st. st. st. rewrite ud_eqb_zxb by lia. brq B4.
  2:{ assert (WF : inspect_wf len fr = false)
        by (apply not_true_iff_false; rewrite ud_inspect_wf_spec; unfold inspect_byte; lia).
      rewrite WF in CONT. st. st. apply CONT. }
  clear HR. st. st. cnd false.
  pose proof (rd1 _ _ _ 1491 HFR ltac:(lia)) as HR. change (Z.to_nat 1491) with 1491%nat in HR.
  st. st. st. st. st. st.
  pose proof (ud_byte_range (nth 1491 fr (Z_to_bv 8 0))) as BR5.
  destruct (Z.eqb_spec (bv_unsigned (nth 1491 fr (Z_to_bv 8 0))) 234) as [B5|B5].
  - assert (WF : inspect_wf len fr = true) by (rewrite ud_inspect_wf_spec; unfold inspect_byte; lia).
    rewrite WF in CONT.
    replace (v_sltiu (Z_to_bv 64 (bv_unsigned (zxb (nth 1491 fr (Z_to_bv 8 0))) + -234)) 1) with (Z_to_bv 64 1).
    { apply CONT. }
    unfold v_sltiu, zxb. rewrite (unsigned_lit (bv_unsigned _)) by lia. rewrite B5. reflexivity.
  - assert (WF : inspect_wf len fr = false)
      by (apply not_true_iff_false; rewrite ud_inspect_wf_spec; unfold inspect_byte; lia).
    rewrite WF in CONT.
    replace (v_sltiu (Z_to_bv 64 (bv_unsigned (zxb (nth 1491 fr (Z_to_bv 8 0))) + -234)) 1) with (Z_to_bv 64 0).
    { apply CONT. }
    unfold v_sltiu, zxb. rewrite (unsigned_lit (bv_unsigned _)) by lia. rewrite unsigned_lit_wrap.
    change (bv_wrap 64 1) with 1.
    destruct (Z.ltb_spec ((bv_unsigned (nth 1491 fr (Z_to_bv 8 0)) + -234) mod 2 ^ 64) 1); [|reflexivity].
    exfalso. Z.div_mod_to_equations. lia.
Qed.

Lemma ud_segC : forall (m : word -> option byte) (j : list byte)
    (r1 r5 r6 r7 r8 r11 r12 r13 r14 r15 r16 r17 r28 r29 r30 r31 : word),
  rw_cells rsegs m (Sp + 8) [C8 (Z_to_bv 64 len); C8 (Z_to_bv 64 frame); CB 16 j] -> bytes_at rsegs m frame fr ->
  (forall y1 y8 y10 y11 y12 : word, evt rsegs Q (SU 0x13070 m y1 r5 r6 r7 y8 y10 y11 y12
     r13 r14 r15 r16 r17 (Z_to_bv 64 (ud_wfz len fr)) r28 r29 r30 r31)) ->
  evt rsegs Q (SU 0x13018 m r1 r5 r6 r7 r8 (Z_to_bv 64 (inspect_result len fr)) r11 r12
     r13 r14 r15 r16 r17 (Z_to_bv 64 (ud_wfz len fr)) r28 r29 r30 r31).
Proof.
  intros m j r1 r5 r6 r7 r8 r11 r12 r13 r14 r15 r16 r17 r28 r29 r30 r31 HS HFR CONT.
  pose proof (bytes_at_bound _ _ _ _ HFR) as HFB. rewrite HLEN in HFB.
  st. rewrite inspect_valid_bit. unfold ud_wfz in CONT |- *.
  st. rewrite bv_eqb_refl. cbn [negb].
  st. destruct (inspect_wf len fr) eqn:WF.
  - brq B1; [lia|].
    pose proof WF as WF0. apply ud_inspect_wf_spec in WF. destruct WF as (W0 & W1 & W2 & W3 & W4).
    st. cnd false. st. st. st. cnd false. st. st. st. cnd false.
    pose proof (rd1 _ _ _ 15 HFR ltac:(lia)) as HR15. change (Z.to_nat 15) with 15%nat in HR15.
    pose proof (rd1 _ _ _ 14 HFR ltac:(lia)) as HR14. change (Z.to_nat 14) with 14%nat in HR14.
    st. st. st. st. st. st. st. st.
    unfold inspect_result. rewrite WF0. rewrite ud_cnt_hi by apply inspect_counter_range. rewrite ud_cnt_lo.
    change (inspect_counter fr) with (bv_unsigned (nth 14 fr (Z_to_bv 8 0)) + 256 * bv_unsigned (nth 15 fr (Z_to_bv 8 0))).
    st. rewrite bv_eqb_refl. cbn [negb].
    st. st.
    eapply evt_cut; [eapply IHC with (bs := fr) |].
    { rewrite unsigned_lit by lia. lia. }
    { lia. }
    { rewrite unsigned_lit by lia. exact HFR. }
    intros ms' (a1' & ->).
    replace (ret_pc (Z_to_bv 64 0x1306c)) with (Z_to_bv 64 0x1306c) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
    change (counter_result fr) with (bv_unsigned (nth 14 fr (Z_to_bv 8 0)) + 256 * bv_unsigned (nth 15 fr (Z_to_bv 8 0))).
    st. rewrite bv_eqb_refl. cbn [negb].
    apply CONT.
  - brq B1; [apply CONT | lia].
Qed.

End DA.
