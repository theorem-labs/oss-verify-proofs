From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Lib Require Import Tac Bytes.
From OSSVerify.Proofs.libreac.fuzz_decode.lib Require Import Img0.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Prog Require Import ReacDecodeLib SlotLoops SlotDown
  reac_frame_inspect_c reac_decode_c reac_decode check_braid_c.
Import ListNotations.
Open Scope Z_scope.

Lemma even_mod2 : forall ch, Z.even ch = (ch mod 2 =? 0).
Proof.
  intros ch. destruct (Z.Even_or_Odd ch) as [[q E]|[q E]].
  - rewrite (proj2 (Z.even_spec ch)) by (exists q; exact E). symmetry. apply Z.eqb_eq. subst. Z.div_mod_to_equations. lia.
  - assert (Z.even ch = false) by (rewrite <- Z.negb_odd; rewrite (proj2 (Z.odd_spec ch)) by (exists q; exact E); reflexivity).
    rewrite H. symmetry. apply Z.eqb_neq. subst. Z.div_mod_to_equations. lia.
Qed.

Lemma braid_pos_off : forall s ch nch j, 0 <= ch -> 0 <= j < 3 ->
  braid_pos s ch nch j = 3 * (s * nch + 2 * (ch / 2)) + braid_off ch j.
Proof.
  intros s ch nch j Hch Hj. unfold braid_pos, braid_off. rewrite even_mod2.
  assert (D : ch - ch mod 2 = 2 * (ch / 2)) by (Z.div_mod_to_equations; lia).
  rewrite D. destruct (ch mod 2 =? 0); destruct (Z.eqb_spec j 0); destruct (Z.eqb_spec j 1); lia.
Qed.

Lemma braid_map_of : forall m out frame fr nch ns,
  bytes_at rsegs m out (braid_out fr nch ns) -> bytes_at rsegs m frame fr -> length fr = 1492%nat ->
  0 < nch -> nch mod 2 = 0 -> 0 < ns -> nch * ns <= 480 ->
  braid_map m (frame + 50) out nch ns.
Proof.
  intros m out frame fr nch ns HB HF HL Hnch Hev Hns H480 ch s j Hch Hs Hj.
  exists (nth (Z.to_nat (50 + braid_pos s ch nch j)) fr (Z_to_bv 8 0)).
  pose proof (Z.mod_pos_bound ch 2 ltac:(lia)) as Hm.
  assert (ch - ch mod 2 <= nch - 2) by (Z.div_mod_to_equations; lia).
  assert (s * nch <= (ns - 1) * nch) by nia.
  assert (ch * ns <= (nch - 1) * ns) by nia.
  assert (BP : 0 <= braid_pos s ch nch j <= 3 * nch * ns - 1).
  { rewrite braid_pos_lin by lia. destruct (Z.eqb_spec j 0); destruct (Z.eqb_spec j 1); nia. }
  pose proof (bytes_at_bound _ _ _ _ HB) as BB. unfold braid_out in BB. rewrite length_mapseq, Z2Nat.id in BB by nia.
  split.
  - destruct HB as (_ & _ & HB3).
    replace (out + 3 * (ch * ns + s) + j) with (out + Z.of_nat (Z.to_nat (3 * (ch * ns + s) + j))) by nia.
    unfold mrd in *. rewrite HB3 by (unfold braid_out; rewrite length_mapseq; nia).
    unfold braid_out. rewrite nth_error_mapseq by nia. cbn [Nat.add].
    rewrite Z2Nat.id by nia. rewrite braid_byte_at by lia. reflexivity.
  - destruct HF as (_ & _ & HF3).
    replace (frame + 50 + 3 * (s * nch + 2 * (ch / 2)) + braid_off ch j)
      with (frame + Z.of_nat (Z.to_nat (50 + braid_pos s ch nch j))) by (rewrite Z2Nat.id by lia; rewrite braid_pos_off by lia; lia).
    rewrite HF3 by lia. apply nth_error_nth'. lia.
Qed.

Section DTB.
Context (ICB : check_braid_contract).
Variables (x3 x4 x8 x9 x18 x21 x22 x23 x24 x25 x27 sp : word) (F : bvmap 5 word) (fc : bv 32)
  (m : word -> option byte) (Q : machine_state -> Prop) (nch ns out frame lo : Z) (fr : list byte).
Hypothesis Hnch : 0 < nch <= 127.
Hypothesis Hev : nch mod 2 = 0.
Hypothesis Hns : 0 < ns <= 127.
Hypothesis H480 : nch * ns <= 480.
Hypothesis HL : length fr = 1492%nat.
Hypothesis HB : bytes_at rsegs m out (braid_out fr nch ns).
Hypothesis HFR : bytes_at rsegs m frame fr.
Hypothesis HS : rw_cells rsegs m (bv_unsigned sp + 32) [C8 (Z_to_bv 64 nch)].
Hypothesis HOP : 0 < out < 2^63.
Hypothesis HFP : 0 < frame /\ frame + 1492 < 2^63.
Hypothesis ST : stk rsegs m lo (bv_unsigned sp).
Hypothesis LO : lo + 32 <= bv_unsigned sp.
Hypothesis DOS : out + 3 * nch * ns <= lo \/ bv_unsigned sp + 40 <= out.
Hypothesis DFS : frame + 1500 <= lo \/ bv_unsigned sp + 40 <= frame.
Hypothesis MI : mem_inv rsegs m.

Lemma seg_DT_braid : forall (y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 : word),
  (forall (z5 z6 z7 z10 z11 z12 z13 z14 z15 z16 z17 z28 z29 z30 z31 : word) (m' : word -> option byte),
     munch [(bv_unsigned sp - 32, bv_unsigned sp)] m m' -> wmono rsegs m m' -> mem_inv rsegs m' ->
     stk rsegs m' lo (bv_unsigned sp) ->
     evt rsegs Q (MS (mkR (Z_to_bv 64 0x12fec) sp x3 x4 z5 z6 z7 x8 x9 z10 z11 z12 z13 z14 z15 z16 z17 x18
       (Z_to_bv 64 out) (Z_to_bv 64 ns) x21 x22 x23 x24 x25 (Z_to_bv 64 frame) x27 z28 z29 z30 z31)
       F (Z_to_bv 64 0x12fec) fc None m' (seg_rom rsegs))) ->
  evt rsegs Q (MS (mkR y1 sp x3 x4 y5 y6 y7 x8 x9 y10 y11 y12 y13 y14 y15 y16 y17 x18
       (Z_to_bv 64 out) (Z_to_bv 64 ns) x21 x22 x23 x24 x25 (Z_to_bv 64 frame) x27 y28 y29 y30 y31)
       F (Z_to_bv 64 0x12fd8) fc None m (seg_rom rsegs)).
Proof.
  intros y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 CONT.
  pose proof (u64_range sp) as Rsp.
  do 5 step.
  eapply evt_cut.
  { eapply (ICB _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m (frame + 50) out nch ns lo);
      first [ lia | exact ST | apply braid_map_of; first [ eassumption | lia ] | idtac ].
    all: unfold CHECK_BRAID_FRAME; try lia.
    eapply braid_map_of; first [ exact HB | exact HFR | exact HL | lia ]. }
  intros ms' (t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m'
    & -> & MU & WM & ST').
  replace (ret_pc (Z_to_bv 64 0x12fec)) with (Z_to_bv 64 0x12fec) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
  unfold CHECK_BRAID_FRAME in MU.
  eapply CONT; try eassumption.
  eapply mem_inv_munch; [exact MI | exact MU |]. intros x Hx. cbn [outside] in Hx.
  pose proof (u64_range x) as Rx.
  assert (X1 : bv_unsigned sp - 32 <= bv_unsigned x < bv_unsigned sp).
  { destruct (Z_le_dec (bv_unsigned sp - 32) (bv_unsigned x)); destruct (Z_lt_dec (bv_unsigned x) (bv_unsigned sp));
      first [ lia | exfalso; apply Hx; repeat split; first [ exact I | lia ] ]. }
  destruct ST as (_ & _ & STw). replace x with (wa (bv_unsigned x)) by (apply wa_of_var; reflexivity).
  exact (proj1 (STw (bv_unsigned x) ltac:(lia))).
Qed.

End DTB.

Section DTR.
Variables (x1 x3 x4 x5 x6 x7 x8 x9 x11 x12 x13 x14 x15 x16 x17 x18 x21 x22 x23 x24 x25 x27 x28 x29 x30 x31 sp : word)
  (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (Q : machine_state -> Prop) (nch ns out frame r : Z).
Hypothesis HS : rw_cells rsegs m (bv_unsigned sp + 32) [C8 (Z_to_bv 64 nch)].
Hypothesis Hr : -1 <= r <= 127 /\ r <> 0.
Hypothesis Hns : -128 <= ns <= 127.
Hypothesis HOP : 0 <= out < 2^63.
Hypothesis HFP : 0 <= frame < 2^62.

Local Notation STR pc y1 y10 y11 y12 y13 :=
  (MS (mkR y1 sp x3 x4 x5 x6 x7 x8 x9 y10 y11 y12 y13 x14 x15 x16 x17 x18 (Z_to_bv 64 out) (Z_to_bv 64 ns)
     x21 x22 x23 x24 x25 (Z_to_bv 64 frame) x27 x28 x29 x30 x31) F (Z_to_bv 64 pc) fc None m (seg_rom rsegs)).

Lemma seg_DT_branch :
  (0 < r -> ns <= 12 -> evt rsegs Q (STR 0x132f8 (Z_to_bv 64 0x12fd0) (Z_to_bv 64 (frame + 50)) (Z_to_bv 64 out)
     (Z_to_bv 64 nch) (Z_to_bv 64 ns))) ->
  (0 < r -> 12 < ns -> forall y11, evt rsegs Q (STR 0x12fd8 x1 (Z_to_bv 64 r) y11 x12 x13)) ->
  (r < 0 -> evt rsegs Q (STR 0x12fec x1 (Z_to_bv 64 r) x11 x12 x13)) ->
  evt rsegs Q (STR 0x12fb0 x1 (Z_to_bv 64 r) x11 x12 x13).
Proof.
  intros C1 C2 C3.
  pose proof (u64_range sp) as Rsp.
  pose proof (rw_cells_bound _ _ _ _ HS) as HSB. cbn [cells_size csize Nat.add] in HSB.
  step. rewrite lts0_lit by lia.
  destruct (Z.ltb_spec 0 r) as [P|P]; cbn [negb].
  - step. step.
    assert (LT : bv_lts (Z_to_bv 64 12) (Z_to_bv 64 ns) = (12 <? ns)).
    { unfold bv_lts. rewrite !Z_to_bv_signed. unfold bv_swrap, bv_wrap.
      change (bv_half_modulus 64) with (2^63). change (bv_modulus 64) with (2^64).
      rewrite !Z.mod_small by lia. f_equal; lia. }
    rewrite ?LT.
    destruct (Z.ltb_spec 12 ns) as [P2|P2].
    + step. rewrite lts0_lit by lia. rewrite (proj2 (Z.ltb_lt 0 r) P). cbn [negb]. apply C2; lia.
    + do 5 step. apply C1; lia.
  - step. rewrite lts0_lit by lia. rewrite (proj2 (Z.ltb_ge 0 r)) by lia. cbn [negb]. apply C3. lia.
Qed.

End DTR.
