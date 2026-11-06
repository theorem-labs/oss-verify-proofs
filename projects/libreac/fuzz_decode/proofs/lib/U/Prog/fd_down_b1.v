From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Lib Require Import Tac Bytes ZBridge.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.U Require Import Img0.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.U.Spec Require Import StrFun.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.U.Prog Require Import ReacDecodeLib reac_frame_inspect_c
  reac_decode_plain_le_c reac_decode_plain_le bcmp_c fd_down_q.
Import ListNotations.
Open Scope Z_scope.

Lemma ub_nth_repeat_lt : forall (b d : byte) n i, (i < n)%nat -> nth i (repeat b n) d = b.
Proof. intros b d n. induction n as [|n IH]; intros i H; [lia|]. destruct i; [reflexivity|]. cbn. apply IH. lia. Qed.

Lemma ub_rd_fill : forall m out n i, bytes_at rsegs m out (repeat FILL (Z.to_nat n)) -> 0 <= i < n ->
  ov_read_bytes rsegs m (Z_to_bv 64 (out + i)) 1 = Some [FILL].
Proof.
  intros m out n i H Hi. rewrite (rd1 _ _ _ i H) by (rewrite repeat_length; lia).
  rewrite ub_nth_repeat_lt by lia. reflexivity.
Qed.

Lemma ub_rw_of_wr : forall m A n (bs : list byte),
  wr_at rsegs m A (Z.of_nat n) -> length bs = n -> bytes_at rsegs m A bs -> rw_cells rsegs m A [CB n bs].
Proof.
  intros m A n bs HW HL HB. split; [split|].
  - cbn [cells_wf cell_wf]. split; [exact HL | exact I].
  - cbn [cells_bytes cbytes]. rewrite app_nil_r. exact HB.
  - cbn [cells_size csize]. rewrite Nat.add_0_r. exact HW.
Qed.

Fixpoint ub_outside_dec (W : list (Z * Z)) (x : Z) : {outside W x} + {~ outside W x}.
Proof.
  destruct W as [|[lo hi] W].
  - left. exact I.
  - destruct (Z_le_dec lo x) as [H1|H1]; [destruct (Z_lt_dec x hi) as [H2|H2]|].
    + right. cbn. tauto.
    + destruct (ub_outside_dec W x) as [O|O]; [left; cbn; split; [lia | exact O] | right; cbn; tauto].
    + destruct (ub_outside_dec W x) as [O|O]; [left; cbn; split; [lia | exact O] | right; cbn; tauto].
Defined.

Lemma ub_mem_inv_munch : forall W m1 m2, mem_inv rsegs m1 -> munch W m1 m2 ->
  (forall x : word, ~ outside W (bv_unsigned x) -> wview rsegs m1 x <> None) -> mem_inv rsegs m2.
Proof.
  intros W m1 m2 MI MU HW a b Ha.
  destruct (ub_outside_dec W (bv_unsigned a)) as [O|O].
  - rewrite (MU a O) in Ha. exact (MI a b Ha).
  - pose proof (HW a O) as Wv. destruct (m1 a) eqn:E.
    + exact (MI a _ E).
    + exact (wview_not_ro rsegs m1 a Wv E).
Qed.

Lemma ub_memcmp_refl : forall l, memcmp_model l l (length l) = Some 0.
Proof. induction l as [|a l IH]; [reflexivity|]. cbn [length memcmp_model]. rewrite Z.eqb_refl. exact IH. Qed.

Lemma ub_bytes_at_of_nth : forall m a (l : list byte), 0 <= a -> a + Z.of_nat (length l) <= 2^64 ->
  (forall i, (i < length l)%nat -> mrd rsegs m (wa (a + Z.of_nat i)) = Some (nth i l (Z_to_bv 8 0))) ->
  bytes_at rsegs m a l.
Proof.
  intros m a l H1 H2 H. split; [lia|]. split; [lia|]. intros i Hi. rewrite H by lia.
  symmetry. apply nth_error_nth'. lia.
Qed.

Definition ub_trip (bs : list byte) (nch ch s : Z) : list byte :=
  [nth (Z.to_nat (50 + 3 * (s * nch + ch))) bs (Z_to_bv 8 0);
   nth (Z.to_nat (50 + 3 * (s * nch + ch) + 1)) bs (Z_to_bv 8 0);
   nth (Z.to_nat (50 + 3 * (s * nch + ch) + 2)) bs (Z_to_bv 8 0)].

Section Trip.
Variables (m : word -> option byte) (out frame nch ns : Z) (fr : list byte).
Hypothesis HB : bytes_at rsegs m out (plain_out fr nch ns).
Hypothesis HF : bytes_at rsegs m frame fr.
Hypothesis HL : length fr = 1492%nat.
Hypothesis Hnch : 0 < nch.
Hypothesis Hns : 0 < ns.
Hypothesis H480 : nch * ns <= 480.

Lemma ub_trip_out : forall ch s, 0 <= ch < nch -> 0 <= s < ns ->
  bytes_at rsegs m (out + 3 * (ch * ns + s)) (ub_trip fr nch ch s).
Proof.
  intros ch s Hch Hs. pose proof (bytes_at_bound _ _ _ _ HB) as BB. unfold plain_out in BB.
  rewrite length_mapseq in BB. rewrite Z2Nat.id in BB by nia.
  assert (ch * ns <= (nch - 1) * ns) by nia.
  assert (A3 : 3 * (ch * ns + s) + 3 <= 3 * nch * ns) by nia.
  apply ub_bytes_at_of_nth; [lia | unfold ub_trip; cbn [length]; lia |].
  intros i Hi. unfold ub_trip in Hi; cbn [length] in Hi.
  destruct HB as (_ & _ & HB3).
  replace (out + 3 * (ch * ns + s) + Z.of_nat i) with (out + Z.of_nat (Z.to_nat (3 * (ch * ns + s)) + i)) by lia.
  unfold mrd in *. rewrite HB3 by (unfold plain_out; rewrite length_mapseq; nia).
  unfold plain_out. rewrite nth_error_mapseq by nia. cbn [Nat.add].
  replace (Z.of_nat (Z.to_nat (3 * (ch * ns + s)) + i)) with (3 * (ch * ns + s) + Z.of_nat i) by lia.
  rewrite plain_byte_at by lia.
  destruct i as [|[|[|i]]]; [| | |lia]; cbn [nth ub_trip]; do 2 f_equal; lia.
Qed.

Lemma ub_trip_frame : forall ch s, 0 <= ch < nch -> 0 <= s < ns ->
  bytes_at rsegs m (frame + 50 + 3 * (s * nch + ch)) (ub_trip fr nch ch s).
Proof.
  intros ch s Hch Hs. pose proof (bytes_at_bound _ _ _ _ HF) as BB. rewrite HL in BB.
  assert (s * nch <= (ns - 1) * nch) by nia.
  assert (A3 : 50 + 3 * (s * nch + ch) + 3 <= 1492) by nia.
  apply ub_bytes_at_of_nth; [lia | unfold ub_trip; cbn [length]; lia |].
  intros i Hi. unfold ub_trip in Hi; cbn [length] in Hi.
  destruct HF as (_ & _ & HF3).
  replace (frame + 50 + 3 * (s * nch + ch) + Z.of_nat i)
    with (frame + Z.of_nat (Z.to_nat (50 + 3 * (s * nch + ch)) + i)) by lia.
  unfold mrd in *. rewrite HF3 by nia.
  rewrite (nth_error_nth' fr (Z_to_bv 8 0)) by nia.
  destruct i as [|[|[|i]]]; [| | |lia]; cbn [nth ub_trip]; do 2 f_equal; lia.
Qed.

End Trip.

Ltac ub_closed :=
  repeat match goal with |- context [Z_to_bv 64 ?e] =>
    lazymatch e with context [v_sltu] => let v := eval vm_compute in e in change e with v end end.

Ltac usubn := repeat match goal with |- context [bv_unsigned (Z_to_bv 64 ?e)] =>
  lazymatch e with context [bv_unsigned _] => fail | _ => rewrite (unsigned_lit e) by nia end end.

Ltac usolve := usubn; rewrite ?Z.shiftl_mul_pow2, ?Z.shiftr_div_pow2 by lia; usubn; nia.

Section UFill.
Variables (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28
  x29 x30 x31 : word) (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (Q : machine_state -> Prop)
  (out n : Z).
Hypothesis HF : bytes_at rsegs m out (repeat FILL (Z.to_nat n)).
Hypothesis Hn : 1 <= n.
Hypothesis Hout : 0 <= out.
Hypothesis HoutN : out + n < 2^64.

Lemma ub_fill :
  x22 = Z_to_bv 64 out -> x23 = Z_to_bv 64 n ->
  (forall y11 y12 y13 y14 : word, evt rsegs Q (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 y11 y12 y13 y14 x15 x16 x17
     x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) F (Z_to_bv 64 0x131c4) fc None m (seg_rom rsegs))) ->
  evt rsegs Q (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25
     x26 x27 x28 x29 x30 x31) F (Z_to_bv 64 0x13194) fc None m (seg_rom rsegs)).
Proof.
  intros E22 E23 CONT. subst x22 x23.
  assert (L : forall (K : nat) (i : Z) (y11 y12 y13 y14 : word), Z.to_nat (n - i) = K -> 0 <= i < n ->
    bv_unsigned y11 = 0 -> bv_unsigned y12 = i -> bv_unsigned y13 = 18446744073709551615 - out ->
    evt rsegs Q (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 y11 y12 y13 y14 x15 x16 x17 x18 x19 x20 x21
      (Z_to_bv 64 out) (Z_to_bv 64 n) x24 x25 x26 x27 x28 x29 x30 x31) F (Z_to_bv 64 0x131a0) fc None m
      (seg_rom rsegs))).
  { induction K as [K IH] using lt_wf_ind. intros i y11 y12 y13 y14 HK Hi H11 H12 H13.
    apply wv in H11, H12, H13. subst y11 y12 y13.
    pose proof (ub_rd_fill m out n i HF Hi) as HR. unfold FILL in HR.
    step. cnd false.
    step. step. step. step. st. st. st.
    ub_closed.
    brq BR.
    - step. cnd false. apply CONT.
    - eapply (IH (Z.to_nat (n - (i + 1))) ltac:(lia) (i + 1)); [reflexivity | lia | ufin | ufin | ufin]. }
  step. step. step.
  eapply (L (Z.to_nat (n - 0)) 0); [reflexivity | lia | ufin | ufin | ufin].
Qed.

End UFill.

Section UCmp.
Context (BC : bcmp_contract).
Variables (x3 x4 sp : word) (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (Q : machine_state -> Prop)
  (out frame nch ns len : Z) (fr : list byte).
Hypothesis HL : length fr = 1492%nat.
Hypothesis HLEN : len = 1492.
Hypothesis Hnch : 0 < nch.
Hypothesis Hns : 0 < ns.
Hypothesis H480 : nch * ns <= 480.
Hypothesis HOP : 0 < out.
Hypothesis HOE : out + 3 * nch * ns < 2^64.
Hypothesis HFP : 0 < frame < 2^60.

Definition INVK (mk : word -> option byte) : Prop :=
  bytes_at rsegs mk out (plain_out fr nch ns) /\ bytes_at rsegs mk frame fr /\
  rw_cells rsegs mk (bv_unsigned sp + 8) [C8 (Z_to_bv 64 len); C8 (Z_to_bv 64 frame); C8 (Z_to_bv 64 (3 * ns));
    C8 (Z_to_bv 64 ns); C8 (Z_to_bv 64 nch); C8 (Z_to_bv 64 ns)] /\
  mem_inv rsegs mk /\ munch [(bv_unsigned sp + 8, bv_unsigned sp + 56)] m mk /\ wmono rsegs m mk.

Lemma INVK_munch0 : forall mk mk', INVK mk -> munch [] mk mk' -> wmono rsegs mk mk' -> mem_inv rsegs mk' -> INVK mk'.
Proof.
  intros mk mk' (I1 & I2 & I3 & I4 & I5 & I6) MU WM MI.
  split; [eapply bytes_at_transport; [exact I1 | exact MU | exact I]|].
  split; [eapply bytes_at_transport; [exact I2 | exact MU | exact I]|].
  split; [eapply rw_cells_transport; [exact I3 | exact MU | exact WM | exact I]|].
  split; [exact MI|].
  split; [eapply munch_trans; [exact I5 | eapply munch_weaken; [|exact MU]; intros x _; cbn; exact I]|].
  eapply wmono_trans; [exact I6 | exact WM].
Qed.

Local Notation STK pc mk y1 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16 y17 y18 y19 y20 y21 y23 y24 y25 y26 y27 y28 y29 y30 y31 :=
  (MS (mkR y1 sp x3 x4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16 y17 y18 y19 y20 y21 (Z_to_bv 64 out)
     y23 y24 y25 y26 y27 y28 y29 y30 y31) F (Z_to_bv 64 pc) fc None mk (seg_rom rsegs)).

Lemma ucmp_inner : forall (ch : Z) (y8 y18 y20 y21 y25 y26 y27 : word),
  0 <= ch < nch -> bv_unsigned y18 = frame + 50 -> bv_unsigned y20 = 3 * nch ->
  bv_unsigned y26 = 18446744073709551615 - out -> bv_unsigned y27 = 18446744073709551615 - (frame + 50) ->
  forall (K : nat) (s : Z) (mk : word -> option byte)
    (y1 y5 y6 y7 y9 y10 y11 y12 y13 y14 y15 y16 y17 y19 y23 y28 y29 y30 y31 : word),
  Z.to_nat (ns - s) = K -> 0 <= s < ns -> INVK mk ->
  bv_unsigned y9 = ns - s -> bv_unsigned y19 = 3 * (ch * ns + s) -> bv_unsigned y23 = 3 * (s * nch + ch) ->
  (forall (mk' : word -> option byte) (z1 z5 z6 z7 z9 z10 z11 z12 z13 z14 z15 z16 z17 z19 z23 z28 z29 z30 z31 : word),
     INVK mk' ->
     evt rsegs Q (STK 0x1326c mk' z1 z5 z6 z7 y8 z9 z10 z11 z12 z13 z14 z15 z16 z17 y18 z19 y20 y21 z23
       (Z_to_bv 64 0) y25 y26 y27 z28 z29 z30 z31)) ->
  evt rsegs Q (STK 0x1323c mk y1 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16 y17 y18 y19 y20 y21 y23
       (Z_to_bv 64 0) y25 y26 y27 y28 y29 y30 y31).
Proof.
  intros ch y8 y18 y20 y21 y25 y26 y27 Hch H18 H20 H26 H27 K.
  apply wv in H18, H20, H26, H27. subst y18 y20 y26 y27.
  induction K as [K IH] using lt_wf_ind.
  intros s mk y1 y5 y6 y7 y9 y10 y11 y12 y13 y14 y15 y16 y17 y19 y23 y28 y29 y30 y31 HK Hs I0 H9 H19 H23 CONT.
  apply wv in H9, H19, H23. subst y9 y19 y23.
  assert (P1 : 0 <= ch * ns) by nia.
  assert (P2 : 3 * (ch * ns + s) + 3 <= 3 * nch * ns) by nia.
  assert (P3 : 0 <= s * nch) by nia.
  assert (P4 : 3 * (s * nch + ch) + 3 <= 3 * nch * ns) by nia.
  pose proof I0 as (IB & IF & _ & IMI & _).
  step. cnd false. step. cnd false.
  step. step. step. step.
  eapply evt_cut; [eapply (BC _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ mk
                    (ub_trip fr nch ch s) (ub_trip fr nch ch s) 0) |].
  { usubn. eapply ub_trip_out; first [ eassumption | lia ]. }
  { usubn. eapply ub_trip_frame; first [ eassumption | lia ]. }
  { usubn. exact (ub_memcmp_refl (ub_trip fr nch ch s)). }
  { exact IMI. }
  intros ms' (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & mk'
    & -> & MU & WM & MI' & _ & _).
  replace (ret_pc (Z_to_bv 64 0x13254)) with (Z_to_bv 64 0x13254) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
  pose proof (INVK_munch0 mk mk' I0 MU WM MI') as I1.
  st. st. st. st. st. st.
  ub_closed.
  brq BR.
  - eapply CONT. exact I1.
  - eapply (IH (Z.to_nat (ns - (s + 1))) ltac:(lia) (s + 1)); [reflexivity | lia | exact I1 | usolve | usolve
      | usolve | exact CONT].
Qed.

Lemma ucmp_outer : forall (y18 y20 y26 y27 : word),
  bv_unsigned y18 = frame + 50 -> bv_unsigned y20 = 3 * nch ->
  bv_unsigned y26 = 18446744073709551615 - out -> bv_unsigned y27 = 18446744073709551615 - (frame + 50) ->
  forall (K : nat) (ch : Z) (mk : word -> option byte)
    (y1 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16 y17 y19 y21 y23 y24 y25 y28 y29 y30 y31 : word),
  Z.to_nat (nch - ch) = K -> 0 <= ch < nch -> INVK mk ->
  bv_unsigned y8 = 3 * ch -> bv_unsigned y21 = 3 * ns * ch -> bv_unsigned y24 = 0 -> bv_unsigned y25 = ch ->
  (forall (mk' : word -> option byte)
     (z5 z6 z7 z9 z11 z12 z13 z14 z15 z16 z17 z19 z20 z21 z23 z24 z26 z27 z28 z29 z30 z31 : word),
     INVK mk' ->
     evt rsegs Q (MS (mkR (Z_to_bv 64 0x13298) sp x3 x4 z5 z6 z7 (Z_to_bv 64 len) z9 (Z_to_bv 64 out) z11 z12 z13
       z14 z15 z16 z17 y18 z19 z20 z21 (Z_to_bv 64 out) z23 z24 (Z_to_bv 64 frame) z26 z27 z28 z29 z30 z31)
       F (Z_to_bv 64 0x14cb4) fc None mk' (seg_rom rsegs))) ->
  evt rsegs Q (STK 0x13228 mk y1 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16 y17 y18 y19 y20 y21 y23 y24 y25 y26 y27
       y28 y29 y30 y31).
Proof.
  intros y18 y20 y26 y27 H18 H20 H26 H27 K.
  induction K as [K IH] using lt_wf_ind.
  intros ch mk y1 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16 y17 y19 y21 y23 y24 y25 y28 y29 y30 y31
    HK Hch I0 H8 H21 H24 H25 CONT.
  pose proof (u64_range sp) as Rsp.
  apply wv in H8, H21, H24, H25. subst y8 y21 y24 y25.
  pose proof I0 as (_ & _ & IS & _).
  pose proof (rw_cells_bound _ _ _ _ IS) as HSB. cbn [cells_size csize Nat.add] in HSB.
  step. step. step. step. step.
  rewrite lts0_lit by lia. rewrite (proj2 (Z.ltb_lt 0 ns) Hns). cbn [negb].
  eapply (ucmp_inner ch _ y18 y20 _ _ y26 y27) with (K := Z.to_nat (ns - 0)) (s := 0);
    [ lia | exact H18 | exact H20 | exact H26 | exact H27 | reflexivity | lia | exact I0 | usolve | usolve | usolve | ].
  apply wv in H18, H20, H26, H27. subst y18 y20 y26 y27.
  intros mk' z1 z5 z6 z7 z9 z10 z11 z12 z13 z14 z15 z16 z17 z19 z23 z28 z29 z30 z31 I1.
  pose proof I1 as (_ & _ & IS1 & _).
  st. st. st. st. st. st.
  assert (Bnch : nch <= 480) by nia.
  brq BR.
  - step. step. step. cnd false. step. step. apply CONT. exact I1.
  - eapply (IH (Z.to_nat (nch - (ch + 1))) ltac:(lia) (ch + 1)); [reflexivity | lia | exact I1 | usolve | usolve
      | ufin | usolve | exact CONT].
Qed.

Lemma ucmp_entry : forall (junk : list byte)
    (y1 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16 y17 y19 y20 y21 y23 y24 y26 y27 y28 y29 y30 y31 : word),
  rw_cells rsegs m (bv_unsigned sp + 8)
    [C8 (Z_to_bv 64 len); C8 (Z_to_bv 64 frame); CB 16 junk; C8 (Z_to_bv 64 nch); C8 (Z_to_bv 64 ns)] ->
  bytes_at rsegs m out (plain_out fr nch ns) -> bytes_at rsegs m frame fr -> mem_inv rsegs m ->
  out + 3 * nch * ns <= bv_unsigned sp -> frame + 1492 <= bv_unsigned sp ->
  (forall (mk' : word -> option byte)
     (z5 z6 z7 z9 z11 z12 z13 z14 z15 z16 z17 z19 z20 z21 z23 z24 z26 z27 z28 z29 z30 z31 : word),
     munch [(bv_unsigned sp + 8, bv_unsigned sp + 56)] m mk' -> wmono rsegs m mk' -> mem_inv rsegs mk' ->
     bytes_at rsegs mk' frame fr ->
     evt rsegs Q (MS (mkR (Z_to_bv 64 0x13298) sp x3 x4 z5 z6 z7 (Z_to_bv 64 len) z9 (Z_to_bv 64 out) z11 z12 z13
       z14 z15 z16 z17 (Z_to_bv 64 (frame + 50)) z19 z20 z21 (Z_to_bv 64 out) z23 z24 (Z_to_bv 64 frame) z26 z27
       z28 z29 z30 z31) F (Z_to_bv 64 0x14cb4) fc None mk' (seg_rom rsegs))) ->
  evt rsegs Q (STK 0x131c8 m y1 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16 y17 (Z_to_bv 64 (frame + 50)) y19 y20
       y21 y23 y24 (Z_to_bv 64 frame) y26 y27 y28 y29 y30 y31).
Proof.
  intros junk y1 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16 y17 y19 y20 y21 y23 y24 y26 y27 y28 y29 y30 y31
    HS HB HF MI DO DF CONT.
  pose proof (u64_range sp) as Rsp.
  pose proof (rw_cells_bound _ _ _ _ HS) as HSB. cbn [cells_size csize Nat.add] in HSB.
  pose proof (munch_refl [(bv_unsigned sp + 8, bv_unsigned sp + 56)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  assert (LP : Z.of_nat (length (plain_out fr nch ns)) = 3 * nch * ns)
    by (unfold plain_out; rewrite !length_map, length_seq, Z2Nat.id by nia; reflexivity).
  assert (LF : Z.of_nat (length fr) = 1492) by (rewrite HL; reflexivity).
  step. cnd false. step. step. step. cnd false.
  step. step. step. step.
  rewrite lts0_lit by lia. rewrite (proj2 (Z.ltb_lt 0 nch) Hnch). cbn [negb].
  step. step. step. step. step. step. step. step. step. step. step. step.
  rewrite ?slli_srli32 by lia.
  step. step. step.
  replace (Z_to_bv 64 (Z.shiftl (bv_unsigned (Z_to_bv 64 ns)) 1 + ns)) with (Z_to_bv 64 (3 * ns))
    by (rewrite unsigned_lit, Z.shiftl_mul_pow2 by lia; f_equal; lia).
  step.
  assert (Bnch : nch <= 480) by nia. assert (Bns : ns <= 480) by nia.
  eapply (ucmp_outer (Z_to_bv 64 (frame + 50))) with (K := Z.to_nat (nch - 0)) (ch := 0).
  all: lazymatch goal with
       | |- INVK _ => unfold INVK; repeat (split; [eassumption|]); eassumption
       | |- forall _, _ => idtac
       | _ => first [ reflexivity | lia | ufin | usolve ]
       end.
  intros mk' z5 z6 z7 z9 z11 z12 z13 z14 z15 z16 z17 z19 z20' z21 z23 z24 z26 z27 z28 z29 z30 z31
    (I1 & I2 & I3 & I4 & I5 & I6).
  apply CONT; assumption.
Qed.

End UCmp.
