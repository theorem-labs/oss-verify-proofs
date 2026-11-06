From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Lib Require Import Tac Bytes.
From OSSVerify.Proofs.libreac.fuzz_decode.lib Require Import Img0.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Spec Require Import StrFun.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Prog Require Import ReacDecodeLib
  reac_frame_inspect_c reac_decode_plain_le_c bcmp_c.
Import ListNotations.
Open Scope Z_scope.

Lemma memcmp_model_refl : forall l, memcmp_model l l (length l) = Some 0.
Proof. induction l as [|a l IH]; [reflexivity|]. cbn [length memcmp_model]. rewrite Z.eqb_refl. exact IH. Qed.

Lemma bytes_at_of_nth : forall m a (l : list byte), 0 <= a -> a + Z.of_nat (length l) <= 2^64 ->
  (forall i, (i < length l)%nat -> mrd rsegs m (wa (a + Z.of_nat i)) = Some (nth i l (Z_to_bv 8 0))) ->
  bytes_at rsegs m a l.
Proof.
  intros m a l H1 H2 H. split; [lia|]. split; [lia|]. intros i Hi. rewrite H by lia.
  symmetry. apply nth_error_nth'. lia.
Qed.

Lemma plain_byte_at' : forall bs nch ns ch s k, 0 <= ch -> 0 <= s < ns -> 0 <= k < 3 ->
  plain_byte bs nch ns (3 * (ch * ns + s) + k) = nth (Z.to_nat (50 + 3 * (s * nch + ch) + k)) bs (Z_to_bv 8 0).
Proof.
  intros bs nch ns ch s k Hch Hs Hk. unfold plain_byte.
  destruct (braid_div ch s k ns Hch Hs Hk) as (D1 & D2 & D3 & D4). rewrite D1, D2, D3, D4. reflexivity.
Qed.

Definition trip (bs : list byte) (nch ch s : Z) : list byte :=
  [nth (Z.to_nat (50 + 3 * (s * nch + ch))) bs (Z_to_bv 8 0);
   nth (Z.to_nat (50 + 3 * (s * nch + ch) + 1)) bs (Z_to_bv 8 0);
   nth (Z.to_nat (50 + 3 * (s * nch + ch) + 2)) bs (Z_to_bv 8 0)].

Section Cmp.
Variables (m : word -> option byte) (out frame nch ns : Z) (fr : list byte).
Hypothesis HB : bytes_at rsegs m out (plain_out fr nch ns).
Hypothesis HF : bytes_at rsegs m frame fr.
Hypothesis HL : length fr = 1492%nat.
Hypothesis Hnch : 0 < nch.
Hypothesis Hns : 0 < ns.
Hypothesis H480 : nch * ns <= 480.

Lemma trip_out : forall ch s, 0 <= ch < nch -> 0 <= s < ns ->
  bytes_at rsegs m (out + 3 * (ch * ns + s)) (trip fr nch ch s).
Proof.
  intros ch s Hch Hs. pose proof (bytes_at_bound _ _ _ _ HB) as BB. unfold plain_out in BB.
  rewrite length_mapseq in BB. rewrite Z2Nat.id in BB by nia.
  assert (ch * ns <= (nch - 1) * ns) by nia.
  assert (A3 : 3 * (ch * ns + s) + 3 <= 3 * nch * ns) by nia.
  apply bytes_at_of_nth; [lia | unfold trip; cbn [length]; lia |].
  intros i Hi. unfold trip in Hi; cbn [length] in Hi.
  destruct HB as (_ & _ & HB3).
  replace (out + 3 * (ch * ns + s) + Z.of_nat i) with (out + Z.of_nat (Z.to_nat (3 * (ch * ns + s)) + i)) by lia.
  rewrite HB3 by (unfold plain_out; rewrite length_mapseq; nia).
  unfold plain_out. rewrite nth_error_mapseq by nia. cbn [Nat.add].
  replace (Z.of_nat (Z.to_nat (3 * (ch * ns + s)) + i)) with (3 * (ch * ns + s) + Z.of_nat i) by lia.
  rewrite plain_byte_at' by lia.
  destruct i as [|[|[|i]]]; [| | |lia]; cbn [nth trip]; do 2 f_equal; lia.
Qed.

Lemma trip_frame : forall ch s, 0 <= ch < nch -> 0 <= s < ns ->
  bytes_at rsegs m (frame + 50 + 3 * ch + 3 * nch * s) (trip fr nch ch s).
Proof.
  intros ch s Hch Hs. pose proof (bytes_at_bound _ _ _ _ HF) as BB. rewrite HL in BB.
  assert (s * nch <= (ns - 1) * nch) by nia.
  assert (A3 : 50 + 3 * ch + 3 * nch * s + 3 <= 1492) by nia.
  apply bytes_at_of_nth; [lia | unfold trip; cbn [length]; lia |].
  intros i Hi. unfold trip in Hi; cbn [length] in Hi.
  destruct HF as (_ & _ & HF3).
  replace (frame + 50 + 3 * ch + 3 * nch * s + Z.of_nat i)
    with (frame + Z.of_nat (Z.to_nat (50 + 3 * (s * nch + ch)) + i)) by lia.
  rewrite HF3 by nia.
  rewrite (nth_error_nth' fr (Z_to_bv 8 0)) by nia.
  destruct i as [|[|[|i]]]; [| | |lia]; cbn [nth trip]; do 2 f_equal; lia.
Qed.

End Cmp.

Ltac closed_vals' :=
  repeat match goal with |- context [Z_to_bv 64 ?e] =>
    lazymatch e with context [v_sltu] => let v := eval vm_compute in e in change e with v end end.

Section CmpLoop.
Context (BC : bcmp_contract).
Variables (x1 x3 x4 x5 x6 x7 x9 x11 x12 x13 x14 x15 x16 x17 x18 x21 x22 x23 x24 x27 x28 x29 x30 x31 sp : word)
  (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (Q : machine_state -> Prop)
  (out frame nch ns len : Z) (fr junk : list byte).
Hypothesis HL : length fr = 1492%nat.
Hypothesis HLEN : len = 1492.
Hypothesis Hnch : 0 < nch.
Hypothesis Hns : 0 < ns.
Hypothesis H480 : nch * ns <= 480.
Hypothesis HOP : 0 < out.
Hypothesis HOE : out + 3 * nch * ns < 2^64.
Hypothesis HFP : 0 < frame < 2^63.

Definition INVC (mk : word -> option byte) : Prop :=
  bytes_at rsegs mk out (plain_out fr nch ns) /\ bytes_at rsegs mk frame fr /\
  rw_cells rsegs mk (bv_unsigned sp + 8)
    [C8 (Z_to_bv 64 (frame + 50)); C8 (Z_to_bv 64 frame); C8 (Z_to_bv 64 len)] /\
  rw_cells rsegs mk (bv_unsigned sp + 32) [C8 (Z_to_bv 64 nch)] /\
  mem_inv rsegs mk /\ munch [(bv_unsigned sp + 8, bv_unsigned sp + 32)] m mk /\ wmono rsegs m mk.

Lemma INVC_munch0 : forall mk mk', INVC mk -> munch [] mk mk' -> wmono rsegs mk mk' -> mem_inv rsegs mk' -> INVC mk'.
Proof.
  intros mk mk' (I1 & I2 & I3 & I4 & I5 & I6 & I7) MU WM MI.
  split; [eapply bytes_at_transport; [exact I1 | exact MU | exact I]|].
  split; [eapply bytes_at_transport; [exact I2 | exact MU | exact I]|].
  split; [eapply rw_cells_transport; [exact I3 | exact MU | exact WM | exact I]|].
  split; [eapply rw_cells_transport; [exact I4 | exact MU | exact WM | exact I]|].
  split; [exact MI|].
  split; [eapply munch_trans; [exact I6 | eapply munch_weaken; [|exact MU]; intros x _; cbn; exact I]|].
  eapply wmono_trans; [exact I7 | exact WM].
Qed.

Local Notation STC pc mk y1 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16 y17 y18 y21 y22 y23 y24 y25 y26 y27 y28 y29 y30 y31 :=
  (MS (mkR y1 sp x3 x4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16 y17 y18 (Z_to_bv 64 out) (Z_to_bv 64 ns)
     y21 y22 y23 y24 y25 y26 y27 y28 y29 y30 y31) F (Z_to_bv 64 pc) fc None mk (seg_rom rsegs)).

Lemma cmp_inner : forall (ch : Z) (y8 y9 y18 y21 y26 y27 : word),
  0 <= ch < nch -> bv_unsigned y8 = frame + 50 + 3 * ch -> bv_unsigned y9 = out + 3 * (ch * ns + ns) ->
  bv_unsigned y26 = 3 * nch ->
  forall (K : nat) (s : Z) (mk : word -> option byte) (y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y22 y23 y28 y29 y30 y31 : word),
  Z.to_nat (ns - s) = K -> 0 <= s < ns -> INVC mk ->
  bv_unsigned y22 = out + 3 * (ch * ns + s) -> bv_unsigned y23 = frame + 50 + 3 * ch + 3 * nch * s ->
  (forall (mk' : word -> option byte) (z1 z5 z6 z7 z10 z11 z12 z13 z14 z15 z16 z17 z22 z23 z28 z29 z30 z31 : word),
     INVC mk' -> bv_unsigned z22 = out + 3 * (ch * ns + ns) ->
     evt rsegs Q (STC 0x130d0 mk' z1 z5 z6 z7 y8 y9 z10 z11 z12 z13 z14 z15 z16 z17 y18 y21 z22 z23 (Z_to_bv 64 0)
       (Z_to_bv 64 ch) y26 y27 z28 z29 z30 z31)) ->
  evt rsegs Q (STC 0x130ac mk y1 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16 y17 y18 y21 y22 y23 (Z_to_bv 64 0)
       (Z_to_bv 64 ch) y26 y27 y28 y29 y30 y31).
Proof.
  intros ch y8 y9 y18 y21 y26 y27 Hch H8 H9 H26 K.
  induction K as [K IH] using lt_wf_ind.
  intros s mk y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y22 y23 y28 y29 y30 y31 HK Hs I0 H22 H23 CONT.
  assert (ch * ns <= (nch - 1) * ns) by nia.
  assert (s * nch <= (ns - 1) * nch) by nia.
  apply wv in H8, H9, H22, H23, H26. subst y8 y9 y22 y23 y26.
  pose proof I0 as (IB & IF & _ & _ & IMI & _).
  pose proof (bytes_at_bound _ _ _ _ IF) as BF. rewrite HL in BF.
  pose proof (bytes_at_bound _ _ _ _ IB) as BB. unfold plain_out in BB. rewrite length_mapseq, Z2Nat.id in BB by nia.
  step. step. step. step.
  eapply evt_cut; [eapply (BC _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ mk
                    (trip fr nch ch s) (trip fr nch ch s) 0) |].
  { rewrite unsigned_lit by nia. eapply trip_out; first [ eassumption | lia ]. }
  { rewrite unsigned_lit by nia. eapply trip_frame; first [ eassumption | lia ]. }
  { rewrite unsigned_lit by lia. exact (memcmp_model_refl (trip fr nch ch s)). }
  { exact IMI. }
  intros ms' (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & mk'
    & -> & MU & WM & MI' & _ & _).
  replace (ret_pc (Z_to_bv 64 0x130bc)) with (Z_to_bv 64 0x130bc) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
  pose proof (INVC_munch0 mk mk' I0 MU WM MI') as I1.
  step. step. step. step. step.
  closed_vals'.
  brq BR.
  - eapply CONT; [exact I1 | rewrite unsigned_lit by nia; lia].
  - eapply (IH (Z.to_nat (ns - (s + 1))) ltac:(lia) (s + 1)); [reflexivity | lia | exact I1
      | rewrite unsigned_lit by nia; lia | rewrite unsigned_lit by nia; lia | exact CONT].
Qed.

Ltac usolve :=
  repeat match goal with |- context [bv_unsigned (Z_to_bv 64 ?e)] =>
    lazymatch e with context [bv_unsigned _] => fail | _ => rewrite (unsigned_lit e) by nia end end;
  rewrite ?Z.shiftl_mul_pow2, ?Z.shiftr_div_pow2 by lia;
  repeat match goal with |- context [bv_unsigned (Z_to_bv 64 ?e)] =>
    lazymatch e with context [bv_unsigned _] => fail | _ => rewrite (unsigned_lit e) by nia end end;
  nia.

Lemma cmp_outer : forall (K : nat) (ch : Z) (mk : word -> option byte)
    (y1 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16 y17 y18 y21 y22 y23 y25 y26 y27 y28 y29 y30 y31 : word),
  Z.to_nat (nch - ch) = K -> 0 <= ch < nch -> INVC mk ->
  bv_unsigned y8 = frame + 50 + 3 * ch -> bv_unsigned y18 = 3 * ns -> bv_unsigned y21 = out + 3 * ns * ch ->
  bv_unsigned y25 = ch -> bv_unsigned y26 = 3 * nch -> bv_unsigned y27 = 3 * ns ->
  (forall (mk' : word -> option byte) (z1 z5 z6 z7 z9 z10 z11 z12 z13 z14 z15 z16 z17 z18 z21 z22 z23 z27 z28 z29 z30 z31 : word),
     INVC mk' ->
     evt rsegs Q (STC 0x130f4 mk' z1 z5 z6 z7 (Z_to_bv 64 (frame + 50)) z9 z10 z11 z12 z13 z14 z15 z16 z17 z18 z21 z22 z23
       (Z_to_bv 64 0) (Z_to_bv 64 len) (Z_to_bv 64 frame) z27 z28 z29 z30 z31)) ->
  evt rsegs Q (STC 0x13094 mk y1 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16 y17 y18 y21 y22 y23 (Z_to_bv 64 0)
       y25 y26 y27 y28 y29 y30 y31).
Proof.
  induction K as [K IH] using lt_wf_ind.
  intros ch mk y1 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16 y17 y18 y21 y22 y23 y25 y26 y27 y28 y29 y30 y31
    HK Hch I0 H8 H18 H21 H25 H26 H27 CONT.
  assert (ch * ns <= (nch - 1) * ns) by nia.
  pose proof (u64_range sp) as Rsp.
  apply wv in H8, H18, H21, H25, H26, H27. subst y8 y18 y21 y25 y26 y27.
  step. rewrite lts0_lit by lia. rewrite (proj2 (Z.ltb_lt 0 ns) Hns). cbn [negb].
  do 5 step.
  eapply (cmp_inner ch) with (K := Z.to_nat (ns - 0)) (s := 0);
    [ lia | usolve | usolve | usolve | reflexivity | lia | exact I0 | usolve | usolve | ].
  intros mk' z1 z5 z6 z7 z10 z11 z12 z13 z14 z15 z16 z17 z22 z23 z28 z29 z30 z31 I1 H22.
  pose proof I1 as (_ & _ & _ & IC & _).
  step. step. step. step. step.
  brq BR.
  - pose proof I1 as (_ & _ & IS & _).
    step. step. step. step.
    rewrite eqb_lit by lia. cbn [negb Z.eqb Pos.eqb]. cbn iota.
    apply CONT. exact I1.
  - eapply (IH (Z.to_nat (nch - (ch + 1))) ltac:(lia) (ch + 1)); [reflexivity | lia | exact I1 | usolve | usolve
      | usolve | usolve | usolve | usolve | exact CONT].
Qed.

Lemma cmp_entry : forall (y1 y5 y6 y7 y9 y11 y12 y13 y14 y15 y16 y17 y18 y21 y22 y23 y24 y27 y28 y29 y30 y31 : word),
  rw_cells rsegs m (bv_unsigned sp + 8) [CB 24 junk] ->
  rw_cells rsegs m (bv_unsigned sp + 32) [C8 (Z_to_bv 64 nch)] ->
  bytes_at rsegs m out (plain_out fr nch ns) -> bytes_at rsegs m frame fr -> mem_inv rsegs m ->
  (out + 3 * nch * ns <= bv_unsigned sp + 8 \/ bv_unsigned sp + 40 <= out) ->
  (frame + 1492 <= bv_unsigned sp + 8 \/ bv_unsigned sp + 40 <= frame) ->
  (forall (mk' : word -> option byte) (z1 z5 z6 z7 z9 z10 z11 z12 z13 z14 z15 z16 z17 z18 z21 z22 z23 z27 z28 z29 z30 z31 : word),
     INVC mk' ->
     evt rsegs Q (STC 0x130f4 mk' z1 z5 z6 z7 (Z_to_bv 64 (frame + 50)) z9 z10 z11 z12 z13 z14 z15 z16 z17 z18 z21 z22 z23
       (Z_to_bv 64 0) (Z_to_bv 64 len) (Z_to_bv 64 frame) z27 z28 z29 z30 z31)) ->
  evt rsegs Q (STC 0x13058 m y1 y5 y6 y7 (Z_to_bv 64 (frame + 50)) y9 (Z_to_bv 64 nch) y11 y12 y13 y14 y15 y16 y17
       y18 y21 y22 y23 y24 (Z_to_bv 64 len) (Z_to_bv 64 frame) y27 y28 y29 y30 y31).
Proof.
  intros y1 y5 y6 y7 y9 y11 y12 y13 y14 y15 y16 y17 y18 y21 y22 y23 y24 y27 y28 y29 y30 y31
    HS8 HS32 HB HF MI DO DF CONT.
  pose proof (u64_range sp) as Rsp.
  pose proof (rw_cells_bound _ _ _ _ HS8) as HSB. cbn [cells_size csize Nat.add] in HSB.
  pose proof (rw_cells_bound _ _ _ _ HS32) as HSB2. cbn [cells_size csize Nat.add] in HSB2.
  pose proof (munch_refl [(bv_unsigned sp + 8, bv_unsigned sp + 32)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  pose proof (bytes_at_bound _ _ _ _ HF) as BF. rewrite HL in BF.
  pose proof (bytes_at_bound _ _ _ _ HB) as BB. unfold plain_out in BB. rewrite length_mapseq, Z2Nat.id in BB by nia.
  assert (LP : Z.of_nat (length (plain_out fr nch ns)) = 3 * nch * ns)
    by (unfold plain_out; rewrite length_mapseq, Z2Nat.id by nia; reflexivity).
  assert (LF : Z.of_nat (length fr) = 1492) by (rewrite HL; reflexivity).
  do 15 step.
  eapply (cmp_outer (Z.to_nat (nch - 0)) 0); [reflexivity | lia | | usolve | usolve | usolve | usolve | usolve | usolve | exact CONT].
  split; [eassumption|]. split; [eassumption|]. split; [eassumption|]. split; [eassumption|].
  split; [eassumption|]. split; eassumption.
Qed.

End CmpLoop.
