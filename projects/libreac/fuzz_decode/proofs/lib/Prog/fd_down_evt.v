From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Lib Require Import Tac Bytes.
From OSSVerify.Proofs.libreac.fuzz_decode.lib Require Import Img0.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Prog Require Import ReacDecodeLib SlotLoops SlotDown SlotDownB
  SlotDownT SlotCmp reac_frame_inspect_c reac_frame_counter_c memset_c reac_decode_c reac_decode_plain_le_c
  bcmp_c check_braid_c.
Import ListNotations.
Open Scope Z_scope.

Lemma rw_of_wr : forall m A n (bs : list byte),
  wr_at rsegs m A (Z.of_nat n) -> length bs = n -> bytes_at rsegs m A bs -> rw_cells rsegs m A [CB n bs].
Proof.
  intros m A n bs HW HL HB. split; [split|].
  - cbn [cells_wf cell_wf]. split; [exact HL | exact I].
  - cbn [cells_bytes cbytes]. rewrite app_nil_r. exact HB.
  - cbn [cells_size csize]. rewrite Nat.add_0_r. exact HW.
Qed.

Lemma munch_join : forall W W1 W2 m m1 m2, munch W1 m m1 -> munch W2 m1 m2 -> sub_fp W1 W -> sub_fp W2 W ->
  munch W m m2.
Proof.
  intros W W1 W2 m m1 m2 H1 H2 S1 S2.
  eapply munch_trans; [eapply munch_weaken; [exact S1 | exact H1] | eapply munch_weaken; [exact S2 | exact H2]].
Qed.

Lemma decode_ok_facts : forall len bs nch ns, decode_ok len bs nch ns = true ->
  len = 1492 /\ 0 < nch /\ nch mod 2 = 0 /\ 0 < ns /\ nch * ns <= 480 /\ fd_olen nch ns = 3 * nch * ns /\
  pokz len bs nch ns = 1.
Proof.
  intros len bs nch ns H. pose proof H as H'. apply decode_ok_spec' in H'.
  destruct H' as (W & H1 & H2 & H3 & H4). pose proof W as W'. apply inspect_wf_spec in W'.
  split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|].
  split; [unfold fd_olen; rewrite (proj2 (Z.ltb_lt 0 nch)), (proj2 (Z.ltb_lt 0 ns)) by lia; reflexivity|].
  unfold pokz. rewrite W, (proj2 (Z.ltb_lt 0 nch)), (proj2 (Z.ltb_lt 0 ns)), (proj2 (Z.ltb_lt (nch * ns) 481)) by lia.
  reflexivity.
Qed.

Ltac side := lazymatch goal with |- forall _, _ => fail | |- _ => first [eassumption | lia | (left; lia) | (right; lia)] end.

Section DM.
Context (IHI : reac_frame_inspect_contract) (IHC : reac_frame_counter_contract) (IMS : memset_contract)
  (IDE : reac_decode_contract) (ICB : check_braid_contract) (IPL : reac_decode_plain_le_contract)
  (BC : bcmp_contract).
Variables (x3 x4 x21 x24 x27 sp : word) (F : bvmap 5 word) (fc : bv 32) (Q : machine_state -> Prop)
  (mode nch ns out frame len lo : Z) (fr junk8 : list byte).
Hypothesis Hnch : -128 <= nch <= 127.
Hypothesis Hns : -128 <= ns <= 127.
Hypothesis HLEN : Z.of_nat (length fr) = len.
Hypothesis HLB : 0 <= len < 2^26.
Hypothesis HOP : 4096 <= out < 2^60.
Hypothesis HFP : 4096 <= frame < 2^60.
Hypothesis HMP : 0 <= mode < 2^60.
Hypothesis LO : lo + 4096 <= bv_unsigned sp.
Hypothesis DOF : out + fd_olen nch ns <= frame \/ frame + len <= out.
Hypothesis DOS : out + fd_olen nch ns <= lo.
Hypothesis DOM : out + fd_olen nch ns <= mode + 4 \/ mode + 12 <= out.
Hypothesis DFS : frame + len + 1500 <= lo.
Hypothesis DMS : mode + 12 <= lo \/ bv_unsigned sp + 40 <= mode + 4.

Definition dn_W : list (Z * Z) := [(lo, bv_unsigned sp + 32); (out, out + fd_olen nch ns)].

Definition dn_free_k (m : word -> option byte) : Prop :=
  forall (z5 z6 z7 z9 z11 z12 z13 z14 z15 z16 z17 z18 z21 z22 z23 z24 z27 z28 z29 z30 z31 : word)
    (m' : word -> option byte),
    munch dn_W m m' -> wmono rsegs m m' -> mem_inv rsegs m' ->
    bytes_at rsegs m' frame fr -> stk rsegs m' lo (bv_unsigned sp) ->
    evt rsegs Q (MS (mkR (Z_to_bv 64 0x130fc) sp x3 x4 z5 z6 z7 (Z_to_bv 64 (frame + 50)) z9 (Z_to_bv 64 out)
      z11 z12 z13 z14 z15 z16 z17 z18 (Z_to_bv 64 out) (Z_to_bv 64 ns) z21 z22 z23 z24 (Z_to_bv 64 len)
      (Z_to_bv 64 frame) z27 z28 z29 z30 z31) F (Z_to_bv 64 0x14684) fc None m' (seg_rom rsegs)).

Definition dn_crt_k (m : word -> option byte) : Prop :=
  decode_ok len fr nch ns = true -> ns <= 12 ->
  forall (y8 y9 u5 u6 u7 u14 u15 u16 u17 u28 u29 u30 u31 : word) (m' : word -> option byte),
    munch dn_W m m' -> wmono rsegs m m' -> mem_inv rsegs m' ->
    stk rsegs m' lo (bv_unsigned sp) -> bytes_at rsegs m' frame fr ->
    bytes_at rsegs m' (mode + 4) (le4 (Z_to_bv 64 nch) ++ le4 (Z_to_bv 64 ns)) ->
    rw_cells rsegs m' (bv_unsigned sp + 32) [C8 (Z_to_bv 64 nch)] ->
    rw_cells rsegs m' (bv_unsigned sp + 8) [CB 24 junk8] ->
    bytes_at rsegs m' out (braid_out fr nch ns) -> wr_at rsegs m' out (fd_olen nch ns) ->
    evt rsegs Q (MS (mkR (Z_to_bv 64 0x12fd0) sp x3 x4 u5 u6 u7 y8 y9 (Z_to_bv 64 (frame + 50))
      (Z_to_bv 64 out) (Z_to_bv 64 nch) (Z_to_bv 64 ns) u14 u15 u16 u17 (Z_to_bv 64 mode) (Z_to_bv 64 out)
      (Z_to_bv 64 ns) x21 (Z_to_bv 64 (fd_olen nch ns)) (Z_to_bv 64 (pokz len fr nch ns)) x24 (Z_to_bv 64 len)
      (Z_to_bv 64 frame) x27 u28 u29 u30 u31) F (Z_to_bv 64 0x132f8) fc None m' (seg_rom rsegs)).

Lemma dn_free_k_shift : forall m m1, munch dn_W m m1 -> wmono rsegs m m1 -> dn_free_k m -> dn_free_k m1.
Proof.
  intros m m1 MU WM K z5 z6 z7 z9 z11 z12 z13 z14 z15 z16 z17 z18 z21 z22 z23 z24 z27 z28 z29 z30 z31 m' MU' WM'.
  apply K; [exact (munch_trans _ _ _ _ MU MU') | exact (wmono_trans _ _ _ _ WM WM')].
Qed.

Lemma olen_ge1 : 1 <= fd_olen nch ns.
Proof. unfold fd_olen. destruct ((0 <? nch) && (0 <? ns)) eqn:E; [rewrite andb_true_iff, !Z.ltb_lt in E; nia | lia]. Qed.

Lemma dn_plain_tail : forall (m : word -> option byte) (junk : list byte)
    (y1 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 : word),
  bytes_at rsegs m (mode + 4) (le4 (Z_to_bv 64 nch) ++ le4 (Z_to_bv 64 ns)) ->
  rw_cells rsegs m (bv_unsigned sp + 8) [CB 24 junk8] ->
  rw_cells rsegs m (bv_unsigned sp + 32) [C8 (Z_to_bv 64 nch)] ->
  bytes_at rsegs m frame fr -> rw_cells rsegs m out [CB (Z.to_nat (fd_olen nch ns)) junk] ->
  stk rsegs m lo (bv_unsigned sp) -> mem_inv rsegs m ->
  dn_free_k m ->
  evt rsegs Q (MS (mkR y1 sp x3 x4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16 y17 (Z_to_bv 64 mode)
    (Z_to_bv 64 out) (Z_to_bv 64 ns) x21 (Z_to_bv 64 (fd_olen nch ns)) (Z_to_bv 64 (pokz len fr nch ns)) x24
    (Z_to_bv 64 len) (Z_to_bv 64 frame) x27 y28 y29 y30 y31) F (Z_to_bv 64 0x12fec) fc None m (seg_rom rsegs)).
Proof.
  intros m junk y1 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 HM HS8 HS HFR HO ST MI K.
  pose proof olen_ge1 as OL.
  pose proof (u64_range sp) as Rsp.
  eapply seg_DT_plain. all: try side. all: try side.
  intros z5 z6 z7 z9 z11 z12 z13 z14 z15 z16 z17 z18 z21 z22 z23 z24 z27 z28 z29 z30 z31 m' MU WM MI' HF' ST'.
  apply K; try assumption.
  eapply munch_weaken; [|exact MU]. unfold sub_fp, dn_W. intros x. cbn [outside]. intros (H1 & H2 & _).
  pose proof (u64_range sp). repeat split; try exact I; lia.
Qed.

Lemma dn_braid_tail : forall (m : word -> option byte)
    (y1 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 : word),
  decode_ok len fr nch ns = true ->
  bytes_at rsegs m (mode + 4) (le4 (Z_to_bv 64 nch) ++ le4 (Z_to_bv 64 ns)) ->
  rw_cells rsegs m (bv_unsigned sp + 8) [CB 24 junk8] ->
  rw_cells rsegs m (bv_unsigned sp + 32) [C8 (Z_to_bv 64 nch)] ->
  bytes_at rsegs m frame fr -> bytes_at rsegs m out (braid_out fr nch ns) -> wr_at rsegs m out (fd_olen nch ns) ->
  stk rsegs m lo (bv_unsigned sp) -> mem_inv rsegs m ->
  dn_free_k m ->
  evt rsegs Q (MS (mkR y1 sp x3 x4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16 y17 (Z_to_bv 64 mode)
    (Z_to_bv 64 out) (Z_to_bv 64 ns) x21 (Z_to_bv 64 (fd_olen nch ns)) (Z_to_bv 64 (pokz len fr nch ns)) x24
    (Z_to_bv 64 len) (Z_to_bv 64 frame) x27 y28 y29 y30 y31) F (Z_to_bv 64 0x12fd8) fc None m (seg_rom rsegs)).
Proof.
  intros m y1 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 OK HM HS8 HS HFR HB HW ST MI K.
  destruct (decode_ok_facts len fr nch ns OK) as (L1492 & P1 & P2 & P3 & P4 & PO & PK).
  assert (HL : length fr = 1492%nat) by lia.
  pose proof (u64_range sp) as Rsp0.
  eapply seg_DT_braid. all: try side. all: try side.
  intros z5 z6 z7 z10 z11 z12 z13 z14 z15 z16 z17 z28 z29 z30 z31 m1 MU1 WM1 MI1 ST1.
  assert (W1 : munch dn_W m m1).
  { eapply munch_weaken; [|exact MU1]. unfold sub_fp, dn_W. intros x. cbn [outside]. intros (H1 & H2 & _).
    pose proof (u64_range sp). repeat split; try exact I; lia. }
  pose proof (u64_range sp) as Rsp.
  pose proof (rw_cells_bound _ _ _ _ HS8) as B8. cbn [cells_size csize Nat.add] in B8.
  pose proof (bytes_at_bound _ _ _ _ HB) as BB. unfold braid_out in BB. rewrite length_mapseq in BB.
  apply (dn_plain_tail m1 (braid_out fr nch ns)).
  - eapply bytes_at_transport; [exact HM | exact MU1 |]. cbn [disjoint_from]. rewrite length_app, !length_le4.
    split; [lia | exact I].
  - eapply rw_cells_transport; [exact HS8 | exact MU1 | exact WM1 |]. cbn [disjoint_from cells_size csize].
    split; [lia | exact I].
  - eapply rw_cells_transport; [exact HS | exact MU1 | exact WM1 |]. cbn [disjoint_from cells_size csize].
    split; [lia | exact I].
  - eapply bytes_at_transport; [exact HFR | exact MU1 |]. cbn [disjoint_from]. split; [lia | exact I].
  - apply rw_of_wr.
    + rewrite Z2Nat.id by (pose proof olen_ge1; lia). eapply wr_at_transport; [exact HW | exact WM1].
    + unfold braid_out. rewrite length_mapseq, PO. reflexivity.
    + assert (LB : Z.of_nat (length (braid_out fr nch ns)) = 3 * nch * ns)
        by (unfold braid_out; rewrite length_mapseq; lia).
      eapply bytes_at_transport; [exact HB | exact MU1 |]. cbn [disjoint_from]. rewrite LB. split; [lia | exact I].
  - exact ST1.
  - exact MI1.
  - exact (dn_free_k_shift m m1 W1 WM1 K).
Qed.

Lemma dn_post : forall (m : word -> option byte)
    (y1 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 : word),
  decode_ok len fr nch ns = true ->
  bytes_at rsegs m (mode + 4) (le4 (Z_to_bv 64 nch) ++ le4 (Z_to_bv 64 ns)) ->
  rw_cells rsegs m (bv_unsigned sp + 8) [CB 24 junk8] ->
  rw_cells rsegs m (bv_unsigned sp + 32) [C8 (Z_to_bv 64 nch)] ->
  bytes_at rsegs m frame fr -> bytes_at rsegs m out (braid_out fr nch ns) -> wr_at rsegs m out (fd_olen nch ns) ->
  stk rsegs m lo (bv_unsigned sp) -> mem_inv rsegs m ->
  dn_free_k m ->
  evt rsegs Q (MS (mkR y1 sp x3 x4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16 y17 (Z_to_bv 64 mode)
    (Z_to_bv 64 out) (Z_to_bv 64 ns) x21 (Z_to_bv 64 (fd_olen nch ns)) (Z_to_bv 64 (pokz len fr nch ns)) x24
    (Z_to_bv 64 len) (Z_to_bv 64 frame) x27 y28 y29 y30 y31) F (Z_to_bv 64 0x12fd0) fc None m (seg_rom rsegs)).
Proof.
  intros m y1 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 OK HM HS8 HS HFR HB HW ST MI K.
  step. apply dn_braid_tail; assumption.
Qed.

Lemma dn_mid : forall (m : word -> option byte) (junk : list byte)
    (x1 x5 x6 x7 x8 x9 x11 x12 x13 x14 x15 x16 x17 x19 x28 x29 x30 x31 : word),
  bytes_at rsegs m (mode + 4) (le4 (Z_to_bv 64 nch) ++ le4 (Z_to_bv 64 ns)) ->
  rw_cells rsegs m (bv_unsigned sp + 8) [CB 24 junk8] ->
  rw_cells rsegs m (bv_unsigned sp + 32) [C8 (Z_to_bv 64 nch)] ->
  bytes_at rsegs m frame fr -> rw_cells rsegs m out [CB (Z.to_nat (fd_olen nch ns)) junk] ->
  stk rsegs m lo (bv_unsigned sp) -> mem_inv rsegs m ->
  dn_crt_k m -> dn_free_k m ->
  evt rsegs Q (MS (mkR x1 sp x3 x4 x5 x6 x7 x8 x9 (Z_to_bv 64 out) x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 mode)
     x19 (Z_to_bv 64 ns) x21 (Z_to_bv 64 (fd_olen nch ns)) (Z_to_bv 64 (fd_fits nch ns)) x24 (Z_to_bv 64 len)
     (Z_to_bv 64 frame) x27 x28 x29 x30 x31) F (Z_to_bv 64 0x12eb4) fc None m (seg_rom rsegs)).
Proof.
  intros m junk x1 x5 x6 x7 x8 x9 x11 x12 x13 x14 x15 x16 x17 x19 x28 x29 x30 x31 HM HS8 HS HFR HO ST MI KC KF.
  pose proof (bytes_at_bound _ _ _ _ HFR) as HFB. rewrite HLEN in HFB.
  pose proof (u64_range sp) as Rsp.
  pose proof olen_ge1 as OL.
  pose proof (rw_cells_bound _ _ _ _ HS8) as B8. cbn [cells_size csize Nat.add] in B8.
  step. if_cases HC; [exfalso; zify_cond HC; lia|].
  do 5 step.
  pose proof IHI as IH. unfold reac_frame_inspect_contract in IH.
  eapply evt_cut.
  { eapply IH with (bs := fr). intros E. rewrite (unsigned_lit len) in E by lia.
    split; [lia | rewrite (unsigned_lit frame) by lia; exact HFR]. }
  intros ms' (a1' & a2' & ->).
  replace (ret_pc (Z_to_bv 64 0x12ecc)) with (Z_to_bv 64 0x12ecc) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
  rewrite (unsigned_lit len) by lia.
  eapply seg_DB_W. all: try side. all: try side.
  intros y12 y13.
  eapply seg_DB_C. all: try side. all: try side.
  intros y1 y9 y10 y11 y12' y13'.
  eapply seg_DB_D. all: try side. all: try side.
  intros u5 u6 u7 u11 u12 u13 u14 u15 u16 u17 u23 u28 u29 u30 u31 m1 E23 MU1 WM1 MI1 ST1 HFR1 HM1 HS1 HB1 HW1.
  subst u23.
  assert (W1 : munch dn_W m m1).
  { eapply munch_weaken; [|exact MU1]. unfold sub_fp, dn_W. intros x. cbn [outside]. intros (H1 & H2 & _).
    repeat split; try exact I; lia. }
  assert (HS81 : rw_cells rsegs m1 (bv_unsigned sp + 8) [CB 24 junk8]).
  { eapply rw_cells_transport; [exact HS8 | exact MU1 | exact WM1 |]. cbn [disjoint_from cells_size csize].
    split; [lia | split; [lia | exact I]]. }
  pose proof (dn_free_k_shift m m1 W1 WM1 KF) as KF1.
  change (Z_to_bv 64 (if inspect_wf len fr && ((0 <? nch) && (0 <? ns) && (nch * ns <? 481)) then 1 else 0))
    with (Z_to_bv 64 (pokz len fr nch ns)).
  destruct (decode_ok len fr nch ns) eqn:OK.
  - destruct (decode_ok_facts len fr nch ns OK) as (L1492 & P1 & P2 & P3 & P4 & PO & PK).
    eapply seg_DT_branch with (r := ns). all: try exact HS1. all: try side.
    + intros _ Hns12.
      exact (KC OK Hns12 (Z_to_bv 64 (wfz len fr)) y9 u5 u6 u7 u14 u15 u16 u17 u28 u29 u30 u31 m1 W1 WM1 MI1 ST1
        HFR1 HM1 HS1 HS81 HB1 HW1).
    + intros _ Hns12 y11'. apply (dn_braid_tail m1); assumption.
    + intros Hr. exfalso. lia.
  - eapply seg_DT_branch with (r := -1). all: try exact HS1. all: try side.
    + intros Hr. exfalso. lia.
    + intros Hr. exfalso. lia.
    + intros _. apply (dn_plain_tail m1 (repeat FILL (Z.to_nat (fd_olen nch ns)))); try assumption.
      apply rw_of_wr; [rewrite Z2Nat.id by lia; exact HW1 | apply repeat_length | exact HB1].
Qed.

End DM.
