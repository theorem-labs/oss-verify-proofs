From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Lib Require Import Tac Bytes.
From OSSVerify.Proofs.libreac.fuzz_decode.lib Require Import Img0.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Prog Require Import ReacDecodeLib SlotLoops SlotDown SlotCmp
  reac_frame_inspect_c memset_c reac_decode_plain_le_c bcmp_c.
Import ListNotations.
Open Scope Z_scope.

Definition pokz (len : Z) (bs : list byte) (nch ns : Z) : Z :=
  if inspect_wf len bs && ((0 <? nch) && (0 <? ns) && (nch * ns <? 481)) then 1 else 0.

Lemma pokz_plain_ok : forall len bs nch ns,
  inspect_wf len bs && ((0 <? nch) && (0 <? ns) && (nch * ns <? 481)) = plain_ok len bs nch ns.
Proof.
  intros. unfold plain_ok. replace (nch * ns <? 481) with (nch * ns <=? 480)
    by (destruct (Z.leb_spec (nch * ns) 480); destruct (Z.ltb_spec (nch * ns) 481); try reflexivity; lia).
  destruct (inspect_wf len bs), (0 <? nch), (0 <? ns), (nch * ns <=? 480); reflexivity.
Qed.

Lemma plain_ok_spec' : forall len bs nch ns,
  plain_ok len bs nch ns = true <-> inspect_wf len bs = true /\ 0 < nch /\ 0 < ns /\ nch * ns <= 480.
Proof. intros. unfold plain_ok. rewrite !andb_true_iff, !Z.ltb_lt, Z.leb_le. tauto. Qed.

Section DT.
Context (IMS : memset_contract) (IPL : reac_decode_plain_le_contract) (BC : bcmp_contract).
Variables (x3 x4 x21 x24 x27 sp : word) (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
  (Q : machine_state -> Prop) (mode nch ns out frame len lo : Z) (fr junk junk8 : list byte).
Let olen := fd_olen nch ns.
Hypothesis Hnch : -128 <= nch <= 127.
Hypothesis Hns : -128 <= ns <= 127.
Hypothesis HM : bytes_at rsegs m (mode + 4) (le4 (Z_to_bv 64 nch) ++ le4 (Z_to_bv 64 ns)).
Hypothesis HS8 : rw_cells rsegs m (bv_unsigned sp + 8) [CB 24 junk8].
Hypothesis HS : rw_cells rsegs m (bv_unsigned sp + 32) [C8 (Z_to_bv 64 nch)].
Hypothesis HFR : bytes_at rsegs m frame fr.
Hypothesis HLEN : Z.of_nat (length fr) = len.
Hypothesis HLB : 0 <= len < 2^26.
Hypothesis HO : rw_cells rsegs m out [CB (Z.to_nat olen) junk].
Hypothesis HOP : 0 < out.
Hypothesis HOE : out + fd_olen nch ns < 2^64.
Hypothesis HFP : 0 < frame < 2^63.
Hypothesis HMP : 0 <= mode.
Hypothesis ST : stk rsegs m lo (bv_unsigned sp).
Hypothesis LO : lo + 32 <= bv_unsigned sp.
Hypothesis DOF : out + olen <= frame \/ frame + len <= out.
Hypothesis DOS : out + olen <= lo \/ bv_unsigned sp + 40 <= out.
Hypothesis DOM : out + olen <= mode + 4 \/ mode + 12 <= out.
Hypothesis DFS : frame + len + 8 <= lo \/ bv_unsigned sp + 40 <= frame.
Hypothesis DMS : mode + 12 <= lo \/ bv_unsigned sp + 40 <= mode + 4.
Hypothesis MI : mem_inv rsegs m.

Lemma seg_DT_plain : forall (y1 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 : word),
  (forall (z5 z6 z7 z9 z11 z12 z13 z14 z15 z16 z17 z18 z21 z22 z23 z24 z27 z28 z29 z30 z31 : word)
     (m' : word -> option byte),
     munch [(bv_unsigned sp - 32, bv_unsigned sp); (bv_unsigned sp + 8, bv_unsigned sp + 32); (out, out + olen)] m m' ->
     wmono rsegs m m' -> mem_inv rsegs m' -> bytes_at rsegs m' frame fr -> stk rsegs m' lo (bv_unsigned sp) ->
     evt rsegs Q (MS (mkR (Z_to_bv 64 0x130fc) sp x3 x4 z5 z6 z7 (Z_to_bv 64 (frame + 50)) z9 (Z_to_bv 64 out)
       z11 z12 z13 z14 z15 z16 z17 z18 (Z_to_bv 64 out) (Z_to_bv 64 ns) z21 z22 z23 z24 (Z_to_bv 64 len)
       (Z_to_bv 64 frame) z27 z28 z29 z30 z31) F (Z_to_bv 64 0x14684) fc None m' (seg_rom rsegs))) ->
  evt rsegs Q (MS (mkR y1 sp x3 x4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16 y17 (Z_to_bv 64 mode) (Z_to_bv 64 out)
     (Z_to_bv 64 ns) x21 (Z_to_bv 64 olen) (Z_to_bv 64 (pokz len fr nch ns)) x24 (Z_to_bv 64 len) (Z_to_bv 64 frame) x27
     y28 y29 y30 y31) F (Z_to_bv 64 0x12fec) fc None m (seg_rom rsegs)).
Proof.
  intros y1 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 CONT.
  pose proof (bytes_at_bound _ _ _ _ HFR) as HFB. rewrite HLEN in HFB.
  pose proof (bytes_at_bound _ _ _ _ HM) as HMB. rewrite length_app, length_le4 in HMB.
  pose proof (u64_range sp) as Rsp.
  pose proof (rw_cells_bound _ _ _ _ HO) as HOB. cbn [cells_size csize Nat.add] in HOB.
  assert (OL : 1 <= olen) by (unfold olen, fd_olen; destruct ((0 <? nch) && (0 <? ns)) eqn:E;
    [rewrite andb_true_iff, !Z.ltb_lt in E; nia | lia]).
  rewrite ?Nat.add_0_r in HOB. rewrite Z2Nat.id in HOB by lia.
  do 4 step.
  eapply evt_cut; [eapply (IMS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ junk) |].
  { rewrite !unsigned_lit by lia. exact HO. }
  { exact MI. }
  intros ms' (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m1
    & -> & MU1 & WM1 & MI1 & HO1).
  replace (ret_pc (Z_to_bv 64 0x12ffc)) with (Z_to_bv 64 0x12ffc) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
  rewrite !unsigned_lit in MU1, HO1 by lia.
  assert (HFR1 : bytes_at rsegs m1 frame fr).
  { eapply bytes_at_transport; [exact HFR | exact MU1 |]. cbn [disjoint_from]. rewrite HLEN. split; [lia | exact I]. }
  assert (HM1 : bytes_at rsegs m1 (mode + 4) (le4 (Z_to_bv 64 nch) ++ le4 (Z_to_bv 64 ns))).
  { eapply bytes_at_transport; [exact HM | exact MU1 |]. cbn [disjoint_from]. rewrite length_app, length_le4.
    split; [cbn; lia | exact I]. }
  assert (HS1 : rw_cells rsegs m1 (bv_unsigned sp + 32) [C8 (Z_to_bv 64 nch)]).
  { eapply rw_cells_transport; [exact HS | exact MU1 | exact WM1 |]. cbn [disjoint_from cells_size csize]. split; [lia | exact I]. }
  assert (HS81 : rw_cells rsegs m1 (bv_unsigned sp + 8) [CB 24 junk8]).
  { eapply rw_cells_transport; [exact HS8 | exact MU1 | exact WM1 |]. cbn [disjoint_from cells_size csize]. split; [lia | exact I]. }
  assert (ST1 : stk rsegs m1 lo (bv_unsigned sp)).
  { eapply stk_transport_disjoint; [exact ST | exact MU1 | exact WM1 |]. cbn [disjoint_from]. split; [lia | exact I]. }
  do 5 step.
  eapply evt_cut.
  { eapply (IPL _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m1 fr frame mode out nch ns lo);
      first [ reflexivity | lia | exact HM1 | exact ST1 | idtac ].
    - intros L. rewrite unsigned_lit in L by lia. split; [lia | exact HFR1].
    - intros L. rewrite unsigned_lit in L by lia. lia.
    - intros OK. rewrite unsigned_lit in OK by lia.
      assert (E : fd_olen nch ns = 3 * nch * ns).
      { apply plain_ok_spec' in OK. unfold fd_olen.
        rewrite (proj2 (Z.ltb_lt 0 nch)), (proj2 (Z.ltb_lt 0 ns)) by lia. reflexivity. }
      assert (L : len = 1492) by (apply plain_ok_spec' in OK; destruct OK as [OK _]; apply inspect_wf_spec in OK; lia).
      rewrite <- E.
      destruct HO1 as [_ HW1]. cbn [cells_size csize] in HW1. rewrite Nat.add_0_r, Z2Nat.id in HW1 by lia.
      split; [exact HW1 | lia]. }
  intros ms' (t0'' & a1'' & a2'' & a3'' & a4'' & a5'' & a6'' & a7'' & m2 & -> & WM2 & ST2 & MU2).
  replace (ret_pc (Z_to_bv 64 0x13010)) with (Z_to_bv 64 0x13010) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
  rewrite (unsigned_lit len) in MU2 |- * by lia.
  assert (MU2w : munch [(bv_unsigned sp - 32, bv_unsigned sp); (out, out + olen)] m1 m2).
  { destruct (plain_ok len fr nch ns) eqn:OK.
    - destruct MU2 as [MU2 _].
      assert (E : fd_olen nch ns = 3 * nch * ns).
      { apply plain_ok_spec' in OK. unfold fd_olen.
        rewrite (proj2 (Z.ltb_lt 0 nch)), (proj2 (Z.ltb_lt 0 ns)) by lia. reflexivity. }
      unfold olen. rewrite E. exact MU2.
    - eapply munch_weaken; [|exact MU2]. intros x Hx. cbn [outside] in *. tauto. }
  assert (MI2 : mem_inv rsegs m2).
  { eapply mem_inv_munch; [exact MI1 | exact MU2w |]. intros x Hx.
    pose proof (u64_range x) as Rx.
    assert (C : (bv_unsigned sp - 32 <= bv_unsigned x < bv_unsigned sp) \/ (out <= bv_unsigned x < out + olen)).
    { destruct (Z_le_dec (bv_unsigned sp - 32) (bv_unsigned x)); destruct (Z_lt_dec (bv_unsigned x) (bv_unsigned sp));
        destruct (Z_le_dec out (bv_unsigned x)); destruct (Z_lt_dec (bv_unsigned x) (out + olen));
        first [ lia | exfalso; apply Hx; repeat split; first [ exact I | lia ] ]. }
    destruct C as [X1|X1].
    - destruct ST1 as (_ & _ & STw). replace x with (wa (bv_unsigned x)) by (apply wa_of_var; reflexivity).
      exact (proj1 (STw (bv_unsigned x) ltac:(lia))).
    - destruct HO1 as [_ (_ & _ & HW1)]. cbn [cells_size csize] in HW1. rewrite Nat.add_0_r, Z2Nat.id in HW1 by lia.
      replace x with (wa (out + (bv_unsigned x - out))) by (apply wa_of_var; lia).
      apply HW1. lia. }
  assert (HFR2 : bytes_at rsegs m2 frame fr).
  { eapply bytes_at_transport; [exact HFR1 | exact MU2w |]. cbn [disjoint_from]. rewrite HLEN.
    split; [lia|]. split; [lia | exact I]. }
  assert (HS2 : rw_cells rsegs m2 (bv_unsigned sp + 32) [C8 (Z_to_bv 64 nch)]).
  { eapply rw_cells_transport; [exact HS1 | exact MU2w | exact WM2 |]. cbn [disjoint_from cells_size csize].
    split; [lia|]. split; [lia | exact I]. }
  assert (HS82 : rw_cells rsegs m2 (bv_unsigned sp + 8) [CB 24 junk8]).
  { eapply rw_cells_transport; [exact HS81 | exact MU2w | exact WM2 |]. cbn [disjoint_from cells_size csize].
    split; [lia|]. split; [lia | exact I]. }
  assert (MU02 : munch [(bv_unsigned sp - 32, bv_unsigned sp); (bv_unsigned sp + 8, bv_unsigned sp + 32); (out, out + olen)] m m2).
  { eapply munch_trans; [eapply munch_weaken; [|exact MU1] | eapply munch_weaken; [|exact MU2w]];
      intros x Hx; cbn [outside] in *; tauto. }
  assert (WM02 : wmono rsegs m m2) by (eapply wmono_trans; [exact WM1 | exact WM2]).
  step. step. step.
  unfold pokz. rewrite ex_H4, pokz_plain_ok, bv_eqb_refl. cbn [negb].
  step. rewrite bv_lts_zero_r.
  destruct (plain_ok len fr nch ns) eqn:OK.
  - pose proof OK as OK'. apply plain_ok_spec' in OK'.
    assert (L : len = 1492) by (destruct OK' as [W _]; apply inspect_wf_spec in W; lia).
    rewrite unsigned_lit by lia. replace (2 ^ 63 <=? ns) with false by (symmetry; apply Z.leb_gt; lia).
    cbn [negb].
    destruct MU2 as [_ BO2].
    step. step. rewrite lts0_lit by lia. rewrite (proj2 (Z.ltb_lt 0 ns)) by lia. cbn [negb].
    step. step. rewrite lts0_lit by lia. rewrite (proj2 (Z.ltb_lt 0 nch)) by lia. cbn [negb].
    assert (EO : olen = 3 * nch * ns) by (unfold olen, fd_olen;
      rewrite (proj2 (Z.ltb_lt 0 nch)), (proj2 (Z.ltb_lt 0 ns)) by lia; reflexivity).
    eapply (cmp_entry BC) with (m := m2) (Q := Q) (out := out) (frame := frame) (nch := nch) (ns := ns) (len := len)
      (fr := fr) (junk := junk8); first [ eassumption | lia | idtac ].
    intros mk' z1 z5 z6 z7 z9 z10 z11 z12 z13 z14 z15 z16 z17 z18 z21 z22 z23 z27 z28 z29 z30 z31 IC.
    destruct IC as (_ & ICF & _ & _ & ICMI & ICMU & ICWM).
    step. step.
    eapply CONT; try eassumption.
    all: first [ eapply munch_trans; [exact MU02 | eapply munch_weaken; [|exact ICMU]]; intros x Hx; cbn [outside] in *; tauto
               | eapply wmono_trans; [exact WM02 | exact ICWM]
               | eapply stk_transport_disjoint; [exact ST2 | exact ICMU | exact ICWM |]; cbn [disjoint_from]; split; [lia | exact I] ].
  - replace (bv_unsigned (Z_to_bv 64 (-1))) with (2 ^ 64 - 1) by reflexivity.
    replace (2 ^ 63 <=? 2 ^ 64 - 1) with true by reflexivity. cbn [negb].
    assert (BF : bytes_at rsegs m2 out (repeat FILL (Z.to_nat olen))).
    { eapply bytes_at_transport; [| exact MU2 |].
      - destruct HO1 as [(_ & HB1) _]. cbn [cells_bytes cbytes] in HB1. rewrite app_nil_r in HB1.
        replace (Z_to_bv 8 (165 mod 256)) with FILL in HB1 by reflexivity. exact HB1.
      - cbn [disjoint_from]. rewrite repeat_length, Z2Nat.id by lia. split; [lia | exact I]. }
    eapply (chg_down2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m2 Q out olen BF OL ltac:(lia)
      ltac:(lia) eq_refl eq_refl).
    intros y14'.
    step. step.
    replace (bv_lts (Z_to_bv 64 0) (Z_to_bv 64 (-1))) with false by reflexivity. cbn [negb].
    step. step.
    eapply CONT; try eassumption.
Qed.

End DT.
