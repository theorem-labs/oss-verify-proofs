From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Lib Require Import Tac Bytes ZBridge.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.U Require Import Img0.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.U.Prog Require Import ReacDecodeLib reac_frame_inspect_c
  reac_decode_c reac_decode reac_decode_plain_le_c reac_decode_plain_le bcmp_c memset_c check_braid_c
  fd_up_evt fd_down_q fd_down_b1.
Import ListNotations.
Open Scope Z_scope.

Lemma ub_decode_facts : forall len bs nch ns, decode_ok len bs nch ns = true ->
  len = 1492 /\ 0 < nch /\ nch mod 2 = 0 /\ 0 < ns /\ nch * ns <= 480 /\ fd_olen nch ns = 3 * nch * ns /\
  pokz len bs nch ns = 1.
Proof.
  intros len bs nch ns H. apply decode_ok_spec in H.
  destruct H as (W & H1 & H2 & H3 & H4). pose proof W as W'.
  unfold inspect_wf in W'. rewrite !andb_true_iff, !Z.eqb_eq in W'.
  split; [tauto|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|].
  split; [unfold fd_olen; rewrite (proj2 (Z.ltb_lt 0 nch)), (proj2 (Z.ltb_lt 0 ns)) by lia; reflexivity|].
  unfold pokz. rewrite W, (proj2 (Z.ltb_lt 0 nch)), (proj2 (Z.ltb_lt 0 ns)), (proj2 (Z.ltb_lt (nch * ns) 481)) by lia.
  reflexivity.
Qed.

Lemma ub_pokz : forall len bs nch ns, pokz len bs nch ns = if plain_ok len bs nch ns then 1 else 0.
Proof.
  intros. unfold pokz, plain_ok. replace (nch * ns <? 481) with (nch * ns <=? 480)
    by (destruct (Z.leb_spec (nch * ns) 480); destruct (Z.ltb_spec (nch * ns) 481); try reflexivity; lia).
  destruct (inspect_wf len bs), (0 <? nch), (0 <? ns), (nch * ns <=? 480); reflexivity.
Qed.

Lemma ub_plain_facts : forall len bs nch ns, plain_ok len bs nch ns = true ->
  len = 1492 /\ 0 < nch /\ 0 < ns /\ nch * ns <= 480 /\ fd_olen nch ns = 3 * nch * ns.
Proof.
  intros len bs nch ns H. apply plain_ok_spec in H. destruct H as (W & H1 & H2 & H3).
  unfold inspect_wf in W. rewrite !andb_true_iff, !Z.eqb_eq in W.
  split; [tauto|]. split; [lia|]. split; [lia|]. split; [lia|].
  unfold fd_olen; rewrite (proj2 (Z.ltb_lt 0 nch)), (proj2 (Z.ltb_lt 0 ns)) by lia; reflexivity.
Qed.

Lemma ub_lt12 : forall ns, -128 <= ns <= 127 -> bv_lts (Z_to_bv 64 12) (Z_to_bv 64 ns) = (12 <? ns).
Proof.
  intros ns Hns. unfold bv_lts. rewrite !Z_to_bv_signed. unfold bv_swrap, bv_wrap.
  change (bv_half_modulus 64) with (2^63). change (bv_modulus 64) with (2^64).
  rewrite !Z.mod_small by lia. f_equal; lia.
Qed.

Lemma ub_lor_ones : forall w : word, Z_to_bv 64 (Z.lor 18446744073709551615 (bv_unsigned w)) = Z_to_bv 64 (-1).
Proof.
  intros w. pose proof (u64_range w) as R.
  replace (Z.lor 18446744073709551615 (bv_unsigned w)) with 18446744073709551615.
  - apply bv_eq. vm_compute. reflexivity.
  - symmetry. change 18446744073709551615 with (Z.ones 64). rewrite Z.lor_comm.
    apply Z.lor_ones_low; [lia|].
    destruct (Z.eq_dec (bv_unsigned w) 0) as [Z0|Z0]; [rewrite Z0; cbn; lia|].
    apply Z.log2_lt_pow2; lia.
Qed.

Section UT.
Context (ICB : check_braid_contract) (IMS : memset_contract) (IPL : reac_decode_plain_le_contract)
  (BC : bcmp_contract).
Variables (x3 x4 sp : word) (F : bvmap 5 word) (fc : bv 32) (Q : machine_state -> Prop)
  (mode nch ns out frame len lo : Z) (fr : list byte).
Hypothesis Hnch : -128 <= nch <= 127.
Hypothesis Hns : -128 <= ns <= 127.
Hypothesis HLEN : Z.of_nat (length fr) = len.
Hypothesis HLB : 0 <= len < 2^26.
Hypothesis HOP : 4096 <= out < 2^60.
Hypothesis HFP : 4096 <= frame < 2^60.
Hypothesis HMP : 0 <= mode < 2^60.
Hypothesis HMA : mode <> 0 /\ mode mod 4 = 0.
Hypothesis LO : lo + 4096 <= bv_unsigned sp.
Hypothesis DOF : out + fd_olen nch ns <= frame \/ frame + len <= out.
Hypothesis DOS : out + fd_olen nch ns <= lo.
Hypothesis DOM : out + fd_olen nch ns <= mode + 4 \/ mode + 12 <= out.
Hypothesis DFS : frame + len + 1500 <= lo.
Hypothesis DMS : mode + 12 <= lo \/ bv_unsigned sp + 56 <= mode + 4.

Definition dt_W : list (Z * Z) := [(lo, bv_unsigned sp + 56); (out, out + fd_olen nch ns)].

Definition dt_free_k (m : word -> option byte) : Prop :=
  forall (z5 z6 z7 z9 z11 z12 z13 z14 z15 z16 z17 z19 z20 z21 z22 z23 z24 z26 z27 z28 z29 z30 z31 : word)
    (m' : word -> option byte),
    munch dt_W m m' -> wmono rsegs m m' -> mem_inv rsegs m' -> bytes_at rsegs m' frame fr ->
    stk rsegs m' lo (bv_unsigned sp) ->
    evt rsegs Q (MS (mkR (Z_to_bv 64 0x13298) sp x3 x4 z5 z6 z7 (Z_to_bv 64 len) z9 (Z_to_bv 64 out) z11 z12 z13
      z14 z15 z16 z17 (Z_to_bv 64 (frame + 50)) z19 z20 z21 z22 z23 z24 (Z_to_bv 64 frame) z26 z27 z28 z29 z30 z31)
      F (Z_to_bv 64 0x14cb4) fc None m' (seg_rom rsegs)).

Definition dt_crt_k (m : word -> option byte) : Prop :=
  decode_ok len fr nch ns = true -> ns <= 12 ->
  forall (u5 u6 u7 u8 u14 u15 u16 u17 u20 u21 u26 u27 u28 u29 u30 u31 : word),
    evt rsegs Q (MS (mkR (Z_to_bv 64 0x13124) sp x3 x4 u5 u6 u7 u8 (Z_to_bv 64 len) (Z_to_bv 64 (frame + 50))
      (Z_to_bv 64 out) (Z_to_bv 64 nch) (Z_to_bv 64 ns) u14 u15 u16 u17 (Z_to_bv 64 (frame + 50))
      (Z_to_bv 64 mode) u20 u21 (Z_to_bv 64 out) (Z_to_bv 64 (fd_olen nch ns))
      (Z_to_bv 64 (pokz len fr nch ns)) (Z_to_bv 64 frame) u26 u27 u28 u29 u30 u31)
      F (Z_to_bv 64 0x134e4) fc None m (seg_rom rsegs)).

Lemma dt_free_k_shift : forall m m1, munch dt_W m m1 -> wmono rsegs m m1 -> dt_free_k m -> dt_free_k m1.
Proof.
  intros m m1 MU WM K z5 z6 z7 z9 z11 z12 z13 z14 z15 z16 z17 z19 z20 z21 z22 z23 z24 z26 z27 z28 z29 z30 z31
    m' MU' WM'.
  apply K; [exact (munch_trans _ _ _ _ MU MU') | exact (wmono_trans _ _ _ _ WM WM')].
Qed.

Lemma dt_olen1 : 1 <= fd_olen nch ns.
Proof. unfold fd_olen. destruct ((0 <? nch) && (0 <? ns)) eqn:E; [rewrite andb_true_iff, !Z.ltb_lt in E; nia | lia]. Qed.

Local Notation CELLS m junk := (rw_cells rsegs m (bv_unsigned sp + 8)
  [C8 (Z_to_bv 64 len); C8 (Z_to_bv 64 frame); CB 16 junk; C8 (Z_to_bv 64 nch); C8 (Z_to_bv 64 ns)]).

Lemma dt_tail : forall (m : word -> option byte) (junk jo : list byte)
    (y1 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16 y17 y20 y21 y26 y27 y28 y29 y30 y31 : word),
  bytes_at rsegs m (mode + 4) (le4 (Z_to_bv 64 nch) ++ le4 (Z_to_bv 64 ns)) -> CELLS m junk ->
  bytes_at rsegs m frame fr -> rw_cells rsegs m out [CB (Z.to_nat (fd_olen nch ns)) jo] ->
  stk rsegs m lo (bv_unsigned sp) -> mem_inv rsegs m -> dt_free_k m ->
  evt rsegs Q (MS (mkR y1 sp x3 x4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16 y17 (Z_to_bv 64 (frame + 50))
    (Z_to_bv 64 mode) y20 y21 (Z_to_bv 64 out) (Z_to_bv 64 (fd_olen nch ns)) (Z_to_bv 64 (pokz len fr nch ns))
    (Z_to_bv 64 frame) y26 y27 y28 y29 y30 y31) F (Z_to_bv 64 0x13158) fc None m (seg_rom rsegs)).
Proof.
  intros m junk jo y1 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16 y17 y20 y21 y26 y27 y28 y29 y30 y31
    HM HS HFR HO ST MI K.
  pose proof (bytes_at_bound _ _ _ _ HFR) as HFB. rewrite HLEN in HFB.
  pose proof (bytes_at_bound _ _ _ _ HM) as HMB. rewrite length_app, !length_le4 in HMB.
  pose proof (u64_range sp) as Rsp.
  pose proof (rw_cells_bound _ _ _ _ HS) as HSB. cbn [cells_size csize Nat.add] in HSB.
  pose proof dt_olen1 as OL.
  do 4 step.
  eapply evt_cut; [eapply (IMS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ jo) |].
  { rewrite !unsigned_lit by lia. exact HO. }
  { exact MI. }
  intros ms' (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m1
    & -> & MU1 & WM1 & MI1 & HO1).
  replace (ret_pc (Z_to_bv 64 0x13168)) with (Z_to_bv 64 0x13168) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
  rewrite !unsigned_lit in MU1, HO1 by lia.
  assert (HFR1 : bytes_at rsegs m1 frame fr).
  { eapply bytes_at_transport; [exact HFR | exact MU1 |]. cbn [disjoint_from]. rewrite HLEN. split; [lia | exact I]. }
  assert (HM1 : bytes_at rsegs m1 (mode + 4) (le4 (Z_to_bv 64 nch) ++ le4 (Z_to_bv 64 ns))).
  { eapply bytes_at_transport; [exact HM | exact MU1 |]. cbn [disjoint_from]. rewrite length_app, length_le4.
    split; [cbn; lia | exact I]. }
  assert (HS1 : CELLS m1 junk).
  { eapply rw_cells_transport; [exact HS | exact MU1 | exact WM1 |]. cbn [disjoint_from cells_size csize Nat.add].
    split; [lia | exact I]. }
  assert (ST1 : stk rsegs m1 lo (bv_unsigned sp)).
  { eapply stk_transport_disjoint; [exact ST | exact MU1 | exact WM1 |]. cbn [disjoint_from]. split; [lia | exact I]. }
  clear HS HM HFR.
  do 6 step.
  eapply evt_cut.
  { eapply (IPL _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m1 fr frame mode out nch ns lo).
    all: lazymatch goal with
         | |- bytes_at _ _ (mode + 4) _ => exact HM1
         | |- stk _ _ _ _ => exact ST1
         | |- _ = Z_to_bv 64 _ => reflexivity
         | |- inspect_wf _ _ = true -> _ => intros _; exact HMA
         | |- bv_unsigned _ = 1492 -> length _ = 1492%nat /\ _ =>
             intros L; rewrite unsigned_lit in L by lia; split; [lia | exact HFR1]
         | |- plain_ok _ _ _ _ = true -> wr_at _ _ _ _ /\ _ =>
             intros OK; rewrite unsigned_lit in OK by lia;
             destruct (ub_plain_facts _ _ _ _ OK) as (L & P1 & P2 & P3 & E);
             rewrite <- E; destruct HO1 as [_ HW1]; cbn [cells_size csize] in HW1;
             rewrite Nat.add_0_r, Z2Nat.id in HW1 by lia; split; [exact HW1 | lia]
         | _ => first [ lia | (intros _; lia) ]
         end. }
  intros ms' (t0'' & t1'' & t2'' & a1'' & a2'' & a3'' & a4'' & a5'' & a6'' & a7'' & t3'' & t4'' & m2
    & -> & WM2 & ST2 & MU2).
  replace (ret_pc (Z_to_bv 64 0x13180)) with (Z_to_bv 64 0x13180) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
  rewrite (unsigned_lit len) in MU2 |- * by lia.
  assert (MU2w : munch [(bv_unsigned sp - 32, bv_unsigned sp); (out, out + fd_olen nch ns)] m1 m2).
  { destruct (plain_ok len fr nch ns) eqn:OK.
    - destruct MU2 as [MU2 _]. destruct (ub_plain_facts _ _ _ _ OK) as (_ & _ & _ & _ & E). rewrite E. exact MU2.
    - eapply munch_weaken; [|exact MU2]. intros x Hx. cbn [outside] in *. tauto. }
  assert (MI2 : mem_inv rsegs m2).
  { eapply ub_mem_inv_munch; [exact MI1 | exact MU2w |]. intros x Hx.
    pose proof (u64_range x) as Rx.
    assert (C : (bv_unsigned sp - 32 <= bv_unsigned x < bv_unsigned sp) \/
                (out <= bv_unsigned x < out + fd_olen nch ns)).
    { destruct (Z_le_dec (bv_unsigned sp - 32) (bv_unsigned x)); destruct (Z_lt_dec (bv_unsigned x) (bv_unsigned sp));
        destruct (Z_le_dec out (bv_unsigned x)); destruct (Z_lt_dec (bv_unsigned x) (out + fd_olen nch ns));
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
  assert (HS2 : CELLS m2 junk).
  { eapply rw_cells_transport; [exact HS1 | exact MU2w | exact WM2 |]. cbn [disjoint_from cells_size csize Nat.add].
    split; [lia|]. split; [lia | exact I]. }
  assert (MU02 : munch dt_W m m2).
  { eapply munch_trans; [eapply munch_weaken; [|exact MU1] | eapply munch_weaken; [|exact MU2w]];
      unfold dt_W; intros x; cbn [outside]; intros (H1 & H2 & _); repeat split; try exact I; lia. }
  assert (WM02 : wmono rsegs m m2) by (eapply wmono_trans; [exact WM1 | exact WM2]).
  pose proof (dt_free_k_shift m m2 MU02 WM02 K) as K2.
  clear K MU02 HS1 HM1 HFR1 ST1.
  rewrite ub_pokz.
  destruct (plain_ok len fr nch ns) eqn:OK.
  - destruct MU2 as [_ BO2].
    destruct (ub_plain_facts _ _ _ _ OK) as (L & P1 & P2 & P3 & E).
    assert (HL : length fr = 1492%nat) by lia.
    st. st. st. st.
    rewrite Z.lor_0_l, bv_eqb_refl. cbn [negb].
    step. rewrite bv_lts_zero_r, unsigned_lit by lia.
    replace (2 ^ 63 <=? ns) with false by (symmetry; apply Z.leb_gt; lia). cbn [negb].
    step. rewrite lts0_lit by lia. rewrite (proj2 (Z.ltb_lt 0 ns)) by lia. cbn [negb].
    eapply (ucmp_entry BC) with (m := m2) (junk := junk) (len := len) (fr := fr) (nch := nch) (ns := ns)
      (out := out) (frame := frame).
    all: lazymatch goal with
         | |- forall _, _ => idtac
         | _ => first [ eassumption | lia ]
         end.
    intros mk' z5 z6 z7 z9 z11 z12 z13 z14 z15 z16 z17 z19 z20 z21 z23 z24 z26 z27 z28 z29 z30 z31 MUk WMk MIk HFk.
    eapply K2; try eassumption.
    + eapply munch_weaken; [|exact MUk]. unfold dt_W. intros x; cbn [outside]; intros (H1 & H2 & _).
      repeat split; try exact I; lia.
    + eapply stk_transport_disjoint; [exact ST2 | exact MUk | exact WMk |]. cbn [disjoint_from].
      split; [lia | exact I].
  - st. st. st. st.
    rewrite ub_lor_ones, bv_eqb_refl. cbn [negb].
    step. cnd false.
    assert (BF : bytes_at rsegs m2 out (repeat FILL (Z.to_nat (fd_olen nch ns)))).
    { eapply bytes_at_transport; [| exact MU2 |].
      - destruct HO1 as [(_ & HB1) _]. cbn [cells_bytes cbytes] in HB1. rewrite app_nil_r in HB1.
        replace (Z_to_bv 8 (165 mod 256)) with FILL in HB1 by reflexivity. exact HB1.
      - cbn [disjoint_from]. rewrite repeat_length, Z2Nat.id by lia. split; [lia | exact I]. }
    eapply (ub_fill _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m2 Q out (fd_olen nch ns)
      BF OL ltac:(lia) ltac:(lia) eq_refl eq_refl).
    intros y11' y12' y13' y14'.
    step. cnd true. step. step.
    eapply K2; first [ apply munch_refl | apply wmono_refl | eassumption ].
Qed.

Lemma dt_braid : forall (m : word -> option byte) (junk : list byte)
    (y1 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16 y17 y20 y21 y26 y27 y28 y29 y30 y31 : word),
  decode_ok len fr nch ns = true ->
  bytes_at rsegs m (mode + 4) (le4 (Z_to_bv 64 nch) ++ le4 (Z_to_bv 64 ns)) -> CELLS m junk ->
  bytes_at rsegs m frame fr -> bytes_at rsegs m out (braid_out fr nch ns) -> wr_at rsegs m out (fd_olen nch ns) ->
  stk rsegs m lo (bv_unsigned sp) -> mem_inv rsegs m -> dt_free_k m ->
  evt rsegs Q (MS (mkR y1 sp x3 x4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16 y17 (Z_to_bv 64 (frame + 50))
    (Z_to_bv 64 mode) y20 y21 (Z_to_bv 64 out) (Z_to_bv 64 (fd_olen nch ns)) (Z_to_bv 64 (pokz len fr nch ns))
    (Z_to_bv 64 frame) y26 y27 y28 y29 y30 y31) F (Z_to_bv 64 0x13130) fc None m (seg_rom rsegs)).
Proof.
  intros m junk y1 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16 y17 y20 y21 y26 y27 y28 y29 y30 y31
    OK HM HS HFR HB HW ST MI K.
  destruct (ub_decode_facts len fr nch ns OK) as (L1492 & P1 & P2 & P3 & P4 & PO & PK).
  pose proof (u64_range sp) as Rsp.
  pose proof (rw_cells_bound _ _ _ _ HS) as HSB. cbn [cells_size csize Nat.add] in HSB.
  pose proof (bytes_at_bound _ _ _ _ HM) as HMB. rewrite length_app, !length_le4 in HMB.
  assert (LB : Z.of_nat (length (braid_out fr nch ns)) = 3 * nch * ns)
    by (unfold braid_out; rewrite length_mapseq, Z2Nat.id by nia; reflexivity).
  step. cnd false. step. step. step. cnd false.
  step. step. step. step. step.
  eapply evt_cut.
  { eapply (ICB _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m (frame + 50) out nch ns lo).
    all: unfold CHECK_BRAID_FRAME; try lia; try exact ST.
    apply (braid_map_up m out frame fr); [exact HB | exact HFR | nia | lia | exact P2 | lia]. }
  intros ms' (t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m'
    & -> & MU & WM & ST').
  replace (ret_pc (Z_to_bv 64 0x13154)) with (Z_to_bv 64 0x13154) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
  unfold CHECK_BRAID_FRAME in MU.
  assert (HS1 : CELLS m' junk).
  { eapply rw_cells_transport; [exact HS | exact MU | exact WM |]. cbn [disjoint_from cells_size csize Nat.add].
    split; [lia | exact I]. }
  assert (MI' : mem_inv rsegs m').
  { eapply ub_mem_inv_munch; [exact MI | exact MU |]. intros x Hx. cbn [outside] in Hx.
    pose proof (u64_range x) as Rx.
    assert (X1 : bv_unsigned sp - 96 <= bv_unsigned x < bv_unsigned sp).
    { destruct (Z_le_dec (bv_unsigned sp - 96) (bv_unsigned x)); destruct (Z_lt_dec (bv_unsigned x) (bv_unsigned sp));
        first [ lia | exfalso; apply Hx; repeat split; first [ exact I | lia ] ]. }
    destruct ST as (_ & _ & STw). replace x with (wa (bv_unsigned x)) by (apply wa_of_var; reflexivity).
    exact (proj1 (STw (bv_unsigned x) ltac:(lia))). }
  step.
  apply (dt_tail m' junk (braid_out fr nch ns)).
  - eapply bytes_at_transport; [exact HM | exact MU |]. cbn [disjoint_from]. rewrite length_app, !length_le4.
    split; [lia | exact I].
  - exact HS1.
  - eapply bytes_at_transport; [exact HFR | exact MU |]. cbn [disjoint_from]. split; [lia | exact I].
  - apply ub_rw_of_wr.
    + rewrite Z2Nat.id by (pose proof dt_olen1; lia). eapply wr_at_transport; [exact HW | exact WM].
    + unfold braid_out. rewrite length_mapseq, PO. reflexivity.
    + eapply bytes_at_transport; [exact HB | exact MU |]. cbn [disjoint_from]. rewrite LB. split; [lia | exact I].
  - exact ST'.
  - exact MI'.
  - eapply dt_free_k_shift; [| exact WM | exact K].
    eapply munch_weaken; [|exact MU]. unfold dt_W. intros x; cbn [outside]; intros (H1 & H2 & _).
    repeat split; try exact I; lia.
Qed.

Lemma dt_b0 : forall (m : word -> option byte) (junk : list byte)
    (y1 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16 y17 y20 y21 y25 y26 y27 y28 y29 y30 y31 : word),
  decode_ok len fr nch ns = true ->
  bytes_at rsegs m (mode + 4) (le4 (Z_to_bv 64 nch) ++ le4 (Z_to_bv 64 ns)) -> CELLS m junk ->
  bytes_at rsegs m frame fr -> bytes_at rsegs m out (braid_out fr nch ns) -> wr_at rsegs m out (fd_olen nch ns) ->
  stk rsegs m lo (bv_unsigned sp) -> mem_inv rsegs m -> dt_free_k m ->
  evt rsegs Q (MS (mkR y1 sp x3 x4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16 y17 (Z_to_bv 64 (frame + 50))
    (Z_to_bv 64 mode) y20 y21 (Z_to_bv 64 out) (Z_to_bv 64 (fd_olen nch ns)) (Z_to_bv 64 (pokz len fr nch ns))
    y25 y26 y27 y28 y29 y30 y31) F (Z_to_bv 64 0x13124) fc None m (seg_rom rsegs)).
Proof.
  intros m junk y1 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16 y17 y20 y21 y25 y26 y27 y28 y29 y30 y31
    OK HM HS HFR HB HW ST MI K.
  pose proof (u64_range sp) as Rsp.
  pose proof (rw_cells_bound _ _ _ _ HS) as HSB. cbn [cells_size csize Nat.add] in HSB.
  step. step.
  eapply dt_braid; eassumption.
Qed.

Lemma dt_head : forall (m : word -> option byte) (junk : list byte)
    (y1 y5 y6 y7 y8 y11 y12 y13 y14 y15 y16 y17 y18 y20 y21 y26 y27 y28 y29 y30 y31 : word),
  bytes_at rsegs m (mode + 4) (le4 (Z_to_bv 64 nch) ++ le4 (Z_to_bv 64 ns)) -> CELLS m junk ->
  bytes_at rsegs m frame fr -> bytes_at rsegs m out (dout len fr nch ns) -> wr_at rsegs m out (fd_olen nch ns) ->
  stk rsegs m lo (bv_unsigned sp) -> mem_inv rsegs m -> dt_crt_k m -> dt_free_k m ->
  evt rsegs Q (MS (mkR y1 sp x3 x4 y5 y6 y7 y8 (Z_to_bv 64 len) (Z_to_bv 64 (dres len fr nch ns)) y11 y12 y13 y14 y15
    y16 y17 y18 (Z_to_bv 64 mode) y20 y21 (Z_to_bv 64 out) (Z_to_bv 64 (fd_olen nch ns))
    (Z_to_bv 64 (pokz len fr nch ns)) (Z_to_bv 64 frame) y26 y27 y28 y29 y30 y31) F (Z_to_bv 64 0x130ec) fc None m
    (seg_rom rsegs)).
Proof.
  intros m junk y1 y5 y6 y7 y8 y11 y12 y13 y14 y15 y16 y17 y18 y20 y21 y26 y27 y28 y29 y30 y31
    HM HS HFR HB HW ST MI KC K.
  pose proof (u64_range sp) as Rsp.
  pose proof (rw_cells_bound _ _ _ _ HS) as HSB. cbn [cells_size csize Nat.add] in HSB.
  pose proof dt_olen1 as OL.
  unfold dres, dout in *.
  st.
  destruct (decode_ok len fr nch ns) eqn:OK.
  - destruct (ub_decode_facts len fr nch ns OK) as (L1492 & P1 & P2 & P3 & P4 & PO & PK).
    step. rewrite lts0_lit by lia. rewrite (proj2 (Z.ltb_lt 0 ns)) by lia. cbn [negb].
    step. step. step. rewrite ub_lt12 by lia.
    destruct (Z.ltb_spec 12 ns) as [G|G].
    + step. rewrite lts0_lit by lia. rewrite (proj2 (Z.ltb_lt 0 ns)) by lia. cbn [negb].
      eapply dt_braid; eassumption.
    + step. cnd false. step. step. step. cnd false.
      step. step. step. step. step.
      apply KC; [exact OK | lia].
  - step. cnd true. step. cnd true.
    apply (dt_tail m junk (repeat FILL (Z.to_nat (fd_olen nch ns)))); try assumption.
    apply ub_rw_of_wr; [rewrite Z2Nat.id by lia; exact HW | apply repeat_length | exact HB].
Qed.

End UT.
