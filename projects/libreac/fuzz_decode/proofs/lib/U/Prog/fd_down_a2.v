From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Lib Require Import Tac Bytes ZBridge.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.U Require Import Img0.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.U.Prog Require Import ReacDecodeLib reac_frame_inspect_c
  memset_c reac_decode_c fd_down_q fd_down_a1.
Import ListNotations.
Open Scope Z_scope.

Fixpoint ud_outside_dec (W : list (Z * Z)) (x : Z) : {outside W x} + {~ outside W x}.
Proof.
  destruct W as [|[lo hi] W].
  - left. exact I.
  - destruct (Z_le_dec lo x) as [H1|H1]; [destruct (Z_lt_dec x hi) as [H2|H2]|].
    + right. cbn. tauto.
    + destruct (ud_outside_dec W x) as [O|O]; [left; cbn; split; [lia | exact O] | right; cbn; tauto].
    + destruct (ud_outside_dec W x) as [O|O]; [left; cbn; split; [lia | exact O] | right; cbn; tauto].
Defined.

Lemma ud_mem_inv_munch : forall W m1 m2, mem_inv rsegs m1 -> munch W m1 m2 ->
  (forall x : word, ~ outside W (bv_unsigned x) -> wview rsegs m1 x <> None) -> mem_inv rsegs m2.
Proof.
  intros W m1 m2 MI MU HW a b Ha.
  destruct (ud_outside_dec W (bv_unsigned a)) as [O|O].
  - rewrite (MU a O) in Ha. exact (MI a b Ha).
  - pose proof (HW a O) as Wv. destruct (m1 a) eqn:E.
    + exact (MI a _ E).
    + exact (wview_not_ro rsegs m1 a Wv E).
Qed.

Lemma ud_decode_ok_spec : forall len bs nch ns,
  decode_ok len bs nch ns = true <->
  inspect_wf len bs = true /\ 0 < nch /\ nch mod 2 = 0 /\ 0 < ns /\ nch * ns <= 480.
Proof. intros. unfold decode_ok. rewrite !andb_true_iff, !Z.ltb_lt, Z.eqb_eq, Z.leb_le. tauto. Qed.

Lemma ud_olen_ok : forall len bs nch ns, decode_ok len bs nch ns = true -> fd_olen nch ns = 3 * nch * ns.
Proof.
  intros len bs nch ns H. rewrite ud_decode_ok_spec in H. unfold fd_olen.
  rewrite (proj2 (Z.ltb_lt 0 nch)), (proj2 (Z.ltb_lt 0 ns)) by lia. reflexivity.
Qed.

Lemma ud_rw_cells_join : forall m A cs1 cs2,
  rw_cells rsegs m A cs1 -> rw_cells rsegs m (A + Z.of_nat (cells_size cs1)) cs2 -> rw_cells rsegs m A (cs1 ++ cs2).
Proof.
  intros m A cs1 cs2 [[W1 B1] R1] [[W2 B2] R2]. split; [split|].
  - apply cells_wf_app. tauto.
  - rewrite cells_bytes_app. apply (proj2 (bytes_at_app _ _ _ _ _)). rewrite cells_bytes_length by exact W1. tauto.
  - rewrite cells_size_app. destruct R1 as (Ra & Rb & Rc). destruct R2 as (Sa & Sb & Sc).
    split; [lia|]. split; [lia|]. intros i Hi.
    destruct (Z_lt_dec i (Z.of_nat (cells_size cs1))) as [L|L].
    + apply Rc. lia.
    + replace (A + i) with (A + Z.of_nat (cells_size cs1) + (i - Z.of_nat (cells_size cs1))) by lia. apply Sc. lia.
Qed.

Lemma ud_olen_bounds : forall nch ns, -128 <= nch <= 127 -> -128 <= ns <= 127 -> 1 <= fd_olen nch ns <= 3 * 127 * 127.
Proof.
  intros nch ns H1 H2. unfold fd_olen. destruct ((0 <? nch) && (0 <? ns)) eqn:E; [|lia].
  rewrite andb_true_iff, !Z.ltb_lt in E. nia.
Qed.

Lemma ud_H1 : forall nch, bv_unsigned (v_sltiu (Z_to_bv 64 (Z.land (bv_unsigned (Z_to_bv 64 nch)) 1)) 1) =
  if nch mod 2 =? 0 then 1 else 0.
Proof.
  intros nch. unfold v_sltiu. rewrite land1. rewrite (unsigned_lit_wrap nch).
  assert (E : (nch mod 2 ^ 64) mod 2 = nch mod 2) by (Z.div_mod_to_equations; lia).
  rewrite E. pose proof (Z.mod_pos_bound nch 2 ltac:(lia)) as B.
  rewrite unsigned_lit by lia. change (bv_wrap 64 1) with 1.
  destruct (Z.eqb_spec (nch mod 2) 0) as [Z0|Z0]; [rewrite Z0; reflexivity|].
  replace (nch mod 2) with 1 by lia. reflexivity.
Qed.

Lemma ud_H2 : forall b : bool, bv_unsigned (Z_to_bv 64 (if b then 1 else 0)) = if b then 1 else 0.
Proof. intros [|]; reflexivity. Qed.

Lemma ud_H3 : forall a b : bool, Z.land (if a then 1 else 0) (if b then 1 else 0) = if a && b then 1 else 0.
Proof. intros [|] [|]; reflexivity. Qed.

Lemma ud_H4 : forall (c : bool) ns,
  Z_to_bv 64 (Z.lor (bv_unsigned (Z_to_bv 64 ((if c then 1 else 0) + -1))) (bv_unsigned (Z_to_bv 64 ns))) =
  Z_to_bv 64 (if c then ns else -1).
Proof.
  intros [|] ns.
  - change (bv_unsigned (Z_to_bv 64 (1 + -1))) with 0. rewrite Z.lor_0_l. apply Z_to_bv_bv_unsigned.
  - change (bv_unsigned (Z_to_bv 64 (0 + -1))) with (Z.ones 64).
    rewrite unsigned_lit_wrap. rewrite Z.lor_comm.
    assert (A : 0 <= ns mod 2^64 < 2^64) by (apply Z.mod_pos_bound; lia).
    rewrite Z.lor_ones_low; [apply bv_eq; vm_compute; reflexivity | lia |].
    destruct (Z.eq_dec (ns mod 2^64) 0) as [Z0|Z0]; [rewrite Z0; cbn; lia|].
    apply Z.log2_lt_pow2; lia.
Qed.

Lemma ud_s8 : forall len bs nch ns,
  Z_to_bv 64 (Z.land (bv_unsigned (Z_to_bv 64 (ud_wfz len bs))) (bv_unsigned (Z_to_bv 64 (fd_fits nch ns)))) =
  Z_to_bv 64 (pokz len bs nch ns).
Proof.
  intros. unfold ud_wfz, fd_fits, pokz.
  destruct (inspect_wf len bs), ((0 <? nch) && (0 <? ns) && (nch * ns <? 481)); reflexivity.
Qed.

Lemma ud_a1 : forall len bs nch ns,
  Z_to_bv 64 (Z.lor (bv_unsigned (Z_to_bv 64 (Z.land (bv_unsigned (Z_to_bv 64 (pokz len bs nch ns)))
    (bv_unsigned (v_sltiu (Z_to_bv 64 (Z.land (bv_unsigned (Z_to_bv 64 nch)) 1)) 1)) + -1)))
    (bv_unsigned (Z_to_bv 64 ns))) = Z_to_bv 64 (dres len bs nch ns).
Proof.
  intros len bs nch ns. rewrite ud_H1. unfold pokz. rewrite ud_H2, ud_H3, ud_H4. unfold dres.
  replace (inspect_wf len bs && ((0 <? nch) && (0 <? ns) && (nch * ns <? 481)) && (nch mod 2 =? 0))
    with (decode_ok len bs nch ns); [reflexivity|].
  unfold decode_ok. replace (nch * ns <? 481) with (nch * ns <=? 480)
    by (destruct (Z.leb_spec (nch * ns) 480); destruct (Z.ltb_spec (nch * ns) 481); try reflexivity; lia).
  destruct (inspect_wf len bs), (0 <? nch), (nch mod 2 =? 0), (0 <? ns), (nch * ns <=? 480); reflexivity.
Qed.

Section DD.
Context (IMS : memset_contract) (IDE : reac_decode_contract).
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

Lemma ud_segD : forall (m : word -> option byte) (j junk : list byte)
    (r1 r5 r6 r7 r8 r10 r11 r12 r13 r14 r15 r16 r17 r28 r29 r30 r31 : word),
  rw_cells rsegs m (Sp + 8) [C8 (Z_to_bv 64 len); C8 (Z_to_bv 64 frame); CB 16 j] ->
  rw_cells rsegs m (Sp + 40) [C8 (Z_to_bv 64 nch); C8 (Z_to_bv 64 ns)] ->
  bytes_at rsegs m frame fr -> bytes_at rsegs m (mode + 4) (le4 (Z_to_bv 64 nch) ++ le4 (Z_to_bv 64 ns)) ->
  rw_cells rsegs m out [CB (Z.to_nat (fd_olen nch ns)) junk] -> stk rsegs m lo Sp -> mem_inv rsegs m ->
  (forall (u1 u5 u6 u7 u11 u12 u13 u14 u15 u16 u17 u28 u29 u30 u31 : word) (m' : word -> option byte),
     munch [(Sp - 80, Sp); (out, out + fd_olen nch ns)] m m' -> wmono rsegs m m' -> mem_inv rsegs m' ->
     stk rsegs m' lo Sp -> bytes_at rsegs m' frame fr ->
     bytes_at rsegs m' (mode + 4) (le4 (Z_to_bv 64 nch) ++ le4 (Z_to_bv 64 ns)) ->
     rw_cells rsegs m' (Sp + 8) [C8 (Z_to_bv 64 len); C8 (Z_to_bv 64 frame); CB 16 j] ->
     rw_cells rsegs m' (Sp + 40) [C8 (Z_to_bv 64 nch); C8 (Z_to_bv 64 ns)] ->
     bytes_at rsegs m' out (dout len fr nch ns) -> wr_at rsegs m' out (fd_olen nch ns) ->
     evt rsegs Q (SU 0x130ec m' u1 u5 u6 u7 r8 (Z_to_bv 64 (dres len fr nch ns)) u11 u12 u13 u14 u15 u16 u17
       (Z_to_bv 64 (pokz len fr nch ns)) u28 u29 u30 u31)) ->
  evt rsegs Q (SU 0x13070 m r1 r5 r6 r7 r8 r10 r11 r12 r13 r14 r15 r16 r17 (Z_to_bv 64 (ud_wfz len fr))
     r28 r29 r30 r31).
Proof.
  intros m j junk r1 r5 r6 r7 r8 r10 r11 r12 r13 r14 r15 r16 r17 r28 r29 r30 r31 HS8 HS40 HFR HM HO ST MI CONT.
  pose proof (bytes_at_bound _ _ _ _ HFR) as HFB. rewrite HLEN in HFB.
  pose proof (bytes_at_bound _ _ _ _ HM) as HMB. rewrite length_app, !length_le4 in HMB.
  pose proof (rw_cells_bound _ _ _ _ HO) as HOB. cbn [cells_size csize Nat.add] in HOB.
  pose proof (ud_olen_bounds nch ns Hnch Hns) as OL.
  rewrite ?Nat.add_0_r in HOB. rewrite Z2Nat.id in HOB by lia.
  st. st. st. st.
  eapply evt_cut; [eapply IMS with (junk := junk) |].
  { rewrite !unsigned_lit by lia. exact HO. }
  { exact MI. }
  intros ms' (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m1
    & -> & MU1 & WM1 & MI1 & HO1).
  replace (ret_pc (Z_to_bv 64 0x13080)) with (Z_to_bv 64 0x13080) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
  rewrite !unsigned_lit in MU1, HO1 by lia.
  assert (HFR1 : bytes_at rsegs m1 frame fr).
  { eapply bytes_at_transport; [exact HFR | exact MU1 |]. cbn [disjoint_from]. rewrite HLEN. split; [lia | exact I]. }
  assert (HM1 : bytes_at rsegs m1 (mode + 4) (le4 (Z_to_bv 64 nch) ++ le4 (Z_to_bv 64 ns))).
  { eapply bytes_at_transport; [exact HM | exact MU1 |]. cbn [disjoint_from]. rewrite length_app, !length_le4.
    split; [cbn; lia | exact I]. }
  assert (HS81 : rw_cells rsegs m1 (Sp + 8) [C8 (Z_to_bv 64 len); C8 (Z_to_bv 64 frame); CB 16 j]).
  { eapply rw_cells_transport; [exact HS8 | exact MU1 | exact WM1 |]. cbn [disjoint_from cells_size csize Nat.add].
    split; [lia | exact I]. }
  assert (HS401 : rw_cells rsegs m1 (Sp + 40) [C8 (Z_to_bv 64 nch); C8 (Z_to_bv 64 ns)]).
  { eapply rw_cells_transport; [exact HS40 | exact MU1 | exact WM1 |]. cbn [disjoint_from cells_size csize Nat.add].
    split; [lia | exact I]. }
  assert (ST1 : stk rsegs m1 lo Sp).
  { eapply stk_transport_disjoint; [exact ST | exact MU1 | exact WM1 |]. cbn [disjoint_from]. split; [lia | exact I]. }
  clear HFR HM HS8 HS40 ST.
  st. st. st. st. st.
  eapply evt_cut.
  { eapply IDE with (bs := fr) (raw := frame) (mode := mode) (out := out) (nch := nch) (ns := ns) (lo := lo).
    all: rewrite ?unsigned_lit by lia.
    all: first [ reflexivity | lia | exact HM1 | exact ST1 | (intros; exact HMA)
               | (intros; split; [lia | exact HFR1]) | (intros; lia) | idtac ].
    intros OK. rewrite <- (ud_olen_ok _ _ _ _ OK).
    destruct HO1 as [_ HW1]. cbn [cells_size csize] in HW1. rewrite Nat.add_0_r, Z2Nat.id in HW1 by lia.
    assert (L : len = 1492) by (apply ud_decode_ok_spec in OK; destruct OK as [OK _];
      apply ud_inspect_wf_spec in OK; lia).
    split; [exact HW1|]. split; [lia|]. split; lia. }
  intros ms' (t0'' & t1'' & t2'' & a1'' & a2'' & a3'' & a4'' & a5'' & a6'' & a7'' & t3'' & t4'' & t5'' & t6'' & m2
    & -> & WM2 & ST2 & MU2).
  replace (ret_pc (Z_to_bv 64 0x13094)) with (Z_to_bv 64 0x13094) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
  rewrite (unsigned_lit len) in MU2 |- * by lia. rewrite (unsigned_lit Sp) in ST2, MU2 by lia.
  assert (MU2w : munch [(Sp - 80, Sp); (out, out + fd_olen nch ns)] m1 m2).
  { destruct (decode_ok len fr nch ns) eqn:OK.
    - destruct MU2 as [MU2 _]. rewrite (ud_olen_ok _ _ _ _ OK). exact MU2.
    - eapply munch_weaken; [|exact MU2]. intros x Hx. cbn [outside] in *. tauto. }
  assert (HS82 : rw_cells rsegs m2 (Sp + 8) [C8 (Z_to_bv 64 len); C8 (Z_to_bv 64 frame); CB 16 j]).
  { eapply rw_cells_transport; [exact HS81 | exact MU2w | exact WM2 |]. cbn [disjoint_from cells_size csize Nat.add].
    split; [lia|]. split; [lia | exact I]. }
  assert (HS402 : rw_cells rsegs m2 (Sp + 40) [C8 (Z_to_bv 64 nch); C8 (Z_to_bv 64 ns)]).
  { eapply rw_cells_transport; [exact HS401 | exact MU2w | exact WM2 |]. cbn [disjoint_from cells_size csize Nat.add].
    split; [lia|]. split; [lia | exact I]. }
  st. st. st. st. st. st. st. st.
  rewrite ud_s8. rewrite ud_a1.
  change (if decode_ok len fr nch ns then ns else -1) with (dres len fr nch ns).
  st. rewrite bv_eqb_refl. cbn [negb].
  assert (MI2 : mem_inv rsegs m2).
  { eapply ud_mem_inv_munch; [exact MI1 | exact MU2w |]. intros x Hx. cbn [outside] in Hx.
    pose proof (u64_range x) as Rx.
    assert (C : (Sp - 80 <= bv_unsigned x < Sp) \/ (out <= bv_unsigned x < out + fd_olen nch ns)).
    { destruct (Z_le_dec (Sp - 80) (bv_unsigned x)); destruct (Z_lt_dec (bv_unsigned x) Sp);
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
  assert (HM2 : bytes_at rsegs m2 (mode + 4) (le4 (Z_to_bv 64 nch) ++ le4 (Z_to_bv 64 ns))).
  { eapply bytes_at_transport; [exact HM1 | exact MU2w |]. cbn [disjoint_from]. rewrite length_app, !length_le4.
    change (Z.of_nat (4 + 4)) with 8. split; [lia|]. split; [lia | exact I]. }
  assert (MU02 : munch [(Sp - 80, Sp); (out, out + fd_olen nch ns)] m m2).
  { eapply munch_trans; [|exact MU2w]. eapply munch_weaken; [|exact MU1]. intros x Hx. cbn [outside] in *. tauto. }
  assert (WM02 : wmono rsegs m m2) by (eapply wmono_trans; [exact WM1 | exact WM2]).
  assert (HW2 : wr_at rsegs m2 out (fd_olen nch ns)).
  { destruct HO1 as [_ HW1]. cbn [cells_size csize] in HW1. rewrite Nat.add_0_r, Z2Nat.id in HW1 by lia.
    eapply wr_at_transport; [exact HW1 | exact WM2]. }
  st. rewrite bv_lts_zero_r. unfold dres in *.
  destruct (decode_ok len fr nch ns) eqn:OK.
  - pose proof OK as OK'. apply ud_decode_ok_spec in OK'.
    rewrite unsigned_lit by lia. replace (2 ^ 63 <=? ns) with false by (symmetry; apply Z.leb_gt; lia).
    cbn [negb].
    destruct MU2 as [_ BO2].
    eapply CONT; try eassumption.
    unfold dout. rewrite OK. exact BO2.
  - replace (bv_unsigned (Z_to_bv 64 (-1))) with (2 ^ 64 - 1) by reflexivity.
    replace (2 ^ 63 <=? 2 ^ 64 - 1) with true by reflexivity. cbn [negb].
    assert (BF : bytes_at rsegs m2 out (repeat FILL (Z.to_nat (fd_olen nch ns)))).
    { eapply bytes_at_transport; [| exact MU2 |].
      - destruct HO1 as [(_ & HB1) _]. cbn [cells_bytes cbytes] in HB1. rewrite app_nil_r in HB1.
        replace (Z_to_bv 8 (165 mod 256)) with FILL in HB1 by reflexivity. exact HB1.
      - cbn [disjoint_from]. rewrite repeat_length, Z2Nat.id by lia. split; [lia | exact I]. }
    eapply ud_fill with (m := m2) (out := out) (n := fd_olen nch ns).
    all: try first [ exact BF | lia ].
    intros y11 y12 y13 y14. eapply CONT; try eassumption.
    unfold dout. rewrite OK. exact BF.
Qed.

End DD.
