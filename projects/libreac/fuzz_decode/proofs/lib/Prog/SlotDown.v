From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Lib Require Import Tac Bytes.
From OSSVerify.Proofs.libreac.fuzz_decode.lib Require Import Img0.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Prog Require Import ReacDecodeLib SlotLoops
  reac_frame_inspect_c reac_frame_counter_c memset_c reac_decode_c.
Import ListNotations.
Open Scope Z_scope.

Lemma eqb_zxb' : forall (b : byte) c, 0 <= c < 2^64 -> bv_eqb (zxb b) (Z_to_bv 64 c) = (bv_unsigned b =? c).
Proof.
  intros b c Hc. pose proof (bv_unsigned_in_range 8 b) as Hb. unfold bv_modulus in Hb.
  change (2 ^ Z.of_N 8) with 256 in Hb. unfold zxb, bv_eqb. rewrite !unsigned_lit by lia. reflexivity.
Qed.

Lemma inspect_wf_spec : forall len bs, inspect_wf len bs = true <->
  len = 1492 /\ inspect_byte bs 12 = 0x88 /\ inspect_byte bs 13 = 0x19 /\
  inspect_byte bs 1490 = 0xC2 /\ inspect_byte bs 1491 = 0xEA.
Proof. intros. unfold inspect_wf. rewrite !andb_true_iff, !Z.eqb_eq. tauto. Qed.

Lemma byte_range : forall b : byte, 0 <= bv_unsigned b < 256.
Proof. intros b. pose proof (bv_unsigned_in_range 8 b) as H. unfold bv_modulus in H. exact H. Qed.

Lemma cnt_hi : forall c, 0 <= c < 2^16 ->
  Z_to_bv 64 (Z.shiftr (bv_unsigned (Z_to_bv 64 (Z.shiftl (bv_unsigned (Z_to_bv 64 (2^32 + c))) 48))) 48) = Z_to_bv 64 c.
Proof.
  intros c Hc. rewrite (unsigned_lit (2^32 + c)) by lia. rewrite Z.shiftl_mul_pow2 by lia.
  rewrite unsigned_lit_wrap. rewrite Z.shiftr_div_pow2 by lia. f_equal.
  replace ((2 ^ 32 + c) * 2 ^ 48) with (c * 2^48 + 2^16 * 2^64) by ring.
  rewrite Z.mod_add by lia. rewrite Z.mod_small by lia. apply Z.div_mul. lia.
Qed.

Lemma cnt_lo : forall b14 b15 : byte,
  Z_to_bv 64 (Z.lor (bv_unsigned (Z_to_bv 64 (Z.shiftl (bv_unsigned (zxb b15)) 8))) (bv_unsigned (zxb b14))) =
  Z_to_bv 64 (bv_unsigned b14 + 256 * bv_unsigned b15).
Proof.
  intros b14 b15. pose proof (byte_range b14). pose proof (byte_range b15).
  unfold zxb. rewrite !(unsigned_lit (bv_unsigned _)) by lia. rewrite Z.shiftl_mul_pow2 by lia.
  rewrite unsigned_lit by lia. f_equal. rewrite Z.lor_comm.
  rewrite <- (lor_shiftl8_add (bv_unsigned b14) (bv_unsigned b15)) by lia.
  rewrite Z.shiftl_mul_pow2 by lia. reflexivity.
Qed.

Lemma decode_ok_spec' : forall len bs nch ns,
  decode_ok len bs nch ns = true <->
  inspect_wf len bs = true /\ 0 < nch /\ nch mod 2 = 0 /\ 0 < ns /\ nch * ns <= 480.
Proof.
  intros. unfold decode_ok. rewrite !andb_true_iff, !Z.ltb_lt, Z.eqb_eq, Z.leb_le. tauto.
Qed.

Lemma ex_H1 : forall nch, bv_unsigned (v_sltiu (Z_to_bv 64 (Z.land (bv_unsigned (Z_to_bv 64 nch)) 1)) 1) =
  if nch mod 2 =? 0 then 1 else 0.
Proof.
  intros nch. unfold v_sltiu. rewrite land1. rewrite (unsigned_lit_wrap nch).
  assert (E : (nch mod 2 ^ 64) mod 2 = nch mod 2) by (Z.div_mod_to_equations; lia).
  rewrite E. pose proof (Z.mod_pos_bound nch 2 ltac:(lia)) as B.
  rewrite unsigned_lit by lia. change (bv_wrap 64 1) with 1.
  destruct (Z.eqb_spec (nch mod 2) 0) as [Z0|Z0]; [rewrite Z0; reflexivity|].
  replace (nch mod 2) with 1 by lia. reflexivity.
Qed.

Lemma ex_H2 : forall b : bool, bv_unsigned (Z_to_bv 64 (if b then 1 else 0)) = if b then 1 else 0.
Proof. intros [|]; reflexivity. Qed.

Lemma ex_H3 : forall a b : bool, Z.land (if a then 1 else 0) (if b then 1 else 0) = if a && b then 1 else 0.
Proof. intros [|] [|]; reflexivity. Qed.

Lemma ex_H4 : forall (c : bool) ns,
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

Fixpoint outside_dec_aux (W : list (Z * Z)) (x : Z) : {outside W x} + {~ outside W x}.
Proof.
  destruct W as [|[lo hi] W].
  - left. exact I.
  - destruct (Z_le_dec lo x) as [H1|H1]; [destruct (Z_lt_dec x hi) as [H2|H2]|].
    + right. cbn. tauto.
    + destruct (outside_dec_aux W x) as [O|O]; [left; cbn; split; [lia | exact O] | right; cbn; tauto].
    + destruct (outside_dec_aux W x) as [O|O]; [left; cbn; split; [lia | exact O] | right; cbn; tauto].
Defined.

Definition outside_dec := outside_dec_aux.

Lemma mem_inv_munch : forall W m1 m2, mem_inv rsegs m1 -> munch W m1 m2 ->
  (forall x : word, ~ outside W (bv_unsigned x) -> wview rsegs m1 x <> None) -> mem_inv rsegs m2.
Proof.
  intros W m1 m2 MI MU HW a b Ha.
  destruct (outside_dec W (bv_unsigned a)) as [O|O].
  - rewrite (MU a O) in Ha. exact (MI a b Ha).
  - pose proof (HW a O) as Wv. destruct (m1 a) eqn:E.
    + exact (MI a _ E).
    + exact (wview_not_ro rsegs m1 a Wv E).
Qed.

Section DB.
Context (IHI : reac_frame_inspect_contract) (IHC : reac_frame_counter_contract) (IMS : memset_contract)
  (IDE : reac_decode_contract).
Variables (x1 x3 x4 x5 x6 x7 x8 x9 x11 x12 x13 x14 x15 x16 x17 x19 x21 x24 x27 x28 x29 x30 x31 sp : word)
  (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (Q : machine_state -> Prop)
  (mode nch ns out frame len lo : Z) (fr junk : list byte).
Let olen := fd_olen nch ns.
Hypothesis Hnch : -128 <= nch <= 127.
Hypothesis Hns : -128 <= ns <= 127.
Hypothesis HM : bytes_at rsegs m (mode + 4) (le4 (Z_to_bv 64 nch) ++ le4 (Z_to_bv 64 ns)).
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
Hypothesis DFS : frame + len <= lo \/ bv_unsigned sp + 40 <= frame.
Hypothesis DMS : mode + 12 <= lo \/ bv_unsigned sp + 40 <= mode + 4.
Hypothesis MI : mem_inv rsegs m.

Local Notation ST0 pc mm x1v x8v x9v x10v x11v x12v x13v :=
  (MS (mkR x1v sp x3 x4 x5 x6 x7 x8v x9v x10v x11v x12v x13v x14 x15 x16 x17
     (Z_to_bv 64 mode) (Z_to_bv 64 out) (Z_to_bv 64 ns) x21 (Z_to_bv 64 (fd_olen nch ns)) (Z_to_bv 64 (fd_fits nch ns)) x24
     (Z_to_bv 64 len) (Z_to_bv 64 frame) x27 x28 x29 x30 x31)
     F (Z_to_bv 64 pc) fc None mm (seg_rom rsegs)).

Definition wfz (len : Z) (bs : list byte) : Z := if inspect_wf len bs then 1 else 0.

Lemma rd_fr : forall k, 0 <= k < len -> ov_read_bytes rsegs m (Z_to_bv 64 (frame + k)) 1 =
  Some [nth (Z.to_nat k) fr (Z_to_bv 8 0)].
Proof. intros k Hk. apply rd1; [exact HFR | lia]. Qed.

Lemma seg_DB_W : forall (a1v a2v a3v : word),
  (forall y12 y13 : word, evt rsegs Q (ST0 0x12f10 m (Z_to_bv 64 0x12ecc) (Z_to_bv 64 (wfz len fr)) x9
     (Z_to_bv 64 (inspect_result len fr)) (Z_to_bv 64 (wfz len fr)) y12 y13)) ->
  evt rsegs Q (ST0 0x12ecc m (Z_to_bv 64 0x12ecc) x8 x9 (Z_to_bv 64 (inspect_result len fr)) a1v a2v a3v).
Proof.
  intros a1v a2v a3v CONT. unfold wfz in CONT.
  pose proof (bytes_at_bound _ _ _ _ HFR) as HFB. rewrite HLEN in HFB.
  step. step. rewrite inspect_valid_bit. step.
  brq B1.
  2:{ assert (WF : inspect_wf len fr = false) by (apply not_true_iff_false; rewrite inspect_wf_spec; lia).
      rewrite WF in CONT |- *. step. apply CONT. }
  pose proof (rd_fr 12 ltac:(lia)) as HR. change (Z.to_nat 12) with 12%nat in HR.
  step. step. step. rewrite eqb_zxb' by lia. brq B2.
  2:{ assert (WF : inspect_wf len fr = false)
        by (apply not_true_iff_false; rewrite inspect_wf_spec; unfold inspect_byte; lia).
      rewrite WF in CONT |- *. step. apply CONT. }
  clear HR. pose proof (rd_fr 13 ltac:(lia)) as HR. change (Z.to_nat 13) with 13%nat in HR.
  step. step. step. rewrite eqb_zxb' by lia. brq B3.
  2:{ assert (WF : inspect_wf len fr = false)
        by (apply not_true_iff_false; rewrite inspect_wf_spec; unfold inspect_byte; lia).
      rewrite WF in CONT |- *. step. apply CONT. }
  clear HR. pose proof (rd_fr 1490 ltac:(lia)) as HR. change (Z.to_nat 1490) with 1490%nat in HR.
  step. step. step. rewrite eqb_zxb' by lia. brq B4.
  2:{ assert (WF : inspect_wf len fr = false)
        by (apply not_true_iff_false; rewrite inspect_wf_spec; unfold inspect_byte; lia).
      rewrite WF in CONT |- *. step. apply CONT. }
  clear HR. pose proof (rd_fr 1491 ltac:(lia)) as HR. change (Z.to_nat 1491) with 1491%nat in HR.
  step. step. step. step.
  pose proof (byte_range (nth 1491 fr (Z_to_bv 8 0))) as BR5.
  destruct (Z.eqb_spec (bv_unsigned (nth 1491 fr (Z_to_bv 8 0))) 234) as [B5|B5].
  - assert (WF : inspect_wf len fr = true) by (rewrite inspect_wf_spec; unfold inspect_byte; lia).
    rewrite WF in CONT |- *.
    replace (v_sltiu (Z_to_bv 64 (bv_unsigned (zxb (nth 1491 fr (Z_to_bv 8 0))) + -234)) 1) with (Z_to_bv 64 1).
    { apply CONT. }
    unfold v_sltiu, zxb. rewrite (unsigned_lit (bv_unsigned _)) by lia. rewrite B5.
    vm_compute. reflexivity.
  - assert (WF : inspect_wf len fr = false)
      by (apply not_true_iff_false; rewrite inspect_wf_spec; unfold inspect_byte; lia).
    rewrite WF in CONT |- *.
    replace (v_sltiu (Z_to_bv 64 (bv_unsigned (zxb (nth 1491 fr (Z_to_bv 8 0))) + -234)) 1) with (Z_to_bv 64 0).
    { apply CONT. }
    unfold v_sltiu, zxb. rewrite (unsigned_lit (bv_unsigned _)) by lia. rewrite unsigned_lit_wrap.
    change (bv_wrap 64 1) with 1.
    destruct (Z.ltb_spec ((bv_unsigned (nth 1491 fr (Z_to_bv 8 0)) + -234) mod 2 ^ 64) 1); [|reflexivity].
    exfalso. Z.div_mod_to_equations. lia.
Qed.

Lemma seg_DB_C : forall (y12 y13 : word),
  (forall y1 y9 y10 y11 y12' y13' : word, evt rsegs Q (ST0 0x12f40 m y1 (Z_to_bv 64 (wfz len fr)) y9 y10 y11 y12' y13')) ->
  evt rsegs Q (ST0 0x12f10 m (Z_to_bv 64 0x12ecc) (Z_to_bv 64 (wfz len fr)) x9
     (Z_to_bv 64 (inspect_result len fr)) (Z_to_bv 64 (wfz len fr)) y12 y13).
Proof.
  intros y12 y13 CONT.
  pose proof (bytes_at_bound _ _ _ _ HFR) as HFB. rewrite HLEN in HFB.
  pose proof (u64_range sp) as Rsp.
  step. rewrite bv_eqb_refl. cbn [negb].
  step. unfold wfz in CONT |- *.
  destruct (inspect_wf len fr) eqn:WF.
  - brq B1; [lia|].
    pose proof WF as WF0.
    apply inspect_wf_spec in WF. destruct WF as (W0 & W1 & W2 & W3 & W4).
    pose proof (rd_fr 15 ltac:(lia)) as HR15. change (Z.to_nat 15) with 15%nat in HR15.
    pose proof (rd_fr 14 ltac:(lia)) as HR14. change (Z.to_nat 14) with 14%nat in HR14.
    do 7 step.
    unfold inspect_result. rewrite WF0.
    rewrite cnt_hi by apply inspect_counter_range. rewrite cnt_lo.
    rewrite eqb_lit by (pose proof (inspect_counter_range fr); pose proof (byte_range (nth 14 fr (Z_to_bv 8 0)));
      pose proof (byte_range (nth 15 fr (Z_to_bv 8 0))); lia).
    replace (inspect_counter fr =? bv_unsigned (nth 14 fr (Z_to_bv 8 0)) + 256 * bv_unsigned (nth 15 fr (Z_to_bv 8 0)))
      with true by (symmetry; apply Z.eqb_eq; reflexivity).
    cbn [negb].
    step. step.
    eapply evt_cut; [eapply (IHC _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ fr) |].
    { lia. }
    { rewrite unsigned_lit by lia. exact HFR. }
    intros ms' (a1' & ->).
    replace (ret_pc (Z_to_bv 64 0x12f3c)) with (Z_to_bv 64 0x12f3c) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
    step.
    rewrite eqb_lit by (unfold counter_result, counter_byte; pose proof (byte_range (nth 14 fr (Z_to_bv 8 0)));
      pose proof (byte_range (nth 15 fr (Z_to_bv 8 0))); lia).
    replace (bv_unsigned (nth 14 fr (Z_to_bv 8 0)) + 256 * bv_unsigned (nth 15 fr (Z_to_bv 8 0)) =? counter_result fr)
      with true by (symmetry; apply Z.eqb_eq; reflexivity).
    cbn [negb]. apply CONT.
  - brq B1; [apply CONT | lia].
Qed.

Lemma olen_ok : decode_ok len fr nch ns = true -> fd_olen nch ns = 3 * nch * ns.
Proof.
  intros H. rewrite decode_ok_spec' in H. unfold fd_olen.
  rewrite (proj2 (Z.ltb_lt 0 nch)), (proj2 (Z.ltb_lt 0 ns)) by lia. reflexivity.
Qed.

Lemma seg_DB_D : forall (y1 y9 y10 y11 y12 y13 : word),
  (forall (u5 u6 u7 u11 u12 u13 u14 u15 u16 u17 u23 u28 u29 u30 u31 : word) (m' : word -> option byte),
     u23 = Z_to_bv 64 (if inspect_wf len fr && ((0 <? nch) && (0 <? ns) && (nch * ns <? 481)) then 1 else 0) ->
     munch [(bv_unsigned sp - 32, bv_unsigned sp); (out, out + olen)] m m' -> wmono rsegs m m' -> mem_inv rsegs m' ->
     stk rsegs m' lo (bv_unsigned sp) -> bytes_at rsegs m' frame fr ->
     bytes_at rsegs m' (mode + 4) (le4 (Z_to_bv 64 nch) ++ le4 (Z_to_bv 64 ns)) ->
     rw_cells rsegs m' (bv_unsigned sp + 32) [C8 (Z_to_bv 64 nch)] ->
     bytes_at rsegs m' out (if decode_ok len fr nch ns then braid_out fr nch ns else repeat FILL (Z.to_nat olen)) ->
     wr_at rsegs m' out olen ->
     evt rsegs Q (MS (mkR (Z_to_bv 64 0x12f64) sp x3 x4 u5 u6 u7 (Z_to_bv 64 (wfz len fr)) y9
       (Z_to_bv 64 (if decode_ok len fr nch ns then ns else -1)) u11 u12 u13 u14 u15 u16 u17
       (Z_to_bv 64 mode) (Z_to_bv 64 out) (Z_to_bv 64 ns) x21 (Z_to_bv 64 olen) u23 x24
       (Z_to_bv 64 len) (Z_to_bv 64 frame) x27 u28 u29 u30 u31) F (Z_to_bv 64 0x12fb0) fc None m' (seg_rom rsegs))) ->
  evt rsegs Q (ST0 0x12f40 m y1 (Z_to_bv 64 (wfz len fr)) y9 y10 y11 y12 y13).
Proof.
  intros y1 y9 y10 y11 y12 y13 CONT.
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
  replace (ret_pc (Z_to_bv 64 0x12f50)) with (Z_to_bv 64 0x12f50) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
  rewrite !unsigned_lit in MU1, HO1 by lia.
  assert (HFR1 : bytes_at rsegs m1 frame fr).
  { eapply bytes_at_transport; [exact HFR | exact MU1 |]. cbn [disjoint_from]. rewrite HLEN. split; [lia | exact I]. }
  assert (HM1 : bytes_at rsegs m1 (mode + 4) (le4 (Z_to_bv 64 nch) ++ le4 (Z_to_bv 64 ns))).
  { eapply bytes_at_transport; [exact HM | exact MU1 |]. cbn [disjoint_from]. rewrite length_app, length_le4.
    split; [cbn; lia | exact I]. }
  assert (HS1 : rw_cells rsegs m1 (bv_unsigned sp + 32) [C8 (Z_to_bv 64 nch)]).
  { eapply rw_cells_transport; [exact HS | exact MU1 | exact WM1 |]. cbn [disjoint_from cells_size csize]. split; [lia | exact I]. }
  assert (ST1 : stk rsegs m1 lo (bv_unsigned sp)).
  { eapply stk_transport_disjoint; [exact ST | exact MU1 | exact WM1 |]. cbn [disjoint_from]. split; [lia | exact I]. }
  do 5 step.
  eapply evt_cut.
  { eapply (IDE _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m1 fr frame mode out nch ns lo);
      first [ reflexivity | lia | exact HM1 | exact ST1 | idtac ].
    - intros L. rewrite unsigned_lit in L by lia. split; [lia | exact HFR1].
    - intros L. rewrite unsigned_lit in L by lia. lia.
    - intros OK. rewrite unsigned_lit in OK by lia. rewrite <- (olen_ok OK).
      destruct HO1 as [_ HW1]. cbn [cells_size csize] in HW1. rewrite Nat.add_0_r, Z2Nat.id in HW1 by lia.
      assert (L : len = 1492) by (apply decode_ok_spec' in OK; destruct OK as [OK _];
        apply inspect_wf_spec in OK; lia).
      split; [exact HW1 | lia]. }
  intros ms' (t0'' & t1'' & t2'' & a1'' & a2'' & a3'' & a4'' & a5'' & a6'' & a7'' & t3'' & t4'' & t5'' & t6'' & m2
    & -> & WM2 & ST2 & MU2).
  replace (ret_pc (Z_to_bv 64 0x12f64)) with (Z_to_bv 64 0x12f64) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
  rewrite (unsigned_lit len) in MU2 |- * by lia.
  assert (MU2w : munch [(bv_unsigned sp - 32, bv_unsigned sp); (out, out + olen)] m1 m2).
  { destruct (decode_ok len fr nch ns) eqn:OK.
    - destruct MU2 as [MU2 _]. unfold olen. rewrite (olen_ok OK). exact MU2.
    - eapply munch_weaken; [|exact MU2]. intros x Hx. cbn [outside] in *. tauto. }
  assert (HS2 : rw_cells rsegs m2 (bv_unsigned sp + 32) [C8 (Z_to_bv 64 nch)]).
  { eapply rw_cells_transport; [exact HS1 | exact MU2w | exact WM2 |]. cbn [disjoint_from cells_size csize].
    split; [lia|]. split; [lia | exact I]. }
  do 8 step.
  rewrite ex_H1. unfold wfz, fd_fits. rewrite !ex_H2, ex_H3, ex_H2, ex_H3, ex_H4.
  assert (DB : (nch mod 2 =? 0) && (inspect_wf len fr && ((0 <? nch) && (0 <? ns) && (nch * ns <? 481)))
             = decode_ok len fr nch ns).
  { unfold decode_ok. replace (nch * ns <? 481) with (nch * ns <=? 480)
      by (destruct (Z.leb_spec (nch * ns) 480); destruct (Z.ltb_spec (nch * ns) 481); try reflexivity; lia).
    destruct (inspect_wf len fr), (0 <? nch), (nch mod 2 =? 0), (0 <? ns), (nch * ns <=? 480); reflexivity. }
  rewrite DB, bv_eqb_refl. cbn [negb].
  assert (MI2 : mem_inv rsegs m2).
  { eapply mem_inv_munch; [exact MI1 | exact MU2w |]. intros x Hx. cbn [outside] in Hx.
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
  assert (HM2 : bytes_at rsegs m2 (mode + 4) (le4 (Z_to_bv 64 nch) ++ le4 (Z_to_bv 64 ns))).
  { eapply bytes_at_transport; [exact HM1 | exact MU2w |]. cbn [disjoint_from]. rewrite length_app, length_le4.
    cbn. split; [lia|]. split; [lia | exact I]. }
  assert (MU02 : munch [(bv_unsigned sp - 32, bv_unsigned sp); (out, out + olen)] m m2).
  { eapply munch_trans; [|exact MU2w]. eapply munch_weaken; [|exact MU1]. intros x Hx. cbn [outside] in *. tauto. }
  assert (WM02 : wmono rsegs m m2) by (eapply wmono_trans; [exact WM1 | exact WM2]).
  assert (HW2 : wr_at rsegs m2 out olen).
  { destruct HO1 as [_ HW1]. cbn [cells_size csize] in HW1. rewrite Nat.add_0_r, Z2Nat.id in HW1 by lia.
    eapply wr_at_transport; [exact HW1 | exact WM2]. }
  step.
  rewrite bv_lts_zero_r.
  destruct (decode_ok len fr nch ns) eqn:OK.
  - pose proof OK as OK'. apply decode_ok_spec' in OK'.
    rewrite unsigned_lit by lia. replace (2 ^ 63 <=? ns) with false by (symmetry; apply Z.leb_gt; lia).
    cbn [negb].
    destruct MU2 as [_ BO2].
    eapply CONT; try eassumption; try reflexivity.
    all: first [ rewrite ex_H2, ex_H2, ex_H3; reflexivity | rewrite OK; exact BO2 ].
  - replace (bv_unsigned (Z_to_bv 64 (-1))) with (2 ^ 64 - 1) by reflexivity.
    replace (2 ^ 63 <=? 2 ^ 64 - 1) with true by reflexivity. cbn [negb].
    assert (BF : bytes_at rsegs m2 out (repeat FILL (Z.to_nat olen))).
    { eapply bytes_at_transport; [| exact MU2 |].
      - destruct HO1 as [(_ & HB1) _]. cbn [cells_bytes cbytes] in HB1. rewrite app_nil_r in HB1.
        replace (Z_to_bv 8 (165 mod 256)) with FILL in HB1 by reflexivity. exact HB1.
      - cbn [disjoint_from]. rewrite repeat_length, Z2Nat.id by lia. split; [lia | exact I]. }
    eapply (chg_down1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m2 Q out olen BF OL ltac:(lia)
      ltac:(lia) eq_refl eq_refl).
    intros y14. eapply CONT; try eassumption; try reflexivity.
    all: first [ rewrite ex_H2, ex_H2, ex_H3; reflexivity | rewrite OK; exact BF ].
Qed.

End DB.
