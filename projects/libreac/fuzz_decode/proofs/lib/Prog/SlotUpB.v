From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Lib Require Import Tac Bytes.
From OSSVerify.Proofs.libreac.fuzz_decode.lib Require Import Img0.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Prog Require Import ReacDecodeLib SlotLoops SlotDown SlotUp
  reac_frame_inspect_c reac_decode_c reac_upstream_channels_c reac_upstream_decode_c memset_c
  reac_upstream_decode fd_up_q.
Import ListNotations.
Open Scope Z_scope.

Lemma up_nch_eq : forall len, 0 <= len < 2^26 -> up_nch len = upstream_result len.
Proof.
  intros len H. unfold up_nch.
  destruct (Z.leb_spec 52 len) as [L|L]; [destruct (Z.eqb_spec ((len - 52) mod 36) 0) as [M|M]|].
  - rewrite (upstream_result_q len) by lia.
    assert (Q : 0 <= (len - 52) / 36 < 2^21) by (split; [apply Z.div_pos | apply Z.div_lt_upper_bound]; lia).
    assert (E : (124 <=? len) = (2 <=? (len - 52) / 36)).
    { destruct (Z.leb_spec 124 len); destruct (Z.leb_spec 2 ((len - 52) / 36)); try reflexivity;
        Z.div_mod_to_equations; lia. }
    rewrite E. cbn [andb].
    destruct (2 <=? (len - 52) / 36), (((len - 52) / 36) mod 2 =? 0), ((len - 52) / 36 <=? 40); reflexivity.
  - rewrite upstream_result_bad by lia. destruct (124 <=? len); reflexivity.
  - rewrite upstream_result_bad by lia. rewrite (proj2 (Z.leb_gt 124 len)) by lia. reflexivity.
Qed.

Lemma up_ok_nch : forall raw out len bs, 0 <= len < 2^26 -> up_ok raw out len bs = true ->
  2 <= up_nch len <= 40.
Proof.
  intros raw out len bs HL OK. rewrite up_ok_true in OK. destruct OK as (_ & _ & U3 & _).
  apply up_nch_pos in U3. destruct U3 as (V1 & V2 & V3 & V4 & V5). rewrite V5.
  split; [|lia]. apply Z.div_le_lower_bound; lia.
Qed.

Lemma olen_pos : forall len, 0 <= len < 2^26 -> 1 <= up_olen len.
Proof.
  intros len HLB. unfold up_olen. pose proof (upstream_result_range len HLB).
  destruct (Z.ltb_spec 0 (upstream_result len)); lia.
Qed.

Lemma olen_nch : forall len, 0 <= len < 2^26 -> 2 <= up_nch len -> up_olen len = 36 * up_nch len.
Proof.
  intros len HLB N. unfold up_olen. rewrite <- (up_nch_eq len HLB).
  destruct (Z.ltb_spec 0 (up_nch len)); lia.
Qed.

Lemma last_val : forall b : byte,
  Z_to_bv 64 (Z.lor (bv_unsigned (Z_to_bv 64 (bv_unsigned (v_sltiu (Z_to_bv 64 (bv_unsigned (zxb b) + -234)) 1)
    + -1))) 12) = Z_to_bv 64 (if bv_unsigned b =? 234 then 12 else -1).
Proof.
  intros b. pose proof (bv_unsigned_in_range 8 b) as Hb. unfold bv_modulus in Hb.
  change (2 ^ Z.of_N 8) with 256 in Hb. unfold zxb, v_sltiu. rewrite (unsigned_lit (bv_unsigned b)) by lia.
  rewrite (unsigned_lit_wrap (bv_unsigned b + -234)). change (bv_wrap 64 1) with 1.
  destruct (Z.eqb_spec (bv_unsigned b) 234) as [E|E].
  - rewrite E. replace ((234 + -234) mod 2 ^ 64 <? 1) with true by reflexivity.
    apply bv_eq. reflexivity.
  - replace ((bv_unsigned b + -234) mod 2 ^ 64 <? 1) with false
      by (symmetry; apply Z.ltb_ge; Z.div_mod_to_equations; lia).
    apply bv_eq. reflexivity.
Qed.

Section UB.
Context (IMS : memset_contract) (IUD : reac_upstream_decode_contract).

Lemma seg_UB : forall (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word) (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
    (Sp len frame out lo : Z) (fr junk : list byte),
  x2 = Z_to_bv 64 Sp -> x8 = Z_to_bv 64 (frame + 50) -> x10 = Z_to_bv 64 out ->
  x19 = Z_to_bv 64 (upstream_result len) -> x21 = Z_to_bv 64 (up_olen len) ->
  x25 = Z_to_bv 64 len -> x26 = Z_to_bv 64 frame ->
  0 <= len < 2 ^ 26 -> Z.of_nat (length fr) = len ->
  4096 <= out -> out + up_olen len < 2 ^ 63 -> 4096 <= frame -> frame + len < 2 ^ 63 ->
  (out + up_olen len <= frame \/ frame + len <= out) ->
  bytes_at rsegs m frame fr -> rw_cells rsegs m out [CB (Z.to_nat (up_olen len)) junk] -> mem_inv rsegs m ->
  evt rsegs (fun ms => q_ucrt F fc x3 x4 m Sp len frame out fr ms \/ q_ufree F fc x3 x4 m Sp len frame out lo ms)
    (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) F (Z_to_bv 64 0x1318c) fc None m (seg_rom rsegs)).
Proof.
  intros x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27
    x28 x29 x30 x31 F fc m Sp len frame out lo fr junk E2 E8 E10 E19 E21 E25 E26 HLB HLEN HOP HOE HFP HFE DOF
    HFR HO MI.
  subst x2 x8 x10 x19 x21 x25 x26.
  pose proof (bytes_at_bound _ _ _ _ HFR) as HFB. rewrite HLEN in HFB.
  pose proof (rw_cells_bound _ _ _ _ HO) as HOB. cbn [cells_size csize Nat.add] in HOB.
  pose proof (olen_pos len HLB) as OL.
  rewrite ?Nat.add_0_r in HOB. rewrite Z2Nat.id in HOB by lia.
  pose proof (upstream_result_range len HLB) as UR.
  pose proof (up_nch_eq len HLB) as UNE.
  step. brq B0; [lia|].
  do 4 step.
  eapply evt_cut; [eapply (IMS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ junk) |].
  { rewrite !unsigned_lit by lia. exact HO. }
  { exact MI. }
  intros ms' (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m1
    & -> & MU1 & WM1 & MI1 & HO1).
  replace (ret_pc (Z_to_bv 64 0x131a0)) with (Z_to_bv 64 0x131a0) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
  rewrite !unsigned_lit in MU1, HO1 by lia.
  assert (HFR1 : bytes_at rsegs m1 frame fr).
  { eapply bytes_at_transport; [exact HFR | exact MU1 |]. cbn [disjoint_from]. rewrite HLEN. split; [lia | exact I]. }
  assert (BF : bytes_at rsegs m1 out (repeat FILL (Z.to_nat (up_olen len)))).
  { destruct HO1 as [(_ & HB1) _]. cbn [cells_bytes cbytes] in HB1. rewrite app_nil_r in HB1.
    replace (Z_to_bv 8 (165 mod 256)) with FILL in HB1 by reflexivity. exact HB1. }
  assert (HW1 : wr_at rsegs m1 out (up_olen len)).
  { destruct HO1 as [_ HW1]. cbn [cells_size csize] in HW1. rewrite Nat.add_0_r, Z2Nat.id in HW1 by lia.
    exact HW1. }
  pose proof (magic_bytes m1 MI1) as HMG1.
  do 4 step.
  eapply evt_cut.
  { eapply (IUD _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m1 fr 0 out);
      first [ reflexivity | lia | exact HMG1 | idtac ].
    all: first [ rewrite unsigned_lit by lia; lia
               | intros Z0; exfalso; exact (Z0 eq_refl)
               | intros OK; rewrite up_ok_true in OK; exfalso; destruct OK as [OK _]; exact (OK eq_refl) ]. }
  intros ms' (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m2 & -> & WM2 & HM2).
  replace (ret_pc (Z_to_bv 64 0x131b0)) with (Z_to_bv 64 0x131b0) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
  replace (up_ok 0 out (bv_unsigned (Z_to_bv 64 len)) fr) with false in *
    by (symmetry; apply not_true_iff_false; rewrite up_ok_true; intros [OK _]; exact (OK eq_refl)).
  subst m2.
  do 5 step.
  eapply evt_cut.
  { eapply (IUD _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m1 fr frame 0);
      first [ reflexivity | lia | exact HMG1 | idtac ].
    all: first [ rewrite unsigned_lit by lia; lia
               | intros _ Z0; exfalso; exact (Z0 eq_refl)
               | intros OK; rewrite up_ok_true in OK; exfalso; destruct OK as (_ & OK & _); exact (OK eq_refl) ]. }
  intros ms' (v0 & v1 & v2 & c1 & c2 & c3 & c4 & c5 & c6 & c7 & v3 & v4 & v5 & v6 & m2 & -> & WM3 & HM3).
  replace (ret_pc (Z_to_bv 64 0x131c4)) with (Z_to_bv 64 0x131c4) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
  replace (up_ok frame 0 (bv_unsigned (Z_to_bv 64 len)) fr) with false in *
    by (symmetry; apply not_true_iff_false; rewrite up_ok_true; intros (_ & OK & _); exact (OK eq_refl)).
  subst m2.
  step. step. rewrite bv_eqb_refl. cbn [negb]. step. rewrite bv_eqb_refl. cbn [negb].
  eapply chg_up3 with (m := m1) (out := out) (n := up_olen len).
  all: first [ exact BF | lia | reflexivity | idtac ].
  intros y12.
  do 4 step.
  eapply evt_cut.
  { eapply (IUD _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m1 fr frame out);
      first [ reflexivity | lia | exact HMG1 | idtac ].
    - rewrite unsigned_lit by lia. lia.
    - intros _ _ _. rewrite unsigned_lit by lia. split; [| exact HFR1]. rewrite <- HLEN. symmetry. apply Nat2Z.id.
    - intros OK. rewrite unsigned_lit in OK |- * by lia. pose proof (up_ok_nch _ _ _ _ HLB OK) as N.
      rewrite <- (olen_nch len HLB ltac:(lia)). split; [exact HW1 | lia]. }
  intros ms' (w0 & w1 & w2 & d1 & d2 & d3 & d4 & d5 & d6 & d7 & w3 & w4 & w5 & w6 & m3 & -> & WM4 & HM4).
  replace (ret_pc (Z_to_bv 64 0x13208)) with (Z_to_bv 64 0x13208) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
  rewrite (unsigned_lit len) in HM4 |- * by lia.
  destruct (up_ok frame out len fr) eqn:OK.
  - pose proof (up_ok_nch _ _ _ _ HLB OK) as N.
    pose proof (olen_nch len HLB ltac:(lia)) as E.
    destruct HM4 as [MU4 BO4].
    pose proof OK as OK'. rewrite up_ok_true in OK'. destruct OK' as (_ & _ & U3 & U4 & U5 & U6 & U7).
    apply up_nch_pos in U3. destruct U3 as (V1 & V2 & V3 & V4 & V5).
    unfold inspect_byte in U4, U5, U6, U7.
    assert (HFR3 : bytes_at rsegs m3 frame fr).
    { eapply bytes_at_transport; [exact HFR1 | exact MU4 |]. cbn [disjoint_from]. rewrite HLEN.
      split; [lia | exact I]. }
    step. step. rewrite lts0_lit by lia. brq B1; [|lia].
    pose proof (rd1 _ _ _ 12 HFR3 ltac:(lia)) as HR. change (Z.to_nat 12) with 12%nat in HR.
    step. step. step. rewrite eqb_zxb by lia. brq B2; [| lia].
    clear HR.
    pose proof (rd1 _ _ _ 13 HFR3 ltac:(lia)) as HR. change (Z.to_nat 13) with 13%nat in HR.
    step. step. step. rewrite eqb_zxb by lia. brq B3; [| lia].
    clear HR.
    pose proof (rd1 _ _ _ (len - 2) HFR3 ltac:(lia)) as HR.
    replace (frame + (len - 2)) with (frame + len + -2) in HR by lia.
    step. step. step. step. rewrite eqb_zxb by lia. brq B4; [| lia].
    clear HR.
    pose proof (rd1 _ _ _ (len - 1) HFR3 ltac:(lia)) as HR.
    replace (frame + (len - 1)) with (frame + len + -1) in HR by lia.
    step. step. step. step. step. step.
    rewrite last_val. rewrite (proj2 (Z.eqb_eq _ _) U7). rewrite bv_eqb_refl. cbn [negb].
    step. rewrite bv_lts_zero_r. rewrite (unsigned_lit 12) by lia.
    replace (2 ^ 63 <=? 12) with false by reflexivity. cbn [negb].
    step. rewrite lts0_lit by lia. replace (0 <? 12) with true by reflexivity. cbn [negb].
    do 5 step.
    apply evt_done. left. unfold q_ucrt.
    eexists _, m3. split; [reflexivity|].
    do 13 (split; [reflexivity|]).
    split; [exact OK|].
    split; [eapply munch_trans; [exact MU1 | rewrite E; exact MU4]|].
    split; [eapply wmono_trans; [exact WM1 | exact WM4]|].
    split; [exact HFR3 | rewrite <- UNE; exact BO4].
  - subst m3.
    assert (TAIL : forall z12 z13 z14 : word,
      evt rsegs (fun ms => q_ucrt F fc x3 x4 m Sp len frame out fr ms \/ q_ufree F fc x3 x4 m Sp len frame out lo ms)
        (MS (mkR (Z_to_bv 64 0x13208) (Z_to_bv 64 Sp) x3 x4 w0 w1 w2 (Z_to_bv 64 (frame + 50)) x9
          (Z_to_bv 64 (-1)) (Z_to_bv 64 (-1)) z12 z13 z14 d5 d6 d7 x18 (Z_to_bv 64 (upstream_result len))
          (Z_to_bv 64 out) (Z_to_bv 64 (out + up_olen len)) (Z_to_bv 64 (-1)) x23 x24 (Z_to_bv 64 len)
          (Z_to_bv 64 frame) x27 w3 w4 w5 w6) F (Z_to_bv 64 0x1324c) fc None m1 (seg_rom rsegs))).
    { intros z12 z13 z14.
      step. rewrite bv_eqb_refl. cbn [negb].
      step. rewrite bv_lts_zero_r. replace (bv_unsigned (Z_to_bv 64 (-1))) with (2 ^ 64 - 1) by reflexivity.
      replace (2 ^ 63 <=? 2 ^ 64 - 1) with true by reflexivity. cbn [negb].
      eapply chg_up4 with (m := m1) (out := out) (n := up_olen len).
      all: first [ exact BF | lia | reflexivity | idtac ].
      intros y13'.
      step. rewrite lts0_lit by lia. replace (0 <? -1) with false by reflexivity. cbn [negb].
      step. step.
      apply evt_done. right. unfold q_ufree.
      eexists _, m1. split; [reflexivity|].
      do 8 (split; [reflexivity|]).
      split; [eapply munch_weaken; [|exact MU1]; intros x Hx; cbn [outside] in *; tauto | exact WM1]. }
    step. step. rewrite lts0_lit by lia. brq B1; [|apply TAIL].
    pose proof (up_nch_pos len ltac:(lia)) as (V1 & V2 & V3 & V4 & V5).
    pose proof (rd1 _ _ _ 12 HFR1 ltac:(lia)) as HR. change (Z.to_nat 12) with 12%nat in HR.
    step. step. step. rewrite eqb_zxb by lia. brq B2; [| apply TAIL].
    clear HR.
    pose proof (rd1 _ _ _ 13 HFR1 ltac:(lia)) as HR. change (Z.to_nat 13) with 13%nat in HR.
    step. step. step. rewrite eqb_zxb by lia. brq B3; [| apply TAIL].
    clear HR.
    pose proof (rd1 _ _ _ (len - 2) HFR1 ltac:(lia)) as HR.
    replace (frame + (len - 2)) with (frame + len + -2) in HR by lia.
    step. step. step. step. rewrite eqb_zxb by lia. brq B4; [| apply TAIL].
    clear HR.
    pose proof (rd1 _ _ _ (len - 1) HFR1 ltac:(lia)) as HR.
    replace (frame + (len - 1)) with (frame + len + -1) in HR by lia.
    step. step. step. step. step.
    rewrite last_val.
    destruct (Z.eqb_spec (bv_unsigned (nth (Z.to_nat (len - 1)) fr (Z_to_bv 8 0))) 234) as [B5|B5].
    + exfalso. rewrite <- not_true_iff_false in OK. apply OK. rewrite up_ok_true. unfold inspect_byte.
      repeat split; lia.
    + apply TAIL.
Qed.

End UB.
