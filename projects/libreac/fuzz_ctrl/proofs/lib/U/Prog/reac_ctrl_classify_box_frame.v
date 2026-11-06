From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame Tac Bytes ZBridge.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.U Require Import Img0.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Spec Require Import StrFun.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require Import RcModel RcLib RcBoxLib RcParse RcClassify
  RcClassifyLib.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.U.Prog Require Import reac_ctrl_parse_c bcmp_c
  reac_ctrl_checksum_verify_c reac_ctrl_classify_box_frame_c.
Import ListNotations.
Open Scope Z_scope.

Ltac ck4 x :=
  step; rewrite (rc_eqb_lit x 0) by lia; rewrite (proj2 (Z.eqb_neq x 0)) by lia; cbv iota;
  step; rewrite (cl_land3 x) by lia;
  step; rewrite (rc_eqb_lit 0 0) by lia; change (0 =? 0) with true; cbn [negb]; cbv iota.

Section Post.
  Variables (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (m : word -> option byte) (f n u o v S k : Z) (fr us vb B : list byte).
  Hypothesis HBC : bcmp_contract.
  Hypothesis HCV : reac_ctrl_checksum_verify_contract.
  Hypothesis Rf : 0 <= f < 2^64.
  Hypothesis Ru : 0 <= u < 2^64.
  Hypothesis Ro : 0 <= o < 2^64.
  Hypothesis Rv : 0 <= v < 2^64.
  Hypothesis RS : 128 <= S < 2^64.
  Hypothesis Lfr : length fr = 50%nat.
  Hypothesis Lus : length us = 6%nat.
  Hypothesis LB : length B = 36%nat.
  Hypothesis Rk : 0 <= k <= 13.
  Hypothesis HK : k <> 0 -> 50 <= n /\ B = cp_struct fr k /\ (k = 5 -> cp_rec fr = true).
  Hypothesis HF : 50 <= n -> 0 < f /\ f + 50 <= 2^64 /\ bytes_at rsegs m f fr /\ (f + 50 <= S - 128 \/ S <= f).
  Hypothesis HU : 50 <= n -> u + 6 <= 2^64 /\ bytes_at rsegs m u us /\ (u + 6 <= S - 128 \/ S <= u).
  Hypothesis Ho0 : o <> 0.
  Hypothesis Ho4 : o mod 4 = 0.
  Hypothesis Ho36 : o + 36 <= 2^64.
  Hypothesis DOs : o + 36 <= S - 128 \/ S <= o.
  Hypothesis DOf : 50 <= n -> o + 36 <= f \/ f + 50 <= o.
  Hypothesis DOu : o + 36 <= u \/ u + 6 <= o.
  Hypothesis Hv0 : v <> 0.
  Hypothesis Hv4 : v mod 4 = 0.
  Hypothesis Hv36 : v + 4 <= 2^64.
  Hypothesis DVs : v + 4 <= S - 128 \/ S <= v.
  Hypothesis DVo : v + 4 <= o \/ o + 36 <= v.
  Hypothesis DVf : v + 4 <= f \/ f + 50 <= v.
  Hypothesis DVu : v + 4 <= u \/ u + 6 <= v.

  Definition Wc : list ivl := [(o, o + 36); (v, v + 4); (S - 128, S)].

  Definition Qc (c : option Z) : machine_state -> Prop :=
    fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : word -> option byte),
      ms' = MS (mkR ra (Z_to_bv 64 S) gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 (cl_r c))
                    a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
               F (ret_pc ra) fc None m' (seg_rom rsegs) /\
      munch Wc m m' /\ wmono rsegs m m' /\ mem_inv rsegs m' /\ stk rsegs m' (S - 128) S /\
      rw_cells rsegs m' o [CB 36 B] /\ rw_cells rsegs m' v [CB 4 (reac_ctrl_classify_box_frame_ev c vb)].

  Definition Jc (m1 : word -> option byte) (vc : list byte) : Prop :=
    rw_cells rsegs m1 (S + -48) [C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] /\
    bytes_at rsegs m1 o B /\ wr_at rsegs m1 o 36 /\ rw_cells rsegs m1 v [CB 4 vc] /\
    munch Wc m m1 /\ wmono rsegs m m1 /\ mem_inv rsegs m1 /\ stk rsegs m1 (S - 128) (S + -48).

Ltac jc := unfold Jc; refine (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ _)))))));
  first [eassumption | unfold Wc; eassumption].

  Lemma epi : forall c x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x20 x28 x29 x30 x31 m1,
    Jc m1 (reac_ctrl_classify_box_frame_ev c vb) ->
    evt rsegs (Qc c)
      (MS (mkR x1 (Z_to_bv 64 (S + -48)) gp tp x5 x6 x7 (Z_to_bv 64 v) (Z_to_bv 64 (cl_r c)) x10 x11 x12 x13 x14
               x15 x16 x17 (Z_to_bv 64 o) (Z_to_bv 64 f) x20 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
          F (Z_to_bv 64 0x14564) fc None m1 (seg_rom rsegs)).
  Proof.
    intros c x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x20 x28 x29 x30 x31 m1
      (FR & HBo & WRo & HV & MU & WM & MI & ST).
    step. step. step. step. step. step. step. step. step.
    replace (S + -48 + 48) with S by lia.
    pose proof (stk_release rsegs m1 _ _ _ ST FR ltac:(lia)) as ST2.
    cbn [cells_size csize Nat.add] in ST2. replace (S + -48 + Z.of_nat 48) with S in ST2 by lia.
    apply evt_done. unfold Qc. do 14 eexists. exists m1.
    split; [reflexivity|].
    split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact ST2|].
    split; [|exact HV].
    rewrite <- LB. apply cl_rw_of; [exact HBo|]. rewrite LB. exact WRo.
  Qed.

  Lemma st : forall e x1 x5 x6 x7 x9 x11 x12 x13 x14 x15 x16 x17 x20 x28 x29 x30 x31 m1,
    Jc m1 vb ->
    evt rsegs (Qc (Some e))
      (MS (mkR x1 (Z_to_bv 64 (S + -48)) gp tp x5 x6 x7 (Z_to_bv 64 v) x9 (Z_to_bv 64 e) x11 x12 x13 x14
               x15 x16 x17 (Z_to_bv 64 o) (Z_to_bv 64 f) x20 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
          F (Z_to_bv 64 0x1450c) fc None m1 (seg_rom rsegs)).
  Proof.
    intros e x1 x5 x6 x7 x9 x11 x12 x13 x14 x15 x16 x17 x20 x28 x29 x30 x31 m1
      (FR & HBo & WRo & HV & MU & WM & MI & ST).
    unfold Wc in MU.
    step. step. step.
    apply cl_rw_c4 in HV.
    eapply (epi (Some e)). jc.
  Qed.

Ltac vst e J := ck4 v; step; step; apply (st e); exact J.

  Lemma tl : k <> 0 -> forall x1 x5 x6 x7 x9 x10 x12 x13 x14 x15 x16 x17 x20 x28 x29 x30 x31 m1,
    x9 = Z_to_bv 64 (cl_r None) -> Jc m1 vb ->
    evt rsegs (Qc (cl_tail k fr))
      (MS (mkR x1 (Z_to_bv 64 (S + -48)) gp tp x5 x6 x7 (Z_to_bv 64 v) x9 x10 (Z_to_bv 64 k) x12 x13 x14
               x15 x16 x17 (Z_to_bv 64 o) (Z_to_bv 64 f) x20 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
          F (Z_to_bv 64 0x14588) fc None m1 (seg_rom rsegs)).
  Proof.
    intros K0 x1 x5 x6 x7 x9 x10 x12 x13 x14 x15 x16 x17 x20 x28 x29 x30 x31 m1 E9 J. subst x9.
    destruct (HK K0) as (HN & EB & _).
    pose proof J as (_ & HBo & _).
    assert (R23 : ov_read_bytes rsegs m1 (wa (o + 23)) 1 = Some [cp_b fr 19])
      by (apply (cl_rd _ _ _ B _ 23 1); [exact HBo | lia | rewrite EB; reflexivity]).
    step. step.
    rewrite (rc_eqb_lit k 2) by lia.
    destruct (Z.eqb_spec k 2) as [K2|K2]; cbv iota.
    { step. step. step.
      rewrite (cl_zxb_eqb (cp_b fr 19) 3) by lia.
      destruct (Z.eqb_spec (bv_unsigned (cp_b fr 19)) 3) as [E19|E19]; cbn [negb]; cbv iota.
      - replace (cl_tail k fr) with (Some 4) by (unfold cl_tail, cp_v; rewrite K2, E19; reflexivity).
        vst 4 J.
      - replace (cl_tail k fr) with (Some 2)
          by (unfold cl_tail, cp_v; rewrite K2, (proj2 (Z.eqb_neq _ 3) E19); reflexivity).
        vst 2 J. }
    step. step.
    rewrite (rc_eqb_lit k 9) by lia.
    destruct (Z.eqb_spec k 9) as [K9|K9]; cbv iota.
    { replace (cl_tail k fr) with (Some 5) by (unfold cl_tail; rewrite K9; reflexivity).
      vst 5 J. }
    step. step.
    rewrite (rc_eqb_lit k 7) by lia.
    destruct (Z.eqb_spec k 7) as [K7|K7]; cbn [negb]; cbv iota.
    - replace (cl_tail k fr) with (Some 3) by (unfold cl_tail; rewrite K7; reflexivity).
      vst 3 J.
    - replace (cl_tail k fr) with (Some 2)
        by (unfold cl_tail; rewrite (proj2 (Z.eqb_neq k 7) K7), (proj2 (Z.eqb_neq k 2) K2),
              (proj2 (Z.eqb_neq k 9) K9); reflexivity).
      vst 2 J.
  Qed.

  Lemma d9 : k <> 0 -> forall w2, -256 < w2 < 256 -> (w2 =? 0) = cl_eq6 fr us ->
    forall x1 x5 x6 x7 x9 x10 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 m1,
    x9 = Z_to_bv 64 (cl_r None) -> Jc m1 vb ->
    evt rsegs (Qc (cl_d9 k fr us))
      (MS (mkR x1 (Z_to_bv 64 (S + -48)) gp tp x5 x6 x7 (Z_to_bv 64 v) x9 x10 (Z_to_bv 64 k) x12 x13 x14
               x15 x16 x17 (Z_to_bv 64 o) (Z_to_bv 64 f) (Z_to_bv 64 w2) s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
          F (Z_to_bv 64 0x14560) fc None m1 (seg_rom rsegs)).
  Proof.
    intros K0 w2 Rw Ew x1 x5 x6 x7 x9 x10 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 m1 E9 J.
    step.
    rewrite (cl_eqb0 w2) by lia. rewrite Ew.
    unfold cl_d9. destruct (cl_eq6 fr us); cbn [negb]; cbv iota.
    - eapply tl; [exact K0 | exact E9 | exact J].
    - subst x9. apply (epi None). exact J.
  Qed.

  Lemma d7 : k <> 0 -> forall w2, -256 < w2 < 256 -> (w2 =? 0) = cl_eq6 fr us ->
    forall x1 x5 x6 x7 x9 x10 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 m1,
    x9 = Z_to_bv 64 (cl_r None) -> Jc m1 vb ->
    evt rsegs (Qc (cl_d7 k fr us))
      (MS (mkR x1 (Z_to_bv 64 (S + -48)) gp tp x5 x6 x7 (Z_to_bv 64 v) x9 x10 (Z_to_bv 64 k) x12 x13 x14
               x15 x16 x17 (Z_to_bv 64 o) (Z_to_bv 64 f) (Z_to_bv 64 w2) s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
          F (Z_to_bv 64 0x144f0) fc None m1 (seg_rom rsegs)).
  Proof.
    intros K0 w2 Rw Ew x1 x5 x6 x7 x9 x10 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 m1 E9 J.
    destruct (HK K0) as (HN & EB & _).
    pose proof J as (_ & HBo & _).
    assert (RB : 0 <= (if cp_bcast fr then 1 else 0) < 128) by (destruct (cp_bcast fr); lia).
    assert (R16 : ov_read_bytes rsegs m1 (wa (o + 16)) 4 = Some (le4 (Z_to_bv 64 (if cp_bcast fr then 1 else 0))))
      by (rewrite cl_le4_small by lia; apply (cl_rd _ _ _ B _ 16 4); [exact HBo | lia | rewrite EB; apply cl_bc16]).
    step. rewrite (cl_sx32 (if cp_bcast fr then 1 else 0)) by lia.
    step. rewrite (rc_eqb_lit (if cp_bcast fr then 1 else 0) 0) by lia.
    unfold cl_d7. destruct (cp_bcast fr); cbv iota.
    - change (1 =? 0) with false. cbv iota.
      step. step. rewrite (rc_eqb_lit k 1) by lia.
      destruct (Z.eqb_spec k 1) as [K1|K1]; cbn [negb]; cbv iota.
      + ck4 v. rewrite K1. apply (st 0). exact J.
      + subst x9. apply (epi None). exact J.
    - change (0 =? 0) with true. cbv iota.
      eapply d9; [exact K0 | exact Rw | exact Ew | exact E9 | exact J].
  Qed.

  Lemma d5 : k <> 0 -> forall w2, -256 < w2 < 256 -> (w2 =? 0) = cl_eq6 fr us ->
    forall x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 m1,
    x9 = Z_to_bv 64 (cl_r None) -> Jc m1 vb ->
    evt rsegs (Qc (cl_d5 k fr us))
      (MS (mkR x1 (Z_to_bv 64 (S + -48)) gp tp x5 x6 x7 (Z_to_bv 64 v) x9 x10 x11 x12 x13 x14
               x15 x16 x17 (Z_to_bv 64 o) (Z_to_bv 64 f) (Z_to_bv 64 w2) s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
          F (Z_to_bv 64 0x14524) fc None m1 (seg_rom rsegs)).
  Proof.
    intros K0 w2 Rw Ew x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 m1 E9 J.
    destruct (HK K0) as (HN & EB & HR5).
    pose proof J as (_ & HBo & _).
    assert (R0 : ov_read_bytes rsegs m1 (wa (o + 0)) 4 = Some (le4 (Z_to_bv 64 k)))
      by (rewrite cl_le4_small by lia; apply (cl_rd _ _ _ B _ 0 4); [exact HBo | lia | rewrite EB; reflexivity]).
    step. rewrite (cl_sx32 k) by lia.
    step. step.
    rewrite (rc_eqb_lit k 5) by lia.
    unfold cl_d5. destruct (Z.eqb_spec k 5) as [K5|K5]; cbn [negb]; cbv iota.
    - pose proof (HR5 K5) as RC.
      assert (R26 : ov_read_bytes rsegs m1 (wa (o + 26)) 1 = Some [cp_b fr 22])
        by (apply (cl_rd _ _ _ B _ 26 1); [exact HBo | lia | rewrite EB; reflexivity]).
      assert (R28 : ov_read_bytes rsegs m1 (wa (o + 28)) 2 =
                    Some (le2 (Z_to_bv 64 (bv_unsigned (cp_b fr 35) + 256 * bv_unsigned (cp_b fr 34)))))
        by (rewrite cl_le2; apply (cl_rd _ _ _ B _ 28 2); [exact HBo | lia | rewrite EB; unfold cp_struct; rewrite RC;
              reflexivity]).
      step. step.
      rewrite (cl_zxb_eqb (cp_b fr 22) 0) by lia.
      rewrite cl_join_lhu. unfold cp_v.
      destruct (Z.eqb_spec (bv_unsigned (cp_b fr 22)) 0) as [E22|E22]; cbn [negb andb]; cbv iota.
      2: { subst x9. apply (epi None). exact J. }
      pose proof (byte_range (cp_b fr 35)). pose proof (byte_range (cp_b fr 34)).
      step. rewrite cl_zx16 by lia.
      step. step.
      rewrite (rc_eqb_lit (bv_unsigned (cp_b fr 35) + 256 * bv_unsigned (cp_b fr 34)) 770) by lia.
      destruct (Z.eqb_spec (bv_unsigned (cp_b fr 35) + 256 * bv_unsigned (cp_b fr 34)) 770); cbv iota.
      { rewrite Bool.orb_true_r. cbv iota. vst 1 J. }
      step. step.
      rewrite (rc_eqb_lit (bv_unsigned (cp_b fr 35) + 256 * bv_unsigned (cp_b fr 34)) 256) by lia.
      destruct (Z.eqb_spec (bv_unsigned (cp_b fr 35) + 256 * bv_unsigned (cp_b fr 34)) 256); cbn [negb orb]; cbv iota.
      + vst 1 J.
      + subst x9. apply (epi None). exact J.
    - eapply d7; [exact K0 | exact Rw | exact Ew | exact E9 | exact J].
  Qed.

  Lemma d4 : k <> 0 -> forall w2, -256 < w2 < 256 -> (w2 =? 0) = cl_eq6 fr us ->
    forall x1 x5 x6 x7 x9 x11 x12 x13 x14 x15 x16 x17 x20 x28 x29 x30 x31 m1,
    x9 = Z_to_bv 64 (cl_r None) -> Jc m1 vb ->
    evt rsegs (Qc (cl_d4 k fr us))
      (MS (mkR x1 (Z_to_bv 64 (S + -48)) gp tp x5 x6 x7 (Z_to_bv 64 v) x9 (Z_to_bv 64 w2) x11 x12 x13 x14
               x15 x16 x17 (Z_to_bv 64 o) (Z_to_bv 64 f) x20 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
          F (Z_to_bv 64 0x144e0) fc None m1 (seg_rom rsegs)).
  Proof.
    intros K0 w2 Rw Ew x1 x5 x6 x7 x9 x11 x12 x13 x14 x15 x16 x17 x20 x28 x29 x30 x31 m1 E9 J.
    destruct (HK K0) as (HN & EB & _).
    pose proof J as (_ & HBo & _ & _ & MU & _).
    assert (R0 : ov_read_bytes rsegs m1 (wa (o + 0)) 4 = Some (le4 (Z_to_bv 64 k)))
      by (rewrite cl_le4_small by lia; apply (cl_rd _ _ _ B _ 0 4); [exact HBo | lia | rewrite EB; reflexivity]).
    step. rewrite (cl_sx32 k) by lia.
    step. step. step.
    rewrite (rc_eqb_lit k 1) by lia.
    unfold cl_d4. destruct (Z.eqb_spec k 1) as [K1|K1]; cbn [negb andb]; cbv iota.
    - replace (cl_d5 k fr us) with (cl_d7 k fr us) by (unfold cl_d5; rewrite K1; reflexivity).
      replace (Z_to_bv 64 1) with (Z_to_bv 64 k) by (rewrite K1; reflexivity).
      eapply d7; [exact K0 | exact Rw | exact Ew | exact E9 | exact J].
    - destruct (HF HN) as (Hf0 & Hf50 & HFm & DFs).
      unfold Wc in MU.
      assert (HF1 : bytes_at rsegs m1 f fr)
        by (eapply bytes_at_transport; [exact HFm | exact MU | cbn [disjoint_from]; rewrite Lfr;
              pose proof (DOf HN); repeat split; lia]).
      pose proof (bytes_at_sub rsegs m1 f fr 18 32 HF1 ltac:(lia)) as H18.
      rewrite firstn_all2 in H18 by (rewrite length_skipn; lia). change (Z.of_nat 18) with 18 in H18.
      step. step.
      eapply evt_cut.
      { eapply HCV with (p := f) (bs := skipn 18 fr); [lia | lia | reflexivity | rewrite length_skipn; lia | exact H18]. }
      intros ms' (a1' & a2' & a3' & a4' & a5' & E). subst ms'.
      replace (ret_pc (Z_to_bv 64 0x14520)) with (Z_to_bv 64 0x14520) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
      unfold cl_bsum.
      destruct (Z.eqb_spec (blocksum (skipn 18 fr)) 0) as [B0|B0]; cbn [negb andb]; cbv iota.
      + step. rewrite (cl_eqb0 0) by lia. change (0 =? 0) with true. cbn [negb]. cbv iota.
        eapply d5; [exact K0 | exact Rw | exact Ew | exact E9 | exact J].
      + step. rewrite (cl_eqb0 (-1)) by lia. change (-1 =? 0) with false. cbn [negb]. cbv iota.
        subst x9. apply (epi None). exact J.
  Qed.

  Lemma d3 : k <> 0 -> forall x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 m1,
    x9 = Z_to_bv 64 (cl_r None) -> Jc m1 vb ->
    evt rsegs (Qc (cl_d3 k fr us))
      (MS (mkR x1 (Z_to_bv 64 (S + -48)) gp tp x5 x6 x7 (Z_to_bv 64 v) x9 x10 x11 x12 x13 x14
               x15 x16 x17 (Z_to_bv 64 o) (Z_to_bv 64 f) (Z_to_bv 64 u) s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
          F (Z_to_bv 64 0x144bc) fc None m1 (seg_rom rsegs)).
  Proof.
    intros K0 x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 m1 E9
      (FR & HBo & WRo & HV & MU & WM & MI & ST).
    destruct (HK K0) as (HN & EB & _).
    destruct (HU HN) as (Hu6 & HUm & DUs).
    unfold Wc in MU.
    assert (HU1 : bytes_at rsegs m1 u us)
      by (eapply bytes_at_transport; [exact HUm | exact MU | cbn [disjoint_from]; rewrite Lus; repeat split; lia]).
    clear HUm.
    pose proof (bytes_at_sub rsegs m1 o B 4 6 HBo ltac:(lia)) as HS.
    replace (firstn 6 (skipn 4 B)) with [cp_b fr 6; cp_b fr 7; cp_b fr 8; cp_b fr 9; cp_b fr 10; cp_b fr 11] in HS
      by (rewrite EB; reflexivity).
    pose proof (bytes_at_sub rsegs m1 o B 10 6 HBo ltac:(lia)) as HD.
    replace (firstn 6 (skipn 10 B)) with [cp_b fr 0; cp_b fr 1; cp_b fr 2; cp_b fr 3; cp_b fr 4; cp_b fr 5] in HD
      by (rewrite EB; reflexivity).
    change (Z.of_nat 4) with 4 in HS. change (Z.of_nat 10) with 10 in HD.
    destruct (cl_memcmp6 [cp_b fr 6; cp_b fr 7; cp_b fr 8; cp_b fr 9; cp_b fr 10; cp_b fr 11] us eq_refl Lus)
      as (w1 & HM1 & Rw1 & Ew1).
    rewrite cl_eq6_src in Ew1.
    step. step. step. step.
    eapply evt_cut.
    { eapply HBC; [rewrite unsigned_lit by lia; exact HS | rewrite unsigned_lit by lia; exact HU1 | exact HM1 | exact MI]. }
    intros ms' PO.
    destruct PO as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m2 & E & MU2 & WM2
                    & MI2 & _ & _).
    subst ms'.
    transport_after_call rsegs m1 m2 MU2 WM2.
    clear MU2 WM2.
    replace (ret_pc (Z_to_bv 64 0x144cc)) with (Z_to_bv 64 0x144cc) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
    step.
    rewrite (cl_eqb0 w1) by lia. rewrite Ew1.
    unfold cl_d3. destruct (cl_eq6 (skipn 6 fr) us); cbv iota.
    { subst x9. apply (epi None). jc. }
    destruct (cl_memcmp6 [cp_b fr 0; cp_b fr 1; cp_b fr 2; cp_b fr 3; cp_b fr 4; cp_b fr 5] us eq_refl Lus)
      as (w2 & HM2 & Rw2 & Ew2).
    rewrite cl_eq6_dst in Ew2.
    step. step. step. step.
    eapply evt_cut.
    { eapply HBC; [rewrite unsigned_lit by lia; exact HD | rewrite unsigned_lit by lia; exact HU1 | exact HM2 | exact MI2]. }
    intros ms' PO.
    destruct PO as (t0'' & t1'' & t2'' & a1'' & a2'' & a3'' & a4'' & a5'' & a6'' & a7'' & t3'' & t4'' & t5'' & t6'' & m3 & E
                    & MU3 & WM3 & MI3 & _ & _).
    subst ms'.
    transport_after_call rsegs m2 m3 MU3 WM3.
    clear MU3 WM3.
    replace (ret_pc (Z_to_bv 64 0x144e0)) with (Z_to_bv 64 0x144e0) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
    eapply d4; [exact K0 | exact Rw2 | exact Ew2 | exact E9 | jc].
  Qed.

  Lemma d2 : k <> 0 -> forall x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 m1,
    x9 = Z_to_bv 64 (cl_r None) -> Jc m1 vb ->
    evt rsegs (Qc (cl_d2 k fr us))
      (MS (mkR x1 (Z_to_bv 64 (S + -48)) gp tp x5 x6 x7 (Z_to_bv 64 v) x9 x10 x11 x12 x13 x14
               x15 x16 x17 (Z_to_bv 64 o) (Z_to_bv 64 f) (Z_to_bv 64 u) s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
          F (Z_to_bv 64 0x1449c) fc None m1 (seg_rom rsegs)).
  Proof.
    intros K0 x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 m1 E9 J.
    destruct (HK K0) as (HN & EB & _).
    pose proof J as (_ & HBo & _).
    assert (R4 : ov_read_bytes rsegs m1 (wa (o + 4)) 1 = Some [cp_b fr 6])
      by (apply (cl_rd _ _ _ B _ 4 1); [exact HBo | lia | rewrite EB; reflexivity]).
    assert (R5 : ov_read_bytes rsegs m1 (wa (o + 5)) 1 = Some [cp_b fr 7])
      by (apply (cl_rd _ _ _ B _ 5 1); [exact HBo | lia | rewrite EB; reflexivity]).
    assert (R6 : ov_read_bytes rsegs m1 (wa (o + 6)) 1 = Some [cp_b fr 8])
      by (apply (cl_rd _ _ _ B _ 6 1); [exact HBo | lia | rewrite EB; reflexivity]).
    unfold cl_d2, cl_oui, cp_v.
    step. step. rewrite (cl_zxb_eqb (cp_b fr 6) 0) by lia.
    destruct (Z.eqb_spec (bv_unsigned (cp_b fr 6)) 0) as [E6|E6]; cbn [negb andb]; cbv iota.
    2: { subst x9. apply (epi None). exact J. }
    step. step. step. rewrite (cl_zxb_eqb (cp_b fr 7) 64) by lia.
    destruct (Z.eqb_spec (bv_unsigned (cp_b fr 7)) 64) as [E7|E7]; cbn [negb andb]; cbv iota.
    2: { subst x9. apply (epi None). exact J. }
    step. step. step. rewrite (cl_zxb_eqb (cp_b fr 8) 171) by lia.
    destruct (Z.eqb_spec (bv_unsigned (cp_b fr 8)) 171) as [E8|E8]; cbn [negb andb]; cbv iota.
    2: { subst x9. apply (epi None). exact J. }
    eapply d3; [exact K0 | exact E9 | exact J].
  Qed.

  Lemma d1 : forall x1 x5 x6 x7 x9 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 m1,
    Jc m1 vb ->
    evt rsegs (Qc (if k =? 0 then None else cl_d2 k fr us))
      (MS (mkR x1 (Z_to_bv 64 (S + -48)) gp tp x5 x6 x7 (Z_to_bv 64 v) x9 (Z_to_bv 64 k) x11 x12 x13 x14
               x15 x16 x17 (Z_to_bv 64 o) (Z_to_bv 64 f) (Z_to_bv 64 u) s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
          F (Z_to_bv 64 0x14488) fc None m1 (seg_rom rsegs)).
  Proof.
    intros x1 x5 x6 x7 x9 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 m1 J.
    step. step.
    rewrite (rc_eqb_lit k 0) by lia.
    destruct (Z.eqb_spec k 0) as [K0|K0]; cbv iota.
    - apply (epi None). exact J.
    - ck4 o. eapply d2; [exact K0 | reflexivity | exact J].
  Qed.
End Post.

Theorem reac_ctrl_classify_box_frame_holds :
  reac_ctrl_parse_contract -> bcmp_contract -> reac_ctrl_checksum_verify_contract ->
  reac_ctrl_classify_box_frame_contract.
Proof.
  intros HP HBC HCV. unfold reac_ctrl_classify_box_frame_contract, REAC_CTRL_CLASSIFY_BOX_FRAME,
    REAC_CTRL_CLASSIFY_BOX_FRAME_K.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    f n u o v S fr us junk vb -> -> -> -> -> -> Rf Rn Ru Ro Rv RS S16 SK ST Lfr HF Ho0 Ho4 Ho36 HO DOs DOf DOu Lus HU
    Hv0 Hv4 Hv36 HV DVs DVo DVf DVu MI.
  pose proof (munch_refl [(o, o + 36); (v, v + 4); (S - 128, S)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  step.
  carve_frame 48%nat ST.
  step. step. step. step. step. step.
  step. step. step. step. step. step.
  assert (HRD : forall i, In i (cp_rd n fr) -> mrd rsegs m1 (wa (f + Z.of_nat i)) = nth_error fr i).
  { intros i Hi. destruct (Z_lt_le_dec n 50) as [Ln|Ln].
    - unfold cp_rd in Hi. rewrite (proj2 (Z.leb_gt 50 n) Ln) in Hi. destruct Hi.
    - destruct (HF Ln) as (_ & _ & HFm & DFs).
      assert (HF1 : bytes_at rsegs m1 f fr)
        by (eapply bytes_at_transport; [exact HFm | exact MU | cbn [disjoint_from]; rewrite Lfr;
              pose proof (DOf Ln); repeat split; lia]).
      destruct HF1 as (_ & _ & HF1). apply HF1. pose proof (cp_rd_lt39 n fr i Hi). lia. }
  eapply evt_cut.
  { eapply HP with (f := f) (n := n) (o := o) (S := S + -48) (fr := fr) (junk := junk).
    - reflexivity.
    - reflexivity.
    - reflexivity.
    - reflexivity.
    - lia.
    - lia.
    - lia.
    - lia.
    - Z.div_mod_to_equations. lia.
    - unfold REAC_CTRL_PARSE_K. lia.
    - unfold REAC_CTRL_PARSE_K. replace (S + -48 - 80) with (S - 128) by lia. exact ST.
    - exact MI.
    - exact Lfr.
    - intros Ln. destruct (HF Ln) as (A1 & A2 & _ & A4). unfold REAC_CTRL_PARSE_K. lia.
    - exact HRD.
    - intros _. unfold REAC_CTRL_PARSE_K.
      refine (conj Ho4 (conj Ho36 (conj HO (conj _ DOf)))). lia. }
  intros ms' PO.
  destruct PO as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m2 & E & MU2 & WM2
                  & MI2 & ST2 & RO2).
  subst ms'.
  specialize (RO2 Ho0).
  unfold reac_ctrl_parse_fp, REAC_CTRL_PARSE_K in MU2, ST2.
  rewrite (proj2 (Z.eqb_neq o 0) Ho0) in MU2. cbn [app] in MU2.
  transport_after_call rsegs m1 m2 MU2 WM2.
  clear MU2 WM2.
  replace (ret_pc (Z_to_bv 64 0x14488)) with (Z_to_bv 64 0x14488) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
  replace (S + -48 - 80) with (S - 128) in ST2 by lia.
  destruct RO2 as [[_ HBo] WRo]. cbn [cells_bytes cbytes] in HBo. rewrite app_nil_r in HBo.
  cbn [cells_size csize] in WRo. change (Z.of_nat (36 + 0)) with 36 in WRo.
  eapply evt_mono.
  - eapply d1 with (ra := ra) (gp := gp) (tp := tp) (s0 := s0) (s1 := s1) (s2 := s2) (s3 := s3) (s4 := s4)
      (s5 := s5) (s6 := s6) (s7 := s7) (s8 := s8) (s9 := s9) (s10 := s10) (s11 := s11) (F := F) (fc := fc) (m := m)
      (f := f) (n := n) (u := u) (o := o) (v := v) (S := S) (k := fst (ctrlparse n fr)) (fr := fr) (us := us)
      (vb := vb) (B := snd (ctrlparse n fr)).
    all: first [eassumption | lia | apply ctrlparse_length | apply ctrlparse_kind_range | apply cl_hk | idtac].
    unfold Jc. refine (conj _ (conj HBo (conj WRo (conj HV (conj MU (conj WM (conj MI2 ST2))))))). eassumption.
  - intros ms' H. rewrite classify_d1. exact H.
Qed.
