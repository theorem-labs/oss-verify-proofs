(* Footprint twin of reac_ctrl_headamp_record_verify.v (not in this delivery) (RECIPE.md steps 1-2 (a working note, not in this delivery)): the same run as an
   ExecF.evtF under a footprint RNG. The script is the old one with StepF's step; each data access closes from an rng
   premise (the frame, the GOT cell and the shadow-offset cell, the record bytes, their shadow bytes).
   reac_ctrl_headamp_record_verify_contract_of_F re-derives the old contract from the twin with RNG_all. *)
From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes ZBridge.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Import Img0 AsanRT.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require Import RcModel RcLib RcLeaf RcLeafLib RcAsan RcAsanLib.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require Import RcAsanRT reac_ctrl_headamp_record_verify_c.
(* Last: StepF's step (evtF goals) shadows Step's (evt goals). *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import ExecF StepF.
Import ListNotations.
Open Scope Z_scope.

Section BodyF.
  Variables (ra sp1 gp tp t0 t1 t2 s0 s1 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (p off : Z) (b0 b1 : byte) (rec : list byte)
    (W : list ivl) (Q : machine_state -> Prop) (RNG : footprint).
  Hypothesis Hp : 0 < p.
  Hypothesis Hp40 : p + 40 <= 2^64.
  Hypothesis HB : bytes_at rsegs m (p + 18) [b0; b1].
  Hypothesis Hlen : length rec = 6%nat.
  Hypothesis HR : bytes_at rsegs m (p + 34) rec.
  Hypothesis HSR1 : asan_shadow_rd rsegs m off (p + 18) 2 W.
  Hypothesis HSR2 : asan_shadow_rd rsegs m off (p + 34) 6 W.
  Hypothesis HAD1 : asan_addressable rsegs m off (p + 18) 2.
  Hypothesis HAD2 : asan_addressable rsegs m off (p + 34) 6.
  Hypothesis RB1 : rng RNG (p + 18) 2.
  Hypothesis RB2 : rng RNG (p + 34) 6.
  Hypothesis RS1 : rng RNG ((p + 18) / 8 + off) ((p + 19) / 8 + off - ((p + 18) / 8 + off) + 1).
  Hypothesis RS2 : rng RNG ((p + 34) / 8 + off) ((p + 39) / 8 + off - ((p + 34) / 8 + off) + 1).

  Abbreviation ST pc x10 x11 x12 x14 x15 x16 :=
    (MS (mkR ra sp1 gp tp t0 t1 t2 s0 s1 x10 x11 x12 (Z_to_bv 64 off) x14 x15 x16 a7
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 pc) fc None m (seg_rom rsegs)).

  Hypothesis EXIT : forall x10 x12 x14 x15 x16,
    evtF rsegs RNG Q (ST 0x84f38 x10 (Z_to_bv 64 (if hv b0 b1 rec then 0 else -1)) x12 x14 x15 x16).

  Lemma hloop_F : bv_unsigned b0 = 4 -> bv_unsigned b1 = 3 -> forall n i x15 x16,
    (i + n = 6)%nat -> (0 < n)%nat ->
    evtF rsegs RNG Q (ST 0x84ef4 (Z_to_bv 64 (p + 34 + Z.of_nat i)) (Z_to_bv 64 (psum rec i))
                    (Z_to_bv 64 (p + 34 + Z.of_nat i)) (Z_to_bv 64 (6 - Z.of_nat i)) x15 x16).
  Proof.
    intros E0 E1.
    induction n as [|n IH]; intros i x15 x16 Hin Hn; [lia|].
    assert (BODY : forall y15 y16,
      evtF rsegs RNG Q (ST 0x84f04 (Z_to_bv 64 (p + 34 + Z.of_nat i)) (Z_to_bv 64 (psum rec i))
                      (Z_to_bv 64 (p + 34 + Z.of_nat i)) (Z_to_bv 64 (6 - Z.of_nat i)) y15 y16)).
    { intros y15 y16.
      pose proof (rd_byte rsegs m (p + 34) rec i HR ltac:(lia)) as RD.
      pose proof (psum_range rec i) as PR.
      step. step. step. step.
      rewrite psum_S_zxb.
      step. step.
      rewrite (rc_eqb0_signed (6 - Z.of_nat i + -1)) by lia.
      destruct n as [|n].
      - replace (6 - Z.of_nat i + -1 =? 0) with true by (symmetry; apply Z.eqb_eq; lia).
        cbn [negb]. step.
        replace i with 5%nat in * by lia.
        step. step. step.
        pose proof (psum_range rec 6) as R6. change (Z.of_nat 6) with 6 in R6.
        rewrite (rcl_fin127 (psum rec 6)) by lia.
        replace (psum rec 6 mod 128 =? 0) with (hv b0 b1 rec) by (unfold hv, rsum; rewrite E0, E1; reflexivity).
        apply EXIT.
      - replace (6 - Z.of_nat i + -1 =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
        cbn [negb].
        replace (p + 34 + Z.of_nat i + 1) with (p + 34 + Z.of_nat (S i)) by lia.
        replace (6 - Z.of_nat i + -1) with (6 - Z.of_nat (S i)) by lia.
        apply (IH (S i)); lia. }
    destruct (asan_shadow_read rsegs m off (p + 34) 6 W (Z.of_nat i) HSR2 ltac:(lia)) as (k & RK & BK).
    pose proof (HAD2 (Z.of_nat i) k ltac:(lia) BK) as OK.
    pose proof (rc_byte_signed k) as KR.
    clear BK.
    step.
    rewrite (unsigned_lit (p + 34 + Z.of_nat i)) by lia. rewrite rc_shr3.
    step. step.
    clear RK.
    step.
    unfold sxb. rewrite (rc_eqb0_signed (bv_signed k)) by lia.
    destruct (Z.eqb_spec (bv_signed k) 0) as [K0|K0]; cbn [negb].
    - apply BODY.
    - step.
      rewrite (unsigned_lit (p + 34 + Z.of_nat i)) by lia. rewrite rc_land7.
      step.
      rewrite (rc_lts_signed ((p + 34 + Z.of_nat i) mod 8) (bv_signed k))
        by (pose proof (Z.mod_pos_bound (p + 34 + Z.of_nat i) 8 ltac:(lia)); lia).
      replace ((p + 34 + Z.of_nat i) mod 8 <? bv_signed k) with true
        by (symmetry; apply Z.ltb_lt; destruct OK; lia).
      apply BODY.
  Qed.

  Lemma hb1_F : bv_unsigned b0 = 4 -> forall x14 x15 x16,
    evtF rsegs RNG Q (ST 0x84ed8 (Z_to_bv 64 p) (Z_to_bv 64 (-1)) (Z_to_bv 64 (p + 19)) x14 x15 x16).
  Proof.
    intros E0 x14 x15 x16.
    pose proof (rcl_rd rsegs m (p + 18) [b0; b1] 1 b1 HB eq_refl) as R1.
    change (Z.of_nat 1) with 1 in R1. replace (p + 18 + 1) with (p + 19) in R1 by lia.
    step. step. step.
    rewrite (rcl_zxb_eqb b1 3) by lia.
    destruct (Z.eqb_spec (bv_unsigned b1) 3) as [E1|E1]; cbn [negb].
    - step. step. step. step.
      change (Z_to_bv 64 0) with (Z_to_bv 64 (psum rec 0)).
      change (Z_to_bv 64 6) with (Z_to_bv 64 (6 - Z.of_nat 0)).
      replace (p + 34) with (p + 34 + Z.of_nat 0) by lia.
      exact (hloop_F E0 E1 6 0 x15 x16 eq_refl ltac:(lia)).
    - pose proof EXIT as EX.
      replace (hv b0 b1 rec) with false in EX
        by (symmetry; unfold hv; apply Z.eqb_neq in E1; rewrite E1; rewrite Bool.andb_false_r; reflexivity).
      apply EX.
  Qed.

  Lemma hb0_F : forall x12 x14 x15 x16,
    evtF rsegs RNG Q (ST 0x84eb4 (Z_to_bv 64 p) (Z_to_bv 64 (p + 18)) x12 x14 x15 x16).
  Proof.
    intros x12 x14 x15 x16.
    pose proof (rcl_rd rsegs m (p + 18) [b0; b1] 0 b0 HB eq_refl) as R0.
    change (Z.of_nat 0) with 0 in R0. replace (p + 18 + 0) with (p + 18) in R0 by lia.
    step. step. step. step.
    rewrite (rcl_zxb_eqb b0 4) by lia.
    destruct (Z.eqb_spec (bv_unsigned b0) 4) as [E0|E0]; cbn [negb].
    - destruct (asan_shadow_read_at rsegs m off (p + 18) 2 W 1 ((p + 19) / 8 + off) HSR1 ltac:(lia)
                  ltac:(unfold asan_shadow; replace (p + 18 + 1) with (p + 19) by lia; reflexivity))
        as (k & RK & BK).
      pose proof (HAD1 1 k ltac:(lia) BK) as OK. unfold asan_ok in OK.
      replace (p + 18 + 1) with (p + 19) in OK by lia.
      pose proof (rc_byte_signed k) as KR. clear BK.
      step. step.
      rewrite (unsigned_lit (p + 19)) by lia. rewrite rc_shr3.
      step. step.
      clear RK.
      step.
      unfold sxb. rewrite (rc_eqb0_signed (bv_signed k)) by lia.
      destruct (Z.eqb_spec (bv_signed k) 0) as [K0|K0]; cbn [negb].
      + apply (hb1_F E0).
      + step.
        rewrite (unsigned_lit (p + 19)) by lia. rewrite rc_land7.
        step.
        rewrite (rc_lts_signed ((p + 19) mod 8) (bv_signed k))
          by (pose proof (Z.mod_pos_bound (p + 19) 8 ltac:(lia)); lia).
        replace ((p + 19) mod 8 <? bv_signed k) with true
          by (symmetry; apply Z.ltb_lt; destruct OK; lia).
        apply (hb1_F E0).
    - pose proof EXIT as EX.
      replace (hv b0 b1 rec) with false in EX
        by (symmetry; unfold hv; apply Z.eqb_neq in E0; rewrite E0; reflexivity).
      apply EX.
  Qed.

  Lemma hentry_F : forall x11 x12 x14 x15 x16,
    evtF rsegs RNG Q (ST 0x84ea0 (Z_to_bv 64 p) x11 x12 x14 x15 x16).
  Proof.
    intros x11 x12 x14 x15 x16.
    destruct (asan_shadow_read_at rsegs m off (p + 18) 2 W 0 ((p + 18) / 8 + off) HSR1 ltac:(lia)
                ltac:(unfold asan_shadow; rewrite Z.add_0_r; reflexivity)) as (k & RK & BK).
    pose proof (HAD1 0 k ltac:(lia) BK) as OK. unfold asan_ok in OK. rewrite Z.add_0_r in OK.
    pose proof (rc_byte_signed k) as KR. clear BK.
    step. step.
    rewrite (unsigned_lit (p + 18)) by lia. rewrite rc_shr3.
    step. step.
    clear RK.
    step.
    unfold sxb. rewrite (rc_eqb0_signed (bv_signed k)) by lia.
    destruct (Z.eqb_spec (bv_signed k) 0) as [K0|K0]; cbn [negb].
    - apply hb0_F.
    - step.
      rewrite (unsigned_lit (p + 18)) by lia. rewrite rc_land7.
      step.
      rewrite (rc_lts_signed ((p + 18) mod 8) (bv_signed k))
        by (pose proof (Z.mod_pos_bound (p + 18) 8 ltac:(lia)); lia).
      replace ((p + 18) mod 8 <? bv_signed k) with true
        by (symmetry; apply Z.ltb_lt; destruct OK; lia).
      apply hb0_F.
  Qed.
End BodyF.

(* Route (C): the proof of the footprint contract without the shadow_rw premise. The old script never used that
   premise. *)
Theorem reac_ctrl_headamp_record_verify_holds_F_on : reac_ctrl_headamp_record_verify_contract_F_on.
Proof.
  unfold reac_ctrl_headamp_record_verify_contract_F_on, REAC_CTRL_HEADAMP_RECORD_VERIFY,
    REAC_CTRL_HEADAMP_RECORD_VERIFY_FRAME.
  intros RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    p lo b0 b1 rec -> Hp Hp40 HB Hlen HR ST HLO HD1 HD2 HCE HADR1 HADR2 HW RFR RGOT RCELL RB1 RB2 RS1 RS2.
  unfold GOT_CELL_K in RGOT. unfold CELL_K in RCELL. unfold shadow_addr in RS1, RS2.
  pose proof (rt_asan_rt m _ HCE HW) as HRT.
  pose proof (rt_shadow_rd m (p + 18) 2 _ HADR1 (fun x Hx => HW x (or_intror (or_intror Hx)))) as HSR1.
  pose proof (rt_shadow_rd m (p + 34) 6 _ HADR2 (fun x Hx => HW x (or_intror (or_intror Hx)))) as HSR2.
  pose proof (rt_addressable m (p + 18) 2 HADR1) as HAD1.
  pose proof (rt_addressable m (p + 34) 6 HADR2) as HAD2.
  set (off := ASAN_K) in HRT, HSR1, HSR2, HAD1, HAD2, RS1, RS2. clearbody off.
  pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. change (bv_modulus 64) with (2^64) in Rsp.
  pose proof ST as (ST0 & _ & _).
  assert (WV : forall x, bv_unsigned sp - 16 <= x < bv_unsigned sp -> wview rsegs m (wa x) <> None)
    by (intros x Hx; destruct ST as (_ & _ & H); exact (proj1 (H x ltac:(lia)))).
  carve_frame 16%nat ST.
  step. step.
  match goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) => rename mm into m1 end.
  pose proof (asan_rt_munch rsegs m m1 _ _ off _ _ HRT MU (fun x Hx => Hx)) as HRT1.
  pose proof (asan_shadow_rd_munch rsegs m m1 off (p + 18) 2 _ _ HSR1 MU (fun x Hx => Hx)) as HSR1'.
  pose proof (asan_shadow_rd_munch rsegs m m1 off (p + 34) 6 _ _ HSR2 MU (fun x Hx => Hx)) as HSR2'.
  pose proof (asan_addressable_munch rsegs m m1 off (p + 18) 2 _ _ HAD1 HSR1 MU (fun x Hx => Hx)) as HAD1'.
  pose proof (asan_addressable_munch rsegs m m1 off (p + 34) 6 _ _ HAD2 HSR2 MU (fun x Hx => Hx)) as HAD2'.
  pose proof (asan_rt_got_read rsegs m1 _ _ off _ HRT1) as RG.
  pose proof (asan_rt_cell_read rsegs m1 _ _ off _ HRT1) as RC.
  unfold GOT_CELL_K, CELL_K in RG, RC.
  step. step. step.
  clear RG RC.
  refine (hentry_F ra _ gp tp t0 t1 t2 s0 s1 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m1 p off b0 b1 rec _ _
            RNG Hp Hp40 HB Hlen HR HSR1' HSR2' HAD1' HAD2' RB1 RB2 RS1 RS2 _ _ _ _ _ _).
  intros x10 x12 x14 x15 x16.
  step. step. step. step.
  release_frame FR ST (bv_unsigned sp).
  apply evtF_done. cbv beta. do 7 eexists. split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|].
  split; [intros HI; exact (rc_mem_inv_frame rsegs m m1 _ _ HI MU WV) | exact ST].
Qed.

(* The old footprint statement, from the narrowed one. *)
Theorem reac_ctrl_headamp_record_verify_holds_F : reac_ctrl_headamp_record_verify_contract_F.
Proof. exact (reac_ctrl_headamp_record_verify_contract_F_of_on reac_ctrl_headamp_record_verify_holds_F_on). Qed.

(* RECIPE step 1: the old contract as a corollary (evtF_evt of the twin at RNG_all, each rng premise by rng_all). *)
Theorem reac_ctrl_headamp_record_verify_contract_of_F :
  reac_ctrl_headamp_record_verify_contract_F -> reac_ctrl_headamp_record_verify_contract.
Proof.
  unfold reac_ctrl_headamp_record_verify_contract_F, reac_ctrl_headamp_record_verify_contract.
  intros HF ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    p lo b0 b1 rec E0 Hp Hp40 HB Hlen HR ST HLO HD1 HD2 HCE HSW HADR1 HADR2 HW.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. change (bv_modulus 64) with (2^64) in Rsp.
  pose proof ST as (ST0 & _ & _).
  apply (evtF_evt rsegs RNG_all).
  apply (HF RNG_all ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
            F fc m p lo b0 b1 rec E0 Hp Hp40 HB Hlen HR ST HLO HD1 HD2 HCE HSW HADR1 HADR2 HW);
    apply rng_all; unfold REAC_CTRL_HEADAMP_RECORD_VERIFY_FRAME, GOT_CELL_K, CELL_K, shadow_addr, ASAN_K in *; lia.
Qed.

(* The same step between the statements without the premise (reac_ctrl_headamp_record_verify_contract_of_F's
   script). The old theorem above keeps its own proof: its premise contract_F does not give contract_F_on. *)
Theorem reac_ctrl_headamp_record_verify_contract_of_F_on :
  reac_ctrl_headamp_record_verify_contract_F_on -> reac_ctrl_headamp_record_verify_contract_on.
Proof.
  unfold reac_ctrl_headamp_record_verify_contract_F_on, reac_ctrl_headamp_record_verify_contract_on.
  intros HF ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    p lo b0 b1 rec E0 Hp Hp40 HB Hlen HR ST HLO HD1 HD2 HCE HADR1 HADR2 HW.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. change (bv_modulus 64) with (2^64) in Rsp.
  pose proof ST as (ST0 & _ & _).
  apply (evtF_evt rsegs RNG_all).
  apply (HF RNG_all ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
            F fc m p lo b0 b1 rec E0 Hp Hp40 HB Hlen HR ST HLO HD1 HD2 HCE HADR1 HADR2 HW);
    apply rng_all; unfold REAC_CTRL_HEADAMP_RECORD_VERIFY_FRAME, GOT_CELL_K, CELL_K, shadow_addr, ASAN_K in *; lia.
Qed.
