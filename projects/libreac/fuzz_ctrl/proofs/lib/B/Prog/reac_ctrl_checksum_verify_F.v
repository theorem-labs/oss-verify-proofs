(* The footprint twin of reac_ctrl_checksum_verify.v: the same run as an ExecF.evtF under a footprint RNG
   (reac_ctrl_checksum_verify_contract_F), by the script of reac_ctrl_checksum_verify.v over StepF's step. Each
   access of the run is closed from one rng premise: the frame store/load of ra, the two 8-byte loads of the GOT
   cell and the runtime cell, the 1-byte load of each data byte, and the 1-byte load of its shadow byte.
   reac_ctrl_checksum_verify_holds_of_F re-derives the old contract from the footprint form with RNG_all. *)
From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes ZBridge.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require Import Img0 AsanRT.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require Import RcModel RcLib RcAsan RcAsanLib.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog Require Import RcAsanRT reac_ctrl_checksum_verify_c reac_ctrl_checksum_verify.
(* Last: StepF's step (evtF goals) shadows Step's (evt goals). *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import ExecF StepF.
Import ListNotations.
Open Scope Z_scope.

Section LoopF.
  Variables (ra sp1 gp tp t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (p off : Z) (bs : list byte) (W : list ivl)
    (Q : machine_state -> Prop) (RNG : footprint).
  Hypothesis Hp : 0 < p.
  Hypothesis Hp50 : p + 50 <= 2^64.
  Hypothesis Hlen : length bs = 32%nat.
  Hypothesis HB : bytes_at rsegs m (p + 18) bs.
  Hypothesis HSR : asan_shadow_rd rsegs m off (p + 18) 32 W.
  Hypothesis HAD : asan_addressable rsegs m off (p + 18) 32.
  Hypothesis RDAT : rng RNG (p + 18) 32.
  Hypothesis RSH : rng RNG ((p + 18) / 8 + off) ((p + 49) / 8 - (p + 18) / 8 + 1).

  Abbreviation ST pc x5 x10 x11 x14 x15 x17 :=
    (MS (mkR ra sp1 gp tp x5 t1 t2 s0 s1 x10 x11 (Z_to_bv 64 off) (Z_to_bv 64 (18446744073709551615 - p))
             x14 x15 (Z_to_bv 64 50) x17 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 pc) fc None m (seg_rom rsegs)).

  Hypothesis EXIT : forall x5 x10 x14 x15 x17,
    evtF rsegs RNG Q (ST 0x83c00 x5 x10 (Z_to_bv 64 (psum bs 32)) x14 x15 x17).

  Lemma loop_F : forall n i x5 x17,
    (i + n = 32)%nat -> (0 < n)%nat ->
    evtF rsegs RNG Q (ST 0x83bc4 x5 (Z_to_bv 64 (p + 18 + Z.of_nat i)) (Z_to_bv 64 (psum bs i))
                         (Z_to_bv 64 (p + 18 + Z.of_nat i)) (Z_to_bv 64 (18 + Z.of_nat i)) x17).
  Proof using Hp Hp50 Hlen HB HSR HAD RDAT RSH EXIT.
    induction n as [|n IH]; intros i x5 x17 Hin Hn; [lia|].
    (* The shadow byte of data byte i: inside RSH. *)
    assert (RSi : rng RNG ((p + 18 + Z.of_nat i) / 8 + off) 1).
    { apply (rng_sub' RNG ((p + 18) / 8 + off) ((p + 49) / 8 - (p + 18) / 8 + 1) _ _ RSH).
      pose proof (Z.div_le_mono (p + 18) (p + 18 + Z.of_nat i) 8 ltac:(lia) ltac:(lia)).
      pose proof (Z.div_le_mono (p + 18 + Z.of_nat i) (p + 49) 8 ltac:(lia) ltac:(lia)).
      split; lia. }
    assert (BODY : forall y5 y17,
      evtF rsegs RNG Q (ST 0x83bd8 y5 (Z_to_bv 64 (p + 18 + Z.of_nat i)) (Z_to_bv 64 (psum bs i))
                           (Z_to_bv 64 (p + 18 + Z.of_nat i)) (Z_to_bv 64 (18 + Z.of_nat i)) y17)).
    { intros y5 y17.
      pose proof (rd_byte rsegs m (p + 18) bs i HB ltac:(lia)) as RD.
      pose proof (psum_range bs i) as PR.
      step. step. step. step. step.
      rewrite psum_S_zxb.
      step.
      assert (R1 : 0 < 18 + Z.of_nat i + 1 <= 2^64) by lia.
      assert (R2 : 0 < 50 <= 2^64) by lia.
      rewrite (eqb_le64 (18 + Z.of_nat i + 1) 50 R1 R2).
      destruct n as [|n].
      - replace (18 + Z.of_nat i + 1 =? 50) with true by (symmetry; apply Z.eqb_eq; lia).
        cbn [negb]. step.
        replace i with 31%nat in * by lia.
        apply EXIT.
      - replace (18 + Z.of_nat i + 1 =? 50) with false by (symmetry; apply Z.eqb_neq; lia).
        cbn [negb].
        replace (18 + Z.of_nat i + 1) with (18 + Z.of_nat (S i)) by lia.
        replace (p + 18 + Z.of_nat i + 1) with (p + 18 + Z.of_nat (S i)) by lia.
        apply (IH (S i)); lia. }
    step.
    rewrite (rc_ltu_lit64 (18446744073709551615 - p) (18 + Z.of_nat i)) by lia.
    replace (18446744073709551615 - p <? 18 + Z.of_nat i) with false by (symmetry; apply Z.ltb_ge; lia).
    destruct (asan_shadow_read rsegs m off (p + 18) 32 W (Z.of_nat i) HSR ltac:(lia)) as (k & RK & BK).
    pose proof (HAD (Z.of_nat i) k ltac:(lia) BK) as OK.
    pose proof (rc_byte_signed k) as KR.
    clear BK.
    step.
    rewrite (unsigned_lit (p + 18 + Z.of_nat i)) by lia. rewrite rc_shr3.
    step.
    step.
    clear RK.
    step.
    unfold sxb. rewrite (rc_eqb0_signed (bv_signed k)) by lia.
    destruct (Z.eqb_spec (bv_signed k) 0) as [K0|K0]; cbn [negb].
    - apply BODY.
    - step.
      rewrite (unsigned_lit (p + 18 + Z.of_nat i)) by lia. rewrite rc_land7.
      step.
      rewrite (rc_lts_signed ((p + 18 + Z.of_nat i) mod 8) (bv_signed k))
        by (pose proof (Z.mod_pos_bound (p + 18 + Z.of_nat i) 8 ltac:(lia)); lia).
      replace ((p + 18 + Z.of_nat i) mod 8 <? bv_signed k) with true
        by (symmetry; apply Z.ltb_lt; destruct OK; lia).
      apply BODY.
  Qed.
End LoopF.

(* Route (C): the proof of the footprint contract without the shadow_rw premise. The old script never used that
   premise. *)
Theorem reac_ctrl_checksum_verify_F_holds_on : reac_ctrl_checksum_verify_contract_F_on.
Proof.
  unfold reac_ctrl_checksum_verify_contract_F_on, REAC_CTRL_CHECKSUM_VERIFY, REAC_CTRL_CHECKSUM_VERIFY_FRAME.
  intros RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    p lo bs Hp Hp50 -> Hlen HB ST HLO HD HCE HADR HW RFR RGOT RCELL RDAT RSH.
  pose proof (rt_asan_rt m _ HCE HW) as HRT.
  pose proof (rt_shadow_rd m (p + 18) 32 _ HADR (fun x Hx => HW x (or_intror (or_intror Hx)))) as HSR.
  pose proof (rt_addressable m (p + 18) 32 HADR) as HAD.
  unfold GOT_CELL_K, CELL_K in RGOT, RCELL.
  set (off := ASAN_K) in HRT, HSR, HAD, RSH. clearbody off.
  pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. change (bv_modulus 64) with (2^64) in Rsp.
  pose proof ST as (ST0 & _ & _).
  assert (WV : forall x, bv_unsigned sp - 16 <= x < bv_unsigned sp -> wview rsegs m (wa x) <> None)
    by (intros x Hx; destruct ST as (_ & _ & H); exact (proj1 (H x ltac:(lia)))).
  carve_frame 16%nat ST.
  step. step.
  match goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) => rename mm into m1 end.
  step.
  rewrite (rc_neq0_64 p) by lia.
  pose proof (asan_rt_munch rsegs m m1 _ _ off _ _ HRT MU (fun x Hx => Hx)) as HRT1.
  pose proof (asan_shadow_rd_munch rsegs m m1 off (p + 18) 32 _ _ HSR MU (fun x Hx => Hx)) as HSR1.
  pose proof (asan_addressable_munch rsegs m m1 off (p + 18) 32 _ _ HAD HSR MU (fun x Hx => Hx)) as HAD1.
  pose proof (asan_rt_got_read rsegs m1 _ _ off _ HRT1) as RG.
  pose proof (asan_rt_cell_read rsegs m1 _ _ off _ HRT1) as RC.
  unfold GOT_CELL_K, CELL_K in RG, RC.
  step. step. step. step.
  clear RG RC.
  step.
  rewrite (unsigned_lit p) by lia. rewrite (zb_lxor_ones p) by lia.
  step. step. step. step.
  change (Z_to_bv 64 0) with (Z_to_bv 64 (psum bs 0)).
  change (Z_to_bv 64 18) with (Z_to_bv 64 (18 + Z.of_nat 0)).
  replace (p + 18) with (p + 18 + Z.of_nat 0) by lia.
  refine (loop_F ra _ gp tp t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m1 p off bs _ _ RNG
            Hp Hp50 Hlen HB HSR1 HAD1 RDAT RSH _ 32 0 t0 a7 eq_refl ltac:(lia)).
  intros x5 x10 x14 x15 x17.
  pose proof (psum_range bs 32) as R32. change (Z.of_nat 32) with 32 in R32.
  step. step. step. step. step. step.
  rewrite (fin_a0 (psum bs 32)) by lia.
  release_frame FR ST (bv_unsigned sp).
  apply evtF_done. cbv beta. unfold blocksum. do 9 eexists. split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|].
  split; [intros HI; exact (rc_mem_inv_frame rsegs m m1 _ _ HI MU WV) | exact ST].
Qed.

(* The old footprint statement, from the one without the premise. *)
Theorem reac_ctrl_checksum_verify_holds_F : reac_ctrl_checksum_verify_contract_F.
Proof. exact (reac_ctrl_checksum_verify_contract_F_of_on reac_ctrl_checksum_verify_F_holds_on). Qed.

(* The contract without the premise as a corollary of the footprint form without it
   (reac_ctrl_checksum_verify_contract_of_F_on). *)
Theorem reac_ctrl_checksum_verify_holds_of_F_on : reac_ctrl_checksum_verify_contract_on.
Proof. exact (reac_ctrl_checksum_verify_contract_of_F_on reac_ctrl_checksum_verify_F_holds_on). Qed.

(* The old contract as a corollary: evtF_evt of the footprint form at RNG_all, each rng premise by rng_all. *)
Theorem reac_ctrl_checksum_verify_holds_of_F : reac_ctrl_checksum_verify_contract.
Proof.
  unfold reac_ctrl_checksum_verify_contract.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    p lo bs Hp Hp50 Ha0 Hlen HB ST HLO HD HCE HSW HADR HW.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. change (bv_modulus 64) with (2^64) in Rsp.
  pose proof ST as (ST0 & _ & _).
  pose proof HLO as HLO'. unfold REAC_CTRL_CHECKSUM_VERIFY_FRAME in HLO'.
  apply (evtF_evt rsegs RNG_all).
  apply (reac_ctrl_checksum_verify_holds_F RNG_all ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
    s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m p lo bs); try assumption;
    apply rng_all; unfold REAC_CTRL_CHECKSUM_VERIFY_FRAME, GOT_CELL_K, CELL_K, ASAN_K;
    Z.div_mod_to_equations; lia.
Qed.
