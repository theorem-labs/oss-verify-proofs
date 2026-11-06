From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes ZBridge.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Import Img0 AsanRT.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require Import RcModel RcLib RcAsan RcAsanLib.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require Import RcAsanRT reac_ctrl_checksum_verify_c.
Import ListNotations.
Open Scope Z_scope.

Section Loop.
  Variables (ra sp1 gp tp t0 t1 t2 s0 s1 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (p off : Z) (bs : list byte) (W : list ivl)
    (Q : machine_state -> Prop).
  Hypothesis Hp : 0 < p.
  Hypothesis Hp50 : p + 50 <= 2^64.
  Hypothesis Hlen : length bs = 32%nat.
  Hypothesis HB : bytes_at rsegs m (p + 18) bs.
  Hypothesis HSR : asan_shadow_rd rsegs m off (p + 18) 32 W.
  Hypothesis HAD : asan_addressable rsegs m off (p + 18) 32.

  Abbreviation ST pc x10 x11 x13 x14 x15 x16 :=
    (MS (mkR ra sp1 gp tp t0 t1 t2 s0 s1 x10 x11 (Z_to_bv 64 off) x13 x14 x15 x16 a7
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 pc) fc None m (seg_rom rsegs)).

  Hypothesis EXIT : forall x10 x13 x14 x15 x16,
    evt rsegs Q (ST 0x83504 x10 (Z_to_bv 64 (psum bs 32)) x13 x14 x15 x16).

  Lemma loop : forall n i x15 x16,
    (i + n = 32)%nat -> (0 < n)%nat ->
    evt rsegs Q (ST 0x834cc (Z_to_bv 64 (p + 18 + Z.of_nat i)) (Z_to_bv 64 (psum bs i))
                    (Z_to_bv 64 (p + 18 + Z.of_nat i)) (Z_to_bv 64 (32 - Z.of_nat i)) x15 x16).
  Proof using Hp Hp50 Hlen HB HSR HAD EXIT.
    induction n as [|n IH]; intros i x15 x16 Hin Hn; [lia|].
    assert (BODY : forall y15 y16,
      evt rsegs Q (ST 0x834dc (Z_to_bv 64 (p + 18 + Z.of_nat i)) (Z_to_bv 64 (psum bs i))
                      (Z_to_bv 64 (p + 18 + Z.of_nat i)) (Z_to_bv 64 (32 - Z.of_nat i)) y15 y16)).
    { intros y15 y16.
      pose proof (rd_byte rsegs m (p + 18) bs i HB ltac:(lia)) as RD.
      pose proof (psum_range bs i) as PR.
      step. step. step. step. step.
      rewrite psum_S_zxb.
      step.
      rewrite (rc_eqb0_signed (32 - Z.of_nat i + -1)) by lia.
      destruct n as [|n].
      - replace (32 - Z.of_nat i + -1 =? 0) with true by (symmetry; apply Z.eqb_eq; lia).
        cbn [negb]. step.
        replace i with 31%nat in * by lia.
        apply EXIT.
      - replace (32 - Z.of_nat i + -1 =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
        cbn [negb].
        replace (p + 18 + Z.of_nat i + 1) with (p + 18 + Z.of_nat (S i)) by lia.
        replace (32 - Z.of_nat i + -1) with (32 - Z.of_nat (S i)) by lia.
        apply (IH (S i)); lia. }
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
End Loop.

Theorem reac_ctrl_checksum_verify_holds : reac_ctrl_checksum_verify_contract.
Proof.
  unfold reac_ctrl_checksum_verify_contract, REAC_CTRL_CHECKSUM_VERIFY, REAC_CTRL_CHECKSUM_VERIFY_FRAME.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    p lo bs Hp Hp50 -> Hlen HB ST HLO HD HCE HSW HADR HW.
  pose proof (rt_asan_rt m _ HCE HW) as HRT.
  pose proof (rt_shadow_rd m (p + 18) 32 _ HADR (fun x Hx => HW x (or_intror (or_intror Hx)))) as HSR.
  pose proof (rt_addressable m (p + 18) 32 HADR) as HAD.
  set (off := ASAN_K) in HRT, HSR, HAD. clearbody off.
  pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. change (bv_modulus 64) with (2^64) in Rsp.
  pose proof ST as (ST0 & _ & _).
  assert (WV : forall x, bv_unsigned sp - 16 <= x < bv_unsigned sp -> wview rsegs m (wa x) <> None)
    by (intros x Hx; destruct ST as (_ & _ & H); exact (proj1 (H x ltac:(lia)))).
  carve_frame 16%nat ST.
  step. step.
  match goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => rename mm into m1 end.
  pose proof (asan_rt_munch rsegs m m1 _ _ off _ _ HRT MU (fun x Hx => Hx)) as HRT1.
  pose proof (asan_shadow_rd_munch rsegs m m1 off (p + 18) 32 _ _ HSR MU (fun x Hx => Hx)) as HSR1.
  pose proof (asan_addressable_munch rsegs m m1 off (p + 18) 32 _ _ HAD HSR MU (fun x Hx => Hx)) as HAD1.
  pose proof (asan_rt_got_read rsegs m1 _ _ off _ HRT1) as RG.
  pose proof (asan_rt_cell_read rsegs m1 _ _ off _ HRT1) as RC.
  unfold GOT_CELL_K, CELL_K in RG, RC.
  step. step. step. step.
  clear RG RC.
  step. step. step.
  change (Z_to_bv 64 0) with (Z_to_bv 64 (psum bs 0)).
  change (Z_to_bv 64 32) with (Z_to_bv 64 (32 - Z.of_nat 0)).
  replace (p + 18) with (p + 18 + Z.of_nat 0) by lia.
  refine (loop ra _ gp tp t0 t1 t2 s0 s1 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m1 p off bs _ _
            Hp Hp50 Hlen HB HSR1 HAD1 _ 32 0 a5 a6 eq_refl ltac:(lia)).
  intros x10 x13 x14 x15 x16.
  pose proof (psum_range bs 32) as R32. change (Z.of_nat 32) with 32 in R32.
  step. step. step. step. step. step.
  rewrite (fin_a0 (psum bs 32)) by lia.
  release_frame FR ST (bv_unsigned sp).
  apply evt_done. cbv beta. unfold blocksum. do 7 eexists. split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|].
  split; [intros HI; exact (rc_mem_inv_frame rsegs m m1 _ _ HI MU WV) | exact ST].
Qed.
