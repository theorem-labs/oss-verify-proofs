From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes ZBridge.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.A Require Import Img0 AsanCells.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.A.Prog Require Import AsanKA AsanKAProof reac_frame_is_reac_c.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.A.Prog Require Import reac_frame_is_reac_F_c.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Lib Require Import ExecF StepF.
Import ListNotations.
Open Scope Z_scope.

(* Proof of reac_frame_is_reac_contract_F (A image, entry 0x81154). It follows reac_frame_is_reac.v step for step,
   with StepF's step. Each access side goal is closed from an rng fact for exactly the accessed range: before the
   shadow byte load at h = ((a0 + off) >> 3) + ASAN_K the proof adds rng RNG h 1 (a sub-range of the shadow range),
   and before the byte load at w = a0 + off it adds rng RNG w 1 (a sub-range of the buffer). *)

(* The shadow byte of a + i, 0 <= i < n, lies in the shadow range of the buffer [a, a + n). *)
Lemma is_reac_shadow_byte_rng : forall RNG a n i, 0 <= i < n ->
  ExecF.rng RNG (shadow_addr a) (shadow_addr (a + n - 1) - shadow_addr a + 1) ->
  ExecF.rng RNG (shadow_addr (a + i)) 1.
Proof.
  intros RNG a n i Hi H. eapply rng_sub'; [exact H|]. unfold shadow_addr. Z.div_mod_to_equations. lia.
Qed.

Theorem reac_frame_is_reac_holds_F : reac_frame_is_reac_contract_F.
Proof.
  unfold reac_frame_is_reac_contract_F, REAC_FRAME_IS_REAC, REAC_FRAME_IS_REAC_FRAME.
  intros RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m bs
    lo ST HLO HB RFR RGOT RCELL RBUF RSH.
  pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. unfold bv_modulus in Rsp. change (2 ^ Z.of_N 64) with (2^64) in Rsp.
  pose proof (bv_unsigned_in_range 64 a0) as Ra0. unfold bv_modulus in Ra0. change (2 ^ Z.of_N 64) with (2^64) in Ra0.
  carve_frame 16%nat ST.
  step. step. step. step. if_cases HZ.
  - zify_cond HZ.
    assert (W : is_reac_result (bv_unsigned a0) (bv_unsigned a1) bs = 0).
    { unfold is_reac_result. rewrite (proj2 (Z.eqb_eq _ _) HZ). reflexivity. }
    do 4 step. apply evtF_done. rewrite W. do 5 eexists. split; [reflexivity|]. split; [eassumption|].
    split; [eassumption|]. release_frame FR ST (bv_unsigned sp). exact ST.
  - zify_cond HZ.
    step. step. if_cases HL.
    + zify_cond HL.
      assert (W : is_reac_result (bv_unsigned a0) (bv_unsigned a1) bs = 0).
      { unfold is_reac_result. rewrite (proj2 (Z.eqb_neq _ _) HZ), (proj2 (Z.ltb_lt _ _) HL). reflexivity. }
      do 4 step. apply evtF_done. rewrite W. do 5 eexists. split; [reflexivity|]. split; [eassumption|].
      split; [eassumption|]. release_frame FR ST (bv_unsigned sp). exact ST.
    + zify_cond HL.
      specialize (RGOT HZ HL). specialize (RCELL HZ HL). specialize (RBUF HZ HL). specialize (RSH HZ HL).
      pose proof (is_reac_shadow_byte_rng RNG (bv_unsigned a0 + 12) 2 0 ltac:(lia) RSH) as RS12.
      pose proof (is_reac_shadow_byte_rng RNG (bv_unsigned a0 + 12) 2 1 ltac:(lia) RSH) as RS13.
      rewrite Z.add_0_r in RS12.
      replace (bv_unsigned a0 + 12 + 1) with (bv_unsigned a0 + 13) in RS13 by lia.
      clear RSH.
      destruct (HB HZ HL) as (LEN & BA & D0 & APS1 & APS2 & CELLS & SRW & DG & DS & ADR).
      destruct CELLS as (CK & GCK & _).
      destruct ADR as (P0 & N0 & PE & AB).
      destruct (AB 0 ltac:(lia)) as (APP12 & k12 & MK12 & SK12).
      destruct (AB 1 ltac:(lia)) as (APP13 & k13 & MK13 & SK13).
      unfold off_stk, GOT_CELL_K, CELL_K, ASAN_K, shadow_addr, shadow_ok in *.
      unfold ASAN_K in RS12, RS13.
      unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in APP12, APP13, APS1, APS2.
      rewrite Z.add_0_r in APP12, MK12, SK12.
      replace (bv_unsigned a0 + 12 + 1) with (bv_unsigned a0 + 13) in APP13, MK13, SK13 by lia.
      match goal with MU' : munch _ m ?m1 |- _ => rename MU' into MU1; rename m1 into m0 end.
      pose proof BA as (BA0 & BA1 & _).
      pose proof (bytes_tp m m0 _ _ 625984 (le8 (wa 658872)) MU1 ltac:(rewrite length_le8; lia) GCK) as GOT0.
      pose proof (bytes_tp m m0 _ _ 658872 (le8 (wa 2147450880)) MU1 ltac:(rewrite length_le8; lia) CK) as SV0.
      assert (RDG : ov_read_bytes rsegs m0 (wa 625984) 8 = Some (le8 (wa 658872))).
      { replace (wa 625984) with (wa (625984 + 0)) by reflexivity.
        rewrite (bytes_at_read rsegs m0 625984 _ 0 8 GOT0 ltac:(lia)) by (rewrite length_le8; lia). reflexivity. }
      assert (RDS : ov_read_bytes rsegs m0 (wa 658872) 8 = Some (le8 (wa 2147450880))).
      { replace (wa 658872) with (wa (658872 + 0)) by reflexivity.
        rewrite (bytes_at_read rsegs m0 658872 _ 0 8 SV0 ltac:(lia)) by (rewrite length_le8; lia). reflexivity. }
      pose proof (mrd_tp m m0 _ _ ((bv_unsigned a0 + 12) / 8 + 2147450880) _ MU1
        ltac:(Z.div_mod_to_equations; lia) ltac:(Z.div_mod_to_equations; lia) MK12) as M12.
      pose proof (mrd_tp m m0 _ _ ((bv_unsigned a0 + 13) / 8 + 2147450880) _ MU1
        ltac:(Z.div_mod_to_equations; lia) ltac:(Z.div_mod_to_equations; lia) MK13) as M13.
      pose proof (mrd_tp m m0 _ _ (bv_unsigned a0 + Z.of_nat 12) _ MU1 ltac:(lia) ltac:(lia)
        (bytes_nth m _ bs 12 BA ltac:(lia))) as F12.
      pose proof (mrd_tp m m0 _ _ (bv_unsigned a0 + Z.of_nat 13) _ MU1 ltac:(lia) ltac:(lia)
        (bytes_nth m _ bs 13 BA ltac:(lia))) as F13.
      change (Z.of_nat 12) with 12 in F12. change (Z.of_nat 13) with 13 in F13.
      step. step. step.
      step. gen_addi a0 w12 U12.
      pose proof (rng_sub' _ _ _ (bv_unsigned w12) 1 RBUF ltac:(lia)) as RW12.
      step. gen_shr w12 g12 G12.
      rewrite U12 in G12.
      step. gen_addi g12 h12 H12.
      pose proof (rng_sub' _ _ _ (bv_unsigned h12) 1 RS12 ltac:(lia)) as RH12.
      pose proof (rdw0 m0 h12 _ _ M12 ltac:(lia)) as R. step. clear R.
      step.
      pose proof (Z.mod_pos_bound (bv_unsigned a0 + 12) 8 ltac:(lia)) as MB12.
      pose proof (Z.mod_pos_bound (bv_unsigned a0 + 13) 8 ltac:(lia)) as MB13.
      destruct SK12 as [C|[C Cu]].
      1: rewrite sxb_eq0, (proj2 (Z.eqb_eq _ _) C); cbn [negb].
      2: rewrite sxb_eq0, (proj2 (Z.eqb_neq (bv_signed k12) 0) ltac:(lia)); cbn [negb]; step; step;
         rewrite land7, U12, (lts_low ((bv_unsigned a0 + 12) mod 8) k12 MB12), (proj2 (Z.ltb_lt _ _) C); cbn [negb].
      all: remember (nth 12 bs (Z_to_bv 8 0)) as b12 eqn:E12.
      all: remember (nth 13 bs (Z_to_bv 8 0)) as b13 eqn:E13.
      all: pose proof (rdw0 m0 w12 _ _ F12 ltac:(lia)) as R; step; clear R.
      all: step; step; if_cases HC; zify_cond HC; rewrite zxb_u in HC.
      1, 3: assert (W : is_reac_result (bv_unsigned a0) (bv_unsigned a1) bs = 0)
              by (unfold is_reac_result, is_reac_byte; rewrite <- E12;
                  rewrite (proj2 (Z.eqb_neq _ _) HZ), (proj2 (Z.ltb_ge _ _) HL), (proj2 (Z.eqb_neq _ _) HC);
                  reflexivity);
            do 5 step; apply evtF_done; rewrite W; do 5 eexists; split; [reflexivity|]; split; [eassumption|];
            split; [eassumption|]; release_frame FR ST (bv_unsigned sp); exact ST.
      all: step; gen_addi a0 w13 U13.
      all: pose proof (rng_sub' _ _ _ (bv_unsigned w13) 1 RBUF ltac:(lia)) as RW13.
      all: step; gen_shr w13 g13 G13.
      all: rewrite U13 in G13.
      all: step; gen_addi g13 h13 H13.
      all: pose proof (rng_sub' _ _ _ (bv_unsigned h13) 1 RS13 ltac:(lia)) as RH13.
      all: pose proof (rdw0 m0 h13 _ _ M13 ltac:(lia)) as R; step; clear R.
      all: step.
      all: destruct SK13 as [C'|[C' Cu']].
      1, 3: rewrite sxb_eq0, (proj2 (Z.eqb_eq _ _) C'); cbn [negb].
      all: try (rewrite sxb_eq0, (proj2 (Z.eqb_neq (bv_signed k13) 0) ltac:(lia)); cbn [negb]; step; step;
         rewrite land7, U13, (lts_low ((bv_unsigned a0 + 13) mod 8) k13 MB13), (proj2 (Z.ltb_lt _ _) C'); cbn [negb]).
      all: pose proof (rdw0 m0 w13 _ _ F13 ltac:(lia)) as R; step; clear R.
      all: do 7 step; apply evtF_done.
      all: assert (A0 : v_sltiu (Z_to_bv 64 (bv_unsigned (zxb b13) + -25)) 1
                     = Z_to_bv 64 (is_reac_result (bv_unsigned a0) (bv_unsigned a1) bs)) by
             (unfold v_sltiu, is_reac_result, is_reac_byte, zxb; rewrite <- E12, <- E13, zxb_u;
              rewrite (proj2 (Z.eqb_neq _ _) HZ), (proj2 (Z.ltb_ge _ _) HL), HC;
              pose proof (byte_range b13) as X13;
              destruct (Z.eq_dec (bv_unsigned b13) 25) as [E|E];
              [ rewrite E; vm_compute; reflexivity
              | rewrite (proj2 (Z.eqb_neq _ _) E), andb_false_r;
                rewrite unsigned_lit_wrap; change (bv_wrap 64 1) with 1;
                replace ((bv_unsigned b13 + -25) mod 2 ^ 64 <? 1) with false; [reflexivity|];
                symmetry; apply Z.ltb_ge; Z.div_mod_to_equations; lia ]).
      all: rewrite A0; do 5 eexists; split; [reflexivity|]; split; [eassumption|]; split; [eassumption|].
      all: release_frame FR ST (bv_unsigned sp); exact ST.
Qed.

(* The footprint form implies the old contract: take the footprint that allows every access. *)
Corollary reac_frame_is_reac_holds_of_F : reac_frame_is_reac_contract.
Proof.
  unfold reac_frame_is_reac_contract.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m bs lo
    ST HLO HB.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. unfold bv_modulus in Rsp. change (2 ^ Z.of_N 64) with (2^64) in Rsp.
  pose proof (stk_lo_nonneg _ _ _ _ ST) as L0.
  apply (ExecF.evtF_evt rsegs RNG_all).
  pose proof reac_frame_is_reac_holds_F as H. unfold reac_frame_is_reac_contract_F in H.
  apply H; [exact ST | exact HLO | exact HB | | | | |].
  - apply rng_all; unfold REAC_FRAME_IS_REAC_FRAME in *; lia.
  - intros _ _. apply rng_all; unfold GOT_CELL_K; lia.
  - intros _ _. apply rng_all; unfold CELL_K; lia.
  - intros HZ HL. destruct (HB HZ HL) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & P0 & N0 & PE & _).
    apply rng_all; unfold APPMEM_END in PE; lia.
  - intros HZ HL. destruct (HB HZ HL) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & P0 & N0 & PE & _).
    unfold shadow_addr, ASAN_K, APPMEM_END in *. apply rng_all; Z.div_mod_to_equations; lia.
Qed.
