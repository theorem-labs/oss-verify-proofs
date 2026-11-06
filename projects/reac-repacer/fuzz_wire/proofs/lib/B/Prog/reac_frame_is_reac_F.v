From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes ZBridge.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.B Require Import Img0 AsanCells.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.B.Prog Require Import AsanKA AsanKAProof reac_frame_is_reac_c reac_frame_is_reac_F_c.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Lib Require Import ExecF StepF.
Import ListNotations.
Open Scope Z_scope.

(* Footprint twin of libreac/fuzz_decode's reac_frame_is_reac_holds (its lib/B/Prog/reac_frame_is_reac.v; B image,
   entry 0x8183c here): reac_frame_is_reac_holds_F proves
   reac_frame_is_reac_contract_F (reac_frame_is_reac_F_c.v), the run as an ExecF.evtF run under a footprint RNG.
   The proof follows that walk step for step, with StepF's step. Before each byte load it narrows the
   rng premise to the one byte the load reads, so that StepF's access check finds it by its address register. *)

(* The two shadow bytes of [p, p + 2) as two one-byte ranges. *)
Lemma shadow2_rng : forall RNG p,
  ExecF.rng RNG (p / 8 + 2147450880) ((p + 2 - 1) / 8 - p / 8 + 1) ->
  ExecF.rng RNG (p / 8 + 2147450880) 1 /\ ExecF.rng RNG ((p + 1) / 8 + 2147450880) 1.
Proof.
  intros RNG p H. split; apply (ExecF.rng_sub RNG _ _ _ _ H); clear H; Z.div_mod_to_equations; lia.
Qed.

Theorem reac_frame_is_reac_holds_F : reac_frame_is_reac_contract_F.
Proof.
  unfold reac_frame_is_reac_contract_F, REAC_FRAME_IS_REAC, REAC_FRAME_IS_REAC_FRAME.
  intros RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m bs lo
    ST HLO HB RFR HR.
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
      destruct (HB HZ HL) as (LEN & BA & D0 & APS1 & APS2 & CELLS & SRW & DG & DS & ADR).
      destruct (HR HZ HL) as (RGC & RCK & RBUF & RSH).
      destruct CELLS as (CK & GCK & _).
      destruct ADR as (P0 & N0 & PE & AB).
      destruct (AB 0 ltac:(lia)) as (APP12 & k12 & MK12 & SK12).
      destruct (AB 1 ltac:(lia)) as (APP13 & k13 & MK13 & SK13).
      unfold off_stk, GOT_CELL_K, CELL_K, ASAN_K, shadow_addr, shadow_ok in *.
      unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in APP12, APP13, APS1, APS2.
      rewrite Z.add_0_r in APP12, MK12, SK12.
      replace (bv_unsigned a0 + 12 + 1) with (bv_unsigned a0 + 13) in APP13, MK13, SK13 by lia.
      destruct (shadow2_rng RNG _ RSH) as (RS12 & RS13).
      replace (bv_unsigned a0 + 12 + 1) with (bv_unsigned a0 + 13) in RS13 by lia.
      match goal with MU' : munch _ m ?m1 |- _ => rename MU' into MU1; rename m1 into m0 end.
      pose proof BA as (BA0 & BA1 & _).
      pose proof (bytes_tp m m0 _ _ 0x98878 (le8 (wa 0xa07f8)) MU1 ltac:(rewrite length_le8; lia) GCK) as GOT0.
      pose proof (bytes_tp m m0 _ _ 0xa07f8 (le8 (wa 2147450880)) MU1 ltac:(rewrite length_le8; lia) CK) as SV0.
      assert (RDG : ov_read_bytes rsegs m0 (wa 0x98878) 8 = Some (le8 (wa 0xa07f8))).
      { replace (wa 0x98878) with (wa (0x98878 + 0)) by reflexivity.
        rewrite (bytes_at_read rsegs m0 0x98878 _ 0 8 GOT0 ltac:(lia)) by (rewrite length_le8; lia). reflexivity. }
      assert (RDS : ov_read_bytes rsegs m0 (wa 0xa07f8) 8 = Some (le8 (wa 2147450880))).
      { replace (wa 0xa07f8) with (wa (0xa07f8 + 0)) by reflexivity.
        rewrite (bytes_at_read rsegs m0 0xa07f8 _ 0 8 SV0 ltac:(lia)) by (rewrite length_le8; lia). reflexivity. }
      pose proof (mrd_tp m m0 _ _ ((bv_unsigned a0 + 12) / 8 + 2147450880) _ MU1
        ltac:(Z.div_mod_to_equations; lia) ltac:(Z.div_mod_to_equations; lia) MK12) as M12.
      pose proof (mrd_tp m m0 _ _ ((bv_unsigned a0 + 13) / 8 + 2147450880) _ MU1
        ltac:(Z.div_mod_to_equations; lia) ltac:(Z.div_mod_to_equations; lia) MK13) as M13.
      pose proof (mrd_tp m m0 _ _ (bv_unsigned a0 + Z.of_nat 12) _ MU1 ltac:(lia) ltac:(lia)
        (bytes_nth m _ bs 12 BA ltac:(lia))) as F12.
      pose proof (mrd_tp m m0 _ _ (bv_unsigned a0 + Z.of_nat 13) _ MU1 ltac:(lia) ltac:(lia)
        (bytes_nth m _ bs 13 BA ltac:(lia))) as F13.
      change (Z.of_nat 12) with 12 in F12. change (Z.of_nat 13) with 13 in F13.
      step. step. if_false.
      step. step. step.
      step. gen_addi a0 w12 U12.
      assert (RW12 : ExecF.rng RNG (bv_unsigned w12) 1) by (apply (ExecF.rng_sub RNG _ _ _ _ RBUF); lia).
      step. gen_shr w12 g12 G12.
      rewrite U12 in G12.
      step. gen_addi g12 h12 H12.
      assert (RH12 : ExecF.rng RNG (bv_unsigned h12) 1) by (apply (ExecF.rng_sub RNG _ _ _ _ RS12); lia).
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
      all: step; step; if_false.
      all: step; gen_addi a0 w13 U13.
      all: assert (RW13 : ExecF.rng RNG (bv_unsigned w13) 1) by (apply (ExecF.rng_sub RNG _ _ _ _ RBUF); lia).
      all: step; gen_shr w13 g13 G13.
      all: rewrite U13 in G13.
      all: step; gen_addi g13 h13 H13.
      all: assert (RH13 : ExecF.rng RNG (bv_unsigned h13) 1) by (apply (ExecF.rng_sub RNG _ _ _ _ RS13); lia).
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

(* The twin implies the original: take the footprint RNG_all, which holds every access. *)
Theorem reac_frame_is_reac_holds_of_F : reac_frame_is_reac_contract.
Proof.
  unfold reac_frame_is_reac_contract.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m bs lo
    ST HLO HB.
  apply (ExecF.evtF_evt rsegs RNG_all).
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. unfold bv_modulus in Rsp. change (2 ^ Z.of_N 64) with (2^64) in Rsp.
  pose proof (bv_unsigned_in_range 64 a0) as Ra0. unfold bv_modulus in Ra0. change (2 ^ Z.of_N 64) with (2^64) in Ra0.
  pose proof (stk_lo_nonneg _ _ _ _ ST) as Hlo.
  apply (reac_frame_is_reac_holds_F RNG_all ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9
           s10 s11 t3 t4 t5 t6 F fc m bs lo ST HLO HB).
  - apply rng_all; unfold REAC_FRAME_IS_REAC_FRAME in *; lia.
  - intros HZ HL. destruct (HB HZ HL) as (LEN & (B0 & B1 & _) & _).
    unfold GOT_CELL_K, CELL_K, ASAN_K.
    split; [|split; [|split]]; apply rng_all; try lia.
    all: clear HB; Z.div_mod_to_equations; lia.
Qed.
