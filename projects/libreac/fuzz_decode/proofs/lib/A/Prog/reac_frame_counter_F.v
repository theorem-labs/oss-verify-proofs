From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes ZBridge.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.A Require Import Img0 AsanCells.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.A.Prog Require Import AsanKA AsanKAProof reac_frame_counter_c.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.A.Prog Require Import reac_frame_counter_F_c.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Lib Require Import ExecF StepF.
Import ListNotations.
Open Scope Z_scope.

(* Proof of reac_frame_counter_contract_F (A image, entry 0x811ec). It follows reac_frame_counter.v step for step,
   with StepF's step. Each access side goal is closed from an rng fact for exactly the accessed range: before the
   shadow byte load at h = ((a0 + off) >> 3) + ASAN_K the proof adds rng RNG h 1 (a sub-range of the shadow range),
   and before the byte load at w = a0 + 15 it adds rng RNG w 1 (a sub-range of the buffer). *)

(* The shadow byte of a + i, 0 <= i < n, lies in the shadow range of the buffer [a, a + n). *)
Lemma counter_shadow_byte_rng : forall RNG a n i, 0 <= i < n ->
  ExecF.rng RNG (shadow_addr a) (shadow_addr (a + n - 1) - shadow_addr a + 1) ->
  ExecF.rng RNG (shadow_addr (a + i)) 1.
Proof.
  intros RNG a n i Hi H. eapply rng_sub'; [exact H|]. unfold shadow_addr. Z.div_mod_to_equations. lia.
Qed.

Theorem reac_frame_counter_holds_F : reac_frame_counter_contract_F.
Proof.
  unfold reac_frame_counter_contract_F, REAC_FRAME_COUNTER, REAC_FRAME_COUNTER_FRAME.
  intros RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m bs
    lo LEN BA ST HLO D0 APS1 APS2 CELLS SRW DG DS ADR RFR RGOT RCELL RBUF RSH.
  pose proof (counter_shadow_byte_rng RNG (bv_unsigned a0 + 14) 2 0 ltac:(lia) RSH) as RS14.
  pose proof (counter_shadow_byte_rng RNG (bv_unsigned a0 + 14) 2 1 ltac:(lia) RSH) as RS15.
  rewrite Z.add_0_r in RS14.
  replace (bv_unsigned a0 + 14 + 1) with (bv_unsigned a0 + 15) in RS15 by lia.
  clear RSH.
  pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. unfold bv_modulus in Rsp. change (2 ^ Z.of_N 64) with (2^64) in Rsp.
  pose proof (bv_unsigned_in_range 64 a0) as Ra0. unfold bv_modulus in Ra0. change (2 ^ Z.of_N 64) with (2^64) in Ra0.
  destruct CELLS as (CK & GCK & _).
  destruct ADR as (P0 & N0 & PE & AB).
  destruct (AB 0 ltac:(lia)) as (APP14 & k14 & MK14 & SK14).
  destruct (AB 1 ltac:(lia)) as (APP15 & k15 & MK15 & SK15).
  unfold off_stk, GOT_CELL_K, CELL_K, ASAN_K, shadow_addr, shadow_ok in *.
  unfold ASAN_K in RS14, RS15.
  unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in APP14, APP15, APS1, APS2.
  rewrite Z.add_0_r in APP14, MK14, SK14.
  replace (bv_unsigned a0 + 14 + 1) with (bv_unsigned a0 + 15) in APP15, MK15, SK15 by lia.
  pose proof BA as (BA0 & BA1 & _).
  pose proof (conj BA (conj CK GCK)) as PK. clear BA CK GCK.
  carve_frame 16%nat ST.
  step. step.
  destruct PK as (BA & CK & GCK).
  match goal with MU' : munch _ m ?m1 |- _ => rename MU' into MU1; rename m1 into m0 end.
  pose proof (bytes_tp m m0 _ _ 625984 (le8 (wa 658872)) MU1 ltac:(rewrite length_le8; lia) GCK) as GOT0.
  pose proof (bytes_tp m m0 _ _ 658872 (le8 (wa 2147450880)) MU1 ltac:(rewrite length_le8; lia) CK) as SV0.
  assert (RDG : ov_read_bytes rsegs m0 (wa 625984) 8 = Some (le8 (wa 658872))).
  { replace (wa 625984) with (wa (625984 + 0)) by reflexivity.
    rewrite (bytes_at_read rsegs m0 625984 _ 0 8 GOT0 ltac:(lia)) by (rewrite length_le8; lia). reflexivity. }
  assert (RDS : ov_read_bytes rsegs m0 (wa 658872) 8 = Some (le8 (wa 2147450880))).
  { replace (wa 658872) with (wa (658872 + 0)) by reflexivity.
    rewrite (bytes_at_read rsegs m0 658872 _ 0 8 SV0 ltac:(lia)) by (rewrite length_le8; lia). reflexivity. }
  pose proof (mrd_tp m m0 _ _ ((bv_unsigned a0 + 14) / 8 + 2147450880) _ MU1
    ltac:(Z.div_mod_to_equations; lia) ltac:(Z.div_mod_to_equations; lia) MK14) as M14.
  pose proof (mrd_tp m m0 _ _ ((bv_unsigned a0 + 15) / 8 + 2147450880) _ MU1
    ltac:(Z.div_mod_to_equations; lia) ltac:(Z.div_mod_to_equations; lia) MK15) as M15.
  pose proof (mrd_tp m m0 _ _ (bv_unsigned a0 + Z.of_nat 14) _ MU1 ltac:(lia) ltac:(lia)
    (bytes_nth m _ bs 14 BA ltac:(lia))) as F14.
  pose proof (mrd_tp m m0 _ _ (bv_unsigned a0 + Z.of_nat 15) _ MU1 ltac:(lia) ltac:(lia)
    (bytes_nth m _ bs 15 BA ltac:(lia))) as F15.
  change (Z.of_nat 14) with 14 in F14. change (Z.of_nat 15) with 15 in F15.
  remember (nth 14 bs (Z_to_bv 8 0)) as b14 eqn:E14.
  remember (nth 15 bs (Z_to_bv 8 0)) as b15 eqn:E15.
  pose proof (Z.mod_pos_bound (bv_unsigned a0 + 14) 8 ltac:(lia)) as MB14.
  pose proof (Z.mod_pos_bound (bv_unsigned a0 + 15) 8 ltac:(lia)) as MB15.
  step. step. step.
  step. gen_addi a0 w14 U14.
  step. gen_shr w14 g14 G14. rewrite U14 in G14.
  step. gen_addi g14 h14 H14.
  pose proof (rng_sub' _ _ _ (bv_unsigned h14) 1 RS14 ltac:(lia)) as RH14.
  pose proof (rdw0 m0 h14 _ _ M14 ltac:(lia)) as R. step. clear R.
  step.
  destruct SK14 as [C|[C Cu]].
  1: rewrite sxb_eq0, (proj2 (Z.eqb_eq _ _) C); cbn [negb].
  2: rewrite sxb_eq0, (proj2 (Z.eqb_neq (bv_signed k14) 0) ltac:(lia)); cbn [negb]; step; step;
     rewrite land7, U14, (lts_low ((bv_unsigned a0 + 14) mod 8) k14 MB14), (proj2 (Z.ltb_lt _ _) C); cbn [negb].
  all: step; gen_addi a0 w15 U15.
  all: pose proof (rng_sub' _ _ _ (bv_unsigned w15) 1 RBUF ltac:(lia)) as RW15.
  all: step; gen_shr w15 g15 G15.
  all: rewrite U15 in G15.
  all: step; gen_addi g15 h15 H15.
  all: pose proof (rng_sub' _ _ _ (bv_unsigned h15) 1 RS15 ltac:(lia)) as RH15.
  all: pose proof (rdw0 m0 h15 _ _ M15 ltac:(lia)) as R; step; clear R.
  all: pose proof (rdw m0 a0 14 _ _ F14 ltac:(lia)) as R; step; clear R.
  all: step.
  all: destruct SK15 as [C'|[C' Cu']].
  1, 3: rewrite sxb_eq0, (proj2 (Z.eqb_eq _ _) C'); cbn [negb].
  all: try (rewrite sxb_eq0, (proj2 (Z.eqb_neq (bv_signed k15) 0) ltac:(lia)); cbn [negb]; step; step;
     rewrite land7, U15, (lts_low ((bv_unsigned a0 + 15) mod 8) k15 MB15), (proj2 (Z.ltb_lt _ _) C'); cbn [negb]).
  all: pose proof (rdw0 m0 w15 _ _ F15 ltac:(lia)) as R; step; clear R.
  all: do 7 step; apply evtF_done.
  all: pose proof (byte_range b14) as X14; pose proof (byte_range b15) as X15.
  all: unfold zxb; rewrite !zxb_u, lor_bytes16.
  all: rewrite (unsigned_lit (Z.shiftl (bv_unsigned b14 + 256 * bv_unsigned b15) 48))
         by (rewrite Z.shiftl_mul_pow2 by lia; lia).
  all: rewrite (Z.shiftl_mul_pow2 (bv_unsigned b14 + 256 * bv_unsigned b15) 48) by lia.
  all: rewrite (Z.shiftr_div_pow2 ((bv_unsigned b14 + 256 * bv_unsigned b15) * 2 ^ 48) 48) by lia.
  all: rewrite Z.div_mul by lia.
  all: replace (bv_unsigned b14 + 256 * bv_unsigned b15) with (counter_result bs)
         by (unfold counter_result, counter_byte; rewrite <- E14, <- E15; reflexivity).
  all: do 5 eexists; split; [reflexivity|]; split; [eassumption|]; split; [eassumption|].
  all: release_frame FR ST (bv_unsigned sp); exact ST.
Qed.

(* The footprint form implies the old contract: take the footprint that allows every access. *)
Corollary reac_frame_counter_holds_of_F : reac_frame_counter_contract.
Proof.
  unfold reac_frame_counter_contract.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m bs lo
    LEN BA ST HLO D0 APS1 APS2 CELLS SRW DG DS ADR.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. unfold bv_modulus in Rsp. change (2 ^ Z.of_N 64) with (2^64) in Rsp.
  pose proof (stk_lo_nonneg _ _ _ _ ST) as L0.
  pose proof ADR as (P0 & N0 & PE & _).
  apply (ExecF.evtF_evt rsegs RNG_all).
  pose proof reac_frame_counter_holds_F as H. unfold reac_frame_counter_contract_F in H.
  apply H; try assumption.
  - apply rng_all; unfold REAC_FRAME_COUNTER_FRAME in *; lia.
  - apply rng_all; unfold GOT_CELL_K; lia.
  - apply rng_all; unfold CELL_K; lia.
  - apply rng_all; unfold APPMEM_END in PE; lia.
  - unfold shadow_addr, ASAN_K, APPMEM_END in *. apply rng_all; Z.div_mod_to_equations; lia.
Qed.
