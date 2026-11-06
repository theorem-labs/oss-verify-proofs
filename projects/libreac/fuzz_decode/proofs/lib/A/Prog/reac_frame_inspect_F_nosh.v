(* reac_frame_inspect: the footprint contract WITHOUT its `shadow_rw m` premise, image A.

   reac_frame_inspect_contract_F_nosh is reac_frame_inspect_contract_F (reac_frame_inspect_F_c.v, frozen, untouched) with the premise `shadow_rw m` (every shadow
   byte present; lib/A/AsanCells.v:32) removed and nothing else changed. reac_frame_inspect_holds_F_nosh is proved by the SAME
   script as reac_frame_inspect_holds_F (reac_frame_inspect_F.v), with only the hypothesis name SRW dropped from its intro / destruct patterns
   
   The original proof never uses SRW:
   its shadow loads read the bytes from the `addressable` premise. This is why callers need not supply whole-band
   shadow presence (a Theorem Labs lane 03:36Z / 03:43Z, same route as a Theorem Labs lane's for reac_braid_encode). *)
From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes ZBridge.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.A Require Import Img0 AsanCells.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.A.Prog Require Import AsanKA AsanKAProof reac_frame_inspect_c.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.A.Prog Require Import reac_frame_inspect_F_c.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Lib Require Import ExecF StepF.
Import ListNotations.
Open Scope Z_scope.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.A.Prog Require Import reac_frame_inspect_F.

Definition reac_frame_inspect_contract_F_nosh : Prop :=
  forall (RNG : ExecF.footprint)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (bs : list byte) (lo : Z),
    stk rsegs m lo (bv_unsigned sp) ->
    lo + REAC_FRAME_INSPECT_FRAME <= bv_unsigned sp ->
    (bv_unsigned a1 = 1492 ->
       length bs = 1492%nat /\ bytes_at rsegs m (bv_unsigned a0) bs /\
       off_stk sp REAC_FRAME_INSPECT_FRAME (bv_unsigned a0) 1492 /\
       app_mem (bv_unsigned sp - REAC_FRAME_INSPECT_FRAME) /\ app_mem (bv_unsigned sp - 1) /\
       asan_cells m /\ off_stk sp REAC_FRAME_INSPECT_FRAME GOT_CELL_K 8 /\
       off_stk sp REAC_FRAME_INSPECT_FRAME CELL_K 8 /\
       addressable m (bv_unsigned a0) 1492) ->
    ExecF.rng RNG (bv_unsigned sp - REAC_FRAME_INSPECT_FRAME) REAC_FRAME_INSPECT_FRAME ->
    (bv_unsigned a1 = 1492 -> ExecF.rng RNG GOT_CELL_K 8) ->
    (bv_unsigned a1 = 1492 -> ExecF.rng RNG CELL_K 8) ->
    (bv_unsigned a1 = 1492 -> ExecF.rng RNG (bv_unsigned a0) 1492) ->
    (bv_unsigned a1 = 1492 ->
       ExecF.rng RNG (shadow_addr (bv_unsigned a0))
         (shadow_addr (bv_unsigned a0 + 1492 - 1) - shadow_addr (bv_unsigned a0) + 1)) ->
    ExecF.evtF rsegs RNG
      (fun ms' => exists (a1' a2' a3' a4' : word) (m' : word -> option byte),
         ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (inspect_result (bv_unsigned a1) bs)) a1' a2' a3' a4'
                       a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (ret_pc ra) fc None m' (seg_rom rsegs) /\
         munch [(bv_unsigned sp - REAC_FRAME_INSPECT_FRAME, bv_unsigned sp)] m m' /\
         wmono rsegs m m' /\
         stk rsegs m' lo (bv_unsigned sp))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 REAC_FRAME_INSPECT) fc None m (seg_rom rsegs)).

Theorem reac_frame_inspect_holds_F_nosh : reac_frame_inspect_contract_F_nosh.
Proof.
  unfold reac_frame_inspect_contract_F_nosh, REAC_FRAME_INSPECT, REAC_FRAME_INSPECT_FRAME.
  intros RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m bs
    lo ST HLO HB RFR RGOT RCELL RBUF RSH.
  pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. unfold bv_modulus in Rsp. change (2 ^ Z.of_N 64) with (2^64) in Rsp.
  pose proof (bv_unsigned_in_range 64 a0) as Ra0. unfold bv_modulus in Ra0. change (2 ^ Z.of_N 64) with (2^64) in Ra0.
  destruct (Z.eq_dec (bv_unsigned a1) 1492) as [EL|NL].
  2: { clear RGOT RCELL RBUF RSH.
       carve_frame 16%nat ST.
       step. step. step. step. if_true.
       assert (W : inspect_result (bv_unsigned a1) bs = 0).
       { unfold inspect_result, inspect_wf. rewrite (proj2 (Z.eqb_neq _ _) NL). reflexivity. }
       do 6 step. apply evtF_done. rewrite W. do 5 eexists. split; [reflexivity|]. split; [eassumption|].
       split; [eassumption|]. release_frame FR ST (bv_unsigned sp). exact ST. }
  specialize (RGOT EL). specialize (RCELL EL). specialize (RBUF EL). specialize (RSH EL).
  pose proof (inspect_shadow_byte_rng RNG (bv_unsigned a0) 1492 12 ltac:(lia) RSH) as RS12.
  pose proof (inspect_shadow_byte_rng RNG (bv_unsigned a0) 1492 13 ltac:(lia) RSH) as RS13.
  pose proof (inspect_shadow_byte_rng RNG (bv_unsigned a0) 1492 1490 ltac:(lia) RSH) as RS90.
  pose proof (inspect_shadow_byte_rng RNG (bv_unsigned a0) 1492 1491 ltac:(lia) RSH) as RS91.
  pose proof (inspect_shadow_byte_rng RNG (bv_unsigned a0) 1492 14 ltac:(lia) RSH) as RS14.
  pose proof (inspect_shadow_byte_rng RNG (bv_unsigned a0) 1492 15 ltac:(lia) RSH) as RS15.
  clear RSH.
  destruct (HB EL) as (LEN & BA & D0 & APS1 & APS2 & CELLS & DG & DS & ADR).
  destruct CELLS as (CK & GCK & _).
  destruct ADR as (P0 & N0 & PE & AB).
  destruct (AB 12 ltac:(lia)) as (APP12 & k12 & MK12 & SK12).
  destruct (AB 13 ltac:(lia)) as (APP13 & k13 & MK13 & SK13).
  destruct (AB 1490 ltac:(lia)) as (APP90 & k90 & MK90 & SK90).
  destruct (AB 1491 ltac:(lia)) as (APP91 & k91 & MK91 & SK91).
  destruct (AB 14 ltac:(lia)) as (APP14 & k14 & MK14 & SK14).
  destruct (AB 15 ltac:(lia)) as (APP15 & k15 & MK15 & SK15).
  unfold off_stk, GOT_CELL_K, CELL_K, ASAN_K, shadow_addr, shadow_ok in *.
  unfold ASAN_K in RS12, RS13, RS90, RS91, RS14, RS15.
  unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in APP12, APP13, APP90, APP91, APP14, APP15, APS1, APS2.
  pose proof BA as (BA0 & BA1 & _).
  rewrite LEN in BA1. change (Z.of_nat 1492) with 1492 in BA1.
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
  (* A shadow address lies outside the stack frame: only Ra0, Rsp, APPi, APS1 and APS2 matter (as in
     reac_frame_inspect_F.v). The clear keeps Z.div_mod_to_equations and lia off the rest of the context. *)
  pose proof (mrd_tp m m0 _ _ ((bv_unsigned a0 + 12) / 8 + 2147450880) _ MU1
    ltac:(clear - Ra0; Z.div_mod_to_equations; lia)
    ltac:(clear - Ra0 Rsp APP12 APS1 APS2; Z.div_mod_to_equations; lia) MK12) as M12.
  pose proof (mrd_tp m m0 _ _ ((bv_unsigned a0 + 13) / 8 + 2147450880) _ MU1
    ltac:(clear - Ra0; Z.div_mod_to_equations; lia)
    ltac:(clear - Ra0 Rsp APP13 APS1 APS2; Z.div_mod_to_equations; lia) MK13) as M13.
  pose proof (mrd_tp m m0 _ _ ((bv_unsigned a0 + 1490) / 8 + 2147450880) _ MU1
    ltac:(clear - Ra0; Z.div_mod_to_equations; lia)
    ltac:(clear - Ra0 Rsp APP90 APS1 APS2; Z.div_mod_to_equations; lia) MK90) as M90.
  pose proof (mrd_tp m m0 _ _ ((bv_unsigned a0 + 1491) / 8 + 2147450880) _ MU1
    ltac:(clear - Ra0; Z.div_mod_to_equations; lia)
    ltac:(clear - Ra0 Rsp APP91 APS1 APS2; Z.div_mod_to_equations; lia) MK91) as M91.
  pose proof (mrd_tp m m0 _ _ ((bv_unsigned a0 + 14) / 8 + 2147450880) _ MU1
    ltac:(clear - Ra0; Z.div_mod_to_equations; lia)
    ltac:(clear - Ra0 Rsp APP14 APS1 APS2; Z.div_mod_to_equations; lia) MK14) as M14.
  pose proof (mrd_tp m m0 _ _ ((bv_unsigned a0 + 15) / 8 + 2147450880) _ MU1
    ltac:(clear - Ra0; Z.div_mod_to_equations; lia)
    ltac:(clear - Ra0 Rsp APP15 APS1 APS2; Z.div_mod_to_equations; lia) MK15) as M15.
  pose proof (mrd_tp m m0 _ _ (bv_unsigned a0 + Z.of_nat 12) _ MU1 ltac:(lia) ltac:(lia)
    (bytes_nth m _ bs 12 BA ltac:(lia))) as F12.
  pose proof (mrd_tp m m0 _ _ (bv_unsigned a0 + Z.of_nat 13) _ MU1 ltac:(lia) ltac:(lia)
    (bytes_nth m _ bs 13 BA ltac:(lia))) as F13.
  pose proof (mrd_tp m m0 _ _ (bv_unsigned a0 + Z.of_nat 1490) _ MU1 ltac:(lia) ltac:(lia)
    (bytes_nth m _ bs 1490 BA ltac:(lia))) as F90.
  pose proof (mrd_tp m m0 _ _ (bv_unsigned a0 + Z.of_nat 1491) _ MU1 ltac:(lia) ltac:(lia)
    (bytes_nth m _ bs 1491 BA ltac:(lia))) as F91.
  pose proof (mrd_tp m m0 _ _ (bv_unsigned a0 + Z.of_nat 14) _ MU1 ltac:(lia) ltac:(lia)
    (bytes_nth m _ bs 14 BA ltac:(lia))) as F14.
  pose proof (mrd_tp m m0 _ _ (bv_unsigned a0 + Z.of_nat 15) _ MU1 ltac:(lia) ltac:(lia)
    (bytes_nth m _ bs 15 BA ltac:(lia))) as F15.
  change (Z.of_nat 12) with 12 in F12. change (Z.of_nat 13) with 13 in F13.
  change (Z.of_nat 1490) with 1490 in F90. change (Z.of_nat 1491) with 1491 in F91.
  change (Z.of_nat 14) with 14 in F14. change (Z.of_nat 15) with 15 in F15.
  remember (nth 12 bs (Z_to_bv 8 0)) as b12 eqn:E12.
  remember (nth 13 bs (Z_to_bv 8 0)) as b13 eqn:E13.
  remember (nth 1490 bs (Z_to_bv 8 0)) as b90 eqn:E90.
  remember (nth 1491 bs (Z_to_bv 8 0)) as b91 eqn:E91.
  remember (nth 14 bs (Z_to_bv 8 0)) as b14 eqn:E14.
  remember (nth 15 bs (Z_to_bv 8 0)) as b15 eqn:E15.
  pose proof (Z.mod_pos_bound (bv_unsigned a0 + 12) 8 ltac:(lia)) as MB12.
  pose proof (Z.mod_pos_bound (bv_unsigned a0 + 13) 8 ltac:(lia)) as MB13.
  pose proof (Z.mod_pos_bound (bv_unsigned a0 + 1490) 8 ltac:(lia)) as MB90.
  pose proof (Z.mod_pos_bound (bv_unsigned a0 + 1491) 8 ltac:(lia)) as MB91.
  pose proof (Z.mod_pos_bound (bv_unsigned a0 + 14) 8 ltac:(lia)) as MB14.
  pose proof (Z.mod_pos_bound (bv_unsigned a0 + 15) 8 ltac:(lia)) as MB15.
  step. step. if_false.
  step. step. step.
  shadow_pass a0 m0 12 w12 g12 h12 U12 G12 H12 M12 k12 SK12 MB12 RBUF RS12 a4 x12.
  all: pose proof (rdw0 m0 w12 _ _ F12 ltac:(lia)) as R; step; clear R.
  all: step; step; if_cases Q12; zify_cond Q12; rewrite zxb_u in Q12.
  all: try (exit0 FR ST sp).
  all: shadow_pass a0 m0 13 w13 g13 h13 U13 G13 H13 M13 k13 SK13 MB13 RBUF RS13 x12 x13.
  all: pose proof (rdw0 m0 w13 _ _ F13 ltac:(lia)) as R; step; clear R.
  all: step; step; if_cases Q13; zify_cond Q13; rewrite zxb_u in Q13.
  all: try (exit0 FR ST sp).
  all: shadow_pass a0 m0 1490 w90 g90 h90 U90 G90 H90 M90 k90 SK90 MB90 RBUF RS90 x13 x90.
  all: pose proof (rdw0 m0 w90 _ _ F90 ltac:(lia)) as R; step; clear R.
  all: step; step; if_cases Q90; zify_cond Q90; rewrite zxb_u in Q90.
  all: try (exit0 FR ST sp).
  all: shadow_pass a0 m0 1491 w91 g91 h91 U91 G91 H91 M91 k91 SK91 MB91 RBUF RS91 x90 x91.
  all: pose proof (rdw0 m0 w91 _ _ F91 ltac:(lia)) as R; step; clear R.
  all: step; step; if_cases Q91; zify_cond Q91; rewrite zxb_u in Q91.
  all: try (exit0 FR ST sp).
  all: shadow_pass a0 m0 14 w14 g14 h14 U14 G14 H14 M14 k14 SK14 MB14 RBUF RS14 x91 x14.
  all: step; gen_addi a0 w15 U15.
  all: pose proof (rng_sub' _ _ _ (bv_unsigned w15) 1 RBUF ltac:(lia)) as RW15.
  all: step; gen_shr w15 g15 G15.
  all: rewrite U15 in G15.
  all: step; gen_addi g15 h15 H15.
  all: pose proof (rng_sub' _ _ _ (bv_unsigned h15) 1 RS15 ltac:(lia)) as RH15.
  all: pose proof (rdw0 m0 h15 _ _ M15 ltac:(lia)) as R; step; clear R.
  all: pose proof (rdw m0 a0 14 _ _ F14 ltac:(lia)) as R; step; clear R.
  all: step.
  all: sk_join a0 15 U15 k15 SK15 MB15 g15 x15.
  all: pose proof (rdw0 m0 w15 _ _ F15 ltac:(lia)) as R; step; clear R.
  all: do 9 step; apply evtF_done.
  all: assert (V : inspect_result (bv_unsigned a1) bs = 2^32 + (bv_unsigned b14 + 256 * bv_unsigned b15))
         by (unfold inspect_result, inspect_wf, inspect_counter, inspect_byte;
             rewrite EL, <- E12, <- E13, <- E90, <- E91, <- E14, <- E15, Q12, Q13, Q90, Q91; reflexivity).
  all: rewrite V; unfold zxb; rewrite !zxb_u.
  all: pose proof (byte_range b14) as X14; pose proof (byte_range b15) as X15.
  all: rewrite lor_bytes16, lor_pow32 by lia.
  all: replace (bv_unsigned b14 + 256 * bv_unsigned b15 + 4294967296)
         with (2^32 + (bv_unsigned b14 + 256 * bv_unsigned b15)) by lia.
  all: do 5 eexists; split; [reflexivity|]; split; [eassumption|]; split; [eassumption|].
  all: release_frame FR ST (bv_unsigned sp); exact ST.
Qed.

(* The footprint form implies the old contract: take the footprint that allows every access. *)
