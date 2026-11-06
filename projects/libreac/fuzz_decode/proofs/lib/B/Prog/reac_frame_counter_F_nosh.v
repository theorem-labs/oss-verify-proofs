(* reac_frame_counter: the footprint contract WITHOUT its `shadow_rw m` premise, image B.

   reac_frame_counter_contract_F_nosh is reac_frame_counter_contract_F (reac_frame_counter_F_c.v, frozen, untouched) with the premise `shadow_rw m` (every shadow
   byte present; lib/B/AsanCells.v:32) removed and nothing else changed. reac_frame_counter_holds_F_nosh is proved by the SAME
   script as reac_frame_counter_holds_F (reac_frame_counter_F.v), with only the hypothesis name SRW dropped from its intro / destruct patterns
   
   The original proof never uses SRW:
   its shadow loads read the bytes from the `addressable` premise. This is why callers need not supply whole-band
   shadow presence (a Theorem Labs lane 03:36Z / 03:43Z, same route as a Theorem Labs lane's for reac_braid_encode). *)
From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes ZBridge.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.B Require Import Img0 AsanCells.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.B.Prog Require Import AsanKA AsanKAProof reac_frame_counter_c.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.B.Prog Require Import reac_frame_counter_F_c.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Lib Require Import ExecF StepF.
Import ListNotations.
Open Scope Z_scope.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.B.Prog Require Import reac_frame_counter_F.

Definition reac_frame_counter_contract_F_nosh : Prop :=
  forall (RNG : ExecF.footprint)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (bs : list byte) (lo : Z),
    (16 <= length bs)%nat ->
    bv_unsigned a0 <> 0 ->
    bytes_at rsegs m (bv_unsigned a0) bs ->
    stk rsegs m lo (bv_unsigned sp) ->
    lo + REAC_FRAME_COUNTER_FRAME <= bv_unsigned sp ->
    off_stk sp REAC_FRAME_COUNTER_FRAME (bv_unsigned a0) 16 ->
    app_mem (bv_unsigned sp - REAC_FRAME_COUNTER_FRAME) -> app_mem (bv_unsigned sp - 1) ->
    asan_cells m -> off_stk sp REAC_FRAME_COUNTER_FRAME GOT_CELL_K 8 ->
    off_stk sp REAC_FRAME_COUNTER_FRAME CELL_K 8 ->
    addressable m (bv_unsigned a0 + 14) 2 ->
    ExecF.rng RNG (bv_unsigned sp - REAC_FRAME_COUNTER_FRAME) REAC_FRAME_COUNTER_FRAME ->
    ExecF.rng RNG GOT_CELL_K 8 ->
    ExecF.rng RNG CELL_K 8 ->
    ExecF.rng RNG (bv_unsigned a0 + 14) 2 ->
    ExecF.rng RNG ((bv_unsigned a0 + 14) / 8 + ASAN_K) ((bv_unsigned a0 + 15) / 8 - (bv_unsigned a0 + 14) / 8 + 1) ->
    ExecF.evtF rsegs RNG
      (fun ms' => exists (a1' a2' a3' a4' : word) (m' : word -> option byte),
         ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (counter_result bs)) a1' a2' a3' a4'
                       a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (ret_pc ra) fc None m' (seg_rom rsegs) /\
         munch [(bv_unsigned sp - REAC_FRAME_COUNTER_FRAME, bv_unsigned sp)] m m' /\
         wmono rsegs m m' /\
         stk rsegs m' lo (bv_unsigned sp))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 REAC_FRAME_COUNTER) fc None m (seg_rom rsegs)).

Theorem reac_frame_counter_holds_F_nosh : reac_frame_counter_contract_F_nosh.
Proof.
  unfold reac_frame_counter_contract_F_nosh, REAC_FRAME_COUNTER, REAC_FRAME_COUNTER_FRAME.
  intros RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m bs lo
    LEN NZ BA ST HLO D0 APS1 APS2 CELLS DG DS ADR RFR RGC RCK RBUF RSH.
  pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. unfold bv_modulus in Rsp. change (2 ^ Z.of_N 64) with (2^64) in Rsp.
  pose proof (bv_unsigned_in_range 64 a0) as Ra0. unfold bv_modulus in Ra0. change (2 ^ Z.of_N 64) with (2^64) in Ra0.
  assert (DV : (bv_unsigned a0 + 14) / 8 <= (bv_unsigned a0 + 15) / 8) by (apply Z.div_le_mono; lia).
  destruct CELLS as (CK & GCK & _).
  destruct ADR as (P0 & N0 & PE & AB).
  destruct (AB 0 ltac:(lia)) as (APP14 & k14 & MK14 & SK14).
  destruct (AB 1 ltac:(lia)) as (APP15 & k15 & MK15 & SK15).
  unfold off_stk, GOT_CELL_K, CELL_K, ASAN_K, shadow_addr, shadow_ok in *.
  unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in APP14, APP15, APS1, APS2.
  rewrite Z.add_0_r in APP14, MK14, SK14.
  replace (bv_unsigned a0 + 14 + 1) with (bv_unsigned a0 + 15) in APP15, MK15, SK15 by lia.
  pose proof BA as (BA0 & BA1 & _).
  pose proof (conj BA (conj CK GCK)) as PK. clear BA CK GCK.
  carve_frame 16%nat ST.
  step. step.
  destruct PK as (BA & CK & GCK).
  match goal with MU' : munch _ m ?m1 |- _ => rename MU' into MU1; rename m1 into m0 end.
  pose proof (bytes_tp m m0 _ _ 627432 (le8 (wa 660280)) MU1 ltac:(rewrite length_le8; lia) GCK) as GOT0.
  pose proof (bytes_tp m m0 _ _ 660280 (le8 (wa 2147450880)) MU1 ltac:(rewrite length_le8; lia) CK) as SV0.
  assert (RDG : ov_read_bytes rsegs m0 (wa 627432) 8 = Some (le8 (wa 660280))).
  { replace (wa 627432) with (wa (627432 + 0)) by reflexivity.
    rewrite (bytes_at_read rsegs m0 627432 _ 0 8 GOT0 ltac:(lia)) by (rewrite length_le8; lia). reflexivity. }
  assert (RDS : ov_read_bytes rsegs m0 (wa 660280) 8 = Some (le8 (wa 2147450880))).
  { replace (wa 660280) with (wa (660280 + 0)) by reflexivity.
    rewrite (bytes_at_read rsegs m0 660280 _ 0 8 SV0 ltac:(lia)) by (rewrite length_le8; lia). reflexivity. }
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
  step. if_false. step. step. if_false. step. if_false.
  step. step. step.
  step. gen_addi a0 w14 U14.
  step. gen_shr w14 g14 G14. rewrite U14 in G14.
  step. gen_addi g14 h14 H14.
  pose proof (rdw0 m0 h14 _ _ M14 ltac:(lia)) as R. step. clear R.
  step.
  destruct SK14 as [C|[C Cu]].
  1: rewrite sxb_eq0, (proj2 (Z.eqb_eq _ _) C); cbn [negb].
  2: rewrite sxb_eq0, (proj2 (Z.eqb_neq (bv_signed k14) 0) ltac:(lia)); cbn [negb]; step; step;
     rewrite land7, U14, (lts_low ((bv_unsigned a0 + 14) mod 8) k14 MB14), (proj2 (Z.ltb_lt _ _) C); cbn [negb].
  all: step; gen_addi a0 w15 U15.
  all: step; gen_shr w15 g15 G15.
  all: rewrite U15 in G15.
  all: step; gen_addi g15 h15 H15.
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

(* The old contract from the footprint twin, with the footprint ExecF.RNG_all that holds every access. *)
