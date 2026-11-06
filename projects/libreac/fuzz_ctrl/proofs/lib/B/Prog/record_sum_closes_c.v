From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require Import Img0 AsanRT.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require Import RcModel RcRec.
Import ListNotations.
Open Scope Z_scope.

Definition RECORD_SUM_CLOSES : Z := 0x83614.
Definition RECORD_SUM_CLOSES_FRAME : Z := 16.

Definition record_sum_closes_contract : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z) (bs : list byte),
    length bs = Z.to_nat (bv_unsigned a1) ->
    (bv_unsigned a1 = 0 \/
     (bv_unsigned a0 <> 0 /\ bv_unsigned a0 + bv_unsigned a1 <= 2^64 /\ bytes_at rsegs m (bv_unsigned a0) bs /\
      (bv_unsigned a0 + bv_unsigned a1 <= bv_unsigned sp - RECORD_SUM_CLOSES_FRAME \/
       bv_unsigned sp <= bv_unsigned a0))) ->
    stk rsegs m lo (bv_unsigned sp) -> lo + RECORD_SUM_CLOSES_FRAME <= bv_unsigned sp ->
    (1 <= bv_unsigned a1 -> asan_cells m) ->
    (1 <= bv_unsigned a1 -> shadow_rw m) ->
    (1 <= bv_unsigned a1 -> addressable m (bv_unsigned a0) (bv_unsigned a1)) ->
    (1 <= bv_unsigned a1 ->
     forall x, GOT_CELL_K <= x < GOT_CELL_K + 8 \/ CELL_K <= x < CELL_K + 8 \/ in_shadow x ->
       outside [(bv_unsigned sp - RECORD_SUM_CLOSES_FRAME, bv_unsigned sp)] x) ->
    evt rsegs
      (fun ms' => exists (t0' a1' a2' a3' a4' a5' a6' a7' : word) (m' : word -> option byte),
         ms' = MS (mkR ra sp gp tp t0' t1 t2 s0 s1 (Z_to_bv 64 (if recsum bs =? 0 then 1 else 0))
                       a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (ret_pc ra) fc None m' (seg_rom rsegs) /\
         munch [(bv_unsigned sp - RECORD_SUM_CLOSES_FRAME, bv_unsigned sp)] m m' /\
         wmono rsegs m m' /\ (mem_inv rsegs m -> mem_inv rsegs m') /\ stk rsegs m' lo (bv_unsigned sp))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 RECORD_SUM_CLOSES) fc None m (seg_rom rsegs)).

(* ---- the footprint form (RECIPE.md step 1 (a working note, not in this delivery)) ----
   The same run as an ExecF.evtF under a footprint RNG that holds every region the run reads or writes: the 16-byte
   frame (ra save/restore, on both paths); and, only when a1 >= 1 (the guard of asan_cells / addressable above; with
   a1 = 0 the run returns before any of these loads), the GOT cell and the runtime cell that hold the shadow offset
   (two 8-byte loads), the data range [a0, a0 + a1) (one 1-byte load per byte), and the byte-exact shadow span of that
   range (the inline check loads the single byte at (x >> 3) + ASAN_K for each byte x).
   record_sum_closes_contract_of_F gives the old statement back with RNG_all. *)
From Stdlib Require Import Lia.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import ExecF.

Definition record_sum_closes_contract_F : Prop :=
  forall (RNG : footprint)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z) (bs : list byte),
    length bs = Z.to_nat (bv_unsigned a1) ->
    (bv_unsigned a1 = 0 \/
     (bv_unsigned a0 <> 0 /\ bv_unsigned a0 + bv_unsigned a1 <= 2^64 /\ bytes_at rsegs m (bv_unsigned a0) bs /\
      (bv_unsigned a0 + bv_unsigned a1 <= bv_unsigned sp - RECORD_SUM_CLOSES_FRAME \/
       bv_unsigned sp <= bv_unsigned a0))) ->
    stk rsegs m lo (bv_unsigned sp) -> lo + RECORD_SUM_CLOSES_FRAME <= bv_unsigned sp ->
    (1 <= bv_unsigned a1 -> asan_cells m) ->
    (1 <= bv_unsigned a1 -> shadow_rw m) ->
    (1 <= bv_unsigned a1 -> addressable m (bv_unsigned a0) (bv_unsigned a1)) ->
    (1 <= bv_unsigned a1 ->
     forall x, GOT_CELL_K <= x < GOT_CELL_K + 8 \/ CELL_K <= x < CELL_K + 8 \/ in_shadow x ->
       outside [(bv_unsigned sp - RECORD_SUM_CLOSES_FRAME, bv_unsigned sp)] x) ->
    rng RNG (bv_unsigned sp - RECORD_SUM_CLOSES_FRAME) RECORD_SUM_CLOSES_FRAME ->
    (1 <= bv_unsigned a1 -> rng RNG GOT_CELL_K 8) ->
    (1 <= bv_unsigned a1 -> rng RNG CELL_K 8) ->
    (1 <= bv_unsigned a1 -> rng RNG (bv_unsigned a0) (bv_unsigned a1)) ->
    (1 <= bv_unsigned a1 ->
     rng RNG (bv_unsigned a0 / 8 + ASAN_K) ((bv_unsigned a0 + bv_unsigned a1 - 1) / 8 - bv_unsigned a0 / 8 + 1)) ->
    evtF rsegs RNG
      (fun ms' => exists (t0' a1' a2' a3' a4' a5' a6' a7' : word) (m' : word -> option byte),
         ms' = MS (mkR ra sp gp tp t0' t1 t2 s0 s1 (Z_to_bv 64 (if recsum bs =? 0 then 1 else 0))
                       a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (ret_pc ra) fc None m' (seg_rom rsegs) /\
         munch [(bv_unsigned sp - RECORD_SUM_CLOSES_FRAME, bv_unsigned sp)] m m' /\
         wmono rsegs m m' /\ (mem_inv rsegs m -> mem_inv rsegs m') /\ stk rsegs m' lo (bv_unsigned sp))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 RECORD_SUM_CLOSES) fc None m (seg_rom rsegs)).

(* The old statement is the _F statement at the footprint that admits every access (every rng premise by rng_all;
   the guarded ones from the a1 >= 1 side of the data premise, which bounds a0 + a1). *)
Lemma record_sum_closes_contract_of_F : record_sum_closes_contract_F -> record_sum_closes_contract.
Proof.
  intros HF ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m lo bs Hlen Hpre ST HLO HCE HSW HADR HW.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. change (bv_modulus 64) with (2^64) in Rsp.
  pose proof (bv_unsigned_in_range 64 a0) as Ra. change (bv_modulus 64) with (2^64) in Ra.
  pose proof (bv_unsigned_in_range 64 a1) as R1. change (bv_modulus 64) with (2^64) in R1.
  pose proof ST as (ST0 & _ & _).
  assert (Hqn : 1 <= bv_unsigned a1 -> bv_unsigned a0 + bv_unsigned a1 <= 2^64)
    by (intros H1; destruct Hpre as [H0 | (_ & H & _)]; lia).
  assert (RFR : rng RNG_all (bv_unsigned sp - RECORD_SUM_CLOSES_FRAME) RECORD_SUM_CLOSES_FRAME)
    by (apply rng_all; unfold RECORD_SUM_CLOSES_FRAME in *; lia).
  assert (RGK : 1 <= bv_unsigned a1 -> rng RNG_all GOT_CELL_K 8)
    by (intros _; apply rng_all; unfold GOT_CELL_K; lia).
  assert (RCK : 1 <= bv_unsigned a1 -> rng RNG_all CELL_K 8)
    by (intros _; apply rng_all; unfold CELL_K; lia).
  assert (RDAT : 1 <= bv_unsigned a1 -> rng RNG_all (bv_unsigned a0) (bv_unsigned a1))
    by (intros H1; specialize (Hqn H1); apply rng_all; lia).
  assert (RSH : 1 <= bv_unsigned a1 ->
                rng RNG_all (bv_unsigned a0 / 8 + ASAN_K)
                  ((bv_unsigned a0 + bv_unsigned a1 - 1) / 8 - bv_unsigned a0 / 8 + 1))
    by (intros H1; specialize (Hqn H1); apply rng_all; unfold ASAN_K; Z.div_mod_to_equations; lia).
  exact (evtF_evt rsegs RNG_all _ _
           (HF RNG_all ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
               F fc m lo bs Hlen Hpre ST HLO HCE HSW HADR HW RFR RGK RCK RDAT RSH)).
Qed.
