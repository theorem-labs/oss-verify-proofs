From Stdlib Require Import ZArith List.
From Stdlib Require Import Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require Import Img0 AsanRT.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require Import RcModel RcRec.
Import ListNotations.
Open Scope Z_scope.

Definition REAC_CTRL_RECORD_CKSUM_STAMP : Z := 0x83c1c.
Definition REAC_CTRL_RECORD_CKSUM_STAMP_FRAME : Z := 16.

Definition reac_ctrl_record_cksum_stamp_contract : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z) (bs : list byte),
    1 <= bv_unsigned a1 ->
    bv_unsigned a0 <> 0 ->
    bv_unsigned a0 + bv_unsigned a1 <= 2^64 ->
    length bs = Z.to_nat (bv_unsigned a1 - 1) ->
    bytes_at rsegs m (bv_unsigned a0) bs ->
    wr_at rsegs m (bv_unsigned a0 + bv_unsigned a1 - 1) 1 ->
    (bv_unsigned a0 + bv_unsigned a1 <= bv_unsigned sp - REAC_CTRL_RECORD_CKSUM_STAMP_FRAME \/
     bv_unsigned sp <= bv_unsigned a0) ->
    stk rsegs m lo (bv_unsigned sp) -> lo + REAC_CTRL_RECORD_CKSUM_STAMP_FRAME <= bv_unsigned sp ->
    asan_cells m -> shadow_rw m ->
    addressable m (bv_unsigned a0) (bv_unsigned a1) ->
    (forall x, GOT_CELL_K <= x < GOT_CELL_K + 8 \/ CELL_K <= x < CELL_K + 8 \/ in_shadow x ->
       outside [(bv_unsigned sp - REAC_CTRL_RECORD_CKSUM_STAMP_FRAME, bv_unsigned sp);
                (bv_unsigned a0 + bv_unsigned a1 - 1, bv_unsigned a0 + bv_unsigned a1)] x) ->
    evt rsegs
      (fun ms' => exists (t0' t1' a0' a1' a2' a3' a4' a5' a6' a7' : word) (m' : word -> option byte),
         ms' = MS (mkR ra sp gp tp t0' t1' t2 s0 s1 a0' a1' a2' a3' a4' a5' a6' a7'
                       s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (ret_pc ra) fc None m' (seg_rom rsegs)
         /\ bytes_at rsegs m' (bv_unsigned a0 + bv_unsigned a1 - 1) [Z_to_bv 8 (stampck bs)]
         /\ bytes_at rsegs m' (bv_unsigned a0) bs
         /\ recsum (bs ++ [Z_to_bv 8 (stampck bs)]) = 0
         /\ munch [(bv_unsigned sp - REAC_CTRL_RECORD_CKSUM_STAMP_FRAME, bv_unsigned sp);
                   (bv_unsigned a0 + bv_unsigned a1 - 1, bv_unsigned a0 + bv_unsigned a1)] m m'
         /\ wmono rsegs m m'
         /\ (mem_inv rsegs m -> mem_inv rsegs m')
         /\ stk rsegs m' lo (bv_unsigned sp))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 REAC_CTRL_RECORD_CKSUM_STAMP) fc None m (seg_rom rsegs)).

(* ---- the footprint form (RECIPE.md step 1 (a working note, not in this delivery)) ----
   The same run as an ExecF.evtF under a footprint RNG that holds every region the run reads or writes: the 16-byte
   frame; the GOT cell and the runtime cell that hold the shadow offset (the outside premise above names the same two
   cells); the data range [a0, a0 + a1); and the byte-exact shadow span of that range (the instrumented check loads
   the byte at (x >> 3) + ASAN_K for each checked byte x).
   reac_ctrl_record_cksum_stamp_contract_of_F gives the old statement back with RNG_all. *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import ExecF.

Definition reac_ctrl_record_cksum_stamp_contract_F : Prop :=
  forall (RNG : footprint)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z) (bs : list byte),
    1 <= bv_unsigned a1 ->
    bv_unsigned a0 <> 0 ->
    bv_unsigned a0 + bv_unsigned a1 <= 2^64 ->
    length bs = Z.to_nat (bv_unsigned a1 - 1) ->
    bytes_at rsegs m (bv_unsigned a0) bs ->
    wr_at rsegs m (bv_unsigned a0 + bv_unsigned a1 - 1) 1 ->
    (bv_unsigned a0 + bv_unsigned a1 <= bv_unsigned sp - REAC_CTRL_RECORD_CKSUM_STAMP_FRAME \/
     bv_unsigned sp <= bv_unsigned a0) ->
    stk rsegs m lo (bv_unsigned sp) -> lo + REAC_CTRL_RECORD_CKSUM_STAMP_FRAME <= bv_unsigned sp ->
    asan_cells m -> shadow_rw m ->
    addressable m (bv_unsigned a0) (bv_unsigned a1) ->
    (forall x, GOT_CELL_K <= x < GOT_CELL_K + 8 \/ CELL_K <= x < CELL_K + 8 \/ in_shadow x ->
       outside [(bv_unsigned sp - REAC_CTRL_RECORD_CKSUM_STAMP_FRAME, bv_unsigned sp);
                (bv_unsigned a0 + bv_unsigned a1 - 1, bv_unsigned a0 + bv_unsigned a1)] x) ->
    rng RNG (bv_unsigned sp - REAC_CTRL_RECORD_CKSUM_STAMP_FRAME) REAC_CTRL_RECORD_CKSUM_STAMP_FRAME ->
    rng RNG GOT_CELL_K 8 -> rng RNG CELL_K 8 ->
    rng RNG (bv_unsigned a0) (bv_unsigned a1) ->
    rng RNG (bv_unsigned a0 / 8 + ASAN_K)
            ((bv_unsigned a0 + bv_unsigned a1 - 1) / 8 - bv_unsigned a0 / 8 + 1) ->
    evtF rsegs RNG
      (fun ms' => exists (t0' t1' a0' a1' a2' a3' a4' a5' a6' a7' : word) (m' : word -> option byte),
         ms' = MS (mkR ra sp gp tp t0' t1' t2 s0 s1 a0' a1' a2' a3' a4' a5' a6' a7'
                       s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (ret_pc ra) fc None m' (seg_rom rsegs)
         /\ bytes_at rsegs m' (bv_unsigned a0 + bv_unsigned a1 - 1) [Z_to_bv 8 (stampck bs)]
         /\ bytes_at rsegs m' (bv_unsigned a0) bs
         /\ recsum (bs ++ [Z_to_bv 8 (stampck bs)]) = 0
         /\ munch [(bv_unsigned sp - REAC_CTRL_RECORD_CKSUM_STAMP_FRAME, bv_unsigned sp);
                   (bv_unsigned a0 + bv_unsigned a1 - 1, bv_unsigned a0 + bv_unsigned a1)] m m'
         /\ wmono rsegs m m'
         /\ (mem_inv rsegs m -> mem_inv rsegs m')
         /\ stk rsegs m' lo (bv_unsigned sp))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 REAC_CTRL_RECORD_CKSUM_STAMP) fc None m (seg_rom rsegs)).

(* The old statement is the _F statement at the footprint that admits every access (every rng premise by rng_all). *)
Lemma reac_ctrl_record_cksum_stamp_contract_of_F :
  reac_ctrl_record_cksum_stamp_contract_F -> reac_ctrl_record_cksum_stamp_contract.
Proof.
  intros HF ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m lo bs Hn Hq Hqn Hlen HB HW HD ST HLO HCE HSW HADR HWO.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. change (bv_modulus 64) with (2^64) in Rsp.
  pose proof (bv_unsigned_in_range 64 a0) as Ra. change (bv_modulus 64) with (2^64) in Ra.
  pose proof ST as (ST0 & _ & _).
  assert (RFR : rng RNG_all (bv_unsigned sp - REAC_CTRL_RECORD_CKSUM_STAMP_FRAME)
                  REAC_CTRL_RECORD_CKSUM_STAMP_FRAME)
    by (apply rng_all; unfold REAC_CTRL_RECORD_CKSUM_STAMP_FRAME in *; lia).
  assert (RGK : rng RNG_all GOT_CELL_K 8) by (apply rng_all; unfold GOT_CELL_K; lia).
  assert (RCK : rng RNG_all CELL_K 8) by (apply rng_all; unfold CELL_K; lia).
  assert (RDAT : rng RNG_all (bv_unsigned a0) (bv_unsigned a1)) by (apply rng_all; lia).
  assert (RSH : rng RNG_all (bv_unsigned a0 / 8 + ASAN_K)
                  ((bv_unsigned a0 + bv_unsigned a1 - 1) / 8 - bv_unsigned a0 / 8 + 1))
    by (apply rng_all; unfold ASAN_K; Z.div_mod_to_equations; lia).
  exact (evtF_evt rsegs RNG_all _ _
           (HF RNG_all ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
               F fc m lo bs Hn Hq Hqn Hlen HB HW HD ST HLO HCE HSW HADR HWO RFR RGK RCK RDAT RSH)).
Qed.


(* Route (C), CORRECTED to a Theorem Labs lane's premise-free form (a Theorem Labs lane 11:26Z measurement; approved a Theorem Labs lane 11:30Z): this run
   reads and stores NO shadow byte THROUGH the shadow_rw premise -- HSW was introduced in reac_ctrl_record_cksum_stampF.v (a version not in this delivery) and never used
   (its shadow bytes come from addressable, rt_shadow_rd) -- so the _on forms DROP `shadow_rw m ->` and name no
   region. Supersedes the narrowed form of c436911dedc, which carried a reac_ctrl_record_cksum_stamp_shadow_R; that
   predicate is gone. Same names as image A. *)
Definition reac_ctrl_record_cksum_stamp_contract_on : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z) (bs : list byte),
    1 <= bv_unsigned a1 ->
    bv_unsigned a0 <> 0 ->
    bv_unsigned a0 + bv_unsigned a1 <= 2^64 ->
    length bs = Z.to_nat (bv_unsigned a1 - 1) ->
    bytes_at rsegs m (bv_unsigned a0) bs ->
    wr_at rsegs m (bv_unsigned a0 + bv_unsigned a1 - 1) 1 ->
    (bv_unsigned a0 + bv_unsigned a1 <= bv_unsigned sp - REAC_CTRL_RECORD_CKSUM_STAMP_FRAME \/
     bv_unsigned sp <= bv_unsigned a0) ->
    stk rsegs m lo (bv_unsigned sp) -> lo + REAC_CTRL_RECORD_CKSUM_STAMP_FRAME <= bv_unsigned sp ->
    asan_cells m ->
    addressable m (bv_unsigned a0) (bv_unsigned a1) ->
    (forall x, GOT_CELL_K <= x < GOT_CELL_K + 8 \/ CELL_K <= x < CELL_K + 8 \/ in_shadow x ->
       outside [(bv_unsigned sp - REAC_CTRL_RECORD_CKSUM_STAMP_FRAME, bv_unsigned sp);
                (bv_unsigned a0 + bv_unsigned a1 - 1, bv_unsigned a0 + bv_unsigned a1)] x) ->
    evt rsegs
      (fun ms' => exists (t0' t1' a0' a1' a2' a3' a4' a5' a6' a7' : word) (m' : word -> option byte),
         ms' = MS (mkR ra sp gp tp t0' t1' t2 s0 s1 a0' a1' a2' a3' a4' a5' a6' a7'
                       s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (ret_pc ra) fc None m' (seg_rom rsegs)
         /\ bytes_at rsegs m' (bv_unsigned a0 + bv_unsigned a1 - 1) [Z_to_bv 8 (stampck bs)]
         /\ bytes_at rsegs m' (bv_unsigned a0) bs
         /\ recsum (bs ++ [Z_to_bv 8 (stampck bs)]) = 0
         /\ munch [(bv_unsigned sp - REAC_CTRL_RECORD_CKSUM_STAMP_FRAME, bv_unsigned sp);
                   (bv_unsigned a0 + bv_unsigned a1 - 1, bv_unsigned a0 + bv_unsigned a1)] m m'
         /\ wmono rsegs m m'
         /\ (mem_inv rsegs m -> mem_inv rsegs m')
         /\ stk rsegs m' lo (bv_unsigned sp))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 REAC_CTRL_RECORD_CKSUM_STAMP) fc None m (seg_rom rsegs)).

Lemma reac_ctrl_record_cksum_stamp_contract_of_on : reac_ctrl_record_cksum_stamp_contract_on -> reac_ctrl_record_cksum_stamp_contract.
Proof. intros H. unfold reac_ctrl_record_cksum_stamp_contract. intros. apply H; assumption. Qed.

Definition reac_ctrl_record_cksum_stamp_contract_F_on : Prop :=
  forall (RNG : footprint)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z) (bs : list byte),
    1 <= bv_unsigned a1 ->
    bv_unsigned a0 <> 0 ->
    bv_unsigned a0 + bv_unsigned a1 <= 2^64 ->
    length bs = Z.to_nat (bv_unsigned a1 - 1) ->
    bytes_at rsegs m (bv_unsigned a0) bs ->
    wr_at rsegs m (bv_unsigned a0 + bv_unsigned a1 - 1) 1 ->
    (bv_unsigned a0 + bv_unsigned a1 <= bv_unsigned sp - REAC_CTRL_RECORD_CKSUM_STAMP_FRAME \/
     bv_unsigned sp <= bv_unsigned a0) ->
    stk rsegs m lo (bv_unsigned sp) -> lo + REAC_CTRL_RECORD_CKSUM_STAMP_FRAME <= bv_unsigned sp ->
    asan_cells m ->
    addressable m (bv_unsigned a0) (bv_unsigned a1) ->
    (forall x, GOT_CELL_K <= x < GOT_CELL_K + 8 \/ CELL_K <= x < CELL_K + 8 \/ in_shadow x ->
       outside [(bv_unsigned sp - REAC_CTRL_RECORD_CKSUM_STAMP_FRAME, bv_unsigned sp);
                (bv_unsigned a0 + bv_unsigned a1 - 1, bv_unsigned a0 + bv_unsigned a1)] x) ->
    rng RNG (bv_unsigned sp - REAC_CTRL_RECORD_CKSUM_STAMP_FRAME) REAC_CTRL_RECORD_CKSUM_STAMP_FRAME ->
    rng RNG GOT_CELL_K 8 -> rng RNG CELL_K 8 ->
    rng RNG (bv_unsigned a0) (bv_unsigned a1) ->
    rng RNG (bv_unsigned a0 / 8 + ASAN_K)
            ((bv_unsigned a0 + bv_unsigned a1 - 1) / 8 - bv_unsigned a0 / 8 + 1) ->
    evtF rsegs RNG
      (fun ms' => exists (t0' t1' a0' a1' a2' a3' a4' a5' a6' a7' : word) (m' : word -> option byte),
         ms' = MS (mkR ra sp gp tp t0' t1' t2 s0 s1 a0' a1' a2' a3' a4' a5' a6' a7'
                       s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (ret_pc ra) fc None m' (seg_rom rsegs)
         /\ bytes_at rsegs m' (bv_unsigned a0 + bv_unsigned a1 - 1) [Z_to_bv 8 (stampck bs)]
         /\ bytes_at rsegs m' (bv_unsigned a0) bs
         /\ recsum (bs ++ [Z_to_bv 8 (stampck bs)]) = 0
         /\ munch [(bv_unsigned sp - REAC_CTRL_RECORD_CKSUM_STAMP_FRAME, bv_unsigned sp);
                   (bv_unsigned a0 + bv_unsigned a1 - 1, bv_unsigned a0 + bv_unsigned a1)] m m'
         /\ wmono rsegs m m'
         /\ (mem_inv rsegs m -> mem_inv rsegs m')
         /\ stk rsegs m' lo (bv_unsigned sp))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 REAC_CTRL_RECORD_CKSUM_STAMP) fc None m (seg_rom rsegs)).

Lemma reac_ctrl_record_cksum_stamp_contract_F_of_on : reac_ctrl_record_cksum_stamp_contract_F_on -> reac_ctrl_record_cksum_stamp_contract_F.
Proof. intros H. unfold reac_ctrl_record_cksum_stamp_contract_F. intros. apply H; assumption. Qed.