From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require Import Img0 AsanRT.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require Import RcRec.
Import ListNotations.
Open Scope Z_scope.

Definition DT1_HEAD : Z := 0x875e8.
Definition DT1_HEAD_FRAME : Z := 16.

Definition dt1_head_contract : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z),
    bv_unsigned a0 + 20 <= 2^64 ->
    wr_at rsegs m (bv_unsigned a0) 20 ->
    stk rsegs m lo (bv_unsigned sp) -> lo + DT1_HEAD_FRAME <= bv_unsigned sp ->
    (bv_unsigned a0 + 20 <= bv_unsigned sp - DT1_HEAD_FRAME \/ bv_unsigned sp <= bv_unsigned a0) ->
    asan_cells m -> shadow_rw m ->
    addressable m (bv_unsigned a0) 20 ->
    (forall x, GOT_CELL_K <= x < GOT_CELL_K + 8 \/ CELL_K <= x < CELL_K + 8 \/ in_shadow x ->
       outside [(bv_unsigned sp - DT1_HEAD_FRAME, bv_unsigned sp); (bv_unsigned a0, bv_unsigned a0 + 20)] x) ->
    evt rsegs
      (fun ms' => exists (a0' a1' a2' a4' a5' a6' a7' : word) (m' : word -> option byte),
         ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0' a1' a2' a3 a4' a5' a6' a7'
                       s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (ret_pc ra) fc None m' (seg_rom rsegs)
         /\ bytes_at rsegs m' (bv_unsigned a0) (dt1_bytes (bv_unsigned a1) (bv_unsigned a2) (bv_unsigned a3))
         /\ munch [(bv_unsigned sp - DT1_HEAD_FRAME, bv_unsigned sp); (bv_unsigned a0, bv_unsigned a0 + 20)] m m'
         /\ wmono rsegs m m'
         /\ (mem_inv rsegs m -> mem_inv rsegs m')
         /\ stk rsegs m' lo (bv_unsigned sp))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 DT1_HEAD) fc None m (seg_rom rsegs)).

From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import ExecF.

(* The footprint form of dt1_head, moved here from lib/B/Prog/build_dt1_singleF.v with RNG as the first binder (the
   binder order of the other footprint forms, and the order dt1_head_F.v's dt1_head_holds_F introduces): the premises
   of dt1_head_contract are unchanged, then one rng premise per region that run reads or writes: its 16-byte frame
   below sp; the runtime words [RT_LO, RT_HI), which hold the GOT cell and the cell of the shadow offset it reads;
   the 20 bytes at o, which it writes; and the byte-exact shadow span of those 20 bytes, which is enough because that
   run reads its shadow bytes one at a time (dt1_head.v, dt1_head_shadow: ov_read_bytes .. 1). *)
Definition dt1_head_contract_F : Prop :=
  forall (RNG : footprint)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z),
    bv_unsigned a0 + 20 <= 2^64 ->
    wr_at rsegs m (bv_unsigned a0) 20 ->
    stk rsegs m lo (bv_unsigned sp) -> lo + DT1_HEAD_FRAME <= bv_unsigned sp ->
    (bv_unsigned a0 + 20 <= bv_unsigned sp - DT1_HEAD_FRAME \/ bv_unsigned sp <= bv_unsigned a0) ->
    asan_cells m -> shadow_rw m ->
    addressable m (bv_unsigned a0) 20 ->
    (forall x, GOT_CELL_K <= x < GOT_CELL_K + 8 \/ CELL_K <= x < CELL_K + 8 \/ in_shadow x ->
       outside [(bv_unsigned sp - DT1_HEAD_FRAME, bv_unsigned sp); (bv_unsigned a0, bv_unsigned a0 + 20)] x) ->
    (* the footprint *)
    rng RNG (bv_unsigned sp - DT1_HEAD_FRAME) DT1_HEAD_FRAME ->
    rng RNG RT_LO (RT_HI - RT_LO) ->
    rng RNG (bv_unsigned a0) 20 ->
    rng RNG (bv_unsigned a0 / 8 + ASAN_K) ((bv_unsigned a0 + 19) / 8 - bv_unsigned a0 / 8 + 1) ->
    evtF rsegs RNG
      (fun ms' => exists (a0' a1' a2' a4' a5' a6' a7' : word) (m' : word -> option byte),
         ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0' a1' a2' a3 a4' a5' a6' a7'
                       s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (ret_pc ra) fc None m' (seg_rom rsegs)
         /\ bytes_at rsegs m' (bv_unsigned a0) (dt1_bytes (bv_unsigned a1) (bv_unsigned a2) (bv_unsigned a3))
         /\ munch [(bv_unsigned sp - DT1_HEAD_FRAME, bv_unsigned sp); (bv_unsigned a0, bv_unsigned a0 + 20)] m m'
         /\ wmono rsegs m m'
         /\ (mem_inv rsegs m -> mem_inv rsegs m')
         /\ stk rsegs m' lo (bv_unsigned sp))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 DT1_HEAD) fc None m (seg_rom rsegs)).

(* Route (C) (a Theorem Labs lane 2026-10-29 09:20Z; wave lead a Theorem Labs lane; a Theorem Labs lane's brief dt1-on-B): this run reads and
   stores NO shadow byte THROUGH the universal `shadow_rw m` premise. Measured (from a working branch 5c355e74408):
   dt1_head.v (a version not in this delivery) / dt1_head_F.v (a version not in this delivery) introduce it as HSW and dt1_head.v (a version not in this delivery) / dt1_head_F.v (a version not in this delivery) clear it unused; the
   20 shadow checks read their bytes through `addressable m a0 20` (rt_shadow_rd / rt_addressable of RcAsanRT.v), and
   the run stores no shadow byte (its munch is the 16-byte frame and the 20 bytes at a0). So the _on forms DROP the
   premise and name no region: they are the two statements above WITHOUT `shadow_rw m ->` (the line
   `asan_cells m -> shadow_rw m ->` becomes `asan_cells m ->`); nothing else changes, and the posts never mention
   shadow_rw. Image A has no twin (lib/A/Prog has no dt1_head file; A's build_dt1_single takes no dt1_head
   contract); the form is the dropped one of image B's other leaves (a working branch 5c355e74408). The old
   statements follow by the bridges dt1_head_contract_of_on and dt1_head_contract_F_of_on. *)
Definition dt1_head_contract_on : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z),
    bv_unsigned a0 + 20 <= 2^64 ->
    wr_at rsegs m (bv_unsigned a0) 20 ->
    stk rsegs m lo (bv_unsigned sp) -> lo + DT1_HEAD_FRAME <= bv_unsigned sp ->
    (bv_unsigned a0 + 20 <= bv_unsigned sp - DT1_HEAD_FRAME \/ bv_unsigned sp <= bv_unsigned a0) ->
    asan_cells m ->
    addressable m (bv_unsigned a0) 20 ->
    (forall x, GOT_CELL_K <= x < GOT_CELL_K + 8 \/ CELL_K <= x < CELL_K + 8 \/ in_shadow x ->
       outside [(bv_unsigned sp - DT1_HEAD_FRAME, bv_unsigned sp); (bv_unsigned a0, bv_unsigned a0 + 20)] x) ->
    evt rsegs
      (fun ms' => exists (a0' a1' a2' a4' a5' a6' a7' : word) (m' : word -> option byte),
         ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0' a1' a2' a3 a4' a5' a6' a7'
                       s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (ret_pc ra) fc None m' (seg_rom rsegs)
         /\ bytes_at rsegs m' (bv_unsigned a0) (dt1_bytes (bv_unsigned a1) (bv_unsigned a2) (bv_unsigned a3))
         /\ munch [(bv_unsigned sp - DT1_HEAD_FRAME, bv_unsigned sp); (bv_unsigned a0, bv_unsigned a0 + 20)] m m'
         /\ wmono rsegs m m'
         /\ (mem_inv rsegs m -> mem_inv rsegs m')
         /\ stk rsegs m' lo (bv_unsigned sp))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 DT1_HEAD) fc None m (seg_rom rsegs)).

Lemma dt1_head_contract_of_on : dt1_head_contract_on -> dt1_head_contract.
Proof. intros H. unfold dt1_head_contract. intros. apply H; assumption. Qed.

Definition dt1_head_contract_F_on : Prop :=
  forall (RNG : footprint)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z),
    bv_unsigned a0 + 20 <= 2^64 ->
    wr_at rsegs m (bv_unsigned a0) 20 ->
    stk rsegs m lo (bv_unsigned sp) -> lo + DT1_HEAD_FRAME <= bv_unsigned sp ->
    (bv_unsigned a0 + 20 <= bv_unsigned sp - DT1_HEAD_FRAME \/ bv_unsigned sp <= bv_unsigned a0) ->
    asan_cells m ->
    addressable m (bv_unsigned a0) 20 ->
    (forall x, GOT_CELL_K <= x < GOT_CELL_K + 8 \/ CELL_K <= x < CELL_K + 8 \/ in_shadow x ->
       outside [(bv_unsigned sp - DT1_HEAD_FRAME, bv_unsigned sp); (bv_unsigned a0, bv_unsigned a0 + 20)] x) ->
    (* the footprint *)
    rng RNG (bv_unsigned sp - DT1_HEAD_FRAME) DT1_HEAD_FRAME ->
    rng RNG RT_LO (RT_HI - RT_LO) ->
    rng RNG (bv_unsigned a0) 20 ->
    rng RNG (bv_unsigned a0 / 8 + ASAN_K) ((bv_unsigned a0 + 19) / 8 - bv_unsigned a0 / 8 + 1) ->
    evtF rsegs RNG
      (fun ms' => exists (a0' a1' a2' a4' a5' a6' a7' : word) (m' : word -> option byte),
         ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0' a1' a2' a3 a4' a5' a6' a7'
                       s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (ret_pc ra) fc None m' (seg_rom rsegs)
         /\ bytes_at rsegs m' (bv_unsigned a0) (dt1_bytes (bv_unsigned a1) (bv_unsigned a2) (bv_unsigned a3))
         /\ munch [(bv_unsigned sp - DT1_HEAD_FRAME, bv_unsigned sp); (bv_unsigned a0, bv_unsigned a0 + 20)] m m'
         /\ wmono rsegs m m'
         /\ (mem_inv rsegs m -> mem_inv rsegs m')
         /\ stk rsegs m' lo (bv_unsigned sp))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 DT1_HEAD) fc None m (seg_rom rsegs)).

Lemma dt1_head_contract_F_of_on : dt1_head_contract_F_on -> dt1_head_contract_F.
Proof. intros H. unfold dt1_head_contract_F. intros. apply H; assumption. Qed.
