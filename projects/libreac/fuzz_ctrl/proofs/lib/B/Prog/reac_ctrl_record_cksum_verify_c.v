From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require Import Img0 AsanRT.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require Import RcModel RcRec.
Import ListNotations.
Open Scope Z_scope.

Definition REAC_CTRL_RECORD_CKSUM_VERIFY : Z := 0x83cfc.
Definition REAC_CTRL_RECORD_CKSUM_VERIFY_FRAME : Z := 16.

Definition reac_ctrl_record_cksum_verify_contract : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z) (bs : list byte),
    length bs = Z.to_nat (bv_unsigned a1) ->
    (bv_unsigned a1 = 0 \/
     (bv_unsigned a0 <> 0 /\ bv_unsigned a0 + bv_unsigned a1 <= 2^64 /\ bytes_at rsegs m (bv_unsigned a0) bs /\
      (bv_unsigned a0 + bv_unsigned a1 <= bv_unsigned sp - REAC_CTRL_RECORD_CKSUM_VERIFY_FRAME \/
       bv_unsigned sp <= bv_unsigned a0))) ->
    stk rsegs m lo (bv_unsigned sp) -> lo + REAC_CTRL_RECORD_CKSUM_VERIFY_FRAME <= bv_unsigned sp ->
    (1 <= bv_unsigned a1 -> asan_cells m) ->
    (1 <= bv_unsigned a1 -> shadow_rw m) ->
    (1 <= bv_unsigned a1 -> addressable m (bv_unsigned a0) (bv_unsigned a1)) ->
    (1 <= bv_unsigned a1 ->
     forall x, GOT_CELL_K <= x < GOT_CELL_K + 8 \/ CELL_K <= x < CELL_K + 8 \/ in_shadow x ->
       outside [(bv_unsigned sp - REAC_CTRL_RECORD_CKSUM_VERIFY_FRAME, bv_unsigned sp)] x) ->
    evt rsegs
      (fun ms' => exists (t0' a1' a2' a3' a4' a5' a6' a7' : word) (m' : word -> option byte),
         ms' = MS (mkR ra sp gp tp t0' t1 t2 s0 s1 (Z_to_bv 64 (if recsum bs =? 0 then 0 else -1))
                       a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (ret_pc ra) fc None m' (seg_rom rsegs) /\
         munch [(bv_unsigned sp - REAC_CTRL_RECORD_CKSUM_VERIFY_FRAME, bv_unsigned sp)] m m' /\
         wmono rsegs m m' /\ (mem_inv rsegs m -> mem_inv rsegs m') /\ stk rsegs m' lo (bv_unsigned sp))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 REAC_CTRL_RECORD_CKSUM_VERIFY) fc None m (seg_rom rsegs)).

(* Footprint form: the same run as an ExecF.evtF under a footprint RNG, with one rng premise per region the run
   reads or writes: the 16-byte frame (ra save/restore), the GOT cell and the runtime cell of the shadow offset
   (two 8-byte loads), and, when the buffer is not empty (the a1 = 0 run reads nothing beyond the frame), the
   bv_unsigned a1 data bytes at bv_unsigned a0 and their shadow bytes (one 1-byte load at shadow_addr a per data
   byte a, so the shadow range runs from the shadow byte of the first data byte to the shadow byte of the last). *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import ExecF.

Definition reac_ctrl_record_cksum_verify_contract_F : Prop :=
  forall (RNG : footprint)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z) (bs : list byte),
    length bs = Z.to_nat (bv_unsigned a1) ->
    (bv_unsigned a1 = 0 \/
     (bv_unsigned a0 <> 0 /\ bv_unsigned a0 + bv_unsigned a1 <= 2^64 /\ bytes_at rsegs m (bv_unsigned a0) bs /\
      (bv_unsigned a0 + bv_unsigned a1 <= bv_unsigned sp - REAC_CTRL_RECORD_CKSUM_VERIFY_FRAME \/
       bv_unsigned sp <= bv_unsigned a0))) ->
    stk rsegs m lo (bv_unsigned sp) -> lo + REAC_CTRL_RECORD_CKSUM_VERIFY_FRAME <= bv_unsigned sp ->
    (1 <= bv_unsigned a1 -> asan_cells m) ->
    (1 <= bv_unsigned a1 -> shadow_rw m) ->
    (1 <= bv_unsigned a1 -> addressable m (bv_unsigned a0) (bv_unsigned a1)) ->
    (1 <= bv_unsigned a1 ->
     forall x, GOT_CELL_K <= x < GOT_CELL_K + 8 \/ CELL_K <= x < CELL_K + 8 \/ in_shadow x ->
       outside [(bv_unsigned sp - REAC_CTRL_RECORD_CKSUM_VERIFY_FRAME, bv_unsigned sp)] x) ->
    rng RNG (bv_unsigned sp - REAC_CTRL_RECORD_CKSUM_VERIFY_FRAME) REAC_CTRL_RECORD_CKSUM_VERIFY_FRAME ->
    rng RNG GOT_CELL_K 8 -> rng RNG CELL_K 8 ->
    (1 <= bv_unsigned a1 -> rng RNG (bv_unsigned a0) (bv_unsigned a1)) ->
    (1 <= bv_unsigned a1 ->
     rng RNG (shadow_addr (bv_unsigned a0))
             (shadow_addr (bv_unsigned a0 + bv_unsigned a1 - 1) - shadow_addr (bv_unsigned a0) + 1)) ->
    evtF rsegs RNG
      (fun ms' => exists (t0' a1' a2' a3' a4' a5' a6' a7' : word) (m' : word -> option byte),
         ms' = MS (mkR ra sp gp tp t0' t1 t2 s0 s1 (Z_to_bv 64 (if recsum bs =? 0 then 0 else -1))
                       a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (ret_pc ra) fc None m' (seg_rom rsegs) /\
         munch [(bv_unsigned sp - REAC_CTRL_RECORD_CKSUM_VERIFY_FRAME, bv_unsigned sp)] m m' /\
         wmono rsegs m m' /\ (mem_inv rsegs m -> mem_inv rsegs m') /\ stk rsegs m' lo (bv_unsigned sp))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 REAC_CTRL_RECORD_CKSUM_VERIFY) fc None m (seg_rom rsegs)).


(* Route (C), a Theorem Labs lane via another Theorem Labs lane 11:28Z (a Theorem Labs lane's reply-run measurement): this run reads and stores NO shadow byte
   THROUGH the premise -- reac_ctrl_record_cksum_verify.v:111 specialises HSW and never uses it afterwards --
   so the _on forms DROP the guarded conjunct `(1 <= bv_unsigned a1 -> shadow_rw m) ->` and name no region.
   (a Theorem Labs lane proposed a narrowed shadow_rw_on (sh_word_on a0 a1); the dropped form is stronger and its run
   discharges it trivially.) The guarded asan_cells and addressable premises STAY: the run does use them.
   Image-A form: premise DROPPED, as A's checksum_verify / headamp_record_verify (a Theorem Labs lane e8539574cef). *)
Definition reac_ctrl_record_cksum_verify_contract_on : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z) (bs : list byte),
    length bs = Z.to_nat (bv_unsigned a1) ->
    (bv_unsigned a1 = 0 \/
     (bv_unsigned a0 <> 0 /\ bv_unsigned a0 + bv_unsigned a1 <= 2^64 /\ bytes_at rsegs m (bv_unsigned a0) bs /\
      (bv_unsigned a0 + bv_unsigned a1 <= bv_unsigned sp - REAC_CTRL_RECORD_CKSUM_VERIFY_FRAME \/
       bv_unsigned sp <= bv_unsigned a0))) ->
    stk rsegs m lo (bv_unsigned sp) -> lo + REAC_CTRL_RECORD_CKSUM_VERIFY_FRAME <= bv_unsigned sp ->
    (1 <= bv_unsigned a1 -> asan_cells m) ->
    (1 <= bv_unsigned a1 -> addressable m (bv_unsigned a0) (bv_unsigned a1)) ->
    (1 <= bv_unsigned a1 ->
     forall x, GOT_CELL_K <= x < GOT_CELL_K + 8 \/ CELL_K <= x < CELL_K + 8 \/ in_shadow x ->
       outside [(bv_unsigned sp - REAC_CTRL_RECORD_CKSUM_VERIFY_FRAME, bv_unsigned sp)] x) ->
    evt rsegs
      (fun ms' => exists (t0' a1' a2' a3' a4' a5' a6' a7' : word) (m' : word -> option byte),
         ms' = MS (mkR ra sp gp tp t0' t1 t2 s0 s1 (Z_to_bv 64 (if recsum bs =? 0 then 0 else -1))
                       a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (ret_pc ra) fc None m' (seg_rom rsegs) /\
         munch [(bv_unsigned sp - REAC_CTRL_RECORD_CKSUM_VERIFY_FRAME, bv_unsigned sp)] m m' /\
         wmono rsegs m m' /\ (mem_inv rsegs m -> mem_inv rsegs m') /\ stk rsegs m' lo (bv_unsigned sp))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 REAC_CTRL_RECORD_CKSUM_VERIFY) fc None m (seg_rom rsegs)).

Lemma reac_ctrl_record_cksum_verify_contract_of_on : reac_ctrl_record_cksum_verify_contract_on -> reac_ctrl_record_cksum_verify_contract.
Proof. intros H. unfold reac_ctrl_record_cksum_verify_contract. intros. apply H; assumption. Qed.

Definition reac_ctrl_record_cksum_verify_contract_F_on : Prop :=
  forall (RNG : footprint)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z) (bs : list byte),
    length bs = Z.to_nat (bv_unsigned a1) ->
    (bv_unsigned a1 = 0 \/
     (bv_unsigned a0 <> 0 /\ bv_unsigned a0 + bv_unsigned a1 <= 2^64 /\ bytes_at rsegs m (bv_unsigned a0) bs /\
      (bv_unsigned a0 + bv_unsigned a1 <= bv_unsigned sp - REAC_CTRL_RECORD_CKSUM_VERIFY_FRAME \/
       bv_unsigned sp <= bv_unsigned a0))) ->
    stk rsegs m lo (bv_unsigned sp) -> lo + REAC_CTRL_RECORD_CKSUM_VERIFY_FRAME <= bv_unsigned sp ->
    (1 <= bv_unsigned a1 -> asan_cells m) ->
    (1 <= bv_unsigned a1 -> addressable m (bv_unsigned a0) (bv_unsigned a1)) ->
    (1 <= bv_unsigned a1 ->
     forall x, GOT_CELL_K <= x < GOT_CELL_K + 8 \/ CELL_K <= x < CELL_K + 8 \/ in_shadow x ->
       outside [(bv_unsigned sp - REAC_CTRL_RECORD_CKSUM_VERIFY_FRAME, bv_unsigned sp)] x) ->
    rng RNG (bv_unsigned sp - REAC_CTRL_RECORD_CKSUM_VERIFY_FRAME) REAC_CTRL_RECORD_CKSUM_VERIFY_FRAME ->
    rng RNG GOT_CELL_K 8 -> rng RNG CELL_K 8 ->
    (1 <= bv_unsigned a1 -> rng RNG (bv_unsigned a0) (bv_unsigned a1)) ->
    (1 <= bv_unsigned a1 ->
     rng RNG (shadow_addr (bv_unsigned a0))
             (shadow_addr (bv_unsigned a0 + bv_unsigned a1 - 1) - shadow_addr (bv_unsigned a0) + 1)) ->
    evtF rsegs RNG
      (fun ms' => exists (t0' a1' a2' a3' a4' a5' a6' a7' : word) (m' : word -> option byte),
         ms' = MS (mkR ra sp gp tp t0' t1 t2 s0 s1 (Z_to_bv 64 (if recsum bs =? 0 then 0 else -1))
                       a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (ret_pc ra) fc None m' (seg_rom rsegs) /\
         munch [(bv_unsigned sp - REAC_CTRL_RECORD_CKSUM_VERIFY_FRAME, bv_unsigned sp)] m m' /\
         wmono rsegs m m' /\ (mem_inv rsegs m -> mem_inv rsegs m') /\ stk rsegs m' lo (bv_unsigned sp))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 REAC_CTRL_RECORD_CKSUM_VERIFY) fc None m (seg_rom rsegs)).

Lemma reac_ctrl_record_cksum_verify_contract_F_of_on : reac_ctrl_record_cksum_verify_contract_F_on -> reac_ctrl_record_cksum_verify_contract_F.
Proof. intros H. unfold reac_ctrl_record_cksum_verify_contract_F. intros. apply H; assumption. Qed.