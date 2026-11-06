From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_repacer.fuzz_egress.lib.Lib Require Import PropExec MState Mem Exec Frame.
From OSSVerify.Proofs.reac_repacer.fuzz_egress.lib.U Require Import Img0.
From OSSVerify.Proofs.reac_repacer.fuzz_egress.lib Require Import EgressFrame.
Import ListNotations.
Open Scope Z_scope.

(* rp_mute (src/repace_wire.c:148-152): if (n > 18 && is_audio(f)) memset(f + 18, 0, n - 18);
   is_audio(f) = frame_is_audio (EgressFrame.v). a0 = f, a1 = n; the frame's n bytes are bs.
   It tail-calls memset, so its contract holds given memset's (U/Prog/memset_c.v). *)
Definition RP_MUTE : Z := 0x13608.

Definition rp_mute_mutes (n : Z) (bs : list byte) : bool := (18 <? n) && frame_is_audio bs.

Definition rp_mute_bytes (n : Z) (bs : list byte) : list byte :=
  if rp_mute_mutes n bs then firstn 18 bs ++ repeat (Z_to_bv 8 0) (Z.to_nat (n - 18)) else bs.

Definition rp_mute_contract : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (bs : list byte),
    0 < bv_unsigned a0 ->
    bytes_at rsegs m (bv_unsigned a0) bs ->
    length bs = Z.to_nat (bv_unsigned a1) ->
    wr_at rsegs m (bv_unsigned a0) (bv_unsigned a1) ->
    mem_inv rsegs m ->
    evt rsegs
      (fun ms' => exists (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word)
                         (m' : word -> option byte),
         ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7'
                       s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                  F (ret_pc ra) fc None m' (seg_rom rsegs) /\
         munch [(bv_unsigned a0 + 18, bv_unsigned a0 + bv_unsigned a1)] m m' /\
         wmono rsegs m m' /\ mem_inv rsegs m' /\
         bytes_at rsegs m' (bv_unsigned a0) (rp_mute_bytes (bv_unsigned a1) bs))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 RP_MUTE) fc None m (seg_rom rsegs)).
