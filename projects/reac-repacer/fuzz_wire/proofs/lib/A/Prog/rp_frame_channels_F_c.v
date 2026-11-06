(* Footprint form of rp_frame_channels (image A, entry 0x8136c), in the form of lib/A/Prog/reac_frame_clean_len_F_c.v
   (libreac/fuzz_decode's released footprint contract, relocated) and of fuzz_uci's rp_hot_clamp_F_c.v. The run is an
   ExecF.evtF run under a footprint RNG: every data access of every step lies in RNG. The code (DIS of image A)
     - stores ra and s0 in its frame [sp - 16, sp) and loads them back;
     - calls reac_frame_clean_len, which loads 8 bytes at A_M and 8 bytes at A_T (reac_frame_clean_len_F_c.v);
     - loads the 8-byte reciprocal K36 at A_K36.
   So RNG holds the frame and the three constants. The constants are premises, as in reac_frame_clean_len_F_c.v, each
   outside the frame (AsanKA.v off_stk), as in fuzz_egress's rp_frame_channels_F_c.v. The callee is taken by its
   footprint contract: the walk proves rp_frame_channels_F_holds_stmt. *)
From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Lib Require Import PropExec MState Mem Exec Frame.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.A Require Import Img0.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.A.Prog Require Import AsanKA reac_frame_clean_len_c rp_frame_channels_c.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.A.Prog Require Import reac_frame_clean_len_F_c.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Lib Require Import ExecF.
Import ListNotations.
Open Scope Z_scope.

Definition rp_frame_channels_contract_F : Prop :=
  forall (RNG : ExecF.footprint)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z),
    bytes_at rsegs m A_M (le8 (Z_to_bv 64 KM)) ->
    bytes_at rsegs m A_T (le8 (Z_to_bv 64 KT)) ->
    bytes_at rsegs m A_K36 (le8 (Z_to_bv 64 K36)) ->
    stk rsegs m lo (bv_unsigned sp) ->
    lo + RP_FRAME_CHANNELS_FRAME <= bv_unsigned sp ->
    off_stk sp RP_FRAME_CHANNELS_FRAME A_M 8 ->
    off_stk sp RP_FRAME_CHANNELS_FRAME A_T 8 ->
    off_stk sp RP_FRAME_CHANNELS_FRAME A_K36 8 ->
    ExecF.rng RNG (bv_unsigned sp - RP_FRAME_CHANNELS_FRAME) RP_FRAME_CHANNELS_FRAME ->
    ExecF.rng RNG A_M 8 ->
    ExecF.rng RNG A_T 8 ->
    ExecF.rng RNG A_K36 8 ->
    ExecF.evtF rsegs RNG
      (fun ms' => exists (a1' a2' a3' : word) (m' : word -> option byte),
         ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (rp_frame_channels_model (bv_signed a0)))
                       a1' a2' a3' a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (ret_pc ra) fc None m' (seg_rom rsegs) /\
         munch [(bv_unsigned sp - RP_FRAME_CHANNELS_FRAME, bv_unsigned sp)] m m' /\
         wmono rsegs m m' /\
         stk rsegs m' lo (bv_unsigned sp))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 RP_FRAME_CHANNELS) fc None m (seg_rom rsegs)).

(* The statement its walk proves: the callee's footprint contract gives this one (callers chain by
   `<callee>_contract_F -> <fn>_contract_F`). *)
Definition rp_frame_channels_F_holds_stmt : Prop :=
  reac_frame_clean_len_contract_F -> rp_frame_channels_contract_F.
