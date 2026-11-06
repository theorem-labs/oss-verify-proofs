From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Lib Require Import PropExec MState Mem Exec Frame.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.U Require Import Img0.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.U.Prog Require Import HeadampModel NextModel.
Import ListNotations.
Open Scope Z_scope.

Definition REAC_HEADAMP_TX_NEXT : Z := 0x15690.
Definition REAC_HEADAMP_TX_NEXT_FRAME : Z := 48.

Definition next_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (m : word -> option byte) (lo t chp parp valp : Z) (res : nres) (ms' : machine_state) : Prop :=
  match res with
  | (r, (c, p, v), T') =>
      exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : word -> option byte),
        ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 r) a1' a2' a3' a4' a5' a6' a7'
                      s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                 F (ret_pc ra) fc None m' (seg_rom rsegs) /\
        bytes_at rsegs m' t T' /\ wmono rsegs m m' /\ stk rsegs m' lo (bv_unsigned sp) /\ mem_inv rsegs m' /\
        (if r =? 1
         then munch [(bv_unsigned sp - REAC_HEADAMP_TX_NEXT_FRAME, bv_unsigned sp);
                     (t, t + 460); (chp, chp + 1); (parp, parp + 1); (valp, valp + 1)] m m' /\
              bytes_at rsegs m' chp (le1 (Z_to_bv 64 c)) /\ bytes_at rsegs m' parp (le1 (Z_to_bv 64 p)) /\
              bytes_at rsegs m' valp (le1 (Z_to_bv 64 v))
         else munch [(bv_unsigned sp - REAC_HEADAMP_TX_NEXT_FRAME, bv_unsigned sp); (t, t + 460)] m m')
  end.

Definition reac_headamp_tx_next_contract : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo t chp parp valp : Z) (T : list byte),
    a0 = Z_to_bv 64 t -> a1 = Z_to_bv 64 chp -> a2 = Z_to_bv 64 parp -> a3 = Z_to_bv 64 valp ->
    0 < t -> t mod 4 = 0 -> length T = 460%nat -> bytes_at rsegs m t T -> wr_at rsegs m t 460 ->
    wr_at rsegs m chp 1 -> wr_at rsegs m parp 1 -> wr_at rsegs m valp 1 -> mem_inv rsegs m ->
    chp <> 0 -> parp <> 0 -> valp <> 0 ->
    (chp + 1 <= t \/ t + 460 <= chp) -> (parp + 1 <= t \/ t + 460 <= parp) -> (valp + 1 <= t \/ t + 460 <= valp) ->
    chp <> parp -> chp <> valp -> parp <> valp ->
    stk rsegs m lo (bv_unsigned sp) -> lo + REAC_HEADAMP_TX_NEXT_FRAME <= bv_unsigned sp ->
    (t + 460 <= lo \/ bv_unsigned sp <= t) ->
    (chp + 1 <= lo \/ bv_unsigned sp <= chp) -> (parp + 1 <= lo \/ bv_unsigned sp <= parp) ->
    (valp + 1 <= lo \/ bv_unsigned sp <= valp) ->
    (tb T 437 <> 0 -> 0 <= s32 T 440) ->
    evt rsegs (next_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m lo t chp parp valp (next_model T t))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 REAC_HEADAMP_TX_NEXT) fc None m (seg_rom rsegs)).
