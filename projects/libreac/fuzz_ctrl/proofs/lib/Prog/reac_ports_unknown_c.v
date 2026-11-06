From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require Import Img0.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require Import RcPorts.
Import ListNotations.
Open Scope Z_scope.

Definition REAC_PORTS_UNKNOWN : Z := 0x1586c.

Definition reac_ports_unknown_contract : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (p c : Z) (bs : list byte),
    bv_unsigned a0 = p ->
    bv_unsigned a1 = c ->
    (p <> 0 -> p + 20 <= 2^64 /\ length bs = 20%nat /\ bytes_at rsegs m p bs) ->
    (c <> 0 -> wr_at rsegs m c 1 /\ (p <> 0 -> c + 1 <= p \/ p + 20 <= c)) ->
    evt rsegs
      (fun ms' => exists (a2' a3' a4' a5' : word) (m' : word -> option byte),
         ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (if pu_ok p bs then 4 * pu_nunk bs 12 else -1))
                       a1 a2' a3' a4' a5' a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (ret_pc ra) fc None m' (seg_rom rsegs)
         /\ munch (if c =? 0 then [] else [(c, c + 1)]) m m'
         /\ wmono rsegs m m'
         /\ (forall lo, stk rsegs m lo (bv_unsigned sp) -> stk rsegs m' lo (bv_unsigned sp))
         /\ (mem_inv rsegs m -> mem_inv rsegs m')
         /\ (c <> 0 -> bytes_at rsegs m' c [Z_to_bv 8 (if pu_ok p bs then pu_first bs 12 else 0)]))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 REAC_PORTS_UNKNOWN) fc None m (seg_rom rsegs)).
