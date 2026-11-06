From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require Import Img0.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require Import RcLeaf.
Import ListNotations.
Open Scope Z_scope.

Definition REAC_PORTS_PARSE : Z := 0x157c4.

Definition reac_ports_parse_post (ra sp gp tp t1 t2 s0 s1 a1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (p q : Z) (bs : list byte) : machine_state -> Prop :=
  fun ms' => exists (t0' a2' a3' a4' a5' a6' a7' : word) (m' : word -> option byte),
    ms' = MS (mkR ra sp gp tp t0' t1 t2 s0 s1 (Z_to_bv 64 (if ports_ok p q bs then 0 else -1))
                  a1 a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom rsegs) /\
    if ports_ok p q bs
    then bytes_at rsegs m' q (le4 (Z_to_bv 64 (4 * n_in bs))) /\
         bytes_at rsegs m' (q + 4) (le4 (Z_to_bv 64 (4 * n_out bs))) /\
         bytes_at rsegs m' (q + 8) (le4 (Z_to_bv 64 (16 * bt bs 7))) /\
         munch [(q, q + 12)] m m' /\ wmono rsegs m m' /\ (mem_inv rsegs m -> mem_inv rsegs m')
    else m' = m.

Definition reac_ports_parse_contract : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (p q : Z) (bs : list byte),
    a0 = Z_to_bv 64 p -> a1 = Z_to_bv 64 q ->
    0 <= p < 2^64 -> 0 <= q < 2^64 ->
    (p <> 0 -> q <> 0 -> length bs = 20%nat /\ bytes_at rsegs m p bs) ->
    (p <> 0 -> q <> 0 -> q mod 4 = 0 /\ wr_at rsegs m q 12 /\ (q + 12 <= p \/ p + 20 <= q)) ->
    evt rsegs
      (reac_ports_parse_post ra sp gp tp t1 t2 s0 s1 a1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m p q bs)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 REAC_PORTS_PARSE) fc None m (seg_rom rsegs)).
