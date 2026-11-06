From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.U Require Import Img0.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.U Require MemNorm RoAdapt.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.U.Prog Require Import StdioModel fread_c.
Import ListNotations.
Open Scope Z_scope.

Definition fread_post_ro (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (d k h : word) (b : Z) (Fc : list byte) (p : Z) (pv nx : word) (lo : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0' a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0' a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom rsegs)
    /\ a0' = wz (fread_j (bv_unsigned k) (Z.of_nat (length Fc)) p)
    /\ munch [(bv_unsigned sp - FREAD_K, bv_unsigned sp); (bv_unsigned d, bv_unsigned d + fread_j (bv_unsigned k) (Z.of_nat (length Fc)) p); (bv_unsigned h, bv_unsigned h + 1304)] m m'
    /\ wmono rsegs m m' /\ MemNorm.ro_agree rsegs m'
    /\ stk rsegs m' lo (bv_unsigned sp)
    /\ bytes_at rsegs m' (bv_unsigned d)
         (firstn (Z.to_nat (fread_j (bv_unsigned k) (Z.of_nat (length Fc)) p)) (skipn (Z.to_nat p) Fc))
    /\ mstl m' (bv_unsigned h) b Fc (p + fread_j (bv_unsigned k) (Z.of_nat (length Fc)) p) pv nx.

Definition fread_ro_contract : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo b : Z) (Fc : list byte)
         (p : Z) (pv nx : word) (junk : list byte),
    mstl m (bv_unsigned a3) b Fc p pv nx -> RoAdapt.not_ro rsegs (bv_unsigned a3) 1304 ->
    a1 = wz 1 -> 1 <= bv_unsigned a2 ->
    rw_cells rsegs m (bv_unsigned a0) [CB (Z.to_nat (bv_unsigned a2)) junk] ->
    RoAdapt.not_ro rsegs (bv_unsigned a0) (bv_unsigned a2) ->
    (bv_unsigned a0 + bv_unsigned a2 <= bv_unsigned a3 \/ bv_unsigned a3 + 1304 <= bv_unsigned a0) ->
    (bv_unsigned a0 + bv_unsigned a2 <= b \/ b + Z.of_nat (length Fc) <= bv_unsigned a0) ->
    (bv_unsigned a0 + bv_unsigned a2 <= lo \/ bv_unsigned sp <= bv_unsigned a0) ->
    MemNorm.ro_agree rsegs m -> stk rsegs m lo (bv_unsigned sp) -> RoAdapt.not_ro rsegs lo ((bv_unsigned sp) - lo) ->
    lo + FREAD_K <= bv_unsigned sp ->
    bv_unsigned a3 + 1304 <= lo -> b + Z.of_nat (length Fc) <= lo ->
    evt rsegs (fread_post_ro ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0 a2 a3 b Fc p pv nx lo m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 FREAD) fc None m (seg_rom rsegs)).
