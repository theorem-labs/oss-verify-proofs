From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.U Require Import Img0.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.U Require MemNorm RoAdapt.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.U.Prog Require Import StdioModel __toread_c.
Import ListNotations.
Open Scope Z_scope.

Definition __toread_post_ro (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (h : word) (b : Z) (Fc : list byte) (fl : word) (q : Z) (pv nx : word) (lo : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0' a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0' a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom rsegs)
    /\ a0' = (if bv_eqb fl (wz 24) then wz (-1) else wz 0)
    /\ munch [(bv_unsigned sp - TOREAD_K, bv_unsigned sp); (bv_unsigned h, bv_unsigned h + 1304)] m m'
    /\ wmono rsegs m m' /\ MemNorm.ro_agree rsegs m'
    /\ stk rsegs m' lo (bv_unsigned sp)
    /\ mfile m' (bv_unsigned h) b Fc fl (wz 4294967295) q (Some (1024, 1024)) pv nx.

Definition __toread_ro_contract : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo b : Z) (Fc : list byte)
         (fl md : word) (q : Z) (rb : option (Z * Z)) (pv nx : word),
    mfile m (bv_unsigned a0) b Fc fl md q rb pv nx -> RoAdapt.not_ro rsegs (bv_unsigned a0) 1304 -> rlen rb = 0 ->
    (fl = wz 8 \/ fl = wz 24) -> (md = wz 0 \/ md = wz 4294967295) ->
    MemNorm.ro_agree rsegs m -> stk rsegs m lo (bv_unsigned sp) -> RoAdapt.not_ro rsegs lo ((bv_unsigned sp) - lo) ->
    lo + TOREAD_K <= bv_unsigned sp ->
    bv_unsigned a0 + 1304 <= lo -> b + Z.of_nat (length Fc) <= lo ->
    evt rsegs (__toread_post_ro ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0 b Fc fl q pv nx lo m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 TOREAD) fc None m (seg_rom rsegs)).
