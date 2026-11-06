From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib Require Import Img0.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib Require MemNorm RoAdapt.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Prog Require Import StdioModel mseek_c.
Import ListNotations.
Open Scope Z_scope.

Definition mseek_post_ro (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (h : word) (b n : Z) (fl rpos rend md : word) (q r : Z) (pv nx : word) (buf : list byte) (lo : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0' a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0' a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom rsegs)
    /\ a0' = wz (q - r)
    /\ munch [(bv_unsigned sp - MSEEK_K, bv_unsigned sp); (bv_unsigned h + 232, bv_unsigned h + 240)] m m'
    /\ wmono rsegs m m' /\ MemNorm.ro_agree rsegs m'
    /\ stk rsegs m' lo (bv_unsigned sp)
    /\ mfile_raw m' (bv_unsigned h) b n fl rpos rend md (q - r) pv nx buf.

Definition mseek_ro_contract : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo b n : Z)
         (fl rpos rend md : word) (q r : Z) (pv nx : word) (buf : list byte),
    mfile_raw m (bv_unsigned a0) b n fl rpos rend md q pv nx buf -> RoAdapt.not_ro rsegs (bv_unsigned a0) 1304 ->
    0 <= r <= q -> q <= n -> 0 <= n < 2 ^ 63 ->
    a1 = wz (- r) -> a2 = wz 1 ->
    guard_ok m ->
    MemNorm.ro_agree rsegs m -> stk rsegs m lo (bv_unsigned sp) -> RoAdapt.not_ro rsegs lo ((bv_unsigned sp) - lo) ->
    lo + MSEEK_K <= bv_unsigned sp ->
    bv_unsigned a0 + 1304 <= lo -> A_OFL_HEAD + 8 <= lo ->
    evt rsegs (mseek_post_ro ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0 b n fl rpos rend md q r pv nx buf lo m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 MSEEK_FN) fc None m (seg_rom rsegs)).
