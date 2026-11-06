From OSSVerify.libreac.fuzz_pcap Require Symbols.
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib Require Import Img0.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Prog Require Import StdioModel.
Import ListNotations.
Open Scope Z_scope.

Definition FFLUSH : Z := Eval compute in Symbols.Plain.s_fflush.
Definition FFLUSH_K : Z := 80.

Definition fflush_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (h : word) (b : Z) (Fc : list byte) (fl md : word) (q : Z) (rb : option (Z * Z)) (pv nx : word) (lo : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0' a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0' a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom rsegs)
    /\ a0' = wz 0
    /\ munch [(bv_unsigned sp - FFLUSH_K, bv_unsigned sp); (bv_unsigned h, bv_unsigned h + 1304)] m m'
    /\ wmono rsegs m m' /\ mem_inv rsegs m'
    /\ stk rsegs m' lo (bv_unsigned sp)
    /\ mfile m' (bv_unsigned h) b Fc fl md (q - rlen rb) None pv nx.

Definition fflush_contract : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo b : Z) (Fc : list byte)
         (fl md : word) (q : Z) (rb : option (Z * Z)) (pv nx : word),
    mfile m (bv_unsigned a0) b Fc fl md q rb pv nx ->
    Z.of_nat (length Fc) < 2 ^ 63 ->
    guard_ok m ->
    mem_inv rsegs m -> stk rsegs m lo (bv_unsigned sp) -> lo + FFLUSH_K <= bv_unsigned sp ->
    bv_unsigned a0 + 1304 <= lo -> b + Z.of_nat (length Fc) <= lo -> A_OFL_HEAD + 8 <= lo ->
    evt rsegs (fflush_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0 b Fc fl md q rb pv nx lo m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 FFLUSH) fc None m (seg_rom rsegs)).
