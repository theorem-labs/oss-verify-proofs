From OSSVerify.libreac.fuzz_pcap Require Symbols.
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.U Require Import Img0.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.U.Prog Require Import StdioModel.
Import ListNotations.
Open Scope Z_scope.

Definition OFL_ADD : Z := Eval compute in Symbols.Ubsan.s___ofl_add.
Definition OFL_ADD_K : Z := 32.

Definition __ofl_add_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (f : word) (lo : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 f a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom rsegs)
    /\ munch [(bv_unsigned sp - OFL_ADD_K, bv_unsigned sp); (bv_unsigned f + 112, bv_unsigned f + 120);
              (A_OFL_HEAD, A_OFL_HEAD + 8)] m m'
    /\ wmono rsegs m m' /\ mem_inv rsegs m'
    /\ stk rsegs m' lo (bv_unsigned sp)
    /\ ofl_one m' (bv_unsigned f)
    /\ rw_cells rsegs m' (bv_unsigned f + 104) [C8 (wz 0); C8 (wz 0)]
    /\ stdio_ok m'.

Definition __ofl_add_contract : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z) (nx : word),
    stdio_ok m -> ofl_empty m -> mem_inv rsegs m ->
    rw_cells rsegs m (bv_unsigned a0 + 104) [C8 (wz 0); C8 nx] ->
    0 < bv_unsigned a0 -> (bv_unsigned a0 + 120 <= A_LIBC \/ A_OFL_HEAD + 8 <= bv_unsigned a0) ->
    bv_unsigned a0 + 120 <= lo -> A_OFL_HEAD + 8 <= lo ->
    stk rsegs m lo (bv_unsigned sp) -> lo + OFL_ADD_K <= bv_unsigned sp ->
    evt rsegs (__ofl_add_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0 lo m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 OFL_ADD) fc None m (seg_rom rsegs)).
