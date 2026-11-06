From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U Require Import Img0.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Spec Require Import CType.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U Require MemNorm RoAdapt.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog Require Import __intscan_c.
Import ListNotations.
Open Scope Z_scope.

Definition __intscan_post_ro (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (Fp P : Z) (str : list byte) (ev : word) (lo : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' (r : Z),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (s10_val str)) a1 a2 a3 a4 a5 a6 a7
                  s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom rsegs)
    /\ munch [(bv_unsigned sp - 80, bv_unsigned sp); (Fp + 8, Fp + 16); (Fp + 184, Fp + 208);
              (bv_unsigned tp + -164, bv_unsigned tp + -164 + 4)] m m'
    /\ wmono rsegs m m' /\ MemNorm.ro_agree rsegs m'
    /\ stk rsegs m' lo (bv_unsigned sp)
    /\ rw_cells rsegs m' (Fp + 8) [C8 (Z_to_bv 64 (P + r)); C8 (Z_to_bv 64 M64)]
    /\ rw_cells rsegs m' (Fp + 184) [C8 (Z_to_bv 64 M64); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 (s10_end str - r))]
    /\ rw_cells rsegs m' (bv_unsigned tp + -164) [C4 (s10_errno str ev)].

Definition __intscan_ro_contract : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a2 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (Fp P : Z) (str : list byte) (ev : word) (lo : Z),
    rw_cells rsegs m (Fp + 8) [C8 (Z_to_bv 64 P); C8 (Z_to_bv 64 M64)] -> RoAdapt.not_ro rsegs (Fp + 8) (Z.of_nat (cells_size [C8 (Z_to_bv 64 P); C8 (Z_to_bv 64 M64)])) ->
    rw_cells rsegs m (Fp + 88) [C8 (Z_to_bv 64 P)] -> RoAdapt.not_ro rsegs (Fp + 88) (Z.of_nat (cells_size [C8 (Z_to_bv 64 P)])) ->
    rw_cells rsegs m (Fp + 184) [C8 (Z_to_bv 64 M64); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)] -> RoAdapt.not_ro rsegs (Fp + 184) (Z.of_nat (cells_size [C8 (Z_to_bv 64 M64); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)])) ->
    bytes_at rsegs m P (str ++ [Z_to_bv 8 0]) ->
    P + Z.of_nat (length str) + 1 < 2^64 ->
    rw_cells rsegs m (bv_unsigned tp + -164) [C4 ev] -> RoAdapt.not_ro rsegs (bv_unsigned tp + -164) (Z.of_nat (cells_size [C4 ev])) ->
    stk rsegs m lo (bv_unsigned sp) -> RoAdapt.not_ro rsegs lo ((bv_unsigned sp) - lo) -> lo + 80 <= bv_unsigned sp ->
    (Fp + 232 <= lo \/ bv_unsigned sp <= Fp) ->
    (P + Z.of_nat (length str) + 1 <= lo \/ bv_unsigned sp <= P) ->
    (bv_unsigned tp + -164 + 4 <= lo \/ bv_unsigned sp <= bv_unsigned tp + -164) ->
    (P + Z.of_nat (length str) + 1 <= Fp \/ Fp + 232 <= P) ->
    (bv_unsigned tp + -164 + 4 <= Fp \/ Fp + 232 <= bv_unsigned tp + -164) ->
    MemNorm.ro_agree rsegs m ->
    evt rsegs (__intscan_post_ro ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc Fp P str ev lo m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 Fp) (Z_to_bv 64 10) a2 (Z_to_bv 64 LMIN) a4 a5 a6 a7
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 INTSCAN) fc None m (seg_rom rsegs)).
