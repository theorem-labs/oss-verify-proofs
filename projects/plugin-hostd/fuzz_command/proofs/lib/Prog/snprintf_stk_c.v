From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Lib Require Import PropExec MState Mem Exec Frame Step Cells FP Arr.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib Require Import Img0.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib Require MemNorm.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import printf_facts_c snprintf_c.
Import ListNotations.
Open Scope Z_scope.

Definition snprintf_stk_contract : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z) (canary : word)
         (fmt : list Z) (ps : list pf_piece) (args : list pf_arg) (T : list Z) (junk : list byte) (xs : list word),
    let S := bv_unsigned sp in let D := bv_unsigned a0 in let n := bv_unsigned a1 in
    bytes_at rsegs m (bv_unsigned a2) (pf_bytes (fmt ++ [0])) ->
    RO_LO <= bv_unsigned a2 -> bv_unsigned a2 + Z.of_nat (length fmt) + 1 <= RO_END ->
    pf_parse fmt = Some ps ->
    pf_args_ok m S lo D n ([a3; a4; a5; a6; a7] ++ xs) args ->
    bytes_at rsegs m S (u64s xs) -> S + 8 * Z.of_nat (length xs) < 2^63 ->
    (D + n <= S \/ S + 8 * Z.of_nat (length xs) <= D) ->
    pf_text ps args = Some T ->
    rw_cells rsegs m D [CB (Z.to_nat n) junk] ->
    1 <= n < 2^31 -> Z.of_nat (length T) < 2^31 - 1 ->
    0 < D -> (D + n <= lo \/ S <= D) -> pf_img_free D n ->
    stk rsegs m lo S -> lo <= S - SNPRINTF_K -> IMG_END <= lo -> S < 2^63 ->
    frm0 fc -> mem_inv rsegs m -> MemNorm.task_mem rsegs m ->
    bytes_at rsegs m GOT_GUARD (le8 (Z_to_bv 64 GUARD)) -> bytes_at rsegs m GUARD (le8 canary) ->
    evt rsegs (printf_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F lo D (Z.of_nat (length T))
                 (firstn (Z.to_nat (n - 1)) T) m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 SNPRINTF) fc None m (seg_rom rsegs)).
