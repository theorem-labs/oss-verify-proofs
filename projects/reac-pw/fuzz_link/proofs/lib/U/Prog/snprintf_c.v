(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/cjson/cjson_read_fuzzer/lib/P/F_vsnprintf.v, with its module paths and module names changed; 710 of its 816 lines of code are new or changed and 1295 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_boxreg/lib/CJ/RL/GX/Printf_text.v, with its module paths and module names changed; 57 of its 133 lines of code are new or changed and 740 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_link/lib/Prog/printf_facts_c.v; 27 of its 44 lines of code are new or changed and 116 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_link/lib/Prog/snprintf_ro_c.v, with its module paths changed; 12 of its 36 lines of code are new or changed and 20 lines of the source are left out. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Lib Require Import PropExec MState Mem Exec Frame Step Cells FP.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.U Require Import Img0.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.U Require MemNorm.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.U.Prog Require Import printf_facts_c.
Import ListNotations.
Open Scope Z_scope.

Definition SNPRINTF : Z := 0x1a560.
Definition GOT_GUARD : Z := 0x21110.
Definition GUARD : Z := 0x960b8.
Definition RO_LO : Z := 0x10000.
Definition RO_END : Z := 0x11f54.
Definition IMG_END : Z := 0x96920.
Definition SNPRINTF_K : Z := 5936.

Definition snprintf_contract : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z) (canary : word)
         (fmt : list Z) (ps : list pf_piece) (args : list pf_arg) (T : list Z) (junk : list byte),
    let S := bv_unsigned sp in let D := bv_unsigned a0 in let n := bv_unsigned a1 in
    bytes_at rsegs m (bv_unsigned a2) (pf_bytes (fmt ++ [0])) ->
    RO_LO <= bv_unsigned a2 -> bv_unsigned a2 + Z.of_nat (length fmt) + 1 <= RO_END ->
    pf_parse fmt = Some ps ->
    pf_args_ok m S lo D n [a3; a4; a5; a6; a7] args ->
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
