(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.jsoncons.fuzz_json_encoder.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PropExec.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CJ.Lib Require Import SFModel Arr.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CJ.Spec Require Import Prelim Monad SoftFloat FmtFp Stdio.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CJ.F5 Require Import F_memset F_memcpy F_fwritex F_pad F_fmt_fp_lib F_fmt_fp F_pop_arg Exit Printf_model Printf_mlib
  F_printf_iface F_printf_core F_printf_snsink F_sn_write F_vfprintf F_vsnprintf F_fmt_fp_nf.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CJMXB Require Import ShZero QcF IcptCells IcptCellsA FfpTac.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

Definition SNI_DEPTH : Z := 8160.

Definition snprintf_icpt_stmt (X : mem -> Prop) : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem)
         (D n A : Z) (dn : nat) (junkd : list byte) (args : list parg)
         (lo : Z) (canary : word) (r : Z) (o : list Z),
    let q := bv_unsigned sp in
    a0 = Z_to_bv 64 D -> a1 = Z_to_bv 64 n -> a2 = Z_to_bv 64 A ->
    rw_cells rsegs m D [CB dn junkd] ->
    bytes_at rsegs m A (zb FMT_G) ->
    Forall no_s args -> args_ok 0 0 0 m lo q 0 [a3; a4; a5; a6; a7] args ->
    printf_model OUT_sn OUTFP_sn FMT_G args [] = ITree.Ret (Ok (r, o)) ->
    Forall (fun c => let '(y, w, p, fl, t) := c in fmt_fp_facts' y fl p t) (fp_calls (length FMT_G) FMT_G args) ->
    r = zlength o -> zlength o < 64 ->
    (length o < dn)%nat -> (zlength o <= n - 1) -> (1 <= n < 2^63) ->
    stk rsegs m lo q -> (lo <= q - SNI_DEPTH) -> (GLOBALS_TOP <= lo) -> (q < 2^63) ->
    ssp_cells m canary -> mem_inv rsegs m -> frm0 fc ->
    (65536 <= A) -> (A + 6 <= STATIC_SPLIT) ->
    (D + Z.of_nat dn <= lo \/ q <= D) -> (D + Z.of_nat dn <= 65536 \/ GLOBALS_TOP <= D) ->

    IcptCells.aenv m -> ShZero.zsh m lo (q - 2256) -> ShZero.zsh m FfpTac.RODATA_LO FfpTac.RODATA_HI -> (0x10007fff8000 <= lo) -> (q <= 2^47) ->
    fmtq m A FMT_G ->
    ShZero.shz rsegs m D (zlength o) -> QcF.shk rsegs m D (zlength o + 1) -> (0x170040 <= D /\ ShZero.app D (Z.of_nat dn)) ->
    X m ->
    evt rsegs (vsnprintf_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F D dn junkd r o lo canary m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x6c23c) fc None m (seg_rom rsegs)).
