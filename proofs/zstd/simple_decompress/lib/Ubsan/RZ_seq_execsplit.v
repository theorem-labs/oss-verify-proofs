(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import Tac Arr Bytes.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import StrFun STRW_tac MemRange ZdCellKit.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import ZdFrame ZdDCtx.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Ubsan Require Import UImg F_memmove RZ_seq_iface RZ_seq_safecopy RZ_seq_execend_a RZ_seq_execsplit_a seqH_kit.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

(* [comment removed for export] *)
Ltac rdl_to_bytes RDL LB :=
  lazymatch type of RDL with rdbl ?segs ?m1 ?r0 ?r1 =>
    let lbs := fresh "lbs" in let LLEN := fresh "LLEN" in
    destruct (rdbl_bytes segs m1 r0 r1 RDL ltac:(lia)) as (lbs & LLEN & LB); clear RDL end.
Ltac bytes_to_rdl LB RDL :=
  lazymatch type of LB with bytes_at ?segs ?m1 ?r0 ?lbs =>
    pose proof (rdbl_of_bytes_at segs m1 r0 lbs LB) as RDL;
    lazymatch goal with LLEN : length lbs = Z.to_nat (?r1 - r0) |- _ =>
      rewrite LLEN in RDL; replace (r0 + Z.of_nat (Z.to_nat (r1 - r0))) with r1 in RDL by lia end;
    clear LB end.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
Tactic Notation "useD" uconstr(L) :=
  eapply L; try eassumption; try close_xs;
  try (lazymatch goal with |- Z_to_bv 64 _ = Z_to_bv 64 _ => first [ reflexivity | f_equal; lia ] end); try lia.

Section D.
  Variables (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m : fmem)
            (SPV lo OP OEND OENDW SQP LPP LP LLIM LL ML OFS PFX DEND B0 B1 : Z).
  Hypothesis HY : xs_hyps SPV lo OP OEND OENDW SQP LPP LP LLIM LL ML OFS PFX B0 B1.
  Notation POST := (zd_execend_post 208 ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc SPV OP OEND SQP LPP LP LLIM LL ML OFS B0 B1 lo m).

  Notation ST pc mm xra x5 x6 x7 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 x28 x29 x30 x31 :=
    (MS (mkR xra (Z_to_bv 64 (SPV + -96)) gp tp x5 x6 x7 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 x28 x29 x30 x31)
        F (Z_to_bv 64 pc) fc None mm (seg_rom usegs)).
  Notation XSm := (XS ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m SPV lo OP OEND SQP LPP LL ML OFS B0 B1).


  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma xs_main : forall (t0 t1 t2 t4 t5 t6 : word),
    stk usegs m B0 B1 -> stk usegs m lo SPV -> mem_inv usegs m ->
    rw_cells usegs m SQP [C8 (Z_to_bv 64 LL); C8 (Z_to_bv 64 ML); C8 (Z_to_bv 64 OFS)] ->
    rw_cells usegs m LPP [C8 (Z_to_bv 64 LP)] -> rdbl usegs m LP LLIM -> SQP mod 8 = 0 -> LPP mod 8 = 0 ->
    evt usegs POST
      (MS (mkR ra (Z_to_bv 64 SPV) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 OP) (Z_to_bv 64 OEND) (Z_to_bv 64 OENDW) (Z_to_bv 64 SQP) (Z_to_bv 64 LPP)
               (Z_to_bv 64 LLIM) (Z_to_bv 64 PFX) (Z_to_bv 64 PFX) s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 DEND) t4 t5 t6)
          F (Z_to_bv 64 0x1e5d0) fc None m (seg_rom usegs)).
  Proof.
    intros until t6. intros REG STK MI SQC LPC RDL SQA LPA. open_hs HY.
    assert (MU : munch [(OP, OEND); (LPP, LPP + 8); (SPV - 208, SPV)] m m) by apply munch_refl.
    assert (WM : wmono usegs m m) by apply wmono_refl.
    rdl_to_bytes RDL LB.
    zstep. first [ uck | zstep; uck ].
    zstep. first [ uck | zstep; uck ].
    clear SQA LPA.
    zstep. carve_frame 96%nat STK.
    do 11 zstep.
    bytes_to_rdl LB RDL.
    zstep. zstep. zstep. zstep. zstep. zstep. if_cases K; zify_cond K.
    - (* [comment removed for export] *)
      useD (xs_ret ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m SPV lo OP OEND OENDW SQP LPP LP LLIM LL ML OFS PFX B0 B1 HY _ (2^64 - 70) LP);
        [ left; reflexivity | apply bv_eq; reflexivity ].
    - zstep. zstep. zstep. if_cases K1; zify_cond K1.
      + zstep. zstep. zstep. if_cases K2; zify_cond K2.
        * useD xs_lit.
        * zstep. if_cases K3; zify_cond K3.
          -- (* [comment removed for export] *)
             useD (xs_ret ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m SPV lo OP OEND OENDW SQP LPP LP LLIM LL ML OFS PFX B0 B1 HY _ (2^64 - 70) LP);
               [ left; reflexivity | apply bv_eq; reflexivity ].
          -- useD xs_lit.
      + (* [comment removed for export] *)
        zstep. zstep.
        useD (xs_ret ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m SPV lo OP OEND OENDW SQP LPP LP LLIM LL ML OFS PFX B0 B1 HY _ (2^64 - 20) LP);
          [ left; reflexivity | apply bv_eq; reflexivity ].
  Qed.
End D.

Theorem zd_execend_split_proof : zd_execend_split_stmt.
Proof.
  unfold zd_execend_split_stmt, PZD_EXECEND_SPLIT, apart, off_stack. intros until B1.
  intros REG B0L B1H PFXR OENDR OW0 OWH SQC LPC LLR MLR OFSR LPR LLIMH RDL LITPOS SQPL SQPH LPPL LPPH SQPB LPPB SQPLPP LITLPP STK LOS SPR OFFB OFFSQ OFFLPP OFFLIT
         SQA LPA MI -> -> -> -> -> -> -> -> ->.
  pose proof STK as (LO0 & _ & _).
  eapply (xs_main ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m SPV lo OP OEND OENDW SQP LPP LP LLIM LL ML OFS PFX DEND B0 B1); try eassumption.
  unfold xs_hyps. repeat split; try eassumption; try lia.
Qed.
