(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Lib Require Import Tac Arr Bytes.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Common Require Import StrFun STRW_tac MemRange ZdCellKit.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Spec Require Import ZdFrame ZdDCtx.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Plain Require Import PImg F_memmove RZ_seq_iface RZ_seq_safecopy RZ_seq_execend_a.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Section B.
  Variables (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m : fmem)
            (SPV lo OP OEND SQP LPP LP LLIM LL ML OFS PFX DEND B0 B1 : Z).
  Hypothesis HY : xe_hyps SPV lo OP OEND SQP LPP LP LLIM LL ML OFS PFX B0 B1.
  Hypothesis HSZ : LL + ML <= OEND - OP.
  Hypothesis HLIT : LL <= LLIM - LP.
  Notation POST := (zd_execend_post 192 ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc SPV OP OEND SQP LPP LP LLIM LL ML OFS B0 B1 lo m).
  Notation ST pc mm xra x5 x6 x7 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 x28 x29 x30 x31 :=
    (MS (mkR xra (Z_to_bv 64 (SPV + -128)) gp tp x5 x6 x7 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 x28 x29 x30 x31)
        F (Z_to_bv 64 pc) fc None mm (seg_rom psegs)).
  Notation XIm := (XI ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m SPV lo OP OEND SQP LPP LL ML OFS B0 B1).
  (* [comment removed for export] *)
  Notation STL pc mm xra x5 x6 x7 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 x28 x29 x30 x31 :=
    (ST pc mm xra x5 x6 x7 (Z_to_bv 64 (OP + LL)) (Z_to_bv 64 (OEND + -32)) xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7
        xs2 xs3 xs4 (Z_to_bv 64 (ML + LL)) (Z_to_bv 64 SQP) (Z_to_bv 64 PFX) (Z_to_bv 64 OFS) (Z_to_bv 64 (LP + LL)) (Z_to_bv 64 PFX) (Z_to_bv 64 LPP)
        x28 x29 x30 x31).

  (* [comment removed for export] *)
  Lemma xe_lit_tail_loop : forall (k : nat) m1 w8 w16 (op lp : Z) xra x5 x6 x7 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 x28 x29 x30 x31,
    XIm w8 w16 LP m1 -> rdbl psegs m1 LP (LLIM + 32) -> OP <= op -> LP <= lp -> lp - LP = op - OP -> op + Z.of_nat k + 1 = OP + LL ->
    xa0 = Z_to_bv 64 op -> xs2 = Z_to_bv 64 lp ->
    evt psegs POST (STL 0x1c2f0 m1 xra x5 x6 x7 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 x28 x29 x30 x31).
  Proof.
    induction k as [|k IH]; intros until x31; intros I RDL HOP HLP HREL HK -> ->; open_hy HY; open_xi I.
    - ldl RDL lp 1%nat. zstep. zstep. strx REG RDL op 1%nat. zstep. zstep. if_cases K; zify_cond K; [exfalso; lia|].
      zstep. use xe_match.
    - ldl RDL lp 1%nat. zstep. zstep. strx REG RDL op 1%nat. zstep. zstep. if_cases K; zify_cond K; [| exfalso; lia].
      use (IH _ w8 w16 (op + 1) (lp + 1)).
  Qed.

  Lemma xe_lit_short_loop : forall (k : nat) m1 w8 w16 (op lp : Z) xra x5 x6 x7 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 x28 x29 x30 x31,
    XIm w8 w16 LP m1 -> rdbl psegs m1 LP (LLIM + 32) -> OP <= op -> LP <= lp -> lp - LP = op - OP -> op + Z.of_nat k + 1 = OP + LL ->
    xa0 = Z_to_bv 64 op -> xs2 = Z_to_bv 64 lp ->
    evt psegs POST (STL 0x1c268 m1 xra x5 x6 x7 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 x28 x29 x30 x31).
  Proof.
    induction k as [|k IH]; intros until x31; intros I RDL HOP HLP HREL HK -> ->; open_hy HY; open_xi I.
    - ldl RDL lp 1%nat. zstep. zstep. strx REG RDL op 1%nat. zstep. zstep. if_cases K; zify_cond K; [exfalso; lia|].
      zstep. use xe_match.
    - ldl RDL lp 1%nat. zstep. zstep. strx REG RDL op 1%nat. zstep. zstep. if_cases K; zify_cond K; [| exfalso; lia].
      use (IH _ w8 w16 (op + 1) (lp + 1)).
  Qed.

  (* [comment removed for export] *)
  Lemma xe_lit_tail : forall m1 w8 w16 (op lp : Z) xra x5 x6 x7 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 x28 x29 x30 x31,
    XIm w8 w16 LP m1 -> rdbl psegs m1 LP (LLIM + 32) -> OP <= op <= OEND -> LP <= lp -> lp - LP = op - OP ->
    xa0 = Z_to_bv 64 op -> xs2 = Z_to_bv 64 lp ->
    evt psegs POST (STL 0x1c2ec m1 xra x5 x6 x7 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 x28 x29 x30 x31).
  Proof.
    intros until x31; intros I RDL HOP HLP HREL -> ->. open_hy HY.
    zstep. if_cases K; zify_cond K.
    - use xe_match.
    - use (xe_lit_tail_loop (Z.to_nat (OP + LL - op - 1)) _ w8 w16 op lp).
  Qed.

  (* [comment removed for export] *)
  Lemma xe_w1_loop : forall (q : nat) m1 w8 w16 (d sr : Z) xra x5 x6 x7 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 x28 x29 x30 x31,
    XIm w8 w16 LP m1 -> rdbl psegs m1 LP (LLIM + 32) -> OP <= d < OP + LL -> sr - LP = d - OP -> OP + LL + 32 <= OEND ->
    OP + LL - d <= 32 * (Z.of_nat q + 1) ->
    xs3 = Z_to_bv 64 d -> xs2 = Z_to_bv 64 (sr + 16) ->
    evt psegs POST (STL 0x1c32c m1 xra x5 x6 x7 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 x28 x29 x30 x31).
  Proof.
    induction q as [|q IH]; intros until x31; intros I RDL HD HREL HEND HQ -> ->; open_hy HY; open_xi I.
    - zstep. zstep. zstep. zstep. mmvl REG RDL d sr. zstep. zstep. zstep. zstep. mmvl REG RDL (d + 16) (sr + 16).
      zstep. zstep. zstep. if_cases K; zify_cond K; [exfalso; lia|]. use xe_match.
    - zstep. zstep. zstep. zstep. mmvl REG RDL d sr. zstep. zstep. zstep. zstep. mmvl REG RDL (d + 16) (sr + 16).
      zstep. zstep. zstep. if_cases K; zify_cond K.
      + use (IH _ w8 w16 (d + 32) (sr + 32)).
      + use xe_match.
  Qed.

  (* [comment removed for export] *)
  Lemma xe_w1 : forall m1 w8 w16 xra x5 x6 x7 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs3 x28 x29 x30 x31,
    XIm w8 w16 LP m1 -> rdbl psegs m1 LP (LLIM + 32) -> 7 < LL -> OP + LL + 32 <= OEND ->
    evt psegs POST (STL 0x1c30c m1 xra x5 x6 x7 (Z_to_bv 64 OP) xa1 xa2 xa3 xa4 xa5 xa6 xa7 (Z_to_bv 64 LP) xs3 (Z_to_bv 64 LL) x28 x29 x30 x31).
  Proof.
    intros until x31; intros I RDL HLL HEND. open_hy HY. open_xi I.
    zstep. zstep. zstep. zstep. mmvl REG RDL OP LP.
    zstep. zstep. if_cases K; zify_cond K.
    - use xe_match.
    - zstep. zstep. use (xe_w1_loop (Z.to_nat LL) _ w8 w16 (OP + 16) (LP + 16)).
  Qed.
End B.
