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
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Ubsan Require Import UImg F_memmove RZ_seq_iface RZ_seq_safecopy RZ_seq_execend_a.
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
    (MS (mkR xra (Z_to_bv 64 (SPV + -96)) gp tp x5 x6 x7 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 x28 x29 x30 x31)
        F (Z_to_bv 64 pc) fc None mm (seg_rom usegs)).
  Notation XIm := (XI ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m SPV lo OP OEND SQP LPP LL ML OFS B0 B1).
  (* [comment removed for export] *)

  (* [comment removed for export] *)
  Lemma xe_lit : forall m1 xra x5 x6 x7 xs0 xs1 xa4 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 x28 x29 x30 x31,
    XIm LP m1 -> rdbl usegs m1 LP (LLIM + 32) ->
    x5 = Z_to_bv 64 LL -> x6 = Z_to_bv 64 LP -> xs3 = Z_to_bv 64 (ML + LL) ->
    evt usegs POST (ST 0x1e050 m1 xra x5 x6 x7 xs0 xs1 (Z_to_bv 64 OP) (Z_to_bv 64 OEND) (Z_to_bv 64 SQP) (Z_to_bv 64 LPP) xa4
                       (Z_to_bv 64 PFX) (Z_to_bv 64 PFX) (Z_to_bv 64 DEND) xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 s10 s11 x28 x29 x30 x31).
  Proof.
    intros until x31; intros I RDL -> -> ->. open_hy HY. open_xi I.
    do 15 zstep.
    pose proof zd_safecopy_proof as SC. unfold zd_safecopy_stmt, PZD_SAFECOPY in SC.
    eapply evt_cut; [ eapply SC with (SPV := SPV + -96) (lo := lo) (OP := OP) (OENDW := OEND + -32) (IP := LP) (LEN := LL) (OV := 0)
                                     (B0 := B0) (B1 := B1) (R0 := LP) (R1 := LLIM + 32);
      [ exact REG | lia | lia | lia | lia | lia | lia | lia | exact RDL | lia | lia | lia | right; unfold apart; lia
      | exact STK | lia | lia | unfold off_stack; lia | unfold off_stack; lia | exact MI
      | first [ reflexivity | apply bv_eq; reflexivity | f_equal; lia ] .. ]
      | clear SC REG STK RDL; post_call usegs m1 ].
    lazymatch goal with H : stk usegs _ B0 B1 |- _ => rename H into REG end.
    lazymatch goal with H : stk usegs _ lo (SPV + -96) |- _ => rename H into STK end.
    eapply xe_match; [ exact HY | close_xi | lia | lia | first [ reflexivity | f_equal; lia ] ].
  Qed.

  (* [comment removed for export] *)

  (* [comment removed for export] *)

  (* [comment removed for export] *)
End B.
