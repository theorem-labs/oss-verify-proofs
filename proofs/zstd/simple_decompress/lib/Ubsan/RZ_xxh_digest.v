(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import Tac ZBridge.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import KXExec KXSound KXFull KXBridge KXTac KXGo KXTree KXAuto KXMem KXPost KXUb KXUb2.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import KXLean KXLeanAll.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Ubsan Require Import UImg RZ_frame_iface frame_kit_xxhfin.
Import ListNotations. Import KXS.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section DIGEST.
  Variables (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : fmem) (SPV STA : Z) (st : list byte) (lo : Z).
  Hypothesis STB : bytes_at usegs m STA st.
  Hypothesis STL : zlen st = 88.
  Hypothesis R0 : 4096 <= STA.
  Hypothesis R8 : STA mod 8 = 0.
  Hypothesis R1 : STA + 88 <= 2^47.
  Hypothesis ST : stk usegs m lo SPV.
  Hypothesis RLO : 4096 <= lo.
  Hypothesis LO : lo <= SPV - 16.
  Hypothesis RSP : SPV <= 2^47.
  Hypothesis SS : STA + 88 <= lo \/ SPV <= STA.
  Hypothesis MI : mem_inv usegs m.

  Notation POST := (zd_xxh_digest_post ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc SPV lo m).
  (* [comment removed for export] *)
  Notation STpc pc x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 :=
    (MS (mkR ra (Z_to_bv 64 SPV) gp tp x5 x6 x7 s0 s1 x10 x11 x12 x13 x14 x15 x16 x17 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
        F (Z_to_bv 64 pc) fc None m (seg_rom usegs)).

  Lemma mem64_bytes : exists pb, bytes_at usegs m (STA + 40) pb /\ zlen pb = 32.
  Proof.
    pose proof STB as H. rewrite <- (firstn_skipn 40 st) in H.
    apply (proj1 (bytes_at_app usegs m STA _ _)) in H. destruct H as [_ H].
    rewrite <- (firstn_skipn 32 (skipn 40 st)) in H.
    apply (proj1 (bytes_at_app usegs m _ _ _)) in H. destruct H as [H _].
    exists (firstn 32 (skipn 40 st)).
    rewrite firstn_length_le in H by lia. rewrite firstn_length_le by (rewrite length_skipn; lia).
    split; [exact H | reflexivity].
  Qed.

  Lemma digest_body : forall (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
    evt usegs POST (STpc PZD_XXH_DIGEST t0 t1 t2 (Z_to_bv 64 STA) a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6).
  Proof.
    intros. unfold PZD_XXH_DIGEST.
    destruct mem64_bytes as (pb & PB & PL).
    pose proof xxhfin_proof as FINP. unfold xxhfin_stmt, PXXH_FIN in FINP.
    kx_autoLx [0x2d3f4] 120%nat [KZImg 0x10fe0 0x11060; KZRange STA 4096 (2^47 - 88); KZAlign STA 8] [(STA, 88)].
    all: lazymatch goal with |- evt _ _ (MS _ _ (Z_to_bv 64 0x2d3f0) _ _ _ _) => kx_trap_fast | _ => idtac end.
    all: kx_abs.
    all: eapply FINP; first [exact PB | exact PL | exact ST | exact MI | lia].
  Qed.
End DIGEST.

Theorem zd_xxh_digest_proof : zd_xxh_digest_stmt.
Proof.
  intros until lo. intros STB STL R0 R8 R1 ST RLO LO RSP SS MI ->.
  eapply digest_body; eassumption.
Qed.
Print Assumptions zd_xxh_digest_proof.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
