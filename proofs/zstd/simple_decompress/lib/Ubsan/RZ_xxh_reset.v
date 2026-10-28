(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import FseNCount FseLemmas ZdFrame ZdFrameThm.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import Tac Arr Bytes ZBridge Walk.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import FseWalkKit ZdFrameW ZdWalkKit.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Ubsan Require Import UImg RZ_libc_iface RZ_frame_iface.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Ubsan Require Import frame_kit.
Import ListNotations.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section RESET.
  Hypothesis MEMSET : zd_memsetZ_stmt.
  Variables (ra gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : fmem) (SP STA : Z) (cs0 : list cell) (lo : Z).
  Hypothesis SC0 : rw_cells usegs m STA cs0.
  Hypothesis SSZ : cells_size cs0 = 88%nat.
  Hypothesis ST : stk usegs m lo SP.
  Hypothesis LO : lo <= SP - 32.
  Hypothesis RSP : 0 <= SP < 2^64.
  Hypothesis SS : STA + 88 <= lo \/ SP <= STA.
  Hypothesis MI : mem_inv usegs m.
  Hypothesis STA0 : 0 < STA.
  Hypothesis STA8 : STA mod 8 = 0.

  Notation W := [(STA, STA + 88); (SP - 32, SP)].

  Lemma reset_body : evt usegs (zd_xxh_reset_post ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc SP STA lo m)
      (MS (mkR ra (Z_to_bv 64 SP) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 STA) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 PZD_XXH_RESET) fc None m (seg_rom usegs)).
  Proof.
    unfold PZD_XXH_RESET.
    destruct (rw_cells_forget _ _ _ _ SC0) as [junk SC]. rewrite SSZ in SC.
    pose proof (munch_refl W m) as MU. pose proof (wmono_refl usegs m) as WM.
    pose proof (rw_cells_bound _ _ _ _ SC) as SB. cbn [cells_size csize Nat.add] in SB.
    pose proof ST as (LO0 & _ & _).
    carve_frame 32%nat ST.
    do 4 zs. zs. fck. do 5 zs.
    call (MEMSET STA 88 0); [ exact SC | exact MI | reflexivity | reflexivity | reflexivity | lia | lia | lia | ].
    rename POST into SC'. rename MI0 into MI1. change (Z.to_nat 88) with 88%nat in SC'.
    apply (rw_cells_split_CB usegs _ _ [] _ _ _ [72; 4; 12]%nat) in SC'; [| reflexivity]. cbn [mk_CB_cells app] in SC'.
    apply (rw_cells_recell usegs _ STA _ [CB 72 (firstn 72 (repeat (Z_to_bv 8 0) 88)); C4 (Z_to_bv 64 0); CB 12 (skipn 76 (repeat (Z_to_bv 8 0) 88))]) in SC';
      [| cbn; tauto | vm_compute; reflexivity].
    zs. zs. fck. do 7 zs. fck. do 6 zs. fck. do 3 zs. fck. do 4 zs.
    (* [comment removed for export] *)
    match type of SC' with rw_cells _ _ _ (?c0 :: ?c1 :: ?c2 :: ?c3 :: ?c4 :: ?c5 :: ?rest) =>
      apply (rw_cells_merge usegs _ STA [] [c0; c1; c2; c3; c4; c5] rest) in SC' end.
    cbn [app cells_size csize Nat.add] in SC'.
    do 5 zs.
    release_frame FR ST SP.
    zs.
    apply evt_done. unfold zd_xxh_reset_post.
    do 14 eexists. eexists. split; [reflexivity|].
    split; [exact MU|]. split; [exact WM|]. split; [exact MI1|]. split; [exact ST|].
    unfold xxh_state, xxh_cells. do 2 eexists. exact SC'.
  Qed.
End RESET.

Theorem zd_xxh_reset_proof : zd_memsetZ_stmt -> zd_xxh_reset_stmt.
Proof.
  intros MEMSET. intros until lo. intros SC SSZ STA0 STA8 ST LO RSP SS MI ->.
  eapply reset_body; eassumption.
Qed.
