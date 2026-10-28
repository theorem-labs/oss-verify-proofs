(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import FseNCount FseLemmas ZdFrame ZdFrameThm.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import Tac Arr Bytes ZBridge.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import FseWalkKit ZdFrameW ZdWalkKit.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.LibA Require Import ExecF StepF Shadow.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import KXExec KXSound KXFull KXBridge KXTac KXGo KXTree KXAuto KXMem KXPost KXGoF.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import KXLean KXLeanAll.   (* [comment removed for export] *)
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.AsanT Require Import BImg RtCells ABase AZ_kit AZ_frame_iface AZ_libc_iface AZ_libc AZ_kx.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import RunDraw.
Import ListNotations. Import KXS.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section CANSEC1. Context {rc : runConstT}.

Lemma zd_xxh_reset_proofA : zd_xxh_reset_stmtA.
Proof.
  intros RNG ra gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m SPV STA cs0 lo.
  intros SC SSZ STA0 STA8 STA1 ST LO SPV47 SS ARS AHS ART AST MI ->.
  destruct (ARS ltac:(lia)) as (ABS & US & RS & RSS). clear ARS.
  pose proof ART as (GOT & RIC & SHB & INI & LAY & REAL).
  pose proof AST as (KLO & RSTK & RI). unfold KHIGH in KLO.
  pose proof ATOP_range as ATR. unfold ATOP_MIN, ATOP_MAX in ATR.
  assert (SA : STA + 88 <= 0x7fff7000 \/ 0x10007fff8000 <= STA) by (unfold ablk, AIMG_HI, KLS in ABS; lia).
  assert (SAL : 0x625000 <= STA) by (unfold ablk, AIMG_HI, KLS in ABS; lia).
  destruct (rw_cells_forget _ _ _ _ SC) as [junk SC1]. rewrite SSZ in SC1. clear SC.
  assert (MU : munch [(STA, STA + 88); (SPV - 2240, SPV)] m m) by apply munch_refl.
  assert (WM : wmono bsegs m m) by apply wmono_refl.
  carve_frame 32%nat ST.
  unfold APZD_XXH_RESET.
  kx_autoFLx [] 30%nat
    [KZRange SPV 4096 (2^47); KZRange STA 0x625000 (2^47 - 88); KZAlign STA 8; KZWr (SPV - 32) 32; KZWr STA 88; KZDisj STA 88 (SPV - 32) 32]
    [(SPV - 32, 32); (STA, 88)] [(SPV - 32, 32); (STA, 88)].
  all: try kx_cell_lit. all: try kx_z. all: try kx_acc RI.
  kx_mem.
  call (zd_memsetZ_proofA RNG STA 88 0 (SPV - 32)).
  all: try (first [ eassumption | lia | reflexivity ]).
  all: try (apply ablk_app_blk; [exact ABS | lia]).
  all: try (eapply astk_sub; [exact AST | lia]).
  all: try (lazymatch goal with |- art _ => unfold art; repeat (split; [eassumption|]); eassumption end).
  all: try (lazymatch goal with
            | |- aro ?R ?mc ?A 88 =>
                lazymatch goal with MUc : munch ?W ?m00 mc, U : unpoisoned ?m00 A _ |- _ =>
                  split; [eapply unpoisoned_munch; [exact U | exact MUc | cbn [disjoint_from]; rewrite !shad_div; unfold ASHOFF;
                            repeat split; Z.div_mod_to_equations; lia] | split; [exact RS | exact RSS]] end
            end).
  all: try (lazymatch goal with
            | |- ahull ?R ?mc ?A 88 =>
                lazymatch goal with WMc : wmono _ ?m00 mc |- _ =>
                  destruct AHS as (RLO & RHI & H1 & H2 & H3 & H4 & H5 & H6 & W0 & R0); exists RLO, RHI;
                  repeat (split; [lia|]); split; [eapply wr_at_transport; [exact W0 | exact WMc] | exact R0] end
            end).
  change (Z.to_nat 88) with 88%nat in POST.
  apply (rw_cells_split_CB bsegs _ _ [] _ _ _ [72; 4; 12]%nat) in POST; [| reflexivity]. cbn [mk_CB_cells app] in POST.
  apply (rw_cells_recell bsegs _ STA _ [CB 72 (firstn 72 (repeat (Z_to_bv 8 0) 88)); C4 (Z_to_bv 64 0); CB 12 (skipn 76 (repeat (Z_to_bv 8 0) 88))]) in POST;
    [| cbn; tauto | vm_compute; reflexivity].
  assert (US1 : unpoisoned x13 STA (STA + 88)).
  { eapply unpoisoned_munch; [exact US | exact MU | cbn [disjoint_from]; rewrite !shad_div; unfold ASHOFF;
      repeat split; Z.div_mod_to_equations; lia]. }
  kx_autoFLx [] 60%nat
    [KZRange SPV 4096 (2^47); KZRange STA 0x625000 (2^47 - 88); KZAlign STA 8; KZWr (SPV - 32) 32; KZWr STA 88; KZDisj STA 88 (SPV - 32) 32;
     KZImg 0x10338 0x103f8]
    [(SPV - 32, 32); (STA, 88)] [(SPV - 32, 32); (STA, 88)].
  all: try kx_cell_lit. all: try kx_z. all: try kx_acc RI. all: try kx_sh_acc RSS. all: try kx_sh_rd_any.
  all: try kx_sh_dead0_any.
  kx_mem. zstep.
  lazymatch goal with FRc : rw_cells _ ?mc (?S + -32) _, STc : stk _ ?mc ?l (?S - 32) |- _ => release_frame FRc STc S end.
  lazymatch goal with P : rw_cells _ _ STA (?c0 :: ?c1 :: ?c2 :: ?c3 :: ?c4 :: ?c5 :: ?rest) |- _ =>
    apply (rw_cells_merge bsegs _ STA [] [c0; c1; c2; c3; c4; c5] rest) in P end.
  lazymatch goal with P : rw_cells _ ?mc STA _ |- _ => cbn [app cells_size csize Nat.add] in P end.
  apply evtF_done. unfold zd_xxh_reset_postA.
  do 14 eexists. eexists. split; [reflexivity|].
  split; [eassumption|]. split; [eassumption|]. split; [eassumption|]. split; [eassumption|].
  unfold xxh_state, xxh_cells. do 2 eexists. eassumption.
Qed.
End CANSEC1.

