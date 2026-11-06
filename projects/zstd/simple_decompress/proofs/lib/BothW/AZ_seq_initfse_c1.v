(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Spec Require Import FseNCount FseLemmas ZdFrame ZdFrameThm ZdDCtx ZdSeqTable.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Lib Require Import Tac Arr Bytes ZBridge.
From OSSVerify.Proofs.zstd.simple_decompress.lib.LibA Require Import ExecF StepF Shadow.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Common Require Import FseWalkKit MemRange ZdSeqW ZdTbl KXExec KXSound KXFull KXBridge KXTac KXGo KXTree KXAuto KXMem KXMem2 KXPost KXGoF KXLean KXAsan KXAutoA KXUb KXUb2 SepHide.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Common Require Import KXLean KXLeanAll.   (* [comment removed for export] *)
From OSSVerify.Proofs.zstd.simple_decompress.lib.BothW Require Import BImg RtCells ABase AZ_kit AZ_kx AZ_globals AZ_globalsR AZ_huf_iface AZ_seq_bit_iface.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Common Require Import RunDraw.
Import ListNotations. Import KXS.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac kxa_norm ::= unfold shspan in *.
(* [comment removed for export] *)
Ltac kx_pull ::= kx_pull1; kx_pull1.
Ltac kx_lia ::= kx_bv_ranges; solve [kx_lia_pruned].

Section CANSEC1. Context {rc : runConstT}.

(* [comment removed for export] *)
Ltac ifs_close :=
  apply evtF_done; unfold zd_initfse_postA, sbd_cells;
  repeat (lazymatch goal with |- ex _ => eexists end);
  split; [reflexivity|]; split; [eassumption|]; split; [eassumption|]; split; [eassumption|]; split; [eassumption|];
  split; [match goal with H : rw_cells _ _ ?B (C8 _ :: C4 _ :: _) |- rw_cells _ _ ?B2 _ => constr_eq B B2; exact H end|];
  split; [match goal with H : rw_cells _ _ ?S [C8 _; C8 _] |- rw_cells _ _ ?S2 _ => constr_eq S S2; exact H end|];
  split; [apply sland_mask_lt; lia|]; split; [lia|]; unfold bit_okS; intros; lia.

Lemma ifs_c1 : zd_initfse_stmtA_if (fun bc tl ptr SEQ n => 65 <= bc + tl).
Proof.
  unfold zd_initfse_stmtA_if, APZD_INITFSE. intros until t.
  intros HBD HST TB OK SQB R1 R2 R3 R4 R5 R5b R6 R7 R8 A1 A2 A3 DJ1 DJ2 DJ3 DJ4 DJ5 RB RBB IB STK LOS SPB OS1 OS2 OS3 OS4 APB AROB APS AROS AROQ AROT ACL ART AST MI C. cbv beta in C.
  pose proof (seq_rdn_log bsegs m T k t TB OK) as RL. pose proof (seq_tl_range k t OK) as RT.
  remember (st_log t) as tl eqn:Etl.
  pose proof (sbitmask_know m tl MI ltac:(clear - RT; lia)) as BK. unfold SBITMASK in BK. change (0x220e0) with 139488 in BK.
  assert (RP : 1 <= 2^tl <= 512) by (clear - RT; split; [pose proof (Z.pow_pos_nonneg 2 tl); lia | change 512 with (2^9); apply Z.pow_le_mono_r; lia]).
  remember (Z.of_nat (length sqb)) as n eqn:En.
  destruct ART as (GOT & RIC & SHB & INI & LAY & REAL).
  destruct AST as (KLO & RSTK & RI). unfold KHIGH in KLO.
  destruct AROB as (UB & RGB & RGBS). destruct AROS as (US & RGS & RGSS). destruct AROQ as (UQ & RGQ & RGQS). destruct AROT as (UT & RGT & RGTS).
  pose proof (aro_client_at RNG m 139488 128 ACL ltac:(cbn [ACLIENT_RO In]; tauto)) as (UM & RGM & RGMS).
  assert (BDB : BD + 40 <= 0x7fff8000 \/ 0x10007fff8000 <= BD) by (unfold app_blk, KLOW, KHIGH, KEND in APB; clear - APB; lia).
  assert (SPB2 : STP + 16 <= 0x7fff8000 \/ 0x10007fff8000 <= STP) by (unfold app_blk, KLOW, KHIGH, KEND in APS; clear - APS; lia).
  assert (MU : munch [(BD, BD + 40); (STP, STP + 16); (SPV - 16, SPV)] m m) by apply munch_refl.
  assert (WM : wmono bsegs m m) by apply wmono_refl.
  assert (RG : 4096 <= BD < 2^47 /\ 4096 <= STP < 2^47 /\ 4096 <= SEQ < 2^47 /\ 4096 <= SEQ + n < 2^47) by lia.
  assert (T16 : 16 <= 8 * (1 + 2^tl)) by (clear - RP; lia).
  assert (UT16 : unpoisoned m T (T + 16)) by (eapply unpoisoned_sub; [exact UT | lia | clear - T16; lia]).
  assert (RGT16 : rng RNG T 16) by (eapply rng_sub'; [exact RGT | clear - T16; lia]).
  assert (RGTS16 : rng RNG (shad T) (shspan T 16))
    by (pose proof (shspan_sub T (8 * (1 + 2^tl)) T 16 ltac:(lia) ltac:(lia) ltac:(clear - T16; lia)) as [SS1 SS2];
        eapply rng_sub'; [exact RGTS | split; [exact SS1 | exact SS2]]).
  clear UT RGT RGTS.
  unfold sbd_cells in HBD. unfold bit_okS in IB.
  carve_frame 16%nat STK.
  clear TB ACL APB APS.
  (* [comment removed for export] *)
  hide DJ1. hide DJ2. hide DJ3. hide DJ4. hide DJ5. hide OS1. hide OS2. hide OS3. hide OS4.
  
  kx_autoFLAx [KAUnp BD 40; KAUnp STP 16; KAUnp SEQ n; KAUnp T 16; KAUnp 139488 128; KAApp BD 40; KAApp STP 16; KAApp (SPV - 16) 16] (@nil Z) 300%nat
      [KZRange bc 0 82; KZRange (bc + tl) 65 91; KZRange n 1 (2^47);
       KZRange BD 4096 (2^47 - 40); KZRange STP 4096 (2^47 - 16); KZRange T 4096 (2^47 - 16); KZRange SEQ 4096 (2^47); KZRange (SEQ + n) 4096 (2^47);
       KZRange SPV 4112 (2^47); KZRange tl 0 9; KZRange (2^tl) 1 512; KZAlign BD 8; KZAlign STP 8; KZAlign T 4;
       KZWord (T + 4) 4 tl; KZWord (139488 + 4 * tl) 4 (2^tl - 1);
       KZWr BD 40; KZWr STP 16; KZWr (SPV - 16) 16; KZDisj BD 40 STP 16; KZDisj BD 40 SEQ n; KZDisj STP 16 SEQ n;
       KZDisj (SPV - 16) 16 BD 40; KZDisj (SPV - 16) 16 STP 16; KZDisj (SPV - 16) 16 SEQ n; KZDisj BD 40 T 16; KZDisj STP 16 T 16; KZDisj (SPV - 16) 16 T 16]
      [(SEQ, n); (SPV - 16, 16); (BD, 40); (STP, 16)] [(BD, 40); (STP, 16); (SPV - 16, 16)].
  all: try kx_cell_lit.
  all: try (lazymatch goal with |- _ /\ _ /\ _ /\ rdn _ _ _ _ = Some _ => split; [lia | split; [lia | split; [lia | assumption]]] end).
  all: try (lazymatch goal with |- accP _ _ _ => first [kx_acc RGQ | kx_acc RGB | kx_acc RGS | kx_acc RGT16 | kx_acc RGM | kx_acc RSTK | kx_acc RI] end).
  all: try (lazymatch goal with |- evtF _ _ _ _ => fail | |- accP _ _ _ => fail | _ => kx_z end).
  (* [comment removed for export] *)
  all: try (lazymatch goal with |- evtF _ _ _ _ => fail | _ => try kx_side_pre;
            lazymatch goal with |- _ /\ _ /\ (?A + _ <= ?B \/ _) =>
              let X := base_of A in let Y := base_of B in unhide_related X Y;
              repeat match goal with H : hidden _ |- _ => clear H end; repeat split; lia end end).
  all: lazymatch goal with |- evtF _ _ _ (MS _ _ (Z_to_bv 64 615468) _ _ _ _) => kx_trap_fast | _ => idtac end.
  all: unhide.
  all: kx_mem.
  all: zstep.
  all: kx_abs.
  all: release_frame FR STK SPV.
  all: kx_mkR_fold.
  all: ifs_close.
Qed.
End CANSEC1.
