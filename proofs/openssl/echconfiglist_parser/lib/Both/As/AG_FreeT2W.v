(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation FMapPositive.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.openssl.echconfiglist_parser.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib Require Import HeapCeil.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import Tac Image ZBridge SysStep SFModel CellsX Arr TacX.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib Require Import AsanAllocModel. From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both Require Import AsanAllocCons. From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib Require Import SReach LazyRestrict LazyLedger LazySR LazyNodes.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.As Require Import ASegs AsShadow AllocWf AllocKit AllocBudget AllocRep AllocRepX AsDepotInv AsDepotHash AsUnwind AW_MallocBase AW_Put1
     AG_Malloc2 AG_Free2 AG_RepQ AG_FreeMid AG_FreeTail AG_WriteSet AG_RecycleDefs AG_RecEntry AG_FreeT2.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section HCW.
  Context {HCEIL : HeapCeil}.

Section FreeTail2W.
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (Q : config -> Prop).
  Variables (s : ast) (LB : list (Z * Z)) (d : depot) (lo : Z) (CH : list (Z * Z)) (ch : chunk).
  Let CHI := icpt_chain (bv_unsigned ra) (bv_unsigned s0) (bv_unsigned sp) (a_top s) CH.
  Let T := utrace 0x1bf2bc (bv_unsigned sp) (a_top s) (a_bot s) 30 CHI.
  Let d' := d_put d (depot_hash T) (Z.of_nat (length T)).
  Let LB' := lb_remove (ch_user_beg ch) LB.

  Hypothesis LO : aceil <= lo.
  Hypothesis HI : lo + 3200 <= bv_unsigned sp.
  Hypothesis SPT : bv_unsigned sp + 16 <= 2^47.
  Hypothesis SPA : bv_unsigned sp mod 16 = 0.
  Hypothesis TPv : bv_unsigned tp = ATP.
  Hypothesis DLO : d_nb d' + 16 * 65536 <= lo /\ d_sb d' + 8 * 131072 <= lo.

  Definition free_tail2_w :=
    free_tail2_raw ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc Q s LB d lo CH ch LO HI SPT SPA TPv DLO
      (rec_pre_ok sp lo LB' LO HI) (rec_entry_ok sp lo d' LB' LO HI).
End FreeTail2W.
End HCW.
