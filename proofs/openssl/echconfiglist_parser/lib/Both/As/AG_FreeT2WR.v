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
     AG_Malloc2 AG_Free2 AG_RepQ AG_FreeMid AG_FreeTail AG_WriteSet AG_RecycleDefs AG_RecEntry AG_FreeT2
     AW_PutR1 AW_EnqueueR1 AW_PutR2 AG_FreeTailR AG_RecEntryR AG_FreeT2R.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section HCW.
  Context {HCEIL : HeapCeil}.

Section FreeTail2WR.
  Variables (sp gp tp cs0 cs2 cs3 cs4 cs5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (Q : config -> Prop).
  Variables (s : ast) (LB : list (Z * Z)) (d : depot) (lo : Z) (ch : chunk).
  Variables (T : list Z) (RFr : mem -> Prop).
  Let d' := d_put d (depot_hash T) (Z.of_nat (length T)).
  Let LB' := lb_remove (ch_user_beg ch) LB.

  Hypothesis LO : aceil <= lo.
  Hypothesis HI : lo + 3280 <= bv_unsigned sp.
  Hypothesis RFrA : forall m0 m1, RFr m0 -> agree_on (fun a => bv_unsigned sp + -2208 <= a) m0 m1 -> RFr m1.
  Hypothesis SPT : bv_unsigned sp + 16 <= 2^47.
  Hypothesis SPA : bv_unsigned sp mod 16 = 0.
  Hypothesis TPv : bv_unsigned tp = ATP.
  Hypothesis DLO : d_nb d' + 16 * 65536 <= lo /\ d_sb d' + 8 * 131072 <= lo.

  Definition free_tail2_wR :=
    free_tail2_rawR sp gp tp cs0 cs2 cs3 cs4 cs5 s6 s7 s8 s9 s10 s11 F fc Q s LB d lo ch T RFr LO HI RFrA SPT SPA TPv DLO
      (rec_pre_okR sp lo LB' LO HI) (rec_entry_okR sp lo d' LB' LO HI).
End FreeTail2WR.
End HCW.
