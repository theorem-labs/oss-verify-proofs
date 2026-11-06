(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.glaze.binary_reflection.lib Require BvWfKernel.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require WdZS.
#[local] Ltac Zify.zify ::= WdZS.wd_zs_stock.   (* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require Import AzSymExec3 AzSymExec3B AzPlanCore AzPlan AzAPS AzGPS AzIface AzContracts AzImageBoth AzOpNewH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AP. Import GPS. Import APC.
Open Scope Z_scope.
Definition OPNEW_RANGES : list (Z * nat) := [(0x1017a8, 18%nat)].
Definition IT_N : itab := mk_itab_ranges BSEGS OPNEW_RANGES.
Lemma IT_N_ok : itab_sound BSEGS IT_N. Proof. apply APS.mk_itab_ranges_sound. Qed.
Definition NXF : nat := 48.
Definition XNl := AzOpNewH.XN_live BSEGS GBOTH NXF 10 33.
Definition XE0 : nat -> list expr -> acs -> option (Z * list spiece * acs) := fun _ _ _ => None.
Definition XB0 : nat -> list expr -> acs -> option (acs * acs) := fun _ _ _ => None.
Definition XA0 : nat -> list expr -> acs -> option (acs * acs) := fun _ _ _ => None.

Definition ESP : expr := EVar 2.
Definition ERRNO : Z := g_errno GBOTH.
Definition regs0 : list expr := ELit 0 :: EVar 1 :: ESP :: EVar 3 :: ELit (g_tp GBOTH) :: map EVar (seq 5 27).
(* [comment removed for export] *)
Definition KCELLS : list kentry := g_opnew_kn GBOTH.
Definition KN0 : list kentry :=
  [KRange (EVar 10) 1 NMAX; KAlign ESP 16; KRange ESP (CEIL + 3600) (two47 - 16); KWr (SA ESP (-3600)) (ELit 3600);
   KRange (EVar 34) 1 64; KWr (SA (ELit 0) ERRNO) (ELit 4)] ++ KCELLS.
Definition mkH (p : Z) (regs : list expr) (k : list kentry) (nx : nat) (vis : list (expr * expr)) (mt : expr) : acs :=
  ACS (mk_ss p regs k nx) [] 0 3600 0 vis [(ELit ERRNO, ELit 4)] 0 ESP FdStd false mt [] (EVar 34).
Definition H0 : acs := mkH 0x1017a8 regs0 KN0 NXF [] (EVar 33).

(* [comment removed for export] *)
Definition EP : expr := EVar 100.
Definition regs1 : list expr :=
  [ELit 0; EVar 1; ESP; EVar 3; ELit (g_tp GBOTH); EVar 101; EVar 102; EVar 103;
   EVar 8; EVar 9; EP; EVar 104; EVar 105; EVar 106; EVar 107; EVar 108; EVar 109; EVar 110;
   EVar 18; EVar 19; EVar 20; EVar 21; EVar 22; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; EVar 111; EVar 112; EVar 113; EVar 114].
Definition KN1 : list kentry :=
  [KAlign EP 16; KWr (SA EP 0) (EVar 10); KShOk (SA EP 0) (EVar 10)] ++ KN0.
Definition MT1 : expr := EAlu Instr.ALU_ADD (EVar 33) (ELit EVT).   (* [comment removed for export] *)
Definition H1 : acs := mkH 0x1017ec regs1 KN1 115 [(EP, EVar 10)] MT1.
Definition HS1 (h : nat) : option acs := match h with 1%nat => Some H1 | _ => None end.
Definition CHKl (hs : nat -> option acs) (cs : acs) (p : plan) : cres :=
  AP.checkA BSEGS IT_N ABOTH NXF 0 GPS.ISP0 XNl XE0 XB0 XA0 AP.XT0 hs 0%nat false 400%nat 400%nat None cs p.

(* [comment removed for export] *)
Definition PLAN_E1 : plan := PRun [] (PExt 120 [] (PRun [] (PHandoff 1))).

(* [comment removed for export] *)
Lemma certE1_ok : CHKl HS1 H0 PLAN_E1 = COk (SHole 1).   Proof. vm_compute. reflexivity. Qed.
Lemma plans_ok : gplan_ok PLAN_E1 = true.
Proof. vm_compute. reflexivity. Qed.
