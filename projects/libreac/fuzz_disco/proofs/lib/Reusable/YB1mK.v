(* Inputs of the split of YB1m.v's startup_cert (see YB1mW.v): the instruction table, the walk from the PVia join
   state to the argc split (yb1m_wband) and its stop state, the PVia arms, and the shapes of the parts. Definitions
   only: nothing is computed in this file. *)
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YK11 YK0c YK09 YA01 YA0c YA02 YA0h YB12 YB1h YB1l YB05 YB01 YB03 YB1mW.
Local Set Warnings "-abstract-large-number".
Import ListNotations.
Open Scope Z_scope.
Import AX2. Import APG.
Definition yb1m_it : itab := mk_itab_ranges TSEGS startup_plan_tfib_ranges.
Definition yb1m_wband : nat * acs * plan :=
YB1mW.walk TSEGS yb1m_it TFIB NX0G YA02.LIMIT (XNG TSEGS tfib_XN1) 0%nat 400000%nat 1000%nat 2847%nat JS_tfib_band startup_plan_tfib_band20.
Definition yb1m_css : acs := snd (fst yb1m_wband).
Definition yb1m_karms : plan :=
PCaseDisj (ELit 2147446784) (escale 4096 (EVar 275)) startup_plan_tfib_band20_arm startup_plan_tfib_band20_arm.
Definition yb1m_sa : shape := SAlt2 (SAlt2 (SHole 8) (SHole 9)) (SAlt2 (SHole 0) (SHole 1)).
Definition yb1m_sb : shape := SAlt2 (SAlt2 (SHole 24) (SHole 25)) (SAlt2 (SHole 16) (SHole 17)).
Definition yb1m_sc : shape := SAlt2 (SHole 36) (SHole 32).
Definition yb1m_shape : shape := SCase (EVar 6) 10 yb1m_sa (SCase (EVar 6) 1802 yb1m_sb yb1m_sc).
