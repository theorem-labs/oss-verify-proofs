From Stdlib Require Import ZArith NArith List Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Lib Require Import Image.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.AS Require Import PropExec AxSymExec3.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.U Require Import El_xs_core El_xs_kitP El_xs_adapt.
Import ListNotations. Import AX2. Open Scope Z_scope.

Definition xspk (k : Z) : expr := if Z.eqb k 0 then XSP else EAlu ALU_ADD XSP (ELit k).

Definition xs_regsD (D : Z) : list expr :=
  [ELit 0; EVar 1; xspk (- D); EVar 3; EVar 4; EVar 5; EVar 6; EVar 7; EVar 8; EVar 9;
   EAlu ALU_ADD XBLK (ELit 128); EVar 11; EVar 12; EVar 13; EVar 14; EVar 15; EVar 16; EVar 17; EVar 18; EVar 19;
   EVar 20; EVar 21; EVar 22; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31].

Definition xs_ssD (D : Z) (xk : list kentry) (pc0 raval : Z) (uw : bool) : sym_state :=
  SS pc0 (xs_regsD D) [] (xs_kn0 raval uw ++ xk) 200.

Definition xk_end : list kentry :=
  [KWord (SA XSP (-40)) 8 (ELit 0x3da0c); KWord (SA XSP (-48)) 8 (EVar 50); KWord (SA XSP (-56)) 8 (EVar 51)].

Definition XS_KD : nat := 200.
