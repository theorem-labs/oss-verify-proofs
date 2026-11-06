(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.boost_beast.http_request.images Require Import Ubsan.
From OSSVerify.Proofs.boost_beast.http_request.lib Require Import Amb PropExec SymExec2 SymExec2Sound SymRun SymDrive SymDriveX RefMemcpyLib SymDriveH4.
From OSSVerify.Proofs.boost_beast.http_request.lib.Ub Require Import RefMainEntry RefMainEntryN LibStdioCall LibDiagKn.
Import ListNotations.
Import OSSVerify.Proofs.boost_beast.http_request.lib.PropExec.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import SX2. Import SX2S.

Abbreviation RSEGS := Ubsan.M.loaded_segments.

Definition STOPSM : list Z := [0x6c344; 0x6c204; 0x79550; 0x2bdbc; 0x2bb78; 0x2bb80; 0x2bc84; 0x2bca4; 0x2bcc0; 0x2bd18; 0x2bd34; 0x2bd7c]%Z.
Definition FUELM : nat := 3000.
Definition runM (scr : scripts) (ss : sym_state) := sym_exec RSEGS FUELM true STOPSM scr ss [].
Definition carryM (r : sym_state * list sidecond * scripts) (kn : list kentry) := carry (s_log (fst (fst r))) kn [].
Definition noscr : scripts := SCR [] [] [].
Definition spx (k : Z) : expr := EAlu ALU_ADD (EVar 0) (ELit k).

(* [comment removed for export] *)
Definition MSTK : Z := 1024.
Definition knL : list kentry :=
  [KAlign (EVar 0) 16; KRange (EVar 0) 0x7fff80000000 0x800000000000;
   KWr (SA (EVar 0) (-128 - MSTK)) MSTK;
   KWr (SA (ELit 0) 0x84000) 0x34000;
   KImg 0x10000 0x7e000]%Z.

(* [comment removed for export] *)
Definition scrU : scripts := SCR [true] [] [].       (* [comment removed for export] *)
Definition rU := Eval vm_compute in runM scrU (SS 0x2baec sr_mainN [] kn_mainN 40).
Definition srU : list expr := Eval vm_compute in s_regs (fst (fst rU)).
Definition knU : list kentry := Eval vm_compute in fst (fst (carryM rU kn_mainN)).

(* [comment removed for export] *)
Definition scrA : scripts := SCR [false] [] [].
Definition rA := Eval vm_compute in runM scrA (SS 0x2baec sr_main [] kn_main 40).
Definition srA : list expr := Eval vm_compute in s_regs (fst (fst rA)).
Definition knA : list kentry := Eval vm_compute in fst (fst (carryM rA kn_main)).

(* [comment removed for export] *)
Definition srC0 : list expr := Eval vm_compute in sr_upd srA (ridx 10) (ELit 3).
Definition rC := Eval vm_compute in runM noscr (SS 0x7a2a8 srC0 [] knA 40).
Definition srC : list expr := Eval vm_compute in s_regs (fst (fst rC)).
Definition knC : list kentry := Eval vm_compute in fst (fst (carryM rC knA)).

(* [comment removed for export] *)
Definition srF0 : list expr := Eval vm_compute in sr_upd srA (ridx 10) (EVar 40).
Definition knF0 : list kentry := (KRange (EVar 40) (2 ^ 64 - 4095) (2 ^ 64 - 1))%Z :: knA.
Definition scrF : scripts := SCR [false] [] [].     (* [comment removed for export] *)
Definition rF := Eval vm_compute in runM scrF (SS 0x7a2a8 srF0 [] knF0 41).
Definition srF : list expr := Eval vm_compute in s_regs (fst (fst rF)).
Definition knF : list kentry := Eval vm_compute in fst (fst (carryM rF knF0)).

(* [comment removed for export] *)
Definition srE0 : list expr :=
  [ELit 0; EVar 15; spx (-128); EVar 17; ELit 0x96970; EVar 19; EVar 20; EVar 21; ELit 2; EVar 23; EVar 3; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31; EVar 2; EVar 33; ELit 3; ELit 65536; EVar 36; EVar 37; EVar 38; EVar 39; EVar 40; EVar 41; EVar 42; EVar 43; EVar 44; EVar 45]%Z.
Definition scrE : scripts := SCR [false] [] [].     (* [comment removed for export] *)
Definition rE := Eval vm_compute in runM scrE (SS 0x2bb40 srE0 [] knL 46).
Definition srE : list expr := Eval vm_compute in s_regs (fst (fst rE)).
(* [comment removed for export] *)
Definition srN0 : list expr :=
  [ELit 0; EVar 15; spx (-128); EVar 17; ELit 0x96970; EVar 19; EVar 20; EVar 21; ELit 2; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31; EVar 2; EVar 4; ELit 3; EVar 5; ELit 0x84f89; EVar 3; EVar 38; EVar 39; EVar 40; EVar 41; EVar 42; EVar 43; EVar 44; EVar 45]%Z.
Definition scrN : scripts := SCR [true] [] [].      (* [comment removed for export] *)
Definition scrN' : scripts := SCR [false] [] [].
Definition rN := Eval vm_compute in runM scrN (SS 0x2bb78 srN0 [] knL 46).
Definition rN' := Eval vm_compute in runM scrN' (SS 0x2bb78 srN0 [] knL 46).
Definition srN : list expr := Eval vm_compute in s_regs (fst (fst rN)).
Definition srN' : list expr := Eval vm_compute in s_regs (fst (fst rN')).
Definition knN : list kentry := Eval vm_compute in fst (fst (carryM rN knL)).
Definition knN' : list kentry := Eval vm_compute in fst (fst (carryM rN' knL)).
(* [comment removed for export] *)
Definition srR0 : list expr :=
  [ELit 0; EVar 15; spx (-128); EVar 17; ELit 0x96970; EVar 19; EVar 20; EVar 21; ELit 2; EVar 3; EVar 24; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31; EVar 2; EVar 4; ELit 3; EVar 5; ELit 0x84f89; EVar 37; EVar 38; EVar 39; EVar 40; EVar 41; EVar 42; EVar 43; EVar 44; EVar 45]%Z.
Definition scrR : scripts := SCR [true] [] [].
Definition scrR' : scripts := SCR [false] [] [].
Definition rR := Eval vm_compute in runM scrR (SS 0x2bbb8 srR0 [] knL 46).
Definition rR' := Eval vm_compute in runM scrR' (SS 0x2bbb8 srR0 [] knL 46).
Definition srR : list expr := Eval vm_compute in s_regs (fst (fst rR)).
Definition srR' : list expr := Eval vm_compute in s_regs (fst (fst rR')).
Definition knR : list kentry := Eval vm_compute in fst (fst (carryM rR knL)).
Definition knR' : list kentry := Eval vm_compute in fst (fst (carryM rR' knL)).
(* [comment removed for export] *)
Definition srL50 : list expr :=
  [ELit 0; ELit 0x7d2e4; spx (-144); EVar 17; ELit 0x96970; EVar 19; EVar 20; EVar 21; ELit 2; EVar 3; EVar 7; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31; EVar 2; EVar 4; ELit 3; EVar 5; ELit 0x84f89; EVar 37; EVar 38; EVar 39; EVar 40; EVar 41; EVar 42; EVar 43; EVar 44; EVar 45]%Z.
Definition knL5 : list kentry := KWord (SA (EVar 0) (-136)) 8 (ELit 0x2bbd4) :: knL.
(* [comment removed for export] *)
Definition scrL5a : scripts := SCR [true; false; true] [] [].
Definition rL5a := Eval vm_compute in runM scrL5a (SS 0x7a2a8 srL50 [] knL5 46).
Definition srL5a : list expr := Eval vm_compute in s_regs (fst (fst rL5a)).
(* [comment removed for export] *)
Definition srL50z : list expr := Eval vm_compute in sr_upd srL50 (ridx 10) (ELit 0).
Definition rL5b := Eval vm_compute in runM noscr (SS 0x7a2a8 srL50z [] knL5 46).
Definition srL5b : list expr := Eval vm_compute in s_regs (fst (fst rL5b)).
Definition knL5b : list kentry := Eval vm_compute in fst (fst (carryM rL5b knL5)).
(* [comment removed for export] *)
Definition srL50e : list expr := Eval vm_compute in sr_upd srL50 (ridx 10) (ELit (2^64 - 21)).
Definition rL5c := Eval vm_compute in runM noscr (SS 0x7a2a8 srL50e [] knL5 46).
Definition srL5c : list expr := Eval vm_compute in s_regs (fst (fst rL5c)).
(* [comment removed for export] *)
Definition srM0 : list expr :=
  [ELit 0; EVar 15; spx (-128); EVar 17; ELit 0x96970; EVar 19; EVar 20; EVar 21; ELit 2; EVar 3; EVar 24; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31; EVar 2; EVar 4; ELit 3; EVar 5; ELit 0x84f89; EVar 7; EVar 38; EVar 39; EVar 40; EVar 41; EVar 42; EVar 43; EVar 44; EVar 45]%Z.
Definition scrMa : scripts := SCR [false] [] [].    (* [comment removed for export] *)
Definition scrMb : scripts := SCR [true] [] [].     (* [comment removed for export] *)
Definition rMa := Eval vm_compute in runM scrMa (SS 0x2bb6c srM0 [] knL 46).
Definition rMb := Eval vm_compute in runM scrMb (SS 0x2bb6c srM0 [] knL 46).
Definition srMa : list expr := Eval vm_compute in s_regs (fst (fst rMa)).
Definition srMb : list expr := Eval vm_compute in s_regs (fst (fst rMb)).
(* [comment removed for export] *)
Definition srG0 : list expr :=
  [ELit 0; EVar 15; spx (-128); EVar 17; ELit 0x96970; EVar 19; EVar 20; EVar 21; ELit 2; EVar 3; EVar 24; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31; EVar 2; EVar 4; ELit 3; EVar 4; ELit 0x84f89; EVar 3; EVar 38; EVar 39; EVar 40; EVar 41; EVar 42; EVar 43; EVar 44; EVar 45]%Z.
Definition scrGb : scripts := SCR [false] [] [].    (* [comment removed for export] *)
Definition scrGr : scripts := SCR [true] [] [].     (* [comment removed for export] *)
Definition rGb := Eval vm_compute in runM scrGb (SS 0x2bb80 srG0 [] knL 46).
Definition rGr := Eval vm_compute in runM scrGr (SS 0x2bb80 srG0 [] knL 46).
Definition srGb : list expr := Eval vm_compute in s_regs (fst (fst rGb)).
Definition srGr : list expr := Eval vm_compute in s_regs (fst (fst rGr)).
(* [comment removed for export] *)
Definition srL20 : list expr :=
  [ELit 0; EVar 15; spx (-128); EVar 17; ELit 0x96970; EVar 19; EVar 20; EVar 21; ELit 2; EVar 3; EVar 6; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31; EVar 2; EVar 4; ELit 3; EVar 5; ELit 0x84f89; EVar 3; EVar 38; EVar 39; EVar 40; EVar 41; EVar 42; EVar 43; EVar 44; EVar 45]%Z.
Definition scrL2 : scripts := SCR [false; false] [] [].   (* [comment removed for export] *)
Definition rL2 := Eval vm_compute in runM scrL2 (SS 0x2bb94 srL20 [] knL 46).
Definition srL2 : list expr := Eval vm_compute in s_regs (fst (fst rL2)).
(* [comment removed for export] *)
Definition srL30 : list expr :=
  [ELit 0; EVar 15; spx (-128); EVar 17; ELit 0x96970; EVar 19; EVar 20; EVar 21; ELit 2; EVar 6; EVar 24; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31; EVar 2; EVar 4; ELit 3; EVar 5; ELit 0x84f89; EVar 3; EVar 38; EVar 39; EVar 40; EVar 41; EVar 42; EVar 43; EVar 44; EVar 45]%Z.
Definition rL3 := Eval vm_compute in runM noscr (SS 0x2bbb0 srL30 [] knL 46).
Definition srL3 : list expr := Eval vm_compute in s_regs (fst (fst rL3)).
(* [comment removed for export] *)
Definition srH0 : list expr :=
  [ELit 0; ELit 0x7d224; spx (-144); EVar 17; ELit 0x96970; EVar 19; EVar 20; EVar 21; ELit 2; EVar 3; ELit 0; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31; EVar 2; EVar 4; ELit 3; EVar 5; EVar 36; EVar 37; EVar 38; EVar 39; EVar 40; EVar 41; EVar 42; EVar 43; EVar 44; EVar 45]%Z.
Definition knH : list kentry := KWord (SA (EVar 0) (-136)) 8 (ELit 0x2bbe8) :: knL.
(* [comment removed for export] *)
Definition scrHs : scripts := SCR [true] [] [].
Definition rHs := Eval vm_compute in runM scrHs (SS 0x7a2a8 srH0 [] knH 46).
Definition srHs : list expr := Eval vm_compute in s_regs (fst (fst rHs)).
(* [comment removed for export] *)
Definition scrHo : scripts := SCR [false; true] [EVar 13; EVar 12] [].
Definition rHo := Eval vm_compute in runM scrHo (SS 0x7a2a8 srH0 [] knH 46).
Definition srHo : list expr := Eval vm_compute in s_regs (fst (fst rHo)).
(* [comment removed for export] *)
Definition scrHk : scripts := SCR [false; false] [EVar 13; EVar 12; EVar 9; EVar 8; EVar 10; EVar 11] [].
Definition rHk := Eval vm_compute in runM scrHk (SS 0x7a2a8 srH0 [] knH 46).
Definition srHk : list expr := Eval vm_compute in s_regs (fst (fst rHk)).
(* [comment removed for export] *)
Definition srI0 : list expr :=
  [ELit 0; EVar 15; spx (-128); EVar 17; ELit 0x96970; EVar 19; EVar 20; EVar 21; EVar 22; EVar 3; EVar 24; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31; EVar 32; EVar 33; EVar 34; EVar 35; EVar 36; EVar 37; EVar 38; EVar 39; EVar 40; EVar 41; EVar 42; EVar 43; EVar 44; EVar 45]%Z.
Definition rI := Eval vm_compute in runM noscr (SS 0x2bce0 srI0 [] knL 46).
Definition srI : list expr := Eval vm_compute in s_regs (fst (fst rI)).

(* [comment removed for export] *)
Definition summary (r : sym_state * list sidecond * scripts) := (s_pc (fst (fst r)), snd (fst r), snd r).
