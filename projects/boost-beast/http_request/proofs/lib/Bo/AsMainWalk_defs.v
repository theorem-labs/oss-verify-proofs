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
From OSSVerify.boost_beast.http_request.images Require Import AsanUbsan.
From OSSVerify.Proofs.boost_beast.http_request.lib Require Import Amb
  PropExec SymExec2 SymExec2Sound SymRun SymDrive SymDriveX MainWalk_defs.
Import ListNotations.
Import OSSVerify.Proofs.boost_beast.http_request.lib.PropExec.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import SX2. Import SX2S.

Abbreviation RSEGS := AsanUbsan.M.loaded_segments.

Definition STOPSAM : list Z :=
  [0x74544; 0x74540; 0x729bc; 0x612bc; 0xa426c; 0xa4028; 0xa4030; 0xa4190; 0xa4134; 0xa4154; 0xa4170; 0xa41c8; 0xa41e4; 0xa422c; 0x1035e8]%Z.
Definition runAM (scr : scripts) (ss : sym_state) := sym_exec RSEGS FUELM true STOPSAM scr ss [].

(* [comment removed for export] *)
Definition aknL : list kentry :=
  [KAlign (EVar 0) 16; KRange (EVar 0) 0x7fff80000000 0x800000000000;
   KWr (SA (EVar 0) (-128 - MSTK)) MSTK;
   KImg 0x10000 0x4e000; KImg 0x119000 0x121000]%Z.

(* [comment removed for export] *)
Definition ESTK : Z := 2048.
Definition kn_amain : list kentry :=
  [KAlign (EVar 0) 16; KRange (EVar 0) 0x7fff80000000 0x800000000000;
   KWr (SA (EVar 0) (- ESTK)) ESTK;
   KWord (SA (EVar 0) 8) 8 (EVar 1); KWord (SA (EVar 0) 16) 8 (EVar 2);
   KWord (SA (ELit 0) 0x681830) 8 (EVar 39);
   KWr (SA (ELit 0) 0x66174c) 4;
   KImg 0x10000 0x4e000; KImg 0x119000 0x121000]%Z.
(* [comment removed for export] *)
Definition kn_amainU : list kentry :=
  [KAlign (EVar 0) 16; KRange (EVar 0) 0x7fff80000000 0x800000000000;
   KWr (SA (EVar 0) (- ESTK)) ESTK;
   KImg 0x10000 0x4e000; KImg 0x119000 0x121000]%Z.

(* [comment removed for export] *)
Definition sr_amain : list expr :=
  [ELit 0; ELit 0x102ee8; spx (-48); EVar 9; ELit 0x6617f0; EVar 11; EVar 12; EVar 13; EVar 14; EVar 15; ELit 2; spx 8; EVar 18; EVar 19; EVar 20; EVar 21; EVar 22; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31; EVar 32; EVar 33; EVar 34; EVar 35; EVar 36; EVar 37]%Z.
Definition sr_amainN : list expr :=
  [ELit 0; ELit 0x102ee8; spx (-48); EVar 9; ELit 0x6617f0; EVar 11; EVar 12; EVar 13; EVar 14; EVar 15; EVar 16; spx 8; EVar 18; EVar 19; EVar 20; EVar 21; EVar 22; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31; EVar 32; EVar 33; EVar 34; EVar 35; EVar 36; EVar 37]%Z.

(* [comment removed for export] *)
Definition scrU : scripts := SCR [true] [] [].       (* [comment removed for export] *)
Definition rU := Eval vm_compute in runAM scrU (SS 0xa3f9c sr_amainN [] kn_amainU 40).
Definition srU : list expr := Eval vm_compute in s_regs (fst (fst rU)).
Definition knU : list kentry := Eval vm_compute in fst (fst (carryM rU kn_amainU)).

(* [comment removed for export] *)
Definition scrA : scripts := SCR [] [] [].
Definition rA := Eval vm_compute in runAM scrA (SS 0xa3f9c sr_amain [] kn_amain 40).
Definition srA : list expr := Eval vm_compute in s_regs (fst (fst rA)).
Definition knA : list kentry := Eval vm_compute in fst (fst (carryM rA kn_amain)).

(* [comment removed for export] *)
Definition srC0 : list expr := Eval vm_compute in sr_upd srA (ridx 10) (ELit 3).
Definition rC := Eval vm_compute in runAM noscr (SS 0x112820 srC0 [] knA 40).
Definition srC : list expr := Eval vm_compute in s_regs (fst (fst rC)).
Definition knC : list kentry := Eval vm_compute in fst (fst (carryM rC knA)).

(* [comment removed for export] *)
Definition srF0 : list expr := Eval vm_compute in sr_upd srA (ridx 10) (EVar 40).
Definition knF0 : list kentry := (KRange (EVar 40) (2 ^ 64 - 4095) (2 ^ 64 - 1))%Z :: knA.
Definition scrF : scripts := SCR [false] [] [].     (* [comment removed for export] *)
Definition rF := Eval vm_compute in runAM scrF (SS 0x112820 srF0 [] knF0 41).
Definition srF : list expr := Eval vm_compute in s_regs (fst (fst rF)).
Definition knF : list kentry := Eval vm_compute in fst (fst (carryM rF knF0)).

(* [comment removed for export] *)
Definition srE0 : list expr :=
  [ELit 0; EVar 15; spx (-128); EVar 17; ELit 0x6617f0; EVar 19; EVar 20; EVar 21; ELit 2; EVar 23; EVar 3; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31; EVar 2; EVar 33; ELit 3; ELit 65536; EVar 36; EVar 37; EVar 38; EVar 39; EVar 40; EVar 41; EVar 42; EVar 43; EVar 44; EVar 45]%Z.
Definition scrE : scripts := SCR [false] [] [].     (* [comment removed for export] *)
Definition rE := Eval vm_compute in runAM scrE (SS 0xa3ff0 srE0 [] aknL 46).
Definition srE : list expr := Eval vm_compute in s_regs (fst (fst rE)).
(* [comment removed for export] *)
Definition srN0 : list expr :=
  [ELit 0; EVar 15; spx (-128); EVar 17; ELit 0x6617f0; EVar 19; EVar 20; EVar 21; ELit 2; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31; EVar 2; EVar 4; ELit 3; EVar 5; ELit 0x64fe10; EVar 3; EVar 38; EVar 39; EVar 40; EVar 41; EVar 42; EVar 43; EVar 44; EVar 45]%Z.
Definition scrN : scripts := SCR [true] [] [].      (* [comment removed for export] *)
Definition scrN' : scripts := SCR [false] [] [].
Definition rN := Eval vm_compute in runAM scrN (SS 0xa4028 srN0 [] aknL 46).
Definition rN' := Eval vm_compute in runAM scrN' (SS 0xa4028 srN0 [] aknL 46).
Definition srN : list expr := Eval vm_compute in s_regs (fst (fst rN)).
Definition srN' : list expr := Eval vm_compute in s_regs (fst (fst rN')).
(* [comment removed for export] *)
Definition srR0 : list expr :=
  [ELit 0; EVar 15; spx (-128); EVar 17; ELit 0x6617f0; EVar 19; EVar 20; EVar 21; ELit 2; EVar 3; EVar 24; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31; EVar 2; EVar 4; ELit 3; EVar 5; ELit 0x64fe10; EVar 37; EVar 38; EVar 39; EVar 40; EVar 41; EVar 42; EVar 43; EVar 44; EVar 45]%Z.
Definition scrR : scripts := SCR [true] [] [].
Definition scrR' : scripts := SCR [false] [] [].
Definition rR := Eval vm_compute in runAM scrR (SS 0xa4068 srR0 [] aknL 46).
Definition rR' := Eval vm_compute in runAM scrR' (SS 0xa4068 srR0 [] aknL 46).
Definition srR : list expr := Eval vm_compute in s_regs (fst (fst rR)).
Definition srR' : list expr := Eval vm_compute in s_regs (fst (fst rR')).
(* [comment removed for export] *)
Definition srL50 : list expr :=
  [ELit 0; EVar 15; spx (-128); EVar 17; ELit 0x6617f0; EVar 19; EVar 20; EVar 21; ELit 2; EVar 3; EVar 7; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31; EVar 2; EVar 4; ELit 3; EVar 5; ELit 0x64fe10; EVar 37; EVar 38; EVar 39; EVar 40; EVar 41; EVar 42; EVar 43; EVar 44; EVar 45]%Z.
(* [comment removed for export] *)
Definition scrL5a : scripts := SCR [false; true] [] [].
Definition rL5a := Eval vm_compute in runAM scrL5a (SS 0xa4084 srL50 [] aknL 46).
Definition srL5a : list expr := Eval vm_compute in s_regs (fst (fst rL5a)).
(* [comment removed for export] *)
Definition srL50z : list expr := Eval vm_compute in sr_upd srL50 (ridx 10) (ELit 0).
Definition rL5b := Eval vm_compute in runAM noscr (SS 0xa4084 srL50z [] aknL 46).
Definition srL5b : list expr := Eval vm_compute in s_regs (fst (fst rL5b)).
Definition knL5b : list kentry := Eval vm_compute in fst (fst (carryM rL5b aknL)).
(* [comment removed for export] *)
Definition srL50e : list expr := Eval vm_compute in sr_upd srL50 (ridx 10) (ELit (2^64 - 1)).
Definition rL5c := Eval vm_compute in runAM noscr (SS 0xa4084 srL50e [] aknL 46).
Definition srL5c : list expr := Eval vm_compute in s_regs (fst (fst rL5c)).
(* [comment removed for export] *)
Definition srM0 : list expr :=
  [ELit 0; EVar 15; spx (-128); EVar 17; ELit 0x6617f0; EVar 19; EVar 20; EVar 21; ELit 2; EVar 3; EVar 24; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31; EVar 2; EVar 4; ELit 3; EVar 5; ELit 0x64fe10; EVar 7; EVar 38; EVar 39; EVar 40; EVar 41; EVar 42; EVar 43; EVar 44; EVar 45]%Z.
Definition scrMa : scripts := SCR [false] [] [].    (* [comment removed for export] *)
Definition scrMb : scripts := SCR [true] [] [].     (* [comment removed for export] *)
Definition rMa := Eval vm_compute in runAM scrMa (SS 0xa401c srM0 [] aknL 46).
Definition rMb := Eval vm_compute in runAM scrMb (SS 0xa401c srM0 [] aknL 46).
Definition srMa : list expr := Eval vm_compute in s_regs (fst (fst rMa)).
Definition srMb : list expr := Eval vm_compute in s_regs (fst (fst rMb)).
(* [comment removed for export] *)
Definition srG0 : list expr :=
  [ELit 0; EVar 15; spx (-128); EVar 17; ELit 0x6617f0; EVar 19; EVar 20; EVar 21; ELit 2; EVar 3; EVar 24; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31; EVar 2; EVar 4; ELit 3; EVar 4; ELit 0x64fe10; EVar 3; EVar 38; EVar 39; EVar 40; EVar 41; EVar 42; EVar 43; EVar 44; EVar 45]%Z.
Definition scrGb : scripts := SCR [false] [] [].    (* [comment removed for export] *)
Definition scrGr : scripts := SCR [true] [] [].     (* [comment removed for export] *)
Definition rGb := Eval vm_compute in runAM scrGb (SS 0xa4030 srG0 [] aknL 46).
Definition rGr := Eval vm_compute in runAM scrGr (SS 0xa4030 srG0 [] aknL 46).
Definition srGb : list expr := Eval vm_compute in s_regs (fst (fst rGb)).
Definition srGr : list expr := Eval vm_compute in s_regs (fst (fst rGr)).
(* [comment removed for export] *)
Definition srL20 : list expr :=
  [ELit 0; EVar 15; spx (-128); EVar 17; ELit 0x6617f0; EVar 19; EVar 20; EVar 21; ELit 2; EVar 3; EVar 6; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31; EVar 2; EVar 4; ELit 3; EVar 5; ELit 0x64fe10; EVar 3; EVar 38; EVar 39; EVar 40; EVar 41; EVar 42; EVar 43; EVar 44; EVar 45]%Z.
Definition scrL2 : scripts := SCR [false; false] [] [].   (* [comment removed for export] *)
Definition rL2 := Eval vm_compute in runAM scrL2 (SS 0xa4044 srL20 [] aknL 46).
Definition srL2 : list expr := Eval vm_compute in s_regs (fst (fst rL2)).
(* [comment removed for export] *)
Definition srL30 : list expr :=
  [ELit 0; EVar 15; spx (-128); EVar 17; ELit 0x6617f0; EVar 19; EVar 20; EVar 21; ELit 2; EVar 6; EVar 24; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31; EVar 2; EVar 4; ELit 3; EVar 5; ELit 0x64fe10; EVar 3; EVar 38; EVar 39; EVar 40; EVar 41; EVar 42; EVar 43; EVar 44; EVar 45]%Z.
Definition rL3 := Eval vm_compute in runAM noscr (SS 0xa4060 srL30 [] aknL 46).
Definition srL3 : list expr := Eval vm_compute in s_regs (fst (fst rL3)).
(* [comment removed for export] *)
Definition srH0 : list expr :=
  [ELit 0; ELit 0x1185f8; spx (-144); EVar 17; ELit 0x6617f0; EVar 19; EVar 20; EVar 21; ELit 2; EVar 3; ELit 0; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31; EVar 2; EVar 4; ELit 3; EVar 5; EVar 36; EVar 37; EVar 38; EVar 39; EVar 40; EVar 41; EVar 42; EVar 43; EVar 44; EVar 45]%Z.
Definition knH : list kentry := KWord (SA (EVar 0) (-136)) 8 (ELit 0xa4098) :: aknL.
(* [comment removed for export] *)
Definition scrHs : scripts := SCR [true] [] [].
Definition rHs := Eval vm_compute in runAM scrHs (SS 0x112820 srH0 [] knH 46).
Definition srHs : list expr := Eval vm_compute in s_regs (fst (fst rHs)).
(* [comment removed for export] *)
Definition scrHo : scripts := SCR [false; true] [EVar 13; EVar 12] [].
Definition rHo := Eval vm_compute in runAM scrHo (SS 0x112820 srH0 [] knH 46).
Definition srHo : list expr := Eval vm_compute in s_regs (fst (fst rHo)).
(* [comment removed for export] *)
Definition scrHk : scripts := SCR [false; false] [EVar 13; EVar 12; EVar 9; EVar 8; EVar 10; EVar 11] [].
Definition rHk := Eval vm_compute in runAM scrHk (SS 0x112820 srH0 [] knH 46).
Definition srHk : list expr := Eval vm_compute in s_regs (fst (fst rHk)).
(* [comment removed for export] *)
Definition srI0 : list expr :=
  [ELit 0; EVar 15; spx (-128); EVar 17; ELit 0x6617f0; EVar 19; EVar 20; EVar 21; EVar 22; EVar 3; EVar 24; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31; EVar 32; EVar 33; EVar 34; EVar 35; EVar 36; EVar 37; EVar 38; EVar 39; EVar 40; EVar 41; EVar 42; EVar 43; EVar 44; EVar 45]%Z.
Definition rI := Eval vm_compute in runAM noscr (SS 0xa4190 srI0 [] aknL 46).
Definition srI : list expr := Eval vm_compute in s_regs (fst (fst rI)).
(* [comment removed for export] *)
Definition srX0 : list expr :=
  [ELit 0; EVar 15; spx (-128); EVar 17; ELit 0x6617f0; EVar 19; EVar 20; EVar 21; EVar 22; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31; EVar 32; EVar 33; EVar 34; EVar 35; EVar 36; EVar 37; EVar 38; EVar 39; EVar 40; EVar 41; EVar 42; EVar 43; EVar 44; EVar 45]%Z.
Definition knX : list kentry :=
  ([KWord (SA (EVar 0) (-56)) 8 (ELit 0x102ee8);
    KWord (SA (EVar 0) (-120)) 8 (EVar 6); KWord (SA (EVar 0) (-112)) 8 (EVar 7); KWord (SA (EVar 0) (-104)) 8 (EVar 8);
    KWord (SA (EVar 0) (-96)) 8 (EVar 9); KWord (SA (EVar 0) (-88)) 8 (EVar 10); KWord (SA (EVar 0) (-80)) 8 (EVar 11);
    KWord (SA (EVar 0) (-72)) 8 (EVar 12); KWord (SA (EVar 0) (-64)) 8 (EVar 13)]%Z) ++ aknL.
Definition rX := Eval vm_compute in runAM noscr (SS 0xa4198 srX0 [] knX 46).
Definition srX : list expr := Eval vm_compute in s_regs (fst (fst rX)).

(* [comment removed for export] *)
Definition asummary (r : sym_state * list sidecond * scripts) := (s_pc (fst (fst r)), snd (fst r), snd r).
