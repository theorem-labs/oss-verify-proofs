(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OssFuzzTheorems.spirv_tools.spvtools_binary_parser_fuzzer.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BAmb BPropExec BSymExec2 BSymExec2Sound BSymRun BSymDrive BSymDriveX BainWalk_defs.
Import ListNotations.
Import BPropExec.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache. Import SX2. Import SX2S.

Abbreviation RSEGS := AsanUbsan.M.loaded_segments.

Definition STOPSAM : list Z :=
  [0xba108; 0xba104; 0xb8580; 0xa36a4; 0xe86c4; 0xe8480; 0xe8488; 0xe85e8; 0xe858c; 0xe85ac; 0xe85c8; 0xe8620; 0xe863c; 0xe8684; 0x165478]%Z.
Definition runAM (scr : scripts) (ss : sym_state) := sym_exec RSEGS FUELM true STOPSAM scr ss [].

Definition aknL : list kentry :=
  [KAlign (EVar 0) 16; KRange (EVar 0) 0x7fff80000000 0x800000000000;
   KWr (SA (EVar 0) (-128 - MSTK)) MSTK;
   KImg 0x10000 0x91000; KImg 0x17e000 0x186000]%Z.

Definition ESTK : Z := 2048.
Definition kn_amain : list kentry :=
  [KAlign (EVar 0) 16; KRange (EVar 0) 0x7fff80000000 0x800000000000;
   KWr (SA (EVar 0) (- ESTK)) ESTK;
   KWord (SA (EVar 0) 8) 8 (EVar 1); KWord (SA (EVar 0) 16) 8 (EVar 2);
   KWord (SA (ELit 0) 0x6e5898) 8 (EVar 39);
   KWr (SA (ELit 0) 0x6c57b4) 4;
   KImg 0x10000 0x91000; KImg 0x17e000 0x186000]%Z.

Definition kn_amainU : list kentry :=
  [KAlign (EVar 0) 16; KRange (EVar 0) 0x7fff80000000 0x800000000000;
   KWr (SA (EVar 0) (- ESTK)) ESTK;
   KImg 0x10000 0x91000; KImg 0x17e000 0x186000]%Z.

Definition sr_amain : list expr :=
  [ELit 0; ELit 0x164cb0; spx (-48); EVar 9; ELit 0x6c5858; EVar 11; EVar 12; EVar 13; EVar 14; EVar 15; ELit 2; spx 8; EVar 18; EVar 19; EVar 20; EVar 21; EVar 22; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31; EVar 32; EVar 33; EVar 34; EVar 35; EVar 36; EVar 37]%Z.
Definition sr_amainN : list expr :=
  [ELit 0; ELit 0x164cb0; spx (-48); EVar 9; ELit 0x6c5858; EVar 11; EVar 12; EVar 13; EVar 14; EVar 15; EVar 16; spx 8; EVar 18; EVar 19; EVar 20; EVar 21; EVar 22; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31; EVar 32; EVar 33; EVar 34; EVar 35; EVar 36; EVar 37]%Z.

Definition scrU : scripts := SCR [true] [] [].
Definition rU := Eval vm_compute in runAM scrU (SS 0xe83f4 sr_amainN [] kn_amainU 40).
Definition srU : list expr := Eval vm_compute in s_regs (fst (fst rU)).
Definition knU : list kentry := Eval vm_compute in fst (fst (carryM rU kn_amainU)).

Definition scrA : scripts := SCR [] [] [].
Definition rA := Eval vm_compute in runAM scrA (SS 0xe83f4 sr_amain [] kn_amain 40).
Definition srA : list expr := Eval vm_compute in s_regs (fst (fst rA)).
Definition knA : list kentry := Eval vm_compute in fst (fst (carryM rA kn_amain)).

Definition srC0 : list expr := Eval vm_compute in sr_upd srA (ridx 10) (ELit 3).
Definition rC := Eval vm_compute in runAM noscr (SS 0x177adc srC0 [] knA 40).
Definition srC : list expr := Eval vm_compute in s_regs (fst (fst rC)).
Definition knC : list kentry := Eval vm_compute in fst (fst (carryM rC knA)).

Definition srF0 : list expr := Eval vm_compute in sr_upd srA (ridx 10) (EVar 40).
Definition knF0 : list kentry := (KRange (EVar 40) (2 ^ 64 - 4095) (2 ^ 64 - 1))%Z :: knA.
Definition scrF : scripts := SCR [false] [] [].
Definition rF := Eval vm_compute in runAM scrF (SS 0x177adc srF0 [] knF0 41).
Definition srF : list expr := Eval vm_compute in s_regs (fst (fst rF)).
Definition knF : list kentry := Eval vm_compute in fst (fst (carryM rF knF0)).

Definition srE0 : list expr :=
  [ELit 0; EVar 15; spx (-128); EVar 17; ELit 0x6c5858; EVar 19; EVar 20; EVar 21; ELit 2; EVar 23; EVar 3; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31; EVar 2; EVar 33; ELit 3; ELit 65536; EVar 36; EVar 37; EVar 38; EVar 39; EVar 40; EVar 41; EVar 42; EVar 43; EVar 44; EVar 45]%Z.
Definition scrE : scripts := SCR [false] [] [].
Definition rE := Eval vm_compute in runAM scrE (SS 0xe8448 srE0 [] aknL 46).
Definition srE : list expr := Eval vm_compute in s_regs (fst (fst rE)).

Definition srN0 : list expr :=
  [ELit 0; EVar 15; spx (-128); EVar 17; ELit 0x6c5858; EVar 19; EVar 20; EVar 21; ELit 2; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31; EVar 2; EVar 4; ELit 3; EVar 5; ELit 0x6b3690; EVar 3; EVar 38; EVar 39; EVar 40; EVar 41; EVar 42; EVar 43; EVar 44; EVar 45]%Z.
Definition scrN : scripts := SCR [true] [] [].
Definition scrN' : scripts := SCR [false] [] [].
Definition rN := Eval vm_compute in runAM scrN (SS 0xe8480 srN0 [] aknL 46).
Definition rN' := Eval vm_compute in runAM scrN' (SS 0xe8480 srN0 [] aknL 46).
Definition srN : list expr := Eval vm_compute in s_regs (fst (fst rN)).
Definition srN' : list expr := Eval vm_compute in s_regs (fst (fst rN')).

Definition srR0 : list expr :=
  [ELit 0; EVar 15; spx (-128); EVar 17; ELit 0x6c5858; EVar 19; EVar 20; EVar 21; ELit 2; EVar 3; EVar 24; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31; EVar 2; EVar 4; ELit 3; EVar 5; ELit 0x6b3690; EVar 37; EVar 38; EVar 39; EVar 40; EVar 41; EVar 42; EVar 43; EVar 44; EVar 45]%Z.
Definition scrR : scripts := SCR [true] [] [].
Definition scrR' : scripts := SCR [false] [] [].
Definition rR := Eval vm_compute in runAM scrR (SS 0xe84c0 srR0 [] aknL 46).
Definition rR' := Eval vm_compute in runAM scrR' (SS 0xe84c0 srR0 [] aknL 46).
Definition srR : list expr := Eval vm_compute in s_regs (fst (fst rR)).
Definition srR' : list expr := Eval vm_compute in s_regs (fst (fst rR')).

Definition srL50 : list expr :=
  [ELit 0; EVar 15; spx (-128); EVar 17; ELit 0x6c5858; EVar 19; EVar 20; EVar 21; ELit 2; EVar 3; EVar 7; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31; EVar 2; EVar 4; ELit 3; EVar 5; ELit 0x6b3690; EVar 37; EVar 38; EVar 39; EVar 40; EVar 41; EVar 42; EVar 43; EVar 44; EVar 45]%Z.

Definition scrL5a : scripts := SCR [false; true] [] [].
Definition rL5a := Eval vm_compute in runAM scrL5a (SS 0xe84dc srL50 [] aknL 46).
Definition srL5a : list expr := Eval vm_compute in s_regs (fst (fst rL5a)).

Definition srL50z : list expr := Eval vm_compute in sr_upd srL50 (ridx 10) (ELit 0).
Definition rL5b := Eval vm_compute in runAM noscr (SS 0xe84dc srL50z [] aknL 46).
Definition srL5b : list expr := Eval vm_compute in s_regs (fst (fst rL5b)).
Definition knL5b : list kentry := Eval vm_compute in fst (fst (carryM rL5b aknL)).

Definition srL50e : list expr := Eval vm_compute in sr_upd srL50 (ridx 10) (ELit (2^64 - 1)).
Definition rL5c := Eval vm_compute in runAM noscr (SS 0xe84dc srL50e [] aknL 46).
Definition srL5c : list expr := Eval vm_compute in s_regs (fst (fst rL5c)).

Definition srM0 : list expr :=
  [ELit 0; EVar 15; spx (-128); EVar 17; ELit 0x6c5858; EVar 19; EVar 20; EVar 21; ELit 2; EVar 3; EVar 24; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31; EVar 2; EVar 4; ELit 3; EVar 5; ELit 0x6b3690; EVar 7; EVar 38; EVar 39; EVar 40; EVar 41; EVar 42; EVar 43; EVar 44; EVar 45]%Z.
Definition scrMa : scripts := SCR [false] [] [].
Definition scrMb : scripts := SCR [true] [] [].
Definition rMa := Eval vm_compute in runAM scrMa (SS 0xe8474 srM0 [] aknL 46).
Definition rMb := Eval vm_compute in runAM scrMb (SS 0xe8474 srM0 [] aknL 46).
Definition srMa : list expr := Eval vm_compute in s_regs (fst (fst rMa)).
Definition srMb : list expr := Eval vm_compute in s_regs (fst (fst rMb)).

Definition srG0 : list expr :=
  [ELit 0; EVar 15; spx (-128); EVar 17; ELit 0x6c5858; EVar 19; EVar 20; EVar 21; ELit 2; EVar 3; EVar 24; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31; EVar 2; EVar 4; ELit 3; EVar 4; ELit 0x6b3690; EVar 3; EVar 38; EVar 39; EVar 40; EVar 41; EVar 42; EVar 43; EVar 44; EVar 45]%Z.
Definition scrGb : scripts := SCR [false] [] [].
Definition scrGr : scripts := SCR [true] [] [].
Definition rGb := Eval vm_compute in runAM scrGb (SS 0xe8488 srG0 [] aknL 46).
Definition rGr := Eval vm_compute in runAM scrGr (SS 0xe8488 srG0 [] aknL 46).
Definition srGb : list expr := Eval vm_compute in s_regs (fst (fst rGb)).
Definition srGr : list expr := Eval vm_compute in s_regs (fst (fst rGr)).

Definition srL20 : list expr :=
  [ELit 0; EVar 15; spx (-128); EVar 17; ELit 0x6c5858; EVar 19; EVar 20; EVar 21; ELit 2; EVar 3; EVar 6; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31; EVar 2; EVar 4; ELit 3; EVar 5; ELit 0x6b3690; EVar 3; EVar 38; EVar 39; EVar 40; EVar 41; EVar 42; EVar 43; EVar 44; EVar 45]%Z.
Definition scrL2 : scripts := SCR [false; false] [] [].
Definition rL2 := Eval vm_compute in runAM scrL2 (SS 0xe849c srL20 [] aknL 46).
Definition srL2 : list expr := Eval vm_compute in s_regs (fst (fst rL2)).

Definition srL30 : list expr :=
  [ELit 0; EVar 15; spx (-128); EVar 17; ELit 0x6c5858; EVar 19; EVar 20; EVar 21; ELit 2; EVar 6; EVar 24; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31; EVar 2; EVar 4; ELit 3; EVar 5; ELit 0x6b3690; EVar 3; EVar 38; EVar 39; EVar 40; EVar 41; EVar 42; EVar 43; EVar 44; EVar 45]%Z.
Definition rL3 := Eval vm_compute in runAM noscr (SS 0xe84b8 srL30 [] aknL 46).
Definition srL3 : list expr := Eval vm_compute in s_regs (fst (fst rL3)).

Definition srH0 : list expr :=
  [ELit 0; ELit 0x17d450; spx (-144); EVar 17; ELit 0x6c5858; EVar 19; EVar 20; EVar 21; ELit 2; EVar 3; ELit 0; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31; EVar 2; EVar 4; ELit 3; EVar 5; EVar 36; EVar 37; EVar 38; EVar 39; EVar 40; EVar 41; EVar 42; EVar 43; EVar 44; EVar 45]%Z.
Definition knH : list kentry := KWord (SA (EVar 0) (-136)) 8 (ELit 0xe84f0) :: aknL.

Definition scrHs : scripts := SCR [true] [] [].
Definition rHs := Eval vm_compute in runAM scrHs (SS 0x177adc srH0 [] knH 46).
Definition srHs : list expr := Eval vm_compute in s_regs (fst (fst rHs)).

Definition scrHo : scripts := SCR [false; true] [EVar 13; EVar 12] [].
Definition rHo := Eval vm_compute in runAM scrHo (SS 0x177adc srH0 [] knH 46).
Definition srHo : list expr := Eval vm_compute in s_regs (fst (fst rHo)).

Definition scrHk : scripts := SCR [false; false] [EVar 13; EVar 12; EVar 9; EVar 8; EVar 10; EVar 11] [].
Definition rHk := Eval vm_compute in runAM scrHk (SS 0x177adc srH0 [] knH 46).
Definition srHk : list expr := Eval vm_compute in s_regs (fst (fst rHk)).

Definition srI0 : list expr :=
  [ELit 0; EVar 15; spx (-128); EVar 17; ELit 0x6c5858; EVar 19; EVar 20; EVar 21; EVar 22; EVar 3; EVar 24; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31; EVar 32; EVar 33; EVar 34; EVar 35; EVar 36; EVar 37; EVar 38; EVar 39; EVar 40; EVar 41; EVar 42; EVar 43; EVar 44; EVar 45]%Z.
Definition rI := Eval vm_compute in runAM noscr (SS 0xe85e8 srI0 [] aknL 46).
Definition srI : list expr := Eval vm_compute in s_regs (fst (fst rI)).

Definition srX0 : list expr :=
  [ELit 0; EVar 15; spx (-128); EVar 17; ELit 0x6c5858; EVar 19; EVar 20; EVar 21; EVar 22; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31; EVar 32; EVar 33; EVar 34; EVar 35; EVar 36; EVar 37; EVar 38; EVar 39; EVar 40; EVar 41; EVar 42; EVar 43; EVar 44; EVar 45]%Z.
Definition knX : list kentry :=
  ([KWord (SA (EVar 0) (-56)) 8 (ELit 0x164cb0);
    KWord (SA (EVar 0) (-120)) 8 (EVar 6); KWord (SA (EVar 0) (-112)) 8 (EVar 7); KWord (SA (EVar 0) (-104)) 8 (EVar 8);
    KWord (SA (EVar 0) (-96)) 8 (EVar 9); KWord (SA (EVar 0) (-88)) 8 (EVar 10); KWord (SA (EVar 0) (-80)) 8 (EVar 11);
    KWord (SA (EVar 0) (-72)) 8 (EVar 12); KWord (SA (EVar 0) (-64)) 8 (EVar 13)]%Z) ++ aknL.
Definition rX := Eval vm_compute in runAM noscr (SS 0xe85f0 srX0 [] knX 46).
Definition srX : list expr := Eval vm_compute in s_regs (fst (fst rX)).

Definition asummary (r : sym_state * list sidecond * scripts) := (s_pc (fst (fst r)), snd (fst r), snd r).
