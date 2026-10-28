(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OssFuzzTheorems.openssl.echconfiglist_parser.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib Require Import Amb
  PropExec SymExec2 SymExec2Sound SymRun SymDrive SymDriveX MainWalk_defs.
Import ListNotations.
Import OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.PropExec.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import SX2. Import SX2S.

Abbreviation RSEGS := AsanUbsan.M.loaded_segments.

Definition STOPST : list Z := [0x1bf174; 0x1bf170; 0x1bdaac; 0x1ef1d0; 0x1ef184; 0x1eee98; 0x1ef040; 0x1ef054; 0x1ef0b4; 0x1ef0f4]%Z.
Definition runT (stops : list Z) (scr : scripts) (ss : sym_state) := sym_exec RSEGS FUELM true stops scr ss [].

(* [comment removed for export] *)
Definition knT : list kentry :=
  [KAlign (EVar 0) 16; KRange (EVar 0) 0x7fff7f811000 0x7fffffffff80;
   KWr (SA (EVar 0) (-128)) 128;
   KWr (SA (ELit 0) 0xbdcf50) 16; KWr (SA (ELit 0) 0xc01ce0) 0x130;
   KImg 0x10000 0x195000; KImg 0x571000 0x5ea000]%Z.
(* [comment removed for export] *)
Definition atexit_pre_cells : list (Z * nat * Z) :=
  [(0xc01f23, 1%nat, 0); (0xc01ce0, 1%nat, 0); (0xc01ce4, 4%nat, 0); (0xc01ce8, 4%nat, 1); (0xc01cf0, 8%nat, 0xc01cf8); (0xc01cf8, 8%nat, 0)]%Z.
Definition knT0 : list kentry := Eval cbv in (knT ++ map (fun c : Z * nat * Z => match c with (a, w, v) => KWord (SA (ELit 0) a) w (ELit v) end) atexit_pre_cells).   (* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition knT8 : list kentry :=
  [KWord (SA (EVar 0) (-8)) 8 (ELit 0x1eee98); KWord (SA (EVar 0) (-16)) 8 (EVar 1); KWord (SA (EVar 0) (-24)) 8 (EVar 2);
   KWord (SA (EVar 0) (-32)) 8 (EVar 5); KWord (SA (EVar 0) (-40)) 8 (EVar 6); KWord (SA (EVar 0) (-48)) 8 (EVar 8);
   KWord (SA (EVar 0) (-56)) 8 (EVar 9); KWord (SA (EVar 0) (-64)) 8 (EVar 12); KWord (SA (EVar 0) (-72)) 8 (EVar 13)]%Z ++ knT.

(* [comment removed for export] *)
Definition srT00 : list expr :=
  [ELit 0; ELit 0x1eee98; EVar 0; EVar 17; ELit 0xbe1c90; EVar 19; EVar 20; EVar 21; EVar 22; EVar 23; EVar 9; EVar 2; EVar 8; EVar 3; EVar 28; EVar 29; EVar 30; EVar 31; EVar 32; EVar 33; EVar 34; EVar 35; EVar 36; EVar 37; EVar 38; EVar 39; EVar 40; EVar 41; EVar 42; EVar 43; EVar 44; EVar 45]%Z.
Definition scrT0a : scripts := SCR [false] [EVar 5] [].     (* [comment removed for export] *)
Definition scrT0b : scripts := SCR [true] [EVar 5] [].      (* [comment removed for export] *)
Definition rT0a := Eval vm_compute in runT STOPST scrT0a (SS 0x1eeff8 srT00 [] knT0 46).
Definition rT0b := Eval vm_compute in runT STOPST scrT0b (SS 0x1eeff8 srT00 [] knT0 46).
Definition srT0a : list expr := Eval vm_compute in s_regs (fst (fst rT0a)).
Definition srT0b : list expr := Eval vm_compute in s_regs (fst (fst rT0b)).
(* [comment removed for export] *)
Definition srT10 : list expr :=
  [ELit 0; EVar 15; spx (-80); EVar 17; ELit 0xbe1c90; EVar 19; EVar 20; EVar 21; EVar 3; EVar 8; EVar 24; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31; EVar 2; EVar 9; ELit 0xbdcf50; EVar 35; EVar 36; EVar 37; EVar 38; EVar 39; EVar 40; EVar 41; EVar 42; EVar 43; EVar 44; EVar 45]%Z.
Definition scrT1a : scripts := SCR [false; false] [EVar 6] [].   (* [comment removed for export] *)
Definition scrT1b : scripts := SCR [false; true] [EVar 6] [].    (* [comment removed for export] *)
Definition scrT1c : scripts := SCR [true; true] [] [].            (* [comment removed for export] *)
Definition scrT1d : scripts := SCR [true; false] [] [].           (* [comment removed for export] *)
Definition rT1a := Eval vm_compute in runT STOPST scrT1a (SS 0x1ef040 srT10 [] knT 46).
Definition rT1b := Eval vm_compute in runT STOPST scrT1b (SS 0x1ef040 srT10 [] knT 46).
Definition rT1c := Eval vm_compute in runT STOPST scrT1c (SS 0x1ef040 srT10 [] knT 46).
Definition rT1d := Eval vm_compute in runT STOPST scrT1d (SS 0x1ef040 srT10 [] knT 46).
Definition srT1a : list expr := Eval vm_compute in s_regs (fst (fst rT1a)).
Definition srT1b : list expr := Eval vm_compute in s_regs (fst (fst rT1b)).
Definition srT1c : list expr := Eval vm_compute in s_regs (fst (fst rT1c)).
Definition srT1d : list expr := Eval vm_compute in s_regs (fst (fst rT1d)).
(* [comment removed for export] *)
Definition srT20 : list expr :=
  [ELit 0; EVar 15; spx (-80); EVar 17; ELit 0xbe1c90; EVar 19; EVar 20; EVar 21; EVar 3; EVar 8; EVar 24; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31; EVar 2; EVar 9; ELit 0xbdcf50; EVar 7; EVar 36; EVar 37; EVar 38; EVar 39; EVar 40; EVar 41; EVar 42; EVar 43; EVar 44; EVar 45]%Z.
Definition rT2 := Eval vm_compute in runT STOPST noscr (SS 0x1ef054 srT20 [] knT 46).
Definition srT2 : list expr := Eval vm_compute in s_regs (fst (fst rT2)).
(* [comment removed for export] *)
Definition srT30 : list expr :=
  [ELit 0; EVar 15; spx (-80); EVar 17; ELit 0xbe1c90; EVar 19; EVar 20; EVar 21; EVar 3; EVar 8; EVar 4; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31; EVar 2; EVar 9; ELit 0xbdcf50; EVar 7; EVar 36; EVar 37; EVar 38; EVar 39; EVar 40; EVar 41; EVar 42; EVar 43; EVar 44; EVar 45]%Z.
Definition scrT3 : scripts := SCR [false] [] [].   (* [comment removed for export] *)
Definition rT3 := Eval vm_compute in runT STOPST scrT3 (SS 0x1ef05c srT30 [] knT 46).
Definition srT3 : list expr := Eval vm_compute in s_regs (fst (fst rT3)).
(* [comment removed for export] *)
Definition srT40 : list expr :=
  [ELit 0; EVar 15; spx (-80); EVar 17; ELit 0xbe1c90; EVar 19; EVar 20; EVar 21; EVar 3; EVar 8; EVar 24; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31; EVar 4; EVar 9; ELit 0xbdcf50; EVar 7; EVar 36; EVar 37; EVar 38; EVar 39; EVar 40; EVar 41; EVar 42; EVar 43; EVar 44; EVar 45]%Z.
Definition rT4 := Eval vm_compute in runT STOPST noscr (SS 0x1ef070 srT40 [] knT 46).
Definition srT4 : list expr := Eval vm_compute in s_regs (fst (fst rT4)).
(* [comment removed for export] *)
Definition srT50 : list expr :=
  [ELit 0; EVar 15; spx (-80); EVar 17; ELit 0xbe1c90; EVar 19; EVar 20; EVar 21; EVar 3; EVar 4; EVar 24; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31; EVar 10; EVar 11; ELit 0xbdcf50; EVar 7; ELit 0; ELit 18446744073709551614; EVar 38; EVar 39; EVar 40; EVar 41; EVar 42; EVar 43; EVar 44; EVar 45]%Z.
Definition rT5 := Eval vm_compute in runT STOPST noscr (SS 0x1ef0b4 srT50 [] knT 46).
Definition srT5 : list expr := Eval vm_compute in s_regs (fst (fst rT5)).
(* [comment removed for export] *)
Definition srT60 : list expr :=
  [ELit 0; EVar 15; spx (-80); EVar 17; ELit 0xbe1c90; EVar 19; EVar 20; EVar 21; EVar 3; EVar 4; ELit 0; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31; EVar 10; EVar 33; ELit 0xbdcf50; EVar 7; ELit 0; ELit 18446744073709551614; EVar 38; EVar 39; EVar 40; EVar 41; EVar 42; EVar 43; EVar 44; EVar 45]%Z.
Definition rT6 := Eval vm_compute in runT STOPST noscr (SS 0x1ef0c8 srT60 [] knT 46).
Definition srT6 : list expr := Eval vm_compute in s_regs (fst (fst rT6)).
(* [comment removed for export] *)
Definition srT70 : list expr :=
  [ELit 0; EVar 15; spx (-80); EVar 17; ELit 0xbe1c90; EVar 19; EVar 20; EVar 21; EVar 3; EVar 4; EVar 24; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31; EVar 10; ELit 0; ELit 0xbdcf50; EVar 7; ELit 0; ELit 18446744073709551614; EVar 38; EVar 39; EVar 40; EVar 41; EVar 42; EVar 43; EVar 44; EVar 45]%Z.
Definition scrT7a : scripts := SCR [true] [] [].    (* [comment removed for export] *)
Definition scrT7b : scripts := SCR [false] [] [].   (* [comment removed for export] *)
Definition rT7a := Eval vm_compute in runT STOPST scrT7a (SS 0x1ef0d8 srT70 [] knT 46).
Definition rT7b := Eval vm_compute in runT STOPST scrT7b (SS 0x1ef0d8 srT70 [] knT 46).
Definition srT7a : list expr := Eval vm_compute in s_regs (fst (fst rT7a)).
Definition srT7b : list expr := Eval vm_compute in s_regs (fst (fst rT7b)).
(* [comment removed for export] *)
Definition srT80 : list expr :=
  [ELit 0; EVar 15; spx (-80); EVar 17; ELit 0xbe1c90; EVar 19; EVar 20; EVar 21; EVar 3; EVar 4; EVar 24; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31; EVar 10; EVar 33; ELit 0xbdcf50; EVar 35; ELit 0; ELit 18446744073709551614; EVar 38; EVar 39; EVar 40; EVar 41; EVar 42; EVar 43; EVar 44; EVar 45]%Z.
Definition rT8 := Eval vm_compute in runT STOPST noscr (SS 0x1ef0f4 srT80 [] knT8 46).
Definition srT8 : list expr := Eval vm_compute in s_regs (fst (fst rT8)).

(* [comment removed for export] *)
Definition summaryT (r : sym_state * list sidecond * scripts) := (s_pc (fst (fst r)), snd (fst r), snd r).
