(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.boost_beast.http_request.images Require Import Asan.
From OSSVerify.Proofs.boost_beast.http_request.lib Require Import Amb
  PropExec SymExec2 SymExec2Sound SymRun SymDrive SymDriveX MainWalk_defs.
Import ListNotations.
Import OSSVerify.Proofs.boost_beast.http_request.lib.PropExec.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import SX2. Import SX2S.

Abbreviation RSEGS := Asan.M.loaded_segments.

(* [comment removed for export] *)
Definition STOPST : list Z := [0x73278; 0x73274; 0x716f0; 0xff194; 0xa3808; 0xa3128; 0xa2e44; 0xa2fe8; 0xa2ffc; 0xa3058; 0xa3098]%Z.
Definition runT (stops : list Z) (scr : scripts) (ss : sym_state) := sym_exec RSEGS FUELM true stops scr ss [].

(* [comment removed for export] *)
Definition knT : list kentry :=
  [KAlign (EVar 0) 16; KRange (EVar 0) 0x7fff7f811000 0x7fffffffff80;
   KWr (SA (EVar 0) (-80)) 80;
   KWr (SA (ELit 0) 0x65bad0) 16;
   KImg 0x10000 0x4d000; KImg 0x115000 0x11d000]%Z.
(* [comment removed for export] *)
Definition knT8 : list kentry :=
  [KWord (SA (EVar 0) (-8)) 8 (ELit 0xa2e44); KWord (SA (EVar 0) (-16)) 8 (EVar 1); KWord (SA (EVar 0) (-24)) 8 (EVar 2);
   KWord (SA (EVar 0) (-32)) 8 (EVar 3); KWord (SA (EVar 0) (-40)) 8 (EVar 5); KWord (SA (EVar 0) (-48)) 8 (EVar 6);
   KWord (SA (EVar 0) (-56)) 8 (EVar 8); KWord (SA (EVar 0) (-64)) 8 (EVar 10); KWord (SA (EVar 0) (-72)) 8 (EVar 11)]%Z ++ knT.

Definition srT00 : list expr :=
  [ELit 0; ELit 0xa2e44; EVar 0; EVar 17; ELit 0x65d4b0; EVar 19; EVar 20; EVar 21; EVar 22; EVar 23; EVar 1; EVar 2; EVar 8; EVar 3; EVar 28; EVar 29; EVar 30; EVar 31; EVar 32; EVar 33; EVar 34; EVar 35; EVar 36; EVar 37; EVar 38; EVar 39; EVar 40; EVar 41; EVar 42; EVar 43; EVar 44; EVar 45]%Z.
Definition srTA0 : list expr :=
  [ELit 0; EVar 15; spx (-80); EVar 17; ELit 0x65d4b0; EVar 19; EVar 20; EVar 21; EVar 3; EVar 8; ELit 0; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31; EVar 2; EVar 1; ELit 0x65bad0; EVar 35; EVar 36; EVar 37; EVar 38; EVar 39; EVar 40; EVar 41; EVar 42; EVar 43; EVar 44; EVar 45]%Z.
Definition srT10 : list expr :=
  [ELit 0; EVar 15; spx (-80); EVar 17; ELit 0x65d4b0; EVar 19; EVar 20; EVar 21; EVar 3; EVar 8; EVar 24; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31; EVar 2; EVar 1; ELit 0x65bad0; EVar 35; EVar 36; EVar 37; EVar 38; EVar 39; EVar 40; EVar 41; EVar 42; EVar 43; EVar 44; EVar 45]%Z.
Definition srT20 : list expr :=
  [ELit 0; EVar 15; spx (-80); EVar 17; ELit 0x65d4b0; EVar 19; EVar 20; EVar 21; EVar 3; EVar 8; EVar 24; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31; EVar 2; EVar 1; ELit 0x65bad0; EVar 7; EVar 36; EVar 37; EVar 38; EVar 39; EVar 40; EVar 41; EVar 42; EVar 43; EVar 44; EVar 45]%Z.
Definition srT30 : list expr :=
  [ELit 0; EVar 15; spx (-80); EVar 17; ELit 0x65d4b0; EVar 19; EVar 20; EVar 21; EVar 3; EVar 8; EVar 4; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31; EVar 2; EVar 1; ELit 0x65bad0; EVar 7; EVar 36; EVar 37; EVar 38; EVar 39; EVar 40; EVar 41; EVar 42; EVar 43; EVar 44; EVar 45]%Z.
Definition srT40 : list expr :=
  [ELit 0; EVar 15; spx (-80); EVar 17; ELit 0x65d4b0; EVar 19; EVar 20; EVar 21; EVar 3; EVar 8; EVar 24; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31; EVar 4; EVar 1; ELit 0x65bad0; EVar 7; EVar 36; EVar 37; EVar 38; EVar 39; EVar 40; EVar 41; EVar 42; EVar 43; EVar 44; EVar 45]%Z.
Definition srT50 : list expr :=
  [ELit 0; EVar 15; spx (-80); EVar 17; ELit 0x65d4b0; EVar 19; EVar 20; EVar 21; EVar 3; EVar 4; EVar 24; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31; EVar 10; EVar 11; ELit 0x65bad0; EVar 7; ELit 0; ELit 18446744073709551614; EVar 38; EVar 39; EVar 40; EVar 41; EVar 42; EVar 43; EVar 44; EVar 45]%Z.
Definition srT60 : list expr :=
  [ELit 0; EVar 15; spx (-80); EVar 17; ELit 0x65d4b0; EVar 19; EVar 20; EVar 21; EVar 3; EVar 4; ELit 0; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31; EVar 10; EVar 33; ELit 0x65bad0; EVar 7; ELit 0; ELit 18446744073709551614; EVar 38; EVar 39; EVar 40; EVar 41; EVar 42; EVar 43; EVar 44; EVar 45]%Z.
Definition srT70 : list expr :=
  [ELit 0; EVar 15; spx (-80); EVar 17; ELit 0x65d4b0; EVar 19; EVar 20; EVar 21; EVar 3; EVar 4; EVar 24; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31; EVar 10; ELit 0; ELit 0x65bad0; EVar 7; ELit 0; ELit 18446744073709551614; EVar 38; EVar 39; EVar 40; EVar 41; EVar 42; EVar 43; EVar 44; EVar 45]%Z.
Definition srT7z0 : list expr :=
  [ELit 0; EVar 15; spx (-80); EVar 17; ELit 0x65d4b0; EVar 19; EVar 20; EVar 21; EVar 3; EVar 4; EVar 24; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31; ELit 0; ELit 0; ELit 0x65bad0; EVar 7; ELit 0; ELit 18446744073709551614; EVar 38; EVar 39; EVar 40; EVar 41; EVar 42; EVar 43; EVar 44; EVar 45]%Z.
Definition srT80 : list expr :=
  [ELit 0; EVar 15; spx (-80); EVar 17; ELit 0x65d4b0; EVar 19; EVar 20; EVar 21; EVar 22; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31; EVar 32; EVar 33; ELit 0x65bad0; EVar 35; ELit 0; ELit 18446744073709551614; EVar 38; EVar 39; EVar 40; EVar 41; EVar 42; EVar 43; EVar 44; EVar 45]%Z.

(* [comment removed for export] *)
Definition scrT0a : scripts := SCR [false] [EVar 5] [].     (* [comment removed for export] *)
Definition scrT0b : scripts := SCR [true] [EVar 5] [].      (* [comment removed for export] *)
Definition rT0a := Eval vm_compute in runT STOPST scrT0a (SS 0xa2fa0 srT00 [] knT 46).
Definition rT0b := Eval vm_compute in runT STOPST scrT0b (SS 0xa2fa0 srT00 [] knT 46).
Definition srT0a : list expr := Eval vm_compute in s_regs (fst (fst rT0a)).
Definition srT0b : list expr := Eval vm_compute in s_regs (fst (fst rT0b)).
(* [comment removed for export] *)
Definition rTA := Eval vm_compute in runT STOPST noscr (SS 0xa3034 srTA0 [] knT 46).
Definition srTA : list expr := Eval vm_compute in s_regs (fst (fst rTA)).
(* [comment removed for export] *)
Definition scrT1a : scripts := SCR [false; false] [EVar 6] [].   (* [comment removed for export] *)
Definition scrT1b : scripts := SCR [false; true] [EVar 6] [].    (* [comment removed for export] *)
Definition scrT1c : scripts := SCR [true; true] [] [].            (* [comment removed for export] *)
Definition scrT1d : scripts := SCR [true; false] [] [].           (* [comment removed for export] *)
Definition rT1a := Eval vm_compute in runT STOPST scrT1a (SS 0xa2fe8 srT10 [] knT 46).
Definition rT1b := Eval vm_compute in runT STOPST scrT1b (SS 0xa2fe8 srT10 [] knT 46).
Definition rT1c := Eval vm_compute in runT STOPST scrT1c (SS 0xa2fe8 srT10 [] knT 46).
Definition rT1d := Eval vm_compute in runT STOPST scrT1d (SS 0xa2fe8 srT10 [] knT 46).
Definition srT1a : list expr := Eval vm_compute in s_regs (fst (fst rT1a)).
Definition srT1b : list expr := Eval vm_compute in s_regs (fst (fst rT1b)).
Definition srT1c : list expr := Eval vm_compute in s_regs (fst (fst rT1c)).
Definition srT1d : list expr := Eval vm_compute in s_regs (fst (fst rT1d)).
(* [comment removed for export] *)
Definition rT2 := Eval vm_compute in runT STOPST noscr (SS 0xa2ffc srT20 [] knT 46).
Definition srT2 : list expr := Eval vm_compute in s_regs (fst (fst rT2)).
(* [comment removed for export] *)
Definition scrT3 : scripts := SCR [false] [] [].   (* [comment removed for export] *)
Definition rT3 := Eval vm_compute in runT STOPST scrT3 (SS 0xa3004 srT30 [] knT 46).
Definition srT3 : list expr := Eval vm_compute in s_regs (fst (fst rT3)).
(* [comment removed for export] *)
Definition rT4 := Eval vm_compute in runT STOPST noscr (SS 0xa3018 srT40 [] knT 46).
Definition srT4 : list expr := Eval vm_compute in s_regs (fst (fst rT4)).
(* [comment removed for export] *)
Definition rT5 := Eval vm_compute in runT STOPST noscr (SS 0xa3058 srT50 [] knT 46).
Definition srT5 : list expr := Eval vm_compute in s_regs (fst (fst rT5)).
(* [comment removed for export] *)
Definition rT6 := Eval vm_compute in runT STOPST noscr (SS 0xa306c srT60 [] knT 46).
Definition srT6 : list expr := Eval vm_compute in s_regs (fst (fst rT6)).
(* [comment removed for export] *)
Definition scrT7a : scripts := SCR [true] [] [].    (* [comment removed for export] *)
Definition scrT7b : scripts := SCR [false] [] [].   (* [comment removed for export] *)
Definition rT7a := Eval vm_compute in runT STOPST scrT7a (SS 0xa307c srT70 [] knT 46).
Definition rT7b := Eval vm_compute in runT STOPST scrT7b (SS 0xa307c srT70 [] knT 46).
Definition srT7a : list expr := Eval vm_compute in s_regs (fst (fst rT7a)).
Definition srT7b : list expr := Eval vm_compute in s_regs (fst (fst rT7b)).
(* [comment removed for export] *)
Definition rT7z := Eval vm_compute in runT STOPST scrT7b (SS 0xa307c srT7z0 [] knT 46).
Definition srT7z : list expr := Eval vm_compute in s_regs (fst (fst rT7z)).
(* [comment removed for export] *)
Definition rT8 := Eval vm_compute in runT STOPST noscr (SS 0xa3098 srT80 [] knT8 46).
Definition srT8 : list expr := Eval vm_compute in s_regs (fst (fst rT8)).

(* [comment removed for export] *)
Definition summaryT (r : sym_state * list sidecond * scripts) := (s_pc (fst (fst r)), snd (fst r), snd r).
