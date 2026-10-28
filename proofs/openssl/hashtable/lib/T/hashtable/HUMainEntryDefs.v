(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.openssl.hashtable.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import
  PropExec CatExec ArgvEnv SymExec SymExec2 SymExec2Sound SymRun SymDrive RefLayout HUStartupDefs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import ConeCfg.   (* [comment removed for export] *)
Import ListNotations.
Import ConeCfg.
Open Scope bv_scope.
Import SX2. Import SX2S.
Import ConeCfg.

Abbreviation RSEGS := Ubsan.M.loaded_segments.
Abbreviation RPH := Ubsan.M.phdrs.

Section MainEntry.
  Variable sp0 : word.
  Variables a0s path : list byte.
  Variable ev : list (list byte).
  Variable uid : word.        (* [comment removed for export] *)
  Variable hw : word.         (* [comment removed for export] *)
  Variable rdraw : EntryDraw. (* [comment removed for export] *)
  Variable tid : word.
  Variable regs : bvmap 5 word.   (* [comment removed for export] *)
  Let av := [a0s; path].

  Definition p0 : word := cat_argv_ptr sp0 av ev 0.
  Definition p1 : word := cat_argv_ptr sp0 av ev 1.
  Definition auxvp : word := auxv_w sp0 av ev.
  Definition rnd : word := at_random_ptr sp0 av ev.

  (* [comment removed for export] *)
  Definition guard8 : list byte := canary8 rdraw.      (* [comment removed for export] *)
  Definition rndw0 : word := le_bytes_to_word (firstn 8 (rnd16 rdraw)).
  Definition rndw1 : word := le_bytes_to_word (skipn 8 (rnd16 rdraw)).
  Definition can : word := le_bytes_to_word guard8.

  (* [comment removed for export] *)
  Definition vals0 : list word := [sp0; p0; p1; auxvp; rnd; tid] ++ junk_vals regs.
  Definition blobs0 : list (list byte) := [a0s ++ [Z_to_bv 8 0]; path ++ [Z_to_bv 8 0]; rnd16 rdraw; guard8].
  Definition E0 : env := Env (vals_ev vals0) (blobs_ev blobs0).

  Definition spx (k : Z) : expr := EAlu ALU_ADD (EVar 0) (ELit k).

  (* [comment removed for export] *)
  Definition sr_main : list expr :=
    [ELit 0; ELit 0x2b1158; spx (-48); ELit 0x10800; ELit 0x331ae8; EVar 11; EVar 12; EVar 13;
     spx 8; ELit 2; ELit 2; spx 8; spx 32; EVar 19; EVar 20; EVar 21;
     EVar 22; EVar 23; ELit 0xe1984; spx 32; ELit 0; ELit 0; ELit 0; ELit 0;
     ELit 0; ELit 0; ELit 0; ELit 0; EVar 34; EVar 35; EVar 36; EVar 37].

  Definition kn_stack : list kentry :=
    [KAlign (EVar 0) 16; KRange (EVar 0) 0x7fff80000000 0x800000000000;
     KWr (SA (EVar 0) (-8388608)) 8388608;
     KWord (SA (EVar 0) 0) 8 (ELit 2); KWord (SA (EVar 0) 8) 8 (EVar 1);
     KWord (SA (EVar 0) 16) 8 (EVar 2); KWord (SA (EVar 0) 24) 8 (ELit 0)].

  (* [comment removed for export] *)
  Definition kn_auxv : list kentry :=
    [KRange (EVar 3) 0x7fff80000000 0x800000000000; KRange (EVar 4) 0x7fff80000000 0x800000000000;
     KDisj (SA (EVar 0) (-8388608)) 8388608 (SA (EVar 3) 0) 160;
     KDisj (SA (EVar 0) (-8388608)) 8388608 (SA (EVar 4) 0) 16;
     KAlign (EVar 3) 8; KAlign (EVar 4) 8;
     KWord (SA (EVar 3) 0) 8 (ELit 3); KWord (SA (EVar 3) 8) 8 (ELit 0x10040);
     KWord (SA (EVar 3) 16) 8 (ELit 4); KWord (SA (EVar 3) 24) 8 (ELit 56);
     KWord (SA (EVar 3) 32) 8 (ELit 5); KWord (SA (EVar 3) 40) 8 (ELit 10);
     KWord (SA (EVar 3) 48) 8 (ELit 16);                                       (* [comment removed for export] *)
     KWord (SA (EVar 3) 64) 8 (ELit 6); KWord (SA (EVar 3) 72) 8 (ELit 4096);
     KWord (SA (EVar 3) 80) 8 (ELit 11);                                       (* [comment removed for export] *)
     KWord (SA (EVar 3) 96) 8 (ELit 12);                                       (* [comment removed for export] *)
     KWord (SA (EVar 3) 112) 8 (ELit 23); KWord (SA (EVar 3) 120) 8 (ELit 0);
     KWord (SA (EVar 3) 128) 8 (ELit 25); KWord (SA (EVar 3) 136) 8 (EVar 4);
     KWord (SA (EVar 3) 144) 8 (ELit 0); KWord (SA (EVar 3) 152) 8 (ELit 0);
     KBlob (SA (EVar 4) 0) (ELit 16) 2].

  (* [comment removed for export] *)
  Definition kn_image : list kentry :=
    [KWr (SA (ELit 0) 0x31e000) 0x36000;
     KImg 0x0 0x1000; KImg 0x10000 0x31eec0; KImg 0x31eec1 0x331a18; KImg 0x351af0 0x351b10; KImg 0x331a4c 0x331a98; KImg 0x331aa0 0x331ab8; KImg 0x331ac0 0x331ad8; KImg 0x331ae8 0x331af8; KImg 0x331b00 0x351af0; KImg 0x351b30 0x351d68; KImg 0x351d79 0x351d80; KImg 0x351d88 0x351d90; KImg 0x351da0 0x351da8; KImg 0x351db0 0x351de0; KImg 0x351de8 0x354000;
     
     
     KWord (SA (ELit 0) 0x351b10) 8 (ELit 0);          (* [comment removed for export] *)
     KWord (SA (ELit 0) 0x351b18) 8 (ELit 8);          (* [comment removed for export] *)
     KWord (SA (ELit 0) 0x351b20) 8 (ELit 0);          (* [comment removed for export] *)
     KWord (SA (ELit 0) 0x331a20) 8 (ELit 0x331a20);    (* [comment removed for export] *)
     KWord (SA (ELit 0) 0x331a28) 8 (ELit 0x331a20);    (* [comment removed for export] *)
     KWord (SA (ELit 0) 0x331a30) 8 (ELit 0x331a20);    (* [comment removed for export] *)
     KWord (SA (ELit 0) 0x331a38) 8 (ELit 0);          (* [comment removed for export] *)
     KWord (SA (ELit 0) 0x331a40) 4 (EVar 5);          (* [comment removed for export] *)
     KWord (SA (ELit 0) 0x331a48) 4 (ELit 2);          (* [comment removed for export] *)
     
     KWord (SA (ELit 0) 0x331a98) 8 (ELit 0x331a98);    (* [comment removed for export] *)
     
     KWord (SA (ELit 0) 0x331ab8) 8 (ELit 0x351db0);    (* [comment removed for export] *)
     
     KBlob (SA (ELit 0) 0x331ad8) (ELit 8) 3;         (* [comment removed for export] *)
     KWord (SA (ELit 0) 0x331ae0) 8 (ELit 0x331af8);    (* [comment removed for export] *)
     
     KWord (SA (ELit 0) 0x331af8) 8 (ELit 0);          (* [comment removed for export] *)
     
     KBlob (SA (ELit 0) 0x351b28) (ELit 8) 3;         (* [comment removed for export] *)
     
      KWord (SA (ELit 0) 0x351d80) 8 (EVar 3);   (* [comment removed for export] *)
     
     KWord (SA (ELit 0) 0x351d90) 8 (ELit 0xe0);       (* [comment removed for export] *)
     KWord (SA (ELit 0) 0x351d98) 8 (ELit 8);          (* [comment removed for export] *)
      KWord (SA (ELit 0) 0x351da8) 8 (ELit 4096); (* [comment removed for export] *)
      
     KWord (SA (ELit 0) 0x351d78) 1 (ELit 1);          (* [comment removed for export] *)
     KRange (EVar 5) 1 4194303
     (* [comment removed for export] *)].

  (* [comment removed for export] *)
  Definition kn_main : list kentry := kn_stack ++ kn_auxv ++ kn_image.
End MainEntry.
