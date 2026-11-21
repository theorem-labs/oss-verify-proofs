(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (the entry facts take the process input: argv's strings at the top of the launch block, AT_RANDOM's place by the rseq flag, the mapped window under the stack pointer from [wok_lo] (MemSplit), the first 26 auxv pairs of the new layout, and [kn_tail], the pairs CONFIG_RSEQ decides). *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.openssl.hashtable.images Require Import Plain.
From OSSVerify.Proofs.openssl.hashtable.lib Require Import
  PropExec CatExec ArgvEnv SymExec SymExec2 SymExec2Sound SymRun SymDrive RefLayout H0StartupDefs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OSSVerify.Proofs.openssl.hashtable.lib Require Import ConeCfg.   (* [comment removed for export] *)
Import ListNotations.
Import ConeCfg.
Open Scope bv_scope.
Import SX2. Import SX2S.
Import ConeCfg.

Abbreviation RSEGS := Plain.M.loaded_segments.
Abbreviation RPH := Plain.M.phdrs.

Section MainEntry.
  Variable sp0 : word.
  Variables a0s path : list byte.
  Variable ev : list (list byte).
  Variable uid : word.        (* [comment removed for export] *)
  Variable hw : word.         (* [comment removed for export] *)
  Variable rdraw : EntryDraw. (* [comment removed for export] *)
  Variable tid : word.
  Variable regs : bvmap 5 word.   (* [comment removed for export] *)
  Variable inp : ProcInput.
  Let av := [a0s; path].

  (* 08b1429: the strings sit at the top of the block ([cat_argv_ptr] over the stack top and the exec file
     name), and AT_RANDOM's place depends on the input's rseq flag *)
  Definition p0 : word := cat_argv_ptr (ed_top rdraw) av ev (in_execfn inp) 0.
  Definition p1 : word := cat_argv_ptr (ed_top rdraw) av ev (in_execfn inp) 1.
  Definition auxvp : word := Z_to_bv 64 (bv_unsigned sp0 + 24 + 8 * Z.of_nat (length av) + 8 * Z.of_nat (length ev)).
  Definition rnd : word := at_random_ptr sp0 (kb_rseq (in_kernel inp)) av ev.

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
    [ELit 0; ELit 0x26b5b0; spx (-48); ELit 0x10800; ELit 0x2ebf58; EVar 11; EVar 12; EVar 13;
     spx 8; ELit 2; ELit 2; spx 8; spx 32; EVar 19; EVar 20; EVar 21;
     EVar 22; EVar 23; ELit 0xdd09c; spx 32; ELit 0; ELit 0; ELit 0; ELit 0;
     ELit 0; ELit 0; ELit 0; ELit 0; EVar 34; EVar 35; EVar 36; EVar 37].

  Definition kn_stack : list kentry :=
    [KAlign (EVar 0) 16; KRange (EVar 0) 0x7fff80000000 0x800000000000;
     (* 08b1429: the mapped window under sp is [wok_lo sp0, sp0) (MemSplit), 6144513 bytes *)
     KWr (SA (EVar 0) (-6144513)) 6144513;
     KWord (SA (EVar 0) 0) 8 (ELit 2); KWord (SA (EVar 0) 8) 8 (EVar 1);
     KWord (SA (EVar 0) 16) 8 (EVar 2); KWord (SA (EVar 0) 24) 8 (ELit 0)].

  (* [comment removed for export] *)
  Definition kn_auxv : list kentry :=
    [KRange (EVar 3) 0x7fff80000000 0x800000000000; KRange (EVar 4) 0x7fff80000000 0x800000000000;
     KDisj (SA (EVar 0) (-8388608)) 8388608 (SA (EVar 3) 0) 416;
     KDisj (SA (EVar 0) (-8388608)) 8388608 (SA (EVar 4) 0) 16;
     KAlign (EVar 3) 8; KAlign (EVar 4) 8;
     (* LPS 727298f3: the first 26 pairs of [StackLayout.auxv_entries], the ones before the CONFIG_RSEQ
        branch: every key, and each value that is the same in every launch (AT_RANDOM's is [rnd]) *)
     KWord (SA (EVar 3) 0) 8 (ELit 33);
     KWord (SA (EVar 3) 16) 8 (ELit 40);
     KWord (SA (EVar 3) 32) 8 (ELit 41);
     KWord (SA (EVar 3) 48) 8 (ELit 42);
     KWord (SA (EVar 3) 64) 8 (ELit 43);
     KWord (SA (EVar 3) 80) 8 (ELit 44);
     KWord (SA (EVar 3) 96) 8 (ELit 45);
     KWord (SA (EVar 3) 112) 8 (ELit 46);
     KWord (SA (EVar 3) 128) 8 (ELit 47);
     KWord (SA (EVar 3) 144) 8 (ELit 51);
     KWord (SA (EVar 3) 160) 8 (ELit 16);
     KWord (SA (EVar 3) 176) 8 (ELit 6); KWord (SA (EVar 3) 184) 8 (ELit 4096);
     KWord (SA (EVar 3) 192) 8 (ELit 17); KWord (SA (EVar 3) 200) 8 (ELit 100);
     KWord (SA (EVar 3) 208) 8 (ELit 3); KWord (SA (EVar 3) 216) 8 (ELit 0x10040);
     KWord (SA (EVar 3) 224) 8 (ELit 4); KWord (SA (EVar 3) 232) 8 (ELit 56);
     KWord (SA (EVar 3) 240) 8 (ELit 5); KWord (SA (EVar 3) 248) 8 (ELit 10);
     KWord (SA (EVar 3) 256) 8 (ELit 7); KWord (SA (EVar 3) 264) 8 (ELit 0);
     KWord (SA (EVar 3) 272) 8 (ELit 8); KWord (SA (EVar 3) 280) 8 (ELit 0);
     KWord (SA (EVar 3) 288) 8 (ELit 9);
     KWord (SA (EVar 3) 304) 8 (ELit 11);
     KWord (SA (EVar 3) 320) 8 (ELit 12);
     KWord (SA (EVar 3) 336) 8 (ELit 13);
     KWord (SA (EVar 3) 352) 8 (ELit 14);
     KWord (SA (EVar 3) 368) 8 (ELit 23); KWord (SA (EVar 3) 376) 8 (ELit 0);
     KWord (SA (EVar 3) 384) 8 (ELit 25); KWord (SA (EVar 3) 392) 8 (EVar 4);
     KWord (SA (EVar 3) 400) 8 (ELit 31);
     KBlob (SA (EVar 4) 0) (ELit 16) 2].

  (* [comment removed for export] *)
  Definition kn_image : list kentry :=
    [KWr (SA (ELit 0) 0x2d8000) 0x36000;
     KImg 0x0 0x1000; KImg 0x10000 0x2d9330; KImg 0x2d9331 0x2ebe88; KImg 0x30bf60 0x30bf80; KImg 0x2ebebc 0x2ebf08; KImg 0x2ebf10 0x2ebf28; KImg 0x2ebf30 0x2ebf48; KImg 0x2ebf58 0x2ebf68; KImg 0x2ebf70 0x30bf60; KImg 0x30bfa0 0x30c1d8; KImg 0x30c1e9 0x30c1f0; KImg 0x30c1f8 0x30c200; KImg 0x30c210 0x30c218; KImg 0x30c220 0x30c250; KImg 0x30c258 0x30e000;
     
     
     KWord (SA (ELit 0) 0x30bf80) 8 (ELit 0);          (* [comment removed for export] *)
     KWord (SA (ELit 0) 0x30bf88) 8 (ELit 8);          (* [comment removed for export] *)
     KWord (SA (ELit 0) 0x30bf90) 8 (ELit 0);          (* [comment removed for export] *)
     KWord (SA (ELit 0) 0x2ebe90) 8 (ELit 0x2ebe90);    (* [comment removed for export] *)
     KWord (SA (ELit 0) 0x2ebe98) 8 (ELit 0x2ebe90);    (* [comment removed for export] *)
     KWord (SA (ELit 0) 0x2ebea0) 8 (ELit 0x2ebe90);    (* [comment removed for export] *)
     KWord (SA (ELit 0) 0x2ebea8) 8 (ELit 0);          (* [comment removed for export] *)
     KWord (SA (ELit 0) 0x2ebeb0) 4 (EVar 5);          (* [comment removed for export] *)
     KWord (SA (ELit 0) 0x2ebeb8) 4 (ELit 2);          (* [comment removed for export] *)
     
     KWord (SA (ELit 0) 0x2ebf08) 8 (ELit 0x2ebf08);    (* [comment removed for export] *)
     
     KWord (SA (ELit 0) 0x2ebf28) 8 (ELit 0x30c220);    (* [comment removed for export] *)
     
     KBlob (SA (ELit 0) 0x2ebf48) (ELit 8) 3;         (* [comment removed for export] *)
     KWord (SA (ELit 0) 0x2ebf50) 8 (ELit 0x2ebf68);    (* [comment removed for export] *)
     
     KWord (SA (ELit 0) 0x2ebf68) 8 (ELit 0);          (* [comment removed for export] *)
     
     KBlob (SA (ELit 0) 0x30bf98) (ELit 8) 3;         (* [comment removed for export] *)
     
      KWord (SA (ELit 0) 0x30c1f0) 8 (EVar 3);   (* [comment removed for export] *)
     
     KWord (SA (ELit 0) 0x30c200) 8 (ELit 0xe0);       (* [comment removed for export] *)
     KWord (SA (ELit 0) 0x30c208) 8 (ELit 8);          (* [comment removed for export] *)
      KWord (SA (ELit 0) 0x30c218) 8 (ELit 4096); (* [comment removed for export] *)
      
     KWord (SA (ELit 0) 0x30c1e8) 1 (ELit 1);          (* [comment removed for export] *)
     KRange (EVar 5) 1 4194303
     (* [comment removed for export] *)].

  (* [comment removed for export] *)
  Definition kn_main : list kentry := kn_stack ++ kn_auxv ++ kn_image.

  (* LPS 727298f3: the auxv's words from pair 26 on, which CONFIG_RSEQ ([kb_rseq]) decides: the two
     rseq pairs and AT_NULL, or AT_NULL alone. With them the range of the vector and its place above
     the whole stack window, so a walk to AT_NULL reads only recorded words. *)
  Definition kn_tail (rseq : bool) : list kentry :=
    [KRange (EVar 3) 0x7fff80000000 0x800000000000;
     KDisj (SA (EVar 0) (-140737488355328)) 140737488355328 (SA (EVar 3) 0) 464]
    ++ (if rseq
        then [KWord (SA (EVar 3) 416) 8 (ELit 27); KWord (SA (EVar 3) 432) 8 (ELit 28);
              KWord (SA (EVar 3) 448) 8 (ELit 0)]
        else [KWord (SA (EVar 3) 416) 8 (ELit 0)]).
End MainEntry.
