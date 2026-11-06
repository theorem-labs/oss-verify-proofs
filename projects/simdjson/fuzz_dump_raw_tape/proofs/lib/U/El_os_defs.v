(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.simdjson.fuzz_dump_raw_tape.lib.Lib Require Import Tac Arr Bytes ITree Nodes Decode SysStep RegsEquiv Image.
From OSSVerify.Proofs.simdjson.fuzz_dump_raw_tape.lib.U Require Export Layout Pj_loc_defs Pj_os_defs.
From OSSVerify.Proofs.simdjson.fuzz_dump_raw_tape.lib.P Require Import Str_tac Startup_glue.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.

Notation EL_SENTRY := 0x7d8dc%Z (only parsing).
Notation EL_SENTRY_D := 0x7d938%Z (only parsing).
Notation EL_GETLOC := 0x7c2b4%Z (only parsing).
Notation EL_USE_FACET := 0xa2840%Z (only parsing).
Notation EL_LOC_D := 0xa1fd8%Z (only parsing).
Notation EL_INS_UL := 0x7df80%Z (only parsing).
Notation EL_INS_U := 0x7dbe4%Z (only parsing).
Notation EL_INS_L := 0x7ddb4%Z (only parsing).
Notation EL_INS_D := 0x7e14c%Z (only parsing).
Notation EL_INS_I := 0x7d9e0%Z (only parsing).
Notation EL_NP_L := 0x88bc4%Z (only parsing).
Notation EL_NP_UL := 0x8911c%Z (only parsing).
Notation EL_NP_D := 0x8962c%Z (only parsing).
Notation EL_WGI := 0x8bfa8%Z (only parsing).
Notation EL_WGF := 0x8c40c%Z (only parsing).
Notation EL_PAD := 0x3bd7c%Z (only parsing).
Notation EL_STRNC := 0x3bf10%Z (only parsing).
Notation EL_SETFILL := 0x3bfec%Z (only parsing).
Notation EL_SNL := 0xb2e98%Z (only parsing).
Notation EL_DO_WIDEN := 0xa41a0%Z (only parsing).
Notation EL_DO_WIDEN_R := 0xa41a8%Z (only parsing).
Notation EL_DO_DECPT := 0xa738c%Z (only parsing).
Notation EL_DO_THSEP := 0xa739c%Z (only parsing).
Notation EL_DO_GROUPING := 0xa73ac%Z (only parsing).

Notation EL_IMP := 0xe91f8%Z (only parsing).
Notation EL_CTYPE_F := 0xe9118%Z (only parsing).
Notation EL_NPUT_F := 0xe8f80%Z (only parsing).
Notation EL_NPUNCT_F := 0xe9198%Z (only parsing).
Notation EL_CTYPE_VT := 0xd4fc8%Z (only parsing).
Notation EL_NPUT_VT := 0xd5b90%Z (only parsing).
Notation EL_NPUNCT_VT := 0xd5180%Z (only parsing).
Notation EL_CTYPE_ID := 0xe8eb0%Z (only parsing).
Notation EL_NPUT_ID := 0xe8c38%Z (only parsing).
Notation EL_NPUNCT_ID := 0xe8ec0%Z (only parsing).
Notation EL_CLOC_CELL := 0xe8dc0%Z (only parsing).
Notation EL_CLOC := 0x21470%Z (only parsing).
Notation EL_GOT_NPUT_ID := 0xd7248%Z (only parsing).
Notation EL_GOT_CTYPE_ID := 0xd7188%Z (only parsing).
Notation EL_NSB_VT := 0xd18c8%Z (only parsing).
Notation EL_OS_VT := 0xd1950%Z (only parsing).
Notation EL_IOS_VT := 0xd1978%Z (only parsing).

Definition el_dcc (m : word -> option byte) : Prop :=
  rw_cells usegs m 0xd1928 [C8 (Z_to_bv 64 0x7d680); C8 (Z_to_bv 64 0x3b1b0); C8 (Z_to_bv 64 8)]
  /\ rw_cells usegs m 0xd5000 [C8 (Z_to_bv 64 0xa41a0); C8 (Z_to_bv 64 0xa41a8)]
  /\ rw_cells usegs m 0xd5bb0 [C8 (Z_to_bv 64 0x88bc4); C8 (Z_to_bv 64 0x88e70); C8 (Z_to_bv 64 0x8911c);
                               C8 (Z_to_bv 64 0x893a4); C8 (Z_to_bv 64 0x8962c)]
  /\ rw_cells usegs m 0xd5198 [C8 (Z_to_bv 64 0xa738c); C8 (Z_to_bv 64 0xa739c); C8 (Z_to_bv 64 0xa73ac)]
  /\ rw_cells usegs m 0xd7248 [C8 (Z_to_bv 64 0xe8c38)]
  /\ rw_cells usegs m 0xd7188 [C8 (Z_to_bv 64 0xe8eb0)].

Definition ios_cellsX (OS : Z) (vptr flags width fill : Z) (j148 j284 : list byte) : list cell :=
  [C8 (Z_to_bv 64 vptr);
   C4 (Z_to_bv 64 flags); CB 4 j148;
   C8 (Z_to_bv 64 6);
   C8 (Z_to_bv 64 width);
   C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0);
   C8 (Z_to_bv 64 OS);
   C8 (Z_to_bv 64 0xe91f8);
   C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0);
   C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0);
   C8 (Z_to_bv 64 0);
   C4 (Z_to_bv 64 fill); CB 4 j284].

Definition os_cellsX (OS : Z) (pb pp ep : word) (flags width fill : Z) (dum j148 j284 : list byte) : list cell :=
  sb_cells pb pp ep dum ++ [C8 (Z_to_bv 64 0xd1950)] ++ ios_cellsX OS 0xd1978 flags width fill j148 j284.

Lemma ios_cells_X : forall OS vptr fill j148 j284, ios_cells OS vptr fill j148 j284 = ios_cellsX OS vptr 0x1002 0 fill j148 j284.
Proof. intros. reflexivity. Qed.
Lemma os_cells_X : forall OS pb pp ep fill dum j148 j284,
  os_cells OS pb pp ep fill dum j148 j284 = os_cellsX OS pb pp ep 0x1002 0 fill dum j148 j284.
Proof. intros. reflexivity. Qed.
Lemma os_cellsX_size : forall OS pb pp ep flags width fill dum j148 j284,
  cells_size (os_cellsX OS pb pp ep flags width fill dum j148 j284) = 288%nat.
Proof. intros. reflexivity. Qed.

Definition PUTINV (OS pp ep : Z) : Prop := (pp = 0 /\ ep = 0)%Z \/ (ep = OS + 128 /\ OS + 64 <= pp <= OS + 128)%Z.

Definition FILLOK (fill : Z) : Prop := (fill = 0xffffffff \/ fill = 0x20 \/ fill = 0x30)%Z.

Definition OSX (m : word -> option byte) (OS fill : Z) : Prop :=
  exists pb pp ep dum j148 j284,
    rw_cells usegs m OS (os_cellsX OS pb (Z_to_bv 64 pp) (Z_to_bv 64 ep) 0x1002 0 fill dum j148 j284) /\ PUTINV OS pp ep.

Lemma OSFRESH_OSX : forall m OS, OSFRESH m OS -> OSX m OS 0xffffffff.
Proof.
  intros m OS (dum & j148 & j284 & H). exists (Z_to_bv 64 0), 0%Z, 0%Z, dum, j148, j284.
  split; [exact H | left; lia].
Qed.

Lemma OSX_transport : forall W m m' OS fill, OSX m OS fill -> munch W m m' -> wmono usegs m m' -> disjoint_from W OS 288 -> OSX m' OS fill.
Proof.
  intros W m m' OS fill (pb & pp & ep & dum & j148 & j284 & H & PI) MU WM D. exists pb, pp, ep, dum, j148, j284.
  split; [| exact PI]. apply (rw_cells_transport usegs W m m' _ _ H MU WM). rewrite os_cellsX_size. exact D.
Qed.

Lemma os_cellsX_parts : forall m OS pb pp ep flags width fill dum j148 j284,
  rw_cells usegs m OS (os_cellsX OS pb pp ep flags width fill dum j148 j284) <->
  (rw_cells usegs m OS (sb_cells pb pp ep dum) /\ rw_cells usegs m (OS + 128) [C8 (Z_to_bv 64 0xd1950)]
   /\ rw_cells usegs m (OS + 136) (ios_cellsX OS 0xd1978 flags width fill j148 j284)).
Proof.
  intros. unfold os_cellsX.
  rewrite (Startup_glue.rw_cells_app usegs m OS). rewrite (Startup_glue.rw_cells_app usegs m _ [_]).
  cbn [sb_cells cells_size csize Nat.add].
  replace (OS + Z.of_nat 128)%Z with (OS + 128)%Z by lia. replace (OS + 128 + Z.of_nat 8)%Z with (OS + 136)%Z by lia.
  tauto.
Qed.

Definition os_xsputnX_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
    (F : bvmap 5 word) (fc : bv 32) (lo OS N : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 pb (pp ep : Z) dum m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 N) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom usegs)
    /\ munch [(bv_unsigned sp - PJ_OS_XSPUTN_STACK, bv_unsigned sp); (OS + 40, OS + 128)]%Z m m'
    /\ wmono usegs m m' /\ mem_inv usegs m'
    /\ stk usegs m' lo (bv_unsigned sp)
    /\ rw_cells usegs m' OS (sb_cells pb (Z_to_bv 64 pp) (Z_to_bv 64 ep) dum) /\ PUTINV OS pp ep.

Definition os_xsputnX_stmt : Prop :=
  forall ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (lo OS S N CAP pp ep : Z) (pb : word) (dum bs : list byte),
  stk usegs m lo (bv_unsigned sp) -> (lo <= bv_unsigned sp - PJ_OS_XSPUTN_STACK)%Z -> (0x10c000 <= lo)%Z ->
  rw_cells usegs m OS (sb_cells pb (Z_to_bv 64 pp) (Z_to_bv 64 ep) dum) -> PUTINV OS pp ep -> (bv_unsigned sp <= OS)%Z -> (OS + 288 < 2^62)%Z ->
  bytes_at usegs m S bs -> Z.of_nat (length bs) = CAP -> (0 <= N <= CAP)%Z -> (0 <= S)%Z -> (S + CAP < 2^62)%Z ->
  (S + CAP <= lo \/ OS + 288 <= S \/ (bv_unsigned sp <= S /\ S + CAP <= OS))%Z ->
  rw_cells usegs m 0xd1928 [C8 (Z_to_bv 64 0x7d680); C8 (Z_to_bv 64 0x3b1b0); C8 (Z_to_bv 64 8)] -> mem_inv usegs m ->
  evt usegs (os_xsputnX_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo OS N m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 OS) (Z_to_bv 64 S) (Z_to_bv 64 N) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 PJ_OS_XSPUTN) fc None m (seg_rom usegs)).
