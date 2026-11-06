(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.simdjson.fuzz_dump.lib.Lib Require Import Tac Arr Bytes ITree Nodes Decode SysStep RegsEquiv Image.
From OSSVerify.Proofs.simdjson.fuzz_dump.lib.P Require Export Layout Pj_loc_defs Pj_os_defs.
From OSSVerify.Proofs.simdjson.fuzz_dump.lib.P Require Import Str_tac Startup_glue.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.

Notation EL_SENTRY := 0x7349c%Z (only parsing).
Notation EL_SENTRY_D := 0x734f8%Z (only parsing).
Notation EL_GETLOC := 0x71e74%Z (only parsing).
Notation EL_USE_FACET := 0x981f8%Z (only parsing).
Notation EL_LOC_D := 0x97990%Z (only parsing).
Notation EL_INS_UL := 0x73938%Z (only parsing).
Notation EL_INS_U := 0x73c94%Z (only parsing).
Notation EL_INS_L := 0x7376c%Z (only parsing).
Notation EL_INS_D := 0x73b04%Z (only parsing).
Notation EL_INS_I := 0x73a90%Z (only parsing).
Notation EL_NP_L := 0x7e57c%Z (only parsing).
Notation EL_NP_UL := 0x7ead4%Z (only parsing).
Notation EL_NP_D := 0x7efe4%Z (only parsing).
Notation EL_WGI := 0x81960%Z (only parsing).
Notation EL_WGF := 0x81dc4%Z (only parsing).
Notation EL_PAD := 0x3b940%Z (only parsing).
Notation EL_STRNC := 0x3baac%Z (only parsing).
Notation EL_SETFILL := 0x3bf6c%Z (only parsing).
Notation EL_SNL := 0xa8850%Z (only parsing).
Notation EL_DO_WIDEN := 0x99b58%Z (only parsing).
Notation EL_DO_WIDEN_R := 0x99b60%Z (only parsing).
Notation EL_DO_DECPT := 0x9cd44%Z (only parsing).
Notation EL_DO_THSEP := 0x9cd54%Z (only parsing).
Notation EL_DO_GROUPING := 0x9cd64%Z (only parsing).

Notation EL_IMP := 0xde8a8%Z (only parsing).
Notation EL_CTYPE_F := 0xde7c8%Z (only parsing).
Notation EL_NPUT_F := 0xde630%Z (only parsing).
Notation EL_NPUNCT_F := 0xde848%Z (only parsing).
Notation EL_CTYPE_VT := 0xca980%Z (only parsing).
Notation EL_NPUT_VT := 0xcb548%Z (only parsing).
Notation EL_NPUNCT_VT := 0xcab38%Z (only parsing).
Notation EL_CTYPE_ID := 0xde560%Z (only parsing).
Notation EL_NPUT_ID := 0xde2e8%Z (only parsing).
Notation EL_NPUNCT_ID := 0xde570%Z (only parsing).
Notation EL_CLOC_CELL := 0xde470%Z (only parsing).
Notation EL_CLOC := 0x215f0%Z (only parsing).
Notation EL_GOT_NPUT_ID := 0xccc00%Z (only parsing).
Notation EL_GOT_CTYPE_ID := 0xccb40%Z (only parsing).
Notation EL_NSB_VT := 0xc7280%Z (only parsing).
Notation EL_OS_VT := 0xc7308%Z (only parsing).
Notation EL_IOS_VT := 0xc7330%Z (only parsing).

Definition el_dcc (m : word -> option byte) : Prop :=
  rw_cells psegs m 0xc72e0 [C8 (Z_to_bv 64 0x73240); C8 (Z_to_bv 64 0x3b5f8); C8 (Z_to_bv 64 8)]
  /\ rw_cells psegs m 0xca9b8 [C8 (Z_to_bv 64 0x99b58); C8 (Z_to_bv 64 0x99b60)]
  /\ rw_cells psegs m 0xcb568 [C8 (Z_to_bv 64 0x7e57c); C8 (Z_to_bv 64 0x7e828); C8 (Z_to_bv 64 0x7ead4);
                               C8 (Z_to_bv 64 0x7ed5c); C8 (Z_to_bv 64 0x7efe4)]
  /\ rw_cells psegs m 0xcab50 [C8 (Z_to_bv 64 0x9cd44); C8 (Z_to_bv 64 0x9cd54); C8 (Z_to_bv 64 0x9cd64)]
  /\ rw_cells psegs m 0xccc00 [C8 (Z_to_bv 64 0xde2e8)]
  /\ rw_cells psegs m 0xccb40 [C8 (Z_to_bv 64 0xde560)].

Definition ios_cellsX (OS : Z) (vptr flags width fill : Z) (j148 j284 : list byte) : list cell :=
  [C8 (Z_to_bv 64 vptr);
   C4 (Z_to_bv 64 flags); CB 4 j148;
   C8 (Z_to_bv 64 6);
   C8 (Z_to_bv 64 width);
   C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0);
   C8 (Z_to_bv 64 OS);
   C8 (Z_to_bv 64 0xde8a8);
   C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0);
   C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0);
   C8 (Z_to_bv 64 0);
   C4 (Z_to_bv 64 fill); CB 4 j284].

Definition os_cellsX (OS : Z) (pb pp ep : word) (flags width fill : Z) (dum j148 j284 : list byte) : list cell :=
  sb_cells pb pp ep dum ++ [C8 (Z_to_bv 64 0xc7308)] ++ ios_cellsX OS 0xc7330 flags width fill j148 j284.

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
    rw_cells psegs m OS (os_cellsX OS pb (Z_to_bv 64 pp) (Z_to_bv 64 ep) 0x1002 0 fill dum j148 j284) /\ PUTINV OS pp ep.

Lemma OSFRESH_OSX : forall m OS, OSFRESH m OS -> OSX m OS 0xffffffff.
Proof.
  intros m OS (dum & j148 & j284 & H). exists (Z_to_bv 64 0), 0%Z, 0%Z, dum, j148, j284.
  split; [exact H | left; lia].
Qed.

Lemma OSX_transport : forall W m m' OS fill, OSX m OS fill -> munch W m m' -> wmono psegs m m' -> disjoint_from W OS 288 -> OSX m' OS fill.
Proof.
  intros W m m' OS fill (pb & pp & ep & dum & j148 & j284 & H & PI) MU WM D. exists pb, pp, ep, dum, j148, j284.
  split; [| exact PI]. apply (rw_cells_transport psegs W m m' _ _ H MU WM). rewrite os_cellsX_size. exact D.
Qed.

Lemma os_cellsX_parts : forall m OS pb pp ep flags width fill dum j148 j284,
  rw_cells psegs m OS (os_cellsX OS pb pp ep flags width fill dum j148 j284) <->
  (rw_cells psegs m OS (sb_cells pb pp ep dum) /\ rw_cells psegs m (OS + 128) [C8 (Z_to_bv 64 0xc7308)]
   /\ rw_cells psegs m (OS + 136) (ios_cellsX OS 0xc7330 flags width fill j148 j284)).
Proof.
  intros. unfold os_cellsX.
  rewrite (Startup_glue.rw_cells_app psegs m OS). rewrite (Startup_glue.rw_cells_app psegs m _ [_]).
  cbn [sb_cells cells_size csize Nat.add].
  replace (OS + Z.of_nat 128)%Z with (OS + 128)%Z by lia. replace (OS + 128 + Z.of_nat 8)%Z with (OS + 136)%Z by lia.
  tauto.
Qed.

Definition os_xsputnX_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
    (F : bvmap 5 word) (fc : bv 32) (lo OS N : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 pb (pp ep : Z) dum m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 N) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom psegs)
    /\ munch [(bv_unsigned sp - PJ_OS_XSPUTN_STACK, bv_unsigned sp); (OS + 40, OS + 128)]%Z m m'
    /\ wmono psegs m m' /\ mem_inv psegs m'
    /\ stk psegs m' lo (bv_unsigned sp)
    /\ rw_cells psegs m' OS (sb_cells pb (Z_to_bv 64 pp) (Z_to_bv 64 ep) dum) /\ PUTINV OS pp ep.

Definition os_xsputnX_stmt : Prop :=
  forall ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (lo OS S N CAP pp ep : Z) (pb : word) (dum bs : list byte),
  stk psegs m lo (bv_unsigned sp) -> (lo <= bv_unsigned sp - PJ_OS_XSPUTN_STACK)%Z -> (0x101000 <= lo)%Z ->
  rw_cells psegs m OS (sb_cells pb (Z_to_bv 64 pp) (Z_to_bv 64 ep) dum) -> PUTINV OS pp ep -> (bv_unsigned sp <= OS)%Z -> (OS + 288 < 2^62)%Z ->
  bytes_at psegs m S bs -> Z.of_nat (length bs) = CAP -> (0 <= N <= CAP)%Z -> (0 <= S)%Z -> (S + CAP < 2^62)%Z ->
  (S + CAP <= lo \/ OS + 288 <= S \/ (bv_unsigned sp <= S /\ S + CAP <= OS))%Z ->
  rw_cells psegs m 0xc72e0 [C8 (Z_to_bv 64 0x73240); C8 (Z_to_bv 64 0x3b5f8); C8 (Z_to_bv 64 8)] -> mem_inv psegs m ->
  evt psegs (os_xsputnX_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo OS N m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 OS) (Z_to_bv 64 S) (Z_to_bv 64 N) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 PJ_OS_XSPUTN) fc None m (seg_rom psegs)).
