(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.simdjson.fuzz_element.lib.Lib Require Import Tac Arr Bytes ITree Nodes Decode SysStep RegsEquiv Image.
From OSSVerify.Proofs.simdjson.fuzz_element.lib.P Require Export Layout Pj_loc_defs Pj_os_defs.
From OSSVerify.Proofs.simdjson.fuzz_element.lib.P Require Import Str_tac Startup_glue.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.

Notation EL_SENTRY := 0x76b8c%Z (only parsing).
Notation EL_SENTRY_D := 0x76be8%Z (only parsing).
Notation EL_GETLOC := 0x75564%Z (only parsing).
Notation EL_USE_FACET := 0x9baf0%Z (only parsing).
Notation EL_LOC_D := 0x9b288%Z (only parsing).
Notation EL_INS_UL := 0x77230%Z (only parsing).
Notation EL_INS_U := 0x76e94%Z (only parsing).
Notation EL_INS_L := 0x77064%Z (only parsing).
Notation EL_INS_D := 0x773fc%Z (only parsing).
Notation EL_INS_I := 0x76c90%Z (only parsing).
Notation EL_NP_L := 0x81e74%Z (only parsing).
Notation EL_NP_UL := 0x823cc%Z (only parsing).
Notation EL_NP_D := 0x828dc%Z (only parsing).
Notation EL_WGI := 0x85258%Z (only parsing).
Notation EL_WGF := 0x856bc%Z (only parsing).
Notation EL_PAD := 0x3ed00%Z (only parsing).
Notation EL_STRNC := 0x3ee6c%Z (only parsing).
Notation EL_SETFILL := 0x3ef24%Z (only parsing).
Notation EL_SNL := 0xac148%Z (only parsing).
Notation EL_DO_WIDEN := 0x9d450%Z (only parsing).
Notation EL_DO_WIDEN_R := 0x9d458%Z (only parsing).
Notation EL_DO_DECPT := 0xa063c%Z (only parsing).
Notation EL_DO_THSEP := 0xa064c%Z (only parsing).
Notation EL_DO_GROUPING := 0xa065c%Z (only parsing).

Notation EL_IMP := 0xe24c8%Z (only parsing).
Notation EL_CTYPE_F := 0xe23e8%Z (only parsing).
Notation EL_NPUT_F := 0xe2250%Z (only parsing).
Notation EL_NPUNCT_F := 0xe2468%Z (only parsing).
Notation EL_CTYPE_VT := 0xce588%Z (only parsing).
Notation EL_NPUT_VT := 0xcf150%Z (only parsing).
Notation EL_NPUNCT_VT := 0xce740%Z (only parsing).
Notation EL_CTYPE_ID := 0xe2180%Z (only parsing).
Notation EL_NPUT_ID := 0xe1f08%Z (only parsing).
Notation EL_NPUNCT_ID := 0xe2190%Z (only parsing).
Notation EL_CLOC_CELL := 0xe2090%Z (only parsing).
Notation EL_CLOC := 0x22288%Z (only parsing).
Notation EL_GOT_NPUT_ID := 0xd0818%Z (only parsing).
Notation EL_GOT_CTYPE_ID := 0xd0770%Z (only parsing).
Notation EL_NSB_VT := 0xcac78%Z (only parsing).
Notation EL_OS_VT := 0xcad00%Z (only parsing).
Notation EL_IOS_VT := 0xcad28%Z (only parsing).

Definition el_dcc (m : word -> option byte) : Prop :=
  rw_cells psegs m 0xcacd8 [C8 (Z_to_bv 64 0x76930); C8 (Z_to_bv 64 0x3e254); C8 (Z_to_bv 64 8)]
  /\ rw_cells psegs m 0xce5c0 [C8 (Z_to_bv 64 0x9d450); C8 (Z_to_bv 64 0x9d458)]
  /\ rw_cells psegs m 0xcf170 [C8 (Z_to_bv 64 0x81e74); C8 (Z_to_bv 64 0x82120); C8 (Z_to_bv 64 0x823cc);
                               C8 (Z_to_bv 64 0x82654); C8 (Z_to_bv 64 0x828dc)]
  /\ rw_cells psegs m 0xce758 [C8 (Z_to_bv 64 0xa063c); C8 (Z_to_bv 64 0xa064c); C8 (Z_to_bv 64 0xa065c)]
  /\ rw_cells psegs m 0xd0818 [C8 (Z_to_bv 64 0xe1f08)]
  /\ rw_cells psegs m 0xd0770 [C8 (Z_to_bv 64 0xe2180)].

Definition ios_cellsX (OS : Z) (vptr flags width fill : Z) (j148 j284 : list byte) : list cell :=
  [C8 (Z_to_bv 64 vptr);
   C4 (Z_to_bv 64 flags); CB 4 j148;
   C8 (Z_to_bv 64 6);
   C8 (Z_to_bv 64 width);
   C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0);
   C8 (Z_to_bv 64 OS);
   C8 (Z_to_bv 64 0xe24c8);
   C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0);
   C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0);
   C8 (Z_to_bv 64 0);
   C4 (Z_to_bv 64 fill); CB 4 j284].

Definition os_cellsX (OS : Z) (pb pp ep : word) (flags width fill : Z) (dum j148 j284 : list byte) : list cell :=
  sb_cells pb pp ep dum ++ [C8 (Z_to_bv 64 0xcad00)] ++ ios_cellsX OS 0xcad28 flags width fill j148 j284.

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
  (rw_cells psegs m OS (sb_cells pb pp ep dum) /\ rw_cells psegs m (OS + 128) [C8 (Z_to_bv 64 0xcad00)]
   /\ rw_cells psegs m (OS + 136) (ios_cellsX OS 0xcad28 flags width fill j148 j284)).
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
  stk psegs m lo (bv_unsigned sp) -> (lo <= bv_unsigned sp - PJ_OS_XSPUTN_STACK)%Z -> (0x105000 <= lo)%Z ->
  rw_cells psegs m OS (sb_cells pb (Z_to_bv 64 pp) (Z_to_bv 64 ep) dum) -> PUTINV OS pp ep -> (bv_unsigned sp <= OS)%Z -> (OS + 288 < 2^62)%Z ->
  bytes_at psegs m S bs -> Z.of_nat (length bs) = CAP -> (0 <= N <= CAP)%Z -> (0 <= S)%Z -> (S + CAP < 2^62)%Z ->
  (S + CAP <= lo \/ OS + 288 <= S \/ (bv_unsigned sp <= S /\ S + CAP <= OS))%Z ->
  rw_cells psegs m 0xcacd8 [C8 (Z_to_bv 64 0x76930); C8 (Z_to_bv 64 0x3e254); C8 (Z_to_bv 64 8)] -> mem_inv psegs m ->
  evt psegs (os_xsputnX_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo OS N m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 OS) (Z_to_bv 64 S) (Z_to_bv 64 N) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 PJ_OS_XSPUTN) fc None m (seg_rom psegs)).
