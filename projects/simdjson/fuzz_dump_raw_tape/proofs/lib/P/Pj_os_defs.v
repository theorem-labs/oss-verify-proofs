(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.simdjson.fuzz_dump_raw_tape.lib.Lib Require Import Tac Arr Bytes ITree Nodes Decode SysStep RegsEquiv Image.
From OSSVerify.Proofs.simdjson.fuzz_dump_raw_tape.lib.P Require Export Layout.
From OSSVerify.Proofs.simdjson.fuzz_dump_raw_tape.lib.P Require Import Str_tac Startup_glue Pj_loc_defs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.

Notation PJ_OS_CTOR := 0x3ab84%Z (only parsing).
Notation PJ_OS_PUT := 0x3bba0%Z (only parsing).
Notation PJ_OS_XSPUTN := 0x73730%Z (only parsing).
Notation PJ_OS_OVERFLOW := 0x3b29c%Z (only parsing).
Notation PJ_IOS_DTOR := 0x73524%Z (only parsing).
Notation PJ_OS_BASE_DTOR := 0x73904%Z (only parsing).

Notation PJ_OS_CTOR_STACK := 672%Z (only parsing).
Notation PJ_OS_PUT_STACK := 256%Z (only parsing).
Notation PJ_OS_XSPUTN_STACK := 64%Z (only parsing).
Notation PJ_IOS_DTOR_STACK := 48%Z (only parsing).

Definition sb_cells (pb pp ep : word) (dum : list byte) : list cell :=
  [C8 (Z_to_bv 64 0xc7978);
   C8 (Z_to_bv 64 0xdefa8);
   C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0);
   C8 pb; C8 pp; C8 ep;
   CB 64 dum].

Definition ios_cells (OS : Z) (vptr fill : Z) (j148 j284 : list byte) : list cell :=
  [C8 (Z_to_bv 64 vptr);
   C4 (Z_to_bv 64 0x1002); CB 4 j148;
   C8 (Z_to_bv 64 6);
   C8 (Z_to_bv 64 0);
   C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0);
   C8 (Z_to_bv 64 OS);
   C8 (Z_to_bv 64 0xdefa8);
   C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0);
   C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0);
   C8 (Z_to_bv 64 0);
   C4 (Z_to_bv 64 fill); CB 4 j284].

Definition os_cells (OS : Z) (pb pp ep : word) (fill : Z) (dum j148 j284 : list byte) : list cell :=
  sb_cells pb pp ep dum ++ [C8 (Z_to_bv 64 0xc7a00)] ++ ios_cells OS 0xc7a28 fill j148 j284.

Lemma os_cells_size : forall OS pb pp ep fill dum j148 j284, cells_size (os_cells OS pb pp ep fill dum j148 j284) = 288%nat.
Proof. intros. reflexivity. Qed.

Definition OSFRESH (m : word -> option byte) (OS : Z) : Prop :=
  exists dum j148 j284, rw_cells psegs m OS (os_cells OS (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) 0xffffffff dum j148 j284).

Definition OSUSED (m : word -> option byte) (OS : Z) : Prop :=
  exists pb pp ep dum j148 j284, rw_cells psegs m OS (os_cells OS pb pp ep 0x20 dum j148 j284).

Definition os_ctor_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
    (F : bvmap 5 word) (fc : bv 32) (lo OS : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom psegs)
    /\ munch [(bv_unsigned sp - PJ_OS_CTOR_STACK, bv_unsigned sp); (OS, OS + 288); (PJ_LOC_LO, PJ_LOC_HI)]%Z m m'
    /\ wmono psegs m m' /\ mem_inv psegs m'
    /\ stk psegs m' lo (bv_unsigned sp)
    /\ OSFRESH m' OS /\ LOCB m'.

Definition os_ctor_stmt : Prop :=
  forall ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (lo OS : Z) (canary : word) (junk : list byte),
  stk psegs m lo (bv_unsigned sp) -> (lo <= bv_unsigned sp - PJ_OS_CTOR_STACK)%Z -> (0x101000 <= lo)%Z -> (bv_unsigned sp < 2^62)%Z ->
  pj_locale m -> rw_cells psegs m OS [CB 288 junk] -> (bv_unsigned sp <= OS)%Z -> (OS + 288 < 2^62)%Z ->
  rw_cells psegs m 0xcd1f8 [C8 (Z_to_bv 64 0xcaed0); C8 (Z_to_bv 64 0xcaf50)] ->
  rw_cells psegs m 0xcd328 [C8 (Z_to_bv 64 0x1003d8)] -> rw_cells psegs m 0x1003d8 [C8 canary] ->
  rw_cells psegs m 0x1003fb [C1 (Z_to_bv 8 0)] -> rw_cells psegs m 0x1004d0 [C4 (Z_to_bv 64 0)] -> mem_inv psegs m ->
  evt psegs (os_ctor_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo OS m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 OS) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 PJ_OS_CTOR) fc None m (seg_rom psegs)).

Definition os_xsputn_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
    (F : bvmap 5 word) (fc : bv 32) (lo OS N : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 pb pp ep dum m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 N) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom psegs)
    /\ munch [(bv_unsigned sp - PJ_OS_XSPUTN_STACK, bv_unsigned sp); (OS + 40, OS + 128)]%Z m m'
    /\ wmono psegs m m' /\ mem_inv psegs m'
    /\ stk psegs m' lo (bv_unsigned sp)
    /\ rw_cells psegs m' OS (sb_cells pb pp ep dum).

Definition os_xsputn_stmt : Prop :=
  forall ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (lo OS S N CAP : Z) (pb : word) (dum bs : list byte),
  stk psegs m lo (bv_unsigned sp) -> (lo <= bv_unsigned sp - PJ_OS_XSPUTN_STACK)%Z -> (0x101000 <= lo)%Z ->
  rw_cells psegs m OS (sb_cells pb (Z_to_bv 64 0) (Z_to_bv 64 0) dum) -> (bv_unsigned sp <= OS)%Z -> (OS + 288 < 2^62)%Z ->
  rw_cells psegs m S [CB (Z.to_nat CAP) bs] -> (0 <= N <= CAP)%Z -> (0 <= S)%Z -> (S + CAP < 2^62)%Z ->
  (S + CAP <= lo \/ OS + 288 <= S)%Z ->
  rw_cells psegs m 0xc79d8 [C8 (Z_to_bv 64 0x73730); C8 (Z_to_bv 64 0x3b29c); C8 (Z_to_bv 64 8)] -> mem_inv psegs m ->
  evt psegs (os_xsputn_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo OS N m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 OS) (Z_to_bv 64 S) (Z_to_bv 64 N) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 PJ_OS_XSPUTN) fc None m (seg_rom psegs)).

Definition os_put_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
    (F : bvmap 5 word) (fc : bv 32) (lo OS : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (OS + 128)) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom psegs)
    /\ munch [(bv_unsigned sp - PJ_OS_PUT_STACK, bv_unsigned sp); (OS, OS + 288)]%Z m m'
    /\ wmono psegs m m' /\ mem_inv psegs m'
    /\ stk psegs m' lo (bv_unsigned sp)
    /\ OSUSED m' OS /\ LOCB m'.

Definition os_put_stmt : Prop :=
  forall ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (lo OS BUF N CAP : Z) (bs : list byte),
  stk psegs m lo (bv_unsigned sp) -> (lo <= bv_unsigned sp - PJ_OS_PUT_STACK)%Z -> (0x101000 <= lo)%Z ->
  OSFRESH m OS -> LOCB m -> (bv_unsigned sp <= OS)%Z -> (OS + 288 < 2^62)%Z ->
  rw_cells psegs m BUF [CB (Z.to_nat CAP) bs] -> (0 <= N <= CAP)%Z -> (0 <= BUF)%Z -> (BUF + CAP < 2^62)%Z ->
  (BUF + CAP <= lo \/ OS + 288 <= BUF)%Z ->
  rw_cells psegs m 0xc79d8 [C8 (Z_to_bv 64 0x73730); C8 (Z_to_bv 64 0x3b29c); C8 (Z_to_bv 64 8)] ->
  rw_cells psegs m 0xcb0b0 [C8 (Z_to_bv 64 0x9a250)] ->
  rw_cells psegs m 0xcd238 [C8 (Z_to_bv 64 0xdec60)] -> mem_inv psegs m ->
  evt psegs (os_put_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo OS m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (OS + 128)) (Z_to_bv 64 BUF) (Z_to_bv 64 N) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 PJ_OS_PUT) fc None m (seg_rom psegs)).

Definition ios_dtor_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
    (F : bvmap 5 word) (fc : bv 32) (lo OS fill : Z) (j148 j284 : list byte) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom psegs)
    /\ munch [(bv_unsigned sp - PJ_IOS_DTOR_STACK, bv_unsigned sp); (OS + 136, OS + 144)]%Z m m'
    /\ wmono psegs m m' /\ mem_inv psegs m'
    /\ stk psegs m' lo (bv_unsigned sp)
    /\ rw_cells psegs m' (OS + 136) (ios_cells OS 0xcae18 fill j148 j284).

Definition ios_dtor_stmt : Prop :=
  forall ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (lo OS fill : Z) (j148 j284 : list byte),
  stk psegs m lo (bv_unsigned sp) -> (lo <= bv_unsigned sp - PJ_IOS_DTOR_STACK)%Z -> (0x101000 <= lo)%Z ->
  rw_cells psegs m (OS + 136) (ios_cells OS 0xc7a28 fill j148 j284) -> (bv_unsigned sp <= OS)%Z -> (OS + 288 < 2^62)%Z ->
  mem_inv psegs m ->
  evt psegs (ios_dtor_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo OS fill j148 j284 m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (OS + 136)) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 PJ_IOS_DTOR) fc None m (seg_rom psegs)).

Lemma os_base_dtor_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte),
  mem_inv psegs m ->
  evt psegs (fun ms' => ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                 F (ret_pc ra) fc None m (seg_rom psegs))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 PJ_OS_BASE_DTOR) fc None m (seg_rom psegs)).
Proof. intros. step. apply evt_done. reflexivity. Qed.

Lemma OSUSED_parts : forall m OS, OSUSED m OS ->
  exists pb pp ep dum j148 j284,
    rw_cells psegs m OS (sb_cells pb pp ep dum) /\ rw_cells psegs m (OS + 128) [C8 (Z_to_bv 64 0xc7a00)]
    /\ rw_cells psegs m (OS + 136) (ios_cells OS 0xc7a28 0x20 j148 j284).
Proof.
  intros m OS (pb & pp & ep & dum & j148 & j284 & H). exists pb, pp, ep, dum, j148, j284.
  unfold os_cells in H.
  apply (proj1 (Startup_glue.rw_cells_app psegs m OS _ _)) in H. destruct H as [H1 H2].
  apply (proj1 (Startup_glue.rw_cells_app psegs m _ _ _)) in H2. destruct H2 as [H2 H3].
  cbn [sb_cells cells_size csize Nat.add] in H2, H3.
  replace (OS + Z.of_nat 128)%Z with (OS + 128)%Z in H2, H3 by lia.
  replace (OS + 128 + Z.of_nat 8)%Z with (OS + 136)%Z in H3 by lia.
  auto.
Qed.
