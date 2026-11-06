(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/openssl/bndiv/lib/A/F_memset.v, with its module paths and addresses changed; 2 of its 33 lines of code are new or changed and 201 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-10: relocated from plugin-hostd/fuzz_reply (a working branch 86b50358d34) to libreac/fuzz_boxreg.asan-ubsan by symbol + offset pairing (port_addr_check 5033540ba83b predict mode; boxreg's interceptor and runtime code is instruction-for-instruction fuzz_reply's modulo numerals): 2 address numeral(s) rewritten, module paths changed (this image's tree is lib/B). *)
(* Ported from: a working branch 840c4afa7e2 proofs/omx-clap-core/fuzz_state/lib/A/Bz/A/F_memset.v.
   Changes (a Theorem Labs lane, 2026-10-29): module path fuzz_state -> fuzz_reply; 2 fuzz_state.asan address numerals moved to
   fuzz_reply.asan (2 code, 0 data cell), each paired by code (instruction by instruction, pc-relative
   fields masked) or, for a data cell, by the auipc pair that loads it (table: lib/A/RT_gxa_mem_Tbl.v); 0 geometry
   constants kept. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.B.Bz.Lib Require Import Tac Arr.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.B.Bz.Lib Require Import ImageA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
(* [comment removed for export] *)
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Open Scope bv_scope.

Definition memset_entry := 0x929ac%Z.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition memset_postZ (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (D C N : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1' a2' a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 D) a1' a2' a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch [(D, D + N)]%Z m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ rw_cells asegs m' D [CB (Z.to_nat N) (repeat (Z_to_bv 8 (C mod 256)) (Z.to_nat N))].
Lemma rw_cells_CB0 : forall m A, (0 <= A <= 2^64)%Z -> rw_cells asegs m A [CB 0 []].
Proof.
  intros m A HA. split; [split|].
  - cbn. split; reflexivity || exact I.
  - cbn [cells_bytes cbytes app]. apply bytes_at_nil. exact HA.
  - cbn [cells_size csize Nat.add]. split; [lia|]. split; [lia|]. intros i Hi. lia.
Qed.

Definition memset_callZ_stmt : Prop :=
  forall ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (D C N : Z) (junk : list byte),
  rw_cells asegs m D [CB (Z.to_nat N) junk] ->
  mem_inv asegs m ->
  (0 <= D)%Z -> (0 <= N < 2^64)%Z -> (D + N <= 2^64)%Z -> (0 <= C < 2^64)%Z ->
  evt asegs (memset_postZ ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc D C N m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 D) (Z_to_bv 64 C) (Z_to_bv 64 N) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x929ac) fc None m (seg_rom asegs)).
