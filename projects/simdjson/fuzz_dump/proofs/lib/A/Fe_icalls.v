(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.simdjson.fuzz_dump.lib.Lib Require Import SFModel Arr ITree Nodes Decode ImageA.
From OSSVerify.Proofs.simdjson.fuzz_dump.lib.A Require Import FX_lib R_m2s I_consts F_achk.
From OSSVerify.Proofs.simdjson.fuzz_dump.lib.Spec Require Import SoftFloat FmtFp.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Notation mem := (word -> option byte).

Definition rod_chk_fp (m : mem) : Prop :=
  chkr m 0x13e80 19 /\ chkr m 0x14980 1 /\ chkr m 0x17d80 3 /\ chkr m 0x20a8f 3 /\ chkr m 0x1a354 3 /\ chkr m 0x1fe16 3.

Definition e_frexpl_stub : Z := 0x6a100.

Definition ifx_real (m : mem) : Prop := ro_cells asegs m 0x163d58 [C8 (Z_to_bv 64 0x14711c)].

Definition IFREXPL_DEPTH : Z := 2240.

Definition ifrexpl_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (P x E lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms' => exists (x' e' : Z) (t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : mem),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (lo64 x')) (Z_to_bv 64 (hi64 x')) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp - IFREXPL_DEPTH, bv_unsigned sp); (P, P + 4)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (bv_unsigned sp)
    /\ rw_cells asegs m' P [C4 (Z_to_bv 64 e')]
    /\ frexpl FREXPL_FUEL x E = Some (x', e').

Definition ifrexpl_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (E lo : Z),
    stk asegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - IFREXPL_DEPTH -> kHighShadowEnd + 8 <= lo -> bv_unsigned sp < 2^63 ->
    mem_inv asegs m ->
    rw_cells asegs m (bv_unsigned a2) [C4 (Z_to_bv 64 E)] ->
    (bv_unsigned a2 + 4 <= lo \/ bv_unsigned sp <= bv_unsigned a2) ->
    chkr m (bv_unsigned a2) 4 -> ictx m -> ifx_real m ->
    (let x := bv_unsigned a0 + 2^64 * bv_unsigned a1 in
     Z.land (Z.shiftr (hi64 x) 48) 0x7fff <> 0 \/ f128_le x F128_ZERO = 0) ->
    evt asegs (ifrexpl_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc
                 (bv_unsigned a2) (bv_unsigned a0 + 2^64 * bv_unsigned a1) E lo m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 e_frexpl_stub) fc None m (seg_rom asegs)).
