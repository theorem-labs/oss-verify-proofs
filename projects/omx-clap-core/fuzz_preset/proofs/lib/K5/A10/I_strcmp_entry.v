(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Theorem Labs, 2026-10-28: fuzz_preset's program code calls the TRAMPOLINE, not the interceptor body, so the walk
   has to start four bytes earlier than the donor's does. The step is the donor's own: the released lift
   K5/A10/I_strcmp_lift.v:66-72 does one `lstep` from the trampoline and then applies the walk. The
   trampoline is one uncompressed instruction, `jal zero, <interceptor>`, measured in fuzz_preset's own images:
     asan        __wrap_strcmp 0x42d20 -> __interceptor_strcmp 0x432d4 (bytes 6f 00 40 5b)
     asan-ubsan  __wrap_strcmp 0x42e0c -> __interceptor_strcmp 0x433c0 (bytes 6f 00 40 5b)
   Nothing else here is new: the statement is I_strcmp.v's, with the entry pc replaced. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.K5.Lib Require Import Tac.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.K5.A10 Require Import ImageA.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.K5.Lib Require Import SysStep.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.K5.Lib Require Import StoreFast.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.K5.PG Require Import Str_tac Startup_glue.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.K5.A10 Require Import Layout.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.K5.AG Require Import Shadow.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.K5.A10 Require Import R_small R_m2s R_thread I_consts I_qck X_atexit D_kit I_ikit I_strcmp_spec I_strcmpw I_strcmpw2.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Import ListNotations.
Open Scope Z_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.K5.A10 Require Import I_strcmp.

(* __wrap_strcmp, measured in fuzz_preset's own image *)
Definition e_wrap_strcmp : Z := 0x42d20.

Section WithRIP.
Hypothesis RIP : rip_stmt.

Theorem istrcmp_wrap_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (p1 p2 : Z) (b1 b2 : list byte) (lo : Z),
  a0 = Z_to_bv 64 p1 -> a1 = Z_to_bv 64 p2 ->
  stk asegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - ISTRCMP_DEPTH -> kHighShadowEnd + 8 <= lo -> bv_unsigned sp < 2^63 ->
  Z.of_nat (length b1) < 2^40 -> Z.of_nat (length b2) < 2^40 ->
  bytes_at asegs m p1 b1 -> bytes_at asegs m p2 b2 -> strcmp_ok b1 b2 ->
  p1 + strcmp_sz b1 b2 <= 2^47 -> p2 + strcmp_sz b1 b2 <= 2^47 ->
  (p1 + strcmp_sz b1 b2 <= lo \/ bv_unsigned sp <= p1) -> (p2 + strcmp_sz b1 b2 <= lo \/ bv_unsigned sp <= p2) ->
  chk_ok m p1 (strcmp_sz b1 b2) -> chk_ok m p2 (strcmp_sz b1 b2) -> m2s_cells m -> icells_scmp m -> mem_inv asegs m ->
  evt asegs (istrcmp_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (strcmp_res b1 b2) lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 e_wrap_strcmp) fc None m (seg_rom asegs)).
Proof using RIP.
  intros until lo. intros.
  pose proof (munch_refl [(bv_unsigned sp - ISTRCMP_DEPTH, bv_unsigned sp)] m) as MU.
  pose proof (wmono_refl asegs m) as WM.
  unfold e_wrap_strcmp. lstep.
  eapply (istrcmp_spec RIP); eassumption.
Qed.

End WithRIP.

From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.K5.A10 Require Import R_isPoisoned.
(* The donors' own discharge of RIP (K5/{A10,B10}/R_isPoisoned.v `rip_proof`, ported here): the walk from the
   trampoline with no hypothesis left. *)
Definition istrcmp_wrap_closed := istrcmp_wrap_spec rip_proof.
