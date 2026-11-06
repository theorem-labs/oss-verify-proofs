(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1cd X1bu X1cf X1cc X1c8 X1bj X1bs X1c2 X1bn.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Agent Require Import X0ok.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Agent Require Import X0pu X0pj X0qm X0pc X0qn.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Spec Require Import X1ra X1qu X1qv X1r3.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Agent Require Import X0qh X0qk X0qj X0pm.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Agent Require Import X0op X0ow X0oq.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Ltac showregs := lazymatch goal with |- evt _ _ (MS ?R _ ?pc _ _ ?m _) => idtac "REGS" R "PC" pc "MEM" m end.

Definition tomp_post {RCEIL : RunCeiling} (sp tp t0 t2 s0 s1 a3 a4 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t4 t5 t6 t1v raw : word) (F : bvmap 5 word) (fc : bv 32)
(lo P : Z) (st : mstate) (m : word -> option byte) : machine_state -> Prop :=
fun ms' => exists m' j0 j1,
ms' = MS (mkR (Z_to_bv 64 0x161c8) (Z_to_bv 64 (bv_unsigned sp + -64)) (Z_to_bv 64 0x1a800) tp t0 t1v t2 (Z_to_bv 64 0x1a000) s1
(Z_to_bv 64 P) (Z_to_bv 64 4096) (Z_to_bv 64 3) a3 a4 (Z_to_bv 64 P) (Z_to_bv 64 CTX) a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 4096) t4 t5 t6)
F (Z_to_bv 64 mprotect_entry) fc None m' (seg_rom asegs)
/\ munch [(bv_unsigned sp - 64, bv_unsigned sp)]%Z m m' /\ wmono asegs m m' /\ mem_inv asegs m'
/\ rw_cells asegs m' (bv_unsigned sp + -64) [CB 8 j0; C8 (Z_to_bv 64 P); C8 t1v; CB 24 j1; C8 s0; C8 raw]
/\ stk asegs m' lo (bv_unsigned sp + -64)
/\ mrep st m'.

Lemma carve_st_regions st p : s_regions (carve_st st p) = s_regions st.
Proof.
unfold carve_st. cbn [ctx upd_ctx s_ctx set_avail_meta_areas set_avail_meta_area_count c_meta_area_tail].
destruct (c_meta_area_tail (s_ctx st)); reflexivity.
Qed.

Definition mp_strict (a : range_ans) : Prop := match a with RgErr e => e <> 38 | RgDone b => b = true end.
Lemma dec_mprotect_rw_weaken A L rsp a : dec_mprotect_rw A L rsp = Some a -> dec_mprotect A L rsp = Some a /\ mp_strict a.
Proof.
unfold dec_mprotect_rw. destruct (dec_mprotect A L rsp) as [[e|b]|]; [| | discriminate].
- destruct (Z.eqb_spec e ENOSYS); [discriminate|]. intros H; inversion H; subst. split; [reflexivity|]. cbn. unfold ENOSYS in *. exact n.
- destruct b; [| discriminate]. intros H; inversion H; subst. split; reflexivity.
Qed.
