(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.LibA Require Import X1di X1cg X1ch X1cq X1d0 X1cl X1dh X1d8 X1cr.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.SpecA Require Import X1rw X1rv X1s9 X1ro.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.PA Require Export X1dw.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.PA Require Import X1e9 X1e5.
From OSSVerify.speex.speex_decode_fuzzer_float.images Require Import Plain.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.LibA Require Import X1dg.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Import ListNotations.
Open Scope bv_scope.
Import X1cq.Exc.

Notation psegs := X1cr.psegs.

Definition stdout_file (m : word -> option byte) (so : stdout_st) : Prop :=
exists (flags mode : word) (tail bufbytes : list byte),
rw_cells psegs m RSTDOUT
(file_cells flags
(if so_active so then RSTDOUT_BUF + 1024 else 0)%Z
(if so_active so then RSTDOUT_BUF + zlength (so_buf so) else 0)%Z
(if so_active so then RSTDOUT_BUF else 0)%Z
(if so_first so then F_STDOUT_WRITE else F_STDIO_WRITE)
RSTDOUT_BUF 1024 1 mode
(if so_lbf_nl so then 10 else 0xffffffff)%Z tail)
/\ Z.land (bv_unsigned flags) 72 = 0%Z
/\ rw_cells psegs m RSTDOUT_BUF [CB 1024 bufbytes]
/\ firstn (length (so_buf so)) bufbytes = to_bytes (so_buf so)
/\ (zlength (so_buf so) <= 1024)%Z
/\ (so_active so = false -> so_buf so = []).

Definition stderr_file (m : word -> option byte) : Prop :=
exists (flags mode : word) (e wend : Z) (tail : list byte),
rw_cells psegs m RSTDERR (file_cells flags wend e e F_STDIO_WRITE 0x66608 0 2 mode 0xffffffff tail).

Section StdioExitStatement.
Context {St : Type} (get_so : St -> stdout_st) (set_so : stdout_st -> St -> St).

Definition stdio_exit_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(lo : Z) (guard : word) (m : word -> option byte) (s : St) : unit -> St -> machine_state -> Prop :=
fun _ s' ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 so' m',
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom psegs)
/\ munch [(bv_unsigned sp - 160, bv_unsigned sp); (RSTDOUT, 0x35dd8); (RSTDOUT_BUF, 0x66a10)]%Z m m'
/\ wmono psegs m m' /\ mem_inv psegs m'
/\ stk psegs m' lo (bv_unsigned sp)
/\ s' = set_so so' s
/\ stdout_file m' so' /\ so_buf so' = []
/\ stderr_file m'
/\ rw_cells psegs m' 0x34bc0 [C8 (Z_to_bv 64 0x661a8)] /\ rw_cells psegs m' 0x661a8 [C8 guard].

Definition stdio_exit_spec_stmt : Prop :=
forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z) (s : St) (guard : word)
(cdt thr sec : byte) (tm1 : word),
stk psegs m lo (bv_unsigned sp) ->
rw_cells psegs m 0x661c8 [C1 cdt; C1 thr; C1 sec; C1 (Z_to_bv 8 0); C4 tm1] ->
rw_cells psegs m 0x665f8 [C8 z64] ->
rw_cells psegs m 0x665e8 [C8 z64] ->
rw_cells psegs m 0x35dd8 [C8 (Z_to_bv 64 RSTDOUT)] ->
rw_cells psegs m 0x35ce8 [C8 (Z_to_bv 64 RSTDERR)] ->
stdout_file m (get_so s) -> stderr_file m ->
rw_cells psegs m 0x34bc0 [C8 (Z_to_bv 64 0x661a8)] -> rw_cells psegs m 0x661a8 [C8 guard] ->
mem_inv psegs m ->
tp = Z_to_bv 64 RTP ->
(lo <= bv_unsigned sp - 160)%Z -> (0x67000 <= lo)%Z ->
implM psegs (stdout_exit_flush get_so set_so) s
(stdio_exit_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo guard m s)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x2d654) fc None m (seg_rom psegs)).
End StdioExitStatement.

Lemma impl_msys_of_enode : forall segs {St A} (n : node) (pl : resp -> option A) (Q : A -> machine_state -> Prop) (s : St) ms,
impl segs (at_node segs) (enode n pl) (epost Q) ms ->
impl segs (at_node segs) (X1rv.msys n pl s) (epost (fun p ms' => Q (fst p) ms' /\ snd p = s)) ms.
Proof.
intros segs St A n pl Q s ms H. unfold X1rv.msys, enode in *. cbn in *.
eapply evt_mono; [exact H|]. intros ms1 [Hat Hk]. split; [exact Hat|].
intros rsp. specialize (Hk rsp). destruct (pl rsp) as [a|]; cbn in *; [|exact Hk].
eapply evt_mono; [exact Hk|]. intros ms2 HQ. cbn. auto.
Qed.
