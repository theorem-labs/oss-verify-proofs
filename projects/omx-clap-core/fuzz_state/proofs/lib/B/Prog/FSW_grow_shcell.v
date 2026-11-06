(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: lib/B (fs.asan-ubsan) twin of lib/A/Prog/FSW_shcell.v (a working branch
   f9ccbd8f565, a Theorem Labs lane; the same text at a working branch 582c4d69613), over B's image (YB1v tfibsegs)
   instead of A's AB1v. Same names; nothing else changed. *)
(* A shadow byte the walk reads through a SAVED register, as a 1-byte read-only region of value 0. The token run
   (FSW_K fsw_aj_run_tokU, Reusable/YCbn.v tok_load) recognizes an inline check only when its address is (x >> 3) + Bx
   computed in the run; a function that keeps a shadow address in a callee-saved register across a program call and
   reads it after the call (grow in B: 0x83d70 lbu 0(s9), 0x83dbc lbu 0(s7), 0x83dc8 lbu 0(s5), around fuzz_realloc)
   presents the engine a plain load from that register's atom. This file gives the region the resumed state needs for it
   (an rs entry of FSW_K3.fsw_after_callFPU_args): based at the register's atom n, one byte, no write window, holding
   SLit 0 - from range_addressable of the 8-aligned granule x .. x + 8 whose shadow byte it is. A lemma file: no
   function's contract is proved here (rule 24). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B Require Import YB1v.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.

(* the shadow byte at atom n's value, read-only, holding 0 *)
Definition fs_shcell_region (n : nat) : YP09.region :=
  YP09.mkRegion (Some n) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SLit 0))].

Lemma fsw_shcell_region_ok : forall (H : word -> bool) (mem : word -> option byte) (E : env) (n : nat) (x : Z),
  bv_unsigned (ew E n) = SHADOW_OFF + x / 8 -> 0 <= x -> x mod 8 = 0 ->
  range_addressable (aview tfibsegs H mem) SHADOW_OFF x 8 ->
  region_ok tfibsegs E (mrestrict H mem) (fs_shcell_region n).
Proof.
intros H mem E n x Hn Hx0 Hx8 Hra.
pose proof (u64_range (ew E n)) as Hr. rewrite Hn in Hr.
destruct (Hra (x + 7) ltac:(lia)) as (s & Hs & Hok).
assert (Esh : shadow_of_addr SHADOW_OFF (x + 7) = SHADOW_OFF + x / 8).
{ unfold shadow_of_addr. f_equal. pose proof (Z.div_mod x 8 ltac:(lia)). Z.div_mod_to_equations. lia. }
assert (Hs0 : s = 0).
{ destruct Hok as [Hok|Hok]; [exact Hok|]. exfalso.
  assert (E7 : (x + 7) mod 8 = 7) by (rewrite Z.add_mod, Hx8 by lia; reflexivity). lia. }
subst s. rewrite Esh in Hs. unfold aview in Hs.
destruct (mbyte tfibsegs (mrestrict H mem) (SHADOW_OFF + x / 8)) as [b|] eqn:Eb; [|discriminate Hs].
cbn in Hs. injection Hs as Hb0.
unfold region_ok, fs_shcell_region. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
rewrite Hn. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
constructor; [|constructor].
intros i Hi. cbn [YP09.c_len YP09.cv_len YP09.c_val YP09.c_off Z.of_N] in Hi. assert (i = 0) as -> by lia.
exists (Z_to_bv 8 0). split.
- cbn [cbyte YP09.c_val]. unfold byte_of_word. f_equal.
- cbn [YP09.c_off]. rewrite !Z.add_0_r, Eb. f_equal. apply bv_eq. rewrite Hb0.
  rewrite Z_to_bv_unsigned. reflexivity.
Qed.
