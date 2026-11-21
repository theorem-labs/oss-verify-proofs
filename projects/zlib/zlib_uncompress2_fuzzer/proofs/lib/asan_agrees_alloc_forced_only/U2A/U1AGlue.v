(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_agrees_alloc_forced_only.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_agrees_alloc_forced_only.Spec Require Import Prelim Monad STree AsanCtrl AsanEmbed AsanProgDeps.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_agrees_alloc_forced_only.LibA Require Import ExecF ITreeA SysStepF Shadow.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_agrees_alloc_forced_only.AsanW Require Import AImg RtCells AProto ABase AMalloc_iface AUri_kit.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_agrees_alloc_forced_only.U2A Require Import U2AIface U2AGlue.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_agrees_alloc_forced_only.Common Require Import DrvAgree RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* unc2s harness fake frame is ASan class 1 (128 bytes); the twin of unc U2AIface.atmost1_c0 *)
Definition atmost1_c1 (LB : list ablock) : Prop :=
  forall F1 n1 F2 n2, In (mkABlock (ABFake 1) F1 n1) LB -> In (mkABlock (ABFake 1) F2 n2) LB -> F1 = F2.

Section CANSEC1. Context {rc : runConstT}.
Section AI.
Variable AI : AMallocIface.
Notation CI := (aci AI).

Lemma stk_sh_pres : forall LB SP m m' X N f,
  aheap_pres CI LB SP m m' ->
  X mod 8 = 0 -> ATOP <= X -> X + 8 * N <= 2^47 ->
  shadow_bytes m (Z.shiftr X 3 + 2147450880) (Z.shiftr X 3 + 2147450880 + N) f ->
  shadow_bytes m' (Z.shiftr X 3 + 2147450880) (Z.shiftr X 3 + 2147450880 + N) f.
Proof.
  intros LB SP m m' X N f HP X8 XA X47 (A & B & H). split; [exact A|]. split; [exact B|].
  intros s Hs. rewrite <- (H s Hs). atop_facts.
  rewrite Z.shiftr_div_pow2 in Hs by lia. change (2^3) with 8 in Hs.
  set (a' := 8 * (s - 2147450880)).
  assert (E : s = shad a') by (subst a'; rewrite shad_div; unfold ASHOFF; Z.div_mod_to_equations; lia).
  rewrite E. apply (aheap_pres_shadow CI LB SP m m' a' HP).
  - left. subst a'. Z.div_mod_to_equations. lia.
  - rewrite <- E. lia.
Qed.
End AI.
End CANSEC1.
