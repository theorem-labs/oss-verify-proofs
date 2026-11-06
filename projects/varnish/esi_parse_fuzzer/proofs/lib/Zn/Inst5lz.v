(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import PropExec ShapeAlg.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Mem Frame RzBridge.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import ImgU.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn Require Import W_redqm.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require Import AllocSpec LayoutPU RzAux.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import BWorld.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Local Open Scope Z_scope.

Lemma realloc_null_p0 {BW : BWorld} :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (m : word -> option byte) (md : Model) (T : TSet),
    m_halted md = None -> m_vm_lazy md = [] ->
    a0 = Z_to_bv 64 0 ->
    realizes rsegs (mkCfg (mkst (mkR ra sp gp tp t0 t1 t2 s0 s1 a1 a1 a2 a3 a4 a5 a6 a7
                                    s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) (al_malloc_pc LayoutPU) m (seg_rom rsegs)) md) T ->
    realizes rsegs (mkCfg (mkst (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
                                    s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) (al_realloc_pc LayoutPU) m (seg_rom rsegs)) md) T.
Proof.
  intros until T. intros Hh Hl -> H. cbn [al_malloc_pc al_realloc_pc LayoutPU] in *.
  rewrite mkst_MS in *.
  eapply rz_evt; [apply realloc_null_evt | exact Hh | exact Hl |].
  intros ms' ->. eapply rz_evt_fwd; [apply malloc_sym_evt | exact Hh | exact Hl | exact H].
Qed.
