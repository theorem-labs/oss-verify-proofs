(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.fast_float.from_chars.images Require Import Plain.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec ShapeSet RealizesCfg FPInv.
From OSSVerify.Proofs.fast_float.from_chars.lib.H Require Import HIface HIfaceInit P_hbase.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng MngL4 MngL4F MngL4I MngL4MC AXG_mwk.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Theorem plain_heap_ok : forall (cfg : SpuriousCfg) (HTOP : Z) (GP : word),
  sc_alloc cfg = false -> 0x97000 <= HTOP -> (forall fx : FPState, @direct_wk_stmt fx) ->
  P_heap_ok cfg (HI HTOP) GP (wa 0x75bd0) HTOP STATIC_P.
Proof.
  intros cfg HTOP GP Hoff HT DIRWK.
  exact (heap_ok_L4 cfg HTOP GP HT (malloc_contract_L4 cfg Hoff DIRWK HTOP GP HT)).
Qed.

Theorem plain_heap_init_ok : forall (cfg : SpuriousCfg) (HTOP : Z) (GP : word),
  sc_alloc cfg = false -> 0x97000 <= HTOP -> (forall fx : FPState, @direct_wk_stmt fx) ->
  heap_init_ok SEGS cfg (HI HTOP) (HeapI HTOP) INIT GP (wa 0x75bd0) HTOP P_KEEP 0x51310 MNEED.
Proof.
  intros cfg HTOP GP Hoff HT DIRWK. split.
  - exact (malloc_contract_init_L4 cfg Hoff DIRWK HTOP GP HT).
  - exact (heap_frame_init_L4 HTOP).
Qed.
