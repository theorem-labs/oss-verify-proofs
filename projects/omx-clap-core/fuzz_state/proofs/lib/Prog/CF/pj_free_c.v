(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/openssl/ct/lib/CtColB/W_set0A.v, with its module paths and module names changed; 44 of its 60 lines of code are new or changed and 129 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_scene/lib/Prog/SceneTac.v, with its module paths changed; 1051 of its 1066 lines of code are new or changed and 45 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_pcap/lib/U/Prog/pcap_source_open.v, with its module paths and module names changed; 547 of its 622 lines of code are new or changed and 991 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_state/lib/Prog/CF/KindBGlue.v, with its module paths and module names changed; 2130 of its 2257 lines of code are new or changed and 495 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_state/lib/Prog/CF/pj_free.v, with its module paths and module names changed; 13 of its 42 lines of code are new or changed and 2228 lines of the source are left out. *)
From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib Require Import Contract.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Lib Require Frame.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Prog Require Import Ledger PjStruct ReaderRes.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Prog.CF Require Import CFS ContractCF KindBGlueCF FrameCF ReaderResCF.
Import ListNotations.
Local Open Scope Z_scope.

Definition PJ_FREE : Z := 0x145a4.

Section K.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Variable F : ResForm.
Let segs := ms_segs B.

Definition pj_free_writes (v : Z) (D : list (Z * Z)) (x : Z) : Prop :=
  v <> 0 /\ (v <= x < v + 56 \/ blk_set D x \/ alloc_statics x).

Definition pj_free_contract : Prop :=
  forall L A regs mem md Lam peak cnt fail b v (d : nat) D,
    reader_env B API (PJ_FREE_K d) L A regs mem md ->
    ledger B L A mem Lam peak cnt fail ->
    rf_ok F A b ->
    getr regs 10 = Z_to_bv 64 v ->
    (v = 0 /\ D = [] \/
     v <> 0 /\ pj_fd segs mem (lin Lam) d v D /\ rplace B L A Lam regs mem v /\
     Frame.disjoint_from [(v, v + 56)] (spZ regs - PJ_FREE_K d) (PJ_FREE_K d)) ->
    SR segs (mkCfg (mkst regs (Z_to_bv 64 PJ_FREE) mem (seg_rom segs)) md)
      (fun c' => exists L' A' regs' mem' md' Lam',
         c' = mkCfg (mkst regs' (getr regs 1) mem' (seg_rom segs)) md' /\
         rpost B API (PJ_FREE_K d) L A regs mem md (pj_free_writes v D) (freed D) L' A' regs' mem' md' /\
         rd_cells B mem' /\
         Permutation Lam (D ++ Lam') /\
         ledger B L' A' mem' Lam' peak cnt fail /\
         (exists D', Permutation D D' /\ rf_ok F A' (rf_frees F b D')) /\
         (v = 0 -> L' = L /\ A' = A /\ Lam' = Lam) /\
         (v <> 0 -> pj_zero segs mem' v)).

End K.
