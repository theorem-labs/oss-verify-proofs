(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib Require Import PropExec HeapIface L5CoreSpecs L5CoreSpecsU L5Top L5TopU L5Defs.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib.CJ.Bridge Require Import HeapInst0 HeapInst1 HeapClosed.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_bigint.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.   (* [comment removed for export] *)
Section SCFG_1.
Context {SCFG_P : ScfgP}.

Lemma L0_layout : forall sptop, L5CS.layout (L0 sptop).
Proof.
  intros sptop. constructor; try reflexivity.
  - cbn [hl_alloc_ro hl_img_lo hl_img_hi hl_sptop L0]. unfold HeapInst0.IMG_LO, HeapInst0.IMG_HI, Ref.RMallocRep.RLIBC, Ref.RMallocRep.RMLOCK, Ref.RMallocRep.RCTX, Ref.RMallocRep.RGOT_SSP, Ref.RMallocRep.RSSP_GUARD. intros a H. lia.
  - cbn [hl_alloc_static L0]. unfold Ref.RMallocRep.RMLOCK, Ref.RMallocRep.RCTX. intros a H. lia.
Qed.

Lemma L0_toplay : forall sptop, 0x7fff80000000 <= sptop <= 2 ^ 47 -> L5TOP.toplay (L0 sptop).
Proof.
  intros sptop H. constructor; cbn [hl_k_per_malloc hl_b_overhead hl_sptop L0]; [vm_compute; reflexivity| vm_compute; split; intros X; discriminate X| exact H].
Qed.

Lemma L1_layout : forall sptop, L5CSU.layout (L1 sptop).
Proof.
  intros sptop. constructor; try reflexivity.
  - cbn [hl_alloc_ro hl_img_lo hl_img_hi hl_sptop L1]. unfold HeapInst1.IMG_LO, HeapInst1.IMG_HI, Tgt.RMallocRep.RLIBC, Tgt.RMallocRep.RMLOCK, Tgt.RMallocRep.RCTX, Tgt.RMallocRep.RGOT_SSP, Tgt.RMallocRep.RSSP_GUARD. intros a H. lia.
  - cbn [hl_alloc_static L1]. unfold Tgt.RMallocRep.RMLOCK, Tgt.RMallocRep.RCTX. intros a H. lia.
Qed.

Lemma L1_toplay : forall sptop, 0x7fff80000000 <= sptop <= 2 ^ 47 -> L5TOPU.toplay (L1 sptop).
Proof.
  intros sptop H. constructor; cbn [hl_k_per_malloc hl_b_overhead hl_sptop L1]; [vm_compute; reflexivity| vm_compute; split; intros X; discriminate X| exact H].
Qed.
End SCFG_1.

(* [comment removed for export] *)
Check (fun sptop scfg (H : sc_alloc scfg = false) => HI0_ok_closed sptop scfg H : heap_iface_ok (L0 sptop) scfg (HI0 sptop)).
Check (fun sptop scfg (H : sc_alloc scfg = false) => HI1_ok_closed sptop scfg H : heap_iface_ok (L1 sptop) scfg (HI1 sptop)).
