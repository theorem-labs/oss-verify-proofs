(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.leptonica.jpegiostub_fuzzer.lib.K5.Lib Require Import Mem Frame Cells.
From OSSVerify.Proofs.leptonica.jpegiostub_fuzzer.lib.K5.B16 Require Import ImageA.
From OSSVerify.Proofs.leptonica.jpegiostub_fuzzer.lib.K5.B16 Require Import Layout.
From OSSVerify.Proofs.leptonica.jpegiostub_fuzzer.lib.K5.AG Require Import Shadow.
From OSSVerify.Proofs.leptonica.jpegiostub_fuzzer.lib.K5.B16 Require Import RT_iface.
From OSSVerify.Proofs.leptonica.jpegiostub_fuzzer.lib.K5.AG Require Import R_sizeclass.
From OSSVerify.Proofs.leptonica.jpegiostub_fuzzer.lib.K5.B16 Require Import R_cache_defs R_prim_defs RT_state RT_rep RT_sep.
Import ListNotations.
Open Scope Z_scope.

Lemma rta_live_align : forall Σ m p n, ART_A Σ m -> In (p, n) (live Σ) -> p mod 16 = 0.
Proof.
  intros Σ m p n HA Hin.
  destruct (geo_live Σ m HA p n Hin) as [(c & i & Hc & _ & -> & _)|(s & Hs & _ & _ & -> & _)].
  - pose proof (geo_layout Σ m HA) as HL. unfold layout_ok in HL.
    assert (SB16 : l_SB (lay Σ) mod 2 ^ 16 = 0) by tauto. clear HL.
    pose proof (ClassSize_range c Hc) as (_ & CS32).
    unfold p_ubeg, p_abeg, rz_size.
    change (2 ^ 32) with (16 * 268435456). change (2 ^ 16) with (16 * 4096) in SB16.
    set (S := l_SB (lay Σ)) in *. set (K := ClassSize c) in *. set (R := 2 ^ rz_log n). set (I := Z.of_nat i).
    assert (E1 : S = 16 * (4096 * (S / (16 * 4096)))) by (pose proof (Z.div_mod S (16 * 4096) ltac:(lia)); lia).
    assert (E2 : K = 16 * (2 * (K / 32))) by (pose proof (Z.div_mod K 32 ltac:(lia)); lia).
    rewrite E1, E2.
    replace (16 * (4096 * (S / (16 * 4096))) + c * (16 * 268435456) + I * (16 * (2 * (K / 32))) + 16 * R)
      with ((4096 * (S / (16 * 4096)) + c * 268435456 + I * (2 * (K / 32)) + R) * 16) by ring.
    apply Z.mod_mul. lia.
  - pose proof (geo_wf Σ m HA) as WF. unfold rt_wf in WF.
    assert (G : grant_ok (lay Σ) (s_mb s) (smsz (s_n s))).
    { destruct WF as (_ & _ & _ & HS & _). destruct HS as (_ & _ & _ & HSF & _).
      exact (proj1 (proj2 (proj1 (Forall_forall _ _) HSF s Hs))). }
    destruct G as (_ & G4096 & _). unfold s_ubeg.
    pose proof (Z.div_mod (s_mb s) 4096 ltac:(lia)) as E.
    replace (s_mb s + 4096 + 2048) with ((256 * (s_mb s / 4096) + 384) * 16) by lia.
    apply Z.mod_mul. lia.
Qed.
