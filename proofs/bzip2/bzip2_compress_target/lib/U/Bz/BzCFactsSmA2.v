(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzArr BzArrD BzCMem BzCStream BzCState BzCMtf BzCRebuildF. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import CmpCutSM. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzCFactsGm. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import BzCFactsSmA. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzCSmF2.
From Stdlib Require Lia.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzParams.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import CmpLiaP.   (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import CpsOpen.
Section ACeilS1. Context {BZP : BzParams}.


Theorem smA_facts_intro : forall e0 e, gm_post e0 e -> 1 <= e_nblock e0 <= NBLOCKMAX + 9 -> smA_facts e.
Proof.
  intros e0 e GP NB.
  cps_destruct GP as (NI & NM & MFD & SUM & EOBc & _).
  unfold smA_facts, smA_ng, sm_alpha, sm_nmtf. cbv zeta.
  pose proof (sm_nGroups_range (e_nMTF e)) as NGR.
  assert (MF3 : forall v, 0 <= v < e_nInUse e + 2 -> zdef (e_mtfFreq e) v = true /\ 0 <= zget (e_mtfFreq e) v <= e_nMTF e).
  { intros v Hv. destruct (MFD v ltac:(lia)) as [D R]. split; [exact D|]. split; [exact R|].
    rewrite <- SUM. apply (sumF_term_le (Z.to_nat (e_nInUse e + 2)) (fun u => zget (e_mtfFreq e) u) 0 v); [|lia].
    intros b Hb. destruct (MFD b ltac:(lia)). lia. }
  assert (MF0 : forall v, 0 <= v < e_nInUse e + 2 -> 0 <= zget (e_mtfFreq e) v) by (intros v Hv; apply (MF3 v Hv)).
  split; [lia|]. split; [lia|]. split; [exact MF3|]. split.
  - intros k Hk. cbv zeta. unfold sip_k, sip0, smA_ng, sm_alpha, sm_nmtf.
    pose proof (OI_iter (e_mtfFreq e) (e_nInUse e + 2) (sm_nGroups (e_nMTF e)) (e_nMTF e) ltac:(lia) MF0 SUM k (smA_len e) ltac:(lia)) as O.
    cps_destruct O as (_ & O1 & O2 & O3 & O4). repeat split; try assumption; lia.
  - unfold sip_k, sip0, smA_ng, sm_alpha, sm_nmtf.
    apply (sm_init_tables_iter (e_mtfFreq e) (e_nInUse e + 2) (sm_nGroups (e_nMTF e)) (e_nMTF e) ltac:(lia) NGR MF0 SUM (smA_len e)).
Qed.

End ACeilS1.
