(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.AS Require Import ShapeAlg.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.Lib Require Import ImageA RzCPS.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A Require Layout RT_iface D_defs D_kit D_clx I_read RT_liveprim L_libA R_unwind_chain. Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.Layout.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.RT_iface.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.D_defs.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.D_kit.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.D_clx.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.I_read.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.RT_liveprim.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.L_libA.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.R_unwind_chain.TwinB__.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A Require Import Shadow.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.L2B Require Import L2Kit L2Act L2Stmt L2StmtS B0_sessK.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require Import PropExec.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import Tac WalkLib SegsB0.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzArr BzCMem BzCStream BzCState BzCBlock BzCDriver BzArrD CmpMem CmpCut CmpSess CmpSess2 CmpSessB CmpFsKit0 AsanKit AsanCut B0_b2c_cbV B0_b2c_hcV B0_b2c_wrV B0_b2c_wrE.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeil.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzParams.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import CmpCut6.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Open Scope Z_scope.
#[local] Notation mem := (word -> option byte).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section ActNewLeaf.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Variables (lo P usp sp0 : Z) (hasf : bool) (k : nat) (FB SHF FSZ SSZ : Z) (fr : list (Z * nat)) (live0 : list (Z * Z)) (Wc : list (Z * Z)).
Hypothesis G : act_geom RT lo P usp sp0 hasf k FB SHF FSZ SSZ fr live0 Wc.
Variable mi : mem.
Notation PRESI := (PRESI usp fr live0 Wc mi).
Notation SOK Σ := (sig_ok RT sp0 hasf k FB fr live0 Σ).

Lemma after_l1_new_leaf : forall Σ W D (m m' : mem), SOK Σ -> ART RT Σ m -> KMem.mem_inv bsegs m -> PRESI m ->
  NMem.mem_inv b0segs m' -> munch W m m' -> wmono b0segs m m' -> 0 <= D -> lo + RT_STACK <= P - D ->
  (forall x, ~ KFrame.outside W x -> (P - D <= x < usp) \/ (FB <= x < FB + FSZ - 8) \/ (SHF <= x < SHF + SSZ) \/ ~ outside Wc x
                                     \/ ((exists p n, In (p, n) (rt_live RT Σ) /\ p <= x < p + n) /\ ~ aclient live0 fr usp x)) ->
  ART RT Σ m' /\ KMem.mem_inv bsegs m' /\ PRESI m' /\ rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) P W m m'.
Proof.
  intros Σ W D m m' S ART0 MI0 PR NMI MU WM HD HLO HW. pose proof S as (S1 & S2 & S3).
  pose proof G as [FSZE SSZE SSB AX LOW LOR PUS SPT SPA GFR GSH SP0R CAP WCL].
  assert (HA : forall x, ~ KFrame.outside W x -> aclient (rt_live RT Σ) (rt_frames RT Σ) (P - D) x).
  { intros x Hx. destruct (HW x Hx) as [E|[E|[E|[E|[(p & n & IN & R) _]]]]].
    - left. lia.
    - apply (aclient_mono _ _ P _ _ (P - D) x (acl_frame G Σ x S E)); [auto| auto| lia].
    - apply (aclient_mono _ _ P _ _ (P - D) x (acl_shadow G Σ x S E)); [auto| auto| lia].
    - apply (aclient_mono _ _ P _ _ (P - D) x (acl_caller G Σ x S (WCL x E))); [auto| auto| lia].
    - right; right; left. exists p, n. split; [exact IN| exact R]. }
  split; [| split; [| split]].
  - apply (art_of_munch RT AF Σ m m' W (P - D) ART0 ltac:(rewrite S2; unfold RT_STACK in *; lia) MU WM HA).
  - apply (kmem_inv_munch' bsegs W m m' MI0 MU NMI). intros x Hx. unfold KMem.UTOP. pose proof (aclient_below RT AF Σ m (P - D) x ART0 (HA x Hx)) as B.
    unfold USTACK_TOP in B. exact B.
  - intros a [Ha Ho]. rewrite <- (PR a (conj Ha Ho)). apply MU.
    destruct (outside_dec W (bv_unsigned a)) as [O|O]; [exact O| exfalso]. destruct (HW _ O) as [E|[E|[E|[E|[_ E]]]]].
    + assert (AC : aclient (rt_live RT Σ) (rt_frames RT Σ) usp (bv_unsigned a)).
      { apply (aclient_mono live0 fr usp _ _ usp _ Ha); [exact S3| intros e He; rewrite S1; apply in_or_app; right; exact He| lia]. }
      destruct (aclient_split RT AF Σ m usp _ ART0 AC) as [E1|E1].
      * apply (CAP _ Ha). left. lia.
      * rewrite S2 in E1. unfold RT_STACK in *. lia.
    + apply (CAP _ Ha). right; left. lia.
    + apply (CAP _ Ha). right; right. exact E.
    + exact (E Ho).
    + exact (E Ha).
  - exact (pfp_of_nmunch _ _ _ W m m' MU).
Qed.
End ActNewLeaf.
