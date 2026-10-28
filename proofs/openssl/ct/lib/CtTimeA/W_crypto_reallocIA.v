(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtLib Require Import ImageCtA.
From Stdlib Require Import ZArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Fpu Sem.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP Frame Cells Step Mem RzCPS. 
From OssFuzzTheorems.Proofs.openssl.ct.lib.Malloc Require Import MallocRep MallocBlocks Malloc_iface.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Spec Require Import Prelim STree Malloc Prog LibProg ProgG BnTree.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Spec Require Import ApBase ApState ApLogic.
From OssFuzzTheorems.Proofs.openssl.ct.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtA Require Import Layout RT_iface RT_client_kit R_cache_defs R_prim_defs R_sec_defs D_defs D_cs I_lkit.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepP Require Import ApCells.
From OssFuzzTheorems.Proofs.openssl.ct.lib.BnP Require Import BnKit BnKit2.
From OssFuzzTheorems.Proofs.openssl.ct.lib.BnW Require Import BnTac BnMem.
From OssFuzzTheorems.Proofs.openssl.ct.lib.BnAsan Require Import AsKit AsLoop.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtA Require Import R_unwind_chain.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtKitA Require Import RT_iface2 LibKitA ARun BnHeapA BnRepDefs BnRepA ImplA ImplAX BnIfaceA AsStruct RtCallA W_cryptoA UnwindA EdgesA UnwindX.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtSctA Require Import RtGenStmtA.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepU Require Import ApUTac.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepA Require Import ApATac ApATacX ApBImg ApWalkTac ApRepDefs ApRep ApIface ApErrKitA2 W_akit.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtSctA Require Import W_crypto_reallocA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Local Notation E_rea_leaf := (E_CRYPTO_realloc_1fc65c : uk_leaf 0x1fd224 0x1fd2bc).                 (* [comment removed for export] *)

Section WithRT.
Context {AR : ARun} {UK : UnwindKit} {BE : BnEdges}.
Local Notation RT := (@ar_RT AR).
Local Notation AF := (@ar_AF AR).
Local Notation PMc := (@ar_PMc AR).
Local Notation FR := (@ar_FR AR).
Local Notation ACEIL := (@BnHeapA.ACEIL AR).
Local Notation AHEAP := (@BnHeapA.AHEAP AR).
Hypothesis REA : realloc_contract_gen RT.

Lemma CRYPTO_reallocI_walkAp : forall {X : Type}
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) (Σ : rts RT) (OW LB : list block) (p : bptr) (A n0 n lo : Z) (ras : list Z)
    (k : option bptr -> aprog bptr X) (Q : X -> rts RT -> machine_state -> Prop),
  AHEAP Σ OW LB m -> In (p, A, n0) OW ->
  stk ctasegs m lo (bv_unsigned sp) -> ACEIL <= lo -> lo <= bv_unsigned sp - CRYPTO_REALLOC2_STACK ->
  bv_unsigned sp + 16 <= USTACK_TOP -> bv_unsigned sp mod 16 = 0 ->
  mem_inv ctasegs m -> tp = wz TP_A -> bv_unsigned ra mod 2 = 0 ->
  realloc_statics m -> a0 = wz A -> a1 = wz n -> 1 <= n <= 0x8000000 ->
  mcost n <= rt_credit RT Σ ->
  uw_chain USTACK_TOP m (bv_unsigned sp) (bv_unsigned s0) ras -> uk_ctx CRYPTO_REALLOC (bv_unsigned ra :: ras) ->
  (forall p' Σ' ms', ~ In p' (map blk_id (OW ++ LB)) ->
     realloc_postA ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 Σ OW LB p A n0 n lo m p' Σ' ms' ->
     implAp (k (Some p')) Σ' Q ms') ->
  implAp (AReallocI p n k) Σ Q
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (wz CRYPTO_REALLOC) fc None m (seg_rom ctasegs)).
Proof.
  intros until Q. intros HEAP IN ST CEIL LO SPT SP16 MI TP RAEV RS HA0 HA1 Hn CRED UW CTX K.
  pose proof (AH_range _ _ _ _ p A n0 HEAP IN) as (A0 & A16 & N0 & AC & AI). pose proof (AH_okA _ _ _ _ p A n0 HEAP IN) as [_ N0'].
  pose proof (AH_ceil _ _ _ _ HEAP) as (C1 & C2 & C3).
  eapply (rea_proA (AReallocI p n k) Q) with (lo := lo) (ras := ras); [exact HEAP| exact ST| exact CEIL| exact LO| exact SPT| exact SP16| exact MI| exact TP| exact RS| exact HA0| exact HA1
    | clear - A0 AC C3 N0; unfold BnHeapA.ACEIL, STACK_WIN, USTACK_TOP in *; lia| clear - Hn; lia| exact UW|].
  intros m0 j0 x12 x14 MU WM MI0 ST0 HEAP0 FRS UW0.
  pose proof LO as LO'. unfold CRYPTO_REALLOC2_STACK, RT_STACK in LO'.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
  assert (ESP : bv_unsigned (Z_to_bv 64 (bv_unsigned sp - 48)) = bv_unsigned sp - 48) by (apply unsigned_lit; clear - SPR LO' CEIL C1; unfold SEGTOP_A, BnHeapA.ACEIL in *; lia).
  eapply implAp_reallocI with (avoid := map blk_id (OW ++ LB)).
  - intros Hn' HLIVE.
    eapply cps_conseq; [ eapply (REA Σ PMc) with (p := A) (n0 := n0) (n := n) (lo := lo); try reflexivity | intros c Hc; exact Hc
                       | intros c Hc; exact (realloc_post_RL Σ OW LB m0 p _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ A n0 n lo m0 c HEAP0 IN Hc) ].
    + exact ar_PMc_fdfs.
    + exact ar_PMc_ms.
    + exact (AH_live_ow _ _ _ _ (p, A, n0) HEAP0 IN).
    + exact Hn.
    + exact HLIVE.
    + exact CRED.
    + exact (AH_art _ _ _ _ HEAP0).
    + exact MI0.
    + eapply (call_okA Σ OW LB m0 lo); [exact HEAP0| exact ST0| exact CEIL| clear - LO'; unfold RT_STACK; lia| unfold USTACK_TOP in *; clear - SPT; lia| rewrite Zminus_mod, SP16; reflexivity].
    + eapply unwind_ch_intro with (ras := bv_unsigned ra :: ras); [unfold RA_CR_REALLOC; rewrite unsigned_lit by (clear; lia); exact (uk_ctx_leaf _ _ _ E_rea_leaf CTX)|].
      rewrite ESP. exact UW0.
  - intros p' Σ' ms' Hn' Hp' Hg HR.
    eapply (rea_epiA (k (Some p')) Q) with (lo := lo) (Σ := Σ) (OW := OW) (LB := LB) (m := m) (m0 := m0) (p := p) (A := A) (n0 := n0) (n := n) (sp := sp); [exact HEAP| exact HEAP0| exact IN| exact CEIL| exact LO| exact SPT| exact MI0| exact MU| exact FRS| clear - Hn; lia| exact RAEV
      | exact HR| exact Hp'| exact Hg| intros ms'' PO; exact (K p' Σ' ms'' Hp' PO)].
Qed.

End WithRT.
