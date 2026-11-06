(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool Lia.
From stdpp Require Import gmap.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Spec Require Import STree Malloc MallocCtrl KLedger MI_Tree MI_Inv MI_Kit MI_Geom MI_List MI_Ext
  MI_Pres2 MI_WFree2 MI_WNtf2 MI_TF2 MI_WSlot MI_WMalloc MI_Sim MI_WAMeta MI_WRealloc MI_Contracts MRemapOp MI_WRemap.
Import ListNotations.
Local Open Scope Z_scope.

Theorem creach2_sim cs L : creach2 cs L -> SIMREL cs L.
Proof.
  induction 1 as [resv ceil Hceil|cs L n L' cs' r CR IH Hn CP|cs L c L' cs' CR IH Hc CP|cs L c g rg dst nn CR IH Hc Hs SC Hrg OK].
  - exists (minit 0 resv ceil), [], (fun _ => []). split; [reflexivity|]. split; [apply INVL_init; [lia| exact Hceil]| reflexivity].
  - destruct IH as (st & BL & LS & <- & INV & LIVE).
    destruct (cpath_follow _ _ _ _ CP) as (ans & Hf & HL).
    pose proof (strel_follow (malloc_control pans0 pupd0 pans0_range st n tt) ans) as SF. rewrite Hf in SF.
    destruct (follow (prun pans0 pupd0 tt (malloc st n)) ans) as [[o' [st' rf]]|] eqn:FF; [| destruct SF].
    destruct (malloc_sim pans0 pupd0 pans0_range st L BL LS n tt ans o' st' rf INV Hn FF) as (rc & Hf2 & _ & LIVE' & _ & RES).
    rewrite Hf in Hf2. inversion Hf2. subst cs' r. rewrite HL in RES, LIVE'.
    destruct rf as [pf|]; destruct rc as [c|]; try (exfalso; exact RES).
    + destruct RES as (off & LS' & Epf & Hoff & INV' & NI).
      exists st', (((c, off), n) :: BL), LS'. split; [reflexivity|]. split; [apply INVL_set_live; exact INV'|]. cbn. rewrite LIVE', LIVE. reflexivity.
    + destruct RES as (LS' & INV'). exists st', BL, LS'. split; [reflexivity|]. split; [exact INV'|]. rewrite LIVE'. exact LIVE.
  - destruct IH as (st & BL & LS & <- & INV & LIVE).
    rewrite LIVE in Hc. destruct (In_bslot _ _ Hc) as (off & n & Hk).
    destruct (cpath_follow _ _ _ _ CP) as (ans & Hf & HL).
    pose proof (strel_follow (free_control pans0 pupd0 st (aadd c (UNIT * off)) c tt (INVL_hdr_ok pans0 pupd0 st L BL LS c off n INV Hk)) ans) as SF.
    rewrite Hf in SF.
    destruct (follow (prun pans0 pupd0 tt (free st (Some (aadd c (UNIT * off))))) ans) as [[o' st']|] eqn:FF; [| destruct SF].
    destruct (free_sim pans0 pupd0 pans0_range st L BL LS c off n tt ans o' st' INV Hk FF) as (Hf2 & _ & LIVE' & LS' & INV').
    rewrite Hf in Hf2. inversion Hf2. subst cs'. rewrite HL in INV', LIVE'.
    exists st', (bl_remove c BL), LS'. split; [reflexivity|]. split; [apply INVL_set_live; exact INV'|]. cbn. rewrite LIVE', LIVE. symmetry. apply bl_remove_map.
  -
    destruct IH as (st & BL & LS & <- & INV & LIVE).
    rewrite LIVE in Hc. destruct (In_bslot _ _ Hc) as (off & n & Hk).
    destruct OK as (D0 & DA & NA & N2 & NL & DC & RESV & DISJ).
    cbn [s_slots strip] in Hs. cbn [s_regions strip] in Hrg, DISJ. cbn [s_reserved strip] in RESV.
    assert (SC' : m_sizeclass (MR st g) = 63) by exact SC.
    destruct (is_blocks _ _ _ (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 INV)))))) _ Hk) as (g2 & i2 & Hs2 & Ho & _ & _). clear g2 i2 Hs2. cbn [boff bsize bslot fst snd] in Ho.
    set (n' := nn - UNIT * off - UNIT - IB).
    assert (Hn' : 0 <= n') by (subst n'; unfold UNIT, IB, PGSZ in *; lia).
    assert (NN : mremap_needed off n' = nn).
    { unfold mremap_needed, n'. replace (nn - UNIT * off - UNIT - IB + UNIT * off + UNIT + IB) with nn by lia. apply round_up_pg_id. exact NA. }
    pose proof (INVL_remap x0 st L BL LS c g off n n' dst INV Hk eq_refl eq_refl Hs SC' Hn' D0 DA) as IR.
    rewrite NN in IR. specialize (IR NL N2 DC DISJ rg Hrg).
    pose proof (rm_eq st c g off n n' dst Hs) as E4. pose proof (rm_strip st c g off n n' dst Hs) as ES. rewrite NN in ES.
    exists (rm_st4 st c g off n n' dst), (((c, off), n') :: bl_remove c BL), LS.
    split; [exact ES|]. split; [apply INVL_set_live; exact IR|]. cbn. rewrite LIVE, bl_remove_map. reflexivity.
Qed.

Theorem cmalloc_contract_proof2 : forall cs L n,
  creach2 cs L -> 0 <= n ->
  ctree_ok L (cmalloc cs n) (fun L' r => match snd r with Some c => ~ In c (ld_live L') | None => True end).
Proof.
  intros cs L n CR Hn. destruct (creach2_sim cs L CR) as (st & BL & LS & <- & INV & LIVE).
  apply (ctree_ok_paths _ L (fun _ _ => True)).
  - apply ptree_ctree_ok. eapply (ptree_strel (malloc_control pans0 pupd0 pans0_range st n tt)); [intros; exact I|].
    eapply ptree_mono; [intros; exact I|]. exact (ftree_prun pans0 pupd0 pans0_range (malloc st n) L _ tt (malloc_INVL st L BL LS n INV Hn)).
  - intros L' [cs' r] CP. destruct (cpath_follow _ _ _ _ CP) as (ans & Hf & HL).
    pose proof (strel_follow (malloc_control pans0 pupd0 pans0_range st n tt) ans) as SF. rewrite Hf in SF.
    destruct (follow (prun pans0 pupd0 tt (malloc st n)) ans) as [[o' [st' rf]]|] eqn:FF; [| destruct SF].
    destruct (malloc_sim pans0 pupd0 pans0_range st L BL LS n tt ans o' st' rf INV Hn FF) as (rc & Hf2 & _ & LIVE' & _ & RES).
    rewrite Hf in Hf2. inversion Hf2. subst cs' r. cbn [snd]. rewrite HL in LIVE'.
    destruct rf as [pf|]; destruct rc as [c|]; try exact I; try (exfalso; exact RES).
    destruct RES as (off & LS' & _ & _ & _ & NI). rewrite LIVE', LIVE. exact NI.
Qed.

Theorem cfree_contract_proof2 : forall cs L c,
  creach2 cs L -> In c (ld_live L) -> ctree_ok L (cfree cs (Some c)) (fun _ _ => True).
Proof.
  intros cs L c CR Hc. destruct (creach2_sim cs L CR) as (st & BL & LS & <- & INV & LIVE).
  rewrite LIVE in Hc. destruct (In_bslot _ _ Hc) as (off & n & Hk).
  apply ptree_ctree_ok.
  eapply (ptree_strel (free_control pans0 pupd0 st (aadd c (UNIT * off)) c tt (INVL_hdr_ok pans0 pupd0 st L BL LS c off n INV Hk))); [intros; exact I|].
  eapply ptree_mono; [intros; exact I|]. exact (ftree_prun pans0 pupd0 pans0_range _ L _ tt (free_INVL_closed st L BL LS c off n INV Hk)).
Qed.
