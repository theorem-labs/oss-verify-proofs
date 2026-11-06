(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool Lia.
From stdpp Require Import gmap.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Spec Require Import STree Malloc MallocCtrl KInv MI_Tree MI_Inv MI_Kit MI_Geom MI_List MI_Ext
  MI_Pres2 MI_WFree2 MI_WNtf2 MI_TF2 MI_WSlot MI_WMalloc MI_Sim MI_Contracts.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Section RC__1.
Context {RC__ : OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.RunCeiling.RunCeiling}.
Lemma SIMREL_init resv : SIMREL (strip (minit rc_secret resv)) (led_init resv).   (* [comment removed for export] *)
Proof. exists (minit rc_secret resv), [], (fun _ => []). split; [reflexivity|]. split; [apply INVL_init; exact rc_secret_range| reflexivity]. Qed.

(* [comment removed for export] *)
Theorem SIMREL_malloc cs L n L' cs' r :
  SIMREL cs L -> 0 <= n -> cpath L (cmalloc cs n) L' (cs', r) ->
  SIMREL cs' (match r with Some c => set_live (c :: ld_live L') L' | None => L' end)
  /\ match r with Some c => ~ In c (ld_live L') | None => True end.
Proof.
  intros (st & BL & LS & <- & INV & LIVE) Hn CP.
  destruct (cpath_follow _ _ _ _ CP) as (ans & Hf & HL).
  pose proof (strel_follow (malloc_control pans0 pupd0 pans0_range st n tt) ans) as SF. rewrite Hf in SF.
  destruct (follow (prun pans0 pupd0 tt (malloc st n)) ans) as [[o' [st' rf]]|] eqn:FF; [| destruct SF].
  destruct (malloc_sim pans0 pupd0 pans0_range st L BL LS n tt ans o' st' rf INV Hn FF) as (rc & Hf2 & _ & LIVE' & _ & RES).
  rewrite Hf in Hf2. inversion Hf2. subst cs' r. rewrite HL in RES, LIVE'.
  destruct rf as [pf|]; destruct rc as [c|]; try (exfalso; exact RES).
  - destruct RES as (off & LS' & Epf & Hoff & INV' & NI). split.
    + exists st', (((c, off), n) :: BL), LS'. split; [reflexivity|]. split; [apply INVL_set_live; exact INV'|]. cbn. rewrite LIVE', LIVE. reflexivity.
    + rewrite LIVE', LIVE. exact NI.
  - destruct RES as (LS' & INV'). split; [|exact I]. exists st', BL, LS'. split; [reflexivity|]. split; [exact INV'|]. rewrite LIVE'. exact LIVE.
Qed.

(* [comment removed for export] *)
Theorem SIMREL_free cs L c L' cs' :
  SIMREL cs L -> In c (ld_live L) -> cpath L (cfree cs (Some c)) L' cs' ->
  SIMREL cs' (set_live (ap_remove c (ld_live L')) L').
Proof.
  intros (st & BL & LS & <- & INV & LIVE) Hc CP.
  rewrite LIVE in Hc. destruct (In_bslot _ _ Hc) as (off & n & Hk).
  destruct (cpath_follow _ _ _ _ CP) as (ans & Hf & HL).
  pose proof (strel_follow (free_control pans0 pupd0 st (aadd c (UNIT * off)) c tt (INVL_hdr_ok pans0 pupd0 st L BL LS c off n INV Hk)) ans) as SF.
  rewrite Hf in SF.
  destruct (follow (prun pans0 pupd0 tt (free st (Some (aadd c (UNIT * off))))) ans) as [[o' st']|] eqn:FF; [| destruct SF].
  destruct (free_sim pans0 pupd0 pans0_range st L BL LS c off n tt ans o' st' INV Hk FF) as (Hf2 & _ & LIVE' & LS' & INV').
  rewrite Hf in Hf2. inversion Hf2. subst cs'. rewrite HL in INV', LIVE'.
  exists st', (bl_remove c BL), LS'. split; [reflexivity|]. split; [apply INVL_set_live; exact INV'|]. cbn. rewrite LIVE', LIVE. symmetry. apply bl_remove_map.
Qed.

(* [comment removed for export] *)
Theorem cmalloc_contract_sim cs L n :
  SIMREL cs L -> 0 <= n ->
  ctree_ok L (cmalloc cs n) (fun L' r => match snd r with Some c => ~ In c (ld_live L') | None => True end).
Proof.
  intros (st & BL & LS & <- & INV & LIVE) Hn.
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

Theorem cfree_contract_sim cs L c :
  SIMREL cs L -> In c (ld_live L) -> ctree_ok L (cfree cs (Some c)) (fun _ _ => True).
Proof.
  intros (st & BL & LS & <- & INV & LIVE) Hc.
  rewrite LIVE in Hc. destruct (In_bslot _ _ Hc) as (off & n & Hk).
  apply ptree_ctree_ok.
  eapply (ptree_strel (free_control pans0 pupd0 st (aadd c (UNIT * off)) c tt (INVL_hdr_ok pans0 pupd0 st L BL LS c off n INV Hk))); [intros; exact I|].
  eapply ptree_mono; [intros; exact I|]. exact (ftree_prun pans0 pupd0 pans0_range _ L _ tt (free_INVL_closed st L BL LS c off n INV Hk)).
Qed.
End RC__1.
