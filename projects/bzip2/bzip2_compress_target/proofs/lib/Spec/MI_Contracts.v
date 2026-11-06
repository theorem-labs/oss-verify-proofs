(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Lia. Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From Stdlib Require Import ZArith NArith List Bool Lia.
From stdpp Require Import gmap.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Spec Require Import STree Malloc MallocCtrl KInv MI_Tree MI_Inv MI_Kit MI_Geom MI_List MI_Ext
  MI_Pres2 MI_WFree2 MI_WNtf2 MI_TF2 MI_WSlot MI_WMalloc MI_Sim.
Import ListNotations.
Local Open Scope Z_scope.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeil.
(* [comment removed for export] *)
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import CpsOpen.
Section ACeilS1. Context {ACEIL__ : ACeil}.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

Lemma INVL_set_live X st L BL LS v : INVL X st L BL LS -> INVL X st (set_live v L) BL LS.
Proof.
  cps_intros (IR & IA & IM & IL & IG & IS & ISH). split; [| split; [exact IA| split; [exact IM| split; [exact IL| split; [exact IG| split; [exact IS| exact ISH]]]]]].
  destruct IR; constructor; cbn; auto.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma cpath_follow {R} L (t : M R) L' r : cpath L t L' r -> exists ans, follow t ans = Some r /\ lafter L t ans = L'.
Proof.
  induction 1 as [L0 r0|L0 e k z L1 r0 Hz Hp IH].
  - exists []. split; reflexivity.
  - cps_destruct IH as (ans & Hf & Hl). exists (z :: ans).
    destruct e; cbn [follow lafter]; try (split; [exact Hf| exact Hl]). cbn in Hz. discriminate.
Qed.

(* [comment removed for export] *)
Lemma ctree_ok_paths {R} : forall (t : M R) L (P1 P2 : mled -> R -> Prop),
  ctree_ok L t P1 -> (forall L' r, cpath L t L' r -> P2 L' r) -> ctree_ok L t P2.
Proof.
  induction t as [r|e k IH]; intros L P1 P2 H HP; cbn [ctree_ok] in *.
  - apply HP. constructor.
  - destruct H as [He Hk]. split; [exact He|]. intros z Hz. apply (IH z _ P1); [apply Hk; exact Hz|].
    intros L' r Hp. apply HP. econstructor; eauto.
Qed.

Lemma bl_remove_map c BL : map bslot (bl_remove c BL) = ap_remove c (map bslot BL).
Proof.
  induction BL as [|k BL IH]; cbn; [reflexivity|]. destruct (aptr_eqb_spec (bslot k) c) as [E|NE]; [reflexivity|]. cbn. rewrite IH. reflexivity.
Qed.

Lemma In_bslot c BL : In c (map bslot BL) -> exists off n, In ((c, off), n) BL.
Proof.
  intros H. apply in_map_iff in H as ([[c' off] n] & E & Hin). cbn in E. subst c'. exists off, n. exact Hin.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition pans0 (_ : unit) (_ : aptr) (_ _ : Z) : Z := 0.
Definition pupd0 (o : unit) (_ : ev) (_ : Z) : unit := o.
Lemma pans0_range : forall o p c h, 0 <= pans0 o p c h < 256.
Proof. intros. unfold pans0. lia. Qed.

Definition SIMREL (cs : mstate) (L : mled) : Prop :=
  exists st BL LS, strip st = cs /\ INVL x0 st L BL LS /\ ld_live L = map bslot BL.

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma simrel_malloc cs L n L' cs' r :
  SIMREL cs L -> 0 <= n -> cpath L (cmalloc cs n) L' (cs', r) ->
  SIMREL cs' (match r with Some c => set_live (c :: ld_live L') L' | None => L' end).
Proof.
  intros IH Hn CP. cps_destruct IH as (st & BL & LS & <- & INV & LIVE).
    cps_destruct (cpath_follow _ _ _ _ CP) as (ans & Hf & HL).
    pose proof (strel_follow (malloc_control pans0 pupd0 pans0_range st n tt) ans) as SF. rewrite Hf in SF.
    destruct (follow (prun pans0 pupd0 tt (malloc st n)) ans) as [[o' [st' rf]]|] eqn:FF; [| destruct SF].
    cps_destruct (malloc_sim pans0 pupd0 pans0_range st L BL LS n tt ans o' st' rf INV Hn FF) as (rc & Hf2 & _ & LIVE' & _ & RES).
    rewrite Hf in Hf2. inversion Hf2. subst cs' r. rewrite HL in RES, LIVE'.
    destruct rf as [pf|]; destruct rc as [c|]; try (exfalso; exact RES).
    + cps_destruct RES as (off & LS' & Epf & Hoff & INV' & NI).
      exists st', (((c, off), n) :: BL), LS'. split; [reflexivity|]. split; [apply INVL_set_live; exact INV'|]. cbn. rewrite LIVE', LIVE. reflexivity.
    + destruct RES as (LS' & INV'). exists st', BL, LS'. split; [reflexivity|]. split; [exact INV'|]. rewrite LIVE'. exact LIVE.
Qed.

Lemma simrel_free cs L c L' cs' :
  SIMREL cs L -> In c (ld_live L) -> cpath L (cfree cs (Some c)) L' cs' ->
  SIMREL cs' (set_live (ap_remove c (ld_live L')) L').
Proof.
  intros IH Hc CP. cps_destruct IH as (st & BL & LS & <- & INV & LIVE).
    rewrite LIVE in Hc. cps_destruct (In_bslot _ _ Hc) as (off & n & Hk).
    cps_destruct (cpath_follow _ _ _ _ CP) as (ans & Hf & HL).
    pose proof (strel_follow (free_control pans0 pupd0 st (aadd c (UNIT * off)) c tt (INVL_hdr_ok pans0 pupd0 st L BL LS c off n INV Hk)) ans) as SF.
    rewrite Hf in SF.
    destruct (follow (prun pans0 pupd0 tt (free st (Some (aadd c (UNIT * off))))) ans) as [[o' st']|] eqn:FF; [| destruct SF].
    cps_destruct (free_sim pans0 pupd0 pans0_range st L BL LS c off n tt ans o' st' INV Hk FF) as (Hf2 & _ & LIVE' & LS' & INV').
    rewrite Hf in Hf2. inversion Hf2. subst cs'. rewrite HL in INV', LIVE'.
    exists st', (bl_remove c BL), LS'. split; [reflexivity|]. split; [apply INVL_set_live; exact INV'|]. cbn. rewrite LIVE', LIVE. symmetry. apply bl_remove_map.
Qed.

Theorem cmalloc_contract_sim : forall cs L n,
  SIMREL cs L -> 0 <= n ->
  ctree_ok L (cmalloc cs n) (fun L' r => match snd r with Some c => ~ In c (ld_live L') | None => True end).
Proof.
  intros cs L n CR Hn. cps_destruct CR as (st & BL & LS & <- & INV & LIVE).
  apply (ctree_ok_paths _ L (fun _ _ => True)).
  - apply ptree_ctree_ok. eapply (ptree_strel (malloc_control pans0 pupd0 pans0_range st n tt)); [intros; exact I|].
    eapply ptree_mono; [intros; exact I|]. exact (ftree_prun pans0 pupd0 pans0_range (malloc st n) L _ tt (malloc_INVL st L BL LS n INV Hn)).
  - intros L' [cs' r] CP. cps_destruct (cpath_follow _ _ _ _ CP) as (ans & Hf & HL).
    pose proof (strel_follow (malloc_control pans0 pupd0 pans0_range st n tt) ans) as SF. rewrite Hf in SF.
    destruct (follow (prun pans0 pupd0 tt (malloc st n)) ans) as [[o' [st' rf]]|] eqn:FF; [| destruct SF].
    cps_destruct (malloc_sim pans0 pupd0 pans0_range st L BL LS n tt ans o' st' rf INV Hn FF) as (rc & Hf2 & _ & LIVE' & _ & RES).
    rewrite Hf in Hf2. inversion Hf2. subst cs' r. cbn [snd]. rewrite HL in LIVE'.
    destruct rf as [pf|]; destruct rc as [c|]; try exact I; try (exfalso; exact RES).
    cps_destruct RES as (off & LS' & _ & _ & _ & NI). rewrite LIVE', LIVE. exact NI.
Qed.

Theorem cfree_contract_sim : forall cs L c,
  SIMREL cs L -> In c (ld_live L) -> ctree_ok L (cfree cs (Some c)) (fun _ _ => True).
Proof.
  intros cs L c CR Hc. cps_destruct CR as (st & BL & LS & <- & INV & LIVE).
  rewrite LIVE in Hc. cps_destruct (In_bslot _ _ Hc) as (off & n & Hk).
  apply ptree_ctree_ok.
  eapply (ptree_strel (free_control pans0 pupd0 st (aadd c (UNIT * off)) c tt (INVL_hdr_ok pans0 pupd0 st L BL LS c off n INV Hk))); [intros; exact I|].
  eapply ptree_mono; [intros; exact I|]. exact (ftree_prun pans0 pupd0 pans0_range _ L _ tt (free_INVL_closed st L BL LS c off n INV Hk)).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

End ACeilS1.
