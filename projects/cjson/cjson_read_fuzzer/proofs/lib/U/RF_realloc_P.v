(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import Tac Image ZBridge.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U Require Export UImg.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared Require Import MallocRep MallocTree MallocFacts_A MallocFacts_B.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require Import Malloc MallocCtrl KInv MI_Inv MI_Kit.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U Require Import RMallocRep.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require Import MI_WRemap.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U Require RMallocKit_A2.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.RMallocKit_A2.RF_realloc_K2.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope Z_scope.

From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib Require Import SspGuard.
(* [comment removed for export] *)
From Stdlib Require Import Zify Lia.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require HeapLiaImp.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.HeapLiaImp.HeapLia.
Local Ltac Lia.lia ::= heap_lia.

(* [comment removed for export] *)
Section CeilWrap.
Context {ACEIL : Ceil} {AGRD : Guard}.


Lemma rr_ptrs_intro st LB0 L BL LS b g r m :
  CINV st LB0 -> INVL x0 st L BL LS -> rmrep st m ->
  hosts st b g -> 48 <= m_sizeclass (MR st g) ->
  s_regions st !! (fst b) = Some r -> r_kind r = RKGroup -> snd b = 0 ->
  rr_ptrs (fst b) g st.
Proof using .
  intros C INV MRP Hg Hsc Hr Kr Hb0.
  pose proof MRP as (WF & _). pose proof WF as (_ & WR & DJ & WA & WG).
  pose proof (ci_links _ _ C) as CL. pose proof (ci_heads _ _ C) as CH. pose proof (ci_mp _ _ C) as (MP1 & MP2 & MP3 & MP4 & MP5).
  assert (Eb : b = (fst b, 0)) by (destruct b as [q o]; cbn in Hb0 |- *; subst; reflexivity).
  (* [comment removed for export] *)
  assert (MS : forall q, meta_slot st q -> fst q <> fst b).
  { intros q (a & ar & k & Ha & Hk & ->) E. unfold aadd in E. cbn [fst] in E.
    destruct (WA a ar Ha) as (ra' & Hra & _ & _ & _ & NK & _). rewrite E, Hr in Hra. injection Hra as <-. exact (NK Kr). }
  assert (NG : forall o, ng_ptr st o -> optr_in (fun x => x <> fst b) o).
  { intros [q|] H; cbn in H |- *; [| exact I]. destruct H as (rq & Hq & NK). intros E. rewrite E, Hr in Hq. injection Hq as <-. exact (NK Kr). }
  unfold rr_ptrs. cbv zeta.
  split. { destruct (c_free_meta_head (ctx st)) as [h|] eqn:FH; cbn; [| exact I].
           destruct (ch_free _ CH h FH) as [NX _]. apply MS. apply (cl_self _ CL). exact NX. }
  split; [apply NG; exact MP1|]. split; [apply NG; exact MP2|]. split; [apply NG; exact MP3|]. split; [apply NG; exact MP4|].
  split. { intros sc. destruct (active st sc) as [a|] eqn:HA; cbn; [| exact I].
           destruct (ch_active _ CH sc a HA) as (_ & NX & _). apply MS. apply (cl_self _ CL). exact NX. }
  split. { destruct (c_brk (ctx st)) as [| |rid boff] eqn:HB; try exact I.
           destruct (ci_bk _ _ C rid boff HB) as (rb & Hrb & Kb). intros E. rewrite E, Hr in Hrb. injection Hrb as <-. rewrite Kr in Kb. discriminate. }
  split. { intros q. split; [| split].
    - destruct (m_prev (get_meta_rec st q)) as [pv|] eqn:HP; cbn; [| exact I]. destruct (cl_prev _ CL q pv HP) as [_ M]. apply MS. exact M.
    - destruct (m_next (get_meta_rec st q)) as [nx|] eqn:HN; cbn; [| exact I]. destruct (cl_next _ CL q nx HN) as [_ M]. apply MS. exact M.
    - intros b' Hm E. pose proof (ci_memh _ _ C q b' Hm) as HH.
      destruct (alone x0 st L BL LS INV g b Hg Hsc b' q HH E) as [-> ->]. split; [reflexivity| exact Eb]. }
  split. { intros a ar Ha. split.
    - destruct (WA a ar Ha) as (ra' & Hra & _ & _ & _ & NK & _). intros E. rewrite E, Hr in Hra. injection Hra as <-. exact (NK Kr).
    - apply NG. exact (MP5 a ar Ha). }
  intros b' gh Hb'. split.
  - destruct (ci_grps _ _ C b' gh Hb') as (g' & Hg' & _). rewrite Hg'. cbn.
    assert (HH : hosts st b' g'). { exists (g_active_idx gh). rewrite Hb'. destruct gh as [gm ai]; cbn in Hg' |- *. subst. reflexivity. }
    apply MS. exact (go_slot _ _ _ (ci_gmetas _ _ C b' g' HH)).
  - intros E. destruct (ci_grps _ _ C b' gh Hb') as (g' & Hg' & _).
    assert (HH : hosts st b' g'). { exists (g_active_idx gh). rewrite Hb'. destruct gh as [gm ai]; cbn in Hg' |- *. subst. reflexivity. }
    destruct (alone x0 st L BL LS INV g b Hg Hsc b' g' HH E) as [-> ->]. exact Eb.
Qed.


End CeilWrap.
