(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs, 2026-10: the GLUE facts of pj_set's image-B walk (fuzz_preset asan-ubsan, B 0x86e8c): the pure
   Props pjs_g_* / pjs_glue of lib/B/Prog/pj_set_defs.v.
   proves no function (kind: glue lemma). Pure facts over the tree model (Spec/PjTree.v), the reader's tree
   predicates (lib/A/PRH_Reader.v) and the allocator's live-set counts (lib/Reusable/YGcfRoomLive.v).
   - pjs_g_node_fd: a represented tree is freeable to its depth, and freeable is monotone in the depth: the
     image-free lib/Reusable/PjpTree.v (pjg_node_fd, pjg_fd_mono; blob 2f986242b094), cited.
   - pjs_g_depth_mem: a member of an object is one level below it (PjTree.depth's list_max).
   - pjs_g_model_hit / pjs_g_model_miss: pj_set_model replaces the first member whose key is equal, and appends
     when there is none (PjTree.v:40-44), by induction on the member list.
   - pjs_g_trace_len: the request list of pj_set's absent arm has three events when n = cap and one otherwise.
   - pjs_g_counts_swap / pjs_g_counts_eq: sec_cnt and ccnt24 (YGcfRoomLive.v:1139, :1167) count a FILTER of the
     live requests, so they ride a permutation of the block list and grow by at most the number of blocks added.
     They are what the fuzz_strdup call needs after grow has swapped the two slot blocks.
   - pjs_g_ab_snd: the allocator's block list and cgif's ablocks have the same sizes (ablocks maps the address only).
   - pjs_hull_nil / pjs_hull_mal / pjs_hull_grow: the hull budgets pj_set's callees ask (the kit's tpj_free_specX: the empty
     list; tfuzz_strdup_specX: one malloc; tgrow_specX: grow's prhPg_evs), from a run position by pj_set_defs.v's
     pjs_g_hull: each list is within one call's counts (A17's NCALL / TCALL), every request being at most
     cf_malloc_max <= 2 ^ 30 (lib/Spec/PresetSecTotalRun.v sec_req_lo / sec_map_size_le bound one secondary's map).
   Numerals: 56 / 8 (LENGTH: the struct pj and a key pointer), in the cited predicates; 2 ^ 30 (LENGTH: the request
   bound of pjs_g_hull).
   No ADDRESS. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn YP0b YP0a.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YN3v YI04 YI00 YG0s YP07 YI16.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YG0p YCbqG FCiface YGcallMx.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfNames YGcfRoomKeep YG0dcf YGcfRoomPre.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK0o YK06.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcfRoomLive.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0d YP0c YC80 YPsym YC4aP YImgTop.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Ledger ReaderRes.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PjTree PjGrammar PresetRoom.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PresetRoomPos PresetReqAt PresetHullBudget
  PresetSecTotal PresetSecTotalRun.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Base PRH_Reader PRH_Charge PRH_FnReader.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_FnPj.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B Require Import Img0 Listing_prog PAImg_prog PRH_ImgB.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require PjpTree.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require Import pj_set_defs.
Import ListNotations.
Local Open Scope Z_scope.
#[local] Existing Instance prh_img_B.

(* ---- a filter's length rides a permutation (this unit's imports resolve the bare name `filter` to stdpp's class method, so the
   list filter is named List.filter here and its two defining equations are rewritten with) ---- *)
Lemma pjs_filter_nil : forall (A : Type) (f : A -> bool), List.filter f [] = [].
Proof. intros A f. reflexivity. Qed.
Lemma pjs_filter_cons : forall (A : Type) (f : A -> bool) x l,
  List.filter f (x :: l) = if f x then x :: List.filter f l else List.filter f l.
Proof. intros A f x l. reflexivity. Qed.

Lemma pjs_perm_filter : forall (A : Type) (f : A -> bool) l1 l2,
  Permutation l1 l2 -> Permutation (List.filter f l1) (List.filter f l2).
Proof.
  intros A f l1 l2 H. induction H as [| x l1 l2 H IH | x y l | l1 l2 l3 H1 IH1 H2 IH2].
  - apply Permutation_refl.
  - rewrite !pjs_filter_cons. destruct (f x); [apply perm_skip; exact IH | exact IH].
  - rewrite !pjs_filter_cons. destruct (f x) eqn:Ex; destruct (f y) eqn:Ey; try apply Permutation_refl.
    apply perm_swap.
  - exact (Permutation_trans IH1 IH2).
Qed.

Lemma pjs_filter_len_perm : forall (A : Type) (f : A -> bool) l1 l2,
  Permutation l1 l2 -> length (List.filter f l1) = length (List.filter f l2).
Proof. intros A f l1 l2 H. exact (Permutation_length (pjs_perm_filter A f l1 l2 H)). Qed.

Lemma pjs_filter_app_len : forall (A : Type) (f : A -> bool) l1 l2,
  length (List.filter f (l1 ++ l2)) = (length (List.filter f l1) + length (List.filter f l2))%nat.
Proof.
  intros A f l1 l2. induction l1 as [|x l1 IH].
  - rewrite pjs_filter_nil. cbn [app length]. lia.
  - cbn [app]. rewrite !pjs_filter_cons. destruct (f x); cbn [length]; lia.
Qed.

Lemma pjs_filter_le : forall (A : Type) (f : A -> bool) l, (length (List.filter f l) <= length l)%nat.
Proof.
  intros A f l. induction l as [|x l IH]; [rewrite pjs_filter_nil; cbn [length]; lia|].
  rewrite pjs_filter_cons. destruct (f x); cbn [length]; lia.
Qed.


(* ---- the eight Props ---- *)

Lemma pjsg_node_fd : pjs_g_node_fd.
Proof.
  intros segs m lblk t p D n H Hd.
  exact (PjpTree.pjg_fd_mono segs m lblk (PjTree.depth t) n p D Hd (PjpTree.pjg_node_fd segs t m lblk p D H)).
Qed.

Lemma pjsg_depth_mem : pjs_g_depth_mem.
Proof.
  intros ms i nm v dd Hnth Hd.
  assert (Hin : In (PjTree.depth v) (map (fun x : list Z * PjTree.jv => let '(_, u) := x in PjTree.depth u) ms)).
  { apply in_map_iff. exists (nm, v). split; [reflexivity|]. exact (nth_error_In _ _ Hnth). }
  cbn [PjTree.depth] in Hd.
  assert (Hle : (list_max (map (fun x : list Z * PjTree.jv => let '(_, u) := x in PjTree.depth u) ms) <= dd)%nat)
    by lia.
  pose proof (proj1 (list_max_le _ dd) Hle) as HF.
  exact (proj1 (Forall_forall _ _) HF _ Hin).
Qed.

Lemma pjsg_model_hit : pjs_g_model_hit.
Proof.
  intros ms. induction ms as [|[k0 v0] r IH]; intros i kname vi tv Hnth Hlt.
  - destruct i; discriminate Hnth.
  - destruct i as [|j]; cbn [nth_error] in Hnth.
    + injection Hnth as E1 E2. subst k0 v0.
      cbn [PjTree.pj_set_model firstn skipn app].
      destruct (list_eq_dec Z.eq_dec kname kname) as [_|Hne]; [reflexivity | exfalso; exact (Hne eq_refl)].
    + assert (Hk0 : k0 <> kname) by (apply (Hlt 0%nat k0 v0); [lia | reflexivity]).
      cbn [PjTree.pj_set_model].
      destruct (list_eq_dec Z.eq_dec k0 kname) as [E|_]; [exfalso; exact (Hk0 E)|].
      rewrite (IH j kname vi tv Hnth); [reflexivity|].
      intros j' nm u Hj' Hnth'. exact (Hlt (S j') nm u ltac:(lia) Hnth').
Qed.

Lemma pjsg_model_miss : pjs_g_model_miss.
Proof.
  intros ms. induction ms as [|[k0 v0] r IH]; intros kname tv Hni; cbn [PjTree.pj_set_model app]; [reflexivity|].
  cbn [map fst In] in Hni.
  destruct (list_eq_dec Z.eq_dec k0 kname) as [E|_]; [exfalso; apply Hni; left; exact E|].
  rewrite IH; [reflexivity|]. intros Hin. apply Hni. right. exact Hin.
Qed.

Lemma pjsg_trace_len : pjs_g_trace_len.
Proof.
  intros n cap kname. unfold prhPj_set_trace.
  destruct (n =? cap); cbn [app length]; reflexivity.
Qed.

Lemma pjsg_counts_swap : pjs_g_counts_swap.
Proof.
  intros S1 S2 a b c H1 H2. unfold YGcfRoomLive.sec_cnt, YGcfRoomLive.ccnt24, PresetRoom.ccnt.
  rewrite (pjs_filter_len_perm _ _ _ _ H1), (pjs_filter_len_perm _ _ _ _ H2),
    (pjs_filter_len_perm _ (PresetRoom.in_cls kBatchClass) _ _ H1),
    (pjs_filter_len_perm _ (PresetRoom.in_cls kBatchClass) _ _ H2),
    !pjs_filter_app_len.
  pose proof (pjs_filter_le _ YGcfRoomLive.rl_sec_req b) as Lb.
  pose proof (pjs_filter_le _ (PresetRoom.in_cls kBatchClass) b) as Lb2.
  split; lia.
Qed.

Lemma pjsg_counts_eq : pjs_g_counts_eq.
Proof.
  intros S1 S2 H. unfold YGcfRoomLive.sec_cnt, YGcfRoomLive.ccnt24, PresetRoom.ccnt.
  rewrite (pjs_filter_len_perm _ _ _ _ H), (pjs_filter_len_perm _ (PresetRoom.in_cls kBatchClass) _ _ H).
  split; reflexivity.
Qed.

Lemma pjsg_ab_snd : pjs_g_ab_snd.
Proof. intros B ly S. unfold ablocks. rewrite map_map. reflexivity. Qed.


(* ---- every block of a represented tree is a block of the ledger list (the lblk the node is stated over): the
   induction the segments need to put a tree's footprint below the allocator ceiling. Transcribed in the shape of
   pj_parse_glue.v's PjpTree lemmas (pjg_items_pf / pjg_mems_pf), over pj_nodeR instead of pj_fdR ---- *)
Module PjsBlk.
Import PjTree.
Section blk.
Variable segs : list Segment.

Lemma pjsb_items : forall m lblk (l : list jv) a D,
  pj_itemsR (pj_nodeR segs m lblk) a l D ->
  (forall u, In u l -> forall p D1 x k, pj_nodeR segs m lblk p u D1 -> In (x, k) D1 -> lblk x k) ->
  forall x k, In (x, k) D -> lblk x k.
Proof.
  intros m lblk l. induction l as [|u r IH]; intros a D HD HI x k Hin; cbn [pj_itemsR] in HD.
  - subst D. destruct Hin.
  - destruct HD as (D1 & D2 & -> & HP & HR). apply in_app_iff in Hin as [Hin | Hin].
    + exact (HI u ltac:(left; reflexivity) a D1 x k HP Hin).
    + apply (IH (a + 56) D2 HR); [|exact Hin].
      intros u' Hu' p D' x' k' HP' Hin'. exact (HI u' ltac:(right; exact Hu') p D' x' k' HP' Hin').
Qed.

Lemma pjsb_mems : forall m lblk (l : list (list Z * jv)) a ka D,
  pj_memsR segs m lblk (pj_nodeR segs m lblk) a ka l D ->
  (forall nm u, In (nm, u) l -> forall p D1 x k, pj_nodeR segs m lblk p u D1 -> In (x, k) D1 -> lblk x k) ->
  forall x k, In (x, k) D -> lblk x k.
Proof.
  intros m lblk l. induction l as [|[nm u] r IH]; intros a ka D HD HI x k Hin; cbn [pj_memsR] in HD.
  - subst D. destruct Hin.
  - destruct HD as (y & ky & D1 & D2 & -> & Hy & (Hlb & _ & _) & HP & HR).
    destruct Hin as [Heq | Hin].
    + injection Heq as <- <-. exact Hlb.
    + apply in_app_iff in Hin as [Hin | Hin].
      * exact (HI nm u ltac:(left; reflexivity) a D1 x k HP Hin).
      * apply (IH (a + 56) (ka + 8) D2 HR); [|exact Hin].
        intros nm' u' Hu' p D' x' k' HP' Hin'. exact (HI nm' u' ltac:(right; exact Hu') p D' x' k' HP' Hin').
Qed.

Lemma pjsb_node : forall t m lblk p D, pj_nodeR segs m lblk p t D -> forall x k, In (x, k) D -> lblk x k.
Proof.
  intros t. induction t as [| | | txt bits | sv | items IH | members IH] using jv_ind';
    intros m lblk p D H x k Hin; cbn [pj_nodeR] in H.
  - destruct H as (_ & _ & num & str & kids & keys & nn & cap & _ & _ & _ & _ & _ & _ & ->). destruct Hin.
  - destruct H as (_ & _ & num & str & kids & keys & nn & cap & _ & _ & _ & _ & _ & _ & ->). destruct Hin.
  - destruct H as (_ & _ & num & str & kids & keys & nn & cap & _ & _ & _ & _ & _ & _ & ->). destruct Hin.
  - destruct H as (_ & _ & num & str & kids & keys & nn & cap & _ & _ & _ & _ & _ & _ & kk & (Hlb & _ & _) & ->).
    destruct Hin as [Heq | []]. injection Heq as <- <-. exact Hlb.
  - destruct H as (_ & _ & num & str & kids & keys & nn & cap & _ & _ & _ & _ & _ & kk & (Hlb & _ & _) & ->).
    destruct Hin as [Heq | []]. injection Heq as <- <-. exact Hlb.
  - destruct H as (_ & _ & num & str & kids & keys & nn & cap & _ & _ & _ & _ & _ & Hcap & Di & -> & Hi).
    apply in_app_iff in Hin as [Hin | Hin].
    + destruct (Z.eqb_spec cap 0) as [-> | Hne]; [destruct Hin|].
      destruct Hin as [Heq | []]. injection Heq as <- <-.
      destruct Hcap as [(Hc & _) | (_ & Hl)]; [lia | exact Hl].
    + apply (pjsb_items m lblk items kids Di Hi); [|exact Hin].
      intros u Hu p' D' x' k' HP' Hin'. rewrite Forall_forall in IH.
      exact (IH u Hu m lblk p' D' HP' x' k' Hin').
  - destruct H as (_ & _ & num & str & kids & keys & nn & cap & _ & _ & _ & _ & Hcap & Di & -> & Hi).
    apply in_app_iff in Hin as [Hin | Hin].
    + destruct (Z.eqb_spec cap 0) as [-> | Hne]; [destruct Hin|].
      destruct Hcap as [(Hc & _ & _) | (_ & L0 & L1)]; [lia|].
      destruct Hin as [Heq | [Heq | []]]; injection Heq as <- <-; [exact L0 | exact L1].
    + apply (pjsb_mems m lblk members kids keys Di Hi); [|exact Hin].
      intros nm u Hu p' D' x' k' HP' Hin'. rewrite Forall_forall in IH.
      specialize (IH (nm, u) Hu). cbn [snd] in IH. exact (IH m lblk p' D' HP' x' k' Hin').
Qed.
End blk.
End PjsBlk.

(* ---- the ledger sum over an append and a permutation (Ledger.v states none) ---- *)
Lemma pjs_lsum_app : forall l1 l2, Ledger.lsum (l1 ++ l2) = Ledger.lsum l1 + Ledger.lsum l2.
Proof.
  intros l1 l2. induction l1 as [|[a k] l1 IH]; cbn [app Ledger.lsum]; [reflexivity|]. rewrite IH. lia.
Qed.
Lemma pjs_lsum_perm : forall l1 l2, Permutation l1 l2 -> Ledger.lsum l1 = Ledger.lsum l2.
Proof.
  intros l1 l2 H. induction H as [| [a k] l1 l2 H IH | [a k] [b m] l | l1 l2 l3 H1 IH1 H2 IH2];
    cbn [Ledger.lsum]; [reflexivity | lia | lia | lia].
Qed.

Theorem pjs_glue_holds {ci : CfImg} {cp : CfParams} : @pjs_glue ci cp.
Proof.
  split; [exact pjsg_node_fd|]. split; [exact pjsg_depth_mem|]. split; [exact pjsg_model_hit|].
  split; [exact pjsg_model_miss|]. split; [exact pjsg_trace_len|]. split; [exact pjsg_counts_swap|].
  split; [exact pjsg_counts_eq | exact pjsg_ab_snd].
Qed.

(* ---- THE HULL BUDGETS of pj_set's callees, from a run position (pjs_g_hull) ---- *)
Section hull. Context {cp : CfParams}.
(* one allocator event of request at most 2 ^ 30 counts at most one secondary and at most its map *)
Lemma pjs_hull_ev : forall e, (exists m r, (e = PresetReqAt.HMal r \/ e = PresetReqAt.HRe m r) /\ 0 <= r <= 2 ^ 30) ->
  (PresetSecTotal.nsec [e] <= 1)%nat /\ PresetSecTotal.tsec [e] <= 2 ^ 30 + PresetSecTotal.SEC_MAP_OVH.
Proof.
  intros e (m & r & He & Hr).
  assert (N : (PresetSecTotal.nsec [e] = PresetSecTotal.nsec [PresetReqAt.HMal r])%nat /\
    PresetSecTotal.tsec [e] = PresetSecTotal.tsec [PresetReqAt.HMal r]).
  { destruct He as [-> | ->]; [split; reflexivity |].
    split; [exact (PresetHullBudget.hull_nsec_re m r) | exact (PresetHullBudget.hull_tsec_re m r)]. }
  destruct N as [-> ->]. rewrite PresetHullBudget.hull_nsec_mal, PresetHullBudget.hull_tsec_mal.
  unfold PresetSecTotal.SEC_MAP_OVH.
  destruct (YG00.from_primary r) eqn:E; cbv beta iota; [lia|].
  assert (L : 64513 <= r).
  { apply PresetSecTotalRun.sec_req_lo. change (negb (YG00.from_primary r) = true). rewrite E. reflexivity. }
  pose proof (PresetSecTotalRun.sec_map_size_le r L) as M. unfold PresetSecTotal.SEC_MAP_OVH in M. lia.
Qed.
Lemma pjs_hull_nil : pjs_g_hull -> forall sm x os i H0 hist S, (length os <= 4)%nat ->
  PresetRoomPos.iface_room_pos sm x os i H0 hist S -> PresetHullBudget.hull_budget S [].
Proof.
  intros [_ HP] sm x os i H0 hist S Hl Hpos. apply (HP sm x os i H0 hist S [] Hl Hpos).
  - rewrite PresetHullBudget.hull_nsec_nil, PresetSecTotal.NCALL_value. lia.
  - rewrite PresetHullBudget.hull_tsec_nil, PresetSecTotal.TCALL_value. lia.
Qed.
Lemma pjs_hull_mal : pjs_g_hull -> forall sm x os i H0 hist S, (length os <= 4)%nat ->
  PresetRoomPos.iface_room_pos sm x os i H0 hist S ->
  forall r, 0 <= r < cf_malloc_max -> PresetHullBudget.hull_budget S [PresetReqAt.HMal r].
Proof.
  intros [HM HP] sm x os i H0 hist S Hl Hpos r Hr.
  destruct (pjs_hull_ev (PresetReqAt.HMal r) ltac:(exists 0, r; split; [left; reflexivity | lia])) as [N T].
  apply (HP sm x os i H0 hist S _ Hl Hpos).
  - rewrite PresetSecTotal.NCALL_value. lia.
  - rewrite PresetSecTotal.TCALL_value. unfold PresetSecTotal.SEC_MAP_OVH in T. lia.
Qed.
Lemma pjs_hull_grow : pjs_g_hull -> forall sm x os i H0 hist S, (length os <= 4)%nat ->
  PresetRoomPos.iface_room_pos sm x os i H0 hist S ->
  forall n cap, 0 <= cap -> n <= cap -> (n = cap -> 56 * cap2R cap + cf_head < cf_malloc_max) ->
  PresetHullBudget.hull_budget S (prhPg_evs true n cap []).
Proof.
  intros HG sm x os i H0 hist S Hl Hpos n cap Hc Hnc Hmax.
  unfold prhPg_evs. destruct (n <? cap) eqn:En; [exact (pjs_hull_nil HG sm x os i H0 hist S Hl Hpos)|].
  apply Z.ltb_ge in En. specialize (Hmax ltac:(lia)).
  destruct HG as [HM HP]. pose proof (@cf_head_nonneg cp) as Hh.
  assert (Hc2 : 0 <= cap2R cap) by (unfold cap2R; destruct (cap =? 0); lia).
  assert (EV : forall k, 0 <= k <= 56 -> exists m r, (prhPg_ev k cap = PresetReqAt.HMal r \/
    prhPg_ev k cap = PresetReqAt.HRe m r) /\ 0 <= r <= 2 ^ 30).
  { intros k Hk. exists (k * cap + cf_head), (k * cap2R cap + cf_head). split; [|nia].
    unfold prhPg_ev. destruct (cap =? 0); [left | right]; reflexivity. }
  destruct (pjs_hull_ev _ (EV 56 ltac:(lia))) as [N1 T1].
  destruct (pjs_hull_ev _ (EV 8 ltac:(lia))) as [N2 T2].
  cbn [nth andb]. change [prhPg_ev 56 cap; prhPg_ev 8 cap] with ([prhPg_ev 56 cap] ++ [prhPg_ev 8 cap]).
  apply (HP sm x os i H0 hist S _ Hl Hpos).
  - rewrite PresetSecTotal.nsec_app, PresetSecTotal.NCALL_value. lia.
  - rewrite PresetSecTotal.tsec_app, PresetSecTotal.TCALL_value. unfold PresetSecTotal.SEC_MAP_OVH in T1, T2. lia.
Qed.
End hull.
