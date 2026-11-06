(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: restates text of projects/cgif/cgif_file_fuzzer/proofs/lib/A/AC9z.v:138-139
   [Apache-2.0]; projects/cgif/cgif_file_fuzzer/proofs/lib/A/ACer.v:148-161 [Apache-2.0];
   projects/cgif/cgif_file_fuzzer/proofs/lib/A/ACh5.v:99 [Apache-2.0]; projects/cgif/cgif_file_fuzzer/proofs/lib/A/ACja.v:107-117
   [Apache-2.0]; projects/cgif/cgif_file_fuzzer/proofs/lib/YC1f.v:367-369 [Apache-2.0 OR MIT];
   projects/cgif/cgif_file_fuzzer/proofs/lib/YC8w.v:289-290 [Apache-2.0 OR MIT], for libreac/fuzz_identity's ASan build
   (lib/A). The [Apache-2.0 OR MIT] text is used under Apache-2.0. The same text also appears in
   projects/cgif/cgif_file_fuzzer/proofs/lib/A/ACai.v:156-159. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_identity/lib/A/Prog/sb_dec_A.v, with its module paths and module names changed; 1279 of its 1357 lines of code are new or changed and 927 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-10: lib/B (fs.asan-ubsan) twin of lib/A/FSW_K.v from a working branch
   60d0985773d, same lemma names; imports point at lib/B's image files (YB1v, YB1w, YF0x, FSH_Base, FSH_Rt, FSPstat,
   FSH_Fn_reader and the other lib/B FSW files); the image-agnostic FSupoison, FSupoisonU, FSH_YC20, FSH_Gen stay lib/A's.
   rule 24: proves no function (kind: segment lemma). *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_state/lib/B/FSW_K.v; 249 of its 295 lines of code are new or changed and 1311 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-10: lib/B (fs.asan-ubsan) twin of lib/A/ZZwv_tree.v (a working branch
   1a5dc5b2e7c): same lemma names, statements and proofs; imports point at lib/B's image files (YB1v, YB1w) and walk
   kit (FSW_rd); the image-agnostic FSupoison, FSupoisonU, FSH_Gen stay lib/A's; FSH_Fn_reader is lib/B's (Required,
   used qualified: lib/B's FSH_Fn_writer states the root node with lib/B's FSH_Fn_reader.pobj).
   rule 24: proves no function (kind: segment lemma) - the container arms of write_value B.
   write_value's CONTAINER arms (array / object), fs.asan-ubsan image B: the TREE / MODEL facts the arms need about a
   `struct pj` node that holds an array or an object, and about the pieces the writer emits for it. No walk, no engine
   run, no function contract: this is a support file for lib/B/ZZwvB_comp.v / the container part of write_value
   (0x84010) against lib/B/FSH_Fn_writer.v's write_value_spec_at.
   The tree side (T1, T2) opens PjStruct.pj_node at JArr / JObj and splits pj_items / pj_mems at one index; the
   footprint side (T3, T4) moves PjStruct.pj_foot from a kid to its parent; T5 / T6 carry FSH_Gen.jv_plain and
   PjTree.depth down to an item; T7 names the two piece lists of WriterValue.wvpieces' container arms; T8 places a
   kid node for the recursive call (FSH_Fn_reader.pobj), over FSW_rd.fsw_block_body_addressable and AR's block law.
   Rule 24 (proof-index v5 built 2026-10-28, exit 0): write_value has RELEASED proofs for fs's PLAIN
   and UBSAN builds only (lib/Prog, lib/U/Prog), none for ASan; they are templates, not drop-ins. LOOKUP of the
   eighteen names below (`git grep -n -w`, output to a file, exit code from the command): parts (1) the four
   released refs and (2) the named live heads (fourteen working
   branches) plus this worktree's HEAD;
   no donor found in (1)-(3). The reusable parts of the two list splits are PjStruct's own pj_items_mono /
   pj_mems_mono shape (lib/Prog/PjStruct.v:264-304), followed here. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00 YI0n.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YI16 YK06 YM05 YG0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YG0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require Import FSupoison FSupoisonU FSH_Gen.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B Require Import YB1v YB1w FSW_rd.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B Require FSH_Fn_reader.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Prog Require WriterSpec WriterValue PjStruct.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Spec Require PjTree.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
(* SINK GUARD (a Theorem Labs lane 02:29Z): a SUCCESS here (the build errors naming this line) means a WRONG sink instance
   resolved. *)
Fail Definition probe_SK : Reusable.YI16.sink_head := _.
Fail Definition probe_SH : Reusable.YI14.sink_syms := _.

(* ================= (T7) the two piece lists of the container arms ================= *)
(* the inner fixpoints of WriterValue.wvpieces' JArr / JObj arms, named so the walk can reason about one item at a
   time (wv_items_cons / wv_items_app) instead of under an anonymous fix *)
Definition wv_items (p : bool) (d : Z) : nat -> list PjTree.jv -> list (list Z) :=
  fix go (i : nat) (l : list PjTree.jv) {struct l} : list (list Z) :=
    match l with
    | [] => []
    | x :: r => WriterValue.wcomma i ++ WriterValue.wind p (d + 1) ++ WriterValue.wvpieces x p (d + 1) ++ go (S i) r
    end.

Definition wv_mems (p : bool) (d : Z) : nat -> list (list Z * PjTree.jv) -> list (list Z) :=
  fix go (i : nat) (l : list (list Z * PjTree.jv)) {struct l} : list (list Z) :=
    match l with
    | [] => []
    | (k, x) :: r =>
        WriterValue.wcomma i ++ WriterValue.wind p (d + 1) ++ WriterSpec.spieces k ++ [WriterValue.wsep p]
        ++ WriterValue.wvpieces x p (d + 1) ++ go (S i) r
    end.

Section T. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Variable B : asyms.

(* ================= (T1, T2) one item / one member of a container node ================= *)
(* pj_items at one index: the kid's blocks are a slice of the list's blocks, the kid sits 56 * i past the base *)
Lemma wv_items_split : forall (P : Z -> PjTree.jv -> list (Z * Z) -> Prop) l a D i u,
  PjStruct.pj_items P a l D -> nth_error l i = Some u ->
  exists Dpre Du Dpost, D = Dpre ++ Du ++ Dpost /\ P (a + 56 * Z.of_nat i) u Du.
Proof.
  intros P l. induction l as [|x r IH]; intros a D i u Hl Hi.
  - destruct i; cbn [nth_error] in Hi; discriminate Hi.
  - cbn [PjStruct.pj_items] in Hl. destruct Hl as (D1 & D2 & ED & HP & HR).
    destruct i as [|j]; cbn [nth_error] in Hi.
    + assert (Eu : x = u) by (injection Hi; auto). subst u.
      exists [], D1, D2. split; [cbn [app]; exact ED|].
      replace (a + 56 * Z.of_nat 0) with a by lia. exact HP.
    + destruct (IH (a + 56) D2 j u HR Hi) as (Dpre & Du & Dpost & ED2 & HU).
      exists (D1 ++ Dpre), Du, Dpost. split.
      * rewrite ED, ED2, <- app_assoc. reflexivity.
      * replace (a + 56 * Z.of_nat (S j)) with (a + 56 + 56 * Z.of_nat j) by lia. exact HU.
Qed.

(* pj_mems at one index: the key slot, the key string's block and the kid's blocks *)
Lemma wv_mems_split : forall (m : word -> option byte) (lblk : Z -> Z -> Prop)
    (P : Z -> PjTree.jv -> list (Z * Z) -> Prop) l a ka D i nm u,
  PjStruct.pj_mems tfibsegs m lblk P a ka l D -> nth_error l i = Some (nm, u) ->
  exists Dpre x k Du Dpost, D = Dpre ++ (x, k) :: Du ++ Dpost /\
    PjStruct.pj_u64 tfibsegs m (ka + 8 * Z.of_nat i) x /\
    PjStruct.pj_cstr tfibsegs m lblk x k nm /\
    P (a + 56 * Z.of_nat i) u Du.
Proof.
  intros m lblk P l. induction l as [|[nm0 u0] r IH]; intros a ka D i nm u Hl Hi.
  - destruct i; cbn [nth_error] in Hi; discriminate Hi.
  - cbn [PjStruct.pj_mems] in Hl. destruct Hl as (x & k & D1 & D2 & ED & Hx & Hc & HP & HR).
    destruct i as [|j]; cbn [nth_error] in Hi.
    + assert (Enm : nm0 = nm) by (injection Hi; auto).
      assert (Eu : u0 = u) by (injection Hi; auto). subst nm0 u0.
      exists [], x, k, D1, D2. split; [cbn [app]; exact ED|].
      replace (ka + 8 * Z.of_nat 0) with ka by lia. replace (a + 56 * Z.of_nat 0) with a by lia.
      split; [exact Hx|]. split; [exact Hc | exact HP].
    + destruct (IH (a + 56) (ka + 8) D2 j nm u HR Hi) as (Dpre & x' & k' & Du & Dpost & ED2 & Hx' & Hc' & HU).
      exists ((x, k) :: D1 ++ Dpre), x', k', Du, Dpost. split.
      * rewrite ED, ED2. cbn [app]. rewrite <- app_assoc. reflexivity.
      * replace (ka + 8 * Z.of_nat (S j)) with (ka + 8 + 8 * Z.of_nat j) by lia.
        replace (a + 56 * Z.of_nat (S j)) with (a + 56 + 56 * Z.of_nat j) by lia.
        split; [exact Hx'|]. split; [exact Hc' | exact HU].
Qed.

(* (T1) an array node: the header, the kids block, and the i-th item as a node of its own *)
Lemma wv_arr_item : forall (m : word -> option byte) (lblk : Z -> Z -> Prop) v items D i u,
  PjStruct.pj_node tfibsegs m lblk v (PjTree.JArr items) D ->
  nth_error items i = Some u ->
  exists num kids n cap Di Dpre Du Dpost,
    PjStruct.pj_hdr tfibsegs m v 5 num 0 kids 0 n cap /\
    n = Z.of_nat (length items) /\ n <= cap /\ 0 < cap /\
    lblk kids (56 * cap) /\
    D = (kids, 56 * cap) :: Di /\
    Di = Dpre ++ Du ++ Dpost /\
    PjStruct.pj_node tfibsegs m lblk (kids + 56 * Z.of_nat i) u Du /\
    (forall b, In b Du -> In b D) /\ NoDup D.
Proof.
  intros m lblk v items D i u H Hi.
  cbn [PjStruct.pj_node] in H.
  destruct H as (HN & HA & num & str & kids & keys & n & cap & Hh & Es & Ek & En & Hnc & Hcap & Di & ED & Hit).
  cbn [PjTree.tag] in Hh. subst str keys.
  assert (Hlen : (0 < length items)%nat).
  { destruct items as [|y ys]; [destruct i; cbn [nth_error] in Hi; discriminate Hi | cbn [length]; lia]. }
  assert (Hc : 0 < cap) by (destruct Hcap as [(Ec & _)|(Hc0 & _)]; [subst cap; lia | exact Hc0]).
  assert (Hl : lblk kids (56 * cap)) by (destruct Hcap as [(Ec & _)|(_ & Hl0)]; [lia | exact Hl0]).
  rewrite (proj2 (Z.eqb_neq cap 0)) in ED by lia. cbn [app] in ED.
  destruct (wv_items_split (PjStruct.pj_node tfibsegs m lblk) items kids Di i u Hit Hi)
    as (Dpre & Du & Dpost & EDi & HU).
  exists num, kids, n, cap, Di, Dpre, Du, Dpost.
  split; [exact Hh|]. split; [exact En|]. split; [exact Hnc|]. split; [exact Hc|].
  split; [exact Hl|]. split; [exact ED|]. split; [exact EDi|]. split; [exact HU|].
  split; [|exact HN].
  intros b Hb. rewrite ED. right. rewrite EDi. apply in_or_app. right. apply in_or_app. left. exact Hb.
Qed.

(* (T2) an object node: the header, the kids and keys blocks, the i-th key slot, its string and the i-th value *)
Lemma wv_obj_mem : forall (m : word -> option byte) (lblk : Z -> Z -> Prop) v members D i nm u,
  PjStruct.pj_node tfibsegs m lblk v (PjTree.JObj members) D ->
  nth_error members i = Some (nm, u) ->
  exists num kids keys n cap Di Dpre x k Du Dpost,
    PjStruct.pj_hdr tfibsegs m v 6 num 0 kids keys n cap /\
    n = Z.of_nat (length members) /\ n <= cap /\ 0 < cap /\
    lblk kids (56 * cap) /\ lblk keys (8 * cap) /\
    D = (kids, 56 * cap) :: (keys, 8 * cap) :: Di /\
    Di = Dpre ++ (x, k) :: Du ++ Dpost /\
    PjStruct.pj_u64 tfibsegs m (keys + 8 * Z.of_nat i) x /\
    PjStruct.pj_cstr tfibsegs m lblk x k nm /\
    PjStruct.pj_node tfibsegs m lblk (kids + 56 * Z.of_nat i) u Du /\
    (forall b, In b Du -> In b D) /\ In (x, k) D /\ NoDup D.
Proof.
  intros m lblk v members D i nm u H Hi.
  cbn [PjStruct.pj_node] in H.
  destruct H as (HN & HA & num & str & kids & keys & n & cap & Hh & Es & En & Hnc & Hcap & Di & ED & Hit).
  cbn [PjTree.tag] in Hh. subst str.
  assert (Hlen : (0 < length members)%nat).
  { destruct members as [|y ys]; [destruct i; cbn [nth_error] in Hi; discriminate Hi | cbn [length]; lia]. }
  assert (Hc : 0 < cap) by (destruct Hcap as [(Ec & _)|(Hc0 & _)]; [subst cap; lia | exact Hc0]).
  assert (Hlk : lblk kids (56 * cap)) by (destruct Hcap as [(Ec & _)|(_ & Hl0 & _)]; [lia | exact Hl0]).
  assert (Hly : lblk keys (8 * cap)) by (destruct Hcap as [(Ec & _)|(_ & _ & Hl1)]; [lia | exact Hl1]).
  rewrite (proj2 (Z.eqb_neq cap 0)) in ED by lia. cbn [app] in ED.
  destruct (wv_mems_split m lblk (PjStruct.pj_node tfibsegs m lblk) members kids keys Di i nm u Hit Hi)
    as (Dpre & x & k & Du & Dpost & EDi & Hx & Hcs & HU).
  exists num, kids, keys, n, cap, Di, Dpre, x, k, Du, Dpost.
  split; [exact Hh|]. split; [exact En|]. split; [exact Hnc|]. split; [exact Hc|].
  split; [exact Hlk|]. split; [exact Hly|]. split; [exact ED|]. split; [exact EDi|].
  split; [exact Hx|]. split; [exact Hcs|]. split; [exact HU|].
  split; [|split; [|exact HN]].
  - intros b Hb. rewrite ED. right. right. rewrite EDi. apply in_or_app. right. right.
    apply in_or_app. left. exact Hb.
  - rewrite ED. right. right. rewrite EDi. apply in_or_app. right. left. reflexivity.
Qed.

(* ================= (T3, T4) the kid's footprint inside the parent's ================= *)
(* a kid's footprint is the parent's, as soon as the kid's blocks are the parent's and the kid's 56 header bytes
   are inside the parent's footprint *)
Lemma wv_foot_sub : forall p q D Dq,
  (forall b, In b Dq -> In b D) ->
  (forall x, q <= x < q + 56 -> PjStruct.pj_foot p D x) ->
  forall x, PjStruct.pj_foot q Dq x -> PjStruct.pj_foot p D x.
Proof.
  intros p q D Dq HI HF x H. unfold PjStruct.pj_foot in H.
  destruct H as [Hx|(b & Hb & Hh)].
  - exact (HF x Hx).
  - right. exists b. split; [exact (HI b Hb) | exact Hh].
Qed.

(* the i-th kid slot of a kids block is in the parent's footprint *)
Lemma wv_foot_kids : forall p D kids cap i,
  In (kids, 56 * cap) D -> 0 <= i -> i < cap ->
  forall x, kids + 56 * i <= x < kids + 56 * i + 56 -> PjStruct.pj_foot p D x.
Proof.
  intros p D kids cap i Hin H0 Hi x Hx. right. exists (kids, 56 * cap). split; [exact Hin|].
  unfold PjStruct.pj_holds. cbn [fst snd]. lia.
Qed.

(* ================= (T5) the narrow form carried to an item ================= *)
Lemma wv_plain_item : forall items i u,
  jv_plain (PjTree.JArr items) -> nth_error items i = Some u -> jv_plain u.
Proof.
  induction items as [|x r IH]; intros i u H Hi.
  - destruct i; cbn [nth_error] in Hi; discriminate Hi.
  - cbn [jv_plain] in H. destruct H as (Hx & Hr).
    destruct i as [|j]; cbn [nth_error] in Hi.
    + assert (Eu : x = u) by (injection Hi; auto). subst u. exact Hx.
    + exact (IH j u Hr Hi).
Qed.

Lemma wv_plain_mem : forall members i nm u,
  jv_plain (PjTree.JObj members) -> nth_error members i = Some (nm, u) ->
  plain_bytes nm /\ jv_plain u.
Proof.
  induction members as [|[k x] r IH]; intros i nm u H Hi.
  - destruct i; cbn [nth_error] in Hi; discriminate Hi.
  - cbn [jv_plain] in H. destruct H as (Hk & Hx & Hr).
    destruct i as [|j]; cbn [nth_error] in Hi.
    + assert (Ek : k = nm) by (injection Hi; auto).
      assert (Eu : x = u) by (injection Hi; auto). subst nm u.
      split; [exact Hk | exact Hx].
    + exact (IH j nm u Hr Hi).
Qed.

(* ================= (T6) the item's depth, for the recursion's measure ================= *)
Lemma wv_depth_item : forall items i u, nth_error items i = Some u ->
  (PjTree.depth u < PjTree.depth (PjTree.JArr items))%nat.
Proof.
  intros items i u Hi. apply PjTree.depth_item. exact (nth_error_In items i Hi).
Qed.

Lemma wv_depth_mem : forall members i nm u, nth_error members i = Some (nm, u) ->
  (PjTree.depth u < PjTree.depth (PjTree.JObj members))%nat.
Proof.
  intros members i nm u Hi. apply (PjTree.depth_member members nm u).
  exact (nth_error_In members i Hi).
Qed.

(* ================= (T7) the pieces of the two container arms ================= *)
Lemma wv_pieces_arr : forall items p d,
  WriterValue.wvpieces (PjTree.JArr items) p d =
  [91] :: wv_items p d 0%nat items ++
  (match items with [] => [] | _ :: _ => WriterValue.wind p d end) ++ [[93]].
Proof. intros items p d. reflexivity. Qed.

Lemma wv_pieces_obj : forall members p d,
  WriterValue.wvpieces (PjTree.JObj members) p d =
  [123] :: wv_mems p d 0%nat members ++
  (match members with [] => [] | _ :: _ => WriterValue.wind p d end) ++ [[125]].
Proof. intros members p d. reflexivity. Qed.

Lemma wv_items_cons : forall p d i x r,
  wv_items p d i (x :: r) =
  WriterValue.wcomma i ++ WriterValue.wind p (d + 1) ++ WriterValue.wvpieces x p (d + 1) ++ wv_items p d (S i) r.
Proof. intros p d i x r. reflexivity. Qed.

Lemma wv_mems_cons : forall p d i k x r,
  wv_mems p d i ((k, x) :: r) =
  WriterValue.wcomma i ++ WriterValue.wind p (d + 1) ++ WriterSpec.spieces k ++ [WriterValue.wsep p]
  ++ WriterValue.wvpieces x p (d + 1) ++ wv_mems p d (S i) r.
Proof. intros p d i k x r. reflexivity. Qed.

Lemma wv_items_app : forall p d i l1 l2,
  wv_items p d i (l1 ++ l2) = wv_items p d i l1 ++ wv_items p d (i + length l1)%nat l2.
Proof.
  intros p d i l1. revert i. induction l1 as [|x r IH]; intros i l2.
  - cbn [app length wv_items]. rewrite Nat.add_0_r. reflexivity.
  - rewrite <- app_comm_cons, !wv_items_cons, IH. cbn [length].
    rewrite Nat.add_succ_r, <- !app_assoc. reflexivity.
Qed.

Lemma wv_mems_app : forall p d i l1 l2,
  wv_mems p d i (l1 ++ l2) = wv_mems p d i l1 ++ wv_mems p d (i + length l1)%nat l2.
Proof.
  intros p d i l1. revert i. induction l1 as [|[k x] r IH]; intros i l2.
  - cbn [app length wv_mems]. rewrite Nat.add_0_r. reflexivity.
  - rewrite <- app_comm_cons, !wv_mems_cons, IH. cbn [length].
    rewrite Nat.add_succ_r, <- !app_assoc. reflexivity.
Qed.

Lemma wv_concat_app : forall (P Q : list (list Z)),
  length (concat (P ++ Q)) = (length (concat P) + length (concat Q))%nat.
Proof. intros P Q. rewrite concat_app, length_app. reflexivity. Qed.

(* ================= (T8) the kid node's placement for the recursive call ================= *)
(* the i-th kid slot of a live reader block is a pobj: the block past its 16-byte head is a live block's body,
   8-aligned (the block is 16-aligned and the slots are 56 bytes apart), addressable on the MACHINE memory
   (FSW_rd.fsw_block_body_addressable: every user-poisoned range is a block's first 16 bytes, fs_heads, and live
   blocks are pairwise disjoint), and writable (AR's block law gives apresent at the unpoisoned reading, and a
   block byte is not a shadow byte, so the two readings agree there) *)
Lemma wv_kid_pobj : forall ly S U (W : world tfibsegs) mem md kids cap i,
  ARU tfibsegs B ly S U W mem md -> fs_heads B ly S U ->
  fs_rblock tfibsegs B ly S W mem kids (56 * cap) -> 0 <= i -> i + 1 <= cap ->
  FSH_Fn_reader.pobj tfibsegs B ly S W mem (kids + 56 * i).
Proof.
  intros ly S U W mem md kids cap i HARU FH HB H0 Hi.
  pose proof (AR_laws_ok tfibsegs B) as LAWS.
  pose proof (ARU_AR tfibsegs B ly S U W mem md HARU) as HAR.
  destruct HB as (Hin & Hal16 & Hpos & _).
  pose proof (req_size_pos (56 * cap + HEAD) ltac:(unfold HEAD; lia)) as (_ & Hrq).
  destruct (al_blocks tfibsegs B LAWS ly S W (unpoison U mem) md (kids - HEAD) (56 * cap + HEAD) HAR Hin)
    as (_ & Hb4096 & Hbceil & _ & HPres & _ & _).
  split.
  - right. split; [|split].
    + exists (kids - HEAD), (56 * cap + HEAD). split; [exact Hin|].
      split; unfold HEAD in *; lia.
    + apply Z.mod_divide in Hal16 as [q Hq]; [|lia]. rewrite Hq.
      replace (q * 16 + 56 * i) with ((q * 2 + 7 * i) * 8) by lia. apply Z_mod_mult.
    + apply (fsw_block_body_addressable B ly S U W mem md (kids - HEAD) (56 * cap + HEAD)
               (kids + 56 * i) 56 HARU FH Hin); unfold HEAD in *; lia.
  - intros j Hj.
    assert (Hrg : kids - HEAD <= kids + 56 * i + j < kids - HEAD + req_size (56 * cap + HEAD))
      by (unfold HEAD in *; lia).
    pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
    assert (Hlo : 0 <= kids + 56 * i + j < 2 ^ 64) by (unfold HEAD in *; lia).
    destruct (HPres (kids + 56 * i + j) Hrg) as (HPa & _).
    assert (NU : in_ush U (bv_unsigned (Z_to_bv 64 (kids + 56 * i + j))) = false).
    { destruct (in_ush U (bv_unsigned (Z_to_bv 64 (kids + 56 * i + j)))) eqn:E; [exfalso|reflexivity].
      assert (UF : aowned B ly S (bv_unsigned (Z_to_bv 64 (kids + 56 * i + j))) /\
                   SHADOW_OFF <= bv_unsigned (Z_to_bv 64 (kids + 56 * i + j)) < kHighMemBeg)
        by (eapply ush_facts; eassumption).
      rewrite (wz (kids + 56 * i + j) Hlo) in UF. destruct UF as (_ & UF1 & UF2).
      apply (fsw_ablock_off_shadow B ly S W (unpoison U mem) md (kids - HEAD) (56 * cap + HEAD) HAR Hin
               (kids + 56 * i + j) ltac:(unfold HEAD in *; lia)).
      change (2 ^ 44) with 17592186044416. unfold SHADOW_OFF, kHighMemBeg in *. lia. }
    assert (EU : unpoison U mem (Z_to_bv 64 (kids + 56 * i + j)) = mem (Z_to_bv 64 (kids + 56 * i + j)))
      by (apply unpoison_out; exact NU).
    apply (apresent_writable tfibsegs). destruct HPa as (HH & b0 & Hb0).
    split; [exact HH|]. exists b0. rewrite <- EU. exact Hb0.
Qed.

End T.
(* rebuilt on the 50968be8342 statement set *)
