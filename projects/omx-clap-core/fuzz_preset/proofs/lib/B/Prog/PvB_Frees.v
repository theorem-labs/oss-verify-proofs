(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/B/Prog/PutB_Base.v, with its module paths and module names changed; 220 of its 265 lines of code are new or changed and 1360 lines of the source are left out. *)
(* fuzz_preset (omx-clap-core), lane PValueB: the FREE-ORDER and CAPACITY lemmas the batch kit reader texts' posts ask
   (the batch kit, a working branch 8ba304fe2f93: lib/A/PRH_FnParse.v tparse_value_specX /
   tparse_items_specX, the free-order tie `pj_foR .. n v D F /\ map (fun b => snd b + cf_head) F = prhPv_frees ..`
   and `pj_ncapR .. v t`). Image-free and state-free: the model side (prhPv_frees at a leaf, at a container; the
   fuel of jfl, a Theorem Labs lane's lib/Spec/PresetFreeFo.v), the tree side (a leaf node's pj_foR at every depth, a
   zero node's, pj_ncapR of a leaf, pj_ncapR across a memory that agrees on the node's footprint pj_footR p D, and
   across a pointwise-equal memory). One writer (PValueB); lane PItemsB takes this file by path.
   Proves no function (kind: segment lemma). Numerals: 123 / 91 the opener bytes (WORD), 56 / 24 / 48 the node
   layout (LENGTH), 8 the word size, 2 ^ 64 the word range. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s YK0j.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn YP0b YP0a.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YN3v YI04 YI00 YG0s YP07.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YI16 YK06.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require ReaderRes.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Base PRH_Reader PRH_FnReader PRH_Charge PRH_FnParse.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require PRH_PjOrder.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PjGrammar PjTree PresetReqAt PresetFreeFo.
Import ListNotations.
Local Open Scope Z_scope.

(* ---- the model: prhPv_frees at the value's first byte ---- *)

(* one step of jfv, as its body reads *)
Lemma pvf_jfv_S : forall sm f d x ok,
  PresetReqAt.jfv sm (S f) d x ok =
  match PjGrammar.skip x with
  | [] => []
  | b :: y =>
      if b =? 123 then PresetReqAt.jf_cont (PresetReqAt.jfl sm f) d true (b :: y) ok
      else if b =? 91 then PresetReqAt.jf_cont (PresetReqAt.jfl sm f) d false (b :: y) ok
      else PresetReqAt.lf (snd (fst (PjGrammar.jrv sm (S f) d x ok)))
  end.
Proof. reflexivity. Qed.

(* end of text: no value, nothing to free *)
Lemma pvf_frees_nil : forall d x ok, PjGrammar.skip x = [] -> prhPv_frees d x ok = [].
Proof. intros d x ok Hs. unfold prhPv_frees. rewrite pvf_jfv_S, Hs. reflexivity. Qed.

(* a leaf (string, number, literal): the frees are the leaf's own block, PresetReqAt.lf of the value's trace *)
Lemma pvf_frees_leaf : forall d x ok b y, PjGrammar.skip x = b :: y -> b <> 123 -> b <> 91 ->
  prhPv_frees d x ok = PresetReqAt.lf (snd (fst (PjGrammar.jr_value prh_jr_strtod d x ok))).
Proof.
intros d x ok b y Hs H1 H2. unfold prhPv_frees, PjGrammar.jr_value.
rewrite PresetFreeFo.jfv_leaf; [reflexivity|].
rewrite Hs. split; apply Z.eqb_neq; assumption.
Qed.

(* a container: the value's frees are parse_items' at the opener (jfl's fuel above its need, jf_fuel_mono) *)
Lemma pvf_frees_cont : forall d x ok (o : bool) y, PjGrammar.skip x = (if o then 123 else 91) :: y ->
  prhPv_frees d x ok = prhPi_frees d o ((if o then 123 else 91) :: y) ok.
Proof.
intros d x ok o y Hs. unfold prhPv_frees, prhPi_frees. rewrite pvf_jfv_S, Hs.
assert (Hl : (S (length y) <= length x)%nat).
{ pose proof (PjGrammar.skip_len x) as H. rewrite Hs in H. exact H. }
assert (Hk : forall f, (2 * length (PjGrammar.skip y) + 2 <= f)%nat -> forall d' n cap af ok',
  PresetReqAt.jfl ReaderRes.jr_strtod f d' o n cap af (PjGrammar.skip y) ok' =
  PresetReqAt.jfl ReaderRes.jr_strtod (2 * length (PjGrammar.skip y) + 2) d' o n cap af (PjGrammar.skip y) ok').
{ intros f Hf d' n cap af ok'.
  exact (proj2 (PresetFreeFo.jf_fuel_mono ReaderRes.jr_strtod (2 * length (PjGrammar.skip y) + 2))
    d' o n cap af (PjGrammar.skip y) f ok' (le_n _) Hf). }
pose proof (PjGrammar.skip_len y) as Hy.
destruct o.
- cbv beta iota. change (123 =? 123) with true. cbv beta iota.
  unfold PresetReqAt.jf_cont. cbv beta zeta. cbn [tl].
  match goal with |- context [Nat.ltb ?M (S d)] => destruct (Nat.ltb M (S d)) end; [reflexivity|].
  rewrite (Hk (2 * length x)%nat ltac:(lia)), (Hk (2 * length (123%Z :: y) + 2)%nat ltac:(cbn [length]; lia)).
  reflexivity.
- cbv beta iota. change (91 =? 123) with false. change (91 =? 91) with true. cbv beta iota.
  unfold PresetReqAt.jf_cont. cbv beta zeta. cbn [tl].
  match goal with |- context [Nat.ltb ?M (S d)] => destruct (Nat.ltb M (S d)) end; [reflexivity|].
  rewrite (Hk (2 * length x)%nat ltac:(lia)), (Hk (2 * length (91%Z :: y) + 2)%nat ltac:(cbn [length]; lia)).
  reflexivity.
Qed.

(* lf of a trace that is not one allocation is empty *)
Lemma pvf_lf_nil : PresetReqAt.lf [] = [].
Proof. reflexivity. Qed.

Lemma pvf_lf_one : forall n, PresetReqAt.lf [PjGrammar.EAlloc n] = [Z.of_nat n + PresetReqAt.HEAD].
Proof. reflexivity. Qed.

Section t.
Variable segs : list Segment.

(* ---- the tree: a leaf's free order ---- *)

(* a node whose children fields are zero holds at most its string block; its free order is that block, at every
   depth bound *)
Lemma pvf_hdr_leaf_foR : forall m lblk n p D ty num str,
  pj_hdrR segs m p ty num str 0 0 0 0 ->
  (str = 0 /\ D = [] \/ exists k, lblk str k /\ D = [(str, k)]) ->
  NoDup D -> pj_apartR D p ->
  PRH_PjOrder.pj_foR segs m lblk n p D D.
Proof.
intros m lblk n p D ty num str Hh HD Hnd Ha.
assert (Hsh : forall Pi : bool -> Z -> Z -> Z -> list (Z * Z) -> list (Z * Z) -> Prop, Pi false 0 0 0 [] [] ->
  PRH_PjOrder.pj_oshapeR segs m lblk Pi p D D).
{ intros Pi HPi. split; [exact Hnd|]. split; [exact Ha|].
  exists ty, num, str, 0, 0, 0, 0, false, D, [], [], [], [].
  split; [exact Hh|].
  split; [destruct HD as [(E1 & E2)|(k & Hk & E)]; [left; split; assumption | right; exists k; split; assumption]|].
  split; [left; split; [reflexivity|split; reflexivity]|].
  split; [left; split; [reflexivity|split; reflexivity]|].
  split; [rewrite !app_nil_r; apply Permutation_refl|].
  split; [exact HPi|]. rewrite !app_nil_l. reflexivity. }
destruct n as [|n]; cbn [PRH_PjOrder.pj_foR]; apply Hsh; cbn; [split; [reflexivity|split; reflexivity]|].
split; reflexivity.
Qed.

(* a node with an all-zero header: no block, the empty free order *)
Lemma pvf_zero_foR : forall m lblk n p ty,
  pj_hdrR segs m p ty 0 0 0 0 0 0 -> PRH_PjOrder.pj_foR segs m lblk n p [] [].
Proof.
intros m lblk n p ty Hh. apply (pvf_hdr_leaf_foR m lblk n p [] ty 0 0 Hh).
- left. split; reflexivity.
- constructor.
- intros b x [].
Qed.

(* a leaf node (no children): its blocks are its free order, at every depth bound *)
Lemma pvf_node_leaf_foR : forall m lblk n p t D, pj_nodeR segs m lblk p t D ->
  (forall items, t <> PjTree.JArr items) -> (forall ms, t <> PjTree.JObj ms) ->
  PRH_PjOrder.pj_foR segs m lblk n p D D.
Proof.
intros m lblk n p t D H Na No.
destruct t as [| | | txt bits | s | items | ms];
  [| | | | | exfalso; exact (Na items eq_refl) | exfalso; exact (No ms eq_refl)];
  cbn [pj_nodeR] in H; destruct H as (Hnd & Ha & num & str & kids & keys & nn & cap & Hh & Hb).
- destruct Hb as (-> & -> & -> & -> & -> & ->).
  exact (pvf_hdr_leaf_foR m lblk n p [] _ num 0 Hh (or_introl (conj eq_refl eq_refl)) Hnd Ha).
- destruct Hb as (-> & -> & -> & -> & -> & ->).
  exact (pvf_hdr_leaf_foR m lblk n p [] _ num 0 Hh (or_introl (conj eq_refl eq_refl)) Hnd Ha).
- destruct Hb as (-> & -> & -> & -> & -> & ->).
  exact (pvf_hdr_leaf_foR m lblk n p [] _ num 0 Hh (or_introl (conj eq_refl eq_refl)) Hnd Ha).
- destruct Hb as (_ & -> & -> & -> & -> & k & Hc & ->).
  apply (pvf_hdr_leaf_foR m lblk n p _ _ num str Hh); [|exact Hnd|exact Ha].
  right. exists k. split; [exact (proj1 Hc)|reflexivity].
- destruct Hb as (-> & -> & -> & -> & k & Hc & ->).
  apply (pvf_hdr_leaf_foR m lblk n p _ _ num str Hh); [|exact Hnd|exact Ha].
  right. exists k. split; [exact (proj1 Hc)|reflexivity].
Qed.

(* the tie's size side at a leaf: D's sizes (plus the head) are lf of the leaf's trace *)
Lemma pvf_tie_nil : forall (hd : Z), map (fun b : Z * Z => snd b + hd) [] = PresetReqAt.lf [].
Proof. reflexivity. Qed.

Lemma pvf_tie_one : forall (a : Z) (q : nat), map (fun b : Z * Z => snd b + PresetReqAt.HEAD) [(a, Z.of_nat q)] =
  PresetReqAt.lf [PjGrammar.EAlloc q].
Proof. intros a q. reflexivity. Qed.

(* ---- the capacity words ---- *)

Lemma pvf_ncap_leaf : forall m p t, (forall items, t <> PjTree.JArr items) -> (forall ms, t <> PjTree.JObj ms) ->
  pj_ncapR segs m p t.
Proof.
intros m p t Na No. destruct t as [| | | | | items | ms]; cbn [pj_ncapR]; try exact I;
  [exfalso; exact (Na items eq_refl) | exfalso; exact (No ms eq_refl)].
Qed.

(* two rd_u64 reads of one restricted memory at one address agree *)
Lemma pvf_rdword_of_val : forall H mem a v,
  val_mem segs (mrestrict H mem) a 8 v -> 0 <= v < 2 ^ 64 -> rdword (aview segs H mem) a = Some v.
Proof.
intros H mem a v Hv Hr.
assert (Bk : forall k, (k < 8)%nat -> aview segs H mem (a + Z.of_nat k) = Some (YG0f.le_byte v 8 k)).
{ intros k Hk. unfold aview. rewrite (Hv k Hk). cbn [option_map]. f_equal.
  rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256.
  change (YO0f.le_byte v 8 k) with (YG0f.le_byte v 8 k). unfold YG0f.le_byte. apply Z.mod_mod. lia. }
unfold rdword.
rewrite <- (Z.add_0_r a) at 1. change 0 with (Z.of_nat 0) at 1. rewrite (Bk 0%nat) by lia.
change 1 with (Z.of_nat 1). rewrite (Bk 1%nat) by lia. change 2 with (Z.of_nat 2) at 1. rewrite (Bk 2%nat) by lia.
change 3 with (Z.of_nat 3). rewrite (Bk 3%nat) by lia. change 4 with (Z.of_nat 4). rewrite (Bk 4%nat) by lia.
change 5 with (Z.of_nat 5). rewrite (Bk 5%nat) by lia. change 6 with (Z.of_nat 6). rewrite (Bk 6%nat) by lia.
change 7 with (Z.of_nat 7). rewrite (Bk 7%nat) by lia.
f_equal. apply le_bytes8. exact Hr.
Qed.

Lemma pvf_u64_det : forall H mem a v v', rd_u64 segs (mrestrict H mem) a v -> rd_u64 segs (mrestrict H mem) a v' ->
  v = v'.
Proof.
intros H mem a v v' (Hr & Hv) (Hr' & Hv').
pose proof (pvf_rdword_of_val H mem a v Hv Hr) as E. rewrite (pvf_rdword_of_val H mem a v' Hv' Hr') in E.
injection E as E. exact (eq_sym E).
Qed.

(* pj_kidsR along pj_itemsR: per item, from the item's node *)
Lemma pvf_kids_items : forall (P : Z -> PjTree.jv -> list (Z * Z) -> Prop) (Q Q' : Z -> PjTree.jv -> Prop) l a D,
  pj_itemsR P a l D -> pj_kidsR Q a l ->
  (forall i u D1, nth_error l i = Some u -> incl D1 D -> P (a + 56 * Z.of_nat i) u D1 ->
     Q (a + 56 * Z.of_nat i) u -> Q' (a + 56 * Z.of_nat i) u) ->
  pj_kidsR Q' a l.
Proof.
intros P Q Q' l. induction l as [|u r IH]; intros a D H HQ HP; cbn [pj_itemsR pj_kidsR] in H, HQ |- *; [exact I|].
destruct H as (D1 & D2 & -> & H1 & H2). destruct HQ as (Q1 & Q2). split.
- specialize (HP 0%nat u D1 eq_refl (incl_appl D2 (incl_refl D1))).
  replace (a + 56 * Z.of_nat 0) with a in HP by lia. exact (HP H1 Q1).
- apply (IH (a + 56) D2 H2 Q2). intros i u' D1' Hi Hinc HPi HQi.
  specialize (HP (S i) u' D1' Hi (incl_appr D1 Hinc)).
  replace (a + 56 * Z.of_nat (S i)) with (a + 56 + 56 * Z.of_nat i) in HP by lia.
  exact (HP HPi HQi).
Qed.

(* pj_kidsR along pj_memsR (an object's members): per member, from the member's node *)
Lemma pvf_kids_mems : forall m lblk (P : Z -> PjTree.jv -> list (Z * Z) -> Prop) (Q Q' : Z -> PjTree.jv -> Prop)
    l a ka D,
  pj_memsR segs m lblk P a ka l D ->
  pj_kidsR (fun a (mb : list Z * PjTree.jv) => let (_, u) := mb in Q a u) a l ->
  (forall i nm u D1, nth_error l i = Some (nm, u) -> incl D1 D -> P (a + 56 * Z.of_nat i) u D1 ->
     Q (a + 56 * Z.of_nat i) u -> Q' (a + 56 * Z.of_nat i) u) ->
  pj_kidsR (fun a (mb : list Z * PjTree.jv) => let (_, u) := mb in Q' a u) a l.
Proof.
intros m lblk P Q Q' l. induction l as [|[nm u] r IH]; intros a ka D H HQ HP;
  cbn [pj_memsR pj_kidsR] in H, HQ |- *; [exact I|].
destruct H as (x & k & D1 & D2 & -> & _ & _ & H1 & H2). destruct HQ as (Q1 & Q2). split.
- specialize (HP 0%nat nm u D1 eq_refl (incl_tl (x, k) (incl_appl D2 (incl_refl D1)))).
  replace (a + 56 * Z.of_nat 0) with a in HP by lia. exact (HP H1 Q1).
- apply (IH (a + 56) (ka + 8) D2 H2 Q2). intros i nm' u' D1' Hi Hinc HPi HQi.
  specialize (HP (S i) nm' u' D1' Hi (incl_tl (x, k) (incl_appr D1 Hinc))).
  replace (a + 56 * Z.of_nat (S i)) with (a + 56 + 56 * Z.of_nat i) in HP by lia.
  exact (HP HPi HQi).
Qed.

(* THE CAPACITY WORDS ACROSS A MEMORY THAT AGREES ON THE NODE'S FOOTPRINT (the node and its blocks D) *)
Lemma pvf_ncap_frame : forall t H mem m' lblk p D,
  pj_nodeR segs (mrestrict H mem) lblk p t D -> pj_agreeR segs (mrestrict H mem) m' (pj_footR p D) ->
  pj_ncapR segs (mrestrict H mem) p t -> pj_ncapR segs m' p t.
Proof.
intros t. induction t as [| | | txt bits | s | items IH | members IH] using PjTree.jv_ind';
  intros H mem m' lblk p D HN HM HC; cbn [pj_ncapR] in HC |- *; try exact I.
- assert (HM1 : forall x, pj_footR p D x -> mbyte segs m' x = mbyte segs (mrestrict H mem) x)
    by (intros x Hx; exact (proj1 (HM x Hx))).
  cbn [pj_nodeR] in HN. destruct HN as (_ & _ & num & str & kids & keys & n & cap & Hh & Hb).
  destruct Hb as (Es & Ek & En & Hc & Hcap & Di & ED & Hi).
  destruct HC as (H48 & kids' & H24 & Hk).
  pose proof Hh as (_ & _ & _ & _ & Hkids & _).
  assert (Ekk : kids' = kids) by exact (pvf_u64_det H mem (p + 24) kids' kids H24 Hkids). subst kids'.
  split; [apply (rd_u64_frame segs _ _ _ _ H48); intros x Hx; apply HM1; left; lia|].
  exists kids. split; [apply (rd_u64_frame segs _ _ _ _ H24); intros x Hx; apply HM1; left; lia|].
  assert (HDi : forall b, In b Di -> In b D) by (intros b Hb; subst D; apply in_or_app; right; exact Hb).
  apply (pvf_kids_items (pj_nodeR segs (mrestrict H mem) lblk) (pj_ncapR segs (mrestrict H mem)) _ items kids Di Hi Hk).
  intros i u D1 Hil Hinc HP HQ.
  pose proof (pj_nth_lenR items i u Hil) as Hlt.
  assert (Hp : 0 < cap) by lia.
  assert (Hin : In (kids, 56 * cap) D).
  { subst D. rewrite (proj2 (Z.eqb_neq cap 0)) by lia. left; reflexivity. }
  rewrite Forall_forall in IH.
  apply (IH u (nth_error_In items i Hil) H mem m' lblk _ D1 HP); [|exact HQ].
  intros x Hx. apply HM. destruct Hx as [Hx|(b & Hb & Hx)].
  + right. exists (kids, 56 * cap). split; [exact Hin | unfold pj_holdsR; cbn [fst snd]; lia].
  + right. exists b. split; [apply HDi; apply Hinc; exact Hb | exact Hx].
- assert (HM1 : forall x, pj_footR p D x -> mbyte segs m' x = mbyte segs (mrestrict H mem) x)
    by (intros x Hx; exact (proj1 (HM x Hx))).
  cbn [pj_nodeR] in HN. destruct HN as (_ & _ & num & str & kids & keys & n & cap & Hh & Hb).
  destruct Hb as (Es & En & Hc & Hcap & Di & ED & Hi).
  destruct HC as (H48 & kids' & H24 & Hk).
  pose proof Hh as (_ & _ & _ & _ & Hkids & _).
  assert (Ekk : kids' = kids) by exact (pvf_u64_det H mem (p + 24) kids' kids H24 Hkids). subst kids'.
  split; [apply (rd_u64_frame segs _ _ _ _ H48); intros x Hx; apply HM1; left; lia|].
  exists kids. split; [apply (rd_u64_frame segs _ _ _ _ H24); intros x Hx; apply HM1; left; lia|].
  assert (HDi : forall b, In b Di -> In b D) by (intros b Hb; subst D; apply in_or_app; right; exact Hb).
  apply (pvf_kids_mems (mrestrict H mem) lblk (pj_nodeR segs (mrestrict H mem) lblk)
    (pj_ncapR segs (mrestrict H mem)) _ members kids keys Di Hi Hk).
  intros i nm u D1 Hil Hinc HP HQ.
  pose proof (pj_nth_lenR members i (nm, u) Hil) as Hlt.
  assert (Hp : 0 < cap) by lia.
  assert (Hin : In (kids, 56 * cap) D).
  { subst D. rewrite (proj2 (Z.eqb_neq cap 0)) by lia. left; reflexivity. }
  rewrite Forall_forall in IH. specialize (IH (nm, u) (nth_error_In members i Hil)). cbn [snd] in IH.
  apply (IH H mem m' lblk _ D1 HP); [|exact HQ].
  intros x Hx. apply HM. destruct Hx as [Hx|(b & Hb & Hx)].
  + right. exists (kids, 56 * cap). split; [exact Hin | unfold pj_holdsR; cbn [fst snd]; lia].
  + right. exists b. split; [apply HDi; apply Hinc; exact Hb | exact Hx].
Qed.

(* the capacity words across a pointwise-equal memory *)
Lemma pvf_ncap_ext : forall t m m' p, (forall x, mbyte segs m' x = mbyte segs m x) ->
  pj_ncapR segs m p t -> pj_ncapR segs m' p t.
Proof.
intros t. induction t as [| | | txt bits | s | items IH | members IH] using PjTree.jv_ind';
  intros m m' p E HC; cbn [pj_ncapR] in HC |- *; try exact I.
- destruct HC as (H48 & kids & H24 & Hk).
  split; [exact (rd_u64_frame segs _ _ _ _ H48 (fun x _ => E x))|].
  exists kids. split; [exact (rd_u64_frame segs _ _ _ _ H24 (fun x _ => E x))|].
  rewrite Forall_forall in IH.
  assert (G : forall l a, incl l items -> pj_kidsR (pj_ncapR segs m) a l -> pj_kidsR (pj_ncapR segs m') a l).
  { intros l. induction l as [|u r IHl]; intros a Hinc Hl; cbn [pj_kidsR] in Hl |- *; [exact I|].
    destruct Hl as (H1 & H2). split.
    - exact (IH u (Hinc u (or_introl eq_refl)) m m' a E H1).
    - exact (IHl (a + 56) (fun z Hz => Hinc z (or_intror Hz)) H2). }
  exact (G items kids (incl_refl items) Hk).
- destruct HC as (H48 & kids & H24 & Hk).
  split; [exact (rd_u64_frame segs _ _ _ _ H48 (fun x _ => E x))|].
  exists kids. split; [exact (rd_u64_frame segs _ _ _ _ H24 (fun x _ => E x))|].
  rewrite Forall_forall in IH.
  assert (G : forall l a, incl l members ->
    pj_kidsR (fun a (mb : list Z * PjTree.jv) => let (_, u) := mb in pj_ncapR segs m a u) a l ->
    pj_kidsR (fun a (mb : list Z * PjTree.jv) => let (_, u) := mb in pj_ncapR segs m' a u) a l).
  { intros l. induction l as [|[nm u] r IHl]; intros a Hinc Hl; cbn [pj_kidsR] in Hl |- *; [exact I|].
    destruct Hl as (H1 & H2). split.
    - exact (IH (nm, u) (Hinc (nm, u) (or_introl eq_refl)) m m' a E H1).
    - exact (IHl (a + 56) (fun z Hz => Hinc z (or_intror Hz)) H2). }
  exact (G members kids (incl_refl members) Hk).
Qed.

End t.
