(* fuzz_preset, program walks (slice S6, for every reader / writer walk): the FRAME lemmas of PRH_Reader.v's tree
   predicates. A walk that keeps a tree across a step (a call, a store elsewhere) carries it to the new memory when
   the memory agrees on the tree's footprint: the 56-byte header and the blocks D (strings, kids arrays, keys arrays),
   bytes equal and writable bytes still writable. Transcribed from preset's plain lib/Prog/CrsNode.v:39-134
   (cn_u64 / cn_hdr / cn_cstr_mframe / cn_node_mframe over plain PjStruct.pj_node), restated over PRH_Reader.v's
   pj_nodeR / pj_fdR / pj_zeroR (rd_u64, rd_u32, rd_rw, garr8 over a memory m); no plain lemma is cited.
   The footprint is PRH_Reader.v's pj_footR (:208-209), restated here as pjx_foot with the same body; this file
   needs no image or allocator context. Image-free, allocator-free: no address, no numeral but the node layout
   (LENGTH: 56 node bytes, 8 / 4 field widths, 16 / 24 / 32 / 40 / 48 field offsets, 8 key-pointer stride). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK11 YP09 YI00 YI04.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require Import PjTree PjGrammar.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Reader.
Import ListNotations.
Local Open Scope Z_scope.

Section e.
Variable segs : list Segment.

(* the bytes a node's header and its blocks cover (PRH_Reader.v's pj_footR, :208-209) *)
Definition pjx_foot (p : Z) (D : list (Z * Z)) (x : Z) : Prop :=
  (p <= x < p + 56) \/ exists b, In b D /\ pj_holdsR b x.

(* two memories agree on a byte set: the byte values, and a writable byte stays writable *)
Definition pjx_agree (m m' : word -> option byte) (X : Z -> Prop) : Prop :=
  forall x, X x -> mbyte segs m' x = mbyte segs m x /\ (writable_at segs m x -> writable_at segs m' x).

Lemma pjx_val : forall m m' a n v, val_mem segs m a n v ->
  (forall x, a <= x < a + Z.of_nat n -> mbyte segs m' x = mbyte segs m x) -> val_mem segs m' a n v.
Proof. intros m m' a n v Hv Hfr k Hk. rewrite Hfr by lia. exact (Hv k Hk). Qed.

Lemma pjx_u64 : forall m m' a v, rd_u64 segs m a v ->
  (forall x, a <= x < a + 8 -> mbyte segs m' x = mbyte segs m x) -> rd_u64 segs m' a v.
Proof.
intros m m' a v (Hr & Hv) E. split; [exact Hr|]. apply (pjx_val m m' a 8 v Hv). intros x Hx. apply E. cbn in Hx. lia.
Qed.

Lemma pjx_u32 : forall m m' a v, rd_u32 segs m a v ->
  (forall x, a <= x < a + 4 -> mbyte segs m' x = mbyte segs m x) -> rd_u32 segs m' a v.
Proof.
intros m m' a v (Hr & Hv) E. split; [exact Hr|]. apply (pjx_val m m' a 4 v Hv). intros x Hx. apply E. cbn in Hx. lia.
Qed.

Lemma pjx_garr8 : forall m m' a l, garr8 segs m a l ->
  (forall x, a <= x < a + Z.of_nat (length l) -> mbyte segs m' x = mbyte segs m x) -> garr8 segs m' a l.
Proof.
intros m m' a l H E j Hj. destruct (H j Hj) as [Hv Hr]. split; [|exact Hr].
apply (pjx_val m m' (a + Z.of_nat j) 1 (nth j l 0) Hv). intros x Hx. apply E. cbn in Hx. lia.
Qed.

Lemma pjx_hdr : forall m m' p ty num str kids keys n cap,
  pj_hdrR segs m p ty num str kids keys n cap -> pjx_agree m m' (fun x => p <= x < p + 56) ->
  pj_hdrR segs m' p ty num str kids keys n cap.
Proof.
intros m m' p ty num str kids keys n cap ((Ha & Hrw) & T & N & Sx & K & Y & Nn & C) E.
assert (F : forall a w, p <= a -> a + w <= p + 56 -> forall x, a <= x < a + w -> mbyte segs m' x = mbyte segs m x)
  by (intros a w H1 H2 x Hx; apply (proj1 (E x ltac:(lia)))).
split; [split; [exact Ha | intros x Hx; apply (proj2 (E x Hx)); exact (Hrw x Hx)]|].
split; [apply (pjx_u32 m m' p ty T); apply (F p 4); lia|].
split; [apply (pjx_u64 m m' (p + 8) num N); apply (F (p + 8) 8); lia|].
split; [apply (pjx_u64 m m' (p + 16) str Sx); apply (F (p + 16) 8); lia|].
split; [apply (pjx_u64 m m' (p + 24) kids K); apply (F (p + 24) 8); lia|].
split; [apply (pjx_u64 m m' (p + 32) keys Y); apply (F (p + 32) 8); lia|].
split; [apply (pjx_u64 m m' (p + 40) n Nn); apply (F (p + 40) 8); lia|].
apply (pjx_u64 m m' (p + 48) cap C); apply (F (p + 48) 8); lia.
Qed.

Lemma pjx_cstr : forall m m' lblk a k s, pj_cstrR segs m lblk a k s ->
  (forall x, a <= x < a + k -> mbyte segs m' x = mbyte segs m x) -> pj_cstrR segs m' lblk a k s.
Proof.
intros m m' lblk a k s (Hl & Hk & Hn & Hf & Hb) E.
split; [exact Hl|]. split; [exact Hk|]. split; [exact Hn|]. split; [exact Hf|].
apply (pjx_garr8 m m' a (s ++ [0]) Hb). intros x Hx. apply E. rewrite length_app in Hx. cbn [length] in Hx. lia.
Qed.

(* the items of an array: each item at a + 56 i, with its blocks among the list's *)
Lemma pjx_items_mono : forall (P P' : Z -> jv -> list (Z * Z) -> Prop) l a D,
  pj_itemsR P a l D ->
  (forall i u D1, nth_error l i = Some u -> incl D1 D -> P (a + 56 * Z.of_nat i) u D1 -> P' (a + 56 * Z.of_nat i) u D1) ->
  pj_itemsR P' a l D.
Proof.
intros P P' l. induction l as [|u r IH]; intros a D H HP; cbn [pj_itemsR] in H |- *; [exact H|].
destruct H as (D1 & D2 & -> & H1 & H2). exists D1, D2. split; [reflexivity|]. split.
- specialize (HP 0%nat u D1 eq_refl (incl_appl D2 (incl_refl D1))).
  replace (a + 56 * Z.of_nat 0) with a in HP by lia. exact (HP H1).
- apply (IH (a + 56) D2 H2). intros i u' D1' Hi Hinc HPi.
  specialize (HP (S i) u' D1' Hi (incl_appr D1 Hinc)). replace (a + 56 * Z.of_nat (S i)) with (a + 56 + 56 * Z.of_nat i) in HP by lia.
  exact (HP HPi).
Qed.

(* the members of an object: value i at a + 56 i, key pointer i at ka + 8 i, the key string a block of the list *)
Lemma pjx_mems_mono : forall m m' lblk (P P' : Z -> jv -> list (Z * Z) -> Prop) l a ka D,
  pj_memsR segs m lblk P a ka l D ->
  (forall i nm u x k D1, nth_error l i = Some (nm, u) -> In (x, k) D -> incl D1 D ->
     rd_u64 segs m (ka + 8 * Z.of_nat i) x -> pj_cstrR segs m lblk x k nm -> P (a + 56 * Z.of_nat i) u D1 ->
     rd_u64 segs m' (ka + 8 * Z.of_nat i) x /\ pj_cstrR segs m' lblk x k nm /\ P' (a + 56 * Z.of_nat i) u D1) ->
  pj_memsR segs m' lblk P' a ka l D.
Proof.
intros m m' lblk P P' l. induction l as [|[nm u] r IH]; intros a ka D H HP; cbn [pj_memsR] in H |- *; [exact H|].
destruct H as (x & k & D1 & D2 & -> & Hx & Hc & H1 & H2). exists x, k, D1, D2. split; [reflexivity|].
pose proof (HP 0%nat nm u x k D1 eq_refl (or_introl eq_refl)
  (fun y Hy => in_cons _ _ _ (in_or_app _ _ _ (or_introl Hy)))) as HP0.
replace (a + 56 * Z.of_nat 0) with a in HP0 by lia. replace (ka + 8 * Z.of_nat 0) with ka in HP0 by lia.
destruct (HP0 Hx Hc H1) as (Hx' & Hc' & H1'). split; [exact Hx'|]. split; [exact Hc'|].
split; [exact H1'|].
apply (IH (a + 56) (ka + 8) D2 H2). intros i nm' u' x' k' D1' Hi Hin Hinc Hx2 Hc2 HP2.
specialize (HP (S i) nm' u' x' k' D1' Hi (in_cons _ _ _ (in_or_app _ _ _ (or_intror Hin)))
  (fun y Hy => in_cons _ _ _ (in_or_app _ _ _ (or_intror (Hinc y Hy))))).
replace (a + 56 * Z.of_nat (S i)) with (a + 56 + 56 * Z.of_nat i) in HP by lia.
replace (ka + 8 * Z.of_nat (S i)) with (ka + 8 + 8 * Z.of_nat i) in HP by lia.
exact (HP Hx2 Hc2 HP2).
Qed.

Lemma pjx_nth_len : forall {X} (l : list X) i u, nth_error l i = Some u -> (i < length l)%nat.
Proof. intros X l i u H. apply nth_error_Some. rewrite H. discriminate. Qed.

(* THE FRAME LEMMA of the tree: a tree whose footprint keeps its bytes (and writability) is the same tree *)
Lemma pj_nodeR_frame : forall t m m' lblk p D, pj_nodeR segs m lblk p t D ->
  pjx_agree m m' (pjx_foot p D) -> pj_nodeR segs m' lblk p t D.
Proof.
intros t. induction t as [| | | txt bits | s | items IH | members IH] using jv_ind';
  intros m m' lblk p D H HM; cbn [pj_nodeR] in H |- *;
  assert (HM1 : forall x, pjx_foot p D x -> mbyte segs m' x = mbyte segs m x) by (intros x Hx; exact (proj1 (HM x Hx)));
  destruct H as (Hn & Ha & num & str & kids & keys & n & cap & Hh & Hb);
  (split; [exact Hn|]); (split; [exact Ha|]); exists num, str, kids, keys, n, cap;
  (split; [apply (pjx_hdr m m'); [exact Hh | intros x Hx; apply HM; left; exact Hx]|]).
- exact Hb.
- exact Hb.
- exact Hb.
- destruct Hb as (E1 & E2 & E3 & E4 & E5 & k & Hc & ED).
  split; [exact E1|]. split; [exact E2|]. split; [exact E3|]. split; [exact E4|]. split; [exact E5|].
  exists k. split; [|exact ED].
  apply (pjx_cstr m m'); [exact Hc|].
  intros x Hx. apply HM1. right. exists (str, k).
  split; [subst D; left; reflexivity | unfold pj_holdsR; cbn [fst snd]; exact Hx].
- destruct Hb as (E2 & E3 & E4 & E5 & k & Hc & ED).
  split; [exact E2|]. split; [exact E3|]. split; [exact E4|]. split; [exact E5|].
  exists k. split; [|exact ED].
  apply (pjx_cstr m m'); [exact Hc|].
  intros x Hx. apply HM1. right. exists (str, k).
  split; [subst D; left; reflexivity | unfold pj_holdsR; cbn [fst snd]; exact Hx].
- destruct Hb as (Es & Ek & En & Hc & Hcap & Di & ED & Hi).
  split; [exact Es|]. split; [exact Ek|]. split; [exact En|]. split; [exact Hc|]. split; [exact Hcap|].
  assert (HDi : forall b, In b Di -> In b D) by (intros b Hb; subst D; apply in_or_app; right; exact Hb).
  exists Di. split; [exact ED|].
  apply (pjx_items_mono (pj_nodeR segs m lblk) (pj_nodeR segs m' lblk) items kids Di Hi).
  intros i u D1 Hil Hinc HP.
  pose proof (pjx_nth_len items i u Hil) as Hlt.
  assert (Hp : 0 < cap) by lia.
  assert (Hin : In (kids, 56 * cap) D).
  { subst D. rewrite (proj2 (Z.eqb_neq cap 0)) by lia. left; reflexivity. }
  rewrite Forall_forall in IH.
  apply (IH u (nth_error_In items i Hil) m m' lblk _ D1 HP).
  intros x Hx. apply HM. destruct Hx as [Hx|(b & Hb & Hx)].
  + right. exists (kids, 56 * cap). split; [exact Hin | unfold pj_holdsR; cbn [fst snd]; lia].
  + right. exists b. split; [apply HDi; apply Hinc; exact Hb | exact Hx].
- destruct Hb as (Es & En & Hc & Hcap & Di & ED & Hi).
  split; [exact Es|]. split; [exact En|]. split; [exact Hc|]. split; [exact Hcap|].
  assert (HDi : forall b, In b Di -> In b D) by (intros b Hb; subst D; apply in_or_app; right; exact Hb).
  exists Di. split; [exact ED|].
  apply (pjx_mems_mono m m' lblk (pj_nodeR segs m lblk) (pj_nodeR segs m' lblk) members kids keys Di Hi).
  intros i nm u x k D1 Hil Hxk Hinc Hx Hcs HP.
  pose proof (pjx_nth_len members i (nm, u) Hil) as Hlt.
  assert (Hp : 0 < cap) by lia.
  assert (Hin : In (kids, 56 * cap) D /\ In (keys, 8 * cap) D).
  { subst D. rewrite (proj2 (Z.eqb_neq cap 0)) by lia. split; [left; reflexivity | right; left; reflexivity]. }
  split; [|split].
  + apply (pjx_u64 m m'); [exact Hx|]. intros y Hy. apply HM1. right. exists (keys, 8 * cap).
    split; [exact (proj2 Hin) | unfold pj_holdsR; cbn [fst snd]; lia].
  + apply (pjx_cstr m m'); [exact Hcs|].
    intros y Hy. apply HM1. right. exists (x, k).
    split; [apply HDi; exact Hxk | unfold pj_holdsR; cbn [fst snd]; exact Hy].
  + rewrite Forall_forall in IH. specialize (IH (nm, u) (nth_error_In members i Hil)). cbn [snd] in IH.
    apply (IH m m' lblk _ D1 HP).
    intros y Hy. apply HM. destruct Hy as [Hy|(b & Hb & Hy)].
    * right. exists (kids, 56 * cap). split; [exact (proj1 Hin) | unfold pj_holdsR; cbn [fst snd]; lia].
    * right. exists b. split; [apply HDi; apply Hinc; exact Hb | exact Hy].
Qed.

(* the zeroed node *)
Lemma pj_zeroR_frame : forall m m' v, pj_zeroR segs m v ->
  (forall x, v <= x < v + 56 -> mbyte segs m' x = mbyte segs m x) -> pj_zeroR segs m' v.
Proof. intros m m' v H E. apply (pjx_garr8 m m' v (repeat 0 56) H). intros x Hx. apply E. cbn [length repeat] in Hx. lia. Qed.

End e.
