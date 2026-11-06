(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* omx-clap-core/fuzz_preset, kit: THE FREE ORDER of pj_free (src/preset_file.c:334-350), pure and image-free, and
   its one fact against the model.
   proves no function (kind: pure definitions and lemmas).

   ONE HOME (the kit owner's ruling, 2026-10-29). These definitions and proofs are TAKEN BY PATH, verbatim, from
   the image-B pj_free lane, commit ab365ca51d33:
   - lib/B/Prog/pj_free_defs.v (blob bd4c58302fde) Section ord: pf_oitemsR, pj_oshapeR, pj_foR;
   - lib/B/Prog/pj_free_pure.v (blob b54814f20036) Section shape, in full: pj_foR_fdR / pj_fdR_foR (the order list of
     a pj_fdR tree exists and is a permutation of its block list), the lblk and frame laws, and pj_free_fo.
   They move here because lib/A/PRH_FnPj.v's tpj_free_specX and tpj_set_specX now NAME the order list F (the kit's
   texts may not Require a lane file), so the lane keeps no second spelling: pj_free_defs.v drops its Section ord and
   pj_free_pure.v its Section shape, and both cite this file. Nothing here mentions an image, a machine state, an
   address or a CfParams; the observer (pf_obs / pf_reach / pf_safe), which is walk machinery, stays in the lane.

   WHAT THE ORDER IS. pj_free frees, for each slot i of the node, first the subtree of kids[i] (its own order list),
   then keys[i]; then kids, keys and str (the C order :340-348, measured in the B' walker's internal file PJFREE-ORDER.md section 1d).
   pj_foR m lblk d p D F is PRH_Reader.pj_fdR with that list F added: same tree shape, F a permutation of the block
   list D. pj_free_fo: for a node read back from the writer's text (pj_nodeR p t D whose requests are the model's
   PresetReqAtNoMiss.tblk t), F's requests are PresetReqAt.fo t, in order - the list the model's HBulk event carries
   (lib/Spec/PresetReqAt.v blob 379c33e9e482, the Spec of record; the kit's earlier blob built that event from the
   LIVE-BLOCK list, which is a different order). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK11 YP09 YI00 YI04.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require Import PjTree.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PresetReqAt PresetReqAtNoMiss.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Reader.
Import ListNotations.
Local Open Scope Z_scope.

(* ================================================================ the free order (pure) *)
Section ord.
Variable segs : list Segment.

(* pf_itemsR (PRH_Reader.v:158) with the order list: slot i frees its value's subtree (F1), then its key (Dk) *)
Fixpoint pf_oitemsR (m : word -> option byte) (lblk : Z -> Z -> Prop)
    (P : Z -> list (Z * Z) -> list (Z * Z) -> Prop) (ks : bool) (a ka : Z) (n : nat) (D F : list (Z * Z))
    {struct n} : Prop :=
  match n with
  | O => D = [] /\ F = []
  | S n' => exists Dk D1 F1 D2 F2, D = Dk ++ D1 ++ D2 /\ F = F1 ++ Dk ++ F2 /\ pj_keyR segs m lblk ks ka Dk /\
      P a D1 F1 /\ pf_oitemsR m lblk P ks (a + 56) (ka + 8) n' D2 F2
  end.

(* pj_fshapeR (PRH_Reader.v:166) with the order list: the slots' list, then kids, keys, str *)
Definition pj_oshapeR (m : word -> option byte) (lblk : Z -> Z -> Prop)
    (Pi : bool -> Z -> Z -> Z -> list (Z * Z) -> list (Z * Z) -> Prop) (p : Z) (D F : list (Z * Z)) : Prop :=
  NoDup D /\ pj_apartR D p /\
  exists ty num str kids keys n cap ks Ds Dk Dy Di Fi,
    pj_hdrR segs m p ty num str kids keys n cap /\
    (str = 0 /\ Ds = [] \/ exists k, lblk str k /\ Ds = [(str, k)]) /\
    (kids = 0 /\ n = 0 /\ Dk = [] \/ exists k, lblk kids k /\ 56 * n <= k /\ Dk = [(kids, k)]) /\
    (keys = 0 /\ ks = false /\ Dy = [] \/ ks = true /\ exists k, lblk keys k /\ 8 * n <= k /\ Dy = [(keys, k)]) /\
    Permutation D (Ds ++ Dk ++ Dy ++ Di) /\
    Pi ks kids keys n Di Fi /\ F = Fi ++ Dk ++ Dy ++ Ds.

(* pj_fdR (PRH_Reader.v:178) with F, the blocks of D in pj_free's order *)
Fixpoint pj_foR (m : word -> option byte) (lblk : Z -> Z -> Prop) (d : nat) (p : Z) (D F : list (Z * Z))
    {struct d} : Prop :=
  match d with
  | O => pj_oshapeR m lblk (fun _ _ _ n Di Fi => n = 0 /\ Di = [] /\ Fi = []) p D F
  | S d' => pj_oshapeR m lblk
      (fun ks kids keys n Di Fi => pf_oitemsR m lblk (pj_foR m lblk d') ks kids keys (Z.to_nat n) Di Fi) p D F
  end.
End ord.

(* ---- the ordered shape ---- *)
Section shape.
Variable segs : list Segment.

(* the order list forgets to the kit's item list (F a permutation of D), for any per-slot relations *)
Lemma pf_oitems_items : forall m lblk (P : Z -> list (Z * Z) -> list (Z * Z) -> Prop)
    (Q : Z -> list (Z * Z) -> Prop) ks n a ka D F,
  (forall a D F, P a D F -> Q a D /\ Permutation F D) ->
  pf_oitemsR segs m lblk P ks a ka n D F -> pf_itemsR segs m lblk Q ks a ka n D /\ Permutation F D.
Proof.
intros m lblk P Q ks n. induction n as [|n IH]; intros a ka D F HPQ H; cbn [pf_oitemsR pf_itemsR] in H |- *.
- destruct H as [-> ->]. split; [reflexivity | apply perm_nil].
- destruct H as (Dk & D1 & F1 & D2 & F2 & -> & -> & Hk & H1 & H2).
  destruct (HPQ a D1 F1 H1) as [Q1 P1]. destruct (IH (a + 56) (ka + 8) D2 F2 HPQ H2) as [Q2 P2].
  split.
  + exists Dk, D1, D2. split; [reflexivity|]. split; [exact Hk|]. split; [exact Q1 | exact Q2].
  + transitivity (Dk ++ F1 ++ F2); [apply Permutation_app_swap_app|].
    apply Permutation_app_head. apply Permutation_app; [exact P1 | exact P2].
Qed.

(* the kit's item list has an order list, for any per-slot relations *)
Lemma pf_items_oitems : forall m lblk (P : Z -> list (Z * Z) -> list (Z * Z) -> Prop)
    (Q : Z -> list (Z * Z) -> Prop) ks n a ka D,
  (forall a D, Q a D -> exists F, P a D F) ->
  pf_itemsR segs m lblk Q ks a ka n D -> exists F, pf_oitemsR segs m lblk P ks a ka n D F.
Proof.
intros m lblk P Q ks n. induction n as [|n IH]; intros a ka D HQP H; cbn [pf_itemsR] in H.
- exists []. cbn [pf_oitemsR]. split; [exact H | reflexivity].
- destruct H as (Dk & D1 & D2 & -> & Hk & H1 & H2).
  destruct (HQP a D1 H1) as [F1 HF1]. destruct (IH (a + 56) (ka + 8) D2 HQP H2) as [F2 HF2].
  exists (F1 ++ Dk ++ F2). cbn [pf_oitemsR]. exists Dk, D1, F1, D2, F2.
  split; [reflexivity|]. split; [reflexivity|]. split; [exact Hk|]. split; [exact HF1 | exact HF2].
Qed.

(* the node's order list Fi ++ Dk ++ Dy ++ Ds is a permutation of its block list *)
Lemma pf_perm_shape : forall Fi Di Dk Dy Ds D : list (Z * Z),
  Permutation Fi Di -> Permutation D (Ds ++ Dk ++ Dy ++ Di) -> Permutation (Fi ++ Dk ++ Dy ++ Ds) D.
Proof.
intros Fi Di Dk Dy Ds D HF HD.
transitivity (Ds ++ Dk ++ Dy ++ Di); [|symmetry; exact HD].
transitivity (Di ++ Dk ++ Dy ++ Ds); [apply Permutation_app_tail; exact HF|].
transitivity ((Dk ++ Dy ++ Ds) ++ Di); [apply Permutation_app_comm|].
rewrite <- !app_assoc.
rewrite (app_assoc Dk Dy (Ds ++ Di)), (app_assoc Dk Dy Di).
apply Permutation_app_swap_app.
Qed.

Lemma pj_foR_fdR : forall m lblk d p D F,
  pj_foR segs m lblk d p D F -> pj_fdR segs m lblk d p D /\ Permutation F D.
Proof.
intros m lblk d. induction d as [|d IH]; intros p D F H;
  cbn [pj_foR pj_fdR pj_oshapeR pj_fshapeR] in H |- *;
  destruct H as (Hnd & Hap & ty & num & str & kids & keys & n & cap & ks & Ds & Dk & Dy & Di & Fi &
    Hh & Hs & Hk & Hy & Hp & HPi & ->).
- destruct HPi as (Hn & HDi & HFi). subst Di Fi. split.
  + split; [exact Hnd|]. split; [exact Hap|]. exists ty, num, str, kids, keys, n, cap, ks, Ds, Dk, Dy, [].
    split; [exact Hh|]. split; [exact Hs|]. split; [exact Hk|]. split; [exact Hy|]. split; [exact Hp|].
    split; [exact Hn | reflexivity].
  + eapply pf_perm_shape; [apply perm_nil | exact Hp].
- destruct (pf_oitems_items m lblk (pj_foR segs m lblk d) (pj_fdR segs m lblk d) ks (Z.to_nat n) kids keys
    Di Fi IH HPi) as [Q1 P1].
  split.
  + split; [exact Hnd|]. split; [exact Hap|]. exists ty, num, str, kids, keys, n, cap, ks, Ds, Dk, Dy, Di.
    split; [exact Hh|]. split; [exact Hs|]. split; [exact Hk|]. split; [exact Hy|]. split; [exact Hp|].
    exact Q1.
  + eapply pf_perm_shape; [exact P1 | exact Hp].
Qed.

Lemma pj_fdR_foR : forall m lblk d p D, pj_fdR segs m lblk d p D -> exists F, pj_foR segs m lblk d p D F.
Proof.
intros m lblk d. induction d as [|d IH]; intros p D H;
  cbn [pj_foR pj_fdR pj_oshapeR pj_fshapeR] in H |- *;
  destruct H as (Hnd & Hap & ty & num & str & kids & keys & n & cap & ks & Ds & Dk & Dy & Di &
    Hh & Hs & Hk & Hy & Hp & HPi).
- destruct HPi as [Hn HDi].
  exists ([] ++ Dk ++ Dy ++ Ds). split; [exact Hnd|]. split; [exact Hap|].
  exists ty, num, str, kids, keys, n, cap, ks, Ds, Dk, Dy, Di, [].
  split; [exact Hh|]. split; [exact Hs|]. split; [exact Hk|]. split; [exact Hy|]. split; [exact Hp|].
  split; [split; [exact Hn | split; [exact HDi | reflexivity]] | reflexivity].
- destruct (pf_items_oitems m lblk (pj_foR segs m lblk d) (pj_fdR segs m lblk d) ks (Z.to_nat n) kids keys
    Di IH HPi) as [Fi HFi].
  exists (Fi ++ Dk ++ Dy ++ Ds). split; [exact Hnd|]. split; [exact Hap|].
  exists ty, num, str, kids, keys, n, cap, ks, Ds, Dk, Dy, Di, Fi.
  split; [exact Hh|]. split; [exact Hs|]. split; [exact Hk|]. split; [exact Hy|]. split; [exact Hp|].
  split; [exact HFi | reflexivity].
Qed.

(* every block of an order list is lblk's, for any per-slot relation whose blocks are *)
Lemma pf_oitems_lblk : forall m lblk (P : Z -> list (Z * Z) -> list (Z * Z) -> Prop) ks n a ka D F,
  (forall a D F, P a D F -> forall x k, In (x, k) D -> lblk x k) ->
  pf_oitemsR segs m lblk P ks a ka n D F -> forall x k, In (x, k) D -> lblk x k.
Proof.
intros m lblk P ks n. induction n as [|n IH]; intros a ka D F HP H x k Hin; cbn [pf_oitemsR] in H.
- destruct H as [-> _]. destruct Hin.
- destruct H as (Dk & D1 & F1 & D2 & F2 & -> & _ & Hk & H1 & H2).
  apply in_app_or in Hin. destruct Hin as [Hin|Hin]; [|apply in_app_or in Hin; destruct Hin as [Hin|Hin]].
  + unfold pj_keyR in Hk. destruct ks; cbv beta iota in Hk.
    * destruct Hk as (y & _ & [(_ & ->) | (k' & Hl & ->)]); [destruct Hin|].
      destruct Hin as [Hin|[]]. injection Hin as <- <-. exact Hl.
    * subst Dk. destruct Hin.
  + exact (HP a D1 F1 H1 x k Hin).
  + exact (IH (a + 56) (ka + 8) D2 F2 HP H2 x k Hin).
Qed.

(* the node's own blocks are lblk's; its items' blocks are when Di's are *)
Lemma pf_shape_lblk : forall (lblk : Z -> Z -> Prop) str kids keys (n : Z) (ks : bool)
    (Ds Dk Dy Di : list (Z * Z)) a k,
  (str = 0 /\ Ds = [] \/ exists k, lblk str k /\ Ds = [(str, k)]) ->
  (kids = 0 /\ n = 0 /\ Dk = [] \/ exists k, lblk kids k /\ 56 * n <= k /\ Dk = [(kids, k)]) ->
  (keys = 0 /\ ks = false /\ Dy = [] \/ ks = true /\ exists k, lblk keys k /\ 8 * n <= k /\ Dy = [(keys, k)]) ->
  (forall x k, In (x, k) Di -> lblk x k) ->
  In (a, k) (Ds ++ Dk ++ Dy ++ Di) -> lblk a k.
Proof.
intros lblk str kids keys n ks Ds Dk Dy Di a k Hs Hk Hy HDi Hin.
apply in_app_or in Hin. destruct Hin as [Hin|Hin].
{ destruct Hs as [(_ & ->)|(k' & Hl & ->)]; [destruct Hin|].
  destruct Hin as [Hin|[]]. injection Hin as <- <-. exact Hl. }
apply in_app_or in Hin. destruct Hin as [Hin|Hin].
{ destruct Hk as [(_ & _ & ->)|(k' & Hl & _ & ->)]; [destruct Hin|].
  destruct Hin as [Hin|[]]. injection Hin as <- <-. exact Hl. }
apply in_app_or in Hin. destruct Hin as [Hin|Hin].
{ destruct Hy as [(_ & _ & ->)|(_ & k' & Hl & _ & ->)]; [destruct Hin|].
  destruct Hin as [Hin|[]]. injection Hin as <- <-. exact Hl. }
exact (HDi a k Hin).
Qed.

Lemma pj_foR_lblk : forall m lblk d p D F, pj_foR segs m lblk d p D F -> forall a k, In (a, k) D -> lblk a k.
Proof.
intros m lblk d. induction d as [|d IH]; intros p D F H a k Hin; cbn [pj_foR pj_oshapeR] in H;
  destruct H as (_ & _ & ty & num & str & kids & keys & n & cap & ks & Ds & Dk & Dy & Di & Fi &
    _ & Hs & Hk & Hy & Hp & HPi & _);
  refine (pf_shape_lblk lblk str kids keys n ks Ds Dk Dy Di a k Hs Hk Hy _ _);
  [| eapply Permutation_in; [exact Hp | exact Hin] | | eapply Permutation_in; [exact Hp | exact Hin]].
- destruct HPi as (_ & -> & _). intros x y Hx. destruct Hx.
- exact (pf_oitems_lblk m lblk (pj_foR segs m lblk d) ks (Z.to_nat n) kids keys Di Fi IH HPi).
Qed.

Lemma pf_oitemsR_lblk : forall m lblk d ks a ka n D F,
  pf_oitemsR segs m lblk (pj_foR segs m lblk d) ks a ka n D F -> forall x k, In (x, k) D -> lblk x k.
Proof.
intros m lblk d ks a ka n D F H.
apply (pf_oitems_lblk m lblk (pj_foR segs m lblk d) ks n a ka D F); [|exact H].
intros a' D' F' H'. exact (pj_foR_lblk m lblk d a' D' F' H').
Qed.

(* the bytes an item list reads: its n structs, its n key slots (when the node is an object), its blocks *)
Definition pf_ofoot (ks : bool) (a ka : Z) (n : nat) (D : list (Z * Z)) (x : Z) : Prop :=
  (a <= x < a + 56 * Z.of_nat n) \/ (ks = true /\ ka <= x < ka + 8 * Z.of_nat n) \/
  exists b, In b D /\ pj_holdsR b x.

Lemma pf_agree_mono : forall m m' (X Y : Z -> Prop),
  pj_agreeR segs m m' X -> (forall x, Y x -> X x) -> pj_agreeR segs m m' Y.
Proof. intros m m' X Y H HYX. unfold pj_agreeR in *. intros x Hx. exact (H x (HYX x Hx)). Qed.

(* an order list survives a memory and ledger change that keeps its footprint, for per-slot relations that do *)
Lemma pf_oitems_frame : forall m m' lblk lblk' (P P' : Z -> list (Z * Z) -> list (Z * Z) -> Prop) ks n a ka D F,
  (forall a D F, P a D F -> (forall x k, In (x, k) D -> lblk' x k) -> pj_agreeR segs m m' (pj_footR a D) ->
     P' a D F) ->
  pf_oitemsR segs m lblk P ks a ka n D F ->
  (forall x k, In (x, k) D -> lblk' x k) ->
  pj_agreeR segs m m' (pf_ofoot ks a ka n D) ->
  pf_oitemsR segs m' lblk' P' ks a ka n D F.
Proof.
intros m m' lblk lblk' P P' ks n. induction n as [|n IH]; intros a ka D F HPP H HL HA;
  cbn [pf_oitemsR] in H |- *; [exact H|].
destruct H as (Dk & D1 & F1 & D2 & F2 & -> & -> & Hk & H1 & H2).
exists Dk, D1, F1, D2, F2. split; [reflexivity|]. split; [reflexivity|]. split; [|split].
- unfold pj_keyR in Hk |- *. destruct ks; cbv beta iota in Hk |- *; [|exact Hk].
  destruct Hk as (x & Hx & Hc). exists x. split.
  + apply (rd_u64_frame segs m m' ka x Hx). intros y Hy.
    refine (proj1 (HA y _)). unfold pf_ofoot. right; left. split; [reflexivity | lia].
  + destruct Hc as [Hc|(k & Hl & ->)]; [left; exact Hc|].
    right. exists k. split; [|reflexivity]. apply HL. apply in_or_app. left. apply in_eq.
- apply (HPP a D1 F1 H1).
  + intros x k Hin. apply HL. apply in_or_app. right. apply in_or_app. left. exact Hin.
  + apply (pf_agree_mono m m' _ _ HA). unfold pj_footR, pf_ofoot. intros y [Hy|(b & Hb & Hy)].
    * left. lia.
    * right. right. exists b. split; [|exact Hy].
      apply in_or_app. right. apply in_or_app. left. exact Hb.
- apply (IH (a + 56) (ka + 8) D2 F2 HPP H2).
  + intros x k Hin. apply HL. apply in_or_app. right. apply in_or_app. right. exact Hin.
  + apply (pf_agree_mono m m' _ _ HA). unfold pf_ofoot. intros y [Hy|[(Hks & Hy)|(b & Hb & Hy)]].
    * left. lia.
    * right. left. split; [exact Hks | lia].
    * right. right. exists b. split; [|exact Hy].
      apply in_or_app. right. apply in_or_app. right. exact Hb.
Qed.

(* the ordered node shape survives a memory and ledger change that keeps its footprint, given its items do *)
Lemma pf_oshape_frame : forall m m' lblk lblk'
    (Pi Pi' : bool -> Z -> Z -> Z -> list (Z * Z) -> list (Z * Z) -> Prop) p D F,
  pj_oshapeR segs m lblk Pi p D F ->
  (forall a k, In (a, k) D -> lblk' a k) ->
  pj_agreeR segs m m' (pj_footR p D) ->
  (forall ks kids keys n Dk Dy Di Fi,
     (kids = 0 /\ n = 0 /\ Dk = [] \/ exists k, lblk kids k /\ 56 * n <= k /\ Dk = [(kids, k)]) ->
     (keys = 0 /\ ks = false /\ Dy = [] \/ ks = true /\ exists k, lblk keys k /\ 8 * n <= k /\ Dy = [(keys, k)]) ->
     (forall b, In b (Dk ++ Dy ++ Di) -> In b D) ->
     Pi ks kids keys n Di Fi -> Pi' ks kids keys n Di Fi) ->
  pj_oshapeR segs m' lblk' Pi' p D F.
Proof.
intros m m' lblk lblk' Pi Pi' p D F H HL HA HPi'. unfold pj_oshapeR in H |- *.
destruct H as (Hnd & Hap & ty & num & str & kids & keys & n & cap & ks & Ds & Dk & Dy & Di & Fi &
  Hh & Hs & Hk & Hy & Hp & HPi & ->).
assert (HinD : forall b, In b (Ds ++ Dk ++ Dy ++ Di) -> In b D)
  by (intros b Hb; eapply Permutation_in; [apply Permutation_sym; exact Hp | exact Hb]).
split; [exact Hnd|]. split; [exact Hap|].
exists ty, num, str, kids, keys, n, cap, ks, Ds, Dk, Dy, Di, Fi.
split.
{ apply (pj_hdrR_frame segs m m' p ty num str kids keys n cap Hh).
  apply (pf_agree_mono m m' _ _ HA). unfold pj_footR. intros x Hx. left. exact Hx. }
split.
{ destruct Hs as [Hs|(k & _ & ->)]; [left; exact Hs|].
  right. exists k. split; [|reflexivity]. apply HL. apply HinD. apply in_or_app. left. apply in_eq. }
split.
{ destruct Hk as [Hk'|(k & _ & Hnk & ->)]; [left; exact Hk'|].
  right. exists k. split; [|split; [exact Hnk | reflexivity]]. apply HL. apply HinD.
  apply in_or_app. right. apply in_or_app. left. apply in_eq. }
split.
{ destruct Hy as [Hy'|(Hks & k & _ & Hnk & ->)]; [left; exact Hy'|].
  right. split; [exact Hks|]. exists k. split; [|split; [exact Hnk | reflexivity]]. apply HL. apply HinD.
  apply in_or_app. right. apply in_or_app. right. apply in_or_app. left. apply in_eq. }
split; [exact Hp|].
split; [|reflexivity].
apply (HPi' ks kids keys n Dk Dy Di Fi Hk Hy); [|exact HPi].
intros b Hb. apply HinD. apply in_or_app. right. exact Hb.
Qed.

Lemma pj_foR_frame : forall d m m' lblk lblk' p D F,
  pj_foR segs m lblk d p D F ->
  (forall a k, In (a, k) D -> lblk' a k) ->
  pj_agreeR segs m m' (pj_footR p D) ->
  pj_foR segs m' lblk' d p D F.
Proof.
intros d. induction d as [|d IH]; intros m m' lblk lblk' p D F H HL HA; cbn [pj_foR] in H |- *;
  apply (pf_oshape_frame m m' lblk lblk' _ _ p D F H HL HA).
- intros ks kids keys n Dk Dy Di Fi _ _ _ HPi. exact HPi.
- intros ks kids keys n Dk Dy Di Fi Hk Hy HinD HPi. cbv beta in HPi |- *.
  apply (pf_oitems_frame m m' lblk lblk' (pj_foR segs m lblk d) (pj_foR segs m' lblk' d) ks (Z.to_nat n)
    kids keys Di Fi).
  + intros a' D' F' H' HL' HA'. exact (IH m m' lblk lblk' a' D' F' H' HL' HA').
  + exact HPi.
  + intros x k Hin. apply HL. apply HinD. apply in_or_app. right. apply in_or_app. right. exact Hin.
  + apply (pf_agree_mono m m' _ _ HA). unfold pf_ofoot, pj_footR.
    intros y [Hy'|[(Hks & Hy')|(b & Hb & Hy')]].
    * destruct Hk as [(-> & -> & ->)|(k & _ & Hnk & ->)]; [cbn in Hy'; lia|].
      right. exists (kids, k). split; [apply HinD; apply in_or_app; left; apply in_eq|].
      unfold pj_holdsR; cbn [fst snd]. lia.
    * destruct Hy as [(-> & -> & ->)|(_ & k & _ & Hnk & ->)]; [discriminate Hks|].
      right. exists (keys, k).
      split; [apply HinD; apply in_or_app; right; apply in_or_app; left; apply in_eq|].
      unfold pj_holdsR; cbn [fst snd]. lia.
    * right. exists b. split; [|exact Hy']. apply HinD. apply in_or_app. right. apply in_or_app. right. exact Hb.
Qed.

Lemma pf_oitemsR_frame : forall d m m' lblk lblk' ks a ka n D F,
  pf_oitemsR segs m lblk (pj_foR segs m lblk d) ks a ka n D F ->
  (forall x k, In (x, k) D -> lblk' x k) ->
  pj_agreeR segs m m' (pf_ofoot ks a ka n D) ->
  pf_oitemsR segs m' lblk' (pj_foR segs m' lblk' d) ks a ka n D F.
Proof.
intros d m m' lblk lblk' ks a ka n D F H HL HA.
apply (pf_oitems_frame m m' lblk lblk' (pj_foR segs m lblk d) (pj_foR segs m' lblk' d) ks n a ka D F);
  [|exact H|exact HL|exact HA].
intros a' D' F' H' HL' HA'. exact (pj_foR_frame d m m' lblk lblk' a' D' F' H' HL' HA').
Qed.

(* ---- the order against the model ---- *)
#[local] Abbreviation hb := (fun b : (Z * Z)%type => snd b + PresetReqAt.HEAD).
#[local] Abbreviation tblkN := PresetReqAtNoMiss.tblk.
#[local] Abbreviation foN := PresetReqAt.fo.
#[local] Abbreviation kblkN := PresetReqAtNoMiss.kblk.

Lemma pf_app_split_len : forall (T : Type) (a x b y : list T),
  length a = length x -> a ++ b = x ++ y -> a = x /\ b = y.
Proof.
intros T a. induction a as [|h a IH]; intros [|h' x] b y L E; cbn [length app] in L, E.
- split; [reflexivity | exact E].
- discriminate L.
- discriminate L.
- injection L as L. injection E as Eh Et. destruct (IH x b y L Et) as [-> ->]. subst h'. split; reflexivity.
Qed.

(* a whole-list request equation splits where the counts force it *)
Lemma pf_map_split : forall (A B : list (Z * Z)) (X Y : list Z),
  map hb (A ++ B) = X ++ Y -> (length X <= length A)%nat -> (length Y <= length B)%nat ->
  map hb A = X /\ map hb B = Y.
Proof.
intros A B X Y E L1 L2. rewrite map_app in E.
assert (L : length (map hb A) = length X).
{ apply (f_equal (@length Z)) in E. rewrite !length_app, !length_map in E. rewrite length_map. lia. }
exact (pf_app_split_len Z _ _ _ _ L E).
Qed.

(* pj_nodeR's block count is at least tblk's (an empty container with cap > 0 has a block tblk does not) *)
Lemma pf_items_len : forall (P : Z -> jv -> list (Z * Z) -> Prop) items a Di,
  Forall (fun u => forall a D, P a u D -> (length (tblkN u) <= length D)%nat) items ->
  pj_itemsR P a items Di -> (length (concat (map tblkN items)) <= length Di)%nat.
Proof.
intros P items a Di HF. revert a Di. induction HF as [|u r Hu Hr IHr]; intros a Di Hi; cbn [pj_itemsR] in Hi.
- subst Di. cbn. lia.
- destruct Hi as (D1 & D2 & -> & H1 & H2). cbn [map concat]. rewrite !length_app.
  assert (L1 : (length (tblkN u) <= length D1)%nat) by exact (Hu a D1 H1).
  pose proof (IHr (a + 56) D2 H2). lia.
Qed.

Lemma pf_mems_len : forall m lblk (P : Z -> jv -> list (Z * Z) -> Prop) ms a ka Di,
  Forall (fun mm => forall a D, P a (snd mm) D -> (length (tblkN (snd mm)) <= length D)%nat) ms ->
  pj_memsR segs m lblk P a ka ms Di ->
  (length (concat (map (fun mm => kblkN (fst mm) :: tblkN (snd mm)) ms)) <= length Di)%nat.
Proof.
intros m lblk P ms a ka Di HF. revert a ka Di.
induction HF as [|[nm u] r Hu Hr IHr]; intros a ka Di Hi; cbn [pj_memsR] in Hi.
- subst Di. cbn. lia.
- destruct Hi as (x & k & D1 & D2 & -> & _ & _ & H1 & H2). cbn [map concat fst snd app length].
  rewrite !length_app.
  assert (L1 : (length (tblkN u) <= length D1)%nat) by exact (Hu a D1 H1).
  pose proof (IHr (a + 56) (ka + 8) D2 H2). lia.
Qed.

Lemma pf_node_len : forall m lblk t p D, pj_nodeR segs m lblk p t D -> (length (tblkN t) <= length D)%nat.
Proof.
intros m lblk t. induction t as [| | | txt bits | s | items IH | ms IH] using jv_ind'; intros p D HN;
  cbn [pj_nodeR] in HN; destruct HN as (_ & _ & num & str & kids & keys & nn & cap & _ & HB).
- cbn. lia.
- cbn. lia.
- cbn. lia.
- destruct HB as (_ & _ & _ & _ & _ & k & _ & ->). cbn. lia.
- destruct HB as (_ & _ & _ & _ & k & _ & ->). cbn. lia.
- destruct HB as (_ & _ & En & Hc & Hcap & Di & -> & Hi).
  pose proof (pf_items_len (pj_nodeR segs m lblk) items kids Di IH Hi) as L.
  change (tblkN (JArr items)) with
    (PresetReqAt.arrz false (PresetReqAtNoMiss.capf 0 0 (length items)) ++ concat (map tblkN items)).
  rewrite !length_app.
  destruct items as [|u r].
  + cbn. lia.
  + destruct Hcap as [(-> & _)|(Hcp & _)]; [cbn [length] in En; lia|].
    rewrite (proj2 (Z.eqb_neq cap 0)) by lia.
    destruct (PresetReqAtNoMiss.capf 0 0 (length (u :: r))) as [|c]; cbn [PresetReqAt.arrz length]; lia.
- destruct HB as (_ & En & Hc & Hcap & Di & -> & Hi).
  pose proof (pf_mems_len m lblk (pj_nodeR segs m lblk) ms kids keys Di IH Hi) as L.
  change (tblkN (JObj ms)) with
    (PresetReqAt.arrz true (PresetReqAtNoMiss.capf 0 0 (length ms)) ++
     concat (map (fun mm => kblkN (fst mm) :: tblkN (snd mm)) ms)).
  rewrite !length_app.
  destruct ms as [|mm r].
  + cbn. lia.
  + destruct Hcap as [(-> & _)|(Hcp & _)]; [cbn [length] in En; lia|].
    rewrite (proj2 (Z.eqb_neq cap 0)) by lia.
    destruct (PresetReqAtNoMiss.capf 0 0 (length (mm :: r))) as [|c]; cbn [PresetReqAt.arrz length]; lia.
Qed.

Lemma pf_items_len' : forall m lblk items a Di,
  pj_itemsR (pj_nodeR segs m lblk) a items Di -> (length (concat (map tblkN items)) <= length Di)%nat.
Proof.
intros m lblk items a Di Hi. apply (pf_items_len (pj_nodeR segs m lblk) items a Di); [|exact Hi].
apply Forall_forall. intros u _ a' D H. exact (pf_node_len m lblk u a' D H).
Qed.

Lemma pf_mems_len' : forall m lblk ms a ka Di,
  pj_memsR segs m lblk (pj_nodeR segs m lblk) a ka ms Di ->
  (length (concat (map (fun mm => kblkN (fst mm) :: tblkN (snd mm)) ms)) <= length Di)%nat.
Proof.
intros m lblk ms a ka Di Hi. apply (pf_mems_len m lblk (pj_nodeR segs m lblk) ms a ka Di); [|exact Hi].
apply Forall_forall. intros mm _ a' D H. exact (pf_node_len m lblk (snd mm) a' D H).
Qed.

(* a node with no kids, no keys, no items: its order list is its block list *)
Lemma pfo_leaf : forall m lblk n p ty num str (Ds : list (Z * Z)),
  NoDup Ds -> pj_apartR Ds p -> pj_hdrR segs m p ty num str 0 0 0 0 ->
  (str = 0 /\ Ds = [] \/ exists k, lblk str k /\ Ds = [(str, k)]) ->
  pj_foR segs m lblk n p Ds Ds.
Proof.
intros m lblk n p ty num str Ds Hnd Hap Hh Hs.
destruct n as [|d]; cbn [pj_foR pj_oshapeR]; (split; [exact Hnd|]); (split; [exact Hap|]);
  exists ty, num, str, 0, 0, 0, 0, false, Ds, [], [], [], [];
  (split; [exact Hh|]); (split; [exact Hs|]);
  (split; [left; split; [reflexivity | split; reflexivity]|]);
  (split; [left; split; [reflexivity | split; reflexivity]|]);
  (split; [cbn [app]; rewrite app_nil_r; apply Permutation_refl|]);
  (split; [|reflexivity]).
- split; [reflexivity | split; reflexivity].
- cbn. split; reflexivity.
Qed.

(* the statement of pj_free_fo for one tree *)
Definition pfo_mot m lblk (t : jv) : Prop :=
  forall p D, pj_nodeR segs m lblk p t D -> map hb D = tblkN t ->
  forall n, (PjTree.depth t <= n)%nat -> exists F, pj_foR segs m lblk n p D F /\ map hb F = foN t.

Lemma pfo_items : forall m lblk items, Forall (pfo_mot m lblk) items ->
  forall a ka Di d, pj_itemsR (pj_nodeR segs m lblk) a items Di ->
  map hb Di = concat (map tblkN items) ->
  (forall u, In u items -> (PjTree.depth u <= d)%nat) ->
  exists Fi, pf_oitemsR segs m lblk (pj_foR segs m lblk d) false a ka (length items) Di Fi /\
    map hb Fi = concat (map foN items).
Proof.
intros m lblk items HF. induction HF as [|u r Hu Hr IHr]; intros a ka Di d Hi HM Hd; cbn [pj_itemsR] in Hi.
- subst Di. exists []. split; [cbn [length pf_oitemsR]; split; reflexivity | reflexivity].
- destruct Hi as (D1 & D2 & -> & H1 & H2).
  cbn [map concat] in HM.
  destruct (pf_map_split D1 D2 (tblkN u) (concat (map tblkN r)) HM
    (pf_node_len m lblk u a D1 H1) (pf_items_len' m lblk r (a + 56) D2 H2)) as [E1 E2].
  destruct (Hu a D1 H1 E1 d (Hd u (or_introl eq_refl))) as (F1 & HF1 & HmF1).
  destruct (IHr (a + 56) (ka + 8) D2 d H2 E2 (fun v Hv => Hd v (or_intror Hv))) as (F2 & HF2 & HmF2).
  exists (F1 ++ [] ++ F2). split.
  + cbn [length pf_oitemsR]. exists [], D1, F1, D2, F2.
    split; [reflexivity|]. split; [reflexivity|]. split; [exact eq_refl|]. split; [exact HF1 | exact HF2].
  + cbn [map concat]. rewrite !map_app, HmF1, HmF2. reflexivity.
Qed.

Lemma pfo_mems : forall m lblk ms, Forall (fun mm => pfo_mot m lblk (snd mm)) ms ->
  forall a ka Di d, pj_memsR segs m lblk (pj_nodeR segs m lblk) a ka ms Di ->
  map hb Di = concat (map (fun mm => kblkN (fst mm) :: tblkN (snd mm)) ms) ->
  (forall nm u, In (nm, u) ms -> (PjTree.depth u <= d)%nat) ->
  exists Fi, pf_oitemsR segs m lblk (pj_foR segs m lblk d) true a ka (length ms) Di Fi /\
    map hb Fi = concat (map (fun mm => foN (snd mm) ++ [kblkN (fst mm)]) ms).
Proof.
intros m lblk ms HF. induction HF as [|[nm u] r Hu Hr IHr]; intros a ka Di d Hi HM Hd; cbn [pj_memsR] in Hi.
- subst Di. exists []. split; [cbn [length pf_oitemsR]; split; reflexivity | reflexivity].
- destruct Hi as (x & k & D1 & D2 & -> & Hx & Hcs & H1 & H2).
  cbn [map concat fst snd app] in HM.
  injection HM as Ek HM2.
  destruct (pf_map_split D1 D2 (tblkN u) (concat (map (fun mm => kblkN (fst mm) :: tblkN (snd mm)) r)) HM2
    (pf_node_len m lblk u a D1 H1) (pf_mems_len' m lblk r (a + 56) (ka + 8) D2 H2)) as [E1 E2].
  destruct (Hu a D1 H1 E1 d (Hd nm u (or_introl eq_refl))) as (F1 & HF1 & HmF1).
  destruct (IHr (a + 56) (ka + 8) D2 d H2 E2 (fun nm' v Hv => Hd nm' v (or_intror Hv))) as (F2 & HF2 & HmF2).
  exists (F1 ++ [(x, k)] ++ F2). split.
  + cbn [length pf_oitemsR]. exists [(x, k)], D1, F1, D2, F2.
    split; [reflexivity|]. split; [reflexivity|]. split.
    * cbn [pj_keyR]. exists x. split; [exact Hx|]. right. exists k. split; [exact (proj1 Hcs) | reflexivity].
    * split; [exact HF1 | exact HF2].
  + rewrite !map_app, HmF1, HmF2. cbn [map concat fst snd]. rewrite <- app_assoc. rewrite Ek. reflexivity.
Qed.

Lemma pfo_all : forall m lblk t, pfo_mot m lblk t.
Proof.
intros m lblk t. induction t as [| | | txt bits | s | items IH | ms IH] using jv_ind';
  unfold pfo_mot; intros p D HN HM n Hd; cbn [pj_nodeR] in HN;
  destruct HN as (Hnd & Hap & num & str & kids & keys & nn & cap & Hh & HB).
- destruct HB as (-> & -> & -> & -> & -> & ->). exists []. split; [|reflexivity].
  exact (pfo_leaf m lblk n p _ num 0 [] Hnd Hap Hh (or_introl (conj eq_refl eq_refl))).
- destruct HB as (-> & -> & -> & -> & -> & ->). exists []. split; [|reflexivity].
  exact (pfo_leaf m lblk n p _ num 0 [] Hnd Hap Hh (or_introl (conj eq_refl eq_refl))).
- destruct HB as (-> & -> & -> & -> & -> & ->). exists []. split; [|reflexivity].
  exact (pfo_leaf m lblk n p _ num 0 [] Hnd Hap Hh (or_introl (conj eq_refl eq_refl))).
- destruct HB as (_ & -> & -> & -> & -> & k & Hcs & ->). exists [(str, k)]. split; [|exact HM].
  exact (pfo_leaf m lblk n p _ num str [(str, k)] Hnd Hap Hh
    (or_intror (ex_intro _ k (conj (proj1 Hcs) eq_refl)))).
- destruct HB as (-> & -> & -> & -> & k & Hcs & ->). exists [(str, k)]. split; [|exact HM].
  exact (pfo_leaf m lblk n p _ num str [(str, k)] Hnd Hap Hh
    (or_intror (ex_intro _ k (conj (proj1 Hcs) eq_refl)))).
- destruct HB as (Es & Ek & En & Hc & Hcap & Di & ED & Hi).
  destruct n as [|d]; [cbn [PjTree.depth] in Hd; lia|].
  assert (Hdep : forall u, In u items -> (PjTree.depth u <= d)%nat)
    by (intros u Hu; pose proof (PjTree.depth_item items u Hu); lia).
  destruct Hcap as [(-> & ->)|(Hcp & Hlk)].
  + destruct items as [|u r]; [|cbn [length] in En; lia].
    cbn [pj_itemsR] in Hi. subst Di. cbn in ED. subst D. subst str keys.
    assert (Hn0 : nn = 0) by (cbn [length] in En; lia). subst nn.
    exists []. split; [|reflexivity].
    exact (pfo_leaf m lblk (S d) p _ num 0 [] Hnd Hap Hh (or_introl (conj eq_refl eq_refl))).
  + rewrite (proj2 (Z.eqb_neq cap 0)) in ED by lia. subst D.
    assert (ET : tblkN (JArr items) =
      PresetReqAt.arrz false (PresetReqAtNoMiss.capf 0 0 (length items)) ++ concat (map tblkN items))
      by reflexivity.
    rewrite ET in HM. cbn [map app fst snd] in HM.
    pose proof (pf_items_len' m lblk items kids Di Hi) as Hlen.
    destruct (PresetReqAtNoMiss.capf 0 0 (length items)) as [|c] eqn:EC.
    * cbn [PresetReqAt.arrz app] in HM. apply (f_equal (@length Z)) in HM. cbn [length] in HM.
      rewrite length_map in HM. lia.
    * assert (EA : PresetReqAt.arrz false (S c) = [Z.of_nat (56 * S c)%nat + PresetReqAt.HEAD]) by reflexivity.
      rewrite EA in HM. cbn [app] in HM. injection HM as Ecap HDi.
      destruct (pfo_items m lblk items IH kids keys Di d Hi HDi Hdep) as (Fi & HFi & HmFi).
      exists (Fi ++ [(kids, 56 * cap)] ++ [] ++ []). split.
      -- cbn [pj_foR pj_oshapeR]. split; [exact Hnd|]. split; [exact Hap|].
         exists (PjTree.tag (JArr items)), num, str, kids, keys, nn, cap, false, [], [(kids, 56 * cap)], [], Di, Fi.
         split; [exact Hh|]. split; [left; split; [exact Es | reflexivity]|].
         split; [right; exists (56 * cap); split; [exact Hlk | split; [lia | reflexivity]]|].
         split; [left; split; [exact Ek | split; reflexivity]|].
         split; [apply Permutation_refl|].
         split; [|reflexivity].
         rewrite En, Nat2Z.id. exact HFi.
      -- assert (EF : foN (JArr items) =
           concat (map foN items) ++ PresetReqAt.arrz false (PresetReqAt.ncap (length items))) by reflexivity.
         rewrite EF, PresetReqAtNoMiss.ncap_eq, EC, EA, !map_app, HmFi.
         assert (E56 : Z.of_nat (56 * S c)%nat = 56 * cap) by lia.
         rewrite E56. reflexivity.
- destruct HB as (Es & En & Hc & Hcap & Di & ED & Hi).
  destruct n as [|d]; [cbn [PjTree.depth] in Hd; lia|].
  assert (Hdep : forall nm u, In (nm, u) ms -> (PjTree.depth u <= d)%nat)
    by (intros nm u Hu; pose proof (PjTree.depth_member ms nm u Hu); lia).
  destruct Hcap as [(-> & -> & ->)|(Hcp & Hlk & Hly)].
  + destruct ms as [|mm r]; [|cbn [length] in En; lia].
    cbn [pj_memsR] in Hi. subst Di. cbn in ED. subst D. subst str.
    assert (Hn0 : nn = 0) by (cbn [length] in En; lia). subst nn.
    exists []. split; [|reflexivity].
    exact (pfo_leaf m lblk (S d) p _ num 0 [] Hnd Hap Hh (or_introl (conj eq_refl eq_refl))).
  + rewrite (proj2 (Z.eqb_neq cap 0)) in ED by lia. subst D.
    assert (ET : tblkN (JObj ms) = PresetReqAt.arrz true (PresetReqAtNoMiss.capf 0 0 (length ms)) ++
      concat (map (fun mm => kblkN (fst mm) :: tblkN (snd mm)) ms)) by reflexivity.
    rewrite ET in HM. cbn [map app fst snd] in HM.
    pose proof (pf_mems_len' m lblk ms kids keys Di Hi) as Hlen.
    destruct (PresetReqAtNoMiss.capf 0 0 (length ms)) as [|c] eqn:EC.
    * cbn [PresetReqAt.arrz app] in HM. apply (f_equal (@length Z)) in HM. cbn [length] in HM.
      rewrite length_map in HM. lia.
    * assert (EA : PresetReqAt.arrz true (S c) =
        [Z.of_nat (56 * S c)%nat + PresetReqAt.HEAD; Z.of_nat (8 * S c)%nat + PresetReqAt.HEAD]) by reflexivity.
      rewrite EA in HM. cbn [app] in HM. injection HM as Ecap Ecap8 HDi.
      destruct (pfo_mems m lblk ms IH kids keys Di d Hi HDi Hdep) as (Fi & HFi & HmFi).
      exists (Fi ++ [(kids, 56 * cap)] ++ [(keys, 8 * cap)] ++ []). split.
      -- cbn [pj_foR pj_oshapeR]. split; [exact Hnd|]. split; [exact Hap|].
         exists (PjTree.tag (JObj ms)), num, str, kids, keys, nn, cap, true, [], [(kids, 56 * cap)], [(keys, 8 * cap)],
           Di, Fi.
         split; [exact Hh|]. split; [left; split; [exact Es | reflexivity]|].
         split; [right; exists (56 * cap); split; [exact Hlk | split; [lia | reflexivity]]|].
         split; [right; split; [reflexivity|]; exists (8 * cap); split; [exact Hly | split; [lia | reflexivity]]|].
         split; [apply Permutation_refl|].
         split; [|reflexivity].
         rewrite En, Nat2Z.id. exact HFi.
      -- assert (EF : foN (JObj ms) = concat (map (fun mm => foN (snd mm) ++ [kblkN (fst mm)]) ms) ++
           PresetReqAt.arrz true (PresetReqAt.ncap (length ms))) by reflexivity.
         rewrite EF, PresetReqAtNoMiss.ncap_eq, EC, EA, !map_app, HmFi.
         assert (E56 : Z.of_nat (56 * S c)%nat = 56 * cap) by lia.
         assert (E8 : Z.of_nat (8 * S c)%nat = 8 * cap) by lia.
         rewrite E56, E8. reflexivity.
Qed.

(* THE ORDER AGAINST THE MODEL: with the writer's block sizes, pj_free's list has fo's requests, in order *)
Theorem pj_free_fo : forall m lblk p t D,
  pj_nodeR segs m lblk p t D ->
  map (fun b => snd b + PresetReqAt.HEAD) D = PresetReqAtNoMiss.tblk t ->
  forall n, (PjTree.depth t <= n)%nat ->
  exists F, pj_foR segs m lblk n p D F /\ map (fun b => snd b + PresetReqAt.HEAD) F = PresetReqAt.fo t.
Proof. intros m lblk p t D HN HM n Hd. exact (pfo_all m lblk t p D HN HM n Hd). Qed.
End shape.
