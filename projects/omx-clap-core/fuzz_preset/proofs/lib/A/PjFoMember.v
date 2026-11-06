(* omx-clap-core/fuzz_preset, a Theorem Labs lane for the kit owner (a Theorem Labs lane): AN OBJECT'S ORDERED FREE LIST PROJECTS TO A MEMBER'S.
   proves no function (kind: statement text).

   pj_foR_member: an object node at o read back from the writer's text (pj_nodeR o (JObj ms) D) with pj_free's order
   list F (PRH_PjOrder.pj_foR (S nn) o D F) whose requests are PresetReqAt.fo (JObj ms) IN ORDER; then the member
   i (nth_error ms i = Some (kname, vi)), the node at kids + 56 i, has an order list Fv of depth nn whose requests are
   PresetReqAt.fo vi in order. Consumer: lib/A/PRH_FnPj.v tpj_set_specX's present-key arm (the pj_free of the replaced
   value needs `map (snd + HEAD) Fv = fo vi`, ordered; a Permutation does not serve).

   THE STATEMENT IS THE KIT'S TEXT PLUS THREE PREMISES (a Theorem Labs lane's ruling, 2026-10-29). The kit's text alone is FALSE; each
   premise below closes one counterexample (hb b = snd b + 16):
   (1) rd_u64 segs m (o + 24) kids - kids is the object's own kids field. Without it the premise on Di names ANY node:
       kids + 56 i may hold an unrelated empty array with cap 5, Di = [(q, 280)]; Fv is a permutation of Di
       (pj_foR_fdR), so map hb Fv = [296] <> [] = fo (JArr []).
   (2) lblk functional (forall a k k', lblk a k -> lblk a k' -> k = k'). With kids tied but lblk str 4 and lblk str 9
       both true, vi = JStr [97;98;99]: the object holds (str, 4) (H3 holds), yet pj_nodeR at kids + 56 i also holds
       with Di = [(str, 9)] (pj_cstrR only asks k >= |s| + 1); Fv = [(str, 9)] and 25 <> 20 = fo vi.
   (3) no block at address 0 (forall a k, lblk a k -> a <> 0). With kids tied and lblk functional, take
       ms = [([34], JStr [97]); (k1, JNull)], the member value's str = 0 with lblk 0 3 (D holds (0, 3)), the key block
       (x0, 2). pj_foR may put (0, 3) in JNull's slot (its kids = 0, n = 0 arm allows a block (0, k)) and none in
       JStr's (its str = 0 arm allows none); F = [(x0, 2); (0, 3); (x1, kx1); kids; keys] and H3 holds
       ([18; 19; ..] = fo (JObj ms): fo (JStr [97]) = [18], kblk [34] = 19). The premise on Di forces Di = [(0, 3)],
       so Fv = [(0, 3)] and 19 <> 18.
   At tpj_set_specX the three come from its pj_hdrR premise at o, prh_ledger's NoDup (map fst Lam) (lblk = prh_lin
   Lam), and prh_hblock (a harness block is never at address 0).

   ROUTE. Under (2) and (3) a pj_foR tree and a pj_nodeR tree at one address have the same blocks (pfm_corr_all: every
   pointer field is read from the same memory, a nonzero one names its block with the one size lblk allows, a zero one
   names none). So each slot j of F's object arm has |F_j| = |D_j| >= |tblk v_j| = |fo v_j| (pf_node_len, fo_tblk); the
   slots line up with fo's (pfm_slots), and F_i is the member's order list, moved to Di by the same correspondence.
   Requires PRH_PjOrder (the kit); edits no file of it. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK11 YP09 YI00 YI04.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YO0f.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require Import PjTree.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PresetReqAt PresetReqAtNoMiss.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Reader PRH_PjOrder.
Import ListNotations.
Local Open Scope Z_scope.

Section fm.
Variable segs : list Segment.

(* ---- a 64-bit read is a function of memory ---- *)
Lemma pfm_rd_u64_det : forall m a v v', rd_u64 segs m a v -> rd_u64 segs m a v' -> v = v'.
Proof.
intros m a v v' (Hv & H) (Hv' & H').
assert (E : forall k, (k < 8)%nat -> YO0f.le_byte v 8 k = YO0f.le_byte v' 8 k).
{ intros k Hk. specialize (H k Hk). specialize (H' k Hk).
  assert (H2 : Z_to_bv 8 (YO0f.le_byte v 8 k) = Z_to_bv 8 (YO0f.le_byte v' 8 k)) by congruence.
  apply (f_equal (@bv_unsigned 8)) in H2. rewrite !Z_to_bv_unsigned in H2.
  rewrite !bv_wrap_small in H2;
    [exact H2 | | ]; unfold bv_modulus; change (2 ^ Z.of_N 8) with 256; unfold YO0f.le_byte;
    apply Z.mod_pos_bound; lia. }
assert (Dg : forall x, 0 <= x < 2 ^ 64 ->
  x = YO0f.le_byte x 8 0 + 256 * (YO0f.le_byte x 8 1 + 256 * (YO0f.le_byte x 8 2 + 256 * (YO0f.le_byte x 8 3 +
      256 * (YO0f.le_byte x 8 4 + 256 * (YO0f.le_byte x 8 5 + 256 * (YO0f.le_byte x 8 6 +
      256 * YO0f.le_byte x 8 7))))))).
{ intros x Hx. unfold YO0f.le_byte. change (8 * Z.of_nat 8) with 64. rewrite (Z.mod_small x) by lia.
  assert (Sh : forall y j, Z.shiftr y (8 * Z.of_nat (S j)) = Z.shiftr (Z.shiftr y (8 * Z.of_nat j)) 8).
  { intros y j. rewrite Z.shiftr_shiftr by lia. f_equal. lia. }
  rewrite !Sh. change (8 * Z.of_nat 0) with 0. rewrite Z.shiftr_0_r.
  rewrite !Z.shiftr_div_pow2 by lia. change (2 ^ 8) with 256.
  Z.div_mod_to_equations. lia. }
rewrite (Dg v Hv), (Dg v' Hv'). rewrite !E by lia. reflexivity.
Qed.

Lemma pfm_hdr_det : forall m p ty num str kids keys n cap ty' num' str' kids' keys' n' cap',
  pj_hdrR segs m p ty num str kids keys n cap -> pj_hdrR segs m p ty' num' str' kids' keys' n' cap' ->
  str' = str /\ kids' = kids /\ keys' = keys /\ n' = n.
Proof.
intros m p ty num str kids keys n cap ty' num' str' kids' keys' n' cap'
  (_ & _ & _ & S1 & K1 & Y1 & N1 & _) (_ & _ & _ & S2 & K2 & Y2 & N2 & _).
split; [exact (pfm_rd_u64_det m _ _ _ S2 S1)|]. split; [exact (pfm_rd_u64_det m _ _ _ K2 K1)|].
split; [exact (pfm_rd_u64_det m _ _ _ Y2 Y1) | exact (pfm_rd_u64_det m _ _ _ N2 N1)].
Qed.

(* ---- the ordered shape's pieces once lblk is functional and has no block at 0 ---- *)
Lemma pfm_ds0 : forall (lblk : Z -> Z -> Prop) str (Ds : list (Z * Z)),
  (forall a k, lblk a k -> a <> 0) -> str = 0 ->
  (str = 0 /\ Ds = [] \/ exists k, lblk str k /\ Ds = [(str, k)]) -> Ds = [].
Proof.
intros lblk str Ds HZ Es [(_ & HD)|(k & Hl & _)]; [exact HD | exfalso; exact (HZ str k Hl Es)].
Qed.

Lemma pfm_ds1 : forall (lblk : Z -> Z -> Prop) str k0 (Ds : list (Z * Z)),
  (forall a k k', lblk a k -> lblk a k' -> k = k') -> (forall a k, lblk a k -> a <> 0) -> lblk str k0 ->
  (str = 0 /\ Ds = [] \/ exists k, lblk str k /\ Ds = [(str, k)]) -> Ds = [(str, k0)].
Proof.
intros lblk str k0 Ds HF HZ Hl [(Es & _)|(k & Hk & ->)]; [exfalso; exact (HZ str k0 Hl Es)|].
rewrite (HF str k k0 Hk Hl). reflexivity.
Qed.

Lemma pfm_dk0 : forall (lblk : Z -> Z -> Prop) kids n (Dk : list (Z * Z)),
  (forall a k, lblk a k -> a <> 0) -> kids = 0 ->
  (kids = 0 /\ n = 0 /\ Dk = [] \/ exists k, lblk kids k /\ 56 * n <= k /\ Dk = [(kids, k)]) -> n = 0 /\ Dk = [].
Proof.
intros lblk kids n Dk HZ Ek [(_ & Hn & HD)|(k & Hl & _ & _)]; [split; [exact Hn | exact HD]|].
exfalso. exact (HZ kids k Hl Ek).
Qed.

Lemma pfm_dk1 : forall (lblk : Z -> Z -> Prop) kids n k0 (Dk : list (Z * Z)),
  (forall a k k', lblk a k -> lblk a k' -> k = k') -> (forall a k, lblk a k -> a <> 0) -> lblk kids k0 ->
  (kids = 0 /\ n = 0 /\ Dk = [] \/ exists k, lblk kids k /\ 56 * n <= k /\ Dk = [(kids, k)]) -> Dk = [(kids, k0)].
Proof.
intros lblk kids n k0 Dk HF HZ Hl [(Ek & _ & _)|(k & Hk & _ & ->)]; [exfalso; exact (HZ kids k0 Hl Ek)|].
rewrite (HF kids k k0 Hk Hl). reflexivity.
Qed.

Lemma pfm_dy0 : forall (lblk : Z -> Z -> Prop) keys n ks (Dy : list (Z * Z)),
  (forall a k, lblk a k -> a <> 0) -> keys = 0 ->
  (keys = 0 /\ ks = false /\ Dy = [] \/ ks = true /\ exists k, lblk keys k /\ 8 * n <= k /\ Dy = [(keys, k)]) ->
  ks = false /\ Dy = [].
Proof.
intros lblk keys n ks Dy HZ Ey [(_ & Hks & HD)|(_ & k & Hl & _ & _)]; [split; [exact Hks | exact HD]|].
exfalso. exact (HZ keys k Hl Ey).
Qed.

Lemma pfm_dy1 : forall (lblk : Z -> Z -> Prop) keys n k0 ks (Dy : list (Z * Z)),
  (forall a k k', lblk a k -> lblk a k' -> k = k') -> (forall a k, lblk a k -> a <> 0) -> lblk keys k0 ->
  (keys = 0 /\ ks = false /\ Dy = [] \/ ks = true /\ exists k, lblk keys k /\ 8 * n <= k /\ Dy = [(keys, k)]) ->
  ks = true /\ Dy = [(keys, k0)].
Proof.
intros lblk keys n k0 ks Dy HF HZ Hl [(Ey & _ & _)|(Hks & k & Hk & _ & ->)]; [exfalso; exact (HZ keys k0 Hl Ey)|].
split; [exact Hks|]. rewrite (HF keys k k0 Hk Hl). reflexivity.
Qed.

(* a key slot of an object whose key pointer names a C string: its one block *)
Lemma pfm_key1 : forall m lblk ka x k (nm : list Z) Dk,
  (forall a k k', lblk a k -> lblk a k' -> k = k') -> (forall a k, lblk a k -> a <> 0) ->
  rd_u64 segs m ka x -> pj_cstrR segs m lblk x k nm -> pj_keyR segs m lblk true ka Dk -> Dk = [(x, k)].
Proof.
intros m lblk ka x k nm Dk HF HZ Hx (Hl & _) Hk. unfold pj_keyR in Hk. cbv beta iota in Hk.
destruct Hk as (x' & Hx' & [(E & _)|(k' & Hl' & ->)]).
- exfalso. rewrite (pfm_rd_u64_det m ka x' x Hx' Hx) in E. exact (HZ x k Hl E).
- rewrite (pfm_rd_u64_det m ka x' x Hx' Hx) in Hl' |- *. rewrite (HF x k' k Hl' Hl). reflexivity.
Qed.

(* pj_foR at either depth, with its slot relation made explicit *)
Lemma pfm_foR_inv : forall m lblk d p D F, pj_foR segs m lblk d p D F ->
  exists ty num str kids keys n cap ks Ds Dk Dy Di Fi,
    pj_hdrR segs m p ty num str kids keys n cap /\
    (str = 0 /\ Ds = [] \/ exists k, lblk str k /\ Ds = [(str, k)]) /\
    (kids = 0 /\ n = 0 /\ Dk = [] \/ exists k, lblk kids k /\ 56 * n <= k /\ Dk = [(kids, k)]) /\
    (keys = 0 /\ ks = false /\ Dy = [] \/ ks = true /\ exists k, lblk keys k /\ 8 * n <= k /\ Dy = [(keys, k)]) /\
    Permutation D (Ds ++ Dk ++ Dy ++ Di) /\ F = Fi ++ Dk ++ Dy ++ Ds /\
    (d = O /\ n = 0 /\ Di = [] /\ Fi = [] \/
     exists d', d = S d' /\ pf_oitemsR segs m lblk (pj_foR segs m lblk d') ks kids keys (Z.to_nat n) Di Fi).
Proof.
intros m lblk d p D F H. destruct d as [|d]; cbn [pj_foR pj_oshapeR] in H;
  destruct H as (_ & _ & ty & num & str & kids & keys & n & cap & ks & Ds & Dk & Dy & Di & Fi &
    Hh & Hs & Hk & Hy & Hp & HPi & HF);
  exists ty, num, str, kids, keys, n, cap, ks, Ds, Dk, Dy, Di, Fi;
  (split; [exact Hh|]); (split; [exact Hs|]); (split; [exact Hk|]); (split; [exact Hy|]);
  (split; [exact Hp|]); (split; [exact HF|]).
- left. destruct HPi as (Hn & HDi & HFi). split; [reflexivity|]. split; [exact Hn|]. split; [exact HDi | exact HFi].
- right. exists d. split; [reflexivity | exact HPi].
Qed.

Lemma pfm_di0 : forall m lblk d ks kids keys n (Di Fi : list (Z * Z)), n = 0 ->
  (d = O /\ n = 0 /\ Di = [] /\ Fi = [] \/
   exists d', d = S d' /\ pf_oitemsR segs m lblk (pj_foR segs m lblk d') ks kids keys (Z.to_nat n) Di Fi) ->
  Di = [].
Proof.
intros m lblk d ks kids keys n Di Fi En [(_ & _ & HD & _)|(d' & _ & HO)]; [exact HD|].
subst n. change (Z.to_nat 0) with O in HO. cbn [pf_oitemsR] in HO. destruct HO as [HD _]. exact HD.
Qed.

(* a tree node's block list is duplicate-free and apart from the node *)
Lemma pfm_node_nd : forall m lblk p t D, pj_nodeR segs m lblk p t D -> NoDup D /\ pj_apartR D p.
Proof.
intros m lblk p t D H. destruct t; cbn [pj_nodeR] in H; destruct H as (Hnd & Hap & _); split; assumption.
Qed.

(* pj_foR does not depend on the order of its block list *)
Lemma pfm_foR_perm : forall m lblk d p D D' F,
  pj_foR segs m lblk d p D F -> Permutation D D' -> NoDup D' -> pj_apartR D' p -> pj_foR segs m lblk d p D' F.
Proof.
intros m lblk d p D D' F H HP Hnd' Hap'. destruct d as [|d]; cbn [pj_foR] in H |- *; unfold pj_oshapeR in H |- *;
  destruct H as (_ & _ & ty & num & str & kids & keys & n & cap & ks & Ds & Dk & Dy & Di & Fi &
    Hh & Hs & Hk & Hy & Hp & HPi & HF);
  (split; [exact Hnd'|]); (split; [exact Hap'|]);
  exists ty, num, str, kids, keys, n, cap, ks, Ds, Dk, Dy, Di, Fi;
  (split; [exact Hh|]); (split; [exact Hs|]); (split; [exact Hk|]); (split; [exact Hy|]);
  (split; [transitivity D; [symmetry; exact HP | exact Hp]|]);
  (split; [exact HPi | exact HF]).
Qed.

(* ---- THE CORRESPONDENCE: a pj_nodeR tree and a pj_foR tree at one address have the same blocks ---- *)
Definition pfm_corr (m : word -> option byte) (lblk : Z -> Z -> Prop) (t : jv) : Prop :=
  forall p D d D' F', pj_nodeR segs m lblk p t D -> pj_foR segs m lblk d p D' F' -> Permutation D D'.

Lemma pfm_items_corr : forall m lblk d items a ka Di0 Di Fi,
  Forall (pfm_corr m lblk) items ->
  pj_itemsR (pj_nodeR segs m lblk) a items Di0 ->
  pf_oitemsR segs m lblk (pj_foR segs m lblk d) false a ka (length items) Di Fi ->
  Permutation Di0 Di.
Proof.
intros m lblk d items a ka Di0 Di Fi HA. revert a ka Di0 Di Fi.
induction HA as [|u r Hu Hr IHr]; intros a ka Di0 Di Fi Hi HO; cbn [pj_itemsR] in Hi;
  cbn [length pf_oitemsR] in HO.
- destruct HO as [-> _]. subst Di0. apply perm_nil.
- destruct Hi as (D1 & D2 & -> & H1 & H2).
  destruct HO as (Dk & D1' & F1 & D2' & F2 & -> & _ & Hk & H1' & H2').
  unfold pj_keyR in Hk. cbv beta iota in Hk. subst Dk. cbn [app].
  apply Permutation_app; [exact (Hu a D1 d D1' F1 H1 H1') | exact (IHr (a + 56) (ka + 8) D2 D2' F2 H2 H2')].
Qed.

Lemma pfm_mems_corr : forall m lblk d ms a ka Di0 Di Fi,
  (forall a k k', lblk a k -> lblk a k' -> k = k') -> (forall a k, lblk a k -> a <> 0) ->
  Forall (fun mm => pfm_corr m lblk (snd mm)) ms ->
  pj_memsR segs m lblk (pj_nodeR segs m lblk) a ka ms Di0 ->
  pf_oitemsR segs m lblk (pj_foR segs m lblk d) true a ka (length ms) Di Fi ->
  Permutation Di0 Di.
Proof.
intros m lblk d ms a ka Di0 Di Fi HF HZ HA. revert a ka Di0 Di Fi.
induction HA as [|[nm u] r Hu Hr IHr]; intros a ka Di0 Di Fi Hm HO; cbn [pj_memsR] in Hm;
  cbn [length pf_oitemsR] in HO.
- destruct HO as [-> _]. subst Di0. apply perm_nil.
- destruct Hm as (x & k & D1 & D2 & -> & Hx & Hcs & H1 & H2).
  destruct HO as (Dk & D1' & F1 & D2' & F2 & -> & _ & Hk & H1' & H2').
  rewrite (pfm_key1 m lblk ka x k nm Dk HF HZ Hx Hcs Hk). cbn [app].
  apply perm_skip.
  apply Permutation_app; [exact (Hu a D1 d D1' F1 H1 H1') | exact (IHr (a + 56) (ka + 8) D2 D2' F2 H2 H2')].
Qed.

Lemma pfm_corr_all : forall m lblk,
  (forall a k k', lblk a k -> lblk a k' -> k = k') -> (forall a k, lblk a k -> a <> 0) ->
  forall t, pfm_corr m lblk t.
Proof.
intros m lblk HF HZ t. induction t as [| | | txt bits | s | items IH | ms IH] using jv_ind';
  unfold pfm_corr; intros p D d D' F' HN HO; cbn [pj_nodeR] in HN;
  destruct HN as (_ & _ & num & str & kids & keys & n & cap & Hh & HB);
  destruct (pfm_foR_inv m lblk d p D' F' HO) as (ty' & num' & str' & kids' & keys' & n' & cap' & ks & Ds & Dk &
    Dy & Di & Fi & Hh' & Hs & Hk & Hy & Hp & _ & Hd);
  destruct (pfm_hdr_det m p _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hh Hh') as (-> & -> & -> & ->);
  (transitivity (Ds ++ Dk ++ Dy ++ Di); [|symmetry; exact Hp]).
- destruct HB as (-> & -> & -> & -> & -> & ->).
  rewrite (pfm_ds0 _ _ _ HZ eq_refl Hs). destruct (pfm_dk0 _ _ _ _ HZ eq_refl Hk) as [_ ->].
  destruct (pfm_dy0 _ _ _ _ _ HZ eq_refl Hy) as [_ ->]. rewrite (pfm_di0 m lblk d ks 0 0 0 Di Fi eq_refl Hd).
  apply Permutation_refl.
- destruct HB as (-> & -> & -> & -> & -> & ->).
  rewrite (pfm_ds0 _ _ _ HZ eq_refl Hs). destruct (pfm_dk0 _ _ _ _ HZ eq_refl Hk) as [_ ->].
  destruct (pfm_dy0 _ _ _ _ _ HZ eq_refl Hy) as [_ ->]. rewrite (pfm_di0 m lblk d ks 0 0 0 Di Fi eq_refl Hd).
  apply Permutation_refl.
- destruct HB as (-> & -> & -> & -> & -> & ->).
  rewrite (pfm_ds0 _ _ _ HZ eq_refl Hs). destruct (pfm_dk0 _ _ _ _ HZ eq_refl Hk) as [_ ->].
  destruct (pfm_dy0 _ _ _ _ _ HZ eq_refl Hy) as [_ ->]. rewrite (pfm_di0 m lblk d ks 0 0 0 Di Fi eq_refl Hd).
  apply Permutation_refl.
- destruct HB as (_ & -> & -> & -> & -> & k & Hcs & ->).
  rewrite (pfm_ds1 _ _ _ _ HF HZ (proj1 Hcs) Hs). destruct (pfm_dk0 _ _ _ _ HZ eq_refl Hk) as [_ ->].
  destruct (pfm_dy0 _ _ _ _ _ HZ eq_refl Hy) as [_ ->]. rewrite (pfm_di0 m lblk d ks 0 0 0 Di Fi eq_refl Hd).
  apply Permutation_refl.
- destruct HB as (-> & -> & -> & -> & k & Hcs & ->).
  rewrite (pfm_ds1 _ _ _ _ HF HZ (proj1 Hcs) Hs). destruct (pfm_dk0 _ _ _ _ HZ eq_refl Hk) as [_ ->].
  destruct (pfm_dy0 _ _ _ _ _ HZ eq_refl Hy) as [_ ->]. rewrite (pfm_di0 m lblk d ks 0 0 0 Di Fi eq_refl Hd).
  apply Permutation_refl.
- destruct HB as (-> & -> & En & Hc & Hcap & Di0 & ED & Hi).
  rewrite (pfm_ds0 _ _ _ HZ eq_refl Hs). destruct (pfm_dy0 _ _ _ _ _ HZ eq_refl Hy) as [-> ->].
  destruct Hcap as [(-> & ->)|(Hcp & Hlk)].
  + destruct items as [|u r]; [|cbn [length] in En; lia].
    cbn [pj_itemsR] in Hi. subst Di0. cbn in ED. subst D. cbn [length] in En.
    destruct (pfm_dk0 _ _ _ _ HZ eq_refl Hk) as [_ ->]. rewrite (pfm_di0 m lblk d false 0 0 n Di Fi En Hd).
    apply Permutation_refl.
  + rewrite (proj2 (Z.eqb_neq cap 0)) in ED by lia. subst D.
    rewrite (pfm_dk1 _ _ _ _ _ HF HZ Hlk Hk).
    destruct Hd as [(-> & En0 & -> & _)|(d' & -> & HPi)].
    * destruct items as [|u r]; [|cbn [length] in En; lia].
      cbn [pj_itemsR] in Hi. subst Di0. apply Permutation_refl.
    * rewrite En, Nat2Z.id in HPi. cbn [app]. apply perm_skip.
      exact (pfm_items_corr m lblk d' items kids 0 Di0 Di Fi IH Hi HPi).
- destruct HB as (-> & En & Hc & Hcap & Di0 & ED & Hm).
  rewrite (pfm_ds0 _ _ _ HZ eq_refl Hs).
  destruct Hcap as [(-> & -> & ->)|(Hcp & Hlk & Hly)].
  + destruct ms as [|mm r]; [|cbn [length] in En; lia].
    cbn [pj_memsR] in Hm. subst Di0. cbn in ED. subst D. cbn [length] in En.
    destruct (pfm_dk0 _ _ _ _ HZ eq_refl Hk) as [_ ->]. destruct (pfm_dy0 _ _ _ _ _ HZ eq_refl Hy) as [_ ->].
    rewrite (pfm_di0 m lblk d ks 0 0 n Di Fi En Hd).
    apply Permutation_refl.
  + rewrite (proj2 (Z.eqb_neq cap 0)) in ED by lia. subst D.
    rewrite (pfm_dk1 _ _ _ _ _ HF HZ Hlk Hk). destruct (pfm_dy1 _ _ _ _ _ _ HF HZ Hly Hy) as [-> ->].
    destruct Hd as [(-> & En0 & -> & _)|(d' & -> & HPi)].
    * destruct ms as [|mm r]; [|cbn [length] in En; lia].
      cbn [pj_memsR] in Hm. subst Di0. apply Permutation_refl.
    * rewrite En, Nat2Z.id in HPi. cbn [app]. apply perm_skip. apply perm_skip.
      exact (pfm_mems_corr m lblk d' ms kids keys Di0 Di Fi HF HZ IH Hm HPi).
Qed.

(* ---- one slot's length, and the slots of an object against fo's ---- *)
Lemma pfm_slot_len : forall m lblk nn p u D1 D1' F1,
  (forall a k k', lblk a k -> lblk a k' -> k = k') -> (forall a k, lblk a k -> a <> 0) ->
  pj_nodeR segs m lblk p u D1 -> pj_foR segs m lblk nn p D1' F1 ->
  (length (PresetReqAt.fo u) <= length F1)%nat.
Proof.
intros m lblk nn p u D1 D1' F1 HF HZ H1 H1'.
pose proof (pfm_corr_all m lblk HF HZ u p D1 nn D1' F1 H1 H1') as P.
pose proof (proj2 (pj_foR_fdR segs m lblk nn p D1' F1 H1')) as PF.
pose proof (pf_node_len segs m lblk u p D1 H1) as L.
rewrite (Permutation_length (PresetReqAtNoMiss.fo_tblk u)), (Permutation_length PF), <- (Permutation_length P).
exact L.
Qed.

(* fo's object arm before its arrays, with the key request K *)
Definition pfm_slots (K : list Z -> Z) (ms : list (list Z * jv)) : list Z :=
  concat (map (fun mm => PresetReqAt.fo (snd mm) ++ [K (fst mm)]) ms).

Lemma pfm_slots_cons : forall K nm u r, pfm_slots K ((nm, u) :: r) = PresetReqAt.fo u ++ K nm :: pfm_slots K r.
Proof. intros K nm u r. unfold pfm_slots. cbn [map concat fst snd]. rewrite <- app_assoc. reflexivity. Qed.

Lemma pfm_oslots_len : forall m lblk nn K ms a ka Dm Di Fi,
  (forall a k k', lblk a k -> lblk a k' -> k = k') -> (forall a k, lblk a k -> a <> 0) ->
  pj_memsR segs m lblk (pj_nodeR segs m lblk) a ka ms Dm ->
  pf_oitemsR segs m lblk (pj_foR segs m lblk nn) true a ka (length ms) Di Fi ->
  (length (pfm_slots K ms) <= length Fi)%nat.
Proof.
intros m lblk nn K ms. induction ms as [|[nm u] r IH]; intros a ka Dm Di Fi HF HZ Hm HO;
  cbn [pj_memsR] in Hm; cbn [length pf_oitemsR] in HO.
- unfold pfm_slots. cbn [map concat length]. lia.
- destruct Hm as (x & k & D1 & D2 & -> & Hx & Hcs & H1 & H2).
  destruct HO as (Dk & D1' & F1 & D2' & F2 & -> & -> & Hk & H1' & H2').
  rewrite (pfm_key1 m lblk ka x k nm Dk HF HZ Hx Hcs Hk).
  rewrite pfm_slots_cons, !length_app. cbn [length].
  pose proof (pfm_slot_len m lblk nn a u D1 D1' F1 HF HZ H1 H1').
  pose proof (IH (a + 56) (ka + 8) D2 D2' F2 HF HZ H2 H2'). lia.
Qed.

Lemma pfm_oslots : forall m lblk nn K ms a ka Dm Di Fi,
  (forall a k k', lblk a k -> lblk a k' -> k = k') -> (forall a k, lblk a k -> a <> 0) ->
  pj_memsR segs m lblk (pj_nodeR segs m lblk) a ka ms Dm ->
  pf_oitemsR segs m lblk (pj_foR segs m lblk nn) true a ka (length ms) Di Fi ->
  map (fun b => snd b + PresetReqAt.HEAD) Fi = pfm_slots K ms ->
  forall i kname vi Dv, nth_error ms i = Some (kname, vi) ->
  pj_nodeR segs m lblk (a + 56 * Z.of_nat i) vi Dv ->
  exists Fv, pj_foR segs m lblk nn (a + 56 * Z.of_nat i) Dv Fv /\
    map (fun b => snd b + PresetReqAt.HEAD) Fv = PresetReqAt.fo vi.
Proof.
intros m lblk nn K ms. induction ms as [|[nm u] r IH]; intros a ka Dm Di Fi HF HZ Hm HO HM i kname vi Dv Hi Hv.
- destruct i; discriminate Hi.
- cbn [pj_memsR] in Hm. cbn [length pf_oitemsR] in HO.
  destruct Hm as (x & k & D1 & D2 & -> & Hx & Hcs & H1 & H2).
  destruct HO as (Dk & D1' & F1 & D2' & F2 & -> & -> & Hk & H1' & H2').
  rewrite (pfm_key1 m lblk ka x k nm Dk HF HZ Hx Hcs Hk) in HM.
  rewrite pfm_slots_cons in HM.
  assert (L2 : (length (K nm :: pfm_slots K r) <= length ([(x, k)] ++ F2))%nat).
  { pose proof (pfm_oslots_len m lblk nn K r (a + 56) (ka + 8) D2 D2' F2 HF HZ H2 H2'). cbn [length app]. lia. }
  destruct (pf_map_split F1 ([(x, k)] ++ F2) (PresetReqAt.fo u) (K nm :: pfm_slots K r) HM
    (pfm_slot_len m lblk nn a u D1 D1' F1 HF HZ H1 H1') L2) as [E1 E2].
  cbn [map app] in E2. injection E2 as _ E2.
  destruct i as [|i].
  + cbn [nth_error] in Hi. injection Hi as Enm Eu. subst u.
    assert (Ea : a + 56 * Z.of_nat 0 = a) by lia. rewrite Ea in Hv |- *.
    exists F1. split; [|exact E1].
    destruct (pfm_node_nd m lblk a vi Dv Hv) as [Hnd Hap].
    apply (pfm_foR_perm m lblk nn a D1' Dv F1 H1'); [symmetry | exact Hnd | exact Hap].
    exact (pfm_corr_all m lblk HF HZ vi a Dv nn D1' F1 Hv H1').
  + cbn [nth_error] in Hi.
    assert (Ea : a + 56 * Z.of_nat (S i) = (a + 56) + 56 * Z.of_nat i) by lia. rewrite Ea in Hv |- *.
    exact (IH (a + 56) (ka + 8) D2 D2' F2 HF HZ H2 H2' E2 i kname vi Dv Hi Hv).
Qed.

(* THE MEMBER'S ORDER: an object's ordered free list projects to member i's, at its slot. The kit's text (a Theorem Labs lane)
   plus the three premises the header shows necessary: kids is o's kids field, lblk is functional, no block at 0. *)
Theorem pj_foR_member : forall m lblk o ms D F nn i kname vi Di kids,
  pj_nodeR segs m lblk o (PjTree.JObj ms) D ->
  pj_foR segs m lblk (S nn) o D F ->
  map (fun b => snd b + PresetReqAt.HEAD) F = PresetReqAt.fo (PjTree.JObj ms) ->
  nth_error ms i = Some (kname, vi) ->
  pj_nodeR segs m lblk (kids + 56 * Z.of_nat i) vi Di ->
  rd_u64 segs m (o + 24) kids ->
  (forall a k k', lblk a k -> lblk a k' -> k = k') ->
  (forall a k, lblk a k -> a <> 0) ->
  exists Fv, pj_foR segs m lblk nn (kids + 56 * Z.of_nat i) Di Fv /\
    map (fun b => snd b + PresetReqAt.HEAD) Fv = PresetReqAt.fo vi.
Proof.
intros m lblk o ms D F nn i kname vi Di kids HN HF HM Hi Hv Hkid HFn HZ.
assert (Hlen : (i < length ms)%nat) by (apply nth_error_Some; rewrite Hi; discriminate).
cbn [pj_nodeR] in HN. destruct HN as (_ & _ & num & str & kids0 & keys & n & cap & Hh & HB).
destruct HB as (Es & En & Hc & Hcap & Dm & _ & Hm).
destruct Hcap as [(Ec & _ & _)|(Hcp & Hlk & Hly)]; [lia|].
assert (Ek : kids0 = kids)
  by (destruct Hh as (_ & _ & _ & _ & K0 & _); exact (pfm_rd_u64_det m (o + 24) kids0 kids K0 Hkid)).
subst kids0.
cbn [pj_foR pj_oshapeR] in HF.
destruct HF as (_ & _ & ty' & num' & str' & kids' & keys' & n' & cap' & ks & Ds & Dk & Dy & Di' & Fi &
  Hh' & Hs & Hk & Hy & _ & HPi & EF).
destruct (pfm_hdr_det m o _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hh Hh') as (-> & -> & -> & ->).
rewrite (pfm_ds0 _ _ _ HZ Es Hs) in EF. rewrite (pfm_dk1 _ _ _ _ _ HFn HZ Hlk Hk) in EF.
destruct (pfm_dy1 _ _ _ _ _ _ HFn HZ Hly Hy) as [-> Ey]. rewrite Ey in EF. subst F.
rewrite En, Nat2Z.id in HPi.
assert (EFo : PresetReqAt.fo (PjTree.JObj ms) =
  pfm_slots PresetReqAtNoMiss.kblk ms ++ PresetReqAt.arrz true (PresetReqAt.ncap (length ms))) by reflexivity.
rewrite EFo in HM.
assert (L2 : (length (PresetReqAt.arrz true (PresetReqAt.ncap (length ms))) <=
  length ([(kids, (56 * cap)%Z)] ++ [(keys, (8 * cap)%Z)] ++ []))%nat)
  by (destruct (PresetReqAt.ncap (length ms)); cbn; lia).
destruct (pf_map_split Fi ([(kids, 56 * cap)] ++ [(keys, 8 * cap)] ++ []) (pfm_slots PresetReqAtNoMiss.kblk ms)
  (PresetReqAt.arrz true (PresetReqAt.ncap (length ms))) HM
  (pfm_oslots_len m lblk nn PresetReqAtNoMiss.kblk ms kids keys Dm Di' Fi HFn HZ Hm HPi) L2) as [E1 _].
exact (pfm_oslots m lblk nn PresetReqAtNoMiss.kblk ms kids keys Dm Di' Fi HFn HZ Hm HPi E1 i kname vi Di Hi Hv).
Qed.
End fm.
