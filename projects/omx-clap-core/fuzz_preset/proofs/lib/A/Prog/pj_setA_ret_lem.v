(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs, 2026-10: the helper lemmas of segment RET of pj_set's image-A' walk (fuzz_preset asan,
   A 0x8685c; the cuts of lib/A/Prog/pj_setA_defs.v; the segment is lib/A/Prog/pj_setA_seg_ret.v).
   proves no function (kind: glue lemma).
   - pure list facts: a duplicate-free sublist is a permutation part (pjrA_perm_sub), NoDup of an append and of a
     permutation, the harness blocks of a ledger list are duplicate-free;
   - pjrA_u64_fun: a 64-bit read names one value;
   - pjrA_new_tree: the object tree after the present arm (member i's value replaced by val's header copied into
     the slot), from the entry decomposition (pj_set_trans.v pjst_mems_app / pjst_mems_frame / pjst_node_move);
     pjrA_new_fo: the same object's ORDERED free list (FREEORD-COPY of the present arm), from the entry's
     ordered list cut at member i (pj_set_trans.v's pjsf_* library) with val's list moved into the slot;
   - pjrA_step_beq: one `beq` step at a listing offset (YK11.v step_beq_tk / step_beq_ft, in the shape of
     pj_setA_steps.v pjsA_step_addi);
   - the ledger's blocks at a state (pjrA_hb), their separation (pjrA_lam_sep), a placed 56-byte struct off a
     ledger block it does not lie in (pjrA_place_off), where a placed struct lies (pjrA_at_where), what a call
     keeps of a placed struct (pjrA_place_call), what a call keeps of a tree's footprint (pjrA_tree_agree) and the
     tree across the call with its header bytes given (pjrA_tree_kept, pj_setA_vis.v pjsA_tree_kept without the
     window condition);
   - the replaced member against the model (the contract's event form): the new object's block sizes with member i's value
     replaced (pjrA_tblk_swap, the contract's present-arm block conjunct: a Permutation, cut at member i from pjsA_pre's
     whole-object Permutation), pj_get's member is prhPj_mfind's (pjrA_mfind_first, pjrA_set_evs_hit), and the
     position after pj_free (pjrA_pos_after_free, by PRH_FnPj.v prhPj_bulk_nil_pos when the order list is empty).
   The section premise HW8 (PRH_Base.v prh_head_wide, 8 <= cf_head; cf_head = 16 at preset's CfParams instance)
   puts a harness block's 8-byte head word inside its allocator block, before its user bytes.
   Numerals: 56 (LENGTH: the struct pj); 8 (LENGTH: the head word, a key pointer); 6 (the object tag); 4 (DERIVED:
   the pc step). No ADDRESS. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn YP0b YP0a.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YN3v YI04 YI00 YG0s YP07 YI16.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YG0p YCbqG YCbqGcall YCbqGcallW FCiface YGcallMx.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfNames YGcfRoomKeep YG0dcf YGcfRoomPre.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK0o YK06 YGcfFsVis.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0d YP0c YC80 YPsym YC4aP YImgTop.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YC1fP YC80x YC1fPx.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Ledger ReaderRes.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PjTree PjGrammar.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PresetRoomPos PresetReqAt PresetReqAtNoMiss.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Base PRH_Reader PRH_Charge PRH_FnReader.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_FnPj PRH_FnAlloc PRH_PjOrder.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require PjFoMember.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require Import S1Ledger.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import Img0 Listing_prog PAImg_prog PRH_Img.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require Import S1ImgA pj_setA_defs pj_setA_glue pj_setA_steps pj_setA_vis.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require Import pj_set_trans.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Set Warnings "-notation-for-abbreviation".
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Local Open Scope Z_scope.
#[local] Existing Instance prh_img_A.

(* ---- pure list facts (NoDup is stdpp's, the one pj_nodeR and prh_ledger state; the proofs pass to Stdlib's
   List.NoDup by stdpp's NoDup_ListNoDup, as S1Ledger.v does) ---- *)
Lemma pjrA_perm_sub : forall {A : Type} (l L : list A), NoDup l -> incl l L -> exists r, Permutation L (l ++ r).
Proof.
intros A l L Hnd. apply NoDup_ListNoDup in Hnd. revert L. induction Hnd as [|x l Hx Hnd IH]; intros L Hinc.
- exists L. reflexivity.
- assert (HxL : In x L) by (apply Hinc; left; reflexivity).
  apply in_split in HxL as (L1 & L2 & ->).
  destruct (IH (L1 ++ L2)) as (r & Hr).
  + intros y Hy. assert (Hy2 : In y (L1 ++ x :: L2)) by (apply Hinc; right; exact Hy).
    apply in_app_or in Hy2. apply in_or_app.
    destruct Hy2 as [Hy2 | [E | Hy2]]; [left; exact Hy2 | subst y; contradiction | right; exact Hy2].
  + exists r. cbn [app]. apply (Permutation_trans (Permutation_sym (Permutation_middle L1 L2 x))).
    apply perm_skip. exact Hr.
Qed.

Lemma pjrA_nodup_app : forall {A : Type} (l l' : list A), NoDup l -> NoDup l' ->
  (forall a, In a l -> ~ In a l') -> NoDup (l ++ l').
Proof.
intros A l l' H1 H2 H3. apply NoDup_ListNoDup in H1. apply NoDup_ListNoDup in H2. apply NoDup_ListNoDup.
revert l' H2 H3. induction H1 as [|x l Hx H1 IH]; intros l' H2 H3; cbn [app]; [exact H2|].
constructor.
- intros Hin. apply in_app_or in Hin as [Hin|Hin]; [exact (Hx Hin)|exact (H3 x (or_introl eq_refl) Hin)].
- apply IH; [exact H2 |]. intros a Ha. apply H3. right. exact Ha.
Qed.

Lemma pjrA_nodup_perm : forall {A : Type} (l l' : list A), NoDup l -> Permutation l l' -> NoDup l'.
Proof.
intros A l l' H HP. apply NoDup_ListNoDup in H. apply NoDup_ListNoDup. exact (Permutation_NoDup HP H).
Qed.

Lemma pjrA_nodup_app_r : forall {A : Type} (l l' : list A), NoDup (l ++ l') -> NoDup l'.
Proof.
intros A l l' H. apply NoDup_ListNoDup in H. apply NoDup_ListNoDup.
induction l as [|x l IH]; cbn [app] in H; [exact H|]. apply NoDup_cons_iff in H as [_ H]. exact (IH H).
Qed.

Lemma pjrA_nodup_app_disj : forall {A : Type} (l l' : list A) a, NoDup (l ++ l') -> In a l -> ~ In a l'.
Proof.
intros A l l' a H. apply NoDup_ListNoDup in H.
induction l as [|x l IH]; cbn [app] in H; intros Hin; [destruct Hin|].
apply NoDup_cons_iff in H as [Hx H]. destruct Hin as [<- | Hin].
- intros Hin'. apply Hx. apply in_or_app. right. exact Hin'.
- exact (IH H Hin).
Qed.

Lemma pjrA_perm_mid : forall {A : Type} (a b c : list A), Permutation (a ++ b ++ c) (b ++ a ++ c).
Proof. intros A a b c. rewrite !app_assoc. apply Permutation_app_tail. apply Permutation_app_comm. Qed.

(* a middle part cancelled: middles equal up to order leave the outer parts permutations of each other *)
Lemma pjrA_perm_cancel_mid : forall {A : Type} (a u c a' u' c' : list A),
  Permutation u u' -> Permutation (a ++ u ++ c) (a' ++ u' ++ c') -> Permutation (a ++ c) (a' ++ c').
Proof.
intros A a u c a' u' c' Hu H. apply (Permutation_app_inv_l u).
apply (Permutation_trans (pjrA_perm_mid u a c)). apply (Permutation_trans H).
apply (Permutation_trans (pjrA_perm_mid a' u' c')).
apply Permutation_app; [apply Permutation_sym; exact Hu | apply Permutation_refl].
Qed.

(* a middle part inserted on both sides *)
Lemma pjrA_perm_ins : forall {A : Type} (a c a' c' w : list A),
  Permutation (a ++ c) (a' ++ c') -> Permutation (a ++ w ++ c) (a' ++ w ++ c').
Proof.
intros A a c a' c' w H. apply (Permutation_trans (pjrA_perm_mid a w c)).
apply (Permutation_trans (Permutation_app (Permutation_refl w) H)).
apply Permutation_sym. apply pjrA_perm_mid.
Qed.

(* a list after a marker k pulled to the front *)
Lemma pjrA_perm_pull : forall {A : Type} (a x y t : list A) (k : A),
  Permutation (a ++ x ++ (k :: t) ++ y) (t ++ a ++ x ++ k :: y).
Proof.
intros A a x y t k.
replace (a ++ x ++ (k :: t) ++ y) with ((a ++ x ++ [k]) ++ t ++ y) by (rewrite <- !app_assoc; reflexivity).
replace (a ++ x ++ k :: y) with ((a ++ x ++ [k]) ++ y) by (rewrite <- !app_assoc; reflexivity).
apply pjrA_perm_mid.
Qed.

Lemma pjrA_nodup_hbl {cp : CfParams} : forall (Lam : list (Z * Z)), NoDup (map fst Lam) -> NoDup (prhPj_hbl Lam).
Proof. intros Lam H. unfold prhPj_hbl. exact (prh_nodup_blocks cf_head Lam H). Qed.

Lemma pjrA_hbl_in {cp : CfParams} : forall (D : list (Z * Z)) b m, In (b, m) (prhPj_hbl D) ->
  In (b + cf_head, m - cf_head) D.
Proof.
intros D b m H. unfold prhPj_hbl in H. apply in_map_iff in H as ([a k] & E & Hin). cbn [fst snd] in E.
injection E as <- <-. replace (a - cf_head + cf_head, k + cf_head - cf_head) with (a, k) by (f_equal; lia). exact Hin.
Qed.

Lemma pjrA_inFP_hbl {cp : CfParams} : forall (D : list (Z * Z)) y, inFP (ablocks_fp (prhPj_hbl D)) y ->
  exists a k, In (a, k) D /\ a - cf_head <= y < a - cf_head + req_size (k + cf_head).
Proof.
intros D y (r & Hr & Hy). unfold ablocks_fp, prhPj_hbl in Hr. rewrite map_map in Hr.
apply in_map_iff in Hr as ([a k] & <- & Hin). cbn [fst snd] in Hy. exists a, k. split; [exact Hin | lia].
Qed.

Lemma pjrA_hbl_inFP {cp : CfParams} : forall (D : list (Z * Z)) a k y, In (a, k) D ->
  a - cf_head <= y < a - cf_head + req_size (k + cf_head) -> inFP (ablocks_fp (prhPj_hbl D)) y.
Proof.
intros D a k y Hin Hy. exists (a - cf_head, a - cf_head + req_size (k + cf_head)).
split; [|cbn [fst snd]; lia].
unfold ablocks_fp, prhPj_hbl. rewrite map_map. apply in_map_iff. exists (a, k). split; [reflexivity | exact Hin].
Qed.

(* ---- memory facts ---- *)
Lemma pjrA_u64_fun : forall (segs : list Segment) m a v v', rd_u64 segs m a v -> rd_u64 segs m a v' -> v = v'.
Proof.
intros segs m a v v' [Hr Hv] [Hr' Hv'].
assert (E : forall k, (k < 8)%nat -> le_byte v 8 k = le_byte v' 8 k).
{ intros k Hk. pose proof (Hv k Hk) as E1. rewrite (Hv' k Hk) in E1.
  assert (E2 : Z_to_bv 8 (le_byte v' 8 k) = Z_to_bv 8 (le_byte v 8 k))
    by exact (f_equal (fun o : option byte => match o with Some b => b | None => Z_to_bv 8 0 end) E1).
  apply (f_equal (fun b : bv 8 => bv_unsigned b)) in E2. cbv beta in E2.
  rewrite !Z_to_bv_unsigned in E2. unfold bv_wrap in E2. change (bv_modulus 8) with 256 in E2.
  unfold le_byte in E2 |- *. rewrite !Z.mod_mod in E2 by lia. symmetry. exact E2. }
rewrite <- (le_bytes8 v Hr), <- (le_bytes8 v' Hr').
rewrite (E 0%nat), (E 1%nat), (E 2%nat), (E 3%nat), (E 4%nat), (E 5%nat), (E 6%nat), (E 7%nat) by lia.
reflexivity.
Qed.

Lemma pjrA_agree_sub : forall (segs : list Segment) m m' (X Y : Z -> Prop), pj_agreeR segs m m' X ->
  (forall y, Y y -> X y) -> pj_agreeR segs m m' Y.
Proof. intros segs m m' X Y H HYX y Hy. exact (H y (HYX y Hy)). Qed.

Lemma pjrA_agree_trans : forall (segs : list Segment) m0 m1 m2 (X : Z -> Prop),
  pj_agreeR segs m0 m1 X -> pj_agreeR segs m1 m2 X -> pj_agreeR segs m0 m2 X.
Proof.
intros segs m0 m1 m2 X H1 H2 x Hx. destruct (H1 x Hx) as [E1 W1]. destruct (H2 x Hx) as [E2 W2].
split; [rewrite E2; exact E1 | intros Hw; exact (W2 (W1 Hw))].
Qed.

Section mb. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Lemma pjrA_mbyte_aview2 : forall (segs : list Segment) (H H' : word -> bool) (m m' : word -> option byte) a a',
  aview segs H' m' a' = aview segs H m a -> mbyte segs (mrestrict H' m') a' = mbyte segs (mrestrict H m) a.
Proof.
intros segs H H' m m' a a' E. unfold aview in E.
destruct (mbyte segs (mrestrict H' m') a') as [b'|], (mbyte segs (mrestrict H m) a) as [b|]; cbn in E;
  try discriminate; [|reflexivity].
injection E as E. f_equal. apply bv_eq. exact E.
Qed.
End mb.

(* ---- the object tree after the present arm: member i's value is val's tree, its header copied to the slot
   z = kids + 56 i; every other byte the tree reads is as at the entry (m0) ---- *)
Section nt.
Variable segs : list Segment.
(* a node's block list is duplicate-free and holds no byte of its header (pj_nodeR's first two conjuncts, at any t) *)
Lemma pjrA_node_nodup : forall m lblk p (t : PjTree.jv) D, pj_nodeR segs m lblk p t D -> NoDup D /\ pj_apartR D p.
Proof. intros m lblk p t D H. destruct t; cbn [pj_nodeR] in H; exact (conj (proj1 H) (proj1 (proj2 H))). Qed.

Lemma pjrA_new_tree : forall (m0 m2 m' : word -> option byte) (lblk0 lblk' : Z -> Z -> Prop)
    o num kids keys cap (ms : list (list Z * PjTree.jv)) i kname vi tv D1 x kx D2 w z Dw,
  pj_hdrR segs m0 o 6 num 0 kids keys (Z.of_nat (length ms)) cap ->
  Z.of_nat (length ms) <= cap -> 0 < cap -> lblk' kids (56 * cap) -> lblk' keys (8 * cap) ->
  nth_error ms i = Some (kname, vi) ->
  pj_memsR segs m0 lblk0 (pj_nodeR segs m0 lblk0) kids keys (firstn i ms) D1 ->
  rd_u64 segs m0 (keys + 8 * Z.of_nat i) x -> pj_cstrR segs m0 lblk0 x kx kname ->
  pj_memsR segs m0 lblk0 (pj_nodeR segs m0 lblk0) (kids + 56 * Z.of_nat (S i)) (keys + 8 * Z.of_nat (S i))
    (skipn (S i) ms) D2 ->
  z = kids + 56 * Z.of_nat i ->
  pj_nodeR segs m2 lblk' w tv Dw ->
  (forall j, 0 <= j < 56 -> mbyte segs m' (z + j) = mbyte segs m2 (w + j)) ->
  pj_rwR segs m' z -> pj_apartR Dw z ->
  pj_agreeR segs m2 m' (fun y => exists b, In b Dw /\ pj_holdsR b y) ->
  pj_agreeR segs m0 m' (fun y => o <= y < o + 56 \/ kids <= y < kids + 56 * Z.of_nat i \/
     kids + 56 * Z.of_nat (S i) <= y < kids + 56 * Z.of_nat (length ms) \/
     keys <= y < keys + 8 * Z.of_nat (length ms) \/ exists b, In b (D1 ++ (x, kx) :: D2) /\ pj_holdsR b y) ->
  (forall a k, In (a, k) (D1 ++ (x, kx) :: D2) -> lblk' a k) ->
  (forall a k, In (a, k) Dw -> lblk' a k) ->
  NoDup ([(kids, 56 * cap); (keys, 8 * cap)] ++ D1 ++ (x, kx) :: Dw ++ D2) ->
  pj_apartR ([(kids, 56 * cap); (keys, 8 * cap)] ++ D1 ++ (x, kx) :: Dw ++ D2) o ->
  pj_nodeR segs m' lblk' o (PjTree.JObj (firstn i ms ++ (kname, tv) :: skipn (S i) ms))
    ([(kids, 56 * cap); (keys, 8 * cap)] ++ D1 ++ (x, kx) :: Dw ++ D2).
Proof.
intros m0 m2 m' lblk0 lblk' o num kids keys cap ms i kname vi tv D1 x kx D2 w z Dw
  Hhdr Hncap Hcap Hlk Hly Hnth HM1 Hkx Hcs HM2 Ez HNw Hcpy Hrwz Hapz HAw HA0 HL1 HLw Hnd Hap.
pose proof (pj_nth_lenR ms i (kname, vi) Hnth) as Hi.
assert (Hlf : length (firstn i ms) = i) by (apply firstn_length_le; lia).
assert (Hlen : length (firstn i ms ++ (kname, tv) :: skipn (S i) ms) = length ms).
{ rewrite length_app. cbn [length]. rewrite Hlf, length_skipn. lia. }
assert (Hls : Z.of_nat (length (skipn (S i) ms)) = Z.of_nat (length ms) - Z.of_nat (S i))
  by (rewrite length_skipn; lia).
cbn [pj_nodeR]. split; [exact Hnd|]. split; [exact Hap|].
exists num, 0, kids, keys, (Z.of_nat (length ms)), cap.
split.
{ apply (pj_hdrR_frame segs m0 m'); [exact Hhdr|]. apply (pjrA_agree_sub segs m0 m' _ _ HA0).
  intros y Hy. cbv beta in Hy |- *. left. exact Hy. }
split; [reflexivity|]. split; [rewrite Hlen; reflexivity|]. split; [exact Hncap|].
split; [right; split; [exact Hcap|]; split; [exact Hlk | exact Hly]|].
exists (D1 ++ (x, kx) :: Dw ++ D2).
split; [rewrite (proj2 (Z.eqb_neq cap 0)) by lia; reflexivity|].
apply (proj2 (pjst_mems_app segs m' lblk' _ (firstn i ms) ((kname, tv) :: skipn (S i) ms) kids keys _)).
exists D1, ((x, kx) :: Dw ++ D2). split; [reflexivity|].
split.
{ (* the members before i *)
  apply (pjst_mems_frame segs (firstn i ms) m0 m' lblk0 lblk' kids keys D1 HM1).
  - apply (pjrA_agree_sub segs m0 m' _ _ HA0). intros y Hy. cbv beta in Hy |- *. rewrite Hlf in Hy.
    destruct Hy as [Hy | [Hy | (b & Hb & Hy)]].
    + right. left. exact Hy.
    + right. right. right. left. lia.
    + right. right. right. right. exists b. split; [apply in_or_app; left; exact Hb | exact Hy].
  - intros a k Hin. apply HL1. apply in_or_app. left. exact Hin. }
rewrite Hlf. cbn [pj_memsR].
exists x, kx, Dw, D2. split; [reflexivity|].
split.
{ apply (rd_u64_frame segs m0 m' _ x Hkx). intros y Hy. apply (pjst_agree_b segs m0 m' _ y HA0). cbv beta.
  right. right. right. left. lia. }
split.
{ apply (pjst_cstr_fsw segs m0 m' lblk0 lblk' x kx kname Hcs); [|apply HL1; apply in_or_app; right; left; reflexivity].
  intros y Hy. apply (pjst_agree_b segs m0 m' _ y HA0). cbv beta. right. right. right. right. exists (x, kx).
  split; [apply in_or_app; right; left; reflexivity | unfold pj_holdsR; cbn [fst snd]; exact Hy]. }
split.
{ (* the value: val's header copied to the slot *)
  rewrite <- Ez.
  exact (pjst_node_move segs tv m2 m' lblk' lblk' w z Dw HNw Hcpy Hrwz Hapz HAw HLw). }
(* the members after i *)
replace (kids + 56 * Z.of_nat i + 56) with (kids + 56 * Z.of_nat (S i)) by lia.
replace (keys + 8 * Z.of_nat i + 8) with (keys + 8 * Z.of_nat (S i)) by lia.
apply (pjst_mems_frame segs (skipn (S i) ms) m0 m' lblk0 lblk' _ _ D2 HM2).
- apply (pjrA_agree_sub segs m0 m' _ _ HA0). intros y Hy. cbv beta in Hy |- *. rewrite Hls in Hy.
  destruct Hy as [Hy | [Hy | (b & Hb & Hy)]].
  + right. right. left. lia.
  + right. right. right. left. lia.
  + right. right. right. right. exists b. split; [apply in_or_app; right; right; exact Hb | exact Hy].
- intros a k Hin. apply HL1. apply in_or_app. right. right. exact Hin.
Qed.

(* an object's key slot at a memory and block predicate that keep its pointer word and its block *)
Lemma pjrA_keyR_frame : forall m m' lblk lblk' ka (Dk : list (Z * Z)),
  pj_keyR segs m lblk true ka Dk ->
  (forall y, ka <= y < ka + 8 -> mbyte segs m' y = mbyte segs m y) ->
  (forall a k, In (a, k) Dk -> lblk' a k) ->
  pj_keyR segs m' lblk' true ka Dk.
Proof.
intros m m' lblk lblk' ka Dk Hk HB HL. unfold pj_keyR in Hk |- *. cbv beta iota in Hk |- *.
destruct Hk as (y & Hy & Hc). exists y. split; [exact (rd_u64_frame segs m m' ka y Hy HB)|].
destruct Hc as [Hc | (k & _ & ->)]; [left; exact Hc|].
right. exists k. split; [apply HL; left; reflexivity | reflexivity].
Qed.

(* THE NEW OBJECT'S ORDERED FREE LIST (FREEORD-COPY of tpj_set_specX's present-key arm), on pjrA_new_tree's block
   list: the entry's ordered list of the object at depth max nn (depth (JObj ms)) = S d (pjsA_pre's ordered premise),
   decomposed (pj_set_trans.v pjsf_obj_dest; the map split by pjsf_slots_map; member i by pjsf_oitems_member); the
   slots before and after member i lowered to nn - 1 (pjsf_oitems_lower: their members are the result's) and carried
   to the final memory (PRH_PjOrder.pf_oitemsR_frame, over pjrA_new_tree's agreement); slot i's key block kept
   (pjrA_keyR_frame) and its value val's ordered list (given at the pre-copy memory m2) moved into the slot
   (pjsf_foR_move); reassembled (pjsf_oitems_one, pjsf_oitems_app, pjsf_obj_intro) and put on the new block list
   (PjFoMember.pfm_foR_perm: member i's entry blocks Du are a permutation of the order list's own, pfm_corr_all).
   fo's object clause is cut at member i on both sides (pjsf_fo_obj, pjsf_slots_app, PjFoMember.pfm_slots_cons);
   the member count, so the arrays' requests, are the entry's. *)
Lemma pjrA_new_fo : forall (m0 m2 m' : word -> option byte) (lblk0 lblk' : Z -> Z -> Prop)
    o kids keys cap (ms : list (list Z * PjTree.jv)) i kname vi tv D1 x kx Du D2 w z Dw,
  (forall a k k', lblk0 a k -> lblk0 a k' -> k = k') -> (forall a k, lblk0 a k -> a <> 0) ->
  pj_nodeR segs m0 lblk0 o (PjTree.JObj ms) ((kids, 56 * cap) :: (keys, 8 * cap) :: D1 ++ (x, kx) :: Du ++ D2) ->
  (forall nn, (PjTree.depth (PjTree.JObj ms) <= nn)%nat ->
     exists F, pj_foR segs m0 lblk0 nn o ((kids, 56 * cap) :: (keys, 8 * cap) :: D1 ++ (x, kx) :: Du ++ D2) F /\
       map (fun b : Z * Z => snd b + PresetReqAt.HEAD) F = PresetReqAt.fo (PjTree.JObj ms)) ->
  nth_error ms i = Some (kname, vi) ->
  pj_memsR segs m0 lblk0 (pj_nodeR segs m0 lblk0) kids keys (firstn i ms) D1 ->
  pj_nodeR segs m0 lblk0 (kids + 56 * Z.of_nat i) vi Du ->
  pj_memsR segs m0 lblk0 (pj_nodeR segs m0 lblk0) (kids + 56 * Z.of_nat (S i)) (keys + 8 * Z.of_nat (S i))
    (skipn (S i) ms) D2 ->
  z = kids + 56 * Z.of_nat i ->
  (forall nv, (PjTree.depth tv <= nv)%nat ->
     exists Fw, pj_foR segs m2 lblk' nv w Dw Fw /\
       map (fun b : Z * Z => snd b + PresetReqAt.HEAD) Fw = PresetReqAt.fo tv) ->
  (forall j, 0 <= j < 56 -> mbyte segs m' (z + j) = mbyte segs m2 (w + j)) ->
  pj_rwR segs m' z -> pj_apartR Dw z ->
  pj_agreeR segs m2 m' (fun y => exists b, In b Dw /\ pj_holdsR b y) ->
  pj_agreeR segs m0 m' (fun y => o <= y < o + 56 \/ kids <= y < kids + 56 * Z.of_nat i \/
     kids + 56 * Z.of_nat (S i) <= y < kids + 56 * Z.of_nat (length ms) \/
     keys <= y < keys + 8 * Z.of_nat (length ms) \/ exists b, In b (D1 ++ (x, kx) :: D2) /\ pj_holdsR b y) ->
  (forall a k, In (a, k) (D1 ++ (x, kx) :: D2) -> lblk' a k) ->
  lblk' kids (56 * cap) -> lblk' keys (8 * cap) ->
  (forall a k, In (a, k) Dw -> lblk' a k) ->
  NoDup ([(kids, 56 * cap); (keys, 8 * cap)] ++ D1 ++ (x, kx) :: Dw ++ D2) ->
  pj_apartR ([(kids, 56 * cap); (keys, 8 * cap)] ++ D1 ++ (x, kx) :: Dw ++ D2) o ->
  forall nn, (PjTree.depth (PjTree.JObj (firstn i ms ++ (kname, tv) :: skipn (S i) ms)) <= nn)%nat ->
    exists F, pj_foR segs m' lblk' nn o ([(kids, 56 * cap); (keys, 8 * cap)] ++ D1 ++ (x, kx) :: Dw ++ D2) F /\
      map (fun b : Z * Z => snd b + PresetReqAt.HEAD) F =
        PresetReqAt.fo (PjTree.JObj (firstn i ms ++ (kname, tv) :: skipn (S i) ms)).
Proof.
intros m0 m2 m' lblk0 lblk' o kids keys cap ms i kname vi tv D1 x kx Du D2 w z Dw
  HFN HNZ HN0 HFO Hnth HM1 HNU HM2 Ez HFW Hcpy Hrwz Hapz HAw HA0 HL1 Hlk Hly HLw Hnd Hap nn Hnn.
subst z.
pose proof (pj_nth_lenR ms i (kname, vi) Hnth) as Hi.
assert (Hlf : length (firstn i ms) = i) by (apply firstn_length_le; lia).
assert (Hls : length (skipn (S i) ms) = (length ms - S i)%nat) by (rewrite length_skipn; reflexivity).
assert (Hlen : length (firstn i ms ++ (kname, tv) :: skipn (S i) ms) = length ms).
{ rewrite length_app. cbn [length]. rewrite Hlf, Hls. lia. }
(* the result is an object: nn = S nn', each of its members at most nn' deep *)
destruct nn as [|nn']; [cbn [PjTree.depth] in Hnn; lia|].
assert (Hdep : forall nm u, In (nm, u) (firstn i ms ++ (kname, tv) :: skipn (S i) ms) ->
  (PjTree.depth u <= nn')%nat).
{ intros nm u Hu. pose proof (PjTree.depth_member _ nm u Hu). lia. }
(* the entry's ordered list at max (S nn') (depth (JObj ms)) = S d, decomposed *)
destruct (HFO (Nat.max (S nn') (PjTree.depth (PjTree.JObj ms))) ltac:(lia)) as (F0 & HF0 & HmF0).
assert (ED0 : Nat.max (S nn') (PjTree.depth (PjTree.JObj ms)) =
  S (Nat.max (S nn') (PjTree.depth (PjTree.JObj ms)) - 1)) by lia.
rewrite ED0 in HF0.
set (d := (Nat.max (S nn') (PjTree.depth (PjTree.JObj ms)) - 1)%nat) in HF0.
destruct (pjsf_obj_dest segs m0 lblk0 d o ms _ F0 HFN HNZ HN0 HF0)
  as (num & kids' & keys' & cap' & Dm & Di & Fi & Hhdr & HMm & HOi & PDm &
      [(_ & Ems & _) | (Hcp' & Hncap & _ & _ & ED & EF0)]).
{ rewrite Ems in Hnth. destruct i; discriminate Hnth. }
injection ED as Ek Ec Ey _ EDm. subst kids' keys' Dm F0.
assert (Ecap : cap' = cap) by lia. subst cap'.
rewrite (pjsf_fo_obj ms) in HmF0.
destruct (pjsf_slots_map segs m0 lblk0 d PresetReqAtNoMiss.kblk ms kids keys _ Di Fi
  [(kids, 56 * cap); (keys, 8 * cap)] (PresetReqAt.arrz true (PresetReqAt.ncap (length ms))) HFN HNZ HMm HOi HmF0
  ltac:(destruct (PresetReqAt.ncap (length ms)); cbn; lia)) as [HmFi HmArr].
destruct (pjsf_oitems_member segs m0 lblk0 d PresetReqAtNoMiss.kblk ms kids keys _ Di Fi i kname vi
  HFN HNZ HMm HOi HmFi Hnth)
  as (Di1 & Fi1 & Dk & Du' & Fu & Di2 & Fi2 & EDi & EFi & HO1 & HKk & HFu & HO2 & Hm1 & _ & HmK & Hm2).
subst Di Fi.
(* member i's entry blocks are the order list's own (up to order); the other blocks are the entry's others *)
pose proof (PjFoMember.pfm_corr_all segs m0 lblk0 HFN HNZ vi (kids + 56 * Z.of_nat i) Du d Du' Fu HNU HFu) as PU.
assert (PR : Permutation ((D1 ++ [(x, kx)]) ++ D2) ((Di1 ++ Dk) ++ Di2)).
{ apply (pjrA_perm_cancel_mid _ Du _ _ Du' _ PU).
  replace ((D1 ++ [(x, kx)]) ++ Du ++ D2) with (D1 ++ (x, kx) :: Du ++ D2) by (rewrite <- app_assoc; reflexivity).
  replace ((Di1 ++ Dk) ++ Du' ++ Di2) with (Di1 ++ Dk ++ Du' ++ Di2) by (rewrite <- app_assoc; reflexivity).
  exact PDm. }
assert (HinR : forall b, In b Di1 \/ In b Dk \/ In b Di2 -> In b (D1 ++ (x, kx) :: D2)).
{ intros b Hb.
  replace (D1 ++ (x, kx) :: D2) with ((D1 ++ [(x, kx)]) ++ D2) by (rewrite <- app_assoc; reflexivity).
  apply (Permutation_in _ (Permutation_sym PR)). rewrite <- app_assoc. apply in_or_app.
  destruct Hb as [Hb | [Hb | Hb]];
    [left; exact Hb | right; apply in_or_app; left; exact Hb | right; apply in_or_app; right; exact Hb]. }
(* the slots before and after member i: lowered to nn', then carried to the final memory *)
rewrite <- Hlf in HO1.
pose proof (pjsf_oitems_lower segs m0 lblk0 d nn' (firstn i ms) kids keys D1 Di1 Fi1 HM1 HO1
  (fun nm u Hu => Hdep nm u (in_or_app _ _ _ (or_introl Hu)))) as HO1l.
rewrite Hlf in HO1l.
rewrite <- Hls in HO2.
pose proof (pjsf_oitems_lower segs m0 lblk0 d nn' (skipn (S i) ms) _ _ D2 Di2 Fi2 HM2 HO2
  (fun nm u Hu => Hdep nm u (in_or_app (firstn i ms) ((kname, tv) :: skipn (S i) ms) (nm, u)
     (or_intror (or_intror Hu))))) as HO2l.
rewrite Hls in HO2l.
assert (HO1f : pf_oitemsR segs m' lblk' (pj_foR segs m' lblk' nn') true kids keys i Di1 Fi1).
{ apply (pf_oitemsR_frame segs nn' m0 m' lblk0 lblk' true kids keys i Di1 Fi1 HO1l).
  - intros a k Hb. apply HL1. apply HinR. left. exact Hb.
  - apply (pjrA_agree_sub segs m0 m' _ _ HA0). unfold pf_ofoot. cbv beta.
    intros y [Hy | [(_ & Hy) | (b & Hb & Hy)]].
    + right. left. exact Hy.
    + right. right. right. left. lia.
    + right. right. right. right. exists b. split; [apply HinR; left; exact Hb | exact Hy]. }
assert (HO2f : pf_oitemsR segs m' lblk' (pj_foR segs m' lblk' nn') true (kids + 56 * Z.of_nat (S i))
    (keys + 8 * Z.of_nat (S i)) (length ms - S i) Di2 Fi2).
{ apply (pf_oitemsR_frame segs nn' m0 m' lblk0 lblk' true _ _ _ Di2 Fi2 HO2l).
  - intros a k Hb. apply HL1. apply HinR. right. right. exact Hb.
  - apply (pjrA_agree_sub segs m0 m' _ _ HA0). unfold pf_ofoot. cbv beta.
    intros y [Hy | [(_ & Hy) | (b & Hb & Hy)]].
    + right. right. left. lia.
    + right. right. right. left. lia.
    + right. right. right. right. exists b. split; [apply HinR; right; right; exact Hb | exact Hy]. }
(* slot i: the key block kept, val's ordered list moved into the slot *)
assert (HKkf : pj_keyR segs m' lblk' true (keys + 8 * Z.of_nat i) Dk).
{ apply (pjrA_keyR_frame m0 m' lblk0 lblk' _ Dk HKk).
  - intros y Hy. apply (pjst_agree_b segs m0 m' _ y HA0). cbv beta. right. right. right. left. lia.
  - intros a k Hb. apply HL1. apply HinR. right. left. exact Hb. }
destruct (HFW nn' (Hdep kname tv (in_or_app (firstn i ms) ((kname, tv) :: skipn (S i) ms) (kname, tv)
  (or_intror (or_introl eq_refl))))) as (Fw & HFw & HmFw).
pose proof (pjsf_foR_move segs nn' m2 m' lblk' lblk' w (kids + 56 * Z.of_nat i) Dw Fw HFw Hcpy Hrwz Hapz HAw HLw)
  as HFwz.
(* reassembled *)
assert (HOone : pf_oitemsR segs m' lblk' (pj_foR segs m' lblk' nn') true (kids + 56 * Z.of_nat i)
    (keys + 8 * Z.of_nat i) 1 (Dk ++ Dw) (Fw ++ Dk)).
{ apply (proj2 (pjsf_oitems_one segs m' lblk' (pj_foR segs m' lblk' nn') true _ _ (Dk ++ Dw) (Fw ++ Dk))).
  exists Dk, Dw, Fw. split; [reflexivity|]. split; [reflexivity|]. split; [exact HKkf | exact HFwz]. }
assert (HOtail : pf_oitemsR segs m' lblk' (pj_foR segs m' lblk' nn') true (kids + 56 * Z.of_nat i)
    (keys + 8 * Z.of_nat i) (1 + (length ms - S i)) ((Dk ++ Dw) ++ Di2) ((Fw ++ Dk) ++ Fi2)).
{ apply (proj2 (pjsf_oitems_app segs m' lblk' (pj_foR segs m' lblk' nn') true 1 (length ms - S i) _ _ _ _)).
  exists (Dk ++ Dw), (Fw ++ Dk), Di2, Fi2. split; [reflexivity|]. split; [reflexivity|]. split; [exact HOone|].
  replace (kids + 56 * Z.of_nat i + 56 * Z.of_nat 1) with (kids + 56 * Z.of_nat (S i)) by lia.
  replace (keys + 8 * Z.of_nat i + 8 * Z.of_nat 1) with (keys + 8 * Z.of_nat (S i)) by lia.
  exact HO2f. }
assert (HOall : pf_oitemsR segs m' lblk' (pj_foR segs m' lblk' nn') true kids keys (i + (1 + (length ms - S i)))
    (Di1 ++ (Dk ++ Dw) ++ Di2) (Fi1 ++ (Fw ++ Dk) ++ Fi2)).
{ apply (proj2 (pjsf_oitems_app segs m' lblk' (pj_foR segs m' lblk' nn') true i (1 + (length ms - S i)) _ _ _ _)).
  exists Di1, Fi1, ((Dk ++ Dw) ++ Di2), ((Fw ++ Dk) ++ Fi2). split; [reflexivity|]. split; [reflexivity|].
  split; [exact HO1f | exact HOtail]. }
assert (PNew : Permutation ([(kids, 56 * cap); (keys, 8 * cap)] ++ D1 ++ (x, kx) :: Dw ++ D2)
    ((kids, 56 * cap) :: (keys, 8 * cap) :: Di1 ++ (Dk ++ Dw) ++ Di2)).
{ cbn [app]. apply perm_skip. apply perm_skip.
  replace (D1 ++ (x, kx) :: Dw ++ D2) with ((D1 ++ [(x, kx)]) ++ Dw ++ D2) by (rewrite <- app_assoc; reflexivity).
  replace (Di1 ++ (Dk ++ Dw) ++ Di2) with ((Di1 ++ Dk) ++ Dw ++ Di2) by (rewrite <- !app_assoc; reflexivity).
  exact (pjrA_perm_ins _ _ _ _ Dw PR). }
assert (HndN : NoDup ((kids, 56 * cap) :: (keys, 8 * cap) :: Di1 ++ (Dk ++ Dw) ++ Di2))
  by exact (pjrA_nodup_perm _ _ Hnd PNew).
assert (HapN : pj_apartR ((kids, 56 * cap) :: (keys, 8 * cap) :: Di1 ++ (Dk ++ Dw) ++ Di2) o).
{ intros b y Hb. apply (Hap b y). exact (Permutation_in _ (Permutation_sym PNew) Hb). }
assert (Hhdr' : pj_hdrR segs m' o 6 num 0 kids keys (Z.of_nat (length ms)) cap).
{ apply (pj_hdrR_frame segs m0 m' o 6 num 0 kids keys (Z.of_nat (length ms)) cap Hhdr).
  apply (pjrA_agree_sub segs m0 m' _ _ HA0). intros y Hy. cbv beta. left. exact Hy. }
assert (Ecnt : Z.to_nat (Z.of_nat (length ms)) = (i + (1 + (length ms - S i)))%nat) by lia.
rewrite <- Ecnt in HOall.
pose proof (pjsf_obj_intro segs m' lblk' nn' o num kids keys (Z.of_nat (length ms)) cap _ _ Hhdr' ltac:(lia) Hcp'
  Hlk Hly HndN HapN HOall) as HFn.
exists ((Fi1 ++ (Fw ++ Dk) ++ Fi2) ++ [(kids, 56 * cap); (keys, 8 * cap)]). split.
- exact (PjFoMember.pfm_foR_perm segs m' lblk' (S nn') o _ _ _ HFn (Permutation_sym PNew) Hnd Hap).
- rewrite (pjsf_fo_obj (firstn i ms ++ (kname, tv) :: skipn (S i) ms)), Hlen, pjsf_slots_app,
    PjFoMember.pfm_slots_cons.
  rewrite !map_app, Hm1, HmFw, HmK, Hm2, HmArr. rewrite <- !app_assoc. reflexivity.
Qed.
End nt.

(* ---- one `beq` step at a listing offset (taken: b = true; falls through: b = false) ---- *)
Section st. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
#[local] Notation PA := PI_prog_A.
#[local] Notation SEGS := (@pa_segs _ A_prog_listing PA).
#[local] Notation BASE := (@pa_val _ A_prog_listing PA A_TEXT).
Lemma pjrA_step_beq : forall (W : world SEGS) (regs : bvmap 5 word) (mem : word -> option byte)
  (md : Model) (Q : world SEGS -> config -> Prop) (k : Z) w (rs1 rs2 : bv 5) (imm : bv 13) (pc' : word) (b : bool),
  clookup (@pa_tbl _ A_prog_listing PA) (BASE + k) = Some w ->
  decode_any (Z_to_bv 32 w) = Some (Branch BC_EQ rs1 rs2 imm, 4%Z) ->
  c_eq (getr regs rs1) (getr regs rs2) = b ->
  (if b then btgt (Z_to_bv 64 (BASE + k)) (bv_signed imm) else v_addi (Z_to_bv 64 (BASE + k)) 4) = pc' ->
  (forall X, SRr SEGS W (mkCfg (@YK11.mkst fx regs pc' mem (YK11.seg_rom SEGS))
     (with_vm_backing (m_vm_lazy md) X md)) Q) ->
  SRr SEGS W (mkCfg (@YK11.mkst fx regs (Z_to_bv 64 (BASE + k)) mem (YK11.seg_rom SEGS)) md) Q.
Proof.
intros W regs mem md Q k w rs1 rs2 imm pc' b Hl Hd Hc Hpc HK. subst pc'.
destruct b; (eapply (SRr_step SEGS (@pa_wx _ A_prog_listing PA) W); [reflexivity | |]).
- rewrite (restrict_mkst_fx (fx := fx)).
  exact (step_beq_tk (fx := fx) SEGS regs (Z_to_bv 64 (BASE + k)) (mrestrict (w_H W) mem) (YK11.seg_rom SEGS)
    (Z_to_bv 32 w) rs1 rs2 imm (pa_fetch_ok (PI := PA) _ _ Hl) (not_ecall_of_decode _ _ _ Hd ltac:(discriminate))
    Hd Hc).
- intros model' Hs. rewrite (same_but_materialized_wvb md model' Hs).
  cbn [ms_regs ms_mem YK11.mkst]. rewrite (unrestrict_mkst_mrestrict (fx := fx)). apply HK.
- rewrite (restrict_mkst_fx (fx := fx)).
  exact (step_beq_ft (fx := fx) SEGS regs (Z_to_bv 64 (BASE + k)) (mrestrict (w_H W) mem) (YK11.seg_rom SEGS)
    (Z_to_bv 32 w) rs1 rs2 imm (pa_fetch_ok (PI := PA) _ _ Hl) (not_ecall_of_decode _ _ _ Hd ltac:(discriminate))
    Hd Hc).
- intros model' Hs. rewrite (same_but_materialized_wvb md model' Hs).
  cbn [ms_regs ms_mem YK11.mkst]. rewrite (unrestrict_mkst_mrestrict (fx := fx)). apply HK.
Qed.
End st.

(* ---- the ledger's blocks at a state, and a placed struct ---- *)
Section lg. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams} {RL : PrhRoomLive}.
Context {SK : YI16.sink_head}.
#[local] Notation PA := PI_prog_A.
#[local] Notation SEGS := (@pa_segs _ A_prog_listing PA).
#[local] Notation PST := (prh_pst (PI := prh_img_A)).
Variable B : asyms.
Variable ARx : alayout -> astate -> list Z -> world SEGS -> (word -> option byte) -> Model -> Prop.
#[local] Abbreviation rdW W mem := (mrestrict (w_H W) mem).
(* a callee's journal at a world relation RJ (inferred from the journal argument; pj_free's is at the re-hiding
   relation, pj_get's at wle; no lemma here reads the world conjunct) *)
Context {RJ : world SEGS -> world SEGS -> Prop}.
#[local] Notation AJ := (ajournal_xR (SK := SK) SEGS B PST ARx RJ).
Hypothesis LAWS : AR_laws_x SEGS B ARx cf_head.
Hypothesis HW8 : @prh_head_wide cp.

(* a harness block of the ledger: its allocator block, its bounds, its bytes present *)
Lemma pjrA_hb : forall ly S Hp W mem md Lam peak cnt fail ran most own a k,
  ARx ly S Hp W mem md -> prh_ledger (PA := PA) B ly S Hp W mem Lam peak cnt fail ran most own -> In (a, k) Lam ->
  0 <= k /\ In (a - cf_head, k + cf_head) (ablocks B ly S) /\ a mod 16 = 0 /\ 4096 <= a - cf_head /\
  a + k <= YM05.alloc_ceiling /\ req_size (k + cf_head) = k + cf_head /\ in_app (a - cf_head) (k + cf_head) /\
  (forall y, a - cf_head <= y < a + k -> apresent (w_H W) mem y /\ ~ aowned B ly S y).
Proof.
intros ly S Hp W mem md Lam peak cnt fail ran most own a k HAR HL Hin.
destruct (prh_ledger_hblock B ly S Hp W mem Lam peak cnt fail ran a k most own HL Hin) as (Hk0 & Hab & _ & Hal & _).
destruct (alx_blocks SEGS B ARx LAWS ly S Hp W mem md _ _ HAR Hab) as (_ & H4096 & Hcl & Happ & Hpo & _).
pose proof HW8 as Hw. unfold prh_head_wide in Hw.
assert (Rq : req_size (k + cf_head) = k + cf_head) by (unfold req_size; destruct (Z.eqb_spec (k + cf_head) 0); lia).
rewrite Rq in Hcl, Happ, Hpo.
split; [exact Hk0|]. split; [exact Hab|]. split; [exact Hal|]. split; [exact H4096|].
split; [lia|]. split; [exact Rq|]. split; [exact Happ|].
intros y Hy. apply Hpo. lia.
Qed.

(* two ledger blocks: their allocator blocks (head word included) are disjoint *)
Lemma pjrA_lam_sep : forall ly S Hp W mem md Lam peak cnt fail ran most own a k a' k' y,
  ARx ly S Hp W mem md -> prh_ledger (PA := PA) B ly S Hp W mem Lam peak cnt fail ran most own ->
  In (a, k) Lam -> In (a', k') Lam -> (a, k) <> (a', k') ->
  a - cf_head <= y < a + k -> ~ (a' - cf_head <= y < a' + k').
Proof.
intros ly S Hp W mem md Lam peak cnt fail ran most own a k a' k' y HAR HL H1 H2 Hne Hy Hy'.
destruct (pjrA_hb ly S Hp W mem md Lam peak cnt fail ran most own a k HAR HL H1) as (_ & Hab & _ & _ & _ & Rq & _).
destruct (pjrA_hb ly S Hp W mem md Lam peak cnt fail ran most own a' k' HAR HL H2) as (_ & Hab' & _ & _ & _ & Rq' & _).
assert (Hne2 : (a - cf_head, k + cf_head) <> (a' - cf_head, k' + cf_head)).
{ intros E. injection E as E1 E2. apply Hne. f_equal; lia. }
pose proof (sep_blocks_x SEGS B ARx LAWS ly S Hp W mem md _ _ _ _ HAR Hab Hab' Hne2) as Hd.
unfold zdisjoint in Hd. cbn [fst snd] in Hd. rewrite Rq, Rq' in Hd. lia.
Qed.

(* a struct placed as prhReader_at says lies off every ledger block whose user bytes do not hold it *)
Lemma pjrA_place_off : forall ly S Hp W mem md Lam peak cnt fail ran most own (regs : bvmap 5 word) e p a k,
  ARx ly S Hp W mem md -> prh_ledger (PA := PA) B ly S Hp W mem Lam peak cnt fail ran most own ->
  prhReader_at B ly S Lam regs e p 56 -> YM05.alloc_ceiling <= spZ regs ->
  In (a, k) Lam -> (forall y, p <= y < p + 56 -> ~ (a <= y < a + k)) ->
  forall y, p <= y < p + 56 -> ~ (a - cf_head <= y < a + k).
Proof.
intros ly S Hp W mem md Lam peak cnt fail ran most own regs e p a k HAR HL Hat Hsp Hin Hno y Hy.
pose proof (@cf_head_nonneg cp) as Hh0.
destruct (pjrA_hb ly S Hp W mem md Lam peak cnt fail ran most own a k HAR HL Hin) as (Hk0 & Hab & _ & _ & Hcl & Rq & _).
destruct Hat as [(a' & k' & Hin' & H1 & H2) | [(b & m & Hbm & HnL & H1 & H2) | [(cid & pos & Hcp & H1 & H2) | (H1 & H2)]]].
- destruct (Z.eq_dec a a') as [Ea | Na]; [destruct (Z.eq_dec k k') as [Ek | Nk] |].
  + subst a' k'. exfalso. exact (Hno p ltac:(lia) ltac:(lia)).
  + intros Hy'. apply (pjrA_lam_sep ly S Hp W mem md Lam peak cnt fail ran most own a' k' a k y HAR HL Hin' Hin
      ltac:(intros E; injection E as _ E2; exact (Nk (eq_sym E2))) ltac:(lia) Hy').
  + intros Hy'. apply (pjrA_lam_sep ly S Hp W mem md Lam peak cnt fail ran most own a' k' a k y HAR HL Hin' Hin
      ltac:(intros E; injection E as E1 _; exact (Na (eq_sym E1))) ltac:(lia) Hy').
- assert (Hne : (b, m) <> (a - cf_head, k + cf_head)).
  { intros E. injection E as E1 E2. apply HnL. replace (b + cf_head, m - cf_head) with (a, k) by (f_equal; lia).
    exact Hin. }
  pose proof (sep_blocks_x SEGS B ARx LAWS ly S Hp W mem md _ _ _ _ HAR Hbm Hab Hne) as Hd.
  pose proof (pjsA_req m ltac:(lia)) as (_ & _ & Rm). unfold zdisjoint in Hd. cbn [fst snd] in Hd.
  rewrite Rq, Rm in Hd by lia. lia.
- pose proof (sep_block_frame_x SEGS B ARx LAWS ly S Hp W mem md _ _ cid pos HAR Hab Hcp) as Hd.
  unfold zdisjoint in Hd. cbn [fst snd] in Hd. rewrite Rq in Hd. lia.
- lia.
Qed.

(* a placed struct holds no byte of a ledger block's head [a - cf_head, a) *)
Lemma pjrA_place_head : forall ly S Hp W mem md Lam peak cnt fail ran most own (regs : bvmap 5 word) e p a k,
  ARx ly S Hp W mem md -> prh_ledger (PA := PA) B ly S Hp W mem Lam peak cnt fail ran most own ->
  prhReader_at B ly S Lam regs e p 56 -> YM05.alloc_ceiling <= spZ regs -> In (a, k) Lam ->
  forall y, p <= y < p + 56 -> ~ (a - cf_head <= y < a).
Proof.
intros ly S Hp W mem md Lam peak cnt fail ran most own regs e p a k HAR HL Hat Hsp Hin y Hy.
pose proof (@cf_head_nonneg cp) as Hh0.
destruct (pjrA_hb ly S Hp W mem md Lam peak cnt fail ran most own a k HAR HL Hin) as (Hk0 & Hab & _ & _ & Hcl & Rq & _).
destruct Hat as [(a' & k' & Hin' & H1 & H2) | [(b & m & Hbm & HnL & H1 & H2) | [(cid & pos & Hcp & H1 & H2) | (H1 & H2)]]].
- destruct (Z.eq_dec a a') as [Ea | Na]; [destruct (Z.eq_dec k k') as [Ek | Nk] |].
  + subst a' k'. lia.
  + intros Hy'. apply (pjrA_lam_sep ly S Hp W mem md Lam peak cnt fail ran most own a' k' a k y HAR HL Hin' Hin
      ltac:(intros E; injection E as _ E2; exact (Nk (eq_sym E2))) ltac:(lia)). lia.
  + intros Hy'. apply (pjrA_lam_sep ly S Hp W mem md Lam peak cnt fail ran most own a' k' a k y HAR HL Hin' Hin
      ltac:(intros E; injection E as E1 _; exact (Na (eq_sym E1))) ltac:(lia)). lia.
- assert (Hne : (b, m) <> (a - cf_head, k + cf_head)).
  { intros E. injection E as E1 E2. apply HnL. replace (b + cf_head, m - cf_head) with (a, k) by (f_equal; lia).
    exact Hin. }
  pose proof (sep_blocks_x SEGS B ARx LAWS ly S Hp W mem md _ _ _ _ HAR Hbm Hab Hne) as Hd.
  pose proof (pjsA_req m ltac:(lia)) as (_ & _ & Rm). unfold zdisjoint in Hd. cbn [fst snd] in Hd.
  rewrite Rq, Rm in Hd by lia. lia.
- pose proof (sep_block_frame_x SEGS B ARx LAWS ly S Hp W mem md _ _ cid pos HAR Hab Hcp) as Hd.
  unfold zdisjoint in Hd. cbn [fst snd] in Hd. rewrite Rq in Hd. lia.
- lia.
Qed.

(* where a placed struct lies: below the allocator ceiling in a live block or frame (its bytes present, no image
   byte), or in the caller's window *)
Lemma pjrA_at_where : forall ly S Hp W mem md Lam peak cnt fail ran most own (regs : bvmap 5 word) e p,
  ARx ly S Hp W mem md -> prh_ledger (PA := PA) B ly S Hp W mem Lam peak cnt fail ran most own ->
  prhReader_at B ly S Lam regs e p 56 ->
  (4096 <= p /\ p + 56 <= YM05.alloc_ceiling /\
   forall x, p <= x < p + 56 -> apresent (w_H W) mem x /\ ~ in_img SEGS x /\
     ((exists b n, In (b, n) (ablocks B ly S) /\ b <= x < b + req_size n) \/
      (exists cid pos, In (cid, pos) (frames S) /\ in_zr x (frame_rng ly (cid, pos))))) \/
  (spZ regs <= p /\ p + 56 <= spZ regs + e).
Proof.
intros ly S Hp W mem md Lam peak cnt fail ran most own regs e p HAR HL Hat.
pose proof (@cf_head_nonneg cp) as Hh0.
destruct Hat as [(a & k & Hin & H1 & H2) | [(b & m & Hbm & HnL & H1 & H2) | [(cid & pos & Hcp & H1 & H2) | Hs]]].
- left. destruct (pjrA_hb ly S Hp W mem md Lam peak cnt fail ran most own a k HAR HL Hin) as (Hk0 & Hab & _ & H4096 & Hcl & Rq & _ & Hpo).
  split; [lia|]. split; [lia|]. intros x Hx.
  split; [exact (proj1 (Hpo x ltac:(lia)))|].
  split; [apply (blk_img_x SEGS B ARx LAWS ly S Hp W mem md _ _ x HAR Hab); rewrite Rq; lia|].
  left. exists (a - cf_head), (k + cf_head). split; [exact Hab | rewrite Rq; lia].
- left. destruct (alx_blocks SEGS B ARx LAWS ly S Hp W mem md b m HAR Hbm) as (_ & H4096 & Hcl & _ & Hpo & _).
  pose proof (pjsA_req m ltac:(lia)) as (_ & _ & Rm). rewrite Rm in Hcl, Hpo by lia.
  split; [lia|]. split; [lia|]. intros x Hx.
  split; [exact (proj1 (Hpo x ltac:(lia)))|].
  split; [apply (blk_img_x SEGS B ARx LAWS ly S Hp W mem md _ _ x HAR Hbm); rewrite Rm; lia|].
  left. exists b, m. split; [exact Hbm | rewrite Rm; lia].
- left. destruct (frames_bounds_x SEGS B ARx LAWS ly S Hp W mem md cid pos HAR Hcp) as (Hf0 & Hfc & _).
  destruct (alx_frames SEGS B ARx LAWS ly S Hp W mem md cid pos HAR Hcp) as (_ & _ & Hfpo & _).
  split; [lia|]. split; [lia|]. intros x Hx.
  split; [exact (proj1 (Hfpo x ltac:(lia)))|].
  split; [exact (frm_img_x SEGS B ARx LAWS ly S Hp W mem md cid pos x HAR Hcp ltac:(lia))|].
  right. exists cid, pos. split; [exact Hcp | unfold in_zr, frame_rng; cbn [fst snd]; lia].
- right. exact Hs.
Qed.

(* what a call keeps of a placed struct: its bytes off the callee's footprint, and their presence *)
Lemma pjrA_place_call : forall ly S Hp W mem md Lam peak cnt fail ran most own STK1 sp sp1 FP1 ly2 S2 Hp2 W2 mem2 md2 k1
    Lam2 peak2 cnt2 fail2 ran2 most2 own2 (regs : bvmap 5 word) e p,
  ARx ly S Hp W mem md ->
  AJ STK1 sp FP1 ly S Hp W mem md [] ly2 S2 Hp2 W2 mem2 md2 k1 ->
  prh_ledger (PA := PA) B ly S Hp W mem Lam peak cnt fail ran most own ->
  prh_ledger (PA := PA) B ly2 S2 Hp2 W2 mem2 Lam2 peak2 cnt2 fail2 ran2 most2 own2 ->
  (forall a, sp1 <= a < sp -> ~ inFP FP1 a -> aview SEGS (w_H W2) mem2 a = aview SEGS (w_H W) mem a) ->
  (forall a, spZ regs <= a < spZ regs + e -> apresent (w_H W2) mem2 a) ->
  sp1 <= spZ regs -> spZ regs + e <= sp ->
  (forall a k, In (a, k) Lam -> a <= p -> p + 56 <= a + k -> In (a, k) Lam2) ->
  (forall b m, In (b, m) (ablocks B ly S) -> ~ In (b + cf_head, m - cf_head) Lam -> b <= p -> p + 56 <= b + m ->
     In (b, m) (ablocks B ly2 S2)) ->
  prhReader_at B ly S Lam regs e p 56 ->
  forall x, p <= x < p + 56 ->
    (~ inFP FP1 x -> aview SEGS (w_H W2) mem2 x = aview SEGS (w_H W) mem x) /\ apresent (w_H W2) mem2 x.
Proof.
intros ly S Hp W mem md Lam peak cnt fail ran most own STK1 sp sp1 FP1 ly2 S2 Hp2 W2 mem2 md2 k1 Lam2 peak2 cnt2 fail2 ran2 most2 own2
  regs e p HAR HJ HL HL2 HX HPR Hs1 Hs2 HSL HSB Hat x Hx.
pose proof (@cf_head_nonneg cp) as Hh0.
pose proof (ajxR_ar HJ) as HAR2. pose proof (ajxR_ly HJ) as Hly. pose proof (ajxR_frs HJ) as Hfr. pose proof (ajxR_frm HJ) as F4.
rewrite app_nil_l in Hfr.
destruct Hat as [(a & k & Hin & H1 & H2) | [(b & m & Hbm & HnL & H1 & H2) | [(cid & pos & Hcp & H1 & H2) | (H1 & H2)]]].
- pose proof (HSL a k Hin H1 H2) as Hin2.
  destruct (pjrA_hb ly S Hp W mem md Lam peak cnt fail ran most own a k HAR HL Hin) as (_ & Hab & _ & _ & _ & Rq & _).
  destruct (pjrA_hb ly2 S2 Hp2 W2 mem2 md2 Lam2 peak2 cnt2 fail2 ran2 most2 own2 a k HAR2 HL2 Hin2) as (_ & Hab2 & _ & _ & _ & _ & _ & Hpo2).
  split; [intros Hf | exact (proj1 (Hpo2 x ltac:(lia)))].
  exact (pjsA_blk_bytes B ARx ly S Hp W mem md STK1 sp FP1 ly2 S2 Hp2 W2 mem2 md2 k1 _ _ x HJ Hab Hab2
    ltac:(rewrite Rq; lia) Hf).
- pose proof (HSB b m Hbm HnL H1 H2) as Hbm2.
  destruct (alx_blocks SEGS B ARx LAWS ly2 S2 Hp2 W2 mem2 md2 b m HAR2 Hbm2) as (_ & _ & _ & _ & Hpo2 & _).
  pose proof (pjsA_req m ltac:(lia)) as (Rm & _).
  split; [intros Hf | exact (proj1 (Hpo2 x ltac:(lia)))].
  exact (pjsA_blk_bytes B ARx ly S Hp W mem md STK1 sp FP1 ly2 S2 Hp2 W2 mem2 md2 k1 _ _ x HJ Hbm Hbm2 ltac:(lia) Hf).
- assert (Efa : forall cid pos, frame_addr ly2 cid pos = frame_addr ly cid pos).
  { intros cid' pos'. unfold frame_addr. destruct Hly as (_ & _ & _ & _ & _ & EF & _). rewrite EF. reflexivity. }
  assert (Hcp2 : In (cid, pos) (frames S2)) by (rewrite Hfr; exact Hcp).
  destruct (alx_frames SEGS B ARx LAWS ly2 S2 Hp2 W2 mem2 md2 cid pos HAR2 Hcp2) as (_ & _ & Hfpo & _).
  rewrite Efa in Hfpo.
  split; [intros Hf | exact (proj1 (Hfpo x ltac:(lia)))].
  apply (F4 cid pos x Hcp); [left; unfold in_zr, frame_rng; cbn [fst snd]; lia | exact Hf].
- split; [intros Hf; apply HX; [lia | exact Hf] | apply HPR; lia].
Qed.

(* what a call keeps of a tree's footprint: its header bytes given, its blocks ledger blocks on both sides and off
   the callee's footprint *)
Lemma pjrA_tree_agree : forall ly S Hp W mem md Lam peak cnt fail ran most own STK1 sp FP1 ly2 S2 Hp2 W2 mem2 md2 k1
    Lam2 peak2 cnt2 fail2 ran2 most2 own2 p (D : list (Z * Z)),
  AJ STK1 sp FP1 ly S Hp W mem md [] ly2 S2 Hp2 W2 mem2 md2 k1 ->
  prh_ledger (PA := PA) B ly S Hp W mem Lam peak cnt fail ran most own ->
  prh_ledger (PA := PA) B ly2 S2 Hp2 W2 mem2 Lam2 peak2 cnt2 fail2 ran2 most2 own2 ->
  (forall x, p <= x < p + 56 -> aview SEGS (w_H W2) mem2 x = aview SEGS (w_H W) mem x) ->
  pj_rwR SEGS (rdW W2 mem2) p ->
  (forall a k, In (a, k) D -> In (a, k) Lam) ->
  (forall a k, In (a, k) D -> In (a, k) Lam2) ->
  (forall x, (exists b, In b D /\ pj_holdsR b x) -> ~ inFP FP1 x) ->
  pj_agreeR SEGS (rdW W mem) (rdW W2 mem2) (pj_footR p D).
Proof.
intros ly S Hp W mem md Lam peak cnt fail ran most own STK1 sp FP1 ly2 S2 Hp2 W2 mem2 md2 k1 Lam2 peak2 cnt2 fail2 ran2 most2 own2 p D
  HJ HL HL2 HHB Hrw2 HDL HDL2 HFP.
pose proof (@cf_head_nonneg cp) as Hh0.
pose proof (ajxR_ar HJ) as HAR2.
pose proof HL2 as (_ & _ & HLF2 & _).
apply pjsA_agree.
- intros x [Hx | ((a, k) & Hb & Hx)].
  + exact (HHB x Hx).
  + unfold pj_holdsR in Hx. cbn [fst snd] in Hx.
    exact (pjsA_lam_bytes B ARx ly S Hp W mem md STK1 sp FP1 ly2 S2 Hp2 W2 mem2 md2 k1 Lam peak cnt fail ran most own
      Lam2 peak2 cnt2 fail2 ran2 most2 own2 a k x HJ HL HL2 (HDL a k Hb) (HDL2 a k Hb) Hx
      (HFP x (ex_intro _ (a, k) (conj Hb Hx)))).
- intros x [Hx | ((a, k) & Hb & Hx)] _.
  + exact (proj2 Hrw2 x Hx).
  + unfold pj_holdsR in Hx. cbn [fst snd] in Hx.
    pose proof (proj1 (Forall_forall _ _) HLF2 (a, k) (HDL2 a k Hb)) as (Hk0 & Hab2 & _). cbn [fst snd] in Hk0, Hab2.
    pose proof (pjsA_req (k + @cf_head cp) ltac:(lia)) as (Rq & _).
    exact (pjsA_blk_writable B ARx LAWS ly2 S2 Hp2 W2 mem2 md2 _ _ x HAR2 Hab2 ltac:(lia)).
Qed.

(* a tree across a call, its header bytes given *)
Lemma pjrA_tree_kept : forall ly S Hp W mem md Lam peak cnt fail ran most own STK1 sp FP1 ly2 S2 Hp2 W2 mem2 md2 k1
    Lam2 peak2 cnt2 fail2 ran2 most2 own2 p t D,
  AJ STK1 sp FP1 ly S Hp W mem md [] ly2 S2 Hp2 W2 mem2 md2 k1 ->
  prh_ledger (PA := PA) B ly S Hp W mem Lam peak cnt fail ran most own ->
  prh_ledger (PA := PA) B ly2 S2 Hp2 W2 mem2 Lam2 peak2 cnt2 fail2 ran2 most2 own2 ->
  (forall x, p <= x < p + 56 -> aview SEGS (w_H W2) mem2 x = aview SEGS (w_H W) mem x) ->
  pj_rwR SEGS (rdW W2 mem2) p ->
  (forall a k, In (a, k) D -> In (a, k) Lam2) ->
  (forall x, (exists b, In b D /\ pj_holdsR b x) -> ~ inFP FP1 x) ->
  pj_nodeR SEGS (rdW W mem) (prh_lin Lam) p t D ->
  pj_nodeR SEGS (rdW W2 mem2) (prh_lin Lam2) p t D.
Proof.
intros ly S Hp W mem md Lam peak cnt fail ran most own STK1 sp FP1 ly2 S2 Hp2 W2 mem2 md2 k1 Lam2 peak2 cnt2 fail2 ran2 most2 own2 p t D
  HJ HL HL2 HHB Hrw2 HDL2 HFP HN.
apply (pjst_node_frame SEGS t (rdW W mem) (rdW W2 mem2) (prh_lin Lam) (prh_lin Lam2) p D HN); [|exact HDL2].
exact (pjrA_tree_agree ly S Hp W mem md Lam peak cnt fail ran most own STK1 sp FP1 ly2 S2 Hp2 W2 mem2 md2 k1
  Lam2 peak2 cnt2 fail2 ran2 most2 own2 p D HJ HL HL2 HHB Hrw2
  (fun a k Hb => pjst_node_lblk SEGS t _ _ p D HN a k Hb) HDL2 HFP).
Qed.

(* an agreement from byte equality and presence at the later state *)
Lemma pjrA_agree_pres : forall (W W2 : world SEGS) mem mem2 (X : Z -> Prop),
  (forall x, X x -> aview SEGS (w_H W2) mem2 x = aview SEGS (w_H W) mem x) ->
  (forall x, X x -> apresent (w_H W2) mem2 x) ->
  pj_agreeR SEGS (rdW W mem) (rdW W2 mem2) X.
Proof.
intros W W2 mem mem2 X HA HP. apply pjsA_agree; [exact HA|]. intros x Hx _.
exact (apresent_writable SEGS _ _ x (HP x Hx)).
Qed.
End lg.

(* ---- the replaced member against the model (the event form): the new object's block sizes, the pj_free event,
   the position after it ---- *)
Lemma pjrA_skipn_nth : forall {A : Type} (l : list A) i a, nth_error l i = Some a ->
  skipn i l = a :: skipn (S i) l.
Proof.
intros A l. induction l as [|h t IH]; intros i a H; [destruct i; discriminate H|].
destruct i as [|i]; cbn [nth_error] in H.
- injection H as ->. reflexivity.
- cbn [skipn]. exact (IH i a H).
Qed.

Lemma pjrA_concat_nth : forall {A B : Type} (f : A -> list B) (l : list A) i a, nth_error l i = Some a ->
  concat (map f l) = concat (map f (firstn i l)) ++ f a ++ concat (map f (skipn (S i) l)).
Proof.
intros A B f l. induction l as [|h t IH]; intros i a H; [destruct i; discriminate H|].
destruct i as [|i]; cbn [nth_error] in H.
- injection H as ->. reflexivity.
- cbn [firstn skipn map concat]. rewrite (IH i a H). rewrite <- app_assoc. reflexivity.
Qed.

(* THE BLOCK SIZES OF THE NEW OBJECT (the contract's block conjunct of tpj_set_specX's present-key arm, a Permutation): the
   object's whole-tree sizes (pjsA_pre's Permutation (map hb D) (tblk (JObj ms))) with member i's value blocks Du
   (sizes a permutation of tblk vi) replaced by Dw (sizes a permutation of tblk tv) are the whole-tree sizes of the
   object with member i's value replaced by tv. tblk's JObj clause is cut at member i on both sides
   (pjrA_concat_nth); the capacity term is the same (the member count is). *)
Lemma pjrA_tblk_swap : forall (hb : Z * Z -> Z) (ms : list (list Z * PjTree.jv)) i kname vi tv
    (Da Du Db Dw : list (Z * Z)),
  nth_error ms i = Some (kname, vi) ->
  Permutation (map hb (Da ++ Du ++ Db)) (PresetReqAtNoMiss.tblk (PjTree.JObj ms)) ->
  Permutation (map hb Du) (PresetReqAtNoMiss.tblk vi) ->
  Permutation (map hb Dw) (PresetReqAtNoMiss.tblk tv) ->
  Permutation (map hb (Da ++ Dw ++ Db))
    (PresetReqAtNoMiss.tblk (PjTree.JObj (firstn i ms ++ (kname, tv) :: skipn (S i) ms))).
Proof.
intros hb ms i kname vi tv Da Du Db Dw Hnth HM HU HW.
pose proof (pj_nth_lenR ms i (kname, vi) Hnth) as Hi.
assert (Hlen : length (firstn i ms ++ (kname, tv) :: skipn (S i) ms) = length ms).
{ rewrite length_app. cbn [length]. rewrite firstn_length_le by lia. rewrite length_skipn. lia. }
assert (ET : forall L, PresetReqAtNoMiss.tblk (PjTree.JObj L) =
  PresetReqAt.arrz true (PresetReqAtNoMiss.capf 0 0 (length L)) ++
  concat (map (fun mm => PresetReqAtNoMiss.kblk (fst mm) :: PresetReqAtNoMiss.tblk (snd mm)) L))
  by (intros L; reflexivity).
rewrite (ET ms), (pjrA_concat_nth _ ms i (kname, vi) Hnth) in HM.
rewrite (ET (firstn i ms ++ (kname, tv) :: skipn (S i) ms)), Hlen, (map_app _ (firstn i ms)), concat_app.
cbn [map concat fst snd] in HM |- *.
set (A := PresetReqAt.arrz true (PresetReqAtNoMiss.capf 0 0 (length ms))) in *.
set (X := concat (map (fun mm => PresetReqAtNoMiss.kblk (fst mm) :: PresetReqAtNoMiss.tblk (snd mm))
  (firstn i ms))) in *.
set (Y := concat (map (fun mm => PresetReqAtNoMiss.kblk (fst mm) :: PresetReqAtNoMiss.tblk (snd mm))
  (skipn (S i) ms))) in *.
rewrite !map_app in HM |- *.
(* the sizes of every block but member i's value, both sides *)
assert (HR : Permutation (map hb Da ++ map hb Db) (A ++ X ++ PresetReqAtNoMiss.kblk kname :: Y)).
{ apply (Permutation_app_inv_l (PresetReqAtNoMiss.tblk vi)).
  apply (Permutation_trans (Permutation_app (Permutation_sym HU) (Permutation_refl (map hb Da ++ map hb Db)))).
  apply (Permutation_trans (pjrA_perm_mid (map hb Du) (map hb Da) (map hb Db))).
  apply (Permutation_trans HM). apply pjrA_perm_pull. }
apply (Permutation_trans (pjrA_perm_mid (map hb Da) (map hb Dw) (map hb Db))).
apply (Permutation_trans (Permutation_app HW (Permutation_refl (map hb Da ++ map hb Db)))).
apply (Permutation_trans (Permutation_app (Permutation_refl (PresetReqAtNoMiss.tblk tv)) HR)).
apply Permutation_sym. apply pjrA_perm_pull.
Qed.

(* pj_get's member is the model's: the first member of that name *)
Lemma pjrA_mfind_first : forall (ms : list (list Z * PjTree.jv)) i kname vi,
  nth_error ms i = Some (kname, vi) ->
  (forall j nm u, (j < i)%nat -> nth_error ms j = Some (nm, u) -> nm <> kname) ->
  prhPj_mfind kname ms = Some vi.
Proof.
intros ms. induction ms as [|[k u] r IH]; intros i kname vi Hn Hf; [destruct i; discriminate Hn|].
destruct i as [|i]; cbn [nth_error] in Hn.
- injection Hn as -> ->. cbn [prhPj_mfind]. rewrite PresetReqAtNoMiss.zl_eqb_refl. reflexivity.
- cbn [prhPj_mfind]. destruct (PresetReqAt.zl_eqb k kname) eqn:E.
  + exfalso. apply (Hf 0%nat k u ltac:(lia) eq_refl). exact (PresetReqAtNoMiss.zl_eqb_true k kname E).
  + apply (IH i kname vi Hn). intros j nm u' Hj Hj'. exact (Hf (S j) nm u' ltac:(lia) Hj').
Qed.

(* pj_set's events on the present arm: the one bulk free of the replaced value *)
Lemma pjrA_set_evs_hit : forall (ms : list (list Z * PjTree.jv)) i kname vi n cap,
  nth_error ms i = Some (kname, vi) ->
  (forall j nm u, (j < i)%nat -> nth_error ms j = Some (nm, u) -> nm <> kname) ->
  prhPj_set_evs ms kname n cap = [PresetReqAt.HBulk (PresetReqAt.fo vi)].
Proof.
intros ms i kname vi n cap Hn Hf. unfold prhPj_set_evs. rewrite (pjrA_mfind_first ms i kname vi Hn Hf).
reflexivity.
Qed.

Section pos. Context {cp : CfParams}.
(* the position after pj_free (old): its text advances by its own events, one bulk free or none (an empty order
   list); the model's event there is HBulk (fo vi), the empty bulk free when the order list is empty, which
   PRH_FnPj.v prhPj_bulk_nil_pos steps over *)
Lemma pjrA_pos_after_free : forall rp_sm rp_x rp_os rp_i rp_H0 (vi : PjTree.jv) (F : list (Z * Z)) S,
  prh_run_at rp_sm rp_x rp_os rp_i [PresetReqAt.HBulk (PresetReqAt.fo vi)] ->
  (F = [] -> PresetReqAt.fo vi = []) ->
  (exists h, PresetRoomPos.iface_room_pos rp_sm rp_x rp_os (rp_i + length (prhPj_free_evs F))%nat rp_H0 h S) ->
  exists h, PresetRoomPos.iface_room_pos rp_sm rp_x rp_os (rp_i + 1)%nat rp_H0 h S.
Proof.
intros rp_sm rp_x rp_os rp_i rp_H0 vi F S HR HF (h & Hp).
destruct F as [|b F'].
- cbn [prhPj_free_evs length] in Hp. rewrite Nat.add_0_r in Hp. rewrite (HF eq_refl) in HR.
  apply prh_run_at_one in HR. exists h. replace (rp_i + 1)%nat with (Datatypes.S rp_i) by lia.
  exact (proj1 (prhPj_bulk_nil_pos rp_sm rp_x rp_os rp_i rp_H0 h S HR) Hp).
- cbn [prhPj_free_evs length] in Hp. exists h. exact Hp.
Qed.
End pos.
