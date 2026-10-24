(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Lia Bool.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import
YO0i YO0f YO0g YO0h YO12 YO0w YO0s YO0x
YO0z YO14 YO0v YO0q YO0a YO0d.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YN2b YN2k YN2f YN2w YN13 YN17.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.
Local Open Scope mm_scope.
Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Definition KSET : list Z := [28; 30; 54; 56; 60; 62; 120; 124; 125; 126].
Definition memZ (x : Z) (l : list Z) : bool := existsb (Z.eqb x) l.
Lemma kset_tab :
forallb (fun sc => forallb (fun cnt => negb (class_size sc * cnt + UNIT <=? PGSZ / 2) || memZ (znth sc size_classes * cnt) KSET)
(icands sc)) (zseq 0 48) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma memZ_In : forall x l, memZ x l = true -> In x l.
Proof. intros x l. unfold memZ. induction l as [|y t IH]; cbn; [discriminate|]. destruct (Z.eqb_spec x y); [intros _; left; lia | intros H; right; exact (IH H)]. Qed.
Lemma nested_k : forall sc u, 0 <= sc < 48 -> class_size sc * initial_cnt sc u + UNIT <= PGSZ / 2 ->
In (znth sc size_classes * initial_cnt sc u) KSET.
Proof.
intros sc u Hsc Harm. brute kset_tab sc as H. rewrite forallb_forall in H. specialize (H _ (initial_cnt_In sc u)).
apply Bool.orb_prop in H as [H|H]; [| exact (memZ_In _ _ H)].
exfalso. destruct (class_size sc * initial_cnt sc u + UNIT <=? PGSZ / 2) eqn:E; [discriminate|]. apply Z.leb_gt in E. lia.
Qed.
Definition jof (k : Z) : Z := if k <? 32 then 15 else if k <? 64 then 19 else 23.
Lemma kset_facts : forall k, In k KSET ->
size_to_class (16 * k + 12) = jof k /\ (jof k = 15 \/ jof k = 19 \/ jof k = 23) /\
class_size (jof k) = (if k <? 32 then 496 else if k <? 64 then 1008 else 2032) /\
16 * k + 12 + IB <= class_size (jof k) /\ 28 <= k <= 126.
Proof.
intros k Hk. cbn in Hk.
destruct Hk as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]]];
(split; [vm_compute; reflexivity|]); (split; [cbn; auto|]); (split; [vm_compute; reflexivity|]);
match goal with |- _ <= ?c /\ _ => let v := eval vm_compute in c in change c with v end; unfold IB; lia.
Qed.
Definition nest_rest (sc : Z) (m : sptr) (cnt0 j idx : Z) : M (option sptr) :=
hj <- get_head (HActive j) ;;
match hj with
| None => fail (FModel 8)
| Some g =>
amg <- getm g ;;
mcheck (stride_of amg =? class_size j) 11 ;;
s1 <- get ;;
p <- enframe g idx (class_size j - IB) (st_mmap_counter s1) FGroup ;;
install_group m sc cnt0 (cnt0 - 1) 0 p slot_junk ;;
ret (Some m)
end.
Definition KN (sc : Z) (m : sptr) (cnt0 j : Z) (r : Z * astate) : itree astate (option sptr * astate) :=
if fst r <? 0 then (free_meta m ;; ret None) (snd r) else nest_rest sc m cnt0 j (fst r) (snd r).
Lemma nest_body_eq : forall fuel sc req m s,
let cnt0 := initial_cnt sc (usage_of s sc) in
let total := UNIT + cnt0 * class_size sc - IB in
nest_body fuel sc req m s = ibind (alloc_slot fuel (size_to_class total) total s) (KN sc m cnt0 (size_to_class total)).
Proof.
intros fuel sc req m s cnt0 total. unfold nest_body. cbv zeta. fold cnt0. fold total. unfold bind at 1. apply ibind_ext.
intros [idx s']. unfold KN. cbn [fst snd]. destruct (idx <? 0); reflexivity.
Qed.
Definition am_nest0 (p : sptr) (sc cnt : Z) : ameta :=
mkAMeta None None p (ones (cnt - 1) - 1) (ones (cnt - 1) - ones (cnt - 1)) (cnt - 1) sc 0 (cnt - 1) (repeat slot_junk (Z.to_nat cnt)).
Definition am_nest (m : sptr) (p : sptr) (sc cnt : Z) : ameta := am_set_links (Some m) (Some m) (am_nest0 p sc cnt).
Definition am_enf (am : ameta) (idx j : Z) : ameta :=
upd_slot am idx (mkSlot (Some (idx + 192, class_size j * idx / UNIT)) (Some (mkFrame 0 (class_size j - IB) FGroup))).
Definition instn_st (sc : Z) (m : sptr) (cnt0 : Z) (p : sptr) (s : astate) : astate :=
let sB := set_usage (zset sc (usage_of s sc + cnt0) (st_usage s)) s in
let sC := upd_meta m (MUsed (am_nest0 p sc cnt0)) sB in
let sD := upd_meta m (MUsed (am_nest m p sc cnt0)) sC in
set_active (lupd (st_active s) (Z.to_nat sc) (Some m)) sD.
Lemma install_nest_eq : forall sc m cnt0 p s,
active_hd s sc = None ->
install_group m sc cnt0 (cnt0 - 1) 0 p slot_junk s = IRet (tt, instn_st sc m cnt0 p s).
Proof.
intros sc m cnt0 p s Hhd. unfold active_hd in Hhd.
unfold install_group, set_usage_of, setm, queue, get_links, massert, get_head, set_links, set_head, setslot, modify, bind, get, put, ret.
cbn - [ones class_size Z.sub Z.add Z.div Z.mul Z.ltb Z.land Z.pow zset usage_of Z.to_nat repeat UNIT lupd nth mlookup mupdate].
rewrite mlookup_mupdate_same.
cbn - [ones class_size Z.sub Z.add Z.div Z.mul Z.ltb Z.land Z.pow zset usage_of Z.to_nat repeat UNIT lupd nth mlookup mupdate].
rewrite Hhd.
cbn - [ones class_size Z.sub Z.add Z.div Z.mul Z.ltb Z.land Z.pow zset usage_of Z.to_nat repeat UNIT lupd nth mlookup mupdate].
rewrite mlookup_mupdate_same.
cbn - [ones class_size Z.sub Z.add Z.div Z.mul Z.ltb Z.land Z.pow zset usage_of Z.to_nat repeat UNIT lupd nth mlookup mupdate].
reflexivity.
Qed.
Lemma enframe_eval0 : forall s g am idx ctr,
MT s g = Some (MUsed am) -> 0 <= idx <= am_last am ->
enframe g idx (stride_of am - IB) ctr FGroup s =
IRet (slot_start am idx, upd_meta g (MUsed (upd_slot am idx (mkSlot (Some (idx + 192, stride_of am * idx / UNIT)) (Some (mkFrame 0 (stride_of am - IB) FGroup))))) s).
Proof.
intros s g am idx ctr Hm Hidx. unfold enframe.
rewrite (bind_IRet (getm g) _ s am s (getm_eval s g am Hm)).
rewrite (bind_IRet (mcheck _ 12) _ s tt s) by (unfold mcheck; rewrite (proj2 (Z.leb_le 0 idx)), (proj2 (Z.leb_le idx _)) by lia; reflexivity).
cbv zeta. replace ((stride_of am - IB - (stride_of am - IB)) / UNIT) with 0 by (rewrite Z.sub_diag; reflexivity).
rewrite (bind_IRet _ _ s 0 s) by reflexivity. cbn [Z.ltb Z.eqb Z.leb].
rewrite (bind_IRet (massert true 4) _ s tt s) by reflexivity.
unfold setm, setslot, modify, bind, ret. cbn [ibind]. unfold upd_meta.
rewrite ?Z.mul_0_r, ?Z.sub_0_r, ?Z.sub_diag, ?padd_0. cbn [Z.leb Z.mul Z.add]. rewrite ?Z.add_0_r. reflexivity.
Qed.
Definition nest_st (sc : Z) (m : sptr) (cnt0 : Z) (g : sptr) (am : ameta) (idx j : Z) (s : astate) : astate :=
instn_st sc m cnt0 (slot_start am idx) (upd_meta g (MUsed (am_enf am idx j)) s).
Lemma nest_rest_eq : forall sc m cnt0 j idx s g am,
active_hd s j = Some g -> MT s g = Some (MUsed am) -> stride_of am = class_size j ->
0 <= idx <= am_last am -> active_hd s sc = None ->
nest_rest sc m cnt0 j idx s = IRet (Some m, nest_st sc m cnt0 g am idx j s).
Proof.
intros sc m cnt0 j idx s g am Hhd Hg Hstr Hidx Hsc. unfold nest_rest.
rewrite (bind_IRet (get_head (HActive j)) _ s (Some g) s) by (unfold get_head, bind, get, ret; cbn [ibind]; unfold active_hd in Hhd; rewrite Hhd; reflexivity).
rewrite (bind_IRet (getm g) _ s am s (getm_eval s g am Hg)).
rewrite (bind_IRet (mcheck _ 11) _ s tt s) by (unfold mcheck; rewrite Hstr, Z.eqb_refl; reflexivity).
rewrite (bind_IRet get _ s s s) by reflexivity.
rewrite <- Hstr.
rewrite (bind_IRet (enframe g idx (stride_of am - IB) (st_mmap_counter s) FGroup) _ s _ _ (enframe_eval0 s g am idx (st_mmap_counter s) Hg Hidx)).
set (s2 := upd_meta g (MUsed (upd_slot am idx (mkSlot (Some (idx + 192, stride_of am * idx / UNIT)) (Some (mkFrame 0 (stride_of am - IB) FGroup))))) s).
assert (Hsc2 : active_hd s2 sc = None) by (unfold active_hd in *; cbn; exact Hsc).
rewrite (bind_IRet (install_group m sc cnt0 (cnt0 - 1) 0 (slot_start am idx) slot_junk) _ s2 tt _ (install_nest_eq sc m cnt0 (slot_start am idx) s2 Hsc2)).
unfold ret, nest_st, am_enf. subst s2. rewrite Hstr. reflexivity.
Qed.
End a.
