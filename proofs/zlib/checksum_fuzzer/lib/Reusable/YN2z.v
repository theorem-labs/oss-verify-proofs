(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool Lia.
From Stdlib Require Import Logic.FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YK11 YK0s YK0i YK15 YM06 YM02.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import
YO0i YO0f YO0g YO0w YO0s YO14 YO0y YO0d.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YN2f YN2k.
From Stdlib Require Import List.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Open Scope Z_scope.
Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Definition msc (A : astate) (n : Z) : Z :=
let sc0 := size_to_class n in
let g0 := nth (Z.to_nat sc0) (st_active A) None in
if (osptr_eqb g0 None) && (4 <=? sc0) && (sc0 <? 32) && negb (sc0 =? 6)
&& Z.even sc0 && (usage_of A sc0 =? 0)
then
let u := usage_of A (sc0 + 1) in
let head_full :=
match nth (Z.to_nat (sc0 + 1)) (st_active A) None with
| None => true
| Some h => match mlookup (st_metas A) h with
| Some (MUsed am) => (am_avail am =? 0) && (am_freed am =? 0)
| _ => true
end
end in
let u := if head_full then u + 3 else u in
if u <=? 12 then sc0 + 1 else sc0
else sc0.
Definition slow_k (n sc : Z) (r : Z * astate) : itree astate (option sptr * astate) :=
let '(idx, s2) := r in
if idx <? 0 then IRet (None, s2)
else match active_hd s2 sc with
| Some gm => ibind (enframe gm idx n (st_mmap_counter s2) FUser s2) (fun ps => IRet (Some (fst ps), snd ps))
| None => IFail (FModel 9)
end.
Definition am_take (am : ameta) : ameta := am_set_avail (am_avail am - lowbit (am_avail am)) am.
End a.
Local Open Scope mm_scope.
Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Definition malloc_small_body (n sc : Z) : M (option sptr) :=
s <- get ;;
let g := nth (Z.to_nat sc) (st_active s) None in
r <- (match g with
| None => ret None
| Some gm =>
am <- getm gm ;;
if am_avail am =? 0 then ret None
else let first := lowbit (am_avail am) in
setm gm (am_set_avail (am_avail am - first) am) ;;
ret (Some (gm, ctz32 first))
end) ;;
gi <- (match r with
| Some gi => ret (Some gi)
| None =>
idx <- alloc_slot NEST_FUEL sc n ;;
if idx <? 0 then ret None
else hd <- get_head (HActive sc) ;;
match hd with
| Some gm => ret (Some (gm, idx))
| None => fail (FModel 9)
end
end) ;;
match gi with
| None => ret None
| Some (gm, idx) =>
s <- get ;;
p <- enframe gm idx n (st_mmap_counter s) FUser ;;
ret (Some p)
end.
End b.
Local Close Scope mm_scope.
Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Lemma malloc_small_unfold n A :
size_overflows n = false -> n < MMAP_THRESHOLD ->
malloc n A = malloc_small_body n (msc A n) A.
Proof.
intros Hov Hth. unfold malloc. rewrite Hov.
replace (MMAP_THRESHOLD <=? n) with false by (symmetry; apply Z.leb_gt; lia).
reflexivity.
Qed.
Lemma malloc_small_body_shape n sc A :
malloc_small_body n sc A =
match active_hd A sc with
| Some gm =>
match MT A gm with
| Some (MUsed am) =>
if am_avail am =? 0 then ibind (alloc_slot NEST_FUEL sc n A) (slow_k n sc)
else ibind (enframe gm (ctz32 (lowbit (am_avail am))) n (st_mmap_counter (upd_meta gm (MUsed (am_take am)) A)) FUser
(upd_meta gm (MUsed (am_take am)) A))
(fun ps => IRet (Some (fst ps), snd ps))
| _ => IFail (FModel 1)
end
| None => ibind (alloc_slot NEST_FUEL sc n A) (slow_k n sc)
end.
Proof.
unfold malloc_small_body, bind, get, getm, setm, modify, ret. unfold bind, get. cbn [ibind].
change (nth (Z.to_nat sc) (st_active A) None) with (active_hd A sc).
assert (K : forall t : itree astate (Z * astate),
ibind (ibind t (fun '(a0, s'0) =>
(if a0 <? 0 then fun s0 : astate => IRet (@None (sptr * Z), s0)
else fun s0 : astate => ibind (get_head (HActive sc) s0)
(fun '(a1, s'1) => match a1 with
| Some gm => fun s1 : astate => IRet (Some (gm, a0), s1)
| None => fail (FModel 9) end s'1)) s'0))
(fun '(a0, s'0) => match a0 with
| Some (gm, idx) => fun s : astate => ibind (enframe gm idx n (st_mmap_counter s) FUser s) (fun '(a1, s'1) => IRet (Some a1, s'1))
| None => fun s : astate => IRet (None, s) end s'0)
= ibind t (slow_k n sc)).
{ intros t. rewrite ibind_assoc. apply ibind_ext. intros [idx s2]. cbn [ibind]. unfold slow_k.
destruct (idx <? 0); cbn [ibind]; [reflexivity|].
unfold get_head, bind, get, ret, fail. cbn [ibind].
change (nth (Z.to_nat sc) (st_active s2) None) with (active_hd s2 sc).
destruct (active_hd s2 sc) as [gm|]; cbn [ibind]; [|reflexivity].
f_equal. apply functional_extensionality. intros [p s']. reflexivity. }
destruct (active_hd A sc) as [gm|]; cbn [ibind].
- change (mlookup (st_metas A) gm) with (MT A gm).
destruct (MT A gm) as [[pv nx| |am]|]; cbn [ibind]; try reflexivity.
destruct (am_avail am =? 0); cbn [ibind].
+ exact (K (alloc_slot NEST_FUEL sc n A)).
+ fold (am_take am).
change (set_metas (mupdate (st_metas A) gm (MUsed (am_take am))) A) with (upd_meta gm (MUsed (am_take am)) A).
f_equal. apply functional_extensionality. intros [p s']. reflexivity.
- exact (K (alloc_slot NEST_FUEL sc n A)).
Qed.
End c.
