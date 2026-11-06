(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_reply/lib/A/YGcfRehidePost.v, with its module paths changed; 176 of its 322 lines of code are new or changed and 19 lines of the source are left out. *)
(* CARRIED from commit fa123bc2baab5eec7dd2568431a33b03bf9325d2,
   proofs/cgif/cgif_file_fuzzer/lib/YGcfRehidePost.v, sha256 628cbbe8b0a25731af0fde5b3edede0dd2aed9b10b09cc35dc277d4f6f6d1452 (donor version not released; internal record).
   DO NOT EDIT in this tree: change it on that branch and carry it again. The changes made here are in the Require lines only:
   the module prefix cgif_file_fuzzer.lib -> fuzz_reply.lib.Reusable, except ImgBaseDG / DMspec / AllocG / DeallocG and the
   F1 core's YGcfRehidePost / YGcfRecStep, which name this image's lib/A files (so this file lives in lib/A); a sentence
   is split at a directory change, the module order kept. *)
(* The per-call posts under the re-hide step (group T of the re-hide design, revision 1). A call that recycles a
   secondary hides the dead shadow hull's interior, so two conjuncts of the released posts no longer hold as stated:
   `wle W W'` (the hidden set grows) and the view frame (a re-hidden address changes its view). The twins here state
   instead: the hidden set grows only inside dead_shadow_new ly S S', the EXACT set THIS CALL may hide (the slots live at
   entry and dead at exit), and the frame holds outside it. Every other conjunct is unchanged, and a path that re-hides
   nothing proves the twin from the released post by weakening (acall_post_cf_rh_of / acall_post_x_rh_of). A caller's
   frame facts survive because the set misses every frame live at entry (dead_shadow_new_off). *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK11 YK0s YK0i YK15 YK0j YK18 YP09.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK04 YA0i YA0n YA0nH.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05 YGcfNames YG01cf YG00cf YG0ncf YG0dcf.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YGcfCallRhG.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import ImgBase.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import ImgBaseDG DMspec.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YA0o YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import AllocG DeallocG.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.

(* The madvised interior of a dead slot's shadow hull: page-up of its start, page-down of its end (the recycle's
   PBr / PEr). A real secondary only: an errbuf control entry is also sm_live = false, but it has no map (its size
   entry has no address and its length changes in place), so it must not enter this set. The filter is sm_size >= 0,
   the same one the layer's slot count uses; replace it by that shared definition when it lands. *)
Definition sec_real (sm : secmap) : Prop := 0 <= sm_size sm.
Definition rh_lo (lo : Z) : Z := (shadow_addr lo + 4095) / 4096 * 4096.
Definition rh_hi (lo len : Z) : Z := (shadow_addr lo + len / 8) / 4096 * 4096.

Section g. Context {rc : YM05.RunCeil}.
(* A slot that is dead, real, and placed in the application's address space. *)
Definition dead_sec (ly : alayout) (S : astate) (r : nat) (sm : secmap) : Prop :=
  nth_error (st_secs S) r = Some sm /\ sm_live sm = false /\ sec_real sm /\
  in_app (ly_sec ly r) (sm_len sm) /\ 0 <= sm_len sm.

(* The exact set a recycle may hide: the madvised interiors of the dead real slots' shadow hulls. *)
Definition dead_shadow (ly : alayout) (S : astate) (a : Z) : Prop :=
  exists r sm, dead_sec ly S r sm /\ rh_lo (ly_sec ly r) <= a < rh_hi (ly_sec ly r) (sm_len sm).

(* It only grows: a real slot never becomes live again, and its length never changes. The premise speaks of real dead
   slots only, so an errbuf append (which rewrites its own control entry in place) cannot break it. *)
Lemma dead_shadow_mono : forall ly S S',
  (forall r sm, dead_sec ly S r sm ->
     exists sm', nth_error (st_secs S') r = Some sm' /\ sm_live sm' = false /\ sec_real sm' /\ sm_len sm' = sm_len sm) ->
  forall a, dead_shadow ly S a -> dead_shadow ly S' a.
Proof.
  intros ly S S' HK a (r & sm & Hd & Hr). destruct (HK r sm Hd) as (sm' & Hn' & Hl' & Hs' & He).
  destruct Hd as (_ & _ & _ & Hia & Hl0).
  exists r, sm'. split; [|rewrite He; exact Hr].
  split; [exact Hn'|]. split; [exact Hl'|]. split; [exact Hs'|]. rewrite He. split; [exact Hia | exact Hl0].
Qed.

(* The set ONE CALL may hide: the madvised interiors of the slots LIVE at the call's entry state S and dead at its exit
   S', keyed by slot INDEX (the slot's own st_secs entry is live at S with the same length). Not dead_shadow: a slot
   dead long ago may have had its range re-used by a later map (the kernel may return an unmapped range again), so the
   shadow of a live frame can lie inside an old dead slot's interior; and not keyed by extent value either, since a
   later slot mapped at an old dead slot's address and length would put the old slot's interior in the set. The text
   is preset's (K0, F6DeadShadowNull.v dead_shadow_new_ix). Where every live slot's extent is placed at S
   (live_slots_placed, from the allocator invariant), its interior misses every frame live at S (dead_shadow_new_off). *)
Definition dead_shadow_new (ly : alayout) (S S' : astate) (a : Z) : Prop :=
  exists r sm sm0, dead_sec ly S' r sm /\ nth_error (st_secs S) r = Some sm0 /\ sm_live sm0 = true /\
    sm_len sm0 = sm_len sm /\ rh_lo (ly_sec ly r) <= a < rh_hi (ly_sec ly r) (sm_len sm).

Lemma dead_shadow_new_sub : forall ly S S' a, dead_shadow_new ly S S' a -> dead_shadow ly S' a.
Proof. intros ly S S' a (r & sm & sm0 & Hd & _ & _ & _ & Hr). exists r, sm. split; [exact Hd | exact Hr]. Qed.

(* A call that leaves st_secs alone (the NULL free) has the empty set (K0, F6DeadShadowNull.v). *)
Lemma dead_shadow_new_same_secs_empty : forall ly S S' a, st_secs S' = st_secs S -> ~ dead_shadow_new ly S S' a.
Proof.
  intros ly S S' a E (r & sm & sm0 & (Hn & Hl & _) & Hn0 & Hl0 & _). rewrite E in Hn. rewrite Hn in Hn0.
  injection Hn0 as <-. rewrite Hl in Hl0. discriminate.
Qed.

(* Every live slot's extent is a secondary extent at S. The allocator invariant gives it (wf_sec + chunk_ok). *)
Definition live_slots_placed (ly : alayout) (S : astate) : Prop :=
  forall r sm0, nth_error (st_secs S) r = Some sm0 -> sm_live sm0 = true -> In (ly_sec ly r, sm_len sm0) (sec_extents ly S).

Lemma live_slots_placed_of_wf : forall ly S, wf_sec S -> Forall (chunk_ok S) (st_chunks S) -> live_slots_placed ly S.
Proof.
  intros ly S WS CK r sm0 Hn Hl.
  assert (Hr : In r (st_sec_arr S)) by (apply (proj2 (ws_arr_live _ WS r)); exists sm0; split; assumption).
  destruct (proj1 (ws_arr_chunks _ WS r) Hr) as (k & Hk & Hb).
  pose proof (proj1 (Forall_forall _ _) CK k Hk) as Hok. unfold chunk_ok in Hok. rewrite Hb in Hok.
  destruct Hok as (_ & _ & _ & sm1 & Hn1 & _ & _ & Hs1). rewrite Hn in Hn1. injection Hn1 as <-.
  unfold sec_extents. apply in_flat_map. exists k. split; [exact Hk|]. rewrite Hb. left. rewrite Hs1. reflexivity.
Qed.

(* The same from the cf layer's invariant (wf_sec_cf + chunk_ok_cf, YG01cf.v:73-81, :110-119). *)
Lemma live_slots_placed_of_wf_cf {cp : CfParams} : forall ly S,
  wf_sec_cf S -> Forall (chunk_ok_cf S) (st_chunks S) -> live_slots_placed ly S.
Proof.
  intros ly S WS CK r sm0 Hn Hl.
  assert (Hr : In r (st_sec_arr S)) by (apply (proj2 (wsc_arr_live _ WS r)); exists sm0; split; assumption).
  destruct (proj1 (wsc_arr_chunks _ WS r) Hr) as (k & Hk & Hb).
  pose proof (proj1 (Forall_forall _ _) CK k Hk) as Hok. unfold chunk_ok_cf in Hok. rewrite Hb in Hok.
  destruct Hok as (_ & _ & _ & sm1 & Hn1 & _ & _ & Hs1). rewrite Hn in Hn1. injection Hn1 as <-.
  unfold sec_extents. apply in_flat_map. exists k. split; [exact Hk|]. rewrite Hb. left. rewrite Hs1. reflexivity.
Qed.

Lemma pairwise_In_rh {X : Type} (R : X -> X -> Prop) : forall (l : list X) x y,
  pairwise R l -> In x l -> In y l -> x = y \/ R x y \/ R y x.
Proof.
  intros l. induction l as [|z l IH]; intros x y P Hx Hy; [destruct Hx|]. cbn in P. destruct P as [F P].
  destruct Hx as [<-|Hx], Hy as [<-|Hy];
    [left; reflexivity | right; left; exact (proj1 (Forall_forall _ _) F y Hy)
    | right; right; exact (proj1 (Forall_forall _ _) F x Hx) | exact (IH x y P Hx Hy)].
Qed.

(* THE vacuity fact a caller's frame clause uses: the shadow of any byte of an extent placed at S, other than the dead
   slot's own, lies outside the set. This covers the static extents (the fake stack ly_F among them) and every other
   live secondary map at S. The dead slot was live at S, so its extent is placed at S (live_slots_placed): it is page
   aligned, and its interior is rounded inward. *)
Lemma dead_shadow_new_off : forall ly S S' e x,
  sec_placed ly S -> live_slots_placed ly S -> In e (sec_extents ly S ++ static_extents ly) -> 0 <= snd e ->
  fst e <= x < fst e + snd e ->
  (forall r sm, dead_sec ly S' r sm -> In (ly_sec ly r, sm_len sm) (sec_extents ly S) -> e <> (ly_sec ly r, sm_len sm)) ->
  ~ dead_shadow_new ly S S' (shadow_addr x).
Proof.
  intros ly S S' e x [HA HP] LP He Hl Hx Hne (r & sm & sm0 & Hd & Hn0 & Hl0 & Hlen & Hr).
  assert (Hin : In (ly_sec ly r, sm_len sm) (sec_extents ly S)) by (rewrite <- Hlen; exact (LP r sm0 Hn0 Hl0)).
  pose proof (Hne r sm Hd Hin) as Ne.
  pose proof (proj1 (Forall_forall _ _) HA _ Hin) as (Hal & _ & _). cbn [fst] in Hal. unfold page_aligned in Hal.
  destruct Hd as (_ & _ & _ & _ & Hl0').
  assert (Hin' : In (ly_sec ly r, sm_len sm) (sec_extents ly S ++ static_extents ly)) by (apply in_or_app; left; exact Hin).
  destruct (pairwise_In_rh zdisjoint _ e _ HP He Hin') as [Eq | [Z | Z]]; [exact (Ne Eq)| |];
    unfold zdisjoint in Z; cbn [fst snd] in Z; unfold rh_lo, rh_hi, shadow_addr in Hr |- *;
    set (lo := ly_sec ly r) in *; set (len := sm_len sm) in *.
  - (* e lies below the dead map: x < lo, and lo is 8-aligned, so x / 8 < lo / 8 <= rh_lo lo - SHADOW_OFF. *)
    pose proof (Z.div_mod lo 8 ltac:(lia)) as Dl. pose proof (Z.mod_pos_bound lo 8 ltac:(lia)).
    assert (Hl8 : lo mod 8 = 0).
    { pose proof (Z.div_mod lo 4096 ltac:(lia)). rewrite Hal in *. apply Z.mod_divide; [lia|]. exists (lo / 4096 * 512). lia. }
    pose proof (Z.div_mod x 8 ltac:(lia)). pose proof (Z.mod_pos_bound x 8 ltac:(lia)).
    pose proof (Z.div_mod (SHADOW_OFF + lo / 8 + 4095) 4096 ltac:(lia)).
    pose proof (Z.mod_pos_bound (SHADOW_OFF + lo / 8 + 4095) 4096 ltac:(lia)). lia.
  - (* e lies above: lo + len <= x, so x / 8 >= lo / 8 + len / 8 >= rh_hi lo len - SHADOW_OFF. *)
    assert (lo / 8 + len / 8 <= (lo + len) / 8).
    { pose proof (Z.div_mod lo 8 ltac:(lia)). pose proof (Z.mod_pos_bound lo 8 ltac:(lia)).
      pose proof (Z.div_mod len 8 ltac:(lia)). pose proof (Z.mod_pos_bound len 8 ltac:(lia)).
      pose proof (Z.div_mod (lo + len) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (lo + len) 8 ltac:(lia)). lia. }
    assert ((lo + len) / 8 <= x / 8) by (apply Z.div_le_mono; lia).
    pose proof (Z.div_mod (SHADOW_OFF + lo / 8 + len / 8) 4096 ltac:(lia)).
    pose proof (Z.mod_pos_bound (SHADOW_OFF + lo / 8 + len / 8) 4096 ltac:(lia)). lia.
Qed.

(* The fixed re-hideable zone: the shadow of the application's address space, low and high (LPS admits a low
   placement, and the walk's zone3 covers both). It does not depend on the state, which keeps the composition
   relation (YA0nH.wle') transitive. *)
Definition RZ_cf (a : Z) : Prop :=
  (shadow_addr 4096 - 4096 < a < shadow_addr kLowShadowBeg + 4096) \/
  (shadow_addr kHighMemBeg - 4096 < a < shadow_addr ASAN_CEIL + 4096).

Lemma shadow_addr_mono : forall x y, x <= y -> shadow_addr x <= shadow_addr y.
Proof. intros x y H. unfold shadow_addr. apply Z.add_le_mono_l. apply Z.div_le_mono; lia. Qed.

(* The interior of ANY in_app extent's shadow hull lies in the zone. This is the form a recycle arm applies: with
   lo := MAP and len := LEN it discharges the step's zone premise from the cut's zone3 fact alone, since rh_lo / rh_hi
   are the walk's PBv / PEv. *)
Lemma rh_interior_RZ : forall lo len a,
  in_app lo len -> 0 <= len -> rh_lo lo <= a < rh_hi lo len -> RZ_cf a.
Proof.
  intros lo len a Hia Hl0 Hr.
  destruct Hia as [Hlo4 Hcase]. revert Hr. unfold RZ_cf, rh_lo, rh_hi, shadow_addr.
  pose proof (Z.div_mod lo 8 ltac:(lia)) as Dl. pose proof (Z.mod_pos_bound lo 8 ltac:(lia)) as Ml.
  pose proof (Z.div_mod len 8 ltac:(lia)) as Dn. pose proof (Z.mod_pos_bound len 8 ltac:(lia)) as Mn.
  pose proof (Z.div_mod (lo + len) 8 ltac:(lia)) as Ds. pose proof (Z.mod_pos_bound (lo + len) 8 ltac:(lia)) as Ms.
  set (x := SHADOW_OFF + lo / 8) in *.
  pose proof (Z.div_mod (x + 4095) 4096 ltac:(lia)) as D1. pose proof (Z.mod_pos_bound (x + 4095) 4096 ltac:(lia)) as B1.
  pose proof (Z.div_mod (x + len / 8) 4096 ltac:(lia)) as D2. pose proof (Z.mod_pos_bound (x + len / 8) 4096 ltac:(lia)) as B2.
  assert (H4 : 4096 / 8 <= lo / 8) by (apply Z.div_le_mono; lia).
  destruct Hcase as [Hhi | [Hhlo Hhi]].
  - assert (Hc : (lo + len) / 8 <= kLowShadowBeg / 8) by (apply Z.div_le_mono; lia).
    pose proof (Z.div_mod kLowShadowBeg 8 ltac:(lia)). pose proof (Z.mod_pos_bound kLowShadowBeg 8 ltac:(lia)).
    pose proof (Z.div_mod 4096 8 ltac:(lia)). intros Hr. left. lia.
  - assert (Hd : kHighMemBeg / 8 <= lo / 8) by (apply Z.div_le_mono; lia).
    assert (Hc : (lo + len) / 8 <= ASAN_CEIL / 8) by (apply Z.div_le_mono; lia).
    pose proof (Z.div_mod kHighMemBeg 8 ltac:(lia)). pose proof (Z.mod_pos_bound kHighMemBeg 8 ltac:(lia)).
    pose proof (Z.div_mod ASAN_CEIL 8 ltac:(lia)). pose proof (Z.mod_pos_bound ASAN_CEIL 8 ltac:(lia)).
    intros Hr. right. lia.
Qed.

(* Every dead real slot's interior lies in the zone, from its in_app placement alone. *)
Lemma dead_shadow_RZ : forall ly S a, dead_shadow ly S a -> RZ_cf a.
Proof.
  intros ly S a (r & sm & (_ & _ & _ & Hia & Hl0) & Hr).
  exact (rh_interior_RZ (ly_sec ly r) (sm_len sm) a Hia Hl0 Hr).
Qed.

(* The per-call set lies in the fixed zone too, so a caller composes successive calls inside RZ_cf. *)
Lemma dead_shadow_new_RZ : forall ly S S' a, dead_shadow_new ly S S' a -> RZ_cf a.
Proof. intros ly S S' a H. exact (dead_shadow_RZ ly S' a (dead_shadow_new_sub ly S S' a H)). Qed.

(* An application address is never in the set: the set is shadow of an in_app slot, which lies above the low
   application range and below the high one. *)
Lemma dead_shadow_new_app : forall ly S S' a, app_addr a -> ~ dead_shadow_new ly S S' a.
Proof.
  intros ly S S' a [HA0 HA] (r & sm & sm0 & (_ & _ & _ & Hia & Hl0) & _ & _ & _ & Hr).
  unfold rh_lo, rh_hi, shadow_addr in Hr. set (lo := ly_sec ly r) in *. set (len := sm_len sm) in *.
  destruct Hia as [I0 I1]. pose proof (proj1 (@ASAN_CEIL_range rc)) as CR.
  assert (D : lo / 8 + len / 8 <= (lo + len) / 8).
  { pose proof (Z.div_mod lo 8 ltac:(lia)). pose proof (Z.mod_pos_bound lo 8 ltac:(lia)).
    pose proof (Z.div_mod len 8 ltac:(lia)). pose proof (Z.mod_pos_bound len 8 ltac:(lia)).
    pose proof (Z.div_mod (lo + len) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (lo + len) 8 ltac:(lia)). lia. }
  assert (L8 : 512 <= lo / 8) by (apply (Z.div_le_lower_bound lo 8 512); lia).
  assert (U8 : (lo + len) / 8 <= 0x7fffff800000 / 8) by (apply Z.div_le_mono; [lia | destruct I1 as [I1|[_ I1]]; unfold kLowShadowBeg in *; lia]).
  pose proof (Z.div_mod (SHADOW_OFF + lo / 8 + 4095) 4096 ltac:(lia)).
  pose proof (Z.mod_pos_bound (SHADOW_OFF + lo / 8 + 4095) 4096 ltac:(lia)).
  pose proof (Z.div_mod (SHADOW_OFF + lo / 8 + len / 8) 4096 ltac:(lia)).
  pose proof (Z.mod_pos_bound (SHADOW_OFF + lo / 8 + len / 8) 4096 ltac:(lia)).
  unfold SHADOW_OFF, kLowShadowBeg, kHighMemBeg in *. destruct HA as [HA|[HA1 HA2]]; lia.
Qed.

(* The zone lies below the allocator's ceiling: its top, shadow_addr ASAN_CEIL + 4096, is about ASAN_CEIL / 8. *)
Lemma RZ_cf_below_ceiling : forall a, RZ_cf a -> a < YM05.alloc_ceiling.
Proof.
  intros a HR. pose proof (proj1 (@ASAN_CEIL_range rc)) as CR. unfold ASAN_CEIL in *.
  assert (D : YM05.alloc_ceiling / 8 <= 0x7fffff800000 / 8) by (apply Z.div_le_mono; lia).
  unfold RZ_cf, shadow_addr, ASAN_CEIL in HR. unfold SHADOW_OFF, kLowShadowBeg, kHighMemBeg in *.
  destruct HR as [HR|HR]; lia.
Qed.

Lemma dead_shadow_new_below_ceiling : forall ly S S' a, dead_shadow_new ly S S' a -> a < YM05.alloc_ceiling.
Proof. intros ly S S' a H. exact (RZ_cf_below_ceiling a (dead_shadow_new_RZ ly S S' a H)). Qed.

(* The set lies above kLowMemEnd = SHADOW_OFF: the slot starts at 4096 or above (in_app), so the page-up of its shadow
   start is at least SHADOW_OFF + 4096 / 8 rounded up to a page. *)
Lemma dead_shadow_new_not_low : forall ly S S' a, dead_shadow_new ly S S' a -> kLowMemEnd < a.
Proof.
intros ly S S' a (r & sm & sm0 & (_ & _ & _ & Hia & _) & _ & _ & _ & [Ha _]). destruct Hia as [Hlo _].
unfold rh_lo, shadow_addr in Ha.
assert (H8 : 4096 / 8 <= ly_sec ly r / 8) by (apply Z.div_le_mono; lia). change (4096 / 8) with 512 in H8.
pose proof (Z.div_mod (SHADOW_OFF + ly_sec ly r / 8 + 4095) 4096 ltac:(lia)) as D.
pose proof (Z.mod_pos_bound (SHADOW_OFF + ly_sec ly r / 8 + 4095) 4096 ltac:(lia)) as M.
(* the quotients as atoms: lia then needs no division law *)
set (y := ly_sec ly r / 8) in *. set (q := (SHADOW_OFF + y + 4095) / 4096) in *.
set (m := (SHADOW_OFF + y + 4095) mod 4096) in *. clearbody q m y.
unfold SHADOW_OFF, kLowMemEnd in *. lia.
Qed.

(* The set misses the high application range: the zone's high arm ends at about ASAN_CEIL / 8, far below kHighMemBeg.
   This covers a stack above ASAN_CEIL, where app_addr (dead_shadow_new_app) does not hold. *)
Lemma dead_shadow_new_high : forall ly S S' a, kHighMemBeg <= a -> ~ dead_shadow_new ly S S' a.
Proof.
  intros ly S S' a Ha H. pose proof (dead_shadow_new_RZ ly S S' a H) as HR.
  pose proof (proj1 (@ASAN_CEIL_range rc)) as CR. unfold ASAN_CEIL in *.
  assert (D : YM05.alloc_ceiling / 8 <= 0x7fffff800000 / 8) by (apply Z.div_le_mono; lia).
  unfold RZ_cf, shadow_addr, ASAN_CEIL in HR. unfold SHADOW_OFF, kLowShadowBeg, kHighMemBeg in *.
  destruct HR as [HR|HR]; lia.
Qed.

(* The set is monotone in its entry state: a walk may read a call's set at the call state and use it at an earlier
   state at which every slot live at the call state was already live, with the same length. *)
Lemma dead_shadow_new_mono_l : forall ly S1 S2 S' a,
  (forall r sm0, nth_error (st_secs S1) r = Some sm0 -> sm_live sm0 = true ->
     exists sm2, nth_error (st_secs S2) r = Some sm2 /\ sm_live sm2 = true /\ sm_len sm2 = sm_len sm0) ->
  dead_shadow_new ly S1 S' a -> dead_shadow_new ly S2 S' a.
Proof.
  intros ly S1 S2 S' a Hlv (r & sm & sm0 & HD & E0 & L0 & Len & HR). destruct (Hlv r sm0 E0 L0) as (sm2 & E2 & L2 & Len2).
  exists r, sm, sm2. exact (conj HD (conj E2 (conj L2 (conj (eq_trans Len2 Len) HR)))).
Qed.
End g.

(* ---------------------------------------------------------------------------- *)
(* T1. A fact about an address OUTSIDE the set DS moves across any wle_in DS step (the general form the review asks
   for, not only at wrehide): such an address that is visible stays visible, so its view, its presence and any
   hsub-style transfer are unchanged. With DS := RZ_cf this is every harness address, the stack window and the at-main
   window, none of which is shadow of the application ranges. *)
Section T1. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable segs : list Segment.

Lemma wle_in_hsub_off : forall (DS : Z -> Prop) (W W' : world segs) (a : word),
  wle_in segs DS W W' -> ~ DS (bv_unsigned a) -> w_H W' a = true -> w_H W a = true.
Proof. intros DS W W' a H Hn Ha. destruct (H a Ha) as [H1 | H2]; [exact H1 | contradiction]. Qed.

(* The same at an integer address, the form a caller's frame clause states (e.g. with ~ DS a from dead_shadow_new_app). *)
Lemma wle_in_hsub_off_Z : forall (DS : Z -> Prop) (W W' : world segs) (a : Z), 0 <= a < 2 ^ 64 ->
  wle_in segs DS W W' -> ~ DS a -> w_H W' (Z_to_bv 64 a) = true -> w_H W (Z_to_bv 64 a) = true.
Proof.
  intros DS W W' a Hr H Hn Ha. apply (wle_in_hsub_off DS W W' _ H); [|exact Ha].
  assert (E : bv_unsigned (Z_to_bv 64 a) = a).
  { rewrite Z_to_bv_unsigned. apply bv_wrap_small. change (bv_modulus 64) with (2 ^ 64). lia. }
  rewrite E. exact Hn.
Qed.

Lemma wle_in_vis_off : forall (DS : Z -> Prop) (W W' : world segs) (a : word),
  wle_in segs DS W W' -> ~ DS (bv_unsigned a) -> w_H W a = false -> w_H W' a = false.
Proof.
  intros DS W W' a H Hn Ha. destruct (w_H W' a) eqn:E; [|reflexivity].
  rewrite (wle_in_hsub_off DS W W' a H Hn E) in Ha. discriminate.
Qed.

Lemma apresent_wle_in_off : forall (DS : Z -> Prop) (W W' : world segs) (m : word -> option byte) (a : Z),
  wle_in segs DS W W' -> ~ DS (bv_unsigned (Z_to_bv 64 a)) -> apresent (w_H W) m a -> apresent (w_H W') m a.
Proof.
  intros DS W W' m a H Hn [Hv Hb]. split; [exact (wle_in_vis_off DS W W' _ H Hn Hv) | exact Hb].
Qed.

Lemma aview_wle_in_off : forall (DS : Z -> Prop) (W W' : world segs) (m : word -> option byte) (a : Z),
  wle_in segs DS W W' -> ~ DS (bv_unsigned (Z_to_bv 64 a)) -> w_H W (Z_to_bv 64 a) = false ->
  aview segs (w_H W') m a = aview segs (w_H W) m a.
Proof.
  intros DS W W' m a H Hn Hv. pose proof (wle_in_vis_off DS W W' _ H Hn Hv) as Hv'.
  unfold aview, mbyte, mrestrict. rewrite Hv, Hv'. reflexivity.
Qed.
End T1.

Section G. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams}.
Section J.
Variable segs : list Segment.
Variable B : asyms.

(* The cf call post under the re-hide (the twin of YG0dcf.acall_post_cf): the generic post YGcfCallRhG.acall_post_cf_rh
   at this core's per-call dead set dead_shadow_new. *)
Definition acall_post_cf_rh (stk : Z) (ly : alayout) (S : astate) (Hp : list Z) (W : world segs) (regs : bvmap 5 word)
  (mem : word -> option byte) (md : Model) (E : Z -> Prop)
  (ly' : alayout) (S' : astate) (W' : world segs) (regs' : bvmap 5 word)
  (mem' : word -> option byte) (md' : Model) : Prop :=
  YGcfCallRhG.acall_post_cf_rh segs B dead_shadow_new stk ly S Hp W regs mem md E ly' S' W' regs' mem' md'.

(* Its text, unfolded: the released post with the two changed conjuncts (reflexivity). *)
Lemma acall_post_cf_rh_unfold : forall stk ly S Hp W regs mem md E ly' S' W' regs' mem' md',
  acall_post_cf_rh stk ly S Hp W regs mem md E ly' S' W' regs' mem' md' =
  (ARcf segs B ly' S' Hp W' mem' md' /\ layout_le (length (st_secs S)) ly ly' /\
   wle_in segs (dead_shadow_new ly S S') W W' /\
   aregs_preserved regs regs' /\ same_io md md' /\
   (forall a, 0 <= a < 2 ^ 64 -> ~ aowned B ly S a -> ~ aowned B ly' S' a -> ~ ascratch B stk regs a -> ~ E a ->
      ~ dead_shadow_new ly S S' a ->
      aview segs (w_H W') mem' a = aview segs (w_H W) mem a) /\
   (forall a, spZ regs - stk <= a < spZ regs -> apresent (w_H W') mem' a)).
Proof. reflexivity. Qed.

(* A path that re-hides nothing proves the twin from the released post. *)
Lemma acall_post_cf_rh_of : forall stk ly S Hp W regs mem md E ly' S' W' regs' mem' md',
  acall_post_cf segs B stk ly S Hp W regs mem md E ly' S' W' regs' mem' md' ->
  acall_post_cf_rh stk ly S Hp W regs mem md E ly' S' W' regs' mem' md'.
Proof. exact (YGcfCallRhG.acall_post_cf_rh_of segs B dead_shadow_new). Qed.
End J.
End G.

(* The image-side call post under the re-hide (the twin of DMspec.acall_post_x), for the drain / recycle specs. *)
Section D. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {IM : AImg} {DI : DImg}.
Variable B : asyms.
Variable ARX : Z -> alayout -> astate -> world im_segs -> (word -> option byte) -> Model -> Prop.
Variable AOX : alayout -> astate -> Z -> Prop.

Definition acall_post_x_rh (inst stk : Z) (ly : alayout) (S : astate) (W : world im_segs) (regs : bvmap 5 word)
  (mem : word -> option byte) (md : Model) (E : Z -> Prop)
  (ly' : alayout) (S' : astate) (W' : world im_segs) (regs' : bvmap 5 word)
  (mem' : word -> option byte) (md' : Model) : Prop :=
  ARX inst ly' S' W' mem' md' /\ layout_le (length (st_secs S)) ly ly' /\
  wle_in im_segs (dead_shadow_new ly S S') W W' /\
  aregs_preserved regs regs' /\ same_io md md' /\
  (forall a, 0 <= a < 2 ^ 64 -> ~ AOX ly S a -> ~ AOX ly' S' a -> ~ ascratch B stk regs a -> ~ E a ->
     ~ dead_shadow_new ly S S' a ->
     aview im_segs (w_H W') mem' a = aview im_segs (w_H W) mem a) /\
  (forall a, spZ regs - stk <= a < spZ regs -> apresent (w_H W') mem' a).

Lemma acall_post_x_rh_of : forall inst stk ly S W regs mem md E ly' S' W' regs' mem' md',
  acall_post_x B ARX AOX inst stk ly S W regs mem md E ly' S' W' regs' mem' md' ->
  acall_post_x_rh inst stk ly S W regs mem md E ly' S' W' regs' mem' md'.
Proof.
  intros inst stk ly S W regs mem md E ly' S' W' regs' mem' md' (H1 & H2 & H3 & H4 & H5 & H6 & H7).
  split; [exact H1|]. split; [exact H2|].
  split; [intros a Ha; left; exact (H3 a Ha)|].
  split; [exact H4|]. split; [exact H5|]. split; [|exact H7].
  intros a A1 A2 A3 A4 A5 _. exact (H6 a A1 A2 A3 A4 A5).
Qed.
End D.

(* The cf free path's own posts (the twins of DeallocG.dealloc_post :103 and dealloc_post_raw :127, used through
   dealloc_leaf_raw at YGcfMallocCompose.v:351-362). Same two changes, and the raw-memory frame keeps its released
   shape with no exception, because the RE-HIDE STEP CHANGES NO MEMORY: it rewrites the world's hidden set and
   allowance only. (The madvise before it does zero-fill the raw bytes, YA06.v:170, but on this walk those bytes are
   the dead map's shadow, which already reads 0, so the released frame still holds there.) *)
Section F. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable segs : list Segment.
Variable B : asyms.
Variable ARX : Z -> alayout -> astate -> world segs -> (word -> option byte) -> Model -> Prop.
Variable AOX : alayout -> astate -> Z -> Prop.

Definition dealloc_post_rh (inst : Z) (ly : alayout) (S : astate) (W : world segs) (regs : bvmap 5 word)
  (mem : word -> option byte) (md : Model) (E : Z -> Prop)
  (ly' : alayout) (S' : astate) (W' : world segs) (regs' : bvmap 5 word)
  (mem' : word -> option byte) (md' : Model) : Prop :=
  ARX inst ly' S' W' mem' md' /\ layout_le (length (st_secs S)) ly ly' /\
  wle_in segs (dead_shadow_new ly S S') W W' /\
  aregs_preserved regs regs' /\ same_io md md' /\
  (forall a, 0 <= a < 2 ^ 64 -> ~ AOX ly S a -> ~ AOX ly' S' a -> ~ ascratch B DFSTACK_G regs a -> ~ E a ->
     ~ dead_shadow_new ly S S' a ->
     aview segs (w_H W') mem' a = aview segs (w_H W) mem a) /\
  (forall a, spZ regs - DFSTACK_G <= a < spZ regs -> apresent (w_H W') mem' a).

Definition dealloc_post_raw_rh (inst : Z) (ly : alayout) (S : astate) (W : world segs) (regs : bvmap 5 word)
  (mem : word -> option byte) (md : Model) (E : Z -> Prop)
  (ly' : alayout) (S' : astate) (W' : world segs) (regs' : bvmap 5 word)
  (mem' : word -> option byte) (md' : Model) : Prop :=
  dealloc_post_rh inst ly S W regs mem md E ly' S' W' regs' mem' md' /\
  (forall x : word, ~ AOX ly S (bv_unsigned x) -> ~ AOX ly' S' (bv_unsigned x) ->
     ~ ascratch B DFSTACK_G regs (bv_unsigned x) -> ~ E (bv_unsigned x) -> mem' x = mem x).

(* A free that re-hides nothing proves the twins from the released posts. *)
Lemma dealloc_post_rh_of : forall inst ly S W regs mem md E ly' S' W' regs' mem' md',
  DeallocG.dealloc_post segs B ARX AOX inst ly S W regs mem md E ly' S' W' regs' mem' md' ->
  dealloc_post_rh inst ly S W regs mem md E ly' S' W' regs' mem' md'.
Proof.
  intros inst ly S W regs mem md E ly' S' W' regs' mem' md' (H1 & H2 & H3 & H4 & H5 & H6 & H7).
  split; [exact H1|]. split; [exact H2|].
  split; [intros a Ha; left; exact (H3 a Ha)|].
  split; [exact H4|]. split; [exact H5|]. split; [|exact H7].
  intros a A1 A2 A3 A4 A5 _. exact (H6 a A1 A2 A3 A4 A5).
Qed.

Lemma dealloc_post_raw_rh_of : forall inst ly S W regs mem md E ly' S' W' regs' mem' md',
  DeallocG.dealloc_post_raw segs B ARX AOX inst ly S W regs mem md E ly' S' W' regs' mem' md' ->
  dealloc_post_raw_rh inst ly S W regs mem md E ly' S' W' regs' mem' md'.
Proof.
  intros inst ly S W regs mem md E ly' S' W' regs' mem' md' (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8).
  split; [|exact H7].
  split; [exact H1|]. split; [exact H2|].
  split; [intros a Ha; left; exact (H3 a Ha)|].
  split; [exact H4|]. split; [exact H5|]. split; [|exact H8].
  intros a A1 A2 A3 A4 A5 _. exact (H6 a A1 A2 A3 A4 A5).
Qed.
End F.

