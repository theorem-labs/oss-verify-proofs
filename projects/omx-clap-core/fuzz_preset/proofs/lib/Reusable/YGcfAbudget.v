(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10-30: taken by path from proofs/cgif/cgif_file_fuzzer/lib/YGcfAbudget.v at commit fec7cbb6287c (the cf layer of record, field rounds 1 + 2), module paths changed; the preset-side hunks kept on top are listed in the round6f report. *)
(* Modified by Theorem Labs, 2026-10-30: taken by path from proofs/cgif/cgif_file_fuzzer/lib/YGcfAbudget.v at commit d0377850faab (the cf layer of record, field round 3 + the hull round + pf_ial_apart_t), module paths changed; the preset-side hunks kept on top are listed in the round6g report. *)
(* Theorem Labs, 2026-10-30: the cf budget's step lemmas (the ledger restatement, Main's decisions of record
   2026-10-30). ARcf's ledger conjunct is the raw `A_bytes (w_A W) <= abudget_cf S` at every state; abudget_cf
   (YG0ncf.v) counts prim_committed / 8 and the unit's hull term cf_hull (YGcfNames.v: preset sec_hulls_cf, cgif's
   sec_hulls over the user entries; reply after F1 the live hulls + 16384 per recycled secondary). This file adds
   CF_HEAD, the room's head (the room itself, its per-call grant list and its margins are YGcfRoomCf.v's), the
   primary grant equations abudget_grant_fa_cf /
   abudget_grant_user_cf, the budget drop of a secondary recycle (abudget_recycle_cf: the map + at most cf_rec_drop),
   the raw ledger step there (free_ledger_recycle_cf, and its wle form), the two instances' hull laws (section 6),
   and alc_eager_x's keep lemmas at the errbuf exits. No function is proved here (rule 24). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK11 YP09 YK04 YA0i YA0n YK08.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YGcfNames YG01cf YG00cf YG0ncf YK0v YG0j YFfn.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG08.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfCount.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YK0g.
(* stdpp, through the LPS modules, shadows NoDup and Forall_forall; the lemmas here are Stdlib's. *)
From Stdlib Require Import List.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.

(* The room's head (Main 2026-10-30, room choice (a)): the room of record is
   E_BASE + eager_cf ly S md + abudget_kit_cf S + CF_HEAD <= ASAN_VM_LMIN (YGcfRoomCf.v room_rec_cf, the kit's
   allowance form). A NEW cf-only constant:
   cgif's VM_HEAD (YG0n.v:542, 2 ^ 30) is unchanged. It must hold one call's grants (the errbuf remap, at most
   2 * cf_nob; the class-24 user map and its shadow; the free-array growths; any other map), which
   ERRB_ROOM (YG00cf.v:107) does not bound against vm_limit. *)
Definition CF_HEAD : Z := 2 ^ 33.

Lemma CF_HEAD_val : CF_HEAD = 8589934592.
Proof. reflexivity. Qed.

(* ---------------------------------------------------------------------------- *)
(* 1. Sums over lists: one entry removed, one entry replaced.                     *)
Lemma cfa_fold_del {X : Type} (F : X -> Z -> Z) (g : X -> Z) :
(forall x a, F x a = g x + a) ->
forall pre x post, fold_right F 0 (pre ++ x :: post) = fold_right F 0 (pre ++ post) + g x.
Proof.
intros HF pre x post. induction pre as [|y t IH]; cbn [app fold_right].
- rewrite HF. lia.
- rewrite !HF, IH. lia.
Qed.

Lemma cfa_fold_lupd {X : Type} (F : X -> Z -> Z) (g : X -> Z) :
(forall x a, F x a = g x + a) ->
forall l i v x, nth_error l i = Some x -> fold_right F 0 (lupd l i v) = fold_right F 0 l - g x + g v.
Proof.
intros HF l. induction l as [|y t IH]; intros i v x Hn; [destruct i; discriminate Hn|].
destruct i as [|i]; cbn [lupd fold_right nth_error] in *.
- injection Hn as <-. rewrite !HF. lia.
- rewrite !HF, (IH i v x Hn). lia.
Qed.

Lemma cfa_filter_lupd {X : Type} (p : X -> bool) :
forall l i v x, nth_error l i = Some x -> p x = false -> p v = false -> List.filter p (lupd l i v) = List.filter p l.
Proof.
intros l. induction l as [|y t IH]; intros i v x Hn Hx Hv; [destruct i; discriminate Hn|].
destruct i as [|i]; cbn [lupd nth_error] in *.
- injection Hn as <-. cbn [List.filter]. rewrite Hx, Hv. reflexivity.
- cbn [List.filter]. rewrite (IH i v x Hn Hx Hv). reflexivity.
Qed.

Section U. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams}.

(* ---------------------------------------------------------------------------- *)
(* 3. The primary grants (item 3). prim_committed sums rg_mapped_user + rg_mapped_fa over the regions        *)
(*    (YG01.v:218-219); a grant updates one region (set_region, YG00.v:215) by one map of 262144 bytes, so *)
(*    abudget_cf rises by the map and its exact shadow 262144 / 8 = 32768.                                 *)
Lemma prim_fold_lupd : forall (rs : list region) i r0 r',
nth_error rs i = Some r0 ->
fold_right (fun r acc => rg_mapped_user r + rg_mapped_fa r + acc) 0 (lupd rs i r')
= fold_right (fun r acc => rg_mapped_user r + rg_mapped_fa r + acc) 0 rs
- (rg_mapped_user r0 + rg_mapped_fa r0) + (rg_mapped_user r' + rg_mapped_fa r').
Proof.
intros rs i r0 r' Hn.
apply (cfa_fold_lupd (fun r acc => rg_mapped_user r + rg_mapped_fa r + acc) (fun r => rg_mapped_user r + rg_mapped_fa r));
[intros x a; cbv beta; lia | exact Hn].
Qed.

Lemma prim_committed_zupd : forall S S' c r',
st_regions S' = zupd c r' (st_regions S) -> 0 <= c -> (Z.to_nat c < length (st_regions S))%nat ->
prim_committed S' = prim_committed S - (rg_mapped_user (reg S c) + rg_mapped_fa (reg S c))
+ (rg_mapped_user r' + rg_mapped_fa r').
Proof.
intros S S' c r' E Hc Hl. unfold prim_committed, reg, znth. rewrite E. unfold zupd.
apply prim_fold_lupd. apply nth_error_nth'. exact Hl.
Qed.

Lemma prim_committed_grant_fa : forall S S' c r',
st_regions S' = zupd c r' (st_regions S) -> 0 <= c -> (Z.to_nat c < length (st_regions S))%nat ->
rg_mapped_user r' = rg_mapped_user (reg S c) -> rg_mapped_fa r' = rg_mapped_fa (reg S c) + kFreeArrayMapSize ->
prim_committed S' = prim_committed S + kFreeArrayMapSize.
Proof.
intros S S' c r' E Hc Hl HU HF. rewrite (prim_committed_zupd S S' c r' E Hc Hl), HU, HF. lia.
Qed.

Lemma prim_committed_grant_user : forall S S' c r',
st_regions S' = zupd c r' (st_regions S) -> 0 <= c -> (Z.to_nat c < length (st_regions S))%nat ->
rg_mapped_user r' = rg_mapped_user (reg S c) + kUserMapSize -> rg_mapped_fa r' = rg_mapped_fa (reg S c) ->
prim_committed S' = prim_committed S + kUserMapSize.
Proof.
intros S S' c r' E Hc Hl HU HF. rewrite (prim_committed_zupd S S' c r' E Hc Hl), HU, HF. lia.
Qed.

(* One primary map of G = 8 * q bytes: abudget_cf rises by exactly G + G / 8. *)
Lemma abudget_grant_prim_cf : forall S S' q,
prim_committed S' = prim_committed S + 8 * q ->
st_sec_reserved S' = st_sec_reserved S -> st_chunks S' = st_chunks S -> st_secs S' = st_secs S ->
abudget_cf S' = abudget_cf S + 8 * q + q.
Proof.
intros S S' q HP HR HC HS.
assert (E1 : sec_live_bytes S' = sec_live_bytes S) by (unfold sec_live_bytes; rewrite HC; reflexivity).
assert (E2 : cf_hull S' = cf_hull S).
{ apply cf_hull_frame; [exact HS | unfold sec_live_hulls; rewrite HC; reflexivity]. }
assert (E3 : errb_cap_cf S' = errb_cap_cf S) by (unfold errb_cap_cf, errb_e; rewrite HS; reflexivity).
assert (D : (prim_committed S + 8 * q) / 8 = prim_committed S / 8 + q).
{ replace (prim_committed S + 8 * q) with (prim_committed S + q * 8) by lia. apply Z.div_add. lia. }
unfold abudget_cf. rewrite HP, D, E1, E2, E3, HR. lia.
Qed.

(* EnsureFreeArraySpace's growth branch (the KMapFreeArray grant). *)
Lemma abudget_grant_fa_cf : forall S S',
prim_committed S' = prim_committed S + kFreeArrayMapSize ->
st_sec_reserved S' = st_sec_reserved S -> st_chunks S' = st_chunks S -> st_secs S' = st_secs S ->
abudget_cf S' = abudget_cf S + kFreeArrayMapSize + kFreeArrayMapSize / 8.
Proof.
intros S S' HP HR HC HS. unfold kFreeArrayMapSize in *. change (262144 / 8) with 32768.
rewrite (abudget_grant_prim_cf S S' 32768); [lia | lia | exact HR | exact HC | exact HS].
Qed.

(* KMapUser (the class's user map). *)
Lemma abudget_grant_user_cf : forall S S',
prim_committed S' = prim_committed S + kUserMapSize ->
st_sec_reserved S' = st_sec_reserved S -> st_chunks S' = st_chunks S -> st_secs S' = st_secs S ->
abudget_cf S' = abudget_cf S + kUserMapSize + kUserMapSize / 8.
Proof.
intros S S' HP HR HC HS. unfold kUserMapSize in *. change (262144 / 8) with 32768.
rewrite (abudget_grant_prim_cf S S' 32768); [lia | lia | exact HR | exact HC | exact HS].
Qed.

(* A primary grant keeps the layer's ledger form when the world gains at most the map and its shadow. *)
Lemma ledger_grant_prim_cf : forall sg (W W' : world sg) S S' q,
A_bytes (w_A W) <= abudget_cf S -> A_bytes (w_A W') <= A_bytes (w_A W) + 8 * q + q ->
prim_committed S' = prim_committed S + 8 * q ->
st_sec_reserved S' = st_sec_reserved S -> st_chunks S' = st_chunks S -> st_secs S' = st_secs S ->
A_bytes (w_A W') <= abudget_cf S'.
Proof.
intros sg W W' S S' q L HA HP HR HC HS. rewrite (abudget_grant_prim_cf S S' q HP HR HC HS). lia.
Qed.

(* ---------------------------------------------------------------------------- *)
(* 4. The secondary recycle. sec_dealloc (YG00.v:472-487) keeps sm_len and sm_size of entry r and sets      *)
(*    sm_live false; recycle_chunk (:496-500) deletes the chunk. With LEN = sec_map_size (ck_req k): the     *)
(*    chunk leaves sec_live_bytes (- LEN), the hull term drops by at most cf_rec_drop LEN (cf_hull_recycle: *)
(*    0 for preset's sec_hulls_cf, whose slot keeps its sm_len; the re-hidden interior for reply under F1),*)
(*    and errb_cap_cf, prim_committed and st_sec_reserved do not move.                                     *)
Lemma sec_live_bytes_del : forall X X2 pre k post,
st_chunks X = pre ++ k :: post -> st_chunks X2 = pre ++ post ->
sec_live_bytes X = sec_live_bytes X2 + match ck_beg k with PSec _ _ => sec_map_size (ck_req k) | _ => 0 end.
Proof.
intros X X2 pre k post E E2. unfold sec_live_bytes. rewrite E, E2.
apply (cfa_fold_del _ (fun k => match ck_beg k with PSec _ _ => sec_map_size (ck_req k) | _ => 0 end)).
intros x a. cbv beta. destruct (ck_beg x); cbv beta iota; lia.
Qed.

Lemma sec_live_hulls_del : forall X X2 pre k post,
st_chunks X = pre ++ k :: post -> st_chunks X2 = pre ++ post ->
sec_live_hulls X = sec_live_hulls X2
+ match ck_beg k with PSec _ _ => Z.max 0 (sec_map_size (ck_req k) / 8 + 8192) | _ => 0 end.
Proof.
intros X X2 pre k post E E2. unfold sec_live_hulls. rewrite E, E2.
apply (cfa_fold_del _ (fun k => match ck_beg k with PSec _ _ => Z.max 0 (sec_map_size (ck_req k) / 8 + 8192) | _ => 0 end)).
intros x a. cbv beta. destruct (ck_beg x); cbv beta iota; lia.
Qed.

Lemma errb_cap_cf_kill_live : forall X X2 r sm,
nth_error (st_secs X) r = Some sm -> 0 <= sm_size sm ->
st_secs X2 = lupd (st_secs X) r (mkSec (sm_len sm) (sm_size sm) false) ->
errb_cap_cf X2 = errb_cap_cf X.
Proof.
intros X X2 r sm Hn HZ E. unfold errb_cap_cf, errb_e. rewrite E.
assert (NC : is_errb_cap sm = false) by (unfold is_errb_cap, ERRB_CAP_TAG; apply Z.eqb_neq; lia).
rewrite (cfa_filter_lupd is_errb_cap (st_secs X) r _ sm Hn NC); [reflexivity|].
unfold is_errb_cap, ERRB_CAP_TAG. cbn [sm_size]. apply Z.eqb_neq. lia.
Qed.

(* abudget_cf at a recycle: it drops by the map LEN and the hull term's drop, which cf_hull_recycle bounds by
   cf_rec_drop LEN (0 on wle; the re-hidden interior under F1). *)
Lemma abudget_recycle_cf : forall X X2 pre k post r off sm,
st_chunks X = pre ++ k :: post -> st_chunks X2 = pre ++ post -> ck_beg k = PSec r off ->
nth_error (st_secs X) r = Some sm -> sm_live sm = true -> 0 <= sm_size sm -> sm_len sm = sec_map_size (ck_req k) ->
st_secs X2 = lupd (st_secs X) r (mkSec (sm_len sm) (sm_size sm) false) ->
st_regions X2 = st_regions X -> st_sec_reserved X2 = st_sec_reserved X ->
abudget_cf X - sec_map_size (ck_req k) - cf_rec_drop (sm_len sm) <= abudget_cf X2.
Proof.
intros X X2 pre k post r off sm E E2 Hb Hn HL HZ HLen ES ER HR.
pose proof (sec_live_bytes_del X X2 pre k post E E2) as B1. rewrite Hb in B1. cbv beta iota in B1.
pose proof (cf_hull_recycle X X2 pre k post r off sm E E2 Hb Hn HL HZ HLen ES) as B3.
pose proof (errb_cap_cf_kill_live X X2 r sm Hn HZ ES) as B4.
assert (P : prim_committed X2 = prim_committed X) by (unfold prim_committed; rewrite ER; reflexivity).
unfold abudget_cf. rewrite P, B4, HR, B1. lia.
Qed.

Section L.
Variable ly : alayout.

Lemma sec_extent_in_cf : forall X k r off,
In k (st_chunks X) -> ck_beg k = PSec r off -> In (ly_sec ly r, sec_map_size (ck_req k)) (sec_extents ly X).
Proof.
intros X k r off Hk Hb. unfold sec_extents. apply in_flat_map. exists k. split; [exact Hk|].
cbv beta. rewrite Hb. cbv iota. apply in_eq.
Qed.

(* The recycle keeps the RAW ledger: abudget_cf drops by at most LEN + cf_rec_drop LEN (abudget_recycle_cf), so a world
   post that drops by at least that much keeps it: the ledger step at the recycle's post (YGcfInstRcSec.v
   rc_sec_step_sl_cf). *)
Lemma free_ledger_recycle_cf : forall sg (W W2 : world sg) X X2 pre k post r off sm,
A_bytes (w_A W) <= abudget_cf X ->
A_bytes (w_A W2) + sec_map_size (ck_req k) + cf_rec_drop (sm_len sm) <= A_bytes (w_A W) ->
st_chunks X = pre ++ k :: post -> st_chunks X2 = pre ++ post -> ck_beg k = PSec r off ->
nth_error (st_secs X) r = Some sm -> sm_live sm = true -> 0 <= sm_size sm -> sm_len sm = sec_map_size (ck_req k) ->
st_secs X2 = lupd (st_secs X) r (mkSec (sm_len sm) (sm_size sm) false) ->
st_regions X2 = st_regions X -> st_sec_reserved X2 = st_sec_reserved X ->
A_bytes (w_A W2) <= abudget_cf X2.
Proof.
intros sg W W2 X X2 pre k post r off sm L DW E E2 Hb Hn HL HZ HLen ES ER HR.
pose proof (abudget_recycle_cf X X2 pre k post r off sm E E2 Hb Hn HL HZ HLen ES ER HR). lia.
Qed.

(* On wle (the world refunds only the map, wrefund, YFg8.v:76-77): the post world drops by at least LEN
   (A_bytes_refund, YFfn.v:137), which is enough when the unit's cf_rec_drop is 0 there (preset). *)
Lemma free_ledger_recycle_wle_cf : forall sg (W : world sg) X X2 pre k post r off sm,
A_bytes (w_A W) <= abudget_cf X -> asecA ly X (w_A W) -> cf_rec_drop (sm_len sm) <= 0 ->
st_chunks X = pre ++ k :: post -> st_chunks X2 = pre ++ post -> ck_beg k = PSec r off ->
nth_error (st_secs X) r = Some sm -> sm_live sm = true -> 0 <= sm_size sm -> sm_len sm = sec_map_size (ck_req k) ->
st_secs X2 = lupd (st_secs X) r (mkSec (sm_len sm) (sm_size sm) false) ->
st_regions X2 = st_regions X -> st_sec_reserved X2 = st_sec_reserved X ->
A_bytes (w_A (wrefund sg W (ly_sec ly r, ly_sec ly r + sec_map_size (ck_req k)))) <= abudget_cf X2.
Proof.
intros sg W X X2 pre k post r off sm L HA H0 E E2 Hb Hn HL HZ HLen ES ER HR.
assert (Hk : In k (st_chunks X)) by (rewrite E; apply in_or_app; right; left; reflexivity).
pose proof (proj1 (HA _ (sec_extent_in_cf X k r off Hk Hb))) as Hin. cbn [fst snd] in Hin.
pose proof (A_bytes_refund _ _ (w_Awf W) Hin) as RF. cbn [fst snd] in RF.
assert (EW : w_A (wrefund sg W (ly_sec ly r, ly_sec ly r + sec_map_size (ck_req k)))
  = A_drop (ly_sec ly r, ly_sec ly r + sec_map_size (ck_req k)) (w_A W)) by reflexivity.
apply (free_ledger_recycle_cf sg W _ X X2 pre k post r off sm L); try assumption.
rewrite EW. lia.
Qed.

(* ---------------------------------------------------------------------------- *)
(* 5. The eager part at the errbuf exits (item 2, form (A)). errb_map_cf (YG00cf.v:120-127) maps the new  *)
(*    buffer and then the walk unmaps the old one (a Theorem Labs lane's RepF4Append order); eager_used moves    *)
(*    by + esec [new] - esec [old] (eager_used_remap, from eager_used_mmap_model / eager_used_munmap,      *)
(*    YG0j.v:103 / :124), and eager_cf by the same two terms (eager_cf_swap), so alc_eager_x is kept       *)
(*    (alc_eager_remap_cf) with ONE premise: the noaccess / lazy coverage is unchanged on the KEPT extents  *)
(*    (sec_extents ++ the new zone), which the walk gives from the old buffer's disjointness from them     *)
(*    (xs_placed_cf); no premise on the old extent's own status. The first map is the case                 *)
(*    errb_zone ly S = [] (esec_nil). errb_append_cf without a remap keeps the maps, errb_zone and          *)
(*    sec_extents (eager_cf_same). The witness at init is ALedger_cf_of_ALedger (YG0ncf.v).                *)
Lemma eager_cf_swap : forall S S' md md' en,
errb_zone ly S' = en -> sec_extents ly S' = sec_extents ly S ->
prim_committed S' = prim_committed S -> st_sec_reserved S' = st_sec_reserved S ->
esec (vm_noaccess (m_vmmaps md')) (m_vm_lazy md') (sec_extents ly S ++ en)
= esec (vm_noaccess (m_vmmaps md)) (m_vm_lazy md) (sec_extents ly S ++ en) ->
eager_cf ly S' md' = eager_cf ly S md - esec (vm_noaccess (m_vmmaps md)) (m_vm_lazy md) (errb_zone ly S)
+ esec (vm_noaccess (m_vmmaps md)) (m_vm_lazy md) en.
Proof.
intros S S' md md' en EZ ES EP ER EC. unfold eager_cf. rewrite EZ, ES, EP, ER, EC, !esec_app. lia.
Qed.

Lemma eager_cf_same : forall S S' md,
errb_zone ly S' = errb_zone ly S -> sec_extents ly S' = sec_extents ly S ->
prim_committed S' = prim_committed S -> st_sec_reserved S' = st_sec_reserved S ->
eager_cf ly S' md = eager_cf ly S md.
Proof. intros S S' md EZ ES EP ER. unfold eager_cf. rewrite EZ, ES, EP, ER. reflexivity. Qed.

Lemma alc_eager_remap_cf : forall S S' md md' en,
eager_used md <= E_BASE + eager_cf ly S md ->
eager_used md' = eager_used md + esec (vm_noaccess (m_vmmaps md)) (m_vm_lazy md) en
- esec (vm_noaccess (m_vmmaps md)) (m_vm_lazy md) (errb_zone ly S) ->
errb_zone ly S' = en -> sec_extents ly S' = sec_extents ly S ->
prim_committed S' = prim_committed S -> st_sec_reserved S' = st_sec_reserved S ->
esec (vm_noaccess (m_vmmaps md')) (m_vm_lazy md') (sec_extents ly S ++ en)
= esec (vm_noaccess (m_vmmaps md)) (m_vm_lazy md) (sec_extents ly S ++ en) ->
eager_used md' <= E_BASE + eager_cf ly S' md'.
Proof.
intros S S' md md' en HE HU EZ ES EP ER EC. rewrite (eager_cf_swap S S' md md' en EZ ES EP ER EC). lia.
Qed.

End L.

(* The remap's two model steps: the new buffer's map, then the old buffer's unmap. *)
Lemma eager_used_remap : forall (a n : word) (e : word * word) md l1 l2,
YK0g.model_ivs_wf md -> bv_unsigned a + bv_unsigned n <= 2 ^ 64 ->
amwf (mmap_model a n md) -> vm_maps (m_vmmaps (mmap_model a n md)) = l1 ++ e :: l2 ->
eager_used (munmap_model (fst e) (snd e) (mmap_model a n md))
= eager_used md + esec (vm_noaccess (m_vmmaps md)) (m_vm_lazy md) [(bv_unsigned a, bv_unsigned n)]
- esec (vm_noaccess (m_vmmaps md)) (m_vm_lazy md) [(bv_unsigned (fst e), bv_unsigned (snd e))].
Proof.
intros a n e md l1 l2 WF Han AW E.
rewrite (proj1 (eager_used_munmap e (mmap_model a n md) l1 l2 AW E)).
rewrite (eager_used_mmap_model a n md WF Han).
reflexivity.
Qed.

(* ---------------------------------------------------------------------------- *)
(* 6. The two instances' hull laws (CfParams's cf_hull_* fields, YGcfNames.v): what each unit's instance proves.  *)
(*    PRESET (on wle): cf_hull := sec_hulls_cf (YG0ncf.v: cgif's sec_hulls over the user entries),               *)
(*    cf_hull_ok := sec_meter_ok_cf, cf_rec_drop := fun _ => 0. REPLY (after F1): cf_hull := reply_hull_cf,       *)
(*    cf_hull_ok := nsec_cf S <= cf_kmax (2 ^ 23 at reply), cf_rec_drop := reply_rec_drop_cf. ONE errbuf filter,  *)
(*    sec_user_cf (YGcfNames.v): the errbuf's control entries (sm_size < 0) stay out of every meter. The count's  *)
(*    lemmas (cfa_fold_app1, user_true / user_false, seg_cons / seg_sum_eq, nsec_cf_alloc / kill / errb,          *)
(*    dead_secs_cf, the index sums cfn_sum / cfn_at / cfn_idx) are YGcfCount.v's.                               *)

Lemma cfa_sum_nonneg : forall (g : secmap -> Z) l, (forall sm, In sm l -> 0 <= g sm) ->
0 <= fold_right (fun sm acc => g sm + acc) 0 l.
Proof.
intros g l. induction l as [|a t IH]; intros H; cbn [fold_right]; [lia|].
pose proof (H a (or_introl eq_refl)). pose proof (IH (fun sm Hs => H sm (or_intror Hs))). lia.
Qed.

(* A summand that does not shrink along an errbuf step and is nonnegative on appended control entries. *)
Lemma seg_sum_le : forall (g : secmap -> Z),
(forall a a', (0 <= sm_size a -> a' = a) -> (sm_size a < 0 -> sm_size a' < 0 /\ sm_len a <= sm_len a') -> g a <= g a') ->
(forall sm, sm_size sm < 0 -> 0 <= sm_len sm -> 0 <= g sm) ->
forall l l', secs_errb_grow l l' ->
fold_right (fun sm acc => g sm + acc) 0 l <= fold_right (fun sm acc => g sm + acc) 0 l'.
Proof.
intros g Hm H0 l. induction l as [|a t IH]; intros l' G.
- destruct G as [_ [_ HA]]. cbn [fold_right]. apply cfa_sum_nonneg. intros sm Hin.
  destruct (In_nth_error l' sm Hin) as [i Hi]. destruct (HA i sm ltac:(cbn; lia) Hi) as [S1 S2]. exact (H0 sm S1 S2).
- destruct (seg_cons a t l' G) as (a' & t' & -> & H1 & H2 & G'). cbn [fold_right].
  pose proof (Hm a a' H1 H2). pose proof (IH t' G'). lia.
Qed.

(* secs_grow's four pointwise conjuncts at the head. *)
Lemma sg_cons : forall a t l', secs_grow (a :: t) l' ->
exists a' t', l' = a' :: t' /\ sm_len a <= sm_len a' /\ (sm_live a = false -> sm_live a' = false) /\
(0 <= sm_size a -> 0 <= sm_size a') /\ (sm_size a < 0 -> sm_size a' < 0) /\ secs_grow t t'.
Proof.
intros a t l' [HL [HP HA]]. destruct l' as [|a' t']; [cbn in HL; exfalso; lia|].
destruct (HP 0%nat a eq_refl) as (x & E & H1 & H2 & H3 & H4). cbn in E. injection E as <-.
exists a', t'. split; [reflexivity|]. split; [exact H1|]. split; [exact H2|]. split; [exact H3|]. split; [exact H4|].
split; [cbn in HL; lia|]. split.
- intros i sm Hn. destruct (HP (S i) sm Hn) as (y & Ey & Y1 & Y2 & Y3 & Y4). exists y. split; [exact Ey|].
  exact (conj Y1 (conj Y2 (conj Y3 Y4))).
- intros i sm' Hi Hn. apply (HA (S i) sm'); [cbn; lia | exact Hn].
Qed.

(* A summand that does not shrink along secs_grow and is nonnegative on appended entries. *)
Lemma sg_sum_le : forall (g : secmap -> Z),
(forall a a', sm_len a <= sm_len a' -> (sm_live a = false -> sm_live a' = false) -> (0 <= sm_size a -> 0 <= sm_size a') ->
  (sm_size a < 0 -> sm_size a' < 0) -> g a <= g a') ->
(forall sm, 0 <= sm_len sm -> 0 <= g sm) ->
forall l l', secs_grow l l' -> fold_right (fun sm acc => g sm + acc) 0 l <= fold_right (fun sm acc => g sm + acc) 0 l'.
Proof.
intros g Hm H0 l. induction l as [|a t IH]; intros l' G.
- destruct G as [_ [_ HA]]. cbn [fold_right]. apply cfa_sum_nonneg. intros sm Hin.
  destruct (In_nth_error l' sm Hin) as [i Hi]. exact (H0 sm (HA i sm ltac:(cbn; lia) Hi)).
- destruct (sg_cons a t l' G) as (a' & t' & -> & H1 & H2 & H3 & H4 & G'). cbn [fold_right].
  pose proof (Hm a a' H1 H2 H3 H4). pose proof (IH t' G'). lia.
Qed.

Lemma sg_nsec_le : forall S S', secs_grow (st_secs S) (st_secs S') -> nsec_cf S <= nsec_cf S'.
Proof.
intros S S' G. unfold nsec_cf. apply (sg_sum_le (fun sm => if sec_user_cf sm then 1 else 0)); [| |exact G].
- intros a a' _ _ H3 _. cbv beta. destruct (Z_le_gt_dec 0 (sm_size a)) as [Hz|Hz].
  + rewrite (user_true a Hz), (user_true a' (H3 Hz)). lia.
  + rewrite (user_false a ltac:(lia)). destruct (sec_user_cf a'); cbv iota; lia.
- intros sm _. cbv beta. destruct (sec_user_cf sm); cbv iota; lia.
Qed.

(* ---- PRESET: sec_hulls_cf (YG0ncf.v). ---- *)
(* cf_hull_init at preset: init_state has no st_secs entry. *)
Lemma preset_hull_init : sec_hulls_cf init_state = 0.
Proof. reflexivity. Qed.

Lemma preset_hull_frame : forall S S', st_secs S' = st_secs S -> sec_hulls_cf S' = sec_hulls_cf S.
Proof. intros S S' E. unfold sec_hulls_cf. rewrite E. reflexivity. Qed.

Lemma preset_hull_alloc : forall S S' L z, 0 <= L -> 0 <= z -> st_secs S' = st_secs S ++ [mkSec L z true] ->
sec_hulls_cf S + Z.max 0 (L / 8 + 8192) <= sec_hulls_cf S'.
Proof.
intros S S' L z HL Hz E. unfold sec_hulls_cf. rewrite E.
rewrite (cfa_fold_app1 (fun sm acc => (if sec_user_cf sm then sm_len sm / 8 + 8192 else 0) + acc)
  (fun sm => if sec_user_cf sm then sm_len sm / 8 + 8192 else 0)) by (intros; reflexivity).
cbv beta. rewrite (user_true (mkSec L z true) Hz). cbn [sm_len]. pose proof (Z.div_pos L 8 HL ltac:(lia)). lia.
Qed.

Lemma preset_hull_errb : forall S S', secs_errb_grow (st_secs S) (st_secs S') -> sec_hulls_cf S <= sec_hulls_cf S'.
Proof.
intros S S' G. unfold sec_hulls_cf. apply Z.eq_le_incl.
apply (seg_sum_eq (fun sm => if sec_user_cf sm then sm_len sm / 8 + 8192 else 0)); [|exact G].
intros sm H. cbv beta. rewrite (user_false sm H). reflexivity.
Qed.

Lemma preset_hull_recycle : forall X X2 r sm, nth_error (st_secs X) r = Some sm ->
st_secs X2 = lupd (st_secs X) r (mkSec (sm_len sm) (sm_size sm) false) -> sec_hulls_cf X - sec_hulls_cf X2 <= 0.
Proof.
intros X X2 r sm Hn E. unfold sec_hulls_cf. rewrite E.
rewrite (cfa_fold_lupd (fun sm acc => (if sec_user_cf sm then sm_len sm / 8 + 8192 else 0) + acc)
  (fun sm => if sec_user_cf sm then sm_len sm / 8 + 8192 else 0) ltac:(intros; reflexivity) (st_secs X) r _ sm Hn).
cbv beta. replace (sec_user_cf (mkSec (sm_len sm) (sm_size sm) false)) with (sec_user_cf sm) by reflexivity.
cbn [sm_len]. lia.
Qed.

(* The admission lemmas below are cp-FREE (no CfParams argument), so the unit records can name them: the meter is
   written out over explicit bounds K and T, `nsec_cf S <= K /\ sec_T_cf S <= T`, which a record instantiates with ONE
   named term per bound for both cf_kmax / cf_T_max and the meter (convertible with sec_meter_ok_cf there). *)

(* The cap (cf_hull_bound): preset's meter bounds sec_hulls_cf whatever the live hulls are, since
   T / 8 + 8192 * K <= 2 ^ 35 + 2 ^ 37 = CF_HULL_MAX under the class caps K <= 2 ^ 24, T <= 2 ^ 38. *)
Lemma preset_hull_bound : forall K T, K <= 2 ^ 24 -> T <= 2 ^ 38 -> forall S, nsec_cf S <= K /\ sec_T_cf S <= T ->
sec_live_hulls S <= 3087007744 -> sec_hulls_cf S <= CF_HULL_MAX.
Proof.
intros K T HK HT S [HN HS] _. pose proof (sec_hulls_le_meter S) as M.
assert (D : sec_T_cf S / 8 <= T / 8) by (apply Z.div_le_mono; lia).
assert (D' : T / 8 <= 2 ^ 35) by (apply Z.div_le_upper_bound; lia).
unfold CF_HULL_MAX. lia.
Qed.

Lemma preset_hull_mono_back : forall K T S S', secs_grow (st_secs S) (st_secs S') ->
nsec_cf S' <= K /\ sec_T_cf S' <= T -> nsec_cf S <= K /\ sec_T_cf S <= T.
Proof.
intros K T S S' G [HN HT]. split.
- pose proof (sg_nsec_le S S' G). lia.
- assert (T' : sec_T_cf S <= sec_T_cf S').
  { unfold sec_T_cf. apply (sg_sum_le (fun sm => if sec_user_cf sm then sm_len sm else 0)); [| |exact G].
    - intros a a' H1 _ H3 H4. cbv beta. destruct (Z_le_gt_dec 0 (sm_size a)) as [Hz|Hz].
      + rewrite (user_true a Hz), (user_true a' (H3 Hz)). cbv iota. exact H1.
      + rewrite (user_false a ltac:(lia)), (user_false a' (H4 ltac:(lia))). cbv iota. lia.
    - intros sm HL. cbv beta. destruct (sec_user_cf sm); cbv iota; lia. }
  lia.
Qed.

(* cf_hull_counts at preset: the meter is the pair of bounds, so equal meters carry it in either direction. *)
Lemma preset_hull_counts : forall K T S S', nsec_cf S' = nsec_cf S -> sec_T_cf S' = sec_T_cf S ->
nsec_cf S' <= K /\ sec_T_cf S' <= T -> nsec_cf S <= K /\ sec_T_cf S <= T.
Proof. intros K T S S' HN HT [H1 H2]. split; [rewrite <- HN | rewrite <- HT]; assumption. Qed.

(* cf_hull_ok_init at preset: init_state has no st_secs entry, so both meters are 0 (YGcfNsec.nsec_cf_init). *)
Lemma preset_hull_ok_init : forall K T, 0 <= K -> 0 <= T -> nsec_cf init_state <= K /\ sec_T_cf init_state <= T.
Proof. intros K T HK HT. unfold nsec_cf, sec_T_cf. cbn. lia. Qed.

(* The admission's errbuf frame (CfParams.cf_hull_ok_errb), preset's discharge: an errbuf step keeps both meters, since
   secs_errb_grow leaves every user entry as it is and appends only control entries (sm_size < 0), whose summands are
   0 (YGcfCount.seg_sum_eq). *)
Lemma preset_hull_ok_errb : forall K T S S', secs_errb_grow (st_secs S) (st_secs S') ->
sec_live_hulls S' = sec_live_hulls S -> nsec_cf S <= K /\ sec_T_cf S <= T -> nsec_cf S' <= K /\ sec_T_cf S' <= T.
Proof.
intros K T S S' G _ [HN HT]. split.
- rewrite (nsec_cf_errb S S' G). exact HN.
- assert (E : sec_T_cf S = sec_T_cf S').
  { unfold sec_T_cf. apply (seg_sum_eq (fun sm => if sec_user_cf sm then sm_len sm else 0)); [|exact G].
    intros sm H. cbv beta. rewrite (user_false sm H). reflexivity. }
  lia.
Qed.

(* The admission's entry headroom (CfParams.cf_hull_adm_post), preset's discharge in the CHARGE form: room at entry
   for the call's user entry and its mapped bytes keeps the meter at the call's post (secs_call_post). The charge of
   T is taken nonnegative (a PNull return adds nothing). *)
Lemma preset_hull_adm_post : forall K T S n q S',
nsec_cf S + (if from_primary n then 0 else 1) <= K ->
sec_T_cf S + (if from_primary n then 0 else sec_map_size n) <= T ->
0 <= (if from_primary n then 0 else sec_map_size n) ->
secs_call_post n S (q, S') -> nsec_cf S' <= K /\ sec_T_cf S' <= T.
Proof.
intros K T S n q S' HN HT H0 [PN PT]. cbn [fst snd] in PN, PT. unfold secs_call_d, secs_call_t in PN, PT.
destruct q; destruct (from_primary n); lia.
Qed.

(* The live hulls are among sec_hulls_cf's summands: each PSec chunk has its own st_secs entry (chunk_ok_cf; the
   chunks' ck_beg are distinct, wfc_chunks_nodup, and every PSec offset is kPage), a live user entry with
   sm_len = sec_map_size (ck_req k) >= 0 (wsc_lens), whose summand is exactly the chunk's hull. The index sums
   (cfn_sum, cfn_at, cfn_idx and their lemmas) are YGcfCount.v's. sec_hulls_cf's summand splits into the live and the
   dead user entries (the control entries give 0). *)
Definition hull_live_g (sm : secmap) : Z :=
if sec_user_cf sm then (if sm_live sm then sm_len sm / 8 + 8192 else 0) else 0.
Definition hull_dead_g (sm : secmap) : Z :=
if sec_user_cf sm then (if sm_live sm then 0 else sm_len sm / 8 + 8192) else 0.

Lemma cfn_at_hull_live_nonneg : forall l r, Forall (fun sm => 0 <= sm_len sm) l -> 0 <= cfn_at hull_live_g l r.
Proof.
intros l r HL. unfold cfn_at. destruct (nth_error l r) as [sm|] eqn:E; cbv iota; [|lia].
pose proof (proj1 (Forall_forall _ _) HL sm (nth_error_In _ _ E)) as L0. cbv beta in L0.
pose proof (Z.div_pos (sm_len sm) 8 L0 ltac:(lia)).
unfold hull_live_g. destruct (sec_user_cf sm), (sm_live sm); cbv iota; lia.
Qed.

(* Each PSec chunk's hull is its entry's live summand (chunk_ok_cf: the entry is live, a user entry, and its sm_len is
   the chunk's map size). *)
Lemma cfn_idx_live : forall s l, Forall (chunk_ok_cf s) l -> Forall (fun sm => 0 <= sm_len sm) (st_secs s) ->
fold_right (fun k acc => match ck_beg k with
| PSec _ _ => Z.max 0 (sec_map_size (ck_req k) / 8 + 8192) + acc | _ => acc end) 0 l
<= cfn_sum (cfn_at hull_live_g (st_secs s)) (cfn_idx l).
Proof.
intros s l H HL. induction H as [|k t Hk Ht IH]; [cbn; lia|].
rewrite cfn_idx_cons, cfn_sum_app. cbn [fold_right].
unfold chunk_ok_cf in Hk. destruct Hk as [Hreq Hk]. unfold cfn_idx1.
destruct (ck_beg k) as [|off|r o|cid pos] eqn:Eb; cbv iota;
  try (change (cfn_sum (cfn_at hull_live_g (st_secs s)) []) with 0; lia).
destruct Hk as (_ & _ & sm & Hsm & Hlive & Hsz & Hlen).
rewrite cfn_sum_cons. change (cfn_sum (cfn_at hull_live_g (st_secs s)) []) with 0.
assert (L0 : 0 <= sm_len sm) by exact (proj1 (Forall_forall _ _) HL sm (nth_error_In _ _ Hsm)).
assert (U : sec_user_cf sm = true) by (apply user_true; rewrite Hsz; apply cfa_needed_size_nonneg; lia).
assert (E : cfn_at hull_live_g (st_secs s) r = sec_map_size (ck_req k) / 8 + 8192).
{ unfold cfn_at. rewrite Hsm. cbv iota. unfold hull_live_g. rewrite U, Hlive, Hlen. reflexivity. }
rewrite E. pose proof (Z.div_pos (sec_map_size (ck_req k)) 8 ltac:(lia) ltac:(lia)). lia.
Qed.

Lemma cfa_lens_nonneg : forall U S, Wf_cf U S -> Forall (fun sm => 0 <= sm_len sm) (st_secs S).
Proof.
intros U S W. unfold Wf_cf in W. pose proof (wsc_lens _ (wfc_secondary _ _ _ _ _ W)) as LEN.
apply Forall_forall. intros sm Hin. cbv beta. pose proof (proj1 (Forall_forall _ _) LEN sm Hin) as H. cbv beta in H. lia.
Qed.

(* The live hulls are at most the live user entries' summands: distinct chunks name distinct entries. *)
Lemma sec_live_hulls_le_live : forall U S, Wf_cf U S ->
sec_live_hulls S <= fold_right (fun sm acc => hull_live_g sm + acc) 0 (st_secs S).
Proof.
intros U S W. pose proof (cfa_lens_nonneg U S W) as LEN. unfold Wf_cf in W.
pose proof (wfc_chunks _ _ _ _ _ W) as CK. pose proof (wfc_chunks_nodup _ _ _ _ _ W) as ND.
apply Z.le_trans with (cfn_sum (cfn_at hull_live_g (st_secs S)) (cfn_idx (st_chunks S))).
- unfold sec_live_hulls. exact (cfn_idx_live S (st_chunks S) CK LEN).
- apply Z.le_trans with (cfn_sum (cfn_at hull_live_g (st_secs S)) (seq 0 (length (st_secs S)))).
  + apply cfn_sum_incl.
    * exact (cfn_idx_nodup S (st_chunks S) CK ND).
    * intros r Hr. pose proof (cfn_idx_bound S (st_chunks S) r CK Hr). apply in_seq. lia.
    * intros r _. exact (cfn_at_hull_live_nonneg (st_secs S) r LEN).
  + apply Z.eq_le_incl. symmetry. apply (cfn_seq hull_live_g). intros; reflexivity.
Qed.

Lemma sec_hulls_cf_split : forall S, sec_hulls_cf S =
fold_right (fun sm acc => hull_live_g sm + acc) 0 (st_secs S) + fold_right (fun sm acc => hull_dead_g sm + acc) 0 (st_secs S).
Proof.
intros S. unfold sec_hulls_cf. induction (st_secs S) as [|a t IH]; cbn [fold_right]; [reflexivity|].
assert (P : (if sec_user_cf a then sm_len a / 8 + 8192 else 0) = hull_live_g a + hull_dead_g a)
  by (unfold hull_live_g, hull_dead_g; destruct (sec_user_cf a), (sm_live a); cbv iota; lia).
lia.
Qed.

(* The recycled secondaries D (YGcfCount.dead_secs_cf: the user entries that are dead). *)
Lemma dead_secs_cf_nonneg : forall S, 0 <= dead_secs_cf S.
Proof.
intros S. unfold dead_secs_cf. apply (cfa_sum_nonneg (fun sm => if sm_live sm || negb (sec_user_cf sm) then 0 else 1)).
intros sm _. destruct (sm_live sm || negb (sec_user_cf sm)); lia.
Qed.

(* Each dead user entry's summand is sm_len / 8 + 8192 >= 8192 (sm_len >= 0). *)
Lemma hull_dead_ge : forall l, Forall (fun sm => 0 <= sm_len sm) l ->
8192 * fold_right (fun sm acc => (if sm_live sm || negb (sec_user_cf sm) then 0 else 1) + acc) 0 l
<= fold_right (fun sm acc => hull_dead_g sm + acc) 0 l.
Proof.
intros l HL. induction HL as [|a t Ha Ht IH]; cbn [fold_right]; [lia|]. cbv beta in Ha.
pose proof (Z.div_pos (sm_len a) 8 Ha ltac:(lia)).
assert (P : 8192 * (if sm_live a || negb (sec_user_cf a) then 0 else 1) <= hull_dead_g a)
  by (unfold hull_dead_g; destruct (sec_user_cf a), (sm_live a); cbn [orb negb]; lia).
lia.
Qed.

(* a Theorem Labs lane's form: the live hulls plus two pages per recycled secondary (kk <= D) fit sec_hulls_cf, since the live
   hulls take only the live user entries' summands and each dead user entry's summand is at least 8192. *)
Lemma preset_hull_live_k : forall U S kk, Wf_cf U S -> 0 <= kk <= dead_secs_cf S ->
sec_live_hulls S + 2 * page_size * kk <= sec_hulls_cf S.
Proof.
intros U S kk W HK. pose proof (sec_live_hulls_le_live U S W) as L. pose proof (sec_hulls_cf_split S) as SP.
pose proof (hull_dead_ge (st_secs S) (cfa_lens_nonneg U S W)) as D. unfold dead_secs_cf in HK.
assert (P : page_size = 4096) by reflexivity. rewrite P. lia.
Qed.

Lemma preset_hull_live : forall U S, Wf_cf U S -> sec_live_hulls S <= sec_hulls_cf S.
Proof.
intros U S W. pose proof (preset_hull_live_k U S 0 W ltac:(pose proof (dead_secs_cf_nonneg S); lia)) as H. lia.
Qed.

(* ---- REPLY: the live hulls + 16384 per recycled secondary (YGcfCount.dead_secs_cf). ---- *)
Definition reply_hull_cf (S : astate) : Z := sec_live_hulls S + 16384 * dead_secs_cf S.
Definition reply_rec_drop_cf (L : Z) : Z := Z.max 0 (L / 8 + 8192) - 16384.

Lemma reply_hull_frame : forall S S', st_secs S' = st_secs S -> sec_live_hulls S' = sec_live_hulls S ->
reply_hull_cf S' = reply_hull_cf S.
Proof. intros S S' E H. unfold reply_hull_cf, dead_secs_cf. rewrite E, H. reflexivity. Qed.

Lemma reply_hull_alloc : forall S S' L z, 0 <= L -> 0 <= z -> st_secs S' = st_secs S ++ [mkSec L z true] ->
sec_live_hulls S' = sec_live_hulls S + Z.max 0 (L / 8 + 8192) ->
reply_hull_cf S + Z.max 0 (L / 8 + 8192) <= reply_hull_cf S'.
Proof.
intros S S' L z HL Hz E H. unfold reply_hull_cf, dead_secs_cf. rewrite E, H.
rewrite (cfa_fold_app1 (fun sm acc => (if sm_live sm || negb (sec_user_cf sm) then 0 else 1) + acc)
  (fun sm => if sm_live sm || negb (sec_user_cf sm) then 0 else 1)) by (intros; reflexivity).
cbv beta. cbn [sm_live orb]. lia.
Qed.

Lemma dead_secs_cf_errb : forall S S', secs_errb_grow (st_secs S) (st_secs S') -> dead_secs_cf S' = dead_secs_cf S.
Proof.
intros S S' G. unfold dead_secs_cf. symmetry.
apply (seg_sum_eq (fun sm => if sm_live sm || negb (sec_user_cf sm) then 0 else 1)); [|exact G].
intros sm H. cbv beta. rewrite (user_false sm H). destruct (sm_live sm); reflexivity.
Qed.

Lemma reply_hull_errb : forall S S', secs_errb_grow (st_secs S) (st_secs S') -> sec_live_hulls S' = sec_live_hulls S ->
reply_hull_cf S <= reply_hull_cf S'.
Proof. intros S S' G H. unfold reply_hull_cf. rewrite H, (dead_secs_cf_errb S S' G). lia. Qed.

Lemma reply_hull_recycle : forall X X2 pre k post r off sm, st_chunks X = pre ++ k :: post -> st_chunks X2 = pre ++ post ->
ck_beg k = PSec r off -> nth_error (st_secs X) r = Some sm -> sm_live sm = true -> 0 <= sm_size sm ->
sm_len sm = sec_map_size (ck_req k) -> st_secs X2 = lupd (st_secs X) r (mkSec (sm_len sm) (sm_size sm) false) ->
reply_hull_cf X - reply_hull_cf X2 <= reply_rec_drop_cf (sm_len sm).
Proof.
intros X X2 pre k post r off sm E E2 Hb Hn HL HZ HLen ES.
pose proof (sec_live_hulls_del X X2 pre k post E E2) as B. rewrite Hb in B. cbv beta iota in B.
assert (D : dead_secs_cf X2 = dead_secs_cf X + 1).
{ unfold dead_secs_cf. rewrite ES.
  rewrite (cfa_fold_lupd (fun sm acc => (if sm_live sm || negb (sec_user_cf sm) then 0 else 1) + acc)
    (fun sm => if sm_live sm || negb (sec_user_cf sm) then 0 else 1) ltac:(intros; reflexivity) (st_secs X) r _ sm Hn).
  cbv beta. replace (sec_user_cf (mkSec (sm_len sm) (sm_size sm) false)) with (sec_user_cf sm) by reflexivity.
  rewrite (user_true sm HZ), HL. cbn [sm_live orb negb]. lia. }
unfold reply_hull_cf, reply_rec_drop_cf. rewrite D, HLen. lia.
Qed.

Lemma reply_hull_init : reply_hull_cf init_state = 0.
Proof. reflexivity. Qed.

(* cf_hull_ok_init at reply: the count is 0 at init_state (YGcfNsec.nsec_cf_init). *)
Lemma reply_hull_ok_init : forall K, 0 <= K -> nsec_cf init_state <= K.
Proof. intros K HK. unfold nsec_cf. cbn. lia. Qed.

(* The cap (cf_hull_bound): the live hulls (<= 3,087,007,744) plus 16384 per dead user entry (at most the count, at
   most K) fit CF_HULL_MAX when 3,087,007,744 + 16384 * K does (the record's bound: 16384 * 2 ^ 23 at fuzz_reply). *)
Lemma reply_hull_bound : forall K, 3087007744 + 16384 * K <= CF_HULL_MAX -> forall S, nsec_cf S <= K ->
sec_live_hulls S <= 3087007744 -> reply_hull_cf S <= CF_HULL_MAX.
Proof. intros K HK S HN HL. pose proof (dead_le_nsec_cf S) as D. unfold reply_hull_cf. lia. Qed.

(* a Theorem Labs lane's form: the live hulls plus two pages per recycled secondary (kk <= D) fit reply_hull_cf's 16384 per dead
   user entry. *)
Lemma reply_hull_live_k : forall S kk, 0 <= kk <= dead_secs_cf S -> sec_live_hulls S + 2 * page_size * kk <= reply_hull_cf S.
Proof. intros S kk HK. assert (P : page_size = 4096) by reflexivity. unfold reply_hull_cf. rewrite P. lia. Qed.

Lemma reply_hull_mono_back : forall S S' K, secs_grow (st_secs S) (st_secs S') -> nsec_cf S' <= K -> nsec_cf S <= K.
Proof. intros S S' K G H. pose proof (sg_nsec_le S S' G). lia. Qed.

(* cf_hull_counts at reply: the admission is the count bound alone. *)
Lemma reply_hull_counts : forall S S' K, nsec_cf S' = nsec_cf S -> nsec_cf S' <= K -> nsec_cf S <= K.
Proof. intros S S' K HN H. rewrite <- HN. exact H. Qed.

(* The admission's errbuf frame (CfParams.cf_hull_ok_errb), reply's discharge: nsec_cf does not move. *)
Lemma reply_hull_ok_errb : forall S S' K, secs_errb_grow (st_secs S) (st_secs S') -> sec_live_hulls S' = sec_live_hulls S ->
nsec_cf S <= K -> nsec_cf S' <= K.
Proof. intros S S' K G _ H. rewrite (nsec_cf_errb S S' G). exact H. Qed.

(* The admission's entry headroom (CfParams.cf_hull_adm_post), reply's discharge in the CHARGE form: room at entry for
   the call's one user entry (none when n is a primary request) keeps the count bound at the call's post. *)
Lemma reply_hull_adm_post : forall K S n q S', nsec_cf S + (if from_primary n then 0 else 1) <= K ->
secs_call_post n S (q, S') -> nsec_cf S' <= K.
Proof.
intros K S n q S' H [PN _]. cbn [fst snd] in PN. unfold secs_call_d in PN.
destruct q; destruct (from_primary n); lia.
Qed.

(* The law in the order the errbuf steps use it (Main 2026-10-30). *)
Lemma cf_hull_ok_errb_frame : forall S S', cf_hull_ok S -> secs_errb_grow (st_secs S) (st_secs S') ->
sec_live_hulls S' = sec_live_hulls S -> cf_hull_ok S'.
Proof. intros S S' H G L. exact (cf_hull_ok_errb S S' G L H). Qed.
End U.
