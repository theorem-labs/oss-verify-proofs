(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10-31: from proofs/plugin-hostd/fuzz_reply/lib/B/RepRelcf.v (commit 4d286b2e618d, file sha256 34663cd48b4e) onto omx-clap-core/fuzz_preset's ASan+UBSan image B' (fuzz_preset.asan-ubsan, pin d663f82d7f48, twin c90d4fa54d43); module paths changed; reply's image-instance names mapped to preset's B' instance (AGif2reply / AImg_reply -> AGif2cgif / AImg_cgif) and its row names to preset's (Reply* -> Preset*, *reply -> *preset); its 1 image numerals moved by symbol from fuzz_reply.asan-ubsan (pin 10ffb5f9202a) to B' (port_addr_check 3d2eee813cce predictions; object addresses written in decimal, jump-table offsets and list indices by the same stage map), 1 list indices re-picked, and 4 addresses named in comments; facts preset already states are cited, not restated; comment references to people and refs dropped; no other numeral changed. *)
(* Modified by Theorem Labs, 2026-10: from proofs/cgif/cgif_file_fuzzer/lib/RepRelcf.v (commit f01d79f3fb5, cf refill round 3; file sha256 e439fe804d10) onto plugin-hostd/fuzz_reply's asan image (unstripped fuzz_reply.asan, sha256 d751b179ea49; pin 42c58610e125); module paths changed; its 1 image addresses moved by function pairs the comparison kit cmpkit 86da41d3ef68 calls the same code (strictcmp3 65688e94214a, by funcpair_reply 6963bc4a94fc on the cgif twin ce511d541cda; 1 port_addr_check e55e1b52a8a0 MAPS predictions, each code one re-derived by the pair, each data one a pc-relative target of both paired functions; 0 code pcs the tool read as sizes, by the pair), and 1 pcs named in comments; no other numeral changed. *)
(* Theorem Labs, 2026-10-30 (a prior worker, RepF4Append's relation side): the MODEL-and-RELATION lemmas the walk of
   __asan::AppendToErrorMessageBuffer (0x55df8, RepIFcf.append_spec_cf) uses to rebuild RepIFcf.errb_call_pre across
   the error-message buffer's (re)map.  Pure Rocq over the existing model (YG00cf.v) and relation (YG0ncf.v,
   YGcfInstBase.v) texts; no machine code runs in this file.
   rule 24: proves no function (kind: model and invariant lemmas; the lane's reuse search is the proof-index
   lookup of UnmapOrDie internal_memset internal_memcpy internal_strlen GetNamedMappingFd IncreaseTotalMmap,
   2026-10-30T02:55Z, 0 released lemmas for every name).
   The lemmas:
   - errb_cells_build / errb_cells_proj: YG0ncf.errb_cells_cf from / to the five object words as val_mem facts,
     the buffer's visibility, size <= cap and cap mod kPage = 0;
   - errb_aox_obj / errb_aox_buf: the object's 56 bytes and the buffer are in the allocator's owned set AOXm_cf;
   - errb_xs_not_aowned: the errbuf extent is never in aowned;
   - rr_grant_facts / errb_grant_facts: YG0j.anon_grant_facts at the cf ledger (plus apartness from the errbuf);
   - errb_rel_setsize: the model facts of errb_set_size;
   - errb_rel_map / errb_rel_remap: the relation SPLIT (rr_split, field round 2) after the first map / after a remap
     and the munmap of the old buffer, at the grown layout set_ly_sec ly (length (st_secs S)) a: ARmcf and ahs at
     the entry state, the ledger and the budget at the step's state.  Both take ALEDGER_X, the eager-ledger
     bound of a Theorem Labs lane's layer fix (alc_eager_x with the errbuf extent inside the esec, a prior worker 03:3xZ), at the
     entry and give it back at the post: with today's alc_eager_x (raw errb_cap_cf) a remap's post is not
     derivable (a lazy range inside the old buffer makes the munmap release fewer eager bytes than its capacity).
   The building blocks: rr_ARmcf_layout (the cf twin of YFib.ARm_layout_le), rr_zf / rr_vis_zf (the relation reads
   memory only in static / secondary extents and the shadow band), rr_ledger_rebuild (ALedger_cf across the map and
   the munmap, after YG0j.ALedger_anon / ALedger_munmap), rr_rel_core.  RepRelXcf.errb_rel_post rebuilds ARcf at the
   end of the walk. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK11 YP09 YK04 YA0i YA0n YI04.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG04 YG07 YG0f YG0v YG0d YG0n.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YB1v YF0m YF0x.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YGcfNames YG01cf YG00cf YG0ncf YG0dcf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK13 YK0g YK0v YA06 YA09 YG0h YG0j YG0q YG0s YG08cf YG06bcf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YFib.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YFfn.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG0scf YG0qcf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfMallocCompose.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfXs YGcfXsMapped.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcfInstBase.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcfLazyMaps YGcfSecsStep YGcfAbudget.
(* stdpp, through the LPS modules, shadows several list names; the lemmas here are Stdlib's. *)
From Stdlib Require Import List.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams}.
Variable B : asyms.

(* ================================================================================================================ *)
(* 1. The object cells (YG0ncf.errb_cells_cf) as val_mem facts.                                               *)
Lemma rr_cell_of_val_mem : forall ly (H : word -> bool) mem (A v : Z),
  val_mem tfibsegs (mrestrict H mem) A 8 v -> cell_holds B ly (aview tfibsegs H mem) (z8 (ANum A) v).
Proof.
intros ly H mem A v HV k Hk. cbn [cell_holds c_at c_val c_w z8 c8 aeval]. unfold aview. rewrite (HV k Hk).
cbn [option_map]. rewrite <- le_byte_eq. rewrite unsigned_lit_small8; [reflexivity|].
unfold YG0f.le_byte. apply Z.mod_pos_bound. lia.
Qed.

Lemma rr_val_mem_of_cell : forall ly (H : word -> bool) mem (A v : Z),
  cell_holds B ly (aview tfibsegs H mem) (z8 (ANum A) v) -> val_mem tfibsegs (mrestrict H mem) A 8 v.
Proof. intros ly H mem A v C. exact (cell_holds_val_mem B ly H mem (ANum A) 8 (ANum v) C). Qed.

Lemma errb_cells_build : forall ly S (H : word -> bool) (mem : word -> option byte),
  val_mem tfibsegs (mrestrict H mem) cf_errbuf_obj 8 (if errb_mapped_cf S then cf_errbuf_obj + 32 else 0) ->
  val_mem tfibsegs (mrestrict H mem) (cf_errbuf_obj + 16) 8 0 ->
  val_mem tfibsegs (mrestrict H mem) (cf_errbuf_obj + 32) 8 (YG0ncf.errb_data_cf ly S) ->
  val_mem tfibsegs (mrestrict H mem) (cf_errbuf_obj + 40) 8 (errb_cap_cf S) ->
  val_mem tfibsegs (mrestrict H mem) (cf_errbuf_obj + 48) 8 (errb_size_cf S) ->
  (forall a, YG0ncf.errb_data_cf ly S <= a < YG0ncf.errb_data_cf ly S + errb_cap_cf S ->
     aview tfibsegs H mem a <> None) ->
  errb_size_cf S <= errb_cap_cf S -> errb_cap_cf S mod kPage = 0 ->
  YG0ncf.errb_cells_cf B ly S (aview tfibsegs H mem).
Proof.
intros ly S H mem P M D C SZ V L1 L2. unfold YG0ncf.errb_cells_cf.
split; [exact (rr_cell_of_val_mem ly H mem _ _ P)|].
split; [exact (rr_cell_of_val_mem ly H mem _ _ M)|].
split; [exact (rr_cell_of_val_mem ly H mem _ _ D)|].
split; [exact (rr_cell_of_val_mem ly H mem _ _ C)|].
split; [exact (rr_cell_of_val_mem ly H mem _ _ SZ)|].
exact (conj V (conj L1 L2)).
Qed.

Lemma errb_cells_proj : forall ly S (H : word -> bool) (mem : word -> option byte),
  YG0ncf.errb_cells_cf B ly S (aview tfibsegs H mem) ->
  val_mem tfibsegs (mrestrict H mem) cf_errbuf_obj 8 (if errb_mapped_cf S then cf_errbuf_obj + 32 else 0) /\
  val_mem tfibsegs (mrestrict H mem) (cf_errbuf_obj + 16) 8 0 /\
  val_mem tfibsegs (mrestrict H mem) (cf_errbuf_obj + 32) 8 (YG0ncf.errb_data_cf ly S) /\
  val_mem tfibsegs (mrestrict H mem) (cf_errbuf_obj + 40) 8 (errb_cap_cf S) /\
  val_mem tfibsegs (mrestrict H mem) (cf_errbuf_obj + 48) 8 (errb_size_cf S) /\
  (forall a, YG0ncf.errb_data_cf ly S <= a < YG0ncf.errb_data_cf ly S + errb_cap_cf S ->
     aview tfibsegs H mem a <> None) /\
  errb_size_cf S <= errb_cap_cf S /\ errb_cap_cf S mod kPage = 0.
Proof.
intros ly S H mem (P & M & D & C & SZ & V & L1 & L2).
split; [exact (rr_val_mem_of_cell ly H mem _ _ P)|].
split; [exact (rr_val_mem_of_cell ly H mem _ _ M)|].
split; [exact (rr_val_mem_of_cell ly H mem _ _ D)|].
split; [exact (rr_val_mem_of_cell ly H mem _ _ C)|].
split; [exact (rr_val_mem_of_cell ly H mem _ _ SZ)|].
exact (conj V (conj L1 L2)).
Qed.

(* ================================================================================================================ *)
(* 2. The write sets: the object's 56 bytes are owned statically (Tfib_owned_static's (0xaaf50, 0x5cdd50 - 0xaaf50),
   YF0m.v:280), and the buffer [data, data + cap) is the errbuf extent xs_cf ly S itself.                           *)
Lemma errb_aox_obj : forall Hp ly S W mem md a,
  TfibSyms B -> cf_errbuf_obj = 0xaaf68 -> ARcf tfibsegs B ly S Hp W mem md ->
  cf_errbuf_obj <= a < cf_errbuf_obj + 56 -> AOXm_cf B ly S a.
Proof.
intros Hp ly S W mem md a TS EO (M & _) Ha. left.
eapply own_static_cf; [exact M|].
rewrite (ts_owned _ TS). unfold Tfib_owned_static.
do 3 apply Exists_cons_tl. apply Exists_cons_hd. unfold in_zr. cbn [fst snd]. rewrite EO in Ha. lia.
Qed.

Lemma errb_data_xs : forall ly S, xs_cf ly S =
  match last_cap_idx (st_secs S) 0 None with
  | Some _ => [(YG0ncf.errb_data_cf ly S, errb_cap_cf S)] | None => [] end.
Proof.
intros ly S. unfold xs_cf, YG0ncf.errb_data_cf. destruct (last_cap_idx (st_secs S) 0 None); reflexivity.
Qed.

(* With no current capacity entry errb_e is the default (mkSec 0 ...), so the capacity is 0 and the range is empty. *)
Lemma rr_last_cap_none : forall l i acc, last_cap_idx l i acc = None -> acc = None /\ filter is_errb_cap l = [].
Proof.
induction l as [|sm t IH]; intros i acc H; cbn [last_cap_idx filter] in *; [split; [exact H | reflexivity]|].
destruct (is_errb_cap sm) eqn:E.
- destruct (IH _ _ H) as [X _]. discriminate X.
- exact (IH _ _ H).
Qed.

Lemma errb_cap_none : forall S, last_cap_idx (st_secs S) 0 None = None -> errb_cap_cf S = 0.
Proof.
intros S E. destruct (rr_last_cap_none _ _ _ E) as [_ F].
unfold errb_cap_cf, errb_e. rewrite F. reflexivity.
Qed.

Lemma errb_aox_buf : forall ly S a,
  YG0ncf.errb_data_cf ly S <= a < YG0ncf.errb_data_cf ly S + errb_cap_cf S -> AOXm_cf B ly S a.
Proof.
intros ly S a Ha. right. rewrite errb_data_xs.
destruct (last_cap_idx (st_secs S) 0 None) eqn:E.
- apply Exists_cons_hd. unfold in_zr. cbn [fst snd]. exact Ha.
- rewrite (errb_cap_none S E) in Ha. lia.
Qed.

(* ================================================================================================================ *)
(* 3. The grant's placement at the cf ledger: YG0j.v:292 anon_grant_facts with ALedger_cf / Wf_cf (rr_grant_facts).  The proof reads
   only the ledger fields ALedger_cf shares with cgif's ALedger (alc_reserved, alc_prim, alc_Q, alc_sec, alc_perm,
   alc_band, alc_top, alc_imgcov), so it is cgif's text with the cf accessors.                                       *)
Ltac rr_ceil := let H := fresh "CR" in let H2 := fresh "CR" in
  pose proof (proj1 (@YG0f.ASAN_CEIL_range _)) as H; pose proof H as H2; unfold ASAN_CEIL in H2.

Lemma rr_grant_facts : forall (ly : alayout) (S : astate) (md : Model) (a n : word),
  layout_ok ly -> Wf_cf (as_universe B) S -> sec_placed ly S -> ALedger_cf tfibsegs ly S md ->
  grant_ok_na_pin md a (bv_unsigned n) = true -> 0 < bv_unsigned n -> bv_unsigned n mod 4096 = 0 ->
  page_aligned (bv_unsigned a) /\ in_app (bv_unsigned a) (bv_unsigned n) /\
  bv_unsigned a + bv_unsigned n <= ASAN_CEIL /\
  Forall (zdisjoint (bv_unsigned a, bv_unsigned n))
    (static_extents ly ++ sec_extents ly S ++ perm_maps ly ++ band_maps).
Proof.
intros ly S md a n LO W PL L G Hn Hnal.
pose proof (bv_unsigned_in_range 64 a) as Ra. pose proof (bv_unsigned_in_range 64 n) as Rn. unfold bv_modulus in Ra, Rn.
unfold grant_ok_na_pin in G. apply andb_prop in G as [G G4]. apply andb_prop in G as [G G3]. apply andb_prop in G as [G1 G2].
apply Z.eqb_eq in G1. apply Z.ltb_lt in G2. apply Z.leb_le in G3. unfold page_size in G1.
assert (Hn64 : Z_to_bv 64 (bv_unsigned n) = n) by (apply w64_uw). rewrite Hn64 in G4.
set (lo := bv_unsigned a) in *. set (len := bv_unsigned n) in *.
destruct L as [L1 L2 L3 L4 L5 L6 L7 L8 L9 L10 L11 L12 L13 L14 L15].
assert (CE : lo + len <= ASAN_CEIL).
{ unfold ASAN_CEIL. apply (YM05.grant_below_ceil (alloc_top (m_vmmaps md)) (lo + len) L13); [| exact G3].
apply Z.mod_divide in G1 as [q Hq]; [|lia]. apply Z.mod_divide in Hnal as [q' Hq']; [|lia]. rewrite Hq, Hq'.
replace (q * 4096 + q' * 4096) with ((q + q') * 4096) by lia. apply Z_mod_mult. }
rr_ceil.
assert (RF : forall z, 0 <= fst z -> 0 <= snd z -> fst z + snd z < 2 ^ 64 ->
In (wiv z) (vm_reserved (m_vmmaps md) ++ vm_maps (m_vmmaps md)) -> zdisjoint (lo, len) z).
{ intros z Z1 Z2 Z3 Hin. pose proof (YK13.region_free_In _ a n (w64 (fst z)) (w64 (snd z)) G4 Hin) as D.
unfold w64 in D. rewrite !Z_to_bv_unsigned, !bv_wrap_small in D by (unfold bv_modulus; lia). unfold zdisjoint. cbn [fst snd]. subst lo len. lia. }
assert (RFm : forall z, 0 <= fst z -> 0 <= snd z -> fst z + snd z < 2 ^ 64 -> In (wiv z) (vm_maps (m_vmmaps md)) -> zdisjoint (lo, len) z).
{ intros z Z1 Z2 Z3 Hin. apply RF; [exact Z1 | exact Z2 | exact Z3 | apply in_app_iff; right; exact Hin]. }
assert (BAND : Forall (zdisjoint (lo, len)) band_maps).
{ apply Forall_forall. intros z Hz. apply RFm; [ | | | exact (L11 z Hz)]; unfold band_maps in Hz; cbn in Hz;
destruct Hz as [<-|[<-|[<-|[]]]]; cbn [fst snd]; unfold kLowShadowBeg, kLowShadowEnd, kHighShadowBeg, kHighShadowEnd; lia. }
assert (APP : in_app lo len).
{ pose proof BAND as B'. unfold band_maps in B'. apply Forall_cons_iff in B' as [D1 B']. apply Forall_cons_iff in B' as [D2 B']. apply Forall_cons_iff in B' as [D3 _].
unfold zdisjoint in D1, D2, D3. cbn [fst snd] in D1, D2, D3. unfold in_app.
unfold kLowShadowBeg, kLowShadowEnd, kHighShadowBeg, kHighShadowEnd, kHighMemBeg, ASAN_CEIL in *.
split; [| clear - D1 D2 D3 Hn CE CR0; lia].
apply Z.mod_divide in G1 as [q Hq]; [|lia]. subst lo len. clear - Hq G2. lia. }
split; [exact G1|]. split; [exact APP|]. split; [exact CE|].
pose proof (lo_high ly LO) as [HP1 HP2].
assert (PRIM : zdisjoint (lo, len) (ly_prim ly, kPrimResvSize)).
{ destruct L4 as (pieces & (P1 & P2 & P3) & P4).
unfold zdisjoint. cbn [fst snd].
destruct (Z_lt_le_dec lo (ly_prim ly + kPrimResvSize)) as [X1|X1]; [|right; lia].
destruct (Z_lt_le_dec (ly_prim ly) (lo + len)) as [X2|X2]; [|left; lia]. exfalso.
set (x := Z.max lo (ly_prim ly)).
assert (Hx : ly_prim ly <= x < ly_prim ly + kPrimResvSize) by (subst x; unfold kPrimResvSize in *; lia).
assert (NH : ~ prim_hole_at ly S x) by exact (wf_no_prim_hole_cf _ _ _ _ S ly x W).
apply (P3 x Hx) in NH. apply Exists_exists in NH as (p0 & Hp0 & Hin0). unfold in_zr in Hin0.
pose proof (proj1 (P4 p0) Hp0) as (Hm0 & C1 & C2 & C3).
pose proof (RFm p0 ltac:(unfold kHighMemBeg in HP1; lia) ltac:(lia) ltac:(clear - C2 C3 HP1 HP2 CR CR0; unfold kPrimResvSize, kHighMemBeg, ASAN_CEIL in *; lia) Hm0) as D.
unfold zdisjoint in D. cbn [fst snd] in D. subst x. lia. }
pose proof (lo_stk_ceil ly LO) as STK.
assert (IMG : zdisjoint (lo, len) (ly_img ly)).
{ pose proof (lo_img ly LO) as (J0 & J1 & J2 & J3). unfold zdisjoint. cbn [fst snd].
destruct (Z_lt_le_dec lo (fst (ly_img ly) + snd (ly_img ly))) as [X1|X1]; [|right; lia].
destruct (Z_lt_le_dec (fst (ly_img ly)) (lo + len)) as [X2|X2]; [|left; lia]. exfalso.
set (x := Z.max lo (fst (ly_img ly))).
destruct (L14 x ltac:(unfold in_zr; subst x; lia)) as (e & He & E1).
pose proof (YK13.region_free_In _ a n (fst e) (snd e) G4 ltac:(apply in_app_iff; left; rewrite L3, <- surjective_pairing; exact He)) as D.
subst lo len x. lia. }
assert (PERM : Forall (zdisjoint (lo, len)) (perm_maps ly)).
{ apply Forall_forall. intros z Hz. pose proof (perm_facts ly 1 LO ltac:(lia) z Hz) as (Z1 & Z2 & Z3 & _). apply RFm; [lia | lia | lia | exact (L10 z Hz)]. }
assert (QQ : zdisjoint (lo, len) (ly_Q ly, kPtrArrayResv)).
{ pose proof (proj1 (Forall_forall _ _) (lo_app ly LO) (ly_Q ly, kPtrArrayResv) ltac:(unfold owned_extents; cbn; tauto)) as [Q1 Q2]. cbn [fst snd] in Q1, Q2.
apply RFm; [cbn [fst]; lia | cbn [snd]; unfold kPtrArrayResv; lia | cbn [fst snd]; unfold kLowShadowBeg, kPtrArrayResv, ASAN_CEIL in *; lia | exact L5]. }
assert (SEC : Forall (zdisjoint (lo, len)) (sec_extents ly S)).
{ apply Forall_forall. intros e He. destruct PL as [PF _]. pose proof (proj1 (Forall_forall _ _) PF e He) as (_ & [E1 E2] & E3).
pose proof (proj1 (Forall_forall _ _) (sec_extents_sizes64P_cf (as_universe B) 0 0 0 ly S W) e He) as E4. cbn beta in E4.
apply RFm; [lia | lia | unfold ASAN_CEIL in *; lia | exact (L7 e He)]. }
rewrite !Forall_app. split; [| split; [exact SEC | split; [exact PERM | exact BAND]]].
unfold static_extents, owned_extents. apply Forall_app. split.
- pose proof PERM as PM. unfold perm_maps in PM. apply Forall_app in PM as [PM _].
apply Forall_cons_iff in PM as [PT PM]. apply Forall_cons_iff in PM as [PFk PM]. apply Forall_cons_iff in PM as [PNB PM].
apply Forall_cons_iff in PM as [PSB PM]. apply Forall_cons_iff in PM as [PC PM]. apply Forall_cons_iff in PM as [PD _].
repeat apply Forall_cons; try apply Forall_nil; try assumption.
unfold zdisjoint in PC |- *. cbn [fst snd] in PC |- *. unfold kCtxMapSize in PC. lia.
- apply Forall_cons; [| apply Forall_cons; [exact IMG | apply Forall_nil]].
unfold zdisjoint. cbn [fst snd]. left. unfold ASAN_CEIL in *. lia.
Qed.

(* ================================================================================================================ *)
(* 4. The state steps that touch only st_secs (errb_frame, YG06bcf.v:67): every part of the relation except Wf_cf
   and the errbuf placement reads the state through st_chunks / st_regions / st_sec_arr / ... only.                 *)
(* The eager-ledger bound of a Theorem Labs lane's layer fix (a prior worker 03:3xZ): alc_eager_x with the errbuf extent charged
   its eager bytes (inside the esec) instead of its raw capacity.  Until the layer lands it is a named premise of
   the map / remap lemmas; they also give it back at the post. *)
Definition ALEDGER_X (ly : alayout) (S : astate) (md : Model) : Prop :=
  eager_used md <= E_BASE + prim_committed S + 8 * st_sec_reserved S +
    esec (vm_noaccess (m_vmmaps md)) (m_vm_lazy md) (sec_extents ly S ++ errb_zone ly S).

Lemma rr_ledger_secs : forall ly S S1 md, errb_frame S S1 -> xs_cf ly S1 = xs_cf ly S -> errb_cap_cf S1 = errb_cap_cf S ->
  ALedger_cf tfibsegs ly S md -> ALedger_cf tfibsegs ly S1 md.
Proof.
intros ly S S1 md EF XS CAP L. unfold errb_frame in EF.
destruct L as [L1 L2 L3 L4 L5 L6 L7 L8 L9 L10 L11 L12 L13 L14 L15 L16 L17].
constructor; try assumption.
- rewrite EF. exact L4.
- rewrite EF. exact L7.
- unfold errb_zone. rewrite XS. rewrite EF. exact L8.
- unfold eager_cf, errb_zone in *. rewrite XS. rewrite EF. exact L9.
- rewrite EF. exact L12.
- rewrite XS. exact L17.
Qed.

(* The new alc_eager_x (YG0ncf.v) is ALEDGER_X: the errbuf extent is inside the esec. *)
Lemma aledger_x_of_ledger : forall ly S md, ALedger_cf tfibsegs ly S md -> ALEDGER_X ly S md.
Proof. intros ly S md L. pose proof (alc_eager_x _ _ _ _ L) as X. unfold eager_cf in X. unfold ALEDGER_X. lia. Qed.

Lemma rr_aledger_x_secs : forall ly S S1 md, errb_frame S S1 -> xs_cf ly S1 = xs_cf ly S ->
  ALEDGER_X ly S md -> ALEDGER_X ly S1 md.
Proof. intros ly S S1 md EF XS X. unfold ALEDGER_X, errb_zone in *. rewrite XS. unfold errb_frame in EF. rewrite EF. exact X. Qed.

(* The hull term across an errbuf step: the layer's errbuf frame of the admission (YGcfAbudget.cf_hull_ok_errb_frame,
   CfParams' cf_hull_ok_errb) and the st_secs steps as secs_errb_grow (YGcfSecsStep.secs_grow_remap /
   secs_errb_set_grow_ret, field round 3). *)

(* An errbuf step keeps the chunks, so the live hulls; with the layer's frame the admission carries over the step. *)
Lemma rr_hulls_frame : forall S S1, errb_frame S S1 -> sec_live_hulls S1 = sec_live_hulls S.
Proof. intros S S1 EF. unfold errb_frame in EF. rewrite EF. reflexivity. Qed.

Lemma rr_hull_ok_step : forall S S1, errb_frame S S1 -> secs_errb_grow (st_secs S) (st_secs S1) ->
  cf_hull_ok S -> cf_hull_ok S1.
Proof. intros S S1 EF G H. exact (YGcfAbudget.cf_hull_ok_errb_frame S S1 H G (rr_hulls_frame S S1 EF)). Qed.

(* errb_map_cf's st_secs step (YGcfXs.cfx_retire is YGcfSecsStep.ss_retire, the same re-tag). *)
Lemma rr_secs_grow_map : forall S S1 ncap, 0 <= ncap ->
  st_secs S1 = map cfx_retire (st_secs S) ++ [mkSec ncap ERRB_CAP_TAG false] -> secs_errb_grow (st_secs S) (st_secs S1).
Proof. intros S S1 ncap Hn E. rewrite E. exact (YGcfSecsStep.secs_grow_remap (st_secs S) ncap Hn). Qed.

(* errb_map_cf's re-tag (cfx_retire) touches no size entry, so the size survives the map. *)
Lemma rr_size_map : forall S S1 ncap,
  st_secs S1 = map cfx_retire (st_secs S) ++ [mkSec ncap ERRB_CAP_TAG false] -> errb_size_cf S1 = errb_size_cf S.
Proof.
intros S S1 ncap E. unfold errb_size_cf. rewrite E.
rewrite find_sz_app_ctl by reflexivity.
change (map cfx_retire (st_secs S)) with (map errb_retire_f (st_secs S)).
rewrite find_sz_retire.
destruct (find_sz (st_secs S) 0) as [i|] eqn:F; [|reflexivity].
destruct (find_sz_spec _ _ _ F) as [_ (sm & Ei & _)]. rewrite Nat.sub_0_r in Ei.
rewrite nth_error_app1 by (rewrite length_map; eapply nth_error_lt; exact Ei).
rewrite nth_error_map, Ei. cbn [option_map].
unfold errb_retire_f. destruct (is_errb_cap sm); reflexivity.
Qed.

Lemma rr_budget_secs : forall ly S S1 (W : world tfibsegs), errb_frame S S1 -> secs_errb_grow (st_secs S) (st_secs S1) ->
  errb_cap_cf S <= errb_cap_cf S1 -> abudget_ok_cf tfibsegs ly S W -> abudget_ok_cf tfibsegs ly S1 W.
Proof.
intros ly S S1 W EF GR CAP (A1 & A2 & A3).
pose proof (cf_hull_errb S S1 GR (rr_hulls_frame S S1 EF)) as HH.
unfold errb_frame in EF.
assert (E1 : prim_committed S1 = prim_committed S) by (rewrite EF; reflexivity).
assert (E2 : st_sec_reserved S1 = st_sec_reserved S) by (rewrite EF; reflexivity).
assert (E3 : sec_live_bytes S1 = sec_live_bytes S) by (rewrite EF; reflexivity).
split; [|split; [rewrite EF; exact A2 | exact A3]].
unfold abudget_cf in *. rewrite E1, E2, E3. lia.
Qed.

Lemma rr_ahs_secs : forall ly S S1 H mem, errb_frame S S1 -> ahs B ly S H mem -> ahs B ly S1 H mem.
Proof. intros ly S S1 H mem EF A. unfold errb_frame in EF. rewrite EF. exact A. Qed.

(* ================================================================================================================ *)
(* 5. errb_set_size (YG00cf.v:91-96): the size entry is rewritten in place or appended.                            *)
Lemma rr_existsb_filter : forall l, existsb is_errb_cap l =
  match filter is_errb_cap l with [] => false | _ => true end.
Proof.
induction l as [|x t IH]; [reflexivity|]. cbn [existsb filter].
destruct (is_errb_cap x); [reflexivity | exact IH].
Qed.

Lemma rr_secs_same : forall ly S S1, last_cap_idx (st_secs S1) 0 None = last_cap_idx (st_secs S) 0 None ->
  filter is_errb_cap (st_secs S1) = filter is_errb_cap (st_secs S) ->
  xs_cf ly S1 = xs_cf ly S /\ errb_cap_cf S1 = errb_cap_cf S /\
  YG0ncf.errb_data_cf ly S1 = YG0ncf.errb_data_cf ly S /\ errb_mapped_cf S1 = errb_mapped_cf S.
Proof.
intros ly S S1 I F.
assert (C : errb_cap_cf S1 = errb_cap_cf S) by (unfold errb_cap_cf, errb_e; rewrite F; reflexivity).
split; [unfold xs_cf; rewrite I, C; reflexivity|]. split; [exact C|].
split; [unfold YG0ncf.errb_data_cf; rewrite I; reflexivity|].
unfold errb_mapped_cf. rewrite !rr_existsb_filter, F. reflexivity.
Qed.

Lemma rr_size_noncap : forall l i, find_sz l 0 = Some i -> forall sm, nth_error l i = Some sm -> is_errb_cap sm = false.
Proof.
intros l i E sm Hsm. destruct (find_sz_spec l 0 i E) as [_ (sm' & E' & Sz)]. rewrite Nat.sub_0_r in E'.
rewrite E' in Hsm. injection Hsm as <-. unfold is_errb_sz, is_errb_cap, ERRB_SZ_TAG, ERRB_CAP_TAG in *.
apply Z.eqb_eq in Sz. rewrite Sz. reflexivity.
Qed.

Lemma rr_setsize_model : forall ly S S' ns, errb_set_size ns S = IRet (tt, S') ->
  errb_frame S S' /\ xs_cf ly S' = xs_cf ly S /\ errb_cap_cf S' = errb_cap_cf S /\
  YG0ncf.errb_data_cf ly S' = YG0ncf.errb_data_cf ly S /\ errb_mapped_cf S' = errb_mapped_cf S /\
  errb_size_cf S' = ns.
Proof.
intros ly S S' ns H. unfold errb_set_size, YG00.modify in H. cbv beta in H. injection H as <-.
set (new := mkSec ns ERRB_SZ_TAG false).
destruct (find_sz (st_secs S) 0) as [i|] eqn:E.
- pose proof (find_sz_spec _ _ _ E) as [_ (smz & Ez & _)]. rewrite Nat.sub_0_r in Ez.
  assert (Hi : (i < length (st_secs S))%nat) by (eapply nth_error_lt; exact Ez).
  pose proof (cfxm_capeq_lupd (st_secs S) i new eq_refl (rr_size_noncap _ _ E)) as C.
  destruct (rr_secs_same ly S (set_secs (lupd (st_secs S) i new) S) (cfxm_capeq_idx _ _ C 0 None) (cfxm_capeq_filter _ _ C))
    as (X1 & X2 & X3 & X4).
  split; [unfold errb_frame; destruct S; reflexivity|].
  split; [exact X1|]. split; [exact X2|]. split; [exact X3|]. split; [exact X4|].
  unfold errb_size_cf. cbn [st_secs set_secs].
  pose proof (find_sz_lupd (st_secs S) 0 i new E eq_refl) as F. rewrite Nat.sub_0_r in F. rewrite F.
  rewrite nth_error_lupd_same by exact Hi. reflexivity.
- assert (I : last_cap_idx (st_secs (set_secs (st_secs S ++ [new]) S)) 0 None = last_cap_idx (st_secs S) 0 None).
  { cbn [st_secs set_secs]. rewrite cfx_last_cap_idx_app. reflexivity. }
  assert (F : filter is_errb_cap (st_secs (set_secs (st_secs S ++ [new]) S)) = filter is_errb_cap (st_secs S)).
  { cbn [st_secs set_secs]. rewrite filter_app. cbn [filter]. rewrite app_nil_r. reflexivity. }
  destruct (rr_secs_same ly S _ I F) as (X1 & X2 & X3 & X4).
  split; [unfold errb_frame; destruct S; reflexivity|].
  split; [exact X1|]. split; [exact X2|]. split; [exact X3|]. split; [exact X4|].
  unfold errb_size_cf. cbn [st_secs set_secs].
  pose proof (find_sz_app_none (st_secs S) new 0 E eq_refl) as F'. cbn [Nat.add] in F'. rewrite F'.
  rewrite nth_error_app2, Nat.sub_diag by lia. reflexivity.
Qed.

Lemma errb_rel_setsize : forall ly (S S' : astate) (md : Model) (ns : Z),
  xs_placed_cf ly S -> xs_mapped_cf ly S md ->
  errb_set_size ns S = IRet (tt, S') ->
  xs_mapped_cf ly S' md /\ xs_placed_cf ly S' /\
  (ALEDGER_X ly S md -> ALEDGER_X ly S' md) /\
  errb_cap_cf S' = errb_cap_cf S /\ YG0ncf.errb_data_cf ly S' = YG0ncf.errb_data_cf ly S /\
  errb_mapped_cf S' = errb_mapped_cf S /\ errb_size_cf S' = ns /\ xs_cf ly S' = xs_cf ly S /\ errb_frame S S'.
Proof.
intros ly S S' md ns XP XM H.
destruct (rr_setsize_model ly S S' ns H) as (EF & XS & CAP & DAT & MAP & SZ).
split; [intros e He; rewrite XS in He; exact (XM e He)|].
split.
{ apply (xs_placed_cf_mono ly S S' XS); [|exact XP].
  intros z Hz. left. unfold errb_frame in EF. rewrite EF in Hz. exact Hz. }
split; [exact (rr_aledger_x_secs ly S S' md EF XS)|].
split; [exact CAP|]. split; [exact DAT|]. split; [exact MAP|]. split; [exact SZ|]. split; [exact XS | exact EF].
Qed.

(* ================================================================================================================ *)
(* 6. The layout step ly -> set_ly_sec ly (length (st_secs S)) a: every ly_sec the relation reads is at an index of a
   chunk, below length (st_secs S).  The cf twin of YFib.v (acells_lt .. ARm_layout_le) over WfP_cf / ARmcf.       *)
Lemma rr_chunk_lt : forall U pp cc bb S, WfP_cf U pp cc bb S -> forall k, In k (st_chunks S) ->
  match ck_beg k with PSec r _ => (r < length (st_secs S))%nat | _ => True end.
Proof.
intros U pp cc bb S W k Hk. pose proof (proj1 (Forall_forall _ _) (wfc_chunks _ _ _ _ _ W) k Hk) as [_ C].
destruct (ck_beg k) as [|o|r o|c p]; try exact I. destruct C as (_ & _ & sm & Hsm & _). eapply nth_error_lt. exact Hsm.
Qed.
Ltac rr_cell_tac := unfold cell_lt; cbn [c_at c_val]; split; cbn; try exact I.
Lemma rr_acells_lt : forall U pp cc bb ly S, WfP_cf U pp cc bb S -> Forall (cell_lt (length (st_secs S))) (acells B ly S).
Proof.
intros U pp cc bb ly S WF. set (n := length (st_secs S)).
pose proof (rr_chunk_lt U pp cc bb S WF) as chunk_lt.
assert (padd_lt : forall p d, match p with PSec r _ => (r < n)%nat | _ => True end -> match padd p d with PSec r _ => (r < n)%nat | _ => True end)
  by (intros p d H; destruct p; cbn; try exact I; exact H).
unfold acells.
apply Forall_app. split.
{   apply (proj2 (Forall_flat_map _ _ _)). apply Forall_forall. intros c _. unfold region_cells.
destruct (rg_mapped_user (reg S c) =? 0); repeat (apply Forall_cons; [rr_cell_tac|]); apply Forall_nil. }
apply Forall_app. split.
{   apply (proj2 (Forall_flat_map _ _ _)). apply Forall_forall. intros c _. unfold cache_cells.
destruct (st_cache_inited S).
+ repeat (apply Forall_cons; [rr_cell_tac|]).
apply Forall_forall. intros x Hx. apply in_map_iff in Hx as (io & <- & _). rr_cell_tac.
+ repeat (apply Forall_cons; [rr_cell_tac|]); apply Forall_nil. }
apply Forall_app. split.
{   apply (proj2 (Forall_flat_map _ _ _)). apply Forall_forall. intros k Hk. pose proof (chunk_lt k Hk) as LT. unfold chunk_cells.
apply Forall_app. split.
+ repeat (apply Forall_cons; [split; cbn [c_at c_val]; try exact I; repeat apply asec_lt_aoff; apply sptr_exp_lt; exact LT|]). apply Forall_nil.
+ destruct (ck_rz k =? kChunkHeaderSize); [apply Forall_nil|].
repeat (apply Forall_cons; [split; cbn [c_at c_val]; try exact I; repeat apply asec_lt_aoff; apply sptr_exp_lt; exact LT|]). apply Forall_nil. }
apply Forall_app. split.
{   unfold sec_cells. apply Forall_cons; [rr_cell_tac|]. apply Forall_cons; [rr_cell_tac|]. apply Forall_cons; [rr_cell_tac|]. apply Forall_app. split.
+ apply Forall_forall. intros x Hx. apply in_map_iff in Hx as ([i r] & <- & Hin). apply in_combine_r in Hin.
pose proof (proj1 (wsc_arr_chunks _ (wfc_secondary _ _ _ _ _ WF) r) Hin) as (k & Hk & Eb). pose proof (chunk_lt k Hk) as LT. rewrite Eb in LT.
rr_cell_tac. exact LT.
+ apply (proj2 (Forall_flat_map _ _ _)). apply Forall_forall. intros k Hk. pose proof (chunk_lt k Hk) as LT.
destruct (ck_beg k) as [|o|r o|c p]; try apply Forall_nil. repeat (apply Forall_cons; [rr_cell_tac; exact LT|]). apply Forall_nil. }
apply Forall_app. split.
{   unfold quar_cells. apply Forall_cons; [rr_cell_tac|]. apply Forall_cons; [rr_cell_tac|].
assert (ITEMS : forall k, In k (q_items S) -> match ck_hdr k with PSec r _ => (r < n)%nat | _ => True end).
{ intros k Hk. pose proof (proj1 (Forall_forall _ _) (wq_items _ (wfc_quarantine _ _ _ _ _ WF)) k Hk) as [Hin _]. unfold ck_hdr. apply padd_lt. exact (chunk_lt k Hin). }
assert (BATCH : forall bl, incl (flat_map b_items bl) (q_items S) -> Forall (cell_lt (length (st_secs S))) (batch_cells bl)).
{ induction bl as [|b t IH]; intros INC; [apply Forall_nil|]. cbn [batch_cells].
apply Forall_cons; [unfold cell_lt; cbn [c_at c_val]; split; [cbn; exact I|]; destruct t; cbn; exact I|].
apply Forall_cons; [rr_cell_tac|]. apply Forall_cons; [rr_cell_tac|]. apply Forall_app. split.
- apply Forall_forall. intros x Hx. apply in_map_iff in Hx as ([i k] & <- & Hin). apply in_combine_r in Hin.
unfold cell_lt; cbn [c_at c_val fst snd]. split; [cbn; exact I|]. apply sptr_exp_lt. apply ITEMS. apply INC. cbn. apply in_app_iff. left. exact Hin.
- apply IH. intros k Hk. apply INC. cbn. apply in_app_iff. right. exact Hk. }
assert (QC : forall root q, asec_lt n root -> (forall e, root <> ASh e) -> incl (flat_map b_items (qc_list q)) (q_items S) -> Forall (cell_lt (length (st_secs S))) (qc_cells root q)).
{ intros root q Hr Hsh INC. unfold qc_cells.
apply Forall_cons; [split; cbn [c_at c_val]; [exact Hr | cbn; exact I]|].
apply Forall_cons; [split; cbn [c_at c_val]; [apply asec_lt_aoff; exact Hr | destruct (qc_list q); cbn; exact I]|].
apply Forall_cons; [split; cbn [c_at c_val]; [apply asec_lt_aoff; exact Hr | destruct (rev (qc_list q)); cbn; exact I]|].
apply Forall_cons; [split; cbn [c_at c_val]; [apply asec_lt_aoff; exact Hr | cbn; exact I]|].
apply BATCH. exact INC. }
apply Forall_app. split; apply QC; cbn; try exact I; try (intros e E; discriminate E); unfold q_items, all_batches; intros k Hk; rewrite flat_map_app; apply in_app_iff; [left | right]; exact Hk. }
apply Forall_app. split.
{   unfold fs_cells. apply Forall_cons; [rr_cell_tac|]. apply Forall_cons; [rr_cell_tac|].
apply Forall_forall. intros x Hx. apply in_map_iff in Hx as ([i h] & <- & _). rr_cell_tac. }
apply Forall_app. split.
{   unfold depot_cells. repeat (apply Forall_cons; [rr_cell_tac|]). apply Forall_nil. }
apply Forall_app. split.
{   unfold ialloc_cells. repeat (apply Forall_cons; [rr_cell_tac|]); [destruct (st_internal_inited S); cbn; exact I | apply Forall_nil]. }
{   unfold thread_cells. apply Forall_cons; [rr_cell_tac | apply Forall_nil]. }
Qed.
Lemma rr_ajunk_lt : forall U pp cc bb ly S, WfP_cf U pp cc bb S ->
  Forall (fun r => asec_lt (length (st_secs S)) (fst r)) (as_junk B ly) ->
  Forall (fun r => asec_lt (length (st_secs S)) (fst r)) (ajunk_cf B ly S).
Proof.
intros U pp cc bb ly S WF JUNK. set (n := length (st_secs S)) in *. pose proof (rr_chunk_lt U pp cc bb S WF) as chunk_lt.
unfold ajunk_cf. apply Forall_cons; [cbn; exact I|]. apply Forall_cons; [cbn; exact I|].
apply Forall_app. split.
{ apply (proj2 (Forall_flat_map _ _ _)). apply Forall_forall. intros c _. unfold region_junk_cf, region_junk. repeat (apply Forall_cons; [cbn; exact I|]). apply Forall_nil. }
apply Forall_app. split.
{ apply (proj2 (Forall_flat_map _ _ _)). apply Forall_forall. intros c _. unfold cache_junk. apply Forall_cons; [cbn; exact I | apply Forall_nil]. }
apply Forall_app. split.
{ apply (proj2 (Forall_flat_map _ _ _)). apply Forall_forall. intros k Hk. pose proof (chunk_lt k Hk) as LT. unfold chunk_junk.
repeat (apply Forall_app; split); try (destruct (ck_rz k =? kChunkHeaderSize)); try (destruct (ck_state k)); try apply Forall_nil;
repeat (apply Forall_cons; [cbn [fst]; apply asec_lt_aoff; apply sptr_exp_lt; exact LT|]); apply Forall_nil. }
apply Forall_app. split.
{ unfold sec_junk. apply Forall_cons; [cbn; exact I|]. apply Forall_cons; [cbn; exact I|]. apply Forall_cons; [cbn; exact I|].
apply (proj2 (Forall_flat_map _ _ _)). apply Forall_forall. intros k Hk. pose proof (chunk_lt k Hk) as LT.
destruct (ck_beg k) as [|o|r o|c p]; try apply Forall_nil. apply Forall_cons; [cbn; exact LT | apply Forall_nil]. }
apply Forall_app. split.
{ unfold quar_junk. apply (proj2 (Forall_flat_map _ _ _)). apply Forall_forall. intros b _. unfold batch_junk. apply Forall_cons; [cbn; exact I | apply Forall_nil]. }
apply Forall_app. split.
{ unfold thread_junk. repeat (apply Forall_cons; [cbn; exact I|]). apply Forall_nil. }
apply Forall_app. split.
{ repeat (apply Forall_cons; [cbn; exact I|]). apply Forall_nil. }
{ exact JUNK. }
Qed.
Lemma rr_aareas_lt : forall U pp cc bb S, WfP_cf U pp cc bb S -> Forall (fun r => asec_lt (length (st_secs S)) (fst r)) (aareas S).
Proof.
intros U pp cc bb S WF. set (n := length (st_secs S)). pose proof (rr_chunk_lt U pp cc bb S WF) as chunk_lt.
unfold aareas. apply Forall_app. split.
{ apply (proj2 (Forall_flat_map _ _ _)). apply Forall_forall. intros c _. repeat (apply Forall_cons; [cbn; exact I|]). apply Forall_nil. }
apply Forall_app. split. { apply Forall_cons; [cbn; exact I | apply Forall_nil]. }
apply Forall_app. split.
{ apply (proj2 (Forall_flat_map _ _ _)). apply Forall_forall. intros k Hk. pose proof (chunk_lt k Hk) as LT.
destruct (ck_beg k) as [|o|r o|c p]; try apply Forall_nil. apply Forall_cons; [cbn; exact LT | apply Forall_nil]. }
repeat (apply Forall_cons; [cbn; exact I|]). apply Forall_nil.
Qed.
Lemma rr_aclient_lt : forall U pp cc bb S, WfP_cf U pp cc bb S -> Forall (fun r => asec_lt (length (st_secs S)) (fst r)) (aclient S).
Proof.
intros U pp cc bb S WF. set (n := length (st_secs S)). pose proof (rr_chunk_lt U pp cc bb S WF) as chunk_lt.
assert (padd_lt : forall p d, match p with PSec r _ => (r < n)%nat | _ => True end -> match padd p d with PSec r _ => (r < n)%nat | _ => True end)
  by (intros p d H; destruct p; cbn; try exact I; exact H).
unfold aclient. apply Forall_app. split.
{ apply (proj2 (Forall_flat_map _ _ _)). apply Forall_forall. intros k Hk. pose proof (chunk_lt k Hk) as LT. unfold chunk_user.
destruct (ck_state k); [|apply Forall_nil]. apply Forall_cons; [|apply Forall_nil]. cbn [fst]. apply sptr_exp_lt. unfold ck_user. apply padd_lt. exact LT. }
apply Forall_app. split; apply Forall_forall; intros x Hx; apply in_map_iff in Hx as (cq & <- & _); cbn; exact I.
Qed.
Lemma rr_ashadow_ly : forall U pp cc bb ly ly' S, WfP_cf U pp cc bb S -> layout_le (length (st_secs S)) ly ly' ->
  forall g, ashadow B ly' S g = ashadow B ly S g.
Proof.
intros U pp cc bb ly ly' S WF LE g. pose proof LE as (E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8 & E9 & E10 & E11 & E12 & E13 & E14 & ED & E15). unfold ashadow.
assert (CB : forall k, In k (st_chunks S) -> ck_base B ly' k = ck_base B ly k).
{ intros k Hk. unfold ck_base. apply (sptr_addr_le B ly ly' (length (st_secs S))); [exact LE|]. exact (rr_chunk_lt _ _ _ _ S WF k Hk). }
assert (FC : find_chunk_at B ly' (st_chunks S) g = find_chunk_at B ly (st_chunks S) g).
{ assert (H : forall l, incl l (st_chunks S) -> find_chunk_at B ly' l g = find_chunk_at B ly l g).
{ induction l as [|k t IH]; intros INC; [reflexivity|]. cbn [find_chunk_at]. rewrite (CB k (INC k (or_introl eq_refl))).
rewrite (IH (fun x Hx => INC x (or_intror Hx))). reflexivity. }
apply H. intros k Hk. exact Hk. }
assert (FIN : forall l k, find_chunk_at B ly l g = Some k -> In k l).
{ induction l as [|k0 t IH]; intros k Hf; [discriminate Hf|]. cbn [find_chunk_at] in Hf.
destruct ((ck_base B ly k0 <=? g) && (g <? ck_base B ly k0 + ck_extent k0)); [injection Hf as <-; left; reflexivity | right; exact (IH k Hf)]. }
rewrite FC. destruct (find_chunk_at B ly (st_chunks S) g) as [k|] eqn:Hf; [rewrite (CB k (FIN _ k Hf)); reflexivity|].
assert (FP : fa_poison_ranges ly' S = fa_poison_ranges ly S).
{ unfold fa_poison_ranges. f_equal.
- unfold region_base, fa_base. rewrite E2. reflexivity.
- pose proof (sec_extents_le_cf ly ly' S _ _ _ _ LE WF) as SE. unfold sec_extents in SE. exact SE. }
rewrite FP. reflexivity.
Qed.

Fixpoint rr_nosec (e : aexp) : bool := match e with ASec _ _ => false | ASh e' => rr_nosec e' | _ => true end.
Lemma rr_nosec_lt : forall n e, rr_nosec e = true -> asec_lt n e.
Proof. intros n e. induction e; cbn; intros H; try exact I; try discriminate H; exact (IHe H). Qed.
Definition rr_cell_nosec (c : acell) : bool :=
  rr_nosec (c_at c) && match c_val c with AV e => rr_nosec e | AVmask _ _ => true end.
Lemma rr_nosec_cells : forall n l, forallb rr_cell_nosec l = true -> Forall (cell_lt n) l.
Proof.
intros n l H. apply Forall_forall. intros c Hc. pose proof (proj1 (forallb_forall _ _) H c Hc) as X.
unfold rr_cell_nosec in X. apply andb_prop in X as [X1 X2]. split; [exact (rr_nosec_lt n _ X1)|].
destruct (c_val c); [exact (rr_nosec_lt n _ X2) | exact I].
Qed.
Lemma rr_const_nosec : forall ly, forallb rr_cell_nosec (Tfib_const ly) = true.
Proof. intros ly. vm_compute. reflexivity. Qed.

(* The errbuf data address reads ly_sec at the current capacity entry, an index below length (st_secs S). *)
Lemma rr_data_layout : forall ly ly' S, layout_le (length (st_secs S)) ly ly' -> YG0ncf.errb_data_cf ly' S = YG0ncf.errb_data_cf ly S.
Proof.
intros ly ly' S LE. unfold YG0ncf.errb_data_cf. destruct (last_cap_idx (st_secs S) 0 None) as [j|] eqn:E; [|reflexivity].
pose proof (cfx_last_cap_idx_lt _ 0 None j E ltac:(intros k Hk; discriminate Hk)) as Hj.
destruct LE as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Esec).
rewrite (Esec j ltac:(lia)). reflexivity.
Qed.

Lemma rr_ARmcf_layout : forall ly ly' S Hp rd, TfibSyms B -> ARmcf B ly S Hp rd ->
  layout_le (length (st_secs S)) ly ly' -> layout_ok ly' -> xs_placed_cf ly' S -> ARmcf B ly' S Hp rd.
Proof.
intros ly ly' S Hp rd TS M LE LO' XP.
pose proof LE as (E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8 & E9 & E10 & E11 & E12 & E13 & E14 & ED & EI & E15).
assert (CONST : as_const B ly' = as_const B ly) by (rewrite !(ts_const _ TS); reflexivity).
assert (CONSTlt : Forall (cell_lt (length (st_secs S))) (as_const B ly)).
{ rewrite (ts_const _ TS). apply rr_nosec_cells. apply rr_const_nosec. }
assert (JUNK : as_junk B ly' = as_junk B ly) by exact (ts_junk_ly _ TS ly ly').
assert (JUNKlt : Forall (fun r => asec_lt (length (st_secs S)) (fst r)) (as_junk B ly)).
{ apply Forall_forall. intros r Hr. destruct (ts_junk _ TS ly r Hr) as (z & Ez & _). rewrite Ez. exact I. }
pose proof M as MM. destruct MM as [M1 M2 M3 M4 M5 M6 M7 M8 M9 M10 M11 M12 M13 M14 M15 M16 M17 M18 M19 M20 M21 M22 M23 M24 M25 M26].
constructor.
- exact M1.
- exact M2.
- exact M3.
- exact LO'.
- unfold sec_placed in *. rewrite (sec_extents_le_cf ly ly' S _ _ _ _ LE M1). rewrite (cfx_static_layout _ ly ly' LE). exact M5.
- rewrite CONST. exact (Forall_cell_holds_le B ly ly' _ LE rd _ CONSTlt M6).
- rewrite CONST. apply Forall_forall. intros c Hc k Hk. pose proof (proj1 (Forall_forall _ _) M7 c Hc k Hk) as O.
  pose proof (proj1 (Forall_forall _ _) CONSTlt c Hc) as [Ha _]. rewrite (aeval_le B ly ly' _ LE _ Ha).
  unfold owned_core in *. replace (core_extents ly') with (core_extents ly); [exact O|].
  unfold core_extents. rewrite E3, E4, E7, E8, E5, ED. reflexivity.
- assert (AC : acells_cf B ly' S = acells_cf B ly S) by (unfold acells_cf, depot_cells; rewrite E13; reflexivity).
  rewrite AC. apply (Forall_cell_holds_le B ly ly' _ LE rd); [|exact M8].
  exact (incl_Forall (acells_cf_incl B ly S) (rr_acells_lt _ _ _ _ ly S M1)).
- intros c i v Hc Hi Hv. unfold fa_base. rewrite E2. exact (M9 c i v Hc Hi Hv).
- intros cid pos Hc Hp'. unfold flag_addr. rewrite E6. exact (M10 cid pos Hc Hp').
- destruct M11 as (heads & links & D1 & D2 & D3). exists heads, links.
  replace (depot_traces ly' S) with (depot_traces ly S) by (unfold depot_traces; rewrite E13; reflexivity). rewrite E7.
  exact (conj D1 (conj D2 D3)).
- intros g v Hg Hs. rewrite (rr_ashadow_ly _ _ _ _ ly ly' S M1 LE g) in Hs. exact (M12 g v Hg Hs).
- unfold zshadow_ok in *. replace (zero_shadow_ranges B ly') with (zero_shadow_ranges B ly); [exact M13|].
  unfold zero_shadow_ranges. rewrite E10, E11. reflexivity.
- assert (AJ : ajunk_cf B ly' S = ajunk_cf B ly S) by (unfold ajunk_cf; rewrite JUNK; reflexivity). rewrite AJ.
  exact (Forall_range_vis_le B ly ly' _ LE rd _ (rr_ajunk_lt _ _ _ _ ly S M1 JUNKlt) M14).
- exact (Forall_range_vis_le B ly ly' _ LE rd _ (rr_aareas_lt _ _ _ _ S M1) M15).
- exact (Forall_range_vis_le B ly ly' _ LE rd _ (rr_aclient_lt _ _ _ _ S M1) M16).
- apply Forall_forall. intros r Hr i Hi. pose proof (proj1 (Forall_forall _ _) M17 r Hr i Hi) as X.
  unfold ialloc_zero in Hr. cbn in Hr. destruct Hr as [<-|[<-|[]]]; cbn in X |- *; exact X.
- rewrite E12. exact M18.
- rewrite EI. exact M19.
- eapply Forall_impl; [|exact M20]. intros p (k & Hk & Hst & Hp0 & Hn). exists k.
  split; [exact Hk|]. split; [exact Hst|]. split; [|exact Hn].
  rewrite Hp0. unfold ck_user. symmetry. apply (sptr_addr_le B ly ly' (length (st_secs S))); [exact LE|].
  pose proof (rr_chunk_lt _ _ _ _ S M1 k Hk) as LT. destruct (ck_beg k); cbn; try exact I; exact LT.
- exact XP.
- destruct M22 as [X1 X2]. split; [|exact X2]. intros c Hc. pose proof (X1 c Hc) as C.
  unfold cell_holds in C |- *. cbn [z1 c1 c_at c_val c_w aoff aeval] in C |- *. rewrite E2. exact C.
- unfold YG0ncf.errb_cells_cf in *. rewrite (rr_data_layout ly ly' S LE). exact M23.
- exact M24.
- (* field round 3: Printf's two cells sit at fixed addresses (ANum), which no layout moves *)
  destruct M25 as [P1 P2]. unfold cell_holds in P1, P2. unfold pf_cells_cf, cell_holds.
  cbn [z8 c8 c_at c_val c_w aeval] in P1, P2 |- *. split; [exact P1 | exact P2].
- exact M26.
Qed.

(* ================================================================================================================ *)
(* 7. The memory the relation reads.  Every address ARmcf reads (a cell, a visibility range, a shadow byte) lies in
   rr_zf: a static extent, a secondary extent, or the shadow band.  An mmap'd errbuf (the new one, or the old one
   being unmapped) lies in none of them, so the machine may do what it likes with its bytes.                      *)
Definition rr_zf (ly : alayout) (S : astate) (x : Z) : Prop :=
  Exists (in_zr x) (static_extents ly ++ sec_extents ly S) \/ kLowShadowBeg <= x < kHighMemBeg.

Lemma rr_zf_static : forall ly S e x, In e (static_extents ly) -> in_zr x e -> rr_zf ly S x.
Proof. intros ly S e x He Hx. left. apply Exists_exists. exists e. split; [apply in_or_app; left; exact He | exact Hx]. Qed.
Lemma rr_zf_sec : forall ly S e x, In e (sec_extents ly S) -> in_zr x e -> rr_zf ly S x.
Proof. intros ly S e x He Hx. left. apply Exists_exists. exists e. split; [apply in_or_app; right; exact He | exact Hx]. Qed.
Lemma rr_zf_band : forall ly S x, kLowShadowBeg <= x < kHighMemBeg -> rr_zf ly S x.
Proof. intros ly S x H. right. exact H. Qed.
Lemma rr_owned_static : forall ly e, In e (owned_extents ly) -> In e (static_extents ly).
Proof. intros ly e He. unfold static_extents. apply in_or_app. left. exact He. Qed.
Lemma rr_img_static : forall ly, In (ly_img ly) (static_extents ly).
Proof. intros ly. unfold static_extents. apply in_or_app. right. right. left. reflexivity. Qed.

Lemma rr_zf_owned : forall ly S Hp rd x, ARmcf B ly S Hp rd -> aowned B ly S x -> rr_zf ly S x.
Proof.
intros ly S Hp rd x M [O _].
destruct O as [O|[O|[O|[O|O]]]].
- apply Exists_exists in O as (r & Hr & Hx).
  pose proof (proj1 (Forall_forall _ _) (amc_static_img _ _ _ _ _ M) r (in_or_app _ _ _ (or_introl Hr))) as [Z1 Z2].
  apply (rr_zf_static ly S (ly_img ly)); [apply rr_img_static | unfold in_zr in *; lia].
- apply Exists_exists in O as (e & He & Hx). exact (rr_zf_static ly S e x (rr_owned_static ly e He) Hx).
- apply (rr_zf_static ly S (ly_C ly, 256)); [apply rr_owned_static; unfold owned_extents; cbn; tauto | exact O].
- apply Exists_exists in O as (e & He & Hx). exact (rr_zf_sec ly S e x He Hx).
- pose proof (owned_shadow_bound_cf B ly S Hp rd x M O) as [X1 X2]. apply rr_zf_band. unfold SHADOW_OFF, kLowShadowBeg in *. lia.
Qed.

Lemma rr_zf_range : forall ly S Hp rd x, ARmcf B ly S Hp rd -> rr_zf ly S x -> 0 <= x < 2 ^ 64.
Proof.
intros ly S Hp rd x M [Z|Z]; [|unfold kLowShadowBeg, kHighMemBeg in *; lia].
apply Exists_exists in Z as (e & He & Hx). unfold in_zr in Hx.
pose proof (proj1 (Forall_forall _ _) (owned_shadow_ranges_cf B ly S Hp rd M) e ltac:(rewrite app_assoc; apply in_or_app; left; exact He)) as (K1 & K2 & K3).
unfold kHighMemEnd in K3. lia.
Qed.

(* An extent apart from the static / secondary extents and in the application range misses rr_zf. *)
Lemma rr_zf_apart : forall ly S lo len x, in_app lo len -> Forall (zdisjoint (lo, len)) (static_extents ly) ->
  Forall (zdisjoint (lo, len)) (sec_extents ly S) -> rr_zf ly S x -> ~ (lo <= x < lo + len).
Proof.
intros ly S lo len x [A0 A1] FS FC [Z|Z] Hx.
- apply Exists_exists in Z as (e & He & Hin). unfold in_zr in Hin. apply in_app_iff in He as [He|He].
  + pose proof (proj1 (Forall_forall _ _) FS e He) as D. unfold zdisjoint in D. cbn [fst snd] in D. lia.
  + pose proof (proj1 (Forall_forall _ _) FC e He) as D. unfold zdisjoint in D. cbn [fst snd] in D. lia.
- unfold kLowShadowBeg, kHighMemBeg in *. lia.
Qed.

Lemma rr_zf_chunk : forall ly S Hp rd k x, ARmcf B ly S Hp rd -> In k (st_chunks S) ->
  ck_base B ly k <= x < ck_base B ly k + ck_extent k -> rr_zf ly S x.
Proof.
intros ly S Hp rd k x M Hk Hx. destruct (extent_zone_cf B ly S Hp rd k M Hk) as [[P1 P2]|(m & len & Hin & E1 & E2)].
- apply (rr_zf_static ly S (ly_prim ly, kPrimResvSize)); [apply rr_owned_static; unfold owned_extents; cbn; tauto | unfold in_zr; cbn [fst snd]; lia].
- apply (rr_zf_sec ly S (m, len) x Hin). unfold in_zr; cbn [fst snd]. unfold kPage in *. lia.
Qed.

Lemma rr_zf_shadow : forall ly S lo len j, in_app lo len -> 0 <= j < len / 8 -> rr_zf ly S (shadow_addr lo + j).
Proof.
intros ly S lo len j HA Hj.
assert (E : shadow_addr lo + j = shadow_addr (lo + 8 * j)).
{ unfold shadow_addr. replace (lo + 8 * j) with (lo + j * 8) by lia. rewrite Z.div_add by lia. lia. }
rewrite E. apply rr_zf_band. pose proof (Z.mul_div_le len 8 ltac:(lia)) as ML.
pose proof (shadow_addr_in_band lo len (8 * j) HA ltac:(lia)) as BD.
unfold in_band_rw, kLowShadowBeg, kLowShadowEnd, kHighShadowBeg, kHighShadowEnd, kHighMemBeg in *. lia.
Qed.

(* Every byte of the visibility ranges is in rr_zf. *)
Lemma rr_vis_zf : forall ly S Hp rd, TfibSyms B -> img_cover ly -> ARmcf B ly S Hp rd ->
  forall r i, In r (ajunk_cf B ly S ++ aareas S ++ aclient S) -> 0 <= i < snd r -> rr_zf ly S (aeval B ly (fst r) + i).
Proof.
intros ly S Hp rd TS IC M r i Hr Hi.
pose proof (amc_layout _ _ _ _ _ M) as LO. pose proof (amc_wf _ _ _ _ _ M) as WF.
pose proof (lo_space_in _ LO) as [SP1 SP2].
assert (EA : forall e d, match e with ASh _ => False | _ => True end -> aeval B ly (aoff e d) = aeval B ly e + d).
{ intros e d He. apply aeval_aoff. intros e' ->. exact He. }
assert (ZE : forall e x, In e (owned_extents ly) -> fst e <= x < fst e + snd e -> rr_zf ly S x).
{ intros e x He Hx. exact (rr_zf_static ly S e x (rr_owned_static ly e He) Hx). }
assert (ZT : forall x, ly_T ly <= x < ly_T ly + kThreadObjSize -> rr_zf ly S x)
  by (intros x Hx; apply (ZE (ly_T ly, kThreadObjSize)); [unfold owned_extents; cbn; tauto | exact Hx]).
assert (ZQ : forall x, ly_Q ly <= x < ly_Q ly + kPtrArrayResv -> rr_zf ly S x)
  by (intros x Hx; apply (ZE (ly_Q ly, kPtrArrayResv)); [unfold owned_extents; cbn; tauto | exact Hx]).
assert (ZF : forall x, ly_F ly <= x < ly_F ly + kFakeStackSize -> rr_zf ly S x)
  by (intros x Hx; apply (ZE (ly_F ly, kFakeStackSize)); [unfold owned_extents; cbn; tauto | exact Hx]).
assert (ZN : forall x, ly_NB ly <= x < ly_NB ly + kNodesBlockSize -> rr_zf ly S x)
  by (intros x Hx; apply (ZE (ly_NB ly, kNodesBlockSize)); [unfold owned_extents; cbn; tauto | exact Hx]).
assert (ZB : forall x, ly_SB ly <= x < ly_SB ly + kStoreBlockSize -> rr_zf ly S x)
  by (intros x Hx; apply (ZE (ly_SB ly, kStoreBlockSize)); [unfold owned_extents; cbn; tauto | exact Hx]).
assert (ZP : forall x, ly_prim ly <= x < ly_prim ly + kPrimResvSize -> rr_zf ly S x)
  by (intros x Hx; apply (ZE (ly_prim ly, kPrimResvSize)); [unfold owned_extents; cbn; tauto | exact Hx]).
assert (ZRI : forall x, ly_space ly + kRegionInfoOff <= x < ly_space ly + kRegionInfoOff + 4096 -> rr_zf ly S x)
  by (intros x Hx; apply ZP; unfold kRegionInfoOff, kSpaceSize in *; lia).
assert (ZAR : forall r0 x, In r0 (asyms_areas B) -> fst r0 <= x < fst r0 + snd r0 -> rr_zf ly S x).
{ intros r0 x Hr0 Hx. apply (rr_zf_owned ly S Hp rd x M). eapply own_area_cf; [exact M | exact Hr0 | exact Hx]. }
pose proof (proj1 (Forall_forall _ _) (lo_app _ LO) (ly_F ly, kFakeStackSize) ltac:(unfold owned_extents; cbn; tauto)) as FAPP.
cbn [fst snd] in FAPP.
rewrite !in_app_iff in Hr. destruct Hr as [Hr|[Hr|Hr]].
- unfold ajunk_cf in Hr. destruct Hr as [E|[E|Hr]].
  + subst r. cbn [fst snd aeval] in Hi |- *. apply ZRI. lia.
  + subst r. cbn [snd] in Hi. lia.
  + rewrite !in_app_iff in Hr. destruct Hr as [Hr|[Hr|[Hr|[Hr|[Hr|[Hr|[Hr|Hr]]]]]]].
    * apply in_flat_map in Hr as (c & Hc & Hr). apply zseq_In in Hc. unfold region_junk_cf, region_junk in Hr. cbv zeta in Hr.
      destruct Hr as [<-|[<-|[<-|[]]]]; cbn [fst snd] in Hi |- *; rewrite EA by exact I; cbn [aeval]; apply ZRI; lia.
    * apply in_flat_map in Hr as (c & Hc & Hr). apply zseq_In in Hc. unfold cache_junk in Hr. destruct Hr as [<-|[]].
      cbn [fst snd aeval] in Hi |- *.
      assert (N0 : 0 <= (if st_cache_inited S then Z.of_nat (length (pc_chunks (cache S c))) else 0))
        by (destruct (st_cache_inited S); lia).
      apply ZT. unfold t_cache, kThreadObjSize in *. lia.
    * apply in_flat_map in Hr as (k & Hk & Hr). apply (rr_zf_chunk ly S Hp rd k _ M Hk).
      pose proof (chunk_facts_cf B ly S Hp rd k M Hk) as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & GG).
      pose proof (req_size_bounds (ck_req k) ltac:(lia)) as (Q1 & Q2 & Q3).
      assert (SP : match sptr_exp (ck_beg k) with ASh _ => False | _ => True end) by (destruct (ck_beg k); exact I).
      assert (E0 : aeval B ly (sptr_exp (ck_beg k)) = ck_base B ly k) by reflexivity.
      unfold chunk_junk in Hr. cbv zeta in Hr. rewrite !in_app_iff in Hr. unfold ck_n in *.
      destruct Hr as [Hr|[[<-|[]]|[Hr|[<-|[]]]]].
      -- destruct (Z.eqb_spec (ck_rz k) kChunkHeaderSize); [destruct Hr|]. destruct Hr as [<-|[]].
         cbn [fst snd] in Hi |- *. rewrite EA by exact SP. rewrite E0. unfold kChunkHeaderSize in *. lia.
      -- cbn [fst snd] in Hi |- *. rewrite EA by exact SP. rewrite E0. lia.
      -- destruct (ck_state k); [destruct Hr|]. destruct Hr as [<-|[]]. cbn [fst snd] in Hi |- *. rewrite EA by exact SP. rewrite E0. lia.
      -- cbn [fst snd] in Hi |- *. rewrite EA by exact SP. rewrite E0. lia.
    * unfold sec_junk in Hr. destruct Hr as [<-|[<-|[<-|Hr]]]; cbn [fst snd aeval] in Hi |- *.
      -- apply (ZAR (as_inst B, 3632)); [cbn; tauto | cbn [fst snd]; unfold o_sec_sorted in *; lia].
      -- apply (ZAR (as_inst B, 3632)); [cbn; tauto | cbn [fst snd]; unfold o_sec_stats, o_sec_mutex in *; lia].
      -- pose proof (wsc_reserved _ (wfc_secondary _ _ _ _ _ WF)) as R1. apply ZQ.
         unfold kPtrArrayEntriesPerCommit, kPtrArrayResv in *. lia.
      -- apply in_flat_map in Hr as (k & Hk & Hr). pose proof (chunk_facts_cf B ly S Hp rd k M Hk) as (_ & _ & _ & _ & _ & _ & G7 & _ & GG).
         destruct (ck_beg k) as [|o|r' o|c p]; try solve [destruct Hr]. destruct Hr as [<-|[]]. cbn [fst snd aeval] in Hi |- *.
         destruct GG as (-> & Gp & Gbase & Gext & Gin & _). apply (rr_zf_sec ly S _ _ Gin). unfold in_zr; cbn [fst snd].
         pose proof (sec_map_size_page (ck_req k) ltac:(lia)). unfold kPage in *. lia.
    * unfold quar_junk in Hr. apply in_flat_map in Hr as (b & Hb & Hr). unfold batch_junk in Hr. destruct Hr as [<-|[]].
      cbn [fst snd] in Hi |- *. unfold batch_exp in *. rewrite EA by exact I. cbn [aeval].
      apply (rr_zf_owned ly S Hp rd _ M). eapply own_batch_cf; [exact M | exact Hb |].
      pose proof (Zle_0_nat (length (b_items b))). unfold kBatchBytes in *. lia.
    * unfold thread_junk in Hr. destruct Hr as [<-|[<-|[<-|[<-|[]]]]]; cbn [fst snd aeval] in Hi |- *; apply ZT;
      unfold t_cache, t_cache_stats, t_stats, t_unwinding, kThreadObjSize in *; lia.
    * destruct Hr as [<-|[<-|[<-|[<-|[]]]]]; cbn [fst snd aeval] in Hi |- *.
      -- apply (ZAR (as_oom_byte B, 1)); [cbn; tauto | cbn [fst snd]; lia].
      -- apply (ZAR (as_depot B, 4 * 2 ^ 20 + 32)); [cbn; tauto | cbn [fst snd]; unfold d_nuniq in *; lia].
      -- apply (ZAR (as_store B, 32)); [cbn; tauto | cbn [fst snd]; lia].
      -- apply (ZAR (as_store B, 32)); [cbn; tauto | cbn [fst snd]; lia].
    * destruct (ts_junk _ TS ly r Hr) as (z & Ez & Z1 & Z2). rewrite Ez. cbn [aeval]. destruct IC as [IC1 IC2].
      apply (rr_zf_static ly S (ly_img ly)); [apply rr_img_static | unfold in_zr, TFIB_IMG_LO, TFIB_IMG_END in *; lia].
- unfold aareas in Hr. rewrite !in_app_iff in Hr. destruct Hr as [Hr|[[<-|[]]|[Hr|Hr]]].
  + apply in_flat_map in Hr as (c & Hc & Hr). apply zseq_In in Hc.
    pose proof (wfc_classes _ _ _ _ _ WF c ltac:(lia)) as CL. pose proof (wrc_mapped_bound _ _ _ _ _ _ CL) as MB.
    pose proof (wrc_fa_bound _ _ _ _ _ _ CL) as FB.
    assert (RO : region_off c = c * 2 ^ 32) by (unfold region_off; apply Z.shiftl_mul_pow2; lia).
    destruct Hr as [<-|[<-|[]]]; cbn [fst snd aeval] in Hi |- *; rewrite RO; apply ZP;
    unfold kFreeArrayOffset, kFreeArrayMax, kSpaceSize, kPrimResvSize in *; lia.
  + cbn [fst snd aeval] in Hi |- *. pose proof (wsc_reserved _ (wfc_secondary _ _ _ _ _ WF)) as R1. apply ZQ.
    unfold kPtrArrayEntriesPerCommit, kPtrArrayResv in *. lia.
  + apply in_flat_map in Hr as (k & Hk & Hr). pose proof (chunk_facts_cf B ly S Hp rd k M Hk) as (_ & _ & _ & _ & _ & _ & G7 & _ & GG).
    destruct (ck_beg k) as [|o|r' o|c p]; try solve [destruct Hr]. destruct Hr as [<-|[]]. cbn [fst snd aeval] in Hi |- *.
    destruct GG as (-> & Gp & Gbase & Gext & Gin & _). apply (rr_zf_sec ly S _ _ Gin). unfold in_zr; cbn [fst snd]. lia.
  + destruct Hr as [<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]; cbn [fst snd aeval] in Hi |- *.
    * apply ZF. lia.
    * apply ZN. lia.
    * apply ZB. lia.
    * apply ZT. lia.
    * apply ZRI. lia.
    * apply (rr_zf_shadow ly S (ly_F ly + kFakeFramesOff) (kFakeStackSize - kFakeFramesOff) i); [|exact Hi].
      apply (in_app_sub (ly_F ly) kFakeStackSize); [exact FAPP | unfold kFakeFramesOff; lia | unfold kFakeStackSize, kFakeFramesOff; lia | lia].
- unfold aclient in Hr. rewrite !in_app_iff in Hr. destruct Hr as [Hr|[Hr|Hr]].
  + apply in_flat_map in Hr as (k & Hk & Hr). unfold chunk_user in Hr.
    pose proof (chunk_facts_cf B ly S Hp rd k M Hk) as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & GG).
    pose proof (req_size_bounds (ck_req k) ltac:(lia)) as (Q1 & Q2 & Q3).
    destruct (ck_state k); [|destruct Hr]. destruct Hr as [<-|[]]. cbn [fst snd] in Hi |- *.
    apply (rr_zf_chunk ly S Hp rd k _ M Hk). change (aeval B ly (sptr_exp (ck_user k))) with (sptr_addr B ly (ck_user k)).
    rewrite G4. unfold ck_n in *. lia.
  + apply in_map_iff in Hr as ([cid pos] & <- & Hcp). cbn [fst snd aeval] in Hi |- *.
    pose proof (frame_facts_cf B ly S Hp rd cid pos M Hcp) as (Fc & Fp & F1 & F2 & F3 & F4 & F5 & _).
    apply ZF. unfold kFakeFramesOff in *. lia.
  + apply in_map_iff in Hr as ([cid pos] & <- & Hcp). cbn [fst snd aeval] in Hi |- *.
    pose proof (frame_facts_cf B ly S Hp rd cid pos M Hcp) as (Fc & Fp & F1 & F2 & F3 & F4 & F5 & F6 & F7 & _).
    apply (rr_zf_shadow ly S (ly_F ly + fs_frame_off cid pos) (fs_frame_bytes cid) i); [|exact Hi].
    apply (in_app_sub (ly_F ly) kFakeStackSize); [exact FAPP | unfold kFakeFramesOff in *; lia | lia | lia].
Qed.

(* ================================================================================================================ *)
(* 8. The ledger, the model's well-formedness and the shadow across the (re)map.                                     *)
Lemma rr_pairwise_in {X : Type} (R : X -> X -> Prop) : forall l x y, pairwise R l -> In x l -> In y l -> x <> y -> R x y \/ R y x.
Proof.
induction l as [|h t IH]; intros x y P Hx Hy Hne; [destruct Hx|]. cbn [pairwise] in P. destruct P as [F P].
destruct Hx as [<-|Hx]; destruct Hy as [<-|Hy].
- exfalso. exact (Hne eq_refl).
- left. exact (proj1 (Forall_forall _ _) F y Hy).
- right. exact (proj1 (Forall_forall _ _) F x Hx).
- exact (IH x y P Hx Hy Hne).
Qed.

Lemma rr_w64_ne : forall x y, 0 <= x < 2 ^ 64 -> 0 <= y < 2 ^ 64 -> x <> y -> w64 x <> w64 y.
Proof. intros x y Hx Hy Hne E. apply Hne. exact (cfxm_w64_inj x y Hx Hy E). Qed.

Lemma rr_cap_remap : forall S S1 ncap, 0 <= ncap ->
  st_secs S1 = map cfx_retire (st_secs S) ++ [mkSec ncap ERRB_CAP_TAG false] -> errb_cap_cf S1 = ncap.
Proof.
intros S S1 ncap Hn Es. unfold errb_cap_cf, errb_e. rewrite Es, filter_app, cfx_filter_retired. cbn. lia.
Qed.

Lemma rr_data_remap : forall ly S S1 ncap,
  st_secs S1 = map cfx_retire (st_secs S) ++ [mkSec ncap ERRB_CAP_TAG false] ->
  YG0ncf.errb_data_cf ly S1 = ly_sec ly (length (st_secs S)).
Proof.
intros ly S S1 ncap Es. unfold YG0ncf.errb_data_cf. rewrite Es, cfx_last_cap_idx_app.
cbn [last_cap_idx]. rewrite length_map. reflexivity.
Qed.

Lemma rr_mapped_remap : forall S S1 ncap,
  st_secs S1 = map cfx_retire (st_secs S) ++ [mkSec ncap ERRB_CAP_TAG false] -> errb_mapped_cf S1 = true.
Proof. intros S S1 ncap Es. unfold errb_mapped_cf. rewrite Es, existsb_app. cbn. apply orb_true_r. Qed.

Lemma rr_xs_unmapped : forall ly S, errb_mapped_cf S = false -> xs_cf ly S = [].
Proof.
intros ly S H. unfold xs_cf. destruct (last_cap_idx (st_secs S) 0 None) as [i|] eqn:E; [|reflexivity]. exfalso.
assert (G : forall l j acc k, last_cap_idx l j acc = Some k -> acc = None -> existsb is_errb_cap l = true).
{ induction l as [|sm t IH]; intros j acc k Hl Ha; cbn [last_cap_idx existsb] in *; [congruence|].
  destruct (is_errb_cap sm) eqn:Ec; [reflexivity|]. cbn [orb]. exact (IH _ _ _ Hl Ha). }
unfold errb_mapped_cf in H. rewrite (G _ _ _ _ E eq_refl) in H. discriminate H.
Qed.

Lemma rr_xs_mapped : forall ly S, errb_mapped_cf S = true ->
  xs_cf ly S = [(YG0ncf.errb_data_cf ly S, errb_cap_cf S)].
Proof.
intros ly S H. rewrite errb_data_xs. destruct (last_cap_idx (st_secs S) 0 None) eqn:E; [reflexivity|].
destruct (rr_last_cap_none _ _ _ E) as [_ F]. unfold errb_mapped_cf in H. rewrite rr_existsb_filter, F in H. discriminate H.
Qed.

Ltac rr_mproj :=
repeat first [ rewrite YK0g.m_vmmaps_with_vm_backing | rewrite YK0g.m_vm_lazy_with_vm_backing
| rewrite YK0g.m_vmmaps_with_vmmaps | rewrite YK0g.m_vm_lazy_with_vmmaps ].

Lemma rr_amwf_mmap : forall md a n, amwf md -> 0 <= a -> 0 < n -> a + n < 2 ^ 64 ->
  (forall q, In q (vm_maps (m_vmmaps md)) -> a + n <= bv_unsigned (fst q) \/ bv_unsigned (fst q) + bv_unsigned (snd q) <= a) ->
  amwf (mmap_model (w64 a) (w64 n) md).
Proof.
intros md a n [(W1 & W2 & W3 & PW & ISP) NE] Ha Hn Han RF.
assert (Ua : bv_unsigned (w64 a) = a) by (apply w64_unsigned; lia).
assert (Un : bv_unsigned (w64 n) = n) by (apply w64_unsigned; lia).
unfold amwf, amwf_ivs, mmap_model. rr_mproj. cbn [vm_maps vm_noaccess].
split; [split; [|split; [|split; [|split]]]|].
- intros q [<-|Hq]; [cbn [fst snd]; rewrite Ua, Un; lia | exact (W1 q Hq)].
- exact W2.
- exact W3.
- cbn [pairwise]. split; [|exact PW]. apply Forall_forall. intros q Hq. cbn [fst snd]. rewrite Ua, Un. exact (RF q Hq).
- exact ISP.
- intros q [<-|Hq]; [cbn [snd]; rewrite Un; lia | exact (NE q Hq)].
Qed.

Lemma rr_munmap_parts : forall (a n : word) md,
  vm_reserved (m_vmmaps (munmap_model a n md)) = vm_reserved (m_vmmaps md) /\
  vm_limit (m_vmmaps (munmap_model a n md)) = vm_limit (m_vmmaps md) /\
  vm_init_sp (m_vmmaps (munmap_model a n md)) = vm_init_sp (m_vmmaps md) /\
  vm_noaccess (m_vmmaps (munmap_model a n md)) = maps_subtract (vm_noaccess (m_vmmaps md)) (bv_unsigned a) (bv_unsigned a + bv_unsigned n).
Proof. intros a n md. destruct md as [fd0 [maps0 lz0 mt0] io0 fs0 proc0 lim0 tm0]. repeat split; reflexivity. Qed.

Lemma rr_model_ivs_wf : forall md, amwf md -> YM05.ceil_of_top (alloc_top (m_vmmaps md)) -> YK0g.model_ivs_wf md.
Proof.
intros md [(W1 & W2 & W3 & _) _] CT. split; [|split; [|split]];
[intros q Hq; exact (W1 q Hq) | intros q Hq; exact (W2 q Hq) | intros q Hq; exact (W3 q Hq) | exact (ceil_top_init_sp_ok _ CT)].
Qed.

(* The ledger at the post layout and state, from the ledger at the entry and the model facts of the map. *)
Lemma rr_ledger_rebuild : forall ly S S1 md md2 (a ncap : Z),
  Wf_cf (as_universe B) S -> sec_placed ly S -> layout_ok ly -> amwf md -> xs_placed_cf ly S -> xs_mapped_cf ly S md ->
  ALedger_cf tfibsegs ly S md -> ALEDGER_X ly S md ->
  errb_frame S S1 -> st_secs S1 = map cfx_retire (st_secs S) ++ [mkSec ncap ERRB_CAP_TAG false] -> 0 < ncap ->
  in_app a ncap -> a + ncap <= ASAN_CEIL ->
  Forall (zdisjoint (a, ncap)) (static_extents ly ++ sec_extents ly S ++ perm_maps ly ++ band_maps) ->
  Forall (zdisjoint (a, ncap)) (xs_cf ly S) ->
  vm_reserved (m_vmmaps md2) = vm_reserved (m_vmmaps md) -> vm_limit (m_vmmaps md2) = vm_limit (m_vmmaps md) ->
  vm_init_sp (m_vmmaps md2) = vm_init_sp (m_vmmaps md) ->
  In (wiv (a, ncap)) (vm_maps (m_vmmaps md2)) ->
  (forall q, In q (vm_maps (m_vmmaps md)) -> Forall (fun e => fst q <> w64 (fst e)) (xs_cf ly S) -> In q (vm_maps (m_vmmaps md2))) ->
  (forall q, In q (vm_maps (m_vmmaps md2)) ->
     q = wiv (a, ncap) \/ (In q (vm_maps (m_vmmaps md)) /\ Forall (fun e => fst q <> w64 (fst e)) (xs_cf ly S))) ->
  (forall x, Forall (fun e => ~ in_zr x e) (xs_cf ly S) ->
     YK0g.covered (vm_noaccess (m_vmmaps md2) ++ m_vm_lazy md2) x = YK0g.covered (vm_noaccess (m_vmmaps md) ++ m_vm_lazy md) x) ->
  eager_used md2 + esec (vm_noaccess (m_vmmaps md)) (m_vm_lazy md) (xs_cf ly S) =
    eager_used md + esec (vm_noaccess (m_vmmaps md)) (m_vm_lazy md) [(a, ncap)] ->
  (forall lo n, region_free (vm_noaccess (m_vmmaps md)) lo n = true -> region_free (vm_noaccess (m_vmmaps md2)) lo n = true) ->
  YGcfLazyMaps.lazy_in_maps_cf md2 ->
  ALedger_cf tfibsegs (set_ly_sec ly (length (st_secs S)) a) S1 md2 /\ ALEDGER_X (set_ly_sec ly (length (st_secs S)) a) S1 md2.
Proof.
intros ly S S1 md md2 a ncap WF PL LO MW XP XM L LX EF Es Hn APP CE FA FX RES LIM ISP HIN KEEP HM2 HCOV HEG HNA LZ2.
set (n := length (st_secs S)) in *. set (ly1 := set_ly_sec ly n a).
assert (LE : layout_le n ly ly1) by apply set_ly_sec_le.
assert (SE : sec_extents ly1 S1 = sec_extents ly S).
{ unfold errb_frame in EF. rewrite EF. exact (sec_extents_le_cf ly ly1 S _ _ _ _ LE WF). }
assert (XS1 : xs_cf ly1 S1 = [(a, ncap)]).
{ rewrite (xs_cf_remap ly1 S S1 ncap Es). unfold ly1, n. cbn [ly_sec set_ly_sec]. rewrite Nat.eqb_refl, Z.max_r by lia. reflexivity. }
assert (CAP1 : errb_cap_cf S1 = ncap) by exact (rr_cap_remap S S1 ncap ltac:(lia) Es).
assert (PC : prim_committed S1 = prim_committed S) by (unfold errb_frame in EF; rewrite EF; reflexivity).
assert (RS : st_sec_reserved S1 = st_sec_reserved S) by (unfold errb_frame in EF; rewrite EF; reflexivity).
pose proof (cfxm_xs_pos ly S md MW XP XM) as XSz.
pose proof alloc_ceiling_lt as CL. rr_ceil. pose proof APP as [APP0 _].
pose proof (sec_extents_sizes64P_cf _ _ _ _ ly S WF) as SZ.
destruct PL as [PF PD].
assert (SECb : forall e, In e (sec_extents ly S) -> 4096 <= fst e /\ 4096 <= snd e /\ fst e + snd e <= ASAN_CEIL).
{ intros e He. destruct (proj1 (Forall_forall _ _) PF e He) as (_ & [E1 _] & E3). destruct (proj1 (Forall_forall _ _) SZ e He) as [E4 _].
  unfold ASAN_CEIL. lia. }
assert (OLDP : forall e, In e (xs_cf ly S) -> in_app (fst e) (snd e) /\ Forall (zdisjoint e) (sec_extents ly S ++ static_extents ly ++ ly_extra ly)).
{ intros e He. destruct (proj1 (Forall_forall _ _) XP e He) as (_ & H1 & _ & H2). split; assumption. }
(* a map of md survives in md2 when its base is not an errbuf base *)
assert (KZ : forall z, In (wiv z) (vm_maps (m_vmmaps md)) -> 0 <= fst z < 2 ^ 64 ->
  (forall e, In e (xs_cf ly S) -> fst z <> fst e) -> In (wiv z) (vm_maps (m_vmmaps md2))).
{ intros z Hz Z1 D. apply KEEP; [exact Hz|]. apply Forall_forall. intros e He. cbn [wiv fst].
  destruct (proj1 (Forall_forall _ _) XSz e He) as (E1 & E2 & E3). apply rr_w64_ne; [lia | lia | exact (D e He)]. }
assert (APS : forall z e, In z (static_extents ly ++ ly_extra ly) -> In e (xs_cf ly S) -> 0 < snd z -> fst z <> fst e).
{ intros z e Hz He Hp. destruct (OLDP e He) as [_ D]. destruct (proj1 (Forall_forall _ _) XSz e He) as (E1 & E2 & E3).
  pose proof (proj1 (Forall_forall _ _) D z ltac:(apply in_or_app; right; exact Hz)) as Dz. unfold zdisjoint in Dz. lia. }
assert (BAP : forall (z : Z * Z) e, In e (xs_cf ly S) -> kLowShadowBeg <= fst z < kHighMemBeg -> fst z <> fst e).
{ intros z e He Hz E. destruct (OLDP e He) as [[A0 A1] _]. destruct (proj1 (Forall_forall _ _) XSz e He) as (E1 & E2 & E3).
  unfold kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *. lia. }
assert (ESS : esec (vm_noaccess (m_vmmaps md2)) (m_vm_lazy md2) (sec_extents ly S) =
              esec (vm_noaccess (m_vmmaps md)) (m_vm_lazy md) (sec_extents ly S)).
{ apply esec_ext.
  - apply Forall_forall. intros e He. destruct (SECb e He) as (E1 & E2 & E3). unfold ASAN_CEIL in *. lia.
  - intros e x He Hx. apply HCOV. apply Forall_forall. intros e' He' Hin.
    destruct (OLDP e' He') as [_ D]. pose proof (proj1 (Forall_forall _ _) D e ltac:(apply in_or_app; left; exact He)) as De.
    unfold zdisjoint, in_zr in *. lia. }
assert (ENEW : esec (vm_noaccess (m_vmmaps md2)) (m_vm_lazy md2) [(a, ncap)] =
               esec (vm_noaccess (m_vmmaps md)) (m_vm_lazy md) [(a, ncap)]).
{ destruct APP as [A0 _]. apply esec_ext.
  - constructor; [cbn [fst snd]; unfold ASAN_CEIL in *; lia | constructor].
  - intros e x [<-|[]] Hx. apply HCOV. apply Forall_forall. intros e' He' Hin.
    pose proof (proj1 (Forall_forall _ _) FX e' He') as De. unfold zdisjoint, in_zr in *. cbn [fst snd] in *. lia. }
pose proof LX as LX'. unfold ALEDGER_X, errb_zone in LX'. rewrite esec_app in LX'.
pose proof (esec_one_le (vm_noaccess (m_vmmaps md)) (m_vm_lazy md) (a, ncap) ltac:(cbn [snd]; unfold ASAN_CEIL in *; lia)) as E1. cbn [snd] in E1.
pose proof (lo_high _ LO) as [HP1 HP2].
pose proof (proj1 (Forall_forall _ _) FA (ly_prim ly, kPrimResvSize) ltac:(apply in_or_app; left; unfold static_extents, owned_extents; cbn; tauto)) as FPR.
split.
- constructor.
  + exact (alc_img _ _ _ _ L).
  + rewrite LIM. exact (alc_limit _ _ _ _ L).
  + rewrite RES. exact (alc_reserved _ _ _ _ L).
  + destruct (alc_prim _ _ _ _ L) as (pieces & PP & PI). exists pieces. split.
    * unfold errb_frame in EF. rewrite EF. exact PP.
    * intros p. rewrite (PI p). split.
      -- intros (Hin & B1 & B2 & B3). split; [|exact (conj B1 (conj B2 B3))].
         apply (KZ p Hin); [unfold in_high, kHighMemBeg, kPrimResvSize, ASAN_CEIL in *; lia|].
         intros e He. destruct (OLDP e He) as [_ D]. destruct (proj1 (Forall_forall _ _) XSz e He) as (Q1 & Q2 & Q3).
         pose proof (proj1 (Forall_forall _ _) D (ly_prim ly, kPrimResvSize)
           ltac:(apply in_or_app; right; apply in_or_app; left; unfold static_extents, owned_extents; cbn; tauto)) as De.
         unfold zdisjoint in De. cbn [fst snd] in De. lia.
      -- intros (Hin & B1 & B2 & B3). split; [|exact (conj B1 (conj B2 B3))].
         destruct (HM2 _ Hin) as [Heq|[Hin0 _]]; [exfalso|exact Hin0].
         change (ly_prim ly1) with (ly_prim ly) in B2, B3.
         apply (f_equal fst) in Heq. cbn [wiv fst] in Heq.
         apply cfxm_w64_inj in Heq; [|unfold in_high, kHighMemBeg, kPrimResvSize, ASAN_CEIL in *; lia | destruct APP as [A0 _]; unfold ASAN_CEIL in *; lia].
         unfold zdisjoint in FPR. cbn [fst snd] in FPR. lia.
  + pose proof (proj1 (Forall_forall _ _) (lo_app _ LO) (ly_Q ly, kPtrArrayResv) ltac:(unfold owned_extents; cbn; tauto)) as [Q1 Q2].
    cbn [fst snd] in Q1, Q2.
    apply (KZ (ly_Q ly, kPtrArrayResv) (alc_Q _ _ _ _ L)); [cbn [fst]; unfold kLowShadowBeg, kHighMemBeg, kPtrArrayResv, ASAN_CEIL in *; lia|].
    intros e He. apply (APS _ e); [apply in_or_app; left; unfold static_extents, owned_extents; cbn; tauto | exact He | cbn; unfold kPtrArrayResv; lia].
  + apply (KZ _ (alc_hs _ _ _ _ L)); [cbn [fst]; unfold kHighShadowBeg; lia|].
    intros e He. apply (BAP _ e He). cbn [fst]. unfold kHighShadowBeg, kLowShadowBeg, kHighMemBeg. lia.
  + rewrite SE. intros e He. destruct (SECb e He) as (Z1 & Z2 & Z3).
    apply (KZ e (alc_sec _ _ _ _ L e He)); [unfold ASAN_CEIL in *; lia|].
    intros e' He'. destruct (OLDP e' He') as [_ D]. destruct (proj1 (Forall_forall _ _) XSz e' He') as (Q1 & Q2 & Q3).
    pose proof (proj1 (Forall_forall _ _) D e ltac:(apply in_or_app; left; exact He)) as De. unfold zdisjoint in De. lia.
  + intros q Hq. destruct (HM2 q Hq) as [->|[Hq0 Hne]].
    * apply Exists_exists. exists (a, ncap).
      split; [apply in_or_app; right; apply in_or_app; right; unfold errb_zone; rewrite XS1; left; reflexivity|].
      destruct APP as [A0 _]. cbn [wiv fst snd]. rewrite !w64_unsigned by (unfold ASAN_CEIL in *; lia). lia.
    * pose proof (alc_cover _ _ _ _ L q Hq0) as X. apply Exists_exists in X as (z & Hz & Hqz). apply Exists_exists. exists z.
      split; [|exact Hqz]. rewrite !in_app_iff in Hz |- *. destruct Hz as [Hz|[Hz|Hz]].
      -- left. exact Hz.
      -- right; left. rewrite SE. exact Hz.
      -- exfalso. unfold errb_zone in Hz.
         pose proof (proj1 (Forall_forall _ _) Hne z Hz) as Nq. pose proof (XM z Hz) as Hz0.
         destruct MW as [(W1 & W2 & W3 & PW & _) NE]. pose proof (NE q Hq0) as Pq.
         destruct (proj1 (Forall_forall _ _) XSz z Hz) as (Z1 & Z2 & Z3).
         assert (NEQ : q <> wiv z) by (intros E; apply Nq; rewrite E; reflexivity).
         destruct (rr_pairwise_in _ _ q (wiv z) PW Hq0 Hz0 NEQ) as [Dq|Dq]; cbn [wiv fst snd] in Dq;
         rewrite !w64_unsigned in Dq by lia; lia.
  + unfold eager_cf, errb_zone. rewrite SE, XS1, PC, RS, esec_app, ESS, ENEW. lia.
  + intros z Hz. change (perm_maps ly1) with (perm_maps ly) in Hz. pose proof (perm_facts ly 1 LO ltac:(lia) z Hz) as (Z1 & Z2 & Z3 & _).
    apply (KZ z (alc_perm _ _ _ _ L z Hz)); [lia|]. intros e He.
    destruct MW as [_ NE]. pose proof (NE _ (alc_perm _ _ _ _ L z Hz)) as Pz. cbn [wiv snd] in Pz. rewrite w64_unsigned in Pz by lia.
    unfold perm_maps in Hz. apply in_app_iff in Hz as [Hz|Hz].
    * cbn [In] in Hz. destruct Hz as [<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]].
      -- apply (APS _ e); [apply in_or_app; left; unfold static_extents, owned_extents; cbn; tauto | exact He | exact Pz].
      -- apply (APS _ e); [apply in_or_app; left; unfold static_extents, owned_extents; cbn; tauto | exact He | exact Pz].
      -- apply (APS _ e); [apply in_or_app; left; unfold static_extents, owned_extents; cbn; tauto | exact He | exact Pz].
      -- apply (APS _ e); [apply in_or_app; left; unfold static_extents, owned_extents; cbn; tauto | exact He | exact Pz].
      -- cbn [fst]. apply (APS (ly_C ly, 256) e); [apply in_or_app; left; unfold static_extents, owned_extents; cbn; tauto | exact He | cbn; lia].
      -- apply (APS _ e); [apply in_or_app; left; unfold static_extents, owned_extents; cbn; tauto | exact He | exact Pz].
    * apply (APS _ e); [apply in_or_app; right; exact Hz | exact He | exact Pz].
  + intros z Hz. apply (KZ z (alc_band _ _ _ _ L z Hz)).
    * unfold band_maps in Hz. cbn in Hz. destruct Hz as [<-|[<-|[<-|[]]]]; cbn [fst];
      unfold kLowShadowBeg, kLowShadowEnd, kHighShadowBeg; lia.
    * intros e He. apply (BAP z e He). unfold band_maps in Hz. cbn in Hz. destruct Hz as [<-|[<-|[<-|[]]]]; cbn [fst];
      unfold kLowShadowBeg, kLowShadowEnd, kHighShadowBeg, kHighMemBeg; lia.
  + intros e z He Hz. rewrite SE in He. exact (alc_secx _ _ _ _ L e z He Hz).
  + unfold alloc_top. rewrite ISP. exact (alc_top _ _ _ _ L).
  + exact (alc_imgcov _ _ _ _ L).
  + destruct (alc_shna _ _ _ _ L) as [N1 N2]. split; apply HNA; assumption.
  + exact LZ2.
  + rewrite XS1. intros e [<-|[]]. exact HIN.
- unfold ALEDGER_X, errb_zone. rewrite SE, XS1, PC, RS, esec_app, ESS, ENEW. lia.
Qed.

Lemma rr_ahs_setly : forall ly S a H mem, Wf_cf (as_universe B) S -> ahs B ly S H mem ->
  ahs B (set_ly_sec ly (length (st_secs S)) a) S H mem.
Proof.
intros ly S a H mem WF [HP HZ]. set (ly1 := set_ly_sec ly (length (st_secs S)) a).
pose proof (set_ly_sec_le (length (st_secs S)) ly a) as LE. fold ly1 in LE.
assert (USR : forall k, In k (st_chunks S) -> sptr_addr B ly1 (ck_user k) = sptr_addr B ly (ck_user k)).
{ intros k Hk. apply (sptr_addr_le B ly ly1 (length (st_secs S)) _ LE).
  pose proof (rr_chunk_lt _ _ _ _ S WF k Hk) as LT. unfold ck_user. destruct (ck_beg k); cbn; try exact I; exact LT. }
assert (CB : forall x, aclient_byte B ly1 S x -> aclient_byte B ly S x).
{ intros x [(k & Hk & Hs & Hr)|(cq & Hcp & Hr)].
  - left. exists k. rewrite (USR k Hk) in Hr. exact (conj Hk (conj Hs Hr)).
  - right. exists cq. exact (conj Hcp Hr). }
split.
- intros x Hx NC Hv. apply (HP x Hx); [intros C; apply NC; destruct C as [(k & Hk & Hs & Hr)|(cq & Hcp & Hr)];
  [left; exists k; rewrite (USR k Hk); exact (conj Hk (conj Hs Hr)) | right; exists cq; exact (conj Hcp Hr)] | exact Hv].
- intros g Hg HA HF. apply (HZ g Hg HA). unfold hfree in *. rewrite (sec_extents_le_cf ly ly1 S _ _ _ _ LE WF) in HF. exact HF.
Qed.

(* ================================================================================================================ *)
(* 9. The grant at the call site, and the relation after the errbuf (re)map.                                         *)
Lemma errb_grant_facts : forall Hp ly S (W : world tfibsegs) mem md (mat : list word) (a n : Z),
  ARcf tfibsegs B ly S Hp W mem md -> xs_mapped_cf ly S md ->
  grant_ok_na_pin (with_vm_backing (m_vm_lazy md) mat md) (w64 a) n = true ->
  0 <= a < 2 ^ 64 -> 0 < n < 2 ^ 64 -> n mod 4096 = 0 ->
  page_aligned a /\ in_app a n /\ a + n <= ASAN_CEIL /\
  Forall (zdisjoint (a, n)) (static_extents ly ++ sec_extents ly S ++ perm_maps ly ++ band_maps ++ xs_cf ly S).
Proof.
intros Hp ly S W mem md mat a n (M & L & _ & MW & _) XM G Ha Hn Hal.
pose proof (amc_wf _ _ _ _ _ M) as WF. pose proof (amc_layout _ _ _ _ _ M) as LO.
pose proof (amc_placed _ _ _ _ _ M) as PL. pose proof (amc_xs_placed _ _ _ _ _ M) as XP.
set (md0 := with_vm_backing (m_vm_lazy md) mat md) in *.
assert (L0 : ALedger_cf tfibsegs ly S md0) by (eapply ALedger_same_cf; [exact L | reflexivity | reflexivity | apply eager_used_wvb]).
assert (Ua : bv_unsigned (w64 a) = a) by (apply w64_unsigned; lia).
assert (Un : bv_unsigned (w64 n) = n) by (apply w64_unsigned; lia).
destruct (rr_grant_facts ly S md0 (w64 a) (w64 n) LO WF PL L0 ltac:(rewrite Un; exact G) ltac:(lia) ltac:(rewrite Un; exact Hal))
  as (GA & GAPP & GCE & GFA).
rewrite Ua in GA. rewrite Ua, Un in GAPP, GCE, GFA.
pose proof alloc_ceiling_lt as CL. rr_ceil.
pose proof (xs_fresh_of_grant ly S md0 a n XP (xs_mapped_cf_wvb ly S md _ mat XM) G ltac:(lia) ltac:(lia) ltac:(unfold ASAN_CEIL in *; lia)) as XF.
split; [exact GA|]. split; [exact GAPP|]. split; [exact GCE|].
apply Forall_forall. intros z Hz. rewrite !in_app_iff in Hz. destruct Hz as [Hz|[Hz|[Hz|[Hz|Hz]]]];
  try (apply (proj1 (Forall_forall _ _) GFA); rewrite !in_app_iff; tauto).
pose proof (proj1 (Forall_forall _ _) XF z Hz) as D. unfold zdisjoint in *. lia.
Qed.

(* The relation SPLIT at an errbuf step (field round 2): ARmcf, which pins the errbuf object's cells at the state
   (amc_errb_cells), and the shadow invariant ahs stay at the entry state S over the entry memory; the ledger, the
   budget and the model's well-formedness are at the step's state S1.  Between the model step and the machine's
   object writes no single state matches the object bytes, so the walk carries this form and RepRelXcf.errb_rel_post
   rebuilds ARcf at the end state from the end memory and its object cells. *)
Definition rr_split (ly : alayout) (S S1 : astate) (Hp : list Z) (W : world tfibsegs) (mem : word -> option byte) (md : Model) : Prop :=
  ARmcf B ly S Hp (aview tfibsegs (w_H W) mem) /\ ahs B ly S (w_H W) mem /\
  ALedger_cf tfibsegs ly S1 md /\ abudget_ok_cf tfibsegs ly S1 W /\ amwf md.

Lemma rr_split_of_ARcf : forall ly S Hp W mem md, ARcf tfibsegs B ly S Hp W mem md -> rr_split ly S S Hp W mem md.
Proof. intros ly S Hp W mem md (M & L & BU & MW & HS). exact (conj M (conj HS (conj L (conj BU MW)))). Qed.

(* the step's state moves by an st_secs-only step that keeps the errbuf extent and capacity *)
Lemma rr_split_secs : forall ly S0 S S1 Hp W mem md, errb_frame S S1 -> secs_errb_grow (st_secs S) (st_secs S1) ->
  xs_cf ly S1 = xs_cf ly S -> errb_cap_cf S1 = errb_cap_cf S ->
  rr_split ly S0 S Hp W mem md -> rr_split ly S0 S1 Hp W mem md.
Proof.
intros ly S0 S S1 Hp W mem md EF GR XS CAP (M & HS & L & BU & MW).
split; [exact M|]. split; [exact HS|]. split; [exact (rr_ledger_secs ly S S1 md EF XS CAP L)|].
split; [apply (rr_budget_secs ly S S1 W EF GR); [lia | exact BU] | exact MW].
Qed.

(* The common core of the first map and the remap: the end model md2 of the case, described by its model facts. *)
Lemma rr_rel_core : forall Hp ly (S S1 : astate) (W : world tfibsegs) (mem : word -> option byte) (md md2 : Model) (a ncap : Z),
  TfibSyms B -> img_cover ly -> ARcf tfibsegs B ly S Hp W mem md -> xs_mapped_cf ly S md -> ALEDGER_X ly S md ->
  0 <= a < 2 ^ 64 -> 0 < ncap < 2 ^ 64 ->
  page_aligned a -> in_app a ncap -> a + ncap <= ASAN_CEIL ->
  Forall (zdisjoint (a, ncap)) (static_extents ly ++ sec_extents ly S ++ perm_maps ly ++ band_maps) ->
  Forall (zdisjoint (a, ncap)) (xs_cf ly S) -> errb_cap_cf S <= ncap ->
  Wf_cf (as_universe B) S1 -> errb_frame S S1 -> st_secs S1 = map cfx_retire (st_secs S) ++ [mkSec ncap ERRB_CAP_TAG false] ->
  amwf md2 ->
  vm_reserved (m_vmmaps md2) = vm_reserved (m_vmmaps md) -> vm_limit (m_vmmaps md2) = vm_limit (m_vmmaps md) ->
  vm_init_sp (m_vmmaps md2) = vm_init_sp (m_vmmaps md) ->
  In (wiv (a, ncap)) (vm_maps (m_vmmaps md2)) ->
  (forall q, In q (vm_maps (m_vmmaps md)) -> Forall (fun e => fst q <> w64 (fst e)) (xs_cf ly S) -> In q (vm_maps (m_vmmaps md2))) ->
  (forall q, In q (vm_maps (m_vmmaps md2)) ->
     q = wiv (a, ncap) \/ (In q (vm_maps (m_vmmaps md)) /\ Forall (fun e => fst q <> w64 (fst e)) (xs_cf ly S))) ->
  (forall x, Forall (fun e => ~ in_zr x e) (xs_cf ly S) ->
     YK0g.covered (vm_noaccess (m_vmmaps md2) ++ m_vm_lazy md2) x = YK0g.covered (vm_noaccess (m_vmmaps md) ++ m_vm_lazy md) x) ->
  eager_used md2 + esec (vm_noaccess (m_vmmaps md)) (m_vm_lazy md) (xs_cf ly S) =
    eager_used md + esec (vm_noaccess (m_vmmaps md)) (m_vm_lazy md) [(a, ncap)] ->
  (forall lo n, region_free (vm_noaccess (m_vmmaps md)) lo n = true -> region_free (vm_noaccess (m_vmmaps md2)) lo n = true) ->
  YGcfLazyMaps.lazy_in_maps_cf md2 ->
  let ly1 := set_ly_sec ly (length (st_secs S)) a in
  layout_le (length (st_secs S)) ly ly1 /\ layout_ok ly1 /\ img_cover ly1 /\ ly_tsd ly1 = ly_tsd ly /\
  rr_split ly1 S S1 Hp W mem md2 /\ ALEDGER_X ly1 S1 md2 /\
  xs_mapped_cf ly1 S1 md2 /\ xs_placed_cf ly1 S1 /\
  YG0ncf.errb_data_cf ly1 S1 = a /\ errb_cap_cf S1 = ncap /\
  A_bytes (w_A W) + ncap - errb_cap_cf S <= abudget_cf S1.
Proof.
intros Hp ly S S1 W mem md md2 a ncap TS IC AR XM LX Ha Hn GA GAPP GCE GFA FX CAPLE W1 EF Es MW2
  RES LIM ISP HIN KEEP HM2 HCOV HEG HNA LZ2 ly1.
pose proof AR as (M & L & BU & MW & HS).
pose proof (amc_wf _ _ _ _ _ M) as WF. pose proof (amc_layout _ _ _ _ _ M) as LO.
pose proof (amc_placed _ _ _ _ _ M) as PL. pose proof (amc_xs_placed _ _ _ _ _ M) as XP.
assert (LE : layout_le (length (st_secs S)) ly ly1) by apply set_ly_sec_le.
assert (LO1 : layout_ok ly1) by exact (set_ly_sec_ok ly _ a LO).
assert (SL : ly_sec ly1 (length (st_secs S)) = a) by (unfold ly1; cbn [ly_sec set_ly_sec]; rewrite Nat.eqb_refl; reflexivity).
assert (SE : sec_extents ly1 S1 = sec_extents ly S).
{ unfold errb_frame in EF. rewrite EF. exact (sec_extents_le_cf ly ly1 S _ _ _ _ LE WF). }
assert (CAP1 : errb_cap_cf S1 = ncap) by exact (rr_cap_remap S S1 ncap ltac:(lia) Es).
assert (DAT : YG0ncf.errb_data_cf ly1 S1 = a) by (rewrite (rr_data_remap ly1 S S1 ncap Es); exact SL).
pose proof (proj1 (Forall_app _ _ _) GFA) as [GFs GFr]. pose proof (proj1 (Forall_app _ _ _) GFr) as [GFc GFr'].
pose proof (proj1 (Forall_app _ _ _) GFr') as [GFp _].
assert (XP1 : xs_placed_cf ly1 S1).
{ apply (xs_placed_cf_remap ly1 S S1 ncap Es). rewrite Z.max_r by lia. rewrite SL.
  split; [exact GA|]. split; [exact GAPP|]. split; [unfold ASAN_CEIL in GCE; exact GCE|].
  rewrite SE, (cfx_static_layout _ ly ly1 LE). change (ly_extra ly1) with (ly_extra ly).
  apply Forall_app. split; [exact GFc|]. apply Forall_app. split; [exact GFs|].
  apply Forall_forall. intros z Hz. apply (proj1 (Forall_forall _ _) GFp). unfold perm_maps. apply in_or_app. right. exact Hz. }
(* the relation *)
destruct (rr_ledger_rebuild ly S S1 md md2 a ncap WF PL LO MW XP XM L LX EF Es ltac:(lia) GAPP GCE GFA FX
  RES LIM ISP HIN KEEP HM2 HCOV HEG HNA LZ2) as [L1 LX1].
assert (GR : secs_errb_grow (st_secs S) (st_secs S1)) by exact (rr_secs_grow_map S S1 ncap ltac:(lia) Es).
assert (BU1 : abudget_ok_cf tfibsegs ly S1 W) by (apply (rr_budget_secs ly S S1 W EF GR); [lia | exact BU]).
assert (BUD : A_bytes (w_A W) + ncap - errb_cap_cf S <= abudget_cf S1).
{ pose proof (cf_hull_errb S S1 GR (rr_hulls_frame S S1 EF)) as HH.
  destruct BU as (A1 & _ & _). unfold errb_frame in EF.
  assert (E1 : prim_committed S1 = prim_committed S) by (rewrite EF; reflexivity).
  assert (E2 : st_sec_reserved S1 = st_sec_reserved S) by (rewrite EF; reflexivity).
  assert (E3 : sec_live_bytes S1 = sec_live_bytes S) by (rewrite EF; reflexivity).
  unfold abudget_cf in *. rewrite E1, E2, E3, CAP1. lia. }
split; [exact LE|]. split; [exact LO1|]. split; [exact IC|]. split; [reflexivity|].
split.
{ split; [exact (rr_ARmcf_layout ly ly1 S Hp _ TS M LE LO1 (xs_placed_cf_layout _ _ _ _ ly ly1 S WF LE XP))|].
  split; [exact (rr_ahs_setly ly S a _ mem WF HS)|].
  split; [exact L1|]. split; [|exact MW2].
  destruct BU1 as (A1 & A2 & A3). split; [exact A1|]. split.
  + intros e He. rewrite SE in He. apply A2. unfold errb_frame in EF. rewrite EF. exact He.
  + exact (cls1_band_vis_layout_cf _ ly ly1 _ LE A3). }
split; [exact LX1|].
split; [apply (xs_mapped_cf_errb_map S ly1 S1 ncap md2 Es ltac:(lia)); rewrite SL; exact HIN|].
split; [exact XP1|]. split; [exact DAT|]. split; [exact CAP1 | exact BUD].
Qed.

Lemma rr_noreserve_34 : mmap_noreserve_b (w64 34) = false.
Proof. vm_compute. reflexivity. Qed.

(* The first map: no capacity entry yet (errb_mapped_cf S = false), so nothing is unmapped. *)
Lemma errb_rel_map : forall Hp ly (S S1 : astate) (W : world tfibsegs) (mem : word -> option byte)
  (md : Model) (mat : list word) (a ncap : Z),
  TfibSyms B -> img_cover ly ->
  ARcf tfibsegs B ly S Hp W mem md -> xs_mapped_cf ly S md -> ALEDGER_X ly S md -> errb_mapped_cf S = false ->
  0 <= a < 2 ^ 64 -> 0 < ncap < 2 ^ 64 -> ncap mod kPage = 0 ->
  grant_ok_na_pin (with_vm_backing (m_vm_lazy md) mat md) (w64 a) ncap = true ->
  Wf_cf (as_universe B) S1 -> errb_frame S S1 ->
  st_secs S1 = map cfx_retire (st_secs S) ++ [mkSec ncap ERRB_CAP_TAG false] ->
  let md1 := with_mmap_backing (w64 34) (w64 a) (w64 ncap)
               (mmap_model (w64 a) (w64 ncap) (with_vm_backing (m_vm_lazy md) mat md)) in
  let ly1 := set_ly_sec ly (length (st_secs S)) a in
  layout_le (length (st_secs S)) ly ly1 /\ layout_ok ly1 /\ img_cover ly1 /\ ly_tsd ly1 = ly_tsd ly /\
  rr_split ly1 S S1 Hp W mem md1 /\ ALEDGER_X ly1 S1 md1 /\
  xs_mapped_cf ly1 S1 md1 /\ xs_placed_cf ly1 S1 /\
  YG0ncf.errb_data_cf ly1 S1 = a /\ errb_cap_cf S1 = ncap /\
  A_bytes (w_A W) + ncap <= abudget_cf S1.
Proof.
intros Hp ly S S1 W mem md mat a ncap TS IC AR XM LX UM Ha Hn Hal G W1 EF Es md1 ly1.
pose proof AR as (M & L & BU & MW & HS).
set (md0 := with_vm_backing (m_vm_lazy md) mat md) in *.
assert (XN : xs_cf ly S = []) by exact (rr_xs_unmapped ly S UM).
assert (CAP0 : errb_cap_cf S = 0).
{ unfold errb_mapped_cf in UM. rewrite rr_existsb_filter in UM. unfold errb_cap_cf, errb_e.
  destruct (filter is_errb_cap (st_secs S)); [reflexivity | discriminate UM]. }
destruct (errb_grant_facts Hp ly S W mem md mat a ncap AR XM G Ha Hn ltac:(unfold kPage in *; lia)) as (GA & GAPP & GCE & GFA').
assert (GFA : Forall (zdisjoint (a, ncap)) (static_extents ly ++ sec_extents ly S ++ perm_maps ly ++ band_maps)).
{ apply Forall_forall. intros z Hz. apply (proj1 (Forall_forall _ _) GFA').
  apply in_app_iff in Hz as [Hz|Hz]; [apply in_or_app; left; exact Hz|]. apply in_or_app; right.
  apply in_app_iff in Hz as [Hz|Hz]; [apply in_or_app; left; exact Hz|]. apply in_or_app; right.
  apply in_app_iff in Hz as [Hz|Hz]; [apply in_or_app; left; exact Hz|]. apply in_or_app; right.
  apply in_or_app; left; exact Hz. }
assert (MD1 : md1 = mmap_model (w64 a) (w64 ncap) md0) by (unfold md1; apply with_mmap_backing_plain; exact rr_noreserve_34).
assert (Ua : bv_unsigned (w64 a) = a) by (apply w64_unsigned; lia).
assert (Un : bv_unsigned (w64 ncap) = ncap) by (apply w64_unsigned; lia).
pose proof alloc_ceiling_lt as CL. rr_ceil.
assert (RF : forall q, In q (vm_maps (m_vmmaps md0)) -> a + ncap <= bv_unsigned (fst q) \/ bv_unsigned (fst q) + bv_unsigned (snd q) <= a).
{ intros q Hq. pose proof G as G'. unfold grant_ok_na_pin in G'. apply andb_prop in G' as [_ G4].
  pose proof (YK13.region_free_In _ (w64 a) (Z_to_bv 64 ncap) (fst q) (snd q) G4 ltac:(apply in_app_iff; right; rewrite <- surjective_pairing; exact Hq)) as D.
  change (Z_to_bv 64 ncap) with (w64 ncap) in D. rewrite Ua, Un in D. exact D. }
assert (MW0 : amwf md0) by exact (amwf_same md md0 eq_refl eq_refl MW).
assert (MW1 : amwf (mmap_model (w64 a) (w64 ncap) md0)) by (apply rr_amwf_mmap; [exact MW0 | lia | lia | unfold ASAN_CEIL in *; lia | exact RF]).
assert (MWF0 : YK0g.model_ivs_wf md0) by exact (rr_model_ivs_wf md0 MW0 (alc_top _ _ _ _ L)).
pose proof (eager_used_mmap_model (w64 a) (w64 ncap) md0 MWF0 ltac:(rewrite Ua, Un; unfold ASAN_CEIL in *; lia)) as EG.
rewrite Ua, Un in EG.
assert (LZ0 : YGcfLazyMaps.lazy_in_maps_cf md0) by exact (alc_lazy_in_maps _ _ _ _ L).
pose proof (rr_rel_core Hp ly S S1 W mem md (mmap_model (w64 a) (w64 ncap) md0) a ncap TS IC AR XM LX Ha Hn GA GAPP GCE GFA
  ltac:(rewrite XN; constructor) ltac:(rewrite CAP0; lia) W1 EF Es
  MW1 eq_refl eq_refl eq_refl ltac:(left; reflexivity)
  ltac:(intros q Hq _; right; exact Hq)
  ltac:(intros q [<-|Hq]; [left; reflexivity | right; split; [exact Hq | rewrite XN; constructor]])
  ltac:(intros x _; reflexivity)
  ltac:(rewrite XN, esec_nil, EG, Z.add_0_r; unfold md0; rewrite eager_used_wvb; reflexivity)
  ltac:(intros lo n0 H0; exact H0)
  (YGcfLazyMaps.lazy_in_maps_mmap_cf (w64 a) (w64 ncap) md0 LZ0)) as C.
cbv zeta in C. rewrite MD1. rewrite CAP0 in C. replace (A_bytes (w_A W) + ncap - 0) with (A_bytes (w_A W) + ncap) in C by lia. exact C.
Qed.

(* The remap: the old buffer (errb_data_cf ly S, errb_cap_cf S) is unmapped after the new one is granted. *)
Lemma errb_rel_remap : forall Hp ly (S S1 : astate) (W : world tfibsegs) (mem : word -> option byte)
  (md : Model) (mat : list word) (a ncap : Z),
  TfibSyms B -> img_cover ly ->
  ARcf tfibsegs B ly S Hp W mem md -> xs_mapped_cf ly S md -> ALEDGER_X ly S md -> errb_mapped_cf S = true ->
  errb_cap_cf S <= ncap ->
  0 <= a < 2 ^ 64 -> 0 < ncap < 2 ^ 64 -> ncap mod kPage = 0 ->
  grant_ok_na_pin (with_vm_backing (m_vm_lazy md) mat md) (w64 a) ncap = true ->
  Wf_cf (as_universe B) S1 -> errb_frame S S1 ->
  st_secs S1 = map cfx_retire (st_secs S) ++ [mkSec ncap ERRB_CAP_TAG false] ->
  let md1 := with_mmap_backing (w64 34) (w64 a) (w64 ncap)
               (mmap_model (w64 a) (w64 ncap) (with_vm_backing (m_vm_lazy md) mat md)) in
  let md2 := munmap_model (w64 (YG0ncf.errb_data_cf ly S)) (w64 (errb_cap_cf S)) md1 in
  let ly1 := set_ly_sec ly (length (st_secs S)) a in
  layout_le (length (st_secs S)) ly ly1 /\ layout_ok ly1 /\ img_cover ly1 /\ ly_tsd ly1 = ly_tsd ly /\
  rr_split ly1 S S1 Hp W mem md2 /\ ALEDGER_X ly1 S1 md2 /\
  xs_mapped_cf ly1 S1 md2 /\ xs_placed_cf ly1 S1 /\
  YG0ncf.errb_data_cf ly1 S1 = a /\ errb_cap_cf S1 = ncap /\
  A_bytes (w_A W) + ncap - errb_cap_cf S <= abudget_cf S1.
Proof.
intros Hp ly S S1 W mem md mat a ncap TS IC AR XM LX MP CAPLE Ha Hn Hal G W1 EF Es md1 md2 ly1.
pose proof AR as (M & L & BU & MW & HS).
pose proof (amc_xs_placed _ _ _ _ _ M) as XP.
set (md0 := with_vm_backing (m_vm_lazy md) mat md) in *.
set (d := YG0ncf.errb_data_cf ly S) in *. set (oc := errb_cap_cf S) in *.
assert (XO : xs_cf ly S = [(d, oc)]) by exact (rr_xs_mapped ly S MP).
pose proof (cfxm_xs_pos ly S md MW XP XM) as XSz. rewrite XO in XSz. apply Forall_inv in XSz. cbn [fst snd] in XSz.
destruct (errb_grant_facts Hp ly S W mem md mat a ncap AR XM G Ha Hn ltac:(unfold kPage in *; lia)) as (GA & GAPP & GCE & GFA').
assert (GFA : Forall (zdisjoint (a, ncap)) (static_extents ly ++ sec_extents ly S ++ perm_maps ly ++ band_maps)).
{ apply Forall_forall. intros z Hz. apply (proj1 (Forall_forall _ _) GFA').
  apply in_app_iff in Hz as [Hz|Hz]; [apply in_or_app; left; exact Hz|]. apply in_or_app; right.
  apply in_app_iff in Hz as [Hz|Hz]; [apply in_or_app; left; exact Hz|]. apply in_or_app; right.
  apply in_app_iff in Hz as [Hz|Hz]; [apply in_or_app; left; exact Hz|]. apply in_or_app; right.
  apply in_or_app; left; exact Hz. }
assert (FX : Forall (zdisjoint (a, ncap)) (xs_cf ly S)).
{ apply Forall_forall. intros z Hz. apply (proj1 (Forall_forall _ _) GFA').
  do 4 (apply in_or_app; right). exact Hz. }
pose proof (proj1 (Forall_forall _ _) FX (d, oc) ltac:(rewrite XO; left; reflexivity)) as FXo. unfold zdisjoint in FXo. cbn [fst snd] in FXo.
assert (MD1 : md1 = mmap_model (w64 a) (w64 ncap) md0) by (unfold md1; apply with_mmap_backing_plain; exact rr_noreserve_34).
assert (Ua : bv_unsigned (w64 a) = a) by (apply w64_unsigned; lia).
assert (Un : bv_unsigned (w64 ncap) = ncap) by (apply w64_unsigned; lia).
pose proof alloc_ceiling_lt as CL. rr_ceil.
assert (Ud : bv_unsigned (w64 d) = d) by (apply w64_unsigned; unfold ASAN_CEIL in *; lia).
assert (Uo : bv_unsigned (w64 oc) = oc) by (apply w64_unsigned; unfold ASAN_CEIL in *; lia).
assert (RF : forall q, In q (vm_maps (m_vmmaps md0)) -> a + ncap <= bv_unsigned (fst q) \/ bv_unsigned (fst q) + bv_unsigned (snd q) <= a).
{ intros q Hq. pose proof G as G'. unfold grant_ok_na_pin in G'. apply andb_prop in G' as [_ G4].
  pose proof (YK13.region_free_In _ (w64 a) (Z_to_bv 64 ncap) (fst q) (snd q) G4 ltac:(apply in_app_iff; right; rewrite <- surjective_pairing; exact Hq)) as D.
  change (Z_to_bv 64 ncap) with (w64 ncap) in D. rewrite Ua, Un in D. exact D. }
assert (MW0 : amwf md0) by exact (amwf_same md md0 eq_refl eq_refl MW).
set (md1' := mmap_model (w64 a) (w64 ncap) md0) in *.
assert (MW1 : amwf md1') by (apply rr_amwf_mmap; [exact MW0 | lia | lia | unfold ASAN_CEIL in *; lia | exact RF]).
assert (MWF0 : YK0g.model_ivs_wf md0) by exact (rr_model_ivs_wf md0 MW0 (alc_top _ _ _ _ L)).
assert (MWF1 : YK0g.model_ivs_wf md1') by exact (rr_model_ivs_wf md1' MW1 (alc_top _ _ _ _ L)).
pose proof (eager_used_mmap_model (w64 a) (w64 ncap) md0 MWF0 ltac:(rewrite Ua, Un; unfold ASAN_CEIL in *; lia)) as EG1.
rewrite Ua, Un in EG1. fold md1' in EG1.
assert (VM1 : vm_maps (m_vmmaps md1') = wiv (a, ncap) :: vm_maps (m_vmmaps md)) by reflexivity.
assert (Hold : In (wiv (d, oc)) (vm_maps (m_vmmaps md1'))) by (rewrite VM1; right; apply XM; rewrite XO; left; reflexivity).
destruct (in_split _ _ Hold) as (l1 & l2 & EM).
destruct (eager_used_munmap (wiv (d, oc)) md1' l1 l2 MW1 EM) as [EG2 VM2]. cbn [wiv fst snd] in EG2, VM2.
rewrite Ud, Uo in EG2.
assert (PW1 := proj1 (proj2 (proj2 (proj2 (proj1 MW1))))). assert (NE1 := proj2 MW1).
assert (NEQ : forall q, In q (l1 ++ l2) -> fst q <> w64 d).
{ intros q Hq E. pose proof PW1 as PW1'. rewrite EM in PW1'. destruct (pairwise_app_mid _ l1 (wiv (d, oc)) l2 PW1') as [D1 D2].
  pose proof (NE1 q ltac:(rewrite EM; apply in_app_iff in Hq as [?|?]; apply in_app_iff; [left|right; right]; assumption)) as Pq.
  apply in_app_iff in Hq as [Hq|Hq]; [pose proof (D1 q Hq) as Dq | pose proof (D2 q Hq) as Dq];
  cbn [wiv fst snd] in Dq; rewrite ?E, ?Ud, ?Uo in Dq; lia. }
pose proof (rr_munmap_parts (w64 d) (w64 oc) md1') as (R1 & R2 & R3 & R4).
assert (KEEP : forall q, In q (vm_maps (m_vmmaps md)) -> Forall (fun e => fst q <> w64 (fst e)) (xs_cf ly S) -> In q (vm_maps (m_vmmaps md2))).
{ intros q Hq Hf. rewrite XO in Hf. apply Forall_inv in Hf. cbn [fst] in Hf. unfold md2. rewrite MD1. fold md1'. rewrite VM2.
  assert (Hq1 : In q (vm_maps (m_vmmaps md1'))) by (rewrite VM1; right; exact Hq). rewrite EM in Hq1.
  apply in_app_iff in Hq1 as [Hq1|[Hq1|Hq1]]; [apply in_app_iff; left; exact Hq1 | exfalso; apply Hf; rewrite <- Hq1; reflexivity | apply in_app_iff; right; exact Hq1]. }
assert (MD2 : md2 = munmap_model (w64 d) (w64 oc) md1') by (unfold md2; rewrite MD1; reflexivity).
pose proof (rr_rel_core Hp ly S S1 W mem md md2 a ncap TS IC AR XM LX Ha Hn GA GAPP GCE GFA FX CAPLE W1 EF Es) as C.
rewrite MD2 in C |- *. rewrite MD2 in KEEP.
refine (C _ _ _ _ _ _ _ _ _ _ _).
- exact (munmap_amwf md1' (wiv (d, oc)) l1 l2 MW1 EM).
- rewrite R1. reflexivity.
- rewrite R2. reflexivity.
- rewrite R3. reflexivity.
- rewrite VM2. assert (Hn1 : In (wiv (a, ncap)) (vm_maps (m_vmmaps md1'))) by (rewrite VM1; left; reflexivity).
  rewrite EM in Hn1. apply in_app_iff in Hn1 as [Hn1|[Hn1|Hn1]]; [apply in_app_iff; left; exact Hn1 | exfalso | apply in_app_iff; right; exact Hn1].
  apply (f_equal fst) in Hn1. cbn [wiv fst] in Hn1. apply cfxm_w64_inj in Hn1; [| unfold ASAN_CEIL in *; lia | lia]. lia.
- exact KEEP.
- intros q Hq. rewrite VM2 in Hq. pose proof (NEQ q Hq) as Nq.
  assert (Hq1 : In q (vm_maps (m_vmmaps md1'))) by (rewrite EM; apply in_app_iff in Hq as [?|?]; apply in_app_iff; [left|right; right]; assumption).
  rewrite VM1 in Hq1. destruct Hq1 as [<-|Hq1]; [left; reflexivity | right; split; [exact Hq1 | rewrite XO; constructor; [exact Nq | constructor]]].
- intros x Hx. rewrite XO in Hx. apply Forall_inv in Hx. unfold in_zr in Hx. cbn [fst snd] in Hx.
  rewrite (cov_munmap (w64 d) (w64 oc) md1' x MWF1 ltac:(rewrite Ud, Uo; exact Hx)). reflexivity.
- rewrite XO, EG2, EG1.
  change (esec (vm_noaccess (m_vmmaps md1')) (m_vm_lazy md1') [(d, oc)]) with (esec (vm_noaccess (m_vmmaps md)) (m_vm_lazy md) [(d, oc)]).
  change (esec (vm_noaccess (m_vmmaps md0)) (m_vm_lazy md0) [(a, ncap)]) with (esec (vm_noaccess (m_vmmaps md)) (m_vm_lazy md) [(a, ncap)]).
  unfold md0. rewrite eager_used_wvb. lia.
- intros lo n0 H0. rewrite R4. apply region_free_subtract; [|exact H0].
  intros q Hq. exact (proj1 (proj2 (proj1 MW1)) q Hq).
- apply YGcfLazyMaps.lazy_in_maps_munmap_cf.
  + exact (YGcfLazyMaps.lazy_in_maps_mmap_cf (w64 a) (w64 ncap) md0 (alc_lazy_in_maps _ _ _ _ L)).
  + exact (proj1 (proj2 (YG0j.model_ivs_wf_parts md1' MWF1))).
  + exact (proj2 (proj2 (YG0j.model_ivs_wf_parts md1' MWF1))).
  + intros c Hc Ec. rewrite EM in Hc. apply in_app_iff in Hc as [Hc|[Hc|Hc]].
    * exfalso. exact (NEQ c ltac:(apply in_app_iff; left; exact Hc) Ec).
    * rewrite <- Hc. cbn [wiv snd]. lia.
    * exfalso. exact (NEQ c ltac:(apply in_app_iff; right; exact Hc) Ec).
Qed.

(* The errbuf extent is never in the allocator's owned set: aowned is inside static / secondary extents and the
   band (rr_zf_owned), and xs_placed_cf puts the extent apart from all of them. *)
Lemma errb_xs_not_aowned : forall Hp ly S rd a, ARmcf B ly S Hp rd ->
  Exists (in_zr a) (xs_cf ly S) -> ~ aowned B ly S a.
Proof.
intros Hp ly S rd a M Hx O. pose proof (rr_zf_owned ly S Hp _ a M O) as Z.
apply Exists_exists in Hx as (e & He & Hin).
destruct (proj1 (Forall_forall _ _) (amc_xs_placed _ _ _ _ _ M) e He) as (_ & OA & _ & OD).
pose proof (proj1 (Forall_app _ _ _) OD) as [ODc ODr]. pose proof (proj1 (Forall_app _ _ _) ODr) as [ODs _].
destruct e as [d oc]. unfold in_zr in Hin. cbn [fst snd] in Hin. exact (rr_zf_apart ly S d oc a OA ODs ODc Z Hin).
Qed.

(* No stack byte is owned (YG0scf.AR_stack_law_ok_cf, which reads only the ARmcf part of the relation). *)
Lemma rr_stack_not_owned : forall ly S Hp rd a, ARmcf B ly S Hp rd -> ly_stk_lo ly <= a < ly_stk_hi ly -> ~ aowned B ly S a.
Proof.
intros ly S Hp rd a M Ha [OW _]. pose proof (amc_layout _ _ _ _ _ M) as LO. pose proof (lo_top _ LO) as TOP.
destruct OW as [O|[O|[O|[O|O]]]].
- pose proof (owned_static_bound B a (amc_syms _ _ _ _ _ M) O). unfold kImgEnd, kHighMemBeg in *. lia.
- exact (proj1 (proj2 (owned_extents_bound ly a LO O)) Ha).
- apply (proj1 (proj2 (owned_extents_bound ly a LO ltac:(apply Exists_exists; exists (ly_C ly, 256); split; [unfold owned_extents; cbn; tauto | exact O]))) Ha).
- exact (proj1 (proj2 (owned_sec_bound_cf B ly S Hp _ a M O)) Ha).
- pose proof (owned_shadow_bound_cf B ly S Hp _ a M O). lia.
Qed.

End a.
