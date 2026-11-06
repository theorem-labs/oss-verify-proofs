(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: from proofs/cgif/cgif_file_fuzzer/lib/RepAppTcf.v (commit f01d79f3fb5, cf refill round 3; file sha256 7ca6f57970d9) onto plugin-hostd/fuzz_reply's asan image (unstripped fuzz_reply.asan, sha256 d751b179ea49; pin 42c58610e125); module paths changed; its 0 image addresses moved by function pairs the comparison kit cmpkit 86da41d3ef68 calls the same code (strictcmp3 65688e94214a, by funcpair_reply 6963bc4a94fc on the cgif twin ce511d541cda; 0 port_addr_check e55e1b52a8a0 MAPS predictions, each code one re-derived by the pair, each data one a pc-relative target of both paired functions; 0 code pcs the tool read as sizes, by the pair), and 1 pcs named in comments; no other numeral changed. *)
(* Theorem Labs, 2026-10-30 (a Theorem Labs lane, slice F4 of a Theorem Labs lane's class-full report walk): the slice's theorem.
   __asan::AppendToErrorMessageBuffer (0x563c0) of cgif_file_fuzzer's asan-ubsan image (pin 1c29845fe605)
   realizes the model step errb_append_cf (YG00cf.v:133): RepIFcf.append_spec_cf, which this file never edits.
   The walk is RepAppWcf.append_ok_w; this file discharges its three premises from the call premise alone:
   - the forced grant: the placement from the cf relation (RepGrantcf, over CfParams' cf_sec_live_place_lt) and
     the room from a Theorem Labs lane's YGcfCker.room_wA_cf at the room of record, which errb_call_pre's Wf_cf, qloose and
     cf_hull_ok give (YGcfRoomCf.room_rec_cf_of_live);
   - no page of a granted map is lazy: ALedger_cf's alc_lazy_in_maps puts every lazy address in a map, and the
     grant is free of every map;
   - the eager ledger: ALedger_cf's alc_eager_x is RepRelcf.ALEDGER_X (RepRelcf.aledger_x_of_ledger).
   rule 24: proves function __asan::AppendToErrorMessageBuffer (reuse search: ossv proof index v5 built
   2026-10-30T01:54:20Z and 02:28:20Z over main / ossv/recipes / ossv/candidates /
   release/pau-projects-recipes plus the delivered package and the live cold/* working heads;
   `proof-index VSNPrintf Printf SharedPrintfCode AppendNumber AppendToErrorMessageBuffer MmapOrDie`
   2026-10-30T02:25:54Z exit 0 and `proof-index UnmapOrDie internal_memset internal_memcpy
   internal_strlen GetNamedMappingFd IncreaseTotalMmap` 2026-10-30T02:55Z exit 3; 0 released lemma(s) for
   every name; rule-24 check RepLookupCheck CONFIRM, nothing reusable). *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK11 YK04 YK0v YK13 YA0i YA0n.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YA09 YG0h.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import AB1v AF0m AF0x.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YGcfNames YG01cf YG00cf YG0ncf YG0dcf YGcfXs YG06bcf.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import YGcfInstBase RepIFcf.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YGcfTok.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YK0g YGcfAbudget YGcfRoomCf YGcfCker.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require RepRelcf RepGrantcf RepGluecf RepAppWcf RepRelXcf CfImgA.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require ReplyImgRefillA ReplyImgRowsA ReplyRelroGeoA.
From Stdlib Require Import List.
Import ListNotations.
Open Scope Z_scope.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams}.
Variable B : asyms.

(* The forced grant at the errbuf map: the placement from the cf relation, the room from the room of record. *)
Lemma errb_map_fits_of_pre :
  forall (Hp : list Z) (ly : alayout) (S : astate) (W : world tfibsegs) (mem : word -> option byte)
    (md : Model) (nZ : Z),
  layout_ok ly -> img_cover ly -> TfibSyms B -> ly_tsd ly = TFIB_TSD ->
  ARcf tfibsegs B ly S Hp W mem md -> xs_mapped_cf ly S md -> qloose S -> cf_hull_ok S ->
  0 < nZ -> nZ mod kPage = 0 -> nZ <= cf_nob ->
  (exists a, YK13.grant_ok_na_pin md a nZ = true) /\
  eager_used md + A_bytes (w_A W) + nZ <= vm_limit (m_vmmaps md).
Proof.
intros Hp ly S W mem md nZ LY IMG TS TSD AR XM QL HT Hpos Hal Hnob. split.
- destruct (RepGrantcf.errb_grant_exists_cf B Hp ly S W mem md [] nZ AR (conj Hpos Hnob)) as [a Ha].
  (* grant_ok_na_pin reads only m_vmmaps, which with_vm_backing keeps (YK04.m_vmmaps_wvb). *)
  exists a. exact Ha.
- pose proof (amc_wf _ _ _ _ _ (proj1 AR)) as WF.
  pose proof cf_nob_ok as NB.
  apply (YGcfCker.room_wA_cf tfibsegs B ly S Hp W mem md nZ AR (YGcfRoomCf.room_rec_cf_of_live _ ly S md WF QL HT)).
  unfold YGcfAbudget.CF_HEAD. lia.
Qed.

(* No page of a granted errbuf map is lazy: a lazy page is covered by a map (alc_lazy_in_maps), and the grant is
   free of every map (grant_ok_na_pin's region_free). *)
Lemma glazy_of_pre : forall lk Hp ly S W mem md n, errb_call_pre B lk Hp ly S W mem md -> 0 < n -> n mod 4096 = 0 ->
  forall (a2 : Z) (pg : word), YK13.grant_ok_na_pin md (w64 a2) n = true -> a2 <= bv_unsigned pg ->
  bv_unsigned pg + page_size <= a2 + n -> page_in_ranges pg (m_vm_lazy md) = false.
Proof.
intros lk Hp ly S W mem md n PRE Hn Hal a2 pg G H1 H2.
pose proof PRE as (_ & _ & _ & _ & _ & _ & (_ & AR & _) & _).
pose proof (YGcfCker.ARcf_lazy_in_maps_cf _ _ _ _ _ _ _ _ AR) as LZ.
pose proof (bv_unsigned_in_range 64 pg) as Rp. change (bv_modulus 64) with (2 ^ 64) in Rp.
pose proof (@YG0f.ASAN_CEIL_range _) as [[_ CEIL] _].
set (a' := bv_unsigned (w64 a2)).
assert (A' : a' = a2 mod 2 ^ 64).
{ unfold a', w64. rewrite Z_to_bv_unsigned. unfold bv_wrap. reflexivity. }
assert (Ra' : 0 <= a' < 2 ^ 64) by (rewrite A'; apply Z.mod_pos_bound; lia).
assert (Ga' : YK13.grant_ok_na_pin md (w64 a') n = true).
{ unfold a', w64. rewrite Z_to_bv_bv_unsigned. exact G. }
destruct (RepGluecf.rep_grant_below_ceil B lk Hp ly S W mem md n PRE Hn Hal a' Ra' Ga') as [CE _].
pose proof (Z.div_mod a2 (2 ^ 64) ltac:(lia)) as DM. rewrite <- A' in DM.
assert (E : a2 = a').
{ destruct (Z_lt_le_dec a2 0) as [Lt|Le].
  - exfalso. assert (Q : a2 / 2 ^ 64 < 0) by (apply Z.div_lt_upper_bound; lia). unfold page_size in H2. lia.
  - destruct (Z_lt_le_dec a2 (2 ^ 64)) as [Lt2|Ge]; [|exfalso; lia].
    rewrite A'. symmetry. apply Z.mod_small. lia. }
rewrite <- E in Ga', CE.
destruct (page_in_ranges pg (m_vm_lazy md)) eqn:EP; [exfalso | reflexivity].
apply YA09.page_in_ranges_true in EP as (iv & Hin & J1 & J2).
assert (C1 : YK0g.covered (vm_noaccess (m_vmmaps md) ++ m_vm_lazy md) (bv_unsigned pg) = true).
{ unfold YK0g.covered. apply existsb_exists. exists iv. split; [apply in_or_app; right; exact Hin|].
  unfold YK0g.in_iv, YK0g.in_rng, YK0g.B, YK0g.S. apply andb_true_intro.
  split; [apply Z.leb_le | apply Z.ltb_lt]; unfold page_size in *; lia. }
pose proof (LZ _ C1) as C2. unfold YK0g.covered in C2. apply existsb_exists in C2 as (c & Hc & Hi).
unfold YK0g.in_iv, YK0g.in_rng, YK0g.B, YK0g.S in Hi. apply andb_prop in Hi as [K1 K2].
apply Z.leb_le in K1. apply Z.ltb_lt in K2.
unfold YK13.grant_ok_na_pin in Ga'. apply andb_prop in Ga' as [_ G4].
pose proof (YK13.region_free_In _ (w64 a2) (Z_to_bv 64 n) (fst c) (snd c) G4
  ltac:(apply in_app_iff; right; rewrite <- surjective_pairing; exact Hc)) as D.
assert (Ua : bv_unsigned (w64 a2) = a2) by (apply YG0h.w64_unsigned; lia).
assert (Un : bv_unsigned (Z_to_bv 64 n) = n) by (apply (YG0h.w64_unsigned n); lia).
rewrite Ua, Un in D. unfold page_size in *. lia.
Qed.

(* The eager ledger at the call: ALedger_cf's alc_eager_x, read through the held memory's ARcf. *)
Lemma aledger_of_pre : forall lk Hp ly S W mem md, errb_call_pre B lk Hp ly S W mem md -> RepRelcf.ALEDGER_X ly S md.
Proof.
intros lk Hp ly S W mem md PRE. pose proof PRE as (_ & _ & _ & _ & _ & _ & (_ & AR & _) & _).
exact (RepRelcf.aledger_x_of_ledger ly S md (proj1 (proj2 AR))).
Qed.

(* Generic in the unit's CfImg: the one unit fact the walk takes is the layer's row YG0ncf.pf_cells_apart_t at the unit's
   symbols (field round 3; not an ARmcf field, so not reachable from errb_call_pre at a generic CfImg). *)
Theorem append_ok : (TfibSyms B -> pf_cells_apart_t B) -> append_spec_cf B.
Proof.
intros PFA. exact (RepAppWcf.append_ok_w B errb_map_fits_of_pre glazy_of_pre aledger_of_pre PFA).
Qed.

End a.

(* At cgif the row is the layer's YGcfImgcgif.pf_cells_apart_cgif. *)
Theorem append_ok_reply {fx : YK11.FPState} {rc : YM05.RunCeil} {cp : CfParams} (B : asyms) :
  @append_spec_cf fx rc CfImgA.CfImg_A cp B.
Proof. exact (append_ok B (ReplyRelroGeoA.pf_cells_apart_reply_A B)). Qed.

Check @append_ok.
Print Assumptions append_ok.
Print Assumptions append_ok_reply.
