(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: from proofs/cgif/cgif_file_fuzzer/lib/RepAppTcf.v (commit 3cae605a900a, blob 6139fc6582f4) onto omx-clap-core/fuzz_preset's asan image (unstripped fuzz_preset.asan, sha256 bff8519bbe3e; pin 1be0f53d96cb), from cgif_file_fuzzer asan-ubsan ce511d541cda (pin 1c29845fe605), the cf layer at part 3c; module paths changed; 0 image numerals moved by port_addr_check 3d2eee813cce MAPS predictions and the twins' symbol + offset map (0 model labels and sizes kept); no other numeral changed; comments removed (the source file keeps them). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK11 YK04 YK0v YK13 YA0i YA0n.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YA09 YG0h.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import AB1v AF0m AF0x.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfNames YG01cf YG00cf YG0ncf YG0dcf YGcfXs YG06bcf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfInstBase.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import RepIFcf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfTok.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YK0g YGcfAbudget YGcfRoomCf YGcfCker.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require RepRelcf RepGrantcf RepGluecf RepAppWcf RepRelXcf CfImgA.
From Stdlib Require Import List.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require PresetRelroGeoA.
Import ListNotations.
Open Scope Z_scope.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams}.
Variable B : asyms.

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

  exists a. exact Ha.
- pose proof (amc_wf _ _ _ _ _ (proj1 AR)) as WF.
  pose proof cf_nob_ok as NB.
  apply (YGcfCker.room_wA_cf tfibsegs B ly S Hp W mem md nZ AR (YGcfRoomCf.room_rec_cf_of_live _ ly S md WF QL HT)).
  unfold YGcfAbudget.CF_HEAD. lia.
Qed.

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

Lemma aledger_of_pre : forall lk Hp ly S W mem md, errb_call_pre B lk Hp ly S W mem md -> RepRelcf.ALEDGER_X ly S md.
Proof.
intros lk Hp ly S W mem md PRE. pose proof PRE as (_ & _ & _ & _ & _ & _ & (_ & AR & _) & _).
exact (RepRelcf.aledger_x_of_ledger ly S md (proj1 (proj2 AR))).
Qed.

Theorem append_ok : (TfibSyms B -> pf_cells_apart_t B) -> append_spec_cf B.
Proof.
intros PFA. exact (RepAppWcf.append_ok_w B errb_map_fits_of_pre glazy_of_pre aledger_of_pre PFA).
Qed.

End a.

Theorem append_ok_preset {fx : YK11.FPState} {rc : YM05.RunCeil} {cp : CfParams} (B : asyms) :
  @append_spec_cf fx rc CfImgA.CfImg_A cp B.
Proof. exact (append_ok B (PresetRelroGeoA.pf_cells_apart_preset_A B)). Qed.

Check @append_ok.
Print Assumptions append_ok.
Print Assumptions append_ok_preset.
