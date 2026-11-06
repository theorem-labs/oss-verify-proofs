(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: the allocator-rule subset of cgif c8557374ad2e lib/A/ACed.v:27-104 (tfibX_lib :40,
   tfibX_LAWS :73, tfibX_ML :74-75, tfibX_env :76, tfibX_AMALLOC4 / tfibX_AFREE4 / tfibX_AFREEN4 :102-104), stated for
   libreac/fuzz_pcap's ASan build at B := PcapB (lib/A/AD2l.v) and segs := tfibsegs (lib/A/AB1v.v, = Asan.M.loaded_segments).
   Adapted:
   - TfibLib and tl_env are lib/A/ACeh.v's, as in the donor (ACed.v:15 imports ACeh); ACeh.tl_env gives YCbq.api_env,
     the form YCbp's *_triv lemmas take. lib/A/ACeg.v's record has the same fields.
   - tl_errno_img: TFIB_ERRNO (A/AF0m.v) is in fuzz_pcap's fourth loaded segment, Asan.Asan_segment_003 (the donor
     takes cgif's segment 3 through its (base, size) literals, ACed.v:45); here the segment is named, not its numbers.
   - tl_lib_consts: lib_const_addr is False for fuzz_pcap (ACeh.v header: its walked program reads no library
     constant cell), so the donor's tfibX_lib_consts_chk (ACed.v:36-39) has no counterpart.
   - The donor's AMALLOC / AFREE (ACed.v:100-101) are lib/A/AF0w.v pcap_amalloc_realizes and lib/A/AF0q.v
     pcap_afree_realizes, the same closures (tfib_amalloc_realizes / afree_realizes_closed at PcapB, PcapB_syms).
   - The three rules are stated for every sink head SK, passed by name: the donor lets instance search pick it.
   - The donor's PB_tfib / PALib / sink-image parts of ACed.v are not part of this file. *)
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OSSVerify.libreac.fuzz_pcap.images Require Import Asan.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YK11 YK04 YA0i YA0n.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0s YG0d YG05 YG0q.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YCbq YI16 YC5d YCbp.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YF0p.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A Require Import AB1v AF0l AF0m ACej ACeh AD2l AF0w AF0q.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
(* donor ACed.v:102-104 segs_low argument: A/ACeh.v tfib_segs_low (the same lemma as A/ACeg.v:81). *)
Definition PcapB_segs_low : forall a, in_img tfibsegs a -> 0 <= a < kLowMemEnd := tfib_segs_low.
(* donor ACed.v:40 tfibX_lib, at PcapB. *)
Theorem PcapB_lib : TfibLib PcapB.
Proof.
constructor.
- reflexivity.
- reflexivity.
- reflexivity.
- reflexivity.
- reflexivity.
- cbn [as_errno PcapB]. unfold TFIB_ERRNO, kLowMemEnd. lia.
- intros a Ha. cbn [as_errno PcapB] in Ha. unfold TFIB_ERRNO in Ha. unfold in_img.
  exists Asan.Asan_segment_003. split; [do 3 right; left; reflexivity|]. cbn. lia.
- reflexivity.
- intros a Ha. unfold lib_const_addr in Ha. destruct Ha.
- cbn [as_gp PcapB]. unfold TFIB_GP. lia.
Qed.
(* donor ACed.v:76 tfibX_env. *)
Definition PcapB_env : api_env tfibsegs PcapB := tl_env PcapB PcapB_lib.
(* donor ACed.v:74-75 tfibX_ML. *)
Lemma PcapB_ML : model_laws (as_universe PcapB).
Proof. exact (model_laws_ok (as_universe PcapB) (ts_universe PcapB PcapB_syms)). Qed.
Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
(* donor ACed.v:73 tfibX_LAWS. *)
Definition PcapB_LAWS : AR_laws tfibsegs PcapB := AR_laws_ok tfibsegs PcapB.
(* donor ACed.v:102-104 tfibX_AMALLOC4 / tfibX_AFREE4 / tfibX_AFREEN4. SK is passed by name: lib/Reusable/YI5b.v's
   global instance src0_sink_head must not stand in for it. *)
Definition PcapB_AMALLOC4 : amalloc04_rule (SK := SK) tfibsegs PcapB ameter_triv :=
  amalloc04_rule_triv (SK := SK) tfibsegs PcapB PcapB_segs_low PcapB_env PcapB_LAWS PcapB_ML (pcap_amalloc_realizes rc fx).
Definition PcapB_AFREE4 : afree04_rule (SK := SK) tfibsegs PcapB ameter_triv :=
  afree04_rule_triv (SK := SK) tfibsegs PcapB PcapB_segs_low PcapB_env PcapB_LAWS PcapB_ML (pcap_afree_realizes rc fx).
Definition PcapB_AFREEN4 : afree_null04_rule (SK := SK) tfibsegs PcapB ameter_triv :=
  afree_null04_rule_triv (SK := SK) tfibsegs PcapB PcapB_segs_low PcapB_env PcapB_LAWS PcapB_ML (pcap_afree_realizes rc fx).
End b.
