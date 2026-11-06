From OSSVerify.Proofs.libreac.fuzz_pcap.lib Require Import SymAddr.
(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: new file for libreac/fuzz_pcap: the image side conditions of the harness's entry
   (lib/A/Prog/PcapEntryA.v G_HARNESS, PcapEntryDefs.v pe_base), proved from PcapSyms B (A/AF0m.v) over the ASan image
   tfibsegs (A/AB1v.v) by computation on the constant lists; no function walk.
   - pcap_G_harness_gx_ok: W_journalG.v's gx_ok for PcapEntryA.G_HARNESS, the harness's two .bss globals
     g_file_len [0x5d3f40, 0x5d3f48) and g_file [0x5d3f60, 0x5d3f68) (8-byte objects; their 24-byte ASan
     redzones are Tfib_owned_static rows, the objects are not): each byte is in a loaded segment and outside
     as_owned_static.
   - pcap_G_harness_pe_bytes: pe_base's per-byte conjunct over the same bytes (PcapEntryDefs.v pe_base, the
     `forall a, inG pe_G a -> ...` clause) at the pin: no byte of G_HARNESS is read-only (in_roP at PcapRelro's
     window), the AddrHashMap meta cell of PSourceK.pcap_KS, or errno.
   - pcap_hg_img_laws: the record hg_img_laws below at g_file_len / g_file and PcapRelro's window: every byte of
     AE3i.v's img_ro_chunks is in a read-only segment, and every byte of the two globals is in the image; neither
     is in as_owned_static nor in errno. *)
(* Modified by Theorem Labs, 2026-10: moved from a working branch 3c32fe5f906 (that branch is retired);
   Requires renamed to the current files (G_HARNESS is in lib/A/Prog/PcapEntryA.v, gx_ok / inG in lib/A/W_journalG.v),
   so the qualifier PcapEntry.G_HARNESS became PcapEntryA.G_HARNESS (the same definition, moved); no other statement or
   proof text changed. Every numeral re-measured by symbol + offset on the pin fuzz_pcap.asan (sha256
   b7a91d9b1fb0017df0462bf382b3211837851bf801e792673b1cee0797cdca2a), symbols from the unstripped twin; all equal the
   values below. g_file_len / g_file: ASan descriptors 2 and 3 in asan_globals (0x9e180 / 0x9e1c0) give beg 0x5d3f40 /
   0x5d3f60, size 8, size_with_redzone 32 (redzone 24; symbol size 32). errno's 4 bytes: __errno_location (0x88628) is
   tp - 0xa4, and each of its callers' first access through the result is lw / sw. The meta cell's 8 bytes: metadata_mem
   (0xa1108, symbol size 16) holds the AddrHashMap, whose acquire (0x47b2c) reads its table_ with ld at offset 0. *)
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import MemImageType.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YG0f YG0n YG0d YP09.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A.Stdio Require Import PSource PSourceK.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A Require Import AB1v AF0m AE3i.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A.Prog Require Import PcapBase PcapRelro.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A.Prog Require PcapEntryA.
(* The journal with program-global ranges: gx_ok / inG, in W_journalG.v (the image-free part of W_journal.v, a Theorem Labs lane's
   copy from fuzz_reply's working branch 6328acea202). *)
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A Require Import W_journalG.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

(* ---- range checks by computation ---- *)
(* A range r = (base, length) lies inside one loaded segment / one read-only loaded segment. *)
Definition rng_in_seg_b (segs : list Segment) (r : Z * Z) : bool :=
existsb (fun s => (Z.of_N (seg_base s) <=? fst r) && (fst r + snd r <=? Z.of_N (seg_base s) + Z.of_N (seg_size s))) segs.
Definition rng_ro_seg_b (segs : list Segment) (r : Z * Z) : bool :=
existsb (fun s => negb (seg_writable s) && (Z.of_N (seg_base s) <=? fst r) &&
  (fst r + snd r <=? Z.of_N (seg_base s) + Z.of_N (seg_size s))) segs.
(* Two ranges are disjoint. *)
Definition rng_disj_b (r r' : Z * Z) : bool := (fst r + snd r <=? fst r') || (fst r' + snd r' <=? fst r).
(* Each range of R: in a loaded segment (read-only if ro), disjoint from every range of L and from the 4 bytes at e. *)
Definition rngs_ok_b (ro : bool) (segs : list Segment) (L : list (Z * Z)) (e : Z) (R : list (Z * Z)) : bool :=
forallb (fun r => (if ro then rng_ro_seg_b segs r else rng_in_seg_b segs r) && forallb (rng_disj_b r) L && rng_disj_b r (e, 4)) R.

Lemma rng_in_seg_sound : forall segs r a, rng_in_seg_b segs r = true -> in_zr a r -> in_img segs a.
Proof.
intros segs r a H Ha. unfold rng_in_seg_b in H. apply existsb_exists in H as (s & Hs & Hb).
apply andb_prop in Hb as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2. unfold in_zr in Ha.
exists s. split; [exact Hs | lia].
Qed.
Lemma rng_ro_seg_sound : forall segs rlo rhi r a, rng_ro_seg_b segs r = true -> in_zr a r -> in_roP segs rlo rhi a.
Proof.
intros segs rlo rhi r a H Ha. unfold rng_ro_seg_b in H. apply existsb_exists in H as (s & Hs & Hb).
apply andb_prop in Hb as [Hb H2]. apply andb_prop in Hb as [Hw H1]. apply negb_true_iff in Hw.
apply Z.leb_le in H1. apply Z.leb_le in H2. unfold in_zr in Ha.
left. exists s. split; [exact Hs|]. split; [exact Hw | lia].
Qed.
Lemma rng_out_sound : forall L r a, forallb (rng_disj_b r) L = true -> in_zr a r -> ~ Exists (in_zr a) L.
Proof.
intros L r a H Ha HE. apply Exists_exists in HE as (r' & Hin & Ha').
pose proof (proj1 (forallb_forall _ _) H r' Hin) as Hd. unfold rng_disj_b, in_zr in *.
apply orb_prop in Hd as [Hd|Hd]; apply Z.leb_le in Hd; lia.
Qed.
Lemma rng_out1_sound : forall r e n a, rng_disj_b r (e, n) = true -> in_zr a r -> ~ (e <= a < e + n).
Proof.
intros r e n a H Ha He. unfold rng_disj_b, in_zr in *. cbn [fst snd] in *.
apply orb_prop in H as [H|H]; apply Z.leb_le in H; lia.
Qed.
(* What rngs_ok_b gives for one byte of one of its ranges. *)
Lemma rngs_ok_sound : forall ro segs L e R r a, rngs_ok_b ro segs L e R = true -> In r R -> in_zr a r ->
(if ro then rng_ro_seg_b segs r else rng_in_seg_b segs r) = true /\ ~ Exists (in_zr a) L /\ ~ (e <= a < e + 4).
Proof.
intros ro segs L e R r a H Hr Ha. pose proof (proj1 (forallb_forall _ _) H r Hr) as Hb.
apply andb_prop in Hb as [Hb He]. apply andb_prop in Hb as [Hs HL].
split; [exact Hs|]. split; [exact (rng_out_sound L r a HL Ha) | exact (rng_out1_sound r e 4 a He Ha)].
Qed.
(* A range lies in no read-only loaded segment. *)
Definition rng_not_ro_b (segs : list Segment) (r : Z * Z) : bool :=
forallb (fun s => seg_writable s || rng_disj_b r (Z.of_N (seg_base s), Z.of_N (seg_size s))) segs.
Lemma rng_not_ro_sound : forall segs r a, rng_not_ro_b segs r = true -> in_zr a r ->
~ (exists s, In s segs /\ seg_writable s = false /\ Z.of_N (seg_base s) <= a < Z.of_N (seg_base s) + Z.of_N (seg_size s)).
Proof.
intros segs r a H Ha (s & Hs & Hw & Hr). pose proof (proj1 (forallb_forall _ _) H s Hs) as Hb. cbn beta in Hb.
rewrite Hw in Hb. cbn [orb] in Hb. exact (rng_out1_sound r _ _ a Hb Ha Hr).
Qed.

(* ---- the harness's globals: W_journalG.v's gx_ok ---- *)
Lemma pcap_G_harness_gx_ok : forall B, PcapSyms B -> gx_ok tfibsegs B PcapEntryA.G_HARNESS.
Proof.
intros B TB a Ha. rewrite (ts_owned B TB).
assert (C : rngs_ok_b false tfibsegs Tfib_owned_static TFIB_ERRNO PcapEntryA.G_HARNESS = true) by (vm_compute; reflexivity).
unfold inG in Ha. apply Exists_exists in Ha as (r & Hr & Ha).
destruct (rngs_ok_sound false _ _ _ _ r a C Hr Ha) as (Hs & Ho & _).
split; [exact (rng_in_seg_sound _ r a Hs Ha) | exact Ho].
Qed.

(* ---- the harness's globals: pe_base's per-byte conjunct (PcapEntryDefs.v pe_base) at the pin ---- *)
(* On the pin pe_G is G_HARNESS (PcapEntryDefs.pe_G_pin), pa_relro_lo / pa_relro_hi are PcapRelro's window and KS is
   PSourceK.pcap_KS (its meta cell is computed from pcap_KS, not written here). *)
Lemma pcap_G_harness_pe_bytes : forall B, PcapSyms B -> forall a, inG PcapEntryA.G_HARNESS a ->
~ in_roP tfibsegs PCAP_RLO PCAP_RHI a /\ ~ (as_meta_mem pcap_KS <= a < as_meta_mem pcap_KS + 8) /\
~ (as_errno B <= a < as_errno B + 4).
Proof.
intros B TB a Ha. rewrite (ts_errno B TB).
assert (C : forallb (fun r => rng_not_ro_b tfibsegs r && rng_disj_b r (PCAP_RLO, PCAP_RHI - PCAP_RLO) &&
  rng_disj_b r (as_meta_mem pcap_KS, 8) && rng_disj_b r (TFIB_ERRNO, 4)) PcapEntryA.G_HARNESS = true)
  by (vm_compute; reflexivity).
unfold inG in Ha. apply Exists_exists in Ha as (r & Hr & Ha).
pose proof (proj1 (forallb_forall _ _) C r Hr) as Hb. cbn beta in Hb.
apply andb_prop in Hb as [Hb He]. apply andb_prop in Hb as [Hb Hm]. apply andb_prop in Hb as [Hs Hl].
split; [|split; [exact (rng_out1_sound r _ _ a Hm Ha) | exact (rng_out1_sound r _ _ a He Ha)]].
intros [Hro | Hrel]; [exact (rng_not_ro_sound _ r a Hs Ha Hro)|].
apply (rng_out1_sound r _ _ a Hl Ha). lia.
Qed.

(* ---- the image laws of the harness's entry (a Theorem Labs lane) ---- *)
(* A byte of one of AE3i.v's read-only image chunks (img_ro_region's chunks). *)
Definition ro_chunk_addr (a : Z) : Prop :=
Exists (fun c => YP09.c_off c <= a < YP09.c_off c + YP09.c_len c) img_ro_chunks.
(* SEGS is the ASan image; every byte of a read-only chunk is read-only image (in_roP) and every byte of the two
   globals at alen / afile (8 bytes each) is image; none of them is an allocator static or an errno byte. *)
Record hg_img_laws (SEGS : list Segment) (B : asyms) (alen afile rlo rhi : Z) : Prop := {
hg_segs : SEGS = tfibsegs;
hg_ro : forall a, ro_chunk_addr a ->
  in_roP SEGS rlo rhi a /\ ~ Exists (in_zr a) (as_owned_static B) /\ ~ (as_errno B <= a < as_errno B + 4);
hg_glob : forall a, (alen <= a < alen + 8) \/ (afile <= a < afile + 8) ->
  in_img SEGS a /\ ~ Exists (in_zr a) (as_owned_static B) /\ ~ (as_errno B <= a < as_errno B + 4)
}.
(* The chunks as ranges. *)
Definition img_ro_ranges : list (Z * Z) := map (fun c => (YP09.c_off c, YP09.c_len c)) img_ro_chunks.
Lemma pcap_hg_ro : forall B, PcapSyms B -> forall a, ro_chunk_addr a ->
in_roP tfibsegs PCAP_RLO PCAP_RHI a /\ ~ Exists (in_zr a) (as_owned_static B) /\ ~ (as_errno B <= a < as_errno B + 4).
Proof.
intros B TB a Ha. rewrite (ts_owned B TB), (ts_errno B TB).
assert (C : rngs_ok_b true tfibsegs Tfib_owned_static TFIB_ERRNO img_ro_ranges = true) by (vm_compute; reflexivity).
unfold ro_chunk_addr in Ha. apply Exists_exists in Ha as (c & Hc & Ha).
assert (Hr : In (YP09.c_off c, YP09.c_len c) img_ro_ranges) by (unfold img_ro_ranges; exact (in_map _ _ _ Hc)).
assert (Ha' : in_zr a (YP09.c_off c, YP09.c_len c)) by (unfold in_zr; cbn [fst snd]; exact Ha).
destruct (rngs_ok_sound true _ _ _ _ _ a C Hr Ha') as (Hs & Ho & He).
split; [exact (rng_ro_seg_sound _ _ _ _ a Hs Ha') | split; [exact Ho | exact He]].
Qed.
Lemma pcap_hg_glob : forall B, PcapSyms B -> forall a, ((symaddr Symbols.Asan.s_g_file_len) <= a < (symaddr Symbols.Asan.s_g_file_len) + 8) \/ ((symaddr Symbols.Asan.s_g_file) <= a < (symaddr Symbols.Asan.s_g_file) + 8) ->
in_img tfibsegs a /\ ~ Exists (in_zr a) (as_owned_static B) /\ ~ (as_errno B <= a < as_errno B + 4).
Proof.
intros B TB a Ha. rewrite (ts_owned B TB), (ts_errno B TB).
assert (C : rngs_ok_b false tfibsegs Tfib_owned_static TFIB_ERRNO PcapEntryA.G_HARNESS = true) by (vm_compute; reflexivity).
assert (Hr : exists r, In r PcapEntryA.G_HARNESS /\ in_zr a r).
{ destruct Ha as [Ha|Ha]; [exists ((symaddr Symbols.Asan.s_g_file_len), 8) | exists ((symaddr Symbols.Asan.s_g_file), 8)];
  (split; [unfold PcapEntryA.G_HARNESS; cbn [In]; first [now left | now (right; left)] | unfold in_zr; cbn [fst snd]; lia]). }
destruct Hr as (r & Hr & Ha').
destruct (rngs_ok_sound false _ _ _ _ r a C Hr Ha') as (Hs & Ho & He).
split; [exact (rng_in_seg_sound _ r a Hs Ha') | split; [exact Ho | exact He]].
Qed.
(* alen = g_file_len (0x5d3f40), afile = g_file (0x5d3f60): PcapEntryA.G_HARNESS; rlo / rhi: PcapRelro's window. *)
Lemma pcap_hg_img_laws : forall B, PcapSyms B -> hg_img_laws tfibsegs B (symaddr Symbols.Asan.s_g_file_len) (symaddr Symbols.Asan.s_g_file) PCAP_RLO PCAP_RHI.
Proof.
intros B TB. split; [reflexivity | exact (pcap_hg_ro B TB) | exact (pcap_hg_glob B TB)].
Qed.
