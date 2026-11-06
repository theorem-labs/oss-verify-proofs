(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: these two lines are the source header of lib/A/Prog/PaGxSites.v, whose lemma
   aj_gx_entry_at (:70-174) this file copies as kr_gx_entry with one conjunct (same_but_materialized) kept in its post;
   the rest of the file is new. *)
(* The body of the record loop of fuzz_pcap's entry function LLVMFuzzerTestOneInput on the ASan build of libreac
   v1.9.0 (lib/A): from the cut PP_KR (0x80b70, the head of the harness's skip loop) to the cut PP_KL2 (0x80fa4,
   the loop's own pcap_source_next returned). This file proves

     pe_KR : forall POST n, at_cut (GI_KL2 B MT KS) POST n -> at_cut (GI_KR B MT KS) POST (S n)

   (at_cut, hw_meas: lib/A/Prog/PcapHarnessWalk.v; GI_KR / GI_KL2: lib/A/Prog/PcapEntryPhases.v, frozen), which
   lib/A/Prog/PcapHarnessWalkR.v takes as its Section hypothesis KR. at_cut is used through the notation
   (@PcapHarnessWalk.at_cut _ SK PI B MT KS), as PcapHarnessWalkR.v names it.

   Section hypotheses: SK (explicit), PI, B, MT, KS; LAWS = AR_laws SEGS B, TL = PALib B, MTL = ameter_laws MT,
   RO = ro_below_ofl SEGS pa_relro_lo pa_relro_hi (explicit), HGX = gx_ok SEGS B pe_G,
   NEXT = tpcap_source_next_specX SK SEGS pa_relro_lo pa_relro_hi NX_STK B MT KS (BASE + AF_pcap_source_next)
   (lib/A/Prog/PcapSourceNextDefs.v), ABCMP = abcmp_realizes SEGS B (SIGMA PS___interceptor_trampoline_bcmp),
   ASIL = asource_img_laws SK SEGS B KS. MTL and RO were added with the owner's yes (a Theorem Labs lane, 05:47Z): NEXT's post
   gives mo_le MT Sc S2 0 only (GI_KL2 needs mo_le_trans, a field of ameter_laws), and NEXT's arodata_okP premise at
   the call comes from pe_base only by PcapBase.arodata_ok_journalP, which needs RO; pe_C carries the same two.

   Every number below is read from the pin fuzz_pcap.asan (sha256 b7a91d9b1fb0017d...; symbols from
   its unstripped twin fuzz_pcap.asan (sha256 36da3052c383), capstone disassembly); listing offsets are from the function's start
   0x80738. The owner's listing (a Theorem Labs lane's fkr-dis-0x80b34-0x81080.txt (sha256 6acef39df26d; internal record)) agrees with this disassembly on every
   instruction this file uses.

   The walk.
     kr_skip   0x80b70 .. 0x80c30, the skip loop (its own induction, in pe_KR, on |F| - e): the incl field of the
               record at e (bytes e+8 .. e+11, swapped when the file is), an empty record (0x80c1c) and a record
               larger than cap (0x80c20) skipped along the reader's skip chain p_skips, the back edge 0x80c30; the
               record found (0 < incl <= cap) is psn_q p (PWalk.skips_exit), seated at 0x80c68 (GI_KREC).
     kr_rec    0x80c68 .. the bcmp calls: the record fits the file, last_orig_len, the vlan tag (incl >= 18 and
               bytes 28 / 29 = 0x81 / 0), last_vlan_tagged, the reader's answer (incl - 4 tagged, incl untagged);
               then bcmp(buf, copy + 16, 12) at 0x80d8c (tagged) or bcmp(buf, copy + 16, incl) at 0x80e08.
     kr_tag1   0x80d90: bcmp(buf + 12, copy + 32, incl - 16) at 0x80da8.
     kr_tag2   0x80dac: last_vlan_id against bytes 30 / 31 (0x80df8), then 0x80e10.
     kr_untag  0x80e0c: on to 0x80e10.
     kr_ts     0x80e10 .. 0x80fa0: ts against sec * 10^6 + usec (bytes 0 .. 7), ts := -1 (0x80f80), at += 16 + incl,
               the call pcap_source_next(&ps, buf, cap) at 0x80fa0.
     kr_next   the call and the return to PP_KL2 (0x80fa4): GI_KL2 at the new position psn_q p + 16 + incl, the
               measure step (|F| - e) - (16 + incl) <= n.
     kr_bcmp   each bcmp call, by ABCMP inside the harness's ajournal_gx: the buffer holds the reader's record bytes
               (p_reader's rec_bytes) and the copy holds the file (p_copy), so the wrapper answers 0.

   The exits to PP_abort 0x81340, each refuted inside the walk (GI_abort is reached by no run):
     0x80c34: refuted by kr_skip at PcapHarnessWalkKR.v:1169, from GI_KR's p_skips e (psn_q p) and
              p_kind (psn_q p) = KFit (kr_m_empty / kr_m_big: e + 16 + incl + 16 <= |F| on the chain).
     0x80c6c: refuted by kr_rec at PcapHarnessWalkKR.v:2820, from p_kind (psn_q p) = KFit (PWalk.kind_fit:
              psn_q p + 16 + incl <= |F|).
     0x80d14: refuted by kr_rec at PcapHarnessWalkKR.v:2820, from p_reader's last_orig_len = PSN.orig
              (kb_le32w_U / kb_be32w_U at PcapHarnessWalkKR.v:297 / :324).
     0x80d68: refuted by kr_rec at PcapHarnessWalkKR.v:2820, from p_reader's last_vlan_tagged = PSN.tagged.
     0x80d80: refuted by kr_rec at PcapHarnessWalkKR.v:2820, from a2 = p_res = rec_len (kr_res_fit at :2754).
     0x80d90: refuted by kr_tag1 at PcapHarnessWalkKR.v:2673, from kr_bcmp's a0 = 0 (ABCMP, kr_cmp_ms3 at
              :2530, kr_recb_tag12 at :2385).
     0x80dac: refuted by kr_tag2 at PcapHarnessWalkKR.v:2605, from kr_bcmp's a0 = 0 (kr_recb_tagmid at
              :2394).
     0x80df8: refuted by kr_tag2 at PcapHarnessWalkKR.v:2605, from p_reader's last_vlan_id = PSN.rec_vid
              (kr_vid_U at :2499).
     0x80e00: refuted by kr_rec at PcapHarnessWalkKR.v:2820, from a2 = p_res = rec_len = incl (kr_res_fit).
     0x80e0c: refuted by kr_untag at PcapHarnessWalkKR.v:2445, from kr_bcmp's a0 = 0 (kr_recb_untag at
              :2381).
     0x80f74: refuted by kr_ts at PcapHarnessWalkKR.v:2256, from p_reader's ts = PSN.rec_ts (kr_tsT_U at
              :938).

   The 20 ASan shadow checks of the copy's bytes, by the entry edge (the body's bnez on the shadow byte); each slow
   block is never entered: the seat's sh_ok entry for the copy makes the token engine read the shadow byte as 0, so
   the bnez falls through. The premise is range_addressable (aview SEGS (w_H W) mem) SHADOW_OFF (b + e + lo) (hi - lo)
   for the copy block (b, |F|) of the cut, from AR's block shadow law (obl_of_block, Reusable/YCbq.v:2777), carried
   by kr_shok at PcapHarnessWalkKR.v:741. Slow blocks and tails checked on the pin (the owner's triples).
     0x80b84 (-> 0x80c38 -> bge 0x80c3c): refuted by kr_skip at PcapHarnessWalkKR.v:1169, from kr_shok (copy e+8 .. e+12).
     0x80b9c (-> 0x80c44 -> bge 0x80c48): refuted by kr_skip at PcapHarnessWalkKR.v:1169, from kr_shok (copy e+8 .. e+12).
     0x80bb4 (-> 0x80c50 -> bge 0x80c54): refuted by kr_skip at PcapHarnessWalkKR.v:1169, from kr_shok (copy e+8 .. e+12).
     0x80bcc (-> 0x80c5c -> bge 0x80c60): refuted by kr_skip at PcapHarnessWalkKR.v:1169, from kr_shok (copy e+8 .. e+12).
     0x80c84 (-> 0x80fb4 -> bge 0x80fb8): refuted by kr_rec at PcapHarnessWalkKR.v:2820, from kr_seat_now at :1509 (copy Q .. Q+L).
     0x80c9c (-> 0x80fc0 -> bge 0x80fc4): refuted by kr_rec at PcapHarnessWalkKR.v:2820, from kr_seat_now at :1509.
     0x80cb4 (-> 0x80fcc -> bge 0x80fd0): refuted by kr_rec at PcapHarnessWalkKR.v:2820, from kr_seat_now at :1509.
     0x80ccc (-> 0x80fd8 -> bge 0x80fdc): refuted by kr_rec at PcapHarnessWalkKR.v:2820, from kr_seat_now at :1509.
     0x80d30 (-> 0x81044 -> bge 0x81048): refuted by kr_rec at PcapHarnessWalkKR.v:2820, from kr_seat_now at :1509 (L = 32).
     0x80d50 (-> 0x81068 -> blt 0x8106c, jal __asan_report_load1 0x81070): refuted by kr_rec at PcapHarnessWalkKR.v:2820,
              from kr_seat_now at :1509 (L = 32).
     0x80dc8 (-> 0x81050 -> bge 0x81054): refuted by kr_tag2 at PcapHarnessWalkKR.v:2605, from kr_seat_now at :1509.
     0x80de0 (-> 0x8105c -> bge 0x81060): refuted by kr_tag2 at PcapHarnessWalkKR.v:2605, from kr_seat_now at :1509.
     0x80e28 (-> 0x80fe4 -> bge 0x80fe8): refuted by kr_ts at PcapHarnessWalkKR.v:2256, from kr_seat_now at :1509.
     0x80e40 (-> 0x80ff0 -> bge 0x80ff4): refuted by kr_ts at PcapHarnessWalkKR.v:2256, from kr_seat_now at :1509.
     0x80e58 (-> 0x80ffc -> bge 0x81000): refuted by kr_ts at PcapHarnessWalkKR.v:2256, from kr_seat_now at :1509.
     0x80e70 (-> 0x81008 -> bge 0x8100c): refuted by kr_ts at PcapHarnessWalkKR.v:2256, from kr_seat_now at :1509.
     0x80ec8 (-> 0x81014 -> bge 0x81018): refuted by kr_ts at PcapHarnessWalkKR.v:2256, from kr_seat_now at :1509.
     0x80ee0 (-> 0x81020 -> bge 0x81024): refuted by kr_ts at PcapHarnessWalkKR.v:2256, from kr_seat_now at :1509.
     0x80ef8 (-> 0x8102c -> bge 0x81030): refuted by kr_ts at PcapHarnessWalkKR.v:2256, from kr_seat_now at :1509.
     0x80f10 (-> 0x81038 -> bge 0x8103c): refuted by kr_ts at PcapHarnessWalkKR.v:2256, from kr_seat_now at :1509.
   The other ASan accesses of the segment need no check on the pin: the slots s1 + [40, 96), ps's fields and ts are
   frame slots the compiler proved addressable; ts's shadow (frame shadow byte 12, PSH_ts) is the premise of the ts
   write's window (kr_seat_now). The bcmp wrapper's own checks are inside ABCMP.

   Templates and reuse. PcapHarnessWalk.v's helpers are Required and reused (hw_entry_body, hw_mem_kept, hw_sh_nil,
   hw_md_fds, hw_body_mem, hw_pspad_mem, hw_plslots_mem, hw_pslot_mem, hw_pglob_mem, hw_preader_mem,
   hw_fields_of_shape, hw_eqon_of_kept, hw_rdword_on, hw_val_on, hw_mbyte_on, ms_of_body), never re-proved;
   PcapHarnessA.v gives h_sp, h_frame, h_base, h_blocks3, h_achain, h_meta_gx, h_arodata_S, h_nx_model, h_psn_lh_fit,
   h_ra_frame, h_rdword_keep, and kr_next follows h_C_next (PcapHarnessA.v:721) for the call of pcap_source_next.
   The skip loop's induction has the SHAPE of lib/B/Prog/PcapEntrySkip.v on a working branch cb8f7855e50
   (pe_from_skip_m, w3_skips_inv, w3_skip_step: the asan-ubsan image, other pcs and registers): no text is taken.
   kr_gx_entry is PaGxSites.v's aj_gx_entry_at (lib/A/Prog/PaGxSites.v:70-174) with one conjunct kept in its post
   (same_but_materialized; see there). NOT USED: pcap_L_x_a (ASegLx.v (sha256 e4355f5a77a3; internal record), a working branch), the
   slot-segment form the owner's brief forbids; no W6 / slot contract / _cf / AsanRT file is Required. The plain
   model lib/Prog/Slot/PWalk.v is Required, never Imported, as PcapHarnessWalk.v does (rule 24). *)
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From Stdlib Require Import FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00 YI0s YI16 YG0s.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YM05 PcapImgEnd YE00 YG0p YC5d YI13.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import PaTable PaSym PaShadow.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A.Prog Require Import PaStep.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import PaRun.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A.Prog Require Import PaJournal PcapSyms PcapList PcapAddr PcapPa PcapPaLib PcapBase YC4b YC81 YC1g YC1h YC85 PcapFrame PcapEntry PcapEntryA PcapEntryDefs PcapEntryPhases.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A.Stdio Require Import PSource PSourceMeta PFreadISpec.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A Require Import W_journal.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A.Prog Require Import PaJournalFs PaGxSites.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A.Prog Require Import PcapSourceClose PcapSourceNextDefs.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A.Prog Require Import PcapHarnessA PcapHarnessWalk.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Prog.Slot Require PWalk.
(* The zify flag leak (a Theorem Labs lane, 09:00Z): `Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::=` is
   global and set both ways by the files Required above (AE2e / YE2e and others to false, PcapHarnessA.v:631 to true),
   so its value here depends on their load order. This file fixes it, for its own proofs only (Local): its division
   goals use explicit div / mod lemmas, so the euclidean equations stay off, as PcapHarnessWalk.v's walk keeps them
   (its line 56); with them on, lia fails ("No applicable tactic") on linear goals beside a mod or div fact. *)
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

Module PW := OSSVerify.Proofs.libreac.fuzz_pcap.lib.Prog.Slot.PWalk.

(* ---- the bytes the harness assembles: four one-byte loads into one 32-bit field (incl 0x80b98..0x80c10,
   orig 0x80c98..0x80d10, the two time fields 0x80e3c..0x80f58), little-endian and byte-swapped ---- *)
Definition kb_lo3 (x0 x1 x2 : sv) : sv :=
  SAlu ALU_OR (SAlu ALU_OR (SAlu ALU_SLL x1 (SLit 8)) x0) (SAlu ALU_SLL x2 (SLit 16)).
Definition kb_le32w (x0 x1 x2 x3 : sv) : sv := SAlu ALU_OR (kb_lo3 x0 x1 x2) (SAluw ALU_SLL x3 (SLit 24)).
Definition kb_le32 (x0 x1 x2 x3 : sv) : sv := SAlu ALU_OR (kb_lo3 x0 x1 x2) (SAlu ALU_SLL x3 (SLit 24)).
Definition kb_be32w (x0 x1 x2 x3 : sv) : sv :=
  SAlu ALU_OR
    (SAlu ALU_OR (SAluw ALU_SLL (kb_lo3 x0 x1 x2) (SLit 24))
       (SAlu ALU_SLL (SAlu ALU_AND (kb_le32w x0 x1 x2 x3) (SLit 65280)) (SLit 8)))
    (SAlu ALU_OR (SAlu ALU_SLL (SAlu ALU_SRL (kb_lo3 x0 x1 x2) (SLit 16)) (SLit 8))
       (SAluw ALU_SRL (SAluw ALU_SLL x3 (SLit 24)) (SLit 24))).
Definition kb_be32 (x0 x1 x2 x3 : sv) : sv :=
  SAlu ALU_OR
    (SAlu ALU_OR (SAlu ALU_SLL (kb_lo3 x0 x1 x2) (SLit 24))
       (SAlu ALU_SLL (SAlu ALU_AND (kb_le32 x0 x1 x2 x3) (SLit 65280)) (SLit 8)))
    (SAlu ALU_OR (SAlu ALU_SLL (SAlu ALU_SRL (kb_lo3 x0 x1 x2) (SLit 16)) (SLit 8))
       (SAluw ALU_SRL (SAlu ALU_SLL x3 (SLit 24)) (SLit 24))).

(* A 32-bit value as the 64-bit register holds it after a sign-extending step. *)
Definition kb_sx32 (v : Z) : Z := if v <? 2 ^ 31 then v else v + (2 ^ 64 - 2 ^ 32).
Definition kb_w (d0 d1 d2 d3 : Z) : Z := d0 + 256 * d1 + 65536 * d2 + 16777216 * d3.

Lemma kb_land0 : forall a b k, 0 <= a -> 0 <= k -> 0 <= b < 2 ^ k -> Z.land (a * 2 ^ k) b = 0.
Proof.
  intros a b k Ha Hk Hb. apply Z.bits_inj'. intros i Hi.
  rewrite Z.land_spec, Z.bits_0.
  destruct (Z.lt_ge_cases i k) as [Hl|Hh].
  - rewrite Z.mul_pow2_bits_low by lia. reflexivity.
  - destruct (Z.eq_dec b 0) as [->|Hb0]; [rewrite Z.bits_0; apply andb_false_r|].
    assert (Hp : 2 ^ k <= 2 ^ i) by (apply Z.pow_le_mono_r; lia).
    rewrite (Z.bits_above_log2 b i); [apply andb_false_r | lia |].
    apply (proj1 (Z.log2_lt_pow2 b i ltac:(lia))). lia.
Qed.

Lemma kb_lor : forall a b k, 0 <= a -> 0 <= k -> 0 <= b < 2 ^ k -> Z.lor (a * 2 ^ k) b = a * 2 ^ k + b.
Proof.
  intros a b k Ha Hk Hb.
  rewrite <- Z.lxor_lor by (apply kb_land0; lia).
  symmetry. apply Z.add_nocarry_lxor. apply kb_land0; lia.
Qed.

Lemma kb_land0g : forall a b k j, 0 <= a -> 0 <= k -> 0 <= j -> 0 <= b < 2 ^ j ->
  Z.land (a * 2 ^ (j + k)) (b * 2 ^ k) = 0.
Proof.
  intros a b k j Ha Hk Hj Hb. apply Z.bits_inj'. intros i Hi.
  rewrite Z.land_spec, Z.bits_0.
  destruct (Z.lt_ge_cases i (j + k)) as [Hl|Hh].
  - rewrite Z.mul_pow2_bits_low by lia. reflexivity.
  - rewrite (Z.mul_pow2_bits b) by lia.
    destruct (Z.eq_dec b 0) as [->|Hb0]; [rewrite Z.bits_0; apply andb_false_r|].
    assert (Hp : 2 ^ j <= 2 ^ (i - k)) by (apply Z.pow_le_mono_r; lia).
    rewrite (Z.bits_above_log2 b (i - k)); [apply andb_false_r | lia |].
    apply (proj1 (Z.log2_lt_pow2 b (i - k) ltac:(lia))). lia.
Qed.

Lemma kb_lorg : forall a b k j, 0 <= a -> 0 <= k -> 0 <= j -> 0 <= b < 2 ^ j ->
  Z.lor (a * 2 ^ (j + k)) (b * 2 ^ k) = a * 2 ^ (j + k) + b * 2 ^ k.
Proof.
  intros a b k j Ha Hk Hj Hb.
  rewrite <- Z.lxor_lor by (apply kb_land0g; lia).
  symmetry. apply Z.add_nocarry_lxor. apply kb_land0g; lia.
Qed.

Lemma kb_bit_lit : forall L i, 0 <= L < 2 ^ 16 -> 16 <= i -> Z.testbit L i = false.
Proof.
  intros L i HL Hi. destruct (Z.eq_dec L 0) as [->|HL0]; [apply Z.bits_0|].
  apply Z.bits_above_log2; [lia|]. apply Z.lt_le_trans with 16; [|lia].
  apply (proj1 (Z.log2_lt_pow2 L 16 ltac:(lia))). lia.
Qed.

Lemma kb_land_ff00 : forall v, 0 <= v -> Z.land v 65280 = 256 * ((v / 256) mod 256).
Proof.
  intros v Hv. apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec.
  change 256 with (2 ^ 8). rewrite Z.mul_comm.
  destruct (Z.lt_ge_cases i 8) as [H8|H8].
  - rewrite Z.mul_pow2_bits_low by lia.
    assert (Hb : Z.testbit 65280 i = false)
      by (assert (i = 0 \/ i = 1 \/ i = 2 \/ i = 3 \/ i = 4 \/ i = 5 \/ i = 6 \/ i = 7) as Hc by lia;
          destruct Hc as [->|[->|[->|[->|[->|[->|[->| ->]]]]]]]; reflexivity).
    rewrite Hb. apply andb_false_r.
  - rewrite Z.mul_pow2_bits by lia.
    destruct (Z.lt_ge_cases i 16) as [H16|H16].
    + rewrite Z.mod_pow2_bits_low by lia. rewrite Z.div_pow2_bits by lia.
      replace (i - 8 + 8) with i by lia.
      assert (Hb : Z.testbit 65280 i = true)
        by (assert (i = 8 \/ i = 9 \/ i = 10 \/ i = 11 \/ i = 12 \/ i = 13 \/ i = 14 \/ i = 15) as Hc by lia;
            destruct Hc as [->|[->|[->|[->|[->|[->|[->| ->]]]]]]]; reflexivity).
      rewrite Hb. apply andb_true_r.
    + rewrite Z.mod_pow2_bits_high by lia. rewrite (kb_bit_lit 65280 i) by lia. apply andb_false_r.
Qed.

Lemma kb_swrap_sx : forall x, 0 <= x < 2 ^ 32 -> bv_wrap 64 (bv_swrap 32 x) = kb_sx32 x.
Proof.
  intros x Hx. unfold bv_swrap, bv_wrap, kb_sx32. change (bv_half_modulus 32) with (2 ^ 31).
  change (bv_modulus 32) with (2 ^ 32). change (bv_modulus 64) with (2 ^ 64).
  destruct (Z.ltb_spec x (2 ^ 31)) as [Hl|Hh].
  - rewrite (Z.mod_small (x + 2 ^ 31)) by lia. replace (x + 2 ^ 31 - 2 ^ 31) with x by lia.
    apply Z.mod_small. lia.
  - rewrite <- (Z.mod_add (x + 2 ^ 31) (-1) (2 ^ 32)) by lia.
    rewrite (Z.mod_small (x + 2 ^ 31 + -1 * 2 ^ 32)) by lia.
    rewrite <- (Z.mod_add (x + 2 ^ 31 + -1 * 2 ^ 32 - 2 ^ 31) 1 (2 ^ 64)) by lia.
    rewrite Z.mod_small by lia. lia.
Qed.

Lemma kb_swrap_mod : forall x, bv_swrap 32 x = bv_swrap 32 (x mod 2 ^ 32).
Proof.
  intros x. unfold bv_swrap, bv_wrap. change (bv_half_modulus 32) with (2 ^ 31).
  change (bv_modulus 32) with (2 ^ 32). f_equal. rewrite Zplus_mod_idemp_l. reflexivity.
Qed.

Lemma kb_U_aluw : forall E op a b,
  U E (SAluw op a b) = bv_wrap 64 (bv_swrap 32 (zalu_raw 31 32 op (U E a mod 2 ^ 32) (U E b mod 2 ^ 32))).
Proof. intros E op a b. rewrite U_of_S, S_SAluw. reflexivity. Qed.

(* sx32 of a value whose top byte is c: the same value, with c's sign copied into bits 32..63 *)
Lemma kb_sx32_top : forall c r, 0 <= c < 256 -> 0 <= r < 2 ^ 24 ->
  kb_sx32 (c * 2 ^ 24 + r) = (c + (if c <? 128 then 0 else 2 ^ 40 - 2 ^ 8)) * 2 ^ 24 + r.
Proof.
  intros c r Hc Hr. unfold kb_sx32.
  destruct (Z.ltb_spec c 128); destruct (Z.ltb_spec (c * 2 ^ 24 + r) (2 ^ 31)); lia.
Qed.

Section kbval.
Variable E : env.
Variables (x0 x1 x2 x3 : sv) (d0 d1 d2 d3 : Z).
Hypotheses (U0 : U E x0 = d0) (U1 : U E x1 = d1) (U2 : U E x2 = d2) (U3 : U E x3 = d3).
Hypotheses (R0 : 0 <= d0 < 256) (R1 : 0 <= d1 < 256) (R2 : 0 <= d2 < 256) (R3 : 0 <= d3 < 256).

Lemma kb_lo3_U : U E (kb_lo3 x0 x1 x2) = d0 + 256 * d1 + 65536 * d2.
Proof.
  unfold kb_lo3. rewrite !U_SAlu, U0, U1, U2, !U_SLit. cbn [zalu_raw].
  change (Z.land (zcanon 8) 63) with 8. change (Z.land (zcanon 16) 63) with 16.
  rewrite !Z.shiftl_mul_pow2 by lia.
  rewrite (zcanon_id (d1 * 2 ^ 8)) by (unfold M64; lia).
  rewrite (kb_lor d1 d0 8) by lia.
  rewrite (zcanon_id (d1 * 2 ^ 8 + d0)) by (unfold M64; lia).
  rewrite (zcanon_id (d2 * 2 ^ 16)) by (unfold M64; lia).
  rewrite Z.lor_comm, (kb_lor d2 (d1 * 2 ^ 8 + d0) 16) by lia.
  rewrite zcanon_id by (unfold M64; lia). lia.
Qed.

Lemma kb_x3w_U : U E (SAluw ALU_SLL x3 (SLit 24)) = kb_sx32 (d3 * 2 ^ 24).
Proof.
  rewrite kb_U_aluw, U3, U_SLit. cbn [zalu_raw].
  change (zcanon 24 mod 2 ^ 32) with 24. change (Z.land 24 31) with 24.
  rewrite (Z.mod_small d3) by lia. rewrite Z.shiftl_mul_pow2 by lia.
  apply kb_swrap_sx. lia.
Qed.

Lemma kb_le32w_U : U E (kb_le32w x0 x1 x2 x3) = kb_sx32 (kb_w d0 d1 d2 d3).
Proof.
  unfold kb_le32w. rewrite U_SAlu, kb_lo3_U, kb_x3w_U. cbn [zalu_raw].
  assert (T : kb_sx32 (d3 * 2 ^ 24) = (d3 + (if d3 <? 128 then 0 else 2 ^ 40 - 2 ^ 8)) * 2 ^ 24)
    by (rewrite <- (Z.add_0_r (d3 * 2 ^ 24)) at 1; rewrite kb_sx32_top by lia; lia).
  rewrite T.
  unfold kb_w. replace (d0 + 256 * d1 + 65536 * d2 + 16777216 * d3) with (d3 * 2 ^ 24 + (d0 + 256 * d1 + 65536 * d2)) by lia.
  rewrite (kb_sx32_top d3 (d0 + 256 * d1 + 65536 * d2)) by lia.
  rewrite Z.lor_comm, kb_lor by (destruct (Z.ltb_spec d3 128); lia).
  rewrite zcanon_id by (unfold M64; destruct (Z.ltb_spec d3 128); lia). reflexivity.
Qed.

Lemma kb_le32_U : U E (kb_le32 x0 x1 x2 x3) = kb_w d0 d1 d2 d3.
Proof.
  unfold kb_le32. rewrite !U_SAlu, kb_lo3_U, U3, U_SLit. cbn [zalu_raw].
  change (Z.land (zcanon 24) 63) with 24. rewrite Z.shiftl_mul_pow2 by lia.
  rewrite (zcanon_id (d3 * 2 ^ 24)) by (unfold M64; lia).
  rewrite Z.lor_comm, kb_lor by lia.
  unfold kb_w. rewrite zcanon_id by (unfold M64; lia). lia.
Qed.

Lemma kb_x3sll_U : U E (SAlu ALU_SLL x3 (SLit 24)) = d3 * 2 ^ 24.
Proof.
  rewrite U_SAlu, U3, U_SLit. cbn [zalu_raw]. change (Z.land (zcanon 24) 63) with 24.
  rewrite Z.shiftl_mul_pow2 by lia. apply zcanon_id. unfold M64. lia.
Qed.

Lemma kb_be32w_U : U E (kb_be32w x0 x1 x2 x3) = kb_sx32 (kb_w d3 d2 d1 d0).
Proof.
  set (X0 := if d0 <? 128 then 0 else 2 ^ 40 - 2 ^ 8).
  assert (HX0 : 0 <= X0 <= 2 ^ 40 - 2 ^ 8) by (unfold X0; destruct (Z.ltb_spec d0 128); lia).
  assert (HA : U E (SAluw ALU_SLL (kb_lo3 x0 x1 x2) (SLit 24)) = (d0 + X0) * 2 ^ 24).
  { rewrite kb_U_aluw, kb_lo3_U, U_SLit. cbn [zalu_raw].
    change (zcanon 24 mod 2 ^ 32) with 24. change (Z.land 24 31) with 24.
    rewrite (Z.mod_small (d0 + 256 * d1 + 65536 * d2)) by lia. rewrite Z.shiftl_mul_pow2 by lia.
    rewrite kb_swrap_mod.
    replace ((d0 + 256 * d1 + 65536 * d2) * 2 ^ 24) with (d0 * 2 ^ 24 + (d1 + 256 * d2) * 2 ^ 32) by lia.
    rewrite Z.mod_add by lia. rewrite (Z.mod_small (d0 * 2 ^ 24)) by lia.
    rewrite kb_swrap_sx by lia. rewrite <- (Z.add_0_r (d0 * 2 ^ 24)). rewrite kb_sx32_top by lia.
    unfold X0. lia. }
  set (X3 := if d3 <? 128 then 0 else 2 ^ 40 - 2 ^ 8).
  assert (HX3 : 0 <= X3 <= 2 ^ 40 - 2 ^ 8) by (unfold X3; destruct (Z.ltb_spec d3 128); lia).
  assert (HW : U E (kb_le32w x0 x1 x2 x3) = (d3 + X3) * 2 ^ 24 + (d0 + 256 * d1 + 65536 * d2)).
  { rewrite kb_le32w_U. unfold kb_w.
    replace (d0 + 256 * d1 + 65536 * d2 + 16777216 * d3) with (d3 * 2 ^ 24 + (d0 + 256 * d1 + 65536 * d2)) by lia.
    rewrite kb_sx32_top by lia. reflexivity. }
  assert (HB : U E (SAlu ALU_SLL (SAlu ALU_AND (kb_le32w x0 x1 x2 x3) (SLit 65280)) (SLit 8)) = d1 * 2 ^ 16).
  { rewrite !U_SAlu, HW, !U_SLit. cbn [zalu_raw]. change (zcanon 65280) with 65280.
    rewrite kb_land_ff00 by lia.
    replace ((d3 + X3) * 2 ^ 24 + (d0 + 256 * d1 + 65536 * d2)) with (d0 + (d1 + (d2 + (d3 + X3) * 256) * 256) * 256) by lia.
    rewrite Z.div_add by lia. rewrite (Z.div_small d0 256) by lia. rewrite Z.add_0_l.
    rewrite Z.mod_add by lia. rewrite (Z.mod_small d1) by lia.
    change (Z.land (zcanon 8) 63) with 8. rewrite (zcanon_id (256 * d1)) by (unfold M64; lia).
    rewrite Z.shiftl_mul_pow2 by lia. rewrite zcanon_id by (unfold M64; lia). lia. }
  assert (HC : U E (SAlu ALU_SLL (SAlu ALU_SRL (kb_lo3 x0 x1 x2) (SLit 16)) (SLit 8)) = d2 * 2 ^ 8).
  { rewrite !U_SAlu, kb_lo3_U, !U_SLit. cbn [zalu_raw].
    change (Z.land (zcanon 16) 63) with 16. change (Z.land (zcanon 8) 63) with 8.
    rewrite Z.shiftr_div_pow2 by lia.
    replace (d0 + 256 * d1 + 65536 * d2) with ((d0 + 256 * d1) + d2 * 2 ^ 16) by lia.
    rewrite Z.div_add by lia. rewrite (Z.div_small (d0 + 256 * d1)) by lia. rewrite Z.add_0_l.
    rewrite (zcanon_id d2) by (unfold M64; lia). rewrite Z.shiftl_mul_pow2 by lia. rewrite zcanon_id by (unfold M64; lia). lia. }
  assert (HD : U E (SAluw ALU_SRL (SAluw ALU_SLL x3 (SLit 24)) (SLit 24)) = d3).
  { rewrite kb_U_aluw, kb_x3w_U, U_SLit. cbn [zalu_raw].
    change (zcanon 24 mod 2 ^ 32) with 24. change (Z.land 24 31) with 24.
    rewrite <- (Z.add_0_r (d3 * 2 ^ 24)). rewrite kb_sx32_top by lia. rewrite Z.add_0_r.
    assert (M : ((d3 + (if d3 <? 128 then 0 else 2 ^ 40 - 2 ^ 8)) * 2 ^ 24) mod 2 ^ 32 = d3 * 2 ^ 24).
    { destruct (Z.ltb_spec d3 128); [rewrite Z.add_0_r; apply Z.mod_small; lia|].
      replace ((d3 + (2 ^ 40 - 2 ^ 8)) * 2 ^ 24) with (d3 * 2 ^ 24 + (2 ^ 32 - 1) * 2 ^ 32) by lia.
      rewrite Z.mod_add by lia. apply Z.mod_small. lia. }
    rewrite M.
    rewrite Z.shiftr_div_pow2 by lia. rewrite Z.div_mul by lia.
    rewrite kb_swrap_sx by lia. unfold kb_sx32. destruct (Z.ltb_spec d3 (2 ^ 31)); lia. }
  unfold kb_be32w. rewrite U_SAlu, (U_SAlu E ALU_OR), (U_SAlu E ALU_OR (SAlu ALU_SLL _ _)), HA, HB, HC, HD.
  cbn [zalu_raw].
  assert (AB : Z.lor ((d0 + X0) * 2 ^ 24) (d1 * 2 ^ 16) = (d0 + X0) * 2 ^ 24 + d1 * 2 ^ 16).
  { replace ((d0 + X0) * 2 ^ 24) with ((d0 + X0) * 2 ^ (8 + 16)) by (change (2 ^ (8 + 16)) with (2 ^ 24); lia).
    rewrite kb_lorg by lia. change (2 ^ (8 + 16)) with (2 ^ 24). lia. }
  assert (CD : Z.lor (d2 * 2 ^ 8) d3 = d2 * 2 ^ 8 + d3) by (apply kb_lor; lia).
  rewrite AB, CD.
  rewrite (zcanon_id ((d0 + X0) * 2 ^ 24 + d1 * 2 ^ 16)) by (unfold M64; lia).
  rewrite (zcanon_id (d2 * 2 ^ 8 + d3)) by (unfold M64; lia).
  assert (ABCD : Z.lor ((d0 + X0) * 2 ^ 24 + d1 * 2 ^ 16) (d2 * 2 ^ 8 + d3) =
                 (d0 + X0) * 2 ^ 24 + d1 * 2 ^ 16 + d2 * 2 ^ 8 + d3).
  { replace ((d0 + X0) * 2 ^ 24 + d1 * 2 ^ 16) with (((d0 + X0) * 2 ^ 8 + d1) * 2 ^ 16) by lia.
    rewrite kb_lor by lia. lia. }
  rewrite ABCD. rewrite zcanon_id by (unfold M64; lia).
  unfold kb_w. replace (d3 + 256 * d2 + 65536 * d1 + 16777216 * d0) with (d0 * 2 ^ 24 + (d3 + 256 * d2 + 65536 * d1)) by lia.
  rewrite kb_sx32_top by lia. unfold X0. lia.
Qed.

Lemma kb_le32sll_U : U E (SAlu ALU_SLL (kb_le32 x0 x1 x2 x3) (SLit 32)) = kb_w d0 d1 d2 d3 * 2 ^ 32.
Proof.
  rewrite U_SAlu, kb_le32_U, U_SLit. cbn [zalu_raw]. change (Z.land (zcanon 32) 63) with 32.
  rewrite Z.shiftl_mul_pow2 by lia. unfold kb_w. apply zcanon_id. unfold M64. lia.
Qed.

Lemma kb_be32sll_U : U E (SAlu ALU_SLL (kb_be32 x0 x1 x2 x3) (SLit 32)) = kb_w d3 d2 d1 d0 * 2 ^ 32.
Proof.
  assert (HA : U E (SAlu ALU_SLL (kb_lo3 x0 x1 x2) (SLit 24)) = (d0 + 256 * d1 + 65536 * d2) * 2 ^ 24).
  { rewrite U_SAlu, kb_lo3_U, U_SLit. cbn [zalu_raw]. change (Z.land (zcanon 24) 63) with 24.
    rewrite Z.shiftl_mul_pow2 by lia. apply zcanon_id. unfold M64. lia. }
  assert (HB : U E (SAlu ALU_SLL (SAlu ALU_AND (kb_le32 x0 x1 x2 x3) (SLit 65280)) (SLit 8)) = d1 * 2 ^ 16).
  { rewrite !U_SAlu, kb_le32_U, !U_SLit. cbn [zalu_raw]. change (zcanon 65280) with 65280.
    unfold kb_w. rewrite kb_land_ff00 by lia.
    replace (d0 + 256 * d1 + 65536 * d2 + 16777216 * d3) with (d0 + (d1 + (d2 + d3 * 256) * 256) * 256) by lia.
    rewrite Z.div_add by lia. rewrite (Z.div_small d0 256) by lia. rewrite Z.add_0_l.
    rewrite Z.mod_add by lia. rewrite (Z.mod_small d1) by lia.
    change (Z.land (zcanon 8) 63) with 8. rewrite (zcanon_id (256 * d1)) by (unfold M64; lia).
    rewrite Z.shiftl_mul_pow2 by lia. rewrite zcanon_id by (unfold M64; lia). lia. }
  assert (HC : U E (SAlu ALU_SLL (SAlu ALU_SRL (kb_lo3 x0 x1 x2) (SLit 16)) (SLit 8)) = d2 * 2 ^ 8).
  { rewrite !U_SAlu, kb_lo3_U, !U_SLit. cbn [zalu_raw].
    change (Z.land (zcanon 16) 63) with 16. change (Z.land (zcanon 8) 63) with 8.
    rewrite Z.shiftr_div_pow2 by lia.
    replace (d0 + 256 * d1 + 65536 * d2) with ((d0 + 256 * d1) + d2 * 2 ^ 16) by lia.
    rewrite Z.div_add by lia. rewrite (Z.div_small (d0 + 256 * d1)) by lia. rewrite Z.add_0_l.
    rewrite (zcanon_id d2) by (unfold M64; lia). rewrite Z.shiftl_mul_pow2 by lia. rewrite zcanon_id by (unfold M64; lia). lia. }
  assert (HD : U E (SAluw ALU_SRL (SAlu ALU_SLL x3 (SLit 24)) (SLit 24)) = d3).
  { rewrite kb_U_aluw, kb_x3sll_U, U_SLit. cbn [zalu_raw].
    change (zcanon 24 mod 2 ^ 32) with 24. change (Z.land 24 31) with 24.
    rewrite (Z.mod_small (d3 * 2 ^ 24)) by lia.
    rewrite Z.shiftr_div_pow2 by lia. rewrite Z.div_mul by lia.
    rewrite kb_swrap_sx by lia. unfold kb_sx32. destruct (Z.ltb_spec d3 (2 ^ 31)); lia. }
  unfold kb_be32. rewrite U_SAlu, U_SAlu, (U_SAlu E ALU_OR), (U_SAlu E ALU_OR (SAlu ALU_SLL _ _)), HA, HB, HC, HD.
  cbn [zalu_raw].
  assert (AB : Z.lor ((d0 + 256 * d1 + 65536 * d2) * 2 ^ 24) (d1 * 2 ^ 16) =
               (d0 + 256 * d1 + 65536 * d2) * 2 ^ 24 + d1 * 2 ^ 16).
  { replace ((d0 + 256 * d1 + 65536 * d2) * 2 ^ 24) with ((d0 + 256 * d1 + 65536 * d2) * 2 ^ (8 + 16))
      by (change (2 ^ (8 + 16)) with (2 ^ 24); lia).
    rewrite kb_lorg by lia. change (2 ^ (8 + 16)) with (2 ^ 24). lia. }
  assert (CD : Z.lor (d2 * 2 ^ 8) d3 = d2 * 2 ^ 8 + d3) by (apply kb_lor; lia).
  rewrite AB, CD.
  rewrite (zcanon_id ((d0 + 256 * d1 + 65536 * d2) * 2 ^ 24 + d1 * 2 ^ 16)) by (unfold M64; lia).
  rewrite (zcanon_id (d2 * 2 ^ 8 + d3)) by (unfold M64; lia).
  assert (ABCD : Z.lor ((d0 + 256 * d1 + 65536 * d2) * 2 ^ 24 + d1 * 2 ^ 16) (d2 * 2 ^ 8 + d3) =
                 (d0 + 256 * d1 + 65536 * d2) * 2 ^ 24 + d1 * 2 ^ 16 + d2 * 2 ^ 8 + d3).
  { replace ((d0 + 256 * d1 + 65536 * d2) * 2 ^ 24 + d1 * 2 ^ 16)
      with (((d0 + 256 * d1 + 65536 * d2) * 2 ^ 8 + d1) * 2 ^ 16) by lia.
    rewrite kb_lor by lia. lia. }
  rewrite ABCD. rewrite (zcanon_id (_ + _ + _ + d3)) by (unfold M64; lia).
  rewrite U_SLit. change (Z.land (zcanon 32) 63) with 32. rewrite Z.shiftl_mul_pow2 by lia.
  unfold zcanon, M64, kb_w.
  replace (((d0 + 256 * d1 + 65536 * d2) * 2 ^ 24 + d1 * 2 ^ 16 + d2 * 2 ^ 8 + d3) * 2 ^ 32)
    with ((d3 + 256 * d2 + 65536 * d1 + 16777216 * d0) * 2 ^ 32 + (d1 + 256 * d2) * 2 ^ 64) by lia.
  rewrite Z.mod_add by lia. apply Z.mod_small. lia.
Qed.

End kbval.

Lemma kb_zext32_U : forall E t, U E (SAlu ALU_SRL (SAlu ALU_SLL t (SLit 32)) (SLit 32)) = U E t mod 2 ^ 32.
Proof.
  intros E t. pose proof (U_range E t) as Ht. unfold M64 in Ht.
  rewrite !U_SAlu, !U_SLit. cbn [zalu_raw]. change (Z.land (zcanon 32) 63) with 32.
  rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia.
  unfold zcanon, M64.
  replace ((U E t * 2 ^ 32) mod 2 ^ 64) with ((U E t mod 2 ^ 32) * 2 ^ 32)
    by (change (2 ^ 64) with (2 ^ 32 * 2 ^ 32); rewrite Z.mul_mod_distr_r by lia; reflexivity).
  rewrite Z.div_mul by lia. apply Z.mod_small. pose proof (Z.mod_pos_bound (U E t) (2 ^ 32)). lia.
Qed.

Lemma kb_sx32_mod : forall v, 0 <= v < 2 ^ 32 -> kb_sx32 v mod 2 ^ 32 = v.
Proof.
  intros v Hv. unfold kb_sx32. destruct (Z.ltb_spec v (2 ^ 31)); [apply Z.mod_small; lia|].
  replace (v + (2 ^ 64 - 2 ^ 32)) with (v + (2 ^ 32 - 1) * 2 ^ 32) by lia. rewrite Z.mod_add by lia.
  apply Z.mod_small. lia.
Qed.

Lemma kb_sx32_zero : forall v, 0 <= v < 2 ^ 32 -> (kb_sx32 v = 0 <-> v = 0).
Proof. intros v Hv. unfold kb_sx32. destruct (Z.ltb_spec v (2 ^ 31)); lia. Qed.

Lemma kb_mulhu_U : forall E a w, U E a = w * 2 ^ 32 -> 0 <= w < 2 ^ 32 ->
  U E (SMd M_MULHU a (SLit 4294967296000000)) = w * 1000000.
Proof.
  intros E a w Ha Hw. rewrite U_SMd, Ha, U_SLit. cbn [zmd_raw].
  rewrite (zcanon_id 4294967296000000) by (unfold M64; lia).
  rewrite Z.shiftr_div_pow2 by lia.
  replace (w * 2 ^ 32 * 4294967296000000) with ((w * 1000000) * 2 ^ 64) by lia.
  rewrite Z.div_mul by lia. apply zcanon_id. unfold M64. lia.
Qed.

Lemma kb_add_U : forall E a b, U E (SAlu ALU_ADD a b) = zcanon (U E a + U E b).
Proof. intros E a b. rewrite U_SAlu. reflexivity. Qed.

Lemma kb_subz_U : forall E s v k, U E s = v -> 0 < k <= v -> v < 2 ^ 31 ->
  U E (SAlu ALU_SRL (SAlu ALU_ADD (SAlu ALU_SLL s (SLit 32)) (SLit (- (k * 2 ^ 32)))) (SLit 32)) = v - k.
Proof.
  intros E s v k Hs Hk Hv. rewrite !U_SAlu, Hs, !U_SLit. cbn [zalu_raw].
  change (Z.land (zcanon 32) 63) with 32. rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia.
  rewrite (zcanon_id (v * 2 ^ 32)) by (unfold M64; lia).
  unfold zcanon, M64.
  replace (v * 2 ^ 32 + (- (k * 2 ^ 32)) mod 2 ^ 64) with ((v - k) * 2 ^ 32 + 2 ^ 64)
    by (replace (- (k * 2 ^ 32)) with (2 ^ 64 - k * 2 ^ 32 + (-1) * 2 ^ 64) by lia; rewrite Z.mod_add by lia;
        rewrite Z.mod_small by lia; lia).
  replace ((v - k) * 2 ^ 32 + 2 ^ 64) with ((v - k) * 2 ^ 32 + 1 * 2 ^ 64) by lia.
  rewrite Z.mod_add by lia. rewrite (Z.mod_small ((v - k) * 2 ^ 32)) by lia.
  rewrite Z.div_mul by lia. apply Z.mod_small. lia.
Qed.

(* ---- the reader's model at the harness's position (lib/Prog/pcap_source_struct_next.v, lib/Prog/Slot/PWalkDef.v):
   the three ways the skip loop (0x80b70..0x80c30) can leave a record ---- *)
Section model.
Variables (sw : bool) (F : list byte) (cap : Z).

Lemma kr_kind_mid : forall e, e + 16 <= PSN.flen F ->
  PSN.kind sw F cap e =
  if PSN.incl sw F e =? 0 then PSN.KEmpty
  else if PSN.incl sw F e <=? cap then (if e + 16 + PSN.incl sw F e <=? PSN.flen F then PSN.KFit else PSN.KCutFit)
  else if cap =? 0 then PSN.KBig0
  else if e + 16 + PSN.incl sw F e <=? PSN.flen F then PSN.KBig else PSN.KCutBig.
Proof.
  intros e He. unfold PSN.kind.
  destruct (Z.eqb_spec (PSN.flen F - e) 0); [lia|]. destruct (Z.ltb_spec (PSN.flen F - e) 16); [lia|]. reflexivity.
Qed.

Lemma kr_m_bound : forall e Q, PWD.skips sw F cap e Q -> PSN.kind sw F cap Q = PSN.KFit ->
  e + 16 + PSN.incl sw F Q <= PSN.flen F /\ e <= Q.
Proof.
  intros e Q HS HK. pose proof (PW.skips_le sw F cap e Q HS) as Hle.
  destruct (PW.kind_fit sw F cap Q HK) as (_ & _ & _ & HQ & _). lia.
Qed.

Lemma kr_m_empty : forall e Q, PWD.skips sw F cap e Q -> PSN.kind sw F cap Q = PSN.KFit ->
  e + 16 <= PSN.flen F -> PSN.incl sw F e = 0 ->
  PWD.skips sw F cap (e + 16) Q /\ e + 16 + 16 <= PSN.flen F.
Proof.
  intros e Q HS HK He Hi.
  assert (Ke : PSN.kind sw F cap e = PSN.KEmpty) by (rewrite kr_kind_mid by exact He; rewrite Hi; reflexivity).
  pose proof (PW.skips_empty_inv sw F cap e Q HS Ke) as HS'. split; [exact HS'|].
  destruct (kr_m_bound (e + 16) Q HS' HK) as [Hb _]. pose proof (PW.incl_nonneg sw F Q). lia.
Qed.

Lemma kr_m_big : forall e Q, PWD.skips sw F cap e Q -> PSN.kind sw F cap Q = PSN.KFit ->
  e + 16 <= PSN.flen F -> PSN.incl sw F e <> 0 -> cap < PSN.incl sw F e ->
  PWD.skips sw F cap (e + 16 + PSN.incl sw F e) Q /\ e + 16 + PSN.incl sw F e + 16 <= PSN.flen F.
Proof.
  intros e Q HS HK He Hi Hc.
  assert (Kn : PSN.kind sw F cap e <> PSN.KEmpty /\ PSN.kind sw F cap e <> PSN.KFit).
  { rewrite kr_kind_mid by exact He. rewrite (proj2 (Z.eqb_neq _ _) Hi), (proj2 (Z.leb_gt _ _) Hc).
    destruct (cap =? 0); [split; discriminate|]. destruct (_ <=? _); split; discriminate. }
  inversion HS as [q Hk1 Hk2 Eq | q Q' Hk HS' Eq1 Eq2 | q Q' Hk HS' Eq1 Eq2]; subst.
  - destruct Kn as [_ Kn]. exfalso. exact (Kn HK).
  - destruct Kn as [Kn _]. exfalso. exact (Kn Hk).
  - split; [exact HS'|]. destruct (kr_m_bound _ Q HS' HK) as [Hb _]. pose proof (PW.incl_nonneg sw F Q). lia.
Qed.

Lemma kr_m_fit : forall e Q, PWD.skips sw F cap e Q -> PSN.kind sw F cap Q = PSN.KFit ->
  e + 16 <= PSN.flen F -> PSN.incl sw F e <> 0 -> PSN.incl sw F e <= cap -> e = Q.
Proof.
  intros e Q HS HK He Hi Hc.
  assert (Kn : PSN.kind sw F cap e <> PSN.KEmpty /\ PSN.kind sw F cap e <> PSN.KBig).
  { rewrite kr_kind_mid by exact He. rewrite (proj2 (Z.eqb_neq _ _) Hi), (proj2 (Z.leb_le _ _) Hc).
    destruct (_ <=? _); split; discriminate. }
  destruct Kn as [K1 K2]. symmetry. exact (PW.skips_exit sw F cap e Q HS K1 K2).
Qed.
End model.

(* ---- the symbolic states of the walk ---- *)
(* The shadow base: s11 (register 27) holds SHADOW_OFF in the whole body (pe_body's pregs). *)
Definition KR_SB : Z := 0x7fff8000.
Definition krBx : sv := SOff 27 0.
Definition krSpan : Z * Z := (KR_SB, KR_SB + 2 ^ 44 - 1).
Lemma KR_SB_eq : KR_SB = SHADOW_OFF.
Proof. reflexivity. Qed.

(* Registers: each its own atom, s7 = 0xff00 and s8 = swapped as literals (0x80bec, 0x80bf8 decide on them), and t1
   (register 6, the struct's address) as atom 32 where the struct region is based (pin6). *)
Definition krR (sw : Z) : list sv := sr_set (sr_set sr_atoms 23%bv (SLit 0xff00)) 24%bv (SLit sw).
(* The copy of the file from b + e (s10, register 26): bytes [lo, hi) as the data list 0 of the environment, which
   holds the copy from position e on. *)
Definition kr_copy (lo hi : Z) : YP09.region :=
  YP09.mkRegion (Some 26%nat) lo hi lo lo [YP09.mkChunk lo (CData 0 lo (hi - lo))].
Definition kr_SH (lo hi : Z) : list shent := [mkSHE 26 lo hi].
(* The spill slots the record checks read (0x80dec, 0x80da4, 0x80f64, 0x80f30, 0x80e1c / 0x80f7c, 0x80dc0 /
   0x80e24): VMASK, BUF12, USEC, FIRST, TSP, PSP. Atom 32 = &ps, 33 = first. *)
Definition kr_slots : YP09.region := YP09.mkRegion (Some 9%nat) 40 96 40 40
  [YP09.mkChunk 40 (CVal 8 (SLit 0xf00)); YP09.mkChunk 48 (CVal 8 (SOff 22 12));
   YP09.mkChunk 56 (CVal 8 (SLit (1000000 * 2 ^ 32))); YP09.mkChunk 72 (CVal 8 (SOff 33 0));
   YP09.mkChunk 80 (CVal 8 (SOff 32 64)); YP09.mkChunk 88 (CVal 8 (SOff 32 0))].
(* ps's three checked fields and ts (= &ps + 64): atoms 34 orig, 35 vlan_tagged, 36 vlan_id, 37 ts. *)
Definition kr_ps_w (wts : bool) : YP09.region :=
  YP09.mkRegion (Some 32%nat) 12 72 (if wts then 64 else 12) (if wts then 72 else 12)
  [YP09.mkChunk 12 (CVal 4 (SOff 34 0)); YP09.mkChunk 16 (CVal 4 (SOff 35 0));
   YP09.mkChunk 20 (CVal 2 (SOff 36 0)); YP09.mkChunk 64 (CVal 8 (SOff 37 0))].
Definition kr_facts : facts := mkFacts [(26%nat, mkAF 4096 (2 ^ 47 - 64) 0); (27%nat, mkAF KR_SB KR_SB 0)] [] [].
(* The record seats also bound &ps (atom 32), so that ts (= &ps + 64, written at 0x80f80) can be a write window that
   a shadow entry covers. *)
Definition kr_facts_r : facts :=
  mkFacts [(26%nat, mkAF 4096 (2 ^ 47 - 64) 0); (27%nat, mkAF KR_SB KR_SB 0); (32%nat, mkAF 4096 (2 ^ 47 - 128) 0)] [] [].
Definition kr_SHr (L : Z) (wts : bool) : list shent := mkSHE 26 0 L :: (if wts then [mkSHE 32 64 72] else []).

(* PP_KR + 4 = 0x80b74 (after s10 := s3 + s2): the skip check reads bytes 8..11 of the record at e. *)
Definition PP_KRS : Z := 0x43c.
Definition kr_ss_skip (sw : Z) : sstate := mkSS PP_KRS (krR sw) [kr_copy 8 12] None kr_facts.
(* The record checks, from a seat at pc with the copy's bytes [0, L): t1 pinned to &ps (pin6, the first seat),
   a0 pinned to 0 (pin10, the seats right after a bcmp call that answered "equal"), ts writable (wts, the last). *)
Definition krRg (sw : Z) (pin6 pin10 : bool) : list sv :=
  let r := krR sw in
  let r := if pin6 then sr_set r 6%bv (SOff 32 0) else r in
  if pin10 then sr_set r 10%bv (SLit 0) else r.
Definition kr_ss_rec (pc sw L : Z) (pin6 pin10 wts : bool) : sstate :=
  mkSS pc (krRg sw pin6 pin10) [kr_copy 0 L; kr_slots; kr_ps_w wts] None kr_facts_r.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
(* The sink head is explicit, as in PcapHarnessWalk.v and PcapEntryDefs.v: it must never be inferred. *)
Context (SK : OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable.YI16.sink_head).
Section b.
Context {PI : PAImg pcap_listing}.
#[local] Notation SEGS := (@pa_segs _ pcap_listing PI).
#[local] Notation VAL := (@pa_val _ pcap_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ pcap_listing PI).
#[local] Notation BASE := (@pa_val _ pcap_listing PI A_TEXT).
#[local] Notation rdW W mem := (mrestrict (w_H W) mem).

Definition kr_env (regs : bvmap 5 word) (X : list word) (D : list byte) : env := Eimg (edset (Ereg regs X) 0 D).

Lemma kr_env_img : forall regs X D, img_env VAL A_LIM (kr_env regs X D).
Proof. intros regs X D. apply Eimg_env. Qed.

Lemma kr_env_reg : forall regs X D n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew (kr_env regs X D) n = getr regs r.
Proof.
  intros regs X D n r Hn. pose proof (bv_unsigned_in_range 5 r) as Hr. change (bv_modulus 5) with 32 in Hr.
  unfold kr_env. rewrite Eimg_low by (unfold A_TEXT; lia). cbn [edset ew]. apply ew_Ereg_nat. exact Hn.
Qed.

Lemma kr_env_x : forall regs X D j, (j < 200)%nat -> ew (kr_env regs X D) (32 + j) = nth j X (Z_to_bv 64 0).
Proof.
  intros regs X D j Hj. unfold kr_env. rewrite Eimg_low by (unfold A_TEXT; lia). cbn [edset ew].
  apply ew_Ereg_extra.
Qed.

Lemma kr_env_d : forall regs X D, ed (kr_env regs X D) 0 = D.
Proof. reflexivity. Qed.

(* The register list of a seat, against the machine's registers. *)
Lemma kr_regs_ok : forall regs X D sw (pin6 pin10 : bool),
  getr regs 23 = w64 0xff00 -> getr regs 24 = w64 sw ->
  (pin6 = true -> getr regs 6 = nth 0 X (Z_to_bv 64 0)) ->
  (pin10 = true -> getr regs 10 = w64 0) ->
  regs_ok (kr_env regs X D) (krRg sw pin6 pin10) regs.
Proof.
  intros regs X D sw pin6 pin10 H23 H24 H6 H10. apply regs_ok_by_cases. intros r Hr.
  cbv [all_regs In] in Hr.
  repeat (destruct Hr as [<-|Hr]); [..|destruct Hr].
  all: destruct pin6, pin10.
  all: match goal with |- _ = sv_denot ?E (sr_get ?sr ?r) =>
         let v := eval vm_compute in (sr_get sr r) in change (sr_get sr r) with v end.
  all: cbn [sv_denot].
  all: try (rewrite getr_zero; reflexivity).
  all: try (rewrite H23; reflexivity).
  all: try (rewrite H24; reflexivity).
  all: try (rewrite (H10 eq_refl); reflexivity).
  all: try (rewrite (H6 eq_refl), Z.add_0_r;
    rewrite (kr_env_x regs X D 0 ltac:(lia) : ew (kr_env regs X D) 32 = nth 0 X (Z_to_bv 64 0));
    rewrite Z_to_bv_bv_unsigned; reflexivity).
  all: rewrite Z.add_0_r;
         match goal with |- context [ew (kr_env ?a ?b ?c) ?n] =>
           rewrite (kr_env_reg a b c n (Z_to_bv 5 (Z.of_nat n)) ltac:(vm_compute; reflexivity)) end;
         match goal with |- _ = Z_to_bv 64 (bv_unsigned (getr ?rg ?x)) =>
           let y := eval vm_compute in x in change x with y end;
         rewrite Z_to_bv_bv_unsigned; reflexivity.
Qed.


(* ---- seating a symbolic state on the machine state of a phase ---- *)
Lemma kr_ew_reg : forall regs X D n (r : bv 5) v, Z.of_nat n = bv_unsigned r -> getr regs r = w64 v -> 0 <= v < 2 ^ 64 ->
  bv_unsigned (ew (kr_env regs X D) n) = v.
Proof. intros regs X D n r v Hn Hr Hv. rewrite (kr_env_reg regs X D n r Hn), Hr. unfold w64. apply unsigned_lit_small. lia. Qed.

Lemma kr_copy_ok : forall regs X D (m : word -> option byte) be lo hi,
  getr regs 26 = w64 be -> 0 <= be -> 0 <= lo < hi -> be + hi <= 2 ^ 64 ->
  (forall i, lo <= i < hi -> exists x, nth_error D (Z.to_nat i) = Some x /\ mbyte SEGS m (be + i) = Some x) ->
  YP09.region_ok SEGS (kr_env regs X D) m (kr_copy lo hi).
Proof.
  intros regs X D m be lo hi R26 Hbe Hlh Hhi HD. unfold YP09.region_ok, kr_copy.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
  rewrite (kr_ew_reg regs X D 26 26%bv be eq_refl R26) by lia.
  split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
  apply Forall_cons; [|apply Forall_nil].
  intros i Hi. cbn [YP09.c_len YP09.cv_len YP09.c_val YP09.c_off] in Hi |- *. cbn [YP09.cbyte].
  destruct (HD (lo + i) ltac:(lia)) as (x & Hx & Hm). exists x. split.
  - rewrite kr_env_d. exact Hx.
  - replace (be + lo + i) with (be + (lo + i)) by lia. exact Hm.
Qed.

Lemma kr_facts_ok : forall regs X D be, getr regs 26 = w64 be -> 4096 <= be <= 2 ^ 47 - 64 ->
  getr regs 27 = w64 KR_SB -> facts_ok (kr_env regs X D) kr_facts.
Proof.
  intros regs X D be R26 Hbe R27. split; [|split; exact I]. cbn [kr_facts f_atoms atoms_ok]. unfold afact_ok.
  cbn [af_lo af_hi af_al2].
  rewrite (kr_ew_reg regs X D 26 26%bv be eq_refl R26) by lia.
  rewrite (kr_ew_reg regs X D 27 27%bv KR_SB eq_refl R27) by (unfold KR_SB; lia).
  change (2 ^ 0) with 1. rewrite !Z.mod_1_r. unfold KR_SB. repeat split; lia.
Qed.

Lemma kr_seat_skip : forall (W : world SEGS) (regs : bvmap 5 word) (mem : word -> option byte) sw D be,
  getr regs 23 = w64 0xff00 -> getr regs 24 = w64 sw -> getr regs 26 = w64 be -> getr regs 27 = w64 KR_SB ->
  4096 <= be <= 2 ^ 47 - 64 ->
  (forall i, 8 <= i < 12 -> exists x, nth_error D (Z.to_nat i) = Some x /\
     mbyte SEGS (mrestrict (w_H W) mem) (be + i) = Some x) ->
  st_ok_pi SEGS VAL (kr_env regs [] D) (kr_ss_skip sw)
    (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + PP_KRS)) mem (seg_rom SEGS))).
Proof.
  intros W regs mem sw D be R23 R24 R26 R27 Hbe HD. rewrite restrict_mkst_fx. unfold kr_ss_skip.
  apply pa_entry_st_ok_full.
  - exact (kr_regs_ok regs [] D sw false false R23 R24 (fun H => ltac:(discriminate H)) (fun H => ltac:(discriminate H))).
  - vm_compute. reflexivity.
  - apply Forall_cons; [|apply Forall_nil]. apply (kr_copy_ok regs [] D _ be 8 12 R26); [lia | lia | lia | exact HD].
  - split; exact I.
  - exact (kr_facts_ok regs [] D be R26 Hbe R27).
Qed.

(* ---- the copy's bytes, in memory and in the environment's data list 0 ---- *)
(* The data list of a seat: the copy from position e on. *)
Lemma kr_D_nth : forall (F : list byte) e k, 0 <= e -> 0 <= k -> e + k < Z.of_nat (length F) ->
  nth_error (skipn (Z.to_nat e) F) (Z.to_nat k) = Some (nth (Z.to_nat (e + k)) F (Z_to_bv 8 0)).
Proof.
  intros F e k He Hk Hl. rewrite nth_error_skipn. replace (Z.to_nat e + Z.to_nat k)%nat with (Z.to_nat (e + k)) by lia.
  apply nth_error_nth'. lia.
Qed.

Lemma kr_fb_range : forall F i, 0 <= PSN.fb F i < 256.
Proof. intros F i. exact (PW.pw_fb_range F i). Qed.

(* The copy's bytes in memory, from the stream's content (asource_at's garr8 at b). *)
Lemma kr_copy_mbyte : forall (m : word -> option byte) b (F : list byte) j,
  garr8 SEGS m b (map (fun x : byte => bv_unsigned x) F) -> 0 <= j < Z.of_nat (length F) ->
  mbyte SEGS m (b + j) = Some (nth (Z.to_nat j) F (Z_to_bv 8 0)).
Proof.
  intros m b F j HG Hj. destruct (HG (Z.to_nat j) ltac:(rewrite length_map; lia)) as (Hv & _).
  specialize (Hv 0%nat ltac:(lia)). cbn [Z.of_nat] in Hv. rewrite Z.add_0_r in Hv.
  rewrite Z2Nat.id in Hv by lia. rewrite Hv. f_equal.
  rewrite (map_nth (fun x : byte => bv_unsigned x) F (Z_to_bv 8 0)).
  pose proof (bv_unsigned_in_range 8 (nth (Z.to_nat j) F (Z_to_bv 8 0))) as Hr. change (bv_modulus 8) with 256 in Hr.
  unfold YO0f.le_byte.
  change (8 * Z.of_nat 0) with 0. rewrite Z.shiftr_0_r. change (2 ^ (8 * Z.of_nat 1)) with 256.
  rewrite Z.mod_mod by lia. rewrite Z.mod_small by lia. apply Z_to_bv_bv_unsigned.
Qed.

Lemma kr_ew_U : forall regs X D n (r : bv 5) v, Z.of_nat n = bv_unsigned r -> getr regs r = w64 v -> 0 <= v < 2 ^ 64 ->
  U (kr_env regs X D) (SOff n 0) = v.
Proof.
  intros regs X D n r v Hn Hr Hv. apply U_atom; [|exact Hv]. rewrite (kr_env_reg regs X D n r Hn), Hr. reflexivity.
Qed.

(* The shadow entry of the copy's bytes [lo, hi) from b + e. *)
Lemma kr_shok : forall regs X D (m : word -> option byte) be lo hi,
  getr regs 26 = w64 be -> getr regs 27 = w64 KR_SB -> 0 <= be -> be + hi < 2 ^ 64 -> 0 <= lo < hi ->
  range_addressable (rd_of SEGS m) KR_SB (be + lo) (hi - lo) ->
  (forall a, be + lo <= a < be + hi -> ~ (KR_SB <= a < KR_SB + 17592186044416)) ->
  sh_ok SEGS krBx (kr_SH lo hi) (kr_env regs X D) m.
Proof.
  intros regs X D m be lo hi R26 R27 Hbe Hhi Hlh HR Happ. unfold sh_ok, kr_SH.
  apply Forall_cons; [|apply Forall_nil]. unfold shent_ok, app_apart. cbn [she_m she_lo she_hi].
  unfold krBx. rewrite (kr_ew_U regs X D 27 27%bv KR_SB eq_refl R27) by (unfold KR_SB; lia).
  rewrite (kr_ew_U regs X D 26 26%bv be eq_refl R26) by lia.
  split; [exact HR|]. intros a Ha. apply Happ. lia.
Qed.

Lemma kr_awr_nowin : forall E rs G XO OUT STK sp0 FP bl0 blc ly own,
  Forall (fun r => YP09.r_whi r <= YP09.r_wlo r) rs -> awr_ok_x E rs G XO OUT STK sp0 FP bl0 blc ly own.
Proof.
  intros E rs G XO OUT STK sp0 FP bl0 blc ly own Hw a (r & Hin & Hr).
  pose proof (proj1 (Forall_forall _ _) Hw r Hin) as Hb. cbv beta in Hb. lia.
Qed.

(* ---- reading the environment of a run's end state ---- *)
Lemma kr_U_dataE : forall E D k x, ed E 0 = D -> 0 <= k -> nth_error D (Z.to_nat k) = Some x ->
  U E (SData 0 k 1) = bv_unsigned x.
Proof.
  intros E D k x HD Hk Hx. unfold U. cbn [sv_denot]. unfold data_word. rewrite HD.
  apply nth_error_split in Hx as (l1 & l2 & -> & Hl1).
  rewrite skipn_app. replace (Z.to_nat k - length l1)%nat with 0%nat by lia.
  rewrite (skipn_all2 l1) by lia. cbn [app skipn].
  change (firstn (N.to_nat 1) (x :: l2)) with [x].
  pose proof (bv_unsigned_in_range 8 x) as Hr. change (bv_modulus 8) with 256 in Hr.
  assert (Hb : bytes_le_to_Z [x] = bv_unsigned x)
    by (cbn [bytes_le_to_Z]; rewrite ?Z.shiftl_0_l, ?Z.lor_0_r, ?Z.mul_0_r, ?Z.add_0_r; reflexivity).
  rewrite Hb. apply unsigned_lit_small. lia.
Qed.

Lemma kr_U_fbE : forall E (F : list byte) e k, ed E 0 = skipn (Z.to_nat e) F ->
  0 <= e -> 0 <= k -> e + k < Z.of_nat (length F) -> U E (SData 0 k 1) = PSN.fb F (e + k).
Proof.
  intros E F e k HD He Hk Hl. rewrite (kr_U_dataE E _ k _ HD Hk (kr_D_nth F e k He Hk Hl)). reflexivity.
Qed.

Lemma kr_swz : forall cx, p_swz cx = 0 \/ p_swz cx = 1.
Proof. intros cx. unfold p_swz, PST.pcap_sw. destruct (_ =? _); [right | left]; reflexivity. Qed.

(* The record's fields as the harness assembles them (PSN.hw), for each byte order. *)
Lemma kr_hw_le : forall F q j, PSN.hw false F q j =
  kb_w (PSN.fb F (q + j)) (PSN.fb F (q + j + 1)) (PSN.fb F (q + j + 2)) (PSN.fb F (q + j + 3)).
Proof. intros F q j. reflexivity. Qed.
Lemma kr_hw_be : forall F q j, PSN.hw true F q j =
  kb_w (PSN.fb F (q + j + 3)) (PSN.fb F (q + j + 2)) (PSN.fb F (q + j + 1)) (PSN.fb F (q + j)).
Proof. intros F q j. reflexivity. Qed.

(* Registers a run kept: those the end state still names by their own atom, read in the seat's environment. *)
Lemma kr_kept_env : forall regs X D (E' : env) ss (ms : machine_state) H (l : list (bv 5)),
  st_ok_pi SEGS VAL E' ss (restrict H ms) ->
  (forall n, (n < 32)%nat -> ew E' n = ew (kr_env regs X D) n) ->
  forallb (fun r : bv 5 => sv_eqb (sr_get (ss_regs ss) r) (SOff (Z.to_nat (bv_unsigned r)) 0)) l = true ->
  forall r, In r l -> getr (ms_regs ms) r = getr regs r.
Proof.
  intros regs X D E' ss ms H l HS Hag Hl r Hr.
  rewrite (st_ok_pi_restrict_reg H E' ss ms r HS).
  pose proof (proj1 (forallb_forall _ l) Hl r Hr) as Hb. apply sv_eqb_eq in Hb. rewrite Hb.
  cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned.
  pose proof (bv_unsigned_in_range 5 r) as Hr5. change (bv_modulus 5) with 32 in Hr5.
  rewrite Hag by lia. apply kr_env_reg. lia.
Qed.

Ltac kr_agree := let n := fresh "n" in let Hn := fresh "Hn" in
  intros n Hn; cbn [ewset ew];
  repeat match goal with |- context [Nat.eqb n ?m] => rewrite (proj2 (Nat.eqb_neq n m)) by lia end;
  reflexivity.

(* ---- the seat of the record checks: the copy's bytes [0, L), the six slots, ps's checked fields and ts ---- *)
Lemma kr_chunk8 : forall E H (m : word -> option byte) base off e v,
  rdword (aview SEGS H m) (base + off) = Some v -> sv_denot E e = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 ->
  YP09.chunk_ok SEGS E (mrestrict H m) base (YP09.mkChunk off (CVal 8 e)).
Proof.
  intros E H m base off e v Hr He Hv.
  apply (chunk_ok_val SEGS E (mrestrict H m) base off 8%N e v); [exact He | cbn; lia | cbn; lia|].
  apply (val_mem_of_rdword SEGS H m). exact Hr.
Qed.

Lemma kr_denot_x : forall regs X D j v, (j < 200)%nat -> nth j X (Z_to_bv 64 0) = w64 v -> 0 <= v < 2 ^ 64 ->
  forall c, sv_denot (kr_env regs X D) (SOff (32 + j) c) = Z_to_bv 64 (v + c).
Proof.
  intros regs X D j v Hj Hx Hv c. cbn [sv_denot]. rewrite (kr_env_x regs X D j Hj), Hx. unfold w64.
  rewrite unsigned_lit_small by lia. reflexivity.
Qed.

Definition kr_X (pps first orig vt vid tsv : Z) : list word :=
  [w64 pps; w64 first; w64 orig; w64 vt; w64 vid; w64 tsv].
Definition kr_L (L32 : bool) : Z := if L32 then 32 else 16.

Lemma kr_seat_rec : forall (W : world SEGS) (regs : bvmap 5 word) (mem : word -> option byte) pc sw (L32 pin6 pin10 wts : bool)
  D be sp1 buf pps first orig vt vid tsv,
  getr regs 23 = w64 0xff00 -> getr regs 24 = w64 sw -> getr regs 26 = w64 be -> getr regs 27 = w64 KR_SB ->
  getr regs 9 = w64 sp1 -> getr regs 22 = w64 buf ->
  (pin6 = true -> getr regs 6 = w64 pps) -> (pin10 = true -> getr regs 10 = w64 0) ->
  4096 <= be <= 2 ^ 47 - 64 -> 0 <= sp1 <= 2 ^ 47 -> 0 <= buf <= 2 ^ 47 -> 4096 <= pps <= 2 ^ 47 - 128 ->
  0 <= orig < 2 ^ 32 -> 0 <= vt < 2 ^ 32 -> 0 <= vid < 2 ^ 16 -> 0 <= tsv < 2 ^ 64 ->
  (be + kr_L L32 <= sp1 + 40 \/ sp1 + 96 <= be) -> (be + kr_L L32 <= pps + 12 \/ pps + 72 <= be) ->
  (sp1 + 96 <= pps + 12 \/ pps + 72 <= sp1 + 40) ->
  (forall i, 0 <= i < kr_L L32 -> exists x, nth_error D (Z.to_nat i) = Some x /\
     mbyte SEGS (mrestrict (w_H W) mem) (be + i) = Some x) ->
  rdword (aview SEGS (w_H W) mem) (sp1 + 40) = Some 0xf00 ->
  rdword (aview SEGS (w_H W) mem) (sp1 + 48) = Some (buf + 12) ->
  rdword (aview SEGS (w_H W) mem) (sp1 + 56) = Some (1000000 * 2 ^ 32) ->
  rdword (aview SEGS (w_H W) mem) (sp1 + 72) = Some (first mod 2 ^ 64) ->
  rdword (aview SEGS (w_H W) mem) (sp1 + 80) = Some (pps + 64) ->
  rdword (aview SEGS (w_H W) mem) (sp1 + 88) = Some pps ->
  val_mem SEGS (mrestrict (w_H W) mem) (pps + 12) 4 orig -> val_mem SEGS (mrestrict (w_H W) mem) (pps + 16) 4 vt ->
  val_mem SEGS (mrestrict (w_H W) mem) (pps + 20) 2 vid -> val_mem SEGS (mrestrict (w_H W) mem) (pps + 64) 8 tsv ->
  (wts = true -> forall o, 64 <= o < 72 -> writable_at SEGS (mrestrict (w_H W) mem) (pps + o)) ->
  st_ok_pi SEGS VAL (kr_env regs (kr_X pps first orig vt vid tsv) D) (kr_ss_rec pc sw (kr_L L32) pin6 pin10 wts)
    (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + pc)) mem (seg_rom SEGS))).
Proof.
  intros W regs mem pc sw L32 pin6 pin10 wts D be sp1 buf pps first orig vt vid tsv R23 R24 R26 R27 R9 R22 R6 R10
    Hbe Hsp1 Hbuf Hpps Horig Hvt Hvid Htsv D1 D2 D3 HD S40 S48 S56 S72 S80 S88 V12 V16 V20 V64 Hwr.
  set (X := kr_X pps first orig vt vid tsv).
  assert (Lr : 16 <= kr_L L32 <= 32) by (unfold kr_L; destruct L32; lia).
  rewrite restrict_mkst_fx. unfold kr_ss_rec.
  apply pa_entry_st_ok_full.
  - apply (kr_regs_ok regs X D sw pin6 pin10 R23 R24); [|exact R10].
    intros H. rewrite (R6 H). reflexivity.
  - unfold kr_L; destruct L32, wts; vm_compute; reflexivity.
  - apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]].
    + apply (kr_copy_ok regs X D _ be 0 (kr_L L32) R26); [lia | lia | lia |]. intros i Hi. apply HD. lia.
    + unfold YP09.region_ok, kr_slots.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      rewrite (kr_ew_reg regs X D 9 9%bv sp1 eq_refl R9) by lia.
      split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      repeat apply Forall_cons; try apply Forall_nil.
      * apply (kr_chunk8 _ _ _ sp1 40 _ 0xf00 S40); [reflexivity | lia].
      * apply (kr_chunk8 _ _ _ sp1 48 _ (buf + 12) S48); [|lia].
        cbn [sv_denot]. rewrite (kr_env_reg regs X D 22 22%bv eq_refl), R22. unfold w64.
        rewrite unsigned_lit_small by lia. reflexivity.
      * apply (kr_chunk8 _ _ _ sp1 56 _ (1000000 * 2 ^ 32) S56); [reflexivity | lia].
      * apply (kr_chunk8 _ _ _ sp1 72 _ (first mod 2 ^ 64) S72);
          [| pose proof (Z.mod_pos_bound first (2 ^ 64)); lia].
        cbn [sv_denot]. rewrite (kr_env_x regs X D 1 ltac:(lia) : ew (kr_env regs X D) 33 = _). cbn [nth X kr_X].
        unfold w64. rewrite Z_to_bv_unsigned, Z.add_0_r. reflexivity.
      * apply (kr_chunk8 _ _ _ sp1 80 _ (pps + 64) S80); [|lia].
        exact (kr_denot_x regs X D 0 pps ltac:(lia) eq_refl ltac:(lia) 64).
      * apply (kr_chunk8 _ _ _ sp1 88 _ pps S88); [|lia].
        etransitivity; [exact (kr_denot_x regs X D 0 pps ltac:(lia) eq_refl ltac:(lia) 0) | rewrite Z.add_0_r; reflexivity].
    + unfold YP09.region_ok, kr_ps_w.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      assert (U32 : bv_unsigned (ew (kr_env regs X D) 32) = pps).
      { rewrite (kr_env_x regs X D 0 ltac:(lia) : ew (kr_env regs X D) 32 = _). cbn [nth X kr_X].
        unfold w64. apply unsigned_lit_small. lia. }
      rewrite U32. split; [lia|]. split; [lia|]. split.
      { intros o Ho. destruct wts; [apply (Hwr eq_refl); lia | lia]. }
      repeat apply Forall_cons; try apply Forall_nil.
      * apply (chunk_ok_val SEGS _ _ pps 12 4%N _ orig); [| cbn; lia | cbn; lia | exact V12].
        etransitivity; [exact (kr_denot_x regs X D 2 orig ltac:(lia) eq_refl ltac:(lia) 0) | rewrite Z.add_0_r; reflexivity].
      * apply (chunk_ok_val SEGS _ _ pps 16 4%N _ vt); [| cbn; lia | cbn; lia | exact V16].
        etransitivity; [exact (kr_denot_x regs X D 3 vt ltac:(lia) eq_refl ltac:(lia) 0) | rewrite Z.add_0_r; reflexivity].
      * apply (chunk_ok_val SEGS _ _ pps 20 2%N _ vid); [| cbn; lia | cbn; lia | exact V20].
        etransitivity; [exact (kr_denot_x regs X D 4 vid ltac:(lia) eq_refl ltac:(lia) 0) | rewrite Z.add_0_r; reflexivity].
      * apply (chunk_ok_val SEGS _ _ pps 64 8%N _ tsv); [| cbn; lia | cbn; lia | exact V64].
        etransitivity; [exact (kr_denot_x regs X D 5 tsv ltac:(lia) eq_refl ltac:(lia) 0) | rewrite Z.add_0_r; reflexivity].
  - apply pairwise_disjoint_of_extents.
    unfold kr_copy, kr_slots, kr_ps_w, extent_of_region. cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val].
    rewrite (kr_ew_reg regs X D 26 26%bv be eq_refl R26) by lia.
    rewrite (kr_ew_reg regs X D 9 9%bv sp1 eq_refl R9) by lia.
    rewrite (kr_env_x regs X D 0 ltac:(lia) : ew (kr_env regs X D) 32 = _). cbn [nth X kr_X]. unfold w64.
    rewrite unsigned_lit_small by lia.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. lia.
  - split; [|split; exact I]. cbn [kr_facts_r f_atoms atoms_ok]. unfold afact_ok.
    cbn [af_lo af_hi af_al2].
    rewrite (kr_ew_reg regs X D 26 26%bv be eq_refl R26) by lia.
    rewrite (kr_ew_reg regs X D 27 27%bv KR_SB eq_refl R27) by (unfold KR_SB; lia).
    rewrite (kr_env_x regs X D 0 ltac:(lia) : ew (kr_env regs X D) 32 = _). cbn [nth X kr_X]. unfold w64.
    rewrite unsigned_lit_small by lia.
    change (2 ^ 0) with 1. rewrite !Z.mod_1_r. unfold KR_SB. repeat split; lia.
Qed.

(* ---- the record's timestamp as the harness computes it (0x80e10 .. 0x80f70): sec * 10^6 + usec, each field
   assembled from four copy bytes in the file's byte order (be: the swapped order) ---- *)
Definition kr_f32 (be : bool) (x0 x1 x2 x3 : sv) : sv := if be then kb_be32 x0 x1 x2 x3 else kb_le32 x0 x1 x2 x3.
Definition kr_tsT (be : bool) : sv :=
  SAlu ALU_ADD
    (SMd M_MULHU (SAlu ALU_SLL (kr_f32 be (SData 0 0 1) (SData 0 1 1) (SData 0 2 1) (SData 0 3 1)) (SLit 32))
       (SLit 4294967296000000))
    (SAlu ALU_SRL (SAlu ALU_SLL (kr_f32 be (SData 0 4 1) (SData 0 5 1) (SData 0 6 1) (SData 0 7 1)) (SLit 32))
       (SLit 32)).

Lemma kr_w_range : forall d0 d1 d2 d3, 0 <= d0 < 256 -> 0 <= d1 < 256 -> 0 <= d2 < 256 -> 0 <= d3 < 256 ->
  0 <= kb_w d0 d1 d2 d3 < 2 ^ 32.
Proof. intros. unfold kb_w. lia. Qed.

Lemma kr_srl32_U : forall E a w, U E a = w * 2 ^ 32 -> 0 <= w < 2 ^ 32 -> U E (SAlu ALU_SRL a (SLit 32)) = w.
Proof.
  intros E a w Ha Hw. rewrite U_SAlu, Ha, U_SLit. cbn [zalu_raw]. change (Z.land (zcanon 32) 63) with 32.
  rewrite Z.shiftr_div_pow2 by lia. rewrite Z.div_mul by lia. apply zcanon_id. unfold M64. lia.
Qed.

Lemma kr_tsT_U : forall E (F : list byte) Q (sw : bool), ed E 0 = skipn (Z.to_nat Q) F -> 0 <= Q ->
  Q + 8 <= Z.of_nat (length F) -> U E (kr_tsT sw) = PSN.rec_ts sw F Q.
Proof.
  intros E F Q sw HD HQ HL.
  assert (UD : forall j, 0 <= j < 8 -> U E (SData 0 j 1) = PSN.fb F (Q + j))
    by (intros j Hj; apply (kr_U_fbE E F Q j HD); lia).
  pose proof (kr_fb_range F) as FR.
  unfold kr_tsT, kr_f32, PSN.rec_ts. rewrite kb_add_U.
  destruct sw.
  - rewrite (kb_mulhu_U E _ (kb_w (PSN.fb F (Q + 3)) (PSN.fb F (Q + 2)) (PSN.fb F (Q + 1)) (PSN.fb F (Q + 0))))
      by (first [ apply (kb_be32sll_U E _ _ _ _ _ _ _ _ (UD 0 ltac:(lia)) (UD 1 ltac:(lia)) (UD 2 ltac:(lia)) (UD 3 ltac:(lia)))
                | apply kr_w_range ]; apply FR).
    rewrite (kr_srl32_U E _ (kb_w (PSN.fb F (Q + 7)) (PSN.fb F (Q + 6)) (PSN.fb F (Q + 5)) (PSN.fb F (Q + 4))))
      by (first [ apply (kb_be32sll_U E _ _ _ _ _ _ _ _ (UD 4 ltac:(lia)) (UD 5 ltac:(lia)) (UD 6 ltac:(lia)) (UD 7 ltac:(lia)))
                | apply kr_w_range ]; apply FR).
    rewrite !kr_hw_be.
    replace (Q + 0 + 3) with (Q + 3) by lia. replace (Q + 0 + 2) with (Q + 2) by lia.
    replace (Q + 0 + 1) with (Q + 1) by lia. replace (Q + 4 + 3) with (Q + 7) by lia.
    replace (Q + 4 + 2) with (Q + 6) by lia. replace (Q + 4 + 1) with (Q + 5) by lia.
    apply zcanon_id. unfold M64.
    pose proof (kr_w_range _ _ _ _ (FR (Q + 3)) (FR (Q + 2)) (FR (Q + 1)) (FR (Q + 0))).
    pose proof (kr_w_range _ _ _ _ (FR (Q + 7)) (FR (Q + 6)) (FR (Q + 5)) (FR (Q + 4))). lia.
  - rewrite (kb_mulhu_U E _ (kb_w (PSN.fb F (Q + 0)) (PSN.fb F (Q + 1)) (PSN.fb F (Q + 2)) (PSN.fb F (Q + 3))))
      by (first [ apply (kb_le32sll_U E _ _ _ _ _ _ _ _ (UD 0 ltac:(lia)) (UD 1 ltac:(lia)) (UD 2 ltac:(lia)) (UD 3 ltac:(lia)))
                | apply kr_w_range ]; apply FR).
    rewrite (kr_srl32_U E _ (kb_w (PSN.fb F (Q + 4)) (PSN.fb F (Q + 5)) (PSN.fb F (Q + 6)) (PSN.fb F (Q + 7))))
      by (first [ apply (kb_le32sll_U E _ _ _ _ _ _ _ _ (UD 4 ltac:(lia)) (UD 5 ltac:(lia)) (UD 6 ltac:(lia)) (UD 7 ltac:(lia)))
                | apply kr_w_range ]; apply FR).
    rewrite !kr_hw_le.
    replace (Q + 0 + 3) with (Q + 3) by lia. replace (Q + 0 + 2) with (Q + 2) by lia.
    replace (Q + 0 + 1) with (Q + 1) by lia. replace (Q + 4 + 3) with (Q + 7) by lia.
    replace (Q + 4 + 2) with (Q + 6) by lia. replace (Q + 4 + 1) with (Q + 5) by lia.
    apply zcanon_id. unfold M64.
    pose proof (kr_w_range _ _ _ _ (FR (Q + 0)) (FR (Q + 1)) (FR (Q + 2)) (FR (Q + 3))).
    pose proof (kr_w_range _ _ _ _ (FR (Q + 4)) (FR (Q + 5)) (FR (Q + 6)) (FR (Q + 7))). lia.
Qed.

Section c.
Variable B : asyms.
Variable MT : ameter_ops.
Variable KS : asource_syms.
#[local] Notation at_cut := (@PcapHarnessWalk.at_cut _ SK PI B MT KS).

Hypothesis LAWS : AR_laws SEGS B.
Hypothesis TL : PALib B.
Hypothesis MTL : ameter_laws MT.
Hypothesis RO : ro_below_ofl SEGS pa_relro_lo pa_relro_hi.
Hypothesis HGX : gx_ok SEGS B pe_G.
Hypothesis NEXT : tpcap_source_next_specX SK SEGS pa_relro_lo pa_relro_hi NX_STK B MT KS (BASE + AF_pcap_source_next).
Hypothesis ABCMP : abcmp_realizes SEGS B (SIGMA PS___interceptor_trampoline_bcmp).
Hypothesis ASIL : asource_img_laws SK SEGS B KS.
Let BR := paj_branch (PI := PI).
Let RUN := paj_run_x B LAWS pe_G HGX 0 [].
Let RUNTO := paj_run_to_x B LAWS pe_G HGX 0 [].

Lemma kr_mem_kept : forall E (rs : smem) (m m' : word -> option byte),
  Forall (fun r => YP09.r_whi r <= YP09.r_wlo r) rs -> frame_of E rs m m' -> m' = m.
Proof.
  intros E rs m m' Hw HF. apply functional_extensionality. intros x. apply HF.
  intros (r & Hin & Hr). pose proof (proj1 (Forall_forall _ _) Hw r Hin) as Hb. cbv beta in Hb. lia.
Qed.

(* ---- the cut GI_KR with its witnesses (PcapEntryPhases.v:336-349, verbatim) ---- *)
Definition kr_body (cx : ecx) (fp k acc : Z) (ly3 : alayout) (S3 : astate) (W3 : world SEGS)
  (ms3 : machine_state) (md3 : Model) (b h buf i p e : Z) : Prop :=
  p_cut B cx fp PP_KR PSH_ts k 3 acc (PA_K3 MT cx) [(b, p_nF cx); (h, SRC_FILE_BLOCK); (buf, p_bn cx)] ly3 S3 W3 ms3 md3 /\
  p_pspad cx fp W3 ms3 /\
  c_n cx < 2 ^ 26 /\ p_good cx = true /\
  0 <= i /\ 24 + 17 * i <= p /\ p_kind cx (p_q cx p) = PSN.KFit /\
  p <= e /\ p_skips cx e (p_q cx p) /\ e + 16 <= p_nF cx /\
  getr (ms_regs ms3) 6 = w64 (pPS cx fp) /\ getr (ms_regs ms3) 11 = w64 (p_nF cx) /\
  getr (ms_regs ms3) 12 = w64 (p_res cx (p_q cx p)) /\ getr (ms_regs ms3) 14 = w64 (e + 16) /\
  getr (ms_regs ms3) 18 = w64 e /\ getr (ms_regs ms3) 19 = w64 b /\
  getr (ms_regs ms3) 21 = w64 (p_cap cx) /\ getr (ms_regs ms3) 22 = w64 buf /\
  getr (ms_regs ms3) 23 = w64 0xff00 /\ getr (ms_regs ms3) 24 = w64 (p_swz cx) /\
  getr (ms_regs ms3) 25 = w64 (i + 1) /\
  p_lslots cx fp W3 ms3 buf /\ pslot cx W3 ms3 PS_FIRST (p_first cx mod 2 ^ 64) /\
  p_glob cx W3 ms3 b /\ p_reader KS cx fp W3 ms3 b h buf p.

Lemma kr_body_GI : forall cx fp k acc ly3 S3 W3 ms3 md3,
  GI_KR B MT KS cx fp k acc ly3 S3 W3 ms3 md3 <->
  exists b h buf i p e, kr_body cx fp k acc ly3 S3 W3 ms3 md3 b h buf i p e.
Proof. intros. unfold GI_KR, kr_body. reflexivity. Qed.

(* ---- the record found: the state at 0x80c68 (listing offset 0x530), after the skip loop's last test
   `bgeu s5,a3` (0x80c20) found 0 < incl <= cap at e, so that e is the record the reader answered for ---- *)
Definition PP_REC : Z := 0x530.
Definition kr_incl (cx : ecx) (q : Z) : Z := PSN.incl (p_sw cx) (p_F cx) q.

Definition kr_rbody (cx : ecx) (fp k acc : Z) (ly3 : alayout) (S3 : astate) (W3 : world SEGS)
  (ms3 : machine_state) (md3 : Model) (b h buf i p : Z) : Prop :=
  p_cut B cx fp PP_REC PSH_ts k 3 acc (PA_K3 MT cx) [(b, p_nF cx); (h, SRC_FILE_BLOCK); (buf, p_bn cx)] ly3 S3 W3 ms3 md3 /\
  p_pspad cx fp W3 ms3 /\
  c_n cx < 2 ^ 26 /\ p_good cx = true /\
  0 <= i /\ 24 + 17 * i <= p /\ p_kind cx (p_q cx p) = PSN.KFit /\ p <= p_q cx p /\
  getr (ms_regs ms3) 6 = w64 (pPS cx fp) /\ getr (ms_regs ms3) 11 = w64 (p_nF cx) /\
  getr (ms_regs ms3) 12 = w64 (p_res cx (p_q cx p)) /\ getr (ms_regs ms3) 13 = w64 (kr_incl cx (p_q cx p)) /\
  getr (ms_regs ms3) 14 = w64 (p_q cx p + 16) /\
  getr (ms_regs ms3) 18 = w64 (p_q cx p) /\ getr (ms_regs ms3) 19 = w64 b /\
  getr (ms_regs ms3) 20 = w64 (kr_incl cx (p_q cx p)) /\
  getr (ms_regs ms3) 21 = w64 (p_cap cx) /\ getr (ms_regs ms3) 22 = w64 buf /\
  getr (ms_regs ms3) 23 = w64 0xff00 /\ getr (ms_regs ms3) 24 = w64 (p_swz cx) /\
  getr (ms_regs ms3) 25 = w64 (i + 1) /\ getr (ms_regs ms3) 26 = w64 (b + p_q cx p) /\
  p_lslots cx fp W3 ms3 buf /\ pslot cx W3 ms3 PS_FIRST (p_first cx mod 2 ^ 64) /\
  p_glob cx W3 ms3 b /\ p_reader KS cx fp W3 ms3 b h buf p.

Definition GI_KREC (cx : ecx) (fp k acc : Z) (ly3 : alayout) (S3 : astate) (W3 : world SEGS)
  (ms3 : machine_state) (md3 : Model) : Prop :=
  exists b h buf i p, kr_rbody cx fp k acc ly3 S3 W3 ms3 md3 b h buf i p.

(* ---- a state of the skip loop, carried to another pc and other registers with the memory kept ---- *)
Definition kr_kept (rs : list (bv 5)) (ms ms3 : machine_state) : Prop :=
  forall r, In r rs -> getr (ms_regs ms) r = getr (ms_regs ms3) r.
(* The registers the skip check keeps (it writes a0, a3..a7, t0, s2, s4, s10), and those the body keeps. *)
Definition kr_keep1 : list (bv 5) :=
  [2%bv; 8%bv; 9%bv; 27%bv; 3%bv; 4%bv; 6%bv; 11%bv; 12%bv; 14%bv; 18%bv; 19%bv; 21%bv; 22%bv; 23%bv; 24%bv; 25%bv].
Definition kr_keepC : list (bv 5) :=
  [2%bv; 8%bv; 9%bv; 27%bv; 3%bv; 4%bv; 6%bv; 11%bv; 12%bv; 19%bv; 21%bv; 22%bv; 25%bv].
Lemma kr_keepC_1 : forall r, In r kr_keepC -> In r kr_keep1.
Proof. intros r Hr. cbn [kr_keepC kr_keep1 In] in *. tauto. Qed.

Ltac kr_in := cbn [In]; repeat (first [left; reflexivity | right]).

Lemma kr_back : forall cx fp k acc ly3 S3 W3 ms3 md3 (ms : machine_state) md b h buf i p e e',
  kr_body cx fp k acc ly3 S3 W3 ms3 md3 b h buf i p e ->
  ms_mem ms = ms_mem ms3 -> ms = mkst (ms_regs ms) (Z_to_bv 64 (BASE + PP_KR)) (ms_mem ms) (seg_rom SEGS) ->
  kr_kept kr_keepC ms ms3 ->
  getr (ms_regs ms) 23 = w64 0xff00 -> getr (ms_regs ms) 24 = w64 (p_swz cx) ->
  getr (ms_regs ms) 18 = w64 e' -> getr (ms_regs ms) 14 = w64 (e' + 16) ->
  p <= e' -> p_skips cx e' (p_q cx p) -> e' + 16 <= p_nF cx ->
  m_fds md = m_fds md3 -> m_fs md = m_fs md3 ->
  kr_body cx fp k acc ly3 S3 W3 ms md b h buf i p e'.
Proof.
  intros cx fp k acc ly3 S3 W3 ms3 md3 ms md b h buf i p e e' HKB Hm Hsh KP R23' R24' R18 R14 Hpe Hsk He16 Hfds' Hfs'.
  destruct HKB as (HCUT & Hpad & H26 & Hgood & Hi0 & Hip & HK & _ & _ & _ & R6 & R11 & R12 & _ & _ & R19 & R21 & R22
    & R23 & R24 & R25 & Hls & Hfirst & Hglob & Hrd).
  destruct HCUT as (HBODY & Hk3 & Hacc & HPerm & Hfds & Hfs).
  destruct (hw_fields_of_shape _ _ _ _ Hsh) as (Hpc & Hrv & Hsv & Hrom & Hfr & Hcs).
  pose proof HBODY as (_ & _ & _ & _ & _ & _ & (G2 & G8 & G9 & G27 & G3 & G4) & _).
  split.
  { split; [|split; [exact Hk3|]; split; [exact Hacc|]; split; [exact HPerm|];
       split; [rewrite Hfds'; exact Hfds | rewrite Hfs'; exact Hfs]].
    apply (hw_body_mem cx fp PP_KR PP_KR W3 ms3 ms PSH_ts Hm Hpc Hrv Hsv Hrom Hfr Hcs); [|exact HBODY].
    unfold pregs. unfold kr_kept, kr_keepC in KP. rewrite !KP by kr_in. repeat split; assumption. }
  split; [exact (hw_pspad_mem cx fp W3 ms3 ms Hm Hpad)|].
  unfold kr_kept, kr_keepC in KP.
  rewrite (KP 6%bv ltac:(kr_in)), (KP 11%bv ltac:(kr_in)), (KP 12%bv ltac:(kr_in)), (KP 19%bv ltac:(kr_in)),
    (KP 21%bv ltac:(kr_in)), (KP 22%bv ltac:(kr_in)), (KP 25%bv ltac:(kr_in)).
  do 19 (split; [assumption|]).
  split; [exact (hw_plslots_mem cx fp W3 ms3 ms buf Hm Hls)|].
  split; [exact (hw_pslot_mem cx W3 ms3 ms PS_FIRST _ Hm Hfirst)|].
  split; [exact (hw_pglob_mem cx W3 ms3 ms b Hm Hglob)|].
  exact (hw_preader_mem KS cx fp W3 ms3 ms b h buf p Hm Hrd).
Qed.

Lemma kr_to_rec : forall cx fp k acc ly3 S3 W3 ms3 md3 (ms : machine_state) md b h buf i p e,
  kr_body cx fp k acc ly3 S3 W3 ms3 md3 b h buf i p e ->
  ms_mem ms = ms_mem ms3 -> ms = mkst (ms_regs ms) (Z_to_bv 64 (BASE + PP_REC)) (ms_mem ms) (seg_rom SEGS) ->
  kr_kept kr_keepC ms ms3 -> getr (ms_regs ms) 14 = getr (ms_regs ms3) 14 ->
  getr (ms_regs ms) 18 = getr (ms_regs ms3) 18 ->
  getr (ms_regs ms) 23 = w64 0xff00 -> getr (ms_regs ms) 24 = w64 (p_swz cx) ->
  getr (ms_regs ms) 13 = w64 (kr_incl cx e) -> getr (ms_regs ms) 20 = w64 (kr_incl cx e) ->
  getr (ms_regs ms) 26 = w64 (b + e) -> e = p_q cx p ->
  m_fds md = m_fds md3 -> m_fs md = m_fs md3 ->
  kr_rbody cx fp k acc ly3 S3 W3 ms md b h buf i p.
Proof.
  intros cx fp k acc ly3 S3 W3 ms3 md3 ms md b h buf i p e HKB Hm Hsh KP R14' R18' R23' R24' R13 R20 R26 HeQ Hfds' Hfs'.
  destruct HKB as (HCUT & Hpad & H26 & Hgood & Hi0 & Hip & HK & Hpe & _ & _ & R6 & R11 & R12 & R14 & R18 & R19 & R21
    & R22 & R23 & R24 & R25 & Hls & Hfirst & Hglob & Hrd).
  destruct HCUT as (HBODY & Hk3 & Hacc & HPerm & Hfds & Hfs).
  destruct (hw_fields_of_shape _ _ _ _ Hsh) as (Hpc & Hrv & Hsv & Hrom & Hfr & Hcs).
  pose proof HBODY as (_ & _ & _ & _ & _ & _ & (G2 & G8 & G9 & G27 & G3 & G4) & _).
  subst e.
  split.
  { split; [|split; [exact Hk3|]; split; [exact Hacc|]; split; [exact HPerm|];
       split; [rewrite Hfds'; exact Hfds | rewrite Hfs'; exact Hfs]].
    apply (hw_body_mem cx fp PP_KR PP_REC W3 ms3 ms PSH_ts Hm Hpc Hrv Hsv Hrom Hfr Hcs); [|exact HBODY].
    unfold pregs. unfold kr_kept, kr_keepC in KP. rewrite !KP by kr_in. repeat split; assumption. }
  split; [exact (hw_pspad_mem cx fp W3 ms3 ms Hm Hpad)|].
  unfold kr_kept, kr_keepC in KP.
  rewrite (KP 6%bv ltac:(kr_in)), (KP 11%bv ltac:(kr_in)), (KP 12%bv ltac:(kr_in)), (KP 19%bv ltac:(kr_in)),
    (KP 21%bv ltac:(kr_in)), (KP 22%bv ltac:(kr_in)), (KP 25%bv ltac:(kr_in)), R14', R18'.
  do 20 (split; [assumption|]).
  split; [exact (hw_plslots_mem cx fp W3 ms3 ms buf Hm Hls)|].
  split; [exact (hw_pslot_mem cx W3 ms3 ms PS_FIRST _ Hm Hfirst)|].
  split; [exact (hw_pglob_mem cx W3 ms3 ms b Hm Hglob)|].
  exact (hw_preader_mem KS cx fp W3 ms3 ms b h buf p Hm Hrd).
Qed.

(* ---- the skip loop, 0x80b70 .. 0x80c30 ---- *)
Ltac kr_nowin := apply kr_awr_nowin; apply Forall_forall; let rr := fresh "rr" in let Hrr := fresh "Hrr" in
  intros rr Hrr; vm_compute in Hrr; repeat (destruct Hrr as [<- | Hrr]; [cbn; lia |]); destruct Hrr.
Ltac kr_zc H := repeat match type of H with context [zcanon ?z] =>
  lazymatch z with context [zcanon _] => fail | _ => rewrite (zcanon_id z) in H by (unfold M64; lia) end end.
(* A register of a run's end state as U of its symbolic value. *)
Ltac kregU HS r Q :=
  lazymatch type of HS with st_ok_pi _ _ ?E ?ss (restrict ?H ?ms) =>
    pose proof (st_ok_pi_restrict_reg H E ss ms r HS) as Q;
    let e := eval vm_compute in (sr_get (ss_regs ss) r) in change (sr_get (ss_regs ss) r) with e in Q;
    rewrite (denot_lit_U E e) in Q end.
(* A run whose regions have no write window keeps the memory function. *)
Ltac kr_kept_run HF Hm :=
  lazymatch type of HF with frame_of _ ?rs _ _ =>
    pose proof (kr_mem_kept _ rs _ _ ltac:(cbn; repeat constructor; cbn; lia) HF) as Hm end;
  clear HF; try match goal with H : frame_of _ _ _ _ |- _ => clear H end;
  try match goal with H : mem_grows _ _ |- _ => clear H end.

(* The back edge 0x80c30 -> 0x80b70: the end state of the skip check is a KR state at e' (kr_back). *)
Ltac kr_backleaf HS1 HKB HJ IH KP1 AG2 UI U18 HIr Hmem Hsw Hskp He16' :=
  lazymatch goal with |- SRr _ _ (mkCfg ?msx _) _ =>
    let Hshx := fresh "Hshx" in let Q18 := fresh "Q18" in let Q14 := fresh "Q14" in
    let Q23x := fresh "Q23x" in let Q24x := fresh "Q24x" in let KPC := fresh "KPC" in
    pose proof (st_ok_pi_restrict_mkst (w_H _) _ _ msx HS1 eq_refl) as Hshx; cbn [ss_pc] in Hshx;
    change 1080 with PP_KR in Hshx;
    kregU HS1 (18%bv : bv 5) Q18; kregU HS1 (14%bv : bv 5) Q14;
    kregU HS1 (23%bv : bv 5) Q23x; kregU HS1 (24%bv : bv 5) Q24x;
    rewrite !kb_add_U, kb_zext32_U, UI, U18, kb_sx32_mod, U_SLit in Q18 by exact HIr;
    rewrite !kb_add_U, kb_zext32_U, UI, U18, kb_sx32_mod, U_SLit in Q14 by exact HIr;
    kr_zc Q18; kr_zc Q14; rewrite U_SLit in Q23x, Q24x; kr_zc Q23x; kr_zc Q24x;
    lazymatch type of KP1 with kr_kept _ _ ?m3 => assert (KPC : kr_kept kr_keepC msx m3) end;
    [ let r := fresh "r" in let Hr := fresh "Hr" in intros r Hr;
      rewrite (kr_kept_env _ _ _ _ _ msx (w_H _) kr_keepC HS1 AG2 ltac:(vm_compute; reflexivity) r Hr);
      exact (KP1 r (kr_keepC_1 r Hr))
    | eapply (IH msx _ _ HJ);
      [ eapply (kr_back _ _ _ _ _ _ _ _ _ msx _ _ _ _ _ _ _ _ HKB);
        [ exact Hmem | exact Hshx | exact KPC | exact Q23x | rewrite Q24x, Hsw; reflexivity | exact Q18
        | rewrite Q14; f_equal; lia | lia | exact Hskp | exact He16'
        | exact (proj1 (hw_md_fds _ _)) | exact (proj2 (hw_md_fds _ _)) ]
      | lia ] ]
  end.

Lemma kr_skip : forall POST n,
  at_cut GI_KREC POST (S n) ->
  forall cx fp k acc ly3 S3 W3 (ms3 : machine_state) md3 b h buf i p e,
  pe_base SK B MT KS cx ->
  ajournal_gx SEGS B pe_G 0 [] LLVMF_STK (spZ (c_regs cx)) [sink_token] (c_ly cx) (c_S cx) (c_W cx)
    (c_mem cx) (c_md cx) [(PE_CID, fp)] ly3 S3 W3 (ms_mem ms3) md3 k ->
  frames S3 = [(PE_CID, fp)] -> mo_le MT (c_S cx) S3 acc ->
  kr_body cx fp k acc ly3 S3 W3 ms3 md3 b h buf i p e ->
  (Z.to_nat (p_nF cx - e) <= S n)%nat ->
  (forall (ms' : machine_state) md' e',
     ajournal_gx SEGS B pe_G 0 [] LLVMF_STK (spZ (c_regs cx)) [sink_token] (c_ly cx) (c_S cx) (c_W cx)
       (c_mem cx) (c_md cx) [(PE_CID, fp)] ly3 S3 W3 (ms_mem ms') md' k ->
     kr_body cx fp k acc ly3 S3 W3 ms' md' b h buf i p e' -> e < e' -> SRr SEGS W3 (mkCfg ms' md') (POST cx)) ->
  SRr SEGS W3 (mkCfg ms3 md3) (POST cx).
Proof.
intros POST n HREC cx fp k acc ly3 S3 W3 ms3 md3 b h buf i p e HB HJ Hfrs Hmo HKB Hmeas IH.
pose proof HKB as (HCUT & Hpad & H26 & Hgood & Hi0 & Hip & HK & Hpe & Hsk & He16 & R6 & R11 & R12 & R14 & R18
  & R19 & R21 & R22 & R23 & R24 & R25 & Hls & Hfirst & Hglob & Hrd).
pose proof HCUT as (HBODY & Hk3 & Hacc & HPerm & Hfds & Hfs).
pose proof HBODY as (Hpc & Hrv & Hsv & Hrom & Hfreg & Hfcsr & Hregs & Hsaved & Hhdr & Hshd & Hshlen & Hinp).
pose proof Hregs as (G2 & G8 & G9 & G27 & G3 & G4).
pose proof (p_sizes cx) as (HnF & Hcap & Hbn).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (proj1 Hrd) as (Wl & cpos & fl & mdd & _ & _ & _ & _ & HbF & _ & _ & _ & HCg & _).
pose proof HJ as (_ & _ & (memS & HJi & _) & _). pose proof HJi as (HAR & _).
pose proof (h_blocks3 B LAWS ly3 S3 W3 (ms_mem ms3) md3 _ _ _ _ HAR HPerm) as (Hb_in & _).
destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR Hb_in) as (_ & Hb4096 & Hbceil & Hbapp & _).
pose proof (req_size_pos (p_nF cx) ltac:(lia)) as [_ Hreqb].
assert (HIr : 0 <= kr_incl cx e < 2 ^ 32) by (unfold kr_incl, PSN.incl; apply PW.pw_hw_range).
(* 0x80b70 add s10,s3,s2 *)
pose proof (hw_entry_body W3 ms3 PP_KR Hpc Hrv Hsv Hrom Hfreg Hfcsr) as HS.
set (E := Eimg (Ereg (ms_regs ms3) [w64 HW_SB])) in HS.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EEo : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr (ms_regs ms3) r).
{ intros n0 r Hn. subst E. pose proof (bv_unsigned_in_range 5 r) as Hr5.
  change (bv_modulus 5) with 32 in Hr5.
  rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_nat. exact Hn. }
pose proof (hw_sh_nil E (mrestrict (w_H W3) (ms_mem ms3))) as SHOK.
paj_run_to_tok RUNTO HS HJ SHOK HWspan PP_KRS; [apply awr_ok_x_nil|].
pose proof (hw_mem_kept E _ _ _ eq_refl HF) as Hm0. clear HF HFr HG.
pose proof (st_ok_pi_restrict_mkst (w_H W3) _ _ ms HS eq_refl) as Hsh1. cbn [ss_pc] in Hsh1.
assert (KP1 : kr_kept kr_keep1 ms ms3).
{ intros r Hr. apply (regs_kept_of_st_ok_pi E _ _ (ms_regs ms3) [w64 HW_SB] kr_keep1 HS); [|vm_compute; reflexivity | exact Hr].
  split; [intros n0 Hn0; subst E; apply Eimg_low; unfold A_TEXT; lia | reflexivity]. }
prreg HS (26%bv : bv 5) Q26. rewrite (EEo 18%nat 18%bv eq_refl), (EEo 19%nat 19%bv eq_refl), R18, R19 in Q26.
unfold w64 in Q26. rewrite alu64_add_lit in Q26.
prreg HS (23%bv : bv 5) Q23. rewrite (EEo 23%nat 23%bv eq_refl), R23 in Q23.
prreg HS (24%bv : bv 5) Q24. rewrite (EEo 24%nat 24%bv eq_refl), R24 in Q24.
prreg HS (27%bv : bv 5) Q27. rewrite (EEo 27%nat 27%bv eq_refl), G27 in Q27.
rewrite Z.add_comm in Q26. rewrite <- KR_SB_eq in Q27.
assert (Hbe : 4096 <= b + e <= 2 ^ 47 - 64) by lia.
set (D := skipn (Z.to_nat e) (p_F cx)).
assert (HDm : forall j, 0 <= j -> e + j < p_nF cx -> exists x, nth_error D (Z.to_nat j) = Some x /\
   mbyte SEGS (mrestrict (w_H W3) (ms_mem ms)) (b + e + j) = Some x).
{ intros j Hj0 Hj. unfold p_nF in Hj. exists (nth (Z.to_nat (e + j)) (p_F cx) (Z_to_bv 8 0)). split.
  - apply kr_D_nth; [lia | lia | exact Hj].
  - rewrite Hm0. replace (b + e + j) with (b + (e + j)) by lia. apply (kr_copy_mbyte _ b (p_F cx) (e + j) HCg). lia. }
pose proof (kr_env_img (ms_regs ms) [] D) as HEI1.
assert (SHOK1 : sh_ok SEGS krBx (kr_SH 8 12) (kr_env (ms_regs ms) [] D) (mrestrict (w_H W3) (ms_mem ms))).
{ pose proof HJ as (_ & _ & (memS1 & HJi1 & _) & _). pose proof HJi1 as (HAR1 & _).
  apply (kr_shok (ms_regs ms) [] D _ (b + e) 8 12 Q26 Q27); [lia | lia | lia | |].
  - replace KR_SB with (U (kr_env (ms_regs ms) [] D) (SLit KR_SB)) by (rewrite U_lit; [reflexivity | unfold KR_SB; lia]).
    apply (obl_of_block SEGS B LAWS ly3 S3 W3 (ms_mem ms) _ _ (SLit KR_SB) (b + e + 8) (12 - 8) b (p_nF cx) HAR1 Hb_in);
      [rewrite U_lit; [reflexivity | unfold KR_SB; lia] | lia | lia].
  - intros a Ha. unfold in_app, kLowShadowBeg, kHighMemBeg in Hbapp. unfold KR_SB. lia. }
assert (UDg : forall E2, ed E2 0 = D -> forall j, 0 <= j < 32 -> e + j < p_nF cx ->
  U E2 (SData 0 j 1) = PSN.fb (p_F cx) (e + j))
  by (intros E2 ED2 j Hj Hj2; unfold p_nF in Hj2; apply (kr_U_fbE E2 (p_F cx) e j ED2); lia).
destruct (kr_swz cx) as [Hsw | Hsw]; rewrite Hsw in Q24.
- (* little-endian (0x80bec beqz s8 taken) *)
  assert (HS1 := kr_seat_skip W3 (ms_regs ms) (ms_mem ms) 0 D (b + e) Q23 Q24 Q26 Q27 Hbe
    (fun j Hj => HDm j ltac:(lia) ltac:(lia))).
  unfold PP_KRS in HS1. rewrite <- Hsh1 in HS1.
  paj_run_tok RUN HS1 HJ SHOK1 krSpan; [kr_nowin|].
  kr_kept_run HF Hm1.
  lazymatch type of HS1 with st_ok_pi _ _ ?Ex _ _ => set (E2 := Ex) in * end.
  pose proof (UDg E2 eq_refl) as UD.
  assert (AG2 : forall n, (n < 32)%nat -> ew E2 n = ew (kr_env (ms_regs ms) [] D) n) by (unfold E2; kr_agree).
  assert (Hpsw : p_sw cx = false) by (unfold p_sw; rewrite Hsw; reflexivity).
  assert (UI : U E2 (kb_le32w (SData 0 8 1) (SData 0 9 1) (SData 0 10 1) (SData 0 11 1)) = kb_sx32 (kr_incl cx e)).
  { rewrite (kb_le32w_U E2 _ _ _ _ _ _ _ _ (UD 8 ltac:(lia) ltac:(lia)) (UD 9 ltac:(lia) ltac:(lia))
      (UD 10 ltac:(lia) ltac:(lia)) (UD 11 ltac:(lia) ltac:(lia)) (kr_fb_range _ _) (kr_fb_range _ _)
      (kr_fb_range _ _) (kr_fb_range _ _)).
    unfold kr_incl, PSN.incl. rewrite Hpsw, kr_hw_le.
    replace (e + 8 + 1) with (e + 9) by lia. replace (e + 8 + 2) with (e + 10) by lia.
    replace (e + 8 + 3) with (e + 11) by lia. reflexivity. }
  unfold kb_le32w, kb_lo3 in UI.
  assert (U11 : U E2 (SOff 11 0) = p_nF cx).
  { apply U_atom; [|lia]. rewrite AG2 by lia. rewrite (kr_env_reg _ _ _ 11 11%bv eq_refl).
    rewrite (KP1 11%bv ltac:(kr_in)), R11. reflexivity. }
  assert (U18 : U E2 (SOff 18 0) = e).
  { apply U_atom; [|lia]. rewrite AG2 by lia. rewrite (kr_env_reg _ _ _ 18 18%bv eq_refl).
    rewrite (KP1 18%bv ltac:(kr_in)), R18. reflexivity. }
  assert (U21 : U E2 (SOff 21 0) = p_cap cx).
  { apply U_atom; [|lia]. rewrite AG2 by lia. rewrite (kr_env_reg _ _ _ 21 21%bv eq_refl).
    rewrite (KP1 21%bv ltac:(kr_in)), R21. reflexivity. }
  psrr_branch_tok RUN BR HS1 SHOK1 krSpan.
  + (* incl = 0: an empty record, skipped (0x80c1c beqz s4 -> 0x80c24) *)
    rewrite branch_eq_U, UI, U_lit in Hc by lia. apply Z.eqb_eq in Hc.
    assert (HI0 : kr_incl cx e = 0) by (apply (kb_sx32_zero _ HIr); exact Hc).
    destruct (kr_m_empty (p_sw cx) (p_F cx) (p_cap cx) e (p_q cx p) Hsk HK He16 HI0) as (Hsk' & He32).
    change (PSN.flen (p_F cx)) with (p_nF cx) in He32.
    paj_run_tok RUN HS1 HJ SHOK1 krSpan; [kr_nowin|].
    kr_kept_run HF Hm2.
    psrr_branch_tok RUN BR HS1 SHOK1 krSpan.
    * (* 0x80c30 bgeu taken: round the loop again *)
      rewrite branch_geu_U, U11, !kb_add_U, kb_zext32_U, UI, U18, kb_sx32_mod, U_SLit in Hc0 by exact HIr.
      kr_zc Hc0. apply Bool.negb_true_iff, Z.ltb_ge in Hc0.
      paj_run_to_tok RUNTO HS1 HJ SHOK1 krSpan PP_KR; [kr_nowin|].
      kr_kept_run HF Hm3.
      assert (Hmem : ms_mem ms2 = ms_mem ms3) by (rewrite Hm3, Hm2, Hm1, Hm0; reflexivity).
      assert (Hskp : p_skips cx (e + kr_incl cx e + 16) (p_q cx p)) by (rewrite HI0, Z.add_0_r; exact Hsk').
      assert (He' : e + kr_incl cx e + 16 + 16 <= p_nF cx) by (rewrite HI0; lia).
      kr_backleaf HS1 HKB HJ IH KP1 AG2 UI U18 HIr Hmem Hsw Hskp He'.
    * (* 0x80c30 bgeu not taken -> 0x80c34 j PP_abort: refuted, e + 16 + incl + 16 <= |F| *)
      rewrite branch_geu_U, U11, !kb_add_U, kb_zext32_U, UI, U18, kb_sx32_mod, U_SLit in Hc0 by exact HIr.
      kr_zc Hc0. apply Bool.negb_false_iff, Z.ltb_lt in Hc0. exfalso. lia.
  + (* incl <> 0 (0x80c1c beqz s4 not taken) *)
    rewrite branch_eq_U, UI, U_lit in Hc by lia. apply Z.eqb_neq in Hc.
    assert (HIn0 : kr_incl cx e <> 0) by (intros HI0; apply Hc; rewrite HI0; reflexivity).
    paj_run_tok RUN HS1 HJ SHOK1 krSpan; [kr_nowin|].
    kr_kept_run HF Hm2.
    psrr_branch_tok RUN BR HS1 SHOK1 krSpan.
    * (* 0x80c20 bgeu s5,a3 taken: incl <= cap, the record the reader found *)
      rewrite branch_geu_U, U21, kb_zext32_U, UI, kb_sx32_mod in Hc0 by exact HIr.
      apply Bool.negb_true_iff, Z.ltb_ge in Hc0.
      assert (HeQ : e = p_q cx p) by exact (kr_m_fit (p_sw cx) (p_F cx) (p_cap cx) e (p_q cx p) Hsk HK He16 HIn0 Hc0).
      paj_run_to_tok RUNTO HS1 HJ SHOK1 krSpan PP_REC; [kr_nowin|].
      kr_kept_run HF Hm3.
      assert (Hmem : ms_mem ms2 = ms_mem ms3) by (rewrite Hm3, Hm2, Hm1, Hm0; reflexivity).
      pose proof (st_ok_pi_restrict_mkst (w_H W3) _ _ ms2 HS1 eq_refl) as Hsh3. cbn [ss_pc] in Hsh3.
      change 1328 with PP_REC in Hsh3.
      kregU HS1 (13%bv : bv 5) Q13. kregU HS1 (20%bv : bv 5) Q20.
      kregU HS1 (23%bv : bv 5) Q23x. kregU HS1 (24%bv : bv 5) Q24x.
      rewrite kb_zext32_U, UI, kb_sx32_mod in Q13 by exact HIr. rewrite UI in Q20.
      assert (HIs : kb_sx32 (kr_incl cx e) = kr_incl cx e) by (unfold kb_sx32; destruct (Z.ltb_spec (kr_incl cx e) (2 ^ 31)); lia).
      rewrite HIs in Q20. rewrite U_SLit in Q23x, Q24x. kr_zc Q23x. kr_zc Q24x.
      assert (KPC : kr_kept kr_keepC ms2 ms3).
      { intros r Hr. rewrite (kr_kept_env _ _ _ _ _ ms2 (w_H W3) kr_keepC HS1 AG2 ltac:(vm_compute; reflexivity) r Hr).
        exact (KP1 r (kr_keepC_1 r Hr)). }
      assert (K1418 : forall r, In r [14%bv; 18%bv; 26%bv] -> getr (ms_regs ms2) r = getr (ms_regs ms) r)
        by (exact (kr_kept_env _ _ _ _ _ ms2 (w_H W3) [14%bv; 18%bv; 26%bv] HS1 AG2 ltac:(vm_compute; reflexivity))).
      apply (HREC cx fp k acc ly3 S3 W3 ms2 _ HB HJ Hfrs Hmo).
      { exists b, h, buf, i, p.
        apply (kr_to_rec cx fp k acc ly3 S3 W3 ms3 md3 ms2 _ b h buf i p e HKB Hmem Hsh3 KPC).
        - rewrite (K1418 14%bv ltac:(kr_in)). exact (KP1 14%bv ltac:(kr_in)).
        - rewrite (K1418 18%bv ltac:(kr_in)). exact (KP1 18%bv ltac:(kr_in)).
        - exact Q23x.
        - rewrite Q24x, Hsw. reflexivity.
        - exact Q13.
        - exact Q20.
        - rewrite (K1418 26%bv ltac:(kr_in)). exact Q26.
        - exact HeQ.
        - exact (proj1 (hw_md_fds _ _)).
        - exact (proj2 (hw_md_fds _ _)). }
      { unfold hw_meas, hw_pos. rewrite (K1418 18%bv ltac:(kr_in)), (KP1 18%bv ltac:(kr_in)), R18.
        unfold w64. rewrite unsigned_lit_small by lia. exact Hmeas. }
    * (* 0x80c20 bgeu not taken: cap < incl, a record too big for the buffer, skipped *)
      rewrite branch_geu_U, U21, kb_zext32_U, UI, kb_sx32_mod in Hc0 by exact HIr.
      apply Bool.negb_false_iff, Z.ltb_lt in Hc0.
      destruct (kr_m_big (p_sw cx) (p_F cx) (p_cap cx) e (p_q cx p) Hsk HK He16 HIn0 Hc0) as (Hsk' & He32).
      change (PSN.flen (p_F cx)) with (p_nF cx) in He32.
      change (PSN.incl (p_sw cx) (p_F cx) e) with (kr_incl cx e) in He32, Hsk'.
      paj_run_tok RUN HS1 HJ SHOK1 krSpan; [kr_nowin|].
      kr_kept_run HF Hm3.
      psrr_branch_tok RUN BR HS1 SHOK1 krSpan.
      -- (* 0x80c30 bgeu taken: round the loop again *)
        rewrite branch_geu_U, U11, !kb_add_U, kb_zext32_U, UI, U18, kb_sx32_mod, U_SLit in Hc1 by exact HIr.
        kr_zc Hc1. apply Bool.negb_true_iff, Z.ltb_ge in Hc1.
        paj_run_to_tok RUNTO HS1 HJ SHOK1 krSpan PP_KR; [kr_nowin|].
        kr_kept_run HF Hm4.
        lazymatch goal with |- SRr _ _ (mkCfg ?msx _) _ =>
          assert (Hmem : ms_mem msx = ms_mem ms3) by (rewrite Hm4, Hm3, Hm2, Hm1, Hm0; reflexivity) end.
        assert (Hskp : p_skips cx (e + kr_incl cx e + 16) (p_q cx p))
          by (replace (e + kr_incl cx e + 16) with (e + 16 + kr_incl cx e) by lia; exact Hsk').
        assert (He' : e + kr_incl cx e + 16 + 16 <= p_nF cx) by lia.
        kr_backleaf HS1 HKB HJ IH KP1 AG2 UI U18 HIr Hmem Hsw Hskp He'.
      -- (* 0x80c30 bgeu not taken -> PP_abort: refuted *)
        rewrite branch_geu_U, U11, !kb_add_U, kb_zext32_U, UI, U18, kb_sx32_mod, U_SLit in Hc1 by exact HIr.
        kr_zc Hc1. apply Bool.negb_false_iff, Z.ltb_lt in Hc1. exfalso. lia.
- (* byte-swapped (0x80bec beqz s8 not taken) *)
  assert (HS1 := kr_seat_skip W3 (ms_regs ms) (ms_mem ms) 1 D (b + e) Q23 Q24 Q26 Q27 Hbe
    (fun j Hj => HDm j ltac:(lia) ltac:(lia))).
  unfold PP_KRS in HS1. rewrite <- Hsh1 in HS1.
  paj_run_tok RUN HS1 HJ SHOK1 krSpan; [kr_nowin|].
  kr_kept_run HF Hm1.
  lazymatch type of HS1 with st_ok_pi _ _ ?Ex _ _ => set (E2 := Ex) in * end.
  pose proof (UDg E2 eq_refl) as UD.
  assert (AG2 : forall n, (n < 32)%nat -> ew E2 n = ew (kr_env (ms_regs ms) [] D) n) by (unfold E2; kr_agree).
  assert (Hpsw : p_sw cx = true) by (unfold p_sw; rewrite Hsw; reflexivity).
  assert (UI : U E2 (kb_be32w (SData 0 8 1) (SData 0 9 1) (SData 0 10 1) (SData 0 11 1)) = kb_sx32 (kr_incl cx e)).
  { rewrite (kb_be32w_U E2 _ _ _ _ _ _ _ _ (UD 8 ltac:(lia) ltac:(lia)) (UD 9 ltac:(lia) ltac:(lia))
      (UD 10 ltac:(lia) ltac:(lia)) (UD 11 ltac:(lia) ltac:(lia)) (kr_fb_range _ _) (kr_fb_range _ _)
      (kr_fb_range _ _) (kr_fb_range _ _)).
    unfold kr_incl, PSN.incl. rewrite Hpsw, kr_hw_be.
    replace (e + 8 + 1) with (e + 9) by lia. replace (e + 8 + 2) with (e + 10) by lia.
    replace (e + 8 + 3) with (e + 11) by lia. reflexivity. }
  unfold kb_be32w, kb_le32w, kb_lo3 in UI.
  assert (U11 : U E2 (SOff 11 0) = p_nF cx).
  { apply U_atom; [|lia]. rewrite AG2 by lia. rewrite (kr_env_reg _ _ _ 11 11%bv eq_refl).
    rewrite (KP1 11%bv ltac:(kr_in)), R11. reflexivity. }
  assert (U18 : U E2 (SOff 18 0) = e).
  { apply U_atom; [|lia]. rewrite AG2 by lia. rewrite (kr_env_reg _ _ _ 18 18%bv eq_refl).
    rewrite (KP1 18%bv ltac:(kr_in)), R18. reflexivity. }
  assert (U21 : U E2 (SOff 21 0) = p_cap cx).
  { apply U_atom; [|lia]. rewrite AG2 by lia. rewrite (kr_env_reg _ _ _ 21 21%bv eq_refl).
    rewrite (KP1 21%bv ltac:(kr_in)), R21. reflexivity. }
  psrr_branch_tok RUN BR HS1 SHOK1 krSpan.
  + (* incl = 0: an empty record, skipped (0x80c1c beqz s4 -> 0x80c24) *)
    rewrite branch_eq_U, UI, U_lit in Hc by lia. apply Z.eqb_eq in Hc.
    assert (HI0 : kr_incl cx e = 0) by (apply (kb_sx32_zero _ HIr); exact Hc).
    destruct (kr_m_empty (p_sw cx) (p_F cx) (p_cap cx) e (p_q cx p) Hsk HK He16 HI0) as (Hsk' & He32).
    change (PSN.flen (p_F cx)) with (p_nF cx) in He32.
    paj_run_tok RUN HS1 HJ SHOK1 krSpan; [kr_nowin|].
    kr_kept_run HF Hm2.
    psrr_branch_tok RUN BR HS1 SHOK1 krSpan.
    * (* 0x80c30 bgeu taken: round the loop again *)
      rewrite branch_geu_U, U11, !kb_add_U, kb_zext32_U, UI, U18, kb_sx32_mod, U_SLit in Hc0 by exact HIr.
      kr_zc Hc0. apply Bool.negb_true_iff, Z.ltb_ge in Hc0.
      paj_run_to_tok RUNTO HS1 HJ SHOK1 krSpan PP_KR; [kr_nowin|].
      kr_kept_run HF Hm3.
      assert (Hmem : ms_mem ms2 = ms_mem ms3) by (rewrite Hm3, Hm2, Hm1, Hm0; reflexivity).
      assert (Hskp : p_skips cx (e + kr_incl cx e + 16) (p_q cx p)) by (rewrite HI0, Z.add_0_r; exact Hsk').
      assert (He' : e + kr_incl cx e + 16 + 16 <= p_nF cx) by (rewrite HI0; lia).
      kr_backleaf HS1 HKB HJ IH KP1 AG2 UI U18 HIr Hmem Hsw Hskp He'.
    * (* 0x80c30 bgeu not taken -> 0x80c34 j PP_abort: refuted, e + 16 + incl + 16 <= |F| *)
      rewrite branch_geu_U, U11, !kb_add_U, kb_zext32_U, UI, U18, kb_sx32_mod, U_SLit in Hc0 by exact HIr.
      kr_zc Hc0. apply Bool.negb_false_iff, Z.ltb_lt in Hc0. exfalso. lia.
  + (* incl <> 0 (0x80c1c beqz s4 not taken) *)
    rewrite branch_eq_U, UI, U_lit in Hc by lia. apply Z.eqb_neq in Hc.
    assert (HIn0 : kr_incl cx e <> 0) by (intros HI0; apply Hc; rewrite HI0; reflexivity).
    paj_run_tok RUN HS1 HJ SHOK1 krSpan; [kr_nowin|].
    kr_kept_run HF Hm2.
    psrr_branch_tok RUN BR HS1 SHOK1 krSpan.
    * (* 0x80c20 bgeu s5,a3 taken: incl <= cap, the record the reader found *)
      rewrite branch_geu_U, U21, kb_zext32_U, UI, kb_sx32_mod in Hc0 by exact HIr.
      apply Bool.negb_true_iff, Z.ltb_ge in Hc0.
      assert (HeQ : e = p_q cx p) by exact (kr_m_fit (p_sw cx) (p_F cx) (p_cap cx) e (p_q cx p) Hsk HK He16 HIn0 Hc0).
      paj_run_to_tok RUNTO HS1 HJ SHOK1 krSpan PP_REC; [kr_nowin|].
      kr_kept_run HF Hm3.
      assert (Hmem : ms_mem ms2 = ms_mem ms3) by (rewrite Hm3, Hm2, Hm1, Hm0; reflexivity).
      pose proof (st_ok_pi_restrict_mkst (w_H W3) _ _ ms2 HS1 eq_refl) as Hsh3. cbn [ss_pc] in Hsh3.
      change 1328 with PP_REC in Hsh3.
      kregU HS1 (13%bv : bv 5) Q13. kregU HS1 (20%bv : bv 5) Q20.
      kregU HS1 (23%bv : bv 5) Q23x. kregU HS1 (24%bv : bv 5) Q24x.
      rewrite kb_zext32_U, UI, kb_sx32_mod in Q13 by exact HIr. rewrite UI in Q20.
      assert (HIs : kb_sx32 (kr_incl cx e) = kr_incl cx e) by (unfold kb_sx32; destruct (Z.ltb_spec (kr_incl cx e) (2 ^ 31)); lia).
      rewrite HIs in Q20. rewrite U_SLit in Q23x, Q24x. kr_zc Q23x. kr_zc Q24x.
      assert (KPC : kr_kept kr_keepC ms2 ms3).
      { intros r Hr. rewrite (kr_kept_env _ _ _ _ _ ms2 (w_H W3) kr_keepC HS1 AG2 ltac:(vm_compute; reflexivity) r Hr).
        exact (KP1 r (kr_keepC_1 r Hr)). }
      assert (K1418 : forall r, In r [14%bv; 18%bv; 26%bv] -> getr (ms_regs ms2) r = getr (ms_regs ms) r)
        by (exact (kr_kept_env _ _ _ _ _ ms2 (w_H W3) [14%bv; 18%bv; 26%bv] HS1 AG2 ltac:(vm_compute; reflexivity))).
      apply (HREC cx fp k acc ly3 S3 W3 ms2 _ HB HJ Hfrs Hmo).
      { exists b, h, buf, i, p.
        apply (kr_to_rec cx fp k acc ly3 S3 W3 ms3 md3 ms2 _ b h buf i p e HKB Hmem Hsh3 KPC).
        - rewrite (K1418 14%bv ltac:(kr_in)). exact (KP1 14%bv ltac:(kr_in)).
        - rewrite (K1418 18%bv ltac:(kr_in)). exact (KP1 18%bv ltac:(kr_in)).
        - exact Q23x.
        - rewrite Q24x, Hsw. reflexivity.
        - exact Q13.
        - exact Q20.
        - rewrite (K1418 26%bv ltac:(kr_in)). exact Q26.
        - exact HeQ.
        - exact (proj1 (hw_md_fds _ _)).
        - exact (proj2 (hw_md_fds _ _)). }
      { unfold hw_meas, hw_pos. rewrite (K1418 18%bv ltac:(kr_in)), (KP1 18%bv ltac:(kr_in)), R18.
        unfold w64. rewrite unsigned_lit_small by lia. exact Hmeas. }
    * (* 0x80c20 bgeu not taken: cap < incl, a record too big for the buffer, skipped *)
      rewrite branch_geu_U, U21, kb_zext32_U, UI, kb_sx32_mod in Hc0 by exact HIr.
      apply Bool.negb_false_iff, Z.ltb_lt in Hc0.
      destruct (kr_m_big (p_sw cx) (p_F cx) (p_cap cx) e (p_q cx p) Hsk HK He16 HIn0 Hc0) as (Hsk' & He32).
      change (PSN.flen (p_F cx)) with (p_nF cx) in He32.
      change (PSN.incl (p_sw cx) (p_F cx) e) with (kr_incl cx e) in He32, Hsk'.
      paj_run_tok RUN HS1 HJ SHOK1 krSpan; [kr_nowin|].
      kr_kept_run HF Hm3.
      psrr_branch_tok RUN BR HS1 SHOK1 krSpan.
      -- (* 0x80c30 bgeu taken: round the loop again *)
        rewrite branch_geu_U, U11, !kb_add_U, kb_zext32_U, UI, U18, kb_sx32_mod, U_SLit in Hc1 by exact HIr.
        kr_zc Hc1. apply Bool.negb_true_iff, Z.ltb_ge in Hc1.
        paj_run_to_tok RUNTO HS1 HJ SHOK1 krSpan PP_KR; [kr_nowin|].
        kr_kept_run HF Hm4.
        lazymatch goal with |- SRr _ _ (mkCfg ?msx _) _ =>
          assert (Hmem : ms_mem msx = ms_mem ms3) by (rewrite Hm4, Hm3, Hm2, Hm1, Hm0; reflexivity) end.
        assert (Hskp : p_skips cx (e + kr_incl cx e + 16) (p_q cx p))
          by (replace (e + kr_incl cx e + 16) with (e + 16 + kr_incl cx e) by lia; exact Hsk').
        assert (He' : e + kr_incl cx e + 16 + 16 <= p_nF cx) by lia.
        kr_backleaf HS1 HKB HJ IH KP1 AG2 UI U18 HIr Hmem Hsw Hskp He'.
      -- (* 0x80c30 bgeu not taken -> PP_abort: refuted *)
        rewrite branch_geu_U, U11, !kb_add_U, kb_zext32_U, UI, U18, kb_sx32_mod, U_SLit in Hc1 by exact HIr.
        kr_zc Hc1. apply Bool.negb_false_iff, Z.ltb_lt in Hc1. exfalso. lia.
Qed.


(* ---- the record checks, 0x80c68 .. 0x80fa0: the context they keep ---- *)
(* The record state at 0x80c68 (the reference: kr_rbody), with the call's frame and journal. *)
Definition kr_ctx (cx : ecx) (fp k acc : Z) (ly3 : alayout) (S3 : astate) (W3 : world SEGS)
  (ms3 : machine_state) (md3 : Model) (b h buf i p : Z) : Prop :=
  pe_base SK B MT KS cx /\
  ajournal_gx SEGS B pe_G 0 [] LLVMF_STK (spZ (c_regs cx)) [sink_token] (c_ly cx) (c_S cx) (c_W cx)
    (c_mem cx) (c_md cx) [(PE_CID, fp)] ly3 S3 W3 (ms_mem ms3) md3 k /\
  frames S3 = [(PE_CID, fp)] /\ mo_le MT (c_S cx) S3 acc /\
  kr_rbody cx fp k acc ly3 S3 W3 ms3 md3 b h buf i p.

(* The callee-saved registers, sp, gp and tp: what the record checks and the bcmp calls keep. *)
Definition kr_keepS : list (bv 5) :=
  [2%bv; 3%bv; 4%bv; 8%bv; 9%bv; 18%bv; 19%bv; 20%bv; 21%bv; 22%bv; 23%bv; 24%bv; 25%bv; 26%bv; 27%bv].

(* A later state of the record checks: the same journal, every byte outside the bcmp wrapper's scratch window below
   s1 as at 0x80c68, the kept registers, and the descriptors and file system. *)
Definition kr_now (cx : ecx) (fp k : Z) (ly3 : alayout) (S3 : astate) (W3 : world SEGS) (ms3 : machine_state)
  (md3 : Model) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) : Prop :=
  ajournal_gx SEGS B pe_G 0 [] LLVMF_STK (spZ (c_regs cx)) [sink_token] (c_ly cx) (c_S cx) (c_W cx)
    (c_mem cx) (c_md cx) [(PE_CID, fp)] ly3 S3 W3 mem md k /\
  (forall a, 0 <= a < 2 ^ 64 -> ~ (c_sp1 cx - 8192 <= a < c_sp1 cx) ->
     aview SEGS (w_H W3) mem a = aview SEGS (w_H W3) (ms_mem ms3) a) /\
  (forall r, In r kr_keepS -> getr regs r = getr (ms_regs ms3) r) /\
  m_fds md = m_fds md3 /\ m_fs md = m_fs md3.

(* The atoms of a record seat: &ps, first, and ps's orig / vlan_tagged / vlan_id and ts as the reader left them
   for the record Q = psn_q p; the data list: the copy from Q on. *)
Definition kr_Xc (cx : ecx) (fp p : Z) : list word :=
  let Q := p_q cx p in
  kr_X (pPS cx fp) (p_first cx) (PSN.orig (p_sw cx) (p_F cx) Q)
    (if PSN.tagged (p_sw cx) (p_F cx) Q then 1 else 0)
    (if PSN.tagged (p_sw cx) (p_F cx) Q then PSN.rec_vid (p_F cx) Q else 0)
    (PSN.rec_ts (p_sw cx) (p_F cx) Q).
Definition kr_Dc (cx : ecx) (p : Z) : list byte := skipn (Z.to_nat (p_q cx p)) (p_F cx).

Lemma kr_now_ref : forall cx fp k acc ly3 S3 W3 ms3 md3 b h buf i p,
  kr_ctx cx fp k acc ly3 S3 W3 ms3 md3 b h buf i p ->
  kr_now cx fp k ly3 S3 W3 ms3 md3 (ms_regs ms3) (ms_mem ms3) md3.
Proof.
  intros cx fp k acc ly3 S3 W3 ms3 md3 b h buf i p (HB & HJ & _).
  split; [exact HJ|]. split; [intros a _ _; reflexivity|]. split; [intros r _; reflexivity|]. split; reflexivity.
Qed.

Lemma kr_rec_vid_range : forall F q, 0 <= PSN.rec_vid F q < 4096.
Proof. intros F q. unfold PSN.rec_vid. apply Z.mod_pos_bound. lia. Qed.

Lemma kr_seat_now : forall cx fp k acc ly3 S3 W3 ms3 md3 b h buf i p (regs : bvmap 5 word) mem md pc
  (L32 pin6 pin10 wts : bool),
  kr_ctx cx fp k acc ly3 S3 W3 ms3 md3 b h buf i p ->
  kr_now cx fp k ly3 S3 W3 ms3 md3 regs mem md ->
  (L32 = true -> 16 <= kr_incl cx (p_q cx p)) ->
  (pin6 = true -> getr regs 6 = w64 (pPS cx fp)) ->
  (pin10 = true -> getr regs 10 = w64 0) ->
  st_ok_pi SEGS VAL (kr_env regs (kr_Xc cx fp p) (kr_Dc cx p)) (kr_ss_rec pc (p_swz cx) (kr_L L32) pin6 pin10 wts)
    (restrict (w_H W3) (mkst regs (Z_to_bv 64 (BASE + pc)) mem (seg_rom SEGS))) /\
  sh_ok SEGS krBx (kr_SHr (kr_L L32) wts) (kr_env regs (kr_Xc cx fp p) (kr_Dc cx p)) (mrestrict (w_H W3) mem).
Proof.
  intros cx fp k acc ly3 S3 W3 ms3 md3 b h buf i p regs mem md pc L32 pin6 pin10 wts Hctx Hnow HL32 HP6 HP10.
  destruct Hctx as (HB & HJ3 & Hfrs & Hmo & HRB).
  destruct HRB as (HCUT & Hpad & H26 & Hgood & Hi0 & Hip & HK & Hpe & R6 & R11 & R12 & R13 & R14 & R18 & R19 & R20
    & R21 & R22 & R23 & R24 & R25 & R26 & Hls & Hfirst & Hglob & Hrd).
  destruct Hnow as (HJ & Hkept & KS3 & _ & _).
  pose proof HCUT as (HBODY & _ & _ & HPerm & _).
  pose proof HBODY as (_ & _ & _ & _ & _ & _ & (G2 & G8 & G9 & G27 & G3 & G4) & _).
  pose proof (h_sp SK B MT KS cx HB) as (Hsp16 & Hsp_lo & Hsp_hi & Hsp1 & Hsp1_32).
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  pose proof (p_sizes cx) as (HnF & Hcap & Hbn).
  pose proof HJ as (_ & _ & (memS & HJi & _) & _). rewrite !Z.add_0_r in HJi. pose proof HJi as (HAR & _).
  pose proof HJ3 as (_ & _ & (memS3 & HJi3 & _) & _). rewrite !Z.add_0_r in HJi3. pose proof HJi3 as (HAR3 & _).
  pose proof (h_frame SK B MT KS LAWS cx fp memS ly3 S3 W3 mem md k HB HJi Hfrs)
    as (EF & EFL & HF4096 & HFceil & HF64 & HFapp & HFimg & ESH & HFpres & HSHpres).
  pose proof (h_blocks3 B LAWS ly3 S3 W3 (ms_mem ms3) md3 _ _ _ _ HAR3 HPerm)
    as (Hb_in & Hh_in & Hbuf_in & Hb_fr & Hh_fr & Hbuf_fr & Dbh & Dbbuf & Dhbuf).
  destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR3 Hb_in) as (_ & Hb4096 & Hbceil & Hbapp & _).
  destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR3 Hbuf_in) as (_ & Hbuf4096 & Hbufceil & _).
  pose proof (req_size_pos (p_nF cx) ltac:(lia)) as [_ Hreqb].
  pose proof (req_size_pos (p_bn cx) ltac:(lia)) as [_ Hreqbn].
  assert (Hfin : In (PE_CID, fp) (frames S3)) by (rewrite Hfrs; left; reflexivity).
  pose proof (sep_block_frame SEGS B LAWS _ _ _ _ _ _ _ _ _ HAR3 Hb_in Hfin) as Db.
  pose proof (h_frame SK B MT KS LAWS cx fp memS3 ly3 S3 W3 (ms_mem ms3) md3 k HB HJi3 Hfrs) as (EF3 & _).
  rewrite EF3 in Db. change (fs_frame_bytes PE_CID) with 128 in Db.
  (* the model *)
  destruct (PW.kind_fit (p_sw cx) (p_F cx) (p_cap cx) (p_q cx p) HK) as (_ & _ & _ & HQfit & HQincl).
  change (PSN.flen (p_F cx)) with (p_nF cx) in HQfit.
  assert (HQ0 : 24 <= (p_q cx p)) by (pose proof (PW.psn_q_ge (p_sw cx) (p_F cx) (p_cap cx) p); unfold p_q; lia).
  (* the kept bytes *)
  assert (HE : hw_eqon W3 (ms_mem ms3) mem (fun a => 0 <= a < 2 ^ 64 /\ ~ (c_sp1 cx + (-8192) <= a < c_sp1 cx + 0))).
  { apply hw_eqon_of_kept. intros a Ha Hn. apply Hkept; [exact Ha | lia]. }
  assert (HPlow : forall a, 0 <= a < alloc_ceiling -> 0 <= a < 2 ^ 64 /\ ~ (c_sp1 cx + (-8192) <= a < c_sp1 cx + 0))
    by (intros a Ha; split; lia).
  assert (HPslot : forall o j, 0 <= o -> o + 8 <= 96 -> 0 <= j < 8 ->
    0 <= c_sp1 cx + o + j < 2 ^ 64 /\ ~ (c_sp1 cx + (-8192) <= c_sp1 cx + o + j < c_sp1 cx + 0))
    by (intros o j Ho1 Ho2 Hj; split; lia).
  (* registers *)
  assert (KR : forall r, In r kr_keepS -> getr regs r = getr (ms_regs ms3) r) by exact KS3.
  assert (Rsw : getr regs 24 = w64 (p_swz cx)) by (rewrite (KR 24%bv ltac:(kr_in)); exact R24).
  (* the KFit fields at 0x80c68 *)
  destruct Hrd as (Hsrc & Hpso & Hfit). specialize (Hfit HK) as (Vo & Vt & Vv & Vts & Vbuf).
  pose proof Hsrc as (Wl & cpos & fl & mdd & _ & _ & _ & _ & HbF & _ & _ & _ & HCg & _).
  unfold pval, pPS, pTS, PO_PS, PO_TS in Vo, Vt, Vv, Vts.
  destruct Hls as (HSL & SVM & SB12 & SUS).
  unfold pslots, pslot, PS_PSP, PS_TSP, PO_PS, PO_TS in HSL. destruct HSL as (SPSP & _ & _ & _ & _ & _ & STSP).
  unfold pslot, PS_VMASK, PS_BUF12, PS_USEC in SVM, SB12, SUS. unfold pslot, PS_FIRST in Hfirst.
  assert (Ho : 0 <= PSN.orig (p_sw cx) (p_F cx) (p_q cx p) < 2 ^ 32) by (unfold PSN.orig; apply PW.pw_hw_range).
  assert (Hts : 0 <= PSN.rec_ts (p_sw cx) (p_F cx) (p_q cx p) < 2 ^ 64).
  { unfold PSN.rec_ts. pose proof (PW.pw_hw_range (p_sw cx) (p_F cx) (p_q cx p) 0). pose proof (PW.pw_hw_range (p_sw cx) (p_F cx) (p_q cx p) 4). lia. }
  pose proof (kr_rec_vid_range (p_F cx) (p_q cx p)) as Hvid.
    split.
  - apply (kr_seat_rec W3 regs mem pc (p_swz cx) L32 pin6 pin10 wts (kr_Dc cx p) (b + (p_q cx p)) (c_sp1 cx) buf (pF cx fp + 32)).
    + rewrite (KR 23%bv ltac:(kr_in)). exact R23.
    + exact Rsw.
    + rewrite (KR 26%bv ltac:(kr_in)). exact R26.
    + rewrite (KR 27%bv ltac:(kr_in)), G27. reflexivity.
    + rewrite (KR 9%bv ltac:(kr_in)). exact G9.
    + rewrite (KR 22%bv ltac:(kr_in)). exact R22.
    + intros H. rewrite (HP6 H). reflexivity.
    + exact HP10.
    + lia.
    + lia.
    + lia.
    + lia.
    + exact Ho.
    + destruct (PSN.tagged _ _ _); lia.
    + destruct (PSN.tagged _ _ _); lia.
    + exact Hts.
    + destruct L32; cbn [kr_L] in *; lia.
    + destruct L32; [specialize (HL32 eq_refl) | ]; cbn [kr_L]; unfold zdisjoint in Db; cbn [fst snd] in Db;
      unfold kr_incl in *; lia.
    + lia.
    + intros j Hj.
      assert (HjF : (p_q cx p) + j < p_nF cx).
      { destruct L32; [specialize (HL32 eq_refl); unfold kr_incl in HL32 | ]; cbn [kr_L] in Hj; lia. }
      exists (nth (Z.to_nat ((p_q cx p) + j)) (p_F cx) (Z_to_bv 8 0)). split.
      * unfold kr_Dc. apply kr_D_nth; [lia | destruct L32; cbn [kr_L] in Hj; lia | unfold p_nF in HjF; exact HjF].
      * rewrite (hw_mbyte_on W3 (ms_mem ms3) mem _ (b + (p_q cx p) + j) HE); [| apply HPlow; lia].
        replace (b + (p_q cx p) + j) with (b + ((p_q cx p) + j)) by lia.
        apply (kr_copy_mbyte _ b (p_F cx) ((p_q cx p) + j) HCg). unfold p_nF in HjF.
        destruct L32; cbn [kr_L] in Hj; lia.
    + apply (hw_rdword_on W3 (ms_mem ms3) mem _ _ _ HE); [intros j Hj; apply HPslot; lia | exact SVM].
    + apply (hw_rdword_on W3 (ms_mem ms3) mem _ _ _ HE); [intros j Hj; apply HPslot; lia | exact SB12].
    + apply (hw_rdword_on W3 (ms_mem ms3) mem _ _ _ HE); [intros j Hj; apply HPslot; lia | exact SUS].
    + apply (hw_rdword_on W3 (ms_mem ms3) mem _ _ _ HE); [intros j Hj; apply HPslot; lia | exact Hfirst].
    + replace (pF cx fp + 32 + 64) with (pF cx fp + 96) by lia.
      apply (hw_rdword_on W3 (ms_mem ms3) mem _ _ _ HE); [intros j Hj; apply HPslot; lia | exact STSP].
    + apply (hw_rdword_on W3 (ms_mem ms3) mem _ _ _ HE); [intros j Hj; apply HPslot; lia | exact SPSP].
    + apply (hw_val_on W3 (ms_mem ms3) mem _ _ _ _ HE); [intros j Hj; apply HPlow; cbn in Hj; lia | exact Vo].
    + apply (hw_val_on W3 (ms_mem ms3) mem _ _ _ _ HE); [intros j Hj; apply HPlow; cbn in Hj; lia | exact Vt].
    + apply (hw_val_on W3 (ms_mem ms3) mem _ _ _ _ HE); [intros j Hj; apply HPlow; cbn in Hj; lia | exact Vv].
    + replace (pF cx fp + 32 + 64) with (pF cx fp + 96) by lia.
      apply (hw_val_on W3 (ms_mem ms3) mem _ _ _ _ HE); [intros j Hj; apply HPlow; cbn in Hj; lia | exact Vts].
    + intros _ o Ho64. apply (apresent_writable SEGS). apply HFpres. lia.
  - unfold sh_ok, kr_SHr. apply Forall_cons.
    + assert (HSH : sh_ok SEGS krBx (kr_SH 0 (kr_L L32)) (kr_env regs (kr_Xc cx fp p) (kr_Dc cx p)) (mrestrict (w_H W3) mem)).
      { apply (kr_shok regs _ _ _ (b + (p_q cx p)) 0 (kr_L L32)).
        - rewrite (KR 26%bv ltac:(kr_in)). exact R26.
        - rewrite (KR 27%bv ltac:(kr_in)), G27. reflexivity.
        - lia.
        - destruct L32; cbn [kr_L] in *; lia.
        - destruct L32; cbn [kr_L] in *; lia.
        - replace KR_SB with (U (kr_env regs (kr_Xc cx fp p) (kr_Dc cx p)) (SLit KR_SB))
            by (rewrite U_lit; [reflexivity | unfold KR_SB; lia]).
          apply (obl_of_block SEGS B LAWS ly3 S3 W3 mem _ _ (SLit KR_SB) (b + (p_q cx p) + 0) (kr_L L32 - 0) b (p_nF cx) HAR Hb_in);
            [rewrite U_lit; [reflexivity | unfold KR_SB; lia] | lia |].
          assert (kr_L L32 <= 32) by (destruct L32; cbn [kr_L] in *; lia).
          destruct L32; [specialize (HL32 eq_refl); unfold kr_incl in HL32 | ]; cbn [kr_L] in *; lia.
        - intros a Ha. unfold in_app, kLowShadowBeg, kHighMemBeg in Hbapp. unfold KR_SB.
          assert (kr_L L32 <= 32) by (destruct L32; cbn [kr_L] in *; lia).
          destruct L32; [specialize (HL32 eq_refl); unfold kr_incl in HL32 | ]; cbn [kr_L] in *; lia. }
      exact (Forall_inv HSH).
    + destruct wts; [|apply Forall_nil]. apply Forall_cons; [|apply Forall_nil].
      unfold shent_ok, app_apart. cbn [she_m she_lo she_hi]. unfold krBx.
      rewrite (kr_ew_U regs _ _ 27 27%bv KR_SB eq_refl ltac:(rewrite (KR 27%bv ltac:(kr_in)), G27; reflexivity))
        by (unfold KR_SB; lia).
      assert (U32 : U (kr_env regs (kr_Xc cx fp p) (kr_Dc cx p)) (SOff 32 0) = pF cx fp + 32).
      { apply U_atom; [|lia]. rewrite (kr_env_x regs _ _ 0 ltac:(lia) : ew (kr_env regs (kr_Xc cx fp p) (kr_Dc cx p)) 32 = _).
        reflexivity. }
      rewrite U32. split.
      * change (rd_of SEGS (mrestrict (w_H W3) mem)) with (aview SEGS (w_H W3) mem).
        replace (pF cx fp + 32 + 64) with (pF cx fp + 96) by lia. rewrite KR_SB_eq.
        apply (h_ra_frame (w_H W3) mem (pF cx fp) (pSH cx fp) 96 (72 - 64) ESH HF64); [lia | reflexivity | lia |].
        intros j Hj. change ((72 - 64 + 7) / 8) with 1 in Hj. change (96 / 8) with 12.
        assert (j = 0) as -> by lia. rewrite Z.add_0_r.
        pose proof HBODY as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Hshd & _).
        assert (HSH12 : pSH cx fp + 12 < alloc_ceiling).
        { rewrite ESH. unfold SHADOW_OFF. pose proof (Z.div_le_upper_bound (pF cx fp) 8 (2 ^ 44) ltac:(lia) ltac:(lia)). lia. }
        assert (HSH0 : 0 <= pSH cx fp)
          by (rewrite ESH; unfold SHADOW_OFF; apply Z.add_nonneg_nonneg; [lia | apply Z.div_pos; lia]).
        rewrite (Hkept (pSH cx fp + 12)); [| lia | lia].
        exact (Hshd 12%nat ltac:(apply Nat.ltb_lt; vm_compute; reflexivity)).
      * intros a Ha. unfold in_app, kLowShadowBeg, kHighMemBeg in HFapp. unfold KR_SB. lia.
Qed.

(* ---- a runtime entry inside the harness's journal, with the model relation kept ---- *)
(* kr_gx_entry is PaGxSites.v's aj_gx_entry_at (lib/A/Prog/PaGxSites.v:70-174) with ONE conjunct added to its post:
   same_but_materialized mdc md2, which that proof has in hand (its Hsame) and drops. The record checks need it: the
   descriptors and the file system after the bcmp calls are the cut's (p_cut, PcapEntryPhases.v:248), and only the
   model relation carries them (wvb_fds_fs). The text below is that proof, with its local MT renamed MTg (this file's
   Section variable MT is the meter). *)
Lemma kr_gx_entry : forall G XO OUT (stk pc : Z) (Wr : Z -> Prop) (Pr : bvmap 5 word -> (word -> option byte) -> Prop)
  W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k (o : Z) raw,
gx_ok SEGS B G -> XO mod 16 = 0 ->
ajournal_gx SEGS B G XO OUT STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc k ->
spZ regsT = sp0 + o -> o mod 16 = 0 -> o <= 0 -> ESTACK <= stk -> stk - o <= STK ->
getr regsT 3 = w64 (as_gp B) -> getr regsT 4 = w64 (as_tp B) -> getr regsT 1 = raw -> YK0s.ret_ok raw ->
(forall a, Wr a \/ ~ Wr a) ->
(forall a, Wr a -> inG G a -> apresent (w_H W) memT a) ->
(forall a, Wr a -> ~ inG G a ->
 awr_byte STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own a /\ ~ (sp0 <= a < sp0 + XO)) ->
(ecall_pre SEGS B lyc Sc W regsT memT mdc -> ascratch_ok stk lyc W regsT memT ->
 SRr SEGS W (cfg_at SEGS pc regsT memT mdc) (aentry_post B stk lyc Sc W regsT memT mdc Wr Pr)) ->
SRr SEGS W (mkCfg (mkst regsT (Z_to_bv 64 pc) memT (seg_rom SEGS)) mdc)
(fun W2 c2 => W2 = W /\ exists regs2 mem2 md2,
 c2 = mkCfg (mkst regs2 raw mem2 (seg_rom SEGS)) md2 /\
 ajournal_gx SEGS B G XO OUT STK sp0 FP ly S W0 mem md own lyc Sc W mem2 md2 k /\
 same_but_materialized mdc md2 /\
 aregs_preserved regsT regs2 /\ Pr regs2 mem2 /\
 (forall a, 0 <= a < 2 ^ 64 -> ~ Wr a -> ~ (sp0 + o - stk <= a < sp0 + o) ->
  aview SEGS (w_H W) mem2 a = aview SEGS (w_H W) memT a) /\
 (forall a, apresent (w_H W) memT a -> apresent (w_H W) mem2 a)).
Proof.
intros G XO OUT stk pc Wr Pr W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k o raw
HG HX16 HJ Hsp Hal Hneg Hstk Hbud Hgp Htp Hra Hraw HWd HWg HWa AM.
pose proof pa_segs_low as Hsegs.
destruct HJ as (HSTK & HXO & (memS & HJi & Hag) & Hout).
pose proof HJi as (HAR & Hly & _ & _ & _ & Hfrs & Hnev & _ & _ & _ & _ & _ & _ & Hpres & (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop) & _ & HQT).
pose proof Hly as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & Eslo & Eshi & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5). assert (Hes : ESTACK = 4096) by reflexivity.
assert (HPRE : ecall_pre SEGS B lyc Sc W regsT memT mdc).
{ eapply (ecall_pre_at SEGS B (STK + XO) (sp0 + XO) FP ly S W0 memS md own lyc Sc W memT mdc k regsT (o - XO) HJi);
  [lia | rewrite <- Zminus_mod_idemp_r, HX16, Z.sub_0_r; exact Hal | lia | lia | rewrite Hra; exact Hraw | exact Hgp | exact Htp]. }
assert (HSC : ascratch_ok stk lyc W regsT memT).
{ split; [rewrite Eslo, Hsp; lia|]. intros a Ha. apply Hpres. rewrite Hsp in Ha. lia. }
eapply SRr_mono; [exact (AM HPRE HSC)|].
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HAR2 & HP2 & Hsame & HPr & Hfr & Hgr).
rewrite Hsp in Hfr.
split; [reflexivity|]. exists regs2, mem2, md2.
split; [unfold cfg_at, raZ; rewrite Hra; unfold w64; rewrite Z_to_bv_bv_unsigned; reflexivity|].
(* the memory that is the call's outside G and the caller's on G *)
set (memM := fun x : word => if inGb G (bv_unsigned x) then memT x else mem2 x).
assert (MG : forall x, inGb G (bv_unsigned x) = false -> memM x = mem2 x) by (intros x Hx; unfold memM; rewrite Hx; reflexivity).
assert (MTg : forall x, inGb G (bv_unsigned x) = true -> memM x = memT x) by (intros x Hx; unfold memM; rewrite Hx; reflexivity).
assert (GLO : forall a, inG G a -> 0 <= a < kLowMemEnd) by (intros a Ha; exact (inG_low SEGS B Hsegs G a HG Ha)).
assert (GB : forall a, 0 <= a < 2 ^ 64 -> inGb G (bv_unsigned (Z_to_bv 64 a)) = inGb G a)
by (intros a Ha; rewrite unsigned_lit_small by lia; reflexivity).
assert (AVT : forall a, 0 <= a < 2 ^ 64 -> inG G a -> aview SEGS (w_H W) memM a = aview SEGS (w_H W) memT a).
{ intros a Ha HGa. apply aview_eq_of. unfold mrestrict. rewrite MTg; [reflexivity|]. rewrite GB by exact Ha. apply inGb_spec. exact HGa. }
assert (AV2 : forall a, 0 <= a < 2 ^ 64 -> ~ inG G a -> aview SEGS (w_H W) memM a = aview SEGS (w_H W) mem2 a).
{ intros a Ha HGa. apply aview_eq_of. unfold mrestrict. rewrite MG; [reflexivity|]. rewrite GB by exact Ha. apply inGb_false. exact HGa. }
(* the scratch lies in the stack, far above every global *)
assert (SCG : forall a, inG G a -> ~ (sp0 + o - stk <= a < sp0 + o)) by (intros a Ha Hs; pose proof (GLO a Ha); unfold kLowMemEnd in *; lia).
assert (HARM : AR SEGS B lyc Sc W memM md2).
{ eapply (al_frame _ _ LAWS); [exact HAR2 | | | reflexivity | reflexivity | reflexivity |].
  - intros a Ha Ho. apply AV2; [exact Ha|]. intros HGa. destruct (HG a HGa) as [Hi Hno].
    apply Hno. exact (proj1 (al_owned_image _ _ LAWS _ _ _ _ _ a HAR2 Hi) Ho).
  - intros a Hv. rewrite aview_wrap64 in Hv |- *.
    pose proof (Z.mod_pos_bound a (2 ^ 64) ltac:(lia)) as Ra. set (a' := a mod 2 ^ 64) in *.
    destruct (inGb G a') eqn:Hg.
    + apply inGb_spec in Hg. rewrite (AVT a' Ra Hg). destruct (HWd a') as [HW | HW].
      * destruct (HWg a' HW Hg) as [Hh [b Hb]]. unfold aview, mbyte, mrestrict. rewrite Hh, Hb. discriminate.
      * rewrite <- (Hfr a' Ra HW (SCG a' Hg)). exact Hv.
    + rewrite (AV2 a' Ra ltac:(apply inGb_false; exact Hg)). exact Hv.
  - intros a _ Hh. unfold memM. destruct (inGb G (bv_unsigned (w64 a))) eqn:Hg; [|reflexivity].
    exfalso. apply inGb_spec in Hg. pose proof (proj1 (HG _ Hg)) as Hi.
    rewrite (hidden_not_img SEGS W _ Hi) in Hh. discriminate. }
(* (i) the writes outside G, by the donor's ajournal_after_write *)
assert (HJM : ajournal SEGS B (STK + XO) (sp0 + XO) FP ly S W0 memS md own lyc Sc W memM md2 k).
{ eapply (ajournal_after_write SEGS B LAWS Hsegs (STK + XO) (sp0 + XO) FP ly S W0 memS md own lyc Sc W memT mdc k memM md2
    (fun a => (Wr a /\ ~ inG G a) \/ (sp0 + o - stk <= a < sp0 + o)) Sc own HJi).
  - intros a Ha Hn. destruct (inGb G a) eqn:Hg.
    + apply inGb_spec in Hg. exact (AVT a Ha Hg).
    + assert (HnG : ~ inG G a) by (apply inGb_false; exact Hg). rewrite (AV2 a Ha HnG).
      apply Hfr; [exact Ha | | intros Hs; apply Hn; right; exact Hs].
      intros HW. apply Hn. left. split; [exact HW | exact HnG].
  - intros a [Hh [b Hb]]. split; [exact Hh|]. unfold memM. destruct (inGb G (bv_unsigned (Z_to_bv 64 a))).
    + exists b. exact Hb.
    + exact (proj2 (Hgr a (conj Hh (ex_intro _ b Hb)))).
  - exact Hsame.
  - intros a [[HW HnG] | Hs]; left.
    + destruct (HWa a HW HnG) as [[Hs | Hrest] _]; [left; lia | right; exact Hrest].
    + left. lia.
  - exact HARM.
  - reflexivity.
  - reflexivity.
  - lia.
  - exact Hfrs.
  - exact HQT. }
(* (ii) the writes to G, by W_journal.v's ajournal_rebase, and (iii) the repack *)
assert (HJ2 : ajournal SEGS B (STK + XO) (sp0 + XO) FP ly S W0 (gover G memS mem2) md own lyc Sc W mem2 md2 k).
{ apply (ajournal_rebase SEGS B LAWS Hsegs G _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ mem2 HG HJM).
  - intros x Hx. symmetry. exact (MG x Hx).
  - intros x Hx. unfold mrestrict in Hx |- *. destruct (w_H W x) eqn:Hh; [exact Hx|].
    destruct (inGb G (bv_unsigned x)) eqn:Hg; [|rewrite (MG x Hg) in Hx; exact Hx].
    rewrite (MTg x Hg) in Hx. destruct (memT x) as [b|] eqn:Eb; [|exfalso; exact (Hx eq_refl)].
    assert (Hp : apresent (w_H W) memT (bv_unsigned x)) by (split; rewrite Z_to_bv_bv_unsigned; [exact Hh | exists b; exact Eb]).
    destruct (Hgr _ Hp) as [_ [b2 Hb2]]. rewrite Z_to_bv_bv_unsigned in Hb2. rewrite Hb2. discriminate. }
split.
{ apply (ajournal_gx_pack SEGS B G XO OUT STK sp0 FP ly S W0 mem md own lyc Sc W mem2 md2 k (gover G memS mem2) HSTK HXO HJ2).
  - intros x Hx. unfold mrestrict, gover in *. rewrite Hx. exact (Hag x Hx).
  - intros a Ha Hno. rewrite <- (Hout a Ha Hno). apply Hfr; [lia | | lia].
    intros HW. destruct (inGb G a) eqn:Hg.
    + apply inGb_spec in Hg. pose proof (GLO a Hg). unfold kLowMemEnd in *. lia.
    + destruct (HWa a HW ltac:(apply inGb_false; exact Hg)) as [_ Hn]. exact (Hn Ha). }
split; [exact Hsame|].
split; [exact HP2|]. split; [exact HPr|]. split; [exact Hfr | exact Hgr].
Qed.

(* ---- the bcmp calls 0x80d8c, 0x80da8, 0x80e08: the wrapper's contract (ABCMP) inside the harness's journal ---- *)
Lemma kr_bcmp : forall cx fp k ly3 S3 W3 (regs : bvmap 5 word) mem md x y n xb xm yb ym raw
  (POST : world SEGS -> config -> Prop),
  pe_base SK B MT KS cx ->
  ajournal_gx SEGS B pe_G 0 [] LLVMF_STK (spZ (c_regs cx)) [sink_token] (c_ly cx) (c_S cx) (c_W cx)
    (c_mem cx) (c_md cx) [(PE_CID, fp)] ly3 S3 W3 mem md k ->
  getr regs 2 = w64 (c_sp1 cx) -> getr regs 3 = getr (c_regs cx) 3 -> getr regs 4 = getr (c_regs cx) 4 ->
  getr regs 1 = raw -> YK0s.ret_ok raw ->
  getr regs 10 = w64 x -> getr regs 11 = w64 y -> getr regs 12 = w64 n -> 0 <= n < 2 ^ 32 ->
  In (xb, xm) (ablocks B ly3 S3) -> xb <= x -> x + n <= xb + req_size xm ->
  In (yb, ym) (ablocks B ly3 S3) -> yb <= y -> y + n <= yb + req_size ym ->
  (forall i, 0 <= i < n -> aview SEGS (w_H W3) mem (x + i) = aview SEGS (w_H W3) mem (y + i)) ->
  (forall regs2 mem2 md2,
     ajournal_gx SEGS B pe_G 0 [] LLVMF_STK (spZ (c_regs cx)) [sink_token] (c_ly cx) (c_S cx) (c_W cx)
       (c_mem cx) (c_md cx) [(PE_CID, fp)] ly3 S3 W3 mem2 md2 k ->
     aregs_preserved regs regs2 -> getr regs2 10 = w64 0 -> m_fds md2 = m_fds md -> m_fs md2 = m_fs md ->
     (forall a, 0 <= a < 2 ^ 64 -> ~ (c_sp1 cx - 8192 <= a < c_sp1 cx) ->
        aview SEGS (w_H W3) mem2 a = aview SEGS (w_H W3) mem a) ->
     SRr SEGS W3 (mkCfg (mkst regs2 raw mem2 (seg_rom SEGS)) md2) POST) ->
  SRr SEGS W3 (mkCfg (mkst regs (Z_to_bv 64 (SIGMA PS___interceptor_trampoline_bcmp)) mem (seg_rom SEGS)) md) POST.
Proof.
  intros cx fp k ly3 S3 W3 regs mem md x y n xb xm yb ym raw POST HB HJ R2 R3 R4 R1 Hraw R10 R11 R12 Hn
    Hxin Hx0 Hx1 Hyin Hy0 Hy1 HEQ K.
  pose proof (h_sp SK B MT KS cx HB) as (Hsp16 & Hsp_lo & Hsp_hi & Hsp1 & Hsp1_32).
  pose proof HB as ((_ & _ & _ & Hgp0 & Htp0 & _) & _).
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  pose proof HJ as (_ & _ & (memS & HJi & _) & _). rewrite !Z.add_0_r in HJi. pose proof HJi as (HAR & _).
  destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR Hxin) as (_ & Hxb4096 & Hxceil & Hxapp & Hxpm & _ & Hxm).
  destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR Hyin) as (_ & Hyb4096 & Hyceil & Hyapp & Hypm & _ & Hym).
  pose proof (req_size_pos xm ltac:(lia)) as [_ Hxr]. pose proof (req_size_pos ym ltac:(lia)) as [_ Hyr].
  assert (Esp : spZ regs = c_sp1 cx) by (unfold spZ; rewrite R2; apply h_w64_unsigned; lia).
  assert (HXS : forall a, x <= a < x + n -> ~ (c_sp1 cx - 8192 <= a < c_sp1 cx)) by (intros a Ha; lia).
  assert (HYS : forall a, y <= a < y + n -> ~ (c_sp1 cx - 8192 <= a < c_sp1 cx)) by (intros a Ha; lia).
  eapply SRr_bind.
  { apply (kr_gx_entry pe_G 0 [] (2 * ESTACK) (SIGMA PS___interceptor_trampoline_bcmp) (fun _ => False)
      (fun regs2 _ => getr regs2 10 = w64 0) W3 regs mem LLVMF_STK (spZ (c_regs cx)) [sink_token] (c_ly cx) (c_S cx)
      (c_W cx) (c_mem cx) (c_md cx) [(PE_CID, fp)] ly3 S3 md k (c_sp1 cx - spZ (c_regs cx)) raw HGX ltac:(reflexivity) HJ).
    - rewrite Esp. lia.
    - destruct (h_mod32_8 _ Hsp1_32) as [H16 _]. rewrite Zminus_mod, H16, Hsp16. reflexivity.
    - lia.
    - unfold ESTACK. lia.
    - unfold ESTACK, LLVMF_STK. lia.
    - rewrite R3. exact Hgp0.
    - rewrite R4. exact Htp0.
    - exact R1.
    - exact Hraw.
    - intros a. right. intros [].
    - intros a [].
    - intros a [].
    - intros HPRE (Hslo & Hpres).
      eapply SRr_mono.
      { apply (ABCMP ly3 S3 W3 regs mem md x y n HPRE).
        - exact Hslo.
        - exact Hpres.
        - exact R10.
        - exact R11.
        - exact R12.
        - exact Hn.
        - lia.
        - lia.
        - lia.
        - lia.
        - intros a Ha. split; [|rewrite Esp; unfold ESTACK; lia].
          destruct (h_apresent_mbyte (w_H W3) mem a (proj1 (Hxpm a ltac:(lia)))) as (bv & Hbv).
          unfold aview. rewrite Hbv. discriminate.
        - intros a Ha. split; [|rewrite Esp; unfold ESTACK; lia].
          destruct (h_apresent_mbyte (w_H W3) mem a (proj1 (Hypm a ltac:(lia)))) as (bv & Hbv).
          unfold aview. rewrite Hbv. discriminate.
        - intros a Ha. rewrite Esp. unfold ESTACK. lia.
        - intros a Ha. rewrite Esp. unfold ESTACK. lia.
        - unfold amem_range. unfold in_app, kLowShadowBeg, kHighMemBeg in Hxapp. lia.
        - unfold amem_range. unfold in_app, kLowShadowBeg, kHighMemBeg in Hyapp. lia.
        - change (aview SEGS (w_H W3) mem) with (rd_of SEGS (mrestrict (w_H W3) mem)).
          replace SHADOW_OFF with (U (Eimg (Ereg regs [])) (SLit SHADOW_OFF)) by (rewrite U_lit; [reflexivity | unfold SHADOW_OFF; lia]).
          apply (obl_of_block SEGS B LAWS ly3 S3 W3 mem md _ _ x n xb xm HAR Hxin); [rewrite U_lit; [reflexivity | unfold SHADOW_OFF; lia] | lia | lia].
        - intros Hn0. apply (shadow_hull_vis_of_block SEGS B LAWS ly3 S3 W3 mem md xb xm x n HAR Hxin); lia.
        - change (aview SEGS (w_H W3) mem) with (rd_of SEGS (mrestrict (w_H W3) mem)).
          replace SHADOW_OFF with (U (Eimg (Ereg regs [])) (SLit SHADOW_OFF)) by (rewrite U_lit; [reflexivity | unfold SHADOW_OFF; lia]).
          apply (obl_of_block SEGS B LAWS ly3 S3 W3 mem md _ _ y n yb ym HAR Hyin); [rewrite U_lit; [reflexivity | unfold SHADOW_OFF; lia] | lia | lia].
        - intros Hn0. apply (shadow_hull_vis_of_block SEGS B LAWS ly3 S3 W3 mem md yb ym y n HAR Hyin); lia. }
      cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & v & -> & HAR2 & HP & Hsame & Hres & Hcmp & Hfr & Hpres2).
      split; [reflexivity|]. exists regs2, mem2, md2.
      split; [reflexivity|]. split; [exact HAR2|]. split; [exact HP|]. split; [exact Hsame|].
      split; [rewrite Hres; apply (proj2 Hcmp); exact HEQ|].
      split; [intros a Ha _ Hw; apply Hfr; [exact Ha | exact Hw]|].
      exact Hpres2. }
  cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & Hsame & HP & HPr & Hfr & Hpres2).
  pose proof (wvb_fds_fs (m_vm_lazy md) (m_vm_materialized md2) md) as (Ef & Es). rewrite <- Hsame in Ef, Es.
  apply (K regs2 mem2 md2 HJ2 HP HPr Ef Es).
  intros a Ha Hw. apply Hfr; [exact Ha | intros [] |]. unfold ESTACK. lia.
Qed.

(* lia over one to three separation facts, kept folded until used (as PcapHarnessA.v's dlia1 .. dlia3, which that file
   does not export). *)
Ltac zuf H := unfold zdisjoint, in_app, off_img, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, YImgTop.IMG_LO, YImgTop.IMG_TOP in H;
  cbn [fst snd] in H.
Ltac dlia1 H := let X := fresh "X" in pose proof H as X; zuf X; lia.
Ltac dlia2 H1 H2 := let X := fresh "X" in pose proof H1 as X; zuf X; dlia1 H2.
Ltac dlia3 H1 H2 H3 := let X := fresh "X" in pose proof H1 as X; zuf X; dlia2 H2 H3.
Ltac acs := unfold acallee_saved; first [left; reflexivity | right; left; reflexivity | right; right; left; reflexivity
  | right; right; right; left; reflexivity | right; right; right; right; left; reflexivity
  | right; right; right; right; right; split; vm_compute; discriminate].
(* ---- the loop's pcap_source_next (0x80fa0) and the return to PP_KL2 (0x80fa4) ---- *)
(* The registers the record checks keep up to the call: sp, gp, tp, s0, s1, s3, s5, s6, s7, s9, s11. *)
Definition kr_keepN : list (bv 5) := [2%bv; 3%bv; 4%bv; 8%bv; 9%bv; 19%bv; 21%bv; 22%bv; 23%bv; 25%bv; 27%bv].

Lemma kr_pos_fit : forall cx Q, p_kind cx Q = PSN.KFit -> p_pos cx Q = Q + 16 + kr_incl cx Q.
Proof. intros cx Q HK. unfold p_pos, PSN.pos_of. unfold p_kind in HK. rewrite HK. reflexivity. Qed.

Lemma kr_next : forall POST n, at_cut (GI_KL2 B MT KS) POST n ->
  forall cx fp k acc ly3 S3 W3 ms3 md3 b h buf i p (regs : bvmap 5 word) mem mdc,
  kr_ctx cx fp k acc ly3 S3 W3 ms3 md3 b h buf i p ->
  (hw_meas cx ms3 <= S n)%nat ->
  ajournal_gx SEGS B pe_G 0 [] LLVMF_STK (spZ (c_regs cx)) [sink_token] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx)
    (c_md cx) [(PE_CID, fp)] ly3 S3 W3 mem mdc k ->
  m_fds mdc = m_fds md3 -> m_fs mdc = m_fs md3 ->
  getr regs 1 = Z_to_bv 64 (BASE + PP_KL2) ->
  (forall r, In r kr_keepN -> getr regs r = getr (ms_regs ms3) r) ->
  getr regs 10 = w64 (pPS cx fp) -> getr regs 11 = w64 buf -> getr regs 12 = w64 (p_cap cx) ->
  getr regs 13 = w64 (pTS cx fp) ->
  getr regs 18 = w64 (p_q cx p + 16 + kr_incl cx (p_q cx p)) -> getr regs 26 = w64 (p_first cx) ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (c_sp1 cx - 8192 <= a < c_sp1 cx) -> ~ (pTS cx fp <= a < pTS cx fp + 8) ->
     aview SEGS (w_H W3) mem a = aview SEGS (w_H W3) (ms_mem ms3) a) ->
  val_mem SEGS (rdW W3 mem) (pTS cx fp) 8 18446744073709551615 ->
  SRr SEGS W3 (mkCfg (mkst regs (Z_to_bv 64 (BASE + AF_pcap_source_next)) mem (seg_rom SEGS)) mdc) (POST cx).
Proof.
  intros POST n HKL2 cx fp k acc ly3 S3 W3 ms3 md3 b h buf i p regs mem mdc Hctx Hmeas HJc Hfdsc Hfsc Q1 KN
    Q10 Q11 Q12 Q13 Q18 Q26 KR TSm.
  destruct Hctx as (HB & HJ3 & HFR & HMO & HRB).
  destruct HRB as (HCUT & Hpad & Hn26 & Hgood & Hi0 & Hip & HK & Hpe & R6 & R11 & R12 & R13 & R14 & R18 & R19 & R20
    & R21 & R22 & R23 & R24 & R25 & R26 & Hls & Hfirst & HGL & Hrd).
  destruct HCUT as (HBODY & Hk & Hacc & HPERM & Hfds & Hfs).
  pose proof HBODY as (Hpc & Hresv & Hsvc & Hrom & Hfr & Hfcsr & (G2 & G8 & G9 & G27 & G3 & G4) & HSAVED & HHDR & HSH &
                       Hlen & HIN).
  set (Q := p_q cx p) in *.
  pose proof (h_sp SK B MT KS cx HB) as (Hsp16 & Hsp_lo & Hsp_hi & Hsp1 & Hsp1_32).
  destruct (h_base SK B MT KS cx HB) as (HROD & HMETA & HG & HGR).
  destruct HJ3 as (_ & _ & (memS & HJ & HAG) & _). rewrite !Z.add_0_r in HJ.
  pose proof (h_frame SK B MT KS LAWS cx fp memS ly3 S3 W3 (ms_mem ms3) md3 k HB HJ HFR)
    as (EF & EFL & HF4096 & HFceil & HF64 & HFapp & HFimg & ESH & HFpres & HSHpres).
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  pose proof HJ as (HAR3 & _).
  pose proof (p_sizes cx) as (HnF & Hcap & Hbn).
  pose proof (h_blocks3 B LAWS ly3 S3 W3 (ms_mem ms3) md3 _ _ _ _ HAR3 HPERM)
    as (Hb_in & Hh_in & Hbuf_in & Hb_fr & Hh_fr & Hbuf_fr & Dbh & Dbbuf & Dhbuf).
  cbn [fst snd] in Dbh, Dbbuf, Dhbuf.
  destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR3 Hb_in) as (_ & Hb4096 & Hbceil & Hbapp & _ & _ & _).
  destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR3 Hh_in) as (_ & Hh4096 & Hhceil & Hhapp & _ & _ & _).
  destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR3 Hbuf_in) as (Hbuf16 & Hbuf4096 & Hbufceil & Hbufapp & _ & _ & _).
  pose proof (req_size_pos (p_bn cx) ltac:(lia)) as [_ Hreqbn].
  pose proof (req_size_pos (p_nF cx) ltac:(lia)) as [_ Hreqb].
  change (req_size SRC_FILE_BLOCK) with 1304 in Hhceil, Dbh, Dhbuf.
  assert (Hfin : In (PE_CID, fp) (frames S3)) by (rewrite HFR; left; reflexivity).
  pose proof (sep_block_frame SEGS B LAWS _ _ _ _ _ _ _ _ _ HAR3 Hbuf_in Hfin) as Dbuf.
  pose proof (sep_block_frame SEGS B LAWS _ _ _ _ _ _ _ _ _ HAR3 Hh_in Hfin) as Dh.
  pose proof (sep_block_frame SEGS B LAWS _ _ _ _ _ _ _ _ _ HAR3 Hb_in Hfin) as Db.
  rewrite EF in Dbuf, Dh, Db. change (fs_frame_bytes PE_CID) with 128 in Dbuf, Dh, Db.
  change (req_size SRC_FILE_BLOCK) with 1304 in Dh, Hhapp.
  assert (HSHr : 0x7fff8000 + 512 <= pSH cx fp /\ pSH cx fp + 16 <= 0x7fff8000 + 2 ^ 44 /\ pSH cx fp mod 8 = 0).
  { destruct (h_div8_of_mul64 (pF cx fp) HF64) as [E8 E64]. rewrite ESH. unfold SHADOW_OFF.
    pose proof (Z.div_lt_upper_bound (pF cx fp + 128) 8 (2 ^ 44) ltac:(lia) ltac:(lia)).
    pose proof (Z.div_le_lower_bound (pF cx fp) 8 512 ltac:(lia) ltac:(lia)).
    replace ((pF cx fp + 128) / 8) with (pF cx fp / 8 + 16) in H
      by (rewrite <- (Z.div_add (pF cx fp) 16 8) by lia; f_equal; lia).
    split; [lia|]. split; [lia|].
    rewrite E8. replace (2147450880 + 8 * (pF cx fp / 64)) with ((268431360 + pF cx fp / 64) * 8) by lia.
    apply Z_mod_mult. }
  (* the frame lies in application memory, its shadow in the shadow band *)
  assert (DFSH : pF cx fp + 128 <= pSH cx fp \/ pSH cx fp + 16 <= pF cx fp).
  { clear - HFapp HSHr C1 C3. unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in HFapp. lia. }
  destruct HJc as (_ & _ & (memS' & HJm & HAGm) & _). rewrite !Z.add_0_r in HJm.
  pose proof HJm as (HARm & _).
  assert (Q2 : getr regs 2 = w64 (c_sp1 cx)) by (rewrite (KN 2%bv ltac:(kr_in)); exact G2).
  assert (Q3 : getr regs 3 = getr (c_regs cx) 3) by (rewrite (KN 3%bv ltac:(kr_in)); exact G3).
  assert (Q4 : getr regs 4 = getr (c_regs cx) 4) by (rewrite (KN 4%bv ltac:(kr_in)); exact G4).
  assert (Q8 : getr regs 8 = w64 (spZ (c_regs cx))) by (rewrite (KN 8%bv ltac:(kr_in)); exact G8).
  assert (Q9 : getr regs 9 = w64 (c_sp1 cx)) by (rewrite (KN 9%bv ltac:(kr_in)); exact G9).
  assert (Q19 : getr regs 19 = w64 b) by (rewrite (KN 19%bv ltac:(kr_in)); exact R19).
  assert (Q21 : getr regs 21 = w64 (p_cap cx)) by (rewrite (KN 21%bv ltac:(kr_in)); exact R21).
  assert (Q22 : getr regs 22 = w64 buf) by (rewrite (KN 22%bv ltac:(kr_in)); exact R22).
  assert (Q23 : getr regs 23 = w64 0xff00) by (rewrite (KN 23%bv ltac:(kr_in)); exact R23).
  assert (Q25 : getr regs 25 = w64 (i + 1)) by (rewrite (KN 25%bv ltac:(kr_in)); exact R25).
  assert (Q27 : getr regs 27 = w64 SHADOW_OFF) by (rewrite (KN 27%bv ltac:(kr_in)); exact G27).
  assert (Esp : spZ regs = c_sp1 cx) by (unfold spZ; rewrite Q2; apply h_w64_unsigned; lia).
  assert (Es0 : s0Z regs = spZ (c_regs cx)) by (unfold s0Z; rewrite Q8; apply h_w64_unsigned; lia).
  unfold pTS, PO_TS in KR, TSm, Q13. unfold pPS, PO_PS in Q10.
  assert (MK : forall a, 0 <= a < 2 ^ 64 -> ~ (c_sp1 cx - 8192 <= a < c_sp1 cx) -> ~ (pF cx fp + 96 <= a < pF cx fp + 96 + 8) ->
     mbyte SEGS (rdW W3 mem) a = mbyte SEGS (rdW W3 (ms_mem ms3)) a)
    by (intros a Ha Hn1 Hn2; apply (mbyte_of_aview SEGS); exact (KR a Ha Hn1 Hn2)).
  (* the record buffer's bytes, as the next call's premise names them *)
  destruct (garr8_of_readable SEGS (rdW W3 mem) buf (Z.to_nat (p_bn cx))) as (bj & Hbjlen & Hbj).
  { intros a Ha. destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HARm Hbuf_in) as (_ & _ & _ & _ & Hpm & _).
    apply h_apresent_mbyte. apply (proj1 (Hpm a ltac:(lia))). }
  pose proof HB as ((_ & _ & Hra4 & Hgp0 & Htp0 & _) & _ & _ & _ & HINP & _).
  destruct Hrd as (HSRC & (HPSO1 & HPSO2) & HFIT). specialize (HFIT HK) as (Vo & Vt & Vv & Vts & Vbuf).
  unfold pval, pPS, PO_PS, pTS, PO_TS in HPSO1, HPSO2, Vo, Vt, Vv, Vts.
  unfold p_pspad, pPS, PO_PS in Hpad.
  assert (PSm : forall o n v, 0 <= o -> o + Z.of_nat n <= 24 ->
     val_mem SEGS (rdW W3 (ms_mem ms3)) (pF cx fp + 32 + o) n v -> val_mem SEGS (rdW W3 mem) (pF cx fp + 32 + o) n v).
  { intros o n0 v Ho1 Ho2 Hv. eapply vm_frame; [|exact Hv]. intros x Hx. apply MK; lia. }
  assert (HLC : Z.of_nat (length (p_C cx)) = p_nF cx) by (unfold p_C, p_nF; rewrite length_map; reflexivity).
  assert (HL24 : 24 <= p_nF cx).
  { unfold p_good, PST.pcap_good in Hgood. apply andb_prop in Hgood as [H24 _]. apply Z.leb_le in H24. exact H24. }
  destruct (PW.kind_fit (p_sw cx) (p_F cx) (p_cap cx) Q HK) as (_ & _ & HQi0 & HQfit & HQincl).
  change (PSN.flen (p_F cx)) with (p_nF cx) in HQfit.
  change (PSN.incl (p_sw cx) (p_F cx) Q) with (kr_incl cx Q) in HQfit, HQi0, HQincl.
  assert (HQ0 : 24 <= Q) by (pose proof (PW.psn_q_ge (p_sw cx) (p_F cx) (p_cap cx) p); unfold Q, p_q; lia).
  pose proof (kr_pos_fit cx Q HK) as HPOS.
  set (P := p_pos cx Q) in *.
  set (lol := PSN.orig (p_sw cx) (p_F cx) Q).
  set (lvt := if PSN.tagged (p_sw cx) (p_F cx) Q then 1 else 0).
  set (lvid := if PSN.tagged (p_sw cx) (p_F cx) Q then PSN.rec_vid (p_F cx) Q else 0).
  assert (Hlol : 0 <= lol < 2 ^ 32) by (unfold lol, PSN.orig; apply PW.pw_hw_range).
  assert (Hlvt : 0 <= lvt < 2 ^ 32) by (unfold lvt; destruct (PSN.tagged _ _ _); lia).
  assert (Hlvid : 0 <= lvid < 2 ^ 16) by (unfold lvid; destruct (PSN.tagged _ _ _); [pose proof (kr_rec_vid_range (p_F cx) Q); lia | lia]).
  eapply SRr_bind.
  { eapply (NEXT LLVMF_STK (spZ (c_regs cx)) [sink_token] (c_ly cx) (c_S cx) (c_W cx) memS' (c_md cx)
      [(PE_CID, fp)] ly3 S3 W3 mem mdc k regs
      (pF cx fp + 32) buf (p_cap cx) (pF cx fp + 96) h b P (p_swz cx) lol lvt lvid 18446744073709551615 (c_M cx)
      PE_CID fp (p_C cx) bj [165; 165] (pch cx)).
    - exact HJm.
    - eapply (arodata_ok_journalP (RO := RO) SEGS pa_relro_lo pa_relro_hi pa_relro_img);
        [exact HJm | exact (h_arodata_S SK B MT KS cx memS' HB HAGm)].
    - rewrite Q1. apply ret_ok_codeptr_v; [unfold PP_KL2; lia | reflexivity].
    - unfold raZ. rewrite Q1, unsigned_lit_small; pose proof pa_base_lo; pose proof pa_B_ok; unfold PP_KL2; lia.
    - rewrite Q3. exact Hgp0.
    - rewrite Q4. exact Htp0.
    - exact Q10.
    - exact Q11.
    - exact Q12.
    - exact Q13.
    - rewrite Esp. exact (proj1 (h_mod32_8 _ Hsp1_32)).
    - rewrite Esp. unfold LLVMF_STK, NX_STK, AFREAD_STK. lia.
    - rewrite Esp. lia.
    - rewrite Esp, Es0. apply (h_achain SK B MT KS cx memS' ly3 S3 W3 mem _ [(PE_CID, fp)] k (c_sp1 cx) HB HJm HAGm).
      + apply (h_rdword_keep (w_H W3) (w_H W3) (ms_mem ms3) mem); [|exact (proj1 HSAVED)].
        intros i0 Hi. apply KR; lia.
      + pose proof (proj2 HSAVED 0 ltac:(lia)) as HS0. rewrite Z.mul_0_r, Z.sub_0_r in HS0.
        apply (h_rdword_keep (w_H W3) (w_H W3) (ms_mem ms3) mem); [|exact HS0].
        intros i0 Hi. apply KR; lia.
      + lia.
    - rewrite HFR. vm_compute. reflexivity.
    - unfold PS_F_OFF. rewrite Z.add_0_r. rewrite <- (Z.add_0_r (pF cx fp + 32)). apply (PSm 0 8%nat); [lia | cbn; lia |].
      rewrite Z.add_0_r. exact HPSO1.
    - lia.
    - apply h_mod64_add; [exact HF64 | reflexivity].
    - lia.
    - unfold PS_LEN. lia.
    - unfold amem_range, PS_LEN. dlia1 HFapp.
    - left. reflexivity.
    - rewrite EF. lia.
    - rewrite EF. change (fs_frame_bytes PE_CID) with 128. unfold PS_LEN. lia.
    - unfold PS_LEN. apply (h_ra_frame (w_H W3) mem (pF cx fp) (pSH cx fp) 32 24 ESH HF64); [lia | reflexivity | lia |].
      intros j Hj. change ((24 + 7) / 8) with 3 in Hj. change (32 / 8) with 4.
      replace (pSH cx fp + 4 + j) with (pSH cx fp + Z.of_nat (Z.to_nat (4 + j))) by lia.
      assert (HSa : 0 <= pSH cx fp + Z.of_nat (Z.to_nat (4 + j)) < 2 ^ 64) by lia.
      rewrite KR by lia. rewrite HSH by (change (length PSH_ts) with 16%nat; lia).
      assert (Hj3 : j = 0 \/ j = 1 \/ j = 2) by lia.
      destruct Hj3 as [-> | [-> | ->]]; reflexivity.
    - intros _. unfold nx_ps_at, PS_F_OFF, PS_SW_OFF, PS_OL_OFF, PS_VT_OFF, PS_VID_OFF.
      split; [apply (PSm 0 8%nat); [lia | cbn; lia | rewrite Z.add_0_r; exact HPSO1]|].
      split; [apply (PSm 8 4%nat); [lia | cbn; lia | exact HPSO2]|].
      split; [apply (PSm 12 4%nat); [lia | cbn; lia | exact Vo]|].
      split; [apply (PSm 16 4%nat); [lia | cbn; lia | exact Vt]|].
      split; [apply (PSm 20 2%nat); [lia | cbn; lia | exact Vv]|].
      split; [|reflexivity].
      apply (garr8_frame SEGS (rdW W3 (ms_mem ms3)) (rdW W3 mem) _ _ Hpad).
      intros x Hx. cbn [length] in Hx. apply MK; lia.
    - intros _. unfold p_swz, PST.pcap_sw. destruct (_ =? _); [right | left]; reflexivity.
    - intros _. lia.
    - intros _ a Ha. unfold PS_LEN in Ha. rewrite Esp. split; [|unfold NX_STK, AFREAD_STK; lia].
      right; right; right. exists PE_CID, fp. split; [left; reflexivity|]. left. unfold in_zr. cbn [frame_rng fst snd].
      rewrite EF. change (fs_frame_bytes PE_CID) with 128. lia.
    - intros _. unfold nx_bufn, NX_CAP_MAX. fold (p_bn cx). rewrite Esp.
      split; [exact Hbuf_in|]. split; [lia|]. split; [lia|]. split; [exact Hbj|]. split; [lia|]. split; [lia|].
      split; [|unfold PS_LEN; dlia1 Dbuf].
      intros a Ha. split; [|unfold NX_STK, AFREAD_STK; lia].
      right; right; left. exists buf, (p_bn cx). split; [exact Hbuf_in|]. split; [exact Hbuf_fr | lia].
    - intros _ _. rewrite Esp. split; [exact TSm|]. split; [apply h_mod64_add; [exact HF64 | reflexivity]|].
      split; [lia|]. split; [lia|]. split; [unfold amem_range; dlia1 HFapp|].
      split; [exists PE_CID, fp; split; [left; reflexivity|]; rewrite EF; change (fs_frame_bytes PE_CID) with 128; lia|].
      split.
      { intros a Ha. split; [|unfold NX_STK, AFREAD_STK; lia].
        right; right; right. exists PE_CID, fp. split; [left; reflexivity|]. left. unfold in_zr. cbn [frame_rng fst snd].
        rewrite EF. change (fs_frame_bytes PE_CID) with 128. lia. }
      split.
      { apply (h_ra_frame (w_H W3) mem (pF cx fp) (pSH cx fp) 96 8 ESH HF64); [lia | reflexivity | lia |].
        intros j Hj. change ((8 + 7) / 8) with 1 in Hj. change (96 / 8) with 12.
        assert (j = 0) as -> by lia. rewrite Z.add_0_r.
        change (pSH cx fp + 12) with (pSH cx fp + Z.of_nat 12).
        rewrite KR by lia. rewrite HSH by (change (length PSH_ts) with 16%nat; lia). reflexivity. }
      unfold nx_bufn, PS_LEN. fold (p_bn cx). split; dlia1 Dbuf.
    - intros _. rewrite HLC. unfold nx_bufn, PS_LEN. fold (p_bn cx).
      split; [exact Hh_in|]. split; [exact Hb_in|].
      split.
      { apply (asource_at_frame KS (rdW W3 (ms_mem ms3)) (rdW W3 mem) h b (p_C cx) P); [|exact HSRC].
        intros a Ha. rewrite HLC in Ha. unfold SRC_FILE_BLOCK in Ha.
        destruct Ha as [Ha | [Ha | Ha]].
        - apply MK; dlia2 Dh Hhapp.
        - apply MK; dlia2 Db Hbapp.
        - destruct (asil_env _ _ _ _ ASIL a Ha) as (Hi & _).
          pose proof (pa_img_range a Hi) as Hr1. pose proof (pa_segs_low a Hi) as Hr2.
          unfold pcap_img_end, YImgTop.IMG_TOP, kLowMemEnd in Hr1, Hr2. apply MK; dlia1 HFimg. }
      unfold SRC_FILE_BLOCK. split; [lia|]. split; [lia|].
      split; [dlia1 Dhbuf|]. split; [dlia1 Dbbuf|]. split; [dlia1 Dh|]. split; [dlia1 Db|].
      split; [intros _; split; [dlia1 Dh | dlia1 Db]|].
      intros x Hx. destruct (in_asource_fp h x Hx) as [Hx1 | Hx0].
      + right. exists h, SRC_FILE_BLOCK. split; [exact Hh_in|]. split; [exact Hh_fr|].
        change (req_size SRC_FILE_BLOCK) with 1304. unfold SRC_FILE_BLOCK in Hx1. lia.
      + left. exists YI16.sink_token. split; [left; reflexivity | unfold YI16.sink_token; cbn [fst snd]; lia].
    - intros _. exact (h_meta_gx SK B MT KS ASIL cx memS' [(PE_CID, fp)] ly3 S3 W3 mem _ k HB HJm HAGm). }
  (* ---- back from pcap_source_next, at 0x80fa4 ---- *)
  cbv beta. intros W2 c2 Hwle (ly2 & S2 & regs2 & mem2 & md2 & Ec & HJ2 & HPR & HBL & HFR2 & HMO2 & Hfds2 & Hfs2 & HFIN).
  subst c2.
  destruct HFIN as [(Hh0 & _) | (_ & Er & HK2 & HSRC2 & HPS2 & (bj' & HBJ2 & Hbjl' & Hpre) & HTS2)]; [lia|].
  destruct HK2 as (K1 & K2 & K3 & K4 & _ & _).
  rewrite Esp in K1.
  assert (NW : forall a, ~ ((pF cx fp + 32 <= a < pF cx fp + 56) \/ (buf <= a < buf + p_bn cx) \/
        (pF cx fp + 96 <= a < pF cx fp + 104) \/ (h <= a < h + 1304)) ->
      ~ nx_wrset (pF cx fp + 32) buf (p_cap cx) (pF cx fp + 96) h a).
  { intros a Hn Hc. apply Hn. unfold nx_wrset, nx_bufn, PS_LEN, SRC_FILE_BLOCK in Hc. fold (p_bn cx) in Hc. lia. }
  (* the stack from s1 up (the slots, the saved registers), as at 0x80c68 *)
  assert (KH : forall a, c_sp1 cx <= a < 2 ^ 64 -> aview SEGS (w_H W2) mem2 a = aview SEGS (w_H W3) (ms_mem ms3) a).
  { intros a Ha. rewrite K1; [apply KR; lia | lia | lia | apply NW; lia]. }
  (* the frame outside ps and ts, as at 0x80c68 *)
  assert (KF : forall a, (pF cx fp <= a < pF cx fp + 32) \/ (pF cx fp + 56 <= a < pF cx fp + 96) \/
      (pF cx fp + 104 <= a < pF cx fp + 128) -> aview SEGS (w_H W2) mem2 a = aview SEGS (w_H W3) (ms_mem ms3) a).
  { intros a Ha. rewrite (K4 PE_CID fp a Hfin).
    - apply KR; lia.
    - left. unfold in_zr. cbn [frame_rng fst snd]. rewrite EF. change (fs_frame_bytes PE_CID) with 128. lia.
    - apply NW; dlia2 Dbuf Dh. }
  (* the frame's shadow, as at 0x80c68 *)
  assert (KSH : forall i, (i < 16)%nat -> aview SEGS (w_H W2) mem2 (pSH cx fp + Z.of_nat i) = Some (nth i PSH_ts 0)).
  { intros i0 Hi. rewrite (K4 PE_CID fp (pSH cx fp + Z.of_nat i0) Hfin).
    - rewrite KR by lia. apply HSH. change (length PSH_ts) with 16%nat. exact Hi.
    - right. unfold in_zr. cbn [fst snd].
      replace (shadow_addr (frame_addr ly3 PE_CID fp)) with (pSH cx fp) by (rewrite EF, ESH; unfold shadow_addr; reflexivity).
      change (fs_frame_bytes PE_CID / 8) with 16. lia.
    - apply NW. dlia2 Hbufapp Hhapp. }
  (* the harness's globals, as at 0x80c68 *)
  assert (KG : forall a, inG pe_G a -> aview SEGS (w_H W2) mem2 a = aview SEGS (w_H W3) (ms_mem ms3) a).
  { intros a Hin. destruct (HG a Hin) as [Hi Hns]. destruct (HGR a Hin) as (_ & _ & Her & _).
    pose proof (pa_img_range a Hi) as Hr1. pose proof (pa_segs_low a Hi) as Hr2.
    unfold pcap_img_end, YImgTop.IMG_TOP, kLowMemEnd in Hr1, Hr2.
    rewrite (K3 a Hi Hns Her). apply KR; dlia1 HFimg. }
  destruct (h_nx_model cx P) as (Nq & Nlh & Nres & Npos & Nkind & NF).
  assert (HP1 : Q + 1 <= P) by (rewrite HPOS; lia).
  assert (HPF : P <= p_nF cx) by (rewrite HPOS; lia).
  apply (HKL2 cx fp (k + EV_NEXT) (acc + 0) ly2 S2 W2 (mkst regs2 (getr regs 1) mem2 (seg_rom SEGS)) md2 HB).
  { eapply ajournal_gx_pack; [unfold LLVMF_STK; lia | lia | | exact HAGm | intros a Ha _; lia].
    rewrite (Z.add_0_r LLVMF_STK), (Z.add_0_r (spZ (c_regs cx))). exact HJ2. }
  { rewrite HFR2. exact HFR. }
  { exact (mo_le_trans MT MTL _ _ _ _ _ HMO HMO2). }
  2:{ unfold hw_meas, hw_pos. cbn [ms_regs mkst]. rewrite (h_pres _ _ _ HPR) by acs. rewrite Q18.
      unfold hw_meas, hw_pos in Hmeas. rewrite R18 in Hmeas.
      rewrite h_w64_unsigned in Hmeas by lia. rewrite h_w64_unsigned by lia. lia. }
  exists b, h, buf, (i + 1), P.
  split.
  { unfold p_cut. split.
    2:{ split; [unfold EV_NEXT; lia|]. split; [lia|]. split; [rewrite HBL; exact HPERM|].
        split; [rewrite Hfds2, Hfdsc; exact Hfds | rewrite Hfs2, Hfsc; exact Hfs]. }
    unfold pe_body, pregs, psaved, pheader, pshadow.
    cbn [ms_mem ms_regs ms_pc_val ms_resv ms_svc_pending ms_rom ms_fregs ms_fcsr mkst].
    split; [rewrite Q1; reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
    split; [reflexivity|]. split; [reflexivity|].
    split.
    { rewrite !(h_pres _ _ _ HPR) by acs.
      split; [exact Q2|]. split; [exact Q8|]. split; [exact Q9|]. split; [exact Q27|]. split; [exact Q3 | exact Q4]. }
    split.
    { split.
      - apply (h_rdword_keep (w_H W3) (w_H W2) (ms_mem ms3) mem2); [intros i0 Hi; apply KH; lia | exact (proj1 HSAVED)].
      - intros j Hj. apply (h_rdword_keep (w_H W3) (w_H W2) (ms_mem ms3) mem2); [intros i0 Hi; apply KH; lia|].
        exact (proj2 HSAVED j Hj). }
    split.
    { destruct HHDR as (HH0 & HH8 & HH16 & HH120).
      split; [|split; [|split]].
      - apply (h_rdword_keep (w_H W3) (w_H W2) (ms_mem ms3) mem2); [intros i0 Hi; apply KF; lia | exact HH0].
      - apply (h_rdword_keep (w_H W3) (w_H W2) (ms_mem ms3) mem2); [intros i0 Hi; apply KF; lia | exact HH8].
      - apply (h_rdword_keep (w_H W3) (w_H W2) (ms_mem ms3) mem2); [intros i0 Hi; apply KF; lia | exact HH16].
      - apply (h_rdword_keep (w_H W3) (w_H W2) (ms_mem ms3) mem2); [intros i0 Hi; apply KF; unfold PE_FLAGPTR; lia | exact HH120]. }
    split; [intros i0 Hi; change (length PSH_ts) with 16%nat in Hi; exact (KSH i0 Hi)|].
    split; [reflexivity|].
    { apply (garr8_frame SEGS (rdW W3 (ms_mem ms3)) (rdW W2 mem2) _ _ HIN). intros a Ha. rewrite length_map in Ha.
      apply (mbyte_of_aview SEGS).
      destruct HINP as [(Hn0 & _) | (Hn & Hinc)]; [unfold c_n in Hn0; lia|].
      assert (Hin3 : In (c_p cx, c_n cx) (ablocks B ly3 S3))
        by (apply (Permutation_in _ (Permutation_sym HPERM)); apply in_or_app; left; exact Hinc).
      destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR3 Hin3) as (_ & Hp4096 & Hpceil & Hpapp & _).
      pose proof (req_size_pos (c_n cx) ltac:(lia)) as [_ Hreqp].
      pose proof (sep_block_frame SEGS B LAWS _ _ _ _ _ _ _ _ _ HAR3 Hin3 Hfin) as Dp.
      rewrite EF in Dp. change (fs_frame_bytes PE_CID) with 128 in Dp.
      assert (Dpbuf : zdisjoint (c_p cx, req_size (c_n cx)) (buf, req_size (p_bn cx))).
      { apply (sep_blocks SEGS B LAWS _ _ _ _ _ _ _ _ _ HAR3 Hin3 Hbuf_in). intros E'. apply Hbuf_fr. rewrite <- E'. exact Hinc. }
      assert (Dph : zdisjoint (c_p cx, req_size (c_n cx)) (h, req_size SRC_FILE_BLOCK)).
      { apply (sep_blocks SEGS B LAWS _ _ _ _ _ _ _ _ _ HAR3 Hin3 Hh_in). intros E'. apply Hh_fr. rewrite <- E'. exact Hinc. }
      change (req_size SRC_FILE_BLOCK) with 1304 in Dph.
      unfold c_n in *.
      replace a with (c_p cx + (a - c_p cx)) by lia.
      rewrite (K2 (c_p cx) _ (a - c_p cx) Hin3 ltac:(lia)); [apply KR; dlia2 Dp Hpapp|]. apply NW. dlia3 Dp Dpbuf Dph. } }
  split; [unfold p_pspad, pPS, PO_PS; cbn [ms_mem mkst]; exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 HPS2))))))|].
  split; [exact Hn26|]. split; [exact Hgood|].
  split; [lia|]. split; [lia|]. split; [exact HPF|].
  cbn [ms_mem ms_regs mkst].
  split; [rewrite Er, Nres; reflexivity|].
  split; [rewrite (h_pres _ _ _ HPR) by acs; rewrite Q18, HPOS; reflexivity|].
  split; [rewrite (h_pres _ _ _ HPR) by acs; exact Q19|].
  split; [rewrite (h_pres _ _ _ HPR) by acs; exact Q21|].
  split; [rewrite (h_pres _ _ _ HPR) by acs; exact Q22|].
  split; [rewrite (h_pres _ _ _ HPR) by acs; exact Q23|].
  split; [rewrite (h_pres _ _ _ HPR) by acs; exact Q25|].
  split; [rewrite (h_pres _ _ _ HPR) by acs; exact Q26|].
  split.
  { destruct Hls as (HSL & SVM & SB12 & SUS).
    unfold p_lslots, pslots, pslot, PS_PSP, PS_GLEN, PS_D, PS_SH, PS_F, PS_FK, PS_TSP, PS_VMASK, PS_BUF12, PS_USEC, pPS, PO_PS, PO_TS
      in HSL, SVM, SB12, SUS |- *.
    cbn [ms_mem mkst].
    destruct HSL as (S1 & S2' & S3' & S4' & S5' & S6' & S7').
    split; [split; [|split; [|split; [|split; [|split; [|split]]]]]|split; [|split]];
      apply (h_rdword_keep (w_H W3) (w_H W2) (ms_mem ms3) mem2);
      first [intros i0 Hi; apply KH; lia | eassumption]. }
  split.
  { unfold p_glob, pval. split.
    - eapply vm_frame; [|exact (proj1 HGL)]. intros x Hx. apply (mbyte_of_aview SEGS). apply KG.
      apply Exists_cons_tl. apply Exists_cons_hd. unfold in_zr. cbn [fst snd]. change (Z.of_nat 8) with 8 in Hx. lia.
    - eapply vm_frame; [|exact (proj2 HGL)]. intros x Hx. apply (mbyte_of_aview SEGS). apply KG.
      apply Exists_cons_hd. unfold in_zr. cbn [fst snd]. change (Z.of_nat 8) with 8 in Hx. lia. }
  { unfold p_reader, p_psopen, pval, pPS, pTS, PO_PS, PO_TS. cbv zeta. cbn [ms_mem mkst].
    rewrite Npos in HSRC2.
    destruct HPS2 as (P0 & P8 & P12 & P16 & P20 & _ & _).
    unfold PS_F_OFF, PS_SW_OFF, PS_OL_OFF, PS_VT_OFF, PS_VID_OFF in P0, P8, P12, P16, P20.
    rewrite Z.add_0_r in P0.
    split; [exact HSRC2|]. split; [split; [exact P0 | exact P8]|].
    intros HKf.
    assert (Hlh : PSN.psn_lh (p_sw cx) (p_F cx) (p_cap cx) P = Some (p_q cx P)) by (apply h_psn_lh_fit; [lia | exact HKf]).
    assert (Hfit : nx_fit (p_swz cx =? 1) (p_C cx) (p_cap cx) P = true) by (unfold nx_fit; rewrite Nkind, HKf; reflexivity).
    unfold nx_orig in P12. rewrite Nlh, Hlh, NF in P12.
    unfold nx_vtag in P16. rewrite Hfit, Nq, NF in P16.
    unfold nx_vid in P20. rewrite Hfit, Nq, NF in P20.
    specialize (HTS2 ltac:(lia)). unfold nx_tsv in HTS2. rewrite Hfit, Nq, NF in HTS2.
    specialize (Hpre Hfit).
    rewrite <- (firstn_skipn (length (nx_rec (p_swz cx =? 1) (p_C cx) (p_cap cx) P)) bj') in HBJ2.
    apply (garr8_app SEGS) in HBJ2. destruct HBJ2 as [HBJa _]. rewrite Hpre in HBJa. unfold nx_rec in HBJa.
    rewrite Nq, NF in HBJa.
    split; [exact P12|]. split; [exact P16|]. split; [exact P20|]. split; [exact HTS2 | exact HBJa]. }
Qed.

(* ---- the timestamp check and the call, 0x80e10 .. 0x80fa0 ---- *)
Definition PP_TS : Z := 0x6d8.

Lemma kb_addz_U : forall E s v k c, c = k * 2 ^ 32 -> U E s = v -> 0 <= v -> 0 <= k -> v + k < 2 ^ 32 ->
  U E (SAlu ALU_SRL (SAlu ALU_ADD (SAlu ALU_SLL s (SLit 32)) (SLit c)) (SLit 32)) = v + k.
Proof.
  intros E s v k c -> Hs Hv Hk Hvk. rewrite !U_SAlu, Hs, !U_SLit. cbn [zalu_raw].
  change (Z.land (zcanon 32) 63) with 32. rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia.
  rewrite (zcanon_id (v * 2 ^ 32)) by (unfold M64; lia). rewrite (zcanon_id (k * 2 ^ 32)) by (unfold M64; lia).
  replace (v * 2 ^ 32 + k * 2 ^ 32) with ((v + k) * 2 ^ 32) by lia.
  rewrite (zcanon_id ((v + k) * 2 ^ 32)) by (unfold M64; lia). rewrite Z.div_mul by lia. apply zcanon_id. unfold M64. lia.
Qed.

(* A register of a call's state (st_ok) as U of its symbolic value. *)
Ltac kregC HS r Q :=
  lazymatch type of HS with st_ok _ ?E ?ss (restrict ?H ?ms) =>
    pose proof (st_ok_restrict_reg SEGS H E ss ms r HS) as Q;
    let e := eval vm_compute in (sr_get (ss_regs ss) r) in change (sr_get (ss_regs ss) r) with e in Q;
    rewrite (denot_lit_U E e) in Q end.

(* The windows of the record seats: only ts (ps + 64 .. ps + 72, atom 32) is written. *)
Ltac kr_wints U32 := let bb := fresh "bb" in let wlo := fresh "wlo" in let whi := fresh "whi" in
  let a := fresh "a" in let Hin := fresh "Hin" in let Ha := fresh "Ha" in
  intros bb wlo whi a Hin Ha; vm_compute in Hin;
  repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; cbn [base_val] in Ha; rewrite ?U32 in Ha; lia |]);
  destruct Hin.

(* The awr obligation of a record seat with ts writable: ts lies in the call's own frame. *)
Ltac kr_awr_ts U32 EF cx fp :=
  apply awr_ok_x_of0;
  lazymatch goal with |- awr_ok ?E0 ?rs ?stk ?spx ?fpp ?b0 ?bc ?lyy ?own =>
    let rs' := eval vm_compute in rs in change (awr_ok E0 rs' stk spx fpp b0 bc lyy own) end;
  apply awr_ok_cons_ro; [cbn; lia|];
  apply awr_ok_cons_ro; [cbn; lia|];
  apply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ 32%nat (pF cx fp + 32)); [reflexivity | exact U32 | |];
  [ let a := fresh "a" in let Ha := fresh "Ha" in
    intros a Ha; cbn [YP09.r_wlo YP09.r_whi] in Ha; right; right; right; exists PE_CID, fp;
    split; [left; reflexivity|]; left; unfold in_zr; cbn [frame_rng fst snd]; rewrite EF;
    change (fs_frame_bytes PE_CID) with 128; lia
  | apply awr_ok_nil ].

Lemma kr_ts : forall POST n, at_cut (GI_KL2 B MT KS) POST n ->
  forall cx fp k acc ly3 S3 W3 ms3 md3 b h buf i p (ms : machine_state) md,
  kr_ctx cx fp k acc ly3 S3 W3 ms3 md3 b h buf i p ->
  (hw_meas cx ms3 <= S n)%nat ->
  kr_now cx fp k ly3 S3 W3 ms3 md3 (ms_regs ms) (ms_mem ms) md ->
  ms = mkst (ms_regs ms) (Z_to_bv 64 (BASE + PP_TS)) (ms_mem ms) (seg_rom SEGS) ->
  SRr SEGS W3 (mkCfg ms md) (POST cx).
Proof.
intros POST n HKL2 cx fp k acc ly3 S3 W3 ms3 md3 b h buf i p ms md Hctx Hmeas Hnow Hsh.
pose proof Hctx as (HB & HJ3 & HFR & HMO & HRB).
pose proof HRB as (HCUT & Hpad & Hn26 & Hgood & Hi0 & Hip & HK & Hpe & R6 & R11 & R12 & R13 & R14 & R18 & R19 & R20
  & R21 & R22 & R23 & R24 & R25 & R26 & Hls & Hfirst & HGL & Hrd).
pose proof Hnow as (HJ & Hkept & KS3 & Hfds' & Hfs').
pose proof HJ as (_ & _ & (memS & HJi & _) & _). rewrite !Z.add_0_r in HJi.
pose proof (h_frame SK B MT KS LAWS cx fp memS ly3 S3 W3 (ms_mem ms) md k HB HJi HFR)
  as (EF & EFL & HF4096 & HFceil & HF64 & HFapp & HFimg & ESH & HFpres & HSHpres).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (p_sizes cx) as (HnF & Hcap & Hbn).
set (Q := p_q cx p) in *.
destruct (PW.kind_fit (p_sw cx) (p_F cx) (p_cap cx) Q HK) as (_ & _ & HQi0 & HQfit & HQincl).
change (PSN.flen (p_F cx)) with (p_nF cx) in HQfit.
change (PSN.incl (p_sw cx) (p_F cx) Q) with (kr_incl cx Q) in HQfit, HQi0, HQincl.
assert (HQ0 : 24 <= Q) by (pose proof (PW.psn_q_ge (p_sw cx) (p_F cx) (p_cap cx) p); unfold Q, p_q; lia).
assert (HIr : 0 <= kr_incl cx Q < 2 ^ 32) by (unfold kr_incl, PSN.incl; apply PW.pw_hw_range).
assert (HTr : 0 <= PSN.rec_ts (p_sw cx) (p_F cx) Q < 2 ^ 64).
{ unfold PSN.rec_ts. pose proof (PW.pw_hw_range (p_sw cx) (p_F cx) Q 0). pose proof (PW.pw_hw_range (p_sw cx) (p_F cx) Q 4). lia. }
destruct (kr_seat_now cx fp k acc ly3 S3 W3 ms3 md3 b h buf i p (ms_regs ms) (ms_mem ms) md PP_TS false false false true
  Hctx Hnow (fun H => ltac:(discriminate H)) (fun H => ltac:(discriminate H)) (fun H => ltac:(discriminate H)))
  as (HS & SHOK).
rewrite <- Hsh in HS.
pose proof (kr_env_img (ms_regs ms) (kr_Xc cx fp p) (kr_Dc cx p)) as HEI.
set (E := kr_env (ms_regs ms) (kr_Xc cx fp p) (kr_Dc cx p)) in *.
assert (U32 : bv_unsigned (ew E 32) = pF cx fp + 32).
{ unfold E. rewrite (kr_env_x _ _ _ 0 ltac:(lia) : ew (kr_env (ms_regs ms) (kr_Xc cx fp p) (kr_Dc cx p)) 32 = _).
  cbn [nth kr_Xc kr_X]. unfold pPS, PO_PS, w64. apply unsigned_lit_small. lia. }
assert (U37 : U E (SOff 37 0) = PSN.rec_ts (p_sw cx) (p_F cx) Q).
{ apply U_atom; [|exact HTr]. unfold E. rewrite (kr_env_x _ _ _ 5 ltac:(lia) : ew (kr_env (ms_regs ms) (kr_Xc cx fp p) (kr_Dc cx p)) 37 = _).
  reflexivity. }
assert (UTS : forall sw : bool, p_sw cx = sw -> U E (kr_tsT sw) = PSN.rec_ts (p_sw cx) (p_F cx) Q).
{ intros sw Hs. rewrite Hs. apply (kr_tsT_U E (p_F cx) Q sw eq_refl); [lia|]. unfold p_nF in HQfit. lia. }
assert (KM : forall (H : word -> bool) (m m' : word -> option byte) rs,
   frame_of E rs (mrestrict H m) (mrestrict H m') ->
   windows rs = [(Some 26%nat, 0, 0); (Some 9%nat, 40, 40); (Some 32%nat, 64, 72)] ->
   forall a, 0 <= a < 2 ^ 64 -> ~ (pF cx fp + 96 <= a < pF cx fp + 104) -> aview SEGS H m' a = aview SEGS H m a).
{ intros H m m' rs HFr Hw. apply (kept_of_frame (segs := SEGS) E rs H m m' _ HFr).
  rewrite Hw. kr_wints U32. }
destruct (kr_swz cx) as [Hsw | Hsw]; rewrite Hsw in HS.
all: paj_run_tok RUN HS HJ SHOK krSpan; [kr_awr_ts U32 EF cx fp|].
all: pose proof (KM _ _ _ _ HFr ltac:(vm_compute; reflexivity)) as KM1; clear HF HFr HG.
all: psrr_branch_tok RUN BR HS SHOK krSpan.
(* 0x80f74 bne a1,a0 -> PP_abort: ts = sec * 10^6 + usec, so it is never taken *)
1, 3: exfalso; rewrite branch_ne_U, U37 in Hc;
  first [ pose proof (UTS false ltac:(unfold p_sw; rewrite Hsw; reflexivity)) as UT
        | pose proof (UTS true ltac:(unfold p_sw; rewrite Hsw; reflexivity)) as UT ];
  unfold kr_tsT, kr_f32, kb_be32, kb_le32, kb_lo3 in UT; rewrite UT, Z.eqb_refl in Hc; discriminate.
all: paj_run_tok RUN HS HJ SHOK krSpan; [kr_awr_ts U32 EF cx fp|].
all: pose proof (KM _ _ _ _ HFr ltac:(vm_compute; reflexivity)) as KM2.
all: rename HS into HSc.
all: assert (TSm : val_mem SEGS (ms_mem (restrict (w_H W3) ms1)) (pF cx fp + 32 + 64) 8 18446744073709551615)
  by (refine (h_field E _ (restrict (w_H W3) ms1) 2 32 12 72 64 72 _ (pF cx fp + 32) 64 8
        (SLit 18446744073709551615) 18446744073709551615 HSc eq_refl U32 _ eq_refl _ _); cbn; [tauto | lia | lia]).
all: prreg HSc (1%bv : bv 5) Q1; change 2156 with PP_KL2 in Q1.
all: prreg HSc (10%bv : bv 5) Q10; prreg HSc (11%bv : bv 5) Q11; prreg HSc (12%bv : bv 5) Q12.
all: prreg HSc (13%bv : bv 5) Q13; prreg HSc (26%bv : bv 5) Q26.
all: kregC HSc (18%bv : bv 5) Q18.
all: assert (KN : forall r, In r kr_keepN -> getr (ms_regs ms1) r = getr (ms_regs ms3) r).
all: try (intros r Hr; cbn [kr_keepN In] in Hr; repeat (destruct Hr as [<- | Hr]); [..|destruct Hr];
          lazymatch goal with |- getr _ ?r = _ =>
            let Q := fresh "Q" in prreg HSc r Q; rewrite Q; clear Q end;
          first [ rewrite R23; reflexivity
                | lazymatch goal with |- ew _ ?n = getr _ ?r =>
                    unfold E; rewrite (kr_env_reg _ _ _ n r eq_refl); apply KS3; kr_in end ]).
all: pmkst HSc; rewrite pa_sigma_pcap_source_next.
all: assert (U18 : U E (SOff 18 0) = Q)
  by (apply U_atom; [|lia]; unfold E; rewrite (kr_env_reg _ _ _ 18 18%bv eq_refl), (KS3 18%bv ltac:(kr_in)); exact R18).
all: assert (U20 : U E (SOff 20 0) = kr_incl cx Q)
  by (apply U_atom; [|lia]; unfold E; rewrite (kr_env_reg _ _ _ 20 20%bv eq_refl), (KS3 20%bv ltac:(kr_in)); exact R20).
all: apply (kr_next POST n HKL2 cx fp k acc ly3 S3 W3 ms3 md3 b h buf i p _ _ _ Hctx Hmeas HJ);
  [ rewrite !(proj1 (wvb_fds_fs _ _ _)); exact Hfds'
  | rewrite !(proj2 (wvb_fds_fs _ _ _)); exact Hfs'
  | exact Q1
  | exact KN
  | rewrite Q10; unfold E; rewrite (kr_env_x _ _ _ 0 ltac:(lia) : ew (kr_env (ms_regs ms) (kr_Xc cx fp p) (kr_Dc cx p)) 32 = _);
    reflexivity
  | rewrite Q11; unfold E; rewrite (kr_env_reg _ _ _ 22 22%bv eq_refl), (KS3 22%bv ltac:(kr_in)); exact R22
  | rewrite Q12; unfold E; rewrite (kr_env_reg _ _ _ 21 21%bv eq_refl), (KS3 21%bv ltac:(kr_in)); exact R21
  | rewrite Q13, U32; unfold pTS, PO_TS, w64; f_equal; lia
  | rewrite Q18, kb_add_U, U18, (kb_addz_U E (SOff 20 0) (kr_incl cx Q) 16 68719476736 eq_refl U20) by lia;
    unfold w64; f_equal; change (p_q cx p) with Q;
    rewrite zcanon_id by (clearbody Q; clear - HQfit HQ0 HnF Hn26 HIr; unfold M64; lia); clearbody Q; lia
  | rewrite Q26; unfold E; rewrite (kr_env_x _ _ _ 1 ltac:(lia) : ew (kr_env (ms_regs ms) (kr_Xc cx fp p) (kr_Dc cx p)) 33 = _);
    reflexivity
  | intros a Ha Hw Ht; unfold pTS, PO_TS in Ht; rewrite KM2, KM1 by lia; apply Hkept; [exact Ha | exact Hw]
  | unfold pTS, PO_TS; replace (pF cx fp + 96) with (pF cx fp + 32 + 64) by lia; exact TSm ].
Qed.

(* ---- the record's bytes the bcmp calls compare: the buffer the reader filled against the copy ---- *)
Lemma kr_garr8_aview : forall H (m : word -> option byte) base l j,
  garr8 SEGS (mrestrict H m) base l -> (j < length l)%nat -> aview SEGS H m (base + Z.of_nat j) = Some (nth j l 0).
Proof. intros H m base l j HG Hj. destruct (HG j Hj) as (Hv & Hr). exact (aview_of_val_mem1 SEGS H m _ _ Hv Hr). Qed.

Lemma kr_copy_aview : forall H (m : word -> option byte) b (F : list byte) j,
  garr8 SEGS (mrestrict H m) b (map (fun x : byte => bv_unsigned x) F) -> 0 <= j < Z.of_nat (length F) ->
  aview SEGS H m (b + j) = Some (bv_unsigned (nth (Z.to_nat j) F (Z_to_bv 8 0))).
Proof.
  intros H m b F j HG Hj. replace (b + j) with (b + Z.of_nat (Z.to_nat j)) by lia.
  rewrite (kr_garr8_aview H m b _ (Z.to_nat j) HG) by (rewrite length_map; lia).
  rewrite (nth_indep _ 0 (bv_unsigned (Z_to_bv 8 0))) by (rewrite length_map; lia).
  rewrite map_nth. reflexivity.
Qed.

Section recb.
Variables (sw : bool) (F : list byte) (Q : Z) (d : byte).
Hypotheses (HQ : 0 <= Q) (HFit : Q + 16 + PSN.incl sw F Q <= Z.of_nat (length F)) (HI0 : 0 <= PSN.incl sw F Q).

Lemma kr_raw_nth : forall j, (j < Z.to_nat (PSN.incl sw F Q))%nat ->
  nth j (PSN.rec_raw sw F Q) d = nth (Z.to_nat (Q + 16) + j) F d.
Proof.
  intros j Hj. unfold PSN.rec_raw. rewrite nth_firstn. destruct (Nat.ltb_spec j (Z.to_nat (PSN.incl sw F Q))); [|lia].
  apply nth_skipn.
Qed.

Lemma kr_raw_len : length (PSN.rec_raw sw F Q) = Z.to_nat (PSN.incl sw F Q).
Proof. unfold PSN.rec_raw. rewrite length_firstn, length_skipn. lia. Qed.

Lemma kr_recb_untag : PSN.tagged sw F Q = false -> forall j, (j < Z.to_nat (PSN.incl sw F Q))%nat ->
  nth j (PSN.rec_bytes sw F Q) d = nth (Z.to_nat (Q + 16) + j) F d.
Proof. intros Ht j Hj. unfold PSN.rec_bytes. rewrite Ht. apply kr_raw_nth. exact Hj. Qed.

Lemma kr_recb_tag12 : PSN.tagged sw F Q = true -> forall j, (j < 12)%nat ->
  nth j (PSN.rec_bytes sw F Q) d = nth (Z.to_nat (Q + 16) + j) F d.
Proof.
  intros Ht j Hj. assert (H18 : 18 <= PSN.incl sw F Q)
    by (unfold PSN.tagged in Ht; apply andb_prop in Ht as [Ht _]; apply andb_prop in Ht as [Ht _]; apply Z.leb_le in Ht; exact Ht).
  unfold PSN.rec_bytes. rewrite Ht. rewrite app_nth1 by (rewrite length_firstn, kr_raw_len; lia).
  rewrite nth_firstn. destruct (Nat.ltb_spec j 12); [|lia]. apply kr_raw_nth. lia.
Qed.

Lemma kr_recb_tagmid : PSN.tagged sw F Q = true -> forall j, (j < Z.to_nat (PSN.incl sw F Q - 16))%nat ->
  nth (12 + j) (PSN.rec_bytes sw F Q) d = nth (Z.to_nat (Q + 16) + (16 + j)) F d.
Proof.
  intros Ht j Hj. assert (H18 : 18 <= PSN.incl sw F Q)
    by (unfold PSN.tagged in Ht; apply andb_prop in Ht as [Ht _]; apply andb_prop in Ht as [Ht _]; apply Z.leb_le in Ht; exact Ht).
  unfold PSN.rec_bytes. rewrite Ht.
  rewrite app_nth2 by (rewrite length_firstn, kr_raw_len; lia).
  rewrite length_firstn, kr_raw_len. replace (12 + j - Nat.min 12 (Z.to_nat (PSN.incl sw F Q)))%nat with j by lia.
  rewrite app_nth1 by (rewrite length_firstn, length_skipn, kr_raw_len; lia).
  rewrite nth_firstn. destruct (Nat.ltb_spec j (Z.to_nat (PSN.incl sw F Q - 16))); [|lia].
  rewrite nth_skipn. apply kr_raw_nth. lia.
Qed.
End recb.

(* ---- a run's end state keeps the context of the record checks ---- *)
Lemma kr_now_keep : forall cx fp k ly3 S3 W3 ms3 md3 regs mem md regs' mem' md',
  kr_now cx fp k ly3 S3 W3 ms3 md3 regs mem md ->
  ajournal_gx SEGS B pe_G 0 [] LLVMF_STK (spZ (c_regs cx)) [sink_token] (c_ly cx) (c_S cx) (c_W cx)
    (c_mem cx) (c_md cx) [(PE_CID, fp)] ly3 S3 W3 mem' md' k ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (c_sp1 cx - 8192 <= a < c_sp1 cx) ->
     aview SEGS (w_H W3) mem' a = aview SEGS (w_H W3) mem a) ->
  (forall r, In r kr_keepS -> getr regs' r = getr regs r) ->
  m_fds md' = m_fds md -> m_fs md' = m_fs md ->
  kr_now cx fp k ly3 S3 W3 ms3 md3 regs' mem' md'.
Proof.
  intros cx fp k ly3 S3 W3 ms3 md3 regs mem md regs' mem' md' (HJ & Hk & KK & Hf & Hs) HJ' Hk' KK' Hf' Hs'.
  split; [exact HJ'|]. split; [intros a Ha Hw; rewrite Hk' by assumption; apply Hk; assumption|].
  split; [intros r Hr; rewrite KK' by exact Hr; apply KK; exact Hr|].
  split; [rewrite Hf'; exact Hf | rewrite Hs'; exact Hs].
Qed.

(* The kept registers of a run's end state: their own atom, or the seat's literal s7 = 0xff00 / s8 = swapped. *)
Ltac kr_keepS_run HS KS3 R23 R24 Hsw :=
  let r := fresh "r" in let Hr := fresh "Hr" in
  intros r Hr; cbn [kr_keepS In] in Hr; repeat (destruct Hr as [<- | Hr]); [..|destruct Hr];
  lazymatch goal with |- getr _ ?r = _ => let Q := fresh "Q" in prreg HS r Q; rewrite Q; clear Q end;
  first [ rewrite (KS3 23%bv ltac:(kr_in)), R23; reflexivity
        | rewrite (KS3 24%bv ltac:(kr_in)), R24, Hsw; reflexivity
        | lazymatch goal with |- ew _ ?n = getr _ ?r => apply (kr_env_reg _ _ _ n r eq_refl) end ].
(* The same, when the seat's registers are the cut's own (no kept relation in between). *)
Ltac kr_keepS_run0 HS R23 R24 Hsw :=
  let r := fresh "r" in let Hr := fresh "Hr" in
  intros r Hr; cbn [kr_keepS In] in Hr; repeat (destruct Hr as [<- | Hr]); [..|destruct Hr];
  lazymatch goal with |- getr _ ?r = _ => let Q := fresh "Q" in prreg HS r Q; rewrite Q; clear Q end;
  first [ rewrite R23; reflexivity
        | rewrite R24, Hsw; reflexivity
        | lazymatch goal with |- ew _ ?n = getr _ ?r => apply (kr_env_reg _ _ _ n r eq_refl) end ].

(* ---- after the third bcmp (untagged), 0x80e0c: bnez a0 -> PP_abort is not taken (a0 = 0) ---- *)
Definition PP_U : Z := 0x6d4.

Lemma kr_untag : forall POST n, at_cut (GI_KL2 B MT KS) POST n ->
  forall cx fp k acc ly3 S3 W3 ms3 md3 b h buf i p (ms : machine_state) md,
  kr_ctx cx fp k acc ly3 S3 W3 ms3 md3 b h buf i p ->
  (hw_meas cx ms3 <= S n)%nat ->
  kr_now cx fp k ly3 S3 W3 ms3 md3 (ms_regs ms) (ms_mem ms) md ->
  ms = mkst (ms_regs ms) (Z_to_bv 64 (BASE + PP_U)) (ms_mem ms) (seg_rom SEGS) ->
  getr (ms_regs ms) 10 = w64 0 ->
  SRr SEGS W3 (mkCfg ms md) (POST cx).
Proof.
intros POST n HKL2 cx fp k acc ly3 S3 W3 ms3 md3 b h buf i p ms md Hctx Hmeas Hnow Hsh R10.
pose proof Hctx as (HB & HJ3 & HFR & HMO & HRB).
pose proof HRB as (HCUT & Hpad & Hn26 & Hgood & Hi0 & Hip & HK & Hpe & R6 & R11 & R12 & R13 & R14 & R18 & R19 & R20
  & R21 & R22 & R23 & R24 & R25 & R26 & Hls & Hfirst & HGL & Hrd).
pose proof Hnow as (HJ & Hkept & KS3 & Hfds' & Hfs').
destruct (kr_seat_now cx fp k acc ly3 S3 W3 ms3 md3 b h buf i p (ms_regs ms) (ms_mem ms) md PP_U false false true false
  Hctx Hnow (fun H => ltac:(discriminate H)) (fun H => ltac:(discriminate H)) (fun _ => R10)) as (HS & SHOK).
rewrite <- Hsh in HS.
pose proof (kr_env_img (ms_regs ms) (kr_Xc cx fp p) (kr_Dc cx p)) as HEI.
destruct (kr_swz cx) as [Hsw | Hsw]; rewrite Hsw in HS.
all: paj_run_to_tok RUNTO HS HJ SHOK krSpan PP_TS; [kr_nowin|].
all: kr_kept_run HF Hm1.
all: lazymatch goal with |- SRr _ _ (mkCfg ?m _) _ =>
       pose proof (st_ok_pi_restrict_mkst (w_H W3) _ _ m HS eq_refl) as Hsh1; cbn [ss_pc] in Hsh1;
       change 1752 with PP_TS in Hsh1 end.
all: apply (kr_ts POST n HKL2 cx fp k acc ly3 S3 W3 ms3 md3 b h buf i p _ _ Hctx Hmeas); [|exact Hsh1].
all: apply (kr_now_keep _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hnow HJ);
  [ intros a _ _; rewrite Hm1; reflexivity
  | kr_keepS_run HS KS3 R23 R24 Hsw
  | exact (proj1 (wvb_fds_fs _ _ _))
  | exact (proj2 (wvb_fds_fs _ _ _)) ].
Qed.

(* ---- values the tagged path computes ---- *)
Lemma kb_subz2_U : forall E s v k c, c = - (k * 2 ^ 32) -> U E s = v -> 0 < k <= v -> v < 2 ^ 31 ->
  U E (SAlu ALU_SRL (SAlu ALU_ADD (SAlu ALU_SLL s (SLit 32)) (SLit c)) (SLit 32)) = v - k.
Proof. intros E s v k c -> Hs Hk Hv. exact (kb_subz_U E s v k Hs Hk Hv). Qed.

Lemma kr_land3840 : forall d30, 0 <= d30 -> Z.land (d30 * 2 ^ 8) 3840 = (d30 mod 2 ^ 4) * 2 ^ 8.
Proof.
  intros d30 H30. replace 3840 with (Z.shiftl (Z.ones 4) 8) by reflexivity.
  rewrite <- Z.shiftl_mul_pow2 by lia. rewrite <- Z.shiftl_land. rewrite Z.land_ones by lia.
  rewrite Z.shiftl_mul_pow2 by lia. reflexivity.
Qed.

Lemma kr_vid_val : forall d30 d31, 0 <= d30 < 256 -> 0 <= d31 < 256 ->
  Z.lor ((d30 mod 2 ^ 4) * 2 ^ 8) d31 = (256 * d30 + d31) mod 4096.
Proof.
  intros d30 d31 H30 H31.
  rewrite kb_lor by (pose proof (Z.mod_pos_bound d30 (2 ^ 4)); lia).
  pose proof (Z.div_mod d30 (2 ^ 4) ltac:(lia)) as Hd. pose proof (Z.mod_pos_bound d30 (2 ^ 4) ltac:(lia)) as Hr.
  apply (Z.mod_unique (256 * d30 + d31) 4096 (d30 / 2 ^ 4)); [lia|].
  change (2 ^ 4) with 16 in *. change (2 ^ 8) with 256. lia.
Qed.

Lemma kr_vid_U : forall E x30 x31 d30 d31, U E x30 = d30 -> U E x31 = d31 -> 0 <= d30 < 256 -> 0 <= d31 < 256 ->
  U E (SAlu ALU_OR (SAlu ALU_AND (SAlu ALU_SLL x30 (SLit 8)) (SLit 3840)) x31) = (256 * d30 + d31) mod 4096.
Proof.
  intros E x30 x31 d30 d31 U30 U31 R30 R31. rewrite !U_SAlu, U30, U31, !U_SLit. cbn [zalu_raw].
  change (Z.land (zcanon 8) 63) with 8. rewrite Z.shiftl_mul_pow2 by lia.
  rewrite (zcanon_id (d30 * 2 ^ 8)) by (unfold M64; lia). change (zcanon 3840) with 3840.
  rewrite kr_land3840 by lia.
  pose proof (Z.mod_pos_bound d30 (2 ^ 4) ltac:(lia)) as Hr.
  rewrite (zcanon_id ((d30 mod 2 ^ 4) * 2 ^ 8)) by (unfold M64; lia).
  rewrite kr_vid_val by assumption. apply zcanon_id. unfold M64. pose proof (Z.mod_pos_bound (256 * d30 + d31) 4096). lia.
Qed.

Lemma kr_zext16_U : forall E a v, U E a = v -> 0 <= v < 2 ^ 16 -> U E (SExt false 16 a) = v.
Proof.
  intros E a v Ha Hv. rewrite U_SExt, Ha. change (Z.of_N 16) with 16. rewrite Z.mod_small by lia.
  apply zcanon_id. unfold M64. lia.
Qed.

Lemma kr_sext32_U : forall E a v, U E a = v -> 0 <= v < 2 ^ 32 -> U E (SExt true 32 a) = kb_sx32 v.
Proof.
  intros E a v Ha Hv. rewrite U_SExt, Ha. change (Z.of_N 32) with 32. rewrite Z.mod_small by lia.
  unfold zcanon, M64. rewrite <- (kb_swrap_sx v Hv). reflexivity.
Qed.

Lemma kr_tagged_incl : forall sw F Q, PSN.tagged sw F Q = true -> 18 <= PSN.incl sw F Q.
Proof.
  intros sw F Q Ht. unfold PSN.tagged in Ht. apply andb_prop in Ht as [Ht _]. apply andb_prop in Ht as [Ht _].
  apply Z.leb_le in Ht. exact Ht.
Qed.

(* ---- what the reader left at 0x80c68, compared byte for byte: buf + jb against the copy at jf ---- *)
Lemma kr_cmp_ms3 : forall cx fp k acc ly3 S3 W3 ms3 md3 b h buf i p jb jf (len : nat),
  kr_ctx cx fp k acc ly3 S3 W3 ms3 md3 b h buf i p ->
  p_kind cx (p_q cx p) = PSN.KFit ->
  (forall j, (j < len)%nat -> nth (jb + j) (PSN.rec_bytes (p_sw cx) (p_F cx) (p_q cx p)) (Z_to_bv 8 0) =
                              nth (jf + j) (p_F cx) (Z_to_bv 8 0)) ->
  (jb + len <= length (PSN.rec_bytes (p_sw cx) (p_F cx) (p_q cx p)))%nat -> (jf + len <= length (p_F cx))%nat ->
  forall j, 0 <= j < Z.of_nat len ->
  aview SEGS (w_H W3) (ms_mem ms3) (buf + Z.of_nat jb + j) = aview SEGS (w_H W3) (ms_mem ms3) (b + Z.of_nat jf + j).
Proof.
  intros cx fp k acc ly3 S3 W3 ms3 md3 b h buf i p jb jf len Hctx HK Heq Hlb Hlf j Hj.
  destruct Hctx as (_ & _ & _ & _ & HRB).
  destruct HRB as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hrd).
  destruct Hrd as (Hsrc & _ & Hfit). specialize (Hfit HK) as (_ & _ & _ & _ & Vbuf).
  pose proof Hsrc as (Wl & cpos & fl & mdd & _ & _ & _ & _ & HbF & _ & _ & _ & HCg & _).
  replace (buf + Z.of_nat jb + j) with (buf + Z.of_nat (jb + Z.to_nat j)) by lia.
  rewrite (kr_garr8_aview _ _ buf _ (jb + Z.to_nat j) Vbuf) by (rewrite length_map; lia).
  replace (b + Z.of_nat jf + j) with (b + (Z.of_nat jf + j)) by lia.
  rewrite (kr_copy_aview _ _ b (p_F cx) (Z.of_nat jf + j) HCg) by lia.
  rewrite (nth_indep _ 0 (bv_unsigned (Z_to_bv 8 0))) by (rewrite length_map; lia).
  rewrite map_nth. rewrite (Heq (Z.to_nat j)) by lia. do 3 f_equal. lia.
Qed.

(* ---- a bcmp call of the record checks, from and back to the record context ---- *)
Lemma kr_bcmp_now : forall cx fp k acc ly3 S3 W3 ms3 md3 b h buf i p (regs : bvmap 5 word) mem md x y n xb xm yb ym
  retpc POST,
  kr_ctx cx fp k acc ly3 S3 W3 ms3 md3 b h buf i p ->
  kr_now cx fp k ly3 S3 W3 ms3 md3 regs mem md ->
  getr regs 1 = Z_to_bv 64 (BASE + retpc) -> 0 <= retpc < 2 ^ 40 -> retpc mod 2 = 0 ->
  getr regs 10 = w64 x -> getr regs 11 = w64 y -> getr regs 12 = w64 n -> 0 <= n < 2 ^ 32 ->
  In (xb, xm) (ablocks B ly3 S3) -> xb <= x -> x + n <= xb + req_size xm ->
  In (yb, ym) (ablocks B ly3 S3) -> yb <= y -> y + n <= yb + req_size ym ->
  (forall j, 0 <= j < n -> aview SEGS (w_H W3) (ms_mem ms3) (x + j) = aview SEGS (w_H W3) (ms_mem ms3) (y + j)) ->
  (forall regs2 mem2 md2, kr_now cx fp k ly3 S3 W3 ms3 md3 regs2 mem2 md2 -> getr regs2 10 = w64 0 ->
     SRr SEGS W3 (mkCfg (mkst regs2 (Z_to_bv 64 (BASE + retpc)) mem2 (seg_rom SEGS)) md2) POST) ->
  SRr SEGS W3 (mkCfg (mkst regs (Z_to_bv 64 (SIGMA PS___interceptor_trampoline_bcmp)) mem (seg_rom SEGS)) md) POST.
Proof.
  intros cx fp k acc ly3 S3 W3 ms3 md3 b h buf i p regs mem md x y n xb xm yb ym retpc POST Hctx Hnow R1 Hret1 Hret2
    R10 R11 R12 Hn Hxin Hx0 Hx1 Hyin Hy0 Hy1 HEQ K.
  pose proof Hctx as (HB & HJ3 & HFR & HMO & HRB).
  pose proof HRB as (HCUT & _).
  pose proof HCUT as (HBODY & _).
  pose proof HBODY as (_ & _ & _ & _ & _ & _ & (G2 & G8 & G9 & G27 & G3 & G4) & _).
  pose proof Hnow as (HJ & Hkept & KS3 & Hfds' & Hfs').
  pose proof (h_sp SK B MT KS cx HB) as (Hsp16 & Hsp_lo & Hsp_hi & Hsp1 & Hsp1_32).
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  pose proof HJ as (_ & _ & (memS & HJi & _) & _). rewrite !Z.add_0_r in HJi. pose proof HJi as (HAR & _).
  destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR Hxin) as (_ & Hxb4096 & Hxceil & _ & _ & _ & Hxm).
  destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR Hyin) as (_ & Hyb4096 & Hyceil & _ & _ & _ & Hym).
  pose proof (req_size_pos xm ltac:(lia)) as [_ Hxr]. pose proof (req_size_pos ym ltac:(lia)) as [_ Hyr].
  apply (kr_bcmp cx fp k ly3 S3 W3 regs mem md x y n xb xm yb ym (Z_to_bv 64 (BASE + retpc)) POST HB HJ).
  - rewrite (KS3 2%bv ltac:(kr_in)). exact G2.
  - rewrite (KS3 3%bv ltac:(kr_in)). exact G3.
  - rewrite (KS3 4%bv ltac:(kr_in)). exact G4.
  - exact R1.
  - apply ret_ok_codeptr_v; [exact Hret1 | exact Hret2].
  - exact R10.
  - exact R11.
  - exact R12.
  - exact Hn.
  - exact Hxin.
  - exact Hx0.
  - exact Hx1.
  - exact Hyin.
  - exact Hy0.
  - exact Hy1.
  - intros j Hj. rewrite !Hkept by lia. exact (HEQ j Hj).
  - intros regs2 mem2 md2 HJ2 HP HR0 Ef Es Hk2. apply K; [|exact HR0].
    apply (kr_now_keep _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hnow HJ2); [exact Hk2 | | exact Ef | exact Es].
    intros r Hr. cbn [kr_keepS In] in Hr.
    repeat (destruct Hr as [<- | Hr]; [rewrite (h_pres _ _ _ HP) by acs; reflexivity|]). destruct Hr.
Qed.

(* ---- after the second bcmp (tagged), 0x80dac: bnez a0 is not taken (a0 = 0); the vlan id check 0x80df8 ---- *)
Definition PP_T2 : Z := 0x674.

Lemma kr_tag2 : forall POST n, at_cut (GI_KL2 B MT KS) POST n ->
  forall cx fp k acc ly3 S3 W3 ms3 md3 b h buf i p (ms : machine_state) md,
  kr_ctx cx fp k acc ly3 S3 W3 ms3 md3 b h buf i p ->
  (hw_meas cx ms3 <= S n)%nat -> PSN.tagged (p_sw cx) (p_F cx) (p_q cx p) = true ->
  kr_now cx fp k ly3 S3 W3 ms3 md3 (ms_regs ms) (ms_mem ms) md ->
  ms = mkst (ms_regs ms) (Z_to_bv 64 (BASE + PP_T2)) (ms_mem ms) (seg_rom SEGS) ->
  getr (ms_regs ms) 10 = w64 0 ->
  SRr SEGS W3 (mkCfg ms md) (POST cx).
Proof.
intros POST n HKL2 cx fp k acc ly3 S3 W3 ms3 md3 b h buf i p ms md Hctx Hmeas Htag Hnow Hsh R10.
pose proof Hctx as (HB & HJ3 & HFR & HMO & HRB).
pose proof HRB as (HCUT & Hpad & Hn26 & Hgood & Hi0 & Hip & HK & Hpe & R6 & R11 & R12 & R13 & R14 & R18 & R19 & R20
  & R21 & R22 & R23 & R24 & R25 & R26 & Hls & Hfirst & HGL & Hrd).
pose proof Hnow as (HJ & Hkept & KS3 & Hfds' & Hfs').
pose proof (kr_tagged_incl _ _ _ Htag) as H18. change (PSN.incl (p_sw cx) (p_F cx) (p_q cx p)) with (kr_incl cx (p_q cx p)) in H18.
destruct (PW.kind_fit (p_sw cx) (p_F cx) (p_cap cx) (p_q cx p) HK) as (_ & _ & _ & HQfit & _).
change (PSN.flen (p_F cx)) with (p_nF cx) in HQfit.
change (PSN.incl (p_sw cx) (p_F cx) (p_q cx p)) with (kr_incl cx (p_q cx p)) in HQfit.
assert (HQ0 : 24 <= p_q cx p) by (pose proof (PW.psn_q_ge (p_sw cx) (p_F cx) (p_cap cx) p); unfold p_q; lia).
destruct (kr_seat_now cx fp k acc ly3 S3 W3 ms3 md3 b h buf i p (ms_regs ms) (ms_mem ms) md PP_T2 true false true false
  Hctx Hnow (fun _ => ltac:(lia)) (fun H => ltac:(discriminate H)) (fun _ => R10)) as (HS & SHOK).
rewrite <- Hsh in HS.
pose proof (kr_env_img (ms_regs ms) (kr_Xc cx fp p) (kr_Dc cx p)) as HEI.
assert (UDg : forall E2, ed E2 0 = kr_Dc cx p -> forall j, 0 <= j < 32 ->
  U E2 (SData 0 j 1) = PSN.fb (p_F cx) (p_q cx p + j))
  by (intros E2 ED2 j Hj; unfold p_nF in HQfit; apply (kr_U_fbE E2 (p_F cx) (p_q cx p) j ED2); lia).
assert (Uvid : forall E2, (forall n0, (n0 < 64)%nat -> ew E2 n0 = ew (kr_env (ms_regs ms) (kr_Xc cx fp p) (kr_Dc cx p)) n0) ->
  U E2 (SExt false 16 (SOff 36 0)) = PSN.rec_vid (p_F cx) (p_q cx p)).
{ intros E2 AG. apply kr_zext16_U; [|pose proof (kr_rec_vid_range (p_F cx) (p_q cx p)); lia].
  apply U_atom; [|pose proof (kr_rec_vid_range (p_F cx) (p_q cx p)); lia].
  rewrite AG by lia. rewrite (kr_env_x _ _ _ 4 ltac:(lia) : ew (kr_env (ms_regs ms) (kr_Xc cx fp p) (kr_Dc cx p)) 36 = _).
  cbn [nth kr_Xc kr_X]. rewrite Htag. reflexivity. }
destruct (kr_swz cx) as [Hsw | Hsw]; rewrite Hsw in HS.
all: paj_run_tok RUN HS HJ SHOK krSpan; [kr_nowin|].
all: kr_kept_run HF Hm1.
all: psrr_branch_tok RUN BR HS SHOK krSpan.
(* 0x80df8 bne a0,a1 -> PP_abort: the id the harness assembles from bytes 30, 31 is the one the reader stored *)
1, 3: exfalso; rewrite branch_ne_U in Hc;
  lazymatch type of Hc with negb (U ?E2 _ =? U _ _) = true =>
    rewrite (kr_vid_U E2 _ _ _ _ (UDg E2 eq_refl 30 ltac:(lia)) (UDg E2 eq_refl 31 ltac:(lia))
               (kr_fb_range _ _) (kr_fb_range _ _)) in Hc;
    rewrite (Uvid E2 ltac:(kr_agree)) in Hc end;
  unfold PSN.rec_vid in Hc; replace (p_q cx p + 30) with (p_q cx p + 30) in Hc by reflexivity;
  rewrite Z.eqb_refl in Hc; discriminate.
all: paj_run_to_tok RUNTO HS HJ SHOK krSpan PP_TS; [kr_nowin|].
all: kr_kept_run HF Hm2.
all: lazymatch goal with |- SRr _ _ (mkCfg ?m _) _ =>
       pose proof (st_ok_pi_restrict_mkst (w_H W3) _ _ m HS eq_refl) as Hsh1; cbn [ss_pc] in Hsh1;
       change 1752 with PP_TS in Hsh1 end.
all: apply (kr_ts POST n HKL2 cx fp k acc ly3 S3 W3 ms3 md3 b h buf i p _ _ Hctx Hmeas); [|exact Hsh1].
all: apply (kr_now_keep _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hnow HJ);
  [ intros a _ _; rewrite Hm2, Hm1; reflexivity
  | kr_keepS_run HS KS3 R23 R24 Hsw
  | rewrite !(proj1 (wvb_fds_fs _ _ _)); reflexivity
  | rewrite !(proj2 (wvb_fds_fs _ _ _)); reflexivity ].
Qed.

(* ---- after the first bcmp (tagged), 0x80d90: bnez a0 is not taken; the second bcmp 0x80da8 ---- *)
Definition PP_T1 : Z := 0x658.

Lemma kr_recb_len_tag : forall sw F Q, 0 <= Q -> Q + 16 + PSN.incl sw F Q <= Z.of_nat (length F) ->
  PSN.tagged sw F Q = true -> (12 + Z.to_nat (PSN.incl sw F Q - 16) <= length (PSN.rec_bytes sw F Q))%nat.
Proof.
  intros sw F Q HQ HL Ht. pose proof (kr_tagged_incl _ _ _ Ht) as H18.
  assert (HI0 : 0 <= PSN.incl sw F Q) by lia.
  unfold PSN.rec_bytes. rewrite Ht. rewrite !length_app, !length_firstn, length_skipn, (kr_raw_len sw F Q HQ HL). lia.
Qed.

Lemma kr_tag1 : forall POST n, at_cut (GI_KL2 B MT KS) POST n ->
  forall cx fp k acc ly3 S3 W3 ms3 md3 b h buf i p (ms : machine_state) md,
  kr_ctx cx fp k acc ly3 S3 W3 ms3 md3 b h buf i p ->
  (hw_meas cx ms3 <= S n)%nat -> PSN.tagged (p_sw cx) (p_F cx) (p_q cx p) = true ->
  kr_now cx fp k ly3 S3 W3 ms3 md3 (ms_regs ms) (ms_mem ms) md ->
  ms = mkst (ms_regs ms) (Z_to_bv 64 (BASE + PP_T1)) (ms_mem ms) (seg_rom SEGS) ->
  getr (ms_regs ms) 10 = w64 0 ->
  SRr SEGS W3 (mkCfg ms md) (POST cx).
Proof.
intros POST n HKL2 cx fp k acc ly3 S3 W3 ms3 md3 b h buf i p ms md Hctx Hmeas Htag Hnow Hsh R10.
pose proof Hctx as (HB & HJ3 & HFR & HMO & HRB).
pose proof HRB as (HCUT & Hpad & Hn26 & Hgood & Hi0 & Hip & HK & Hpe & R6 & R11 & R12 & R13 & R14 & R18 & R19 & R20
  & R21 & R22 & R23 & R24 & R25 & R26 & Hls & Hfirst & HGL & Hrd).
pose proof HCUT as (_ & _ & _ & HPERM & _).
pose proof Hnow as (HJ & Hkept & KS3 & Hfds' & Hfs').
pose proof HJ3 as (_ & _ & (memS & HJi & _) & _). rewrite !Z.add_0_r in HJi. pose proof HJi as (HAR3 & _).
pose proof (h_blocks3 B LAWS ly3 S3 W3 (ms_mem ms3) md3 _ _ _ _ HAR3 HPERM) as (Hb_in & Hh_in & Hbuf_in & _).
destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR3 Hb_in) as (_ & Hb4096 & Hbceil & _).
destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR3 Hbuf_in) as (_ & Hbuf4096 & Hbufceil & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (p_sizes cx) as (HnF & Hcap & Hbn).
pose proof (req_size_pos (p_bn cx) ltac:(lia)) as [_ Hreqbn].
pose proof (req_size_pos (p_nF cx) ltac:(lia)) as [_ Hreqb].
pose proof (kr_tagged_incl _ _ _ Htag) as H18. change (PSN.incl (p_sw cx) (p_F cx) (p_q cx p)) with (kr_incl cx (p_q cx p)) in H18.
destruct (PW.kind_fit (p_sw cx) (p_F cx) (p_cap cx) (p_q cx p) HK) as (_ & _ & _ & HQfit & HQincl).
change (PSN.flen (p_F cx)) with (p_nF cx) in HQfit.
change (PSN.incl (p_sw cx) (p_F cx) (p_q cx p)) with (kr_incl cx (p_q cx p)) in HQfit, HQincl.
assert (HQ0 : 24 <= p_q cx p) by (pose proof (PW.psn_q_ge (p_sw cx) (p_F cx) (p_cap cx) p); unfold p_q; lia).
assert (HIr : 0 <= kr_incl cx (p_q cx p) < 2 ^ 32) by (unfold kr_incl, PSN.incl; apply PW.pw_hw_range).
destruct (kr_seat_now cx fp k acc ly3 S3 W3 ms3 md3 b h buf i p (ms_regs ms) (ms_mem ms) md PP_T1 true false true false
  Hctx Hnow (fun _ => ltac:(lia)) (fun H => ltac:(discriminate H)) (fun _ => R10)) as (HS & SHOK).
rewrite <- Hsh in HS.
pose proof (kr_env_img (ms_regs ms) (kr_Xc cx fp p) (kr_Dc cx p)) as HEI.
set (E := kr_env (ms_regs ms) (kr_Xc cx fp p) (kr_Dc cx p)) in *.
assert (EG : forall n0 (r : bv 5), Z.of_nat n0 = bv_unsigned r -> ew E n0 = getr (ms_regs ms3) r ->
   forall v, getr (ms_regs ms3) r = w64 v -> 0 <= v < 2 ^ 64 -> bv_unsigned (ew E n0) = v).
{ intros n0 r Hn0 Hr v Hv Hvr. rewrite Hr, Hv. unfold w64. apply unsigned_lit_small. exact Hvr. }
assert (E22 : ew E 22 = getr (ms_regs ms3) 22) by (unfold E; rewrite (kr_env_reg _ _ _ 22 22%bv eq_refl); apply KS3; kr_in).
assert (E26 : ew E 26 = getr (ms_regs ms3) 26) by (unfold E; rewrite (kr_env_reg _ _ _ 26 26%bv eq_refl); apply KS3; kr_in).
assert (U20 : U E (SOff 20 0) = kr_incl cx (p_q cx p))
  by (apply U_atom; [|lia]; unfold E; rewrite (kr_env_reg _ _ _ 20 20%bv eq_refl), (KS3 20%bv ltac:(kr_in)); exact R20).
destruct (kr_swz cx) as [Hsw | Hsw]; rewrite Hsw in HS.
all: paj_run_tok RUN HS HJ SHOK krSpan; [kr_nowin|].
all: kr_kept_run HF Hm1.
all: prreg HS (1%bv : bv 5) Q1; change 1652 with PP_T2 in Q1.
all: prreg HS (10%bv : bv 5) Q10; prreg HS (11%bv : bv 5) Q11; kregC HS (12%bv : bv 5) Q12.
all: lazymatch goal with |- SRr _ _ (mkCfg ?m ?mdx) _ =>
       assert (Hnow1 : kr_now cx fp k ly3 S3 W3 ms3 md3 (ms_regs m) (ms_mem m) mdx) end.
all: try (apply (kr_now_keep _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hnow HJ);
          [ intros a _ _; rewrite Hm1; reflexivity
          | kr_keepS_run HS KS3 R23 R24 Hsw
          | exact (proj1 (wvb_fds_fs _ _ _))
          | exact (proj2 (wvb_fds_fs _ _ _)) ]).
all: pmkst HS.
all: apply (kr_bcmp_now cx fp k acc ly3 S3 W3 ms3 md3 b h buf i p _ _ _ (buf + 12) (b + p_q cx p + 32)
       (kr_incl cx (p_q cx p) - 16) buf (p_bn cx) b (p_nF cx) PP_T2 (POST cx) Hctx Hnow1 Q1);
  [ unfold PP_T2; lia | reflexivity
  | rewrite Q10, (EG 22%nat 22%bv eq_refl E22 buf R22) by lia; reflexivity
  | rewrite Q11, (EG 26%nat 26%bv eq_refl E26 (b + p_q cx p) R26) by lia; unfold w64; f_equal; lia
  | rewrite Q12, (kb_subz2_U E (SOff 20 0) (kr_incl cx (p_q cx p)) 16 (-68719476736) eq_refl U20) by lia; reflexivity
  | lia
  | exact Hbuf_in | lia | (pose proof (req_size_pos (p_bn cx) ltac:(lia)); unfold p_bn in *; lia)
  | exact Hb_in | lia | lia
  | 
  | intros regs2 mem2 md2 Hnow2 HR0;
    exact (kr_tag2 POST n HKL2 cx fp k acc ly3 S3 W3 ms3 md3 b h buf i p (mkst regs2 (Z_to_bv 64 (BASE + PP_T2)) mem2 (seg_rom SEGS))
             md2 Hctx Hmeas Htag Hnow2 eq_refl HR0) ].
all: intros j Hj.
all: pose proof (kr_cmp_ms3 cx fp k acc ly3 S3 W3 ms3 md3 b h buf i p 12 (Z.to_nat (p_q cx p + 32))
       (Z.to_nat (kr_incl cx (p_q cx p) - 16)) Hctx HK) as HC.
all: replace (buf + 12 + j) with (buf + Z.of_nat 12 + j) by reflexivity.
all: replace (b + p_q cx p + 32 + j) with (b + Z.of_nat (Z.to_nat (p_q cx p + 32)) + j) by lia.
all: apply HC; [ | | | lia ].
all: unfold kr_incl in *.
all: try (intros j0 Hj0; rewrite (kr_recb_tagmid (p_sw cx) (p_F cx) (p_q cx p) (Z_to_bv 8 0)) by (unfold p_nF in HQfit; first [lia | exact Htag]);
          f_equal; lia).
all: try (unfold p_nF in HQfit; apply (kr_recb_len_tag (p_sw cx) (p_F cx) (p_q cx p)); first [lia | exact Htag]).
all: try (unfold p_nF in HQfit; lia).
Qed.

(* ---- the record checks, 0x80c68 .. the bcmp calls 0x80d8c (tagged) / 0x80e08 (untagged) ---- *)
Lemma kr_res_fit : forall cx Q, p_kind cx Q = PSN.KFit ->
  p_res cx Q = if PSN.tagged (p_sw cx) (p_F cx) Q then kr_incl cx Q - 4 else kr_incl cx Q.
Proof. intros cx Q HK. unfold p_res, PSN.res_of. unfold p_kind in HK. rewrite HK. reflexivity. Qed.

Lemma kr_sltu1_U : forall E a, U E (SAlu ALU_SLTU a (SLit 1)) = if U E a <? 1 then 1 else 0.
Proof. intros E a. rewrite U_SAlu, U_SLit. cbn [zalu_raw]. change (zcanon 1) with 1. destruct (_ <? _); reflexivity. Qed.

Ltac kr_boolZ := repeat match goal with
  | H : negb _ = true |- _ => apply Bool.negb_true_iff in H
  | H : negb _ = false |- _ => apply Bool.negb_false_iff in H
  | H : Z.ltb _ _ = true |- _ => apply Z.ltb_lt in H
  | H : Z.ltb _ _ = false |- _ => apply Z.ltb_ge in H
  | H : Z.eqb _ _ = true |- _ => apply Z.eqb_eq in H
  | H : Z.eqb _ _ = false |- _ => apply Z.eqb_neq in H
  | H : Z.leb _ _ = true |- _ => apply Z.leb_le in H
  | H : Z.leb _ _ = false |- _ => apply Z.leb_gt in H
  | H : (_ && _) = true |- _ => apply andb_prop in H; destruct H
  end.

(* A branch hypothesis of a run's end state, as a fact about the base environment E's values. *)
Ltac kr_toE E H := repeat match type of H with context [U ?E2 ?t] =>
  tryif constr_eq E2 E then fail else
    (let AG := fresh "AG" in
     assert (AG : env_agree 64 E E2)
       by (split; [ let ii := fresh "ii" in let Hii := fresh "Hii" in intros ii Hii; cbn [ewset ew];
                    repeat match goal with |- context [Nat.eqb ii ?m] => rewrite (proj2 (Nat.eqb_neq ii m)) by lia end;
                    reflexivity
                  | reflexivity ]);
     rewrite (U_agree 64 E E2 t AG ltac:(vm_compute; reflexivity)) in H; clear AG) end.

Ltac kr_tagf := repeat match goal with
  | H : PSN.tagged _ _ _ = true |- _ => unfold PSN.tagged in H; kr_boolZ
  | H : PSN.tagged _ _ _ = false |- _ => unfold PSN.tagged in H
  | H : (_ && _) = false |- _ => apply Bool.andb_false_iff in H; destruct H as [H | H]; kr_boolZ
  end.

(* A branch hypothesis made a fact about values: the branch lemma, the base environment, the values (rw), the
   conditions inside (the record's tag, a byte test), then Z facts. *)
Ltac kr_normH E H rw :=
  first [ rewrite branch_ne_U in H | rewrite branch_eq_U in H | rewrite branch_ltu_U in H | rewrite branch_geu_U in H ];
  kr_toE E H; rw H;
  repeat match type of H with context [if ?c then _ else _] => let e := fresh "Eif" in destruct c eqn:e end;
  kr_boolZ.

(* The record checks as a run: run to the next branch, take both arms, normalize the new branch fact, and close
   every arm whose facts contradict (an abort: the cut's facts refute it); stop at the bcmp calls. *)
Ltac kr_run HS HJ SHOK :=
  paj_run_tok RUN HS HJ SHOK krSpan; [kr_nowin|];
  let Hm := fresh "Hm" in
  lazymatch goal with HF : frame_of _ _ (ms_mem _) (ms_mem _) |- _ => kr_kept_run HF Hm end.
(* One step: at a branch, take both arms (psrr_branch_tok decides the condition, the state stays at the branch),
   close the arms whose facts contradict, and run the others past the branch; elsewhere run to the next stop. *)
Ltac kr_step HS HJ SHOK NORM :=
  lazymatch type of HS with
  | st_ok_pi _ _ _ ?ss _ =>
      let pc := eval vm_compute in (ss_pc ss) in
      let isbr := eval vm_compute in (Z.eqb pc 1332 || Z.eqb pc 1500 || Z.eqb pc 1508 || Z.eqb pc 1540 ||
                                      Z.eqb pc 1584 || Z.eqb pc 1592 || Z.eqb pc 1608 || Z.eqb pc 1736) in
      lazymatch isbr with
      | true => psrr_branch_tok RUN BR HS SHOK krSpan;
                lazymatch goal with H : branch_taken _ _ _ = _ |- _ => NORM H end;
                first [ solve [kr_tagf; unfold kr_incl in *; lia] | kr_run HS HJ SHOK ]
      | false => kr_run HS HJ SHOK
      end
  end.

Lemma kr_rec : forall POST n, at_cut (GI_KL2 B MT KS) POST n -> at_cut GI_KREC POST (S n).
Proof.
intros POST n HKL2 cx fp k acc ly3 S3 W3 ms3 md3 HB HJ HFR HMO (b & h & buf & i & p & HRB) Hmeas.
assert (Hctx : kr_ctx cx fp k acc ly3 S3 W3 ms3 md3 b h buf i p) by exact (conj HB (conj HJ (conj HFR (conj HMO HRB)))).
pose proof HRB as (HCUT & Hpad & Hn26 & Hgood & Hi0 & Hip & HK & Hpe & R6 & R11 & R12 & R13 & R14 & R18 & R19 & R20
  & R21 & R22 & R23 & R24 & R25 & R26 & Hls & Hfirst & HGL & Hrd).
pose proof HCUT as (HBODY & _ & _ & HPERM & _).
pose proof HBODY as (Hpc & Hrv & Hsv & Hrom & Hfreg & Hfcsr & (G2 & G8 & G9 & G27 & G3 & G4) & _).
pose proof HJ as (_ & _ & (memS & HJi & _) & _). rewrite !Z.add_0_r in HJi. pose proof HJi as (HAR3 & _).
pose proof (h_blocks3 B LAWS ly3 S3 W3 (ms_mem ms3) md3 _ _ _ _ HAR3 HPERM) as (Hb_in & Hh_in & Hbuf_in & _).
destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR3 Hb_in) as (_ & Hb4096 & Hbceil & _).
destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR3 Hbuf_in) as (_ & Hbuf4096 & Hbufceil & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (p_sizes cx) as (HnF & Hcap & Hbn).
pose proof (req_size_pos (p_bn cx) ltac:(lia)) as [_ Hreqbn].
pose proof (req_size_pos (p_nF cx) ltac:(lia)) as [_ Hreqb].
destruct (PW.kind_fit (p_sw cx) (p_F cx) (p_cap cx) (p_q cx p) HK) as (_ & _ & _ & HQfit & HQincl).
change (PSN.flen (p_F cx)) with (p_nF cx) in HQfit.
change (PSN.incl (p_sw cx) (p_F cx) (p_q cx p)) with (kr_incl cx (p_q cx p)) in HQfit, HQincl.
assert (HQ0 : 24 <= p_q cx p) by (pose proof (PW.psn_q_ge (p_sw cx) (p_F cx) (p_cap cx) p); unfold p_q; lia).
assert (HIr : 0 <= kr_incl cx (p_q cx p) < 2 ^ 32) by (unfold kr_incl, PSN.incl; apply PW.pw_hw_range).
assert (Hor : 0 <= PSN.orig (p_sw cx) (p_F cx) (p_q cx p) < 2 ^ 32) by (unfold PSN.orig; apply PW.pw_hw_range).
pose proof (kr_now_ref _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hctx) as Hnow0.
pose proof (kr_res_fit cx (p_q cx p) HK) as HRES.
pose proof (kr_fb_range (p_F cx) (p_q cx p + 28)) as F28. pose proof (kr_fb_range (p_F cx) (p_q cx p + 29)) as F29.
assert (KS0 : forall r, In r kr_keepS -> getr (ms_regs ms3) r = getr (ms_regs ms3) r) by (intros; reflexivity).
pose proof (kr_env_img (ms_regs ms3) (kr_Xc cx fp p) (kr_Dc cx p)) as HEI.
set (E := kr_env (ms_regs ms3) (kr_Xc cx fp p) (kr_Dc cx p)) in *.
assert (UR : forall n0 (r : bv 5) v, Z.of_nat n0 = bv_unsigned r -> getr (ms_regs ms3) r = w64 v -> 0 <= v < 2 ^ 64 ->
   U E (SOff n0 0) = v).
{ intros n0 r v Hn0 Hr Hv. apply U_atom; [|exact Hv]. unfold E. rewrite (kr_env_reg _ _ _ n0 r Hn0), Hr. reflexivity. }
assert (U11 : U E (SOff 11 0) = p_nF cx) by (apply (UR 11%nat 11%bv); [reflexivity | exact R11 | lia]).
assert (U13 : U E (SOff 13 0) = kr_incl cx (p_q cx p)) by (apply (UR 13%nat 13%bv); [reflexivity | exact R13 | lia]).
assert (U14 : U E (SOff 14 0) = p_q cx p + 16) by (apply (UR 14%nat 14%bv); [reflexivity | exact R14 | lia]).
assert (U20 : U E (SOff 20 0) = kr_incl cx (p_q cx p)) by (apply (UR 20%nat 20%bv); [reflexivity | exact R20 | lia]).
assert (U12 : U E (SOff 12 0) =
  if PSN.tagged (p_sw cx) (p_F cx) (p_q cx p) then kr_incl cx (p_q cx p) - 4 else kr_incl cx (p_q cx p)).
{ rewrite <- HRES. apply (UR 12%nat 12%bv); [reflexivity | exact R12 |].
  rewrite HRES. pose proof (kr_tagged_incl (p_sw cx) (p_F cx) (p_q cx p)).
  destruct (PSN.tagged _ _ _); [specialize (H eq_refl); unfold kr_incl in *|]; lia. }
assert (UB1 : U E (SAlu ALU_ADD (SOff 13 0) (SOff 14 0)) = p_q cx p + 16 + kr_incl cx (p_q cx p)).
{ rewrite kb_add_U, U13, U14. rewrite zcanon_id by (unfold M64; lia). lia. }
assert (UX : forall j v, (j < 6)%nat -> nth j (kr_Xc cx fp p) (Z_to_bv 64 0) = w64 v -> 0 <= v < 2 ^ 64 ->
   U E (SOff (32 + j) 0) = v).
{ intros j v Hj Hx Hv. apply U_atom; [|exact Hv]. unfold E. rewrite (kr_env_x _ _ _ j ltac:(lia)). exact Hx. }
assert (U34 : U E (SExt true 32 (SOff 34 0)) = kb_sx32 (PSN.orig (p_sw cx) (p_F cx) (p_q cx p))).
{ apply kr_sext32_U; [|exact Hor]. apply (UX 2%nat); [lia | reflexivity | lia]. }
assert (U35 : U E (SExt true 32 (SOff 35 0)) = if PSN.tagged (p_sw cx) (p_F cx) (p_q cx p) then 1 else 0).
{ rewrite (kr_sext32_U E _ (if PSN.tagged (p_sw cx) (p_F cx) (p_q cx p) then 1 else 0)).
  - destruct (PSN.tagged _ _ _); reflexivity.
  - apply (UX 3%nat); [lia | reflexivity | destruct (PSN.tagged _ _ _); lia].
  - destruct (PSN.tagged _ _ _); lia. }
assert (U4 : 4 <= kr_incl cx (p_q cx p) ->
  U E (SAlu ALU_SRL (SAlu ALU_ADD (SAlu ALU_SLL (SOff 20 0) (SLit 32)) (SLit (-17179869184))) (SLit 32)) =
  kr_incl cx (p_q cx p) - 4) by (intros H4; apply (kb_subz2_U E (SOff 20 0) _ 4 _ eq_refl U20); lia).
assert (UDg : forall j, 0 <= j -> p_q cx p + j < p_nF cx -> U E (SData 0 j 1) = PSN.fb (p_F cx) (p_q cx p + j))
  by (intros j Hj0 Hj; unfold p_nF in Hj; apply (kr_U_fbE E (p_F cx) (p_q cx p) j eq_refl); lia).
pose proof (UDg 12 ltac:(lia) ltac:(lia)) as UD12. pose proof (UDg 13 ltac:(lia) ltac:(lia)) as UD13.
pose proof (UDg 14 ltac:(lia) ltac:(lia)) as UD14. pose proof (UDg 15 ltac:(lia) ltac:(lia)) as UD15.
assert (UO : forall sw : bool, p_sw cx = sw ->
  U E (if sw then kb_be32w (SData 0 12 1) (SData 0 13 1) (SData 0 14 1) (SData 0 15 1)
       else kb_le32w (SData 0 12 1) (SData 0 13 1) (SData 0 14 1) (SData 0 15 1)) =
  kb_sx32 (PSN.orig (p_sw cx) (p_F cx) (p_q cx p))).
{ intros sw Hs. unfold PSN.orig. rewrite Hs. destruct sw.
  - rewrite (kb_be32w_U E _ _ _ _ _ _ _ _ UD12 UD13 UD14 UD15) by apply kr_fb_range.
    rewrite kr_hw_be. replace (p_q cx p + 12 + 3) with (p_q cx p + 15) by lia.
    replace (p_q cx p + 12 + 2) with (p_q cx p + 14) by lia. replace (p_q cx p + 12 + 1) with (p_q cx p + 13) by lia.
    reflexivity.
  - rewrite (kb_le32w_U E _ _ _ _ _ _ _ _ UD12 UD13 UD14 UD15) by apply kr_fb_range.
    rewrite kr_hw_le. replace (p_q cx p + 12 + 3) with (p_q cx p + 15) by lia.
    replace (p_q cx p + 12 + 2) with (p_q cx p + 14) by lia. replace (p_q cx p + 12 + 1) with (p_q cx p + 13) by lia.
    reflexivity. }
destruct (Z.leb_spec 16 (kr_incl cx (p_q cx p))) as [HL | HL].
- pose proof (UDg 28 ltac:(lia) ltac:(lia)) as UD28. pose proof (UDg 29 ltac:(lia) ltac:(lia)) as UD29.
  destruct (kr_seat_now cx fp k acc ly3 S3 W3 ms3 md3 b h buf i p (ms_regs ms3) (ms_mem ms3) md3 PP_REC true true false false
    Hctx Hnow0 (fun _ => HL) (fun _ => R6) (fun H => ltac:(discriminate H))) as (HS & SHOK).
  rewrite <- (ms_of_body ms3 (BASE + PP_REC) (seg_rom SEGS) Hpc Hrv Hsv Hrom Hfreg Hfcsr) in HS.
  destruct (kr_swz cx) as [Hsw | Hsw]; rewrite Hsw in HS;
    [ pose proof (UO false ltac:(unfold p_sw; rewrite Hsw; reflexivity)) as UOx
    | pose proof (UO true ltac:(unfold p_sw; rewrite Hsw; reflexivity)) as UOx ];
    cbv iota in UOx; unfold kb_be32w in UOx; unfold kb_le32w in UOx; unfold kb_lo3 in UOx.
  all: change (kr_env (ms_regs ms3) (kr_Xc cx fp p) (kr_Dc cx p)) with E in HS, SHOK.
  all: do 10 (try (kr_step HS HJ SHOK ltac:(fun H => kr_normH E H ltac:(fun H2 =>
         rewrite ?UB1, ?U11, ?U12, ?U13, ?U14, ?U20, ?U34, ?U35, ?UOx, ?kr_sltu1_U, ?UD12, ?UD13, ?UD14, ?UD15,
           ?UD28, ?UD29 in H2; try (rewrite U4 in H2 by (unfold kr_incl in *; lia));
           repeat (rewrite U_lit in H2 by lia))))).
  all: prreg HS (1%bv : bv 5) Q1; prreg HS (10%bv : bv 5) Q10; prreg HS (11%bv : bv 5) Q11; prreg HS (12%bv : bv 5) Q12.
  all: lazymatch goal with |- SRr _ _ (mkCfg ?m ?mdx) _ =>
         assert (Hnow1 : kr_now cx fp k ly3 S3 W3 ms3 md3 (ms_regs m) (ms_mem m) mdx);
         [ apply (kr_now_keep _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hnow0 HJ);
           [ intros a _ _; f_equal; congruence
           | kr_keepS_run0 HS R23 R24 Hsw
           | rewrite ?(proj1 (wvb_fds_fs _ _ _)); reflexivity
           | rewrite ?(proj2 (wvb_fds_fs _ _ _)); reflexivity ]
         | ] end.
  all: pmkst HS.
  all: assert (Q10' : getr (ms_regs ms3) 22 = getr (ms_regs ms3) 22) by reflexivity.
  all: lazymatch type of Q1 with
       | _ = Z_to_bv 64 (_ + 1748) => change 1748 with PP_U in Q1
       | _ = Z_to_bv 64 (_ + 1624) => change 1624 with PP_T1 in Q1
       end.
  all: lazymatch type of Q1 with
       | _ = Z_to_bv 64 (_ + PP_U) =>
         lazymatch goal with Ht : PSN.tagged _ _ _ = false |- _ =>
         apply (kr_bcmp_now cx fp k acc ly3 S3 W3 ms3 md3 b h buf i p _ _ _ buf (b + p_q cx p + 16) (kr_incl cx (p_q cx p))
                  buf (p_bn cx) b (p_nF cx) PP_U (POST cx) Hctx Hnow1 Q1);
         [ unfold PP_U; lia | reflexivity
         | rewrite Q10; try unfold E; rewrite (kr_env_reg _ _ _ 22 22%bv eq_refl); exact R22
         | rewrite Q11; try unfold E; rewrite (kr_env_reg _ _ _ 26 26%bv eq_refl), R26; unfold w64;
           rewrite unsigned_lit_small by lia; f_equal; lia
         | rewrite Q12; try unfold E; rewrite (kr_env_reg _ _ _ 12 12%bv eq_refl), R12, HRES; try rewrite Ht; reflexivity
         | exact HIr
         | exact Hbuf_in | lia | pose proof (req_size_pos (p_bn cx) ltac:(lia)); unfold p_bn in *; lia
         | exact Hb_in | lia | lia
         | let j := fresh "j" in let Hj := fresh "Hj" in intros j Hj;
           pose proof (kr_cmp_ms3 cx fp k acc ly3 S3 W3 ms3 md3 b h buf i p 0 (Z.to_nat (p_q cx p + 16))
             (Z.to_nat (kr_incl cx (p_q cx p))) Hctx HK) as HC;
           replace (buf + j) with (buf + Z.of_nat 0 + j) by lia;
           replace (b + p_q cx p + 16 + j) with (b + Z.of_nat (Z.to_nat (p_q cx p + 16)) + j) by lia;
           apply HC;
           [ let j0 := fresh "j0" in let Hj0 := fresh "Hj0" in intros j0 Hj0; cbn [Nat.add]; unfold kr_incl in *;
             rewrite (kr_recb_untag (p_sw cx) (p_F cx) (p_q cx p) (Z_to_bv 8 0))
               by (unfold p_nF in HQfit; first [lia | exact Ht]); reflexivity
           | unfold PSN.rec_bytes; rewrite Ht; unfold kr_incl in *;
             rewrite (kr_raw_len (p_sw cx) (p_F cx) (p_q cx p)) by (unfold p_nF in HQfit; lia); lia
           | unfold kr_incl, p_nF in *; lia
           | unfold kr_incl in *; lia ]
         | let regs2 := fresh "regs2" in let mem2 := fresh "mem2" in let md2 := fresh "md2" in
           let Hnow2 := fresh "Hnow2" in let HR0 := fresh "HR0" in
           intros regs2 mem2 md2 Hnow2 HR0;
           exact (kr_untag POST n HKL2 cx fp k acc ly3 S3 W3 ms3 md3 b h buf i p
                    (mkst regs2 (Z_to_bv 64 (BASE + PP_U)) mem2 (seg_rom SEGS)) md2 Hctx Hmeas Hnow2 eq_refl HR0) ]
         end
       | _ = Z_to_bv 64 (_ + PP_T1) =>
         lazymatch goal with Ht : PSN.tagged _ _ _ = true |- _ =>
         let H18 := fresh "H18" in
         pose proof (kr_tagged_incl _ _ _ Ht) as H18;
         change (PSN.incl (p_sw cx) (p_F cx) (p_q cx p)) with (kr_incl cx (p_q cx p)) in H18;
         apply (kr_bcmp_now cx fp k acc ly3 S3 W3 ms3 md3 b h buf i p _ _ _ buf (b + p_q cx p + 16) 12
                  buf (p_bn cx) b (p_nF cx) PP_T1 (POST cx) Hctx Hnow1 Q1);
         [ unfold PP_T1; lia | reflexivity
         | rewrite Q10; try unfold E; rewrite (kr_env_reg _ _ _ 22 22%bv eq_refl); exact R22
         | rewrite Q11; try unfold E; rewrite (kr_env_reg _ _ _ 26 26%bv eq_refl), R26; unfold w64;
           rewrite unsigned_lit_small by lia; f_equal; lia
         | rewrite Q12; reflexivity
         | lia
         | exact Hbuf_in | lia | pose proof (req_size_pos (p_bn cx) ltac:(lia)); unfold p_bn in *; lia
         | exact Hb_in | lia | lia
         | let j := fresh "j" in let Hj := fresh "Hj" in intros j Hj;
           pose proof (kr_cmp_ms3 cx fp k acc ly3 S3 W3 ms3 md3 b h buf i p 0 (Z.to_nat (p_q cx p + 16)) 12 Hctx HK) as HC;
           replace (buf + j) with (buf + Z.of_nat 0 + j) by lia;
           replace (b + p_q cx p + 16 + j) with (b + Z.of_nat (Z.to_nat (p_q cx p + 16)) + j) by lia;
           apply HC;
           [ let j0 := fresh "j0" in let Hj0 := fresh "Hj0" in intros j0 Hj0; cbn [Nat.add];
             rewrite (kr_recb_tag12 (p_sw cx) (p_F cx) (p_q cx p) (Z_to_bv 8 0))
               by (unfold p_nF, kr_incl in *; first [lia | exact Ht]); reflexivity
           | unfold p_nF, kr_incl in *;
             pose proof (kr_recb_len_tag (p_sw cx) (p_F cx) (p_q cx p) ltac:(lia) ltac:(lia) Ht); lia
           | unfold kr_incl, p_nF in *; lia
           | lia ]
         | let regs2 := fresh "regs2" in let mem2 := fresh "mem2" in let md2 := fresh "md2" in
           let Hnow2 := fresh "Hnow2" in let HR0 := fresh "HR0" in
           intros regs2 mem2 md2 Hnow2 HR0;
           exact (kr_tag1 POST n HKL2 cx fp k acc ly3 S3 W3 ms3 md3 b h buf i p
                    (mkst regs2 (Z_to_bv 64 (BASE + PP_T1)) mem2 (seg_rom SEGS)) md2 Hctx Hmeas Ht Hnow2 eq_refl HR0) ]
         end
       end.
- destruct (kr_seat_now cx fp k acc ly3 S3 W3 ms3 md3 b h buf i p (ms_regs ms3) (ms_mem ms3) md3 PP_REC false true false false
    Hctx Hnow0 (fun H => ltac:(discriminate H)) (fun _ => R6) (fun H => ltac:(discriminate H))) as (HS & SHOK).
  rewrite <- (ms_of_body ms3 (BASE + PP_REC) (seg_rom SEGS) Hpc Hrv Hsv Hrom Hfreg Hfcsr) in HS.
  destruct (kr_swz cx) as [Hsw | Hsw]; rewrite Hsw in HS;
    [ pose proof (UO false ltac:(unfold p_sw; rewrite Hsw; reflexivity)) as UOx
    | pose proof (UO true ltac:(unfold p_sw; rewrite Hsw; reflexivity)) as UOx ];
    cbv iota in UOx; unfold kb_be32w in UOx; unfold kb_le32w in UOx; unfold kb_lo3 in UOx.
  all: change (kr_env (ms_regs ms3) (kr_Xc cx fp p) (kr_Dc cx p)) with E in HS, SHOK.
  all: do 10 (try (kr_step HS HJ SHOK ltac:(fun H => kr_normH E H ltac:(fun H2 =>
         rewrite ?UB1, ?U11, ?U12, ?U13, ?U14, ?U20, ?U34, ?U35, ?UOx, ?kr_sltu1_U, ?UD12, ?UD13, ?UD14, ?UD15 in H2;
         try (rewrite U4 in H2 by (unfold kr_incl in *; lia));
         repeat (rewrite U_lit in H2 by lia))))).
  all: prreg HS (1%bv : bv 5) Q1; prreg HS (10%bv : bv 5) Q10; prreg HS (11%bv : bv 5) Q11; prreg HS (12%bv : bv 5) Q12.
  all: lazymatch goal with |- SRr _ _ (mkCfg ?m ?mdx) _ =>
         assert (Hnow1 : kr_now cx fp k ly3 S3 W3 ms3 md3 (ms_regs m) (ms_mem m) mdx);
         [ apply (kr_now_keep _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hnow0 HJ);
           [ intros a _ _; f_equal; congruence
           | kr_keepS_run0 HS R23 R24 Hsw
           | rewrite ?(proj1 (wvb_fds_fs _ _ _)); reflexivity
           | rewrite ?(proj2 (wvb_fds_fs _ _ _)); reflexivity ]
         | ] end.
  all: pmkst HS.
  all: assert (Q10' : getr (ms_regs ms3) 22 = getr (ms_regs ms3) 22) by reflexivity.
  all: lazymatch type of Q1 with
       | _ = Z_to_bv 64 (_ + 1748) => change 1748 with PP_U in Q1
       | _ = Z_to_bv 64 (_ + 1624) => change 1624 with PP_T1 in Q1
       end.
  all: lazymatch type of Q1 with
       | _ = Z_to_bv 64 (_ + PP_U) =>
         lazymatch goal with Ht : PSN.tagged _ _ _ = false |- _ =>
         apply (kr_bcmp_now cx fp k acc ly3 S3 W3 ms3 md3 b h buf i p _ _ _ buf (b + p_q cx p + 16) (kr_incl cx (p_q cx p))
                  buf (p_bn cx) b (p_nF cx) PP_U (POST cx) Hctx Hnow1 Q1);
         [ unfold PP_U; lia | reflexivity
         | rewrite Q10; try unfold E; rewrite (kr_env_reg _ _ _ 22 22%bv eq_refl); exact R22
         | rewrite Q11; try unfold E; rewrite (kr_env_reg _ _ _ 26 26%bv eq_refl), R26; unfold w64;
           rewrite unsigned_lit_small by lia; f_equal; lia
         | rewrite Q12; try unfold E; rewrite (kr_env_reg _ _ _ 12 12%bv eq_refl), R12, HRES; try rewrite Ht; reflexivity
         | exact HIr
         | exact Hbuf_in | lia | pose proof (req_size_pos (p_bn cx) ltac:(lia)); unfold p_bn in *; lia
         | exact Hb_in | lia | lia
         | let j := fresh "j" in let Hj := fresh "Hj" in intros j Hj;
           pose proof (kr_cmp_ms3 cx fp k acc ly3 S3 W3 ms3 md3 b h buf i p 0 (Z.to_nat (p_q cx p + 16))
             (Z.to_nat (kr_incl cx (p_q cx p))) Hctx HK) as HC;
           replace (buf + j) with (buf + Z.of_nat 0 + j) by lia;
           replace (b + p_q cx p + 16 + j) with (b + Z.of_nat (Z.to_nat (p_q cx p + 16)) + j) by lia;
           apply HC;
           [ let j0 := fresh "j0" in let Hj0 := fresh "Hj0" in intros j0 Hj0; cbn [Nat.add]; unfold kr_incl in *;
             rewrite (kr_recb_untag (p_sw cx) (p_F cx) (p_q cx p) (Z_to_bv 8 0))
               by (unfold p_nF in HQfit; first [lia | exact Ht]); reflexivity
           | unfold PSN.rec_bytes; rewrite Ht; unfold kr_incl in *;
             rewrite (kr_raw_len (p_sw cx) (p_F cx) (p_q cx p)) by (unfold p_nF in HQfit; lia); lia
           | unfold kr_incl, p_nF in *; lia
           | unfold kr_incl in *; lia ]
         | let regs2 := fresh "regs2" in let mem2 := fresh "mem2" in let md2 := fresh "md2" in
           let Hnow2 := fresh "Hnow2" in let HR0 := fresh "HR0" in
           intros regs2 mem2 md2 Hnow2 HR0;
           exact (kr_untag POST n HKL2 cx fp k acc ly3 S3 W3 ms3 md3 b h buf i p
                    (mkst regs2 (Z_to_bv 64 (BASE + PP_U)) mem2 (seg_rom SEGS)) md2 Hctx Hmeas Hnow2 eq_refl HR0) ]
         end
       | _ = Z_to_bv 64 (_ + PP_T1) =>
         lazymatch goal with Ht : PSN.tagged _ _ _ = true |- _ =>
         let H18 := fresh "H18" in
         pose proof (kr_tagged_incl _ _ _ Ht) as H18;
         change (PSN.incl (p_sw cx) (p_F cx) (p_q cx p)) with (kr_incl cx (p_q cx p)) in H18;
         apply (kr_bcmp_now cx fp k acc ly3 S3 W3 ms3 md3 b h buf i p _ _ _ buf (b + p_q cx p + 16) 12
                  buf (p_bn cx) b (p_nF cx) PP_T1 (POST cx) Hctx Hnow1 Q1);
         [ unfold PP_T1; lia | reflexivity
         | rewrite Q10; try unfold E; rewrite (kr_env_reg _ _ _ 22 22%bv eq_refl); exact R22
         | rewrite Q11; try unfold E; rewrite (kr_env_reg _ _ _ 26 26%bv eq_refl), R26; unfold w64;
           rewrite unsigned_lit_small by lia; f_equal; lia
         | rewrite Q12; reflexivity
         | lia
         | exact Hbuf_in | lia | pose proof (req_size_pos (p_bn cx) ltac:(lia)); unfold p_bn in *; lia
         | exact Hb_in | lia | lia
         | let j := fresh "j" in let Hj := fresh "Hj" in intros j Hj;
           pose proof (kr_cmp_ms3 cx fp k acc ly3 S3 W3 ms3 md3 b h buf i p 0 (Z.to_nat (p_q cx p + 16)) 12 Hctx HK) as HC;
           replace (buf + j) with (buf + Z.of_nat 0 + j) by lia;
           replace (b + p_q cx p + 16 + j) with (b + Z.of_nat (Z.to_nat (p_q cx p + 16)) + j) by lia;
           apply HC;
           [ let j0 := fresh "j0" in let Hj0 := fresh "Hj0" in intros j0 Hj0; cbn [Nat.add];
             rewrite (kr_recb_tag12 (p_sw cx) (p_F cx) (p_q cx p) (Z_to_bv 8 0))
               by (unfold p_nF, kr_incl in *; first [lia | exact Ht]); reflexivity
           | unfold p_nF, kr_incl in *;
             pose proof (kr_recb_len_tag (p_sw cx) (p_F cx) (p_q cx p) ltac:(lia) ltac:(lia) Ht); lia
           | unfold kr_incl, p_nF in *; lia
           | lia ]
         | let regs2 := fresh "regs2" in let mem2 := fresh "mem2" in let md2 := fresh "md2" in
           let Hnow2 := fresh "Hnow2" in let HR0 := fresh "HR0" in
           intros regs2 mem2 md2 Hnow2 HR0;
           exact (kr_tag1 POST n HKL2 cx fp k acc ly3 S3 W3 ms3 md3 b h buf i p
                    (mkst regs2 (Z_to_bv 64 (BASE + PP_T1)) mem2 (seg_rom SEGS)) md2 Hctx Hmeas Ht Hnow2 eq_refl HR0) ]
         end
       end.
Qed.

(* ---- the segment: from PP_KR through the skip loop and the record checks to PP_KL2 ---- *)
Theorem pe_KR : forall POST n, at_cut (GI_KL2 B MT KS) POST n -> at_cut (GI_KR B MT KS) POST (S n).
Proof.
  intros POST n HKL2.
  pose proof (kr_rec POST n HKL2) as HREC.
  intros cx fp k acc ly3 S3 W3 ms3 md3 HB HJ HFR HMO HG Hmeas.
  apply kr_body_GI in HG as (b & h & buf & i & p & e & HKB).
  (* the skip loop's own induction, on |F| - e *)
  assert (IND : forall m (ms : machine_state) md e',
    (Z.to_nat (p_nF cx - e') <= m)%nat ->
    ajournal_gx SEGS B pe_G 0 [] LLVMF_STK (spZ (c_regs cx)) [sink_token] (c_ly cx) (c_S cx) (c_W cx)
      (c_mem cx) (c_md cx) [(PE_CID, fp)] ly3 S3 W3 (ms_mem ms) md k ->
    kr_body cx fp k acc ly3 S3 W3 ms md b h buf i p e' ->
    (Z.to_nat (p_nF cx - e') <= S n)%nat ->
    SRr SEGS W3 (mkCfg ms md) (POST cx)).
  { intros m. induction m as [m IHm] using lt_wf_ind.
    intros ms md e' Hm HJ' HKB' Hle.
    apply (kr_skip POST n HREC cx fp k acc ly3 S3 W3 ms md b h buf i p e' HB HJ' HFR HMO HKB' Hle).
    intros ms' md' e'' HJ'' HKB'' Hlt.
    pose proof HKB'' as (_ & _ & _ & _ & _ & _ & _ & _ & _ & He16'' & _).
    apply (IHm (Z.to_nat (p_nF cx - e'')) ltac:(lia) ms' md' e'' ltac:(lia) HJ'' HKB''). lia. }
  pose proof HKB as (_ & _ & _ & _ & _ & _ & _ & Hpe & _ & He16 & _ & _ & _ & _ & R18 & _).
  assert (Hm0 : hw_meas cx ms3 = Z.to_nat (p_nF cx - e)).
  { unfold hw_meas, hw_pos. rewrite R18. rewrite h_w64_unsigned by (pose proof (p_sizes cx); lia). reflexivity. }
  apply (IND (Z.to_nat (p_nF cx - e)) ms3 md3 e ltac:(lia) HJ HKB). lia.
Qed.

End c.
End b.
End a.
