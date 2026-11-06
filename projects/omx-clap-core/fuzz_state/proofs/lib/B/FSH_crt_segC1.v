(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Rares Buhai, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YN0j.v, with its module paths changed. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_boxreg/lib/Reusable/YN0j.v, with its module paths and module names changed; 546 of its 584 lines of code are new or changed and 260 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_state/lib/A/FSH_crt_segC.v, with its module names changed; 1538 of its 1613 lines of code are new or changed and 509 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_state/lib/A/FSH_crt_segC2.v, with its module paths and module names changed; 1534 of its 1691 lines of code are new or changed and 1456 lines of the source are left out. *)
(* check_round_trip 0x81b9c (fuzz_state.c:278-314 with round_trip_document fs.c:229-264 inlined), fs.asan-ubsan (image
   tfibsegs = lib/B/YB1v.v, the pinned fuzz_state.asan-ubsan sha256
   5ac5ce0954f87e2d050c481b7b0599cfd55ef554eadc008e51491f44c053d204): the B twin of lane C1 of the ASan walk of
   lib/B/FSH_Fn_crt.v check_round_trip_spec, segments 20-24, from the return of pj_set at 0x82304 (0x82308,
   FSH_crt_base.crt_INV_821ac) to the return of pj_set at 0x82370 (0x82374, FSH_crt_base.crt_INV_82218):
     20  0x82308..0x82318  pj_string (&v, "preset" 0x20f80)            v = s11 = F + 0xe0 (A: s6)
     21  0x8231c..0x82330  pj_set (&state, "context" 0x20fa0, &v)       state = s7 = F + 0x80
     22  0x82334..0x82340  pj_string (&v, text)                         text = s2 (encode's block)
     23  0x82344..0x82358  pj_set (&state, "bytes" 0x20fc0, &v)
     24  0x8235c..0x82370  pj_set (&doc, "state" 0x20f00, &state)       doc = F + 0x20 from slot 0x38 (A: s10)
   rule 24: proves no function (kind: segment lemma of check_round_trip's walk, PORTED from 27728fda52c lib/A/FSH_crt_segC1.v)
   Port source: a working branch 27728fda52c proofs/omx-clap-core/fuzz_state/lib/A/FSH_crt_segC1.v (blob
   d29d532641a, over S0 + A base v25 / site v24 e377e99a5c4), CTX-free, itself PORTED from a working branch
   d25a984c903 proofs/omx-clap-core/fuzz_state/lib/A/Prog/check_round_trip_sd10.v .. check_round_trip_sd14.v (the steps
   st10 .. st14 across the stage cuts St10 .. St15 of check_round_trip_stdefs.v :375-439) and check_round_trip_sdglue.v
   (the footprint / keep lemmas), restated in the S0 forms (checker a Theorem Labs lane, CONFIRM 2026-10-29 04:3xZ, on the
   lane head (internal path) lines 6-21). Same Definition / Lemma names and
   statement shapes as the A file; every pc, return address, callee address and register fact RE-MEASURED on B
   (capstone over the pinned fs.asan-ubsan, (internal path), crt.calls.tsv rows 22-26)
   and mapped from A by instruction meaning. Requires lib/B/FSH_crt_base.v (v25), lib/B/FSH_crt_site.v (v24) and
   lib/B/FSH_crt_segC.v. A new file: no licence lines.

   A name -> A pc -> B pc (names keep their A form, content is B's):
     crt_INV_821ac       0x821ac -> 0x82308   (lane entry, B base)    crt_INV_82218   0x82218 -> 0x82374 (lane exit, B base)
     crtC1_INV_1c0       0x821c0 -> 0x8231c   crtC1_INV_1d8   0x821d8 -> 0x82334   crtC1_INV_1e8   0x821e8 -> 0x82344
     crtC1_INV_200       0x82200 -> 0x8235c
     crtC1_site_1ac / crtC1_hcall_1ac  pj_string 0x83be4 -> 0x83e58 at 0x821bc -> 0x82318, ra 0x821c0 -> 0x8231c
     crtC1_site_1c0 / crtC1_hcall_1c0  pj_set    0x838e8 -> 0x83adc at 0x821d4 -> 0x82330, ra 0x821d8 -> 0x82334
     crtC1_site_1d8 / crtC1_hcall_1d8  pj_string 0x83be4 -> 0x83e58 at 0x821e4 -> 0x82340, ra 0x821e8 -> 0x82344
     crtC1_site_1e8 / crtC1_hcall_1e8  pj_set    0x838e8 -> 0x83adc at 0x821fc -> 0x82358, ra 0x82200 -> 0x8235c
     crtC1_site_200 / crtC1_hcall_200  pj_set    0x838e8 -> 0x83adc at 0x82214 -> 0x82370, ra 0x82218 -> 0x82374
     crtC1_pjset_call                  pj_set's entry 0x838e8 -> 0x83adc
   B register allocation differs from A's in this lane (B base crt_INV_821ac / crt_INV_82218): v = s11 (atom 27; A: s6,
   atom 22), s6 = F + 0x1c0 (atom 22; A: none), s3 = F (atom 19; A: none), and the document's address F + 0x20 is NOT a
   register (A: s10, atom 26) - segment 24 loads it from slot 0x38 (crt_cs1: SOff 47 0x20, atom 47 = F, FSH_crt_base
   crt_E_F), and F + 0x1a0 is slot 0x28, not a register (A: s11, atom 27). So crtC1_corex's ten register conjuncts are,
   in A's positions, 10 18 20 21 27 23 24 25 22 19 (A: 10 18 20 21 22 23 24 25 26 27), and crtC1_hcall_200 reads pj_set's
   obj from atom 47 (crtC1_doc_arg below).
   The segment step is FSH_crt_site.crt_seg_call_br (the generic call crossing, with a generic callee post and the
   leading `bnez a0` of every pj_* return). The keeps across a call are FSW_rd.v's (rtree_kept_call, pobj_kept_call,
   fs_rblock_kept_call, cstr_ok_kept_call) and the byte keeps below. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00 YI0n.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YI16 YK06 YM05 YG0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B Require Import YB1v YB1w.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require Import FSupoison FSupoisonU FSH_YC20 FSH_Gen.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B Require Import
FSH_Base FSH_Rt FSPstat FSW_K FSW_ret FSW_K3 FSH_Fn_reader
FSH_Fn_writer FSH_Fn_crt FSW_frame FSW_frame3 FSW_rres FSW_crt_tbl FSW_strkit FSW_rd FSH_crt_base FSH_crt_site
FSH_crt_segC.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B Require YE2k YF0x.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Prog Require PjStruct ReaderRes WriterSpecFacts.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
(* SINK GUARD: a SUCCESS here (the build errors naming this line) means a wrong sink instance resolved. *)
Fail Definition probe_SK : Reusable.YI16.sink_head := _.
Fail Definition probe_SH : Reusable.YI14.sink_syms := _.


(* ================= the five call sites =================
   The runs are FSH_crt_segC.v's crtC_br_<r> / crtC_run_<r> (from FSH_crt_site.crt_ss2 at each pj_* return: the
   `bnez a0` to the trap tail 0x824e4 (A: 0x824b8), then on the not-taken arm, a0 = 0, store-free to the next callee's
   entry). What each call-site state holds, read off the engine's answers (B: v is atom 27, A's 22; segment 24's obj is
   slot 0x38's SOff 47 0x20, A's atom 26): *)
Lemma crtC1_site_1ac : crt_site crtC_sb_1ac crtC_sc_1ac 0x83e58 0x8231c /\
  sr_get (ss_regs crtC_sc_1ac) 10%bv = SOff 27 0 /\ sr_get (ss_regs crtC_sc_1ac) 11%bv = SLit 0x20f80.
Proof. unfold crt_site, crt_csite. repeat split; vm_compute; reflexivity. Qed.
Lemma crtC1_site_1c0 : crt_site crtC_sb_1c0 crtC_sc_1c0 0x83adc 0x82334 /\
  sr_get (ss_regs crtC_sc_1c0) 10%bv = SOff 23 0 /\ sr_get (ss_regs crtC_sc_1c0) 11%bv = SLit 0x20fa0 /\
  sr_get (ss_regs crtC_sc_1c0) 12%bv = SOff 27 0.
Proof. unfold crt_site, crt_csite. repeat split; vm_compute; reflexivity. Qed.
Lemma crtC1_site_1d8 : crt_site crtC_sb_1d8 crtC_sc_1d8 0x83e58 0x82344 /\
  sr_get (ss_regs crtC_sc_1d8) 10%bv = SOff 27 0 /\ sr_get (ss_regs crtC_sc_1d8) 11%bv = SOff 18 0.
Proof. unfold crt_site, crt_csite. repeat split; vm_compute; reflexivity. Qed.
Lemma crtC1_site_1e8 : crt_site crtC_sb_1e8 crtC_sc_1e8 0x83adc 0x8235c /\
  sr_get (ss_regs crtC_sc_1e8) 10%bv = SOff 23 0 /\ sr_get (ss_regs crtC_sc_1e8) 11%bv = SLit 0x20fc0 /\
  sr_get (ss_regs crtC_sc_1e8) 12%bv = SOff 27 0.
Proof. unfold crt_site, crt_csite. repeat split; vm_compute; reflexivity. Qed.
Lemma crtC1_site_200 : crt_site crtC_sb_200 crtC_sc_200 0x83adc 0x82374 /\
  sr_get (ss_regs crtC_sc_200) 10%bv = SOff 47 0x20 /\ sr_get (ss_regs crtC_sc_200) 11%bv = SLit 0x20f00 /\
  sr_get (ss_regs crtC_sc_200) 12%bv = SOff 23 0.
Proof. unfold crt_site, crt_csite. repeat split; vm_compute; reflexivity. Qed.
Lemma crtC1_ssave_all : crt_ssave crtC_sc_1ac /\ crt_ssave crtC_sc_1c0 /\ crt_ssave crtC_sc_1d8 /\
  crt_ssave crtC_sc_1e8 /\ crt_ssave crtC_sc_200.
Proof. repeat split; apply crt_ssave_dec; vm_compute; reflexivity. Qed.


(* ================= byte keeps: across a program call and across a store-free run ================= *)
Section zc1k. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable SK : YI16.sink_head.
Variable B : asyms.

(* ---- across a PROGRAM call (the callee's journal, FSW_rd.v pobj_kept_call's hypotheses): a byte of a block or fake
   frame live before, off FP1, is kept in the restricted memory (fsw_journal_kept_byte) ---- *)
Lemma crtC1_kept_mbyte : forall STK1 sp1 FP1 lyc Sc Uc (W : world tfibsegs) memc mdc ly' S' U' W' mem' md' kc a,
  ajournal tfibsegs B STK1 sp1 FP1 lyc Sc W (unpoison Uc memc) mdc [] ly' S' W' (unpoison U' mem') md' kc ->
  ARU tfibsegs B lyc Sc Uc W memc mdc -> upoison_ok B ly' S' U' -> upoisoned tfibsegs W' mem' U' ->
  ((exists p n, In (p, n) (ablocks B lyc Sc) /\ p <= a < p + req_size n) \/
   (exists cid pos, In (cid, pos) (frames Sc) /\ frame_addr lyc cid pos <= a < frame_addr lyc cid pos + fs_frame_bytes cid)) ->
  ~ inFP FP1 a ->
  mbyte tfibsegs (mrestrict (w_H W') mem') a = mbyte tfibsegs (mrestrict (w_H W) memc) a.
Proof.
intros STK1 sp1 FP1 lyc Sc Uc W memc mdc ly' S' U' W' mem' md' kc a HJ HU HO' HP' HL Hf.
unfold mbyte.
rewrite (proj2 (fsw_journal_kept_byte B STK1 sp1 FP1 lyc Sc Uc W memc mdc ly' S' U' W' mem' md' kc a HJ HU HO' HP' HL Hf)).
reflexivity.
Qed.
Lemma crtC1_kept_word : forall STK1 sp1 FP1 lyc Sc Uc (W : world tfibsegs) memc mdc ly' S' U' W' mem' md' kc (x : word),
  ajournal tfibsegs B STK1 sp1 FP1 lyc Sc W (unpoison Uc memc) mdc [] ly' S' W' (unpoison U' mem') md' kc ->
  ARU tfibsegs B lyc Sc Uc W memc mdc -> upoison_ok B ly' S' U' -> upoisoned tfibsegs W' mem' U' ->
  ((exists p n, In (p, n) (ablocks B lyc Sc) /\ p <= bv_unsigned x < p + req_size n) \/
   (exists cid pos, In (cid, pos) (frames Sc) /\
      frame_addr lyc cid pos <= bv_unsigned x < frame_addr lyc cid pos + fs_frame_bytes cid)) ->
  ~ inFP FP1 (bv_unsigned x) ->
  mrestrict (w_H W') mem' x = mrestrict (w_H W) memc x.
Proof.
intros STK1 sp1 FP1 lyc Sc Uc W memc mdc ly' S' U' W' mem' md' kc x HJ HU HO' HP' HL Hf.
assert (Ex : x = Z_to_bv 64 (bv_unsigned x)) by (symmetry; apply Z_to_bv_bv_unsigned).
rewrite Ex.
exact (proj2 (fsw_journal_kept_byte B STK1 sp1 FP1 lyc Sc Uc W memc mdc ly' S' U' W' mem' md' kc (bv_unsigned x)
  HJ HU HO' HP' HL Hf)).
Qed.

(* (1) a byte window *)
Lemma crtC1_zbytes_kept_call : forall STK1 sp1 FP1 lyc Sc Uc (W : world tfibsegs) memc mdc ly' S' U' W' mem' md' kc q l,
  ajournal tfibsegs B STK1 sp1 FP1 lyc Sc W (unpoison Uc memc) mdc [] ly' S' W' (unpoison U' mem') md' kc ->
  ARU tfibsegs B lyc Sc Uc W memc mdc -> upoison_ok B ly' S' U' -> upoisoned tfibsegs W' mem' U' ->
  (forall a, q <= a < q + Z.of_nat (length l) ->
    ((exists p n, In (p, n) (ablocks B lyc Sc) /\ p <= a < p + req_size n) \/
     (exists cid pos, In (cid, pos) (frames Sc) /\ frame_addr lyc cid pos <= a < frame_addr lyc cid pos + fs_frame_bytes cid)) /\
    ~ inFP FP1 a) ->
  zbytes_at tfibsegs W memc q l -> zbytes_at tfibsegs W' mem' q l.
Proof.
intros STK1 sp1 FP1 lyc Sc Uc W memc mdc ly' S' U' W' mem' md' kc q l HJ HU HO' HP' HF HZ.
unfold zbytes_at in *.
apply (garr8_frame tfibsegs (mrestrict (w_H W) memc) (mrestrict (w_H W') mem') q l HZ).
intros a Ha. destruct (HF a Ha) as (HL & Hf).
exact (crtC1_kept_mbyte STK1 sp1 FP1 lyc Sc Uc W memc mdc ly' S' U' W' mem' md' kc a HJ HU HO' HP' HL Hf).
Qed.

(* (2) a little-endian value *)
Lemma crtC1_val_mem_kept_call : forall STK1 sp1 FP1 lyc Sc Uc (W : world tfibsegs) memc mdc ly' S' U' W' mem' md' kc q n v,
  ajournal tfibsegs B STK1 sp1 FP1 lyc Sc W (unpoison Uc memc) mdc [] ly' S' W' (unpoison U' mem') md' kc ->
  ARU tfibsegs B lyc Sc Uc W memc mdc -> upoison_ok B ly' S' U' -> upoisoned tfibsegs W' mem' U' ->
  (forall a, q <= a < q + Z.of_nat n ->
    ((exists b k, In (b, k) (ablocks B lyc Sc) /\ b <= a < b + req_size k) \/
     (exists cid pos, In (cid, pos) (frames Sc) /\ frame_addr lyc cid pos <= a < frame_addr lyc cid pos + fs_frame_bytes cid)) /\
    ~ inFP FP1 a) ->
  val_mem tfibsegs (mrestrict (w_H W) memc) q n v -> val_mem tfibsegs (mrestrict (w_H W') mem') q n v.
Proof.
intros STK1 sp1 FP1 lyc Sc Uc W memc mdc ly' S' U' W' mem' md' kc q n v HJ HU HO' HP' HF Hv k Hk.
destruct (HF (q + Z.of_nat k) ltac:(lia)) as (HL & Hf).
rewrite (crtC1_kept_mbyte STK1 sp1 FP1 lyc Sc Uc W memc mdc ly' S' U' W' mem' md' kc (q + Z.of_nat k) HJ HU HO' HP' HL Hf).
exact (Hv k Hk).
Qed.

(* (3) a zeroed pj object *)
Lemma crtC1_pj_zero_kept_call : forall STK1 sp1 FP1 lyc Sc Uc (W : world tfibsegs) memc mdc ly' S' U' W' mem' md' kc o,
  ajournal tfibsegs B STK1 sp1 FP1 lyc Sc W (unpoison Uc memc) mdc [] ly' S' W' (unpoison U' mem') md' kc ->
  ARU tfibsegs B lyc Sc Uc W memc mdc -> upoison_ok B ly' S' U' -> upoisoned tfibsegs W' mem' U' ->
  (forall a, o <= a < o + 56 ->
    ((exists p n, In (p, n) (ablocks B lyc Sc) /\ p <= a < p + req_size n) \/
     (exists cid pos, In (cid, pos) (frames Sc) /\ frame_addr lyc cid pos <= a < frame_addr lyc cid pos + fs_frame_bytes cid)) /\
    ~ inFP FP1 a) ->
  PjStruct.pj_zero tfibsegs (mrestrict (w_H W) memc) o -> PjStruct.pj_zero tfibsegs (mrestrict (w_H W') mem') o.
Proof.
intros STK1 sp1 FP1 lyc Sc Uc W memc mdc ly' S' U' W' mem' md' kc o HJ HU HO' HP' HF ((H8 & Hs) & Hb).
assert (E : forall x : word, o <= bv_unsigned x < o + 56 -> mrestrict (w_H W') mem' x = mrestrict (w_H W) memc x).
{ intros x Hx. destruct (HF (bv_unsigned x) Hx) as (HL & Hf).
  exact (crtC1_kept_word STK1 sp1 FP1 lyc Sc Uc W memc mdc ly' S' U' W' mem' md' kc x HJ HU HO' HP' HL Hf). }
split; [split; [exact H8 | exact (PjStruct.pj_stk_eq tfibsegs _ _ o (o + 56) Hs E)]|].
apply (PjStruct.pj_bytes_eq tfibsegs _ _ o _ Hb). intros x Hx. apply E.
rewrite repeat_length in Hx. change (Z.of_nat 56) with 56 in Hx. exact Hx.
Qed.

(* (4) a pj object header *)
Lemma crtC1_pj_hdr_kept_call : forall STK1 sp1 FP1 lyc Sc Uc (W : world tfibsegs) memc mdc ly' S' U' W' mem' md' kc
    o ty num str kids keys n cap,
  ajournal tfibsegs B STK1 sp1 FP1 lyc Sc W (unpoison Uc memc) mdc [] ly' S' W' (unpoison U' mem') md' kc ->
  ARU tfibsegs B lyc Sc Uc W memc mdc -> upoison_ok B ly' S' U' -> upoisoned tfibsegs W' mem' U' ->
  (forall a, o <= a < o + 56 ->
    ((exists b k, In (b, k) (ablocks B lyc Sc) /\ b <= a < b + req_size k) \/
     (exists cid pos, In (cid, pos) (frames Sc) /\ frame_addr lyc cid pos <= a < frame_addr lyc cid pos + fs_frame_bytes cid)) /\
    ~ inFP FP1 a) ->
  PjStruct.pj_hdr tfibsegs (mrestrict (w_H W) memc) o ty num str kids keys n cap ->
  PjStruct.pj_hdr tfibsegs (mrestrict (w_H W') mem') o ty num str kids keys n cap.
Proof.
intros STK1 sp1 FP1 lyc Sc Uc W memc mdc ly' S' U' W' mem' md' kc o ty num str kids keys n cap HJ HU HO' HP' HF HH.
apply (PjStruct.pj_hdr_eq tfibsegs _ _ o ty num str kids keys n cap HH).
intros x Hx. destruct (HF (bv_unsigned x) Hx) as (HL & Hf).
exact (crtC1_kept_word STK1 sp1 FP1 lyc Sc Uc W memc mdc ly' S' U' W' mem' md' kc x HJ HU HO' HP' HL Hf).
Qed.

(* (5) a fake-frame range's addressability: each byte's raw shadow byte is kept (fsw_journal_kept_shadow, frame arm); it
   is in no Uc range, since a Uc shadow byte reads 247 (upoisoned) and 247 is no saddr_ok value (pobj_kept_call's RA) *)
Lemma crtC1_raddr_kept_call : forall STK1 sp1 FP1 lyc Sc Uc (W : world tfibsegs) memc mdc ly' S' U' W' mem' md' kc q n,
  ajournal tfibsegs B STK1 sp1 FP1 lyc Sc W (unpoison Uc memc) mdc [] ly' S' W' (unpoison U' mem') md' kc ->
  ARU tfibsegs B lyc Sc Uc W memc mdc -> upoison_ok B ly' S' U' -> upoisoned tfibsegs W' mem' U' ->
  (forall a, inFP FP1 a -> ~ (SHADOW_OFF <= a < SHADOW_OFF + 2 ^ 44)) -> FSupoisonU.fs_heads B ly' S' U' ->
  (forall a, q <= a < q + n -> exists cid pos, In (cid, pos) (frames Sc) /\
     frame_addr lyc cid pos <= a < frame_addr lyc cid pos + fs_frame_bytes cid) ->
  range_addressable (aview tfibsegs (w_H W) memc) SHADOW_OFF q n ->
  range_addressable (aview tfibsegs (w_H W') mem') SHADOW_OFF q n.
Proof.
intros STK1 sp1 FP1 lyc Sc Uc W memc mdc ly' S' U' W' mem' md' kc q n HJ HU HO' HP' HFsh HH HQ Hra x Hx.
pose proof HU as (_ & _ & HPUc).
destruct (Hra x Hx) as (sv & Esv & Hok). exists sv. split; [|exact Hok].
rewrite <- Esv. apply (fsw_journal_kept_shadow B STK1 sp1 FP1 lyc Sc Uc W memc mdc ly' S' U' W' mem' md' kc x HJ HU HO' HP' HFsh HH).
- right. exact (HQ x Hx).
- destruct (in_ush Uc (shadow_of_addr SHADOW_OFF x)) eqn:E; [|reflexivity]. exfalso.
  pose proof (HPUc _ E) as E247. rewrite Esv in E247. injection E247 as ->. unfold saddr_ok in Hok. lia.
Qed.

(* ---- (6) across same_below m m' alloc_ceiling (the run's stack writes lie above alloc_ceiling) ---- *)
Lemma crtC1_zbytes_below : forall (W : world tfibsegs) m m' q l, same_below m m' alloc_ceiling ->
  0 <= q -> q + Z.of_nat (length l) <= alloc_ceiling ->
  zbytes_at tfibsegs W m q l -> zbytes_at tfibsegs W m' q l.
Proof.
intros W m m' q l Hs H0 H1 HZ. unfold zbytes_at in *.
apply (garr8_frame tfibsegs (mrestrict (w_H W) m) (mrestrict (w_H W) m') q l HZ).
intros a Ha. apply (mbyte_below (w_H W) m m' alloc_ceiling a Hs). lia.
Qed.
Lemma crtC1_pj_zero_below : forall (W : world tfibsegs) m m' o, same_below m m' alloc_ceiling ->
  0 <= o -> o + 56 <= alloc_ceiling ->
  PjStruct.pj_zero tfibsegs (mrestrict (w_H W) m) o -> PjStruct.pj_zero tfibsegs (mrestrict (w_H W) m') o.
Proof.
intros W m m' o Hs H0 H1 ((H8 & Hst) & Hb).
assert (E : forall x : word, o <= bv_unsigned x < o + 56 -> mrestrict (w_H W) m' x = mrestrict (w_H W) m x).
{ intros x Hx. apply (fsw_mrestrict_below (w_H W) m m' x Hs). lia. }
split; [split; [exact H8 | exact (PjStruct.pj_stk_eq tfibsegs _ _ o (o + 56) Hst E)]|].
apply (PjStruct.pj_bytes_eq tfibsegs _ _ o _ Hb). intros x Hx. apply E.
rewrite repeat_length in Hx. change (Z.of_nat 56) with 56 in Hx. exact Hx.
Qed.
Lemma crtC1_pj_hdr_below : forall (W : world tfibsegs) m m' o ty num str kids keys n cap, same_below m m' alloc_ceiling ->
  0 <= o -> o + 56 <= alloc_ceiling ->
  PjStruct.pj_hdr tfibsegs (mrestrict (w_H W) m) o ty num str kids keys n cap ->
  PjStruct.pj_hdr tfibsegs (mrestrict (w_H W) m') o ty num str kids keys n cap.
Proof.
intros W m m' o ty num str kids keys n cap Hs H0 H1 HH.
apply (PjStruct.pj_hdr_eq tfibsegs _ _ o ty num str kids keys n cap HH).
intros x Hx. apply (fsw_mrestrict_below (w_H W) m m' x Hs). lia.
Qed.
Lemma crtC1_rtree_below : forall ly S (W : world tfibsegs) mx md m m' v t D, AR tfibsegs B ly S W mx md ->
  same_below m m' alloc_ceiling -> 0 <= v -> v + 56 <= alloc_ceiling ->
  rtree tfibsegs B ly S W m v t D -> rtree tfibsegs B ly S W m' v t D.
Proof.
intros ly S W mx md m m' v t D HAR Hs H0 H1 HT. unfold rtree in *.
exact (rnode_below B ly S W mx md m m' D v t D HAR Hs H0 H1 HT).
Qed.

(* ---- (7) the head list FSupoisonU.fs_heads: grown by new heads of live blocks, and up to permutation ---- *)
Lemma crtC1_fs_heads_grow : forall ly S ly' S' U X, FSupoisonU.fs_heads B ly S U ->
  (forall b, In b (ablocks B ly S) -> In b (ablocks B ly' S')) ->
  (forall r, In r X -> snd r = 16 /\ exists m, In (fst r, m) (ablocks B ly' S') /\ 16 <= req_size m) ->
  FSupoisonU.fs_heads B ly' S' (U ++ X).
Proof.
intros ly S ly' S' U X HH Hb HX r Hr. apply in_app_or in Hr as [Hr|Hr]; [|exact (HX r Hr)].
destruct (HH r Hr) as (E & m & Hm & M). split; [exact E|]. exists m. split; [exact (Hb _ Hm) | exact M].
Qed.
Lemma crtC1_fs_heads_perm : forall ly S U V, Permutation U V -> FSupoisonU.fs_heads B ly S U -> FSupoisonU.fs_heads B ly S V.
Proof.
intros ly S U V HP HH r Hr. exact (HH r (Permutation_in r (Permutation_sym HP) Hr)).
Qed.

(* ---- (8) no head of U meets [p, p + len] when p is the body of a live block (p - HEAD, n + HEAD) with len < n: a head
   (q, 16) is the start of a live block (fs_heads), either the same block (its head [p - HEAD, p)) or one disjoint from
   it (AR's pairwise zdisjoint, the pattern of FSW_rd.v fsw_journal_kept_shadow) ---- *)
Lemma crtC1_heads_apart : forall ly S (W : world tfibsegs) mem md U p n len, AR tfibsegs B ly S W mem md ->
  FSupoisonU.fs_heads B ly S U -> In (p - HEAD, n + HEAD) (ablocks B ly S) -> 0 <= len -> len + 1 <= n ->
  forall r, In r U -> p + len + 1 <= fst r \/ fst r + snd r <= p.
Proof.
intros ly S W mem md U p n len HAR HH Hin Hl Hn [q sz] Hr.
pose proof (AR_laws_ok tfibsegs B) as LAWS.
destruct (HH (q, sz) Hr) as (E16 & m & Hm & M16). cbn [fst snd] in *. subst sz.
destruct (Z.eq_dec q (p - HEAD)) as [->|NE]; [unfold HEAD; right; lia|].
destruct (al_blocks tfibsegs B LAWS ly S W mem md q m HAR Hm) as (_ & _ & _ & _ & _ & PW & _).
assert (I1 : In (q, req_size m) (map (fun b => (fst b, req_size (snd b))) (ablocks B ly S)))
  by exact (in_map (fun b => (fst b, req_size (snd b))) _ (q, m) Hm).
assert (I2 : In (p - HEAD, req_size (n + HEAD)) (map (fun b => (fst b, req_size (snd b))) (ablocks B ly S)))
  by exact (in_map (fun b => (fst b, req_size (snd b))) _ (p - HEAD, n + HEAD) Hin).
pose proof (req_size_pos (n + HEAD) ltac:(unfold HEAD; lia)) as (_ & Hr2).
destruct (FSupoisonU.pairwise_In2 zdisjoint _ _ _ PW I1 I2 ltac:(intros E; injection E; intros _ E'; exact (NE E')))
  as [D|D]; unfold zdisjoint in D; cbn [fst snd] in D; unfold HEAD in *; lia.
Qed.
End zc1k.

(* ---- the cap of an object read back off its tree (pj_set's post gives the new object only as rtree, whose pj_node
   keeps cap existential): an object tree whose block list is, up to order, a 448-byte block, a 64-byte block and blocks
   of sizes not multiples of 56 has cap = 8 - pj_node's kids block (kids, 56 * cap) is in D when cap > 0, and cap = 0
   contradicts n = length ms >= 1 ---- *)
Section c1cap. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : asyms.
Lemma crtC1_cap8 : forall ly S (W : world tfibsegs) mem o ms D rest kb yb,
  rtree tfibsegs B ly S W mem o (PjTree.JObj ms) D -> (1 <= length ms)%nat ->
  Permutation D ((kb, 56 * 8) :: (yb, 8 * 8) :: rest) -> Forall (fun b => snd b mod 56 <> 0) rest ->
  exists num str kids keys,
    PjStruct.pj_hdr tfibsegs (mrestrict (w_H W) mem) o 6 num str kids keys (Z.of_nat (length ms)) 8 /\
    incl (ReaderRes.kids_blk kids 8 ++ ReaderRes.keys_blk 6 keys 8) D.
Proof.
  intros ly S W mem o ms D rest kb yb Ht Hl HP HF.
  destruct Ht as (Hn & _ & _). cbn [PjStruct.pj_node] in Hn.
  destruct Hn as (_ & _ & num & str & kids & keys & n & cap & Hh & _ & En & Hc & Hcap & Di & ED & _).
  cbn [PjTree.tag] in Hh.
  destruct Hcap as [(Hc0 & _ & _)|(Hc0 & _ & _)]; [lia|].
  assert (E0 : (cap =? 0) = false) by (apply Z.eqb_neq; lia).
  rewrite E0 in ED.
  assert (Hk : In (kids, 56 * cap) D) by (rewrite ED; left; reflexivity).
  assert (Hy : In (keys, 8 * cap) D) by (rewrite ED; right; left; reflexivity).
  assert (Ec : cap = 8).
  { pose proof (Permutation_in _ HP Hk) as Hk'.
    destruct Hk' as [Ek|[Ek|Ek]].
    - injection Ek as E1 E2. lia.
    - injection Ek as E1 E2. lia.
    - rewrite Forall_forall in HF. exfalso. apply (HF _ Ek). cbn [snd].
      rewrite Z.mul_comm. apply Z.mod_mul. lia. }
  subst cap n. exists num, str, kids, keys. split; [exact Hh|].
  change (ReaderRes.kids_blk kids 8 ++ ReaderRes.keys_blk 6 keys 8) with [(kids, 56 * 8); (keys, 8 * 8)].
  intros b Hb. destruct Hb as [<-|[<-|[]]]; assumption.
Qed.
End c1cap.

(* ================= budgets and block lists ================= *)
Section c1b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : asyms.
(* the decoded length: PORTED from lib/Prog/check_no_overread.v:125-139 (six_len, dec_len), over the same
   lib/Prog/WriterSpec.v b64_dec, names qualified *)
Lemma crtC1_six_len : forall six, (length (WriterSpec.six_bytes six) * 4 <= length six * 3)%nat.
Proof.
  fix IH 1. intros [|a [|b [|c [|e r]]]]; cbn [WriterSpec.six_bytes length]; try lia.
  specialize (IH r). lia.
Qed.
Lemma crtC1_dec_len : forall tb bs, WriterSpec.b64_dec tb = Some bs -> (length bs * 4 <= length tb * 3)%nat.
Proof.
  intros tb bs H. unfold WriterSpec.b64_dec in H.
  destruct (WriterSpec.b64_scan 0 [] tb) as [[six pad]|] eqn:E; [|discriminate].
  destruct ((pad <=? 2) && WriterSpec.six_tail_ok six); [|discriminate]. injection H as <-.
  destruct (WriterSpecFacts.scan_inv tb 0 [] six pad E) as [H1 _]. cbn [length] in H1.
  pose proof (crtC1_six_len six). lia.
Qed.
(* the prefix budgets at B 0x82374 (K_82218): K_* / CNT_* do not read cx, so once unfolded they are closed numerals *)
Lemma crtC1_K_le : forall cx, K_82218 cx <= EV_check_round_trip.
Proof. intros cx. unfold K_82218, K_821ac, K_82068. apply Z.leb_le. vm_compute. reflexivity. Qed.
Lemma crtC1_ticks_nonneg : forall cx,
  0 <= EV_pj_string /\ 0 <= rd_ev (pj_set_c.set_trace 1 8 7) /\ 0 <= rd_ev (pj_set_c.set_trace 2 8 5) /\
  0 <= K_821ac cx.
Proof.
  intros cx. unfold K_821ac, K_82068.
  refine (conj _ (conj _ (conj _ _))); apply Z.leb_le; vm_compute; reflexivity.
Qed.
Lemma crtC1_CNT_le : forall cx, CNT_82218 cx <= EV_check_round_trip.
Proof. intros cx. unfold CNT_82218, CNT_821ac, CNT_82068. apply Z.leb_le. vm_compute. reflexivity. Qed.
(* pj_set_c.set_trace n cap klen with n <> cap is the one key allocation [EAlloc (klen + 1)] *)
Lemma crtC1_trlen :
  Z.of_nat (length (pj_set_c.set_trace 1 8 7)) = 1 /\ Z.of_nat (length (pj_set_c.set_trace 2 8 5)) = 1 /\
  crt_trlen (pj_set_c.set_trace 1 8 7) = 1 /\ crt_trlen (pj_set_c.set_trace 2 8 5) = 1.
Proof. refine (conj _ (conj _ (conj _ _))); vm_compute; reflexivity. Qed.
(* LIVE_82218 under crt_base: the text is at most 3 * 2^20 bytes, the decoded bytes at most 3/4 of that and the
   re-encoded text es at most 4/3 of those (WriterSpecFacts.b64_enc_length); the closed rd_live terms are the pj_set
   traces' requests + HEAD. Worst case 14,943,598 < 2^25. *)
Lemma crtC1_LIVE_le : forall cx, crt_base B cx -> LIVE_82218 cx <= LIVE_check_round_trip.
Proof.
  intros cx HB. unfold crt_base in HB.
  destruct HB as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Htb & _ & _ & Hdec & _).
  pose proof (crtC1_dec_len _ _ Hdec) as Hl. unfold HState.zs in Hl. rewrite length_map in Hl.
  assert (HE : Z.of_nat (length (WriterSpec.b64_enc (c_bs cx))) = (Z.of_nat (length (c_bs cx)) + 2) / 3 * 4).
  { rewrite WriterSpecFacts.b64_enc_length. rewrite Nat2Z.inj_mul, Nat2Z.inj_div, Nat2Z.inj_add. reflexivity. }
  assert (X1 : rd_live (pj_set_c.set_trace 0 0 6) = 567) by (vm_compute; reflexivity).
  assert (X2 : rd_live (pj_set_c.set_trace 1 8 7) = 24) by (vm_compute; reflexivity).
  assert (X3 : rd_live (pj_set_c.set_trace 0 0 8) = 569) by (vm_compute; reflexivity).
  assert (X4 : rd_live (pj_set_c.set_trace 2 8 5) = 22) by (vm_compute; reflexivity).
  unfold LIVE_82218, LIVE_821ac, LIVE_82068, crt_len, crt_es, FSH_Fn_writer.enc_size, FSH_Fn_writer.dec_size.
  rewrite X1, X2, X3, X4, HE. unfold HEAD, LIVE_check_round_trip.
  Z.div_mod_to_equations. lia.
Qed.
Lemma crtC1_rd_heads_app : forall D1 D2, rd_heads (D1 ++ D2) = rd_heads D1 ++ rd_heads D2.
Proof. intros D1 D2. unfold rd_heads. apply map_app. Qed.
Lemma crtC1_rd_hblocks_app : forall D1 D2, rd_hblocks (D1 ++ D2) = rd_hblocks D1 ++ rd_hblocks D2.
Proof. intros D1 D2. unfold rd_hblocks. apply map_app. Qed.
(* each reader block (a, k) is the ASan block (a - HEAD, k + HEAD) *)
Lemma crtC1_bsum_rd_hblocks : forall D, YCbq.bsum (rd_hblocks D) = rd_sum D + HEAD * Z.of_nat (length D).
Proof.
  induction D as [|b D IH]; [reflexivity|].
  change (rd_hblocks (b :: D)) with ((fst b - HEAD, snd b + HEAD) :: rd_hblocks D).
  change (rd_sum (b :: D)) with (snd b + rd_sum D).
  rewrite YCbq.bsum_cons, IH. cbn [snd length]. rewrite Nat2Z.inj_succ. unfold HEAD. lia.
Qed.
(* blocks_bytes across a boundary whose block list is the entry's plus L plus the reader blocks of D
   (YCbq.blocks_bytes_bsum / bsum_perm / bsum_app) *)
Lemma crtC1_rd_sum_le : forall ly3 S3 ly0 S0 L D,
  Permutation (ablocks B ly3 S3) (ablocks B ly0 S0 ++ L ++ rd_hblocks D) ->
  blocks_bytes S3 = blocks_bytes S0 + YCbq.bsum L + rd_sum D + HEAD * Z.of_nat (length D).
Proof.
  intros ly3 S3 ly0 S0 L D HP.
  rewrite (YCbq.blocks_bytes_bsum B ly3 S3), (YCbq.blocks_bytes_bsum B ly0 S0), (YCbq.bsum_perm _ _ HP).
  rewrite !YCbq.bsum_app, crtC1_bsum_rd_hblocks. lia.
Qed.
End c1b.

(* ================= the inner boundaries of lane C1 =================
   St10 .. St14 of d25a984c903's check_round_trip_stdefs.v (:375-427) restated as S0 boundary invariants at the four
   inner return addresses (B 0x8231c / 0x82334 / 0x82344 / 0x8235c; A 0x821c0 / 0x821d8 / 0x821e8 / 0x82200).
   crtC1_corex is the part every boundary of the lane shares, B base crt_INV_821ac's and crt_INV_82218's own form with
   the trees' blocks collected in one list D (the order of D is free: it enters only through Permutation and rd_sum):
   the s-registers (B: s11 = v = atom 27, s6 = F + 0x1c0 = atom 22, s3 = F = atom 19 in the places A gives s6 = v = 22,
   s10 = doc = 26, s11 = F + 0x1a0 = 27), the block list and U, the text and decode blocks, the back object and the n
   cell, g_live's exact equation and the three prefix budgets. ---- *)
Definition crtC1_KC_1c0 (cx : crt_cx) : Z := K_821ac cx + EV_pj_string.
Definition crtC1_CNT_1c0 (cx : crt_cx) : Z := CNT_821ac cx + 1.
Definition crtC1_LIVE_1c0 (cx : crt_cx) : Z := LIVE_821ac cx + (7 + HEAD).
Definition crtC1_KC_1d8 (cx : crt_cx) : Z := crtC1_KC_1c0 cx + rd_ev (pj_set_c.set_trace 1 8 7).
Definition crtC1_CNT_1d8 (cx : crt_cx) : Z := crtC1_CNT_1c0 cx + crt_trlen (pj_set_c.set_trace 1 8 7).
Definition crtC1_LIVE_1d8 (cx : crt_cx) : Z := crtC1_LIVE_1c0 cx + rd_live (pj_set_c.set_trace 1 8 7).
Definition crtC1_KC_1e8 (cx : crt_cx) : Z := crtC1_KC_1d8 cx + EV_pj_string.
Definition crtC1_CNT_1e8 (cx : crt_cx) : Z := crtC1_CNT_1d8 cx + 1.
Definition crtC1_LIVE_1e8 (cx : crt_cx) : Z := crtC1_LIVE_1d8 cx + (Z.of_nat (length (crt_es cx)) + 1 + HEAD).
Definition crtC1_KC_200 (cx : crt_cx) : Z := crtC1_KC_1e8 cx + rd_ev (pj_set_c.set_trace 2 8 5).
Definition crtC1_CNT_200 (cx : crt_cx) : Z := crtC1_CNT_1e8 cx + crt_trlen (pj_set_c.set_trace 2 8 5).
Definition crtC1_LIVE_200 (cx : crt_cx) : Z := crtC1_LIVE_1e8 cx + rd_live (pj_set_c.set_trace 2 8 5).
(* the last pj_set closes the base's budgets *)
Lemma crtC1_K_last : forall cx, K_82218 cx = crtC1_KC_200 cx + rd_ev (pj_set_c.set_trace 2 8 5).
Proof. intros cx. unfold K_82218, crtC1_KC_200, crtC1_KC_1e8, crtC1_KC_1d8, crtC1_KC_1c0. lia. Qed.
Lemma crtC1_CNT_last : forall cx, CNT_82218 cx = crtC1_CNT_200 cx + crt_trlen (pj_set_c.set_trace 2 8 5).
Proof. intros cx. unfold CNT_82218, crtC1_CNT_200, crtC1_CNT_1e8, crtC1_CNT_1d8, crtC1_CNT_1c0. lia. Qed.
Lemma crtC1_LIVE_last : forall cx, LIVE_82218 cx = crtC1_LIVE_200 cx + rd_live (pj_set_c.set_trace 2 8 5).
Proof. intros cx. unfold LIVE_82218, crtC1_LIVE_200, crtC1_LIVE_1e8, crtC1_LIVE_1d8, crtC1_LIVE_1c0. lia. Qed.

Section inv. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : asyms.
Definition crtC1_corex (cx : crt_cx) (E : env) (k : Z) (ly3 : alayout) (S3 : astate) (U3 : list (Z * Z))
  (W3 : world tfibsegs) (mem : word -> option byte) (D : list (Z * Z)) (Kb CNTb LIVEb : Z)
  (same nsame dec live peak cnt : Z) : Prop :=
  let F := crt_F cx in let len := Z.of_nat (length (c_bs cx)) in let tb2 := WriterSpec.b64_enc (c_bs cx) in
  ew E 10 = Z_to_bv 64 0 /\ ew E 18 = Z_to_bv 64 (c_text cx) /\ ew E 20 = Z_to_bv 64 len /\
  ew E 21 = Z_to_bv 64 (c_bd cx) /\ ew E 27 = Z_to_bv 64 (F + 0xe0) /\ ew E 23 = Z_to_bv 64 (F + 0x80) /\
  ew E 24 = Z_to_bv 64 same /\ ew E 25 = Z_to_bv 64 dec /\
  ew E 22 = Z_to_bv 64 (F + 0x1c0) /\ ew E 19 = Z_to_bv 64 F /\
  Permutation (ablocks B ly3 S3)
    (ablocks B (c_ly cx) (c_S cx) ++
     [(c_text cx - HEAD, FSH_Fn_writer.enc_size len + HEAD); (c_want cx, FSH_Fn_writer.enc_size len);
      (same, nsame); (dec - HEAD, FSH_Fn_writer.dec_size tb2 + HEAD)] ++ rd_hblocks D) /\
  Permutation U3 (c_U cx ++ [(c_text cx - HEAD, HEAD); (dec - HEAD, HEAD)] ++ rd_heads D) /\
  FSupoisonU.fs_heads B ly3 S3 U3 /\
  fs_rblock tfibsegs B ly3 S3 W3 mem (c_text cx) (FSH_Fn_writer.enc_size len) /\
  zbytes_at tfibsegs W3 mem (c_text cx) (tb2 ++ [0]) /\ cstr_ok tfibsegs W3 mem (c_text cx) tb2 /\
  fs_rblock tfibsegs B ly3 S3 W3 mem dec (FSH_Fn_writer.dec_size tb2) /\
  zbytes_at tfibsegs W3 mem dec (c_bs cx) /\
  pobj tfibsegs B ly3 S3 W3 mem (F + 0x140) /\
  val_mem tfibsegs (mrestrict (w_H W3) mem) (F + 0x1a0) 8 0 /\
  range_addressable (aview tfibsegs (w_H W3) mem) SHADOW_OFF (F + 0x1a0) 8 /\
  fs_glob tfibsegs W3 mem live peak cnt SIZE_MAXZ /\
  live = c_live cx + FSH_Fn_writer.enc_size len + FSH_Fn_writer.dec_size tb2 + rd_sum D /\
  blocks_bytes S3 <= blocks_bytes (c_S cx) + LIVEb /\ c_cnt cx <= cnt <= c_cnt cx + CNTb /\ k <= Kb.
(* the document as segments 20-23 keep it: doc = F + 0x20 holds crt_doc8 with cap = 8 *)
Definition crtC1_doc (cx : crt_cx) (ly3 : alayout) (S3 : astate) (W3 : world tfibsegs) (mem : word -> option byte)
  (Ddoc : list (Z * Z)) : Prop :=
  rtree tfibsegs B ly3 S3 W3 mem (crt_F cx + 0x20) (PjTree.JObj check_round_trip_st8.crt_doc8) Ddoc /\
  (exists num str kids keys,
     PjStruct.pj_hdr tfibsegs (mrestrict (w_H W3) mem) (crt_F cx + 0x20) 6 num str kids keys 2 8) /\
  pobj tfibsegs B ly3 S3 W3 mem (crt_F cx + 0x20).
(* B 0x8231c (A 0x821c0), the return of pj_string (&v, "preset"): St10 with v = JStr V_PRESET on one fresh block *)
Definition crtC1_INV_1c0 : crt_inv :=
  fun cx E k ly3 S3 U3 W3 ms3 md3 =>
  let mem := ms_mem ms3 in let F := crt_F cx in
  exists Ddoc Dst a1 same nsame dec live peak cnt,
    crtC1_corex cx E k ly3 S3 U3 W3 mem (Ddoc ++ Dst ++ [(a1, 7)]) (crtC1_KC_1c0 cx) (crtC1_CNT_1c0 cx)
      (crtC1_LIVE_1c0 cx) same nsame dec live peak cnt /\
    crtC1_doc cx ly3 S3 W3 mem Ddoc /\
    rtree tfibsegs B ly3 S3 W3 mem (F + 0x80) (PjTree.JObj check_round_trip_stages_b.crt_s1) Dst /\
    (exists sk sy se sv, Permutation Dst [(sk, 56 * 8); (sy, 8 * 8); (se, 9); (sv, 7)]) /\
    pobj tfibsegs B ly3 S3 W3 mem (F + 0x80) /\
    rtree tfibsegs B ly3 S3 W3 mem (F + 0xe0) (PjTree.JStr check_round_trip_stages_b.V_PRESET) [(a1, 7)] /\
    pobj tfibsegs B ly3 S3 W3 mem (F + 0xe0).
(* B 0x82334 (A 0x821d8), the return of pj_set (&state, "context", &v): St11 -> St12, the state holds crt_s2, v is
   zeroed *)
Definition crtC1_INV_1d8 : crt_inv :=
  fun cx E k ly3 S3 U3 W3 ms3 md3 =>
  let mem := ms_mem ms3 in let F := crt_F cx in
  exists Ddoc Dst same nsame dec live peak cnt,
    crtC1_corex cx E k ly3 S3 U3 W3 mem (Ddoc ++ Dst) (crtC1_KC_1d8 cx) (crtC1_CNT_1d8 cx)
      (crtC1_LIVE_1d8 cx) same nsame dec live peak cnt /\
    crtC1_doc cx ly3 S3 W3 mem Ddoc /\
    rtree tfibsegs B ly3 S3 W3 mem (F + 0x80) (PjTree.JObj check_round_trip_stages_b.crt_s2) Dst /\
    (exists sk sy se sv sc sp,
       Permutation Dst [(sk, 56 * 8); (sy, 8 * 8); (se, 9); (sv, 7); (sc, 8); (sp, 7)]) /\
    pobj tfibsegs B ly3 S3 W3 mem (F + 0x80) /\
    PjStruct.pj_zero tfibsegs (mrestrict (w_H W3) mem) (F + 0xe0) /\ pobj tfibsegs B ly3 S3 W3 mem (F + 0xe0).
(* B 0x82344 (A 0x821e8), the return of pj_string (&v, text): St12 -> St13, v = JStr es on one fresh block *)
Definition crtC1_INV_1e8 : crt_inv :=
  fun cx E k ly3 S3 U3 W3 ms3 md3 =>
  let mem := ms_mem ms3 in let F := crt_F cx in
  exists Ddoc Dst a3 same nsame dec live peak cnt,
    crtC1_corex cx E k ly3 S3 U3 W3 mem (Ddoc ++ Dst ++ [(a3, Z.of_nat (length (crt_es cx)) + 1)]) (crtC1_KC_1e8 cx)
      (crtC1_CNT_1e8 cx) (crtC1_LIVE_1e8 cx) same nsame dec live peak cnt /\
    crtC1_doc cx ly3 S3 W3 mem Ddoc /\
    rtree tfibsegs B ly3 S3 W3 mem (F + 0x80) (PjTree.JObj check_round_trip_stages_b.crt_s2) Dst /\
    (exists sk sy se sv sc sp,
       Permutation Dst [(sk, 56 * 8); (sy, 8 * 8); (se, 9); (sv, 7); (sc, 8); (sp, 7)]) /\
    pobj tfibsegs B ly3 S3 W3 mem (F + 0x80) /\
    rtree tfibsegs B ly3 S3 W3 mem (F + 0xe0) (PjTree.JStr (crt_es cx)) [(a3, Z.of_nat (length (crt_es cx)) + 1)] /\
    pobj tfibsegs B ly3 S3 W3 mem (F + 0xe0).
(* B 0x8235c (A 0x82200), the return of pj_set (&state, "bytes", &v): St13 -> St14, the state holds crt_st es, v is
   zeroed *)
Definition crtC1_INV_200 : crt_inv :=
  fun cx E k ly3 S3 U3 W3 ms3 md3 =>
  let mem := ms_mem ms3 in let F := crt_F cx in
  exists Ddoc Dst same nsame dec live peak cnt,
    crtC1_corex cx E k ly3 S3 U3 W3 mem (Ddoc ++ Dst) (crtC1_KC_200 cx) (crtC1_CNT_200 cx)
      (crtC1_LIVE_200 cx) same nsame dec live peak cnt /\
    crtC1_doc cx ly3 S3 W3 mem Ddoc /\
    rtree tfibsegs B ly3 S3 W3 mem (F + 0x80) (PjTree.JObj (check_round_trip_stages_b.crt_st (crt_es cx))) Dst /\
    pobj tfibsegs B ly3 S3 W3 mem (F + 0x80) /\
    PjStruct.pj_zero tfibsegs (mrestrict (w_H W3) mem) (F + 0xe0) /\ pobj tfibsegs B ly3 S3 W3 mem (F + 0xe0).
(* each boundary's a0 is 0 (the callee's return), which decides the next `bnez a0` *)
Lemma crtC1_a0_821ac : forall cx E k ly3 S3 U3 (W3 : world tfibsegs) ms3 md3,
  crt_INV_821ac B cx E k ly3 S3 U3 W3 ms3 md3 -> ew E 10 = Z_to_bv 64 0.
Proof. intros cx E k ly3 S3 U3 W3 ms3 md3 H. exact (proj1 H). Qed.
Lemma crtC1_a0_1c0 : forall cx E k ly3 S3 U3 (W3 : world tfibsegs) ms3 md3,
  crtC1_INV_1c0 cx E k ly3 S3 U3 W3 ms3 md3 -> ew E 10 = Z_to_bv 64 0.
Proof. intros cx E k ly3 S3 U3 W3 ms3 md3 (_ & _ & _ & _ & _ & _ & _ & _ & _ & (H & _) & _). exact H. Qed.
Lemma crtC1_a0_1d8 : forall cx E k ly3 S3 U3 (W3 : world tfibsegs) ms3 md3,
  crtC1_INV_1d8 cx E k ly3 S3 U3 W3 ms3 md3 -> ew E 10 = Z_to_bv 64 0.
Proof. intros cx E k ly3 S3 U3 W3 ms3 md3 (_ & _ & _ & _ & _ & _ & _ & _ & (H & _) & _). exact H. Qed.
Lemma crtC1_a0_1e8 : forall cx E k ly3 S3 U3 (W3 : world tfibsegs) ms3 md3,
  crtC1_INV_1e8 cx E k ly3 S3 U3 W3 ms3 md3 -> ew E 10 = Z_to_bv 64 0.
Proof. intros cx E k ly3 S3 U3 W3 ms3 md3 (_ & _ & _ & _ & _ & _ & _ & _ & _ & (H & _) & _). exact H. Qed.
Lemma crtC1_a0_200 : forall cx E k ly3 S3 U3 (W3 : world tfibsegs) ms3 md3,
  crtC1_INV_200 cx E k ly3 S3 U3 W3 ms3 md3 -> ew E 10 = Z_to_bv 64 0.
Proof. intros cx E k ly3 S3 U3 W3 ms3 md3 (_ & _ & _ & _ & _ & _ & _ & _ & (H & _) & _). exact H. Qed.
End inv.

(* ================= list helpers: pairwise separation survives a permutation =================
   AR's separation law is a `pairwise zdisjoint` over the block list; the walk states the block list only up to a
   permutation, so the separation is read through it (zdisjoint is symmetric). *)
Lemma crtC1_pairwise_perm : forall {X} (R : X -> X -> Prop), (forall x y, R x y -> R y x) ->
  forall l l', Permutation l l' -> pairwise R l -> pairwise R l'.
Proof.
intros X R Hs l l' HP. induction HP as [| x l l' HP IH | x y l | l l' l'' H1 IH1 H2 IH2]; cbn; intros H.
- exact H.
- destruct H as [F P]. split; [|exact (IH P)].
  apply Forall_forall. intros z Hz. apply (proj1 (Forall_forall _ _) F). exact (Permutation_in _ (Permutation_sym HP) Hz).
- destruct H as [F1 [F2 P]]. inversion F1 as [|? ? Hxy F1']; subst.
  split; [constructor; [exact (Hs _ _ Hxy) | exact F2] | split; [exact F1' | exact P]].
- exact (IH2 (IH1 H)).
Qed.
Lemma crtC1_zdisj_sym : forall x y, zdisjoint x y -> zdisjoint y x.
Proof. intros x y H. unfold zdisjoint in *. lia. Qed.
Section sep. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : asyms.
Let LAWS : AR_laws tfibsegs B := AR_laws_ok tfibsegs B.
(* two blocks from the two halves of a split of the block list are apart *)
Lemma crtC1_perm_sep : forall ly S (W : world tfibsegs) mem md L1 L2,
  AR tfibsegs B ly S W mem md -> Permutation (ablocks B ly S) (L1 ++ L2) ->
  forall x y, In x L1 -> In y L2 -> zdisjoint (fst x, req_size (snd x)) (fst y, req_size (snd y)).
Proof.
intros ly S W mem md L1 L2 HAR HP x y Hx Hy.
destruct (al_sep _ _ LAWS ly S W mem md HAR) as [Hp _]. apply pairwise_app_l in Hp as [Hp _].
pose proof (crtC1_pairwise_perm zdisjoint crtC1_zdisj_sym _ _ (Permutation_map (fun b => (fst b, req_size (snd b))) HP) Hp)
  as Hq.
rewrite map_app in Hq.
exact (proj2 (proj2 (YG0s.pairwise_app_inv zdisjoint _ _ Hq)) _ _ (in_map _ _ _ Hx) (in_map _ _ _ Hy)).
Qed.
End sep.

(* the text's length against its block, the body's against the decode block (WriterSpecFacts.b64_enc_length) *)
Lemma crtC1_tb2_len : forall bs,
  Z.of_nat (length (WriterSpec.b64_enc bs)) + 1 = FSH_Fn_writer.enc_size (Z.of_nat (length bs)).
Proof.
intros bs. rewrite WriterSpecFacts.b64_enc_length. rewrite Nat2Z.inj_mul, Nat2Z.inj_div, Nat2Z.inj_add.
unfold FSH_Fn_writer.enc_size. cbn. lia.
Qed.
Lemma crtC1_bs_le_dec : forall bs,
  Z.of_nat (length bs) <= FSH_Fn_writer.dec_size (WriterSpec.b64_enc bs).
Proof.
intros bs. unfold FSH_Fn_writer.dec_size. rewrite WriterSpecFacts.b64_enc_length.
rewrite Nat2Z.inj_mul, Nat2Z.inj_div, Nat2Z.inj_add. cbn. Z.div_mod_to_equations. lia.
Qed.

(* ================= what a call of the lane may touch =================
   Every callee footprint of lane C1 is inside crt's object region [F, F + 0x118) (doc, state, v), fs's statics, or
   blocks of a list Y of the trees' blocks (pj_set's old kids / keys). So a byte of any OTHER live block (the text,
   the decode block) or of the frame's tail (back, the n cells, the flag word) is off the footprint, and no footprint
   byte is a shadow byte. ---- *)
Section fpk. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : asyms.
Let LAWS : AR_laws tfibsegs B := AR_laws_ok tfibsegs B.
Definition crtC1_fp (ly : alayout) (pos : Z) (FPc Y : list (Z * Z)) : Prop :=
  forall x, inFP FPc x -> (frame_addr ly 3 pos <= x < frame_addr ly 3 pos + 0x118) \/ inFP FS_PSTAT_FP x \/
    (exists b, In b Y /\ fst b <= x < fst b + req_size (snd b)).
Lemma crtC1_notFP : forall ly S (W : world tfibsegs) mem md FPc pos Y L1 L2 a,
  AR tfibsegs B ly S W mem md -> In (3, pos) (frames S) -> crtC1_fp ly pos FPc Y ->
  Permutation (ablocks B ly S) (L1 ++ L2) -> (forall b, In b Y -> In b L2) ->
  ((exists blk, In blk L1 /\ fst blk <= a < fst blk + req_size (snd blk)) \/
   (frame_addr ly 3 pos + 0x118 <= a < frame_addr ly 3 pos + 512)) ->
  ~ inFP FPc a.
Proof.
intros ly S W mem md FPc pos Y L1 L2 a HAR Hfr HFP HP HY Ha Hin.
assert (HinB : forall b, In b L1 -> In b (ablocks B ly S))
  by (intros b Hb; apply (Permutation_in _ (Permutation_sym HP)); apply in_or_app; left; exact Hb).
assert (HinB2 : forall b, In b L2 -> In b (ablocks B ly S))
  by (intros b Hb; apply (Permutation_in _ (Permutation_sym HP)); apply in_or_app; right; exact Hb).
destruct (HFP a Hin) as [Hf | [Hs | (b & Hb & Hr)]].
- destruct Ha as [((p, n) & Hblk & Hr) | Hr]; [|lia].
  pose proof (sep_block_frame tfibsegs B LAWS ly S W mem md p n 3 pos HAR (HinB _ Hblk) Hfr) as D.
  unfold zdisjoint in D. rewrite crt_frame3 in D. cbn [fst snd] in *. lia.
- pose proof (crt_pstat_img a Hs) as Himg.
  destruct Ha as [((p, n) & Hblk & Hr) | Hr].
  + exact (blk_img tfibsegs B LAWS ly S W mem md p n a HAR (HinB _ Hblk) Hr Himg).
  + exact (frm_img tfibsegs B LAWS ly S W mem md 3 pos a HAR Hfr ltac:(rewrite crt_frame3; lia) Himg).
- destruct Ha as [((p, n) & Hblk & Hr') | Hr'].
  + pose proof (crtC1_perm_sep B ly S W mem md L1 L2 HAR HP (p, n) b Hblk (HY b Hb)) as D.
    unfold zdisjoint in D. cbn [fst snd] in *. lia.
  + destruct b as (q, m).
    pose proof (sep_block_frame tfibsegs B LAWS ly S W mem md q m 3 pos HAR (HinB2 _ (HY _ Hb)) Hfr) as D.
    unfold zdisjoint in D. rewrite crt_frame3 in D. cbn [fst snd] in *. lia.
Qed.
Lemma crtC1_FP_noshadow : forall ly S (W : world tfibsegs) mem md FPc pos Y,
  AR tfibsegs B ly S W mem md -> In (3, pos) (frames S) -> crtC1_fp ly pos FPc Y ->
  (forall b, In b Y -> In b (ablocks B ly S)) ->
  forall a, inFP FPc a -> ~ (SHADOW_OFF <= a < SHADOW_OFF + 2 ^ 44).
Proof.
intros ly S W mem md FPc pos Y HAR Hfr HFP HY a Hin.
destruct (HFP a Hin) as [Hf | [Hs | ((q, m) & Hb & Hr)]].
- destruct (frames_bounds tfibsegs B LAWS ly S W mem md 3 pos HAR Hfr) as (_ & _ & Happ).
  rewrite crt_frame3 in Happ. pose proof (in_app_addr _ _ a Happ ltac:(lia)) as AP.
  unfold app_addr, kLowShadowBeg, kHighMemBeg, SHADOW_OFF in AP |- *. lia.
- pose proof (fs_segs_img a (crt_pstat_img a Hs)) as Hl. unfold FS_IMG_END, SHADOW_OFF in *. lia.
- exact (fsw_ablock_off_shadow B ly S W mem md q m HAR (HY _ Hb) a Hr).
Qed.
End fpk.

(* ================= the shared part of a boundary across a store-free run and across a call ================= *)
Section core. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable SK : YI16.sink_head.
Variable B : asyms.
Let LAWS : AR_laws tfibsegs B := AR_laws_ok tfibsegs B.
(* across the run from the boundary to the call: every byte below alloc_ceiling is kept *)
Lemma crtC1_core_below : forall cx E k ly3 S3 U3 (W3 : world tfibsegs) mx md m m' D Kb CNTb LIVEb
    same nsame dec live peak cnt,
  AR tfibsegs B ly3 S3 W3 mx md -> 0 <= crt_F cx -> crt_F cx + 512 <= alloc_ceiling ->
  same_below m m' alloc_ceiling ->
  crtC1_corex B cx E k ly3 S3 U3 W3 m D Kb CNTb LIVEb same nsame dec live peak cnt ->
  crtC1_corex B cx E k ly3 S3 U3 W3 m' D Kb CNTb LIVEb same nsame dec live peak cnt.
Proof.
intros cx E k ly3 S3 U3 W3 mx md m m' D Kb CNTb LIVEb same nsame dec live peak cnt HAR HF0 HF1 Hs HC.
cbv beta zeta delta [crtC1_corex] in HC |- *.
destruct HC as (C10 & C18 & C20 & C21 & C27 & C23 & C24 & C25 & C22 & C19 & PB & PU & HH & TB & TZ & TC & DB & DZ & PO &
  VM & RA & GL & LV & BB & CN & KB).
pose proof (fsw_rblock_low B _ _ _ _ _ m _ _ HAR TB) as (T0 & T1).
pose proof (fsw_rblock_low B _ _ _ _ _ m _ _ HAR DB) as (D0 & D1).
pose proof (crtC1_tb2_len (c_bs cx)) as Etb. pose proof (crtC1_bs_le_dec (c_bs cx)) as Ebs.
repeat (split; [assumption|]).
split; [exact (fs_rblock_below B _ _ _ _ _ m m' _ _ HAR Hs TB)|].
split; [apply (crtC1_zbytes_below W3 m m' _ _ Hs); [unfold HEAD in T0; lia | rewrite length_app; cbn [length]; lia | exact TZ]|].
split; [exact (cstr_ok_below W3 m m' _ _ Hs TC)|].
split; [exact (fs_rblock_below B _ _ _ _ _ m m' _ _ HAR Hs DB)|].
split; [apply (crtC1_zbytes_below W3 m m' _ _ Hs); [unfold HEAD in D0; lia | lia | exact DZ]|].
split; [exact (pobj_below B _ _ _ _ _ m m' _ HAR Hs PO)|].
split; [apply (val_mem_below (w_H W3) m m' alloc_ceiling _ 8 0 Hs); [lia | cbn; lia | exact VM]|].
split; [apply (fsw_range_addressable_below (w_H W3) m m' _ 8 Hs); [lia | lia | exact RA]|].
split; [exact (fs_glob_below W3 m m' _ _ _ _ Hs GL)|].
exact (conj LV (conj BB (conj CN KB))).
Qed.

(* across a program call: the callee's journal (own = []) with a footprint of crtC1_fp's shape, the new blocks Dn of
   the trees (rd_hblocks Dn joins the block list, their heads U), g_live grown by rd_sum Dn, the callee's ticks and
   counter bumps, and the s-registers kept *)
Lemma crtC1_core_call : forall cx E E' k kc ly3 S3 U3 (W3 : world tfibsegs) memC mdC STKc spc FPc ly' S' U' W' mem' md'
    D Dn D' Y Kb CNTb LIVEb Kb' CNTb' LIVEb' same nsame dec live peak cnt peak' cntd,
  crtC1_corex B cx E k ly3 S3 U3 W3 memC D Kb CNTb LIVEb same nsame dec live peak cnt ->
  ARU tfibsegs B ly3 S3 U3 W3 memC mdC -> frames S3 = (3, c_pos cx) :: frames (c_S cx) ->
  frame_addr ly3 3 (c_pos cx) = crt_F cx ->
  ajournal tfibsegs B STKc spc FPc ly3 S3 W3 (unpoison U3 memC) mdC [] ly' S' W' (unpoison U' mem') md' kc ->
  upoison_ok B ly' S' U' -> upoisoned tfibsegs W' mem' U' ->
  crtC1_fp ly3 (c_pos cx) FPc Y -> (forall b, In b Y -> In b (rd_hblocks D)) ->
  ew E' 10 = Z_to_bv 64 0 -> (forall n, (18 <= n <= 27)%nat -> ew E' n = ew E n) ->
  Permutation (ablocks B ly' S') (ablocks B ly3 S3 ++ rd_hblocks Dn) ->
  Permutation U' (U3 ++ rd_heads Dn) ->
  Forall (fun b => 0 < snd b) Dn ->
  Permutation D' (D ++ Dn) ->
  fs_glob tfibsegs W' mem' (live + rd_sum Dn) peak' (cnt + cntd) SIZE_MAXZ ->
  0 <= cntd -> Kb + kc <= Kb' -> CNTb + cntd <= CNTb' -> LIVEb + YCbq.bsum (rd_hblocks Dn) <= LIVEb' ->
  crtC1_corex B cx E' (k + kc) ly' S' U' W' mem' D' Kb' CNTb' LIVEb' same nsame dec (live + rd_sum Dn) peak'
    (cnt + cntd).
Proof.
intros cx E E' k kc ly3 S3 U3 W3 memC mdC STKc spc FPc ly' S' U' W' mem' md' D Dn D' Y Kb CNTb LIVEb Kb' CNTb' LIVEb'
  same nsame dec live peak cnt peak' cntd HC HARU Hfr EF HJc OK' PO' HFP HY R10 RS HPB HPU HDn HD' HGL Hcd HKb HCb HLb.
cbv beta zeta delta [crtC1_corex] in HC |- *.
destruct HC as (C10 & C18 & C20 & C21 & C27 & C23 & C24 & C25 & C22 & C19 & PB & PU & HH & TB & TZ & TC & DB & DZ & PO &
  VM & RA & GL & LV & BB & CN & KB).
pose proof (ARU_AR tfibsegs B _ _ _ _ _ _ HARU) as HAR3.
assert (HAR' : AR tfibsegs B ly' S' W' (unpoison U' mem') md') by exact (proj1 HJc).
assert (Hin3 : In (3, c_pos cx) (frames S3)) by (rewrite Hfr; left; reflexivity).
set (L4 := [(c_text cx - HEAD, FSH_Fn_writer.enc_size (Z.of_nat (length (c_bs cx))) + HEAD);
  (c_want cx, FSH_Fn_writer.enc_size (Z.of_nat (length (c_bs cx)))); (same, nsame);
  (dec - HEAD, FSH_Fn_writer.dec_size (WriterSpec.b64_enc (c_bs cx)) + HEAD)]) in *.
assert (PB' : Permutation (ablocks B ly3 S3) ((ablocks B (c_ly cx) (c_S cx) ++ L4) ++ rd_hblocks D))
  by (rewrite <- app_assoc; exact PB).
assert (HYb : forall b, In b Y -> In b (ablocks B ly3 S3))
  by (intros b Hb; apply (Permutation_in _ (Permutation_sym PB')); apply in_or_app; right; exact (HY b Hb)).
pose proof (crtC1_FP_noshadow B ly3 S3 W3 _ mdC FPc (c_pos cx) Y HAR3 Hin3 HFP HYb) as HFsh.
assert (NFb : forall blk a, In blk L4 -> fst blk <= a < fst blk + req_size (snd blk) -> ~ inFP FPc a).
{ intros blk a Hb Ha. apply (crtC1_notFP B ly3 S3 W3 _ mdC FPc (c_pos cx) Y _ _ a HAR3 Hin3 HFP PB' HY).
  left. exists blk. split; [apply in_or_app; right; exact Hb | exact Ha]. }
assert (NFt : forall a, crt_F cx + 0x118 <= a < crt_F cx + 512 -> ~ inFP FPc a).
{ intros a Ha. apply (crtC1_notFP B ly3 S3 W3 _ mdC FPc (c_pos cx) Y _ _ a HAR3 Hin3 HFP PB' HY).
  right. rewrite EF. exact Ha. }
pose proof (crtC1_tb2_len (c_bs cx)) as Etb. pose proof (crtC1_bs_le_dec (c_bs cx)) as Ebs.
set (len := Z.of_nat (length (c_bs cx))) in *. set (tb2 := WriterSpec.b64_enc (c_bs cx)) in *.
assert (Ht : In (c_text cx - HEAD, FSH_Fn_writer.enc_size len + HEAD) (ablocks B ly3 S3))
  by (apply (Permutation_in _ (Permutation_sym PB')); apply in_or_app; left; apply in_or_app; right; left; reflexivity).
assert (Hd : In (dec - HEAD, FSH_Fn_writer.dec_size tb2 + HEAD) (ablocks B ly3 S3))
  by (apply (Permutation_in _ (Permutation_sym PB')); apply in_or_app; left; apply in_or_app; right;
      right; right; right; left; reflexivity).
assert (Hsub : forall b, In b (ablocks B ly3 S3) -> In b (ablocks B ly' S'))
  by (intros b Hb; apply (Permutation_in _ (Permutation_sym HPB)); apply in_or_app; left; exact Hb).
assert (Enp : forall n, 0 < n -> req_size (n + HEAD) = n + HEAD)
  by (intros n Hn; unfold req_size, HEAD; destruct (Z.eqb_spec (n + 16) 0); lia).
pose proof (fsw_rblock_low B _ _ _ _ _ memC _ _ HAR3 TB) as (T0 & T1).
pose proof (fsw_rblock_low B _ _ _ _ _ memC _ _ HAR3 DB) as (D0 & D1).
pose proof TB as (_ & _ & Tpos & _). pose proof DB as (_ & _ & Dpos & _).
assert (NFtext : forall a, c_text cx - HEAD <= a < c_text cx + FSH_Fn_writer.enc_size len -> ~ inFP FPc a).
{ intros a Ha. apply (NFb _ a ltac:(left; reflexivity)). cbn [fst snd]. rewrite Enp by lia. lia. }
assert (NFdec : forall a, dec - HEAD <= a < dec + FSH_Fn_writer.dec_size tb2 -> ~ inFP FPc a).
{ intros a Ha. apply (NFb _ a ltac:(right; right; right; left; reflexivity)). cbn [fst snd]. rewrite Enp by lia. lia. }
(* the heads after the call *)
assert (HH' : FSupoisonU.fs_heads B ly' S' U').
{ apply (crtC1_fs_heads_perm B ly' S' (U3 ++ rd_heads Dn) U' (Permutation_sym HPU)).
  apply (crtC1_fs_heads_grow B ly3 S3 ly' S' U3 (rd_heads Dn) HH Hsub).
  intros r Hr. unfold rd_heads in Hr. apply in_map_iff in Hr as ((a, n) & <- & Han). cbn [fst snd].
  split; [reflexivity|]. exists (n + HEAD). split.
  - apply (Permutation_in _ (Permutation_sym HPB)). apply in_or_app; right. unfold rd_hblocks.
    exact (in_map (fun b => (fst b - HEAD, snd b + HEAD)) _ (a, n) Han).
  - rewrite Forall_forall in HDn. pose proof (HDn _ Han) as Hn. cbn [snd] in Hn. rewrite Enp by lia. unfold HEAD. lia. }
assert (LBblk : forall p n a, In (p, n) (ablocks B ly3 S3) -> p <= a < p + req_size n ->
  ((exists p0 n0, In (p0, n0) (ablocks B ly3 S3) /\ p0 <= a < p0 + req_size n0) \/
   (exists cid pos, In (cid, pos) (frames S3) /\ frame_addr ly3 cid pos <= a < frame_addr ly3 cid pos + fs_frame_bytes cid)))
  by (intros p n a Hpn Ha; left; exists p, n; split; [exact Hpn | exact Ha]).
assert (LBfrm : forall a, crt_F cx <= a < crt_F cx + 512 ->
  exists cid pos, In (cid, pos) (frames S3) /\ frame_addr ly3 cid pos <= a < frame_addr ly3 cid pos + fs_frame_bytes cid)
  by (intros a Ha; exists 3, (c_pos cx); split; [exact Hin3 | rewrite EF, crt_frame3; exact Ha]).
split; [exact R10|].
split; [rewrite (RS 18%nat ltac:(lia)); exact C18|].
split; [rewrite (RS 20%nat ltac:(lia)); exact C20|].
split; [rewrite (RS 21%nat ltac:(lia)); exact C21|].
split; [rewrite (RS 27%nat ltac:(lia)); exact C27|].
split; [rewrite (RS 23%nat ltac:(lia)); exact C23|].
split; [rewrite (RS 24%nat ltac:(lia)); exact C24|].
split; [rewrite (RS 25%nat ltac:(lia)); exact C25|].
split; [rewrite (RS 22%nat ltac:(lia)); exact C22|].
split; [rewrite (RS 19%nat ltac:(lia)); exact C19|].
split.
{ eapply Permutation_trans; [exact HPB|].
  eapply Permutation_trans; [apply Permutation_app_tail; exact PB|]. rewrite <- !app_assoc.
  apply Permutation_app_head. apply Permutation_app_head.
  rewrite <- crtC1_rd_hblocks_app. apply Permutation_map. apply Permutation_sym. exact HD'. }
split.
{ eapply Permutation_trans; [exact HPU|].
  eapply Permutation_trans; [apply Permutation_app_tail; exact PU|]. rewrite <- !app_assoc.
  apply Permutation_app_head. apply Permutation_app_head.
  rewrite <- crtC1_rd_heads_app. apply Permutation_map. apply Permutation_sym. exact HD'. }
split; [exact HH'|].
split; [exact (fs_rblock_kept_call B STKc spc FPc ly3 S3 U3 W3 memC mdC ly' S' U' W' mem' md' kc _ _ HJc HARU OK' PO'
  NFtext TB)|].
split.
{ apply (crtC1_zbytes_kept_call SK B STKc spc FPc ly3 S3 U3 W3 memC mdC ly' S' U' W' mem' md' kc _ _ HJc HARU OK' PO'); [|exact TZ].
  intros a Ha. rewrite length_app in Ha. cbn [length] in Ha.
  split; [apply (LBblk _ _ a Ht); rewrite Enp by lia; unfold HEAD in *; lia | apply NFtext; unfold HEAD in *; lia]. }
split.
{ apply (FSW_strkit.cstr_ok_kept_blkU B STKc spc FPc ly3 S3 U3 W3 memC mdC [] ly' S' U' W' mem' md' kc (c_text cx) tb2
    (c_text cx - HEAD) (FSH_Fn_writer.enc_size len + HEAD) HARU HJc OK' PO' Ht (Hsub _ Ht));
    [unfold HEAD in *; lia | unfold HEAD in *; lia | | | exact TC].
  - intros a Ha. apply NFtext. unfold HEAD in *. lia.
  - intros r Hr. right.
    destruct (crtC1_heads_apart B ly' S' W' _ md' U' (c_text cx) (FSH_Fn_writer.enc_size len) (Z.of_nat (length tb2))
      HAR' HH' (Hsub _ Ht) ltac:(lia) ltac:(unfold HEAD in *; lia) r Hr) as [X|X]; [right; exact X | left; exact X]. }
split; [exact (fs_rblock_kept_call B STKc spc FPc ly3 S3 U3 W3 memC mdC ly' S' U' W' mem' md' kc _ _ HJc HARU OK' PO'
  NFdec DB)|].
split.
{ apply (crtC1_zbytes_kept_call SK B STKc spc FPc ly3 S3 U3 W3 memC mdC ly' S' U' W' mem' md' kc _ _ HJc HARU OK' PO'); [|exact DZ].
  intros a Ha. split; [apply (LBblk _ _ a Hd); rewrite Enp by lia; unfold HEAD in *; lia | apply NFdec; unfold HEAD in *; lia]. }
split.
{ apply (pobj_kept_call B STKc spc FPc ly3 S3 U3 W3 memC mdC ly' S' U' W' mem' md' kc _ HJc HARU OK' PO'); 
    [intros a Ha; apply NFt; lia | exact HFsh | exact HH' | exact PO]. }
split.
{ apply (crtC1_val_mem_kept_call SK B STKc spc FPc ly3 S3 U3 W3 memC mdC ly' S' U' W' mem' md' kc _ _ _ HJc HARU OK' PO');
    [|exact VM].
  intros a Ha. cbn in Ha. split; [right; apply LBfrm; lia | apply NFt; lia]. }
split.
{ apply (crtC1_raddr_kept_call SK B STKc spc FPc ly3 S3 U3 W3 memC mdC ly' S' U' W' mem' md' kc _ _ HJc HARU OK' PO' HFsh HH');
    [|exact RA].
  intros a Ha. apply LBfrm. lia. }
split; [exact HGL|].
split.
{ assert (ED : rd_sum D' = rd_sum D + rd_sum Dn).
  { change (rd_sum D') with (YCbq.bsum D'). rewrite (YCbq.bsum_perm _ _ HD').
    change (YCbq.bsum (D ++ Dn)) with (rd_sum (D ++ Dn)). apply crt_rd_sum_app. }
  rewrite LV, ED. lia. }
split.
{ rewrite (YCbq.blocks_bytes_bsum B ly' S'), (YCbq.bsum_perm _ _ HPB), YCbq.bsum_app, <- (YCbq.blocks_bytes_bsum B ly3 S3).
  lia. }
split; lia.
Qed.
End core.

(* ================= facts every call of the lane uses ================= *)
Section cc. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : asyms.
Let LAWS : AR_laws tfibsegs B := AR_laws_ok tfibsegs B.
(* crt_base's four room facts: the counter, g_live, the ticks and the live bytes the whole call may use *)
Lemma crtC1_base_facts : forall cx, crt_base B cx ->
  quiet (c_cnt cx) SIZE_MAXZ EV_check_round_trip /\ c_live cx + LIVE_check_round_trip < 2 ^ 64 /\
  st_nev (c_S cx) + EV_check_round_trip <= EV_MAX /\ blocks_bytes (c_S cx) + LIVE_check_round_trip <= LIVE_MAX.
Proof.
intros cx HB. unfold crt_base in HB.
(* base v27 (A c6275044faa): crt_base's new LAST conjunct (the input outside U) is the trailing `_` *)
destruct HB as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hq & Hl & _ & _ & Hev & Hlv & _).
exact (conj Hq (conj Hl (conj Hev Hlv))).
Qed.
(* the s-registers a pj_* call keeps: the call site held them as the boundary atoms (crt_ssave), the callee preserves
   them (aregs_preserved), so the next boundary env reads the old values *)
Lemma crtC1_regs_kept : forall E ssC regsC regs' X,
  (forall rr : bv 5, YK11.getr regsC rr = sv_denot E (sr_get (ss_regs ssC) rr)) -> crt_ssave ssC ->
  aregs_preserved regsC regs' -> forall n, (18 <= n <= 27)%nat -> ew (Ereg regs' X) n = ew E n.
Proof.
intros E ssC regsC regs' X RG HS HP n Hn.
assert (Hr : Z.of_nat n = bv_unsigned (Z_to_bv 5 (Z.of_nat n) : bv 5)).
{ rewrite Z_to_bv_unsigned, bv_wrap_small; [reflexivity|]. change (bv_modulus 5) with 32. lia. }
rewrite (ew_Ereg_nat regs' X n (Z_to_bv 5 (Z.of_nat n)) Hr).
rewrite (fsw_pres regsC regs' _ HP) by (unfold acallee_saved; rewrite <- Hr; lia).
rewrite RG, (HS n Hn). apply fsw_SOff0.
Qed.
Lemma crtC1_a0_post : forall regs' X, YK11.getr regs' 10%bv = w64 0 -> ew (Ereg regs' X) 10 = Z_to_bv 64 0.
Proof. intros regs' X H. rewrite (ew_Ereg_nat regs' X 10 10%bv ltac:(reflexivity)). exact H. Qed.
(* B only: an argument the engine answered as SOff 47 off (a frame object read from an s1 slot: segment 24's obj
   F + 0x20 from slot 0x38) is F + off on the machine, atom 47 = F (FSH_crt_base.crt_E_F) *)
Lemma crtC1_F_arg : forall cx E off, crt_E cx E -> 0 <= crt_F cx < 2 ^ 64 -> 0 <= crt_F cx + off < 2 ^ 64 ->
  sv_denot E (SOff 47 off) = Z_to_bv 64 (crt_F cx + off).
Proof.
intros cx E off HE HF HFo.
apply bv_eq. rewrite denot_SOff, (crt_E_F cx E HE), (wz (crt_F cx) HF), (wz (crt_F cx + off) HFo).
apply zcanon_id. unfold M64. lia.
Qed.
(* g_live under the boundary's live budget: the four fixed blocks and the trees' blocks are counted by blocks_bytes *)
Lemma crtC1_live_le : forall cx E k ly3 S3 U3 (W3 : world tfibsegs) mx md mem D Kb CNTb LIVEb same nsame dec live peak cnt,
  AR tfibsegs B ly3 S3 W3 mx md ->
  crtC1_corex B cx E k ly3 S3 U3 W3 mem D Kb CNTb LIVEb same nsame dec live peak cnt ->
  live + 32 <= c_live cx + LIVEb.
Proof.
intros cx E k ly3 S3 U3 W3 mx md mem D Kb CNTb LIVEb same nsame dec live peak cnt HAR HC.
cbv beta zeta delta [crtC1_corex] in HC.
destruct HC as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & PB & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & LV & BB & _ & _).
pose proof (crtC1_rd_sum_le B ly3 S3 (c_ly cx) (c_S cx) _ D PB) as E1.
assert (Hs : In (same, nsame) (ablocks B ly3 S3)).
{ apply (Permutation_in _ (Permutation_sym PB)). apply in_or_app; right. apply in_or_app; left.
  right; right; left; reflexivity. }
destruct (al_blocks _ _ LAWS _ _ _ _ _ same nsame HAR Hs) as (_ & _ & _ & _ & _ & _ & Hn0).
assert (He : 0 <= FSH_Fn_writer.enc_size (Z.of_nat (length (c_bs cx)))).
{ unfold FSH_Fn_writer.enc_size. pose proof (Z.div_pos (Z.of_nat (length (c_bs cx)) + 2) 3 ltac:(lia) ltac:(lia)). lia. }
unfold YCbq.bsum in E1. cbn [fold_right fst snd] in E1. pose proof (Zle_0_nat (length D)). unfold HEAD in *. lia.
Qed.
(* the room every call of the lane needs, from the budgets at B 0x82374 (K / CNT / LIVE_82218) *)
Lemma crtC1_quiet : forall cx cnt CNTb t, crt_base B cx -> c_cnt cx <= cnt <= c_cnt cx + CNTb ->
  0 <= t -> CNTb + t <= CNT_82218 cx -> quiet cnt SIZE_MAXZ t.
Proof.
intros cx cnt CNTb t HB Hc Ht Hb. destruct (crtC1_base_facts cx HB) as ((_ & Hc0 & Hc78) & _).
pose proof (crtC1_CNT_le cx) as X. unfold EV_check_round_trip in *. split; [reflexivity|]. lia.
Qed.
Lemma crtC1_nev : forall cx k S3 Kb t, crt_base B cx -> st_nev S3 <= st_nev (c_S cx) + k -> k <= Kb ->
  Kb + t <= K_82218 cx -> st_nev S3 + t <= EV_MAX.
Proof.
intros cx k S3 Kb t HB Hs Hk Hb. destruct (crtC1_base_facts cx HB) as (_ & _ & Hev & _).
pose proof (crtC1_K_le cx). unfold EV_check_round_trip in *. lia.
Qed.
Lemma crtC1_bb : forall cx S3 LIVEb t, crt_base B cx -> blocks_bytes S3 <= blocks_bytes (c_S cx) + LIVEb ->
  LIVEb + t <= LIVE_82218 cx -> blocks_bytes S3 + t <= LIVE_MAX.
Proof.
intros cx S3 LIVEb t HB Hs Hb. destruct (crtC1_base_facts cx HB) as (_ & _ & _ & Hlv).
pose proof (crtC1_LIVE_le B cx HB). unfold LIVE_check_round_trip in *. lia.
Qed.
Lemma crtC1_live_room : forall cx live LIVEb t, crt_base B cx -> live + 32 <= c_live cx + LIVEb ->
  LIVEb + t <= LIVE_82218 cx -> live + t < 2 ^ 64.
Proof.
intros cx live LIVEb t HB Hl Hb. destruct (crtC1_base_facts cx HB) as (_ & Hlive & _).
pose proof (crtC1_LIVE_le B cx HB). lia.
Qed.
(* the five calls' ticks / counter bumps / live bytes against the budgets at B 0x82374 (K / CNT / LIVE_82218) *)
Lemma crtC1_steps : forall cx,
  crtC1_KC_200 cx + rd_ev (pj_set_c.set_trace 2 8 5) = K_82218 cx /\
  crtC1_CNT_200 cx + 1 = CNT_82218 cx /\ crtC1_LIVE_200 cx + 22 = LIVE_82218 cx /\
  0 <= EV_pj_string /\ 0 <= rd_ev (pj_set_c.set_trace 1 8 7) /\ 0 <= rd_ev (pj_set_c.set_trace 2 8 5) /\
  crt_trlen (pj_set_c.set_trace 1 8 7) = 1 /\ crt_trlen (pj_set_c.set_trace 2 8 5) = 1 /\
  rd_live (pj_set_c.set_trace 1 8 7) = 24 /\ rd_live (pj_set_c.set_trace 2 8 5) = 22 /\
  0 <= Z.of_nat (length (crt_es cx)).
Proof.
intros cx. destruct (crtC1_ticks_nonneg cx) as (T1 & T2 & T3 & _). destruct crtC1_trlen as (_ & _ & L1 & L2).
assert (X2 : rd_live (pj_set_c.set_trace 1 8 7) = 24) by (vm_compute; reflexivity).
assert (X4 : rd_live (pj_set_c.set_trace 2 8 5) = 22) by (vm_compute; reflexivity).
rewrite <- crtC1_K_last, crtC1_CNT_last, crtC1_LIVE_last, L2, X4.
repeat split; try lia; assumption.
Qed.
End cc.

(* a tree whose blocks lie in the block list is off a footprint of crtC1_fp's shape with no tree blocks (Y = []) *)
Section tnf. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : asyms.
Let LAWS : AR_laws tfibsegs B := AR_laws_ok tfibsegs B.
Lemma crtC1_tree_notFP : forall ly S (W : world tfibsegs) mx md mem FPc pos D,
  AR tfibsegs B ly S W mx md -> In (3, pos) (frames S) -> crtC1_fp ly pos FPc [] ->
  rd_blocks_ok tfibsegs B ly S W mem D ->
  forall a k x, In (a, k) D -> a - HEAD <= x < a + k -> ~ inFP FPc x.
Proof.
intros ly S W mx md mem FPc pos D HAR Hfr HFP HB a k x Hak Hx.
destruct (HB a k Hak) as (Hin & _ & Hk & _).
apply (crtC1_notFP B ly S W mx md FPc pos [] (ablocks B ly S) [] x HAR Hfr HFP ltac:(rewrite app_nil_r; reflexivity)
  (fun b H => match H with end)).
left. exists (a - HEAD, k + HEAD). split; [exact Hin|]. cbn [fst snd].
unfold req_size, HEAD in *. destruct (Z.eqb_spec (k + 16) 0); lia.
Qed.
End tnf.

(* ================= the five calls of the lane ================= *)
Section calls. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable SK : YI16.sink_head.
Variable B : asyms.
Let LAWS : AR_laws tfibsegs B := AR_laws_ok tfibsegs B.
(* the image facts (FSH_Fn_reader.v's own named hypothesis) and the two callee contracts, at crt's call sites *)
Hypothesis IMG : fs_img_facts tfibsegs B.
Hypothesis PJS : @pj_string_spec fx rc SK tfibsegs B.
Hypothesis PJSET : @pj_set_spec fx rc SK tfibsegs B.

(* ---- segment 20: pj_string (&v, "preset") at B 0x82318 (A 0x821bc); St10 (d25a984c903 sd10.v): v = JStr V_PRESET on
   a fresh block of 7 bytes, its head joins U, g_live + 7; the document, the state and every other byte of crt are
   kept ---- *)
Lemma crtC1_hcall_1ac : crt_hcall SK B crtC_sc_1ac 0x83e58 0x8231c STK_pj_string (crt_INV_821ac B)
  (crtC1_INV_1c0 B).
Proof.
intros cx E k ly3 S3 U3 W3 ms3 md3 regsC memC mdC HB HE HINV HJC HARUC Hfr HSB RG HPREc HFRL HTOPc.
destruct crtC1_site_1ac as ((_ & _ & _ & _ & G1 & _) & G10 & G11).
destruct crtC1_ssave_all as (SV & _).
cbv beta zeta delta [crt_INV_821ac] in HINV.
destruct HINV as (R10 & R18 & R20 & R21 & R27 & R23 & R22 & R19 & same & nsame & dec & Ddoc & Dst & live & peak & cnt &
  R24 & R25 & PB & PU & HH & TB & TZ & TC & DB & DZ & TDoc & TSt & SZst & (dnum & dstr & dkids & dkeys & dcap & HDh & Edc & _) &
  _ & PDoc & PSt & PV & P140 & _ & VM & RA & GL & LV & BB & CN & KB).
subst dcap.
pose proof (ARU_AR tfibsegs B _ _ _ _ _ _ HARUC) as HARC.
destruct (crt_F_facts SK B cx ly3 S3 U3 W3 memC mdC k HJC HARUC Hfr) as (_ & F4096 & Fceil & _ & _ & _).
pose proof HJC as (_ & HlyC & _ & _ & _ & _ & HnevC & _).
pose proof (crt_F_ly cx _ ly3 HlyC) as EF.
assert (Hin3 : In (3, c_pos cx) (frames S3)) by (rewrite Hfr; left; reflexivity).
set (F := crt_F cx) in *.
(* the boundary at the call site (the run kept every byte below alloc_ceiling) *)
assert (HC3 : crtC1_corex B cx E k ly3 S3 U3 W3 (ms_mem ms3) (Ddoc ++ Dst) (K_821ac cx) (CNT_821ac cx) (LIVE_821ac cx)
  same nsame dec live peak cnt).
{ exact (conj R10 (conj R18 (conj R20 (conj R21 (conj R27 (conj R23 (conj R24 (conj R25 (conj R22 (conj R19 (conj PB
    (conj PU (conj HH (conj TB (conj TZ (conj TC (conj DB (conj DZ (conj P140 (conj VM (conj RA (conj GL (conj LV
    (conj BB (conj CN KB))))))))))))))))))))))))). }
pose proof (crtC1_core_below B cx E k ly3 S3 U3 W3 _ mdC (ms_mem ms3) memC _ _ _ _ _ _ _ _ _ _ HARC ltac:(lia) Fceil HSB HC3)
  as HCC.
pose proof (crtC1_rtree_below B ly3 S3 W3 _ mdC (ms_mem ms3) memC (F + 0x20) _ Ddoc HARC HSB ltac:(lia) ltac:(lia) TDoc)
  as TDocC.
pose proof (crtC1_rtree_below B ly3 S3 W3 _ mdC (ms_mem ms3) memC (F + 0x80) _ Dst HARC HSB ltac:(lia) ltac:(lia) TSt)
  as TStC.
pose proof (pobj_below B ly3 S3 W3 _ mdC (ms_mem ms3) memC _ HARC HSB PDoc) as PDocC.
pose proof (pobj_below B ly3 S3 W3 _ mdC (ms_mem ms3) memC _ HARC HSB PSt) as PStC.
pose proof (pobj_below B ly3 S3 W3 _ mdC (ms_mem ms3) memC _ HARC HSB PV) as PVC.
pose proof (crtC1_pj_hdr_below W3 (ms_mem ms3) memC (F + 0x20) _ _ _ _ _ _ _ HSB ltac:(lia) ltac:(lia) HDh) as HDhC.
(* the call site *)
assert (R1 : YK11.getr regsC 1%bv = Z_to_bv 64 0x8231c) by (rewrite RG, G1; reflexivity).
assert (Rra : raZ regsC = 0x8231c) by (unfold raZ; rewrite R1; apply wz; lia).
assert (Rv : YK11.getr regsC 10%bv = w64 (F + 0xe0)) by (rewrite RG, G10, fsw_SOff0; exact R27).
assert (Rs : YK11.getr regsC 11%bv = w64 0x20f80) by (rewrite RG, G11; reflexivity).
destruct (crtC_key SK B IMG cx k ly3 S3 U3 W3 (mkst regsC (Z_to_bv 64 0x83e58) memC (seg_rom tfibsegs)) mdC
  0x20f80 check_round_trip_stages_b.V_PRESET HB HJC HARUC crtC_in_preset) as (KOK & KKEPT).
pose proof (fsw_sp B _ _ _ _ _ _ _ _ _ (proj1 HPREc)) as (_ & Hsp & _ & _).
pose proof (crtC1_live_le B cx E k ly3 S3 U3 W3 _ mdC memC _ _ _ _ _ _ _ _ _ _ HARC HCC) as Hlv.
pose proof (crtC1_steps cx) as (_ & _ & SL & T1 & T2 & T3 & L1 & L2 & X2 & X4 & Les).
assert (EK : K_821ac cx + EV_pj_string <= K_82218 cx) by (unfold K_82218; lia).
assert (ECN : CNT_821ac cx + 1 <= CNT_82218 cx) by (unfold CNT_82218, crt_trlen in *; lia).
assert (ELV : LIVE_821ac cx + (7 + HEAD) <= LIVE_82218 cx) by (unfold LIVE_82218; rewrite X2, X4; unfold HEAD; lia).
assert (E6 : Z.of_nat (length check_round_trip_stages_b.V_PRESET) = 6) by reflexivity.
(* the footprint: v's 56 bytes and the statics *)
set (FPs := [(F + 0xe0, F + 0xe0 + 56)] ++ FS_PSTAT_FP).
assert (HFPs : crtC1_fp ly3 (c_pos cx) FPs []).
{ intros x Hx. apply inFP_app in Hx as [Hx | Hx].
  - left. apply inFP_cons in Hx as [Hx | Hx]; [rewrite EF; lia | exfalso; exact (inFP_nil x Hx)].
  - right; left; exact Hx. }
assert (NFo : forall o x, (o = F + 0x20 \/ o = F + 0x80) -> o <= x < o + 56 -> ~ inFP FPs x).
{ intros o x Ho Hx Hin. apply inFP_app in Hin as [Hin | Hin].
  - apply inFP_cons in Hin as [Hin | Hin]; [lia | exact (inFP_nil x Hin)].
  - exact (frm_img tfibsegs B LAWS ly3 S3 W3 _ mdC 3 (c_pos cx) x HARC Hin3 ltac:(rewrite EF, crt_frame3; lia)
      (crt_pstat_img x Hin)). }
exists FPs, EV_pj_string.
eexists. split.
{ apply (PJS ly3 S3 U3 W3 regsC memC mdC (crt_ch1 cx) (F + 0xe0) 0x20f80 check_round_trip_stages_b.V_PRESET
    live peak cnt SIZE_MAXZ HPREc HH).
  - exact Rv.
  - exact Rs.
  - exact PVC.
  - left. lia.
  - right. split; [lia|]. split; [exact KOK|]. split; [exact KKEPT|]. rewrite E6.
    destruct (fsw_pobj_off_img B ly3 S3 W3 _ mdC memC _ HARC PVC) as [X | X]; unfold FS_IMG_END in *; lia.
  - exact (fs_glob_below W3 (ms_mem ms3) memC _ _ _ _ HSB GL).
  - exact (crtC1_quiet B cx cnt (CNT_821ac cx) 1 HB CN ltac:(lia) ECN).
  - rewrite E6. unfold HEAD, MALLOC_MAX. lia.
  - rewrite E6. exact (crtC1_live_room B cx live (LIVE_821ac cx) 7 HB Hlv ltac:(unfold HEAD in ELV; lia)).
  - exact (crtC1_nev B cx k S3 (K_821ac cx) EV_pj_string HB HnevC KB EK).
  - rewrite E6. exact (crtC1_bb B cx S3 (LIVE_821ac cx) (6 + 1 + HEAD) HB BB ELV). }
split.
{ pose proof (crtC_fpsub_obj B (c_ly cx) (c_S cx) ly3 S3 (c_pos cx) 0xe0 ltac:(lia) ltac:(lia)) as X.
  rewrite EF in X. exact X. }
split.
{ intros a Ha. apply (crtC1_notFP B ly3 S3 W3 _ mdC FPs (c_pos cx) [] (ablocks B ly3 S3) [] a HARC Hin3 HFPs
    ltac:(rewrite app_nil_r; reflexivity) (fun b H => match H with end)).
  right. rewrite EF. rewrite crt_frame3 in Ha. lia. }
intros W' c' (a1 & ly' & S' & regs' & mem' & md' & -> & HJc & OK' & PO' & HP & (R10' & Ha1 & HAB & HTV & HPV & HGL')).
exists ly', S', (U3 ++ [(a1 - HEAD, HEAD)]), regs', mem', md'.
split; [reflexivity|]. split; [exact HJc|]. split; [exact OK'|]. split; [exact PO'|]. split; [exact HP|].
intros HJ' HARU'.
change (Z.of_nat (length check_round_trip_stages_b.V_PRESET) + 1) with 7 in HAB, HTV, HGL'.
set (E' := Ereg regs' (crt_extra cx)).
pose proof (crtC1_regs_kept E crtC_sc_1ac regsC regs' (crt_extra cx) RG SV HP) as RS.
pose proof (crtC1_a0_post regs' (crt_extra cx) R10') as R10E.
assert (HC' : crtC1_corex B cx E' (k + EV_pj_string) ly' S' (U3 ++ [(a1 - HEAD, HEAD)]) W' mem'
  (Ddoc ++ Dst ++ [(a1, 7)]) (crtC1_KC_1c0 cx) (crtC1_CNT_1c0 cx) (crtC1_LIVE_1c0 cx) same nsame dec
  (live + rd_sum [(a1, 7)]) (Z.max peak (live + 7)) (cnt + 1)).
{ apply (crtC1_core_call SK B cx E E' k EV_pj_string ly3 S3 U3 W3 memC mdC STK_pj_string (spZ regsC) FPs ly' S'
    (U3 ++ [(a1 - HEAD, HEAD)]) W' mem' md' (Ddoc ++ Dst) [(a1, 7)] (Ddoc ++ Dst ++ [(a1, 7)]) [] (K_821ac cx)
    (CNT_821ac cx) (LIVE_821ac cx) _ _ _ same nsame dec live peak cnt (Z.max peak (live + 7)) 1
    HCC HARUC Hfr EF HJc OK' PO' HFPs (fun b H => match H with end) R10E RS).
  - rewrite HAB. apply Permutation_refl.
  - apply Permutation_refl.
  - constructor; [cbn; lia | constructor].
  - rewrite app_assoc. apply Permutation_refl.
  - change (rd_sum [(a1, 7)]) with (7 + 0). rewrite Z.add_0_r. exact HGL'.
  - lia.
  - unfold crtC1_KC_1c0. lia.
  - unfold crtC1_CNT_1c0. lia.
  - unfold crtC1_LIVE_1c0. change (YCbq.bsum (rd_hblocks [(a1, 7)])) with (7 + HEAD + 0). lia. }
pose proof HC' as HC''. cbv beta zeta delta [crtC1_corex] in HC''.
destruct HC'' as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HH' & _).
pose proof (crtC1_FP_noshadow B ly3 S3 W3 _ mdC FPs (c_pos cx) [] HARC Hin3 HFPs (fun b H => match H with end)) as HFsh.
assert (LBo : forall o a, (o = F + 0x20 \/ o = F + 0x80) -> o <= a < o + 56 ->
  ((exists p n, In (p, n) (ablocks B ly3 S3) /\ p <= a < p + req_size n) \/
   (exists cid pos, In (cid, pos) (frames S3) /\ frame_addr ly3 cid pos <= a < frame_addr ly3 cid pos + fs_frame_bytes cid)) /\
  ~ inFP FPs a).
{ intros o a Ho Ha. split; [right; exists 3, (c_pos cx); split; [exact Hin3 | rewrite EF, crt_frame3; lia] | exact (NFo o a Ho Ha)]. }
exists Ddoc, Dst, a1, same, nsame, dec, (live + rd_sum [(a1, 7)]), (Z.max peak (live + 7)), (cnt + 1).
split; [exact HC'|].
split.
{ split; [|split].
  - apply (rtree_kept_call B STK_pj_string (spZ regsC) FPs ly3 S3 U3 W3 memC mdC ly' S' _ W' mem' md' EV_pj_string
      (F + 0x20) _ Ddoc HJc HARUC OK' PO' (fun x => NFo (F + 0x20) x (or_introl eq_refl))); [|exact PDocC | exact TDocC].
    destruct TDocC as (_ & HBk & _).
    exact (crtC1_tree_notFP B ly3 S3 W3 _ mdC memC FPs (c_pos cx) Ddoc HARC Hin3 HFPs HBk).
  - exists dnum, dstr, dkids, dkeys.
    exact (crtC1_pj_hdr_kept_call SK B STK_pj_string (spZ regsC) FPs ly3 S3 U3 W3 memC mdC ly' S' _ W' mem' md' EV_pj_string
      _ _ _ _ _ _ _ _ HJc HARUC OK' PO' (fun a => LBo (F + 0x20) a (or_introl eq_refl)) HDhC).
  - exact (pobj_kept_call B STK_pj_string (spZ regsC) FPs ly3 S3 U3 W3 memC mdC ly' S' _ W' mem' md' EV_pj_string _
      HJc HARUC OK' PO' (fun x => NFo (F + 0x20) x (or_introl eq_refl)) HFsh HH' PDocC). }
split.
{ apply (rtree_kept_call B STK_pj_string (spZ regsC) FPs ly3 S3 U3 W3 memC mdC ly' S' _ W' mem' md' EV_pj_string
    (F + 0x80) _ Dst HJc HARUC OK' PO' (fun x => NFo (F + 0x80) x (or_intror eq_refl))); [|exact PStC | exact TStC].
  destruct TStC as (_ & HBk & _).
  exact (crtC1_tree_notFP B ly3 S3 W3 _ mdC memC FPs (c_pos cx) Dst HARC Hin3 HFPs HBk). }
split; [exact SZst|].
split; [exact (pobj_kept_call B STK_pj_string (spZ regsC) FPs ly3 S3 U3 W3 memC mdC ly' S' _ W' mem' md' EV_pj_string _
  HJc HARUC OK' PO' (fun x => NFo (F + 0x80) x (or_intror eq_refl)) HFsh HH' PStC)|].
split; [exact HTV | exact HPV].
Qed.
End calls.

(* ================= helpers for the three pj_set calls ================= *)
(* a no-grow pj_set's trace is its one key allocation *)
Lemma crtC1_set_nc : forall n klen, n <> 8 -> 0 <= klen ->
  pj_set_c.set_trace n 8 klen = [PjGrammar.EAlloc (Z.to_nat (klen + 1))].
Proof.
intros n klen Hn Hk. unfold pj_set_c.set_trace.
replace (n =? 8) with false by (symmetry; apply Z.eqb_neq; exact Hn). reflexivity.
Qed.
Lemma crtC1_tr_facts : forall n klen, n <> 8 -> 0 <= klen ->
  PjGrammar.held (pj_set_c.set_trace n 8 klen) = klen + 1 /\
  Z.of_nat (length (pj_set_c.set_trace n 8 klen)) = 1 /\ crt_trlen (pj_set_c.set_trace n 8 klen) = 1 /\
  rd_live (pj_set_c.set_trace n 8 klen) = klen + 1 + HEAD /\ rd_ev (pj_set_c.set_trace n 8 klen) = EV_fuzz_malloc.
Proof.
intros n klen Hn Hk. unfold crt_trlen. rewrite (crtC1_set_nc n klen Hn Hk).
unfold rd_live, rd_ev. cbn [PjGrammar.held PjGrammar.held_ev fold_right PjGrammar.esize length].
rewrite Z2Nat.id by lia. repeat split; lia.
Qed.
(* the walk's trees as one permutation of the block list, one tree's blocks picked out *)
Lemma crtC1_perm_pick : forall (X A L D D1 D2 D3 : list (Z * Z)),
  Permutation X (A ++ L ++ rd_hblocks D) -> Permutation D (D1 ++ D2 ++ D3) ->
  Permutation X (rd_hblocks D2 ++ (rd_hblocks D1 ++ rd_hblocks D3 ++ A ++ L)).
Proof.
intros X A L D D1 D2 D3 HX HD.
eapply Permutation_trans; [exact HX|].
apply Permutation_trans with (A ++ L ++ rd_hblocks (D1 ++ D2 ++ D3)).
{ apply Permutation_app_head. apply Permutation_app_head. unfold rd_hblocks. apply Permutation_map. exact HD. }
rewrite !crtC1_rd_hblocks_app.
set (h1 := rd_hblocks D1). set (h2 := rd_hblocks D2). set (h3 := rd_hblocks D3).
apply Permutation_trans with ((h1 ++ h2 ++ h3) ++ A ++ L).
{ rewrite (app_assoc A L). apply Permutation_app_comm. }
rewrite <- !app_assoc. rewrite (app_assoc h1 h2), (app_assoc h2 h1). apply Permutation_app_tail. apply Permutation_app_comm.
Qed.
Section hlp. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : asyms.
Let LAWS : AR_laws tfibsegs B := AR_laws_ok tfibsegs B.
(* a block is not on both sides of a split of the block list *)
Lemma crtC1_hb_dup : forall ly S (W : world tfibsegs) mx md L1 L2 x,
  AR tfibsegs B ly S W mx md -> Permutation (ablocks B ly S) (L1 ++ L2) -> In x L1 -> In x L2 -> False.
Proof.
intros ly S W mx md L1 L2 x HAR HP H1 H2.
pose proof (crtC1_perm_sep B ly S W mx md L1 L2 HAR HP x x H1 H2) as D.
destruct x as (p, n).
assert (Hin : In (p, n) (ablocks B ly S))
  by (apply (Permutation_in _ (Permutation_sym HP)); apply in_or_app; left; exact H1).
destruct (al_blocks _ _ LAWS _ _ _ _ _ p n HAR Hin) as (_ & _ & _ & _ & _ & _ & Hn).
pose proof (YCbq.req_size_pos n ltac:(lia)) as (Hr & _).
unfold zdisjoint in D. cbn [fst snd] in D. lia.
Qed.
(* a reader block's bytes (head included) are outside crt's frame, and outside the image *)
Lemma crtC1_rblk_frame : forall ly S (W : world tfibsegs) mx md m pos a0 k0 x,
  AR tfibsegs B ly S W mx md -> In (3, pos) (frames S) -> fs_rblock tfibsegs B ly S W m a0 k0 ->
  a0 - HEAD <= x < a0 + k0 -> ~ (frame_addr ly 3 pos <= x < frame_addr ly 3 pos + 512).
Proof.
intros ly S W mx md m pos a0 k0 x HAR Hfr (Hin & _ & Hk & _) Hx Hf.
pose proof (sep_block_frame tfibsegs B LAWS ly S W mx md _ _ 3 pos HAR Hin Hfr) as D.
unfold zdisjoint in D. rewrite crt_frame3 in D. cbn [fst snd] in D.
unfold req_size in D. destruct (Z.eqb_spec (k0 + HEAD) 0); unfold HEAD in *; lia.
Qed.
Lemma crtC1_rblk_img : forall ly S (W : world tfibsegs) mx md m a0 k0 x,
  AR tfibsegs B ly S W mx md -> fs_rblock tfibsegs B ly S W m a0 k0 ->
  a0 - HEAD <= x < a0 + k0 -> x < 0x10000 \/ FS_IMG_END <= x.
Proof.
intros ly S W mx md m a0 k0 x HAR (Hin & _ & Hk & _) Hx.
destruct (fsw_ablock_off_img B ly S W mx md _ _ HAR Hin) as [X | X];
  unfold req_size in X; destruct (Z.eqb_spec (k0 + HEAD) 0); unfold HEAD in *; lia.
Qed.
End hlp.

(* pj_set's footprint at crt's call: obj's header tail, val's 56 bytes, the old kids / keys blocks, the statics *)
Definition crtC1_Dold0 (kids keys : Z) : list (Z * Z) := ReaderRes.kids_blk kids 8 ++ ReaderRes.keys_blk 6 keys 8.
Definition crtC1_FPset (cx : crt_cx) (oo ow kids keys : Z) : list (Z * Z) :=
  [(crt_F cx + oo + 24, crt_F cx + oo + 56); (crt_F cx + ow, crt_F cx + ow + 56)] ++
  ablocks_fp (rd_hblocks (crtC1_Dold0 kids keys)) ++ FS_PSTAT_FP.
Definition crtC1_tr (ms : list (list Z * PjTree.jv)) (kname : list Z) : list PjGrammar.ev :=
  pj_set_c.set_trace (Z.of_nat (length ms)) 8 (Z.of_nat (length kname)).

Section calls2. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable SK : YI16.sink_head.
Variable B : asyms.
Let LAWS : AR_laws tfibsegs B := AR_laws_ok tfibsegs B.
Hypothesis IMG : fs_img_facts tfibsegs B.
Hypothesis PJS : @pj_string_spec fx rc SK tfibsegs B.
Hypothesis PJSET : @pj_set_spec fx rc SK tfibsegs B.

(* ---- one no-grow pj_set (&F[oo], key, &F[ow]) at crt's call site, generic over the trees: obj holds ms on Dobj
   with cap = 8 and n = |ms| < 8, val holds tv on Dval, the boundary's tree blocks are D ~ Dobj ++ Dval ++ Doth.
   The callee's SRr, its FP relation and flag-word safety, and from any post state the boundary core at
   D' = Doth ++ Do (Do ~ the key block :: Dobj ++ Dval, obj's new tree), val zeroed, and what the caller needs to keep
   its other data across the call (the footprint misses every other frame byte and every Doth block, and no shadow
   byte). St11 / St13 / St14 of d25a984c903 (sd11.v, sd13.v, sd14.v). ---- *)
Lemma crtC1_pjset_call : forall cx E k ly3 S3 U3 (W3 : world tfibsegs) regsC memC mdC ssC r oo ow kaddr kname
    (ms : list (list Z * PjTree.jv)) tv Dobj Dval Doth D num str kids keys Kb CNTb LIVEb same nsame dec live peak cnt
    (Q : env -> Z -> alayout -> astate -> list (Z * Z) -> world tfibsegs -> machine_state -> Model -> Prop),
  crt_base B cx ->
  crt_J SK B cx ly3 S3 W3 (unpoison U3 memC) mdC k -> ARU tfibsegs B ly3 S3 U3 W3 memC mdC ->
  frames S3 = (3, c_pos cx) :: frames (c_S cx) ->
  (forall rr : bv 5, YK11.getr regsC rr = sv_denot E (sr_get (ss_regs ssC) rr)) -> crt_ssave ssC ->
  fpreU tfibsegs B STK_pj_set ly3 S3 U3 W3 regsC memC mdC (crt_ch1 cx) ->
  YK11.getr regsC 10%bv = w64 (crt_F cx + oo) -> YK11.getr regsC 11%bv = w64 kaddr ->
  YK11.getr regsC 12%bv = w64 (crt_F cx + ow) ->
  0 <= oo -> oo + 56 <= 0x118 -> 0 <= ow -> ow + 56 <= 0x118 -> (oo + 56 <= ow \/ ow + 56 <= oo) ->
  In (kaddr, kname) FS_RO_STRS -> 0x10000 <= kaddr -> kaddr + Z.of_nat (length kname) + 1 <= FS_IMG_END ->
  Z.of_nat (length kname) + 1 + HEAD < MALLOC_MAX -> ~ In kname (map fst ms) -> (length ms < 8)%nat ->
  crtC1_corex B cx E k ly3 S3 U3 W3 memC D Kb CNTb LIVEb same nsame dec live peak cnt ->
  Permutation D (Dobj ++ Dval ++ Doth) -> 0 <= rd_sum Doth ->
  rtree tfibsegs B ly3 S3 W3 memC (crt_F cx + oo) (PjTree.JObj ms) Dobj ->
  pobj tfibsegs B ly3 S3 W3 memC (crt_F cx + oo) ->
  PjStruct.pj_hdr tfibsegs (mrestrict (w_H W3) memC) (crt_F cx + oo) 6 num str kids keys (Z.of_nat (length ms)) 8 ->
  rtree tfibsegs B ly3 S3 W3 memC (crt_F cx + ow) tv Dval -> pobj tfibsegs B ly3 S3 W3 memC (crt_F cx + ow) ->
  Kb + rd_ev (crtC1_tr ms kname) <= K_82218 cx -> CNTb + crt_trlen (crtC1_tr ms kname) <= CNT_82218 cx ->
  LIVEb + rd_live (crtC1_tr ms kname) <= LIVE_82218 cx ->
  (forall a ly' S' (W' : world tfibsegs) regs' mem' md' Do peak',
     ajournal tfibsegs B STK_pj_set (spZ regsC) (crtC1_FPset cx oo ow kids keys) ly3 S3 W3 (unpoison U3 memC) mdC []
       ly' S' W' (unpoison (U3 ++ [(a - HEAD, HEAD)]) mem') md' (rd_ev (crtC1_tr ms kname)) ->
     upoison_ok B ly' S' (U3 ++ [(a - HEAD, HEAD)]) -> upoisoned tfibsegs W' mem' (U3 ++ [(a - HEAD, HEAD)]) ->
     aregs_preserved regsC regs' ->
     crt_J SK B cx ly' S' W' (unpoison (U3 ++ [(a - HEAD, HEAD)]) mem') md' (k + rd_ev (crtC1_tr ms kname)) ->
     ARU tfibsegs B ly' S' (U3 ++ [(a - HEAD, HEAD)]) W' mem' md' ->
     crtC1_corex B cx (Ereg regs' (crt_extra cx)) (k + rd_ev (crtC1_tr ms kname)) ly' S' (U3 ++ [(a - HEAD, HEAD)]) W'
       mem' (Doth ++ Do) (Kb + rd_ev (crtC1_tr ms kname)) (CNTb + crt_trlen (crtC1_tr ms kname))
       (LIVEb + rd_live (crtC1_tr ms kname)) same nsame dec (live + (Z.of_nat (length kname) + 1)) peak' (cnt + 1) ->
     rtree tfibsegs B ly' S' W' mem' (crt_F cx + oo) (PjTree.JObj (PjTree.pj_set_model ms kname tv)) Do ->
     Permutation Do ((a, Z.of_nat (length kname) + 1) :: Dobj ++ Dval) ->
     PjStruct.pj_zero tfibsegs (mrestrict (w_H W') mem') (crt_F cx + ow) ->
     pobj tfibsegs B ly' S' W' mem' (crt_F cx + oo) -> pobj tfibsegs B ly' S' W' mem' (crt_F cx + ow) ->
     (forall x, crt_F cx <= x < crt_F cx + 512 -> ~ (crt_F cx + oo + 24 <= x < crt_F cx + oo + 56) ->
        ~ (crt_F cx + ow <= x < crt_F cx + ow + 56) -> ~ inFP (crtC1_FPset cx oo ow kids keys) x) ->
     (forall a0 k0 x, In (a0, k0) Doth -> a0 - HEAD <= x < a0 + k0 -> ~ inFP (crtC1_FPset cx oo ow kids keys) x) ->
     (forall x, inFP (crtC1_FPset cx oo ow kids keys) x -> ~ (SHADOW_OFF <= x < SHADOW_OFF + 2 ^ 44)) ->
     Q (Ereg regs' (crt_extra cx)) (k + rd_ev (crtC1_tr ms kname)) ly' S' (U3 ++ [(a - HEAD, HEAD)]) W'
       (mkst regs' (Z_to_bv 64 r) mem' (seg_rom tfibsegs)) md') ->
  exists FPc kc (P : world tfibsegs -> config -> Prop),
    SRr tfibsegs W3 (cfg_at tfibsegs 0x83adc regsC memC mdC) P /\
    fsw_fp_sub B (c_ly cx) (c_S cx) ly3 S3 [(3, c_pos cx)] FS_PSTAT_FP FPc /\
    (forall a, crt_F cx + fs_frame_bytes 3 - 8 <= a < crt_F cx + fs_frame_bytes 3 -> ~ inFP FPc a) /\
    (forall W' c', P W' c' -> exists ly' S' U' regs' mem' md',
       c' = mkCfg (mkst regs' (YK11.getr regsC 1%bv) mem' (seg_rom tfibsegs)) md' /\
       ajournal tfibsegs B STK_pj_set (spZ regsC) FPc ly3 S3 W3 (unpoison U3 memC) mdC [] ly' S' W'
         (unpoison U' mem') md' kc /\
       upoison_ok B ly' S' U' /\ upoisoned tfibsegs W' mem' U' /\ aregs_preserved regsC regs' /\
       (crt_J SK B cx ly' S' W' (unpoison U' mem') md' (k + kc) -> ARU tfibsegs B ly' S' U' W' mem' md' ->
        Q (Ereg regs' (crt_extra cx)) (k + kc) ly' S' U' W' (mkst regs' (Z_to_bv 64 r) mem' (seg_rom tfibsegs)) md')).
Proof.
intros cx E k ly3 S3 U3 W3 regsC memC mdC ssC r oo ow kaddr kname ms tv Dobj Dval Doth D num str kids keys Kb CNTb LIVEb
  same nsame dec live peak cnt Q HB HJC HARUC Hfr RG SV HPREc R10 R11 R12 Ho0 Ho1 Hw0 Hw1 Hsep Hkin Hk0 Hk1 Hkm Hnin
  Hlen HC HPD HDoth TO PO HH TV PV EKb ECb ELb CONT.
pose proof (ARU_AR tfibsegs B _ _ _ _ _ _ HARUC) as HARC.
destruct (crt_F_facts SK B cx ly3 S3 U3 W3 memC mdC k HJC HARUC Hfr) as (_ & F4096 & Fceil & _ & _ & _).
pose proof HJC as (_ & HlyC & _ & _ & _ & _ & HnevC & _).
pose proof (crt_F_ly cx _ ly3 HlyC) as EF.
assert (Hin3 : In (3, c_pos cx) (frames S3)) by (rewrite Hfr; left; reflexivity).
pose proof HC as HCd. cbv beta zeta delta [crtC1_corex] in HCd.
destruct HCd as (C10 & C18 & C20 & C21 & C27 & C23 & C24 & C25 & C22 & C19 & PB & PU & HHU & TB & TZ & TC & DB & DZ & P140 &
  VM & RA & GL & LV & BB & CN & KB).
set (F := crt_F cx) in *.
set (klen := Z.of_nat (length kname)) in *.
set (Dold0 := crtC1_Dold0 kids keys) in *.
set (FPs := crtC1_FPset cx oo ow kids keys) in *.
assert (Hn8 : Z.of_nat (length ms) <> 8) by lia.
destruct (crtC1_tr_facts (Z.of_nat (length ms)) klen Hn8 ltac:(lia)) as (Eheld & Elen & Etrl & Elive & Eev).
change (pj_set_c.set_trace (Z.of_nat (length ms)) 8 klen) with (crtC1_tr ms kname) in Eheld, Elen, Etrl, Elive, Eev.
pose proof TO as (TN & TBk & _). pose proof TV as (_ & TVk & _).
destruct (crt_dold0_split _ _ _ _ _ _ _ _ _ _ _ TN HH) as (Di & EDo).
assert (HIncl : incl Dold0 Dobj) by (rewrite EDo; apply incl_appl, incl_refl).
assert (HY : forall b, In b (rd_hblocks Dold0) -> In b (rd_hblocks D)).
{ intros b Hb. unfold rd_hblocks in *. apply in_map_iff in Hb as (b0 & Eb & Hb0). apply in_map_iff.
  exists b0. split; [exact Eb|].
  apply (Permutation_in _ (Permutation_sym HPD)). apply in_or_app; left. exact (HIncl _ Hb0). }
assert (Hblk : forall bk, In bk (rd_hblocks Dold0) ->
  In bk (ablocks B ly3 S3) /\ ~ In bk (ablocks B (c_ly cx) (c_S cx))).
{ intros bk Hbk. split.
  - apply (Permutation_in _ (Permutation_sym PB)). apply in_or_app; right. apply in_or_app; right. exact (HY _ Hbk).
  - intros Hc. apply (crtC1_hb_dup B ly3 S3 W3 _ mdC _ _ bk HARC PB Hc). apply in_or_app; right. exact (HY _ Hbk). }
assert (HYb : forall b, In b (rd_hblocks Dold0) -> In b (ablocks B ly3 S3)) by (intros b Hb; exact (proj1 (Hblk b Hb))).
assert (HFPs : crtC1_fp ly3 (c_pos cx) FPs (rd_hblocks Dold0)).
{ intros x Hx. unfold FPs, crtC1_FPset in Hx. apply inFP_app in Hx as [Hx | Hx].
  - left. rewrite EF. apply inFP_cons in Hx as [Hx | Hx]; [fold F; lia|].
    apply inFP_cons in Hx as [Hx | Hx]; [fold F; lia | exfalso; exact (inFP_nil x Hx)].
  - apply inFP_app in Hx as [Hx | Hx].
    + right; right. destruct Hx as (rg & Hrg & Hx). unfold ablocks_fp in Hrg.
      apply in_map_iff in Hrg as (b & <- & Hb). cbn [fst snd] in Hx. exists b. split; [exact Hb | exact Hx].
    + right; left; exact Hx. }
destruct (crtC_key SK B IMG cx k ly3 S3 U3 W3 (mkst regsC (Z_to_bv 64 0x83adc) memC (seg_rom tfibsegs)) mdC
  kaddr kname HB HJC HARUC Hkin) as (KOK & KKEPT).
pose proof (fsw_sp B _ _ _ _ _ _ _ _ _ (proj1 HPREc)) as (_ & Hsp & _ & _).
pose proof (crtC1_live_le B cx E k ly3 S3 U3 W3 _ mdC memC D Kb CNTb LIVEb same nsame dec live peak cnt HARC HC) as Hlv.
pose proof (crtC1_tb2_len (c_bs cx)) as Etb. pose proof (crtC1_bs_le_dec (c_bs cx)) as Ebs.
pose proof (crt_live0 B cx HB) as HL0.
assert (ED : rd_sum D = rd_sum Dobj + rd_sum Dval + rd_sum Doth).
{ change (rd_sum D) with (YCbq.bsum D). rewrite (YCbq.bsum_perm _ _ HPD).
  change (YCbq.bsum (Dobj ++ Dval ++ Doth)) with (rd_sum (Dobj ++ Dval ++ Doth)). rewrite !crt_rd_sum_app. lia. }
pose proof (crt_dold0_le B ly3 S3 W3 memC (F + oo) ms Dobj num str kids keys _ 8 (rd_sum ([] ++ Dobj ++ [])) 0 [] []
  TO HH (fun a0 k0 H => match H with end) ltac:(lia) eq_refl) as HD0.
rewrite app_nil_r in HD0. cbn [app] in HD0.
pose proof (crt_rd_sum_pos B ly3 S3 W3 memC Dval TVk) as HVs.
exists FPs, (rd_ev (crtC1_tr ms kname)).
pose proof (PJSET ly3 S3 U3 W3 regsC memC mdC (crt_ch1 cx) (F + oo) kaddr (F + ow) ms tv Dobj Dval num str kids keys
  (Z.of_nat (length ms)) 8 kname live peak cnt SIZE_MAXZ) as SP.
cbv zeta in SP.
eexists. split.
{ apply SP; clear SP.
  - exact HPREc.
  - exact HHU.
  - exact R10.
  - exact R11.
  - exact R12.
  - exact TO.
  - exact PO.
  - exact HH.
  - lia.
  - intros x Hx. unfold rd_heads in Hx. apply in_map_iff in Hx as (b & <- & Hb).
    apply (Permutation_in _ (Permutation_sym PU)). apply in_or_app; right. apply in_or_app; right.
    unfold rd_heads. apply in_map_iff. exists b. split; [reflexivity|].
    apply (Permutation_in _ (Permutation_sym HPD)). apply in_or_app; left.
    exact (HIncl _ Hb).
  - exact TV.
  - exact PV.
  - intros bk Hv Ho.
    apply (crtC1_hb_dup B ly3 S3 W3 _ mdC (rd_hblocks Dval) (rd_hblocks Dobj ++ rd_hblocks Doth ++
      ablocks B (c_ly cx) (c_S cx) ++ _) (fst bk - HEAD, snd bk + HEAD) HARC (crtC1_perm_pick _ _ _ _ Dobj Dval Doth PB HPD)).
    + unfold rd_hblocks. exact (in_map (fun b => (fst b - HEAD, snd b + HEAD)) _ bk Hv).
    + apply in_or_app; left. unfold rd_hblocks. exact (in_map (fun b => (fst b - HEAD, snd b + HEAD)) _ bk Ho).
  - intros x Hx [Hx' | ((a0, k0) & Hb & Hh)]; [lia|]. unfold PjStruct.pj_holds in Hh. cbn [fst snd] in Hh.
    apply (crtC1_rblk_frame B ly3 S3 W3 _ mdC memC (c_pos cx) a0 k0 x HARC Hin3 (TBk a0 k0 Hb));
      [unfold HEAD; lia | rewrite EF; fold F; lia].
  - intros (a0, k0) x Hb Hh Hx. unfold PjStruct.pj_holds in Hh. cbn [fst snd] in Hh.
    apply (crtC1_rblk_frame B ly3 S3 W3 _ mdC memC (c_pos cx) a0 k0 x HARC Hin3 (TVk a0 k0 Hb));
      [unfold HEAD; lia | rewrite EF; fold F; lia].
  - left. lia.
  - left. lia.
  - exact KOK.
  - exact KKEPT.
  - intros x Hx. split.
    + intros [Hx' | ((a0, k0) & Hb & Hh)].
      * destruct (fsw_pobj_off_img B ly3 S3 W3 _ mdC memC _ HARC PO) as [X | X]; lia.
      * unfold PjStruct.pj_holds in Hh. cbn [fst snd] in Hh.
        destruct (crtC1_rblk_img B ly3 S3 W3 _ mdC memC a0 k0 x HARC (TBk a0 k0 Hb) ltac:(unfold HEAD; lia))
          as [X | X]; lia.
    + intros [Hx' | ((a0, k0) & Hb & Hh)].
      * destruct (fsw_pobj_off_img B ly3 S3 W3 _ mdC memC _ HARC PV) as [X | X]; lia.
      * unfold PjStruct.pj_holds in Hh. cbn [fst snd] in Hh.
        destruct (crtC1_rblk_img B ly3 S3 W3 _ mdC memC a0 k0 x HARC (TVk a0 k0 Hb) ltac:(unfold HEAD; lia))
          as [X | X]; lia.
  - exact Hnin.
  - exact GL.
  - change (pj_set_c.set_trace (Z.of_nat (length ms)) 8 klen) with (crtC1_tr ms kname).
    exact (crtC1_quiet B cx cnt CNTb (Z.of_nat (length (crtC1_tr ms kname))) HB CN ltac:(lia) ECb).
  - fold Dold0. rewrite LV, ED. lia.
  - exact Hkm.
  - intros Heq. lia.
  - change (pj_set_c.set_trace (Z.of_nat (length ms)) 8 klen) with (crtC1_tr ms kname).
    exact (crtC1_live_room B cx live LIVEb _ HB Hlv ELb).
  - change (pj_set_c.set_trace (Z.of_nat (length ms)) 8 klen) with (crtC1_tr ms kname).
    exact (crtC1_nev B cx k S3 Kb _ HB HnevC KB EKb).
  - change (pj_set_c.set_trace (Z.of_nat (length ms)) 8 klen) with (crtC1_tr ms kname).
    exact (crtC1_bb B cx S3 LIVEb _ HB BB ELb). }
split.
{ pose proof (crtC_fpsub_pjset B (c_ly cx) (c_S cx) ly3 S3 (c_pos cx) oo ow Dold0 Ho0 ltac:(lia) Hw0 ltac:(lia) Hblk) as X.
  rewrite EF in X. exact X. }
split.
{ intros a Ha. apply (crtC1_notFP B ly3 S3 W3 _ mdC FPs (c_pos cx) (rd_hblocks Dold0) [] (ablocks B ly3 S3) a HARC Hin3
    HFPs (Permutation_refl _) HYb).
  right. rewrite EF. rewrite crt_frame3 in Ha. fold F. lia. }
intros W' c' (k' & y' & cap' & Dold & Dnew & Dr & Do & Ug & a & HGR & HPDr & HPDo & HFP).
destruct HGR as [(Hlt & -> & -> & -> & -> & -> & ->) | (Heq & _)]; [|exfalso; lia].
destruct HFP as (ly' & S' & regs' & mem' & md' & -> & HJc & OK' & PO' & HP & HQ).
destruct HQ as (R10' & Ha & HAB & TO' & HZ & POo & POw & _ & (peak' & Hpk & HGL')).
exists ly', S', (U3 ++ [(a - HEAD, HEAD)]), regs', mem', md'.
split; [reflexivity|]. split; [exact HJc|]. split; [exact OK'|]. split; [exact PO'|]. split; [exact HP|].
intros HJ' HARU'.
change (pj_set_c.set_trace (Z.of_nat (length ms)) 8 klen) with (crtC1_tr ms kname) in *.
assert (Eh' : PjGrammar.held (pj_set_c.set_trace (Z.of_nat (length ms)) 8 (Z.of_nat (length kname))) = klen + 1)
  by exact Eheld.
assert (El' : Z.of_nat (length (pj_set_c.set_trace (Z.of_nat (length ms)) 8 (Z.of_nat (length kname)))) = 1)
  by exact Elen.
rewrite Eh', El' in HGL'.
pose proof (crtC1_regs_kept E ssC regsC regs' (crt_extra cx) RG SV HP) as RS.
pose proof (crtC1_a0_post regs' (crt_extra cx) R10') as R10E.
assert (HDo : Permutation Do ((a, klen + 1) :: Dobj ++ Dval)).
{ eapply Permutation_trans; [exact HPDo|]. cbn [app]. apply perm_skip. apply Permutation_app_tail.
  apply Permutation_sym. exact HPDr. }
assert (HC' : crtC1_corex B cx (Ereg regs' (crt_extra cx)) (k + rd_ev (crtC1_tr ms kname)) ly' S' (U3 ++ [(a - HEAD, HEAD)])
  W' mem' (Doth ++ Do) (Kb + rd_ev (crtC1_tr ms kname)) (CNTb + crt_trlen (crtC1_tr ms kname))
  (LIVEb + rd_live (crtC1_tr ms kname)) same nsame dec (live + rd_sum [(a, klen + 1)]) peak' (cnt + 1)).
{ apply (crtC1_core_call SK B cx E (Ereg regs' (crt_extra cx)) k (rd_ev (crtC1_tr ms kname)) ly3 S3 U3 W3 memC mdC
    STK_pj_set (spZ regsC) FPs ly' S' (U3 ++ [(a - HEAD, HEAD)]) W' mem' md' D [(a, klen + 1)] (Doth ++ Do)
    (rd_hblocks Dold0) Kb CNTb LIVEb _ _ _ same nsame dec live peak cnt peak' 1
    HC HARUC Hfr EF HJc OK' PO' HFPs HY R10E RS).
  - unfold rd_hblocks in HAB |- *. cbn [map app fst snd] in HAB |- *. rewrite app_nil_r in HAB. exact HAB.
  - unfold rd_heads. cbn [map fst]. apply Permutation_refl.
  - constructor; [cbn [snd]; lia | constructor].
  - apply Permutation_trans with ((Do ++ Doth)); [apply Permutation_app_comm|].
    apply Permutation_trans with ((((a, klen + 1) :: Dobj ++ Dval) ++ Doth)); [apply Permutation_app_tail; exact HDo|].
    cbn [app]. rewrite <- app_assoc.
    apply Permutation_trans with ((a, klen + 1) :: D); [apply perm_skip; apply Permutation_sym; exact HPD|].
    apply Permutation_cons_append.
  - replace (live + rd_sum [(a, klen + 1)]) with (live + (klen + 1)) by (unfold rd_sum; cbn [fold_right snd]; lia).
    exact HGL'.
  - lia.
  - lia.
  - rewrite Etrl. lia.
  - rewrite Elive. change (YCbq.bsum (rd_hblocks [(a, klen + 1)])) with (klen + 1 + HEAD + 0). lia. }
replace (live + rd_sum [(a, klen + 1)]) with (live + (klen + 1)) in HC' by (unfold rd_sum; cbn [fold_right snd]; lia).
apply (CONT a ly' S' W' regs' mem' md' Do peak' HJc OK' PO' HP HJ' HARU' HC' TO' HDo HZ POo POw).
- intros x Hx N1 N2 Hin. unfold FPs, crtC1_FPset in Hin. apply inFP_app in Hin as [Hin | Hin].
  + apply inFP_cons in Hin as [Hin | Hin]; [fold F in Hin; lia|].
    apply inFP_cons in Hin as [Hin | Hin]; [fold F in Hin; lia | exact (inFP_nil x Hin)].
  + apply inFP_app in Hin as [Hin | Hin].
    * destruct Hin as (rg & Hrg & Hx'). unfold ablocks_fp in Hrg. apply in_map_iff in Hrg as ((p, n) & <- & Hb).
      cbn [fst snd] in Hx'.
      pose proof (sep_block_frame tfibsegs B LAWS ly3 S3 W3 _ mdC p n 3 (c_pos cx) HARC (HYb _ Hb) Hin3) as Dj.
      unfold zdisjoint in Dj. rewrite crt_frame3, EF in Dj. cbn [fst snd] in Dj. fold F in Dj. lia.
    * exact (frm_img tfibsegs B LAWS ly3 S3 W3 _ mdC 3 (c_pos cx) x HARC Hin3 ltac:(rewrite EF, crt_frame3; fold F; lia)
        (crt_pstat_img x Hin)).
- intros a0 k0 x Hb Hx.
  assert (HPD' : Permutation D ((Dobj ++ Dval) ++ Doth ++ [])) by (rewrite app_nil_r, <- app_assoc; exact HPD).
  pose proof (crtC1_perm_pick _ _ _ _ (Dobj ++ Dval) Doth [] PB HPD') as HPP.
  apply (crtC1_notFP B ly3 S3 W3 _ mdC FPs (c_pos cx) (rd_hblocks Dold0) _ _ x HARC Hin3 HFPs HPP).
  + intros b Hb'. apply in_or_app; left. rewrite crtC1_rd_hblocks_app. apply in_or_app; left.
    unfold rd_hblocks in *. apply in_map_iff in Hb' as (b0 & Eb & Hb0). apply in_map_iff. exists b0.
    split; [exact Eb | exact (HIncl _ Hb0)].
  + left. exists (a0 - HEAD, k0 + HEAD). split.
    * unfold rd_hblocks. exact (in_map (fun b => (fst b - HEAD, snd b + HEAD)) _ (a0, k0) Hb).
    * cbn [fst snd]. unfold req_size. destruct (Z.eqb_spec (k0 + HEAD) 0); unfold HEAD in *; lia.
- exact (crtC1_FP_noshadow B ly3 S3 W3 _ mdC FPs (c_pos cx) (rd_hblocks Dold0) HARC Hin3 HFPs HYb).
Qed.

(* a byte of crt's frame is a byte of a live frame at the call (the LB side of the byte keeps) *)
Lemma crtC1_LBfr : forall cx ly3 S3 a, frames S3 = (3, c_pos cx) :: frames (c_S cx) ->
  frame_addr ly3 3 (c_pos cx) = crt_F cx -> crt_F cx <= a < crt_F cx + 512 ->
  (exists p n, In (p, n) (ablocks B ly3 S3) /\ p <= a < p + req_size n) \/
  (exists cid pos, In (cid, pos) (frames S3) /\ frame_addr ly3 cid pos <= a < frame_addr ly3 cid pos + fs_frame_bytes cid).
Proof.
intros cx ly3 S3 a Hfr EF Ha. right. exists 3, (c_pos cx). split; [rewrite Hfr; left; reflexivity|].
rewrite EF, crt_frame3. exact Ha.
Qed.

(* ---- segment 21: pj_set (&state, "context", &v) at B 0x82330 (A 0x821d4); St11 -> St12 (d25a984c903 sd11.v): the
   state becomes crt_s2 on its old blocks + the key block + v's block, v is zeroed; the document is kept ---- *)
Lemma crtC1_hcall_1c0 : crt_hcall SK B crtC_sc_1c0 0x83adc 0x82334 STK_pj_set (crtC1_INV_1c0 B) (crtC1_INV_1d8 B).
Proof.
intros cx E k ly3 S3 U3 W3 ms3 md3 regsC memC mdC HB HE HINV HJC HARUC Hfr HSB RG HPREc HFRL HTOPc.
destruct crtC1_site_1c0 as ((_ & _ & _ & _ & G1 & _) & G10 & G11 & G12).
destruct crtC1_ssave_all as (_ & SV & _).
destruct HINV as (Ddoc & Dst & a1 & same & nsame & dec & live & peak & cnt & HC &
  (TDoc & (dnum & dstr & dkids & dkeys & HDh) & PDoc) & TSt & (sk & sy & se & sv & SZst) & PSt & TV & PV).
pose proof (ARU_AR tfibsegs B _ _ _ _ _ _ HARUC) as HARC.
destruct (crt_F_facts SK B cx ly3 S3 U3 W3 memC mdC k HJC HARUC Hfr) as (_ & F4096 & Fceil & _ & _ & _).
pose proof HJC as (_ & HlyC & _).
pose proof (crt_F_ly cx _ ly3 HlyC) as EF.
pose proof HC as HCd. cbv beta zeta delta [crtC1_corex] in HCd. destruct HCd as (_ & _ & _ & _ & C27 & C23 & _).
set (F := crt_F cx) in *.
pose proof (crtC1_core_below B cx E k ly3 S3 U3 W3 _ mdC (ms_mem ms3) memC _ _ _ _ _ _ _ _ _ _ HARC ltac:(lia) Fceil HSB HC)
  as HCC.
pose proof (crtC1_rtree_below B ly3 S3 W3 _ mdC (ms_mem ms3) memC (F + 0x20) _ Ddoc HARC HSB ltac:(lia) ltac:(lia) TDoc)
  as TDocC.
pose proof (crtC1_rtree_below B ly3 S3 W3 _ mdC (ms_mem ms3) memC (F + 0x80) _ Dst HARC HSB ltac:(lia) ltac:(lia) TSt)
  as TStC.
pose proof (crtC1_rtree_below B ly3 S3 W3 _ mdC (ms_mem ms3) memC (F + 0xe0) _ _ HARC HSB ltac:(lia) ltac:(lia) TV)
  as TVC.
pose proof (pobj_below B ly3 S3 W3 _ mdC (ms_mem ms3) memC _ HARC HSB PDoc) as PDocC.
pose proof (pobj_below B ly3 S3 W3 _ mdC (ms_mem ms3) memC _ HARC HSB PSt) as PStC.
pose proof (pobj_below B ly3 S3 W3 _ mdC (ms_mem ms3) memC _ HARC HSB PV) as PVC.
pose proof (crtC1_pj_hdr_below W3 (ms_mem ms3) memC (F + 0x20) _ _ _ _ _ _ _ HSB ltac:(lia) ltac:(lia) HDh) as HDhC.
destruct (crtC1_cap8 B ly3 S3 W3 memC (F + 0x80) check_round_trip_stages_b.crt_s1 Dst [(se, 9); (sv, 7)] sk sy TStC
  ltac:(cbv [check_round_trip_stages_b.crt_s1 length]; lia) SZst
  ltac:(constructor; [cbn [snd]; lia | constructor; [cbn [snd]; lia | constructor]])) as (num & str & kids & keys & HHs & _).
assert (R10 : YK11.getr regsC 10%bv = w64 (F + 0x80)) by (rewrite RG, G10, fsw_SOff0; exact C23).
assert (R11 : YK11.getr regsC 11%bv = w64 0x20fa0) by (rewrite RG, G11; reflexivity).
assert (R12 : YK11.getr regsC 12%bv = w64 (F + 0xe0)) by (rewrite RG, G12, fsw_SOff0; exact C27).
pose proof (crtC1_steps cx) as (_ & _ & _ & T1 & T2 & T3 & L1 & L2 & X2 & X4 & Les).
assert (Em : PjTree.pj_set_model check_round_trip_stages_b.crt_s1 check_round_trip_stages_b.K_CONTEXT
  (PjTree.JStr check_round_trip_stages_b.V_PRESET) = check_round_trip_stages_b.crt_s2) by (vm_compute; reflexivity).
apply (crtC1_pjset_call cx E k ly3 S3 U3 W3 regsC memC mdC crtC_sc_1c0 0x82334 0x80 0xe0 0x20fa0
  check_round_trip_stages_b.K_CONTEXT check_round_trip_stages_b.crt_s1 (PjTree.JStr check_round_trip_stages_b.V_PRESET)
  Dst [(a1, 7)] Ddoc (Ddoc ++ Dst ++ [(a1, 7)]) num str kids keys (crtC1_KC_1c0 cx) (crtC1_CNT_1c0 cx)
  (crtC1_LIVE_1c0 cx) same nsame dec live peak cnt (crtC1_INV_1d8 B cx) HB HJC HARUC Hfr RG SV HPREc R10 R11 R12).
- lia.
- lia.
- lia.
- lia.
- lia.
- exact crtC_in_context.
- lia.
- apply Z.leb_le. vm_compute. reflexivity.
- apply Z.ltb_lt. vm_compute. reflexivity.
- vm_compute. intros [H | H]; [discriminate H | exact H].
- apply Nat.ltb_lt. vm_compute. reflexivity.
- exact HCC.
- rewrite (app_assoc Dst). apply Permutation_app_comm.
- exact (crt_rd_sum_pos B ly3 S3 W3 memC Ddoc (proj1 (proj2 TDocC))).
- exact TStC.
- exact PStC.
- exact HHs.
- exact TVC.
- exact PVC.
- change (crtC1_tr check_round_trip_stages_b.crt_s1 check_round_trip_stages_b.K_CONTEXT) with (pj_set_c.set_trace 1 8 7).
  unfold crtC1_KC_1c0, K_82218. lia.
- change (crtC1_tr check_round_trip_stages_b.crt_s1 check_round_trip_stages_b.K_CONTEXT) with (pj_set_c.set_trace 1 8 7).
  unfold crtC1_CNT_1c0, CNT_82218. unfold crt_trlen in *. lia.
- change (crtC1_tr check_round_trip_stages_b.crt_s1 check_round_trip_stages_b.K_CONTEXT) with (pj_set_c.set_trace 1 8 7).
  unfold crtC1_LIVE_1c0, LIVE_82218. rewrite X2, X4. unfold HEAD. lia.
- intros a ly' S' W' regs' mem' md' Do peak' HJc OK' PO' HP HJ' HARU' HC' TO' HDo HZ POo POw NFfr NFoth HFsh.
  pose proof HC' as HCd'. cbv beta zeta delta [crtC1_corex] in HCd'.
  destruct HCd' as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HH' & _).
  set (FPs := crtC1_FPset cx 0x80 0xe0 kids keys) in *.
  assert (NFd : forall x, F + 0x20 <= x < F + 0x20 + 56 -> ~ inFP FPs x)
    by (intros x Hx; apply NFfr; [lia | lia | lia]).
  exists Ddoc, Do, same, nsame, dec, (live + (Z.of_nat (length check_round_trip_stages_b.K_CONTEXT) + 1)), peak', (cnt + 1).
  split; [exact HC'|].
  split.
  { split; [|split].
    - apply (rtree_kept_call B STK_pj_set (spZ regsC) FPs ly3 S3 U3 W3 memC mdC ly' S' _ W' mem' md' _
        (F + 0x20) _ Ddoc HJc HARUC OK' PO' NFd); [exact NFoth | exact PDocC | exact TDocC].
    - exists dnum, dstr, dkids, dkeys.
      exact (crtC1_pj_hdr_kept_call SK B STK_pj_set (spZ regsC) FPs ly3 S3 U3 W3 memC mdC ly' S' _ W' mem' md' _
        _ _ _ _ _ _ _ _ HJc HARUC OK' PO'
        (fun a0 (Ha0 : F + 0x20 <= a0 < F + 0x20 + 56) =>
           conj (crtC1_LBfr cx ly3 S3 a0 Hfr EF ltac:(lia)) (NFd a0 Ha0)) HDhC).
    - exact (pobj_kept_call B STK_pj_set (spZ regsC) FPs ly3 S3 U3 W3 memC mdC ly' S' _ W' mem' md' _ _
        HJc HARUC OK' PO' NFd HFsh HH' PDocC). }
  split; [rewrite Em in TO'; exact TO'|].
  split.
  { exists sk, sy, se, sv, a, a1.
    eapply Permutation_trans; [exact HDo|]. change (Z.of_nat (length check_round_trip_stages_b.K_CONTEXT) + 1) with 8.
    apply Permutation_trans with ((a, 8) :: [(sk, 56 * 8); (sy, 8 * 8); (se, 9); (sv, 7)] ++ [(a1, 7)]).
    { apply perm_skip. apply Permutation_app_tail. exact SZst. }
    exact (Permutation_middle [(sk, 56 * 8); (sy, 8 * 8); (se, 9); (sv, 7)] [(a1, 7)] (a, 8)). }
  split; [exact POo|]. split; [exact HZ | exact POw].
Qed.

(* ---- segment 22: pj_string (&v, text) at B 0x82340 (A 0x821e4); St12 -> St13 (d25a984c903 sd12.v): v = JStr es on a
   fresh block of |es| + 1 bytes (es = the re-encoded text, the text block's own string), its head joins U, g_live +
   |es| + 1; the document and the state are kept ---- *)
Lemma crtC1_hcall_1d8 : crt_hcall SK B crtC_sc_1d8 0x83e58 0x82344 STK_pj_string (crtC1_INV_1d8 B) (crtC1_INV_1e8 B).
Proof.
intros cx E k ly3 S3 U3 W3 ms3 md3 regsC memC mdC HB HE HINV HJC HARUC Hfr HSB RG HPREc HFRL HTOPc.
destruct crtC1_site_1d8 as ((_ & _ & _ & _ & G1 & _) & G10 & G11).
destruct crtC1_ssave_all as (_ & _ & SV & _).
destruct HINV as (Ddoc & Dst & same & nsame & dec & live & peak & cnt & HC &
  (TDoc & (dnum & dstr & dkids & dkeys & HDh) & PDoc) & TSt & SZst & PSt & HZv & PV).
pose proof (ARU_AR tfibsegs B _ _ _ _ _ _ HARUC) as HARC.
destruct (crt_F_facts SK B cx ly3 S3 U3 W3 memC mdC k HJC HARUC Hfr) as (_ & F4096 & Fceil & _ & _ & _).
pose proof HJC as (_ & HlyC & _ & _ & _ & _ & HnevC & _).
pose proof (crt_F_ly cx _ ly3 HlyC) as EF.
assert (Hin3 : In (3, c_pos cx) (frames S3)) by (rewrite Hfr; left; reflexivity).
pose proof HC as HCd. cbv beta zeta delta [crtC1_corex] in HCd. destruct HCd as (_ & C18 & _ & _ & C27 & _).
set (F := crt_F cx) in *.
pose proof (crtC1_core_below B cx E k ly3 S3 U3 W3 _ mdC (ms_mem ms3) memC _ _ _ _ _ _ _ _ _ _ HARC ltac:(lia) Fceil HSB HC)
  as HCC.
pose proof (crtC1_rtree_below B ly3 S3 W3 _ mdC (ms_mem ms3) memC (F + 0x20) _ Ddoc HARC HSB ltac:(lia) ltac:(lia) TDoc)
  as TDocC.
pose proof (crtC1_rtree_below B ly3 S3 W3 _ mdC (ms_mem ms3) memC (F + 0x80) _ Dst HARC HSB ltac:(lia) ltac:(lia) TSt)
  as TStC.
pose proof (pobj_below B ly3 S3 W3 _ mdC (ms_mem ms3) memC _ HARC HSB PDoc) as PDocC.
pose proof (pobj_below B ly3 S3 W3 _ mdC (ms_mem ms3) memC _ HARC HSB PSt) as PStC.
pose proof (pobj_below B ly3 S3 W3 _ mdC (ms_mem ms3) memC _ HARC HSB PV) as PVC.
pose proof (crtC1_pj_hdr_below W3 (ms_mem ms3) memC (F + 0x20) _ _ _ _ _ _ _ HSB ltac:(lia) ltac:(lia) HDh) as HDhC.
pose proof HCC as HCd2. cbv beta zeta delta [crtC1_corex] in HCd2.
destruct HCd2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & PB & PU & HHU & TB & TZ & TC & DB & DZ & P140 & VM & RA & GL & LV &
  BB & CN & KB).
pose proof (crtC1_tb2_len (c_bs cx)) as Etb. pose proof (crtC1_bs_le_dec (c_bs cx)) as Ebs.
pose proof (fsw_rblock_low B _ _ _ _ _ memC _ _ HARC TB) as (T0 & T1).
pose proof (proj1 TB) as Ht.
pose proof (sep_block_frame tfibsegs B LAWS ly3 S3 W3 _ mdC _ _ 3 (c_pos cx) HARC Ht Hin3) as Dj.
unfold zdisjoint in Dj. rewrite crt_frame3, EF in Dj. cbn [fst snd] in Dj.
assert (Enp : req_size (FSH_Fn_writer.enc_size (Z.of_nat (length (c_bs cx))) + HEAD) =
  FSH_Fn_writer.enc_size (Z.of_nat (length (c_bs cx))) + HEAD)
  by (unfold req_size, HEAD in *; destruct (Z.eqb_spec (FSH_Fn_writer.enc_size (Z.of_nat (length (c_bs cx))) + 16) 0); lia).
rewrite Enp in Dj.
assert (R10 : YK11.getr regsC 10%bv = w64 (F + 0xe0)) by (rewrite RG, G10, fsw_SOff0; exact C27).
assert (R11 : YK11.getr regsC 11%bv = w64 (c_text cx)) by (rewrite RG, G11, fsw_SOff0; exact C18).
pose proof (fsw_sp B _ _ _ _ _ _ _ _ _ (proj1 HPREc)) as (_ & Hsp & _ & _).
pose proof (crtC1_live_le B cx E k ly3 S3 U3 W3 _ mdC memC _ _ _ _ _ _ _ _ _ _ HARC HCC) as Hlv.
pose proof (crtC1_steps cx) as (_ & _ & _ & T1' & T2 & T3 & L1 & L2 & X2 & X4 & Les).
pose proof (crtC1_LIVE_le B cx HB) as HLm.
pose proof (crt_live0 B cx HB) as HL0.
pose proof (crt_rd_sum_pos B ly3 S3 W3 memC Ddoc (proj1 (proj2 TDocC))) as Pd.
pose proof (crt_rd_sum_pos B ly3 S3 W3 memC Dst (proj1 (proj2 TStC))) as Ps.
rewrite crt_rd_sum_app in LV.
assert (EK : crtC1_KC_1d8 cx + EV_pj_string <= K_82218 cx) by (unfold crtC1_KC_1d8, crtC1_KC_1c0, K_82218; lia).
assert (ECN : crtC1_CNT_1d8 cx + 1 <= CNT_82218 cx)
  by (unfold crtC1_CNT_1d8, crtC1_CNT_1c0, CNT_82218; unfold crt_trlen in *; lia).
assert (ELV : crtC1_LIVE_1d8 cx + (Z.of_nat (length (WriterSpec.b64_enc (c_bs cx))) + 1 + HEAD) <= LIVE_82218 cx)
  by (unfold crtC1_LIVE_1d8, crtC1_LIVE_1c0, LIVE_82218, crt_es in *; rewrite X2, X4; unfold HEAD; lia).
set (FPs := [(F + 0xe0, F + 0xe0 + 56)] ++ FS_PSTAT_FP).
assert (HFPs : crtC1_fp ly3 (c_pos cx) FPs []).
{ intros x Hx. apply inFP_app in Hx as [Hx | Hx].
  - left. apply inFP_cons in Hx as [Hx | Hx]; [rewrite EF; lia | exfalso; exact (inFP_nil x Hx)].
  - right; left; exact Hx. }
assert (NFo : forall o x, (o = F + 0x20 \/ o = F + 0x80) -> o <= x < o + 56 -> ~ inFP FPs x).
{ intros o x Ho Hx Hin. apply inFP_app in Hin as [Hin | Hin].
  - apply inFP_cons in Hin as [Hin | Hin]; [lia | exact (inFP_nil x Hin)].
  - exact (frm_img tfibsegs B LAWS ly3 S3 W3 _ mdC 3 (c_pos cx) x HARC Hin3 ltac:(rewrite EF, crt_frame3; lia)
      (crt_pstat_img x Hin)). }
exists FPs, EV_pj_string.
eexists. split.
{ apply (PJS ly3 S3 U3 W3 regsC memC mdC (crt_ch1 cx) (F + 0xe0) (c_text cx) (WriterSpec.b64_enc (c_bs cx))
    live peak cnt SIZE_MAXZ HPREc HHU).
  - exact R10.
  - exact R11.
  - exact PVC.
  - left. lia.
  - right. split; [unfold HEAD in T0; lia|]. split; [exact TC|]. split.
    + left. exists (c_text cx - HEAD), (FSH_Fn_writer.enc_size (Z.of_nat (length (c_bs cx))) + HEAD).
      split; [exact Ht|]. split; [unfold HEAD; lia|]. split; [lia|].
      exact (crtC1_heads_apart B ly3 S3 W3 _ mdC U3 (c_text cx) (FSH_Fn_writer.enc_size (Z.of_nat (length (c_bs cx))))
        (Z.of_nat (length (WriterSpec.b64_enc (c_bs cx)))) HARC HHU Ht ltac:(lia) ltac:(lia)).
    + unfold HEAD in *. lia.
  - exact GL.
  - exact (crtC1_quiet B cx cnt (crtC1_CNT_1d8 cx) 1 HB CN ltac:(lia) ECN).
  - assert (0 <= crtC1_LIVE_1d8 cx) by (unfold HEAD in *; lia). unfold HEAD, MALLOC_MAX, LIVE_check_round_trip in *. lia.
  - exact (crtC1_live_room B cx live (crtC1_LIVE_1d8 cx) (Z.of_nat (length (WriterSpec.b64_enc (c_bs cx))) + 1) HB Hlv
      ltac:(unfold HEAD in ELV; lia)).
  - exact (crtC1_nev B cx k S3 (crtC1_KC_1d8 cx) EV_pj_string HB HnevC KB EK).
  - exact (crtC1_bb B cx S3 (crtC1_LIVE_1d8 cx) _ HB BB ELV). }
split.
{ pose proof (crtC_fpsub_obj B (c_ly cx) (c_S cx) ly3 S3 (c_pos cx) 0xe0 ltac:(lia) ltac:(lia)) as X.
  rewrite EF in X. exact X. }
split.
{ intros a Ha. apply (crtC1_notFP B ly3 S3 W3 _ mdC FPs (c_pos cx) [] (ablocks B ly3 S3) [] a HARC Hin3 HFPs
    ltac:(rewrite app_nil_r; reflexivity) (fun b H => match H with end)).
  right. rewrite EF. rewrite crt_frame3 in Ha. lia. }
intros W' c' (a3 & ly' & S' & regs' & mem' & md' & -> & HJc & OK' & PO' & HP & (R10' & Ha3 & HAB & HTV & HPV & HGL')).
exists ly', S', (U3 ++ [(a3 - HEAD, HEAD)]), regs', mem', md'.
split; [reflexivity|]. split; [exact HJc|]. split; [exact OK'|]. split; [exact PO'|]. split; [exact HP|].
intros HJ' HARU'.
pose proof (crtC1_regs_kept E crtC_sc_1d8 regsC regs' (crt_extra cx) RG SV HP) as RS.
pose proof (crtC1_a0_post regs' (crt_extra cx) R10') as R10E.
assert (HC' : crtC1_corex B cx (Ereg regs' (crt_extra cx)) (k + EV_pj_string) ly' S' (U3 ++ [(a3 - HEAD, HEAD)]) W' mem'
  (Ddoc ++ Dst ++ [(a3, Z.of_nat (length (WriterSpec.b64_enc (c_bs cx))) + 1)]) (crtC1_KC_1e8 cx) (crtC1_CNT_1e8 cx)
  (crtC1_LIVE_1e8 cx) same nsame dec (live + rd_sum [(a3, Z.of_nat (length (WriterSpec.b64_enc (c_bs cx))) + 1)])
  (Z.max peak (live + (Z.of_nat (length (WriterSpec.b64_enc (c_bs cx))) + 1))) (cnt + 1)).
{ apply (crtC1_core_call SK B cx E (Ereg regs' (crt_extra cx)) k EV_pj_string ly3 S3 U3 W3 memC mdC STK_pj_string
    (spZ regsC) FPs ly' S' (U3 ++ [(a3 - HEAD, HEAD)]) W' mem' md' (Ddoc ++ Dst)
    [(a3, Z.of_nat (length (WriterSpec.b64_enc (c_bs cx))) + 1)]
    (Ddoc ++ Dst ++ [(a3, Z.of_nat (length (WriterSpec.b64_enc (c_bs cx))) + 1)]) [] (crtC1_KC_1d8 cx)
    (crtC1_CNT_1d8 cx) (crtC1_LIVE_1d8 cx) _ _ _ same nsame dec live peak cnt
    (Z.max peak (live + (Z.of_nat (length (WriterSpec.b64_enc (c_bs cx))) + 1))) 1
    HCC HARUC Hfr EF HJc OK' PO' HFPs (fun b H => match H with end) R10E RS).
  - rewrite HAB. apply Permutation_refl.
  - apply Permutation_refl.
  - constructor; [cbn [snd]; lia | constructor].
  - rewrite app_assoc. apply Permutation_refl.
  - change (rd_sum [(a3, Z.of_nat (length (WriterSpec.b64_enc (c_bs cx))) + 1)])
      with (Z.of_nat (length (WriterSpec.b64_enc (c_bs cx))) + 1 + 0).
    rewrite Z.add_0_r. exact HGL'.
  - lia.
  - unfold crtC1_KC_1e8. lia.
  - unfold crtC1_CNT_1e8. lia.
  - unfold crtC1_LIVE_1e8, crt_es.
    change (YCbq.bsum (rd_hblocks [(a3, Z.of_nat (length (WriterSpec.b64_enc (c_bs cx))) + 1)]))
      with (Z.of_nat (length (WriterSpec.b64_enc (c_bs cx))) + 1 + HEAD + 0). lia. }
pose proof HC' as HCd'. cbv beta zeta delta [crtC1_corex] in HCd'.
destruct HCd' as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HH' & _).
pose proof (crtC1_FP_noshadow B ly3 S3 W3 _ mdC FPs (c_pos cx) [] HARC Hin3 HFPs (fun b H => match H with end)) as HFsh.
exists Ddoc, Dst, a3, same, nsame, dec, (live + rd_sum [(a3, Z.of_nat (length (WriterSpec.b64_enc (c_bs cx))) + 1)]),
  (Z.max peak (live + (Z.of_nat (length (WriterSpec.b64_enc (c_bs cx))) + 1))), (cnt + 1).
split; [exact HC'|].
split.
{ split; [|split].
  - apply (rtree_kept_call B STK_pj_string (spZ regsC) FPs ly3 S3 U3 W3 memC mdC ly' S' _ W' mem' md' EV_pj_string
      (F + 0x20) _ Ddoc HJc HARUC OK' PO' (fun x => NFo (F + 0x20) x (or_introl eq_refl))); [|exact PDocC | exact TDocC].
    destruct TDocC as (_ & HBk & _).
    exact (crtC1_tree_notFP B ly3 S3 W3 _ mdC memC FPs (c_pos cx) Ddoc HARC Hin3 HFPs HBk).
  - exists dnum, dstr, dkids, dkeys.
    exact (crtC1_pj_hdr_kept_call SK B STK_pj_string (spZ regsC) FPs ly3 S3 U3 W3 memC mdC ly' S' _ W' mem' md'
      EV_pj_string _ _ _ _ _ _ _ _ HJc HARUC OK' PO'
      (fun a0 (Ha0 : F + 0x20 <= a0 < F + 0x20 + 56) =>
         conj (crtC1_LBfr cx ly3 S3 a0 Hfr EF ltac:(lia)) (NFo (F + 0x20) a0 (or_introl eq_refl) Ha0)) HDhC).
  - exact (pobj_kept_call B STK_pj_string (spZ regsC) FPs ly3 S3 U3 W3 memC mdC ly' S' _ W' mem' md' EV_pj_string _
      HJc HARUC OK' PO' (fun x => NFo (F + 0x20) x (or_introl eq_refl)) HFsh HH' PDocC). }
split.
{ apply (rtree_kept_call B STK_pj_string (spZ regsC) FPs ly3 S3 U3 W3 memC mdC ly' S' _ W' mem' md' EV_pj_string
    (F + 0x80) _ Dst HJc HARUC OK' PO' (fun x => NFo (F + 0x80) x (or_intror eq_refl))); [|exact PStC | exact TStC].
  destruct TStC as (_ & HBk & _).
  exact (crtC1_tree_notFP B ly3 S3 W3 _ mdC memC FPs (c_pos cx) Dst HARC Hin3 HFPs HBk). }
split; [exact SZst|].
split; [exact (pobj_kept_call B STK_pj_string (spZ regsC) FPs ly3 S3 U3 W3 memC mdC ly' S' _ W' mem' md' EV_pj_string _
  HJc HARUC OK' PO' (fun x => NFo (F + 0x80) x (or_intror eq_refl)) HFsh HH' PStC)|].
split; [exact HTV | exact HPV].
Qed.

(* ---- segment 23: pj_set (&state, "bytes", &v) at B 0x82358 (A 0x821fc); St13 -> St14 (d25a984c903 sd13.v): the
   state becomes crt_st es, v is zeroed; the document is kept ---- *)
Lemma crtC1_hcall_1e8 : crt_hcall SK B crtC_sc_1e8 0x83adc 0x8235c STK_pj_set (crtC1_INV_1e8 B) (crtC1_INV_200 B).
Proof.
intros cx E k ly3 S3 U3 W3 ms3 md3 regsC memC mdC HB HE HINV HJC HARUC Hfr HSB RG HPREc HFRL HTOPc.
destruct crtC1_site_1e8 as ((_ & _ & _ & _ & G1 & _) & G10 & G11 & G12).
destruct crtC1_ssave_all as (_ & _ & _ & SV & _).
destruct HINV as (Ddoc & Dst & a3 & same & nsame & dec & live & peak & cnt & HC &
  (TDoc & (dnum & dstr & dkids & dkeys & HDh) & PDoc) & TSt & (sk & sy & se & sv & sc & sp & SZst) & PSt & TV & PV).
pose proof (ARU_AR tfibsegs B _ _ _ _ _ _ HARUC) as HARC.
destruct (crt_F_facts SK B cx ly3 S3 U3 W3 memC mdC k HJC HARUC Hfr) as (_ & F4096 & Fceil & _ & _ & _).
pose proof HJC as (_ & HlyC & _).
pose proof (crt_F_ly cx _ ly3 HlyC) as EF.
pose proof HC as HCd. cbv beta zeta delta [crtC1_corex] in HCd. destruct HCd as (_ & _ & _ & _ & C27 & C23 & _).
set (F := crt_F cx) in *.
pose proof (crtC1_core_below B cx E k ly3 S3 U3 W3 _ mdC (ms_mem ms3) memC _ _ _ _ _ _ _ _ _ _ HARC ltac:(lia) Fceil HSB HC)
  as HCC.
pose proof (crtC1_rtree_below B ly3 S3 W3 _ mdC (ms_mem ms3) memC (F + 0x20) _ Ddoc HARC HSB ltac:(lia) ltac:(lia) TDoc)
  as TDocC.
pose proof (crtC1_rtree_below B ly3 S3 W3 _ mdC (ms_mem ms3) memC (F + 0x80) _ Dst HARC HSB ltac:(lia) ltac:(lia) TSt)
  as TStC.
pose proof (crtC1_rtree_below B ly3 S3 W3 _ mdC (ms_mem ms3) memC (F + 0xe0) _ _ HARC HSB ltac:(lia) ltac:(lia) TV)
  as TVC.
pose proof (pobj_below B ly3 S3 W3 _ mdC (ms_mem ms3) memC _ HARC HSB PDoc) as PDocC.
pose proof (pobj_below B ly3 S3 W3 _ mdC (ms_mem ms3) memC _ HARC HSB PSt) as PStC.
pose proof (pobj_below B ly3 S3 W3 _ mdC (ms_mem ms3) memC _ HARC HSB PV) as PVC.
pose proof (crtC1_pj_hdr_below W3 (ms_mem ms3) memC (F + 0x20) _ _ _ _ _ _ _ HSB ltac:(lia) ltac:(lia) HDh) as HDhC.
destruct (crtC1_cap8 B ly3 S3 W3 memC (F + 0x80) check_round_trip_stages_b.crt_s2 Dst [(se, 9); (sv, 7); (sc, 8); (sp, 7)]
  sk sy TStC ltac:(cbv [check_round_trip_stages_b.crt_s2 length]; lia) SZst
  ltac:(constructor; [cbn [snd]; lia | constructor; [cbn [snd]; lia | constructor; [cbn [snd]; lia |
    constructor; [cbn [snd]; lia | constructor]]]])) as (num & str & kids & keys & HHs & _).
assert (R10 : YK11.getr regsC 10%bv = w64 (F + 0x80)) by (rewrite RG, G10, fsw_SOff0; exact C23).
assert (R11 : YK11.getr regsC 11%bv = w64 0x20fc0) by (rewrite RG, G11; reflexivity).
assert (R12 : YK11.getr regsC 12%bv = w64 (F + 0xe0)) by (rewrite RG, G12, fsw_SOff0; exact C27).
pose proof (crtC1_steps cx) as (_ & _ & _ & T1 & T2 & T3 & L1 & L2 & X2 & X4 & Les).
assert (Em : PjTree.pj_set_model check_round_trip_stages_b.crt_s2 check_round_trip_runs.CRT_BYTES
  (PjTree.JStr (crt_es cx)) = check_round_trip_stages_b.crt_st (crt_es cx)) by reflexivity.
apply (crtC1_pjset_call cx E k ly3 S3 U3 W3 regsC memC mdC crtC_sc_1e8 0x8235c 0x80 0xe0 0x20fc0
  check_round_trip_runs.CRT_BYTES check_round_trip_stages_b.crt_s2 (PjTree.JStr (crt_es cx))
  Dst [(a3, Z.of_nat (length (crt_es cx)) + 1)] Ddoc (Ddoc ++ Dst ++ [(a3, Z.of_nat (length (crt_es cx)) + 1)])
  num str kids keys (crtC1_KC_1e8 cx) (crtC1_CNT_1e8 cx) (crtC1_LIVE_1e8 cx) same nsame dec live peak cnt
  (crtC1_INV_200 B cx) HB HJC HARUC Hfr RG SV HPREc R10 R11 R12).
- lia.
- lia.
- lia.
- lia.
- lia.
- exact crtC_in_bytes.
- lia.
- apply Z.leb_le. vm_compute. reflexivity.
- apply Z.ltb_lt. vm_compute. reflexivity.
- vm_compute. intros [H | [H | H]]; [discriminate H | discriminate H | exact H].
- apply Nat.ltb_lt. vm_compute. reflexivity.
- exact HCC.
- rewrite (app_assoc Dst). apply Permutation_app_comm.
- exact (crt_rd_sum_pos B ly3 S3 W3 memC Ddoc (proj1 (proj2 TDocC))).
- exact TStC.
- exact PStC.
- exact HHs.
- exact TVC.
- exact PVC.
- change (crtC1_tr check_round_trip_stages_b.crt_s2 check_round_trip_runs.CRT_BYTES) with (pj_set_c.set_trace 2 8 5).
  unfold crtC1_KC_1e8, crtC1_KC_1d8, crtC1_KC_1c0, K_82218. lia.
- change (crtC1_tr check_round_trip_stages_b.crt_s2 check_round_trip_runs.CRT_BYTES) with (pj_set_c.set_trace 2 8 5).
  unfold crtC1_CNT_1e8, crtC1_CNT_1d8, crtC1_CNT_1c0, CNT_82218. unfold crt_trlen in *. lia.
- change (crtC1_tr check_round_trip_stages_b.crt_s2 check_round_trip_runs.CRT_BYTES) with (pj_set_c.set_trace 2 8 5).
  unfold crtC1_LIVE_1e8, crtC1_LIVE_1d8, crtC1_LIVE_1c0, LIVE_82218. rewrite X2, X4. unfold HEAD. lia.
- intros a ly' S' W' regs' mem' md' Do peak' HJc OK' PO' HP HJ' HARU' HC' TO' HDo HZ POo POw NFfr NFoth HFsh.
  pose proof HC' as HCd'. cbv beta zeta delta [crtC1_corex] in HCd'.
  destruct HCd' as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HH' & _).
  set (FPs := crtC1_FPset cx 0x80 0xe0 kids keys) in *.
  assert (NFd : forall x, F + 0x20 <= x < F + 0x20 + 56 -> ~ inFP FPs x)
    by (intros x Hx; apply NFfr; [lia | lia | lia]).
  exists Ddoc, Do, same, nsame, dec, (live + (Z.of_nat (length check_round_trip_runs.CRT_BYTES) + 1)), peak', (cnt + 1).
  split; [exact HC'|].
  split.
  { split; [|split].
    - apply (rtree_kept_call B STK_pj_set (spZ regsC) FPs ly3 S3 U3 W3 memC mdC ly' S' _ W' mem' md' _
        (F + 0x20) _ Ddoc HJc HARUC OK' PO' NFd); [exact NFoth | exact PDocC | exact TDocC].
    - exists dnum, dstr, dkids, dkeys.
      exact (crtC1_pj_hdr_kept_call SK B STK_pj_set (spZ regsC) FPs ly3 S3 U3 W3 memC mdC ly' S' _ W' mem' md' _
        _ _ _ _ _ _ _ _ HJc HARUC OK' PO'
        (fun a0 (Ha0 : F + 0x20 <= a0 < F + 0x20 + 56) =>
           conj (crtC1_LBfr cx ly3 S3 a0 Hfr EF ltac:(lia)) (NFd a0 Ha0)) HDhC).
    - exact (pobj_kept_call B STK_pj_set (spZ regsC) FPs ly3 S3 U3 W3 memC mdC ly' S' _ W' mem' md' _ _
        HJc HARUC OK' PO' NFd HFsh HH' PDocC). }
  split; [rewrite Em in TO'; exact TO'|].
  split; [exact POo|]. split; [exact HZ | exact POw].
Qed.

(* ---- segment 24: pj_set (&doc, "state", &state) at B 0x82370 (A 0x82214); St14 -> St15 (d25a984c903 sd14.v): the
   document becomes crt_doc es on its old blocks + the key block + all the state's blocks, the state object is zeroed; v
   stays zeroed. B: obj = F + 0x20 is slot 0x38's SOff 47 0x20 (crtC1_F_arg), not a register (A: s10 = atom 26) ---- *)
Lemma crtC1_hcall_200 : crt_hcall SK B crtC_sc_200 0x83adc 0x82374 STK_pj_set (crtC1_INV_200 B) (crt_INV_82218 B).
Proof.
intros cx E k ly3 S3 U3 W3 ms3 md3 regsC memC mdC HB HE HINV HJC HARUC Hfr HSB RG HPREc HFRL HTOPc.
destruct crtC1_site_200 as ((_ & _ & _ & _ & G1 & _) & G10 & G11 & G12).
destruct crtC1_ssave_all as (_ & _ & _ & _ & SV).
destruct HINV as (Ddoc & Dst & same & nsame & dec & live & peak & cnt & HC &
  (TDoc & (dnum & dstr & dkids & dkeys & HDh) & PDoc) & TSt & PSt & HZv & PV).
pose proof (ARU_AR tfibsegs B _ _ _ _ _ _ HARUC) as HARC.
destruct (crt_F_facts SK B cx ly3 S3 U3 W3 memC mdC k HJC HARUC Hfr) as (_ & F4096 & Fceil & _ & _ & _).
pose proof HJC as (_ & HlyC & _).
pose proof (crt_F_ly cx _ ly3 HlyC) as EF.
pose proof HC as HCd. cbv beta zeta delta [crtC1_corex] in HCd.
destruct HCd as (_ & _ & _ & _ & _ & C23 & _).
pose proof asan_consts as (AC & _).
assert (HF0 : 0 <= crt_F cx < 2 ^ 64) by (clear - F4096 Fceil AC; lia).
assert (HF20 : 0 <= crt_F cx + 0x20 < 2 ^ 64) by (clear - F4096 Fceil AC; lia).
set (F := crt_F cx) in *.
pose proof (crtC1_core_below B cx E k ly3 S3 U3 W3 _ mdC (ms_mem ms3) memC _ _ _ _ _ _ _ _ _ _ HARC ltac:(lia) Fceil HSB HC)
  as HCC.
pose proof (crtC1_rtree_below B ly3 S3 W3 _ mdC (ms_mem ms3) memC (F + 0x20) _ Ddoc HARC HSB ltac:(lia) ltac:(lia) TDoc)
  as TDocC.
pose proof (crtC1_rtree_below B ly3 S3 W3 _ mdC (ms_mem ms3) memC (F + 0x80) _ Dst HARC HSB ltac:(lia) ltac:(lia) TSt)
  as TStC.
pose proof (pobj_below B ly3 S3 W3 _ mdC (ms_mem ms3) memC _ HARC HSB PDoc) as PDocC.
pose proof (pobj_below B ly3 S3 W3 _ mdC (ms_mem ms3) memC _ HARC HSB PSt) as PStC.
pose proof (pobj_below B ly3 S3 W3 _ mdC (ms_mem ms3) memC _ HARC HSB PV) as PVC.
pose proof (crtC1_pj_hdr_below W3 (ms_mem ms3) memC (F + 0x20) _ _ _ _ _ _ _ HSB ltac:(lia) ltac:(lia) HDh) as HDhC.
pose proof (crtC1_pj_zero_below W3 (ms_mem ms3) memC (F + 0xe0) HSB ltac:(lia) ltac:(lia) HZv) as HZvC.
assert (R10 : YK11.getr regsC 10%bv = w64 (F + 0x20)) by (rewrite RG, G10; exact (crtC1_F_arg cx E 0x20 HE HF0 HF20)).
assert (R11 : YK11.getr regsC 11%bv = w64 0x20f00) by (rewrite RG, G11; reflexivity).
assert (R12 : YK11.getr regsC 12%bv = w64 (F + 0x80)) by (rewrite RG, G12, fsw_SOff0; exact C23).
pose proof (crtC1_steps cx) as (_ & _ & _ & T1 & T2 & T3 & L1 & L2 & X2 & X4 & Les).
assert (Em : PjTree.pj_set_model check_round_trip_st8.crt_doc8 check_round_trip_runs.CRT_STATE
  (PjTree.JObj (check_round_trip_stages_b.crt_st (crt_es cx))) = check_round_trip_stages_b.crt_doc (crt_es cx))
  by reflexivity.
apply (crtC1_pjset_call cx E k ly3 S3 U3 W3 regsC memC mdC crtC_sc_200 0x82374 0x20 0x80 0x20f00
  check_round_trip_runs.CRT_STATE check_round_trip_st8.crt_doc8
  (PjTree.JObj (check_round_trip_stages_b.crt_st (crt_es cx))) Ddoc Dst [] (Ddoc ++ Dst)
  dnum dstr dkids dkeys (crtC1_KC_200 cx) (crtC1_CNT_200 cx) (crtC1_LIVE_200 cx) same nsame dec live peak cnt
  (crt_INV_82218 B cx) HB HJC HARUC Hfr RG SV HPREc R10 R11 R12).
- lia.
- lia.
- lia.
- lia.
- lia.
- exact crtC_in_state.
- lia.
- apply Z.leb_le. vm_compute. reflexivity.
- apply Z.ltb_lt. vm_compute. reflexivity.
- vm_compute. intros [H | [H | H]]; [discriminate H | discriminate H | exact H].
- apply Nat.ltb_lt. vm_compute. reflexivity.
- exact HCC.
- rewrite app_nil_r. apply Permutation_refl.
- cbv [rd_sum fold_right]. lia.
- exact TDocC.
- exact PDocC.
- exact HDhC.
- exact TStC.
- exact PStC.
- change (crtC1_tr check_round_trip_st8.crt_doc8 check_round_trip_runs.CRT_STATE) with (pj_set_c.set_trace 2 8 5).
  rewrite crtC1_K_last. lia.
- change (crtC1_tr check_round_trip_st8.crt_doc8 check_round_trip_runs.CRT_STATE) with (pj_set_c.set_trace 2 8 5).
  rewrite crtC1_CNT_last. lia.
- change (crtC1_tr check_round_trip_st8.crt_doc8 check_round_trip_runs.CRT_STATE) with (pj_set_c.set_trace 2 8 5).
  rewrite crtC1_LIVE_last. lia.
- intros a ly' S' W' regs' mem' md' Do peak' HJc OK' PO' HP HJ' HARU' HC' TO' HDo HZ POo POw NFfr NFoth HFsh.
  set (FPs := crtC1_FPset cx 0x20 0x80 dkids dkeys) in *.
  assert (NFv : forall x, F + 0xe0 <= x < F + 0xe0 + 56 -> ~ inFP FPs x)
    by (intros x Hx; apply NFfr; [lia | lia | lia]).
  cbv beta zeta delta [crtC1_corex] in HC'.
  destruct HC' as (C10' & C18' & C20' & C21' & C27' & C23' & C24' & C25' & C22' & C19' & PB' & PU' & HH' & TB' & TZ' & TC' &
    DB' & DZ' & P140' & VM' & RA' & GL' & LV' & BB' & CN' & KB').
  cbv beta zeta delta [crt_INV_82218].
  refine (conj C10' (conj C18' (conj C20' (conj C21' (conj C27' (conj C23' (conj C22' (conj C19' _)))))))).
  exists same, nsame, dec, ([] ++ Do), (live + (Z.of_nat (length check_round_trip_runs.CRT_STATE) + 1)), peak',
    (cnt + 1).
  split; [exact C24'|]. split; [exact C25'|]. split; [exact PB'|]. split; [exact PU'|]. split; [exact HH'|].
  split; [exact TB'|]. split; [exact TZ'|]. split; [exact TC'|]. split; [exact DB'|]. split; [exact DZ'|].
  split; [rewrite Em in TO'; exact TO'|].
  split; [exact POo|]. split; [exact POw|].
  split; [exact (pobj_kept_call B STK_pj_set (spZ regsC) FPs ly3 S3 U3 W3 memC mdC ly' S' _ W' mem' md' _ _
    HJc HARUC OK' PO' NFv HFsh HH' PVC)|].
  split; [exact P140'|]. split; [exact HZ|].
  split; [exact (crtC1_pj_zero_kept_call SK B STK_pj_set (spZ regsC) FPs ly3 S3 U3 W3 memC mdC ly' S' _ W' mem' md' _ _
    HJc HARUC OK' PO'
    (fun a0 (Ha0 : F + 0xe0 <= a0 < F + 0xe0 + 56) =>
       conj (crtC1_LBfr cx ly3 S3 a0 Hfr EF ltac:(lia)) (NFv a0 Ha0)) HZvC)|].
  split; [exact VM'|]. split; [exact RA'|]. split; [exact GL'|]. split; [exact LV'|].
  split; [rewrite crtC1_LIVE_last; exact BB'|].
  split; [rewrite crtC1_CNT_last; exact CN' | rewrite crtC1_K_last; exact KB'].
Qed.

(* ================= the lane: crt_INV_821ac at B 0x82308 (A 0x821ac) to crt_INV_82218 at B 0x82374 (A 0x82218) =================
   Five segments, each a `bnez a0` (not taken: the boundary's a0 = 0), a store-free run to the callee and the program
   call (FSH_crt_site.crt_seg_call_br), the call's own part crtC1_hcall_<r>. *)
Lemma crtC1_from : crt_from SK B (crt_ss_ret 0x82374 crt_cs1 crt_csF) (crt_INV_82218 B) ->
  crt_from SK B (crt_ss_ret 0x82308 crt_cs1 crt_csF) (crt_INV_821ac B).
Proof.
intros H.
assert (Hstr : 0 <= STK_pj_string /\ STK_pj_string + 208 <= STK_check_round_trip)
  by (split; apply Z.leb_le; vm_compute; reflexivity).
assert (Hset : 0 <= STK_pj_set /\ STK_pj_set + 208 <= STK_check_round_trip)
  by (split; apply Z.leb_le; vm_compute; reflexivity).
apply (crt_seg_call_br SK B 0x82308 0x83e58 0x8231c crtC_sb_1ac crtC_sc_1ac (crt_INV_821ac B) (crtC1_INV_1c0 B)
  STK_pj_string crtC_br_1ac crtC_run_1ac (proj1 crtC1_site_1ac) ltac:(lia) eq_refl (proj1 Hstr) (proj2 Hstr)
  (crtC1_a0_821ac B) (crtC1_hcall_1ac SK B IMG PJS)).
apply (crt_seg_call_br SK B 0x8231c 0x83adc 0x82334 crtC_sb_1c0 crtC_sc_1c0 (crtC1_INV_1c0 B) (crtC1_INV_1d8 B)
  STK_pj_set crtC_br_1c0 crtC_run_1c0 (proj1 crtC1_site_1c0) ltac:(lia) eq_refl (proj1 Hset) (proj2 Hset)
  (crtC1_a0_1c0 B) crtC1_hcall_1c0).
apply (crt_seg_call_br SK B 0x82334 0x83e58 0x82344 crtC_sb_1d8 crtC_sc_1d8 (crtC1_INV_1d8 B) (crtC1_INV_1e8 B)
  STK_pj_string crtC_br_1d8 crtC_run_1d8 (proj1 crtC1_site_1d8) ltac:(lia) eq_refl (proj1 Hstr) (proj2 Hstr)
  (crtC1_a0_1d8 B) crtC1_hcall_1d8).
apply (crt_seg_call_br SK B 0x82344 0x83adc 0x8235c crtC_sb_1e8 crtC_sc_1e8 (crtC1_INV_1e8 B) (crtC1_INV_200 B)
  STK_pj_set crtC_br_1e8 crtC_run_1e8 (proj1 crtC1_site_1e8) ltac:(lia) eq_refl (proj1 Hset) (proj2 Hset)
  (crtC1_a0_1e8 B) crtC1_hcall_1e8).
apply (crt_seg_call_br SK B 0x8235c 0x83adc 0x82374 crtC_sb_200 crtC_sc_200 (crtC1_INV_200 B) (crt_INV_82218 B)
  STK_pj_set crtC_br_200 crtC_run_200 (proj1 crtC1_site_200) ltac:(lia) eq_refl (proj1 Hset) (proj2 Hset)
  (crtC1_a0_200 B) crtC1_hcall_200).
exact H.
Qed.
End calls2.

