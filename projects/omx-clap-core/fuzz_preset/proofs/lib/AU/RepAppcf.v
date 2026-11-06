(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10-31: from proofs/plugin-hostd/fuzz_reply/lib/B/RepAppcf.v (commit 4d286b2e618d, file sha256 84ac1337edea) onto omx-clap-core/fuzz_preset's ASan+UBSan image B' (fuzz_preset.asan-ubsan, pin d663f82d7f48, twin c90d4fa54d43); module paths changed; reply's image-instance names mapped to preset's B' instance (AGif2reply / AImg_reply -> AGif2cgif / AImg_cgif) and its row names to preset's (Reply* -> Preset*, *reply -> *preset); its 11 image numerals moved by symbol from fuzz_reply.asan-ubsan (pin 10ffb5f9202a) to B' (port_addr_check 3d2eee813cce predictions; object addresses written in decimal by the same symbol map), and 2 addresses named in comments; comment references to people and refs dropped; no other numeral changed. *)
(* Modified by Theorem Labs, 2026-10: from proofs/cgif/cgif_file_fuzzer/lib/RepAppcf.v (commit f01d79f3fb5, cf refill round 3; file sha256 3cc245387f4a) onto plugin-hostd/fuzz_reply's asan image (unstripped fuzz_reply.asan, sha256 d751b179ea49; pin 42c58610e125); module paths changed; its 10 image addresses moved by function pairs the comparison kit cmpkit 86da41d3ef68 calls the same code except at the by-hand acceptances named below (strictcmp3 65688e94214a, by funcpair_reply 6963bc4a94fc on the cgif twin ce511d541cda; 8 port_addr_check e55e1b52a8a0 MAPS predictions, each code one re-derived by the pair, each data one a pc-relative target of both paired functions; 0 code pcs the tool read as sizes, by the pair; 1 pair(s) carry a BY-HAND acceptance (the internal file accept.tsv, re-measured each run): _ZN11__sanitizer17GetNamedMappingFdEPKcmPi+0x90 (lui-in-section: CONSTANT)), and 6 pcs named in comments; 4 hand maps (the internal file resolve-run-f01d79f3fb5.tsv, each with its evidence: pinned image bytes, YImgTop, the unit AF twin); no other numeral changed. *)
(* Theorem Labs, 2026-10-30 (a prior worker, slice F4 of a Theorem Labs lane's class-full report walk):
   __asan::AppendToErrorMessageBuffer (0x55df8) of cgif_file_fuzzer's asan-ubsan image (pin 1c29845fe605)
   realizes the model step errb_append_cf (YG00cf.v:133).  The statement proved here is
   RepIFcf.append_spec_cf, which this file never edits.
   rule 24: proves function __asan::AppendToErrorMessageBuffer (reuse search: ossv proof index v5 built
   2026-10-30T01:54:20Z and 02:28:20Z over main / ossv/recipes / ossv/candidates /
   release/pau-projects-recipes plus the proof index and the live internal working heads;
   `proof-index VSNPrintf Printf SharedPrintfCode AppendNumber AppendToErrorMessageBuffer MmapOrDie`
   2026-10-30T02:25:54Z exit 0 and `proof-index UnmapOrDie internal_memset internal_memcpy
   internal_strlen GetNamedMappingFd IncreaseTotalMmap` 2026-10-30T02:55Z exit 3; 0 released lemma(s) for
   every name; rule-24 check RepLookupCheck CONFIRM, nothing reusable: every cgif_file_fuzzer hit is a
   `by address` row of the YB1q.v / YB1w.v decode and symbol-name tables). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool String Ascii.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s YO0d.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.Z Require Import Placement.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YP0j.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YK0v YK13 YA0i YA0n YA0o YA0p YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG04 YG03 YG0f YG0v YG0n YG0d YG0s YG0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YB1v YB1q YF0l YF0m YF0x YFl0 YFl1.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YGcfNames YG01cf YG00cf YG0ncf YG0dcf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import ImgBase.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import ImgBaseAG AGif0n. From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require Import AGif2cgif AGif0cgif.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfInstBase YGcfInstRefill.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfXs.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require YFk5cf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require MemnormT.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require Import RepIFcf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG06bcf.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams}.
Variable B : asyms.

(* --------------------------------------------------------------------------------------------------------- *)
(* The kernel cannot refuse the error-message buffer's mmap: a placement exists, and the backing budget has
   room for it.  The grant half is RepGrantcf.errb_grant_exists_cf (SecGrantW.ifs_grant_w_cf at the cf
   relation); the room half is AGif4.ifs_room_w (AGif4.v:343) at ROOMW := nZ.  The Realloc walk exposes the
   new map through w_H alone (YG0b.commit_expose), so one nZ of room is all it spends.  RepAppTcf assembles
   this from the two halves; the machine's refused branch is therefore vacuous. *)
Hypothesis errb_map_fits_cf :
  forall (Hp : list Z) (ly : alayout) (S : astate) (W : world tfibsegs) (mem : word -> option byte)
    (md : Model) (nZ : Z),
  layout_ok ly -> img_cover ly -> TfibSyms B -> ly_tsd ly = TFIB_TSD ->
  ARcf tfibsegs B ly S Hp W mem md -> xs_mapped_cf ly S md -> qloose S -> cf_hull_ok S ->
  0 < nZ -> nZ mod kPage = 0 -> nZ <= cf_nob ->
  (exists a, grant_ok_na_pin md a nZ = true) /\
  eager_used md + A_bytes (w_A W) + nZ <= vm_limit (m_vmmaps md).

(* The form the mmap node wants (YF05.v:149 anon_node, through YK13.v:239
   grant_na_pin_not_grant_refusable): at the errbuf map the kernel's refusal is impossible.  The guard on
   [mat] is necessary: vm_backing_used counts the materialized pages too (YK04.v:525), so a long enough
   materialized list refuses any size; every [mat] the invariant AI admits is within A_bytes (w_A W). *)
Lemma errb_map_not_refusable :
  forall (Hp : list Z) (ly : alayout) (S : astate) (W : world tfibsegs) (mem : word -> option byte)
    (md : Model) (mat : list word) (nZ : Z),
  layout_ok ly -> img_cover ly -> TfibSyms B -> ly_tsd ly = TFIB_TSD ->
  ARcf tfibsegs B ly S Hp W mem md -> xs_mapped_cf ly S md -> qloose S -> cf_hull_ok S ->
  0 < nZ -> nZ mod kPage = 0 -> nZ <= cf_nob ->
  Z.of_nat (length mat) * page_size <= A_bytes (w_A W) ->
  mmap_grant_refusable (Z_to_bv 64 34) (with_vm_backing (m_vm_lazy md) mat md) nZ = false.
Proof.
intros Hp ly S W mem md mat nZ LY IMG TS TSD AR XM QL HT Hpos Hal Hnob Hmat.
destruct (errb_map_fits_cf Hp ly S W mem md nZ LY IMG TS TSD AR XM QL HT Hpos Hal Hnob) as [[a Ha] Hroom].
assert (Hvm : m_vmmaps (with_vm_backing (m_vm_lazy md) mat md) = m_vmmaps md) by apply m_vmmaps_wvb.
apply (grant_na_pin_not_grant_refusable _ _ a).
- unfold grant_ok_na_pin in Ha |- *. rewrite Hvm. exact Ha.
- unfold mmap_noreserve_backed_ok.
  replace (mmap_noreserve_b (Z_to_bv 64 34)) with false by (vm_compute; reflexivity).
  cbv iota. apply Z.leb_le. rewrite vm_backing_used_split, Hvm.
  assert (He : eager_used (with_vm_backing (m_vm_lazy md) mat md) = eager_used md).
  { unfold eager_used. rewrite Hvm. rewrite m_vm_lazy_wvb. reflexivity. }
  assert (Hm : m_vm_materialized (with_vm_backing (m_vm_lazy md) mat md) = mat) by reflexivity.
  rewrite He, Hm. unfold page_size in *. lia.
Qed.

(* --------------------------------------------------------------------------------------------------------- *)
(* The image words the walk's callees branch on, out of the relation rather than out of the image: every one
   of them is an as_const cell (TfibSyms' ts_const pins as_const to Tfib_const, YF0m.v:90-170), and ARcf's
   ARmcf field amc_const says each holds. *)
Lemma rep_cell_lit :
  forall (Hp : list Z) (ly : alayout) (S : astate) (W : world tfibsegs) (mem : word -> option byte)
    (md : Model) (a : Z) (w : nat) (x : Z),
  TfibSyms B -> ARcf tfibsegs B ly S Hp W mem md ->
  YF0x.cell_lookup (Tfib_const ly) (ANum a) = Some (ACell (ANum a) w (AV (ANum x))) ->
  val_mem tfibsegs (mrestrict (w_H W) mem) a w x.
Proof.
intros Hp ly S W mem md a w x TB AR E.
apply (YF0x.cell_holds_val_mem B ly (w_H W) mem (ANum a) w (ANum x)).
apply (proj1 (Forall_forall _ _) (amc_const _ _ _ _ _ (proj1 AR))).
rewrite (ts_const B TB ly). exact (YF0x.cell_lookup_In _ _ _ E).
Qed.

(* The page-size cache GetPageSize / MmapOrDie / Realloc read (0x9e1e8 -> 0x135d20 = 4096) and the Mutex
   unlock mask word at 0x103b8 that AppendToErrorMessageBuffer loads at 0x565d4. *)
Lemma rep_pagesize_cells :
  forall (Hp : list Z) (ly : alayout) (S : astate) (W : world tfibsegs) (mem : word -> option byte) (md : Model),
  TfibSyms B -> ARcf tfibsegs B ly S Hp W mem md ->
  val_mem tfibsegs (mrestrict (w_H W) mem) 0xa2830 8 0x13b1a0 /\
  val_mem tfibsegs (mrestrict (w_H W) mem) 0x13b1a0 8 4096 /\
  val_mem tfibsegs (mrestrict (w_H W) mem) 0x103b8 8 0xafffff00000fffff.
Proof.
intros Hp ly S W mem md TB AR.
split; [|split]; eapply (rep_cell_lit Hp ly S W mem md); try eassumption; vm_compute; reflexivity.
Qed.

(* A single byte out of a const word: Tfib_const lists 8-byte cells, and GetNamedMappingFd reads one byte. *)
Lemma rep_const_byte :
  forall (m : word -> option byte) (a : Z) (n : nat) (v : Z) (k : nat) (x : Z),
  val_mem tfibsegs m a n v -> (k < n)%nat -> YO0f.le_byte v n k = YO0f.le_byte x 1 0 ->
  val_mem tfibsegs m (a + Z.of_nat k) 1 x.
Proof.
intros m a n v k x H Hk E j Hj. assert (j = 0%nat) as -> by lia.
cbn [Z.of_nat]. rewrite Z.add_0_r, <- E. exact (H k Hk).
Qed.

(* The two cells MmapOrDie's callees branch on: common_flags()->decorate_proc_maps = 0 (the lbu at 0x67e40 in
   GetNamedMappingFd) and common_flags()->mmap_limit_mb = 0 (the ld at 0x61948 in IncreaseTotalMmap), both
   through the common_flags pointer at 0x9e1f8 = 0x137da8.  The byte 0x137eac is byte 4 of the const word
   0x137ea8 = 0x1010101. *)
Lemma rep_mmap_cells :
  forall (Hp : list Z) (ly : alayout) (S : astate) (W : world tfibsegs) (mem : word -> option byte) (md : Model),
  TfibSyms B -> ARcf tfibsegs B ly S Hp W mem md ->
  val_mem tfibsegs (mrestrict (w_H W) mem) 0xa2840 8 0x13d228 /\
  val_mem tfibsegs (mrestrict (w_H W) mem) 0x13d32c 1 0 /\
  val_mem tfibsegs (mrestrict (w_H W) mem) 0x13d2b8 8 0.
Proof.
intros Hp ly S W mem md TB AR.
assert (Hw : val_mem tfibsegs (mrestrict (w_H W) mem) 0x13d328 8 0x1010101)
  by (eapply (rep_cell_lit Hp ly S W mem md); try eassumption; vm_compute; reflexivity).
split; [eapply (rep_cell_lit Hp ly S W mem md); try eassumption; vm_compute; reflexivity|].
split; [|eapply (rep_cell_lit Hp ly S W mem md); try eassumption; vm_compute; reflexivity].
replace 0x13d32c with (0x13d328 + Z.of_nat 4) by reflexivity.
apply (rep_const_byte _ _ 8%nat 0x1010101 4%nat 0 Hw ltac:(lia)). vm_compute. reflexivity.
Qed.

(* --------------------------------------------------------------------------------------------------------- *)
(* The call premise's object cells, at the machine's own address.  RepIFcf's errb_call_pre pins
   cf_errbuf_obj to C_ERRBUF = 0xa5ae8, which is the address AppendToErrorMessageBuffer forms at
   0x56454 / 0x56464, so the five words, the buffer's visibility and the buffer's model shape come out
   there.  Stated without RepRelcf, so that the two files move independently. *)
Lemma rep_cell8 : forall (ly : alayout) (H : word -> bool) (mem : word -> option byte) (A v : Z),
  cell_holds B ly (aview tfibsegs H mem) (z8 (ANum A) v) -> val_mem tfibsegs (mrestrict H mem) A 8 v.
Proof. intros ly H mem A v C. exact (YF0x.cell_holds_val_mem B ly H mem (ANum A) 8 (ANum v) C). Qed.

Lemma rep_pre_cells :
  forall (lk : option Z) (Hp : list Z) (ly : alayout) (S : astate) (W : world tfibsegs)
    (mem : word -> option byte) (md : Model),
  errb_call_pre B lk Hp ly S W mem md ->
  val_mem tfibsegs (mrestrict (w_H W) mem) C_ERRBUF 8 (if errb_mapped_cf S then C_ERRBUF + 32 else 0) /\
  val_mem tfibsegs (mrestrict (w_H W) mem) (C_ERRBUF + 16) 8 0 /\
  val_mem tfibsegs (mrestrict (w_H W) mem) (C_ERRBUF + 32) 8 (YG0ncf.errb_data_cf ly S) /\
  val_mem tfibsegs (mrestrict (w_H W) mem) (C_ERRBUF + 40) 8 (errb_cap_cf S) /\
  val_mem tfibsegs (mrestrict (w_H W) mem) (C_ERRBUF + 48) 8 (errb_size_cf S) /\
  (forall a, YG0ncf.errb_data_cf ly S <= a < YG0ncf.errb_data_cf ly S + errb_cap_cf S ->
     aview tfibsegs (w_H W) mem a <> None) /\
  errb_size_cf S <= errb_cap_cf S /\ errb_cap_cf S mod kPage = 0.
Proof.
intros lk Hp ly S W mem md PRE.
destruct PRE as (Hobj & Hexh & LY & IMG & TS & TSD & AR & XM & WFS & QL & EXH & CELLS & IMGF & _).
unfold YG0ncf.errb_cells_cf in CELLS. cbv zeta in CELLS.
rewrite Hobj in CELLS.
destruct CELLS as (C0 & C16 & C32 & C40 & C48 & CV & CLE & CPG).
split; [exact (rep_cell8 ly (w_H W) mem _ _ C0)|].
split; [exact (rep_cell8 ly (w_H W) mem _ _ C16)|].
split; [exact (rep_cell8 ly (w_H W) mem _ _ C32)|].
split; [exact (rep_cell8 ly (w_H W) mem _ _ C40)|].
split; [exact (rep_cell8 ly (w_H W) mem _ _ C48)|].
split; [exact CV|]. split; [exact CLE | exact CPG].
Qed.


(* --------------------------------------------------------------------------------------------------------- *)
(* Every size the append maps is within cf_nob, so errb_map_fits_cf applies at each of the (at most two)
   maps: the first map asks ERRB_INIT = 65536, and a growing map asks the new size, which the call's room
   premise bounds.  round_up w kPage <= w + kPage is YG06bcf.v:330's RU. *)
Lemma rep_round_le : forall w, 0 < w -> round_up w kPage <= w + kPage.
Proof.
intros w Hw. pose proof (round_up_ge w kPage ltac:(unfold kPage; lia)) as [[_ R2] _]. lia.
Qed.

Lemma rep_ncap_init : round_up ERRB_INIT kPage <= cf_nob.
Proof.
pose proof cf_nob_lo as N. replace (round_up ERRB_INIT kPage) with 65536 by reflexivity. lia.
Qed.

Lemma rep_ncap_grow : forall (S : astate) (len : Z),
  0 <= errb_size_cf S -> 0 < len -> errb_room_for S len ->
  round_up (errb_size_cf S + len) kPage <= cf_nob /\ round_up len kPage <= cf_nob.
Proof.
intros S len Hs Hl HR. unfold errb_room_for in HR.
pose proof (rep_round_le (errb_size_cf S + len) ltac:(lia)) as R1.
pose proof (rep_round_le len Hl) as R2. split; lia.
Qed.

(* --------------------------------------------------------------------------------------------------------- *)
(* The model step, reduced to the shape the walk meets it in.  errb_map_cf (YG00cf.v:122-127) is a single
   refusable ask whose granted answer is a pure state step, and errb_append_cf (YG00cf.v:133-143) is one of
   three trees according to the two booleans the machine itself branches on.  Written without naming the
   event counter: errb_frame (YG06bcf.v:67) says only st_secs and the counter moved. *)
Lemma rep_map_ask : forall (want : Z) (S : astate),
  exists (snap S1 : astate) (k : Z -> itree astate (unit * astate)),
  errb_map_cf want S = IAsk (KMmapSec (round_up want kPage)) snap k /\
  (forall z, z <> 0 -> k z = IRet (tt, S1)) /\
  errb_frame S S1 /\
  st_secs S1 = map cfx_retire (st_secs S) ++ [mkSec (round_up want kPage) ERRB_CAP_TAG false].
Proof.
intros want S. destruct S as [rg cin ca ch secs sa sr qt qg fsx dp ii nv].
unfold errb_map_cf, YG00.bind, YG00.tick, YG00.askz, errb_retire, YG00.modify, errb_frame.
cbn. eexists. eexists. eexists. split; [reflexivity|].
split; [intros z Hz; destruct (Z.eqb_spec z 0); [congruence | cbn; reflexivity]|].
split; reflexivity.
Qed.

Lemma rep_append_mapped_fit : forall (len : Z) (S : astate),
  errb_mapped_cf S = true -> (errb_cap_cf S <? errb_size_cf S + len) = false ->
  errb_append_cf len S = errb_set_size (errb_size_cf S + len) S.
Proof.
intros len S EM Hc. unfold errb_append_cf, YG00.bind, YG00.get, YG00.ret.
cbn [ibind fst snd]. rewrite EM. cbn [negb]. rewrite Hc. cbn [ibind fst snd]. reflexivity.
Qed.

Lemma rep_append_mapped_grow : forall (len : Z) (S : astate),
  errb_mapped_cf S = true -> (errb_cap_cf S <? errb_size_cf S + len) = true ->
  errb_append_cf len S =
  ibind (errb_map_cf (errb_size_cf S + len) S) (fun '(_, s1) => errb_set_size (errb_size_cf S + len) s1).
Proof.
intros len S EM Hc. unfold errb_append_cf, YG00.bind, YG00.get.
cbn [ibind fst snd]. rewrite EM. cbn [negb]. rewrite Hc. reflexivity.
Qed.

Lemma rep_append_unmapped : forall (len : Z) (S : astate),
  errb_mapped_cf S = false ->
  errb_append_cf len S =
  ibind (errb_map_cf ERRB_INIT S)
    (fun '(_, s1) => ibind ((if errb_cap_cf s1 <? len then errb_map_cf len else YG00.ret tt) s1)
                           (fun '(_, s2) => errb_set_size len s2)).
Proof.
intros len S EM. unfold errb_append_cf, YG00.bind, YG00.get.
cbn [ibind fst snd]. rewrite EM. cbn [negb]. reflexivity.
Qed.
End a.
