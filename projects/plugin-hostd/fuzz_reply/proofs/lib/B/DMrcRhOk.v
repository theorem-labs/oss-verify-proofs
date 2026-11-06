(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: from proofs/cgif/cgif_file_fuzzer/lib/DMrcRhOk.v (commit 3d8ad2aeb77e, H4 stage B (slack-indexed post relation; DMrcDefs / DGif1Geo split; re-hide head); file sha256 d1a63d27efc0) onto plugin-hostd/fuzz_reply's asan image (unstripped fuzz_reply.asan, sha256 d751b179ea49; pin 42c58610e125); module paths changed; its 0 image addresses moved by code-verified function pairs (0 port_addr_check e55e1b52a8a0 MAPS predictions, each code one re-derived by funcpair.py; 0 code pcs the tool read as sizes, by funcpair.py), and 1 pcs named in comments; no other numeral changed. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/plugin-hostd/fuzz_reply/lib/A/DMrcRhOk.v at commit 2c35faeeaec, with its module paths changed (lib.A to lib.B; the image twins A<r> to Y<r>), and its fuzz_reply.asan-ubsan addresses relocated from fuzz_reply.asan (1 numerals; per-numeral report). *)
(* Theorem Labs, 2026-10-30 (F1 priming row R3, lane B1, slice H4; integrator a Theorem Labs lane): new file. rule 24: no function
   proved here (kind: F1 priming of already proved walks: the head of __asan::QuarantineCallback::Recycle (0x33e88) at
   the re-hide twin, from the secondary arm under the re-hide (DMrcRh.rchunk_sec_rh) and the primary arm, which
   re-hides nothing, as the named read field rc_prim_mach_rh_t (the cf side discharges it with DMrcPrim.rchunk_prim_m,
   lifted)).

   WHAT.
   - the targets DIfaceRh.de_rchunk_m_rh_t, DMwalkIFRh.rchunk_m_rh_t / rchunk_ok_rh_t: reply's own field texts, by name
     (cgif's file inlines them as [de_rchunk_m_rh_t] / [rchunk_m_rh_t] / [rchunk_ok_rh_t]; ReplyDrainA dropped the three
     inlined Definitions for R3's (commit bb0215cfee16): MnRecycle.de_rchunk_m_t / DMwalkIF.rchunk_m_t /
     rchunk_ok_t over YG0dH.amreal' at YGcfRehidePost.RZ_cf with the call post YGcfRehidePost.acall_post_x_rh.
   - [rc_sec_pre_rh_t]: the read field of the re-hide's pre-state premises, DMrcRh's HULL / SREAL / M1 / M2 at the
     call, quantified like DMrcSecReads' fields.
   - [rc_sec_rehide_all_t]: DMrcRh.rc_sec_rehide_t at every call.
   - [rc_prim_mach_rh_t]: DMrcPrim.rchunk_prim_m's statement (DMrcPrim.v:236, its Section hypotheses TfibSyms B,
     rc_prim_reads and H3's cdealloc_g_t included) in its primed form: amreal' at YGcfRehidePost.RZ_cf, the call post
     YGcfRehidePost.acall_post_x_rh.  This file does not Require DMrcPrim or DMrc.
   - [rc_reads_rh]: DMrc.rc_reads with DMrcSecReads.rc_sec_step_g over the loosened post relation ARXsl (indexed by
     the slack: the post at ARXsl (YGcfRehidePost.rh_hi MAP LEN - YGcfRehidePost.rh_lo MAP)) in place of
     rc_sec_step_t, the split DMrcDefs.rc_split_t (DMrc.rc_split_t's text), and the three fields above.
   - [rchunk_ok_rh]: rc_reads_rh -> rchunk_ok_rh_t, proved as DMrc.rchunk_ok: the arm split; the PPrim arm is
     rc_prim_mach_rh_t at rchunk_ok_rh_t's TfibSyms B and cdealloc_g_t; the PSec arm is DMrcRh.rchunk_sec_rh with
     DRq (snd r0) ks zs from DMrcReads.rc_model_t (YG0dHc.amreal'_apost). *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s YO0d.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YP0j.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0p YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG00 YG0a YG01 YG04 YG02 YG06 YG07 YG03 YG0f YG0v YG0n YG0d YG0s YG0q YG0o.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YB1v YB1q YB1t YF0l YF0m YF0x YFl0 YFl1.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YO0a.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YB1w YFeq YFex YFfu.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YFfj.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YFew YFeu YFfm YFf3 YFf4 YFff YFgu YFf5 YFgw YFfb YFg8 YFfc YB13.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG08 YG0g.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import ImgBase.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import ImgBaseDG AGif2reply DGif0reply DMspec DMiface.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require ErrnoG MemnormT DMrcReads DMrcSecReads DMrcDefs DMrcRh.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import DIfaceR DMwalkIF.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YA0nH YG0dH.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YG0dHc.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require YGcfRehidePost.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require DIfaceRh DMwalkIFRh.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Set Warnings "-notation-for-abbreviation".
Open Scope Z_scope.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Open Scope am_scope.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* The read record under the re-hide, and the head.                                                                 *)
Section h.
Variable B : asyms.
Variable ARXr : Z -> alayout -> astate -> world tfibsegs -> (word -> option byte) -> Model -> Prop.
Variable ARXsl : Z -> (Z -> alayout -> astate -> world tfibsegs -> (word -> option byte) -> Model -> Prop).
Variable AOX : alayout -> astate -> Z -> Prop.
Variable DRq : astate -> list chunk -> list Z -> Prop.
Variables NMAXD LMAXD RMAXD : Z.
(* DMrcRh's HULL / SREAL / M1 / M2 at the call (the cf side reads them from the cut relation at the live pre-state). *)
Definition rc_sec_pre_rh_t : Prop :=
forall inst ly X k cbp W regs mem md r o sm i,
rcc_pre_x B ARXr inst ly X k cbp W regs mem md -> ck_beg k = PSec r o -> nth_error (st_secs X) r = Some sm ->
nth_error (st_sec_arr X) i = Some r -> In k (st_chunks X) -> ck_state k = CQuarantined ->
In (shull (YFg8.MAP ly r, YFg8.LEN sm)) (w_A W) /\
YGcfRehidePost.sec_real sm /\
Forall (zdisjoint (YFg8.MAP ly r, YFg8.LEN sm)) (sec_extents ly (YFg8.X2v X k r sm i)) /\
kMaxSize + kPage <= YFg8.LEN sm.
(* The re-hide keeps the cut relation, at every call (the cf side: YGcfRehideAR.ARcfR_rehide). *)
Definition rc_sec_rehide_all_t : Prop :=
forall inst ly X k r sm i, DMrcRh.rc_sec_rehide_t B ARXr ARXsl inst ly X k r sm i.
(* The primary arm, which re-hides nothing: DMrcPrim.rchunk_prim_m's statement with its Section hypotheses (TfibSyms B,
   rc_prim_reads, H3's cdealloc_g_t) as premises, in its primed form (amreal' at RZ_cf, acall_post_x_rh). *)
Definition rc_prim_mach_rh_t : Prop :=
TfibSyms B -> DMrcReads.rc_prim_reads B ARXr AOX DRq RMAXD -> cdealloc_g_t B ARXr AOX RMAXD ->
forall inst ly X k ks zs cbp W regs mem md off,
rcc_pre_x B ARXr inst ly X k cbp W regs mem md -> DRq X (k :: ks) zs -> ck_beg k = PPrim off ->
amreal' tfibsegs YGcfRehidePost.RZ_cf (recycle_chunk k X) W (cfg_at tfibsegs A_RChunk regs mem md)
(fun r W' c' => exists regs' mem' md',
  c' = cfg_at tfibsegs (raZ regs) regs' mem' md' /\
  YGcfRehidePost.acall_post_x_rh B ARXr AOX inst KSTACK_CF ly X W regs mem md (fun _ => False) ly (snd r) W' regs' mem' md' /\
  acall_raw_x B AOX inst KSTACK_CF ly X W regs mem md (fun _ => False) ly (snd r) W' regs' mem' md' /\
  ErrnoG.errno_kept B mem mem' /\
  MemnormT.memnorm_keep tfibsegs mem mem' /\
  (forall a, 0 <= a < 2 ^ 64 -> YFeuC.puser ly X a -> ~ (ck_base B ly k <= a < ck_base B ly k + ck_extent k) ->
   aview tfibsegs (w_H W') mem' a = aview tfibsegs (w_H W) mem a) /\
  (forall a, YFeuC.puser ly X a -> YFeuC.puser ly (snd r) a) /\
  DRq (snd r) ks zs /\ st_cache_inited (snd r) = true /\ (forall a, AOX ly (snd r) a -> AOX ly X a)).
(* DMrc.rc_reads with the primary arm as the field above, the step field over the loosened post relation ARXsl, and
   the two re-hide fields. *)
Definition rc_reads_rh : Prop :=
DMrcReads.rc_prim_reads B ARXr AOX DRq RMAXD /\ rc_prim_mach_rh_t /\
DMrcSecReads.rc_sec_cut_t B ARXr /\ DMrcSecReads.rc_sec_mapr_t B ARXr /\ DMrcSecReads.rc_sec_step_g B ARXr ARXsl AOX /\
DMrcDefs.rc_split_t DRq /\ rc_sec_pre_rh_t /\ rc_sec_rehide_all_t.

Theorem rchunk_ok_rh : rc_reads_rh -> DMwalkIFRh.rchunk_ok_rh_t B ARXr AOX DRq NMAXD LMAXD RMAXD.
Proof.
intros (RP & PRIM & RCs & RMs & RSs & RSP & RPR & RRH) TB NOK LOK ROK DS DF DV CDG.
unfold DMwalkIFRh.rchunk_m_rh_t, DIfaceRh.de_rchunk_m_rh_t.
intros inst ly X k ks zs cbp W regs mem md PRE RX.
destruct (RSP X k ks zs RX) as [(off & Hb) | (r & o & sm & i & Hb & Hsm & Hi)].
- (* the primary arm re-hides nothing *)
  exact (PRIM TB RP CDG inst ly X k ks zs cbp W regs mem md off PRE RX Hb).
- (* the secondary arm under the re-hide *)
  pose proof (DS X (k :: ks) zs k RX (or_introl eq_refl)) as [[_ HN] HE].
  pose proof RP as (HHD & HMD & _). destruct (HHD X k ks zs RX) as (Hkin & Hst & Hni).
  destruct (RPR inst ly X k cbp W regs mem md r o sm i PRE Hb Hsm Hi Hkin Hst) as (HULL & SREAL & M1 & M2).
  pose proof (YG0dHc.amreal'_apost tfibsegs YGcfRehidePost.RZ_cf _ _ W _ _ (HMD X k ks zs RX)
    (DMrcRh.rchunk_sec_rh B TB ARXr ARXsl AOX RCs RMs RSs NMAXD LMAXD NOK LOK inst ly X k cbp W regs mem md r o sm i
       PRE Hb Hsm Hi HN HE Hst Hni Hkin HULL SREAL M1 M2 (RRH inst ly X k r sm i))) as A.
  eapply YG0dH.amreal'_mono; [|exact A]. cbv beta.
  intros r0 W' c' [DQ (regs' & mem' & md' & Hc & HP & HR & HE' & HK & HV & PU & CI & AO)].
  exists regs', mem', md'. repeat (split; [assumption|]). exact AO.
Qed.
End h.
End d.
