(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: the three target statements de_rchunk_m_rh_t / rchunk_m_rh_t / rchunk_ok_rh_t are Required from the light files DIfaceRh.v / DMwalkIFRhA.v (the cgif texts of reply's) and their inline Definitions here are dropped, as in reply's DMrcRhOk.v; no proof changes. *)
(* Modified by Theorem Labs, 2026-10: from proofs/cgif/cgif_file_fuzzer/lib/DMrcRhOk.v (commit d95decb76fc2, file sha256 19c15b91256c) onto omx-clap-core/fuzz_preset's asan image (unstripped fuzz_preset.asan, sha256 bff8519bbe3e; #102 pin 1be0f53d96cb); module paths changed; its 0 image addresses moved by code-verified function pairs (0 port_addr_check e55e1b52a8a0 MAPS predictions, each code one re-derived by the internal file funcpair.py; 0 code pcs the tool read as sizes, by the internal file funcpair.py), and 1 pcs named in comments; no other numeral changed. *)
(* Theorem Labs, 2026-10-30 (F1 priming row R3, lane B1, slice H4; integrator a Theorem Labs lane): new file. rule 24: no function
   proved here (kind: F1 priming of already proved walks: the head of __asan::QuarantineCallback::Recycle (0x34810) at
   the re-hide twin, from the secondary arm under the re-hide (DMrcRhA.rchunk_sec_rh) and the primary arm, which
   re-hides nothing, as the named read field rc_prim_mach_rh_t (the cf side discharges it with DMrcPrim.rchunk_prim_m,
   lifted)).

   WHAT.
   - the targets DIfaceRh.de_rchunk_m_rh_t, DMwalkIFRhA.rchunk_m_rh_t / rchunk_ok_rh_t, by name (the light files of
     the statements; this file inlined them before, as [de_rchunk_m_rh_t] / [rchunk_m_rh_t] / [rchunk_ok_rh_t], over
     tfibsegs): MnRecycle.de_rchunk_m_t / DMwalkIFA.rchunk_m_t / rchunk_ok_t over YG0dH.amreal' at
     YGcfRehidePost.RZ_cf with the call post YGcfRehidePost.acall_post_x_rh.
   - [rc_sec_pre_rh_t]: the read field of the re-hide's pre-state premises, DMrcRh's HULL / SREAL / M1 / M2 at the
     call, quantified like DMrcSecReads' fields.
   - [rc_sec_rehide_all_t]: DMrcRhA.rc_sec_rehide_t at every call.
   - [rc_prim_mach_rh_t]: DMrcPrim.rchunk_prim_m's statement (DMrcPrim.v:236, its Section hypotheses TfibSyms B,
     rc_prim_reads and H3's cdealloc_g_t included) in its primed form: amreal' at YGcfRehidePost.RZ_cf, the call post
     YGcfRehidePost.acall_post_x_rh.  This file does not Require DMrcPrim or DMrc.
   - [rc_reads_rh]: DMrc.rc_reads with DMrcSecReadsA.rc_sec_step_g over the loosened post relation ARXsl (indexed by
     the slack: the post at ARXsl (YGcfRehidePost.rh_hi MAP LEN - YGcfRehidePost.rh_lo MAP)) in place of
     rc_sec_step_t, the split DMrcDefs.rc_split_t (DMrc.rc_split_t's text), and the three fields above.
   - [rchunk_ok_rh]: rc_reads_rh -> rchunk_ok_rh_t, proved as DMrc.rchunk_ok: the arm split; the PPrim arm is
     rc_prim_mach_rh_t at rchunk_ok_rh_t's TfibSyms B and cdealloc_g_t; the PSec arm is DMrcRhA.rchunk_sec_rh with
     DRq (snd r0) ks zs from DMrcReadsA.rc_model_t (YG0dHc.amreal'_apost). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s YO0d.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YP0j.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0p YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG04 YG02 YG06 YG07 YG03 YG0f YG0v YG0n YG0d YG0s YG0q YG0o.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import AB1v AB1q AB1t AF0l AF0m AF0x AFl0 AFl1.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YO0a.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import AB1w AFeq AFex AFfu.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YFfj.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import AFew AFeu AFfm AFf3 AFf4 AFff AFgu AFf5 AFgw AFfb AFg8 AFfc AB13.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG08 YG0g.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import ImgBase ImgBaseDG.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import AImgA ADIfaceA.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import DMspec DMiface.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require ErrnoG MemnormT.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require DMrcReadsA DMrcSecReadsA DMrcRhA.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require DMrcDefs.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import DIfaceR.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import DMwalkIFA.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YA0nH YG0dH.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YG0dHc YGcfRehidePost.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require DIfaceRh.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require DMwalkIFRhA.
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
In (shull (AFg8.MAP ly r, AFg8.LEN sm)) (w_A W) /\
YGcfRehidePost.sec_real sm /\
Forall (zdisjoint (AFg8.MAP ly r, AFg8.LEN sm)) (sec_extents ly (AFg8.X2v X k r sm i)) /\
kMaxSize + kPage <= AFg8.LEN sm.
(* The re-hide keeps the cut relation, at every call (the cf side: YGcfRehideAR.ARcfR_rehide). *)
Definition rc_sec_rehide_all_t : Prop :=
forall inst ly X k r sm i, DMrcRhA.rc_sec_rehide_t B ARXr ARXsl inst ly X k r sm i.
(* The primary arm, which re-hides nothing: DMrcPrim.rchunk_prim_m's statement with its Section hypotheses (TfibSyms B,
   rc_prim_reads, H3's cdealloc_g_t) as premises, in its primed form (amreal' at RZ_cf, acall_post_x_rh). *)
Definition rc_prim_mach_rh_t : Prop :=
TfibSyms B -> DMrcReadsA.rc_prim_reads B ARXr AOX DRq RMAXD -> cdealloc_g_t B ARXr AOX RMAXD ->
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
DMrcReadsA.rc_prim_reads B ARXr AOX DRq RMAXD /\ rc_prim_mach_rh_t /\
DMrcSecReadsA.rc_sec_cut_t B ARXr /\ DMrcSecReadsA.rc_sec_mapr_t B ARXr /\ DMrcSecReadsA.rc_sec_step_g B ARXr ARXsl AOX /\
DMrcDefs.rc_split_t DRq /\ rc_sec_pre_rh_t /\ rc_sec_rehide_all_t.

Theorem rchunk_ok_rh : rc_reads_rh -> DMwalkIFRhA.rchunk_ok_rh_t B ARXr AOX DRq NMAXD LMAXD RMAXD.
Proof.
intros (RP & PRIM & RCs & RMs & RSs & RSP & RPR & RRH) TB NOK LOK ROK DS DF DV CDG.
unfold DMwalkIFRhA.rchunk_m_rh_t, DIfaceRh.de_rchunk_m_rh_t.
intros inst ly X k ks zs cbp W regs mem md PRE RX.
destruct (RSP X k ks zs RX) as [(off & Hb) | (r & o & sm & i & Hb & Hsm & Hi)].
- (* the primary arm re-hides nothing *)
  exact (PRIM TB RP CDG inst ly X k ks zs cbp W regs mem md off PRE RX Hb).
- (* the secondary arm under the re-hide *)
  pose proof (DS X (k :: ks) zs k RX (or_introl eq_refl)) as [[_ HN] HE].
  pose proof RP as (HHD & HMD & _). destruct (HHD X k ks zs RX) as (Hkin & Hst & Hni).
  destruct (RPR inst ly X k cbp W regs mem md r o sm i PRE Hb Hsm Hi Hkin Hst) as (HULL & SREAL & M1 & M2).
  pose proof (YG0dHc.amreal'_apost tfibsegs YGcfRehidePost.RZ_cf _ _ W _ _ (HMD X k ks zs RX)
    (DMrcRhA.rchunk_sec_rh B TB ARXr ARXsl AOX RCs RMs RSs NMAXD LMAXD NOK LOK inst ly X k cbp W regs mem md r o sm i
       PRE Hb Hsm Hi HN HE Hst Hni Hkin HULL SREAL M1 M2 (RRH inst ly X k r sm i))) as A.
  eapply YG0dH.amreal'_mono; [|exact A]. cbv beta.
  intros r0 W' c' [DQ (regs' & mem' & md' & Hc & HP & HR & HE' & HK & HV & PU & CI & AO)].
  exists regs', mem', md'. repeat (split; [assumption|]). exact AO.
Qed.
End h.
End d.
