(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: from proofs/cgif/cgif_file_fuzzer/lib/DMrcReads.v (commit 5ad50e61fc6a, file sha256 78734be5a5a4) onto omx-clap-core/fuzz_preset's asan image (unstripped fuzz_preset.asan, sha256 bff8519bbe3e; #102 pin 1be0f53d96cb); module paths changed; its 0 image addresses moved by code-verified function pairs (0 port_addr_check e55e1b52a8a0 MAPS predictions, each code one re-derived by the internal file funcpair.py; 0 code pcs the tool read as sizes, by the internal file funcpair.py), and 2 pcs named in comments; no other numeral changed. *)
(* Theorem Labs, 2026-10-30 (head H4 of the interface DMwalkIF.v at dc3949af11c): the READ FIELDS of
   __asan::QuarantineCallback::Recycle (0x34810) over the opaque cut relation [ARXr] and recycle invariant [DRq].
   rule 24: no function proved here (kind: field statements; head H4's walk is DMrcPrim.v / DMrcSec.v).

   WHY.  DMwalkIFA.rchunk_ok_t gives head H4 rcc_pre_x, the recycle invariant, di_frame_t, di_rview_x_t and
   drq_sizes.  The released Recycle walk (YFh7.segRC over AFgs.free_hyps for a primary chunk; YFg8 / YFgv for a
   secondary one) reads far more than that: the layout, the chunk's header words, the region-info word, the thread
   stats, the shadow's presence and the runner's seed, which cgif takes from ARm (YFfr.FH_ok, YFf4).  Over an opaque
   [ARXr] those are FIELDS: head H4 proves [rc_reads -> rchunk_ok_t] (DMrc.v), and the cf instance discharges
   [rc_reads] at ARXr_cf / DRq_cf (CfF2b); at cgif they are YFfr.FH_ok / YFf3 / YFf4.
   SHAPE (a Theorem Labs lane 00:20Z, as H3's F12): a CUT-READ field (what the walk reads at the call), a STEP-TRANSPORT field
   (the relation after the walk's own writes: MEQ outside the window, the written values, presence on the window, the
   image's constant cells still holding (review RevRcReads F1), with the side facts), and MODEL-ONLY fields (the recycle invariant and the owned / user sets along the model's
   step).  The no-map primary step and the secondary's unmapping step are SIBLING fields.
   No size literal: a primary chunk's n is below its class size (rz + n <= class_size <= kMaxSize, AFgs.class_facts),
   and the secondary's bounds are the Section Variables NMAXD / LMAXD of DMwalkIFA.v (DMrcSec.v). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s YO0d.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YP0j.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0p YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG04 YG03 YG0f YG0v YG0n YG0d YG0s YG0q YG0k.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import AB1v AB1q AB1t AF0l AF0m AF0x AFl0 AFl1.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YO0a.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import AB1w AFeq AFew AFeu.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require AFgs AFf3.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import ImgBase ImgBaseDG.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import AImgA ADIfaceA.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import DMspec DMiface DIfaceR.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import DMwalkIFA.
Import ListNotations.
Local Set Warnings "-abstract-large-number".
Local Set Warnings "-notation-for-abbreviation".
Open Scope Z_scope.
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Open Scope am_scope.

Section rr.
Variable B : asyms.
Variable ARXr : Z -> alayout -> astate -> world tfibsegs -> (word -> option byte) -> Model -> Prop.
Variable AOX : alayout -> astate -> Z -> Prop.
Variable DRq : astate -> list chunk -> list Z -> Prop.
Variable RMAXD : Z.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* MODEL-ONLY fields.                                                                                               *)
(* The chunk at the head of the recycle invariant is a live, quarantined chunk of the state, no longer in the quarantine's
   items (cgif: RIx_head). *)
Definition rc_head_t : Prop :=
forall X k ks zs, DRq X (k :: ks) zs ->
In k (st_chunks X) /\ ck_state k = CQuarantined /\ ~ In (ck_beg k) (map ck_beg (q_items X)).

(* Along every path of the model's step, the recycle invariant moves to the rest of the list (cgif: recycle_chunk_okx +
   RIx_rc_step).  The owned-set and user-range steps are the step fields' and the callee posts' (review RevRcReads F3). *)
Definition rc_model_t : Prop :=
forall X k ks zs, DRq X (k :: ks) zs -> apost (recycle_chunk k X) (fun r => DRq (snd r) ks zs).

(* ---------------------------------------------------------------------------------------------------------------- *)
(* PRIMARY chunk: the CUT-READ field.  What YFh7.segRC reads at 0x34810, as the released walk's own premise record
   (AFgs.free_hyps, AFgs.v:140-160): at cgif this is YFfr.FH_ok (YFfr.v:471). *)
Definition rc_prim_fh_t : Prop :=
forall inst ly X k ks zs cbp W regs mem md off,
rcc_pre_x B ARXr inst ly X k cbp W regs mem md -> DRq X (k :: ks) zs -> ck_beg k = PPrim off ->
inst = as_inst B /\ ly_tsd ly = as_tsd B /\ Forall (cell_holds B ly (aview tfibsegs (w_H W) mem)) (as_const B ly) /\
exists hb1 muc j1 j2,
AFgs.free_hyps W ly regs mem (prim_class off) (ck_base B ly k) (ck_rz k) (ck_n k) hb1 cbp muc j1 j2.

(* PRIMARY chunk: the STEP-TRANSPORT field (no map change).  At the tail call into CacheDealloc (AFgs.at_CD) the
   walk's writes lie in AFf3.D (the stack window, the chunk's header words, the thread stats, the chunk's shadow;
   YFg7.WIN_D); the relation then holds at the model's intermediate state AFf3.X1 (the chunk deleted), with
   CacheDealloc's model premises for the user object (cd_model), and the window lies in the owned set or the stack
   scratch.  The memory facts are the walk's own frame (cgif: YFg7.CDPRE from AFf3.rc_fin_ARm). *)
Definition rc_prim_step_t : Prop :=
forall inst ly X k ks zs cbp W regs mem md off mem' md',
rcc_pre_x B ARXr inst ly X k cbp W regs mem md -> DRq X (k :: ks) zs -> ck_beg k = PPrim off ->
(forall a, 0 <= a < 2 ^ 64 -> ~ AFf3.D B ly k (spZ regs) a -> aview tfibsegs (w_H W) mem' a = aview tfibsegs (w_H W) mem a) ->
(forall a, aview tfibsegs (w_H W) mem a <> None -> aview tfibsegs (w_H W) mem' a <> None) ->
(forall a, AFf3.DH B ly k a -> aview tfibsegs (w_H W) mem a <> None -> aview tfibsegs (w_H W) mem' a = Some shHeapLeftRz) ->
(forall a, in_band_rw a -> w_H W (w64 a) = true -> mem' (w64 a) = mem (w64 a)) ->
Forall (cell_holds B ly (aview tfibsegs (w_H W) mem')) (as_const B ly) ->
m_vmmaps md' = m_vmmaps md -> m_vm_lazy md' = m_vm_lazy md -> eager_used md' = eager_used md ->
ARXr inst ly (AFf3.X1 X k) W mem' md' /\
cd_model RMAXD (AFf3.X1 X k) (prim_class off) off /\
(forall a, 0 <= a < 2 ^ 64 -> AFf3.D B ly k (spZ regs) a -> AOX ly X a \/ AFf3.DS (spZ regs) a) /\
(forall a, AOX ly (AFf3.X1 X k) a -> AOX ly X a) /\
(forall a, YFeuC.puser ly X a -> ~ (ck_base B ly k <= a < ck_base B ly k + ck_extent k) -> ~ AFf3.D B ly k (spZ regs) a).

(* The record of the slice's reads (primary half; the secondary half is DMrcSec.rc_sec_reads). *)
(* CacheDealloc's free-array GROWTH room at the cut (DMwalkIFA.cd_pre_cx's last conjunct, WalkB1 ffbbfde0c14): on the
   growth arm (its branch test as the guard) the model's budget has room for the free array's map.  A READ of the cut
   state; the cf layer gives it from its room (room_wA_parts_cf / room_rec_cf). *)
Definition rc_prim_room_t : Prop :=
forall inst ly X k ks zs cbp W regs mem md off,
rcc_pre_x B ARXr inst ly X k cbp W regs mem md -> DRq X (k :: ks) zs -> ck_beg k = PPrim off ->
(rg_mapped_fa (reg X (prim_class off)) < 4 * (fa_len (rg_free (reg X (prim_class off))) + max_cached (prim_class off) / 2) ->
 eager_used md + A_bytes (w_A W) + 2 * kUserMapSize + 32768 <= vm_limit (m_vmmaps md)).

Definition rc_prim_reads : Prop :=
rc_head_t /\ rc_model_t /\ rc_prim_fh_t /\ rc_prim_step_t /\ rc_prim_room_t.
End rr.
End d.
