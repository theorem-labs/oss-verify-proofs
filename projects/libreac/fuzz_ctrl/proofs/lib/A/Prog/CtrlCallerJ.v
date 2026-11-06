(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* fuzz_ctrl image A: the caller-journal shapes the program walks share (tcj_kept, twr_ok, tsrc_ok). Copied verbatim
   from projects/libreac/fuzz_grant/proofs/lib/A/Prog/CtrlFinish.v:111-143 (where
   grant's ctrl_finish walk defines them for its slice), with the module prefix fuzz_grant -> fuzz_ctrl and grant's
   listing / Grant* modules -> ctrl's (ctrl_listing, CtrlSyms / CtrlList / CtrlAddr / CtrlPa / CtrlPaLib / CtrlBase).
   ctrl_finish itself is not walked in ctrl's port (it is a leaf inside ctrl_emit_as's lifted stretch), so the shapes
   live in this file of their own. The caller-journal form is cgif's (projects/cgif/cgif_file_fuzzer/proofs/lib/YC20.v:311-365). *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation Znumtheory.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00 YI16.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require Import
PaTable PaSym PaShadow PaStep PaRun PaJournal CtrlSyms CtrlList CtrlAddr CtrlPa CtrlPaLib CtrlBase.
Import ListNotations.
Local Unset Lia Cache. Local Unset Nia Cache.
Open Scope bv_scope.
Open Scope Z_scope.

Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section d.
Context {PI : PAImg ctrl_listing}.
#[local] Notation SEGS := (@pa_segs _ ctrl_listing PI).
Section e.
Variable B : asyms.

(* What a call keeps: everything but its own stack window and the bytes E it is allowed to write
   (cgif lib/YC20.v:311-323). *)
Definition tcj_kept (STK : Z) (lyc : alayout) (Sc : astate) (W : world SEGS) (memc : word -> option byte)
(W2 : world SEGS) (mem2 : word -> option byte) (sp : Z) (E : Z -> Prop) : Prop :=
(forall a, alloc_ceiling <= a < 2 ^ 64 -> ~ (sp - STK <= a < sp) -> ~ E a ->
aview SEGS (w_H W2) mem2 a = aview SEGS (w_H W) memc a) /\
(forall b m i, In (b, m) (ablocks B lyc Sc) -> 0 <= i < req_size m -> ~ E (b + i) ->
aview SEGS (w_H W2) mem2 (b + i) = aview SEGS (w_H W) memc (b + i)) /\
(forall a, in_img SEGS a -> ~ Exists (in_zr a) (as_owned_static B) -> ~ (as_errno B <= a < as_errno B + 4) ->
aview SEGS (w_H W2) mem2 a = aview SEGS (w_H W) memc a) /\
(forall cid pos a, In (cid, pos) (frames Sc) ->
(in_zr a (frame_rng lyc (cid, pos)) \/ in_zr a (shadow_addr (frame_addr lyc cid pos), fs_frame_bytes cid / 8)) ->
~ E a -> aview SEGS (w_H W2) mem2 a = aview SEGS (w_H W) memc a) /\
(forall a, alloc_ceiling <= a < 2 ^ 64 -> ~ (sp - STK <= a < sp) -> apresent (w_H W) memc a -> apresent (w_H W2) mem2 a) /\
(forall a, sp - STK <= a < sp -> apresent (w_H W2) mem2 a).

(* The caller's right to let the call write [q, q + n) (cgif lib/YC20.v:358-359). *)
Definition twr_ok (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate)
(lyc : alayout) (Sc : astate) (own : list (Z * Z)) (W : world SEGS) (memc : word -> option byte)
(sp q n : Z) : Prop :=
forall a, q <= a < q + n ->
awr_byte STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own a /\
apresent (w_H W) memc a /\ ~ aowned B lyc Sc a /\ ~ (sp - ESTACK <= a < sp).

(* A range the call reads. *)
Definition tsrc_ok (W : world SEGS) (memc : word -> option byte) (sp q n : Z) : Prop :=
(forall a, q <= a < q + n -> aview SEGS (w_H W) memc a <> None /\ ~ (sp - ESTACK <= a < sp)) /\
range_addressable (aview SEGS (w_H W) memc) SHADOW_OFF q n /\
shadow_hull_vis (aview SEGS (w_H W) memc) q n /\ amem_range q n /\ 0 <= q /\ q + n <= 2 ^ 63.
End e.
End d.
End b.
