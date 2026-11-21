(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YCe5.v, with its module paths changed. *)
(* Modified by Theorem Labs, 2026-10: off_img's image bounds cite fuzz_knock's image (YImgTop.IMG_LO, YImgTop.IMG_TOP = 0x5f3000, both knock ASan builds) in place of cgif's 0x10000 and 0x5fb000. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/libreac/fuzz_knock/lib/Reusable/YCe5.v (fuzz_knock's released ASan tree); module paths changed to reac-pw/fuzz_headamp. *)
(* Modified by Theorem Labs, 2026-11: made from Reusable/YCe5.v for the ASan run at the 16 GiB limit (lib/BudgetWit/AW), with the modules it imports from that set renamed to their twins (suffix _w). *)
(* Modified by Theorem Labs, 2026-11: internal commit ids in comments replaced by public commits or removed. *)
(* Theorem Labs, 2026-11: cut to the declarations the usage path at 16 GiB uses. *)
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require YZ00.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require YImgTop.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From Stdlib Require Import FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.BudgetWit.AW Require Import YK18_w.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YK0j YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YI04.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YK04 YA0i.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.BudgetWit.AW Require Import YA0n_w YA0o_w YA0q_w.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YG00 YG0a YG01 YG0f.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.BudgetWit.AW Require Import YG0n_w YG0d_w.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Export YM04.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.
Ltac appn := unfold app_addr, in_app, amem_range, ASAN_CEIL, kLowShadowBeg, kLowMemEnd, kHighMemBeg, kHighMemEnd, kHighShadowEnd, kImgLo in *.
Ltac zlia := appn; lia.
Section e. Context {rc : YM05.RunCeil}.
Definition frame_rng (ly : alayout) (f : Z * Z) : Z * Z := (frame_addr ly (fst f) (snd f), fs_frame_bytes (fst f)).
Section t.
Variable segs : list Segment.
Variable B : asyms.
Local Notation code := (as_code B).
Local Notation AIw W md := (AI segs (w_H W) (w_A W) md).
Definition astk_ok (STK : Z) (ly : alayout) (sp0 : Z) : Prop :=
sp0 mod 16 = 0 /\ 0 <= STK /\ alloc_ceiling <= ly_stk_lo ly /\ ly_stk_lo ly + STK <= sp0 /\ sp0 <= ly_stk_hi ly /\
ly_stk_hi ly <= 2 ^ 47 /\ ly_bot ly + STK < sp0 + ASTACK /\ sp0 <= ly_top ly /\ ly_top ly <= ly_stk_hi ly.
Definition ajournal (STK sp0 : Z) (FP : list (Z * Z))
(ly : alayout) (S : astate) (W : world segs) (mem : word -> option byte) (md : Model)
(own : list (Z * Z))
(ly' : alayout) (S' : astate) (W' : world segs) (mem' : word -> option byte) (md' : Model) (k : Z) : Prop :=
AR segs B ly' S' W' mem' md' /\
layout_le (length (st_secs S)) ly ly' /\ (length (st_secs S) <= length (st_secs S'))%nat /\ wle W W' /\ same_io md md' /\
frames S' = own ++ frames S /\
st_nev S' <= st_nev S + k /\ 0 <= k /\
(forall a, alloc_ceiling <= a < 2 ^ 64 -> ~ (sp0 - STK <= a < sp0) ->
aview segs (w_H W') mem' a = aview segs (w_H W) mem a) /\
(forall p n i, In (p, n) (ablocks B ly S) -> In (p, n) (ablocks B ly' S') -> 0 <= i < req_size n ->
~ inFP FP (p + i) -> aview segs (w_H W') mem' (p + i) = aview segs (w_H W) mem (p + i)) /\
(forall a, in_img segs a -> ~ Exists (in_zr a) (as_owned_static B) -> ~ (as_errno B <= a < as_errno B + 4) ->
aview segs (w_H W') mem' a = aview segs (w_H W) mem a) /\
(forall cid pos a, In (cid, pos) (frames S) ->
(in_zr a (frame_rng ly (cid, pos)) \/ in_zr a (shadow_addr (frame_addr ly cid pos), fs_frame_bytes cid / 8)) ->
~ inFP FP a -> aview segs (w_H W') mem' a = aview segs (w_H W) mem a) /\
(forall p n i, In (p, n) (ablocks B ly S) -> ~ In (p, n) (ablocks B ly' S') -> 0 <= i < req_size n -> inFP FP (p + i)) /\
(forall a, sp0 - STK <= a < sp0 -> apresent (w_H W') mem' a) /\
astk_ok STK ly sp0 /\
qtight S'                                              .
Lemma asan_consts : (0x7fff7f800000 <= alloc_ceiling <= 0x7fffff800000) /\ kHighShadowEnd = 0x10007fff8000 /\ kHighMemBeg = 0x10007fff8000 /\
kHighMemEnd = 0x800000000000 /\ kLowMemEnd = 0x7fff8000.
Proof. split; [exact (proj1 alloc_ceiling_val)|]. repeat split; reflexivity. Qed.
Lemma mbyte_of_aview : forall H H' (m m' : word -> option byte) a,
aview segs H' m' a = aview segs H m a -> mbyte segs (mrestrict H' m') a = mbyte segs (mrestrict H m) a.
Proof.
intros H H' m m' a E. unfold aview in E.
destruct (mbyte segs (mrestrict H' m') a) as [b'|], (mbyte segs (mrestrict H m) a) as [b|]; cbn in E; try discriminate; [|reflexivity].
injection E as E. f_equal. apply bv_eq. exact E.
Qed.
Lemma apresent_writable : forall H (m : word -> option byte) a,
apresent H m a -> writable_at segs (mrestrict H m) a.
Proof.
intros H m a [Hh [b Hb]]. unfold writable_at, wview, mrestrict. rewrite Hh, Hb. discriminate.
Qed.
End t.
Section f0.
Variable segs : list Segment.
Variable B : asyms.
Lemma val_mem_kept : forall H H' (m m' : word -> option byte) a n v,
(forall k, 0 <= k < Z.of_nat n -> aview segs H' m' (a + k) = aview segs H m (a + k)) ->
val_mem segs (mrestrict H m) a n v -> val_mem segs (mrestrict H' m') a n v.
Proof.
intros H H' m m' a n v Hk Hv k Hkn. rewrite (mbyte_of_aview segs H H' m m' (a + Z.of_nat k)); [apply Hv, Hkn|]. apply Hk. zlia.
Qed.
Local Notation ajournal := (ajournal segs B).
End f0.
End e.
