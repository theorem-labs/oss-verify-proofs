(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10-31: from proofs/plugin-hostd/fuzz_reply/lib/B/ReplyImg_oomconst.v (commit 4d286b2e618d, file sha256 df4e454263ea) onto omx-clap-core/fuzz_preset's ASan+UBSan image B' (fuzz_preset.asan-ubsan, pin d663f82d7f48, twin c90d4fa54d43); module paths changed; reply's image-instance names mapped to preset's B' instance (AGif2reply / AImg_reply -> AGif2cgif / AImg_cgif) and its row names to preset's (Reply* -> Preset*, *reply -> *preset); its 0 image numerals moved by symbol from fuzz_reply.asan-ubsan (pin 10ffb5f9202a) to B' (port_addr_check 3d2eee813cce predictions; object addresses written in decimal by the same symbol map), and 1 addresses named in comments; comment references to people and refs dropped; no other numeral changed. *)
(* Theorem Labs: reply image row img-oomconst-B of the cf layer at plugin-hostd/fuzz_reply.
   rule 24: no function proved (kind: closed image fact over the constant-cell table of reply's image B,
   fuzz_reply.asan-ubsan, pin 10ffb5f9202a).

   oom_const_img : oom_const_t, proofs/cgif/cgif_file_fuzzer/lib/YGcfInstMiss.v:312-314 (Definition) / :316 (Hypothesis)
   @ 90854e46e5c, over its Section's Variable B under TS : im_syms B.  Reply does not carry YGcfInstMiss.v nor
   YGcfInstBase.v, so the Lemma states the body of oom_const_t VERBATIM at a B with image B's symbol facts (im_syms of
   AImg_cgif, B/AGif2cgif.v:24, which is YF0m.TfibSyms), with the premise ly_img_ok B ly unfolded; ly_img_ok is
   proofs/cgif/cgif_file_fuzzer/lib/YGcfInstBase.v:140-142 @ 90854e46e5c (= @ e73dee6cc107):
   ly_img_ok B ly := layout_ok ly /\ ly_tsd ly = as_tsd B /\
                     Forall (fun r => zr_sub r (ly_img ly)) (as_owned_static B ++ as_zero_shadow B).
   Proof at image B: the SYM cells of Tfib_const_sym (B/YF0m.v:32-37) at AT / AC / AD lie in the owned extents
   (ly_T, 4096), (ly_C, 256), (ly_D, 4096), which lo_disj keeps apart from ly_img, while an owned-static byte lies in
   ly_img (the third conjunct): no such cell has an owned-static byte.  ATsd 0 is TFIB_TSD's slot (the second conjunct
   with ts_tsd); ATp / AInst are fixed by TfibSyms: all apart from TFIB_OOM = 0x12d960 (B/YF0m.v:19).  The absolute and
   shadow cells avoid TFIB_OOM by computation (YFi5.abs_cells_okJ, B/YFi5.v:347, cgif's discharge). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YP0j.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d YG0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YB1v YB1q YF0l YF0m YF0x.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import ImgBase.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require Import AGif2cgif.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YFi5.
Import ListNotations.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

(* An owned extent of a layout_ok layout is apart from its image window (lo_disj over static_extents). *)
Lemma owned_apart_img : forall {rc : YM05.RunCeil} ly e, layout_ok ly -> In e (owned_extents ly) -> zdisjoint e (ly_img ly).
Proof.
intros rc ly e LO He.
apply (pairwise_In zdisjoint (static_extents ly) _ _ (owned_extents ly) [(ly_stk_lo ly, ly_stk_hi ly - ly_stk_lo ly); ly_img ly]
  eq_refl (lo_disj _ LO) He). right; left; reflexivity.
Qed.
Local Ltac mem_owned := unfold owned_extents; cbn [In]; repeat (first [left; reflexivity | right]).

Section r. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.

(* oom_const_img at image B, over ly_img_ok (unfolded). *)
Lemma oom_const_img_B : forall B, @im_syms AImg_cgif B ->
  forall ly c k,
  (layout_ok ly /\ ly_tsd ly = as_tsd B /\ Forall (fun r => zr_sub r (ly_img ly)) (as_owned_static B ++ as_zero_shadow B)) ->
  In c (as_const B ly) -> 0 <= k < Z.max 1 (Z.of_nat (c_w c)) ->
  Exists (in_zr (aeval B ly (c_at c) + k)) (as_owned_static B) -> aeval B ly (c_at c) + k <> as_oom_byte B.
Proof.
intros B TS ly c k (LO & HTSD & SUB) Hc Hk HO. change (TfibSyms B) in TS. rewrite (ts_oom B TS).
(* the owned-static byte lies in the image window *)
assert (IMGb : fst (ly_img ly) <= aeval B ly (c_at c) + k < fst (ly_img ly) + snd (ly_img ly)).
{ apply Exists_exists in HO as (r & Hr & Hin).
  destruct (proj1 (Forall_forall _ _) SUB r (in_or_app _ _ _ (or_introl Hr))) as [S1 S2].
  unfold in_zr in Hin. lia. }
(* the owned extents of the SYM cells are apart from the image window *)
pose proof (owned_apart_img ly (ly_T ly, kThreadObjSize) LO ltac:(mem_owned)) as DT.
pose proof (owned_apart_img ly (ly_C ly, 256) LO ltac:(mem_owned)) as DC.
pose proof (owned_apart_img ly (ly_D ly, 4096) LO ltac:(mem_owned)) as DD.
clear SUB HO.
rewrite (ts_const B TS ly) in Hc. unfold Tfib_const in Hc. apply in_app_iff in Hc as [Hc|Hc].
- pose proof (ts_tp B TS) as ETP. pose proof (ts_inst B TS) as EIN. rewrite (ts_tsd B TS) in HTSD.
  unfold Tfib_const_sym in Hc. cbn [In] in Hc.
  repeat match type of Hc with
  | _ \/ _ => destruct Hc as [<-|Hc];
      [cbn [c_at c_w aeval c8 c4 c2 c1 z8 z4 z2 z1] in Hk, IMGb |- *; cbn in Hk; rewrite ?ETP, ?EIN, ?HTSD in *;
       unfold zdisjoint in DT, DC, DD; cbn [fst snd] in DT, DC, DD;
       unfold TFIB_OOM, TFIB_TP, TFIB_INST, TFIB_TSD, o_space, o_rinfo, o_sec_chunks, kThreadObjSize in *; lia |]
  | False => destruct Hc
  end.
- pose proof (proj1 (forallb_forall _ _) YFi5.abs_cells_okJ c Hc) as K. unfold YFi5.abs_cell_okJ in K.
  destruct (c_at c) eqn:Ea; try discriminate K. cbn [aeval].
  apply Bool.orb_prop in K as [K|K]; apply Z.leb_le in K; lia.
Qed.

End r.
