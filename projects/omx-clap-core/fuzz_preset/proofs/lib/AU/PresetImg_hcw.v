(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10-31: from proofs/plugin-hostd/fuzz_reply/lib/B/ReplyImg_hcw.v (commit 4d286b2e618d, file sha256 365c556ed00b) onto omx-clap-core/fuzz_preset's ASan+UBSan image B' (fuzz_preset.asan-ubsan, pin d663f82d7f48, twin c90d4fa54d43); module paths changed; reply's image-instance names mapped to preset's B' instance (AGif2reply / AImg_reply -> AGif2cgif / AImg_cgif) and its row names to preset's (Reply* -> Preset*, *reply -> *preset); its 0 image numerals moved by symbol from fuzz_reply.asan-ubsan (pin 10ffb5f9202a) to B' (port_addr_check 3d2eee813cce predictions; object addresses written in decimal by the same symbol map), and 0 addresses named in comments; comment references to people and refs dropped; no other numeral changed. *)
(* Theorem Labs, 2026-10-30 (a prior worker, row img-hcw-B of a Theorem Labs lane's internal file REPLY-IMG-ROWS.md, for the cf layer at
   plugin-hostd/fuzz_reply). The B twin of a prior worker's lib/A/PresetImg_hcw.v hcw_A (row img-hcw-A, 
   cf407cb5886): same stem, same form.
   rule 24: no function proved (kind: image row; the constant cells against the hit walk's thread cells, at reply's
   image B, fuzz_reply.asan-ubsan).

   The row is the cf layer's image hypothesis HCW (YGcfInstHit.v:160-162 at ee95275bccb): no byte
   of a constant cell is one of the thread-object cells the hit walk writes (ImgBaseAG.WINT).  cgif's discharge is
   YGcfInstHitcgif.v:95 HCW_cgif.  Reply does not carry YGcfInstHit.v yet, so [hcw_B] states the hypothesis's text at
   reply B's instances (ImgBase.AImg at AImg_cgif, B/AGif2cgif.v:24; ImgBaseAG.WINT, B/ImgBaseAG.v:123), in the
   consumer form of B/PresetImg_depkeep.v, and a consumer closes the layer's hypothesis by `exact` once the layer is on
   reply.

   The proof is HCW_cgif's at reply's image: the constant cells lie in reply B's constant-cell zone CZONE
   (B/AGif0cgif.v:63; AGix.const_cells_zone, the vm_compute check over reply B's tables B/YF0m.v), and
   CZONE misses the WINT cells: the thread object (static extent 2) is in the application range (lo_app) and apart
   from the image window (extent 9), the context object (extent 6) and the D page (extent 7) (lo_disj); the image
   window covers the image and TFIB_TSD (img_cover); and every WINT cell lies in [T + 80, T + kThreadObjSize), past
   CZONE's 80 thread bytes. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s YO0d.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0p YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YB1v YB1q YF0l YF0m YF0x.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import ImgBase.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require Import AGif2cgif AGif0cgif.
(* Used qualified: AGis's and ImgBaseAG's names (WINT, Pv, SSLOTv) clash with each other. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require AGis. From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require ImgBaseAG. From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require PresetImg_depkeep.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require AGix.
Import ListNotations.
Local Unset Lia Cache. Local Unset Nia Cache.
Local Open Scope Z_scope.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.

(* HCW (YGcfInstHit.v:160-162; YGcfInstHitcgif.v:95 HCW_cgif's twin): the constant cells miss the thread cells the
   hit walk writes. *)
Theorem hcw_B : forall B, @im_syms AImg_cgif B ->
forall ly' c j cl', layout_ok ly' -> @im_img_cover AImg_cgif ly' -> ly_tsd ly' = as_tsd B ->
In c (as_const B ly') -> 0 <= j < Z.max 1 (Z.of_nat (c_w c)) -> 1 <= cl' <= 31 ->
~ ImgBaseAG.WINT ly' cl' (aeval B ly' (c_at c) + j).
Proof.
intros B TS ly c j cl LY IMG TSD Hc Hj Hcl Hw. change (TfibSyms B) in TS. change (img_cover ly) in IMG.
assert (HTSD : ly_tsd ly = TFIB_TSD) by (rewrite TSD; exact (ts_tsd B TS)).
pose proof (AGix.const_cells_zone B ly TS LY IMG HTSD c j Hc Hj) as CZ.
set (a := aeval B ly (c_at c) + j) in *.
destruct IMG as [I1 I2].
pose proof (lo_disj ly LY) as HD.
(* thread object (extent 2) against the image window (9), the context object (6) and the D page (7) *)
pose proof (AGis.pairwise_ij _ _ 2 6 _ _ HD eq_refl eq_refl) as DTI.
pose proof (AGis.pairwise_ij _ _ 2 3 _ _ HD eq_refl eq_refl) as DTC.
pose proof (AGis.pairwise_ij _ _ 2 4 _ _ HD eq_refl eq_refl) as DTD.
pose proof (AGis.Forall_nth' _ _ 2 _ (lo_app ly LY) eq_refl) as AT.
cbn beta in AT. unfold zdisjoint in DTI, DTC, DTD. cbn [fst snd] in DTI, DTC, DTD, AT.
unfold ImgBaseAG.WINT, ImgBaseAG.Pv, ImgBaseAG.SSLOTv in Hw. unfold CZONE in CZ.
unfold in_app, TFIB_TSD, TFIB_IMG_LO, TFIB_IMG_END, kThreadObjSize, t_cache, t_stats, t_unwinding,
  kLowShadowBeg, kHighMemBeg in *.
lia.
Qed.

End d.
