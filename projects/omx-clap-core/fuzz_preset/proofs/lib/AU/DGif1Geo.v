(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10-31: from proofs/plugin-hostd/fuzz_reply/lib/B/DGif1Geo.v (commit ce1a656b52b7, file sha256 d4aaaa88e55e) onto omx-clap-core/fuzz_preset's ASan+UBSan image B' (fuzz_preset.asan-ubsan, pin d663f82d7f48, twin c90d4fa54d43); module paths changed; reply's image-instance names mapped to preset's B' instance (AGif2reply / AImg_reply -> AGif2cgif / AImg_cgif) and its image-row names to preset's (ReplyImg_* -> PresetImg_*, *reply -> *preset); its 0 image numerals moved by symbol from fuzz_reply.asan-ubsan (pin 10ffb5f9202a) to B' (port_addr_check 3d2eee813cce predictions; object addresses written in decimal by the same symbol map), and 0 addresses named in comments; comment references to people and refs dropped; no other numeral changed. *)
(* Modified by Theorem Labs, 2026-10: from proofs/cgif/cgif_file_fuzzer/lib/DGif1Geo.v (commit 3d8ad2aeb77e, H4 stage B (slack-indexed post relation; DMrcDefs / DGif1Geo split; re-hide head); file sha256 5f2980ad4890) onto plugin-hostd/fuzz_reply's asan image (unstripped fuzz_reply.asan, sha256 d751b179ea49; pin 42c58610e125); module paths changed; taken by path: no numeral of it names an image address, none changed. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/plugin-hostd/fuzz_reply/lib/A/DGif1Geo.v at commit 2c35faeeaec, with its module paths changed (lib.A to lib.B; the image twins A<r> to Y<r>), taken by path: no numeral of it names an image address that differs in fuzz_reply.asan-ubsan. *)
(* Theorem Labs, 2026-10-30 (lane B1, slice H4; F1 row R3): new file. rule 24: no function proved here (kind: a
   geometry lemma moved out of DGif1drM.v, unchanged).
   [win_zone_mn]: the zones of the CacheDealloc and Recycle-primary windows are mn_safe.  The text is DGif1drM.v's
   (task MEMNORM, a Theorem Labs lane), with its Section context; DGif1drM.win_zone_mn is an abbreviation of this lemma, so
   DMrcPrim (the primary arm of __asan::QuarantineCallback::Recycle) takes the lemma from here and does not need
   DGif1drM. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s YO0d.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YP0j YP0n YK0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0p YA0q YA05.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG04 YG02 YG06 YG07 YG03 YG0f YG0v YG0n YG0d YG0s YG0q YG0o YG0j YG0k YG08 YG0g.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YB1v YB1q YB1t YF0l YF0m YF0x YFl0 YFl1.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YO0a.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YB1w YFeq YFew YFeu.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YFfj YFfk YFfn YFhh.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require MemnormT. From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require MemnormHitG.
Import ListNotations.
Local Unset Lia Cache. Local Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Set Warnings "-notation-for-abbreviation".
Local Open Scope Z_scope.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* The zones of the CacheDealloc and Recycle-primary windows are mn_safe.                                           *)
(* YFg0.WIN_zone (YFg0.v:94) and YFg7.WIN_zone (YFg7.v:100) place each window byte in the stack scratch below the
   entry sp, the thread object, the primary reserve, or (Recycle's shadow cells) high memory below kHighMemBeg.
   The stack lies in high memory (lo_top: kHighMemBeg <= ly_stk_lo, ly_stk_hi <= kHighMemEnd = TASK_SIZE); the
   thread object and the primary reserve are owned extents (MemnormHitG.mn_safe_owned). *)
Lemma win_zone_mn : forall ly sp (x : word), layout_ok ly -> img_cover ly -> ly_stk_lo ly + KSTACK <= sp <= ly_stk_hi ly ->
(sp - KSTACK <= bv_unsigned x < sp) \/ (ly_T ly <= bv_unsigned x < ly_T ly + kThreadObjSize) \/
(ly_prim ly <= bv_unsigned x < ly_prim ly + kPrimResvSize) \/ (kImgEnd <= bv_unsigned x < TASK_SIZE) ->
MemnormT.mn_safe tfibsegs x.
Proof.
intros ly sp x LY IMG HSP Hz. pose proof (lo_top ly LY) as (_ & _ & _ & T4 & _ & _ & T7).
destruct Hz as [Hz|[Hz|[Hz|Hz]]].
- apply MemnormHitG.mn_safe_high. unfold KSTACK, kHighMemBeg, kHighMemEnd, kImgEnd, TASK_SIZE in *. lia.
- exact (MemnormHitG.mn_safe_owned ly (ly_T ly, kThreadObjSize) x LY IMG
    ltac:(unfold owned_extents; right; right; left; reflexivity) Hz).
- exact (MemnormHitG.mn_safe_owned ly (ly_prim ly, kPrimResvSize) x LY IMG
    ltac:(unfold owned_extents; left; reflexivity) Hz).
- exact (MemnormHitG.mn_safe_high x Hz).
Qed.
End a.
