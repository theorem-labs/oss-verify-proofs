(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: lines 18-46 of proofs/libreac/fuzz_knock/lib/A/APgBase.v
   (origin/ossv/recipes 4b6f0df50aa7: in_roP, arodata_okP, ro_below_ofl, ro_spares, arodata_ok_journalP), in the
   form projects/reac-pw/fuzz_qdisc/proofs/lib/A/QPgBase.v states them, for libdiginet/fuzz_codec's ASan builds; knock's
   afobj / apost_base are not carried (codec hands its callees objects that are 4-aligned, so the contracts use
   the caller-journal shapes of lib/A/Prog/CodecCJ.v instead). The rest of this file is codec's own. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_codec/lib/A/Prog/CPgBase.v, with its module paths and module names changed; 10 of its 29 lines of code are new or changed and 221 lines of the source are left out. *)
(* reac-pw/fuzz_headamp image B (fuzz_headamp.asan-ubsan, pinned sha256
   53edda9bdeeba1803865babfecb1af6732babe47ab83c64d38cc59a90d717a94; every address measured on the unstripped twin
   1674e30a0698f381704e66d2398d7906c881f4ba8fc619cb41b89fb97ad112ff): THE STATIC FACTS the walk of
   LLVMFuzzerTestOneInput (0x80c40) takes at each of its five middle contracts' starts, at image B's record
   lib/AU/HPgImgB.v headamp_himg_B. The same text as image A's lib/A/HPgHarn.v hq_static_law at image A's record:
   hd_seg_pre's static conjuncts (lib/A/HPgCSpec.v) are image-free, only the record differs. Statement text only:
   no function is proved here (kind: statement text).

   The whole run is chained (lib/AU/HPgTop.v) in this order:
     ENTRY --E01--> C1 --M01 headamp_build_contract--> C2 --malloc(pod)--> C3 --M02 headamp_dup_contract--> C4
     --malloc(out)--> C5 --M03 headamp_check_contract--> C6 --malloc(first)--> C7 --M04a headamp_first_contract-->
     C8 --M04b headamp_plain_contract--> C9 --X01 (the four frees)--> J --X01 (the frame's release, the epilogue)-->
     the return.
   Every harness-level cut is stated relative to the harness's ENTRY state (lib/AU/HPgSegM.v hqu_hcx) and states
   only what the chaining cannot derive. Left out on purpose is what hd_seg_pre asks of the symbols and the image:
   the registered globals' shadow (the 43 rows of asan_globals), the strings' bytes and shadow (hd_cstr), the
   read-only 8-byte cells, the stack-guard pair (the GOT word 0x9d478, whose value is the guard object's address
   0x5f8210, and that guard word) and rom_view. They are static facts of the symbols B and the image (the
   start-up's const cells and zero-shadow ranges, AR's am_const / al_zshadow, the owned read-only bytes pinned as
   const cells), not facts a cut can carry: a global's shadow byte and an owned read-only byte are aowned, and the
   allocator's post keeps no aowned byte (YG0d.v acall_post). The chaining takes this law at each middle
   contract's start, at the state's AR and the read-only agreement the journal keeps. *)
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YK11 YK14 YK0s YK15 YK18 YP09 YI04 YI08 YN3v YI00 YI0m YI09.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.A Require Import HPgBase HPgCSpec.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.AU Require Import HPgImgB.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.

Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable segs : list Segment.
Variable B : asyms.
Variables RLO RHI : Z.

(* hd_seg_pre's static conjuncts at image B's record, at any state AR accepts with the read-only data as in the
   image. *)
Definition hqu_static_law : Prop :=
forall ly S (W : world segs) mem md,
AR segs B ly S W mem md -> arodata_okP segs RLO RHI B (aview segs (w_H W) mem) ->
Forall (fun g => range_addressable (aview segs (w_H W) mem) SHADOW_OFF (fst g) (snd g)) (hi_globs headamp_himg_B) /\
Forall (fun s => hd_cstr segs (w_H W) mem (fst s) (snd s)) (hi_strs headamp_himg_B) /\
hd_ro_cells segs (w_H W) mem (hi_cells headamp_himg_B) /\
hd_guard_ok (aview segs (w_H W) mem) (hi_gotw headamp_himg_B) (hi_guard headamp_himg_B) /\
rom_view segs W mem.

End b.
