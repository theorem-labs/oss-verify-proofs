(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: lines 18-46 of proofs/libreac/fuzz_knock/lib/A/APgBase.v
   (origin/ossv/recipes 4b6f0df50aa7: in_roP, arodata_okP, ro_below_ofl, ro_spares, arodata_ok_journalP), in the
   form projects/reac-pw/fuzz_qdisc/proofs/lib/A/QPgBase.v states them, for libdiginet/fuzz_codec's ASan builds; knock's
   afobj / apost_base are not carried (codec hands its callees objects that are 4-aligned, so the contracts use
   the caller-journal shapes of lib/A/Prog/CodecCJ.v instead). The rest of this file is codec's own. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_codec/lib/A/Prog/CPgBase.v, with its module paths and module names changed; 10 of its 28 lines of code are new or changed and 222 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/A/RPgHarn.v at 3c7e900fc63 (its lines 218-231, rh_static_law) for reac-pw/fuzz_headamp image A; module paths changed, rh_ renamed to hq_, the facts are those of lib/A/HPgCSpec.v hd_seg_pre's static conjuncts at lib/A/HPgImgA.v headamp_himg_A (headamp's strings in hd_cstr form and the stack-guard pair musl's strtol reads, which role's program has not); role's cut states and segment statements (lines 1-216) are not taken: headamp's are stated in lib/A/HPgE01D.v (C1, E01), lib/A/HPgSegC23.v (C2, C3, the malloc(pod) step), lib/A/HPgM24Out.v (C4, the malloc(out) step) and lib/A/HPgSegM.v (C5 .. C9, the retirement join J, the return, the malloc(first) step and X01's two parts). *)
(* reac-pw/fuzz_headamp image A (fuzz_headamp.asan, pinned sha256
   f3e0669d2819724922df0556b11c2dcd22d1e16fe7e0fe1535ce784b34436c47; every address measured on the unstripped twin
   b5f352154c54a97c66fd92dfa228e8a854498f6cd313dba0107900546b043f9a, same loaded bytes except .note.gnu.build-id): THE STATIC FACTS the walk
   of LLVMFuzzerTestOneInput (0x80bc0) takes at each of its five middle contracts' starts. Statement text only: no
   function is proved here (kind: statement text).

   The whole run is chained (lib/A/HPgTop.v) in this order:
     ENTRY --E01--> C1 --M01 headamp_build_contract--> C2 --malloc(pod)--> C3 --M02 headamp_dup_contract--> C4
     --malloc(out)--> C5 --M03 headamp_check_contract--> C6 --malloc(first)--> C7 --M04a headamp_first_contract-->
     C8 --M04b headamp_plain_contract--> C9 --X01 (the four frees)--> J --X01 (the frame's release, the epilogue)-->
     the return.
   Every harness-level cut is stated relative to the harness's ENTRY state (lib/A/HPgSegM.v hq_hcx) and states only
   what the chaining cannot derive. Left out on purpose is what hd_seg_pre asks of the symbols and the image: the
   registered globals' shadow, the strings' bytes and shadow (hd_cstr), the read-only 8-byte cells, the stack-guard
   pair (the GOT word 0x9cff8, an owned byte range that a const cell pins to 0x5f7d90; the guard 0x5f7d90, readable
   from the image's .bss segment through mbyte's fall-back to seg_rom) and rom_view. They are static facts of the
   symbols B and the image (the start-up's const cells and zero-shadow ranges, AR's am_const / al_zshadow, the owned
   read-only bytes pinned as const cells), not facts a cut can carry: a global's shadow byte and an owned read-only
   byte are aowned, and
   the allocator's post keeps no aowned byte (YG0d.v acall_post). The chaining takes this law at each middle
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
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.A Require Import HPgBase HPgCSpec HPgImgA.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.

Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable segs : list Segment.
Variable B : asyms.
Variables RLO RHI : Z.

(* hd_seg_pre's static conjuncts at image A's record, at any state AR accepts with the read-only data as in the
   image. *)
Definition hq_static_law : Prop :=
forall ly S (W : world segs) mem md,
AR segs B ly S W mem md -> arodata_okP segs RLO RHI B (aview segs (w_H W) mem) ->
Forall (fun g => range_addressable (aview segs (w_H W) mem) SHADOW_OFF (fst g) (snd g)) (hi_globs headamp_himg_A) /\
Forall (fun s => hd_cstr segs (w_H W) mem (fst s) (snd s)) (hi_strs headamp_himg_A) /\
hd_ro_cells segs (w_H W) mem (hi_cells headamp_himg_A) /\
hd_guard_ok (aview segs (w_H W) mem) (hi_gotw headamp_himg_A) (hi_guard headamp_himg_A) /\
rom_view segs W mem.

End b.
