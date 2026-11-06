(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the record that collects the runtime contracts of an image beyond cgif_file_fuzzer's AsanAPI (lib/YG0d.v:530-545), in the shape cgif_rgb_fuzzer's AsanAPI2 (lib/YG0e.v:60-72) has, with the entries plugin-hostd/fuzz_command calls and the program counters of its own image. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/plugin-hostd/fuzz_command/lib/A/Rt/RtAPI.v (donor image sha256 c0661b96b5bd), with its module paths changed and its addresses moved to reac-pw/fuzz_segconf's ASan build. *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK11 YK0s YK0i YK15 YK0j YK18 YP09.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Rt Require Import RtDefs RtStack RtShadow RtString RtNumber RtFormat RtAlloc.
Import ListNotations.
Open Scope Z_scope.

(* cgif_file_fuzzer's AsanAPI takes the side-stack classes 1 and 2 only (lib/YG0d.v:535), because its image calls
   those two. fuzz_command.asan calls the classes 0, 1, 3, 4, 5 and 7. This record carries what that one does not,
   so no file of the ported core changes. The alternative is a one-line change of AsanAPI (aa_stack_malloc taking
   every side-stack class 0 to 6 whose entry the image has); this port decides which of the two to take.

   Program counters, measured on the pinned fuzz_command.asan (sha256 c0661b96...f858bb9). A program call goes to
   the one-instruction trampoline, which jumps to the interceptor; the contract is of the trampoline. *)

Definition PC_stack_malloc_7 : Z := 0.
Definition PC_stack_free_5 : Z := 0x3ec38.
Definition PC_stack_free_7 : Z := 0.
Definition PC_set_shadow_00 : Z := 0x589dc.
Definition PC_set_shadow_f5 : Z := 0x58ae4.
Definition PC_set_shadow_f8 : Z := 0x58afc.
Definition PC_strlen : Z := 0x43a0c.
Definition PC_strndup : Z := 0.
Definition PC_strcmp : Z := 0x43a14.
Definition PC_strncmp : Z := 0x43a18.
Definition PC_strspn : Z := 0x43a30.
Definition PC_strcspn : Z := 0.
Definition PC_memchr : Z := 0x43a3c.
(* The range check every check of more than 64 bytes calls. *)
Definition PC_region_is_poisoned : Z := 0x58698.
(* The program counters the two duplicating entries give the stack unwinder for their allocation, measured on the
   image: strdup allocates at 0x4cdd0 through asan_malloc; strndup allocates by calling the malloc interceptor's
   body, so the unwinder sees the malloc entry's own return address 0x45770 under the allocation point 0x58c20
   (= pc_malloc_ra0 of this image, A/AF0l.v). *)
Definition PC_STRDUP_RA0 : Z := 0.
Definition PC_STRNDUP_RA0 : Z := 0x56ed4.
Definition PC_STRNDUP_MID : Z := 0.
Definition PC_sprintf : Z := 0.
Definition PC_snprintf : Z := 0x43a64.
Definition PC_strcat : Z := 0.
Definition PC_strcpy : Z := 0.
Definition PC_strdup : Z := 0.
Definition PC_strtol : Z := 0x43ab8.
Definition PC_atoi : Z := 0.
(* The runtime's replace_str flag byte: 0xae8b8 (the flags object the GOT word 0xa63e8 points at) + 29. *)
Definition A_FLAG_REPLACE_STR : Z := 0xa9815.
Definition PC_strtok_r : Z := 0.
(* The stack-protector cells musl's strspn, strcspn and strtok_r read: a pointer word of .got and the guard. *)
Definition A_SSP_GOT : Z := 0xa36d8.
Definition A_SSP_GUARD : Z := 0x5ff078.

Section d. Context {rc : YM05.RunCeil}.

Record CmdRtAPI (segs : list Segment) (B : asyms) := {
(* the side-stack classes of this image that AsanAPI does not take *)
rt_stack_malloc : forall {fx : YK11.FPState} cid, cid = 0 \/ cid = 3 \/ cid = 4 \/ cid = 5 ->
astack_malloc_realizes segs B cid;
rt_stack_malloc_7 : forall {fx : YK11.FPState}, astack_malloc_sz_realizes segs B PC_stack_malloc_7 7;
rt_stack_free_5 : forall {fx : YK11.FPState}, astack_free_cls_realizes segs B PC_stack_free_5 5;
rt_stack_free_7 : forall {fx : YK11.FPState}, astack_free_realizes segs B PC_stack_free_7 7;
rt_set_shadow_00 : forall {fx : YK11.FPState}, aset_shadow_realizes segs B PC_set_shadow_00 0;
rt_set_shadow_f5 : forall {fx : YK11.FPState}, aset_shadow_realizes segs B PC_set_shadow_f5 0xf5;
rt_set_shadow_f8 : forall {fx : YK11.FPState}, aset_shadow_realizes segs B PC_set_shadow_f8 0xf8;
(* the string, number and format entries *)
rt_region_ok : forall {fx : YK11.FPState}, aregion_poisoned_zero_realizes segs B PC_region_is_poisoned;
rt_strlen : forall {fx : YK11.FPState}, astrlen_realizes segs B PC_strlen;
rt_memchr_nf : forall {fx : YK11.FPState}, amemchr0_nf_realizes segs B PC_memchr;
rt_strcmp : forall {fx : YK11.FPState}, astrcmp_realizes segs B PC_strcmp;
rt_strncmp : forall {fx : YK11.FPState}, astrncmp_realizes segs B PC_strncmp;
rt_strspn : forall {fx : YK11.FPState}, astrspn_realizes segs B PC_strspn A_SSP_GOT A_SSP_GUARD;
rt_strcspn : forall {fx : YK11.FPState}, astrcspn_realizes segs B PC_strcspn A_SSP_GOT A_SSP_GUARD;
rt_strcat : forall {fx : YK11.FPState}, astrcat_realizes segs B PC_strcat;
rt_strcpy : forall {fx : YK11.FPState}, astrcpy_realizes segs B PC_strcpy;
rt_strtok_r : forall {fx : YK11.FPState}, astrtok_r_realizes segs B PC_strtok_r A_SSP_GOT A_SSP_GUARD;
rt_atoi : forall {fx : YK11.FPState}, aatoi_realizes segs B PC_atoi A_FLAG_REPLACE_STR A_SSP_GOT A_SSP_GUARD;
rt_strtol : forall {fx : YK11.FPState}, astrtol_realizes segs B PC_strtol A_SSP_GOT A_SSP_GUARD;
rt_snprintf : forall {fx : YK11.FPState}, asnprintf_realizes segs B PC_snprintf A_SSP_GOT A_SSP_GUARD;
rt_sprintf : forall {fx : YK11.FPState}, asprintf_realizes segs B PC_sprintf A_SSP_GOT A_SSP_GUARD;
(* the two allocating entries: each gives the unwinder its own program counter *)
rt_strdup : forall {fx : YK11.FPState}, astrdup_realizes segs B PC_strdup PC_STRDUP_RA0;
rt_strndup : forall {fx : YK11.FPState}, astrndup_realizes segs B PC_strndup PC_STRNDUP_RA0 PC_STRNDUP_MID
}.

End d.

Arguments rt_stack_malloc {rc segs B} _ {fx}. Arguments rt_stack_malloc_7 {rc segs B} _ {fx}.
Arguments rt_stack_free_5 {rc segs B} _ {fx}. Arguments rt_stack_free_7 {rc segs B} _ {fx}.
Arguments rt_set_shadow_00 {rc segs B} _ {fx}. Arguments rt_set_shadow_f5 {rc segs B} _ {fx}.
Arguments rt_set_shadow_f8 {rc segs B} _ {fx}.
Arguments rt_strlen {rc segs B} _ {fx}. Arguments rt_strcmp {rc segs B} _ {fx}.
Arguments rt_strncmp {rc segs B} _ {fx}. Arguments rt_strspn {rc segs B} _ {fx}.
Arguments rt_strcspn {rc segs B} _ {fx}. Arguments rt_strcat {rc segs B} _ {fx}.
Arguments rt_strtok_r {rc segs B} _ {fx}. Arguments rt_atoi {rc segs B} _ {fx}.
Arguments rt_strtol {rc segs B} _ {fx}. Arguments rt_snprintf {rc segs B} _ {fx}.
Arguments rt_sprintf {rc segs B} _ {fx}.
Arguments rt_strdup {rc segs B} _ {fx}. Arguments rt_strndup {rc segs B} _ {fx}.
Arguments rt_memchr_nf {rc segs B} _ {fx}.
Arguments rt_region_ok {rc segs B} _ {fx}. Arguments rt_strcpy {rc segs B} _ {fx}.
