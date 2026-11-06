(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: the statement of the walk of libreac/fuzz_scene's LLVMFuzzerTestOneInput in the
   asan-ubsan build: the text of lib/A/P_LLVMFuzzerTestOneInput.v (the asan build) over this image's names and
   numbers, in the released form of proofs/cgif/cgif_file_fuzzer (c8557374ad2e): the entry contract is scene's own
   `scene_tfib_lib_contract_x` (lib/AU/P_LLVMFuzzerTestOneInput_ctx.v, the text of lib/A's: A/ACfn.v:59-69 with the
   changes a Theorem Labs lane's ENTRY-REVIEW.md required), and the Section hypotheses follow A/ACfj.v:94-127 (the donor's
   harness walk) and A/ACk1.v:62-110 (its position-abstract walks), module paths changed.  STATEMENTS ONLY (rule 24):
   the walk `scene_llvmf : scene_llvmf_stmt`, proved in Section h under its hypotheses, is not in this file; its
   SEGMENT CUTS are lib/AU/P_LLVMFuzzerTestOneInput_seg.v.  Module layout (gate 6o, a Theorem Labs lane): every module of the
   trunk's lib/Reusable and every shared contract from lib.Reusable; the A twins, the listing lib.AU.Prog and the
   modules outside the trunk's lib/Reusable whose closure reaches YCbq (YCbq, YC5d, YE01, YCbp) from lib.AU. *)

(*   Image: fuzz_scene.asan-ubsan, sha256 e98b1ed286c1aa5c3d558cb2069011d2413d58b2122f741531364382a528833f
   (pau-pipeline/libreac/bin/fuzz_scene/), symbols from the unstripped twin
   (unstripped/fuzz_scene/fuzz_scene.asan-ubsan, sha256 ef0b41158fe08b45b5a8a0e514f8ebc31f2960d2b90acc03576a682fae2baf33,
   same loaded bytes apart from the ELF header's section-table fields and the build-id note). The numbers this file
   uses, each by its symbol, with the measured value:
     - LLVMFuzzerTestOneInput = 0x828a4, 2544 bytes; the listing's base (scene_text) and AF_LLVMFuzzerTestOneInput = 0
       (lib/AU/Prog/SceneAddr.v, SceneList.v), so A_LLVMF = BASE + AF_LLVMFuzzerTestOneInput.
     - RA_LLVMF = 0x827a0 = target_run (0x826d4) + 0xcc, after `jal` 0x8279c -> 0x828a4.
     - A_EMPTY = 0x5d6160 = oft_aligned_copy.empty (32 bytes).  target_run passes it when n = 0: s4 = 0x5d6150
       (target_run.initialized; `auipc` 0x82708, `addi` 0x8270c), s1 = s4 + 0x10 (0x82780), a0 = s1 (0x82794).
       cgif's A/ACfn.v:20 value falls inside builtin_tls (at +0x1c90) in this image (ENTRY-REVIEW.md RC2).
     - the closed sink's cells (ENTRY-REVIEW.md RC1), from the twin's .symtab: __libc = 0x5f6d28 (104 bytes), so its
       `threaded` byte is 0x5f6d29; ofl_lock = 0x5f7188 (4 bytes); ofl_head = 0x5f7190 (8 bytes), which is also the
       sink head scene_sink_head.
     - reac_ctrl_build_scene_step.TAIL_TRAILER = 0x20e20 (STT_OBJECT, 32 bytes), registered in the asan_globals
       record at 0xa0380 as (0x20e20, size 12, size with redzone 32), bytes 00 00 03 00 00 00 01 00 00 00 00 00
       (MEASURED); its shadow is a static fact of B (HB_Z_TT, HB_C_TT below), not a clause of the contract.
     - frame: `addi sp,sp,-0xe0` 0x828a4 (224), `andi sp,sp,-0x20` 0x828e4 (realign: 0 or 16 more, sp0 being
       16-aligned): every call runs at sp0 - 224 or sp0 - 240, so LLVMF_SPDROP = 240.
     - fake frame: class 8 (LLVMF_CID), __asan_stack_malloc_8 0x3f438 called at 0x82918 with a0 = 0x24c0 = 9408
       (LLVMF_FRAME; `lui a0,2` 0x82910, `addiw a0,a0,0x4c0` 0x82914); __asan_stack_free_8 0x3f5b4 called at 0x831a8
       with a0 = s4 (the frame) and a1 = 0x24c0 (0x8319c-0x831a0). fs_frame_bytes 8 = 16384.
     - __asan_set_shadow_f8 0x569d0 (calls 0x82a0c, 0x83154), __asan_set_shadow_00 0x568b0 (call 0x830bc; the call
       0x831b8 is on the real-stack arm only), __asan_memset 0x53e8c, __asan_memcpy 0x539f0, __wrap_bcmp 0x44338,
       __wrap_malloc 0x54d44, __wrap_free 0x54d40: lib/AU/Prog/SceneAddr.v scene_sigma, by their SS_ names.
     - the six allocator call sites, return address = BASE + AF_LLVMFuzzerTestOneInput + offset:
       malloc 0x82c4c (ra +0x3ac = 0x82c50), 0x82e6c (+0x5cc = 0x82e70), 0x82fa8 (+0x708 = 0x82fac);
       free 0x82f9c (+0x6fc = 0x82fa0), 0x8315c (+0x8bc = 0x83160), 0x83164 (+0x8c4 = 0x83168).
     - the allocator's own return pcs, pc_malloc_ra0 (as_code B) = 0x54fe0 (__interceptor_malloc 0x54f18 + 0xc8,
       after `jal` 0x54fdc) and pc_free_ra0 (as_code B) = 0x54e80 (__interceptor_free 0x54d48 + 0x138, after `jal`
       0x54e7c); a Theorem Labs lane's universe (a working branch a219644fba4, lib/AU/YCej.v:35-55) holds the 12
       traces [pc; ra] and [pc; ra; 0x827a0] of these sites.
     - reac_scene_placeholder = 0x20e80 (STT_OBJECT, 11136 bytes with its redzone; registered size 8904 in its
       asan_globals record at 0xa0400), read through GOT word 0x9c6b8 (`auipc` 0x82c64, `ld` 0x82c68) for i < 8904
       (`srli a0,a1,3` / `bltu 0x458,a0` 0x82c70-0x82c74).
     - shadow base: as_shadow_cell B = __asan_shadow_memory_dynamic_address 0xa3af8, through GOT 0x9ba40 (`ld s10`
       0x82904). UAR flag: as_uar_cell B = __asan_option_detect_stack_use_after_return 0xa3b00 (.bss, SHT_NOBITS:
       initial value 0), through GOT 0x9ba98 (`lw a2` 0x82900, decision `beqz a2` 0x8290c). These two are named in
       this file only as as_shadow_cell B / as_uar_cell B; their bindings are PALib's (lib/AU/Prog/ScenePaLib.v:
       objects 16, 17).
     - the read-only window RLO..RHI is PI_scene's pa_relro_lo / pa_relro_hi (lib/AU/Prog/SceneImg.v: 0x9b4e0..0x9c740,
       the listing at a working branch ae48bfd851f).
     - this build's 23 UBSan trap branches (to `unimp` 0x83234) and the `unimp` 0x83240 after `jal abort` add no
       hypothesis: each guard tests an address in the input block, in a block from the three mallocs or in the fake
       frame for wrap-around, and the facts that keep it untaken come from the entry contract's pre, the allocator
       and stack-malloc posts and AR (each one: the review sheet STMT-REVIEW-1-AU.md, section 3.6).
   THE UAR FLAG IS NOT A HYPOTHESIS (ENTRY-REVIEW.md item 5, R4).  The walk reads the flag through `al_const`
   (AR_const_law, YG0d.v:460-466) on the entry state's AR, as cgif A/ACf5.v:198 does; AR carries `asyms_ok B`
   (YG0n.v:208), whose `aso_const_law` second conjunct (YG0f.v:188-189) is the fact.  Measured chain for the value:
   the cell's only writer is `sw a0,0(a1)` 0x5b888 in __asan::AsanInitInternal (0x5b74c), storing
   `lbu a0,0x1f(s0)` of __asan::asan_flags_dont_use_directly (0xa12f8 + 0x1f), whose built-in default is 1
   (InitializeFlags builds a3 = 0x0101010000000001 at 0x3f804-0x3f868 and stores it with `sd a3,0x18(s3)` 0x3f8f4);
   that writer runs once, from .preinit_array's __asan_init (0x9b4d8 -> 0x5bc6c, which calls AsanInitInternal at
   0x5bcdc), before __asan::asan_inited (0xa47d8) is set to 1 at 0x5b924, and every later entry returns at
   0x5b76c/0x5b778.
   LAWS AND SMP ARE NOT HYPOTHESES EITHER (ENTRY-REVIEW.md R4): `AR_laws SEGS B` is the theorem
   `AR_laws_ok SEGS B` (Reusable/YG0q.v:803) and `stack_malloc_progressP B` is `ml_stack_malloc_progress` of ML
   (YG0d.v:520-521).
   Owners of the hypotheses below (each marked at its line), all Theorem Labs lanes: the glue (the sink's laws
   sink_img_laws of G_Sink, the PALib / PALibF / ML / FFL instances); the malloc/free contracts and HTRACE;
   memcpy, memset and bcmp; the class-8 stack-malloc leaf and its asan-ubsan table (the
   shared lib/Reusable/AsStackSz.v and lib/Reusable/StackFreeDef.v are landed); SetShadowDef;
   build_scene_step, which in this build calls reac_ctrl_block_cksum_stamp 0x83930 out of line at 0x83d34,
   scene_build and set_mac; check_step's contract and the frame lemma file lib/AU/P_check_step_frame.v;
   the static shadow facts of B (two lanes, one of them the glue's); and the start-up certificate
   that discharges them (a lane, or the composition). *)
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.AU.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00 YI16.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.AU Require Import YCbq YC5d.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import YG0s.
(* A Theorem Labs lane's glue stages these from cgif_file_fuzzer: lib_shape (YO09), the image laws (YE00, YE01), ameter_triv
   (YCbp). *)
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import YO09 YE00.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.AU Require Import YE01 YCbp.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.AU.Prog Require Import PaRun PaShadow SceneSyms SceneList SceneAddr ScenePa SceneImg.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.AU.Prog Require Import PaJournal ScenePaLib SceneBase SceneRo SceneFrame.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import YM05.
(* A Theorem Labs lane (landed) and a Theorem Labs lane: the three shared runtime contract types, one copy each -- no file of mine
   defines any of them.  astack_malloc_sz_realizes <- lib/Reusable/AsStackSz.v, astack_free_realizes <-
   lib/Reusable/StackFreeDef.v, aset_shadow_realizes <- lib/Reusable/SetShadowDef.v (from a Theorem Labs lane,
   at 798447a1772 proofs/libreac/fuzz_grant/lib/A/Rt/SetShadowDef.v:19, at scene's relocated
   path). *)
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import AsStackSz StackFreeDef SetShadowDef.
(* scene_shape is image-independent and lives in lib/SceneAsanBase.v (split out of lib/A/SceneAsanTop.v by
   a Theorem Labs lane, 2026-10-29, so that this asan-ubsan file needs nothing from lib/A). *)
From OSSVerify.Proofs.libreac.fuzz_scene.lib Require SceneAsanBase.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.AU Require Import P_LLVMFuzzerTestOneInput_ctx J_StackSz.
(* The three callee walks of a Theorem Labs lane, written in a separate worktree, now in this tree (the Require below). *)
From OSSVerify.Proofs.libreac.fuzz_scene.lib.AU Require Import P_reac_ctrl_build_scene_step P_reac_ctrl_scene_build P_reac_ctrl_scene_set_mac.
(* A Theorem Labs lane: the class-8 table's asan-ubsan twin, lib/AU/Rt/StackMalloc8Tbl.v (its asan file,
   at 08cb863a87d, names this twin): CID8 = 8 and
   PC_STACK_MALLOC_8 = 0x3f438 = __asan_stack_malloc_8 of this image. *)
From OSSVerify.Proofs.libreac.fuzz_scene.lib.AU.Rt Require Import StackMalloc8Tbl.
(* A Theorem Labs lane: check_step's asan-ubsan contract tcheck_step_specX (the sink head is its explicit first argument,
   gate 6h) and its window TCHECK_STEP_STK = 8496, exported from lib/AU/P_check_step_cut.v:66-70
   (at aa04a8e2795; the same value as asan). *)
From OSSVerify.Proofs.libreac.fuzz_scene.lib.AU Require Import P_check_step P_check_step_cut.
(* A Theorem Labs lane: the fake-frame region setup for every class and size, `frame_setup : forall segs val B cid n,
   frame_setup_stmt segs val B cid n`, in its asan-ubsan twin lib/AU/P_check_step_frame.v (the asan file is Qed at
   aa91b415da2, the asan-ubsan twin at 9aad9023964; both are Qed with kernel primitives
   only, of record at 55f2a74be63).  It replaces this file's former local copy of frame_setup_stmt and its hypothesis HFRAME8;
   the walk uses the instance `frame_setup SEGS VAL B 8 9408`. *)
From OSSVerify.Proofs.libreac.fuzz_scene.lib.AU Require Import P_check_step_frame.
(* A Theorem Labs lane: sink_img_laws, the laws of the closed sink's own cells, from the glue's asan-ubsan G_Sink (the path
   its lib/A/G_Sink.v names for this image; the text names no image value). *)
From OSSVerify.Proofs.libreac.fuzz_scene.lib.AU Require Import G_Sink.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.
(* The fake-stack class and frame size of LLVMFuzzerTestOneInput (stack_malloc_8 / stack_free_8 with a0 / a1 = 9408). *)
Definition LLVMF_CID : Z := 8.
Definition LLVMF_FRAME : Z := 9408.
(* The most the function moves sp before any call: 224 of frame plus 16 of realignment. *)
Definition LLVMF_SPDROP : Z := 240.
(* Allocator events on the longest path: three mallocs (0x82c4c, 0x82e6c, 0x82fa8) and three frees (0x82f9c,
   0x8315c, 0x83164). *)
Definition LLVMF_EV : Z := 6.
(* The largest heap request: n' + (n' == 0) with n' a 16-bit field of the input or 8904. Two such blocks are live
   at once (body and before; body and again, both 8904). *)
Definition LLVMF_NMAX : Z := 65535.
(* reac_scene_placeholder and its registered size. *)
Definition A_reac_scene_placeholder : Z := 0x20e80.
Definition LLVMF_SCENE_BYTES : Z := 8904.
(* reac_ctrl_build_scene_step.TAIL_TRAILER and its registered size (RC3). *)
Definition A_TAIL_TRAILER : Z := 0x20e20.
Definition TAIL_TRAILER_N : Z := 12.
(* The closed sink's cells (RC1): __libc + 1, ofl_lock, ofl_head, each with the width the clause reads as 0. *)
Definition SCENE_SINK_OWNED : list (Z * Z) := [(0x5f6d29, 1); (0x5f7188, 4); (0x5f7190, 8)].
(* The return addresses of the six allocator calls, as offsets in LLVMFuzzerTestOneInput. *)
Definition RT_malloc1_off : Z := 0x3ac.
Definition RT_malloc2_off : Z := 0x5cc.
Definition RT_malloc3_off : Z := 0x708.
Definition RT_free1_off : Z := 0x6fc.
Definition RT_free2_off : Z := 0x8bc.
Definition RT_free3_off : Z := 0x8c4.
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
(* RC1: scene's own sink head, musl's ofl_head of this image.  It is an instance, not a Context, so that RO below
   speaks about scene's head and not about cgif's. *)
#[local] Instance scene_sink_head : OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable.YI16.sink_head := {| OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable.YI16.sk_ofl_head := 0x5f7190 |}.
#[local] Existing Instance SceneAsanBase.scene_shape.
#[local] Notation SEGS := (@pa_segs _ scene_listing PI_scene).
#[local] Notation VAL := (@pa_val _ scene_listing PI_scene).
#[local] Notation SIGMA := (@pa_sigma _ scene_listing PI_scene).
#[local] Notation BASE := (@pa_val _ scene_listing PI_scene A_TEXT).
#[local] Notation RLO := (@pa_relro_lo _ scene_listing PI_scene).
#[local] Notation RHI := (@pa_relro_hi _ scene_listing PI_scene).
Definition RT_malloc1_ra : Z := BASE + AF_LLVMFuzzerTestOneInput + RT_malloc1_off.
Definition RT_malloc2_ra : Z := BASE + AF_LLVMFuzzerTestOneInput + RT_malloc2_off.
Definition RT_malloc3_ra : Z := BASE + AF_LLVMFuzzerTestOneInput + RT_malloc3_off.
Definition RT_free1_ra : Z := BASE + AF_LLVMFuzzerTestOneInput + RT_free1_off.
Definition RT_free2_ra : Z := BASE + AF_LLVMFuzzerTestOneInput + RT_free2_off.
Definition RT_free3_ra : Z := BASE + AF_LLVMFuzzerTestOneInput + RT_free3_off.

Section h.
Variable B : asyms.
(* A Theorem Labs lane: the entry's constants, the parameters of scene_tfib_lib_contract_x.  A_EMPTY is the SIXTH (order
   fixed with a Theorem Labs lane, 2026-10-28 22:33Z). *)
Variables A_LLVMF RA_LLVMF EV_LIB LIVE_LIB LLVMF_STK A_EMPTY : Z.
(* A Theorem Labs lane: the read-only range stays below the sink's overflow head (cgif A/ACeh.v ro_tfa_below_ofl). *)
(* gate 6h: the sink head is passed BY NAME here.  Left implicit, Coq could resolve it to a global instance (the
   released plain YI5b.src0_sink_head, or cgif's AE2k.tfib_sink_head), and RO would then be about another unit's
   overflow head. *)
Context {RO : ro_below_ofl (SK := scene_sink_head) SEGS RLO RHI}.

(* -- the entry's own facts, each bound by symbol -- *)
Hypothesis HA_LLVMF : A_LLVMF = BASE + AF_LLVMFuzzerTestOneInput.
(* target_run's call site: `jal 0x8279c` -> 0x828a4. *)
Hypothesis HRA_LLVMF : RA_LLVMF = 0x827a0.
(* n = 0: target_run passes oft_aligned_copy.empty: s4 = 0x5d6150 (0x82708-0x8270c), s1 = s4 + 0x10 (0x82780),
   a0 = s1 (0x82794). *)
Hypothesis HA_EMPTY : A_EMPTY = 0x5d6160.
(* Budgets the glue's constants must meet (HAND1-PLAN.md section 2.4): six allocator events, two live blocks of at
   most 65535 bytes, and the deepest callee window below the realigned sp (the allocators' ASTACK, YG0d.v:18; and
   check_step's window TCHECK_STEP_STK = 8496, a Theorem Labs lane).  Every other callee window (ESTACK, 2 * ESTACK for bcmp,
   48 / 16 / 32 + ESTACK for build_scene_step / set_mac / scene_build) is below ASTACK, so HSTK is the binding one:
   240 + 16384 = 16624, against 240 + 8496 = 8736 for check_step. *)
Hypothesis HEV : LLVMF_EV <= EV_LIB.
Hypothesis HLIVE : 2 * LLVMF_NMAX <= LIVE_LIB.
Hypothesis HSTK : LLVMF_SPDROP + ASTACK <= LLVMF_STK.
Hypothesis HSTK_CS : LLVMF_SPDROP + TCHECK_STEP_STK <= LLVMF_STK.

(* The TAIL_TRAILER bytes that a Theorem Labs lane's build_scene_step premise asks for.  Only the two NEGATIVE conditions are
   assumed: the shadow half is derivable from HB_Z_TT / HB_C_TT (al_zshadow + am_const) and the image half
   (in_roP and the twelve ROM bytes = scene_trailer) is provable by vm_compute, while nothing in the statement
   constrains as_owned_static B or as_errno B at 0x20e20 -- arodata_okS (Reusable/YE01.v:190-193) needs exactly
   these and AR_owned_image_law (YG0d.v:474-475) does not give them.  Minimal form ruled by a Theorem Labs lane at
   03:48Z over the wider ro_bytes shape: assuming the derivable ten twelfths would weaken the theorem.  Lanes S2,
   S3, S4, both images. *)
Hypothesis HRO_TT : forall i, 0 <= i < 12 ->
  ~ Exists (in_zr (0x20e20 + i)) (as_owned_static B) /\ ~ (as_errno B <= 0x20e20 + i < as_errno B + 4).

(* reac_scene_placeholder's bytes and the GOT word through which S1 reads it (a Theorem Labs lane's S1 finding, ruled into
   Section h by a Theorem Labs lane at 04:39Z), in HRO_TT's minimal shape: only the two NEGATIVE conditions; the image-byte
   half stays a segment-side fact.  SYMBOLIC: the length is LLVMF_SCENE_BYTES (8904, the asan_globals
   descriptor's size), NEVER the symbol's st_size 11136, which includes the redzone and would overlap the owned
   row (0x23148, 0x8b8).  The GOT word is the listing's object 4 (VAL (A_OBJ 4): 0x9c6b8 here, 0x9c388 in asan),
   the only .got word holding 0x20e80.  Zero margin above in both images, as with HRO_TT. *)
Hypothesis HRO_PL : forall i, 0 <= i < LLVMF_SCENE_BYTES ->
  ~ Exists (in_zr (A_reac_scene_placeholder + i)) (as_owned_static B) /\
  ~ (as_errno B <= A_reac_scene_placeholder + i < as_errno B + 4).
Hypothesis HRO_PLGOT : forall i, 0 <= i < 8 ->
  ~ Exists (in_zr (VAL (A_OBJ 4) + i)) (as_owned_static B) /\ ~ (as_errno B <= VAL (A_OBJ 4) + i < as_errno B + 4).

(* -- framework laws: relocation (a Theorem Labs lane) and the glue's instances (cgif A/ACfj.v:97-105, A/ACk1.v:64-74, :82).
   AR_laws and stack_malloc_progressP are NOT hypotheses: they are AR_laws_ok (YG0q.v:803) and a field of ML
   (YG0d.v:520-521), per ENTRY-REVIEW.md R4. -- *)
Hypothesis TL : PALib (L := scene_listing) (PI := PI_scene) B.
Hypothesis TLF : PALibF (L := scene_listing) (PI := PI_scene) B.
Hypothesis ML : model_laws (as_universe B).
Hypothesis FFL : frame_flag_lawP SEGS B.

(* -- the closed sink (RC1): its cells are the image's, and the laws about them are a Theorem Labs lane's, in the parameter
   form it fixed (2026-10-28 22:33Z).  `sink_img_laws` must give, for every range of SINK_OWNED, what cgif's
   `ail_env` (YE01.v:29) gives for its own: the range is in the image, is not static-owned, is not the errno cell
   and is not inside the context block, so the walk's writes never touch it and the post's clause is kept. -- *)
Hypothesis AIL : sink_img_laws SEGS B SCENE_SINK_OWNED.

(* -- the static shadow the walk and its callees read.  Two rulings shape this: a Theorem Labs lane's CHECKSTEP-REVIEW.md
   item 7 (a BLANKET globs_marked / img_shadow_vis over every AR state is not implied by AR, so neither is taken)
   and an internal review's item R2, through a Theorem Labs lane's CUTS.md:605-609 (a PER-STATE block_shadow of a global is lost at the first
   runtime call, because a global's shadow byte lies in the shadow of lm_zone, YG0n.v:227, hence is `aowned`, and
   astack_malloc_realizes YG0d.v:298-299 keeps only bytes that are not aowned).  So every such fact is a STATIC
   fact of B, read at any state through AR's `am_const` / `al_zshadow`, and neither the entry contract nor a cut
   carries it.  The two objects the walk needs: reac_scene_placeholder (read in the fill loop) and
   reac_ctrl_build_scene_step.TAIL_TRAILER (which build_scene_step's spec names at both accepting call sites).
   MEASURED cells, re-derived for this image from its asan_globals records (0xa0300..0xa0440: check_step.trailer,
   __const.check_step.frame, TAIL_TRAILER at 0xa0380, .str.4, the placeholder at 0xa0400 -- the same five (address,
   size, size with redzone) triples as the asan image's), which agree with a Theorem Labs lane's GlobShadow certificate as
   a Theorem Labs lane copied it for asan (CUTS.md:611-628):
   the placeholder (0x20e80, 8904 = 1113 whole granules) lies inside the zero range (0x20e60, 0x23148 - 0x20e60),
   and the f9 run above it starts at shadow_addr 0x23148 = 0x7fffc629; TAIL_TRAILER (0x20e20, 12) has its first
   granule inside the zero range (0x20e00, 0x20e28 - 0x20e00), its second granule's cell is
   `z1 (ANum 0x7fffc1c5) 0x4` (= shadow_addr (0x20e20 + 8)), and the two redzone cells above it are 0xf9.
   Owners: two Theorem Labs lanes (B's tables), a third lane (the start-up certificate that the start state meets
   them). -- *)
Definition TT_SHCELLS : list acell :=
z1 (ANum (shadow_addr (A_TAIL_TRAILER + 8))) (TAIL_TRAILER_N mod 8)
:: map (fun k => z1 (ANum (shadow_addr (A_TAIL_TRAILER + 8) + 1 + Z.of_nat k)) 0xf9) (seq 0 2).
Definition PL_SHCELLS : list acell :=
map (fun k => z1 (ANum (shadow_addr (A_reac_scene_placeholder + LLVMF_SCENE_BYTES) + Z.of_nat k)) 0xf9) (seq 0 8).
Hypothesis HZS_PL : in_zs B A_reac_scene_placeholder LLVMF_SCENE_BYTES.
Hypothesis HB_C_PL : forall ly, Forall (fun c => In c (as_const B ly)) PL_SHCELLS.
Hypothesis HB_Z_TT : in_zs B (A_TAIL_TRAILER - 0x20) (0x20 + (TAIL_TRAILER_N - TAIL_TRAILER_N mod 8)).
Hypothesis HB_C_TT : forall ly, Forall (fun c => In c (as_const B ly)) TT_SHCELLS.

(* -- runtime contracts -- *)
(* A Theorem Labs lane (AM_*.v): the wrappers; the walk derives the journal rules (YCbp.v:30-56 amalloc04_rule_triv,
   afree04_rule_triv) under ameter_triv. *)
Hypothesis AMALLOC : amalloc_realizes SEGS B.
Hypothesis AFREE : afree_realizes SEGS B.
(* A Theorem Labs lane. *)
Hypothesis AMEMSET : aintrin_realizes SEGS B OSet (SIGMA SS___asan_memset).
Hypothesis AMEMCPY : aintrin_realizes SEGS B OCpy (SIGMA SS___asan_memcpy).
Hypothesis ABCMP : abcmp_realizes SEGS B (SIGMA SS___interceptor_trampoline_bcmp).
(* Two Theorem Labs lanes, landed: lib/Reusable/AsStackSz.v, lib/Reusable/StackFreeDef.v, lib/Reusable/SetShadowDef.v
   (cgif_rgb YG0e.v:17 / :34 / :48).  Class 8 is NOT in the AsanAPI record, so its stack-malloc leaf is taken
   under a Theorem Labs lane's own name (23:23Z, per a Theorem Labs lane's ruling), over a Theorem Labs lane's table twin lib/AU/Rt/StackMalloc8Tbl.v
   (PC_STACK_MALLOC_8 = 0x3f438 = __asan_stack_malloc_8, CID8 = 8); do not use aa_stack_malloc for cid 8. *)
Hypothesis stack_malloc_8_sz : astack_malloc_sz_realizes SEGS B PC_STACK_MALLOC_8 CID8.
Hypothesis ASF8 : StackFreeDef.astack_free_realizes SEGS B (SIGMA SS___asan_stack_free_8) LLVMF_CID.
Hypothesis ASH00 : SetShadowDef.aset_shadow_realizes SEGS B (SIGMA SS___asan_set_shadow_00) 0.
Hypothesis ASHF8 : SetShadowDef.aset_shadow_realizes SEGS B (SIGMA SS___asan_set_shadow_f8) 0xf8.

(* -- the program's callees -- *)
(* A Theorem Labs lane: stated on the caller's journal (YCbq.v:1955-1977 aj_intrin_at shape), the caller's own frames
   quantified. *)
Hypothesis BSS : treac_ctrl_build_scene_step_spec (SK := scene_sink_head) (PI := PI_scene) B.
Hypothesis SSB : treac_ctrl_scene_build_spec (SK := scene_sink_head) (PI := PI_scene) B.
Hypothesis SSM : treac_ctrl_scene_set_mac_spec (SK := scene_sink_head) (PI := PI_scene) B.
(* A Theorem Labs lane: check_step's contract; its sink head is an explicit first argument (gate 6h). *)
Hypothesis TCHECKX : tcheck_step_specX scene_sink_head B.
(* A Theorem Labs lane's frame_setup is a lemma (lib/AU/P_check_step_frame.v; Qed in lib/A and in lib/AU): no
   hypothesis; the walk applies
   `frame_setup SEGS VAL B LLVMF_CID LLVMF_FRAME`, i.e. `frame_setup SEGS VAL B 8 9408`. *)

(* -- allocation traces: a Theorem Labs lane proves this instance of P_LLVMFuzzerTestOneInput_ctx.rt_trace_in_stmt (in
   lib/AU/P_LLVMFuzzerTestOneInput_trace.v, over its universe lib/AU/YCej.v Tfib_universe with the glue's binding of
   as_universe B and as_code B, as cgif A/ACeh.v:26, :33 tl_code / tl_universe). -- *)
Hypothesis HTRACE : rt_trace_in_stmt SEGS RA_LLVMF (pc_malloc_ra0 (as_code B)) (pc_free_ra0 (as_code B))
RT_malloc1_ra RT_malloc2_ra RT_malloc3_ra RT_free1_ra RT_free2_ra RT_free3_ra (as_universe B).

(* The walk's statement: scene's entry contract (lib/AU/P_LLVMFuzzerTestOneInput_ctx.v, cgif's A/ACfn.v:59-69 with
   RC1-RC3)
   at scene's constants, the trivial meter (YCbp.v:16-17) with zero meter budgets (cgif A/ACfi.v:56 XL0), and
   PI_scene's read-only window. *)
Definition scene_llvmf_stmt : Prop :=
@scene_tfib_lib_contract_x fx rc scene_sink_head SceneAsanBase.scene_shape
SEGS SCENE_SINK_OWNED
A_LLVMF RA_LLVMF EV_LIB LIVE_LIB LLVMF_STK A_EMPTY B ameter_triv (fun _ : Z => 0) (fun _ : Z => 0) RLO RHI.
End h.
End d.
