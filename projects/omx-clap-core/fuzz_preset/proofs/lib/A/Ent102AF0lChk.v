(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* omx-clap-core/fuzz_preset, image A' (asan, harness fix #102 pin sha256
   1be0f53d96cb9d6c2d5c92820c254e9db28e4830054a02631390e27c9547dc44, unstripped twin bff8519bbe3ea0e4): A CHECK of
   every code address of the runtime record lib/A/AF0l.v (blob dfca6bb1a8d7, Tfib_code, the as_code of the #102 A'
   TfibB) against the #102 A' listing (lib/A/Listing_prog.v blob 7ed1529926bd) and its PAImg instance PI_prog_A
   (lib/A/PAImg_prog.v blob 505a51ff7d08), with a planted-defect control that shows the check can fail.
   rule 24: proves no function (kind: check of generated runtime code addresses against the listing).

   No value below is copied from AF0l: each field is compared with pa_sigma AS_<sym> of PI_prog_A, or with a
   property of the pinned image's own instruction words (fetch_word on rsegs) located by pa_sigma.

   THE FIELDS (Tfib_code has 25; pc_stack_malloc is read at preset's classes 0, 1, 3), by the strength of the check:
   (A) EQUAL to a listing symbol (10): pc_malloc = AS___interceptor_malloc, pc_wrap_malloc = AS___wrap_malloc,
       pc_free = AS___interceptor_free, pc_wrap_free = AS___wrap_free, pc_stack_malloc 0 / 1 / 3 =
       AS___asan_stack_malloc_0 / _1 / _3, pc_asan_memcpy = AS___asan_memcpy, pc_asan_memset = AS___asan_memset,
       pc_wrap_bcmp = AS___wrap_bcmp.
   (B) RETURN SITES (2), no listing symbol is a return site inside the runtime: pc_malloc_ra0 lies strictly inside
       __interceptor_malloc (between AS___interceptor_malloc and the next listing symbol above it,
       AS___interceptor_realloc) and the image word 4 bytes before it is a `jal ra`; pc_free_ra0 the same inside
       __interceptor_free (up to AS___interceptor_malloc).
   (C) TRAMPOLINES the listing does not name (10): pc_wrap_memcmp, pc_wrap_memchr, pc_wrap_read, pc_wrap_fwrite,
       pc_wrap_vprintf, pc_wrap_vfprintf, pc_wrap_fprintf, pc_wrap_strnlen are word-aligned `jal zero` words inside the
       trampoline block [AS___wrap_strlen, AS___wrap_snprintf], pairwise distinct and distinct from the four listed
       trampolines of that block; pc_wrap_memset / pc_wrap_memcpy are `jal zero` words directly below
       AS___asan_memcpy (pc_wrap_memset + 4 = pc_wrap_memcpy, pc_wrap_memcpy + 4 = AS___asan_memcpy).
   (D) pc_region_is_poisoned (1): a function entry (`addi sp, sp, -N` with N > 0) between
       AS___asan_unpoison_memory_region and AS___asan_set_shadow_f5.
   (E) SPIN PCS (4): pc_spin_mmapdie, pc_spin_batch, pc_spin_freearray, pc_spin_shadow are each the self-loop word
       `jal zero, 0` of the runtime text, below the listing's base.
   (B)-(E) do not identify the function by name (the listing has no symbol for it); they bound it by listing symbols
   and the image's words. The names were matched outside Rocq against the unstripped twin's .symtab (all 27 values
   are the named symbol or return site). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK11 YP0m YP09 YP02 YP0l YP0b YP0a YCbn.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YG00 YG0f YG0n YG0d YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0d YP0c YPsym YImgTop YC4aP.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import Img0 Listing_prog PAImg_prog.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require AF0l.
Import ListNotations.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.

(* the pinned image's instruction word at a, and the fields of a RISC-V jal / I-type word *)
Definition img_word (a : Z) : option Z :=
  match fetch_word rsegs (Z_to_bv 64 a) with Some w => Some (bv_unsigned w) | None => None end.
Definition w_opc (w : Z) : Z := Z.land w 0x7f.
Definition w_rd (w : Z) : Z := Z.land (Z.shiftr w 7) 31.
Definition w_f3 (w : Z) : Z := Z.land (Z.shiftr w 12) 7.
Definition w_rs1 (w : Z) : Z := Z.land (Z.shiftr w 15) 31.
Definition jal_imm (w : Z) : Z :=
  let u := Z.land (Z.shiftr w 31) 1 * 2 ^ 20 + Z.land (Z.shiftr w 12) 0xff * 2 ^ 12 +
           Z.land (Z.shiftr w 20) 1 * 2 ^ 11 + Z.land (Z.shiftr w 21) 0x3ff * 2 in
  if Z.land (Z.shiftr w 31) 1 =? 1 then u - 2 ^ 21 else u.
(* the word at a is `jal rd, _` *)
Definition jal_rd_at (a rd : Z) : bool :=
  match img_word a with Some w => (w_opc w =? 0x6f) && (w_rd w =? rd) | None => false end.
(* the word at a is `jal zero, 0` (a self-loop) *)
Definition spin_at (a : Z) : bool :=
  match img_word a with Some w => (w_opc w =? 0x6f) && (w_rd w =? 0) && (jal_imm w =? 0) | None => false end.
(* the word at a is `addi sp, sp, -N` with N > 0 (a frame-allocating function entry) *)
Definition prologue_at (a : Z) : bool :=
  match img_word a with
  | Some w => (w_opc w =? 0x13) && (w_rd w =? 2) && (w_f3 w =? 0) && (w_rs1 w =? 2) && (Z.shiftr w 20 >=? 0x800)
  | None => false end.
Fixpoint nodupZ (l : list Z) : bool :=
  match l with [] => true | x :: t => negb (existsb (Z.eqb x) t) && nodupZ t end.

Section chk.
Context {rc : YM05.RunCeil}.
Local Notation SG s := (@pa_sigma rc A_prog_listing PI_prog_A s).

(* a trampoline of the block [__wrap_strlen, __wrap_snprintf] *)
Definition tramp_in_block (a : Z) : bool :=
  (SG AS___wrap_strlen <=? a) && (a <=? SG AS___wrap_snprintf) && (a mod 4 =? 0) && jal_rd_at a 0.

(* THE CHECK, over any record of runtime code addresses *)
Definition af0l_pcs_match_of (c : acode) : bool :=
  (* (A) the listing's symbols *)
  (pc_malloc c =? SG AS___interceptor_malloc) && (pc_wrap_malloc c =? SG AS___wrap_malloc) &&
  (pc_free c =? SG AS___interceptor_free) && (pc_wrap_free c =? SG AS___wrap_free) &&
  (pc_stack_malloc c 0 =? SG AS___asan_stack_malloc_0) && (pc_stack_malloc c 1 =? SG AS___asan_stack_malloc_1) &&
  (pc_stack_malloc c 3 =? SG AS___asan_stack_malloc_3) &&
  (pc_asan_memcpy c =? SG AS___asan_memcpy) && (pc_asan_memset c =? SG AS___asan_memset) &&
  (pc_wrap_bcmp c =? SG AS___wrap_bcmp) &&
  (* (B) the two return sites *)
  (SG AS___interceptor_malloc <? pc_malloc_ra0 c) && (pc_malloc_ra0 c <? SG AS___interceptor_realloc) &&
  jal_rd_at (pc_malloc_ra0 c - 4) 1 &&
  (SG AS___interceptor_free <? pc_free_ra0 c) && (pc_free_ra0 c <? SG AS___interceptor_malloc) &&
  jal_rd_at (pc_free_ra0 c - 4) 1 &&
  (* (C) the trampolines the listing does not name *)
  forallb tramp_in_block [pc_wrap_memcmp c; pc_wrap_memchr c; pc_wrap_read c; pc_wrap_fwrite c; pc_wrap_vprintf c;
                          pc_wrap_vfprintf c; pc_wrap_fprintf c; pc_wrap_strnlen c] &&
  nodupZ [pc_wrap_memcmp c; pc_wrap_memchr c; pc_wrap_read c; pc_wrap_fwrite c; pc_wrap_vprintf c;
          pc_wrap_vfprintf c; pc_wrap_fprintf c; pc_wrap_strnlen c;
          SG AS___wrap_strlen; SG AS___wrap_strcmp; SG AS___wrap_bcmp; SG AS___wrap_snprintf] &&
  jal_rd_at (pc_wrap_memset c) 0 && jal_rd_at (pc_wrap_memcpy c) 0 &&
  (pc_wrap_memset c + 4 =? pc_wrap_memcpy c) && (pc_wrap_memcpy c + 4 =? SG AS___asan_memcpy) &&
  (* (D) __asan_region_is_poisoned *)
  (SG AS___asan_unpoison_memory_region <? pc_region_is_poisoned c) &&
  (pc_region_is_poisoned c <? SG AS___asan_set_shadow_f5) && prologue_at (pc_region_is_poisoned c) &&
  (* (E) the spin pcs *)
  forallb (fun a => spin_at a && (a <? SG AS_LLVMFuzzerTestOneInput))
    [pc_spin_mmapdie c; pc_spin_batch c; pc_spin_freearray c; pc_spin_shadow c].

(* (A) as equalities *)
Lemma af0l_pcs_listing :
  pc_malloc AF0l.Tfib_code = SG AS___interceptor_malloc /\ pc_wrap_malloc AF0l.Tfib_code = SG AS___wrap_malloc /\
  pc_free AF0l.Tfib_code = SG AS___interceptor_free /\ pc_wrap_free AF0l.Tfib_code = SG AS___wrap_free /\
  pc_stack_malloc AF0l.Tfib_code 0 = SG AS___asan_stack_malloc_0 /\
  pc_stack_malloc AF0l.Tfib_code 1 = SG AS___asan_stack_malloc_1 /\
  pc_stack_malloc AF0l.Tfib_code 3 = SG AS___asan_stack_malloc_3 /\
  pc_asan_memcpy AF0l.Tfib_code = SG AS___asan_memcpy /\ pc_asan_memset AF0l.Tfib_code = SG AS___asan_memset /\
  pc_wrap_bcmp AF0l.Tfib_code = SG AS___wrap_bcmp.
Proof. repeat split; vm_compute; reflexivity. Qed.

(* PASS: the whole check holds of the record *)
Lemma af0l_pcs_match : af0l_pcs_match_of AF0l.Tfib_code = true.
Proof. vm_compute. reflexivity. Qed.

(* PLANTED DEFECT 1 (an (A) field): the record with pc_wrap_free shifted by 0x94, the shift a Theorem Labs lane found in the
   old pins' AF0l eb3d91d8c440 *)
Definition af0l_planted_wrap_free : acode := {|
  pc_malloc := pc_malloc AF0l.Tfib_code; pc_wrap_malloc := pc_wrap_malloc AF0l.Tfib_code;
  pc_malloc_ra0 := pc_malloc_ra0 AF0l.Tfib_code; pc_free := pc_free AF0l.Tfib_code;
  pc_wrap_free := pc_wrap_free AF0l.Tfib_code + 0x94; pc_free_ra0 := pc_free_ra0 AF0l.Tfib_code;
  pc_stack_malloc := pc_stack_malloc AF0l.Tfib_code;
  pc_asan_memcpy := pc_asan_memcpy AF0l.Tfib_code; pc_asan_memset := pc_asan_memset AF0l.Tfib_code;
  pc_wrap_memcpy := pc_wrap_memcpy AF0l.Tfib_code; pc_wrap_memset := pc_wrap_memset AF0l.Tfib_code;
  pc_wrap_memcmp := pc_wrap_memcmp AF0l.Tfib_code; pc_wrap_bcmp := pc_wrap_bcmp AF0l.Tfib_code;
  pc_wrap_read := pc_wrap_read AF0l.Tfib_code; pc_wrap_fwrite := pc_wrap_fwrite AF0l.Tfib_code;
  pc_wrap_vprintf := pc_wrap_vprintf AF0l.Tfib_code; pc_wrap_vfprintf := pc_wrap_vfprintf AF0l.Tfib_code;
  pc_wrap_fprintf := pc_wrap_fprintf AF0l.Tfib_code; pc_wrap_memchr := pc_wrap_memchr AF0l.Tfib_code;
  pc_wrap_strnlen := pc_wrap_strnlen AF0l.Tfib_code; pc_region_is_poisoned := pc_region_is_poisoned AF0l.Tfib_code;
  pc_spin_mmapdie := pc_spin_mmapdie AF0l.Tfib_code; pc_spin_batch := pc_spin_batch AF0l.Tfib_code;
  pc_spin_freearray := pc_spin_freearray AF0l.Tfib_code; pc_spin_shadow := pc_spin_shadow AF0l.Tfib_code |}.
Lemma af0l_planted_wrap_free_fails : ~ (af0l_pcs_match_of af0l_planted_wrap_free = true).
Proof. intros H. vm_compute in H. discriminate H. Qed.

(* PLANTED DEFECT 2 (a (C) field, checked only by the image's words): pc_wrap_memchr shifted by 0x94 *)
Definition af0l_planted_wrap_memchr : acode := {|
  pc_malloc := pc_malloc AF0l.Tfib_code; pc_wrap_malloc := pc_wrap_malloc AF0l.Tfib_code;
  pc_malloc_ra0 := pc_malloc_ra0 AF0l.Tfib_code; pc_free := pc_free AF0l.Tfib_code;
  pc_wrap_free := pc_wrap_free AF0l.Tfib_code; pc_free_ra0 := pc_free_ra0 AF0l.Tfib_code;
  pc_stack_malloc := pc_stack_malloc AF0l.Tfib_code;
  pc_asan_memcpy := pc_asan_memcpy AF0l.Tfib_code; pc_asan_memset := pc_asan_memset AF0l.Tfib_code;
  pc_wrap_memcpy := pc_wrap_memcpy AF0l.Tfib_code; pc_wrap_memset := pc_wrap_memset AF0l.Tfib_code;
  pc_wrap_memcmp := pc_wrap_memcmp AF0l.Tfib_code; pc_wrap_bcmp := pc_wrap_bcmp AF0l.Tfib_code;
  pc_wrap_read := pc_wrap_read AF0l.Tfib_code; pc_wrap_fwrite := pc_wrap_fwrite AF0l.Tfib_code;
  pc_wrap_vprintf := pc_wrap_vprintf AF0l.Tfib_code; pc_wrap_vfprintf := pc_wrap_vfprintf AF0l.Tfib_code;
  pc_wrap_fprintf := pc_wrap_fprintf AF0l.Tfib_code; pc_wrap_memchr := pc_wrap_memchr AF0l.Tfib_code + 0x94;
  pc_wrap_strnlen := pc_wrap_strnlen AF0l.Tfib_code; pc_region_is_poisoned := pc_region_is_poisoned AF0l.Tfib_code;
  pc_spin_mmapdie := pc_spin_mmapdie AF0l.Tfib_code; pc_spin_batch := pc_spin_batch AF0l.Tfib_code;
  pc_spin_freearray := pc_spin_freearray AF0l.Tfib_code; pc_spin_shadow := pc_spin_shadow AF0l.Tfib_code |}.
Lemma af0l_planted_wrap_memchr_fails : ~ (af0l_pcs_match_of af0l_planted_wrap_memchr = true).
Proof. intros H. vm_compute in H. discriminate H. Qed.
End chk.

(* the values the check compared, for the report *)
Eval vm_compute in (map (fun z => z) [pc_malloc AF0l.Tfib_code; pc_wrap_malloc AF0l.Tfib_code;
  pc_malloc_ra0 AF0l.Tfib_code; pc_free AF0l.Tfib_code; pc_wrap_free AF0l.Tfib_code; pc_free_ra0 AF0l.Tfib_code;
  pc_stack_malloc AF0l.Tfib_code 0; pc_stack_malloc AF0l.Tfib_code 1; pc_stack_malloc AF0l.Tfib_code 3;
  pc_asan_memcpy AF0l.Tfib_code; pc_asan_memset AF0l.Tfib_code; pc_wrap_memcpy AF0l.Tfib_code;
  pc_wrap_memset AF0l.Tfib_code; pc_wrap_memcmp AF0l.Tfib_code; pc_wrap_bcmp AF0l.Tfib_code;
  pc_wrap_read AF0l.Tfib_code; pc_wrap_fwrite AF0l.Tfib_code; pc_wrap_vprintf AF0l.Tfib_code;
  pc_wrap_vfprintf AF0l.Tfib_code; pc_wrap_fprintf AF0l.Tfib_code; pc_wrap_memchr AF0l.Tfib_code;
  pc_wrap_strnlen AF0l.Tfib_code; pc_region_is_poisoned AF0l.Tfib_code; pc_spin_mmapdie AF0l.Tfib_code;
  pc_spin_batch AF0l.Tfib_code; pc_spin_freearray AF0l.Tfib_code; pc_spin_shadow AF0l.Tfib_code]).

Print Assumptions af0l_pcs_listing.
Print Assumptions af0l_pcs_match.
Print Assumptions af0l_planted_wrap_free_fails.
Print Assumptions af0l_planted_wrap_memchr_fails.
