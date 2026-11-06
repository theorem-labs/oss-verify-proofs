From OSSVerify.Proofs.libreac.fuzz_pcap.lib Require Import SymAddr.
(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs, 2026-10: pcap_KS, the CONCRETE asource_syms for libreac/fuzz_pcap's v1.9.0 ASan
   image -- row 6 of the port's obligation set
   (OBLIGATIONS.md (sha256 781e8f81f164; internal record), a Theorem Labs lane 22:00Z), and the
   instance a Theorem Labs lane listed as NOT CHECKED because none existed (21:50Z).

   IMAGE ROOT: the ORIGINAL v1.9.0 set, which is what the statements target --
   the pinned fuzz_pcap images and their unstripped twins,
   statements ed6b6b7b0ab. NOT the toolchain-N images.

   EVERY FIELD IS MEASURED, each with the line it came from. Symbols are from the image's own
   nm dump fuzz_pcap.nm.txt (sha256 21120db6ab2e; internal record); the words are read out of the ELF's
   PT_LOADs; the three derived ones are derived from instructions, cited below.

     as_read   mread      0x8ea40   nm 't'      | as_write  mwrite  0x8eb14  nm 't'
     as_seek   mseek      0x8ec28   nm 't'      | as_close  mclose  0x8ecc4  nm 't'
     as_mode   "rb\0"     0x20d40   .rodata, bytes 72 62 00 (PSource.v's src_mode_Z)
     as_threaded          0x5f4b21  = __libc+1   (DERIVED, see below)
     as_need_locks        0x5f4b23  = __libc+3   (DERIVED, see below)
     as_ofl_lock          0x5f4f80  nm 'b' ofl_lock, size 4
                 (so as_ofl_head = +8 = 0x5f4f88 = nm 'b' ofl_head, size 8 -- the two symbols
                  are adjacent in .bss exactly as PSource.v's as_ofl_head assumes, and 0x5f4f88
                  is the value a Theorem Labs lane's ASan sink_head Definition must carry, row 7)
     as_meta_ptr          0xa1100   nm 'b' _ZL24interceptor_metadata_map, size 8
     as_meta_mem          0xa1108   nm 'b' _ZZL28InitializeCommonInterceptorsvE12metadata_mem
                 (a Theorem Labs lane measured the same two independently, 21:50Z)
     as_can_got           0x9a4b8   .got; the word there READS 0x5f48d0 (verified from the ELF)
     as_canary            0x5f48d0  nm 'B' __stack_chk_guard, size 8
     as_icells            the REAL() cells the two interceptors on this stream read

   THE TWO DERIVED FIELDS, because they are NOT separate symbols in this build. musl's `__libc`
   struct holds can_do_threads / threaded / secure / need_locks as four bytes. The image proves
   the layout:
     - `__lock` (0x9342c) tests `lb a3,1783(a1)` with a1 = auipc 0x561 -> the objdump itself
       resolves the address as `5f4b23 <__libc+0x3>`, and clears it at 0x9345c (`sb zero,1783`).
       So need_locks = __libc+3 = 0x5f4b23.
     - threaded is __libc+1 = 0x5f4b21, by the same struct layout. CONFIRMED against the donor,
       whose own two fields sit at the same offsets of its __libc: cgif A_threaded 0x5f9221 and
       A_need_locks 0x5f9223 (lib/A/AE2k.v) -- a +1/+3 pair exactly like this one.
     - `__lockfile` (0x8e2e0) reads the FILE's own lock word (+140) against the thread pointer
       and never reads a `__threaded` global, which is why no such symbol exists to measure.

   ALL OF THESE CELLS ARE .bss (zero-initialised): verified by reading the ELF, which maps them
   with no file bytes. That is what asrc_stdio_env's `= 0` conjuncts assert at entry; they are
   runtime-mutable, so they are state facts, not image facts, and a walk must carry them.

   NOT PROVED HERE. This file gives the instance and its measured values. The obligation
   `asource_img_laws SK segs B pcap_KS` (PSourceMeta.v; SK explicit, the ASan image's sink_head)
   is discharged against a Theorem Labs lane's B (row 4)
   once that lands, and `asil_icells` in particular requires every pair below to be in
   `as_const B ly` -- so THE LIST BELOW IS COUPLED TO a Theorem Labs lane's TfibB and must be agreed with it,
   not guessed. rule 24: no function is proved in this file. *)
From Stdlib Require Import ZArith List.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A.Stdio Require Import PSource.
Import ListNotations.
Open Scope Z_scope.

(* musl's memory-stream callbacks, stored into the FILE by fmemopen (0x8e9fc..0x8ea0c). *)
Definition PCAP_MREAD  : Z := (symaddr Symbols.Asan.s_mread).
Definition PCAP_MWRITE : Z := (symaddr Symbols.Asan.s_mwrite).
Definition PCAP_MSEEK  : Z := (symaddr Symbols.Asan.s_mseek).
Definition PCAP_MCLOSE : Z := (symaddr Symbols.Asan.s_mclose).

(* The stdio environment. *)
Definition PCAP_MODE       : Z := (symaddr (Symbols.Asan.Sec.s_rodata + 68192)%Z).    (* "rb\0" *)
(* musl's "rwa\0" mode-set literal, now a FIELD (as_rwa) rather than a constant named inside
   asrc_stdio_env. MEASURED: file offset 0x10026 = vaddr 0x20026, bytes 72 77 61 00, a unique
   occurrence -- and the SAME address in the asan-ubsan twin (each image searched through its own
   program headers), so KS_U carries 0x20026 too. *)
Definition PCAP_RWA        : Z := (symaddr (Symbols.Asan.Sec.s_rodata + 0xfd46)%Z).
Definition PCAP_THREADED   : Z := (symaddr (Symbols.Asan.s___libc + 0x1)%Z).   (* __libc+1 *)
Definition PCAP_NEED_LOCKS : Z := (symaddr (Symbols.Asan.s___libc + 0x3)%Z).   (* __libc+3, read by __lock at 0x93430 *)
Definition PCAP_OFL_LOCK   : Z := (symaddr Symbols.Asan.s_ofl_lock).   (* ofl_lock; ofl_head = +8 = 0x5f4f88 *)

(* The ASan interceptor metadata map, and the stack guard with its GOT slot. *)
Definition PCAP_META_PTR : Z := (symaddr Symbols.Asan.s__ZL24interceptor_metadata_map).
Definition PCAP_META_MEM : Z := (symaddr Symbols.Asan.s__ZZL28InitializeCommonInterceptorsvE12metadata_mem).
Definition PCAP_CAN_GOT  : Z := (symaddr (Symbols.Asan.Sec.s_got + 0xce8)%Z).
Definition PCAP_CANARY   : Z := (symaddr Symbols.Asan.s___stack_chk_guard).

(* The REAL() cells the interceptors on this stream read, each (GOT slot, value), with the word
   at the slot READ OUT OF THE ELF rather than assumed:
     0x9b5f8 -> 0x8e214 musl fclose      0x9b5f0 -> 0x8e43c musl fflush
   mread / mwrite / mseek / mclose are NOT here: they are reached through the FILE's vtable,
   which fmemopen writes, not through the GOT, so asource_at pins them instead (PSource.v's
   as_read/as_write/as_seek/as_close fields at FILE +64/+72/+80/+24). *)
Definition PCAP_GOT_FCLOSE  : Z := (symaddr Symbols.Asan.s__ZN14__interception11real_fcloseE).
Definition PCAP_REAL_FCLOSE : Z := (symaddr Symbols.Asan.s_fclose).
Definition PCAP_GOT_FFLUSH  : Z := (symaddr Symbols.Asan.s__ZN14__interception11real_fflushE).
Definition PCAP_REAL_FFLUSH : Z := (symaddr Symbols.Asan.s_fflush_unlocked).

Definition pcap_icells : list (Z * Z) :=
  [(PCAP_GOT_FCLOSE, PCAP_REAL_FCLOSE); (PCAP_GOT_FFLUSH, PCAP_REAL_FFLUSH)].

Definition pcap_KS : asource_syms :=
  mkASource PCAP_MREAD PCAP_MWRITE PCAP_MSEEK PCAP_MCLOSE PCAP_MODE PCAP_RWA
            PCAP_THREADED PCAP_NEED_LOCKS PCAP_OFL_LOCK
            PCAP_META_PTR PCAP_META_MEM PCAP_CAN_GOT PCAP_CANARY
            pcap_icells.

(* The head is the lock plus eight, and it is pcap's measured ofl_head: the computation check,
   in the style of Reusable/PcapImgEnd.v's, so a wrong field cannot pass silently. *)
Lemma pcap_KS_head : as_ofl_head pcap_KS = (symaddr Symbols.Asan.s_ofl_head).
Proof. reflexivity. Qed.
