(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* gated: a Theorem Labs lane PASS A+B at c061542723f / 731386609e0.  Nothing is filled.  Gates on this text (a Theorem Labs lane's pcmd tools, both images, all exit 0; gates3.md (sha256 73e84770b991; internal record)): cellcheck --target-only 308 facts, 153 OK, 155 STATE, 0 WRONG; shadowcheck 45/45 const-shadow cells, 6 zero ranges, 0 poisoned, 0 unparsed; ownedcheck 38 owned ranges, 308 const cells, UNOWNED 0, OVERCLAIM 0, UNPARSED 0. *)
From OSSVerify.Proofs.libreac.fuzz_pcap.lib Require Import SymAddr.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YG00 YG01 YG0f.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require YF0p.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A Require Import AF0l.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YImgTop.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Definition TFIB_INST : Z := (symaddr Symbols.Asan.s__ZN6__asanL8instanceE).      Definition TFIB_TP : Z := (symaddr (Symbols.Asan.s_builtin_tls + 0xc8)%Z).       Definition TFIB_TSD : Z := (symaddr Symbols.Asan.s___pthread_tsd_main).
Definition TFIB_DEPOT : Z := (symaddr Symbols.Asan.s__ZN11__sanitizerL8theDepotE).     Definition TFIB_STORE : Z := (symaddr Symbols.Asan.s__ZN11__sanitizerL10stackStoreE).
Definition TFIB_IAL_LO : Z := (symaddr Symbols.Asan.s__ZN11__sanitizerL26internal_alloc_placeholderE).    Definition TFIB_IAL_HI : Z := (symaddr (Symbols.Asan.s__ZN11__sanitizerL26internal_alloc_placeholderE + 528432)%Z).   Definition TFIB_IAL_W : Z := (symaddr (Symbols.Asan.s__ZN11__sanitizerL26internal_alloc_placeholderE + 265664)%Z).
Definition TFIB_IAL_FLAG : Z := (symaddr Symbols.Asan.s__ZN11__sanitizerL30internal_allocator_initializedE).  Definition TFIB_OOM : Z := (symaddr Symbols.Asan.s__ZN11__sanitizerL23allocator_out_of_memoryE).
Definition TFIB_MAIN : Z := (symaddr Symbols.Asan.s_main).      Definition TFIB_MAIN_RA : Z := (symaddr (Symbols.Asan.s_libc_start_main_stage2 + 0x44)%Z).  Definition TFIB_GP : Z := (symaddr (Symbols.Asan.Sec.s_rodata + 0x520)%Z).
Definition TFIB_ERRNO : Z := (symaddr (Symbols.Asan.s_builtin_tls + 0x24)%Z).
Definition DRV_TRACES : list (list Z) :=
[[(symaddr (Symbols.Asan.s___interceptor_malloc + 0xc8)%Z); (symaddr (Symbols.Asan.s_main + 0x54)%Z)]; [(symaddr (Symbols.Asan.s___interceptor_malloc + 0xc8)%Z); (symaddr (Symbols.Asan.s_main + 0xa8)%Z)]; [(symaddr (Symbols.Asan.s___interceptor_malloc + 0xc8)%Z); (symaddr (Symbols.Asan.s_target_run + 0x64)%Z)]; [(symaddr (Symbols.Asan.s___interceptor_malloc + 0xc8)%Z)];
[(symaddr (Symbols.Asan.s___interceptor_free + 0x138)%Z); (symaddr (Symbols.Asan.s_main + 0xcc)%Z)]; [(symaddr (Symbols.Asan.s___interceptor_free + 0x138)%Z); (symaddr (Symbols.Asan.s_main + 0x1fc)%Z)]; [(symaddr (Symbols.Asan.s___interceptor_free + 0x138)%Z); (symaddr (Symbols.Asan.s_target_run + 0xf8)%Z)]; [(symaddr (Symbols.Asan.s___interceptor_free + 0x138)%Z)]].
Definition Tfib_const_sym : list acell :=
[ c8 (AT 0) (AC 0); c8 (AT 8) (ATop 0); c8 (AT 16) (ATop (- kStackSpan)); z8 (AT 24) 0; z8 (AT 32) 0; z1 (AT 40) 0;
z8 (AT 48) (symaddr (Symbols.Asan.s_builtin_tls + 0x800)%Z); z8 (AT 56) (symaddr (Symbols.Asan.s_builtin_tls + 0x8dc)%Z); z8 (AT 64) (symaddr (Symbols.Asan.s_builtin_tls + 0xd0)%Z); c8 (AT 72) (AF 0)    ;
z4 (AC 8) 0; c8 (AC 152) (AT 0);
c8 (ATsd 0) (AC 0); c8 (ATp 0) (AF 0); c8 (ATp (-88)) (ATsd 0); z8 (ATp (-8)) (symaddr (Symbols.Asan.s_builtin_tls + 0xe8)%Z)  ;
c8 (ATp 8) (AD 0); c8 (AD 24) (ATp 0)  ;
c8 (AInst o_space) (ASp 0); c8 (AInst o_rinfo) (ASp kRegionInfoOff); c8 (AInst o_sec_chunks) (AQ 0); c8 (AInst 80) (AQ 0) ].
Definition Tfib_const_abs : list acell :=
[z8 (ANum (symaddr Symbols.Asan.s__ZN11__sanitizer21common_flags_dont_useE)) 0x1  (* E-PEND run2/RT *) ;
z8 (ANum (symaddr (Symbols.Asan.s__ZN11__sanitizer21common_flags_dont_useE + 0x8)%Z)) 0x0  (* E-PEND run2/RT *) ;
z8 (ANum (symaddr (Symbols.Asan.s__ZN11__sanitizer21common_flags_dont_useE + 0x10)%Z)) 0x0  (* E-PEND run2/RT *) ;
z8 (ANum (symaddr (Symbols.Asan.s__ZN11__sanitizer21common_flags_dont_useE + 0x18)%Z)) (symaddr (Symbols.Asan.Sec.s_rodata + 0x3b9d)%Z)  (* E-PEND run2/RT *) ;
z8 (ANum (symaddr (Symbols.Asan.s__ZN11__sanitizer21common_flags_dont_useE + 0x20)%Z)) 0x1e00010000  (* E-PEND run2/RT *) ;
z8 (ANum (symaddr (Symbols.Asan.s__ZN11__sanitizer21common_flags_dont_useE + 0x28)%Z)) 0x0  (* E-PEND run2/RT *) ;
z8 (ANum (symaddr (Symbols.Asan.s__ZN11__sanitizer21common_flags_dont_useE + 0x30)%Z)) 0x0  (* E-PEND run2/RT *) ;
z8 (ANum (symaddr (Symbols.Asan.s__ZN11__sanitizer21common_flags_dont_useE + 0x38)%Z)) 0x0  (* E-PEND run2/RT *) ;
z8 (ANum (symaddr (Symbols.Asan.s__ZN11__sanitizer21common_flags_dont_useE + 0x40)%Z)) 0x0  (* E-PEND run2/RT *) ;
z8 (ANum (symaddr (Symbols.Asan.s__ZN11__sanitizer21common_flags_dont_useE + 0x48)%Z)) 0x10101000101  (* E-PEND run2/RT *) ;
z8 (ANum (symaddr (Symbols.Asan.s__ZN11__sanitizer21common_flags_dont_useE + 0x50)%Z)) 0x100000000  (* E-PEND run2/RT *) ;
z8 (ANum (symaddr (Symbols.Asan.s__ZN11__sanitizer21common_flags_dont_useE + 0x58)%Z)) 0x0  (* E-PEND run2/RT *) ;
z8 (ANum (symaddr (Symbols.Asan.s__ZN11__sanitizer21common_flags_dont_useE + 0x60)%Z)) 0x0  (* E-PEND run2/RT *) ;
z8 (ANum (symaddr (Symbols.Asan.s__ZN11__sanitizer21common_flags_dont_useE + 0x68)%Z)) 0x0  (* E-PEND run2/RT *) ;
z8 (ANum (symaddr (Symbols.Asan.s__ZN11__sanitizer21common_flags_dont_useE + 0x70)%Z)) 0x10001  (* E-PEND run2/RT *) ;
z8 (ANum (symaddr (Symbols.Asan.s__ZN11__sanitizer21common_flags_dont_useE + 0x78)%Z)) 0xffffffffffffffff  (* E-PEND run2/RT *) ;
z8 (ANum (symaddr (Symbols.Asan.s__ZN11__sanitizer21common_flags_dont_useE + 0x80)%Z)) (symaddr (Symbols.Asan.Sec.s_rodata + 0x1527)%Z)  (* E-PEND run2/RT *) ;
z8 (ANum (symaddr (Symbols.Asan.s__ZN11__sanitizer21common_flags_dont_useE + 0x88)%Z)) 0x100  (* E-PEND run2/RT *) ;
z8 (ANum (symaddr (Symbols.Asan.s__ZN11__sanitizer21common_flags_dont_useE + 0x90)%Z)) 0x0  (* E-PEND run2/RT *) ;
z8 (ANum (symaddr (Symbols.Asan.s__ZN11__sanitizer21common_flags_dont_useE + 0x98)%Z)) 0x0  (* E-PEND run2/RT *) ;
z8 (ANum (symaddr (Symbols.Asan.s__ZN11__sanitizer21common_flags_dont_useE + 0xa0)%Z)) 0x0  (* E-PEND run2/RT *) ;
z8 (ANum (symaddr (Symbols.Asan.s__ZN11__sanitizer21common_flags_dont_useE + 0xa8)%Z)) 0x0  (* E-PEND run2/RT *) ;
z8 (ANum (symaddr (Symbols.Asan.s__ZN11__sanitizer21common_flags_dont_useE + 0xb0)%Z)) 0xffffffff00000000  (* E-PEND run2/RT *) ;
z8 (ANum (symaddr (Symbols.Asan.s__ZN11__sanitizer21common_flags_dont_useE + 0xb8)%Z)) 0x1  (* E-PEND run2/RT *) ;
z8 (ANum (symaddr (Symbols.Asan.s__ZN11__sanitizer21common_flags_dont_useE + 0xc0)%Z)) (symaddr (Symbols.Asan.Sec.s_rodata + 0x3f15)%Z)  (* E-PEND run2/RT *) ;
z8 (ANum (symaddr (Symbols.Asan.s__ZN11__sanitizer21common_flags_dont_useE + 0xc8)%Z)) (symaddr (Symbols.Asan.Sec.s_rodata + 0x3b9d)%Z)  (* E-PEND run2/RT *) ;
z8 (ANum (symaddr (Symbols.Asan.s__ZN11__sanitizer21common_flags_dont_useE + 0xd0)%Z)) (symaddr (Symbols.Asan.Sec.s_rodata + 0x3b9d)%Z)  (* E-PEND run2/RT *) ;
z8 (ANum (symaddr (Symbols.Asan.s__ZN11__sanitizer21common_flags_dont_useE + 0xd8)%Z)) 0x10101000100  (* E-PEND run2/RT *) ;
z8 (ANum (symaddr (Symbols.Asan.s__ZN11__sanitizer21common_flags_dont_useE + 0xe0)%Z)) 0x0  (* E-PEND run2/RT *) ;
z8 (ANum (symaddr (Symbols.Asan.s__ZN11__sanitizer21common_flags_dont_useE + 0xe8)%Z)) (symaddr (Symbols.Asan.Sec.s_rodata + 0xd6a9)%Z)  (* E-PEND run2/RT *) ;
z8 (ANum (symaddr (Symbols.Asan.s__ZN11__sanitizer21common_flags_dont_useE + 0xf0)%Z)) 0x101000100000000  (* E-PEND run2/RT *) ;
z8 (ANum (symaddr (Symbols.Asan.s__ZN11__sanitizer21common_flags_dont_useE + 0xf8)%Z)) 0x101010101010101  (* E-PEND run2/RT *) ;
z8 (ANum (symaddr (Symbols.Asan.s__ZN11__sanitizer21common_flags_dont_useE + 0x100)%Z)) 0x1010101  (* E-PEND run2/RT *) ;
z8 (ANum (symaddr (Symbols.Asan.s__ZN11__sanitizer21common_flags_dont_useE + 0x108)%Z)) 0x10100000001  (* E-PEND run2/RT *) ;
z8 (ANum (symaddr Symbols.Asan.s__ZN6__asan28asan_flags_dont_use_directlyE)) 0x100ffffffff  (* E-PEND pcrel/RT *) ;
z8 (ANum (symaddr (Symbols.Asan.s__ZN6__asan28asan_flags_dont_use_directlyE + 0x8)%Z)) 0x1000000400  (* E-PEND run2/RT *) ;
z8 (ANum (symaddr (Symbols.Asan.s__ZN6__asan28asan_flags_dont_use_directlyE + 0x10)%Z)) 0x800  (* E-PEND run2/RT *) ;
z8 (ANum (symaddr (Symbols.Asan.s__ZN6__asan28asan_flags_dont_use_directlyE + 0x18)%Z)) 0x101010000000001  (* E-PEND run2/RT *) ;
z8 (ANum (symaddr (Symbols.Asan.s__ZN6__asan28asan_flags_dont_use_directlyE + 0x20)%Z)) 0x1400000010  (* E-PEND run2/RT *) ;
z8 (ANum (symaddr (Symbols.Asan.s__ZN6__asan28asan_flags_dont_use_directlyE + 0x28)%Z)) 0x100000000000  (* E-PEND run2/RT *) ;
z8 (ANum (symaddr (Symbols.Asan.s__ZN6__asan28asan_flags_dont_use_directlyE + 0x30)%Z)) 0xbe00000000  (* E-PEND run2/RT *) ;
z8 (ANum (symaddr (Symbols.Asan.s__ZN6__asan28asan_flags_dont_use_directlyE + 0x38)%Z)) 0x100000055  (* E-PEND run2/RT *) ;
z8 (ANum (symaddr (Symbols.Asan.s__ZN6__asan28asan_flags_dont_use_directlyE + 0x40)%Z)) 0x0  (* E-PEND run2/RT *) ;
z8 (ANum (symaddr (Symbols.Asan.s__ZN6__asan28asan_flags_dont_use_directlyE + 0x48)%Z)) 0x1000100000000  (* E-PEND run2/RT *) ;
z8 (ANum (symaddr (Symbols.Asan.s__ZN6__asan28asan_flags_dont_use_directlyE + 0x50)%Z)) 0x101010101000001  (* E-PEND run2/RT *) ;
z8 (ANum (symaddr (Symbols.Asan.s__ZN6__asan28asan_flags_dont_use_directlyE + 0x58)%Z)) 0x1  (* E-PEND run2/RT *) ;
z8 (ANum (symaddr (Symbols.Asan.s__ZN6__asan28asan_flags_dont_use_directlyE + 0x60)%Z)) 0x200000001  (* E-PEND run2/RT *) ;
z8 (ANum (symaddr (Symbols.Asan.s__ZN6__asan28asan_flags_dont_use_directlyE + 0x68)%Z)) (symaddr (Symbols.Asan.Sec.s_rodata + 0x3b9d)%Z)  (* E-PEND run2/RT *) ;
z8 (ANum (symaddr (Symbols.Asan.s__ZN6__asan28asan_flags_dont_use_directlyE + 0x70)%Z)) 0x10101  (* E-PEND run2/RT *) ;
z8 (ANum (symaddr Symbols.Asan.s___asan_shadow_memory_dynamic_address)) 0x7fff8000  (* E-PEND measured/RT *) ;
z4 (ANum (symaddr Symbols.Asan.s___asan_option_detect_stack_use_after_return)) 0x1  (* E-PEND measured/RT *) ;
z1 (ANum (symaddr Symbols.Asan.s__ZN6__asanL11asan_initedE)) 0x1  (* E-PEND pcrel/RT *) ;
z1 (ANum (symaddr Symbols.Asan.s__ZN6__asan21replace_intrin_cachedE)) 0x1  (* E-PEND run2/RT *) ;
z8 (ANum (symaddr Symbols.Asan.s__ZN6__asan11kHighMemEndE)) 0x7fffffffffff  (* E-PEND pcrel/RT *) ;
z8 (ANum (symaddr Symbols.Asan.s__ZN6__asan10kMidMemBegE)) 0x0  (* E-PEND run2/RT *) ;
z8 (ANum (symaddr Symbols.Asan.s__ZN6__asan10kMidMemEndE)) 0x0  (* E-PEND run2/RT *) ;
z4 (ANum (symaddr Symbols.Asan.s__ZN6__asanL19malloc_context_sizeE)) 0x1e  (* E-PEND pcrel/RT *) ;
z1 (ANum (symaddr Symbols.Asan.s__ZN6__asanL17can_poison_memoryE)) 0x1  (* E-PEND pcrel/RT *) ;
z1 (ANum (symaddr Symbols.Asan.s__ZN6__asanL14tsd_key_initedE)) 0x1  (* E-PEND pcrel/RT *) ;
z4 (ANum (symaddr Symbols.Asan.s__ZN6__asanL7tsd_keyE)) 0x0  (* E-PEND pcrel/RT *) ;
z1 (ANum (symaddr Symbols.Asan.s__ZN11__sanitizerL25allocator_may_return_nullE)) 0x1  (* E-PEND pcrel/RT *) ;
z1 (ANum (symaddr Symbols.Asan.s__ZN11__sanitizerL18rss_limit_exceededE)) 0x0  (* E-PEND pcrel/RT *) ;
z8 (ANum (symaddr Symbols.Asan.s__ZN11__sanitizer14PageSizeCachedE)) 0x1000  (* E-PEND run2/RT *) ;
z4 (ANum (symaddr Symbols.Asan.s__ZN11__sanitizer25sealed_report_in_progressE)) 0x0  (* E-PEND pcrel/RT *) ;
z8 (ANum (symaddr Symbols.Asan.s__ZN14__interception10real_atollE)) (symaddr Symbols.Asan.s_atoll)  (* M-IMG run; real_atoll (cgif 0x9fe18); fixed 22:55Z, auditor #19: was 0x9b698 = real_atoi *) ;
z8 (ANum (symaddr Symbols.Asan.s__ZN14__interception11real_memcpyE)) (symaddr Symbols.Asan.s_memcpy)  (* M-IMG pcrel *) ;
z8 (ANum (symaddr Symbols.Asan.s__ZN14__interception11real_memsetE)) (symaddr Symbols.Asan.s_memset)  (* M-IMG pcrel *) ;
z8 (ANum (symaddr Symbols.Asan.s__ZN14__interception11real_memcmpE)) (symaddr Symbols.Asan.s_memcmp)  (* M-IMG pcrel *) ;
z8 (ANum (symaddr Symbols.Asan.s__ZN14__interception9real_bcmpE)) (symaddr Symbols.Asan.s_bcmp)  (* M-IMG pcrel *) ;
z1 (ANum (symaddr (Symbols.Asan.s__ZN11__sanitizer21common_flags_dont_useE + 0x89)%Z)) 0x1  (* E-PEND run2/RT *) ;
z4 (ANum (symaddr Symbols.Asan.s__ZN11__sanitizer17current_verbosityE)) 0x0  (* E-PEND run2/RT *) ;
z8 (ANum (symaddr (Symbols.Asan.Sec.s_got + 0xd50)%Z)) 0x8  (* M-IMG pcrel *) ;
z8 (ANum (symaddr Symbols.Asan.s__ZN14__interception9real_readE)) (symaddr Symbols.Asan.s_read)  (* M-IMG pcrel *) ;
z8 (ANum (symaddr Symbols.Asan.s__ZN14__interception11real_fwriteE)) (symaddr Symbols.Asan.s_fwrite_unlocked)  (* M-IMG pcrel; real_fwrite (cgif 0x9fcf0); fixed 22:55Z, auditor #19: was 0x9b570 = real_fread, a pcap-only slot *) ;
z8 (ANum (symaddr Symbols.Asan.s__ZN14__interception12real_strnlenE)) (symaddr Symbols.Asan.s_strnlen)  (* M-IMG pcrel *) ;
z8 (ANum (symaddr Symbols.Asan.s__ZN14__interception11real_memchrE)) (symaddr Symbols.Asan.s_memchr)  (* M-IMG pcrel *) ;
z1 (ANum (symaddr (Symbols.Asan.s__ZN11__sanitizer21common_flags_dont_useE + 0xfb)%Z)) 0x1  (* E-PEND run2/RT *) ;
z1 (ANum (symaddr (Symbols.Asan.s__ZN11__sanitizer21common_flags_dont_useE + 0x54)%Z)) 0x1  (* E-PEND run2/RT *) ;
z8 (ANum (symaddr Symbols.Asan.s__ZN14__interception12real_vprintfE)) (symaddr Symbols.Asan.s_vprintf)  (* M-IMG pcrel *) ;
z8 (ANum (symaddr Symbols.Asan.s__ZN14__interception13real_vfprintfE)) (symaddr Symbols.Asan.s_vfprintf)  (* M-IMG pcrel *) ;
z8 (ANum (symaddr Symbols.Asan.s__ZN14__interception19real___tls_get_addrE)) (symaddr Symbols.Asan.s___tls_get_addr)  (* M-IMG pcrel *) ;
z8 (ANum (symaddr (Symbols.Asan.Sec.s_got + 0xbc8)%Z)) (symaddr Symbols.Asan.s__ZN6__asan21replace_intrin_cachedE)  (* M-IMG pcrel *) ;
z8 (ANum (symaddr (Symbols.Asan.Sec.s_got + 0xcd8)%Z)) (symaddr Symbols.Asan.Sec.s_asan_globals)  (* M-IMG pcrel *) ;
z8 (ANum (symaddr (Symbols.Asan.Sec.s_got + 0xce0)%Z)) (symaddr Symbols.Asan.s____asan_globals_registered)  (* M-IMG pcrel *) ;
z8 (ANum (symaddr Symbols.Asan.s____asan_globals_registered)) 0x1  (* E-PEND pcrel/RT *) ;
z8 (ANum (symaddr (Symbols.Asan.Sec.s_got + 0xd40)%Z)) 0x1  (* M-IMG pcrel *) ;
z8 (ANum (symaddr (Symbols.Asan.Sec.s_got + 0xd48)%Z)) 0xfffffffffffff800  (* M-IMG run *) ;
z8 (ANum (symaddr (Symbols.Asan.s__ZN11__sanitizerL10stackStoreE + 0x8)%Z)) 0x800000  (* E-PEND run2/RT *) ;
z8 (ANum (symaddr (Symbols.Asan.s__ZN6__asanL8instanceE + 0x8)%Z)) 0x2000011000  (* E-PEND run2/RT *) ;
z8 (ANum (symaddr (Symbols.Asan.s__ZN6__asanL8instanceE + 0x10)%Z)) (symaddr (Symbols.Asan.Sec.s_rodata + 0x6803)%Z)  (* E-PEND run2/RT *) ;
z8 (ANum (symaddr (Symbols.Asan.s__ZN6__asanL8instanceE + 0x18)%Z)) 0x0  (* E-PEND run2/RT *) ;
z8 (ANum (symaddr (Symbols.Asan.s__ZN6__asanL8instanceE + 0x28)%Z)) 0xffffffff  (* E-PEND run2/RT *) ;
z8 (ANum (symaddr (Symbols.Asan.s__ZN6__asanL8instanceE + 0x38)%Z)) 0x0  (* E-PEND run2/RT *) ;
z8 (ANum (symaddr (Symbols.Asan.s__ZN6__asanL8instanceE + 0x40)%Z)) 0x1000  (* E-PEND run2/RT *) ;
z8 (ANum (symaddr (Symbols.Asan.s__ZN6__asanL8instanceE + 0x58)%Z)) 0x800000  (* E-PEND run2/RT *) ;
z8 (ANum (symaddr (Symbols.Asan.s__ZN6__asanL8instanceE + 0x60)%Z)) (symaddr (Symbols.Asan.Sec.s_rodata + 0x8f00)%Z)  (* E-PEND run2/RT *) ;
z8 (ANum (symaddr (Symbols.Asan.s__ZN6__asanL8instanceE + 0x68)%Z)) 0x0  (* E-PEND run2/RT *) ;
z8 (ANum (symaddr (Symbols.Asan.s__ZN6__asanL8instanceE + 0x318)%Z)) 0x10000000  (* E-PEND run2/RT *) ;
z8 (ANum (symaddr (Symbols.Asan.s__ZN6__asanL8instanceE + 0x320)%Z)) 0xe666661  (* E-PEND run2/RT *) ;
z8 (ANum (symaddr (Symbols.Asan.s__ZN6__asanL8instanceE + 0x328)%Z)) 0x100000  (* E-PEND run2/RT *) ;
z8 (ANum (symaddr (Symbols.Asan.s__ZN6__asanL8instanceE + 0xe20)%Z)) 0x10000000000  (* E-PEND run2/RT *) ;
z8 (ANum (symaddr (Symbols.Asan.s__ZN6__asanL8instanceE + 0xe28)%Z)) 0x108000010  (* E-PEND run2/RT *) ;
z8 (ANum (symaddr (Symbols.Asan.s_builtin_tls + 0x70)%Z)) (symaddr Symbols.Asan.s___pthread_tsd_main)  (* E-PEND run2/RT *) ;
z8 (ANum (symaddr (Symbols.Asan.s_builtin_tls + 0xc0)%Z)) (symaddr (Symbols.Asan.s_builtin_tls + 0xe8)%Z)  (* E-PEND run2/RT *) ;
z8 (ANum (symaddr (Symbols.Asan.s_builtin_tls + 0xe8)%Z)) 0x1  (* E-PEND run2/RT *) ;
z8 (ANum (symaddr (Symbols.Asan.s_builtin_tls + 0xf0)%Z)) (symaddr (Symbols.Asan.s_builtin_tls + 0x8c8)%Z)  (* E-PEND run2/RT *) ;
z8 (ANum (symaddr (Symbols.Asan.s_builtin_tls + 0xd8)%Z)) 0x0  (* E-PEND run2/RT *) ;
z8 (ANum (symaddr (Symbols.Asan.Sec.s_rodata + 0xd0)%Z)) 0x218a392cd3d5dbf  (* M-IMG pcrel *) ;
z8 (ANum (symaddr (Symbols.Asan.Sec.s_rodata + 0x48)%Z)) 0xcc6e96b9cc6e96b9  (* M-IMG pcrel *) ;
z8 (ANum (symaddr (Symbols.Asan.Sec.s_rodata + 0xc0)%Z)) 0xafffff00000fffff  (* M-IMG pcrel *) ;
z8 (ANum (symaddr (Symbols.Asan.Sec.s_rodata + 0x8)%Z)) 0xc6a4a7935bd1e995  (* M-IMG pcrel *) ;
z8 (ANum (symaddr (Symbols.Asan.Sec.s_rodata + 0x28)%Z)) 0x35253c9ade8f4ca8  (* M-IMG pcrel *) ;
z8 (ANum (symaddr (Symbols.Asan.Sec.s_rodata + 0xb8)%Z)) 0x9747b28c9747b28c  (* M-IMG pcrel *) ;
z8 (ANum (symaddr (Symbols.Asan.Sec.s_got + 0xcb8)%Z)) 0x10  (* M-IMG pcrel *) ;
z8 (ANum (symaddr (Symbols.Asan.Sec.s_rodata + 0x240)%Z)) 0x13080d0307020100  (* M-IMG pcrel *) ;
z8 (ANum (symaddr (Symbols.Asan.Sec.s_rodata + 0x248)%Z)) 0x281422091c0e1904  (* M-IMG run *) ;
z8 (ANum (symaddr (Symbols.Asan.Sec.s_rodata + 0x250)%Z)) 0x301d2e0f261a1105  (* M-IMG run *) ;
z8 (ANum (symaddr (Symbols.Asan.Sec.s_rodata + 0x258)%Z)) 0x3929321536231f0a  (* M-IMG run *) ;
z8 (ANum (symaddr (Symbols.Asan.Sec.s_rodata + 0x260)%Z)) 0x27211b18120c063f  (* M-IMG run *) ;
z8 (ANum (symaddr (Symbols.Asan.Sec.s_rodata + 0x268)%Z)) 0x3831351e2f2d2510  (* M-IMG run *) ;
z8 (ANum (symaddr (Symbols.Asan.Sec.s_rodata + 0x270)%Z)) 0x37342c2420170b3e  (* M-IMG run *) ;
z8 (ANum (symaddr (Symbols.Asan.Sec.s_rodata + 0x278)%Z)) 0x3a3b2a3c332b163d  (* M-IMG run *) ;
z8 (ANum (symaddr (Symbols.Asan.Sec.s_rodata + 0x140)%Z)) 0x13080d0307020100  (* M-IMG pcrel *) ;
z8 (ANum (symaddr (Symbols.Asan.Sec.s_rodata + 0x148)%Z)) 0x281422091c0e1904  (* M-IMG run *) ;
z8 (ANum (symaddr (Symbols.Asan.Sec.s_rodata + 0x150)%Z)) 0x301d2e0f261a1105  (* M-IMG run *) ;
z8 (ANum (symaddr (Symbols.Asan.Sec.s_rodata + 0x158)%Z)) 0x3929321536231f0a  (* M-IMG run *) ;
z8 (ANum (symaddr (Symbols.Asan.Sec.s_rodata + 0x160)%Z)) 0x27211b18120c063f  (* M-IMG run *) ;
z8 (ANum (symaddr (Symbols.Asan.Sec.s_rodata + 0x168)%Z)) 0x3831351e2f2d2510  (* M-IMG run *) ;
z8 (ANum (symaddr (Symbols.Asan.Sec.s_rodata + 0x170)%Z)) 0x37342c2420170b3e  (* M-IMG run *) ;
z8 (ANum (symaddr (Symbols.Asan.Sec.s_rodata + 0x178)%Z)) 0x3a3b2a3c332b163d  (* M-IMG run *) ;
z8 (ANum (symaddr Symbols.Asan.s__ZN11__sanitizerL7MFHooksE)) 0x0  (* E-PEND pcrel/RT *) ;
z8 (ANum (symaddr (Symbols.Asan.s__ZN11__sanitizerL7MFHooksE + 0x8)%Z)) 0x0  (* E-PEND run2/RT *) ;
z8 (ANum (symaddr (Symbols.Asan.s__ZN11__sanitizerL7MFHooksE + 0x10)%Z)) 0x0  (* E-PEND run2/RT *) ;
z8 (ANum (symaddr (Symbols.Asan.s__ZN11__sanitizerL7MFHooksE + 0x18)%Z)) 0x0  (* E-PEND run2/RT *) ;
z8 (ANum (symaddr (Symbols.Asan.s__ZN11__sanitizerL7MFHooksE + 0x20)%Z)) 0x0  (* E-PEND run2/RT *) ;
z8 (ANum (symaddr (Symbols.Asan.s__ZN11__sanitizerL7MFHooksE + 0x28)%Z)) 0x0  (* E-PEND run2/RT *) ;
z8 (ANum (symaddr (Symbols.Asan.s__ZN11__sanitizerL7MFHooksE + 0x30)%Z)) 0x0  (* E-PEND run2/RT *) ;
z8 (ANum (symaddr (Symbols.Asan.s__ZN11__sanitizerL7MFHooksE + 0x38)%Z)) 0x0  (* E-PEND run2/RT *) ;
z8 (ANum (symaddr (Symbols.Asan.s__ZN11__sanitizerL7MFHooksE + 0x40)%Z)) 0x0  (* E-PEND run2/RT *) ;
z8 (ANum (symaddr (Symbols.Asan.s__ZN11__sanitizerL7MFHooksE + 0x48)%Z)) 0x0  (* E-PEND run2/RT *) ;
z8 (ANum (symaddr (Symbols.Asan.Sec.s_got + 0x40)%Z)) (symaddr Symbols.Asan.s__ZN11__sanitizer14PageSizeCachedE)  (* M-IMG pcrel *) ;
z8 (ANum (symaddr (Symbols.Asan.Sec.s_got + 0x48)%Z)) (symaddr Symbols.Asan.s__ZN11__sanitizer22SecondaryAllocatorNameE)  (* M-IMG pcrel *) ;
z8 (ANum (symaddr (Symbols.Asan.Sec.s_got + 0x50)%Z)) (symaddr Symbols.Asan.s__ZN11__sanitizer21common_flags_dont_useE)  (* M-IMG pcrel *) ;
z8 (ANum (symaddr (Symbols.Asan.Sec.s_got + 0x58)%Z)) (symaddr Symbols.Asan.s__ZN6__asan28asan_flags_dont_use_directlyE)  (* M-IMG pcrel *) ;
z8 (ANum (symaddr (Symbols.Asan.Sec.s_got + 0x60)%Z)) (symaddr Symbols.Asan.s___asan_shadow_memory_dynamic_address)  (* M-IMG pcrel *) ;
z8 (ANum (symaddr (Symbols.Asan.Sec.s_got + 0x68)%Z)) (symaddr Symbols.Asan.s__ZN6__asan10kMidMemBegE)  (* M-IMG pcrel *) ;
z8 (ANum (symaddr (Symbols.Asan.Sec.s_got + 0x70)%Z)) (symaddr Symbols.Asan.s__ZN6__asan10kMidMemEndE)  (* M-IMG pcrel *) ;
z8 (ANum (symaddr (Symbols.Asan.Sec.s_got + 0x78)%Z)) (symaddr Symbols.Asan.s__ZN6__asan11kHighMemEndE)  (* M-IMG pcrel *) ;
z8 (ANum (symaddr (Symbols.Asan.Sec.s_got + 0x80)%Z)) (symaddr Symbols.Asan.s__ZN14__interception11real_memsetE)  (* M-IMG pcrel *) ;
z8 (ANum (symaddr (Symbols.Asan.Sec.s_got + 0x88)%Z)) (symaddr Symbols.Asan.s__ZN14__interception11real_memcpyE)  (* M-IMG pcrel *) ;
z8 (ANum (symaddr (Symbols.Asan.Sec.s_got + 0x90)%Z)) (symaddr Symbols.Asan.s__ZN11__sanitizer20PrimaryAllocatorNameE)  (* M-IMG pcrel *) ;
z8 (ANum (symaddr (Symbols.Asan.Sec.s_got + 0x98)%Z)) (symaddr Symbols.Asan.s__ZN11__sanitizer17SanitizerToolNameE)  (* M-IMG pcrel *) ;
z8 (ANum (symaddr (Symbols.Asan.Sec.s_got + 0xa0)%Z)) 0x1  (* M-IMG pcrel *) ;
z8 (ANum (symaddr (Symbols.Asan.Sec.s_got + 0xa8)%Z)) (symaddr Symbols.Asan.s__ZN11__sanitizer25sealed_report_in_progressE)  (* M-IMG pcrel *) ;
z8 (ANum (symaddr (Symbols.Asan.Sec.s_got + 0xb0)%Z)) (symaddr Symbols.Asan.s__ZN11__sanitizer17current_verbosityE)  (* M-IMG pcrel *) ;
z8 (ANum (symaddr (Symbols.Asan.Sec.s_got + 0xb8)%Z)) (symaddr Symbols.Asan.s___asan_option_detect_stack_use_after_return)  (* M-IMG pcrel *) ;
z8 (ANum (symaddr Symbols.Asan.Sec.s_asan_globals)) (symaddr (Symbols.Asan.Sec.s_rodata + 68128)%Z)  (* M-DESC descriptor *) ;
z8 (ANum (symaddr (Symbols.Asan.Sec.s_asan_globals + 0x8)%Z)) 0xd  (* M-DESC descriptor *) ;
z8 (ANum (symaddr (Symbols.Asan.Sec.s_asan_globals + 0x10)%Z)) 0x20  (* M-DESC descriptor *) ;
z8 (ANum (symaddr (Symbols.Asan.Sec.s_asan_globals + 0x18)%Z)) (symaddr (Symbols.Asan.Sec.s_rodata + 0xbcf7)%Z)  (* M-DESC descriptor *) ;
z8 (ANum (symaddr (Symbols.Asan.Sec.s_asan_globals + 0x20)%Z)) (symaddr (Symbols.Asan.Sec.s_rodata + 68160)%Z)  (* M-DESC descriptor *) ;
z8 (ANum (symaddr (Symbols.Asan.Sec.s_asan_globals + 0x28)%Z)) 0x0  (* M-DESC descriptor *) ;
z8 (ANum (symaddr (Symbols.Asan.Sec.s_asan_globals + 0x30)%Z)) 0x0  (* M-DESC descriptor *) ;
z8 (ANum (symaddr (Symbols.Asan.Sec.s_asan_globals + 0x38)%Z)) 0xffffffffffffffff  (* M-DESC descriptor *) ;
z8 (ANum (symaddr (Symbols.Asan.Sec.s_asan_globals + 0x40)%Z)) (symaddr (Symbols.Asan.Sec.s_rodata + 68192)%Z)  (* M-DESC descriptor *) ;
z8 (ANum (symaddr (Symbols.Asan.Sec.s_asan_globals + 0x48)%Z)) 0x3  (* M-DESC descriptor *) ;
z8 (ANum (symaddr (Symbols.Asan.Sec.s_asan_globals + 0x50)%Z)) 0x20  (* M-DESC descriptor *) ;
z8 (ANum (symaddr (Symbols.Asan.Sec.s_asan_globals + 0x58)%Z)) (symaddr (Symbols.Asan.Sec.s_rodata + 0xbcf7)%Z)  (* M-DESC descriptor *) ;
z8 (ANum (symaddr (Symbols.Asan.Sec.s_asan_globals + 0x60)%Z)) (symaddr (Symbols.Asan.Sec.s_rodata + 68224)%Z)  (* M-DESC descriptor *) ;
z8 (ANum (symaddr (Symbols.Asan.Sec.s_asan_globals + 0x68)%Z)) 0x0  (* M-DESC descriptor *) ;
z8 (ANum (symaddr (Symbols.Asan.Sec.s_asan_globals + 0x70)%Z)) 0x0  (* M-DESC descriptor *) ;
z8 (ANum (symaddr (Symbols.Asan.Sec.s_asan_globals + 0x78)%Z)) 0xffffffffffffffff  (* M-DESC descriptor *) ;
z8 (ANum (symaddr (Symbols.Asan.Sec.s_asan_globals + 0x80)%Z)) (symaddr Symbols.Asan.s_g_file_len)  (* M-DESC descriptor *) ;
z8 (ANum (symaddr (Symbols.Asan.Sec.s_asan_globals + 0x88)%Z)) 0x8  (* M-DESC descriptor *) ;
z8 (ANum (symaddr (Symbols.Asan.Sec.s_asan_globals + 0x90)%Z)) 0x20  (* M-DESC descriptor *) ;
z8 (ANum (symaddr (Symbols.Asan.Sec.s_asan_globals + 0x98)%Z)) (symaddr (Symbols.Asan.Sec.s_rodata + 0x556d)%Z)  (* M-DESC descriptor *) ;
z8 (ANum (symaddr (Symbols.Asan.Sec.s_asan_globals + 0xa0)%Z)) (symaddr (Symbols.Asan.Sec.s_rodata + 68160)%Z)  (* M-DESC descriptor *) ;
z8 (ANum (symaddr (Symbols.Asan.Sec.s_asan_globals + 0xa8)%Z)) 0x0  (* M-DESC descriptor *) ;
z8 (ANum (symaddr (Symbols.Asan.Sec.s_asan_globals + 0xb0)%Z)) 0x0  (* M-DESC descriptor *) ;
z8 (ANum (symaddr (Symbols.Asan.Sec.s_asan_globals + 0xb8)%Z)) 0xffffffffffffffff  (* M-DESC descriptor *) ;
z8 (ANum (symaddr (Symbols.Asan.Sec.s_asan_globals + 0xc0)%Z)) (symaddr Symbols.Asan.s_g_file)  (* M-DESC descriptor *) ;
z8 (ANum (symaddr (Symbols.Asan.Sec.s_asan_globals + 0xc8)%Z)) 0x8  (* M-DESC descriptor *) ;
z8 (ANum (symaddr (Symbols.Asan.Sec.s_asan_globals + 0xd0)%Z)) 0x20  (* M-DESC descriptor *) ;
z8 (ANum (symaddr (Symbols.Asan.Sec.s_asan_globals + 0xd8)%Z)) (symaddr (Symbols.Asan.Sec.s_rodata + 0x9add)%Z)  (* M-DESC descriptor *) ;
z8 (ANum (symaddr (Symbols.Asan.Sec.s_asan_globals + 0xe0)%Z)) (symaddr (Symbols.Asan.Sec.s_rodata + 68160)%Z)  (* M-DESC descriptor *) ;
z8 (ANum (symaddr (Symbols.Asan.Sec.s_asan_globals + 0xe8)%Z)) 0x0  (* M-DESC descriptor *) ;
z8 (ANum (symaddr (Symbols.Asan.Sec.s_asan_globals + 0xf0)%Z)) 0x0  (* M-DESC descriptor *) ;
z8 (ANum (symaddr (Symbols.Asan.Sec.s_asan_globals + 0xf8)%Z)) 0xffffffffffffffff  (* M-DESC descriptor *) ;
z1 (ANum (symaddr Symbols.Asan.s__ZN8__sancov12_GLOBAL__N_119pc_guard_controllerE)) 0x0  (* E-PEND pcrel/RT *) ;
z8 (ANum (symaddr Symbols.Asan.s__ZN6__asanL14mu_for_globalsE)) 0x0  (* E-PEND run2/RT *) ;
z2 (ANum (symaddr (Symbols.Asan.s__ZN6__asanL8instanceE + 0x372)%Z)) 0x0  (* E-PEND run2/RT *) ;
z4 (ANum (symaddr (Symbols.Asan.s__ZN6__asanL8instanceE + 0x374)%Z)) 0x0  (* E-PEND run2/RT *) ;
z1 (ANum (symaddr (Symbols.Asan.s__ZN6__asanL8instanceE + 0x2a9)%Z)) 0x0  (* E-PEND run2/RT *) ;
z2 (ANum (symaddr (Symbols.Asan.s__ZN6__asanL8instanceE + 0x2aa)%Z)) 0x0  (* E-PEND run2/RT *) ;
z4 (ANum (symaddr (Symbols.Asan.s__ZN6__asanL8instanceE + 0x2ac)%Z)) 0x0  (* E-PEND run2/RT *) ;
z8 (ANum (symaddr Symbols.Asan.s__ZN11__sanitizer22SecondaryAllocatorNameE)) (symaddr (Symbols.Asan.Sec.s_rodata + 0x8f00)%Z)  (* M-IMG pcrel *) ;
z8 (ANum (symaddr (Symbols.Asan.Sec.s_rodata + 0xc978)%Z)) 0x612079726f6d656d  (* M-IMG pcrel *) ;
z8 (ANum (symaddr (Symbols.Asan.Sec.s_rodata + 0xc980)%Z)) 0x7365726464612074  (* M-IMG run *) ;
z4 (ANum (symaddr (Symbols.Asan.Sec.s_rodata + 0xc988)%Z)) 0x70252073  (* M-IMG run *) ;
z1 (ANum (symaddr (Symbols.Asan.Sec.s_rodata + 0xc98c)%Z)) 0x0  (* M-IMG run *) ;
z4 (ANum (symaddr (Symbols.Asan.Sec.s_rodata + 67488)%Z)) (symaddr ((Symbols.Asan.s__ZN11__sanitizer9VSNPrintfEPciPKcPv + 0x350) - (Symbols.Asan.Sec.s_rodata + 67392))%Z)  (* M-IMG measured *) ;
z8 (ANum (symaddr (Symbols.Asan.Sec.s_got + 0xce8)%Z)) (symaddr Symbols.Asan.s___stack_chk_guard)  (* M-IMG pcrel *) ;
z8 (ANum (symaddr (Symbols.Asan.s___libc + 0x30)%Z)) 0x1000  (* E-PEND pcrel/RT *) ;
z1 (ANum (symaddr (Symbols.Asan.s_sysconf_values + 0x3c)%Z)) 0x4  (* M-IMG run *) ;
z1 (ANum (symaddr (Symbols.Asan.s_sysconf_values + 0x3d)%Z)) 0xff  (* M-IMG run *) ;
z4 (ANum (symaddr (Symbols.Asan.Sec.s_rodata + 69636)%Z)) (symaddr ((Symbols.Asan.s_sysconf + 0x208) - (Symbols.Asan.Sec.s_rodata + 69624))%Z)  (* M-IMG run2 *) ;
z1 (ANum (symaddr (Symbols.Asan.s__ZN11__sanitizer21common_flags_dont_useE + 0xdb)%Z)) 0x1  (* E-PEND run2/RT *) ;
z1 (ANum (symaddr (Symbols.Asan.s__ZN11__sanitizer21common_flags_dont_useE + 0xf4)%Z)) 0x1  (* E-PEND run2/RT *) ;
z8 (ANum (symaddr Symbols.Asan.s__ZL24interceptor_metadata_map)) (symaddr Symbols.Asan.s__ZZL28InitializeCommonInterceptorsvE12metadata_mem)  (* E-PEND pcrel/RT *) ;
z8 (ANum (symaddr Symbols.Asan.s__ZN14__interception11real_fflushE)) (symaddr Symbols.Asan.s_fflush_unlocked)  (* M-IMG pcrel *) ;
z8 (ANum (symaddr Symbols.Asan.s__ZN14__interception11real_fcloseE)) (symaddr Symbols.Asan.s_fclose)  (* M-IMG pcrel *) ;
z8 (ANum (symaddr Symbols.Asan.s__ZN14__interception10real_fopenE)) (symaddr Symbols.Asan.s_fopen)  (* M-IMG pcrel *) ;
z8 (ANum (symaddr Symbols.Asan.s__ZN14__interception11real_strchrE)) (symaddr Symbols.Asan.s_strchr)  (* M-IMG pcrel *) ;
z1 (ANum (symaddr (Symbols.Asan.Sec.s_rodata + 68141)%Z)) 0x0  (* M-IMG in_rom pin: descriptor 0 redzone, a Theorem Labs lane 23:56Z *) ;
z1 (ANum (symaddr (Symbols.Asan.Sec.s_rodata + 68142)%Z)) 0x0 ;
z1 (ANum (symaddr (Symbols.Asan.Sec.s_rodata + 68143)%Z)) 0x0 ;
z1 (ANum (symaddr (Symbols.Asan.Sec.s_rodata + 68144)%Z)) 0x0 ;
z1 (ANum (symaddr (Symbols.Asan.Sec.s_rodata + 68145)%Z)) 0x0 ;
z1 (ANum (symaddr (Symbols.Asan.Sec.s_rodata + 68146)%Z)) 0x0 ;
z1 (ANum (symaddr (Symbols.Asan.Sec.s_rodata + 68147)%Z)) 0x0 ;
z1 (ANum (symaddr (Symbols.Asan.Sec.s_rodata + 68148)%Z)) 0x0 ;
z1 (ANum (symaddr (Symbols.Asan.Sec.s_rodata + 68149)%Z)) 0x0 ;
z1 (ANum (symaddr (Symbols.Asan.Sec.s_rodata + 68150)%Z)) 0x0 ;
z1 (ANum (symaddr (Symbols.Asan.Sec.s_rodata + 68151)%Z)) 0x0 ;
z1 (ANum (symaddr (Symbols.Asan.Sec.s_rodata + 68152)%Z)) 0x0 ;
z1 (ANum (symaddr (Symbols.Asan.Sec.s_rodata + 68153)%Z)) 0x0 ;
z1 (ANum (symaddr (Symbols.Asan.Sec.s_rodata + 68154)%Z)) 0x0 ;
z1 (ANum (symaddr (Symbols.Asan.Sec.s_rodata + 68155)%Z)) 0x0 ;
z1 (ANum (symaddr (Symbols.Asan.Sec.s_rodata + 68156)%Z)) 0x0 ;
z1 (ANum (symaddr (Symbols.Asan.Sec.s_rodata + 68157)%Z)) 0x0 ;
z1 (ANum (symaddr (Symbols.Asan.Sec.s_rodata + 68158)%Z)) 0x0 ;
z1 (ANum (symaddr (Symbols.Asan.Sec.s_rodata + 68159)%Z)) 0x0 ;
z1 (ANum (symaddr (Symbols.Asan.Sec.s_rodata + 68195)%Z)) 0x0  (* M-IMG measured *) ;
z1 (ANum (symaddr (Symbols.Asan.Sec.s_rodata + 68196)%Z)) 0x0  (* M-IMG measured *) ;
z1 (ANum (symaddr (Symbols.Asan.Sec.s_rodata + 68197)%Z)) 0x0  (* M-IMG measured *) ;
z1 (ANum (symaddr (Symbols.Asan.Sec.s_rodata + 68198)%Z)) 0x0  (* M-IMG measured *) ;
z1 (ANum (symaddr (Symbols.Asan.Sec.s_rodata + 68199)%Z)) 0x0  (* M-IMG measured *) ;
z1 (ANum (symaddr (Symbols.Asan.Sec.s_rodata + 68200)%Z)) 0x0  (* M-IMG in_rom pin: descriptor 1 redzone, a Theorem Labs lane 23:56Z *) ;
z1 (ANum (symaddr (Symbols.Asan.Sec.s_rodata + 68201)%Z)) 0x0 ;
z1 (ANum (symaddr (Symbols.Asan.Sec.s_rodata + 68202)%Z)) 0x0 ;
z1 (ANum (symaddr (Symbols.Asan.Sec.s_rodata + 68203)%Z)) 0x0 ;
z1 (ANum (symaddr (Symbols.Asan.Sec.s_rodata + 68204)%Z)) 0x0 ;
z1 (ANum (symaddr (Symbols.Asan.Sec.s_rodata + 68205)%Z)) 0x0 ;
z1 (ANum (symaddr (Symbols.Asan.Sec.s_rodata + 68206)%Z)) 0x0 ;
z1 (ANum (symaddr (Symbols.Asan.Sec.s_rodata + 68207)%Z)) 0x0 ;
z1 (ANum (symaddr (Symbols.Asan.Sec.s_rodata + 68208)%Z)) 0x0 ;
z1 (ANum (symaddr (Symbols.Asan.Sec.s_rodata + 68209)%Z)) 0x0 ;
z1 (ANum (symaddr (Symbols.Asan.Sec.s_rodata + 68210)%Z)) 0x0 ;
z1 (ANum (symaddr (Symbols.Asan.Sec.s_rodata + 68211)%Z)) 0x0 ;
z1 (ANum (symaddr (Symbols.Asan.Sec.s_rodata + 68212)%Z)) 0x0 ;
z1 (ANum (symaddr (Symbols.Asan.Sec.s_rodata + 68213)%Z)) 0x0 ;
z1 (ANum (symaddr (Symbols.Asan.Sec.s_rodata + 68214)%Z)) 0x0 ;
z1 (ANum (symaddr (Symbols.Asan.Sec.s_rodata + 68215)%Z)) 0x0 ;
z1 (ANum (symaddr (Symbols.Asan.Sec.s_rodata + 68216)%Z)) 0x0 ;
z1 (ANum (symaddr (Symbols.Asan.Sec.s_rodata + 68217)%Z)) 0x0 ;
z1 (ANum (symaddr (Symbols.Asan.Sec.s_rodata + 68218)%Z)) 0x0 ;
z1 (ANum (symaddr (Symbols.Asan.Sec.s_rodata + 68219)%Z)) 0x0 ;
z1 (ANum (symaddr (Symbols.Asan.Sec.s_rodata + 68220)%Z)) 0x0 ;
z1 (ANum (symaddr (Symbols.Asan.Sec.s_rodata + 68221)%Z)) 0x0 ;
z1 (ANum (symaddr (Symbols.Asan.Sec.s_rodata + 68222)%Z)) 0x0 ;
z1 (ANum (symaddr (Symbols.Asan.Sec.s_rodata + 68223)%Z)) 0x0 ;
z8 (ANum (symaddr Symbols.Asan.s__ZN14__interception13real_fmemopenE)) (symaddr Symbols.Asan.s_fmemopen)  (* M-IMG; pcap-only cell, no cgif twin: __interception::real_fmemopen (nm) holding musl
   fmemopen 0x8e870 (nm; value read from the pin); needed by a Theorem Labs lane's fmemopen interceptor walk
   (22:54Z). asan-ubsan twin: 0x9b4b0 -> 0x8e73c. *) ;
z8 (ANum (symaddr Symbols.Asan.s__ZN14__interception10real_freadE)) (symaddr Symbols.Asan.s_fread_unlocked)  (* M-IMG; pcap-only cell, no cgif twin: __interception::real_fread (nm) holding musl fread
   0x8ee5c (value read from the pin); named by a pcap walk (a working branch a05f266b202, 23:26Z; porter's ruling:
   a cell is added only when a pcap walk or premise names it). asan-ubsan twin: 0x9b438 -> 0x8ed28. *)
].
Definition Tfib_const_shadow : list acell :=
[ z1 (ANum (symaddr ((Symbols.Asan.Sec.s_rodata + 68136) / 8 + 0x7fff8000)%Z)) 0x5  ;          (* shadow-asan.tsv:2  0x20d08 partial 5   .str "<fuzz-input>", 13 B *)
z1 (ANum (symaddr ((Symbols.Asan.Sec.s_rodata + 68144) / 8 + 0x7fff8000)%Z)) 0xf9  ;           (* shadow-asan.tsv:3  0x20d10 redzone *)
z1 (ANum (symaddr ((Symbols.Asan.Sec.s_rodata + 68152) / 8 + 0x7fff8000)%Z)) 0xf9  ;           (* shadow-asan.tsv:4  0x20d18 redzone *)
z1 (ANum (symaddr ((Symbols.Asan.Sec.s_rodata + 68192) / 8 + 0x7fff8000)%Z)) 0x3  ;            (* shadow-asan.tsv:5  0x20d40 partial 3   .str "rb", 3 B *)
z1 (ANum (symaddr ((Symbols.Asan.Sec.s_rodata + 68200) / 8 + 0x7fff8000)%Z)) 0xf9  ;           (* shadow-asan.tsv:6  0x20d48 redzone *)
z1 (ANum (symaddr ((Symbols.Asan.Sec.s_rodata + 68208) / 8 + 0x7fff8000)%Z)) 0xf9  ;           (* shadow-asan.tsv:7  0x20d50 redzone *)
z1 (ANum (symaddr ((Symbols.Asan.Sec.s_rodata + 68216) / 8 + 0x7fff8000)%Z)) 0xf9  ;           (* shadow-asan.tsv:8  0x20d58 redzone *)
z1 (ANum (symaddr ((Symbols.Asan.s_g_file_len + 0x8) / 8 + 0x7fff8000)%Z)) 0xf9  ;           (* shadow-asan.tsv:10 0x5d3f48 redzone  g_file_len (.bss, 8 B: no partial) *)
z1 (ANum (symaddr ((Symbols.Asan.s_g_file_len + 0x10) / 8 + 0x7fff8000)%Z)) 0xf9  ;           (* shadow-asan.tsv:11 0x5d3f50 redzone *)
z1 (ANum (symaddr ((Symbols.Asan.s_g_file_len + 0x18) / 8 + 0x7fff8000)%Z)) 0xf9  ;           (* shadow-asan.tsv:12 0x5d3f58 redzone *)
z1 (ANum (symaddr ((Symbols.Asan.s_g_file + 0x8) / 8 + 0x7fff8000)%Z)) 0xf9  ;           (* shadow-asan.tsv:14 0x5d3f68 redzone  g_file (.bss, 8 B: no partial) *)
z1 (ANum (symaddr ((Symbols.Asan.s_g_file + 0x10) / 8 + 0x7fff8000)%Z)) 0xf9  ;           (* shadow-asan.tsv:15 0x5d3f70 redzone *)
z1 (ANum (symaddr ((Symbols.Asan.s_g_file + 0x18) / 8 + 0x7fff8000)%Z)) 0xf9  ;           (* shadow-asan.tsv:16 0x5d3f78 redzone *)
z1 (ANum (symaddr ((Symbols.Asan.Sec.s_asan_globals) / 8 + 0x7fff8000)%Z)) 0xf9  ;           (* guard run: the asan_globals section itself, 0x9e100..0x9e200,
                                          shadow-asan.tsv:17-48, 32 granules = 32 shadow bytes *)
z1 (ANum (symaddr ((Symbols.Asan.Sec.s_asan_globals + 0x8) / 8 + 0x7fff8000)%Z)) 0xf9  ;
z1 (ANum (symaddr ((Symbols.Asan.Sec.s_asan_globals + 0x10) / 8 + 0x7fff8000)%Z)) 0xf9  ;
z1 (ANum (symaddr ((Symbols.Asan.Sec.s_asan_globals + 0x18) / 8 + 0x7fff8000)%Z)) 0xf9  ;
z1 (ANum (symaddr ((Symbols.Asan.Sec.s_asan_globals + 0x20) / 8 + 0x7fff8000)%Z)) 0xf9  ;
z1 (ANum (symaddr ((Symbols.Asan.Sec.s_asan_globals + 0x28) / 8 + 0x7fff8000)%Z)) 0xf9  ;
z1 (ANum (symaddr ((Symbols.Asan.Sec.s_asan_globals + 0x30) / 8 + 0x7fff8000)%Z)) 0xf9  ;
z1 (ANum (symaddr ((Symbols.Asan.Sec.s_asan_globals + 0x38) / 8 + 0x7fff8000)%Z)) 0xf9  ;
z1 (ANum (symaddr ((Symbols.Asan.Sec.s_asan_globals + 0x40) / 8 + 0x7fff8000)%Z)) 0xf9  ;
z1 (ANum (symaddr ((Symbols.Asan.Sec.s_asan_globals + 0x48) / 8 + 0x7fff8000)%Z)) 0xf9  ;
z1 (ANum (symaddr ((Symbols.Asan.Sec.s_asan_globals + 0x50) / 8 + 0x7fff8000)%Z)) 0xf9  ;
z1 (ANum (symaddr ((Symbols.Asan.Sec.s_asan_globals + 0x58) / 8 + 0x7fff8000)%Z)) 0xf9  ;
z1 (ANum (symaddr ((Symbols.Asan.Sec.s_asan_globals + 0x60) / 8 + 0x7fff8000)%Z)) 0xf9  ;
z1 (ANum (symaddr ((Symbols.Asan.Sec.s_asan_globals + 0x68) / 8 + 0x7fff8000)%Z)) 0xf9  ;
z1 (ANum (symaddr ((Symbols.Asan.Sec.s_asan_globals + 0x70) / 8 + 0x7fff8000)%Z)) 0xf9  ;
z1 (ANum (symaddr ((Symbols.Asan.Sec.s_asan_globals + 0x78) / 8 + 0x7fff8000)%Z)) 0xf9  ;
z1 (ANum (symaddr ((Symbols.Asan.Sec.s_asan_globals + 0x80) / 8 + 0x7fff8000)%Z)) 0xf9  ;
z1 (ANum (symaddr ((Symbols.Asan.Sec.s_asan_globals + 0x88) / 8 + 0x7fff8000)%Z)) 0xf9  ;
z1 (ANum (symaddr ((Symbols.Asan.Sec.s_asan_globals + 0x90) / 8 + 0x7fff8000)%Z)) 0xf9  ;
z1 (ANum (symaddr ((Symbols.Asan.Sec.s_asan_globals + 0x98) / 8 + 0x7fff8000)%Z)) 0xf9  ;
z1 (ANum (symaddr ((Symbols.Asan.Sec.s_asan_globals + 0xa0) / 8 + 0x7fff8000)%Z)) 0xf9  ;
z1 (ANum (symaddr ((Symbols.Asan.Sec.s_asan_globals + 0xa8) / 8 + 0x7fff8000)%Z)) 0xf9  ;
z1 (ANum (symaddr ((Symbols.Asan.Sec.s_asan_globals + 0xb0) / 8 + 0x7fff8000)%Z)) 0xf9  ;
z1 (ANum (symaddr ((Symbols.Asan.Sec.s_asan_globals + 0xb8) / 8 + 0x7fff8000)%Z)) 0xf9  ;
z1 (ANum (symaddr ((Symbols.Asan.Sec.s_asan_globals + 0xc0) / 8 + 0x7fff8000)%Z)) 0xf9  ;
z1 (ANum (symaddr ((Symbols.Asan.Sec.s_asan_globals + 0xc8) / 8 + 0x7fff8000)%Z)) 0xf9  ;
z1 (ANum (symaddr ((Symbols.Asan.Sec.s_asan_globals + 0xd0) / 8 + 0x7fff8000)%Z)) 0xf9  ;
z1 (ANum (symaddr ((Symbols.Asan.Sec.s_asan_globals + 0xd8) / 8 + 0x7fff8000)%Z)) 0xf9  ;
z1 (ANum (symaddr ((Symbols.Asan.Sec.s_asan_globals + 0xe0) / 8 + 0x7fff8000)%Z)) 0xf9  ;
z1 (ANum (symaddr ((Symbols.Asan.Sec.s_asan_globals + 0xe8) / 8 + 0x7fff8000)%Z)) 0xf9  ;
z1 (ANum (symaddr ((Symbols.Asan.Sec.s_asan_globals + 0xf0) / 8 + 0x7fff8000)%Z)) 0xf9  ;
z1 (ANum (symaddr ((Symbols.Asan.Sec.s_asan_globals + 0xf8) / 8 + 0x7fff8000)%Z)) 0xf9   ].
Definition Tfib_const (ly : alayout) : list acell := Tfib_const_sym ++ Tfib_const_abs ++ Tfib_const_shadow.
Definition Tfib_zero_shadow : list (Z * Z) :=
[ (0x10000, (symaddr (Symbols.Asan.Sec.s_rodata + 68136)%Z) - 0x10000); ((symaddr (Symbols.Asan.Sec.s_rodata + 68160)%Z), (symaddr (Symbols.Asan.Sec.s_rodata + 68192)%Z) - (symaddr (Symbols.Asan.Sec.s_rodata + 68160)%Z)); ((symaddr (Symbols.Asan.Sec.s_rodata + 68224)%Z), (symaddr Symbols.Asan.Sec.s_asan_globals) - (symaddr (Symbols.Asan.Sec.s_rodata + 68224)%Z)); ((symaddr Symbols.Asan.s____asan_globals_registered), (symaddr (Symbols.Asan.s_g_file_len + 0x8)%Z) - (symaddr Symbols.Asan.s____asan_globals_registered)); ((symaddr Symbols.Asan.s_g_file), (symaddr (Symbols.Asan.s_g_file + 0x8)%Z) - (symaddr Symbols.Asan.s_g_file)); ((symaddr Symbols.Asan.s__ZN9libunwind13DwarfFDECacheINS_17LocalAddressSpaceEE5_lockE), IMG_TOP - (symaddr Symbols.Asan.s__ZN9libunwind13DwarfFDECacheINS_17LocalAddressSpaceEE5_lockE)) ].
(* IMG_TOP = Reusable/YImgTop.v pcap_img_end = 0x5f7000 (MEASURED hull of fuzz_pcap.asan). *)
(* Tfib_owned_static per-entry notes -- row n is element n of the Definition below, in order.
   They are kept OUT of the list on purpose: a Theorem Labs lane's termeval.ranges splits the
   list on top-level `;` and needs every element to end in `)`, so an in-list comment
   makes each range UNPARSED (pcmd/ownedcheck.py, gates3.md section 4).
   M = MEASURED on the unit image, E = ESTIMATED / DERIVED by the named rule.
    1. (0x9b528, 0x9ddc0 - 0x9b528)   E both ends by rule A (pcrel / run)
    2. (0x9e100, 0x100)               M asan_globals sh_addr / sh_size of the unit image
    3. (0x9e200, 8)                   E lo by rule A (pcrel); length unchanged
    4. (0x9e258, 0xa1108 - 0x9e258)   E both ends by rule A (pcrel / run2)
    5. (0xa1110, 0x5c3f10 - 0xa1110)  E both ends by rule A (run2 / pcrel)
    6. (0x5d4890, 0x3c)               E lo by rule A (run2); length unchanged
    7. (0x99830, 8)                   E lo by rule A (pcrel); length unchanged
    8. (0x99888, 8)                   E lo by rule A (pcrel); length unchanged
    9. (0x102e8, 8)                   E lo by rule A (pcrel); length unchanged
   10. (0x10308, 8)                   E lo by rule A (pcrel); length unchanged
   11. (0x10328, 8)                   E lo by rule A (pcrel); length unchanged
   12. (0x10398, 8)                   E lo by rule A (pcrel); length unchanged
   13. (0x103a0, 8)                   E lo by rule A (pcrel); length unchanged
   14. (0x103b0, 8)                   E lo by rule A (pcrel); length unchanged
   15. (0x10420, 64)                  E lo by rule A (pcrel); length unchanged
   16. (0x10520, 64)                  E lo by rule A (pcrel); length unchanged
   17. (0x99810, 0x20)                E lo by rule A (pcrel); length unchanged
   18. (0x99838, 0x18)                E lo by rule A (pcrel); length unchanged
   19. (0x99850, 0x38)                E lo by rule A (pcrel); length unchanged
   20. (0x9a398, 8)                   E lo by rule A (pcrel); length unchanged
   21. (0x9a488, 8)                   E lo by rule A (pcrel); length unchanged
   22. (0x9a4a8, 16)                  E lo by rule A (pcrel); length unchanged
   23. (0x9a510, 16)                  E lo by rule A (pcrel); length unchanged
   24. (0x9a520, 8)                   E lo by rule A (pcrel); length unchanged
   25. (0x20d0d, 0x13)                M descriptor 0: beg + size, size_with_redzone - size
   26. (0x20d43, 0x1d)                M descriptor 1: beg + size, size_with_redzone - size
   27. (0x5d3f48, 0x18)               M descriptor 2 (g_file_len, .bss, 8 B at 0x5d3f40): beg + size, size_with_redzone - size; auditor #23 j, 23:40Z: the harness-globals ruling keeps the bodies out and the redzones in
   28. (0x5d3f68, 0x18)               M descriptor 3 (g_file, .bss, 8 B at 0x5d3f60): beg + size, size_with_redzone - size; #23 j
   29. (0x5d4838, 8)                  E lo by rule A (run2); length unchanged
   30. (0x5d4888, 8)                  E lo by rule A (run2); length unchanged
   31. (0x5d48a0, 8)                  E lo by rule A (run2); length unchanged
   32. (0x5f5c38, 8)                  E lo by rule A (pcrel); length unchanged
   33. (0x1cc58, 21)                  E lo by rule A (pcrel); length unchanged
   34. (0x20a80, 4)                   E lo by rule A (measured); length unchanged
   35. (0x212e4, 4)                   E lo by rule A (run2); length unchanged
   36. (0x21348, 2)                   E lo by rule A (run); length unchanged
   37. (0x9a4b8, 8)                   E lo by rule A (pcrel); length unchanged
   38. (0x5f4b50, 8)                  E lo by rule A (pcrel); length unchanged *)
Definition Tfib_owned_static : list (Z * Z) :=
[((symaddr Symbols.Asan.s___dso_handle), (symaddr Symbols.Asan.s_oft_arg0) - (symaddr Symbols.Asan.s___dso_handle)) ;
((symaddr Symbols.Asan.Sec.s_asan_globals), 0x100) ;
((symaddr Symbols.Asan.s____asan_globals_registered), 8) ;
((symaddr Symbols.Asan.s__ZN6__asanL8instanceE), (symaddr Symbols.Asan.s__ZZL28InitializeCommonInterceptorsvE12metadata_mem) - (symaddr Symbols.Asan.s__ZN6__asanL8instanceE)) ;
((symaddr (Symbols.Asan.s__ZZL28InitializeCommonInterceptorsvE12metadata_mem + 0x8)%Z), (symaddr Symbols.Asan.s_read_stage) - (symaddr (Symbols.Asan.s__ZZL28InitializeCommonInterceptorsvE12metadata_mem + 0x8)%Z)) ;
((symaddr (Symbols.Asan.s_builtin_tls + 0xc8)%Z), 0x3c) ;
((symaddr (Symbols.Asan.Sec.s_got + 0x60)%Z), 8) ;
((symaddr (Symbols.Asan.Sec.s_got + 0xb8)%Z), 8) ;
((symaddr (Symbols.Asan.Sec.s_rodata + 0x8)%Z), 8) ;
((symaddr (Symbols.Asan.Sec.s_rodata + 0x28)%Z), 8) ;
((symaddr (Symbols.Asan.Sec.s_rodata + 0x48)%Z), 8) ;
((symaddr (Symbols.Asan.Sec.s_rodata + 0xb8)%Z), 8) ;
((symaddr (Symbols.Asan.Sec.s_rodata + 0xc0)%Z), 8) ;
((symaddr (Symbols.Asan.Sec.s_rodata + 0xd0)%Z), 8) ;
((symaddr (Symbols.Asan.Sec.s_rodata + 0x140)%Z), 64) ;
((symaddr (Symbols.Asan.Sec.s_rodata + 0x240)%Z), 64) ;
((symaddr (Symbols.Asan.Sec.s_got + 0x40)%Z), 0x20) ;
((symaddr (Symbols.Asan.Sec.s_got + 0x68)%Z), 0x18) ;
((symaddr (Symbols.Asan.Sec.s_got + 0x80)%Z), 0x38) ;
((symaddr (Symbols.Asan.Sec.s_got + 0xbc8)%Z), 8) ;
((symaddr (Symbols.Asan.Sec.s_got + 0xcb8)%Z), 8) ;
((symaddr (Symbols.Asan.Sec.s_got + 0xcd8)%Z), 16) ;
((symaddr (Symbols.Asan.Sec.s_got + 0xd40)%Z), 16) ;
((symaddr (Symbols.Asan.Sec.s_got + 0xd50)%Z), 8) ;
((symaddr (Symbols.Asan.Sec.s_rodata + 68141)%Z), 0x13) ;
((symaddr (Symbols.Asan.Sec.s_rodata + 68195)%Z), 0x1d) ;
((symaddr (Symbols.Asan.s_g_file_len + 0x8)%Z), 0x18) ;
((symaddr (Symbols.Asan.s_g_file + 0x8)%Z), 0x18) ;
((symaddr (Symbols.Asan.s_builtin_tls + 0x70)%Z), 8) ;
((symaddr (Symbols.Asan.s_builtin_tls + 0xc0)%Z), 8) ;
((symaddr (Symbols.Asan.s_builtin_tls + 0xd8)%Z), 8) ;
((symaddr Symbols.Asan.s___pthread_tsd_main), 8) ;
((symaddr (Symbols.Asan.Sec.s_rodata + 0xc978)%Z), 21) ;
((symaddr (Symbols.Asan.Sec.s_rodata + 67488)%Z), 4) ;
((symaddr (Symbols.Asan.Sec.s_rodata + 69636)%Z), 4) ;
((symaddr (Symbols.Asan.s_sysconf_values + 0x3c)%Z), 2) ;
((symaddr (Symbols.Asan.Sec.s_got + 0xce8)%Z), 8) ;
((symaddr (Symbols.Asan.s___libc + 0x30)%Z), 8)
].
Definition TFIB_TR0 (h : nat) : list Z := match h with O => [(symaddr (Symbols.Asan.s___asan_register_globals + 0xd0)%Z); (symaddr (Symbols.Asan.s___asan_register_elf_globals + 0x38)%Z)] | _ => [(symaddr (Symbols.Asan.s___asan_register_globals + 0xd0)%Z)] end.
(* The stack depot's hash of each trace, computed from the trace when this file is compiled: a relink that moves the
   traced pcs changes the hash with them. *)
Definition TFIB_HASH (h : nat) : Z := match h with
  | O => ltac:(let v := eval vm_compute in (YF0p.tfib_dhash (TFIB_TR0 O)) in exact v)
  | _ => ltac:(let v := eval vm_compute in (YF0p.tfib_dhash (TFIB_TR0 1)) in exact v) end.
Example tfib_hash_buckets : map (fun h => (TFIB_HASH h) mod d_tab_words) [0%nat; 1%nat] =
  ltac:(let v := eval vm_compute in (map (fun h => (TFIB_HASH h) mod d_tab_words) [0%nat; 1%nat]) in exact v).
Proof. vm_compute. reflexivity. Qed.
Record PcapSyms (B : asyms) : Prop := {
ts_inst : as_inst B = TFIB_INST;
ts_tp : as_tp B = TFIB_TP;
ts_tsd : as_tsd B = TFIB_TSD;
ts_gp : as_gp B = TFIB_GP;
ts_code : as_code B = Tfib_code;
ts_errno : as_errno B = TFIB_ERRNO;
ts_depot : as_depot B = TFIB_DEPOT;
ts_store : as_store B = TFIB_STORE;
ts_ial_lo : as_ialloc_lo B = TFIB_IAL_LO;
ts_ial_hi : as_ialloc_hi B = TFIB_IAL_HI;
ts_ial_w : as_ialloc_w B = TFIB_IAL_W;
ts_ial_flag : as_ialloc_flag B = TFIB_IAL_FLAG;
ts_oom : as_oom_byte B = TFIB_OOM;
ts_ok : asyms_ok B;
ts_owned : as_owned_static B = Tfib_owned_static;
ts_const : forall ly, as_const B ly = Tfib_const ly;
ts_junk : forall ly r, In r (as_junk B ly) -> exists z, fst r = ANum z /\ (symaddr ImgPages.Asan.relro_lo) <= z /\ z + snd r <= IMG_TOP;
(* 0x99000 = the page of fuzz_pcap.asan's first RW PT_LOAD (0x99298); the donor's 0x9d000 is the page of cgif's (0x9da00).  IMG_TOP replaces the donor's 0x5fb000: the core rule since 20:57Z allows no image-end literal outside Reusable/YImgTop.v (a Theorem Labs lane). *)
ts_junk_comb : forall ly, In (ANum (TFIB_INST + o_comb_stats), 40) (as_junk B ly);
ts_junk_ly : forall ly ly', as_junk B ly' = as_junk B ly;
ts_zsh : as_zero_shadow B = Tfib_zero_shadow;
ts_universe : universe_ok (as_universe B);
ts_universe_drv : forall t, In t DRV_TRACES -> In t (as_universe B);
ts_hash : forall h, (h < 2)%nat -> (as_dhash B (TFIB_TR0 h)) mod 2 ^ 64 = TFIB_HASH h
}.
