(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/A/AF0m.v, with its module paths changed, names TfibSyms -> GrantSyms, its addresses moved to libreac/fuzz_grant's ASan build, the bytes start-up leaves marked usable (Tfib_zero_shadow) and the guard bytes of the 13 globals the ASan build registers (in Tfib_owned_static) computed from fuzz_grant.asan's asan_globals, and the trace store's hashes and buckets recomputed from the moved start-up trace. *)
(* Modified by Theorem Labs, 2026-10: TFIB_IAL_HI and TFIB_IAL_W are libreac/fuzz_decode.asan's 0x122ff0 and 0xe2d80, moved from the donor's by the relocation. *)
(* Modified by Theorem Labs, 2026-10: Tfib_const_abs re-derived from libreac/fuzz_decode.asan's bytes: the 3 asan_globals descriptors at 0x9d610 (all 8 fields each), __asan_option_detect_stack_use_after_return at 0xa0dc0, real_atoll at 0x9abb0 and real_fflush at 0x9ab00, and the two jump-table entries at 0x20ad4 and 0x21324, which are offsets from their table base, not code addresses. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/libreac/fuzz_grant/lib/A/AF0m.v (donor image sha256 c2c7559b29bd), with its module paths changed and its addresses moved to libreac/fuzz_decode's ASan build. *)
(* Modified by Theorem Labs, 2026-10: Tfib_owned_static DERIVED from libreac/fuzz_decode.asan's own section headers and symtab (and its asan_globals), not relocated: see startdecode/gen/A/baseaudit.tsv. *)
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import YG00 YG01 YG0f.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.A Require Import AF0l.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Definition TFIB_INST : Z := 0x9d758.      Definition TFIB_TP : Z := 0x5d3d58.       Definition TFIB_TSD : Z := 0x5f5100.
Definition TFIB_DEPOT : Z := 0x182c98.     Definition TFIB_STORE : Z := 0x172c88.
Definition TFIB_IAL_LO : Z := 0xa1fc0.    Definition TFIB_IAL_HI : Z := 0x122ff0.   Definition TFIB_IAL_W : Z := 0xe2d80.
Definition TFIB_IAL_FLAG : Z := 0x130848.  Definition TFIB_OOM : Z := 0x123020.
Definition TFIB_MAIN : Z := 0x7fbc4.      Definition TFIB_MAIN_RA : Z := 0x88158.  Definition TFIB_GP : Z := 0x10800.
Definition TFIB_ERRNO : Z := 0x5d3cb4.
Definition DRV_TRACES : list (list Z) :=
[[0x52204; 0x7fc18]; [0x52204; 0x7fc6c]; [0x52204; 0x7fef8]; [0x52204];
[0x520a4; 0x7fc90]; [0x520a4; 0x7fdc0]; [0x520a4; 0x7ff8c]; [0x520a4]].
Definition Tfib_const_sym : list acell :=
[ c8 (AT 0) (AC 0); c8 (AT 8) (ATop 0); c8 (AT 16) (ATop (- kStackSpan)); z8 (AT 24) 0; z8 (AT 32) 0; z1 (AT 40) 0;
z8 (AT 48) 0x5d4490; z8 (AT 56) 0x5d456c; z8 (AT 64) 0x5d3d60; c8 (AT 72) (AF 0)    ;
z4 (AC 8) 0; c8 (AC 152) (AT 0);
c8 (ATsd 0) (AC 0); c8 (ATp 0) (AF 0); c8 (ATp (-88)) (ATsd 0); z8 (ATp (-8)) 0x5d3d78  ;
c8 (ATp 8) (AD 0); c8 (AD 24) (ATp 0)  ;
c8 (AInst o_space) (ASp 0); c8 (AInst o_rinfo) (ASp kRegionInfoOff); c8 (AInst o_sec_chunks) (AQ 0); c8 (AInst 80) (AQ 0) ].
(* Start-up-only image cells (the .got words ioctl_table_fill reads, and their like) are not listed here either:
   the certificate's KImg range in A/AB01.v (65536 633856 = [0x10000, 0x9ac00), no KWord over them) says the
   image bytes are unchanged, and no walk after main reads them. *)
(* Not pinned here, on purpose: the owned read-only redzone tails of the 3 registered globals, 60 bytes —
   0x20d4c+20, 0x20d6c+20, 0x20d8c+20 (.rodata). No contract of libreac/fuzz_decode

   needs the kept read-only view of them (the strncmp / memchr / strlen-type interceptors do); a unit whose contracts
   need it appends them after the last row of Tfib_const_abs, so no index moves, and A/AF0mCheck.v checks them. *)
Definition Tfib_const_abs : list acell :=
[
z8 (ANum 0x1328e8) 0x1  ;
z8 (ANum 0x1328f0) 0x0  ;
z8 (ANum 0x1328f8) 0x0  ;
z8 (ANum 0x132900) 0x13eeb  ;
z8 (ANum 0x132908) 0x1e00010000  ;
z8 (ANum 0x132910) 0x0  ;
z8 (ANum 0x132918) 0x0  ;
z8 (ANum 0x132920) 0x0  ;
z8 (ANum 0x132928) 0x0  ;
z8 (ANum 0x132930) 0x10101000101  ;
z8 (ANum 0x132938) 0x100000000  ;
z8 (ANum 0x132940) 0x0  ;
z8 (ANum 0x132948) 0x0  ;
z8 (ANum 0x132950) 0x0  ;
z8 (ANum 0x132958) 0x10001  ;
z8 (ANum 0x132960) 18446744073709551615  ;
z8 (ANum 0x132968) 0x1181f  ;
z8 (ANum 0x132970) 0x100  ;
z8 (ANum 0x132978) 0x0  ;
z8 (ANum 0x132980) 0x0  ;
z8 (ANum 0x132988) 0x0  ;
z8 (ANum 0x132990) 0x0  ;
z8 (ANum 0x132998) 0xffffffff00000000  ;
z8 (ANum 0x1329a0) 0x1  ;
z8 (ANum 0x1329a8) 0x14247  ;
z8 (ANum 0x1329b0) 0x13eeb  ;
z8 (ANum 0x1329b8) 0x13eeb  ;
z8 (ANum 0x1329c0) 0x10101000100  ;
z8 (ANum 0x1329c8) 0x0  ;
z8 (ANum 0x1329d0) 0x1d9e1  ;
z8 (ANum 0x1329d8) 0x101000100000000  ;
z8 (ANum 0x1329e0) 0x101010101010101  ;
z8 (ANum 0x1329e8) 0x1010101  ;
z8 (ANum 0x1329f0) 0x10100000001  ;
z8 (ANum 0x9e5b8) 0x100ffffffff  ;
z8 (ANum 0x9e5c0) 0x1000000400  ;
z8 (ANum 0x9e5c8) 0x800  ;
z8 (ANum 0x9e5d0) 0x101010000000001  ;
z8 (ANum 0x9e5d8) 0x1400000010  ;
z8 (ANum 0x9e5e0) 0x100000000000  ;
z8 (ANum 0x9e5e8) 0xbe00000000  ;
z8 (ANum 0x9e5f0) 0x100000055  ;
z8 (ANum 0x9e5f8) 0x0  ;
z8 (ANum 0x9e600) 0x1000100000000  ;
z8 (ANum 0x9e608) 0x101010101000001  ;
z8 (ANum 0x9e610) 0x1  ;
z8 (ANum 0x9e618) 0x200000001  ;
z8 (ANum 0x9e620) 0x13eeb  ;
z8 (ANum 0x9e628) 0x10101  ;
z8 (ANum 0xa0db8) 0x7fff8000  ;
z4 (ANum 0xa0dc0) 0x1  ;
z1 (ANum 0xa1a98) 0x1  ;
z1 (ANum 0xa1a99) 0x1  ;
z8 (ANum 0xa1aa0) 0x7fffffffffff  ;
z8 (ANum 0xa1aa8) 0x0  ;
z8 (ANum 0xa1ab0) 0x0  ;
z4 (ANum 0xa1abc) 0x1e  ;
z1 (ANum 0xa061c) 0x1  ;
z1 (ANum 0xa0620) 0x1  ;
z4 (ANum 0xa0624) 0x0  ;
z1 (ANum 0x123021) 0x1  ;
z1 (ANum 0x123022) 0x0  ;
z8 (ANum 0x130860) 0x1000  ;
z4 (ANum 0x1328dc) 0x0  ;
z8 (ANum 0x9abb0) 0x91cb4  ;
z8 (ANum 0x9abb8) 0x92070  ;
z8 (ANum 0x9abc0) 0x92474  ;
z8 (ANum 0x9aa70) 0x92040  ;
z8 (ANum 0x9aa78) 0x91f70  ;
z1 (ANum 0x132971) 0x1  ;
z4 (ANum 0x130858) 0x0  ;
z8 (ANum 0x99a48) 0x8  ;
z8 (ANum 0x9aa90) 0x97774  ;
z8 (ANum 0x9aa98) 0x8e624  ;
z8 (ANum 0x9ab68) 0x928fc  ;
z8 (ANum 0x9aa80) 0x91f74  ;
z1 (ANum 0x1329e3) 0x1  ;
z1 (ANum 0x13293c) 0x1  ;
z8 (ANum 0x9aab0) 0x919bc  ;
z8 (ANum 0x9aab8) 0x8e8ac  ;
z8 (ANum 0x9aaf8) 0x92c64  ;
z8 (ANum 0x998a8) 0xa1a99  ;
z8 (ANum 0x999b8) 0x20d40  ;
z8 (ANum 0x999d8) 0x9d6d0  ;
z8 (ANum 0x9d700) 0x1  ;
z8 (ANum 0x99a38) 0x1  ;
z8 (ANum 0x99a40) 0xfffffffffffff800  ;
z8 (ANum 0x172c90) 0x800000  ;
z8 (ANum 0x9d760) 0x2000011000  ;
z8 (ANum 0x9d768) 0x16b28  ;
z8 (ANum 0x9d770) 0x0  ;
z8 (ANum 0x9d780) 0xffffffff  ;
z8 (ANum 0x9d790) 0x0  ;
z8 (ANum 0x9d798) 0x1000  ;
z8 (ANum 0x9d7b0) 0x800000  ;
z8 (ANum 0x9d7b8) 0x19234  ;
z8 (ANum 0x9d7c0) 0x0  ;
z8 (ANum 0x9da70) 0x10000000  ;
z8 (ANum 0x9da78) 0xe666661  ;
z8 (ANum 0x9da80) 0x100000  ;
z8 (ANum 0x9e578) 0x10000000000  ;
z8 (ANum 0x9e580) 0x108000010  ;
z8 (ANum 0x5d3d00) 0x5f5100  ;
z8 (ANum 0x5d3d50) 0x5d3d78  ;
z8 (ANum 0x5d3d78) 0x1  ;
z8 (ANum 0x5d3d80) 0x5d4558  ;
z8 (ANum 0x5d3d68) 0x0  ;
z8 (ANum 0x103c8) 0x218a392cd3d5dbf  ;
z8 (ANum 0x10330) 0xcc6e96b9cc6e96b9  ;
z8 (ANum 0x103b0) 0xafffff00000fffff  ;
z8 (ANum 0x102e8) 0xc6a4a7935bd1e995  ;
z8 (ANum 0x10308) 0x35253c9ade8f4ca8  ;
z8 (ANum 0x103a8) 0x9747b28c9747b28c  ;
z8 (ANum 0x99998) 0x10  ;
z8 (ANum 0x10538) 0x13080d0307020100  ;
z8 (ANum 0x10540) 0x281422091c0e1904  ;
z8 (ANum 0x10548) 0x301d2e0f261a1105  ;
z8 (ANum 0x10550) 0x3929321536231f0a  ;
z8 (ANum 0x10558) 0x27211b18120c063f  ;
z8 (ANum 0x10560) 0x3831351e2f2d2510  ;
z8 (ANum 0x10568) 0x37342c2420170b3e  ;
z8 (ANum 0x10570) 0x3a3b2a3c332b163d  ;
z8 (ANum 0x10438) 0x13080d0307020100  ;
z8 (ANum 0x10440) 0x281422091c0e1904  ;
z8 (ANum 0x10448) 0x301d2e0f261a1105  ;
z8 (ANum 0x10450) 0x3929321536231f0a  ;
z8 (ANum 0x10458) 0x27211b18120c063f  ;
z8 (ANum 0x10460) 0x3831351e2f2d2510  ;
z8 (ANum 0x10468) 0x37342c2420170b3e  ;
z8 (ANum 0x10470) 0x3a3b2a3c332b163d  ;
z8 (ANum 0x132880) 0x0  ;
z8 (ANum 0x132888) 0x0  ;
z8 (ANum 0x132890) 0x0  ;
z8 (ANum 0x132898) 0x0  ;
z8 (ANum 0x1328a0) 0x0  ;
z8 (ANum 0x1328a8) 0x0  ;
z8 (ANum 0x1328b0) 0x0  ;
z8 (ANum 0x1328b8) 0x0  ;
z8 (ANum 0x1328c0) 0x0  ;
z8 (ANum 0x1328c8) 0x0  ;
z8 (ANum 0x98d20) 0x130860  ;
z8 (ANum 0x98d28) 0x9abf8  ;
z8 (ANum 0x98d30) 0x1328e8  ;
z8 (ANum 0x98d38) 0x9e5b8  ;
z8 (ANum 0x98d40) 0xa0db8  ;
z8 (ANum 0x98d48) 0xa1aa8  ;
z8 (ANum 0x98d50) 0xa1ab0  ;
z8 (ANum 0x98d58) 0xa1aa0  ;
z8 (ANum 0x98d60) 0x9abc0  ;
z8 (ANum 0x98d68) 0x9abb8  ;
z8 (ANum 0x98d70) 0x9abf0  ;
z8 (ANum 0x98d78) 0x9ac08  ;
z8 (ANum 0x98d80) 0x1  ;
z8 (ANum 0x98d88) 0x1328dc  ;
z8 (ANum 0x98d90) 0x130858  ;
z8 (ANum 0x98d98) 0xa0dc0  ;
z8 (ANum 0x9d610) 0x20d40  ;
z8 (ANum 0x9d618) 0xc  ;
z8 (ANum 0x9d620) 0x20  ;
z8 (ANum 0x9d628) 0x17dd3  ;
z8 (ANum 0x9d630) 0x20da0  ;
z8 (ANum 0x9d638) 0x0  ;
z8 (ANum 0x9d640) 0x0  ;
z8 (ANum 0x9d648) 0x5d3440  ;
z8 (ANum 0x9d650) 0x20d60  ;
z8 (ANum 0x9d658) 0xc  ;
z8 (ANum 0x9d660) 0x20  ;
z8 (ANum 0x9d668) 0x1588f  ;
z8 (ANum 0x9d670) 0x20da0  ;
z8 (ANum 0x9d678) 0x0  ;
z8 (ANum 0x9d680) 0x0  ;
z8 (ANum 0x9d688) 0x5d3441  ;
z8 (ANum 0x9d690) 0x20d80  ;
z8 (ANum 0x9d698) 0xc  ;
z8 (ANum 0x9d6a0) 0x20  ;
z8 (ANum 0x9d6a8) 0x12d84  ;
z8 (ANum 0x9d6b0) 0x20da0  ;
z8 (ANum 0x9d6b8) 0x0  ;
z8 (ANum 0x9d6c0) 0x0  ;
z8 (ANum 0x9d6c8) 0x5d3442  ;
















































































z1 (ANum 0x132c60) 0x0  ;
z8 (ANum 0x9e670) 0x0  ;
z2 (ANum 0x9daca) 0x0  ;
z4 (ANum 0x9dacc) 0x0  ;
z1 (ANum 0x9da01) 0x0  ;
z2 (ANum 0x9da02) 0x0  ;
z4 (ANum 0x9da04) 0x0  ;
z8 (ANum 0x9abf8) 0x19234   ;
z8 (ANum 0x1ccb0) 0x612079726f6d656d  ;
z8 (ANum 0x1ccb8) 0x7365726464612074  ;
z4 (ANum 0x1ccc0) 0x70252073  ;
z1 (ANum 0x1ccc4) 0x0  ;
z4 (ANum 0x20ad4) 0x45bd0  ;
z8 (ANum 0x999e0) 0x5f3d98  ;
z8 (ANum 0x5f4018) 0x1000  ;
z1 (ANum 0x21388) 0x04  ;
z1 (ANum 0x21389) 0xff  ;
z4 (ANum 0x21324) 0x66b00  ;
z1 (ANum 0x1329c3) 0x1  ;
z1 (ANum 0x1329dc) 0x1  ;
z8 (ANum 0xa0600) 0xa0608  ;

z8 (ANum 0x9ab00) 0x8e0b8  ;
z8 (ANum 0x9aa68) 0x9256c
;
z8 (ANum 0x999c0) 0x20d80  ;
z8 (ANum 0x999c8) 0x20d60  ;
z8 (ANum 0x10338) 0xe38e38e38e38e38f  ;
z4 (ANum 0x9d780) 0xffffffff  ;
z4 (ANum 0x13299c) 0xffffffff  ;
z4 (ANum 0x13290c) 0x1e  ;
z8 (ANum 0x999d0) 0x9d610
;
z4 (ANum 0x20d4c) 0x0  ;
z8 (ANum 0x20d50) 0x0  ;
z8 (ANum 0x20d58) 0x0  ;
z4 (ANum 0x20d6c) 0x0  ;
z8 (ANum 0x20d70) 0x0  ;
z8 (ANum 0x20d78) 0x0  ;
z4 (ANum 0x20d8c) 0x0  ;
z8 (ANum 0x20d90) 0x0  ;
z8 (ANum 0x20d98) 0x0
].
Definition Tfib_const_shadow : list acell :=
[ z1 (ANum 0x7fffc1a9) 0x4  ;
z1 (ANum 0x7fffc1aa) 0xf9  ;
z1 (ANum 0x7fffc1ab) 0xf9  ;
z1 (ANum 0x7fffc1ad) 0x4  ;
z1 (ANum 0x7fffc1ae) 0xf9  ;
z1 (ANum 0x7fffc1af) 0xf9  ;
z1 (ANum 0x7fffc1b1) 0x4  ;
z1 (ANum 0x7fffc1b2) 0xf9  ;
z1 (ANum 0x7fffc1b3) 0xf9  ;
z1 (ANum 0x8000bac2) 0xf9  ;
z1 (ANum 0x8000bac3) 0xf9  ;
z1 (ANum 0x8000bac4) 0xf9  ;
z1 (ANum 0x8000bac5) 0xf9  ;
z1 (ANum 0x8000bac6) 0xf9  ;
z1 (ANum 0x8000bac7) 0xf9  ;
z1 (ANum 0x8000bac8) 0xf9  ;
z1 (ANum 0x8000bac9) 0xf9  ;
z1 (ANum 0x8000baca) 0xf9  ;
z1 (ANum 0x8000bacb) 0xf9  ;
z1 (ANum 0x8000bacc) 0xf9  ;
z1 (ANum 0x8000bacd) 0xf9  ;
z1 (ANum 0x8000bace) 0xf9  ;
z1 (ANum 0x8000bacf) 0xf9  ;
z1 (ANum 0x8000bad0) 0xf9  ;
z1 (ANum 0x8000bad1) 0xf9  ;
z1 (ANum 0x8000bad2) 0xf9  ;
z1 (ANum 0x8000bad3) 0xf9  ;
z1 (ANum 0x8000bad4) 0xf9  ;
z1 (ANum 0x8000bad5) 0xf9  ;
z1 (ANum 0x8000bad6) 0xf9  ;
z1 (ANum 0x8000bad7) 0xf9  ;
z1 (ANum 0x8000bad8) 0xf9  ;
z1 (ANum 0x8000bad9) 0xf9   ].
Definition Tfib_const (ly : alayout) : list acell := Tfib_const_sym ++ Tfib_const_abs ++ Tfib_const_shadow.
Definition Tfib_zero_shadow : list (Z * Z) :=
[ (0x10000, 0x20d48 - 0x10000); (0x20d60, 0x20d68 - 0x20d60); (0x20d80, 0x20d88 - 0x20d80); (0x20da0, 0x9d610 - 0x20da0); (0x9d6d0, 0x5f6000 - 0x9d6d0) ].
Definition Tfib_owned_static : list (Z * Z) :=
[ (0x9aa50, 0x2878); (0x9d610, 0xc0); (0x9d700, 0x8); (0x9d758, 0x2eb0); (0xa0610, 0x522e00)    ; (0x5d3d58, 0x3c)  ;
(0x98d40, 0x8); (0x98d98, 0x8);
(0x102e8, 0x8); (0x10308, 0x8); (0x10330, 0x8); (0x103a8, 0x8); (0x103b0, 0x8); (0x103c8, 0x8); (0x10438, 0x40); (0x10538, 0x40);
(0x98d20, 0x20); (0x98d48, 0x18); (0x98d60, 0x38); (0x998a8, 0x8); (0x99998, 0x8); (0x999d0, 0x10); (0x99a38, 0x10); (0x99a48, 0x8)  ;
(0x20d4c, 0x14); (0x20d6c, 0x14); (0x20d8c, 0x14); 
(0x5d3d00, 0x8); (0x5d3d50, 0x8); (0x5d3d68, 0x8)  ; (0x5f5100, 0x8);
(0x1ccb0, 0x15); (0x20ad4, 0x4); (0x21324, 0x4); (0x21388, 0x2); (0x999e0, 0x8); (0x5f4018, 0x8) ;
(0x999c0, 8);
(0x999c8, 8);
(0x10338, 8) ;
(0x999b8, 8) ].
Definition TFIB_TR0 (h : nat) : list Z := match h with O => [0x3e168; 0x3f4b8] | _ => [0x3e168] end.
Definition TFIB_HASH (h : nat) : Z := match h with O => 9626852019045623916 | _ => 16313749981238458731 end.
Example tfib_hash_buckets : map (fun h => (TFIB_HASH h) mod d_tab_words) [0%nat; 1%nat] = [485484; 63851].
Proof. vm_compute. reflexivity. Qed.
Record GrantSyms (B : asyms) : Prop := {
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
ts_junk : forall ly r, In r (as_junk B ly) -> exists z, fst r = ANum z /\ 0x98000 <= z /\ z + snd r <= 0x5f6000;
ts_junk_comb : forall ly, In (ANum (TFIB_INST + o_comb_stats), 40) (as_junk B ly);
ts_junk_ly : forall ly ly', as_junk B ly' = as_junk B ly;
ts_zsh : as_zero_shadow B = Tfib_zero_shadow;
ts_universe : universe_ok (as_universe B);
ts_universe_drv : forall t, In t DRV_TRACES -> In t (as_universe B);
ts_hash : forall h, (h < 2)%nat -> (as_dhash B (TFIB_TR0 h)) mod 2 ^ 64 = TFIB_HASH h
}.
