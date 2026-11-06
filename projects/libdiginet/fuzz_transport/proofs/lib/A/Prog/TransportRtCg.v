(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: only the contract of the strlen wrapper of libreac/fuzz_identity.asan (trampoline 0x4218c -> ___interceptor_strlen 0x4221c -> musl strlen 0x94c64), restated from cgif_file_fuzzer lib/YG0d.v:401-419 astrnlen_realizes without the n bound (no `getr regs 11 = w64 n`, no `0 <= n < 2 ^ 63`, no `k + 8 <= n`; the string ends at the NUL at x + k, so first_byte is stated at k + 1), and with `rom_view segs W mem` replaced by `aro_unowned segs B (aview segs (w_H W) mem)` (lib/A/Rt/WrapRo.v: only the unowned read-only bytes, which a caller can carry across __asan_stack_malloc_<c>); module names. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_identity/lib/A/Rt/StrlenDef.v, with its module paths changed; 32 of its 67 lines of code are new or changed and 3 lines of the source are left out. *)
(* TransportRtCg: the callee TEXTS of three runtime entries that the image-A program-walk statements of
   libdiginet/fuzz_transport (fuzz_transport.asan e89be137db17) assume, as STATEMENTS only (no proof). No contract of
   these entries is on this unit's base: lib/Reusable has no SetShadowDef.v, no landed file states the release
   entry of a class-5 side-stack frame, and the strlen wrapper's text on the base is YG0d.v astrnlen_realizes, the
   bounded form with a read-only premise over the whole image (rom_view). __asan_stack_malloc_5 needs no text here:
   YG0d.v astack_malloc_realizes 5.

   - aset_shadow_realizes pc v: __asan_set_shadow_v at pc fills a0's n = a1 shadow bytes, inside the shadow of one live
     side-stack frame, with v. Image A calls it at TS___asan_set_shadow_00 (0x55270) and TS___asan_set_shadow_f8
     (0x55390) from diginet_session_tick, diginet_session_poll and build_and_receive, and at TS___asan_set_shadow_00 and
     TS___asan_set_shadow_f5 (0x55378) from on_announce.
   - astack_free_cls_realizes pc cid: the release entry __asan_stack_free_cid at pc of a class whose release fills the
     whole frame's shadow with 0xf5 (class 5 at TS___asan_stack_free_5, 0x3df10), and stores 0 at the frame's flag
     byte. Image A calls it from diginet_session_tick, diginet_session_poll and build_and_receive.
   - astrlen_realizes pc: the strlen wrapper at pc returns in a0 the length k of the NUL-terminated string at x = a0,
     reading x .. x + k, the rest of the 8-byte word that holds the NUL, the shadow of the range's hull, and unowned
     read-only bytes as the image holds them (aro_unowned). Image A calls it at TS___interceptor_trampoline_strlen
     (0x42ce4) from LLVMFuzzerTestOneInput.

   The walks that prove these entries (of the stack-free classes, of the set_shadow entries and of the strlen wrapper)
   must prove exactly these definitions, or a copy that is convertible to them. Each text below is verbatim from the
   source named above it, with this unit's module paths. *)
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YK11 YK0s YK0i YK15 YK0j YK18 YP09.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YM05.
Import ListNotations.
Open Scope Z_scope.
(* Source: libreac/fuzz_identity lib/A/Rt/WrapRo.v at origin/ossv/recipes (1aeda8ab8602): the read-only premise of
   astrlen_realizes below, every unowned byte of a read-only segment outside errno read as the image holds it. *)
Definition aro_unowned (segs : list Segment) (B : asyms) (rd : reader) : Prop :=
forall a, in_rom segs a -> ~ Exists (in_zr a) (as_owned_static B) -> ~ (as_errno B <= a < as_errno B + 4) ->
rd a = option_map (fun b : byte => bv_unsigned b) (seg_rom segs (Z_to_bv 64 a)).

Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Section c.
Variable segs : list Segment.
Variable B : asyms.

(* Source: libdiginet/fuzz_decode lib/Reusable/SetShadowDef.v (file sha256 222a99d8bbed; donor not released). The same
   Definition text is libreac/fuzz_grant lib/Reusable/SetShadowDef.v at origin/ossv/recipes. *)
Definition aset_shadow_realizes (pc v : Z) : Prop :=
forall ly S W regs mem md cid pos q n,
ecall_pre segs B ly S W regs mem md -> In (cid, pos) (frames S) ->
getr regs 10 = w64 q -> getr regs 11 = w64 n -> 0 < n ->
shadow_addr (frame_addr ly cid pos) <= q -> q + n <= shadow_addr (frame_addr ly cid pos) + fs_frame_bytes cid / 8 ->
SRr segs W (cfg_at segs pc regs mem md)
(fun W' c' => W' = W /\ exists regs' mem' md',
c' = cfg_at segs (raZ regs) regs' mem' md' /\
AR segs B ly S W mem' md' /\ aregs_preserved regs regs' /\ same_but_materialized md md' /\
(forall i, 0 <= i < n -> aview segs (w_H W) mem' (q + i) = Some v) /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (q <= a < q + n) -> aview segs (w_H W) mem' a = aview segs (w_H W) mem a) /\
(forall a, spZ regs - ESTACK <= a < spZ regs -> apresent (w_H W) mem' a) /\
(forall a, apresent (w_H W) mem a -> apresent (w_H W) mem' a)).

(* Source: libdiginet/fuzz_transport lib/A/Rt/RtStack.v (file sha256 d8909f5e5403; donor not released): a class-5
   text, not landed. *)
Definition astack_free_cls_realizes (pc cid : Z) : Prop :=
forall ly S W regs mem md pos n,
ecall_pre segs B ly S W regs mem md -> In (cid, pos) (frames S) ->
getr regs 10 = w64 (frame_addr ly cid pos) -> getr regs 11 = w64 n ->
rdword (aview segs (w_H W) mem) (frame_addr ly cid pos + fs_frame_bytes cid - 8) = Some (flag_addr ly cid pos) ->
SRr segs W (cfg_at segs pc regs mem md)
(fun W' c' => W' = W /\ exists regs' mem' md',
c' = cfg_at segs (raZ regs) regs' mem' md' /\
AR segs B ly (stack_free_state cid pos S) W mem' md' /\ aregs_preserved regs regs' /\ same_but_materialized md md' /\
(forall i, 0 <= i < fs_frame_bytes cid / 8 ->
aview segs (w_H W) mem' (shadow_addr (frame_addr ly cid pos) + i) = Some 0xf5) /\
(forall a, 0 <= a < 2 ^ 64 ->
~ (shadow_addr (frame_addr ly cid pos) <= a < shadow_addr (frame_addr ly cid pos) + fs_frame_bytes cid / 8) ->
a <> flag_addr ly cid pos -> ~ (spZ regs - ESTACK <= a < spZ regs) ->
aview segs (w_H W) mem' a = aview segs (w_H W) mem a) /\
(forall a, spZ regs - ESTACK <= a < spZ regs -> apresent (w_H W) mem' a)).

(* Source: libreac/fuzz_identity lib/A/Rt/StrlenDef.v at origin/ossv/recipes (1aeda8ab8602). *)
Definition astrlen_realizes (pc : Z) : Prop :=
forall ly S W regs mem md x k,
ecall_pre segs B ly S W regs mem md ->
ly_stk_lo ly + 2 * ESTACK <= spZ regs -> (forall a, spZ regs - 2 * ESTACK <= a < spZ regs -> apresent (w_H W) mem a) ->
getr regs 10 = w64 x -> 0 < x ->
0 <= k -> k + 1 < 2 ^ 32 -> x + k + 1 <= 2 ^ 63 ->
first_byte segs W mem x (k + 1) 0 k ->
src_ok segs W regs mem x (k + 1) -> (forall a, x <= a <= x + k -> ~ (spZ regs - 2 * ESTACK <= a < spZ regs)) -> amem_range x (k + 1) ->
range_addressable (aview segs (w_H W) mem) SHADOW_OFF x (k + 1) ->
shadow_hull_vis (aview segs (w_H W) mem) x (k + 1) ->
(forall a, x + k < a < x + k - (x + k) mod 8 + 8 -> aview segs (w_H W) mem a <> None) ->
aro_unowned segs B (aview segs (w_H W) mem) ->
SRr segs W (cfg_at segs pc regs mem md)
(fun W' c' => W' = W /\ exists regs' mem' md',
c' = cfg_at segs (raZ regs) regs' mem' md' /\
AR segs B ly S W mem' md' /\ aregs_preserved regs regs' /\ same_but_materialized md md' /\
getr regs' 10 = w64 k /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 2 * ESTACK <= a < spZ regs) -> aview segs (w_H W) mem' a = aview segs (w_H W) mem a) /\
(forall a, apresent (w_H W) mem a -> apresent (w_H W) mem' a)).

End c.
End b.
