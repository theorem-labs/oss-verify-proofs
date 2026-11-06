(* CARRIED from a working branch 3dd49fa29fa14b99e3c465cacbfe79a09756bb26,
   proofs/omx-clap-core/fuzz_preset/lib/Reusable/YG0d2cf.v, sha256 ff5ffb31b57800a69412b45a2ea1f38a3d3cac88f2f582a2398be52528144d93.
   DO NOT EDIT in this tree: change it on that branch and carry it again. The only change
   made here is the module prefix OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib -> OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib. *)
(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs, 2026-10: the event-free second allocator instance (suffix cf), the REMAINING CALL FORMS
   over ARcf (the first batch, the stack forms and the AR laws are in YG0dcf.v). Statements only.
   Each form is cgif's statement word for word, with ecall_pre -> ecall_pre_cf, AR -> ARcf, and the
   ghost set Hp inserted right after the state S in the binder list and in every ARcf / ecall_pre_cf
   application; every call leaves Hp unchanged.
   Sources: aintrin_realizes (YG0d.v:330-348), amemcmp_realizes (:337-352), abcmp_realizes (:353-372),
   amemchr0_realizes (:384-401), and aset_shadow_realizes in cgif_rgb_fuzzer's YG0e.v:48-59 form.
   dest_ok / src_ok (YG0d.v:324-327) name aowned B ly S, writable_at, aview, spZ and ESTACK, and neither AR
   nor Wf; the cf call forms already use cgif's aowned (YG0dcf.v acall_post_cf). So they are REUSED: the
   cf names below are parse-only abbreviations of cgif's constants, and no Hp enters them.
   first_byte, rom_view, amem_range, shadow_hull_vis, rdword, cfg_at and memop are reused unchanged.
   No address. cgif's YG0d.v and YG0dcf.v are NOT edited. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK11 YK0s YK0i YK15 YK0j YK18 YP09.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05 YGcfNames YG01cf YG00cf YG0ncf YG0dcf.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.

(* dest_ok_cf segs B ly S W regs mem d n IS dest_ok segs B ly S W regs mem d n, and
   src_ok_cf segs W regs mem s n IS src_ok segs W regs mem s n: same constants, same arity. *)
Abbreviation dest_ok_cf := dest_ok (only parsing).
Abbreviation src_ok_cf := src_ok (only parsing).

Section G. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams}.
Section J.
Variable segs : list Segment.
Variable B : asyms.

(* YG0d.v:330-348. *)
Definition aintrin_realizes_cf (op : memop) (pc : Z) : Prop :=
forall ly S Hp W regs mem md d x n,
ecall_pre_cf segs B ly S Hp W regs mem md ->
getr regs 10 = w64 d -> getr regs 11 = w64 x -> getr regs 12 = w64 n -> 0 <= n < 2 ^ 32 -> 0 <= d -> d + n <= 2 ^ 63 ->
dest_ok_cf segs B ly S W regs mem d n -> amem_range d n ->
range_addressable (aview segs (w_H W) mem) SHADOW_OFF d n -> (0 < n -> shadow_hull_vis (aview segs (w_H W) mem) d n) ->
(match op with
| OCpy => 0 <= x /\ x + n <= 2 ^ 63 /\ src_ok_cf segs W regs mem x n /\ (d + n <= x \/ x + n <= d) /\ amem_range x n /\
range_addressable (aview segs (w_H W) mem) SHADOW_OFF x n /\ (0 < n -> shadow_hull_vis (aview segs (w_H W) mem) x n)
| OSet => True end) ->
SRr segs W (cfg_at segs pc regs mem md)
(fun W' c' => W' = W /\ exists regs' mem' md',
c' = cfg_at segs (raZ regs) regs' mem' md' /\
ARcf segs B ly S Hp W mem' md' /\ aregs_preserved regs regs' /\ same_but_materialized md md' /\
getr regs' 10 = w64 d /\
(forall i, 0 <= i < n -> aview segs (w_H W) mem' (d + i) =
match op with OCpy => aview segs (w_H W) mem (x + i) | OSet => Some (x mod 256) end) /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (d <= a < d + n) -> ~ (spZ regs - ESTACK <= a < spZ regs) -> aview segs (w_H W) mem' a = aview segs (w_H W) mem a) /\
(forall a, apresent (w_H W) mem a -> apresent (w_H W) mem' a)).

(* YG0d.v:349-364. *)
Definition amemcmp_realizes_cf (pc : Z) : Prop :=
forall ly S Hp W regs mem md x y n,
ecall_pre_cf segs B ly S Hp W regs mem md ->
getr regs 10 = w64 x -> getr regs 11 = w64 y -> getr regs 12 = w64 n -> 0 <= n < 2 ^ 32 ->
0 <= x -> x + n <= 2 ^ 63 -> 0 <= y -> y + n <= 2 ^ 63 ->
src_ok_cf segs W regs mem x n -> src_ok_cf segs W regs mem y n -> amem_range x n -> amem_range y n ->
range_addressable (aview segs (w_H W) mem) SHADOW_OFF x n -> (0 < n -> shadow_hull_vis (aview segs (w_H W) mem) x n) ->
range_addressable (aview segs (w_H W) mem) SHADOW_OFF y n -> (0 < n -> shadow_hull_vis (aview segs (w_H W) mem) y n) ->
SRr segs W (cfg_at segs pc regs mem md)
(fun W' c' => W' = W /\ exists regs' mem' md' (v : word),
c' = cfg_at segs (raZ regs) regs' mem' md' /\
ARcf segs B ly S Hp W mem' md' /\ aregs_preserved regs regs' /\ same_but_materialized md md' /\
getr regs' 10 = v /\
(v = w64 0 <-> forall i, 0 <= i < n -> aview segs (w_H W) mem (x + i) = aview segs (w_H W) mem (y + i)) /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - ESTACK <= a < spZ regs) -> aview segs (w_H W) mem' a = aview segs (w_H W) mem a) /\
(forall a, apresent (w_H W) mem a -> apresent (w_H W) mem' a)).

(* YG0d.v:365-384. *)
Definition abcmp_realizes_cf (pc : Z) : Prop :=
forall ly S Hp W regs mem md x y n,
ecall_pre_cf segs B ly S Hp W regs mem md ->
ly_stk_lo ly + 2 * ESTACK <= spZ regs -> (forall a, spZ regs - 2 * ESTACK <= a < spZ regs -> apresent (w_H W) mem a) ->
getr regs 10 = w64 x -> getr regs 11 = w64 y -> getr regs 12 = w64 n -> 0 <= n < 2 ^ 32 ->
0 <= x -> x + n <= 2 ^ 63 -> 0 <= y -> y + n <= 2 ^ 63 ->
src_ok_cf segs W regs mem x n -> src_ok_cf segs W regs mem y n ->
(forall a, x <= a < x + n -> ~ (spZ regs - 2 * ESTACK <= a < spZ regs)) ->
(forall a, y <= a < y + n -> ~ (spZ regs - 2 * ESTACK <= a < spZ regs)) ->
amem_range x n -> amem_range y n ->
range_addressable (aview segs (w_H W) mem) SHADOW_OFF x n -> (0 < n -> shadow_hull_vis (aview segs (w_H W) mem) x n) ->
range_addressable (aview segs (w_H W) mem) SHADOW_OFF y n -> (0 < n -> shadow_hull_vis (aview segs (w_H W) mem) y n) ->
SRr segs W (cfg_at segs pc regs mem md)
(fun W' c' => W' = W /\ exists regs' mem' md' (v : word),
c' = cfg_at segs (raZ regs) regs' mem' md' /\
ARcf segs B ly S Hp W mem' md' /\ aregs_preserved regs regs' /\ same_but_materialized md md' /\
getr regs' 10 = v /\
(v = w64 0 <-> forall i, 0 <= i < n -> aview segs (w_H W) mem (x + i) = aview segs (w_H W) mem (y + i)) /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 2 * ESTACK <= a < spZ regs) -> aview segs (w_H W) mem' a = aview segs (w_H W) mem a) /\
(forall a, apresent (w_H W) mem a -> apresent (w_H W) mem' a)).

(* YG0d.v:396-413. *)
Definition amemchr0_realizes_cf (pc : Z) : Prop :=
forall ly S Hp W regs mem md x n k,
ecall_pre_cf segs B ly S Hp W regs mem md ->
getr regs 10 = w64 x -> getr regs 11 = w64 0 -> getr regs 12 = w64 n -> 0 <= n < 2 ^ 63 -> 0 < x ->
0 <= k -> k + 8 <= n -> k + 1 < 2 ^ 32 -> x + k + 1 <= 2 ^ 63 ->
first_byte segs W mem x n 0 k ->
src_ok_cf segs W regs mem x (k + 1) -> amem_range x (k + 1) ->
range_addressable (aview segs (w_H W) mem) SHADOW_OFF x (k + 1) ->
shadow_hull_vis (aview segs (w_H W) mem) x (k + 1) ->
(forall a, x + k < a < x + k - (x + k) mod 8 + 8 -> aview segs (w_H W) mem a <> None) ->
rom_view segs W mem ->
SRr segs W (cfg_at segs pc regs mem md)
(fun W' c' => W' = W /\ exists regs' mem' md',
c' = cfg_at segs (raZ regs) regs' mem' md' /\
ARcf segs B ly S Hp W mem' md' /\ aregs_preserved regs regs' /\ same_but_materialized md md' /\
getr regs' 10 = w64 (x + k) /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - ESTACK <= a < spZ regs) -> aview segs (w_H W) mem' a = aview segs (w_H W) mem a) /\
(forall a, apresent (w_H W) mem a -> apresent (w_H W) mem' a)).

(* cgif_rgb_fuzzer's YG0e.v:48-59 (c8557374ad2e), plus ONE final conjunct: presence never shrinks
   (forall a, apresent (w_H W) mem a -> apresent (w_H W) mem' a), exactly as FCiface.v's aset_shadow_realizes_x
   at d9a884240c6e (mirrored from fuzz_state's SetShadowDef, 5c02ddf4dee). It does not follow from the aview
   clause: on image bytes aview reads the rom, so aview-equality says nothing about presence there. *)
Definition aset_shadow_realizes_cf (pc v : Z) : Prop :=
forall ly S Hp W regs mem md cid pos q n,
ecall_pre_cf segs B ly S Hp W regs mem md -> In (cid, pos) (frames S) ->
getr regs 10 = w64 q -> getr regs 11 = w64 n -> 0 < n ->
shadow_addr (frame_addr ly cid pos) <= q -> q + n <= shadow_addr (frame_addr ly cid pos) + fs_frame_bytes cid / 8 ->
SRr segs W (cfg_at segs pc regs mem md)
(fun W' c' => W' = W /\ exists regs' mem' md',
c' = cfg_at segs (raZ regs) regs' mem' md' /\
ARcf segs B ly S Hp W mem' md' /\ aregs_preserved regs regs' /\ same_but_materialized md md' /\
(forall i, 0 <= i < n -> aview segs (w_H W) mem' (q + i) = Some v) /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (q <= a < q + n) -> aview segs (w_H W) mem' a = aview segs (w_H W) mem a) /\
(forall a, spZ regs - ESTACK <= a < spZ regs -> apresent (w_H W) mem' a) /\
(forall a, apresent (w_H W) mem a -> apresent (w_H W) mem' a)).

End J.
End G.
