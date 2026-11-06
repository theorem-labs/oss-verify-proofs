(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: only the contract of the stack-frame release entry (astack_free_realizes of proofs/cgif/cgif_rgb_fuzzer/lib/YG0e.v), restated over the asan-state definitions of the cgif_file_fuzzer proof as libreac/fuzz_grant holds them; module names. One change: the shadow span the entry marks released is sf_span cid n, not n / 8. For class cid <= 6 the span is the frame's whole shadow, fs_frame_bytes cid / 8 bytes, for any size argument n; for a higher class it is n / 8 bytes, as cgif_rgb_fuzzer states it. *)
(* Modified by Theorem Labs, 2026-10: taken by path into libreac/fuzz_ctrl from libreac/fuzz_grant (a working branch c3bfa00452c, the shared text of record); only the module prefix fuzz_grant -> fuzz_ctrl changed. *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require Import YK11 YK0s YK0i YK15 YK0j YK18 YP09.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require Import YM05.
Import ListNotations.
Open Scope Z_scope.
Definition sf_span (cid n : Z) : Z := if cid <=? 6 then fs_frame_bytes cid / 8 else n / 8.
Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Section c.
Variable segs : list Segment.
Variable B : asyms.
Definition astack_free_realizes (pc cid : Z) : Prop :=
forall ly S W regs mem md pos n,
ecall_pre segs B ly S W regs mem md -> In (cid, pos) (frames S) ->
getr regs 10 = w64 (frame_addr ly cid pos) -> getr regs 11 = w64 n -> 8 <= n <= fs_frame_bytes cid -> n mod 8 = 0 ->
rdword (aview segs (w_H W) mem) (frame_addr ly cid pos + fs_frame_bytes cid - 8) = Some (flag_addr ly cid pos) ->
SRr segs W (cfg_at segs pc regs mem md)
(fun W' c' => W' = W /\ exists regs' mem' md',
c' = cfg_at segs (raZ regs) regs' mem' md' /\
AR segs B ly (stack_free_state cid pos S) W mem' md' /\ aregs_preserved regs regs' /\ same_but_materialized md md' /\
(forall i, 0 <= i < sf_span cid n -> aview segs (w_H W) mem' (shadow_addr (frame_addr ly cid pos) + i) = Some 0xf5) /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (shadow_addr (frame_addr ly cid pos) <= a < shadow_addr (frame_addr ly cid pos) + sf_span cid n) ->
a <> flag_addr ly cid pos -> ~ (spZ regs - ESTACK <= a < spZ regs) ->
aview segs (w_H W) mem' a = aview segs (w_H W) mem a) /\
(forall a, spZ regs - ESTACK <= a < spZ regs -> apresent (w_H W) mem' a)).
End c.
End b.
