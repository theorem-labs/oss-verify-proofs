(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: only the contract of the shadow-fill entries (__asan_set_shadow_XX): proofs/cgif/cgif_rgb_fuzzer/lib/YG0e.v:48-61@c8557374ad2e (aset_shadow_realizes) restated over the asan-state definitions of the cgif_file_fuzzer proof as omx-clap-core/fuzz_state holds them, as libreac/fuzz_grant did (a working branch a1ee3c81405 lib/A/Rt/SetShadowDef.v); module names. *)
(* Modified by Theorem Labs, 2026-10: the frame clause exempts the callee's own stack window [sp - ESTACK, sp), as aintrin_realizesU / apoison16 do (a Theorem Labs lane's R1 audit; a shadow-fill path that spills keeps the contract); the post keeps presence monotone over all memory (last conjunct), as FSupoisonU.aintrin_realizesU does. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YK11 YK0s YK0i YK15 YK0j YK18 YP09.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YM05.
Import ListNotations.
Open Scope Z_scope.
Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Section c.
Variable segs : list Segment.
Variable B : asyms.
(* The strict form (the released cgif_rgb YG0e.v:48 text): no write outside [q, q + n). *)
Definition aset_shadow_realizes_strict (pc v : Z) : Prop :=
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
(* The shared form: the callee's own stack window [sp - ESTACK, sp) is exempt from the frame clause, as in aintrin_realizesU / apoison16. *)
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
(forall a, 0 <= a < 2 ^ 64 -> ~ (q <= a < q + n) -> ~ (spZ regs - ESTACK <= a < spZ regs) -> aview segs (w_H W) mem' a = aview segs (w_H W) mem a) /\
(forall a, spZ regs - ESTACK <= a < spZ regs -> apresent (w_H W) mem' a) /\
(forall a, apresent (w_H W) mem a -> apresent (w_H W) mem' a)).

Lemma aset_shadow_realizes_of_strict : forall pc v, aset_shadow_realizes_strict pc v -> aset_shadow_realizes pc v.
Proof.
intros pc v H ly S W regs mem md cid pos q n Hpre Hin G10 G11 Hn Hq1 Hq2.
eapply SRr_mono; [exact (H ly S W regs mem md cid pos q n Hpre Hin G10 G11 Hn Hq1 Hq2)|].
intros W' c' _ (EW & regs' & mem' & md' & Ec & HI & Hr & Hs & Hv & Hout & Hp & Hm). split; [exact EW|].
exists regs', mem', md'. repeat (split; [eassumption|]). split; [intros a Ha Hq _; exact (Hout a Ha Hq)|exact (conj Hp Hm)].
Qed.

End c.
End b.