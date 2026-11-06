(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs, 2026-10: the window-exempt set_shadow contract over the frame-area interface, image-free.
   FCiface.aset_shadow_realizes_x is the STRICT form (cgif_rgb YG0e.v:48: no byte outside [q, q + n) changes).
   aset_shadow_realizes_xw below exempts the callee's own stack window [sp - ESTACK, sp) from that frame clause, as
   fuzz_state's SetShadowDefU.aset_shadow_realizesU does (10ffef27396). The strict form implies the exempt one
   (aset_shadow_realizes_xw_of_x); the converse does not hold, so the strict form is the statement of record and a
   consumer that cites the exempt form takes it through this corollary. Both forms end with the presence-growth
   conjunct `forall a, apresent (w_H W) mem a -> apresent (w_H W) mem' a` (see FCiface.v's header for why it is a
   separate conjunct: it cannot be derived from the aview clause, because apresent_transfer needs `~ in_img a`).
   No address and no image numeral appears in this file. *)
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YK11 YK0s YK0i YK15 YK0j YK18 YP09.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YM05 FCiface.
Import ListNotations.
Local Open Scope Z_scope.
Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Section b.
Variable segs : list Segment.
Variable B : asyms.
Variable ARx : alayout -> astate -> list Z -> world segs -> (word -> option byte) -> Model -> Prop.

Definition aset_shadow_realizes_xw (pc v : Z) : Prop :=
forall ly S Hp W regs mem md cid pos q n,
ecall_pre_x segs B ARx ly S Hp W regs mem md -> In (cid, pos) (frames S) ->
getr regs 10 = w64 q -> getr regs 11 = w64 n -> 0 < n ->
shadow_addr (frame_addr ly cid pos) <= q -> q + n <= shadow_addr (frame_addr ly cid pos) + fs_frame_bytes cid / 8 ->
SRr segs W (cfg_at segs pc regs mem md)
(fun W' c' => W' = W /\ exists regs' mem' md',
c' = cfg_at segs (raZ regs) regs' mem' md' /\
ARx ly S Hp W mem' md' /\ aregs_preserved regs regs' /\ same_but_materialized md md' /\
(forall i, 0 <= i < n -> aview segs (w_H W) mem' (q + i) = Some v) /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (q <= a < q + n) -> ~ (spZ regs - ESTACK <= a < spZ regs) ->
aview segs (w_H W) mem' a = aview segs (w_H W) mem a) /\
(forall a, spZ regs - ESTACK <= a < spZ regs -> apresent (w_H W) mem' a) /\
(forall a, apresent (w_H W) mem a -> apresent (w_H W) mem' a)).

Lemma aset_shadow_realizes_xw_of_x : forall pc v,
aset_shadow_realizes_x segs B ARx pc v -> aset_shadow_realizes_xw pc v.
Proof.
intros pc v H ly S Hp W regs mem md cid pos q n Hpre Hin G10 G11 Hn Hq1 Hq2.
eapply SRr_mono; [exact (H ly S Hp W regs mem md cid pos q n Hpre Hin G10 G11 Hn Hq1 Hq2)|].
intros W' c' _ (EW & regs' & mem' & md' & Ec & HI & Hr & Hs & Hv & Hout & Hp' & Hg). split; [exact EW|].
exists regs', mem', md'. repeat (split; [eassumption|]). split; [intros a Ha Hq _; exact (Hout a Ha Hq) | split; [exact Hp' | exact Hg]].
Qed.
End b.
End a.
