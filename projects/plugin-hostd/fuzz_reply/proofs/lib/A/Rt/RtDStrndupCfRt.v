(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* the definitions of fuzz_command's lib/A/Rt/RtDefs.v and
   RtSRegionDef.v (a working branch 8aaeb29ab7b2) that its strndup walk (RtDStrndup{F,R,Z}.v and the top) names,
   with their module paths changed: ascratch_stk, abytes_at and aerrno_cell verbatim; aread_ok, art_post_cf and the
   range check's contract as noted at each. Nothing is proved here. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK11 YK0s YK0i YK15 YK0j YK18 YP09.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05 YGcfNames YG01cf YG00cf YG0ncf YG0dcf.
Import ListNotations.
Open Scope Z_scope.

Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams}.
Section c.
Variable segs : list Segment.
Variable B : asyms.

(* The scratch window of a runtime call: [stk] bytes below the stack pointer at entry. *)
Definition ascratch_stk (stk : Z) (regs : bvmap 5 word) (a : Z) : Prop := spZ regs - stk <= a < spZ regs.

Definition abytes_at (W : world segs) (mem : word -> option byte) (a : Z) (l : list byte) : Prop :=
forall i, (i < length l)%nat -> aview segs (w_H W) mem (a + Z.of_nat i) = Some (bv_unsigned (nth i l (Z_to_bv 8 0))).

(* errno's four bytes *)
Definition aerrno_cell (a : Z) : Prop := as_errno B <= a < as_errno B + 4.

(* The remaining two of command's RtDefs.v that its region-check contract names, with AR -> ARcf (the ghost head
   set Hp threaded) in art_post; aread_ok is unchanged. command's rt_rom_view premise is dropped: the cf strndup
   contract (Reusable/YG0dcf.v astrndup_realizes_cf) has no read-only view of the image, and the walk that discharges
   the range check (RtDStrndupZ.v, fuzz_command's RtSRegion.v relocated) runs on the memory itself, its read-only
   words from the invariant's const cells, so it needs none. *)
Definition aread_ok (stk : Z) (W : world segs) (regs : bvmap 5 word) (mem : word -> option byte) (x n : Z) : Prop :=
0 <= x /\ x + n <= 2 ^ 63 /\ 0 <= n < 2 ^ 32 /\
(forall a, x <= a < x + n -> aview segs (w_H W) mem a <> None /\ ~ ascratch_stk stk regs a) /\
amem_range x n /\
range_addressable (aview segs (w_H W) mem) SHADOW_OFF x n /\
(0 < n -> shadow_hull_vis (aview segs (w_H W) mem) x n).

Definition art_post_cf (stk : Z) (ly : alayout) (S : astate) (Hp : list Z) (W : world segs) (regs : bvmap 5 word)
(mem : word -> option byte) (md : Model) (E : Z -> Prop)
(Q : bvmap 5 word -> (word -> option byte) -> Prop) : world segs -> config -> Prop :=
fun W' c' => W' = W /\ exists regs' mem' md',
c' = cfg_at segs (raZ regs) regs' mem' md' /\
ARcf segs B ly S Hp W mem' md' /\ aregs_preserved regs regs' /\ same_but_materialized md md' /\
Q regs' mem' /\
(forall a, 0 <= a < 2 ^ 64 -> ~ ascratch_stk stk regs a -> ~ E a ->
aview segs (w_H W) mem' a = aview segs (w_H W) mem a) /\
(forall a, apresent (w_H W) mem a -> apresent (w_H W) mem' a) /\
(forall a, ascratch_stk stk regs a -> apresent (w_H W) mem' a) /\
(* the frame on the raw memory (command's art_post states it on the view only): the strndup leaf
   (YG0dcf.v strndup_leaf_cf) states its frame on the raw memory, which the view does not give on image bytes *)
(forall z : word, ~ ascratch_stk stk regs (bv_unsigned z) -> ~ E (bv_unsigned z) -> mem' z = mem z).

(* The ASan range check __asan_region_is_poisoned returning 0 (no poisoned byte), over the cf invariant: command's
   RtSRegionDef.v aregion_zero_at / aregion_zero_stk with AR -> ARcf, without rt_rom_view (above). RtDStrndupZ.v
   proves it (reply_region_zero_stk_cf), by fuzz_command's RtSRegion.v walk relocated to this image. *)
Definition RGN_SCR : Z := 72.
(* __asan_region_is_poisoned of fuzz_reply.asan (AB1w.v tfib_A_asan_region_is_poisoned; command's RtAPI.v names it
   PC_region_is_poisoned at its own image's 0x5a1ac) *)
Definition PC_region_is_poisoned : Z := 0x5595c.

Definition aregion_zero_at_cf (stk pc : Z) : Prop :=
forall ly S Hp W regs mem md x n,
ARcf segs B ly S Hp W mem md ->
YK0s.ret_ok (getr regs 1) ->
spZ regs mod 16 = 0 -> ly_stk_lo ly + stk <= spZ regs -> spZ regs <= ly_stk_hi ly ->
(forall a, spZ regs - stk <= a < spZ regs -> apresent (w_H W) mem a) ->
getr regs 10 = w64 x -> getr regs 11 = w64 n -> 64 < n < 2 ^ 32 -> 0 < x ->
aread_ok stk W regs mem x n ->
SRr segs W (cfg_at segs pc regs mem md)
(art_post_cf stk ly S Hp W regs mem md (fun _ => False) (fun regs' _ => getr regs' 10 = w64 0)).

Definition aregion_zero_stk_cf (pc : Z) : Prop := forall stk, RGN_SCR <= stk -> aregion_zero_at_cf stk pc.

End c.
End b.
