(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: ported from proofs/cgif/cgif_file_fuzzer/lib/A/ACey.v lines 190-246 (rfc_post, trfc_specX) in the Section form of lib/YC7y.v lines 4-18, 26-32 and 69-113 at c8557374ad2e to libreac/fuzz_knock: rfc_post -> kn_post_init / kn_post_heard / kn_post_step, trfc_specX -> tknock_init_specX / tknock_heard_specX / tknock_step_specX, tfibsegs -> the Section variable segs, A_read_frameconfig -> the parameter a, LAY_FrameConfig -> LAY_Knock, the parse_frameN result -> knock_step_f (reac_knock_step_c.v lines 11-18 restated over Z), the 32-byte destination dst -> the 40-byte struct kp in the caller's frame, written through awr_byte's in_frames case by In (cid, pos) own for any frame class cid (knock's harness frame is class 1), its addressability carried by afobj (APgBase.v) and kp <> 0; the stack struct st, the heap blocks Bb, the CTX_read_frameconfig premise and the malloc budget are dropped, because knock's three callees allocate nothing and call only the memset intrinsic; TRFC_STK = 112 + ASTACK -> T_init_STK = 48 + ESTACK (addi sp,sp,-48 at 0x7f44c), T_heard_STK = 16 (addi sp,sp,-16 at 0x7f4e8), T_step_STK = 16 (addi sp,sp,-16 at 0x7f570); EV_RFC = 6 -> EV_init = EV_heard = EV_step = 0; RFC_COST MT N -> 0 in mo_le; the file states no image-end or RELRO address. *)
From OSSVerify.Proofs.libreac.fuzz_knock.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_knock.lib.Reusable Require Import YK11 YK14 YK0s YK15 YP09 YI04 YI08 YN3v YI00 YI0m YI09.
From OSSVerify.Proofs.libreac.fuzz_knock.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_knock.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.libreac.fuzz_knock.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.libreac.fuzz_knock.lib.A Require Import APgBase.
From OSSVerify.Proofs.libreac.fuzz_knock.lib.Reusable Require Import YM05.
Import ListNotations.
Local Open Scope Z_scope.
Definition LAY_Knock : layout_t := [(0, 4%N); (4, 4%N); (8, 8%N); (16, 8%N); (24, 8%N); (32, 4%N); (36, 4%N)].
Definition L_NS : Z := 500000000.
Definition T_init_STK : Z := 48 + ESTACK.
Definition T_heard_STK : Z := 16.
Definition T_step_STK : Z := 16.
Definition EV_init : Z := 0.
Definition EV_heard : Z := 0.
Definition EV_step : Z := 0.
Definition knock_step_f (st g due heard t : Z) : Z * Z * Z * Z :=
if Z.eqb st 2 then
if (t <=? heard) || (t - heard <? L_NS) then (0, st, due, g) else (1, 1, (heard + L_NS) mod 2 ^ 64, 1)
else if Z.eqb st 0 then
if t <? due then (0, st, due, g) else (1, 1, due, 1)
else (0, st, due, g).
Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section c.
Variable segs : list Segment.
Section d.
Variable B : asyms.
Variable MT : ameter_ops.
Definition kn_post_init (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate) (W0 : world segs)
(mem0 : word -> option byte) (md0 : Model) (own : list (Z * Z)) (k : Z) (regs : bvmap 5 word) (kp now : Z)
(lyc : alayout) (Sc : astate) (W : world segs) (memc : word -> option byte) (mdc : Model)
: world segs -> config -> Prop :=
fun W2 c2 => exists ly2 S2 regs2 mem2 md2,
c2 = mkCfg (mkst regs2 (getr regs 1) mem2 (seg_rom segs)) md2 /\
ajournal segs B STK sp0 FP ly S W0 mem0 md0 own ly2 S2 W2 mem2 md2 (k + EV_init) /\
aregs_preserved regs regs2 /\ frames S2 = frames Sc /\
Permutation (ablocks B ly2 S2) (ablocks B lyc Sc) /\ same_io mdc md2 /\ mo_le MT Sc S2 0 /\
(forall a, alloc_ceiling <= a < 2 ^ 64 ->
~ (spZ regs - T_init_STK <= a < spZ regs) -> ~ (kp <= a < kp + 40) ->
aview segs (w_H W2) mem2 a = aview segs (w_H W) memc a) /\
(forall b m i, In (b, m) (ablocks B lyc Sc) -> 0 <= i < req_size m ->
aview segs (w_H W2) mem2 (b + i) = aview segs (w_H W) memc (b + i)) /\
(forall c p a, In (c, p) (frames Sc) ->
(in_zr a (frame_rng lyc (c, p)) \/ in_zr a (shadow_addr (frame_addr lyc c p), fs_frame_bytes c / 8)) ->
~ (kp <= a < kp + 40) ->
aview segs (w_H W2) mem2 a = aview segs (w_H W) memc a) /\
(forall a, in_img segs a -> ~ Exists (in_zr a) (as_owned_static B) ->
~ (as_errno B <= a < as_errno B + 4) ->
aview segs (w_H W2) mem2 a = aview segs (w_H W) memc a) /\
obj_at segs (mrestrict (w_H W2) mem2) kp LAY_Knock [0; 0; now; (now + L_NS) mod 2 ^ 64; 0; 0; 0].
Definition tknock_init_specX (a : Z) : Prop :=
forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word)
(kp now : Z) (cid pos : Z) ch,
ajournal segs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
YK0s.ret_ok (getr regs 1) -> 4096 <= raZ regs ->
getr regs 3 = w64 (as_gp B) -> getr regs 4 = w64 (as_tp B) ->
getr regs 10 = w64 kp -> getr regs 11 = w64 now -> 0 <= now < 2 ^ 64 ->
achain lyc (aview segs (w_H W) memc) (spZ regs) (s0Z regs) ch ->
spZ regs mod 16 = 0 -> sp0 - STK <= spZ regs - T_init_STK -> spZ regs <= sp0 ->
In (cid, pos) own -> 0 <= cid -> frame_addr lyc cid pos mod 8 = 0 ->
frame_addr lyc cid pos <= kp -> kp + 40 <= frame_addr lyc cid pos + fs_frame_bytes cid ->
kp mod 8 = 0 -> kp <> 0 ->
(spZ regs <= kp \/ kp + 40 <= spZ regs - T_init_STK) ->
afobj segs B lyc Sc W memc kp 40 ->
st_nev S + k + EV_init <= EV_MAX ->
SRr segs W (cfg_at segs a regs memc mdc)
(kn_post_init STK sp0 FP ly S W0 mem0 md0 own k regs kp now lyc Sc W memc mdc).
Definition kn_post_heard (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate) (W0 : world segs)
(mem0 : word -> option byte) (md0 : Model) (own : list (Z * Z)) (k : Z) (regs : bvmap 5 word) (kp now : Z)
(st p1 opened due heard g p2 : Z)
(lyc : alayout) (Sc : astate) (W : world segs) (memc : word -> option byte) (mdc : Model)
: world segs -> config -> Prop :=
fun W2 c2 => exists ly2 S2 regs2 mem2 md2,
c2 = mkCfg (mkst regs2 (getr regs 1) mem2 (seg_rom segs)) md2 /\
ajournal segs B STK sp0 FP ly S W0 mem0 md0 own ly2 S2 W2 mem2 md2 (k + EV_heard) /\
aregs_preserved regs regs2 /\ frames S2 = frames Sc /\
Permutation (ablocks B ly2 S2) (ablocks B lyc Sc) /\ same_io mdc md2 /\ mo_le MT Sc S2 0 /\
(forall a, alloc_ceiling <= a < 2 ^ 64 ->
~ (spZ regs - T_heard_STK <= a < spZ regs) -> ~ (kp <= a < kp + 40) ->
aview segs (w_H W2) mem2 a = aview segs (w_H W) memc a) /\
(forall b m i, In (b, m) (ablocks B lyc Sc) -> 0 <= i < req_size m ->
aview segs (w_H W2) mem2 (b + i) = aview segs (w_H W) memc (b + i)) /\
(forall c p a, In (c, p) (frames Sc) ->
(in_zr a (frame_rng lyc (c, p)) \/ in_zr a (shadow_addr (frame_addr lyc c p), fs_frame_bytes c / 8)) ->
~ (kp <= a < kp + 40) ->
aview segs (w_H W2) mem2 a = aview segs (w_H W) memc a) /\
(forall a, in_img segs a -> ~ Exists (in_zr a) (as_owned_static B) ->
~ (as_errno B <= a < as_errno B + 4) ->
aview segs (w_H W2) mem2 a = aview segs (w_H W) memc a) /\
obj_at segs (mrestrict (w_H W2) mem2) kp LAY_Knock [if st =? 0 then 2 else st; p1; opened; due; now; g; p2].
Definition tknock_heard_specX (a : Z) : Prop :=
forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word)
(kp now : Z) (cid pos : Z) ch (st p1 opened due heard g p2 : Z),
ajournal segs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
YK0s.ret_ok (getr regs 1) -> 4096 <= raZ regs ->
getr regs 3 = w64 (as_gp B) -> getr regs 4 = w64 (as_tp B) ->
getr regs 10 = w64 kp -> getr regs 11 = w64 now -> 0 <= now < 2 ^ 64 ->
achain lyc (aview segs (w_H W) memc) (spZ regs) (s0Z regs) ch ->
spZ regs mod 16 = 0 -> sp0 - STK <= spZ regs - T_heard_STK -> spZ regs <= sp0 ->
In (cid, pos) own -> 0 <= cid -> frame_addr lyc cid pos mod 8 = 0 ->
frame_addr lyc cid pos <= kp -> kp + 40 <= frame_addr lyc cid pos + fs_frame_bytes cid ->
kp mod 8 = 0 -> kp <> 0 ->
(spZ regs <= kp \/ kp + 40 <= spZ regs - T_heard_STK) ->
afobj segs B lyc Sc W memc kp 40 ->
obj_at segs (mrestrict (w_H W) memc) kp LAY_Knock [st; p1; opened; due; heard; g; p2] ->
st_nev S + k + EV_heard <= EV_MAX ->
SRr segs W (cfg_at segs a regs memc mdc)
(kn_post_heard STK sp0 FP ly S W0 mem0 md0 own k regs kp now st p1 opened due heard g p2 lyc Sc W memc mdc).
Definition kn_post_step (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate) (W0 : world segs)
(mem0 : word -> option byte) (md0 : Model) (own : list (Z * Z)) (k : Z) (regs : bvmap 5 word) (kp now : Z)
(st p1 opened due heard g p2 : Z)
(lyc : alayout) (Sc : astate) (W : world segs) (memc : word -> option byte) (mdc : Model)
: world segs -> config -> Prop :=
fun W2 c2 => exists ly2 S2 regs2 mem2 md2,
c2 = mkCfg (mkst regs2 (getr regs 1) mem2 (seg_rom segs)) md2 /\
ajournal segs B STK sp0 FP ly S W0 mem0 md0 own ly2 S2 W2 mem2 md2 (k + EV_step) /\
aregs_preserved regs regs2 /\ frames S2 = frames Sc /\
Permutation (ablocks B ly2 S2) (ablocks B lyc Sc) /\ same_io mdc md2 /\ mo_le MT Sc S2 0 /\
(forall a, alloc_ceiling <= a < 2 ^ 64 ->
~ (spZ regs - T_step_STK <= a < spZ regs) -> ~ (kp <= a < kp + 40) ->
aview segs (w_H W2) mem2 a = aview segs (w_H W) memc a) /\
(forall b m i, In (b, m) (ablocks B lyc Sc) -> 0 <= i < req_size m ->
aview segs (w_H W2) mem2 (b + i) = aview segs (w_H W) memc (b + i)) /\
(forall c p a, In (c, p) (frames Sc) ->
(in_zr a (frame_rng lyc (c, p)) \/ in_zr a (shadow_addr (frame_addr lyc c p), fs_frame_bytes c / 8)) ->
~ (kp <= a < kp + 40) ->
aview segs (w_H W2) mem2 a = aview segs (w_H W) memc a) /\
(forall a, in_img segs a -> ~ Exists (in_zr a) (as_owned_static B) ->
~ (as_errno B <= a < as_errno B + 4) ->
aview segs (w_H W2) mem2 a = aview segs (w_H W) memc a) /\
let '(r, st', due', g') := knock_step_f st g due heard now in
getr regs2 10 = w64 r /\
obj_at segs (mrestrict (w_H W2) mem2) kp LAY_Knock [st'; p1; opened; due'; heard; g'; p2].
Definition tknock_step_specX (a : Z) : Prop :=
forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word)
(kp now : Z) (cid pos : Z) ch (st p1 opened due heard g p2 : Z),
ajournal segs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
YK0s.ret_ok (getr regs 1) -> 4096 <= raZ regs ->
getr regs 3 = w64 (as_gp B) -> getr regs 4 = w64 (as_tp B) ->
getr regs 10 = w64 kp -> getr regs 11 = w64 now -> 0 <= now < 2 ^ 64 ->
achain lyc (aview segs (w_H W) memc) (spZ regs) (s0Z regs) ch ->
spZ regs mod 16 = 0 -> sp0 - STK <= spZ regs - T_step_STK -> spZ regs <= sp0 ->
In (cid, pos) own -> 0 <= cid -> frame_addr lyc cid pos mod 8 = 0 ->
frame_addr lyc cid pos <= kp -> kp + 40 <= frame_addr lyc cid pos + fs_frame_bytes cid ->
kp mod 8 = 0 -> kp <> 0 ->
(spZ regs <= kp \/ kp + 40 <= spZ regs - T_step_STK) ->
afobj segs B lyc Sc W memc kp 40 ->
obj_at segs (mrestrict (w_H W) memc) kp LAY_Knock [st; p1; opened; due; heard; g; p2] ->
st_nev S + k + EV_step <= EV_MAX ->
SRr segs W (cfg_at segs a regs memc mdc)
(kn_post_step STK sp0 FP ly S W0 mem0 md0 own k regs kp now st p1 opened due heard g p2 lyc Sc W memc mdc).
End d.
End c.
End b.
