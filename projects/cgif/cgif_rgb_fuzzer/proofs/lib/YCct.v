(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YK11 YK0s YK15 YQ0b YI00 YI02.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YI1i YI08 YI0c.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YG10.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YK05 YA0i YA0l.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YG00 YG0a YG01 YG0h YG0u YG0d YC04.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YB0z YF8z YC1d YC1a YC1b YC4u.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Export YCcx.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Open Scope Z_scope.
Definition A_rread_frameconfig : Z := 0x815ac.
Definition TRRFC_STK : Z := 128 + ASTACK.
Definition EV_RRFC : Z := 2.
Definition LIVE_RRFC : Z := 4 * RGB_NMAX.
Section d. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Section e.
Variable B : asyms.
Definition trrfc_spec : Prop :=
forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word) (Bb : list (Z * Z))
(st dst N pdata nb cur : Z) (cid pos : Z),
ajournal trasegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
(forall b, In b (ablocks B ly S) -> In b Bb) -> Permutation (ablocks B lyc Sc) Bb -> In (pdata, nb) Bb ->
YK0s.ret_ok (getr regs 1) -> 4096 <= raZ regs ->
getr regs 3 = w64 (as_gp B) -> getr regs 4 = w64 (as_tp B) ->
getr regs 10 = w64 st -> getr regs 11 = w64 dst -> getr regs 12 = w64 N ->
spZ regs mod 16 = 0 -> sp0 - STK <= spZ regs - TRRFC_STK -> spZ regs <= sp0 ->
In (cid, pos) own -> 0 <= cid -> frame_addr lyc cid pos mod 8 = 0 ->
frame_addr lyc cid pos <= dst -> dst + RGBFC_SIZE <= frame_addr lyc cid pos + fs_frame_bytes cid -> dst mod 8 = 0 ->
spZ regs <= st -> st + 24 <= sp0 -> st mod 8 = 0 ->
range_addressable (aview trasegs (w_H W) memc) SHADOW_OFF st 24 ->
range_addressable (aview trasegs (w_H W) memc) SHADOW_OFF dst RGBFC_SIZE ->
1 <= N <= RGB_NMAX -> 0 <= cur <= nb -> 0 < nb ->
val_mem trasegs (mrestrict (w_H W) memc) st 8 pdata -> val_mem trasegs (mrestrict (w_H W) memc) (st + 8) 8 nb ->
val_mem trasegs (mrestrict (w_H W) memc) (st + 16) 8 cur ->
rrfc_universe B nb ->
vev Sc + EV_RRFC <= VEV_MAX   -> blocks_bytes Sc + LIVE_RRFC <= LIVE_MAX ->
SRr trasegs W (cfg_at trasegs A_rread_frameconfig regs memc mdc)
(fun W2 c2 => exists ly2 S2 regs2 mem2 md2 (res cur2 : Z),
c2 = mkCfg (mkst regs2 (getr regs 1) mem2 (seg_rom trasegs)) md2 /\
ajournal trasegs B STK sp0 FP ly S W0 mem0 md0 own ly2 S2 W2 mem2 md2 (k + EV_RRFC) /\
aregs_preserved regs regs2 /\ frames S2 = frames Sc /\
jbud Sc S2 EV_RRFC /\
getr regs2 10 = w64 res /\
(forall a, alloc_ceiling <= a < 2 ^ 64 ->
~ (spZ regs - TRRFC_STK <= a < spZ regs) -> ~ (dst <= a < dst + RGBFC_SIZE) -> ~ (st + 16 <= a < st + 24) ->
aview trasegs (w_H W2) mem2 a = aview trasegs (w_H W) memc a) /\
(forall b m i, In (b, m) Bb -> 0 <= i < req_size m -> aview trasegs (w_H W2) mem2 (b + i) = aview trasegs (w_H W) memc (b + i)) /\
(forall c p a, In (c, p) (frames Sc) ->
(in_zr a (frame_rng lyc (c, p)) \/ in_zr a (shadow_addr (frame_addr lyc c p), fs_frame_bytes c / 8)) ->
~ (dst <= a < dst + RGBFC_SIZE) -> ~ (st + 16 <= a < st + 24) ->
aview trasegs (w_H W2) mem2 a = aview trasegs (w_H W) memc a) /\
val_mem trasegs (mrestrict (w_H W2) mem2) st 8 pdata /\ val_mem trasegs (mrestrict (w_H W2) mem2) (st + 8) 8 nb /\
val_mem trasegs (mrestrict (w_H W2) mem2) (st + 16) 8 cur2 /\ cur <= cur2 <= nb /\
((res = 2 ^ 64 - 1 /\ Permutation (ablocks B ly2 S2) Bb /\
exists fattr fgen delay, obj_at trasegs (mrestrict (w_H W2) mem2) dst LAY_RgbFrameConfig [0; 0; fattr; fgen; delay]) \/
(res = 0 /\ Permutation (ablocks B ly2 S2) Bb) \/
(res = 1 /\ exists img fmt fattr fgen delay, (fmt = 3 \/ fmt = 4) /\
obj_at trasegs (mrestrict (w_H W2) mem2) dst LAY_RgbFrameConfig [img; fmt; fattr; fgen; delay] /\
Permutation (ablocks B ly2 S2) ((img, fmt * N) :: Bb) /\
aftok FP (ablocks B ly S) (img, fmt * N) /\
forall blc i, In (img, fmt * N) blc -> 0 <= i < req_size (fmt * N) ->
awr_byte STK sp0 FP (ablocks B ly S) blc ly2 own (img + i)))).
End e.
End d.
