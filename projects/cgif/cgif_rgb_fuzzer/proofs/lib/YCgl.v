(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YK11 YK0s YK15 YQ0b YI00.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YK05 YA0i YA0l.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YG00 YG0a YG01 YG0h YG0u YG0d YCcz.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YB1u YF9i YCeb YCe8.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Open Scope Z_scope.
Section c. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Definition A_LZW : Z := 0x8a454.
Definition LZW_TSTK : Z := 304 + ASTACK.
Definition LZW_EV : Z := 19.
Section d.
Variable B : asyms.
Definition tlzw_kept (lyc : alayout) (Sc : astate) (W : world trbsegs) (memc : word -> option byte)
(W2 : world trbsegs) (mem2 : word -> option byte) (sp pR : Z) (E : Z -> Prop) : Prop :=
(forall a, alloc_ceiling <= a < 2 ^ 64 -> ~ (sp - LZW_TSTK <= a < sp) -> ~ (pR <= a < pR + 12) ->
aview trbsegs (w_H W2) mem2 a = aview trbsegs (w_H W) memc a) /\
(forall b m i, In (b, m) (ablocks B lyc Sc) -> 0 <= i < req_size m -> ~ E (b + i) ->
aview trbsegs (w_H W2) mem2 (b + i) = aview trbsegs (w_H W) memc (b + i)) /\
(forall a, in_img trbsegs a -> ~ Exists (in_zr a) (as_owned_static B) -> ~ (as_errno B <= a < as_errno B + 4) ->
aview trbsegs (w_H W2) mem2 a = aview trbsegs (w_H W) memc a) /\
(forall cid pos a, In (cid, pos) (frames Sc) ->
(in_zr a (frame_rng lyc (cid, pos)) \/ in_zr a (shadow_addr (frame_addr lyc cid pos), fs_frame_bytes cid / 8)) ->
~ (pR <= a < pR + 12) -> aview trbsegs (w_H W2) mem2 a = aview trbsegs (w_H W) memc a) /\
(forall a, alloc_ceiling <= a < 2 ^ 64 -> ~ (sp - LZW_TSTK <= a < sp) -> apresent (w_H W) memc a -> apresent (w_H W2) mem2 a) /\
(forall a, sp - LZW_TSTK <= a < sp -> apresent (w_H W2) mem2 a).
Definition tlzw_pR_ok (lyc : alayout) (Sc : astate) (W : world trbsegs) (memc : word -> option byte) (pR : Z) : Prop :=
(exists cid pos, In (cid, pos) (frames Sc) /\ (forall a, pR <= a < pR + 16 -> in_zr a (frame_rng lyc (cid, pos))) /\
aview trbsegs (w_H W) memc (shadow_addr pR) = Some 0 /\ aview trbsegs (w_H W) memc (shadow_addr pR + 1) = Some 0)
\/ (ly_stk_lo lyc <= pR /\ pR + 16 <= ly_stk_hi lyc).
Definition tlzw_post (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate) (W0 : world trbsegs)
(mem0 : word -> option byte) (md0 : Model) (own : list (Z * Z))
(lyc : alayout) (Sc : astate) (W : world trbsegs) (memc : word -> option byte) (k : Z)
(regs : bvmap 5 word) (pR : Z) : world trbsegs -> config -> Prop :=
fun W2 c2 => exists ly2 S2 regs2 mem2 md2 (res : Z),
c2 = mkCfg (mkst regs2 (getr regs 1) mem2 (seg_rom trbsegs)) md2 /\
ajournal trbsegs B STK sp0 FP ly S W0 mem0 md0 own ly2 S2 W2 mem2 md2 (k + LZW_EV) /\
aregs_preserved regs regs2 /\ getr regs2 10 = w64 res /\ frames S2 = frames Sc /\
((res = 0 /\
exists bb Lbb M,
Permutation (ablocks B ly2 S2) ((bb, Lbb) :: ablocks B lyc Sc) /\ 4096 <= bb /\ 1 <= M <= Lbb /\
(forall blc i, In (bb, Lbb) blc -> 0 <= i < Lbb -> awr_byte STK sp0 FP (ablocks B ly S) blc ly2 own (bb + i)) /\
aftok FP (ablocks B ly S) (bb, Lbb) /\
val_mem trbsegs (mrestrict (w_H W2) mem2) pR 8 bb /\ val_mem trbsegs (mrestrict (w_H W2) mem2) (pR + 8) 4 M /\
tlzw_kept lyc Sc W memc W2 mem2 (spZ regs) pR (fun a => bb <= a < bb + req_size Lbb))
\/ ((res = 2 \/ res = 5) /\
Permutation (ablocks B ly2 S2) (ablocks B lyc Sc) /\
tlzw_kept lyc Sc W memc W2 mem2 (spZ regs) pR (fun _ => False) /\
(forall a, pR <= a < pR + 12 -> aview trbsegs (w_H W2) mem2 a = aview trbsegs (w_H W) memc a))).
Definition tlzw_spec : Prop :=
forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word) (pR nP img idl icl bi Li : Z) ch,
ajournal trbsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
arodata_ok B (aview trbsegs (w_H W) memc) ->
YK0s.ret_ok (getr regs 1) -> 4096 <= raZ regs ->
getr regs 3 = w64 (as_gp B) -> getr regs 4 = w64 (as_tp B) ->
getr regs 10 = w64 pR -> getr regs 11 = w64 nP -> getr regs 12 = w64 img ->
getr regs 13 = w64 idl -> getr regs 14 = w64 icl ->
achain lyc (aview trbsegs (w_H W) memc) (spZ regs) (s0Z regs) ch -> In (raZ regs :: spine ch) CTX_LZW_GenerateStream ->
spZ regs mod 16 = 0 -> sp0 - STK <= spZ regs - LZW_TSTK -> spZ regs <= sp0 ->
pR mod 8 = 0 -> (spZ regs <= pR \/ pR + 16 <= spZ regs - LZW_TSTK) -> 0 <= pR -> pR + 16 <= 2 ^ 63 ->
(forall a, pR <= a < pR + 16 -> awr_byte STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own a /\
apresent (w_H W) memc a) ->
tlzw_pR_ok lyc Sc W memc pR ->
1 <= nP <= 100000000 -> 2 <= idl <= 256 -> 0 <= icl <= 12 ->
In (bi, Li) (ablocks B lyc Sc) -> bi <= img -> img + nP <= bi + req_size Li ->
vev Sc + LZW_EV <= VEV_MAX -> blocks_bytes Sc + 2 ^ 29 <= LIVE_MAX ->
SRr trbsegs W (cfg_at trbsegs A_LZW regs memc mdc)
(tlzw_post STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs pR).
End d.
End c.
