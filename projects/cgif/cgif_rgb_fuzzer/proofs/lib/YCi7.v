(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YK11 YK0p YK0s YK15 YQ0b YQ08 YI00 YI02.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YI1i YP14 YI08 YI0c.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YG10.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YK05 YA0i YA0l.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YG00 YG0a YG01 YG0h YG0u YG0d YCcz.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YB1u YF9i YCeb YCe8 YCe9 YCi1 YCia.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YCip.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Open Scope Z_scope.
Definition TROUND_STK : Z := 16.
Definition GPB_STK (d : Z) : Z := GP_STK d + TROUND_STK.
Definition TRB_FPC_LO : Z := 0x10300.
Definition TRB_FPC_HI : Z := 0x103b8.
Definition trb_fpc_addr (a : Z) : Prop :=
(0x10300 <= a < 0x10308) \/ (0x10318 <= a < 0x10320) \/ (0x10340 <= a < 0x10348) \/ (0x10368 <= a < 0x10370) \/ (0x10380 <= a < 0x10388).
Definition trb_fp_consts (B : asyms) : Prop :=
forall a, trb_fpc_addr a -> ~ Exists (in_zr a) (as_owned_static B) /\ ~ (as_errno B <= a < as_errno B + 4).
Section c. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Section e.
Variable B : asyms.
Definition tround_spec : Prop :=
forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word),
ajournal trbsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
YK0s.ret_ok (getr regs 1) -> 4096 <= raZ regs ->
spZ regs mod 16 = 0 -> sp0 - STK <= spZ regs - TROUND_STK -> spZ regs <= sp0 ->
frm_zero fp_csr ->
arodata_ok B (aview trbsegs (w_H W) memc) ->
SRr trbsegs W (cfg_at trbsegs A_round regs memc mdc)
(fun W2 c2 => W2 = W /\ exists (fx' : YK11.FPState) regs2 mem2 md2,
c2 = mkCfg (@mkst fx' regs2 (getr regs 1) mem2 (seg_rom trbsegs)) md2 /\ frm_zero (@fp_csr fx') /\
reg_get (@fp_regs fx') 10 = round_bits (reg_get (@fp_regs fx) 10) /\
fregs_preserved (@fp_regs fx) (@fp_regs fx') /\
ajournal trbsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mem2 md2 k /\
aregs_preserved regs regs2 /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - TROUND_STK <= a < spZ regs) -> aview trbsegs (w_H W) mem2 a = aview trbsegs (w_H W) memc a) /\
(forall a, apresent (w_H W) memc a -> apresent (w_H W) mem2 a)).
Definition tgetpal_specB : Prop :=
forall (d : nat) STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word) (t : tree) (pal cid pos : Z),
ajournal trbsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
(tree_height t <= d)%nat -> tree_full t ->
tree_forall tnode_wf t -> tree_forall tnode_means_ok t ->
arodata_ok B (aview trbsegs (w_H W) memc) ->
YK0s.ret_ok (getr regs 1) -> 4096 <= raZ regs ->
getr regs 10 = w64 (troot t) -> getr regs 11 = w64 pal ->
spZ regs mod 16 = 0 -> sp0 - STK <= spZ regs - GPB_STK (Z.of_nat d) -> spZ regs <= sp0 ->
frm_zero fp_csr ->
In (cid, pos) own -> 0 <= cid ->
frame_addr lyc cid pos <= pal -> pal + 768 <= frame_addr lyc cid pos + fs_frame_bytes cid ->
range_addressable (aview trbsegs (w_H W) memc) SHADOW_OFF pal 768 ->
(forall b, In b (tree_blocks t) -> In b (ablocks B lyc Sc)) ->
tree_at trbsegs (mrestrict (w_H W) memc) t ->
SRr trbsegs W (cfg_at trbsegs A_get_palette regs memc mdc)
(fun W2 c2 => W2 = W /\ exists (fx' : YK11.FPState) regs2 mem2 md2,
c2 = mkCfg (@mkst fx' regs2 (getr regs 1) mem2 (seg_rom trbsegs)) md2 /\ frm_zero (@fp_csr fx') /\
ajournal trbsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mem2 md2 k /\
aregs_preserved regs regs2 /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - GPB_STK (Z.of_nat d) <= a < spZ regs) -> ~ (pal <= a < pal + 768) ->
aview trbsegs (w_H W) mem2 a = aview trbsegs (w_H W) memc a) /\
(forall a, apresent (w_H W) memc a -> apresent (w_H W) mem2 a)).
End e.
End c.
