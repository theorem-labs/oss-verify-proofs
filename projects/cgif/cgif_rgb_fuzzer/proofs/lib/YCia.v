(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YK11 YK0p YK0s YK15 YQ0b YI00 YI02.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YI1i YP14 YI08 YI0c.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YG10.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YK05 YA0i YA0l.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YG00 YG0a YG01 YG0h YG0u YG0d YCcz.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YB1u YF9i YCeb YCe8 YCe9 YCi1.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Open Scope Z_scope.
Definition A_getPixelVal : Z := 0x8508c.
Definition A_get_leave_node_index : Z := 0x85b28.
Definition A_round : Z := 0x967f4.
Definition TGPV_STK : Z := 16.
Definition TGLNI_STK : Z := 16.
Definition pixel_word (c : colour) (op : bool) : Z :=
cR c + cG c * 2 ^ 8 + cB c * 2 ^ 16 + (if op then 255 else 0) * 2 ^ 24.
Definition TGLNI_FKEEP : list (bv 5) :=
[0; 1; 2; 3; 4; 5; 6; 7; 8; 9; 10; 11; 12; 13; 16; 17; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%bv.
Section d. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Section e.
Variable B : asyms.
Definition tgpv_spec : Prop :=
forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word) (pb pm pd fmt : Z) (c : colour) (op : bool),
ajournal trbsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
YK0s.ret_ok (getr regs 1) -> 4096 <= raZ regs ->
spZ regs mod 16 = 0 -> sp0 - STK <= spZ regs - TGPV_STK -> spZ regs <= sp0 ->
getr regs 10 = w64 pd -> getr regs 11 = w64 fmt -> (fmt = 3 \/ fmt = 4) ->
In (pb, pm) (ablocks B lyc Sc) -> pb <= pd -> pd + fmt <= pb + pm ->
pixel_at trbsegs (mrestrict (w_H W) memc) pd fmt c op ->
SRr trbsegs W (cfg_at trbsegs A_getPixelVal regs memc mdc)
(fun W2 c2 => W2 = W /\ exists regs2 mem2 md2,
c2 = mkCfg (mkst regs2 (getr regs 1) mem2 (seg_rom trbsegs)) md2 /\
ajournal trbsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mem2 md2 k /\
aregs_preserved regs regs2 /\
getr regs2 10 = w64 (pixel_word c op) /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - TGPV_STK <= a < spZ regs) -> aview trbsegs (w_H W) mem2 a = aview trbsegs (w_H W) memc a) /\
(forall a, apresent (w_H W) memc a -> apresent (w_H W) mem2 a)).
Definition tglni_spec : Prop :=
forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word) (fb nF rgb : Z) (t : tree),
ajournal trbsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
YK0s.ret_ok (getr regs 1) -> 4096 <= raZ regs ->
spZ regs mod 16 = 0 -> sp0 - STK <= spZ regs - TGLNI_STK -> spZ regs <= sp0 ->
frm_zero fp_csr ->
getr regs 10 = w64 (troot t) -> getr regs 11 = w64 rgb ->
In (fb, nF) (ablocks B lyc Sc) -> fb <= rgb -> rgb + 12 <= fb + nF -> rgb mod 4 = 0 ->
tree_full t -> tree_forall tnode_wf t -> tree_at trbsegs (mrestrict (w_H W) memc) t ->
(forall b, In b (tree_blocks t) -> In b (ablocks B lyc Sc)) ->
SRr trbsegs W (cfg_at trbsegs A_get_leave_node_index regs memc mdc)
(fun W2 c2 => W2 = W /\ exists (fx' : YK11.FPState) regs2 mem2 md2,
c2 = mkCfg (@mkst fx' regs2 (getr regs 1) mem2 (seg_rom trbsegs)) md2 /\ frm_zero (@fp_csr fx') /\
(forall r : bv 5, In r TGLNI_FKEEP -> reg_get (@fp_regs fx') r = reg_get (@fp_regs fx) r) /\
ajournal trbsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mem2 md2 k /\
aregs_preserved regs regs2 /\
(exists nl, In nl (tree_leaves t) /\ getr regs2 10 = w64 (tn_cidx nl)) /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - TGLNI_STK <= a < spZ regs) -> aview trbsegs (w_H W) mem2 a = aview trbsegs (w_H W) memc a) /\
(forall a, apresent (w_H W) memc a -> apresent (w_H W) mem2 a)).
End e.
End d.
