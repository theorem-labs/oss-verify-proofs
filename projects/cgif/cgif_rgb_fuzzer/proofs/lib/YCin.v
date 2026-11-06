(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YK11 YK0p YK0s YK15 YQ0b YI00 YI02.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YI1i YP14 YI08 YI0c YM01 YM02.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YG10.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YK05 YA0i YA0l.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YG00 YG0a YG01 YG0h YG0u YG0d YCcz.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YB1u YF9i YCeb YCe8 YCe9 YCi1 YCil.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Open Scope Z_scope.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YCim.
Section b.
Context {rc : YN05.RunCeil}.
Variable B : asyms.
Definition tntn_spec2V : Prop :=
forall (fx : YK11.FPState) STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word)
(palp frp nln imin imax cidx n0 : Z) (pal fr : list Z) (pb pm fb fm : Z),
ajournal trbsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
YK0s.ret_ok (getr regs 1) -> 4096 <= raZ regs ->
getr regs 3 = w64 (as_gp B) -> getr regs 4 = w64 (as_tp B) ->
spZ regs mod 16 = 0 -> sp0 - STK <= spZ regs - TNTN_STK -> spZ regs <= sp0 ->
frm_zero (@fp_csr fx) ->
getr regs 10 = w64 palp -> getr regs 11 = w64 frp -> getr regs 12 = w64 nln ->
getr regs 13 = w64 imin -> getr regs 14 = w64 imax -> getr regs 15 = w64 cidx ->
In (pb, pm) (ablocks B lyc Sc) -> pb <= palp -> palp + zlen pal <= pb + pm ->
In (fb, fm) (ablocks B lyc Sc) -> fb <= frp -> frp + 4 * zlen fr <= fb + fm -> frp mod 4 = 0 -> (pb, pm) <> (fb, fm) ->
arr8 trbsegs (mrestrict (w_H W) memc) palp pal -> arr32 trbsegs (mrestrict (w_H W) memc) frp fr ->
0 <= imin <= imax -> imax < 2 ^ 30 -> 3 * (imax + 1) <= zlen pal -> imax + 1 <= zlen fr -> 0 <= cidx < 256 ->
(forall i, imin <= i <= imax -> 1 <= getz fr i) ->
wsum (node_list pal fr imin imax 0) <= RGB_NMAX ->
spZ regs <= nln -> nln + 2 <= sp0 -> nln mod 8 = 2 ->
val_mem trbsegs (mrestrict (w_H W) memc) nln 2 n0 -> 0 <= n0 < 2 ^ 16 - 1 ->
vev Sc < VEV_MAX   -> blocks_bytes Sc + NODE_SIZE <= LIVE_MAX ->
SRr trbsegs W (mkCfg (@mkst fx regs (Z_to_bv 64 A_new_tree_node) memc (seg_rom trbsegs)) mdc)
(fun W2 c2 => exists (fx' : YK11.FPState) ly2 S2 regs2 mem2 md2 (res : Z),
c2 = mkCfg (@mkst fx' regs2 (getr regs 1) mem2 (seg_rom trbsegs)) md2 /\ frm_zero (@fp_csr fx') /\
ajournal trbsegs B STK sp0 FP ly S W0 mem0 md0 own ly2 S2 W2 mem2 md2 (k + EV_NTN) /\
aregs_preserved regs regs2 /\ frames S2 = frames Sc /\
bud_le Sc S2 1 1 208 0   /\ getr regs2 10 = w64 res /\
acall_keptE trbsegs B lyc Sc W memc W2 mem2 (spZ regs - TNTN_STK) (spZ regs) (fun a => nln <= a < nln + 2) /\
((res = 0 /\ ablocks B ly2 S2 = ablocks B lyc Sc /\ val_mem trbsegs (mrestrict (w_H W2) mem2) nln 2 n0)
\/ (4096 <= res /\ ablocks B ly2 S2 = ablocks B lyc Sc ++ [(res, NODE_SIZE)] /\
val_mem trbsegs (mrestrict (w_H W2) mem2) nln 2 (n0 + 1) /\
exists nd : tnode,
tn_addr nd = res /\ tn_imin nd = imin /\ tn_imax nd = imax /\ tn_cidx nd = cidx /\
tree_at trbsegs (mrestrict (w_H W2) mem2) (TLeaf nd) /\ tnode_wf nd /\
(forall d, 0 <= d <= 2 ->
is_quot (nth (Z.to_nat d) (tn_mean nd) 0)
(wdot (node_list pal fr imin imax d)) (wsum (node_list pal fr imin imax d))) /\
(range_has_two pal imin imax -> dim_splits pal imin imax (tn_cut nd))))).
End b.
