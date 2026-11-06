(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YK11 YK0p YK0s YK15 YQ0b YI00 YI02.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YI1i YP14 YI08 YI0c.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YG10.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YK05 YA0i YA0l.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YG00 YG0a YG01 YG0h YG0u YG0d YC04.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YB0z YF8z YC1d YC1a YC1b.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Open Scope Z_scope.
Definition A_cgif_rgb_newgif : Z := 0x81bf4.
Definition A_cgif_rgb_addframe : Z := 0x81f84.
Definition A_free_col_hash_table : Z := 0x84b9c.
Definition A_cgif_rgb_close : Z := 0x84c74.
Definition A_col_hash : Z := 0x84cfc.
Definition A_free_decision_tree : Z := 0x84ea8.
Definition A_new_tree_node : Z := 0x84f60.
Definition A_get_palette : Z := 0x853b8.
Definition TFREECHT_STK : Z := 32 + ASTACK.
Definition TRGBCLOSE_STK : Z := 32 + TCLOSE_STK.
Definition FDT_STK (d : Z) : Z := 32 * (d + 1) + ASTACK.
Definition GP_STK (d : Z) : Z := 32 * (d + 1).
Definition TCOLHASH_STK : Z := 64 + 2 * ESTACK.
Definition A_bcmp_tra : Z := 0x420d8.
Definition EV_FREECHT : Z := 6.
Definition EV_RGBCLOSE : Z := EV_CLOSE + 2.
Section e. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Section i.
Variable B : asyms.
Definition trgb_close_spec : Prop :=
forall ly S W (regs : bvmap 5 word) mem md ch (r g : Z) (s : cgif_st) (N bef nbef : Z) (rest : list (Z * Z)),
afn_pre trasegs B TRGBCLOSE_STK ly S W regs mem md ch ->
In (raZ regs :: spine ch) CTX_cgif_rgb_close -> Z.of_nat (length (frames S)) <= 7 ->
arodata_ok B (aview trasegs (w_H W) mem) ->
getr regs 10 = w64 r ->
val_mem trasegs (mrestrict (w_H W) mem) r 8 g ->
val_mem trasegs (mrestrict (w_H W) mem) (r + 48) 8 bef -> 0 <= bef < 2 ^ 64 ->
tcgif_at (mrestrict (w_H W) mem) g s -> cgif_wf s N ->
Permutation (ablocks B ly S) ((r, RGB_SIZE) :: cgif_blocks g s N ++ optb bef nbef ++ rest) ->
vev S + EV_RGBCLOSE <= VEV_MAX -> blocks_bytes S + LIVE_FLUSH <= LIVE_MAX ->
SRr trasegs W (cfg_at trasegs A_cgif_rgb_close regs mem md)
(apost_base B TRGBCLOSE_STK (ablocks_fp ((r, RGB_SIZE) :: cgif_blocks g s N ++ optb bef nbef)) regs ly S W mem md EV_RGBCLOSE
(fun ly' S' W' regs' mem' md' => Permutation (ablocks B ly' S') rest)).
Definition tfree_cht_spec : Prop :=
forall ly S W (regs : bvmap 5 word) mem md ch (c : Z) (f h u p x : Z) (nf nh nu np nx : Z) (rest : list (Z * Z)),
afn_pre trasegs B TFREECHT_STK ly S W regs mem md ch ->
In (raZ regs :: spine ch) CTX_free_col_hash_table ->
getr regs 10 = w64 c ->
val_mem trasegs (mrestrict (w_H W) mem) c 8 f -> val_mem trasegs (mrestrict (w_H W) mem) (c + 8) 8 h ->
val_mem trasegs (mrestrict (w_H W) mem) (c + 16) 8 u -> val_mem trasegs (mrestrict (w_H W) mem) (c + 24) 8 p ->
val_mem trasegs (mrestrict (w_H W) mem) (c + 32) 8 x ->
0 <= f < 2 ^ 64 -> 0 <= h < 2 ^ 64 -> 0 <= u < 2 ^ 64 -> 0 <= p < 2 ^ 64 -> 0 <= x < 2 ^ 64 ->
Permutation (ablocks B ly S) ((c, CHT_SIZE) :: optb f nf ++ optb h nh ++ optb u nu ++ optb p np ++ optb x nx ++ rest) ->
vev S + EV_FREECHT <= VEV_MAX ->
SRr trasegs W (cfg_at trasegs A_free_col_hash_table regs mem md)
(apost_base B TFREECHT_STK (ablocks_fp ((c, CHT_SIZE) :: optb f nf ++ optb h nh ++ optb u nu ++ optb p np ++ optb x nx))
regs ly S W mem md EV_FREECHT
(fun ly' S' W' regs' mem' md' => Permutation (ablocks B ly' S') rest)).
Definition tfree_tree_spec : Prop :=
forall (d : nat) ly S W (regs : bvmap 5 word) mem md ch (t : tree) (rest : list (Z * Z)),
(tree_height t <= d)%nat ->
afn_pre trasegs B (FDT_STK (Z.of_nat d)) ly S W regs mem md ch ->
In (raZ regs :: spine ch) CTX_free_decision_tree ->
getr regs 10 = w64 (troot t) ->
tree_at trasegs (mrestrict (w_H W) mem) t ->
Permutation (ablocks B ly S) (tree_blocks t ++ rest) ->
vev S + Z.of_nat (length (tree_nodes t)) <= VEV_MAX ->
SRr trasegs W (cfg_at trasegs A_free_decision_tree regs mem md)
(apost_base B (FDT_STK (Z.of_nat d)) (ablocks_fp (tree_blocks t)) regs ly S W mem md (Z.of_nat (length (tree_nodes t)))
(fun ly' S' W' regs' mem' md' => Permutation (ablocks B ly' S') rest)).
Definition tgetpal_spec : Prop :=
forall (d : nat) STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word) (t : tree) (pal cid pos : Z),
ajournal trasegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
(tree_height t <= d)%nat -> tree_full t ->
YK0s.ret_ok (getr regs 1) -> 4096 <= raZ regs ->
getr regs 10 = w64 (troot t) -> getr regs 11 = w64 pal ->
spZ regs mod 16 = 0 -> sp0 - STK <= spZ regs - GP_STK (Z.of_nat d) -> spZ regs <= sp0 ->
frm_zero fp_csr ->
In (cid, pos) own -> 0 <= cid ->
frame_addr lyc cid pos <= pal -> pal + 768 <= frame_addr lyc cid pos + fs_frame_bytes cid ->
range_addressable (aview trasegs (w_H W) memc) SHADOW_OFF pal 768 ->
(forall b, In b (tree_blocks t) -> In b (ablocks B lyc Sc)) ->
tree_at trasegs (mrestrict (w_H W) memc) t ->
SRr trasegs W (cfg_at trasegs A_get_palette regs memc mdc)
(fun W2 c2 => W2 = W /\ exists (fx' : YK11.FPState) regs2 mem2 md2,
c2 = mkCfg (@mkst fx' regs2 (getr regs 1) mem2 (seg_rom trasegs)) md2 /\ frm_zero (@fp_csr fx') /\
ajournal trasegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mem2 md2 k /\
aregs_preserved regs regs2 /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - GP_STK (Z.of_nat d) <= a < spZ regs) -> ~ (pal <= a < pal + 768) ->
aview trasegs (w_H W) mem2 a = aview trasegs (w_H W) memc a) /\
(forall a, apresent (w_H W) memc a -> apresent (w_H W) mem2 a)).
Definition tcolhash_spec : Prop :=
forall ly S W (regs : bvmap 5 word) mem md ch (img Nimg off h Nh u Nu T fmt : Z) (used keys : list Z) (c : colour) (op : bool) (r : Z),
afn_pre trasegs B TCOLHASH_STK ly S W regs mem md ch ->
getr regs 10 = w64 (img + off) -> getr regs 11 = w64 h -> getr regs 12 = w64 u -> getr regs 13 = w64 T -> getr regs 14 = w64 fmt ->
In (img, Nimg) (ablocks B ly S) -> 0 <= off -> off + fmt <= Nimg ->
In (h, Nh) (ablocks B ly S) -> 3 * T <= Nh -> In (u, Nu) (ablocks B ly S) -> T <= Nu ->
pixel_at trasegs (mrestrict (w_H W) mem) (img + off) fmt c op ->
arr8 trasegs (mrestrict (w_H W) mem) u used -> arr8 trasegs (mrestrict (w_H W) mem) h keys ->
zlen used = T -> zlen keys = 3 * T -> 0 < T < 2 ^ 30 ->
(op = true -> probe T used keys c = Some r) ->
SRr trasegs W (cfg_at trasegs A_col_hash regs mem md)
(apost_base B TCOLHASH_STK [] regs ly S W mem md 0
(fun ly' S' W' regs' mem' md' => ly' = ly /\ S' = S /\ W' = W /\ getr regs' 10 = w64 (if op then r else 2 ^ 64 - 1))).
End i.
End e.
