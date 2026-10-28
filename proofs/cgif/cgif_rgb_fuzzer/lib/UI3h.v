(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YK11 YK0p YK0s YK15 YN06 YQ0b.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YP0j YP0g YP0c.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import UH04 UH07 UH06 YI00 YI02
UI1i YP14 YI08 YI0c YL0e.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YQ08 YM01 YM02.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Open Scope Z_scope.
Definition SRC2_RO_LO : Z := Eval compute in ubs2_D_const_float_m2147483904.
Definition SRC2_RO_HI : Z := Eval compute in ubs2_D_d_103d8 + 8.
Definition ubs2_rgb_rodata_ok (mem : word -> option byte) : Prop :=
forall a, SRC2_RO_LO <= a < SRC2_RO_HI -> mbyte ubs2segs mem a = seg_rom ubs2segs (Z_to_bv 64 a).
Lemma ubs2_rgb_rodata_of_lib : forall mem, rodata_ok ubs2_msyms mem -> ubs2_rgb_rodata_ok mem.
Proof.
intros mem H a Ha. apply H. split.
- exists (nth 0 ubs2segs seg_dummy). split; [apply nth_In; vm_compute; lia|].
split; [vm_compute; reflexivity|].
match goal with |- ?lo <= a < ?hi => let l := eval vm_compute in lo in let h := eval vm_compute in hi in change (l <= a < h) end.
unfold SRC2_RO_LO, SRC2_RO_HI in Ha. lia.
- unfold SRC2_RO_LO, SRC2_RO_HI in Ha. unfold static_owned. cbv -[Z.le Z.lt Z.add Z.sub not]. lia.
Qed.
Lemma ubs2_rgb_rodata_kept : forall mem mem',
(forall a, in_img ubs2_msyms a -> ~ static_owned ubs2_msyms a -> ~ (ms_ctx ubs2_msyms <= a < ms_ctx ubs2_msyms + CTX_SIZE) ->
~ (errno_addr ubs2_msyms <= a < errno_addr ubs2_msyms + 4) ->
mbyte ubs2segs mem' a = mbyte ubs2segs mem a /\ (writable_at ubs2segs mem a <-> writable_at ubs2segs mem' a)) ->
ubs2_rgb_rodata_ok mem -> ubs2_rgb_rodata_ok mem'.
Proof.
intros mem mem' HK H a Ha. rewrite <- (H a Ha).
assert (H1 : in_img ubs2_msyms a).
{ split; [vm_compute; discriminate|]. exists (nth 0 (segments_reserved (ms_segs ubs2_msyms)) (Z_to_bv 64 0, Z_to_bv 64 0)). split; [apply nth_In; vm_compute; lia|].
match goal with |- ?lo <= a < ?hi => let l := eval vm_compute in lo in let h := eval vm_compute in hi in change (l <= a < h) end.
unfold SRC2_RO_LO, SRC2_RO_HI in Ha. lia. }
assert (H2 : ~ static_owned ubs2_msyms a).
{ unfold SRC2_RO_LO, SRC2_RO_HI in Ha. unfold static_owned. cbv -[Z.le Z.lt Z.add Z.sub not]. lia. }
assert (H3 : ~ (ms_ctx ubs2_msyms <= a < ms_ctx ubs2_msyms + CTX_SIZE)).
{ unfold SRC2_RO_LO, SRC2_RO_HI in Ha. cbv -[Z.le Z.lt Z.add Z.sub not]. lia. }
assert (H4 : ~ (errno_addr ubs2_msyms <= a < errno_addr ubs2_msyms + 4)).
{ unfold SRC2_RO_LO, SRC2_RO_HI in Ha. cbv -[Z.le Z.lt Z.add Z.sub not]. lia. }
exact (proj1 (HK a H1 H2 H3 H4)).
Qed.
Section e. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Section f.
Variable API : AllocAPI ubs2_msyms.
Let MR : MR_t := aa_MR API.
Local Notation segs := ubs2segs.
Local Notation rom := (seg_rom ubs2segs).
Local Notation tp := (ms_tp ubs2_msyms).
Definition col_hash_spec : Prop :=
forall STK sp0 FP L A mem md Lc Ac memc mdc (regs : bvmap 5 word)
(rgb h u T fmt : Z) (used keys : list Z) (c : colour) (op : bool) (r : Z),
journal ubs2_msyms MR STK sp0 FP L A mem md Lc Ac memc mdc ->
YK0s.ret_ok (getr regs 1) -> spZ regs mod 16 = 0 ->
sp0 - STK <= spZ regs - COLHASH_STK -> spZ regs <= sp0 ->
getr regs 10 = Z_to_bv 64 rgb -> getr regs 11 = Z_to_bv 64 h -> getr regs 12 = Z_to_bv 64 u ->
getr regs 13 = Z_to_bv 64 T -> getr regs 14 = Z_to_bv 64 fmt ->
pixel_at segs memc rgb fmt c op ->
arr8 segs memc u used -> arr8 segs memc h keys -> zlen used = T -> zlen keys = 3 * T -> 0 < T < 2 ^ 30 ->
4096 <= rgb -> rgb + fmt <= alloc_ceiling -> 4096 <= u -> u + T <= alloc_ceiling -> 4096 <= h -> h + 3 * T <= alloc_ceiling ->
(op = true -> probe T used keys c = Some r) ->
SR segs (mkCfg (mkst regs (Z_to_bv 64 ubs2_A_col_hash) memc rom) mdc)
(fun c' => exists regs2 mem2,
c' = mkCfg (mkst regs2 (getr regs 1) mem2 rom) mdc /\
journal ubs2_msyms MR STK sp0 FP L A mem md Lc Ac mem2 mdc /\
regs_preserved regs regs2 /\
getr regs2 10 = Z_to_bv 64 (if op then r else 2 ^ 64 - 1) /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - COLHASH_STK <= a < spZ regs) ->
mbyte segs mem2 a = mbyte segs memc a)).
Definition ntn_spec : Prop :=
forall STK sp0 FP L A mem md Lc Ac memc mdc (regs : bvmap 5 word)
(palp frp nln imin imax cidx n0 : Z) (pal fr : list Z),
journal ubs2_msyms MR STK sp0 FP L A mem md Lc Ac memc mdc -> st_init_done Ac = true ->
YK0s.ret_ok (getr regs 1) -> spZ regs mod 16 = 0 -> getr regs 4 = Z_to_bv 64 tp ->
sp0 - STK <= spZ regs - NTN_STK -> spZ regs <= sp0 ->
frm_zero fp_csr ->
getr regs 10 = Z_to_bv 64 palp -> getr regs 11 = Z_to_bv 64 frp -> getr regs 12 = Z_to_bv 64 nln ->
getr regs 13 = Z_to_bv 64 imin -> getr regs 14 = Z_to_bv 64 imax -> getr regs 15 = Z_to_bv 64 cidx ->
arr8 segs memc palp pal -> arr32 segs memc frp fr ->
0 <= imin <= imax -> imax < 2 ^ 30 -> 3 * (imax + 1) <= zlen pal -> imax + 1 <= zlen fr -> 0 <= cidx < 256 ->
4096 <= palp -> palp + zlen pal <= alloc_ceiling -> 4096 <= frp -> frp + 4 * zlen fr <= alloc_ceiling -> frp mod 4 = 0 ->
(exists b m, In (b, m) (blocks Lc Ac) /\ b <= palp /\ palp + zlen pal <= b + m) ->
(exists b m, In (b, m) (blocks Lc Ac) /\ b <= frp /\ frp + 4 * zlen fr <= b + m) ->
(palp + zlen pal <= frp \/ frp + 4 * zlen fr <= palp) ->
(forall i, imin <= i <= imax -> 1 <= getz fr i) ->
wsum (node_list pal fr imin imax 0) <= RGB_NMAX ->
spZ regs <= nln -> nln + 2 <= sp0 -> nln mod 2 = 0 -> val_mem segs memc nln 2 n0 -> 0 <= n0 < 2 ^ 16 - 1 ->
SR segs (mkCfg (mkst regs (Z_to_bv 64 ubs2_A_new_tree_node) memc rom) mdc)
(fun c' => exists (fx' : FPState) L2 A2 regs2 mem2 md2 (res : Z),
c' = mkCfg (@mkst fx' regs2 (getr regs 1) mem2 rom) md2 /\ frm_zero (@fp_csr fx') /\
journal ubs2_msyms MR STK sp0 FP L A mem md L2 A2 mem2 md2 /\ st_init_done A2 = true /\
regs_preserved regs regs2 /\ getr regs2 10 = Z_to_bv 64 res /\
(forall a, alloc_ceiling <= a < 2 ^ 64 -> ~ (spZ regs - NTN_STK <= a < spZ regs) -> ~ (nln <= a < nln + 2) ->
mbyte segs mem2 a = mbyte segs memc a) /\
(forall b m i, In (b, m) (blocks Lc Ac) -> 0 <= i < m -> mbyte segs mem2 (b + i) = mbyte segs memc (b + i)) /\
((res = 0 /\ blocks L2 A2 = blocks Lc Ac /\ val_mem segs mem2 nln 2 n0)
\/ (res <> 0 /\ res mod 16 = 0 /\
(exists b1 b2, blocks L2 A2 = b1 ++ (res, NODE_SIZE) :: b2 /\ blocks Lc Ac = b1 ++ b2) /\
(forall blc i, In (res, NODE_SIZE) blc -> 0 <= i < NODE_SIZE -> wr_byte STK sp0 FP (blocks L A) blc (res + i)) /\
val_mem segs mem2 nln 2 (n0 + 1) /\
exists nd : tnode,
tn_addr nd = res /\ tn_imin nd = imin /\ tn_imax nd = imax /\ tn_cidx nd = cidx /\
tree_at segs mem2 (TLeaf nd) /\ tnode_wf nd /\
(forall d, 0 <= d <= 2 ->
is_quot (nth (Z.to_nat d) (tn_mean nd) 0)
(wdot (node_list pal fr imin imax d)) (wsum (node_list pal fr imin imax d))) /\
(range_has_two pal imin imax -> dim_splits pal imin imax (tn_cut nd))))).
Definition free_tree_spec : Prop :=
forall L A (regs : bvmap 5 word) mem md (t : tree) (rest : list (Z * Z)),
fn_pre ubs2_msyms MR FREETREE_STK L A regs mem md ->
getr regs 10 = Z_to_bv 64 (troot t) ->
tree_at segs mem t -> Z.of_nat (tree_height t) <= TREE_HMAX ->
Permutation (blocks L A) (tree_blocks t ++ rest) ->
SR segs (mkCfg (mkst regs (Z_to_bv 64 ubs2_A_free_decision_tree) mem rom) md)
(fun c' => exists L' A' regs' mem' md',
c' = mkCfg (mkst regs' (getr regs 1) mem' rom) md' /\
journal ubs2_msyms MR FREETREE_STK (spZ regs) (blocks_fp (tree_blocks t)) L A mem md L' A' mem' md' /\
regs_preserved regs regs' /\
Permutation (blocks L' A') rest).
Definition getpal_spec : Prop :=
forall STK sp0 FP L A mem md Lc Ac memc mdc (regs : bvmap 5 word) (t : tree) (pal : Z),
journal ubs2_msyms MR STK sp0 FP L A mem md Lc Ac memc mdc ->
YK0s.ret_ok (getr regs 1) -> spZ regs mod 16 = 0 ->
sp0 - STK <= spZ regs - GETPAL_STK -> spZ regs <= sp0 ->
frm_zero fp_csr ->
getr regs 10 = Z_to_bv 64 (troot t) -> getr regs 11 = Z_to_bv 64 pal ->
tree_at segs memc t -> tree_full t -> Z.of_nat (tree_height t) <= TREE_HMAX -> tree_forall tnode_wf t ->
tree_forall tnode_means_ok t ->
(forall b, In b (tree_blocks t) -> In b (blocks Lc Ac)) ->
spZ regs <= pal -> pal + 768 <= sp0 ->
ubs2_rgb_rodata_ok memc ->
SR segs (mkCfg (mkst regs (Z_to_bv 64 ubs2_A_get_palette_from_decision_tree) memc rom) mdc)
(fun c' => exists (fx' : FPState) regs2 mem2,
c' = mkCfg (@mkst fx' regs2 (getr regs 1) mem2 rom) mdc /\ frm_zero (@fp_csr fx') /\
fregs_preserved (@fp_regs fx) (@fp_regs fx') /\
journal ubs2_msyms MR STK sp0 FP L A mem md Lc Ac mem2 mdc /\
regs_preserved regs regs2 /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - GETPAL_STK <= a < spZ regs) -> ~ (pal <= a < pal + 768) ->
mbyte segs mem2 a = mbyte segs memc a)).
Definition fmt_okb (fmt : Z) : bool := (fmt =? 3) || (fmt =? 4).
Definition img_block (img fmt N : Z) : list (Z * Z) := if fmt_okb fmt then [(img, fmt * N)] else [].
Definition rgb_addframe_spec : Prop :=
forall L A (regs : bvmap 5 word) mem md
(r cfp : Z) (g wfn ctx path attr gen loops W H bef beffmt cur : Z) (s : cgif_st) (N : Z)
(img fmt fattr fgen delay : Z) (rest : list (Z * Z)),
fn_pre ubs2_msyms MR RGBA_STK L A regs mem md -> st_init_done A = true ->
frm_zero fp_csr ->
getr regs 10 = Z_to_bv 64 r -> getr regs 11 = Z_to_bv 64 cfp ->
cfp mod 8 = 0 -> spZ regs <= cfp -> cfp + RGBFC_SIZE <= 2 ^ 63 ->
obj_at segs mem cfp LAY_RgbFrameConfig [img; fmt; fattr; fgen; delay] ->
obj_at segs mem r LAY_Rgb [g; wfn; ctx; path; attr; gen; loops; W; H; bef; beffmt; cur] ->
cgif_at mem g s -> cgif_wf s N -> cg_W s = W -> cg_H s = H -> N <= RGB_NMAX ->
(bef = 0 \/ beffmt = 3 \/ beffmt = 4) ->
ubs2_rgb_rodata_ok mem ->
Permutation (blocks L A)
((r, RGB_SIZE) :: cgif_blocks g s N ++ optb bef (beffmt * N) ++ img_block img fmt N ++ rest) ->
SR segs (mkCfg (mkst regs (Z_to_bv 64 ubs2_A_cgif_rgb_addframe) mem rom) md)
(fun c' => exists (fx' : FPState) L' A' regs' mem' md' (s' : cgif_st) (bef' beffmt' cur' : Z),
c' = mkCfg (@mkst fx' regs' (getr regs 1) mem' rom) md' /\ frm_zero (@fp_csr fx') /\
journal ubs2_msyms MR RGBA_STK (spZ regs)
((r, r + RGB_SIZE) :: blocks_fp (cgif_blocks g s N) ++ optfp bef (beffmt * N))
L A mem md L' A' mem' md' /\
regs_preserved regs regs' /\ st_init_done A' = true /\
obj_at segs mem' r LAY_Rgb [g; wfn; ctx; path; attr; gen; loops; W; H; bef'; beffmt'; cur'] /\
cgif_at mem' g s' /\ cgif_wf s' N /\
cg_W s' = W /\ cg_H s' = H /\ cg_attr s' = cg_attr s /\ cg_raw s' = cg_raw s /\
(bef' = 0 \/ beffmt' = 3 \/ beffmt' = 4) /\
Permutation (blocks L' A')
((r, RGB_SIZE) :: cgif_blocks g s' N ++ optb bef' (beffmt' * N) ++ img_block img fmt N ++ rest)).
End f.
End e.
