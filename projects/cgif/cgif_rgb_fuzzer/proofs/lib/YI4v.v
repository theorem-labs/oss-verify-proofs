(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Sem.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YK11 YK0p YK0s YK15 YN06 YQ0b.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YP0j YP0g YP0c.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YH04 YH07 YH06 YI00 YI02
YI1i YP14 YI08 YI0c YI0g YI3h.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YQ08 YM01 YM02.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Open Scope Z_scope.
Definition RGBA_FRAME : Z := 5136.
Definition PC_E1  : Z := 0x13414.   Definition PC_A1  : Z := 0x13540.
Definition PC_HL  : Z := 0x13680.   Definition PC_RS  : Z := 0x1386c.
Definition PC_HD  : Z := 0x13b94.   Definition PC_CR  : Z := 0x13d68.
Definition PC_QT  : Z := 0x13f84.   Definition PC_DI  : Z := 0x14004.
Definition PC_ND  : Z := 0x14308.   Definition PC_QE  : Z := 0x14464.
Definition PC_SM  : Z := 0x13c78.   Definition PC_FIN : Z := 0x14480.
Definition PC_X38 : Z := 0x14298.   Definition PC_XB  : Z := 0x142a0.
Definition PC_XF  : Z := 0x142a8.   Definition PC_XS  : Z := 0x142b0.
Definition PC_XC  : Z := 0x144f0.   Definition PC_XD  : Z := 0x144e4.
Definition PC_XT  : Z := 0x144dc.   Definition PC_XT2 : Z := 0x142fc.
Definition RA_SAVED : list reg := [1; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv.
Definition SL_16 : Z := 16.
Definition SL_fa1 : Z := 24.
Definition SL_N : Z := 32.
Definition SL_cfp : Z := 40.
Definition SL_new : Z := 48.
Definition SL_fimg : Z := 56.
Definition SL_64 : Z := 64.
Definition SL_72 : Z := 72.
Definition SL_80 : Z := 80.
Definition SL_88 : Z := 88.
Definition SL_96 : Z := 96.
Definition SL_104 : Z := 104.
Definition SL_112 : Z := 112.
Definition OFF_fcfg : Z := 120. Definition OFF_apal : Z := 158. Definition OFF_nln : Z := 926.
Definition OFF_nl : Z := 928.   Definition OFF_sblk : Z := 5028.
Section a. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Section d.
Variable API : AllocAPI src2_msyms.
Let MR : MR_t := aa_MR API.
Local Notation segs := src2segs.
Local Notation rom := (seg_rom src2segs).
Local Notation tp := (ms_tp src2_msyms).
Variables (L : layout) (A : astate) (regs0 : bvmap 5 word) (mem0 : word -> option byte) (md0 : Model).
Variables (r cfp g wfn ctx path attr gen loops W H bef beffmt cur : Z) (s : cgif_st) (N : Z).
Variables (img fmt fattr fgen delay : Z) (rest : list (Z * Z)).
Definition sp0 : Z := spZ regs0.
Definition sp : Z := sp0 - RGBA_FRAME.
Definition FPfoot : list (Z * Z) := (r, r + RGB_SIZE) :: blocks_fp (cgif_blocks g s N) ++ optfp bef (beffmt * N).
Definition BASE (s1 : cgif_st) (bef1 beffmt1 : Z) : list (Z * Z) :=
(r, RGB_SIZE) :: cgif_blocks g s1 N ++ optb bef1 (beffmt1 * N) ++ img_block img fmt N ++ rest.
Definition fattr1 : Z := if Z.land fattr 1 =? 0 then 1 else 9.
Definition rgba_pre : Prop :=
fn_pre src2_msyms MR RGBA_STK L A regs0 mem0 md0 /\ st_init_done A = true /\ frm_zero fp_csr /\
getr regs0 10 = Z_to_bv 64 r /\ getr regs0 11 = Z_to_bv 64 cfp /\
cfp mod 8 = 0 /\ sp0 <= cfp /\ cfp + RGBFC_SIZE <= 2 ^ 63 /\
obj_at segs mem0 cfp LAY_RgbFrameConfig [img; fmt; fattr; fgen; delay] /\
obj_at segs mem0 r LAY_Rgb [g; wfn; ctx; path; attr; gen; loops; W; H; bef; beffmt; cur] /\
cgif_at mem0 g s /\ cgif_wf s N /\ cg_W s = W /\ cg_H s = H /\ N <= RGB_NMAX /\
(bef = 0 \/ beffmt = 3 \/ beffmt = 4) /\ src2_rgb_rodata_ok mem0 /\
Permutation (blocks L A) (BASE s bef beffmt).
Definition rgba_post : config -> Prop :=
fun c' => exists (fx' : FPState) L' A' regs' mem' md' (s' : cgif_st) (bef' beffmt' cur' : Z),
c' = mkCfg (@mkst fx' regs' (getr regs0 1) mem' rom) md' /\ frm_zero (@fp_csr fx') /\
journal src2_msyms MR RGBA_STK sp0 FPfoot L A mem0 md0 L' A' mem' md' /\
regs_preserved regs0 regs' /\ st_init_done A' = true /\
obj_at segs mem' r LAY_Rgb [g; wfn; ctx; path; attr; gen; loops; W; H; bef'; beffmt'; cur'] /\
cgif_at mem' g s' /\ cgif_wf s' N /\
cg_W s' = W /\ cg_H s' = H /\ cg_attr s' = cg_attr s /\ cg_raw s' = cg_raw s /\
(bef' = 0 \/ beffmt' = 3 \/ beffmt' = 4) /\
Permutation (blocks L' A') (BASE s' bef' beffmt').
Definition ra_saved_ok (memc : word -> option byte) : Prop :=
forall j rr, nth_error RA_SAVED j = Some rr -> word_mem segs memc (sp0 - 8 * (Z.of_nat j + 1)) (bv_unsigned (getr regs0 rr)).
Definition slot (memc : word -> option byte) (off v : Z) : Prop := word_mem segs memc (sp + off) v.
Definition rgba_inv (Lc : layout) (Ac : astate) (memc : word -> option byte) (mdc : Model) : Prop :=
journal src2_msyms MR RGBA_STK sp0 FPfoot L A mem0 md0 Lc Ac memc mdc /\ st_init_done Ac = true /\
frm_zero (@fp_csr fx)   /\
YK0s.ret_ok (getr regs0 1) /\ sp0 mod 16 = 0 /\ getr regs0 4 = Z_to_bv 64 tp /\
ra_saved_ok memc /\
cfp mod 8 = 0 /\ sp0 <= cfp /\ cfp + RGBFC_SIZE <= 2 ^ 63 /\
obj_at segs memc cfp LAY_RgbFrameConfig [img; fmt; fattr; fgen; delay] /\
src2_rgb_rodata_ok mem0   /\
cgif_wf s N /\ cg_W s = W /\ cg_H s = H /\ N <= RGB_NMAX /\ (bef = 0 \/ beffmt = 3 \/ beffmt = 4) /\
Permutation (blocks L A) (BASE s bef beffmt)  .

Definition rgba_regs (regs1 : bvmap 5 word) : Prop :=
getr regs1 2 = Z_to_bv 64 sp /\ getr regs1 3 = getr regs0 3 /\ getr regs1 4 = getr regs0 4.
Definition rgb_obj (memc : word -> option byte) : Prop :=
obj_at segs memc r LAY_Rgb [g; wfn; ctx; path; attr; gen; loops; W; H; bef; beffmt; cur].
Definition fcfg_at (memc : word -> option byte) (fimg nlpe tidx : Z) : Prop :=
obj_at segs memc (sp + OFF_fcfg) LAY_FrameConfig [sp + OFF_apal; fimg; fattr1; 0; delay; nlpe; tidx].
Definition slots_mid (memc : word -> option byte) (pnew fimg : Z) : Prop :=
slot memc SL_N N /\ slot memc SL_cfp cfp /\ slot memc SL_new pnew /\ slot memc SL_fimg fimg /\ slot memc SL_fa1 fattr1.
Definition nha (ha : Z) : Z := if ha =? 0 then 1 else 0.
Definition img_at (memc : word -> option byte) (imgl : list Z) : Prop :=
arr8 segs memc img imgl /\ zlen imgl = fmt * N.
Record cht := mkCHT { ch_c : Z; ch_f : Z; ch_h : Z; ch_u : Z; ch_p : Z; ch_x : Z; ch_T : Z;
ch_hS : Z; ch_uS : Z; ch_TS : Z; ch_H : htab; ch_ent : list (colour * Z) }.
Definition cht_ok (memc : word -> option byte) (C : cht) : Prop :=
obj_at segs memc (ch_c C) LAY_Cht [ch_f C; ch_hS C; ch_uS C; ch_p C; ch_x C; ht_cnt (ch_H C); ch_TS C] /\
cht_arrays segs memc (ch_f C) (ch_h C) (ch_u C) (ch_p C) (ch_x C) (ch_H C) /\
ht_inv (ch_H C) (ch_ent C) /\ ht_T (ch_H C) = ch_T C /\ In (ch_T C) ts_chain /\
0 <= ch_hS C < 2 ^ 64 /\ 0 <= ch_uS C < 2 ^ 64 /\ 0 <= ch_TS C < 2 ^ 32.
Definition cht_blks (C : cht) : list (Z * Z) := (ch_c C, CHT_SIZE) :: cht_blocks (ch_f C) (ch_h C) (ch_u C) (ch_p C) (ch_x C) (ch_T C).
Definition chtq_ok (memc : word -> option byte) (C : cht) (cnt : Z) (pal : list Z) : Prop :=
obj_at segs memc (ch_c C) LAY_Cht [ch_f C; ch_h C; ch_u C; ch_p C; ch_x C; cnt; ch_T C] /\
arr8 segs memc (ch_p C) pal /\ zlen pal = 3 * ch_T C /\ In (ch_T C) ts_chain /\
(forall b, In b (cht_blks C) -> 4096 <= fst b).
Definition dense_ok (memc : word -> option byte) (fdp : Z) (fdl pal : list Z) (cnt : Z) : Prop :=
arr32 segs memc fdp fdl /\ zlen fdl = cnt /\ 256 <= cnt /\ 3 * cnt <= zlen pal /\
(forall i, 0 <= i < cnt -> 1 <= getz fdl i) /\ zsum fdl <= N /\
(forall i j, 0 <= i < cnt -> 0 <= j < cnt -> i <> j -> col_at pal i <> col_at pal j).
Definition at_A1 (regs1 : bvmap 5 word) (Lc : layout) (Ac : astate) (memc : word -> option byte) (mdc : Model)
(pnew fimg : Z) (imgl : list Z) : Prop :=
rgba_inv Lc Ac memc mdc /\ rgba_regs regs1 /\ (fmt = 3 \/ fmt = 4) /\ 1 <= N /\
getr regs1 8 = Z_to_bv 64 r /\ getr regs1 19 = Z_to_bv 64 cfp /\ getr regs1 9 = Z_to_bv 64 pnew /\
getr regs1 25 = Z_to_bv 64 fimg /\ getr regs1 21 = Z_to_bv 64 2 /\ getr regs1 22 = Z_to_bv 64 N /\
getr regs1 26 = Z_to_bv 64 img /\ getr regs1 27 = Z_to_bv 64 fmt /\ getr regs1 18 = Z_to_bv 64 fattr1 /\
fcfg_at memc fimg 0 0 /\ rgb_obj memc /\ cgif_at memc g s /\ img_at memc imgl /\
pnew <> 0 /\ fimg <> 0 /\
Permutation (blocks Lc Ac) (BASE s bef beffmt ++ [(pnew, fmt * N); (fimg, N)]).
Definition hist_regs (regs1 : bvmap 5 word) (i ha : Z) (C : cht) : Prop :=
getr regs1 9 = Z_to_bv 64 i /\ getr regs1 10 = Z_to_bv 64 ha /\ getr regs1 15 = Z_to_bv 64 fmt /\
getr regs1 16 = Z_to_bv 64 3 /\ getr regs1 17 = Z_to_bv 64 N /\ getr regs1 26 = Z_to_bv 64 img /\
getr regs1 27 = Z_to_bv 64 fmt /\ getr regs1 20 = Z_to_bv 64 (ch_c C) /\ getr regs1 8 = Z_to_bv 64 r /\
getr regs1 21 = Z_to_bv 64 2.
Definition hist_mem (Lc : layout) (Ac : astate) (memc : word -> option byte) (pnew fimg : Z) (imgl : list Z) (C : cht) (i : Z) : Prop :=
slots_mid memc pnew fimg /\ slot memc SL_16 0x10001 /\ slot memc SL_104 (2 ^ 32 - 1) /\ slot memc SL_64 img /\
slot memc SL_80 N /\ slot memc SL_88 fmt /\ slot memc SL_96 fmt /\
fcfg_at memc fimg 0 0 /\ rgb_obj memc /\ cgif_at memc g s /\ img_at memc imgl /\
cht_ok memc C /\ ch_hS C = ch_h C /\ ch_uS C = ch_u C /\ ch_TS C = ch_T C /\ zsum (map snd (ch_ent C)) <= i /\
pnew <> 0 /\ fimg <> 0 /\
Permutation (blocks Lc Ac) (BASE s bef beffmt ++ [(pnew, fmt * N); (fimg, N)] ++ cht_blks C).
Definition at_HL (regs1 : bvmap 5 word) (Lc : layout) (Ac : astate) (memc : word -> option byte) (mdc : Model)
(i ha pnew fimg : Z) (imgl : list Z) (C : cht) : Prop :=
rgba_inv Lc Ac memc mdc /\ rgba_regs regs1 /\ (fmt = 3 \/ fmt = 4) /\ 0 <= i < N /\ (ha = 0 \/ (ha = 1 /\ fmt = 4)) /\
hist_regs regs1 i ha C /\ hist_mem Lc Ac memc pnew fimg imgl C i.
Definition at_RS (regs1 : bvmap 5 word) (Lc : layout) (Ac : astate) (memc : word -> option byte) (mdc : Model)
(i ha pnew fimg : Z) (imgl : list Z) (C : cht) : Prop :=
rgba_inv Lc Ac memc mdc /\ rgba_regs regs1 /\ (fmt = 3 \/ fmt = 4) /\ 0 <= i < N /\ (ha = 0 \/ (ha = 1 /\ fmt = 4)) /\
getr regs1 11 = Z_to_bv 64 (ch_T C) /\ getr regs1 5 = Z_to_bv 64 ha /\ getr regs1 9 = Z_to_bv 64 i /\
getr regs1 20 = Z_to_bv 64 (ch_c C) /\ getr regs1 8 = Z_to_bv 64 r /\ getr regs1 21 = Z_to_bv 64 2 /\
getr regs1 22 = Z_to_bv 64 1   /\
ch_T C < MAX_TABLE_SIZE /\
hist_mem Lc Ac memc pnew fimg imgl C (i + 1).
Definition at_HD (regs1 : bvmap 5 word) (Lc : layout) (Ac : astate) (memc : word -> option byte) (mdc : Model)
(ha pnew fimg : Z) (imgl : list Z) (C : cht) : Prop :=
rgba_inv Lc Ac memc mdc /\ rgba_regs regs1 /\ (fmt = 3 \/ fmt = 4) /\ 1 <= N /\ (ha = 0 \/ (ha = 1 /\ fmt = 4)) /\
getr regs1 10 = Z_to_bv 64 ha /\ getr regs1 20 = Z_to_bv 64 (ch_c C) /\ getr regs1 8 = Z_to_bv 64 r /\
getr regs1 21 = Z_to_bv 64 2 /\
hist_mem Lc Ac memc pnew fimg imgl C N.
Definition slots_h (memc : word -> option byte) (ha : Z) : Prop :=
slot memc SL_88 (nha ha) /\ slot memc SL_96 bef /\ slot memc SL_112 (sx32v beffmt).
Definition slots_q (memc : word -> option byte) (ha : Z) : Prop :=
slots_h memc ha /\ slot memc SL_72 fattr /\ slot memc SL_80 img /\ slot memc SL_104 W.
Definition at_CR (regs1 : bvmap 5 word) (Lc : layout) (Ac : astate) (memc : word -> option byte) (mdc : Model)
(ha pnew fimg : Z) (imgl : list Z) (C : cht) (cnt fdp : Z) (fdl pal : list Z) : Prop :=
rgba_inv Lc Ac memc mdc /\ rgba_regs regs1 /\ (fmt = 3 \/ fmt = 4) /\ 1 <= N /\ (ha = 0 \/ (ha = 1 /\ fmt = 4)) /\
getr regs1 14 = Z_to_bv 64 (cnt - 1) /\ getr regs1 25 = Z_to_bv 64 (ch_p C) /\ getr regs1 24 = Z_to_bv 64 fdp /\
getr regs1 9 = Z_to_bv 64 fmt /\ getr regs1 22 = Z_to_bv 64 N /\ getr regs1 20 = Z_to_bv 64 (ch_c C) /\
getr regs1 8 = Z_to_bv 64 r /\ getr regs1 21 = Z_to_bv 64 2 /\
slots_mid memc pnew fimg /\ slots_q memc ha /\
fcfg_at memc fimg 0 0 /\ rgb_obj memc /\ cgif_at memc g s /\ img_at memc imgl /\
chtq_ok memc C cnt pal /\ dense_ok memc fdp fdl pal cnt /\
pnew <> 0 /\ fimg <> 0 /\ fdp <> 0 /\
Permutation (blocks Lc Ac) (BASE s bef beffmt ++ [(pnew, fmt * N); (fimg, N)] ++ cht_blks C ++ [(fdp, 4 * cnt)]).
Definition tree_ok (memc : word -> option byte) (t : tree) : Prop :=
tree_at segs memc t /\ tree_full t /\ Z.of_nat (tree_height t) <= TREE_HMAX /\ tree_forall tnode_wf t /\
(forall n, In n (tree_nodes t) -> 4096 <= tn_addr n /\ tn_addr n + NODE_SIZE <= alloc_ceiling /\ tn_addr n mod 16 = 0).
Definition at_QT (regs1 : bvmap 5 word) (Lc : layout) (Ac : astate) (memc : word -> option byte) (mdc : Model)
(ha pnew fimg : Z) (imgl : list Z) (C : cht) (cnt fdp : Z) (pal : list Z) (t : tree) : Prop :=
rgba_inv Lc Ac memc mdc /\ rgba_regs regs1 /\ (fmt = 3 \/ fmt = 4) /\ 1 <= N /\ (ha = 0 \/ (ha = 1 /\ fmt = 4)) /\ 256 <= cnt /\
getr regs1 12 = Z_to_bv 64 (troot t) /\ getr regs1 9 = Z_to_bv 64 (troot t)   /\
getr regs1 24 = Z_to_bv 64 fdp /\ getr regs1 18 = Z_to_bv 64 fmt /\
getr regs1 22 = Z_to_bv 64 N /\ getr regs1 20 = Z_to_bv 64 (ch_c C) /\ getr regs1 8 = Z_to_bv 64 r /\
getr regs1 21 = Z_to_bv 64 2 /\
slots_mid memc pnew fimg /\ slots_q memc ha /\
fcfg_at memc fimg 0 0 /\ rgb_obj memc /\ cgif_at memc g s /\ img_at memc imgl /\
chtq_ok memc C cnt pal /\ tree_ok memc t /\
pnew <> 0 /\ fimg <> 0 /\ fdp <> 0 /\
Permutation (blocks Lc Ac) (BASE s bef beffmt ++ [(pnew, fmt * N); (fimg, N)] ++ cht_blks C ++ [(fdp, 4 * cnt)] ++ tree_blocks t).
Definition quant_regs (regs1 : bvmap 5 word) (flt pnew fimg ha : Z) (C : cht) (t : tree) : Prop :=
getr regs1 10 = Z_to_bv 64 flt /\ getr regs1 11 = Z_to_bv 64 (Z.land fattr 2) /\ getr regs1 17 = Z_to_bv 64 (nha ha) /\
getr regs1 1 = Z_to_bv 64 W /\ getr regs1 27 = Z_to_bv 64 (troot t) /\ getr regs1 24 = Z_to_bv 64 pnew /\
getr regs1 26 = Z_to_bv 64 fmt /\ getr regs1 22 = Z_to_bv 64 N /\ getr regs1 25 = Z_to_bv 64 fimg /\
getr regs1 20 = Z_to_bv 64 (ch_c C) /\ getr regs1 8 = Z_to_bv 64 r.
Definition quant_mem (Lc : layout) (Ac : astate) (memc : word -> option byte) (ha pnew fimg : Z) (imgl : list Z)
(C : cht) (pal : list Z) (t : tree) (flt : Z) : Prop :=
slots_mid memc pnew fimg /\ slots_q memc ha /\
fcfg_at memc fimg 0 0 /\ rgb_obj memc /\ cgif_at memc g s /\ img_at memc imgl /\
chtq_ok memc C 255 pal /\ tree_ok memc t /\
pnew <> 0 /\ fimg <> 0 /\ flt <> 0 /\
Permutation (blocks Lc Ac) (BASE s bef beffmt ++ [(pnew, fmt * N); (fimg, N)] ++ cht_blks C ++ tree_blocks t ++ [(flt, 4 * (fmt * N))]).
Definition at_DI (regs1 : bvmap 5 word) (Lc : layout) (Ac : astate) (memc : word -> option byte) (mdc : Model)
(ha pnew fimg : Z) (imgl : list Z) (C : cht) (cnt : Z) (pal : list Z) (t : tree) (flt : Z) : Prop :=
rgba_inv Lc Ac memc mdc /\ rgba_regs regs1 /\ (fmt = 3 \/ fmt = 4) /\ 1 <= N /\ (ha = 0 \/ (ha = 1 /\ fmt = 4)) /\
Z.land fattr 2 = 0 /\ quant_regs regs1 flt pnew fimg ha C t /\
slots_mid memc pnew fimg /\ slots_q memc ha /\
fcfg_at memc fimg 0 0 /\ rgb_obj memc /\ cgif_at memc g s /\ img_at memc imgl /\
chtq_ok memc C cnt pal /\ tree_ok memc t /\
pnew <> 0 /\ fimg <> 0 /\ flt <> 0 /\
Permutation (blocks Lc Ac) (BASE s bef beffmt ++ [(pnew, fmt * N); (fimg, N)] ++ cht_blks C ++ tree_blocks t ++ [(flt, 4 * (fmt * N))]).
Definition at_ND (regs1 : bvmap 5 word) (Lc : layout) (Ac : astate) (memc : word -> option byte) (mdc : Model)
(ha pnew fimg : Z) (imgl : list Z) (C : cht) (cnt : Z) (pal : list Z) (t : tree) (flt : Z) : Prop :=
rgba_inv Lc Ac memc mdc /\ rgba_regs regs1 /\ (fmt = 3 \/ fmt = 4) /\ 1 <= N /\ (ha = 0 \/ (ha = 1 /\ fmt = 4)) /\
Z.land fattr 2 <> 0 /\ quant_regs regs1 flt pnew fimg ha C t /\
slots_mid memc pnew fimg /\ slots_q memc ha /\
fcfg_at memc fimg 0 0 /\ rgb_obj memc /\ cgif_at memc g s /\ img_at memc imgl /\
chtq_ok memc C cnt pal /\ tree_ok memc t /\
pnew <> 0 /\ fimg <> 0 /\ flt <> 0 /\
Permutation (blocks Lc Ac) (BASE s bef beffmt ++ [(pnew, fmt * N); (fimg, N)] ++ cht_blks C ++ tree_blocks t ++ [(flt, 4 * (fmt * N))]).
Definition at_QE (regs1 : bvmap 5 word) (Lc : layout) (Ac : astate) (memc : word -> option byte) (mdc : Model)
(ha pnew fimg : Z) (imgl : list Z) (C : cht) (cnt : Z) (pal : list Z) (t : tree) (flt : Z) : Prop :=
rgba_inv Lc Ac memc mdc /\ rgba_regs regs1 /\ (fmt = 3 \/ fmt = 4) /\ 1 <= N /\ (ha = 0 \/ (ha = 1 /\ fmt = 4)) /\
getr regs1 10 = Z_to_bv 64 flt /\ getr regs1 27 = Z_to_bv 64 (troot t) /\ getr regs1 20 = Z_to_bv 64 (ch_c C) /\
getr regs1 8 = Z_to_bv 64 r /\ getr regs1 24 = Z_to_bv 64 pnew /\
slots_mid memc pnew fimg /\ slots_q memc ha /\
fcfg_at memc fimg 0 0 /\ rgb_obj memc /\ cgif_at memc g s /\ img_at memc imgl /\
chtq_ok memc C cnt pal /\ tree_ok memc t /\
pnew <> 0 /\ fimg <> 0 /\ flt <> 0 /\
Permutation (blocks Lc Ac) (BASE s bef beffmt ++ [(pnew, fmt * N); (fimg, N)] ++ cht_blks C ++ tree_blocks t ++ [(flt, 4 * (fmt * N))]).
Definition at_SM (regs1 : bvmap 5 word) (Lc : layout) (Ac : astate) (memc : word -> option byte) (mdc : Model)
(ha pnew fimg : Z) (imgl : list Z) (C : cht) : Prop :=
rgba_inv Lc Ac memc mdc /\ rgba_regs regs1 /\ (fmt = 3 \/ fmt = 4) /\ 1 <= N /\ (ha = 0 \/ (ha = 1 /\ fmt = 4)) /\
ht_cnt (ch_H C) < 256 /\
getr regs1 9 = Z_to_bv 64 fmt /\ getr regs1 18 = Z_to_bv 64 (ht_cnt (ch_H C)) /\ getr regs1 23 = Z_to_bv 64 img /\
getr regs1 22 = Z_to_bv 64 N /\ getr regs1 19 = Z_to_bv 64 cfp /\ getr regs1 25 = Z_to_bv 64 fimg /\
getr regs1 20 = Z_to_bv 64 (ch_c C) /\ getr regs1 8 = Z_to_bv 64 r /\
slots_mid memc pnew fimg /\ slots_h memc ha /\
fcfg_at memc fimg 0 0 /\ rgb_obj memc /\ cgif_at memc g s /\ img_at memc imgl /\
obj_at segs memc (ch_c C) LAY_Cht [ch_f C; ch_h C; ch_u C; ch_p C; ch_x C; ht_cnt (ch_H C); ch_T C] /\
cht_arrays segs memc (ch_f C) (ch_h C) (ch_u C) (ch_p C) (ch_x C) (ch_H C) /\
ht_inv (ch_H C) (ch_ent C) /\ ht_T (ch_H C) = ch_T C /\ In (ch_T C) ts_chain /\
pnew <> 0 /\ fimg <> 0 /\
Permutation (blocks Lc Ac) (BASE s bef beffmt ++ [(pnew, fmt * N); (fimg, N)] ++ cht_blks C).
Definition at_FIN (regs1 : bvmap 5 word) (Lc : layout) (Ac : astate) (memc : word -> option byte) (mdc : Model)
(ha pnew fimg sizeLCT : Z) : Prop :=
rgba_inv Lc Ac memc mdc /\ rgba_regs regs1 /\ (fmt = 3 \/ fmt = 4) /\ 1 <= N /\ (ha = 0 \/ (ha = 1 /\ fmt = 4)) /\ 0 <= sizeLCT <= 255 /\
getr regs1 9 = Z_to_bv 64 sizeLCT /\ getr regs1 8 = Z_to_bv 64 r /\ getr regs1 24 = Z_to_bv 64 pnew /\
slots_mid memc pnew fimg /\ slot memc SL_88 (nha ha) /\
fcfg_at memc fimg 0 0 /\ rgb_obj memc /\ cgif_at memc g s /\
(forall i, 0 <= i < 768 -> exists b, mbyte segs memc (sp + OFF_apal + i) = Some b) /\
pnew <> 0 /\ fimg <> 0 /\
Permutation (blocks Lc Ac) (BASE s bef beffmt ++ [(pnew, fmt * N); (fimg, N)]).
Definition rgb_obj2 (memc : word -> option byte) (bef' beffmt' cur1 : Z) : Prop :=
obj_at segs memc r LAY_Rgb [g; wfn; ctx; path; attr; gen; loops; W; H; bef'; beffmt'; cur1].
Definition at_XF (regs1 : bvmap 5 word) (Lc : layout) (Ac : astate) (memc : word -> option byte) (mdc : Model)
(res tb tn : Z) (s' : cgif_st) (bef' beffmt' cur1 : Z) : Prop :=
rgba_inv Lc Ac memc mdc /\ rgba_regs regs1 /\ 0 <= res < 2 ^ 64 /\
getr regs1 25 = Z_to_bv 64 tb /\ getr regs1 21 = Z_to_bv 64 res /\ getr regs1 8 = Z_to_bv 64 r /\
rgb_obj2 memc bef' beffmt' cur1 /\ cgif_at memc g s' /\ cgif_wf s' N /\
cg_W s' = W /\ cg_H s' = H /\ cg_attr s' = cg_attr s /\ cg_raw s' = cg_raw s /\
(bef' = 0 \/ beffmt' = 3 \/ beffmt' = 4) /\ tb <> 0 /\
~ In (tb, tn) (blocks L A) /\
Permutation (blocks Lc Ac) (BASE s' bef' beffmt' ++ [(tb, tn)]).
Definition at_XS (regs1 : bvmap 5 word) (Lc : layout) (Ac : astate) (memc : word -> option byte) (mdc : Model)
(res : Z) (s' : cgif_st) (bef' beffmt' cur1 : Z) : Prop :=
rgba_inv Lc Ac memc mdc /\ rgba_regs regs1 /\ 0 <= res < 2 ^ 64 /\
getr regs1 21 = Z_to_bv 64 res /\ getr regs1 8 = Z_to_bv 64 r /\
rgb_obj2 memc bef' beffmt' cur1 /\ cgif_at memc g s' /\ cgif_wf s' N /\
cg_W s' = W /\ cg_H s' = H /\ cg_attr s' = cg_attr s /\ cg_raw s' = cg_raw s /\
(bef' = 0 \/ beffmt' = 3 \/ beffmt' = 4) /\
Permutation (blocks Lc Ac) (BASE s' bef' beffmt').
Definition at_XB (regs1 : bvmap 5 word) (Lc : layout) (Ac : astate) (memc : word -> option byte) (mdc : Model)
(pnew fimg : Z) : Prop :=
rgba_inv Lc Ac memc mdc /\ rgba_regs regs1 /\ (fmt = 3 \/ fmt = 4) /\
getr regs1 9 = Z_to_bv 64 pnew /\ getr regs1 25 = Z_to_bv 64 fimg /\ getr regs1 21 = Z_to_bv 64 2 /\
getr regs1 8 = Z_to_bv 64 r /\
rgb_obj memc /\ cgif_at memc g s /\ pnew <> 0 /\ fimg <> 0 /\
Permutation (blocks Lc Ac) (BASE s bef beffmt ++ [(pnew, fmt * N); (fimg, N)]).
Definition at_X38 (regs1 : bvmap 5 word) (Lc : layout) (Ac : astate) (memc : word -> option byte) (mdc : Model)
(pnew fimg c f h u p x cnt0 ts0 : Z) : Prop :=
rgba_inv Lc Ac memc mdc /\ rgba_regs regs1 /\ (fmt = 3 \/ fmt = 4) /\
getr regs1 20 = Z_to_bv 64 c /\ getr regs1 9 = Z_to_bv 64 pnew /\ getr regs1 25 = Z_to_bv 64 fimg /\
getr regs1 21 = Z_to_bv 64 2 /\ getr regs1 8 = Z_to_bv 64 r /\
rgb_obj memc /\ cgif_at memc g s /\ pnew <> 0 /\ fimg <> 0 /\
obj_at segs memc c LAY_Cht [f; h; u; p; x; cnt0; ts0] /\
Permutation (blocks Lc Ac) (BASE s bef beffmt ++ [(pnew, fmt * N); (fimg, N); (c, CHT_SIZE)] ++
optb f (4 * TS0) ++ optb h (3 * TS0) ++ optb u TS0 ++ optb p (3 * TS0) ++ optb x (4 * TS0)).
Definition at_XC (regs1 : bvmap 5 word) (Lc : layout) (Ac : astate) (memc : word -> option byte) (mdc : Model)
(ha pnew fimg : Z) (C : cht) (cnt : Z) (pal : list Z) : Prop :=
rgba_inv Lc Ac memc mdc /\ rgba_regs regs1 /\ (fmt = 3 \/ fmt = 4) /\
getr regs1 20 = Z_to_bv 64 (ch_c C) /\ getr regs1 25 = Z_to_bv 64 fimg /\ getr regs1 21 = Z_to_bv 64 2 /\
getr regs1 8 = Z_to_bv 64 r /\
slots_mid memc pnew fimg /\ rgb_obj memc /\ cgif_at memc g s /\ chtq_ok memc C cnt pal /\
pnew <> 0 /\ fimg <> 0 /\
Permutation (blocks Lc Ac) (BASE s bef beffmt ++ [(pnew, fmt * N); (fimg, N)] ++ cht_blks C).
Definition at_XD (regs1 : bvmap 5 word) (Lc : layout) (Ac : astate) (memc : word -> option byte) (mdc : Model)
(ha pnew fimg : Z) (C : cht) (cnt : Z) (pal : list Z) (fdp fdn : Z) : Prop :=
rgba_inv Lc Ac memc mdc /\ rgba_regs regs1 /\ (fmt = 3 \/ fmt = 4) /\
getr regs1 24 = Z_to_bv 64 fdp /\ getr regs1 20 = Z_to_bv 64 (ch_c C) /\ getr regs1 21 = Z_to_bv 64 2 /\
getr regs1 8 = Z_to_bv 64 r /\
slots_mid memc pnew fimg /\ rgb_obj memc /\ cgif_at memc g s /\ chtq_ok memc C cnt pal /\
pnew <> 0 /\ fimg <> 0 /\ fdp <> 0 /\
Permutation (blocks Lc Ac) (BASE s bef beffmt ++ [(pnew, fmt * N); (fimg, N)] ++ cht_blks C ++ [(fdp, fdn)]).
Definition at_XT (regs1 : bvmap 5 word) (Lc : layout) (Ac : astate) (memc : word -> option byte) (mdc : Model)
(ha pnew fimg : Z) (C : cht) (cnt : Z) (pal : list Z) (fdp fdn : Z) (t : tree) : Prop :=
rgba_inv Lc Ac memc mdc /\ rgba_regs regs1 /\ (fmt = 3 \/ fmt = 4) /\
getr regs1 9 = Z_to_bv 64 (troot t) /\ getr regs1 24 = Z_to_bv 64 fdp /\ getr regs1 20 = Z_to_bv 64 (ch_c C) /\
getr regs1 21 = Z_to_bv 64 2 /\ getr regs1 8 = Z_to_bv 64 r /\
slots_mid memc pnew fimg /\ rgb_obj memc /\ cgif_at memc g s /\ chtq_ok memc C cnt pal /\
tree_at segs memc t /\ Z.of_nat (tree_height t) <= TREE_HMAX /\
pnew <> 0 /\ fimg <> 0 /\ fdp <> 0 /\
Permutation (blocks Lc Ac) (BASE s bef beffmt ++ [(pnew, fmt * N); (fimg, N)] ++ cht_blks C ++ [(fdp, fdn)] ++ tree_blocks t).
Definition at_XT2 (regs1 : bvmap 5 word) (Lc : layout) (Ac : astate) (memc : word -> option byte) (mdc : Model)
(ha pnew fimg : Z) (C : cht) (cnt : Z) (pal : list Z) (t : tree) : Prop :=
rgba_inv Lc Ac memc mdc /\ rgba_regs regs1 /\ (fmt = 3 \/ fmt = 4) /\
getr regs1 23 = Z_to_bv 64 (troot t) /\ getr regs1 25 = Z_to_bv 64 fimg /\ getr regs1 20 = Z_to_bv 64 (ch_c C) /\
getr regs1 21 = Z_to_bv 64 2 /\ getr regs1 8 = Z_to_bv 64 r /\
slots_mid memc pnew fimg /\ rgb_obj memc /\ cgif_at memc g s /\ chtq_ok memc C cnt pal /\
tree_at segs memc t /\ Z.of_nat (tree_height t) <= TREE_HMAX /\
pnew <> 0 /\ fimg <> 0 /\
Permutation (blocks Lc Ac) (BASE s bef beffmt ++ [(pnew, fmt * N); (fimg, N)] ++ cht_blks C ++ tree_blocks t).
Definition cfg_at (regs1 : bvmap 5 word) (pc : Z) (memc : word -> option byte) (mdc : Model) : config :=
mkCfg (mkst regs1 (Z_to_bv 64 pc) memc rom) mdc.
Definition cfg_atF (fx1 : FPState) (regs1 : bvmap 5 word) (pc : Z) (memc : word -> option byte) (mdc : Model) : config :=
mkCfg (@mkst fx1 regs1 (Z_to_bv 64 pc) memc rom) mdc.
Definition K_A1 : Prop := forall regs1 Lc Ac memc mdc pnew fimg imgl,
at_A1 regs1 Lc Ac memc mdc pnew fimg imgl -> SR segs (cfg_at regs1 PC_A1 memc mdc) rgba_post.
Definition K_HL (i : Z) : Prop := forall regs1 Lc Ac memc mdc ha pnew fimg imgl C,
at_HL regs1 Lc Ac memc mdc i ha pnew fimg imgl C -> SR segs (cfg_at regs1 PC_HL memc mdc) rgba_post.
Definition K_RS (i : Z) : Prop := forall regs1 Lc Ac memc mdc ha pnew fimg imgl C,
at_RS regs1 Lc Ac memc mdc i ha pnew fimg imgl C -> SR segs (cfg_at regs1 PC_RS memc mdc) rgba_post.
Definition K_HD : Prop := forall regs1 Lc Ac memc mdc ha pnew fimg imgl C,
at_HD regs1 Lc Ac memc mdc ha pnew fimg imgl C -> SR segs (cfg_at regs1 PC_HD memc mdc) rgba_post.
Definition K_CR : Prop := forall fx1 regs1 Lc Ac memc mdc ha pnew fimg imgl C cnt fdp fdl pal,
frm_zero (@fp_csr fx1) ->
at_CR regs1 Lc Ac memc mdc ha pnew fimg imgl C cnt fdp fdl pal -> SR segs (cfg_atF fx1 regs1 PC_CR memc mdc) rgba_post.
Definition K_QT : Prop := forall fx1 regs1 Lc Ac memc mdc ha pnew fimg imgl C cnt fdp pal t,
frm_zero (@fp_csr fx1) ->
at_QT regs1 Lc Ac memc mdc ha pnew fimg imgl C cnt fdp pal t -> SR segs (cfg_atF fx1 regs1 PC_QT memc mdc) rgba_post.
Definition K_DI : Prop := forall fx1 regs1 Lc Ac memc mdc ha pnew fimg imgl C cnt pal t flt,
frm_zero (@fp_csr fx1) ->
at_DI regs1 Lc Ac memc mdc ha pnew fimg imgl C cnt pal t flt -> SR segs (cfg_atF fx1 regs1 PC_DI memc mdc) rgba_post.
Definition K_ND : Prop := forall fx1 regs1 Lc Ac memc mdc ha pnew fimg imgl C cnt pal t flt,
frm_zero (@fp_csr fx1) ->
at_ND regs1 Lc Ac memc mdc ha pnew fimg imgl C cnt pal t flt -> SR segs (cfg_atF fx1 regs1 PC_ND memc mdc) rgba_post.
Definition K_QE : Prop := forall fx1 regs1 Lc Ac memc mdc ha pnew fimg imgl C cnt pal t flt,
frm_zero (@fp_csr fx1) ->
at_QE regs1 Lc Ac memc mdc ha pnew fimg imgl C cnt pal t flt -> SR segs (cfg_atF fx1 regs1 PC_QE memc mdc) rgba_post.
Definition K_SM : Prop := forall regs1 Lc Ac memc mdc ha pnew fimg imgl C,
at_SM regs1 Lc Ac memc mdc ha pnew fimg imgl C -> SR segs (cfg_at regs1 PC_SM memc mdc) rgba_post.
Definition K_FIN : Prop := forall fx1 regs1 Lc Ac memc mdc ha pnew fimg sizeLCT,
frm_zero (@fp_csr fx1) ->
at_FIN regs1 Lc Ac memc mdc ha pnew fimg sizeLCT -> SR segs (cfg_atF fx1 regs1 PC_FIN memc mdc) rgba_post.
Definition K_XF : Prop := forall fx1 regs1 Lc Ac memc mdc res tb tn s' bef' beffmt' cur1,
frm_zero (@fp_csr fx1) ->
at_XF regs1 Lc Ac memc mdc res tb tn s' bef' beffmt' cur1 -> SR segs (cfg_atF fx1 regs1 PC_XF memc mdc) rgba_post.
Definition K_XS : Prop := forall fx1 regs1 Lc Ac memc mdc res s' bef' beffmt' cur1,
frm_zero (@fp_csr fx1) ->
at_XS regs1 Lc Ac memc mdc res s' bef' beffmt' cur1 -> SR segs (cfg_atF fx1 regs1 PC_XS memc mdc) rgba_post.
Definition K_XB : Prop := forall regs1 Lc Ac memc mdc pnew fimg,
at_XB regs1 Lc Ac memc mdc pnew fimg -> SR segs (cfg_at regs1 PC_XB memc mdc) rgba_post.
Definition K_X38 : Prop := forall regs1 Lc Ac memc mdc pnew fimg c f h u p x cnt0 ts0,
at_X38 regs1 Lc Ac memc mdc pnew fimg c f h u p x cnt0 ts0 -> SR segs (cfg_at regs1 PC_X38 memc mdc) rgba_post.
Definition K_XC : Prop := forall fx1 regs1 Lc Ac memc mdc ha pnew fimg C cnt pal,
frm_zero (@fp_csr fx1) ->
at_XC regs1 Lc Ac memc mdc ha pnew fimg C cnt pal -> SR segs (cfg_atF fx1 regs1 PC_XC memc mdc) rgba_post.
Definition K_XD : Prop := forall fx1 regs1 Lc Ac memc mdc ha pnew fimg C cnt pal fdp fdn,
frm_zero (@fp_csr fx1) ->
at_XD regs1 Lc Ac memc mdc ha pnew fimg C cnt pal fdp fdn -> SR segs (cfg_atF fx1 regs1 PC_XD memc mdc) rgba_post.
Definition K_XT : Prop := forall fx1 regs1 Lc Ac memc mdc ha pnew fimg C cnt pal fdp fdn t,
frm_zero (@fp_csr fx1) ->
at_XT regs1 Lc Ac memc mdc ha pnew fimg C cnt pal fdp fdn t -> SR segs (cfg_atF fx1 regs1 PC_XT memc mdc) rgba_post.
Definition K_XT2 : Prop := forall fx1 regs1 Lc Ac memc mdc ha pnew fimg C cnt pal t,
frm_zero (@fp_csr fx1) ->
at_XT2 regs1 Lc Ac memc mdc ha pnew fimg C cnt pal t -> SR segs (cfg_atF fx1 regs1 PC_XT2 memc mdc) rgba_post.
Definition seg_E1 : Prop := K_A1 -> K_XS -> K_XF -> rgba_pre -> SR segs (cfg_at regs0 PC_E1 mem0 md0) rgba_post.
Definition seg_E2 : Prop := K_HL 0 -> K_X38 -> K_XB -> K_A1.
Definition seg_HB (i : Z) : Prop := K_HL (i + 1) -> K_HD -> K_RS i -> K_HL i.
Definition seg_HR (i : Z) : Prop := K_HL (i + 1) -> K_HD -> K_XB -> K_RS i.
Definition seg_Q0 : Prop := K_SM -> K_CR -> K_XC -> K_HD.
Definition seg_CR : Prop := K_QT -> K_XD -> K_XT -> K_CR.
Definition seg_QT : Prop := K_DI -> K_ND -> K_XT2 -> K_QT.
Definition seg_DI : Prop := K_QE -> K_DI.
Definition seg_ND : Prop := K_QE -> K_ND.
Definition seg_QE : Prop := K_FIN -> K_QE.
Definition seg_SM : Prop := K_FIN -> K_SM.
Definition seg_FIN : Prop := K_XF -> K_FIN.
Definition seg_X38 : Prop := K_XB -> K_X38.
Definition seg_XB : Prop := K_XF -> K_XB.
Definition seg_XF : Prop := K_XS -> K_XF.
Definition seg_XS : Prop := K_XS.
Definition seg_XC : Prop := K_XF -> K_XC.
Definition seg_XD : Prop := K_XC -> K_XD.
Definition seg_XT : Prop := K_XD -> K_XT.
Definition seg_XT2 : Prop := K_XC -> K_XT2.
Lemma src2_rgbadd_E1 : seg_E1. Proof. Abort.
Lemma src2_rgbadd_E2 : seg_E2. Proof. Abort.
Lemma src2_rgbadd_HB : forall i, seg_HB i. Proof. Abort.
Lemma src2_rgbadd_HR : forall i, seg_HR i. Proof. Abort.
Lemma src2_rgbadd_Q0 : seg_Q0. Proof. Abort.
Lemma src2_rgbadd_CR : seg_CR. Proof. Abort.
Lemma src2_rgbadd_QT : seg_QT. Proof. Abort.
Lemma src2_rgbadd_DI : seg_DI. Proof. Abort.
Lemma src2_rgbadd_ND : seg_ND. Proof. Abort.
Lemma src2_rgbadd_QE : seg_QE. Proof. Abort.
Lemma src2_rgbadd_SM : seg_SM. Proof. Abort.
Lemma src2_rgbadd_FIN : seg_FIN. Proof. Abort.
Lemma src2_rgbadd_X38 : seg_X38. Proof. Abort.
Lemma src2_rgbadd_XB : seg_XB. Proof. Abort.
Lemma src2_rgbadd_XF : seg_XF. Proof. Abort.
Lemma src2_rgbadd_XS : seg_XS. Proof. Abort.
Lemma src2_rgbadd_XC : seg_XC. Proof. Abort.
Lemma src2_rgbadd_XD : seg_XD. Proof. Abort.
Lemma src2_rgbadd_XT : seg_XT. Proof. Abort.
Lemma src2_rgbadd_XT2 : seg_XT2. Proof. Abort.
Definition all_segments : Prop :=
seg_E1 /\ seg_E2 /\ (forall i, seg_HB i) /\ (forall i, seg_HR i) /\ seg_Q0 /\ seg_CR /\ seg_QT /\
seg_DI /\ seg_ND /\ seg_QE /\ seg_SM /\ seg_FIN /\ seg_X38 /\ seg_XB /\ seg_XF /\ seg_XS /\
seg_XC /\ seg_XD /\ seg_XT /\ seg_XT2.
Lemma K_HL_all : (forall i, seg_HB i) -> (forall i, seg_HR i) -> K_HD -> K_XB ->
forall n i, N - i <= Z.of_nat n -> K_HL i.
Proof.
intros HB HR HD XB. induction n as [|n IH]; intros i Hn.
- intros regs1 Lc Ac memc mdc ha pnew fimg imgl C (_ & _ & _ & Hi & _). exfalso. cbn in Hn. lia.
- assert (K1 : K_HL (i + 1)) by (apply IH; rewrite Nat2Z.inj_succ in Hn; lia).
exact (HB i K1 HD (HR i K1 HD XB)).
Qed.
Theorem rgba_composed : all_segments -> rgba_pre -> SR segs (cfg_at regs0 PC_E1 mem0 md0) rgba_post.
Proof.
intros (E1 & E2 & HB & HR & Q0 & CR & QT & DI & ND & QE & SM & FIN & X38 & XB & XF & XS & XC & XD & XT & XT2) PRE.
pose proof (XF XS) as KXF.
pose proof (XB KXF) as KXB.
pose proof (XC KXF) as KXC.
pose proof (XD KXC) as KXD.
pose proof (FIN KXF) as KFIN.
pose proof (QE KFIN) as KQE.
pose proof (SM KFIN) as KSM.
pose proof (DI KQE) as KDI.
pose proof (ND KQE) as KND.
pose proof (QT KDI KND (XT2 KXC)) as KQT.
pose proof (CR KQT KXD (XT KXD)) as KCR.
pose proof (Q0 KSM KCR KXC) as KHD.
assert (KHL0 : K_HL 0).
{ destruct (Z_lt_le_dec 0 N) as [HN|HN].
- apply (K_HL_all HB HR KHD KXB (Z.to_nat N)). lia.
- intros regs1 Lc Ac memc mdc ha pnew fimg imgl C (_ & _ & _ & Hi & _). exfalso. lia. }
exact (E1 (E2 KHL0 (X38 KXB) KXB) XS KXF PRE).
Qed.
End d.
Theorem rgb_addframe_of_segments (API : AllocAPI src2_msyms) :
(forall L A regs0 mem0 md0 r cfp g wfn ctx path attr gen loops W H bef beffmt cur s N img fmt fattr fgen delay rest,
all_segments API L A regs0 mem0 md0 r cfp g wfn ctx path attr gen loops W H bef beffmt cur s N img fmt fattr fgen delay rest) ->
rgb_addframe_spec API.
Proof.
intros ALL. unfold rgb_addframe_spec.
intros L A regs mem md r cfp g wfn ctx path attr gen loops W H bef beffmt cur s N img fmt fattr fgen delay rest
HPRE Hid Hfrm G10 G11 Hc8 Hclo Hchi Hcf Hobj Hat Hwf HW HH HN Hbf Hro HB.
eapply SR_mono.
- apply (rgba_composed API L A regs mem md r cfp g wfn ctx path attr gen loops W H bef beffmt cur s N img fmt fattr fgen delay rest
(ALL L A regs mem md r cfp g wfn ctx path attr gen loops W H bef beffmt cur s N img fmt fattr fgen delay rest)).
unfold rgba_pre. repeat (split; [assumption|]). exact HB.
- intros c' Hc. exact Hc.
Qed.
End a.
