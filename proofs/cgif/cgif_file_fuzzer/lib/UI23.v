(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require YZ00.
From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YK11 YK0s YK15 YM06 YP09.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YO0i YO0f YO0d YO03
YO0p YO0j YO0m YO0l YO0n YO0k YO0o.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import UH00 UH03 UH02 YI06 UI5b YI09 YI00.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YI16 YI17 YI14 UI5c UI21 UI3u UI22 YI5a.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require YO07.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YO08.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Open Scope Z_scope.
Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Section d.
Variable API : AllocAPI ubs0_msyms.
Let MR : MR_t := aa_MR API.
Definition rfc_specX : Prop :=
forall STK sp0 FP L A mem md Lc Ac memc mdc (regs : bvmap 5 word) (Bb : list (Z * Z)) (st dst N pdata nb cur : Z) (PAYLOAD : list Z) (b : rbound),
journal ubs0_msyms MR STK sp0 FP L A mem md Lc Ac memc mdc -> st_init_done Ac = true ->
(forall blk, In blk (blocks L A) -> In blk Bb) -> Permutation (blocks Lc Ac) Bb -> In (pdata, nb) Bb ->
YK0s.ret_ok (getr regs 1) -> getr regs 4 = Z_to_bv 64 (ms_tp ubs0_msyms) ->
getr regs 10 = Z_to_bv 64 st -> getr regs 11 = Z_to_bv 64 dst -> getr regs 12 = Z_to_bv 64 N ->
spZ regs mod 16 = 0 -> sp0 - STK <= spZ regs - RFC_STK -> spZ regs <= st -> st + 24 <= sp0 ->
spZ regs <= dst -> dst + 32 <= sp0 -> (st + 24 <= dst \/ dst + 32 <= st) -> st mod 8 = 0 -> dst mod 8 = 0 -> sp0 < 2 ^ 63 ->
1 <= N <= 100000000 -> 0 <= cur <= nb -> 0 < nb ->
word_mem ubs0segs memc st pdata -> word_mem ubs0segs memc (st + 8) nb -> word_mem ubs0segs memc (st + 16) cur ->
garr8 ubs0segs memc pdata PAYLOAD -> Z.of_nat (length PAYLOAD) = nb ->
res_ok Ac b -> rfc_room b N ->
SR ubs0segs (mkCfg (mkst regs (Z_to_bv 64 ubs0_A_read_frameconfig) memc (seg_rom ubs0segs)) mdc)
(fun c' => exists L2 A2 regs2 mem2 md2 (res cur2 : Z),
c' = mkCfg (mkst regs2 (getr regs 1) mem2 (seg_rom ubs0segs)) md2 /\
journal ubs0_msyms MR STK sp0 FP L A mem md L2 A2 mem2 md2 /\
st_init_done A2 = true /\ regs_preserved regs regs2 /\
getr regs2 10 = Z_to_bv 64 res /\
(forall a, alloc_ceiling <= a < 2 ^ 64 ->
~ (spZ regs - RFC_STK <= a < spZ regs) -> ~ (dst <= a < dst + 32) -> ~ (st + 16 <= a < st + 24) ->
mbyte ubs0segs mem2 a = mbyte ubs0segs memc a) /\
(forall blk m i, In (blk, m) Bb -> 0 <= i < m -> mbyte ubs0segs mem2 (blk + i) = mbyte ubs0segs memc (blk + i)) /\
word_mem ubs0segs mem2 st pdata /\ word_mem ubs0segs mem2 (st + 8) nb /\
word_mem ubs0segs mem2 (st + 16) cur2 /\ cur <= cur2 <= nb /\
((res = 0 /\ fst (fst (parse_frameN N (skipn (Z.to_nat cur) PAYLOAD))) = false /\
(exists leak, Permutation (blocks L2 A2) (leak ++ Bb)) /\ res_ok A2 (rfc_rb_fail b)) \/
(res = 1 /\ exists lpal lpa img fattr fgen delay nlp tidx (LPAL IMG : list Z),
obj_at ubs0segs mem2 dst LAY_FrameConfig [lpal; img; fattr; fgen; delay; nlp; tidx] /\
(Z.land fattr 1 = 0 -> lpal = 0) /\ Z_to_bv 64 lpa = Z_to_bv 64 lpal /\
Permutation (blocks L2 A2) ((img, N) :: (if Z.land fattr 1 =? 0 then [] else [(lpa, 3 * nlp)]) ++ Bb) /\
parse_frameN N (skipn (Z.to_nat cur) PAYLOAD) = (true, (fattr, fgen, delay, tidx, nlp, LPAL, IMG), skipn (Z.to_nat cur2) PAYLOAD) /\
garr8 ubs0segs mem2 img IMG /\ Z.of_nat (length IMG) = N /\
(Z.land fattr 1 <> 0 -> garr8 ubs0segs mem2 lpa LPAL /\ Z.of_nat (length LPAL) = 3 * nlp) /\
res_ok A2 (rfc_rb_ok b fattr nlp N)))).
Definition addframe_specX : Prop :=
forall L A (regs : bvmap 5 word) mem md (g cfp : Z) (s : cgif_st) (N : Z)
(lpal lpa img fattr fgen delay nlp tidx : Z) (rest : list (Z * Z)) (GPAL IMG LPAL : list Z) (gs : YO07.gif_st) (b : rbound),
fn_pre ubs0_msyms MR ADDFRAME_STK L A regs mem md -> st_init_done A = true ->
Z.of_nat (length (concat (YO07.s_out gs))) + FRAME_OUT N <= SINK_MAX ->
spZ regs <= 2 ^ 47 ->
getr regs 10 = Z_to_bv 64 g -> getr regs 11 = Z_to_bv 64 cfp ->
cfp mod 8 = 0 -> spZ regs <= cfp -> cfp + 32 <= 2 ^ 63 ->
obj_at ubs0segs mem cfp LAY_FrameConfig [lpal; img; fattr; fgen; delay; nlp; tidx] ->
cgif_at mem g s -> cgif_wf s N ->
Z_to_bv 64 lpa = Z_to_bv 64 lpal ->
Permutation (blocks L A)
(cgif_blocks g s N ++ (img, N) :: (if Z.land fattr 1 =? 0 then [] else [(lpa, 3 * nlp)]) ++ rest) ->
cgif_rel mem md s N GPAL gs ->
garr8 ubs0segs mem img IMG -> Z.of_nat (length IMG) = N ->
(Z.land fattr 1 <> 0 -> garr8 ubs0segs mem lpa LPAL /\ Z.of_nat (length LPAL) = 3 * nlp) ->
res_ok A b -> af_room b N ->
SR ubs0segs (mkCfg (mkst regs (Z_to_bv 64 ubs0_A_cgif_addframe) mem (seg_rom ubs0segs)) md)
(fun c' => exists L' A' regs' mem' md' (s' : cgif_st),
c' = mkCfg (mkst regs' (getr regs 1) mem' (seg_rom ubs0segs)) md' /\
journal ubs0_msyms MR ADDFRAME_STK (spZ regs) (cgif_fp g s N) L A mem md L' A' mem' md' /\
regs_preserved regs regs' /\ st_init_done A' = true /\
cgif_at mem' g s' /\ cgif_wf s' N /\
cg_W s' = cg_W s /\ cg_H s' = cg_H s /\ cg_attr s' = cg_attr s /\ cg_raw s' = cg_raw s /\ cg_file s' = cg_file s /\
Permutation (blocks L' A')
(cgif_blocks g s' N ++ (img, N) :: (if Z.land fattr 1 =? 0 then [] else [(lpa, 3 * nlp)]) ++ rest) /\
cg_gen s' = cg_gen s /\ cg_ngp s' = cg_ngp s /\ cg_pal s' = cg_pal s /\
cgif_rel mem' md' s' N GPAL (YO07.add_frame (gcfg_of s GPAL) gs fattr fgen delay tidx nlp LPAL IMG) /\
Z.of_nat (length (concat (YO07.s_out (YO07.add_frame (gcfg_of s GPAL) gs fattr fgen delay tidx nlp LPAL IMG))))
<= Z.of_nat (length (concat (YO07.s_out gs))) + FRAME_OUT N /\
res_ok A' (af_rb b N (qcount gs) (qcount (YO07.add_frame (gcfg_of s GPAL) gs fattr fgen delay tidx nlp LPAL IMG)))).
Definition close_specX : Prop :=
forall L A (regs : bvmap 5 word) mem md (g : Z) (s : cgif_st) (N : Z) (rest : list (Z * Z)) (GPAL : list Z) (gs : YO07.gif_st) (b : rbound),
fn_pre ubs0_msyms MR CLOSE_STK L A regs mem md -> st_init_done A = true ->
Z.of_nat (length (concat (YO07.s_out gs))) + CLOSE_OUT N <= SINK_MAX ->
spZ regs <= 2 ^ 47 ->
getr regs 10 = Z_to_bv 64 g ->
cgif_at mem g s -> cgif_wf s N ->
Permutation (blocks L A) (cgif_blocks g s N ++ rest) ->
cgif_rel mem md s N GPAL gs ->
res_ok A b -> close_room b N ->
SR ubs0segs (mkCfg (mkst regs (Z_to_bv 64 ubs0_A_cgif_close) mem (seg_rom ubs0segs)) md)
(fun c' => exists L' A' regs' mem' md',
c' = mkCfg (mkst regs' (getr regs 1) mem' (seg_rom ubs0segs)) md' /\
journal ubs0_msyms MR CLOSE_STK (spZ regs) (cgif_fp g s N) L A mem md L' A' mem' md' /\
regs_preserved regs regs' /\ st_init_done A' = true /\
sink_none ubs0_msyms mem' md' /\
Permutation (blocks L' A') rest /\
Fs.fs_lookup (m_fs md') sink_path = Some (bytes (concat (YO07.close_gif (gcfg_of s GPAL) gs) ++ [59])) /\
res_ok A' (close_rb b N (qcount gs))).
Definition newgif_cfg (W H attr gen ngp : Z) (GPAL : list Z) : YO07.gcfg := YO07.mkG W H attr gen ngp GPAL.
Definition newgif_postA (L : layout) (A : astate) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) (b : rbound) (c' : config) : Prop :=
exists L' A' regs' mem' md',
c' = mkCfg (mkst regs' (getr regs 1) mem' (seg_rom ubs0segs)) md' /\
journal ubs0_msyms MR NEWGIF_STK (spZ regs) [sink_token] L A mem md L' A' mem' md' /\
regs_preserved regs regs' /\ st_init_done A' = true /\
getr regs' 10 = Z_to_bv 64 0 /\
Permutation (blocks L' A') (blocks L A) /\ sink_none ubs0_msyms mem' md' /\ m_fs md' = m_fs md /\
res_ok A' (newgif_rb b).
Definition newgif_postB0 (L : layout) (A : astate) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) (b : rbound) (c' : config) : Prop :=
exists L' A' regs' mem' md',
c' = mkCfg (mkst regs' (getr regs 1) mem' (seg_rom ubs0segs)) md' /\
journal ubs0_msyms MR NEWGIF_STK (spZ regs) [sink_token] L A mem md L' A' mem' md' /\
regs_preserved regs regs' /\ st_init_done A' = true /\
getr regs' 10 = Z_to_bv 64 0 /\
Permutation (blocks L' A') (blocks L A) /\ sink_none ubs0_msyms mem' md' /\
Fs.fs_lookup (m_fs md') sink_path = Some (bytes []) /\
res_ok A' (newgif_rb b).
Definition newgif_postB1 (L : layout) (A : astate) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) (b : rbound)
(attr gen W H ngp loops : Z) (GPAL : list Z) (c' : config) : Prop :=
exists L' A' regs' mem' md' (res : Z) (s : cgif_st),
c' = mkCfg (mkst regs' (getr regs 1) mem' (seg_rom ubs0segs)) md' /\
journal ubs0_msyms MR NEWGIF_STK (spZ regs) [sink_token] L A mem md L' A' mem' md' /\
regs_preserved regs regs' /\ st_init_done A' = true /\
getr regs' 10 = Z_to_bv 64 res /\ res <> 0 /\
cgif_at mem' res s /\ cgif_wf s (W * H) /\
cg_frames s = [None; None; None] /\ cg_W s = W /\ cg_H s = H /\ cg_attr s = attr /\
cg_cur s = R_PENDING /\ cg_ihead s = 1 /\ cg_gen s = gen /\ cg_ngp s = ngp /\
Permutation (blocks L' A') (cgif_blocks res s (W * H) ++ blocks L A) /\
cgif_rel mem' md' s (W * H) GPAL (gs_new W H attr ngp loops GPAL) /\
Z.of_nat (length (concat (YO07.s_out (gs_new W H attr ngp loops GPAL)))) <= HDR_OUT /\
res_ok A' (newgif_rb b).
Definition newgif_x : Prop :=
forall L A (regs : bvmap 5 word) mem md (cfgp pal0 pala attr gen W H ngp loops : Z) (rest : list (Z * Z)) (GPAL : list Z)
(b : rbound) (TA TB : TSet),
fn_pre ubs0_msyms MR NEWGIF_STK L A regs mem md -> st_init_done A = true ->
getr regs 10 = Z_to_bv 64 cfgp -> cfgp mod 8 = 0 -> spZ regs <= cfgp -> cfgp + 48 <= 2 ^ 63 ->
obj_at ubs0segs mem cfgp LAY_Config [pal0; ubs0_D_str_tmp_out_gif; attr; gen; W; H; ngp; loops; 0; 0] ->
sink_none ubs0_msyms mem md ->
spZ regs <= 2 ^ 47 ->
W * H <= 100000000 ->
Z_to_bv 64 pala = Z_to_bv 64 pal0 ->
Permutation (blocks L A) ((if Z.land attr 4 =? 0 then [(pala, 3 * ngp)] else []) ++ rest) ->
(Z.land attr 4 = 0 -> garr8 ubs0segs mem pala GPAL /\ Z.of_nat (length GPAL) = 3 * ngp) ->
fd_lookup (m_fds md) (alloc_fd (m_fds md)) = None ->
res_ok A b -> newgif_room b ->
(forall c', newgif_postA L A regs mem md b c' -> realizes ubs0segs c' TA) ->
(g_sgct_ok (newgif_cfg W H attr gen ngp GPAL) = false -> forall c', newgif_postB0 L A regs mem md b c' -> realizes ubs0segs c' TB) ->
(g_sgct_ok (newgif_cfg W H attr gen ngp GPAL) = true -> forall c', newgif_postB1 L A regs mem md b attr gen W H ngp loops GPAL c' -> realizes ubs0segs c' TB) ->
realizes ubs0segs (mkCfg (mkst regs (Z_to_bv 64 ubs0_A_cgif_newgif) mem (seg_rom ubs0segs)) md)
(if g_opens (newgif_cfg W H attr gen ngp GPAL) then openat_shape (m_fs md) TA TB else TA).
End d.
End c.
