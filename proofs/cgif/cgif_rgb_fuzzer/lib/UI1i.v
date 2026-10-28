(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YK11 YK0s YK15 YN06 YQ0b.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YP0j YP0g YP0c.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import UH04 UH07 UH06 YI00 YI02.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Open Scope Z_scope.
Section c. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Definition NEWGIF_STK : Z := 1024 + ALLOC_STACK.
Definition ADDFRAME_STK : Z := 1536 + ALLOC_STACK.
Definition CLOSE_STK : Z := 1536 + ALLOC_STACK.
Definition RFC_STK : Z := 80 + ALLOC_STACK.
Record frame_st := mkFrame {
fr_ptr : Z;
fr_lpal : Z;
fr_img : Z;
fr_attr : Z;
fr_gen : Z;
fr_delay : Z;
fr_nlp : Z;
fr_ctidx : Z;
fr_disp : Z;
fr_tidx : Z
}.
Record cgif_st := mkCgif {
cg_frames : list (option frame_st);
cg_pal : Z;
cg_attr : Z;
cg_gen : Z;
cg_W : Z;
cg_H : Z;
cg_ngp : Z;
cg_loops : Z;
cg_raw : Z;
cg_cur : Z;
cg_ihead : Z;
rw_gct : Z;
rw_attr : Z;
rw_loops : Z;
rw_cur : Z
}.
Definition frame_ptr (o : option frame_st) : Z := match o with Some f => fr_ptr f | None => 0 end.
Definition cgif_vals (s : cgif_st) : list Z :=
[ frame_ptr (nth 0 (cg_frames s) None); frame_ptr (nth 1 (cg_frames s) None); frame_ptr (nth 2 (cg_frames s) None);
cg_pal s; 0  ; cg_attr s; cg_gen s; cg_W s; cg_H s; cg_ngp s; cg_loops s;
ubs2_A_writecb  ; 0  ; cg_raw s; 0  ; cg_cur s; cg_ihead s ].
Definition raw_sgct (s : cgif_st) : Z := if Z.land (cg_attr s) 4 =? 0 then cg_ngp s else 0.
Definition raw_vals (g : Z) (s : cgif_st) : list Z :=
[ ubs2_A_cgif_writecb; g; rw_gct s; rw_attr s; cg_W s; cg_H s; raw_sgct s; rw_loops s; rw_cur s ].
Definition frame_vals (f : frame_st) : list Z :=
[ fr_lpal f; fr_img f; fr_attr f; fr_gen f; fr_delay f; fr_nlp f; fr_ctidx f; fr_disp f; fr_tidx f ].
Definition cgif_at (mem : word -> option byte) (g : Z) (s : cgif_st) : Prop :=
obj_at ubs2segs mem g LAY_CGIF (cgif_vals s) /\
obj_at ubs2segs mem (cg_raw s) LAY_Raw (raw_vals g s) /\
(forall f, In (Some f) (cg_frames s) -> obj_at ubs2segs mem (fr_ptr f) LAY_Frame (frame_vals f)).
Definition pal_blocks (s : cgif_st) : list (Z * Z) :=
if Z.land (cg_attr s) 4 =? 0 then [(cg_pal s, 3 * cg_ngp s)] else [].
Definition frame_blocks (N : Z) (f : frame_st) : list (Z * Z) :=
(fr_ptr f, FRAME_SIZE) :: (fr_img f, N) ::
(if Z.land (fr_attr f) 1 =? 0 then [] else [(fr_lpal f, 3 * fr_nlp f)]).
Definition frames_blocks (N : Z) (fs : list (option frame_st)) : list (Z * Z) :=
flat_map (fun o => match o with Some f => frame_blocks N f | None => [] end) fs.
Definition cgif_blocks (g : Z) (s : cgif_st) (N : Z) : list (Z * Z) :=
(g, CGIF_SIZE) :: (cg_raw s, RAW_SIZE) :: pal_blocks s ++ frames_blocks N (cg_frames s).
Definition blocks_fp (bl : list (Z * Z)) : list (Z * Z) := map (fun b => (fst b, fst b + snd b)) bl.
Definition frame_wf (gattr : Z) (f : frame_st) : Prop :=
(Z.land (fr_attr f) 1 = 0 -> Z.land gattr 4 = 0)
/\ (fr_disp f = 4 \/ fr_disp f = 8).
Definition cgif_wf (s : cgif_st) (N : Z) : Prop :=
length (cg_frames s) = 3%nat /\
1 <= cg_W s /\ 1 <= cg_H s /\ N = cg_W s * cg_H s /\ N <= 100000000 /\
(Z.land (cg_attr s) 4 = 0 -> cg_ngp s <= 256) /\
(cg_ihead s = 1 \/ (cg_ihead s = 2 /\ nth 1 (cg_frames s) None <> None)) /\
(forall f, In (Some f) (cg_frames s) -> frame_wf (cg_attr s) f).
Section d.
Variable API : AllocAPI ubs2_msyms.
Let MR : MR_t := aa_MR API.
Definition newgif_spec : Prop :=
forall L A (regs : bvmap 5 word) mem md (cfgp pal0 pala attr gen W H ngp loops : Z) (rest : list (Z * Z)),
fn_pre ubs2_msyms MR NEWGIF_STK L A regs mem md -> st_init_done A = true ->
getr regs 10 = Z_to_bv 64 cfgp -> cfgp mod 8 = 0 -> spZ regs <= cfgp -> cfgp + 48 <= 2 ^ 63 ->
obj_at ubs2segs mem cfgp LAY_Config [pal0; 0; attr; gen; W; H; ngp; loops; ubs2_A_writecb; 0] ->
W * H <= 100000000 ->
Z_to_bv 64 pala = Z_to_bv 64 pal0 ->
Permutation (blocks L A) ((if Z.land attr 4 =? 0 then [(pala, 3 * ngp)] else []) ++ rest) ->
SR ubs2segs (mkCfg (mkst regs (Z_to_bv 64 ubs2_A_cgif_newgif) mem (seg_rom ubs2segs)) md)
(fun c' => exists L' A' regs' mem' md' (res : Z),
c' = mkCfg (mkst regs' (getr regs 1) mem' (seg_rom ubs2segs)) md' /\
journal ubs2_msyms MR NEWGIF_STK (spZ regs) [] L A mem md L' A' mem' md' /\
regs_preserved regs regs' /\
getr regs' 10 = Z_to_bv 64 res /\
((res = 0 /\ exists leak, Permutation (blocks L' A') (leak ++ blocks L A)) \/
(res <> 0 /\ exists s,
cgif_at mem' res s /\ cgif_wf s (W * H) /\
cg_frames s = [None; None; None] /\ cg_W s = W /\ cg_H s = H /\ cg_attr s = attr /\
cg_cur s = R_PENDING /\ cg_ihead s = 1 /\
Permutation (blocks L' A') (cgif_blocks res s (W * H) ++ blocks L A)))).
Definition addframe_spec : Prop :=
forall L A (regs : bvmap 5 word) mem md (g cfp : Z) (s : cgif_st) (N : Z)
(lpal lpa img fattr fgen delay nlp tidx : Z) (rest : list (Z * Z)),
fn_pre ubs2_msyms MR ADDFRAME_STK L A regs mem md -> st_init_done A = true ->
getr regs 10 = Z_to_bv 64 g -> getr regs 11 = Z_to_bv 64 cfp ->
cfp mod 8 = 0 -> spZ regs <= cfp -> cfp + 32 <= 2 ^ 63 ->
obj_at ubs2segs mem cfp LAY_FrameConfig [lpal; img; fattr; fgen; delay; nlp; tidx] ->
cgif_at mem g s -> cgif_wf s N ->
Z_to_bv 64 lpa = Z_to_bv 64 lpal ->
Permutation (blocks L A)
(cgif_blocks g s N ++ (img, N) :: (if Z.land fattr 1 =? 0 then [] else [(lpa, 3 * nlp)]) ++ rest) ->
SR ubs2segs (mkCfg (mkst regs (Z_to_bv 64 ubs2_A_cgif_addframe) mem (seg_rom ubs2segs)) md)
(fun c' => exists L' A' regs' mem' md' (s' : cgif_st),
c' = mkCfg (mkst regs' (getr regs 1) mem' (seg_rom ubs2segs)) md' /\
journal ubs2_msyms MR ADDFRAME_STK (spZ regs) (blocks_fp (cgif_blocks g s N)) L A mem md L' A' mem' md' /\
regs_preserved regs regs' /\ st_init_done A' = true /\
cgif_at mem' g s' /\ cgif_wf s' N /\
cg_W s' = cg_W s /\ cg_H s' = cg_H s /\ cg_attr s' = cg_attr s /\ cg_raw s' = cg_raw s /\
Permutation (blocks L' A')
(cgif_blocks g s' N ++ (img, N) :: (if Z.land fattr 1 =? 0 then [] else [(lpa, 3 * nlp)]) ++ rest)).
Definition close_spec : Prop :=
forall L A (regs : bvmap 5 word) mem md (g : Z) (s : cgif_st) (N : Z) (rest : list (Z * Z)),
fn_pre ubs2_msyms MR CLOSE_STK L A regs mem md -> st_init_done A = true ->
getr regs 10 = Z_to_bv 64 g ->
cgif_at mem g s -> cgif_wf s N ->
Permutation (blocks L A) (cgif_blocks g s N ++ rest) ->
SR ubs2segs (mkCfg (mkst regs (Z_to_bv 64 ubs2_A_cgif_close) mem (seg_rom ubs2segs)) md)
(fun c' => exists L' A' regs' mem' md',
c' = mkCfg (mkst regs' (getr regs 1) mem' (seg_rom ubs2segs)) md' /\
journal ubs2_msyms MR CLOSE_STK (spZ regs) (blocks_fp (cgif_blocks g s N)) L A mem md L' A' mem' md' /\
regs_preserved regs regs' /\
Permutation (blocks L' A') rest).
Definition rfc_spec : Prop :=
forall STK sp0 FP L A mem md Lc Ac memc mdc (regs : bvmap 5 word) (Bb : list (Z * Z)) (st dst N pdata nb cur : Z),
journal ubs2_msyms MR STK sp0 FP L A mem md Lc Ac memc mdc -> st_init_done Ac = true ->
(forall b, In b (blocks L A) -> In b Bb) -> Permutation (blocks Lc Ac) Bb -> In (pdata, nb) Bb ->
YK0s.ret_ok (getr regs 1) -> getr regs 4 = Z_to_bv 64 (ms_tp ubs2_msyms) ->
getr regs 10 = Z_to_bv 64 st -> getr regs 11 = Z_to_bv 64 dst -> getr regs 12 = Z_to_bv 64 N ->
spZ regs mod 16 = 0 -> sp0 - STK <= spZ regs - RFC_STK -> spZ regs <= st -> st + 24 <= sp0 ->
spZ regs <= dst -> dst + 32 <= sp0 -> (st + 24 <= dst \/ dst + 32 <= st) -> st mod 8 = 0 -> dst mod 8 = 0 -> sp0 < 2 ^ 63 ->
1 <= N <= 100000000 -> 0 <= cur <= nb -> 0 < nb ->
word_mem ubs2segs memc st pdata -> word_mem ubs2segs memc (st + 8) nb -> word_mem ubs2segs memc (st + 16) cur ->
SR ubs2segs (mkCfg (mkst regs (Z_to_bv 64 ubs2_A_read_frameconfig) memc (seg_rom ubs2segs)) mdc)
(fun c' => exists L2 A2 regs2 mem2 md2 (res cur2 : Z),
c' = mkCfg (mkst regs2 (getr regs 1) mem2 (seg_rom ubs2segs)) md2 /\
journal ubs2_msyms MR STK sp0 FP L A mem md L2 A2 mem2 md2 /\
st_init_done A2 = true /\ regs_preserved regs regs2 /\
getr regs2 10 = Z_to_bv 64 res /\
(forall a, alloc_ceiling <= a < 2 ^ 64 ->
~ (spZ regs - RFC_STK <= a < spZ regs) -> ~ (dst <= a < dst + 32) -> ~ (st + 16 <= a < st + 24) ->
mbyte ubs2segs mem2 a = mbyte ubs2segs memc a) /\
(forall b m i, In (b, m) Bb -> 0 <= i < m -> mbyte ubs2segs mem2 (b + i) = mbyte ubs2segs memc (b + i)) /\
word_mem ubs2segs mem2 st pdata /\ word_mem ubs2segs mem2 (st + 8) nb /\
word_mem ubs2segs mem2 (st + 16) cur2 /\ cur <= cur2 <= nb /\
((res = 0 /\ exists leak, Permutation (blocks L2 A2) (leak ++ Bb)) \/
(res = 1 /\ exists lpal lpa img fattr fgen delay nlp tidx,
obj_at ubs2segs mem2 dst LAY_FrameConfig [lpal; img; fattr; fgen; delay; nlp; tidx] /\
(Z.land fattr 1 = 0 -> lpal = 0) /\ Z_to_bv 64 lpa = Z_to_bv 64 lpal /\
Permutation (blocks L2 A2) ((img, N) :: (if Z.land fattr 1 =? 0 then [] else [(lpa, 3 * nlp)]) ++ Bb)))).
End d.
End c.
