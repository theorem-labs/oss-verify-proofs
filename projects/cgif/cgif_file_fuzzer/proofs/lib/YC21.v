(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require YZ00.
From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YK11 YK14 YK0s YK15 YP09 YI04 YI09 YI08 YN3v YI00.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YI5w YI5z.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YG0v.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YC20.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YI16 YE00 YE01.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require YO07.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YO08 YI0f YC5d YC7x.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Open Scope Z_scope.
Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section d.
Variable segs : list Segment.
Variable K : asink_syms.
Section e.
Variable B : asyms.
Variable MT : ameter_ops.
Variable XN : xnums.
#[local] Abbreviation rdW W mem := (mrestrict (w_H W) mem).
#[local] Abbreviation lpal_blocks fattr lpa nlp := (if Z.land fattr 1 =? 0 then [] else [(lpa, 3 * nlp)]).
Definition taddframe_specX (a : Z) (CTX : list (list Z)) (wfn rlo rhi : Z) : Prop :=
forall ly S W (regs : bvmap 5 word) mem md ch (g cfp : Z) (s : cgif_st) (N : Z)
(lpal lpa img fattr fgen delay nlp tidx : Z) (f path hw : Z) (rest : list (Z * Z))
(GPAL IMG LPAL : list Z) (gs : YO07.gif_st),
afn_pre segs B TADDFRAME_STK ly S W regs mem md ch ->
In (raZ regs :: spine ch) CTX -> Z.of_nat (length (frames S)) <= 7 ->
arodata_okP segs rlo rhi B (aview segs (w_H W) mem) ->
getr regs 10 = w64 g -> getr regs 11 = w64 cfp ->
afobj segs B ly S W mem cfp 32 ->
obj_at segs (rdW W mem) cfp LAY_FrameConfig [lpal; img; fattr; fgen; delay; nlp; tidx] ->
xcgif_at segs wfn path hw f (rdW W mem) g s -> cgif_wf s N -> f <> 0 ->
Z_to_bv 64 lpa = Z_to_bv 64 lpal ->
Permutation (ablocks B ly S) (cgif_blocks g s N ++ (img, N) :: lpal_blocks fattr lpa nlp ++ (f, FILE_BLOCK) :: rest) ->
cgif_relA segs K (rdW W mem) md s f N GPAL gs ->
Z.of_nat (length (concat (YO07.s_out gs))) + FRAME_OUT N <= SINK_MAX ->
garr8 segs (rdW W mem) img IMG -> Z.of_nat (length IMG) = N ->
(Z.land fattr 1 <> 0 -> garr8 segs (rdW W mem) lpa LPAL /\ Z.of_nat (length LPAL) = 3 * nlp) ->
st_nev S + EV_ADDFRAME <= EV_MAX -> blocks_bytes S + LIVE_ADDFRAME <= LIVE_MAX ->
mo_ok MT S (xm_addframe XN N) ->
SRr segs W (cfg_at segs a regs mem md)
(apost_base segs B TADDFRAME_STK (ablocks_fp (cgif_blocks g s N) ++ asink_fp f) regs ly S W mem md EV_ADDFRAME
(fun ly' S' W' regs' mem' md' => exists s' : cgif_st,
xcgif_at segs wfn path hw f (rdW W' mem') g s' /\ cgif_wf s' N /\
cg_W s' = cg_W s /\ cg_H s' = cg_H s /\ cg_attr s' = cg_attr s /\ cg_raw s' = cg_raw s /\
cg_gen s' = cg_gen s /\ cg_ngp s' = cg_ngp s /\ cg_pal s' = cg_pal s /\
Permutation (ablocks B ly' S') (cgif_blocks g s' N ++ (img, N) :: lpal_blocks fattr lpa nlp ++ (f, FILE_BLOCK) :: rest) /\
(forall b, In b (cgif_blocks g s' N) ->
aftok (ablocks_fp (cgif_blocks g s N) ++ asink_fp f) (ablocks B ly S) b /\
forall blc i, In b blc -> 0 <= i < req_size (snd b) ->
awr_byte TADDFRAME_STK (spZ regs) (ablocks_fp (cgif_blocks g s N) ++ asink_fp f) (ablocks B ly S) blc ly' [] (fst b + i)) /\
cgif_relA segs K (rdW W' mem') md' s' f N GPAL (YO07.add_frame (gcfg_of s GPAL) gs fattr fgen delay tidx nlp LPAL IMG) /\
Z.of_nat (length (concat (YO07.s_out (YO07.add_frame (gcfg_of s GPAL) gs fattr fgen delay tidx nlp LPAL IMG))))
<= Z.of_nat (length (concat (YO07.s_out gs))) + FRAME_OUT N /\
mo_le MT S S' (xn_addframe XN N))).
Definition tclose_specX (a : Z) (CTX : list (list Z)) (wfn rlo rhi : Z) : Prop :=
forall ly S W (regs : bvmap 5 word) mem md ch (g : Z) (s : cgif_st) (N : Z) (f path hw aM : Z) (rest : list (Z * Z))
(GPAL : list Z) (gs : YO07.gif_st),
afn_pre segs B TCLOSE_STK ly S W regs mem md ch ->
In (raZ regs :: spine ch) CTX -> Z.of_nat (length (frames S)) <= 7 ->
arodata_okP segs rlo rhi B (aview segs (w_H W) mem) ->
getr regs 10 = w64 g ->
xcgif_at segs wfn path hw f (rdW W mem) g s -> cgif_wf s N -> f <> 0 ->
Permutation (ablocks B ly S) (cgif_blocks g s N ++ (f, FILE_BLOCK) :: rest) ->
cgif_relA segs K (rdW W mem) md s f N GPAL gs ->
Z.of_nat (length (concat (YO07.s_out gs))) + CLOSE_OUT N <= SINK_MAX ->
ameta_inv segs K ly (rdW W mem) aM ->
st_nev S + EV_CLOSE <= EV_MAX -> blocks_bytes S + LIVE_FLUSH <= LIVE_MAX ->
mo_ok MT S (xm_close XN N) ->
SRr segs W (cfg_at segs a regs mem md)
(apost_base segs B TCLOSE_STK (ablocks_fp (cgif_blocks g s N) ++ asink_fp f) regs ly S W mem md EV_CLOSE
(fun ly' S' W' regs' mem' md' =>
Permutation (ablocks B ly' S') rest /\
asink_none segs K (rdW W' mem') md' /\
Fs.fs_lookup (m_fs md') sink_path = Some (bytes (concat (YO07.close_gif (gcfg_of s GPAL) gs) ++ [59])) /\
ameta_ok segs K (rdW W' mem') aM /\
mo_le MT S S' (xn_close XN N))).
Definition newgif_cfg (Wd Hd attr gen ngp : Z) (GPAL : list Z) : YO07.gcfg := YO07.mkG Wd Hd attr gen ngp GPAL.
Definition tnewgif_specXJ (a : Z) (CTX : list (list Z)) (wfn rlo rhi : Z) : Prop :=
forall ly S W (regs : bvmap 5 word) mem md ch (cfgp pal0 pala attr gen Wd Hd ngp loops aM : Z) (rest : list (Z * Z)) (GPAL : list Z),
afn_pre segs B TNEWGIF_STK ly S W regs mem md ch -> spZ regs mod 32 = 0 ->
In (raZ regs :: spine ch) CTX -> Z.of_nat (length (frames S)) <= 7 -> spZ regs + 32 <= ly_top ly ->
arodata_okP segs rlo rhi B (aview segs (w_H W) mem) ->
getr regs 10 = w64 cfgp ->
afobj segs B ly S W mem cfgp 48 ->
obj_at segs (rdW W mem) cfgp LAY_Config [pal0; ak_path K; attr; gen; Wd; Hd; ngp; loops; 0; 0] ->
Wd * Hd <= 100000000 ->
Z_to_bv 64 pala = Z_to_bv 64 pal0 ->
Permutation (ablocks B ly S) ((if Z.land attr 4 =? 0 then [(pala, 3 * ngp)] else []) ++ rest) ->
(Z.land attr 4 = 0 -> garr8 segs (rdW W mem) pala GPAL /\ Z.of_nat (length GPAL) = 3 * ngp) ->
asink_none segs K (rdW W mem) md ->
fd_lookup (m_fds md) (alloc_fd (m_fds md)) = None ->
ameta_inv segs K ly (rdW W mem) aM ->
st_nev S + EV_NEWGIF <= EV_MAX -> blocks_bytes S + LIVE_NEWGIF <= LIVE_MAX ->
mo_ok MT S (xm_newgif XN ngp) ->
SRr segs W (cfg_at segs a regs mem md)
(apost_base segs B TNEWGIF_STK [sink_token] regs ly S W mem md EV_NEWGIF
(fun ly' S' W' regs' mem' md' => exists res : Z, getr regs' 10 = w64 res /\
ameta_ok segs K (rdW W' mem') aM /\ mo_le MT S S' (xn_newgif XN ngp) /\
(
(res = 0 /\ Permutation (ablocks B ly' S') (ablocks B ly S) /\
asink_none segs K (rdW W' mem') md' /\ m_fs md' = m_fs md /\
(g_opens (newgif_cfg Wd Hd attr gen ngp GPAL) = true -> m_fds md' = m_fds md))
\/
(res = 0 /\ g_opens (newgif_cfg Wd Hd attr gen ngp GPAL) = true /\ g_sgct_ok (newgif_cfg Wd Hd attr gen ngp GPAL) = false /\
Permutation (ablocks B ly' S') (ablocks B ly S) /\
asink_none segs K (rdW W' mem') md' /\
Fs.fs_lookup (m_fs md') sink_path = Some (bytes []))
\/
(res <> 0 /\ g_opens (newgif_cfg Wd Hd attr gen ngp GPAL) = true /\ g_sgct_ok (newgif_cfg Wd Hd attr gen ngp GPAL) = true /\
exists (s : cgif_st) (f : Z),
xcgif_at segs wfn (ak_path K) 0 f (rdW W' mem') res s /\ cgif_wf s (Wd * Hd) /\ f <> 0 /\
cg_frames s = [None; None; None] /\ cg_W s = Wd /\ cg_H s = Hd /\ cg_attr s = attr /\
cg_cur s = R_PENDING /\ cg_ihead s = 1 /\ cg_gen s = gen /\ cg_ngp s = ngp /\
Permutation (ablocks B ly' S') (cgif_blocks res s (Wd * Hd) ++ (f, FILE_BLOCK) :: ablocks B ly S) /\
(forall b, In b (cgif_blocks res s (Wd * Hd) ++ [(f, FILE_BLOCK)]) ->
aftok [sink_token] (ablocks B ly S) b /\
forall blc i, In b blc -> 0 <= i < req_size (snd b) ->
awr_byte TNEWGIF_STK (spZ regs) [sink_token] (ablocks B ly S) blc ly' [] (fst b + i)) /\
cgif_relA segs K (rdW W' mem') md' s f (Wd * Hd) GPAL (gs_new Wd Hd attr ngp loops GPAL) /\
Z.of_nat (length (concat (YO07.s_out (gs_new Wd Hd attr ngp loops GPAL)))) <= HDR_OUT)))).
End e.
End d.
End c.
