(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.AS Require Import ShapeAlg.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.Lib Require Import ImageA RzCPS.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A Require Layout RT_iface D_defs D_kit I_read. Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.Layout.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.RT_iface.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.D_defs.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.D_kit.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.I_read.TwinB__.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A Require Import Shadow.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.L2B Require Import L2Kit L2Act L2Stmt B0_fs_L2f.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require Import PropExec.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import Tac WalkLib SegsB0.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzTac BzArr BzCMem BzCStream BzCState BzCMtf BzCHuff BzArrD CmpMem CmpCut CmpCutSM CmpCutSmA BzCFactsSmA CmpCutSmB BzCFactsGm BzCSmF1 BzCFactsSmB BzCFactsSd CmpHmKit CmpSmKit CmpSmKit2 AsanKit AsanKit2 AsanCut AsanCutB0.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzCLemmas1 BzCHuffF1.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCHuffF1.BzCFactsHm.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import CmpCut6.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import A0_cmp_fsV A0_cmp_smV B0_cmp_sdV B0_cmp_smV B0_cmp_smBz B0_cmp_smZ.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeil.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzParams.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Open Scope Z_scope.
#[local] Notation mem := (word -> option byte).

Section SMG.
Context {BZP : BzParams} {ACEIL__ : ACeil}.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Hypothesis HBM : hbMakeCodeLengths_contract RT.
Hypothesis AF_DRV : forall Σ m, ART RT Σ m -> drv_consts m.
(* [comment removed for export] *)
Variables (cx : cctx) (g : eg) (e : est) (lo : Z) (sp gp tp : word).
Hypothesis CX : cctx_ok cx. Hypothesis SEP : cctx_sep cx. Hypothesis IMG : cctx_img (aci_c B0C) cx.
Hypothesis GM : g_mtf g = true. Hypothesis GB : g_bs g = true. Hypothesis GZ : g_zbits g = Z_to_bv 64 (c_A2 cx + e_nblock e).
Hypothesis SFA : smA_facts e. Hypothesis SFB : smB_facts e znew znew znew znew znew.
Hypothesis TP : tp = Z_to_bv 64 0x6094d8.
Notation usp := (bv_unsigned sp).
Notation E := (c_E cx). Notation A1 := (c_A1 cx). Notation A2 := (c_A2 cx). Notation FT := (c_FT cx). Notation J := (c_J cx).
Notation A := (sm_alpha e). Notation nG := (smA_ng e). Notation nMTF := (sm_nmtf e). Notation nInUse := (e_nInUse e).
Notation Wsm := [(E, E + 55768); (A2, A2 + ARR2_SIZE)].
Notation cSB := (Z_to_bv 64 2147450880).
(* [comment removed for export] *)
Variables (PMc : Model -> Prop) (P FB SHF SHE : Z) (fr : list (Z * nat)) (live0 : list (Z * Z)) (sp0 : Z).
Hypothesis FDO : fdfs_only PMc. Hypothesis MST : mat_stable PMc.
Hypothesis G : act_geom RT lo P usp sp0 true 2 FB SHF 256 32 fr live0 Wsm.
Hypothesis ACE : alloc_ceiling = sp0 - STACK_WIN.
Hypothesis FRLO : P + 1696 <= usp. Hypothesis FRHI : usp <= P + 1712.
Hypothesis ROOM : lo + RT_STACK + 304 <= P.
Hypothesis FRB : (length fr + 1 < FRAMES_MAX)%nat.
Hypothesis LIVE : In (E, 55768) live0. Hypothesis LIV1 : In (A1, ARR1_SIZE) live0. Hypothesis LIV2 : In (A2, ARR2_SIZE) live0. Hypothesis LIVF : In (FT, 262148) live0.
Hypothesis AE : sanchor E SHE. Hypothesis EIMG : 0x62b000 <= E.
(* [comment removed for export] *)
Hypothesis GFE : E + 55768 <= FB \/ FB + 256 <= E. Hypothesis GFA1 : A1 + ARR1_SIZE <= FB \/ FB + 256 <= A1.
Hypothesis GFA2 : A2 + ARR2_SIZE <= FB \/ FB + 256 <= A2. Hypothesis GFFT : FT + 262148 <= FB \/ FB + 256 <= FT.
Hypothesis GLSE : E + 55768 <= SHF \/ SHF + 32 <= E. Hypothesis GLSA1 : A1 + ARR1_SIZE <= SHF \/ SHF + 32 <= A1.
Hypothesis GLSA2 : A2 + ARR2_SIZE <= SHF \/ SHF + 32 <= A2. Hypothesis GLSFT : FT + 262148 <= SHF \/ SHF + 32 <= FT.
Hypothesis GSELF : FB + 256 <= SHF \/ SHF + 32 <= FB.
Hypothesis FSEG : 0x62b000 <= FB. Hypothesis FHI : FB + 256 <= 0x7fff7000 \/ 0x10007fff8000 <= FB.
Hypothesis OFFE : E + 55768 <= 0x7fff7000 \/ 0x10007fff8000 <= E. Hypothesis OFF1 : A1 + ARR1_SIZE <= 0x7fff7000 \/ 0x10007fff8000 <= A1.
Hypothesis OFF2 : A2 + ARR2_SIZE <= 0x7fff7000 \/ 0x10007fff8000 <= A2.
Hypothesis SHR0 : 2147450880 <= SHF. Hypothesis SHR1 : SHF + 32 <= 17594333495296.
Variable mi : mem.   (* [comment removed for export] *)
Notation PRESI := (PRESI usp fr live0 Wsm mi).
Notation SOK Σ := (sig_ok RT sp0 true 2 FB fr live0 Σ).

(* [comment removed for export] *)
Definition sm_shsep : Prop :=
  (E + 55768 <= A1 \/ A1 + ARR1_SIZE <= E) /\
  (E + 55768 <= A2 \/ A2 + ARR2_SIZE <= E) /\
  (E + 55768 <= FT \/ FT + 262148 <= E) /\
  (A1 + ARR1_SIZE <= A2 \/ A2 + ARR2_SIZE <= A1) /\
  (A1 + ARR1_SIZE <= FT \/ FT + 262148 <= A1) /\
  (A2 + ARR2_SIZE <= FT \/ FT + 262148 <= A2) /\
  (E + 55768 <= FB \/ FB + 256 <= E) /\
  (A1 + ARR1_SIZE <= FB \/ FB + 256 <= A1) /\
  (A2 + ARR2_SIZE <= FB \/ FB + 256 <= A2) /\
  (FT + 262148 <= FB \/ FB + 256 <= FT) /\
  (E + 55768 <= SHF \/ SHF + 32 <= E) /\
  (A1 + ARR1_SIZE <= SHF \/ SHF + 32 <= A1) /\
  (A2 + ARR2_SIZE <= SHF \/ SHF + 32 <= A2) /\
  (FT + 262148 <= SHF \/ SHF + 32 <= FT) /\
  (FB + 256 <= SHF \/ SHF + 32 <= FB) /\
  E + 55768 + 4096 <= P /\ A1 + ARR1_SIZE + 4096 <= P /\ A2 + ARR2_SIZE + 4096 <= P /\ FT + 262148 + 4096 <= P /\ FB + 256 + 4096 <= P /\ SHF + 32 + 4096 <= P /\ 17594333495296 + 65536 <= P /\ 0 < A1 /\ 0 < A2 /\ 0 < FT /\ P + 1712 <= 18446744073709551616 /\ lo + 4096 + 304 <= P.
Lemma sm_shsep_ok : sm_shsep.
Proof.
  pose proof CX as CX'. unfold cctx_ok in CX'. cbv zeta in CX'. destruct CX' as (RE & RE' & RA1 & RA1' & RA2 & RA2' & RFT & RFT' & _).
  pose proof SEP as SEP'. unfold cctx_sep, apart in SEP'. cbv zeta in SEP'. destruct SEP' as (SEA1 & SEA2 & SEFT & _ & _ & SA1A2 & SA1FT & _ & _ & SA2FT & _).
  pose proof G as [_ _ _ _ GLOW GLOR GPUS GSPT _ GFR GSH GSP0 _ _]. unfold RT_STACK, STACK_WIN, SEGTOP_A, USTACK_TOP, ESTATE_SIZE, FTAB_WORDS, CEIL in *.
  change (4 * 65537) with 262148 in *. pose proof ROOM as ROOM'. unfold RT_STACK in ROOM'.
  pose proof alloc_ceiling_range as ACR.
  unfold sm_shsep.
  split; [exact SEA1|].
  split; [exact SEA2|].
  split; [exact SEFT|].
  split; [exact SA1A2|].
  split; [exact SA1FT|].
  split; [exact SA2FT|].
  split; [exact GFE|].
  split; [exact GFA1|].
  split; [exact GFA2|].
  split; [exact GFFT|].
  split; [exact GLSE|].
  split; [exact GLSA1|].
  split; [exact GLSA2|].
  split; [exact GLSFT|].
  split; [exact GSELF|].
  clear SEA1 SEA2 SEFT SA1A2 SA1FT SA2FT. clear - RE RE' RA1 RA1' RA2 RA2' RFT RFT' GLOW GLOR GPUS GSPT GFR GSH GSP0 ACE ACR FRLO FRHI ROOM'. repeat split; lia.
Qed.
Ltac shsep_open :=
  let H := fresh "SHS" in pose proof sm_shsep_ok as H; unfold sm_shsep in H;
  destruct H as (?DEA1 & ?DEA2 & ?DEFT & ?DA1A2 & ?DA1FT & ?DA2FT & ?DEFB & ?DA1FB & ?DA2FB & ?DFTFB & ?DESH & ?DA1SH & ?DA2SH & ?DFTSH & ?DFBSH & ?XL1 & ?XL2 & ?XL3 & ?XL4 & ?XL5 & ?XL6 & ?XL7 & ?XL8 & ?XL9 & ?XL10 & ?XL11 & ?XL12);
  box_ors.

(* [comment removed for export] *)
Ltac sm_keys :=
  pose proof (ck_intro P CStack) as KP; pose proof (ck_intro usp CStack) as KU; pose proof (ck_intro FB CFrame) as KFB; pose proof (ck_intro SHF CShadow) as KSH;
  pose proof (ck_intro E (CLive E 55768)) as KE; pose proof (ck_intro A1 (CLive A1 ARR1_SIZE)) as KA1; pose proof (ck_intro A2 (CLive A2 ARR2_SIZE)) as KA2;
  pose proof (ck_intro FT (CLive FT 262148)) as KFT.
Ltac fp_ours := per_interval; cbn [outside]; lia.
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Notation cP := (Z_to_bv 64 P).
Notation CO := (FB + 32). Notation FV := (FB + 64).
Notation arr1 := (e_arr1 e).
Notation ITK k := (ITk e znew znew znew znew znew k).
Notation NOT z := (Z_to_bv 64 (18446744073709551615 - z)).
Notation ITR ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4 s10 t3 t4 :=
  (mkR ra cP gp tp t0 t1 t2 sp cP a0 a1 a2 a3 a4 a5 a6 a7 cSB (Z_to_bv 64 (258 * nG)) s4 (Z_to_bv 64 1032) (Z_to_bv 64 1548) (Z_to_bv 64 (4 * A)) (Z_to_bv 64 257)
       (Z_to_bv 64 CO) s10 (Z_to_bv 64 (CO + 12)) t3 t4 (Z_to_bv 64 (E + 37708)) (Z_to_bv 64 (-9))).
Notation HIT v32 v48 v56 v88 v20 v28 :=
  (sd_hi cx nG (SDW (Z_to_bv 64 FV) (Z_to_bv 64 (1032 * nG)) (Z_to_bv 64 A) (Z_to_bv 64 (E + 37708)) v32 v48 v56 (Z_to_bv 64 (E + 37708)) v88 (NOT (E + 45448)) (Z_to_bv 64 (E + 45448)) (Z_to_bv 64 A) v20 v28)).
Notation LOWk w104 := (sd_loA cx FB SHF SHE (Z_to_bv 64 (FB + 88)) (Z_to_bv 64 (flag6 nG)) w104).
Ltac dj H := let D := fresh "D" in pose proof H as D; unfold id in D |- *; clear - D; lia.
Ltac openST :=
  let H := fresh "ST0" in pose proof (proj1 SFB) as H; unfold smB_static in H;
  destruct H as (?HA & ?HNG & ?HM & ?HNI & ?ZB & ?MV & ?HK & ?HK2 & ?HN6).
Ltac act_open :=
  shsep_open; sm_keys;
  pose proof G as [_ _ _ _ GLOW GLOR GPUS GSPT GSPA GFR GSH GSP0 _ _]; unfold USTACK_TOP, RT_STACK, STACK_WIN, SEGTOP_A in GLOW, GLOR, GSPT, GFR, GSH, GSP0;
  pose proof (ag_ax G) as AX; pose proof alloc_ceiling_range as ACR;
  assert (CEP : CEIL <= P) by (unfold CEIL; rewrite ACE; unfold STACK_WIN; clear - GLOW GLOR; lia);
  assert (FBH : FB + 160 <= CEIL) by (unfold CEIL; rewrite ACE; unfold STACK_WIN; clear - GFR; lia).

Lemma shd_anchor0 : forall X SHX q2 x, sanchor X SHX -> (x < X \/ X + 8 * q2 <= x) -> (x / 8 + 2147450880 + 1 <= SHX \/ SHX + q2 <= x / 8 + 2147450880).
Proof. intros X SHX q2 x [M E'] H. subst SHX. Z.div_mod_to_equations. lia. Qed.

(* [comment removed for export] *)
Lemma sm_shE : forall Σ (m : mem) W, SOK Σ -> ART RT Σ m ->
  (forall x, E <= x < E + 55768 -> 0 <= x < 2^47 -> disjoint_from W (x / 8 + 2147450880) 1) -> shzW b0segs W m E (E + 55768).
Proof.
  intros Σ m W SK ART0 D. pose proof SK as (_ & SP0E & LIVS). pose proof (LIVS _ LIVE) as LVE.
  destruct (af_acc_live RT AF Σ m E 55768 ART0 LVE) as [_ ACCE].
  pose proof (af_live_range RT AF Σ m E 55768 ART0 LVE) as (EL0 & EL1 & _). rewrite SP0E in EL1.
  pose proof G as [_ _ _ _ _ _ _ _ _ _ _ GSP0 _ _]. unfold USTACK_TOP, STACK_WIN, SEGTOP_A in GSP0, EL1.
  pose proof CX as CX'. unfold cctx_ok in CX'. cbv zeta in CX'. destruct CX' as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & ME16 & _).
  apply (shzW_of_acc_gen b0segs W m E 55768 E (E + 55768) ACCE); [clear - EL0; lia| clear; lia| clear - ME16; Z.div_mod_to_equations; lia|].
  intros x Hx. apply (D x Hx). clear - Hx EL0 EL1 GSP0. lia.
Qed.
Lemma sm_shA1 : forall Σ (m : mem) W, SOK Σ -> ART RT Σ m ->
  (forall x, A1 <= x < A1 + ARR1_SIZE -> 0 <= x < 2^47 -> disjoint_from W (x / 8 + 2147450880) 1) -> shzW b0segs W m A1 (A1 + ARR1_SIZE).
Proof.
  intros Σ m W SK ART0 D. pose proof SK as (_ & SP0E & LIVS). pose proof (LIVS _ LIV1) as LV1.
  destruct (af_acc_live RT AF Σ m A1 ARR1_SIZE ART0 LV1) as [_ ACC1].
  pose proof (af_live_range RT AF Σ m A1 ARR1_SIZE ART0 LV1) as (L0 & L1 & _). rewrite SP0E in L1.
  pose proof G as [_ _ _ _ _ _ _ _ _ _ _ GSP0 _ _]. unfold USTACK_TOP, STACK_WIN, SEGTOP_A in GSP0, L1.
  pose proof CX as CX'. unfold cctx_ok in CX'. cbv zeta in CX'. destruct CX' as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & MA16 & _).
  apply (shzW_of_acc_gen b0segs W m A1 ARR1_SIZE A1 (A1 + ARR1_SIZE) ACC1); [clear - L0; lia| clear; lia| clear - MA16; Z.div_mod_to_equations; lia|].
  intros x Hx. apply (D x Hx). clear - Hx L0 L1 GSP0. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Notation Winit := [(E + 1704, E + 19706); (E + 37708, E + 39256); (E + 45448, E + 51640); (E + 51640, E + 55768); (P + 24, P + 136); (P + 136, P + 1264); (P + 1264, P + 1576);
                   (FB, FB + 24); (CO, CO + 12); (FV, FV + 24); (SHF, SHF + 20)].

Lemma sm_init : forall (Σ1 : rts RT) (m : mem) (Jsp : list byte)
    (w24 w32 w40 w48 w56 w64 w72 w80 w88 w96 w104 w112 w120 w128 : word)
    (w1264 w1272 w1280 w1288 w1296 w1304 w1312 w1320 w1328 w1336 w1344 w1352 w1360 w1368 w1376 : word)
    (w1384 w1392 w1400 w1408 w1416 w1424 w1432 w1440 w1448 w1456 w1464 w1472 w1480 w1488 w1496 w1504 w1512 w1520 w1528 w1536 w1544 w1552 w1560 w1568 : word)
    (ra t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc T c,
  SOK Σ1 -> length Jsp = 1128%nat ->
  rw_cells b0segs m E (EHEAD1 cx g e) -> rw_cells b0segs m (E + 640) (EHEAD2 cx g e) ->
  u32arr b0segs m (E + 672) (ovw (e_mtfFreq e) (jseg J 672 1032) 258) ->
  u8arr b0segs m A1 (zb8 arr1 ARR1_SIZE) ->
  u8arr b0segs m (E + 37708) (ovb (e_len e) (jseg J 37708 1548) 1548) ->
  u32arr b0segs m (E + 51640) (ovw (e_len_pack e) (jseg J 51640 4128) 1032) ->
  u32arr b0segs m (E + 45448) (ovw (e_rfreq e) (jseg J 45448 6192) 1548) ->
  u8arr b0segs m (E + 1704) (ovb (e_selector e) (jseg J 1704 18002) 18002) ->
  rw_cells b0segs m (P + 24) [C8 w24] ->
  rw_cells b0segs m (P + 32) [C8 w32; C8 w40; C8 w48; C8 w56; C8 w64; C8 w72; C8 w80; C8 w88; C8 w96; C8 w104; C8 w112; C8 w120; C8 w128] ->
  u8arr b0segs m (P + 136) Jsp ->
  rw_cells b0segs m (P + 1264) [C8 w1264; C8 w1272; C8 w1280; C8 w1288; C8 w1296; C8 w1304; C8 w1312; C8 w1320; C8 w1328; C8 w1336; C8 w1344; C8 w1352; C8 w1360; C8 w1368; C8 w1376] ->
  rw_cells b0segs m (P + 1384) [C8 w1384; C8 w1392; C8 w1400; C8 w1408; C8 w1416; C8 w1424; C8 w1432; C8 w1440; C8 w1448; C8 w1456; C8 w1464; C8 w1472; C8 w1480; C8 w1488; C8 w1496; C8 w1504; C8 w1512; C8 w1520; C8 w1528; C8 w1536; C8 w1544; C8 w1552; C8 w1560; C8 w1568] ->
  wr_at bsegs m FB 248 -> wr_at bsegs m SHF 32 ->
  ART RT Σ1 m -> KMem.mem_inv bsegs m -> stk bsegs m lo P -> PRESI m ->
  ASTA RT Σ1 PMc (eq (MS (mkR ra cP gp tp t0 t1 t2 sp cP (Z_to_bv 64 FB) a1 a2 a3 a4 a5 a6 a7 cSB (Z_to_bv 64 E) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                         F (Z_to_bv 64 0x8bcb0) fc None m (seg_rom b0segs))) c ->
  (forall c' (m' : mem) (Jsp' jc' : list byte) (v32' v88' : word) (ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' : word),
     let s := ITK 0 in
     ASTA RT Σ1 PMc (eq (MS (ITR ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' (Z_to_bv 64 (-1548)) (Z_to_bv 64 0) t3' t4')
                            F (Z_to_bv 64 0x9399c) fc None m' (seg_rom b0segs))) c' ->
     length Jsp' = 1128%nat -> length jc' = 12%nat ->
     rw_cells b0segs m' E (EHEAD1 cx g e) -> rw_cells b0segs m' (E + 640) (EHEAD2 cx g e) ->
     u32arr b0segs m' (E + 672) (ovw (e_mtfFreq e) (jseg J 672 1032) 258) ->
     u8arr b0segs m' A1 (zb8 arr1 ARR1_SIZE) ->
     u8arr b0segs m' (E + 37708) (ovb (it_len s) (jseg J 37708 1548) 1548) ->
     u32arr b0segs m' (E + 51640) (ovw (it_lpk e s) (jseg J 51640 4128) 1032) ->
     u32arr b0segs m' (E + 45448) (ovw (g_rfreq (Gend e s)) (jseg J 45448 6192) 1548) ->
     u8arr b0segs m' (E + 1704) (ovb (g_sel (Gend e s)) (jseg J 1704 18002) 18002) ->
     rw_cells b0segs m' (P + 24) [C8 (Z_to_bv 64 (E + 37450))] ->
     rw_cells b0segs m' (P + 32) (LOWk (Z_to_bv 64 1)) ->
     u8arr b0segs m' (P + 136) Jsp' ->
     rw_cells b0segs m' (P + 1264) (sm_set cx FV) ->
     rw_cells b0segs m' (P + 1384) (HIT v32' (Z_to_bv 64 (g_totc (Gend e s))) (Z_to_bv 64 nMTF) v88' (Z_to_bv 64 (g_nSel (Gend e s))) (Z_to_bv 64 (E + 37708))) ->
     rw_cells b0segs m' (P + 1568) [C8 (Z_to_bv 64 FB)] ->
     rw_cells b0segs m' FB [C8 (Z_to_bv 64 0x41b58ab3); C8 (Z_to_bv 64 0x148b3); C8 (Z_to_bv 64 0x8bc40)] ->
     u32arr b0segs m' FV (zw32 (g_fave (Gend e s)) 6) -> u8arr b0segs m' CO jc' ->
     rw_cells b0segs m' SHF sm_shadow ->
     ART RT Σ1 m' -> KMem.mem_inv bsegs m' -> stk bsegs m' lo P -> PRESI m' ->
     rt_pres_fp (rt_live RT Σ1) (rt_frames RT Σ1) P Winit m m' -> wmono bsegs m m' ->
     realizes bsegs c' T) ->
  realizes bsegs c T.
Proof.
  intros Σ1 m Jsp w24 w32 w40 w48 w56 w64 w72 w80 w88 w96 w104 w112 w120 w128 w1264 w1272 w1280 w1288 w1296 w1304 w1312 w1320 w1328 w1336 w1344 w1352 w1360 w1368 w1376
    w1384 w1392 w1400 w1408 w1416 w1424 w1432 w1440 w1448 w1456 w1464 w1472 w1480 w1488 w1496 w1504 w1512 w1520 w1528 w1536 w1544 w1552 w1560 w1568
    ra t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc T c
    SK LJsp EH1 EH2 MTF AR1 LEN LPK RFQ SEL SL24 LOW SPL SETc HI WRF WRS ART0 MI0 ST0 PR0 Hc Hk.
  act_open. pose proof SK as (FRM & SP0E & LIVS).
  (* [comment removed for export] *)
  destruct (n_wr_at_rw_CB m FB 24 (wr_at_sub bsegs m FB 248 FB 24 WRF ltac:(clear; lia) ltac:(clear; lia) ltac:(clear; lia)) ltac:(clear; lia)) as (jh & HDj).
  change (Z.to_nat 24) with 24%nat in HDj.
  apply (rw_cells_split_CB b0segs _ _ [] 24 _ [] [8;8;8]%nat) in HDj; [| reflexivity]. cbn [mk_CB_cells app] in HDj. cb8_all HDj.
  destruct (n_wr_at_rw_CB m CO 12 (wr_at_sub bsegs m FB 248 CO 12 WRF ltac:(clear; lia) ltac:(clear; lia) ltac:(clear; lia)) ltac:(clear; lia)) as (jc & COj).
  change (Z.to_nat 12) with 12%nat in COj. destruct (rw_cells_CB_C1s b0segs _ _ _ _ COj) as [_ Ljc]. pose proof (u8arr_of_rw_cells b0segs m _ _ _ COj) as COST. clear COj.
  destruct (n_wr_at_rw_CB m FV 24 (wr_at_sub bsegs m FB 248 FV 24 WRF ltac:(clear; lia) ltac:(clear; lia) ltac:(clear; lia)) ltac:(clear; lia)) as (jf & FVj).
  change (Z.to_nat 24) with 24%nat in FVj. destruct (rw_cells_CB_C1s b0segs _ _ _ _ FVj) as [_ Ljf]. pose proof (u8arr_of_rw_cells b0segs m _ _ _ FVj) as FAV. clear FVj.
  destruct (n_wr_at_rw_CB m SHF 20 (wr_at_sub bsegs m SHF 32 SHF 20 WRS ltac:(clear; lia) ltac:(clear; lia) ltac:(clear; lia)) ltac:(clear; lia)) as (j20 & SHj).
  change (Z.to_nat 20) with 20%nat in SHj.
  (* [comment removed for export] *)
  assert (OP : forall a b, P <= a -> b <= SH_LO \/ SH_HI <= a) by (intros a b Ha; right; unfold SH_HI; clear - Ha XL7; lia).
  assert (OE : forall a b, E <= a -> b <= E + 55768 -> b <= SH_LO \/ SH_HI <= a) by (intros a b Ha Hb; pose proof OFFE as D; unfold id in D; unfold SH_LO, SH_HI; clear - D Ha Hb; lia).
  assert (OF : forall a b, FB <= a -> b <= FB + 256 -> b <= SH_LO \/ SH_HI <= a) by (intros a b Ha Hb; pose proof FHI as D; unfold id in D; unfold SH_LO, SH_HI; clear - D Ha Hb; lia).
  assert (SHe : shzW b0segs (WsA cx P FB SHF) m E (E + ESTATE_SIZE)).
  { apply (sm_shE Σ1 m _ SK ART0). intros x Hx X47. unfold WsA. cbn [disjoint_from].
    repeat (split; [first [ apply shd_app; [exact X47| first [apply OE; clear; lia| apply OP; clear; lia| apply OF; clear; lia]]
                          | apply (shd_anchor0 FB SHF 20 x AX); pose proof DEFB as DJ; unfold id in DJ; clear - DJ Hx; lia ]|]). exact I. }
  assert (SHa : shzW b0segs (WsA cx P FB SHF) m A1 (A1 + ARR1_SIZE)).
  { apply (sm_shA1 Σ1 m _ SK ART0). intros x Hx X47. unfold WsA. cbn [disjoint_from].
    repeat (split; [first [ apply shd_app; [exact X47| first [apply OE; clear; lia| apply OP; clear; lia| apply OF; clear; lia]]
                          | apply (shd_anchor0 FB SHF 20 x AX); pose proof DA1FB as DJ; unfold id in DJ; clear - DJ Hx; lia ]|]). exact I. }
  (* [comment removed for export] *)
  eapply (l1_realizes RT AF Σ1 PMc _ T c MST Hc).
  eapply (B0_sm_segA cx e g _ gp tp sp F fc znew znew znew znew znew P SHE FB SHF CX SEP GM CEP XL11 ltac:(clear - GFR; lia) FBH
            ltac:(unfold SH_LO; exact SHR0) ltac:(unfold SH_HI; clear - SHR1; lia) AE AX
            ltac:(dj DEFB) ltac:(dj DA1FB) ltac:(dj DESH) ltac:(dj DA1SH) ltac:(dj DFBSH) ltac:(unfold id; left; clear - XL6; lia)
            ltac:(pose proof OFFE as D; unfold id in D |- *; unfold SH_LO, SH_HI; clear - D; lia) ltac:(pose proof FHI as D; unfold id in D |- *; unfold SH_LO, SH_HI; clear - D; lia)
            ltac:(unfold SH_HI; clear - XL7; lia) SFA SFB m Jsp jc jf j20
            w24 w32 w40 w48 w56 w64 w72 w80 w88 w96 w104 w112 w120 w128 w1264 w1272 w1280 w1288 w1296 w1304 w1312 w1320 w1328 w1336 w1344 w1352 w1360 w1368 w1376
            w1384 w1392 w1400 w1408 w1416 w1424 w1432 w1440 w1448 w1456 w1464 w1472 w1480 w1488 w1496 w1504 w1512 w1520 w1528 w1536 w1544 w1552 w1560 w1568);
    [exact LJsp| rewrite Ljc; reflexivity| rewrite Ljf; reflexivity| exact EH1| exact EH2| exact MTF| exact AR1| exact LEN| exact LPK| exact RFQ| exact SEL| exact SL24| exact LOW| exact SPL| exact SETc| exact HI
    | exact HDj| exact COST| exact FAV| exact SHj| exact (kmem_inv_N _ _ MI0)| exact SHa| exact SHe|].
  clear EH1 EH2 MTF AR1 LEN LPK RFQ SEL SL24 LOW SPL SETc HI HDj COST FAV SHj SHa SHe Hc.
  intros m1 Jsp' jc' v32' v88' ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4'. cbv zeta.
  intros LJsp' Ljc' EH1 EH2 MTF AR1 LEN LPK RFQ SEL SL24 LOW SPL SETc HI S1568 HD FAVE COST SHD NMI1 MU1 WM1. apply evt_done. intros c1 Hc1.
  unfold WsA in MU1.
  lazymatch type of MU1 with munch ?W _ _ => destruct (after_l1 AF G Σ1 W m m1 SK ART0 MI0 ST0 PR0 NMI1 MU1 WM1 ltac:(fp_ours)) as (ART1 & MI1 & ST1 & PR1 & STEP1) end.
  eapply (Hk c1 m1 Jsp' jc' v32' v88'); [exact Hc1| exact LJsp'| exact Ljc'| exact EH1| exact EH2| exact MTF| exact AR1| exact LEN| exact LPK| exact RFQ| exact SEL| exact SL24| exact LOW| exact SPL
    | exact SETc| exact HI| exact S1568| exact HD| exact FAVE| exact COST| exact SHD| exact ART1| exact MI1| exact ST1| exact PR1| exact STEP1| exact WM1].
Qed.

End SMG.
