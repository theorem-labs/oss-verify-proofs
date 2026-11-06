(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.AS Require Import ShapeAlg.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.Lib Require Import ImageA RzCPS.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A Require Import Layout RT_iface D_defs D_kit I_read.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A Require Import Shadow.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.L2 Require Import L2Kit L2Act L2Stmt A0_fs_L2f A0_sm_L2a A0_sm_L2b.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require Import PropExec.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import Tac WalkLib SegsA0.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzTac BzArr BzCMem BzCStream BzCState BzCMtf BzCHuff BzArrD CmpMem CmpCut CmpCutSM CmpCutSmA BzCFactsSmA CmpCutSmB BzCFactsGm BzCSmF1 BzCFactsSmB BzCFactsSd CmpHmKit CmpSmKit CmpSmKit2 AsanKit AsanKit2 AsanCut.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzCLemmas1 BzCHuffF1.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCHuffF1.BzCFactsHm.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import CmpCut6.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import A0_cmp_fsV A0_cmp_smV A0_cmp_fsP A0_cmp_msV A0_cmp_sdV A0_cmp_smS A0_cmp_sdZ A0_cmp_sdY A0_cmp_sdY2.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeil.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzParams.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Open Scope Z_scope.
#[local] Notation mem := (word -> option byte).

Section SMG.
Context {BZP : BzParams} {ACEIL__ : ACeil}.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Hypothesis MSET : memset_icontract RT e_asan_memset.
Hypothesis HBM : hbMakeCodeLengths_contract RT.
Hypothesis AF_DRV : forall Σ m, ART RT Σ m -> drv_consts m.
(* [comment removed for export] *)
Variables (cx : cctx) (g : eg) (e : est) (lo : Z) (sp gp tp : word).
Hypothesis CX : cctx_ok cx. Hypothesis SEP : cctx_sep cx. Hypothesis IMG : cctx_img (aci_c A0C) cx.
Hypothesis GM : g_mtf g = true. Hypothesis GB : g_bs g = true. Hypothesis GZ : g_zbits g = Z_to_bv 64 (c_A2 cx + e_nblock e).
Hypothesis SFA : smA_facts e. Hypothesis SFB : smB_facts e znew znew znew znew znew.
Hypothesis TP : tp = Z_to_bv 64 0x5fc0d8.
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
Hypothesis FRLO : P + 1600 <= usp. Hypothesis FRHI : usp <= P + 1616.
Hypothesis ROOM : lo + RT_STACK + 240 <= P.
Hypothesis FRB : (length fr + 1 < FRAMES_MAX)%nat.
Hypothesis LIVE : In (E, 55768) live0. Hypothesis LIV1 : In (A1, ARR1_SIZE) live0. Hypothesis LIV2 : In (A2, ARR2_SIZE) live0. Hypothesis LIVF : In (FT, 262148) live0.
Hypothesis AE : sanchor E SHE. Hypothesis EIMG : 0x61e000 <= E.
(* [comment removed for export] *)
Hypothesis GFE : E + 55768 <= FB \/ FB + 256 <= E. Hypothesis GFA1 : A1 + ARR1_SIZE <= FB \/ FB + 256 <= A1.
Hypothesis GFA2 : A2 + ARR2_SIZE <= FB \/ FB + 256 <= A2. Hypothesis GFFT : FT + 262148 <= FB \/ FB + 256 <= FT.
Hypothesis GLSE : E + 55768 <= SHF \/ SHF + 32 <= E. Hypothesis GLSA1 : A1 + ARR1_SIZE <= SHF \/ SHF + 32 <= A1.
Hypothesis GLSA2 : A2 + ARR2_SIZE <= SHF \/ SHF + 32 <= A2. Hypothesis GLSFT : FT + 262148 <= SHF \/ SHF + 32 <= FT.
Hypothesis GSELF : FB + 256 <= SHF \/ SHF + 32 <= FB.
Hypothesis FSEG : 0x61e000 <= FB. Hypothesis FHI : FB + 256 <= 0x7fff7000 \/ 0x10007fff8000 <= FB.
Hypothesis OFFE : E + 55768 <= 0x7fff7000 \/ 0x10007fff8000 <= E. Hypothesis OFF1 : A1 + ARR1_SIZE <= 0x7fff7000 \/ 0x10007fff8000 <= A1.
Hypothesis OFF2 : A2 + ARR2_SIZE <= 0x7fff7000 \/ 0x10007fff8000 <= A2.
Hypothesis SHR0 : 2147450880 <= SHF. Hypothesis SHR1 : SHF + 32 <= 17594333495296.
Variable mi : mem.   (* [comment removed for export] *)
Notation PRESI := (PRESI usp fr live0 Wsm mi).
Notation SOK Σ := (sig_ok RT sp0 true 2 FB fr live0 Σ).

Lemma sm_shsep_ok_here : sm_shsep cx lo P FB SHF.
Proof. eapply sm_shsep_ok; eassumption. Qed.
Ltac shsep_open :=
  let H := fresh "SHS" in pose proof (sm_shsep_ok_here) as H; unfold sm_shsep in H;
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
(* [comment removed for export] *)

(* [comment removed for export] *)
Hypothesis SDF : sd_facts (est_C e znew znew znew znew znew znew) nG (smB_nsel e znew znew znew znew znew).
Hypothesis ZI : zb8 (CmpCut.zbl (e_arr2 e) (e_nblock e) (e_bw e)) ARR2_SIZE = zb8 (e_arr2 e) ARR2_SIZE.
Hypothesis BWOK : BzCLemmas1.bw_ok (e_bw e). Hypothesis NB0 : 0 <= e_nblock e.
Hypothesis ROOMZ : e_nblock e + BzCStream.bw_numZ (e_bw (est_D e znew znew znew znew znew znew znew)) <= ARR2_SIZE.

Notation cP := (Z_to_bv 64 P).
Notation CO := (FB + 32). Notation FV := (FB + 64).
Notation arr1 := (e_arr1 e).
Notation eC := (est_C e znew znew znew znew znew znew). Notation eD := (est_D e znew znew znew znew znew znew znew).
Notation itB := (smB_it e znew znew znew znew znew). Notation nSel := (smB_nsel e znew znew znew znew znew).
Notation IZ ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s5 s6 s11 t3 t4 t5 t6 :=
  (mkR ra cP gp tp t0 t1 t2 sp cP a0 a1 a2 a3 a4 a5 a6 a7
       s2 s3 cSB s5 s6 (Z_to_bv 64 A) (Z_to_bv 64 A1) (Z_to_bv 64 (SHE + 83)) (Z_to_bv 64 nG) s11 t3 t4 t5 t6).

Ltac dj H := let D := fresh "D" in pose proof H as D; unfold id in D |- *; clear - D; lia.
Ltac vwW H := apply frdW_intro; [exact H| x_disj].
Ltac openST :=
  let H := fresh "ST0" in pose proof (proj1 SFB) as H; unfold smB_static in H;
  destruct H as (?HA & ?HNG & ?HM & ?HNI & ?ZB & ?MV & ?HK & ?HK2 & ?HN6).
Ltac act_open :=
  shsep_open; sm_keys;
  pose proof G as [_ _ _ _ GLOW GLOR GPUS GSPT GSPA GFR GSH GSP0 _ _]; unfold USTACK_TOP, RT_STACK, STACK_WIN, SEGTOP_A in GLOW, GLOR, GSPT, GFR, GSH, GSP0;
  pose proof (ag_ax G) as AX; pose proof alloc_ceiling_range as ACR;
  assert (CEP : CEIL <= P) by (unfold CEIL; rewrite ACE; unfold STACK_WIN; clear - GLOW GLOR; lia).
Ltac cutL R k H nb :=
  let T := fresh "T" in
  lazymatch type of R with rw_cells ?segs ?m ?A ?cs =>
    destruct (rw_cells_cutZ segs m A cs k R) as [H T]; clear R; rename T into R;
    cbn [firstn skipn cells_size csize Nat.add] in H, R;
    lazymatch type of R with rw_cells _ _ ?A' _ => replace A' with nb in R by (cbn; lia) end
  end.
Ltac glueL H1 H2 H :=
  lazymatch type of H1 with rw_cells ?segs ?m ?A ?cs1 => lazymatch type of H2 with rw_cells _ _ ?B ?cs2 =>
    assert (H : rw_cells segs m A (cs1 ++ cs2))
      by (apply (proj2 (rw_cells_app_iff_c segs m A cs1 cs2)); split; [exact H1| cbn [cells_size csize Nat.add];
          lazymatch goal with |- rw_cells _ _ ?A' _ => replace A' with B by (cbn; lia) end; exact H2]);
    cbn [app] in H; clear H1 H2 end end.
(* [comment removed for export] *)
Lemma stk_joinL : forall segs (m : mem) a b b' c, stk segs m a b -> stk segs m b' c -> b = b' -> a <= b <= c -> stk segs m a c.
Proof. intros segs m a b b' c H1 H2 -> Hle. eapply stk_merge; [exact H1| exact H2| exact Hle]. Qed.
Ltac stk_addL ST K :=
  lazymatch type of K with stk _ _ ?b' ?c =>
  lazymatch type of ST with stk ?segs ?m ?lo ?b =>
    let H := fresh in pose proof (stk_joinL segs m lo b b' c ST K ltac:(lia) ltac:(lia)) as H; clear ST K; rename H into ST end end.
Ltac stk_eatL ST H :=
  let K := fresh "Kst" in
  pose proof (stk_of_rw_cells a0segs _ _ _ H) as K; cbn [cells_size csize Nat.add] in K;
  lazymatch type of K with stk _ _ _ (?A + Z.of_nat ?k) => let z := eval cbv in (Z.of_nat k) in change (Z.of_nat k) with z in K end;
  stk_addL ST K; clear H.

Lemma sm_shE' : forall Σ (m : mem) W, SOK Σ -> ART RT Σ m ->
  (forall x, E <= x < E + 55768 -> 0 <= x < 2^47 -> disjoint_from W (x / 8 + 2147450880) 1) -> shzW a0segs W m E (E + 55768).
Proof. intros. eapply sm_shE; eassumption. Qed.

(* [comment removed for export] *)
Lemma sd_vw_intro6 : forall (A' nG' : Z) (w16 w24 w208 : word) (ee : est) (m0 : mem),
  sd_ro cx ee A' nG' P FB SHF SHE w16 w24 w208 m0 -> sd_vw cx ee A' nG' P FB SHF SHE w16 w24 w208 m0.
Proof.
  intros A' nG' w16 w24 w208 ee m0 RO m MU. shsep_open. bz_params.
  pose proof CX as CXL. unfold cctx_ok, ESTATE_SIZE, FTAB_WORDS, CEIL in CXL. cbv zeta in CXL.
  destruct CXL as (XE0 & XE1 & XA10 & XA11 & XA20 & XA21 & _).
  unfold sdWA in MU.
  destruct RO as (AR1 & INU & SLM & SEL & LEN & COD & LOA & LOB).
  unfold sd_ro. refine (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ _))))))).
  - eapply u8arr_munch; [exact AR1| exact MU|]. x_disj.
  - eapply u8arr_munch; [exact INU| exact MU|]. x_disj.
  - eapply u8arr_munch; [exact SLM| exact MU|]. x_disj.
  - eapply u8arr_munch; [exact SEL| exact MU|]. x_disj.
  - eapply u8arr_munch; [exact LEN| exact MU|]. x_disj.
  - eapply u32arr_munch; [exact COD| exact MU|]. x_disj.
  - eapply rw_cells_munch; [exact LOA| exact MU|]. x_disj.
  - eapply rw_cells_munch; [exact LOB| exact MU|]. x_disj.
Qed.

(* [comment removed for export] *)
Lemma RF_smD_bd_A0 : A0_cmp_sdZ.RF eC A nG nSel (e_nMTF eC) znew = smD_bd e znew znew znew znew znew znew znew.
Proof.
  unfold A0_cmp_sdZ.RF, A0_cmp_sdZ.BE, A0_cmp_sdZ.BD, A0_cmp_sdZ.BC, A0_cmp_sdZ.BC3, A0_cmp_sdZ.BB, A0_cmp_sdZ.BA, A0_cmp_sdZ.IN16,
         smD_bd, smD_b4, smD_b3, smD_b2, smD_b1, smD_b0, smD_in16, sm_nmtf, sm_alpha.
  cbn [e_nMTF e_len e_code e_arr1 e_selector e_selectorMtf e_inUse e_bw e_nInUse est_C]. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma sm_tail : forall (Σ1 : rts RT) (m : mem) (Jsp j1440 i16 : list byte) (v16 v24 w1360 w0 w8 : word) (totc gs : Z)
    (f8 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 rra : word)
    (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s3 s11 t3 t4 t5 t6 : word) F fc T c,
  SOK Σ1 -> length Jsp = 1112%nat -> length i16 = 16%nat ->
  rw_cells a0segs m E (EHEAD1 cx g e) ->
  u8arr a0segs m (E + 128) (ovb (e_inUse e) (jseg J 128 256) 256) ->
  u8arr a0segs m (E + 384) (ovb (e_unseqToSeq e) (jseg J 384 256) 256) ->
  rw_cells a0segs m (E + 640) (EHEAD2 cx g e) ->
  u32arr a0segs m (E + 672) (ovw (e_mtfFreq e) (jseg J 672 1032) 258) ->
  u8arr a0segs m (E + 1704) (ovb (it_sel itB) (jseg J 1704 18002) 18002) ->
  u8arr a0segs m (E + 19706) (ovb (e_selectorMtf e) (jseg J 19706 18002) 18002) ->
  u8arr a0segs m (E + 37708) (ovb (it_len itB) (jseg J 37708 1548) 1548) ->
  u32arr a0segs m (E + 39256) (ovw (e_code e) (jseg J 39256 6192) 1548) ->
  u32arr a0segs m (E + 45448) (ovw (it_rfreq itB) (jseg J 45448 6192) 1548) ->
  u32arr a0segs m (E + 51640) (ovw (it_lp itB) (jseg J 51640 4128) 1032) ->
  u8arr a0segs m A1 (zb8 arr1 ARR1_SIZE) -> u8arr a0segs m A2 (zb8 (e_arr2 e) ARR2_SIZE) -> u32arr a0segs m FT (zw32 (e_ftab e) 65537) ->
  rw_cells a0segs m P [C8 w0; C8 w8] ->
  rw_cells a0segs m (P + 16) (sm_loA cx e FB SHF SHE v16 v24) -> rw_cells a0segs m (P + 152) [C8 (Z_to_bv 64 4)] -> rw_cells a0segs m (P + 160) (sm_loB cx e SHE) ->
  u8arr a0segs m (P + 232) Jsp ->
  rw_cells a0segs m (P + 1344) (sm_hi cx e CO FV w1360 totc gs) ->
  rw_cells a0segs m (P + 1440) [CB 24 j1440] -> rw_cells a0segs m (P + 1464) [C8 (Z_to_bv 64 FB)] ->
  u8arr a0segs m (P + 1472) i16 -> stk a0segs m (P + 1488) (usp + -112) ->
  rw_cells a0segs m (usp + -112) [C8 f8; C8 r11; C8 r10; C8 r9; C8 r8; C8 r7; C8 r6; C8 r5; C8 r4; C8 r3; C8 r2; C8 r1; C8 r0; C8 rra] ->
  rw_cells a0segs m FB [C8 (Z_to_bv 64 0x41b58ab3); C8 (Z_to_bv 64 0x148b3); C8 (Z_to_bv 64 0x8a3ac)] -> rw_cells a0segs m SHF sm_shadow ->
  wr_at asegs m (FB + 128) 6 -> wr_at asegs m SHF 32 ->
  ART RT Σ1 m -> KMem.mem_inv asegs m -> stk asegs m lo P -> PRESI m ->
  ASTA RT Σ1 PMc (eq (MS (IZ ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 (E + 45448)) s3 (Z_to_bv 64 (it_nSel itB)) (Z_to_bv 64 (E + 668)) s11 t3 t4 t5 t6)
                         F (Z_to_bv 64 0x8f29c) fc None m (seg_rom a0segs))) c ->
  (forall c' (Σ2 : rts RT) (m' : mem) (u0 u1 u2 e0 e1 e2 e3 e4 e5 e6 e7 u3 u4 u5 u6 : word) F',
     ASTA RT Σ2 PMc (eq (MS (mkR rra sp gp tp u0 u1 u2 r0 r1 e0 e1 e2 e3 e4 e5 e6 e7 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 u3 u4 u5 u6)
                            F' (ret_pc rra) fc None m' (seg_rom a0segs))) c' ->
     rt_frames RT Σ2 = fr -> rt_live RT Σ2 = rt_live RT Σ1 -> rt_sp0 RT Σ2 = sp0 -> rt_credit RT Σ2 = rt_credit RT Σ1 ->
     ART RT Σ2 m' -> KMem.mem_inv asegs m' -> stk asegs m' lo usp ->
     emem cx a0segs g eD m' ->
     u8arr a0segs m' A1 (zb8 arr1 ARR1_SIZE) -> u8arr a0segs m' A2 (zb8 (CmpCut.zbl (e_arr2 e) (e_nblock e) (e_bw eD)) ARR2_SIZE) -> u32arr a0segs m' FT (zw32 (e_ftab e) 65537) ->
     BzCLemmas1.bw_ok (e_bw eD) -> PRESI m' ->
     realizes asegs c' T) ->
  realizes asegs c T.
Proof.
  intros Σ1 m Jsp j1440 i16 v16 v24 w1360 w0 w8 totc gs f8 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 rra ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s3 s11 t3 t4 t5 t6 F fc T c
    SK LJsp Li16 EH1 INU UNS EH2 MTF SEL SELM LEN CODE RFQ LPK AR1 AR2 FTB C0 LOA ITER LOB SPL HI J1440 S1464 I16 GAP SAV HD SHD WRF WRS ART0 MI0 ST0 PR0 Hc Hk.
  act_open. openST. pose proof SK as (FRM & SP0E & LIVS). pose proof (LIVS _ LIVE) as LVE. pose proof (LIVS _ LIV1) as LV1. pose proof (LIVS _ LIV2) as LV2.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
  (* [comment removed for export] *)
  pose proof (rw_cells_of_u8arr a0segs m (P + 232) Jsp SPL) as SPC. rewrite LJsp in SPC. clear SPL.
  apply (rw_cells_split_CB a0segs _ _ [] 1112 _ [] [1104; 8]%nat) in SPC; [| reflexivity]. cbn [mk_CB_cells app] in SPC.
  cutL SPC 1%nat SPL (P + 1336). cb8_all SPC.
  destruct (n_wr_at_rw_CB m (FB + 128) 6 WRF ltac:(clear; lia)) as (i6 & POSj).
  change (Z.to_nat 6) with 6%nat in POSj.
  destruct (rw_cells_CB_C1s a0segs _ _ _ _ POSj) as [_ Li6]. pose proof (u8arr_of_rw_cells a0segs m _ _ _ POSj) as POS. clear POSj.
  unfold sm_shadow in SHD. cutL SHD 16%nat SHa (SHF + 16). cutL SHD 1%nat SHP (SHF + 17).
  (* [comment removed for export] *)
  assert (ACW : acoW [(E + 19706, E + 37708); (E + 39256, E + 45448); (P + 208, P + 216); (P + 1344, P + 1440); (FB + 128, FB + 134); (SHF + 16, SHF + 17); (P - 16, P)] m).
  { destruct (af_client_consts RT AF Σ1 m ART0) as (G1 & G2 & _ & _).
    apply acoW_intro; [split; [exact (ro_C8_KN m _ _ G1)| exact (ro_C8_KN m _ _ G2)]| |];
      cbn [disjoint_from aci_got_sh aci_shvar A0C]; repeat (split; [left; clear - EIMG FSEG SHR0 XL7; lia|]); exact I. }
  assert (SHe : shzW a0segs [(E + 19706, E + 37708); (E + 39256, E + 45448); (P + 208, P + 216); (P + 1344, P + 1440); (FB + 128, FB + 134); (SHF + 16, SHF + 17); (P - 16, P)] m E (E + 55768)).
  { apply (sm_shE' Σ1 m _ SK ART0). intros x Hx X47. cbn [disjoint_from].
    assert (OP : forall a b, P - 16 <= a -> b <= SH_LO \/ SH_HI <= a) by (intros a b Ha; right; unfold SH_HI; clear - Ha XL7; lia).
    assert (OE : forall a b, E <= a -> b <= E + 55768 -> b <= SH_LO \/ SH_HI <= a) by (intros a b Ha Hb; pose proof OFFE as D; unfold id in D; unfold SH_LO, SH_HI; clear - D Ha Hb; lia).
    assert (OF : forall a b, FB <= a -> b <= FB + 256 -> b <= SH_LO \/ SH_HI <= a) by (intros a b Ha Hb; pose proof FHI as D; unfold id in D; unfold SH_LO, SH_HI; clear - D Ha Hb; lia).
    split; [apply shd_app; [exact X47| apply OE; clear; lia]|]. split; [apply shd_app; [exact X47| apply OE; clear; lia]|].
    split; [apply shd_app; [exact X47| apply OP; clear; lia]|]. split; [apply shd_app; [exact X47| apply OP; clear; lia]|].
    split; [apply shd_app; [exact X47| apply OF; clear; lia]|].
    split; [apply (shd_anchor FB SHF 16 17 x AX); pose proof DEFB as DJ; unfold id in DJ; clear - DJ Hx; lia|].
    split; [apply shd_app; [exact X47| apply OP; clear; lia]| exact I]. }
  eapply (l1_realizes RT AF Σ1 PMc _ T c MST Hc).
  eapply (A0_smC_body cx e _ gp tp sp F fc P SHE FB SHF CX CEP XL11 EIMG ltac:(clear - GFR; lia) ltac:(unfold CEIL; rewrite ACE; unfold STACK_WIN; clear - GFR; lia)
            ltac:(dj DEFB) ltac:(unfold SH_LO; exact SHR0) ltac:(unfold SH_HI; clear - SHR1; lia) AX ltac:(dj DESH) ltac:(dj DFBSH) ltac:(unfold id; left; clear - XL6; lia)
            ltac:(pose proof OFFE as D; unfold id in D |- *; unfold SH_LO, SH_HI; clear - D; lia) ltac:(pose proof FHI as D; unfold id in D |- *; unfold SH_LO, SH_HI; clear - D; lia)
            HA HNG znew znew znew znew znew znew m v16 v24 _ w1360 CO FV totc gs i6 lo);
    [exact SDF| exact SEL| exact SELM| exact LEN| exact CODE| exact LOA| exact LOB| exact SPC| exact HI| exact POS| rewrite Li6; reflexivity| exact SHP
    | exact ST0| clear - ROOM; unfold RT_STACK in ROOM; lia| unfold CEIL; rewrite ACE; exact GLOW| exact (kmem_inv_N _ _ MI0)| exact ACW| exact SHe|].
  clear Hc SEL SELM LEN CODE LOA LOB SPC HI POS SHP ST0 ACW SHe.
  intros m1 i6' qra q0 q1 q2 g0 g1 g2 g3 g4 g5 g6 g7 qs2 qs3 qs5 qs6 qs7 qs8 qs9 qs10 qs11 q3 q4 q5 SEL SELM LEN CODE LOA LOB HI POS Li6' SHP ST1n NMI1 MU1 WM1. apply evt_done. intros c1 Hc1.
  lazymatch type of MU1 with munch ?W _ _ =>
    destruct (after_l1_leaf AF G Σ1 W 16 m m1 SK ART0 MI0 PR0 NMI1 MU1 WM1 ltac:(clear; lia) ltac:(clear - ROOM; unfold RT_STACK in *; lia) ltac:(fp_ours)) as (ART1 & MI1 & PR1 & STEP1) end.
  xfer_l1 m m1 MU1 WM1. clear NMI1 MU1 WM1 STEP1.
  assert (ST1 : stk asegs m1 lo P) by exact ST1n. clear ST1n.
  (* [comment removed for export] *)
  set (v1336 := le_bytes_to_word (firstn 8 (skipn 1104 Jsp))) in *. clearbody v1336.
  set (H0 := SDW v1336 (Z_to_bv 64 (E + 37708)) (Z_to_bv 64 999999999) (Z_to_bv 64 nSel) (Z_to_bv 64 CO) (Z_to_bv 64 FV) (Z_to_bv 64 (E + 45448)) (Z_to_bv 64 3005)) in *.
  assert (VW : sd_vw cx eC A nG P FB SHF SHE v16 v24 (Z_to_bv 64 (E + 37708 + 258 * nG)) m1).
  { apply (sd_vw_intro6 A nG v16 v24 _ eC m1). unfold sd_ro.
    split; [exact AR1|]. split; [exact INU|]. split; [exact SELM|]. split; [exact SEL|]. split; [exact LEN|]. split; [exact CODE|]. split; [exact LOA| exact LOB]. }
  assert (MB : MA3 cx g eC A nG nSel P m1 H0 i16 (e_bw eC) m1).
  { unfold MA3. split; [exact EH1|]. split; [exact EH2|].
    split; [cbn [e_arr2 e_nblock e_bw est_C]; rewrite ZI; exact AR2|]. split; [exact HI|]. split; [exact I16|]. split; [exact (kmem_inv_N _ _ MI1)|]. split; [apply munch_refl| apply wmono_refl]. }
  clear EH1 EH2 AR2 HI I16.
  assert (AFW : app_fp [(E + 116, E + 120); (E + 640, E + 648); (A2, A2 + ARR2_SIZE); (P + 1336, P + 1440); (P + 1472, P + 1488)]).
  { cbn [app_fp]. unfold SH_LO, SH_HI. pose proof OFFE as D1. pose proof OFF2 as D2. unfold id in D1, D2. clear - D1 D2 XL7. repeat split; lia. }
  pose proof CX as CX'. unfold cctx_ok in CX'. cbv zeta in CX'. destruct CX' as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & MA16 & MA26 & _).
  assert (SHe : shzW a0segs [(E + 116, E + 120); (E + 640, E + 648); (A2, A2 + ARR2_SIZE); (P + 1336, P + 1440); (P + 1472, P + 1488)] m1 E (E + 55768)).
  { apply (sm_shE' Σ1 m1 _ SK ART1). intros x Hx X47. cbn [disjoint_from].
    assert (OP : forall a b, P <= a -> b <= SH_LO \/ SH_HI <= a) by (intros a b Ha; right; unfold SH_HI; clear - Ha XL7; lia).
    assert (OE : forall a b, E <= a -> b <= E + 55768 -> b <= SH_LO \/ SH_HI <= a) by (intros a b Ha Hb; pose proof OFFE as D; unfold id in D; unfold SH_LO, SH_HI; clear - D Ha Hb; lia).
    split; [apply shd_app; [exact X47| apply OE; clear; lia]|]. split; [apply shd_app; [exact X47| apply OE; clear; lia]|].
    split; [apply shd_app; [exact X47| pose proof OFF2 as D; unfold id in D; unfold SH_LO, SH_HI; clear - D; lia]|].
    split; [apply shd_app; [exact X47| apply OP; clear; lia]|]. split; [apply shd_app; [exact X47| apply OP; clear; lia]| exact I]. }
  assert (SH1 : shzW a0segs [(E + 116, E + 120); (E + 640, E + 648); (A2, A2 + ARR2_SIZE); (P + 1336, P + 1440); (P + 1472, P + 1488)] m1 A1 (A1 + ARR1_SIZE)).
  { destruct (af_acc_live RT AF Σ1 m1 A1 ARR1_SIZE ART1 LV1) as [_ ACC1'].
    pose proof (af_live_range RT AF Σ1 m1 A1 ARR1_SIZE ART1 LV1) as (A1L0 & A1L1 & _). rewrite SP0E in A1L1. unfold STACK_WIN in A1L1.
    apply (shzW_of_acc a0segs _ m1 A1 ARR1_SIZE A1 (A1 + ARR1_SIZE) ACC1' AFW); [clear - A1L0; lia| clear - A1L1 GSP0; lia| clear; lia|].
    clear - MA16. Z.div_mod_to_equations. lia. }
  assert (SH2 : shzW a0segs [(E + 116, E + 120); (E + 640, E + 648); (A2, A2 + ARR2_SIZE); (P + 1336, P + 1440); (P + 1472, P + 1488)] m1 A2 (A2 + ARR2_SIZE)).
  { destruct (af_acc_live RT AF Σ1 m1 A2 ARR2_SIZE ART1 LV2) as [_ ACC2'].
    pose proof (af_live_range RT AF Σ1 m1 A2 ARR2_SIZE ART1 LV2) as (A2L0 & A2L1 & _). rewrite SP0E in A2L1. unfold STACK_WIN in A2L1.
    apply (shzW_of_acc a0segs _ m1 A2 ARR2_SIZE A2 (A2 + ARR2_SIZE) ACC2' AFW); [clear - A2L0; lia| clear - A2L1 GSP0; lia| clear; lia|].
    clear - MA26. Z.div_mod_to_equations. lia. }
  pose proof SDF as SDF'. unfold sd_facts in SDF'. cbv zeta in SDF'.
  destruct SDF' as (HA' & HG' & HNS' & HNM' & HNMA' & ZB1' & MTFVN' & INUF' & SLMF' & SELF' & LENF' & CODF' & SCN').
  assert (HLIM : e_nblock eC + BzCStream.bw_numZ (fst (A0_cmp_sdZ.RF eC A nG nSel (e_nMTF eC) znew)) <= ARR2_SIZE) by (rewrite RF_smD_bd_A0; exact ROOMZ).
  eapply (l1_realizes RT AF Σ1 PMc _ T c1 MST Hc1).
  eapply (A0_smD_seg cx g eC _ gp tp sp F fc P SHE FB SHF v16 v24 (Z_to_bv 64 (E + 37708 + 258 * nG)) CX SEP GM GB GZ NB0 CEP XL11 AE
            (BzCStream.bw_numZ (fst (A0_cmp_sdZ.RF eC A nG nSel (e_nMTF eC) znew))) HLIM A nG nSel m1 VW SHe SH1 SH2 eq_refl HA' HG' HNS' (e_nMTF eC) HNM' eq_refl HNMA' ZB1' MTFVN' INUF' SLMF' SELF' LENF' CODF' SCN'
            znew BWOK eq_refl H0 i16);
    [reflexivity| rewrite Li16; reflexivity| exact MB|].
  clear Hc1 MB VW SHe SH1 SH2.
  intros m2 H' i16' pra p0 p1 p2 pa0 pa1 pa2 pa3 pa4 pa5 pa6 pa7 ps10 p3 p4 p5 p6 MB' Li16' BWD. apply evt_done. intros c2 Hc2.
  destruct MB' as (EH1 & EH2 & AR2 & HI & I16 & NMI2 & MU2 & WM2). unfold sdWA in MU2.
  lazymatch type of MU2 with munch ?W _ _ => destruct (after_l1 AF G Σ1 W m1 m2 SK ART1 MI1 ST1 PR1 NMI2 MU2 WM2 ltac:(fp_ours)) as (ART2 & MI2 & ST2 & PR2 & STEP2) end.
  xfer_l1 m1 m2 MU2 WM2. clear NMI2 MU2 WM2 STEP2.
  (* [comment removed for export] *)
  destruct (n_wr_at_rw_CB m2 (SHF + 20) 12 (wr_at_sub asegs m2 SHF 32 (SHF + 20) 12 WRS ltac:(clear; lia) ltac:(clear; lia) ltac:(clear; lia)) ltac:(clear; lia)) as (j12 & SHj).
  change (Z.to_nat 12) with 12%nat in SHj. destruct (rw_cells_CB_C1s a0segs _ _ _ _ SHj) as [_ Lj12].
  glueL SHP SHD SHq. glueL SHa SHq SHr. glueL SHr SHj SHs.
  pose proof (rw_cells_merge a0segs m2 SHF [] _ [] ltac:(rewrite app_nil_r; exact SHs)) as SHm. cbn [app cells_size csize Nat.add] in SHm. clear SHs.
  pose proof (u8arr_of_rw_cells a0segs m2 SHF _ _ SHm) as SHU. clear SHm.
  cutL HD 1%nat HD0 (FB + 8).
  (* [comment removed for export] *)
  eapply (l1_realizes RT AF Σ1 PMc _ T c2 MST Hc2).
  eapply (A0_sm_E1 cx _ gp tp sp F fc P SHE FB SHF A nG v16 v24 ltac:(clear - GFR; lia) ltac:(clear - GFR GSP0; lia) ltac:(dj DFBSH) m2 _ _);
    [| exact SHU| exact HD0| exact (kmem_inv_N _ _ MI2)| vwW LOA|].
  { cbn [cells_bytes cbytes app]. rewrite ?app_nil_r. cbn [length]. rewrite Lj12. reflexivity. }
  clear Hc2 SHU HD0. intros m3 qa0 SHF5 HDm NMI3 MU3 WM3. apply evt_done. intros c3 Hc3.
  lazymatch type of MU3 with munch ?W _ _ => destruct (after_l1 AF G Σ1 W m2 m3 SK ART2 MI2 ST2 PR2 NMI3 MU3 WM3 ltac:(fp_ours)) as (ART3 & MI3 & ST3 & PR3 & STEP3) end.
  clear POS HD WRF WRS. xfer_l1 m2 m3 MU3 WM3. clear NMI3 MU3 WM3 STEP3 SHF5 HDm.
  (* [comment removed for export] *)
  destruct (release_inline2 AF G (mi := mi) Σ1 m3 eq_refl SK ART3) as (Σ2 & fl & FLC & FLP & FL0 & FLW & FLD & REL).
  replace (FB + 256 - 8) with (FB + 248) in FLP by (clear; lia).
  eapply (l1_realizes RT AF Σ1 PMc _ T c3 MST Hc3).
  eapply (A0_sm_E1b _ gp tp sp F fc FB fl m3); [exact (ro_C8_KN m3 _ _ FLP)|].
  eapply (A0_sm_E2 _ gp tp sp F fc fl m3 (Z_to_bv 8 1)); [exact FLC| exact (kmem_inv_N _ _ MI3)|].
  clear Hc3. intros m4 FLC4 NMI4 MU4 WM4. apply evt_done. intros c4 Hc4.
  destruct (REL m4 MU4 WM4 FLC4 MI3 NMI4 ST3 PR3) as (ART4 & FRS4 & LV4 & SP4 & CR4 & AL4 & AM4 & MI4 & ST4 & PR4).
  xfer_fl G SK FLD m3 m4 MU4 WM4.
  pose proof (ASTA_switch RT Σ1 Σ2 PMc _ c4 Hc4 AL4 AM4) as Hc4'. clear Hc4.
  (* [comment removed for export] *)
  eapply (l1_realizes RT AF Σ2 PMc _ T c4 MST Hc4').
  eapply (A0_sm_E3 _ gp tp sp F fc m4 f8 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 rra); [exact SAV|].
  apply evt_done. clear Hc4'. intros c5 Hc5.
  (* [comment removed for export] *)
  assert (STn : stk a0segs m4 lo P) by exact ST4.
  stk_eatL STn C0. unfold sd_loA in LOA. cbv zeta in LOA. stk_eatL STn LOA. stk_eatL STn ITER. unfold sd_loB in LOB. cbv zeta in LOB. stk_eatL STn LOB.
  stk_eatL STn SPL. unfold sd_hi in HI. cbv zeta in HI. stk_eatL STn HI. stk_eatL STn J1440. stk_eatL STn S1464.
  pose proof (stk_of_u8arr a0segs _ _ _ I16) as K16. replace (Z.of_nat (length i16')) with 16 in K16 by (clear - Li16'; lia). stk_addL STn K16. clear I16.
  stk_addL STn GAP. stk_eatL STn SAV.
  lazymatch type of STn with stk _ _ _ ?hi => replace hi with usp in STn by (clear; lia) end.
  (* [comment removed for export] *)
  rewrite RF_smD_bd_A0 in EH1, EH2, AR2, BWD.
  eapply (Hk c5 Σ2 m4); [exact Hc5| exact FRS4| exact LV4| exact SP4| exact CR4| exact ART4| exact MI4| exact STn| | exact AR1| exact AR2| exact FTB| exact BWD| exact PR4].
  unfold emem. split; [exact EH1|]. split; [exact INU|]. split; [exact UNS|]. split; [exact EH2|]. split; [exact MTF|]. split; [exact SEL|]. split; [exact SELM|].
  split; [exact LEN|]. split; [exact CODE|]. split; [exact RFQ| exact LPK].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Notation LOWJ w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 w96 w104 w112 w120 w128 w136 w152 w160 w168 w176 w184 w192 w200 w208 w216 w224 :=
  [C8 w16; C8 w24; C8 w32; C8 w40; C8 w48; C8 w56; C8 w64; C8 w72; C8 w80; C8 w88; C8 w96; C8 w104; C8 w112; C8 w120; C8 w128; C8 w136; C8 (Z_to_bv 64 E);
   C8 w152; C8 w160; C8 w168; C8 w176; C8 w184; C8 w192; C8 w200; C8 w208; C8 w216; C8 w224].

Lemma sm_act : forall (Σ1 : rts RT) (jsp j1440 i16 : list byte) (w0 w8 : word)
    (w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 w96 w104 w112 w120 w128 w136 w152 w160 w168 w176 w184 w192 w200 w208 w216 w224 : word)
    (w1344 w1352 w1360 w1368 w1376 w1384 w1392 w1400 w1408 w1416 w1424 w1432 w1464 : word)
    (f8 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 rra : word)
    (ra t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s2 s3 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc T c,
  SOK Σ1 -> 4 * nG <= rt_credit RT Σ1 -> length jsp = 1112%nat -> length i16 = 16%nat ->
  emem cx a0segs g e mi ->
  u8arr a0segs mi A1 (zb8 arr1 ARR1_SIZE) -> u8arr a0segs mi A2 (zb8 (e_arr2 e) ARR2_SIZE) -> u32arr a0segs mi FT (zw32 (e_ftab e) 65537) ->
  rw_cells a0segs mi P [C8 w0; C8 w8] ->
  rw_cells a0segs mi (P + 16) (LOWJ w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 w96 w104 w112 w120 w128 w136 w152 w160 w168 w176 w184 w192 w200 w208 w216 w224) ->
  u8arr a0segs mi (P + 232) jsp ->
  rw_cells a0segs mi (P + 1344) [C8 w1344; C8 w1352; C8 w1360; C8 w1368; C8 w1376; C8 w1384; C8 w1392; C8 w1400; C8 w1408; C8 w1416; C8 w1424; C8 w1432] ->
  rw_cells a0segs mi (P + 1440) [CB 24 j1440] -> rw_cells a0segs mi (P + 1464) [C8 w1464] ->
  u8arr a0segs mi (P + 1472) i16 -> stk a0segs mi (P + 1488) (usp + -112) ->
  rw_cells a0segs mi (usp + -112) [C8 f8; C8 r11; C8 r10; C8 r9; C8 r8; C8 r7; C8 r6; C8 r5; C8 r4; C8 r3; C8 r2; C8 r1; C8 r0; C8 rra] ->
  wr_at asegs mi FB 248 -> wr_at asegs mi SHF 32 ->
  ART RT Σ1 mi -> KMem.mem_inv asegs mi -> stk asegs mi lo P ->
  ASTA RT Σ1 PMc (eq (MS (mkR ra cP gp tp t0 t1 t2 sp cP (Z_to_bv 64 FB) a1 a2 a3 a4 a5 a6 a7 s2 s3 cSB s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                         F (Z_to_bv 64 0x8a420) fc None mi (seg_rom a0segs))) c ->
  (forall c' (Σ2 : rts RT) (m' : mem) (u0 u1 u2 e0 e1 e2 e3 e4 e5 e6 e7 u3 u4 u5 u6 : word) F' fc',
     ASTA RT Σ2 PMc (eq (MS (mkR rra sp gp tp u0 u1 u2 r0 r1 e0 e1 e2 e3 e4 e5 e6 e7 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 u3 u4 u5 u6)
                            F' (ret_pc rra) fc' None m' (seg_rom a0segs))) c' ->
     rt_frames RT Σ2 = fr -> rt_live RT Σ2 = rt_live RT Σ1 -> rt_sp0 RT Σ2 = sp0 -> rt_credit RT Σ2 = rt_credit RT Σ1 - 4 * nG ->
     ART RT Σ2 m' -> KMem.mem_inv asegs m' -> stk asegs m' lo usp ->
     emem cx a0segs g eD m' ->
     u8arr a0segs m' A1 (zb8 arr1 ARR1_SIZE) -> u8arr a0segs m' A2 (zb8 (CmpCut.zbl (e_arr2 e) (e_nblock e) (e_bw eD)) ARR2_SIZE) -> u32arr a0segs m' FT (zw32 (e_ftab e) 65537) ->
     BzCLemmas1.bw_ok (e_bw eD) -> PRESI m' ->
     realizes asegs c' T) ->
  realizes asegs c T.
Proof.
  intros Σ1 jsp j1440 i16 w0 w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 w96 w104 w112 w120 w128 w136 w152 w160 w168 w176 w184 w192 w200 w208 w216 w224
    w1344 w1352 w1360 w1368 w1376 w1384 w1392 w1400 w1408 w1416 w1424 w1432 w1464 f8 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 rra
    ra t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s2 s3 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc T c SK CRED Ljsp Li16 EM AR1 AR2 FTB C0 LOW SPL HI J1440 S1464 I16 GAP SAV WRF WRS ART1 MI1 ST1 Hc Hk.
  act_open. bz_params.
  destruct EM as (EH1 & INU & UNS & EH2 & MTF & SEL & SELM & LEN & CODE & RFQ & LPK).
  assert (PR1 : PRESI mi) by (intros a _; reflexivity).
  (* [comment removed for export] *)
  eapply (sm_init RT AF MSET AF_DRV cx g e lo sp gp tp CX SEP GM SFA PMc P FB SHF SHE fr live0 sp0 FDO MST G ACE FRLO ROOM FRB LIVE AE
            GFE GFA1 GFA2 GFFT GLSE GLSA1 GLSA2 GLSFT GSELF FHI OFFE SHR0 SHR1 mi Σ1 mi
            w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 w96 w104 w112 w120 w128 w136 w152 w160 w168 w176 w184 w192 w200 w208 w216 w224
            w1344 w1352 w1360 w1368 w1376 w1384 w1392 w1400 w1408 w1416 w1424 w1432 w1464 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc T c
            SK EH1 EH2 MTF LEN LOW HI S1464 WRF WRS ART1 MI1 ST1 PR1 Hc).
  clear Hc EH1 EH2 MTF LEN LOW HI S1464.
  intros c2 m2 v16 v24 y0 y1 y3 y4 y5 y6 y7 x3 x5 x11 y6' F2 fc2 Hc2 EH1 EH2 MTF LEN LOA ITER LOB HI S1464 HD SHD ART2 MI2 ST2 PR2 ACC2 WM2.
  xfer_rt G SK ACC2 WM2 mi m2. clear ACC2 WM2.
  (* [comment removed for export] *)
  unfold sm_shadow in SHD. cutL SHD 4%nat SH0 (SHF + 4). cutL SHD 2%nat SHC (SHF + 6). cutL SHD 2%nat SH6 (SHF + 8). cutL SHD 3%nat SHV (SHF + 11).
  assert (WRC : wr_at asegs m2 CO 12) by exact (wr_at_sub asegs m2 FB 248 CO 12 WRF ltac:(clear; lia) ltac:(clear; lia) ltac:(clear; lia)).
  assert (WRV : wr_at asegs m2 FV 24) by exact (wr_at_sub asegs m2 FB 248 FV 24 WRF ltac:(clear; lia) ltac:(clear; lia) ltac:(clear; lia)).
  assert (WRP : wr_at asegs m2 (FB + 128) 6) by exact (wr_at_sub asegs m2 FB 248 (FB + 128) 6 WRF ltac:(clear; lia) ltac:(clear; lia) ltac:(clear; lia)). clear WRF.
  (* [comment removed for export] *)
  eapply (sm_l2_iters RT AF MSET HBM cx g e lo sp gp tp CX SEP GM SFB TP PMc P FB SHF SHE fr live0 sp0 FDO MST G ACE FRLO ROOM FRB LIVE LIV1 AE EIMG
            GFE GFA1 GFA2 GFFT GLSE GLSA1 GLSA2 GLSFT GSELF FSEG FHI OFFE SHR0 SHR1 mi 4 0 Σ1 Σ1 m2 m2 jsp v16 v24 (Z_to_bv 64 37450) (E + 676) (E + 672)
            _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F2 fc2 T c2 eq_refl ltac:(clear; lia) SK eq_refl eq_refl ltac:(clear - CRED; lia) Ljsp
            AR1 LEN LPK RFQ SEL LOA ITER LOB SPL HI EH2 SHC SHV WRC WRV ART2 MI2 ST2 PR2 (pfp_refl _ _ _ _ m2) Hc2).
  clear Hc2 AR1 LEN LPK RFQ SEL LOA ITER LOB SPL HI EH2 SHC SHV WRC WRV.
  intros c3 Σ3 m3 Jsp3 w1360' totc' gs' ra3 z0 z1 z2 g0 g1 g2 g3 g4 g5 g6 g7 zs3 zs11 z3 z4 z5 z6 F3 fc3 Hc3 SK3 LV3 FR3 CR3 LJsp3
    AR1 LEN LPK RFQ SEL LOA ITER LOB SPL HI EH2 SHC SHV WRC WRV ART3 MI3 ST3 PR3 ACC3.
  xfer_rtf G SK ACC3 m2 m3. clear ACC3 WRC WRV.
  glueL SHV SHD SHx. glueL SH6 SHx SHy. glueL SHC SHy SHz. glueL SH0 SHz SHD.
  rewrite <- (smB_it_eq e znew znew znew znew znew) in LEN, LPK, RFQ, SEL, Hc3.
  (* [comment removed for export] *)
  eapply (sm_tail Σ3 m3 Jsp3 j1440 i16 v16 v24 w1360' w0 w8 totc' gs' f8 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 rra _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F3 fc3 T c3 SK3 LJsp3 Li16
            EH1 INU UNS EH2 MTF SEL SELM LEN CODE RFQ LPK AR1 AR2 FTB C0 LOA ITER LOB SPL HI J1440 S1464 I16 GAP SAV HD SHD WRP WRS ART3 MI3 ST3 PR3 Hc3).
  intros c4 Σ4 m4 q0 q1 q2 p0 p1 p2 p3 p4 p5 p6 p7 q3 q4 q5 q6 F4 Hc4 FRS4 LV4 SP4 CR4 ART4 MI4 ST4 EM4 AR1' AR2' FTB' BWD PR4.
  eapply (Hk c4 Σ4 m4); [exact Hc4| exact FRS4| rewrite LV4; exact LV3| exact SP4| rewrite CR4, CR3; clear; lia| exact ART4| exact MI4| exact ST4| exact EM4| exact AR1'| exact AR2'| exact FTB'| exact BWD| exact PR4].
Qed.

End SMG.
