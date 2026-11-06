(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.AS Require Import ShapeAlg.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.Lib Require Import ImageA RzCPS.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A Require Layout RT_iface D_defs D_kit I_read. Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.Layout.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.RT_iface.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.D_defs.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.D_kit.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.I_read.TwinB__.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A Require Import Shadow.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A Require L_libA.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.L2B Require Import L2Kit L2Act L2Stmt B0_fs_L2f B0_cb_L2a.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.L2B Require B0_sessK.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require Import PropExec.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import Tac WalkLib SegsA0 SegsB0.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzTac BzArr BzCMem BzCStream BzCState BzCMtf BzCBlock BzCHuff BzArrD BzCLemmas1 CmpMem CmpCut CmpCutMS CmpCutMtf CmpCutSM CmpCutSmA BzCFactsSmA CmpCutSmB BzCFactsGm BzCSmF1 BzCFactsSmB BzCFactsSd CmpHmKit CmpSmKit CmpSmKit2 AsanKit AsanKit2 AsanCut AsanCutB0.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzCNumZ CmpLaws CmpCutCB BzCFactsSmA2 BzCFactsSmB3 BzCFactsSd2 BzCLemmasMs6 BzCFactsBs6 BzCFactsCb BzCSortPost.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzCHuffF1.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCHuffF1.BzCFactsHm.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import CmpCut6.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import B0_cmp_fsV B0_cmp_msV B0_cmp_cbV B0_cmp_cbP B0_cmp_cbWc B0_cmp_cbH2 B0_cmp_cbS B0_cmp_cbG B0_cmp_cbT.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeil.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzParams.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Open Scope Z_scope.
#[local] Notation mem := (word -> option byte).

Section CBG.
Context {BZP : BzParams} {ACEIL__ : ACeil}.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Hypothesis SSH : forall v, In v set_shadow_vals -> set_shadow_contract RT v.
Hypothesis BSC : blockSort_contract RT bsX.
Hypothesis SMC : sendMTFValues_contract RT smA_facts smB_facts sd_facts.
(* [comment removed for export] *)
Variable X : cbenv. Variable Y : acenv. Variables (g : eg) (e : est).
Hypothesis XOK : cbenv_ok X. Hypothesis YOK : acenv_ok X Y. Hypothesis YSEP : acenv_sep X Y. Hypothesis YOFF : acenv_offsh X Y.
Hypothesis AE : sanchor (c_E (ce_cx X)) (ac_SHE Y).
Hypothesis IMG : cctx_img (aci_c B0C) (ce_cx X).
Hypothesis PRE : cb_pre g e. Hypothesis CBF : cb_facts e.
Hypothesis TP : ce_tp X = Z_to_bv 64 0x6094d8.
Notation cx := (ce_cx X).
Notation usp := (bv_unsigned (ce_sp X)). Notation P := (ac_P Y). Notation FB := (ac_FB Y). Notation SHF := (ac_SHF Y). Notation SHE := (ac_SHE Y).
Notation gp := (ce_gp X). Notation tp := (ce_tp X). Notation lo := (ce_lo X). Notation il := (ce_il X).
Notation E := (c_E cx). Notation A1 := (c_A1 cx). Notation A2 := (c_A2 cx). Notation FT := (c_FT cx). Notation J := (c_J cx).
Notation nb := (e_nblock e).
Notation Wcb := [(E, E + 55768); (A1, A1 + ARR1_SIZE); (A2, A2 + ARR2_SIZE); (FT, FT + 262148)].
Notation cSB := (Z_to_bv 64 2147450880).
Notation cP := (Z_to_bv 64 P).
(* [comment removed for export] *)
Variables (PMc : Model -> Prop) (fr : list (Z * nat)) (live0 : list (Z * Z)) (sp0 : Z).
Hypothesis FDO : fdfs_only PMc. Hypothesis MST : mat_stable PMc.
Hypothesis G : act_geom RT lo P usp sp0 true 3 FB SHF 512 64 fr live0 Wcb.
Hypothesis ACE : alloc_ceiling = sp0 - STACK_WIN.
Hypothesis ROOM : lo + RT_STACK + 2064 <= P.
Hypothesis FRB : (length fr + 2 < FRAMES_MAX)%nat.
Hypothesis LIVE : In (E, 55768) live0. Hypothesis LIV1 : In (A1, ARR1_SIZE) live0. Hypothesis LIV2 : In (A2, ARR2_SIZE) live0. Hypothesis LIVF : In (FT, 262148) live0.
(* [comment removed for export] *)
Hypothesis GFE : E + 55768 <= FB \/ FB + 512 <= E. Hypothesis GFA1 : A1 + ARR1_SIZE <= FB \/ FB + 512 <= A1.
Hypothesis GFA2 : A2 + ARR2_SIZE <= FB \/ FB + 512 <= A2. Hypothesis GFFT : FT + 262148 <= FB \/ FB + 512 <= FT.
Hypothesis GLSE : E + 55768 <= SHF \/ SHF + 64 <= E. Hypothesis GLSA1 : A1 + ARR1_SIZE <= SHF \/ SHF + 64 <= A1.
Hypothesis GLSA2 : A2 + ARR2_SIZE <= SHF \/ SHF + 64 <= A2. Hypothesis GLSFT : FT + 262148 <= SHF \/ SHF + 64 <= FT.
Hypothesis GSELF : FB + 512 <= SHF \/ SHF + 64 <= FB.
Hypothesis OFFF : FT + 262148 <= 0x7fff7000 \/ 0x10007fff8000 <= FT.
Variable mi : mem.   (* [comment removed for export] *)
Hypothesis LIB0 : OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.L_libA.TwinB__.LIB_A mi.   (* [comment removed for export] *)
Notation PRESI := (PRESI usp fr live0 Wcb mi).
Notation SOK Σ := (sig_ok RT sp0 true 3 FB fr live0 Σ).

Lemma xFc_ok : forall F fc, cbenv_ok (xFc X F fc). Proof. intros. exact XOK. Qed.
Lemma xFc_aok : forall F fc, acenv_ok (xFc X F fc) Y. Proof. intros. exact YOK. Qed.
Lemma xFc_sep : forall F fc, acenv_sep (xFc X F fc) Y. Proof. intros. exact YSEP. Qed.
Lemma CE : cb_entry g e. Proof. exact (conj PRE CBF). Qed.

Lemma cb_shsep_ok_here : cb_shsep X Y.
Proof. eapply cb_shsep_ok; eassumption. Qed.
Ltac shsep_open :=
  let H := fresh "SHS" in pose proof (cb_shsep_ok_here) as H; unfold cb_shsep in H;
  destruct H as (?DEA1 & ?DEA2 & ?DEFT & ?DA1A2 & ?DA1FT & ?DA2FT & ?DEFB & ?DA1FB & ?DA2FB & ?DFTFB & ?DESH & ?DA1SH & ?DA2SH & ?DFTSH & ?DFBSH & ?XL1 & ?XL2 & ?XL3 & ?XL4 & ?XL5 & ?XL6 & ?XL7 & ?XL8 & ?XL9 & ?XL10 & ?XL11 & ?XL12 & ?XL13 & ?XL14 & ?XL15 & ?XL16);
  box_ors.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Ltac cb_keys :=
  pose proof (ck_intro P CStack) as KP; pose proof (ck_intro usp CStack) as KU; pose proof (ck_intro FB CFrame) as KFB; pose proof (ck_intro SHF CShadow) as KSH;
  pose proof (ck_intro E (CLive E 55768)) as KE; pose proof (ck_intro A1 (CLive A1 ARR1_SIZE)) as KA1; pose proof (ck_intro A2 (CLive A2 ARR2_SIZE)) as KA2;
  pose proof (ck_intro FT (CLive FT 262148)) as KFT.
Ltac fp_ours := per_interval; cbn [outside]; lia.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac act_open :=
  shsep_open; cb_keys;
  pose proof G as [_ _ _ _ GLOW GLOR GPUS GSPT GSPA GFR GSH GSP0 _ _]; unfold USTACK_TOP, RT_STACK, STACK_WIN, SEGTOP_A in GLOW, GLOR, GSPT, GFR, GSH, GSP0;
  pose proof (ag_ax G) as AX; pose proof alloc_ceiling_range as ACR.
Ltac cutL R k H nb :=
  let T := fresh "T" in
  lazymatch type of R with rw_cells ?segs ?m ?A ?cs =>
    destruct (rw_cells_cutZ segs m A cs k R) as [H T]; clear R; rename T into R;
    cbn [firstn skipn cells_size csize Nat.add] in H, R;
    lazymatch type of R with rw_cells _ _ ?A' _ => replace A' with nb in R by (cbn; lia) end
  end.
(* [comment removed for export] *)
Ltac cb_appfp :=
  let XL7 := ident:(XL7) in let OFFE' := ident:(OFFE') in let OFF1' := ident:(OFF1') in let OFF2' := ident:(OFF2') in let OFFF' := ident:(OFFF') in let FHI' := ident:(FHI') in
  cbn [app_fp]; unfold SH_LO, SH_HI;
  repeat (split; [first [ right; clear - XL7; lia
                        | clear - OFFE'; lia | clear - OFF1'; lia | clear - OFF2'; lia | clear - OFFF'; lia | clear - FHI'; lia ]|]); exact I.
Ltac cb_gotapart :=
  let XL7 := ident:(XL7) in let XL14 := ident:(XL14) in let XEi := ident:(XEi) in let XA1i := ident:(XA1i) in let XA2i := ident:(XA2i) in let XFTi := ident:(XFTi) in
  cbn [disjoint_from aci_got_sh aci_shvar B0C]; repeat (split; [left; clear - XEi XA1i XA2i XFTi XL14 XL7; lia|]); exact I.

(* [comment removed for export] *)
Ltac offsh_open :=
  pose proof YOFF as YOFF'; unfold acenv_offsh, ESTATE_SIZE, SH_LO, SH_HI in YOFF'; cbv zeta in YOFF'; destruct YOFF' as (OFFE' & OFF1' & OFF2' & FHI');
  pose proof OFFF as OFFF'.

Notation RB ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s3 s4 s6 s7 s9 s10 t3 t4 t5 t6 :=
  (mkR ra cP gp tp t0 t1 t2 (ce_sp X) cP a0 a1 a2 a3 a4 a5 a6 a7
       cSB s3 s4 (Z_to_bv 64 FB) s6 s7 (Z_to_bv 64 FB) s9 s10 (Z_to_bv 64 SHF) t3 t4 t5 t6).
Notation ILW := (il_w il).
Notation g1 := (EG (g_aie g) true (g_mtf g) (g_bs g) (g_zbits g)).
Notation g3h := (g3 X g1 (cbE1 e)).
Notation g3z := (g3 X g (cbZ0 e)).
(* [comment removed for export] *)
Notation gF := (EG (g_aie g) true true true (Z_to_bv 64 (A2 + nb))).

Lemma cb_readers' : forall Σ (m : mem) W, SOK Σ -> ART RT Σ m -> app_fp W ->
  disjoint_from W (aci_got_sh B0C) 8 -> disjoint_from W (aci_shvar B0C) 8 -> acoW W m /\ cctx_sh b0segs cx W m.
Proof. intros. eapply cb_readers; eassumption. Qed.

(* [comment removed for export] *)
Lemma cbZBL_eq : forall e0 b, cbZBL e0 b = CmpCut.zbl (e_arr2 (cbE1 e0)) (e_nblock e0) b. Proof. reflexivity. Qed.
Lemma cbED_def : forall e0, cbED e0 = est_D (cbEG e0) znew znew znew znew znew znew znew. Proof. reflexivity. Qed.

(* [comment removed for export] *)
Lemma cbEU5_rest : 0 < nb ->
  e_unseqToSeq (cbEU5 e) = e_unseqToSeq e /\ e_mtfFreq (cbEU5 e) = e_mtfFreq e /\
  e_selector (cbEU5 e) = e_selector e /\ e_selectorMtf (cbEU5 e) = e_selectorMtf e /\ e_len (cbEU5 e) = e_len e /\
  e_code (cbEU5 e) = e_code e /\ e_rfreq (cbEU5 e) = e_rfreq e /\ e_len_pack (cbEU5 e) = e_len_pack e.
Proof.
  intros POS. destruct (cbE1_shape g e CE POS) as (sa1 & sa2 & sft & sop & E1 & _).
  unfold cbEU5, est_set_arr2, est_set_bw. rewrite E1.
  cbn [e_mode e_state e_avail_in_expect e_arr1 e_arr2 e_ftab e_origPtr e_state_in_ch e_state_in_len e_nblock e_state_out_pos e_nInUse
       e_inUse e_unseqToSeq e_bw e_blockCRC e_combinedCRC e_blockNo e_nMTF e_mtfFreq e_selector e_selectorMtf e_len e_code e_rfreq e_len_pack].
  repeat split; reflexivity.
Qed.

(* [comment removed for export] *)
Ltac canon_in H :=
  unfold EH1b, EH2b, AR2b, EHEAD1, EHEAD2, EHEAD1n, cbEU5, cbZBL in H;
  cbn [e_mode e_state e_avail_in_expect e_arr1 e_arr2 e_ftab e_origPtr e_state_in_ch e_state_in_len e_nblock e_state_out_pos e_nInUse
       e_inUse e_unseqToSeq e_bw e_blockCRC e_combinedCRC e_blockNo e_nMTF e_mtfFreq e_selector e_selectorMtf e_len e_code e_rfreq e_len_pack
       est_set_bw est_set_arr2 g_aie g_sort g_mtf g_bs g_zbits xFc ce_cx] in H.
Ltac canon_goal :=
  unfold EH1b, EH2b, AR2b, EHEAD1, EHEAD2, EHEAD1n, cbEU5, cbZBL;
  cbn [e_mode e_state e_avail_in_expect e_arr1 e_arr2 e_ftab e_origPtr e_state_in_ch e_state_in_len e_nblock e_state_out_pos e_nInUse
       e_inUse e_unseqToSeq e_bw e_blockCRC e_combinedCRC e_blockNo e_nMTF e_mtfFreq e_selector e_selectorMtf e_len e_code e_rfreq e_len_pack
       est_set_bw est_set_arr2 g_aie g_sort g_mtf g_bs g_zbits xFc ce_cx].

Notation Wmtf := [(E, E + 55768); (A1, A1 + ARR1_SIZE); (A2, A2 + ARR2_SIZE); (P, P + 184); (FB + 32, FB + 288); (SHF + 4, SHF + 36)].

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma cb_mtf : forall (Σ2 : rts RT) (m : mem) (sl : cbslB)
    (ra t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 : word) F fc T c,
  0 < nb -> SOK Σ2 -> 25 <= rt_credit RT Σ2 ->
  q32 sl = ILW -> q40 sl = Z_to_bv 64 (E + 652) -> q48 sl = Z_to_bv 64 (E + 656) -> q56 sl = Z_to_bv 64 (SHE + 10) -> q64 sl = Z_to_bv 64 (E + 80) ->
  q88 sl = Z_to_bv 64 E -> q144 sl = Z_to_bv 64 (SHE + 13) ->
  EH1b X g3h (cbE1 e) m (cbBH e) -> EH2b X g3h (cbE1 e) m (cbBH e) -> AR2b X (cbE1 e) m (cbBH e) ->
  u8arr b0segs m (E + 128) (ovb (e_inUse e) (jseg J 128 256) 256) ->
  u8arr b0segs m (E + 384) (ovb (e_unseqToSeq e) (jseg J 384 256) 256) ->
  u32arr b0segs m (E + 672) (ovw (e_mtfFreq e) (jseg J 672 1032) 258) ->
  u8arr b0segs m (E + 1704) (ovb (e_selector e) (jseg J 1704 18002) 18002) ->
  u8arr b0segs m (E + 19706) (ovb (e_selectorMtf e) (jseg J 19706 18002) 18002) ->
  u8arr b0segs m (E + 37708) (ovb (e_len e) (jseg J 37708 1548) 1548) ->
  u32arr b0segs m (E + 39256) (ovw (e_code e) (jseg J 39256 6192) 1548) ->
  u32arr b0segs m (E + 45448) (ovw (e_rfreq e) (jseg J 45448 6192) 1548) ->
  u32arr b0segs m (E + 51640) (ovw (e_len_pack e) (jseg J 51640 4128) 1032) ->
  u8arr b0segs m A1 (zb8 (e_arr1 (cbE1 e)) ARR1_SIZE) -> u32arr b0segs m FT (zw32 (e_ftab (cbE1 e)) 65537) ->
  rw_cells b0segs m P (cbslB_cells sl) -> rw_cells b0segs m (SHF + 4) (yysh cf8b) -> wr_at bsegs m (FB + 32) 256 -> wr_at bsegs m SHF 64 ->
  ART RT Σ2 m -> KMem.mem_inv bsegs m -> stk bsegs m lo P -> PRESI m ->
  ASTA RT Σ2 PMc (eq (MS (RB ra t0 t1 t2 (Z_to_bv 64 (E + 56)) (Z_to_bv 64 (SHE + 80)) a2 a3 a4 a5 a6 a7 (Z_to_bv 64 (SHE + 10)) (Z_to_bv 64 (E + 116))
                             (Z_to_bv 64 (E + 108)) (Z_to_bv 64 E) (Z_to_bv 64 (E + 644)) (Z_to_bv 64 (E + 640)) t3 t4 t5 (Z_to_bv 64 (E + 80)))
                         F (Z_to_bv 64 0x8a11c) fc None m (seg_rom b0segs))) c ->
  (forall c' (Σ3 : rts RT) (m' : mem) (Xo : est) (sl' : cbslB) (ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a7' s6' s7' t3' t4' t5' t6' : word) F' fc',
     let eD := est_D Xo znew znew znew znew znew znew znew in
     ASTA RT Σ3 PMc (eq (MS (RB ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' (Z_to_bv 64 E) a7' ILW (Z_to_bv 64 (E + 116)) s6' s7' (Z_to_bv 64 (E + 644)) (Z_to_bv 64 (E + 640)) t3' t4' t5' t6')
                            F' (Z_to_bv 64 0x8aa58) fc' None m' (seg_rom b0segs))) c' ->
     Xo = gm_e (cbEU5 e) -> e_nblock Xo = nb -> e_arr2 Xo = zbl (e_arr2 (cbE1 e)) nb (cbBH e) ->
     0 <= bw_numZ (cbBH e) <= bw_numZ (e_bw eD) -> nb + bw_numZ (e_bw eD) + 64 <= ARR2_SIZE ->
     0 <= e_combinedCRC Xo < 4294967296 -> BzCLemmas1.bw_ok (e_bw eD) ->
     SOK Σ3 -> rt_live RT Σ3 = rt_live RT Σ2 -> rt_frames RT Σ3 = rt_frames RT Σ2 -> rt_credit RT Σ2 - 25 <= rt_credit RT Σ3 <= rt_credit RT Σ2 - 1 ->
     q40 sl' = Z_to_bv 64 (E + 652) -> q48 sl' = Z_to_bv 64 (E + 656) -> q56 sl' = Z_to_bv 64 (SHE + 10) -> q64 sl' = Z_to_bv 64 (E + 80) -> q88 sl' = Z_to_bv 64 E ->
     emem cx b0segs gF eD m' ->
     u8arr b0segs m' A1 (zb8 (e_arr1 Xo) ARR1_SIZE) -> u8arr b0segs m' A2 (zb8 (CmpCut.zbl (e_arr2 Xo) (e_nblock Xo) (e_bw eD)) ARR2_SIZE) ->
     u32arr b0segs m' FT (zw32 (e_ftab Xo) 65537) ->
     rw_cells b0segs m' P (cbslB_cells sl') -> rw_cells b0segs m' (SHF + 4) (yysh cf8b) -> wr_at bsegs m' (FB + 32) 256 -> wr_at bsegs m' SHF 64 ->
     ART RT Σ3 m' -> KMem.mem_inv bsegs m' -> stk bsegs m' lo P -> PRESI m' ->
     rt_pres_fp (rt_live RT Σ2) (rt_frames RT Σ2) P Wmtf m m' ->
     realizes bsegs c' T) ->
  realizes bsegs c T.
Proof.
  intros Σ2 m sl ra t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 F fc T c POS SK CRED H32 H40 H48 H56 H64 H88 H144 EH1 EH2 AR2 INU UNS MTF SEL SELM LEN CODE RFQ LPK AR1 FTB SL YYSH WRY WRS
    ART0 MI0 ST0 PR0 Hc Hk.
  act_open. offsh_open. bz_params. cbenv_open XOK. acenv_open YOK.
  pose proof SK as (FRM & SP0E & LIVS). pose proof (LIVS _ LIVE) as LVE. pose proof (LIVS _ LIV1) as LV1. pose proof (LIVS _ LIV2) as LV2. pose proof (LIVS _ LIVF) as LVF.
  (* [comment removed for export] *)
  destruct (cb_entry_facts g e CE) as (OK & NBR & DEFR & IU & POS0 & NZ & B1 & ALT).
  pose proof (cb_sorted_fields e) as SF. change (cb_sorted e) with (cbE1 e) in SF. destruct SF as (F1 & F2 & F3 & F4).
  destruct (cbBH_facts g e CE POS) as (OKH & NH & BH & LH & BC1 & OP1 & _). pose proof OKH as (OKHb & OKHl & OKHn).
  destruct (cbEU5_facts g e CE POS) as (GF5 & N5 & B5 & A5 & A15 & FT5 & I5 & NI5 & BN5 & ZB5).
  destruct (cbEU5_rest POS) as (FE1 & FE2 & FE3 & FE4 & FE5 & FE6 & FE7 & FE8).
  pose proof (cbEG_facts g e CE POS) as GP.
  destruct (cbED_fields g e CE POS) as (D1 & D2 & D3 & D4 & D5 & D6 & D7 & D8 & D9 & D10 & D11).
  destruct (cbED_room g e CE POS) as (R1 & R2 & R3).
  destruct (maps_facts _ GF5) as (NI & _ & _).
  set (nI := gp_nInUse (cbEU5 e)) in *.
  (* [comment removed for export] *)
  rewrite <- I5 in INU. rewrite <- FE1 in UNS. rewrite <- FE2 in MTF. rewrite <- FE3 in SEL. rewrite <- FE4 in SELM. rewrite <- FE5 in LEN. rewrite <- FE6 in CODE.
  rewrite <- FE7 in RFQ. rewrite <- FE8 in LPK. rewrite <- A15 in AR1. rewrite <- FT5 in FTB.
  unfold EH1b in EH1. unfold EH2b in EH2. unfold AR2b in AR2. rewrite F1 in AR2. rewrite <- (cbZBL_eq e (cbBH e)) in AR2. rewrite <- A5 in AR2.
  (* [comment removed for export] *)
  eapply (l1_realizes RT AF Σ2 PMc _ T c MST Hc).
  eapply (B0_cb_scope_begin (xFc X F fc) Y _ (xFc_aok F fc) m); [exact YYSH| exact (kmem_inv_N _ _ MI0)|].
  clear Hc YYSH. intros m1 YYSH NMI1 MU1 WM1. apply evt_done. intros c1 Hc1.
  cbn [xFc ce_cx ce_sp ce_gp ce_tp ce_il ce_F ce_fc] in Hc1.
  lazymatch type of MU1 with munch ?W _ _ => destruct (after_l1 AF G Σ2 W m m1 SK ART0 MI0 ST0 PR0 NMI1 MU1 WM1 ltac:(fp_ours)) as (ART1 & MI1 & ST1 & PR1 & STEP1) end.
  xfer_l1 m m1 MU1 WM1. clear NMI1 MU1 WM1.
  (* [comment removed for export] *)
  destruct (n_wr_at_rw_CB m1 (FB + 32) 256 WRY ltac:(clear; lia)) as (Jy & YYj). change (Z.to_nat 256) with 256%nat in YYj.
  destruct (rw_cells_CB_C1s b0segs _ _ _ _ YYj) as [_ LJy]. pose proof (u8arr_of_rw_cells b0segs m1 _ _ _ YYj) as YY. clear YYj.
  assert (AFW : app_fp (cbG_W (xFc X F fc) Y)) by (unfold cbG_W; cbn [xFc ce_cx]; cb_appfp).
  destruct (cb_readers' Σ2 m1 (cbG_W (xFc X F fc) Y) SK ART1 AFW ltac:(unfold cbG_W; cbn [xFc ce_cx]; cb_gotapart) ltac:(unfold cbG_W; cbn [xFc ce_cx]; cb_gotapart)) as (_ & SHe & SH1 & SH2 & _).
  assert (SHy : shzW b0segs (cbG_W (xFc X F fc) Y) m1 (FB + 32) (FB + 288)).
  { destruct (n_rw_cells_bytes b0segs m1 _ _ YYSH) as [BYy _]. rewrite yysh_bytes in BYy. destruct AX as [AX1 AX2].
    pose proof (acc_of_zero_shadow b0segs m1 FB SHF 4 32 AX1 AX2 ltac:(clear - GFR; lia) ltac:(clear; lia) BYy) as ACCy.
    replace (FB + 8 * 4) with (FB + 32) in ACCy by (clear; lia). change (8 * Z.of_nat 32) with 256 in ACCy.
    apply (shzW_of_acc b0segs _ m1 (FB + 32) 256 (FB + 32) (FB + 288) ACCy AFW); [clear - GFR; lia| clear - GFR GSP0; lia| clear; lia| clear - AX1; Z.div_mod_to_equations; lia]. }
  eapply (l1_realizes RT AF Σ2 PMc _ T c1 MST Hc1).
  eapply (B0_cb_G (xFc X F fc) Y g3h (cbEU5 e) _ (xFc_ok F fc) (xFc_aok F fc) (xFc_sep F fc) AE GF5 m1 sl Jy);
    [rewrite N5; exact POS| exact H32| exact H88| exact H144
    | canon_goal; canon_in EH1; exact EH1| exact INU| exact UNS| canon_goal; canon_in EH2; exact EH2| exact MTF| exact AR1| exact AR2| exact YY| rewrite LJy; reflexivity
    | exact SL| exact (kmem_inv_N _ _ MI1)| exact SHe| exact SH1| exact SH2| exact SHy|].
  clear Hc1 EH1 INU UNS EH2 MTF AR1 AR2 YY SL SHe SH1 SH2 SHy AFW.
  intros m4 Jy' ra4 t0_4 t1_4 t2_4 a0_4 a1_4 a2_4 a3_4 a5_4 a6_4 a7_4 s6_4 s7_4 t3_4 t4_4 t5_4 t6_4 EH1 INU UNS EH2 MTF AR1 AR2 YY LJy' SL NMI4 MU4 WM4. apply evt_done. intros c4 Hc4.
  cbn [xFc ce_cx ce_sp ce_gp ce_tp ce_il ce_F ce_fc] in EH1, INU, UNS, EH2, MTF, AR1, AR2, YY, MU4, Hc4. unfold cbG_W in MU4. cbn [xFc ce_cx] in MU4.
  lazymatch type of MU4 with munch ?W _ _ => destruct (after_l1 AF G Σ2 W m1 m4 SK ART1 MI1 ST1 PR1 NMI4 MU4 WM4 ltac:(fp_ours)) as (ART4 & MI4 & ST4 & PR4 & STEP4) end.
  xfer_l1 m1 m4 MU4 WM4. clear NMI4 MU4 WM4 YY LJy' LJy.
  (* [comment removed for export] *)
  lazymatch type of SL with rw_cells _ _ _ (cbslB_cells ?slx) =>
    assert (K40 : q40 slx = Z_to_bv 64 (E + 652)) by (unfold slG; cbn [q40 bset16 bset24 bset32 bset72 bset80 bset96 bset104 bset112 bset120 bset128 bset136 bset144 bset152]; exact H40);
    assert (K48 : q48 slx = Z_to_bv 64 (E + 656)) by (unfold slG; cbn [q48 bset16 bset24 bset32 bset72 bset80 bset96 bset104 bset112 bset120 bset128 bset136 bset144 bset152]; exact H48);
    assert (K56 : q56 slx = Z_to_bv 64 (SHE + 10)) by (unfold slG; cbn [q56 bset16 bset24 bset32 bset72 bset80 bset96 bset104 bset112 bset120 bset128 bset136 bset144 bset152]; exact H56);
    assert (K64 : q64 slx = Z_to_bv 64 (E + 80)) by (unfold slG; cbn [q64 bset16 bset24 bset32 bset72 bset80 bset96 bset104 bset112 bset120 bset128 bset136 bset144 bset152]; exact H64);
    assert (K88 : q88 slx = Z_to_bv 64 E) by (unfold slG; cbn [q88 bset16 bset24 bset32 bset72 bset80 bset96 bset104 bset112 bset120 bset128 bset136 bset144 bset152]; exact H88)
  end.
  (* [comment removed for export] *)
  eapply (l1_realizes RT AF Σ2 PMc _ T c4 MST Hc4).
  eapply (B0_cb_scope_end (xFc X F fc) Y _ (xFc_aok F fc) m4); [exact YYSH| exact (kmem_inv_N _ _ MI4)|].
  clear Hc4 YYSH. intros m5 YYSH NMI5 MU5 WM5. apply evt_done. intros c5 Hc5.
  cbn [xFc ce_cx ce_sp ce_gp ce_tp ce_il ce_F ce_fc] in Hc5.
  lazymatch type of MU5 with munch ?W _ _ => destruct (after_l1 AF G Σ2 W m4 m5 SK ART4 MI4 ST4 PR4 NMI5 MU5 WM5 ltac:(fp_ours)) as (ART5 & MI5 & ST5 & PR5 & STEP5) end.
  xfer_l1 m4 m5 MU5 WM5. clear NMI5 MU5 WM5.
  (* [comment removed for export] *)
  assert (ACC5 : rt_pres_fp (rt_live RT Σ2) (rt_frames RT Σ2) P Wmtf m m5).
  { apply (pfp_trans _ _ _ _ m m1 m5); [apply (pfp_weaken _ _ _ _ Wmtf m m1 STEP1); per_interval; cbn [KFrame.outside]; lia|].
    apply (pfp_trans _ _ _ _ m1 m4 m5); [apply (pfp_weaken _ _ _ _ Wmtf m1 m4 STEP4); per_interval; cbn [KFrame.outside]; lia|].
    apply (pfp_weaken _ _ _ _ Wmtf m4 m5 STEP5); per_interval; cbn [KFrame.outside]; lia. }
  clear STEP1 STEP4 STEP5.
  (* [comment removed for export] *)
  pose proof GP as GP'. unfold gm_post in GP'. cbv zeta in GP'.
  destruct GP' as (P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9 & Q10 & Q11 & Q12 & Q13 & Q14 & Q15 & _).
  assert (EGdef : gm_e (cbEU5 e) = cbEG e) by (unfold cbEG; reflexivity). rewrite EGdef in EH1, INU, EH2, UNS, MTF, AR1, AR2. clear EGdef.
  rewrite <- Q14 in SEL. rewrite <- Q15 in SELM. rewrite <- Q10 in LEN. rewrite <- Q11 in CODE. rewrite <- Q12 in RFQ. rewrite <- Q13 in LPK. rewrite <- Q5 in FTB.
  rewrite N5 in Q1. rewrite A5, cbZBL_eq in Q2. rewrite B5 in Q4.
  rewrite (cbED_def e) in R1, R3, D11.
  pose proof (est_D_fields (cbEG e) znew znew znew znew znew znew znew) as DFX. cbv zeta in DFX.
  destruct DFX as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & D16X & _). rewrite D16X in D11. clear D16X.
  assert (HSFA : smA_facts (cbEG e)) by (apply (smA_facts_intro (cbEU5 e) (cbEG e) GP); rewrite N5; clear - NBR POS; lia).
  assert (HSFB : smB_facts (cbEG e) znew znew znew znew znew) by (apply (smB_facts_intro (cbEU5 e) (cbEG e)); [exact GP| rewrite N5; clear - NBR POS; lia]).
  assert (HSDF : sd_facts (est_C (cbEG e) znew znew znew znew znew znew) (smA_ng (cbEG e)) (smB_nsel (cbEG e) znew znew znew znew znew)).
  { apply (sd_facts_intro (cbEU5 e) (cbEG e)); [exact GP| rewrite N5; clear - NBR POS; lia| rewrite I5; exact DEFR| rewrite I5; exact IU]. }
  assert (XEG0 : cbEG e = gm_e (cbEU5 e)) by (unfold cbEG; reflexivity).
  assert (R1' : 0 <= bw_numZ (cbBH e) <= bw_numZ (e_bw (est_D (cbEG e) znew znew znew znew znew znew znew))) by (split; [exact OKHn| exact R1]).
  clear GP P1 P2 P3 P4 P5 P6 P7 P8 Q3 Q5 Q6 Q7 Q8 Q9 Q10 Q11 Q12 Q13 Q14 Q15 R1 R2 GF5 A5 A15 FT5 I5 NI5 BN5 ZB5 D1 D2 D3 D4 D5 D6 D7 D8 D9 D10 FE1 FE2 FE3 FE4 FE5 FE6 FE7 FE8 NI.
  clearbody nI.
  revert EH1 EH2 INU UNS MTF SEL SELM LEN CODE RFQ LPK AR1 AR2 FTB Q1 Q2 Q4 R1' R3 D11 HSFA HSFB HSDF XEG0.
  generalize (cbEG e) as Xo. intros Xo EH1 EH2 INU UNS MTF SEL SELM LEN CODE RFQ LPK AR1 AR2 FTB Q1 Q2 Q4 R1' R3 D11 HSFA HSFB HSDF XEG0.
  assert (HZI : zb8 (CmpCut.zbl (e_arr2 Xo) (e_nblock Xo) (e_bw Xo)) ARR2_SIZE = zb8 (e_arr2 Xo) ARR2_SIZE).
  { rewrite Q2, Q1, Q4. apply zb8_zbl_absorb. clear - OKHn. revert OKHn. generalize (cbBH e) as bH. intros; lia. }
  assert (HBW : BzCLemmas1.bw_ok (e_bw Xo)) by (rewrite Q4; exact OKH).
  assert (HNB : 0 <= e_nblock Xo) by (rewrite Q1; clear - POS; lia).
  assert (HROOM : e_nblock Xo + bw_numZ (e_bw (est_D Xo znew znew znew znew znew znew znew)) <= ARR2_SIZE).
  { rewrite Q1. revert R3. clear. generalize (bw_numZ (e_bw (est_D Xo znew znew znew znew znew znew znew))) as z. intros; lia. }
  pose proof (proj1 HSFB) as STB. unfold smB_static in STB. destruct STB as (_ & HNG & _).
  assert (EM5 : emem cx b0segs (g_mtf_on g3h) Xo m5).
  { unfold emem. split; [exact EH1|]. split; [exact INU|]. split; [exact UNS|]. split; [exact EH2|]. split; [exact MTF|]. split; [exact SEL|]. split; [exact SELM|].
    split; [exact LEN|]. split; [exact CODE|]. split; [exact RFQ| exact LPK]. }
  assert (AM5 : CmpCut.amem cx b0segs Xo m5) by (unfold CmpCut.amem, FTAB_WORDS; split; [exact AR1| split; [exact AR2| exact FTB]]).
  (* [comment removed for export] *)
  refine (cps_realizes bsegs _ _ T c5 (SMC Σ2 PMc _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m5 cx (g_mtf_on g3h) Xo lo FDO MST eq_refl TP
            ltac:(rewrite SP0E; exact ACE) eq_refl eq_refl ltac:(unfold g_mtf_on, g3; cbn [g_zbits]; rewrite Q1, F1; reflexivity) EM5 AM5 LVE LV1 LV2 LVF
            ltac:(rewrite FRM; cbn [length app]; clear - FRB; unfold FRAMES_MAX in *; lia) CRED ART5 MI5
            ltac:(rewrite (P_unsigned G); exact ST5) ltac:(rewrite SP0E; exact GLOW) ltac:(rewrite (P_unsigned G); clear - ROOM; lia)
            ltac:(rewrite (P_unsigned G); unfold USTACK_TOP; clear - GSPT GPUS; lia) ltac:(rewrite (P_unsigned G); exact GSPA) CX SEP IMG HZI HBW HNB HROOM HSFA HSFB HSDF) Hc5 _).
  clear Hc5. intros c6 (Σs & Hq & LVs & FRs & SPs & CRs).
  destruct (ASTA_unpack RT Σs _ _ c6 Hq) as (mss & (m6 & q0 & q1 & q2 & h0 & h1 & h2 & h3 & h4 & h5 & h6 & h7 & q3 & q4 & q5 & q6 & Fs & fcs & -> & ARTs & MIs & STs & EM6 & AR1s & AR2s & FTBs & BWD & STEPs) & Hc6).
  clear Hq. rewrite (P_unsigned G) in STs, STEPs. unfold ESTATE_SIZE in STEPs. unfold FTAB_WORDS in FTBs.
  rewrite (ret_pc_even 0x8aa54 ltac:(lia) eq_refl) in Hc6.
  destruct (after_call G Σ2 Σs _ m5 m6 SK LVs FRs SPs PR5 STEPs ltac:(per_interval; right; cbn [outside]; lia)) as (SKs & PRs).
  clear EH1 EH2 INU UNS MTF SEL SELM LEN CODE RFQ LPK AR1 AR2 FTB EM5 AM5.
  xfer_rtf G SK STEPs m5 m6.
  (* [comment removed for export] *)
  assert (EGF : g_mtf_on g3h = gF) by (unfold g_mtf_on, g3; cbn [g_aie g_sort g_mtf g_bs g_zbits]; rewrite F1; reflexivity).
  rewrite EGF in EM6.
  (* [comment removed for export] *)
  eapply (l1_realizes RT AF Σs PMc _ T c6 MST Hc6).
  eapply (B0_cb_Tld (xFc X Fs fcs) Y _ (xFc_aok Fs fcs) m6); [exact K88| exact SL|].
  clear Hc6. apply evt_done. intros c7 Hc7.
  cbn [xFc ce_cx ce_sp ce_gp ce_tp ce_il ce_F ce_fc ce_lo] in Hc7.
  eapply (Hk c7 Σs m6 Xo _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Fs fcs Hc7 XEG0 Q1 Q2 R1' R3 D11 BWD SKs LVs FRs ltac:(rewrite CRs; clear - HNG; lia));
    [exact K40| exact K48| exact K56| exact K64| exact K88
    | exact EM6| exact AR1s| exact AR2s| exact FTBs| exact SL| exact YYSH| exact WRY| exact WRS| exact ARTs| exact MIs| exact STs| exact PRs|].
  apply (pfp_trans _ _ _ _ m m5 m6 ACC5). apply (pfp_weaken _ _ _ _ Wmtf m5 m6 STEPs). per_interval; cbn [KFrame.outside]; lia.
Qed.

End CBG.
