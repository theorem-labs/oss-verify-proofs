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
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.L2B Require Import L2Kit L2Act L2Stmt B0_fs_L2f B0_cb_L2a B0_cb_L2b.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.L2B Require B0_sessK.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require Import PropExec.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import Tac WalkLib SegsA0 SegsB0.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzTac BzArr BzCMem BzCStream BzCState BzCMtf BzCBlock BzCHuff BzArrD BzCLemmas1 CmpMem CmpCut CmpCutMS CmpCutMtf CmpCutSM CmpCutSmA BzCFactsSmA CmpCutSmB BzCFactsGm BzCSmF1 BzCFactsSmB BzCFactsSd CmpHmKit CmpSmKit CmpSmKit2 AsanKit AsanKit2 AsanCut AsanCutB0.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzCNumZ CmpLaws CmpCutCB BzCFactsSmA2 BzCFactsSmB3 BzCFactsSd2 BzCLemmasMs6 BzCFactsBs6 BzCFactsCb BzCSortPost.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzCHuffF1.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCHuffF1.BzCFactsHm.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import CmpCut6.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import B0_cmp_fsV B0_cmp_msV B0_cmp_cbV B0_cmp_cbP B0_cmp_cbWc B0_cmp_cbH2 B0_cmp_cbT B0_cmp_cbE.
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
Lemma In_f5 : In 245 set_shadow_vals. Proof. unfold set_shadow_vals. do 11 right. left. reflexivity. Qed.

Notation Wtail := [(E + 116, E + 120); (E + 640, E + 648); (A2, A2 + ARR2_SIZE); (P - 48, P); (FB, FB + 8); (SHF, SHF + 64)].

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma cb_tail : forall (gt : eg) (et : est) (b : bw) (Σ3 : rts RT) (m : mem) (sl : cbslB) (h0 h1 h2 : word)
    (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a7 s6 s7 t3 t4 t5 t6 : word) F fc T c,
  g_bs gt = true -> g_zbits gt = Z_to_bv 64 (A2 + e_nblock et) -> 0 <= e_nblock et ->
  BzCLemmas1.bw_ok b -> e_nblock et + bw_numZ b + 40 <= ARR2_SIZE -> 0 <= e_combinedCRC et < 4294967296 ->
  SOK Σ3 ->
  q40 sl = Z_to_bv 64 (E + 652) -> q48 sl = Z_to_bv 64 (E + 656) -> q56 sl = Z_to_bv 64 (SHE + 10) -> q64 sl = Z_to_bv 64 (E + 80) ->
  EH1b X gt et m b -> EH2b X gt et m b -> AR2b X et m b ->
  rw_cells b0segs m P (cbslB_cells sl) -> stk b0segs m (P + 184) (usp + -104) -> rw_cells b0segs m (usp + -104) (CSAVED X) ->
  rw_cells b0segs m FB [C8 h0; C8 h1; C8 h2] -> rw_cells b0segs m (SHF + 4) (yysh cf8b) -> wr_at bsegs m SHF 64 ->
  ART RT Σ3 m -> KMem.mem_inv bsegs m -> stk bsegs m lo P -> PRESI m ->
  ASTA RT Σ3 PMc (eq (MS (RB ra t0 t1 t2 a0 a1 a2 a3 a4 a5 (Z_to_bv 64 E) a7 ILW (Z_to_bv 64 (E + 116)) s6 s7 (Z_to_bv 64 (E + 644)) (Z_to_bv 64 (E + 640)) t3 t4 t5 t6)
                         F (Z_to_bv 64 0x8aa58) fc None m (seg_rom b0segs))) c ->
  (forall c' (Σ4 : rts RT) (m' : mem) (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) F' fc',
     let b' := cb_trailer il b (e_combinedCRC et) in
     ASTA RT Σ4 PMc (eq (MS (mkR (ce_ra X) (ce_sp X) gp tp t0' t1' t2' (ce_s0 X) (ce_s1 X) a0' a1' a2' a3' a4' a5' a6' a7'
                                 (ce_s2 X) (ce_s3 X) (ce_s4 X) (ce_s5 X) (ce_s6 X) (ce_s7 X) (ce_s8 X) (ce_s9 X) (ce_s10 X) (ce_s11 X) t3' t4' t5' t6')
                            F' (ret_pc (ce_ra X)) fc' None m' (seg_rom b0segs))) c' ->
     rt_frames RT Σ4 = fr -> rt_live RT Σ4 = rt_live RT Σ3 -> rt_sp0 RT Σ4 = sp0 -> rt_credit RT Σ4 = rt_credit RT Σ3 ->
     EH1b X gt et m' b' -> EH2b X gt et m' b' -> AR2b X et m' b' -> bw_numZ b <= bw_numZ b' <= bw_numZ b + 36 ->
     ART RT Σ4 m' -> KMem.mem_inv bsegs m' -> stk bsegs m' lo usp -> PRESI m' ->
     rt_pres_fp (rt_live RT Σ3) (rt_frames RT Σ3) P Wtail m m' ->
     realizes bsegs c' T) ->
  realizes bsegs c T.
Proof.
  intros gt et b Σ3 m sl h0 h1 h2 ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a7 s6 s7 t3 t4 t5 t6 F fc T c GBS GZB HNB OKB RM CCR SK H40 H48 H56 H64 EH1 EH2 AR2 SL GAP SAV HD YYSH WRS
    ART0 MI0 ST0 PR0 Hc Hk.
  act_open. offsh_open. bz_params. cbenv_open XOK. acenv_open YOK.
  pose proof SK as (FRM & SP0E & LIVS).
  unfold EH1b in EH1. unfold EH2b in EH2. unfold AR2b in AR2.
  cutL HD 1%nat HD0 (FB + 8).
  (* [comment removed for export] *)
  destruct (cb_readers' Σ3 m (cbT_W (xFc X F fc) Y) SK ART0 ltac:(unfold cbT_W; cbn [xFc ce_cx]; cb_appfp) ltac:(unfold cbT_W; cbn [xFc ce_cx]; cb_gotapart)
              ltac:(unfold cbT_W; cbn [xFc ce_cx]; cb_gotapart)) as (ACW & CSH).
  eapply (l1_realizes RT AF Σ3 PMc _ T c MST Hc).
  eapply (B0_cb_T (xFc X F fc) Y gt et _ (xFc_ok F fc) (xFc_aok F fc) (xFc_sep F fc) AE GBS GZB HNB b m sl);
    [exact OKB| exact RM| exact CCR| exact H40| exact H48| exact H56| exact H64| exact EH1| exact EH2| exact AR2| exact SL| exact HD0| exact (kmem_inv_N _ _ MI0)| exact ST0| exact ACW| exact CSH|].
  clear Hc EH1 EH2 AR2 SL HD0 ST0 ACW CSH.
  intros m1 t0_1 t1_1 t2_1 a2_1 a3_1 a4_1 a5_1 a6_1 a7_1 s3_1 s6_1 s7_1 t3_1 t4_1 t5_1 t6_1. cbv zeta. intros EH1 EH2 AR2 SL HD0 NMI1 ST1n MU1 WM1 NZT. apply evt_done. intros c1 Hc1.
  cbn [xFc ce_cx ce_sp ce_gp ce_tp ce_il ce_F ce_fc ce_lo] in EH1, EH2, AR2, SL, HD0, ST1n, MU1, Hc1, NZT. unfold cbT_W in MU1. cbn [xFc ce_cx] in MU1.
  unfold EH1b in EH1. unfold EH2b in EH2. unfold AR2b in AR2. cbn [xFc ce_cx] in EH1, EH2, AR2.
  lazymatch type of MU1 with munch ?W _ _ =>
    destruct (after_l1_leaf AF G Σ3 W 48 m m1 SK ART0 MI0 PR0 NMI1 MU1 WM1 ltac:(clear; lia) ltac:(clear - ROOM; unfold RT_STACK in *; lia) ltac:(fp_ours)) as (ART1 & MI1 & PR1 & STEP1) end.
  xfer_l1 m m1 MU1 WM1. clear NMI1 MU1 WM1.
  assert (ST1 : stk bsegs m1 lo P) by exact ST1n. clear ST1n.
  (* [comment removed for export] *)
  clear YYSH.
  eapply (ss_call G PMc FDO MST Σ3 245 0 64 m1); [exact SSH| exact SK| exact In_f5| reflexivity| exact ART1| exact MI1| exact ST1| exact WRS| rewrite Z.add_0_r; exact Hc1|].
  clear Hc1. intros c2 m2 u0 u1 u2 v0 e1 e2 e3 e4 e5 e6 e7 u3 u4 u5 u6 F2 fc2 Hc2 ART2 MI2 ST2 WM2 BY2 STEP2.
  replace (SHF + 0 + 64) with (SHF + 64) in STEP2 by (clear; lia). replace (SHF + 0) with SHF in STEP2 by (clear; lia).
  pose proof (pres_step_ours G Σ3 _ _ m1 m2 SK PR1 STEP2 ltac:(right; right; clear; lia)) as PR2.
  xfer_rt G SK STEP2 WM2 m1 m2.
  rewrite (KMState.ret_pc_even 0x8ac50 ltac:(lia) eq_refl) in Hc2.
  clear HD HD0 WRS BY2.
  (* [comment removed for export] *)
  destruct (release_inline2 AF G (mi := mi) Σ3 m2 eq_refl SK ART2) as (Σ4 & fl & FLC & FLP & FL0 & FLW & FLD & REL).
  replace (FB + 512 - 8) with (FB + 504) in FLP by (clear; lia).
  eapply (l1_realizes RT AF Σ3 PMc _ T c2 MST Hc2).
  eapply (B0_cb_E1 (xFc X F2 fc2) Y _ (xFc_aok F2 fc2) m2 fl); [exact (ro_C8_KN m2 _ _ FLP)|].
  eapply (B0_cb_E2 (xFc X F2 fc2) _ m2 fl (Z_to_bv 8 1)); [exact FLC| exact (kmem_inv_N _ _ MI2)|].
  clear Hc2. intros m3 FLC3 NMI3 MU3 WM3. apply evt_done. intros c3 Hc3.
  destruct (REL m3 MU3 WM3 FLC3 MI2 NMI3 ST2 PR2) as (ART3 & FRS3 & LV3 & SP3 & CR3 & AL3 & AM3 & MI3 & ST3 & PR3).
  assert (STEP3 : rt_pres_fp (rt_live RT Σ3) (rt_frames RT Σ3) P Wtail m2 m3).
  { intros a Ha _. apply MU3. cbn [outside]. split; [| exact I].
    destruct (FLD (bv_unsigned a) 1 ltac:(intros x Hx; replace x with (bv_unsigned a) by (clear - Hx; lia); exact Ha)) as [D|D]; clear - D; lia. }
  xfer_fl G SK FLD m2 m3 MU3 WM3.
  pose proof (ASTA_switch RT Σ3 Σ4 PMc _ c3 Hc3 AL3 AM3) as Hc3'. clear Hc3.
  (* [comment removed for export] *)
  eapply (l1_realizes RT AF Σ4 PMc _ T c3 MST Hc3').
  eapply (B0_cb_E3 (xFc X F2 fc2) Y _ (xFc_ok F2 fc2) (xFc_aok F2 fc2) m3 sl); [exact SL| exact GAP| exact SAV| exact ST3|].
  intros STu. apply evt_done. intros c4 Hc4.
  cbn [xFc ce_cx ce_sp ce_gp ce_tp ce_il ce_F ce_fc ce_lo ce_ra ce_s0 ce_s1 ce_s2 ce_s3 ce_s4 ce_s5 ce_s6 ce_s7 ce_s8 ce_s9 ce_s10 ce_s11] in Hc4, STu.
  eapply (Hk c4 Σ4 m3 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F2 fc2 Hc4 FRS3 LV3 SP3 CR3); [exact EH1| exact EH2| exact AR2| exact NZT| exact ART3| exact MI3| exact STu| exact PR3|].
  apply (pfp_trans _ _ _ _ m m1 m3); [apply (pfp_weaken _ _ _ _ Wtail m m1 STEP1); per_interval; cbn [KFrame.outside]; lia|].
  apply (pfp_trans _ _ _ _ m1 m2 m3); [apply (pfp_weaken _ _ _ _ Wtail m1 m2 STEP2); per_interval; cbn [KFrame.outside]; lia| exact STEP3].
Qed.

(* [comment removed for export] *)
Ltac canonF_in H :=
  unfold EH1b, EH2b, AR2b, EHEAD1, EHEAD2, EHEAD1n, cbEF, cbBT, cbED, cbEU5, cbZBL in H;
  cbn [e_mode e_state e_avail_in_expect e_arr1 e_arr2 e_ftab e_origPtr e_state_in_ch e_state_in_len e_nblock e_state_out_pos e_nInUse
       e_inUse e_unseqToSeq e_bw e_blockCRC e_combinedCRC e_blockNo e_nMTF e_mtfFreq e_selector e_selectorMtf e_len e_code e_rfreq e_len_pack
       est_set_bw est_set_arr2 est_D g_aie g_sort g_mtf g_bs g_zbits xFc ce_cx] in H.
Ltac canonF_goal :=
  unfold EH1b, EH2b, AR2b, EHEAD1, EHEAD2, EHEAD1n, cbEF, cbBT, cbED, cbEU5, cbZBL;
  cbn [e_mode e_state e_avail_in_expect e_arr1 e_arr2 e_ftab e_origPtr e_state_in_ch e_state_in_len e_nblock e_state_out_pos e_nInUse
       e_inUse e_unseqToSeq e_bw e_blockCRC e_combinedCRC e_blockNo e_nMTF e_mtfFreq e_selector e_selectorMtf e_len e_code e_rfreq e_len_pack
       est_set_bw est_set_arr2 est_D g_aie g_sort g_mtf g_bs g_zbits xFc ce_cx].
Lemma cbZBL_eqc : forall e0 b, cbZBL e0 b = CmpCut.zbl (e_arr2 (cbE1 e0)) (e_nblock e0) b. Proof. reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma cb_act : forall (Σ1 : rts RT) (sl : cbslB)
    (ra t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc T c,
  SOK Σ1 -> 27 <= rt_credit RT Σ1 ->
  emem cx b0segs g e mi -> CmpCut.amem cx b0segs e mi ->
  rw_cells b0segs mi P (cbslB_cells (bset88 sl (Z_to_bv 64 E))) -> stk b0segs mi (P + 184) (usp + -104) -> rw_cells b0segs mi (usp + -104) (CSAVED X) ->
  wr_at bsegs mi FB 504 -> wr_at bsegs mi SHF 64 ->
  ART RT Σ1 mi -> KMem.mem_inv bsegs mi -> stk bsegs mi lo P ->
  ASTA RT Σ1 PMc (eq (MS (mkR ra cP gp tp t0 t1 t2 (ce_sp X) cP (Z_to_bv 64 FB) a1 a2 a3 a4 a5 a6 a7 cSB ILW s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                         F (Z_to_bv 64 0x899e4) fc None mi (seg_rom b0segs))) c ->
  (forall c' (Σ2 : rts RT) (m' : mem) (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) F' fc',
     ASTA RT Σ2 PMc (eq (MS (mkR (ce_ra X) (ce_sp X) gp tp t0' t1' t2' (ce_s0 X) (ce_s1 X) a0' a1' a2' a3' a4' a5' a6' a7'
                                 (ce_s2 X) (ce_s3 X) (ce_s4 X) (ce_s5 X) (ce_s6 X) (ce_s7 X) (ce_s8 X) (ce_s9 X) (ce_s10 X) (ce_s11 X) t3' t4' t5' t6')
                            F' (ret_pc (ce_ra X)) fc' None m' (seg_rom b0segs))) c' ->
     rt_frames RT Σ2 = fr -> rt_live RT Σ2 = rt_live RT Σ1 -> rt_sp0 RT Σ2 = sp0 -> rt_credit RT Σ1 - 27 <= rt_credit RT Σ2 <= rt_credit RT Σ1 ->
     ART RT Σ2 m' -> KMem.mem_inv bsegs m' -> stk bsegs m' lo usp ->
     (let e' := fst (BzCBlock.compressBlock e il znew) in emem cx b0segs (eg_after_cb cx g e) e' m' /\ CmpCut.amem cx b0segs e' m') ->
     PRESI m' ->
     realizes bsegs c' T) ->
  realizes bsegs c T.
Proof.
  intros Σ1 sl ra t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc T c SK CRED EM AM SL GAP SAV WRF WRS ART0 MI0 ST0 Hc Hk.
  act_open. offsh_open. bz_params. cbenv_open XOK. acenv_open YOK.
  pose proof SK as (FRM & SP0E & LIVS).
  destruct EM as (EH1 & INU & UNS & EH2 & MTF & SEL & SELM & LEN & CODE & RFQ & LPK).
  assert (PR0 : PRESI mi) by (intros a _; reflexivity).
  (* [comment removed for export] *)
  destruct (n_wr_at_rw_CB mi FB 24 (wr_at_sub bsegs mi FB 504 FB 24 WRF ltac:(clear; lia) ltac:(clear; lia) ltac:(clear; lia)) ltac:(clear; lia)) as (jh & HDj).
  change (Z.to_nat 24) with 24%nat in HDj.
  apply (rw_cells_split_CB b0segs _ _ [] 24 _ [] [8;8;8]%nat) in HDj; [| reflexivity]. cbn [mk_CB_cells app] in HDj. cb8_all HDj.
  destruct (n_wr_at_rw_CB mi SHF 44 (wr_at_sub bsegs mi SHF 64 SHF 44 WRS ltac:(clear; lia) ltac:(clear; lia) ltac:(clear; lia)) ltac:(clear; lia)) as (j44 & SHj).
  change (Z.to_nat 44) with 44%nat in SHj.
  eapply (l1_realizes RT AF Σ1 PMc _ T c MST Hc).
  eapply (B0_cb_P2 (xFc X F fc) Y _ (xFc_ok F fc) (xFc_aok F fc) YOFF AX mi sl); [exact SL| exact HDj| exact SHj| exact (kmem_inv_N _ _ MI0)|].
  clear Hc HDj SHj SL. intros m1 y12 y13 SL HD YYSH NMI1 MU1 WM1. apply evt_done. intros c1 Hc1.
  cbn [xFc ce_cx ce_sp ce_gp ce_tp ce_il ce_F ce_fc] in SL, HD, YYSH, MU1, Hc1.
  lazymatch type of MU1 with munch ?W _ _ => destruct (after_l1 AF G Σ1 W mi m1 SK ART0 MI0 ST0 PR0 NMI1 MU1 WM1 ltac:(fp_ours)) as (ART1 & MI1 & ST1 & PR1 & STEP1) end.
  destruct AM as (AR1 & AR2 & FTB). unfold FTAB_WORDS in FTB.
  xfer_l1 mi m1 MU1 WM1. clear NMI1 MU1 WM1 STEP1.
  assert (WRY : wr_at bsegs m1 (FB + 32) 256) by exact (wr_at_sub bsegs m1 FB 504 (FB + 32) 256 WRF ltac:(clear; lia) ltac:(clear; lia) ltac:(clear; lia)).
  clear WRF.
  destruct (Z_lt_dec 0 nb) as [POS|NPOS].
  - (* [comment removed for export] *)
    assert (AM1 : CmpCut.amem cx b0segs e m1) by (unfold CmpCut.amem, FTAB_WORDS; split; [exact AR1| split; [exact AR2| exact FTB]]).
    eapply (cb_head_pos RT AF BSC X Y g e XOK YOK YOFF AE IMG PRE CBF TP PMc fr live0 sp0 FDO MST G ACE ROOM FRB LIVE LIV1 LIV2 LIVF GFE GFA1 GFA2 GFFT GLSE GLSA1 GLSA2 GLSFT GSELF OFFF mi LIB0
              Σ1 m1 (bset176 (bset88 sl (Z_to_bv 64 E)) (Z_to_bv 64 FB)) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc T c1 POS SK ltac:(clear - CRED; lia) eq_refl EH1 EH2 AM1 SL ART1 MI1 ST1 PR1 Hc1).
    clear Hc1 EH1 EH2 AR1 AR2 FTB AM1 SL.
    intros c2 Σ2 m2 sl2 ra2 t0_2 t1_2 t2_2 a2_2 a3_2 a4_2 a5_2 a6_2 a7_2 t3_2 t4_2 t5_2 F2 fc2 Hc2 SK2 LV2 FR2 CR2 K32 K40 K48 K56 K64 K88 K144 EH1 EH2 AR2 AR1 FTB SL ART2 MI2 ST2 PR2 ACC2.
    xfer_rtf G SK ACC2 m1 m2. clear ACC2.
    (* [comment removed for export] *)
    eapply (cb_mtf RT AF SMC X Y g e XOK YOK YSEP YOFF AE IMG PRE CBF TP PMc fr live0 sp0 FDO MST G ACE ROOM FRB LIVE LIV1 LIV2 LIVF GFE GFA1 GFA2 GFFT GLSE GLSA1 GLSA2 GLSFT GSELF OFFF mi
              Σ2 m2 sl2 _ _ _ _ _ _ _ _ _ _ _ _ _ F2 fc2 T c2 POS SK2 ltac:(clear - CRED CR2; lia) K32 K40 K48 K56 K64 K88 K144 EH1 EH2 AR2 INU UNS MTF SEL SELM LEN CODE RFQ LPK AR1 FTB SL YYSH WRY WRS
              ART2 MI2 ST2 PR2 Hc2).
    clear Hc2 EH1 EH2 AR2 INU UNS MTF SEL SELM LEN CODE RFQ LPK AR1 FTB SL YYSH WRY WRS.
    intros c3 Σ3 m3 Xo sl3 ra3 t0_3 t1_3 t2_3 a0_3 a1_3 a2_3 a3_3 a4_3 a5_3 a7_3 s6_3 s7_3 t3_3 t4_3 t5_3 t6_3 F3 fc3 eD Hc3 XEG XN XA2 R1X R3X CCX BWD SK3 LV3 FR3 CR3 K40' K48' K56' K64' K88'
      EM3 AR1 AR2 FTB SL YYSH WRY WRS ART3 MI3 ST3 PR3 ACC3.
    xfer_rtf G SK2 ACC3 m2 m3. clear ACC3 WRY.
    (* [comment removed for export] *)
    pose proof (est_D_fields Xo znew znew znew znew znew znew znew) as DF. cbv zeta in DF. fold eD in DF.
    destruct DF as (_ & _ & _ & D4 & D5 & D6 & _ & _ & _ & D10 & _ & _ & D13 & _ & D15 & D16 & D17 & _).
    destruct EM3 as (EH1 & INU & UNS & EH2 & MTF & SEL & SELM & LEN & CODE & RFQ & LPK).
    (* [comment removed for export] *)
    assert (EH1t : EH1b X gF eD m3 (e_bw eD)).
    { revert EH1. subst eD. unfold EH1b, EHEAD1, est_set_bw.
      cbn [e_mode e_state e_avail_in_expect e_arr1 e_arr2 e_ftab e_origPtr e_state_in_ch e_state_in_len e_nblock e_state_out_pos e_nInUse
           e_inUse e_unseqToSeq e_bw e_blockCRC e_combinedCRC e_blockNo e_nMTF e_mtfFreq e_selector e_selectorMtf e_len e_code e_rfreq e_len_pack est_D].
      intros EH1. exact EH1. }
    assert (EH2t : EH2b X gF eD m3 (e_bw eD)).
    { revert EH2. subst eD. unfold EH2b, EHEAD2, est_set_bw.
      cbn [e_mode e_state e_avail_in_expect e_arr1 e_arr2 e_ftab e_origPtr e_state_in_ch e_state_in_len e_nblock e_state_out_pos e_nInUse
           e_inUse e_unseqToSeq e_bw e_blockCRC e_combinedCRC e_blockNo e_nMTF e_mtfFreq e_selector e_selectorMtf e_len e_code e_rfreq e_len_pack est_D].
      intros EH2. exact EH2. }
    assert (AR2t : AR2b X eD m3 (e_bw eD)) by (unfold AR2b; rewrite D5, D10; exact AR2).
    clear EH1 EH2 AR2.
    eapply (cb_tail gF eD (e_bw eD) Σ3 m3 sl3 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F3 fc3 T c3 eq_refl ltac:(cbn [g_zbits]; rewrite D10, XN; reflexivity) ltac:(rewrite D10, XN; clear - POS; lia) BWD
              ltac:(rewrite D10, XN; revert R3X; clear; generalize (bw_numZ (e_bw eD)) as z; intros; lia) ltac:(rewrite D16; exact CCX) SK3 K40' K48' K56' K64' EH1t EH2t AR2t SL GAP SAV HD YYSH WRS
              ART3 MI3 ST3 PR3 Hc3).
    clear Hc3 EH1t EH2t AR2t SL GAP SAV HD YYSH WRS.
    intros c4 Σ4 m4 t0_4 t1_4 t2_4 a0_4 a1_4 a2_4 a3_4 a4_4 a5_4 a6_4 a7_4 t3_4 t4_4 t5_4 t6_4 F4 fc4 bT' Hc4 FRS4 LV4 SP4 CR4 EH1 EH2 AR2 NZT ART4 MI4 ST4 PR4 ACC4.
    xfer_rtf G SK3 ACC4 m3 m4. clear ACC4.
    eapply (Hk c4 Σ4 m4 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F4 fc4 Hc4 FRS4 ltac:(rewrite LV4, LV3, LV2; reflexivity) SP4 ltac:(rewrite CR4; clear - CR2 CR3; lia) ART4 MI4 ST4); [| exact PR4].
    (* [comment removed for export] *)
    cbv zeta. rewrite (cb_final_eq cb_glue_gm_ok g e il CE POS).
    unfold cbEF, cbBT, cbED. rewrite (cbZBL_eqc e).
    assert (EGX : cbEG e = Xo) by (rewrite XEG; reflexivity). rewrite EGX. fold eD. rewrite D16.
    subst bT'. rewrite D16 in EH1, EH2, AR2, NZT.
    set (bT := cb_trailer il (e_bw eD) (e_combinedCRC Xo)) in *.
    unfold eg_after_cb. replace (0 <? e_nblock e) with true by (symmetry; apply Z.ltb_lt; exact POS). rewrite !Bool.orb_true_r.
    unfold AR2b in AR2. rewrite D5, D10, XN, XA2 in AR2.
    subst eD.
    canonF_in EH1. canonF_in EH2. canonF_in INU. canonF_in UNS. canonF_in MTF. canonF_in SEL. canonF_in SELM. canonF_in LEN. canonF_in CODE.
    canonF_in RFQ. canonF_in LPK. canonF_in AR1. canonF_in FTB.
    split.
    + unfold emem. canonF_goal.
      split; [exact EH1|]. split; [exact INU|]. split; [exact UNS|]. split; [exact EH2|]. split; [exact MTF|].
      split; [exact SEL|]. split; [exact SELM|]. split; [exact LEN|]. split; [exact CODE|]. split; [exact RFQ| exact LPK].
    + unfold CmpCut.amem, FTAB_WORDS. canonF_goal.
      split; [exact AR1|]. split; [| exact FTB].
      assert (BND : 0 <= bw_numZ (cbBH e) <= bw_numZ bT).
      { revert R1X NZT. clear. generalize (e_bw (est_D Xo znew znew znew znew znew znew znew)) as bD. generalize bT as b2. generalize (cbBH e) as bH.
        intros bH b2 bD R1X NZT. lia. }
      rewrite <- (zb8_zbl_absorb (e_arr2 (cbE1 e)) (e_nblock e) (cbBH e) bT _ BND). exact AR2.
  - (* [comment removed for export] *)
    assert (ZE : nb = 0) by (destruct (cb_entry_facts g e CE) as (_ & NBR & _); clear - NBR NPOS; lia).
    destruct (cbZ_facts g e CE ltac:(clear - ZE; lia)) as (OKS & NS & BS & _ & _ & EBZ & _ & CC' & _).
    eapply (cb_head_zero RT AF X Y g e XOK YOK YOFF AE PRE CBF PMc fr live0 sp0 MST G ACE ROOM FRB LIVE LIV1 LIV2 LIVF GFE GFA1 GFA2 GFFT GLSE GLSA1 GLSA2 GLSFT GSELF OFFF mi
              Σ1 m1 (bset176 (bset88 sl (Z_to_bv 64 E)) (Z_to_bv 64 FB)) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc T c1 ZE SK eq_refl EH1 EH2 AR2 SL ART1 MI1 ST1 PR1 Hc1).
    clear Hc1 EH1 EH2 AR2 SL.
    intros c2 m2 sl2 ra2 t0_2 t1_2 t2_2 a0_2 a1_2 a2_2 a3_2 a4_2 a5_2 t3_2 t4_2 t5_2 t6_2 Hc2 K40 K48 K56 K64 K88 EH1 EH2 AR2 SL ART2 MI2 ST2 PR2 ACC2.
    xfer_rtf G SK ACC2 m1 m2. clear ACC2 WRY.
    eapply (cb_tail g3z (cbZ0 e) (cbZS e) Σ1 m2 sl2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc T c2 eq_refl eq_refl ltac:(cbn [e_nblock cbZ0 est_set_bw]; clear - ZE; lia) OKS
              ltac:(cbn [e_nblock cbZ0 est_set_bw]; clear - ZE NS BZbsL__; lia) ltac:(cbn [e_combinedCRC cbZ0 est_set_bw]; exact CC') SK K40 K48 K56 K64 EH1 EH2 AR2 SL GAP SAV HD YYSH WRS
              ART2 MI2 ST2 PR2 Hc2).
    clear Hc2 EH1 EH2 AR2 SL GAP SAV HD YYSH WRS.
    intros c4 Σ4 m4 t0_4 t1_4 t2_4 a0_4 a1_4 a2_4 a3_4 a4_4 a5_4 a6_4 a7_4 t3_4 t4_4 t5_4 t6_4 F4 fc4 bT' Hc4 FRS4 LV4 SP4 CR4 EH1 EH2 AR2 NZT ART4 MI4 ST4 PR4 ACC4.
    xfer_rtf G SK ACC4 m2 m4. clear ACC4.
    eapply (Hk c4 Σ4 m4 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F4 fc4 Hc4 FRS4 LV4 SP4 ltac:(rewrite CR4; clear - CRED; lia) ART4 MI4 ST4); [| exact PR4].
    cbv zeta. rewrite (cb_final_eq0 e il) by (clear - ZE; lia).
    unfold eg_after_cb. replace (0 <? e_nblock e) with false by (rewrite ZE; reflexivity). rewrite !Bool.orb_false_r.
    subst bT'. unfold EH1b in EH1. unfold EH2b in EH2. unfold AR2b in AR2.
    split.
    + unfold emem, cbZF, cbZT.
      cbn [e_mode e_state e_avail_in_expect e_arr1 e_arr2 e_ftab e_origPtr e_state_in_ch e_state_in_len e_nblock e_state_out_pos e_nInUse
           e_inUse e_unseqToSeq e_bw e_blockCRC e_combinedCRC e_blockNo e_nMTF e_mtfFreq e_selector e_selectorMtf e_len e_code e_rfreq e_len_pack est_set_arr2 est_set_bw].
      split; [exact EH1|]. split; [exact INU|]. split; [exact UNS|]. split; [exact EH2|]. split; [exact MTF|].
      split; [exact SEL|]. split; [exact SELM|]. split; [exact LEN|]. split; [exact CODE|]. split; [exact RFQ| exact LPK].
    + unfold CmpCut.amem, FTAB_WORDS, cbZF, cbZT. cbn [e_arr1 e_arr2 e_ftab e_nblock est_set_arr2 est_set_bw].
      split; [exact AR1|]. split; [exact AR2| exact FTB].
Qed.

End CBG.
