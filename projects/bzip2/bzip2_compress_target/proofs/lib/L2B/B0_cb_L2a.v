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
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.L2B Require Import L2Kit L2Act L2Stmt B0_fs_L2f.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.L2B Require B0_sessK.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require Import PropExec.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import Tac WalkLib SegsA0 SegsB0.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzTac BzArr BzCMem BzCStream BzCState BzCMtf BzCBlock BzCHuff BzArrD BzCLemmas1 CmpMem CmpCut CmpCutMS CmpCutMtf CmpCutSM CmpCutSmA BzCFactsSmA CmpCutSmB BzCFactsGm BzCSmF1 BzCFactsSmB BzCFactsSd CmpHmKit CmpSmKit CmpSmKit2 AsanKit AsanKit2 AsanCut AsanCutB0.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzCNumZ CmpLaws CmpCutCB BzCFactsSmA2 BzCFactsSmB3 BzCFactsSd2 BzCLemmasMs6 BzCFactsBs6 BzCFactsCb BzCSortPost.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzCHuffF1.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCHuffF1.BzCFactsHm.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import CmpCut6.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import B0_cmp_fsV B0_cmp_msV B0_cmp_cbV B0_cmp_cbP B0_cmp_cbH1 B0_cmp_cbWc B0_cmp_cbH2 B0_cmp_cbH3 B0_cmp_cbH3z.
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

(* [comment removed for export] *)
Definition cb_shsep : Prop :=
  (E + 55768 <= A1 \/ A1 + ARR1_SIZE <= E) /\
  (E + 55768 <= A2 \/ A2 + ARR2_SIZE <= E) /\
  (E + 55768 <= FT \/ FT + 262148 <= E) /\
  (A1 + ARR1_SIZE <= A2 \/ A2 + ARR2_SIZE <= A1) /\
  (A1 + ARR1_SIZE <= FT \/ FT + 262148 <= A1) /\
  (A2 + ARR2_SIZE <= FT \/ FT + 262148 <= A2) /\
  (E + 55768 <= FB \/ FB + 512 <= E) /\
  (A1 + ARR1_SIZE <= FB \/ FB + 512 <= A1) /\
  (A2 + ARR2_SIZE <= FB \/ FB + 512 <= A2) /\
  (FT + 262148 <= FB \/ FB + 512 <= FT) /\
  (E + 55768 <= SHF \/ SHF + 64 <= E) /\
  (A1 + ARR1_SIZE <= SHF \/ SHF + 64 <= A1) /\
  (A2 + ARR2_SIZE <= SHF \/ SHF + 64 <= A2) /\
  (FT + 262148 <= SHF \/ SHF + 64 <= FT) /\
  (FB + 512 <= SHF \/ SHF + 64 <= FB) /\
  E + 55768 + 4096 <= P /\ A1 + ARR1_SIZE + 4096 <= P /\ A2 + ARR2_SIZE + 4096 <= P /\ FT + 262148 + 4096 <= P /\ FB + 512 + 4096 <= P /\ SHF + 64 + 4096 <= P /\ 17594333495296 + 65536 <= P /\ 0 < A1 /\ 0 < A2 /\ 0 < FT /\ P + 304 <= 18446744073709551616 /\ lo + 65536 + 2064 <= P /\ 0x62b000 <= E /\ 0x62b000 <= FB /\ P + 288 <= usp /\ usp <= P + 304.
Lemma cb_shsep_ok : cb_shsep.
Proof.
  cbenv_open XOK. acenv_open YOK.
  pose proof CX as CX'. unfold cctx_ok in CX'. cbv zeta in CX'. destruct CX' as (RE & RE' & RA1 & RA1' & RA2 & RA2' & RFT & RFT' & _).
  pose proof SEP as SEP'. unfold cctx_sep, apart in SEP'. cbv zeta in SEP'. destruct SEP' as (SEA1 & SEA2 & SEFT & _ & _ & SA1A2 & SA1FT & _ & _ & SA2FT & _).
  pose proof G as [_ _ _ _ GLOW GLOR GPUS GSPT _ GFR GSH GSP0 _ _]. unfold RT_STACK, STACK_WIN, SEGTOP_A, USTACK_TOP, ESTATE_SIZE, FTAB_WORDS, CEIL in *.
  change (4 * 65537) with 262148 in *. pose proof ROOM as ROOM'. unfold RT_STACK in ROOM'.
  pose proof alloc_ceiling_range as ACR.
  unfold cb_shsep.
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
  clear SEA1 SEA2 SEFT SA1A2 SA1FT SA2FT. clear - RE RE' RA1 RA1' RA2 RA2' RFT RFT' GLOW GLOR GPUS GSPT GFR GSH GSP0 ACE ACR ROOM' XEi YFl YPh YPa. repeat split; lia.
Qed.
Ltac shsep_open :=
  let H := fresh "SHS" in pose proof cb_shsep_ok as H; unfold cb_shsep in H;
  destruct H as (?DEA1 & ?DEA2 & ?DEFT & ?DA1A2 & ?DA1FT & ?DA2FT & ?DEFB & ?DA1FB & ?DA2FB & ?DFTFB & ?DESH & ?DA1SH & ?DA2SH & ?DFTSH & ?DFBSH & ?XL1 & ?XL2 & ?XL3 & ?XL4 & ?XL5 & ?XL6 & ?XL7 & ?XL8 & ?XL9 & ?XL10 & ?XL11 & ?XL12 & ?XL13 & ?XL14 & ?XL15 & ?XL16);
  box_ors.

(* [comment removed for export] *)
Lemma cb_lib : forall m : mem, PRESI m -> OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.L_libA.TwinB__.LIB_A m.
Proof.
  intros m PR. apply (OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.L_libA.TwinB__.LIB_locA mi m LIB0). intros a (l0 & h0 & IN & R).
  cbn [OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.D_libiface.TwinB__.LIB_FP In] in IN. cbenv_open XOK.
  assert (RR : 857056 <= bv_unsigned a < 860480) by (destruct IN as [EQ|[EQ|[EQ|[]]]]; injection EQ as <- <-; clear - R; lia).
  apply PR. split.
  - right; left. apply B0_sessK.lib_static. destruct IN as [EQ|[EQ|[EQ|[]]]]; injection EQ as <- <-; clear - R; lia.
  - cbn [outside]. clear - RR XEi XA1i XA2i XFTi. repeat split; lia.
Qed.

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

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma cb_readers : forall Σ (m : mem) W, SOK Σ -> ART RT Σ m -> app_fp W ->
  disjoint_from W (aci_got_sh B0C) 8 -> disjoint_from W (aci_shvar B0C) 8 ->
  acoW W m /\ cctx_sh b0segs cx W m.
Proof.
  intros Σ m W SK ART0 AFW D1 D2. pose proof SK as (_ & SP0E & LIVS).
  pose proof (LIVS _ LIVE) as LVE. pose proof (LIVS _ LIV1) as LV1. pose proof (LIVS _ LIV2) as LV2. pose proof (LIVS _ LIVF) as LVF.
  pose proof G as [_ _ _ _ _ _ _ _ _ _ _ GSP0 _ _]. unfold USTACK_TOP, STACK_WIN, SEGTOP_A in GSP0.
  cbenv_open XOK. pose proof CX as CX'. unfold cctx_ok in CX'. cbv zeta in CX'. destruct CX' as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & ME16 & MA16 & MA26 & MFT & _).
  split.
  - destruct (af_client_consts RT AF Σ m ART0) as (G1 & G2 & _ & _).
    apply acoW_intro; [split; [exact (ro_C8_KN m _ _ G1)| exact (ro_C8_KN m _ _ G2)]| exact D1| exact D2].
  - destruct (af_acc_live RT AF Σ m E 55768 ART0 LVE) as [_ ACCE]. destruct (af_acc_live RT AF Σ m A1 ARR1_SIZE ART0 LV1) as [_ ACC1].
    destruct (af_acc_live RT AF Σ m A2 ARR2_SIZE ART0 LV2) as [_ ACC2]. destruct (af_acc_live RT AF Σ m FT 262148 ART0 LVF) as [_ ACCF].
    pose proof (af_live_range RT AF Σ m E 55768 ART0 LVE) as (EL0 & EL1 & _). pose proof (af_live_range RT AF Σ m A1 ARR1_SIZE ART0 LV1) as (A1L0 & A1L1 & _).
    pose proof (af_live_range RT AF Σ m A2 ARR2_SIZE ART0 LV2) as (A2L0 & A2L1 & _). pose proof (af_live_range RT AF Σ m FT 262148 ART0 LVF) as (FTL0 & FTL1 & _).
    rewrite SP0E in EL1, A1L1, A2L1, FTL1. unfold STACK_WIN in EL1, A1L1, A2L1, FTL1.
    unfold cctx_sh, ESTATE_SIZE.
    split; [apply (shzW_of_acc b0segs W m E 55768 E (E + 55768) ACCE AFW); [clear - EL0; lia| clear - EL1 GSP0; lia| clear; lia| clear - ME16; Z.div_mod_to_equations; lia]|].
    split; [apply (shzW_of_acc b0segs W m A1 ARR1_SIZE A1 (A1 + ARR1_SIZE) ACC1 AFW); [clear - A1L0; lia| clear - A1L1 GSP0; lia| clear; lia| clear - MA16; Z.div_mod_to_equations; lia]|].
    split; [apply (shzW_of_acc b0segs W m A2 ARR2_SIZE A2 (A2 + ARR2_SIZE) ACC2 AFW); [clear - A2L0; lia| clear - A2L1 GSP0; lia| clear; lia| clear - MA26; Z.div_mod_to_equations; lia]|].
    split; [apply (shzW_of_acc b0segs W m FT 262148 FT (FT + 262144) ACCF AFW); [clear - FTL0; lia| clear - FTL1 GSP0; lia| clear; lia| clear - MFT; Z.div_mod_to_equations; lia]|].
    apply (shpW_of_acc b0segs W m FT 262148 ACCF AFW); [clear - FTL0; lia| clear - FTL1 GSP0; lia].
Qed.

Notation Whead := [(E, E + 128); (E + 640, E + 672); (A1, A1 + ARR1_SIZE); (A2, A2 + ARR2_SIZE); (FT, FT + 262148); (P - 48, P + 184)].

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma cb_head_pos : forall (Σ1 : rts RT) (m : mem) (sl : cbslB)
    (ra t0 t1 t2 a2 a3 a4 a5 a7 s4 s6 s7 s9 s10 t3 t4 t5 t6 : word) F fc T c,
  0 < nb -> SOK Σ1 -> 2 <= rt_credit RT Σ1 ->
  q88 sl = Z_to_bv 64 E ->
  rw_cells b0segs m E (EHEAD1 cx g e) -> rw_cells b0segs m (E + 640) (EHEAD2 cx g e) -> CmpCut.amem cx b0segs e m ->
  rw_cells b0segs m P (cbslB_cells sl) ->
  ART RT Σ1 m -> KMem.mem_inv bsegs m -> stk bsegs m lo P -> PRESI m ->
  ASTA RT Σ1 PMc (eq (MS (RB ra t0 t1 t2 (Z_to_bv 64 (-8)) (Z_to_bv 64 (-13)) a2 a3 a4 a5 (Z_to_bv 64 E) a7 ILW s4 s6 s7 s9 s10 t3 t4 t5 t6)
                         F (Z_to_bv 64 0x89b08) fc None m (seg_rom b0segs))) c ->
  (forall c' (Σ2 : rts RT) (m' : mem) (sl' : cbslB) (ra' t0' t1' t2' a2' a3' a4' a5' a6' a7' t3' t4' t5' : word) F' fc',
     ASTA RT Σ2 PMc (eq (MS (RB ra' t0' t1' t2' (Z_to_bv 64 (E + 56)) (Z_to_bv 64 (SHE + 80)) a2' a3' a4' a5' a6' a7' (Z_to_bv 64 (SHE + 10)) (Z_to_bv 64 (E + 116))
                                (Z_to_bv 64 (E + 108)) (Z_to_bv 64 E) (Z_to_bv 64 (E + 644)) (Z_to_bv 64 (E + 640)) t3' t4' t5' (Z_to_bv 64 (E + 80)))
                            F' (Z_to_bv 64 0x8a11c) fc' None m' (seg_rom b0segs))) c' ->
     SOK Σ2 -> rt_live RT Σ2 = rt_live RT Σ1 -> rt_frames RT Σ2 = rt_frames RT Σ1 -> rt_credit RT Σ1 - 2 <= rt_credit RT Σ2 <= rt_credit RT Σ1 - 1 ->
     q32 sl' = ILW -> q40 sl' = Z_to_bv 64 (E + 652) -> q48 sl' = Z_to_bv 64 (E + 656) -> q56 sl' = Z_to_bv 64 (SHE + 10) -> q64 sl' = Z_to_bv 64 (E + 80) ->
     q88 sl' = Z_to_bv 64 E -> q144 sl' = Z_to_bv 64 (SHE + 13) ->
     EH1b X g3h (cbE1 e) m' (cbBH e) -> EH2b X g3h (cbE1 e) m' (cbBH e) -> AR2b X (cbE1 e) m' (cbBH e) ->
     u8arr b0segs m' A1 (zb8 (e_arr1 (cbE1 e)) ARR1_SIZE) -> u32arr b0segs m' FT (zw32 (e_ftab (cbE1 e)) 65537) ->
     rw_cells b0segs m' P (cbslB_cells sl') ->
     ART RT Σ2 m' -> KMem.mem_inv bsegs m' -> stk bsegs m' lo P -> PRESI m' ->
     rt_pres_fp (rt_live RT Σ1) (rt_frames RT Σ1) P Whead m m' ->
     realizes bsegs c' T) ->
  realizes bsegs c T.
Proof.
  intros Σ1 m sl ra t0 t1 t2 a2 a3 a4 a5 a7 s4 s6 s7 s9 s10 t3 t4 t5 t6 F fc T c POS SK CRED H88 EH1 EH2 AM SL ART0 MI0 ST0 PR0 Hc Hk.
  act_open. offsh_open. bz_params. cbenv_open XOK. acenv_open YOK.
  pose proof SK as (FRM & SP0E & LIVS). pose proof (LIVS _ LIVE) as LVE. pose proof (LIVS _ LIV1) as LV1. pose proof (LIVS _ LIV2) as LV2. pose proof (LIVS _ LIVF) as LVF.
  (* [comment removed for export] *)
  destruct (cb_entry_facts g e CE) as (OK & NBR & DEFR & IU & POS0 & NZ & B1 & ALT).
  pose proof OK as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & BC & CC & BN).
  destruct (cbE0_ok g e CE POS) as [OK0 NB0].
  pose proof (cb_sorted_fields e) as SF. change (cb_sorted e) with (cbE1 e) in SF. destruct SF as (F1 & F2 & F3 & F4).
  destruct (cbBS_facts g e CE POS) as (OKS & NS & BS & _ & _ & _).
  destruct (cbBH_facts g e CE POS) as (OKH & NH & BH & LH & BC1 & OP1 & _).
  destruct AM as (AR1 & AR2 & FTB). unfold FTAB_WORDS in FTB.
  (* [comment removed for export] *)
  assert (SHe : shzW b0segs [(E + 116, E + 120); (E + 648, E + 656); (P, P + 184)] m E (E + 55768)).
  { refine (proj1 (proj2 (cb_readers Σ1 m _ SK ART0 _ _ _))); [cb_appfp| cb_gotapart| cb_gotapart]. }
  eapply (l1_realizes RT AF Σ1 PMc _ T c MST Hc).
  eapply (B0_cb_H1 (xFc X F fc) Y g e _ (xFc_ok F fc) (xFc_aok F fc) AE CE m sl); [exact EH1| exact EH2| exact SL| exact (kmem_inv_N _ _ MI0)| exact SHe| | intros ZE; exfalso; clear - ZE POS; lia].
  clear Hc EH1 EH2 SL SHe. intros _ m1 y11 y13 y14 y15 y17 EH1 EH2 SL NMI1 MU1 WM1. apply evt_done. intros c1 Hc1.
  cbn [xFc ce_cx ce_sp ce_gp ce_tp ce_il ce_F ce_fc] in EH1, EH2, SL, MU1, Hc1.
  lazymatch type of MU1 with munch ?W _ _ => destruct (after_l1 AF G Σ1 W m m1 SK ART0 MI0 ST0 PR0 NMI1 MU1 WM1 ltac:(fp_ours)) as (ART1 & MI1 & ST1 & PR1 & STEP1) end.
  xfer_l1 m m1 MU1 WM1. clear NMI1 MU1 WM1.
  (* [comment removed for export] *)
  assert (AM1 : CmpCut.amem cx b0segs (cbE0 e) m1).
  { unfold CmpCut.amem, cbE0, cb_e0. cbv zeta. cbn [e_arr1 e_arr2 e_ftab]. unfold FTAB_WORDS. split; [exact AR1| split; [exact AR2| exact FTB]]. }
  pose proof (cb_lib m1 PR1) as LIB1.
  refine (cps_realizes bsegs _ _ T c1 (BSC Σ1 PMc _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m1 cx g (cbE0 e) lo FDO MST eq_refl TP
            ltac:(rewrite SP0E; exact ACE) EH1 EH2 AM1 LIB1 LVE LV1 LV2 LVF ltac:(rewrite FRM; cbn [length app]; clear - FRB; unfold FRAMES_MAX in *; lia) CRED ART1 MI1
            ltac:(rewrite (P_unsigned G); exact ST1) ltac:(rewrite SP0E; exact GLOW) ltac:(rewrite (P_unsigned G); clear - ROOM; lia)
            ltac:(rewrite (P_unsigned G); unfold USTACK_TOP; clear - GSPT GPUS; lia) ltac:(rewrite (P_unsigned G); exact GSPA) CX SEP IMG OK0
            ltac:(unfold cbE0, cb_e0; cbv zeta; cbn [e_nblock]; clear - NBR POS; lia) (bsX_intro _ OK0 ltac:(unfold cbE0, cb_e0; cbv zeta; cbn [e_nblock]; clear - NBR POS; lia))) Hc1 _).
  clear Hc1. intros c2 (Σb & Hq & LVb & FRb & SPb & CRb).
  destruct (ASTA_unpack RT Σb _ _ c2 Hq) as (msb & (m2 & q0 & q1 & q2 & h0 & h1 & h2 & h3 & h4 & h5 & h6 & h7 & q3 & q4 & q5 & q6 & Fb & fcb & -> & ARTb & MIb & STb & POSTb & STEPb) & Hc2).
  clear Hq. cbv zeta in POSTb. destruct POSTb as (EH1b' & EH2b' & AMb).
  change (fst (fst (fst (blockSort (cbE0 e) znew)))) with (cbE1 e) in EH1b', EH2b', AMb.
  rewrite (P_unsigned G) in STb, STEPb. unfold FTAB_WORDS in STEPb. change (4 * 65537) with 262148 in STEPb.
  rewrite (ret_pc_even 0x89c18 ltac:(lia) eq_refl) in Hc2.
  destruct (after_call G Σ1 Σb _ m1 m2 SK LVb FRb SPb PR1 STEPb ltac:(per_interval; right; cbn [outside]; lia)) as (SKb & PRb).
  clear EH1 EH2 AR1 AR2 FTB AM1 LIB1.
  xfer_rtf G SK STEPb m1 m2.
  destruct AMb as (AR1 & AR2 & FTB). unfold FTAB_WORDS in FTB.
  (* [comment removed for export] *)
  destruct (cb_readers Σb m2 (cbH_W X Y) SKb ARTb ltac:(unfold cbH_W; cb_appfp) ltac:(unfold cbH_W; cb_gotapart) ltac:(unfold cbH_W; cb_gotapart)) as (ACW2 & CSH2).
  pose proof (B0_cb_H2r (xFc X Fb fcb) Y g1 (cbE1 e) (fun ms => forall c', ASTA RT Σb PMc (eq ms) c' -> realizes bsegs c' T) (xFc_ok Fb fcb) (xFc_aok Fb fcb) AE) as H2.
  specialize (H2 ltac:(rewrite F1; clear - POS; lia) m2 (bset144 (bset48 sl (Z_to_bv 64 (E + 656))) (Z_to_bv 64 (SHE + 13)))).
  eapply (l1_realizes RT AF Σb PMc _ T c2 MST Hc2).
  eapply H2; [rewrite F4; reflexivity| rewrite F2; exact BN| rewrite F2, F4; destruct ALT as [A|[GB BOK]]; [left; exact A| right; split; [exact GB| apply bw_ok_reset; exact BOK]]
             | rewrite F1; clear - NBR; lia| cbn [q88 bset144 bset48]; exact H88| reflexivity
             | exact EH1b'| exact EH2b'| exact AR2| exact SL| exact (kmem_inv_N _ _ MIb)| exact STb| exact ACW2| exact CSH2|].
  clear H2 Hc2 EH1b' EH2b' AR2 SL STb ACW2 CSH2.
  intros m3 ra3 t0_3 t1_3 t2_3 a0_3 a1_3 a2_3 a3_3 a4_3 a5_3 t3_3 t4_3 t5_3 t6_3. cbv zeta. intros EH1 EH2 AR2 SL NMI3 ST3n MU3 WM3 OKS' NS'. apply evt_done. intros c3 Hc3.
  cbn [xFc ce_cx ce_sp ce_gp ce_tp ce_il ce_F ce_fc ce_lo] in EH1, EH2, AR2, SL, ST3n, MU3, Hc3. unfold cbH_W in MU3. cbn [xFc ce_cx] in MU3.
  lazymatch type of MU3 with munch ?W _ _ =>
    destruct (after_l1_leaf AF G Σb W 48 m2 m3 SKb ARTb MIb PRb NMI3 MU3 WM3 ltac:(clear; lia) ltac:(clear - ROOM; unfold RT_STACK in *; lia) ltac:(fp_ours)) as (ART3 & MI3 & PR3 & STEP3) end.
  xfer_l1 m2 m3 MU3 WM3. clear NMI3 MU3 WM3.
  assert (ST3 : stk bsegs m3 lo P) by exact ST3n. clear ST3n.
  change (cb_hdr (cbE1 e)) with (cbBS e) in EH1, EH2, AR2.
  (* [comment removed for export] *)
  destruct (cb_readers Σb m3 (cbH3_W X Y) SKb ART3 ltac:(unfold cbH3_W; cb_appfp) ltac:(unfold cbH3_W; cb_gotapart) ltac:(unfold cbH3_W; cb_gotapart)) as (ACW3 & CSH3).
  pose proof (B0_cb_H3 (xFc X Fb fcb) Y g3h (cbE1 e) (fun ms => forall c', ASTA RT Σb PMc (eq ms) c' -> realizes bsegs c' T) (xFc_ok Fb fcb) (xFc_aok Fb fcb) AE eq_refl eq_refl eq_refl) as H3.
  specialize (H3 ltac:(rewrite F1; clear - POS; lia) (cbBS e) m3 (bset56 (bset64 (bset40 (bset144 (bset48 sl (Z_to_bv 64 (E + 656))) (Z_to_bv 64 (SHE + 13))) (Z_to_bv 64 (E + 652))) (Z_to_bv 64 (E + 80))) (Z_to_bv 64 (SHE + 10)))).
  eapply (l1_realizes RT AF Σb PMc _ T c3 MST Hc3).
  eapply H3; [exact OKS| rewrite F1; clear - NS NBR BZbsL__ BZbsH__; lia| exact BC1| exact OP1| rewrite F1; clear - NBR; lia| reflexivity| reflexivity| cbn [q88 bset56 bset64 bset40 bset144 bset48]; exact H88| reflexivity
             | exact EH1| exact EH2| exact AR2| exact SL| exact (kmem_inv_N _ _ MI3)| exact ST3| exact ACW3| exact CSH3| | intros ZE; exfalso; rewrite F1 in ZE; clear - ZE POS; lia].
  clear H3 Hc3 EH1 EH2 AR2 SL ST3 ACW3 CSH3.
  intros _ m4 ra4 t0_4 t1_4 t2_4 a1_4 a2_4 a3_4 a4_4 a5_4 a6_4 a7_4 t3_4 t4_4 t5_4. cbv zeta. intros EH1 EH2 AR2 SL NMI4 ST4n MU4 WM4 OKH' NH'. apply evt_done. intros c4 Hc4.
  cbn [xFc ce_cx ce_sp ce_gp ce_tp ce_il ce_F ce_fc ce_lo] in SL, ST4n, MU4, Hc4. unfold cbH3_W in MU4. cbn [xFc ce_cx] in MU4.
  lazymatch type of MU4 with munch ?W _ _ =>
    destruct (after_l1_leaf AF G Σb W 48 m3 m4 SKb ART3 MI3 PR3 NMI4 MU4 WM4 ltac:(clear; lia) ltac:(clear - ROOM; unfold RT_STACK in *; lia) ltac:(fp_ours)) as (ART4 & MI4 & PR4 & STEP4) end.
  xfer_l1 m3 m4 MU4 WM4. clear NMI4 MU4 WM4.
  assert (ST4 : stk bsegs m4 lo P) by exact ST4n. clear ST4n.
  change (cb_bhdr (cbBS e) (cbE1 e)) with (cbBH e) in EH1, EH2, AR2.
  eapply (Hk c4 Σb m4 (bset32 (bset56 (bset64 (bset40 (bset144 (bset48 sl (Z_to_bv 64 (E + 656))) (Z_to_bv 64 (SHE + 13))) (Z_to_bv 64 (E + 652))) (Z_to_bv 64 (E + 80))) (Z_to_bv 64 (SHE + 10))) ILW)
            _ _ _ _ _ _ _ _ _ _ _ _ _ Fb fcb Hc4 SKb LVb FRb CRb); [reflexivity| reflexivity| reflexivity| reflexivity| reflexivity| cbn [q88 bset32 bset56 bset64 bset40 bset144 bset48]; exact H88| reflexivity
             | exact EH1| exact EH2| exact AR2| exact AR1| exact FTB| exact SL| exact ART4| exact MI4| exact ST4| exact PR4|].
  rewrite LVb, FRb in STEP3, STEP4.
  apply (pfp_trans _ _ _ _ m m1 m4); [apply (pfp_weaken _ _ _ _ Whead m m1 STEP1); per_interval; cbn [KFrame.outside]; lia|].
  apply (pfp_trans _ _ _ _ m1 m2 m4); [apply (pfp_weaken _ _ _ _ Whead m1 m2 STEPb); per_interval; cbn [KFrame.outside]; lia|].
  apply (pfp_trans _ _ _ _ m2 m3 m4); [apply (pfp_weaken _ _ _ _ Whead m2 m3 STEP3); per_interval; cbn [KFrame.outside]; lia|].
  apply (pfp_weaken _ _ _ _ Whead m3 m4 STEP4); per_interval; cbn [KFrame.outside]; lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Notation Whz := [(E, E + 128); (E + 640, E + 672); (A2, A2 + ARR2_SIZE); (P - 48, P + 184)].
Lemma cb_head_zero : forall (Σ1 : rts RT) (m : mem) (sl : cbslB)
    (ra t0 t1 t2 a2 a3 a4 a5 a7 s4 s6 s7 s9 s10 t3 t4 t5 t6 : word) F fc T c,
  nb = 0 -> SOK Σ1 ->
  q88 sl = Z_to_bv 64 E ->
  rw_cells b0segs m E (EHEAD1 cx g e) -> rw_cells b0segs m (E + 640) (EHEAD2 cx g e) -> u8arr b0segs m A2 (zb8 (e_arr2 e) ARR2_SIZE) ->
  rw_cells b0segs m P (cbslB_cells sl) ->
  ART RT Σ1 m -> KMem.mem_inv bsegs m -> stk bsegs m lo P -> PRESI m ->
  ASTA RT Σ1 PMc (eq (MS (RB ra t0 t1 t2 (Z_to_bv 64 (-8)) (Z_to_bv 64 (-13)) a2 a3 a4 a5 (Z_to_bv 64 E) a7 ILW s4 s6 s7 s9 s10 t3 t4 t5 t6)
                         F (Z_to_bv 64 0x89b08) fc None m (seg_rom b0segs))) c ->
  (forall c' (m' : mem) (sl' : cbslB) (ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' t3' t4' t5' t6' : word),
     ASTA RT Σ1 PMc (eq (MS (RB ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' (Z_to_bv 64 E) (Z_to_bv 64 (SHE + 13)) ILW (Z_to_bv 64 (E + 116))
                                (Z_to_bv 64 (E + 108)) (Z_to_bv 64 (E + 648)) (Z_to_bv 64 (E + 644)) (Z_to_bv 64 (E + 640)) t3' t4' t5' t6')
                            F (Z_to_bv 64 0x8aa58) fc None m' (seg_rom b0segs))) c' ->
     q40 sl' = Z_to_bv 64 (E + 652) -> q48 sl' = Z_to_bv 64 (E + 656) -> q56 sl' = Z_to_bv 64 (SHE + 10) -> q64 sl' = Z_to_bv 64 (E + 80) -> q88 sl' = Z_to_bv 64 E ->
     EH1b X g3z (cbZ0 e) m' (cbZS e) -> EH2b X g3z (cbZ0 e) m' (cbZS e) -> AR2b X (cbZ0 e) m' (cbZS e) ->
     rw_cells b0segs m' P (cbslB_cells sl') ->
     ART RT Σ1 m' -> KMem.mem_inv bsegs m' -> stk bsegs m' lo P -> PRESI m' ->
     rt_pres_fp (rt_live RT Σ1) (rt_frames RT Σ1) P Whz m m' ->
     realizes bsegs c' T) ->
  realizes bsegs c T.
Proof.
  intros Σ1 m sl ra t0 t1 t2 a2 a3 a4 a5 a7 s4 s6 s7 s9 s10 t3 t4 t5 t6 F fc T c ZE SK H88 EH1 EH2 AR2 SL ART0 MI0 ST0 PR0 Hc Hk.
  act_open. offsh_open. bz_params. cbenv_open XOK. acenv_open YOK.
  pose proof SK as (FRM & SP0E & LIVS).
  destruct (cb_entry_facts g e CE) as (OK & NBR & DEFR & IU & POS0 & NZ & B1 & ALT).
  pose proof OK as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & BC & CC & BN).
  (* [comment removed for export] *)
  assert (SHe : shzW b0segs [(E + 116, E + 120); (E + 648, E + 656); (P, P + 184)] m E (E + 55768)).
  { refine (proj1 (proj2 (cb_readers Σ1 m _ SK ART0 _ _ _))); [cb_appfp| cb_gotapart| cb_gotapart]. }
  eapply (l1_realizes RT AF Σ1 PMc _ T c MST Hc).
  eapply (B0_cb_H1 (xFc X F fc) Y g e _ (xFc_ok F fc) (xFc_aok F fc) AE CE m sl); [exact EH1| exact EH2| exact SL| exact (kmem_inv_N _ _ MI0)| exact SHe| intros POS; exfalso; clear - ZE POS; lia|].
  clear Hc EH1 EH2 SL SHe. intros _ m1 y10 EH1 EH2 SL NMI1 MU1 WM1. apply evt_done. intros c1 Hc1.
  cbn [xFc ce_cx ce_sp ce_gp ce_tp ce_il ce_F ce_fc] in EH1, EH2, SL, MU1, Hc1.
  lazymatch type of MU1 with munch ?W _ _ => destruct (after_l1 AF G Σ1 W m m1 SK ART0 MI0 ST0 PR0 NMI1 MU1 WM1 ltac:(fp_ours)) as (ART1 & MI1 & ST1 & PR1 & STEP1) end.
  xfer_l1 m m1 MU1 WM1. clear NMI1 MU1 WM1.
  (* [comment removed for export] *)
  destruct (cb_readers Σ1 m1 (cbH_W X Y) SK ART1 ltac:(unfold cbH_W; cb_appfp) ltac:(unfold cbH_W; cb_gotapart) ltac:(unfold cbH_W; cb_gotapart)) as (ACW2 & CSH2).
  eapply (l1_realizes RT AF Σ1 PMc _ T c1 MST Hc1).
  eapply (B0_cb_H2 (xFc X F fc) Y g (cbZ0 e) _ (xFc_ok F fc) (xFc_aok F fc) AE ltac:(cbn [e_nblock cbZ0 est_set_bw]; clear - ZE; lia) m1
            (bset144 (bset48 sl (Z_to_bv 64 (E + 656))) (Z_to_bv 64 (SHE + 13))));
    [exact NZ| exact BN| destruct ALT as [A|[GB BOK]]; [left; exact A| right; split; [exact GB| cbn [e_bw cbZ0 est_set_bw]; rewrite NZ; apply bw_ok_reset; exact BOK]]
    | cbn [e_nblock cbZ0 est_set_bw]; clear - NBR; lia| cbn [q88 bset144 bset48]; exact H88| reflexivity
    | exact EH1| exact EH2| exact AR2| exact SL| exact (kmem_inv_N _ _ MI1)| exact ST1| exact ACW2| exact CSH2|].
  clear Hc1 EH1 EH2 AR2 SL ST1 ACW2 CSH2.
  intros m3 ra3 t0_3 t1_3 t2_3 a0_3 a1_3 a2_3 a3_3 a4_3 a5_3 t3_3 t4_3 t5_3 t6_3. cbv zeta. intros EH1 EH2 AR2 SL NMI3 ST3n MU3 WM3 OKS' NS'. apply evt_done. intros c3 Hc3.
  cbn [xFc ce_cx ce_sp ce_gp ce_tp ce_il ce_F ce_fc ce_lo] in EH1, EH2, AR2, SL, ST3n, MU3, Hc3. unfold cbH_W in MU3. cbn [xFc ce_cx] in MU3.
  lazymatch type of MU3 with munch ?W _ _ =>
    destruct (after_l1_leaf AF G Σ1 W 48 m1 m3 SK ART1 MI1 PR1 NMI3 MU3 WM3 ltac:(clear; lia) ltac:(clear - ROOM; unfold RT_STACK in *; lia) ltac:(fp_ours)) as (ART3 & MI3 & PR3 & STEP3) end.
  xfer_l1 m1 m3 MU3 WM3. clear NMI3 MU3 WM3.
  assert (ST3 : stk bsegs m3 lo P) by exact ST3n. clear ST3n.
  change (cb_hdr (cbZ0 e)) with (cbZS e) in EH1, EH2, AR2.
  (* [comment removed for export] *)
  assert (SHz : shzW b0segs [] m3 E (E + 55768)).
  { refine (proj1 (proj2 (cb_readers Σ1 m3 [] SK ART3 I I I))). }
  eapply (l1_realizes RT AF Σ1 PMc _ T c3 MST Hc3).
  eapply (B0_cb_H3z (xFc X F fc) Y g3z (est_set_bw (cbZ0 e) (cbZS e)) _ (xFc_ok F fc) (xFc_aok F fc) AE m3);
    [exact ZE| exact EH1| exact (kmem_inv_N _ _ MI3)| exact SHz|].
  clear Hc3 SHz. intros a0'. apply evt_done. intros c4 Hc4.
  cbn [xFc ce_cx ce_sp ce_gp ce_tp ce_il ce_F ce_fc ce_lo] in Hc4.
  eapply (Hk c4 m3 (bset56 (bset64 (bset40 (bset144 (bset48 sl (Z_to_bv 64 (E + 656))) (Z_to_bv 64 (SHE + 13))) (Z_to_bv 64 (E + 652))) (Z_to_bv 64 (E + 80))) (Z_to_bv 64 (SHE + 10)))
            _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hc4); [reflexivity| reflexivity| reflexivity| reflexivity| cbn [q88 bset56 bset64 bset40 bset144 bset48]; exact H88| exact EH1| exact EH2| exact AR2| exact SL| exact ART3| exact MI3| exact ST3| exact PR3|].
  apply (pfp_trans _ _ _ _ m m1 m3); [apply (pfp_weaken _ _ _ _ Whz m m1 STEP1); per_interval; cbn [KFrame.outside]; lia|].
  apply (pfp_weaken _ _ _ _ Whz m1 m3 STEP3); per_interval; cbn [KFrame.outside]; lia.
Qed.

End CBG.
