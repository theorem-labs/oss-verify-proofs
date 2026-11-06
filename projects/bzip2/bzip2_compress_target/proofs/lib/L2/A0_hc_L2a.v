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
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A Require L_libA D_libiface.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.L2 Require Import L2Kit L2Act L2Stmt A0_fs_L2f.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require Import PropExec.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import Tac WalkLib SegsA0.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzTac BzArr BzCMem BzCStream BzCState BzCMtf BzCBlock BzCHuff BzArrD BzCLemmas1 CmpMem CmpCut CmpCutMS CmpCutMtf CmpCutSM CmpCutSmA BzCFactsSmA CmpCutSmB BzCFactsGm BzCSmF1 BzCFactsSmB BzCFactsSd CmpHmKit CmpSmKit CmpSmKit2 AsanKit AsanKit2 AsanCut.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzCNumZ CmpLaws CmpCutCB BzCFactsSmA2 BzCFactsSmB3 BzCFactsSd2 BzCLemmasMs6 BzCFactsBs6 BzCFactsCb BzCSortPost.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzCDriver CmpSess CmpSessB.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzCHuffF1 BzTables.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCHuffF1.BzCFactsHm.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import CmpCut6.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import A0_cmp_fsV A0_cmp_msV A0_b2c_hcV A0_b2c_hcR A0_b2c_hcD A0_b2c_hcE A0_b2c_hcG.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeil.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzParams.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Open Scope Z_scope.
#[local] Notation mem := (word -> option byte).

Section HCG.
Context {BZP : BzParams} {ACEIL__ : ACeil}.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Hypothesis MSET : memset_icontract RT e_asan_memset.
Variables (HCXB : cctx -> Z -> eg -> est -> zstrm -> Prop) (CBFACTS : est -> Prop).
Hypothesis CBC : compressBlock_contract RT CBFACTS.
Hypothesis AF_DRV : forall Σ m, ART RT Σ m -> drv_consts m.
(* [comment removed for export] *)
Hypothesis AF_CRC : forall Σ m, ART RT Σ m -> acc asegs m 0xc4000 1024.
(* [comment removed for export] *)
Variables (cx : cctx) (ob on dbza dbzfr : Z) (z0 : zstrm) (nin : Z) (pl OB : list byte) (p1 p2 : word) (lo : Z) (sp gp tp : word).
Hypothesis CX : cctx_ok cx. Hypothesis SEP : cctx_sep cx. Hypothesis IMG : cctx_img (aci_c A0C) cx. Hypothesis LAWS : hc_lawsB HCXB CBFACTS.
Hypothesis TP : tp = Z_to_bv 64 0x5fc0d8.
Hypothesis LOB : Z.of_nat (length OB) = on. Hypothesis OOK : out_okB (aci_c A0C) cx ob on. Hypothesis PAY : pay_condB cx ob on nin pl.
Notation usp := (bv_unsigned sp). Notation P := (usp - 304).
Notation E := (c_E cx). Notation A1 := (c_A1 cx). Notation A2 := (c_A2 cx). Notation FT := (c_FT cx). Notation J := (c_J cx).
Notation STRM := (c_bz cx + BZF_STRM).
Notation sv := (Z_to_bv 64 STDERR_FILE).
Notation cSB := (Z_to_bv 64 2147450880).
Notation cP := (Z_to_bv 64 P).
Variables (SHE SHS : Z).
Hypothesis AE : sanchor E SHE. Hypothesis AS : sanchor STRM SHS.
Variables (PMc : Model -> Prop) (fr : list (Z * nat)) (live0 : list (Z * Z)) (sp0 : Z).
Hypothesis FDO : fdfs_only PMc. Hypothesis MST : mat_stable PMc.
Notation Whc := [(E, E + 55768); (A1, A1 + ARR1_SIZE); (A2, A2 + ARR2_SIZE); (FT, FT + 262148); (ob, ob + on); (STRM, STRM + 80)].
Hypothesis G : act_geom RT lo P usp sp0 false 0 8 2147450881 0 0 fr live0 Whc.
Hypothesis ACE : alloc_ceiling = sp0 - STACK_WIN.
Hypothesis ROOM : lo + RT_STACK + 240 + 1968 <= P.
Hypothesis FRB : (length fr + 3 < FRAMES_MAX)%nat.
Hypothesis LIVE : In (E, 55768) live0. Hypothesis LIV1 : In (A1, ARR1_SIZE) live0. Hypothesis LIV2 : In (A2, ARR2_SIZE) live0. Hypothesis LIVF : In (FT, 262148) live0.
Hypothesis LIVO : In (ob, on) live0.
(* [comment removed for export] *)
Variables (fS : Z) (kS : nat).
Hypothesis INS : In (fS, kS) fr. Hypothesis SFL : fS <= STRM. Hypothesis SFH : STRM + 80 <= fS + fs_size kS - 8.
Variables (pP nP : Z).
Hypothesis PAYL : pl <> [] -> In (pP, nP) live0 /\ pP <= nin /\ nin + Z.of_nat (length pl) <= pP + nP.
(* [comment removed for export] *)
Hypothesis EIMG : 0x61e000 <= E. Hypothesis SLO : 0x61e000 <= STRM. Hypothesis SHI : STRM + 80 <= CmpFsKit0.CEILv.
Hypothesis SES : CmpFsKit0.apartv E ESTATE_SIZE STRM 80. Hypothesis S1S : CmpFsKit0.apartv A1 ARR1_SIZE STRM 80. Hypothesis S2S : CmpFsKit0.apartv A2 ARR2_SIZE STRM 80.
Hypothesis SFS : CmpFsKit0.apartv FT 262148 STRM 80. Hypothesis SOS : CmpFsKit0.apartv ob on STRM 80.
Hypothesis PSS : pl <> [] -> CmpFsKit0.apartv nin (Z.of_nat (length pl)) STRM 80.
Hypothesis OFFE : E + 55768 <= 0x7fff7000 \/ 0x10007fff8000 <= E. Hypothesis OFF1 : A1 + ARR1_SIZE <= 0x7fff7000 \/ 0x10007fff8000 <= A1.
Hypothesis OFF2 : A2 + ARR2_SIZE <= 0x7fff7000 \/ 0x10007fff8000 <= A2. Hypothesis OFFF : FT + 262148 <= 0x7fff7000 \/ 0x10007fff8000 <= FT.
Hypothesis OFFO : ob + on <= 0x7fff7000 \/ 0x10007fff8000 <= ob. Hypothesis OFFS : STRM + 80 <= 0x7fff7000 \/ 0x10007fff8000 <= STRM.
Hypothesis SHSR : 2147450880 <= SHS /\ SHS + 10 <= 17594333495296.
Variable mi : mem.   (* [comment removed for export] *)
Hypothesis SSH0 : bytes_at asegs mi SHS (repeat z8 10). Hypothesis PLM0 : u8ro a0segs mi nin pl. Hypothesis LIB0 : L_libA.LIB_A mi.
Notation PRESI := (PRESI usp fr live0 Whc mi).
Notation SOK Σ := (sig_ok RT sp0 false 0 8 fr live0 Σ).

(* [comment removed for export] *)
Ltac hc_keys :=
  pose proof (ck_intro usp CStack) as KU;
  pose proof (ck_intro E (CLive E 55768)) as KE; pose proof (ck_intro A1 (CLive A1 ARR1_SIZE)) as KA1; pose proof (ck_intro A2 (CLive A2 ARR2_SIZE)) as KA2;
  pose proof (ck_intro FT (CLive FT 262148)) as KFT; pose proof (ck_intro ob (CLive ob on)) as KOB; pose proof (ck_intro (c_bz cx) CCaller) as KST.
Ltac fp_ours := per_interval; cbn [outside]; lia.
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition hc_shsep : Prop :=
  (E + 55768 <= A1 \/ A1 + ARR1_SIZE <= E) /\ (E + 55768 <= A2 \/ A2 + ARR2_SIZE <= E) /\ (E + 55768 <= FT \/ FT + 262148 <= E) /\
  (A1 + ARR1_SIZE <= A2 \/ A2 + ARR2_SIZE <= A1) /\ (A1 + ARR1_SIZE <= FT \/ FT + 262148 <= A1) /\ (A2 + ARR2_SIZE <= FT \/ FT + 262148 <= A2) /\
  (ob + on <= E \/ E + 55768 <= ob) /\ (ob + on <= A1 \/ A1 + ARR1_SIZE <= ob) /\ (ob + on <= A2 \/ A2 + ARR2_SIZE <= ob) /\ (ob + on <= FT \/ FT + 262148 <= ob) /\
  (E + 55768 <= STRM \/ STRM + 80 <= E) /\ (A1 + ARR1_SIZE <= STRM \/ STRM + 80 <= A1) /\ (A2 + ARR2_SIZE <= STRM \/ STRM + 80 <= A2) /\
  (FT + 262148 <= STRM \/ STRM + 80 <= FT) /\ (ob + on <= STRM \/ STRM + 80 <= ob) /\
  E + 55768 + 4096 <= P /\ A1 + ARR1_SIZE + 4096 <= P /\ A2 + ARR2_SIZE + 4096 <= P /\ FT + 262148 + 4096 <= P /\ ob + on + 4096 <= P /\ STRM + 80 + 4096 <= P /\
  17594333495296 + 65536 <= P /\ 0 < A1 /\ 0 < A2 /\ 0 < FT /\ 0 < ob /\ 0 < on /\ usp <= 18446744073709551616 - 16 /\ lo + 65536 + 240 + 1968 <= P /\ 0x61e000 <= A2 /\ 0x61e000 <= A1 /\ 0x61e000 <= FT.
Lemma hc_shsep_ok : hc_shsep.
Proof.
  pose proof CX as CX'. unfold cctx_ok in CX'. cbv zeta in CX'. destruct CX' as (RE & RE' & RA1 & RA1' & RA2 & RA2' & RFT & RFT' & _).
  pose proof SEP as SEP'. unfold cctx_sep, apart in SEP'. cbv zeta in SEP'. destruct SEP' as (SEA1 & SEA2 & SEFT & _ & _ & SA1A2 & SA1FT & _ & _ & SA2FT & _).
  pose proof OOK as OOK'. unfold out_okB, apart in OOK'. destruct OOK' as (RO1 & RO2 & RO3 & RO4 & SO1 & SO2 & SO3 & SO4 & IO).
  pose proof IMG as IMG'. unfold cctx_img, img_apart, IMG_LO3 in IMG'. cbn [ci_hi aci_c A0C] in IMG'. destruct IMG' as (_ & IA1 & IA2 & IFT & _).
  pose proof G as [_ _ _ _ GLOW GLOR GPUS GSPT _ GFR GSH GSP0 _ _]. unfold RT_STACK, STACK_WIN, SEGTOP_A, USTACK_TOP, ESTATE_SIZE, FTAB_WORDS, CEIL, CmpFsKit0.CEILv, CmpFsKit0.apartv in *.
  change (4 * 65537) with 262148 in *. pose proof ROOM as ROOM'. unfold RT_STACK in ROOM'.
  pose proof alloc_ceiling_range as ACR. bz_params.
  unfold hc_shsep.
  split; [exact SEA1|]. split; [exact SEA2|]. split; [exact SEFT|]. split; [exact SA1A2|]. split; [exact SA1FT|]. split; [exact SA2FT|].
  split; [exact SO1|]. split; [exact SO2|]. split; [exact SO3|]. split; [exact SO4|].
  split; [exact SES|]. split; [exact S1S|]. split; [exact S2S|]. split; [exact SFS|]. split; [exact SOS|].
  assert (A2I : 0x61e000 <= A2) by (destruct IA2 as [D|D]; [exfalso; clear - D RA2 BZbsL__; lia| clear - D; lia]).
  assert (A1I : 0x61e000 <= A1) by (destruct IA1 as [D|D]; [exfalso; clear - D RA1 BZbsL__; lia| clear - D; lia]).
  assert (FTI : 0x61e000 <= FT) by (destruct IFT as [D|D]; [exfalso; clear - D RFT; lia| clear - D; lia]).
  clear SEA1 SEA2 SEFT SA1A2 SA1FT SA2FT SO1 SO2 SO3 SO4 IO IA1 IA2 IFT.
  clear - RE RE' RA1 RA1' RA2 RA2' RFT RFT' RO1 RO2 RO3 GLOW GLOR GPUS GSPT GSP0 ACE ACR ROOM' SHI A2I A1I FTI. repeat split; lia.
Qed.
(* [comment removed for export] *)
Ltac shsep_open :=
  let H := fresh "SHS" in pose proof hc_shsep_ok as H; unfold hc_shsep in H;
  destruct H as (?DEA1 & ?DEA2 & ?DEFT & ?DA1A2 & ?DA1FT & ?DA2FT & ?DOE & ?DOA1 & ?DOA2 & ?DOFT & ?DES & ?DA1S & ?DA2S & ?DFTS & ?DOS &
                 ?XL1 & ?XL2 & ?XL3 & ?XL4 & ?XL5 & ?XL6 & ?XL7 & ?XL8 & ?XL9 & ?XL10 & ?XL11 & ?XL12 & ?XL13 & ?XL14 & ?XL15 & ?XL16 & ?XL17);
  box_ors.
Ltac act_open :=
  shsep_open; hc_keys;
  pose proof G as [_ _ _ _ GLOW GLOR GPUS GSPT GSPA _ _ GSP0 _ _]; unfold USTACK_TOP, RT_STACK, STACK_WIN, SEGTOP_A in GLOW, GLOR, GSPT, GSP0;
  pose proof alloc_ceiling_range as ACR;
  assert (SCL : forall x, STRM <= x < STRM + 80 -> aclient live0 fr usp x)
    by (intros x Hx; right; right; right; left; exists fS, kS; split; [exact INS| clear - Hx SFL SFH; lia]).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma hc_strm_sh : forall (m : mem), PRESI m -> bytes_at asegs m SHS (repeat z8 10).
Proof.
  intros m PR. apply (bytes_at_agree a0segs mi m SHS _ SSH0). intros a Ha. cbv beta in Ha. rewrite repeat_length in Ha. change (Z.of_nat 10) with 10 in Ha.
  apply PR. destruct AS as [AS1 AS2]. destruct SHSR as [SR0 SR1]. split.
  - right; right; right; right. exists fS, kS. split; [exact INS|]. unfold shad, SHB. rewrite AS2 in Ha.
    pose proof SFH as SFH'. revert SFH'. generalize (fs_size kS). intros fsz SFH'. clear - Ha SFL SFH' AS1. Z.div_mod_to_equations. lia.
  - pose proof OFFE as D1. pose proof OFF1 as D2. pose proof OFF2 as D3. pose proof OFFF as D4. pose proof OFFO as D5. pose proof OFFS as D6.
    cbn [outside]. clear - Ha SR0 SR1 D1 D2 D3 D4 D5 D6. repeat split; lia.
Qed.

Lemma hc_pay : forall (m : mem), PRESI m -> u8ro a0segs m nin pl.
Proof.
  intros m PR. apply (bytes_at_agree a0segs mi m nin _ PLM0). intros a Ha. cbv beta in Ha.
  destruct pl as [|b0 pl'] eqn:EPL; [cbn [length] in Ha; exfalso; clear - Ha; lia|]. rewrite <- EPL in *.
  assert (NE : pl <> []) by (rewrite EPL; discriminate).
  destruct (PAYL NE) as (PIN & PL0 & PL1). pose proof (PAY NE) as PK. unfold pay_okB, apart, ESTATE_SIZE, FTAB_WORDS in PK. change (4 * 65537) with 262148 in PK.
  destruct PK as (_ & _ & _ & K1 & K2 & K3 & K4 & K5). pose proof (PSS NE) as K6. unfold CmpFsKit0.apartv in K6.
  apply PR. split.
  - right; right; left. exists pP, nP. split; [exact PIN| clear - Ha PL0 PL1; lia].
  - cbn [outside]. clear - Ha K1 K2 K3 K4 K5 K6. repeat split; lia.
Qed.

Lemma hc_lib : forall (m : mem), PRESI m -> L_libA.LIB_A m.
Proof.
  intros m PR. apply (L_libA.LIB_locA mi m LIB0). intros a (lo' & hi' & HIn & Hx). refine (PR a _).
  assert (R : 0xc4000 <= bv_unsigned a < 0xc4400 \/ 0xc4500 <= bv_unsigned a < 0xc4d00).
  { unfold D_libiface.LIB_FP in HIn. cbn [In] in HIn. destruct HIn as [HI|[HI|[]]]; injection HI as <- <-; [left| right]; exact Hx. }
  clear HIn Hx. split.
  - right; left. split.
    + exists 0xc3fe0, 0xc5ad8. split; [unfold CLIENT_STATIC; cbn [In]; left; reflexivity| clear - R; lia].
    + intros (l2 & h2 & HIn2 & Hx2). unfold RT_STATIC in HIn2. cbn [In] in HIn2.
      repeat (destruct HIn2 as [HI|HIn2]; [injection HI as <- <-; clear - R Hx2; lia|]). exact HIn2.
  - pose proof CX as CX'. unfold cctx_ok in CX'. cbv zeta in CX'. destruct CX' as (_ & _ & RA1 & _ & _ & _ & RFT & _).
    pose proof hc_shsep_ok as HS. unfold hc_shsep in HS. destruct HS as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & A2I & A1I & FTI).
    pose proof OOK as OOK'. unfold out_okB, img_apart, IMG_LO3 in OOK'. cbn [ci_hi aci_c A0C] in OOK'. destruct OOK' as (_ & _ & _ & _ & _ & _ & _ & _ & IO).
    cbn [outside]. clear - R EIMG SLO A1I FTI A2I IO. repeat split; lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma crc_bytes_eq : L_libA.CRC_BYTES = BzTables.bz_crc_table_bytes. Proof. vm_compute. reflexivity. Qed.

Lemma hc_views : forall Σ (m : mem) W, SOK Σ -> ART RT Σ m -> PRESI m -> app_fp W ->
  disjoint_from W (aci_got_sh A0C) 8 -> disjoint_from W (aci_shvar A0C) 8 ->
  disjoint_from W 788152 8 -> disjoint_from W 788176 8 -> disjoint_from W 784720 8 -> disjoint_from W 802816 1024 ->
  (pl <> [] -> disjoint_from W nin (Z.of_nat (length pl))) ->
  acoW W m /\ acimgW W m sv /\ cctx_sh a0segs cx W m /\ cimg_sh A0C W m /\ shzW a0segs W m STRM (STRM + 80) /\
  shpW a0segs W m nin (nin + Z.of_nat (length pl)) /\ shpW a0segs W m ob (ob + on) /\ u8roW W m nin pl.
Proof.
  intros Σ m W SK ART0 PR AFW D1 D2 D3 D4 D5 D6 DP. pose proof SK as (_ & SP0E & LIVS).
  pose proof (LIVS _ LIVE) as LVE. pose proof (LIVS _ LIV1) as LV1. pose proof (LIVS _ LIV2) as LV2. pose proof (LIVS _ LIVF) as LVF. pose proof (LIVS _ LIVO) as LVO.
  pose proof G as [_ _ _ _ _ _ _ _ _ _ _ GSP0 _ _]. unfold USTACK_TOP, STACK_WIN, SEGTOP_A in GSP0.
  pose proof CX as CX'. unfold cctx_ok in CX'. cbv zeta in CX'. destruct CX' as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & ME16 & MA16 & MA26 & MFT & _).
  split; [| split; [| split; [| split; [| split; [| split; [| split]]]]]].
  - destruct (af_client_consts RT AF Σ m ART0) as (G1 & G2 & _ & _).
    apply acoW_intro; [split; [exact (ro_C8_KN m _ _ G1)| exact (ro_C8_KN m _ _ G2)]| exact D1| exact D2].
  - apply acimgW_intro; [| exact D3| exact D4| exact D5| exact D6].
    destruct (AF_DRV Σ m ART0) as ((GS1 & GS2) & _). destruct (af_got_lib RT AF Σ m ART0) as (GL1 & _).
    pose proof (hc_lib m PR) as (LIBC & _).
    unfold acimg_mem. cbn [aci_segs aci_c A0C ci_segs ci_got ci_stderrp ci_crc ci_crcx].
    split; [exact (ro_C8_KN m _ _ GS1)|]. split; [exact (ro_C8_KN m _ _ GL1)|]. split; [exact (ro_C8_KN m _ _ GS2)|].
    destruct LIBC as [[_ LB] LW]. cbn [KCells.cells_bytes KCells.cbytes KCells.cells_size KCells.csize Nat.add app] in LB, LW. rewrite app_nil_r in LB.
    pose proof (n_rw_CB_of_bytes m L_libA.CRC_A L_libA.CRC_BYTES LB ltac:(rewrite L_libA.CRC_BYTES_length; exact LW)) as CR.
    rewrite L_libA.CRC_BYTES_length, crc_bytes_eq in CR. exact CR.
  - destruct (af_acc_live RT AF Σ m E 55768 ART0 LVE) as [_ ACCE]. destruct (af_acc_live RT AF Σ m A1 ARR1_SIZE ART0 LV1) as [_ ACC1].
    destruct (af_acc_live RT AF Σ m A2 ARR2_SIZE ART0 LV2) as [_ ACC2]. destruct (af_acc_live RT AF Σ m FT 262148 ART0 LVF) as [_ ACCF].
    pose proof (af_live_range RT AF Σ m E 55768 ART0 LVE) as (EL0 & EL1 & _). pose proof (af_live_range RT AF Σ m A1 ARR1_SIZE ART0 LV1) as (A1L0 & A1L1 & _).
    pose proof (af_live_range RT AF Σ m A2 ARR2_SIZE ART0 LV2) as (A2L0 & A2L1 & _). pose proof (af_live_range RT AF Σ m FT 262148 ART0 LVF) as (FTL0 & FTL1 & _).
    rewrite SP0E in EL1, A1L1, A2L1, FTL1. unfold STACK_WIN in EL1, A1L1, A2L1, FTL1.
    unfold cctx_sh, ESTATE_SIZE.
    split; [apply (shzW_of_acc a0segs W m E 55768 E (E + 55768) ACCE AFW); [clear - EL0; lia| clear - EL1 GSP0; lia| clear; lia| clear - ME16; Z.div_mod_to_equations; lia]|].
    split; [apply (shzW_of_acc a0segs W m A1 ARR1_SIZE A1 (A1 + ARR1_SIZE) ACC1 AFW); [clear - A1L0; lia| clear - A1L1 GSP0; lia| clear; lia| clear - MA16; Z.div_mod_to_equations; lia]|].
    split; [apply (shzW_of_acc a0segs W m A2 ARR2_SIZE A2 (A2 + ARR2_SIZE) ACC2 AFW); [clear - A2L0; lia| clear - A2L1 GSP0; lia| clear; lia| clear - MA26; Z.div_mod_to_equations; lia]|].
    split; [apply (shzW_of_acc a0segs W m FT 262148 FT (FT + 262144) ACCF AFW); [clear - FTL0; lia| clear - FTL1 GSP0; lia| clear; lia| clear - MFT; Z.div_mod_to_equations; lia]|].
    apply (shpW_of_acc a0segs W m FT 262148 ACCF AFW); [clear - FTL0; lia| clear - FTL1 GSP0; lia].
  - unfold cimg_sh. cbn [aci_segs aci_c A0C ci_segs ci_crc].
    apply (shzW_of_acc a0segs W m 0xc4000 1024 0xc4000 (0xc4000 + 1024) (AF_CRC Σ m ART0) AFW); [clear; lia| clear; lia| clear; lia| reflexivity].
  - destruct AS as [AS1 AS2]. pose proof (hc_strm_sh m PR) as SSHm. rewrite <- (Z.add_0_r SHS) in SSHm.
    pose proof (acc_of_zero_shadow a0segs m STRM SHS 0 10 AS1 AS2 ltac:(clear - SLO; lia) ltac:(clear; lia) SSHm) as ACCS.
    replace (STRM + 8 * 0) with STRM in ACCS by (clear; lia). change (8 * Z.of_nat 10) with 80 in ACCS.
    pose proof alloc_ceiling_range as ACR. unfold CmpFsKit0.CEILv in SHI.
    apply (shzW_of_acc a0segs W m STRM 80 STRM (STRM + 80) ACCS AFW); [clear - SLO; lia| clear - SHI ACR; lia| clear; lia| clear - AS1; Z.div_mod_to_equations; lia].
  - destruct pl as [|b0 pl'] eqn:EPL.
    { intros m' x s MU H1 H2 H3. exfalso. cbn [length] in H2. clear - H1 H2 H3. lia. }
    rewrite <- EPL in *. assert (NE : pl <> []) by (rewrite EPL; discriminate).
    destruct (PAYL NE) as (PIN & PL0 & PL1). pose proof (LIVS _ PIN) as LVP.
    destruct (af_acc_live RT AF Σ m pP nP ART0 LVP) as [_ ACCP].
    pose proof (af_live_range RT AF Σ m pP nP ART0 LVP) as (PPL0 & PPL1 & _). rewrite SP0E in PPL1. unfold STACK_WIN in PPL1.
    pose proof (acc_sub a0segs m pP nP nin (Z.of_nat (length pl)) ACCP PL0 PL1) as ACCN.
    apply (shpW_of_acc a0segs W m nin (Z.of_nat (length pl)) ACCN AFW); [clear - PPL0 PL0; lia| clear - PPL1 PL1 GSP0; lia].
  - destruct (af_acc_live RT AF Σ m ob on ART0 LVO) as [_ ACCO].
    pose proof (af_live_range RT AF Σ m ob on ART0 LVO) as (OL0 & OL1 & _). rewrite SP0E in OL1. unfold STACK_WIN in OL1.
    apply (shpW_of_acc a0segs W m ob on ACCO AFW); [clear - OL0; lia| clear - OL1 GSP0; lia].
  - pose proof (hc_pay m PR) as PM. destruct (Nat.eq_dec (length pl) 0) as [L0|LN].
    { intros m' MU. apply (bytes_at_agree a0segs m m' nin pl PM). intros a Ha. cbv beta in Ha. exfalso. rewrite L0 in Ha. clear - Ha. lia. }
    assert (NE : pl <> []) by (intros EN; apply LN; rewrite EN; reflexivity).
    apply (u8roW_intro W m nin pl PM (DP NE)).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac offs_open :=
  pose proof OFFE as OFFE'; pose proof OFF2 as OFF2'; pose proof OFFO as OFFO'; pose proof OFFS as OFFS'; unfold id in OFFE', OFF2', OFFO', OFFS';
  pose proof OOK as OOK'; unfold out_okB, img_apart, IMG_LO3 in OOK'; cbn [ci_hi aci_c A0C] in OOK'; destruct OOK' as (_ & _ & OCE & _ & _ & _ & _ & _ & IO');
  unfold CEIL in OCE.
Ltac hc_appfp :=
  let XL7 := ident:(XL7) in let OFFE' := ident:(OFFE') in let OFF2' := ident:(OFF2') in let OFFO' := ident:(OFFO') in let OFFS' := ident:(OFFS') in
  cbn [app_fp]; unfold SH_LO, SH_HI;
  repeat (split; [first [ right; clear - XL7; lia | clear - OFFE'; lia | clear - OFF2'; lia | clear - OFFO'; lia | clear - OFFS'; lia ]|]); exact I.
Ltac hc_imgapart :=
  let XL7 := ident:(XL7) in let XL15 := ident:(XL15) in let IO' := ident:(IO') in
  cbn [disjoint_from aci_got_sh aci_shvar A0C]; repeat (split; [clear - EIMG SLO XL7 XL15 IO'; lia|]); exact I.
Ltac hc_paydisj :=
  let XL14 := ident:(XL14) in let GLOW := ident:(GLOW) in let ACR := ident:(ACR) in
  let NE := fresh "NE" in intros NE; let PK := fresh "PK" in pose proof (PAY NE) as PK; unfold pay_okB, apart, ESTATE_SIZE, FTAB_WORDS, CEIL in PK; change (4 * 65537) with 262148 in PK;
  let K6 := fresh "K6" in pose proof (PSS NE) as K6; unfold CmpFsKit0.apartv in K6;
  let ACE' := fresh "ACE'" in pose proof ACE as ACE'; unfold STACK_WIN in ACE';
  cbn [disjoint_from]; repeat (split; [clear - PK K6 XL14 GLOW ACE'; lia|]); exact I.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma hc_obm_len : forall g e z, HCXB cx on g e z -> Z.of_nat (length (outb (z_outr z) OB)) = on.
Proof.
  intros g e z HX. pose proof (hlB_hci _ _ LAWS _ _ _ _ _ HX) as HI. pose proof (HCIB_avail_out _ _ _ _ _ HI) as (AOR & OLEN).
  apply (outb_length (z_outr z) OB on LOB). clear - AOR OLEN. lia.
Qed.
(* [comment removed for export] *)
Ltac obm_l1 OBM LOBn m m' MU WM :=
  lazymatch type of MU with munch ?W _ _ => apply (u8arr_transport a0segs W m m' ob _) in OBM; [| exact MU| exact WM| rewrite LOBn; x_disj] end.
Ltac obm_rtf G SK OBM LOBn STEP m m' :=
  apply (x_u8arr _ _ _ _ m m' STEP ob _) in OBM; [| rewrite LOBn; x_cls G SK| rewrite LOBn; x_disj].

Notation INR ra a0 a1 a2 a3 a4 a5 s2 s6 t4 t5 t6 :=
  (mkR ra cP gp tp (Z_to_bv 64 (E + 16)) (Z_to_bv 64 (E + 8)) (Z_to_bv 64 2) (Z_to_bv 64 E) cSB
       a0 a1 a2 a3 a4 a5 (Z_to_bv 64 1) (Z_to_bv 64 (E + 108))
       s2 (Z_to_bv 64 (E + 120)) (Z_to_bv 64 (SHE + 15)) (Z_to_bv 64 (E + 92)) s6 (Z_to_bv 64 (E + 116)) (Z_to_bv 64 (E + 96)) (Z_to_bv 64 SHE) (Z_to_bv 64 (E + 80))
       (Z_to_bv 64 (SHE + 14)) (Z_to_bv 64 (E + 648)) t4 t5 t6).
Notation TOPR ra a0 a1 a4 a5 s2 s6 t4 t5 t6 := (INR ra a0 a1 (Z_to_bv 64 (E + 12)) (Z_to_bv 64 (SHE + 1)) a4 a5 s2 s6 t4 t5 t6).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma hc_l2_in : forall (Σ1 : rts RT) g e z (pin pout : bool) (m : mem) (v0 v8 v16 v24 v32 v40 v48 v64 v72 v80 v88 v96 v112 : word)
    (c11 c10 c9 c8 c7 c6 c5 c4 c3 c2 c1 c0 cra : word) (ra a0 a1 a2 a3 a4 a5 s6 t4 t5 t6 : word) F fc T c,
  e_state e = BZ_S_INPUT -> HPURE HCXB cx on z0 pl g e z -> SOK Σ1 -> 28 <= rt_credit RT Σ1 ->
  emem cx a0segs g e m -> CmpCut.amem cx a0segs e m ->
  rw_cells a0segs m STRM (STRMB cx ob on dbza dbzfr z (nin + hkin z0 z) p1 p2) -> u8arr a0segs m ob (outb (z_outr z) OB) ->
  rw_cells a0segs m P (hc_slots E SHE v0 v8 v16 v24 v32 v40 v48 v64 v72 v80 v88 v96 (Z_to_bv 64 (Z.b2z pin)) v112) ->
  rw_cells a0segs m (P + 200) (HSAVED c11 c10 c9 c8 c7 c6 c5 c4 c3 c2 c1 c0 cra) ->
  ART RT Σ1 m -> KMem.mem_inv asegs m -> stk asegs m lo P -> PRESI m ->
  ASTA RT Σ1 PMc (eq (MS (INR ra a0 a1 a2 a3 a4 a5 (Z_to_bv 64 (Z.b2z pout)) s6 t4 t5 t6) F (Z_to_bv 64 0x82d64) fc None m (seg_rom a0segs))) c ->
  (forall c' (Σ2 : rts RT) (m' : mem) (e_cb : est) (il : bool) z1 (pin1 : bool) (w0 w8 w16 w24 w32 w40 w48 w64 w72 w80 w88 w96 w112 : word)
          (ra' a1' a4' a5' s6' t4' t5' t6' : word) F' fc',
     hc_in znew e z pin pout = (hc_after_cb e_cb il, z1, pin1, pout, false) ->
     HPURE HCXB cx on z0 pl (eg_after_cb cx g e_cb) (hc_after_cb e_cb il) z1 ->
     SOK Σ2 -> rt_live RT Σ2 = rt_live RT Σ1 -> rt_frames RT Σ2 = rt_frames RT Σ1 -> rt_credit RT Σ1 - 28 <= rt_credit RT Σ2 <= rt_credit RT Σ1 - 1 ->
     emem cx a0segs (eg_after_cb cx g e_cb) (hc_after_cb e_cb il) m' -> CmpCut.amem cx a0segs (hc_after_cb e_cb il) m' ->
     rw_cells a0segs m' STRM (STRMB cx ob on dbza dbzfr z1 (nin + hkin z0 z1) p1 p2) -> u8arr a0segs m' ob (outb (z_outr z1) OB) -> z_outr z1 = z_outr z ->
     rw_cells a0segs m' P (hc_slots E SHE w0 w8 w16 w24 w32 w40 w48 w64 w72 w80 w88 w96 (Z_to_bv 64 (Z.b2z pin1)) w112) ->
     rw_cells a0segs m' (P + 200) (HSAVED c11 c10 c9 c8 c7 c6 c5 c4 c3 c2 c1 c0 cra) ->
     ART RT Σ2 m' -> KMem.mem_inv asegs m' -> stk asegs m' lo P -> PRESI m' ->
     ASTA RT Σ2 PMc (eq (MS (TOPR ra' (Z_to_bv 64 0) a1' a4' a5' (Z_to_bv 64 (Z.b2z pout)) s6' t4' t5' t6') F' (Z_to_bv 64 0x829ec) fc' None m' (seg_rom a0segs))) c' ->
     realizes asegs c' T) ->
  realizes asegs c T.
Proof.
  intros Σ1 g e z pin pout m v0 v8 v16 v24 v32 v40 v48 v64 v72 v80 v88 v96 v112 c11 c10 c9 c8 c7 c6 c5 c4 c3 c2 c1 c0 cra ra a0 a1 a2 a3 a4 a5 s6 t4 t5 t6 F fc T c
    STI PU SK CRED EM AM SM OBM SL SAVED ART0 MI0 ST0 PR0 Hc Hk.
  act_open. offs_open. bz_params.
  pose proof SK as (FRM & SP0E & LIVS). pose proof (LIVS _ LIVE) as LVE. pose proof (LIVS _ LIV1) as LV1. pose proof (LIVS _ LIV2) as LV2. pose proof (LIVS _ LIVF) as LVF.
  destruct EM as (EH1 & INU & UNS & EH2 & MTF & SEL & SELM & LEN & CODE & RFQ & LPK). destruct AM as (AR1 & AR2 & FTB). unfold FTAB_WORDS in FTB.
  assert (CEP : CmpFsKit0.CEILv <= lo) by (unfold CmpFsKit0.CEILv; rewrite ACE; unfold STACK_WIN; exact GLOW).
  pose proof (hc_obm_len g e z (proj1 PU)) as LOBn.
  (* [comment removed for export] *)
  destruct (hc_views Σ1 m (A0_b2c_hcC.ci_W cx P STRM) SK ART0 PR0 ltac:(unfold A0_b2c_hcC.ci_W; hc_appfp) ltac:(unfold A0_b2c_hcC.ci_W; hc_imgapart) ltac:(unfold A0_b2c_hcC.ci_W; hc_imgapart)
              ltac:(unfold A0_b2c_hcC.ci_W; hc_imgapart) ltac:(unfold A0_b2c_hcC.ci_W; hc_imgapart) ltac:(unfold A0_b2c_hcC.ci_W; hc_imgapart) ltac:(unfold A0_b2c_hcC.ci_W; hc_imgapart)
              ltac:(unfold A0_b2c_hcC.ci_W; hc_paydisj)) as (VAC & VCM & CSH & ISH & SHs & SHp & _ & VPL).
  eapply (l1_realizes RT AF Σ1 PMc _ T c MST Hc).
  eapply (A0_hc_in cx _ HCXB CBFACTS SHE ob on dbza dbzfr p1 p2 sv P STRM lo z0 nin pl gp tp F fc eq_refl CX SEP IMG LAWS AE SLO SHI CEP
            ltac:(clear - XL14; lia) ltac:(clear - XL13; lia) SES S2S
            ltac:(intros NE; pose proof (PAY NE) as PK; unfold pay_okB, CEIL in PK; unfold CmpFsKit0.CEILv; clear - PK; lia) g e z pin pout m);
    [exact STI| exact PU| exact EH1| exact EH2| exact INU| exact AR2| exact SM| exact SL| exact ST0| exact (kmem_inv_N _ _ MI0)| exact VPL| exact VCM| exact VAC| exact CSH| exact ISH| exact SHs| exact SHp|].
  clear Hc EH1 EH2 INU AR2 SM SL ST0 VPL VCM VAC CSH ISH SHs SHp.
  intros e_cb il z1 pin1 m1 w8 w16 w24 w64 w72 w80 w88 t0_1 t1_1 t2_1 a2_1 a3_1 a4_1 a5_1 a6_1 a7_1 s6_1 t3_1 t4_1 t5_1 t6_1 HIN PRE FACTS REST PU1 EH1 EH2 INU AR2 SM SL ST1n NMI1 MU1 WM1.
  apply evt_done. intros k1 Hc1. unfold A0_b2c_hcC.ci_W in MU1.
  lazymatch type of MU1 with munch ?W _ _ =>
    destruct (after_l1_leaf AF G Σ1 W 16 m m1 SK ART0 MI0 PR0 NMI1 MU1 WM1 ltac:(clear; lia) ltac:(clear - ROOM; unfold RT_STACK in *; lia) ltac:(fp_ours)) as (ART1 & MI1 & PR1 & STEP1) end.
  obm_l1 OBM LOBn m m1 MU1 WM1. xfer_l1 m m1 MU1 WM1. clear NMI1 MU1 WM1 STEP1.
  assert (ST1 : stk asegs m1 lo P) by exact ST1n. clear ST1n.
  (* [comment removed for export] *)
  destruct REST as (R1 & R2 & R3 & R4 & R5 & R6 & R7 & R8 & R9 & R10).
  rewrite <- R1 in UNS. rewrite <- R2 in MTF. rewrite <- R3 in SEL. rewrite <- R4 in SELM. rewrite <- R5 in LEN. rewrite <- R6 in CODE. rewrite <- R7 in RFQ. rewrite <- R8 in LPK.
  rewrite <- R9 in AR1. rewrite <- R10 in FTB.
  assert (EM1 : emem cx a0segs g e_cb m1).
  { unfold emem. split; [exact EH1|]. split; [exact INU|]. split; [exact UNS|]. split; [exact EH2|]. split; [exact MTF|]. split; [exact SEL|]. split; [exact SELM|].
    split; [exact LEN|]. split; [exact CODE|]. split; [exact RFQ| exact LPK]. }
  assert (AM1 : CmpCut.amem cx a0segs e_cb m1) by (unfold CmpCut.amem, FTAB_WORDS; split; [exact AR1| split; [exact AR2| exact FTB]]).
  (* [comment removed for export] *)
  destruct (compressBlock e_cb il znew) as [e' yy] eqn:CBE.
  assert (HAC : hc_after_cb e_cb il = est_set_modes e' (e_mode e') BZ_S_OUTPUT (e_avail_in_expect e')) by (unfold hc_after_cb; rewrite CBE; reflexivity).
  refine (cps_realizes asegs _ _ T k1 (CBC Σ1 PMc _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m1 cx g e_cb il lo FDO MST eq_refl eq_refl TP
            ltac:(rewrite SP0E; exact ACE) EM1 AM1 LVE LV1 LV2 LVF ltac:(rewrite FRM; cbn [length app]; clear - FRB; unfold FRAMES_MAX in *; lia) CRED ART1 MI1
            ltac:(rewrite (P_unsigned G); exact ST1) ltac:(rewrite SP0E; exact GLOW) ltac:(rewrite (P_unsigned G); exact ROOM)
            ltac:(rewrite (P_unsigned G); unfold USTACK_TOP; clear - GSPT GPUS; lia) ltac:(rewrite (P_unsigned G); exact GSPA) CX SEP IMG PRE FACTS) Hc1 _).
  clear Hc1. intros k2 (Σb & Hq & LVb & FRb & SPb & CRb).
  destruct (ASTA_unpack RT Σb _ _ k2 Hq) as (msb & (m2 & q0 & q1 & q2 & h0 & h1 & h2 & h3 & h4 & h5 & h6 & h7 & q3 & q4 & q5 & q6 & Fb & fcb & -> & ARTb & MIb & STb & POSTb & STEPb) & Hc2).
  clear Hq. cbv zeta in POSTb. rewrite CBE in POSTb. cbn [fst] in POSTb. destruct POSTb as (EMb & AMb).
  rewrite (P_unsigned G) in STb, STEPb. unfold ESTATE_SIZE, FTAB_WORDS in STEPb. change (4 * 65537) with 262148 in STEPb.
  rewrite (ret_pc_even 0x8373c ltac:(lia) eq_refl) in Hc2.
  destruct (after_call G Σ1 Σb _ m1 m2 SK LVb FRb SPb PR1 STEPb ltac:(per_interval; right; cbn [outside]; lia)) as (SKb & PRb).
  clear EH1 EH2 INU UNS MTF SEL SELM LEN CODE RFQ LPK AR1 AR2 FTB EM1 AM1.
  obm_rtf G SK OBM LOBn STEPb m1 m2. xfer_rtf G SK STEPb m1 m2. clear STEPb.
  destruct EMb as (EH1 & INU & UNS & EH2 & MTF & SEL & SELM & LEN & CODE & RFQ & LPK). destruct AMb as (AR1 & AR2 & FTB). unfold FTAB_WORDS in FTB.
  (* [comment removed for export] *)
  destruct (hc_views Σb m2 (hcr_W cx) SKb ARTb PRb ltac:(unfold hcr_W; hc_appfp) ltac:(unfold hcr_W; hc_imgapart) ltac:(unfold hcr_W; hc_imgapart)
              ltac:(unfold hcr_W; hc_imgapart) ltac:(unfold hcr_W; hc_imgapart) ltac:(unfold hcr_W; hc_imgapart) ltac:(unfold hcr_W; hc_imgapart)
              ltac:(unfold hcr_W; hc_paydisj)) as (_ & _ & (SHe & _) & _).
  eapply (l1_realizes RT AF Σb PMc _ T k2 MST Hc2).
  eapply (A0_hc_cbret cx _ SHE P lo gp tp Fb fcb CX AE CEP ltac:(clear - XL14; lia) (eg_after_cb cx g e_cb) e' m2); [exact EH1| exact SL| exact (kmem_inv_N _ _ MIb)| exact SHe|].
  clear Hc2 EH1 SL SHe. intros m3 EH1 SL NMI3 MU3 WM3. apply evt_done. intros k3 Hc3. unfold hcr_W in MU3.
  lazymatch type of MU3 with munch ?W _ _ => destruct (after_l1 AF G Σb W m2 m3 SKb ARTb MIb STb PRb NMI3 MU3 WM3 ltac:(fp_ours)) as (ART3 & MI3 & ST3 & PR3 & _) end.
  obm_l1 OBM LOBn m2 m3 MU3 WM3. xfer_l1 m2 m3 MU3 WM3. clear NMI3 MU3 WM3.
  rewrite <- HAC in EH1.
  eapply (Hk k3 Σb m3 e_cb il z1 pin1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Fb fcb HIN PU1 SKb LVb FRb CRb); [| | exact SM| | | exact SL| exact SAVED| exact ART3| exact MI3| exact ST3| exact PR3| exact Hc3].
  - rewrite HAC. unfold emem. split; [rewrite <- HAC; exact EH1|]. split; [exact INU|]. split; [exact UNS|]. split; [exact EH2|]. split; [exact MTF|]. split; [exact SEL|]. split; [exact SELM|].
    split; [exact LEN|]. split; [exact CODE|]. split; [exact RFQ| exact LPK].
  - rewrite HAC. unfold CmpCut.amem. split; [exact AR1|]. split; [exact AR2| exact FTB].
  - rewrite (proj1 (hc_in_outr _ _ _ _ _ _ _ _ _ _ HIN)). exact OBM.
  - exact (proj1 (hc_in_outr _ _ _ _ _ _ _ _ _ _ HIN)).
Qed.

End HCG.
