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
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A Require L_libA D_libiface.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.L2B Require Import L2Kit L2Act L2Stmt B0_fs_L2f B0_sessK.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require Import PropExec.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import Tac WalkLib SegsA0 SegsB0.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzTac BzArr BzCMem BzCStream BzCState BzCMtf BzCBlock BzCHuff BzArrD BzCLemmas1 CmpMem CmpCut CmpCutMS CmpCutMtf CmpCutSM CmpCutSmA BzCFactsSmA CmpCutSmB BzCFactsGm BzCSmF1 BzCFactsSmB BzCFactsSd CmpHmKit CmpSmKit CmpSmKit2 AsanKit AsanKit2 AsanCut AsanCutB0.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzCNumZ CmpLaws CmpCutCB BzCFactsSmA2 BzCFactsSmB3 BzCFactsSd2 BzCLemmasMs6 BzCFactsBs6 BzCFactsCb BzCSortPost.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzCDriver CmpSess CmpSessB.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzCHuffF1 BzTables.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCHuffF1.BzCFactsHm.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import CmpCut6.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import A0_cmp_fsV B0_cmp_msV B0_b2c_cbV B0_b2c_hcV A0_b2c_hcR B0_b2c_hcC B0_b2c_hcD B0_b2c_hcE B0_b2c_hcG.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.L2B Require Import B0_hc_L2a.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeil.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzParams.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Open Scope Z_scope.
#[local] Notation mem := (word -> option byte).

Section HCG.
Context {BZP : BzParams} {ACEIL__ : ACeil}.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Variables (HCXB : cctx -> Z -> eg -> est -> zstrm -> Prop) (CBFACTS : est -> Prop).
Hypothesis CBC : compressBlock_contract RT CBFACTS.
Hypothesis AF_DRV : forall Σ m, ART RT Σ m -> drv_consts m.
(* [comment removed for export] *)
Hypothesis AF_CRC : forall Σ m, ART RT Σ m -> acc bsegs m 0xd13e0 1024.
(* [comment removed for export] *)
Variables (cx : cctx) (ob on dbza dbzfr : Z) (z0 : zstrm) (nin : Z) (pl OB : list byte) (p1 p2 : word) (lo : Z) (sp gp tp : word).
Hypothesis CX : cctx_ok cx. Hypothesis SEP : cctx_sep cx. Hypothesis IMG : cctx_img (aci_c B0C) cx. Hypothesis LAWS : hc_lawsB HCXB CBFACTS.
Hypothesis TP : tp = Z_to_bv 64 0x6094d8.
Hypothesis LOB : Z.of_nat (length OB) = on. Hypothesis OOK : out_okB (aci_c B0C) cx ob on. Hypothesis PAY : pay_condB cx ob on nin pl.
Notation usp := (bv_unsigned sp). Notation P := (usp - 288).
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
Hypothesis ROOM : lo + RT_STACK + 304 + 2064 <= P.
Hypothesis FRB : (length fr + 3 < FRAMES_MAX)%nat.
Hypothesis LIVE : In (E, 55768) live0. Hypothesis LIV1 : In (A1, ARR1_SIZE) live0. Hypothesis LIV2 : In (A2, ARR2_SIZE) live0. Hypothesis LIVF : In (FT, 262148) live0.
Hypothesis LIVO : In (ob, on) live0.
(* [comment removed for export] *)
Variables (fS : Z) (kS : nat).
Hypothesis INS : In (fS, kS) fr. Hypothesis SFL : fS <= STRM. Hypothesis SFH : STRM + 80 <= fS + fs_size kS - 8.
Variables (pP nP : Z).
Hypothesis PAYL : pl <> [] -> In (pP, nP) live0 /\ pP <= nin /\ nin + Z.of_nat (length pl) <= pP + nP.
(* [comment removed for export] *)
Hypothesis EIMG : 0x62b000 <= E. Hypothesis SLO : 0x62b000 <= STRM. Hypothesis SHI : STRM + 80 <= CmpFsKit0.CEILv.
Hypothesis SES : CmpFsKit0.apartv E ESTATE_SIZE STRM 80. Hypothesis S1S : CmpFsKit0.apartv A1 ARR1_SIZE STRM 80. Hypothesis S2S : CmpFsKit0.apartv A2 ARR2_SIZE STRM 80.
Hypothesis SFS : CmpFsKit0.apartv FT 262148 STRM 80. Hypothesis SOS : CmpFsKit0.apartv ob on STRM 80.
Hypothesis PSS : pl <> [] -> CmpFsKit0.apartv nin (Z.of_nat (length pl)) STRM 80.
Hypothesis OFFE : E + 55768 <= 0x7fff7000 \/ 0x10007fff8000 <= E. Hypothesis OFF1 : A1 + ARR1_SIZE <= 0x7fff7000 \/ 0x10007fff8000 <= A1.
Hypothesis OFF2 : A2 + ARR2_SIZE <= 0x7fff7000 \/ 0x10007fff8000 <= A2. Hypothesis OFFF : FT + 262148 <= 0x7fff7000 \/ 0x10007fff8000 <= FT.
Hypothesis OFFO : ob + on <= 0x7fff7000 \/ 0x10007fff8000 <= ob. Hypothesis OFFS : STRM + 80 <= 0x7fff7000 \/ 0x10007fff8000 <= STRM.
Hypothesis SHSR : 2147450880 <= SHS /\ SHS + 10 <= 17594333495296.
Variable mi : mem.   (* [comment removed for export] *)
Hypothesis SSH0 : bytes_at bsegs mi SHS (repeat z8 10). Hypothesis PLM0 : u8ro b0segs mi nin pl. Hypothesis LIB0 : OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.L_libA.TwinB__.LIB_A mi.
Notation PRESI := (PRESI usp fr live0 Whc mi).
Notation SOK Σ := (sig_ok RT sp0 false 0 8 fr live0 Σ).

(* [comment removed for export] *)
Ltac hc_keys :=
  pose proof (ck_intro usp CStack) as KU;
  pose proof (ck_intro E (CLive E 55768)) as KE; pose proof (ck_intro A1 (CLive A1 ARR1_SIZE)) as KA1; pose proof (ck_intro A2 (CLive A2 ARR2_SIZE)) as KA2;
  pose proof (ck_intro FT (CLive FT 262148)) as KFT; pose proof (ck_intro ob (CLive ob on)) as KOB; pose proof (ck_intro (c_bz cx) CCaller) as KST.
Ltac fp_ours := per_interval; cbn [outside]; lia.
(* [comment removed for export] *)

Lemma hc_shsep_ok_here : hc_shsep cx ob on lo sp.
Proof. eapply hc_shsep_ok; eassumption. Qed.
(* [comment removed for export] *)
Ltac shsep_open :=
  let H := fresh "SHS" in pose proof hc_shsep_ok_here as H; unfold hc_shsep in H;
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
Ltac offs_open :=
  pose proof OFFE as OFFE'; pose proof OFF2 as OFF2'; pose proof OFFO as OFFO'; pose proof OFFS as OFFS'; unfold id in OFFE', OFF2', OFFO', OFFS';
  pose proof OOK as OOK'; unfold out_okB, img_apart, IMG_LO3 in OOK'; cbn [ci_hi aci_c B0C] in OOK'; destruct OOK' as (_ & _ & OCE & _ & _ & _ & _ & _ & IO');
  unfold CEIL in OCE.
Ltac hc_appfp :=
  let XL7 := ident:(XL7) in let OFFE' := ident:(OFFE') in let OFF2' := ident:(OFF2') in let OFFO' := ident:(OFFO') in let OFFS' := ident:(OFFS') in
  cbn [app_fp]; unfold SH_LO, SH_HI;
  repeat (split; [first [ right; clear - XL7; lia | clear - OFFE'; lia | clear - OFF2'; lia | clear - OFFO'; lia | clear - OFFS'; lia ]|]); exact I.
Ltac hc_imgapart :=
  let XL7 := ident:(XL7) in let XL15 := ident:(XL15) in let IO' := ident:(IO') in
  cbn [disjoint_from aci_got_sh aci_shvar B0C]; repeat (split; [clear - EIMG SLO XL7 XL15 IO'; lia|]); exact I.
Ltac hc_paydisj :=
  let XL14 := ident:(XL14) in let GLOW := ident:(GLOW) in let ACR := ident:(ACR) in
  let NE := fresh "NE" in intros NE; let PK := fresh "PK" in pose proof (PAY NE) as PK; unfold pay_okB, apart, ESTATE_SIZE, FTAB_WORDS, CEIL in PK; change (4 * 65537) with 262148 in PK;
  let K6 := fresh "K6" in pose proof (PSS NE) as K6; unfold CmpFsKit0.apartv in K6;
  let ACE' := fresh "ACE'" in pose proof ACE as ACE'; unfold STACK_WIN in ACE';
  cbn [disjoint_from]; repeat (split; [clear - PK K6 XL14 GLOW ACE'; lia|]); exact I.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Notation CIR s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s7 t6 :=
  (mkR (Z_to_bv 64 (SHE + 14)) cP gp tp (Z_to_bv 64 (E + 92)) (Z_to_bv 64 (E + 96)) (Z_to_bv 64 (E + 108)) (Z_to_bv 64 E) s1 a0 a1 a2 a3 a4 a5 a6 a7
       s2 s3 (Z_to_bv 64 2) (Z_to_bv 64 (E + 120)) (Z_to_bv 64 1) s7 (Z_to_bv 64 (E + 116)) (Z_to_bv 64 SHE) (Z_to_bv 64 (E + 80)) cSB
       (Z_to_bv 64 (SHE + 13)) (Z_to_bv 64 (E + 16)) (Z_to_bv 64 (E + 112)) t6).
Notation TOPR s1 a0 a1 a4 a5 a6 a7 s2 s3 s7 t6 := (CIR s1 a0 a1 (Z_to_bv 64 (E + 12)) (Z_to_bv 64 (SHE + 1)) a4 a5 a6 a7 s2 s3 s7 t6).

(* [comment removed for export] *)
Local Notation hc_l2_inL := (hc_l2_in RT AF HCXB CBFACTS CBC AF_DRV AF_CRC cx ob on dbza dbzfr z0 nin pl OB p1 p2 lo sp gp tp CX SEP IMG LAWS TP LOB OOK PAY SHE SHS AE AS PMc fr live0 sp0 FDO MST G ACE ROOM FRB
                               LIVE LIV1 LIV2 LIVF LIVO fS kS INS SFL SFH pP nP PAYL EIMG SLO SHI SES S1S S2S SFS SOS PSS OFFE OFF1 OFF2 OFFF OFFO OFFS SHSR mi SSH0 PLM0 LIB0).
Local Notation hc_viewsL := (hc_views RT AF AF_DRV AF_CRC cx ob on nin pl lo sp CX SEP IMG OOK PAY SHS AS fr live0 sp0 G ACE ROOM LIVE LIV1 LIV2 LIVF LIVO fS kS INS SFL SFH pP nP PAYL EIMG SLO SHI
                               SES S1S S2S SFS SOS PSS OFFE OFF1 OFF2 OFFF OFFO OFFS SHSR mi SSH0 PLM0 LIB0).
Local Notation hc_obm_lenL := (hc_obm_len HCXB CBFACTS cx on OB LAWS LOB).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma hc_l2_top : forall (fuel : nat) (Σ1 : rts RT) g e z (pin pout : bool) (m : mem) (v64 v80 v88 : word)
    (c11 c10 c9 c8 c7 c6 c5 c4 c3 c2 c1 c0 cra : word) (s1 a0 a1 a4 a5 a6 a7 s2 s7 t6 : word) F fc T c (ef : est) (zf : zstrm) (prf : bool),
  hc_breaks fuel znew e z pin pout -> hc_loop fuel znew e z pin pout = (ef, zf, prf) ->
  HPURE HCXB cx on z0 pl g e z -> SOK Σ1 -> 28 * Z.of_nat fuel <= rt_credit RT Σ1 ->
  emem cx b0segs g e m -> CmpCut.amem cx b0segs e m ->
  rw_cells b0segs m STRM (STRMB cx ob on dbza dbzfr z (nin + hkin z0 z) p1 p2) -> u8arr b0segs m ob (outb (z_outr z) OB) ->
  rw_cells b0segs m P (hc_slots E SHE v64 (Z_to_bv 64 (Z.b2z pout)) v80 v88) ->
  rw_cells b0segs m (P + 184) (HSAVED c11 c10 c9 c8 c7 c6 c5 c4 c3 c2 c1 c0 cra) ->
  ART RT Σ1 m -> KMem.mem_inv bsegs m -> stk bsegs m lo P -> PRESI m ->
  ASTA RT Σ1 PMc (eq (MS (TOPR s1 a0 a1 a4 a5 a6 a7 s2 (Z_to_bv 64 (Z.b2z pin)) s7 t6) F (Z_to_bv 64 0x825d4) fc None m (seg_rom b0segs))) c ->
  (forall c' (Σ' : rts RT) (m' : mem) (g' : eg) (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) F' fc',
     ASTA RT Σ' PMc (eq (MS (mkR cra sp gp tp t0' t1' t2' c0 c1 (Z_to_bv 64 (Z.b2z prf)) a1' a2' a3' a4' a5' a6' a7' c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 t3' t4' t5' t6')
                            F' (ret_pc cra) fc' None m' (seg_rom b0segs))) c' ->
     rt_live RT Σ' = rt_live RT Σ1 -> rt_frames RT Σ' = rt_frames RT Σ1 -> rt_sp0 RT Σ' = sp0 ->
     rt_credit RT Σ1 - 28 * Z.of_nat fuel <= rt_credit RT Σ' <= rt_credit RT Σ1 ->
     HPURE HCXB cx on z0 pl g' ef zf ->
     emem cx b0segs g' ef m' -> CmpCut.amem cx b0segs ef m' ->
     rw_cells b0segs m' STRM (STRMB cx ob on dbza dbzfr zf (nin + hkin z0 zf) p1 p2) -> u8arr b0segs m' ob (outb (z_outr zf) OB) ->
     ART RT Σ' m' -> KMem.mem_inv bsegs m' -> stk bsegs m' lo usp -> PRESI m' ->
     realizes bsegs c' T) ->
  realizes bsegs c T.
Proof.
  induction fuel as [|fuel IH];
    intros Σ1 g e z pin pout m v64 v80 v88 c11 c10 c9 c8 c7 c6 c5 c4 c3 c2 c1 c0 cra s1 a0 a1 a4 a5 a6 a7 s2 s7 t6 F fc T c ef zf prf
      BRK RES PU SK CRED EM AM SM OBM SL SAVED ART0 MI0 ST0 PR0 Hc Hk; [destruct BRK|].
  rewrite hc_breaks_S in BRK. rewrite hc_loop_S in RES.
  act_open. offs_open. bz_params.
  pose proof SK as (FRM & SP0E & LIVS). pose proof (LIVS _ LIVE) as LVE.
  assert (CEP : CmpFsKit0.CEILv <= lo) by (unfold CmpFsKit0.CEILv; rewrite ACE; unfold STACK_WIN; exact GLOW).
  pose proof PU as (HX & ZI & KNN).
  pose proof (hlB_hci _ _ LAWS _ _ _ _ _ HX) as HI0. pose proof (HCIB_mode _ _ _ _ _ HI0) as (MD & _).
  pose proof (HCIB_est_ok _ _ _ _ _ HI0) as EOK. unfold est_ok in EOK. destruct EOK as (_ & _ & _ & _ & _ & _ & _ & STATES & _ & _ & _ & _ & BNO).
  pose proof (hc_obm_lenL g e z HX) as LOBn.
  destruct EM as (EH1 & INU & UNS & EH2 & MTF & SEL & SELM & LEN & CODE & RFQ & LPK). destruct AM as (AR1 & AR2 & FTB). unfold FTAB_WORDS in FTB.
  assert (CR28 : 28 <= rt_credit RT Σ1) by (clear - CRED; lia).
  destruct STATES as [STO|STI].
  - (* [comment removed for export] *)
    rewrite (hc_iter_output znew e z pin pout STO) in BRK, RES.
    destruct (hc_viewsL Σ1 m (hco_W cx ob on P STRM) SK ART0 PR0 ltac:(unfold hco_W; hc_appfp) ltac:(unfold hco_W; hc_imgapart) ltac:(unfold hco_W; hc_imgapart)
                ltac:(unfold hco_W; hc_imgapart) ltac:(unfold hco_W; hc_imgapart) ltac:(unfold hco_W; hc_imgapart) ltac:(unfold hco_W; hc_imgapart)
                ltac:(unfold hco_W; hc_paydisj)) as (VAC & _ & (SHe & _ & SH2 & _) & _ & SHs & _ & SHo & _).
    assert (VA2 : u8arrW (hco_W cx ob on P STRM) m A2 (zb8 (e_arr2 e) ARR2_SIZE)) by (apply (u8arrW_intro _ m A2 _ AR2); unfold hco_W; x_disj).
    eapply (l1_realizes RT AF Σ1 PMc _ T c MST Hc).
    eapply (B0_hc_out cx _ HCXB CBFACTS SHE SHS ob on dbza dbzfr p1 p2 OB P STRM lo gp tp F fc eq_refl CX SEP LAWS AE AS SLO SHI EIMG CEP ltac:(clear - XL14; lia) ltac:(clear - XL13; lia) OOK LOB SES SOS
              g e z pin pout (nin + hkin z0 z) m v64 v80 v88 s1 a0 a1 a4 a5 a6 a7 s2 s7 t6);
      [exact STO| exact HX| exact EH1| exact EH2| exact INU| exact SM| exact OBM| exact SL| exact ST0| exact VA2| exact (kmem_inv_N _ _ MI0)| exact VAC| exact SHe| exact SHs| exact SH2| exact SHo| |].
    + (* [comment removed for export] *)
      clear Hc EH1 EH2 INU SM OBM SL VA2 VAC SHe SHs SH2 SHo IH.
      intros e1 z1 pout1 m1 a0' a1' a2' a3' a4' a5' a6' s2' HO HX1 ZIN1 ZAI1 EA2 EH1 EH2 INU SM OBM SL ST1n NMI1 MU1 WM1. apply evt_done. intros k1 Hc1. unfold hco_W in MU1.
      lazymatch type of MU1 with munch ?W _ _ =>
        destruct (after_l1_leaf AF G Σ1 W 16 m m1 SK ART0 MI0 PR0 NMI1 MU1 WM1 ltac:(clear; lia) ltac:(clear - ROOM; unfold RT_STACK in *; lia) ltac:(fp_ours)) as (ART1 & MI1 & PR1 & _) end.
      xfer_l1 m m1 MU1 WM1. clear NMI1 MU1 WM1.
      assert (ST1 : stk bsegs m1 lo P) by exact ST1n. clear ST1n.
      rewrite HO in RES. cbn iota in RES. injection RES as <- <- <-.
      eapply (l1_realizes RT AF Σ1 PMc _ T k1 MST Hc1).
      eapply (B0_hc_ret cx _ SHE P lo gp tp F fc ltac:(clear - XL14; lia) pin pout1 m1 sp); [reflexivity| exact SL| exact SAVED| exact ST1|].
      intros STu. apply evt_done. clear Hc1. intros k2 Hc2.
      destruct (hc_out_rest _ _ _ _ _ _ _ HO) as (R1 & R2 & R3 & R4 & R5 & R6 & R7 & R8 & R9 & R10).
      pose proof (hc_out_ret_inuse _ _ _ _ _ _ MD HO) as RI.
      rewrite <- R1 in UNS. rewrite <- R2 in MTF. rewrite <- R3 in SEL. rewrite <- R4 in SELM. rewrite <- R5 in LEN. rewrite <- R6 in CODE. rewrite <- R7 in RFQ. rewrite <- R8 in LPK.
      rewrite <- R9 in AR1. rewrite <- R10 in FTB. rewrite <- EA2 in AR2.
      assert (HK1 : hkin z0 z1 = hkin z0 z) by (unfold hkin; rewrite ZAI1; reflexivity).
      eapply (Hk k2 Σ1 m1 g _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc Hc2 eq_refl eq_refl SP0E ltac:(clear - CRED; lia)); [| | | | exact OBM| exact ART1| exact MI1| exact STu| exact PR1].
      * unfold HPURE. rewrite HK1, ZIN1. split; [exact HX1| split; [exact ZI| exact KNN]].
      * unfold emem. split; [exact EH1|]. split; [exact INU|]. split; [exact UNS|]. split; [exact EH2|]. split; [exact MTF|]. split; [exact SEL|]. split; [exact SELM|].
        split; [exact LEN|]. split; [exact CODE|]. split; [exact RFQ| exact LPK].
      * unfold CmpCut.amem, FTAB_WORDS. split; [exact AR1|]. split; [exact AR2| exact FTB].
      * rewrite HK1. exact SM.
    + (* [comment removed for export] *)
      clear Hc EH1 EH2 INU SM OBM SL VA2 VAC SHe SHs SH2 SHo.
      intros e1 z1 pout1 m1 a1' a4' a5' a6' a7' s2' HO HX1 ZIN1 ZAI1 EA2 EH1 EH2 INU SM OBM SL ST1n NMI1 MU1 WM1. apply evt_done. intros k1 Hc1. unfold hco_W in MU1.
      lazymatch type of MU1 with munch ?W _ _ =>
        destruct (after_l1_leaf AF G Σ1 W 16 m m1 SK ART0 MI0 PR0 NMI1 MU1 WM1 ltac:(clear; lia) ltac:(clear - ROOM; unfold RT_STACK in *; lia) ltac:(fp_ours)) as (ART1 & MI1 & PR1 & _) end.
      xfer_l1 m m1 MU1 WM1. clear NMI1 MU1 WM1.
      assert (ST1 : stk bsegs m1 lo P) by exact ST1n. clear ST1n.
      rewrite HO in BRK, RES. cbn iota in BRK, RES.
      destruct (hc_out_ms_facts _ _ _ _ _ _ HO) as (EMD & EBN & REST).
      assert (HK1 : hkin z0 z1 = hkin z0 z) by (unfold hkin; rewrite ZAI1; reflexivity).
      (* [comment removed for export] *)
      destruct REST as (R1 & R2 & R3 & R4 & R5 & R6 & R7 & R8 & R9 & R10).
      rewrite <- R1 in UNS. rewrite <- R2 in MTF. rewrite <- R3 in SEL. rewrite <- R4 in SELM. rewrite <- R5 in LEN. rewrite <- R6 in CODE. rewrite <- R7 in RFQ. rewrite <- R8 in LPK.
      rewrite <- R9 in AR1. rewrite <- R10 in FTB.
      assert (EA2' : e_arr2 (hc_prep e1) = e_arr2 e) by (rewrite hc_prep_of_a; cbn [e_arr2]; exact EA2). rewrite <- EA2' in AR2.
      pose proof (hc_prep_rest e1) as PR'. destruct PR' as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9 & Q10).
      rewrite Q1 in UNS. rewrite Q2 in MTF. rewrite Q3 in SEL. rewrite Q4 in SELM. rewrite Q5 in LEN. rewrite Q6 in CODE. rewrite Q7 in RFQ. rewrite Q8 in LPK.
      rewrite Q9 in AR1. rewrite Q10 in FTB.
      eapply (hc_l2_inL Σ1 g (hc_prep e1) z1 pin pout1 m1 _ _ _ c11 c10 c9 c8 c7 c6 c5 c4 c3 c2 c1 c0 cra _ _ _ _ _ _ _ _ _ F fc T k1
                ltac:(rewrite hc_prep_of_a; reflexivity) ltac:(unfold HPURE; rewrite HK1, ZIN1; split; [exact HX1| split; [exact ZI| exact KNN]]) SK CR28);
        [| | rewrite HK1; exact SM| exact OBM| exact SL| exact SAVED| exact ART1| exact MI1| exact ST1| exact PR1| exact Hc1|].
      { unfold emem. split; [exact EH1|]. split; [exact INU|]. split; [exact UNS|]. split; [exact EH2|]. split; [exact MTF|]. split; [exact SEL|]. split; [exact SELM|].
        split; [exact LEN|]. split; [exact CODE|]. split; [exact RFQ| exact LPK]. }
      { unfold CmpCut.amem, FTAB_WORDS. split; [exact AR1|]. split; [exact AR2| exact FTB]. }
      clear Hc1 EH1 EH2 INU UNS MTF SEL SELM LEN CODE RFQ LPK AR1 AR2 FTB SM OBM SL SAVED.
      intros k4 Σ2 m4 e_cb il z2 pin2 s1_4 a0_4 a1_4 a4_4 a5_4 a6_4 a7_4 s2_4 s7_4 t6_4 F4 fc4 HIN PU2 SK2 LV2 FR2 CR2 EM2 AM2 SM2 OBM2 ZO2 SL2 SAVED2
        ART4 MI4 ST4 PR4 Hc4.
      rewrite HIN in BRK, RES. cbn iota in BRK, RES.
      eapply (IH Σ2 (eg_after_cb cx g e_cb) (hc_after_cb e_cb il) z2 pin2 pout1 m4 _ _ _ c11 c10 c9 c8 c7 c6 c5 c4 c3 c2 c1 c0 cra _ _ _ _ _ _ _ _ _ _ F4 fc4 T k4 ef zf prf
                BRK RES PU2 SK2 ltac:(clear - CRED CR2; lia) EM2 AM2 SM2 OBM2 SL2 SAVED2 ART4 MI4 ST4 PR4 Hc4).
      intros k5 Σ5 m5 g5 q0 q1 q2 b1 b2 b3 b4 b5 b6 b7 q3 q4 q5 q6 F5 fc5 Hc5 LV5 FR5 SP5 CR5 PU5 EM5 AM5 SM5 OBM5 ART5 MI5 ST5 PR5.
      eapply (Hk k5 Σ5 m5 g5 _ _ _ _ _ _ _ _ _ _ _ _ _ _ F5 fc5 Hc5 ltac:(rewrite LV5; exact LV2) ltac:(rewrite FR5; exact FR2) SP5 ltac:(clear - CR5 CR2; lia) PU5 EM5 AM5 SM5 OBM5 ART5 MI5 ST5 PR5).
  - (* [comment removed for export] *)
    rewrite (hc_iter_input znew e z pin pout STI) in BRK, RES.
    destruct (hc_viewsL Σ1 m [] SK ART0 PR0 I I I I I I I ltac:(intros _; exact I)) as (_ & _ & (SHe & _) & _).
    eapply (l1_realizes RT AF Σ1 PMc _ T c MST Hc).
    eapply (B0_hc_top_in cx _ SHE P gp tp F fc CX AE g e m); [exact STI| exact MD| exact EH1| exact SL| exact SHe|].
    apply evt_done. clear Hc SHe. intros k1 Hc1.
    eapply (hc_l2_inL Σ1 g e z pin pout m _ _ _ c11 c10 c9 c8 c7 c6 c5 c4 c3 c2 c1 c0 cra _ _ _ _ _ _ _ _ _ F fc T k1 STI PU SK CR28);
      [| | exact SM| exact OBM| exact SL| exact SAVED| exact ART0| exact MI0| exact ST0| exact PR0| exact Hc1|].
    { unfold emem. split; [exact EH1|]. split; [exact INU|]. split; [exact UNS|]. split; [exact EH2|]. split; [exact MTF|]. split; [exact SEL|]. split; [exact SELM|].
      split; [exact LEN|]. split; [exact CODE|]. split; [exact RFQ| exact LPK]. }
    { unfold CmpCut.amem, FTAB_WORDS. split; [exact AR1|]. split; [exact AR2| exact FTB]. }
    clear Hc1 EH1 EH2 INU UNS MTF SEL SELM LEN CODE RFQ LPK AR1 AR2 FTB SM OBM SL SAVED.
    intros k4 Σ2 m4 e_cb il z2 pin2 s1_4 a0_4 a1_4 a4_4 a5_4 a6_4 a7_4 s2_4 s7_4 t6_4 F4 fc4 HIN PU2 SK2 LV2 FR2 CR2 EM2 AM2 SM2 OBM2 ZO2 SL2 SAVED2
      ART4 MI4 ST4 PR4 Hc4.
    rewrite HIN in BRK, RES. cbn iota in BRK, RES.
    eapply (IH Σ2 (eg_after_cb cx g e_cb) (hc_after_cb e_cb il) z2 pin2 pout m4 _ _ _ c11 c10 c9 c8 c7 c6 c5 c4 c3 c2 c1 c0 cra _ _ _ _ _ _ _ _ _ _ F4 fc4 T k4 ef zf prf
              BRK RES PU2 SK2 ltac:(clear - CRED CR2; lia) EM2 AM2 SM2 OBM2 SL2 SAVED2 ART4 MI4 ST4 PR4 Hc4).
    intros k5 Σ5 m5 g5 q0 q1 q2 b1 b2 b3 b4 b5 b6 b7 q3 q4 q5 q6 F5 fc5 Hc5 LV5 FR5 SP5 CR5 PU5 EM5 AM5 SM5 OBM5 ART5 MI5 ST5 PR5.
    eapply (Hk k5 Σ5 m5 g5 _ _ _ _ _ _ _ _ _ _ _ _ _ _ F5 fc5 Hc5 ltac:(rewrite LV5; exact LV2) ltac:(rewrite FR5; exact FR2) SP5 ltac:(clear - CR5 CR2; lia) PU5 EM5 AM5 SM5 OBM5 ART5 MI5 ST5 PR5).
Qed.

End HCG.
