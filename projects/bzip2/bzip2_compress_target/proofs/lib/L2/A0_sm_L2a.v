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
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.L2 Require Import L2Kit L2Act L2Stmt A0_fs_L2f.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require Import PropExec.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import Tac WalkLib SegsA0.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzTac BzArr BzCMem BzCStream BzCState BzCMtf BzCHuff BzArrD CmpMem CmpCut CmpCutSM CmpCutSmA BzCFactsSmA CmpCutSmB BzCFactsGm BzCSmF1 BzCFactsSmB BzCFactsSd CmpHmKit CmpSmKit CmpSmKit2 AsanKit AsanKit2 AsanCut.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzCLemmas1 BzCHuffF1.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCHuffF1.BzCFactsHm.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import CmpCut6.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import A0_cmp_fsV A0_cmp_smV A0_cmp_smA A0_cmp_smP A0_cmp_smZ.
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
  E + 55768 + 4096 <= P /\ A1 + ARR1_SIZE + 4096 <= P /\ A2 + ARR2_SIZE + 4096 <= P /\ FT + 262148 + 4096 <= P /\ FB + 256 + 4096 <= P /\ SHF + 32 + 4096 <= P /\ 17594333495296 + 65536 <= P /\ 0 < A1 /\ 0 < A2 /\ 0 < FT /\ P + 1616 <= 18446744073709551616 /\ lo + 4096 + 240 <= P.
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
Ltac vw0 H k := eapply (frdW_cell_at a0segs [] _ _ _ k); [apply frdW_intro; [exact H| exact I]| reflexivity| clear; lia].
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Notation LOW0 w16 w24 w64 w72 w80 w88 w96 w104 w112 w120 w152 w160 w168 w184 w200 w208 w216 :=
  [C8 w16; C8 w24; C8 (Z_to_bv 64 FB); C8 (Z_to_bv 64 FB); C8 (Z_to_bv 64 (FB + 128)); C8 (Z_to_bv 64 SHF); C8 w64; C8 w72;
   C8 w80; C8 w88; C8 w96; C8 w104; C8 w112; C8 w120; C8 (Z_to_bv 64 (SHE + 82)); C8 (Z_to_bv 64 (E + 656)); C8 (Z_to_bv 64 E);
   C8 w152; C8 w160; C8 w168; C8 (Z_to_bv 64 (E + 668)); C8 w184; C8 (Z_to_bv 64 A); C8 w200; C8 w208; C8 w216; C8 (Z_to_bv 64 nInUse)].
Notation HI0 w1344 w1352 w1360 w1368 w1392 w1400 w1408 w1424 w1432 :=
  [C8 w1344; C8 w1352; C8 w1360; C8 w1368; C8 (Z_to_bv 64 (FB + 32)); C8 (Z_to_bv 64 (FB + 64)); C8 w1392; C8 w1400; C8 w1408; C8 (Z_to_bv 64 A); C8 w1424; C8 w1432].
Notation Wlen := [(E + 37708, E + 39256)].
Notation cP := (Z_to_bv 64 P).

Lemma sm_lenrows : forall (n : nat) (t : Z) (len : zarr) (Σ1 : rts RT) (m0 m : mem)
    (w16 w24 w64 w72 w80 w88 w96 w104 w112 w120 w152 w160 w168 w184 w200 w208 w216 : word) (w1344 w1352 w1360 w1368 w1392 w1400 w1408 w1424 w1432 : word)
    (t1 t2 a3 a4 a5 a6 s3 s9 s10 s11 t3 t4 t5 t6 : word) F fc T c,
  t + Z.of_nat n = 6 -> 0 <= t -> (1 <= n)%nat -> SOK Σ1 ->
  u8arr a0segs m (E + 37708) (ovb len (jseg J 37708 1548) 1548) ->
  rw_cells a0segs m (P + 16) (LOW0 w16 w24 w64 w72 w80 w88 w96 w104 w112 w120 w152 w160 w168 w184 w200 w208 w216) ->
  rw_cells a0segs m (P + 1344) (HI0 w1344 w1352 w1360 w1368 w1392 w1400 w1408 w1424 w1432) ->
  ART RT Σ1 m -> KMem.mem_inv asegs m -> stk asegs m lo P -> PRESI m ->
  rt_pres_fp (rt_live RT Σ1) (rt_frames RT Σ1) P Wlen m0 m -> wmono asegs m0 m ->
  ASTA RT Σ1 PMc (eq (MS (mkR (Z_to_bv 64 0x8a5d4) cP gp tp (Z_to_bv 64 E) t1 t2 sp cP (Z_to_bv 64 (E + 37708 + 258 * t)) (Z_to_bv 64 15) (Z_to_bv 64 A) a3 a4 a5 a6 (Z_to_bv 64 nInUse)
                              (Z_to_bv 64 (E + 37708 + 258 * t)) s3 cSB (Z_to_bv 64 (6 - t)) (Z_to_bv 64 (E + 668)) (Z_to_bv 64 (-1)) (Z_to_bv 64 A1) s9 s10 s11 t3 t4 t5 t6)
                         F (Z_to_bv 64 0x52ea0) fc None m (seg_rom a0segs))) c ->
  (forall c' (m' : mem) (u0 u1 u2 e0 e1 e2 e3 e4 e5 e6 e7 u3 u4 u5 u6 : word) F' fc',
     ASTA RT Σ1 PMc (eq (MS (mkR (Z_to_bv 64 0x8a5d4) cP gp tp u0 u1 u2 sp cP e0 e1 e2 e3 e4 e5 e6 e7
                                 (Z_to_bv 64 (E + 37708 + 258 * 5)) s3 cSB (Z_to_bv 64 1) (Z_to_bv 64 (E + 668)) (Z_to_bv 64 (-1)) (Z_to_bv 64 A1) s9 s10 s11 u3 u4 u5 u6)
                            F' (Z_to_bv 64 0x8a5d4) fc' None m' (seg_rom a0segs))) c' ->
     u8arr a0segs m' (E + 37708) (ovb (sm_len_init n len A t) (jseg J 37708 1548) 1548) ->
     rw_cells a0segs m' (P + 16) (LOW0 w16 w24 w64 w72 w80 w88 w96 w104 w112 w120 w152 w160 w168 w184 w200 w208 w216) ->
     rw_cells a0segs m' (P + 1344) (HI0 w1344 w1352 w1360 w1368 w1392 w1400 w1408 w1424 w1432) ->
     ART RT Σ1 m' -> KMem.mem_inv asegs m' -> stk asegs m' lo P -> PRESI m' ->
     rt_pres_fp (rt_live RT Σ1) (rt_frames RT Σ1) P Wlen m0 m' -> wmono asegs m0 m' ->
     realizes asegs c' T) ->
  realizes asegs c T.
Proof.
  induction n as [|n IH]. { intros; lia. }
  intros t len Σ1 m0 m w16 w24 w64 w72 w80 w88 w96 w104 w112 w120 w152 w160 w168 w184 w200 w208 w216 w1344 w1352 w1360 w1368 w1392 w1400 w1408 w1424 w1432
    t1 t2 a3 a4 a5 a6 s3 s9 s10 s11 t3 t4 t5 t6 F fc T c Ht Ht0 Hn SK LEN LOW HI ART0 MI0 ST0 PR0 ACC WMA Hc Hk.
  shsep_open. sm_keys. pose proof SK as (FRM & SP0E & LIVS). pose proof (LIVS _ LIVE) as LVE.
  pose proof G as [_ _ _ _ GLOW GLOR GPUS GSPT GSPA GFR GSH GSP0 _ _]. unfold USTACK_TOP, RT_STACK, STACK_WIN, SEGTOP_A in GLOW, GLOR, GSPT, GFR, GSH, GSP0.
  pose proof SFA as SFA'. unfold smA_facts in SFA'. cbv zeta in SFA'. destruct SFA' as (NI & NM & _).
  assert (HA : A = nInUse + 2) by reflexivity.
  pose proof (af_live_range RT AF Σ1 m E 55768 ART0 LVE) as (EL0 & EL1 & _). rewrite SP0E in EL1. unfold STACK_WIN in EL1.
  (* [comment removed for export] *)
  destruct (row_before_memset a0segs m (E + 37708) len (jseg J 37708 1548) 1548 (258 * t) A LEN ltac:(clear - Ht0; lia) ltac:(clear - NI HA; lia) ltac:(clear - Ht Ht0 NI HA Hn; lia)) as (L0 & L1 & L2). clear LEN L1.
  eapply (memset_call G PMc FDO MST Σ1 (E + 37708 + 258 * t) A (Z_to_bv 8 15) m); [exact MSET| exact SK| clear - EL0 EL1 Ht Ht0 GSP0; lia| clear - NI HA; lia| | exact ART0| exact MI0| exact ST0| exact Hc|].
  { apply (cdst_live AF G Σ1 m E 55768 (E + 37708 + 258 * t) A ART0 LVE); [clear - Ht0; lia| clear - Ht Ht0 NI HA Hn; lia| clear - NI HA; lia]. }
  clear Hc. intros c1 m1 u0 u1 u2 e1 e2 e3 e4 e5 e6 e7 u3 u4 u5 u6 F1 fc1 Hc1 ART1 MI1 ST1 WM1 BY1 STEP1.
  pose proof (pres_step G Σ1 _ m m1 SK PR0 STEP1 ltac:(per_interval; right; cbn [outside]; lia)) as PR1.
  xfer_rt G SK STEP1 WM1 m m1.
  rewrite (KMState.ret_pc_even 0x8a5d4 ltac:(lia) eq_refl) in Hc1.
  assert (LEN1 : u8arr a0segs m1 (E + 37708) (ovb (sm_len_init_row (Z.to_nat A) len t 0) (jseg J 37708 1548) 1548)).
  { destruct (af_acc_live RT AF Σ1 m1 E 55768 ART1 LVE) as [WRE _].
    pose proof (n_rw_CB_of_bytes m1 (E + 37708 + 258 * t) (repeat (Z_to_bv 8 15) (Z.to_nat A)) BY1
                  ltac:(rewrite repeat_length; apply (wr_at_sub asegs m1 E 55768 _ _ WRE); clear - Ht Ht0 NI HA Hn; lia)) as ROW.
    rewrite repeat_length in ROW.
    apply (row_after_memset a0segs m1 (E + 37708) len (jseg J 37708 1548) 1548 t A L0 ROW L2); [clear - Ht0; lia| clear - NI HA; lia| clear - Ht Ht0 NI HA Hn; lia]. }
  clear L0 L2 BY1.
  assert (ACC1 : rt_pres_fp (rt_live RT Σ1) (rt_frames RT Σ1) P Wlen m0 m1).
  { apply (pfp_trans _ _ _ _ m0 m m1 ACC). apply (pfp_weaken _ _ _ _ Wlen m m1 STEP1). per_interval; cbn [KFrame.outside]; lia. }
  assert (WMA1 : wmono asegs m0 m1) by (eapply wmono_trans; [exact WMA| exact WM1]).
  clear STEP1 WM1 ACC WMA.
  destruct n as [|n'].
  - (* [comment removed for export] *)
    assert (t = 5) by (clear - Ht; lia). subst t. cbn [sm_len_init].
    eapply (Hk c1 m1); [exact Hc1| exact LEN1| exact LOW| exact HI| exact ART1| exact MI1| exact ST1| exact PR1| exact ACC1| exact WMA1].
  - (* [comment removed for export] *)
    eapply (l1_realizes RT AF Σ1 PMc _ T c1 MST Hc1).
    eapply (A0_smA_in3r cx e _ gp tp sp F1 fc1 P CX SFA t m1); [exact Ht0| clear - Ht; lia| vw0 LOW 128%nat| vw0 LOW 208%nat| vw0 HI 72%nat|].
    apply evt_done. clear Hc1. intros c2 Hc2.
    rewrite sm_len_init_S in Hk.
    eapply (IH (t + 1) _ Σ1 m0 m1 w16 w24 w64 w72 w80 w88 w96 w104 w112 w120 w152 w160 w168 w184 w200 w208 w216 w1344 w1352 w1360 w1368 w1392 w1400 w1408 w1424 w1432
              _ _ _ _ _ _ s3 s9 s10 s11 _ _ _ _ F1 fc1 T c2 ltac:(clear - Ht; lia) ltac:(clear - Ht0; lia) ltac:(clear; lia) SK LEN1 LOW HI ART1 MI1 ST1 PR1 ACC1 WMA1).
    + replace (6 - (t + 1)) with (6 - (t + 1)) by reflexivity. exact Hc2.
    + exact Hk.
Qed.

(* [comment removed for export] *)
Ltac dj H := let D := fresh "D" in pose proof H as D; unfold id in D |- *; clear - D; lia.
Lemma shd_anchor0 : forall X SHX q2 x, sanchor X SHX -> (x < X \/ X + 8 * q2 <= x) -> (x / 8 + 2147450880 + 1 <= SHX \/ SHX + q2 <= x / 8 + 2147450880).
Proof. intros X SHX q2 x [M E'] H. subst SHX. Z.div_mod_to_equations. lia. Qed.

(* [comment removed for export] *)
Lemma sm_shE : forall Σ (m : mem) W, SOK Σ -> ART RT Σ m ->
  (forall x, E <= x < E + 55768 -> 0 <= x < 2^47 -> disjoint_from W (x / 8 + 2147450880) 1) -> shzW a0segs W m E (E + 55768).
Proof.
  intros Σ m W SK ART0 D. pose proof SK as (_ & SP0E & LIVS). pose proof (LIVS _ LIVE) as LVE.
  destruct (af_acc_live RT AF Σ m E 55768 ART0 LVE) as [_ ACCE].
  pose proof (af_live_range RT AF Σ m E 55768 ART0 LVE) as (EL0 & EL1 & _). rewrite SP0E in EL1.
  pose proof G as [_ _ _ _ _ _ _ _ _ _ _ GSP0 _ _]. unfold USTACK_TOP, STACK_WIN, SEGTOP_A in GSP0, EL1.
  pose proof CX as CX'. unfold cctx_ok in CX'. cbv zeta in CX'. destruct CX' as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & ME16 & _).
  apply (shzW_of_acc_gen a0segs W m E 55768 E (E + 55768) ACCE); [clear - EL0; lia| clear; lia| clear - ME16; Z.div_mod_to_equations; lia|].
  intros x Hx. apply (D x Hx). clear - Hx EL0 EL1 GSP0. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Notation LOWJ w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 w96 w104 w112 w120 w128 w136 w152 w160 w168 w176 w184 w192 w200 w208 w216 w224 :=
  [C8 w16; C8 w24; C8 w32; C8 w40; C8 w48; C8 w56; C8 w64; C8 w72; C8 w80; C8 w88; C8 w96; C8 w104; C8 w112; C8 w120; C8 w128; C8 w136; C8 (Z_to_bv 64 E);
   C8 w152; C8 w160; C8 w168; C8 w176; C8 w184; C8 w192; C8 w200; C8 w208; C8 w216; C8 w224].
Notation Winit := [(E + 37708, E + 39256); (P + 16, P + 232); (P + 1344, P + 1440); (P + 1464, P + 1472); (FB, FB + 24); (SHF, SHF + 20)].

Lemma sm_init : forall (Σ1 : rts RT) (m : mem)
    (w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 w96 w104 w112 w120 w128 w136 w152 w160 w168 w176 w184 w192 w200 w208 w216 w224 : word)
    (w1344 w1352 w1360 w1368 w1376 w1384 w1392 w1400 w1408 w1416 w1424 w1432 w1464 : word)
    (ra t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s2 s3 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc T c,
  SOK Σ1 ->
  rw_cells a0segs m E (EHEAD1 cx g e) -> rw_cells a0segs m (E + 640) (EHEAD2 cx g e) ->
  u32arr a0segs m (E + 672) (ovw (e_mtfFreq e) (jseg J 672 1032) 258) ->
  u8arr a0segs m (E + 37708) (ovb (e_len e) (jseg J 37708 1548) 1548) ->
  rw_cells a0segs m (P + 16) (LOWJ w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 w96 w104 w112 w120 w128 w136 w152 w160 w168 w176 w184 w192 w200 w208 w216 w224) ->
  rw_cells a0segs m (P + 1344) [C8 w1344; C8 w1352; C8 w1360; C8 w1368; C8 w1376; C8 w1384; C8 w1392; C8 w1400; C8 w1408; C8 w1416; C8 w1424; C8 w1432] ->
  rw_cells a0segs m (P + 1464) [C8 w1464] ->
  wr_at asegs m FB 248 -> wr_at asegs m SHF 32 ->
  ART RT Σ1 m -> KMem.mem_inv asegs m -> stk asegs m lo P -> PRESI m ->
  ASTA RT Σ1 PMc (eq (MS (mkR ra cP gp tp t0 t1 t2 sp cP (Z_to_bv 64 FB) a1 a2 a3 a4 a5 a6 a7 s2 s3 cSB s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                         F (Z_to_bv 64 0x8a420) fc None m (seg_rom a0segs))) c ->
  (forall c' (m' : mem) (v16 v24 : word) (u0 u1 e3 e4 e5 e6 e7 x3 x5 x11 u6 : word) F' fc',
     ASTA RT Σ1 PMc (eq (MS (mkR (Z_to_bv 64 0x8a9d8) cP gp tp u0 u1 (Z_to_bv 64 (E + 676)) sp cP (Z_to_bv 64 (FB + 64)) (Z_to_bv 64 0) (Z_to_bv 64 24) e3 e4 e5 e6 e7
                                 (Z_to_bv 64 (E + 45448)) x3 cSB x5 (Z_to_bv 64 (E + 668)) (Z_to_bv 64 A) (Z_to_bv 64 A1) (Z_to_bv 64 (SHE + 83)) (Z_to_bv 64 nG) x11
                                 (Z_to_bv 64 3) (Z_to_bv 64 (-1)) (Z_to_bv 64 (-2147483647)) u6)
                            F' (Z_to_bv 64 0x52ea0) fc' None m' (seg_rom a0segs))) c' ->
     rw_cells a0segs m' E (EHEAD1 cx g e) -> rw_cells a0segs m' (E + 640) (EHEAD2 cx g e) ->
     u32arr a0segs m' (E + 672) (ovw (e_mtfFreq e) (jseg J 672 1032) 258) ->
     u8arr a0segs m' (E + 37708) (ovb (ip_len (smA_ip e)) (jseg J 37708 1548) 1548) ->
     rw_cells a0segs m' (P + 16) (sm_loA cx e FB SHF SHE v16 v24) -> rw_cells a0segs m' (P + 152) [C8 (Z_to_bv 64 0)] -> rw_cells a0segs m' (P + 160) (sm_loB cx e SHE) ->
     rw_cells a0segs m' (P + 1344) (sm_hi cx e (FB + 32) (FB + 64) (Z_to_bv 64 37450) (E + 676) (E + 672)) ->
     rw_cells a0segs m' (P + 1464) [C8 (Z_to_bv 64 FB)] ->
     rw_cells a0segs m' FB [C8 (Z_to_bv 64 0x41b58ab3); C8 (Z_to_bv 64 0x148b3); C8 (Z_to_bv 64 0x8a3ac)] -> rw_cells a0segs m' SHF sm_shadow ->
     ART RT Σ1 m' -> KMem.mem_inv asegs m' -> stk asegs m' lo P -> PRESI m' ->
     rt_pres_fp (rt_live RT Σ1) (rt_frames RT Σ1) P Winit m m' -> wmono asegs m m' ->
     realizes asegs c' T) ->
  realizes asegs c T.
Proof.
  intros Σ1 m w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 w96 w104 w112 w120 w128 w136 w152 w160 w168 w176 w184 w192 w200 w208 w216 w224
    w1344 w1352 w1360 w1368 w1376 w1384 w1392 w1400 w1408 w1416 w1424 w1432 w1464
    ra t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s2 s3 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc T c SK EH1 EH2 MTF LEN LOW HI S1464 WRF WRS ART0 MI0 ST0 PR0 Hc Hk.
  shsep_open. sm_keys. pose proof SK as (FRM & SP0E & LIVS). pose proof (LIVS _ LIVE) as LVE.
  pose proof G as [_ _ _ _ GLOW GLOR GPUS GSPT GSPA GFR GSH GSP0 _ _]. unfold USTACK_TOP, RT_STACK, STACK_WIN, SEGTOP_A in GLOW, GLOR, GSPT, GFR, GSH, GSP0.
  pose proof (ag_ax G) as AX. pose proof alloc_ceiling_range as ACR.
  assert (CEP : CEIL <= P) by (unfold CEIL; rewrite ACE; unfold STACK_WIN; clear - GLOW GLOR; lia).
  assert (FBH : FB + 160 <= CEIL) by (unfold CEIL; rewrite ACE; unfold STACK_WIN; clear - GFR; lia).
  (* [comment removed for export] *)
  destruct (n_wr_at_rw_CB m FB 24 (wr_at_sub asegs m FB 248 FB 24 WRF ltac:(clear; lia) ltac:(clear; lia) ltac:(clear; lia)) ltac:(clear; lia)) as (jh & HDj).
  change (Z.to_nat 24) with 24%nat in HDj.
  apply (rw_cells_split_CB a0segs _ _ [] 24 _ [] [8;8;8]%nat) in HDj; [| reflexivity]. cbn [mk_CB_cells app] in HDj. cb8_all HDj.
  destruct (n_wr_at_rw_CB m SHF 20 (wr_at_sub asegs m SHF 32 SHF 20 WRS ltac:(clear; lia) ltac:(clear; lia) ltac:(clear; lia)) ltac:(clear; lia)) as (j20 & SHj).
  change (Z.to_nat 20) with 20%nat in SHj.
  assert (SHe : shzW a0segs [(P + 16, P + 232); (P + 1344, P + 1440); (P + 1464, P + 1472); (FB, FB + 24); (SHF, SHF + 20)] m E (E + 55768)).
  { apply (sm_shE Σ1 m _ SK ART0). intros x Hx X47. cbn [disjoint_from].
    assert (OP : forall a b, P <= a -> b <= SH_LO \/ SH_HI <= a) by (intros a b Ha; right; unfold SH_HI; clear - Ha XL7; lia).
    split; [apply shd_app; [exact X47| apply OP; clear; lia]|]. split; [apply shd_app; [exact X47| apply OP; clear; lia]|]. split; [apply shd_app; [exact X47| apply OP; clear; lia]|].
    split; [apply shd_app; [exact X47| pose proof FHI as D; unfold id in D; unfold SH_LO, SH_HI; clear - D; lia]|].
    split; [| exact I]. apply (shd_anchor0 FB SHF 20 x AX). pose proof DEFB as DJ. unfold id in DJ. clear - DJ Hx. lia. }
  eapply (l1_realizes RT AF Σ1 PMc _ T c MST Hc).
  eapply (A0_smA_in2 cx g e _ gp tp sp F fc P SHE (FB + 32) (FB + 64) FB SHF CX SFA GM CEP ltac:(clear - GFR; lia) FBH eq_refl eq_refl AE AX
            ltac:(dj DEFB) ltac:(dj DESH) ltac:(dj DFBSH) ltac:(unfold id; left; clear - XL6; lia) m);
    [exact EH1| exact EH2| exact LOW| exact HI| exact S1464| exact HDj| exact SHj| exact (kmem_inv_N _ _ MI0)| exact SHe|].
  clear EH1 EH2 LOW HI S1464 HDj SHj SHe Hc.
  intros m1 y1 y2 y3 y4 y5 y6 ys3 EH1 EH2 LOW HI S1464 HD SHD NMI1 MU1 WM1. apply evt_done. intros c1 Hc1.
  lazymatch type of MU1 with munch ?W _ _ => destruct (after_l1 AF G Σ1 W m m1 SK ART0 MI0 ST0 PR0 NMI1 MU1 WM1 ltac:(fp_ours)) as (ART1 & MI1 & ST1 & PR1 & STEP1) end.
  xfer_l1 m m1 MU1 WM1. clear NMI1 MU1.
  (* [comment removed for export] *)
  replace (Z_to_bv 64 (E + 37708)) with (Z_to_bv 64 (E + 37708 + 258 * 0)) in Hc1 by (f_equal; clear; lia).
  eapply (sm_lenrows 6 0 (e_len e) Σ1 m1 m1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc T c1 eq_refl ltac:(clear; lia) ltac:(clear; lia) SK LEN LOW HI ART1 MI1 ST1 PR1
            (pfp_refl _ _ _ _ m1) (wmono_refl _ m1) Hc1).
  clear Hc1 LEN LOW HI. intros c2 m2 z0 z1 z2 g0 g1 g2 g3 g4 g5 g6 g7 z3 z4 z5 z6 F2 fc2 Hc2 LEN LOW HI ART2 MI2 ST2 PR2 ACC2 WMA2.
  xfer_rt G SK ACC2 WMA2 m1 m2.
  change (sm_len_init 6 (e_len e) A 0) with (smA_len e) in LEN.
  (* [comment removed for export] *)
  destruct (AF_DRV Σ1 m2 ART2) as ((GS & _) & _). pose proof (ro_C8_KN m2 _ _ GS) as GOTS. clear GS.
  assert (SHe : shzW a0segs [(E + 37708, E + 39256); (P + 16, P + 232); (P + 1344, P + 1440)] m2 E (E + 55768)).
  { apply (sm_shE Σ1 m2 _ SK ART2). intros x Hx X47. cbn [disjoint_from].
    assert (OP : forall a b, P <= a -> b <= SH_LO \/ SH_HI <= a) by (intros a b Ha; right; unfold SH_HI; clear - Ha XL7; lia).
    split; [apply shd_app; [exact X47| pose proof OFFE as D; unfold id in D; unfold SH_LO, SH_HI; clear - D; lia]|].
    split; [apply shd_app; [exact X47| apply OP; clear; lia]|]. split; [apply shd_app; [exact X47| apply OP; clear; lia]| exact I]. }
  eapply (l1_realizes RT AF Σ1 PMc _ T c2 MST Hc2).
  eapply (A0_smA_in3z cx g e _ gp tp sp F2 fc2 P SHE (FB + 32) (FB + 64) FB SHF CX SFA GM CEP XL11 AE m2);
    [exact LEN| exact MTF| exact EH2| exact LOW| exact HI| exact GOTS| exact (kmem_inv_N _ _ MI2)| exact SHe|].
  clear LEN MTF EH2 LOW HI GOTS SHe Hc2.
  intros m3 v16 v24 q0 q1 q3 q4 q5 q6 q7 qs3 qs5 qs11 qt6 LEN MTF EH2 LOA ITER LOB HI NMI3 MU3 WM3. apply evt_done. intros c3 Hc3.
  lazymatch type of MU3 with munch ?W _ _ => destruct (after_l1 AF G Σ1 W m2 m3 SK ART2 MI2 ST2 PR2 NMI3 MU3 WM3 ltac:(fp_ours)) as (ART3 & MI3 & ST3 & PR3 & STEP3) end.
  xfer_l1 m2 m3 MU3 WM3. clear NMI3 MU3.
  eapply (Hk c3 m3 v16 v24); [exact Hc3| exact EH1| exact EH2| exact MTF| exact LEN| exact LOA| exact ITER| exact LOB| exact HI| exact S1464| exact HD| exact SHD
                             | exact ART3| exact MI3| exact ST3| exact PR3| | ].
  - apply (pfp_trans _ _ _ _ m m1 m3); [apply (pfp_weaken _ _ _ _ Winit m m1 STEP1); per_interval; cbn [KFrame.outside]; lia|].
    apply (pfp_trans _ _ _ _ m1 m2 m3); [apply (pfp_weaken _ _ _ _ Winit m1 m2 ACC2); per_interval; cbn [KFrame.outside]; lia|].
    apply (pfp_weaken _ _ _ _ Winit m2 m3 STEP3); per_interval; cbn [KFrame.outside]; lia.
  - eapply wmono_trans; [exact WM1|]. eapply wmono_trans; [exact WMA2| exact WM3].
Qed.

End SMG.
