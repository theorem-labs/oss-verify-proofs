(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.AS Require Import ShapeAlg.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.Lib Require Import ImageA RzCPS.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A Require Layout RT_iface D_defs D_kit I_read RT_liveprim RT_globals. Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.Layout.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.RT_iface.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.D_defs.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.D_kit.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.I_read.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.RT_liveprim.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.RT_globals.TwinB__.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A Require Import Shadow.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A Require L_libA D_libiface.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.L2B Require Import L2Kit L2Act L2StmtD B0_fs_L2f B0_sessK B0F_decK B0F_decX B0F_dec_L2a.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require Import PropExec.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import Tac WalkLib SegsA0 SegsB0.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzModel BzTac BzTables CmpMem AsanKit AsanKit2 AsanCut AsanCutB0.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzDefs BzInv BzContracts.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzArr BzCStream BzDState BzDBlock BzDK BzDU7 BzDU4 DecCutFB B0F_leafCut B0F_decV B0F_decRet B0F_decCutsA B0F_decCuts4 B0F_decCuts5 B0F_decCuts6 B0F_decCuts7 B0F_decCutsM B0F_decCuts8 B0F_decCutsE B0F_decCuts12S.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzArr OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDState OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDBlock.BzDHuff OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDBlock OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDK OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDU7 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.DecCutFB OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.B0F_decV OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.B0F_decRet OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.B0F_decCutsA OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.B0F_decCuts4 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.B0F_decCuts5 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.B0F_decCuts6 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.B0F_decCuts7 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.B0F_decCutsM OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.B0F_decCuts8 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.B0F_decCutsE OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.B0F_decCuts12S.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require B0F_decMain B0F_dec_U13b B0F_dec_epi B0F_dec_U12SF B0F_dec_U7B B0F_dec_U7C.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeil.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Open Scope Z_scope.
#[local] Notation mem := (word -> option byte).

Section DECL2.
Context {ACEIL__ : ACeil}.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Hypothesis AF_DRV : forall Σ m, ART RT Σ m -> drv_consts m.
Variable A : act14.                                   (* [comment removed for export] *)
Variables (sp0 : Z) (fr : list (Z * nat)) (live0 Wc : list (Z * Z)).
Hypothesis G : act_geom RT (a_lo A) (a_P A) (a_usp A) sp0 true 0 (a_fb A) (a_shf A) 64 8 fr live0 Wc.
Variable mi : mem.
Variable PMc : Model -> Prop.
Hypothesis FDO : fdfs_only PMc. Hypothesis MST : mat_stable PMc.
Variable T : TSet.
Notation PRESI := (PRESI (a_usp A) fr live0 Wc mi).
Notation SOK Σ := (sig_ok RT sp0 true 0 (a_fb A) fr live0 Σ).
Notation cx := (a_cx A).
Notation S := (b_s (a_cx A)).
Notation QL := (QL RT PMc T).

Hypothesis AOK : act_ok BIHI0 A.
Hypothesis ATP : a_tp A = Z_to_bv 64 0x6094d8.
Hypothesis AG1 : a_g1 A = B0F_decK.DG1. Hypothesis ASV : a_sv A = B0F_decK.DSV.
Hypothesis ROOM : a_lo A + RT_STACK <= a_P A - 256.
Hypothesis W14C : forall x, ~ KFrame.outside (W14 A) x ->
  (a_P A - 256 <= x < a_usp A) \/ (a_fb A <= x < a_fb A + 64 - 8) \/ (a_shf A <= x < a_shf A + 8) \/ ~ outside Wc x.
Hypothesis DSC : forall x, S <= x < S + 64144 -> ~ outside Wc x.
(* [comment removed for export] *)
Variables (zp zn : Z) (fS : Z) (kS : nat).
Hypothesis SLIV0 : In (S, 64144) live0.
Hypothesis ZLIV0 : In (zp, zn) live0. Hypothesis ZLO : zp <= b_src cx. Hypothesis ZHI : b_src cx + b_len cx <= zp + zn.
Hypothesis TLIV0 : b_small cx = 0 -> In (b_tt cx, 400000 * b_n cx) live0.
Hypothesis LLIV0 : b_small cx = 1 -> In (b_ll16 cx, 200000 * b_n cx) live0 /\ In (b_ll4 cx, 50000 * b_n cx) live0.
Hypothesis FSIN : In (fS, kS) fr. Hypothesis FSLO : fS <= b_strm cx. Hypothesis FSHI : b_strm cx + 80 <= fS + fs_size kS - 8.
Hypothesis ZSH0 : bytes_at b0segs mi (a_sht A) (repeat z8 10).
Hypothesis LIB0 : OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.L_libA.TwinB__.LIB_A mi.
Hypothesis WCI : forall x, ~ outside Wc x -> (S <= x < S + 64144) \/ (b_strm cx <= x < b_strm cx + 20) \/ ~ outside (blk_ivls cx) x.
(* [comment removed for export] *)
Variable CR : Z.
Variable R0 : dres.
Definition INV (Σ : rts RT) (m : mem) : Prop :=
  SOK Σ /\ rt_live RT Σ = live0 /\ rt_credit RT Σ = CR /\ ART RT Σ m /\ KMem.mem_inv bsegs m /\ PRESI m.
Hypothesis HK : forall c' (Σ2 : rts RT) (m' : mem) (rv : Z) (L : dsv) (d : dst) (s : dstrm) (J : jk)
    (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) F' fc',
  DRet rv L d s = R0 ->
  ASTA RT Σ2 PMc (eq (MS (mkR (a_ra A) (a_sp A) (a_gp A) (a_tp A) t0 t1 t2 (a_s0 A) (a_s1 A) (Z_to_bv 64 rv) a1 a2 a3 a4 a5 a6 a7
                              (a_s2 A) (a_s3 A) (a_s4 A) (a_s5 A) (a_s6 A) (a_s7 A) (a_s8 A) (a_s9 A) (a_s10 A) (a_s11 A) t3 t4 t5 t6)
                         F' (ret_pc (a_ra A)) fc' None m' (seg_rom b0segs))) c' ->
  rt_frames RT Σ2 = fr -> rt_live RT Σ2 = live0 -> rt_sp0 RT Σ2 = sp0 -> rt_credit RT Σ2 = CR ->
  ART RT Σ2 m' -> KMem.mem_inv bsegs m' -> stk bsegs m' (a_lo A) (a_usp A) -> PRESI m' ->
  dmem DI_B0 cx (a_g1 A) (a_sv A) (a_payload A) m' (dvF cx J (d_set_sv d L) s) ->
  dpureF cx (a_b0 A) (a_payload A) J (d_set_sv d L) s -> dpost14 (d_set_sv d L) ->
  realizes bsegs c' T.
(* [comment removed for export] *)
Hypothesis KLIB : forall m, PRESI m -> OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.L_libA.TwinB__.LIB_A m.
Hypothesis KZSH : forall m, PRESI m -> bytes_at b0segs m (a_sht A) (repeat z8 10).
Hypothesis OFFT : b_strm cx + 80 <= 0x7fff7000 \/ 0x10007fff8000 <= b_strm cx.
Hypothesis OFFF : a_fb A + 64 <= 0x7fff7000 \/ 0x10007fff8000 <= a_fb A.
Hypothesis OFFP : 0x10007fff8000 <= a_P A - 256.
Hypothesis USPT : a_usp A <= 2^47.
Hypothesis HIS : BIHI0 <= S.
Hypothesis ACE : alloc_ceiling = sp0 - STACK_WIN.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Notation AA m F fc := (dk_setm0 A m F fc).
Ltac dk_norm := cbn [dk_setm0 a_cx a_g1 a_sv a_payload a_m0 a_lo a_P a_sp a_b0 a_h0 a_fb a_shf a_shs a_sht a_gp a_tp a_F a_fc a_ra a_s0 a_s1 a_s2 a_s3 a_s4 a_s5 a_s6 a_s7 a_s8 a_s9 a_s10 a_s11] in *.

Lemma dk_aok : forall m F fc, act_ok BIHI0 (AA m F fc).
Proof. intros. apply act_ok_setm0. exact AOK. Qed.

Lemma dk_ash : forall Σ m F fc, INV Σ m -> act_sh DI_B0 (AA m F fc).
Proof.
  intros Σ m F fc (SK & LV & _ & ART0 & _ & PR).
  apply (dec_act_sh RT AF Σ m (AA m F fc) zp zn ART0 eq_refl (dk_aok m F fc)); cbn [dk_setm0 a_cx a_sht a_fb a_P a_sp]; rewrite ?LV;
    first [assumption| exact (KZSH m PR)].
Qed.

Lemma dk_plen : Z.of_nat (length (a_payload A)) = b_len cx.
Proof. destruct AOK as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & PL & _). exact PL. Qed.

Lemma dk_dsep : dsep cx.
Proof.
  destruct AOK as (LINB & _ & SEPB & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & NZF & NZS). cbv zeta in LINB.
  destruct LINB as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & SM01 & NR & _).
  destruct SEPB as (D1 & D2 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & DTT & DL16 & DL4 & _). unfold disj, DSTATE_SIZE in *.
  intros x Hx. split; [clear - D1 Hx; lia|]. split; [clear - D2 Hx; lia|].
  unfold blk_ivls. destruct SM01 as [E|E]; rewrite E; cbn [Z.eqb outside].
  - destruct (DTT (NZF E)) as (B1 & _). clear - B1 Hx. lia.
  - destruct (NZS E) as [N16 N4]. destruct (DL16 N16) as (B1 & _). destruct (DL4 N4) as (B2 & _). clear - B1 B2 Hx. lia.
Qed.

(* [comment removed for export] *)
Lemma dk_acl : forall Σ x, SOK Σ -> rt_live RT Σ = live0 -> dfp cx x -> aclient (rt_live RT Σ) (rt_frames RT Σ) (a_P A) x.
Proof.
  intros Σ x SK LV [D|[D|[D|D]]].
  - apply (acl_live RT (a_P A) Σ S 64144 x); [rewrite LV; exact SLIV0| exact D].
  - apply (acl_caller G Σ x SK). right; right; right; left. exists fS, kS. split; [exact FSIN| clear - D FSLO FSHI; lia].
  - apply (acl_live RT (a_P A) Σ zp zn x); [rewrite LV; exact ZLIV0| clear - D ZLO ZHI; lia].
  - destruct AOK as (LINB & _). cbv zeta in LINB. destruct LINB as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & SM01 & _).
    unfold blk_ivls in D. destruct SM01 as [E|E]; rewrite E in D; cbn [Z.eqb outside] in D.
    + apply (acl_live RT (a_P A) Σ (b_tt cx) (400000 * b_n cx) x); [rewrite LV; exact (TLIV0 E)| clear - D; lia].
    + destruct (LLIV0 E) as [L16 L4].
      assert (C : (b_ll16 cx <= x < b_ll16 cx + 200000 * b_n cx) \/ (b_ll4 cx <= x < b_ll4 cx + 50000 * b_n cx)) by (clear - D; lia).
      destruct C as [C|C].
      * apply (acl_live RT (a_P A) Σ (b_ll16 cx) (200000 * b_n cx) x); [rewrite LV; exact L16| exact C].
      * apply (acl_live RT (a_P A) Σ (b_ll4 cx) (50000 * b_n cx) x); [rewrite LV; exact L4| exact C].
Qed.

(* [comment removed for export] *)
Lemma dk_dmem : forall Σ (m : mem) v, ART RT Σ m -> PRESI m -> dmemL cx (a_payload A) m v -> dmem DI_B0 cx (a_g1 A) (a_sv A) (a_payload A) m v.
Proof. intros Σ m v ART0 PR H. rewrite AG1, ASV. exact (dmem_of_L RT AF AF_DRV Σ m cx _ v ART0 (KLIB m PR) H). Qed.

Lemma dk_ro_C8_inj : forall (m : mem) a w w', ro_cells b0segs m a [C8 w] -> ro_cells b0segs m a [C8 w'] -> w = w'.
Proof.
  intros m a w w' [_ B1] [_ B2]. cbn [cells_bytes cbytes app] in B1, B2. rewrite app_nil_r in B1, B2.
  destruct B1 as (_ & _ & R1). destruct B2 as (_ & _ & R2). rewrite length_le8 in R1, R2.
  rewrite <- (le_bytes_to_word_le8 w), <- (le_bytes_to_word_le8 w'). f_equal.
  apply nth_error_ext. intros i. destruct (Nat.lt_ge_cases i 8) as [L|L].
  - rewrite <- (R1 i L). exact (R2 i L).
  - rewrite (proj2 (nth_error_None (le8 w) i)) by (rewrite length_le8; exact L).
    rewrite (proj2 (nth_error_None (le8 w') i)) by (rewrite length_le8; exact L). reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma dec_flag : forall Σ m F fc, INV Σ m -> B0F_FLAG (AA m F fc) (QL Σ R0).
Proof.
  intros Σ m0 F0 fc0 (SK & LV & CRE & ART0 & MI0 & PR0).
  unfold B0F_FLAG. intros until j38. intros DM FRL FRH GEO NG FLP FRM FRT FF FS ST MU WM NMI DP DPO.
  apply evt_done. intros ER c1 Hc1. dk_norm.
  destruct (after_l1_leaf AF G Σ (W14 (AA m0 F0 fc0)) 256 m0 m SK ART0 MI0 PR0 NMI MU WM ltac:(clear; lia) ROOM W14C) as (ART1 & MI1 & PR1 & _).
  pose proof AOK as AOK'. destruct AOK' as (_ & _ & _ & _ & _ & _ & LO2 & LO1 & _ & GEO' & _).
  pose proof (ck_intro (a_P A) CStack) as KP. pose proof (ck_intro (a_lo A) CStack) as KLO.
  (* [comment removed for export] *)
  destruct (release_inline2 AF G (mi := mi) Σ m eq_refl SK ART1) as (Σ2 & fl' & FLC & FLP' & FL0 & FLW & FLD & REL).
  replace (a_fb A + 64 - 8) with (a_fb A + 56) in FLP' by (clear; lia).
  pose proof (dk_ro_C8_inj m _ _ _ FLP (ro_C8_KN m _ _ FLP')) as EFL. rewrite EFL in Hc1. clear FLP FLP' FF FS EFL.
  (* [comment removed for export] *)
  eapply (l1_realizes RT AF Σ PMc _ T c1 MST Hc1).
  eapply (B0F_dec_epi.B0F_rel_flag _ m fl' (Z_to_bv 8 1)); [exact FLC| exact (kmem_inv_N _ _ MI1)|].
  intros m2 FLC2 NMI2 MU2 WM2. apply evt_done. intros c2 Hc2.
  destruct (REL m2 MU2 WM2 FLC2 MI1 NMI2 ST PR1) as (ART2 & FRS2 & LV2 & SP2 & CR2 & AL2 & AM2 & MI2 & ST2 & PR2).
  (* [comment removed for export] *)
  assert (DM2 : dmem DI_B0 cx (a_g1 A) (a_sv A) (a_payload A) m2 (dvF cx J (d_set_sv d L) s)).
  { apply (dk_dmem Σ2 m2 _ ART2 PR2). apply (dmemLF_agree cx _ m m2 J _ s dk_plen); [| exact (dmemL_of m cx _ _ _ _ DM)].
    apply (agree_of_nmunch [(fl', fl' + 1)] m m2 _ MU2). intros x Hx. cbn [outside]. split; [| exact I].
    assert (C : cls RT (a_P A) Σ x 1) by (intros y Hy; replace y with x by (clear - Hy; lia); exact (dk_acl Σ x SK LV Hx)).
    pose proof (FLD x 1 C) as D. clear - D. lia. }
  clear DM ST. unfold FT_REGS in FRT. dk_norm.
  xfer_fl G SK FLD m m2 MU2 WM2.
  pose proof (ASTA_switch RT Σ Σ2 PMc _ c2 Hc2 AL2 AM2) as Hc2'. clear Hc2.
  (* [comment removed for export] *)
  eapply (l1_realizes RT AF Σ2 PMc _ T c2 MST Hc2').
  eapply (B0F_dec_epi.B0F_epi (AA m0 F0 fc0) _ m2 _ _ zt ng jg); dk_norm; [exact GEO| exact NG| clear - LO1; lia| exact FRL| exact FRM| exact FRH| exact FRT| exact ST2|].
  intros STu. apply evt_done. intros c3 Hc3.
  eapply (HK c3 Σ2 m2 rv L d s J); [exact ER| exact Hc3| exact FRS2| rewrite LV2; exact LV| exact SP2| rewrite CR2; exact CRE| exact ART2| exact MI2| exact STu| exact PR2| exact DM2| exact DP| exact DPO].
Qed.

Lemma dec_retc : forall Σ m F fc, INV Σ m -> B0F_RETC (AA m F fc) (QL Σ R0).
Proof. intros Σ m F fc IV. apply (B0F_dec_U13b.B0F_dec_retA (AA m F fc) (dk_aok m F fc) (dk_ash Σ m F fc IV)). exact (dec_flag Σ m F fc IV). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma dk_geo : a_lo A + 256 <= a_P A /\ a_P A + 864 <= a_usp A /\ a_usp A <= a_P A + 880 /\ S + 64144 <= a_lo A /\ 0 < S.
Proof.
  destruct AOK as (LINB & _ & _ & _ & _ & _ & LO2 & LO1 & _ & GEO & _). cbv zeta in LINB. destruct LINB as (S0 & SCE & _). unfold DSTATE_SIZE, CEILING in *.
  clear - S0 SCE LO2 LO1 GEO. lia.
Qed.
Lemma dk_fsep : (a_fb A + 64 <= S \/ S + 64144 <= a_fb A) /\ (a_shf A + 8 <= S \/ S + 64144 <= a_shf A).
Proof.
  destruct AOK as (_ & _ & SEPB & _). destruct SEPB as (_ & _ & _ & _ & _ & _ & DFS & _ & _ & _ & DSS & _). unfold disj, DSTATE_SIZE in DFS, DSS. clear - DFS DSS. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma dk_lin : 0 < S /\ S + 64144 <= a_lo A /\ 0 < b_strm cx /\ b_strm cx + 80 <= a_lo A /\ 0 < b_src cx /\ b_src cx + b_len cx <= a_lo A /\
  0 < a_fb A /\ a_fb A + 64 <= a_lo A /\ 2147450880 <= a_shf A /\ a_shf A + 8 <= 17594333495296 /\
  (b_small cx = 0 -> 0 < b_tt cx /\ b_tt cx + 400000 * b_n cx <= a_lo A) /\
  (b_small cx = 1 -> 0 < b_ll16 cx /\ b_ll16 cx + 200000 * b_n cx <= a_lo A /\ 0 < b_ll4 cx /\ b_ll4 cx + 50000 * b_n cx <= a_lo A) /\
  (b_small cx = 0 \/ b_small cx = 1).
Proof.
  destruct AOK as (LINB & _ & _ & _ & _ & _ & LO2 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & NZF & NZS). cbv zeta in LINB.
  destruct LINB as (S0 & SCE & T0 & T1c & SRC0 & _ & _ & SRC1 & _ & _ & _ & _ & FB0 & FB1 & SH0 & SH1 & SM01 & _ & TTb & L16b & L4b & _).
  unfold DSTATE_SIZE, CEILING in *.
  repeat (split; [first [assumption| clear - SCE T1c SRC1 FB1 LO2; lia]|]).
  split. { intros E. destruct TTb as [B|B]; [exfalso; exact (NZF E B)| clear - B LO2; lia]. }
  split. { intros E. destruct (NZS E) as [N16 N4]. destruct L16b as [B|B]; [exfalso; exact (N16 B)|]. destruct L4b as [B4|B4]; [exfalso; exact (N4 B4)|]. clear - B B4 LO2; lia. }
  exact SM01.
Qed.

Lemma dk_dfp_lo : forall x, dfp cx x -> 0 < x < a_lo A.
Proof.
  pose proof dk_lin as (S0 & S1 & T0 & T1 & Z0 & Z1 & _ & _ & _ & _ & TT & LL & SM01). intros x [D|[D|[D|D]]]; try (clear - D S0 S1 T0 T1 Z0 Z1; lia).
  unfold blk_ivls in D. destruct SM01 as [E|E]; rewrite E in D; cbn [Z.eqb outside] in D.
  - destruct (TT E) as (B0 & B1). clear - D B0 B1. lia.
  - destruct (LL E) as (B0 & B1 & B2 & B3). clear - D B0 B1 B2 B3. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma dk_w14_img : forall a n, 0x10000 <= a -> a + n <= BIHI0 -> disjoint_from (W14 A) a n.
Proof.
  intros a n A0 A1. pose proof dk_lin as (_ & _ & _ & _ & _ & _ & _ & _ & SH0 & _ & _ & _ & SM01). pose proof dk_geo as (G1 & G2 & G3 & _).
  pose proof alloc_ceiling_range as ACR.
  destruct AOK as (_ & _ & SEPB & _ & _ & _ & LO2 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & NZF & NZS). unfold CEILING in LO2.
  destruct SEPB as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & IS & IT & IFB & ITT & IL16 & IL4). unfold img_apartA, DSTATE_SIZE in *.
  unfold W14, blk_ivls, DSTATE_SIZE. destruct SM01 as [E|E]; rewrite E; cbn [Z.eqb app disjoint_from].
  - pose proof (ITT (NZF E)) as B. clear - A0 A1 IS IT IFB B SH0 G1 LO2 ACR. repeat split; lia.
  - destruct (NZS E) as [N16 N4]. pose proof (IL16 N16) as B1. pose proof (IL4 N4) as B2. clear - A0 A1 IS IT IFB B1 B2 SH0 G1 LO2 ACR. repeat split; lia.
Qed.

Lemma dk_aconsts : forall Σ m0 (m : mem), ART RT Σ m0 -> munch (W14 A) m0 m -> aconsts B0C m.
Proof.
  intros Σ m0 m ART0 MU. destruct (fs_aconsts_of_art RT AF Σ m0 ART0) as [[C1 C2] _]. cbn [aci_segs aci_got_sh aci_shvar aci_c CmpCut.ci_segs B0C] in C1, C2.
  split; cbn [aci_segs aci_got_sh aci_shvar aci_c CmpCut.ci_segs B0C].
  - apply (ro_cells_transport b0segs _ m0 m _ _ C1 MU). cbn [cells_size csize Nat.add]. apply dk_w14_img; clear; lia.
  - apply (ro_cells_transport b0segs _ m0 m _ _ C2 MU). cbn [cells_size csize Nat.add]. apply dk_w14_img; clear; lia.
Qed.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma dk_outD : forall (WD : list (Z * Z)) x, (forall lo hi, In (lo, hi) WD -> S <= lo /\ hi <= S + 64144) -> (x < S \/ S + 64144 <= x) -> outside WD x.
Proof.
  induction WD as [|[l h] WD IH]; intros x HW Hx; cbn [outside]; [exact I|].
  destruct (HW l h (or_introl eq_refl)) as [B0 B1]. split; [clear - B0 B1 Hx; lia|].
  apply IH; [intros lo hi Hi; exact (HW lo hi (or_intror Hi))| exact Hx].
Qed.
Lemma dk_out_app : forall (W1 W2 : list (Z * Z)) x, outside W1 x -> outside W2 x -> outside (W1 ++ W2) x.
Proof.
  induction W1 as [|[l h] W1 IH]; intros W2 x H1 H2; cbn [outside app] in *; [exact H2|].
  destruct H1 as [A1 B1]. split; [exact A1| exact (IH W2 x B1 H2)].
Qed.

Lemma dk_xferW : forall (WD : list (Z * Z)) lfr (m m' : mem), munch (WD ++ [(a_P A - lfr, a_P A)]) m m' ->
  (forall lo hi, In (lo, hi) WD -> S <= lo /\ hi <= S + 64144) -> 0 <= lfr <= 256 ->
  agree_on (fun x => dfp cx x /\ outside WD x) m m' /\
  agree_on (fun x => 0x10000 <= x < BIHI0) m m' /\
  (forall a cs, a_P A <= a -> rw_cells b0segs m a cs -> rw_cells b0segs m' a cs) /\
  (aframe A m -> aframe A m').
Proof.
  intros WD lfr m m' MU HW Hfr. pose proof dk_lin as (S0 & S1 & _ & _ & _ & _ & FB0 & FB1 & SH0 & SH1 & _). pose proof dk_geo as (G1 & G2 & G3 & _).
  pose proof dk_fsep as (F1 & F2). pose proof alloc_ceiling_range as ACR.
  assert (LOI : BIHI0 <= a_lo A) by (destruct AOK as (_ & _ & _ & _ & _ & _ & LO2 & _); unfold CEILING in LO2; clear - LO2 ACR; lia).
  assert (AG : agree_on (fun x => outside WD x /\ (x < a_P A - lfr \/ a_P A <= x)) m m').
  { apply (agree_of_nmunch _ m m' _ MU). intros x Hx. cbv beta in Hx. destruct Hx as [O R]. apply dk_out_app; [exact O|]. cbn [outside]. split; [clear - R; lia| exact I]. }
  assert (XO : forall x, (x < S \/ S + 64144 <= x) -> (x < a_P A - 256 \/ a_P A <= x) -> outside WD x /\ (x < a_P A - lfr \/ a_P A <= x)).
  { intros x H1 H2. split; [exact (dk_outD WD x HW H1)| clear - H2 Hfr; lia]. }
  split; [| split; [| split]].
  - eapply agree_sub; [exact AG|]. intros x Hx. cbv beta in Hx |- *. destruct Hx as [Dx Ox]. split; [exact Ox|]. pose proof (dk_dfp_lo x Dx) as DL. clear - DL G1 Hfr. lia.
  - eapply agree_sub; [exact AG|]. intros x Hx. cbv beta in Hx |- *. apply XO; clear - Hx HIS LOI G1; lia.
  - intros a cs PA H. apply (n_rw_cells_agree b0segs m m' _ _ H). eapply agree_sub; [exact AG|]. intros x Hx. cbv beta in Hx |- *. apply XO; clear - Hx PA S1 G1; lia.
  - intros (zt & ng & jg & j24 & pos & j38 & fl & GEO & NG & FLP & FRM & FRT & FF & FS).
    exists zt, ng, jg, j24, pos, j38, fl. split; [exact GEO|]. split; [exact NG|].
    split. { apply (n_ro_cells_agree b0segs m m' _ _ FLP). eapply agree_sub; [exact AG|]. intros x Hx. cbv beta in Hx |- *. cbn [cells_size csize Nat.add] in Hx. apply XO; clear - Hx F1 FB1 G1; lia. }
    split. { apply (n_rw_cells_agree b0segs m m' _ _ FRM). eapply agree_sub; [exact AG|]. intros x Hx. cbv beta in Hx |- *. apply XO; clear - Hx S1 G1; lia. }
    split. { apply (n_rw_cells_agree b0segs m m' _ _ FRT). eapply agree_sub; [exact AG|]. intros x Hx. cbv beta in Hx |- *. apply XO; clear - Hx S1 G1; lia. }
    split. { apply (n_rw_cells_agree b0segs m m' _ _ FF). eapply agree_sub; [exact AG|]. intros x Hx. cbv beta in Hx |- *. cbn [cells_size csize Nat.add] in Hx. apply XO; clear - Hx F1 FB1 G1; lia. }
    apply (n_rw_cells_agree b0segs m m' _ _ FS). eapply agree_sub; [exact AG|]. intros x Hx. cbv beta in Hx |- *. cbn [cells_size csize Nat.add] in Hx. apply XO; clear - Hx F2 SH1 OFFP; lia.
Qed.

(* [comment removed for export] *)
Lemma dk_dmem_img : forall (m m' : mem) g1 sv v v', dmem DI_B0 cx g1 sv (a_payload A) m v -> agree_on (fun x => 0x10000 <= x < BIHI0) m m' ->
  dmemL cx (a_payload A) m' v' -> dmem DI_B0 cx g1 sv (a_payload A) m' v'.
Proof.
  intros m m' g1 sv v v' DM AG (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9).
  pose proof DM as (_ & _ & _ & _ & _ & _ & _ & _ & _ & GOT & SEV & RN). b0img.
  unfold dmem. b0img. repeat (split; [assumption|]).
  split. { apply (n_ro_cells_agree b0segs m m' _ _ GOT). eapply agree_sub; [exact AG|]. intros x Hx. cbv beta in Hx |- *. cbn [cells_size csize Nat.add] in Hx. clear - Hx. lia. }
  split. { apply (n_ro_cells_agree b0segs m m' _ _ SEV). eapply agree_sub; [exact AG|]. intros x Hx. cbv beta in Hx |- *. cbn [cells_size csize Nat.add] in Hx. clear - Hx. lia. }
  apply (n_u32arr_agree b0segs m m' _ _ RN). eapply agree_sub; [exact AG|]. intros x Hx. cbv beta in Hx |- *. pose proof rnums_words_length as RNL. rewrite RNL in Hx. clear - Hx. lia.
Qed.

(* [comment removed for export] *)
Lemma dk_subW : forall (WD : list (Z * Z)) lfr m F fc, (forall lo hi, In (lo, hi) WD -> S <= lo /\ hi <= S + 64144) -> 0 <= lfr <= 256 ->
  sub_fp (WD ++ [(a_P A - lfr, a_P A)]) (W14 (AA m F fc)).
Proof.
  intros WD lfr m F fc HW Hfr x Ho. pose proof dk_geo as (_ & G2 & _). unfold W14, DSTATE_SIZE in Ho. cbn [dk_setm0 a_cx a_P a_sp a_fb a_shf outside app] in Ho.
  destruct Ho as (H1 & _ & H3 & _). apply dk_out_app; [apply (dk_outD WD x HW); clear - H1; lia|]. cbn [outside]. split; [clear - H3 G2 Hfr; lia| exact I].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma dec_mm : forall Σ m0 F0 fc0 Fu, INV Σ m0 ->
  B0F_cut_MMR (AA m0 F0 fc0) (QL Σ R0) Fu -> B0F_call_MM (AA m0 F0 fc0) (QL Σ R0) Fu.
Proof.
  intros Σ m0 F0 fc0 Fu IV HRET. pose proof IV as (SK & LV & CRE & ART0 & MI0 & PR0).
  unfold B0F_call_MM. intros until w752. intros DM FRL FRH AFR ST MU WM NMI DP DI FU.
  pose proof (dk_aconsts Σ m0 m ART0 MU) as AC.
  pose proof DI as (_ & _ & IU & _).
  eapply evt_cut.
  { eapply (B0F_mm_lift (AA m0 F0 fc0) (dk_aok m0 F0 fc0) (dk_ash Σ m0 F0 fc0 IV) HIS J _ s m); [exact DM| exact ST| exact MU| exact NMI| exact IU| exact AC]. }
  intros ms' PO. unfold B0F_leafCut.makeMaps_d_apostF in PO.
  destruct PO as (t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & -> & MUc & WMc & MIc & ST' & MID' & _ & S2U').
  pose proof dk_geo as (G1 & G2 & G3 & _).
  unfold B0F_leafCut.B0_FR_makeMaps_d in MUc, ST'. cbn [dk_setm0 a_P a_cx] in MUc, ST', MID', S2U'. rewrite (P_unsigned G) in MUc, ST'.
  rewrite (ret_pc_even 0xb00d8 ltac:(lia) eq_refl).
  dk_norm. change (aframe A m) in AFR.
  set (WD := [(S + 3192, S + 3196); (S + 3468, S + 3724)]).
  assert (HW : forall lo hi, In (lo, hi) WD -> S <= lo /\ hi <= S + 64144) by (intros lo hi [E|[E|[]]]; injection E as <- <-; clear; lia).
  destruct (dk_xferW WD 16 m m' MUc HW ltac:(clear; lia)) as (AG & AGI & XR & XA).
  assert (DM' : dmem DI_B0 cx (a_g1 A) (a_sv A) (a_payload A) m' (dvF cx J (makeMaps_d d) s)).
  { apply (dk_dmem_img m m' _ _ _ _ DM AGI).
    apply (dmx_mm cx _ m m' J d s dk_plen); [| exact dk_dsep| exact MID'| exact S2U'| exact (dmemL_of m cx _ _ _ _ DM)].
    eapply agree_sub; [exact AG|]. intros x Hx. cbv beta in Hx |- *. destruct Hx as [Dx Ox]. split; [exact Dx| exact Ox]. }
  unfold B0F_cut_MMR in HRET.
  eapply (HRET L d s J); cbn [dk_setm0 a_cx a_g1 a_sv a_payload a_m0 a_lo a_P a_sp a_b0 a_fb a_shf a_shs a_sht a_gp a_tp a_F a_fc];
    [exact DM'| exact (XR (a_P A) _ ltac:(clear; lia) FRL)| exact (XR (a_P A + 344) _ ltac:(clear; lia) FRH)| exact (XA AFR)| exact ST'
    | exact (munch_trans _ m0 m m' MU (munch_weaken _ _ m m' (dk_subW WD 16 m0 F0 fc0 HW ltac:(clear; lia)) MUc))| exact (wmono_trans b0segs m0 m m' WM WMc)| exact MIc
    | exact DP| exact DI| exact FU].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma dec_hbc : forall Σ m0 F0 fc0 Fu t mn mx, INV Σ m0 ->
  B0F_cut_HBCR (AA m0 F0 fc0) (QL Σ R0) Fu t mn mx -> B0F_call_HBC (AA m0 F0 fc0) (QL Σ R0) Fu t mn mx.
Proof.
  intros Σ m0 F0 fc0 Fu t mn mx IV HRET. pose proof IV as (SK & LV & CRE & ART0 & MI0 & PR0).
  unfold B0F_call_HBC. intros until w752. intros DM FRL FRH AFR ST MU WM NMI DP DI FU.
  pose proof (dk_aconsts Σ m0 m ART0 MU) as AC.
  (* [comment removed for export] *)
  pose proof DI as (COM & Ht & Hmm & SCAN & _). destruct COM as [SEL LALL]. destruct SEL as ((AL1 & AL2 & _) & NG & _).
  assert (Ha : 1 <= sv_alphaSize L <= 258) by (clear - AL1 AL2; lia).
  assert (Ht6 : 0 <= t < 6) by (clear - Ht NG; lia).
  assert (LALLt : forall j, 0 <= j < sv_alphaSize L -> 1 <= zget (d_len d) (258 * t + j) <= 20) by (intros j Hj; exact (LALL t j Ht Hj)).
  pose proof (rows_len_ok d t (sv_alphaSize L) mn mx Ht6 Ha SCAN LALLt) as HLEN.
  eapply evt_cut.
  { eapply (B0F_hbc_lift (AA m0 F0 fc0) (dk_aok m0 F0 fc0) (dk_ash Σ m0 F0 fc0 IV) HIS J _ s m t mn mx (sv_alphaSize L));
      [exact DM| exact ST| exact MU| exact NMI| exact Ht6| exact Ha| exact Hmm| exact HLEN| exact AC]. }
  intros ms' PO. unfold B0F_leafCut.hbCreateDecodeTables_apostF in PO.
  destruct PO as (t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & lws' & bws' & pws' & -> & MUc & WMc & MIc
      & ARL' & LNl' & ARB' & LNb' & ARP' & LNp' & _ & ST' & AGS).
  pose proof dk_geo as (G1 & G2 & G3 & _).
  unfold B0F_leafCut.hbCreate_W, B0F_leafCut.B0_FR_hbCreate in MUc, ST'. cbn [dk_setm0 a_P a_cx] in MUc, ST', ARL', ARB', ARP', AGS. rewrite (P_unsigned G) in MUc, ST'.
  rewrite (ret_pc_even 0xb131c ltac:(lia) eq_refl).
  dk_norm. change (aframe A m) in AFR.
  set (WD := [(S + 45436 + 1032 * t, S + 45436 + 1032 * t + 1032); (S + 51628 + 1032 * t, S + 51628 + 1032 * t + 1032); (S + 57820 + 1032 * t, S + 57820 + 1032 * t + 1032)]).
  assert (HW : forall lo hi, In (lo, hi) WD -> S <= lo /\ hi <= S + 64144) by (intros lo hi [E|[E|[E|[]]]]; injection E as <- <-; clear - Ht6; lia).
  destruct (dk_xferW WD 48 m m' MUc HW ltac:(clear; lia)) as (AG & AGI & XR & XA).
  assert (DM' : dmem DI_B0 cx (a_g1 A) (a_sv A) (a_payload A) m' (dvF cx J (mt_rows t (sv_alphaSize L) d mn mx) s)).
  { apply (dk_dmem_img m m' _ _ _ _ DM AGI).
    exact (dmx_rows cx _ m m' J d s t (sv_alphaSize L) mn mx lws' bws' pws' dk_plen AG dk_dsep Ha Ht6 Hmm SCAN LALLt
             ARL' LNl' ARB' LNb' ARP' LNp' AGS (dmemL_of m cx _ _ _ _ DM)). }
  unfold B0F_cut_HBCR in HRET.
  eapply (HRET L d s J); cbn [dk_setm0 a_cx a_g1 a_sv a_payload a_m0 a_lo a_P a_sp a_b0 a_fb a_shf a_shs a_sht a_gp a_tp a_F a_fc];
    [exact DM'| exact (XR (a_P A) _ ltac:(clear; lia) FRL)| exact (XR (a_P A + 344) _ ltac:(clear; lia) FRH)| exact (XA AFR)| exact ST'
    | exact (munch_trans _ m0 m m' MU (munch_weaken _ _ m m' (dk_subW WD 48 m0 F0 fc0 HW ltac:(clear; lia)) MUc))| exact (wmono_trans b0segs m0 m m' WM WMc)| exact MIc
    | exact DP| exact DI| exact FU].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma dec_idxn : forall Σ m0 F0 fc0 Fu fa fb j5 sym unz l16 l4, INV Σ m0 ->
  B0F_cut_IDXNR (AA m0 F0 fc0) (QL Σ R0) Fu fa fb j5 sym unz l16 l4 -> B0F_call_IDXN (AA m0 F0 fc0) (QL Σ R0) Fu fa fb j5 sym unz l16 l4.
Proof.
  intros Σ m0 F0 fc0 Fu fa fb j5 sym unz l16 l4 IV HRET. pose proof IV as (SK & LV & CRE & ART0 & MI0 & PR0).
  unfold B0F_call_IDXN. intros until w752. intros DM FRL FRH AFR ST MU WM NMI DP SMF FA FB ZA ZB DR0 FU.
  pose proof (dk_aconsts Σ m0 m ART0 MU) as AC.
  eapply evt_cut.
  { eapply (B0F_dec_U12SF.B0F_idx_lift (AA m0 F0 fc0) (dk_aok m0 F0 fc0) (dk_ash Σ m0 F0 fc0 IV) HIS J _ s m); [exact DM| exact ST| exact MU| exact NMI| exact AC]. }
  intros ms' PO. unfold B0F_leafCut.indexIntoF_apostF in PO.
  destruct PO as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & -> & MUc & WMc & MIc & ST' & _).
  pose proof dk_geo as (G1 & G2 & G3 & _).
  unfold B0F_leafCut.B0_FR_indexIntoF in MUc, ST'. cbn [dk_setm0 a_P] in MUc, ST'. rewrite (P_unsigned G) in MUc, ST'.
  rewrite (ret_pc_even 0xb3dc8 ltac:(lia) eq_refl).
  dk_norm. change (aframe A m) in AFR.
  assert (HW : forall lo hi, In (lo, hi) (@nil (Z * Z)) -> S <= lo /\ hi <= S + 64144) by (intros lo hi []).
  destruct (dk_xferW [] 16 m m' MUc HW ltac:(clear; lia)) as (AG & AGI & XR & XA).
  assert (DM' : dmem DI_B0 cx (a_g1 A) (a_sv A) (a_payload A) m' (dvF cx J (d_set_nused (d_set_tPos d (d_origPtr d)) 0) s)).
  { apply (dk_dmem_img m m' _ _ _ _ DM AGI). apply (dmemLF_agree cx _ m m' J _ s dk_plen); [| exact (dmemL_of m cx _ _ _ _ DM)].
    eapply agree_sub; [exact AG|]. intros x Hx. cbv beta in Hx |- *. split; [exact Hx| exact I]. }
  unfold B0F_cut_IDXNR in HRET.
  eapply (HRET L d s J); cbn [dk_setm0 a_cx a_g1 a_sv a_payload a_m0 a_lo a_P a_sp a_b0 a_fb a_shf a_shs a_sht a_gp a_tp a_F a_fc];
    [exact DM'| exact (XR (a_P A) _ ltac:(clear; lia) FRL)| exact (XR (a_P A + 344) _ ltac:(clear; lia) FRH)| exact (XA AFR)| exact ST'
    | exact (munch_trans _ m0 m m' MU (munch_weaken _ _ m m' (dk_subW [] 16 m0 F0 fc0 HW ltac:(clear; lia)) MUc))| exact (wmono_trans b0segs m0 m m' WM WMc)| exact MIc
    | exact DP| exact SMF| exact FA| exact FB| exact ZA| exact ZB| exact DR0| exact FU].
Qed.

Lemma dec_idxr : forall Σ m0 F0 fc0 Fu fa fb j5 sym unz l16 l4, INV Σ m0 ->
  B0F_cut_IDXRR (AA m0 F0 fc0) (QL Σ R0) Fu fa fb j5 sym unz l16 l4 -> B0F_call_IDXR (AA m0 F0 fc0) (QL Σ R0) Fu fa fb j5 sym unz l16 l4.
Proof.
  intros Σ m0 F0 fc0 Fu fa fb j5 sym unz l16 l4 IV HRET. pose proof IV as (SK & LV & CRE & ART0 & MI0 & PR0).
  unfold B0F_call_IDXR. intros until w752. intros DM FRL FRH AFR ST MU WM NMI DP SMF FA FB ZA ZB DR0 FU.
  pose proof (dk_aconsts Σ m0 m ART0 MU) as AC.
  eapply evt_cut.
  { eapply (B0F_dec_U12SF.B0F_idx_lift (AA m0 F0 fc0) (dk_aok m0 F0 fc0) (dk_ash Σ m0 F0 fc0 IV) HIS J _ s m); [exact DM| exact ST| exact MU| exact NMI| exact AC]. }
  intros ms' PO. unfold B0F_leafCut.indexIntoF_apostF in PO.
  destruct PO as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & -> & MUc & WMc & MIc & ST' & _).
  pose proof dk_geo as (G1 & G2 & G3 & _).
  unfold B0F_leafCut.B0_FR_indexIntoF in MUc, ST'. cbn [dk_setm0 a_P] in MUc, ST'. rewrite (P_unsigned G) in MUc, ST'.
  rewrite (ret_pc_even 0xb39d0 ltac:(lia) eq_refl).
  dk_norm. change (aframe A m) in AFR.
  assert (HW : forall lo hi, In (lo, hi) (@nil (Z * Z)) -> S <= lo /\ hi <= S + 64144) by (intros lo hi []).
  destruct (dk_xferW [] 16 m m' MUc HW ltac:(clear; lia)) as (AG & AGI & XR & XA).
  assert (DM' : dmem DI_B0 cx (a_g1 A) (a_sv A) (a_payload A) m' (dvF cx J (d_set_rTPos (d_set_rNToGo (d_set_nused (d_set_tPos d (d_origPtr d)) 0) 0) 0) s)).
  { apply (dk_dmem_img m m' _ _ _ _ DM AGI). apply (dmemLF_agree cx _ m m' J _ s dk_plen); [| exact (dmemL_of m cx _ _ _ _ DM)].
    eapply agree_sub; [exact AG|]. intros x Hx. cbv beta in Hx |- *. split; [exact Hx| exact I]. }
  unfold B0F_cut_IDXRR in HRET.
  eapply (HRET L d s J); cbn [dk_setm0 a_cx a_g1 a_sv a_payload a_m0 a_lo a_P a_sp a_b0 a_fb a_shf a_shs a_sht a_gp a_tp a_F a_fc];
    [exact DM'| exact (XR (a_P A) _ ltac:(clear; lia) FRL)| exact (XR (a_P A + 344) _ ltac:(clear; lia) FRH)| exact (XA AFR)| exact ST'
    | exact (munch_trans _ m0 m m' MU (munch_weaken _ _ m m' (dk_subW [] 16 m0 F0 fc0 HW ltac:(clear; lia)) MUc))| exact (wmono_trans b0segs m0 m m' WM WMc)| exact MIc
    | exact DP| exact SMF| exact FA| exact FB| exact ZA| exact ZB| exact DR0| exact FU].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma dec_idxn_all : forall Σ m F fc, INV Σ m -> forall Fu fa fb j5 sym unz l16 l4, B0F_call_IDXN (AA m F fc) (QL Σ R0) Fu fa fb j5 sym unz l16 l4.
Proof.
  intros Σ m F fc IV Fu fa fb j5 sym unz l16 l4. apply (dec_idxn Σ m F fc _ _ _ _ _ _ _ _ IV).
  apply (B0F_decMain.B0F_seg5N (AA m F fc) (dk_aok m F fc) (dk_ash Σ m F fc IV) (QL Σ R0) (dec_retc Σ m F fc IV)).
Qed.
Lemma dec_idxr_all : forall Σ m F fc, INV Σ m -> forall Fu fa fb j5 sym unz l16 l4, B0F_call_IDXR (AA m F fc) (QL Σ R0) Fu fa fb j5 sym unz l16 l4.
Proof.
  intros Σ m F fc IV Fu fa fb j5 sym unz l16 l4. apply (dec_idxr Σ m F fc _ _ _ _ _ _ _ _ IV).
  apply (B0F_decMain.B0F_seg5R (AA m F fc) (dk_aok m F fc) (dk_ash Σ m F fc IV) (QL Σ R0) (dec_retc Σ m F fc IV)).
Qed.
Lemma dec_seg4 : forall Σ m F fc, INV Σ m -> forall Fu, B0F_decMain.B0F_cuts4 (AA m F fc) (QL Σ R0) Fu.
Proof.
  intros Σ m F fc IV. apply (B0F_decMain.B0F_seg4 (AA m F fc) (dk_aok m F fc) (dk_ash Σ m F fc IV) (QL Σ R0) (dec_retc Σ m F fc IV)).
  - intros. apply dec_idxn_all. exact IV.
  - intros. apply dec_idxr_all. exact IV.
Qed.

Lemma dec_hbc_ind : forall k Σ m F fc, INV Σ m -> forall Fu t mn mx, 6 - Z.of_nat k <= t -> B0F_call_HBC (AA m F fc) (QL Σ R0) Fu t mn mx.
Proof.
  induction k as [|k IH]; intros Σ m F fc IV Fu t mn mx Ht.
  - unfold B0F_call_HBC. intros until w752. intros DM FRL FRH AFR ST MU WM NMI DP DI FU. exfalso.
    destruct DI as (COM & Ht' & _). destruct COM as [SEL _]. destruct SEL as (_ & NG & _). clear - Ht Ht' NG. lia.
  - apply (dec_hbc Σ m F fc Fu t mn mx IV).
    apply (B0F_dec_U7B.B0F_U7_C2 (AA m F fc) (dk_aok m F fc) (dk_ash Σ m F fc IV) (QL Σ R0) Fu t mn mx).
    apply (B0F_dec_U7C.B0F_U7_D (AA m F fc) (dk_aok m F fc) (dk_ash Σ m F fc IV) (QL Σ R0) Fu (proj1 (dec_seg4 Σ m F fc IV Fu)) t).
    apply (B0F_dec_U7C.B0F_U7_T (AA m F fc) (dk_aok m F fc) (dk_ash Σ m F fc IV) (QL Σ R0) Fu (t + 1)). intros mn' mx'.
    apply (B0F_dec_U7B.B0F_U7_C1 (AA m F fc) (dk_aok m F fc) (QL Σ R0) Fu (t + 1) mn' mx'). apply (IH Σ m F fc IV). clear - Ht. lia.
Qed.
Lemma dec_hbc_all : forall Σ m F fc, INV Σ m -> forall Fu t mn mx, B0F_call_HBC (AA m F fc) (QL Σ R0) Fu t mn mx.
Proof. intros Σ m F fc IV Fu t mn mx. apply (dec_hbc_ind (Z.to_nat (6 - t)) Σ m F fc IV). lia. Qed.

Lemma dec_seg2 : forall Σ m F fc, INV Σ m -> forall Fu, B0F_decMain.B0F_cuts2 (AA m F fc) (QL Σ R0) Fu.
Proof.
  intros Σ m F fc IV. apply (B0F_decMain.B0F_seg2 (AA m F fc) (dk_aok m F fc) (dk_ash Σ m F fc IV) (QL Σ R0) (dec_retc Σ m F fc IV)).
  intros. apply dec_hbc_all. exact IV.
Qed.
Lemma dec_mm_all : forall Σ m F fc, INV Σ m -> forall Fu, B0F_call_MM (AA m F fc) (QL Σ R0) Fu.
Proof. intros Σ m F fc IV Fu. apply (dec_mm Σ m F fc Fu IV). exact (proj1 (dec_seg2 Σ m F fc IV Fu)). Qed.

(* [comment removed for export] *)
Theorem dec_H14 : forall Σ m F fc, INV Σ m -> forall Fu, B0F_cut_H14 (AA m F fc) (QL Σ R0) Fu.
Proof.
  intros Σ m F fc IV Fu.
  exact (proj1 (B0F_decMain.B0F_seg1 (AA m F fc) (dk_aok m F fc) (dk_ash Σ m F fc IV) (QL Σ R0) (dec_retc Σ m F fc IV) (dec_mm_all Σ m F fc IV) Fu)).
Qed.
End DECL2.
