(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.AS Require Import ShapeAlg.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.Lib Require Import ImageA RzCPS.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A Require Import Layout RT_iface D_defs D_kit I_read RT_liveprim RT_globals.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A Require Import Shadow.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A Require L_libA D_libiface.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.L2 Require Import L2Kit L2Act L2StmtD A0_fs_L2f A0_sessK A0F_decK A0F_decX A0F_dec_L2a.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require Import PropExec.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import Tac WalkLib SegsA0.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzModel BzTac BzTables CmpMem AsanKit AsanKit2 AsanCut.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzDefs BzInv BzContracts.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzArr BzCStream BzDState BzDBlock BzDK BzDU7 DecCutFA A0F_decV A0F_decRet A0F_decRet3 A0F_decCutsA A0F_decCuts4 A0F_decCuts5 A0F_decCuts6 A0F_decCuts7 A0F_decCutsM A0F_decCuts8 A0F_decCutsE A0F_decCuts12S.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzArr OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDState OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDBlock.BzDHuff OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDBlock OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDK OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDU7 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.DecCutFA OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.A0F_decV OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.A0F_decRet OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.A0F_decRet3 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.A0F_decCutsA OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.A0F_decCuts4 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.A0F_decCuts5 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.A0F_decCuts6 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.A0F_decCuts7 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.A0F_decCutsM OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.A0F_decCuts8 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.A0F_decCutsE OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.A0F_decCuts12S.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require A0F_decMain A0F_dec_U13b A0F_dec_epi A0F_dec_U12SF A0F_dec_U7B A0F_dec_U7C A0F_dec_U7D.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeil.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Open Scope Z_scope.
#[local] Notation mem := (word -> option byte).

Section DECL2.
Context {ACEIL__ : ACeil}.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Hypothesis AF_DRV : forall Σ m, ART RT Σ m -> drv_consts m.
Hypothesis MSET : memset_icontract RT e_asan_memset.
Hypothesis HBCC : hbCreateDecodeTables_contract RT.
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

Hypothesis AOK : act_ok AIHI0 A.
Hypothesis ATP : a_tp A = Z_to_bv 64 0x5fc0d8.
Hypothesis AG1 : a_g1 A = A0F_decK.DG1. Hypothesis ASV : a_sv A = A0F_decK.DSV.
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
Hypothesis ZSH0 : bytes_at a0segs mi (a_sht A) (repeat z8 10).
Hypothesis LIB0 : L_libA.LIB_A mi.
Hypothesis WCI : forall x, ~ outside Wc x -> (S <= x < S + 64144) \/ (b_strm cx <= x < b_strm cx + 20) \/ ~ outside (blk_ivls cx) x.
(* [comment removed for export] *)
Variable CR : Z.
Variable R0 : dres.
Definition INV (Σ : rts RT) (m : mem) : Prop :=
  SOK Σ /\ rt_live RT Σ = live0 /\ rt_credit RT Σ = CR /\ ART RT Σ m /\ KMem.mem_inv asegs m /\ PRESI m.
Hypothesis HK : forall c' (Σ2 : rts RT) (m' : mem) (rv : Z) (L : dsv) (d : dst) (s : dstrm) (J : jk)
    (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) F' fc',
  DRet rv L d s = R0 ->
  ASTA RT Σ2 PMc (eq (MS (mkR (a_ra A) (a_sp A) (a_gp A) (a_tp A) t0 t1 t2 (a_s0 A) (a_s1 A) (Z_to_bv 64 rv) a1 a2 a3 a4 a5 a6 a7
                              (a_s2 A) (a_s3 A) (a_s4 A) (a_s5 A) (a_s6 A) (a_s7 A) (a_s8 A) (a_s9 A) (a_s10 A) (a_s11 A) t3 t4 t5 t6)
                         F' (ret_pc (a_ra A)) fc' None m' (seg_rom a0segs))) c' ->
  rt_frames RT Σ2 = fr -> rt_live RT Σ2 = live0 -> rt_sp0 RT Σ2 = sp0 -> rt_credit RT Σ2 = CR ->
  ART RT Σ2 m' -> KMem.mem_inv asegs m' -> stk asegs m' (a_lo A) (a_usp A) -> PRESI m' ->
  dmem DI_A0 cx (a_g1 A) (a_sv A) (a_payload A) m' (dvF cx J (d_set_sv d L) s) ->
  dpureF cx (a_b0 A) (a_payload A) J (d_set_sv d L) s -> dpost14 (d_set_sv d L) ->
  realizes asegs c' T.
(* [comment removed for export] *)
Hypothesis KLIB : forall m, PRESI m -> L_libA.LIB_A m.
Hypothesis KZSH : forall m, PRESI m -> bytes_at a0segs m (a_sht A) (repeat z8 10).
Hypothesis OFFT : b_strm cx + 80 <= 0x7fff7000 \/ 0x10007fff8000 <= b_strm cx.
Hypothesis OFFF : a_fb A + 64 <= 0x7fff7000 \/ 0x10007fff8000 <= a_fb A.
Hypothesis OFFP : 0x10007fff8000 <= a_P A - 256.
Hypothesis USPT : a_usp A <= 2^47.
Hypothesis HIS : AIHI0 <= S.
Hypothesis ACE : alloc_ceiling = sp0 - STACK_WIN.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Notation AA m F fc := (dk_setm0 A m F fc).
Ltac dk_norm := cbn [dk_setm0 a_cx a_g1 a_sv a_payload a_m0 a_lo a_P a_sp a_b0 a_h0 a_fb a_shf a_shs a_sht a_gp a_tp a_F a_fc a_ra a_s0 a_s1 a_s2 a_s3 a_s4 a_s5 a_s6 a_s7 a_s8 a_s9 a_s10 a_s11] in *.

Lemma dk_aok : forall m F fc, act_ok AIHI0 (AA m F fc).
Proof. intros. apply act_ok_setm0. exact AOK. Qed.

Lemma dk_ash : forall Σ m F fc, INV Σ m -> act_sh DI_A0 (AA m F fc).
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

Lemma dk_agree : forall Σ W (m m' : mem), SOK Σ -> rt_live RT Σ = live0 ->
  rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) (a_P A) W m m' -> agree_on (fun x => dfp cx x /\ outside W x) m m'.
Proof.
  intros Σ W m m' SK LV STEP. apply (agree_of_pres_fp _ _ _ W m m' _ STEP). intros x [D O]. split; [exact (dk_acl Σ x SK LV D)| exact O].
Qed.

(* [comment removed for export] *)
Lemma dk_dmem : forall Σ (m : mem) v, ART RT Σ m -> PRESI m -> dmemL cx (a_payload A) m v -> dmem DI_A0 cx (a_g1 A) (a_sv A) (a_payload A) m v.
Proof. intros Σ m v ART0 PR H. rewrite AG1, ASV. exact (dmem_of_L RT AF AF_DRV Σ m cx _ v ART0 (KLIB m PR) H). Qed.

Lemma dk_ro_C8_inj : forall (m : mem) a w w', ro_cells a0segs m a [C8 w] -> ro_cells a0segs m a [C8 w'] -> w = w'.
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
Lemma dec_flag : forall Σ m F fc, INV Σ m -> A0F_FLAG (AA m F fc) (QL Σ R0).
Proof.
  intros Σ m0 F0 fc0 (SK & LV & CRE & ART0 & MI0 & PR0).
  unfold A0F_FLAG. intros until j38. intros DM FRL FRH GEO NG FLP FRM FRT FF FS ST MU WM NMI DP DPO.
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
  eapply (A0F_dec_epi.A0F_rel_flag _ m fl' (Z_to_bv 8 1)); [exact FLC| exact (kmem_inv_N _ _ MI1)|].
  intros m2 FLC2 NMI2 MU2 WM2. apply evt_done. intros c2 Hc2.
  destruct (REL m2 MU2 WM2 FLC2 MI1 NMI2 ST PR1) as (ART2 & FRS2 & LV2 & SP2 & CR2 & AL2 & AM2 & MI2 & ST2 & PR2).
  (* [comment removed for export] *)
  assert (DM2 : dmem DI_A0 cx (a_g1 A) (a_sv A) (a_payload A) m2 (dvF cx J (d_set_sv d L) s)).
  { apply (dk_dmem Σ2 m2 _ ART2 PR2). apply (dmemLF_agree cx _ m m2 J _ s dk_plen); [| exact (dmemL_of m cx _ _ _ _ DM)].
    apply (agree_of_nmunch [(fl', fl' + 1)] m m2 _ MU2). intros x Hx. cbn [outside]. split; [| exact I].
    assert (C : cls RT (a_P A) Σ x 1) by (intros y Hy; replace y with x by (clear - Hy; lia); exact (dk_acl Σ x SK LV Hx)).
    pose proof (FLD x 1 C) as D. clear - D. lia. }
  clear DM ST. unfold FT_REGS in FRT. dk_norm.
  xfer_fl G SK FLD m m2 MU2 WM2.
  pose proof (ASTA_switch RT Σ Σ2 PMc _ c2 Hc2 AL2 AM2) as Hc2'. clear Hc2.
  (* [comment removed for export] *)
  eapply (l1_realizes RT AF Σ2 PMc _ T c2 MST Hc2').
  eapply (A0F_dec_epi.A0F_epi (AA m0 F0 fc0) _ m2 _ _ zt ng jg); dk_norm; [exact GEO| exact NG| clear - LO1; lia| exact FRL| exact FRM| exact FRH| exact FRT| exact ST2|].
  intros STu. apply evt_done. intros c3 Hc3.
  eapply (HK c3 Σ2 m2 rv L d s J); [exact ER| exact Hc3| exact FRS2| rewrite LV2; exact LV| exact SP2| rewrite CR2; exact CRE| exact ART2| exact MI2| exact STu| exact PR2| exact DM2| exact DP| exact DPO].
Qed.

Lemma dec_retc : forall Σ m F fc, INV Σ m -> A0F_RETC (AA m F fc) (QL Σ R0).
Proof. intros Σ m F fc IV. apply (A0F_dec_U13b.A0F_dec_retA (AA m F fc) (dk_aok m F fc) (dk_ash Σ m F fc IV)). exact (dec_flag Σ m F fc IV). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma dk_geo : a_lo A + 256 <= a_P A /\ a_P A + 832 <= a_usp A /\ a_usp A <= a_P A + 848 /\ S + 64144 <= a_lo A /\ 0 < S.
Proof.
  destruct AOK as (LINB & _ & _ & _ & _ & _ & LO2 & LO1 & _ & GEO & _). cbv zeta in LINB. destruct LINB as (S0 & SCE & _). unfold DSTATE_SIZE, CEILING in *.
  clear - S0 SCE LO2 LO1 GEO. lia.
Qed.
Lemma dk_fsep : (a_fb A + 64 <= S \/ S + 64144 <= a_fb A) /\ (a_shf A + 8 <= S \/ S + 64144 <= a_shf A).
Proof.
  destruct AOK as (_ & _ & SEPB & _). destruct SEPB as (_ & _ & _ & _ & _ & _ & DFS & _ & _ & _ & DSS & _). unfold disj, DSTATE_SIZE in DFS, DSS. clear - DFS DSS. lia.
Qed.

(* [comment removed for export] *)
Lemma dk_dj : forall W, (forall lo hi, In (lo, hi) W -> S <= lo /\ hi <= S + 64144) ->
  disjoint_from W (a_P A) (a_usp A - a_P A) /\ disjoint_from W (a_fb A) 64 /\ disjoint_from W (a_shf A) 8.
Proof.
  intros W HW. pose proof dk_geo as (G1 & G2 & G3 & G4 & G5). pose proof dk_fsep as (F1 & F2).
  induction W as [|[l h] W IH]; cbn [disjoint_from]; [repeat split; exact I|].
  destruct (HW l h (or_introl eq_refl)) as [B0 B1]. destruct (IH (fun lo hi H => HW lo hi (or_intror H))) as (I1 & I2 & I3).
  repeat split; try assumption; clear - B0 B1 G1 G2 G3 G4 G5 F1 F2; lia.
Qed.

(* [comment removed for export] *)
Lemma dk_frames : forall Σ Σ' W (m m' : mem) (a1 a2 : Z) (cs1 cs2 : list cell),
  SOK Σ -> SOK Σ' -> rt_live RT Σ' = rt_live RT Σ -> rt_frames RT Σ' = rt_frames RT Σ -> ART RT Σ' m' ->
  rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) (a_P A) W m m' ->
  (forall lo hi, In (lo, hi) W -> S <= lo /\ hi <= S + 64144) ->
  a_P A <= a1 -> a1 + Z.of_nat (cells_size cs1) <= a_usp A -> a_P A <= a2 -> a2 + Z.of_nat (cells_size cs2) <= a_usp A ->
  rw_cells a0segs m a1 cs1 -> rw_cells a0segs m a2 cs2 -> aframe A m ->
  rw_cells a0segs m' a1 cs1 /\ rw_cells a0segs m' a2 cs2 /\ aframe A m'.
Proof.
  intros Σ Σ' W m m' a1 a2 cs1 cs2 SK SK' LV' FR' ART' STEP HW A1 B1 A2 B2 C1 C2 AFR.
  destruct (dk_dj W HW) as (DJP & DJF & DJS).
  assert (STEP' : rt_pres_fp (rt_live RT Σ') (rt_frames RT Σ') (a_P A) W m m') by (rewrite LV', FR'; exact STEP).
  split; [exact (dec_rframe_xfer RT _ _ _ _ _ _ _ _ _ G Σ _ m m' a1 cs1 STEP DJP A1 B1 C1)|].
  split; [exact (dec_rframe_xfer RT _ _ _ _ _ _ _ _ _ G Σ _ m m' a2 cs2 STEP DJP A2 B2 C2)|].
  exact (dec_aframe_xfer RT AF _ _ _ _ _ _ _ _ _ G A eq_refl eq_refl eq_refl eq_refl Σ' _ m m' mi SK' ART' STEP' DJP DJF DJS AFR).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma dec_msi : forall Σ m0 F0 fc0, INV Σ m0 ->
  (forall m2 F2 fc2, INV Σ m2 -> forall Fu, A0F_cut_MSIR (AA m2 F2 fc2) (QL Σ R0) Fu) ->
  forall Fu, A0F_call_MSI (AA m0 F0 fc0) (QL Σ R0) Fu.
Proof.
  intros Σ m0 F0 fc0 (SK & LV & CRE & ART0 & MI0 & PR0) HNEXT Fu.
  unfold A0F_call_MSI. intros until w720. intros DM FRL FRH AFR ST MU WM NMI DP DI FU.
  apply evt_done. intros ER c1 Hc1. dk_norm. change (aframe A m) in AFR.
  destruct (after_l1_leaf AF G Σ (W14 (AA m0 F0 fc0)) 256 m0 m SK ART0 MI0 PR0 NMI MU WM ltac:(clear; lia) ROOM W14C) as (ART1 & MI1 & PR1 & _).
  assert (SLIV : In (S, 64144) (rt_live RT Σ)) by (rewrite LV; exact SLIV0).
  pose proof (af_live_range RT AF Σ m _ _ ART1 SLIV) as (SL0 & SL1 & _). pose proof (af_sp0_range RT AF Σ m ART1) as (_ & SP0T). unfold USTACK_TOP, STACK_WIN in *.
  rewrite ATP in Hc1.
  eapply (memset_call G PMc FDO MST Σ (S + 3196) 256 z8 m); [exact MSET| exact SK| clear - SL0 SL1 SP0T; lia| clear; lia| | exact ART1| exact MI1| exact ST| exact Hc1|].
  { apply (cdst_live AF G Σ m S 64144 _ 256 ART1 SLIV); clear; lia. }
  clear Hc1. intros c2 m2 u0 u1 u2 e1 e2 e3 e4 e5 e6 e7 u3 u4 u5 u6 F2 fc2 Hc2 ART2 MI2 ST2 WM2 BY2 STEP2.
  pose proof (pres_step G Σ _ m m2 SK PR1 STEP2 ltac:(per_interval; right; apply DSC; lia)) as PR2.
  rewrite (KMState.ret_pc_even 0xa3fd8 ltac:(lia) eq_refl) in Hc2.
  pose proof dk_geo as (G1 & G2 & G3 & _).
  lazymatch type of STEP2 with rt_pres_fp _ _ _ ?W _ _ => lazymatch type of FRL with rw_cells _ _ ?a1 ?cs1 => lazymatch type of FRH with rw_cells _ _ ?a2 ?cs2 =>
    destruct (dk_frames Σ Σ W m m2 a1 a2 cs1 cs2 SK SK eq_refl eq_refl ART2 STEP2 ltac:(intros lo hi [E|[]]; injection E as <- <-; clear; lia)
                ltac:(clear; lia) ltac:(cbn [cells_size csize Nat.add]; clear - G2; lia) ltac:(clear; lia) ltac:(cbn [cells_size csize Nat.add]; clear - G2; lia) FRL FRH AFR)
      as (FRL2 & FRH2 & AFR2) end end end.
  assert (DM2 : dmem DI_A0 cx (a_g1 A) (a_sv A) (a_payload A) m2 (dvF cx J (d_set_inUse d (clear256 256 0 iu)) s)).
  { apply (dk_dmem Σ m2 _ ART2 PR2). exact (dmx_inUse cx _ m m2 J d s iu dk_plen (dk_agree Σ _ m m2 SK LV STEP2) WM2 dk_dsep BY2 (dmemL_of m cx _ _ _ _ DM)). }
  rewrite <- ATP in Hc2.
  eapply (l1_realizes RT AF Σ PMc _ T c2 MST Hc2).
  eapply evt_mono; [| intros ms' HQ; exact (HQ ER)].
  pose proof (HNEXT m2 F2 fc2 (conj SK (conj LV (conj CRE (conj ART2 (conj MI2 PR2))))) Fu) as HN. unfold A0F_cut_MSIR in HN.
  eapply (HN L d s J iu); cbn [dk_setm0 a_cx a_g1 a_sv a_payload a_m0 a_lo a_P a_sp a_b0 a_fb a_shf a_shs a_sht a_gp a_tp a_F a_fc];
    [exact DM2| exact FRL2| exact FRH2| exact AFR2| exact ST2| apply munch_refl| apply wmono_refl| exact (kmem_inv_N _ _ MI2)| exact DP| exact DI| exact FU].
Qed.

Lemma dec_msu : forall Σ m0 F0 fc0, INV Σ m0 ->
  (forall m2 F2 fc2, INV Σ m2 -> forall Fu, A0F_cut_MSUR (AA m2 F2 fc2) (QL Σ R0) Fu) ->
  forall Fu, A0F_call_MSU (AA m0 F0 fc0) (QL Σ R0) Fu.
Proof.
  intros Σ m0 F0 fc0 (SK & LV & CRE & ART0 & MI0 & PR0) HNEXT Fu.
  unfold A0F_call_MSU. intros until w720. intros DM FRL FRH AFR ST MU WM NMI DP DI FU.
  apply evt_done. intros ER c1 Hc1. dk_norm. change (aframe A m) in AFR.
  destruct (after_l1_leaf AF G Σ (W14 (AA m0 F0 fc0)) 256 m0 m SK ART0 MI0 PR0 NMI MU WM ltac:(clear; lia) ROOM W14C) as (ART1 & MI1 & PR1 & _).
  assert (SLIV : In (S, 64144) (rt_live RT Σ)) by (rewrite LV; exact SLIV0).
  pose proof (af_live_range RT AF Σ m _ _ ART1 SLIV) as (SL0 & SL1 & _). pose proof (af_sp0_range RT AF Σ m ART1) as (_ & SP0T). unfold USTACK_TOP, STACK_WIN in *.
  rewrite ATP in Hc1.
  eapply (memset_call G PMc FDO MST Σ (S + 68) 1024 z8 m); [exact MSET| exact SK| clear - SL0 SL1 SP0T; lia| clear; lia| | exact ART1| exact MI1| exact ST| exact Hc1|].
  { apply (cdst_live AF G Σ m S 64144 _ 1024 ART1 SLIV); clear; lia. }
  clear Hc1. intros c2 m2 u0 u1 u2 e1 e2 e3 e4 e5 e6 e7 u3 u4 u5 u6 F2 fc2 Hc2 ART2 MI2 ST2 WM2 BY2 STEP2.
  pose proof (pres_step G Σ _ m m2 SK PR1 STEP2 ltac:(per_interval; right; apply DSC; lia)) as PR2.
  rewrite (KMState.ret_pc_even 0xa51c0 ltac:(lia) eq_refl) in Hc2.
  pose proof dk_geo as (G1 & G2 & G3 & _).
  lazymatch type of STEP2 with rt_pres_fp _ _ _ ?W _ _ => lazymatch type of FRL with rw_cells _ _ ?a1 ?cs1 => lazymatch type of FRH with rw_cells _ _ ?a2 ?cs2 =>
    destruct (dk_frames Σ Σ W m m2 a1 a2 cs1 cs2 SK SK eq_refl eq_refl ART2 STEP2 ltac:(intros lo hi [E|[]]; injection E as <- <-; clear; lia)
                ltac:(clear; lia) ltac:(cbn [cells_size csize Nat.add]; clear - G2; lia) ltac:(clear; lia) ltac:(cbn [cells_size csize Nat.add]; clear - G2; lia) FRL FRH AFR)
      as (FRL2 & FRH2 & AFR2) end end end.
  assert (DM2 : dmem DI_A0 cx (a_g1 A) (a_sv A) (a_payload A) m2 (dvF cx J (d_set_unzftab d (clear256 256 0 (d_unzftab d))) s)).
  { apply (dk_dmem Σ m2 _ ART2 PR2). exact (dmx_unzftab cx _ m m2 J d s dk_plen (dk_agree Σ _ m m2 SK LV STEP2) WM2 dk_dsep BY2 (dmemL_of m cx _ _ _ _ DM)). }
  rewrite <- ATP in Hc2.
  eapply (l1_realizes RT AF Σ PMc _ T c2 MST Hc2).
  eapply evt_mono; [| intros ms' HQ; exact (HQ ER)].
  pose proof (HNEXT m2 F2 fc2 (conj SK (conj LV (conj CRE (conj ART2 (conj MI2 PR2))))) Fu) as HN. unfold A0F_cut_MSUR in HN.
  eapply (HN L d s J); cbn [dk_setm0 a_cx a_g1 a_sv a_payload a_m0 a_lo a_P a_sp a_b0 a_fb a_shf a_shs a_sht a_gp a_tp a_F a_fc];
    [exact DM2| exact FRL2| exact FRH2| exact AFR2| exact ST2| apply munch_refl| apply wmono_refl| exact (kmem_inv_N _ _ MI2)| exact DP| exact DI| exact FU].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma dec_hbc : forall Σ m0 F0 fc0 Fu t mn mx, INV Σ m0 ->
  (forall Σ2 m2 F2 fc2, INV Σ2 m2 -> A0F_cut_HBCR (AA m2 F2 fc2) (QL Σ2 R0) Fu t mn mx) ->
  A0F_call_HBC (AA m0 F0 fc0) (QL Σ R0) Fu t mn mx.
Proof.
  intros Σ m0 F0 fc0 Fu t mn mx (SK & LV & CRE & ART0 & MI0 & PR0) HNEXT.
  unfold A0F_call_HBC. intros until w720. intros DM FRL FRH AFR ST MU WM NMI DP DI FU.
  apply evt_done. intros ER c1 Hc1. dk_norm. change (aframe A m) in AFR.
  destruct (after_l1_leaf AF G Σ (W14 (AA m0 F0 fc0)) 256 m0 m SK ART0 MI0 PR0 NMI MU WM ltac:(clear; lia) ROOM W14C) as (ART1 & MI1 & PR1 & _).
  assert (SLIV : In (S, 64144) (rt_live RT Σ)) by (rewrite LV; exact SLIV0).
  (* [comment removed for export] *)
  pose proof DI as (COM & Ht & Hmm & SCAN & _). destruct COM as [SEL LALL]. destruct SEL as ((AL1 & AL2 & _) & NG & _).
  assert (Ha : 1 <= sv_alphaSize L <= 258) by (clear - AL1 AL2; lia).
  assert (Ht6 : 0 <= t < 6) by (clear - Ht NG; lia).
  assert (LALLt : forall j, 0 <= j < sv_alphaSize L -> 1 <= zget (d_len d) (258 * t + j) <= 20) by (intros j Hj; exact (LALL t j Ht Hj)).
  destruct (dmx_rows_pre cx _ m J d s t Ht6 (dmemL_of m cx _ _ _ _ DM)) as (RL & NL & RB & NB & RP & NP & R8 & N8).
  pose proof (rows_len_ok d t (sv_alphaSize L) mn mx Ht6 Ha SCAN LALLt) as HLEN.
  assert (S16 : S mod 16 = 0) by (destruct AOK as (_ & AL & _); exact (proj1 AL)).
  pose proof G as [_ _ _ _ GLOW GLOR GPUS GSPT GSPA _ _ _ _ _].
  pose proof (proj1 (proj2 SK)) as SP0E.
  rewrite ATP in Hc1.
  refine (cps_realizes asegs _ _ T c1 (HBCC Σ PMc _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m S t (rows_lws d t) (rows_bws d t) (rows_pws d t) (rows_lbs d t)
            mn mx (sv_alphaSize L) (a_lo A) FDO MST eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl ltac:(rewrite SP0E; exact ACE)
            RL NL RB NB RP NP R8 N8 SLIV S16 Ht6 ART1 MI1 ltac:(rewrite (P_unsigned G); exact ST) ltac:(rewrite SP0E; exact GLOW)
            ltac:(rewrite (P_unsigned G); clear - ROOM; lia) ltac:(rewrite (P_unsigned G); clear - GSPT GPUS; lia) ltac:(rewrite (P_unsigned G); exact GSPA)
            Ha Hmm HLEN) Hc1 _).
  clear Hc1. intros c2 (Σ' & Hq & LV' & FR' & SP' & CR').
  destruct (ASTA_unpack RT Σ' _ _ c2 Hq) as (ms2 & (m2 & u0 & u1 & u2 & e0 & e1 & e2 & e3 & e4 & e5 & e6 & e7 & u3 & u4 & u5 & u6 & F2 & fc2 & lws' & bws' & pws'
      & -> & ART2 & MI2 & ST2 & ARL' & LNl' & ARB' & LNb' & ARP' & LNp' & AGS & STEP2) & Hc2).
  clear Hq. rewrite (P_unsigned G) in ST2, STEP2.
  rewrite (ret_pc_even 0xa5124 ltac:(lia) eq_refl) in Hc2.
  destruct (after_call G Σ Σ' _ m m2 SK LV' FR' SP' PR1 STEP2 ltac:(per_interval; right; apply DSC; match goal with HX : _ <= _ < _ |- _ => clear - HX Ht6; lia end)) as (SK' & PR2).
  pose proof dk_geo as (G1 & G2 & G3 & _).
  lazymatch type of STEP2 with rt_pres_fp _ _ _ ?W _ _ => lazymatch type of FRL with rw_cells _ _ ?a1 ?cs1 => lazymatch type of FRH with rw_cells _ _ ?a2 ?cs2 =>
    destruct (dk_frames Σ Σ' W m m2 a1 a2 cs1 cs2 SK SK' LV' FR' ART2 STEP2 ltac:(intros lo hi [E|[E|[E|[]]]]; injection E as <- <-; clear - Ht6; lia)
                ltac:(clear; lia) ltac:(cbn [cells_size csize Nat.add]; clear - G2; lia) ltac:(clear; lia) ltac:(cbn [cells_size csize Nat.add]; clear - G2; lia) FRL FRH AFR)
      as (FRL2 & FRH2 & AFR2) end end end.
  assert (LV2 : rt_live RT Σ' = live0) by (rewrite LV'; exact LV).
  assert (CRE2 : rt_credit RT Σ' = CR) by (rewrite CR'; exact CRE).
  assert (DM2 : dmem DI_A0 cx (a_g1 A) (a_sv A) (a_payload A) m2 (dvF cx J (mt_rows t (sv_alphaSize L) d mn mx) s)).
  { apply (dk_dmem Σ' m2 _ ART2 PR2).
    exact (dmx_rows cx _ m m2 J d s t (sv_alphaSize L) mn mx lws' bws' pws' dk_plen (dk_agree Σ _ m m2 SK LV STEP2) dk_dsep Ha Ht6 Hmm SCAN LALLt
             ARL' LNl' ARB' LNb' ARP' LNp' AGS (dmemL_of m cx _ _ _ _ DM)). }
  rewrite <- ATP in Hc2.
  eapply (l1_realizes RT AF Σ' PMc _ T c2 MST Hc2).
  eapply evt_mono; [| intros ms' HQ; exact (HQ ER)].
  pose proof (HNEXT Σ' m2 F2 fc2 (conj SK' (conj LV2 (conj CRE2 (conj ART2 (conj MI2 PR2)))))) as HN. unfold A0F_cut_HBCR in HN.
  eapply (HN L d s J); cbn [dk_setm0 a_cx a_g1 a_sv a_payload a_m0 a_lo a_P a_sp a_b0 a_fb a_shf a_shs a_sht a_gp a_tp a_F a_fc];
    [exact DM2| exact FRL2| exact FRH2| exact AFR2| exact ST2| apply munch_refl| apply wmono_refl| exact (kmem_inv_N _ _ MI2)| exact DP| exact DI| exact FU].
Qed.

(* [comment removed for export] *)
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
Lemma dk_leaf_xfer : forall (m m' : mem), munch [(a_P A - 16, a_P A)] m m' ->
  (forall J d s, dmem DI_A0 cx (a_g1 A) (a_sv A) (a_payload A) m (dvF cx J d s) -> dmem DI_A0 cx (a_g1 A) (a_sv A) (a_payload A) m' (dvF cx J d s)) /\
  (forall a cs, a_P A <= a -> rw_cells a0segs m a cs -> rw_cells a0segs m' a cs) /\
  (aframe A m -> aframe A m').
Proof.
  intros m m' MU. pose proof dk_lin as (_ & _ & _ & _ & _ & _ & FB0 & FB1 & SH0 & SH1 & _). pose proof dk_geo as (G1 & G2 & G3 & _).
  pose proof alloc_ceiling_range as ACR.
  assert (LOI : AIHI0 <= a_lo A) by (destruct AOK as (_ & _ & _ & _ & _ & _ & LO2 & _); unfold CEILING in LO2; clear - LO2 ACR; lia).
  assert (AG : agree_on (fun x => x < a_P A - 16 \/ a_P A <= x) m m') by (apply (agree_of_nmunch _ m m' _ MU); intros x Hx; cbn [KFrame.outside NFrame.outside]; clear - Hx; lia).
  split; [| split].
  - intros J d s DM. pose proof DM as (_ & _ & _ & _ & _ & _ & _ & _ & _ & GOT & SEV & RN). cbn [di_segs di_got di_stderrp di_crc di_rnums DI_A0] in GOT, SEV, RN.
    pose proof (dmemLF_agree cx _ m m' J d s dk_plen ltac:(eapply agree_sub; [exact AG|]; intros x Hx; cbv beta; pose proof (dk_dfp_lo x Hx) as DL0; clear - DL0 G1; lia) (dmemL_of m cx _ _ _ _ DM)) as DL.
    destruct DL as (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9). unfold dmem. cbn [di_segs di_got di_stderrp di_crc di_rnums DI_A0].
    repeat (split; [assumption|]).
    split. { apply (n_ro_cells_agree a0segs m m' _ _ GOT). eapply agree_sub; [exact AG|]. intros x Hx. cbv beta in Hx |- *. cbn [cells_size csize Nat.add] in Hx. clear - Hx LOI G1. lia. }
    split. { apply (n_ro_cells_agree a0segs m m' _ _ SEV). eapply agree_sub; [exact AG|]. intros x Hx. cbv beta in Hx |- *. cbn [cells_size csize Nat.add] in Hx. clear - Hx LOI G1. lia. }
    apply (n_u32arr_agree a0segs m m' _ _ RN). eapply agree_sub; [exact AG|]. intros x Hx. cbv beta in Hx |- *. pose proof rnums_words_length as RNL. rewrite RNL in Hx. clear - Hx LOI G1. lia.
  - intros a cs PA H. apply (n_rw_cells_agree a0segs m m' _ _ H). eapply agree_sub; [exact AG|]. intros x Hx. cbv beta in Hx |- *. clear - Hx PA. lia.
  - intros (zt & ng & jg & j24 & pos & j38 & fl & GEO & NG & FLP & FRM & FRT & FF & FS).
    exists zt, ng, jg, j24, pos, j38, fl. split; [exact GEO|]. split; [exact NG|].
    split. { apply (n_ro_cells_agree a0segs m m' _ _ FLP). eapply agree_sub; [exact AG|]. intros x Hx. cbv beta in Hx |- *. cbn [cells_size csize Nat.add] in Hx. clear - Hx FB1 G1. lia. }
    split. { apply (n_rw_cells_agree a0segs m m' _ _ FRM). eapply agree_sub; [exact AG|]. intros x Hx. cbv beta in Hx |- *. clear - Hx. lia. }
    split. { apply (n_rw_cells_agree a0segs m m' _ _ FRT). eapply agree_sub; [exact AG|]. intros x Hx. cbv beta in Hx |- *. clear - Hx. lia. }
    split. { apply (n_rw_cells_agree a0segs m m' _ _ FF). eapply agree_sub; [exact AG|]. intros x Hx. cbv beta in Hx |- *. cbn [cells_size csize Nat.add] in Hx. clear - Hx FB1 G1. lia. }
    apply (n_rw_cells_agree a0segs m m' _ _ FS). eapply agree_sub; [exact AG|]. intros x Hx. cbv beta in Hx |- *. cbn [cells_size csize Nat.add] in Hx. clear - Hx SH1 OFFP. lia.
Qed.

(* [comment removed for export] *)
Lemma dk_w14_img : forall a n, 0x10000 <= a -> a + n <= AIHI0 -> disjoint_from (W14 A) a n.
Proof.
  intros a n A0 A1. pose proof dk_lin as (_ & _ & _ & _ & _ & _ & _ & _ & SH0 & _ & _ & _ & SM01). pose proof dk_geo as (G1 & G2 & G3 & _).
  pose proof alloc_ceiling_range as ACR.
  destruct AOK as (_ & _ & SEPB & _ & _ & _ & LO2 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & NZF & NZS). unfold CEILING in LO2.
  destruct SEPB as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & IS & IT & IFB & ITT & IL16 & IL4). unfold img_apartA, DSTATE_SIZE in *.
  unfold W14, blk_ivls, DSTATE_SIZE. destruct SM01 as [E|E]; rewrite E; cbn [Z.eqb app disjoint_from].
  - pose proof (ITT (NZF E)) as B. clear - A0 A1 IS IT IFB B SH0 G1 LO2 ACR. repeat split; lia.
  - destruct (NZS E) as [N16 N4]. pose proof (IL16 N16) as B1. pose proof (IL4 N4) as B2. clear - A0 A1 IS IT IFB B1 B2 SH0 G1 LO2 ACR. repeat split; lia.
Qed.

Lemma dk_aconsts : forall Σ m0 (m : mem), ART RT Σ m0 -> munch (W14 A) m0 m -> aconsts A0C m.
Proof.
  intros Σ m0 m ART0 MU. destruct (fs_aconsts_of_art RT AF Σ m0 ART0) as [[C1 C2] _]. cbn [aci_segs aci_got_sh aci_shvar aci_c CmpCut.ci_segs A0C] in C1, C2.
  split; cbn [aci_segs aci_got_sh aci_shvar aci_c CmpCut.ci_segs A0C].
  - apply (ro_cells_transport a0segs _ m0 m _ _ C1 MU). cbn [cells_size csize Nat.add]. apply dk_w14_img; clear; lia.
  - apply (ro_cells_transport a0segs _ m0 m _ _ C2 MU). cbn [cells_size csize Nat.add]. apply dk_w14_img; clear; lia.
Qed.

Lemma dk_sub16 : forall m F fc, sub_fp [(a_P A - 16, a_P A)] (W14 (AA m F fc)).
Proof. intros m F fc x Ho. pose proof dk_geo as (_ & G2 & _). unfold W14 in Ho. cbn [dk_setm0 a_cx a_P a_sp a_fb a_shf outside app] in Ho |- *. destruct Ho as (_ & _ & H3 & _). split; [clear - H3 G2; lia| exact I]. Qed.

Lemma dec_idxn : forall Σ m0 F0 fc0 Fu fa fb j5 sym unz l16 l4, INV Σ m0 ->
  A0F_cut_IDXNR (AA m0 F0 fc0) (QL Σ R0) Fu fa fb j5 sym unz l16 l4 -> A0F_call_IDXN (AA m0 F0 fc0) (QL Σ R0) Fu fa fb j5 sym unz l16 l4.
Proof.
  intros Σ m0 F0 fc0 Fu fa fb j5 sym unz l16 l4 IV HRET. pose proof IV as (SK & LV & CRE & ART0 & MI0 & PR0).
  unfold A0F_call_IDXN. intros until w720. intros DM FRL FRH AFR ST MU WM NMI DP SMF FA FB ZA ZB DR0 FU.
  pose proof (dk_aconsts Σ m0 m ART0 MU) as AC.
  eapply evt_cut.
  { eapply (A0F_dec_U12SF.A0F_idx_lift (AA m0 F0 fc0) (dk_aok m0 F0 fc0) (dk_ash Σ m0 F0 fc0 IV) HIS J _ s m); [exact DM| exact ST| exact MU| exact NMI| exact AC]. }
  intros ms' PO. unfold A0F_leafCut.indexIntoF_apost in PO.
  destruct PO as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & -> & MUc & WMc & MIc & ST' & _).
  pose proof dk_geo as (G1 & G2 & G3 & _).
  cbn [dk_setm0 a_P] in MUc, ST'. rewrite (P_unsigned G) in MUc, ST'.
  rewrite (ret_pc_even 0xa7204 ltac:(lia) eq_refl).
  dk_norm. change (aframe A m) in AFR.
  destruct (dk_leaf_xfer m m' MUc) as (XD & XR & XA).
  unfold A0F_cut_IDXNR in HRET.
  eapply (HRET L d s J); cbn [dk_setm0 a_cx a_g1 a_sv a_payload a_m0 a_lo a_P a_sp a_b0 a_fb a_shf a_shs a_sht a_gp a_tp a_F a_fc];
    [exact (XD _ _ _ DM)| exact (XR (a_P A) _ ltac:(clear; lia) FRL)| exact (XR (a_P A + 496) _ ltac:(clear; lia) FRH)| exact (XA AFR)| exact ST'
    | exact (munch_trans _ m0 m m' MU (munch_weaken _ _ m m' (dk_sub16 m0 F0 fc0) MUc))| exact (wmono_trans a0segs m0 m m' WM WMc)| exact MIc| exact DP| exact SMF| exact FA| exact FB| exact ZA| exact ZB| exact DR0| exact FU].
Qed.

Lemma dec_idxr : forall Σ m0 F0 fc0 Fu fa fb j5 sym unz l16 l4, INV Σ m0 ->
  A0F_cut_IDXRR (AA m0 F0 fc0) (QL Σ R0) Fu fa fb j5 sym unz l16 l4 -> A0F_call_IDXR (AA m0 F0 fc0) (QL Σ R0) Fu fa fb j5 sym unz l16 l4.
Proof.
  intros Σ m0 F0 fc0 Fu fa fb j5 sym unz l16 l4 IV HRET. pose proof IV as (SK & LV & CRE & ART0 & MI0 & PR0).
  unfold A0F_call_IDXR. intros until w720. intros DM FRL FRH AFR ST MU WM NMI DP SMF FA FB ZA ZB DR0 FU.
  pose proof (dk_aconsts Σ m0 m ART0 MU) as AC.
  eapply evt_cut.
  { eapply (A0F_dec_U12SF.A0F_idx_lift (AA m0 F0 fc0) (dk_aok m0 F0 fc0) (dk_ash Σ m0 F0 fc0 IV) HIS J _ s m); [exact DM| exact ST| exact MU| exact NMI| exact AC]. }
  intros ms' PO. unfold A0F_leafCut.indexIntoF_apost in PO.
  destruct PO as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & -> & MUc & WMc & MIc & ST' & _).
  pose proof dk_geo as (G1 & G2 & G3 & _).
  cbn [dk_setm0 a_P] in MUc, ST'. rewrite (P_unsigned G) in MUc, ST'.
  rewrite (ret_pc_even 0xa6f80 ltac:(lia) eq_refl).
  dk_norm. change (aframe A m) in AFR.
  destruct (dk_leaf_xfer m m' MUc) as (XD & XR & XA).
  unfold A0F_cut_IDXRR in HRET.
  eapply (HRET L d s J); cbn [dk_setm0 a_cx a_g1 a_sv a_payload a_m0 a_lo a_P a_sp a_b0 a_fb a_shf a_shs a_sht a_gp a_tp a_F a_fc];
    [exact (XD _ _ _ DM)| exact (XR (a_P A) _ ltac:(clear; lia) FRL)| exact (XR (a_P A + 496) _ ltac:(clear; lia) FRH)| exact (XA AFR)| exact ST'
    | exact (munch_trans _ m0 m m' MU (munch_weaken _ _ m m' (dk_sub16 m0 F0 fc0) MUc))| exact (wmono_trans a0segs m0 m m' WM WMc)| exact MIc| exact DP| exact SMF| exact FA| exact FB| exact ZA| exact ZB| exact DR0| exact FU].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma dec_idxn_all : forall Σ m F fc, INV Σ m -> forall Fu fa fb j5 sym unz l16 l4, A0F_call_IDXN (AA m F fc) (QL Σ R0) Fu fa fb j5 sym unz l16 l4.
Proof.
  intros Σ m F fc IV Fu fa fb j5 sym unz l16 l4. apply (dec_idxn Σ m F fc _ _ _ _ _ _ _ _ IV).
  apply (A0F_decMain.A0F_seg5N (AA m F fc) (dk_aok m F fc) (dk_ash Σ m F fc IV) (QL Σ R0) (dec_retc Σ m F fc IV)).
Qed.
Lemma dec_idxr_all : forall Σ m F fc, INV Σ m -> forall Fu fa fb j5 sym unz l16 l4, A0F_call_IDXR (AA m F fc) (QL Σ R0) Fu fa fb j5 sym unz l16 l4.
Proof.
  intros Σ m F fc IV Fu fa fb j5 sym unz l16 l4. apply (dec_idxr Σ m F fc _ _ _ _ _ _ _ _ IV).
  apply (A0F_decMain.A0F_seg5R (AA m F fc) (dk_aok m F fc) (dk_ash Σ m F fc IV) (QL Σ R0) (dec_retc Σ m F fc IV)).
Qed.
Lemma dec_seg4 : forall Σ m F fc, INV Σ m -> forall Fu, A0F_decMain.A0F_cuts4 (AA m F fc) (QL Σ R0) Fu.
Proof.
  intros Σ m F fc IV. apply (A0F_decMain.A0F_seg4 (AA m F fc) (dk_aok m F fc) (dk_ash Σ m F fc IV) (QL Σ R0) (dec_retc Σ m F fc IV)).
  - intros. apply dec_idxn_all. exact IV.
  - intros. apply dec_idxr_all. exact IV.
Qed.
Lemma dec_msu_all : forall Σ m F fc, INV Σ m -> forall Fu, A0F_call_MSU (AA m F fc) (QL Σ R0) Fu.
Proof. intros Σ m F fc IV. apply (dec_msu Σ m F fc IV). intros m2 F2 fc2 IV2 Fu. exact (proj1 (dec_seg4 Σ m2 F2 fc2 IV2 Fu)). Qed.

Lemma dec_hbc_ind : forall k Σ m F fc, INV Σ m -> forall Fu t mn mx, 6 - Z.of_nat k <= t -> A0F_call_HBC (AA m F fc) (QL Σ R0) Fu t mn mx.
Proof.
  induction k as [|k IH]; intros Σ m F fc IV Fu t mn mx Ht.
  - unfold A0F_call_HBC. intros until w720. intros DM FRL FRH AFR ST MU WM NMI DP DI FU. exfalso.
    destruct DI as (COM & Ht' & _). destruct COM as [SEL _]. destruct SEL as (_ & NG & _). clear - Ht Ht' NG. lia.
  - apply (dec_hbc Σ m F fc Fu t mn mx IV). intros Σ2 m2 F2 fc2 IV2.
    apply (A0F_dec_U7B.A0F_U7_C2 (AA m2 F2 fc2) (dk_aok m2 F2 fc2) (dk_ash Σ2 m2 F2 fc2 IV2) (QL Σ2 R0) Fu t mn mx).
    apply (A0F_dec_U7C.A0F_U7_D (AA m2 F2 fc2) (dk_aok m2 F2 fc2) (dk_ash Σ2 m2 F2 fc2 IV2) (QL Σ2 R0) Fu).
    + apply (A0F_dec_U7D.A0F_U7_M1 (AA m2 F2 fc2) (dk_aok m2 F2 fc2) (dk_ash Σ2 m2 F2 fc2 IV2) (QL Σ2 R0) Fu). exact (dec_msu_all Σ2 m2 F2 fc2 IV2 Fu).
    + apply (A0F_dec_U7C.A0F_U7_T (AA m2 F2 fc2) (dk_aok m2 F2 fc2) (dk_ash Σ2 m2 F2 fc2 IV2) (QL Σ2 R0) Fu (t + 1)). intros mn' mx'.
      apply (A0F_dec_U7B.A0F_U7_C1 (AA m2 F2 fc2) (QL Σ2 R0) Fu (t + 1) mn' mx'). apply (IH Σ2 m2 F2 fc2 IV2). clear - Ht. lia.
Qed.
Lemma dec_hbc_all : forall Σ m F fc, INV Σ m -> forall Fu t mn mx, A0F_call_HBC (AA m F fc) (QL Σ R0) Fu t mn mx.
Proof. intros Σ m F fc IV Fu t mn mx. apply (dec_hbc_ind (Z.to_nat (6 - t)) Σ m F fc IV). lia. Qed.

Lemma dec_seg2 : forall Σ m F fc, INV Σ m -> forall Fu, A0F_decMain.A0F_cuts2 (AA m F fc) (QL Σ R0) Fu.
Proof.
  intros Σ m F fc IV. apply (A0F_decMain.A0F_seg2 (AA m F fc) (dk_aok m F fc) (dk_ash Σ m F fc IV) (QL Σ R0) (dec_retc Σ m F fc IV)).
  intros. apply dec_hbc_all. exact IV.
Qed.
Lemma dec_msi_all : forall Σ m F fc, INV Σ m -> forall Fu, A0F_call_MSI (AA m F fc) (QL Σ R0) Fu.
Proof. intros Σ m F fc IV. apply (dec_msi Σ m F fc IV). intros m2 F2 fc2 IV2 Fu. exact (proj1 (dec_seg2 Σ m2 F2 fc2 IV2 Fu)). Qed.

(* [comment removed for export] *)
Theorem dec_H14 : forall Σ m F fc, INV Σ m -> forall Fu, A0F_cut_H14 (AA m F fc) (QL Σ R0) Fu.
Proof.
  intros Σ m F fc IV Fu.
  exact (proj1 (A0F_decMain.A0F_seg1 (AA m F fc) (dk_aok m F fc) (dk_ash Σ m F fc IV) (QL Σ R0) (dec_retc Σ m F fc IV) (dec_msi_all Σ m F fc IV) Fu)).
Qed.
End DECL2.
