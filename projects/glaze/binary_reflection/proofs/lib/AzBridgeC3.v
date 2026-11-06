(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.glaze.binary_reflection.lib Require BvWfKernel.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require WdZS.
#[local] Ltac Zify.zify ::= WdZS.wd_zs_stock.   (* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape OSSVerify.Proofs.glaze.binary_reflection.lib.Spec4 OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3 OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3B OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3Sound OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymRun3 OSSVerify.Proofs.glaze.binary_reflection.lib.AzPlanCore OSSVerify.Proofs.glaze.binary_reflection.lib.AzPlan OSSVerify.Proofs.glaze.binary_reflection.lib.AzAPS OSSVerify.Proofs.glaze.binary_reflection.lib.AzGPS OSSVerify.Proofs.glaze.binary_reflection.lib.AzIface OSSVerify.Proofs.glaze.binary_reflection.lib.AzContracts OSSVerify.Proofs.glaze.binary_reflection.lib.AzKnowLib OSSVerify.Proofs.glaze.binary_reflection.lib.AzNSpec OSSVerify.Proofs.glaze.binary_reflection.lib.AzFrame OSSVerify.Proofs.glaze.binary_reflection.lib.AzBridgeH OSSVerify.Proofs.glaze.binary_reflection.lib.AzOpNewK OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst. Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape.ShapeRel OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape.ShapeRetry OSSVerify.Proofs.glaze.binary_reflection.lib.Spec4.AgentLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3 OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3B OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3Sound OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymRun3 OSSVerify.Proofs.glaze.binary_reflection.lib.AzPlanCore OSSVerify.Proofs.glaze.binary_reflection.lib.AzPlan OSSVerify.Proofs.glaze.binary_reflection.lib.AzAPS OSSVerify.Proofs.glaze.binary_reflection.lib.AzGPS OSSVerify.Proofs.glaze.binary_reflection.lib.AzIface OSSVerify.Proofs.glaze.binary_reflection.lib.AzContracts OSSVerify.Proofs.glaze.binary_reflection.lib.AzKnowLib OSSVerify.Proofs.glaze.binary_reflection.lib.AzNSpec OSSVerify.Proofs.glaze.binary_reflection.lib.AzFrame OSSVerify.Proofs.glaze.binary_reflection.lib.AzBridgeH OSSVerify.Proofs.glaze.binary_reflection.lib.AzOpNewK OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.AsIfaceNM3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AX2S. Import AP. Import GPS.
Open Scope Z_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Notation u := bv_unsigned.

Section BridgeC.
Context {RC : run_ceil}.
Context {SFL : stk_floor}.   (* [comment removed for export] *)
Variable SEGS : list Segment.
Variable IA : AsVocab.AsCells.as_addrs.
Variable FXOK : FX -> Prop.
Variable AAINVH : option Z -> list (Z * Z) -> list (Z * Z) -> Z -> Z -> Z -> (word -> option byte) -> Model -> Prop.
Variable FRESH : list (Z * Z) -> list (Z * Z) -> Z -> Z -> Z -> (word -> option byte) -> Model -> Z -> Prop.
Variable fsbase : Z.
Hypothesis ASC : AsIfaceNM3.as_contracts_n SEGS FXOK IA AAINVH FRESH fsbase.   (* [comment removed for export] *)
Variable G : gtable.
(* [comment removed for export] *)
Hypothesis G_imglo : g_img_lo G = AsVocab.AsCells.ia_img_lo IA.
Hypothesis G_hi : g_img_hi G = AsVocab.AsCells.ia_img_hi IA.
Hypothesis G_ro_img : g_img_lo G <= g_ro_lo G /\ g_ro_lo G <= g_ro_hi G <= g_img_hi G.
Hypothesis G_tp : g_tp G = AsVocab.AsCells.ia_tp IA.
Hypothesis G_errno : g_errno G = AsVocab.ia_errno IA.   (* [comment removed for export] *)
Hypothesis G_privs : forall z, AsVocab.in_wins (AsVocab.AsCells.ia_priv IA) z -> in_wins (g_priv G) z.
Hypothesis G_malloc : g_malloc G = AsVocab.AsCells.ia_malloc IA.
Hypothesis G_malloc_thunk : g_malloc_thunk G = AsVocab.AsCells.ia_malloc_thunk IA.
Hypothesis G_free : g_free G = AsVocab.AsCells.ia_free IA.
Hypothesis G_free_thunk : g_free_thunk G = AsVocab.AsCells.ia_free_thunk IA.
Hypothesis G_opdel : g_opdel G = AsVocab.AsCells.ia_opdel IA.
Hypothesis G_opdel_sized : g_opdel_sized G = AsVocab.AsCells.ia_opdel_sz IA.
Hypothesis G_stkmal : forall k, 0 <= k <= 3 -> g_stkmal G k = AsVocab.AsCells.ia_stkmal IA k.
(* [comment removed for export] *)

(* [comment removed for export] *)
Hypothesis FF_classes : forall h L FF B C K M mdl f k, AAINVH h L FF B C K M mdl -> In (f, k) FF -> 0 <= k.

#[local] Notation AINVw := (AzBridgeH.AINVw).
Definition AINVH0 := AINVw (AAINVH None).
Definition AINVHN (n : Z) := AINVw (AAINVH (Some n)).
Definition FPCw (M : word -> option byte) (s0 sp : Z) : Prop := AsVocab.fpc M s0 sp AsVocab.DMAX.
Definition RZ : GPS.rz_t := rrealizes SEGS.



(* [comment removed for export] *)
Lemma in_shadow_sh : forall b n z, in_shadow SB b n z <-> AsVocab.sh_lo b <= z < AsVocab.sh_hi b n.
Proof. intros b n z. unfold in_shadow, AsVocab.sh_lo, AsVocab.sh_hi, AsVocab.SB, SB. tauto. Qed.

Lemma callee_saved_same : AsVocab.as_callee_saved = callee_saved_regs.
Proof. reflexivity. Qed.

Lemma regs_kept_w : forall R0 R', AsIface3.regs_kept R0 R' -> regs_kept R0 R'.
Proof. intros R0 R' H r Hr. apply H. rewrite callee_saved_same. exact Hr. Qed.

Lemma call_pre_w : forall R0 M ret sp stk,
  hcall_pre SEGS G R0 M ret sp stk -> AsIface3.call_pre SEGS IA R0 M ret sp stk.
Proof.
  intros R0 M ret sp stk (R1 & Rr & Re & R2 & Hal & Hsp & Hhi & R4 & Hstk).
  unfold AsIface3.call_pre. rewrite <- G_tp.
  assert (E1 : (1%bv : bv 5) = Z_to_bv 5 1) by (apply bv_eq; reflexivity).
  assert (E2 : (2%bv : bv 5) = Z_to_bv 5 2) by (apply bv_eq; reflexivity).
  assert (E4 : (4%bv : bv 5) = Z_to_bv 5 4) by (apply bv_eq; reflexivity).
  rewrite E1, E2, E4.
  split; [exact R1|]. split; [exact Rr|]. split; [exact Re|]. split; [exact R2|]. split; [exact Hal|].
  split; [exact Hsp|]. split; [unfold AsVocab.PTRHI; unfold two47 in Hhi; lia|]. split; [exact R4|]. intros a Ha. apply Hstk. exact Ha.
Qed.

(* [comment removed for export] *)
Lemma nvisible_app_visible : forall L FF z,
  nvisible G L (map AzBridgeH.wfr FF) z -> AsVocab.app_visible IA L FF z.
Proof.
  intros L FF z H. unfold nvisible in H. unfold AsVocab.app_visible.
  destruct H as [Hb|[Hf|[Hl|[Hs|Hi]]]].
  - left. exact Hb.
  - right; left. destruct Hf as (f & m & Hin & Hz). apply AzBridgeH.in_map_wfr in Hin as (k & Hin & ->). exists f, k. split; [exact Hin | exact Hz].
  - apply in_lshadow_app in Hl as [Hl|Hl]; destruct Hl as (b & n & Hin & Hz); apply in_shadow_sh in Hz.
    + right; right; left. exists b, n. split; assumption.
    + right; right; right; left. apply AzBridgeH.in_map_wfr in Hin as (k & Hin & ->). exists b, k. split; assumption.
  - right; right; right; right; left. unfold AsVocab.in_stack_shadow, AsVocab.sh_lo, AsVocab.SB.
    unfold in_sshadow, SB, HEAPLO in Hs. lia.
  - right; right; right; right; right. unfold AsVocab.in_image_shadow, AsVocab.sh_lo, AsVocab.sh_hi, AsVocab.SB.
    unfold in_ishadow, SB in Hi. rewrite G_hi in Hi. rewrite <- G_imglo.
    replace (g_img_lo G + (AsVocab.AsCells.ia_img_hi IA - g_img_lo G) + 7) with (AsVocab.AsCells.ia_img_hi IA + 7) by lia.
    pose proof G_ro_img as (GR0 & GR1 & GR2).
    assert (D : g_img_lo G / 8 <= g_ro_lo G / 8) by (apply Z.div_le_mono; lia).
    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
    lia.
    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Qed.

Lemma changed_w : forall stk L FF sp (a : word),
  AsVocab.as_changed IA stk L FF sp a -> hchanged G stk L (map AzBridgeH.wfr FF) sp a.
Proof.
  intros stk L FF sp a H. unfold hchanged. destruct H as [Hs|[(Hr & Hni & Hnv)|[Hp|He]]].
  - left. exact Hs.
  - right; left. split; [exact Hr|]. split; [rewrite G_imglo, G_hi; exact Hni|].
    intros Hv. apply Hnv. apply nvisible_app_visible. exact Hv.
  - right; right. apply AzKnowLib.in_wins_privx. right. apply G_privs. exact Hp.
  - right; right. apply AzKnowLib.in_wins_privx. left. unfold errw. rewrite G_errno. exact He.   (* [comment removed for export] *)
Qed.

(* [comment removed for export] *)
Lemma errno_kept_w : forall M M', AsVocab.errno_kept IA M M' -> errno_kept G M M'.
Proof. intros M M' H a He. apply H. unfold AsVocab.in_errno. unfold errw in He. rewrite G_errno in He. exact He. Qed.

Lemma nmodel_of_vm : forall mdl mdl', AsVocab.same_except_vm mdl mdl' -> m_halted mdl' = None -> nmodel mdl mdl'.
Proof.
  intros mdl mdl' H Hh. destruct (AsVocab.same_except_vm_frame mdl mdl' H) as (F1 & F2 & F3 & _).
  unfold nmodel. repeat split; assumption.
Qed.


#[local] Notation cfg := (fun fx R0 p M mdl => mkCfg (mkstF fx R0 (Z_to_bv 64 p) M (seg_rom SEGS)) mdl).

(* [comment removed for export] *)
Lemma wfr_inj : forall FF FF0, map AzBridgeH.wfr FF0 = map AzBridgeH.wfr FF -> Forall (fun fk => 0 <= snd fk) FF -> FF0 = FF.
Proof.
  intros FF. induction FF as [|[f k] r IH]; intros [|[f0 k0] r0] H HF; cbn in H; try discriminate H; [reflexivity|].
  injection H as E1 E2 E3. apply Forall_cons_iff in HF as [Hk HF]. cbn in Hk. subst f0. f_equal; [|exact (IH _ E3 HF)].
  f_equal. unfold AsVocab.FS in E2.
  assert (P : 2 ^ k0 = 2 ^ k) by lia.
  destruct (Z_lt_le_dec k0 0) as [N|N].
  { rewrite (Z.pow_neg_r 2 k0 N) in P. pose proof (Z.pow_pos_nonneg 2 k ltac:(lia) Hk). lia. }
  exact (Z.pow_inj_r 2 k0 k ltac:(lia) N Hk P).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma malloc_pre_w : forall fpcreq fx R0 M mdl L FF B C K ret n sp stk,
  hmalloc_pre SEGS G FXOK AINVH0 FPCw fpcreq fx R0 M mdl L (map AzBridgeH.wfr FF) B C K ret n sp stk ->
  AINVw (AAINVH None) L (map AzBridgeH.wfr FF) B C K M mdl ->
  forall FF', map AzBridgeH.wfr FF = map AzBridgeH.wfr FF' -> AAINVH None L FF' B C K M mdl ->
  AsIface3.malloc_pre SEGS FXOK IA AAINVH None stk fpcreq fx R0 M mdl L FF' B C K ret n sp.
Proof.
  intros fpcreq fx R0 M mdl L FF B C K ret n sp stk (HFX & Hh & _ & Hpre & Hn & Hnr & Hfpc & HB & HCc & HK) _ FF' _ HA.
  unfold AsIface3.malloc_pre.
  assert (E10 : (10%bv : bv 5) = Z_to_bv 5 10) by (apply bv_eq; reflexivity).
  assert (E8 : (8%bv : bv 5) = Z_to_bv 5 8) by (apply bv_eq; reflexivity).
  rewrite E10, E8.
  split; [exact Hh|]. split; [exact HFX|]. split; [exact HA|]. split; [left; reflexivity|]. split; [exact (call_pre_w _ _ _ _ _ Hpre)|].
  split; [exact Hn|]. split; [unfold AsVocab.NMAX; unfold AzIface.NMAX in Hnr; exact Hnr|].
  split; [intros Hq; exact (Hfpc Hq)|].
  unfold AsVocab.MBLK, AsVocab.GBUDGET, AsVocab.LMAX, AsVocab.kcost_malloc, AsVocab.EVT, AsVocab.KCAP.
  unfold AzIface.mcost, AzIface.MBLK, AzIface.GBUDGET, AzIface.MCNT, AzIface.GCOUNT, AzIface.LMAX, AzIface.kcost, AzIface.EVT, AzIface.GKCAP in HB, HCc, HK. lia.
Qed.


#[local] Notation MKATW := (AsIface3.MALLOC_KATW SEGS FXOK IA AAINVH).
#[local] Notation MALT := (AsIface3.MALLOC_ALT SEGS FXOK IA AAINVH FRESH).

(* [comment removed for export] *)
Lemma malloc_ok_w : forall stk R0 M mdl L FF B C K ret n sp c',
  m_halted mdl = None ->
  AsIface3.malloc_ok SEGS FXOK IA AAINVH stk R0 M mdl L FF B C K ret n sp c' ->
  exists fx' R' M' mdl' p, c' = cfg fx' R' ret M' mdl'
    /\ hmalloc_post_ok SEGS G FXOK AINVH0 R0 M mdl L (map AzBridgeH.wfr FF) B C K n sp stk fx' R' M' mdl' p.
Proof.
  intros stk R0 M mdl L FF B C K ret n sp c' Hh
         (fx' & R' & M' & mdl' & p & Hc & HFX' & Hkept & Ha0 & Hpal & Hblk & Hal2k & HdisjL & HdisjF & Hdef & Hsh0 & Hshp & Hshw & Hch & Hek & Hscr & HA' & Hvm & Hlz & Hh').   (* [comment removed for export] *)
  exists fx', R', M', mdl', p. split; [exact Hc|].
  assert (E10 : (10%bv : bv 5) = Z_to_bv 5 10) by (apply bv_eq; reflexivity). rewrite E10 in Ha0.
  split; [exact HFX'|]. split; [exact (regs_kept_w _ _ Hkept)|]. split; [exact Ha0|]. split; [exact Hpal|].
  split; [exact (AzBridgeH.ablk_ok_of IA G G_imglo G_hi _ _ Hblk)|]. split; [exact Hal2k|].
  split.
  { intros b m Hin. apply in_app_iff in Hin as [Hin|Hin]; [exact (HdisjL b m Hin)|].
    apply AzBridgeH.in_map_wfr in Hin as (k & Hin & ->). exact (HdisjF b k Hin). }
  split; [exact Hdef|].
  split.
  { (* [comment removed for export] *)
    intros z Hz. unfold AsVocab.sh_lo, AsVocab.SB in Hsh0, Hshp.
    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
    destruct (Z_lt_le_dec (z / 8 - u p / 8) (n / 8)) as [Hlt|Hge].
    - exists (Z_to_bv 8 0). split; [|left; reflexivity].
      replace (SB + z / 8) with (0x7fff8000 + u p / 8 + (z / 8 - u p / 8)) by (unfold SB; lia). apply Hsh0. lia.
    - assert (Hmod : n mod 8 <> 0) by lia.
      exists (Z_to_bv 8 (n mod 8)). split.
      { replace (SB + z / 8) with (0x7fff8000 + u p / 8 + n / 8) by (unfold SB; lia). apply Hshp. exact Hmod. }
      right. rewrite u8_lit. rewrite (Z.mod_small (n mod 8) 256) by lia. lia.
    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false). }
  split; [intros a Ha; apply Hshw; apply in_shadow_sh; exact Ha|].
  split; [intros a Ha; apply changed_w; apply Hch; exact Ha|].
  split; [exact (errno_kept_w _ _ Hek)|].   (* [comment removed for export] *)
  split; [exact Hscr|].
  split.
  { exists FF. split; [reflexivity|].
    unfold AsVocab.MBLK, AsVocab.kcost_malloc, AsVocab.EVT in HA'. unfold AzIface.mcost, AzIface.MBLK, AzIface.MCNT, AzIface.kcost, AzIface.EVT. exact HA'. }
  exact (nmodel_of_vm _ _ Hvm Hh').
Qed.

Lemma malloc_null_w : forall stk R0 M mdl L FF B C K ret n sp c',
  AsIface3.malloc_null SEGS FXOK IA AAINVH stk R0 M mdl L FF B C K ret n sp c' ->
  exists fx' R' M' mdl', c' = cfg fx' R' ret M' mdl'
    /\ hmalloc_post_null SEGS G FXOK AINVHN R0 M mdl L (map AzBridgeH.wfr FF) B C K n sp stk fx' R' M' mdl'.
Proof.
  intros stk R0 M mdl L FF B C K ret n sp c' (fx' & R' & M' & mdl' & Hc & HFX' & Hkept & Ha0 & Hch & Hek & Hscr & HA' & Hvm & Hlz & Hh').   (* [comment removed for export] *)
  exists fx', R', M', mdl'. split; [exact Hc|].
  assert (E10 : (10%bv : bv 5) = Z_to_bv 5 10) by (apply bv_eq; reflexivity). rewrite E10 in Ha0.
  split; [exact HFX'|]. split; [exact (regs_kept_w _ _ Hkept)|]. split; [exact Ha0|].
  split; [intros a Ha; apply changed_w; apply Hch; exact Ha|].
  split; [exact (errno_kept_w _ _ Hek)|].   (* [comment removed for export] *)
  split; [exact Hscr|].
  split; [| exact (nmodel_of_vm _ _ Hvm Hh')].
  exists FF. split; [reflexivity|]. exact HA'.   (* [comment removed for export] *)
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
#[local] Notation FKAT := (AsIfaceNM3.AsIfacePR3.FREE_KAT_N SEGS FXOK IA AAINVH).   (* [comment removed for export] *)
#[local] Notation SKAT := (AsIface3.STKMAL SEGS FXOK IA AAINVH fsbase).
#[local] Notation FREL := (AsIface3.FAKEREL SEGS FXOK IA AAINVH).

Section GenRZ.
Variable RZg : GPS.rz_t.
Hypothesis RZg_kc : forall T, AsIface3.AsK.kclosedD SEGS (fun c => RZg c T).

(* [comment removed for export] *)
Lemma katD_g : forall c (Q : config -> Prop) T, AsIface3.AsK.katD SEGS c Q -> (forall c', Q c' -> RZg c' T) -> RZg c T.
Proof. intros c Q T H HQ. exact (H (fun c => RZg c T) (RZg_kc T) HQ). Qed.
Lemma katwD_g : forall c (Qok Qf : config -> Prop) T,
  AsIface3.AsK.katwD SEGS c Qok Qf -> (forall c', Qok c' -> RZg c' T) -> (forall c', Qf c' -> RZg c' T) -> RZg c T.
Proof.
  intros c Qok Qf T H Hok Hf. apply (katD_g c _ T (AsIface3.AsK.katwD_katD SEGS c Qok Qf H)).
  intros c' [X|X]; [apply Hok | apply Hf]; exact X.
Qed.
Lemma katwD_ok_g : forall c (Qok Qf : config -> Prop) T,
  AsIface3.AsK.katwD SEGS c Qok Qf -> (forall c', Qok c' -> RZg c' T) -> RZg c T.
Proof. intros c Qok Qf T H Hok. exact (katD_g c Qok T (AsIface3.AsK.katwD_ok_only SEGS c Qok Qf H) Hok). Qed.
Lemma katsD_ok_g : forall c (Qok Qf : config -> Prop) T,
  AsIface3.AsK.katsD SEGS c Qok Qf -> (forall c', Qok c' -> RZg c' T) -> RZg c T.
Proof. intros c Qok Qf T H Hok. exact (katwD_ok_g c Qok Qf T (AsIface3.AsK.katsD_katwD SEGS c Qok Qf H) Hok). Qed.

(* [comment removed for export] *)
Lemma h_malloc_wj : forall stk entry,
  MKATW stk entry true -> h_malloc_at SEGS G FXOK RZg AINVH0 AINVHN FPCw stk entry.
Proof.
  intros stk entry MS fx R0 M mdl L LF B C K ret n sp T Hpre HT0 Hok Hnull.
  pose proof Hpre as (HFX & Hh & (FF & HLF & HA) & _). subst LF.
  apply (katwD_g _ _ _ T (MS None fx R0 M mdl L FF B C K ret n sp (malloc_pre_w _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hpre ltac:(exists FF; split; [reflexivity | exact HA]) FF eq_refl HA))).
  - intros c' Hc'. destruct (malloc_ok_w stk R0 M mdl L FF B C K ret n sp c' Hh Hc') as (fx' & R' & M' & mdl' & p & -> & Hpost).
    exact (Hok fx' R' M' mdl' p Hpost).
  - intros c' Hc'. destruct (malloc_null_w stk R0 M mdl L FF B C K ret n sp c' Hc') as (fx' & R' & M' & mdl' & -> & Hpost).
    exact (Hnull fx' R' M' mdl' Hpost).
Qed.

(* [comment removed for export] *)
Lemma h_malloc1_wj : forall stk entry,
  MALT stk entry true -> h_malloc1_at SEGS G FXOK RZg AINVH0 FPCw (fun L LF B C K M mdl n => exists FF, LF = map AzBridgeH.wfr FF /\ FRESH L FF B C K M mdl n) stk entry.
Proof.
  intros stk entry MS fx R0 M mdl L LF B C K ret n sp Tok Hpre (FF0 & HLF0 & Hfresh) HTok Hok.
  pose proof Hpre as (HFX & Hh & (FF & HLF & HA) & _).
  assert (EFF : FF0 = FF).
  { apply wfr_inj; [rewrite <- HLF0; exact HLF|]. apply Forall_forall. intros [f k] Hin. cbn. exact (FF_classes _ _ _ _ _ _ _ _ _ _ HA Hin). }
  subst FF0. subst LF.
  apply (katsD_ok_g _ _ _ Tok (MS None fx R0 M mdl L FF B C K ret n sp (malloc_pre_w _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hpre ltac:(exists FF; split; [reflexivity | exact HA]) FF eq_refl HA) Hfresh)).
  intros c' Hc'. destruct (malloc_ok_w stk R0 M mdl L FF B C K ret n sp c' Hh Hc') as (fx' & R' & M' & mdl' & p & -> & Hpost).
  exact (Hok fx' R' M' mdl' p Hpost).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)


Lemma h_free_wj : forall stk entry, FKAT stk entry -> h_free_at SEGS G FXOK RZg AINVH0 FPCw stk entry.
Proof.
  intros stk entry FS fx R0 M mdl L L' LF B C K B' C' K' ret sp p T HFX Hh (FF & HLF & HA) Hpre Hp Hfpc CASES Hpost. subst LF.
  assert (E10 : (10%bv : bv 5) = Z_to_bv 5 10) by (apply bv_eq; reflexivity).
  assert (E8 : (8%bv : bv 5) = Z_to_bv 5 8) by (apply bv_eq; reflexivity).
  assert (PRE : AsIface3.free_pre SEGS FXOK IA AAINVH None stk fx R0 M mdl L L' FF B C K B' C' K' ret sp p).
  { unfold AsIface3.free_pre. rewrite E10, E8.
    split; [exact Hh|]. split; [exact HFX|]. split; [exact HA|]. split; [exact (call_pre_w _ _ _ _ _ Hpre)|].
    split; [exact Hp|]. split; [exact Hfpc|].
    destruct CASES as [H0|(m & L1 & L2 & HL & HL' & HB' & HC' & HK' & HKc)]; [left; exact H0 | right].
    exists m, L1, L2. unfold AsVocab.MBLK, AsVocab.kcost_free, AsVocab.EVT, AsVocab.KCAP.
    unfold AzIface.mcost, AzIface.MBLK, AzIface.MCNT, AzIface.KFREE, AzIface.EVT, AzIface.GKCAP in *.
    repeat split; try assumption. }
  apply (katD_g _ _ T (FS fx R0 M mdl L L' FF B C K B' C' K' ret sp p PRE)).
  intros c' (fx' & R' & M' & mdl' & -> & HFX' & Hkept & Hch & Hek & Hscr & HA' & Hvm & Hlz & Hh').   (* [comment removed for export] *)
  apply (Hpost fx' R' M' mdl' HFX' (regs_kept_w _ _ Hkept)).
  - intros a Ha. apply changed_w. apply Hch. exact Ha.
  - exact (errno_kept_w _ _ Hek).
  - exact Hscr.
  - exists FF. split; [reflexivity | exact HA'].
  - exact (nmodel_of_vm _ _ Hvm Hh').
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma nmodel_of_mat : forall mdl mdl', m_halted mdl = None -> same_but_materialized mdl mdl' -> nmodel mdl mdl'.
Proof.
  intros mdl mdl' Hh H.
  pose proof (same_but_materialized_frame mdl mdl' H) as (_ & _ & _ & _ & _ & _ & _ & _ & Hfds & _ & _ & Hfs & Hhalt & _).
  unfold nmodel. rewrite Hhalt. repeat split; assumption.
Qed.

Lemma fcount_hfcount : forall k FF, AsVocab.fcount k FF <= hfcount (AsVocab.FS k) (map AzBridgeH.wfr FF).
Proof.
  intros k FF. induction FF as [|[f k'] r IH]; cbn [AsVocab.fcount hfcount map AzBridgeH.wfr fst snd]; [lia|].
  destruct (Z.eqb_spec k' k) as [->|Hne].
  - rewrite Z.eqb_refl. lia.
  - destruct (Z.eqb (AsVocab.FS k') (AsVocab.FS k)); lia.
Qed.


Lemma h_stkmal_wj : forall k, 0 <= k <= 3 -> SKAT k -> h_stkmal SEGS G FXOK RZg AINVH0 k.
Proof.
  intros k Hk SK. unfold h_stkmal. intros fx R0 M mdl L LF B C K ret sp T _ HFX Hh (FF & HLF & HA) Hpre Hcnt Hpost. subst LF.
  rewrite (G_stkmal k Hk).
  assert (HFS : AsVocab.FS k = 64 * 2 ^ k) by reflexivity.
  assert (PRE : AsIface3.stkmal_pre SEGS FXOK IA AAINVH None k fx R0 M mdl L FF B C K ret sp).
  { unfold AsIface3.stkmal_pre. split; [unfold AsVocab.KMAXCLASS; lia|]. split; [exact Hh|]. split; [exact HFX|]. split; [exact HA|].
    split; [exact (call_pre_w _ _ _ _ _ Hpre)|].
    pose proof (fcount_hfcount k FF) as FC. rewrite HFS in FC. unfold AsVocab.FCAP. unfold FMIN in Hcnt.
    assert (2 ^ 11 <= 2 ^ (14 - k)) by (apply Z.pow_le_mono_r; lia). lia. }
  apply (katD_g _ _ T (SK None fx R0 M mdl L FF B C K ret sp PRE)).
  intros c' (fx' & R' & M' & mdl' & f & flag & -> & HFX' & Hkept & Ha0 & Hfal & Hblk & Hflo & Hfhi & HdisjL & HdisjF & Hdef & Hlast & Hsh0 & Hshw & Hch & Hek & Hscr & HA' & Hmat).   (* [comment removed for export] *)
  assert (E10 : (10%bv : bv 5) = Z_to_bv 5 10) by (apply bv_eq; reflexivity). rewrite E10 in Ha0.
  rewrite HFS in *.
  apply (Hpost fx' R' M' mdl' f flag HFX' (regs_kept_w _ _ Hkept) Ha0 Hfal (AzBridgeH.ablk_ok_of IA G G_imglo G_hi _ _ Hblk)).
  - intros b m Hin. apply in_app_iff in Hin as [Hin|Hin]; [exact (HdisjL b m Hin)|].
    apply AzBridgeH.in_map_wfr in Hin as (k' & Hin & ->). pose proof (HdisjF b k' Hin) as D. unfold AsVocab.FS in D |- *. exact D.
  - exact Hdef.
  - exact Hlast.
  - intros i Hi. unfold AsVocab.sh_lo, AsVocab.SB in Hsh0. exact (Hsh0 i Hi).
  - intros a Ha. apply Hshw. apply in_shadow_sh. exact Ha.
  - intros a Ha. apply changed_w. apply Hch. exact Ha.
  - exact (errno_kept_w _ _ Hek).
  - exact Hscr.
  - exists ((u f, k) :: FF). split; [| exact HA']. cbn [map]. unfold AzBridgeH.wfr at 1. cbn [fst snd]. unfold AsVocab.FS. reflexivity.
  - exact (nmodel_of_mat _ _ Hh Hmat).
Qed.


Lemma h_fakerel_wj : FREL -> h_fakerel SEGS G FXOK RZg AINVH0.
Proof.
  intros FR p rs fx R0 M mdl L LF F1 F2 B C K f n flag T HFX Hh (FF & HLF & HA) HLf Hlast Hfw Hrs Hflag Hp0 Hp4 Hpost. subst LF.
  destruct (AzBridgeH.map_wfr_split FF F1 f n F2 HLf) as (G1 & k & G2 & EFF & EF1 & EF2 & En). subst FF F1 F2 n.
  assert (Hk : 0 <= k) by (eapply (FF_classes None); [exact HA | apply in_app_iff; right; left; reflexivity]).
  assert (HFS : AsVocab.FS k = 64 * 2 ^ k) by reflexivity.
  apply (katD_g _ _ T (FR None p rs fx R0 M mdl L (G1 ++ (f, k) :: G2) G1 G2 B C K f k flag HFX Hh HA eq_refl Hlast Hfw Hrs Hflag Hp0 Hp4)).
  intros c' (M' & mdl' & -> & Hch & HA' & Hmat).
  apply (Hpost M' mdl').
  - intros a Ha. destruct (Hch a Ha) as (Hu & Hr & Hni & Hnv). split; [exact Hu|]. split; [exact Hr|]. split; [rewrite G_imglo, G_hi; exact Hni|].
    intros Hv. apply Hnv. apply (nvisible_app_visible L (G1 ++ G2)). rewrite map_app. exact Hv.
  - exists (G1 ++ G2). split; [rewrite map_app; reflexivity | exact HA'].
  - exact (nmodel_of_mat _ _ Hh Hmat).
Qed.

(* [comment removed for export] *)
Lemma fpc_w : forall M v lo d, AX2S.fpc M v lo d -> AsVocab.fpc M v lo d.
Proof.
  intros M v lo d H. induction H as [v lo d ST | v lo d w H16 H8 HP DEF RD CH IH].
  - apply AsVocab.fpc_stop. unfold AsVocab.PTRHI. unfold AX2S.FPC_HI in ST. exact ST.
  - apply (AsVocab.fpc_frame M v lo d w); try assumption.
Qed.
Lemma fpc_stop_w : forall M v lo, v <= lo -> FPCw M v lo.
Proof. intros M v lo H. unfold FPCw. apply AsVocab.fpc_stop. left. exact H. Qed.
Lemma fpc_kfpc_w : forall M v lo, AX2S.fpc M v lo DMAXN -> FPCw M v lo.
Proof. intros M v lo H. unfold FPCw. exact (fpc_w _ _ _ _ H). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section Op.   (* [comment removed for export] *)
Variable n_e : Z.
Variable L_e : list (Z * Z).     (* [comment removed for export] *)

(* [comment removed for export] *)
Definition hole_op (h : option Z) (L : list (Z * Z)) : Prop := h = None \/ (h = Some n_e /\ Permutation L L_e).
Definition AINVH_op (L LF : list (Z * Z)) (B C K : Z) (M : word -> option byte) (mdl : Model) : Prop :=
  exists h, hole_op h L /\ AINVw (AAINVH h) L LF B C K M mdl.

Lemma AINVH_op_of : forall h L LF B C K M mdl, hole_op h L -> AINVw (AAINVH h) L LF B C K M mdl -> AINVH_op L LF B C K M mdl.
Proof. intros h L LF B C K M mdl Hh H. exists h. split; assumption. Qed.

(* [comment removed for export] *)
Lemma malloc_pre_wh : forall X h fpcreq fx R0 M mdl L FF B C K ret n sp stk,
  hmalloc_pre SEGS G FXOK X FPCw fpcreq fx R0 M mdl L (map AzBridgeH.wfr FF) B C K ret n sp stk ->
  AAINVH h L FF B C K M mdl -> AsIface3.hole_ok h n ->
  AsIface3.malloc_pre SEGS FXOK IA AAINVH h stk fpcreq fx R0 M mdl L FF B C K ret n sp.
Proof.
  intros X h fpcreq fx R0 M mdl L FF B C K ret n sp stk (HFX & Hh & _ & Hpre & Hn & Hnr & Hfpc & HB & HCc & HK) HA Hho.
  unfold AsIface3.malloc_pre.
  assert (E10 : (10%bv : bv 5) = Z_to_bv 5 10) by (apply bv_eq; reflexivity).
  assert (E8 : (8%bv : bv 5) = Z_to_bv 5 8) by (apply bv_eq; reflexivity).
  rewrite E10, E8.
  split; [exact Hh|]. split; [exact HFX|]. split; [exact HA|]. split; [exact Hho|]. split; [exact (call_pre_w _ _ _ _ _ Hpre)|].
  split; [exact Hn|]. split; [unfold AsVocab.NMAX; unfold AzIface.NMAX in Hnr; exact Hnr|].
  split; [intros Hq; exact (Hfpc Hq)|].
  unfold AsVocab.MBLK, AsVocab.GBUDGET, AsVocab.LMAX, AsVocab.kcost_malloc, AsVocab.EVT, AsVocab.KCAP.
  unfold AzIface.mcost, AzIface.MBLK, AzIface.GBUDGET, AzIface.MCNT, AzIface.GCOUNT, AzIface.LMAX, AzIface.kcost, AzIface.EVT, AzIface.GKCAP in HB, HCc, HK. lia.
Qed.

(* [comment removed for export] *)
Lemma hpost_ok_mono : forall (X Y : list (Z * Z) -> list (Z * Z) -> Z -> Z -> Z -> (word -> option byte) -> Model -> Prop)
  R M mdl L LF B C K n sp stk fx' R' M' mdl' (p : word),
  (X ((u p, n) :: L) LF (B + mcost n) (C + MCNT) (K + kcost n) M' mdl' -> Y ((u p, n) :: L) LF (B + mcost n) (C + MCNT) (K + kcost n) M' mdl') ->
  hmalloc_post_ok SEGS G FXOK X R M mdl L LF B C K n sp stk fx' R' M' mdl' p ->
  hmalloc_post_ok SEGS G FXOK Y R M mdl L LF B C K n sp stk fx' R' M' mdl' p.
Proof.
  intros X Y R M mdl L LF B C K n sp stk fx' R' M' mdl' p HXY
         (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11 & H12 & H13 & HA & H16).
  unfold hmalloc_post_ok. repeat (split; [assumption|]). split; [apply HXY; exact HA | exact H16].
Qed.




End Op.

(* [comment removed for export] *)
Lemma h_malloc_live_wj : forall n_e L_e stk entry,
  MKATW stk entry true ->
  AzOpNewK.h_malloc_live_on SEGS (fun n L => n = n_e /\ L = L_e) G FXOK RZg (AINVH_op n_e L_e) FPCw stk entry.
Proof.
  intros n_e L_e stk entry MS fx R0 M mdl L LF B C K ret n sp T HN Hpre HT0 Hok. cbv beta in HN. destruct HN as [-> ->].
  pose proof Hpre as (HFX & Hh & (h & Hho & FF & HLF & HA) & _). subst LF.
  assert (HOK : AsIface3.hole_ok h n_e) by (destruct Hho as [->|[-> _]]; [left | right]; reflexivity).
  apply (katwD_ok_g _ _ _ T (MS h fx R0 M mdl L_e FF B C K ret n_e sp (malloc_pre_wh _ h _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hpre HA HOK))).
  intros c' Hc'. destruct (malloc_ok_w stk R0 M mdl L_e FF B C K ret n_e sp c' Hh Hc') as (fx' & R' & M' & mdl' & p & -> & Hpost).
  apply (Hok fx' R' M' mdl' p). revert Hpost. apply hpost_ok_mono.
  intros HX. exact (AINVH_op_of n_e L_e None _ _ _ _ _ _ _ (or_introl eq_refl) HX).
Qed.
End GenRZ.













(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section L.
Variable SWIN : list (Z * Z).
Hypothesis SWIN_ok : AsVocab.as_wins_ok IA SWIN.

Lemma sbyte_small : forall k : byte, u k <= 7 -> bv_signed k = u k.
Proof.
  intros k Hk. pose proof (bv_unsigned_in_range _ k) as Hr. change (bv_modulus 8) with 256 in Hr.
  unfold bv_signed, bv_swrap, bv_wrap, bv_half_modulus. change (bv_modulus 8) with 256. change (256 / 2) with 128.
  rewrite Z.mod_small by lia. lia.
Qed.

Lemma nmem_w : forall a, nmem a -> AsVocab.addr_is_mem a.
Proof. intros a H. unfold AsVocab.addr_is_mem, AsVocab.AS_HEAPLO, AsVocab.PTRHI, AsVocab.SB. unfold nmem, KHI, SB, two47 in H. lia. Qed.

Lemma nacc_w : forall M b n, nacc M b n -> AsVocab.accessible M b n.
Proof.
  intros M b n H a Ha. destruct (H a Ha) as (bt & Hbt & Hv). unfold AsVocab.sbyte, AsVocab.sh_lo, AsVocab.SB. unfold SB in Hbt. rewrite Hbt.
  destruct Hv as [Hz|Hnz]; [left | right]; rewrite sbyte_small by lia; lia.
Qed.

Lemma hshvis_w : forall L FF b n, hshvis G L (map AzBridgeH.wfr FF) b n -> AsVocab.shadow_visible IA L FF b n.
Proof.
  intros L FF b n H z Hz. destruct (H z Hz) as [Hb|[Hs|Hi]].
  - apply in_blocks_app in Hb as [Hb|Hf]; [left; exact Hb|]. right; left.
    apply in_blocks_fusable in Hf as (f & m & Hin & Hfz). apply AzBridgeH.in_map_wfr in Hin as (k & Hin & ->). exists f, k. split; [exact Hin | lia].
  - right; right; left. unfold AsVocab.PTRHI. unfold two47 in Hs. exact Hs.
  - right; right; right. rewrite <- G_imglo, <- G_hi. pose proof G_ro_img. lia.
Qed.

Lemma hdst_w : forall L FF (a : word), hdst SWIN L (map AzBridgeH.wfr FF) a -> AsVocab.as_app_owned IA SWIN L FF (u a).
Proof.
  intros L FF a H. unfold AsVocab.as_app_owned. destruct H as [Hb|[Hf|[Hc|Hw]]].
  - left. exact Hb.
  - right; left. apply in_blocks_fusable in Hf as (f & m & Hin & Hfz). apply AzBridgeH.in_map_wfr in Hin as (k & Hin & ->). exists f, k. split; [exact Hin | lia].
  - right; right; left. exact Hc.
  - right; right; right; left. exact Hw.
Qed.

Lemma off_scratch_w : forall sp lo hi, 0 <= lo -> hi <= two47 ->
  (forall a : word, lo <= u a < hi -> ~ scratch sp AzIface.MSTK_M a) -> AsIface3.off_scratch sp lo hi.
Proof.
  intros sp lo hi H0 H1 H a Ha Hs. unfold two47 in H1.
  apply (H (Z_to_bv 64 a)); unfold scratch; rewrite u64_lit by lia; [exact Ha|]. unfold AsVocab.MSTK_M in Hs. unfold AzIface.MSTK_M. exact Hs.
Qed.

Lemma nmem2_bounds : forall a b, nmem a -> nmem b -> 0 <= a /\ b <= two47.
Proof. intros a b Ha Hb. unfold nmem, KHI, SB, two47 in *. lia. Qed.

#[local] Notation MCPY := (AsIface3.MEMCPY_AT SEGS FXOK IA AAINVH).
#[local] Notation MSET := (AsIface3.MEMSET_AT SEGS FXOK IA AAINVH).
#[local] Notation MMOV := (AsIface3.MEMMOVE_AT SEGS FXOK IA AAINVH).
#[local] Notation MSTR := (AsIface3.STRLEN_AT SEGS FXOK IA AAINVH).

Ltac pre_regs :=
  assert (E10 : (10%bv : bv 5) = Z_to_bv 5 10) by (apply bv_eq; reflexivity);
  assert (E11 : (11%bv : bv 5) = Z_to_bv 5 11) by (apply bv_eq; reflexivity);
  assert (E12 : (12%bv : bv 5) = Z_to_bv 5 12) by (apply bv_eq; reflexivity).

(* [comment removed for export] *)
Hypothesis G_memcpy : g_memcpy G = AsVocab.AsCells.ia_memcpy_icpt IA.
Hypothesis G_amemcpy : g_amemcpy G = AsVocab.AsCells.ia_asan_memcpy IA.
Hypothesis G_memset : g_memset G = AsVocab.AsCells.ia_memset_icpt IA.
Hypothesis G_amemset : g_amemset G = AsVocab.AsCells.ia_asan_memset IA.
Hypothesis G_memmove : g_memmove G = AsVocab.AsCells.ia_memmove_icpt IA.
Hypothesis G_amemmove : g_amemmove G = AsVocab.AsCells.ia_asan_memmove IA.

(* [comment removed for export] *)
Section GenRZL.
Variable RZg : GPS.rz_t.
Hypothesis RZg_kc : forall T, AsIface3.AsK.kclosedD SEGS (fun c => RZg c T).

(* [comment removed for export] *)
Lemma mem_post_wj : forall R0 M mdl L FF B C K ret sp dst n (bytes : nat -> option byte) T c',
  m_halted mdl = None ->
  hmem_post SEGS FXOK RZg AINVH0 R0 M mdl L (map AzBridgeH.wfr FF) B C K ret sp dst n bytes T ->
  AsIface3.mem_post SEGS FXOK AAINVH None R0 M mdl L FF B C K ret sp dst n (fun i => bytes (Z.to_nat i)) c' ->
  RZg c' T.
Proof.
  intros R0 M mdl L FF B C K ret sp dst n bytes T c' Hh Hpost (fx' & R' & M' & mdl' & -> & HFX' & Hkept & Ha0 & Hby & Hch & Hscr & HA' & Hmat).
  assert (E10 : (10%bv : bv 5) = Z_to_bv 5 10) by (apply bv_eq; reflexivity). rewrite E10 in Ha0.
  apply (Hpost fx' R' M' mdl' HFX' (regs_kept_w _ _ Hkept) Ha0).
  - intros i Hi. rewrite (Hby (Z.of_nat i)) by lia. rewrite Nat2Z.id. reflexivity.
  - intros a Ha. destruct (Hch a Ha) as [X|X]; [left; exact X | right]. unfold scratch, AzIface.MSTK_M. unfold AsVocab.MSTK_M in X. exact X.
  - exact Hscr.
  - exists FF. split; [reflexivity | exact HA'].
  - exact (nmodel_of_mat _ _ Hh Hmat).
Qed.

Lemma h_copy_wj : forall entry, MCPY entry -> h_copy_at SEGS SWIN G FXOK RZg AINVH0 entry.
Proof.
  intros entry MC fx R0 M mdl L LF B C K ret sp dst src n bs T HFX Hh (FF & HLF & HA) Hpre R10 R11 R12 Hap
         (NB & M1 & M2 & ACC & SHV & OWN) (M3 & M4 & ACC2 & SHV2 & RD) SC1 SC2 Hpost. subst LF.
  pre_regs. destruct (nmem2_bounds _ _ M1 M2) as [D0 D1]. destruct (nmem2_bounds _ _ M3 M4) as [S0 S1].
  refine (katD_g RZg RZg_kc _ _ T (MC None fx R0 M mdl L FF SWIN B C K ret sp dst src n bs HFX Hh HA (call_pre_w _ _ _ _ _ Hpre) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _);
    try (rewrite ?E10, ?E11, ?E12; first [exact R10 | exact R11 | exact R12]).
  - unfold AsVocab.NMAX. exact NB.
  - right. exact Hap.
  - exact (nmem_w _ M1). - exact (nmem_w _ M2). - exact (nmem_w _ M3). - exact (nmem_w _ M4).
  - exact (nacc_w _ _ _ ACC2). - exact (nacc_w _ _ _ ACC).
  - exact (hshvis_w _ _ _ _ SHV2). - exact (hshvis_w _ _ _ _ SHV).
  - exact RD.
  - split; [exact SWIN_ok|]. intros a Ha. pose proof (OWN (Z_to_bv 64 a) ltac:(rewrite u64_lit by (unfold two47 in *; lia); exact Ha)) as [Ho _].
    rewrite <- (u64_lit a) by (unfold two47 in *; lia). exact (hdst_w _ _ _ Ho).
  - exact (off_scratch_w _ _ _ D0 D1 SC1).
  - exact (off_scratch_w _ _ _ S0 S1 SC2).
  - intros a Ha. exact (proj2 (OWN a Ha)).
  - intros c' Hc'. exact (mem_post_wj R0 M mdl L FF B C K ret sp dst n (fun i => Some (nth i bs (Z_to_bv 8 0))) T c' Hh Hpost Hc').
Qed.

Lemma h_move_wj : forall entry, MMOV entry -> h_move_at SEGS SWIN G FXOK RZg AINVH0 entry.
Proof.
  intros entry MC fx R0 M mdl L LF B C K ret sp dst src n bs T HFX Hh (FF & HLF & HA) Hpre R10 R11 R12 Hmv
         (NB & M1 & M2 & ACC & SHV & OWN) (M3 & M4 & ACC2 & SHV2 & RD) SC1 SC2 Hpost. subst LF.
  pre_regs. destruct (nmem2_bounds _ _ M1 M2) as [D0 D1]. destruct (nmem2_bounds _ _ M3 M4) as [S0 S1].
  refine (katD_g RZg RZg_kc _ _ T (MC None fx R0 M mdl L FF SWIN B C K ret sp dst src n bs HFX Hh HA (call_pre_w _ _ _ _ _ Hpre) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _);
    try (rewrite ?E10, ?E11, ?E12; first [exact R10 | exact R11 | exact R12]).
  - unfold AsVocab.NMAX. exact NB.
  - exact (nmem_w _ M1). - exact (nmem_w _ M2). - exact (nmem_w _ M3). - exact (nmem_w _ M4).
  - exact (nacc_w _ _ _ ACC2). - exact (nacc_w _ _ _ ACC).
  - exact (hshvis_w _ _ _ _ SHV2). - exact (hshvis_w _ _ _ _ SHV).
  - exact RD.
  - exact Hmv.
  - split; [exact SWIN_ok|]. intros a Ha. pose proof (OWN (Z_to_bv 64 a) ltac:(rewrite u64_lit by (unfold two47 in *; lia); exact Ha)) as [Ho _].
    rewrite <- (u64_lit a) by (unfold two47 in *; lia). exact (hdst_w _ _ _ Ho).
  - exact (off_scratch_w _ _ _ D0 D1 SC1).
  - exact (off_scratch_w _ _ _ S0 S1 SC2).
  - intros a Ha. exact (proj2 (OWN a Ha)).
  - intros c' Hc'. exact (mem_post_wj R0 M mdl L FF B C K ret sp dst n (fun i => Some (nth i bs (Z_to_bv 8 0))) T c' Hh Hpost Hc').
Qed.

Lemma h_fill_wj : forall entry, MSET entry -> h_fill_at SEGS SWIN G FXOK RZg AINVH0 entry.
Proof.
  intros entry MC fx R0 M mdl L LF B C K ret sp dst c n T HFX Hh (FF & HLF & HA) Hpre R10 R11 R12
         (NB & M1 & M2 & ACC & SHV & OWN) SC1 Hpost. subst LF.
  pre_regs. destruct (nmem2_bounds _ _ M1 M2) as [D0 D1].
  refine (katD_g RZg RZg_kc _ _ T (MC None fx R0 M mdl L FF SWIN B C K ret sp dst c n HFX Hh HA (call_pre_w _ _ _ _ _ Hpre) _ _ _ _ _ _ _ _ _ _ _) _);
    try (rewrite ?E10, ?E11, ?E12; first [exact R10 | exact R11 | exact R12]).
  - unfold AsVocab.NMAX. exact NB.
  - exact (nmem_w _ M1). - exact (nmem_w _ M2).
  - exact (nacc_w _ _ _ ACC).
  - exact (hshvis_w _ _ _ _ SHV).
  - split; [exact SWIN_ok|]. intros a Ha. pose proof (OWN (Z_to_bv 64 a) ltac:(rewrite u64_lit by (unfold two47 in *; lia); exact Ha)) as [Ho _].
    rewrite <- (u64_lit a) by (unfold two47 in *; lia). exact (hdst_w _ _ _ Ho).
  - exact (off_scratch_w _ _ _ D0 D1 SC1).
  - intros a Ha. exact (proj2 (OWN a Ha)).
  - intros c' Hc'. exact (mem_post_wj R0 M mdl L FF B C K ret sp dst n (fun _ => Some (Z_to_bv 8 c)) T c' Hh Hpost Hc').
Qed.

Lemma h_strlen_wj : forall entry, MSTR entry -> h_strlen_at SEGS G FXOK RZg AINVH0 entry.
Proof.
  intros entry MC fx R0 M mdl L LF B C K ret sp s len T HFX Hh (FF & HLF & HA) Hpre R10
         (L0 & L1 & M1 & M2 & ACC & SHV & BY & NUL & HULL) SC Hpost. subst LF.
  pre_regs. destruct (nmem2_bounds _ _ M1 M2) as [D0 D1].
  refine (katD_g RZg RZg_kc _ _ T (MC None fx R0 M mdl L FF B C K ret sp s len HFX Hh HA (call_pre_w _ _ _ _ _ Hpre) _ _ _ _ _ _ _ _ _ _ _) _);
    try (rewrite ?E10, ?E11, ?E12; first [exact R10 | exact R11 | exact R12]).
  - exact L0.
  - unfold AsVocab.NMAX. exact L1.
  - exact BY.
  - exact NUL.
  - exact HULL.
  - exact (nmem_w _ M1). - exact (nmem_w _ M2).
  - exact (nacc_w _ _ _ ACC).
  - exact (hshvis_w _ _ _ _ SHV).
  - exact (off_scratch_w _ _ _ D0 D1 SC).
  - intros c' (fx' & R' & M' & mdl' & -> & HFX' & Hkept & Ha0 & Hch & Hscr & HA' & Hmat).
    rewrite E10 in Ha0.
    apply (Hpost fx' R' M' mdl' HFX' (regs_kept_w _ _ Hkept) Ha0).
    + intros a Ha. unfold scratch, AzIface.MSTK_M. unfold AsVocab.MSTK_M in Hch. exact (Hch a Ha).
    + exact Hscr.
    + exists FF. split; [reflexivity | exact HA'].
    + exact (nmodel_of_mat _ _ Hh Hmat).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section OpL.   (* [comment removed for export] *)
Variable n_e : Z.
Variable L_e : list (Z * Z).


End OpL.

(* [comment removed for export] *)
Hypothesis H_strlen_entry_j : h_strlen_at SEGS G FXOK RZg AINVH0 (AsVocab.AsCells.ia_strlen_icpt IA) -> h_strlen_at SEGS G FXOK RZg AINVH0 (g_strlen G).

Theorem lcontracts_of_as_j : lcontracts SEGS SWIN G FXOK RZg AINVH0.
Proof.
  destruct ASC as [Wk Mk Mkt Ma Mat Fr Frt Od Ods Sk Frl Mc Amc Ms Ams Mm Amm Sl].
  constructor; rewrite ?G_memcpy, ?G_amemcpy, ?G_memset, ?G_amemset, ?G_memmove, ?G_amemmove.
  - exact (h_copy_wj _ Mc).
  - exact (h_copy_wj _ Amc).
  - exact (h_fill_wj _ Ms).
  - exact (h_fill_wj _ Ams).
  - exact (h_move_wj _ Mm).
  - exact (h_move_wj _ Amm).
  - exact (H_strlen_entry_j (h_strlen_wj _ Sl)).
Qed.
End GenRZL.











Hypothesis H_strlen_entry : h_strlen_at SEGS G FXOK RZ AINVH0 (AsVocab.AsCells.ia_strlen_icpt IA) -> h_strlen_at SEGS G FXOK RZ AINVH0 (g_strlen G).

Hypothesis H_strlen_entry_f :
  h_strlen_at SEGS G FXOK (realizes SEGS) AINVH0 (AsVocab.AsCells.ia_strlen_icpt IA) -> h_strlen_at SEGS G FXOK (realizes SEGS) AINVH0 (g_strlen G).

End L.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition FRESHw (L LF : list (Z * Z)) (B C K : Z) (M : word -> option byte) (mdl : Model) (n : Z) : Prop :=
  exists FF, LF = map AzBridgeH.wfr FF /\ FRESH L FF B C K M mdl n.

(* [comment removed for export] *)
Section GenRZC.   (* [comment removed for export] *)
Variable RZg : GPS.rz_t.
Hypothesis RZg_kc : forall T, AsIface3.AsK.kclosedD SEGS (fun c => RZg c T).
Theorem hcontracts_core_of_as_j : hcontracts_core SEGS G FXOK RZg AINVH0 AINVHN FPCw FRESHw.
Proof.
  destruct ASC as [Wk Mk Mkt Ma Mat Fr Frt Od Ods Sk Frl Mc Amc Ms Ams Mm Amm Sl].
  constructor.
  - rewrite G_malloc. exact (h_malloc1_wj RZg RZg_kc _ _ Ma).
  - rewrite G_malloc_thunk. exact (h_malloc1_wj RZg RZg_kc _ _ Mat).
  - rewrite G_malloc. exact (h_malloc_wj RZg RZg_kc _ _ Mk).
  - rewrite G_malloc_thunk. exact (h_malloc_wj RZg RZg_kc _ _ Mkt).
  - rewrite G_free. exact (h_free_wj RZg RZg_kc _ _ Fr).
  - rewrite G_free_thunk. exact (h_free_wj RZg RZg_kc _ _ Frt).
  - rewrite G_opdel. exact (h_free_wj RZg RZg_kc _ _ Od).
  - rewrite G_opdel_sized. exact (h_free_wj RZg RZg_kc _ _ Ods).
  - intros k Hk. exact (h_stkmal_wj RZg RZg_kc k Hk (Sk k ltac:(unfold AsVocab.KMAXCLASS; lia))).
  - exact (h_fakerel_wj RZg RZg_kc Frl).
  - exact fpc_stop_w.
  - exact fpc_kfpc_w.
Qed.
Hypothesis OPNEW_j : h_alloc1_at SEGS G FXOK RZg AINVH0 FPCw (hopnew_x SEGS G) MSTK_N (g_opnew G).

End GenRZC.



Hypothesis OPNEW : h_alloc1_at SEGS G FXOK RZ AINVH0 FPCw (hopnew_x SEGS G) MSTK_N (g_opnew G).


Hypothesis OPNEW_f : h_alloc1_at SEGS G FXOK (realizes SEGS) AINVH0 FPCw (hopnew_x SEGS G) MSTK_N (g_opnew G).


End BridgeC.
