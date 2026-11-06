(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.glaze.binary_reflection.lib Require BvWfKernel.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require WdZS.
#[local] Ltac Zify.zify ::= WdZS.wd_zs_stock.   (* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape OSSVerify.Proofs.glaze.binary_reflection.lib.Spec4 OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3 OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3B OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3Sound OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymRun3 OSSVerify.Proofs.glaze.binary_reflection.lib.AzPlanCore OSSVerify.Proofs.glaze.binary_reflection.lib.AzPlan OSSVerify.Proofs.glaze.binary_reflection.lib.AzAPS OSSVerify.Proofs.glaze.binary_reflection.lib.AzGPS OSSVerify.Proofs.glaze.binary_reflection.lib.AzIface OSSVerify.Proofs.glaze.binary_reflection.lib.AzContracts OSSVerify.Proofs.glaze.binary_reflection.lib.AzKnowLib OSSVerify.Proofs.glaze.binary_reflection.lib.AzNSpec OSSVerify.Proofs.glaze.binary_reflection.lib.AzFrame OSSVerify.Proofs.glaze.binary_reflection.lib.AzNodesAlloc3 OSSVerify.Proofs.glaze.binary_reflection.lib.AzFrameAlloc OSSVerify.Proofs.glaze.binary_reflection.lib.AzFrameAllocNM OSSVerify.Proofs.glaze.binary_reflection.lib.AzBridgeLG OSSVerify.Proofs.glaze.binary_reflection.lib.AzBridgeH OSSVerify.Proofs.glaze.binary_reflection.lib.AzBridgeC3 OSSVerify.Proofs.glaze.binary_reflection.lib.AzBridgeE3 OSSVerify.Proofs.glaze.binary_reflection.lib.AzBridgeM2 OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst. Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape.ShapeRel OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape.ShapeRetry OSSVerify.Proofs.glaze.binary_reflection.lib.Spec4.AgentLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3 OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3B OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3Sound OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymRun3 OSSVerify.Proofs.glaze.binary_reflection.lib.AzPlanCore OSSVerify.Proofs.glaze.binary_reflection.lib.AzPlan OSSVerify.Proofs.glaze.binary_reflection.lib.AzAPS OSSVerify.Proofs.glaze.binary_reflection.lib.AzGPS OSSVerify.Proofs.glaze.binary_reflection.lib.AzIface OSSVerify.Proofs.glaze.binary_reflection.lib.AzContracts OSSVerify.Proofs.glaze.binary_reflection.lib.AzKnowLib OSSVerify.Proofs.glaze.binary_reflection.lib.AzNSpec OSSVerify.Proofs.glaze.binary_reflection.lib.AzFrame OSSVerify.Proofs.glaze.binary_reflection.lib.AzNodesAlloc3 OSSVerify.Proofs.glaze.binary_reflection.lib.AzFrameAlloc OSSVerify.Proofs.glaze.binary_reflection.lib.AzFrameAllocNM OSSVerify.Proofs.glaze.binary_reflection.lib.AzBridgeLG OSSVerify.Proofs.glaze.binary_reflection.lib.AzBridgeH OSSVerify.Proofs.glaze.binary_reflection.lib.AzBridgeC3 OSSVerify.Proofs.glaze.binary_reflection.lib.AzBridgeE3 OSSVerify.Proofs.glaze.binary_reflection.lib.AzBridgeM2 OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsIfaceNM3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFFam.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AX2S. Import AP. Import GPS.
Open Scope Z_scope.

#[local] Notation u := bv_unsigned.

Section PR.
Context {RC : run_ceil}.
Context {SFL : stk_floor}.
Variable bt : AsAinvDefs3.as_boot.
Variable Q : AsAinvDefs3.ast -> Prop.   (* [comment removed for export] *)
#[local] Notation IA := (AsAinvDefs3.bt_ia bt).
#[local] Notation PRX := (AsAllocFFam.AsAinvPrist3.AAINV_QX bt Q).
Variable SEGS : list Segment.
Variable FXOK : FX -> Prop.
Hypothesis ASCP : AsIfaceNM3.AsIfacePR3.as_contracts_pr SEGS FXOK IA PRX (AsAinvDefs3.bt_fs bt).
Variable G : gtable.
Hypothesis G_imglo : g_img_lo G = AsVocab.AsCells.ia_img_lo IA.
Hypothesis G_hi : g_img_hi G = AsVocab.AsCells.ia_img_hi IA.
Hypothesis G_ro_img : g_img_lo G <= g_ro_lo G /\ g_ro_lo G <= g_ro_hi G <= g_img_hi G.
Hypothesis G_img_al : 0 <= g_img_lo G /\ g_img_lo G mod 8 = 0 /\ g_img_hi G mod 8 = 0.
Hypothesis G_img_shlo : g_img_hi G <= SHMAPLO.
Hypothesis G_priv : forall lo hi, In (lo, hi) (g_priv G) -> g_ro_hi G <= lo /\ hi <= g_img_hi G.
Hypothesis G_privs : forall z, AsVocab.in_wins (AsVocab.AsCells.ia_priv IA) z -> in_wins (g_priv G) z.
Hypothesis G_tp : g_tp G = AsVocab.AsCells.ia_tp IA.
Hypothesis G_errno : g_errno G = AsVocab.ia_errno IA.
Hypothesis G_errno_img : g_ro_hi G <= g_errno G /\ g_errno G + 4 <= g_img_hi G.
Hypothesis G_malloc : g_malloc G = AsVocab.AsCells.ia_malloc IA.
Hypothesis G_malloc_thunk : g_malloc_thunk G = AsVocab.AsCells.ia_malloc_thunk IA.
Hypothesis G_free : g_free G = AsVocab.AsCells.ia_free IA.
Hypothesis G_free_thunk : g_free_thunk G = AsVocab.AsCells.ia_free_thunk IA.
Hypothesis G_opdel : g_opdel G = AsVocab.AsCells.ia_opdel IA.
Hypothesis G_opdel_sized : g_opdel_sized G = AsVocab.AsCells.ia_opdel_sz IA.
Hypothesis G_stkmal : forall k, 0 <= k <= 3 -> g_stkmal G k = AsVocab.AsCells.ia_stkmal IA k.
Hypothesis G_memcpy : g_memcpy G = AsVocab.AsCells.ia_memcpy_icpt IA.
Hypothesis G_amemcpy : g_amemcpy G = AsVocab.AsCells.ia_asan_memcpy IA.
Hypothesis G_memset : g_memset G = AsVocab.AsCells.ia_memset_icpt IA.
Hypothesis G_amemset : g_amemset G = AsVocab.AsCells.ia_asan_memset IA.
Hypothesis G_memmove : g_memmove G = AsVocab.AsCells.ia_memmove_icpt IA.
Hypothesis G_amemmove : g_amemmove G = AsVocab.AsCells.ia_asan_memmove IA.
Hypothesis G_newh_img : g_img_lo G <= g_newh_got G /\ g_newh_got G + 8 <= g_img_hi G /\ g_img_lo G <= g_newh_cell G /\ g_newh_cell G + 8 <= g_img_hi G.
Hypothesis SEGS_in_hull_out : forall a : word, ~ (g_img_lo G <= u a < g_img_hi G) -> find_segment SEGS (u a) 1 = None.
Hypothesis SEGS_wx : wx_segs_nowrap SEGS.
Hypothesis SEGS_wr : AzCallLib.GCL.segs_wr_ok SEGS.
Hypothesis ROM_ok : forall x : word, g_ro_lo G <= u x -> u x < g_ro_hi G -> seg_rom SEGS x <> None.
Hypothesis RO_hi : g_ro_hi G < 2 ^ 64.
Variable SWIN : list (Z * Z).
Hypothesis SWIN_ok : AsVocab.as_wins_ok IA SWIN.
Hypothesis SWIN_img : forall lo hi, In (lo, hi) SWIN -> g_ro_hi G <= lo /\ hi <= g_img_hi G /\ (forall plo phi, In (plo, phi) (g_priv G) -> hi <= plo \/ phi <= lo).

(* [comment removed for export] *)
Definition AAINV_PL (h : option Z) : list (Z * Z) -> list (Z * Z) -> Z -> Z -> Z -> (word -> option byte) -> Model -> Prop :=
  AzBridgeLG.AAINV_LG (PRX h).
Definition AINVH_pr : list (Z * Z) -> list (Z * Z) -> Z -> Z -> Z -> (word -> option byte) -> Model -> Prop :=
  AzBridgeH.AINVw (AAINV_PL None).


Let AAP := AsAllocFFam.AsAinvPrist3.AAINV_QX_props bt Q.
Lemma PR_zone : forall h Lc FF B C K M mdl b n, PRX h Lc FF B C K M mdl -> In (b, n) Lc -> AsVocab.ablk_ok IA b n /\ 1 <= n /\ b mod 16 = 0.
Proof. intros h Lc FF B C K M mdl b n HA Hin. exact (AsVocab.aap_zone _ _ _ _ (AAP h) _ _ _ _ _ _ _ b n HA Hin). Qed.
Lemma IMG_LO_pr : AsVocab.AsCells.ia_img_hi IA <= AsVocab.AS_LO.
Proof. rewrite <- G_hi. unfold AsVocab.AS_LO. unfold SHMAPLO in G_img_shlo. exact G_img_shlo. Qed.
Lemma PRIV_IMG_pr : forall z, AsVocab.in_wins (AsVocab.AsCells.ia_priv IA) z -> z < AsVocab.AsCells.ia_img_hi IA.
Proof. intros z Hz. destruct (G_privs z Hz) as (lo & hi & Hin & Hr). destruct (G_priv lo hi Hin) as [_ P2]. rewrite <- G_hi. lia. Qed.
Lemma ERRNO_IMG_pr : AsVocab.ia_errno IA + 4 <= AsVocab.AsCells.ia_img_hi IA.
Proof. rewrite <- G_errno, <- G_hi. exact (proj2 G_errno_img). Qed.
Lemma SWIN_hi_pr : forall z, in_wins SWIN z -> z < g_img_hi G.
Proof. intros z Hz. rewrite G_hi. exact (proj2 (proj1 (SWIN_ok z Hz))). Qed.

Theorem hprops_h_pr : forall h, hprops SWIN G (AzBridgeH.SHC_bt bt) (AzBridgeH.AINVw (AAINV_PL h)).
Proof.
  intros h.
  apply (AzBridgeH.hprops_LG (PRX h) SWIN G (AzBridgeH.SHC_bt bt)
           (AzBridgeH.hprops_of_AAINV_props IA (PRX h) (AsAinvDefs3.bt_fs bt) (AsAinvDefs3.bt_segs bt) (AAP h) SWIN G G_imglo G_hi G_ro_img G_img_al G_errno_img SWIN_ok)
           G_ro_img G_img_al G_img_shlo SWIN_hi_pr).
  intros L LF B C K M mdl b n (FF & _ & HA) Hin. exact (proj1 (proj2 (PR_zone h _ _ _ _ _ _ _ b n HA Hin))).
Qed.
Theorem hprops_pr : hprops SWIN G (AzBridgeH.SHC_bt bt) AINVH_pr.
Proof. exact (hprops_h_pr None). Qed.

(* [comment removed for export] *)
Lemma AINVH_pr_bt : forall L LF B C K M mdl, AINVH_pr L LF B C K M mdl -> AzBridgeH.AINVH_bt bt L LF B C K M mdl.
Proof.
  intros L LF B C K M mdl (FF & HLF & (HA & HL)). exists FF. split; [exact HLF|]. split; [|exact HL].
  exact (AsAllocFFam.AsAinvPrist3.AAINV_QX_HS bt Q _ _ _ _ _ _ _ HA).
Qed.

(* [comment removed for export] *)
Definition PRc (_ : option Z) : list (Z * Z) -> list (Z * Z) -> Z -> Z -> Z -> (word -> option byte) -> Model -> Prop := PRX None.
Definition PLc (_ : option Z) : list (Z * Z) -> list (Z * Z) -> Z -> Z -> Z -> (word -> option byte) -> Model -> Prop := AAINV_PL None.
Lemma PRc_zone : forall h Lc FF B C K M mdl b n, PRc h Lc FF B C K M mdl -> In (b, n) Lc -> AsVocab.ablk_ok IA b n /\ 1 <= n /\ b mod 16 = 0.
Proof. intros h. exact (PR_zone None). Qed.

Lemma FF_classes_pr : forall (h : option Z) L FF B C K M mdl f k, PLc h L FF B C K M mdl -> In (f, k) FF -> 0 <= k.
Proof.
  intros h L FF B C K M mdl f k [HA _] Hin.
  pose proof (AsVocab.aap_fzone _ _ _ _ (AAP None) L FF B C K M mdl f k HA Hin) as (X & _). lia.
Qed.

Section GenRZ1.   (* [comment removed for export] *)
Variable RZg : GPS.rz_t.
Hypothesis RZg_kc : forall T, AsIface3.AsK.kclosedD SEGS (fun c => RZg c T).
Theorem hcontracts_nm_pr_j : hcontracts_nm SEGS G FXOK RZg AINVH_pr AzBridgeC3.FPCw.
Proof.
  destruct ASCP as [Ms Mst Fr Frt OD ODS Sk Frl Mc Amc Mset Ams Mm Amm Sl].
  assert (FL : forall entry, AsIfaceNM3.AsIfacePR3.FREE_KAT_N SEGS FXOK IA PRX AsVocab.MSTK_A entry -> AsIface3.FREE_KAT SEGS FXOK IA PLc AsVocab.MSTK_A entry).
  { intros entry FK. exact (AzBridgeLG.FREE_KAT_LG SEGS FXOK IA PRc PRc_zone IMG_LO_pr PRIV_IMG_pr ERRNO_IMG_pr AsVocab.MSTK_A entry ltac:(unfold AsVocab.MSTK_A; lia) (fun h => FK)). }
  constructor.
  - rewrite G_free. exact (AzBridgeC3.h_free_wj SEGS IA FXOK PLc G G_imglo G_hi G_ro_img G_tp G_errno G_privs RZg RZg_kc _ _ (FL _ Fr None)).
  - rewrite G_free_thunk. exact (AzBridgeC3.h_free_wj SEGS IA FXOK PLc G G_imglo G_hi G_ro_img G_tp G_errno G_privs RZg RZg_kc _ _ (FL _ Frt None)).
  - rewrite G_opdel. exact (AzBridgeC3.h_free_wj SEGS IA FXOK PLc G G_imglo G_hi G_ro_img G_tp G_errno G_privs RZg RZg_kc _ _ (FL _ OD None)).
  - rewrite G_opdel_sized. exact (AzBridgeC3.h_free_wj SEGS IA FXOK PLc G G_imglo G_hi G_ro_img G_tp G_errno G_privs RZg RZg_kc _ _ (FL _ ODS None)).
  - intros k Hk.
    exact (AzBridgeC3.h_stkmal_wj SEGS IA FXOK PLc (AsAinvDefs3.bt_fs bt) G G_imglo G_hi G_ro_img G_tp G_errno G_privs G_stkmal RZg RZg_kc k Hk
             (AzBridgeLG.STKMAL_LG SEGS FXOK IA PRc (AsAinvDefs3.bt_fs bt) PRc_zone IMG_LO_pr PRIV_IMG_pr ERRNO_IMG_pr k
                (fun h => Sk k ltac:(unfold AsVocab.KMAXCLASS; lia) None))).
  - exact (AzBridgeC3.h_fakerel_wj SEGS IA FXOK PLc G G_imglo G_hi G_ro_img FF_classes_pr RZg RZg_kc
             (AzBridgeLG.FAKEREL_LG SEGS FXOK IA PRc PRc_zone (fun h => Frl None))).
Qed.
End GenRZ1.



(* [comment removed for export] *)
Section GenRZ2.   (* [comment removed for export] *)
Variable RZg : GPS.rz_t.
Hypothesis RZg_kc : forall T, AsIface3.AsK.kclosedD SEGS (fun c => RZg c T).
Hypothesis H_strlen_entry_j :
  h_strlen_at SEGS G FXOK RZg AINVH_pr (AsVocab.AsCells.ia_strlen_icpt IA) -> h_strlen_at SEGS G FXOK RZg AINVH_pr (g_strlen G).

Theorem lcontracts_pr_j : lcontracts SEGS SWIN G FXOK RZg AINVH_pr.
Proof.
  destruct ASCP as [Ms Mst Fr Frt OD ODS Sk Frl Mc Amc Mset Ams Mm Amm Sl].
  constructor.
  - rewrite G_memcpy. exact (AzBridgeC3.h_copy_wj SEGS IA FXOK PLc G G_imglo G_hi G_ro_img G_tp SWIN SWIN_ok RZg RZg_kc _ (AzBridgeLG.MEMCPY_LG SEGS FXOK IA PRc PRc_zone _ (fun h => Mc None))).
  - rewrite G_amemcpy. exact (AzBridgeC3.h_copy_wj SEGS IA FXOK PLc G G_imglo G_hi G_ro_img G_tp SWIN SWIN_ok RZg RZg_kc _ (AzBridgeLG.MEMCPY_LG SEGS FXOK IA PRc PRc_zone _ (fun h => Amc None))).
  - rewrite G_memset. exact (AzBridgeC3.h_fill_wj SEGS IA FXOK PLc G G_imglo G_hi G_ro_img G_tp SWIN SWIN_ok RZg RZg_kc _ (AzBridgeLG.MEMSET_LG SEGS FXOK IA PRc PRc_zone _ (fun h => Mset None))).
  - rewrite G_amemset. exact (AzBridgeC3.h_fill_wj SEGS IA FXOK PLc G G_imglo G_hi G_ro_img G_tp SWIN SWIN_ok RZg RZg_kc _ (AzBridgeLG.MEMSET_LG SEGS FXOK IA PRc PRc_zone _ (fun h => Ams None))).
  - rewrite G_memmove. exact (AzBridgeC3.h_move_wj SEGS IA FXOK PLc G G_imglo G_hi G_ro_img G_tp SWIN SWIN_ok RZg RZg_kc _ (AzBridgeLG.MEMMOVE_LG SEGS FXOK IA PRc PRc_zone _ (fun h => Mm None))).
  - rewrite G_amemmove. exact (AzBridgeC3.h_move_wj SEGS IA FXOK PLc G G_imglo G_hi G_ro_img G_tp SWIN SWIN_ok RZg RZg_kc _ (AzBridgeLG.MEMMOVE_LG SEGS FXOK IA PRc PRc_zone _ (fun h => Amm None))).
  - exact (H_strlen_entry_j (AzBridgeC3.h_strlen_wj SEGS IA FXOK PLc G G_imglo G_hi G_ro_img G_tp RZg RZg_kc _ (AzBridgeLG.STRLEN_LG SEGS FXOK IA PRc PRc_zone _ (fun h => Sl None)))).
Qed.
End GenRZ2.
Hypothesis H_strlen_entry_pr :
  h_strlen_at SEGS G FXOK (rrealizes SEGS) AINVH_pr (AsVocab.AsCells.ia_strlen_icpt IA) -> h_strlen_at SEGS G FXOK (rrealizes SEGS) AINVH_pr (g_strlen G).

Hypothesis H_strlen_entry_pr_f :
  h_strlen_at SEGS G FXOK (realizes SEGS) AINVH_pr (AsVocab.AsCells.ia_strlen_icpt IA) -> h_strlen_at SEGS G FXOK (realizes SEGS) AINVH_pr (g_strlen G).


(* [comment removed for export] *)
Definition FRESHsec (L LF : list (Z * Z)) (B C K : Z) (M : word -> option byte) (mdl : Model) (n : Z) : Prop := 64512 < n.

Lemma MALLOC_ALT_SEC_LG : forall stk entry fpc, 0 <= stk ->
  AsIfaceNM3.AsIfacePR3.MALLOC_ALT_SEC SEGS FXOK IA PRX stk entry fpc -> AsIfaceNM3.AsIfacePR3.MALLOC_ALT_SEC SEGS FXOK IA AAINV_PL stk entry fpc.
Proof.
  intros stk entry fpc Hstk MK fx R M mdl Lc FF B C K ret n sp PRE Hbig.
  destruct (AzBridgeLG.malloc_pre_LG SEGS FXOK IA PRX _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ PRE) as (PRE0 & HL & Hsp).
  assert (Hn : 1 <= n) by lia.
  refine (AsIface3.AsK.katsD_conseq SEGS _ _ _ _ _ (MK fx R M mdl Lc FF B C K ret n sp PRE0 Hbig) _ _).
  - intros c'. exact (AzBridgeLG.malloc_ok_LG SEGS FXOK IA PRX FRESHsec PR_zone IMG_LO_pr PRIV_IMG_pr ERRNO_IMG_pr stk R M mdl Lc FF B C K ret n sp c' Hstk Hsp Hn HL).
  - intros c'. exact (AzBridgeLG.malloc_null_LG SEGS FXOK IA PRX PR_zone IMG_LO_pr PRIV_IMG_pr ERRNO_IMG_pr stk R M mdl Lc FF B C K ret n sp c' Hstk Hsp HL).
Qed.

Section GenRZ3.   (* [comment removed for export] *)
Variable RZg : GPS.rz_t.
Hypothesis RZg_kc : forall T, AsIface3.AsK.kclosedD SEGS (fun c => RZg c T).
Lemma h_malloc1_sec_wj : forall stk entry, 0 <= stk ->
  AsIfaceNM3.AsIfacePR3.MALLOC_ALT_SEC SEGS FXOK IA PRX stk entry true ->
  h_malloc1_at SEGS G FXOK RZg AINVH_pr AzBridgeC3.FPCw FRESHsec stk entry.
Proof.
  intros stk entry Hstk MS0 fx R0 M mdl L LF B C K ret n sp Tok Hpre Hfresh HTok Hok.
  pose proof (MALLOC_ALT_SEC_LG stk entry true Hstk MS0) as MS.
  pose proof Hpre as (HFX & Hh & (FF & HLF & HA) & _). subst LF.
  apply (AzBridgeC3.katsD_ok_g SEGS RZg RZg_kc _ _ _ Tok
           (MS fx R0 M mdl L FF B C K ret n sp
              (AzBridgeC3.malloc_pre_w SEGS IA FXOK AAINV_PL G G_tp _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hpre ltac:(exists FF; split; [reflexivity | exact HA]) FF eq_refl HA) Hfresh)).
  intros c' Hc'. destruct (AzBridgeC3.malloc_ok_w SEGS IA FXOK AAINV_PL G G_imglo G_hi G_ro_img G_errno G_privs stk R0 M mdl L FF B C K ret n sp c' Hh Hc') as (fx' & R' & M' & mdl' & p & -> & Hpost).
  exact (Hok fx' R' M' mdl' p Hpost).
Qed.
End GenRZ3.



(* [comment removed for export] *)
Variable PERMc : list (Z * Z).
Variable SPTOPc : Z.
Variable HID : list (Z * Z).
Variable HIDF : list (Z * Z).
Variable M0 : word -> option byte.
Variable B0 C0 : Z.
Hypothesis B0_nonneg : 0 <= B0.
Hypothesis C0_nonneg : 0 <= C0.
Variable FTOPc : Z.
Hypothesis FTOPc_ok : Z.of_nat (length HIDF) + FTOPc <= FMIN.
Variable A : atable.
Hypothesis A_img_hi : img_hi A = g_img_hi G.
Hypothesis A_img_lo : img_lo A = g_img_lo G.
Variable KCAP : Z.
Hypothesis GKCAP_le : GKCAP <= KCAP.
Variable IT : itab.
Hypothesis IT_ok : itab_sound SEGS IT.
Variable nx0 : nat.
Variable FS0 : Fs.Fs.
Variable UINV : env -> Prop.
Hypothesis UINV_agree : forall E E', env_agree nx0 E E' -> UINV E -> UINV E'.

Definition AINV_pr := AINV_f SWIN G AINVH_pr PERMc SPTOPc HID HIDF M0 B0 C0.
#[local] Notation AINV_bt := (AzBridgeE3.AINV_bt bt G SWIN PERMc SPTOPc HID HIDF M0 B0 C0).
#[local] Notation AINVN_bt := (AzBridgeE3.AINVN_bt bt G SWIN PERMc SPTOPc HID HIDF M0 B0 C0).
#[local] Notation SHCb := (AzBridgeH.SHC_bt bt).
#[local] Notation VSHf := (AzFrame.VSHf HID HIDF).

Lemma SEGS_in_hull_pr : forall a : word, APS.in_hull A (u a) = false -> find_segment SEGS (u a) 1 = None.
Proof.
  intros a Ha. apply SEGS_in_hull_out. unfold APS.in_hull in Ha. rewrite A_img_hi, A_img_lo in Ha.
  intros [H1 H2]. rewrite (proj2 (Z.leb_le _ _) H1), (proj2 (Z.ltb_lt _ _) H2) in Ha. discriminate Ha.
Qed.

(* [comment removed for export] *)
Section GenRZ4.   (* [comment removed for export] *)
Variable RZg : GPS.rz_t.
Hypothesis RZg_kc : forall T, AsIface3.AsK.kclosedD SEGS (fun c => RZg c T).
Hypothesis RZg_silent1 : GPS.RZ_SILENT1 SEGS RZg.
Hypothesis H_strlen_entry_j :
  h_strlen_at SEGS G FXOK RZg AINVH_pr (AsVocab.AsCells.ia_strlen_icpt IA) -> h_strlen_at SEGS G FXOK RZg AINVH_pr (g_strlen G).
Theorem gcontracts_core_pr_j :
  gcontracts_core SEGS IT A nx0 PERMc SPTOPc FS0 SHCb VSHf AINV_pr KCAP FTOPc FXOK UINV RZg G.
Proof.
  unfold AINV_pr.
  exact (AzFrameAllocNM.gcontracts_core_nm SEGS SWIN G FXOK SHCb AINVH_pr hprops_pr
           G_ro_img G_img_al G_img_shlo G_priv SWIN_img RZg AzBridgeC3.FPCw PERMc SPTOPc HID HIDF M0 B0 C0
           B0_nonneg C0_nonneg FTOPc FTOPc_ok A A_img_hi A_img_lo SEGS_in_hull_pr SEGS_wx SEGS_wr SEGS_in_hull_out ROM_ok
           RO_hi G_newh_img KCAP GKCAP_le IT IT_ok nx0 FS0 UINV UINV_agree RZg_silent1 AzBridgeC3.fpc_kfpc_w
           (hcontracts_nm_pr_j RZg RZg_kc) (lcontracts_pr_j RZg RZg_kc H_strlen_entry_j)).
Qed.
End GenRZ4.



(* [comment removed for export] *)
Lemma AINV_pr_bt : forall Lc Lf B C K M mdl, AINV_pr Lc Lf B C K M mdl -> AINV_bt Lc Lf B C K M mdl.
Proof. intros Lc Lf B C K M mdl (HA & Hrest). split; [exact (AINVH_pr_bt _ _ _ _ _ _ _ HA) | exact Hrest]. Qed.
Lemma cs_ok_pr_weaken : forall E cs fx R M model,
  GPS.cs_ok SEGS PERMc SPTOPc FS0 SHCb VSHf AINV_pr KCAP FTOPc FXOK UINV E cs fx R M model ->
  GPS.cs_ok SEGS PERMc SPTOPc FS0 SHCb VSHf AINV_bt KCAP FTOPc FXOK UINV E cs fx R M model.
Proof.
  intros E cs fx R M model HC. destruct HC as [c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12 c13 c14].
  constructor; try assumption. exact (AINV_pr_bt _ _ _ _ _ _ _ c7).
Qed.

(* [comment removed for export] *)
Lemma ainv_q_of_cs_ok : forall E cs fx R M model,
  GPS.cs_ok SEGS PERMc SPTOPc FS0 SHCb VSHf AINV_pr KCAP FTOPc FXOK UINV E cs fx R M model ->
  exists FF, blocks_den E (a_fake cs) ++ HIDF = map AzBridgeH.wfr FF
             /\ PRX None (blocks_den E (a_vis cs) ++ HID) FF (B0 + bcost E (a_vis cs)) (C0 + bcount (a_vis cs)) (uE E (a_meter cs)) M model.
Proof.
  intros E cs fx R M model HC. destruct (co_ainv HC) as ((FF & HFF & (HA & _)) & _). exists FF. split; [exact HFF | exact HA].
Qed.
Lemma fresh_site_q : forall (FRESH : list (Z * Z) -> list (Z * Z) -> Z -> Z -> Z -> (word -> option byte) -> Model -> Z -> Prop) E cs fx R M model,
  GPS.cs_ok SEGS PERMc SPTOPc FS0 SHCb VSHf AINV_pr KCAP FTOPc FXOK UINV E cs fx R M model ->
  (forall FF, PRX None (blocks_den E (a_vis cs) ++ HID) FF (B0 + bcost E (a_vis cs)) (C0 + bcount (a_vis cs)) (uE E (a_meter cs)) M model ->
              FRESH (blocks_den E (a_vis cs) ++ HID) FF (B0 + bcost E (a_vis cs)) (C0 + bcount (a_vis cs)) (uE E (a_meter cs)) M model (uE E (reg cs 10))) ->
  AzBridgeM2.fresh_site FRESH HID HIDF B0 C0 E cs M model.
Proof.
  intros FRESH E cs fx R M model HC HF. destruct (ainv_q_of_cs_ok E cs fx R M model HC) as (FF & HFF & HA).
  exists FF. split; [exact HFF | exact (HF FF HA)].
Qed.

(* [comment removed for export] *)
Variable bcap ccap : Z.
Hypothesis bcap_ok : B0 + bcap <= GBUDGET.
Hypothesis ccap_ok : C0 + ccap <= GCOUNT.

Let SWIN_img' : forall lo hi, In (lo, hi) SWIN -> g_img_lo G <= lo /\ hi <= g_img_hi G :=
  fun lo hi Hin => match SWIN_img lo hi Hin with conj S1 (conj S2 _) => conj (Z.le_trans _ _ _ (Z.le_trans _ _ _ (proj1 G_ro_img) (proj1 (proj2 G_ro_img))) S1) S2 end.
Let G_img_hull : 0 <= g_img_lo G /\ g_img_lo G <= g_ro_lo G <= g_img_hi G :=
  conj (proj1 G_img_al) (conj (proj1 G_ro_img) (Z.le_trans _ _ _ (proj1 (proj2 G_ro_img)) (proj2 (proj2 G_ro_img)))).
Let G_errno_img' : g_img_lo G <= g_errno G /\ g_errno G + 4 <= g_img_hi G.
Proof. pose proof G_ro_img. lia. Qed.

Section GenRZ5.   (* [comment removed for export] *)
Variable RZg : GPS.rz_t.
Hypothesis RZg_kc : forall T, AsIface3.AsK.kclosedD SEGS (fun c => RZg c T).
Theorem malloc1_glue_pr_j : forall args cs csa csb E fx R M model (Tb : TSet),
  GPS.cs_ok SEGS PERMc SPTOPc FS0 SHCb VSHf AINV_pr KCAP FTOPc FXOK UINV E cs fx R M model ->
  XAg SEGS nx0 G bcap ccap 12%nat args cs = Some (csa, csb) ->
  64512 < uE E (reg cs 10) ->
  Tb [] ->
  (forall E' fx' R' M' model',
      env_agree nx0 E E' /\ env_agree (nxt cs) E E' ->
      GPS.cs_ok SEGS PERMc SPTOPc FS0 SHCb VSHf AINV_pr KCAP FTOPc FXOK UINV E' csb fx' R' M' model' -> m_fs model' = m_fs model ->
      RZg (cfgF SEGS fx' R' (pc csb) M' model') Tb) ->
  RZg (cfgF SEGS fx R (pc cs) M model) Tb.
Proof.
  intros args cs csa csb E fx R M model Tb HC Hn Hbig HTb Kok.
  destruct ASCP as [Ms Mst Fr Frt OD ODS Sk Frl Mc Amc Mset Ams Mm Amm Sl].
  pose proof (h_malloc1_sec_wj RZg RZg_kc AsVocab.MSTK_A _ ltac:(unfold AsVocab.MSTK_A; lia) Ms) as H2.
  pose proof (h_malloc1_sec_wj RZg RZg_kc AsVocab.MSTK_A _ ltac:(unfold AsVocab.MSTK_A; lia) Mst) as H2t.
  rewrite <- G_malloc in H2. rewrite <- G_malloc_thunk in H2t.
  pose proof (AzFrameAlloc.malloc1_nspec_f SEGS SWIN G FXOK SHCb AINVH_pr hprops_pr
                G_ro_img G_img_al G_img_shlo G_priv SWIN_img RZg AzBridgeC3.FPCw PERMc SPTOPc HID HIDF M0 B0 C0 bcap ccap bcap_ok ccap_ok
                FRESHsec MSTK_A) as NS.
  pose proof (NS (g_malloc G) ltac:(unfold MSTK_A; lia) H2) as NSm.
  pose proof (NS (g_malloc_thunk G) ltac:(unfold MSTK_A; lia) H2t) as NSt.
  refine (AzNodesAlloc3.node_malloc1_glue SEGS A nx0 SWIN PERMc SPTOPc FTOPc FS0 SHCb VSHf AINV_pr KCAP FXOK UINV UINV_agree
            RZg G bcap ccap AzBridgeC3.FPCw
            (AzFrameAlloc.If_ifacts SWIN G SHCb G_ro_img G_img_al SWIN_img PERMc SPTOPc HID HIDF M0 B0 C0 A A_img_hi A_img_lo AINVH_pr hprops_pr)
            A_img_hi A_img_lo (hp_shc_stack _ _ _ _ hprops_pr) (hp_shc_image _ _ _ _ hprops_pr) SWIN_img' G_img_hull
            (AzFrame.G_img_ceil G G_img_al G_img_shlo) G_errno_img' GKCAP_le AzBridgeC3.fpc_kfpc_w
            (AzFrameAlloc.FRESHf HID HIDF B0 C0 FRESHsec)
            args cs csa csb E fx R M model Tb NSt NSm HC Hn _ HTb Kok).
  unfold AzFrameAlloc.FRESHf, FRESHsec. exact Hbig.
Qed.
End GenRZ5.


End PR.
