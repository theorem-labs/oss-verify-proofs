(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.glaze.binary_reflection.lib Require BvWfKernel.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require WdZS.
#[local] Ltac Zify.zify ::= WdZS.wd_zs_stock.   (* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Spec4 OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3 OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3B OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3Sound OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymRun3 OSSVerify.Proofs.glaze.binary_reflection.lib.AzPlanCore OSSVerify.Proofs.glaze.binary_reflection.lib.AzPlan OSSVerify.Proofs.glaze.binary_reflection.lib.AzAPS OSSVerify.Proofs.glaze.binary_reflection.lib.AzGPS OSSVerify.Proofs.glaze.binary_reflection.lib.AzIface OSSVerify.Proofs.glaze.binary_reflection.lib.AzContracts OSSVerify.Proofs.glaze.binary_reflection.lib.AzKnowLib OSSVerify.Proofs.glaze.binary_reflection.lib.AzCallLib OSSVerify.Proofs.glaze.binary_reflection.lib.AzFrame OSSVerify.Proofs.glaze.binary_reflection.lib.AzNSpec OSSVerify.Proofs.glaze.binary_reflection.lib.AzNodesSound OSSVerify.Proofs.glaze.binary_reflection.lib.AzNodesAlloc3 OSSVerify.Proofs.glaze.binary_reflection.lib.AzNodesLibc2 OSSVerify.Proofs.glaze.binary_reflection.lib.AzFrameAlloc OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst. Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg OSSVerify.Proofs.glaze.binary_reflection.lib.Spec4.AgentLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3 OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3B OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3Sound OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymRun3 OSSVerify.Proofs.glaze.binary_reflection.lib.AzPlanCore OSSVerify.Proofs.glaze.binary_reflection.lib.AzPlan OSSVerify.Proofs.glaze.binary_reflection.lib.AzAPS OSSVerify.Proofs.glaze.binary_reflection.lib.AzGPS OSSVerify.Proofs.glaze.binary_reflection.lib.AzIface OSSVerify.Proofs.glaze.binary_reflection.lib.AzContracts OSSVerify.Proofs.glaze.binary_reflection.lib.AzKnowLib OSSVerify.Proofs.glaze.binary_reflection.lib.AzCallLib OSSVerify.Proofs.glaze.binary_reflection.lib.AzFrame OSSVerify.Proofs.glaze.binary_reflection.lib.AzNSpec OSSVerify.Proofs.glaze.binary_reflection.lib.AzNodesSound OSSVerify.Proofs.glaze.binary_reflection.lib.AzNodesAlloc3 OSSVerify.Proofs.glaze.binary_reflection.lib.AzNodesLibc2 OSSVerify.Proofs.glaze.binary_reflection.lib.AzFrameAlloc OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AX2S. Import AP. Import GPS.
Open Scope Z_scope.
#[local] Notation u := bv_unsigned.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section Defs.
Variable SEGS : list Segment.
Context {RC : run_ceil}.
Context {SFL : stk_floor}.   (* [comment removed for export] *)
(* [comment removed for export] *)
Variable NOK : Z -> list (Z * Z) -> Prop.
#[local] Notation cfg := (cfgF SEGS).


(* [comment removed for export] *)
Definition h_malloc_live_on (G : gtable) (FXOK : FX -> Prop) (RZ : GPS.rz_t)
    (AINVH : list (Z * Z) -> list (Z * Z) -> Z -> Z -> Z -> (word -> option byte) -> Model -> Prop)
    (FPC : (word -> option byte) -> Z -> Z -> Prop) (stk entry : Z) : Prop :=
  forall fx R M mdl L LF B C K (ret n sp : Z) T,
    NOK n L ->
    hmalloc_pre SEGS G FXOK AINVH FPC true fx R M mdl L LF B C K ret n sp stk -> T [] ->
    (forall fx' R' M' mdl' (p : word), hmalloc_post_ok SEGS G FXOK AINVH R M mdl L LF B C K n sp stk fx' R' M' mdl' p -> RZ (cfg fx' R' ret M' mdl') T) ->
    RZ (cfg fx R entry M mdl) T.
Definition malloc_nspec_live_on (SWIN PERMc : list (Z * Z)) (SPTOPc : Z) (G : gtable)
    (AINV : list (Z * Z) -> list (Z * Z) -> Z -> Z -> Z -> (word -> option byte) -> Model -> Prop)
    (FXOK : FX -> Prop) (RZ : GPS.rz_t) (FPC : (word -> option byte) -> Z -> Z -> Prop) (bcap ccap stk entry : Z) : Prop :=
  forall fx R M mdl Lc Lf B C K (ret n sp : Z) T,
    NOK n Lc ->
    nmalloc_pre SEGS SPTOPc G AINV FXOK FPC bcap ccap true fx R M mdl Lc Lf B C K ret n sp stk -> T [] ->
    (forall fx' R' M' mdl' (p : word), nmalloc_post_ok SEGS SWIN PERMc G AINV FXOK R M mdl Lc Lf B C K n sp stk fx' R' M' mdl' p -> RZ (cfg fx' R' ret M' mdl') T) ->
    RZ (cfg fx R entry M mdl) T.
End Defs.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section KFrame.
Variable SEGS : list Segment.
Context {RC : run_ceil}.
Context {SFL : stk_floor}.   (* [comment removed for export] *)
Variable NOK : Z -> list (Z * Z) -> Prop.      (* [comment removed for export] *)
Variable NOKn : Z -> list (Z * Z) -> Prop.     (* [comment removed for export] *)
Variable SWIN : list (Z * Z).
Variable G : gtable.
Variable FXOK : FX -> Prop.
Variable SHC : list (Z * Z).
Variable AINVH : list (Z * Z) -> list (Z * Z) -> Z -> Z -> Z -> (word -> option byte) -> Model -> Prop.
Variable AINVHN : Z -> list (Z * Z) -> list (Z * Z) -> Z -> Z -> Z -> (word -> option byte) -> Model -> Prop.
Hypothesis HP : hprops SWIN G SHC AINVH.
Hypothesis G_ro_img : g_img_lo G <= g_ro_lo G /\ g_ro_lo G <= g_ro_hi G <= g_img_hi G.
Hypothesis G_img_al : 0 <= g_img_lo G /\ g_img_lo G mod 8 = 0 /\ g_img_hi G mod 8 = 0.
Hypothesis G_img_shlo : g_img_hi G <= SHMAPLO.
Hypothesis G_priv : forall lo hi, In (lo, hi) (g_priv G) -> g_ro_hi G <= lo /\ hi <= g_img_hi G.
Hypothesis SWIN_img : forall lo hi, In (lo, hi) SWIN -> g_ro_hi G <= lo /\ hi <= g_img_hi G /\ (forall plo phi, In (plo, phi) (g_priv G) -> hi <= plo \/ phi <= lo).
Variable RZ : GPS.rz_t.
Variable FPC : (word -> option byte) -> Z -> Z -> Prop.
Variable PERMc : list (Z * Z).
Variable SPTOPc : Z.
Variable HID HIDF : list (Z * Z).
Variable M0 : word -> option byte.
Variable B0 C0 : Z.
Variable bcap ccap : Z.
Hypothesis bcap_ok : B0 + bcap <= GBUDGET.
Hypothesis ccap_ok : C0 + ccap <= GCOUNT.

Hypothesis NOK_frame : forall n Lc, NOKn n Lc -> NOK n (Lc ++ HID).

#[local] Notation AINVf := (AINV_f SWIN G AINVH PERMc SPTOPc HID HIDF M0 B0 C0).
#[local] Notation AINVfN := (AzFrameAlloc.AINV_fN SWIN G AINVHN PERMc SPTOPc HID HIDF M0 B0 C0).

Theorem malloc_nspec_live_f_on : forall stk entry,
  0 <= stk ->
  h_malloc_live_on SEGS NOK G FXOK RZ AINVH FPC stk entry ->
  malloc_nspec_live_on SEGS NOKn SWIN PERMc SPTOPc G AINVf FXOK RZ FPC bcap ccap stk entry.
Proof.
  intros stk entry Hstk HM fx R M mdl Lc Lf B C K ret n sp T HN Hpre HT0 Hok.
  pose proof Hpre as (Hh & HFX & HAf & Hcall & _).
  assert (Hsp : SFLOOR + stk <= sp /\ sp <= SPTOPc) by (destruct Hcall as (_ & _ & _ & _ & _ & X1 & X2 & _); split; assumption).
  apply (HM fx R M mdl (Lc ++ HID) (Lf ++ HIDF) (B0 + B) (C0 + C) K ret n sp T (NOK_frame _ _ HN)
            (AzFrameAlloc.nmalloc_pre_h SEGS SWIN G FXOK AINVH G_ro_img G_img_al FPC PERMc SPTOPc HID HIDF M0 B0 C0 bcap ccap bcap_ok ccap_ok
               _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hpre) HT0).
  intros fx' R' M' mdl' p Hpost. apply (Hok fx' R' M' mdl' p).
  eapply (AzFrameAlloc.nmalloc_post_ok_f SEGS SWIN G FXOK SHC AINVH HP G_ro_img G_img_al G_img_shlo G_priv SWIN_img PERMc SPTOPc HID HIDF M0 B0 C0);
    [exact Hstk | exact HAf | right; exact Hsp | exact Hpost].
Qed.
End KFrame.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section KNode.
Variable SEGS : list Segment.
Context {RC : run_ceil}.
Context {SFL : stk_floor}.   (* [comment removed for export] *)
Variable NOK : Z -> list (Z * Z) -> Prop.      (* [comment removed for export] *)
Variable A : atable.
Variable nx0 : nat.
Variable SWIN : list (Z * Z).
Variable PERMc : list (Z * Z).
Variable SPTOPc : Z.
Variable FTOPc : Z.
Variable FS0 : Fs.Fs.
Variable SHC : list (Z * Z).
Variable VSH : list (Z * Z).
Variable AINV : list (Z * Z) -> list (Z * Z) -> Z -> Z -> Z -> (word -> option byte) -> Model -> Prop.
Variable AINVN : Z -> list (Z * Z) -> list (Z * Z) -> Z -> Z -> Z -> (word -> option byte) -> Model -> Prop.
Variable KCAP : Z.
Variable FXOK : FX -> Prop.
Variable UINV : env -> Prop.
Hypothesis UINV_agree : forall E E', env_agree nx0 E E' -> UINV E -> UINV E'.
Variable RZ : GPS.rz_t.
Variable G : gtable.
Variable bcap ccap : Z.
Variable FPC : (word -> option byte) -> Z -> Z -> Prop.
Hypothesis AINV_if : AzNodesAlloc3.ifacts A PERMc SPTOPc SHC VSH G AINV.
Hypothesis AINVN_if : forall n, AzNodesAlloc3.ifacts A PERMc SPTOPc SHC VSH G (AINVN n).
Hypothesis A_img_hi : img_hi A = g_img_hi G.
Hypothesis A_img_lo : img_lo A = g_img_lo G.
Hypothesis SHC_stack : forall z, in_sshadow z -> in_shc SHC z = true.
Hypothesis SHC_image : forall z, in_ishadow G z -> in_shc SHC z = true.
Hypothesis SWIN_img : forall lo hi, In (lo, hi) SWIN -> g_img_lo G <= lo /\ hi <= g_img_hi G.
Hypothesis G_img_hull : 0 <= g_img_lo G /\ g_img_lo G <= g_ro_lo G <= g_img_hi G.
Hypothesis G_img_ceil : g_img_hi G <= CEIL_run.
Hypothesis G_errno_img : g_img_lo G <= g_errno G /\ g_errno G + 4 <= g_img_hi G.
Hypothesis GKCAP_le : GKCAP <= KCAP.
Hypothesis FPC_kfpc : forall M v lo, AX2S.fpc M v lo DMAXN -> FPC M v lo.

#[local] Notation cs_okX X := (GPS.cs_ok SEGS PERMc SPTOPc FS0 SHC VSH X KCAP FTOPc FXOK UINV).
#[local] Notation cs_ok := (GPS.cs_ok SEGS PERMc SPTOPc FS0 SHC VSH AINV KCAP FTOPc FXOK UINV).

(* [comment removed for export] *)
Theorem node_alloc_nb_live_sound : forall nv mv,
  AzNodesAlloc3.NBF UINV bcap ccap nv mv ->
  (forall E, UINV E -> NOK (uE E (EVar nv)) []) ->
  malloc_nspec_live_on SEGS NOK SWIN PERMc SPTOPc G AINV FXOK RZ FPC bcap ccap MSTK_A (g_malloc_thunk G) ->
  GPS.node1_stmtN SEGS nx0 PERMc SPTOPc FS0 SHC VSH AINV KCAP FTOPc FXOK UINV RZ always
    (node_alloc_nb SEGS nx0 G MSTK_A (g_malloc_thunk G) nv mv).
Proof.
  intros nv mv HNB HNOK MT cs ok E fx R M model T HT HC _ Hna Hk.
  destruct (call_ok_stk nx0 G MSTK_A (g_malloc_thunk G) cs) as [ret|] eqn:Hco.
  2:{ unfold node_alloc_nb in Hna. rewrite Hco in Hna. discriminate Hna. }
  assert (Hreg : reg cs 10 = EVar nv /\ a_vis cs = []).
  { pose proof Hna as Hg. unfold node_alloc_nb in Hg. rewrite Hco in Hg. cbv zeta in Hg.
    match type of Hg with (if negb ?c then _ else _) = _ => destruct c; cbn [negb] in Hg; [|discriminate] end.
    match type of Hg with (if negb ?c then _ else _) = _ => destruct c eqn:Hc; cbn [negb] in Hg; [|discriminate] end.
    apply andb_prop in Hc as [Hc _]. apply andb_prop in Hc as [Hc _]. apply andb_prop in Hc as [Hv He].
    apply expr_eqb_eq in He. split; [exact He|]. destruct (a_vis cs); [reflexivity | discriminate Hv]. }
  assert (Hstk : 0 < MSTK_A < 2 ^ 40) by (unfold MSTK_A; lia).
  destruct (AzNodesAlloc3.node_alloc_nb_pre_sound SEGS nx0 PERMc SPTOPc FTOPc FS0 SHC VSH AINV KCAP FXOK UINV G bcap ccap FPC
              G_img_hull G_img_ceil G_errno_img FPC_kfpc nv mv MSTK_A (g_malloc_thunk G) cs ok ret E fx R M model HNB Hstk HC Hco Hna) as [Hpc PRE].
  unfold cfgF. rewrite Hpc.
  assert (HN : NOK (uE E (reg cs 10)) (blocks_den E (a_vis cs))) by (rewrite (proj1 Hreg), (proj2 Hreg); apply HNOK; exact (co_uinv HC)).
  apply (MT fx R M model _ _ _ _ _ ret _ _ T HN PRE HT).
  intros fx' R' M' mdl' p POST.
  destruct (AzNodesAlloc3.node_alloc_nb_ok_sound SEGS A nx0 SWIN PERMc SPTOPc FTOPc FS0 SHC VSH AINV KCAP FXOK UINV UINV_agree G bcap ccap
              AINV_if A_img_hi A_img_lo SHC_stack SHC_image SWIN_img G_img_hull G_img_ceil G_errno_img GKCAP_le
              nv mv MSTK_A (g_malloc_thunk G) cs ok ret E fx R M model fx' R' M' mdl' p HNB Hstk HC Hco Hna POST) as (E' & Hag & HC' & Hpc' & Hfs').
  rewrite <- Hpc'. exact (Hk E' fx' R' M' mdl' Hag HC' Hfs').
Qed.
End KNode.
