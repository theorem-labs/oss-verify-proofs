(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.glaze.binary_reflection.lib Require BvWfKernel.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require WdZS.
#[local] Ltac Zify.zify ::= WdZS.wd_zs_stock.   (* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape OSSVerify.Proofs.glaze.binary_reflection.lib.Spec4 OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymStepR OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3 OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3B OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3Sound OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymRun3 OSSVerify.Proofs.glaze.binary_reflection.lib.AzPlanCore OSSVerify.Proofs.glaze.binary_reflection.lib.AzPlan OSSVerify.Proofs.glaze.binary_reflection.lib.AzAPS OSSVerify.Proofs.glaze.binary_reflection.lib.AzGPS OSSVerify.Proofs.glaze.binary_reflection.lib.AzIface OSSVerify.Proofs.glaze.binary_reflection.lib.AzContracts OSSVerify.Proofs.glaze.binary_reflection.lib.AzKnowLib OSSVerify.Proofs.glaze.binary_reflection.lib.AzNSpec OSSVerify.Proofs.glaze.binary_reflection.lib.AzFrame OSSVerify.Proofs.glaze.binary_reflection.lib.AzFrameAlloc OSSVerify.Proofs.glaze.binary_reflection.lib.AzNodesSound OSSVerify.Proofs.glaze.binary_reflection.lib.AzNodesAlloc OSSVerify.Proofs.glaze.binary_reflection.lib.AzNodesAlloc2 OSSVerify.Proofs.glaze.binary_reflection.lib.AzNodesAlloc3 OSSVerify.Proofs.glaze.binary_reflection.lib.AzCall OSSVerify.Proofs.glaze.binary_reflection.lib.AzEntry OSSVerify.Proofs.glaze.binary_reflection.lib.AzOpNewK OSSVerify.Proofs.glaze.binary_reflection.lib.AzOpNewH OSSVerify.Proofs.glaze.binary_reflection.lib.AzImageAsan OSSVerify.Proofs.glaze.binary_reflection.lib.AzImageBss OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanHexScan OSSVerify.Proofs.glaze.binary_reflection.lib.AzOpNewA OSSVerify.Proofs.glaze.binary_reflection.lib.AzOpNewE OSSVerify.Proofs.glaze.binary_reflection.lib.AzBridgeH OSSVerify.Proofs.glaze.binary_reflection.lib.AzBridgeC3 OSSVerify.Proofs.glaze.binary_reflection.lib.AzBridgeOp OSSVerify.Proofs.glaze.binary_reflection.lib.AzOpNewS OSSVerify.Proofs.glaze.binary_reflection.lib.AzCallLib OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst. Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape.ShapeRel OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape.DivergeSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape.SpinAlg OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape.ShapeRetry OSSVerify.Proofs.glaze.binary_reflection.lib.Spec4.AgentLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymStepR OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3 OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3B OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3Sound OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymRun3 OSSVerify.Proofs.glaze.binary_reflection.lib.AzPlanCore OSSVerify.Proofs.glaze.binary_reflection.lib.AzPlan OSSVerify.Proofs.glaze.binary_reflection.lib.AzAPS OSSVerify.Proofs.glaze.binary_reflection.lib.AzGPS OSSVerify.Proofs.glaze.binary_reflection.lib.AzIface OSSVerify.Proofs.glaze.binary_reflection.lib.AzContracts OSSVerify.Proofs.glaze.binary_reflection.lib.AzKnowLib OSSVerify.Proofs.glaze.binary_reflection.lib.AzNSpec OSSVerify.Proofs.glaze.binary_reflection.lib.AzFrame OSSVerify.Proofs.glaze.binary_reflection.lib.AzFrameAlloc OSSVerify.Proofs.glaze.binary_reflection.lib.AzNodesSound OSSVerify.Proofs.glaze.binary_reflection.lib.AzNodesAlloc OSSVerify.Proofs.glaze.binary_reflection.lib.AzNodesAlloc2 OSSVerify.Proofs.glaze.binary_reflection.lib.AzNodesAlloc3 OSSVerify.Proofs.glaze.binary_reflection.lib.AzCall OSSVerify.Proofs.glaze.binary_reflection.lib.AzEntry OSSVerify.Proofs.glaze.binary_reflection.lib.AzOpNewK OSSVerify.Proofs.glaze.binary_reflection.lib.AzOpNewH OSSVerify.Proofs.glaze.binary_reflection.lib.AzImageAsan OSSVerify.Proofs.glaze.binary_reflection.lib.AzImageBss OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanHexScan OSSVerify.Proofs.glaze.binary_reflection.lib.AzOpNewA OSSVerify.Proofs.glaze.binary_reflection.lib.AzOpNewE OSSVerify.Proofs.glaze.binary_reflection.lib.AzBridgeH OSSVerify.Proofs.glaze.binary_reflection.lib.AzBridgeC3 OSSVerify.Proofs.glaze.binary_reflection.lib.AzBridgeOp OSSVerify.Proofs.glaze.binary_reflection.lib.AzOpNewS OSSVerify.Proofs.glaze.binary_reflection.lib.AzCallLib OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst.
From OSSVerify.glaze.binary_reflection.images Require Import Asan.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require AsIfaceNM3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AX2S. Import AP. Import GPS.
Open Scope Z_scope.
#[local] Notation u := bv_unsigned.

(* [comment removed for export] *)
Lemma GA_img_al : 0 <= g_img_lo GASAN /\ g_img_lo GASAN mod 8 = 0 /\ g_img_hi GASAN mod 8 = 0.
Proof. cbn. split; [lia|]. split; reflexivity. Qed.
Lemma GA_img_shlo : g_img_hi GASAN <= SHMAPLO.
Proof. cbn. unfold SHMAPLO. lia. Qed.
Lemma GA_newh_img : g_img_lo GASAN <= g_newh_got GASAN /\ g_newh_got GASAN + 8 <= g_img_hi GASAN
                    /\ g_img_lo GASAN <= g_newh_cell GASAN /\ g_newh_cell GASAN + 8 <= g_img_hi GASAN.
Proof. cbn. lia. Qed.
Definition ERRW : list (Z * Z) := [(g_errno GASAN, g_errno GASAN + 4)].
Lemma ERRW_img : forall lo hi, In (lo, hi) ERRW ->
  g_ro_hi GASAN <= lo /\ hi <= g_img_hi GASAN /\ (forall plo phi, In (plo, phi) (g_priv GASAN) -> hi <= plo \/ phi <= lo).
Proof.
  intros lo hi [H|[]]. injection H as <- <-. cbn [g_errno g_ro_hi g_img_hi GASAN]. split; [lia|]. split; [lia|].
  intros plo phi Hp. cbn [g_priv GASAN] in Hp.
  repeat (destruct Hp as [Hp|Hp]; [injection Hp as <- <-; lia|]). destruct Hp.
Qed.
Lemma GA_opnew_kn_wf : opnew_kn_wf GASAN = true.
Proof. vm_compute. reflexivity. Qed.

(* [comment removed for export] *)
Lemma asan_bss_wview : forall (m : word -> option byte) (x : word),
  BSS_LO <= bv_unsigned x < BSS_HI -> wview ASEGS m x <> None.
Proof.
  intros m x [Hlo Hhi]. unfold BSS_LO, BSS_HI in *. unfold wview. destruct (m x); [discriminate|].
  replace (find_segment ASEGS (bv_unsigned x) 1) with (Some Asan_segment_003).
  2:{ unfold ASEGS, Asan_loaded_segments.
      cbn [find_segment Asan_segment_000 Asan_segment_001
           Asan_segment_002 Asan_segment_003 seg_base seg_size].
      replace (bv_unsigned x + 1 <=? Z.of_N 65536 + Z.of_N 237568) with false by (symmetry; apply Z.leb_gt; lia).
      replace (bv_unsigned x + 1 <=? Z.of_N 303104 + Z.of_N 724992) with false by (symmetry; apply Z.leb_gt; lia).
      replace (bv_unsigned x + 1 <=? Z.of_N 1028096 + Z.of_N 24576) with false by (symmetry; apply Z.leb_gt; lia).
      rewrite !andb_false_r.
      replace (Z.of_N 1052672 <=? bv_unsigned x) with true by (symmetry; apply Z.leb_le; lia).
      replace (bv_unsigned x + 1 <=? Z.of_N 1052672 + Z.of_N 5619712) with true by (symmetry; apply Z.leb_le; lia).
      reflexivity. }
  cbn [seg_writable seg_perms Asan_segment_003 string_has Ascii.eqb seg_bytes seg_base orb].
  cbn [segment_byte_at].
  replace (Z.to_N (bv_unsigned x - Z.of_N 1052672) <? Z.to_N (Uint63.to_Z (PrimString.length Asan_seg_bytes_003) / 2))%N
    with true by (symmetry; apply N.ltb_lt; rewrite asan_len3; lia).
  pose proof (zscanN_sound _ _ _ _ asan_bss_scan (Z.to_N (bv_unsigned x - Z.of_N 1052672) - 0x2ea0)%N ltac:(lia)) as Z0.
  replace (0x2ea0 + (Z.to_N (bv_unsigned x - Z.of_N 1052672) - 0x2ea0))%N with (Z.to_N (bv_unsigned x - Z.of_N 1052672)) in Z0 by lia.
  rewrite Z0. discriminate.
Qed.

(* [comment removed for export] *)
Lemma CHKl_eq : forall hs cs p, CHKl hs cs p =
  AP.checkA ASEGS IT_N AASAN NXF 0 GPS.ISP0 (AzOpNewS.XNl ASEGS GASAN NXF 10 33) AzOpNewS.XE0 AzOpNewS.XB0 AzOpNewS.XA0 AP.XT0
    hs 0%nat false 400%nat 400%nat None cs p.
Proof. intros. reflexivity. Qed.

Lemma asan_segs_wr : AzCallLib.GCL.segs_wr_ok ASEGS.
Proof.
  intros seg Hin Hw. rewrite asan_segs_eq in Hin.
  destruct Hin as [<-|[<-|[<-|[<-|[]]]]]; vm_compute in Hw; try discriminate Hw; vm_compute; reflexivity.
Qed.

Section TopA.
Context {RC : run_ceil}.
Variable bt : AsAinvDefs3.as_boot.
#[local] Notation IA := (AsAinvDefs3.bt_ia bt).
#[local] Notation G := GASAN.

(* [comment removed for export] *)
Variable fx : FX.
Variable R : bvmap 5 word.
Variable M : word -> option byte.
Variable mdl : Model.
Variable L LF : list (Z * Z).
Variable B C K ret n sp : Z.
Hypothesis Hpre : hmalloc_pre ASEGS G fx_ok (AzBridgeH.AINVH_bt bt) AzBridgeC3.FPCw false fx R M mdl L LF B C K ret n sp MSTK_N.
Hypothesis HX : hopnew_x ASEGS G M.
Hypothesis HFDS : m_fds mdl = APS.fds_std.
Hypothesis HLF : Z.of_nat (length LF) + 1 <= FMIN.
Hypothesis HK0 : 0 <= K.     (* [comment removed for export] *)

Lemma sp_floor : CEIL_run <= sp - MSTK_N.
Proof. destruct Hpre as (_ & _ & _ & (_ & _ & _ & _ & _ & H & _) & _). lia. Qed.

(* [comment removed for export] *)
Definition SFLop : stk_floor := {| SFLOOR := sp - MSTK_N ; sfloor_ge := sp_floor |}.
#[local] Existing Instance SFLop.

Definition UINVop (E : env) : Prop :=
  (forall i : nat, (1 <= i < 32)%nat -> ev E i = getr R (Z_to_bv 5 (Z.of_nat i)))
  /\ ev E 33%nat = Z_to_bv 64 K.
Definition E0 : env :=
  Env (fun i => if Nat.ltb i 32 then getr R (Z_to_bv 5 (Z.of_nat i)) else if Nat.eqb i 33 then Z_to_bv 64 K else Z_to_bv 64 1) (fun _ => []).
Lemma UINVop_E0 : UINVop E0.
Proof.
  split; [|reflexivity]. intros i Hi. cbn [E0 ev]. replace (Nat.ltb i 32) with true by (symmetry; apply Nat.ltb_lt; lia). reflexivity.
Qed.
Lemma UINVop_agree : forall E E', env_agree NXF E E' -> UINVop E -> UINVop E'.
Proof.
  intros E E' [Hag _] [H1 H2]. split.
  - intros i Hi. rewrite <- (Hag i ltac:(unfold NXF; lia)). exact (H1 i Hi).
  - rewrite <- (Hag 33%nat ltac:(unfold NXF; lia)). exact H2.
Qed.

(* [comment removed for export] *)
Variable FRESH : list (Z * Z) -> list (Z * Z) -> Z -> Z -> Z -> (word -> option byte) -> Model -> Z -> Prop.
Hypothesis ASC : AsIfaceNM3.as_contracts_n ASEGS fx_ok IA (AsAinvEntry3.AsAinvHole3.AAINV_HS bt) FRESH (AsAinvDefs3.bt_fs bt).
Hypothesis G_imglo : g_img_lo G = AsVocab.AsCells.ia_img_lo IA.
Hypothesis G_hi : g_img_hi G = AsVocab.AsCells.ia_img_hi IA.
Hypothesis SWIN_ok : AsVocab.as_wins_ok IA ERRW.

#[local] Notation SHCb := (AzBridgeH.SHC_bt bt).
#[local] Notation VSHo := (AzFrame.VSHf L LF).
#[local] Notation AINVHop := (AzBridgeOp.AINVH_op_bt bt n L).
Definition HPop := AzBridgeOp.hprops_op_bt bt ERRW G G_imglo G_hi asan_G_ro_img2 GA_img_al GASAN_errno SWIN_ok GA_img_shlo n L.
#[local] Notation AINVop := (AzOpNewS.AINV_op bt G ERRW ERRW sp L LF M B C n).
Definition IFop := AzFrameAlloc.If_ifacts ERRW G SHCb asan_G_ro_img2 GA_img_al ERRW_img ERRW sp L LF M B C AASAN asan_A_img_hi asan_A_img_lo AINVHop HPop.

Lemma sp_facts : u (getr R (Z_to_bv 5 2)) = sp /\ sp mod 16 = 0 /\ CEIL_run + MSTK_N <= sp /\ sp + 16 <= two47.
Proof. destruct Hpre as (_ & _ & _ & (_ & _ & _ & H2 & H3 & H4 & H5 & _) & _). repeat split; assumption. Qed.

Lemma AINVop_entry : AINVop [] [] 0 0 K M mdl.
Proof.
  destruct Hpre as (_ & _ & HA & _). destruct sp_facts as (S1 & S2 & S3 & S4).
  unfold AzOpNewS.AINV_op, AINV_f. cbn [app]. rewrite !Z.add_0_r.
  split; [exact (AzBridgeOp.AINVH_op_bt_none bt n L _ _ _ _ _ _ _ HA)|].
  split.
  { split; intros z Hz; [right; right; right; exact Hz|].
    destruct Hz as (lo & hi & [H|[]] & Hz). injection H as <- <-. cbn [g_errno GASAN] in Hz. unfold two47. lia. }
  split.
  { unfold MSTK_N in S3. split; [lia|].
    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
    lia.
    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false). }
  split; [intros a _; reflexivity | intros a _ H; exact H].
Qed.

(* [comment removed for export] *)
Lemma ERRW_img' : forall lo hi, In (lo, hi) ERRW -> g_img_lo G <= lo /\ hi <= g_img_hi G.
Proof. intros lo hi H. destruct (ERRW_img lo hi H) as (H1 & H2 & _). cbn in *. lia. Qed.

Lemma hid_entry : forall a : word,
  CEIL_run <= u a \/ (g_img_lo G <= u a < g_img_hi G) -> GPS.hid SHCb VSHo E0 H0 mdl a = false.
Proof.
  intros a Ha.
  eapply (AzNodesAlloc3.hid_app_falseX AASAN ERRW ERRW sp SHCb VSHo G asan_A_img_hi asan_A_img_lo ERRW_img' AINVop IFop E0 H0 mdl 0 0 K M a AINVop_entry).
  destruct Ha as [Ha|Ha]; [right; right; left; exact Ha | right; right; right; right; exact Ha].
Qed.
Lemma Mr_entry : forall a : word,
  CEIL_run <= u a \/ (g_img_lo G <= u a < g_img_hi G) -> GPS.Mr SHCb VSHo E0 H0 mdl M a = M a.
Proof. intros a Ha. unfold GPS.Mr. apply mrestrict_visible. exact (hid_entry a Ha). Qed.

Lemma uE_sp : uE E0 ESP = sp.
Proof. destruct sp_facts as (S1 & _). unfold uE, ESP. cbn [edenot E0 ev Nat.ltb Nat.leb]. exact S1. Qed.

(* [comment removed for export] *)
Lemma kn_scratch : kentry_ok ASEGS E0 (GPS.Mr SHCb VSHo E0 H0 mdl M) (KWr (SA ESP (-3600)) (ELit 3600)).
Proof.
  destruct sp_facts as (S1 & S2 & S3 & S4). pose proof ceil_pos as CP. unfold MSTK_N in S3. unfold two47 in S4.
  pose proof uE_sp as US. unfold uE in US.
  assert (ES : estart E0 (SA ESP (-3600)) = sp - 3600) by (unfold estart; cbn [a_base a_off]; rewrite US; lia).
  assert (EL : elenZ E0 (ELit 3600) = 3600) by (unfold elenZ; cbn [edenot]; apply u64_lit; lia).
  apply kentry_ok_KWr_wview.
  - unfold flat. rewrite ES, EL. lia.
  - intros x Hx. rewrite ES, EL in Hx.
    destruct Hpre as (_ & _ & _ & (_ & _ & _ & _ & _ & _ & _ & _ & Hst) & _).
    assert (Hsc : scratch sp MSTK_N x) by (unfold scratch, MSTK_N; lia).
    pose proof (store_ok_all ASEGS M 1 x ltac:(pose proof (u64_range x); lia) (Hst x Hsc) x ltac:(lia)) as W.
    unfold wview in W |- *. rewrite (Mr_entry x ltac:(left; lia)). exact W.
Qed.

Lemma kn_errno : kentry_ok ASEGS E0 (GPS.Mr SHCb VSHo E0 H0 mdl M) (KWr (SA (ELit 0) ERRNO) (ELit 4)).
Proof.
  assert (ES : estart E0 (SA (ELit 0) ERRNO) = ERRNO) by (unfold estart; cbn [a_base a_off edenot]; rewrite u64_lit by lia; reflexivity).
  assert (EL : elenZ E0 (ELit 4) = 4) by (unfold elenZ; cbn [edenot]; apply u64_lit; lia).
  apply kentry_ok_KWr_wview.
  - unfold flat. rewrite ES, EL. unfold ERRNO. cbn [g_errno GASAN]. lia.
  - intros x Hx. rewrite ES, EL in Hx. unfold ERRNO in Hx. cbn [g_errno GASAN] in Hx.
    apply asan_bss_wview. unfold BSS_LO, BSS_HI. lia.
Qed.


Lemma GA_img_hull : 0 <= g_img_lo G /\ g_img_lo G <= g_ro_lo G <= g_img_hi G.
Proof. cbn. lia. Qed.

Lemma kn0_ok : know_ok ASEGS E0 (GPS.Mr SHCb VSHo E0 H0 mdl M) KN0.
Proof.
  destruct sp_facts as (S1 & S2 & S3 & S4). pose proof uE_sp as US. unfold uE in US.
  pose proof (ceil_lo) as CL. unfold MSTK_N in S3.
  destruct Hpre as (_ & _ & _ & _ & Hn & Hnr & _).
  unfold KN0, know_ok. apply Forall_app. split.
  - repeat apply Forall_cons; [| | | | | | apply Forall_nil].
    + apply kentry_ok_KRange. change (edenot E0 (EVar 10)) with (getr R (Z_to_bv 5 10)). rewrite Hn. exact Hnr.
    + apply kentry_ok_KAlign; [lia|]. rewrite US. exact S2.
    + apply kentry_ok_KRange. rewrite US. unfold APC.CEIL. unfold two47 in *. lia.
    + exact kn_scratch.
    + apply kentry_ok_KRange. change (edenot E0 (EVar 34)) with (Z_to_bv 64 1). rewrite u64_lit by lia. lia.
    + exact kn_errno.
  - unfold KCELLS.
    exact (AzOpNewE.opnew_kn_restrict ASEGS AASAN ERRW ERRW sp SHCb VSHo AINVop G IFop asan_A_img_hi asan_A_img_lo
             (hp_shc_stack _ _ _ _ HPop) (hp_shc_image _ _ _ _ HPop) ERRW_img' GA_img_hull
             (AzFrame.G_img_ceil G GA_img_al GA_img_shlo) GA_opnew_kn_wf E0 H0 mdl M 0 0 K AINVop_entry HX).
Qed.

Lemma regs0_ok : regs_ok E0 regs0 R.
Proof.
  destruct Hpre as (_ & _ & _ & (_ & _ & _ & _ & _ & _ & _ & R4 & _) & _).
  apply regs_ok_intro; [reflexivity|]. intros i Hi.
  do 32 (destruct i as [|i]; [first [lia | exact R4 | reflexivity]|]). lia.
Qed.
#[local] Notation cs_okop := (GPS.cs_ok ASEGS ERRW sp (m_fs mdl) SHCb VSHo AINVop GKCAP (FMIN - Z.of_nat (length LF)) fx_ok UINVop).

(* [comment removed for export] *)
Theorem entry_cs_ok : cs_okop E0 H0 fx R M mdl.
Proof.
  destruct sp_facts as (S1 & S2 & S3 & S4). pose proof uE_sp as US. unfold MSTK_N in S3. pose proof ceil_pos as CP.
  pose proof Hpre as (HFX & Hh & _ & _ & Hn & Hnr & _ & _ & _ & HKc).
  assert (UK : uE E0 (EVar 33) = K).
  { unfold uE. change (edenot E0 (EVar 33)) with (Z_to_bv 64 K). apply u64_lit. unfold kcost, EVT, GKCAP in HKc. lia. }
  apply AzEntry.cs_ok_intro.
  - exact regs0_ok.
  - reflexivity.
  - exact kn0_ok.
  - exact Hh.
  - reflexivity.
  - exact HFDS.
  - change (AINVop [] [] 0 0 (uE E0 (EVar 33)) M mdl). rewrite UK. exact AINVop_entry.
  - exact UINVop_E0.
  - exact HFX.
  - unfold H0, mkH. cbn [a_ghost wins_den map fst snd]. unfold uE. cbn [edenot]. unfold ERRW, ERRNO.
    rewrite !u64_lit by (cbn [g_errno GASAN]; lia). reflexivity.
  - change (sptop_den E0 ESP = sp). unfold sptop_den. rewrite US. destruct (Z.eqb_spec sp 0); [lia | reflexivity].
  - change (uE E0 (EVar 33) <= GKCAP). rewrite UK. unfold kcost, EVT in HKc. lia.
  - change (Z.of_nat 0 + uE E0 (EVar 34) <= FMIN - Z.of_nat (length LF)).
    unfold uE. change (edenot E0 (EVar 34)) with (Z_to_bv 64 1). rewrite u64_lit by lia. lia.
  - change (floor_sem E0 None ESP 3600). cbn [floor_sem]. change (sptop_den E0 ESP) with (sptop_den E0 ESP).
    unfold sptop_den. rewrite US. destruct (Z.eqb_spec sp 0); [lia|]. cbn [SFLOOR SFLop]. unfold MSTK_N. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section Exit.
Variables (E' : env) (fx' : FX) (R' : bvmap 5 word) (M' : word -> option byte) (mdl' : Model).
Hypothesis HC1 : cs_okop E' H1 fx' R' M' mdl'.

Let U1 : forall i : nat, (1 <= i < 32)%nat -> ev E' i = getr R (Z_to_bv 5 (Z.of_nat i)) := proj1 (co_uinv HC1).
Let U2 : ev E' 33%nat = Z_to_bv 64 K := proj2 (co_uinv HC1).
Definition pret : word := getr R' (Z_to_bv 5 10).

Lemma exit_reg : forall i : nat, (0 < i < 32)%nat -> getr R' (Z_to_bv 5 (Z.of_nat i)) = edenot E' (reg H1 i).
Proof. intros i Hi. exact (GPS.reg_sound ASEGS ERRW sp (m_fs mdl) SHCb VSHo AINVop GKCAP _ fx_ok UINVop E' H1 fx' R' M' mdl' i HC1 Hi). Qed.

Lemma exit_regs_kept : regs_kept R R'.
Proof.
  destruct Hpre as (_ & _ & _ & (_ & _ & _ & _ & _ & _ & _ & R4 & _) & _).
  intros r Hr. unfold callee_saved_regs in Hr.
  repeat (destruct Hr as [<-|Hr];
          [first [ rewrite R4; exact (exit_reg 4 ltac:(lia))
                 | match goal with |- getr R' (Z_to_bv 5 ?z) = _ =>
                     let i := constr:(Z.to_nat z) in
                     let i' := eval vm_compute in i in
                     change (getr R' (Z_to_bv 5 (Z.of_nat i')) = getr R (Z_to_bv 5 (Z.of_nat i')));
                     rewrite (exit_reg i' ltac:(lia)); exact (U1 i' ltac:(lia)) end ]|]).
  destruct Hr.
Qed.

Lemma exit_p : pret = ev E' 100%nat.
Proof. unfold pret. exact (exit_reg 10 ltac:(lia)). Qed.
Lemma exit_n : uE E' (EVar 10) = n.
Proof. destruct Hpre as (_ & _ & _ & _ & Hn & _). unfold uE. cbn [edenot]. rewrite (U1 10%nat ltac:(lia)). exact Hn. Qed.   (* [comment removed for export] *)
Lemma n_rng : 1 <= n <= NMAX.
Proof. destruct Hpre as (_ & _ & _ & _ & _ & Hnr & _). exact Hnr. Qed.
Lemma K_rng : 0 <= K /\ K + kcost n <= GKCAP.
Proof. destruct Hpre as (_ & _ & _ & _ & _ & _ & _ & _ & _ & HKc). split; [exact HK0 | exact HKc]. Qed.

(* [comment removed for export] *)
Lemma exit_ainv : AINVop [(u pret, n)] [] (mcost n) MCNT (K + kcost n) M' mdl'.
Proof.
  pose proof (co_ainv HC1) as HA. pose proof n_rng as [N1 N2]. destruct K_rng as [K1 K2]. unfold NMAX in N2. unfold kcost, EVT, GKCAP in K2.
  change (a_vis H1) with [(EP, EVar 10)] in HA. change (a_fake H1) with (@nil (expr * expr)) in HA. change (a_meter H1) with MT1 in HA.
  cbn [blocks_den map fst snd bcost bcount length] in HA. rewrite exit_n in HA.
  assert (EPp : uE E' EP = u pret) by (rewrite exit_p; reflexivity). rewrite EPp in HA.
  assert (EM : uE E' MT1 = K + kcost n).
  { pose proof (U1 10%nat ltac:(lia)) as U10. change (Z.of_nat 10) with 10 in U10.
    unfold uE, MT1, EVT. cbn [edenot]. rewrite !u_add64. cbn [edenot]. rewrite U2.
    rewrite !u64_lit by lia.
    unfold kcost, EVT. rewrite Z.mod_small by lia. lia. }   (* [comment removed for export] *)
  rewrite EM in HA. change (bcount [(EP, EVar 10)]) with 1 in HA. unfold mcost, MCNT.
  replace (n + AzIface.MBLK) with (n + MBLK + 0) by (unfold AzIface.MBLK, MBLK; lia). exact HA.
Qed.
(* [comment removed for export] *)
Lemma exit_changed : forall a : word, M' a <> M a -> hchanged G MSTK_N L LF sp a.
Proof.
  intros a Hne. destruct exit_ainv as (_ & _ & _ & HZ & _).
  destruct sp_facts as (S1 & S2 & S3 & S4).
  destruct (AzCall.in_wins_dec G ERRW (u a)) as [Hew|Hnew].
  { right; right. destruct Hew as (lo & hi & [H|[]] & Hz). injection H as <- <-. exists (g_errno G), (g_errno G + 4). split; [left; reflexivity | exact Hz]. }
  assert (ND : ~ (in_blocks L (u a) \/ in_blocks LF (u a) \/ sp <= u a
                  \/ (g_ro_lo G <= u a < g_img_hi G /\ ~ in_wins (g_privx G) (u a))
                  \/ in_lshadow (L ++ LF) (u a) \/ in_sshadow (u a) \/ in_ishadow G (u a) \/ (CEIL_run <= u a < sp - MSTK_N))).
  { intros D. apply Hne. apply HZ. split; [exact D | split; exact Hnew]. }
  destruct (Z_lt_le_dec (u a) CEIL_run) as [Hlo|Hhi].
  - destruct (Z_lt_le_dec (u a) (g_img_lo G)) as [Hb|Hb]; [| destruct (Z_lt_le_dec (u a) (g_img_hi G)) as [Hi|Hi]].
    + right; left. split; [exact Hlo|]. split; [lia|]. intros [V|[V|[V|[V|V]]]]; apply ND; tauto.
    + right; right. destruct (AzCall.in_wins_dec G (g_privx G) (u a)) as [Hp|Hp]; [exact Hp|].
      exfalso. apply ND. right; right; right; left. split; [cbn [g_ro_lo g_img_lo GASAN] in *; lia | exact Hp].
    + right; left. split; [exact Hlo|]. split; [lia|]. intros [V|[V|[V|[V|V]]]]; apply ND; tauto.
  - left. unfold scratch.
    destruct (Z_lt_le_dec (u a) sp) as [Hs|Hs]; [|exfalso; apply ND; tauto].
    destruct (Z_lt_le_dec (u a) (sp - MSTK_N)) as [Hf|Hf]; [exfalso; apply ND; right; right; right; right; right; right; right; lia | lia].
Qed.
(* [comment removed for export] *)
Lemma exit_geom : ablk_ok G (u pret) n /\ u pret mod 8 = 0
  /\ (forall b m, In (b, m) (L ++ LF) -> u pret + n <= b \/ b + m <= u pret).
Proof.
  destruct exit_ainv as (HA & _). cbn [app] in HA.
  destruct (hp_zone _ _ _ _ HPop _ _ _ _ _ _ _ (u pret) n HA ltac:(left; reflexivity)) as [Z1 Z2].
  split; [exact Z1|]. split; [exact Z2|].
  intros b m Hin. apply in_app_iff in Hin as [Hin|Hin].
  - exact (hp_disj _ _ _ _ HPop _ _ _ _ _ _ _ [] L (u pret) n b m HA eq_refl Hin).
  - exact (hp_bfdisj _ _ _ _ HPop _ _ _ _ _ _ _ (u pret) n b m HA ltac:(left; reflexivity) Hin).
Qed.

(* [comment removed for export] *)
Lemma exit_ainvh : AzBridgeH.AINVH_bt bt ((u pret, n) :: L) LF (B + mcost n) (C + MCNT) (K + kcost n) M' mdl'.
Proof. destruct exit_ainv as (HA & _). cbn [app] in HA. exact (AzBridgeOp.AINVH_op_bt_grown bt G n L _ _ _ _ _ _ _ HA). Qed.
Lemma exit_bigal : 64512 < n -> u pret mod 4096 = 2048.
Proof.
  intros Hb. destruct exit_ainvh as (FF & _ & (HA & _)).
  exact (AsAinvEntry3.AsAinvFacts3c.BIGAL bt None _ _ _ _ _ _ _ (u pret) n HA ltac:(left; reflexivity) Hb).
Qed.

Lemma exit_model : nmodel mdl mdl'.
Proof.
  split; [exact (co_halt HC1)|]. split; [exact (co_fs HC1)|].
  pose proof (co_fds HC1) as X. change (a_fd H1) with FdStd in X. cbn [APS.fds_ok] in X. rewrite X, HFDS. reflexivity.
Qed.
Lemma exit_errno : errno_kept G M M'.
Proof. destruct exit_ainv as (_ & _ & _ & _ & HD). intros a Hew HM. apply HD; [right; right; exact Hew | exact HM]. Qed.
(* [comment removed for export] *)
#[local] Notation MR1 := (GPS.Mr SHCb VSHo E' H1 mdl' M').
Lemma exit_kn : kentry_ok ASEGS E' MR1 (KAlign EP 16) /\ kentry_ok ASEGS E' MR1 (KWr (SA EP 0) (EVar 10))
  /\ kentry_ok ASEGS E' MR1 (KShOk (SA EP 0) (EVar 10)) /\ kentry_ok ASEGS E' MR1 (KWr (SA ESP (-3600)) (ELit 3600)).
Proof.
  pose proof (co_know HC1) as HK. change (kn H1) with KN1 in HK. unfold KN1, KN0, know_ok in HK.
  apply Forall_app in HK as [HK1 HKr]. apply Forall_app in HKr as [HKz _].
  pose proof (proj1 (Forall_forall _ _) HK1) as F1. pose proof (proj1 (Forall_forall _ _) HKz) as F0.
  split; [apply F1; left; reflexivity|]. split; [apply F1; right; left; reflexivity|].
  split; [apply F1; right; right; left; reflexivity|]. apply F0. right; right; right; left; reflexivity.
Qed.

Lemma exit_vis : forall a : word,
  (u pret <= u a < u pret + n) \/ CEIL_run <= u a \/ in_shadow SB (u pret) n (u a) -> MR1 a = M' a.
Proof.
  intros a Ha. unfold GPS.Mr. apply mrestrict_visible.
  pose proof (co_ainv HC1) as HA.
  assert (BD : blocks_den E' (a_vis H1) ++ blocks_den E' (a_fake H1) = [(u pret, n)]).
  { change (a_vis H1) with [(EP, EVar 10)]. change (a_fake H1) with (@nil (expr * expr)). cbn [blocks_den map fst snd app].
    rewrite exit_n. replace (uE E' EP) with (u pret) by (rewrite exit_p; reflexivity). reflexivity. }
  destruct Ha as [Hb|[Hs|Hsh]].
  - eapply (AzNodesAlloc3.hid_app_falseX AASAN ERRW ERRW sp SHCb VSHo G asan_A_img_hi asan_A_img_lo ERRW_img' AINVop IFop E' H1 mdl' _ _ _ M' a HA).
    left. rewrite BD. exists (u pret), n. split; [left; reflexivity | exact Hb].
  - eapply (AzNodesAlloc3.hid_app_falseX AASAN ERRW ERRW sp SHCb VSHo G asan_A_img_hi asan_A_img_lo ERRW_img' AINVop IFop E' H1 mdl' _ _ _ M' a HA).
    right; right; left. exact Hs.
  - apply (hid_shadow_false SHCb VSHo G (hp_shc_stack _ _ _ _ HPop) (hp_shc_image _ _ _ _ HPop)). left.
    rewrite AzNodesAlloc.blocks_den_app, BD. exists (u pret), n. split; [left; reflexivity | exact Hsh].
Qed.
Lemma exit_align : u pret mod 16 = 0.
Proof. destruct exit_kn as (A & _). cbn [kentry_ok] in A. destruct A as [_ A]. cbn [edenot EP] in A. rewrite <- exit_p in A. exact A. Qed.

Lemma exit_block : forall a : word, u pret <= u a < u pret + n ->
  M' a <> None /\ RiscvSemantics.store_ok ASEGS M' a 1 = true.
Proof.
  intros a Ha. destruct exit_kn as (_ & W & _). cbn [kentry_ok] in W. destruct W as [Wf W].
  assert (ES : estart E' (SA EP 0) = u pret) by (unfold estart; cbn [a_base a_off edenot EP]; rewrite <- exit_p; lia).
  assert (EL : elenZ E' (EVar 10) = n) by exact exit_n.
  specialize (W (u a - u pret) 1%nat ltac:(lia) ltac:(rewrite EL; lia)). rewrite ES in W.
  replace (u pret + (u a - u pret)) with (u a) in W by lia. rewrite Z_to_bv_bv_unsigned in W.
  apply store_ok_mrestrict_full in W.
  split; [|exact W].
  destruct exit_geom as ((_ & _ & Gi & _) & _ & _).
  apply (AzFrame.store_ok_defined ASEGS G asan_segs_out M' a); [|exact W]. cbn [g_img_lo g_img_hi GASAN] in *. lia.
Qed.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Lemma exit_shok : forall z, u pret <= z < u pret + n ->
  exists b : byte, M' (Z_to_bv 64 (SB + z / 8)) = Some b /\ (u b = 0 \/ z mod 8 < u b <= 7).
Proof.
  intros z Hz. destruct exit_kn as (_ & _ & S & _). cbn [kentry_ok] in S. destruct S as (Sf & S47 & S).
  assert (ES : estart E' (SA EP 0) = u pret) by (unfold estart; cbn [a_base a_off edenot EP]; rewrite <- exit_p; lia).
  assert (EL : elenZ E' (EVar 10) = n) by exact exit_n.
  rewrite ES, EL in S, S47. destruct (S z Hz) as (b & Hb & Hv). exists b. split; [|exact Hv].
  rewrite <- Hb. symmetry. apply exit_vis. right; right.
  pose proof n_rng as [N1 _]. pose proof (u64_range pret) as RP.
  rewrite u64_lit by (unfold SB; lia). unfold in_shadow, SB. lia.
Qed.

Lemma exit_shw : forall a : word, in_shadow SB (u pret) n (u a) -> RiscvSemantics.store_ok ASEGS M' a 1 = true.
Proof.
  intros a [H1 H2]. destruct exit_geom as (_ & P8 & _). pose proof n_rng as [N1 _].
  set (z := Z.max (u pret) (8 * (u a - SB))).
  assert (Hz : u pret <= z < u pret + n) by (subst z; lia).
  assert (Ez : SB + z / 8 = u a) by (subst z; lia).
  destruct (exit_shok z Hz) as (b & Hb & _). rewrite Ez, Z_to_bv_bv_unsigned in Hb.
  apply store_ok_of_all; [pose proof (u64_range a); lia|]. intros x Hx.
  assert (x = a) by (apply bv_eq; lia). subst x. unfold wview. rewrite Hb. discriminate.
Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Lemma exit_scratch : scratch_ok ASEGS M' sp MSTK_N.
Proof.
  intros a Ha. unfold scratch, MSTK_N in Ha. destruct exit_kn as (_ & _ & _ & W). cbn [kentry_ok] in W. destruct W as [Wf W].
  destruct sp_facts as (S1 & S2 & S3 & S4). unfold MSTK_N in S3.
  assert (USP : u (edenot E' ESP) = sp) by (cbn [edenot ESP]; rewrite (U1 2%nat ltac:(lia)); exact S1).
  assert (ES : estart E' (SA ESP (-3600)) = sp - 3600) by (unfold estart; cbn [a_base a_off]; rewrite USP; lia).
  assert (EL : elenZ E' (ELit 3600) = 3600) by (unfold elenZ; cbn [edenot]; apply u64_lit; lia).
  specialize (W (u a - (sp - 3600)) 1%nat ltac:(lia) ltac:(rewrite EL; lia)). rewrite ES in W.
  replace (sp - 3600 + (u a - (sp - 3600))) with (u a) in W by lia. rewrite Z_to_bv_bv_unsigned in W.
  apply store_ok_mrestrict_full in W. split; [|exact W].
  apply (AzFrame.store_ok_defined ASEGS G asan_segs_out M' a); [|exact W].
  pose proof (AzFrame.G_img_ceil G GA_img_al GA_img_shlo) as GC. lia.
Qed.

(* [comment removed for export] *)
Theorem exit_post : hmalloc_post_ok ASEGS G fx_ok (AzBridgeH.AINVH_bt bt) R M mdl L LF B C K n sp MSTK_N fx' R' M' mdl' pret.
Proof.
  destruct exit_geom as (GA & _ & GD).
  unfold hmalloc_post_ok.
  split; [exact (co_fx HC1)|]. split; [exact exit_regs_kept|]. split; [reflexivity|]. split; [exact exit_align|].
  split; [exact GA|]. split; [exact exit_bigal|]. split; [exact GD|]. split; [exact exit_block|]. split; [exact exit_shok|].
  split; [exact exit_shw|]. split; [exact exit_changed|]. split; [exact exit_errno|]. split; [exact exit_scratch|].
  split; [exact exit_ainvh | exact exit_model].
Qed.
End Exit.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Hypothesis G_tp : g_tp G = AsVocab.AsCells.ia_tp IA.
Hypothesis G_errno : g_errno G = AsVocab.ia_errno IA.
Hypothesis G_privs : forall z, AsVocab.in_wins (AsVocab.AsCells.ia_priv IA) z -> in_wins (g_priv G) z.
Hypothesis G_malloc_thunk : g_malloc_thunk G = AsVocab.AsCells.ia_malloc_thunk IA.
Hypothesis G_stkmal : forall k, 0 <= k <= 3 -> g_stkmal G k = AsVocab.AsCells.ia_stkmal IA k.
Hypothesis G_amemcpy : g_amemcpy G = AsVocab.AsCells.ia_asan_memcpy IA.

Lemma bcap_op : B + (GBUDGET - B) <= GBUDGET. Proof. lia. Qed.
Lemma ccap_op : C + (GCOUNT - C) <= GCOUNT. Proof. lia. Qed.

Lemma UINVop_n : forall E, UINVop E -> uE E (EVar 10) = n.
Proof.
  intros E [U1 _]. destruct Hpre as (_ & _ & _ & _ & Hn & _). unfold uE. cbn [edenot]. rewrite (U1 10%nat ltac:(lia)). exact Hn.
Qed.
Lemma UINVop_K : forall E, UINVop E -> uE E (EVar 33) = K.
Proof.
  intros E [_ U2]. destruct Hpre as (_ & _ & _ & _ & _ & Hnr & _ & _ & _ & HKc). unfold uE. cbn [edenot]. rewrite U2.
  apply u64_lit. unfold kcost, EVT, GKCAP in HKc. lia.
Qed.
Lemma HNBFop : AzNodesAlloc3.NBF UINVop (GBUDGET - B) (GCOUNT - C) 10 33.
Proof.
  intros E HU. rewrite (UINVop_n E HU), (UINVop_K E HU).
  destruct Hpre as (_ & _ & _ & _ & _ & _ & _ & HB & HCc & HKc). lia.
Qed.

Section Body.
Variable T : TSet.
Hypothesis HT : T [].
(* [comment removed for export] *)
Definition HOLESop : nat -> env -> Fs.Fs -> TSet := fun _ _ _ => T.
#[local] Notation holes_at := (GPS.holes_stmt ASEGS).

(* [comment removed for export] *)
Lemma cs_ok_model : forall E cs fx' R' M' m1 m2,
  cs_okop E cs fx' R' M' m1 ->
  GPS.hid SHCb VSHo E cs m2 = GPS.hid SHCb VSHo E cs m1 -> m_halted m2 = None -> m_fs m2 = m_fs m1 -> m_fds m2 = m_fds m1 ->
  AINVop (blocks_den E (a_vis cs)) (blocks_den E (a_fake cs)) (bcost E (a_vis cs)) (bcount (a_vis cs)) (uE E (a_meter cs)) M' m2 ->
  cs_okop E cs fx' R' M' m2.
Proof.
  intros E cs fx' R' M' m1 m2 [CR CL CK CH CF CD CA CU CX CP CT CK2 CFB CFL] Hh Hha Hfs Hfds HA.
  constructor; try assumption.
  - unfold GPS.Mr in *. rewrite Hh. exact CK.
  - rewrite Hfs. exact CF.
  - eapply GPS.fds_ok_model; [exact Hfds | exact Hfs | exact CD].
Qed.

Section GenRZ.
Variable RZg : GPS.rz_t.
Hypothesis RZg_kc : forall T, AsIface3.AsK.kclosedD ASEGS (fun c => RZg c T).
Hypothesis RZg_silent1 : GPS.RZ_SILENT1 ASEGS RZg.
Hypothesis RZg_exit : GPS.RZ_EXIT ASEGS RZg.
Hypothesis RZg_conseq : GPS.RZ_CONSEQ RZg.
(* [comment removed for export] *)
Hypothesis Hk_j : forall fx' R' M' mdl' (p : word),
  hmalloc_post_ok ASEGS G fx_ok (AzBridgeH.AINVH_bt bt) R M mdl L LF B C K n sp MSTK_N fx' R' M' mdl' p ->
  RZg (cfgF ASEGS fx' R' ret M' mdl') T.

(* [comment removed for export] *)
Lemma op_sound_j : forall HSx,
  GPS.holes_stmt ASEGS HSx ERRW sp (m_fs mdl) SHCb VSHo AINVop GKCAP (FMIN - Z.of_nat (length LF)) fx_ok UINVop HOLESop RZg ->
  forall p cs s, gplan_ok p = true -> CHKl HSx cs p = COk s ->
  forall E fx' R' M' mdl', cs_okop E cs fx' R' M' mdl' ->
    RZg (cfgF ASEGS fx' R' (pc cs) M' mdl') (GPS.sd HOLESop T E (m_fs mdl') s).
Proof.
  intros HSx HSx_sound p cs s Hg Hc E fx' R' M' mdl' HC.
  pose proof (AzOpNewS.op_check_sound_live_j bt ASEGS fx_ok FRESH ASC G G_imglo G_hi asan_G_ro_img2 GA_img_al GA_img_shlo GASAN_priv G_privs G_tp G_errno GASAN_errno
           G_malloc_thunk GA_newh_img asan_segs_out asan_segs_wx ERRW SWIN_ok ERRW_img ERRW sp L LF M B C
           (GBUDGET - B) (GCOUNT - C) bcap_op ccap_op (FMIN - Z.of_nat (length LF)) AASAN asan_A_img_hi asan_A_img_lo asan_hull_ok
           GKCAP (Z.le_refl _) IT_N IT_N_ok NXF 0 0%nat (m_fs mdl) HSx (RUN_sound_fx ASEGS) n 10%nat 33%nat UINVop UINVop_agree HNBFop UINVop_n
           HOLESop (fun _ _ _ _ _ => eq_refl) (fun _ _ _ => HT) (fun _ _ _ => eq_refl) RZg RZg_kc RZg_silent1 RZg_exit RZg_conseq HSx_sound
           400%nat 400%nat None p cs s Hg) as X.
  rewrite CHKl_eq in Hc. exact (X Hc E fx' R' M' mdl' T HC I HT).
Qed.

(* [comment removed for export] *)
Lemma hole1_j : forall E fx' R' M' mdl', cs_okop E H1 fx' R' M' mdl' -> RZg (cfgF ASEGS fx' R' (pc H1) M' mdl') T.
Proof.
  intros E fx' R' M' mdl' HC.
  eapply (GPS.restricted_run_sound ASEGS AASAN ERRW sp (m_fs mdl) SHCb VSHo AINVop GKCAP (FMIN - Z.of_nat (length LF))
            (AINV_f_lazy ERRW G SHCb AINVHop HPop ERRW sp L LF M B C)
            (AzFrameAlloc.If_facts ERRW G SHCb ERRW sp L LF M B C AASAN asan_A_img_hi asan_A_img_lo AINVHop HPop)
            fx_ok UINVop RZg RZg_silent1 asan_in_hull asan_segs_wx E H1 fx' R' M' mdl' _ T HC).
  { eapply msteps_one; [reflexivity|].
    change (restrict (GPS.hid SHCb VSHo E H1 mdl') (mkstF fx' R' (Z_to_bv 64 (pc H1)) M' (seg_rom ASEGS)))
      with (mkstF fx' R' (Z_to_bv 64 (pc H1)) (GPS.Mr SHCb VSHo E H1 mdl' M') (seg_rom ASEGS)).
    apply (AzCall.is_ret_at_sound ASEGS). vm_compute. reflexivity. }
  intros model' Hsame Hhid Hhalt' Hfs2 Hfds2 HAm Hclean.
  unfold unrestrict. cbn [ms_regs ms_fregs ms_pc_val ms_svc_pending ms_resv ms_fcsr ms_mem ms_rom mkstF mkst].
  unfold GPS.Mr. rewrite munrestrict_mrestrict.
  pose proof (cs_ok_model E H1 fx' R' M' mdl' model' HC Hhid Hhalt' Hfs2 Hfds2 HAm) as HC'.
  destruct Hpre as (_ & _ & _ & (Hr1 & Hr2 & Hr3 & _) & _).
  assert (HR1 : getr R' (Z_to_bv 5 1) = Z_to_bv 64 ret).
  { change (Z_to_bv 5 1) with (Z_to_bv 5 (Z.of_nat 1)). rewrite (exit_reg E fx' R' M' model' HC' 1%nat ltac:(lia)).
    change (edenot E (reg H1 1)) with (ev E 1%nat). rewrite (proj1 (co_uinv HC') 1%nat ltac:(lia)). exact Hr1. }
  rewrite HR1.
  assert (Hro : ret_ok (Z_to_bv 64 ret)) by (apply ret_ok_even; rewrite u64_lit by lia; exact Hr3).
  unfold ret_ok in Hro. rewrite Hro.
  apply (Hk_j fx' R' M' model' (pret R')). exact (exit_post E fx' R' M' model' HC').
Qed.

Lemma holes_j : GPS.holes_stmt ASEGS HS1 ERRW sp (m_fs mdl) SHCb VSHo AINVop GKCAP (FMIN - Z.of_nat (length LF)) fx_ok UINVop HOLESop RZg.
Proof.
  intros h ch Hh E fx' R' M' mdl' HC. destruct h as [|[|h]]; try discriminate Hh; injection Hh as <-.
  exact (hole1_j E fx' R' M' mdl' HC).
Qed.

Theorem opnew_run_j : RZg (cfgF ASEGS fx R (g_opnew G) M mdl) T.
Proof.
  pose proof (op_sound_j HS1 holes_j PLAN_E1 H0 _ plans_ok certE1_ok E0 fx R M mdl entry_cs_ok) as X.
  cbn [GPS.sd] in X. exact X.
Qed.
End GenRZ.

(* [comment removed for export] *)
Hypothesis Hk : forall fx' R' M' mdl' (p : word),
  hmalloc_post_ok ASEGS G fx_ok (AzBridgeH.AINVH_bt bt) R M mdl L LF B C K n sp MSTK_N fx' R' M' mdl' p ->
  rrealizes ASEGS (cfgF ASEGS fx' R' ret M' mdl') T.





(* [comment removed for export] *)
Hypothesis Hk_f : forall fx' R' M' mdl' (p : word),
  hmalloc_post_ok ASEGS G fx_ok (AzBridgeH.AINVH_bt bt) R M mdl L LF B C K n sp MSTK_N fx' R' M' mdl' p ->
  realizes ASEGS (cfgF ASEGS fx' R' ret M' mdl') T.

End Body.

End TopA.


(* [comment removed for export] *)
Theorem opnew_h_A_j : forall {RC : run_ceil} (bt : AsAinvDefs3.as_boot)
    (FRESH : list (Z * Z) -> list (Z * Z) -> Z -> Z -> Z -> (word -> option byte) -> Model -> Z -> Prop),
  AsIfaceNM3.as_contracts_n ASEGS fx_ok (AsAinvDefs3.bt_ia bt) (AsAinvEntry3.AsAinvHole3.AAINV_HS bt) FRESH (AsAinvDefs3.bt_fs bt) ->
  g_img_lo GASAN = AsVocab.AsCells.ia_img_lo (AsAinvDefs3.bt_ia bt) ->
  g_img_hi GASAN = AsVocab.AsCells.ia_img_hi (AsAinvDefs3.bt_ia bt) ->
  AsVocab.as_wins_ok (AsAinvDefs3.bt_ia bt) ERRW ->
  g_tp GASAN = AsVocab.AsCells.ia_tp (AsAinvDefs3.bt_ia bt) ->
  g_errno GASAN = AsVocab.ia_errno (AsAinvDefs3.bt_ia bt) ->
  (forall z, AsVocab.in_wins (AsVocab.AsCells.ia_priv (AsAinvDefs3.bt_ia bt)) z -> in_wins (g_priv GASAN) z) ->
  g_malloc_thunk GASAN = AsVocab.AsCells.ia_malloc_thunk (AsAinvDefs3.bt_ia bt) ->
  (forall k, 0 <= k <= 3 -> g_stkmal GASAN k = AsVocab.AsCells.ia_stkmal (AsAinvDefs3.bt_ia bt) k) ->
  g_amemcpy GASAN = AsVocab.AsCells.ia_asan_memcpy (AsAinvDefs3.bt_ia bt) ->
  forall RZg : GPS.rz_t, (forall T, AsIface3.AsK.kclosedD ASEGS (fun c => RZg c T)) -> GPS.RZ_SILENT1 ASEGS RZg -> GPS.RZ_EXIT ASEGS RZg -> GPS.RZ_CONSEQ RZg ->
  h_alloc1_at ASEGS GASAN fx_ok RZg (AzBridgeH.AINVH_bt bt) AzBridgeC3.FPCw (hopnew_x ASEGS GASAN) MSTK_N (g_opnew GASAN).
Proof.
  intros RC bt FRESH ASC Gl Gh SW Gtp Ger Gpr Gmt Gsk Gam RZg RZg_kc RZg_silent1 RZg_exit RZg_conseq fx R M mdl L LF B C K ret n sp T Hpre HX HFDS HLF HT Hk.
  assert (HK0 : 0 <= K).
  { destruct Hpre as (_ & _ & (FF & _ & (HA & _)) & _).
    pose proof (AsVocab.aap_bounds _ _ _ _ (AsAinvFrame3b.AAINV_props_all bt (AsAinvEntry3.AsAinvHole3.holes_lsopt None)) L FF B C K M mdl HA) as X. lia. }
  eapply opnew_run_j; eassumption.   (* [comment removed for export] *)
Qed.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma asan_errw_ok : AsVocab.as_wins_ok AsVocab.AsCells.asan_addrs ERRW.
Proof.
  intros a (lo & hi & [H|[]] & Ha). injection H as <- <-. cbn [g_errno GASAN] in Ha.
  split; [cbn; lia|]. split; [|split].
  - intros (plo & phi & Hin & Hp). cbn in Hin. repeat (destruct Hin as [Hin|Hin]; [injection Hin as <- <-; lia|]). destruct Hin.
  - unfold AsVocab.in_rtc. cbn. lia.
  - intros (plo & phi & Hin & Hp). cbn in Hin. repeat (destruct Hin as [Hin|Hin]; [injection Hin as <- <-; lia|]). destruct Hin.
Qed.

Theorem opnew_h_asan_j : forall {RC : run_ceil} (bt : AsAinvDefs3.as_boot)
    (FRESH : list (Z * Z) -> list (Z * Z) -> Z -> Z -> Z -> (word -> option byte) -> Model -> Z -> Prop),
  AsAinvDefs3.bt_ia bt = AsVocab.AsCells.asan_addrs ->
  AsIfaceNM3.as_contracts_n ASEGS fx_ok (AsAinvDefs3.bt_ia bt) (AsAinvEntry3.AsAinvHole3.AAINV_HS bt) FRESH (AsAinvDefs3.bt_fs bt) ->
  forall RZg : GPS.rz_t, (forall T, AsIface3.AsK.kclosedD ASEGS (fun c => RZg c T)) -> GPS.RZ_SILENT1 ASEGS RZg -> GPS.RZ_EXIT ASEGS RZg -> GPS.RZ_CONSEQ RZg ->
  h_alloc1_at ASEGS GASAN fx_ok RZg (AzBridgeH.AINVH_bt bt) AzBridgeC3.FPCw (hopnew_x ASEGS GASAN) MSTK_N (g_opnew GASAN).
Proof.
  intros RC bt FRESH BT ASC RZg RZg_kc RZg_silent1 RZg_exit RZg_conseq. apply (opnew_h_A_j bt FRESH ASC); rewrite ?BT; try reflexivity; try assumption.
  - exact asan_errw_ok.
  - intros z Hz. exact Hz.
Qed.

