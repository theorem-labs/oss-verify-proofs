(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.glaze.binary_reflection.lib Require BvWfKernel.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require WdZS.
(* [comment removed for export] *)
Require Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.Bool.Bool LinuxProcessSemantics.LinuxProcessSem.MemImageType OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3 OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3B OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlanCore OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlan OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzIface OSSVerify.Proofs.glaze.binary_reflection.lib.GlzCall OSSVerify.Proofs.glaze.binary_reflection.lib.B2JCutShare OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhDefs OSSVerify.Proofs.glaze.binary_reflection.lib.GlzImageUbsan OSSVerify.Proofs.glaze.binary_reflection.lib.UbDrvHooks OSSVerify.Proofs.glaze.binary_reflection.lib.GlzSpecsStr OSSVerify.Proofs.glaze.binary_reflection.lib.UbDrvS3Plan.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module UbDrvTPlan.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3 OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3B OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlanCore OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlan OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzIface OSSVerify.Proofs.glaze.binary_reflection.lib.GlzCall OSSVerify.Proofs.glaze.binary_reflection.lib.B2JCutShare.GlzCallCert OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhDefs.UbImg OSSVerify.Proofs.glaze.binary_reflection.lib.GlzImageUbsan OSSVerify.Proofs.glaze.binary_reflection.lib.UbDrvHooks.GuFuzzT OSSVerify.Proofs.glaze.binary_reflection.lib.UbDrvHooks.UbDrvIT OSSVerify.Proofs.glaze.binary_reflection.lib.GlzSpecsStr.UbDrvNodes OSSVerify.Proofs.glaze.binary_reflection.lib.UbDrvHooks OSSVerify.Proofs.glaze.binary_reflection.lib.UbDrvS3Plan.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AP.
Open Scope Z_scope.

(* [comment removed for export] *)
Definition S : list Z := [P_FZ; P_STDIO_WRITE; P_FREE_T; P_EXIT].
Definition SM : list Z := P_MEMCPY :: S.

Definition p_tail : plan := PRun S (PExt 11 [] (PRun S (PEmit 65 [] PExit))).      (* [comment removed for export] *)
Definition p_after : plan := PExt 11 [] (PRun S (PCase2 B1S M63 p_tail p_tail)).


(* [comment removed for export] *)
Fixpoint p_callsL (c : expr) (fz : nat) (more : nat) (j : Z) (first : bool) : plan :=
  let nxt := match more with
             | O => PRun S p_after
             | Datatypes.S m => PSplit c j (PRun S p_after) (PRun S (p_callsL c fz m (j + 1) false))
             end in
  PExt fz [ELit 0x8ab90] (if first then PRun S (PExt 63 [] (PRun S (PEmit 64 [] nxt))) else nxt).
Definition planE (calls : expr) : plan := PRun S (p_callsL calls 121 3 1 true).
Definition planN (calls : expr) : plan := PRun SM (PExt 1 [] (PRun S (p_callsL calls 120 3 1 true))).

(* [comment removed for export] *)
Definition tinEA : acs := holeEA.   Definition tinPA : acs := holePA.
Definition tinEB : acs := holeEB.   Definition tinPB : acs := holePB.
Definition okchild (h : acs) : acs := match node_alloc NXD GDRV BCAP CCAP P_MALLOC_T h with Some c => c | None => h end.
Definition tinNA : acs := okchild tinPA.
Definition tinNB : acs := okchild tinPB.
Definition CALLSA : expr := ELit 1.

(* [comment removed for export] *)
Fixpoint zl (n : nat) : list Z := match n with O => [] | Datatypes.S k => 48 :: 10 :: zl k end.
Definition s_calls (n : nat) : shape :=
  SEmitP 1 [SPLit [48]; SPLit [10]] (SEmitP 1 (match n with 1%nat => [] | _ => [SPLit (zl (n - 1))] end) (SExit 0)).


Definition shapeA : shape := s_calls 1.          (* [comment removed for export] *)
(* [comment removed for export] *)
Definition shapeL (calls : expr) : shape :=
  SEmitP 1 [SPLit [48]; SPLit [10]]
    (SCase calls 1 (SEmitP 1 [] (SExit 0))
      (SCase calls 2 (SEmitP 1 [SPLit (zl 1)] (SExit 0))
        (SCase calls 3 (SEmitP 1 [SPLit (zl 2)] (SExit 0)) (SEmitP 1 [SPLit (zl 3)] (SExit 0))))).
Definition shapeB : shape := shapeL CALLSB.

(* [comment removed for export] *)
Lemma certEA : CHKf HS0 BF FUEL tinEA (planE CALLSA) = COk shapeA. Proof. match goal with |- @eq ?A ?l ?r => vm_cast_no_check (@eq_refl A r) end. Qed.
Lemma certNA : CHKf HS0 BF FUEL tinNA (planN CALLSA) = COk shapeA. Proof. match goal with |- @eq ?A ?l ?r => vm_cast_no_check (@eq_refl A r) end. Qed.
Lemma certEB : CHKf HS0 BF FUEL tinEB (planE CALLSB) = COk shapeB. Proof. match goal with |- @eq ?A ?l ?r => vm_cast_no_check (@eq_refl A r) end. Qed.
Lemma certNB : CHKf HS0 BF FUEL tinNB (planN CALLSB) = COk shapeB. Proof. match goal with |- @eq ?A ?l ?r => vm_cast_no_check (@eq_refl A r) end. Qed.
Lemma planE_ok : forall e, GPS.gplan_ok (planE e) = true. Proof. reflexivity. Qed.
Lemma planN_ok : forall e, GPS.gplan_ok (planN e) = true. Proof. reflexivity. Qed.
(* [comment removed for export] *)
Lemma tinPA_call_ok : call_ok NXD GDRV P_MALLOC_T tinPA = Some P_TR_AFTERM. Proof. match goal with |- @eq ?A ?l ?r => vm_cast_no_check (@eq_refl A r) end. Qed.
Lemma tinPA_alloc : node_alloc NXD GDRV BCAP CCAP P_MALLOC_T tinPA = Some tinNA. Proof. match goal with |- @eq ?A ?l ?r => vm_cast_no_check (@eq_refl A r) end. Qed.
Lemma tinPB_call_ok : call_ok NXD GDRV P_MALLOC_T tinPB = Some P_TR_AFTERM. Proof. match goal with |- @eq ?A ?l ?r => vm_cast_no_check (@eq_refl A r) end. Qed.
Lemma tinPB_alloc : node_alloc NXD GDRV BCAP CCAP P_MALLOC_T tinPB = Some tinNB. Proof. match goal with |- @eq ?A ?l ?r => vm_cast_no_check (@eq_refl A r) end. Qed.
Lemma tinPA_pc : pc tinPA = P_MALLOC_T. Proof. match goal with |- @eq ?A ?l ?r => vm_cast_no_check (@eq_refl A r) end. Qed.
Lemma tinPB_pc : pc tinPB = P_MALLOC_T. Proof. match goal with |- @eq ?A ?l ?r => vm_cast_no_check (@eq_refl A r) end. Qed.


End UbDrvTPlan.
Require Stdlib.NArith.NArith Stdlib.micromega.Lia LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape OSSVerify.Proofs.glaze.binary_reflection.lib.Spec4 OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymStepR OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3Sound OSSVerify.Proofs.glaze.binary_reflection.lib.UbDrvNodesSound.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module UbDrvTSound.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape.ShapeRel OSSVerify.Proofs.glaze.binary_reflection.lib.Spec4.AgentLib OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymStepR OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3 OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3B OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3Sound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound.GxSymRun3 OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlanCore OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlan OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound.GxPlanSound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzIface OSSVerify.Proofs.glaze.binary_reflection.lib.GlzSpecsStr.GlzContracts OSSVerify.Proofs.glaze.binary_reflection.lib.GlzCall.GlzFrame OSSVerify.Proofs.glaze.binary_reflection.lib.GlzCall OSSVerify.Proofs.glaze.binary_reflection.lib.B2JCutShare.GlzCallCert OSSVerify.Proofs.glaze.binary_reflection.lib.GlzSpecsStr.GlzNodesSound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhDefs.UbImg OSSVerify.Proofs.glaze.binary_reflection.lib.GlzImageUbsan OSSVerify.Proofs.glaze.binary_reflection.lib.UbDrvHooks.GuFuzzT OSSVerify.Proofs.glaze.binary_reflection.lib.Spec4 OSSVerify.Proofs.glaze.binary_reflection.lib.UbDrvHooks.UbDrvIT OSSVerify.Proofs.glaze.binary_reflection.lib.GlzSpecsStr.UbDrvNodes OSSVerify.Proofs.glaze.binary_reflection.lib.UbDrvNodesSound OSSVerify.Proofs.glaze.binary_reflection.lib.UbDrvHooks OSSVerify.Proofs.glaze.binary_reflection.lib.UbDrvS3Plan UbDrvTPlan.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AX2S. Import AP. Import APS. Import GPS.
Open Scope Z_scope.

#[local] Notation RSEGS := USEGS.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition PERM_Tc : list (Z * Z) :=
  [(DN.FILE1, DN.FILE1 + 232); (DN.FILE2, DN.FILE2 + 232); (0xab260, 0xab668); (0x8a020, 0x8a028); (0x8a050, 0x8a058);
   (0x7a018, 0x7a019); (0xaabd8, 0xaadfc)].     (* [comment removed for export] *)
(* [comment removed for export] *)
Definition RSTAGE_W : Z * Z := (0x7a019, 0x8a019).
Definition SWIN_T : list (Z * Z) := PERM_Tc ++ [RSTAGE_W].
Lemma PERM_Tc_den : forall E, wins_den E PERM_T = PERM_Tc. Proof. reflexivity. Qed.
Definition UTRUE (E : env) : Prop := True.
Definition HOLES_T (h : nat) (E : env) (fs : Fs.Fs) : TSet := t_nil.

Lemma drv_G_ro_img : g_img_lo GDRV <= g_ro_lo GDRV /\ g_ro_lo GDRV <= g_ro_hi GDRV <= g_img_hi GDRV. Proof. cbn. lia. Qed.
Lemma drv_G_img_ceil {RC : run_ceil} : g_img_hi GDRV <= CEIL_run. Proof. pose proof ceil_rng. cbn [g_img_hi GUBSAN]. lia. Qed.
Lemma drv_G_img_hull : 0 <= g_img_lo GDRV <= g_img_hi GDRV /\ g_img_hi GDRV < 2 ^ 64. Proof. cbn. lia. Qed.
Lemma drv_G_priv : forall lo hi, In (lo, hi) (g_priv GDRV) -> g_ro_hi GDRV <= lo /\ hi <= g_img_hi GDRV.
Proof. intros lo hi H. cbn in H. destruct H as [H|[H|[H|[]]]]; injection H as <- <-; cbn; lia. Qed.
Lemma drv_SEGS_out : forall a : word, ~ (g_img_lo GDRV <= bv_unsigned a < g_img_hi GDRV) -> find_segment RSEGS (bv_unsigned a) 1 = None.
Proof.
  intros a Ha. apply ubsan_in_hull. unfold APS.in_hull. cbn [img_lo img_hi ADRV g_img_lo g_img_hi GDRV] in *.
  destruct (Z_lt_ge_dec (bv_unsigned a) 0x10000) as [H|H].
  - apply Bool.andb_false_iff. left. apply Z.leb_gt. exact H.
  - apply Bool.andb_false_iff. right. apply Z.ltb_ge. lia.
Qed.
Lemma SWIN_T_img : forall lo hi, In (lo, hi) SWIN_T ->
  g_ro_hi GDRV <= lo /\ hi <= g_img_hi GDRV /\ (forall plo phi, In (plo, phi) (g_priv GDRV) -> hi <= plo \/ phi <= lo).
Proof.
  intros lo hi H. unfold SWIN_T, PERM_Tc, RSTAGE_W, DN.FILE1, DN.FILE2 in H. cbn in H.
  destruct H as [H|[H|[H|[H|[H|[H|[H|[H|[]]]]]]]]]; injection H as <- <-; cbn; (split; [lia|]); (split; [lia|]); intros plo phi Hp;
    repeat (destruct Hp as [Hp|Hp]; [injection Hp as <- <-; lia|]); destruct Hp.
Qed.
Lemma SWIN_Tc : forall a, (DN.FILE1 <= a < DN.FILE1 + 232 \/ DN.FILE2 <= a < DN.FILE2 + 232) -> in_wins SWIN_T a.
Proof.
  intros a [H|H]; unfold in_wins, SWIN_T, PERM_Tc.
  - exists DN.FILE1, (DN.FILE1 + 232). split; [left; reflexivity | exact H].
  - exists DN.FILE2, (DN.FILE2 + 232). split; [right; left; reflexivity | exact H].
Qed.
(* [comment removed for export] *)
Lemma PERM_T_SWIN : forall z, in_wins PERM_Tc z -> in_wins SWIN_T z.
Proof. intros z (lo & hi & Hin & Hz). exists lo, hi. split; [| exact Hz]. unfold SWIN_T. apply in_app_iff. left. exact Hin. Qed.

Lemma UTRUE_agree : forall E E', env_agree NXD E E' -> UTRUE E -> UTRUE E'. Proof. intros; exact I. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section TgtSound.
Context {RC : run_ceil}.
(* [comment removed for export] *)
Variable SR : shape_rel RSEGS.
#[local] Notation RZ := (sr_rel RSEGS SR).
Hypothesis SR_det : forall c T T', sr_rel RSEGS SR c T -> realizes RSEGS c T' -> t_eq T T'.
Lemma RZ_step_SR : GPS.RZ_STEP RSEGS RZ. Proof. exact (sr_step RSEGS SR). Qed.
Lemma RZ_msteps_SR : GPS.RZ_MSTEPS RSEGS RZ. Proof. exact (sr_msteps RSEGS SR). Qed.
Lemma RZ_exit_SR : GPS.RZ_EXIT RSEGS RZ. Proof. exact (sr_exit RSEGS SR). Qed.
Lemma RZ_conseq_SR : GPS.RZ_CONSEQ RZ. Proof. exact (sr_conseq RSEGS SR). Qed.

(* [comment removed for export] *)
Variable AINVH : list (Z * Z) -> Z -> Z -> (word -> option byte) -> Model -> Prop.
Hypothesis AINVH_frame : forall L B C M M' mdl,
  AINVH L B C M mdl ->
  (forall a, M' a <> M a -> (in_blocks L (bv_unsigned a) \/ CEIL_run <= bv_unsigned a \/ in_wins SWIN_T (bv_unsigned a)) /\ M' a <> None) ->
  AINVH L B C M' mdl.
Hypothesis AINVH_mono : forall L B C B' C' M mdl, AINVH L B C M mdl -> B <= B' -> C <= C' -> AINVH L B' C' M mdl.
Hypothesis AINVH_zone : forall L B C M mdl b m, AINVH L B C M mdl -> In (b, m) L -> blk_ok GDRV b m.
Hypothesis AINVH_disj : forall L B C M mdl L1 L2 b m b' m',
  AINVH L B C M mdl -> L = L1 ++ (b, m) :: L2 -> In (b', m') (L1 ++ L2) -> b + m <= b' \/ b' + m' <= b.
Hypothesis AINVH_perm : forall L L' B C M mdl, Permutation.Permutation L L' -> AINVH L B C M mdl -> AINVH L' B C M mdl.

(* [comment removed for export] *)
#[local] Notation AINVc TOP M0 := (AINV_f SWIN_T GDRV AINVH PERM_Tc TOP [] M0 0 0).
#[local] Notation cs_okT TOP FS0 M0 := (GPS.cs_ok RSEGS PERM_Tc TOP FS0 fds_std (AINVc TOP M0) fx_ok UTRUE).

(* [comment removed for export] *)
Hypothesis GC_T : forall TOP FS0 M0, gcontracts RSEGS ITD ADRV NXD PERM_Tc TOP FS0 fds_std (AINVc TOP M0) fx_ok UTRUE RZ GDRV BCAP CCAP.
(* [comment removed for export] *)
Hypothesis FZN_sound : callee_contract RSEGS SWIN_T GDRV fx_ok RZ AINVH FuzzN.ce.
Hypothesis FZE_sound : callee_contract RSEGS SWIN_T GDRV fx_ok RZ AINVH FuzzE.ce.
Lemma CT_sound : forall id ce, CT id = Some ce -> callee_contract RSEGS SWIN_T GDRV fx_ok RZ AINVH ce.
Proof.
  intros id ce H. unfold CT in H.
  do 120 (destruct id as [|id]; [discriminate|]).
  destruct id as [|id]; [injection H as <-; exact FZN_sound|].
  destruct id as [|id]; [injection H as <-; exact FZE_sound|]. discriminate.
Qed.
#[local] Notation XN_T := XNt.
#[local] Notation XE_T := XEt.

Lemma XN_T_sound : forall TOP FS0 M0, GPS.ext_stmt RSEGS NXD XN_T PERM_Tc TOP FS0 fds_std (AINVc TOP M0) fx_ok UTRUE RZ.
Proof.
  intros TOP FS0 M0 id args cs cs' E fx R M model T HT HC Hp Hn Hk. unfold XN_T in Hn.
  pose proof (AINV_f_frame SWIN_T GDRV AINVH AINVH_frame AINVH_zone AINVH_disj drv_G_ro_img drv_G_img_ceil PERM_Tc TOP [] M0 0 0) as AF.
  assert (XG : GPS.ext_stmt RSEGS NXD (XNc RSEGS ITD ADRV NXD GDRV BCAP CCAP CT) PERM_Tc TOP FS0 fds_std (AINVc TOP M0) fx_ok UTRUE RZ).
  { apply (XNc_sound RSEGS ITD ADRV ubsan_in_hull ubsan_hull_ok ITD_ok NXD SWIN_T GDRV BCAP CCAP fx_ok RZ RZ_step_SR AINVH AINVH_frame AINVH_zone AINVH_disj AINVH_perm
             drv_G_ro_img drv_G_img_ceil drv_G_img_hull SWIN_T_img drv_SEGS_out PERM_Tc TOP FS0 fds_std [] M0 0 0
             ltac:(lia) ltac:(lia) ltac:(unfold BCAP; lia) ltac:(unfold CCAP; lia) UTRUE UTRUE_agree CT CT_sound).
    apply GC_T. }
  do 63 (destruct id as [|id]; [exact (XG _ args cs cs' E fx R M model T HT HC Hp Hn Hk)|]).
  destruct id as [|id]; [| exact (XG _ args cs cs' E fx R M model T HT HC Hp Hn Hk)].
  exact (node_ioctl_sound SR NXD SWIN_T PERM_Tc TOP FS0 fds_std (AINVc TOP M0) AF fx_ok UTRUE
           ltac:(reflexivity) ltac:(reflexivity) cs cs' E fx R M model T HT HC Hp Hn Hk).
Qed.

Lemma XE_T_sound : forall TOP FS0 M0, GPS.emit_stmt RSEGS NXD XE_T PERM_Tc TOP FS0 fds_std (AINVc TOP M0) fx_ok UTRUE RZ.
Proof.
  intros TOP FS0 M0. unfold XE_T.
  pose proof (AINV_f_frame SWIN_T GDRV AINVH AINVH_frame AINVH_zone AINVH_disj drv_G_ro_img drv_G_img_ceil PERM_Tc TOP [] M0 0 0) as AF.
  exact (XEd_sound SR NXD SWIN_T PERM_Tc TOP FS0 fds_std (AINVc TOP M0) AF fx_ok UTRUE UTRUE_agree SR_det SWIN_Tc ltac:(reflexivity) ltac:(reflexivity)).
Qed.

Lemma XB_T_sound : forall TOP FS0 M0, GPS.ext2_stmt RSEGS NXD XB0 PERM_Tc TOP FS0 fds_std (AINVc TOP M0) fx_ok UTRUE RZ.
Proof. intros TOP FS0 M0 id args cs csa csb E1 fx1 R1 M1 m1 T1 HC1 Hn. discriminate Hn. Qed.
Lemma XC_T_sound : forall TOP FS0 M0, GPS.alt2x_stmt RSEGS NXD XC0 PERM_Tc TOP FS0 fds_std (AINVc TOP M0) fx_ok UTRUE RZ.
Proof. intros TOP FS0 M0 id args cs csa csb E1 fx1 R1 M1 m1 Ta Tb _ Hn. discriminate Hn. Qed.
Lemma HS_T_sound : forall TOP FS0 M0, GPS.holes_stmt RSEGS HS0 PERM_Tc TOP FS0 fds_std (AINVc TOP M0) fx_ok UTRUE HOLES_T RZ.
Proof. intros TOP FS0 M0 h ch Hh. discriminate Hh. Qed.

(* [comment removed for export] *)
Theorem drv_cert_sound : forall TOP M0 bf fuel p cs s E fx R M model,
  gplan_ok p = true -> CHKf HS0 bf fuel cs p = COk s ->
  cs_okT TOP (m_fs model) M0 E cs fx R M model ->
  RZ (cfgF RSEGS fx R (pc cs) M model) (sd HOLES_T t_nil E (m_fs model) s).
Proof.
  intros TOP M0 bf fuel p cs s E fx R M model Hp CERT HC.
  pose proof (AINV_f_frame SWIN_T GDRV AINVH AINVH_frame AINVH_zone AINVH_disj drv_G_ro_img drv_G_img_ceil PERM_Tc TOP [] M0 0 0) as AF.
  refine (GPS.check_sound RSEGS ITD ITD_ok ADRV NXD LIMIT HS0 XN_T XE_T XB0 XC0 0%nat SWIN_T PERM_Tc TOP (m_fs model) fds_std (AINVc TOP M0) AF
            fx_ok UTRUE UTRUE_agree HOLES_T (fun _ _ _ _ _ => eq_refl) (fun _ _ _ => eq_refl) (fun _ _ _ => eq_refl)
            RZ RZ_step_SR RZ_msteps_SR RZ_exit_SR RZ_conseq_SR (RUN_sound_fx RSEGS) ubsan_in_hull ubsan_hull_ok
            (XN_T_sound TOP (m_fs model) M0) (XE_T_sound TOP (m_fs model) M0) (XB_T_sound TOP (m_fs model) M0) (XC_T_sound TOP (m_fs model) M0)
            (HS_T_sound TOP (m_fs model) M0)
            fuel bf None p cs s Hp CERT E fx R M model t_nil HC I eq_refl).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Theorem tgtEA_sound : forall TOP M0 E fx R M model, cs_okT TOP (m_fs model) M0 E tinEA fx R M model ->
  RZ (cfgF RSEGS fx R (pc tinEA) M model) (sd HOLES_T t_nil E (m_fs model) shapeA).
Proof. intros TOP M0 E fx R M model HC. exact (drv_cert_sound TOP M0 BF FUEL (planE CALLSA) tinEA shapeA E fx R M model (planE_ok _) certEA HC). Qed.
Theorem tgtNA_sound : forall TOP M0 E fx R M model, cs_okT TOP (m_fs model) M0 E tinNA fx R M model ->
  RZ (cfgF RSEGS fx R (pc tinNA) M model) (sd HOLES_T t_nil E (m_fs model) shapeA).
Proof. intros TOP M0 E fx R M model HC. exact (drv_cert_sound TOP M0 BF FUEL (planN CALLSA) tinNA shapeA E fx R M model (planN_ok _) certNA HC). Qed.
Theorem tgtEB_sound : forall TOP M0 E fx R M model, cs_okT TOP (m_fs model) M0 E tinEB fx R M model ->
  RZ (cfgF RSEGS fx R (pc tinEB) M model) (sd HOLES_T t_nil E (m_fs model) shapeB).
Proof. intros TOP M0 E fx R M model HC. exact (drv_cert_sound TOP M0 BF FUEL (planE CALLSB) tinEB shapeB E fx R M model (planE_ok _) certEB HC). Qed.
Theorem tgtNB_sound : forall TOP M0 E fx R M model, cs_okT TOP (m_fs model) M0 E tinNB fx R M model ->
  RZ (cfgF RSEGS fx R (pc tinNB) M model) (sd HOLES_T t_nil E (m_fs model) shapeB).
Proof. intros TOP M0 E fx R M model HC. exact (drv_cert_sound TOP M0 BF FUEL (planN CALLSB) tinNB shapeB E fx R M model (planN_ok _) certNB HC). Qed.
End TgtSound.

(* [comment removed for export] *)
Lemma Wp_zl : forall E n, Wp E 1 [SPLit (zl n)] = Spec4.W 1 (zero_lines n).
Proof.
  intros E n. unfold Wp, Spec4.W. f_equal. cbn [flat_map piece_den]. rewrite app_nil_r.
  induction n as [|n IH]; [reflexivity|]. cbn [zl zero_lines map]. rewrite IH. reflexivity.
Qed.

Lemma sd_s_calls : forall D E fs n, (1 <= n)%nat ->
  t_eq (sd HOLES_T D E fs (s_calls n)) (t_success n fs).
Proof.
  intros D E fs n Hn. unfold s_calls. cbn [sd].
  assert (W1 : Wp E 1 [SPLit [48]; SPLit [10]] = Spec4.W 1 (zero_lines 1)) by reflexivity.
  rewrite W1. destruct n as [|[|k]]; [lia| |].
  - unfold t_success, exit_code. apply Spec4.AgentLib.t_emit_congr. apply t_emit_nil_eq. apply t_exit_has_nil.
  - change (Datatypes.S (Datatypes.S k) - 1)%nat with (Datatypes.S k). rewrite Wp_zl. eapply t_eq_trans; [| apply t_eq_sym; apply t_success_S]. unfold exit_code. apply t_eq_refl.
Qed.

(* [comment removed for export] *)
Lemma sd_shapeL : forall D E fs e, 1 <= uE E e <= 4 ->
  t_eq (sd HOLES_T D E fs (shapeL e)) (t_success (Z.to_nat (uE E e)) fs).
Proof.
  intros D E fs e H. unfold uE in *.
  assert (Hs : sd HOLES_T D E fs (shapeL e) = sd HOLES_T D E fs (s_calls (Z.to_nat (bv_unsigned (edenot E e))))).
  { unfold shapeL, s_calls. cbn [sd].
    destruct (Z.leb_spec (bv_unsigned (edenot E e)) 1) as [H1|H1].
    { replace (Z.to_nat (bv_unsigned (edenot E e))) with 1%nat by lia. reflexivity. }
    destruct (Z.leb_spec (bv_unsigned (edenot E e)) 2) as [H2|H2].
    { replace (Z.to_nat (bv_unsigned (edenot E e))) with 2%nat by lia. reflexivity. }
    destruct (Z.leb_spec (bv_unsigned (edenot E e)) 3) as [H3|H3].
    { replace (Z.to_nat (bv_unsigned (edenot E e))) with 3%nat by lia. reflexivity. }
    replace (Z.to_nat (bv_unsigned (edenot E e))) with 4%nat by lia. reflexivity. }
  rewrite Hs. apply sd_s_calls. lia.
Qed.
Lemma sd_shapeA : forall D E fs, t_eq (sd HOLES_T D E fs shapeA) (t_success 1 fs).
Proof. intros. apply sd_s_calls. lia. Qed.
End UbDrvTSound.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhAInv OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhIface3 OSSVerify.Proofs.glaze.binary_reflection.lib.MhK OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module UbDrvTInst.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape.ShapeRel OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape.ShapeRetry OSSVerify.Proofs.glaze.binary_reflection.lib.Spec4.AgentLib OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymStepR OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3 OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3B OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3Sound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound.GxSymRun3 OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlanCore OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlan OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound.GxPlanSound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzIface OSSVerify.Proofs.glaze.binary_reflection.lib.GlzSpecsStr.GlzContracts OSSVerify.Proofs.glaze.binary_reflection.lib.GlzCall.GlzFrame OSSVerify.Proofs.glaze.binary_reflection.lib.GlzCall OSSVerify.Proofs.glaze.binary_reflection.lib.B2JCutShare.GlzCallCert OSSVerify.Proofs.glaze.binary_reflection.lib.GlzSpecsStr.GlzNodesSound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhDefs.UbImg OSSVerify.Proofs.glaze.binary_reflection.lib.GlzImageUbsan OSSVerify.Proofs.glaze.binary_reflection.lib.UbDrvHooks.GuFuzzT OSSVerify.Proofs.glaze.binary_reflection.lib.Spec4 OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.MallocDefs OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhDefs OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhAInv OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhIface3.UbMhSpec3 OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhIface3 OSSVerify.Proofs.glaze.binary_reflection.lib.MhK OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3.MhKInst OSSVerify.Proofs.glaze.binary_reflection.lib.UbDrvHooks.UbDrvIT OSSVerify.Proofs.glaze.binary_reflection.lib.GlzSpecsStr.UbDrvNodes OSSVerify.Proofs.glaze.binary_reflection.lib.UbDrvNodesSound OSSVerify.Proofs.glaze.binary_reflection.lib.UbDrvHooks OSSVerify.Proofs.glaze.binary_reflection.lib.UbDrvS3Plan UbDrvTPlan UbDrvTSound.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AX2S. Import AP. Import APS. Import GPS.
Open Scope Z_scope.

#[local] Notation RSEGS := USEGS.

(* [comment removed for export] *)
Lemma swin_ok_T {RC : run_ceil} : swin_ok SWIN_T.
Proof.
  intros lo hi a Hin Ha. unfold SWIN_T, PERM_Tc, RSTAGE_W, DN.FILE1, DN.FILE2 in Hin. cbn in Hin.
  unfold mh_static, UbMhRotate.UbMhRepT.statb, A_NEED_LOCKS, A_PAGESIZE, MLOCK, A_CANARY, A_GOT_CANARY, A_ERRNO, TPV, A_TAB_CTZ, A_TAB_SC, A_TAB_MED, CTX_END, CTX.
  destruct Hin as [H|[H|[H|[H|[H|[H|[H|[H|[]]]]]]]]]; injection H as <- <-; split; lia.
Qed.

(* [comment removed for export] *)
Lemma SR_det_of_exact : forall (SR : shape_rel RSEGS), sr_exactness RSEGS SR ->
  forall c T T', sr_rel RSEGS SR c T -> realizes RSEGS c T' -> t_eq T T'.
Proof.
  intros SR SRX c T T' H1 H2 tr.
  pose proof (SRX c T H1 tr) as X1. pose proof (exact_realizes RSEGS c T' H2 tr) as X2. tauto.
Qed.

Section Inst.
Context {RC : run_ceil}.
Variable SR : shape_rel RSEGS.
Hypothesis SRX : sr_exactness RSEGS SR.
#[local] Notation RZ := (sr_rel RSEGS SR).

(* [comment removed for export] *)
Lemma AINV_frame_T : forall L B C M M' mdl,
  AINV L B C M mdl ->
  (forall a, M' a <> M a -> (in_blocks L (bv_unsigned a) \/ CEIL_run <= bv_unsigned a \/ in_wins SWIN_T (bv_unsigned a)) /\ M' a <> None) ->
  AINV L B C M' mdl.
Proof. intros L B C M M' mdl HA H. exact (AINV_frame SWIN_T L B C M M' mdl swin_ok_T HA H). Qed.

Lemma AINV_zone_T : forall L B C M mdl b m, AINV L B C M mdl -> In (b, m) L -> GlzSpecsStr.GlzContracts.blk_ok GUBSAN b m.
Proof.
  intros L B C M mdl b m HA Hin. destruct (AINV_zone L B C M mdl b m HA Hin) as (Z1 & Z2 & Z3).
  unfold GlzSpecsStr.GlzContracts.blk_ok. cbn [g_img_lo g_img_hi GUBSAN]. unfold HEAPLO in Z1. unfold PTRLO. lia.
Qed.

#[local] Notation AINVc TOP M0 := (AINV_f SWIN_T GUBSAN AINV PERM_Tc TOP [] M0 0 0).
#[local] Notation cs_okT TOP FS0 M0 := (GPS.cs_ok RSEGS PERM_Tc TOP FS0 fds_std (AINVc TOP M0) fx_ok UTRUE).

(* [comment removed for export] *)
Hypothesis GC_T : forall TOP FS0 M0, gcontracts RSEGS ITD AUBSAN NXD PERM_Tc TOP FS0 fds_std (AINVc TOP M0) fx_ok UTRUE RZ GUBSAN BCAP CCAP.
(* [comment removed for export] *)
Hypothesis FZN_sound : callee_contract RSEGS SWIN_T GUBSAN fx_ok RZ AINV FuzzN.ce.
Hypothesis FZE_sound : callee_contract RSEGS SWIN_T GUBSAN fx_ok RZ AINV FuzzE.ce.

Theorem tgtEA_sound_P : forall TOP M0 E fx R M model,
  cs_okT TOP (m_fs model) M0 E tinEA fx R M model ->
  RZ (cfgF RSEGS fx R (pc tinEA) M model) (sd HOLES_T t_nil E (m_fs model) shapeA).
Proof. exact (tgtEA_sound SR (SR_det_of_exact SR SRX) AINV AINV_frame_T AINV_zone_T AINV_disj AINV_perm GC_T FZN_sound FZE_sound). Qed.
Theorem tgtNA_sound_P : forall TOP M0 E fx R M model,
  cs_okT TOP (m_fs model) M0 E tinNA fx R M model ->
  RZ (cfgF RSEGS fx R (pc tinNA) M model) (sd HOLES_T t_nil E (m_fs model) shapeA).
Proof. exact (tgtNA_sound SR (SR_det_of_exact SR SRX) AINV AINV_frame_T AINV_zone_T AINV_disj AINV_perm GC_T FZN_sound FZE_sound). Qed.
Theorem tgtEB_sound_P : forall TOP M0 E fx R M model,
  cs_okT TOP (m_fs model) M0 E tinEB fx R M model ->
  RZ (cfgF RSEGS fx R (pc tinEB) M model) (sd HOLES_T t_nil E (m_fs model) shapeB).
Proof. exact (tgtEB_sound SR (SR_det_of_exact SR SRX) AINV AINV_frame_T AINV_zone_T AINV_disj AINV_perm GC_T FZN_sound FZE_sound). Qed.
Theorem tgtNB_sound_P : forall TOP M0 E fx R M model,
  cs_okT TOP (m_fs model) M0 E tinNB fx R M model ->
  RZ (cfgF RSEGS fx R (pc tinNB) M model) (sd HOLES_T t_nil E (m_fs model) shapeB).
Proof. exact (tgtNB_sound SR (SR_det_of_exact SR SRX) AINV AINV_frame_T AINV_zone_T AINV_disj AINV_perm GC_T FZN_sound FZE_sound). Qed.
End Inst.
End UbDrvTInst.
Module UbDrvTGlue.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape.ShapeRel OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape.ShapeRetry OSSVerify.Proofs.glaze.binary_reflection.lib.Spec4.AgentLib OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymStepR OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3 OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3B OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3Sound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound.GxSymRun3 OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlanCore OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlan OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound.GxPlanSound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzIface OSSVerify.Proofs.glaze.binary_reflection.lib.GlzSpecsStr.GlzContracts OSSVerify.Proofs.glaze.binary_reflection.lib.GlzCall.GlzFrame OSSVerify.Proofs.glaze.binary_reflection.lib.GlzCall OSSVerify.Proofs.glaze.binary_reflection.lib.B2JCutShare.GlzCallCert OSSVerify.Proofs.glaze.binary_reflection.lib.GlzSpecsStr.GlzNodesSound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzCall.GlzNodesAlloc OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhDefs.UbImg OSSVerify.Proofs.glaze.binary_reflection.lib.GlzImageUbsan OSSVerify.Proofs.glaze.binary_reflection.lib.UbDrvHooks.GuFuzzT OSSVerify.Proofs.glaze.binary_reflection.lib.Spec4 OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.MallocDefs OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhDefs OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhAInv OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhIface3.UbMhSpec3 OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhIface3 OSSVerify.Proofs.glaze.binary_reflection.lib.MhK OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3.MhKInst OSSVerify.Proofs.glaze.binary_reflection.lib.UbDrvHooks.UbDrvIT OSSVerify.Proofs.glaze.binary_reflection.lib.GlzSpecsStr.UbDrvNodes OSSVerify.Proofs.glaze.binary_reflection.lib.UbDrvNodesSound OSSVerify.Proofs.glaze.binary_reflection.lib.UbDrvHooks OSSVerify.Proofs.glaze.binary_reflection.lib.UbDrvS3Plan UbDrvTPlan UbDrvTSound UbDrvTInst.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AX2S. Import AP. Import APS. Import GPS.
Open Scope Z_scope.

#[local] Notation RSEGS := USEGS.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
Ltac in_list_solve := cbn; repeat (first [left; reflexivity | right]).
Lemma kn_fact : forall {RC : run_ceil} PERMc TOP FS0 FDS0 AINV FXOK UINV E cs fx R M model K,
  GPS.cs_ok RSEGS PERMc TOP FS0 FDS0 AINV FXOK UINV E cs fx R M model -> In K (kn cs) -> kentry_ok RSEGS E M K.
Proof. intros. eapply (proj1 (Forall_forall _ _)); [exact (co_know H) | exact H0]. Qed.

Section GlueT.
Context {RC : run_ceil}.
Variable SR : shape_rel RSEGS.
Hypothesis SRX : sr_exactness RSEGS SR.
#[local] Notation RZ := (sr_rel RSEGS SR).

(* [comment removed for export] *)
Hypothesis HMA : forall fx : FPState, @MALLOC_ALT_F fx RC MSTK_M.

#[local] Notation AINVcT TOP M0 := (AINV_f SWIN_T GUBSAN AINV PERM_Tc TOP [] M0 0 0).
#[local] Notation AINVcS TOP M0 := (AINV_f SWIN_T GUBSAN AINV_R PERM_Tc TOP [] M0 0 0).
#[local] Notation cs_okT TOP FS0 M0 := (GPS.cs_ok RSEGS PERM_Tc TOP FS0 fds_std (AINVcT TOP M0) fx_ok UTRUE).
#[local] Notation cs_okS TOP FS0 M0 := (GPS.cs_ok RSEGS PERM_Tc TOP FS0 fds_std (AINVcS TOP M0) fx_ok UTRUE).

(* [comment removed for export] *)
Hypothesis GC_T : forall TOP FS0 M0, gcontracts RSEGS ITD AUBSAN NXD PERM_Tc TOP FS0 fds_std (AINVcT TOP M0) fx_ok UTRUE RZ GUBSAN BCAP CCAP.
Hypothesis FZN_sound : callee_contract RSEGS SWIN_T GUBSAN fx_ok RZ AINV FuzzN.ce.
Hypothesis FZE_sound : callee_contract RSEGS SWIN_T GUBSAN fx_ok RZ AINV FuzzE.ce.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma getr_z5 : forall (R : bvmap 5 word) (r : bv 5), getr R (Z_to_bv 5 (bv_unsigned r)) = getr R r.
Proof. intros R r. rewrite Z_to_bv_bv_unsigned. reflexivity. Qed.

Lemma drv_malloc_mspec1_F : forall bc cc, bc <= GBUDGET -> cc <= GCOUNT ->
  malloc_mspec1 RSEGS AINV fx_ok RZ GUBSAN (fun Lc B C M mdl _ => AINVF Lc B C M mdl) MSTK_M bc cc P_MALLOC_T.
Proof.
  intros bc cc Hbc Hcc.
  unfold malloc_mspec1. intros fx R M mdl Lc B C ret n sp Tok PRE FRESH HTok KOK.
  destruct PRE as (Hh & Hl & Hm & HFX & HA & Hra & Hret & Hev & Hn & Hnr & Hsp & Hal & Hceil & Htp & Hstk & HB & HC).
  cbn [g_tp GUBSAN] in Htp.
  assert (HPRE : malloc_pre MSTK_M R M mdl B C ret n sp).
  { unfold malloc_pre. unfold NMAX in Hnr. unfold MH_NMAX. unfold mcost, GlzIface.MBLK, GBUDGET in HB, Hbc. unfold MH_GBUDGET, UbMhDefs.MBLK.
    unfold MCNT, GCOUNT, GlzIface.LMAX in HC, Hcc. unfold UbMhDefs.LMAX. unfold TPV.
    split; [exact Hh|]. split; [exact Hl|]. split; [exact Hm|].
    split; [rewrite <- (getr_z5 R 1); exact Hra|]. split; [exact Hret|]. split; [exact Hev|].
    split; [rewrite <- (getr_z5 R 10); exact Hn|]. split; [lia|].
    split; [rewrite <- (getr_z5 R 2); exact Hsp|]. split; [exact Hal|]. split; [exact Hceil|].
    split; [rewrite <- (getr_z5 R 4); exact Htp|]. split; [exact Hstk|]. lia. }
  pose proof (kats_ok_exact RSEGS SR SRX (malloc_cfg R M mdl) _ _ Tok (HMA fx R M mdl Lc B C ret n sp FRESH HPRE)) as K.
  unfold malloc_cfg, A_MALLOC in K. unfold P_MALLOC_T, mkstF. apply K; clear K.
  - intros c' Hok.
    destruct Hok as (R' & M' & mdl' & p & -> & RK & H10 & Hp16 & Hblk & Hdisj & Hdef & CH & ST & HA' & Hh' & Hl' & Hm' & Hfs' & Hfd').
    apply (KOK fx R' M' mdl' p). unfold alloc_post_ok.
    split; [exact HFX|]. split; [exact RK|]. split; [rewrite <- (getr_z5 R' 10); exact H10|]. split; [exact Hp16|].
    split. { destruct Hblk as (Z1 & Z2 & Z3). unfold GlzSpecsStr.GlzContracts.blk_ok. cbn [g_img_lo g_img_hi GUBSAN]. unfold HEAPLO in Z1. unfold PTRLO. lia. }
    split; [exact Hdisj|]. split; [exact Hdef|].
    split. { intros a Ha. pose proof (CH a Ha) as X. unfold mh_changed in X. unfold alloc_changed. cbn [g_img_lo g_img_hi g_priv GUBSAN].
             unfold HEAPLO, CTX_END, CTX, A_ERRNO, TPV in X. pose proof (u64_range a).
             destruct X as [(X1 & X2 & X3)|[X|[X|X]]];
               [ left; split; [lia|]; split; [lia|]; unfold GPS.in_blocks; unfold UbMhAInv.in_blocks in X3; exact X3
               | right; left; lia
               | right; right; exists 0xaae90, 0xab240; split; [cbn; right; right; left; reflexivity | lia]
               | right; right; exists 0x8aaec, 0xaabd4; split; [cbn; right; left; reflexivity | lia] ]. }
    split; [exact ST|]. split; [| repeat split; assumption].
    unfold mcost, MCNT, GlzIface.MBLK. unfold UbMhDefs.MBLK in HA'. exact HA'.
Qed.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma AINV_f_S_T : forall TOP M0 Lc B C M mdl, AINVcS TOP M0 Lc B C M mdl -> AINVcT TOP M0 Lc B C M mdl.
Proof.
  intros TOP M0 Lc B C M mdl (HA & HP & HT & HZ & HD). split; [exact (AINV_R_AINV _ _ _ _ _ HA)|].
  split; [exact HP|]. split; [exact HT|]. split; [exact HZ | exact HD].
Qed.

Lemma cs_ok_S_T : forall TOP FS0 M0 E cs fx R M model,
  cs_okS TOP FS0 M0 E cs fx R M model -> cs_okT TOP FS0 M0 E cs fx R M model.
Proof.
  intros TOP FS0 M0 E cs fx R M model HC.
  destruct HC as [CR CL CK CH CZ CF CD CA CU CX CP CT CM CFL]; constructor; try assumption.
  apply AINV_f_S_T. exact CA.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section GlueE.
Variables (hE : acs) (sh : shape) (calls : env -> nat).
Hypothesis hE_sound : forall TOP M0 E fx R M model, cs_okT TOP (m_fs model) M0 E hE fx R M model ->
  RZ (cfgF RSEGS fx R (pc hE) M model) (sd HOLES_T t_nil E (m_fs model) sh).
Hypothesis sh_den : forall E fx R M model TOP M0, cs_okT TOP (m_fs model) M0 E hE fx R M model ->
  t_eq (sd HOLES_T t_nil E (m_fs model) sh) (t_success (calls E) (m_fs model)).
Theorem glue_E_gen : forall TOP M0 E fx R M model,
  cs_okS TOP (m_fs model) M0 E hE fx R M model ->
  RZ (cfgF RSEGS fx R (pc hE) M model) (t_success (calls E) (m_fs model)).
Proof.
  intros TOP M0 E fx R M model HCS. pose proof (cs_ok_S_T _ _ _ _ _ _ _ _ _ HCS) as HCT.
  eapply (sr_conseq RSEGS SR); [exact (hE_sound TOP M0 E fx R M model HCT) | exact (sh_den E fx R M model TOP M0 HCT)].
Qed.
End GlueE.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section GluePay.
Variables (hP hN : acs) (shN : shape) (calls : env -> nat).
Hypothesis hP_pc : pc hP = P_MALLOC_T.
Hypothesis hP_call_ok : call_ok NXD GUBSAN P_MALLOC_T hP = Some P_TR_AFTERM.
Hypothesis hP_alloc : node_alloc NXD GUBSAN BCAP CCAP P_MALLOC_T hP = Some hN.
Hypothesis hP_pay : In (KRange PAYX 1 (2 ^ 26)) (kn hP).
Hypothesis calls_agree : forall E E', env_agree NXD E E' -> calls E' = calls E.
Hypothesis hN_sound : forall TOP M0 E fx R M model, cs_okT TOP (m_fs model) M0 E hN fx R M model ->
  RZ (cfgF RSEGS fx R (pc hN) M model) (sd HOLES_T t_nil E (m_fs model) shN).
Hypothesis shN_den : forall TOP M0 E fx R M model, cs_okT TOP (m_fs model) M0 E hN fx R M model ->
  t_eq (sd HOLES_T t_nil E (m_fs model) shN) (t_success (calls E) (m_fs model)).

Theorem glue_pay_gen : forall TOP M0 E fx R M model,
  cs_okS TOP (m_fs model) M0 E hP fx R M model ->
  RZ (cfgF RSEGS fx R (pc hP) M model)
     (t_payload (Z.ltb M63 (uE E B1S)) (uE E PAYX) (calls E) (m_fs model)).
Proof.
  intros TOP M0 E fx R M model HCS.
  pose proof (cs_ok_S_T _ _ _ _ _ _ _ _ _ HCS) as HCT.
  pose proof (kn_fact _ _ _ _ _ _ _ E hP fx R M model (KRange PAYX 1 (2 ^ 26)) HCT hP_pay) as HRp. cbn [kentry_ok] in HRp.
  (* [comment removed for export] *)
  destruct (node_alloc_pre_sound RSEGS NXD PERM_Tc TOP (m_fs model) fds_std (AINVcT TOP M0) fx_ok UTRUE GUBSAN BCAP CCAP P_MALLOC_T hP hN P_TR_AFTERM
              E fx R M model HCT hP_call_ok hP_alloc) as [Hpc NPRE].
  pose proof NPRE as (Hh & Hlz & Hmat & HFX & HAF & R1 & Rr & Re & Hn & Hnr & Hsp & Hal & Hspc & Hsptop & R4 & Hstk & HB & HC).
  assert (STK : 0 <= MSTK_M <= GlzIface.MSTK) by (unfold MSTK_M, GlzIface.MSTK; lia).
  pose proof (alloc_pre_of RSEGS SWIN_T GUBSAN fx_ok AINV PERM_Tc TOP [] M0 0 0 MSTK_M STK BCAP CCAP ltac:(unfold BCAP; lia) ltac:(unfold CCAP; lia)
                fx R M model _ _ _ _ _ _ NPRE) as PRE.
  assert (FRESH : AINVF (blocks_den E (a_vis hP) ++ []) (0 + GPS.bcost E (a_vis hP)) (0 + GPS.bcount (a_vis hP)) M model).
  { destruct (co_ainv HCS) as (HA & _). exact (AINV_R_AINVF _ _ _ _ _ HA). }
  rewrite hP_pc. unfold cfgF.
  unfold t_payload.
  apply (drv_malloc_mspec1_F BCAP CCAP ltac:(unfold BCAP; lia) ltac:(unfold CCAP; lia) fx R M model _ _ _ P_TR_AFTERM _ _
           (t_success (calls E) (m_fs model)) PRE FRESH (t_success_has_nil _ _)).
  - (* [comment removed for export] *)
    intros fx' R' M' mdl' p POST.
    pose proof (nalloc_post_ok_of RSEGS SWIN_T GUBSAN fx_ok AINV AINV_zone_T AINV_disj drv_G_ro_img drv_G_img_ceil drv_G_priv SWIN_T_img drv_SEGS_out
                  PERM_Tc TOP [] M0 0 0 MSTK_M STK fx R M model _ _ _ _ _ fx' R' M' mdl' p HAF Hspc Hsptop (proj1 Hnr) Hstk POST) as NPOST.
    destruct (node_alloc_ok_sound RSEGS NXD SWIN_T PERM_Tc TOP (m_fs model) fds_std (AINVcT TOP M0) fx_ok UTRUE UTRUE_agree GUBSAN BCAP CCAP P_MALLOC_T
                hP hN P_TR_AFTERM E fx R M model fx' R' M' mdl' p ltac:(cbn; lia) ltac:(cbn; lia) HCT hP_call_ok hP_alloc NPOST)
      as (E' & [Hag0 Hag] & HC' & Hpc').
    destruct POST as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hfs' & _).
    assert (HC'' : cs_okT TOP (m_fs mdl') M0 E' hN fx' R' M' mdl') by (rewrite Hfs'; exact HC').
    pose proof (hN_sound TOP M0 E' fx' R' M' mdl' HC'') as HT. pose proof (shN_den TOP M0 E' fx' R' M' mdl' HC'') as HD.
    rewrite Hpc', Hfs' in HT. rewrite Hfs' in HD. unfold cfgF in HT.
    eapply (sr_conseq RSEGS SR); [exact HT|]. rewrite <- (calls_agree E E' Hag0). exact HD.
Qed.
End GluePay.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition callsA (E : env) : nat := 1%nat.
Definition callsB (E : env) : nat := Z.to_nat (uE E CALLSB).

Lemma shapeA_den : forall E fx R M model TOP M0 (cs : acs), cs_okT TOP (m_fs model) M0 E cs fx R M model ->
  t_eq (sd HOLES_T t_nil E (m_fs model) shapeA) (t_success (callsA E) (m_fs model)).
Proof. intros. apply sd_shapeA. Qed.
Lemma shapeB_den : forall (cs : acs), In (KRange CALLSB 1 4) (kn cs) ->
  forall E fx R M model TOP M0, cs_okT TOP (m_fs model) M0 E cs fx R M model ->
  t_eq (sd HOLES_T t_nil E (m_fs model) shapeB) (t_success (callsB E) (m_fs model)).
Proof.
  intros cs Hin E fx R M model TOP M0 HC. apply sd_shapeL.
  pose proof (kn_fact _ _ _ _ _ _ _ E cs fx R M model (KRange CALLSB 1 4) HC Hin) as HR. cbn [kentry_ok] in HR. unfold uE. exact HR.
Qed.
Lemma callsB_agree : forall E E', env_agree NXD E E' -> callsB E' = callsB E.
Proof. intros E E' Hag. unfold callsB, uE. f_equal. f_equal. symmetry. eapply (edenot_agree' NXD); [exact Hag | reflexivity]. Qed.

Theorem glue_EA : forall TOP M0 E fx R M model, cs_okS TOP (m_fs model) M0 E tinEA fx R M model ->
  RZ (cfgF RSEGS fx R (pc tinEA) M model) (t_success 1 (m_fs model)).
Proof.
  intros TOP M0 E fx R M model HCS.
  exact (glue_E_gen tinEA shapeA callsA (tgtEA_sound_P SR SRX GC_T FZN_sound FZE_sound) (fun E fx R M model TOP M0 HC => shapeA_den E fx R M model TOP M0 tinEA HC)
           TOP M0 E fx R M model HCS).
Qed.
Theorem glue_EB : forall TOP M0 E fx R M model, cs_okS TOP (m_fs model) M0 E tinEB fx R M model ->
  RZ (cfgF RSEGS fx R (pc tinEB) M model) (t_success (callsB E) (m_fs model)).
Proof.
  intros TOP M0 E fx R M model HCS.
  exact (glue_E_gen tinEB shapeB callsB (tgtEB_sound_P SR SRX GC_T FZN_sound FZE_sound) (shapeB_den tinEB ltac:(vm_compute; in_list_solve))
           TOP M0 E fx R M model HCS).
Qed.
Theorem glue_payA : forall TOP M0 E fx R M model, cs_okS TOP (m_fs model) M0 E tinPA fx R M model ->
  RZ (cfgF RSEGS fx R (pc tinPA) M model) (t_payload (Z.ltb M63 (uE E B1S)) (uE E PAYX) 1 (m_fs model)).
Proof.
  intros TOP M0 E fx R M model HCS.
  exact (glue_pay_gen tinPA tinNA shapeA callsA tinPA_pc tinPA_call_ok tinPA_alloc ltac:(vm_compute; in_list_solve)
           (fun _ _ _ => eq_refl) (tgtNA_sound_P SR SRX GC_T FZN_sound FZE_sound)
           (fun TOP M0 E fx R M model HC => shapeA_den E fx R M model TOP M0 tinNA HC) TOP M0 E fx R M model HCS).
Qed.
Theorem glue_payB : forall TOP M0 E fx R M model, cs_okS TOP (m_fs model) M0 E tinPB fx R M model ->
  RZ (cfgF RSEGS fx R (pc tinPB) M model) (t_payload (Z.ltb M63 (uE E B1S)) (uE E PAYX) (callsB E) (m_fs model)).
Proof.
  intros TOP M0 E fx R M model HCS.
  exact (glue_pay_gen tinPB tinNB shapeB callsB tinPB_pc tinPB_call_ok tinPB_alloc ltac:(vm_compute; in_list_solve)
           callsB_agree (tgtNB_sound_P SR SRX GC_T FZN_sound FZE_sound)
           (fun TOP M0 E fx R M model HC => shapeB_den tinNB ltac:(vm_compute; in_list_solve) E fx R M model TOP M0 HC) TOP M0 E fx R M model HCS).
Qed.
End GlueT.
End UbDrvTGlue.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape OSSVerify.Proofs.glaze.binary_reflection.lib.Spec4 OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymStepR OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3 OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3B OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3Sound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlanCore OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlan OSSVerify.Proofs.glaze.binary_reflection.lib.GlzIface OSSVerify.Proofs.glaze.binary_reflection.lib.GlzSpecsStr OSSVerify.Proofs.glaze.binary_reflection.lib.GlzCall OSSVerify.Proofs.glaze.binary_reflection.lib.B2JCutShare OSSVerify.Proofs.glaze.binary_reflection.lib.GlzNodesLibcUbsan OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhDefs OSSVerify.Proofs.glaze.binary_reflection.lib.GlzImageUbsan OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhAInv OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhIface3 OSSVerify.Proofs.glaze.binary_reflection.lib.MhK OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3 OSSVerify.Proofs.glaze.binary_reflection.lib.UbDrvHooks OSSVerify.Proofs.glaze.binary_reflection.lib.UbDrvNodesSound OSSVerify.Proofs.glaze.binary_reflection.lib.UbDrvS3Plan. Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape.ShapeRel OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape.ShapeRetry OSSVerify.Proofs.glaze.binary_reflection.lib.Spec4.AgentLib OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymStepR OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3 OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3B OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3Sound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound.GxSymRun3 OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlanCore OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlan OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound.GxPlanSound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzIface OSSVerify.Proofs.glaze.binary_reflection.lib.GlzSpecsStr.GlzContracts OSSVerify.Proofs.glaze.binary_reflection.lib.GlzCall.GlzFrame OSSVerify.Proofs.glaze.binary_reflection.lib.GlzCall OSSVerify.Proofs.glaze.binary_reflection.lib.B2JCutShare.GlzCallCert OSSVerify.Proofs.glaze.binary_reflection.lib.GlzSpecsStr.GlzNodesSound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzCall.GlzNodesAlloc OSSVerify.Proofs.glaze.binary_reflection.lib.GlzNodesLibcUbsan OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhDefs.UbImg OSSVerify.Proofs.glaze.binary_reflection.lib.GlzImageUbsan OSSVerify.Proofs.glaze.binary_reflection.lib.Spec4 OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.MallocDefs OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhDefs OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhAInv OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhIface3.UbMhSpec3 OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhIface3 OSSVerify.Proofs.glaze.binary_reflection.lib.MhK OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3.MhKInst OSSVerify.Proofs.glaze.binary_reflection.lib.UbDrvHooks.UbDrvIT OSSVerify.Proofs.glaze.binary_reflection.lib.GlzSpecsStr.UbDrvNodes OSSVerify.Proofs.glaze.binary_reflection.lib.UbDrvNodesSound OSSVerify.Proofs.glaze.binary_reflection.lib.UbDrvHooks OSSVerify.Proofs.glaze.binary_reflection.lib.UbDrvS3Plan.UbDrvHooksS UbDrvTSound UbDrvTInst.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AX2S. Import AP. Import APS. Import GPS.
Open Scope Z_scope.

#[local] Notation RSEGS := USEGS.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section AllocR.
Context {RC : run_ceil}.
Variable SR : shape_rel RSEGS.
Hypothesis SRX : sr_exactness RSEGS SR.
#[local] Notation RZ := (sr_rel RSEGS SR).

Lemma getr_z5' : forall (R : bvmap 5 word) (r : bv 5), getr R (Z_to_bv 5 (bv_unsigned r)) = getr R r.
Proof. intros R r. rewrite Z_to_bv_bv_unsigned. reflexivity. Qed.

(* [comment removed for export] *)
Lemma drv_malloc_mspec1_of_kats :
  forall (INV : list (Z * Z) -> Z -> Z -> (word -> option byte) -> Model -> Prop)
         (FRESH : list (Z * Z) -> Z -> Z -> (word -> option byte) -> Model -> Z -> Prop),
  (forall (fx : FPState) R M mdl Lc B C ret n sp,
      INV Lc B C M mdl -> FRESH Lc B C M mdl n -> malloc_pre MSTK_M R M mdl B C ret n sp ->
      kats RSEGS (malloc_cfg R M mdl) (malloc_ok INV MSTK_M R M mdl Lc B C ret n sp) (malloc_null INV MSTK_M R M mdl Lc B C ret sp)) ->
  forall bc cc, bc <= GBUDGET -> cc <= GCOUNT ->
  malloc_mspec1 RSEGS INV fx_ok RZ GUBSAN FRESH MSTK_M bc cc P_MALLOC_T.
Proof.
  intros INV FRESH HK bc cc Hbc Hcc.
  unfold malloc_mspec1. intros fx R M mdl Lc B C ret n sp Tok PRE HFR HTok KOK.
  destruct PRE as (Hh & Hl & Hm & HFX & HA & Hra & Hret & Hev & Hn & Hnr & Hsp & Hal & Hceil & Htp & Hstk & HB & HC).
  cbn [g_tp GUBSAN] in Htp.
  assert (HPRE : malloc_pre MSTK_M R M mdl B C ret n sp).
  { unfold malloc_pre. unfold NMAX in Hnr. unfold MH_NMAX. unfold mcost, GlzIface.MBLK, GBUDGET in HB, Hbc. unfold MH_GBUDGET, UbMhDefs.MBLK.
    unfold MCNT, GCOUNT, GlzIface.LMAX in HC, Hcc. unfold UbMhDefs.LMAX. unfold TPV.
    split; [exact Hh|]. split; [exact Hl|]. split; [exact Hm|].
    split; [rewrite <- (getr_z5' R 1); exact Hra|]. split; [exact Hret|]. split; [exact Hev|].
    split; [rewrite <- (getr_z5' R 10); exact Hn|]. split; [lia|].
    split; [rewrite <- (getr_z5' R 2); exact Hsp|]. split; [exact Hal|]. split; [exact Hceil|].
    split; [rewrite <- (getr_z5' R 4); exact Htp|]. split; [exact Hstk|]. lia. }
  pose proof (kats_ok_exact RSEGS SR SRX (malloc_cfg R M mdl) _ _ Tok (HK fx R M mdl Lc B C ret n sp HA HFR HPRE)) as K.
  unfold malloc_cfg, A_MALLOC in K. unfold P_MALLOC_T, mkstF. apply K; clear K.
  - intros c' Hok.
    destruct Hok as (R' & M' & mdl' & p & -> & RK & H10 & Hp16 & Hblk & Hdisj & Hdef & CH & ST & HA' & Hh' & Hl' & Hm' & Hfs' & Hfd').
    apply (KOK fx R' M' mdl' p). unfold alloc_post_ok.
    split; [exact HFX|]. split; [exact RK|]. split; [rewrite <- (getr_z5' R' 10); exact H10|]. split; [exact Hp16|].
    split. { destruct Hblk as (Z1 & Z2 & Z3). unfold GlzSpecsStr.GlzContracts.blk_ok. cbn [g_img_lo g_img_hi GUBSAN]. unfold HEAPLO in Z1. unfold PTRLO. lia. }
    split; [exact Hdisj|]. split; [exact Hdef|].
    split. { intros a Ha. pose proof (CH a Ha) as X. unfold mh_changed in X. unfold alloc_changed. cbn [g_img_lo g_img_hi g_priv GUBSAN].
             unfold HEAPLO, CTX_END, CTX, A_ERRNO, TPV in X. pose proof (u64_range a).
             destruct X as [(X1 & X2 & X3)|[X|[X|X]]];
               [ left; split; [lia|]; split; [lia|]; unfold GPS.in_blocks; unfold UbMhAInv.in_blocks in X3; exact X3
               | right; left; lia
               | right; right; exists 0xaae90, 0xab240; split; [cbn; right; right; left; reflexivity | lia]
               | right; right; exists 0x8aaec, 0xaabd4; split; [cbn; right; left; reflexivity | lia] ]. }
    split; [exact ST|]. split; [| repeat split; assumption].
    unfold mcost, MCNT, GlzIface.MBLK. unfold UbMhDefs.MBLK in HA'. exact HA'.
Qed.

Lemma same_csr' : GlzSpecsStr.GlzContracts.callee_saved_regs = UbMhIface3.UbMhSpec3.callee_saved_regs.
Proof. reflexivity. Qed.
(* [comment removed for export] *)
Lemma drv_free_mspecR_of_kat :
  forall (INV : list (Z * Z) -> Z -> Z -> (word -> option byte) -> Model -> Prop),
  (forall (fx : FPState) R M mdl Lc Lc' B C B' C' ret sp p,
      INV Lc B C M mdl -> free_pre MSTK_M R M mdl Lc Lc' B C B' C' ret sp p ->
      kat RSEGS (free_cfg R M mdl) (free_post INV MSTK_M R M mdl Lc' B' C' ret sp)) ->
  free_mspecR RSEGS INV fx_ok RZ GUBSAN MSTK_MALLOC P_FREE_T.
Proof.
  intros INV HF. unfold free_mspecR.
  intros fx R M mdl Lc Lc' B C B' C' ret sp p T Hh Hl Hm HFX HA Hra Hret Hev H10 Hcase Hsp Hal Hceil Htp Hstk HK.
  assert (HPRE : free_pre MSTK_M R M mdl Lc Lc' B C B' C' ret sp p).
  { unfold free_pre. unfold MSTK_M. unfold MSTK_MALLOC in Hceil, Hstk. unfold mcost, GlzIface.MBLK, MCNT in Hcase. unfold UbMhDefs.MBLK.
    cbn [g_tp GUBSAN] in Htp. unfold TPV.
    repeat match goal with |- _ /\ _ => split end; try assumption; lia. }
  pose proof (HF fx R M mdl Lc Lc' B C B' C' ret sp p HA HPRE) as KAT.
  unfold free_cfg, A_FREE in KAT. unfold P_FREE_T, mkstF. apply (kat_exact RSEGS SR SRX _ _ T KAT).
  intros c' (R' & M' & mdl' & -> & RK & CH & ST & HA' & Hh' & Hl' & Hm' & Hfs' & Hfd').
  apply (HK fx R' M' mdl' HFX).
  - rewrite same_csr'. exact RK.
  - intros a Ha. pose proof (CH a Ha) as X. unfold mh_changed in X. unfold alloc_changed.
    cbn [g_img_lo g_img_hi g_priv GUBSAN]. unfold MSTK_M in X. unfold MSTK_MALLOC.
    unfold UbMhAInv.in_blocks in X. unfold GPS.in_blocks, GPS.in_wins.
    unfold CTX_END, CTX, A_ERRNO, TPV in X.
    destruct X as [(X1 & X2 & X3)|[X|[X|X]]];
      [ left; split; [lia | split; [lia | exact X3]]
      | right; left; lia
      | right; right; exists 0xaae90, 0xab240; split; [cbv; tauto | lia]
      | right; right; exists 0x8aaec, 0xaabd4; split; [cbv; tauto | lia] ].
  - intros a Ha. apply ST. unfold MSTK_M. unfold MSTK_MALLOC in Ha. lia.
  - exact HA'.
  - exact Hh'. - exact Hl'. - exact Hm'. - exact Hfs'. - exact Hfd'.
Qed.
End AllocR.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section SSound.
Context {RC : run_ceil}.
Variable SR : shape_rel RSEGS.
Hypothesis SRX : sr_exactness RSEGS SR.
#[local] Notation RZ := (sr_rel RSEGS SR).

(* [comment removed for export] *)
Hypothesis HFR : forall fx : FPState, @FREE_R fx RC MSTK_M.
Hypothesis HMB : forall fx : FPState, @MALLOC_BIG_R fx RC MSTK_M.

(* [comment removed for export] *)
Lemma AINV_R_frame_T : forall L B C M M' mdl,
  AINV_R L B C M mdl ->
  (forall a, M' a <> M a -> (in_blocks L (bv_unsigned a) \/ CEIL_run <= bv_unsigned a \/ in_wins SWIN_T (bv_unsigned a)) /\ M' a <> None) ->
  AINV_R L B C M' mdl.
Proof. intros L B C M M' mdl HA H. exact (AINV_R_frame SWIN_T L B C M M' mdl swin_ok_T HA H). Qed.
Lemma AINV_R_zone_T : forall L B C M mdl b m, AINV_R L B C M mdl -> In (b, m) L -> GlzSpecsStr.GlzContracts.blk_ok GUBSAN b m.
Proof. intros L B C M mdl b m HA Hin. exact (AINV_zone_T L B C M mdl b m (AINV_R_AINV _ _ _ _ _ HA) Hin). Qed.
Lemma AINV_R_disj_T : forall L B C M mdl L1 L2 b m b' m',
  AINV_R L B C M mdl -> L = L1 ++ (b, m) :: L2 -> In (b', m') (L1 ++ L2) -> b + m <= b' \/ b' + m' <= b.
Proof. intros L B C M mdl L1 L2 b m b' m' HA. exact (AINV_disj L B C M mdl L1 L2 b m b' m' (AINV_R_AINV _ _ _ _ _ HA)). Qed.

#[local] Notation AINVcS TOP M0 := (AINV_f SWIN_T GUBSAN AINV_R PERM_Tc TOP [] M0 0 0).
#[local] Notation cs_okS TOP FS0 FDS0 M0 UINV := (GPS.cs_ok RSEGS PERM_Tc TOP FS0 FDS0 (AINVcS TOP M0) fx_ok UINV).

Lemma AF_S : forall TOP M0 Lc B C M M' mdl,
  AINVcS TOP M0 Lc B C M mdl -> (forall a, M' a <> M a -> owned SWIN_T PERM_Tc TOP Lc a /\ M' a <> None) -> AINVcS TOP M0 Lc B C M' mdl.
Proof. intros TOP M0. exact (AINV_f_frame SWIN_T GUBSAN AINV_R AINV_R_frame_T AINV_R_zone_T AINV_R_disj_T drv_G_ro_img drv_G_img_ceil PERM_Tc TOP [] M0 0 0). Qed.

(* [comment removed for export] *)
Definition FRESH_BIG (Lc : list (Z * Z)) (B C : Z) (M : word -> option byte) (mdl : Model) (n : Z) : Prop := MMAP_THRESHOLD <= n.
Lemma drv_malloc_mspec1_R : forall bc cc, bc <= GBUDGET -> cc <= GCOUNT ->
  malloc_mspec1 RSEGS AINV_R fx_ok RZ GUBSAN FRESH_BIG MSTK_M bc cc P_MALLOC_T.
Proof.
  intros bc cc Hbc Hcc. apply (drv_malloc_mspec1_of_kats SR SRX AINV_R FRESH_BIG); [| exact Hbc | exact Hcc].
  intros fx R M mdl Lc B C ret n sp HA HFRESH HPRE. exact (HMB fx R M mdl Lc B C ret n sp HFRESH HA HPRE).
Qed.
Lemma drv_free_mspecR_R : free_mspecR RSEGS AINV_R fx_ok RZ GUBSAN MSTK_MALLOC P_FREE_T.
Proof. apply (drv_free_mspecR_of_kat SR SRX AINV_R). intros fx. exact (HFR fx). Qed.

Section Inst.
(* [comment removed for export] *)
Variables (TOP : Z) (FS0 : Fs.Fs) (FDS0 : list (word * FdEntry)) (M0 : word -> option byte).
Hypothesis FDS1 : fd_lookup FDS0 (Z_to_bv 64 1) = Some (FdChannel (Z_to_bv 64 1)).
Hypothesis FDS2 : fd_lookup FDS0 (Z_to_bv 64 2) = Some (FdChannel (Z_to_bv 64 2)).
(* [comment removed for export] *)
Variable UINV : env -> Prop.
Hypothesis UINV_agree : forall E E', env_agree NXD E E' -> UINV E -> UINV E'.

Lemma FRESH_BIG_chk : forall nmin, MMAP_THRESHOLD <= nmin -> forall cs E fx R M model,
  cs_okS TOP FS0 FDS0 M0 UINV E cs fx R M model -> fresh_chk [ELit nmin] cs = true ->
  (fun Lc B C M mdl n => FRESH_BIG (Lc ++ []) (0 + B) (0 + C) M mdl n)
    (blocks_den E (a_vis cs)) (GPS.bcost E (a_vis cs)) (GPS.bcount (a_vis cs)) M model (uE E (reg cs 10)).
Proof.
  intros nmin Hn cs E fx R M model HC Hf. unfold FRESH_BIG. cbn [fresh_chk] in Hf.
  destruct (xlo (kn cs) (reg cs 10)) as [l|] eqn:Hlo; [|discriminate Hf]. apply Z.leb_le in Hf.
  pose proof (xlo_sound RSEGS E M (kn cs) _ _ (co_know HC) Hlo) as Blo. unfold uE. lia.
Qed.

Lemma XNs_sound : GPS.ext_stmt RSEGS NXD XNs PERM_Tc TOP FS0 FDS0 (AINVcS TOP M0) fx_ok UINV RZ.
Proof.
  intros id args cs cs' E fx R M model T HT HC Hp Hn Hk. unfold XNs in Hn.
  pose proof (AF_S TOP M0) as AF.
  destruct id as [|id]; [discriminate Hn|].
  destruct id as [|id].
  { (* [comment removed for export] *)
    exact (ubsan_OBL_memcpy ADRV NXD SWIN_T PERM_Tc TOP FS0 FDS0 (AINVcS TOP M0) AF fx_ok UINV UINV_agree RZ (sr_msteps RSEGS SR) GUBSAN eq_refl
             cs cs' E fx R M model T HC Hp Hn Hk). }
  do 9 (destruct id as [|id]; [discriminate Hn|]).
  destruct id as [|id].
  { (* [comment removed for export] *)
    assert (STK : 0 <= MSTK_MALLOC <= GlzIface.MSTK) by (unfold MSTK_MALLOC, GlzIface.MSTK; lia).
    pose proof (free_nspec_of_mspec RSEGS SWIN_T GUBSAN fx_ok RZ AINV_R AINV_R_mono AINV_R_zone_T drv_G_ro_img drv_G_img_ceil drv_G_priv SWIN_T_img drv_SEGS_out
                  PERM_Tc TOP [] M0 0 0 ltac:(lia) ltac:(lia) MSTK_MALLOC STK P_FREE_T drv_free_mspecR_R) as FNS.
    exact (node_free_sound RSEGS NXD SWIN_T PERM_Tc TOP FS0 FDS0 (AINVcS TOP M0) fx_ok UINV UINV_agree RZ GUBSAN FNS FNS
             cs cs' E fx R M model T HC Hp Hn Hk). }
  destruct id as [|id]; [discriminate Hn|].
  destruct id as [|id].
  { (* [comment removed for export] *)
    destruct args as [|a args']; [discriminate Hn|].
    destruct a; try discriminate Hn.
    destruct args' as [|a' args'']; [| discriminate Hn].
    destruct (MMAP_TH <=? z) eqn:Hle; [| discriminate Hn].
    apply Z.leb_le in Hle. unfold MMAP_TH in Hle.
    assert (STK : 0 <= MSTK_M <= GlzIface.MSTK) by (unfold MSTK_M, GlzIface.MSTK; lia).
    pose proof (malloc_nspec1_of_mspec1 RSEGS SWIN_T GUBSAN fx_ok RZ AINV_R AINV_R_zone_T AINV_R_disj_T drv_G_ro_img drv_G_img_ceil drv_G_priv SWIN_T_img drv_SEGS_out
                  PERM_Tc TOP [] M0 0 0 MSTK_M STK BCAP CCAP ltac:(unfold BCAP; lia) ltac:(unfold CCAP; lia) FRESH_BIG P_MALLOC_T
                  (drv_malloc_mspec1_R BCAP CCAP ltac:(unfold BCAP; lia) ltac:(unfold CCAP; lia))) as MS.
    exact (node_malloc1_sound_gen RSEGS NXD SWIN_T PERM_Tc TOP FS0 FDS0 (AINVcS TOP M0) fx_ok UINV UINV_agree RZ GUBSAN BCAP CCAP _ [ELit z]
             ltac:(cbn; lia) ltac:(cbn; lia) (FRESH_BIG_chk z ltac:(unfold MMAP_THRESHOLD; lia)) MS MS
             cs cs' E fx R M model T HT HC Hp Hn Hk). }
  do 49 (destruct id as [|id]; [discriminate Hn|]).
  destruct id as [|id]; [| discriminate Hn].
  (* [comment removed for export] *)
  exact (node_ioctl_sound SR NXD SWIN_T PERM_Tc TOP FS0 FDS0 (AINVcS TOP M0) AF fx_ok UINV FDS1 FDS2 cs cs' E fx R M model T HT HC Hp Hn Hk).
Qed.

Lemma XEs_sound : GPS.emit_stmt RSEGS NXD XEs PERM_Tc TOP FS0 FDS0 (AINVcS TOP M0) fx_ok UINV RZ.
Proof.
  unfold XEs. pose proof (AF_S TOP M0) as AF.
  exact (XEd_sound SR NXD SWIN_T PERM_Tc TOP FS0 FDS0 (AINVcS TOP M0) AF fx_ok UINV UINV_agree (SR_det_of_exact SR SRX) SWIN_Tc FDS1 FDS2).
Qed.

Lemma XBs_sound : GPS.ext2_stmt RSEGS NXD XB0 PERM_Tc TOP FS0 FDS0 (AINVcS TOP M0) fx_ok UINV RZ.
Proof. intros id args cs csa csb E1 fx1 R1 M1 m1 T1 HC1 Hn. discriminate Hn. Qed.

Lemma XCs_sound : GPS.alt2x_stmt RSEGS NXD XCs PERM_Tc TOP FS0 FDS0 (AINVcS TOP M0) fx_ok UINV RZ.
Proof. intros id args cs csa csb E fx R M model Ta Tb _ Hn. unfold XCs in Hn. discriminate Hn. Qed.

(* [comment removed for export] *)
Theorem drvS_cert_sound : forall (HS : nat -> option acs) (HOLES : nat -> env -> Fs.Fs -> TSet),
  (forall h E E' fs, env_agree NXD E E' -> HOLES h E fs = HOLES h E' fs) ->
  (forall h E fs, HOLES h E fs []) ->
  (forall h E fs, HOLES h E fs = HOLES 0%nat E fs) ->
  GPS.holes_stmt RSEGS HS PERM_Tc TOP FS0 FDS0 (AINVcS TOP M0) fx_ok UINV HOLES RZ ->
  forall bf fuel p cs s E fx R M model,
  gplan_ok p = true -> CHKs HS bf fuel cs p = COk s ->
  cs_okS TOP FS0 FDS0 M0 UINV E cs fx R M model -> m_fs model = FS0 ->
  RZ (cfgF RSEGS fx R (pc cs) M model) (sd HOLES t_nil E FS0 s).
Proof.
  intros HS HOLES Hag Hnil Hsame HST bf fuel p cs s E fx R M model Hp CERT HC Hfs.
  pose proof (AF_S TOP M0) as AF. rewrite <- Hfs.
  refine (GPS.check_sound RSEGS ITD ITD_ok ADRV NXD LIMIT HS XNs XEs XB0 XCs 0%nat SWIN_T PERM_Tc TOP FS0 FDS0 (AINVcS TOP M0) AF
            fx_ok UINV UINV_agree HOLES Hag Hnil Hsame
            RZ (sr_step RSEGS SR) (sr_msteps RSEGS SR) (sr_exit RSEGS SR) (sr_conseq RSEGS SR) (RUN_sound_fx RSEGS) ubsan_in_hull ubsan_hull_ok
            XNs_sound XEs_sound XBs_sound XCs_sound HST
            fuel bf None p cs s Hp CERT E fx R M model t_nil HC I eq_refl).
Qed.
End Inst.
End SSound.
