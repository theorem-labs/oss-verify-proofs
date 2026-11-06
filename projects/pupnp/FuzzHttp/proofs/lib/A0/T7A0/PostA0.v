(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation Strings.String.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP Agree MonadX Ceiling.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Lib Require Import RunWord.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.A0.ZAW Require Import Segs Shadow Contracts Globals IcptA0 AllocA0.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Lib Require Import InitStack EntrySecret.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Spec Require Import Prelim STree Monad Stdio Driver Prog.
From OSSVerify.pupnp.FuzzHttp.images Require Import Asan.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.ASN Require Import AsanAcct.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Top Require Import AllocIF.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Spec Require Import MSafe.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Top Require Import Realize SafeReach Bridge TSim DriverSim StdioShape.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Top Require AssembleP0.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.LZ Require Import ITreeLZ BridgeLZ NodesLZ NodesLZSound.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.A0.T7 Require Import RealizeS RealizeS2 SeamA0 A0Prog AssembleA0 DriverModelA.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.A0.T7A0 Require Import ShadowKit GlobalsShadow Stdio_base Printf_lib F_printf_iface Stdio_iface F_printf_diag Exit RDriverA_kit RDriverA_ctx RDriverA_main RDriverA_exit RF_mainA_A.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.A0.T7A0 Require Import F_syscalls RDriverA_lib RDriverA_iface RF_mainA_B1 RF_mainA_B2 RF_mainA_B3 RF_mainA_B4 RF_mainA_C RF_mainA_T RF_mainA_post RDriverA_seams RDriverA_parser RF_mainA.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope mspec_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Ltac rpc := apply ret_pc_even; [lia| reflexivity].

Local Notation tsh := (tshape node nstep nexit) (only parsing).
Local Notation implS := (RealizeS.implS asegs gst VA INVA ATNA GOODA).
Local Notation SEAM := (RealizeS.SEAM asegs gst VA INVA).

Lemma tshape_exit_msysA : forall st (s : ASt) mo (K : exc (Empty_set * ASt) -> Model -> TSet),
  t_eq (tsh (msys (NExit st) dec_exit s) mo K) (t_exit (exit_code st) (m_fs mo)).
Proof.
  intros st s mo K. unfold msys, enode. cbn [tshape].
  intro tr. unfold t_alt, t_exit. split.
  - intros [[[[[rsp mo'] evs] Hst] | [[code mo'] Hex]] H]; cbn in *.
    + exfalso. first [exact Hst | exact (nstep_exit_none _ _ _ _ _ Hst)].
    + destruct Hex as [-> ->]. rewrite m_fs_with_halted in H. exact H.
  - intros H. unshelve eexists (inr (exist _ (exit_code st, with_halted (exit_code st) mo) _)).
    { cbn. split; reflexivity. }
    cbn. rewrite m_fs_with_halted. exact H.
Qed.

Lemma tshape_exit_kA : forall {A} st (s : ASt) mo (K : exc (A * ASt) -> Model -> TSet),
  minv mo -> Z.of_nat (length (so_buf s)) < 2^64 ->
  t_eq (tsh (exit_k ioA (A:=A) st s) mo K)
       (t_emit (wr 1 (fst (exit_flush_run s))) (t_exit (exit_code st) (m_fs mo))).
Proof.
  intros A st s mo K MI BND. unfold exit_k, exit_model. cbn [io_exit ioA io_S].
  eapply t_eq_trans; [apply tshape_mbind|].
  eapply t_eq_trans; [apply tshape_mbind|].
  eapply t_eq_trans.
  { apply (tshape_stdout_exit_flush aget_so aset_so aget_set aset_set aset_get); [exact MI| exact BND|].
    cbn [kbind fst snd]. apply (proj2 (tshape_exit_msysA _ _ _ _ [])). apply t_emit_has_nil. }
  apply t_eq_emit. cbn [kbind fst snd]. apply tshape_exit_msysA.
Qed.

Lemma twf_exit_kA : forall {A} st (s : ASt) mo (P : exc (A * ASt) -> Model -> Prop),
  minv mo -> Z.of_nat (length (so_buf s)) < 2^64 -> twf (exit_k ioA (A:=A) st s) mo P.
Proof.
  intros A st s mo P MI BND. unfold exit_k, exit_model. cbn [io_exit ioA io_S].
  unfold mbind. apply twf_bind. apply twf_bind.
  apply (twfP_stdout_exit_flush aget_so aset_so aget_set aset_set aset_get); [exact MI| exact BND|].
  cbn [fst snd]. unfold msys, enode. cbn [twf]. split; [exact I|].
  intros rsp mo' evs Hst. exfalso. exact (nstep_exit_none _ _ _ _ _ Hst).
Qed.

Lemma twf_fdtree_fs {R} : forall (t : itree node R) (P : R -> Model -> Prop) mo,
  fdtree t -> twf t mo P -> twf t mo (fun r mo' => P r mo' /\ m_fs mo' = m_fs mo).
Proof.
  induction t as [r | n k IH]; intros P mo Ht H; cbn in *.
  - split; [exact H| reflexivity].
  - destruct Ht as [Hn Hk]. destruct H as [Hs H]. split; [exact Hs|]. intros rsp mo' evs ST.
    assert (EF : m_fs mo' = m_fs mo).
    { destruct Hn as [Hfd | Hex].
      - destruct (fd_transfer n mo mo rsp mo' evs Hfd eq_refl eq_refl ST) as (mo2 & _ & [[-> _] | (f & -> & _)]); [reflexivity| apply m_fs_with_fds].
      - destruct n; try contradiction. all: exfalso; exact (nstep_exit_none _ _ _ _ _ ST). }
    eapply twf_mono; [apply IH; [apply Hk| exact (H rsp mo' evs ST)]|]. cbv beta. intros r mo1 [HPr E1]. split; [exact HPr| congruence].
Qed.

Section POSTA.
  Context {HC : HasCeiling} {HG : HasGuard}.
  Variable FI : fs_if.
  Variable AI : am_if FI.
  Hypothesis AMS : forall lo hi, a0_static lo hi -> am_static FI AI lo hi.
  Variable PZ : mem -> Prop.
  Hypothesis PZ_agree : forall (P : Z -> Prop) m m', gagree_on P m m' -> (forall a, pz_band a -> P a) -> PZ m -> PZ m'.
  Variables (sp0 : word) (argv envp : list (list byte)) (uid hw : word) (rnd : EntryDraw) (TID : Z) (S4 S5 S6 S7 S8 S9 S10 S11 : word).
  Hypothesis VSP : valid_sp sp0.
  Hypothesis CEIL : alloc_ceiling = LO sp0.
  Hypothesis ESF : entry_stack_fits sp0 argv envp.
  Hypothesis HT : 0 < TID < 2^31.
  Hypothesis AC : am_contracts FI AI (JA FI AI).
  Hypothesis FZ : fuzz_one_stmtA FI AI (JA FI AI) PZ.
  Hypothesis EMIT : emit_printf_stmt aget_so aset_so.
  Hypothesis EXK : exit_k_stmtA TID.
  Notation usp0 := (bv_unsigned sp0).
  Notation rat_callA' := (rat_callA FI AI PZ sp0 argv envp uid hw rnd TID S4 S5 S6 S7 S8 S9 S10 S11).
  Notation rat_retA' := (rat_retA FI AI PZ sp0 argv envp uid hw rnd TID S4 S5 S6 S7 S8 S9 S10 S11).
  Notation rat_emitA' := (rat_emitA FI AI PZ sp0 argv envp uid hw rnd TID S4 S5 S6 S7 S8 S9 S10 S11).
  Notation rat_emit_retA' := (rat_emit_retA FI AI PZ sp0 argv envp uid hw rnd TID S4 S5 S6 S7 S8 S9 S10 S11).
  Notation rat_free_ownedA' := (rat_free_ownedA FI AI PZ sp0 argv envp uid hw rnd TID S4 S5 S6 S7 S8 S9 S10 S11).
  Notation rat_owned_retA' := (rat_owned_retA FI AI PZ sp0 argv envp uid hw rnd TID S4 S5 S6 S7 S8 S9 S10 S11).
  Notation rat_free_bufA' := (rat_free_bufA FI AI PZ sp0 argv envp uid hw rnd TID S4 S5 S6 S7 S8 S9 S10 S11).
  Notation rat_main_retA' := (rat_main_retA FI AI PZ sp0 argv envp uid hw rnd TID S4 S5 S6 S7 S8 S9 S10 S11).

  Definition LF (msr : machine_state) (g : gst) (msF : machine_state) (mo : Model) : Prop :=
    hzero (g_H g) msF /\ restrict (g_H g) msF = msr /\ INVA (mkCfg msF mo) g.

  #[using="Type"] Lemma LF_minv : forall msr g msF mo, LF msr g msF mo -> exists mo', meq (VA g mo) mo' /\ minv mo' /\ m_fs mo' = m_fs mo.
  Proof.
    intros msr g msF mo (_ & _ & [HF _]). exists (strip_vm (VA g mo)). pose proof (lf_minv _ _ _ _ _ HF) as (M & _).
    unfold meq, VA in *. rewrite m_fds_strip_vm, !m_fs_strip_vm, m_fs_perase. split; [split; reflexivity|]. split; [exact M| reflexivity].
  Qed.

  #[using="Type"] Lemma seamr_realizes : forall (P : machine_state -> gst -> Prop) msr g msF mo T,
    SEAMr P msr g -> LF msr g msF mo ->
    (forall msr' g' msF' mo', P msr' g' -> LF msr' g' msF' mo' -> m_fs mo' = m_fs mo -> realizes asegs (mkCfg msF' mo') T) ->
    realizes asegs (mkCfg msF mo) T.
  Proof.
    intros P msr g msF mo T HS (HZ & ER & HINV) HK.
    pose proof (HS msF HZ ER mo HINV) as SR.
    apply (sr_realizes asegs _ _ _ SR). intros [msF' mo'] (a' & HINV' & HM & HP). cbn [cfg_ms cfg_model] in *.
    eapply (HK _ a' msF' mo' HP); [| rewrite <- (VA_fs g mo), <- (VA_fs a' mo'); symmetry; exact (proj2 HM)].
    split; [exact (proj1 (proj2 HINV'))|]. split; [reflexivity| exact HINV'].
  Qed.

  #[using="Type"] Lemma evtr_realizes : forall (Pm : machine_state -> Prop) msr g msF mo T,
    evt asegs Pm msr -> LF msr g msF mo ->
    (forall msr' msF' mo', Pm msr' -> LF msr' g msF' mo' -> m_fs mo' = m_fs mo -> realizes asegs (mkCfg msF' mo') T) ->
    realizes asegs (mkCfg msF mo) T.
  Proof.
    intros Pm msr g msF mo T HE HL HK.
    eapply (seamr_realizes (fun msr' g' => g' = g /\ Pm msr')); [| exact HL|].
    - eapply SEAMr_evt; [exact HE|]. intros msr' HP. apply SEAMr_ret. auto.
    - intros msr' g' msF' mo' [-> HP] HL' EF. exact (HK _ _ _ HP HL' EF).
  Qed.

  #[using="Type"] Lemma implM_realizes : forall {A} (c : M ASt A) (s : ASt) (Q : A -> ASt -> machine_state -> Prop)
      (P : exc (A * ASt) -> Model -> Prop) (K : exc (A * ASt) -> Model -> TSet) msr g msF mo,
    implM asegs c s Q msr -> fdtree (c s) -> LF msr g msF mo ->
    twf (c s) (VA g mo) P -> (forall r m1 m2, meq m1 m2 -> P r m1 -> P r m2) -> (forall m, ~ P Unr m) ->
    (forall x s' msr' msF' mo', Q x s' msr' -> LF msr' g msF' mo' -> P (Ok (x, s')) (VA g mo') -> m_fs mo' = m_fs mo ->
        realizes asegs (mkCfg msF' mo') (K (Ok (x, s')) (VA g mo'))) ->
    (forall r m1 m2, meq m1 m2 -> t_eq (K r m1) (K r m2)) ->
    realizes asegs (mkCfg msF mo) (tsh (c s) (VA g mo) K).
  Proof.
    intros A c s Q P K msr g msF mo HI HFT (HZ & ER & HINV) TW HP HPU HK KC.
    pose proof (dj_of_impl (c s) (epost (fun p => Q (fst p) (snd p))) msr g HFT HI msF HZ ER) as HS.
    apply (implS_realizes_twf asegs gst VA INVA ATNA GOODA VA_fs NODE_A (c s) _
             (fun r mo' => P r mo' /\ m_fs mo' = m_fs (VA g mo)) K msF g mo HFT HS HINV); [| | | exact KC].
    - apply twf_fdtree_fs; [exact HFT| exact TW].
    - intros r m1 m2 HM [HPr EF]. split; [exact (HP r m1 m2 HM HPr)| rewrite <- EF; symmetry; exact (proj2 HM)].
    - intros [|[x s']] msF' a' mo' [HQ ->] HINV' [HPr EF]; cbn [epost fst snd] in HQ; [destruct (HPU _ HPr)|].
      eapply HK; [exact HQ| | exact HPr| rewrite !VA_fs in EF; exact EF].
      split; [exact (proj1 (proj2 HINV'))|]. split; [reflexivity| exact HINV'].
  Qed.

  #[using="Type"] Lemma twfP_twf {R} : forall (t : itree node R) mo P, twfP node nstep nsafe t mo P -> MSafe.twf t mo P.
  Proof.
    induction t as [r | n k IH]; intros mo P H; cbn in *; [exact H|].
    destruct H as [Hs Hk]. split; [exact Hs|]. intros rsp mo' evs ST. apply IH. exact (Hk rsp mo' evs ST).
  Qed.

  #[using="Type"] Lemma fdtree_stdout_vprintfA : forall ps (so : ASt), fdtree (stdout_vprintf aget_so aset_so ps so).
  Proof.
    intros ps so. unfold stdout_vprintf. apply fdtree_mbind; [unfold stdout_towrite; fdt|]. intros _ so1. clear so. revert so1.
    induction ps as [|p ps IH]; intros so; cbn [out_pieces]; [apply fdtree_mret|].
    apply fdtree_mbind; [| intros; apply IH]. unfold stdout_fwritex, stdout_towrite. fdt.
  Qed.

  Definition noUnr {A} : exc A -> Model -> Prop := fun r _ => match r with Unr => False | Ok _ => True end.
  #[using="Type"] Lemma noUnr_meq {A} : forall (r : exc A) m1 m2, meq m1 m2 -> noUnr r m1 -> noUnr r m2.
  Proof. intros [|a] m1 m2 _ H; exact H. Qed.
  #[using="Type"] Lemma noUnr_unr {A} : forall m, ~ @noUnr A Unr m. Proof. intros m H. exact H. Qed.

  #[using="EXK"] Lemma exit_realizesA : forall sts so msr g msF mo,
    rat_exitA TID sts so msr -> LF msr g msF mo -> Z.of_nat (length (so_buf so)) < 2^64 ->
    realizes asegs (mkCfg msF mo) (t_emit (wr 1 (fst (exit_flush_run so))) (t_exit (exit_code sts) (m_fs mo))).
  Proof.
    intros sts so msr g msF mo HX HL BND.
    destruct (LF_minv _ _ _ _ HL) as (mo1 & HM1 & MI1 & EF1).
    pose proof (EXK (at_parser (ptr:=unit)) sts so (fun _ _ _ => False) msr HX) as IMPL.
    assert (FT : fdtree (exit_k ioA (A:=at_parser (ptr:=unit)) sts so)) by (unfold exit_k; fdt).
    eapply rz_conseq.
    - eapply (implM_realizes (exit_k ioA sts) so (fun _ _ _ => False) noUnr (fun _ _ => t_nil));
        [exact IMPL| exact FT| exact HL| | apply noUnr_meq| apply noUnr_unr| intros x s' msr' msF' mo' F; destruct F| intros; apply t_eq_refl].
      apply (twf_fdtree_cong _ _ mo1 (VA g mo) FT (meq_sym _ _ HM1) noUnr_meq). apply twf_exit_kA; [exact MI1| exact BND].
    - eapply t_eq_trans; [apply (tsh_fdtree_cong _ (fun _ _ => t_nil) (VA g mo) mo1 FT HM1); intros; apply t_eq_refl|].
      rewrite <- EF1. apply tshape_exit_kA; [exact MI1| exact BND].
  Qed.

  #[using="AMS PZ_agree VSP CEIL ESF HT AC EXK"] Lemma free_buf_realizesA : forall sts ap d so msr g msF mo,
    rat_free_bufA' sts ap d so msr g -> LF msr g msF mo -> Z.of_nat (length (so_buf so)) < 2^64 ->
    realizes asegs (mkCfg msF mo) (t_emit (wr 1 (fst (exit_flush_run so))) (t_exit (exit_code sts) (m_fs mo))).
  Proof.
    intros sts ap d so msr g msF mo HR HL BND.
    eapply seamr_realizes; [eapply free_buf_seamA; first [exact HR| eassumption]| exact HL|].
    cbv beta. intros msr' g' msF' mo' HR' HL' EF. rewrite <- EF.
    eapply evtr_realizes; [eapply main_ret_exitA; first [exact HR'| eassumption]| exact HL'|].
    cbv beta. intros msr'' msF'' mo'' HX HL'' EF'. rewrite <- EF'.
    eapply exit_realizesA; [exact HX| exact HL''| exact BND].
  Qed.

  #[using="Type"] Lemma drv_statusA_0 : forall (d : dlayA (am_K FI AI)), drv_status d false = 0.
  Proof. intros d. unfold drv_status. destruct (d_sc d <? 0); reflexivity. Qed.

  #[using="AMS PZ_agree VSP CEIL ESF HT AC EXK"] Lemma free_owned_realizesA : forall ap d so msr g msF mo,
    rat_free_ownedA' false ap d so msr g -> LF msr g msF mo -> Z.of_nat (length (so_buf so)) < 2^64 ->
    realizes asegs (mkCfg msF mo) (AssembleP0.PSH 0 so (m_fs mo)).
  Proof.
    intros ap d so msr g msF mo HR HL BND. cbn [AssembleP0.PSH].
    eapply seamr_realizes; [eapply free_owned_seamA; first [exact HR| eassumption]| exact HL|].
    cbv beta. intros msr' g' msF' mo' HR' HL' EF. rewrite <- EF.
    eapply evtr_realizes; [eapply owned_ret_to_free_bufA; first [exact HR'| eassumption]| exact HL'|].
    cbv beta. intros msr'' msF'' mo'' HFB HL'' EF'. rewrite <- EF'. rewrite drv_statusA_0 in HFB.
    eapply free_buf_realizesA; [exact HFB| exact HL''| exact BND].
  Qed.

  #[using="AMS PZ_agree VSP CEIL ESF EMIT"] Lemma emit_realizesA : forall k (fl : bool) ap d so msr g msF mo (REST : ASt -> TSet),
    rat_emitA' k 0 fl ap d so msr g -> LF msr g msF mo -> Z.of_nat (length (so_buf so)) + 2 < 2^64 ->
    REST (snd (vprintf_run so pieces_emit)) [] ->
    (forall msr'' msF'' mo'', rat_emit_retA' k 0 fl ap d (snd (vprintf_run so pieces_emit)) msr'' g -> LF msr'' g msF'' mo'' -> m_fs mo'' = m_fs mo ->
        realizes asegs (mkCfg msF'' mo'') (REST (snd (vprintf_run so pieces_emit)))) ->
    realizes asegs (mkCfg msF mo) (t_emit (wr 1 (fst (vprintf_run so pieces_emit))) (REST (snd (vprintf_run so pieces_emit)))).
  Proof.
    intros k fl ap d so msr g msF mo REST HE HL BND RN HREST.
    pose proof (emit_stepA FI AI AMS PZ PZ_agree sp0 argv envp uid hw rnd TID S4 S5 S6 S7 S8 S9 S10 S11 VSP CEIL ESF EMIT k fl ap d so msr g HE) as IMPL.
    destruct (LF_minv _ _ _ _ HL) as (mo1 & HM1 & MI1 & EF1).
    set (so2 := snd (vprintf_run so pieces_emit)) in *.
    assert (BND' : Z.of_nat (length (so_buf so) + length (concat pieces_emit)) < 2^64) by (cbn [pieces_emit concat length app]; lia).
    pose proof (fdtree_stdout_vprintfA pieces_emit so) as FT.
    eapply rz_conseq.
    - eapply (implM_realizes (stdout_vprintf aget_so aset_so pieces_emit) so _
                (fun r _ => match r with Ok p => snd p = so2 | Unr => False end)
                (fun r _ => match r with Ok p => REST (snd p) | Unr => t_nil end));
        [exact IMPL| exact FT| exact HL| | intros [|p] m1 m2 _ H; exact H| intros m H; exact H| | intros; apply t_eq_refl].
      + apply (twf_fdtree_cong _ _ mo1 (VA g mo) FT (meq_sym _ _ HM1)); [intros [|p] m1 m2 _ H; exact H|].
        apply twfP_twf. eapply (twfP_stdout_vprintf aget_so aset_so aget_set aset_set aset_get pieces_emit so mo1); [exact MI1| exact BND'|].
        subst so2. cbn [fst snd]. unfold aget_so, aset_so. reflexivity.
      + intros [] s' msr' msF' mo' HQ HL' Es EF. cbn [fst snd] in Es. cbn [fst snd]. subst s'. exact (HREST _ _ _ HQ HL' EF).
    - eapply t_eq_trans; [apply (tsh_fdtree_cong _ _ (VA g mo) mo1 FT HM1); intros; apply t_eq_refl|].
      eapply t_eq_trans.
      + apply (tshape_stdout_vprintf aget_so aset_so aget_set aset_set aset_get pieces_emit so mo1); [exact MI1| exact BND'|]. cbn [fst snd]. unfold aget_so, aset_so. exact RN.
      + cbn [fst snd]. unfold aget_so, aset_so. apply t_eq_refl.
  Qed.

  Local Notation PSH := AssembleP0.PSH.
  Local Notation sost := AssembleP0.sost.

  #[using="AMS PZ_agree VSP CEIL ESF HT AC FZ EMIT EXK"] Lemma call_lastA : forall (first : bool) (j : nat) ap d msr g msF mo,
    (j <= 4)%nat ->
    rat_callA' 1 false ap d (sost first j) msr g -> LF msr g msF mo ->
    realizes asegs (mkCfg msF mo) (PSH 1 (sost first j) (m_fs mo)).
  Proof.
    intros first j ap d msr g msF mo HJ HCL HL.
    eapply seamr_realizes; [eapply parser_seamA; first [exact HCL| eassumption]| exact HL|].
    cbv beta. intros msr' g' msF' mo' HR' HL' EF. rewrite <- EF.
    eapply evtr_realizes; [eapply ret_to_emitA; first [exact HR'| eassumption]| exact HL'|].
    cbv beta. intros msr1 msF1 mo1 HE HL1 EF1. rewrite <- EF1.
    cbn [AssembleP0.PSH].
    assert (BND1 : Z.of_nat (length (so_buf (sost first j))) + 2 < 2^64) by (apply AssembleP0.sost_buf_small; lia).
    assert (BND2 : Z.of_nat (length (so_buf (snd (vprintf_run (sost first j) pieces_emit)))) < 2^64).
    { rewrite AssembleP0.vprintf_run_sost by lia. cbn [snd]. pose proof (AssembleP0.sost_buf_small false (if first then 0%nat else S j) ltac:(destruct first; lia)). lia. }
    apply (emit_realizesA 1 false ap d (sost first j) msr1 g' msF1 mo1 (fun sx => PSH 0 sx (m_fs mo1)) HE HL1 BND1 (AssembleP0.PSH_nil _ _ _)).
    intros msr2 msF2 mo2 HER HL2 EF2. rewrite <- EF2.
    eapply evtr_realizes; [eapply emit_ret_freeA; [exact HER| reflexivity]| exact HL2|].
    cbv beta. intros msr3 msF3 mo3 HFO HL3 EF3. rewrite <- EF3.
    exact (free_owned_realizesA ap d _ msr3 g' msF3 mo3 HFO HL3 BND2).
  Qed.

  #[using="AMS PZ_agree VSP CEIL ESF HT FZ EMIT"] Lemma call_stepA : forall (k : nat),
    (forall (first : bool) (j : nat) ap d msr g msF mo,
      (j + k <= 4)%nat ->
      rat_callA' (Z.of_nat (S k)) false ap d (sost first j) msr g -> LF msr g msF mo ->
      realizes asegs (mkCfg msF mo) (PSH (S k) (sost first j) (m_fs mo))) ->
    forall (first : bool) (j : nat) ap d msr g msF mo,
    (j + S k <= 4)%nat ->
    rat_callA' (Z.of_nat (S (S k))) false ap d (sost first j) msr g -> LF msr g msF mo ->
    realizes asegs (mkCfg msF mo) (PSH (S (S k)) (sost first j) (m_fs mo)).
  Proof.
    intros k IH first j ap d msr g msF mo HJ HCL HL.
    eapply seamr_realizes; [eapply parser_seamA; first [exact HCL| eassumption]| exact HL|].
    cbv beta. intros msr' g' msF' mo' HR' HL' EF. rewrite <- EF.
    eapply evtr_realizes; [eapply ret_to_emitA; first [exact HR'| eassumption]| exact HL'|].
    cbv beta. intros msr1 msF1 mo1 HE HL1 EF1. rewrite <- EF1.
    cbn [AssembleP0.PSH].
    assert (BND1 : Z.of_nat (length (so_buf (sost first j))) + 2 < 2^64) by (apply AssembleP0.sost_buf_small; lia).
    assert (ESO2 : snd (vprintf_run (sost first j) pieces_emit) = sost false (if first then 0%nat else S j)).
    { rewrite AssembleP0.vprintf_run_sost by lia. reflexivity. }
    apply (emit_realizesA (Z.of_nat (S (S k))) false ap d (sost first j) msr1 g' msF1 mo1 (fun sx => PSH (S k) sx (m_fs mo1)) HE HL1 BND1 (AssembleP0.PSH_nil _ _ _)).
    intros msr2 msF2 mo2 HER HL2 EF2. rewrite <- EF2.
    eapply evtr_realizes; [eapply emit_ret_callA; first [exact HER| eassumption| lia]| exact HL2|].
    cbv beta. intros msr3 msF3 mo3 HCL' HL3 EF3. rewrite <- EF3. replace (Z.of_nat (S (S k)) - 1) with (Z.of_nat (S k)) in HCL' by lia.
    change (false || (0 <? 0)) with false in HCL'.
    rewrite ESO2 in HCL' |- *.
    exact (IH false (if first then 0%nat else S j) ap d msr3 g' msF3 mo3 ltac:(destruct first; lia) HCL' HL3).
  Qed.

  #[using="AMS PZ_agree VSP CEIL ESF HT AC FZ EMIT EXK"] Lemma call_realizesA : forall (k : nat) (first : bool) (j : nat) ap d msr g msF mo,
    (j + k <= 4)%nat ->
    rat_callA' (Z.of_nat (S k)) false ap d (sost first j) msr g -> LF msr g msF mo ->
    realizes asegs (mkCfg msF mo) (PSH (S k) (sost first j) (m_fs mo)).
  Proof.
    induction k as [|k IH]; intros first j ap d msr g msF mo HJ HCL HL.
    - apply (call_lastA first j ap d msr g msF mo); [lia| exact HCL| exact HL].
    - apply (call_stepA k IH first j ap d msr g msF mo HJ HCL HL).
  Qed.
End POSTA.

Section LEAFA.
  Context {HC : HasCeiling} {HG : HasGuard}.
  Variable FI : fs_if.
  Variable AI : am_if FI.
  Hypothesis AMS : forall lo hi, a0_static lo hi -> am_static FI AI lo hi.
  Variable PZ : mem -> Prop.
  Hypothesis PZ_agree : forall (P : Z -> Prop) m m', gagree_on P m m' -> (forall a, pz_band a -> P a) -> PZ m -> PZ m'.
  Variables (sp0 : word) (argv envp : list (list byte)) (uid hw : word) (rnd : EntryDraw).
  Hypothesis VSP : valid_sp sp0.
  Hypothesis CEIL : alloc_ceiling = LO sp0.
  Hypothesis ESF : entry_stack_fits sp0 argv envp.
  Hypothesis AC : am_contracts FI AI (JA FI AI).
  Hypothesis FZ : fuzz_one_stmtA FI AI (JA FI AI) PZ.
  Hypothesis EMIT : emit_printf_stmt aget_so aset_so.
  Hypothesis EXK : forall TID, 0 < TID < 2^31 -> exit_k_stmtA TID.

  #[using="AMS PZ_agree VSP CEIL ESF AC FZ EMIT EXK"] Theorem leaf_realizesA : forall ap so msr g msF mo,
    QPARSER FI AI PZ sp0 argv envp uid hw rnd ap so msr g -> LF msr g msF mo -> ap_factsA ap ->
    realizes asegs (mkCfg msF mo) (AssembleP0.PSH (Z.to_nat (ap_calls ap)) stdout_init (m_fs mo)).
  Proof.
    intros ap so msr g msF mo (TID & S4 & S5 & S6 & S7 & S8 & S9 & S10 & S11 & HT & _ & RP) HL HF.
    destruct (rat_parser_callA FI AI AMS PZ PZ_agree sp0 argv envp uid hw rnd TID S4 S5 S6 S7 S8 S9 S10 S11 VSP CEIL ESF HT ap so msr g RP) as (d & HCL & ->).
    pose proof HF as (HK & _).
    assert (EK : ap_calls ap = Z.of_nat (S (Nat.pred (Z.to_nat (ap_calls ap))))) by lia.
    replace (Z.to_nat (ap_calls ap)) with (S (Nat.pred (Z.to_nat (ap_calls ap)))) by lia.
    rewrite EK in HCL.
    change stdout_init with (AssembleP0.sost true 0).
    eapply evtr_realizes; [exact HCL| exact HL|].
    cbv beta. intros msr' msF' mo' HCL' HL' EF. rewrite <- EF.
    eapply (call_realizesA FI AI AMS PZ PZ_agree sp0 argv envp uid hw rnd TID S4 S5 S6 S7 S8 S9 S10 S11 VSP CEIL ESF HT AC FZ EMIT (EXK TID HT) _ true 0%nat ap d msr' g msF' mo'); [lia| exact HCL'| exact HL'].
  Qed.
End LEAFA.
