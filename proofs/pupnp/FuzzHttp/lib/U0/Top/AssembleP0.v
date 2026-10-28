(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence MustExit.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Kernel Require Import Fork.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP Agree Keeps RegsEquiv Ceiling InitStack EntrySecret.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.U0.Malloc Require Import MallocBlocks MallocTree MallocHINV Malloc_iface.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.U0.P0 Require Import Segs RMallocRep RMallocTree RMalloc_iface.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.U0.P0 Require Import Stdio_base Printf_lib Startup RefImpl Stdio_iface RDriver_kit RDriver_ctx RDriver_iface RF_main RF_main_post RDriver_seams RDriver_close RDriver_parser AllocInst AllocInit. From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.P0 Require Import AllocLink. From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.U0.P0 Require Import H_fuzz_stmt.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.Spec Require Import Prelim STree Malloc Monad MSafe Stdio Driver Prog KInv KStepK.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.Top Require Import Realize SafeReach Bridge AllocIF SReach AllocSpec StdioShape DriverModel.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

Notation tsh := (tshape node nstep nexit).
Notation twf := (twfP node nstep nsafe).

Lemma tshape_exit_msys : forall st (s : PState) mo (K : exc (Empty_set * PState) -> Model -> TSet),
  t_eq (tsh (msys (NExit st) dec_exit s) mo K)
       (t_exit (exit_code st) (m_fs mo)).
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

Lemma tshape_exit_k : forall {A} st (s : PState) mo (K : exc (A * PState) -> Model -> TSet),
  minv mo -> Z.of_nat (length (so_buf (ps_so s))) < 2^64 ->
  t_eq (tsh (exit_k (io_S ps_so set_so_ps) (A:=A) st s) mo K)
       (t_emit (wr 1 (fst (exit_flush_run (ps_so s))))
               (t_exit (exit_code st) (m_fs mo))).
Proof.
  intros A st s mo K MI BND. unfold exit_k, exit_model. cbn [io_exit io_S].
  eapply t_eq_trans; [apply tshape_mbind|].
  eapply t_eq_trans; [apply tshape_mbind|].
  eapply t_eq_trans.
  { apply (tshape_stdout_exit_flush ps_so set_so_ps ps_get_set ps_set_set RDriver_close.ps_set_get); [exact MI| exact BND|].
    cbn [kbind fst snd]. apply (proj2 (tshape_exit_msys _ _ _ _ [])). apply t_emit_has_nil. }
  apply t_eq_emit. cbn [kbind fst snd]. apply tshape_exit_msys.
Qed.

Lemma twf_exit_k : forall {A} st (s : PState) mo (P : exc (A * PState) -> Model -> Prop),
  minv mo -> Z.of_nat (length (so_buf (ps_so s))) < 2^64 ->
  twf (exit_k (io_S ps_so set_so_ps) (A:=A) st s) mo P.
Proof.
  intros A st s mo P MI BND. unfold exit_k, exit_model. cbn [io_exit io_S].
  apply twfP_mbind. apply twfP_mbind.
  apply (twfP_stdout_exit_flush ps_so set_so_ps ps_get_set ps_set_set RDriver_close.ps_set_get); [exact MI| exact BND|].
  cbn [pbind fst snd]. unfold msys, enode. cbn [twfP]. split; [exact I|].
  intros rsp mo' evs Hst. exfalso. exact (nstep_exit_none _ _ _ _ _ Hst).
Qed.

Notation NSR := (nodes_sound rsegs).
Definition mfr := Bridge.mframe minv.

Lemma evt_realizes : forall (P : machine_state -> Prop) ms mo T,
  mfr mo -> evt rsegs P ms -> (forall ms', P ms' -> realizes rsegs (mkCfg ms' mo) T) ->
  realizes rsegs (mkCfg ms mo) T.
Proof.
  intros P ms mo T [Hh Hm] (ms' & Hs & HP) K.
  eapply (realizes_msteps rsegs); [exact Hh| exact (minv_nolazy _ Hm)| exact Hs| apply K; exact HP].
Qed.

Section POST.
  Context {HGW : HasGuard} {HCEIL : HasCeiling}.
  Variables (sp0 : word) (argv : list (list byte)) (TID : Z) (S4 S5 S6 S7 S8 S9 S10 S11 : word).
  Hypothesis VSP : valid_sp sp0.
  Hypothesis CEIL : alloc_ceiling = LO sp0.
  Hypothesis HTID : 0 < TID < 4194304.
  Hypothesis FZ : fuzz_one_stmt AI_P0.

  #[using="VSP CEIL HTID"] Lemma exit_realizes : forall st s LB m ms mo,
    rat_main_ret sp0 argv TID S4 S5 S6 S7 S8 S9 S10 S11 st s LB m ms ->
    mfr mo -> Z.of_nat (length (so_buf (ps_so s))) < 2^64 ->
    realizes rsegs (mkCfg ms mo)
      (t_emit (wr 1 (fst (exit_flush_run (ps_so s)))) (t_exit (exit_code st) (m_fs mo))).
  Proof.
    intros st s LB m ms mo HR HF BND.
    eapply evt_realizes; [exact HF| eapply (main_ret_exit sp0 argv TID S4 S5 S6 S7 S8 S9 S10 S11 CEIL); eauto|].
    intros ms' HX.
    pose proof (exit_k_proof (at_parser (ptr:=bptr)) st s (fun _ _ _ => False) ms' HX) as IMPL.
    unfold implM in IMPL.
    eapply rz_conseq.
    - eapply (impl_realizes node rsegs (at_node rsegs) nstep nexit minv nsafe NSR _ _ ms' mo (fun _ _ => False)
                (fun _ _ => t_nil)); [exact IMPL| apply twf_exit_k; [destruct HF as [_ Hm]; exact Hm| exact BND]| exact HF|].
      intros r ms'' mo'' _ HP _. destruct HP.
    - apply tshape_exit_k; [destruct HF as [_ Hm]; exact Hm| exact BND].
  Qed.

  #[using="Type"] Lemma link_mfr : forall s LB mo, LINK rsegs AI_P0 s LB mo -> mfr mo.
  Proof.
    intros s LB mo HL. cbn [LINK AI_P0] in HL. destruct HL as [(L & _ & HK & _) _].
    split; [exact (kl_halt _ _ _ HK)| exact (kl_minv _ _ _ HK)].
  Qed.

  #[using="Type"] Lemma keep_so : forall s s', ai_keep rsegs AI_P0 s s' -> ps_so s' = ps_so s.
  Proof. intros s s' [_ H]. exact H. Qed.

  #[using="Type"] Lemma mrel_fs : forall mo mo', ai_mrel rsegs AI_P0 mo mo' -> m_fs mo' = m_fs mo.
  Proof. intros mo mo' H. exact (proj1 (ai_mrel_fs rsegs AI_P0 mo mo' H)). Qed.

  #[using="VSP CEIL HTID"] Lemma free_buf_realizes : forall st ap d s LB m ms mo,
    rat_free_buf sp0 argv TID S4 S5 S6 S7 S8 S9 S10 S11 st ap d s LB m ms ->
    LINK rsegs AI_P0 s LB mo -> Z.of_nat (length (so_buf (ps_so s))) < 2^64 ->
    realizes rsegs (mkCfg ms mo)
      (t_emit (wr 1 (fst (exit_flush_run (ps_so s)))) (t_exit (exit_code st) (m_fs mo))).
  Proof.
    intros st ap d s LB m ms mo HR HL BND.
    pose proof (free_buf_seam sp0 argv TID S4 S5 S6 S7 S8 S9 S10 S11 VSP CEIL st ap d s LB m ms HR mo HL) as SR.
    eapply sr_realizes; [exact SR|].
    intros [ms' mo'] (s' & LB' & HL' & HK & HM & (m' & HR')). cbn [cfg_ms cfg_model] in *.
    rewrite <- (keep_so _ _ HK), <- (mrel_fs _ _ HM).
    eapply exit_realizes; [exact HR'| eapply link_mfr; exact HL'| rewrite (keep_so _ _ HK); exact BND].
  Qed.

  Fixpoint PSH (k : nat) (so : stdout_st) (fs : Fs.Fs) : TSet :=
    match k with
    | O => t_emit (wr 1 (fst (exit_flush_run so))) (t_exit (exit_code 0) fs)
    | S k' => t_emit (wr 1 (fst (vprintf_run so pieces_emit))) (PSH k' (snd (vprintf_run so pieces_emit)) fs)
    end.

  Definition lines (j : nat) : list Z := concat (repeat [48; 10] j).
  Definition sost (first : bool) (j : nat) : stdout_st :=
    if first then stdout_init else mkStdout true (lines j) false false.

  #[using="Type"] Lemma lines_len : forall j, length (lines j) = (2 * j)%nat.
  Proof. induction j as [|j IH]; [reflexivity|]. unfold lines in *. cbn [repeat concat]. rewrite length_app, IH. cbn. lia. Qed.

  #[using="Type"] Lemma vprintf_run_sost : forall first j, (j <= 8)%nat ->
    vprintf_run (sost first j) pieces_emit
    = (if first then [48; 10] else [], sost false (if first then 0 else S j)%nat).
  Proof.
    intros first j Hj. destruct first.
    - cbn [sost]. rewrite vprintf_run_emit_first. reflexivity.
    - assert (E : lines j ++ [48; 10] = lines (S j)).
      { unfold lines. clear Hj. induction j as [|j IH]; [reflexivity|]. cbn [repeat concat]. rewrite <- app_assoc, IH. reflexivity. }
      cbn [sost]. rewrite vprintf_run_emit_later; [rewrite E; reflexivity|].
      unfold zlength. rewrite lines_len. unfold STDOUT_BUFSIZ. lia.
  Qed.

  #[using="Type"] Lemma sost_buf_len : forall first j, (length (so_buf (sost first j)) <= 2 * j)%nat.
  Proof. intros [|] j; cbn [sost so_buf stdout_init]; [cbn; lia| rewrite lines_len; lia]. Qed.

  #[using="Type"] Lemma sost_buf_small : forall first j, (j <= 8)%nat -> Z.of_nat (length (so_buf (sost first j))) + 2 < 2^64.
  Proof. intros [|] j Hj; cbn [sost so_buf stdout_init length]; [lia| rewrite lines_len; lia]. Qed.

  #[using="Type"] Lemma drv_status_0 : forall d, drv_status d false = 0.
  Proof. intros d. unfold drv_status. destruct (d_sc d <? 0); reflexivity. Qed.

  #[using="VSP CEIL HTID"] Lemma free_owned_realizes : forall ap d s LB m ms mo,
    rat_free_owned sp0 argv TID S4 S5 S6 S7 S8 S9 S10 S11 false ap d s LB m ms ->
    LINK rsegs AI_P0 s LB mo -> Z.of_nat (length (so_buf (ps_so s))) < 2^64 ->
    realizes rsegs (mkCfg ms mo) (PSH 0 (ps_so s) (m_fs mo)).
  Proof.
    intros ap d s LB m ms mo HR HL BND. cbn [PSH].
    pose proof (free_owned_seam sp0 argv TID S4 S5 S6 S7 S8 S9 S10 S11 VSP CEIL false ap d s LB m ms HR mo HL) as SR.
    eapply sr_realizes; [exact SR|].
    intros [ms' mo'] (s' & LB' & HL' & HK & HM & (m' & HR')). cbn [cfg_ms cfg_model] in *.
    rewrite <- (keep_so _ _ HK), <- (mrel_fs _ _ HM).
    eapply evt_realizes; [eapply link_mfr; exact HL'| eapply (owned_ret_to_free_buf sp0 argv TID); eauto|].
    intros ms'' HFB. rewrite drv_status_0 in HFB.
    eapply free_buf_realizes; [exact HFB| exact HL'| rewrite (keep_so _ _ HK); exact BND].
  Qed.

  #[using="Type"] Lemma link_set_so : forall s LB mo so, LINK rsegs AI_P0 s LB mo -> LINK rsegs AI_P0 (set_so_ps so s) LB mo.
  Proof.
    intros s LB mo so HL. cbn [LINK AI_P0] in *. unfold P0_LINK, OWN in *. destruct s; cbn in *. exact HL.
  Qed.

  #[using="Type"] Lemma PSH_nil : forall k so fs, PSH k so fs [].
  Proof. intros k so fs. destruct k; cbn [PSH]; apply t_emit_has_nil. Qed.

  #[using="VSP CEIL"] Lemma emit_realizes : forall k ap d s LB m ms mo (REST : PState -> TSet),
    rat_emit sp0 argv TID S4 S5 S6 S7 S8 S9 S10 S11 k 0 false ap d s LB m ms ->
    LINK rsegs AI_P0 s LB mo -> Z.of_nat (length (so_buf (ps_so s))) + 2 < 2^64 ->
    REST (set_so_ps (snd (vprintf_run (ps_so s) pieces_emit)) s) [] ->
    (forall m'' ms'', rat_emit_ret sp0 argv TID S4 S5 S6 S7 S8 S9 S10 S11 k 0 false ap d
                        (set_so_ps (snd (vprintf_run (ps_so s) pieces_emit)) s) LB m'' ms'' ->
        realizes rsegs (mkCfg ms'' mo) (REST (set_so_ps (snd (vprintf_run (ps_so s) pieces_emit)) s))) ->
    realizes rsegs (mkCfg ms mo)
      (t_emit (wr 1 (fst (vprintf_run (ps_so s) pieces_emit)))
              (REST (set_so_ps (snd (vprintf_run (ps_so s) pieces_emit)) s))).
  Proof.
    intros k ap d s LB m ms mo REST HE HL BND RN HREST.
    pose proof (emit_step sp0 argv TID S4 S5 S6 S7 S8 S9 S10 S11 CEIL k false ap d s LB m ms VSP HE) as IMPL. unfold implM in IMPL.
    pose proof (link_mfr _ _ _ HL) as HF. destruct HF as [Hh Hm].
    set (s2 := set_so_ps (snd (vprintf_run (ps_so s) pieces_emit)) s) in *.
    assert (BND' : Z.of_nat (length (so_buf (ps_so s)) + length (concat pieces_emit)) < 2^64).
    { cbn [pieces_emit concat length app]. lia. }
    eapply rz_conseq.
    - eapply (impl_realizes node rsegs (at_node rsegs) nstep nexit minv nsafe NSR _ _ ms mo
                (fun r mo1 => r = Ok (tt, s2) /\ mo1 = mo)
                (fun r mo1 => match r with Ok p => REST (snd p) | Unr => t_nil end));
        [exact IMPL| | split; assumption|].
      + apply (twfP_stdout_vprintf ps_so set_so_ps ps_get_set ps_set_set RDriver_close.ps_set_get);
          [exact Hm| exact BND'| split; reflexivity].
      + intros r ms'' mo1 HQ [-> ->] _. cbn [epost fst snd] in HQ. destruct HQ as (m'' & so' & HR'' & Es).
        cbn [snd]. eapply HREST. exact HR''.
    - eapply t_eq_trans.
      + apply (tshape_stdout_vprintf ps_so set_so_ps ps_get_set ps_set_set RDriver_close.ps_set_get);
          [exact Hm| exact BND'|]. cbn [fst snd]. exact RN.
      + cbn [fst snd]. apply t_eq_refl.
  Qed.

  #[using="Type"] Lemma ai_PS_P0 : ai_PS rsegs AI_P0 = PState.
  Proof. reflexivity. Qed.

  #[using="Type"] Lemma so_of_set : forall (s : PState) so, ps_so (set_so_ps so s) = so.
  Proof. intros [] so; reflexivity. Qed.

  #[using="VSP CEIL HTID FZ"] Lemma call_last : forall (first : bool) (j : nat) ap d (s : PState) LB m ms mo,
    (j <= 4)%nat ->
    rat_call sp0 argv TID S4 S5 S6 S7 S8 S9 S10 S11 1 false ap d s LB m ms ->
    LINK rsegs AI_P0 s LB mo -> ps_so s = sost first j ->
    realizes rsegs (mkCfg ms mo) (PSH 1 (sost first j) (m_fs mo)).
  Proof.
    intros first j ap d s LB m ms mo HJ HC HL HSO.
    pose proof (parser_seam sp0 argv TID S4 S5 S6 S7 S8 S9 S10 S11 VSP CEIL FZ 1 false ap d s LB m ms HC mo HL) as SR.
    eapply sr_realizes; [exact SR|].
    intros [ms' mo'] (s' & LB' & HL' & HK & HM & (m' & HR')). cbn [cfg_ms cfg_model] in HL', HK, HM, HR' |- *.
    change (ai_PS rsegs AI_P0) with PState in s'.
    rewrite <- (mrel_fs _ _ HM).
    apply (evt_realizes (fun ms1 => exists m1, rat_emit sp0 argv TID S4 S5 S6 S7 S8 S9 S10 S11 1 0 false ap d s' LB' m1 ms1) ms' mo');
      [exact (link_mfr _ _ _ HL')| exact (ret_to_emit sp0 argv TID S4 S5 S6 S7 S8 S9 S10 S11 1 0 false ap d s' LB' m' ms' VSP HR')|].
    intros ms1 (m1 & HE).
    assert (EQS : sost first j = ps_so s') by (rewrite (keep_so _ _ HK); symmetry; exact HSO).
    set (so2 := snd (vprintf_run (ps_so s') pieces_emit)).
    set (s2 := set_so_ps so2 s').
    assert (ES2 : ps_so s2 = so2) by (subst s2; apply so_of_set).
    assert (BND1 : Z.of_nat (length (so_buf (ps_so s'))) + 2 < 2^64) by (rewrite <- EQS; apply sost_buf_small; lia).
    assert (BND2 : Z.of_nat (length (so_buf (ps_so s2))) < 2^64).
    { rewrite ES2. subst so2. rewrite <- EQS, vprintf_run_sost by lia. cbn [snd].
      pose proof (sost_buf_small false (if first then 0%nat else S j) ltac:(destruct first; lia)) as BS. lia. }
    assert (R : realizes rsegs (mkCfg ms1 mo') (t_emit (wr 1 (fst (vprintf_run (ps_so s') pieces_emit))) (PSH 0 (ps_so s2) (m_fs mo')))).
    { apply (emit_realizes 1 ap d s' LB' m1 ms1 mo' (fun sx => PSH 0 (ps_so sx) (m_fs mo')) HE HL' BND1 (PSH_nil _ _ _)).
      intros m'' ms'' HER. fold so2 in HER. fold s2 in HER.
      apply (evt_realizes (rat_free_owned sp0 argv TID S4 S5 S6 S7 S8 S9 S10 S11 false ap d s2 LB' m'') ms'' mo');
        [exact (link_mfr _ _ _ (link_set_so s' LB' mo' so2 HL'))| apply (emit_ret_free sp0 argv TID S4 S5 S6 S7 S8 S9 S10 S11 1 0 false ap d s2 LB' m'' ms''); [exact HER| reflexivity] |].
      intros ms3 HFO.
      exact (free_owned_realizes ap d s2 LB' m'' ms3 mo' HFO (link_set_so _ _ _ _ HL') BND2). }
    rewrite EQS. cbn [PSH]. rewrite ES2 in R. exact R.
  Qed.

  #[using="VSP CEIL FZ"] Lemma call_step : forall (k : nat),
    (forall (first : bool) (j : nat) ap d (s : PState) LB m ms mo,
      (j + k <= 4)%nat ->
      rat_call sp0 argv TID S4 S5 S6 S7 S8 S9 S10 S11 (Z.of_nat (S k)) false ap d s LB m ms ->
      LINK rsegs AI_P0 s LB mo -> ps_so s = sost first j ->
      realizes rsegs (mkCfg ms mo) (PSH (S k) (sost first j) (m_fs mo))) ->
    forall (first : bool) (j : nat) ap d (s : PState) LB m ms mo,
    (j + S k <= 4)%nat ->
    rat_call sp0 argv TID S4 S5 S6 S7 S8 S9 S10 S11 (Z.of_nat (S (S k))) false ap d s LB m ms ->
    LINK rsegs AI_P0 s LB mo -> ps_so s = sost first j ->
    realizes rsegs (mkCfg ms mo) (PSH (S (S k)) (sost first j) (m_fs mo)).
  Proof.
    intros k IH first j ap d s LB m ms mo HJ HC HL HSO.
    pose proof (parser_seam sp0 argv TID S4 S5 S6 S7 S8 S9 S10 S11 VSP CEIL FZ (Z.of_nat (S (S k))) false ap d s LB m ms HC mo HL) as SR.
    eapply sr_realizes; [exact SR|].
    intros [ms' mo'] (s' & LB' & HL' & HK & HM & (m' & HR')). cbn [cfg_ms cfg_model] in HL', HK, HM, HR' |- *.
    change (ai_PS rsegs AI_P0) with PState in s'.
    rewrite <- (mrel_fs _ _ HM).
    apply (evt_realizes (fun ms1 => exists m1, rat_emit sp0 argv TID S4 S5 S6 S7 S8 S9 S10 S11 (Z.of_nat (S (S k))) 0 false ap d s' LB' m1 ms1) ms' mo');
      [exact (link_mfr _ _ _ HL')| exact (ret_to_emit sp0 argv TID S4 S5 S6 S7 S8 S9 S10 S11 (Z.of_nat (S (S k))) 0 false ap d s' LB' m' ms' VSP HR')|].
    intros ms1 (m1 & HE).
    assert (EQS : sost first j = ps_so s') by (rewrite (keep_so _ _ HK); symmetry; exact HSO).
    set (so2 := snd (vprintf_run (ps_so s') pieces_emit)).
    set (s2 := set_so_ps so2 s').
    assert (ES2 : ps_so s2 = so2) by (subst s2; apply so_of_set).
    assert (ESO2 : so2 = sost false (if first then 0%nat else S j)).
    { subst so2. rewrite <- EQS, vprintf_run_sost by lia. reflexivity. }
    assert (BND1 : Z.of_nat (length (so_buf (ps_so s'))) + 2 < 2^64) by (rewrite <- EQS; apply sost_buf_small; lia).
    assert (R : realizes rsegs (mkCfg ms1 mo') (t_emit (wr 1 (fst (vprintf_run (ps_so s') pieces_emit))) (PSH (S k) (ps_so s2) (m_fs mo')))).
    { apply (emit_realizes (Z.of_nat (S (S k))) ap d s' LB' m1 ms1 mo' (fun sx => PSH (S k) (ps_so sx) (m_fs mo')) HE HL' BND1 (PSH_nil _ _ _)).
      intros m'' ms'' HER. fold so2 in HER. fold s2 in HER.
      apply (evt_realizes (fun ms3 => exists m3, rat_call sp0 argv TID S4 S5 S6 S7 S8 S9 S10 S11 (Z.of_nat (S (S k)) - 1) false ap d s2 LB' m3 ms3) ms'' mo');
        [exact (link_mfr _ _ _ (link_set_so s' LB' mo' so2 HL'))| apply (emit_ret_call sp0 argv TID S4 S5 S6 S7 S8 S9 S10 S11 (Z.of_nat (S (S k))) 0 false ap d s2 LB' m'' ms''); [exact VSP| exact HER| lia] |].
      intros ms3 (m3 & HC'). replace (Z.of_nat (S (S k)) - 1) with (Z.of_nat (S k)) in HC' by lia.
      rewrite ES2, ESO2.
      exact (IH false (if first then 0%nat else S j) ap d s2 LB' m3 ms3 mo' ltac:(destruct first; lia) HC'
               (link_set_so s' LB' mo' so2 HL') ltac:(rewrite ES2; exact ESO2)). }
    rewrite EQS. cbn [PSH]. fold so2. rewrite <- ES2. exact R.
  Qed.

  #[using="VSP CEIL HTID FZ"] Lemma call_realizes : forall (k : nat) (first : bool) (j : nat) ap d (s : PState) LB m ms mo,
    (j + k <= 4)%nat ->
    rat_call sp0 argv TID S4 S5 S6 S7 S8 S9 S10 S11 (Z.of_nat (S k)) false ap d s LB m ms ->
    LINK rsegs AI_P0 s LB mo -> ps_so s = sost first j ->
    realizes rsegs (mkCfg ms mo) (PSH (S k) (sost first j) (m_fs mo)).
  Proof.
    induction k as [|k IH]; intros first j ap d s LB m ms mo HJ HC HL HSO.
    - apply (call_last first j ap d s LB m ms mo); [lia| exact HC| exact HL| exact HSO].
    - apply (call_step k IH first j ap d s LB m ms mo HJ HC HL HSO).
  Qed.
End POST.

Definition KLEAF (r : exc (at_parser (ptr:=bptr) * PState)) (mo : Model) : TSet :=
  match r with
  | Ok p => PSH (Z.to_nat (ap_calls (fst p))) stdout_init (m_fs mo)
  | Unr => t_nil
  end.

Definition prog_pre {HCEIL : HasCeiling} (argv : list (list byte)) : itree node (exc (at_parser (ptr:=bptr) * PState)) :=
  ebind (enode NSetTid dec_set_tid)
        (fun _ => drv_pre (io_S ps_so set_so_ps) raw_malloc raw_free RSV (argv_Z argv) (ps_init (reservedZ rsegs) alloc_ceiling)).

Definition T_P0 {HCEIL : HasCeiling} (argv : list (list byte)) (mo0 : Model) : TSet := tsh (prog_pre argv) mo0 KLEAF.

Lemma OWN_with_tid : forall X G s mo t,
  OWN X G s mo -> 0 < bv_unsigned t < PID_MAX_ENVELOPE -> (G s (with_tid t mo)) -> OWN X G s (with_tid t mo).
Proof.
  intros X G s mo t [(L & HC & HK & HI) [ND HG]] Ht HG'. split; [| split; [exact ND| exact HG']].
  exists L. split; [exact HC|]. split; [| exact HI].
  destruct HK. constructor; rewrite ?m_vmmaps_with_tid, ?m_halted_with_tid; try assumption.
  apply minv_with_tid; assumption.
Qed.

Section RUN.
  Context {HGW : HasGuard} {HCEIL : HasCeiling}.
  Variables (sp0 : word) (argv envp : list (list byte)) (uid hw : word) (rnd : EntryDraw).
  Variables (brk0 mbase : word) (lim : Z) (inp : ProcInput).
  Hypothesis VSP : valid_sp sp0.
  Hypothesis CEIL : alloc_ceiling = LO sp0.
  Hypothesis VARGV : valid_argv argv.
  Hypothesis VENVP : valid_envp envp.
  Hypothesis ESF : entry_stack_fits sp0 argv envp.
  Hypothesis GW : guard_word = entry_guard rnd.
  Hypothesis GS : secret_word = entry_secret rnd.
  Hypothesis VBRK : valid_brk rsegs brk0.
  Hypothesis FZ : fuzz_one_stmt AI_P0.

  Let mo0 := init_model (segments_reserved rsegs) brk0 mbase sp0 lim inp.
  Let ms0 := init_ms rsegs Ubsan_init_pc Ubsan_phdrs sp0 argv envp uid hw rnd.

  #[using="VSP CEIL FZ"] Lemma leaf_realizes : forall ap s ms mo TID S4 S5 S6 S7 S8 S9 S10 S11,
    0 < TID < 4194304 ->
    rat_parser sp0 argv TID S4 S5 S6 S7 S8 S9 S10 S11 ap s ms ->
    OWN (ap_blocks ap ++ []) DriverModel.G0 s mo ->
    realizes rsegs (mkCfg ms mo) (KLEAF (Ok (ap, s)) mo).
  Proof.
    intros ap s ms mo TID S4 S5 S6 S7 S8 S9 S10 S11 HT HP HO.
    destruct (rat_parser_call sp0 argv TID S4 S5 S6 S7 S8 S9 S10 S11 ap s ms VSP HP) as (d & LB & HEV & HSO & HFA & HLB).
    assert (HL : LINK rsegs AI_P0 s LB mo).
    { cbn [LINK AI_P0]. unfold P0_LINK. rewrite app_nil_r in HO.
      assert (E : map blk_id LB = ap_blocks ap).
      { rewrite HLB. unfold ap_blocks. destruct (ap_owned ap); reflexivity. }
      rewrite E. exact HO. }
    eapply evt_realizes; [exact (link_mfr _ _ _ HL)| exact HEV|].
    intros ms1 (m & HC0).
    pose proof HC0 as (t0 & t1 & t2 & a2 & a3 & a4 & a5 & a6 & a7 & x19 & t3 & t4 & t5 & t6 & F & fc & _ & _ & HK & SM).
    pose proof SM as ((_ & _ & _ & HC4 & _) & _).
    cbn [KLEAF fst].
    assert (EK : ap_calls ap = Z.of_nat (S (Nat.pred (Z.to_nat (ap_calls ap))))) by lia.
    replace (Z.to_nat (ap_calls ap)) with (S (Nat.pred (Z.to_nat (ap_calls ap)))) by lia.
    rewrite EK in HC0.
    apply (call_realizes sp0 argv TID S4 S5 S6 S7 S8 S9 S10 S11 VSP CEIL HT FZ _ true 0%nat ap d s LB m ms1 mo); [lia| exact HC0| exact HL| exact HSO].
  Qed.

  #[using="VARGV"] Lemma argvZ_small : Forall (fun a => Z.of_nat (length a) < 2^32) (argv_Z argv).
  Proof.
    destruct VARGV as (_ & _ & HL & _). unfold argv_Z. apply Forall_map.
    eapply Forall_impl; [| exact HL]. intros a Ha. cbn in Ha |- *. rewrite length_map. lia.
  Qed.

  #[using="HGW VSP CEIL VARGV VENVP ESF GW GS VBRK FZ"] Theorem p0_realizes : realizes rsegs (mkCfg ms0 mo0) (T_P0 argv mo0).
  Proof.
    unfold T_P0, prog_pre.
    assert (MF0 : mfr mo0). { split; [apply m_halted_init_model| apply minv_init; destruct VSP as (V1 & V2 & _); split; [exact V1| exact V2]]. }
    eapply (impl_realizes node rsegs (at_node rsegs) nstep nexit minv nsafe NSR _ _ ms0 mo0
              (fun r mo' => match r with
                            | Unr => False
                            | Ok p => OWN (ap_blocks (fst p) ++ []) DriverModel.G0 (snd p) mo'
                                      /\ (length (so_buf (ps_so (snd p))) <= 1024)%nat
                                      /\ ap_facts (fst p)
                            end)).
    -
      eapply impl_ebind.
      + exact (rstartup_spec sp0 argv envp uid hw rnd VSP VARGV VENVP).
      + intros u ms' HRM. cbn in HRM.
        exact (rmain_pre_closed sp0 argv envp uid hw rnd ms' VSP CEIL VARGV VENVP ESF GW GS HRM).
    -
      unfold ebind. apply twfP_bind. unfold enode. cbn [twfP]. split; [exact I|].
      intros rsp mo1 evs Hst.
      destruct (nstep_dec_set_tid _ _ _ _ (proj2 MF0) Hst) as (_ & t & D & Ht & Hmo1). rewrite D. cbn [twfP ITree.bind].
      assert (HO1 : OWN [] DriverModel.G0 (ps_init (reservedZ rsegs) alloc_ceiling) mo1).
      { destruct Hmo1 as [[E _] | [_ ->]].
        - exfalso. unfold mo0 in E. rewrite m_tid_init_model in E. discriminate.
        - apply OWN_with_tid; [| rewrite unsigned_lit by (unfold PID_MAX_ENVELOPE in Ht; lia); exact Ht| exact I].
          pose proof (P0_link_init brk0 mbase sp0 lim inp VBRK VSP CEIL) as L0. cbn [LINK AI_P0] in L0. unfold P0_LINK in L0. cbn [map] in L0. exact L0. }
      eapply twfP_mono.
      + apply (drv_pre_twf RSV [] (argv_Z argv) (ps_init (reservedZ rsegs) alloc_ceiling) mo1 argvZ_small HO1). cbn. lia.
      + intros [|[ap s']] mo'; cbn [fst snd]; [intros F; exact F|]. intros (O & B & _ & F). auto.
    - exact MF0.
    -
      intros [|[ap s']] ms' mo' HQ HP HF; cbn [fst snd epost] in HQ, HP; [destruct HP|].
      destruct HQ as (TID & S4 & S5 & S6 & S7 & S8 & S9 & S10 & S11 & HT & HR).
      destruct HP as (HO & _ & _).
      apply (leaf_realizes ap s' ms' mo' TID S4 S5 S6 S7 S8 S9 S10 S11 HT HR HO).
  Qed.
End RUN.
