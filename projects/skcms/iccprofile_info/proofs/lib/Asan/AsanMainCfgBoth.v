(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.skcms.iccprofile_info.lib.AsLib Require AsFuzzContract.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.skcms.iccprofile_info.images Require Import AsanUbsan.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Asan Require Import
  PropExec ShapeAlg SpinAlg AgentLib AsanSpec AxSymExec3 AxSymExec3Sound AxSymRun3 AsanPlanCore AsanPlan AsanPlanSound AsanPlanFO
  BothAsanPlanImages AsanInit AsanNodesArg AsanNodesIO AsanNodesRP AsanMainLib AsanMainHooksBoth AsanShape AsanMainDefsBoth AsanMainTreeBoth
  SpinAlgCfg AsanPlanSoundCfg.
Unset Nia Cache.  (* [comment removed for export] *)
Import ListNotations.
Import AX2. Import AX2S. Import APC. Import AP. Import APS.
Unset Lia Cache.
Open Scope Z_scope.

(* [comment removed for export] *)
Definition FPI (FP : PropExec.FPState) : Prop := (bv_unsigned (@PropExec.fp_csr FP) < 32)%Z.
Lemma FPI_fx0 : FPI PropExec.fx0.
Proof. unfold FPI. vm_compute. reflexivity. Qed.

Section Main.
  (* [comment removed for export] *)
  Variable sp : word.
  Variable rdraw : EntryDraw.
  Variable brk0 : word.
  Variable argv envp : list (list byte).
  Variable fs : Fs.Fs.
  Variables uid hw : word.
  Hypothesis Hsp : valid_sp sp.
  Hypothesis Hva : valid_argv argv.
  Hypothesis Hve : valid_envp envp.
  Hypothesis Hfit : entry_stack_fits sp argv envp.

  #[local] Notation c := (content_of argv fs).
  #[local] Notation SINV0' := (SINV0 APH sp rdraw brk0 argv envp uid hw).
  #[local] Notation SINV := (SINVm APH sp rdraw brk0 argv envp uid hw (content_of argv fs)).
  #[local] Notation argH := (argH0 APH sp rdraw argv envp uid hw).
  #[local] Notation LIM := AsanInit.LIMIT.

  (* [comment removed for export] *)
  Variable HS_asan : nat -> option acs.
  (* [comment removed for export] *)
  Hypothesis HSA_noblob : forall h ch, HS_asan h = Some ch -> acs_noblob ch = true.

  (* [comment removed for export] *)
  Variables KCm BFUELm FUELm : nat.
  Variable ITm : itab.

  (* [comment removed for export] *)
  Hypothesis Mrun : APSC.run_block_stmt_cfg ASEGS ITm INFO_BOTH NX0 LIM SINV argH fs KCm FPI.
  Hypothesis Msys : forall y, APSC.sys_stmt_cfg ASEGS INFO_BOTH NX0 LIM SINV argH fs FPI y.
  Hypothesis Mbrk2 : APSC.brk2_stmt_fo ASEGS INFO_BOTH NX0 LIM SINV argH fs FPI.
  Hypothesis Mbrku : APSC.brku_stmt_cfg ASEGS INFO_BOTH NX0 LIM SINV argH fs FPI.
  Hypothesis Mmmap2 : APSC.mm2_stmt_fo ASEGS INFO_BOTH NX0 LIM SINV argH fs FPI (node_mmap2 INFO_BOTH NX0 LIM).
  Hypothesis Mmmapin : forall hole : bool, APSC.mm3_stmt_fo ASEGS INFO_BOTH NX0 LIM SINV argH fs FPI (node_mmapin INFO_BOTH LIM hole).
  Hypothesis Mmprotect2 : APSC.mm2_stmt_fo ASEGS INFO_BOTH NX0 LIM SINV argH fs FPI (node_mprotect2 INFO_BOTH LIM).
  Hypothesis Mexit : APSC.exit_stmt_cfg ASEGS INFO_BOTH LIM SINV argH fs FPI.
  Hypothesis Mx : forall x, APF.xnode_fo x = true -> APSC.x_stmt_cfg ASEGS INFO_BOTH NX0 LIM SINV argH fs FPI x.
  Hypothesis Mjoin : APSC.join_stmt_cfg ASEGS INFO_BOTH NX0 LIM SINV argH fs FPI.
  (* [comment removed for export] *)
  Hypothesis Mxn : forall T, H_class_prop T argv fs SINV ->
    APSC.ext_stmt_cfg ASEGS INFO_BOTH NX0 LIM (XNm ASEGS INFO_BOTH NX0 RPN.RP_BOTH T) SINV argH fs FPI.
  Hypothesis Mxe : APSC.emit_stmt_cfg ASEGS INFO_BOTH NX0 LIM (XEm ASEGS INFO_BOTH NX0) SINV argH fs FPI.
  Hypothesis Mxb : forall T, H_class_prop T argv fs SINV ->
    APSC.ext2_stmt_cfg ASEGS INFO_BOTH NX0 LIM (XBm ASEGS NX0 T) SINV argH fs FPI.
  (* [comment removed for export] *)
  Hypothesis VF : forall E M, SINV E M -> know_ok ASEGS E M (vfacts (variant_of c)).

  Lemma SINVm_frame' : forall E M M', (forall a, argH E a = true -> M' a = M a) -> SINV E M -> SINV E M'.
  Proof. intros. eapply SINVm_frame; eassumption. Qed.
  Lemma SINVm_agree' : forall E E' M, env_agree NX0 E E' -> SINV E M -> SINV E' M.
  Proof. intros. eapply SINVm_agree; eassumption. Qed.
  Lemma SINVm_blob : forall E M, SINV E M -> forall j, eb E (8 + j)%nat = chunk j (content_of argv fs).
  Proof. intros E M (_ & _ & _ & H) j. apply H. Qed.

  Lemma HOLES0_agree : forall h E E' fs', env_agree NX0 E E' -> HOLES0 h E fs' = HOLES0 h E' fs'.
  Proof. reflexivity. Qed.
  Lemma HOLES0_nil : forall h E fs', HOLES0 h E fs' [].
  Proof. intros. reflexivity. Qed.
  Lemma HS_none_sound : APSC.holes_stmt_cfg ASEGS INFO_BOTH LIM HS_none SINV argH HOLES0 fs FPI.
  Proof. intros FP HFP h ch H. discriminate H. Qed.

  (* [comment removed for export] *)
  Fixpoint lshape_lvl (x : lshape) : nat :=
    match x with
    | LNode L => L
    | LSplit q mid a b => if qval q argv fs <=? mid then lshape_lvl a else lshape_lvl b
    end.
  Definition mtree_lvl (t : mtree) : nat := lshape_lvl (lvl_shape t).
  Lemma mtree_lvl_split : forall q mid le gt,
    mtree_lvl (MSplit q mid le gt) = if qval q argv fs <=? mid then mtree_lvl le else mtree_lvl gt.
  Proof. reflexivity. Qed.

  #[local] Notation CHK C HS cs p :=
    (APF.check ASEGS ITm INFO_BOTH NX0 LIM (XNm ASEGS INFO_BOTH NX0 RPN.RP_BOTH (iotab_of C)) (XEm ASEGS INFO_BOTH NX0) (XBm ASEGS NX0 (iotab_of C))
           HS KCm BFUELm FUELm None cs p).
  #[local] Notation AA := (argH0_agree APH sp rdraw argv envp uid hw).

  (* [comment removed for export] *)
  Lemma main_check_sound : forall C HS HOLES,
    H_class_prop (iotab_of C) argv fs SINV ->
    (forall h E E' fs', env_agree NX0 E E' -> HOLES h E fs' = HOLES h E' fs') -> (forall h E fs', HOLES h E fs' []) ->
    (forall h h' E fs', HOLES h E fs' = HOLES h' E fs') ->
    APSC.holes_stmt_cfg ASEGS INFO_BOTH LIM HS SINV argH HOLES fs FPI ->
    forall p cs s, CHK C HS cs p = COk s ->
    forall (FP : PropExec.FPState), FPI FP -> forall E R FULL model, cs_ok ASEGS INFO_BOTH LIM SINV argH fs E cs R FULL model ->
      srealizes_cfg ASEGS (@APSC.cfg_fp FP ASEGS R (pc cs) FULL model) (sd HOLES t_nil E (m_fs model) s).
  Proof.
    intros C HS HOLES HCL HOa HOn HOe HOs p cs s Hchk FP HFP E R FULL model HC.
    exact (APSC.check_sound_cfg ASEGS ITm INFO_BOTH NX0 LIM HS
                  (XNm ASEGS INFO_BOTH NX0 RPN.RP_BOTH (iotab_of C)) (XEm ASEGS INFO_BOTH NX0) (XBm ASEGS NX0 (iotab_of C))
                  asan_in_hull asan_hull_ok asan_shadow_ok SINV argH AA SINVm_agree' NX0_sp0
                  HOLES HOa HOn HOe fs KCm FPI
                  Mrun Msys Mbrk2 Mbrku Mmmap2 Mmmapin Mmprotect2 Mexit Mx Mjoin
                  (Mxn _ HCL) Mxe (Mxb _ HCL) HOs
                  FUELm BFUELm None p cs s Hchk FP HFP E R FULL model t_nil HC I eq_refl).
  Qed.

  (* [comment removed for export] *)
  Lemma cs_ok_main_facts : forall E cs R FULL model,
    cs_ok ASEGS INFO_BOTH LIM SINV argH fs E cs R FULL model ->
    (forall n, (n < 8)%nat -> ev E n = ev (E0 APH sp rdraw brk0 argv envp uid hw) n)
    /\ eb E 1%nat = nth 0 argv [] /\ eb E 2%nat = nth 1 argv [] /\ m_fs model = fs
    /\ know_ok ASEGS E FULL (vfacts (variant_of c)).
  Proof.
    intros E cs R FULL model HC.
    pose proof (co_sinv _ _ _ _ _ _ _ _ _ _ _ HC) as HS. pose proof HS as HS'.
    destruct HS as [[Hev _] [HB1 [HB2 _]]].
    refine (conj _ (conj HB1 (conj HB2 (conj (co_fs _ _ _ _ _ _ _ _ _ _ _ HC) (VF _ _ HS'))))).
    intros n Hn. apply Hev. unfold NX0. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma cs_ok_pay_start : forall C E cs R FULL model,
    in_class C argv fs = true ->
    cs_ok ASEGS INFO_BOTH LIM SINV argH fs E cs R FULL model ->
    cs_ok ASEGS INFO_BOTH LIM SINV argH fs E (pay_start cs C) R FULL model.
  Proof.
    intros C E cs R FULL model HC HCS. unfold pay_start. apply cs_ok_set_kn; [exact HCS|]. apply Forall_app. split.
    - eapply facts_of_class_sound; [eassumption.. | ]. apply (cs_ok_main_facts E cs R FULL model HCS).
    - exact (co_know _ _ _ _ _ _ _ _ _ _ _ HCS).
  Qed.

  Lemma in_class_split : forall C q mid,
    in_class C argv fs = true ->
    if qval q argv fs <=? mid then in_class (C ++ [(q, QMIN, mid)]) argv fs = true
    else in_class (C ++ [(q, mid + 1, QMAX)]) argv fs = true.
  Proof.
    intros C q mid HC. pose proof (qval_bounds APH sp rdraw argv envp fs uid hw Hva Hfit q) as Hq.
    destruct (Z.leb_spec (qval q argv fs) mid); rewrite in_class_app, HC; cbn;
      (apply andb_true_intro; split; [|reflexivity]); apply andb_true_intro; split; apply Z.leb_le; lia.
  Qed.

  (* [comment removed for export] *)
  Lemma cbounds_entry : forall C q lo hi acc,
    In (q, lo, hi) C ->
    lo <= fst (fold_left (fun acc (t : qty * Z * Z) => let '(q', lo', hi') := t in
                           if qty_eqb q q' then (Z.max (fst acc) lo', Z.min (snd acc) hi') else acc) C acc)
    /\ snd (fold_left (fun acc (t : qty * Z * Z) => let '(q', lo', hi') := t in
                         if qty_eqb q q' then (Z.max (fst acc) lo', Z.min (snd acc) hi') else acc) C acc) <= hi.
  Proof.
    assert (MONO : forall C q acc,
      fst acc <= fst (fold_left (fun acc (t : qty * Z * Z) => let '(q', lo', hi') := t in
                                  if qty_eqb q q' then (Z.max (fst acc) lo', Z.min (snd acc) hi') else acc) C acc)
      /\ snd (fold_left (fun acc (t : qty * Z * Z) => let '(q', lo', hi') := t in
                           if qty_eqb q q' then (Z.max (fst acc) lo', Z.min (snd acc) hi') else acc) C acc) <= snd acc).
    { intros C q. induction C as [|[[q' lo'] hi'] C IH]; intros acc; cbn [fold_left]; [lia|].
      destruct (qty_eqb q q'); [|apply IH]. specialize (IH (Z.max (fst acc) lo', Z.min (snd acc) hi')). cbn [fst snd] in IH. lia. }
    intros C q lo hi. induction C as [|[[q' lo'] hi'] C IH]; intros acc Hin; [destruct Hin|].
    cbn [fold_left]. destruct Hin as [E|Hin]; [|apply IH; exact Hin].
    injection E as -> -> ->. replace (qty_eqb q q) with true by (symmetry; apply qty_eqb_eq; reflexivity).
    specialize (MONO C q (Z.max (fst acc) lo, Z.min (snd acc) hi)). cbn [fst snd] in MONO. lia.
  Qed.
  (* [comment removed for export] *)
  Lemma qval_qrange : forall q, fst (qrange q) <= qval q argv fs <= snd (qrange q).
  Proof.
    pose proof (argc_range argv Hva). pose proof (L0_range' argv Hva). pose proof (L1_range' APH sp rdraw argv envp uid hw Hva). pose proof (qlook_range sp argv envp fs Hva Hfit).
    pose proof (cfglen_range (content_of argv fs)). pose proof (flen_range (content_of argv fs)).
    pose proof (bz_range 2 (content_of argv fs)). pose proof (bz_range 1 (content_of argv fs)).
    pose proof (Z.mod_pos_bound (bz 2 (content_of argv fs)) 4 ltac:(lia)).
    assert (0 <= bz 1 (content_of argv fs) / 128 <= 1).
    { split; [apply Z.div_pos; lia |]. assert (bz 1 (content_of argv fs) / 128 < 2) by (apply Z.div_lt_upper_bound; lia). lia. }
    pose proof (room_eq (content_of argv fs)). pose proof (cmod_eq (content_of argv fs)).
    intros q; destruct q; cbn [qval qrange fst snd]; lia.
  Qed.
  (* [comment removed for export] *)
  Lemma qbounds_sound : forall C q, in_class C argv fs = true -> fst (qbounds C q) <= qval q argv fs <= snd (qbounds C q).
  Proof.
    intros C q HC. unfold qbounds, clamp. cbn [fst snd].
    pose proof (cbounds_sound C q argv fs HC (qval_bounds APH sp rdraw argv envp fs uid hw Hva Hfit q)). pose proof (qval_qrange q). lia.
  Qed.
  Lemma in_class_nonempty : forall C, in_class C argv fs = true -> class_empty C = false.
  Proof.
    intros C HC. apply Bool.not_true_is_false. unfold class_empty. rewrite existsb_exists. intros (q & _ & H).
    apply Z.ltb_lt in H. pose proof (qbounds_sound C q HC). lia.
  Qed.
  (* [comment removed for export] *)
  Lemma qbounds2_sound : forall C q, in_class C argv fs = true -> fst (qbounds2 C q) <= qval q argv fs <= snd (qbounds2 C q).
  Proof.
    intros C q HC. pose proof (qbounds_sound C q HC) as B. unfold qbounds2.
    destruct q; try exact B.
    - (* [comment removed for export] *)
      assert (HLK : look_of C = qlook argv fs \/ look_of C = -1).
      { unfold look_of. destruct (Z.eqb_spec (fst (cbounds C QLook)) (snd (cbounds C QLook))); [|right; reflexivity].
        left. pose proof (cbounds_sound C QLook argv fs HC (qval_bounds APH sp rdraw argv envp fs uid hw Hva Hfit QLook)) as BL.
        pose proof (qlook_range sp argv envp fs Hva Hfit). cbn [qval] in BL. lia. }
      pose proof (look_L1_sound APH sp rdraw argv envp fs uid hw Hva Hfit (look_of C) HLK) as [LL _].
      unfold clamp. cbn [qval fst snd] in *. lia.
    - (* [comment removed for export] *)
      pose proof (qbounds_sound C QFlen HC) as BF. pose proof (qbounds_sound C QCfgLen HC) as BC.
      unfold clamp. cbn [qval fst snd] in *. pose proof (room_eq (content_of argv fs)). unfold cfglen in *. lia.
  Qed.
  Lemma in_class_weaken2 : forall C C', class_le2 C C' = true -> in_class C argv fs = true -> in_class C' argv fs = true.
  Proof.
    intros C C' HLE HC. unfold in_class. apply forallb_forall. intros [[q lo] hi] Hin.
    pose proof (qbounds2_sound C q HC) as B.
    unfold class_le2 in HLE. rewrite forallb_forall in HLE.
    assert (Hq : In q all_qty) by (destruct q; cbn; tauto).
    specialize (HLE q Hq). cbn beta in HLE. apply Bool.orb_prop in HLE as [H0|HLE]; [apply Z.ltb_lt in H0; lia|].
    apply andb_prop in HLE as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2.
    pose proof (cbounds_entry C' q lo hi (QMIN, QMAX) Hin) as E. unfold cbounds in H1, H2.
    apply andb_true_intro; split; apply Z.leb_le; lia.
  Qed.
  Lemma in_class_weaken : forall C C', class_le C C' = true -> in_class C argv fs = true -> in_class C' argv fs = true.
  Proof.
    intros C C' HLE HC. unfold in_class. apply forallb_forall. intros [[q lo] hi] Hin.
    pose proof (qbounds_sound C q HC) as B.
    unfold class_le in HLE. rewrite forallb_forall in HLE.
    assert (Hq : In q all_qty) by (destruct q; cbn; tauto).
    specialize (HLE q Hq). cbn beta in HLE. apply Bool.orb_prop in HLE as [H0|HLE]; [apply Z.ltb_lt in H0; lia|].
    apply andb_prop in HLE as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2.
    pose proof (cbounds_entry C' q lo hi (QMIN, QMAX) Hin) as E. unfold cbounds in H1, H2.
    apply andb_true_intro; split; apply Z.leb_le; lia.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma t_res_ge1 : forall L argv' fs', (1 <= L)%nat -> t_res L argv' fs' = t_res 2 argv' fs'.
  Proof. intros [|[|L]] argv' fs' H; [lia | reflexivity | reflexivity]. Qed.

  Theorem mtree_sound : forall t lo hi ch C,
    mtree_ok KCm BFUELm FUELm ITm lo hi ch C t = true -> in_class C argv fs = true ->
    (lo <= mtree_lvl t)%nat /\ (mtree_lvl t <= hi)%nat /\
    forall (FP : PropExec.FPState), FPI FP -> forall E R FULL model,
      cs_ok ASEGS INFO_BOTH LIM SINV argH fs E ch R FULL model ->
      srealizes_cfg ASEGS (@APSC.cfg_fp FP ASEGS R (pc ch) FULL model) (t_res (mtree_lvl t) argv fs).
  Proof.
    induction t as [L p | L p HT PT IH | q mid le gt IHle IHgt | e mid le gt IHle IHgt | C' t IHt | L] using mtree_ind2; intros lo hi ch C HT0 HC.
    - (* [comment removed for export] *)
      cbn [mtree_ok] in HT0. apply andb_prop in HT0 as [HL HT0]. apply andb_prop in HL as [HL1 HL2].
      apply Nat.leb_le in HL1. apply Nat.leb_le in HL2. cbn [mtree_lvl lvl_shape lshape_lvl]. split; [exact HL1|]. split; [exact HL2|].
      intros FP HFP E R FULL model HCS.
      destruct (APF.check _ _ _ _ _ _ _ _ _ _ _ _ _ _ p) as [s| ] eqn:Hchk; [|discriminate].
      pose proof (cs_ok_pay_start C E ch R FULL model HC HCS) as HC2.
      destruct (cs_ok_main_facts E _ R FULL model HC2) as (Hev & HB1 & HB2 & Hfs & HVF).
      pose proof (in_class_H_class APH sp rdraw argv envp fs uid hw Hva Hfit C SINV HC SINVm_blob) as HCL.
      pose proof (main_check_sound C HS_none HOLES0 HCL HOLES0_agree HOLES0_nil (fun _ _ _ _ => eq_refl) HS_none_sound p _ s Hchk FP HFP E R FULL model HC2) as RZ.
      rewrite Hfs in RZ. unfold pay_start in RZ. rewrite pc_set_kn in RZ.
      eapply srz_cfg_conseq; [exact RZ|].
      exact (class_pay_sound APH sp rdraw brk0 argv envp fs Hsp Hva Hve uid hw Hfit ASEGS L C s E _ HOLES0 t_nil HC HT0 Hev HB1 HB2 HVF).
    - (* [comment removed for export] *)
      rewrite mtree_ok_MPre in HT0. apply andb_prop in HT0 as [HL HT0]. apply andb_prop in HL as [HL1 HL2].
      apply Nat.leb_le in HL1. apply Nat.leb_le in HL2. cbn [mtree_lvl lvl_shape lshape_lvl]. split; [exact HL1|]. split; [exact HL2|].
      intros FP HFP E R FULL model HCS.
      destruct (APF.check _ _ _ _ _ _ _ _ _ _ _ _ _ _ p) as [s| ] eqn:Hchk; [|discriminate].
      apply andb_prop in HT0 as [HT0 HF]. apply andb_prop in HT0 as [Hseg Hcov].
      (* [comment removed for export] *)
      (* [comment removed for export] *)
      set (HOLESL := fun (h : nat) (E' : env) (fs' : Fs.Fs) => t_res 2 argv fs').
      assert (HLa : forall h E1 E2 fs', env_agree NX0 E1 E2 -> HOLESL h E1 fs' = HOLESL h E2 fs') by reflexivity.
      assert (HLn : forall h E1 fs', HOLESL h E1 fs' []) by (intros h E1 fs'; apply t_res_nil).
      assert (HLe : forall h h' E1 fs', HOLESL h E1 fs' = HOLESL h' E1 fs') by reflexivity.
      assert (HLs : APSC.holes_stmt_cfg ASEGS INFO_BOTH LIM (hs_of HT) SINV argH HOLESL fs FPI).
      { intros FP1 HFP1 j chj Hj E1 R1 FULL1 model1 HC1.
        unfold hs_of in Hj. destruct (ht_of HT j) as [[Lj chj']|] eqn:He; [|discriminate]. cbn [snd] in Hj. injection Hj as ->.
        destruct (mcover_sound HT PT j _ Hcov He) as (t' & Ht').
        pose proof (mforest_ok_sound KCm BFUELm FUELm ITm L HT C PT j t' _ HF (lookupT_In _ _ _ Ht') He) as Hok. cbn [fst snd] in Hok.
        destruct (IH j t' (lookupT_In _ _ _ Ht') (Nat.max L 1) Lj chj C Hok HC) as (H1 & _ & RZ).
        unfold HOLESL. rewrite (co_fs _ _ _ _ _ _ _ _ _ _ _ HC1), <- (t_res_ge1 (mtree_lvl t') argv fs) by lia.
        exact (RZ FP1 HFP1 E1 R1 FULL1 model1 HC1). }
      pose proof (cs_ok_pay_start C E ch R FULL model HC HCS) as HC2.
      destruct (cs_ok_main_facts E _ R FULL model HC2) as (Hev & HB1 & HB2 & Hfs & HVF).
      pose proof (in_class_H_class APH sp rdraw argv envp fs uid hw Hva Hfit C SINV HC SINVm_blob) as HCL.
      pose proof (main_check_sound C (hs_of HT) HOLESL HCL HLa HLn HLe HLs p _ s Hchk FP HFP E R FULL model HC2) as RZ.
      rewrite Hfs in RZ. unfold pay_start in RZ. rewrite pc_set_kn in RZ.
      eapply srz_cfg_conseq; [exact RZ|].
      eapply (class_seg_sound APH sp rdraw brk0 argv envp fs Hsp Hva Hve uid hw Hfit ASEGS (lv_of HT) L C s E _ HOLESL t_nil HC Hseg Hev HB1 HB2 HVF).
      (* [comment removed for export] *)
      intros j Lj Hlv. unfold lv_of in Hlv. destruct (ht_of HT j) as [[Lj' chj]|] eqn:He; [|discriminate]. cbn [fst] in Hlv. injection Hlv as ->.
      destruct (mcover_sound HT PT j _ Hcov He) as (t' & Ht').
      pose proof (mforest_ok_sound KCm BFUELm FUELm ITm L HT C PT j t' _ HF (lookupT_In _ _ _ Ht') He) as Hok. cbn [fst snd] in Hok.
      destruct (IH j t' (lookupT_In _ _ _ Ht') (Nat.max L 1) Lj chj C Hok HC) as (H1 & H2 & _).
      exists (mtree_lvl t'). split; [lia|]. split; [exact H2|]. unfold HOLESL. rewrite <- (t_res_ge1 (mtree_lvl t') argv fs) by lia. apply t_eq_refl.
    - (* [comment removed for export] *)
      cbn [mtree_ok] in HT0. apply andb_prop in HT0 as [H1 H2]. rewrite mtree_lvl_split.
      pose proof (in_class_split C q mid HC) as HC'.
      destruct (qval q argv fs <=? mid); [exact (IHle lo hi ch _ H1 HC') | exact (IHgt lo hi ch _ H2 HC')].
    - (* [comment removed for export] *)
      cbn [mtree_ok] in HT0. apply andb_prop in HT0 as [HT0 H2]. apply andb_prop in HT0 as [Hsh H1].
      apply lshape_eqb_eq in Hsh.
      assert (Llo : mtree_lvl (MCase e mid le gt) = mtree_lvl le) by reflexivity.
      assert (Lhi : mtree_lvl (MCase e mid le gt) = mtree_lvl gt) by (unfold mtree_lvl; cbn [lvl_shape]; rewrite Hsh; reflexivity).
      destruct (IHle lo hi _ C H1 HC) as (A1 & A2 & RZle). destruct (IHgt lo hi _ C H2 HC) as (_ & _ & RZgt).
      rewrite Llo. split; [exact A1|]. split; [exact A2|].
      intros FP HFP E R FULL model HCS.
      pose proof (u64_range (edenot E e)) as He. pose proof (co_know _ _ _ _ _ _ _ _ _ _ _ HCS) as HK.
      assert (HB : fst (ebounds (kn ch) e) <= uE E e <= snd (ebounds (kn ch) e)).
      { unfold ebounds. destruct (erange (kn ch) e) as [[blo bhi]|] eqn:Her; cbn [fst snd].
        - exact (erange_sound ASEGS E _ (kn ch) e blo bhi HK Her).
        - unfold uE, two64. lia. }
      destruct (Z.leb_spec (uE E e) mid) as [Hm|Hm].
      + apply (RZle FP HFP E R FULL model). unfold mcase_lo. apply cs_ok_set_kn; [exact HCS|].
        constructor; [cbn [kentry_ok]; unfold uE in *; lia | exact HK].
      + rewrite <- Llo, Lhi. apply (RZgt FP HFP E R FULL model). unfold mcase_hi. apply cs_ok_set_kn; [exact HCS|].
        constructor; [cbn [kentry_ok]; unfold uE, two64 in *; lia | exact HK].
    - (* [comment removed for export] *)
      cbn [mtree_ok] in HT0. apply andb_prop in HT0 as [HLE H1].
      exact (IHt lo hi ch C' H1 (in_class_weaken2 C C' HLE HC)).
    - (* [comment removed for export] *)
      cbn [mtree_ok] in HT0. apply andb_prop in HT0 as [_ HE]. rewrite (in_class_nonempty C HC) in HE. discriminate HE.
  Qed.

  (* [comment removed for export] *)
  Definition HOLESM (h : nat) (E : env) (fs' : Fs.Fs) : TSet := spec argv fs'.
  Lemma HOLESM_agree : forall h E E' fs', env_agree NX0 E E' -> HOLESM h E fs' = HOLESM h E' fs'.
  Proof. reflexivity. Qed.
  Lemma HOLESM_nil : forall h E fs', HOLESM h E fs' [].
  Proof. intros. apply spec_nil. Qed.

  #[local] Notation TREE_OK h := (mtree_ok KCm BFUELm FUELm ITm 0 0 (HSA HS_asan h)).

  Variable TREE : nat -> nat -> mtree.
  Hypothesis TREES : forall h ch i, HS_asan h = Some ch -> (i < 6)%nat -> TREE_OK h (root_class i) (TREE h i) = true.

  Theorem main_holes : forall FPS, (forall FP, FPS FP -> FPI FP) -> APSC.holes_stmt_cfg ASEGS INFO_BOTH LIM HS_asan SINV0' argH HOLESM fs FPS.
  Proof.
    intros FPS HFPS FP HFP h ch Hh E R FULL model HC.
    assert (Ech : ch = HSA HS_asan h) by (unfold HSA; rewrite Hh; reflexivity).
    rewrite Ech in HC |- *.
    (* [comment removed for export] *)
    assert (HNB : acs_noblob (HSA HS_asan h) = true) by (rewrite <- Ech; exact (HSA_noblob h ch Hh)).
    pose proof (cs_ok_reblob ASEGS INFO_BOTH APH sp rdraw brk0 argv envp uid hw c LIM fs E (HSA HS_asan h) R FULL model HNB HC) as HC1.
    unfold HOLESM. rewrite (co_fs _ _ _ _ _ _ _ _ _ _ _ HC).
    destruct (root_cover argv fs Hva) as (i & Hi & HCi).
    destruct (mtree_sound (TREE h i) 0 0 (HSA HS_asan h) (root_class i) (TREES h ch i Hh Hi) HCi) as (H1 & H2 & RZ).
    assert (HL : mtree_lvl (TREE h i) = 0%nat) by lia. rewrite HL in RZ. cbn [t_res] in RZ.
    exact (RZ FP (HFPS FP HFP) _ R FULL model HC1).
  Qed.

End Main.
