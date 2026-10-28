From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap Mprotect.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Kernel Require Import Fork.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.Lib Require Import Cfg.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.Lib Require Import PropExec MState Mem Exec ITree Nodes Decode Ceiling.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.Spec Require Import Prelim Monad MSafe STree Malloc Prog KInv KStep KStepK JLedger MBound EquivK EquivAlloc EquivMR.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.Spec Require Import KRemapDef.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.Spec Require Import Stdio Driver MNonNull KNonNull.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.Top Require Import Realize Bridge TSim DriverSim DriverModel.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.Top Require AssembleP0.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.P0 Require Segs RDriver_kit.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.U0.P0 Require Segs.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.ClfIx Require Import PathX.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.A0.T7 Require Import TSimS MSimS DriverSimS A0Prog ShapeA0.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

Local Notation tsh := (tshape node nstep nexit) (only parsing).
Local Notation rsP := OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.P0.Segs.rsegs (only parsing).
Local Notation rsU := OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.U0.P0.Segs.rsegs (only parsing).

Definition T_P0g {HCEIL : HasCeiling} (rsv : Z) (segs : list Segment) (argv : list (list byte)) (mo0 : Model) : TSet :=
  tsh (ebind (enode NSetTid dec_set_tid)
             (fun _ => drv_pre (io_S ps_so set_so_ps) raw_malloc raw_free rsv (argv_Z argv) (ps_init (reservedZ segs) alloc_ceiling)))
      mo0 AssembleP0.KLEAF.

Lemma T_P0_g : forall (CP : HasCeiling) argv mo,
  @AssembleP0.T_P0 CP argv mo = @T_P0g CP P0.RDriver_kit.RSV rsP argv mo.
Proof. reflexivity. Qed.

Section ShapeU.
  Context {CP : HasCeiling}.
  Variables (RS_A rsv : Z) (segs : list Segment).

  Variable PI : nat -> list bptr -> PState -> Model -> Prop.
  Variable NMAX : Z.
  Hypothesis HNMAX : 2^26 <= NMAX.
  Hypothesis PI_mo : forall k X s mo, PI k X s mo -> minv mo /\ m_halted mo = None.
  Hypothesis PI_soupd : forall k X s mo so, PI k X s mo -> PI k X (set_so_ps so s) mo.
  Hypothesis PI_fdupd : forall k X s mo mo', PI k X s mo -> (mo' = mo \/ exists f, mo' = with_fds f mo) ->
    minv mo' -> m_halted mo' = None -> PI k X s mo'.
  Hypothesis PI_perm : forall k X Y s mo, Permutation X Y -> PI k X s mo -> PI k Y s mo.
  Hypothesis PI_weaken : forall k X s mo, PI (S k) X s mo -> PI k X s mo.
  Hypothesis MALLOC_P : forall k X n s mo, 0 <= n <= NMAX -> PI (S k) X s mo ->
    stwf node nstep nexit nsafe (raw_malloc n s) mo
      (fun r mo' => exists p s', r = Ok (Some p, s') /\ PI k (p :: X) s' mo' /\ ps_so s' = ps_so s
                                 /\ m_fds mo' = m_fds mo /\ m_fs mo' = m_fs mo).
  Hypothesis MALLOC_PX : forall k X n s mo, 0 <= n <= NMAX -> PI (S k) X s mo ->
    exists p s' mo', tpaths (raw_malloc n s) mo [] (Ok (Some p, s')) mo'.
  Hypothesis FREE_P : forall k X p s mo, PI k (p :: X) s mo ->
    stwf node nstep nexit nsafe (raw_free p s) mo
      (fun r mo' => exists s', r = Ok (tt, s') /\ PI k X s' mo' /\ ps_so s' = ps_so s
                               /\ m_fds mo' = m_fds mo /\ m_fs mo' = m_fs mo).
  Hypothesis FREE_PX : forall k X p s mo, PI k (p :: X) s mo -> exists s' mo', tpaths (raw_free p s) mo [] (Ok (tt, s')) mo'.

  Definition STARTg (k : nat) (moP0 moA : Model) : Prop :=
    m_tid moP0 = None /\ minv moP0 /\ m_halted moP0 = None /\
    (forall t, 0 < t < PID_MAX_ENVELOPE -> PI (DRV_BUDGET k) [] (ps_init (reservedZ segs) alloc_ceiling) (with_tid (Z_to_bv 64 t) moP0)) /\
    m_fds moP0 = m_fds moA /\ m_fs moP0 = m_fs moA /\ minv moA /\ m_halted moA = None.

  #[using="NMAX HNMAX PI_mo PI_soupd PI_fdupd PI_perm PI_weaken MALLOC_P MALLOC_PX FREE_P FREE_PX"] Theorem shape_incl0_g : forall k argv moP0 moA,
    STARTg k moP0 moA ->
    t_incl0 (T_P0g rsv segs argv moP0) (T_A0main RS_A argv moA)
    /\ t_incl0 (T_A0main RS_A argv moA) (T_P0g rsv segs argv moP0).
  Proof.
    intros k argv moP0 moA (TID0 & MIP & HP & PINIT & EF & ES & MIA & HA).
    unfold T_P0g, T_A0main. unfold enode. rewrite ebind_vis.
    split.
    -
      eapply stsim_tshape.
      + apply ss_left.
        * split; [| intros code mo' EX; exact EX]. intros rsp mo' evs ST. exact (proj1 ST).
        * intros rsp moP1 evs ST. destruct (nstep_dec_set_tid _ _ _ _ MIP ST) as (_ & t & D & Ht & [[E _]|[_ ->]]); [rewrite TID0 in E; discriminate|].
          rewrite D, ebind_ret_ok.
          pose proof (malloc_simS_PA PI NMAX MALLOC_P) as MS. pose proof (free_simS_PA PI FREE_P) as FS.
          destruct (RI_laws PI PI_mo PI_soupd PI_fdupd PI_perm PI_weaken) as (L1 & L2 & L3 & L4 & L5 & L6).
          apply (drv_pre_simS ps_so set_so_ps aget_so aset_so raw_malloc raw_free amalloc0 afree0 rsv RS_A (RI PI) NMAX HNMAX
                   L1 L2 L3 L4 L5 L6 MS FS k [] (argv_Z argv)).
          split; [apply PINIT; exact Ht|]. split; [reflexivity|]. rewrite m_fds_with_tid, m_fs_with_tid.
          split; [exact EF|]. split; [exact ES|]. split; assumption.
      + intros [|[apA sA']] moA' [|[apB sB']] moB'; cbn [leafQ]; intros HQ; try contradiction; [apply t_incl0_refl|].
        destruct HQ as [(_ & _ & _ & EC & _) (_ & _ & _ & ES' & _)]. cbn [AssembleP0.KLEAF KLEAF_A fst snd]. rewrite EC, ES'. apply t_incl0_refl.
    -
      eapply stsim_tshape.
      + eapply (ss_right nstep nexit nstep nexit _ _ moA _ _ moP0 (eff0 (Z_to_bv 64 1)) (with_tid (Z_to_bv 64 1) moP0)).
        * split; [| intros code mo' EX; exact EX]. intros rsp mo' evs ST. exact (proj1 ST).
        * cbn [nstep]. split; [reflexivity|]. exists (Z_to_bv 64 1). split; [reflexivity|]. rewrite TID0.
          split; [rewrite unsigned_lit by lia; unfold PID_MAX_ENVELOPE; lia| reflexivity].
        * assert (D : dec_set_tid (eff0 (Z_to_bv 64 1)) = Some 1).
          { unfold dec_set_tid, eff0. cbn [eff_ret eff_writes eff_zeros eff_unmaps eff_copies]. rewrite unsigned_lit by lia. reflexivity. }
          rewrite D, ebind_ret_ok.
          pose proof (malloc_simS_AP PI NMAX MALLOC_P MALLOC_PX) as MS. pose proof (free_simS_AP PI FREE_P FREE_PX) as FS.
          destruct (RI'_laws PI PI_mo PI_soupd PI_fdupd PI_perm PI_weaken) as (L1 & L2 & L3 & L4 & L5 & L6).
          apply (drv_pre_simS aget_so aset_so ps_so set_so_ps amalloc0 afree0 raw_malloc raw_free RS_A rsv (RI' PI) NMAX HNMAX
                   L1 L2 L3 L4 L5 L6 MS FS k [] (argv_Z argv)).
          unfold RI', RI. cbn [map]. split; [apply PINIT; unfold PID_MAX_ENVELOPE; lia|]. split; [reflexivity|]. rewrite m_fds_with_tid, m_fs_with_tid.
          split; [exact EF|]. split; [exact ES|]. split; assumption.
      + intros [|[apA sA']] moA' [|[apB sB']] moB'; cbn [leafQ]; intros HQ; try contradiction; [apply t_incl0_refl|].
        destruct HQ as [(_ & _ & _ & EC & _) HRI]. unfold RI', RI in HRI. destruct HRI as (_ & _ & _ & ES' & _).
        cbn [AssembleP0.KLEAF KLEAF_A fst snd]. rewrite EC, ES'. apply t_incl0_refl.
  Qed.
End ShapeU.

Theorem PI_init_U (CP : HasCeiling) (sp brk mb : word) (inp : ProcInput) (t : Z) (k : nat) :
  valid_input inp -> valid_sp sp -> valid_brk rsU brk -> valid_mmap_base mb ->
  @alloc_ceiling CP = bv_unsigned sp - stack_max_size -> 0 < t < PID_MAX_ENVELOPE -> (k <= KTOP)%nat ->
  KNonNull.PI k [] (ps_init (reservedZ rsU) (@alloc_ceiling CP))
     (with_tid (Z_to_bv 64 t) (init_model (segments_reserved rsU) brk mb sp target_alloc_limit inp)).
Proof.
  intros _ (SP1 & SP2 & _) (LO & HI & AL) (MB & _ & _) EC Ht Hk.
  assert (TOP : reserved_top (segments_reserved rsU) = 0x5d000) by (vm_compute; reflexivity). rewrite TOP in LO, HI.
  assert (BAM : brk_aslr_max = 1073741824) by (vm_compute; reflexivity).
  assert (PG : page_size = PGSZ) by (vm_compute; reflexivity). rewrite PG in AL.
  assert (PE : PID_MAX_ENVELOPE = 4194304) by reflexivity.
  assert (Ht' : 0 < bv_unsigned (Z_to_bv 64 t) < PID_MAX_ENVELOPE) by (rewrite unsigned_lit by lia; lia).
  assert (RZ : reservedZ rsU = map wwZ (segments_reserved rsU)) by reflexivity. rewrite RZ, EC.
  split; [| split].
  - split; [| split; [constructor| exact Logic.I]].
    exists (led_init (map wwZ (segments_reserved rsU)) (bv_unsigned sp - stack_max_size)). split; [| split; [| intros x []]].
    + unfold ps_init. cbn [ps_m]. apply c2_init. unfold alloc_ceiling_max, sp_window_hi, stack_max_size in *. lia.
    + unfold ps_init. cbn [ps_brk]. apply KL_with_tid; [| exact Ht'].
      apply KL_init; [| lia| exact AL| unfold sp_window_lo, stack_max_size, PGSZ in *; lia| lia].
      intros e He. pose proof (reserved_top_ehi _ _ He) as H. rewrite TOP in H. lia.
  - apply PK_with_tid. eapply PK_weaken; [apply PK_init| | |].
    + vm_compute. cbn. lia.
    + unfold SBMAX. lia.
    + unfold BACKTOP, target_alloc_limit. cbn. lia.
    + exact MB.
    + unfold Wb, BB, KTOP in *. lia.
    + unfold Wm, BM, KTOP in *. lia.
    + unfold Wp, BP, KTOP in *. lia.
  - unfold ps_init. cbn [ps_m]. apply PHM_init. exact Hk.
Qed.

Lemma HNMAX_K : 2^26 <= KNonNull.NMAX.
Proof. unfold KNonNull.NMAX, MBound.NMAX. apply Z.pow_le_mono_r; lia. Qed.

Theorem T_P0g_eq : forall (CPA CPB : HasCeiling) (rsvP rsvU : Z) (spA brkA mbA spB brkB mbB : word) (inp : ProcInput),
  valid_input inp ->
  valid_sp spA -> valid_brk rsP brkA -> valid_mmap_base mbA -> @alloc_ceiling CPA = bv_unsigned spA - stack_max_size ->
  valid_sp spB -> valid_brk rsU brkB -> valid_mmap_base mbB -> @alloc_ceiling CPB = bv_unsigned spB - stack_max_size ->
  @T_P0g CPA rsvP rsP (in_argv inp) (init_model (segments_reserved rsP) brkA mbA spA source_alloc_limit inp) [] ->
  @T_P0g CPB rsvU rsU (in_argv inp) (init_model (segments_reserved rsU) brkB mbB spB target_alloc_limit inp) [] ->
  t_eq (@T_P0g CPA rsvP rsP (in_argv inp) (init_model (segments_reserved rsP) brkA mbA spA source_alloc_limit inp))
       (@T_P0g CPB rsvU rsU (in_argv inp) (init_model (segments_reserved rsU) brkB mbB spB target_alloc_limit inp)).
Proof.
  intros CPA CPB rsvP rsvU spA brkA mbA spB brkB mbB inp VI VSA VBA VMA CEA VSB VBB VMB CEB NA NB.
  set (moA := init_model (segments_reserved rsP) brkA mbA spA source_alloc_limit inp) in *.
  set (moB := init_model (segments_reserved rsU) brkB mbB spB target_alloc_limit inp) in *.
  assert (MIA : minv moA) by (unfold moA; apply minv_init; destruct VSA as (V1 & V2 & _); split; [exact V1| exact V2]).
  assert (MIB : minv moB) by (unfold moB; apply minv_init; destruct VSB as (V1 & V2 & _); split; [exact V1| exact V2]).
  assert (HA : m_halted moA = None) by (unfold moA; apply m_halted_init_model).
  assert (HB : m_halted moB = None) by (unfold moB; apply m_halted_init_model).
  assert (STA : @STARTg CPA rsP KNonNull.PI 0 moA moA).
  { unfold STARTg, moA. split; [apply m_tid_init_model|]. split; [exact MIA|]. split; [exact HA|].
    split; [intros t Ht; apply (KNonNull.PI_init CPA spA brkA mbA inp t _ VI VSA VBA VMA CEA Ht); unfold DRV_BUDGET, KTOP; cbn; lia|].
    split; [reflexivity|]. split; [reflexivity|]. split; [exact MIA| exact HA]. }
  assert (STB : @STARTg CPB rsU KNonNull.PI 0 moB moA).
  { unfold STARTg, moA, moB. split; [apply m_tid_init_model|]. split; [exact MIB|]. split; [exact HB|].
    split; [intros t Ht; apply (PI_init_U CPB spB brkB mbB inp t _ VI VSB VBB VMB CEB Ht); unfold DRV_BUDGET, KTOP; cbn; lia|].
    split; [rewrite !m_fds_init_model; reflexivity|]. split; [rewrite !m_fs_init_model; reflexivity|].
    split; [exact MIA| exact HA]. }
  destruct (@shape_incl0_g CPA 0 rsvP rsP KNonNull.PI KNonNull.NMAX HNMAX_K PI_mo PI_soupd PI_fdupd PI_perm PI_weaken
              raw_malloc_stwf raw_malloc_px raw_free_stwf raw_free_px 0%nat (in_argv inp) moA moA STA) as [A1 A2].
  destruct (@shape_incl0_g CPB 0 rsvU rsU KNonNull.PI KNonNull.NMAX HNMAX_K PI_mo PI_soupd PI_fdupd PI_perm PI_weaken
              raw_malloc_stwf raw_malloc_px raw_free_stwf raw_free_px 0%nat (in_argv inp) moB moA STB) as [B1 B2].
  apply t_eq_of_incl0; [exact NA| exact NB| eapply t_incl0_trans; [exact A1| exact B2]| eapply t_incl0_trans; [exact B1| exact A2]].
Qed.
