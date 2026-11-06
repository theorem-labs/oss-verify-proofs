(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.glaze.binary_reflection.lib Require BvWfKernel.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require WdZS.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.glaze.binary_reflection.images Require Import Ubsan.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.Common.ExitSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32 OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AllocSim OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhEnframeBase OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhDefs OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhInv OSSVerify.Proofs.glaze.binary_reflection.lib.MhK OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhTac OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhFrame OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhOpen OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhRotate OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhAMetaN. Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.ExitSim.SimInv OSSVerify.Proofs.glaze.binary_reflection.lib.Common.ExitSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AllocSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AllocSim.StreamSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.MallocDefs OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhEnframeBase OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhDefs OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhInv OSSVerify.Proofs.glaze.binary_reflection.lib.MhK OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhTac OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhFrame OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhOpen OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhRotate.UbMhRepT OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhAMetaN.UbMhNtfLib.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma perm_filter : forall (A : Type) (f : A -> bool) (l l' : list A),
  Permutation l l' -> Permutation (List.filter f l) (List.filter f l').
Proof.
  intros A f l l' P. induction P as [|x l l' P IH|x y l|l l' l'' P1 IH1 P2 IH2]; cbn.
  - apply Permutation_refl.
  - destruct (f x); [apply perm_skip; exact IH | exact IH].
  - destruct (f y); destruct (f x); try apply perm_swap; try apply Permutation_refl; apply perm_skip; apply Permutation_refl.
  - eapply Permutation_trans; eassumption.
Qed.

Lemma filter_all : forall (A : Type) (f : A -> bool) (l : list A),
  (forall x, In x l -> f x = true) -> List.filter f l = l.
Proof.
  intros A f l H. induction l as [|a l IH]; cbn; [reflexivity|].
  rewrite (H a ltac:(left; reflexivity)). f_equal. apply IH. intros x Hx. apply H. right. exact Hx.
Qed.

Lemma perm_flat_map : forall (A B : Type) (f : A -> list B) (l l' : list A),
  Permutation l l' -> Permutation (flat_map f l) (flat_map f l').
Proof.
  intros A B f l l' P. induction P as [|x l l' P IH|x y l|l l' l'' P1 IH1 P2 IH2]; cbn.
  - apply Permutation_refl.
  - apply Permutation_app_head. exact IH.
  - rewrite !app_assoc. apply Permutation_app_tail. apply Permutation_app_comm.
  - eapply Permutation_trans; eassumption.
Qed.

(* [comment removed for export] *)
Lemma iv_subtract_apart : forall x y lo hi,
  0 <= x -> 0 < y -> x + y < 2 ^ 64 -> lo < hi -> (x + y <= lo \/ hi <= x) ->
  iv_subtract (Z_to_bv 64 x) (Z_to_bv 64 y) lo hi = [(Z_to_bv 64 x, Z_to_bv 64 y)].
Proof.
  intros x y lo hi Hx Hy Hxy Hlh D. unfold iv_subtract.
  assert (Ux : bv_unsigned (Z_to_bv 64 x) = x) by (apply u_Z2bv; lia).
  assert (Uy : bv_unsigned (Z_to_bv 64 y) = y) by (apply u_Z2bv; lia).
  rewrite Ux, Uy. destruct D as [D|D].
  - rewrite (proj2 (Z.ltb_lt x lo)) by lia. rewrite (proj2 (Z.ltb_ge hi (x + y))) by lia.
    rewrite Z.min_l by lia. reflexivity.
  - rewrite (proj2 (Z.ltb_ge x lo)) by lia. rewrite (proj2 (Z.ltb_lt hi (x + y))) by lia.
    rewrite Z.max_l by lia. cbn. f_equal. f_equal. f_equal. lia.
Qed.

Lemma maps_subtract_apart : forall l lo hi,
  lo < hi ->
  (forall e, In e l -> exists x y, e = (Z_to_bv 64 x, Z_to_bv 64 y) /\ 0 <= x /\ 0 < y /\ x + y < 2 ^ 64 /\ (x + y <= lo \/ hi <= x)) ->
  maps_subtract l lo hi = l.
Proof.
  intros l lo hi Hlh H. induction l as [|[a sz] l IH]; cbn; [reflexivity|].
  destruct (H (a, sz) ltac:(left; reflexivity)) as (x & y & E & Hx & Hy & Hxy & D).
  injection E. intros -> ->. rewrite (iv_subtract_apart x y lo hi Hx Hy Hxy Hlh D). cbn. f_equal.
  apply IH. intros e He. apply H. right. exact He.
Qed.

Lemma map_has_In : forall l (a n : word), In (a, n) l -> map_has l a n = true.
Proof.
  intros l a n Hin. unfold map_has. apply existsb_exists. exists (a, n). split; [exact Hin|].
  cbn. rewrite !bv_eqb_refl. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition segs_below (segs : list Segment) (top : Z) : bool :=
  forallb (fun seg => Z.leb (Z.of_N (seg_base seg) + Z.of_N (seg_size seg)) top) segs.
Definition segs_above (segs : list Segment) (bot : Z) : bool :=
  forallb (fun seg => Z.leb bot (Z.of_N (seg_base seg))) segs.

Lemma find_segment_above : forall segs top a n,
  segs_below segs top = true -> top <= a -> 0 < n -> find_segment segs a n = None.
Proof.
  intros segs top a n H Ha Hn. induction segs as [|s segs IH]; cbn; [reflexivity|].
  cbn in H. apply andb_prop in H. destruct H as [H1 H2]. apply Z.leb_le in H1.
  replace (Z.leb (Z.of_N (seg_base s)) a && Z.leb (a + n) (Z.of_N (seg_base s) + Z.of_N (seg_size s)))%bool with false.
  - apply IH. exact H2.
  - symmetry. apply andb_false_iff. right. apply Z.leb_gt. lia.
Qed.

Lemma find_segment_below : forall segs bot a n,
  segs_above segs bot = true -> a < bot -> 0 < n -> find_segment segs a n = None.
Proof.
  intros segs bot a n H Ha Hn. induction segs as [|s segs IH]; cbn; [reflexivity|].
  cbn in H. apply andb_prop in H. destruct H as [H1 H2]. apply Z.leb_le in H1.
  replace (Z.leb (Z.of_N (seg_base s)) a && Z.leb (a + n) (Z.of_N (seg_base s) + Z.of_N (seg_size s)))%bool with false.
  - apply IH. exact H2.
  - symmetry. apply andb_false_iff. left. apply Z.leb_gt. lia.
Qed.

Lemma rsegs_below : segs_below RSEGS IMG_HI = true.
Proof. vm_compute. reflexivity. Qed.
Lemma rsegs_above : segs_above RSEGS IMG_LO = true.
Proof. vm_compute. reflexivity. Qed.

(* [comment removed for export] *)
Lemma find_segment_out : forall a n, 0 < n -> (a < IMG_LO \/ IMG_HI <= a) -> find_segment RSEGS a n = None.
Proof.
  intros a n Hn [H|H].
  - exact (find_segment_below RSEGS IMG_LO a n rsegs_above H Hn).
  - exact (find_segment_above RSEGS IMG_HI a n rsegs_below H Hn).
Qed.

Section FPGen.
  Context {RN : mh_run}.
  Context {fx : FPState}.

  (* [comment removed for export] *)
  Lemma store_ok1_high : forall (M : mem) a, 0 <= a < 2 ^ 64 -> (a < IMG_LO \/ IMG_HI <= a) ->
    store_ok RSEGS M (Z_to_bv 64 a) 1%nat = true -> M (Z_to_bv 64 a) <> None.
  Proof.
    intros M a Ha Hout SOK. cbn [store_ok] in SOK. unfold wview in SOK.
    destruct (M (Z_to_bv 64 a)) eqn:E; [discriminate|].
    rewrite u_Z2bv in SOK by lia.
    rewrite (find_segment_out a 1 ltac:(lia) Hout) in SOK. discriminate SOK.
  Qed.

  Lemma defined_of_store_ok : forall (M : mem) lo hi, 0 <= lo -> hi <= 2 ^ 64 -> (hi <= IMG_LO \/ IMG_HI <= lo) ->
    (forall a, lo <= a < hi -> store_ok RSEGS M (Z_to_bv 64 a) 1%nat = true) -> defined M lo hi.
  Proof. intros M lo hi Hlo Hhi Hout H a Ha. apply store_ok1_high; [lia | lia | apply H; exact Ha]. Qed.

  Lemma store_ok_of_defined1 : forall (M : mem) lo hi a, defined M lo hi -> 0 <= lo -> hi < 2 ^ 64 -> lo <= a < hi ->
    store_ok RSEGS M (Z_to_bv 64 a) 1%nat = true.
  Proof. intros M lo hi a D H0 H64 Ha. eapply store_ok_defined; [exact D | lia | cbn; lia | exact H0 | exact H64]. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

  Lemma kat_ecall_munmap : forall regs (pc : word) mem rom model w (a : word) (len : Z) (Q : config -> Prop),
    fetch_word RSEGS pc = Some w -> is_ecall w = true ->
    m_halted model = None -> m_vm_lazy model = [] ->
    getr regs 17 = Z_to_bv 64 215 ->
    getr regs 10 = a -> bv_unsigned a mod 4096 = 0 ->
    getr regs 11 = Z_to_bv 64 len -> 0 < len -> len mod 4096 = 0 ->
    bv_unsigned a + len <= CEIL ->
    map_has (vm_maps (m_vmmaps model)) a (Z_to_bv 64 len) = true ->
    kat RSEGS (mkCfg (mkst (regupd regs 10 (Z_to_bv 64 0)) (v_addi pc 4) (unfill a (Z_to_bv 64 len) mem) rom)
                     (munmap_model a (Z_to_bv 64 len) model)) Q ->
    kat RSEGS (mkCfg (mkst regs pc mem rom) model) Q.
  Proof.
    intros regs pc mem rom model w a len Q HF HE Hh Hlazy H17 H10 Hal H11 Hlen Hlm Hce Hhas Hk.
    assert (Hnw : bv_unsigned a + len < 2 ^ 64) by (ceil; lia).
    pose proof (u64_range a) as Ra.
    assert (Hpr : page_round_up_Z len = len) by (apply page_round_up_Z_aligned; [lia | exact Hlm]).
    set (ms := {| ms_regs := regs; ms_fregs := fp_regs; ms_pc_val := pc; ms_svc_pending := Some (getr regs 17);
                  ms_resv := None; ms_fcsr := fp_csr; ms_mem := mem; ms_rom := rom |}).
    assert (Hu1 : bv_unsigned (ms_gpr ms 1) = len).
    { unfold ms, ms_gpr. cbn [ms_regs]. rewrite arg_reg_1. change (reg_get regs 11) with (getr regs 11). rewrite H11. apply u_Z2bv; lia. }
    assert (H0 : ms_gpr ms 0 = a).
    { unfold ms, ms_gpr. cbn [ms_regs]. rewrite arg_reg_0. change (reg_get regs 10) with (getr regs 10). exact H10. }
    assert (Hprw : page_round_up (ms_gpr ms 1) = Z_to_bv 64 len) by (unfold page_round_up; rewrite Hu1, Hpr; reflexivity).
    assert (Hargs : munmap_args_ok ms model).
    { unfold munmap_args_ok. rewrite H0, Hu1, Hprw, Hpr. split; [exact Hal|]. split.
      - intros Hz. apply (f_equal bv_unsigned) in Hz. rewrite Hu1 in Hz. change (bv_unsigned (Z_to_bv 64 0)) with 0 in Hz. lia.
      - split; [unfold TASK_SIZE; ceil; lia | exact Hhas]. }
    eapply kat_step; [exact Hh | exact Hlazy | reflexivity | |].
    { apply (step_ecall RSEGS regs pc mem rom w HF HE). }
    change (kat RSEGS (mkCfg ms model) Q).
    eapply (kat_munmap RSEGS ms model (getr regs 17)); [exact Hh | exact Hlazy | reflexivity | rewrite H17; apply u_Z2bv; lia | exact Hargs |].
    unfold munmap_eff. rewrite H0, Hprw. unfold ms. rewrite adv_munmap. exact Hk.
  Qed.

  (* [comment removed for export] *)
  Lemma munmap_model_eq : forall (a n : word) m,
    m_vm_lazy m = [] -> m_vm_materialized m = [] ->
    munmap_model a n m
    = with_vmmaps (mkVmMapsFull (vm_reserved (m_vmmaps m)) (map_remove (vm_maps (m_vmmaps m)) a)
                     (maps_subtract (vm_noaccess (m_vmmaps m)) (bv_unsigned a) (bv_unsigned a + bv_unsigned n))
                     (vm_start_brk (m_vmmaps m)) (vm_brk (m_vmmaps m)) (vm_limit (m_vmmaps m))
                   (vm_mmap_base (m_vmmaps m)) (vm_init_sp (m_vmmaps m))) m.
  Proof.
    intros a n m Hl Hm. destruct m as [fd [vmm lazy mat] io fsys proc lim tm].
    cbn in Hl, Hm. subst lazy mat. reflexivity.
  Qed.

  Lemma with_vmmaps_facts : forall h m,
    m_vmmaps (with_vmmaps h m) = h /\ m_halted (with_vmmaps h m) = m_halted m /\
    m_vm_lazy (with_vmmaps h m) = m_vm_lazy m /\ m_vm_materialized (with_vmmaps h m) = m_vm_materialized m /\
    m_fs (with_vmmaps h m) = m_fs m /\ m_fds (with_vmmaps h m) = m_fds m.
  Proof. intros h m. destruct m as [fd [vmm lazy mat] io fsys proc lim tm]. repeat split; reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

  Lemma REP_agree_but : forall st L (M M' : mem) (lo hi : Z),
    WF st L -> REP st M ->
    (forall a, 0 <= a < 2 ^ 64 -> M' (Z_to_bv 64 a) <> M (Z_to_bv 64 a) -> lo <= a < hi) ->
    HEAPLO <= lo /\ (hi <= IMG_LO \/ IMG_HI <= lo) ->
    (forall a, lo <= a < hi -> ~ dfoot st a /\ ~ (exists x, is_group st x /\ gcell st x a)) ->
    REP st M'.
  Proof.
    intros st L M M' lo hi HWF HREP HW [Hlo Himg] CLR.
    assert (AG : forall a, 0 <= a < 2 ^ 64 -> ~ (lo <= a < hi) -> M' (Z_to_bv 64 a) = M (Z_to_bv 64 a)).
    { intros a Hr Hn. destruct (decide (M' (Z_to_bv 64 a) = M (Z_to_bv 64 a))) as [E|NE]; [exact E|]. exfalso. exact (Hn (HW a Hr NE)). }
    assert (KEEP : forall a, dfoot st a -> M (Z_to_bv 64 a) <> None -> M' (Z_to_bv 64 a) <> None).
    { intros a Fa D E. apply D. destruct (Z.lt_ge_cases a 0) as [Hn|Hp].
      - (* [comment removed for export] *)
        exfalso. destruct Fa as [Fa|[Fa|[(ar & Har & Fa)|(x & Hx & Kx & Fa)]]]; unfold A_ERRNO, TPV, CTX in *; try lia.
        + destruct (wa_rng st (WF_areas st L HWF) ar Har) as (_ & R & _). hsep; unfold HEAPLO in R. lia.
        + destruct (group_range st L HWF x Hx) as [R _]. hsep; unfold HEAPLO in R. lia.
      - destruct (Z.lt_ge_cases a (2 ^ 64)) as [Hs|Hb].
        + rewrite <- (AG a ltac:(lia)); [exact E|]. intros Ha. exact (proj1 (CLR a Ha) Fa).
        + exfalso. destruct Fa as [Fa|[Fa|[(ar & Har & Fa)|(x & Hx & Kx & Fa)]]]; unfold A_ERRNO, TPV, CTX_END, CTX in *; try lia.
          * destruct (wa_rng st (WF_areas st L HWF) ar Har) as (_ & _ & R). ceil. lia.
          * pose proof (wg_kind st L x (wG_each st L (WF_groups st L HWF) x Hx)) as KD. rewrite Kx in KD.
            destruct KD as (_ & Kreg & _). destruct (wr_rng st (WF_regions st L HWF) _ Kreg) as (_ & R & _). cbn in R. ceil. lia. }
    constructor.
    - apply (rep_statics_tr st st M M' HREP KEEP); [|reflexivity|reflexivity].
      intros a Hr Ha. apply AG; [exact Hr|]. hsep; unfold HEAPLO, CTX in *. lia.
    - apply (rep_ctx_tr st st M M' HREP KEEP (fun _ => false) false); try reflexivity.
      + intros a Hr (Ha & _). apply AG; [exact Hr|]. hsep; unfold HEAPLO, CTX_END, CTX in *. lia.
      + intros; right; split; reflexivity.
      + right; split; reflexivity.
    - apply (rep_areas_tr st st L M M' HWF HREP KEEP (fun _ => false)); try reflexivity.
      + intros ar a Har Ha NE. exfalso. destruct (wa_rng st (WF_areas st L HWF) ar Har) as (Hal & Rlo & Rhi).
        pose proof (HW a ltac:(hsep; ceil; unfold HEAPLO in *; lia) NE) as X.
        apply (proj1 (CLR a X)). right; right; left. exists ar. split; [exact Har | exact Ha].
      + intros x Ux X. discriminate X.
    - apply (rep_groups_tr st st L M M' HWF HREP KEEP); try (intros; assumption).
      + intros; repeat split; reflexivity.
      + intros x k Hx Hk. left. reflexivity.
      + intros x a Hx G. pose proof (gcell_in_span st L HWF x a Hx G). destruct (group_range st L HWF x Hx).
        apply AG; [hsep; ceil; unfold HEAPLO in *; lia|]. intros Ha. apply (proj2 (CLR a Ha)). exists x. split; [exact Hx | exact G].
      + intros x a Hx G. left. exact G.
  Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

  Section Unmapped.
    Variables (st1 st' : mst) (L1 L : list (Z * Z)) (b len x : Z).
    Hypothesis HWF1 : WF st1 L1.
    Hypothesis HWF' : WF st' L.
    Hypothesis PERM : Permutation (s_regions st1) (RG b len (RGroup x) :: s_regions st').
    Hypothesis EBRK : s_brk st' = s_brk st1.
    #[local] Notation rg := (RG b len (RGroup x)).

    Lemma rg_in : In rg (s_regions st1).
    Proof. apply (Permutation_in _ (Permutation_sym PERM)). left. reflexivity. Qed.

    Lemma rg_rng : HEAPLO <= b /\ b + len <= CEIL /\ b mod 4096 = 0 /\ 0 < len /\ len mod 4096 = 0.
    Proof. exact (wr_rng st1 (WF_regions st1 L1 HWF1) rg rg_in). Qed.
    Lemma rg_img : b + len <= IMG_LO \/ IMG_HI <= b.
    Proof. exact (wi_regions st1 (WF_img st1 L1 HWF1) rg rg_in). Qed.

    Lemma reg'_old : forall r, In r (s_regions st') -> In r (s_regions st1) /\ r <> rg.
    Proof.
      intros r Hr. split.
      - apply (Permutation_in _ (Permutation_sym PERM)). right. exact Hr.
      - intros ->. pose proof (wr_nodup st1 (WF_regions st1 L1 HWF1)) as ND. apply NoDup_ListNoDup in ND.
        apply (Permutation_NoDup PERM) in ND. inversion ND as [|y l NI ND2]. exact (NI Hr).
    Qed.

    Lemma reg'_disj : forall r, In r (s_regions st') -> rg_base r + rg_len r <= b \/ b + len <= rg_base r.
    Proof.
      intros r Hr. destruct (reg'_old r Hr) as [H1 H2].
      destruct (wr_disj st1 (WF_regions st1 L1 HWF1) r rg H1 rg_in H2) as [D|D]; cbn in D; [left | right]; exact D.
    Qed.

    (* [comment removed for export] *)
    Lemma unmapped_clear : forall a, b <= a < b + len ->
      ~ dfoot st' a /\ ~ (exists y, is_group st' y /\ gcell st' y a).
    Proof.
      intros a Ha. pose proof rg_rng as (R1 & R2 & R3 & R4 & R5). pose proof rg_img as RI. split.
      - intros [F|[F|[(ar & Har & F)|(y & Hy & Ky & F)]]].
        + hsep; unfold A_ERRNO, TPV, HEAPLO in *. lia.
        + hsep; unfold CTX_END, CTX, HEAPLO in *. lia.
        + destruct (wa_inreg st' (WF_areas st' L HWF') ar Har) as [(rb & rl & Hin & B1 & B2 & _)|(rb & rl & e & Hin & B1 & B2)].
          * pose proof (reg'_disj _ Hin) as D. cbn in D. lia.
          * pose proof (reg'_disj _ Hin) as D. cbn in D.
            destruct (wr_meta st' (WF_regions st' L HWF') rb rl e Hin) as (E1 & E2 & E3). lia.
        + pose proof (wg_kind st' L y (wG_each st' L (WF_groups st' L HWF') y Hy)) as KD. rewrite Ky in KD.
          destruct KD as (_ & Kreg & _). pose proof (reg'_disj _ Kreg) as D. cbn in D. lia.
      - intros (y & Hy & G). pose proof (gcell_in_span st' L HWF' y a Hy G) as SP.
        destruct (ge_inreg st' (WF_geom st' L HWF') y Hy) as (r & Hin & C1 & C2).
        pose proof (reg'_disj r Hin) as D. lia.
    Qed.

    (* [comment removed for export] *)
    Lemma unmapped_not_app : forall a q nq, b <= a < b + len -> In (q, nq) L -> q <= a < q + nq -> False.
    Proof.
      intros a q nq Ha Hin Hqa.
      destruct (wL_in st' L (WF_live st' L HWF') q nq Hin) as (y & k & o & r & Hy & Hk & Sy).
      pose proof (wG_each st' L (WF_groups st' L HWF') y Hy) as WG.
      pose proof (wg_slots st' L y WG k Hk) as SW. rewrite Sy in SW. cbn [slot_wf] in SW. destruct SW as (A1 & A2 & A3 & A4 & A5 & _).
      pose proof (wg_stride st' L y WG) as [S16 _].
      assert (g_stride st' y * (k + 1) <= g_stride st' y * g_cnt st' y) by (apply Z.mul_le_mono_nonneg_l; unfold g_cnt; lia).
      assert (0 <= g_stride st' y * k) by (apply Z.mul_nonneg_nonneg; lia).
      assert (IN : g_mem st' y <= a < gspan st' y) by (unfold gspan, g_span_end, g_slot_start, UNIT, IB in *; lia).
      destruct (ge_inreg st' (WF_geom st' L HWF') y Hy) as (rr & Hrr & C1 & C2).
      pose proof (reg'_disj rr Hrr) as D. lia.
    Qed.

    (* [comment removed for export] *)
    Lemma LEDGER_unmap : forall vm, LEDGER st1 vm ->
      LEDGER st' (mkVmMapsFull (vm_reserved vm) (map_remove (vm_maps vm) (Z_to_bv 64 b))
                     (maps_subtract (vm_noaccess vm) b (b + len))
                     (vm_start_brk vm) (vm_brk vm) (vm_limit vm) (vm_mmap_base vm) (vm_init_sp vm)).
    Proof.
      intros vm [LM LN LB LR LMB]. pose proof rg_rng as (R1 & R2 & R3 & R4 & R5). hsep; ceil; unfold HEAPLO in R1, R2.
      constructor; cbn [vm_maps vm_noaccess vm_brk vm_start_brk vm_reserved].
      - (* [comment removed for export] *)
        unfold map_remove. eapply Permutation_trans.
        { apply perm_filter. eapply Permutation_trans; [exact LM|]. apply Permutation_map. exact PERM. }
        cbn [map List.filter region_entry rg_base rg_len fst]. rewrite bv_eqb_refl. cbn [negb].
        rewrite filter_all; [apply Permutation_refl|].
        intros e He. apply in_map_iff in He. destruct He as (r & <- & Hr). cbn [region_entry fst].
        destruct (reg'_old r Hr) as [Hr1 _]. destruct (wr_rng st1 (WF_regions st1 L1 HWF1) r Hr1) as (Q1 & Q2 & Q3 & Q4 & Q5).
        pose proof (reg'_disj r Hr) as D. hsep; ceil; unfold HEAPLO in Q1, Q2.
        rewrite bv_eqb_neq; [reflexivity|]. intros E. apply (f_equal bv_unsigned) in E. rewrite !u_Z2bv in E by lia. lia.
      - (* [comment removed for export] *)
        rewrite maps_subtract_apart; [| lia |].
        + eapply Permutation_trans; [exact LN|]. unfold noacc_of. rewrite EBRK. apply Permutation_app_head.
          eapply Permutation_trans; [apply perm_flat_map; exact PERM|]. cbn [flat_map noacc_of_region rg_kind]. apply Permutation_refl.
        + intros e He. apply (Permutation_in _ LN) in He. unfold noacc_of in He. apply in_app_iff in He. destruct He as [He|He].
          * (* [comment removed for export] *)
            pose proof (wr_brk st1 (WF_regions st1 L1 HWF1)) as RB.
            assert (GB : forall b0, guard_noacc (s_brk st1) = Some b0 -> In (RG b0 8192 RBrk) (s_regions st1)).
            { intros g0 Hg. unfold guard_noacc in Hg.
              destruct (s_brk st1) as [|b0 b1 gk|[[g gk]|]]; cbn in Hg; try discriminate Hg;
                destruct gk; try discriminate Hg; injection Hg; intros <-.
              - destruct RB as (_ & _ & Hin). exact Hin.
              - destruct RB as (_ & Hin). exact Hin. }
            destruct (guard_noacc (s_brk st1)) as [b0|]; [|destruct He].
            destruct He as [<-|[]]. pose proof (GB b0 eq_refl) as Hin.
            destruct (wr_rng st1 (WF_regions st1 L1 HWF1) _ Hin) as (W1 & W2 & W3 & W4 & W5). cbn [rg_base rg_len] in W1, W2, W3, W4, W5.
            assert (Hne : RG b0 8192 RBrk <> rg) by (intros E; discriminate E).
            destruct (wr_disj st1 (WF_regions st1 L1 HWF1) _ rg Hin rg_in Hne) as [D|D]; cbn in D;
              exists b0, 4096; (split; [reflexivity|]); hsep; ceil; unfold HEAPLO in *; lia.
          * apply in_flat_map in He. destruct He as (r & Hr & He).
            destruct (wr_rng st1 (WF_regions st1 L1 HWF1) r Hr) as (Q1 & Q2 & Q3 & Q4 & Q5). hsep; ceil; unfold HEAPLO in Q1, Q2.
            destruct r as [rb rl [| ex | y]]; cbn in He; [destruct He | | destruct He].
            destruct (wr_meta st1 (WF_regions st1 L1 HWF1) rb rl ex Hr) as (E1 & E2 & E3). cbn in Q1, Q2, Q4, Q5.
            assert (Hne : RG rb rl (RMeta ex) <> rg) by (intros E; discriminate E).
            destruct (ex =? 0) eqn:EX0.
            { destruct He as [<-|[]].
              destruct (wr_disj st1 (WF_regions st1 L1 HWF1) _ rg Hr rg_in Hne) as [D|D]; cbn in D; exists rb, rl; (split; [reflexivity|]); lia. }
            destruct (wr_disj st1 (WF_regions st1 L1 HWF1) _ rg Hr rg_in Hne) as [D|D]; cbn in D.
            -- destruct He as [<-|He].
               ++ exists rb, 4096. split; [reflexivity|]. lia.
               ++ destruct (4096 * (1 + ex) <? rl) eqn:T; [|destruct He]. apply Z.ltb_lt in T. destruct He as [<-|[]].
                  exists (rb + 4096 * (1 + ex)), (rl - 4096 * (1 + ex)). split; [reflexivity|]. lia.
            -- destruct He as [<-|He].
               ++ exists rb, 4096. split; [reflexivity|]. lia.
               ++ destruct (4096 * (1 + ex) <? rl) eqn:T; [|destruct He]. apply Z.ltb_lt in T. destruct He as [<-|[]].
                  exists (rb + 4096 * (1 + ex)), (rl - 4096 * (1 + ex)). split; [reflexivity|]. lia.
      - rewrite EBRK. exact LB.
      - exact LR.
      - exact LMB.
    Qed.

    (* [comment removed for export] *)
    Lemma rg_map_has : forall vm, LEDGER st1 vm -> map_has (vm_maps vm) (Z_to_bv 64 b) (Z_to_bv 64 len) = true.
    Proof.
      intros vm [LM _ _ _ _]. apply map_has_In. apply (Permutation_in _ (Permutation_sym LM)).
      apply in_map_iff. exists rg. split; [reflexivity | exact rg_in].
    Qed.
  End Unmapped.


  (* [comment removed for export] *)
  Lemma store_ok_errno : forall (M : mem), store_ok RSEGS M (Z_to_bv 64 A_ERRNO) 4%nat = true.
  Proof. intros M. apply store_ok_wseg. vm_compute. reflexivity. Qed.

  (* [comment removed for export] *)
  Lemma REP_errno_write : forall st L (M : mem), WF st L -> REP st M ->
    REP st (wbytes M (Z_to_bv 64 A_ERRNO) (word_to_le_bytes 4 (Z_to_bv 64 (s_errno st)))).
  Proof.
    intros st L M HWF HREP. set (M' := wbytes M _ _).
    pose proof (wc_errno st (WF_ctx st L HWF)) as He.
    assert (GR : mem_grows M M') by (unfold M'; apply wbytes_grows).
    assert (AG : forall a, 0 <= a < 2 ^ 64 -> ~ (A_ERRNO <= a < A_ERRNO + 4) -> M' (Z_to_bv 64 a) = M (Z_to_bv 64 a)).
    { intros a Hr Hn. unfold M'. apply UbMhEnframeBase.wbytes_miss; rewrite ?UbMhEnframeBase.length_wle4, ?u_Z2bv by (unfold A_ERRNO, TPV in *; lia); unfold A_ERRNO, TPV in *; lia. }
    constructor.
    - pose proof (rp_statics st M HREP) as [A1 A2 A3 A4 A5 A6 A7 A8].
      assert (LOW : forall a k v, 0 <= a -> a + Z.of_nat k <= 2 ^ 64 -> (a + Z.of_nat k <= A_ERRNO \/ A_ERRNO + 4 <= a) -> cell M a k v -> cell M' a k v).
      { intros a k v Ha Hk Hd C. eapply cell_agree; [exact Ha | exact Hk | | exact C]. intros y Hy Ry. cbv beta in Ry. apply AG; [lia|]. lia. }
      constructor; try (eapply LOW; [ unfold A_NEED_LOCKS, A_PAGESIZE, MLOCK, A_CANARY, A_GOT_CANARY, A_ERRNO, TPV; lia
                                    | cbn; unfold A_NEED_LOCKS, A_PAGESIZE, MLOCK, A_CANARY, A_GOT_CANARY, A_ERRNO, TPV; lia
                                    | cbn; unfold A_NEED_LOCKS, A_PAGESIZE, MLOCK, A_CANARY, A_GOT_CANARY, A_ERRNO, TPV; lia
                                    | eassumption ]).
      + unfold cell, M'. rewrite <- (UbMhEnframeBase.length_wle4 (Z_to_bv 64 (s_errno st))) at 2. apply rdn_wbytes_hit.
        rewrite UbMhEnframeBase.length_wle4, u_Z2bv by (unfold A_ERRNO, TPV; lia). unfold A_ERRNO, TPV. cbn. lia.
      + intros a Ha. rewrite AG; [exact (A7 a Ha) | unfold A_TAB_CTZ in Ha; lia | unfold A_TAB_CTZ, A_ERRNO, TPV in *; lia].
      + intros a Ha. rewrite AG; [exact (A8 a Ha) | unfold A_TAB_SC, A_TAB_MED in Ha; lia | unfold A_TAB_SC, A_TAB_MED, A_ERRNO, TPV in *; lia].
    - apply (rep_ctx_tr st st M M' HREP (dkeep_of_grows _ _ _ GR) (fun _ => false) false); try reflexivity.
      + intros a Hr (Ha & _). cbv beta. apply AG; [exact Hr|]. unfold CTX_END, CTX, A_ERRNO, TPV in *. lia.
      + intros; right; split; reflexivity.
      + right; split; reflexivity.
    - apply (rep_areas_tr st st L M M' HWF HREP (dkeep_of_grows _ _ _ GR) (fun _ => false)); try reflexivity.
      + intros ar a Har Ha NE. exfalso. destruct (wa_rng st (WF_areas st L HWF) ar Har) as (Hal & Rlo & Rhi).
        apply NE. apply AG; hsep; ceil; unfold HEAPLO, A_ERRNO, TPV in *; lia.
      + intros x Ux X. discriminate X.
    - intros x Hx. destruct (group_range st L HWF x Hx) as [X1 X2].
      pose proof (wg_stride st L x (wG_each st L (WF_groups st L HWF) x Hx)) as [S16 _].
      pose proof (wg_mem st L x (wG_each st L (WF_groups st L HWF) x Hx)) as (Y1 & Y2 & Y3).
      assert (SPAN : 0 <= g_mem st x /\ g_mem st x + 16 <= g_span_end st x /\ g_span_end st x < 2 ^ 64).
      { assert (16 <= g_stride st x * g_cnt st x) by (unfold g_cnt, g_lastidx, w_lastidx; pose proof (Z.mod_pos_bound (g_W st x) 32 ltac:(lia)); nia).
        hsep; ceil; unfold gspan, g_span_end, UNIT, IB, HEAPLO in *. lia. }
      apply (rep_group_transport st st M M' x); try reflexivity.
      + intros E; exact E.
      + destruct (s_kind st x); [split; reflexivity | exact I].
      + intros k Hk. left. reflexivity.
      + intros a G. pose proof (gcell_in_span st L HWF x a Hx G). apply AG; hsep; ceil; unfold HEAPLO, A_ERRNO, TPV in *; lia.
      + exact GR.
      + exact SPAN.
      + intros a G. exact (gcell_in_span st L HWF x a Hx G).
      + exact (rp_groups st M HREP x Hx).
  Qed.

  (* [comment removed for export] *)
  Lemma LEDGER_same : forall st st' vm, s_regions st' = s_regions st -> s_brk st' = s_brk st -> LEDGER st vm -> LEDGER st' vm.
  Proof.
    intros st st' vm ER EB [LM LN LB LR LMB]. constructor; unfold noacc_of; rewrite ?ER, ?EB; assumption.
  Qed.
End FPGen.
