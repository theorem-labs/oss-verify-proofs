(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.Common Require Import
  PropExec CatExec Hoare StoreOk MmapSim AllocSim ShapeAlg ShapeNodes VmLedger.
From OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.Common Require SeqExec.
From OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.Common.Mallocng Require Import
  MallocLayout MallocTree MallocTreeW MallocOps MallocInv_defs MallocInv_heap MallocInv_word
  MallocInv_sep MallocInv_wf MallocInv_wf3 MallocInv_wf4 MallocInv_dll MallocInv_tables MallocInv_steps MallocInv_repw
  MallocInv_env MallocInv_vm MallocInv_coh MallocInv_ops MallocInv_vmops MallocInv_auxv
  MallocInv_ameta_base MallocInv_ameta_iface MallocInv_ameta1 MallocInv_ameta2 MallocInv_ameta3
  MallocInv_budget MallocInv_ameta4 MallocInv_ameta5 MallocInv_ametax_iface MallocSureLedger.
Import ListNotations.
Local Open Scope Z_scope.
Local Open Scope malloc_scope.

Ltac treassoc :=
  lazymatch goal with
  | |- tsall ?W (mbind (mbind ?m ?f) ?g ?s) ?P => apply (tsall_assoc W m f g s P)
  end.

Section WithLayout.
Context {ML : MallocLayout} {MLok : MallocLayoutOk ML} {HT : HeapTop}.

Local Notation u := bv_unsigned (only parsing).
Section TailX.
  Variable W : wmode.
  Variables (sp0 : word) (argv envp : list (list byte)) (cb : list byte) (D : list Z) (A0 : astate) (s0 : mstate).

  (* [comment removed for export] *)
  Definition am_pre (h h1 : VmMaps) : Prop :=
    ((exists b, vm_maps h1 = (b, Z_to_bv 64 8192) :: vm_maps h) \/ vm_maps h1 = vm_maps h) /\
    vm_backed_bytes h1 <= vm_backed_bytes h /\
    vm_init_sp h1 = vm_init_sp h /\ vm_reserved h1 = vm_reserved h /\ vm_limit h1 = vm_limit h.

  (* [comment removed for export] *)
  Definition am_preg (h h1 : VmMaps) : Prop :=
    Z.of_nat (length (vm_maps h1)) <= Z.of_nat (length (vm_maps h)) + 1 /\
    vm_backed_bytes h1 <= vm_backed_bytes h /\
    vm_init_sp h1 = vm_init_sp h /\ vm_reserved h1 = vm_reserved h /\ vm_limit h1 = vm_limit h.
  Lemma am_preg_refl : forall h, am_preg h h.
  Proof. intros h. unfold am_preg. repeat split; auto; lia. Qed.
  Lemma am_grow_of_preg : forall h h1, am_preg h h1 -> am_grow h h1.
  Proof. intros h h1 (P1 & P2 & P3 & P4 & P5). unfold am_grow. repeat split; auto; lia. Qed.

  Lemma am_pre_refl : forall h, am_pre h h.
  Proof. intros h. unfold am_pre. repeat split; auto. lia. Qed.
  Lemma am_delta_refl : forall h, am_delta h h.
  Proof. intros h. unfold am_delta. repeat split; auto. lia. Qed.

  Definition FailPostX (s' : mstate) : Prop :=
    exists A', (am_grow (ms_vm s0) (ms_vm s') /\ (W <> WFail -> ~ am_room A0 s0)) /\   (* [comment removed for export] *)
               II sp0 argv envp cb D A' s' /\ FR A0 s0 A' s' /\ gsame A0 A' /\ AMvm A0 A' s0 s' /\
               spare A0 = 0 /\ a_areas A' = a_areas A0 /\ (W = WOk -> ~ am_budget A0 s0) /\ a_xmaps A' = a_xmaps A0 /\
               (forall x, dom A' x <-> dom A0 x).
  Definition SuccPostX (m : Z) (s' : mstate) : Prop :=
    exists A', am_grow (ms_vm s0) (ms_vm s') /\   (* [comment removed for export] *)
       II sp0 argv envp cb (m :: D) A' s' /\ FR A0 s0 A' s' /\ got_meta A0 D A' m /\ AMvm A0 A' s0 s' /\
       a_xmaps A' = a_xmaps A0 /\
       (W = WOk -> a_areas A0 = [] -> am_delta (ms_vm s0) (ms_vm s')) /\
       ((0 < spare A0 /\ ms_vm s' = ms_vm s0 /\ a_areas A' = a_areas A0 /\ spare A' = spare A0 - 1)
        \/ (spare A0 = 0 /\ a_areas A' = a_areas A0 ++ [m - 24] /\ a_ctx A' KAmc = 100 /\ a_freelist A' = [])).
  Definition BodyPostX (res : word) (s' : mstate) : Prop :=
    (res = Z_to_bv 64 0 /\ FailPostX s') \/ (exists m, res = Z_to_bv 64 m /\ SuccPostX m s').

  (* [comment removed for export] *)
  Definition apart0X (p : Z) : Prop :=
    forall b sz, In (b, sz) (vm_maps (ms_vm s0)) -> region_free (vm_noaccess (ms_vm s0)) b sz = true ->
      p + 4096 <= u b \/ u b + u sz <= p.

  (* [comment removed for export] *)
  Record PreTX (k : Z) (A : astate) (s : mstate) (p : Z) : Prop := {
    ptx_ii : II sp0 argv envp cb D A s;
    ptx_fr : FR A0 s0 A s;
    ptx_gs : gsame A0 A;
    ptx_areas : a_areas A = a_areas A0;
    ptx_amk : AMK k A0 A s0 s;
    ptx_k : 0 <= k <= 12288;
    ptx_spare0 : spare A0 = 0;
    ptx_init : a_ctx A KInit = 1;
    ptx_amc : a_ctx A KAmc = 0;
    ptx_fl : a_freelist A = [];
    ptx_aac : 1 <= a_ctx A KAac;
    ptx_p : a_ctx A KAareas = p;
    ptx_apart : apart0X p;
    ptx_budget : am_budget A0 s0 -> vm_backed_bytes (ms_vm s) + 4096 <= vm_limit (ms_vm s);
    ptx_xm : a_xmaps A = a_xmaps A0;
    ptx_dom : forall x, dom A x <-> dom A0 x;
    ptx_pre : W = WOk -> a_areas A0 = [] -> am_pre (ms_vm s0) (ms_vm s);
    ptx_preg : am_preg (ms_vm s0) (ms_vm s) (* [comment removed for export] *) }.

  (* [comment removed for export] *)
  Record PreFX (k : Z) (A : astate) (s : mstate) (p : Z) : Prop := {
    pfx_is : IS sp0 argv envp cb A s;
    pfx_vc : VMcore A (ms_vm s);
    pfx_va : VMall A (ms_vm s);
    pfx_av : AvOK A;
    pfx_us : UsOK A;
    pfx_dd : deads A D;
    pfx_frh : FRH (fun x => p <= x < p + 4096) A0 s0 A s;
    pfx_gs : gsame A0 A;
    pfx_areas : a_areas A = a_areas A0;
    pfx_amk : AMK k A0 A s0 s;
    pfx_k : 0 <= k <= 12288;
    pfx_spare0 : spare A0 = 0;
    pfx_init : a_ctx A KInit = 1;
    pfx_amc : a_ctx A KAmc = 0;
    pfx_fl : a_freelist A = [];
    pfx_brk : a_ctx A KBrk <> 0;
    pfx_aac : a_ctx A KAac = 1;
    pfx_al : page_aligned p;
    pfx_heap : heap_range p (p + 4096);
    pfx_pdom : forall x, p <= x < p + 4096 -> ~ dom A x;
    pfx_zero : forall x, p <= x < p + 4096 -> ms_mem s (Z_to_bv 64 x) = Some (Z_to_bv 8 0);
    pfx_cov : mcov (vm_maps (ms_vm s)) p 4096;
    pfx_nafree : region_free (vm_noaccess (ms_vm s)) (Z_to_bv 64 p) (Z_to_bv 64 4096) = true;
    pfx_brkok : a_ctx A KBrk = u (vm_brk (ms_vm s)) /\ 0 < u (vm_brk (ms_vm s)) /\
               u (vm_start_brk (ms_vm s)) <= u (vm_brk (ms_vm s)) /\ page_aligned (u (vm_brk (ms_vm s)));
    pfx_span : u (vm_brk (ms_vm s)) - u (vm_start_brk (ms_vm s)) <= 4096 * (Z.of_nat (length (a_areas A)) + 2);
    pfx_apart : apart0X p;
    pfx_xm : a_xmaps A = a_xmaps A0;
    pfx_nok : W = WOk -> False;
    pfx_grow : am_grow (ms_vm s0) (ms_vm s) (* [comment removed for export] *) }.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma commit_leafX : forall k A s p,
    IS sp0 argv envp cb A s -> VMcore A (ms_vm s) -> VMall A (ms_vm s) -> AvOK A -> UsOK A -> deads A D ->
    a_ctx A KInit = 1 -> a_ctx A KAmc = 0 -> a_freelist A = [] -> a_ctx A KBrk <> 0 -> 1 <= a_ctx A KAac ->
    page_aligned p -> heap_range p (p + 4096) ->
    (forall x, p <= x < p + 4096 -> ~ dom A x) ->
    (forall x, p <= x < p + 4096 -> ms_mem s (Z_to_bv 64 x) = Some (Z_to_bv 8 0)) ->
    mcov (vm_maps (ms_vm s)) p 4096 ->
    region_free (vm_noaccess (ms_vm s)) (Z_to_bv 64 p) (Z_to_bv 64 4096) = true ->
    (a_ctx A KBrk = 2^64 - 1 \/
     (a_ctx A KBrk = u (vm_brk (ms_vm s)) /\ 0 < u (vm_brk (ms_vm s)) /\
      u (vm_start_brk (ms_vm s)) <= u (vm_brk (ms_vm s)) /\ page_aligned (u (vm_brk (ms_vm s))))) ->
    (a_ctx A KAac - 1 > 0 ->
     (p + 4096) + 4096 * (a_ctx A KAac - 1) <= alloc_ceiling /\
     map_contains (vm_maps (ms_vm s)) (Z_to_bv 64 (p + 4096)) (Z_to_bv 64 (4096 * (a_ctx A KAac - 1))) = true /\
     map_contains (vm_noaccess (ms_vm s)) (Z_to_bv 64 (p + 4096)) (Z_to_bv 64 (4096 * (a_ctx A KAac - 1))) = true) ->
    u (vm_brk (ms_vm s)) - u (vm_start_brk (ms_vm s)) <= 4096 * (Z.of_nat (length (a_areas A)) + 2) ->
    (* [comment removed for export] *)
    FRH (fun x => p <= x < p + 4096) A0 s0 A s -> gsame A0 A -> a_areas A = a_areas A0 -> a_xmaps A = a_xmaps A0 ->
    (W = WOk -> a_areas A0 = [] -> am_delta (ms_vm s0) (ms_vm s)) ->
    am_grow (ms_vm s0) (ms_vm s) ->   (* [comment removed for export] *)
    AMK k A0 A s0 s -> 0 <= k <= 12288 -> spare A0 = 0 -> apart0X p ->
    tsall W (am_commit (Z_to_bv 64 p) s) BodyPostX.
  Proof.
    intros k A s p HI HVc HVa HAV HUS HD Hinit Hamc Hfl Hbrk Haac Hal Hheap Hpdom Hzero Hcov Hnafree HbrkOK Hres Hspan
           HFRH HGS Hareas Hxm Hdelta Hgrow HAMK Hk Hsp0 Hapart.
    pose proof (is_wf _ _ _ _ _ _ HI) as HW.
    apply tsall_of_tsafe. apply (tsafe_leaves_of_cps (am_commit (Z_to_bv 64 p)) s BodyPostX).
    intros K' P' HK'. unfold am_commit.
    apply (commit_ok sp0 argv envp cb D A s p HI HVc HVa HAV HUS HD Hinit Hamc Hbrk Haac Hal Hheap Hpdom Hzero Hcov Hnafree HbrkOK Hres Hspan K' P').
    intros s' HII HFR HGM Hvm. apply HK'.
    right. exists (p + 24). split; [reflexivity|]. exists (cmA A p).
    assert (Hdisj : forall pg, In pg (a_areas A) -> pg + 4096 <= p \/ p + 4096 <= pg).
    { intros pg Hpg. destruct (wf_areas_al A HW pg Hpg) as [Hpal _]. unfold page_aligned in *.
      destruct (Z.eq_dec pg p) as [-> | Hne].
      - exfalso. apply (Hpdom p); [lia|]. left. exists p. split; [exact Hpg | lia].
      - pose proof (Z_div_mod_eq_full pg 4096). pose proof (Z_div_mod_eq_full p 4096). lia. }
    assert (Hdom' : forall x, dom (cmA A p) x <-> dom A x \/ p <= x < p + 4096).
    { intros x. unfold cmA. apply (dom_aaA A HW p _ _ Hdisj x). }
    split; [rewrite Hvm; exact Hgrow|].
    split; [exact HII|]. split; [| split; [| split; [| split; [unfold cmA, aaA; cbn [a_xmaps]; exact Hxm | split; [rewrite Hvm; exact Hdelta|]]]]].
    - apply (FR_of_FRH (fun x => p <= x < p + 4096)); [apply (FRH_FR _ A0 s0 A s); [exact HFRH | exact HFR] |].
      intros x Hx. right. apply (proj2 (Hdom' x)). right. exact Hx.
    - apply (got_meta_pre A0 A); assumption.
    - destruct HAMK as [M1 A1 N1 L1]. constructor; rewrite ?Hvm.
      + exact M1.
      + exact A1.
      + intros x b sz Hd Hn Hin Hf. destruct (proj1 (Hdom' x) Hd) as [HdA | Hpg].
        * destruct (N1 x HdA) as [H0 | Hap]; [exfalso; exact (Hn H0) | exact (Hap b sz Hin Hf)].
        * pose proof (Hapart b sz Hin Hf). lia.
      + intros H0. specialize (L1 H0). lia.
    - right. split; [exact Hsp0|]. split; [| split].
      + unfold cmA, aaA. cbn [a_areas]. rewrite Hareas. replace (p + 24 - 24) with p by lia. reflexivity.
      + rewrite cmA_ctx. reflexivity.
      + unfold cmA, aaA. cbn [a_freelist]. exact Hfl.
  Qed.
  Theorem tailF_okX : forall k A s p, PreFX k A s p -> tsall W (am_tail (Some (Z_to_bv 64 p, false)) s) BodyPostX.
  Proof.
    intros k A s p PF. destruct PF.
    cbn [am_tail]. rewrite am_unprot_false. apply tw_bind_ret. cbn [negb].
    apply (commit_leafX k A s p); try assumption.
    - rewrite pfx_aac0. lia.
    - right. exact pfx_brkok0.
    - rewrite pfx_aac0. intros H. exfalso. lia.
    - intros HWk. exfalso. exact (pfx_nok0 HWk).
  Qed.
  Theorem tailT_okX : forall k A s p, PreTX k A s p -> tsall W (am_tail (Some (Z_to_bv 64 p, true)) s) BodyPostX.
  Proof.
    intros k A s p PT. destruct PT as [HII HFR HGS Hareas HAMK Hk Hsp0 Hinit Hamc Hfl Haac Hp Hapart Hbud Hxm Hdom2 Hpre Hpreg].
    pose proof HII as [HI HVo HAV HUS HD]. pose proof HI as [HW HR HC HWIN HE HG].
    pose proof (VMok_core A _ HVo) as HVc. pose proof HVo as [Vg Vb Va Vres Vbv Vpw Vmw Vna Vac Vpc Vall Vspan Vtop].
    destruct (Va ltac:(lia)) as (R1 & R2 & R3 & R4). rewrite Hp in R1, R2, R3, R4.
    ceil. pose proof (wf_ctx_nonneg A HW KAareas) as Hp0. rewrite Hp in Hp0.
    set (aac := a_ctx A KAac) in *.
    assert (Hbrk : a_ctx A KBrk <> 0).
    { intros H0. destruct (wf_brk0 A HW H0) as (_ & _ & X). unfold aac in *. lia. }
    pose proof (na_nw A _ HVc) as NW. pose proof (maps_nw_of A _ HVc) as NWM.
    assert (Hcovp : mcov (vm_maps (ms_vm s)) p 4096).
    { apply (mcov_sub _ (u (Z_to_bv 64 p)) (u (Z_to_bv 64 (4096 * aac)))); [apply map_contains_mcov; exact R3 | rewrite uZ by lia; lia | rewrite !uZ by lia; lia]. }
    assert (Hnap : mcov (vm_noaccess (ms_vm s)) p 4096).
    { apply (mcov_sub _ (u (Z_to_bv 64 p)) (u (Z_to_bv 64 (4096 * aac)))); [apply map_contains_mcov; exact R4 | rewrite uZ by lia; lia | rewrite !uZ by lia; lia]. }
    cbn [am_tail]. rewrite (am_unprot_true p) by first [lia | exact R1].
    treassoc. rewrite A_PAGE_SIZE_eq. eapply (tw_ld_pagesize W sp0 argv envp cb A); [exact HI|].
    treassoc. apply tw_assert; [reflexivity|].
    treassoc.
    eapply tw_sys_mprotect_none04;
      [exact HWIN | rewrite PZ_u; lia | rewrite uZ by lia; exact R1 | rewrite pruZ_PZ, uZ, Vtop by lia; lia
      | rewrite pru_PZ; apply (map_contains_sub _ _ _ _ _ R3); rewrite !uZ by lia; lia
      | rewrite pru_PZ; apply (map_contains_sub _ _ _ _ _ R4); rewrite !uZ by lia; lia | |].
    - (* [comment removed for export] *)
      (* [comment removed for export] *)
      intros Hnok. assert (HWf : W <> WOk \/ mprot_ok_vm (ms_vm s) (Z_to_bv 64 p) (page_round_up PZ) = false) by (right; exact Hnok).
      cbv beta. change (is0 MAP_FAILED) with false. cbv iota.
      treassoc. eapply (tw_lw_errno12 W _ (ms_mem s)); [apply WIN_upd; exact HWIN | reflexivity |].
      apply tw_bind_ret. unfold wlit. rewrite c_eq_Z by lia. cbn [Z.eqb Pos.eqb negb].
      apply tw_ret'. left. split; [reflexivity|].
      exists A.
      split.
      { (* [comment removed for export] *)
        split; [cbn [ms_vm upd]; apply am_grow_of_preg; exact Hpreg|].
        intros _ Hroom. destruct Hroom as [Hsp | [Hbud' _]]; [lia|].
        destruct Hcovp as (B & SZ & HinB & B1 & B2).
        rewrite (mprot_ok_vm_intro (ms_vm s) (Z_to_bv 64 p) (page_round_up PZ) B SZ) in Hnok; [discriminate | exact NWM | exact NW | exact Vpw | exact HinB | rewrite uZ by lia; lia | rewrite pru_PZ, !uZ by lia; lia |].
        rewrite pru_PZ, uZ by lia. destruct Hpreg as (_ & Pb & _ & _ & Pl). rewrite Pl. lia. }
      split; [apply II_errno; exact HII|]. split; [| split; [exact HGS | split; [| split; [exact Hsp0 | split; [exact Hareas | split; [| split; [exact Hxm | exact Hdom2]]]]]]].
      + apply (FR_trans A0 s0 A s); [exact HFR | apply FR_errno; exact HW].
      + apply (AMvm_of_AMK k); [| lia]. replace k with (k + 0) by lia.
        apply (AMK_trans k 0 A0 A A s0 s); [exact HAMK | apply AMK_vm; [reflexivity | auto | lia] | exact Hareas].
      + intros HWk Hb. destruct HWf as [HWf | HWf]; [exact (HWf HWk)|].
        destruct Hcovp as (B & SZ & HinB & B1 & B2).
        rewrite (mprot_ok_vm_intro (ms_vm s) (Z_to_bv 64 p) (page_round_up PZ) B SZ) in HWf; [discriminate | exact NWM | exact NW | exact Vpw | exact HinB | rewrite uZ by lia; lia | rewrite pru_PZ, !uZ by lia; lia |].
        rewrite pru_PZ, uZ by lia. exact (Hbud Hb).
    - (* [comment removed for export] *)
      intros HWs Hmp. cbv beta. unfold is0 at 1. rewrite w0_eq, c_eq_Z by lia. cbn [Z.eqb].
      apply tw_bind_ret. cbn [negb]. rewrite pru_PZ.
      pose proof (mprotect_page_state sp0 argv envp cb A s (Z_to_bv 64 p) HI HVc ltac:(rewrite uZ by lia; exact Hnap) ltac:(rewrite uZ by lia; lia))
        as (HI' & HVc' & Emaps & Ena & Hcov' & Hlo & Himg & NODOM & ZIN & ZOUT).
      rewrite !uZ in * by lia.
      set (n := Z_to_bv 64 4096) in *. set (m' := zfill (Z_to_bv 64 p) n (ms_mem s)) in *. set (h' := vm_unprotect (Z_to_bv 64 p) n (ms_vm s)) in *.
      assert (En : u n = 4096) by (unfold n; apply uZ; lia).
      apply (commit_leafX k A (upd s m' h') p); cbn [ms_mem ms_vm upd]; try assumption.
      + split; [lia|]. split; [lia|]. split; [lia | exact Himg].
      + intros x Hx. rewrite <- (uZ x) in Hx by lia. exact (ZIN (Z_to_bv 64 x) Hx).
      + rewrite Ena. apply (maps_subtract_free_self _ _ _ _ _ NW); rewrite ?uZ by lia; lia.
      + destruct Vb as [H0 | [H1 | H2]]; [exfalso; exact (Hbrk H0) | left; exact H1 | right; exact H2].
      + intros Hgt. split; [unfold aac in *; lia|]. split.
        * rewrite Emaps. apply (map_contains_sub _ _ _ _ _ R3); rewrite !uZ by lia; unfold aac in *; lia.
        * rewrite Ena. apply (proj2 (map_contains_mcov _ _ _)). rewrite !uZ by (unfold aac in *; lia).
          apply (maps_subtract_cover _ _ _ _ _ NW); [| unfold aac in *; lia | lia].
          apply (mcov_sub _ (u (Z_to_bv 64 p)) (u (Z_to_bv 64 (4096 * aac)))); [apply map_contains_mcov; exact R4 | rewrite uZ by lia; lia | rewrite !uZ by lia; unfold aac in *; lia].
      + pose proof (proj2 Vspan). unfold h'. cbn. rewrite Hareas in *. lia.
      + (* [comment removed for export] *)
        eapply FRH_mono.
        * apply (FRH_extend (fun _ => False) (fun x => p <= x < p + 4096) A0 s0 A s A (upd s m' h')); cbn [ms_mem ms_vm ms_lo ms_hi upd].
          -- apply FRH_of_FR. exact HFR.
          -- exact HW.
          -- reflexivity.
          -- reflexivity.
          -- reflexivity.
          -- auto.
          -- reflexivity.
          -- intros a. pose proof (u64_range a).
             assert (CASE : p <= u a < p + 4096 \/ ~ (p <= u a < p + 4096)) by lia.
             destruct CASE as [IN | NI]; [right; right; right; split; [exact IN | apply NODOM; exact IN] | left; apply ZOUT; exact NI].
          -- intros a Ha. pose proof (u64_range a). assert (CASE : p <= u a < p + 4096 \/ ~ (p <= u a < p + 4096)) by lia.
             destruct CASE as [IN | NI]; [rewrite (ZIN a IN); discriminate | rewrite (ZOUT a NI); exact Ha].
        * intros x [F | Hx]; [destruct F | exact Hx].
      + (* [comment removed for export] *)
        intros HWk Har0. destruct (Hpre HWk Har0) as (Pm & Pb & Pi & Pr & Pl). unfold am_delta, h'.
        cbn [vm_maps vm_init_sp vm_reserved vm_limit vm_unprotect].
        split; [exact Pm|]. split; [| split; [exact Pi | split; [exact Pr | exact Pl]]].
        destruct Hcovp as (B0 & SZ0 & HinB & HB1 & HB2).
        pose proof (backed_unprotect_le (ms_vm s) (Z_to_bv 64 p) n B0 SZ0 NWM NW Vpw HinB ltac:(rewrite uZ by lia; lia) ltac:(rewrite uZ, En by lia; lia)) as BU.
        fold h' in BU. rewrite En in BU. unfold h' in BU. lia.
      + (* [comment removed for export] *)
        destruct Hpreg as (Pc & Pb & Pi & Pr & Pl). unfold am_grow, h'.
        cbn [vm_maps vm_init_sp vm_reserved vm_limit vm_unprotect].
        split; [exact Pc|]. split; [| split; [exact Pi | split; [exact Pr | exact Pl]]].
        destruct Hcovp as (B0 & SZ0 & HinB & HB1 & HB2).
        pose proof (backed_unprotect_le (ms_vm s) (Z_to_bv 64 p) n B0 SZ0 NWM NW Vpw HinB ltac:(rewrite uZ by lia; lia) ltac:(rewrite uZ, En by lia; lia)) as BU.
        fold h' in BU. rewrite En in BU. unfold h' in BU. lia.
      + (* [comment removed for export] *)
        apply (AMK_weaken (k + 0)); [| lia].
        apply (AMK_trans k 0 A0 A A s0 s); [exact HAMK | | exact Hareas].
        constructor; cbn [ms_vm upd].
        * rewrite Emaps. auto.
        * intros b sz Hin Hf. rewrite Ena. apply maps_subtract_free; [exact NW | exact Hf].
        * intros x Hx. left. exact Hx.
        * intros _. unfold vm_live_bytes. rewrite Emaps. lia.
  Qed.
End TailX.

End WithLayout.
