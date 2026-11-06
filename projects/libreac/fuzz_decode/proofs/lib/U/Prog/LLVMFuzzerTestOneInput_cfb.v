From Stdlib Require Import ZArith List Bool Lia Wf_nat.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.U.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.U.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.U.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.U.Reusable Require YK14 YO03.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.U Require Import Contract Img0 AllocSlots AllocRoom SlotAgree AgreeLift KindBGlue.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Lib Require Mem Frame MState Regs6ss Exec RegisterBridge.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.U.Prog Require Import LLVMFuzzerTestOneInput_c
  LLVMFuzzerTestOneInput_fr fd_segments_c.
Import ListNotations.
Local Open Scope Z_scope.

Definition llvm_room_cf (b : sbound) : Prop :=
  sb_live b <= 64 /\ 0 <= sb_bytes b <= 2 ^ 28 /\ 128 <= sb_cap b <= CAP_AG.

Lemma llvm_LIVE_BOUND_mono : forall c c' x x', 0 <= c' <= c -> x' <= x -> LIVE_BOUND c' x' <= LIVE_BOUND c x.
Proof.
  intros c c' x x' Hc Hx. unfold LIVE_BOUND, NA, AREA_BOUND, P2, HCAP.
  assert (D : (13 * c' + 48) / METAS_PER_AREA <= (13 * c + 48) / METAS_PER_AREA)
    by (apply Z.div_le_mono; unfold METAS_PER_AREA; lia).
  unfold YO03.MMAX, PGSZ in *. lia.
Qed.

Lemma CAP_AG_le : CAP_AG <= 1679.
Proof.
  destruct (Z_le_gt_dec CAP_AG 1679) as [H|H]; [exact H|].
  pose proof CAP_AG_fits as F. pose proof CAP_AG_max as M.
  pose proof (llvm_LIVE_BOUND_mono CAP_AG 1680 (2 ^ 29) (2 ^ 29) ltac:(lia) ltac:(lia)) as Mo. lia.
Qed.

Section RunCf.
Variable B : malloc_syms.
Hypothesis SEGS : ms_segs B = rsegs.

Lemma evt_SRcf_canon_r : forall ms (Q : machine_state -> Prop) md (P : config -> Prop),
  Exec.evt rsegs Q (RegisterBridge.canonical_register_state ms) -> m_halted md = None -> m_vm_lazy md = [] ->
  (forall ms', (exists can, Q can /\ Regs6ss.ms_eqv can ms') -> SRcf B (mkCfg ms' md) P) ->
  SRcf B (mkCfg ms md) P.
Proof. rewrite <- SEGS. exact (evt_SRcf_canon B). Qed.

Lemma llvm_run_norm_cf : forall (fx' : FPState) regs pc mem md (Q : machine_state -> Prop) (P : config -> Prop),
  m_halted md = None -> m_vm_lazy md = [] -> ro_agree rsegs mem ->
  Exec.evt rsegs Q (MState.MS (Regs6ss.mkR_of regs) (@fp_regs fx') pc (@fp_csr fx') None
                      (normalize rsegs mem) (seg_rom rsegs)) ->
  (forall ms, Q ms -> exists R F pc' fc m', ms = MState.MS R F pc' fc None m' (seg_rom rsegs)) ->
  (forall R F pc' fc m0', Q (MState.MS R F pc' fc None m0' (seg_rom rsegs)) ->
     forall regs' m', Regs6ss.xregs_eqv R regs' -> mem_rel rsegs m' m0' -> ro_same rsegs mem m' ->
     SRcf B (mkCfg (@mkst (mkFP F fc) regs' pc' m' (seg_rom rsegs)) md) P) ->
  SRcf B (mkCfg (@mkst fx' regs pc mem (seg_rom rsegs)) md) P.
Proof.
  intros fx' regs pc mem md Q P Hh Hl Hro HE Hform HK.
  apply (evt_SRcf_canon_r _ (fun s => exists s0, Q s0 /\ ms_rel rsegs s s0 /\ ro_same rsegs mem (ms_mem s)) md P);
    [| exact Hh | exact Hl |].
  - change (RegisterBridge.canonical_register_state (mkst regs pc mem (seg_rom rsegs)))
      with (MState.MS (Regs6ss.mkR_of regs) (@fp_regs fx') pc (@fp_csr fx') None mem (seg_rom rsegs)).
    apply evt_normalize; [exact lf_wx | exact Hro | exact HE].
  - intros ms' (can & (s0 & HQ & Hrel & Hsame) & Heq).
    destruct (Hform s0 HQ) as (R & F & pc' & fc & m0' & ->).
    destruct can as [cr cf cp cs cv cc cm co].
    destruct Hrel as (E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8).
    cbn [ms_regs ms_fregs ms_pc_val ms_svc_pending ms_resv ms_fcsr ms_mem ms_rom MState.MS] in *. subst.
    destruct (lf_eqv_mkst R F pc' fc cm (seg_rom rsegs) ms' Heq) as [Ems Hx]. rewrite Ems.
    exact (HK R F pc' fc m0' HQ _ cm Hx E8 Hsame).
Qed.

Lemma llvm_run_norm_cj_cf : forall (fx' : FPState) regs pc mem md (Q : machine_state -> Prop) (P : config -> Prop),
  m_halted md = None -> m_vm_lazy md = [] -> ro_agree rsegs mem ->
  Exec.evt rsegs Q (MState.MS (Regs6ss.mkR_of regs) (@fp_regs fx') pc (@fp_csr fx') None
                      (normalize_cj rsegs mem) (seg_rom rsegs)) ->
  (forall ms, Q ms -> exists R F pc' fc m', ms = MState.MS R F pc' fc None m' (seg_rom rsegs)) ->
  (forall R F pc' fc m0', Q (MState.MS R F pc' fc None m0' (seg_rom rsegs)) ->
     forall regs' m', Regs6ss.xregs_eqv R regs' -> mem_rel_cj rsegs m' m0' -> cj_same rsegs mem m' ->
     SRcf B (mkCfg (@mkst (mkFP F fc) regs' pc' m' (seg_rom rsegs)) md) P) ->
  SRcf B (mkCfg (@mkst fx' regs pc mem (seg_rom rsegs)) md) P.
Proof.
  intros fx' regs pc mem md Q P Hh Hl Hro HE Hform HK.
  apply (evt_SRcf_canon_r _ (fun s => exists s0, Q s0 /\ ms_rel_cj rsegs s s0 /\ cj_same rsegs mem (ms_mem s)) md P);
    [| exact Hh | exact Hl |].
  - change (RegisterBridge.canonical_register_state (mkst regs pc mem (seg_rom rsegs)))
      with (MState.MS (Regs6ss.mkR_of regs) (@fp_regs fx') pc (@fp_csr fx') None mem (seg_rom rsegs)).
    apply evt_normalize_cj; [exact lf_wx | exact Hro | exact HE].
  - intros ms' (can & (s0 & HQ & Hrel & Hsame) & Heq).
    destruct (Hform s0 HQ) as (R & F & pc' & fc & m0' & ->).
    destruct can as [cr cf cp cs cv cc cm co].
    destruct Hrel as (E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8).
    cbn [ms_regs ms_fregs ms_pc_val ms_svc_pending ms_resv ms_fcsr ms_mem ms_rom MState.MS] in *. subst.
    destruct (lf_eqv_mkst R F pc' fc cm (seg_rom rsegs) ms' Heq) as [Ems Hx]. rewrite Ems.
    exact (HK R F pc' fc m0' HQ _ cm Hx E8 Hsame).
Qed.

Lemma llvm_run_cf : forall (fx' : FPState) regs pc mem md (Q : machine_state -> Prop) (P : config -> Prop),
  m_halted md = None -> m_vm_lazy md = [] ->
  Exec.evt rsegs Q (MState.MS (Regs6ss.mkR_of regs) (@fp_regs fx') pc (@fp_csr fx') None mem (seg_rom rsegs)) ->
  (forall ms, Q ms -> exists R F pc' fc m', ms = MState.MS R F pc' fc None m' (seg_rom rsegs)) ->
  (forall R F pc' fc m', Q (MState.MS R F pc' fc None m' (seg_rom rsegs)) ->
     forall regs', Regs6ss.xregs_eqv R regs' ->
     SRcf B (mkCfg (@mkst (mkFP F fc) regs' pc' m' (seg_rom rsegs)) md) P) ->
  SRcf B (mkCfg (@mkst fx' regs pc mem (seg_rom rsegs)) md) P.
Proof.
  intros fx' regs pc mem md Q P Hh Hl HE Hform HK.
  apply (evt_SRcf_canon_r _ Q md P); [exact HE | exact Hh | exact Hl |].
  intros ms' (can & HQ & Heq). destruct (Hform can HQ) as (R & F & pc' & fc & m' & ->).
  destruct (lf_eqv_mkst R F pc' fc m' (seg_rom rsegs) ms' Heq) as [Ems Hx]. rewrite Ems.
  exact (HK R F pc' fc m' HQ _ Hx).
Qed.

Lemma SRcf_wf : forall (W : Type) (R : W -> W -> Prop),
  well_founded R ->
  forall (P : W -> config -> Prop) (Q : config -> Prop),
  (forall w c, P w c -> SRcf B c (fun c' => Q c' \/ exists w', R w' w /\ P w' c')) ->
  forall w c, P w c -> SRcf B c Q.
Proof.
  intros W R Hwf P Q Hbody w.
  induction (Hwf w) as [w _ IH].
  intros c HP. eapply (SRcf_bind B); [apply Hbody, HP|].
  intros c' [HQ | (w' & HR & HP')].
  - apply (SRcf_ret B), HQ.
  - apply (IH w' HR c' HP').
Qed.

Lemma SRcf_loop : forall (W : Type) (m : W -> nat)
  (P : W -> config -> Prop) (Q : config -> Prop),
  (forall w c, P w c -> SRcf B c (fun c' => Q c' \/ exists w', (m w' < m w)%nat /\ P w' c')) ->
  forall w c, P w c -> SRcf B c Q.
Proof.
  intros W m P Q Hbody.
  apply (SRcf_wf W (fun a b => (m a < m b)%nat)).
  - exact (well_founded_ltof W m).
  - exact Hbody.
Qed.

End RunCf.

Section KbCf.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Let segs := ms_segs B.

Lemma kb_run_cf : forall regs pc mem md (K : bvmap 5 word -> word -> (word -> option byte) -> Prop) (P : config -> Prop),
  m_halted md = None -> m_vm_lazy md = [] ->
  Exec.evt segs (fun ms => exists R pc' mem', ms = MState.MS R fp_regs pc' fp_csr None mem' (seg_rom segs) /\ K R pc' mem')
    (MState.MS (rmk regs) fp_regs pc fp_csr None mem (seg_rom segs)) ->
  (forall R pc' mem' regs', K R pc' mem' -> (forall r, getr regs' r = getr R r) ->
     SRcf B (mkCfg (mkst regs' pc' mem' (seg_rom segs)) md) P) ->
  SRcf B (mkCfg (mkst regs pc mem (seg_rom segs)) md) P.
Proof.
  intros regs pc mem md K P Hh Hl HE HK.
  eapply (evt_SRcf_canon B (mkst regs pc mem (seg_rom segs)) _ md P); [exact HE | exact Hh | exact Hl |].
  intros ms' (can & (R & pc' & mem' & -> & HKR) & Heq).
  destruct Heq as (HR & HF & Hpc & Hsvc & Hres & Hfc & Hm & Hrom).
  destruct ms' as [regs' fr' pcv' svc' rv' fc' m' ro'].
  cbn in HR, HF, Hpc, Hsvc, Hres, Hfc, Hm, Hrom. subst.
  apply (HK R _ _ regs' HKR). apply kb_getr_eqv. exact HR.
Qed.

End KbCf.

Definition room_ag (b : sbound) (n : Z) : Prop :=
  room_slots b n /\ 0 <= sb_cap b <= CAP_AG /\ sb_bytes b + n <= 2 ^ 29.

Lemma room_ag_gen : forall b n, sb_live b + 1 <= sb_cap b -> 128 <= sb_cap b <= CAP_AG ->
  0 <= sb_bytes b -> sb_bytes b + n <= 2 ^ 29 -> 0 <= n <= 2 ^ 22 -> room_ag b n.
Proof.
  intros b n Hl Hc Hb Hbn Hn. pose proof CAP_AG_le as Hle. split; [|split; lia].
  apply room_slots_small; unfold CAPMAX in *; lia.
Qed.

Lemma room_ag_big : forall b n, sb_live b + 1 <= sb_cap b -> 128 <= sb_cap b <= CAP_AG ->
  0 <= sb_bytes b -> sb_bytes b + n <= 2 ^ 29 -> 0 <= n <= 2 ^ 26 -> room_ag b n.
Proof.
  intros b n Hl Hc Hb Hbn Hn. pose proof CAP_AG_le as Hle. split; [|split; lia].
  apply room_slots_big; unfold CAPMAX in *; lia.
Qed.

Lemma lf_room_ag : forall b n, sb_live b <= 70 -> 0 <= sb_bytes b <= 2 ^ 28 + 2 ^ 27 -> 128 <= sb_cap b <= CAP_AG ->
  0 <= n <= 2 ^ 26 -> room_ag b n.
Proof. intros b n Hl Hb Hc Hn. apply room_ag_big; lia. Qed.

Section I.
Context {fx : YK11.FPState} {rc : YM05.RunCeil} {LS : lib_shape}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Context {SH : sink_head} {SK : sink_syms}.

Definition llvm_limlaw : Prop := forall L A mem md, aa_MR API L A mem md -> 2 ^ 34 <= vm_limit (m_vmmaps md).

Definition malloc_contract_ag : Prop :=
  forall L A regs mem md n b,
    call_pre B (aa_MR API) L A regs mem md -> ro_agree (ms_segs B) mem -> getr regs 10 = Z_to_bv 64 n ->
    res_ok_slots A b -> room_ag b n ->
    SRcf B (mkCfg (mkst regs (Z_to_bv 64 (ms_malloc B)) mem (seg_rom (ms_segs B))) md)
      (malloc_ret B API ALLOC_STACK L A regs mem md n b).

Lemma malloc_ag_of_cf : llvm_limlaw -> malloc_contract_cf B API -> malloc_contract_ag.
Proof.
  intros LIM MCF L A regs mem md n b Hpre Hro Hn HR (Hrs & Hc & Hbn).
  apply (MCF L A regs mem md n b Hpre Hro Hn HR).
  pose proof Hpre as (HM & _). exact (room_cf_of_limit md b n (LIM L A mem md HM) Hrs Hc Hbn).
Qed.

Definition calloc_contract_ag (pc : Z) : Prop :=
  forall L A regs mem md m n b,
    call_pre_k B (aa_MR API) CALLOC_STACK L A regs mem md -> ro_agree (ms_segs B) mem ->
    getr regs 10 = Z_to_bv 64 m -> getr regs 11 = Z_to_bv 64 n -> 0 <= m -> 0 <= n -> m * n < 4096 ->
    ms_calloc B = Some pc ->
    res_ok_slots A b -> room_ag b (m * n) ->
    SRcf B (mkCfg (mkst regs (Z_to_bv 64 pc) mem (seg_rom (ms_segs B))) md)
      (fun c' => malloc_ret B API CALLOC_STACK L A regs mem md (m * n) b c' /\
         exists ms' md', c' = mkCfg ms' md' /\
           forall i, 0 <= i < m * n ->
             mbyte (ms_segs B) (ms_mem ms') (bv_unsigned (getr (ms_regs ms') 10) + i) = Some (Z_to_bv 8 0)).

Lemma calloc_ag_of_cf : forall pc, llvm_limlaw -> calloc_contract_cf B API pc -> calloc_contract_ag pc.
Proof.
  intros pc LIM CCF L A regs mem md m n b Hpre Hro Hm Hn Hm0 Hn0 Hmn Hpc HR (Hrs & Hc & Hbn).
  apply (CCF L A regs mem md m n b Hpre Hro Hm Hn Hm0 Hn0 Hmn Hpc HR).
  pose proof Hpre as (HM & _). exact (room_cf_of_limit md b (m * n) (LIM L A mem md HM) Hrs Hc Hbn).
Qed.

Definition llvm_ls_laws_cf : Prop :=
  (forall pl fs (K : lleaf -> TSet), t_eq (LIBK pl fs K) (K (LL 0 fs []))) /\
  (forall b n, lib_room b n -> llvm_room_cf b) /\
  (forall n b, lib_delta n b = b).

Definition LLVMFuzzerTestOneInput_contract_cg : Prop :=
  llvm_binds B API -> llvm_ls_laws_cf ->
  forall j, (j < 4)%nat ->
  forall ra empty stk, LLVM_K <= stk -> YK0s.ret_ok (Z_to_bv 64 ra) ->
    lib_contract_cg B API llvm_G llvm_RELRO llvm_GI j LLVM_ENTRY ra empty stk.

Definition LLVMFuzzerTestOneInput_sr_contract_cf : Prop :=
  llvm_binds B API ->
  forall j, (j < 4)%nat ->
  forall ra empty stk, LLVM_K <= stk -> YK0s.ret_ok (Z_to_bv 64 ra) ->
  forall L A regs mem md p n pl b,
    lib_pre B API stk empty L A regs mem md ra p n ->
    n = Z.of_nat (length pl) -> blk_data B mem p pl ->
    sink_none B mem md -> spZ regs <= 2 ^ 47 ->
    res_ok_slots A b ->
    llvm_room_cf b ->
    ro_agree rsegs mem -> G_img_c B llvm_RELRO mem ->
    llvm_GI j mem ->
    frm_zero fp_csr ->
    SRcf B (mkCfg (mkst regs (Z_to_bv 64 LLVM_ENTRY) mem (seg_rom (ms_segs B))) md)
      (fun c' => exists (fx' : FPState) L' A' regs' mem' md',
         c' = mkCfg (@mkst fx' regs' (Z_to_bv 64 ra) mem' (seg_rom (ms_segs B))) md' /\
         frm_zero (@fp_csr fx') /\
         lib_post B API llvm_G stk L A regs mem md p L' A' regs' mem' md' /\
         sink_none B mem' md' /\
         res_ok_slots A' b /\
         (forall i, 0 <= i < n -> mbyte (ms_segs B) mem' (p + i) = mbyte (ms_segs B) mem (p + i)) /\
         ro_agree rsegs mem' /\
         llvm_GI (S j) mem').

End I.

Ltac segs_tac :=
  first [ assumption
        | (symmetry; assumption)
        | (match goal with BI : llvm_binds _ _ |- _ => exact (proj1 BI) end)
        | (match goal with E : fd_env _ _ |- _ => exact (proj1 (proj1 E)) end) ].
