From Stdlib Require Import ZArith List Bool Lia Wf_nat.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.U.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.U.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.U.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.U.Reusable Require YK14 YO03.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.U Require Import Contract Img0 AllocSlots AllocRoom SlotAgree AgreeLift.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Lib Require Mem Frame MState Regs6ss Exec RegisterBridge.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.U.Prog Require Import LLVMFuzzerTestOneInput_c
  LLVMFuzzerTestOneInput_fr LLVMFuzzerTestOneInput_inv.
Import ListNotations.
Local Open Scope Z_scope.

Definition llvm_room_cf (b : sbound) : Prop :=
  sb_live b <= 64 /\ 0 <= sb_bytes b <= 2 ^ 28 /\ 128 <= sb_cap b <= CAP_AG.

Definition llvm_bmax (b : sbound) : sbound := SB (sb_live b) (sb_bytes b) CAPMAX.

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

Lemma llvm_res_cap : forall A b c, res_ok_slots A b -> sb_cap b <= c ->
  res_ok_slots A (SB (sb_live b) (sb_bytes b) c).
Proof.
  intros A b c (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11) Hc.
  unfold res_ok_slots. cbn [sb_live sb_bytes sb_cap].
  refine (conj H1 (conj H2 (conj H3 (conj H4 (conj H5 (conj H6 (conj H7 (conj H8 (conj _ (conj H10 _)))))))))).
  - lia.
  - unfold HCAP in *. lia.
Qed.

Lemma llvm_room_bmax : forall A b, res_ok_slots A b -> llvm_room_cf b ->
  res_ok_slots A (llvm_bmax b) /\ llvm_room (llvm_bmax b).
Proof.
  intros A b HR (Hl & Hb & Hc). split.
  - apply llvm_res_cap; [exact HR | pose proof CAP_AG_le; unfold CAPMAX in *; lia].
  - unfold llvm_room, llvm_bmax. cbn [sb_live sb_bytes sb_cap]. lia.
Qed.

Lemma llvm_bmax_malloc : forall A b n, res_ok_slots A (sb_malloc b n) -> sb_cap b <= CAPMAX ->
  res_ok_slots A (sb_malloc (llvm_bmax b) n).
Proof.
  intros A b n HR Hc. unfold sb_malloc, llvm_bmax in *. cbn [sb_live sb_bytes sb_cap] in *.
  exact (llvm_res_cap A (SB (sb_live b + 1) (sb_bytes b + n) (sb_cap b)) CAPMAX HR Hc).
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

Definition room_ag (b : sbound) (n : Z) : Prop :=
  room_slots b n /\ 0 <= sb_cap b <= CAP_AG /\ sb_bytes b + n <= 2 ^ 29.

Lemma room_ag_gen : forall b n, sb_live b + 1 <= sb_cap b -> 0 <= sb_live b -> 128 <= sb_cap b <= CAP_AG ->
  0 <= sb_bytes b -> sb_bytes b + n <= 2 ^ 29 -> 0 <= n <= 2 ^ 22 -> room_ag b n.
Proof.
  intros b n Hl Hl0 Hc Hb Hbn Hn. pose proof CAP_AG_le as Hle. split; [|split; lia].
  apply room_slots_small; unfold CAPMAX in *; lia.
Qed.

Lemma lf_room0_ag : forall A b n, res_ok_slots A b -> llvm_room_cf b -> 0 <= n <= LLVM_REQ -> room_ag b n.
Proof.
  intros A b n HR (Hl & Hb & Hc) Hn.
  destruct HR as (_ & _ & _ & _ & _ & _ & _ & _ & Hlc & Hb0 & _).
  apply room_ag_gen; try assumption; unfold LLVM_REQ in *; lia.
Qed.

Lemma lf_room1_ag : forall A b n, res_ok_slots A b -> llvm_room_cf b -> 0 <= n <= LLVM_REQ ->
  room_ag (sb_malloc b LLVM_REQ) n.
Proof.
  intros A b n HR (Hl & Hb & Hc) Hn.
  destruct HR as (_ & _ & _ & _ & _ & _ & _ & _ & Hlc & Hb0 & _).
  apply room_ag_gen; unfold sb_malloc; cbn [sb_live sb_bytes sb_cap]; try assumption;
    unfold LLVM_REQ in *; lia.
Qed.

Section I.
Context {fx : YK11.FPState} {rc : YM05.RunCeil} {LS : lib_shape}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Context {SH : sink_head} {SK : sink_syms}.

Definition llvm_limlaw : Prop := forall L A mem md, aa_MR API L A mem md -> 2 ^ 34 <= vm_limit (m_vmmaps md).

Definition llvm_ctx_cf (stk empty : Z) (L0 : layout) (A0 : astate) (regs0 : bvmap 5 word)
    (mem0 : word -> option byte) (md0 : Model) (ra p n : Z) (b : sbound) : Prop :=
  llvm_binds B API /\ LLVM_K <= stk /\ YK0s.ret_ok (Z_to_bv 64 ra) /\
  lib_pre B API stk empty L0 A0 regs0 mem0 md0 ra p n /\ sink_none B mem0 md0 /\ spZ regs0 <= 2 ^ 47 /\
  res_ok_slots A0 b /\ llvm_room_cf b /\
  ro_agree rsegs mem0 /\ G_img_c B llvm_RELRO mem0 /\ frm_zero (@fp_csr fx) /\ n < 2 ^ 26.

Lemma llvm_ctx_of_cf : forall stk empty L0 A0 regs0 mem0 md0 ra p n b,
  llvm_ctx_cf stk empty L0 A0 regs0 mem0 md0 ra p n b ->
  llvm_ctx B API stk empty L0 A0 regs0 mem0 md0 ra p n (llvm_bmax b).
Proof.
  intros stk empty L0 A0 regs0 mem0 md0 ra p n b (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11 & H12).
  destruct (llvm_room_bmax A0 b H7 H8) as [R1 R2].
  exact (conj H1 (conj H2 (conj H3 (conj H4 (conj H5 (conj H6 (conj R1 (conj R2 (conj H9 (conj H10 (conj H11 H12))))))))))).
Qed.

Lemma llvm_ctx_cf_segs : forall stk empty L0 A0 regs0 mem0 md0 ra p n b,
  llvm_ctx_cf stk empty L0 A0 regs0 mem0 md0 ra p n b -> ms_segs B = rsegs.
Proof. intros stk empty L0 A0 regs0 mem0 md0 ra p n b ((H & _) & _). exact H. Qed.

Lemma llvm_payload_read_cf : forall stk empty L0 A0 regs0 mem0 md0 ra p n b L A mem md x,
  llvm_ctx_cf stk empty L0 A0 regs0 mem0 md0 ra p n b ->
  lf_fr B API stk (spZ regs0) L0 A0 mem0 md0 L A mem md -> p <= x < p + n ->
  exists v, ov_read_bytes rsegs mem (Z_to_bv 64 x) 1 = Some [v].
Proof.
  intros stk empty L0 A0 regs0 mem0 md0 ra p n b L A mem md x CTX FR Hx.
  exact (llvm_payload_read B API stk empty L0 A0 regs0 mem0 md0 ra p n (llvm_bmax b) L A mem md x
    (llvm_ctx_of_cf stk empty L0 A0 regs0 mem0 md0 ra p n b CTX) FR Hx).
Qed.

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

Definition llvm_top_ok_cf : Prop :=
  forall stk empty L0 A0 regs0 mem0 md0 ra p n b i k c,
    llvm_ctx_cf stk empty L0 A0 regs0 mem0 md0 ra p n b ->
    llvm_J B API stk L0 A0 regs0 mem0 md0 p n b i k c ->
    SRcf B c (llvm_T B API stk L0 A0 regs0 mem0 md0 p n b i k).

Definition llvm_case_ok_cf (op3 : Z) : Prop :=
  forall stk empty L0 A0 regs0 mem0 md0 ra p n b i k c,
    llvm_ctx_cf stk empty L0 A0 regs0 mem0 md0 ra p n b ->
    llvm_T B API stk L0 A0 regs0 mem0 md0 p n b i k c ->
    (exists ms md, c = mkCfg ms md /\ ms_pc_val ms = Z_to_bv 64 (llvm_case_pc op3)) ->
    SRcf B c (fun c' => exists k', llvm_K B API stk L0 A0 regs0 mem0 md0 p n b i k' c').

Definition llvm_join_ok_cf : Prop :=
  forall stk empty L0 A0 regs0 mem0 md0 ra p n b i k c,
    llvm_ctx_cf stk empty L0 A0 regs0 mem0 md0 ra p n b ->
    llvm_K B API stk L0 A0 regs0 mem0 md0 p n b i k c ->
    SRcf B c (fun c' => llvm_J B API stk L0 A0 regs0 mem0 md0 p n b (i + 1) k c' \/
                        llvm_X B API stk L0 A0 regs0 mem0 md0 b k c').

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
  forall L A regs mem md p n b,
    lib_pre B API stk empty L A regs mem md ra p n ->
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
        | (eapply llvm_ctx_cf_segs; eassumption)
        | (match goal with BI : llvm_binds _ _ |- _ => exact (proj1 BI) end) ].
