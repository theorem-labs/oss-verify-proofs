From Stdlib Require Import ZArith List Lia Bool FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.LinuxProcessSem Require Import StackLayout Fs Monad Specs.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.U.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.U.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.U.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.U Require Import Contract FrameAPI Img0.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Lib Require Import Mem Cells Frame Step.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Lib Require PropExec Exec Regs6ss MState.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.U.Prog Require Import LLVMFuzzerTestOneInput_c GrantSlotPlan SlotBridge SlotGlueStep SlotImg SlotGlue.
Import ListNotations.
Open Scope Z_scope.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.U Require Import SlotAgree AgreeLift.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.U.Prog Require Import GrantSlotPlanCf.

(* Cut-free twins of the SlotGlue allocator glue segments: the allocator calls go through
   malloc_contract_cf / free_contract_cf, so each segment ends in SRcf instead of SR. *)

Section CfG.
Context {fx : YK11.FPState} {rc : YM05.RunCeil} {LS : lib_shape}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Context {SH : sink_head} {SK : sink_syms}.
Hypothesis HMC : malloc_contract_cf B API.
Hypothesis HFC : free_contract_cf B API.

Local Abbreviation call_post_k_regs := (SlotGlue.call_post_k_regs B API).
Local Abbreviation cs_after := (SlotGlue.cs_after B API).
Local Abbreviation call_pre_after_jal := (SlotGlue.call_pre_after_jal B API).
Local Abbreviation frame_kept := (SlotGlue.frame_kept B API).
Local Abbreviation stack_kept := (SlotGlue.stack_kept B API).
Local Abbreviation row_kept := (SlotGlue.row_kept B API).
Local Abbreviation block_kept := (SlotGlue.block_kept B API).
Local Abbreviation payload_kept := (SlotGlue.payload_kept B API).
Local Abbreviation new_block_cells := (SlotGlue.new_block_cells B API).
Local Abbreviation new_block_apart := (SlotGlue.new_block_apart B API).
Local Abbreviation payload_after_malloc := (SlotGlue.payload_after_malloc B API).
Local Abbreviation blk_after_malloc := (SlotGlue.blk_after_malloc B API).
Local Abbreviation live_after := (SlotGlue.live_after B API).
Local Abbreviation live_after_free := (SlotGlue.live_after_free B API).
Local Abbreviation payload_after_free := (SlotGlue.payload_after_free B API).
Local Abbreviation freed_low := (SlotGlue.freed_low B API).
Local Abbreviation freed_noimg := (SlotGlue.freed_noimg B API).

Lemma malloc_core_cf : forall s s0 md L A b n ret (P : config -> Prop),
  unit_binding B -> ms_rel rsegs s s0 ->
  MemNorm.ro_agree (ms_segs B) (ms_mem s) -> ms_fregs s = fp_regs -> ms_fcsr s = fp_csr ->
  alloc_state B API L A (ms_mem s) md b -> errno_wr B (ms_mem s) -> room_cf md b n ->
  Exec.evt rsegs (jal_post s0 MALLOC_PC ret (w64 n)) s0 -> YK0s.ret_ok (Z_to_bv 64 ret) ->
  ms_rom s0 = seg_rom rsegs -> rg s0 4 = w64 (ms_tp B) -> sp_ok s0 ->
  (forall L' A' regs' mem' md' res,
     call_post_k B (aa_MR API) ALLOC_STACK L A (ms_regs s) (ms_mem s) md (fun _ => False) L' A' regs' mem' md' ->
     YK11.getr regs' (Z_to_bv 5 10) = Z_to_bv 64 res -> res mod 16 = 0 -> fresh_block B res n ->
     (exists b1 b2, blocks L' A' = b1 ++ (res, n) :: b2 /\ blocks L A = b1 ++ b2) ->
     blocks_kept B L A (ms_mem s) mem' (fun _ => False) -> ro_agree rsegs mem' -> guard_kept B (ms_mem s) mem' ->
     (forall q k, In (q, k) (user_blocks A) -> In (q, k) (user_blocks A')) -> st_init_done A' = true ->
     res_ok_slots A' (sb_malloc b n) ->
     P (mkCfg (YK11.mkst regs' (Z_to_bv 64 ret) mem' (seg_rom rsegs)) md')) ->
  SRcf B (mkCfg s md) P.
Proof.
  intros s s0 md L A b n ret P HUB HR Hro Hfr Hfc (HMR & HWF & Hbd & Hinit & Hres) Herr Hroom
    HJ0 Hret Hrom0 Htp Hsp K.
  pose proof HUB as (Hseg & Hmal & Hfre).
  destruct (mr_model B _ (aa_laws API) L A (ms_mem s) md HMR) as (Hh & Hl & _).
  pose proof (evt_rel rsegs _ s s0 wx_apart_rsegs HR HJ0) as HE.
  apply (evt_SRcf B s _ md P (eq_rect_r (fun g => Exec.evt g _ s) HE Hseg) Hh Hl).
  intros s1 (s1' & HJ & HR1 & Hrs).
  pose proof (state_after_jal s s0 s1 s1' _ _ _ HR HR1 HJ Hrs Hfr Hfc Hrom0) as Es1.
  assert (Em : ms_mem s1 = ms_mem s) by (rewrite Es1; reflexivity).
  destruct (regs_after_jal s s0 s1 s1' _ _ _ HR HR1 HJ) as [G Hcs].
  pose proof (call_pre_after_jal s s0 s1 s1' _ _ _ L A md HUB HR HR1 HJ Em HMR HWF Hbd Hinit Herr Hret Htp Hsp) as Hpre.
  rewrite Es1.
  pose proof (HMC L A (ms_regs s1) (ms_mem s) md n b) as HM.
  rewrite Hseg, Hmal in HM.
  eapply (SRcf_mono B); [apply HM | ].
  - exact Hpre.
  - rewrite <- Hseg. exact Hro.
  - change (YK11.getr (ms_regs s1) 10%bv) with (YK11.getr (ms_regs s1) (Z_to_bv 5 10)). rewrite G.
    destruct HJ as (_ & _ & _ & _ & _ & _ & _ & J10 & _). exact J10.
  - exact Hres.
  - exact Hroom.
  - intros c' (L' & A' & regs' & mem' & md' & res & Ec' & HCP & Hr10 & _ & H16 & Hfresh & Hsplit & Hkept &
                 Hro' & Hguard & Hub & Hinit' & _ & Hslots).
    assert (Hra : YK11.getr (ms_regs s1) 1%bv = Z_to_bv 64 ret).
    { change (YK11.getr (ms_regs s1) 1%bv) with (YK11.getr (ms_regs s1) (Z_to_bv 5 1)). rewrite G.
      destruct HJ as (_ & J1 & _). exact J1. }
    rewrite Ec', Hra. rewrite ?Hseg. rewrite ?Hseg in Hro'.
    apply (K L' A' regs' mem' md' res); try assumption.
    apply (call_post_k_regs ALLOC_STACK L A (ms_regs s1) (ms_regs s)); [exact Hcs | exact HCP].
Qed.

Lemma free_core_cf : forall s s0 md L A b q n ret (P : config -> Prop),
  unit_binding B -> ms_rel rsegs s s0 ->
  MemNorm.ro_agree (ms_segs B) (ms_mem s) -> ms_fregs s = fp_regs -> ms_fcsr s = fp_csr ->
  alloc_state B API L A (ms_mem s) md b -> errno_wr B (ms_mem s) -> In (q, n) (user_blocks A) ->
  Exec.evt rsegs (jal_post s0 FREE_PC ret (w64 (ptr_addr L q))) s0 -> YK0s.ret_ok (Z_to_bv 64 ret) ->
  ms_rom s0 = seg_rom rsegs -> rg s0 4 = w64 (ms_tp B) -> sp_ok s0 ->
  (forall L' A' regs' mem' md',
     call_post_k B (aa_MR API) ALLOC_STACK L A (ms_regs s) (ms_mem s) md
       (fun a => ptr_addr L q <= a < ptr_addr L q + n) L' A' regs' mem' md' ->
     (exists b1 b2, blocks L A = b1 ++ (ptr_addr L q, n) :: b2 /\ blocks L' A' = b1 ++ b2) ->
     blocks_kept B L A (ms_mem s) mem' (fun a => a = ptr_addr L q) -> ro_agree rsegs mem' -> guard_kept B (ms_mem s) mem' ->
     (forall q' k, In (q', k) (user_blocks A) -> q' <> q -> In (q', k) (user_blocks A')) ->
     st_init_done A' = true -> res_ok_slots A' (sb_free b n) ->
     P (mkCfg (YK11.mkst regs' (Z_to_bv 64 ret) mem' (seg_rom rsegs)) md')) ->
  SRcf B (mkCfg s md) P.
Proof.
  intros s s0 md L A b q n ret P HUB HR Hro Hfr Hfc (HMR & HWF & Hbd & Hinit & Hres) Herr Hq
    HJ0 Hret Hrom0 Htp Hsp K.
  pose proof HUB as (Hseg & Hmal & Hfre).
  destruct (mr_model B _ (aa_laws API) L A (ms_mem s) md HMR) as (Hh & Hl & _).
  pose proof (evt_rel rsegs _ s s0 wx_apart_rsegs HR HJ0) as HE.
  apply (evt_SRcf B s _ md P (eq_rect_r (fun g => Exec.evt g _ s) HE Hseg) Hh Hl).
  intros s1 (s1' & HJ & HR1 & Hrs).
  pose proof (state_after_jal s s0 s1 s1' _ _ _ HR HR1 HJ Hrs Hfr Hfc Hrom0) as Es1.
  assert (Em : ms_mem s1 = ms_mem s) by (rewrite Es1; reflexivity).
  destruct (regs_after_jal s s0 s1 s1' _ _ _ HR HR1 HJ) as [G Hcs].
  pose proof (call_pre_after_jal s s0 s1 s1' _ _ _ L A md HUB HR HR1 HJ Em HMR HWF Hbd Hinit Herr Hret Htp Hsp) as Hpre.
  rewrite Es1.
  pose proof (HFC L A (ms_regs s1) (ms_mem s) md q n b) as HM.
  rewrite Hseg, Hfre in HM.
  eapply (SRcf_mono B); [apply HM | ].
  - exact Hpre.
  - rewrite <- Hseg. exact Hro.
  - exact Hq.
  - change (YK11.getr (ms_regs s1) 10%bv) with (YK11.getr (ms_regs s1) (Z_to_bv 5 10)). rewrite G.
    destruct HJ as (_ & _ & _ & _ & _ & _ & _ & J10 & _). exact J10.
  - exact Hres.
  - intros c' (L' & A' & regs' & mem' & md' & Ec' & HCP & Hsplit & Hkept & Hro' & Hguard & Hub & Hinit' & _ & Hslots).
    assert (Hra : YK11.getr (ms_regs s1) 1%bv = Z_to_bv 64 ret).
    { change (YK11.getr (ms_regs s1) 1%bv) with (YK11.getr (ms_regs s1) (Z_to_bv 5 1)). rewrite G.
      destruct HJ as (_ & J1 & _). exact J1. }
    rewrite Ec', Hra. rewrite ?Hseg. rewrite ?Hseg in Hro'.
    apply (K L' A' regs' mem' md'); try assumption.
    + apply (call_post_k_regs ALLOC_STACK L A (ms_regs s1) (ms_regs s)); [exact Hcs|].
      apply call_post_k_alloc. exact HCP.
    + exact (Hinit' Hinit).
Qed.

Theorem seg_mallocT_cf_holds : seg_mallocT_cf B API.
Proof.
  unfold seg_mallocT_cf, malloc_glue_cf. intros x HS s md L A b Hpre _ Hroom.
  destruct Hpre as (HFA & HUB & Htp & (s0 & HP & HR) & Hro & Hfr & Hfc & Hal & Herr & Hpay & Herrlo & Hrow).
  pose proof HUB as (Hseg & _ & _).
  pose proof HFA as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Hbw & _ & _ & _ & HAX & _).
  pose proof Hal as (HMR & _).
  pose proof HP as HP0.
  destruct HP0 as (((Hpc0 & HF0 & Hfc0 & Hrv0 & Hsvc0 & Hro0 & Hgp0 & Htp0 & HPL0 & HST0 & HMI0 & Hp00 & Hpn0 & Hpd0 &
                     HRW0 & HRS0 & HRP0) & Hsp0 & HSV0 & HS160 & Hsv120 & HS630) &
                   Hn0 & Ha00 & (Hs10 & Hs90) & Hs200 & Hs190 & Hs180 & Hs210).
  pose proof HR as (HRr & HRf & _ & _ & _ & HRc & _ & HRm).
  apply (malloc_core_cf s s0 md L A b 460 PC_MALLOC_T_RET _ HUB HR Hro Hfr Hfc Hal Herr Hroom).
  - rewrite <- Ha00. apply jal_at_mallocT; assumption.
  - vm_compute. reflexivity.
  - exact Hro0.
  - rewrite Htp0, Htp. reflexivity.
  - exact (sp_ok_of_body x s0 Hsp0 HST0 HS160 HS630 HS).
  - intros L' A' regs' mem' md' res HCP Hr10 H16 Hfresh Hsplit Hkept Hro' Hguard Hub Hinit' Hslots.
    pose proof HCP as (HMR' & HWF' & Hbd' & _).
    assert (HEl : forall a, False -> a < alloc_ceiling) by tauto.
    assert (HEi : forall a, False -> ~ in_img B a) by tauto.
    destruct (payload_after_malloc x L A L' A' _ _ _ _ _ _ _ HCP Hub Hpay) as [Hpay' Hpayk].
    assert (CS := cs_after _ _ _ _ _ _ _ _ _ _ _ _ _ HR HCP).
    exists (YK11.mkst regs' (Z_to_bv 64 PC_MALLOC_T_RET) mem' (seg_rom rsegs)), md', L', A', res.
    split; [reflexivity|].
    split.
    2:{ split; [exact (live_after_malloc L A L' A' res 460 Hsplit)|].
        split; [exact HCP|]. split; [exact Hfresh|]. split; [exact H16|]. split; [exact Hsplit|].
        split; [exact Hkept|]. split; [exact Hguard|]. exact Hub. }
    unfold glue_post. cbn [ms_mem ms_fregs ms_fcsr YK11.mkst].
    split; [|split; [rewrite Hseg; exact Hro'|]].
    2:{ split; [reflexivity|]. split; [reflexivity|].
        split; [exact (conj HMR' (conj HWF' (conj Hbd' (conj Hinit' Hslots))))|].
        split; [|split; [exact Hpay' | exact I]].
        intros a Ha. destruct HCP as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Hscr). apply Hscr. unfold scratch_k. right. exact Ha. }
    exists (YK11.mkst regs' (Z_to_bv 64 PC_MALLOC_T_RET) (normalize rsegs mem') (seg_rom rsegs)).
    split.
    2:{ unfold ms_rel. cbn [ms_regs ms_fregs ms_pc_val ms_svc_pending ms_resv ms_fcsr ms_rom ms_mem YK11.mkst].
        repeat split; apply mem_rel_normalize; exact Hro'. }
    assert (HFx : fp_regs = x_F x) by (rewrite <- HF0, <- HRf, Hfr; reflexivity).
    assert (HCx : fp_csr = x_fc x) by (rewrite <- Hfc0, <- HRc, Hfc; reflexivity).
    assert (RG : forall k, rg (YK11.mkst regs' (Z_to_bv 64 PC_MALLOC_T_RET) (normalize rsegs mem') (seg_rom rsegs)) k =
                           YK11.getr regs' (Z_to_bv 5 k)) by (intros; reflexivity).
    assert (HSTk : stk rsegs (normalize rsegs mem') (x_S x - LLVM_STACK) (x_S x)) by (eapply stack_kept; eassumption).
    assert (HSVk : rw_cells rsegs (normalize rsegs mem') (x_S x - 104) (map C8 (rev (x_sv x) ++ [x_ra x]))).
    { eapply frame_kept; try eassumption; [lia | rewrite (SegSetModel.saved_size _ _ Hsv120); lia]. }
    assert (HRWk : bytes_at rsegs (normalize rsegs mem') CTRL_HEADAMP_ROW CTRL_HEADAMP_BYTES)
      by (eapply row_kept; eassumption).
    assert (HPLk : rw_cells rsegs (normalize rsegs mem') (x_p x) [CB (length (x_pl x)) (x_pl x)])
      by (eapply payload_kept; eassumption).
    destruct (live_after_malloc L A L' A' res 460 Hsplit) as (qn & Hqn & Hpqn).
    destruct (new_block_cells L' A' mem' md' qn res 460 Hseg HMR' Hro' Hqn Hpqn Hfresh ltac:(lia)) as (junk & Hjunk).
    pose proof (blk_after_malloc x L A L' A' mem' md' res 460 Hseg HMR' Hfresh ltac:(lia) Hsplit Hpay HS) as Hblk.
    unfold At_mallocT_ret, body, common, cur.
    cbn [ms_pc_val ms_fregs ms_fcsr ms_resv ms_svc_pending ms_rom ms_mem YK11.mkst].
    rewrite !RG. rewrite (CS 2), (CS 3), (CS 4), (CS 27), (CS 25), (CS 9), (CS 19), (CS 18), (CS 20)
      by (unfold callee_saved; lia).
    repeat match goal with |- _ /\ _ => split end.
    all: first [ reflexivity | assumption | exact Hr10 | apply mem_inv_normalize | lia | exists junk; exact Hjunk ].
Qed.

Theorem seg_mallocSW1_cf_holds : seg_mallocSW1_cf B API.
Proof.
  unfold seg_mallocSW1_cf, malloc_glue_cf. intros x t HS s md L A b Hpre Hlive Hroom.
  destruct Hpre as (HFA & HUB & Htp & (s0 & HP & HR) & Hro & Hfr & Hfc & Hal & Herr & Hpay & Herrlo & Hrow).
  pose proof HUB as (Hseg & _ & _).
  pose proof HFA as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Hbw & _ & _ & _ & HAX & _).
  pose proof Hal as (HMR & _).
  pose proof HP as HP0.
  destruct HP0 as ((((Hpc0 & HF0 & Hfc0 & Hrv0 & Hsvc0 & Hro0 & Hgp0 & Htp0 & HPL0 & HST0 & HMI0 & Hp00 & Hpn0 & Hpd0 &
                      HRW0 & HRS0 & HRP0) & Hsp0 & HSV0 & HS160 & Hsv120 & HS630) &
                    Hn0 & H80 & Hs90 & HSL0 & HCS0 & (HTb0 & HT160 & HTl0 & HT0) & (Hwl0 & Hstl0 & HWS0 & HSTA0) &
                    HHr0 & HI10) & Hok0 & Ha00 & (H210 & H250) & H180 & H190 & HC1980).
  unfold slots, cslot in HSL0, HCS0.
  pose proof HR as (HRr & HRf & _ & _ & _ & HRc & _ & HRm).
  assert (Hn1 : 0 < sw1_size x) by (unfold sw1_size; lia).
  apply (malloc_core_cf s s0 md L A b (sw1_size x) PC_MALLOC_SW1_RET _ HUB HR Hro Hfr Hfc Hal Herr Hroom).
  - rewrite <- Ha00. apply jal_at_mallocSW1; assumption.
  - vm_compute. reflexivity.
  - exact Hro0.
  - rewrite Htp0, Htp. reflexivity.
  - exact (sp_ok_of_body x s0 Hsp0 HST0 HS160 HS630 HS).
  - intros L' A' regs' mem' md' res HCP Hr10 H16 Hfresh Hsplit Hkept Hro' Hguard Hub Hinit' Hslots.
    pose proof HCP as (HMR' & HWF' & Hbd' & _).
    assert (HEl : forall a, False -> a < alloc_ceiling) by tauto.
    assert (HEi : forall a, False -> ~ in_img B a) by tauto.
    destruct (payload_after_malloc x L A L' A' _ _ _ _ _ _ _ HCP Hub Hpay) as [Hpay' Hpayk].
    destruct (live_after L A L' A' _ _ _ _ _ _ _ t 460 HCP Hlive (fun q Hq _ => Hub q 460 Hq)) as [Hlive' (qt & Hqt & Hqt' & Hpqt)].
    assert (CS := cs_after _ _ _ _ _ _ _ _ _ _ _ _ _ HR HCP).
    exists (YK11.mkst regs' (Z_to_bv 64 PC_MALLOC_SW1_RET) mem' (seg_rom rsegs)), md', L', A', res.
    split; [reflexivity|].
    split.
    2:{ split; [exact (live_after_malloc L A L' A' res (sw1_size x) Hsplit)|].
        split; [exact HCP|]. split; [exact Hfresh|]. split; [exact H16|]. split; [exact Hsplit|].
        split; [exact Hkept|]. split; [exact Hguard|]. exact Hub. }
    unfold glue_post. cbn [ms_mem ms_fregs ms_fcsr YK11.mkst].
    split; [|split; [rewrite Hseg; exact Hro'|]].
    2:{ split; [reflexivity|]. split; [reflexivity|].
        split; [exact (conj HMR' (conj HWF' (conj Hbd' (conj Hinit' Hslots))))|].
        split; [|split; [exact Hpay' | exact Hlive']].
        intros a Ha. destruct HCP as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Hscr). apply Hscr. unfold scratch_k. right. exact Ha. }
    exists (YK11.mkst regs' (Z_to_bv 64 PC_MALLOC_SW1_RET) (normalize rsegs mem') (seg_rom rsegs)).
    split.
    2:{ unfold ms_rel. cbn [ms_regs ms_fregs ms_pc_val ms_svc_pending ms_resv ms_fcsr ms_rom ms_mem YK11.mkst].
        repeat split; apply mem_rel_normalize; exact Hro'. }
    assert (HFx : fp_regs = x_F x) by (rewrite <- HF0, <- HRf, Hfr; reflexivity).
    assert (HCx : fp_csr = x_fc x) by (rewrite <- Hfc0, <- HRc, Hfc; reflexivity).
    assert (RG : forall k, rg (YK11.mkst regs' (Z_to_bv 64 PC_MALLOC_SW1_RET) (normalize rsegs mem') (seg_rom rsegs)) k =
                           YK11.getr regs' (Z_to_bv 5 k)) by (intros; reflexivity).
    assert (HSTk : stk rsegs (normalize rsegs mem') (x_S x - LLVM_STACK) (x_S x)) by (eapply stack_kept; eassumption).
    assert (HSVk : rw_cells rsegs (normalize rsegs mem') (x_S x - 104) (map C8 (rev (x_sv x) ++ [x_ra x]))).
    { eapply frame_kept; try eassumption; [lia | rewrite (SegSetModel.saved_size _ _ Hsv120); lia]. }
    assert (HRWk : bytes_at rsegs (normalize rsegs mem') CTRL_HEADAMP_ROW CTRL_HEADAMP_BYTES)
      by (eapply row_kept; eassumption).
    assert (HPLk : rw_cells rsegs (normalize rsegs mem') (x_p x) [CB (length (x_pl x)) (x_pl x)])
      by (eapply payload_kept; eassumption).
    assert (HSLk := HSL0). assert (HCSk := HCS0). assert (HWSk := HWS0). assert (HSTAk := HSTA0).
    assert (HC198k := HC1980).
    eapply frame_kept in HSLk; try eassumption; [| change (SPL x) with (x_S x - 608); lia | change (SPL x) with (x_S x - 608); cbn; lia].
    eapply frame_kept in HCSk; try eassumption; [| change (SPL x) with (x_S x - 608); lia | change (SPL x) with (x_S x - 608); cbn; lia].
    eapply frame_kept in HWSk; try eassumption; [| change (SPL x) with (x_S x - 608); lia | change (SPL x) with (x_S x - 608); cbn; lia].
    eapply frame_kept in HSTAk; try eassumption; [| change (SPL x) with (x_S x - 608); lia | change (SPL x) with (x_S x - 608); cbn; lia].
    eapply frame_kept in HC198k; try eassumption; [| change (SPL x) with (x_S x - 608); lia | change (SPL x) with (x_S x - 608); cbn; lia].
    assert (HTk : rw_cells rsegs (normalize rsegs mem') t [CB 460 (T_end (x_pl x))]).
    { rewrite <- Hpqt. eapply block_kept; try eassumption; [cbn; lia | rewrite Hpqt; exact HT0]. }
    destruct (live_after_malloc L A L' A' res _ Hsplit) as (qn & Hqn & Hpqn).
    destruct (new_block_cells L' A' mem' md' qn res (sw1_size x) Hseg HMR' Hro' Hqn Hpqn Hfresh ltac:(lia)) as (junk & Hjunk).
    pose proof (blk_after_malloc x L A L' A' mem' md' res (sw1_size x) Hseg HMR' Hfresh Hn1 Hsplit Hpay HS) as Hblk.
    assert (Htap : res + sw1_size x <= t \/ t + 460 <= res).
    { rewrite <- Hpqt. exact (new_block_apart L A L' A' mem' md' res _ _ _ HMR' Hsplit (in_blocks L A qt _ Hqt)). }
    unfold At_mallocSW1_ret, at_after_admit, body, common, cur5, slots, cslot, table, arrays.
    cbn [ms_pc_val ms_fregs ms_fcsr ms_resv ms_svc_pending ms_rom ms_mem YK11.mkst].
    rewrite !RG. rewrite (CS 2), (CS 3), (CS 4), (CS 8), (CS 25), (CS 21), (CS 19), (CS 18)
      by (unfold callee_saved; lia).
    repeat match goal with |- _ /\ _ => split end.
    all: first [ reflexivity | assumption | exact Hr10 | apply mem_inv_normalize | lia | exists junk; exact Hjunk ].
Qed.

Theorem seg_mallocSW2_cf_holds : seg_mallocSW2_cf B API.
Proof.
  unfold seg_mallocSW2_cf, malloc_glue_cf. intros x t HS s md L A b Hpre Hlive Hroom.
  destruct Hpre as (HFA & HUB & Htp & (s0 & HP & HR) & Hro & Hfr & Hfc & Hal & Herr & Hpay & Herrlo & Hrow).
  pose proof HUB as (Hseg & _ & _).
  pose proof HFA as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Hbw & _ & _ & _ & HAX & _).
  pose proof Hal as (HMR & _).
  unfold At_mallocSW2 in HP. unfold At_mallocSW2_ret. destruct (raw_rd (x_pl x)) as [[rb rw] prw].
  pose proof HP as HP0.
  destruct HP0 as (((Hpc0 & HF0 & Hfc0 & Hrv0 & Hsvc0 & Hro0 & Hgp0 & Htp0 & HPL0 & HST0 & HMI0 & Hp00 & Hpn0 & Hpd0 &
                     HRW0 & HRS0 & HRP0) & Hsp0 & HSV0 & HS160 & Hsv120 & HS630) &
                   Hn0 & H80 & (Hs10 & Hs90) & Ha00 & HC500 & (HTb0 & HT160 & HTl0 & HT0) & (Hwl0 & Hstl0 & HWS0 & HSTA0) &
                   HHr0 & HI10).
  pose proof HR as (HRr & HRf & _ & _ & _ & HRc & _ & HRm).
  apply (malloc_core_cf s s0 md L A b 4352 PC_MALLOC_SW2_RET _ HUB HR Hro Hfr Hfc Hal Herr Hroom).
  - rewrite <- Ha00. apply jal_at_mallocSW2; assumption.
  - vm_compute. reflexivity.
  - exact Hro0.
  - rewrite Htp0, Htp. reflexivity.
  - exact (sp_ok_of_body x s0 Hsp0 HST0 HS160 HS630 HS).
  - intros L' A' regs' mem' md' res HCP Hr10 H16 Hfresh Hsplit Hkept Hro' Hguard Hub Hinit' Hslots.
    pose proof HCP as (HMR' & HWF' & Hbd' & _).
    assert (HEl : forall a, False -> a < alloc_ceiling) by tauto.
    assert (HEi : forall a, False -> ~ in_img B a) by tauto.
    destruct (payload_after_malloc x L A L' A' _ _ _ _ _ _ _ HCP Hub Hpay) as [Hpay' Hpayk].
    destruct (live_after L A L' A' _ _ _ _ _ _ _ t 460 HCP Hlive (fun q Hq _ => Hub q 460 Hq)) as [Hlive' (qt & Hqt & Hqt' & Hpqt)].
    assert (CS := cs_after _ _ _ _ _ _ _ _ _ _ _ _ _ HR HCP).
    exists (YK11.mkst regs' (Z_to_bv 64 PC_MALLOC_SW2_RET) mem' (seg_rom rsegs)), md', L', A', res.
    split; [reflexivity|].
    split.
    2:{ split; [exact (live_after_malloc L A L' A' res 4352 Hsplit)|].
        split; [exact HCP|]. split; [exact Hfresh|]. split; [exact H16|]. split; [exact Hsplit|].
        split; [exact Hkept|]. split; [exact Hguard|]. exact Hub. }
    unfold glue_post. cbn [ms_mem ms_fregs ms_fcsr YK11.mkst].
    split; [|split; [rewrite Hseg; exact Hro'|]].
    2:{ split; [reflexivity|]. split; [reflexivity|].
        split; [exact (conj HMR' (conj HWF' (conj Hbd' (conj Hinit' Hslots))))|].
        split; [|split; [exact Hpay' | exact Hlive']].
        intros a Ha. destruct HCP as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Hscr). apply Hscr. unfold scratch_k. right. exact Ha. }
    exists (YK11.mkst regs' (Z_to_bv 64 PC_MALLOC_SW2_RET) (normalize rsegs mem') (seg_rom rsegs)).
    split.
    2:{ unfold ms_rel. cbn [ms_regs ms_fregs ms_pc_val ms_svc_pending ms_resv ms_fcsr ms_rom ms_mem YK11.mkst].
        repeat split; apply mem_rel_normalize; exact Hro'. }
    assert (HFx : fp_regs = x_F x) by (rewrite <- HF0, <- HRf, Hfr; reflexivity).
    assert (HCx : fp_csr = x_fc x) by (rewrite <- Hfc0, <- HRc, Hfc; reflexivity).
    assert (RG : forall k, rg (YK11.mkst regs' (Z_to_bv 64 PC_MALLOC_SW2_RET) (normalize rsegs mem') (seg_rom rsegs)) k =
                           YK11.getr regs' (Z_to_bv 5 k)) by (intros; reflexivity).
    assert (HSTk : stk rsegs (normalize rsegs mem') (x_S x - LLVM_STACK) (x_S x)) by (eapply stack_kept; eassumption).
    assert (HSVk : rw_cells rsegs (normalize rsegs mem') (x_S x - 104) (map C8 (rev (x_sv x) ++ [x_ra x]))).
    { eapply frame_kept; try eassumption; [lia | rewrite (SegSetModel.saved_size _ _ Hsv120); lia]. }
    assert (HRWk : bytes_at rsegs (normalize rsegs mem') CTRL_HEADAMP_ROW CTRL_HEADAMP_BYTES)
      by (eapply row_kept; eassumption).
    assert (HPLk : rw_cells rsegs (normalize rsegs mem') (x_p x) [CB (length (x_pl x)) (x_pl x)])
      by (eapply payload_kept; eassumption).
    assert (HWSk := HWS0). assert (HSTAk := HSTA0). assert (HC50k := HC500).
    eapply frame_kept in HWSk; try eassumption; [| change (SPL x) with (x_S x - 608); lia | change (SPL x) with (x_S x - 608); cbn; lia].
    eapply frame_kept in HSTAk; try eassumption; [| change (SPL x) with (x_S x - 608); lia | change (SPL x) with (x_S x - 608); cbn; lia].
    eapply frame_kept in HC50k; try eassumption; [| change (SPL x) with (x_S x - 608); lia | change (SPL x) with (x_S x - 608); cbn; lia].
    assert (HTk : rw_cells rsegs (normalize rsegs mem') t [CB 460 (T_end (x_pl x))]).
    { rewrite <- Hpqt. eapply block_kept; try eassumption; [cbn; lia | rewrite Hpqt; exact HT0]. }
    destruct (live_after_malloc L A L' A' res _ Hsplit) as (qn & Hqn & Hpqn).
    destruct (new_block_cells L' A' mem' md' qn res 4352 Hseg HMR' Hro' Hqn Hpqn Hfresh ltac:(lia)) as (junk & Hjunk).
    pose proof (blk_after_malloc x L A L' A' mem' md' res 4352 Hseg HMR' Hfresh ltac:(lia) Hsplit Hpay HS) as Hblk.
    assert (Htap : res + 4352 <= t \/ t + 460 <= res).
    { rewrite <- Hpqt. exact (new_block_apart L A L' A' mem' md' res _ _ _ HMR' Hsplit (in_blocks L A qt _ Hqt)). }
    unfold body, common, cur5, table, arrays.
    cbn [ms_pc_val ms_fregs ms_fcsr ms_resv ms_svc_pending ms_rom ms_mem YK11.mkst].
    rewrite !RG. rewrite (CS 2), (CS 3), (CS 4), (CS 8), (CS 21), (CS 25) by (unfold callee_saved; lia).
    repeat match goal with |- _ /\ _ => split end.
    all: first [ reflexivity | assumption | exact Hr10 | apply mem_inv_normalize | lia | exists junk; exact Hjunk ].
Qed.

Theorem seg_freeT_cf_holds : seg_freeT_cf B API.
Proof.
  unfold seg_freeT_cf, free_glue_cf. intros x t HS s md L A b q Hpre _ Hq Hpq.
  destruct Hpre as (HFA & HUB & Htp & (s0 & HP & HR) & Hro & Hfr & Hfc & Hal & Herr & Hpay & Herrlo & Hrow).
  pose proof HUB as (Hseg & _ & _).
  pose proof HFA as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Hbw & _ & _ & _ & HAX & _).
  pose proof Hal as (HMR & _).
  pose proof HP as HP0.
  destruct HP0 as (((Hpc0 & HF0 & Hfc0 & Hrv0 & Hsvc0 & Hro0 & Hgp0 & Htp0 & HPL0 & HST0 & HMI0 & Hp00 & Hpn0 & Hpd0 &
                     HRW0 & HRS0 & HRP0) & Hsp0 & HSV0 & HS160 & Hsv120 & HS630) &
                   Hn0 & H80 & Hblkt & Ht16).
  pose proof HR as (HRr & HRf & _ & _ & _ & HRc & _ & HRm).
  apply (free_core_cf s s0 md L A b q 460 PC_FREE_T_RET _ HUB HR Hro Hfr Hfc Hal Herr Hq).
  - rewrite Hpq, <- H80. apply jal_at_freeT; assumption.
  - vm_compute. reflexivity.
  - exact Hro0.
  - rewrite Htp0, Htp. reflexivity.
  - exact (sp_ok_of_body x s0 Hsp0 HST0 HS160 HS630 HS).
  - intros L' A' regs' mem' md' HCP Hsplit Hkept Hro' Hguard Hub Hinit' Hslots.
    pose proof HCP as (HMR' & HWF' & Hbd' & _).
    assert (HEl : forall a, ptr_addr L q <= a < ptr_addr L q + 460 -> a < alloc_ceiling)
      by (intros a Ha; exact (freed_low L A _ md q 460 a HMR Hq Ha)).
    assert (HEi : forall a, ptr_addr L q <= a < ptr_addr L q + 460 -> ~ in_img B a)
      by (intros a Ha; exact (freed_noimg L A _ md q 460 a HAX HMR Hq Ha)).
    pose proof Hblkt as (_ & _ & _ & Htpay & _).
    destruct (payload_after_free x L A L' A' _ _ _ _ _ _ _ q 460 HCP Hub ltac:(lia) ltac:(rewrite Hpq; exact Htpay) Hpay)
      as [Hpay' Hpayk].
    assert (CS := cs_after _ _ _ _ _ _ _ _ _ _ _ _ _ HR HCP).
    exists (YK11.mkst regs' (Z_to_bv 64 PC_FREE_T_RET) mem' (seg_rom rsegs)), md', L', A'.
    split; [reflexivity|].
    split.
    2:{ rewrite <- Hpq. split; [apply call_post_k_alloc; exact HCP|].
        split; [exact Hsplit|]. split; [exact Hkept|]. split; [exact Hguard|]. exact Hub. }
    unfold glue_post. cbn [ms_mem ms_fregs ms_fcsr YK11.mkst].
    split; [|split; [rewrite Hseg; exact Hro'|]].
    2:{ split; [reflexivity|]. split; [reflexivity|].
        split; [exact (conj HMR' (conj HWF' (conj Hbd' (conj Hinit' Hslots))))|].
        split; [|split; [exact Hpay' | exact I]].
        intros a Ha. destruct HCP as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Hscr). apply Hscr. unfold scratch_k. right. exact Ha. }
    exists (YK11.mkst regs' (Z_to_bv 64 PC_FREE_T_RET) (normalize rsegs mem') (seg_rom rsegs)).
    split.
    2:{ unfold ms_rel. cbn [ms_regs ms_fregs ms_pc_val ms_svc_pending ms_resv ms_fcsr ms_rom ms_mem YK11.mkst].
        repeat split; apply mem_rel_normalize; exact Hro'. }
    assert (HFx : fp_regs = x_F x) by (rewrite <- HF0, <- HRf, Hfr; reflexivity).
    assert (HCx : fp_csr = x_fc x) by (rewrite <- Hfc0, <- HRc, Hfc; reflexivity).
    assert (RG : forall k, rg (YK11.mkst regs' (Z_to_bv 64 PC_FREE_T_RET) (normalize rsegs mem') (seg_rom rsegs)) k =
                           YK11.getr regs' (Z_to_bv 5 k)) by (intros; reflexivity).
    assert (HSTk : stk rsegs (normalize rsegs mem') (x_S x - LLVM_STACK) (x_S x)) by (eapply stack_kept; eassumption).
    assert (HSVk : rw_cells rsegs (normalize rsegs mem') (x_S x - 104) (map C8 (rev (x_sv x) ++ [x_ra x]))).
    { eapply frame_kept; try eassumption; [lia | rewrite (SegSetModel.saved_size _ _ Hsv120); lia]. }
    assert (HRWk : bytes_at rsegs (normalize rsegs mem') CTRL_HEADAMP_ROW CTRL_HEADAMP_BYTES)
      by (eapply row_kept; eassumption).
    assert (HPLk : rw_cells rsegs (normalize rsegs mem') (x_p x) [CB (length (x_pl x)) (x_pl x)])
      by (eapply payload_kept; eassumption).
    unfold At_ret0. right. unfold body, common.
    cbn [ms_pc_val ms_fregs ms_fcsr ms_resv ms_svc_pending ms_rom ms_mem YK11.mkst].
    rewrite !RG. rewrite (CS 2), (CS 3), (CS 4) by (unfold callee_saved; lia).
    repeat match goal with |- _ /\ _ => split end.
    all: first [ reflexivity | assumption | apply mem_inv_normalize | lia ].
Qed.

Theorem seg_freeSW1_cf_holds : seg_freeSW1_cf B API.
Proof.
  unfold seg_freeSW1_cf, free_glue_cf. intros x t sw HS s md L A b q Hpre Hlive Hq Hpq.
  destruct Hpre as (HFA & HUB & Htp & (s0 & HP & HR) & Hro & Hfr & Hfc & Hal & Herr & Hpay & Herrlo & Hrow).
  pose proof HUB as (Hseg & _ & _).
  pose proof HFA as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Hbw & _ & _ & _ & HAX & _).
  pose proof Hal as (HMR & _).
  pose proof HP as HP0.
  destruct HP0 as ((((Hpc0 & HF0 & Hfc0 & Hrv0 & Hsvc0 & Hro0 & Hgp0 & Htp0 & HPL0 & HST0 & HMI0 & Hp00 & Hpn0 & Hpd0 &
                      HRW0 & HRS0 & HRP0) & Hsp0 & HSV0 & HS160 & Hsv120 & HS630) &
                    Hn0 & H80 & Hs90 & HSL0 & HCS0 & (HTb0 & HT160 & HTl0 & HT0) & (Hwl0 & Hstl0 & HWS0 & HSTA0) &
                    HHr0 & HI10) & Hok0 & Ha00 & H190 & Hblks).
  unfold slots, cslot in HSL0, HCS0.
  pose proof HR as (HRr & HRf & _ & _ & _ & HRc & _ & HRm).
  assert (Hn1 : 0 < sw1_size x) by (unfold sw1_size; lia).
  assert (Hn460 : sw1_size x <> 460) by (unfold sw1_size; lia).
  apply (free_core_cf s s0 md L A b q (sw1_size x) PC_FREE_SW1_RET _ HUB HR Hro Hfr Hfc Hal Herr Hq).
  - rewrite Hpq, <- Ha00. apply jal_at_freeSW1; assumption.
  - vm_compute. reflexivity.
  - exact Hro0.
  - rewrite Htp0, Htp. reflexivity.
  - exact (sp_ok_of_body x s0 Hsp0 HST0 HS160 HS630 HS).
  - intros L' A' regs' mem' md' HCP Hsplit Hkept Hro' Hguard Hub Hinit' Hslots.
    pose proof HCP as (HMR' & HWF' & Hbd' & _).
    assert (HEl : forall a, ptr_addr L q <= a < ptr_addr L q + sw1_size x -> a < alloc_ceiling)
      by (intros a Ha; exact (freed_low L A _ md q _ a HMR Hq Ha)).
    assert (HEi : forall a, ptr_addr L q <= a < ptr_addr L q + sw1_size x -> ~ in_img B a)
      by (intros a Ha; exact (freed_noimg L A _ md q _ a HAX HMR Hq Ha)).
    pose proof Hblks as (_ & _ & _ & Hspay & _).
    destruct (payload_after_free x L A L' A' _ _ _ _ _ _ _ q _ HCP Hub Hn1 ltac:(rewrite Hpq; exact Hspay) Hpay)
      as [Hpay' Hpayk].
    destruct (live_after_free L A L' A' _ _ _ _ _ _ _ t 460 q _ HMR HCP Hub Hq ltac:(lia) Hn1 ltac:(lia) Hlive)
      as [Hlive' (qt & Hqt & Hqt' & Hpqt)].
    assert (CS := cs_after _ _ _ _ _ _ _ _ _ _ _ _ _ HR HCP).
    exists (YK11.mkst regs' (Z_to_bv 64 PC_FREE_SW1_RET) mem' (seg_rom rsegs)), md', L', A'.
    split; [reflexivity|].
    split.
    2:{ rewrite <- Hpq. split; [apply call_post_k_alloc; exact HCP|].
        split; [exact Hsplit|]. split; [exact Hkept|]. split; [exact Hguard|]. exact Hub. }
    unfold glue_post. cbn [ms_mem ms_fregs ms_fcsr YK11.mkst].
    split; [|split; [rewrite Hseg; exact Hro'|]].
    2:{ split; [reflexivity|]. split; [reflexivity|].
        split; [exact (conj HMR' (conj HWF' (conj Hbd' (conj Hinit' Hslots))))|].
        split; [|split; [exact Hpay' | exact Hlive']].
        intros a Ha. destruct HCP as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Hscr). apply Hscr. unfold scratch_k. right. exact Ha. }
    exists (YK11.mkst regs' (Z_to_bv 64 PC_FREE_SW1_RET) (normalize rsegs mem') (seg_rom rsegs)).
    split.
    2:{ unfold ms_rel. cbn [ms_regs ms_fregs ms_pc_val ms_svc_pending ms_resv ms_fcsr ms_rom ms_mem YK11.mkst].
        repeat split; apply mem_rel_normalize; exact Hro'. }
    assert (HFx : fp_regs = x_F x) by (rewrite <- HF0, <- HRf, Hfr; reflexivity).
    assert (HCx : fp_csr = x_fc x) by (rewrite <- Hfc0, <- HRc, Hfc; reflexivity).
    assert (RG : forall k, rg (YK11.mkst regs' (Z_to_bv 64 PC_FREE_SW1_RET) (normalize rsegs mem') (seg_rom rsegs)) k =
                           YK11.getr regs' (Z_to_bv 5 k)) by (intros; reflexivity).
    assert (HSTk : stk rsegs (normalize rsegs mem') (x_S x - LLVM_STACK) (x_S x)) by (eapply stack_kept; eassumption).
    assert (HSVk : rw_cells rsegs (normalize rsegs mem') (x_S x - 104) (map C8 (rev (x_sv x) ++ [x_ra x]))).
    { eapply frame_kept; try eassumption; [lia | rewrite (SegSetModel.saved_size _ _ Hsv120); lia]. }
    assert (HRWk : bytes_at rsegs (normalize rsegs mem') CTRL_HEADAMP_ROW CTRL_HEADAMP_BYTES)
      by (eapply row_kept; eassumption).
    assert (HPLk : rw_cells rsegs (normalize rsegs mem') (x_p x) [CB (length (x_pl x)) (x_pl x)])
      by (eapply payload_kept; eassumption).
    assert (HSLk := HSL0). assert (HCSk := HCS0). assert (HWSk := HWS0). assert (HSTAk := HSTA0).
    eapply frame_kept in HSLk; try eassumption; [| change (SPL x) with (x_S x - 608); lia | change (SPL x) with (x_S x - 608); cbn; lia].
    eapply frame_kept in HCSk; try eassumption; [| change (SPL x) with (x_S x - 608); lia | change (SPL x) with (x_S x - 608); cbn; lia].
    eapply frame_kept in HWSk; try eassumption; [| change (SPL x) with (x_S x - 608); lia | change (SPL x) with (x_S x - 608); cbn; lia].
    eapply frame_kept in HSTAk; try eassumption; [| change (SPL x) with (x_S x - 608); lia | change (SPL x) with (x_S x - 608); cbn; lia].
    assert (HTk : rw_cells rsegs (normalize rsegs mem') t [CB 460 (T_end (x_pl x))]).
    { rewrite <- Hpqt. eapply block_kept; try eassumption; [cbn; lia | rewrite Hpqt; exact HT0]. }
    unfold At_raw, at_after_admit, body, common, slots, cslot, table, arrays.
    cbn [ms_pc_val ms_fregs ms_fcsr ms_resv ms_svc_pending ms_rom ms_mem YK11.mkst].
    rewrite !RG. rewrite (CS 2), (CS 3), (CS 4), (CS 8), (CS 25) by (unfold callee_saved; lia).
    repeat match goal with |- _ /\ _ => split end.
    all: first [ reflexivity | assumption | apply mem_inv_normalize | lia | (right; split; [reflexivity | exact Hok0]) ].
Qed.

Theorem seg_freeSW2_cf_holds : seg_freeSW2_cf B API.
Proof.
  unfold seg_freeSW2_cf, free_glue_cf. intros x t sw HS s md L A b q Hpre Hlive Hq Hpq.
  destruct Hpre as (HFA & HUB & Htp & (s0 & HP & HR) & Hro & Hfr & Hfc & Hal & Herr & Hpay & Herrlo & Hrow).
  pose proof HUB as (Hseg & _ & _).
  pose proof HFA as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Hbw & _ & _ & _ & HAX & _).
  pose proof Hal as (HMR & _).
  pose proof HP as HP0.
  destruct HP0 as (((Hpc0 & HF0 & Hfc0 & Hrv0 & Hsvc0 & Hro0 & Hgp0 & Htp0 & HPL0 & HST0 & HMI0 & Hp00 & Hpn0 & Hpd0 &
                     HRW0 & HRS0 & HRP0) & Hsp0 & HSV0 & HS160 & Hsv120 & HS630) &
                   Hn0 & H80 & Ha00 & H90 & (H210 & H250) & (HTb0 & HT160 & HTl0 & HT0) & (Hwl0 & Hstl0 & HWS0 & HSTA0) &
                   HHr0 & HI10 & Hblks).
  pose proof HR as (HRr & HRf & _ & _ & _ & HRc & _ & HRm).
  apply (free_core_cf s s0 md L A b q 4352 PC_FREE_SW2_RET _ HUB HR Hro Hfr Hfc Hal Herr Hq).
  - rewrite Hpq, <- Ha00. apply jal_at_freeSW2; assumption.
  - vm_compute. reflexivity.
  - exact Hro0.
  - rewrite Htp0, Htp. reflexivity.
  - exact (sp_ok_of_body x s0 Hsp0 HST0 HS160 HS630 HS).
  - intros L' A' regs' mem' md' HCP Hsplit Hkept Hro' Hguard Hub Hinit' Hslots.
    pose proof HCP as (HMR' & HWF' & Hbd' & _).
    assert (HEl : forall a, ptr_addr L q <= a < ptr_addr L q + 4352 -> a < alloc_ceiling)
      by (intros a Ha; exact (freed_low L A _ md q _ a HMR Hq Ha)).
    assert (HEi : forall a, ptr_addr L q <= a < ptr_addr L q + 4352 -> ~ in_img B a)
      by (intros a Ha; exact (freed_noimg L A _ md q _ a HAX HMR Hq Ha)).
    pose proof Hblks as (_ & _ & _ & Hspay & _).
    destruct (payload_after_free x L A L' A' _ _ _ _ _ _ _ q 4352 HCP Hub ltac:(lia) ltac:(rewrite Hpq; exact Hspay) Hpay)
      as [Hpay' Hpayk].
    destruct (live_after_free L A L' A' _ _ _ _ _ _ _ t 460 q 4352 HMR HCP Hub Hq ltac:(lia) ltac:(lia) ltac:(lia) Hlive)
      as [Hlive' (qt & Hqt & Hqt' & Hpqt)].
    assert (CS := cs_after _ _ _ _ _ _ _ _ _ _ _ _ _ HR HCP).
    exists (YK11.mkst regs' (Z_to_bv 64 PC_FREE_SW2_RET) mem' (seg_rom rsegs)), md', L', A'.
    split; [reflexivity|].
    split.
    2:{ rewrite <- Hpq. split; [apply call_post_k_alloc; exact HCP|].
        split; [exact Hsplit|]. split; [exact Hkept|]. split; [exact Hguard|]. exact Hub. }
    unfold glue_post. cbn [ms_mem ms_fregs ms_fcsr YK11.mkst].
    split; [|split; [rewrite Hseg; exact Hro'|]].
    2:{ split; [reflexivity|]. split; [reflexivity|].
        split; [exact (conj HMR' (conj HWF' (conj Hbd' (conj Hinit' Hslots))))|].
        split; [|split; [exact Hpay' | exact Hlive']].
        intros a Ha. destruct HCP as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Hscr). apply Hscr. unfold scratch_k. right. exact Ha. }
    exists (YK11.mkst regs' (Z_to_bv 64 PC_FREE_SW2_RET) (normalize rsegs mem') (seg_rom rsegs)).
    split.
    2:{ unfold ms_rel. cbn [ms_regs ms_fregs ms_pc_val ms_svc_pending ms_resv ms_fcsr ms_rom ms_mem YK11.mkst].
        repeat split; apply mem_rel_normalize; exact Hro'. }
    assert (HFx : fp_regs = x_F x) by (rewrite <- HF0, <- HRf, Hfr; reflexivity).
    assert (HCx : fp_csr = x_fc x) by (rewrite <- Hfc0, <- HRc, Hfc; reflexivity).
    assert (RG : forall k, rg (YK11.mkst regs' (Z_to_bv 64 PC_FREE_SW2_RET) (normalize rsegs mem') (seg_rom rsegs)) k =
                           YK11.getr regs' (Z_to_bv 5 k)) by (intros; reflexivity).
    assert (HSTk : stk rsegs (normalize rsegs mem') (x_S x - LLVM_STACK) (x_S x)) by (eapply stack_kept; eassumption).
    assert (HSVk : rw_cells rsegs (normalize rsegs mem') (x_S x - 104) (map C8 (rev (x_sv x) ++ [x_ra x]))).
    { eapply frame_kept; try eassumption; [lia | rewrite (SegSetModel.saved_size _ _ Hsv120); lia]. }
    assert (HRWk : bytes_at rsegs (normalize rsegs mem') CTRL_HEADAMP_ROW CTRL_HEADAMP_BYTES)
      by (eapply row_kept; eassumption).
    assert (HPLk : rw_cells rsegs (normalize rsegs mem') (x_p x) [CB (length (x_pl x)) (x_pl x)])
      by (eapply payload_kept; eassumption).
    assert (HWSk := HWS0). assert (HSTAk := HSTA0).
    eapply frame_kept in HWSk; try eassumption; [| change (SPL x) with (x_S x - 608); lia | change (SPL x) with (x_S x - 608); cbn; lia].
    eapply frame_kept in HSTAk; try eassumption; [| change (SPL x) with (x_S x - 608); lia | change (SPL x) with (x_S x - 608); cbn; lia].
    assert (HTk : rw_cells rsegs (normalize rsegs mem') t [CB 460 (T_end (x_pl x))]).
    { rewrite <- Hpqt. eapply block_kept; try eassumption; [cbn; lia | rewrite Hpqt; exact HT0]. }
    unfold At_freeSW2_ret, body, common, cur5, table, arrays.
    cbn [ms_pc_val ms_fregs ms_fcsr ms_resv ms_svc_pending ms_rom ms_mem YK11.mkst].
    rewrite !RG. rewrite (CS 2), (CS 3), (CS 4), (CS 8), (CS 21), (CS 25) by (unfold callee_saved; lia).
    repeat match goal with |- _ /\ _ => split end.
    all: first [ reflexivity | assumption | apply mem_inv_normalize | lia ].
Qed.

End CfG.
