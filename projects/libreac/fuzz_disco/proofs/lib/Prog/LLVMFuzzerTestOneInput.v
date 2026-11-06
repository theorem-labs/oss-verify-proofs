From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.libreac.fuzz_disco.lib Require Import Img0 Contract FrameAPI KindBGlue AllocSlots AllocRoom.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Lib Require MState Mem.
From OSSVerify.Proofs.libreac.fuzz_disco.lib Require MemNorm.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import LLVMFuzzerTestOneInput_c slot_inv slot_norm slot_cut slot_seg.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import slot_preds slot_transport.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import disco_classify_c disco_table_c hunt_c.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import reac_disco_table_init_c reac_disco_gate_init_c.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import reac_disco_peer_lock_init_c reac_hunt_init_c.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import reac_hunt_pin_c reac_hunt_silence_proven_c.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import reac_disco_table_age_c check_table_c.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import printf_facts_c slot_ser_defs slot_ser_iface.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import memcpy_c find_entry_c reac_hunt_observe_c.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import check_sighting_c reac_disco_classify_c.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import reac_disco_classify_on_segment_c.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import reac_disco_gate_should_push_c bcmp_c.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import reac_disco_table_observe_c.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import reac_hunt_step_c reac_hunt_verdict_name_c.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import reac_hunt_role_c reac_hunt_heard_anything_c.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import slot_exit slot_R0_R3 slot_frame slot_step.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import slot_sE slot_sE2 slot_sB1 slot_sB2a slot_sB2b.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import slot_sB3a slot_sLatch slot_sX slot_record.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import snprintf_c json_scalar_c reac_box_name_c.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import reac_disco_table_json_c slot_steps slot_run.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require strlen_c jtok_is_c snprintf_stk_c slot_ser_chain.
Import ListNotations.
Open Scope Z_scope.

Lemma glue_ret : forall ra, ra mod 2 = 0 ->
  Z_to_bv 64 (bv_unsigned (MState.ret_pc (Z_to_bv 64 ra))) = Z_to_bv 64 ra.
Proof.
  intros ra H. rewrite MState.Z_to_bv_bv_unsigned.
  assert (E : Z_to_bv 64 ra = Z_to_bv 64 (ra mod 2 ^ 64)).
  { apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
    rewrite Z.mod_mod by lia. reflexivity. }
  rewrite E. apply MState.ret_pc_even.
  - apply Z.mod_pos_bound. lia.
  - rewrite kb_mod2_land. exact H.
Qed.

Lemma glue_start {fx : FPState} {rc : RunCeil} {LS : lib_shape} (B : malloc_syms) (API : AllocAPI B)
    {SH : sink_head} {SK : sink_syms} :
  forall (ra empty : Z) L A regs mem md p n pl b,
    ms_segs B = rsegs -> AllocExtra B (aa_MR API) -> empty = 0x31170 -> ms_tp B = 0x31260 ->
    lib_pre_x B API SLOT_STACK empty L A regs mem md ra p n pl b ->
    MemNorm.ro_agree (ms_segs B) mem -> frm_zero (@fp_csr fx) ->
    xok (spZ regs - SLOT_FRAME) /\ dok (spZ regs - SLOT_FRAME) p pl /\
    xin SLOT_STACK (spZ regs) (spZ regs - SLOT_FRAME) /\
    slot_cut B API SLOT_STACK (spZ regs) L A mem md b ENTRY_PC [] (P_ENT (spZ regs - SLOT_FRAME) p pl regs)
      (mkCfg (mkst regs (Z_to_bv 64 ENTRY) mem (seg_rom rsegs)) md).
Proof.
  intros ra empty L A regs mem md p n pl b HSEGS HAX HEMP HTP Hpre Hro Hfrm.
  destruct Hpre as (HP0 & HLEN & HD & Hres & Hroom & HSink & Hfd & Hsorted & Hch & Hsp47).
  pose proof HP0 as (HM & HW & HB & HID & Hra & Hal & Hceil & H63 & Hstw & Htp & Herr & Hp & Hnn & Hpp & Hrod).
  pose proof ceil_hi as Hhi. pose proof alloc_ceiling_lt as Hlt. unfold IMG_HI in Hhi.
  rewrite HSEGS in Hro.
  assert (HREL : MemNorm.mem_rel_cj rsegs mem (MemNorm.normalize_cj rsegs mem))
    by (apply MemNorm.mem_rel_cj_normalize; exact Hro).
  assert (HPL : 0 <= p /\ p + n <= alloc_ceiling /\ (0 < n -> forall i, 0 <= i < n -> nseg (p + i))).
  { destruct Hpp as [[Hn0 Hpe] | [Hnpos (q & Hq & Eq)]].
    - rewrite Hpe, HEMP, Hn0. split; [lia|]. split; [lia|]. intros H0. exfalso. lia.
    - pose proof (mr_blocks_range _ _ (aa_laws API) L A mem md q n HM Hq) as [R1 R2]. rewrite <- Eq.
      split; [lia|]. split; [lia|]. intros _ i Hi. unfold nseg.
      destruct (Z_lt_le_dec (ptr_addr L q + i) IMG_LO) as [H1|H1]; [left; exact H1|].
      destruct (Z_lt_le_dec (ptr_addr L q + i) IMG_HI) as [H2|H2]; [|right; exact H2].
      exfalso. apply (ax_blocks_img HAX L A mem md q n i HM Hq Hi). apply (in_img_hi B _ HSEGS). lia. }
  destruct HPL as (HP1 & HP2 & HP3).
  split.
  { unfold xok, LO, SLOT_FRAME, SLOT_STACK, IMG_HI in *.
    split; [lia|]. split.
    { replace (spZ regs - 2592) with (spZ regs + (-162) * 16) by lia. rewrite Z.mod_add by lia. exact Hal. }
    split; lia. }
  split.
  { unfold dok. rewrite <- HLEN. split; [lia|]. split; [lia|].
    split; [unfold LO, SLOT_FRAME, SLOT_STACK in *; lia|].
    intros Hne i Hi. apply HP3; [|exact Hi]. destruct pl as [|x pl']; [exfalso; apply Hne; reflexivity|].
    cbn [length] in HLEN. lia. }
  split; [unfold xin, LO, SLOT_FRAME, SLOT_STACK; lia|].
  unfold slot_cut. exists fx, L, A, regs, mem, md, (MemNorm.normalize_cj rsegs mem).
  split; [reflexivity|]. split; [exact Hfrm|].
  split.
  { unfold slot_fr, slot_sofar.
    split.
    { refine (conj HM (conj HW (conj HB (conj HID (conj _ (conj _ (conj _ (conj _ (conj _ (conj HSink Hrod)))))))))).
      - exists (m_vmmaps md). symmetry. apply kb_vm_id.
      - intros a _ _ _. split; [reflexivity | tauto].
      - intros a _ _ _ _. split; [reflexivity | tauto].
      - intros q k i _ _. reflexivity.
      - intros a [Ha | Ha]; [apply Hstw | apply Herr]; exact Ha. }
    split; [exact Hro|]. split; [cbn [app]; apply Permutation_refl|]. rewrite sb_hb_nil. exact Hres. }
  split; [exact HREL|].
  unfold P_ENT. split; [intros r; reflexivity|].
  split.
  { replace (spZ regs - SLOT_FRAME + SLOT_FRAME) with (spZ regs) by lia. unfold spZ.
    symmetry. apply MState.Z_to_bv_bv_unsigned. }
  split; [exact Hp|]. split; [rewrite Hnn, HLEN; reflexivity|]. split; [rewrite Htp, HTP; reflexivity|].
  split; [lia|]. split; [rewrite <- HLEN; lia|].
  intros i Hi.
  assert (Hi' : 0 <= Z.of_nat i < n) by lia.
  pose proof (HD (Z.of_nat i) ltac:(lia)) as E.
  rewrite Nat2Z.id in E. unfold mbyte in E. rewrite HSEGS in E.
  unfold Mem.mrd. rewrite (norm_nseg mem _ (p + Z.of_nat i) HREL).
  - exact E.
  - unfold TASK_SIZE. lia.
  - apply HP3; lia.
Qed.

Lemma glue_post {fx : FPState} {rc : RunCeil} {LS : lib_shape} (B : malloc_syms) (API : AllocAPI B)
    {SH : sink_head} {SK : sink_syms} :
  forall (ra empty : Z) L A regs mem md p n pl b j q c',
    ms_segs B = rsegs -> ra mod 2 = 0 -> (forall n b, @lib_delta LS n b = b) ->
    lib_pre_x B API SLOT_STACK empty L A regs mem md ra p n pl b ->
    slot_cut B API SLOT_STACK (spZ regs) L A mem md b q []
      (fun R m => q = bv_unsigned (MState.ret_pc (getr regs 1)) /\ P_RET regs R m) c' ->
    exists (fx' : FPState) L' A' regs' mem' md',
      c' = mkCfg (@mkst fx' regs' (Z_to_bv 64 ra) mem' (seg_rom rsegs)) md' /\
      frm_zero (@fp_csr fx') /\
      lib_post_g B API [] SLOT_STACK L A regs mem md p n b (LL 0 (m_fs md) []) L' A' regs' mem' md' /\
      disco_GI (S j) mem'.
Proof.
  intros ra empty L A regs mem md p n pl b j q c' HSEGS HRA HDELTA Hpre HC.
  destruct Hpre as (HP0 & HLEN & HD & Hres & Hroom & HSink & Hfd & Hsorted & Hch & Hsp47).
  pose proof HP0 as (HM & HW & HB & HID & Hra & Hal & Hceil & H63 & Hstw & Htp & Herr & Hp & Hnn & Hpp & Hrod).
  destruct HC as (fx' & L' & A' & regs' & mem' & md' & m0' & Ec & Hf & HFR & HREL & Hq & HPR & H10).
  destruct HFR as ((HM' & HW' & HB' & HID' & (vm & Hmd) & Hhi & Himg & Hblk & Hwr & HSink' & Hrod') &
    Hro' & HP & Hres').
  exists fx', L', A', regs', mem', md'.
  split; [rewrite Ec, Hq, Hra, (glue_ret ra HRA); reflexivity|].
  split; [exact Hf|].
  split; [|exact I].
  unfold lib_post_g.
  split; [exact HM'|]. split; [exact HW'|]. split; [exact HB'|]. split; [exact HID'|].
  split; [exact H10|]. split; [exact HPR|].
  split.
  { exists vm, (m_fds md), (m_statpins md).
    split; [rewrite Hmd; apply with_vmmaps_os_upd | intros k; reflexivity]. }
  split.
  { intros q0 k Hq0.
    destruct (in_blocks L' A' (ptr_addr L q0) k (Permutation_in _ (Permutation_sym HP) (blocks_in L A q0 k Hq0)))
      as (q' & Hq' & Eq').
    exists q'. split; [exact Hq' | exact Eq']. }
  split.
  { intros a Ha Hns. apply Hhi; [exact Ha | intros H; apply Hns; left; exact H | intros H; apply Hns; right; exact H]. }
  split; [intros a H1 H2 H3 H4 _; exact (Himg a H1 H2 H3 H4)|].
  split; [intros a (lo & len & [] & _)|].
  split; [intros q0 k i Hq0 _ Hi; exact (Hblk q0 k i Hq0 Hi)|].
  split; [intros a Ha; apply Hwr; exact Ha|].
  split; [reflexivity|]. split; [reflexivity|]. split; [exact Hsorted|].
  split; [exact HSink'|].
  split; [rewrite HSEGS; exact Hro'|].
  split; [rewrite HDELTA; rewrite sb_hb_nil in Hres'; exact Hres'|].
  intros i Hi. destruct Hpp as [[Hn0 _] | [_ (q0 & Hq0 & Eq0)]]; [lia|].
  rewrite <- Eq0. exact (Hblk q0 n i Hq0 Hi).
Qed.

Theorem LLVMFuzzerTestOneInput_holds :
  reac_disco_table_init_contract -> reac_disco_gate_init_contract -> reac_disco_peer_lock_init_contract ->
  reac_hunt_init_contract -> reac_hunt_pin_contract -> reac_hunt_silence_proven_contract ->
  reac_disco_table_age_contract -> check_table_contract ->
  reac_disco_table_json_contract -> strlen_c.strlen_contract -> json_scalar_contract -> jtok_is_c.jtok_is_contract ->
  reac_box_name_contract -> snprintf_stk_c.snprintf_stk_contract ->
  reac_hunt_step_contract -> reac_hunt_verdict_name_contract -> reac_hunt_role_contract ->
  reac_hunt_heard_anything_contract -> memcpy_contract -> find_entry_contract -> reac_hunt_observe_contract ->
  check_sighting_contract -> reac_disco_classify_contract -> reac_disco_classify_on_segment_contract ->
  reac_disco_gate_should_push_contract -> bcmp_contract -> reac_disco_table_observe_contract ->
  LLVMFuzzerTestOneInput_contract.
Proof.
  intros TIC GIC LIC HIC PIC SIC AGE CTC TJC SLC JSC JTC BNC SNK HTC VNC RLC HAC MC FEC HOC CSC CC0 CC1 GSC BC OBC.
  destruct (slot_ser_chain.slot_ser_chain_holds TJC SLC JSC JTC BNC SNK) as [SERA SERB].
  intros B API LS SH SK ra empty HSEGS HRA HMAL HFRE HREAL HCAL HERRC HGD HGG HCTX HLK HLIBC HSC HSMC HMDC
    HDB HTP HERR HREP HVML HDBL HHEAD HLOCK HTHR HEMP HEMP2 HCTXRO HG HRELRO HLIBK HDELTA HROOM HFA rc fx j Hj.
  intros L A regs mem md p n pl b K Hpre HGI HR Hro Hsp Hfrm HK.
  rewrite HLIBK.
  destruct (HFA rc fx) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HAX & _).
  pose proof Hpre as (HP0 & HLEN & _ & _ & Hroom & _ & _ & _ & _ & Hsp47).
  pose proof HP0 as (_ & _ & _ & _ & _ & _ & Hceil & _ & _ & _ & _ & _ & _ & Hpp & _).
  destruct (HROOM b n Hroom) as (Hl & Hby & Hcap).
  destruct (glue_start B (API rc) ra empty L A regs mem md p n pl b HSEGS HAX HEMP HTP Hpre Hro Hfrm)
    as (HXOK & HDOK & HXIN & HCUT).
  assert (HDBLK : dblk L A p pl).
  { unfold dblk. destruct Hpp as [[Hn0 Hpe] | [_ (q0 & Hq0 & Eq0)]].
    - left. split.
      + destruct pl as [|x pl']; [reflexivity | exfalso; cbn [length] in HLEN; lia].
      + rewrite Hpe, HEMP. unfold IMG_LO, IMG_HI. lia.
    - right. rewrite <- Eq0, <- HLEN. exact (blocks_in L A q0 n Hq0). }
  assert (HSR : SR rsegs (mkCfg (mkst regs (Z_to_bv 64 ENTRY) mem (seg_rom rsegs)) md)
    (fun c' => exists q, slot_cut B (API rc) SLOT_STACK (spZ regs) L A mem md b q []
      (fun R m => q = bv_unsigned (MState.ret_pc (getr regs 1)) /\ P_RET regs R m) c')).
  { eapply (@slot_run rc B (API rc) SH SK SLOT_STACK (spZ regs) L A mem md b);
      first [ exact HCUT | exact HXOK | exact HDOK | exact HXIN | exact HDBLK | exact (HFA rc) | exact HR
            | exact (conj Hl (conj Hby Hcap)) | eassumption | (unfold SLOT_STACK; lia) ]. }
  rewrite HSEGS in HK |- *.
  apply (SR_realizes rsegs _ _ _ HSR).
  intros c' (q & Hc'). apply HK.
  exact (glue_post B (API rc) ra empty L A regs mem md p n pl b j q c' HSEGS HRA HDELTA Hpre Hc').
Qed.
