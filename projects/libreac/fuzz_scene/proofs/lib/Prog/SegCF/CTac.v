From Stdlib Require Import ZArith List Bool Lia Permutation String.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Sem.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Lib Require Import PropExec MState Mem Exec Frame Step Tac
  Regs6ss RegisterBridge.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Lib Require Cells.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14 YI04.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import YM05 YL0i YO03.
From OSSVerify.Proofs.libreac.fuzz_scene.lib Require Import Img0 Contract FrameAPI MemNorm AllocSlots AllocRoom
  SlotAgree AgreeLift.
From OSSVerify.Proofs.libreac.fuzz_scene.lib Require KindBGlue.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Prog.Seg Require Import SInv STac SGlue SMid.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Prog.SegCF Require Import CInv.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import YM0b.
Import ListNotations.
Open Scope Z_scope.

(* Cut-free twins of the SR-level steps of STac, SMid and SGlue: the same proofs with SRcf for SR, the cut-free
   allocator contracts, and the room of the cut-free malloc. *)

(* KindBGlue.kb_run in the cut-free form. *)
Section KB.
Variable B : malloc_syms.

Lemma kb_run_cf : forall {fx : YK11.FPState} regs pc mem md (K : bvmap 5 word -> word -> (word -> option byte) -> Prop)
    (P : config -> Prop),
  m_halted md = None -> m_vm_lazy md = [] ->
  Exec.evt (ms_segs B) (fun ms => exists R pc' mem', ms = MState.MS R fp_regs pc' fp_csr None mem' (seg_rom (ms_segs B)) /\
      K R pc' mem')
    (MState.MS (KindBGlue.rmk regs) fp_regs pc fp_csr None mem (seg_rom (ms_segs B))) ->
  (forall R pc' mem' regs', K R pc' mem' -> (forall r, getr regs' r = getr R r) ->
     SRcf B (mkCfg (mkst regs' pc' mem' (seg_rom (ms_segs B))) md) P) ->
  SRcf B (mkCfg (mkst regs pc mem (seg_rom (ms_segs B))) md) P.
Proof.
  intros fx regs pc mem md K P Hh Hl HE HK.
  eapply (evt_SRcf_canon B (mkst regs pc mem (seg_rom (ms_segs B))) _ md P); [exact HE | exact Hh | exact Hl |].
  intros ms' (can & (R & pc' & mem' & -> & HKR) & Heq).
  destruct Heq as (HR & HF & Hpc & Hsvc & Hres & Hfc & Hm & Hrom).
  destruct ms' as [regs' fr' pcv' svc' rv' fc' m' ro'].
  cbn in HR, HF, Hpc, Hsvc, Hres, Hfc, Hm, Hrom. subst.
  apply (HK R _ _ regs' HKR). apply KindBGlue.kb_getr_eqv. exact HR.
Qed.

End KB.

Section T.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AllocAPI B.
Context {LS : lib_shape} {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Hypothesis FF : frame_facts B APIf LS SH SK ra empty.
Let API := APIf rc.
Let MR := aa_MR API.

Lemma ss_run_cf : forall regs pc mem md (Q : machine_state -> Prop) (P : config -> Prop),
  m_halted md = None -> m_vm_lazy md = [] -> ro_agree rsegs mem ->
  Exec.evt rsegs Q (MState.MS (Regs6ss.mkR_of regs) fp_regs pc fp_csr None (normalize rsegs mem) (seg_rom rsegs)) ->
  (forall ms, Q ms -> exists R pc' m', ms = MState.MS R fp_regs pc' fp_csr None m' (seg_rom rsegs)) ->
  (forall R pc' m0', Q (MState.MS R fp_regs pc' fp_csr None m0' (seg_rom rsegs)) ->
     forall regs' m', Regs6ss.xregs_eqv R regs' -> mem_rel rsegs m' m0' -> ro_same rsegs mem m' ->
     SRcf B (mkCfg (mkst regs' pc' m' (seg_rom (ms_segs B))) md) P) ->
  SRcf B (mkCfg (mkst regs pc mem (seg_rom (ms_segs B))) md) P.
Proof.
  intros regs pc mem md Q P Hh Hl Hro HE Hform HK.
  pose proof (ss_segs B APIf ra empty FF) as SEG.
  apply (evt_SRcf_canon B _ (fun s => exists s0, Q s0 /\ ms_rel rsegs s s0 /\ ro_same rsegs mem (ms_mem s)) md P);
    [| exact Hh | exact Hl |].
  - rewrite SEG.
    change (RegisterBridge.canonical_register_state (mkst regs pc mem (seg_rom rsegs)))
      with (MState.MS (Regs6ss.mkR_of regs) fp_regs pc fp_csr None mem (seg_rom rsegs)).
    apply evt_normalize; [exact wx_apart_rsegs | exact Hro | exact HE].
  - intros ms' (can & (s0 & HQ & Hrel & Hsame) & Heq).
    destruct (Hform s0 HQ) as (R & pc' & m0' & ->).
    destruct can as [cr cf cp cs cv cc cm co].
    destruct Hrel as (E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8).
    cbn [ms_regs ms_fregs ms_pc_val ms_svc_pending ms_resv ms_fcsr ms_mem ms_rom MState.MS] in *. subst.
    destruct (ss_eqv_mkfp R fp_regs pc' fp_csr cm (seg_rom rsegs) ms' Heq) as [Ems Hx].
    rewrite Ems, ss_mkFP. rewrite SEG in HK.
    exact (HK R pc' m0' HQ _ cm Hx E8 Hsame).
Qed.

Lemma ss_kA_run_cf : forall (regs : bvmap 5 word) pc mem md (Q : bvmap 5 word -> word -> (word -> option byte) -> Prop) P,
  m_halted md = None -> m_vm_lazy md = [] -> ro_agree (ms_segs B) mem ->
  Exec.evt rsegs (fun ms => exists R pc' m', ms = MS R fp_regs pc' fp_csr None m' (seg_rom rsegs) /\ Q R pc' m')
    (MS (mkR_of regs) fp_regs pc fp_csr None (normalize rsegs mem) (seg_rom rsegs)) ->
  (forall R pc' m' regs' mem', Q R pc' m' -> xregs_eqv R regs' -> mem_rel rsegs mem' m' -> ro_same rsegs mem mem' ->
     SRcf B (mkCfg (mkst regs' pc' mem' (seg_rom (ms_segs B))) md) P) ->
  SRcf B (mkCfg (mkst regs pc mem (seg_rom (ms_segs B))) md) P.
Proof.
  intros regs pc mem md Q P Hh Hl HRO HE HK.
  pose proof (ss_segs B APIf ra empty FF) as SEG.
  eapply (evt_SRcf_canon B (mkst regs pc mem (seg_rom (ms_segs B))) _ md P); [| exact Hh | exact Hl |].
  - rewrite ss_canon_mkst. rewrite SEG. apply (evt_normalize rsegs); [exact wx_apart_rsegs | rewrite <- SEG; exact HRO |].
    exact HE.
  - intros ms' (can & (s0 & (R & pc' & m' & -> & HQ) & Hrel & Hsame) & Heq).
    destruct can as [cR cF cpc csvc cres cfc cmem crom].
    destruct Hrel as (E1 & E2 & E3 & E4 & E5 & E6 & E7 & Hmr). cbn in E1, E2, E3, E4, E5, E6, E7, Hmr, Hsame.
    subst cR cF cpc csvc cres cfc crom.
    destruct (ss_eqv_mkst R pc' cmem (seg_rom rsegs) ms' Heq) as (R' & -> & XR).
    rewrite <- SEG. apply (HK R pc' m' R' cmem HQ XR Hmr Hsame).
Qed.

Lemma ss_kA_run0_cf : forall (regs : bvmap 5 word) pc mem md (Q : bvmap 5 word -> word -> (word -> option byte) -> Prop) P,
  m_halted md = None -> m_vm_lazy md = [] ->
  Exec.evt rsegs (fun ms => exists R pc' m', ms = MS R fp_regs pc' fp_csr None m' (seg_rom rsegs) /\ Q R pc' m')
    (MS (mkR_of regs) fp_regs pc fp_csr None mem (seg_rom rsegs)) ->
  (forall R pc' m' regs', Q R pc' m' -> xregs_eqv R regs' ->
     SRcf B (mkCfg (mkst regs' pc' m' (seg_rom (ms_segs B))) md) P) ->
  SRcf B (mkCfg (mkst regs pc mem (seg_rom (ms_segs B))) md) P.
Proof.
  intros regs pc mem md Q P Hh Hl HE HK.
  pose proof (ss_segs B APIf ra empty FF) as SEG.
  eapply (evt_SRcf_canon B (mkst regs pc mem (seg_rom (ms_segs B))) _ md P); [| exact Hh | exact Hl |].
  - rewrite ss_canon_mkst. rewrite SEG. exact HE.
  - intros ms' (can & (R & pc' & m' & -> & HQ) & Heq).
    destruct (ss_eqv_mkst R pc' m' (seg_rom rsegs) ms' Heq) as (R' & -> & XR).
    rewrite <- SEG. exact (HK R pc' m' R' HQ XR).
Qed.

Lemma ss_mid_cf : forall g km hb L A regs mem md pc (Q : machine_state -> Prop) (P : config -> Prop),
  FR B APIf ra empty g km hb L A regs mem md ->
  Permutation (blocks L A) (hb ++ blocks (g_L g) (g_A g)) ->
  Exec.evt rsegs Q (MState.MS (Regs6ss.mkR_of regs) fp_regs pc fp_csr None (normalize rsegs mem) (seg_rom rsegs)) ->
  (forall ms, Q ms -> exists R pc' m', ms = MState.MS R fp_regs pc' fp_csr None m' (seg_rom rsegs) /\
     (exists W, Frame.munch W (normalize rsegs mem) m' /\ Frame.wmono rsegs (normalize rsegs mem) m' /\
        (forall x, 0 <= x < 2 ^ 64 -> ~ Frame.outside W x -> g_S g - SLOT_K <= x < g_S g - 104)) /\
     getr R 2 = getr regs 2 /\ getr R 3 = getr regs 3 /\ getr R 4 = getr regs 4) ->
  (forall R pc' m0' regs' m', Q (MState.MS R fp_regs pc' fp_csr None m0' (seg_rom rsegs)) ->
     Regs6ss.xregs_eqv R regs' -> mem_rel rsegs m' m0' ->
     FR B APIf ra empty g km hb L A regs' m' md ->
     SRcf B (mkCfg (mkst regs' pc' m' (seg_rom (ms_segs B))) md) P) ->
  SRcf B (mkCfg (mkst regs pc mem (seg_rom (ms_segs B))) md) P.
Proof.
  intros g km hb L A regs mem md pc Q P HFR HP HE Hform HK.
  pose proof (ss_segs B APIf ra empty FF) as SEGS.
  pose proof HFR as (_ & _ & _ & _ & _ & _ & HMI & _ & HM & _).
  unfold MI in HMI. rewrite SEGS in HMI.
  destruct (mr_model B _ (aa_laws API) _ _ _ _ HM) as (Hh & Hl & _).
  apply (ss_run_cf regs pc mem md Q P Hh Hl HMI HE).
  - intros ms HQ. destruct (Hform ms HQ) as (R & pc' & m' & -> & _). exists R, pc', m'. reflexivity.
  - intros R pc' m0' HQ regs' m' Hx Hrel Hsame.
    destruct (Hform _ HQ) as (R1 & pc1 & m1 & E & (W & MU & WM & HW) & E2 & E3 & E4).
    injection E; intros; subst.
    pose proof (mem_rel_normalize rsegs mem HMI) as HR0.
    apply (HK R1 pc1 m1 regs' m' HQ Hx Hrel).
    apply (ss_fr_run B APIf ra empty FF g km hb L A regs mem md regs' m' W HFR HP).
    + exact (munch_rel rsegs W mem (normalize rsegs mem) m' m1 HR0 Hrel Hsame MU).
    + exact (wmono_rel rsegs mem (normalize rsegs mem) m' m1 HR0 Hrel Hsame WM).
    + exact (ro_agree_same rsegs mem m' HMI Hsame).
    + exact HW.
    + rewrite (ss_getr_eqv _ _ _ Hx). exact E2.
    + rewrite (ss_getr_eqv _ _ _ Hx). exact E3.
    + rewrite (ss_getr_eqv _ _ _ Hx). exact E4.
Qed.

Lemma sm_mid_cf : forall g km hb L A regs mem md pc (Q : machine_state -> Prop) (P : config -> Prop),
  FR B APIf ra empty g km hb L A regs mem md ->
  Permutation (blocks L A) (hb ++ blocks (g_L g) (g_A g)) ->
  Exec.evt rsegs Q (MState.MS (Regs6ss.mkR_of regs) fp_regs pc fp_csr None (normalize rsegs mem) (seg_rom rsegs)) ->
  (forall ms, Q ms -> exists R pc' m', ms = MState.MS R fp_regs pc' fp_csr None m' (seg_rom rsegs) /\
     (exists W, Frame.munch W (normalize rsegs mem) m' /\ Frame.wmono rsegs (normalize rsegs mem) m' /\
        (forall lo hi y, In (lo, hi) W -> lo <= y < hi -> kreg g hb y \/ g_S g - 104 <= y < g_S g)) /\
     bytes_at rsegs m' (g_S g - 104) (saved_bytes ra g) /\
     getr R 2 = getr regs 2 /\ getr R 3 = getr regs 3 /\ getr R 4 = getr regs 4) ->
  (forall R pc' m0' regs' m', Q (MState.MS R fp_regs pc' fp_csr None m0' (seg_rom rsegs)) ->
     Regs6ss.xregs_eqv R regs' -> mem_rel rsegs m' m0' ->
     FR B APIf ra empty g km hb L A regs' m' md ->
     SRcf B (mkCfg (mkst regs' pc' m' (seg_rom (ms_segs B))) md) P) ->
  SRcf B (mkCfg (mkst regs pc mem (seg_rom (ms_segs B))) md) P.
Proof.
  intros g km hb L A regs mem md pc Q P HFR HP HE Hform HK.
  pose proof (ss_segs B APIf ra empty FF) as SEGS.
  pose proof HFR as (HGV & _ & _ & _ & Hsv & _ & HMI & _ & HM & _).
  pose proof HGV as (_ & _ & _ & _ & HSc & HS47 & _).
  pose proof alloc_ceiling_value as HAC.
  unfold MI in HMI. rewrite SEGS in HMI.
  destruct (mr_model B _ (aa_laws (APIf rc)) _ _ _ _ HM) as (Hh & Hl & _).
  apply (ss_run_cf regs pc mem md Q P Hh Hl HMI HE).
  - intros ms HQ. destruct (Hform ms HQ) as (R & pc' & m' & -> & _). exists R, pc', m'. reflexivity.
  - intros R pc' m0' HQ regs' m' Hx Hrel Hsame.
    destruct (Hform _ HQ) as (R1 & pc1 & m1 & E & (W & MU & WM & HW) & HSV & E2 & E3 & E4).
    injection E; intros; subst.
    pose proof (mem_rel_normalize rsegs mem HMI) as HR0.
    apply (HK R1 pc1 m1 regs' m' HQ Hx Hrel).
    pose proof (munch_rel rsegs W mem (normalize rsegs mem) m' m1 HR0 Hrel Hsame MU) as MU'.
    pose proof (wmono_rel rsegs mem (normalize rsegs mem) m' m1 HR0 Hrel Hsame WM) as WM'.
    apply (proj2 (bytes_at_rel rsegs m' m1 _ _ Hrel)) in HSV.
    apply (ss_FR_kA B APIf ra empty FF g km hb L A regs mem md regs' m' HFR HP).
    + rewrite (ss_getr_eqv _ _ _ Hx). exact E2.
    + rewrite (ss_getr_eqv _ _ _ Hx). exact E3.
    + rewrite (ss_getr_eqv _ _ _ Hx). exact E4.
    + intros x Hx64 Hk.
      assert (Hdec : (g_S g - 104 <= x < g_S g) \/ ~ (g_S g - 104 <= x < g_S g)) by lia.
      destruct Hdec as [Hs|Hs].
      * apply (sm_saved_eq ra g mem m' x Hsv HSV); [unfold IMG_HI, SLOT_K, SLOT_STACK in *; lia | lia | exact Hs].
      * apply MU'. rewrite (unsigned_lit x Hx64).
        apply (ss_outside (fun y => kreg g hb y \/ g_S g - 104 <= y < g_S g) W x HW). tauto.
    + exact WM'.
Qed.

Lemma cut_open_cf : forall g pc km hb P c (Q : config -> Prop),
  CUTST B APIf ra empty g pc km hb P c ->
  (forall L A regs mem md, FR B APIf ra empty g km hb L A regs mem md ->
     Permutation (blocks L A) (hb ++ blocks (g_L g) (g_A g)) -> P regs mem ->
     SRcf B (mkCfg (mkst regs (Z_to_bv 64 pc) mem (seg_rom (ms_segs B))) md) Q) ->
  SRcf B c Q.
Proof.
  intros g pc km hb P c Q (L & A & regs & mem & md & -> & H1 & H2 & H3) K. exact (K L A regs mem md H1 H2 H3).
Qed.

End T.

Section M.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AllocAPI B.
Context {LS : lib_shape} {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Hypothesis FF : frame_facts B APIf LS SH SK ra empty.
Hypothesis MALLOC : malloc_contract_cf B (APIf rc).
Hypothesis LIMLAW : forall L A mem md, aa_MR (APIf rc) L A mem md -> SRC_LIM_MIN <= vm_limit (m_vmmaps md).
Let API := APIf rc.
Let MR := aa_MR API.

Lemma ss_malloc_step_cf : forall g, capag g -> forall km hb L A regs mem md n P,
  FR B APIf ra empty g km hb L A regs mem md ->
  Permutation (blocks L A) (hb ++ blocks (g_L g) (g_A g)) ->
  (length hb <= 16)%nat -> 0 <= hb_bytes hb <= 2 ^ 24 -> 0 <= n <= 2 ^ 20 ->
  YK0s.ret_ok (getr regs 1) -> getr regs 10 = Z_to_bv 64 n ->
  (forall L' A' regs' mem' md' res,
     FR B APIf ra empty g (km + 1) (hb ++ [(res, n)]) L' A' regs' mem' md' ->
     Permutation (blocks L' A') ((hb ++ [(res, n)]) ++ blocks (g_L g) (g_A g)) ->
     regs_preserved regs regs' -> getr regs' 10 = Z_to_bv 64 res -> res <> 0 ->
     (forall x, fsp g <= x < g_S g -> mbyte (ms_segs B) mem' x = mbyte (ms_segs B) mem x) ->
     (forall a k i, In (a, k) hb -> 0 <= i < k -> mbyte (ms_segs B) mem' (a + i) = mbyte (ms_segs B) mem (a + i)) ->
     SRcf B (mkCfg (mkst regs' (getr regs 1) mem' (seg_rom (ms_segs B))) md') P) ->
  SRcf B (mkCfg (mkst regs (Z_to_bv 64 (ms_malloc B)) mem (seg_rom (ms_segs B))) md) P.
Proof.
  intros g HCAP km hb L A regs mem md n P HF HP Hlen Hhb Hn HRA H10 HK.
  pose proof (ss_spZ B APIf ra empty _ _ _ _ _ _ _ _ HF) as SPZ.
  pose proof (ss_call_pre B APIf ra empty _ _ _ _ _ _ _ _ HF HRA) as CP.
  pose proof HF as (HGV & Hsp & Hgp & Htp & Hsv & Hstk & HMI & Hrel & HMR & HWF & HBD & HIN & Hmd & Hhi & Himg & HB0
    & Her & Hsk & HRS & Hwin).
  pose proof HGV as (Hn0 & Hnp & Hblk & HS16 & HSc & HS47 & Hroom & HgS & HgT).
  pose proof (@YM05.alloc_ceiling_val rc) as HAC. pose proof (ss_errc B APIf ra empty FF) as ERC.
  pose proof (room_cf_of md (g_b g) hb n Hroom HCAP Hlen Hhb Hn (LIMLAW L A mem md HMR)) as ROOM.
  eapply (SRcf_bind B); [exact (MALLOC L A regs mem md n (sb_hb (g_b g) hb) CP HMI H10 HRS ROOM)|].
  intros c' (L' & A' & regs' & mem' & md' & res & -> & HC & R10 & Hr0 & Hr16 & Hfr & (b1 & b2 & Eb' & Eb) & Hkept
    & HRO' & HGK & HUB & HIN' & HLEN & HRES').
  assert (HP' : Permutation (blocks L' A') ((hb ++ [(res, n)]) ++ blocks (g_L g) (g_A g))).
  { rewrite Eb', <- app_assoc. cbn [app].
    apply Permutation_trans with ((res, n) :: (b1 ++ b2)); [apply Permutation_sym, Permutation_middle|].
    rewrite <- Eb. apply Permutation_trans with ((res, n) :: hb ++ blocks (g_L g) (g_A g)); [apply perm_skip; exact HP|].
    apply Permutation_middle. }
  assert (HF' : FR B APIf ra empty g (km + 1) (hb ++ [(res, n)]) L' A' regs' mem' md').
  { apply (ss_FR_call B APIf ra empty FF g km hb L A regs mem md (fun _ => False) L' A' regs' mem' md' (km + 1)
      (hb ++ [(res, n)]) HF HC).
    - intros a [].
    - intros a k i Hin Hi. apply (Hkept a k i); [|intros []|exact Hi].
      apply (Permutation_in _ (Permutation_sym HP)). apply in_or_app. right. exact Hin.
    - exact HRO'.
    - exact HIN'.
    - exact (resb_malloc (g_b g) (km + 1) hb (hb ++ [(res, n)]) A' res n
               (Permutation_sym (Permutation_cons_append hb (res, n))) HRES'). }
  destruct HC as (_ & _ & _ & _ & _ & RP' & _ & FR' & _ & _).
  apply (HK L' A' regs' mem' md' res HF' HP' RP' R10 Hr0).
  - intros x Hx. unfold fsp, SLOT_FRAME in Hx. unfold SLOT_K, SLOT_STACK in HSc. apply FR'.
    + left. lia.
    + intros Ho. pose proof (mr_owned_low B MR (ss_laws B APIf) L A mem md x HMR Ho). lia.
    + intros Ho. destruct HF' as (_ & _ & _ & _ & _ & _ & _ & _ & HMR' & _).
      pose proof (mr_owned_low B MR (ss_laws B APIf) L' A' mem' md' x HMR' Ho). lia.
    + unfold scratch_k. rewrite SPZ. unfold ALLOC_STACK. lia.
    + intros [].
  - intros a k i Hin Hi. apply (Hkept a k i); [|intros []|exact Hi].
    apply (Permutation_in _ (Permutation_sym HP)). apply in_or_app. left. exact Hin.
Qed.

End M.

Section F.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AllocAPI B.
Context {LS : lib_shape} {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Hypothesis FF : frame_facts B APIf LS SH SK ra empty.
Hypothesis FREE : free_contract_cf B (APIf rc).
Let API := APIf rc.
Let MR := aa_MR API.

Lemma ss_free_step_cf : forall g km hb1 a n hb2 L A regs mem md P,
  FR B APIf ra empty g km (hb1 ++ (a, n) :: hb2) L A regs mem md ->
  Permutation (blocks L A) ((hb1 ++ (a, n) :: hb2) ++ blocks (g_L g) (g_A g)) ->
  0 < n <= MMAP_THRESHOLD ->
  YK0s.ret_ok (getr regs 1) -> getr regs 10 = Z_to_bv 64 a ->
  (forall L' A' regs' mem' md',
     FR B APIf ra empty g km (hb1 ++ hb2) L' A' regs' mem' md' ->
     Permutation (blocks L' A') ((hb1 ++ hb2) ++ blocks (g_L g) (g_A g)) ->
     regs_preserved regs regs' ->
     (forall x, fsp g <= x < g_S g -> mbyte (ms_segs B) mem' x = mbyte (ms_segs B) mem x) ->
     SRcf B (mkCfg (mkst regs' (getr regs 1) mem' (seg_rom (ms_segs B))) md') P) ->
  SRcf B (mkCfg (mkst regs (Z_to_bv 64 (ms_free B)) mem (seg_rom (ms_segs B))) md) P.
Proof.
  intros g km hb1 a n hb2 L A regs mem md P HF HP Hn HRA H10 HK.
  pose proof (ss_spZ B APIf ra empty _ _ _ _ _ _ _ _ HF) as SPZ.
  pose proof (ss_call_pre B APIf ra empty _ _ _ _ _ _ _ _ HF HRA) as CP.
  pose proof HF as (HGV & Hsp & Hgp & Htp & Hsv & Hstk & HMI & Hrel & HMR & HWF & HBD & HIN & Hmd & Hhi & Himg & HB0
    & Her & Hsk & HRS & Hwin).
  pose proof HGV as (Hn0 & Hnp & Hblk & HS16 & HSc & HS47 & Hroom & HgS & HgT).
  pose proof (@YM05.alloc_ceiling_val rc) as HAC. pose proof (ss_errc B APIf ra empty FF) as ERC.
  pose proof (Permutation_sym (Permutation_middle hb1 hb2 (a, n))) as HPm.
  assert (Hab : In (a, n) (blocks L A)).
  { apply (Permutation_in _ (Permutation_sym HP)). apply in_or_app. left. apply in_or_app. right. left. reflexivity. }
  destruct (ss_blk_of L A a n Hab) as (p & Hp & Epa).
  eapply (SRcf_bind B);
    [exact (FREE L A regs mem md p n (sb_hb (g_b g) (hb1 ++ (a, n) :: hb2)) CP HMI Hp ltac:(rewrite Epa; exact H10) HRS)|].
  intros c' (L' & A' & regs' & mem' & md' & -> & HC & (b1 & b2 & Eb & Eb') & Hkept & HRO' & HGK & HUB & HINi & HLEN
    & HRES').
  rewrite Epa in Eb, Hkept, HC.
  try (apply call_post_k_alloc in HC).
  assert (HP' : Permutation (blocks L' A') ((hb1 ++ hb2) ++ blocks (g_L g) (g_A g))).
  { rewrite Eb', <- app_assoc. apply (Permutation_app_inv _ _ _ _ (a, n)).
    rewrite <- Eb. rewrite <- app_assoc in HP. cbn [app] in HP. exact HP. }
  assert (HF' : FR B APIf ra empty g km (hb1 ++ hb2) L' A' regs' mem' md').
  { apply (ss_FR_call B APIf ra empty FF g km (hb1 ++ (a, n) :: hb2) L A regs mem md _ L' A' regs' mem' md' km
      (hb1 ++ hb2) HF HC).
    - intros x Hx. destruct (ss_blk_facts B APIf ra empty FF L A mem md a n (x - a) HMR Hab ltac:(lia))
        as (_ & H2 & H3 & _ & H5).
      replace (a + (x - a)) with x in H5 by lia. split; [lia | exact H5].
    - intros a' k i Hin Hi. apply (Hkept a' k i); [| | exact Hi].
      + apply (Permutation_in _ (Permutation_sym HP)). apply in_or_app. right. exact Hin.
      + intros Ea. subst a'.
        destruct (ss_b0_facts B APIf ra empty FF L A mem md _ _ a k 0 HMR HP Hin ltac:(lia)) as (_ & _ & Hnh0).
        apply Hnh0. exists a, n. split; [apply in_or_app; right; left; reflexivity | lia].
    - exact HRO'.
    - exact (HINi HIN).
    - apply (resb_free (g_b g) km (hb1 ++ (a, n) :: hb2) (hb1 ++ hb2) A' a n HPm).
      exact HRES'. }
  destruct HC as (_ & _ & _ & _ & _ & RP' & _ & FR' & _ & _).
  apply (HK L' A' regs' mem' md' HF' HP' RP').
  intros x Hx. unfold fsp, SLOT_FRAME in Hx. unfold SLOT_K, SLOT_STACK in HSc. apply FR'.
  - left. lia.
  - intros Ho. pose proof (mr_owned_low B MR (ss_laws B APIf) L A mem md x HMR Ho). lia.
  - intros Ho. destruct HF' as (_ & _ & _ & _ & _ & _ & _ & _ & HMR' & _).
    pose proof (mr_owned_low B MR (ss_laws B APIf) L' A' mem' md' x HMR' Ho). lia.
  - unfold scratch, scratch_k. rewrite SPZ. unfold ALLOC_STACK. lia.
  - cbn. destruct (ss_blk_facts B APIf ra empty FF L A mem md a n 0 HMR Hab ltac:(lia)) as (_ & H2 & H3 & _). lia.
Qed.

End F.
