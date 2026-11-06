(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Copyright 2026 Theorem Labs *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-repacer/fuzz_uci/lib/Prog/LLVMFuzzerTestOneInput_c.v, with its module paths changed; 150 of its 167 lines of code are new or changed and 50 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-repacer/fuzz_lock/lib/Prog/FrameRet.v, with its module paths and addresses changed; 232 of its 268 lines of code are new or changed and 131 lines of the source are left out. *)
(* The cut-free (agreement) form of the slot of reac-pw/fuzz_segconf LLVMFuzzerTestOneInput (UBSan, [0x13888,
   0x14268)): U/Prog/SlotFR.v and U/Prog/SlotInv.v with SR := SRcf, in the form of reac-pw/fuzz_pin's
   U/Prog/SlotInvCF.v (commit a2a7540da98; itself libreac/fuzz_ctrl's released U/Prog/SlotInvCF.v,
   commit 25e3d17bdb50). The U segment files of the slot (U/Prog/Seg/*.v, U/Prog/SegSlot.v) are copied
   to U/Prog/SegCF/*.v over this file, which each copy imports after SlotFR and SlotInv. Changes:
   - SR, its lemmas, Contract.evt_SR(_canon) and KindBGlue.kb_run are redefined under the same names (pin's block,
     verbatim), so the copied segment proofs prove the cut-free run (crealizes: realizes, cut_free and uniform,
     U/SlotAgree.v);
   - frame_facts_cf: U/FrameAPI.frame_facts_ubsan, conjunct for conjunct, with the agreement room
     (128 <= sb_cap <= CAP_AG) and the cut-free allocator frame_allocator_cf (malloc as malloc_contract_cfg, whose room
     is room_ag; free and free of NULL in cut-free form); calloc_contract_cfg is
     CallocBigC.calloc_contract_big in the same form (room_ag, SR := SRcf), the premise of the CF b1_calloc_call;
   - slot_room: 128 <= sb_cap <= CAP_AG (the agreement frame's entry bound sb_cap = CAP_AG); GV, FR, CUTST and
     Inv_ENTRY are restated over it; resb_room gives room_ag (sb_bytes + n <= 2^29: 2^28 + 2^24 + 2^26 for at most 16
     blocks of at most 2^24 bytes and a request of at most 2^26; segconf asks at most 65536 bytes with at most 26572
     live);
   - Hcut, Hat (over SlotFR.Post, which does not mention SR) and the cuts Inv_K13984 .. Inv_K141ec over the CF CUTST,
     with SlotInv's block lists hb_* and cut record cut_preds (the same record, so one record of cut predicates fills
     both slots);
   - slot_goal: lib_contract_cg with G = frame_G (longl, 0x33460) and GI = GI_SLOT (longl[120] = 0);
   - FR_u_of_cf: the CF frame gives U/SlotFR's (the evt statements of the walks are stated over U/SlotFR.FR).
   The ghost record, the resources (sb_hb, RESB, RES_END, resb_malloc/free/start/end), rg, MI, relro, saved_bytes,
   LONGL, GIb, GI_SLOT and Post are U/Prog/SlotFR.v's. Statement text and the SR block: no function is proved here. *)
From Stdlib Require Import ZArith List Bool Lia Permutation Wf_nat Wellfounded.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.U.Reusable Require Import YK11 YK0i YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.U.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.U.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.U.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Lib Require Import Mem Frame.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.U Require Import Img0 Contract FrameAPI AllocRoom SlotAgree AgreeLift.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Lib Require Exec RegisterBridge Regs6ss MState.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.U Require KindBGlue CallocBigC.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.U.Prog Require Import SlotFR SlotInv.
Import ListNotations.
Open Scope Z_scope.

(* The cut-free run relation under the names of YM06.SR and its lemmas and U/Contract.v's evt_SR(_canon): a run
   relation whose realizes also carries cut_free and uniform (crealizes, SlotAgree.v), so the copied segment proofs,
   which use only these names, prove the cut-free run. *)
Definition seg_syms (segs : list Segment) : malloc_syms := MSyms segs (MPcs 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 None None) 0 0 None 0 0 0 0 0 None 0 0 0 0 0 0 None None 0.

Definition SR (segs : list Segment) (c : config) (Q : config -> Prop) : Prop := SRcf (seg_syms segs) c Q.

Lemma SR_ret : forall segs c (Q : config -> Prop), Q c -> SR segs c Q.
Proof. intros segs c Q HQ. exact (SRcf_ret (seg_syms segs) c Q HQ). Qed.

Lemma SR_bind : forall segs c (R Q : config -> Prop), SR segs c R -> (forall c', R c' -> SR segs c' Q) ->
  SR segs c Q.
Proof. intros segs c R Q H1 H2. exact (SRcf_bind (seg_syms segs) c R Q H1 H2). Qed.

Lemma SR_mono : forall segs c (Q Q' : config -> Prop), SR segs c Q -> (forall c', Q c' -> Q' c') ->
  SR segs c Q'.
Proof. intros segs c Q Q' H HQ. exact (SRcf_mono (seg_syms segs) c Q Q' H HQ). Qed.

Lemma SR_realizes : forall segs c Q T, SR segs c Q ->
  (forall c', Q c' -> crealizes (seg_syms segs) c' T) -> crealizes (seg_syms segs) c T.
Proof. intros segs c Q T H HK. exact (H T HK). Qed.

Lemma SR_realizes_ms : forall (B : malloc_syms) segs, ms_segs B = segs -> forall c Q T, SR segs c Q ->
  (forall c', Q c' -> crealizes B c' T) -> crealizes B c T.
Proof. intros B segs E c Q T H HK. subst segs. exact (H T HK). Qed.

Lemma SR_msteps : forall segs ms ms' model Q, m_halted model = None -> m_vm_lazy model = [] ->
  msteps segs ms ms' -> SR segs (mkCfg ms' model) Q -> SR segs (mkCfg ms model) Q.
Proof.
  intros segs ms ms' model Q Hh Hl Hms H T HK.
  exact (crealizes_msteps (seg_syms segs) ms ms' model T Hh Hl Hms (H T HK)).
Qed.

Lemma SR_step : forall segs ms model ms' Q, m_halted model = None -> m_vm_lazy model = [] ->
  ms_svc_pending ms = None -> RiscvSemantics.step segs ms = MachineOk ms' ->
  SR segs (mkCfg ms' model) Q -> SR segs (mkCfg ms model) Q.
Proof.
  intros segs ms model ms' Q Hh Hl Hs Hst H.
  exact (SR_msteps segs ms ms' model Q Hh Hl (mst_step segs ms ms' ms' Hs Hst (mst_refl segs ms')) H).
Qed.

Lemma SR_case : forall segs (A : Prop) c Q, (A \/ ~ A) -> (A -> SR segs c Q) -> (~ A -> SR segs c Q) ->
  SR segs c Q.
Proof. intros segs A c Q [a|na] H1 H2; [exact (H1 a) | exact (H2 na)]. Qed.

Lemma SR_wf : forall segs (W : Type) (R : W -> W -> Prop), well_founded R ->
  forall (P : W -> config -> Prop) (Q : config -> Prop),
  (forall w c, P w c -> SR segs c (fun c' => Q c' \/ exists w', R w' w /\ P w' c')) ->
  forall w c, P w c -> SR segs c Q.
Proof.
  intros segs W R Hwf P Q Hb w. induction (Hwf w) as [w _ IH]. intros c HP.
  apply (SR_bind segs c _ Q (Hb w c HP)). intros c' [HQ | (w' & HR & HP')].
  - exact (SR_ret segs c' Q HQ).
  - exact (IH w' HR c' HP').
Qed.

Lemma SR_loop : forall segs (W : Type) (m : W -> nat) (P : W -> config -> Prop) (Q : config -> Prop),
  (forall w c, P w c -> SR segs c (fun c' => Q c' \/ exists w', (m w' < m w)%nat /\ P w' c')) ->
  forall w c, P w c -> SR segs c Q.
Proof.
  intros segs W m P Q Hb. apply (SR_wf segs W (fun a b => (m a < m b)%nat)); [|exact Hb].
  apply (wf_inverse_image W nat lt m), PeanoNat.Nat.lt_wf_0.
Qed.

Lemma SR_loopZ : forall segs (W : Type) (m : W -> Z) (P : W -> config -> Prop) (Q : config -> Prop),
  (forall w c, P w c -> SR segs c (fun c' => Q c' \/ exists w', (0 <= m w' < m w)%Z /\ P w' c')) ->
  forall w c, P w c -> SR segs c Q.
Proof.
  intros segs W m P Q Hb. apply (SR_wf segs W (fun a b => (0 <= m a < m b)%Z)); [|exact Hb].
  apply (wf_inverse_image W Z (fun x y => (0 <= x < y)%Z) m). apply Z.lt_wf with (z := 0%Z).
Qed.

Lemma evt_SR : forall segs ms (Q : machine_state -> Prop) md (P : config -> Prop),
  Exec.evt segs Q ms -> m_halted md = None -> m_vm_lazy md = [] ->
  (forall ms', Q ms' -> SR segs (mkCfg ms' md) P) -> SR segs (mkCfg ms md) P.
Proof. intros segs ms Q md P H Hh Hl K. exact (evt_SRcf (seg_syms segs) ms Q md P H Hh Hl K). Qed.

Lemma evt_SR_canon : forall segs ms (Q : machine_state -> Prop) md (P : config -> Prop),
  Exec.evt segs Q (RegisterBridge.canonical_register_state ms) -> m_halted md = None -> m_vm_lazy md = [] ->
  (forall ms', (exists can, Q can /\ Regs6ss.ms_eqv can ms') -> SR segs (mkCfg ms' md) P) ->
  SR segs (mkCfg ms md) P.
Proof. intros segs ms Q md P H Hh Hl K. exact (evt_SRcf_canon (seg_syms segs) ms Q md P H Hh Hl K). Qed.

(* The cut-free form of KindBGlue.kb_run (same name; the segment files import this file after KindBGlue). *)
Section KBR.
Context {fx : FPState}.

Lemma kb_run : forall (B : malloc_syms) regs pc mem md (K : bvmap 5 word -> word -> (word -> option byte) -> Prop)
  (P : config -> Prop),
  m_halted md = None -> m_vm_lazy md = [] ->
  Exec.evt (ms_segs B) (fun ms => exists R pc' mem', ms = MState.MS R fp_regs pc' fp_csr None mem' (seg_rom (ms_segs B))
    /\ K R pc' mem')
    (MState.MS (KindBGlue.rmk regs) fp_regs pc fp_csr None mem (seg_rom (ms_segs B))) ->
  (forall R pc' mem' regs', K R pc' mem' -> (forall r, getr regs' r = getr R r) ->
     SR (ms_segs B) (mkCfg (mkst regs' pc' mem' (seg_rom (ms_segs B))) md) P) ->
  SR (ms_segs B) (mkCfg (mkst regs pc mem (seg_rom (ms_segs B))) md) P.
Proof.
  intros B regs pc mem md K P Hh Hl HE HK.
  eapply (evt_SR_canon (ms_segs B) (mkst regs pc mem (seg_rom (ms_segs B))) _ md P); [exact HE | exact Hh | exact Hl |].
  intros ms' (can & (R & pc' & mem' & -> & HKR) & Heq).
  destruct Heq as (HR & HF & Hpc & Hsvc & Hres & Hfc & Hm & Hrom).
  destruct ms' as [regs' fr' pcv' svc' rv' fc' m' ro'].
  cbn in HR, HF, Hpc, Hsvc, Hres, Hfc, Hm, Hrom. subst.
  apply (HK R _ _ regs' HKR). apply KindBGlue.kb_getr_eqv. exact HR.
Qed.

End KBR.

(* The slot's allocator room in the agreement frame: room_slots, and the cap and bytes bounds that room_cf needs. *)
Definition room_ag (b : sbound) (n : Z) : Prop := room_slots b n /\ 0 <= sb_cap b <= CAP_AG /\ sb_bytes b + n <= 2 ^ 29.

(* The cut-free allocator contracts the slot's calls use: U/FrameAPI.frame_allocator with malloc, free and free of
   NULL in cut-free form (malloc with the agreement room), and calloc at CALLOC_PC (
   CallocBigC.calloc_contract_big with SR := SRcf and the agreement room). *)
Definition malloc_contract_cfg {rc : RunCeil} {fx : FPState} (B : malloc_syms) (API : AllocAPI B) : Prop :=
  forall L A regs mem md n b,
    call_pre B (aa_MR API) L A regs mem md -> ro_agree (ms_segs B) mem -> getr regs 10 = Z_to_bv 64 n ->
    res_ok_slots A b -> room_ag b n ->
    SR (ms_segs B) (mkCfg (mkst regs (Z_to_bv 64 (ms_malloc B)) mem (seg_rom (ms_segs B))) md)
      (malloc_ret B API ALLOC_STACK L A regs mem md n b).

Definition calloc_contract_cfg {rc : RunCeil} {fx : FPState} (B : malloc_syms) (API : AllocAPI B) (pc : Z) : Prop :=
  forall L A regs mem md m n b,
    call_pre_k B (aa_MR API) CALLOC_STACK L A regs mem md -> ro_agree (ms_segs B) mem ->
    getr regs 10 = Z_to_bv 64 m -> getr regs 11 = Z_to_bv 64 n -> 0 <= m -> 0 <= n ->
    m * n <= CallocBigC.CALLOC_BIG_CAP ->
    res_ok_slots A b -> room_ag b (m * n) ->
    SR (ms_segs B) (mkCfg (mkst regs (Z_to_bv 64 pc) mem (seg_rom (ms_segs B))) md)
      (fun c' => malloc_ret B API CALLOC_STACK L A regs mem md (m * n) b c' /\
         exists ms' md', c' = mkCfg ms' md' /\
           forall i, 0 <= i < m * n ->
             mbyte (ms_segs B) (ms_mem ms') (bv_unsigned (getr (ms_regs ms') 10) + i) = Some (Z_to_bv 8 0)).

Definition frame_allocator_cf {rc : RunCeil} {fx : FPState} (B : malloc_syms) (API : AllocAPI B) : Prop :=
  malloc_contract_cfg B API /\ free_contract_cf B API /\ free_null_contract_cf B /\
  (forall pc, ms_realloc B = Some pc -> realloc_contract B API pc /\ realloc_null_contract B API pc) /\
  (forall pc, ms_calloc B = Some pc -> calloc_contract B API pc) /\
  block_slack_present B API /\ ctx_owned B API /\ blocks_low B API /\ blocks_nodup B API /\ blocks_writable B API /\ errno_unowned B API /\
  guard_rw B API /\ libc_no_locks B API /\
  AllocExtra B (aa_MR API) /\
  (forall L A mem md a, aa_MR API L A mem md -> in_globals frame_G a -> ~ owned B L A a) /\
  (forall L A mem md a, aa_MR API L A mem md -> in_globals frame_RELRO a -> ~ owned B L A a).

(* U/FrameAPI.frame_facts_ubsan, conjunct for conjunct, with the agreement room and the cut-free allocator. *)
Definition frame_facts_cf (B : malloc_syms) (API : forall rc : RunCeil, AllocAPI B)
    (LS : lib_shape) (SH : sink_head) (SK : sink_syms) (ra empty : Z) : Prop :=
    ms_segs B = rsegs /\ ra mod 2 = 0 /\
    ms_malloc B = 0x17518 /\ ms_free B = 0x173d8 /\ ms_realloc B = None /\ ms_calloc B = None /\
    (forall rc : RunCeil, errno_addr B + 4 <= @alloc_ceiling rc) /\
    ms_guard B = 0x53820 /\ ms_got_guard B = 0x221b0 /\
    ms_ctx B = 0x538b8 /\ ms_lock B = 0x538b0 /\ ms_libc B = 0x53840 /\ ms_size_classes B = 0x11350 /\
    ms_small_cnt B = 0x113b0 /\ ms_med_cnt B = 0x113cb /\ ms_debruijn B = 0x11330 /\ ms_tp B = 0x335b0 /\
    ms_errno_off B = -164 /\ ms_replaced B = None /\ ms_vmlock B = None /\ ms_debruijn_len B = 32 /\
    @sk_ofl_head SH = 0x53c70 /\ @sk_ofl_lock SK = 0x53c68 /\ @sk_threaded SK = 0x53840 + 1 /\
    empty = 0x33440 /\ 0 < empty < 2 ^ 62 /\
    (forall a, ms_ctx B <= a < ms_ctx B + CTX_SIZE -> Mem.ro_addr (ms_segs B) (Z_to_bv 64 a) = false) /\
    (forall a, in_globals frame_G a -> in_img B a /\ ~ static_owned B a /\ ~ (ms_ctx B <= a < ms_ctx B + CTX_SIZE) /\
       ~ (errno_addr B <= a < errno_addr B + 4)) /\
    (forall a, in_globals frame_RELRO a ->
       in_img B a /\ ~ static_owned B a /\ ~ (ms_ctx B <= a < ms_ctx B + CTX_SIZE) /\
       ~ (errno_addr B <= a < errno_addr B + 4)) /\
    (forall pl fs K, @LIBK LS pl fs K = K (LL 0 fs [])) /\
    (forall n b, @lib_delta LS n b = b) /\
    (forall b n, @lib_room LS b n -> sb_live b <= 64 /\ 0 <= sb_bytes b <= 2 ^ 28 /\ 128 <= sb_cap b <= CAP_AG) /\
    (forall (rc : RunCeil) (fx : FPState), @frame_allocator_cf rc fx B (API rc)).

(* The slot's entry bound in the agreement frame: sb_cap = CAP_AG there. *)
Definition slot_room (b : sbound) : Prop :=
  sb_live b <= 64 /\ 0 <= sb_bytes b <= 2 ^ 28 /\ 128 <= sb_cap b <= CAP_AG.

Lemma slot_room_u : forall b, slot_room b -> SlotFR.slot_room b.
Proof.
  intros b (H1 & H2 & H3). unfold SlotFR.slot_room. split; [exact H1|]. split; [exact H2|].
  split; [lia|]. apply (Z.le_trans _ CAP_AG); [lia | apply Z.leb_le; vm_compute; reflexivity].
Qed.

(* room_ag at the request bound 2^26 (pin's room_ag_big): room_slots from AllocRoom.room_slots_big, the cap below
   CAP_AG, the bytes below 2^29. *)
Lemma room_ag_big : forall b n, sb_live b + 1 <= sb_cap b -> 128 <= sb_cap b <= CAP_AG ->
  0 <= sb_bytes b -> sb_bytes b + n <= 2 ^ 29 -> 0 <= n <= 2 ^ 26 -> room_ag b n.
Proof.
  intros b n Hl Hc Hb Hbn Hn. split; [|split; lia].
  apply room_slots_big; [lia | | lia | lia]. split; [lia|].
  apply (Z.le_trans _ CAP_AG); [lia | apply Z.leb_le; vm_compute; reflexivity].
Qed.

(* The request bound is 2^26 for any hb of at most 16 blocks and 2^24 bytes: sb_bytes + n <= 2^28 + 2^24 + 2^26. *)
Lemma resb_room : forall b0 hb n, slot_room b0 -> (length hb <= 16)%nat ->
  0 <= hb_bytes hb <= 2 ^ 24 -> 0 <= n <= 2 ^ 26 -> room_ag (sb_hb b0 hb) n.
Proof.
  intros b0 hb n (HL & HB & HC) Hlen HS Hn.
  unfold sb_hb. apply room_ag_big; cbn [sb_live sb_bytes sb_cap]; lia.
Qed.

Section Slot.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AllocAPI B.
Context {LS : lib_shape} {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Let API := APIf rc.
Let segs := ms_segs B.
Let MR := aa_MR API.

(* GV: the ghost facts (U/SlotFR.GV with the agreement slot_room). *)
Definition GV (g : ghost) : Prop :=
  0 <= g_n g < 2 ^ 26 /\
  ((g_n g = 0 /\ g_p g = empty) \/ (0 < g_n g /\ In (g_p g, g_n g) (blocks (g_L g) (g_A g)))) /\
  blk_data B (g_mem g) (g_p g) (g_in g) /\
  g_S g mod 16 = 0 /\ alloc_ceiling + SLOT_K <= g_S g /\ g_S g <= 2 ^ 47 /\
  slot_room (g_b g) /\
  getr (g_regs g) 2 = Z_to_bv 64 (g_S g) /\ getr (g_regs g) 4 = Z_to_bv 64 (ms_tp B) /\
  GIb (ms_segs B) (g_mem g).

(* FR: U/SlotFR.FR over GV. *)
Definition FR (g : ghost) (hb : list (Z * Z)) (L : layout) (A : astate) (regs : bvmap 5 word)
    (mem : word -> option byte) (md : Model) : Prop :=
  GV g /\
  getr regs 2 = Z_to_bv 64 (fsp g) /\ getr regs 3 = getr (g_regs g) 3 /\ getr regs 4 = getr (g_regs g) 4 /\
  bytes_at rsegs mem (g_S g - SLOT_SAVE) (saved_bytes ra g) /\
  stk rsegs mem (g_S g - SLOT_K) (g_S g) /\
  MI B mem /\ relro B mem /\
  MR L A mem md /\ WF A /\ bounded A /\ st_init_done A = true /\
  (exists vm, md = with_vmmaps vm (g_md g)) /\
  (forall a, alloc_ceiling <= a < 2 ^ 64 -> ~ (g_S g - SLOT_K <= a < g_S g) ->
     ~ (errno_addr B <= a < errno_addr B + 4) ->
     mbyte segs mem a = mbyte segs (g_mem g) a /\ (writable_at segs (g_mem g) a <-> writable_at segs mem a)) /\
  (forall a, in_img B a -> ~ static_owned B a -> ~ (ms_ctx B <= a < ms_ctx B + CTX_SIZE) ->
     ~ (errno_addr B <= a < errno_addr B + 4) -> ~ (LONGL <= a < LONGL + LONGL_W) ->
     mbyte segs mem a = mbyte segs (g_mem g) a /\ (writable_at segs (g_mem g) a <-> writable_at segs mem a)) /\
  (forall a k i, In (a, k) (blocks (g_L g) (g_A g)) -> 0 <= i < k ->
     mbyte segs mem (a + i) = mbyte segs (g_mem g) (a + i)) /\
  (forall a, errno_addr B <= a < errno_addr B + 4 -> writable_at segs mem a) /\
  sink_none B mem md /\ RESB (g_b g) hb A /\
  (forall a, g_S g - SLOT_K <= a < g_S g -> writable_at segs mem a).

Definition CUTST (g : ghost) (pc : Z) (hb : list (Z * Z))
    (P : bvmap 5 word -> (word -> option byte) -> Prop) (c : config) : Prop :=
  exists (fx' : YK11.FPState) L A regs mem md,
    c = mkCfg (@YK11.mkst fx' regs (Z_to_bv 64 pc) mem (seg_rom segs)) md /\
    frm_zero (@YK11.fp_csr fx') /\
    FR g hb L A regs mem md /\
    Permutation (blocks L A) (hb ++ blocks (g_L g) (g_A g)) /\
    P regs mem.

Definition Inv_ENTRY (g : ghost) (c : config) : Prop :=
  c = mkCfg (mkst (g_regs g) (Z_to_bv 64 ENTRY) (g_mem g) (seg_rom segs)) (g_md g) /\
  GV g /\
  lib_pre B API SLOT_STACK empty (g_L g) (g_A g) (g_regs g) (g_mem g) (g_md g) ra (g_p g) (g_n g) /\
  getr (g_regs g) 2 = Z_to_bv 64 (g_S g) /\
  sink_none B (g_mem g) (g_md g) /\ MI B (g_mem g) /\ relro B (g_mem g) /\
  res_ok_slots (g_A g) (g_b g) /\
  frm_zero fp_csr.

(* H(X): every configuration of cut X runs, in the cut-free SR sense, to U/SlotFR.Post. *)
Definition Hcut (X : ghost -> config -> Prop) : Prop := forall g c, X g c -> SR segs c (Post B APIf ra g).

(* The cut-free slot obligation (AgreeFrame.ubsan_agrees_of_slots' U premise): G = frame_G (longl),
   GI = GI_SLOT (longl[120] = 0). *)
Definition slot_goal : Prop :=
  forall j, (j < 4)%nat -> lib_contract_cg B API frame_G frame_RELRO (GI_SLOT segs) j ENTRY ra empty SLOT_STACK.

Lemma GV_u_of_cf : forall g, GV g -> SlotFR.GV B empty g.
Proof.
  intros g (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10).
  exact (conj H1 (conj H2 (conj H3 (conj H4 (conj H5 (conj H6 (conj (slot_room_u _ H7) (conj H8 (conj H9 H10))))))))).
Qed.

(* The CF frame is U/SlotFR's frame with the stronger room bound. *)
Lemma FR_u_of_cf : forall g hb L A regs mem md, FR g hb L A regs mem md ->
  SlotFR.FR B APIf ra empty g hb L A regs mem md.
Proof.
  intros g hb L A regs mem md (HGV & HR). split; [exact (GV_u_of_cf g HGV) | exact HR].
Qed.

End Slot.

(* The cuts of U/Prog/SlotInv.v over the CF CUTST (same pcs, block lists and cut record). *)
Section Cuts.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AllocAPI B.
Context {LS : lib_shape} {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Variable CP : cut_preds.
Let segs := ms_segs B.

Definition Hat {I : Type} (X : ghost -> I -> config -> Prop) (i : I) : Prop :=
  forall g c, X g i c -> SR segs c (Post B APIf ra g).

Definition Inv_K13984 (g : ghost) (c : config) : Prop :=
  exists bc bm, CUTST B APIf ra empty g 0x13984 (hb_cm bc bm) (cp_K13984 CP (g_in g) (g_p g) (g_S g) bc bm) c.

Definition Inv_K139e4 (g : ghost) (f : nat) (c : config) : Prop :=
  (f < 4)%nat /\
  exists bc bm, CUTST B APIf ra empty g 0x139e4 (hb_cm bc bm) (cp_K139e4 CP (g_in g) (g_p g) (g_S g) f bc bm) c.

Definition Inv_K13aac (g : ghost) (f : nat) (c : config) : Prop :=
  exists bc bm t nt,
    CUTST B APIf ra empty g 0x13aac (hb_tcm bc bm t nt) (cp_K13aac CP (g_in g) (g_p g) (g_S g) f bc bm t nt) c.

Definition Inv_K13c34 (g : ghost) (f : nat) (c : config) : Prop :=
  exists bc bm t nt,
    CUTST B APIf ra empty g 0x13c34 (hb_tcm bc bm t nt) (cp_K13c34 CP (g_in g) (g_p g) (g_S g) f bc bm t nt) c.

Definition Inv_K13c3c (g : ghost) (c : config) : Prop :=
  exists bc bm, CUTST B APIf ra empty g 0x13c3c (hb_cm bc bm) (cp_K13c3c CP (g_in g) (g_p g) (g_S g) bc bm) c.

Definition Inv_K13e90 (g : ghost) (c : config) : Prop :=
  exists bc bm tab ntab mt nmt,
    CUTST B APIf ra empty g 0x13e90 (hb_end bc bm tab ntab mt nmt)
      (cp_K13e90 CP (g_in g) (g_p g) (g_S g) bc bm tab ntab mt nmt) c.

Definition Inv_K141ec (g : ghost) (c : config) : Prop :=
  exists bc bm tab ntab mt nmt,
    CUTST B APIf ra empty g 0x141ec (hb_end bc bm tab ntab mt nmt)
      (cp_K141ec CP (g_in g) (g_p g) (g_S g) bc bm tab ntab mt nmt) c.

End Cuts.
