(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Copyright 2026 Theorem Labs *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-repacer/fuzz_uci/lib/Prog/LLVMFuzzerTestOneInput_c.v, with its module paths changed; 150 of its 167 lines of code are new or changed and 50 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-repacer/fuzz_lock/lib/Prog/FrameRet.v, with its module paths, module names and addresses changed; 326 of its 364 lines of code are new or changed and 129 lines of the source are left out. *)
(* The cut-free (agreement) copy of the slot frame and cut invariants of reac-pw/fuzz_headamp LLVMFuzzerTestOneInput
   (UBSan, [0x12fa8, 0x148ac); fuzz_headamp.c:311-360): lib/U/Prog/SlotFR.v and lib/U/Prog/SlotInv.v with SR := SRcf,
   in one file. Model: reac-pw/fuzz_role's U/Prog/SlotInvCF.v, itself in the
   form of reac-pw/fuzz_pin's U/Prog/SlotInvCF.v and libreac/fuzz_ctrl's released U/Prog/SlotInvCF.v (origin/ossv/recipes
   25e3d17bdb50). The U segment files of the slot (U/Prog/Seg/*.v and U/Prog/HeadSlot.v) are copied to U/Prog/SegCF/*.v
   over this file. Changes from U/Prog/SlotFR.v and U/Prog/SlotInv.v (role's, for headamp's four blocks and five cuts):
   - SR, its lemmas, evt_SR(_canon) and kb_run are redefined under the same names (ctrl's block, verbatim), so the
     copied segment proofs prove the cut-free run (crealizes: realizes, cut_free and uniform, U/SlotAgree.v);
   - frame_facts_cf: U/FrameAPI.frame_facts_ubsan, conjunct for conjunct in its order, with the agreement room
     (128 <= sb_cap <= CAP_AG) and the cut-free allocator (frame_allocator_cf: malloc in malloc_contract_cfg form,
     whose room is room_ag; free and free of NULL in cut-free form);
   - slot_room: 128 <= sb_cap <= CAP_AG (the agreement frame's entry bound sb_cap = CAP_AG);
   - resb_room gives room_ag, at the request bound 2^26 (room_ag_big: room_slots from AllocRoom.room_slots_big).
     headamp's largest hb at a malloc is three blocks of at most 19744 + 5440 + 30 bytes, and its requests are at
     most 19744, far under the 16 blocks, 2^24 bytes and 2^26 of resb_room;
   - slot_goal: lib_contract_cg;
   - the input-only definitions of U/Prog/SlotInv.v (the struct pod_props constants POD_PROPS, POD_LEN_OFF,
     POD_NENT_OFF, and head_rec, head_len, head_ans, OUT_LEN, out_after, first_req) are its own, named here by
     abbreviations, since the evt contracts of U/Prog/LLVMFuzzerTestOneInput_c.v state them; the ghost quantities
     (g_b0 .. g_ans), the four hb shapes and the five Inv_K* are U/Prog/SlotInv.v's text over this file's ghost.
   Statement text and the SR block: no function is proved here. *)
From Stdlib Require Import ZArith List Bool Lia Permutation Wf_nat Wellfounded.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.U.Reusable Require Import YK11 YK0i YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.U.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.U.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.U.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Lib Require Import Mem Frame.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.U Require Import Img0 Contract FrameAPI SlotAgree AgreeLift.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Lib Require Exec RegisterBridge Regs6ss MState.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.U Require KindBGlue.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.U.Prog Require SlotInv.
Import ListNotations.
Open Scope Z_scope.

(* The cut-free (agreement) copy of the ubsan slot proof (SlotFR.v, SlotInv.v and Seg/*.v copied to SlotInvCF.v and
   SegCF/*.v). Here SR and its lemmas are redefined under the same names as YM06.SR and U/Contract.v's evt_SR(_canon):
   a run relation whose realizes also carries cut_free (crealizes, SlotAgree.v), so the copied segment proofs, which
   use only these names, prove the cut-free run. The allocator facts are the cut-free ones (frame_allocator_cf), and
   the slot's room is the agreement shape's (128 <= sb_cap <= CAP_AG). *)
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

(* The slot's malloc room in the agreement frame: room_slots, and the cap and bytes bounds that room_cf needs. *)
Definition room_ag (b : sbound) (n : Z) : Prop := room_slots b n /\ 0 <= sb_cap b <= CAP_AG /\ sb_bytes b + n <= 2 ^ 29.

(* The cut-free allocator contracts the slot's calls use (FrameAPI.frame_allocator with malloc, free and free of
   NULL in cut-free form; malloc with the agreement room). *)
Definition malloc_contract_cfg {rc : RunCeil} {fx : FPState} (B : malloc_syms) (API : AllocAPI B) : Prop :=
  forall L A regs mem md n b,
    call_pre B (aa_MR API) L A regs mem md -> ro_agree (ms_segs B) mem -> getr regs 10 = Z_to_bv 64 n ->
    res_ok_slots A b -> room_ag b n ->
    SR (ms_segs B) (mkCfg (mkst regs (Z_to_bv 64 (ms_malloc B)) mem (seg_rom (ms_segs B))) md)
      (malloc_ret B API ALLOC_STACK L A regs mem md n b).

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
    ms_malloc B = 0x1693c /\ ms_free B = 0x167fc /\ ms_realloc B = None /\ ms_calloc B = None /\
    (forall rc : RunCeil, errno_addr B + 4 <= @alloc_ceiling rc) /\
    ms_guard B = 0x509d0 /\ ms_got_guard B = 0x1f3e8 /\
    ms_ctx B = 0x50a68 /\ ms_lock B = 0x50a60 /\ ms_libc B = 0x509f0 /\ ms_size_classes B = 0x10678 /\
    ms_small_cnt B = 0x106d8 /\ ms_med_cnt B = 0x106f3 /\ ms_debruijn B = 0x10658 /\ ms_tp B = 0x30760 /\
    ms_errno_off B = -164 /\ ms_replaced B = None /\ ms_vmlock B = None /\ ms_debruijn_len B = 32 /\
    @sk_ofl_head SH = 0x50e20 /\ @sk_ofl_lock SK = 0x50e18 /\ @sk_threaded SK = 0x509f0 + 1 /\
    empty = 0x30670 /\ 0 < empty < 2 ^ 62 /\
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

Definition SLOT_FRAME : Z := 608.
Definition SLOT_SAVE : Z := 104.
Definition SLOT_K : Z := SLOT_STACK.

(* Ghost values fixed at ENTRY: the input bytes (n = length), p, S, the entry registers (s0-s11, gp, tp by
   getr), the entry layout, allocator state, memory and model (B0 = blocks g_L g_A) and the entry bound. *)
Record ghost := Ghost {
  g_in : list byte;
  g_p : Z;
  g_S : Z;
  g_regs : bvmap 5 word;
  g_L : layout;
  g_A : astate;
  g_mem : word -> option byte;
  g_md : Model;
  g_b : sbound
}.

Definition g_n (g : ghost) : Z := Z.of_nat (length (g_in g)).
Definition fsp (g : ghost) : Z := g_S g - SLOT_FRAME.
Definition spk (g : ghost) (k : Z) : Z := fsp g + k.

(* Resources (sbound): the live harness blocks hb on top of the entry bound. *)
Definition hb_bytes (hb : list (Z * Z)) : Z := fold_right Z.add 0 (map snd hb).
Definition sb_hb (b0 : sbound) (hb : list (Z * Z)) : sbound :=
  SB (sb_live b0 + Z.of_nat (length hb)) (sb_bytes b0 + hb_bytes hb) (sb_cap b0).
(* The slot's entry bound in the agreement frame: sb_cap = CAP_AG there. *)
Definition slot_room (b : sbound) : Prop :=
  sb_live b <= 64 /\ 0 <= sb_bytes b <= 2 ^ 28 /\ 128 <= sb_cap b <= CAP_AG.
Definition RESB (b0 : sbound) (hb : list (Z * Z)) (A : astate) : Prop := res_ok_slots A (sb_hb b0 hb).
Definition RES_END (b0 : sbound) (A : astate) : Prop := res_ok_slots A b0.

Lemma hb_bytes_cons : forall x l, hb_bytes (x :: l) = snd x + hb_bytes l.
Proof. intros x l. reflexivity. Qed.

Lemma sb_hb_perm : forall b0 h h', Permutation h h' -> sb_hb b0 h = sb_hb b0 h'.
Proof.
  intros b0 h h' HP. unfold sb_hb. rewrite (Permutation_length HP).
  assert (E : hb_bytes h = hb_bytes h').
  { induction HP as [|x l l' _ IH|x y l|l l' l'' _ IH1 _ IH2]; rewrite ?hb_bytes_cons.
    - reflexivity.
    - rewrite IH. reflexivity.
    - ring.
    - rewrite IH1, IH2. reflexivity. }
  rewrite E. reflexivity.
Qed.

(* room_ag at the request bound 2^26 (libreac/fuzz_decode's U/Prog/LLVMFuzzerTestOneInput_cfb.v room_ag_big):
   room_slots from AllocRoom.room_slots_big, the cap below CAP_AG, the bytes below 2^29. (U/AllocRoom's CAPMAX
   and AgreeCap's are two constants of the same value, so the cap bound is computed.) *)
Lemma room_ag_big : forall b n, sb_live b + 1 <= sb_cap b -> 128 <= sb_cap b <= CAP_AG ->
  0 <= sb_bytes b -> sb_bytes b + n <= 2 ^ 29 -> 0 <= n <= 2 ^ 26 -> room_ag b n.
Proof.
  intros b n Hl Hc Hb Hbn Hn. split; [|split; lia].
  apply room_slots_big; [lia | | lia | lia]. split; [lia|].
  apply (Z.le_trans _ CAP_AG); [lia | apply Z.leb_le; vm_compute; reflexivity].
Qed.

(* The request bound is 2^26 for any hb of at most 16 blocks and 2^24 bytes. *)
Lemma resb_room : forall b0 hb n, slot_room b0 -> (length hb <= 16)%nat ->
  0 <= hb_bytes hb <= 2 ^ 24 -> 0 <= n <= 2 ^ 26 -> room_ag (sb_hb b0 hb) n.
Proof.
  intros b0 hb n (HL & HB & HC) Hlen HS Hn.
  unfold sb_hb. apply room_ag_big; cbn [sb_live sb_bytes sb_cap]; lia.
Qed.

Lemma resb_malloc : forall b0 hb hb' A res n, Permutation hb' ((res, n) :: hb) ->
  res_ok_slots A (sb_malloc (sb_hb b0 hb) n) -> RESB b0 hb' A.
Proof.
  intros b0 hb hb' A res n HP H. unfold RESB. rewrite (sb_hb_perm b0 _ _ HP).
  replace (sb_hb b0 ((res, n) :: hb)) with (sb_malloc (sb_hb b0 hb) n); [exact H|].
  unfold sb_malloc, sb_hb, hb_bytes. cbn [length map fold_right snd sb_live sb_bytes sb_cap].
  f_equal; lia.
Qed.

Lemma resb_free : forall b0 hb hb' A q n, Permutation hb ((q, n) :: hb') ->
  res_ok_slots A (sb_free (sb_hb b0 hb) n) -> RESB b0 hb' A.
Proof.
  intros b0 hb hb' A q n HP H. unfold RESB.
  rewrite (sb_hb_perm b0 _ _ HP) in H.
  replace (sb_hb b0 hb') with (sb_free (sb_hb b0 ((q, n) :: hb')) n); [exact H|].
  unfold sb_free, sb_hb, hb_bytes. cbn [length map fold_right snd sb_live sb_bytes sb_cap].
  f_equal; lia.
Qed.

Lemma resb_end : forall b0 A, RESB b0 [] A -> RES_END b0 A.
Proof.
  intros b0 A H. unfold RESB, RES_END in *.
  replace b0 with (sb_hb b0 []); [exact H|].
  unfold sb_hb, hb_bytes. destruct b0. cbn. f_equal; lia.
Qed.

Lemma resb_start : forall b0 A, res_ok_slots A b0 -> RESB b0 [] A.
Proof.
  intros b0 A H. unfold RESB. replace (sb_hb b0 []) with b0; [exact H|].
  unfold sb_hb, hb_bytes. destruct b0. cbn. f_equal; lia.
Qed.

(* Registers. Register numbers: ra 1, sp 2, gp 3, tp 4, s0 8, s1 9, a0-a7 10-17, s2-s11 18-27. *)
Definition rg (regs : bvmap 5 word) (r : bv 5) (v : Z) : Prop := getr regs r = Z_to_bv 64 v.

Section Slot.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AllocAPI B.
Context {LS : lib_shape} {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Let API := APIf rc.
Let segs := ms_segs B.
Let MR := aa_MR API.

Definition MI (m : word -> option byte) : Prop := ro_agree segs m.
Definition relro (m : word -> option byte) : Prop := G_img_c B frame_RELRO m.

(* [S - 104, S): s11, s10, .., s2, s1, s0, ra (0x12fdc `sd s11,0x1f8(sp)` .. 0x12fac `sd ra,0x258(sp)`). *)
Definition saved_bytes (g : ghost) : list byte :=
  le8 (getr (g_regs g) 27) ++ le8 (getr (g_regs g) 26) ++ le8 (getr (g_regs g) 25) ++
  le8 (getr (g_regs g) 24) ++ le8 (getr (g_regs g) 23) ++ le8 (getr (g_regs g) 22) ++
  le8 (getr (g_regs g) 21) ++ le8 (getr (g_regs g) 20) ++ le8 (getr (g_regs g) 19) ++
  le8 (getr (g_regs g) 18) ++ le8 (getr (g_regs g) 9) ++ le8 (getr (g_regs g) 8) ++ le8 (Z_to_bv 64 ra).

(* GV: the ghost facts. *)
Definition GV (g : ghost) : Prop :=
  0 <= g_n g < 2 ^ 26 /\
  ((g_n g = 0 /\ g_p g = empty) \/ (0 < g_n g /\ In (g_p g, g_n g) (blocks (g_L g) (g_A g)))) /\
  blk_data B (g_mem g) (g_p g) (g_in g) /\
  g_S g mod 16 = 0 /\ alloc_ceiling + SLOT_K <= g_S g /\ g_S g <= 2 ^ 47 /\
  slot_room (g_b g) /\
  getr (g_regs g) 2 = Z_to_bv 64 (g_S g) /\ getr (g_regs g) 4 = Z_to_bv 64 (ms_tp B).

(* FR: sp, gp, tp, the saved registers, the window, ro_agree and RELRO, the allocator, no byte changed outside
   [S - K, S), A and the live harness blocks hb, the resources (ctrl's FR, conjunct for conjunct). *)
Definition FR (g : ghost) (hb : list (Z * Z)) (L : layout) (A : astate) (regs : bvmap 5 word)
    (mem : word -> option byte) (md : Model) : Prop :=
  GV g /\
  getr regs 2 = Z_to_bv 64 (fsp g) /\ getr regs 3 = getr (g_regs g) 3 /\ getr regs 4 = getr (g_regs g) 4 /\
  bytes_at rsegs mem (g_S g - SLOT_SAVE) (saved_bytes g) /\
  stk rsegs mem (g_S g - SLOT_K) (g_S g) /\
  MI mem /\ relro mem /\
  MR L A mem md /\ WF A /\ bounded A /\ st_init_done A = true /\
  (exists vm, md = with_vmmaps vm (g_md g)) /\
  (forall a, alloc_ceiling <= a < 2 ^ 64 -> ~ (g_S g - SLOT_K <= a < g_S g) ->
     ~ (errno_addr B <= a < errno_addr B + 4) ->
     mbyte segs mem a = mbyte segs (g_mem g) a /\ (writable_at segs (g_mem g) a <-> writable_at segs mem a)) /\
  (forall a, in_img B a -> ~ static_owned B a -> ~ (ms_ctx B <= a < ms_ctx B + CTX_SIZE) ->
     ~ (errno_addr B <= a < errno_addr B + 4) ->
     mbyte segs mem a = mbyte segs (g_mem g) a /\ (writable_at segs (g_mem g) a <-> writable_at segs mem a)) /\
  (forall a k i, In (a, k) (blocks (g_L g) (g_A g)) -> 0 <= i < k ->
     mbyte segs mem (a + i) = mbyte segs (g_mem g) (a + i)) /\
  (forall a, errno_addr B <= a < errno_addr B + 4 -> writable_at segs mem a) /\
  sink_none B mem md /\ RESB (g_b g) hb A /\
  (forall a, g_S g - SLOT_K <= a < g_S g -> writable_at segs mem a).

(* A cut state at pc: some FP state with rounding mode 0, FR with the live harness blocks hb, the allocator's
   blocks = hb and the entry blocks, and the cut's own facts P. *)
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
  sink_none B (g_mem g) (g_md g) /\ MI (g_mem g) /\ relro (g_mem g) /\
  res_ok_slots (g_A g) (g_b g) /\
  frm_zero fp_csr.

(* RET: lib_post with G = [], stk = SLOT_STACK, from the ENTRY state, at some FP state with rounding mode 0. *)
Definition Post (g : ghost) (c : config) : Prop :=
  exists (fx' : YK11.FPState) L A regs mem md,
    c = mkCfg (@YK11.mkst fx' regs (Z_to_bv 64 ra) mem (seg_rom segs)) md /\
    frm_zero (@YK11.fp_csr fx') /\
    lib_post B API [] SLOT_STACK (g_L g) (g_A g) (g_regs g) (g_mem g) (g_md g) (g_p g) L A regs mem md /\
    sink_none B mem md /\ MI mem /\
    RES_END (g_b g) A /\
    (forall i, 0 <= i < g_n g -> mbyte segs mem (g_p g + i) = mbyte segs (g_mem g) (g_p g + i)).

(* H(X): every configuration of cut X runs, in the SR sense, to Post. *)
Definition Hcut (X : ghost -> config -> Prop) : Prop := forall g c, X g c -> SR segs c (Post g).

(* The cut-free slot obligation for this function (U/AgreeFrame's ubsan_agrees_of_slots): G = frame_G = [], GI
   trivial. *)
Definition slot_goal : Prop :=
  forall j, (j < 4)%nat -> lib_contract_cg B API [] frame_RELRO (fun _ _ => True) j ENTRY ra empty SLOT_STACK.

End Slot.

From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Lib Require Import Cells Step.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Pod Require Cursor.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Pod Require Import Model Layout Headamp.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Spec Require Import HeadBytes.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.U.Prog Require Import reac_headamp_prop_parse_result_c.

(* struct pod_props: 19744 bytes; len at 0x4000, n_ent at 0x4d14 (corrupt at 0x4d18); the record, its length, the
   parse's answer, out's size and bytes, first's request: U/Prog/SlotInv.v's own definitions, which the evt
   contracts of U/Prog/LLVMFuzzerTestOneInput_c.v state. *)
Abbreviation POD_PROPS := OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.U.Prog.SlotInv.POD_PROPS.
Abbreviation POD_LEN_OFF := OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.U.Prog.SlotInv.POD_LEN_OFF.
Abbreviation POD_NENT_OFF := OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.U.Prog.SlotInv.POD_NENT_OFF.
Abbreviation head_rec := OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.U.Prog.SlotInv.head_rec.
Abbreviation head_len := OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.U.Prog.SlotInv.head_len.
Abbreviation head_ans := OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.U.Prog.SlotInv.head_ans.
Abbreviation OUT_LEN := OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.U.Prog.SlotInv.OUT_LEN.
Abbreviation out_after := OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.U.Prog.SlotInv.out_after.
Abbreviation first_req := OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.U.Prog.SlotInv.first_req.

(* The headamp quantities of the input, as in U/Prog/SlotInv.v. *)
Definition g_b0 (g : ghost) : Z := fst (Cursor.fuzz_u8 (g_in g)).
Definition g_null (g : ghost) : Z := Z.land (g_b0 g) 1.
Definition g_cap (g : ghost) : Z := fst (Cursor.fuzz_u8 (snd (Cursor.fuzz_u8 (g_in g)))) mod 10.
Definition g_rest (g : ghost) : list byte := snd (Cursor.fuzz_u8 (snd (Cursor.fuzz_u8 (g_in g)))).
Definition g_src (g : ghost) : Z := g_p g + Z.min 2 (g_n g).
Definition g_k (g : ghost) : Z := g_n g - Z.min 2 (g_n g).
Definition g_rec (g : ghost) : pod_rec := head_rec (g_rest g).
Definition g_len (g : ghost) : Z := head_len (g_rest g).
Definition g_ans (g : ghost) : answer := head_ans (g_null g) (g_cap g) (g_rest g).

Definition hb_pp (pp : Z) : list (Z * Z) := [(pp, POD_PROPS)].
Definition hb_pod (g : ghost) (pod pp : Z) : list (Z * Z) := [(pod, g_len g); (pp, POD_PROPS)].
Definition hb_out (g : ghost) (out pod pp : Z) : list (Z * Z) := (out, OUT_LEN (g_cap g)) :: hb_pod g pod pp.
Definition hb_first (g : ghost) (first nf out pod pp : Z) : list (Z * Z) := (first, nf) :: hb_out g out pod pp.

Section Cuts.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AllocAPI B.
Context {LS : lib_shape} {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.

(* K13090, malloc(pp)'s return (0x1308c `jal malloc` with a0 = 19744). *)
Definition Inv_K13090 (g : ghost) (c : config) : Prop :=
  exists pp, CUTST B APIf ra empty g 0x13090 (hb_pp pp) (fun regs m =>
    rg regs 10 pp /\ pp <> 0 /\ pp mod 16 = 0 /\
    rg regs 22 (g_src g) /\ rg regs 18 (g_k g) /\ rg regs 19 (g_cap g) /\
    bytes_at rsegs m (fsp g + 0x10) (le8 (Z_to_bv 64 (1 - g_null g))) /\
    rg regs 9 POD_PROPS /\ rg regs 8 0x5000) c.

(* K140e4, malloc(pod)'s return (0x140e0 `jal malloc` with a0 = len): the record in the pp block. *)
Definition Inv_K140e4 (g : ghost) (c : config) : Prop :=
  exists pp pod, CUTST B APIf ra empty g 0x140e4 (hb_pod g pod pp) (fun regs m =>
    rg regs 10 pod /\ pod <> 0 /\ pod mod 16 = 0 /\
    rg regs 19 (g_len g) /\ rg regs 23 (pp + POD_LEN_OFF) /\ rg regs 24 pp /\
    bytes_at rsegs m (fsp g + 0x8) (le8 (Z_to_bv 64 (g_cap g))) /\
    bytes_at rsegs m (fsp g + 0x10) (le8 (Z_to_bv 64 (1 - g_null g))) /\
    bytes_at rsegs m (fsp g + 0x68) (le8 (Z_to_bv 64 (pp + POD_NENT_OFF))) /\
    bytes_at rsegs m (fsp g + 0x70) (le8 (Z_to_bv 64 pp)) /\
    bytes_at rsegs m (fsp g + 0x78) (le8 (Z_to_bv 64 (pp + POD_LEN_OFF))) /\
    bytes_at rsegs m pp (pp_bytes (g_rec g))) c.

(* K14118, malloc(out)'s return (0x14114 `jal malloc` with a0 = 3 cap + 3). *)
Definition Inv_K14118 (g : ghost) (c : config) : Prop :=
  exists pp pod out, CUTST B APIf ra empty g 0x14118 (hb_out g out pod pp) (fun regs m =>
    rg regs 10 out /\ out <> 0 /\ out mod 16 = 0 /\
    rg regs 8 (3 * g_cap g) /\ rg regs 9 pod /\ pod <> 0 /\ pod mod 16 = 0 /\ rg regs 18 (g_cap g) /\
    rg regs 20 (OUT_LEN (g_cap g)) /\ rg regs 23 (pp + POD_LEN_OFF) /\
    bytes_at rsegs m (fsp g + 0x10) (le8 (Z_to_bv 64 (1 - g_null g))) /\
    bytes_at rsegs m (fsp g + 0x68) (le8 (Z_to_bv 64 (pp + POD_NENT_OFF))) /\
    bytes_at rsegs m (fsp g + 0x70) (le8 (Z_to_bv 64 pp)) /\
    bytes_at rsegs m (fsp g + 0x78) (le8 (Z_to_bv 64 (pp + POD_LEN_OFF))) /\
    bytes_at rsegs m pp (pp_bytes (g_rec g)) /\
    bytes_at rsegs m pod (buf (g_rec g))) c.

(* K147e0, malloc(first)'s return (0x147dc `jal malloc` with a0 = first_req rc). *)
Definition Inv_K147e0 (g : ghost) (c : config) : Prop :=
  exists pp pod out first nf, CUTST B APIf ra empty g 0x147e0 (hb_first g first nf out pod pp) (fun regs m =>
    rg regs 10 first /\ first <> 0 /\ first mod 16 = 0 /\ nf = first_req (ans_rc (g_ans g)) /\
    rg regs 9 pod /\ pod <> 0 /\ pod mod 16 = 0 /\ rg regs 18 (g_cap g) /\
    rg regs 19 out /\ out <> 0 /\ out mod 16 = 0 /\ rg regs 20 (OUT_LEN (g_cap g)) /\
    rg regs 21 (if g_null g =? 1 then 0 else pod) /\ rg regs 22 (ans_rc (g_ans g)) /\
    rg regs 24 (3 * Z.max (ans_rc (g_ans g)) 0) /\
    bytes_at rsegs m (fsp g + 0x70) (le8 (Z_to_bv 64 pp)) /\
    bytes_at rsegs m pod (buf (g_rec g)) /\
    bytes_at rsegs m out (out_after (g_cap g) (g_ans g)) /\
    (exists ev, rw_cells rsegs m (errno_addr B) [C4 ev])) c.

(* K1482c, after check_plain, before free(first) (0x1482c `mv a0,s7`; 0x14830 `jal free`). *)
Definition Inv_K1482c (g : ghost) (c : config) : Prop :=
  exists pp pod out first nf, CUTST B APIf ra empty g 0x1482c (hb_first g first nf out pod pp) (fun regs m =>
    rg regs 23 first /\ rg regs 19 out /\ rg regs 9 pod /\
    bytes_at rsegs m (fsp g + 0x70) (le8 (Z_to_bv 64 pp))) c.

End Cuts.
