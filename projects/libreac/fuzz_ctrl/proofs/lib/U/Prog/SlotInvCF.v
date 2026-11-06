(* Cut invariants of fuzz_ctrl LLVMFuzzerTestOneInput (ubsan, [0x132c4, 0x14160)): ghost values, the frame FR,
   CUTST, Post, Hcut and one Inv_<cut> per cut of slot-plan-ubsan.md section 3 (ENTRY, the 85 U cuts, RET = Post).

   libreac v1.9.0 (internal path, sha256 3c5b94f2cf6d): every cut pc, frame offset and
   register below is the one of the v1.9 listing, through a Theorem Labs lane's v190-segment-table-ubsan.md sections 5a, 6a, 7a, 8, A1 (a working note, not in this delivery).
   What changed from v1.8 (fuzz_ctrl.debug 51bc238d4375):
   - Cut renames (a cut is named by its v1.9 pc; the `exists` wrapper of an `_at` cut is renamed with it):
     U132f8->U13310 U13328->U13340 U13348->U13360 U13354->U1336c U13390->U133a8 U133a0->U133b8 U133d0->U133e8
     U133f4->U1340c U13438->U13450 U1344c->U13464 U1345c->U13474 U13490->U134a8 U13494->U134ac U134c8->U134e0
     U134e4->U134fc U134f0->U13508 U1354c->U13564 U13568->U13580 U13598->U135b0 U135ac->U135c4 U135b4->U135cc
     U135d8->U135f0 U135e0->U135f8 U1362c->U13644 U13634->U1364c U1363c->U13654 U136ac->U136c4 U136bc->U136e4
     U136c4->U136ec U136d4->U136fc U13704->U1372c U13728->U13750 U13738->U13760 U1374c->U13774 U1375c->U13784
     U13774->U1379c U13848->U13844 U1386c->U13868 U1389c->U13898 U138ac->U138a8 U13af8->U13af0 U13b10->U13b04
     U13b68->U13b60 U13b6c->U13b64 U13c64->U13c58 U13c78->U13c6c U13c94->U13c88 U13d00->U13cf4 U13dac->U13da0
     U13dcc->U13dc0 U13de4->U13dd8 U13df4->U13de8 U13e34->U13e28 U13ee0->U13ed4 U13fa4->U13f98 U13fc4->U13fb8
     U13ff8->U13fec U14014->U14008 U14054->U14048 U14070->U14064 U1409c->U14090 U140b0->U140a4 U140bc->U140b0
     U140cc->U140c0 U140d0->U140c4 U140dc->U140d0 U140e8->U140dc U14108->U140f8 U14120->U14110 U14124->U14114.
     Kept (same pc): U137d0 U13820 U13954 U13964 U13978 U13984 U139bc U13a14 U13a28 U13a64 U13a68 U13a78 U13a94
     U13ab0 U13ab4. Five v1.9 names were v1.8 names of OTHER cuts: U136c4 (v1.8 U136ac), U13774 (v1.8 U1374c),
     U140b0 (v1.8 U140bc), U140d0 (v1.8 U140dc), U140dc (v1.8 U140e8).
   - U136e4 (v1.8 U136bc) is the `addi a0,sp,0x4c` after v1.9's new memset(sp+36, 0, 40) at 0x136d4..0x136e0 (the
     three branches that reached v1.8 0x136bc now reach the memset), so its state also holds `first` = 0 (FIRST0).
   - U13af0 (v1.8 U13af8, `addi a0,sp,0x5a`, rewritten in v1.9): the anchor of section 8, the first instruction of the
     v1.9 block that replaces it (`addi a0,zero,-8`); v1.9 keeps &frag + 8 in s0, so nothing at the cut is lost.
   - U140dc (v1.8 U140e8, `addi a2,zero,1`, deleted in v1.9): the cut is put at 0x140dc, the return point of the
     same `jal free` (v1.8 0x140e4 = v1.9 0x140d8) and the image of the next v1.8 instruction (0x140ec `li a0,254`);
     no branch targets either pc. It holds the cut's facts (LK, FC, IFS (S j)) with no change, and it moves no
     instruction between S_C05 (0x140d0 .. 0x140d8, `jal free` included) and S_C06 (0x140dc .. 0x140f4); 0x140d8
     would move `jal free` into S_C06, 0x140e0 would move `li a0,254` into S_C05.
   - Frame objects (DWARF + paired instructions): our sp+76 -> sp+114; id sp+154 -> sp+76 (IDB) but the round trip's
     id sp+154 -> sp+36 (RIDB: one v1.8 offset, two v1.9 objects); frag sp+82 -> sp+120 (frag + 15 / + 19 = sp+135 /
     sp+139, id + 3 = sp+79); the round trip's count 1824 -> 1792, p 1752 -> 76, addr 1736 -> 1824, pl 1688 -> 1752,
     pll / ports 1792 -> 1688 (ports + 4 / + 8 = 1692 / 1696), declaration 1688 -> 1752. Spill slots by live range:
     [A+64] -> [A+24] (M8 in the round trip, FC in the frame loop), [A+56] -> [A+16] (VC), the -7 pair [A+16] ->
     [A+8] (M7). SLOT_FRAME (1936) and the save area (g_S g - 104) are unchanged.
   - v1.9 has no frame-state slots [A+24/32/40/48] and no flag [A+8]: FSb is restated over the local `first`
     (sp+36: have u32, n u8 at +4, body at +5; a Theorem Labs lane's text for S_G07), with SlotModel's fstate = (have, n, body)
     (fs_a0 / fs_a1 removed; joined_byte / fg_addr_joined added there); OVF over s0 = sp+128 (&frag + 8, set by the
     new 0x137b8; it replaces the flag v1.8 computed from sp+90), and the 1 that v1.8 kept in a2 (A2) and s0 (FT) is
     s2 in v1.9 (0x137bc `addi s2,zero,1`, v1.8's `addi s2,zero,0x20` there), so S2, A2 and FT's last conjunct all
     state s2 = 1 (v1.8's s2 = 32 has no v1.9 register: 0x138f0 rematerialises 32 in a5). LK thus carries the two
     v1.9 loop constants s0 = sp+128 (OVF, position 5) and s2 = 1 (S2, position 6).
   - Registers (appendix A1): the cursor pair is swapped (s6 <-> s7 in CUR); in the frame loop j s11 -> s1, body s4 ->
     s5, len s5 -> s6, left - h s7 -> s3 (U13820), phi s6 -> s7, VC s7 -> s8, V7 s8 -> s9, V1 s1 -> s3, V0 s10 -> s11,
     V2 s3 -> s4, rf s9 -> s10, want_v s1 -> s3, rp s10 -> s11, unk s9 -> s10, want_m s8 -> s9, and in WB cat s9 ->
     s10, i s1 -> s3, row s8 -> s9, CAT + CAT_ROW * i s3 -> s4. Every conjunct keeps its position (FSb's five are
     restated); FIRST0 is appended last to PB. *)
From Stdlib Require Import ZArith List Bool Lia Permutation Wf_nat Wellfounded.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.U.Reusable Require Import YK11 YK0i YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.U.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.U.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.U.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import Mem Frame.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require RcModel RcRec RcParse RcReply RcIdentModel RcFrag RcLeaf
  RcPorts RcDecl RcClassify.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.U Require Import Img0 Contract FrameAPI SlotAgree AgreeLift.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Exec RegisterBridge Regs6ss MState.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.U Require KindBGlue.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.U.Prog Require Import SlotModel.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.U.Prog Require reac_ctrl_kind_name_c reac_ctrl_classify_box_frame_c.
From OSSVerify.libreac.fuzz_ctrl Require Statements.
Import ListNotations.
Open Scope Z_scope.


(* The cut-free (agreement) copy of the ubsan slot proof (SlotInv.v and Seg/*.v copied to SlotInvCF.v and SegCF/*.v).
   Here SR and its lemmas are redefined under the same names as YM06.SR and U/Contract.v's evt_SR(_canon): a run
   relation whose realizes also carries cut_free (crealizes, SlotAgree.v), so the copied segment proofs, which use
   only these names, prove the cut-free run. The allocator facts are the cut-free ones (frame_allocator_cf), and the
   slot's room is the agreement shape's (128 <= sb_cap <= CAP_AG). *)
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

(* frame_ubsan (U/FrameAPI.v) without its last conjunct, and that conjunct (the slot's obligation). frame_ubsan's
   ms_debruijn_len B = 132 (7c15abed81: static_owned covers [ms_debruijn B - 108, ms_debruijn B + max 32 len)) is
   placed just before frame_allocator, so the positions of the earlier conjuncts stay as they were. *)
Definition frame_facts (B : malloc_syms) (API : forall rc : RunCeil, AllocAPI B) (LS : lib_shape)
    (SH : sink_head) (SK : sink_syms) (ra empty : Z) : Prop :=
  ms_segs B = rsegs /\ ra mod 2 = 0 /\
  ms_malloc B = 0x173c0 /\ ms_free B = 0x17280 /\ ms_realloc B = None /\ ms_calloc B = None /\
  (forall rc : RunCeil, errno_addr B + 4 <= @alloc_ceiling rc) /\
  ms_guard B = 0x52100 /\ ms_got_guard B = 0x20b18 /\
  ms_ctx B = 0x52198 /\ ms_lock B = 0x52190 /\ ms_libc B = 0x52120 /\ ms_size_classes B = 0x10750 /\
  ms_small_cnt B = 0x107b0 /\ ms_med_cnt B = 0x106f0 /\ ms_debruijn B = 0x106cc /\ ms_tp B = 0x31e90 /\
  ms_errno_off B = -164 /\ ms_replaced B = None /\ ms_vmlock B = None /\
  @sk_ofl_head SH = 0x52550 /\ @sk_ofl_lock SK = 0x52548 /\ @sk_threaded SK = 0x52120 + 1 /\
  empty = 0x31da0 /\ 0 < empty < 2 ^ 62 /\
  (forall a, ms_ctx B <= a < ms_ctx B + CTX_SIZE -> Mem.ro_addr (ms_segs B) (Z_to_bv 64 a) = false) /\
  (forall a, in_globals frame_G a -> in_img B a /\ ~ static_owned B a /\ ~ (ms_ctx B <= a < ms_ctx B + CTX_SIZE) /\
     ~ (errno_addr B <= a < errno_addr B + 4)) /\
  (forall a, in_globals frame_RELRO a ->
     in_img B a /\ ~ static_owned B a /\ ~ (ms_ctx B <= a < ms_ctx B + CTX_SIZE) /\
     ~ (errno_addr B <= a < errno_addr B + 4)) /\
  (forall pl fs K, @LIBK LS pl fs K = K (LL 0 fs [])) /\
  (forall n b, @lib_delta LS n b = b) /\
  (forall b n, @lib_room LS b n -> sb_live b <= 64 /\ 0 <= sb_bytes b <= 2 ^ 28 /\ 128 <= sb_cap b <= CAP_AG) /\
  ms_debruijn_len B = 132 /\
  (forall (rc : RunCeil) (fx : FPState), @frame_allocator_cf rc fx B (API rc)).



Definition SLOT_FRAME : Z := 1936.
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

Definition g_n (g : ghost) : Z := nlen (g_in g).
Definition fsp (g : ghost) : Z := g_S g - SLOT_FRAME.
Definition spk (g : ghost) (k : Z) : Z := fsp g + k.
Definition z8 : byte := Z_to_bv 8 0.

(* Resources (sbound): the live harness blocks hb on top of the entry bound. *)
Definition hb_bytes (hb : list (Z * Z)) : Z := fold_right Z.add 0 (map snd hb).
Definition sb_hb (b0 : sbound) (hb : list (Z * Z)) : sbound :=
  SB (sb_live b0 + Z.of_nat (length hb)) (sb_bytes b0 + hb_bytes hb) (sb_cap b0).
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

(* The agreement cap is below CAPMAX, from the frame's bounds on CAP_AG (CAP_AG itself is not unfolded). *)
Lemma CAP_AG_le_CAPMAX : CAP_AG <= CAPMAX.
Proof.
  destruct (Z_lt_le_dec CAP_AG 1680) as [H|H]; [unfold CAPMAX; lia|].
  pose proof (LIVE_BOUND_mono 1680 CAP_AG (2 ^ 29) (2 ^ 29) ltac:(lia) ltac:(lia)).
  pose proof CAP_AG_fits. pose proof CAP_AG_max. lia.
Qed.

Lemma resb_room : forall b0 hb n, slot_room b0 -> (length hb <= 16)%nat ->
  0 <= hb_bytes hb <= 2 ^ 24 -> 0 <= n <= 2 ^ 20 -> room_ag (sb_hb b0 hb) n.
Proof.
  intros b0 hb n (HL & HB & HC) Hlen HS Hn.
  pose proof CAP_AG_le_CAPMAX as HCM.
  unfold room_ag, room_slots, sb_hb. cbn [sb_live sb_bytes sb_cap].
  split; [split; [exact (proj1 Hn)|]; split; [lia|] | split; [lia | lia]].
  apply (CAPOK_mono CAPMAX (sb_cap b0) (2 ^ 40) _ (2 ^ 22) n); [lia | lia | lia | exact CAPOK_small].
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

(* Registers and memory cells. Register numbers: ra 1, sp 2, gp 3, tp 4, t2 7, s0 8, s1 9, a0-a7 10-17,
   s2-s11 18-27. *)
Definition rg (regs : bvmap 5 word) (r : bv 5) (v : Z) : Prop := getr regs r = Z_to_bv 64 v.
Definition q64 (m : word -> option byte) (a v : Z) : Prop := bytes_at rsegs m a (le8 (Z_to_bv 64 v)).
Definition u32 (m : word -> option byte) (a v : Z) : Prop := bytes_at rsegs m a (le4 (Z_to_bv 64 v)).
Definition u16 (m : word -> option byte) (a v : Z) : Prop := bytes_at rsegs m a (le2 (Z_to_bv 64 v)).
Definition b8 (m : word -> option byte) (a v : Z) : Prop := bytes_at rsegs m a [Z_to_bv 8 v].
Definition hb1 (phi n : Z) : list (Z * Z) := [(phi, n)].

(* Bundles of slot-plan-ubsan.md 3.1, at the v1.9 offsets and registers (header). CUR: v1.9 swaps the cursor pair
   (0x13344 `addi s7,a0,1`, 0x13358 `addi s6,a1,-1`): s7 = p + c, s6 = n - c. *)
Definition CUR (g : ghost) (c : Z) (regs : bvmap 5 word) : Prop :=
  0 <= c <= g_n g /\ rg regs 23 (g_p g + c) /\ rg regs 22 (g_n g - c).
Definition OURb (g : ghost) (m : word -> option byte) : Prop := bytes_at rsegs m (spk g 114) (OUR (g_in g)).
(* `id` (Init and the frame loop) is at sp+76; the round trip's own `id` is at sp+36 (RIDB). *)
Definition IDB (g : ghost) (m : word -> option byte) (idb : list byte) : Prop := bytes_at rsegs m (spk g 76) idb.
Definition RIDB (g : ghost) (m : word -> option byte) (idb : list byte) : Prop := bytes_at rsegs m (spk g 36) idb.
Definition FGB (g : ghost) (m : word -> option byte) (st : list byte) : Prop := bytes_at rsegs m (spk g 120) st.
(* The -7 pair: 0x137cc `sd a0,8(sp)`, read 0x13da4 `ld a0,8(sp)`. *)
Definition M7 (g : ghost) (m : word -> option byte) : Prop := q64 m (spk g 8) 0xfffffff9fffffff9.
(* The new one-slot and one-register facts of plan section 7. M8: 0x133c0 `sd a0,24(sp)`. OVF: v1.9 keeps &frag + 8
   in s0 (0x137b8 `addi s0,sp,0x80`) where v1.8 kept a flag computed from it at [sp+8]. S2 / A2: the 1 in s2. *)
Definition M8 (g : ghost) (m : word -> option byte) : Prop := q64 m (spk g 24) 0.
Definition OVF (g : ghost) (regs : bvmap 5 word) : Prop := rg regs 8 (spk g 128).
Definition S2 (regs : bvmap 5 word) : Prop := rg regs 18 1.
Definition A2 (regs : bvmap 5 word) : Prop := rg regs 18 1.
Definition T2 (regs : bvmap 5 word) : Prop := rg regs 7 12.
(* `first` = { 0 }: 0x136d4 .. 0x136e0 memset(sp+36, 0, 40), before U136e4. *)
Definition FIRST0 (g : ghost) (m : word -> option byte) : Prop := bytes_at rsegs m (spk g 36) (repeat z8 40).

(* Round trip. *)
Definition RT (g : ghost) (regs : bvmap 5 word) : Prop :=
  rg regs 8 (mrow (g_in g)) /\ rg regs 18 BOXA /\ rg regs 19 CNT16 /\ rg regs 24 32 /\ rg regs 25 7 /\
  rg regs 26 0xe38f0000 /\ rg regs 27 36.
Definition rnb (g : ghost) (b : nat) : Z := rt_n (g_in g) (Z.of_nat b).
Definition rFb (g : ghost) (b : nat) : list byte := rt_F (g_in g) (Z.of_nat b).
Definition rgb (g : ghost) (b : nat) : list byte := rt_g (g_in g) (Z.of_nat b).
Definition RB (g : ghost) (b : nat) (idb fgb : list byte) (regs : bvmap 5 word) (m : word -> option byte) : Prop :=
  (b <= 6)%nat /\ CUR g 7 regs /\ OURb g m /\ RT g regs /\ M8 g m /\ rg regs 9 (Z.of_nat b) /\ RIDB g m idb /\
  FGB g m fgb.
Definition RS (g : ghost) (b : nat) (regs : bvmap 5 word) (m : word -> option byte) : Prop :=
  RB g b (RID (g_in g) b) (RFG (g_in g) b) regs m.
Definition RFb (g : ghost) (b : nat) (idb fgb : list byte) (phi : Z) (regs : bvmap 5 word)
    (m : word -> option byte) : Prop :=
  RB g b idb fgb regs m /\ rnb g b <> 0 /\ rg regs 20 phi /\ bytes_at rsegs m phi (rFb g b).
Definition RFx (g : ghost) (b : nat) (idb fgb : list byte) (phi : Z) (regs : bvmap 5 word)
    (m : word -> option byte) : Prop :=
  RFb g b idb fgb phi regs m /\ rg regs 21 (rnb g b).
Definition RF (g : ghost) (b : nat) (phi : Z) (regs : bvmap 5 word) (m : word -> option byte) : Prop :=
  RFx g b (RID (g_in g) b) (RFG (g_in g) b) phi regs m.

(* Frame loop, turn j. *)
Definition IDb (g : ghost) (idb : list byte) (m : word -> option byte) : Prop :=
  IDB g m idb /\ RcIdentModel.id_ok idb.
Definition FGb (g : ghost) (st : list byte) (m : word -> option byte) : Prop := FGB g m st /\ frag_ok st.
(* `first` (sp+36, 40 B: have u32 at +0, n u8 at +4, body from +5): 0x13c2c `sw s2,36(sp)` (have = 1),
   0x13c3c `sb a2,40(sp)` (n = block[8] = frame[26]), 0x13c54 memcpy(sp+41, block + 9, n) (body = fg_body); zeroed by
   0x136e0's memset (FIRST0, fs0 = (0, 0, [])); read 0x13b08 `lw a0,36(sp)` and joined_byte(&first, block, 9 / 10)
   (SlotModel.joined_byte, fg_addr_joined). *)
Definition FSb (g : ghost) (s : fstate) (st : list byte) (m : word -> option byte) : Prop :=
  u32 m (spk g 36) (fs_have s) /\ b8 m (spk g 40) (fs_nb s) /\ bytes_at rsegs m (spk g 41) (fs_body s) /\
  Z.of_nat (length (fs_body s)) = fs_nb s /\ FI st s.
Definition IDj (g : ghost) (j : nat) (m : word -> option byte) : Prop := IDb g (t_ID (g_in g) j) m.
Definition FGj (g : ghost) (j : nat) (m : word -> option byte) : Prop := FGb g (t_FG (g_in g) j) m.
Definition FSj (g : ghost) (j : nat) (m : word -> option byte) : Prop :=
  FSb g (fst_at (g_in g) j) (t_FG (g_in g) j) m.
Definition IFS (g : ghost) (j : nat) (m : word -> option byte) : Prop := IDj g j m /\ FGj g j m /\ FSj g j m.

(* The parts of LI that hold at every frame-loop cut (s1 = j, our, the -7 pair, s0 = &frag + 8, s2 = 1). *)
Definition LK (g : ghost) (j : nat) (regs : bvmap 5 word) (m : word -> option byte) : Prop :=
  (j <= 255)%nat /\ rg regs 9 (Z.of_nat j) /\ OURb g m /\ M7 g m /\ OVF g regs /\ S2 regs.
Definition LI (g : ghost) (j : nat) (regs : bvmap 5 word) (m : word -> option byte) : Prop :=
  LK g j regs m /\ CUR g (t_c (g_in g) j) regs /\ 1 <= t_left (g_in g) j /\ IFS g j m /\ A2 regs.
(* The cursor after the record header: left - h saved at sp+24 (0x1382c `sd s3,24(sp)`), body (s5), len (s6). *)
Definition FC (g : ghost) (j : nat) (regs : bvmap 5 word) (m : word -> option byte) : Prop :=
  q64 m (spk g 24) (t_left (g_in g) j - t_h (g_in g) j) /\ rg regs 21 (g_p g + t_body (g_in g) j) /\
  rg regs 22 (t_len (g_in g) j).
(* phi in s7 (0x13820 `mv s7,a0`); the 1 that v1.8 set in s0 (0x13830) is v1.9's s2. *)
Definition FT (g : ghost) (j : nat) (phi : Z) (regs : bvmap 5 word) (m : word -> option byte) : Prop :=
  LK g j regs m /\ FC g j regs m /\ rg regs 23 phi /\ bytes_at rsegs m phi (t_phi (g_in g) j) /\ rg regs 18 1.
Definition V7 (g : ghost) (j : nat) (regs : bvmap 5 word) : Prop := rg regs 25 (t_k (g_in g) j).
Definition V1 (g : ghost) (j : nat) (regs : bvmap 5 word) : Prop := rg regs 19 (b2z (t_8819 (g_in g) j)).
Definition V0 (g : ghost) (j : nat) (regs : bvmap 5 word) : Prop := rg regs 27 (b2z (t_sum_ok (g_in g) j)).
Definition V2 (g : ghost) (j : nat) (regs : bvmap 5 word) : Prop := rg regs 20 (b2z (t_big (g_in g) j)).
Definition VC (g : ghost) (j : nat) (phi : Z) (regs : bvmap 5 word) (m : word -> option byte) : Prop :=
  rg regs 24 (if t_big (g_in g) j then phi + 18 else 0) /\
  q64 m (spk g 16) (b2z (t_TF (g_in g) j)) /\ bytes_at rsegs m (spk g 1752) (t_B (g_in g) j).
Definition FV (g : ghost) (j : nat) (phi : Z) (regs : bvmap 5 word) (m : word -> option byte) : Prop :=
  V7 g j regs /\ V1 g j regs /\ V0 g j regs /\ V2 g j regs /\ VC g j phi regs m.
Definition FB (g : ghost) (j : nat) (phi : Z) (regs : bvmap 5 word) (m : word -> option byte) : Prop :=
  FT g j phi regs m /\ FV g j phi regs m.
(* U13c58 (EA), from U13da0 on without s3 and s11 (EQ), and the parts kept to U13f98 (CC) and to W00 (CC7). *)
Definition EA (g : ghost) (j : nat) (phi : Z) (regs : bvmap 5 word) (m : word -> option byte) : Prop :=
  FB g j phi regs m /\ IFS g (S j) m.
Definition EQ (g : ghost) (j : nat) (phi : Z) (regs : bvmap 5 word) (m : word -> option byte) : Prop :=
  FT g j phi regs m /\ V7 g j regs /\ V2 g j regs /\ VC g j phi regs m /\ IFS g (S j) m /\
  t_8819 (g_in g) j = true.
Definition CC7 (g : ghost) (j : nat) (phi : Z) (regs : bvmap 5 word) (m : word -> option byte) : Prop :=
  FT g j phi regs m /\ VC g j phi regs m /\ IFS g (S j) m.
Definition CC (g : ghost) (j : nat) (phi : Z) (regs : bvmap 5 word) (m : word -> option byte) : Prop :=
  CC7 g j phi regs m /\ V2 g j regs /\ V7 g j regs.
Definition PORTS (g : ghost) (j : nat) (m : word -> option byte) : Prop :=
  (t_rp (g_in g) j = 0 ->
     u32 m (spk g 1688) (4 * RcLeaf.n_in (t_pbs (g_in g) j)) /\
     u32 m (spk g 1692) (4 * RcLeaf.n_out (t_pbs (g_in g) j)) /\
     u32 m (spk g 1696) (16 * RcLeaf.bt (t_pbs (g_in g) j) 7)) /\
  (t_rp (g_in g) j <> 0 -> u32 m (spk g 1688) (-7) /\ u32 m (spk g 1692) (-7) /\ u32 m (spk g 1696) (-7)).
Definition QB (g : ghost) (j : nat) (phi : Z) (regs : bvmap 5 word) (m : word -> option byte) : Prop :=
  EQ g j phi regs m /\ rg regs 27 (t_rp (g_in g) j) /\ PORTS g j m /\ b8 m (spk g 1792) (t_first (g_in g) j).
Definition RSEL (g : ghost) (j : nat) (phi : Z) (regs : bvmap 5 word) (m : word -> option byte) : Prop :=
  CC7 g j phi regs m /\ t_rowsel (g_in g) j = true.

Section Slot.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AllocAPI B.
Context {LS : lib_shape} {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Hypothesis FF : frame_facts B APIf LS SH SK ra empty.
Let API := APIf rc.
Let segs := ms_segs B.
Let MR := aa_MR API.

Definition MI (m : word -> option byte) : Prop := ro_agree segs m.
Definition relro (m : word -> option byte) : Prop := G_img_c B frame_RELRO m.

Definition saved_bytes (g : ghost) : list byte :=
  le8 (getr (g_regs g) 27) ++ le8 (getr (g_regs g) 26) ++ le8 (getr (g_regs g) 25) ++
  le8 (getr (g_regs g) 24) ++ le8 (getr (g_regs g) 23) ++ le8 (getr (g_regs g) 22) ++
  le8 (getr (g_regs g) 21) ++ le8 (getr (g_regs g) 20) ++ le8 (getr (g_regs g) 19) ++
  le8 (getr (g_regs g) 18) ++ le8 (getr (g_regs g) 9) ++ le8 (getr (g_regs g) 8) ++ le8 (Z_to_bv 64 ra).

(* GV: the ghost facts (S1 of C1); the last conjunct is PB (plan section 7: the input block's range). *)
Definition GV (g : ghost) : Prop :=
  0 <= g_n g < 2 ^ 26 /\
  ((g_n g = 0 /\ g_p g = empty) \/ (0 < g_n g /\ In (g_p g, g_n g) (blocks (g_L g) (g_A g)))) /\
  blk_data B (g_mem g) (g_p g) (g_in g) /\
  g_S g mod 16 = 0 /\ alloc_ceiling + SLOT_K <= g_S g /\ g_S g <= 2 ^ 47 /\
  slot_room (g_b g) /\
  getr (g_regs g) 2 = Z_to_bv 64 (g_S g) /\ getr (g_regs g) 4 = Z_to_bv 64 (ms_tp B) /\
  (g_n g = 0 \/ (4096 <= g_p g /\ g_p g + g_n g <= alloc_ceiling)).

(* FR (FR1-FR5 of the plan): sp, gp, tp, the saved registers, the window, ro_agree and RELRO, the allocator,
   no byte changed outside [S - K, S), A and the live harness blocks hb, the resources. *)
Definition FR (g : ghost) (hb : list (Z * Z)) (L : layout) (A : astate) (regs : bvmap 5 word)
    (mem : word -> option byte) (md : Model) : Prop :=
  GV g /\
  getr regs 2 = Z_to_bv 64 (fsp g) /\ getr regs 3 = getr (g_regs g) 3 /\ getr regs 4 = getr (g_regs g) 4 /\
  bytes_at rsegs mem (g_S g - 104) (saved_bytes g) /\
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

Definition CUTST (g : ghost) (pc : Z) (hb : list (Z * Z))
    (P : bvmap 5 word -> (word -> option byte) -> Prop) (c : config) : Prop :=
  exists L A regs mem md,
    c = mkCfg (mkst regs (Z_to_bv 64 pc) mem (seg_rom segs)) md /\
    FR g hb L A regs mem md /\
    Permutation (blocks L A) (hb ++ blocks (g_L g) (g_A g)) /\
    P regs mem.

Definition Inv_ENTRY (g : ghost) (c : config) : Prop :=
  c = mkCfg (mkst (g_regs g) (Z_to_bv 64 ENTRY) (g_mem g) (seg_rom segs)) (g_md g) /\
  GV g /\
  lib_pre B API SLOT_STACK empty (g_L g) (g_A g) (g_regs g) (g_mem g) (g_md g) ra (g_p g) (g_n g) /\
  getr (g_regs g) 2 = Z_to_bv 64 (g_S g) /\
  sink_none B (g_mem g) (g_md g) /\ MI (g_mem g) /\ relro (g_mem g) /\
  res_ok_slots (g_A g) (g_b g).

(* RET: C1's post at pc = R (lib_post with G = [], stk = SLOT_STACK, from the ENTRY state). *)
Definition Post (g : ghost) (c : config) : Prop :=
  exists L A regs mem md,
    c = mkCfg (mkst regs (Z_to_bv 64 ra) mem (seg_rom segs)) md /\
    lib_post B API [] SLOT_STACK (g_L g) (g_A g) (g_regs g) (g_mem g) (g_md g) (g_p g) L A regs mem md /\
    sink_none B mem md /\ MI mem /\
    RES_END (g_b g) A /\
    (forall i, 0 <= i < g_n g -> mbyte segs mem (g_p g + i) = mbyte segs (g_mem g) (g_p g + i)).

(* H(X) of plan section 5, for plain cuts and for cuts with one or two indices. *)
Definition Hcut (X : ghost -> config -> Prop) : Prop := forall g c, X g c -> SR segs c (Post g).
Definition Hat {I : Type} (X : ghost -> I -> config -> Prop) (i : I) : Prop :=
  forall g c, X g i c -> SR segs c (Post g).
Definition Hat2 {I J : Type} (X : ghost -> I -> J -> config -> Prop) (i : I) (k : J) : Prop :=
  forall g c, X g i k c -> SR segs c (Post g).

(* The slot obligation for this function: G = frame_G = [], GI trivial. *)
Definition slot_goal : Prop :=
  forall j, (j < 4)%nat -> lib_contract_cg B API [] frame_RELRO (fun _ _ => True) j ENTRY ra empty SLOT_STACK.

(* ---- 3.2 Start (A) ---- *)
Definition Inv_U13310_at (g : ghost) (t : Z) (c : config) : Prop :=
  CUTST g 0x13310 [] (fun regs m =>
    0 <= t <= 5 /\ rg regs 10 (g_p g + Z.min t (g_n g)) /\ rg regs 11 (g_n g - Z.min t (g_n g)) /\
    rg regs 12 (spk g 114 + t) /\ rg regs 13 (6 - t) /\ rg regs 14 1 /\
    bytes_at rsegs m (spk g 114) (firstn (Z.to_nat t) (OUR (g_in g)))) c.
Definition Inv_U13310 (g : ghost) (c : config) : Prop := exists t, Inv_U13310_at g t c.
Definition Inv_U13340 (g : ghost) (c : config) : Prop :=
  CUTST g 0x13340 [] (fun regs m =>
    OURb g m /\ rg regs 10 (g_p g + Z.min 6 (g_n g)) /\ rg regs 11 (g_n g - Z.min 6 (g_n g))) c.

(* ---- 3.2 Round trip (R); b : nat is the turn ---- *)
Definition RA (g : ghost) (regs : bvmap 5 word) (m : word -> option byte) : Prop :=
  7 <= g_n g /\ CUR g 7 regs /\ OURb g m.
Definition Inv_U13360 (g : ghost) (c : config) : Prop :=
  CUTST g 0x13360 [] (fun regs m => RA g regs m /\ rg regs 8 (mode (g_in g)) /\ rt_on (g_in g) = true) c.
Definition Inv_U1336c (g : ghost) (c : config) : Prop :=
  CUTST g 0x1336c [] (fun regs m => RA g regs m /\ rg regs 8 (mode (g_in g)) /\ rt_on (g_in g) = true /\
    rg regs 10 CAT /\ q64 m (spk g 1792) CAT_N) c.
Definition Inv_U133a8 (g : ghost) (c : config) : Prop :=
  CUTST g 0x133a8 [] (fun regs m => RA g regs m /\ rg regs 8 (mrow (g_in g)) /\ RIDB g m RcIdentModel.ID0) c.
Definition Inv_U133b8 (g : ghost) (c : config) : Prop :=
  CUTST g 0x133b8 [] (fun regs m => RA g regs m /\ rg regs 8 (mrow (g_in g)) /\ RIDB g m RcIdentModel.ID0 /\
    FGB g m z72) c.
Definition Inv_U133e8_at (g : ghost) (b : nat) (c : config) : Prop := CUTST g 0x133e8 [] (RS g b) c.
Definition Inv_U133e8 (g : ghost) (c : config) : Prop := exists b, Inv_U133e8_at g b c.
Definition Inv_U1340c_at (g : ghost) (b : nat) (c : config) : Prop :=
  CUTST g 0x1340c [] (fun regs m => RS g b regs m /\ rg regs 10 (rnb g b) /\
    (rnb g b <> 0 -> bytes_at rsegs m (spk g 192) (rFb g b))) c.
Definition Inv_U1340c (g : ghost) (c : config) : Prop := exists b, Inv_U1340c_at g b c.
Definition Inv_U13450_at (g : ghost) (b : nat) (c : config) : Prop :=
  exists phi, CUTST g 0x13450 (hb1 phi (rnb g b)) (fun regs m => RS g b regs m /\ rnb g b <> 0 /\
    rg regs 21 (rnb g b) /\ rg regs 10 phi /\ phi <> 0 /\ bytes_at rsegs m (spk g 192) (rFb g b)) c.
Definition Inv_U13450 (g : ghost) (c : config) : Prop := exists b, Inv_U13450_at g b c.
Definition Inv_U13464_at (g : ghost) (b : nat) (c : config) : Prop :=
  exists phi, CUTST g 0x13464 (hb1 phi (rnb g b)) (RF g b phi) c.
Definition Inv_U13464 (g : ghost) (c : config) : Prop := exists b, Inv_U13464_at g b c.
Definition Inv_U13474_at (g : ghost) (b : nat) (c : config) : Prop :=
  exists phi, CUTST g 0x13474 (hb1 phi (rnb g b)) (fun regs m => RF g b phi regs m /\
    rg regs 10 (rt_k (g_in g) (Z.of_nat b)) /\ bytes_at rsegs m (spk g 76) (rt_B (g_in g) (Z.of_nat b))) c.
Definition Inv_U13474 (g : ghost) (c : config) : Prop := exists b, Inv_U13474_at g b c.
Definition Inv_U134a8_at (g : ghost) (b : nat) (c : config) : Prop :=
  exists phi, CUTST g 0x134a8 (hb1 phi (rnb g b)) (fun regs m => RF g b phi regs m /\ (b = 3 \/ b = 4)%nat /\
    rt_k (g_in g) (Z.of_nat b) = 5 /\ RcReply.ir (rnb g b) (rgb g b) = true /\ rg regs 10 1 /\
    bytes_at rsegs m (spk g 1824) (RcReply.reply_addr (rgb g b)) /\ q64 m (spk g 1752) (phi + 38) /\
    q64 m (spk g 1688) (r_pll (rgb g b))) c.
Definition Inv_U134a8 (g : ghost) (c : config) : Prop := exists b, Inv_U134a8_at g b c.
Definition Inv_U134e0 (g : ghost) (c : config) : Prop :=
  exists phi, CUTST g 0x134e0 (hb1 phi (rnb g 6)) (fun regs m =>
    RFx g 6 (RID (g_in g) 6) (RFG (g_in g) 7) phi regs m /\ rt_k (g_in g) 6 = 11 /\
    fg_rf (rnb g 6) (RFG (g_in g) 6) (rgb g 6) = 1 /\ rg regs 10 1 /\
    u16 m (spk g 1824) (RcFrag.fg_addr (RFG (g_in g) 6) (rgb g 6)) /\ q64 m (spk g 1752) (spk g 139) /\
    q64 m (spk g 1688) (f_pll (RFG (g_in g) 6) (rgb g 6))) c.
Definition Inv_U134ac_at (g : ghost) (b : nat) (c : config) : Prop :=
  exists phi, CUTST g 0x134ac (hb1 phi (rnb g b)) (fun regs m => RF g b phi regs m /\ (b = 5 \/ b = 6)%nat /\
    rg regs 10 (rt_k (g_in g) (Z.of_nat b))) c.
Definition Inv_U134ac (g : ghost) (c : config) : Prop := exists b, Inv_U134ac_at g b c.
Definition Inv_U134fc_at (g : ghost) (b : nat) (c : config) : Prop :=
  exists phi, CUTST g 0x134fc (hb1 phi (rnb g b)) (fun regs m =>
    RFx g b (RID (g_in g) (S b)) (RFG (g_in g) (S b)) phi regs m /\ (b = 3 \/ b = 4 \/ b = 6)%nat /\
    rg regs 10 1) c.
Definition Inv_U134fc (g : ghost) (c : config) : Prop := exists b, Inv_U134fc_at g b c.
Definition Inv_U13508_at (g : ghost) (b : nat) (c : config) : Prop :=
  exists phi, CUTST g 0x13508 (hb1 phi (rnb g b)) (fun regs m => RF g b phi regs m /\ (b <= 2)%nat /\
    rg regs 10 (rt_k (g_in g) (Z.of_nat b))) c.
Definition Inv_U13508 (g : ghost) (c : config) : Prop := exists b, Inv_U13508_at g b c.
Definition Inv_U13564 (g : ghost) (c : config) : Prop :=
  exists phi, CUTST g 0x13564 (hb1 phi (rnb g 0)) (fun regs m => RF g 0 phi regs m /\
    rt_k (g_in g) 0 = 9 /\ RcModel.blocksum (skipn 18 (rgb g 0)) = 0 /\ rg regs 10 (mrow (g_in g))) c.
Definition Inv_U13580 (g : ghost) (c : config) : Prop :=
  exists phi, CUTST g 0x13580 (hb1 phi (rnb g 0)) (fun regs m =>
    RFb g 0 (RID (g_in g) 0) (RFG (g_in g) 0) phi regs m /\ rg regs 21 (phi + 18) /\ rg regs 10 0 /\
    u32 m (spk g 1688) (4 * RcLeaf.n_in (rt_pbs (g_in g))) /\
    u32 m (spk g 1692) (4 * RcLeaf.n_out (rt_pbs (g_in g))) /\
    u32 m (spk g 1696) (16 * RcLeaf.bt (rt_pbs (g_in g)) 7)) c.
Definition Inv_U135b0 (g : ghost) (c : config) : Prop :=
  exists phi, CUTST g 0x135b0 (hb1 phi (rnb g 0)) (fun regs m =>
    RFb g 0 (RID (g_in g) 0) (RFG (g_in g) 0) phi regs m /\ rg regs 21 (phi + 18) /\ rg regs 10 1 /\
    bytes_at rsegs m (spk g 1752) (RcDecl.decl (rt_mb (g_in g)))) c.
Definition Inv_U135c4 (g : ghost) (c : config) : Prop :=
  exists phi, CUTST g 0x135c4 (hb1 phi (rnb g 0)) (fun regs m =>
    RFb g 0 (RID (g_in g) 0) (RFG (g_in g) 0) phi regs m /\ rg regs 21 (phi + 18) /\ rg regs 10 0 /\
    bytes_at rsegs m (spk g 1752) (RcDecl.decl (rt_mb (g_in g)))) c.
Definition Inv_U135cc (g : ghost) (c : config) : Prop :=
  exists phi, CUTST g 0x135cc (hb1 phi (rnb g 5)) (fun regs m => RF g 5 phi regs m /\
    rg regs 10 (rt_k (g_in g) 5)) c.
Definition Inv_U135f0 (g : ghost) (c : config) : Prop :=
  exists phi, CUTST g 0x135f0 (hb1 phi (rnb g 5)) (fun regs m =>
    RFx g 5 (RID (g_in g) 6) (RFG (g_in g) 6) phi regs m /\ rg regs 10 0) c.
Definition Inv_U135f8_at (g : ghost) (b : nat) (c : config) : Prop :=
  exists phi, CUTST g 0x135f8 (hb1 phi (rnb g b)) (fun regs m => RF g b phi regs m /\ (b = 1 \/ b = 2)%nat /\
    rg regs 10 (rt_k (g_in g) (Z.of_nat b))) c.
Definition Inv_U135f8 (g : ghost) (c : config) : Prop := exists b, Inv_U135f8_at g b c.
Definition Inv_U13644_at (g : ghost) (b : nat) (c : config) : Prop :=
  exists phi, CUTST g 0x13644 (hb1 phi (rnb g b)) (fun regs m =>
    RB g b (RID (g_in g) (S b)) (RFG (g_in g) (S b)) regs m /\ rnb g b <> 0 /\ rg regs 20 phi) c.
Definition Inv_U13644 (g : ghost) (c : config) : Prop := exists b, Inv_U13644_at g b c.
Definition Inv_U1364c_at (g : ghost) (b : nat) (c : config) : Prop :=
  CUTST g 0x1364c [] (RB g b (RID (g_in g) (S b)) (RFG (g_in g) (S b))) c.
Definition Inv_U1364c (g : ghost) (c : config) : Prop := exists b, Inv_U1364c_at g b c.
Definition Inv_U13654 (g : ghost) (c : config) : Prop :=
  CUTST g 0x13654 [] (fun regs m => RA g regs m /\ rg regs 8 (mrow (g_in g)) /\ M8 g m /\
    RIDB g m (RID (g_in g) 7)) c.
Definition Inv_U136c4 (g : ghost) (c : config) : Prop :=
  CUTST g 0x136c4 [] (fun regs m => RA g regs m /\ rg regs 8 (mrow (g_in g)) /\ M8 g m /\
    RIDB g m (RID (g_in g) 7) /\ rg regs 10 0) c.

(* ---- 3.3 Init and P8 (P) ---- *)
(* PB: from U136e4 on, `first` = { 0 } too (FIRST0, appended last). *)
Definition PB (g : ghost) (regs : bvmap 5 word) (m : word -> option byte) : Prop :=
  CUR g (c0 (g_in g)) regs /\ OURb g m /\ FIRST0 g m.
Definition P0 (g : ghost) (regs : bvmap 5 word) (m : word -> option byte) : Prop :=
  PB g regs m /\ IDB g m RcIdentModel.ID0 /\ FGB g m z72.
Definition PZ (g : ghost) (code : Z) (m : word -> option byte) : Prop :=
  b8 m (spk g 1824) code /\ bytes_at rsegs m (spk g 192) (repeat z8 32).
Definition Inv_U136e4 (g : ghost) (c : config) : Prop := CUTST g 0x136e4 [] (PB g) c.
Definition Inv_U136ec (g : ghost) (c : config) : Prop :=
  CUTST g 0x136ec [] (fun regs m => PB g regs m /\ IDB g m RcIdentModel.ID0) c.
Definition Inv_U136fc (g : ghost) (c : config) : Prop := CUTST g 0x136fc [] (P0 g) c.
Definition Inv_U1372c (g : ghost) (c : config) : Prop :=
  CUTST g 0x1372c [] (fun regs m => P0 g regs m /\ PZ g 0xee m /\ rg regs 10 (-1)) c.
Definition Inv_U13750 (g : ghost) (c : config) : Prop :=
  CUTST g 0x13750 [] (fun regs m => P0 g regs m /\ PZ g 0xee m /\ rg regs 8 (-1) /\ rg regs 10 (-1)) c.
Definition Inv_U13760 (g : ghost) (c : config) : Prop :=
  CUTST g 0x13760 [] (fun regs m => P0 g regs m /\ PZ g 0xee m /\ rg regs 10 (-1)) c.
Definition Inv_U13774 (g : ghost) (c : config) : Prop :=
  CUTST g 0x13774 [] (fun regs m => P0 g regs m /\ PZ g 0xee m /\ rg regs 8 (-1) /\ rg regs 10 (-1)) c.
Definition Inv_U13784 (g : ghost) (c : config) : Prop :=
  CUTST g 0x13784 [] (fun regs m => P0 g regs m /\ PZ g 0 m /\ rg regs 10 (-1)) c.
Definition Inv_U1379c (g : ghost) (c : config) : Prop :=
  CUTST g 0x1379c [] (fun regs m => P0 g regs m /\ b8 m (spk g 1824) 0 /\
    rg regs 10 reac_ctrl_kind_name_c.QMARK) c.

(* ---- 3.4 Frame loop, turn j (F, I, G); Φ is an existential of the cut ---- *)
Definition FCUT (g : ghost) (pc : Z) (j : nat) (P : Z -> bvmap 5 word -> (word -> option byte) -> Prop)
    (c : config) : Prop :=
  exists phi, CUTST g pc (hb1 phi (t_len (g_in g) j)) (P phi) c.

Definition Inv_U137d0_at (g : ghost) (j : nat) (c : config) : Prop := CUTST g 0x137d0 [] (LI g j) c.
Definition Inv_U137d0 (g : ghost) (c : config) : Prop := exists j, Inv_U137d0_at g j c.
(* v1.9: body in s5 (0x137fc `addi s5,s7,2`), len in s6 (0x13804 / 0x1380c), left - h in s3 (0x137e0 / 0x137f8). *)
Definition Inv_U13820_at (g : ghost) (j : nat) (c : config) : Prop :=
  FCUT g 0x13820 j (fun phi regs m => LK g j regs m /\ 1 <= t_left (g_in g) j /\ IFS g j m /\
    rg regs 21 (g_p g + t_body (g_in g) j) /\ rg regs 22 (t_len (g_in g) j) /\
    rg regs 19 (t_left (g_in g) j - t_h (g_in g) j) /\ rg regs 10 phi /\ phi <> 0) c.
Definition Inv_U13820 (g : ghost) (c : config) : Prop := exists j, Inv_U13820_at g j c.
Definition Inv_U13844_at (g : ghost) (j : nat) (c : config) : Prop :=
  FCUT g 0x13844 j (fun phi regs m => FT g j phi regs m /\ t_len (g_in g) j <> 0 /\ IFS g j m) c.
Definition Inv_U13844 (g : ghost) (c : config) : Prop := exists j, Inv_U13844_at g j c.
Definition Inv_U13898_at (g : ghost) (j : nat) (c : config) : Prop :=
  FCUT g 0x13898 j (fun phi regs m => FT g j phi regs m /\ t_len (g_in g) j <= 49 /\ IFS g j m) c.
Definition Inv_U13898 (g : ghost) (c : config) : Prop := exists j, Inv_U13898_at g j c.
Definition Inv_U13868_at (g : ghost) (j : nat) (c : config) : Prop :=
  FCUT g 0x13868 j (fun phi regs m => FT g j phi regs m /\ 50 <= t_len (g_in g) j /\ IFS g j m /\
    rg regs 10 (t_k (g_in g) j) /\ bytes_at rsegs m (spk g 1752) (t_B (g_in g) j)) c.
Definition Inv_U13868 (g : ghost) (c : config) : Prop := exists j, Inv_U13868_at g j c.
Definition Inv_U138a8_at (g : ghost) (j : nat) (c : config) : Prop :=
  FCUT g 0x138a8 j (fun phi regs m => FT g j phi regs m /\ t_len (g_in g) j <= 49 /\ IFS g j m /\
    rg regs 10 (t_k (g_in g) j) /\ bytes_at rsegs m (spk g 1752) (t_B (g_in g) j)) c.
Definition Inv_U138a8 (g : ghost) (c : config) : Prop := exists j, Inv_U138a8_at g j c.
Definition Inv_U13954_at (g : ghost) (j : nat) (c : config) : Prop :=
  FCUT g 0x13954 j (fun phi regs m => FB g j phi regs m /\ IFS g j m) c.
Definition Inv_U13954 (g : ghost) (c : config) : Prop := exists j, Inv_U13954_at g j c.
Definition Inv_U13964_at (g : ghost) (j : nat) (c : config) : Prop :=
  FCUT g 0x13964 j (fun phi regs m => FB g j phi regs m /\ IFS g j m /\ rg regs 10 (t_k (g_in g) j)) c.
Definition Inv_U13964 (g : ghost) (c : config) : Prop := exists j, Inv_U13964_at g j c.
Definition Inv_U13978_at (g : ghost) (j : nat) (c : config) : Prop :=
  FCUT g 0x13978 j (fun phi regs m => FB g j phi regs m /\ IFS g j m /\
    rg regs 10 (reac_ctrl_kind_name_c.kind_name_addr (t_k (g_in g) j))) c.
Definition Inv_U13978 (g : ghost) (c : config) : Prop := exists j, Inv_U13978_at g j c.
Definition Inv_U13984_at (g : ghost) (j : nat) (c : config) : Prop :=
  FCUT g 0x13984 j (fun phi regs m => FB g j phi regs m /\ IFS g j m /\
    rg regs 10 (reac_ctrl_kind_name_c.kind_name_addr (t_k (g_in g) j))) c.
Definition Inv_U13984 (g : ghost) (c : config) : Prop := exists j, Inv_U13984_at g j c.
(* The reply's three outputs: written when IR(Φ, len), else the 0 stored at 0x13998-0x139a0. *)
Definition RPS (g : ghost) (j : nat) (phi : Z) (m : word -> option byte) : Prop :=
  (t_ir (g_in g) j = true ->
     bytes_at rsegs m (spk g 1750) (RcReply.reply_addr (t_g (g_in g) j)) /\ q64 m (spk g 1736) (phi + 38) /\
     q64 m (spk g 1728) (r_pll (t_g (g_in g) j))) /\
  (t_ir (g_in g) j = false -> u16 m (spk g 1750) 0 /\ q64 m (spk g 1736) 0 /\ q64 m (spk g 1728) 0).
Definition Inv_U139bc_at (g : ghost) (j : nat) (c : config) : Prop :=
  FCUT g 0x139bc j (fun phi regs m => FB g j phi regs m /\ IFS g j m /\ rg regs 10 (t_r (g_in g) j) /\
    RPS g j phi m) c.
Definition Inv_U139bc (g : ghost) (c : config) : Prop := exists j, Inv_U139bc_at g j c.
Definition Inv_U13a14_at (g : ghost) (j : nat) (c : config) : Prop :=
  FCUT g 0x13a14 j (fun phi regs m => FB g j phi regs m /\ IFS g j m /\ t_ir (g_in g) j = true /\
    RPS g j phi m /\ rg regs 11 (r_pll (t_g (g_in g) j))) c.
Definition Inv_U13a14 (g : ghost) (c : config) : Prop := exists j, Inv_U13a14_at g j c.
(* After record_sum_closes(blk + 16, pll + 5): a0 is 1 exactly when the record sums to 0 mod 128. *)
Definition Inv_U13a28_at (g : ghost) (j : nat) (c : config) : Prop :=
  FCUT g 0x13a28 j (fun phi regs m => FB g j phi regs m /\ IFS g j m /\ t_ir (g_in g) j = true /\
    RPS g j phi m /\
    rg regs 10 (if RcRec.recsum (RcFrag.bsl (t_g (g_in g) j) 34 (r_pll (t_g (g_in g) j) + 5)) =? 0
                then 1 else 0)) c.
Definition Inv_U13a28 (g : ghost) (c : config) : Prop := exists j, Inv_U13a28_at g j c.
(* After the reply arm: id = IDr. *)
Definition GA (g : ghost) (j : nat) (phi : Z) (regs : bvmap 5 word) (m : word -> option byte) : Prop :=
  FB g j phi regs m /\ IDb g (t_IDr (g_in g) j) m /\ FGj g j m /\ FSj g j m.
Definition Inv_U13a64_at (g : ghost) (j : nat) (c : config) : Prop :=
  FCUT g 0x13a64 j (fun phi regs m => GA g j phi regs m /\ t_ir (g_in g) j = true /\
    rg regs 10 (fst (RcIdentModel.ING (t_ID (g_in g) j) (r_addr (t_g (g_in g) j)) (r_pl (t_g (g_in g) j))))) c.
Definition Inv_U13a64 (g : ghost) (c : config) : Prop := exists j, Inv_U13a64_at g j c.
Definition Inv_U13a68_at (g : ghost) (j : nat) (c : config) : Prop := FCUT g 0x13a68 j (GA g j) c.
Definition Inv_U13a68 (g : ghost) (c : config) : Prop := exists j, Inv_U13a68_at g j c.
Definition Inv_U13a78_at (g : ghost) (j : nat) (c : config) : Prop :=
  FCUT g 0x13a78 j (fun phi regs m => GA g j phi regs m /\ bytes_at rsegs m (spk g 192) (t_FG (g_in g) j)) c.
Definition Inv_U13a78 (g : ghost) (c : config) : Prop := exists j, Inv_U13a78_at g j c.
(* After the fragment call: frag = FGf, FS and FI still of turn j's start. *)
Definition GF (g : ghost) (j : nat) (phi : Z) (regs : bvmap 5 word) (m : word -> option byte) : Prop :=
  FB g j phi regs m /\ IDb g (t_IDr (g_in g) j) m /\ FGb g (t_FGf (g_in g) j) m /\ FSj g j m /\
  bytes_at rsegs m (spk g 192) (t_FG (g_in g) j) /\
  (t_rf (g_in g) j = 1 ->
     u16 m (spk g 1750) (RcFrag.fg_addr (t_FG (g_in g) j) (t_g (g_in g) j)) /\
     q64 m (spk g 1736) (spk g 139) /\ q64 m (spk g 1728) (f_pll (t_FG (g_in g) j) (t_g (g_in g) j))).
Definition Inv_U13a94_at (g : ghost) (j : nat) (c : config) : Prop :=
  FCUT g 0x13a94 j (fun phi regs m => GF g j phi regs m /\ rg regs 10 (t_rf (g_in g) j)) c.
Definition Inv_U13a94 (g : ghost) (c : config) : Prop := exists j, Inv_U13a94_at g j c.
(* rf in s10 (0x13a98 `mv s10,a0`) from U13ab0 to U13b04. *)
Definition Inv_U13ab0_at (g : ghost) (j : nat) (c : config) : Prop :=
  FCUT g 0x13ab0 j (fun phi regs m => GF g j phi regs m /\ rg regs 26 (t_rf (g_in g) j) /\
    t_sum_ok (g_in g) j = false /\ rg regs 10 0) c.
Definition Inv_U13ab0 (g : ghost) (c : config) : Prop := exists j, Inv_U13ab0_at g j c.
Definition Inv_U13ab4_at (g : ghost) (j : nat) (c : config) : Prop :=
  FCUT g 0x13ab4 j (fun phi regs m => GF g j phi regs m /\ rg regs 26 (t_rf (g_in g) j)) c.
Definition Inv_U13ab4 (g : ghost) (c : config) : Prop := exists j, Inv_U13ab4_at g j c.
Definition Inv_U13af0_at (g : ghost) (j : nat) (c : config) : Prop :=
  FCUT g 0x13af0 j (fun phi regs m => GF g j phi regs m /\ rg regs 26 (t_rf (g_in g) j) /\
    t_rf (g_in g) j = 1 /\ rg regs 11 (f_pll (t_FG (g_in g) j) (t_g (g_in g) j))) c.
Definition Inv_U13af0 (g : ghost) (c : config) : Prop := exists j, Inv_U13af0_at g j c.
(* After record_sum_closes(buf + 7, pll + 5) over the frag bytes (buf + 7 = frag + 15 = sp+135). *)
Definition Inv_U13b04_at (g : ghost) (j : nat) (c : config) : Prop :=
  FCUT g 0x13b04 j (fun phi regs m => GF g j phi regs m /\ rg regs 26 (t_rf (g_in g) j) /\
    t_rf (g_in g) j = 1 /\
    rg regs 10 (if RcRec.recsum (RcFrag.bsl (t_FGf (g_in g) j) 15
                                   (f_pll (t_FG (g_in g) j) (t_g (g_in g) j) + 5)) =? 0
                then 1 else 0)) c.
Definition Inv_U13b04 (g : ghost) (c : config) : Prop := exists j, Inv_U13b04_at g j c.
(* After the fragment arm: id = ID_(j+1), frag = FG_(j+1) = FGf, FS still of turn j. *)
Definition GE (g : ghost) (j : nat) (phi : Z) (regs : bvmap 5 word) (m : word -> option byte) : Prop :=
  FB g j phi regs m /\ IDj g (S j) m /\ FGb g (t_FGf (g_in g) j) m /\ FSj g j m.
Definition Inv_U13b60_at (g : ghost) (j : nat) (c : config) : Prop :=
  FCUT g 0x13b60 j (fun phi regs m => GE g j phi regs m /\ t_rf (g_in g) j = 1 /\
    rg regs 10 (fst (RcIdentModel.ING (t_IDr (g_in g) j) (RcFrag.fg_addr (t_FG (g_in g) j) (t_g (g_in g) j))
                       (f_pl (t_len (g_in g) j) (t_FG (g_in g) j) (t_g (g_in g) j))))) c.
Definition Inv_U13b60 (g : ghost) (c : config) : Prop := exists j, Inv_U13b60_at g j c.
Definition Inv_U13b64_at (g : ghost) (j : nat) (c : config) : Prop := FCUT g 0x13b64 j (GE g j) c.
Definition Inv_U13b64 (g : ghost) (c : config) : Prop := exists j, Inv_U13b64_at g j c.
Definition Inv_U13c58_at (g : ghost) (j : nat) (c : config) : Prop := FCUT g 0x13c58 j (EA g j) c.
Definition Inv_U13c58 (g : ghost) (c : config) : Prop := exists j, Inv_U13c58_at g j c.

(* ---- 3.5 is_8819, check_ports, classify, match, latch (E, Q, C, W, X) ---- *)
Definition EB (g : ghost) (j : nat) (phi : Z) (regs : bvmap 5 word) (m : word -> option byte) : Prop :=
  EA g j phi regs m /\ t_8819 (g_in g) j = true.
Definition Inv_U13c6c_at (g : ghost) (j : nat) (c : config) : Prop :=
  FCUT g 0x13c6c j (fun phi regs m => EB g j phi regs m /\ rg regs 10 0) c.
Definition Inv_U13c6c (g : ghost) (c : config) : Prop := exists j, Inv_U13c6c_at g j c.
Definition Inv_U13c88_at (g : ghost) (j : nat) (c : config) : Prop :=
  FCUT g 0x13c88 j (fun phi regs m => EB g j phi regs m /\ rg regs 10 0) c.
Definition Inv_U13c88 (g : ghost) (c : config) : Prop := exists j, Inv_U13c88_at g j c.
Definition Inv_U13cf4_at (g : ghost) (j : nat) (c : config) : Prop :=
  FCUT g 0x13cf4 j (fun phi regs m => EB g j phi regs m /\
    rg regs 10 (if t_sum_ok (g_in g) j then 0 else -1)) c.
Definition Inv_U13cf4 (g : ghost) (c : config) : Prop := exists j, Inv_U13cf4_at g j c.
Definition Inv_U13da0_at (g : ghost) (j : nat) (c : config) : Prop :=
  FCUT g 0x13da0 j (fun phi regs m => EQ g j phi regs m /\
    rg regs 19 (t_want_v (g_in g) j) /\ rg regs 10 (t_want_v (g_in g) j)) c.
Definition Inv_U13da0 (g : ghost) (c : config) : Prop := exists j, Inv_U13da0_at g j c.
Definition Inv_U13dc0_at (g : ghost) (j : nat) (c : config) : Prop :=
  FCUT g 0x13dc0 j (fun phi regs m => EQ g j phi regs m /\ rg regs 10 (t_rp (g_in g) j) /\ PORTS g j m) c.
Definition Inv_U13dc0 (g : ghost) (c : config) : Prop := exists j, Inv_U13dc0_at g j c.
Definition Inv_U13dd8_at (g : ghost) (j : nat) (c : config) : Prop :=
  FCUT g 0x13dd8 j (fun phi regs m => QB g j phi regs m /\ rg regs 10 (t_unk (g_in g) j)) c.
Definition Inv_U13dd8 (g : ghost) (c : config) : Prop := exists j, Inv_U13dd8_at g j c.
Definition Inv_U13de8_at (g : ghost) (j : nat) (c : config) : Prop :=
  FCUT g 0x13de8 j (fun phi regs m => QB g j phi regs m /\ rg regs 26 (t_unk (g_in g) j) /\
    rg regs 10 (t_unk (g_in g) j)) c.
Definition Inv_U13de8 (g : ghost) (c : config) : Prop := exists j, Inv_U13de8_at g j c.
Definition Inv_U13e28_at (g : ghost) (j : nat) (c : config) : Prop :=
  FCUT g 0x13e28 j (fun phi regs m => QB g j phi regs m /\ rg regs 26 (t_unk (g_in g) j) /\
    t_rp (g_in g) j = 0 /\ 0 <= t_unk (g_in g) j /\ T2 regs) c.
Definition Inv_U13e28 (g : ghost) (c : config) : Prop := exists j, Inv_U13e28_at g j c.
Definition Inv_U13ed4_at (g : ghost) (j : nat) (c : config) : Prop :=
  FCUT g 0x13ed4 j (fun phi regs m => QB g j phi regs m /\ rg regs 26 (t_unk (g_in g) j) /\
    t_rp (g_in g) j = 0 /\ 0 <= t_unk (g_in g) j /\
    rg regs 11 (RcLeaf.n_in (t_pbs (g_in g) j)) /\ rg regs 10 (RcLeaf.n_out (t_pbs (g_in g) j)) /\
    rg regs 12 (RcLeaf.cnt is_empty (t_pbs (g_in g) j) 12) /\
    rg regs 17 (RcPorts.pu_first (t_pbs (g_in g) j) 12)) c.
Definition Inv_U13ed4 (g : ghost) (c : config) : Prop := exists j, Inv_U13ed4_at g j c.
Definition Inv_U13f98_at (g : ghost) (j : nat) (c : config) : Prop := FCUT g 0x13f98 j (CC g j) c.
Definition Inv_U13f98 (g : ghost) (c : config) : Prop := exists j, Inv_U13f98_at g j c.
Definition CLS (g : ghost) (j : nat) (regs : bvmap 5 word) (m : word -> option byte) : Prop :=
  bytes_at rsegs m (spk g 1688) (t_B (g_in g) j) /\
  bytes_at rsegs m (spk g 1684)
    (reac_ctrl_classify_box_frame_c.reac_ctrl_classify_box_frame_ev (t_cls (g_in g) j) (le4 (Z_to_bv 64 (-1)))).
Definition Inv_U13fb8_at (g : ghost) (j : nat) (c : config) : Prop :=
  FCUT g 0x13fb8 j (fun phi regs m => CC g j phi regs m /\ CLS g j regs m /\
    rg regs 10 (RcClassify.cl_r (t_cls (g_in g) j))) c.
Definition Inv_U13fb8 (g : ghost) (c : config) : Prop := exists j, Inv_U13fb8_at g j c.
Definition Inv_U13fec_at (g : ghost) (j : nat) (c : config) : Prop :=
  FCUT g 0x13fec j (fun phi regs m => CC g j phi regs m /\ CLS g j regs m /\ t_cls (g_in g) j <> None /\
    (getr regs 10 = Z_to_bv 64 0 <-> firstn 6 (skipn 4 (t_B (g_in g) j)) = OUR (g_in g))) c.
Definition Inv_U13fec (g : ghost) (c : config) : Prop := exists j, Inv_U13fec_at g j c.
Definition Inv_U14008_at (g : ghost) (j : nat) (c : config) : Prop := FCUT g 0x14008 j (CC g j) c.
Definition Inv_U14008 (g : ghost) (c : config) : Prop := exists j, Inv_U14008_at g j c.
Definition Inv_U14048_at (g : ghost) (j : nat) (c : config) : Prop :=
  FCUT g 0x14048 j (fun phi regs m => CC g j phi regs m /\ t_rowsel (g_in g) j = true /\ rg regs 10 CAT /\
    q64 m (spk g 1824) CAT_N) c.
Definition Inv_U14048 (g : ghost) (c : config) : Prop := exists j, Inv_U14048_at g j c.
(* row_of_block, row i (i : nat, 0 .. 10): s10 = cat, s3 = i, s9 = the row, count reread from sp+1824. *)
Definition WB (g : ghost) (j i : nat) (phi : Z) (regs : bvmap 5 word) (m : word -> option byte) : Prop :=
  RSEL g j phi regs m /\ (i <= 10)%nat /\ rg regs 26 CAT /\ rg regs 19 (Z.of_nat i) /\
  rg regs 25 (CAT + CAT_ROW * Z.of_nat i) /\ q64 m (spk g 1824) CAT_N /\
  (forall i', (i' < i)%nat -> t_blk (g_in g) j <> decl_i (Z.of_nat i')).
Definition Inv_U14064_at (g : ghost) (j i : nat) (c : config) : Prop := FCUT g 0x14064 j (WB g j i) c.
Definition Inv_U14064 (g : ghost) (c : config) : Prop := exists j i, Inv_U14064_at g j i c.
Definition Inv_U14090_at (g : ghost) (j i : nat) (c : config) : Prop :=
  FCUT g 0x14090 j (fun phi regs m => WB g j i phi regs m /\ rg regs 20 (CAT + CAT_ROW * Z.of_nat i) /\
    rg regs 10 1 /\ bytes_at rsegs m (spk g 1792) (decl_i (Z.of_nat i))) c.
Definition Inv_U14090 (g : ghost) (c : config) : Prop := exists j i, Inv_U14090_at g j i c.
Definition Inv_U140a4_at (g : ghost) (j i : nat) (c : config) : Prop :=
  FCUT g 0x140a4 j (fun phi regs m => WB g j i phi regs m /\ rg regs 20 (CAT + CAT_ROW * Z.of_nat i) /\
    bytes_at rsegs m (spk g 1792) (decl_i (Z.of_nat i)) /\
    (getr regs 10 = Z_to_bv 64 0 <-> t_blk (g_in g) j = decl_i (Z.of_nat i))) c.
Definition Inv_U140a4 (g : ghost) (c : config) : Prop := exists j i, Inv_U140a4_at g j i c.
Definition Inv_U140b0_at (g : ghost) (j i : nat) (c : config) : Prop :=
  FCUT g 0x140b0 j (fun phi regs m => WB g j i phi regs m /\ t_blk (g_in g) j <> decl_i (Z.of_nat i)) c.
Definition Inv_U140b0 (g : ghost) (c : config) : Prop := exists j i, Inv_U140b0_at g j i c.
Definition Inv_U140c0_at (g : ghost) (j : nat) (c : config) : Prop :=
  FCUT g 0x140c0 j (fun phi regs m => CC7 g j phi regs m /\ t_want_m (g_in g) j = 0) c.
Definition Inv_U140c0 (g : ghost) (c : config) : Prop := exists j, Inv_U140c0_at g j c.
Definition Inv_U140c4_at (g : ghost) (j : nat) (c : config) : Prop :=
  FCUT g 0x140c4 j (fun phi regs m => CC7 g j phi regs m /\ rg regs 25 (t_want_m (g_in g) j)) c.
Definition Inv_U140c4 (g : ghost) (c : config) : Prop := exists j, Inv_U140c4_at g j c.
Definition Inv_U140d0_at (g : ghost) (j : nat) (c : config) : Prop :=
  FCUT g 0x140d0 j (fun phi regs m => CC7 g j phi regs m /\ rg regs 25 (t_want_m (g_in g) j) /\
    rg regs 10 (t_want (g_in g) j)) c.
Definition Inv_U140d0 (g : ghost) (c : config) : Prop := exists j, Inv_U140d0_at g j c.
(* v1.8 U140e8 (deleted instruction): the return point of `jal free`, see the header. *)
Definition Inv_U140dc_at (g : ghost) (j : nat) (c : config) : Prop :=
  CUTST g 0x140dc [] (fun regs m => LK g j regs m /\ FC g j regs m /\ IFS g (S j) m) c.
Definition Inv_U140dc (g : ghost) (c : config) : Prop := exists j, Inv_U140dc_at g j c.
Definition Inv_U140f8 (g : ghost) (c : config) : Prop :=
  CUTST g 0x140f8 [] (fun regs m => IDj g (fJ (g_in g)) m) c.
Definition Inv_U14110 (g : ghost) (c : config) : Prop :=
  CUTST g 0x14110 [] (fun regs m => IDj g (fJ (g_in g)) m /\
    RcIdentModel.has_model_name (t_ID (g_in g) (fJ (g_in g))) = 1 /\
    rg regs 10 (spk g 79 + Z.of_nat (RcIdentModel.first_zero
                                        (RcIdentModel.model_name (t_ID (g_in g) (fJ (g_in g))))))) c.
Definition Inv_U14114 (g : ghost) (c : config) : Prop := CUTST g 0x14114 [] (fun _ _ => True) c.

End Slot.
