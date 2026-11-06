(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Copyright 2026 Theorem Labs *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_decode/lib/Prog/LLVMFuzzerTestOneInput_fr.v, with its module paths and module names changed; 458 of its 575 lines of code are new or changed and 410 lines of the source are left out. *)
(* Cut-free (agreement) copy of lib/U/Prog/Seg/Tac_slot.v, over U/Prog/SlotInvCF.v (SR := SRcf). Model:
   reac-pw/fuzz_role's U/Prog/SegCF/Tac_slot.v, as libreac/fuzz_ctrl's released
   U/Prog/SegCF/*.v copy its U/Prog/Seg/*.v: the same text with SlotFR, SlotInv -> SlotInvCF, Seg -> SegCF, the
   segment statements from SegCF/StmtsCF.v, frame_facts_ubsan -> SlotInvCF.frame_facts_cf and the allocator
   contracts in their cut-free forms (frame_allocator_cf, malloc_contract_cfg, free_contract_cf); ff_lib_room and ff_room read the agreement room 128 <= sb_cap <= CAP_AG.
   The text of the original follows. *)
(* Shared helpers for the segment lemmas of reac-pw/fuzz_rate LLVMFuzzerTestOneInput (UBSan): the accessors of
   FrameAPI.frame_facts_cf (the ff_ lemmas), the image bound SL_TOP, munch/writability transport, the run lemmas
   sl_run and sl_run_fp (evt -> SR through MemNorm; sl_run_fp for a run that ends with its own FP registers and
   fflags), FR from scratch (sl_fr_of), FR across a Kind A run (sl_fr_run, sl_mid, sl_mid_fp), and FR's window and
   bounds.
   The plain file (lib/Prog/Seg/Tac_slot.v) with the UBSan numbers below. Taken from reac-pw/fuzz_role's copy, itself reac-pw/fuzz_pin's U/Prog/Seg/Tac_slot.v, itself libreac/fuzz_ctrl's released Prog/Seg/Tac_slot.v
   (origin/ossv/recipes 25e3d17bdb50) adapted, same lemma names, with rate's UBSan numbers: the frame is 592 bytes, so the
   saved registers at S - 104 are fsp g + 488 (sl_fp); the sink and errno numerals (sl_sink, sl_errno_val) are
   frame_facts_cf's (ofl_head 0x508b0, ofl_lock 0x508a8, __libc 0x50480, builtin_tls 0x301f0); the last PT_LOAD
   ends at 0x50cc8, under SL_TOP. Every use of frame_facts_cf goes through the named accessors (the ff_ lemmas
   below), proved by destructing frame_facts_cf in its own order. sl_run_fp and sl_mid_fp are new: the run's
   final FP state is any (F', fc'), and the continuation is at the FP state mkFP F' fc'. *)
From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.U.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.U.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.U.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Lib Require Import Mem Frame.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Lib Require MState Regs6ss RegisterBridge Exec Cells Step.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.U Require Import Img0 Contract FrameAPI SlotAgree.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.U.Prog Require Import SlotInvCF.
Import ListNotations.
Open Scope Z_scope.

(* Every reserved image segment ends at or below SL_TOP (the last PT_LOAD ends at 0x50cc8; the sink cells end at
   0x508b8). *)
Definition SL_TOP : Z := 0x60000.

Lemma sl_find_segment_in : forall segs a n seg, find_segment segs a n = Some seg ->
  In seg segs /\ Z.of_N (seg_base seg) <= a /\ a + n <= Z.of_N (seg_base seg) + Z.of_N (seg_size seg).
Proof.
  induction segs as [|s segs IH]; intros a n seg E; cbn in E; [discriminate|].
  match type of E with context [if ?c then _ else _] => destruct c eqn:C end.
  - injection E as <-. apply andb_true_iff in C as [C1 C2]. apply Z.leb_le in C1. apply Z.leb_le in C2.
    split; [left; reflexivity | lia].
  - destruct (IH a n seg E) as (H1 & H2 & H3). split; [right; exact H1 | lia].
Qed.

Lemma sl_rsegs_ok : forallb (fun s => let r := segment_reservation s in
    (bv_unsigned (fst r) <=? Z.of_N (seg_base s)) &&
    (Z.of_N (seg_base s) + Z.of_N (seg_size s) <=? bv_unsigned (fst r) + bv_unsigned (snd r)) &&
    (bv_unsigned (fst r) + bv_unsigned (snd r) <=? SL_TOP)) rsegs = true.
Proof. vm_compute. reflexivity. Qed.

Lemma sl_rsegs_seg : forall seg, In seg rsegs ->
  bv_unsigned (fst (segment_reservation seg)) <= Z.of_N (seg_base seg) /\
  Z.of_N (seg_base seg) + Z.of_N (seg_size seg) <=
    bv_unsigned (fst (segment_reservation seg)) + bv_unsigned (snd (segment_reservation seg)) /\
  bv_unsigned (fst (segment_reservation seg)) + bv_unsigned (snd (segment_reservation seg)) <= SL_TOP.
Proof.
  intros seg Hin. pose proof (proj1 (forallb_forall _ _) sl_rsegs_ok seg Hin) as H. cbv beta zeta in H.
  apply andb_true_iff in H as [H H3]. apply andb_true_iff in H as [H1 H2].
  apply Z.leb_le in H1. apply Z.leb_le in H2. apply Z.leb_le in H3. auto.
Qed.

Lemma sl_find_top : forall a n seg, find_segment rsegs a n = Some seg -> a + n <= SL_TOP.
Proof.
  intros a n seg E. destruct (sl_find_segment_in rsegs a n seg E) as (Hin & H1 & H2).
  destruct (sl_rsegs_seg seg Hin) as (R1 & R2 & R3). lia.
Qed.

Lemma sl_in_img_top : forall B a, ms_segs B = rsegs -> in_img B a -> 0 <= a < SL_TOP.
Proof.
  intros B a HS [_ (s & Hin & Hr)]. rewrite HS in Hin. unfold segments_reserved in Hin.
  apply in_map_iff in Hin as (seg & <- & Hseg).
  destruct (sl_rsegs_seg seg Hseg) as (R1 & R2 & R3).
  pose proof (bv_unsigned_in_range _ (fst (segment_reservation seg))) as R. lia.
Qed.

Lemma sl_wview_hi : forall m a, SL_TOP <= a < 2 ^ 64 -> wview rsegs m (Z_to_bv 64 a) = m (Z_to_bv 64 a).
Proof.
  intros m a Ha. unfold wview. destruct (m (Z_to_bv 64 a)) as [b|]; [reflexivity|].
  rewrite (MState.unsigned_lit a ltac:(unfold SL_TOP in Ha; lia)).
  destruct (find_segment rsegs a 1) as [seg|] eqn:E; [|reflexivity].
  exfalso. pose proof (sl_find_top a 1 seg E). unfold SL_TOP in *. lia.
Qed.

Lemma sl_outside_dec : forall W x, {Frame.outside W x} + {~ Frame.outside W x}.
Proof.
  induction W as [|[lo hi] W IH]; intros x; cbn [Frame.outside]; [left; exact I|].
  destruct (Z_le_dec lo x) as [H1|H1]; [destruct (Z_lt_dec x hi) as [H2|H2]|].
  - right. intros [H _]. lia.
  - destruct (IH x) as [O|O]; [left; split; [lia | exact O] | right; intros [_ H]; exact (O H)].
  - destruct (IH x) as [O|O]; [left; split; [lia | exact O] | right; intros [_ H]; exact (O H)].
Qed.

Lemma sl_unch : forall W m m' lo hi, Frame.munch W m m' ->
  (forall x, 0 <= x < 2 ^ 64 -> ~ Frame.outside W x -> lo <= x < hi) ->
  forall a, 0 <= a < 2 ^ 64 -> ~ (lo <= a < hi) -> m' (Z_to_bv 64 a) = m (Z_to_bv 64 a).
Proof.
  intros W m m' lo hi MU HW a Ha Hn. apply MU. rewrite (MState.unsigned_lit a Ha).
  destruct (sl_outside_dec W a) as [O|O]; [exact O|]. exfalso. apply Hn. exact (HW a Ha O).
Qed.

Lemma sl_eq_at : forall (m m' : word -> option byte) a, m' (Z_to_bv 64 a) = m (Z_to_bv 64 a) ->
  mbyte rsegs m' a = mbyte rsegs m a /\ (writable_at rsegs m a <-> writable_at rsegs m' a).
Proof.
  intros m m' a E. unfold mbyte, writable_at, wview. rewrite E. split; [reflexivity | tauto].
Qed.

Lemma sl_mkFP : forall f : FPState, mkFP (@fp_regs f) (@fp_csr f) = f.
Proof. intros []. reflexivity. Qed.

Lemma sl_eqv_mkst : forall R F pc fc m ro ms',
  Regs6ss.ms_eqv (MState.MS R F pc fc None m ro) ms' ->
  ms' = @mkst (mkFP F fc) (ms_regs ms') pc m ro /\ Regs6ss.xregs_eqv R (ms_regs ms').
Proof.
  intros R F pc fc m ro ms' (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8).
  destruct ms' as [r f p s v c mm rr]; cbn in *. subst. split; [reflexivity | exact H1].
Qed.

Lemma sl_getr_eqv : forall R R' r, Regs6ss.xregs_eqv R R' -> getr R' r = getr R r.
Proof.
  intros R R' r H. unfold getr. destruct (bv_eqb r 0) eqn:E; [reflexivity|].
  symmetry. apply H. exact E.
Qed.

Lemma sl_mkR_of : forall regs, Regs6ss.mkR_of regs = Frame.mkR (getr regs 1) (getr regs 2) (getr regs 3) (getr regs 4) (getr regs 5) (getr regs 6) (getr regs 7) (getr regs 8) (getr regs 9) (getr regs 10) (getr regs 11) (getr regs 12) (getr regs 13) (getr regs 14) (getr regs 15) (getr regs 16) (getr regs 17) (getr regs 18) (getr regs 19) (getr regs 20) (getr regs 21) (getr regs 22) (getr regs 23) (getr regs 24) (getr regs 25) (getr regs 26) (getr regs 27) (getr regs 28) (getr regs 29) (getr regs 30) (getr regs 31).
Proof. intros regs. reflexivity. Qed.

Lemma sl_bytes_cells_tail : forall m A n j cs,
  Step.rw_cells rsegs m A (Cells.CB n j :: cs) -> bytes_at rsegs m (A + Z.of_nat n) (Cells.cells_bytes cs).
Proof.
  intros m A n j cs [[Hwf Hb] _]. cbn [Cells.cells_bytes Cells.cbytes] in Hb.
  apply (proj1 (bytes_at_app rsegs m A j (Cells.cells_bytes cs))) in Hb as [_ Hb].
  cbn [Cells.cells_wf] in Hwf. destruct Hwf as [Hl _]. rewrite Hl in Hb. exact Hb.
Qed.

Lemma sl_bytes_keep : forall m m' a bs, bytes_at rsegs m a bs ->
  (forall i, 0 <= i < Z.of_nat (length bs) -> m' (Z_to_bv 64 (a + i)) = m (Z_to_bv 64 (a + i))) ->
  bytes_at rsegs m' a bs.
Proof.
  intros m m' a bs (H1 & H2 & H3) HE. split; [exact H1|]. split; [exact H2|].
  intros i Hi. unfold Mem.mrd, Mem.wa. rewrite (HE (Z.of_nat i) ltac:(lia)). exact (H3 i Hi).
Qed.

Lemma sl_rw_of_stk : forall m lo hi a n, Frame.stk rsegs m lo hi -> lo <= a -> a + Z.of_nat n <= hi ->
  exists bs, Step.rw_cells rsegs m a [Cells.CB n bs].
Proof.
  intros m lo hi a n ST H1 H2.
  destruct (stk_split rsegs m lo (a + Z.of_nat n) hi ST ltac:(lia)) as [ST1 _].
  destruct (stk_carve rsegs m lo (a + Z.of_nat n) n ST1 ltac:(lia)) as [_ (junk & HJ)].
  exists junk. replace a with (a + Z.of_nat n - Z.of_nat n) at 1 by lia. exact HJ.
Qed.

Lemma sl_rw_bytes : forall m A n bs, Step.rw_cells rsegs m A [Cells.CB n bs] -> bytes_at rsegs m A bs.
Proof. intros m A n bs [[_ Hb] _]. cbn [Cells.cells_bytes Cells.cbytes] in Hb. rewrite app_nil_r in Hb. exact Hb. Qed.

Lemma sl_cells_bytes : forall m A cs, Step.rw_cells rsegs m A cs -> bytes_at rsegs m A (Cells.cells_bytes cs).
Proof. intros m A cs [[_ Hb] _]. exact Hb. Qed.

Lemma sl_bytes_nil : forall m a, 0 <= a <= 2 ^ 64 -> bytes_at rsegs m a [].
Proof. intros m a Ha. split; [lia|]. split; [cbn; lia|]. intros i Hi. cbn in Hi. lia. Qed.

(* Writes of a segment (below the saved registers at S - 104) stay inside [S - K, S - 104). *)
Lemma sl_fp : forall g x, 0 <= x < 2 ^ 64 -> ~ Frame.outside [(g_S g - SLOT_K, fsp g + 488)] x ->
  g_S g - SLOT_K <= x < g_S g - 104.
Proof.
  intros g x Hx O. unfold fsp, SLOT_FRAME in *.
  destruct (Z_le_dec (g_S g - SLOT_K) x); destruct (Z_lt_dec x (g_S g - 592 + 488)); try lia;
    exfalso; apply O; cbn [Frame.outside]; (split; [lia | exact I]).
Qed.

Lemma sl_fp1 : forall g lo hi x, g_S g - SLOT_K <= lo -> hi <= g_S g - 104 ->
  0 <= x < 2 ^ 64 -> ~ Frame.outside [(lo, hi)] x -> g_S g - SLOT_K <= x < g_S g - 104.
Proof.
  intros g lo hi x H1 H2 Hx O.
  destruct (Z_le_dec lo x); destruct (Z_lt_dec x hi); try lia;
    exfalso; apply O; cbn [Frame.outside]; (split; [lia | exact I]).
Qed.

Lemma sl_saved_len : forall ra g, length (saved_bytes ra g) = 104%nat.
Proof. intros ra g. unfold saved_bytes. rewrite !length_app, !length_le8. reflexivity. Qed.

Section R.
Context {fx : FPState}.

Lemma sl_run : forall regs pc mem md (Q : machine_state -> Prop) (P : config -> Prop),
  m_halted md = None -> m_vm_lazy md = [] -> ro_agree rsegs mem ->
  Exec.evt rsegs Q (MState.MS (Regs6ss.mkR_of regs) fp_regs pc fp_csr None (normalize rsegs mem) (seg_rom rsegs)) ->
  (forall ms, Q ms -> exists R pc' m', ms = MState.MS R fp_regs pc' fp_csr None m' (seg_rom rsegs)) ->
  (forall R pc' m0', Q (MState.MS R fp_regs pc' fp_csr None m0' (seg_rom rsegs)) ->
     forall regs' m', Regs6ss.xregs_eqv R regs' -> mem_rel rsegs m' m0' -> ro_same rsegs mem m' ->
     SR rsegs (mkCfg (mkst regs' pc' m' (seg_rom rsegs)) md) P) ->
  SR rsegs (mkCfg (mkst regs pc mem (seg_rom rsegs)) md) P.
Proof.
  intros regs pc mem md Q P Hh Hl Hro HE Hform HK.
  apply (evt_SR_canon rsegs _ (fun s => exists s0, Q s0 /\ ms_rel rsegs s s0 /\ ro_same rsegs mem (ms_mem s)) md P);
    [| exact Hh | exact Hl |].
  - change (RegisterBridge.canonical_register_state (mkst regs pc mem (seg_rom rsegs)))
      with (MState.MS (Regs6ss.mkR_of regs) fp_regs pc fp_csr None mem (seg_rom rsegs)).
    apply evt_normalize; [exact wx_apart_rsegs | exact Hro | exact HE].
  - intros ms' (can & (s0 & HQ & Hrel & Hsame) & Heq).
    destruct (Hform s0 HQ) as (R & pc' & m0' & ->).
    destruct can as [cr cf cp cs cv cc cm co].
    destruct Hrel as (E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8).
    cbn [ms_regs ms_fregs ms_pc_val ms_svc_pending ms_resv ms_fcsr ms_mem ms_rom MState.MS] in *. subst.
    destruct (sl_eqv_mkst R fp_regs pc' fp_csr cm (seg_rom rsegs) ms' Heq) as [Ems Hx].
    rewrite Ems, sl_mkFP.
    exact (HK R pc' m0' HQ _ cm Hx E8 Hsame).
Qed.

(* sl_run for a run whose final states carry their own FP registers F' and fcsr fc' (FP code: the FP registers
   are written and fflags accrue): the continuation runs at the FP state mkFP F' fc'. *)
Lemma sl_run_fp : forall regs pc mem md (Q : machine_state -> Prop) (P : config -> Prop),
  m_halted md = None -> m_vm_lazy md = [] -> ro_agree rsegs mem ->
  Exec.evt rsegs Q (MState.MS (Regs6ss.mkR_of regs) fp_regs pc fp_csr None (normalize rsegs mem) (seg_rom rsegs)) ->
  (forall ms, Q ms -> exists R F' pc' fc' m', ms = MState.MS R F' pc' fc' None m' (seg_rom rsegs)) ->
  (forall R F' pc' fc' m0', Q (MState.MS R F' pc' fc' None m0' (seg_rom rsegs)) ->
     forall regs' m', Regs6ss.xregs_eqv R regs' -> mem_rel rsegs m' m0' -> ro_same rsegs mem m' ->
     SR rsegs (mkCfg (@mkst (mkFP F' fc') regs' pc' m' (seg_rom rsegs)) md) P) ->
  SR rsegs (mkCfg (mkst regs pc mem (seg_rom rsegs)) md) P.
Proof.
  intros regs pc mem md Q P Hh Hl Hro HE Hform HK.
  apply (evt_SR_canon rsegs _ (fun s => exists s0, Q s0 /\ ms_rel rsegs s s0 /\ ro_same rsegs mem (ms_mem s)) md P);
    [| exact Hh | exact Hl |].
  - change (RegisterBridge.canonical_register_state (mkst regs pc mem (seg_rom rsegs)))
      with (MState.MS (Regs6ss.mkR_of regs) fp_regs pc fp_csr None mem (seg_rom rsegs)).
    apply evt_normalize; [exact wx_apart_rsegs | exact Hro | exact HE].
  - intros ms' (can & (s0 & HQ & Hrel & Hsame) & Heq).
    destruct (Hform s0 HQ) as (R & F' & pc' & fc' & m0' & ->).
    destruct can as [cr cf cp cs cv cc cm co].
    destruct Hrel as (E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8).
    cbn [ms_regs ms_fregs ms_pc_val ms_svc_pending ms_resv ms_fcsr ms_mem ms_rom MState.MS] in *.
    subst cr cf cp cs cv cc co.
    destruct (sl_eqv_mkst R F' pc' fc' cm (seg_rom rsegs) ms' Heq) as [Ems Hx].
    rewrite Ems.
    exact (HK R F' pc' fc' m0' HQ _ cm Hx E8 Hsame).
Qed.

End R.

Section S.
Context {fx : FPState} {rc : RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AllocAPI B.
Context {LS : lib_shape} {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Hypothesis FF : frame_facts_cf B APIf LS SH SK ra empty.
Let API := APIf rc.

(* ---- The conjuncts of frame_facts_cf (FrameAPI.v), by name, in its own order ---- *)
Ltac ff_destruct :=
  destruct FF as (F01 & F02 & F03 & F04 & F05 & F06 & F07 & F08 & F09 & F10 & F11 & F12 & F13 & F14 & F15 & F16 &
                  F17 & F18 & F19 & F20 & F21 & F22 & F23 & F24 & F25 & F26 & F27 & F28 & F29 & F30 & F31 & F32 &
                  F33).

Lemma ff_segs : ms_segs B = rsegs.
Proof. ff_destruct. exact F01. Qed.

Lemma ff_ra : ra mod 2 = 0.
Proof. ff_destruct. exact F02. Qed.

Lemma ff_malloc : ms_malloc B = 0x16a7c.
Proof. ff_destruct. exact F03. Qed.

Lemma ff_free : ms_free B = 0x1693c.
Proof. ff_destruct. exact F04. Qed.

Lemma ff_realloc : ms_realloc B = None.
Proof. ff_destruct. exact F05. Qed.

Lemma ff_calloc : ms_calloc B = None.
Proof. ff_destruct. exact F06. Qed.

Lemma ff_errno_ceil : errno_addr B + 4 <= alloc_ceiling.
Proof. ff_destruct. exact (F07 rc). Qed.

Lemma ff_guard : ms_guard B = 0x50460.
Proof. ff_destruct. exact F08. Qed.

Lemma ff_got_guard : ms_got_guard B = 0x1ee78.
Proof. ff_destruct. exact F09. Qed.

Lemma ff_ctx : ms_ctx B = 0x504f8.
Proof. ff_destruct. exact F10. Qed.

Lemma ff_lock : ms_lock B = 0x504f0.
Proof. ff_destruct. exact F11. Qed.

Lemma ff_libc : ms_libc B = 0x50480.
Proof. ff_destruct. exact F12. Qed.

Lemma ff_size_classes : ms_size_classes B = 0x106d8.
Proof. ff_destruct. exact F13. Qed.

Lemma ff_small_cnt : ms_small_cnt B = 0x10738.
Proof. ff_destruct. exact F14. Qed.

Lemma ff_med_cnt : ms_med_cnt B = 0x10753.
Proof. ff_destruct. exact F15. Qed.

Lemma ff_debruijn : ms_debruijn B = 0x106b8.
Proof. ff_destruct. exact F16. Qed.

Lemma ff_tp : ms_tp B = 0x301f0.
Proof. ff_destruct. exact F17. Qed.

Lemma ff_errno_off : ms_errno_off B = -164.
Proof. ff_destruct. exact F18. Qed.

Lemma ff_replaced : ms_replaced B = None.
Proof. ff_destruct. exact F19. Qed.

Lemma ff_vmlock : ms_vmlock B = None.
Proof. ff_destruct. exact F20. Qed.

Lemma ff_debruijn_len : ms_debruijn_len B = 32.
Proof. ff_destruct. exact F21. Qed.

Lemma ff_sink : @sk_ofl_head SH = 0x508b0 /\ @sk_ofl_lock SK = 0x508a8 /\ @sk_threaded SK = 0x50480 + 1.
Proof. ff_destruct. exact (conj F22 (conj F23 F24)). Qed.

Lemma ff_empty_val : empty = 0x30100.
Proof. ff_destruct. exact F25. Qed.

Lemma ff_empty : 0 < empty < 2 ^ 62.
Proof. ff_destruct. exact F26. Qed.

Lemma ff_ctx_rw : forall a, ms_ctx B <= a < ms_ctx B + CTX_SIZE -> Mem.ro_addr (ms_segs B) (Z_to_bv 64 a) = false.
Proof. ff_destruct. exact F27. Qed.

Lemma ff_G : forall a, in_globals frame_G a -> in_img B a /\ ~ static_owned B a /\
  ~ (ms_ctx B <= a < ms_ctx B + CTX_SIZE) /\ ~ (errno_addr B <= a < errno_addr B + 4).
Proof. ff_destruct. exact F28. Qed.

Lemma ff_relro : forall a, in_globals frame_RELRO a -> in_img B a /\ ~ static_owned B a /\
  ~ (ms_ctx B <= a < ms_ctx B + CTX_SIZE) /\ ~ (errno_addr B <= a < errno_addr B + 4).
Proof. ff_destruct. exact F29. Qed.

Lemma ff_libk : forall pl fs K, @LIBK LS pl fs K = K (LL 0 fs []).
Proof. ff_destruct. exact F30. Qed.

Lemma ff_delta : forall n b, @lib_delta LS n b = b.
Proof. ff_destruct. exact F31. Qed.

Lemma ff_lib_room : forall b n, @lib_room LS b n -> sb_live b <= 64 /\ 0 <= sb_bytes b <= 2 ^ 28 /\
  128 <= sb_cap b <= CAP_AG.
Proof. ff_destruct. exact F32. Qed.

(* lib_room's agreement bound is the slot's (SlotInvCF.slot_room). *)
Lemma ff_room : forall b n, @lib_room LS b n -> slot_room b.
Proof.
  intros b n H. destruct (ff_lib_room b n H) as (H1 & H2 & H3). unfold slot_room.
  lia.
Qed.

Lemma ff_alloc : frame_allocator_cf B API.
Proof. ff_destruct. exact (F33 rc fx). Qed.

(* ---- The slot helpers ---- *)
Lemma sl_segs : ms_segs B = rsegs.
Proof. exact ff_segs. Qed.

Lemma sl_errno : errno_addr B + 4 <= alloc_ceiling.
Proof. exact ff_errno_ceil. Qed.

Lemma sl_sink : @sk_ofl_head SH = 0x508b0 /\ @sk_ofl_lock SK = 0x508a8 /\ @sk_threaded SK = 0x50480 + 1.
Proof. exact ff_sink. Qed.

Lemma sl_errno_val : errno_addr B = 0x301f0 - 164.
Proof. unfold errno_addr. rewrite ff_tp, ff_errno_off. reflexivity. Qed.

Lemma sl_ceil : SL_TOP < alloc_ceiling.
Proof. pose proof alloc_ceiling_value. unfold SL_TOP. lia. Qed.

Lemma sl_sink_keep : forall (m m' : word -> option byte) md,
  (forall a, 0 <= a < SL_TOP -> m' (Z_to_bv 64 a) = m (Z_to_bv 64 a)) ->
  sink_none B m md -> sink_none B m' md.
Proof.
  intros m m' md HK (Henv & Hhead & Hn). destruct sl_sink as (E1 & E2 & E3).
  assert (HM : forall a, 0 <= a < SL_TOP -> mbyte (ms_segs B) m' a = mbyte (ms_segs B) m a).
  { intros a Ha. unfold mbyte. rewrite (HK a Ha). reflexivity. }
  destruct Henv as [Ht Hl]. split; [split|split; [|exact Hn]].
  - eapply val_mem_frame; [|exact Ht]. intros x Hx. apply HM. rewrite E3 in Hx. cbn in Hx. unfold SL_TOP. lia.
  - eapply val_mem_frame; [|exact Hl]. intros x Hx. apply HM. rewrite E2 in Hx. cbn in Hx. unfold SL_TOP. lia.
  - apply (val_mem_word_mem (ms_segs B)). apply (val_mem_word_mem (ms_segs B)) in Hhead.
    eapply val_mem_frame; [|exact Hhead]. intros x Hx. apply HM. rewrite E1 in Hx. cbn in Hx. unfold SL_TOP. lia.
Qed.

Lemma sl_present_of_writable : forall m a, SL_TOP <= a < 2 ^ 64 ->
  writable_at rsegs m a -> exists b, m (Z_to_bv 64 a) = Some b.
Proof.
  intros m a Ha W. unfold writable_at in W. rewrite (sl_wview_hi m a Ha) in W.
  destruct (m (Z_to_bv 64 a)) as [b|]; [exists b; reflexivity | contradiction].
Qed.

Lemma sl_stk_of_writable : forall m lo hi, SL_TOP <= lo -> hi <= 2 ^ 64 ->
  (forall a, lo <= a < hi -> writable_at rsegs m a) -> Frame.stk rsegs m lo hi.
Proof.
  intros m lo hi Hlo Hhi H. split; [unfold SL_TOP in Hlo; lia|]. split; [lia|]. intros a Ha.
  pose proof (H a Ha) as W. unfold writable_at in W. rewrite (sl_wview_hi m a ltac:(lia)) in W.
  unfold Mem.wa. split.
  - rewrite (sl_wview_hi m a ltac:(lia)). exact W.
  - unfold Mem.mrd. destruct (m (Z_to_bv 64 a)) as [b|]; [exists b; reflexivity | contradiction].
Qed.

Lemma sl_ro_false : forall a, SL_TOP <= a < 2 ^ 64 -> Mem.ro_addr rsegs (Z_to_bv 64 a) = false.
Proof.
  intros a Ha. unfold Mem.ro_addr. rewrite (MState.unsigned_lit a ltac:(unfold SL_TOP in Ha; lia)).
  destruct (find_segment rsegs a 1) as [seg|] eqn:E; [|reflexivity].
  exfalso. pose proof (sl_find_top a 1 seg E). unfold SL_TOP in *. lia.
Qed.

Lemma sl_stk_norm : forall m lo hi, ro_agree rsegs m -> SL_TOP <= lo -> hi <= 2 ^ 64 ->
  (forall a, lo <= a < hi -> writable_at rsegs m a) -> Frame.stk rsegs (normalize rsegs m) lo hi.
Proof.
  intros m lo hi Hro Hlo Hhi H. apply sl_stk_of_writable; [exact Hlo | exact Hhi |].
  intros a Ha. unfold writable_at.
  rewrite (wview_rel_rw rsegs m (normalize rsegs m) _ (mem_rel_normalize rsegs m Hro) (sl_ro_false a ltac:(lia))).
  exact (H a Ha).
Qed.

Lemma sl_fr_of : forall g hb L A mem0 md regs' mem',
  GV B empty g ->
  aa_MR API L A mem0 md -> WF A -> bounded A -> st_init_done A = true ->
  (exists vm, md = with_vmmaps vm (g_md g)) ->
  (forall a, alloc_ceiling <= a < 2 ^ 64 -> ~ (g_S g - SLOT_K <= a < g_S g) ->
     ~ (errno_addr B <= a < errno_addr B + 4) ->
     mbyte (ms_segs B) mem0 a = mbyte (ms_segs B) (g_mem g) a /\
     (writable_at (ms_segs B) (g_mem g) a <-> writable_at (ms_segs B) mem0 a)) ->
  (forall a, in_img B a -> ~ static_owned B a -> ~ (ms_ctx B <= a < ms_ctx B + CTX_SIZE) ->
     ~ (errno_addr B <= a < errno_addr B + 4) ->
     mbyte (ms_segs B) mem0 a = mbyte (ms_segs B) (g_mem g) a /\
     (writable_at (ms_segs B) (g_mem g) a <-> writable_at (ms_segs B) mem0 a)) ->
  (forall a k i, In (a, k) (blocks (g_L g) (g_A g)) -> 0 <= i < k ->
     mbyte (ms_segs B) mem0 (a + i) = mbyte (ms_segs B) (g_mem g) (a + i)) ->
  (forall a k, In (a, k) (blocks (g_L g) (g_A g)) -> In (a, k) (blocks L A)) ->
  (forall a, errno_addr B <= a < errno_addr B + 4 -> writable_at (ms_segs B) mem0 a) ->
  sink_none B mem0 md -> RESB (g_b g) hb A ->
  (forall a, g_S g - SLOT_K <= a < g_S g -> writable_at (ms_segs B) mem0 a) ->
  relro B mem0 ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (g_S g - SLOT_K <= a < g_S g) -> mem' (Z_to_bv 64 a) = mem0 (Z_to_bv 64 a)) ->
  Frame.wmono rsegs mem0 mem' -> ro_agree rsegs mem' ->
  getr regs' 2 = Z_to_bv 64 (fsp g) -> getr regs' 3 = getr (g_regs g) 3 -> getr regs' 4 = getr (g_regs g) 4 ->
  bytes_at rsegs mem' (g_S g - SLOT_SAVE) (saved_bytes ra g) ->
  FR B APIf ra empty g hb L A regs' mem' md.
Proof.
  intros g hb L A mem0 md regs' mem' HGV HM HW HB HID Hmd Hhigh Himg Hblk HBL Herr Hsn Hres Hwin Hrel
    HU WM MI' E2 E3 E4 Hsv.
  pose proof sl_segs as SEGS. pose proof sl_ceil as Hc. pose proof sl_errno as Her.
  pose proof alloc_ceiling_value as Hac.
  pose proof HGV as (_ & _ & _ & HS16 & HSK & HS47 & _).
  unfold SLOT_K, SLOT_STACK in *.
  assert (HL : forall a, 0 <= a < SL_TOP -> mem' (Z_to_bv 64 a) = mem0 (Z_to_bv 64 a)).
  { intros a Ha. apply HU; lia. }
  assert (HL' : forall a, 0 <= a < alloc_ceiling -> mem' (Z_to_bv 64 a) = mem0 (Z_to_bv 64 a)).
  { intros a Ha. apply HU; lia. }
  assert (Hwr : forall a, writable_at (ms_segs B) mem0 a -> writable_at (ms_segs B) mem' a).
  { intros a W. unfold writable_at in *. rewrite SEGS in *. apply WM. exact W. }
  split; [exact HGV|]. split; [exact E2|]. split; [exact E3|]. split; [exact E4|]. split; [exact Hsv|].
  split.
  { apply sl_stk_of_writable; [unfold SL_TOP, SLOT_K, SLOT_STACK; lia | lia |].
    intros a Ha. rewrite <- SEGS. apply Hwr, Hwin. exact Ha. }
  split; [unfold MI; rewrite SEGS; exact MI'|].
  split.
  { unfold relro, G_img_c in *. intros a Ha. rewrite <- (Hrel a Ha).
    destruct Ha as (lo & len & Hin & Hr). unfold frame_RELRO in Hin. cbn in Hin.
    destruct Hin as [E|[E|[]]]; injection E as <- <-;
      unfold mbyte; rewrite (HL' a ltac:(lia)); reflexivity. }
  split.
  { destruct (mr_model B _ (aa_laws API) _ _ _ _ HM) as (Hh & Hl & Hmat).
    eapply (mr_frame B (aa_MR API) (aa_laws API)); [exact HM | | | | reflexivity | exact Hh | exact Hl | exact Hmat].
    - intros a Ho. pose proof (mr_owned_low B (aa_MR API) (aa_laws API) _ _ _ _ a HM Ho) as Ha.
      unfold mbyte. rewrite (HL' a Ha). reflexivity.
    - intros a Ho [bb Hb]. pose proof (mr_owned_low B (aa_MR API) (aa_laws API) _ _ _ _ a HM Ho) as Ha.
      exists bb. rewrite (HL' a Ha). exact Hb.
    - intros p n i Hin Hi.
      destruct (mr_blocks B (aa_MR API) (aa_laws API) L A mem0 md p n i HM Hin Hi) as ([bb Hpr] & H1 & H2 & _).
      exists bb. rewrite (HL' (ptr_addr L p + i) ltac:(lia)). exact Hpr. }
  split; [exact HW|]. split; [exact HB|]. split; [exact HID|]. split; [exact Hmd|].
  split.
  { intros a Ha Hns Hne. destruct (Hhigh a Ha Hns Hne) as [F1 F2].
    rewrite SEGS in *. destruct (sl_eq_at mem0 mem' a (HU a ltac:(lia) Hns)) as [G1 G2].
    split; [rewrite G1; exact F1 | rewrite F2; exact G2]. }
  split.
  { intros a H1 H2 H3 H4. pose proof (sl_in_img_top B a SEGS H1) as Ht. destruct (Himg a H1 H2 H3 H4) as [F1 F2].
    rewrite SEGS in *. destruct (sl_eq_at mem0 mem' a (HL a Ht)) as [G1 G2].
    split; [rewrite G1; exact F1 | rewrite F2; exact G2]. }
  split.
  { intros a k i Hin Hi. rewrite <- (Hblk a k i Hin Hi).
    pose proof (HBL a k Hin) as Hin2. apply blocks_In in Hin2 as (p & Hp & Hpin).
    destruct (mr_blocks B (aa_MR API) (aa_laws API) L A mem0 md p k i HM Hpin Hi) as (_ & H1 & H2 & _).
    unfold mbyte. rewrite (HL' (a + i) ltac:(subst a; lia)). reflexivity. }
  split.
  { intros a Ha. pose proof sl_errno_val as Ev.
    destruct (sl_eq_at mem0 mem' a (HL' a ltac:(lia))) as [_ G2].
    rewrite SEGS. apply G2. rewrite <- SEGS. exact (Herr a Ha). }
  split; [exact (sl_sink_keep mem0 mem' md HL Hsn)|].
  split; [exact Hres|].
  intros a Ha. apply Hwr, Hwin. exact Ha.
Qed.

Lemma sl_fr_run : forall g hb L A regs mem md regs' mem' W,
  FR B APIf ra empty g hb L A regs mem md ->
  Permutation (blocks L A) (hb ++ blocks (g_L g) (g_A g)) ->
  Frame.munch W mem mem' -> Frame.wmono rsegs mem mem' -> ro_agree rsegs mem' ->
  (forall x, 0 <= x < 2 ^ 64 -> ~ Frame.outside W x -> g_S g - SLOT_K <= x < g_S g - 104) ->
  getr regs' 2 = getr regs 2 -> getr regs' 3 = getr regs 3 -> getr regs' 4 = getr regs 4 ->
  FR B APIf ra empty g hb L A regs' mem' md.
Proof.
  intros g hb L A regs mem md regs' mem' W HFR HP MU WM MI' HW E2 E3 E4.
  destruct HFR as (HGV & F2 & F3 & F4 & Hsv & Hstk & HMI & Hrel & HM & HWf & HB & HID & Hmd & Hhigh & Himg &
                   Hblk & Herr & Hsn & Hres & Hwin).
  pose proof HGV as (_ & _ & _ & HS16 & HSK & HS47 & _).
  pose proof alloc_ceiling_value as Hac.
  pose proof (sl_unch W mem mem' (g_S g - SLOT_K) (g_S g - 104) MU HW) as HU.
  unfold SLOT_K, SLOT_STACK in *.
  apply (sl_fr_of g hb L A mem md regs' mem'); try assumption; unfold SLOT_K, SLOT_STACK in *.
  - intros a k Hin. apply (Permutation_in _ (Permutation_sym HP)). apply in_or_app. right. exact Hin.
  - intros a Ha Hn. apply HU; [exact Ha | lia].
  - rewrite E2. exact F2.
  - rewrite E3. exact F3.
  - rewrite E4. exact F4.
  - apply (sl_bytes_keep mem mem' _ _ Hsv). intros i Hi. rewrite sl_saved_len in Hi.
    unfold SLOT_SAVE. apply HU; lia.
Qed.

Lemma sl_fr_stk : forall g hb L A regs mem md,
  FR B APIf ra empty g hb L A regs mem md ->
  Frame.stk rsegs (normalize rsegs mem) (g_S g - SLOT_K) (g_S g).
Proof.
  intros g hb L A regs mem md HFR.
  destruct HFR as (HGV & _ & _ & _ & _ & _ & HMI & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hwin).
  pose proof HGV as (_ & _ & _ & HS16 & HSK & HS47 & _).
  pose proof alloc_ceiling_value as Hac. pose proof sl_segs as SEGS.
  unfold MI in HMI. rewrite SEGS in HMI.
  apply sl_stk_norm; [exact HMI | unfold SL_TOP, SLOT_K, SLOT_STACK in *; lia | lia |].
  intros a Ha. rewrite <- SEGS. exact (Hwin a Ha).
Qed.

Lemma sl_fr_bnd : forall g hb L A regs mem md,
  FR B APIf ra empty g hb L A regs mem md ->
  getr regs 2 = Z_to_bv 64 (fsp g) /\ fsp g mod 16 = 0 /\ SL_TOP + SLOT_K <= g_S g /\ g_S g <= 2 ^ 47 /\
  ro_agree rsegs mem.
Proof.
  intros g hb L A regs mem md HFR.
  destruct HFR as (HGV & F2 & _ & _ & _ & _ & HMI & _).
  pose proof HGV as (_ & _ & _ & HS16 & HSK & HS47 & _).
  pose proof alloc_ceiling_value as Hac. pose proof sl_segs as SEGS.
  unfold MI in HMI. rewrite SEGS in HMI.
  unfold fsp, SLOT_FRAME, SL_TOP in *. repeat split; try assumption; try lia.
Qed.

Lemma sl_mid : forall g hb L A regs mem md pc (Q : machine_state -> Prop) (P : config -> Prop),
  FR B APIf ra empty g hb L A regs mem md ->
  Permutation (blocks L A) (hb ++ blocks (g_L g) (g_A g)) ->
  Exec.evt rsegs Q (MState.MS (Regs6ss.mkR_of regs) fp_regs pc fp_csr None (normalize rsegs mem) (seg_rom rsegs)) ->
  (forall ms, Q ms -> exists R pc' m', ms = MState.MS R fp_regs pc' fp_csr None m' (seg_rom rsegs) /\
     (exists W, Frame.munch W (normalize rsegs mem) m' /\ Frame.wmono rsegs (normalize rsegs mem) m' /\
        (forall x, 0 <= x < 2 ^ 64 -> ~ Frame.outside W x -> g_S g - SLOT_K <= x < g_S g - 104)) /\
     getr R 2 = getr regs 2 /\ getr R 3 = getr regs 3 /\ getr R 4 = getr regs 4) ->
  (forall R pc' m0' regs' m', Q (MState.MS R fp_regs pc' fp_csr None m0' (seg_rom rsegs)) ->
     Regs6ss.xregs_eqv R regs' -> mem_rel rsegs m' m0' ->
     FR B APIf ra empty g hb L A regs' m' md ->
     SR (ms_segs B) (mkCfg (mkst regs' pc' m' (seg_rom (ms_segs B))) md) P) ->
  SR (ms_segs B) (mkCfg (mkst regs pc mem (seg_rom (ms_segs B))) md) P.
Proof.
  intros g hb L A regs mem md pc Q P HFR HP HE Hform HK.
  pose proof sl_segs as SEGS.
  pose proof HFR as (_ & _ & _ & _ & _ & _ & HMI & _ & HM & _).
  unfold MI in HMI. rewrite SEGS in HMI.
  destruct (mr_model B _ (aa_laws API) _ _ _ _ HM) as (Hh & Hl & _).
  rewrite SEGS.
  apply (sl_run regs pc mem md Q P Hh Hl HMI HE).
  - intros ms HQ. destruct (Hform ms HQ) as (R & pc' & m' & -> & _). exists R, pc', m'. reflexivity.
  - intros R pc' m0' HQ regs' m' Hx Hrel Hsame.
    destruct (Hform _ HQ) as (R1 & pc1 & m1 & E & (W & MU & WM & HW) & E2 & E3 & E4).
    injection E; intros; subst.
    pose proof (mem_rel_normalize rsegs mem HMI) as HR0.
    rewrite <- SEGS. apply (HK R1 pc1 m1 regs' m' HQ Hx Hrel).
    apply (sl_fr_run g hb L A regs mem md regs' m' W HFR HP).
    + exact (munch_rel rsegs W mem (normalize rsegs mem) m' m1 HR0 Hrel Hsame MU).
    + exact (wmono_rel rsegs mem (normalize rsegs mem) m' m1 HR0 Hrel Hsame WM).
    + exact (ro_agree_same rsegs mem m' HMI Hsame).
    + exact HW.
    + rewrite (sl_getr_eqv _ _ _ Hx). exact E2.
    + rewrite (sl_getr_eqv _ _ _ Hx). exact E3.
    + rewrite (sl_getr_eqv _ _ _ Hx). exact E4.
Qed.

(* sl_mid for a run that ends with its own FP registers F' and fcsr fc', rounding mode 0 kept (frm_zero fc'):
   the continuation runs at the FP state mkFP F' fc'. *)
Lemma sl_mid_fp : forall g hb L A regs mem md pc (Q : machine_state -> Prop) (P : config -> Prop),
  FR B APIf ra empty g hb L A regs mem md ->
  Permutation (blocks L A) (hb ++ blocks (g_L g) (g_A g)) ->
  Exec.evt rsegs Q (MState.MS (Regs6ss.mkR_of regs) fp_regs pc fp_csr None (normalize rsegs mem) (seg_rom rsegs)) ->
  (forall ms, Q ms -> exists R F' pc' fc' m', ms = MState.MS R F' pc' fc' None m' (seg_rom rsegs) /\
     frm_zero fc' /\
     (exists W, Frame.munch W (normalize rsegs mem) m' /\ Frame.wmono rsegs (normalize rsegs mem) m' /\
        (forall x, 0 <= x < 2 ^ 64 -> ~ Frame.outside W x -> g_S g - SLOT_K <= x < g_S g - 104)) /\
     getr R 2 = getr regs 2 /\ getr R 3 = getr regs 3 /\ getr R 4 = getr regs 4) ->
  (forall R F' pc' fc' m0' regs' m', Q (MState.MS R F' pc' fc' None m0' (seg_rom rsegs)) ->
     Regs6ss.xregs_eqv R regs' -> mem_rel rsegs m' m0' -> frm_zero fc' ->
     FR B APIf ra empty g hb L A regs' m' md ->
     SR (ms_segs B) (mkCfg (@mkst (mkFP F' fc') regs' pc' m' (seg_rom (ms_segs B))) md) P) ->
  SR (ms_segs B) (mkCfg (mkst regs pc mem (seg_rom (ms_segs B))) md) P.
Proof.
  intros g hb L A regs mem md pc Q P HFR HP HE Hform HK.
  pose proof sl_segs as SEGS.
  pose proof HFR as (_ & _ & _ & _ & _ & _ & HMI & _ & HM & _).
  unfold MI in HMI. rewrite SEGS in HMI.
  destruct (mr_model B _ (aa_laws API) _ _ _ _ HM) as (Hh & Hl & _).
  rewrite SEGS.
  apply (sl_run_fp regs pc mem md Q P Hh Hl HMI HE).
  - intros ms HQ. destruct (Hform ms HQ) as (R & F' & pc' & fc' & m' & -> & _). exists R, F', pc', fc', m'.
    reflexivity.
  - intros R F' pc' fc' m0' HQ regs' m' Hx Hrel Hsame.
    destruct (Hform _ HQ) as (R1 & F1 & pc1 & fc1 & m1 & E & Hfrm & (W & MU & WM & HW) & E2 & E3 & E4).
    injection E; intros; subst.
    pose proof (mem_rel_normalize rsegs mem HMI) as HR0.
    rewrite <- SEGS. apply (HK R1 F1 pc1 fc1 m1 regs' m' HQ Hx Hrel Hfrm).
    apply (sl_fr_run g hb L A regs mem md regs' m' W HFR HP).
    + exact (munch_rel rsegs W mem (normalize rsegs mem) m' m1 HR0 Hrel Hsame MU).
    + exact (wmono_rel rsegs mem (normalize rsegs mem) m' m1 HR0 Hrel Hsame WM).
    + exact (ro_agree_same rsegs mem m' HMI Hsame).
    + exact HW.
    + rewrite (sl_getr_eqv _ _ _ Hx). exact E2.
    + rewrite (sl_getr_eqv _ _ _ Hx). exact E3.
    + rewrite (sl_getr_eqv _ _ _ Hx). exact E4.
Qed.

(* The composition of a segment whose run changes the FP registers and fflags (rounding mode 0 kept): from FR at a
   cut state, a run to pc' that writes only the stack window and leaves P' closes the cut at pc' at the run's own
   FP state (CUTST takes the FP state of its configuration), so H(cut at pc') runs the start state to Post. *)
Lemma sl_seg_fp : forall g hb L A regs mem md pc pc' (P' : bvmap 5 word -> (word -> option byte) -> Prop)
    (Q : machine_state -> Prop),
  FR B APIf ra empty g hb L A regs mem md ->
  Permutation (blocks L A) (hb ++ blocks (g_L g) (g_A g)) ->
  Exec.evt rsegs Q (MState.MS (Regs6ss.mkR_of regs) fp_regs pc fp_csr None (normalize rsegs mem) (seg_rom rsegs)) ->
  (forall ms, Q ms -> exists R F' fc' m', ms = MState.MS R F' (Z_to_bv 64 pc') fc' None m' (seg_rom rsegs) /\
     frm_zero fc' /\
     (exists W, Frame.munch W (normalize rsegs mem) m' /\ Frame.wmono rsegs (normalize rsegs mem) m' /\
        (forall x, 0 <= x < 2 ^ 64 -> ~ Frame.outside W x -> g_S g - SLOT_K <= x < g_S g - 104)) /\
     getr R 2 = getr regs 2 /\ getr R 3 = getr regs 3 /\ getr R 4 = getr regs 4 /\
     (forall regs' m, Regs6ss.xregs_eqv R regs' -> mem_rel rsegs m m' -> P' regs' m)) ->
  (forall c, CUTST B APIf ra empty g pc' hb P' c -> SR (ms_segs B) c (Post B APIf ra g)) ->
  SR (ms_segs B) (mkCfg (mkst regs pc mem (seg_rom (ms_segs B))) md) (Post B APIf ra g).
Proof.
  intros g hb L A regs mem md pc pc' P' Q HFR HP HE Hform HK.
  apply (sl_mid_fp g hb L A regs mem md pc Q _ HFR HP HE).
  - intros ms HQ. destruct (Hform ms HQ) as (R & F' & fc' & m' & -> & Hz & HW & E2 & E3 & E4 & _).
    exists R, F', (Z_to_bv 64 pc'), fc', m'. split; [reflexivity|]. split; [exact Hz|].
    split; [exact HW|]. split; [exact E2|]. split; [exact E3 | exact E4].
  - intros R F' pc1 fc' m0' regs' m' HQ Hx Hrel Hz HFR'.
    destruct (Hform _ HQ) as (R1 & F1 & fc1 & m1 & E & _ & _ & _ & _ & _ & HP').
    injection E; intros; subst.
    apply HK. exists (mkFP F1 fc1), L, A, regs', m', md.
    split; [reflexivity|]. split; [exact Hz|]. split; [exact HFR'|]. split; [exact HP|].
    exact (HP' regs' m' Hx Hrel).
Qed.

(* Post -> the return premise of the frame's lib_contract_body: Post's FP state, with rounding mode 0, is the fx'
   the frame takes (fuzz_pin's PinSlot.slot_post_g, with Post's own FP state in place of the entry's). *)
Lemma sl_post_g : forall g c', Post B APIf ra g c' -> Fs.fs_sorted (m_fs (g_md g)) = true ->
  exists (fx' : FPState) L' A' regs' mem' md',
    c' = mkCfg (@YK11.mkst fx' regs' (Z_to_bv 64 ra) mem' (YK11.seg_rom (ms_segs B))) md' /\
    frm_zero (@fp_csr fx') /\
    lib_post_g B API [] SLOT_STACK (g_L g) (g_A g) (g_regs g) (g_mem g) (g_md g) (g_p g) (g_n g) (g_b g)
      (LL 0 (m_fs (g_md g)) []) L' A' regs' mem' md'.
Proof.
  intros g c' (fx' & L' & A' & regs' & mem' & md' & -> & Hfrm & HLP & HSN & HMI & HRE & HPAY) Hsorted.
  exists fx', L', A', regs', mem', md'. split; [reflexivity|]. split; [exact Hfrm|].
  destruct HLP as (H1 & H2 & H3 & H4 & H5 & H6 & (vm' & Hmd) & H8 & H9 & H10 & H11 & H12).
  unfold lib_post_g. cbn [ll_ret ll_out ll_fs].
  split; [exact H1|]. split; [exact H2|]. split; [exact H3|]. split; [exact H4|]. split; [exact H5|].
  split; [exact H6|].
  split; [exists vm', (m_fds (g_md g)), (m_statpins (g_md g)); split; [rewrite Hmd; apply with_vmmaps_os_upd |
          intros k; reflexivity]|].
  split; [exact H8|]. split; [exact H9|]. split; [exact H10|].
  split; [intros a (lo & len & [] & _)|].
  split; [exact H11|]. split; [exact H12|].
  split; [reflexivity|]. split; [reflexivity|]. split; [exact Hsorted|].
  split; [exact HSN|]. split; [exact HMI|].
  split; [rewrite ff_delta; exact HRE|].
  exact HPAY.
Qed.

End S.
