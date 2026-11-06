From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Lib Require Import Mem Frame.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Lib Require MState Regs6ss RegisterBridge Exec Cells Step.
From OSSVerify.Proofs.libreac.fuzz_identity.lib Require Import Img0 Contract FrameAPI.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog Require Import IdentSpec SlotModel SlotInv.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog Require Import URzP.
Import ListNotations.
Open Scope Z_scope.

Definition SA_TOP : Z := 0x51000.

Lemma sa_find_segment_in : forall segs a n seg, find_segment segs a n = Some seg ->
  In seg segs /\ Z.of_N (seg_base seg) <= a /\ a + n <= Z.of_N (seg_base seg) + Z.of_N (seg_size seg).
Proof.
  induction segs as [|s segs IH]; intros a n seg E; cbn in E; [discriminate|].
  match type of E with context [if ?c then _ else _] => destruct c eqn:C end.
  - injection E as <-. apply andb_true_iff in C as [C1 C2]. apply Z.leb_le in C1. apply Z.leb_le in C2.
    split; [left; reflexivity | lia].
  - destruct (IH a n seg E) as (H1 & H2 & H3). split; [right; exact H1 | lia].
Qed.

Lemma sa_rsegs_ok : forallb (fun s => let r := segment_reservation s in
    (bv_unsigned (fst r) <=? Z.of_N (seg_base s)) &&
    (Z.of_N (seg_base s) + Z.of_N (seg_size s) <=? bv_unsigned (fst r) + bv_unsigned (snd r)) &&
    (bv_unsigned (fst r) + bv_unsigned (snd r) <=? SA_TOP)) rsegs = true.
Proof. vm_compute. reflexivity. Qed.

Lemma sa_rsegs_seg : forall seg, In seg rsegs ->
  bv_unsigned (fst (segment_reservation seg)) <= Z.of_N (seg_base seg) /\
  Z.of_N (seg_base seg) + Z.of_N (seg_size seg) <=
    bv_unsigned (fst (segment_reservation seg)) + bv_unsigned (snd (segment_reservation seg)) /\
  bv_unsigned (fst (segment_reservation seg)) + bv_unsigned (snd (segment_reservation seg)) <= SA_TOP.
Proof.
  intros seg Hin. pose proof (proj1 (forallb_forall _ _) sa_rsegs_ok seg Hin) as H. cbv beta zeta in H.
  apply andb_true_iff in H as [H H3]. apply andb_true_iff in H as [H1 H2].
  apply Z.leb_le in H1. apply Z.leb_le in H2. apply Z.leb_le in H3. auto.
Qed.

Lemma sa_find_top : forall a n seg, find_segment rsegs a n = Some seg -> a + n <= SA_TOP.
Proof.
  intros a n seg E. destruct (sa_find_segment_in rsegs a n seg E) as (Hin & H1 & H2).
  destruct (sa_rsegs_seg seg Hin) as (R1 & R2 & R3). lia.
Qed.

Lemma sa_in_img_top : forall B a, ms_segs B = rsegs -> in_img B a -> 0 <= a < SA_TOP.
Proof.
  intros B a HS [_ (s & Hin & Hr)]. rewrite HS in Hin. unfold segments_reserved in Hin.
  apply in_map_iff in Hin as (seg & <- & Hseg).
  destruct (sa_rsegs_seg seg Hseg) as (R1 & R2 & R3).
  pose proof (bv_unsigned_in_range _ (fst (segment_reservation seg))) as R. lia.
Qed.

Lemma sa_wview_hi : forall m a, SA_TOP <= a < 2 ^ 64 -> wview rsegs m (Z_to_bv 64 a) = m (Z_to_bv 64 a).
Proof.
  intros m a Ha. unfold wview. destruct (m (Z_to_bv 64 a)) as [b|]; [reflexivity|].
  rewrite (MState.unsigned_lit a ltac:(unfold SA_TOP in Ha; lia)).
  destruct (find_segment rsegs a 1) as [seg|] eqn:E; [|reflexivity].
  exfalso. pose proof (sa_find_top a 1 seg E). unfold SA_TOP in *. lia.
Qed.

Lemma sa_outside_dec : forall W x, {Frame.outside W x} + {~ Frame.outside W x}.
Proof.
  induction W as [|[lo hi] W IH]; intros x; cbn [Frame.outside]; [left; exact I|].
  destruct (Z_le_dec lo x) as [H1|H1]; [destruct (Z_lt_dec x hi) as [H2|H2]|].
  - right. intros [H _]. lia.
  - destruct (IH x) as [O|O]; [left; split; [lia | exact O] | right; intros [_ H]; exact (O H)].
  - destruct (IH x) as [O|O]; [left; split; [lia | exact O] | right; intros [_ H]; exact (O H)].
Qed.

Lemma sa_unch : forall W m m' lo hi, Frame.munch W m m' ->
  (forall x, 0 <= x < 2 ^ 64 -> ~ Frame.outside W x -> lo <= x < hi) ->
  forall a, 0 <= a < 2 ^ 64 -> ~ (lo <= a < hi) -> m' (Z_to_bv 64 a) = m (Z_to_bv 64 a).
Proof.
  intros W m m' lo hi MU HW a Ha Hn. apply MU. rewrite (MState.unsigned_lit a Ha).
  destruct (sa_outside_dec W a) as [O|O]; [exact O|]. exfalso. apply Hn. exact (HW a Ha O).
Qed.

Lemma sa_eq_at : forall (m m' : word -> option byte) a, m' (Z_to_bv 64 a) = m (Z_to_bv 64 a) ->
  mbyte rsegs m' a = mbyte rsegs m a /\ (writable_at rsegs m a <-> writable_at rsegs m' a).
Proof.
  intros m m' a E. unfold mbyte, writable_at, wview. rewrite E. split; [reflexivity | tauto].
Qed.

Lemma sa_mkFP : forall f : FPState, mkFP (@fp_regs f) (@fp_csr f) = f.
Proof. intros []. reflexivity. Qed.

Lemma sa_eqv_mkst : forall R F pc fc m ro ms',
  Regs6ss.ms_eqv (MState.MS R F pc fc None m ro) ms' ->
  ms' = @mkst (mkFP F fc) (ms_regs ms') pc m ro /\ Regs6ss.xregs_eqv R (ms_regs ms').
Proof.
  intros R F pc fc m ro ms' (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8).
  destruct ms' as [r f p s v c mm rr]; cbn in *. subst. split; [reflexivity | exact H1].
Qed.

Lemma sa_getr_eqv : forall R R' r, Regs6ss.xregs_eqv R R' -> getr R' r = getr R r.
Proof.
  intros R R' r H. unfold getr. destruct (bv_eqb r 0) eqn:E; [reflexivity|].
  symmetry. apply H. exact E.
Qed.

Lemma sa_mkR_of : forall regs, Regs6ss.mkR_of regs = Frame.mkR (getr regs 1) (getr regs 2) (getr regs 3) (getr regs 4) (getr regs 5) (getr regs 6) (getr regs 7) (getr regs 8) (getr regs 9) (getr regs 10) (getr regs 11) (getr regs 12) (getr regs 13) (getr regs 14) (getr regs 15) (getr regs 16) (getr regs 17) (getr regs 18) (getr regs 19) (getr regs 20) (getr regs 21) (getr regs 22) (getr regs 23) (getr regs 24) (getr regs 25) (getr regs 26) (getr regs 27) (getr regs 28) (getr regs 29) (getr regs 30) (getr regs 31).
Proof. intros regs. reflexivity. Qed.

Lemma sa_bytes_cells_tail : forall m A n j cs,
  Step.rw_cells rsegs m A (Cells.CB n j :: cs) -> bytes_at rsegs m (A + Z.of_nat n) (Cells.cells_bytes cs).
Proof.
  intros m A n j cs [[Hwf Hb] _]. cbn [Cells.cells_bytes Cells.cbytes] in Hb.
  apply (proj1 (bytes_at_app rsegs m A j (Cells.cells_bytes cs))) in Hb as [_ Hb].
  cbn [Cells.cells_wf] in Hwf. destruct Hwf as [Hl _]. rewrite Hl in Hb. exact Hb.
Qed.

Lemma sa_bytes_keep : forall m m' a bs, bytes_at rsegs m a bs ->
  (forall i, 0 <= i < Z.of_nat (length bs) -> m' (Z_to_bv 64 (a + i)) = m (Z_to_bv 64 (a + i))) ->
  bytes_at rsegs m' a bs.
Proof.
  intros m m' a bs (H1 & H2 & H3) HE. split; [exact H1|]. split; [exact H2|].
  intros i Hi. unfold Mem.mrd, Mem.wa. rewrite (HE (Z.of_nat i) ltac:(lia)). exact (H3 i Hi).
Qed.

Lemma sa_rw_of_stk : forall m lo hi a n, Frame.stk rsegs m lo hi -> lo <= a -> a + Z.of_nat n <= hi ->
  exists bs, Step.rw_cells rsegs m a [Cells.CB n bs].
Proof.
  intros m lo hi a n ST H1 H2.
  destruct (stk_split rsegs m lo (a + Z.of_nat n) hi ST ltac:(lia)) as [ST1 _].
  destruct (stk_carve rsegs m lo (a + Z.of_nat n) n ST1 ltac:(lia)) as [_ (junk & HJ)].
  exists junk. replace a with (a + Z.of_nat n - Z.of_nat n) at 1 by lia. exact HJ.
Qed.

Lemma sa_rw_bytes : forall m A n bs, Step.rw_cells rsegs m A [Cells.CB n bs] -> bytes_at rsegs m A bs.
Proof. intros m A n bs [[_ Hb] _]. cbn [Cells.cells_bytes Cells.cbytes] in Hb. rewrite app_nil_r in Hb. exact Hb. Qed.

Lemma sa_cells_bytes : forall m A cs, Step.rw_cells rsegs m A cs -> bytes_at rsegs m A (Cells.cells_bytes cs).
Proof. intros m A cs [[_ Hb] _]. exact Hb. Qed.

Lemma sa_fp : forall g x, 0 <= x < 2 ^ 64 -> ~ Frame.outside [(g_S g - SLOT_K, fsp g + 264)] x ->
  g_S g - SLOT_K <= x < g_S g - 104.
Proof.
  intros g x Hx O. unfold fsp, SLOT_FRAME in *.
  destruct (Z_le_dec (g_S g - SLOT_K) x); destruct (Z_lt_dec x (g_S g - 368 + 264)); try lia;
    exfalso; apply O; cbn [Frame.outside]; (split; [lia | exact I]).
Qed.

Lemma sa_fp1 : forall g lo hi x, g_S g - SLOT_K <= lo -> hi <= g_S g - 104 ->
  0 <= x < 2 ^ 64 -> ~ Frame.outside [(lo, hi)] x -> g_S g - SLOT_K <= x < g_S g - 104.
Proof.
  intros g lo hi x H1 H2 Hx O.
  destruct (Z_le_dec lo x); destruct (Z_lt_dec x hi); try lia;
    exfalso; apply O; cbn [Frame.outside]; (split; [lia | exact I]).
Qed.

Section R.
Context {fx : FPState}.
Context {RzCi : RzC}.

Lemma sa_run : forall regs pc mem md (Q : machine_state -> Prop) (P : config -> Prop),
  m_halted md = None -> m_vm_lazy md = [] -> ro_agree rsegs mem ->
  Exec.evt rsegs Q (MState.MS (Regs6ss.mkR_of regs) fp_regs pc fp_csr None (normalize rsegs mem) (seg_rom rsegs)) ->
  (forall ms, Q ms -> exists R pc' m', ms = MState.MS R fp_regs pc' fp_csr None m' (seg_rom rsegs)) ->
  (forall R pc' m0', Q (MState.MS R fp_regs pc' fp_csr None m0' (seg_rom rsegs)) ->
     forall regs' m', Regs6ss.xregs_eqv R regs' -> mem_rel rsegs m' m0' -> ro_same rsegs mem m' ->
     Rz rsegs (mkCfg (mkst regs' pc' m' (seg_rom rsegs)) md) P) ->
  Rz rsegs (mkCfg (mkst regs pc mem (seg_rom rsegs)) md) P.
Proof.
  intros regs pc mem md Q P Hh Hl Hro HE Hform HK.
  apply (rz_evt_canon rsegs _ (fun s => exists s0, Q s0 /\ ms_rel rsegs s s0 /\ ro_same rsegs mem (ms_mem s)) md P);
    [| exact Hh | exact Hl |].
  - change (RegisterBridge.canonical_register_state (mkst regs pc mem (seg_rom rsegs)))
      with (MState.MS (Regs6ss.mkR_of regs) fp_regs pc fp_csr None mem (seg_rom rsegs)).
    apply evt_normalize; [exact wx_apart_rsegs | exact Hro | exact HE].
  - intros ms' (can & (s0 & HQ & Hrel & Hsame) & Heq).
    destruct (Hform s0 HQ) as (R & pc' & m0' & ->).
    destruct can as [cr cf cp cs cv cc cm co].
    destruct Hrel as (E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8).
    cbn [ms_regs ms_fregs ms_pc_val ms_svc_pending ms_resv ms_fcsr ms_mem ms_rom MState.MS] in *. subst.
    destruct (sa_eqv_mkst R fp_regs pc' fp_csr cm (seg_rom rsegs) ms' Heq) as [Ems Hx].
    rewrite Ems, sa_mkFP.
    exact (HK R pc' m0' HQ _ cm Hx E8 Hsame).
Qed.

End R.

Section S.
Context {fx : FPState} {rc : RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AllocAPI B.
Context {LS : lib_shape} {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Context {RzCi : RzC} {RzAi : RzA B (APIf rc)}.
Hypothesis FF : frame_facts B APIf LS SH SK ra empty.
Let API := APIf rc.

Lemma sa_segs : ms_segs B = rsegs.
Proof. exact (proj1 FF). Qed.

Lemma sa_errno : errno_addr B + 4 <= alloc_ceiling.
Proof.
  destruct FF as (_ & _ & _ & _ & _ & _ & H & _). exact (H rc).
Qed.

Lemma sa_sink : @sk_ofl_head SH = 0x50640 /\ @sk_ofl_lock SK = 0x50638 /\ @sk_threaded SK = 0x50210 + 1.
Proof.
  destruct FF as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & H1 & H2 & H3 & _).
  auto.
Qed.

Lemma sa_errno_val : errno_addr B = 0x2ff80 - 164.
Proof.
  destruct FF as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & H1 & H2 & _).
  unfold errno_addr. rewrite H1, H2. reflexivity.
Qed.

Lemma sa_ceil : SA_TOP < alloc_ceiling.
Proof. pose proof alloc_ceiling_value. unfold SA_TOP. lia. Qed.

Lemma sa_sink_keep : forall (m m' : word -> option byte) md,
  (forall a, 0 <= a < SA_TOP -> m' (Z_to_bv 64 a) = m (Z_to_bv 64 a)) ->
  sink_none B m md -> sink_none B m' md.
Proof.
  intros m m' md HK (Henv & Hhead & Hn). destruct sa_sink as (E1 & E2 & E3).
  assert (HM : forall a, 0 <= a < SA_TOP -> mbyte (ms_segs B) m' a = mbyte (ms_segs B) m a).
  { intros a Ha. unfold mbyte. rewrite (HK a Ha). reflexivity. }
  destruct Henv as [Ht Hl]. split; [split|split; [|exact Hn]].
  - eapply val_mem_frame; [|exact Ht]. intros x Hx. apply HM. rewrite E3 in Hx. cbn in Hx. unfold SA_TOP. lia.
  - eapply val_mem_frame; [|exact Hl]. intros x Hx. apply HM. rewrite E2 in Hx. cbn in Hx. unfold SA_TOP. lia.
  - apply (val_mem_word_mem (ms_segs B)). apply (val_mem_word_mem (ms_segs B)) in Hhead.
    eapply val_mem_frame; [|exact Hhead]. intros x Hx. apply HM. rewrite E1 in Hx. cbn in Hx. unfold SA_TOP. lia.
Qed.

Lemma sa_present_of_writable : forall m a, SA_TOP <= a < 2 ^ 64 ->
  writable_at rsegs m a -> exists b, m (Z_to_bv 64 a) = Some b.
Proof.
  intros m a Ha W. unfold writable_at in W. rewrite (sa_wview_hi m a Ha) in W.
  destruct (m (Z_to_bv 64 a)) as [b|]; [exists b; reflexivity | contradiction].
Qed.

Lemma sa_stk_of_writable : forall m lo hi, SA_TOP <= lo -> hi <= 2 ^ 64 ->
  (forall a, lo <= a < hi -> writable_at rsegs m a) -> Frame.stk rsegs m lo hi.
Proof.
  intros m lo hi Hlo Hhi H. split; [unfold SA_TOP in Hlo; lia|]. split; [lia|]. intros a Ha.
  pose proof (H a Ha) as W. unfold writable_at in W. rewrite (sa_wview_hi m a ltac:(lia)) in W.
  unfold Mem.wa. split.
  - rewrite (sa_wview_hi m a ltac:(lia)). exact W.
  - unfold Mem.mrd. destruct (m (Z_to_bv 64 a)) as [b|]; [exists b; reflexivity | contradiction].
Qed.

Lemma sa_ro_false : forall a, SA_TOP <= a < 2 ^ 64 -> Mem.ro_addr rsegs (Z_to_bv 64 a) = false.
Proof.
  intros a Ha. unfold Mem.ro_addr. rewrite (MState.unsigned_lit a ltac:(unfold SA_TOP in Ha; lia)).
  destruct (find_segment rsegs a 1) as [seg|] eqn:E; [|reflexivity].
  exfalso. pose proof (sa_find_top a 1 seg E). unfold SA_TOP in *. lia.
Qed.

Lemma sa_stk_norm : forall m lo hi, ro_agree rsegs m -> SA_TOP <= lo -> hi <= 2 ^ 64 ->
  (forall a, lo <= a < hi -> writable_at rsegs m a) -> Frame.stk rsegs (normalize rsegs m) lo hi.
Proof.
  intros m lo hi Hro Hlo Hhi H. apply sa_stk_of_writable; [exact Hlo | exact Hhi |].
  intros a Ha. unfold writable_at.
  rewrite (wview_rel_rw rsegs m (normalize rsegs m) _ (mem_rel_normalize rsegs m Hro) (sa_ro_false a ltac:(lia))).
  exact (H a Ha).
Qed.

Lemma sa_fr_of : forall g km hb L A mem0 md regs' mem',
  GV B APIf empty g ->
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
  sink_none B mem0 md -> RESB (g_b g) km hb A ->
  (forall a, g_S g - SLOT_K <= a < g_S g -> writable_at (ms_segs B) mem0 a) ->
  relro B mem0 ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (g_S g - SLOT_K <= a < g_S g) -> mem' (Z_to_bv 64 a) = mem0 (Z_to_bv 64 a)) ->
  Frame.wmono rsegs mem0 mem' -> ro_agree rsegs mem' ->
  getr regs' 2 = Z_to_bv 64 (fsp g) -> getr regs' 3 = getr (g_regs g) 3 -> getr regs' 4 = getr (g_regs g) 4 ->
  bytes_at rsegs mem' (g_S g - 104) (saved_bytes ra g) ->
  FR B APIf ra empty g km hb L A regs' mem' md.
Proof.
  intros g km hb L A mem0 md regs' mem' HGV HM HW HB HID Hmd Hhigh Himg Hblk HBL Herr Hsn Hres Hwin Hrel
    HU WM MI' E2 E3 E4 Hsv.
  pose proof sa_segs as SEGS. pose proof sa_ceil as Hc. pose proof sa_errno as Her.
  pose proof alloc_ceiling_value as Hac.
  pose proof HGV as (_ & _ & _ & HS16 & HSK & HS47 & _).
  unfold SLOT_K, SLOT_STACK in *.
  assert (HL : forall a, 0 <= a < SA_TOP -> mem' (Z_to_bv 64 a) = mem0 (Z_to_bv 64 a)).
  { intros a Ha. apply HU; lia. }
  assert (HL' : forall a, 0 <= a < alloc_ceiling -> mem' (Z_to_bv 64 a) = mem0 (Z_to_bv 64 a)).
  { intros a Ha. apply HU; lia. }
  assert (Hwr : forall a, writable_at (ms_segs B) mem0 a -> writable_at (ms_segs B) mem' a).
  { intros a W. unfold writable_at in *. rewrite SEGS in *. apply WM. exact W. }
  split; [exact HGV|]. split; [exact E2|]. split; [exact E3|]. split; [exact E4|]. split; [exact Hsv|].
  split.
  { apply sa_stk_of_writable; [unfold SA_TOP, SLOT_K, SLOT_STACK; lia | lia |].
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
    rewrite SEGS in *. destruct (sa_eq_at mem0 mem' a (HU a ltac:(lia) Hns)) as [G1 G2].
    split; [rewrite G1; exact F1 | rewrite F2; exact G2]. }
  split.
  { intros a H1 H2 H3 H4. pose proof (sa_in_img_top B a SEGS H1) as Ht. destruct (Himg a H1 H2 H3 H4) as [F1 F2].
    rewrite SEGS in *. destruct (sa_eq_at mem0 mem' a (HL a Ht)) as [G1 G2].
    split; [rewrite G1; exact F1 | rewrite F2; exact G2]. }
  split.
  { intros a k i Hin Hi. rewrite <- (Hblk a k i Hin Hi).
    pose proof (HBL a k Hin) as Hin2. apply blocks_In in Hin2 as (p & Hp & Hpin).
    destruct (mr_blocks B (aa_MR API) (aa_laws API) L A mem0 md p k i HM Hpin Hi) as (_ & H1 & H2 & _).
    unfold mbyte. rewrite (HL' (a + i) ltac:(subst a; lia)). reflexivity. }
  split.
  { intros a Ha. pose proof sa_errno_val as Ev.
    destruct (sa_eq_at mem0 mem' a (HL' a ltac:(lia))) as [_ G2].
    rewrite SEGS. apply G2. rewrite <- SEGS. exact (Herr a Ha). }
  split; [exact (sa_sink_keep mem0 mem' md HL Hsn)|].
  split; [exact Hres|].
  intros a Ha. apply Hwr, Hwin. exact Ha.
Qed.

Lemma sa_fr_run : forall g km hb L A regs mem md regs' mem' W,
  FR B APIf ra empty g km hb L A regs mem md ->
  Permutation (blocks L A) (hb ++ blocks (g_L g) (g_A g)) ->
  Frame.munch W mem mem' -> Frame.wmono rsegs mem mem' -> ro_agree rsegs mem' ->
  (forall x, 0 <= x < 2 ^ 64 -> ~ Frame.outside W x -> g_S g - SLOT_K <= x < g_S g - 104) ->
  getr regs' 2 = getr regs 2 -> getr regs' 3 = getr regs 3 -> getr regs' 4 = getr regs 4 ->
  FR B APIf ra empty g km hb L A regs' mem' md.
Proof.
  intros g km hb L A regs mem md regs' mem' W HFR HP MU WM MI' HW E2 E3 E4.
  destruct HFR as (HGV & F2 & F3 & F4 & Hsv & Hstk & HMI & Hrel & HM & HWf & HB & HID & Hmd & Hhigh & Himg &
                   Hblk & Herr & Hsn & Hres & Hwin).
  pose proof HGV as (_ & _ & _ & HS16 & HSK & HS47 & _).
  pose proof alloc_ceiling_value as Hac.
  pose proof (sa_unch W mem mem' (g_S g - SLOT_K) (g_S g - 104) MU HW) as HU.
  unfold SLOT_K, SLOT_STACK in *.
  apply (sa_fr_of g km hb L A mem md regs' mem'); try assumption; unfold SLOT_K, SLOT_STACK in *.
  - intros a k Hin. apply (Permutation_in _ (Permutation_sym HP)). apply in_or_app. right. exact Hin.
  - intros a Ha Hn. apply HU; [exact Ha | lia].
  - rewrite E2. exact F2.
  - rewrite E3. exact F3.
  - rewrite E4. exact F4.
  - apply (sa_bytes_keep mem mem' _ _ Hsv). intros i Hi. unfold saved_bytes in Hi.
    rewrite !length_app, !length_le8 in Hi. cbn in Hi. apply HU; lia.
Qed.

Lemma sa_fr_stk : forall g km hb L A regs mem md,
  FR B APIf ra empty g km hb L A regs mem md ->
  Frame.stk rsegs (normalize rsegs mem) (g_S g - SLOT_K) (g_S g).
Proof.
  intros g km hb L A regs mem md HFR.
  destruct HFR as (HGV & _ & _ & _ & _ & _ & HMI & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hwin).
  pose proof HGV as (_ & _ & _ & HS16 & HSK & HS47 & _).
  pose proof alloc_ceiling_value as Hac. pose proof sa_segs as SEGS.
  unfold MI in HMI. rewrite SEGS in HMI.
  apply sa_stk_norm; [exact HMI | unfold SA_TOP, SLOT_K, SLOT_STACK in *; lia | lia |].
  intros a Ha. rewrite <- SEGS. exact (Hwin a Ha).
Qed.

Lemma sa_fr_bnd : forall g km hb L A regs mem md,
  FR B APIf ra empty g km hb L A regs mem md ->
  getr regs 2 = Z_to_bv 64 (fsp g) /\ fsp g mod 16 = 0 /\ SA_TOP + SLOT_K <= g_S g /\ g_S g <= 2 ^ 47 /\
  ro_agree rsegs mem.
Proof.
  intros g km hb L A regs mem md HFR.
  destruct HFR as (HGV & F2 & _ & _ & _ & _ & HMI & _).
  pose proof HGV as (_ & _ & _ & HS16 & HSK & HS47 & _).
  pose proof alloc_ceiling_value as Hac. pose proof sa_segs as SEGS.
  unfold MI in HMI. rewrite SEGS in HMI.
  unfold fsp, SLOT_FRAME, SA_TOP in *. repeat split; try assumption; try lia.
Qed.

Lemma sa_mid : forall g km hb L A regs mem md pc (Q : machine_state -> Prop) (P : config -> Prop),
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
     Rz (ms_segs B) (mkCfg (mkst regs' pc' m' (seg_rom (ms_segs B))) md) P) ->
  Rz (ms_segs B) (mkCfg (mkst regs pc mem (seg_rom (ms_segs B))) md) P.
Proof.
  intros g km hb L A regs mem md pc Q P HFR HP HE Hform HK.
  pose proof sa_segs as SEGS.
  pose proof HFR as (_ & _ & _ & _ & _ & _ & HMI & _ & HM & _).
  unfold MI in HMI. rewrite SEGS in HMI.
  destruct (mr_model B _ (aa_laws API) _ _ _ _ HM) as (Hh & Hl & _).
  rewrite SEGS.
  apply (sa_run regs pc mem md Q P Hh Hl HMI HE).
  - intros ms HQ. destruct (Hform ms HQ) as (R & pc' & m' & -> & _). exists R, pc', m'. reflexivity.
  - intros R pc' m0' HQ regs' m' Hx Hrel Hsame.
    destruct (Hform _ HQ) as (R1 & pc1 & m1 & E & (W & MU & WM & HW) & E2 & E3 & E4).
    injection E; intros; subst.
    pose proof (mem_rel_normalize rsegs mem HMI) as HR0.
    rewrite <- SEGS. apply (HK R1 pc1 m1 regs' m' HQ Hx Hrel).
    apply (sa_fr_run g km hb L A regs mem md regs' m' W HFR HP).
    + exact (munch_rel rsegs W mem (normalize rsegs mem) m' m1 HR0 Hrel Hsame MU).
    + exact (wmono_rel rsegs mem (normalize rsegs mem) m' m1 HR0 Hrel Hsame WM).
    + exact (ro_agree_same rsegs mem m' HMI Hsame).
    + exact HW.
    + rewrite (sa_getr_eqv _ _ _ Hx). exact E2.
    + rewrite (sa_getr_eqv _ _ _ Hx). exact E3.
    + rewrite (sa_getr_eqv _ _ _ Hx). exact E4.
Qed.

End S.
