(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Copyright 2026 Theorem Labs *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_decode/lib/Prog/LLVMFuzzerTestOneInput_fr.v, with its module paths and module names changed; 456 of its 574 lines of code are new or changed and 409 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_headamp/lib/U/Prog/Seg/Tac_slot.v; 237 of its 370 lines of code are new or changed and 441 lines of the source are left out. *)
(* FR lifts of the segments of reac-pw/fuzz_headamp LLVMFuzzerTestOneInput (UBSan) for a run that also writes errno.
   Both parses of the harness call strtol, which writes errno (tp - 164 by the frame's TLS layout, an image static
   below alloc_ceiling): M03 (K14118 -> the malloc of first: memset(out), reac_headamp_prop_parse_result, the
   checks, the inlined pod_nearest) and M04b ([0x147fc, 0x1482c): memset(out), reac_headamp_prop_parse, check_plain)
   write the stack window [S - K, S - 104), the out block and errno, at a changed FP state. The kit's lifts
   (Tac_b1.b1_fr_hb, Tac_slot.sl_fr_run, Tac_slot.sl_mid_fp) ask every byte outside the window (and the one block) to
   stay. FR itself lets errno change: its two unchanged-byte clauses exclude [errno_addr B, errno_addr B + 4), and
   errno stays writable by its own clause, which wmono keeps. So the lifts below allow errno too:
   - te_fr_core: the common proof, b1_fr_hb's with errno excluded wherever b1_fr_hb uses mem' = mem below
     alloc_ceiling: the allocator-owned bytes (the frame's errno_unowned), the bytes of the live blocks (outside the
     image by AllocExtra's ax_blocks_img, while errno is in the image: te_errno_img), RELRO and the sink cells (the
     frame's ff_relro and the kit's b1_sink_addr exclude errno), the image clause (its own premise excludes errno),
     the saved bytes and the high clause (errno + 4 <= alloc_ceiling <= S - K);
   - b1_fr_hb_errno (Tac_b1 form, M03 and M04b: the out block), sl_fr_run_errno (Tac_slot form: window and errno),
     sl_fr_run_hb_errno and sl_mid_fp_hb_errno (the munch and FP-runner forms with one block),
     sl_mid_fp_hb_errno_cj (the FP runner on MemNorm.normalize_cj, for M03: headamp_check_contract takes
     MemNorm.task_mem for the soft-float callees; through sl_run_fp_cj, Tac_slot.sl_run_fp's twin by
     MemNorm.evt_normalize_cj; no runner of the kit or the frame runs on normalize_cj), te_fp3 (the footprint of the
     evts' munch lists), te_parse_tp / te_parse_writes (the parse's errno cell and write set at the two call sites).
   errno's cell is [errno_addr B, errno_addr B + 4) = [tp - 164, tp - 160) (errno_addr B = ms_tp B + ms_errno_off B);
   its value comes only from the frame's ff_tp / ff_errno_off (Tac_slot.sl_errno_val) inside proofs.
   New lemmas: the released-proof lookup of 2026-10-30 found no b1_fr_hb_errno / sl_fr_run_errno on main,
   ossv/recipes, ossv/candidates, release/pau-projects-recipes or the live heads. *)
From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.U.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.U.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.U.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Lib Require Import Mem Frame.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Lib Require MState Regs6ss RegisterBridge Exec Cells Step.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.U Require Import Img0 Contract FrameAPI.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.U.Prog Require Import SlotFR.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.U.Prog Require reac_headamp_prop_parse_result_c.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.U.Prog.Seg Require Import Tac_slot Tac_b1.
Import ListNotations.
Open Scope Z_scope.

(* A point not outside (lo, hi) :: W is in [lo, hi) or not outside W. *)
Lemma te_nout_cons : forall lo hi W x, ~ Frame.outside ((lo, hi) :: W) x -> lo <= x < hi \/ ~ Frame.outside W x.
Proof.
  intros lo hi W x O. destruct (Z_le_dec lo x) as [H1|H1]; [destruct (Z_lt_dec x hi) as [H2|H2]|].
  - left. lia.
  - right. intros O'. apply O. cbn [Frame.outside]. split; [lia | exact O'].
  - right. intros O'. apply O. cbn [Frame.outside]. split; [lia | exact O'].
Qed.

Lemma te_nout_nil : forall x, ~ Frame.outside [] x -> False.
Proof. intros x O. apply O. exact I. Qed.

Section RC.
Context {fx : FPState}.

(* Tac_slot.sl_run_fp for a run on MemNorm.normalize_cj (the memory of an evt whose callees take
   MemNorm.task_mem): the continuation gets the run's final memory up to mem_rel_cj and cj_same. *)
Lemma sl_run_fp_cj : forall regs pc mem md (Q : machine_state -> Prop) (P : config -> Prop),
  m_halted md = None -> m_vm_lazy md = [] -> ro_agree rsegs mem ->
  Exec.evt rsegs Q
    (MState.MS (Regs6ss.mkR_of regs) fp_regs pc fp_csr None (normalize_cj rsegs mem) (seg_rom rsegs)) ->
  (forall ms, Q ms -> exists R F' pc' fc' m', ms = MState.MS R F' pc' fc' None m' (seg_rom rsegs)) ->
  (forall R F' pc' fc' m0', Q (MState.MS R F' pc' fc' None m0' (seg_rom rsegs)) ->
     forall regs' m', Regs6ss.xregs_eqv R regs' -> mem_rel_cj rsegs m' m0' -> cj_same rsegs mem m' ->
     SR rsegs (mkCfg (@mkst (mkFP F' fc') regs' pc' m' (seg_rom rsegs)) md) P) ->
  SR rsegs (mkCfg (mkst regs pc mem (seg_rom rsegs)) md) P.
Proof.
  intros regs pc mem md Q P Hh Hl Hro HE Hform HK.
  apply (evt_SR_canon rsegs _
           (fun s => exists s0, Q s0 /\ ms_rel_cj rsegs s s0 /\ cj_same rsegs mem (ms_mem s)) md P);
    [| exact Hh | exact Hl |].
  - change (RegisterBridge.canonical_register_state (mkst regs pc mem (seg_rom rsegs)))
      with (MState.MS (Regs6ss.mkR_of regs) fp_regs pc fp_csr None mem (seg_rom rsegs)).
    apply evt_normalize_cj; [exact wx_apart_rsegs | exact Hro | exact HE].
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

End RC.

Section TE.
Context {fx : FPState} {rc : RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AllocAPI B.
Context {LS : lib_shape} {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Hypothesis FF : frame_facts_ubsan B APIf LS SH SK ra empty.
Let API := APIf rc.

(* errno's cell [tp - 164, tp - 160) lies in one reserved image segment (the RW segment). *)
Lemma te_resv_errno : existsb (fun s : word * word => (bv_unsigned (fst s) <=? errno_addr B) &&
    (errno_addr B + 4 <=? bv_unsigned (fst s) + bv_unsigned (snd s))) (segments_reserved rsegs) = true.
Proof. rewrite (sl_errno_val B APIf ra empty FF). vm_compute. reflexivity. Qed.

Lemma te_alloc : frame_allocator B API.
Proof. exact (b1_alloc B APIf ra empty FF). Qed.

Lemma te_ax : AllocExtra B (aa_MR API).
Proof. exact (b1_ax B APIf ra empty FF). Qed.

(* errno is in the image (so in no live block). *)
Lemma te_errno_img : forall a, errno_addr B <= a < errno_addr B + 4 -> in_img B a.
Proof.
  intros a Ha.
  pose proof (sl_segs B APIf ra empty FF) as HS.
  pose proof te_resv_errno as H. apply existsb_exists in H as (s & Hs & Hc).
  apply andb_true_iff in Hc as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2.
  split; [rewrite HS; intros Hn; rewrite Hn in Hs; cbn in Hs; destruct Hs|].
  exists s. rewrite HS. split; [exact Hs | lia].
Qed.

(* errno is not allocator-owned (the frame's errno_unowned). *)
Lemma te_errno_unowned : forall L A mem md a, aa_MR API L A mem md ->
  errno_addr B <= a < errno_addr B + 4 -> ~ owned B L A a.
Proof.
  intros L A mem md a HM Ha.
  destruct te_alloc as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & EU & _).
  exact (EU L A mem md a HM Ha).
Qed.

(* The common lift: FR across a run that writes the window [S - K, S - 104), the bytes [phi, phi + n) and errno,
   for [phi, phi + n) below alloc_ceiling, outside the image and the allocator's own bytes, present after the run and
   apart from the entry blocks (a live block of hb: b1_fr_hb_errno; nothing, n = 0: sl_fr_run_errno). Sound
   because FR's unchanged-byte clauses exclude errno and its errno clause asks only writability (wmono keeps it);
   every other use of mem' = mem below alloc_ceiling is at a byte that is not errno (the header). *)
Lemma te_fr_core : forall g hb phi n L A regs mem md regs' mem',
  FR B APIf ra empty g hb L A regs mem md ->
  Permutation (blocks L A) (hb ++ blocks (g_L g) (g_A g)) ->
  phi + n <= alloc_ceiling ->
  (forall a, phi <= a < phi + n ->
     ~ in_img B a /\ ~ owned B L A a /\ exists b, mem' (Z_to_bv 64 a) = Some b) ->
  (forall a k i, In (a, k) (blocks (g_L g) (g_A g)) -> 0 <= i < k -> ~ (phi <= a + i < phi + n)) ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (g_S g - SLOT_K <= a < g_S g - 104) -> ~ (phi <= a < phi + n) ->
     ~ (errno_addr B <= a < errno_addr B + 4) -> mem' (Z_to_bv 64 a) = mem (Z_to_bv 64 a)) ->
  Frame.wmono rsegs mem mem' -> ro_agree rsegs mem' ->
  YK11.getr regs' 2 = YK11.getr regs 2 -> YK11.getr regs' 3 = YK11.getr regs 3 ->
  YK11.getr regs' 4 = YK11.getr regs 4 ->
  FR B APIf ra empty g hb L A regs' mem' md.
Proof.
  intros g hb phi n L A regs mem md regs' mem' HFR HP Hbnd HBK HBE HU WM MI' E2 E3 E4.
  destruct HFR as (HGV & F2 & F3 & F4 & Hsv & Hstk & HMI & Hrel & HM & HWf & HB & HID & Hmd & Hhigh & Himg &
                   Hblk & Herr & Hsn & Hres & Hwin).
  pose proof HGV as (_ & _ & _ & HS16 & HSK & HS47 & _).
  pose proof alloc_ceiling_value as Hac. pose proof (sl_segs B APIf ra empty FF) as SEGS.
  pose proof (sl_errno B APIf ra empty FF) as Her.
  unfold SLOT_K, SLOT_STACK in *.
  assert (HL : forall a, 0 <= a < alloc_ceiling -> ~ (phi <= a < phi + n) ->
                 ~ (errno_addr B <= a < errno_addr B + 4) -> mem' (Z_to_bv 64 a) = mem (Z_to_bv 64 a)).
  { intros a Ha Hn He. apply HU; lia. }
  assert (HI : forall a, in_img B a -> ~ (errno_addr B <= a < errno_addr B + 4) ->
                 mem' (Z_to_bv 64 a) = mem (Z_to_bv 64 a)).
  { intros a Ha He. pose proof (sl_in_img_top B a SEGS Ha) as Ht. unfold SL_TOP in Ht.
    apply HL; [lia | intros Hc; exact (proj1 (HBK a Hc) Ha) | exact He]. }
  assert (HNE : forall a, ~ in_img B a -> ~ (errno_addr B <= a < errno_addr B + 4)).
  { intros a Hn He. exact (Hn (te_errno_img a He)). }
  assert (Hwr : forall a, writable_at (ms_segs B) mem a -> writable_at (ms_segs B) mem' a).
  { intros a W. unfold writable_at in *. rewrite SEGS in *. apply WM. exact W. }
  split; [exact HGV|]. split; [rewrite E2; exact F2|]. split; [rewrite E3; exact F3|].
  split; [rewrite E4; exact F4|].
  split.
  { apply (sl_bytes_keep mem mem' _ _ Hsv). intros i Hi. rewrite sl_saved_len in Hi.
    unfold SLOT_SAVE. apply HU; lia. }
  split.
  { apply sl_stk_of_writable; [unfold SL_TOP, SLOT_K, SLOT_STACK; lia | lia |].
    intros a Ha. rewrite <- SEGS. apply Hwr, Hwin. exact Ha. }
  split; [unfold MI; rewrite SEGS; exact MI'|].
  split.
  { unfold relro, G_img_c in *. intros a Ha. rewrite <- (Hrel a Ha).
    destruct (b1_relro_full B APIf ra empty FF a Ha) as (H1 & _ & _ & H4).
    unfold mbyte. rewrite (HI a H1 H4). reflexivity. }
  split.
  { destruct (mr_model B _ (aa_laws API) _ _ _ _ HM) as (Hh & Hl & Hmat).
    eapply (mr_frame B (aa_MR API) (aa_laws API)); [exact HM | | | | reflexivity | exact Hh | exact Hl | exact Hmat].
    - intros a Ho. pose proof (mr_owned_low B (aa_MR API) (aa_laws API) _ _ _ _ a HM Ho) as Ha.
      unfold mbyte.
      rewrite (HL a Ha (fun Hc => proj1 (proj2 (HBK a Hc)) Ho) (fun He => te_errno_unowned L A mem md a HM He Ho)).
      reflexivity.
    - intros a Ho [bb Hb]. pose proof (mr_owned_low B (aa_MR API) (aa_laws API) _ _ _ _ a HM Ho) as Ha.
      exists bb.
      rewrite (HL a Ha (fun Hc => proj1 (proj2 (HBK a Hc)) Ho) (fun He => te_errno_unowned L A mem md a HM He Ho)).
      exact Hb.
    - intros q k i Hq Hi.
      destruct (mr_blocks B (aa_MR API) (aa_laws API) L A mem md q k i HM Hq Hi) as ([bb Hpr] & H1 & H2 & _).
      pose proof (ax_blocks_img te_ax L A mem md q k i HM Hq Hi) as Hqi.
      destruct (Z_le_dec phi (ptr_addr L q + i)) as [Hl1|Hl1];
        [destruct (Z_lt_dec (ptr_addr L q + i) (phi + n)) as [Hl2|Hl2]|].
      + exact (proj2 (proj2 (HBK _ (conj Hl1 Hl2)))).
      + exists bb. rewrite (HL (ptr_addr L q + i) ltac:(lia) ltac:(lia) (HNE _ Hqi)). exact Hpr.
      + exists bb. rewrite (HL (ptr_addr L q + i) ltac:(lia) ltac:(lia) (HNE _ Hqi)). exact Hpr. }
  split; [exact HWf|]. split; [exact HB|]. split; [exact HID|]. split; [exact Hmd|].
  split.
  { intros a Ha Hns Hne. destruct (Hhigh a Ha Hns Hne) as [Q1 Q2]. unfold SLOT_K, SLOT_STACK in Hns.
    rewrite SEGS in *.
    destruct (sl_eq_at mem mem' a (HU a ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia))) as [G1 G2].
    split; [rewrite G1; exact Q1 | rewrite Q2; exact G2]. }
  split.
  { intros a H1 H2 H3 H4. destruct (Himg a H1 H2 H3 H4) as [Q1 Q2].
    destruct (sl_eq_at mem mem' a (HI a H1 H4)) as [G1 G2]. rewrite SEGS in *.
    split; [rewrite G1; exact Q1 | rewrite Q2; exact G2]. }
  split.
  { intros a k i Hin Hi. rewrite <- (Hblk a k i Hin Hi).
    pose proof (b1_in_E _ _ _ _ HP Hin) as HinL.
    apply blocks_In in HinL as (q & Eq & Hq).
    destruct (mr_blocks B (aa_MR API) (aa_laws API) L A mem md q k i HM Hq Hi) as (_ & H1 & H2 & _).
    pose proof (ax_blocks_img te_ax L A mem md q k i HM Hq Hi) as Hqi.
    rewrite Eq in H1, H2, Hqi.
    unfold mbyte. rewrite (HL (a + i) ltac:(lia) (HBE a k i Hin Hi) (HNE _ Hqi)). reflexivity. }
  split; [intros a Ha; apply Hwr; exact (Herr a Ha)|].
  split.
  { apply (b1_sink_frame B APIf ra empty FF mem mem' md md); [| reflexivity | exact Hsn].
    intros a Ha. destruct (b1_sink_addr B APIf ra empty FF a Ha) as (H1 & _ & _ & H4).
    unfold mbyte. rewrite (HI a H1 H4). reflexivity. }
  split; [exact Hres|].
  intros a Ha. apply Hwr, Hwin. exact Ha.
Qed.

(* b1_fr_hb with errno writable: FR across a run that writes the stack window [S - K, S - 104), one block (phi, n)
   of hb and [errno_addr B, errno_addr B + 4). Used by M03 (headamp_check_contract: memset(out), the parse with
   strtol, the checks) and M04b (headamp_plain_contract: memset(out), the plain parse, check_plain) with the out
   block. The widened premise is sound: te_fr_core (FR asks nothing of errno's bytes but writability). *)
Lemma b1_fr_hb_errno : forall g hb phi n L A regs mem md regs' mem',
  FR B APIf ra empty g hb L A regs mem md ->
  Permutation (blocks L A) (hb ++ blocks (g_L g) (g_A g)) -> In (phi, n) hb ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (g_S g - SLOT_K <= a < g_S g - 104) -> ~ (phi <= a < phi + n) ->
     ~ (errno_addr B <= a < errno_addr B + 4) ->
     mem' (Z_to_bv 64 a) = mem (Z_to_bv 64 a)) ->
  Frame.wmono rsegs mem mem' -> ro_agree rsegs mem' ->
  YK11.getr regs' 2 = YK11.getr regs 2 -> YK11.getr regs' 3 = YK11.getr regs 3 ->
  YK11.getr regs' 4 = YK11.getr regs 4 ->
  FR B APIf ra empty g hb L A regs' mem' md.
Proof.
  intros g hb phi n L A regs mem md regs' mem' HFR HP Hphi HU WM MI' E2 E3 E4.
  pose proof HFR as (_ & _ & _ & _ & _ & _ & _ & _ & HM & _).
  pose proof (sl_segs B APIf ra empty FF) as SEGS.
  pose proof (b1_in_hb _ _ _ _ HP Hphi) as Hin.
  pose proof (b1_blk_present B APIf ra empty FF L A mem md mem' phi n HM Hin WM) as Hpres.
  apply blocks_In in Hin as (p & Ep & Hp).
  destruct (mr_blocks_range B _ (aa_laws API) _ _ _ _ _ _ HM Hp) as [R1 R2]. rewrite Ep in R1, R2.
  pose proof alloc_ceiling_value as Hac.
  assert (Hnimg : forall a, phi <= a < phi + n -> ~ in_img B a).
  { intros a Ha Hi. apply (ax_blocks_img te_ax L A mem md p n (a - phi) HM Hp ltac:(lia)).
    rewrite Ep. replace (phi + (a - phi)) with a by lia. exact Hi. }
  apply (te_fr_core g hb phi n L A regs mem md regs' mem' HFR HP);
    [lia | | | exact HU | exact WM | exact MI' | exact E2 | exact E3 | exact E4].
  - intros a Ha. split; [exact (Hnimg a Ha)|]. split.
    + destruct (mr_blocks B _ (aa_laws API) L A mem md p n (a - phi) HM Hp ltac:(lia)) as (_ & _ & _ & H).
      rewrite Ep in H. replace (phi + (a - phi)) with a in H by lia. exact H.
    + destruct (Hpres a Ha) as (b' & Hb').
      exact (b1_present B mem' a b' SEGS (Hnimg a Ha) ltac:(lia) Hb').
  - intros a k i HinE Hi Hc.
    destruct (in_split _ _ Hphi) as (h1 & h2 & Eh). rewrite Eh in HP.
    pose proof (mr_blocks_disjoint B _ (aa_laws API) _ _ _ _ HM) as PD.
    apply (b1_pw_perm _ ranges_disjoint b1_rd_sym _ _ (b1_perm_front h1 h2 _ _ (phi, n) HP)) in PD.
    destruct PD as [PD _].
    assert (Hin2 : In (a, k) (h1 ++ h2 ++ blocks (g_L g) (g_A g)))
      by (apply in_or_app; right; apply in_or_app; right; exact HinE).
    pose proof (PD (a, k) Hin2) as Hd. unfold ranges_disjoint in Hd. cbn [fst snd] in Hd. lia.
Qed.

(* sl_fr_run with errno writable: FR across a Kind A run whose writes lie in the window [S - K, S - 104) and
   errno (no block). Sound: te_fr_core with the empty block (phi, n) = (0, 0). *)
Lemma sl_fr_run_errno : forall g hb L A regs mem md regs' mem' W,
  FR B APIf ra empty g hb L A regs mem md ->
  Permutation (blocks L A) (hb ++ blocks (g_L g) (g_A g)) ->
  Frame.munch W mem mem' -> Frame.wmono rsegs mem mem' -> ro_agree rsegs mem' ->
  (forall x, 0 <= x < 2 ^ 64 -> ~ Frame.outside W x ->
     g_S g - SLOT_K <= x < g_S g - 104 \/ errno_addr B <= x < errno_addr B + 4) ->
  getr regs' 2 = getr regs 2 -> getr regs' 3 = getr regs 3 -> getr regs' 4 = getr regs 4 ->
  FR B APIf ra empty g hb L A regs' mem' md.
Proof.
  intros g hb L A regs mem md regs' mem' W HFR HP MU WM MI' HW E2 E3 E4.
  pose proof alloc_ceiling_value as Hac.
  apply (te_fr_core g hb 0 0 L A regs mem md regs' mem' HFR HP);
    [lia | intros a Ha; exfalso; lia | intros a k i _ _; lia | | exact WM | exact MI' | exact E2 | exact E3 |
     exact E4].
  intros a Ha Hw _ He. apply MU. rewrite (MState.unsigned_lit a Ha).
  destruct (sl_outside_dec W a) as [O|O]; [exact O|]. exfalso.
  destruct (HW a Ha O) as [H|H]; [exact (Hw H) | exact (He H)].
Qed.

(* b1_fr_hb_errno in sl_fr_run's munch form: the run's writes W lie in the window, one block (phi, n) of hb and
   errno. For M03 / M04b, whose evts post munch over [sp - MID_STACK, ..), the out block and errno (te_fp3). *)
Lemma sl_fr_run_hb_errno : forall g hb phi n L A regs mem md regs' mem' W,
  FR B APIf ra empty g hb L A regs mem md ->
  Permutation (blocks L A) (hb ++ blocks (g_L g) (g_A g)) -> In (phi, n) hb ->
  Frame.munch W mem mem' -> Frame.wmono rsegs mem mem' -> ro_agree rsegs mem' ->
  (forall x, 0 <= x < 2 ^ 64 -> ~ Frame.outside W x ->
     g_S g - SLOT_K <= x < g_S g - 104 \/ phi <= x < phi + n \/ errno_addr B <= x < errno_addr B + 4) ->
  getr regs' 2 = getr regs 2 -> getr regs' 3 = getr regs 3 -> getr regs' 4 = getr regs 4 ->
  FR B APIf ra empty g hb L A regs' mem' md.
Proof.
  intros g hb phi n L A regs mem md regs' mem' W HFR HP Hphi MU WM MI' HW E2 E3 E4.
  apply (b1_fr_hb_errno g hb phi n L A regs mem md regs' mem' HFR HP Hphi);
    [| exact WM | exact MI' | exact E2 | exact E3 | exact E4].
  intros a Ha Hw Hb He. apply MU. rewrite (MState.unsigned_lit a Ha).
  destruct (sl_outside_dec W a) as [O|O]; [exact O|]. exfalso.
  destruct (HW a Ha O) as [H|[H|H]]; [exact (Hw H) | exact (Hb H) | exact (He H)].
Qed.

(* sl_mid_fp with one block of hb and errno writable: a run that ends at its own FP state (rounding mode 0 kept)
   and writes the window, the block (phi, n) and errno keeps FR; the continuation runs at the FP state mkFP F' fc'.
   For M04b (headamp_plain_contract on the normalized memory: the plain parse and check_plain write the FP
   registers and fflags, the out block and errno). *)
Lemma sl_mid_fp_hb_errno : forall g hb phi n L A regs mem md pc (Q : machine_state -> Prop) (P : config -> Prop),
  FR B APIf ra empty g hb L A regs mem md ->
  Permutation (blocks L A) (hb ++ blocks (g_L g) (g_A g)) -> In (phi, n) hb ->
  Exec.evt rsegs Q (MState.MS (Regs6ss.mkR_of regs) fp_regs pc fp_csr None (normalize rsegs mem) (seg_rom rsegs)) ->
  (forall ms, Q ms -> exists R F' pc' fc' m', ms = MState.MS R F' pc' fc' None m' (seg_rom rsegs) /\
     frm_zero fc' /\
     (exists W, Frame.munch W (normalize rsegs mem) m' /\ Frame.wmono rsegs (normalize rsegs mem) m' /\
        (forall x, 0 <= x < 2 ^ 64 -> ~ Frame.outside W x ->
           g_S g - SLOT_K <= x < g_S g - 104 \/ phi <= x < phi + n \/ errno_addr B <= x < errno_addr B + 4)) /\
     getr R 2 = getr regs 2 /\ getr R 3 = getr regs 3 /\ getr R 4 = getr regs 4) ->
  (forall R F' pc' fc' m0' regs' m', Q (MState.MS R F' pc' fc' None m0' (seg_rom rsegs)) ->
     Regs6ss.xregs_eqv R regs' -> mem_rel rsegs m' m0' -> frm_zero fc' ->
     FR B APIf ra empty g hb L A regs' m' md ->
     SR (ms_segs B) (mkCfg (@mkst (mkFP F' fc') regs' pc' m' (seg_rom (ms_segs B))) md) P) ->
  SR (ms_segs B) (mkCfg (mkst regs pc mem (seg_rom (ms_segs B))) md) P.
Proof.
  intros g hb phi n L A regs mem md pc Q P HFR HP Hphi HE Hform HK.
  pose proof (sl_segs B APIf ra empty FF) as SEGS.
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
    apply (sl_fr_run_hb_errno g hb phi n L A regs mem md regs' m' W HFR HP Hphi).
    + exact (munch_rel rsegs W mem (normalize rsegs mem) m' m1 HR0 Hrel Hsame MU).
    + exact (wmono_rel rsegs mem (normalize rsegs mem) m' m1 HR0 Hrel Hsame WM).
    + exact (ro_agree_same rsegs mem m' HMI Hsame).
    + exact HW.
    + rewrite (sl_getr_eqv _ _ _ Hx). exact E2.
    + rewrite (sl_getr_eqv _ _ _ Hx). exact E3.
    + rewrite (sl_getr_eqv _ _ _ Hx). exact E4.
Qed.

(* sl_mid_fp_hb_errno for an evt run on MemNorm.normalize_cj of the cut's memory: M03 (headamp_check_contract takes
   MemNorm.task_mem for the soft-float callees of the inlined pod_nearest, as role's role_check_contract does). The
   run's munch / wmono / footprint facts are on normalize_cj; munch_rel_cj, wmono_rel_cj and ro_agree_same_cj carry
   them to the continuation's memory, which relates to the run's final memory by mem_rel_cj; FR follows by
   sl_fr_run_hb_errno (the window, the out block and errno). *)
Lemma sl_mid_fp_hb_errno_cj : forall g hb phi n L A regs mem md pc (Q : machine_state -> Prop)
    (P : config -> Prop),
  FR B APIf ra empty g hb L A regs mem md ->
  Permutation (blocks L A) (hb ++ blocks (g_L g) (g_A g)) -> In (phi, n) hb ->
  Exec.evt rsegs Q
    (MState.MS (Regs6ss.mkR_of regs) fp_regs pc fp_csr None (normalize_cj rsegs mem) (seg_rom rsegs)) ->
  (forall ms, Q ms -> exists R F' pc' fc' m', ms = MState.MS R F' pc' fc' None m' (seg_rom rsegs) /\
     frm_zero fc' /\
     (exists W, Frame.munch W (normalize_cj rsegs mem) m' /\ Frame.wmono rsegs (normalize_cj rsegs mem) m' /\
        (forall x, 0 <= x < 2 ^ 64 -> ~ Frame.outside W x ->
           g_S g - SLOT_K <= x < g_S g - 104 \/ phi <= x < phi + n \/ errno_addr B <= x < errno_addr B + 4)) /\
     getr R 2 = getr regs 2 /\ getr R 3 = getr regs 3 /\ getr R 4 = getr regs 4) ->
  (forall R F' pc' fc' m0' regs' m', Q (MState.MS R F' pc' fc' None m0' (seg_rom rsegs)) ->
     Regs6ss.xregs_eqv R regs' -> mem_rel_cj rsegs m' m0' -> frm_zero fc' ->
     FR B APIf ra empty g hb L A regs' m' md ->
     SR (ms_segs B) (mkCfg (@mkst (mkFP F' fc') regs' pc' m' (seg_rom (ms_segs B))) md) P) ->
  SR (ms_segs B) (mkCfg (mkst regs pc mem (seg_rom (ms_segs B))) md) P.
Proof.
  intros g hb phi n L A regs mem md pc Q P HFR HP Hphi HE Hform HK.
  pose proof (sl_segs B APIf ra empty FF) as SEGS.
  pose proof HFR as (_ & _ & _ & _ & _ & _ & HMI & _ & HM & _).
  unfold MI in HMI. rewrite SEGS in HMI.
  destruct (mr_model B _ (aa_laws API) _ _ _ _ HM) as (Hh & Hl & _).
  rewrite SEGS.
  apply (sl_run_fp_cj regs pc mem md Q P Hh Hl HMI HE).
  - intros ms HQ. destruct (Hform ms HQ) as (R & F' & pc' & fc' & m' & -> & _). exists R, F', pc', fc', m'.
    reflexivity.
  - intros R F' pc' fc' m0' HQ regs' m' Hx Hrel Hsame.
    destruct (Hform _ HQ) as (R1 & F1 & pc1 & fc1 & m1 & E & Hfrm & (W & MU & WM & HW) & E2 & E3 & E4).
    injection E; intros; subst.
    pose proof (mem_rel_cj_normalize rsegs mem HMI) as HR0.
    rewrite <- SEGS. apply (HK R1 F1 pc1 fc1 m1 regs' m' HQ Hx Hrel Hfrm).
    apply (sl_fr_run_hb_errno g hb phi n L A regs mem md regs' m' W HFR HP Hphi).
    + exact (munch_rel_cj rsegs W mem (normalize_cj rsegs mem) m' m1 HR0 Hrel Hsame MU).
    + exact (wmono_rel_cj rsegs mem (normalize_cj rsegs mem) m' m1 HR0 Hrel Hsame WM).
    + exact (ro_agree_same_cj rsegs mem m' HMI Hsame).
    + exact HW.
    + rewrite (sl_getr_eqv _ _ _ Hx). exact E2.
    + rewrite (sl_getr_eqv _ _ _ Hx). exact E3.
    + rewrite (sl_getr_eqv _ _ _ Hx). exact E4.
Qed.

(* The footprint of M03's and M04b's evts: munch over an interval inside the window, an interval inside the block
   (phi, n) and errno lies in the window, the block and errno (the premise of sl_fr_run_hb_errno). *)
Lemma te_fp3 : forall g lo hi o k phi n E x,
  g_S g - SLOT_K <= lo -> hi <= g_S g - 104 -> phi <= o -> o + k <= phi + n -> E = errno_addr B ->
  ~ Frame.outside [(lo, hi); (o, o + k); (E, E + 4)] x ->
  g_S g - SLOT_K <= x < g_S g - 104 \/ phi <= x < phi + n \/ errno_addr B <= x < errno_addr B + 4.
Proof.
  intros g lo hi o k phi n E x H1 H2 H3 H4 -> HO.
  destruct (te_nout_cons _ _ _ _ HO) as [H|HO1]; [left; lia|].
  destruct (te_nout_cons _ _ _ _ HO1) as [H|HO2]; [right; left; lia|].
  destruct (te_nout_cons _ _ _ _ HO2) as [H|HO3]; [right; right; lia|].
  exfalso. exact (te_nout_nil x HO3).
Qed.

(* The parse's errno cell at a cut: FR's tp is the entry's, Z_to_bv 64 (ms_tp B) (GV), and tp - 164 is
   errno_addr B (the frame's ms_tp and ms_errno_off), so PARSE_ERRNO (getr regs 4) = errno_addr B. *)
Lemma te_parse_tp : forall g hb L A regs mem md, FR B APIf ra empty g hb L A regs mem md ->
  getr regs 4 = Z_to_bv 64 (ms_tp B) /\
  reac_headamp_prop_parse_result_c.PARSE_ERRNO (getr regs 4) = errno_addr B.
Proof.
  intros g hb L A regs mem md HFR.
  pose proof HFR as (HGV & _ & _ & F4 & _).
  pose proof HGV as (_ & _ & _ & _ & _ & _ & _ & _ & Htp).
  rewrite F4, Htp. split; [reflexivity|].
  unfold reac_headamp_prop_parse_result_c.PARSE_ERRNO, errno_addr.
  rewrite (ff_tp B APIf ra empty FF), (ff_errno_off B APIf ra empty FF).
  rewrite MState.unsigned_lit by lia. reflexivity.
Qed.

(* The write set of the parse at M03's call (0x14158, reac_headamp_prop_parse_result, res = sp + 0x178) and M04b's
   (0x14818, reac_headamp_prop_parse, res = NULL), sp = fsp g = S - 608: for n <= cap cells, parse_writes lies in
   the window (the parse's stack [sp - 0x200, sp) and res [S - 232, S - 220)), the out block (out, 3 (cap + 1)) and
   errno (PARSE_ERRNO tp = errno_addr B: te_parse_tp). *)
Lemma te_parse_writes : forall g out cap n R tp x,
  reac_headamp_prop_parse_result_c.PARSE_ERRNO tp = errno_addr B -> n <= cap -> (R = 0 \/ R = fsp g + 0x178) ->
  ~ Frame.outside (reac_headamp_prop_parse_result_c.parse_writes (fsp g) out n
                     (reac_headamp_prop_parse_result_c.PARSE_ERRNO tp) R) x ->
  g_S g - SLOT_K <= x < g_S g - 104 \/ out <= x < out + 3 * (cap + 1) \/ errno_addr B <= x < errno_addr B + 4.
Proof.
  intros g out cap n R tp x Etp Hn HR HO. rewrite Etp in HO.
  unfold reac_headamp_prop_parse_result_c.parse_writes in HO. cbn [app] in HO.
  unfold reac_headamp_prop_parse_result_c.PARSE_STACK, fsp, SLOT_FRAME, SLOT_K, SLOT_STACK in *.
  destruct (te_nout_cons _ _ _ _ HO) as [H|HO1]; [left; lia|].
  destruct (te_nout_cons _ _ _ _ HO1) as [H|HO2]; [right; left; lia|].
  destruct (te_nout_cons _ _ _ _ HO2) as [H|HO3]; [right; right; lia|].
  destruct (R =? 0) eqn:ER; cbv iota in HO3.
  - exfalso. exact (te_nout_nil x HO3).
  - apply Z.eqb_neq in ER.
    destruct (te_nout_cons _ _ _ _ HO3) as [H|HO4]; [|exfalso; exact (te_nout_nil x HO4)].
    destruct HR as [HR|HR]; [exfalso; exact (ER HR) | left; lia].
Qed.

End TE.
