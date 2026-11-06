(* reac_box_model_block (0x865d8) of fuzz_ctrl's ASan+UBSan build (image B, libreac v1.9.0): the TOP of
   pb_reac_box_model_block, the proof of treac_box_model_block_spec (lib/B/Prog/C_reac_box_model_block.v),
   a Theorem Labs lane.  Plan of record: pb_reac_box_model_block.plan.md (a working note, not in this delivery).

   The composition (plan, section "The composition"), one continuation each, all at the same world W:
     ENTRY  mbB_entry (C_reac_box_model_blockEnt.v): the spec's premises give stretch A's premises at memc;
            mbB_rngW (C_reac_box_model_blockVis.v) gives the footprint at RNG_W (w_H W) over normalize memc;
     A      mbB_to_E0 (C_reac_box_model_blockPf.v): stretch A lifted, the journal at m1;
     E0     mbB_E0 (Pf): the class-0 fake-stack request (aj_stack_malloc_at_fc at cid 0);
     MID    mbB_mid (C_reac_box_model_blockMid.v): stretch B's premises at mem2;
     B      GlueLift.rrB_lift over mb_post_rebaseRB (C_reac_box_model_blockRBLib.v): stretch B re-based at mem2;
     J      pb_J_SB below, by GlueLift.rrB_journal_free at cid 0: the journal after the frame's release;
     POST   mbB_post (C_reac_box_model_blockPost.v): the spec's post.

   Route (C) (a Theorem Labs lane 11:13Z; L3 recipe): no VIS0.  The lifted run is the NARROWED copy (gen_rb_modelblock.py --narrow,
   the run's universal shadow premise is shadow_rw_on R over its own region R, reac_box_model_block_shadow_R), and
   the glue supplies R at mem2 from ctl_rt_C_of_AR's cut_shadow / img_shadow (C_reac_box_model_blockMid.v by
   C_reac_box_model_blockCover.mbB_R_on).  Every ProgWorld statement the glue uses is PROVED on image B and cited
   by name inside Ent and Mid (a Theorem Labs lane's db8a86df2da); none is a premise here.

   rule 24: no function proved (glue of the proved run reac_box_model_block_holds_F; lookup of record
   lookup-reac_box_model_block.txt (a working note, not in this delivery), CONFIRM in lookup-check.md (a working note, not in this delivery)). *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Sem.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Frame Cells Step.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require Import Img0 AsanRT.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog Require Import asan_stack_malloc_c reac_box_model_block_c.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require ExecF Regs6ss.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require YK11 YK04 YK0s YA0n YA0nR YM05 YI16 YI00.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require YG00 YG01 YG0f YG0d YG0n YG0v YCbq YF0m.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require MemNorm MemNormTr ProgBridge ProgBridgeData ProgWorld.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog Require ImgBounds CtrlRo CtrlImg CtrlCallerJ GlueLift.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog Require C_reac_box_model_block C_reac_box_model_blockRB.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog Require C_reac_box_model_blockRBF C_reac_box_model_blockRBLib
  C_reac_box_model_blockEnt C_reac_box_model_blockVis C_reac_box_model_blockPf C_reac_box_model_blockMid
  C_reac_box_model_blockPost reac_box_model_blockF.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog Require asan_stack_malloc_cF_on asan_memset_cF_on
  asan_memcpy_cF_on build_dt1_single_c dt1_head_c name_field_c name_field_c_on.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require RcSynth.
#[local] Existing Instance CtrlImg.PI_ctrl_B.
Import ListNotations.
Open Scope Z_scope.

(* ---- small facts above the image end ---------------------------------------------------------------------------- *)

(* No segment reaches above IMG_HI, so there the writable view of a memory is the memory itself. *)
Lemma pb_wv_present : forall (m : word -> option byte) (x : word),
  ImgBounds.IMG_HI <= bv_unsigned x -> wview rsegs m x <> None -> exists b, m x = Some b.
Proof.
  intros m x Hx V. destruct (m x) as [b|] eqn:E; [exists b; reflexivity|].
  exfalso. apply V. unfold wview. rewrite E.
  destruct (find_segment rsegs (bv_unsigned x) 1) as [s|] eqn:F; [|reflexivity].
  exfalso. pose proof (bv_unsigned_in_range _ x) as R.
  destruct (B.MemNormTr.find_segment_end_below rsegs ImgBounds.IMG_HI (bv_unsigned x) 1 s
              B.MemNormTr.rsegs_below_img F ltac:(lia)) as [L|L]; lia.
Qed.

(* A byte present in mn above IMG_HI is readable in any m' that wmono keeps writable from mn. *)
Lemma pb_rd_end : forall (mn m' : word -> option byte) (x : word),
  wmono rsegs mn m' -> ImgBounds.IMG_HI <= bv_unsigned x -> (exists b, mn x = Some b) ->
  exists b, mrd rsegs m' x = Some b.
Proof.
  intros mn m' x WM Hx [b E].
  assert (V : wview rsegs mn x <> None) by (unfold wview; rewrite E; discriminate).
  destruct (pb_wv_present m' x Hx (WM x V)) as [b' E'].
  exists b'. unfold mrd. rewrite E'. reflexivity.
Qed.

(* normalize keeps every byte above IMG_HI. *)
Lemma pb_norm_above : forall (m : word -> option byte) (a : Z), ImgBounds.IMG_HI <= a < 2 ^ 64 ->
  B.MemNorm.normalize rsegs m (wa a) = m (wa a).
Proof.
  intros m a Ha. unfold B.MemNorm.normalize. rewrite (B.MemNormTr.ro_addr_above_img a Ha). reflexivity.
Qed.

(* A byte the accessible view reads above IMG_HI is a byte of the memory (no rom fallback there). *)
Lemma pb_aview_present : forall (H : word -> bool) (m : word -> option byte) (a : Z),
  ImgBounds.IMG_HI <= a < 2 ^ 64 -> lib.Reusable.YG0n.aview rsegs H m a <> None ->
  exists b, m (Z_to_bv 64 a) = Some b.
Proof.
  intros H m a Ha V. unfold lib.Reusable.YG0n.aview, lib.Reusable.YP09.mbyte, lib.Reusable.YK04.mrestrict in V.
  destruct (H (Z_to_bv 64 a)); [|destruct (m (Z_to_bv 64 a)) as [b|] eqn:E; [exists b; reflexivity|]].
  all: exfalso; apply V;
    match goal with |- option_map _ ?X = None =>
      replace X with (@None byte) by (first [exact (GlueLift.rrB_seg_rom_above a Ha)
                                             | symmetry; exact (GlueLift.rrB_seg_rom_above a Ha)]) end;
    reflexivity.
Qed.

Lemma pb_in_dec : forall lo hi a : Z, lo <= a < hi \/ ~ (lo <= a < hi).
Proof.
  intros lo hi a. destruct (Z_lt_le_dec a lo) as [H1|H1]; [right; intros [H _]; lia|].
  destruct (Z_lt_le_dec a hi) as [H2|H2]; [left; lia | right; intros [_ H]; lia].
Qed.

Lemma pb_outside_dec : forall (L : list ivl) (a : Z), outside L a \/ ~ outside L a.
Proof.
  induction L as [|(lo, hi) L IH]; intros a; cbn [outside]; [left; exact I|].
  destruct (pb_in_dec lo hi a) as [I1|I1]; [right; intros [N _]; exact (N I1)|].
  destruct (IH a) as [O|O]; [left; split; assumption | right; intros [_ O']; exact (O O')].
Qed.

Lemma pb_not_outside : forall (L : list ivl) (a : Z), ~ outside L a -> exists r, In r L /\ fst r <= a < snd r.
Proof.
  induction L as [|(lo, hi) L IH]; intros a N; cbn [outside] in N; [exfalso; exact (N I)|].
  destruct (pb_in_dec lo hi a) as [I1|I1]; [exists (lo, hi); split; [left; reflexivity | exact I1]|].
  destruct (pb_outside_dec L a) as [O|O]; [exfalso; exact (N (conj I1 O))|].
  destruct (IH a O) as (r & Hr & Hin). exists r. split; [right; exact Hr | exact Hin].
Qed.

Lemma pb_in_not_outside : forall (L : list ivl) (r : ivl) (a : Z), In r L -> fst r <= a < snd r -> ~ outside L a.
Proof.
  induction L as [|(lo, hi) L IH]; intros r a Hr Hin O; cbn [outside] in O; [destruct Hr|].
  destruct O as [N O]. destruct Hr as [Er|Hr]; [subst r; exact (N Hin) | exact (IH r a Hr Hin O)].
Qed.

(* the class-0 frame and flag of the layout are the side stack's fs_frame / fs_flag at FS := ly_F *)
Lemma pb_frame_addr0 : forall ly pos,
  lib.Reusable.YG0f.frame_addr ly 0 pos = fs_frame (lib.Reusable.YG0f.ly_F ly) 0 pos.
Proof.
  intros ly pos. unfold lib.Reusable.YG0f.frame_addr, lib.Reusable.YG0f.fs_frame_off, fs_frame, fs_B.
  unfold lib.Reusable.YG0f.kFakeFramesOff, lib.Reusable.YG00.fs_frame_bytes.
  change (Z.shiftl 64 0) with 64. cbn [Z.of_nat]. lia.
Qed.

Lemma pb_flag_addr0 : forall ly pos,
  lib.Reusable.YG0f.flag_addr ly 0 pos = fs_flag (lib.Reusable.YG0f.ly_F ly) 0 pos.
Proof.
  intros ly pos. unfold lib.Reusable.YG0f.flag_addr, lib.Reusable.YG0f.fs_flag_off, fs_flag.
  unfold lib.Reusable.YG0f.kFakeFlagsOff. change (lib.Reusable.YG0f.fs_flags_off 0) with 0. cbn [Z.of_nat]. lia.
Qed.

Lemma pb_awr_cons : forall STK sp0 FP bl0 blc ly own x a,
  lib.Reusable.YCbq.awr_byte STK sp0 FP bl0 blc ly own a ->
  lib.Reusable.YCbq.awr_byte STK sp0 FP bl0 blc ly (x :: own) a.
Proof.
  intros STK sp0 FP bl0 blc ly own x a H. unfold lib.Reusable.YCbq.awr_byte in *.
  destruct H as [H|[H|[H|(cid & pos & Hin & H)]]]; [left; exact H | right; left; exact H |
    right; right; left; exact H | right; right; right].
  exists cid, pos. split; [right; exact Hin | exact H].
Qed.

(* ---- stretch B's own write set ----------------------------------------------------------------------------------- *)

(* The bytes stretch B writes (the re-based copy's Q0 munch list at the run frame fr = fs_frame FS 0 pos): the
   window, the flag byte, the frame, its 8 shadow bytes, and the output block when p and o are nonzero. *)
Definition pb_WL (sp : word) (FS pos p o : Z) : list ivl :=
  C_reac_box_model_blockRB.Wf sp FS (fs_frame FS 0 pos) pos 1 ++
  (if (p =? 0) || (o =? 0) then [] else [(o, o + 32)]).

Definition pb_Wr (sp : word) (FS pos p o : Z) : Z -> Prop := fun a => ~ outside (pb_WL sp FS pos p o) a.

Lemma pb_Wr_cases : forall sp FS pos p o a, pb_Wr sp FS pos p o a ->
  bv_unsigned sp - 4272 <= a < bv_unsigned sp \/
  a = fs_flag FS 0 pos \/
  fs_frame FS 0 pos <= a < fs_frame FS 0 pos + 64 \/
  shadow_addr (fs_frame FS 0 pos) <= a < shadow_addr (fs_frame FS 0 pos) + 8 \/
  ((p =? 0) || (o =? 0) = false /\ o <= a < o + 32).
Proof.
  intros sp FS pos p o a H. destruct (pb_not_outside _ a H) as (r & Hr & Hin).
  unfold pb_WL, C_reac_box_model_blockRB.Wf in Hr. apply in_app_or in Hr.
  destruct Hr as [Hr|Hr].
  - cbn [In] in Hr. destruct Hr as [E|[E|[E|[E|[E|[]]]]]]; subst r; cbn [fst snd] in Hin.
    + left. exact Hin.
    + lia.
    + right; left. lia.
    + right; right; left. exact Hin.
    + right; right; right; left. exact Hin.
  - destruct ((p =? 0) || (o =? 0)) eqn:E; [destruct Hr|].
    destruct Hr as [Er|[]]. subst r. cbn [fst snd] in Hin. right; right; right; right. split; [reflexivity | exact Hin].
Qed.

Lemma pb_Wr_dec : forall sp FS pos p o a, pb_Wr sp FS pos p o a \/ ~ pb_Wr sp FS pos p o a.
Proof.
  intros sp FS pos p o a. unfold pb_Wr. destruct (pb_outside_dec (pb_WL sp FS pos p o) a) as [O|O];
    [right; intros N; exact (N O) | left; exact O].
Qed.

Lemma pb_Wr_out : forall sp FS pos p o a, ~ pb_Wr sp FS pos p o a -> outside (pb_WL sp FS pos p o) a.
Proof.
  intros sp FS pos p o a N. destruct (pb_outside_dec (pb_WL sp FS pos p o) a) as [O|O]; [exact O|].
  exfalso. exact (N O).
Qed.

Section Pb.
Context {fx : lib.Reusable.YK11.FPState} {rc : lib.Reusable.YM05.RunCeil} {SK : lib.Reusable.YI16.sink_head}.
Variable B : lib.Reusable.YG0f.asyms.
(* core, the TfibLib record (PENDING THE RECORD CORE, YCeg.v:25 refused name) *)
Hypothesis LAWS : lib.Reusable.YG0d.AR_laws rsegs B.
Hypothesis segs_low : forall a, lib.Reusable.YG0d.in_img rsegs a -> 0 <= a < lib.Reusable.YG0f.kLowMemEnd.
Hypothesis ML : lib.Reusable.YG0d.model_laws (lib.Reusable.YG0f.as_universe B).
(* a Theorem Labs lane's fake-stack release rules (a working branch) *)
Hypothesis ASF : lib.Reusable.YG0d.astack_free_law rsegs B.
Hypothesis FFL : lib.Reusable.YCbq.frame_flag_lawP rsegs B.

(* ---- The journal after stretch B (step J of the composition).  Stretch B writes pb_Wr: the window and the class-0
   frame with its shadow are awr bytes through own ((0, pos) :: own), the output block is the caller's grant, and the
   flag byte is the release.  All of them lie above IMG_HI.  Off pb_Wr the normalized end memory is normalize mem2
   (Q0's munch).  Each written byte is readable at the end: the window by the post's stk, the flag by Q0's readback
   (generator item 12), the frame shadow by the post's shadow_rw, and the frame and the output block by wmono from
   their presence at mem2.  rrB_journal_free at cid 0 then frees the frame. ---- *)
Lemma pb_J_SB :
  forall STK sp0 FP ly S0 (W0 : lib.Reusable.YA0n.world rsegs) mem0 md0 own lyc S2
         (W : lib.Reusable.YA0n.world rsegs) (mem2 : word -> option byte) md2 k (sp : word) (pos p o : Z)
         (sN : machine_state) (m1 : word -> option byte) md3,
    lib.Reusable.YCbq.ajournal rsegs B STK sp0 FP ly S0 W0 mem0 md0 ((0, pos) :: own) lyc S2 W mem2 md2 k ->
    0 <= pos < fs_M 0 ->
    sp0 - STK <= bv_unsigned sp - 4272 -> bv_unsigned sp <= sp0 ->
    HIGHMEM_BEG <= bv_unsigned sp - 4272 -> bv_unsigned sp <= APPMEM_END ->
    ImgBounds.IMG_HI <= lib.Reusable.YG0f.ly_F lyc -> ASAN_GT <= lib.Reusable.YG0f.ly_F lyc ->
    lib.Reusable.YG0f.ly_F lyc + FS_SIZE <= bv_unsigned sp - 4272 ->
    (o <> 0 -> ImgBounds.IMG_HI <= o /\ o + 32 <= 2 ^ 64 /\
       (forall a, o <= a < o + 32 ->
          lib.Reusable.YCbq.awr_byte STK sp0 FP (lib.Reusable.YG0d.ablocks B ly S0)
            (lib.Reusable.YG0d.ablocks B lyc S2) lyc own a) /\
       wr_at rsegs mem2 o 32) ->
    (forall a, lib.Reusable.YG0f.frame_addr lyc 0 pos <= a <
               lib.Reusable.YG0f.frame_addr lyc 0 pos + lib.Reusable.YG00.fs_frame_bytes 0 ->
       lib.Reusable.YG0n.apresent (lib.Reusable.YA0n.w_H W) mem2 a) ->
    munch (pb_WL sp (lib.Reusable.YG0f.ly_F lyc) pos p o) (B.MemNorm.normalize rsegs mem2) (ms_mem sN) ->
    mrd rsegs (ms_mem sN) (wa (fs_flag (lib.Reusable.YG0f.ly_F lyc) 0 pos)) = Some (Z_to_bv 8 0) ->
    wmono rsegs (B.MemNorm.normalize rsegs mem2) (ms_mem sN) ->
    stk rsegs (ms_mem sN) (bv_unsigned sp - 4272) (bv_unsigned sp) ->
    lib.Reusable.YG0v.zero_shadow (lib.Reusable.YG0n.aview rsegs (lib.Reusable.YA0n.w_H W) mem2)
      lib.Reusable.YG0f.SHADOW_OFF (lib.Reusable.YG0f.frame_addr lyc 0 pos) (lib.Reusable.YG00.fs_frame_bytes 0) ->
    B.MemNorm.mem_rel rsegs m1 (ms_mem sN) -> B.MemNorm.ro_same rsegs mem2 m1 ->
    (forall x : word, lib.Reusable.YA0n.w_H W x = true -> m1 x = mem2 x) ->
    lib.Reusable.YK04.same_but_materialized md2 md3 ->
    lib.Reusable.YCbq.ajournal rsegs B STK sp0 FP ly S0 W0 mem0 md0 own lyc
      (lib.Reusable.YG01.stack_free_state 0 pos S2) W m1 md3 k.
Proof using LAWS segs_low ML ASF FFL.
  intros STK sp0 FP ly S0 W0 mem0 md0 own lyc S2 W mem2 md2 k sp pos p o sN m1 md3
    HJ Hpos Hlo Hhi HHM HAE HFimg HFgt HFS HO HFR MU FLG WM STN HZ HREL HROS HKH Hsame.
  remember (lib.Reusable.YG0f.ly_F lyc) as FS eqn:EFS.
  pose proof (bv_unsigned_in_range _ sp) as Rsp.
  assert (EM : fs_M 0 = 16384) by reflexivity.
  assert (EFR : fs_frame FS 0 pos = FS + 36864 + pos * 64) by (unfold fs_frame, fs_B; cbn [Z.of_nat]; lia).
  assert (EFL : fs_flag FS 0 pos = FS + 4096 + pos) by (unfold fs_flag; cbn [Z.of_nat]; lia).
  unfold HIGHMEM_BEG, APPMEM_END, FS_SIZE, ASAN_GT, ImgBounds.IMG_HI in *.
  assert (HIMG : forall a, pb_Wr sp FS pos p o a -> ImgBounds.IMG_HI <= a < 2 ^ 64).
  { intros a Ha. unfold ImgBounds.IMG_HI.
    destruct (pb_Wr_cases _ _ _ _ _ a Ha) as [W1|[W1|[W1|[W1|(Epo & W1)]]]].
    - lia.
    - rewrite EFL in W1. lia.
    - rewrite EFR in W1. lia.
    - unfold shadow_addr, ASAN_K in W1. rewrite EFR in W1. Z.div_mod_to_equations. lia.
    - apply orb_false_iff in Epo. destruct Epo as (_ & Eo). apply Z.eqb_neq in Eo.
      destruct (HO Eo) as (O1 & O2 & _). unfold ImgBounds.IMG_HI in O1. lia. }
  apply (GlueLift.rrB_journal_free B LAWS segs_low ML ASF FFL STK sp0 FP ly S0 W0 mem0 md0 own lyc S2 W mem2 md2 k
           m1 (ms_mem sN) md3 (pb_Wr sp FS pos p o) 0 pos HJ).
  - lia.
  - (* each written byte is an awr byte of ((0, pos) :: own), or the flag *)
    intros a Ha. destruct (pb_Wr_cases _ _ _ _ _ a Ha) as [W1|[W1|[W1|[W1|(Epo & W1)]]]].
    + left. unfold lib.Reusable.YCbq.awr_byte. left. lia.
    + right. rewrite pb_flag_addr0, <- EFS. exact W1.
    + left. unfold lib.Reusable.YCbq.awr_byte. right; right; right.
      exists 0, pos. split; [left; reflexivity|]. left.
      unfold lib.Reusable.YG0n.in_zr. cbn [fst snd]. rewrite pb_frame_addr0, <- EFS.
      change (lib.Reusable.YG00.fs_frame_bytes 0) with 64. exact W1.
    + left. unfold lib.Reusable.YCbq.awr_byte. right; right; right.
      exists 0, pos. split; [left; reflexivity|]. right.
      unfold lib.Reusable.YG0n.in_zr. cbn [fst snd]. rewrite pb_frame_addr0, <- EFS.
      change (lib.Reusable.YG00.fs_frame_bytes 0 / 8) with 8.
      unfold lib.Reusable.YG0f.shadow_addr, lib.Reusable.YG0f.SHADOW_OFF. unfold shadow_addr, ASAN_K in W1. lia.
    + apply orb_false_iff in Epo. destruct Epo as (_ & Eo). apply Z.eqb_neq in Eo.
      destruct (HO Eo) as (_ & _ & HW & _). left. apply pb_awr_cons. exact (HW a W1).
  - exact HIMG.
  - intros a. exact (pb_Wr_dec sp FS pos p o a).
  - (* off the write set the normalized end memory is normalize mem2 *)
    intros x Hx. apply MU. exact (pb_Wr_out _ _ _ _ _ _ Hx).
  - (* each written byte is readable at the end *)
    intros a Ha. pose proof (HIMG a Ha) as Ia.
    assert (Ua : bv_unsigned (wa a) = a) by (apply wa_unsigned; unfold ImgBounds.IMG_HI in Ia; lia).
    destruct (pb_Wr_cases _ _ _ _ _ a Ha) as [W1|[W1|[W1|[W1|(Epo & W1)]]]].
    + destruct STN as (_ & _ & H). exact (proj2 (H a W1)).
    + subst a. exists (Z_to_bv 8 0). exact FLG.
    + apply (pb_rd_end _ _ _ WM); [rewrite Ua; exact (proj1 Ia)|].
      rewrite pb_norm_above by exact Ia.
      assert (Hf : lib.Reusable.YG0f.frame_addr lyc 0 pos <= a <
                   lib.Reusable.YG0f.frame_addr lyc 0 pos + lib.Reusable.YG00.fs_frame_bytes 0)
        by (rewrite pb_frame_addr0, <- EFS; change (lib.Reusable.YG00.fs_frame_bytes 0) with 64; exact W1).
      destruct (HFR a Hf) as [_ (bb & Ebb)]. exists bb. exact Ebb.
    + apply (pb_rd_end _ _ _ WM); [rewrite Ua; exact (proj1 Ia)|].
      rewrite pb_norm_above by exact Ia.
      apply (pb_aview_present (lib.Reusable.YA0n.w_H W) mem2 a Ia).
      unfold shadow_addr, ASAN_K in W1.
      pose proof (HZ (a - (fs_frame FS 0 pos / 8 + 0x7fff8000)) ltac:(change (lib.Reusable.YG00.fs_frame_bytes 0 / 8)
                                                                        with 8; lia)) as Zi.
      unfold lib.Reusable.YG0v.shadow_of_addr, lib.Reusable.YG0f.SHADOW_OFF in Zi.
      rewrite pb_frame_addr0, <- EFS in Zi.
      replace (0x7fff8000 + fs_frame FS 0 pos / 8 + (a - (fs_frame FS 0 pos / 8 + 0x7fff8000))) with a in Zi by lia.
      rewrite Zi. discriminate.
    + apply orb_false_iff in Epo. destruct Epo as (_ & Eo). apply Z.eqb_neq in Eo.
      destruct (HO Eo) as (_ & _ & _ & (_ & _ & HWo)).
      apply (pb_rd_end _ _ _ WM); [rewrite Ua; exact (proj1 Ia)|].
      rewrite pb_norm_above by exact Ia.
      apply (pb_wv_present mem2 (wa a)); [rewrite Ua; exact (proj1 Ia)|].
      replace a with (o + (a - o)) by lia. apply HWo. lia.
  - rewrite pb_flag_addr0, <- EFS, EFL. unfold ImgBounds.IMG_HI. lia.
  - rewrite pb_flag_addr0, <- EFS. exact FLG.
  - exact HREL.
  - exact HROS.
  - exact HKH.
  - exact Hsame.
Qed.

(* ---- The top: the spec, by the seven steps.  The Section premises below are the named premises of the top
   Section of the plan of record (section "Named hypotheses of the top Section (owner)"); the callee contracts are
   those mb_post_rebaseRB takes, each its owner's text. ---- *)
Variables (RLO RHI : Z) (GLOBS : list (Z * Z)).
(* image: the RELRO range lies in the image (the spec's arodata_okS range) *)
Hypothesis RELRO_IMG : forall a, RLO <= a < RHI -> lib.Reusable.YG0d.in_img rsegs a.
(* core (TfibLib record, pending the record core) *)
Hypothesis TS : lib.Reusable.YF0m.CtrlTSyms B.
Hypothesis errno_low : lib.Reusable.YCbq.api_env rsegs B.
(* a Theorem Labs lane's class-0 fake-stack request rules (a working branch) *)
Hypothesis SMP : lib.Reusable.YCbq.stack_malloc_progressP B.
Hypothesis ASM0 : lib.Reusable.YG0d.astack_malloc_realizes rsegs B 0.
Hypothesis PC0 : lib.Reusable.YG0f.pc_stack_malloc (lib.Reusable.YG0f.as_code B) 0 = 251636.
(* image globals (CtrlRo; GLOBS := ctrl_ro_globs at the top of the closure, lib/B/ProgBridgeData.v) *)
Hypothesis HGM : B.Prog.CtrlRo.globs_marked rsegs B GLOBS.
Hypothesis HZS_J13 : B.Prog.CtrlRo.in_zs B JOIN_0013 32.
Hypothesis HZS_J14 : B.Prog.CtrlRo.in_zs B JOIN_0014 32.
Hypothesis HIMGSH : B.Prog.CtrlRo.img_shadow_vis rsegs B.
(* the callee contracts of stretch B (each its owner's text), all six in their route-(C) _on form *)
Hypothesis HSM : B.Prog.asan_stack_malloc_cF_on.asan_stack_malloc_0_contract_F_on.
Hypothesis HMS : B.Prog.asan_memset_cF_on.asan_memset_contract_F_on.
Hypothesis HMC : B.Prog.asan_memcpy_cF_on.asan_memcpy_contract_F_on.
Hypothesis HBD : B.Prog.build_dt1_single_c.build_dt1_single_contract_F_on.
Hypothesis HDH : B.Prog.dt1_head_c.dt1_head_contract_F_on.
Hypothesis HNF : B.Prog.name_field_c_on.name_field_contract_F_on.

Theorem pb_reac_box_model_block : C_reac_box_model_block.treac_box_model_block_spec RLO RHI B GLOBS.
Proof.
  unfold C_reac_box_model_block.treac_box_model_block_spec.
  intros STK sp0 FP ly S0 W0 mem0 md0 own lyc Sc W memc mdc k regs p b o row nb
    HJ HRO HRET HRA HGP HTP HA0 HA1 HA2 Hp Hb Ho HS16 HSlo HShi HCNT HROW HNAME HOB.
  unfold C_reac_box_model_block.REAC_BOX_MODEL_BLOCK_STK in HSlo.
  (* ENTRY *)
  destruct (B.Prog.C_reac_box_model_blockEnt.mbB_entry RLO RHI RELRO_IMG B GLOBS TS LAWS
              STK sp0 FP ly S0 W0 mem0 md0 own lyc Sc W memc mdc k regs p o row HJ HRO HTP HS16 HSlo HShi HROW HOB)
    as (ROc & HS16' & STc & ACc & HHMc & HAEc & FPc & HFimg).
  pose proof HJ as (HARc & _).
  (* one spelling of the entry sp / tp for lia: getr r is reg_get r at a nonzero literal r *)
  unfold lib.Reusable.YG0d.spZ in HS16, HSlo, HShi.
  change (lib.Reusable.YK11.getr regs 2) with (reg_get regs 2) in *.
  change (lib.Reusable.YK11.getr regs 4) with (reg_get regs 4) in *.
  pose proof (bv_unsigned_in_range _ (reg_get regs 2)) as Rsp.
  assert (Etp : bv_unsigned (reg_get regs 4) = RT_TP).
  { rewrite HTP. unfold lib.Reusable.YG0d.w64.
    rewrite (B.ProgWorld.as_tp_RT_TP B TS). apply B.ProgWorld.pws_u64. unfold RT_TP. lia. }
  (* V at memc: the footprint at RNG_W (w_H W) over normalize memc *)
  assert (VISc : B.Prog.reac_box_model_blockF.mbF_rng (B.ProgBridge.RNG_W (lib.Reusable.YA0n.w_H W))
                   (B.MemNorm.normalize rsegs memc) (reg_get regs 2) (reg_get regs 4) p b o
                   (lib.Reusable.YG0f.ly_F lyc) row nb).
  { apply (B.Prog.C_reac_box_model_blockVis.mbB_rngW B TS STK sp0 FP ly S0 W0 mem0 md0 own lyc Sc W memc mdc k
             (reg_get regs 2) (reg_get regs 4) p b o row nb HJ ROc HSlo HShi Etp).
    - intros Hp0. destruct (HROW Hp0) as (P1 & P2 & P3 & _ & P5 & P6 & P7 & _).
      unfold B.Prog.CtrlRo.IMG_LO, B.Prog.CtrlRo.IMG_HI in P5, P6.
      split; [lia|]. split; [lia|]. split; [exact P2|]. split; [exact P3|].
      apply (B.Prog.CtrlRo.ro_hull rsegs B lyc Sc W memc mdc p 296 HIMGSH HARc);
        unfold B.Prog.CtrlRo.IMG_LO, B.Prog.CtrlRo.IMG_HI; lia.
    - intros Hp0 Hb56 Hh Hr. destruct (HNAME Hp0 Hb56 Hh Hr) as (N1 & N2 & _ & Bn0 & Bn1 & _).
      pose proof N1 as (NL & _).
      unfold B.Prog.CtrlRo.IMG_LO, B.Prog.CtrlRo.IMG_HI in Bn0, Bn1.
      split; [lia|]. split; [exact N2|].
      apply (B.Prog.CtrlRo.ro_hull rsegs B lyc Sc W memc mdc (RcSynth.rname row) (Z.of_nat (length nb)) HIMGSH HARc);
        unfold B.Prog.CtrlRo.IMG_LO, B.Prog.CtrlRo.IMG_HI; lia.
    - intros _ Ho0. destruct (HOB Ho0) as (_ & _ & Hwr & Hsrc & _).
      unfold B.Prog.CtrlCallerJ.twr_ok in Hwr. unfold B.Prog.CtrlCallerJ.tsrc_ok in Hsrc.
      destruct Hsrc as (_ & _ & Hsh & _ & Ho1 & Ho2).
      split; [lia|]. split; [lia|]. split; [|exact Hsh].
      intros a Ha. exact (proj1 (proj2 (Hwr a Ha))). }
  (* the entry state in mkR form *)
  unfold lib.Reusable.YG0d.cfg_at.
  apply (lib.Reusable.YA0nR.SRr_xregs_eqv rsegs W (Regs6ss.mkR_of regs) regs lib.Reusable.YK11.fp_regs
           (Z_to_bv 64 C_reac_box_model_block.REAC_BOX_MODEL_BLOCK) lib.Reusable.YK11.fp_csr None memc
           (lib.Lib.PropExec.seg_rom rsegs) mdc); [|exact (Regs6ss.xregs_eqv_sym _ _ (Regs6ss.mkR_of_eqv regs))].
  unfold Regs6ss.mkR_of.
  assert (E10 : reg_get regs 10 = Z_to_bv 64 p) by exact HA0.
  assert (E11 : reg_get regs 11 = Z_to_bv 64 b) by exact HA1.
  assert (E12 : reg_get regs 12 = Z_to_bv 64 o) by exact HA2.
  rewrite E10, E11, E12.
  set (A := (bv_unsigned (reg_get regs 2) - 160) / 32 * 32).
  (* A: stretch A lifted, then the class-0 request *)
  apply (B.Prog.C_reac_box_model_blockPf.mbB_to_E0 B LAWS segs_low STK sp0 FP ly S0 W0 mem0 md0 own lyc Sc W memc
           mdc k (reg_get regs 1) (reg_get regs 2) (reg_get regs 3) (reg_get regs 4) (reg_get regs 8)
           (reg_get regs 9) (reg_get regs 18) (reg_get regs 19) (reg_get regs 20) (reg_get regs 21)
           (reg_get regs 22) (reg_get regs 23) (reg_get regs 24) (reg_get regs 25) (reg_get regs 26)
           (reg_get regs 27) lib.Reusable.YK11.fp_regs lib.Reusable.YK11.fp_csr p b o (lib.Reusable.YG0f.ly_F lyc)
           A row nb (reg_get regs 5) (reg_get regs 6) (reg_get regs 7) (reg_get regs 13) (reg_get regs 14)
           (reg_get regs 15) (reg_get regs 16) (reg_get regs 17) (reg_get regs 28) (reg_get regs 29)
           (reg_get regs 30) (reg_get regs 31) _ HJ HSlo HShi ROc eq_refl HS16' STc ACc HHMc HAEc FPc VISc).
  intros m1 mc mdc1 PF HREL HROS HKH1 HJ1.
  unfold HIGHMEM_BEG in HHMc.
  apply (B.Prog.C_reac_box_model_blockPf.mbB_E0 B LAWS segs_low errno_low ML SMP ASM0 PC0 STK sp0 FP ly S0 W0 mem0
           md0 own lyc Sc W m1 mdc1 k (reg_get regs 2) (reg_get regs 3) (reg_get regs 4) (reg_get regs 5)
           (reg_get regs 6) (reg_get regs 7) (reg_get regs 13) (reg_get regs 14) (reg_get regs 15) (reg_get regs 16)
           (reg_get regs 17) (reg_get regs 18) (reg_get regs 21) (reg_get regs 23) (reg_get regs 24)
           (reg_get regs 26) (reg_get regs 27) (reg_get regs 28) (reg_get regs 29) (reg_get regs 30)
           (reg_get regs 31) p b o A _ HJ1 HSlo HShi eq_refl HS16' ltac:(lia) HGP HTP HCNT).
  intros S2 regs2 mem2 md2 pos HJ2 HPRES HA0' HAB HFR2 HNI HNEV HBB HZ HRDW HKEPT HECALL HFP HVIEW HEST.
  (* MID *)
  match type of HECALL with lib.Reusable.YG0d.ecall_pre _ _ _ _ _ ?R _ _ => set (regsT := R) in * end.
  assert (HspT : lib.Reusable.YG0d.spZ regsT = A).
  { unfold lib.Reusable.YG0d.spZ. change (lib.Reusable.YK11.getr regsT 2) with (Z_to_bv 64 A).
    apply unsigned_lit. unfold A. unfold APPMEM_END in HAEc. Z.div_mod_to_equations. lia. }
  destruct (B.Prog.C_reac_box_model_blockMid.mbB_mid B RLO RHI GLOBS LAWS TS RELRO_IMG
              HGM HZS_J13 HZS_J14 HIMGSH STK sp0 FP ly S0 W0 mem0 md0 own lyc Sc W memc mdc k
              (reg_get regs 1) (reg_get regs 2) (reg_get regs 4) (reg_get regs 8) (reg_get regs 9)
              (reg_get regs 18) (reg_get regs 19) (reg_get regs 20) (reg_get regs 21) (reg_get regs 22)
              (reg_get regs 23) (reg_get regs 24) (reg_get regs 25) p b o A row nb m1 mc mdc1 S2 regsT regs2 mem2 md2
              pos HJ HRO HTP Hp Hb Ho HS16' HSlo HShi eq_refl HROW HNAME HOB PF HREL HROS HJ1 HJ2 HA0' HFR2 HNI HZ
              HRDW HKEPT HECALL HspT HFP HVIEW HEST)
    as (ob & RO2 & _ & S16 & ST2 & AC2 & SR2 & HHM2 & HAE2 & AW2 & FP2 & TLS2 & Rp & Rb & Ro & ROW2 & NAME2 & OB2 &
        ORO & PAD & NAD & OAD & J14 & J13 & NDJ & Hpos & B56 & HINT & SAV & OIMG & RNG2).
  (* the state at the class-0 return in mkR form: the callee-saved registers are the call's (aregs_preserved) and
     a0 is the class-0 frame fr = fs_frame (ly_F lyc) 0 pos *)
  set (fr := fs_frame (lib.Reusable.YG0f.ly_F lyc) 0 pos).
  apply (lib.Reusable.YA0nR.SRr_xregs_eqv rsegs W (Regs6ss.mkR_of regs2) regs2 lib.Reusable.YK11.fp_regs
           (Z_to_bv 64 550472) lib.Reusable.YK11.fp_csr None mem2 (lib.Lib.PropExec.seg_rom rsegs) md2);
    [|exact (Regs6ss.xregs_eqv_sym _ _ (Regs6ss.mkR_of_eqv regs2))].
  unfold Regs6ss.mkR_of.
  pose proof HPRES as CS. unfold lib.Reusable.YG0d.aregs_preserved in CS.
  assert (P2 : reg_get regs2 2 = Z_to_bv 64 A) by exact (CS 2 ltac:(unfold lib.Reusable.YG0d.acallee_saved; lia)).
  assert (P3 : reg_get regs2 3 = reg_get regs 3) by exact (CS 3 ltac:(unfold lib.Reusable.YG0d.acallee_saved; lia)).
  assert (P4 : reg_get regs2 4 = reg_get regs 4) by exact (CS 4 ltac:(unfold lib.Reusable.YG0d.acallee_saved; lia)).
  assert (P8 : reg_get regs2 8 = reg_get regs 2) by exact (CS 8 ltac:(unfold lib.Reusable.YG0d.acallee_saved; lia)).
  assert (P9 : reg_get regs2 9 = Z_to_bv 64 A) by exact (CS 9 ltac:(unfold lib.Reusable.YG0d.acallee_saved; lia)).
  assert (P18 : reg_get regs2 18 = reg_get regs 18) by exact (CS 18 ltac:(unfold lib.Reusable.YG0d.acallee_saved; lia)).
  assert (P19 : reg_get regs2 19 = Z_to_bv 64 o) by exact (CS 19 ltac:(unfold lib.Reusable.YG0d.acallee_saved; lia)).
  assert (P20 : reg_get regs2 20 = Z_to_bv 64 p) by exact (CS 20 ltac:(unfold lib.Reusable.YG0d.acallee_saved; lia)).
  assert (P21 : reg_get regs2 21 = reg_get regs 21) by exact (CS 21 ltac:(unfold lib.Reusable.YG0d.acallee_saved; lia)).
  assert (P22 : reg_get regs2 22 = Z_to_bv 64 b) by exact (CS 22 ltac:(unfold lib.Reusable.YG0d.acallee_saved; lia)).
  assert (P23 : reg_get regs2 23 = reg_get regs 23) by exact (CS 23 ltac:(unfold lib.Reusable.YG0d.acallee_saved; lia)).
  assert (P24 : reg_get regs2 24 = reg_get regs 24) by exact (CS 24 ltac:(unfold lib.Reusable.YG0d.acallee_saved; lia)).
  assert (P25 : reg_get regs2 25 = wa ASAN_K) by exact (CS 25 ltac:(unfold lib.Reusable.YG0d.acallee_saved; lia)).
  assert (P26 : reg_get regs2 26 = reg_get regs 26) by exact (CS 26 ltac:(unfold lib.Reusable.YG0d.acallee_saved; lia)).
  assert (P27 : reg_get regs2 27 = reg_get regs 27) by exact (CS 27 ltac:(unfold lib.Reusable.YG0d.acallee_saved; lia)).
  assert (P10 : reg_get regs2 10 = Z_to_bv 64 fr).
  { change (reg_get regs2 10) with (lib.Reusable.YK11.getr regs2 10). rewrite HA0'. unfold lib.Reusable.YG0d.w64.
    rewrite pb_frame_addr0. reflexivity. }
  rewrite P2, P3, P4, P8, P9, P10, P18, P19, P20, P21, P22, P23, P24, P25, P26, P27.
  (* B: stretch B re-based at mem2, lifted to the real memory *)
  apply (GlueLift.rrB_lift B.ProgBridgeData.rsegs_wx_nowrap W md2 _ lib.Reusable.YK11.fp_regs (Z_to_bv 64 550472)
           lib.Reusable.YK11.fp_csr None mem2 (lib.Lib.PropExec.seg_rom rsegs)
           (B.Prog.C_reac_box_model_blockRB.Q0 (reg_get regs 1) (reg_get regs 2) (reg_get regs 3) (reg_get regs 4)
              (reg_get regs 8) (reg_get regs 9) (reg_get regs 18) (reg_get regs 19) (reg_get regs 20)
              (reg_get regs 21) (reg_get regs 22) (reg_get regs 23) (reg_get regs 24) (reg_get regs 25)
              (reg_get regs 26) (reg_get regs 27) lib.Reusable.YK11.fp_regs lib.Reusable.YK11.fp_csr
              (B.MemNorm.normalize rsegs mem2) p b o (lib.Reusable.YG0f.ly_F lyc) row nb fr pos 1)
           _ RO2).
  { exact (B.Prog.C_reac_box_model_blockRBLib.mb_post_rebaseRB mem2 (reg_get regs 1) (reg_get regs 2)
             (reg_get regs 3) (reg_get regs 4) (reg_get regs 8) (reg_get regs 9) (reg_get regs 18)
             (reg_get regs 19) (reg_get regs 20) (reg_get regs 21) (reg_get regs 22) (reg_get regs 23)
             (reg_get regs 24) (reg_get regs 25) (reg_get regs 26) (reg_get regs 27) lib.Reusable.YK11.fp_regs
             lib.Reusable.YK11.fp_csr p b o (lib.Reusable.YG0f.ly_F lyc) A row nb ob
             (B.ProgBridge.RNG_W (lib.Reusable.YA0n.w_H W)) pos fr (reg_get regs2 1)
             (reg_get regs2 5) (reg_get regs2 6) (reg_get regs2 7) (reg_get regs2 28) (reg_get regs2 29)
             (reg_get regs2 30) (reg_get regs2 31) (reg_get regs2 11) (reg_get regs2 12) (reg_get regs2 13)
             (reg_get regs2 14) (reg_get regs2 15) (reg_get regs2 16) (reg_get regs2 17)
             RO2 eq_refl S16 ST2 AC2 SR2 HHM2 HAE2 AW2 FP2 TLS2 Rp Rb Ro ROW2 NAME2 OB2 ORO PAD NAD OAD J14 J13 NDJ
             Hpos eq_refl B56 HINT SAV HSM HMS HMC HBD HDH HNF RNG2). }
  intros ms' md' (sN & HQ & HMSR & HROS2) HKH2 HSBM.
  apply lib.Reusable.YA0n.SRr_ret.
  destruct HQ as (HPOST & HMU & HFLG).
  pose proof HPOST as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' &
                       Es & _ & WMe & _ & STe & _).
  assert (EmN : ms_mem sN = m') by (rewrite Es; reflexivity).
  (* the frame facts from fp at memc: the side stack above ASAN_GT and below the window *)
  pose proof FPc as (DT & TSc & C & T & DB & kk & _ & _ & HPm & _ & _ & _ & HFSz & _).
  pose proof HPm as (_ & _ & HFgt & _).
  (* J: the journal after stretch B *)
  assert (HJ3 : lib.Reusable.YCbq.ajournal rsegs B STK sp0 FP ly S0 W0 mem0 md0 own lyc
                  (lib.Reusable.YG01.stack_free_state 0 pos S2) W (ms_mem ms') md' k).
  { apply (pb_J_SB STK sp0 FP ly S0 W0 mem0 md0 own lyc S2 W mem2 md2 k (reg_get regs 2) pos p o sN (ms_mem ms') md'
             HJ2 Hpos HSlo HShi ltac:(unfold HIGHMEM_BEG; lia) HAE2 HFimg HFgt HFSz).
    - intros Ho0. destruct (HOB Ho0) as (_ & _ & Hwr & Hsrc & _).
      unfold B.Prog.CtrlCallerJ.twr_ok in Hwr. unfold B.Prog.CtrlCallerJ.tsrc_ok in Hsrc.
      destruct Hsrc as (_ & _ & _ & _ & Ho1 & Ho2).
      destruct (OB2 Ho0) as ((_ & OW) & _).
      split; [exact (OIMG Ho0)|]. split; [lia|]. split; [|exact OW].
      intros a Ha. rewrite HAB. exact (proj1 (Hwr a Ha)).
    - exact HFP.
    - exact HMU.
    - exact (HFLG eq_refl).
    - rewrite EmN. exact WMe.
    - rewrite EmN. exact STe.
    - exact HZ.
    - exact (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 HMSR))))))).
    - exact HROS2.
    - exact HKH2.
    - exact HSBM. }
  (* POST *)
  destruct PF as (MUc & _).
  apply (B.Prog.C_reac_box_model_blockPost.mbB_post B LAWS segs_low STK sp0 FP ly S0 W0 mem0 md0 own lyc Sc W memc k
           regs p b o row nb (reg_get regs 1) (reg_get regs 2) (reg_get regs 3) (reg_get regs 4) (reg_get regs 8)
           (reg_get regs 9) (reg_get regs 18) (reg_get regs 19) (reg_get regs 20) (reg_get regs 21)
           (reg_get regs 22) (reg_get regs 23) (reg_get regs 24) (reg_get regs 25) (reg_get regs 26)
           (reg_get regs 27) m1 mc A S2 mem2 md2 pos (lib.Reusable.YG0f.ly_F lyc) sN ms' md'
           (pb_Wr (reg_get regs 2) (lib.Reusable.YG0f.ly_F lyc) pos p o)
           eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl
           eq_refl eq_refl eq_refl HRET HS16 HSlo HShi).
  - intros Hp0. destruct (HROW Hp0) as (_ & P2' & _). exact P2'.
  - intros Ho0 x Hx. destruct (HOB Ho0) as (_ & Himg & Hwr & _).
    unfold B.Prog.CtrlCallerJ.twr_ok in Hwr.
    split; [exact (Himg x Hx) | exact (proj1 (proj2 (Hwr x Hx)))].
  - exact MUc.
  - exact HREL.
  - exact HROS.
  - reflexivity.
  - exact HJ2.
  - exact HFR2.
  - exact HAB.
  - exact HKEPT.
  - exact HPOST.
  - exact HMSR.
  - exact HROS2.
  - intros x Hx. apply HMU. exact (pb_Wr_out _ _ _ _ _ _ Hx).
  - (* the write set in mbB_post's form *)
    intros a Ha. destruct (pb_Wr_cases _ _ _ _ _ a Ha) as [W1|[W1|[W1|[W1|(Epo & W1)]]]].
    + left. exact W1.
    + right; right; right; left. rewrite pb_flag_addr0. exact W1.
    + right; left. unfold lib.Reusable.YG0n.in_zr, lib.Reusable.YCbq.frame_rng. cbn [fst snd].
      rewrite pb_frame_addr0. change (lib.Reusable.YG00.fs_frame_bytes 0) with 64. exact W1.
    + right; right; left. unfold lib.Reusable.YG0n.in_zr. cbn [fst snd]. rewrite pb_frame_addr0.
      change (lib.Reusable.YG00.fs_frame_bytes 0 / 8) with 8.
      unfold lib.Reusable.YG0f.shadow_addr, lib.Reusable.YG0f.SHADOW_OFF. unfold shadow_addr, ASAN_K in W1. lia.
    + right; right; right; right. rewrite Epo. exact W1.
  - exact HJ3.
Qed.
End Pb.

About pb_reac_box_model_block.
Print Assumptions pb_reac_box_model_block.
