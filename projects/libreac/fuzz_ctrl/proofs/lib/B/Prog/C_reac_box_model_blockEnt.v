(* reac_box_model_block (image B, asan-ubsan, libreac v1.9.0): ENTRY of pb_reac_box_model_block, a Theorem Labs lane
   (plan of record analyses/libreac/fuzz_ctrl/glue-B/model_block/pb_reac_box_model_block.plan.md (a working note, not in this delivery), row ENTRY).

   mbB_entry: from the premises of treac_box_model_block_spec (lib/B/Prog/C_reac_box_model_block.v) at the entry --
   the caller's journal at memc, arodata_okS, the tp / sp facts, the window bounds, the row premise and the o premise --
   to the memory premises that mbB_to_E0 (lib/B/Prog/C_reac_box_model_blockPf.v) takes at memc, with sp := getr regs 2,
   tp := getr regs 4 and FS := ly_F lyc:
     B.MemNorm.ro_agree, sp mod 16, the stk window [sp - 4272, sp), asan_cells, HIGHMEM_BEG <= sp - 4272,
     sp <= APPMEM_END, fp [0] .. (reac_box_model_block_W o sp) (reac_box_model_block_D p o), and IMG_HI <= ly_F lyc.
   Sources: the journal's AR, its window presence and astk_ok; B.ProgWorldCtlRtC's ctl_rt_C_of_AR (asan_cells and
   ro_agree, route (C): no VIS0, no OWNED_RO; arodata_okP from the spec's arodata_okS by B.ProgWorld.arodata_okP_of_S), ctl_fp_of_AR (fp), fp_tls_owned (the
   thread cells are owned, so apart from the bytes the call writes), as_tp_RT_TP (tp = RT_TP); the core's layout_ok
   (the side stack below the allocator's ceiling, apart from the image hull), Wf (a live frame's position) and
   ALedger (every segment inside the image hull).  Each ProgWorld statement is a Section hypothesis typed by its _stmt.

   rule 24: no function proved (the glue of the proved run reac_box_model_block_holds_F). *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
(* the core, Imported as treac_box_model_block_spec Imports it, so the premises below read as the spec's text *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00 YI0f YI16.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require Import YM05 YE01.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require APostBase YB1v YF0m.
(* image B: qualified only *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require B.Img0 B.AsanRT B.ACtlK B.ACtlCut B.MemNorm B.ProgWorld.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require B.ProgWorldCtlRtC B.ProgWorld_Fs B.ProgWorldTlsOwned.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require B.Prog.asan_stack_malloc_c B.Prog.RcAsanFP.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require B.Prog.reac_box_model_block_c B.Prog.ImgBounds.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require B.Prog.CtrlImg B.Prog.CtrlRo B.Prog.CtrlCallerJ.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require B.Prog.C_reac_box_model_block.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Mem Frame.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require RcLay.
(* the concrete PA instance the spec resolves CtrlCallerJ's shapes with (as the spec activates it) *)
#[local] Existing Instance B.Prog.CtrlImg.PI_ctrl_B.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.

(* ---- arithmetic and memory helpers (no world fact) ---- *)

(* Two non-empty intervals with no common point are apart. *)
Lemma mbE_dj_of_pt : forall a b c d : Z, a < b -> c < d ->
  (forall x, a <= x < b -> c <= x < d -> False) -> lib.Prog.RcLay.ly_dj a b c d.
Proof.
  intros a b c d Hab Hcd H. unfold lib.Prog.RcLay.ly_dj.
  destruct (Z_le_gt_dec b c) as [L|L]; [left; exact L|].
  destruct (Z_le_gt_dec d a) as [L2|L2]; [right; exact L2|].
  exfalso. apply (H (Z.max a c)); lia.
Qed.

(* A non-empty interval of non-owned bytes is apart from every non-empty interval of owned bytes. *)
Lemma mbE_dj_owned : forall (Own : Z -> Prop) (a b : Z) (L : list (Z * Z)),
  a < b -> (forall x, a <= x < b -> ~ Own x) ->
  Forall (fun d => fst d < snd d /\ forall x, fst d <= x < snd d -> Own x) L ->
  Forall (fun d => lib.Prog.RcLay.ly_dj a b (fst d) (snd d)) L.
Proof.
  intros Own a b L Hab Hn HL. eapply Forall_impl; [|exact HL].
  intros [c d] [Hcd Ho]. cbn [fst snd] in *. apply mbE_dj_of_pt; [exact Hab | exact Hcd |].
  intros x H1 H2. exact (Hn x H1 (Ho x H2)).
Qed.

(* A range of present bytes is a readable stack range. *)
Lemma mbE_stk_of_present : forall (H : word -> bool) (m : word -> option byte) (lo hi : Z),
  0 <= lo -> hi <= 2 ^ 64 -> (forall a, lo <= a < hi -> lib.Reusable.YG0n.apresent H m a) ->
  lib.Lib.Frame.stk B.Img0.rsegs m lo hi.
Proof.
  intros H m lo hi H0 H1 HP. split; [exact H0|]. split; [exact H1|]. intros a Ha.
  destruct (HP a Ha) as [_ [b Hb]]. unfold lib.Lib.Mem.wa.
  split; [unfold wview; rewrite Hb; discriminate | exists b; unfold lib.Lib.Mem.mrd; rewrite Hb; reflexivity].
Qed.

(* The side-stack header of fp's write-apartness ends at the first class-0 frame: fs_frame FS 0 0 = FS + 36864. *)
Lemma mbE_fs_frame00 : forall FS, B.Prog.asan_stack_malloc_c.fs_frame FS 0 0 = FS + 36864.
Proof.
  intros FS. unfold B.Prog.asan_stack_malloc_c.fs_frame, B.Prog.asan_stack_malloc_c.fs_B.
  change (Z.of_nat 0) with 0. lia.
Qed.

(* A range [q, q + n) apart from the class-0 bytes fp_w [0] FS names (hint word, flags, frames, their shadow): it is
   apart from the side stack's first 1085440 bytes or above them, and it is application memory below the low shadow
   band or above the high one.  The side stack lies in application memory below the allocator's ceiling. *)
Lemma mbE_cls0_dj : forall FS q n : Z,
  0 < n -> 4096 <= FS -> FS + 11571200 <= 0x7fffff800000 ->
  (FS + 11571200 <= q \/ q + n <= FS \/ FS + 1085440 <= q) ->
  (q + n <= 0x7fff7000 \/ 0x10007fff7fe0 <= q) ->
  B.Prog.RcAsanFP.fp_dj [(q, q + n)] (B.Prog.RcAsanFP.fp_w [0%nat] FS).
Proof.
  intros FS q n Hn HF HFc Hq Hs.
  assert (EM : B.Prog.asan_stack_malloc_c.fs_M 0 = 16384) by reflexivity.
  assert (E0F : forall j, B.Prog.asan_stack_malloc_c.fs_frame FS 0 j = FS + 36864 + j * 64)
    by (intros j; unfold B.Prog.asan_stack_malloc_c.fs_frame, B.Prog.asan_stack_malloc_c.fs_B;
        change (Z.of_nat 0) with 0; lia).
  assert (EF : B.Prog.asan_stack_malloc_c.fs_flag FS 0 0 = FS + 4096)
    by (unfold B.Prog.asan_stack_malloc_c.fs_flag; change (2 ^ (15 - Z.of_nat 0)) with 32768; lia).
  assert (EH : B.Prog.asan_stack_malloc_c.fs_hint FS 0 = FS)
    by (unfold B.Prog.asan_stack_malloc_c.fs_hint; change (Z.of_nat 0) with 0; lia).
  unfold B.Prog.RcAsanFP.fp_dj, B.Prog.RcAsanFP.fp_w, B.Prog.RcAsanFP.fp_w1.
  cbn [flat_map app].
  rewrite EM, !E0F, EF, EH.
  apply Forall_forall; intros w Hw; destruct Hw as [<-|[]].
  apply Forall_forall; intros d Hd.
  destruct Hd as [<-|[<-|[<-|[<-|[]]]]]; cbn [fst snd];
    unfold lib.Prog.RcLay.ly_dj, B.AsanRT.shadow_addr, B.AsanRT.ASAN_K; Z.div_mod_to_equations; lia.
Qed.

(* ---- world facts and the entry ---- *)
Section Ent.
Context {fx : lib.Reusable.YK11.FPState} {rc : lib.Reusable.YM05.RunCeil} {SK : lib.Reusable.YI16.sink_head}.
(* the spec's concrete segments (C_reac_box_model_block.v Section d) *)
#[local] Notation SEGS := lib.Reusable.YB1v.tfibsegs.
(* the spec's read-only span and its Section hypothesis (C_reac_box_model_block.v Section d) *)
Variables RLO RHI : Z.
Hypothesis RELRO_IMG : forall a, RLO <= a < RHI -> lib.Reusable.YG0d.in_img SEGS a.
Variable B : lib.Reusable.YG0f.asyms.
(* the spec's registered globals (C_reac_box_model_block.v Section e) *)
Variable GLOBS : list (Z * Z).
(* core: the bundle law (the plan's CtrlTSyms B) and the world's laws *)
Hypothesis TS : lib.Reusable.YF0m.CtrlTSyms B.
Hypothesis LAWS : lib.Reusable.YG0d.AR_laws SEGS B.
(* B ProgWorld statements, PROVED on image B and cited (L3 rule, two Theorem Labs lanes 13:12Z; a Theorem Labs lane's db8a86df2da) *)
Let ctl_fp_of_AR : B.ProgWorld.ctl_fp_of_AR_stmt B := lib.B.ProgWorld_Fs.ctl_fp_of_AR B.
Let fp_tls_owned : B.ProgWorld.fp_tls_owned_stmt B := lib.B.ProgWorldTlsOwned.fp_tls_owned B.

(* A live side-stack frame: its class is in 0..10, and it starts at or above ly_F + 36864 + cid * 2^20 (AR's Wf). *)
Lemma mbE_frame_lo : forall ly S (W : lib.Reusable.YA0n.world SEGS) m md cid pos,
  lib.Reusable.YG0n.AR SEGS B ly S W m md -> In (cid, pos) (lib.Reusable.YG01.frames S) ->
  0 <= cid <= 10 /\
  lib.Reusable.YG0f.ly_F ly + 36864 + cid * 1048576 <= lib.Reusable.YG0f.frame_addr ly cid pos.
Proof.
  intros ly S W m md cid pos [M _] Hin.
  pose proof (lib.Reusable.YG01.wfs_live _
                (lib.Reusable.YG01.wf_fakestack _ _ _ _ _ (lib.Reusable.YG0n.am_wf _ _ _ _ M))) as LV.
  unfold lib.Reusable.YG01.frames in Hin.
  pose proof (proj1 (Forall_forall _ _) LV _ Hin) as [H1 H2]. cbn [fst snd] in H1, H2.
  assert (HB : 0 <= lib.Reusable.YG00.fs_frame_bytes cid)
    by (unfold lib.Reusable.YG00.fs_frame_bytes; apply Z.shiftl_nonneg; lia).
  pose proof (Z.mul_nonneg_nonneg pos (lib.Reusable.YG00.fs_frame_bytes cid) ltac:(lia) HB) as HP.
  split; [exact H1|].
  unfold lib.Reusable.YG0f.frame_addr, lib.Reusable.YG0f.fs_frame_off, lib.Reusable.YG0f.kFakeFramesOff,
    lib.Reusable.YG00.kStackSizeLog.
  change (Z.shiftl 1 20) with 1048576. lia.
Qed.

(* The side stack is application memory below the allocator's ceiling, and the machine stack is above the ceiling
   (AR's layout_ok: lo_app, lo_stk_ceil). *)
Lemma mbE_fs_app : forall ly S (W : lib.Reusable.YA0n.world SEGS) m md,
  lib.Reusable.YG0n.AR SEGS B ly S W m md ->
  4096 <= lib.Reusable.YG0f.ly_F ly /\
  lib.Reusable.YG0f.ly_F ly + 11571200 <= lib.Reusable.YM05.alloc_ceiling /\
  0x7fff7f800000 <= lib.Reusable.YM05.alloc_ceiling <= 0x7fffff800000 /\
  lib.Reusable.YM05.alloc_ceiling <= lib.Reusable.YG0f.ly_stk_lo ly.
Proof.
  intros ly S W m md [M _].
  pose proof (lib.Reusable.YG0n.am_layout _ _ _ _ M) as LO.
  pose proof (proj1 (Forall_forall _ _) (lib.Reusable.YG0f.lo_app _ LO)
                (lib.Reusable.YG0f.ly_F ly, lib.Reusable.YG0f.kFakeStackSize)
                ltac:(unfold lib.Reusable.YG0f.owned_extents; cbn [In]; right; right; right; left; reflexivity)) as FA.
  cbn [fst snd] in FA. pose proof (lib.Reusable.YG0f.lo_stk_ceil _ LO) as SC.
  pose proof lib.Reusable.YCbq.asan_consts as (C1 & _).
  unfold lib.Reusable.YG0f.in_app, lib.Reusable.YG0f.ASAN_CEIL, lib.Reusable.YG0f.kLowShadowBeg,
    lib.Reusable.YG0f.kHighMemBeg, lib.Reusable.YG0f.kFakeStackSize in FA.
  unfold lib.Reusable.YG0f.ASAN_CEIL in SC. lia.
Qed.

(* The side stack is apart from the image hull ly_img (AR's layout_ok: lo_disj over static_extents). *)
Lemma mbE_fs_img : forall ly S (W : lib.Reusable.YA0n.world SEGS) m md,
  lib.Reusable.YG0n.AR SEGS B ly S W m md ->
  lib.Reusable.YG0f.ly_F ly + 11571200 <= fst (lib.Reusable.YG0f.ly_img ly) \/
  fst (lib.Reusable.YG0f.ly_img ly) + snd (lib.Reusable.YG0f.ly_img ly) <= lib.Reusable.YG0f.ly_F ly.
Proof.
  intros ly S W m md [M _].
  pose proof (lib.Reusable.YG0f.lo_disj _ (lib.Reusable.YG0n.am_layout _ _ _ _ M)) as D.
  unfold lib.Reusable.YG0f.static_extents, lib.Reusable.YG0f.owned_extents in D.
  cbn [app lib.Reusable.YG0f.pairwise] in D.
  destruct D as (_ & _ & _ & HF & _).
  pose proof (proj1 (Forall_forall _ _) HF (lib.Reusable.YG0f.ly_img ly)
                ltac:(cbn [In]; right; right; right; right; right; left; reflexivity)) as DI.
  unfold lib.Reusable.YG0f.zdisjoint, lib.Reusable.YG0f.kFakeStackSize in DI. cbn [fst snd] in DI. lia.
Qed.

(* A read-only image byte (in_roP over the spec's span) lies in the image hull ly_img (ALedger's al_img, RELRO_IMG). *)
Lemma mbE_ro_img : forall ly S (W : lib.Reusable.YA0n.world SEGS) m md x,
  lib.Reusable.YG0n.AR SEGS B ly S W m md -> lib.Reusable.APostBase.in_roP SEGS RLO RHI x ->
  fst (lib.Reusable.YG0f.ly_img ly) <= x < fst (lib.Reusable.YG0f.ly_img ly) + snd (lib.Reusable.YG0f.ly_img ly).
Proof.
  intros ly S W m md x (_ & L & _) [(s & Hs & _ & Hr) | Hr].
  - pose proof (lib.Reusable.YG0n.al_img _ _ _ _ L s Hs) as [J1 J2]. lia.
  - destruct (RELRO_IMG x Hr) as (s & Hs & Hr').
    pose proof (lib.Reusable.YG0n.al_img _ _ _ _ L s Hs) as [J1 J2]. lia.
Qed.

(* ENTRY.  The premises are those of treac_box_model_block_spec that the conclusions need, in the spec's text (b and
   nb, which they do not mention, are dropped).  The conclusions are mbB_to_E0's memory premises at memc with
   sp := getr regs 2, tp := getr regs 4, FS := ly_F lyc, and ImgBounds.IMG_HI <= ly_F lyc. *)
Lemma mbB_entry :
  forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc (W : lib.Reusable.YA0n.world SEGS) memc mdc k
         (regs : bvmap 5 word) (p o : Z) (row : list byte),
  ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
  arodata_okS SEGS B RLO RHI (aview SEGS (w_H W) memc) ->
  lib.Reusable.YK11.getr regs 4 = w64 (as_tp B) ->
  spZ regs mod 16 = 0 ->
  sp0 - STK <= spZ regs - B.Prog.C_reac_box_model_block.REAC_BOX_MODEL_BLOCK_STK -> spZ regs <= sp0 ->
  (p <> 0 -> p mod 8 = 0 /\ length row = 296%nat /\
             garr8 SEGS (mrestrict (w_H W) memc) p (B.Prog.C_reac_box_model_block.bmb_z row) /\
             (exists q sz, In (q, sz) GLOBS /\ q <= p /\ p + 296 <= q + sz) /\
             B.Prog.CtrlRo.IMG_LO + 64 <= p /\ p + 296 + 64 <= B.Prog.CtrlRo.IMG_HI /\
             (forall x, p <= x < p + 296 -> lib.Reusable.APostBase.in_roP SEGS RLO RHI x /\
                ~ Exists (in_zr x) (as_owned_static B) /\ ~ (as_errno B <= x < as_errno B + 4)) /\
             (o = 0 \/ o + 32 <= p \/ p + 296 <= o)) ->
  (o <> 0 -> B.Prog.C_reac_box_model_block.tbmb_o_home lyc Sc o /\
             (forall x, o <= x < o + 32 -> ~ in_img SEGS x) /\
             B.Prog.CtrlCallerJ.twr_ok B STK sp0 FP ly S lyc Sc own W memc (spZ regs) o 32 /\
             B.Prog.CtrlCallerJ.tsrc_ok W memc (spZ regs) o 32 /\
             (spZ regs <= o \/ o + 32 <= spZ regs - B.Prog.C_reac_box_model_block.REAC_BOX_MODEL_BLOCK_STK)) ->
  B.MemNorm.ro_agree B.Img0.rsegs memc /\
  bv_unsigned (lib.Reusable.YK11.getr regs 2) mod 16 = 0 /\
  lib.Lib.Frame.stk B.Img0.rsegs memc (bv_unsigned (lib.Reusable.YK11.getr regs 2) - 4272)
    (bv_unsigned (lib.Reusable.YK11.getr regs 2)) /\
  B.AsanRT.asan_cells memc /\
  B.AsanRT.HIGHMEM_BEG <= bv_unsigned (lib.Reusable.YK11.getr regs 2) - 4272 /\
  bv_unsigned (lib.Reusable.YK11.getr regs 2) <= B.AsanRT.APPMEM_END /\
  B.Prog.RcAsanFP.fp [0%nat] memc (bv_unsigned (lib.Reusable.YK11.getr regs 4)) (lib.Reusable.YG0f.ly_F lyc)
    (bv_unsigned (lib.Reusable.YK11.getr regs 2) - 4272) (bv_unsigned (lib.Reusable.YK11.getr regs 2))
    (B.Prog.reac_box_model_block_c.reac_box_model_block_W o (bv_unsigned (lib.Reusable.YK11.getr regs 2)))
    (B.Prog.reac_box_model_block_c.reac_box_model_block_D p o) /\
  B.Prog.ImgBounds.IMG_HI <= lib.Reusable.YG0f.ly_F lyc.
Proof.
  intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs p o row HJ HRO Htp H16 Hlo Hhi HP HO.
  unfold B.Prog.C_reac_box_model_block.REAC_BOX_MODEL_BLOCK_STK in Hlo, HO.
  pose proof HJ as (HAR & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & Hstk & _ & _).
  pose proof Hstk as (_ & _ & Hceil & Hslo & Hshi & H47 & _).
  pose proof (mbE_fs_app lyc Sc W memc mdc HAR) as (F0 & F1 & F2 & F3).
  pose proof (bv_unsigned_in_range 64 (lib.Reusable.YK11.getr regs 2)) as RSp.
  unfold bv_modulus in RSp. cbn [Z.of_N] in RSp.
  change (bv_unsigned (lib.Reusable.YK11.getr regs 2)) with (lib.Reusable.YG0d.spZ regs) in RSp |- *.
  set (Sp := lib.Reusable.YG0d.spZ regs) in *.
  (* the window [Sp - 4272, Sp) is inside the caller's journal window, above the allocator's ceiling *)
  assert (HWlo : lib.Reusable.YM05.alloc_ceiling <= Sp - 4272) by lia.
  assert (HWhi : Sp <= 2 ^ 47) by lia.
  (* the window's bytes are not owned (awr_byte, window clause) *)
  assert (NOW : forall x, Sp - 4272 <= x < Sp -> ~ lib.Reusable.YG0n.aowned B lyc Sc x).
  { intros x Hx.
    assert (Hw : lib.Reusable.YCbq.awr_byte STK sp0 FP (lib.Reusable.YG0d.ablocks B ly S)
                   (lib.Reusable.YG0d.ablocks B lyc Sc) lyc own x) by (left; lia).
    exact (proj1 (lib.Reusable.YCbq.awr_byte_cases SEGS B LAWS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ x HJ Hw)). }
  (* the row: an image byte range, so apart from the side stack and below the low shadow band *)
  assert (HPr : p <> 0 -> p + 296 <= 0x7fff7000 /\
            (lib.Reusable.YG0f.ly_F lyc + 11571200 <= p \/ p + 296 <= lib.Reusable.YG0f.ly_F lyc)).
  { intros Hp. destruct (HP Hp) as (_ & _ & _ & _ & HL & HH & HR & _).
    unfold B.Prog.CtrlRo.IMG_LO, B.Prog.CtrlRo.IMG_HI in HL, HH.
    pose proof (mbE_fs_img lyc Sc W memc mdc HAR) as DI.
    pose proof (mbE_ro_img lyc Sc W memc mdc p HAR (proj1 (HR p ltac:(lia)))) as I1.
    pose proof (mbE_ro_img lyc Sc W memc mdc (p + 295) HAR (proj1 (HR (p + 295) ltac:(lia)))) as I2.
    lia. }
  (* o: in a caller frame of class 1 or more, or on the machine stack; not owned *)
  assert (HOr : o <> 0 ->
            (lib.Reusable.YG0f.ly_F lyc + 11571200 <= o \/ lib.Reusable.YG0f.ly_F lyc + 1085440 <= o) /\
            (o + 32 <= 0x7fff7000 \/ 0x10007fff7fe0 <= o) /\
            (forall x, o <= x < o + 32 -> ~ lib.Reusable.YG0n.aowned B lyc Sc x)).
  { intros Ho. destruct (HO Ho) as (Hhome & _ & Hwr & _ & _).
    unfold B.Prog.CtrlCallerJ.twr_ok in Hwr.
    unfold B.Prog.C_reac_box_model_block.tbmb_o_home in Hhome.
    split; [| split].
    - destruct Hhome as [(cid & pos & Hin & Hc & Hr) | (Hs1 & Hs2)].
      + right. destruct (mbE_frame_lo lyc Sc W memc mdc cid pos HAR Hin) as (Hc10 & Hf).
        specialize (Hr o ltac:(lia)).
        unfold lib.Reusable.YG0n.in_zr, lib.Reusable.YCbq.frame_rng in Hr. cbn [fst snd] in Hr. lia.
      + left. lia.
    - destruct Hhome as [(cid & pos & Hin & Hc & Hr) | (Hs1 & Hs2)].
      + destruct (lib.Reusable.YG0d.al_frames _ _ LAWS lyc Sc W memc mdc cid pos HAR Hin) as (_ & Happ & _).
        pose proof (Hr o ltac:(lia)) as R1. pose proof (Hr (o + 31) ltac:(lia)) as R2.
        unfold lib.Reusable.YG0n.in_zr, lib.Reusable.YCbq.frame_rng in R1, R2. cbn [fst snd] in R1, R2.
        unfold lib.Reusable.YG0f.in_app, lib.Reusable.YG0f.kLowShadowBeg, lib.Reusable.YG0f.kHighMemBeg in Happ.
        lia.
      + right. lia.
    - intros x Hx. exact (proj1 (proj2 (proj2 (Hwr x Hx)))). }
  (* the thread cells fp names are non-empty and owned (fp_tls_owned) *)
  assert (TLO : Forall (fun d => fst d < snd d /\ forall x, fst d <= x < snd d -> lib.Reusable.YG0n.aowned B lyc Sc x)
     (B.Prog.RcAsanFP.fp_tls B.AsanRT.RT_TP (Z_to_bv 64 (B.AsanRT.RT_TP + 32))
        (Z_to_bv 64 (lib.Reusable.YG0f.ly_tsd lyc)) (Z_to_bv 64 (lib.Reusable.YG0f.ly_C lyc))
        (Z_to_bv 64 (lib.Reusable.YG0f.ly_T lyc)) (Z_to_bv 64 (lib.Reusable.YG0f.ly_D lyc)) 0)).
  { apply Forall_forall. intros d Hd. split.
    - unfold B.Prog.RcAsanFP.fp_tls in Hd. cbn [In] in Hd.
      repeat (destruct Hd as [<-|Hd]; [cbn [fst snd]; lia|]). destruct Hd.
    - intros x Hx. apply (fp_tls_owned TS LAWS lyc Sc W memc mdc x HAR).
      apply Exists_exists. exists d. split; [exact Hd | exact Hx]. }
  (* fp's write-apartness: the window and o against the thread cells and the side-stack header *)
  assert (DJW : B.Prog.RcAsanFP.fp_dj (B.Prog.reac_box_model_block_c.reac_box_model_block_W o Sp)
     (B.Prog.RcAsanFP.fp_tls B.AsanRT.RT_TP (Z_to_bv 64 (B.AsanRT.RT_TP + 32))
        (Z_to_bv 64 (lib.Reusable.YG0f.ly_tsd lyc)) (Z_to_bv 64 (lib.Reusable.YG0f.ly_C lyc))
        (Z_to_bv 64 (lib.Reusable.YG0f.ly_T lyc)) (Z_to_bv 64 (lib.Reusable.YG0f.ly_D lyc)) 0 ++
      (lib.Reusable.YG0f.ly_F lyc, B.Prog.asan_stack_malloc_c.fs_frame (lib.Reusable.YG0f.ly_F lyc) 0 0) :: nil)).
  { unfold B.Prog.RcAsanFP.fp_dj. rewrite mbE_fs_frame00.
    assert (WR : forall w, In w (B.Prog.reac_box_model_block_c.reac_box_model_block_W o Sp) ->
              fst w < snd w /\ (forall x, fst w <= x < snd w -> ~ lib.Reusable.YG0n.aowned B lyc Sc x) /\
              lib.Prog.RcLay.ly_dj (fst w) (snd w) (lib.Reusable.YG0f.ly_F lyc) (lib.Reusable.YG0f.ly_F lyc + 36864)).
    { intros w Hw.
      unfold B.Prog.reac_box_model_block_c.reac_box_model_block_W,
        B.Prog.reac_box_model_block_c.REAC_BOX_MODEL_BLOCK_K in Hw.
      destruct Hw as [<-|Hw].
      - cbn [fst snd]. split; [lia|]. split; [exact NOW|]. unfold lib.Prog.RcLay.ly_dj. lia.
      - revert Hw. destruct (o =? 0) eqn:Eo; intros Hw; [destruct Hw|].
        apply Z.eqb_neq in Eo. destruct Hw as [<-|[]].
        destruct (HOr Eo) as (H1 & H2 & H3). cbn [fst snd].
        split; [lia|]. split; [exact H3|]. unfold lib.Prog.RcLay.ly_dj. lia. }
    apply Forall_forall. intros w Hw. destruct (WR w Hw) as (Wne & Wno & Whd).
    apply Forall_app. split.
    - exact (mbE_dj_owned (lib.Reusable.YG0n.aowned B lyc Sc) (fst w) (snd w) _ Wne Wno TLO).
    - constructor; [exact Whd | constructor]. }
  (* fp's data-apartness: the row and o against the class-0 bytes *)
  assert (DJD : B.Prog.RcAsanFP.fp_dj (B.Prog.reac_box_model_block_c.reac_box_model_block_D p o)
                  (B.Prog.RcAsanFP.fp_w [0%nat] (lib.Reusable.YG0f.ly_F lyc))).
  { unfold B.Prog.reac_box_model_block_c.reac_box_model_block_D, B.Prog.RcAsanFP.fp_dj. apply Forall_app. split.
    - destruct (p =? 0) eqn:Ep; [constructor|]. apply Z.eqb_neq in Ep.
      destruct (HPr Ep) as (P1 & P2).
      exact (mbE_cls0_dj (lib.Reusable.YG0f.ly_F lyc) p 296 ltac:(lia) F0 ltac:(lia) ltac:(lia) ltac:(lia)).
    - destruct (o =? 0) eqn:Eo; [constructor|]. apply Z.eqb_neq in Eo.
      destruct (HOr Eo) as (O1 & O2 & _).
      exact (mbE_cls0_dj (lib.Reusable.YG0f.ly_F lyc) o 32 ltac:(lia) F0 ltac:(lia) ltac:(lia) ltac:(lia)). }
  (* fp, by ctl_fp_of_AR *)
  assert (HFP : B.Prog.RcAsanFP.fp [0%nat] memc B.AsanRT.RT_TP (lib.Reusable.YG0f.ly_F lyc) (Sp - 4272) Sp
                  (B.Prog.reac_box_model_block_c.reac_box_model_block_W o Sp)
                  (B.Prog.reac_box_model_block_c.reac_box_model_block_D p o)).
  { apply (ctl_fp_of_AR TS LAWS lyc Sc W memc mdc [0%nat] (Sp - 4272) Sp _ _ HAR).
    - constructor; [lia | constructor].
    - unfold B.Prog.asan_stack_malloc_c.FS_SIZE. lia.
    - intros a Ha. unfold B.AsanRT.app_mem, B.AsanRT.HIGHMEM_BEG, B.AsanRT.APPMEM_END. right. lia.
    - exact DJW.
    - exact DJD. }
  (* tp = RT_TP *)
  assert (Etp : bv_unsigned (lib.Reusable.YK11.getr regs 4) = B.AsanRT.RT_TP).
  { rewrite Htp, (B.ProgWorld.as_tp_RT_TP B TS). unfold lib.Reusable.YG0d.w64.
    apply B.ProgWorld.pws_u64. unfold B.AsanRT.RT_TP. lia. }
  (* asan_cells and ro_agree, by ctl_rt_C_of_AR (route (C); its shadow conjuncts are not used at the entry) *)
  destruct (B.ProgWorldCtlRtC.ctl_rt_C_of_AR B TS LAWS RLO RHI lyc Sc W memc mdc HAR
              (B.ProgWorld.arodata_okP_of_S B RLO RHI RLO RHI _ HRO (Z.le_refl _) (Z.le_refl _)))
    as (HAC & _ & _ & HROa).
  split; [exact HROa|]. split; [exact H16|]. split.
  { apply (mbE_stk_of_present (lib.Reusable.YA0n.w_H W)); [lia | lia |]. intros a Ha. apply Hpres. lia. }
  split; [exact HAC|].
  split; [unfold B.AsanRT.HIGHMEM_BEG; lia|].
  split; [unfold B.AsanRT.APPMEM_END; lia|].
  split; [rewrite Etp; exact HFP|].
  destruct HFP as (DT & TS' & C & T & DB & kk & _ & _ & HPL & _).
  destruct HPL as (_ & _ & HGT & _).
  unfold B.Prog.ImgBounds.IMG_HI. unfold B.Prog.asan_stack_malloc_c.ASAN_GT in HGT. lia.
Qed.
End Ent.

Print Assumptions mbB_entry.
